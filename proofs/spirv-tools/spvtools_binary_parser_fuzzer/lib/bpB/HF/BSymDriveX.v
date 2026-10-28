(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BCatSim BSeqExec BStoreOk BSimInv BExitSim BShapeAlg BMmapSim BSymExec BSymExec2 BSymExec2Sound BSymRun BSymDrive BMemSplit BRefMemcpyLib.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma know_nth : forall segs E M kn i K,
  know_ok segs E M kn -> nth_error kn i = Some K -> kentry_ok segs E M K.
Proof.
  intros segs E M kn i K HK Hn. unfold know_ok in HK.
  apply (proj1 (Forall_forall _ _) HK K). eapply nth_error_In. exact Hn.
Qed.

Lemma know_ok_app : forall segs E M k1 k2,
  know_ok segs E M (k1 ++ k2) <-> know_ok segs E M k1 /\ know_ok segs E M k2.
Proof. intros. unfold know_ok. apply Forall_app. Qed.

Lemma know_ok_cons : forall segs E M K kn,
  kentry_ok segs E M K -> know_ok segs E M kn -> know_ok segs E M (K :: kn).
Proof. intros. constructor; assumption. Qed.

Fixpoint kindex (p : kentry -> bool) (kn : list kentry) (i : nat) : option nat :=
  match kn with
  | [] => None
  | K :: r => if p K then Some i else kindex p r (S i)
  end.

Definition is_krange (e : expr) (K : kentry) : bool :=
  match K with KRange e' _ _ => expr_eqb e e' | _ => false end.
Definition is_kalign (e : expr) (K : kentry) : bool :=
  match K with KAlign e' _ => expr_eqb e e' | _ => false end.
Definition is_kdisj (b1 : expr) (b2 : expr) (K : kentry) : bool :=
  match K with
  | KDisj (SA c1 _) _ (SA c2 _) _ => expr_eqb b1 c1 && expr_eqb b2 c2
  | _ => false
  end.

Definition is_kwr_cov (b : expr) (k m : Z) (K : kentry) : bool :=
  match K with
  | KWr (SA c kk) len => expr_eqb b c && Z.leb kk k && Z.leb (k + m) (kk + len)
  | _ => false
  end.

Definition is_kimg_cov (a n : Z) (K : kentry) : bool :=
  match K with
  | KImg lo hi => Z.leb lo a && Z.leb (a + n) hi
  | _ => false
  end.

Lemma rdn_agree : forall segs M M' n (a : word),
  (forall j, (j < n)%nat -> M (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = M' (Z_to_bv 64 (bv_unsigned a + Z.of_nat j))) ->
  rdn segs M a n = rdn segs M' a n.
Proof.
  intros segs M M' n. induction n as [|n IH]; intros a Hag; [reflexivity|].
  cbn [rdn].
  pose proof (Hag 0%nat ltac:(lia)) as H0.
  rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned in H0. rewrite H0.
  rewrite (IH (a + 1)); [reflexivity|].
  intros j Hj. rewrite w_add_1.
  pose proof (u64_range a) as Ha.
  destruct (Z_lt_le_dec (bv_unsigned a + 1) (2 ^ 64)) as [Hlt | Hge].
  - rewrite u_small by lia.
    replace (bv_unsigned a + 1 + Z.of_nat j)%Z with (bv_unsigned a + Z.of_nat (S j))%Z by lia.
    apply Hag. lia.
  - replace (Z_to_bv 64 (bv_unsigned a + 1)) with (Z_to_bv 64 0)
      by (apply bv_eq; rewrite !Z_to_bv_unsigned, !bv_wrap64_mod; replace (bv_unsigned a + 1)%Z with (2^64)%Z by lia; reflexivity).
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
    specialize (Hag (S j) ltac:(lia)).
    replace (bv_unsigned a + Z.of_nat (S j))%Z with (2 ^ 64 + Z.of_nat j)%Z in Hag by lia.
    replace (Z_to_bv 64 (2 ^ 64 + Z.of_nat j)) with (Z_to_bv 64 (0 + Z.of_nat j)) in Hag; [exact Hag|].
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
    rewrite <- (Zplus_mod_idemp_l (2 ^ 64) (Z.of_nat j)), Z_mod_same_full. reflexivity.
Qed.

Lemma rdn_untouched : forall segs M (a : Z) n,
  (0 <= a)%Z -> (a + Z.of_nat n <= 2 ^ 64)%Z ->
  (forall i, (a <= i < a + Z.of_nat n)%Z -> M (Z_to_bv 64 i) = None) ->
  rdn segs M (Z_to_bv 64 a) n = rdn segs (fun _ => None) (Z_to_bv 64 a) n.
Proof.
  intros segs M a n H0 Hnw Hnone. apply rdn_agree. intros j Hj.
  rewrite u_small by lia. rewrite Hnone by lia. reflexivity.
Qed.

Lemma kimg_rdn : forall segs E M kn i lo hi (a : Z) n,
  know_ok segs E M kn -> nth_error kn i = Some (KImg lo hi) ->
  (lo <= a)%Z -> (a + Z.of_nat n <= hi)%Z ->
  rdn segs M (Z_to_bv 64 a) n = rdn segs (fun _ => None) (Z_to_bv 64 a) n.
Proof.
  intros segs E M kn i lo hi a n HK Hn Hlo Hhi.
  pose proof (know_nth segs E M kn i _ HK Hn) as (H0 & H64 & Hnone).
  apply rdn_untouched; [lia | lia |]. intros j Hj. apply Hnone. lia.
Qed.

Lemma kwr_store_ok : forall segs E M kn i b kk len (k : Z) (m : nat),
  know_ok segs E M kn -> nth_error kn i = Some (KWr (SA b kk) len) ->
  (kk <= k)%Z -> (k + Z.of_nat m <= kk + len)%Z ->
  store_ok segs M (adenot E (SA b k)) m = true.
Proof.
  intros segs E M kn i b kk len k m HK Hn H1 H2.
  pose proof (know_nth segs E M kn i _ HK Hn) as (Hfl & Hst).
  unfold adenot. cbn [a_base a_off].
  destruct Hfl as (F1 & F2 & F3 & F4). unfold estart in *. cbn [a_base a_off] in *.
  specialize (Hst (k - kk)%Z m ltac:(lia) ltac:(lia)).
  replace (bv_unsigned (edenot E b) + kk + (k - kk))%Z with (bv_unsigned (edenot E b) + k)%Z in Hst by lia.
  unfold v_addi. exact Hst.
Qed.

Definition entry_below_b (spi : nat) (ihi : Z) (e : sentry) : bool :=
  match e with
  | SE (SA (EVar i) k) w _ => Nat.eqb i spi && Z.leb (k + Z.of_nat w) 0 && Z.leb (- 2 ^ 40) k
  | SE (SA (ELit 0) k) w _ => Z.leb 0 k && Z.leb (k + Z.of_nat w) ihi
  | _ => false
  end.

Definition log_below_b (spi : nat) (ihi : Z) (log : list sentry) : bool :=
  forallb (entry_below_b spi ihi) log.

Fixpoint esub (f t : expr) (e : expr) : expr :=
  if expr_eqb e f then t else
  match e with
  | EAlu op a b => EAlu op (esub f t a) (esub f t b)
  | EAluw op a b => EAluw op (esub f t a) (esub f t b)
  | EMd op a b => EMd op (esub f t a) (esub f t b)
  | EMdw op a b => EMdw op (esub f t a) (esub f t b)
  | EExt sx lo n a => EExt sx lo n (esub f t a)
  | _ => e
  end.

Definition asub (f t : expr) (a : saddr) : saddr := SA (esub f t (a_base a)) (a_off a).

Definition ksub (f t : expr) (K : kentry) : kentry :=
  match K with
  | KWord a w v => KWord (asub f t a) w (esub f t v)
  | KZero a n => KZero (asub f t a) (esub f t n)
  | KBlob a n bk => KBlob (asub f t a) (esub f t n) bk
  | KImg lo hi => K
  | KAlign e m => KAlign (esub f t e) m
  | KRange e lo hi => KRange (esub f t e) lo hi
  | KWr a n => KWr (asub f t a) n
  | KDisj a1 n1 a2 n2 => KDisj (asub f t a1) n1 (asub f t a2) n2
  end.

Lemma regs_ok_ext : forall E sr sr' R,
  length sr = length sr' ->
  (forall i, (i < length sr)%nat -> edenot E (nth i sr (ELit 0)) = edenot E (nth i sr' (ELit 0))) ->
  regs_ok E sr R -> regs_ok E sr' R.
Proof.
  intros E sr sr' R Hlen Heq HR r. rewrite (HR r). unfold sr_get.
  destruct (bv_eqb r 0); [reflexivity|].
  destruct (Nat.lt_ge_cases (ridx r) (length sr)) as [Hlt | Hge].
  - apply Heq. exact Hlt.
  - rewrite !nth_overflow by lia. reflexivity.
Qed.

Lemma junk_vals_length : forall R, length (junk_vals R) = 32%nat.
Proof. intros R. unfold junk_vals. rewrite length_map, length_seq. reflexivity. Qed.

Lemma vals_ev_app_l : forall vals extra n, (n < length vals)%nat ->
  vals_ev (vals ++ extra) n = vals_ev vals n.
Proof. intros. unfold vals_ev. rewrite app_nth1 by assumption. reflexivity. Qed.

Lemma vals_ev_app_r : forall vals extra n,
  vals_ev (vals ++ extra) (length vals + n) = vals_ev extra n.
Proof. intros. unfold vals_ev. rewrite app_nth2_plus. reflexivity. Qed.

Lemma env_app_know : forall segs vals extra ebs M kn,
  kn_vars_lt (length vals) kn = true ->
  know_ok segs (Env (vals_ev vals) ebs) M kn -> know_ok segs (Env (vals_ev (vals ++ extra)) ebs) M kn.
Proof. intros. eapply know_ok_agree; [apply vals_app_agree | eassumption | eassumption]. Qed.

Lemma env_app_regs : forall vals extra ebs sr R,
  sr_vars_lt (length vals) sr = true ->
  regs_ok (Env (vals_ev vals) ebs) sr R -> regs_ok (Env (vals_ev (vals ++ extra)) ebs) sr R.
Proof. intros. eapply regs_ok_agree; [apply vals_app_agree | eassumption | eassumption]. Qed.

Lemma regs_after_keeps : forall vals ebs sr R R' (kept : list reg),
  sr_vars_lt (length vals) sr = true ->
  regs_ok (Env (vals_ev vals) ebs) sr R ->
  (forall r : reg, In r kept -> getr R' r = getr R r) ->
  ~ In 0%bv kept ->
  regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs)
          (sr_after_call_j sr (map ridx kept) (length vals)) R'.
Proof.
  intros vals ebs sr R R' kept Hlt HR Hk H0.
  apply (regs_after_call vals ebs sr R R' (map ridx kept) Hlt HR).
  - intros i Hi. apply in_map_iff in Hi as (r & <- & Hr). split; [apply ridx_range|].
    rewrite ridx_roundtrip. apply Hk. exact Hr.
  - intros Hin. apply in_map_iff in Hin as (r & Hr0 & Hr). apply H0.
    replace 0%bv with r; [exact Hr|]. apply ridx_inj. rewrite Hr0. reflexivity.
Qed.

Lemma know_after_store : forall segs E M kn sa w v bs kn' scs hs,
  carry [SE sa w v] kn [] = (kn', scs, hs) -> scs = [] ->
  know_ok segs E M kn -> (w <= 8)%nat -> flat E sa (Z.of_nat w) ->
  bs = word_to_le_bytes w (edenot E v) ->
  know_ok segs E (wbytes M (adenot E sa) bs) kn'.
Proof.
  intros segs E M kn sa w v bs kn' scs hs Hc -> HK Hw Hfl ->.
  change (wbytes M (adenot E sa) (word_to_le_bytes w (edenot E v))) with (mem_denot E M [SE sa w v]).
  eapply carry_after; [exact Hc | | exact HK | constructor].
  cbn [log_flat]. auto.
Qed.

Lemma flat_intro : forall E b k n,
  (0 <= bv_unsigned (edenot E b) + k)%Z -> (0 <= n)%Z ->
  (bv_unsigned (edenot E b) + k < 2 ^ 64)%Z ->
  (bv_unsigned (edenot E b) + k + n <= 2 ^ 64)%Z ->
  flat E (SA b k) n.
Proof. intros. unfold flat, estart. cbn [a_base a_off]. lia. Qed.

Definition ECALLW : bv 32 := Z_to_bv 32 0x73.
Lemma is_ecall_ECALLW : is_ecall ECALLW = true. Proof. reflexivity. Qed.

Lemma adenot_lit0 : forall E a, adenot E (SA (ELit 0) a) = Z_to_bv 64 a.
Proof. intros. unfold adenot, v_addi. cbn [a_base a_off edenot]. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_l. reflexivity. Qed.

Lemma edenot_add_lit : forall E b k, edenot E (EAlu ALU_ADD b (ELit k)) = adenot E (SA b k).
Proof.
  intros. cbn [edenot]. rewrite alu_add. unfold adenot, v_addi, v_add. cbn [a_base a_off].
  apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. apply Zplus_mod_idemp_r.
Qed.

Ltac split_foralls :=
  repeat lazymatch goal with
  | |- scs_denot _ _ _ [] => constructor
  | |- scs_denot _ _ _ (_ :: _) => constructor; [| ]
  | |- Forall _ [] => constructor
  | |- Forall _ (_ :: _) => constructor; [| ]
  end.

Ltac run_block_with HR HK fuel stops scr NX keep :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
    lazymatch type of HK with
    | know_ok ?segs _ ?M ?kn =>
      lazymatch goal with
      | |- realizes _ (mkCfg (mkst R (Z_to_bv 64 ?pc) M ?rom) ?model) ?T =>
        let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn NX) []) in
        lazymatch r with
        | (?ss', ?scs, ?scr') =>
          let c := eval vm_compute in (carry (s_log ss') kn []) in
          lazymatch c with
          | (?kn', ?scs2, ?hs2) =>
            eapply (rz_run segs fuel stops scr pc sr kn NX ss' scs scr' kn' scs2 hs2 E M rom R model T);

            [ vm_cast_no_check (@eq_refl _ (ss', scs, scr'))
            | vm_cast_no_check (@eq_refl _ (kn', scs2, hs2))
            | exact HR | exact HK
            | split_foralls
            | split_foralls
            | try reflexivity; try assumption
            | try reflexivity; try assumption
            | clear HR HK;
              let R' := fresh "R" in let M' := fresh "M" in let EQM := fresh "EQM" in
              intros R' M' HR HK EQM; cbn [s_pc s_regs s_log] in HR, EQM |- *;
              lazymatch keep with
              | true => idtac
              | false => clear EQM; try clear R; try clear M;
                         try rename R' into R; try rename M' into M
              end ]
          end
        end
      end
    end
  end.

Tactic Notation "run_block_gen" constr(fuel) constr(stops) constr(scr) constr(NX) constr(keep) :=
  match goal with
  | HR : regs_ok _ _ _, HK : know_ok _ _ _ _ |- _ => run_block_with HR HK fuel stops scr NX keep
  end.

Ltac regv HR r :=
  lazymatch type of HR with regs_ok ?E ?sr ?R =>
    let e := eval vm_compute in (sr_get sr r) in
    rewrite (reg_val E sr R r HR); change (sr_get sr r) with e;
    lazymatch e with ELit _ => cbn [edenot] | _ => idtac end
  end.

Ltac krd HK a n H :=
  lazymatch type of HK with
  | know_ok ?segs ?E ?M ?kn =>
    let r := eval vm_compute in (kread segs kn (ELit 0) a n) in
    lazymatch r with
    | Some ?v =>
        pose proof (kread_rdn segs E M kn (ELit 0) a n v HK
                      ltac:(vm_cast_no_check (@eq_refl _ (Some v))) ltac:(lia) ltac:(lia)
                      ltac:(unfold flat, estart; cbn [a_base a_off edenot];
                            change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia)) as H;
        rewrite adenot_lit0 in H; cbn [edenot] in H
    | None => fail "krd: knowledge does not determine this read"
    end
  end.

Ltac krdv HK i k n H :=
  lazymatch type of HK with
  | know_ok ?segs ?E ?M ?kn =>
    let r := eval vm_compute in (kread segs kn (EVar i) k n) in
    lazymatch r with
    | Some ?v =>
        let Hf := fresh "Hflat" in
        assert (Hf : flat E (SA (EVar i) k) (Z.of_nat n));
        [ | pose proof (kread_rdn segs E M kn (EVar i) k n v HK
                          ltac:(vm_cast_no_check (@eq_refl _ (Some v))) ltac:(lia) ltac:(lia) Hf) as H;
            clear Hf; cbn [edenot] in H ]
    | None => fail "krdv: knowledge does not determine this read"
    end
  end.

Ltac kidx kn p :=
  let r := eval vm_compute in (kindex p kn 0) in
  lazymatch r with Some ?i => i | None => fail "kidx: no such entry" end.

Ltac krd_solve HK :=
  lazymatch goal with
  | |- rdn _ _ (Z_to_bv 64 ?a) ?n = Some _ =>
      let H := fresh "Hrd" in
      krd HK a n H; rewrite H; clear H;
      first [ reflexivity | rewrite ?Z_to_bv_bv_unsigned; reflexivity | idtac ]
  end.

Lemma callee_kept_no0 : ~ In (0%bv : reg) callee_kept.
Proof.
  unfold callee_kept. intros Hin.
  repeat (destruct Hin as [Hin|Hin]; [apply (f_equal bv_unsigned) in Hin; cbn in Hin; discriminate Hin|]).
  exact Hin.
Qed.

Definition kentry_apart_b (allkn : list kentry) (ub : expr) (uk un : Z) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => ranges_apart allkn ub uk un b k (Z.of_nat w)
  | KZero (SA b k) (ELit l) => Z.leb 0 l && Z.ltb l (2 ^ 64) && ranges_apart allkn ub uk un b k l
  | KBlob (SA b k) (ELit l) _ => Z.leb 0 l && Z.ltb l (2 ^ 64) && ranges_apart allkn ub uk un b k l
  | KImg _ _ => true
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KDisj _ _ _ _ => true
  | KWr (SA b k) n => ranges_apart allkn ub uk un b k n
  | _ => false
  end.

Definition kn_unfill (kn : list kentry) (ub : expr) (uk un : Z) : list kentry :=
  List.filter (kentry_apart_b kn ub uk un) kn.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
