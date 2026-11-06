(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare ShapeAlg SRealizes RefMemcpyLib LibIface
  ZStores SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma u64_of_Z : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply u_Z2bv; lia. Qed.

Lemma v_addi_Z : forall a k, 0 <= a < 2 ^ 64 ->
  v_addi (Z_to_bv 64 a) k = Z_to_bv 64 (a + k).
Proof. intros a k Ha. unfold v_addi. rewrite u64_of_Z by lia. reflexivity. Qed.

Definition Eseed (R : bvmap 5 word) (vals : list word) : env :=
  Env (reg_ev R (fun n => nth (N.to_nat n - 32) vals (Z_to_bv 64 0))) (fun _ => []).

Lemma Eseed_reg : forall R vals (n : N), (n < 32)%N ->
  ev (Eseed R vals) n = getr R (Z_to_bv 5 (Z.of_N n)).
Proof.
  intros R vals n Hn. unfold Eseed, reg_ev. cbn [ev].
  destruct (N.ltb_spec n 32); [reflexivity | lia].
Qed.

Lemma Eseed_regZ : forall R vals (r : reg),
  ev (Eseed R vals) (Z.to_N (bv_unsigned r)) = getr R r.
Proof.
  intros R vals r. pose proof (u5_range r). rewrite Eseed_reg by lia.
  f_equal. rewrite Z2N.id by lia. apply Z_to_bv_bv_unsigned.
Qed.

Tactic Notation "evreg" constr(E) constr(R) constr(k) uconstr(r) :=
  let r' := constr:(r : reg) in
  replace (ev E k) with (getr R r') by (symmetry; exact (Eseed_regZ R _ r')).

Lemma regs_ok_seed : forall R vals, regs_ok (Eseed R vals) sr_id R.
Proof. intros R vals. unfold Eseed. apply regs_ok_id. Qed.

Lemma regs_ok_know : forall E sr R (rd : reg) e,
  regs_ok E sr R -> rd <> 0%bv -> getr R rd = edenot E e ->
  regs_ok E (sr_upd sr (ridx rd) e) R.
Proof.
  intros E sr R rd e HR Hrd He r. unfold sr_get.
  destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. apply getr_zero.
  - rewrite nth_sr_upd. destruct (Nat.eqb_spec (ridx r) (ridx rd)) as [Heq|Hne].
    + apply ridx_inj in Heq. subst r. exact He.
    + rewrite (HR r). unfold sr_get. rewrite Hr0. reflexivity.
Qed.

Lemma reg_lit : forall E sr R (r : reg) z,
  regs_ok E sr R -> sr_get sr r = ELit z -> getr R r = Z_to_bv 64 z.
Proof. intros E sr R r z HR Hs. rewrite (HR r), Hs. reflexivity. Qed.

Definition syms_id (sr : list expr) (l : list reg) : bool :=
  forallb (fun r : reg => expr_eqb (sr_get sr r) (EVar (Z.to_N (bv_unsigned r)))) l.

Lemma syms_id_sound : forall R vals sr R' l,
  regs_ok (Eseed R vals) sr R' -> syms_id sr l = true -> forall r, In r l -> getr R' r = getr R r.
Proof.
  intros R vals sr R' l HR Hk r Hr.
  pose proof (ZStores.forallb_In _ _ r Hk Hr) as H. apply expr_eqb_eq in H.
  pose proof (u5_range r) as Hr5.
  rewrite (HR r), H. cbn [edenot]. rewrite Eseed_reg by lia.
  f_equal. rewrite Z2N.id by lia. apply Z_to_bv_bv_unsigned.
Qed.

Definition kept_syms (sr : list expr) : bool := syms_id sr callee_saved.

Lemma kept_of_syms : forall R vals sr R',
  regs_ok (Eseed R vals) sr R' -> kept_syms sr = true -> keeps_cs R R'.
Proof. intros R vals sr R' HR Hk r Hr. exact (syms_id_sound R vals sr R' _ HR Hk r Hr). Qed.

Definition non_arg : list reg :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition aonly (R R' : bvmap 5 word) : Prop := forall r, In r non_arg -> getr R' r = getr R r.

Lemma aonly_trans : forall R1 R2 R3, aonly R1 R2 -> aonly R2 R3 -> aonly R1 R3.
Proof. intros R1 R2 R3 A B r Hr. rewrite (B r Hr). apply A, Hr. Qed.
Lemma aonly_kept : forall R R', aonly R R' -> keeps_cs R R'.
Proof. intros R R' A r Hr. apply A. cbn in Hr |- *. tauto. Qed.
Lemma aonly_of_syms : forall R vals sr R',
  regs_ok (Eseed R vals) sr R' -> syms_id sr non_arg = true -> aonly R R'.
Proof. intros R vals sr R' HR Hk r Hr. exact (syms_id_sound R vals sr R' _ HR Hk r Hr). Qed.

Fixpoint srs (sr : list expr) (l : list (reg * expr)) : list expr :=
  match l with [] => sr | (r, e) :: t => srs (sr_upd sr (ridx r) e) t end.

Lemma regs_ok_srs : forall E R l sr,
  regs_ok E sr R ->
  Forall (fun re => fst re <> 0%bv /\ getr R (fst re) = edenot E (snd re)) l ->
  regs_ok E (srs sr l) R.
Proof.
  intros E R l. induction l as [|[r e] t IH]; intros sr HR Hl; cbn; [exact HR|].
  apply Forall_cons_iff in Hl. destruct Hl as [[Hr He] Ht].
  apply IH; [|exact Ht]. apply regs_ok_know; assumption.
Qed.

Section K.
Context {AC : AllocCeiling}.
Variable SEGS : list Segment.

Lemma kword_abs : forall E M (a : Z) (w : N) (v : Z) (e : expr),
  cellw SEGS M a w v -> (w <= 8)%N -> 0 <= a < 2 ^ 64 -> a + Z.of_N w <= 2 ^ 64 ->
  edenot E e = Z_to_bv 64 v ->
  kentry_ok SEGS E M (KWord (SA (ELit 0) a) (N.to_nat w) e).
Proof using SEGS.
  intros E M a w v e [Hv Hr] Hw Ha Haw He. cbn [kentry_ok]. rewrite !N_nat_Z.
  split; [lia|]. split.
  - unfold flat, estart. cbn [a_base a_off edenot]. rewrite Z_to_bv_unsigned, bv_wrap64_mod, Z.mod_0_l by lia. lia.
  - unfold adenot. cbn [a_base a_off edenot]. rewrite He.
    rewrite v_addi_Z by lia. rewrite Z.add_0_l. exact Hr.
Qed.

Lemma kword_var : forall E M (n : N) (base off : Z) (w : N) (v : Z) (e : expr),
  cellw SEGS M (base + off) w v -> (w <= 8)%N ->
  ev E n = Z_to_bv 64 base -> 0 <= base < 2 ^ 64 -> 0 <= base + off < 2 ^ 64 -> base + off + Z.of_N w <= 2 ^ 64 ->
  edenot E e = Z_to_bv 64 v ->
  kentry_ok SEGS E M (KWord (SA (EVar n) off) (N.to_nat w) e).
Proof using SEGS.
  intros E M n base off w v e [Hv Hr] Hw Hn Hb Hbo Hbow He. cbn [kentry_ok]. rewrite !N_nat_Z.
  split; [lia|]. split.
  - unfold flat, estart. cbn [a_base a_off edenot]. rewrite Hn, u64_of_Z by lia. lia.
  - unfold adenot. cbn [a_base a_off edenot]. rewrite Hn, He, v_addi_Z by lia. exact Hr.
Qed.

Lemma krange_var : forall E M (n : N) (z lo hi : Z),
  ev E n = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> lo <= z <= hi ->
  kentry_ok SEGS E M (KRange (EVar n) lo hi).
Proof using SEGS. intros E M n z lo hi Hn Hz Hr. cbn [kentry_ok edenot]. rewrite Hn, u64_of_Z by lia. lia. Qed.

Lemma kalign_var : forall E M (n : N) (z m : Z),
  ev E n = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> 0 < m -> z mod m = 0 ->
  kentry_ok SEGS E M (KAlign (EVar n) m).
Proof using SEGS. intros E M n z m Hn Hz Hm Hr. cbn [kentry_ok edenot]. rewrite Hn, u64_of_Z by lia. lia. Qed.

Lemma kimg_abs : forall E M lo hi,
  0 <= lo -> hi <= 2 ^ 64 -> (forall i, lo <= i < hi -> M (Z_to_bv 64 i) = None) ->
  kentry_ok SEGS E M (KImg lo hi).
Proof using SEGS. intros E M lo hi Hlo Hhi H. cbn [kentry_ok]. repeat split; assumption. Qed.

Lemma kwr_stack_sub : forall E M (n : N) (sp S k off : Z),
  ev E n = Z_to_bv 64 sp -> off = - k -> 0 <= k <= S -> S <= sp -> sp < 2 ^ 64 ->
  stack_room SEGS M sp S ->
  kentry_ok SEGS E M (KWr (SA (EVar n) off) (ELit k)).
Proof using SEGS.
  intros E M n sp S k off Hn -> Hk HS Hsp Hroom. cbn [kentry_ok].
  unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite Hn, !u64_of_Z by lia.
  split; [lia|]. intros d m Hd Hdm.
  unfold stack_room in Hroom.
  eapply store_ok_sub; [ | exact Hroom | | ]; rewrite ?u64_of_Z by lia; lia.
Qed.

Lemma kdisj_vars : forall E M (n1 n2 : N) (b1 b2 o1 o2 l1 l2 : Z),
  ev E n1 = Z_to_bv 64 b1 -> ev E n2 = Z_to_bv 64 b2 -> 0 <= b1 < 2 ^ 64 -> 0 <= b2 < 2 ^ 64 ->
  0 <= l1 < 2 ^ 64 -> 0 <= l2 < 2 ^ 64 ->
  (b1 + o1 + l1 <= b2 + o2 \/ b2 + o2 + l2 <= b1 + o1) ->
  kentry_ok SEGS E M (KDisj (SA (EVar n1) o1) (ELit l1) (SA (EVar n2) o2) (ELit l2)).
Proof using SEGS.
  intros E M n1 n2 b1 b2 o1 o2 l1 l2 H1 H2 Hb1 Hb2 Hl1 Hl2 H. cbn [kentry_ok].
  unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite H1, H2, !u64_of_Z by lia. exact H.
Qed.

Lemma kwr_stack : forall E M (n : N) (sp S off : Z),
  ev E n = Z_to_bv 64 sp -> off = - S -> 0 <= S <= sp -> sp < 2 ^ 64 ->
  stack_room SEGS M sp S ->
  kentry_ok SEGS E M (KWr (SA (EVar n) off) (ELit S)).
Proof using SEGS.
  intros E M n sp S off Hn -> HS Hsp Hroom. cbn [kentry_ok].
  unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite Hn, !u64_of_Z by lia.
  split; [lia|]. intros d m Hd Hdm.
  unfold stack_room in Hroom.
  eapply store_ok_sub; [ | exact Hroom | | ]; rewrite ?u64_of_Z by lia; lia.
Qed.
End K.

Ltac xrun HR HK fuel stops scr nx :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
    lazymatch type of HK with
    | know_ok ?segs _ ?M ?kn =>
      lazymatch goal with
      | |- context [@mkst ?fxg R (Z_to_bv 64 ?pc) M ?rom] =>
          let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn nx) []) in
          lazymatch r with
          | (?ss', ?scs, ?scr') =>
              let Hsc := fresh "Hsc" in
              assert (Hsc : scs_denot segs M E scs);
              [ | let R' := fresh "R'" in let HR' := fresh "HR'" in
                  let Hlf := fresh "Hlf" in let Hms := fresh "Hms" in
                  destruct (@run_sound fxg segs fuel stops scr pc sr kn nx ss' scs scr' E M rom R
                             ltac:(vm_cast_no_check (@eq_refl _ (ss', scs, scr'))) HR HK Hsc)
                    as (R' & HR' & Hlf & Hms);
                  clear Hsc; cbn [s_pc s_regs s_log mem_denot] in HR', Hlf, Hms ]
          end
      end
    end
  end.

Ltac evs :=
  repeat match goal with X := Eseed _ _ |- _ => subst X end;
  unfold adenot, estart, elenZ;
  cbn [edenot a_base a_off];
  unfold Eseed;
  lazy [ev eb reg_ev N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont
        N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op Init.Nat.add Nat.sub nth].

Ltac evs_in H :=
  repeat match goal with X := Eseed _ _ |- _ => subst X end;
  unfold adenot, estart, elenZ in H;
  cbn [edenot a_base a_off] in H;
  unfold Eseed in H;
  lazy [ev eb reg_ev N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont
        N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op Init.Nat.add Nat.sub nth] in H.

Ltac rreg_ HR r H :=
  lazymatch type of HR with regs_ok ?E ?sr ?R' =>
    let e := eval vm_compute in (sr_get sr r) in
    assert (H : getr R' r = edenot E e) by (exact (HR r));
    evs_in H
  end.
Tactic Notation "rreg" constr(HR) uconstr(r) ident(H) :=
  let r' := constr:(r : reg) in rreg_ HR r' H.

Lemma w_add : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= a + b < 2 ^ 64 ->
  alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b Ha Hb Hab. apply bv_eq. cbn [alu64 alu].
  rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite (Z.mod_small a), (Z.mod_small b), !Z.mod_small by lia. reflexivity.
Qed.

Lemma w_addm : forall a k, 0 <= a < 2 ^ 64 -> 0 <= a + k < 2 ^ 64 -> - 2 ^ 64 < k < 0 ->
  alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 k) = Z_to_bv 64 (a + k).
Proof.
  intros a k Ha Hak Hk. apply bv_eq. cbn [alu64 alu].
  rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite (Z.mod_small a) by lia.
  replace (k mod 2 ^ 64) with (k + 2 ^ 64).
  2:{ rewrite <- (Z.mod_add k 1 (2 ^ 64)) by lia. symmetry. apply Z.mod_small. lia. }
  replace (a + (k + 2 ^ 64)) with ((a + k) + 1 * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. rewrite !Z.mod_small by lia. reflexivity.
Qed.

Lemma w_and : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  alu64 ALU_AND (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (Z.land a b).
Proof.
  intros a b Ha Hb. apply bv_eq. cbn [alu64 alu].
  rewrite bv_and_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite (Z.mod_small a), (Z.mod_small b) by lia.
  assert (0 <= Z.land a b < 2 ^ 64).
  { split; [apply Z.land_nonneg; lia|].
    apply (Z.le_lt_trans _ a); [|lia]. apply land_le_l; lia. }
  rewrite !Z.mod_small by lia. reflexivity.
Qed.

Lemma w_mul : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= a * b < 2 ^ 64 ->
  mul_div M_MUL (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
Proof.
  intros a b Ha Hb Hab. apply bv_eq. cbn [mul_div].
  rewrite bv_mul_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite (Z.mod_small a), (Z.mod_small b), !Z.mod_small by lia. reflexivity.
Qed.

Lemma w_remu : forall a b, 0 <= a < 2 ^ 64 -> 0 < b < 2 ^ 64 ->
  mul_div M_REMU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a mod b).
Proof.
  intros a b Ha Hb. cbn [mul_div]. rewrite Z_to_bv_unsigned, bv_wrap64_mod, (Z.mod_small b) by lia.
  destruct (Z.eqb_spec b 0); [lia|].
  apply bv_eq. rewrite bv_modu_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  pose proof (Z.mod_pos_bound a b ltac:(lia)).
  rewrite (Z.mod_small a), (Z.mod_small b), (Z.mod_small (a mod b)) by lia. reflexivity.
Qed.

Lemma br_eq : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_EQ (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. cbn [branch_taken]. unfold bv_eqb. rewrite !u64_of_Z by lia. reflexivity. Qed.
Lemma br_ne : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_NE (Z_to_bv 64 x) (Z_to_bv 64 y) = negb (x =? y).
Proof. intros x y Hx Hy. cbn [branch_taken]. unfold bv_eqb. rewrite !u64_of_Z by lia. reflexivity. Qed.
Lemma br_ltu : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_LTU (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. cbn [branch_taken]. unfold bv_ltu. rewrite !u64_of_Z by lia. reflexivity. Qed.
Lemma br_geu : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_GEU (Z_to_bv 64 x) (Z_to_bv 64 y) = negb (x <? y).
Proof. intros x y Hx Hy. cbn [branch_taken]. unfold bv_ltu. rewrite !u64_of_Z by lia. reflexivity. Qed.

Section SC.
Context {AC : AllocCeiling}.
Variable SEGS : list Segment.

Lemma extz_false : forall n u, extz false n u = u.
Proof using. reflexivity. Qed.

Lemma sc_read_cellw : forall E M (sa : saddr) (a : Z) (w : N) (v : Z) (e : expr),
  cellw SEGS M a w v -> (w <= 8)%N ->
  adenot E sa = Z_to_bv 64 a -> edenot E e = Z_to_bv 64 v ->
  sc_denot SEGS M E (SCReadBase sa (N.to_nat w) false e).
Proof using SEGS.
  intros E M sa a w v e [Hv Hr] Hw Ha He. cbn [sc_denot].
  exists (word_to_le_bytes (N.to_nat w) (Z_to_bv 64 v)). rewrite Ha, He. split; [exact Hr|].
  rewrite extz_false, bytes_le_N, N_nat_Z.
  assert (Hw64 : 2 ^ (8 * Z.of_N w) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  rewrite u64_of_Z by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma sc_flat : forall M E (sa : saddr) (b n : Z),
  edenot E (a_base sa) = Z_to_bv 64 b -> 0 <= b < 2 ^ 64 -> 0 <= b + a_off sa < 2 ^ 64 ->
  0 <= n < 2 ^ 64 -> b + a_off sa + n <= 2 ^ 64 ->
  sc_denot SEGS M E (SCFlat sa (ELit n)).
Proof using SEGS.
  intros M E sa b n Hb Hbr H0 Hn Han. cbn [sc_denot]. unfold flat, estart, elenZ. cbn [edenot].
  rewrite Hb. rewrite (u64_of_Z b), (u64_of_Z n) by lia. lia.
Qed.

Lemma adenot_Z : forall E (sa : saddr) (b : Z),
  edenot E (a_base sa) = Z_to_bv 64 b -> 0 <= b < 2 ^ 64 ->
  adenot E sa = Z_to_bv 64 (b + a_off sa).
Proof using. intros E sa b Hb Hr. unfold adenot. rewrite Hb, v_addi_Z by lia. reflexivity. Qed.
End SC.

Ltac bool_lia :=
  first [ reflexivity
        | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia
        | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia
        | apply (proj2 (Bool.negb_true_iff _)); bool_lia
        | apply (proj2 (Bool.negb_false_iff _)); bool_lia ].

Ltac sc_br := cbn [sc_denot]; evs; rewrite ?br_eq, ?br_ne, ?br_ltu, ?br_geu by lia; bool_lia.

Ltac sc_rd H :=
  eapply (sc_read_cellw _ _ _ _ _ _ _ _ H);
  [ cbn; lia
  | evs; rewrite ?v_addi_Z by lia; first [reflexivity | f_equal; lia]
  | evs; first [reflexivity | f_equal; lia] ].

Ltac sc_fl := eapply sc_flat; [evs; reflexivity | lia | cbn [a_off]; lia | lia | cbn [a_off]; lia].

Ltac sc_auto1 :=
  first [ sc_fl | sc_br
        | match goal with H : cellw _ _ _ _ _ |- _ => sc_rd H end
        | match goal with H : cell8 _ _ _ _ |- _ => unfold cell8 in H; sc_rd H end
        | match goal with H : cell4 _ _ _ _ |- _ => unfold cell4 in H; sc_rd H end
        | idtac ].

Definition sxw (k : Z) : word := Z_to_bv 64 (bv_swrap 32 k).

Lemma bv_swrap32_cases : forall k, 0 <= k < 2 ^ 32 ->
  bv_swrap 32 k = (if k <? 2 ^ 31 then k else k - 2 ^ 32).
Proof.
  intros k Hk. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  destruct (Z.ltb_spec k (2 ^ 31)).
  - rewrite Z.mod_small by lia. lia.
  - replace (k + 2 ^ 31) with ((k - 2 ^ 31) + 1 * 2 ^ 32) by lia.
    rewrite Z.mod_add, Z.mod_small by lia. lia.
Qed.

Lemma sxw_inj : forall k k', 0 <= k < 2 ^ 32 -> 0 <= k' < 2 ^ 32 -> sxw k = sxw k' -> k = k'.
Proof.
  intros k k' Hk Hk' H. unfold sxw in H.
  apply (f_equal bv_unsigned) in H. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod in H.
  rewrite !bv_swrap32_cases in H by lia.
  destruct (Z.ltb_spec k (2 ^ 31)); destruct (Z.ltb_spec k' (2 ^ 31)).
  - rewrite !Z.mod_small in H by lia. lia.
  - rewrite (Z.mod_small k) in H by lia.
    replace ((k' - 2 ^ 32) mod 2 ^ 64) with (k' - 2 ^ 32 + 2 ^ 64) in H; [lia|].
    rewrite <- (Z.mod_add _ 1) by lia. symmetry. apply Z.mod_small. lia.
  - rewrite (Z.mod_small k') in H by lia.
    replace ((k - 2 ^ 32) mod 2 ^ 64) with (k - 2 ^ 32 + 2 ^ 64) in H; [lia|].
    rewrite <- (Z.mod_add _ 1) by lia. symmetry. apply Z.mod_small. lia.
  - replace ((k' - 2 ^ 32) mod 2 ^ 64) with (k' - 2 ^ 32 + 2 ^ 64) in H.
    2:{ rewrite <- (Z.mod_add _ 1) by lia. symmetry. apply Z.mod_small. lia. }
    replace ((k - 2 ^ 32) mod 2 ^ 64) with (k - 2 ^ 32 + 2 ^ 64) in H.
    2:{ rewrite <- (Z.mod_add _ 1) by lia. symmetry. apply Z.mod_small. lia. }
    lia.
Qed.

Lemma br_eq_sxw : forall k k', 0 <= k < 2 ^ 32 -> 0 <= k' < 2 ^ 32 ->
  branch_taken BC_EQ (sxw k) (sxw k') = (k =? k').
Proof.
  intros k k' Hk Hk'. cbn [branch_taken]. unfold bv_eqb.
  destruct (Z.eqb_spec k k') as [->|Hne].
  - apply Z.eqb_refl.
  - apply Z.eqb_neq. intros H. apply Hne. apply sxw_inj; try lia. apply bv_eq. exact H.
Qed.
Lemma br_ne_sxw : forall k k', 0 <= k < 2 ^ 32 -> 0 <= k' < 2 ^ 32 ->
  branch_taken BC_NE (sxw k) (sxw k') = negb (k =? k').
Proof. intros k k' Hk Hk'. cbn [branch_taken]. rewrite <- br_eq_sxw by lia. reflexivity. Qed.

Lemma sextw_val : forall k, 0 <= k < 2 ^ 32 ->
  sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 k)) (low32 (Z_to_bv 64 0))) = sxw k.
Proof.
  intros k Hk. unfold sxw, sext. apply bv_eq.
  rewrite bv_sign_extend_unsigned, Z_to_bv_unsigned.
  f_equal. cbn [alu32 alu]. rewrite bv_add_signed.
  unfold low32. rewrite !bv_extract_signed, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite !Z.shiftr_0_r, (Z.mod_small k), Z.mod_0_l by lia.
  rewrite bv_swrap_0, Z.add_0_r.
  unfold bv_swrap. f_equal.
  replace (bv_wrap 32 (k + bv_half_modulus 32) - bv_half_modulus 32 + bv_half_modulus 32)
    with (bv_wrap 32 (k + bv_half_modulus 32)) by lia.
  apply bv_wrap_idemp.
Qed.

Section SC2.
Context {AC : AllocCeiling}.
Variable SEGS : list Segment.

Lemma sc_read_cell4_sx : forall E M (sa : saddr) (a v : Z) (e : expr),
  cell4 SEGS M a v ->
  adenot E sa = Z_to_bv 64 a -> edenot E e = sxw v ->
  sc_denot SEGS M E (SCReadBase sa 4 true e).
Proof using SEGS.
  intros E M sa a v e [Hv Hr] Ha He. cbn [sc_denot].
  exists (word_to_le_bytes 4 (Z_to_bv 64 v)). rewrite Ha, He. split; [exact Hr|].
  unfold extz, sxw. rewrite bytes_le_N. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32).
  rewrite u64_of_Z by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
End SC2.

Ltac sc_rd_sx H :=
  eapply (sc_read_cell4_sx _ _ _ _ _ _ _ H);
  [ evs; rewrite ?v_addi_Z by lia; first [reflexivity | f_equal; lia]
  | evs; first [reflexivity | f_equal; lia] ].

Ltac sc_br ::= cbn [sc_denot]; evs;
  rewrite ?br_eq, ?br_ne, ?br_ltu, ?br_geu, ?br_eq_sxw, ?br_ne_sxw by lia; bool_lia.

Ltac xruns HR HK fuel stops scr nx :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
    lazymatch type of HK with
    | know_ok ?segs _ ?M ?kn =>
      lazymatch goal with
      | |- srealizes _ (mkCfg (@mkst ?fxg R (Z_to_bv 64 ?pc) M ?rom) ?model) _ =>
          let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn nx) []) in
          lazymatch r with
          | (?ss', ?scs, ?scr') =>
              let Hsc := fresh "Hsc" in
              assert (Hsc : scs_denot segs M E scs);
              [ | let R' := fresh "R'" in let HR' := fresh "HR'" in
                  let Hlf := fresh "Hlf" in let Hms := fresh "Hms" in
                  destruct (@run_sound fxg segs fuel stops scr pc sr kn nx ss' scs scr' E M rom R
                             ltac:(vm_cast_no_check (@eq_refl _ (ss', scs, scr'))) HR HK Hsc)
                    as (R' & HR' & Hlf & Hms);
                  clear Hsc; cbn [s_pc s_regs s_log mem_denot] in HR', Hlf, Hms;
                  eapply srz_msteps;
                  [ lazymatch goal with |- m_halted ?m = None => first [eapply ms_halt; eassumption | idtac] end
                  | lazymatch goal with |- m_vm_lazy ?m = [] => first [eapply ms_lazy; eassumption | idtac] end
                  | exact Hms
                  | clear Hms ] ]
          end
      end
    end
  end.

Section SO.
Context {AC : AllocCeiling}.
Variable SEGS : list Segment.
Lemma store_ok_of_defined : forall M (a n : Z),
  0 <= a < 2 ^ 64 -> a + n <= 2 ^ 64 -> defined M a n ->
  store_ok SEGS M (Z_to_bv 64 a) (Z.to_nat n) = true.
Proof using SEGS.
  intros M a n Ha Han Hd. destruct (Z.lt_ge_cases n 0).
  { replace (Z.to_nat n) with 0%nat by lia. reflexivity. }
  apply store_ok_of_all; rewrite u64_of_Z by lia; [lia|].
  intros x Hx Hw. unfold wview in Hw.
  specialize (Hd (bv_unsigned x - a) ltac:(lia)).
  replace (a + (bv_unsigned x - a)) with (bv_unsigned x) in Hd by lia. rewrite Z_to_bv_bv_unsigned in Hd.
  destruct (M x); [discriminate Hw | exact (Hd eq_refl)].
Qed.

Lemma sc_storeok : forall M E (sa : saddr) (b : Z) (n : nat),
  edenot E (a_base sa) = Z_to_bv 64 b -> 0 <= b < 2 ^ 64 -> 0 <= b + a_off sa ->
  b + a_off sa + Z.of_nat n <= 2 ^ 64 -> defined M (b + a_off sa) (Z.of_nat n) ->
  sc_denot SEGS M E (SCStoreOk sa n).
Proof using SEGS.
  intros M E sa b n Hb Hbr H0 Hn Hd. cbn [sc_denot]. unfold adenot. rewrite Hb, v_addi_Z by lia.
  destruct n as [|k]; [reflexivity|].
  rewrite <- (Nat2Z.id (S k)). apply store_ok_of_defined; [ lia | lia | exact Hd].
Qed.
End SO.

Ltac sc_so := eapply sc_storeok; [evs; reflexivity | lia | cbn [a_off]; lia | cbn [a_off]; lia | cbn [a_off] ].

Ltac inl := first [ solve [cbn [In]; repeat (first [left; reflexivity | right])] | cbn; repeat (first [left; reflexivity | right]) ].

Ltac ninl := cbn; let H := fresh in intros H; repeat (destruct H as [H|H]; [discriminate H|]); destruct H.
