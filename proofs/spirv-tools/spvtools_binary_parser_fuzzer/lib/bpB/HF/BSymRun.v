(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BCatSim BSeqExec BStoreOk BSymExec.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSymExec2 BSymExec2Sound.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition vals_ev (vals : list word) : nat -> word :=
  fun n => nth n vals (Z_to_bv 64 0).

Fixpoint expr_vars_lt (b : nat) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar n => Nat.ltb n b
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_vars_lt b x && expr_vars_lt b y
  | EExt _ _ _ x => expr_vars_lt b x
  | EBlob _ _ _ _ => true
  end.

Definition saddr_vars_lt (b : nat) (a : saddr) : bool := expr_vars_lt b (a_base a).

Fixpoint sr_vars_lt (b : nat) (sr : list expr) : bool :=
  match sr with [] => true | e :: r => expr_vars_lt b e && sr_vars_lt b r end.

Definition kentry_vars_lt (b : nat) (K : kentry) : bool :=
  match K with
  | KWord a _ v => saddr_vars_lt b a && expr_vars_lt b v
  | KZero a n => saddr_vars_lt b a && expr_vars_lt b n
  | KBlob a n _ => saddr_vars_lt b a && expr_vars_lt b n
  | KImg _ _ => true
  | KAlign e _ => expr_vars_lt b e
  | KRange e _ _ => expr_vars_lt b e
  | KWr a _ => saddr_vars_lt b a
  | KDisj a1 _ a2 _ => saddr_vars_lt b a1 && saddr_vars_lt b a2
  end.

Fixpoint kn_vars_lt (b : nat) (kn : list kentry) : bool :=
  match kn with [] => true | K :: r => kentry_vars_lt b K && kn_vars_lt b r end.

Fixpoint log_vars_lt (b : nat) (log : list sentry) : bool :=
  match log with
  | [] => true
  | SE a _ v :: r => saddr_vars_lt b a && expr_vars_lt b v && log_vars_lt b r
  end.

Definition env_agree (b : nat) (E E' : env) : Prop :=
  (forall n, (n < b)%nat -> ev E n = ev E' n) /\ eb E = eb E'.

Lemma edenot_agree : forall b E E' e,
  env_agree b E E' -> expr_vars_lt b e = true -> edenot E e = edenot E' e.
Proof.
  intros b E E' e [Hv Hb]. induction e; cbn [expr_vars_lt edenot]; intros H;
    repeat match goal with
      | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
      end;
    try reflexivity;
    try (rewrite IHe1, IHe2 by assumption; reflexivity);
    try (rewrite IHe by assumption; reflexivity).
  - apply Nat.ltb_lt in H. apply Hv. exact H.
  - rewrite Hb. reflexivity.
Qed.

Lemma adenot_agree : forall b E E' a,
  env_agree b E E' -> saddr_vars_lt b a = true -> adenot E a = adenot E' a.
Proof.
  intros b E E' a Ha H. unfold adenot. rewrite (edenot_agree b E E' _ Ha H). reflexivity.
Qed.

Lemma regs_ok_agree : forall b E E' sr regs,
  env_agree b E E' -> sr_vars_lt b sr = true -> regs_ok E sr regs -> regs_ok E' sr regs.
Proof.
  intros b E E' sr regs Ha Hsr HR r. rewrite (HR r).
  unfold sr_get. destruct (bv_eqb r 0); [reflexivity|].
  assert (Hnth : forall i, expr_vars_lt b (nth i sr (ELit 0)) = true).
  { clear HR r. induction sr as [|e t IH]; intros i.
    - destruct i; reflexivity.
    - cbn [sr_vars_lt] in Hsr. apply andb_prop in Hsr as [He Ht].
      destruct i; [exact He | apply IH; exact Ht]. }
  apply (edenot_agree b); [exact Ha | apply Hnth].
Qed.

Lemma flat_agree : forall b E E' a n,
  env_agree b E E' -> saddr_vars_lt b a = true -> flat E a n <-> flat E' a n.
Proof.
  intros b E E' a n Ha H. unfold flat, estart.
  rewrite (edenot_agree b E E' (a_base a) Ha H). tauto.
Qed.

Lemma know_ok_agree : forall segs b E E' base kn,
  env_agree b E E' -> kn_vars_lt b kn = true -> know_ok segs E base kn -> know_ok segs E' base kn.
Proof.
  intros segs b E E' base kn Ha. induction kn as [|K r IH]; cbn [kn_vars_lt]; intros H Hk.
  - constructor.
  - apply andb_prop in H as [HK Hr]. apply Forall_cons_iff in Hk as [Hk1 Hk2].
    constructor; [| apply IH; assumption].
    destruct Ha as [Hv Hb].
    destruct K as [a w v|a n|a n k|lo hi|ae am|re rlo rhi|wa wn|da1 dn1 da2 dn2]; cbn [kentry_vars_lt kentry_ok] in *;
      [ | | | | rewrite <- (edenot_agree b E E' ae (conj Hv Hb) HK); exact Hk1
              | rewrite <- (edenot_agree b E E' re (conj Hv Hb) HK); exact Hk1
              | unfold flat, estart in *; rewrite <- (edenot_agree b E E' (a_base wa) (conj Hv Hb) HK); exact Hk1
              | apply andb_prop in HK as [HK1 HK2]; unfold estart in *;
                rewrite <- (edenot_agree b E E' (a_base da1) (conj Hv Hb) HK1),
                        <- (edenot_agree b E E' (a_base da2) (conj Hv Hb) HK2); exact Hk1 ].
    + apply andb_prop in HK as [H1 H2].
      rewrite <- (adenot_agree b E E' a (conj Hv Hb) H1), <- (edenot_agree b E E' v (conj Hv Hb) H2).
      destruct Hk1 as (A & B & C). split; [exact A|]. split; [|exact C].
      apply (flat_agree b E E' a _ (conj Hv Hb) H1). exact B.
    + apply andb_prop in HK as [H1 H2]. unfold elenZ, estart in *.
      rewrite <- (edenot_agree b E E' n (conj Hv Hb) H2), <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1).
      destruct Hk1 as [A B]. split; [|exact B].
      unfold flat, estart in *. rewrite <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1). exact A.
    + apply andb_prop in HK as [H1 H2]. unfold elenZ, estart in *. rewrite <- Hb.
      rewrite <- (edenot_agree b E E' n (conj Hv Hb) H2), <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1).
      destruct Hk1 as (A & B & C). split; [|split; [exact B | exact C]].
      unfold flat, estart in *. rewrite <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1). exact A.
    + exact Hk1.
Qed.

Lemma vals_app_agree : forall vals extra ebs,
  env_agree (length vals) (Env (vals_ev vals) ebs) (Env (vals_ev (vals ++ extra)) ebs).
Proof.
  intros vals extra ebs. split; [|reflexivity]. intros n Hn. cbn [ev]. unfold vals_ev.
  rewrite app_nth1 by exact Hn. reflexivity.
Qed.

Section Run.
Context {fx : DFP}.
Variable segs : list Segment.

Lemma st_ok_entry : forall E base rom pc sr kn nx regs,
  regs_ok E sr regs -> know_ok segs E base kn ->
  st_ok segs E base rom (SS pc sr [] kn nx) (mkst regs (Z_to_bv 64 pc) base rom).
Proof.
  intros E base rom pc sr kn nx regs HR HK. exists regs. cbn [s_pc s_log s_regs s_know mem_denot].
  split; [reflexivity|]. split; [exact HR|]. split; [exact I | exact HK].
Qed.

Theorem run_sound : forall fuel stops scr pc sr kn nx ss' scs scr' E base rom regs,
  sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
  regs_ok E sr regs -> know_ok segs E base kn ->
  scs_denot segs base E scs ->
  exists R, regs_ok E (s_regs ss') R
         /\ log_flat E (s_log ss')
         /\ msteps segs (mkst regs (Z_to_bv 64 pc) base rom)
                        (mkst R (Z_to_bv 64 (s_pc ss')) (mem_denot E base (s_log ss')) rom).
Proof.
  intros fuel stops scr pc sr kn nx ss' scs scr' E base rom regs Hex HR HK Hsc.
  eapply sym_exec_ex; [exact Hex | exact Hsc | apply st_ok_entry; assumption].
Qed.

Theorem carry_after : forall E base log kn hints kn' scs hs',
  carry log kn hints = (kn', scs, hs') ->
  log_flat E log -> know_ok segs E base kn -> scs_denot segs base E scs ->
  know_ok segs E (mem_denot E base log) kn'.
Proof. intros. eapply carry_sound; eauto. Qed.

Lemma reg_val : forall E sr R (r : reg), regs_ok E sr R -> getr R r = edenot E (sr_get sr r).
Proof. intros E sr R r HR. apply HR. Qed.

Lemma regs_ok_set : forall E sr R (rd : reg) v e,
  regs_ok E sr R -> rd <> 0%bv -> edenot E e = v ->
  regs_ok E (sr_upd sr (ridx rd) e) (regupd R rd v).
Proof.
  intros E sr R rd v e HR Hrd He.
  pose proof (regs_ok_upd E sr R rd v e HR He) as H.
  assert (Hb : bv_eqb rd 0 = false).
  { unfold bv_eqb. apply Z.eqb_neq. intros Hc. apply Hrd. apply bv_eq. exact Hc. }
  rewrite Hb in H. exact H.
Qed.

End Run.

Definition sr_init : list expr :=
  [ELit 0; ELit 0; EVar 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0].

Definition stk_ok (segs : list Segment) (mem : word -> option byte) (sp : word) (K : Z) : Prop :=
  forall (a : word) (n : nat),
    (bv_unsigned sp - K <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp)%Z ->
    store_ok segs mem a n = true.

Lemma stk_ok_vaddi : forall segs mem sp K off n,
  stk_ok segs mem sp K -> (K <= bv_unsigned sp)%Z ->
  (- K <= off)%Z -> (off + Z.of_nat n <= 0)%Z ->
  store_ok segs mem (v_addi sp off) n = true.
Proof.
  intros segs mem sp K off n Hs HK H1 H2. pose proof (u64_range sp).
  apply Hs; unfold v_addi; rewrite u_small by lia; lia.
Qed.

Lemma stk_ok_lit : forall segs mem sp K z n,
  stk_ok segs mem sp K ->
  (bv_unsigned sp - K <= z)%Z -> (z + Z.of_nat n <= bv_unsigned sp)%Z -> (0 <= z)%Z ->
  store_ok segs mem (Z_to_bv 64 z) n = true.
Proof.
  intros segs mem sp K z n Hs H1 H2 H3. pose proof (u64_range sp).
  apply Hs; rewrite u_small by lia; lia.
Qed.

Lemma kwr_of_stk_ok : forall segs E mem (e : expr) (sp : word) K,
  edenot E e = sp -> stk_ok segs mem sp K -> (0 <= K <= bv_unsigned sp)%Z ->
  kentry_ok segs E mem (KWr (SA e (- K)) K).
Proof.
  intros segs E mem e sp K He Hs HK. cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off]. rewrite He.
  pose proof (u64_range sp). split; [lia|].
  intros d m Hd Hm. apply Hs; rewrite u_small by lia; lia.
Qed.

Lemma kword_intro : forall segs E mem (e : expr) (a : word) off w (v : expr) (x : word),
  edenot E e = a -> edenot E v = x -> (1 <= w)%nat -> (w <= 8)%nat ->
  (0 <= bv_unsigned a + off)%Z -> (bv_unsigned a + off + Z.of_nat w <= 2 ^ 64)%Z ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned a + off)) w = Some (word_to_le_bytes w x) ->
  kentry_ok segs E mem (KWord (SA e off) w v).
Proof.
  intros segs E mem e a off w v x He Hv Hw1 Hw H1 H2 Hr. cbn [kentry_ok]. unfold flat, estart, adenot, v_addi.
  cbn [a_base a_off]. rewrite He, Hv. split; [exact Hw|]. split; [lia | exact Hr].
Qed.

Lemma krange_intro : forall segs E mem (e : expr) lo hi,
  (lo <= bv_unsigned (edenot E e) <= hi)%Z -> kentry_ok segs E mem (KRange e lo hi).
Proof. intros. cbn [kentry_ok]. lia. Qed.

Lemma kalign_intro : forall segs E mem (e : expr) m,
  (0 < m)%Z -> (bv_unsigned (edenot E e) mod m = 0)%Z -> kentry_ok segs E mem (KAlign e m).
Proof. intros. cbn [kentry_ok]. auto. Qed.

Lemma kimg_intro : forall segs E mem lo hi,
  (0 <= lo)%Z -> (hi <= 2 ^ 64)%Z ->
  (forall i, (lo <= i < hi)%Z -> mem (Z_to_bv 64 i) = None) ->
  kentry_ok segs E mem (KImg lo hi).
Proof. intros. cbn [kentry_ok]. auto. Qed.

Lemma kzero_intro : forall segs E mem (e : expr) (a : word) off (n : expr) len,
  edenot E e = a -> bv_unsigned (edenot E n) = len ->
  (0 <= bv_unsigned a + off)%Z -> (0 < len)%Z -> (bv_unsigned a + off + len <= 2 ^ 64)%Z ->
  (forall i, (0 <= i < len)%Z -> mem (Z_to_bv 64 (bv_unsigned a + off + i)) = Some (Z_to_bv 8 0)) ->
  kentry_ok segs E mem (KZero (SA e off) n).
Proof.
  intros segs E mem e a off n len He Hn H1 H2 H3 Hz. cbn [kentry_ok]. unfold flat, elenZ, estart.
  cbn [a_base a_off]. rewrite He, Hn. split; [lia | exact Hz].
Qed.

Lemma ext_val_sx_id : forall n (v : word),
  (1 <= n)%nat -> (bv_unsigned v < 2 ^ (8 * Z.of_nat n - 1))%Z -> ext_val true 0 n v = v.
Proof.
  intros n v Hn Hv. unfold ext_val, ext_Z. pose proof (u64_range v).
  assert (Hp : (2 ^ (8 * Z.of_nat n - 1) * 2 = 2 ^ (8 * Z.of_nat n))%Z).
  { rewrite Z.mul_comm, <- Z.pow_succ_r by lia. f_equal. lia. }
  change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. rewrite Z.div_1_r, Z.mod_small by lia.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  replace (Z.of_N (8 * N.of_nat n)) with (8 * Z.of_nat n)%Z by lia.
  rewrite <- Hp. rewrite Z.div_mul by lia.
  rewrite Z.mod_small by lia. replace (bv_unsigned v + 2 ^ (8 * Z.of_nat n - 1) - 2 ^ (8 * Z.of_nat n - 1))%Z
    with (bv_unsigned v) by lia.
  apply Z_to_bv_bv_unsigned.
Qed.

Ltac split_scs :=
  lazymatch goal with
  | |- scs_denot _ _ _ [] => constructor
  | |- scs_denot _ _ _ (_ :: _) => constructor; [| split_scs]
  | |- Forall _ [] => constructor
  | |- Forall _ (_ :: _) => constructor; [| split_scs]
  end.

Ltac ground_mod :=
  repeat match goal with
  | |- context [ (?a mod ?b)%Z ] =>
      lazymatch a with
      | context [bv_unsigned _] => fail
      | _ => lazymatch b with
             | context [bv_unsigned _] => fail
             | _ => let v := eval vm_compute in (a mod b)%Z in change ((a mod b)%Z) with v
             end
      end
  end.

Ltac sc_unfold :=
  unfold sc_denot, flat, estart, elenZ, adenot;
  cbn [a_base a_off edenot ev eb vals_ev nth];
  rewrite ?Z_to_bv_unsigned, ?bv_wrap64_mod; ground_mod.

Ltac lit_u :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
      lazymatch z with
      | context [bv_unsigned _] => fail
      | _ => rewrite (u_small z) by (cbn; lia)
      end
  end.

Ltac sc_store :=
  match goal with
  | Hs : stk_ok _ _ _ _ |- store_ok _ _ (v_addi _ _) _ = true =>
      apply (stk_ok_vaddi _ _ _ _ _ _ Hs); lia
  | Hs : stk_ok _ _ _ _ |- store_ok _ _ (Z_to_bv 64 _) _ = true =>
      apply (stk_ok_lit _ _ _ _ _ _ Hs); lia
  end.

Ltac sc_auto extra :=
  sc_unfold;
  first [ lia
        | sc_store
        | extra
        | match goal with |- _ /\ _ => repeat split; first [lia | sc_store | extra] end
        | idtac ].

Ltac sym_run_tac segs fuel stops scr nx HR HK R' HR' Hlf Hms extra :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?regs =>
    lazymatch type of HK with
    | know_ok _ _ ?base ?kn =>
      lazymatch goal with
      | |- context [mkst regs (Z_to_bv 64 ?pc) base ?rom] =>
          let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn nx) []) in
          lazymatch r with
          | (?ss', ?scs, ?scr') =>
              let Hsc := fresh "Hsc" in
              assert (Hsc : scs_denot segs base E scs);
              [ split_scs; sc_auto extra
              | destruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E base rom regs
                          (eq_refl _) HR HK Hsc) as (R' & HR' & Hlf & Hms);
                clear Hsc ]
          end
      end
    end
  end.
