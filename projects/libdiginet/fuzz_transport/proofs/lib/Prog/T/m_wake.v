(* The walk of m_wake in the plain image, against m_wake_c.v. *)
(* m_wake (fuzz/fuzz_transport.c:218-233) at 0x14df4-0x14ea4: a leaf with no prologue, m_set inlined.
   Its machine contract is Prog/T/m_wake_c.v; the model is TModel/TCb.v m_wake_m, characterised once
   (m_wake_m_eq) so that the walk keeps a small hypothesis about it. The world loads and stores are
   stepped by the kit's world hooks (TModel/TWorldMem.v); OW.t[OW.n] is written once per value
   0..15 of OW.n, so that every store address is a literal. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TImg TSess0 TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract m_wake_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- Z / bitvector bridges for the branches (every scalar the function tests is a C int) ---- *)

Lemma mod64_neg : forall v, -2^64 <= v < 0 -> v mod 2^64 = v + 2^64.
Proof. intros v Hv. rewrite <- (Z.mod_add v 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia. Qed.

Lemma s32_mod_inj : forall v w, -2^31 <= v < 2^31 -> -2^31 <= w < 2^31 ->
  v mod 2^64 = w mod 2^64 -> v = w.
Proof. intros v w Hv Hw H. Z.div_mod_to_equations. lia. Qed.

Lemma eqb_s32 : forall v w, -2^31 <= v < 2^31 -> -2^31 <= w < 2^31 ->
  bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 w) = (v =? w).
Proof.
  intros v w Hv Hw. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec v w) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intro E. apply N. exact (s32_mod_inj v w Hv Hw E).
Qed.

Lemma signed_s32 : forall v, -2^31 <= v < 2^31 -> bv_signed (Z_to_bv 64 v) = v.
Proof.
  intros v Hv. rewrite zb_signed, unsigned_lit_wrap.
  destruct (Z_lt_le_dec v 0) as [L|L].
  - rewrite (mod64_neg v) by lia.
    replace (v + 2 ^ 64 <? 2 ^ 63) with false by (symmetry; apply Z.ltb_ge; lia).
    cbv iota. lia.
  - rewrite (Z.mod_small v (2 ^ 64)) by lia.
    replace (v <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia).
    cbv iota. reflexivity.
Qed.

Lemma lts_s32 : forall v w, -2^31 <= v < 2^31 -> -2^31 <= w < 2^31 ->
  bv_lts (Z_to_bv 64 v) (Z_to_bv 64 w) = (v <? w).
Proof. intros v w Hv Hw. unfold bv_lts. rewrite !signed_s32 by lia. reflexivity. Qed.

(* ---- the world algebra the two orders of the writes need ---- *)

Lemma firstn_app_add : forall (l1 l2 : list byte) n, firstn (length l1 + n) (l1 ++ l2) = l1 ++ firstn n l2.
Proof. induction l1 as [|x l1 IH]; intros l2 n; cbn; [reflexivity | f_equal; apply IH]. Qed.

Lemma skipn_app_add : forall (l1 l2 : list byte) n, skipn (length l1 + n) (l1 ++ l2) = skipn n l2.
Proof. induction l1 as [|x l1 IH]; intros l2 n; cbn; [reflexivity | apply IH]. Qed.

Lemma firstn_app_self : forall (l1 l2 : list byte), firstn (length l1) (l1 ++ l2) = l1.
Proof. induction l1 as [|x l1 IH]; intros l2; cbn; [reflexivity | f_equal; apply IH]. Qed.

Lemma upd_app : forall (bs v w : list byte) k,
  0 <= k -> (Z.to_nat k + length v <= length bs)%nat ->
  upd bs k (v ++ w) = upd (upd bs k v) (k + Z.of_nat (length v)) w.
Proof.
  intros bs v w k Hk Hl.
  assert (LL : length (firstn (Z.to_nat k) bs) = Z.to_nat k) by (rewrite length_firstn; lia).
  unfold upd. rewrite length_app.
  replace (Z.to_nat (k + Z.of_nat (length v))) with (Z.to_nat k + length v)%nat by lia.
  replace (Z.to_nat k + length v)%nat with (length (firstn (Z.to_nat k) bs) + length v)%nat by lia.
  rewrite firstn_app_add, firstn_app_self.
  replace (length (firstn (Z.to_nat k) bs) + length v + length w)%nat
    with (length (firstn (Z.to_nat k) bs) + (length v + length w))%nat by lia.
  rewrite skipn_app_add, skipn_app_add, skipn_skipn.
  replace (length w + (length (firstn (Z.to_nat k) bs) + length v))%nat
    with (Z.to_nat k + (length v + length w))%nat by lia.
  rewrite <- !app_assoc. reflexivity.
Qed.

(* the 8-byte zeroing of M.e2_acked / M.e1_us (one sd) is the model's two 4-byte stores *)
Lemma upd_zero8 : forall (bs : list byte) k k', 0 <= k -> k' = k + 4 -> k + 8 <= Z.of_nat (length bs) ->
  upd (upd bs k (put 4 0)) k' (put 4 0) = upd bs k (put 8 0).
Proof.
  intros bs k k' Hk -> Hl.
  replace (put 8 0) with (put 4 0 ++ put 4 0) by (vm_compute; reflexivity).
  rewrite (upd_app bs (put 4 0) (put 4 0) k) by (rewrite ?length_put; lia).
  rewrite length_put. reflexivity.
Qed.

Lemma wlen_upd : forall (bs : list byte) k n v, Z.of_nat (length bs) = 65616 -> 0 <= k -> k + Z.of_nat n <= 65616 ->
  Z.of_nat (length (upd bs k (put n v))) = 65616.
Proof. intros bs k n v H Hk Hn. rewrite length_upd_put; [exact H | lia | lia]. Qed.

Lemma s32_peel : forall (bs : list byte) k n v k',
  Z.of_nat (length bs) = 65616 -> 0 <= k -> 0 <= k' -> k + Z.of_nat n <= 65616 ->
  (k' + 4 <= k \/ k + Z.of_nat n <= k') ->
  s32_at (upd bs k (put n v)) k' = s32_at bs k'.
Proof.
  intros bs k n v k' HL Hk Hk' Hn Hd.
  rewrite s32_at_upd_out; [reflexivity | lia | lia | rewrite length_put; lia | rewrite length_put; lia].
Qed.

Lemma u_peel : forall (bs : list byte) k n v k' n',
  Z.of_nat (length bs) = 65616 -> 0 <= k -> 0 <= k' -> k + Z.of_nat n <= 65616 ->
  (k' + Z.of_nat n' <= k \/ k + Z.of_nat n <= k') ->
  u_at (upd bs k (put n v)) k' n' = u_at bs k' n'.
Proof.
  intros bs k n v k' n' HL Hk Hk' Hn Hd.
  rewrite u_at_upd_out; [reflexivity | lia | lia | rewrite length_put; lia | rewrite length_put; lia].
Qed.

Ltac wlen := repeat (apply wlen_upd; [ | lia | lia ]); assumption.
Ltac wside :=
  rewrite ?length_put;
  first [ lia
        | match goal with
          | |- context [Z.of_nat (length ?X)] =>
              let H := fresh "HW" in assert (H : Z.of_nat (length X) = 65616) by wlen; rewrite H; lia
          end ].
Ltac peelg := repeat first [ rewrite s32_peel by (first [wlen | lia]) | rewrite u_peel by (first [wlen | lia]) ].

(* OW.t[i]'s setters at their world offsets; not convertible to these for an open i, so proved *)
Lemma s_ots : forall bs i v, set_OW_t_state bs i v = upd bs (65316 + 12 * i) (put 4 v).
Proof. intros. unfold set_OW_t_state, A_OW_t_state, OFF_OW. f_equal. lia. Qed.
Lemma s_oto : forall bs i v, set_OW_t_old bs i v = upd bs (65320 + 12 * i) (put 4 v).
Proof. intros. unfold set_OW_t_old, A_OW_t_old, OFF_OW. f_equal. lia. Qed.
Lemma s_otr : forall bs i v, set_OW_t_reason bs i v = upd bs (65324 + 12 * i) (put 4 v).
Proof. intros. unfold set_OW_t_reason, A_OW_t_reason, OFF_OW. f_equal. lia. Qed.

(* the model's world, re-ordered into the order the binary writes it *)
Ltac to_machine Bw :=
  peelg;
  rewrite (upd_zero8 _ 16 20) by (first [lia | wside]);
  rewrite (upd_upd_comm _ (put 8 (u_at Bw 65000 8)) (put 4 (s32_at Bw 65508 + 1)) 40 65508)
    by (first [lia | wside]);
  rewrite (upd_upd_comm _ (put 8 0) (put 4 (s32_at Bw 65508 + 1)) 16 65508)
    by (first [lia | wside]).

(* ==== the model of m_wake, split so that every term the proof touches stays small ====
   The model's four intermediate worlds, named exactly as TCb.v builds them, so that the
   characterisation below holds by conversion alone. *)
Definition mw_B1 (B : list byte) : list byte := set_M_e1_us (set_M_e2_acked B 0) 0.
Definition mw_B2 (B : list byte) : list byte := set_M_wake_sent (mw_B1 B) (g_now (mw_B1 B)).
Definition mw_B3 (B : list byte) : list byte := set_OW_e2 (mw_B2 B) (OW_e2 (mw_B2 B) + 1).
Definition mw_W (B : list byte) : list byte := set_M_fail (mw_B3 B) 0.
Definition mw_fin (B : list byte) : list byte :=
  set_M_state (set_OW_n (mw_W B) (OW_n (mw_W B) + 1)) S_WAKING.
Definition mw_fin_rec (B : list byte) : list byte :=
  set_M_state (set_OW_n (set_OW_t_reason (set_OW_t_old (set_OW_t_state (mw_W B) (OW_n (mw_W B)) S_WAKING)
                                            (OW_n (mw_W B)) (M_state (mw_W B)))
                           (OW_n (mw_W B)) R_WAKE)
                 (OW_n (mw_W B) + 1)) S_WAKING.

(* m_wake's model as a flat cascade of tests. Proved by conversion after the four worlds are named:
   no rewriting touches the model's unfolded body, which the kernel would otherwise copy per rewrite. *)
Lemma m_wake_m_eq : forall B,
  m_wake_m B =
    (if M_desk_known B =? 0 then Some (B, -1)
     else if negb (M_foreign B =? 0) then Some (B, -10)
     else if OW_e2 (mw_B2 B) =? 2 ^ 31 - 1 then None
     else if negb (M_fail (mw_B3 B) =? 0) then Some (mw_W B, -5)
     else if M_state (mw_W B) =? 1 then Some (mw_W B, 0)
     else if OW_n (mw_W B) <? 0 then None
     else if OW_n (mw_W B) =? 2 ^ 31 - 1 then None
     else if 15 <? OW_n (mw_W B) then Some (mw_fin B, 0)
     else Some (mw_fin_rec B, 0)).
Proof.
  intros B.
  unfold mw_fin_rec, mw_fin, mw_W, mw_B3, mw_B2, mw_B1.
  unfold m_wake_m, m_set_m, truth, int_inc.
  cbv zeta.
  set (b1 := set_M_e1_us (set_M_e2_acked B 0) 0) in *.
  set (b2 := set_M_wake_sent b1 (g_now b1)) in *.
  destruct (M_desk_known B =? 0) eqn:E1; cbn [negb]; cbv iota; [reflexivity|].
  destruct (M_foreign B =? 0) eqn:E2; cbn [negb]; cbv iota; [|reflexivity].
  destruct (OW_e2 b2 =? 2 ^ 31 - 1) eqn:EO; unfold INT_MAX; rewrite ?EO; cbv iota; [reflexivity|].
  set (b3 := set_OW_e2 b2 (OW_e2 b2 + 1)) in *.
  destruct (M_fail b3 =? 0) eqn:E3; cbn [negb]; cbv iota; [|reflexivity].
  set (b4 := set_M_fail b3 0) in *.
  destruct (M_state b4 =? 1) eqn:E4; unfold S_WAKING; rewrite ?E4; cbv iota; [reflexivity|].
  unfold TRANS_MAX, INT_MAX, R_WAKE.
  destruct (OW_n b4 <? 0) eqn:EN.
  { apply Z.ltb_lt in EN.
    replace (OW_n b4 <? 16) with true by (symmetry; apply Z.ltb_lt; lia).
    try rewrite (proj2 (Z.ltb_lt _ _) EN). cbv iota. reflexivity. }
  apply Z.ltb_ge in EN.
  destruct (OW_n b4 =? 2 ^ 31 - 1) eqn:EI.
  { apply Z.eqb_eq in EI.
    replace (OW_n b4 <? 16) with false by (symmetry; apply Z.ltb_ge; lia).
    try rewrite (proj2 (Z.eqb_eq _ _) EI). cbv iota. reflexivity. }
  apply Z.eqb_neq in EI.
  try rewrite (proj2 (Z.eqb_neq _ _) EI).
  destruct (15 <? OW_n b4) eqn:E5.
  { apply Z.ltb_lt in E5.
    replace (OW_n b4 <? 16) with false by (symmetry; apply Z.ltb_ge; lia).
    cbv iota. reflexivity. }
  { apply Z.ltb_ge in E5.
    replace (OW_n b4 <? 16) with true by (symmetry; apply Z.ltb_lt; lia).
    try replace (OW_n b4 <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
    cbv iota. reflexivity. }
Qed.

(* ---- the model's tests and worlds, read off B and written in the binary's order ---- *)

Definition mwm_W (B : list byte) : list byte :=
  upd (upd (upd (upd B 65508 (put 4 (s32_at B 65508 + 1))) 16 (put 8 0))
           40 (put 8 (u_at B 65000 8))) 88 (put 4 0).

Lemma mw_dk : forall B, M_desk_known B = s32_at B 0.   Proof. reflexivity. Qed.
Lemma mw_fo : forall B, M_foreign B = s32_at B 24.     Proof. reflexivity. Qed.

(* Getters and setters to their literal offsets by SYNTACTIC matching and [change]: a [rewrite ?g_on]
   loops, because rewrite unifies up to delta and the lemma's two sides are convertible, so its own
   output matches its left side again. *)
Ltac gs :=
  repeat match goal with
  | |- context [M_desk_known ?x] => change (M_desk_known x) with (s32_at x 0)
  | |- context [M_foreign ?x] => change (M_foreign x) with (s32_at x 24)
  | |- context [M_fail ?x] => change (M_fail x) with (s32_at x 88)
  | |- context [M_state ?x] => change (M_state x) with (s32_at x 12)
  | |- context [OW_e2 ?x] => change (OW_e2 x) with (s32_at x 65508)
  | |- context [OW_n ?x] => change (OW_n x) with (s32_at x 65312)
  | |- context [g_now ?x] => change (g_now x) with (u_at x 65000 8)
  | |- context [set_M_e2_acked ?x ?v] => change (set_M_e2_acked x v) with (upd x 16 (put 4 v))
  | |- context [set_M_e1_us ?x ?v] => change (set_M_e1_us x v) with (upd x 20 (put 4 v))
  | |- context [set_M_wake_sent ?x ?v] => change (set_M_wake_sent x v) with (upd x 40 (put 8 v))
  | |- context [set_OW_e2 ?x ?v] => change (set_OW_e2 x v) with (upd x 65508 (put 4 v))
  | |- context [set_M_fail ?x ?v] => change (set_M_fail x v) with (upd x 88 (put 4 v))
  | |- context [set_OW_n ?x ?v] => change (set_OW_n x v) with (upd x 65312 (put 4 v))
  | |- context [set_M_state ?x ?v] => change (set_M_state x v) with (upd x 12 (put 4 v))
  end.

Lemma mw_e2 : forall B, Z.of_nat (length B) = 65616 -> OW_e2 (mw_B2 B) = s32_at B 65508.
Proof. intros B HL. unfold mw_B2, mw_B1. gs. peelg. reflexivity. Qed.

Lemma mw_fa : forall B, Z.of_nat (length B) = 65616 -> M_fail (mw_B3 B) = s32_at B 88.
Proof. intros B HL. unfold mw_B3, mw_B2, mw_B1. gs. peelg. reflexivity. Qed.

Lemma mw_st : forall B, Z.of_nat (length B) = 65616 -> M_state (mw_W B) = s32_at B 12.
Proof. intros B HL. unfold mw_W, mw_B3, mw_B2, mw_B1. gs. peelg. reflexivity. Qed.

Lemma mw_on : forall B, Z.of_nat (length B) = 65616 -> OW_n (mw_W B) = s32_at B 65312.
Proof. intros B HL. unfold mw_W, mw_B3, mw_B2, mw_B1. gs. peelg. reflexivity. Qed.

Lemma mw_W_m : forall B, Z.of_nat (length B) = 65616 -> mw_W B = mwm_W B.
Proof.
  intros B HL. unfold mw_W, mw_B3, mw_B2, mw_B1, mwm_W. gs.
  to_machine B. reflexivity.
Qed.

Lemma mw_fin_m : forall B, Z.of_nat (length B) = 65616 ->
  mw_fin B = upd (upd (mwm_W B) 65312 (put 4 (s32_at B 65312 + 1))) 12 (put 4 1).
Proof.
  intros B HL. unfold mw_fin. rewrite (mw_on B HL). rewrite (mw_W_m B HL). gs.
  unfold S_WAKING. reflexivity.
Qed.

Lemma mw_fin_rec_m : forall B, Z.of_nat (length B) = 65616 ->
  mw_fin_rec B =
    upd (upd (upd (upd (upd (mwm_W B) (65316 + 12 * s32_at B 65312) (put 4 1))
                        (65320 + 12 * s32_at B 65312) (put 4 (s32_at B 12)))
                   (65324 + 12 * s32_at B 65312) (put 4 1))
              65312 (put 4 (s32_at B 65312 + 1))) 12 (put 4 1).
Proof.
  intros B HL. unfold mw_fin_rec.
  rewrite (mw_on B HL). rewrite (mw_st B HL). rewrite (mw_W_m B HL). gs.
  rewrite s_ots. rewrite s_oto. rewrite s_otr.
  unfold S_WAKING, R_WAKE. reflexivity.
Qed.

Theorem m_wake_holds : m_wake_contract.
Proof.
  unfold m_wake_contract, m_wake_ENTRY, m_wake_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo B B' r SPA ST LO WOFF MI WM HM.
  unfold w_off_stack in WOFF.
  pose proof (wm_len rsegs W_BASE_PLAIN m B WM) as LB.
  assert (LB0 : Z.of_nat (length B) = 65616) by (rewrite LB; unfold W_LEN; vm_compute; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - 0, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMo.
  wk_facts.
  rewrite (m_wake_m_eq B) in HM.
  change (M_desk_known B) with (s32_at B 0) in HM. change (M_foreign B) with (s32_at B 24) in HM.
  rewrite (mw_e2 B LB0) in HM. rewrite (mw_fa B LB0) in HM.
  rewrite (mw_st B LB0) in HM. rewrite (mw_on B LB0) in HM.
  clear LB.
  do 4 step.
  rewrite (eqb_s32 (s32_at B 0) 0) by (first [apply s32_range | lia]).
  destruct (s32_at B 0 =? 0) eqn:E1; cbv iota; try rewrite E1 in HM; cbv iota in HM.
  - (* M.desk_known == 0: SPEC_E_ARG *)
    do 2 step.
    injection HM as HB Hr. subst r. subst B'.
    finish.
  - (* M.desk_known != 0 *)
    do 2 step.
    rewrite (eqb_s32 (s32_at B 24) 0) by (first [apply s32_range | lia]).
    destruct (s32_at B 24 =? 0) eqn:E2; cbv iota;
      try rewrite E2 in HM; cbn [negb] in HM; cbv iota in HM.
    + (* M.foreign == 0: the body *)
      destruct (s32_at B 65508 =? 2 ^ 31 - 1) eqn:EO;
        [ try rewrite EO in HM; cbv iota in HM; discriminate HM | ].
      try rewrite EO in HM. cbv iota in HM.
      do 10 step.
      step.
      rewrite (eqb_s32 (s32_at B 88) 0) by (first [apply s32_range | lia]).
      destruct (s32_at B 88 =? 0) eqn:E3; cbv iota;
        try rewrite E3 in HM; cbn [negb] in HM; cbv iota in HM.
      * (* M.fail == 0: m_set (S_WAKING, R_WAKE) *)
        step. peelg. do 2 step.
        rewrite (eqb_s32 (s32_at B 12) 1) by (first [apply s32_range | lia]).
        destruct (s32_at B 12 =? 1) eqn:E4; cbn [negb]; cbv iota;
          try rewrite E4 in HM; cbv iota in HM.
        -- (* M.state == S_WAKING already: no transition record *)
           do 2 step.
           injection HM as HB Hr. subst r. subst B'.
           rewrite (mw_W_m B LB0). unfold mwm_W.
           finish.
        -- (* a transition is recorded *)
           destruct (s32_at B 65312 <? 0) eqn:EN;
             [ try rewrite EN in HM; cbv iota in HM; discriminate HM | ].
           try rewrite EN in HM. cbv iota in HM. apply Z.ltb_ge in EN.
           destruct (s32_at B 65312 =? 2 ^ 31 - 1) eqn:EI;
             [ try rewrite EI in HM; cbv iota in HM; discriminate HM | ].
           try rewrite EI in HM. cbv iota in HM.
           step. peelg. do 2 step.
           rewrite (lts_s32 15 (s32_at B 65312)) by (first [apply s32_range | lia]).
           destruct (15 <? s32_at B 65312) eqn:E5; cbv iota;
             try rewrite E5 in HM; cbv iota in HM.
           ++ (* OW.n > 15: the record is dropped *)
              do 2 step. step. do 2 step. step.
              injection HM as HB Hr. subst r. subst B'.
              rewrite (mw_fin_m B LB0). unfold mwm_W.
              finish.
           ++ (* OW.n <= 15: OW.t[OW.n] is written. One branch per value of OW.n, so that each of
                 the three stores has a literal address: with an open index the world hook's
                 side goal `E = A + k` is tried by [reflexivity] on open terms first, which
                 does not finish. *)
              apply Z.ltb_ge in E5.
              assert (HN : s32_at B 65312 = 0 \/ s32_at B 65312 = 1 \/ s32_at B 65312 = 2 \/
                           s32_at B 65312 = 3 \/ s32_at B 65312 = 4 \/ s32_at B 65312 = 5 \/
                           s32_at B 65312 = 6 \/ s32_at B 65312 = 7 \/ s32_at B 65312 = 8 \/
                           s32_at B 65312 = 9 \/ s32_at B 65312 = 10 \/ s32_at B 65312 = 11 \/
                           s32_at B 65312 = 12 \/ s32_at B 65312 = 13 \/ s32_at B 65312 = 14 \/
                           s32_at B 65312 = 15) by lia.
              injection HM as HB Hr. subst r. subst B'.
              rewrite (mw_fin_rec_m B LB0). unfold mwm_W.
              destruct HN as [En|[En|[En|[En|[En|[En|[En|[En|[En|[En|[En|[En|[En|[En|[En|En]]]]]]]]]]]]]]];
                rewrite En in *;
                do 5 step; do 3 step; do 2 step; step; do 2 step; step;
                finish.
      * (* M.fail != 0: -EIO *)
        do 2 step.
        injection HM as HB Hr. subst r. subst B'.
        rewrite (mw_W_m B LB0). unfold mwm_W.
        finish.
    + (* M.foreign != 0: SPEC_E_REFUSED *)
      do 2 step.
      injection HM as HB Hr. subst r. subst B'.
      finish.
Qed.
