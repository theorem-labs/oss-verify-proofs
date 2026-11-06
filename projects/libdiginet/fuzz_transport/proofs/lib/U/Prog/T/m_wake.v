(* The walk of m_wake in the ubsan image, against m_wake_c.v. *)
(* m_wake (fuzz/fuzz_transport.c:218-233) at 0x14f64-0x14fe8. OW.e2++ is checked (blt to the unimp at
   0x14fe8, closed by the model's INT_MAX test); m_set is a call (jal 0x15e3c) inside a 16-byte frame
   that holds ra. Its machine contract is U/Prog/T/m_wake_c.v; the callee's is U/Prog/T/m_set_c.v; the
   model is TModel/TCb.v m_wake_m. The world loads and stores are stepped by the kit's hooks
   (TModel/TWorldMem.v); every world address here is a literal. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TImg TSess0 TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract m_set_c m_wake_c.
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

Lemma swrap32_id : forall v, -2^31 <= v < 2^31 -> bv_swrap 32 v = v.
Proof.
  intros v Hv. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  rewrite Z.mod_small by lia. lia.
Qed.

(* addiw a2,a3,1 on a sign-extended C int a3 = v: the 32-bit sum, sign-extended, is v + 1 when v < INT_MAX *)
Lemma addiw_s32 : forall v, -2^31 <= v < 2^31 - 1 -> bv_swrap 32 (bv_unsigned (Z_to_bv 64 v) + 1) = v + 1.
Proof.
  intros v Hv. rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  Z.div_mod_to_equations. lia.
Qed.
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

(* ==== the model of m_wake up to its call of m_set; every term the proof touches stays small ====
   The model's four intermediate worlds, named exactly as TCb.v builds them, so that the
   characterisation below holds by conversion alone. *)
Definition mw_B1 (B : list byte) : list byte := set_M_e1_us (set_M_e2_acked B 0) 0.
Definition mw_B2 (B : list byte) : list byte := set_M_wake_sent (mw_B1 B) (g_now (mw_B1 B)).
Definition mw_B3 (B : list byte) : list byte := set_OW_e2 (mw_B2 B) (OW_e2 (mw_B2 B) + 1).
Definition mw_W (B : list byte) : list byte := set_M_fail (mw_B3 B) 0.

Lemma m_wake_m_eq : forall B,
  m_wake_m B =
    (if M_desk_known B =? 0 then Some (B, -1)
     else if negb (M_foreign B =? 0) then Some (B, -10)
     else if OW_e2 (mw_B2 B) =? 2 ^ 31 - 1 then None
     else if negb (M_fail (mw_B3 B) =? 0) then Some (mw_W B, -5)
     else match m_set_m (mw_W B) S_WAKING R_WAKE with
          | Some (B5, _) => Some (B5, 0)
          | None => None
          end).
Proof.
  intros B.
  unfold mw_W, mw_B3, mw_B2, mw_B1.
  unfold m_wake_m, truth, int_inc.
  cbv zeta.
  set (b1 := set_M_e1_us (set_M_e2_acked B 0) 0) in *.
  set (b2 := set_M_wake_sent b1 (g_now b1)) in *.
  destruct (M_desk_known B =? 0) eqn:E1; cbn [negb]; cbv iota; [reflexivity|].
  destruct (M_foreign B =? 0) eqn:E2; cbn [negb]; cbv iota; [|reflexivity].
  destruct (OW_e2 b2 =? 2 ^ 31 - 1) eqn:EO; unfold INT_MAX; rewrite ?EO; cbv iota; [reflexivity|].
  set (b3 := set_OW_e2 b2 (OW_e2 b2 + 1)) in *.
  destruct (M_fail b3 =? 0) eqn:E3; cbn [negb]; cbv iota; reflexivity.
Qed.

(* the world after the four field writes, in the order the binary writes them *)
Definition mwu_W (B : list byte) : list byte :=
  upd (upd (upd (upd B 16 (put 8 0)) 40 (put 8 (u_at B 65000 8)))
           65508 (put 4 (s32_at B 65508 + 1))) 88 (put 4 0).

Lemma mw_e2 : forall B, Z.of_nat (length B) = 65616 -> OW_e2 (mw_B2 B) = s32_at B 65508.
Proof. intros B HL. unfold mw_B2, mw_B1. gs. peelg. reflexivity. Qed.

Lemma mw_fa : forall B, Z.of_nat (length B) = 65616 -> M_fail (mw_B3 B) = s32_at B 88.
Proof. intros B HL. unfold mw_B3, mw_B2, mw_B1. gs. peelg. reflexivity. Qed.

Lemma mw_W_u : forall B, Z.of_nat (length B) = 65616 -> mw_W B = mwu_W B.
Proof.
  intros B HL. unfold mw_W, mw_B3, mw_B2, mw_B1, mwu_W. gs. peelg.
  rewrite (upd_zero8 _ 16 20) by (first [lia | wside]). reflexivity.
Qed.


Theorem m_wake_holds : m_set_contract -> m_wake_contract.
Proof.
  intros MSET.
  unfold m_wake_contract, m_wake_ENTRY, m_wake_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo B B' r SPA ST LO WOFF MI WM HM.
  unfold w_off_stack in WOFF.
  pose proof (wm_len rsegs W_BASE_UBSAN m B WM) as LB.
  assert (LB0 : Z.of_nat (length B) = 65616) by (rewrite LB; unfold W_LEN; vm_compute; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMo.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  wk_facts.
  rewrite (m_wake_m_eq B) in HM.
  change (M_desk_known B) with (s32_at B 0) in HM. change (M_foreign B) with (s32_at B 24) in HM.
  rewrite (mw_e2 B LB0) in HM. rewrite (mw_fa B LB0) in HM. rewrite (mw_W_u B LB0) in HM.
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
      try rewrite EO in HM. cbv iota in HM. apply Z.eqb_neq in EO.
      pose proof (s32_range B 65508) as R2.
      do 5 step.
      rewrite (addiw_s32 (s32_at B 65508)) by lia.
      do 2 step.
      step.
      rewrite (lts_s32 (s32_at B 65508 + 1) (s32_at B 65508)) by lia.
      replace (s32_at B 65508 + 1 <? s32_at B 65508) with false by (symmetry; apply Z.ltb_ge; lia).
      cbv iota.
      step. peelg.
      do 2 step.
      step.
      rewrite (eqb_s32 (s32_at B 88) 0) by (first [apply s32_range | lia]).
      destruct (s32_at B 88 =? 0) eqn:E3; cbv iota;
        try rewrite E3 in HM; cbn [negb] in HM; cbv iota in HM.
      * (* M.fail == 0: m_set (S_WAKING, R_WAKE), called inside a 16-byte frame holding ra *)
        destruct (m_set_m (mwu_W B) S_WAKING R_WAKE) as [[B5 []]|] eqn:HMS;
          try rewrite HMS in HM; cbv iota in HM; [ | discriminate HM ].
        injection HM as HB Hr. subst r. subst B'.
        assert (HSP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16)
          by (apply unsigned_lit; lia).
        carve_frame 16%nat ST.
        do 2 step.
        do 2 step.
        step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mcall end.
        assert (HF : m_set_FRAME = 0) by reflexivity.
        eapply evt_cut.
        { eapply MSET.
          - reflexivity.
          - reflexivity.
          - lia.
          - lia.
          - rewrite HSP. replace (bv_unsigned sp + -16) with (bv_unsigned sp + (-1) * 16) by lia.
            rewrite Z.mod_add by lia. exact SPA.
          - rewrite HSP. exact ST.
          - unfold m_set_FRAME. rewrite HSP. lia.
          - unfold w_off_stack, m_set_FRAME. rewrite HSP. lia.
          - assumption.
          - eassumption.
          - exact HMS. }
        wk_post_call rsegs mcall.
        step. step.
        (* the stack below the frame is the callee's own [stk] fact, at the bv form of sp - 16 *)
        repeat match goal with
        | H : stk rsegs _ lo (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16))) |- _ => rewrite HSP in H
        end.
        lazymatch goal with H : stk rsegs _ lo (bv_unsigned sp + -16) |- _ => rename H into ST2 end.
        lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -16) _ |- _ => rename H into FR2 end.
        release_frame FR2 ST2 (bv_unsigned sp).
        step. step.
        finish.
      * (* M.fail != 0: -EIO *)
        do 2 step.
        injection HM as HB Hr. subst r. subst B'. unfold mwu_W.
        finish.
    + (* M.foreign != 0: SPEC_E_REFUSED *)
      do 2 step.
      injection HM as HB Hr. subst r. subst B'.
      finish.
Qed.
