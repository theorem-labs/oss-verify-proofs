(* The walk of host_offset in the ubsan image, against host_offset_c.v. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes Image.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TImg TSess0 TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import bcmp_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract host_offset_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- small arithmetic / bitvector helpers ---- *)

Lemma ltu_lit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit by assumption. reflexivity. Qed.

Lemma eqb_lit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit by assumption. reflexivity. Qed.

Lemma eqb_small : forall v, -256 < v < 256 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
  intros v Hv. unfold bv_eqb. rewrite !unsigned_lit_wrap. change (0 mod 2^64) with 0.
  destruct (Z.eqb_spec v 0) as [->|N].
  - reflexivity.
  - apply Z.eqb_neq. intros E. apply N.
    apply Z.mod_divide in E; [| lia]. destruct E as [c Ec]. nia.
Qed.

Lemma addiw_small : forall z c, 0 <= z < 2^64 -> -2^31 <= z + c < 2^31 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 z) + c)) = Z_to_bv 64 (z + c).
Proof.
  intros z c Hz Hc. rewrite unsigned_lit by lia.
  f_equal. apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). lia.
Qed.

Lemma seqz_neg_zero : forall z, 0 < z < 2^64 -> v_sltiu (Z_to_bv 64 (- z)) 1 = Z_to_bv 64 0.
Proof.
  intros z Hz. unfold v_sltiu. rewrite unsigned_lit_wrap.
  replace (bv_wrap 64 1) with 1 by (vm_compute; reflexivity).
  assert (Hm : (- z) mod 2^64 = 2^64 - z).
  { rewrite Z.mod_opp_l_nz.
    - rewrite Z.mod_small by lia. reflexivity.
    - lia.
    - rewrite Z.mod_small by lia. lia. }
  rewrite Hm.
  destruct (Z.ltb_spec (2^64 - z) 1) as [H1|H1]; [lia | reflexivity].
Qed.

(* ---- byte lists: a sub-slice is bytes_at at the shifted address ---- *)

Lemma nth_firstn : forall {X} n (l : list X) i, (i < n)%nat -> nth_error (firstn n l) i = nth_error l i.
Proof.
  intros X n. induction n as [|n IH]; intros l i Hi; [lia|].
  destruct l as [|x l]; [reflexivity|]. destruct i as [|i]; [reflexivity|]. cbn. apply IH. lia.
Qed.

Lemma bytes_at_sub : forall m a bs k n, bytes_at rsegs m a bs -> 0 <= k ->
  k + Z.of_nat n <= Z.of_nat (length bs) -> bytes_at rsegs m (a + k) (sub bs k n).
Proof.
  intros m a bs k n (Ha & Hl & H) Hk Hn. unfold sub.
  assert (Ln : length (firstn n (skipn (Z.to_nat k) bs)) = n)
    by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite Ln; lia|].
  intros i Hi. rewrite Ln in Hi.
  rewrite nth_firstn by lia. rewrite nth_skipn.
  replace (a + k + Z.of_nat i) with (a + Z.of_nat (Z.to_nat k + i)) by lia.
  apply H. lia.
Qed.

(* ---- memcmp_model = 0 iff list equality, for equal-length lists ---- *)

Lemma memcmp_model_eq : forall n l r v, length l = n -> length r = n -> memcmp_model l r n = Some v ->
  (v = 0 <-> l = r) /\ -256 < v < 256.
Proof.
  induction n as [|n IH]; intros l r v Hl Hr Hm.
  - destruct l; [|discriminate]. destruct r; [|discriminate]. cbn in Hm. inversion Hm. split; [tauto|lia].
  - destruct l as [|a l]; [discriminate|]. destruct r as [|b r]; [discriminate|].
    cbn in Hl, Hr, Hm. pose proof (bv_unsigned_in_range 8 a) as Ra. pose proof (bv_unsigned_in_range 8 b) as Rb.
    unfold bv_modulus in Ra, Rb. change (2 ^ Z.of_N 8) with 256 in Ra, Rb.
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|E].
    + destruct (IH l r v ltac:(lia) ltac:(lia) Hm) as [[I1 I2] I3]. split; [|exact I3].
      assert (a = b) by (apply bv_eq; exact E). subst b. split.
      * intros ->. f_equal. tauto.
      * intros Q. inversion Q. tauto.
    + inversion Hm. subst v. split; [|lia]. split.
      * intros. lia.
      * intros Q. inversion Q. subst. lia.
Qed.

Lemma memcmp6 : forall l r, length l = 6%nat -> length r = 6%nat ->
  exists v, memcmp_model l r 6 = Some v /\ (v = 0 <-> l = r) /\ -256 < v < 256.
Proof.
  intros l r Hl Hr. destruct (memcmp_model_total l r 6 ltac:(lia) ltac:(lia)) as [v Hv].
  exists v. split; [exact Hv|]. apply (memcmp_model_eq 6); assumption.
Qed.

(* ---- beq_bytes true iff list equality ---- *)

Lemma zs_inj : forall a b : list byte, zs a = zs b -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; unfold zs in H; cbn [map] in H; try discriminate H; [reflexivity|].
  injection H as Hxy Hab. f_equal; [apply bz_inj; exact Hxy | apply IH; exact Hab].
Qed.

Lemma beq_bytes_true_iff : forall a b, beq_bytes a b = true <-> a = b.
Proof.
  intros a b. unfold beq_bytes. destruct (list_eq_dec Z.eq_dec (zs a) (zs b)) as [E|E].
  - split; [intros _; apply zs_inj; exact E | reflexivity].
  - split; [discriminate | intros ->; exfalso; apply E; reflexivity].
Qed.

(* ---- HOST (02 00 00 00 00 01 at 0x10470, rodata, 6 bytes) is read-only image ---- *)

Lemma host_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x10470 HOST.
Proof.
  intros m MI. apply ro_bytes_at.
  - exact MI.
  - lia.
  - replace (Z.of_nat (length HOST)) with 6 by (vm_compute; reflexivity). lia.
  - apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

(* ---- the model's loop, one step, on a reachable (Some) result ---- *)

Lemma hol_step : forall k' body i r, 0 <= i <= 9 ->
  host_offset_loop (S k') body i = Some r ->
  i + 6 <= Z.of_nat (length body) /\
  ((sub body i 6 = HOST /\ r = i) \/
   (sub body i 6 <> HOST /\ host_offset_loop k' body (i + 1) = Some r)).
Proof.
  intros k' body i r Hi HL. cbn [host_offset_loop] in HL.
  unfold SPEC_MAC, SPEC_ANN_UNKNOWN in HL.
  rewrite (proj2 (Z.leb_le (i + 6) 15) ltac:(lia)) in HL. cbv iota in HL.
  destruct (Z.ltb_spec (Z.of_nat (length body)) (i + 6)) as [Hlt|Hge]; cbv iota in HL.
  - discriminate HL.
  - split; [lia|].
    destruct (beq_bytes (sub body i 6) HOST) eqn:EB; try rewrite EB in HL; cbv iota in HL.
    + left. split; [apply beq_bytes_true_iff; exact EB | injection HL as Heq; symmetry; exact Heq].
    + right. split; [| exact HL]. intro E. apply beq_bytes_true_iff in E. rewrite E in EB. discriminate EB.
Qed.

Theorem host_offset_holds : bcmp_contract -> host_offset_contract.
Proof.
  intros BC. unfold host_offset_contract, host_offset_ENTRY, host_offset_FRAME. unfold BCMP in BC.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo B B' p r body -> HP HB HWIN HSP ST LO WOS MI WM HM.
  (* model: B' = B and the loop returns r *)
  unfold host_offset_m in HM.
  destruct (host_offset_loop 10 body 0) as [r0|] eqn:HLOOP; [| discriminate HM].
  injection HM as HBB Hr0. subst B' r0.
  rename m into mB.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  unfold w_off_stack in WOS. unfold off_window in HWIN.
  pose proof (bytes_at_bound rsegs mB p body HB) as PB.
  destruct (hol_step 9 body 0 r ltac:(lia) HLOOP) as (HLEN0 & _).
  assert (Hp64 : p + 6 <= 2^64) by lia.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] mB) as MU.
  pose proof (wmono_refl rsegs mB) as WMO.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  wk_facts.
  carve_frame 80%nat ST.
  do 10 step.
  do 9 step.
  (* normalise the two constant registers s4 and s6 *)
  replace (0 - bv_unsigned (Z_to_bv 64 p)) with (- p) by (rewrite unsigned_lit by lia; lia).
  replace (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 p)) with (Z_to_bv 64 1)
    by (unfold v_sltu, c_ltu; rewrite (ltu_lit 0 p) by lia;
        destruct (Z.ltb_spec 0 p) as [_|Hc]; [reflexivity | exfalso; lia]).

  (* ===== the return epilogue, from pc 0x15d0c (mv a0,s0; restore; ret) ===== *)
  assert (EPI : forall (m2 : word -> option byte) (jb : list byte)
      (ra' a0' s1' s2' s3' s4' s5' s6' s7' u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 w3 w4 w5 w6 : word),
      rw_cells rsegs m2 (bv_unsigned sp + -80)
        [CB 8 jb; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      stk rsegs m2 lo (bv_unsigned sp + -80) ->
      munch [(bv_unsigned sp - 80, bv_unsigned sp)] mB m2 ->
      wmono rsegs mB m2 -> mem_inv rsegs m2 -> wmem rsegs m2 B ->
      evt rsegs QQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp u0 u1 u2
                 (Z_to_bv 64 r) s1' a0' b1 b2 b3 b4 b5 b6 b7
                 s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 w3 w4 w5 w6)
            F (Z_to_bv 64 89356) fc None m2 (seg_rom rsegs))).
  { intros m2 jb ra' a0' s1' s2' s3' s4' s5' s6' s7' u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 w3 w4 w5 w6
      FR2 ST2 MU2 WMO2 MI2 WM2.
    do 10 step.
    release_frame FR2 ST2 (bv_unsigned sp).
    step.
    replace (Z_to_bv 64 (bv_unsigned sp + -80 + 80)) with sp
      by (replace (bv_unsigned sp + -80 + 80) with (bv_unsigned sp) by lia; symmetry; apply Z_to_bv_lit_self).
    step.
    apply evt_done. unfold QQ. do 14 eexists. exists m2.
    rewrite ?Z.add_0_r.
    split; [reflexivity|].
    split; [exact MU2|]. split; [exact WMO2|]. split; [exact MI2|]. split; [exact ST2|].
    split; [reflexivity|]. exact WM2. }

  (* ===== the loop, induction on the fuel k ===== *)
  assert (LOOP : forall (k : nat) (i q f : Z) (m2 : word -> option byte) (jb : list byte)
      (ra' a0' b1 b2 b3 b4 b5 b6 b7 u0 u1 u2 w3 w4 w5 w6 : word),
      Z.of_nat k = 10 - i -> 0 <= i <= 9 -> q = p + i -> f = Z.of_nat k ->
      host_offset_loop k body i = Some r ->
      rw_cells rsegs m2 (bv_unsigned sp + -80)
        [CB 8 jb; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      stk rsegs m2 lo (bv_unsigned sp + -80) ->
      munch [(bv_unsigned sp - 80, bv_unsigned sp)] mB m2 ->
      wmono rsegs mB m2 -> mem_inv rsegs m2 -> wmem rsegs m2 B -> bytes_at rsegs m2 p body ->
      evt rsegs QQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp u0 u1 u2
                 (Z_to_bv 64 i) (Z_to_bv 64 p) a0' b1 b2 b3 b4 b5 b6 b7
                 (Z_to_bv 64 66672) (Z_to_bv 64 q) (Z_to_bv 64 (- p)) (Z_to_bv 64 f)
                 (Z_to_bv 64 1) (Z_to_bv 64 q) s8 s9 s10 s11 w3 w4 w5 w6)
            F (Z_to_bv 64 89292) fc None m2 (seg_rom rsegs))).
  { induction k as [|k' IH];
      intros i q f m2 jb ra' a0' b1 b2 b3 b4 b5 b6 b7 u0 u1 u2 w3 w4 w5 w6
        Hk Hi Hq Hf HL FR2 ST2 MU2 WMO2 MI2 WM2 HBODY2.
    { lia. }
    destruct (hol_step k' body i r Hi HL) as (HLEN & [ [HMATCH Hri] | [HNE HREC] ]).
    - (* match at this i: r = i *)
      subst r.
      do 2 step. step.
      lazymatch goal with |- context [v_sltiu (Z_to_bv 64 ?E) 1] =>
        replace E with (- (p + i)) by lia end.
      rewrite seqz_neg_zero by lia.
      step. rewrite eqb_lit by lia.
      destruct (Z.eqb_spec 1 0) as [bad|_]; [exfalso; lia | cbv iota].
      step. rewrite ltu_lit by lia.
      destruct (Z.ltb_spec q p) as [bad|_]; [exfalso; lia | cbv iota].
      do 4 step.
      destruct (memcmp6 (sub body i 6) HOST ltac:(apply length_sub; lia)
                        ltac:(vm_compute; reflexivity)) as (v & Hv & Veq & Vr).
      eapply evt_cut.
      { eapply BC with (ls := sub body i 6) (rs := HOST) (v := v).
        - rewrite unsigned_lit by lia.
          lazymatch goal with |- bytes_at _ _ ?A _ => replace A with (p + i) by lia end.
          apply bytes_at_sub; [exact HBODY2 | lia | lia].
        - rewrite unsigned_lit by lia.
          lazymatch goal with |- bytes_at _ _ ?A _ => replace A with 0x10470 by lia end.
          apply host_bytes; exact MI2.
        - exact Hv.
        - exact MI2. }
      post_call rsegs m2.
      step. rewrite eqb_small by exact Vr.
      destruct (Z.eqb_spec v 0) as [V0|V1]; cbv iota.
      + eapply EPI; eassumption.
      + exfalso. apply V1. apply Veq. exact HMATCH.
    - (* no match at this i: recurse with i+1 *)
      do 2 step. step.
      lazymatch goal with |- context [v_sltiu (Z_to_bv 64 ?E) 1] =>
        replace E with (- (p + i)) by lia end.
      rewrite seqz_neg_zero by lia.
      step. rewrite eqb_lit by lia.
      destruct (Z.eqb_spec 1 0) as [bad|_]; [exfalso; lia | cbv iota].
      step. rewrite ltu_lit by lia.
      destruct (Z.ltb_spec q p) as [bad|_]; [exfalso; lia | cbv iota].
      do 4 step.
      destruct (memcmp6 (sub body i 6) HOST ltac:(apply length_sub; lia)
                        ltac:(vm_compute; reflexivity)) as (v & Hv & Veq & Vr).
      eapply evt_cut.
      { eapply BC with (ls := sub body i 6) (rs := HOST) (v := v).
        - rewrite unsigned_lit by lia.
          lazymatch goal with |- bytes_at _ _ ?A _ => replace A with (p + i) by lia end.
          apply bytes_at_sub; [exact HBODY2 | lia | lia].
        - rewrite unsigned_lit by lia.
          lazymatch goal with |- bytes_at _ _ ?A _ => replace A with 0x10470 by lia end.
          apply host_bytes; exact MI2.
        - exact Hv.
        - exact MI2. }
      post_call rsegs m2.
      step. rewrite eqb_small by exact Vr.
      destruct (Z.eqb_spec v 0) as [V0|V1]; cbv iota.
      + exfalso. apply HNE. apply Veq. exact V0.
      + step. rewrite addiw_small by lia.
        step. step. step.
        step. rewrite eqb_lit by lia.
        destruct (Z.eqb_spec (f + -1) 0) as [FE|FN]; cbn [negb].
        * (* fuel exhausted: k' = 0, r = -1 *)
          assert (k' = 0%nat) by (apply Nat2Z.inj; lia). subst k'.
          cbn [host_offset_loop] in HREC. injection HREC as Hrm. subst r.
          step.
          eapply EPI; eassumption.
        * (* loop back: apply IH with i+1, q+1, f-1 *)
          eapply (IH (i + 1) (q + 1) (f + -1)); try eassumption; try lia. }

  (* ===== launch the loop at i = 0, k = 10 ===== *)
  eapply (LOOP 10%nat 0 p 10); try eassumption; try lia.
Qed.
