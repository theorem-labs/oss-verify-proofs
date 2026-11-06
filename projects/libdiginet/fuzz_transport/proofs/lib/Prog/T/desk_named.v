(* The walk of desk_named (fuzz/fuzz_transport.c:265-273, spec_strz_len inlined) in the plain image, against desk_named_c.v. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Image.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldMem TImg TSess0 TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import bcmp_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract desk_named_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- the model (TCb.v desk_named_m), no machine ---- *)

(* what desk_named_m returns for the strz length n of the name field fld *)
Definition dn_r (I : timg) (n : nat) (fld : list byte) : Z :=
  if (n =? 8)%nat && beq_bytes (firstn n fld) C24_NAME then ti_spec_c24 I
  else if (n =? 8)%nat && beq_bytes (firstn n fld) PC_NAME then ti_spec_pc I
  else 0.

Lemma dn_model : forall I B body B' r, desk_named_m I B body = Some (B', r) ->
  B' = B /\ (Nat.min 9 (S (strz_len (skipn 24 body))) <= length (skipn 24 body))%nat /\
  r = dn_r I (strz_len (skipn 24 body)) (skipn 24 body).
Proof.
  intros I B body B' r H. unfold desk_named_m, list_strz_len, SPEC_ANN_NAME in H. cbv zeta in H.
  change (Z.to_nat 24) with 24%nat in H. unfold dn_r. revert H.
  destruct (length (skipn 24 body) <? Nat.min 9 (S (strz_len (skipn 24 body))))%nat eqn:E; [discriminate|].
  apply Nat.ltb_ge in E. intros H. cbv beta iota in H. revert H.
  destruct ((strz_len (skipn 24 body) =? 8)%nat
              && beq_bytes (firstn (strz_len (skipn 24 body)) (skipn 24 body)) C24_NAME).
  { intros H. injection H as <- <-. split; [reflexivity|]. split; [exact E | reflexivity]. }
  destruct ((strz_len (skipn 24 body) =? 8)%nat
              && beq_bytes (firstn (strz_len (skipn 24 body)) (skipn 24 body)) PC_NAME);
    intros H; injection H as <- <-; (split; [reflexivity|]; split; [exact E | reflexivity]).
Qed.

Lemma dn_nz_lt : forall l j, (j < nz_run l)%nat -> exists b, nth_error l j = Some b /\ bz b <> 0.
Proof.
  induction l as [|x l IH]; cbn; [intros; lia|].
  destruct (bz x =? 0) eqn:E; intros j H; [lia|].
  destruct j as [|j]; cbn.
  - exists x. split; [reflexivity|]. apply Z.eqb_neq. exact E.
  - apply IH. lia.
Qed.

Lemma dn_nz_at : forall l, (nz_run l < length l)%nat -> exists b, nth_error l (nz_run l) = Some b /\ bz b = 0.
Proof.
  induction l as [|x l IH]; cbn; [intros H; lia|].
  destruct (bz x =? 0) eqn:E; intros H.
  - exists x. split; [reflexivity|]. apply Z.eqb_eq. exact E.
  - cbn. apply IH. lia.
Qed.

Lemma dn_nz_le : forall l, (nz_run l <= length l)%nat.
Proof. induction l as [|x l IH]; cbn; [lia|]. destruct (bz x =? 0); lia. Qed.

Lemma dn_memcmp : forall n l r v, length l = n -> length r = n -> memcmp_model l r n = Some v ->
  -256 < v < 256 /\ (v = 0 <-> zs l = zs r).
Proof.
  induction n as [|n IH]; intros l r v Hl Hr Hm.
  - destruct l; [|discriminate]. destruct r; [|discriminate]. cbn in Hm. injection Hm as <-.
    split; [lia|]. split; reflexivity.
  - destruct l as [|a l]; [discriminate|]. destruct r as [|b r]; [discriminate|].
    cbn in Hl, Hr, Hm. injection Hl as Hl. injection Hr as Hr.
    assert (Ra : 0 <= bv_unsigned a < 256)
      by (pose proof (bv_unsigned_in_range 8 a); unfold bv_modulus in *; change (Z.of_N 8) with 8%Z in *; lia).
    assert (Rb : 0 <= bv_unsigned b < 256)
      by (pose proof (bv_unsigned_in_range 8 b); unfold bv_modulus in *; change (Z.of_N 8) with 8%Z in *; lia).
    unfold zs in *. cbn [map].
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|E].
    + destruct (IH l r v Hl Hr Hm) as [R I]. split; [exact R|]. rewrite I, E. split.
      * intros H. rewrite H. reflexivity.
      * intros H. injection H as H. exact H.
    + injection Hm as <-. split; [lia|]. split; [lia|]. intros H. injection H as H1 _. lia.
Qed.

Lemma dn_beq_true : forall a b, zs a = zs b -> beq_bytes a b = true.
Proof. intros a b E. unfold beq_bytes. destruct (list_eq_dec Z.eq_dec (zs a) (zs b)); [reflexivity | contradiction]. Qed.

Lemma dn_beq_false : forall a b, zs a <> zs b -> beq_bytes a b = false.
Proof. intros a b E. unfold beq_bytes. destruct (list_eq_dec Z.eq_dec (zs a) (zs b)); [contradiction | reflexivity]. Qed.

Lemma dn_len_c24 : length C24_NAME = 8%nat. Proof. reflexivity. Qed.
Lemma dn_len_pc : length PC_NAME = 8%nat. Proof. reflexivity. Qed.

Lemma dn_nth_firstn : forall (l : list byte) k j, (j < k)%nat -> nth_error (firstn k l) j = nth_error l j.
Proof.
  intros l k. revert l. induction k as [|k IH]; intros l j H; [lia|].
  destruct l as [|x l]; [reflexivity|]. destruct j as [|j]; cbn; [reflexivity | apply IH; lia].
Qed.

Lemma dn_nth_skipn : forall (l : list byte) k j, nth_error (skipn k l) j = nth_error l (k + j).
Proof.
  intros l k. revert l. induction k as [|k IH]; intros l j; [reflexivity|].
  destruct l as [|x l]; cbn; [destruct j; reflexivity | apply IH].
Qed.

(* ---- machine helpers ---- *)

Lemma dn_rd1 : forall m a bs k b, bytes_at rsegs m a bs -> 0 <= k -> nth_error bs (Z.to_nat k) = Some b ->
  ov_read_bytes rsegs m (Z_to_bv 64 (a + k)) 1 = Some [b].
Proof.
  intros m a bs k b H Hk E.
  assert (L : (Z.to_nat k < length bs)%nat) by (apply nth_error_Some; rewrite E; discriminate).
  pose proof (bytes_at_read rsegs m a bs k 1 H Hk ltac:(lia)) as R. unfold wa in R. rewrite R.
  rewrite <- (firstn_skipn_step bs (Z.to_nat k) 0 b E). reflexivity.
Qed.

Lemma dn_bsub : forall m a bs k j, bytes_at rsegs m a bs -> (k + j <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn j (skipn k bs)).
Proof.
  intros m a bs k j H L.
  rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn in H. replace (Nat.min k (length bs)) with k in H by lia.
  rewrite <- (firstn_skipn j (skipn k bs)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

Lemma dn_eqb : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma dn_eqb0 : forall v, -2^63 <= v < 2^63 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
  intros v Hv. unfold bv_eqb. rewrite !unsigned_lit_wrap. change (0 mod 2^64) with 0.
  destruct (Z.eqb_spec v 0) as [->|N]; [reflexivity|].
  apply Z.eqb_neq. intros E. apply Z.mod_divide in E; [|lia]. destruct E as [c Ec]. nia.
Qed.

(* ---- the walk ---- *)

Theorem desk_named_holds : bcmp_contract -> desk_named_contract.
Proof.
  intros BC. unfold desk_named_contract, desk_named_ENTRY, desk_named_FRAME. unfold BCMP in BC.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo B B' p r body -> Hp HB OW Hsp ST LO WOS MI WM HM.
  destruct (dn_model _ _ _ _ _ HM) as (-> & HL & ->). clear HM.
  unfold off_window in OW. unfold w_off_stack in WOS.
  wk_facts.
  pose proof (bytes_at_bound rsegs m p body HB) as BB.
  set (fld := skipn 24 body) in *.
  set (n := strz_len fld) in *.
  assert (Lf : length fld = (length body - 24)%nat) by (unfold fld; apply length_skipn).
  assert (Hn9 : (n <= 9)%nat).
  { unfold n, strz_len. pose proof (dn_nz_le (firstn 9 fld)) as X. rewrite length_firstn in X. lia. }
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMo.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  carve_frame 16%nat ST.
  step. step. step. step. step. step.
  (* the epilogue at 0x15884, a0 = the result *)
  assert (EPI : forall (v : Z) (m2 : word -> option byte)
                       (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    rw_cells rsegs m2 (bv_unsigned sp + -16) [C8 s0; C8 ra] -> stk rsegs m2 lo (bv_unsigned sp + -16) ->
    munch [(bv_unsigned sp + -16, bv_unsigned sp)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
    wmem rsegs m2 B -> v = dn_r timg_plain n fld ->
    evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 x6 x7 x8 s1
                          (Z_to_bv 64 v) x11 x12 x13 x14 x15 x16 x17
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x15884) fc None m2 (seg_rom rsegs))).
  { intros v m2 x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 FR2 ST2 MU2 WMo2 MI2 W2 Hv.
    step. step. step.
    release_frame FR2 ST2 (bv_unsigned sp).
    step.
    apply evt_done. unfold QQ. do 14 eexists. exists m2. split; [subst v; reflexivity|].
    replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) by lia.
    split; [exact MU2|]. split; [exact WMo2|]. split; [exact MI2|]. split; [exact ST2|].
    split; [reflexivity | exact W2]. }
  (* 0x15880: li a0, 0, then the epilogue *)
  assert (RET0 : forall (m2 : word -> option byte)
                        (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    rw_cells rsegs m2 (bv_unsigned sp + -16) [C8 s0; C8 ra] -> stk rsegs m2 lo (bv_unsigned sp + -16) ->
    munch [(bv_unsigned sp + -16, bv_unsigned sp)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
    wmem rsegs m2 B -> dn_r timg_plain n fld = 0 ->
    evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 x6 x7 x8 s1
                          x10 x11 x12 x13 x14 x15 x16 x17
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x15880) fc None m2 (seg_rom rsegs))).
  { intros m2 x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 FR2 ST2 MU2 WMo2 MI2 W2 H0.
    step.
    apply EPI; try assumption. symmetry. exact H0. }
  (* 0x15850: the name is 8 bytes long; compare it with "CNTRL|24", then "MAINUNIT" *)
  assert (CMP : forall (x10 x11 x12 : word), n = 8%nat ->
    evt rsegs QQ (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 (p + 24)) s1
                          x10 x11 x12 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x15850) fc None m1 (seg_rom rsegs))).
  { intros x10 x11 x12 N8.
    assert (L9 : (9 <= length fld)%nat) by lia.
    assert (LS : length (firstn 8 fld) = 8%nat) by (rewrite length_firstn; lia).
    pose proof (dn_bsub m1 p body 24 8 HB ltac:(lia)) as BS. change (Z.of_nat 24) with 24 in BS.
    assert (RC : bytes_at rsegs m1 0x10339 C24_NAME).
    { apply ro_bytes_at; [exact MI | vm_compute; discriminate | vm_compute; discriminate |].
      apply ro_bytes_b_sound. vm_compute. reflexivity. }
    destruct (memcmp_model_total (firstn 8 fld) C24_NAME 8 ltac:(lia) ltac:(rewrite dn_len_c24; lia))
      as [v Hv].
    destruct (dn_memcmp 8 _ _ v LS dn_len_c24 Hv) as [Rv Ev].
    step. step. step. step. step.
    eapply evt_cut.
    { eapply BC with (ls := firstn 8 fld) (rs := C24_NAME) (v := v).
      - rewrite unsigned_lit by lia. exact BS.
      - rewrite unsigned_lit by lia. exact RC.
      - rewrite unsigned_lit by lia. exact Hv.
      - exact MI. }
    post_call rsegs m1.
    lazymatch goal with H : rw_cells _ ?mm (bv_unsigned sp + -16) _ |- _ => rename mm into m2 end.
    step.
    rewrite dn_eqb0 by lia.
    destruct (Z.eqb_spec v 0) as [V0|V0]; cbn [negb].
    { step. step. step.
      apply EPI; try assumption.
      unfold dn_r. rewrite N8. rewrite (dn_beq_true _ _ (proj1 Ev V0)). reflexivity. }
    assert (RP : bytes_at rsegs m2 0x10330 PC_NAME).
    { apply ro_bytes_at; [assumption | vm_compute; discriminate | vm_compute; discriminate |].
      apply ro_bytes_b_sound. vm_compute. reflexivity. }
    destruct (memcmp_model_total (firstn 8 fld) PC_NAME 8 ltac:(lia) ltac:(rewrite dn_len_pc; lia))
      as [w Hw].
    destruct (dn_memcmp 8 _ _ w LS dn_len_pc Hw) as [Rw EqW].
    step. step. step. step. step.
    eapply evt_cut.
    { eapply BC with (ls := firstn 8 fld) (rs := PC_NAME) (v := w).
      - rewrite unsigned_lit by lia. exact BS.
      - rewrite unsigned_lit by lia. exact RP.
      - rewrite unsigned_lit by lia. exact Hw.
      - assumption. }
    post_call rsegs m2.
    lazymatch goal with H : rw_cells _ ?mm (bv_unsigned sp + -16) _ |- _ => rename mm into m3 end.
    step.
    rewrite dn_eqb0 by lia.
    destruct (Z.eqb_spec w 0) as [W0|W0]; cbn [negb].
    { step. step. step.
      apply EPI; try assumption.
      unfold dn_r. rewrite N8. rewrite (dn_beq_false _ _ (fun E => V0 (proj2 Ev E))).
      rewrite (dn_beq_true _ _ (proj1 EqW W0)). reflexivity. }
    apply RET0; try assumption.
    unfold dn_r. rewrite N8. rewrite (dn_beq_false _ _ (fun E => V0 (proj2 Ev E))).
    rewrite (dn_beq_false _ _ (fun E => W0 (proj2 EqW E))). reflexivity. }
  (* 0x15830: the strz scan, i bytes read so far, all of them non-NUL *)
  assert (LOOP : forall k i (x12 : word), Z.of_nat k = 9 - i -> 0 <= i < 9 -> (Z.to_nat i <= n)%nat ->
    evt rsegs QQ (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 (p + 24)) s1
                          (Z_to_bv 64 (9 - i)) (Z_to_bv 64 (p + 24 + i)) x12 a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x15830) fc None m1 (seg_rom rsegs))).
  { induction k as [|k IH]; intros i x12 Hk Hi Hin; [lia|].
    assert (Li : (Z.to_nat i < length fld)%nat) by lia.
    destruct (nth_error fld (Z.to_nat i)) as [b|] eqn:Eb; [| apply nth_error_None in Eb; lia].
    assert (Eb' : nth_error body (Z.to_nat (24 + i)) = Some b).
    { replace (Z.to_nat (24 + i)) with (24 + Z.to_nat i)%nat by lia. rewrite <- dn_nth_skipn. exact Eb. }
    pose proof (dn_rd1 m1 p body (24 + i) b HB ltac:(lia) Eb') as RD.
    replace (p + (24 + i)) with (p + 24 + i) in RD by lia.
    assert (Rb : 0 <= bv_unsigned b < 256)
      by (pose proof (bv_unsigned_in_range 8 b); unfold bv_modulus in *; change (Z.of_N 8) with 8%Z in *; lia).
    step. step.
    unfold zxb. rewrite dn_eqb by lia.
    destruct (Nat.eq_dec (Z.to_nat i) n) as [Ein|Ein].
    - (* byte i is the NUL: n = i *)
      assert (Z0 : bv_unsigned b = 0).
      { assert (Lt : (n < length (firstn 9 fld))%nat) by (rewrite length_firstn; lia).
        destruct (dn_nz_at (firstn 9 fld) Lt) as (b0 & E0 & Z0).
        change (nz_run (firstn 9 fld)) with n in E0. rewrite <- Ein in E0.
        rewrite dn_nth_firstn in E0 by lia. rewrite Eb in E0. injection E0 as <-. exact Z0. }
      replace (bv_unsigned b =? 0) with true by (symmetry; apply Z.eqb_eq; exact Z0). cbn [negb].
      step. step.
      rewrite dn_eqb by lia.
      destruct (Z.eqb_spec (9 - i) 1) as [E1|E1]; cbn [negb].
      + apply CMP. lia.
      + apply RET0; try assumption.
        unfold dn_r. destruct (Nat.eqb_spec n 8); [lia | reflexivity].
    - (* byte i is not NUL: i < n *)
      assert (Lt : (Z.to_nat i < n)%nat) by lia.
      assert (NZ : bv_unsigned b <> 0).
      { destruct (dn_nz_lt (firstn 9 fld) (Z.to_nat i) Lt) as (b0 & E0 & Z0).
        rewrite dn_nth_firstn in E0 by lia. rewrite Eb in E0. injection E0 as <-. exact Z0. }
      replace (bv_unsigned b =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ). cbn [negb].
      step. step. step.
      rewrite dn_eqb by lia.
      destruct (Z.eqb_spec (9 - i + -1) 0) as [E9|E9]; cbn [negb].
      + step.
        apply RET0; try assumption.
        unfold dn_r. destruct (Nat.eqb_spec n 8); [lia | reflexivity].
      + replace (9 - i + -1) with (9 - (i + 1)) by lia.
        replace (p + 24 + i + 1) with (p + 24 + (i + 1)) by lia.
        apply (IH (i + 1)); lia. }
  pose proof (LOOP 9%nat 0 a2 ltac:(lia) ltac:(lia) ltac:(lia)) as L0.
  rewrite Z.add_0_r in L0. exact L0.
Qed.
