(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* LLVMFuzzerTestOneInput_seg.cstep_stmt: the cursor loop's memset (&m, 0, 56) (0x12ddc .. 0x12dec) and the inlined
   spec_msg_step (0x12dec .. 0x12ef8, with its out-of-line part 0x12f54 .. 0x13020) of the plain image. Every path
   ends at 0x12ef8 through cstep_end with m = spec_msg_cells of DgnSpec.spec_msg_step: the end of the body, F0 with
   the F7 scan 0x12e30 .. 0x12e40 (cstep_scan, by induction on len - i), F1 .. FF, a data byte with no running
   status, and a channel message (cstep_chan, cstep_chan2) with its data-byte loop 0x12fa0 .. 0x12fb4 unrolled
   for one or two data bytes. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib DgnDecHarness.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import memset_c memcpy_c DgnLayout.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import LLVMFuzzerTestOneInput_seg.
Import ListNotations.
Open Scope Z_scope.

(* ---- cells ---- *)

Lemma cstep_rw_split : forall segs m A cs1 cs2, rw_cells segs m A (cs1 ++ cs2) ->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2 [[W B] (Ra & Rb & R)].
  apply cells_wf_app in W. destruct W as [W1 W2].
  rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [B1 B2].
  rewrite cells_bytes_length in B2 by exact W1.
  rewrite cells_size_app in Rb, R.
  split; split; [split; assumption | | split; assumption | ].
  - split; [lia|]. split; [lia|]. intros i Hi. apply R. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. rewrite <- Z.add_assoc. apply R. lia.
Qed.

Lemma cstep_rw_app : forall segs m A cs1 cs2, rw_cells segs m A cs1 ->
  rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells segs m A (cs1 ++ cs2).
Proof.
  intros segs m A cs1 cs2 [[W1 B1] (R1a & R1b & R1)] [[W2 B2] (R2a & R2b & R2)].
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|].
    rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i (Z.of_nat (cells_size cs1))) as [H|H]; [apply R1; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
    apply R2. lia.
Qed.

Lemma cstep_rwc_bytes : forall segs m A cs cs', rw_cells segs m A cs -> cells_wf cs' ->
  cells_bytes cs' = cells_bytes cs -> rw_cells segs m A cs'.
Proof.
  intros segs m A cs cs' [[Hwf Hb] Hw] Hwf' E.
  split; [split; [exact Hwf' | rewrite E; exact Hb]|].
  rewrite <- (cells_bytes_length cs' Hwf'), E, (cells_bytes_length cs Hwf). exact Hw.
Qed.

Lemma cstep_bytes_eq : forall l1 l2 : list byte, map (@bv_unsigned 8) l1 = map (@bv_unsigned 8) l2 -> l1 = l2.
Proof.
  induction l1 as [|a l1 IH]; intros [|b l2]; cbn; intros H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

(* ---- register values ---- *)

Lemma cstep_le1 : forall z, le1 (Z_to_bv 64 z) = [b8 z].
Proof.
  intros z. unfold le1, b8. cbn [Z_to_le_bytes]. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ Z.of_N 8) with (2 ^ 8).
  apply Z.mod_mod_divide. exists (2 ^ 56). reflexivity.
Qed.

Lemma cstep_not : forall z,
  Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 z)) 18446744073709551615) = Z_to_bv 64 (- z - 1).
Proof.
  intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  change 18446744073709551615 with (Z.ones 64).
  replace (- z - 1) with (Z.lnot z) by (unfold Z.lnot; lia).
  apply Z.bits_inj'. intros n Hn.
  destruct (Z_lt_le_dec n 64).
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite Z.lxor_spec, Z.ones_spec_low by lia.
    rewrite Z.mod_pow2_bits_low by lia. rewrite Z.lnot_spec by lia. destruct (Z.testbit z n); reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma cstep_neg : forall z, Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 z)) = Z_to_bv 64 (- z).
Proof.
  intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zminus_mod_idemp_r. reflexivity.
Qed.

Lemma cstep_sub : forall a b,
  Z_to_bv 64 (bv_unsigned (Z_to_bv 64 a) - bv_unsigned (Z_to_bv 64 b)) = Z_to_bv 64 (a - b).
Proof.
  intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r. reflexivity.
Qed.

(* ---- the model ---- *)

Lemma cstep_byte_at : forall bb i, byte_at (bzl bb) i = bz (nth (Z.to_nat i) bb (Z_to_bv 8 0)).
Proof.
  intros bb i. unfold byte_at, bzl.
  transitivity (nth (Z.to_nat i) (map bz bb) (bz (Z_to_bv 8 0))); [reflexivity | apply map_nth].
Qed.

Lemma cstep_scan_step : forall b len i, i < len -> byte_at b i <> 247 ->
  scan_f7 b len i (Z.to_nat (len - i)) = scan_f7 b len (i + 1) (Z.to_nat (len - (i + 1))).
Proof.
  intros b len i H1 H2. replace (Z.to_nat (len - i)) with (S (Z.to_nat (len - (i + 1)))) by lia.
  cbn [scan_f7]. rewrite (proj2 (Z.ltb_lt i len) H1), (proj2 (Z.eqb_neq _ 247) H2). reflexivity.
Qed.

(* beq / bne of two signed 64-bit values *)
Lemma cstep_eqb : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof.
  intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec x y) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E. apply N.
  replace (2^64) with 18446744073709551616 in E by reflexivity.
  replace (2^63) with 9223372036854775808 in Hx, Hy by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

(* snez (sltu zero, x) of a signed 64-bit value *)
Lemma cstep_snez : forall z, -2^63 <= z < 2^63 ->
  v_sltu (Z_to_bv 64 0) (Z_to_bv 64 z) = Z_to_bv 64 (Z.b2z (negb (z =? 0))).
Proof.
  intros z Hz. rewrite v_sltu_b2z. f_equal. f_equal.
  rewrite !unsigned_lit_wrap. change (0 mod 2^64) with 0.
  replace (2^64) with 18446744073709551616 by reflexivity.
  replace (2^63) with 9223372036854775808 in Hz by reflexivity.
  destruct (Z.eqb_spec z 0) as [->|N]; [reflexivity|].
  apply Z.ltb_lt. Z.div_mod_to_equations. lia.
Qed.

Lemma cstep_scan_hit : forall b len i, i < len -> byte_at b i = 247 -> scan_f7 b len i (Z.to_nat (len - i)) = i.
Proof.
  intros b len i H1 H2. replace (Z.to_nat (len - i)) with (S (Z.to_nat (len - (i + 1)))) by lia.
  cbn [scan_f7]. rewrite (proj2 (Z.ltb_lt i len) H1), H2. reflexivity.
Qed.

Lemma cstep_scan_end : forall b len, scan_f7 b len len (Z.to_nat (len - len)) = len.
Proof. intros b len. rewrite Z.sub_diag. reflexivity. Qed.

Lemma cstep_m_end : forall b len pos st, len <= pos ->
  spec_msg_step b len pos st =
  {| sm_code := 0; sm_at := pos; sm_len := 0; sm_next := pos; sm_status := 0; sm_running := 0; sm_d1 := 0;
     sm_d2 := 0; sm_status_out := st; sm_sysex_at := 0; sm_sysex_len := 0 |}.
Proof. intros b len pos st H. unfold spec_msg_step. destruct (Z.leb_spec len pos); [reflexivity | lia]. Qed.

Lemma cstep_m_f0_trunc : forall b len pos st, pos < len -> byte_at b pos = 240 ->
  scan_f7 b len (pos + 1) (Z.to_nat (len - (pos + 1))) = len ->
  spec_msg_step b len pos st =
  {| sm_code := -6; sm_at := pos; sm_len := 0; sm_next := len; sm_status := 0; sm_running := 0; sm_d1 := 0;
     sm_d2 := 0; sm_status_out := 0; sm_sysex_at := 0; sm_sysex_len := 0 |}.
Proof.
  intros b len pos st H1 H2 H3. unfold spec_msg_step. cbv beta zeta.
  rewrite (proj2 (Z.leb_gt len pos) H1), H2, H3, !Z.eqb_refl. reflexivity.
Qed.

Lemma cstep_m_f0_ok : forall b len pos st i, pos < len -> byte_at b pos = 240 ->
  scan_f7 b len (pos + 1) (Z.to_nat (len - (pos + 1))) = i -> i <> len ->
  spec_msg_step b len pos st =
  {| sm_code := 1; sm_at := pos; sm_len := i + 1 - pos; sm_next := i + 1; sm_status := 240; sm_running := 0;
     sm_d1 := 0; sm_d2 := 0; sm_status_out := 0; sm_sysex_at := pos + 1; sm_sysex_len := i - pos - 1 |}.
Proof.
  intros b len pos st i H1 H2 H3 H4. unfold spec_msg_step. cbv beta zeta.
  rewrite (proj2 (Z.leb_gt len pos) H1), H2, H3, (proj2 (Z.eqb_neq i len) H4). reflexivity.
Qed.

Lemma cstep_m_status : forall b len pos st, pos < len -> 240 < byte_at b pos ->
  spec_msg_step b len pos st =
  {| sm_code := -8; sm_at := pos; sm_len := 0; sm_next := pos + 1; sm_status := 0; sm_running := 0; sm_d1 := 0;
     sm_d2 := 0; sm_status_out := 0; sm_sysex_at := 0; sm_sysex_len := 0 |}.
Proof.
  intros b len pos st H1 H2. unfold spec_msg_step. cbv beta zeta.
  rewrite (proj2 (Z.leb_gt len pos) H1), (proj2 (Z.eqb_neq (byte_at b pos) 240) ltac:(lia)),
    (proj2 (Z.ltb_lt 240 (byte_at b pos)) H2). reflexivity.
Qed.

Lemma cstep_m_nost : forall b len pos, pos < len -> byte_at b pos < 128 ->
  spec_msg_step b len pos 0 =
  {| sm_code := -7; sm_at := pos; sm_len := 0; sm_next := pos + 1; sm_status := 0; sm_running := 0; sm_d1 := 0;
     sm_d2 := 0; sm_status_out := 0; sm_sysex_at := 0; sm_sysex_len := 0 |}.
Proof.
  intros b len pos H1 H2. unfold spec_msg_step. cbv beta zeta.
  rewrite (proj2 (Z.leb_gt len pos) H1), (proj2 (Z.eqb_neq (byte_at b pos) 240) ltac:(lia)),
    (proj2 (Z.ltb_ge 240 (byte_at b pos)) ltac:(lia)), (proj2 (Z.ltb_lt (byte_at b pos) 128) H2). reflexivity.
Qed.

(* a channel message: lead is the byte at pos, stv the status in force, pos + dz the first data byte, nb the
   test for one data byte (spec.h:339-363) *)
Lemma cstep_m_chan : forall b len pos st lead stv dz nb,
  pos < len -> byte_at b pos = lead -> 0 <= lead < 240 -> (128 <= lead \/ st <> 0) ->
  stv = (if 128 <=? lead then lead else st) -> dz = (if 128 <=? lead then 1 else 0) ->
  ((Z.land stv 240 =? 192) || (Z.land stv 240 =? 208)) = nb ->
  spec_msg_step b len pos st =
  if len <? pos + dz + (if nb then 1 else 2) then
    {| sm_code := -6; sm_at := pos; sm_len := 0; sm_next := len; sm_status := 0; sm_running := 0; sm_d1 := 0;
       sm_d2 := 0; sm_status_out := st; sm_sysex_at := 0; sm_sysex_len := 0 |}
  else if 128 <=? byte_at b (pos + dz) then
    {| sm_code := -6; sm_at := pos; sm_len := 0; sm_next := pos + dz; sm_status := 0; sm_running := 0;
       sm_d1 := 0; sm_d2 := 0; sm_status_out := 0; sm_sysex_at := 0; sm_sysex_len := 0 |}
  else if negb nb && (128 <=? byte_at b (pos + dz + 1)) then
    {| sm_code := -6; sm_at := pos; sm_len := 0; sm_next := pos + dz + 1; sm_status := 0; sm_running := 0;
       sm_d1 := 0; sm_d2 := 0; sm_status_out := 0; sm_sysex_at := 0; sm_sysex_len := 0 |}
  else
    {| sm_code := 1; sm_at := pos; sm_len := pos + dz + (if nb then 1 else 2) - pos;
       sm_next := pos + dz + (if nb then 1 else 2); sm_status := stv;
       sm_running := if lead <? 128 then 1 else 0; sm_d1 := byte_at b (pos + dz);
       sm_d2 := if nb then 0 else byte_at b (pos + dz + 1); sm_status_out := stv; sm_sysex_at := 0;
       sm_sysex_len := 0 |}.
Proof.
  intros b len pos st lead stv dz nb H1 H2 H3 H4 Hstv Hdz Hnb.
  unfold spec_msg_step. cbv beta zeta.
  rewrite (proj2 (Z.leb_gt len pos) H1), H2.
  rewrite (proj2 (Z.eqb_neq lead 240)) by lia. rewrite (proj2 (Z.ltb_ge 240 lead)) by lia.
  revert Hnb. subst stv dz.
  destruct (Z.leb_spec 128 lead) as [Hh|Hh]; intros Hnb.
  - rewrite (proj2 (Z.ltb_ge lead 128)) by lia. rewrite Hnb. cbv beta iota.
    destruct nb; reflexivity.
  - rewrite (proj2 (Z.ltb_lt lead 128)) by lia. rewrite (proj2 (Z.eqb_neq st 0)) by lia. rewrite Hnb.
    cbv beta iota. rewrite !Z.add_0_r. destruct nb; reflexivity.
Qed.

(* ---- the frame and the end state ---- *)

(* the struct spec_msg the memset leaves, and the same after the stores of at and status_out *)
Definition cstep_mz : spec_msg :=
  {| sm_code := 0; sm_at := 0; sm_len := 0; sm_next := 0; sm_status := 0; sm_running := 0; sm_d1 := 0;
     sm_d2 := 0; sm_status_out := 0; sm_sysex_at := 0; sm_sysex_len := 0 |}.
Definition cstep_m1 (pos status : Z) : spec_msg :=
  {| sm_code := 0; sm_at := pos; sm_len := 0; sm_next := 0; sm_status := 0; sm_running := 0; sm_d1 := 0;
     sm_d2 := 0; sm_status_out := status; sm_sysex_at := 0; sm_sysex_len := 0 |}.

Lemma cstep_mz_cells : forall segs m A,
  rw_cells segs m A [CB 56 (repeat (Z_to_bv 8 0) 56)] -> rw_cells segs m A (spec_msg_cells cstep_mz).
Proof.
  intros segs m A H. apply (cstep_rwc_bytes segs m A _ _ H).
  - cbn. repeat split.
  - apply cstep_bytes_eq. vm_compute. reflexivity.
Qed.

(* the rest of the run from the segment's end *)
Definition cstep_K (Q : machine_state -> Prop) (x3 x4 x19 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (Sp body pos status : Z) (bb j0 : list byte) (w8 w10 : word) (rest : list cell)
    : Prop :=
  forall (r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 : word) (m' : word -> option byte),
     munch [(Sp + 32, Sp + 88)] m0 m' -> wmono rsegs m0 m' -> mem_inv rsegs m' ->
     bytes_at rsegs m' body bb ->
     rw_cells rsegs m' Sp (fr_head j0 w8 w10 body ++
       spec_msg_cells (spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos status) ++ rest) ->
     evt rsegs Q
       (MS (mkR r1 (Z_to_bv 64 Sp) x3 x4 r5 r6 r7 (Z_to_bv 64 status)
              (Z_to_bv 64 (sm_next (spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos status)))
              r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 (Z.of_nat (length bb))) x19
              (Z_to_bv 64 (if sm_code (spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos status) =? 1 then 1 else 0))
              (Z_to_bv 64 body) (Z_to_bv 64 (- Z.of_nat (length bb))) (Z_to_bv 64 240) (Z_to_bv 64 247)
              (Z_to_bv 64 pos)
              (Z_to_bv 64 (sm_status_out (spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos status)))
              (Z_to_bv 64 241) r28 r29 r30 r31)
           F (Z_to_bv 64 0x12ef8) fc None m' (seg_rom rsegs)).

(* the end state 0x12ef8 of a path whose struct is M *)
Lemma cstep_end :
  forall (Q : machine_state -> Prop) (x3 x4 x19 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 m : word -> option byte) (Sp body pos status : Z) (bb j0 : list byte) (w8 w10 : word) (rest : list cell)
    (M : spec_msg) (nx so c1 : Z)
    (r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 : word),
  cstep_K Q x3 x4 x19 F fc m0 Sp body pos status bb j0 w8 w10 rest ->
  spec_msg_step (bzl bb) (Z.of_nat (length bb)) pos status = M ->
  sm_next M = nx -> sm_status_out M = so -> (if sm_code M =? 1 then 1 else 0) = c1 ->
  munch [(Sp + 32, Sp + 88)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> bytes_at rsegs m body bb ->
  rw_cells rsegs m Sp (fr_head j0 w8 w10 body ++ spec_msg_cells M ++ rest) ->
  evt rsegs Q
    (MS (mkR r1 (Z_to_bv 64 Sp) x3 x4 r5 r6 r7 (Z_to_bv 64 status) (Z_to_bv 64 nx)
           r10 r11 r12 r13 r14 r15 r16 r17 (Z_to_bv 64 (Z.of_nat (length bb))) x19 (Z_to_bv 64 c1)
           (Z_to_bv 64 body) (Z_to_bv 64 (- Z.of_nat (length bb))) (Z_to_bv 64 240) (Z_to_bv 64 247)
           (Z_to_bv 64 pos) (Z_to_bv 64 so) (Z_to_bv 64 241) r28 r29 r30 r31)
        F (Z_to_bv 64 0x12ef8) fc None m (seg_rom rsegs)).
Proof.
  intros Q x3 x4 x19 F fc m0 m Sp body pos status bb j0 w8 w10 rest M nx so c1
    r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 K E Hn Hs Hc MU WM MI BA FR.
  subst nx so c1 M. apply K; assumption.
Qed.

(* ---- reading the body ---- *)

Lemma cstep_rd_pl : forall m a bs i, bytes_at rsegs m a bs -> (i < length bs)%nat ->
  ov_read_bytes rsegs m (Z_to_bv 64 (a + Z.of_nat i)) 1 = Some [nth i bs (Z_to_bv 8 0)].
Proof.
  intros m a bs i H Hi.
  change (Z_to_bv 64 (a + Z.of_nat i)) with (wa (a + Z.of_nat i)).
  rewrite (bytes_at_ov_read rsegs m a bs i 1 H ltac:(lia)).
  f_equal. clear H. revert i Hi. induction bs as [|x bs IH]; intros [|i] Hi; cbn [length] in Hi.
  - lia.
  - lia.
  - reflexivity.
  - cbn [skipn nth]. apply IH. lia.
Qed.

Lemma cstep_rd : forall m a bs i, bytes_at rsegs m a bs -> 0 <= i < Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (Z_to_bv 64 (a + i)) 1 = Some [nth (Z.to_nat i) bs (Z_to_bv 8 0)].
Proof.
  intros m a bs i H Hi. pose proof (cstep_rd_pl m a bs (Z.to_nat i) H ltac:(lia)) as R.
  rewrite Z2Nat.id in R by lia. exact R.
Qed.

Ltac cstep_usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end.
Ltac cstep_solve := unfold bv_eqb, bv_ltu, bv_leu, bv_lts; cbn [negb]; cstep_usub; fold_lit_ux; solve_cond_rec.
Ltac cstep_take b := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; cstep_solve]
  end.
(* read the body byte at i: L names it, zxb L is turned into Z_to_bv 64 (bz L), and its range is known *)
Ltac cstep_rd1 i L := lazymatch goal with
  | BA : bytes_at rsegs ?mm ?a ?bs |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let HR := fresh "HR" in pose proof (cstep_rd mm a bs i BA ltac:(lia)) as HR;
      step;
      set (L := nth (Z.to_nat i) bs (Z_to_bv 8 0)) in *;
      change (zxb L) with (Z_to_bv 64 (bz L));
      let RL := fresh "RL" in
      pose proof (bv_unsigned_in_range 8 L) as RL; unfold bv_modulus in RL;
      change (2 ^ Z.of_N 8) with 256 in RL; change (bv_unsigned L) with (bz L) in RL;
      let EL := fresh "EL" in
      assert (EL : byte_at (bzl bs) i = bz L) by (apply cstep_byte_at);
      clear HR
  end.
Ltac cstep_sstep := step; try (rewrite cstep_le1; mem_after_store_opt);
  rewrite ?cstep_not, ?cstep_neg, ?cstep_sub.
Ltac cstep_rds i D ED := lazymatch goal with
  | BA : bytes_at rsegs ?mm ?a ?bs |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let HR := fresh "HR" in pose proof (cstep_rd mm a bs i BA ltac:(lia)) as HR;
      step;
      set (D := nth (Z.to_nat i) bs (Z_to_bv 8 0)) in *;
      let RL := fresh "RL" in
      pose proof (bv_unsigned_in_range 8 D) as RL; unfold bv_modulus in RL;
      change (2 ^ Z.of_N 8) with 256 in RL; change (bv_unsigned D) with (bz D) in RL;
      assert (ED : byte_at (bzl bs) i = bz D) by (apply cstep_byte_at);
      clear HR
  end.
Ltac cstep_rd2 i D := lazymatch goal with
  | BA : bytes_at rsegs ?mm ?a ?bs |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let HR := fresh "HR" in pose proof (cstep_rd mm a bs i BA ltac:(lia)) as HR;
      change (nth (Z.to_nat i) bs (Z_to_bv 8 0)) with D in HR;
      step; change (zxb D) with (Z_to_bv 64 (bz D)); clear HR
  end.
Ltac cstep_run_to t := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) => tryif constr_eq p t then fail else cstep_sstep
  end).
Ltac cstep_zdec := repeat match goal with
  | |- context [?a <=? ?b] => first [rewrite (proj2 (Z.leb_le a b)) by lia | rewrite (proj2 (Z.leb_gt a b)) by lia]
  | |- context [?a <? ?b] => first [rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia]
  end.
Ltac cstep_mfin := cstep_zdec; cbv beta iota; cbn [negb andb]; first [reflexivity | f_equal; first [reflexivity | lia]].

(* ---- the F7 scan, 0x12e30: by induction on len - i ---- *)
Lemma cstep_scan : forall (k : nat)
    (x1 x3 x4 x5 x6 x7 x13 x14 x15 x16 x17 x19 x20 x26 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
    (Sp body pos status i : Z) (bb j0 : list byte) (w8 w10 : word) (rest : list cell)
    (Q : machine_state -> Prop),
  k = Z.to_nat (Z.of_nat (length bb) - i) ->
  seg_ok Sp body bb -> 0 <= pos -> pos + 1 <= i < Z.of_nat (length bb) -> 0 <= status < 256 ->
  byte_at (bzl bb) pos = 240 ->
  scan_f7 (bzl bb) (Z.of_nat (length bb)) (pos + 1) (Z.to_nat (Z.of_nat (length bb) - (pos + 1))) =
    scan_f7 (bzl bb) (Z.of_nat (length bb)) i (Z.to_nat (Z.of_nat (length bb) - i)) ->
  cstep_K Q x3 x4 x19 F fc m0 Sp body pos status bb j0 w8 w10 rest ->
  munch [(Sp + 32, Sp + 88)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> bytes_at rsegs m body bb ->
  rw_cells rsegs m Sp (fr_head j0 w8 w10 body ++ spec_msg_cells (cstep_m1 pos status) ++ rest) ->
  evt rsegs Q
    (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 (Z_to_bv 64 status) (Z_to_bv 64 (pos + 1)) (Z_to_bv 64 (pos + 1))
           (Z_to_bv 64 (- i)) (Z_to_bv 64 (body + i)) x13 x14 x15 x16 x17
           (Z_to_bv 64 (Z.of_nat (length bb))) x19 x20 (Z_to_bv 64 body) (Z_to_bv 64 (- Z.of_nat (length bb)))
           (Z_to_bv 64 240) (Z_to_bv 64 247) (Z_to_bv 64 pos) x26 (Z_to_bv 64 241) x28 x29 x30 x31)
        F (Z_to_bv 64 0x12e30) fc None m (seg_rom rsegs)).
Proof.
  induction k as [|k IH];
    intros x1 x3 x4 x5 x6 x7 x13 x14 x15 x16 x17 x19 x20 x26 x28 x29 x30 x31 F fc m0 m Sp body pos status i
      bb j0 w8 w10 rest Q Hk SEG Hp0 Hi Hst Hlead Hinv K MU WM MI BA FR.
  { lia. }
  pose proof SEG as (S0 & S1 & B0 & B1 & L26).
  unfold fr_head, spec_msg_cells, cstep_m1 in FR.
  cbn [app sm_code sm_at sm_len sm_next sm_status sm_running sm_d1 sm_d2 sm_status_out sm_sysex_at sm_sysex_len] in FR.
  cstep_rd1 i Li.
  step.
  destruct (Z.eq_dec (bz Li) 247) as [E|N].
  - (* an F7 at i: the whole sysex *)
    cstep_take true. cstep_sstep. rewrite Z.opp_involutive.
    cstep_sstep. step. cstep_take true.
    do 13 cstep_sstep.
    replace (b8 (-16)) with (b8 240) in FR by (apply bv_eq; reflexivity).
    eapply (cstep_end Q x3 x4 x19 F fc m0 _ Sp body pos status bb j0 w8 w10 rest
      {| sm_code := 1; sm_at := pos; sm_len := i + 1 - pos; sm_next := i + 1; sm_status := 240;
         sm_running := 0; sm_d1 := 0; sm_d2 := 0; sm_status_out := 0; sm_sysex_at := pos + 1;
         sm_sysex_len := i + (- pos - 1) |});
      [exact K | | reflexivity | reflexivity | reflexivity | eassumption .. ].
    rewrite (cstep_m_f0_ok _ _ _ _ i); [f_equal; lia | lia | exact Hlead | | lia].
    rewrite Hinv. apply cstep_scan_hit; lia.
  - cstep_take false. cstep_sstep. cstep_sstep. step.
    rewrite cstep_eqb by lia.
    destruct (Z.eq_dec (i + 1) (Z.of_nat (length bb))) as [Ei|Ni].
    + (* no F7 before the end *)
      cstep_take false. do 9 cstep_sstep.
      eapply (cstep_end Q x3 x4 x19 F fc m0 _ Sp body pos status bb j0 w8 w10 rest
        {| sm_code := -6; sm_at := pos; sm_len := 0; sm_next := Z.of_nat (length bb); sm_status := 0;
           sm_running := 0; sm_d1 := 0; sm_d2 := 0; sm_status_out := 0; sm_sysex_at := 0; sm_sysex_len := 0 |});
        [exact K | | reflexivity | reflexivity | reflexivity | eassumption .. ].
      apply cstep_m_f0_trunc; [lia | exact Hlead |].
      rewrite Hinv, cstep_scan_step by lia. rewrite Ei. apply cstep_scan_end.
    + cstep_take true.
      replace (- i + -1) with (- (i + 1)) by lia.
      replace (body + i + 1) with (body + (i + 1)) by lia.
      eapply IH; try reflexivity; try eassumption; try lia.
      rewrite Hinv. apply cstep_scan_step; lia.
Qed.

(* ---- bytes: facts checked on all 256 values ---- *)

Lemma cstep_all256 : forall (P : Z -> bool), forallb P (map Z.of_nat (seq 0 256)) = true ->
  forall z, 0 <= z < 256 -> P z = true.
Proof.
  intros P H z Hz. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat z).
  split; [lia | apply in_seq; lia].
Qed.

(* slli 56 then srai 56, and bltz: the byte's bit 7 *)
Lemma cstep_bf_srai : forall z, 0 <= z < 256 ->
  bv_lts (Z_to_bv 64 (bv_signed (Z_to_bv 64 (Z.shiftl z 56)) ≫ 56)) (Z_to_bv 64 0) = (128 <=? z).
Proof.
  intros z Hz. apply Bool.eqb_prop.
  exact (cstep_all256 (fun z => Bool.eqb (bv_lts (Z_to_bv 64 (bv_signed (Z_to_bv 64 (Z.shiftl z 56)) ≫ 56))
    (Z_to_bv 64 0)) (128 <=? z)) ltac:(vm_compute; reflexivity) z Hz).
Qed.

(* slli 56 and bltz *)
Lemma cstep_bf_sll : forall z, 0 <= z < 256 ->
  bv_lts (Z_to_bv 64 (Z.shiftl z 56)) (Z_to_bv 64 0) = (128 <=? z).
Proof.
  intros z Hz. apply Bool.eqb_prop.
  exact (cstep_all256 (fun z => Bool.eqb (bv_lts (Z_to_bv 64 (Z.shiftl z 56)) (Z_to_bv 64 0)) (128 <=? z))
    ltac:(vm_compute; reflexivity) z Hz).
Qed.

(* srli 7 *)
Lemma cstep_bf_srl7 : forall z, 0 <= z < 256 -> Z.shiftr z 7 = (if 128 <=? z then 1 else 0).
Proof.
  intros z Hz. apply Z.eqb_eq.
  exact (cstep_all256 (fun z => Z.shiftr z 7 =? (if 128 <=? z then 1 else 0)) ltac:(vm_compute; reflexivity) z Hz).
Qed.

(* andi 0xe0 *)
Lemma cstep_bf_land : forall z, 0 <= z < 256 -> 0 <= Z.land z 224 < 256.
Proof.
  intros z Hz.
  pose proof (cstep_all256 (fun z => (0 <=? Z.land z 224) && (Z.land z 224 <? 256)) ltac:(vm_compute; reflexivity)
    z Hz) as H.
  apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

(* the length test of spec.h:341 on the status's high nibble, as the code does it on bits 7..5 *)
Lemma cstep_bf_n : forall z, 0 <= z < 256 ->
  ((Z.land z 240 =? 192) || (Z.land z 240 =? 208)) = (Z.land z 224 =? 192).
Proof.
  intros z Hz. apply Bool.eqb_prop.
  exact (cstep_all256 (fun z => Bool.eqb ((Z.land z 240 =? 192) || (Z.land z 240 =? 208)) (Z.land z 224 =? 192))
    ltac:(vm_compute; reflexivity) z Hz).
Qed.

Lemma cstep_b8_bz : forall b : byte, Z_to_bv 8 (bz b) = b.
Proof.
  intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* lb and bltz: the byte's bit 7 *)
Lemma cstep_lts_sxb : forall b : byte, bv_lts (sxb b) (Z_to_bv 64 0) = (128 <=? bz b).
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 8) with 256 in R.
  pose proof (cstep_all256 (fun z => Bool.eqb (bv_lts (sxb (Z_to_bv 8 z)) (Z_to_bv 64 0)) (128 <=? z))
    ltac:(vm_compute; reflexivity) (bz b) R) as H.
  cbv beta in H. apply Bool.eqb_prop in H. rewrite cstep_b8_bz in H. exact H.
Qed.

(* not, slli 56, srli 63: running = lead < 0x80 *)
Lemma cstep_bf_run : forall z, 0 <= z < 256 ->
  Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (- z - 1)) ≪ 56)) ≫ 63) =
  Z_to_bv 64 (if z <? 128 then 1 else 0).
Proof.
  intros z Hz.
  pose proof (cstep_all256 (fun z => bv_eqb (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (- z - 1))
    ≪ 56)) ≫ 63)) (Z_to_bv 64 (if z <? 128 then 1 else 0))) ltac:(vm_compute; reflexivity) z Hz) as H.
  cbv beta in H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H.
Qed.

(* ---- a channel message from 0x12f60, its status stv in s10 ---- *)
Lemma cstep_chan2 :
  forall (x1 x3 x4 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
    (Sp body pos status : Z) (bb j0 : list byte) (w8 w10 : word) (rest : list cell)
    (Q : machine_state -> Prop) (L : byte) (stv dz : Z),
  seg_ok Sp body bb -> 0 <= pos < Z.of_nat (length bb) -> 0 <= status < 256 ->
  byte_at (bzl bb) pos = bz L -> 0 <= bz L < 240 -> (128 <= bz L \/ status <> 0) ->
  stv = (if 128 <=? bz L then bz L else status) -> dz = (if 128 <=? bz L then 1 else 0) ->
  cstep_K Q x3 x4 x19 F fc m0 Sp body pos status bb j0 w8 w10 rest ->
  munch [(Sp + 32, Sp + 88)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> bytes_at rsegs m body bb ->
  rw_cells rsegs m Sp (fr_head j0 w8 w10 body ++ spec_msg_cells (cstep_m1 pos status) ++ rest) ->
  evt rsegs Q
    (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 (Z_to_bv 64 status) x9 (Z_to_bv 64 (bz L))
           x11 x12 x13 x14 x15 x16 x17
           (Z_to_bv 64 (Z.of_nat (length bb))) x19 x20 (Z_to_bv 64 body) (Z_to_bv 64 (- Z.of_nat (length bb)))
           (Z_to_bv 64 240) (Z_to_bv 64 247) (Z_to_bv 64 pos) (Z_to_bv 64 stv) (Z_to_bv 64 241) x28 x29 x30 x31)
        F (Z_to_bv 64 0x12f60) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x3 x4 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x28 x29 x30 x31
    F fc m0 m Sp body pos status bb j0 w8 w10 rest Q L stv dz SEG Hpos Hst EL HL HLs Hsv Hdz K MU WM MI BA FR.
  pose proof SEG as (S0 & S1 & B0 & B1 & L26).
  unfold fr_head, spec_msg_cells, cstep_m1 in FR.
  cbn [app sm_code sm_at sm_len sm_next sm_status sm_running sm_d1 sm_d2 sm_status_out sm_sysex_at sm_sysex_len] in FR.
  assert (Hstv : 0 <= stv < 256) by (subst stv; destruct (128 <=? bz L); lia).
  assert (Hdz' : Z.shiftr (bz L) 7 = dz) by (rewrite cstep_bf_srl7 by lia; subst dz; reflexivity).
  assert (Hdz2 : dz = 0 \/ dz = 1) by (subst dz; destruct (128 <=? bz L); lia).
  pose proof (cstep_bf_land stv Hstv) as Hland.
  cstep_sstep. rewrite (unsigned_lit (bz L)) by lia. rewrite Hdz'.
  cstep_sstep. rewrite (unsigned_lit stv) by lia.
  cstep_sstep. cstep_sstep. cstep_sstep.
  rewrite cstep_snez by lia.
  destruct (Z.eq_dec (Z.land stv 224) 192) as [N1|N2].
  - (* one data byte: C0 .. DF *)
    assert (Hnb : ((Z.land stv 240 =? 192) || (Z.land stv 240 =? 208)) = true)
      by (rewrite cstep_bf_n by lia; apply Z.eqb_eq; exact N1).
    pose proof (cstep_m_chan (bzl bb) (Z.of_nat (length bb)) pos status (bz L) stv dz true
      ltac:(lia) EL ltac:(lia) HLs Hsv Hdz Hnb) as Em.
    rewrite N1. change (Z.b2z (negb (192 + -192 =? 0))) with 0.
    cstep_sstep. cstep_sstep. step.
    destruct (Z_lt_le_dec (Z.of_nat (length bb)) (1 + (pos + dz))) as [Hs|Hs].
    + (* cut short at the end of the body *)
      cstep_take false. cstep_run_to 0x12ef8.
      eapply (cstep_end Q x3 x4 x19 F fc m0 _ Sp body pos status bb j0 w8 w10 rest
        {| sm_code := -6; sm_at := pos; sm_len := 0; sm_next := Z.of_nat (length bb); sm_status := 0;
           sm_running := 0; sm_d1 := 0; sm_d2 := 0; sm_status_out := status; sm_sysex_at := 0; sm_sysex_len := 0 |});
        [exact K | | reflexivity | reflexivity | reflexivity | eassumption .. ].
      rewrite Em. cstep_mfin.
    + cstep_take true. cstep_sstep. cstep_sstep.
      cstep_rds (pos + dz) D0 ED0. step. rewrite cstep_lts_sxb.
      destruct (Z_lt_le_dec (bz D0) 128) as [D0l|D0h].
      2: { (* a status byte where d1 is due *)
        cstep_take true. cstep_run_to 0x12ef8. rewrite Z.opp_involutive in *.
        eapply (cstep_end Q x3 x4 x19 F fc m0 _ Sp body pos status bb j0 w8 w10 rest
          {| sm_code := -6; sm_at := pos; sm_len := 0; sm_next := pos + dz; sm_status := 0;
             sm_running := 0; sm_d1 := 0; sm_d2 := 0; sm_status_out := 0; sm_sysex_at := 0; sm_sysex_len := 0 |});
          [exact K | | reflexivity | reflexivity | reflexivity | eassumption .. ].
        rewrite Em, ED0. cstep_mfin. }
      cstep_take false. cstep_sstep. cstep_sstep. cstep_sstep. step. cstep_take false.
      cstep_sstep. cstep_sstep. cstep_sstep.
      rewrite (cstep_bf_run (bz L)) by lia.
      cstep_sstep. cstep_sstep. cstep_sstep. cstep_sstep. cstep_sstep.
      cstep_rd2 (pos + dz) D0.
      cstep_sstep. cstep_sstep. step. cstep_take false.
      cstep_run_to 0x12ef8.
      eapply (cstep_end Q x3 x4 x19 F fc m0 _ Sp body pos status bb j0 w8 w10 rest
        {| sm_code := 1; sm_at := pos; sm_len := 1 + (pos + dz) - pos; sm_next := 1 + (pos + dz); sm_status := stv;
           sm_running := if bz L <? 128 then 1 else 0; sm_d1 := bz D0; sm_d2 := 0; sm_status_out := stv;
           sm_sysex_at := 0; sm_sysex_len := 0 |});
        [exact K | | reflexivity | reflexivity | reflexivity | eassumption .. ].
      rewrite Em, ED0. cstep_mfin.
  - (* two data bytes *)
    assert (Hnb : ((Z.land stv 240 =? 192) || (Z.land stv 240 =? 208)) = false)
      by (rewrite cstep_bf_n by lia; apply Z.eqb_neq; exact N2).
    pose proof (cstep_m_chan (bzl bb) (Z.of_nat (length bb)) pos status (bz L) stv dz false
      ltac:(lia) EL ltac:(lia) HLs Hsv Hdz Hnb) as Em.
    rewrite (proj2 (Z.eqb_neq (Z.land stv 224 + -192) 0)) by lia. change (Z.b2z (negb false)) with 1.
    cstep_sstep. cstep_sstep. step.
    destruct (Z_lt_le_dec (Z.of_nat (length bb)) (2 + (pos + dz))) as [Hs|Hs].
    + (* cut short at the end of the body *)
      cstep_take false. cstep_run_to 0x12ef8.
      eapply (cstep_end Q x3 x4 x19 F fc m0 _ Sp body pos status bb j0 w8 w10 rest
        {| sm_code := -6; sm_at := pos; sm_len := 0; sm_next := Z.of_nat (length bb); sm_status := 0;
           sm_running := 0; sm_d1 := 0; sm_d2 := 0; sm_status_out := status; sm_sysex_at := 0; sm_sysex_len := 0 |});
        [exact K | | reflexivity | reflexivity | reflexivity | eassumption .. ].
      rewrite Em. cstep_mfin.
    + cstep_take true. cstep_sstep. cstep_sstep.
      cstep_rds (pos + dz) D0 ED0. step. rewrite cstep_lts_sxb.
      destruct (Z_lt_le_dec (bz D0) 128) as [D0l|D0h].
      2: { (* a status byte where d1 is due *)
        cstep_take true. cstep_run_to 0x12ef8. rewrite Z.opp_involutive in *.
        eapply (cstep_end Q x3 x4 x19 F fc m0 _ Sp body pos status bb j0 w8 w10 rest
          {| sm_code := -6; sm_at := pos; sm_len := 0; sm_next := pos + dz; sm_status := 0;
             sm_running := 0; sm_d1 := 0; sm_d2 := 0; sm_status_out := 0; sm_sysex_at := 0; sm_sysex_len := 0 |});
          [exact K | | reflexivity | reflexivity | reflexivity | eassumption .. ].
        rewrite Em, ED0. cstep_mfin. }
      cstep_take false. cstep_sstep. cstep_sstep. cstep_sstep. step. cstep_take true.
      cstep_rds (pos + dz + 1) D1 ED1. step. rewrite cstep_lts_sxb.
      destruct (Z_lt_le_dec (bz D1) 128) as [D1l|D1h].
      2: { (* a status byte where d2 is due *)
        cstep_take true. cstep_run_to 0x12ef8.
        replace (- (- (pos + dz) + -1)) with (pos + dz + 1) in * by lia.
        eapply (cstep_end Q x3 x4 x19 F fc m0 _ Sp body pos status bb j0 w8 w10 rest
          {| sm_code := -6; sm_at := pos; sm_len := 0; sm_next := pos + dz + 1; sm_status := 0;
             sm_running := 0; sm_d1 := 0; sm_d2 := 0; sm_status_out := 0; sm_sysex_at := 0; sm_sysex_len := 0 |});
          [exact K | | reflexivity | reflexivity | reflexivity | eassumption .. ].
        rewrite Em, ED0, ED1. cstep_mfin. }
      cstep_take false. cstep_sstep. cstep_sstep. cstep_sstep. step. cstep_take false.
      cstep_sstep. cstep_sstep. cstep_sstep.
      rewrite (cstep_bf_run (bz L)) by lia.
      cstep_sstep. cstep_sstep. cstep_sstep. cstep_sstep. cstep_sstep.
      cstep_rd2 (pos + dz) D0.
      cstep_sstep. cstep_sstep. step. cstep_take true.
      cstep_rd2 (pos + dz + 1) D1.
      cstep_run_to 0x12ef8.
      eapply (cstep_end Q x3 x4 x19 F fc m0 _ Sp body pos status bb j0 w8 w10 rest
        {| sm_code := 1; sm_at := pos; sm_len := 2 + (pos + dz) - pos; sm_next := 2 + (pos + dz); sm_status := stv;
           sm_running := if bz L <? 128 then 1 else 0; sm_d1 := bz D0; sm_d2 := bz D1; sm_status_out := stv;
           sm_sysex_at := 0; sm_sysex_len := 0 |});
        [exact K | | reflexivity | reflexivity | reflexivity | eassumption .. ].
      rewrite Em, ED0, ED1. cstep_mfin.
Qed.

(* ---- a channel message, 0x12f54 ---- *)
Lemma cstep_chan :
  forall (x1 x3 x4 x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x19 x20 x26 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
    (Sp body pos status : Z) (bb j0 : list byte) (w8 w10 : word) (rest : list cell)
    (Q : machine_state -> Prop) (L : byte),
  seg_ok Sp body bb -> 0 <= pos < Z.of_nat (length bb) -> 0 <= status < 256 ->
  byte_at (bzl bb) pos = bz L -> 0 <= bz L < 240 -> (128 <= bz L \/ status <> 0) ->
  cstep_K Q x3 x4 x19 F fc m0 Sp body pos status bb j0 w8 w10 rest ->
  munch [(Sp + 32, Sp + 88)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> bytes_at rsegs m body bb ->
  rw_cells rsegs m Sp (fr_head j0 w8 w10 body ++ spec_msg_cells (cstep_m1 pos status) ++ rest) ->
  evt rsegs Q
    (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 (Z_to_bv 64 status) x9 (Z_to_bv 64 (bz L))
           (Z_to_bv 64 (Z.shiftl (bz L) 56)) x12 x13 x14 x15 x16 x17
           (Z_to_bv 64 (Z.of_nat (length bb))) x19 x20 (Z_to_bv 64 body) (Z_to_bv 64 (- Z.of_nat (length bb)))
           (Z_to_bv 64 240) (Z_to_bv 64 247) (Z_to_bv 64 pos) x26 (Z_to_bv 64 241) x28 x29 x30 x31)
        F (Z_to_bv 64 0x12f54) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x3 x4 x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x19 x20 x26 x28 x29 x30 x31
    F fc m0 m Sp body pos status bb j0 w8 w10 rest Q L SEG Hpos Hst EL HL HLs K MU WM MI BA FR.
  pose proof SEG as (S0 & S1 & B0 & B1 & L26).
  unfold fr_head, spec_msg_cells, cstep_m1 in FR.
  cbn [app sm_code sm_at sm_len sm_next sm_status sm_running sm_d1 sm_d2 sm_status_out sm_sysex_at sm_sysex_len] in FR.
  cstep_sstep. step.
  rewrite (cstep_bf_sll (bz L)) by lia.
  destruct (Z_lt_le_dec (bz L) 128) as [Hl128|Hg128].
  - cstep_take false. cstep_sstep.
    eapply (cstep_chan2 x1 x3 x4 x5 x6 x7 x9 _ _ x13 x14 x15 x16 x17 x19 x20 x28 x29 x30 x31 F fc m0 _
      Sp body pos status bb j0 w8 w10 rest Q L status 0); try eassumption; try lia.
    + rewrite (proj2 (Z.leb_gt 128 (bz L))) by lia. reflexivity.
    + rewrite (proj2 (Z.leb_gt 128 (bz L))) by lia. reflexivity.
  - cstep_take true.
    eapply (cstep_chan2 x1 x3 x4 x5 x6 x7 x9 _ _ x13 x14 x15 x16 x17 x19 x20 x28 x29 x30 x31 F fc m0 _
      Sp body pos status bb j0 w8 w10 rest Q L (bz L) 1); try eassumption; try lia.
    + rewrite (proj2 (Z.leb_le 128 (bz L))) by lia. reflexivity.
    + rewrite (proj2 (Z.leb_le 128 (bz L))) by lia. reflexivity.
Qed.

(* the inlined spec_msg_step from 0x12dec, after the memset *)
Lemma cstep_body :
  forall (x1 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x26 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
    (Sp body pos status : Z) (bb j0 : list byte) (w8 w10 : word) (rest : list cell)
    (Q : machine_state -> Prop),
  seg_ok Sp body bb ->
  0 <= pos <= Z.of_nat (length bb) -> 0 <= status < 256 ->
  cstep_K Q x3 x4 x19 F fc m0 Sp body pos status bb j0 w8 w10 rest ->
  munch [(Sp + 32, Sp + 88)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  bytes_at rsegs m body bb ->
  rw_cells rsegs m Sp (fr_head j0 w8 w10 body ++ spec_msg_cells cstep_mz ++ rest) ->
  evt rsegs Q
    (MS (mkR x1 (Z_to_bv 64 Sp) x3 x4 x5 x6 x7 (Z_to_bv 64 status) x9 x10 x11 x12 x13 x14 x15 x16 x17
           (Z_to_bv 64 (Z.of_nat (length bb))) x19 x20 (Z_to_bv 64 body) (Z_to_bv 64 (- Z.of_nat (length bb)))
           (Z_to_bv 64 240) (Z_to_bv 64 247) (Z_to_bv 64 pos) x26 (Z_to_bv 64 241) x28 x29 x30 x31)
        F (Z_to_bv 64 0x12dec) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x26 x28 x29 x30 x31
    F fc m0 m Sp body pos status bb j0 w8 w10 rest Q SEG Hpos Hst K MU WM MI BA FR.
  pose proof SEG as (S0 & S1 & B0 & B1 & L26).
  unfold fr_head, spec_msg_cells, cstep_mz in FR.
  cbn [app sm_code sm_at sm_len sm_next sm_status sm_running sm_d1 sm_d2 sm_status_out sm_sysex_at sm_sysex_len] in FR.
  cstep_sstep. cstep_sstep. step.
  destruct (Z_lt_le_dec pos (Z.of_nat (length bb))) as [Hlt|Hge].
  2: { (* the end of the body *)
    cstep_take false.
    do 5 cstep_sstep.
    eapply (cstep_end Q x3 x4 x19 F fc m0 _ Sp body pos status bb j0 w8 w10 rest
      {| sm_code := 0; sm_at := pos; sm_len := 0; sm_next := pos; sm_status := 0; sm_running := 0; sm_d1 := 0;
         sm_d2 := 0; sm_status_out := status; sm_sysex_at := 0; sm_sysex_len := 0 |});
      [exact K | apply cstep_m_end; lia | reflexivity | reflexivity | reflexivity | eassumption .. ]. }
  cstep_take true.
  cstep_sstep.
  cstep_rd1 pos L.
  step.
  destruct (Z.eq_dec (bz L) 240) as [E240|N240].
  - (* F0 *)
    cstep_take false. cstep_sstep. cstep_sstep. step.
    destruct (Z_lt_le_dec (pos + 1) (Z.of_nat (length bb))) as [Hlt1|Hge1].
    + cstep_take false. cstep_sstep. cstep_sstep. cstep_sstep.
      replace (- pos - 1) with (- (pos + 1)) by lia.
      replace (body + 1 + pos) with (body + (pos + 1)) by lia.
      eapply (cstep_scan _ x1 x3 x4 x5 x6 x7 x13 x14 x15 x16 x17 x19 x20 x26 x28 x29 x30 x31 F fc m0 _
        Sp body pos status (pos + 1)); try reflexivity; try eassumption; try lia.
    + cstep_take true. cstep_sstep. step. cstep_take false.
      do 7 cstep_sstep.
      eapply (cstep_end Q x3 x4 x19 F fc m0 _ Sp body pos status bb j0 w8 w10 rest
        {| sm_code := -6; sm_at := pos; sm_len := 0; sm_next := Z.of_nat (length bb); sm_status := 0;
           sm_running := 0; sm_d1 := 0; sm_d2 := 0; sm_status_out := 0; sm_sysex_at := 0; sm_sysex_len := 0 |});
        [exact K | | reflexivity | reflexivity | reflexivity | eassumption .. ].
      apply cstep_m_f0_trunc; [lia | rewrite EL; exact E240 |].
      replace (pos + 1) with (Z.of_nat (length bb)) by lia. apply cstep_scan_end.
  - cstep_take true. step.
    destruct (Z_lt_le_dec (bz L) 241) as [Hl241|Hg241].
    + cstep_take true. cstep_sstep. step.
      rewrite (unsigned_lit (bz L)) by lia.
      destruct (Z.eq_dec status 0) as [Sz|Snz].
      * cstep_take false. cstep_sstep. step.
        rewrite (cstep_bf_srai (bz L)) by lia.
        destruct (Z_lt_le_dec (bz L) 128) as [Hl128|Hg128].
        -- (* a data byte with no running status *)
           cstep_take false. subst status. do 7 cstep_sstep.
           eapply (cstep_end Q x3 x4 x19 F fc m0 _ Sp body pos 0 bb j0 w8 w10 rest
             {| sm_code := -7; sm_at := pos; sm_len := 0; sm_next := pos + 1; sm_status := 0;
                sm_running := 0; sm_d1 := 0; sm_d2 := 0; sm_status_out := 0; sm_sysex_at := 0; sm_sysex_len := 0 |});
             [exact K | apply cstep_m_nost; lia | reflexivity | reflexivity | reflexivity | eassumption .. ].
        -- cstep_take true.
           eapply (cstep_chan x1 x3 x4 x5 x6 x7 x9); try reflexivity; try eassumption; lia.
      * cstep_take true.
        eapply (cstep_chan x1 x3 x4 x5 x6 x7 x9); try reflexivity; try eassumption; lia.
    + (* F1 .. FF *)
      cstep_take false. do 8 cstep_sstep.
      eapply (cstep_end Q x3 x4 x19 F fc m0 _ Sp body pos status bb j0 w8 w10 rest
        {| sm_code := -8; sm_at := pos; sm_len := 0; sm_next := pos + 1; sm_status := 0;
           sm_running := 0; sm_d1 := 0; sm_d2 := 0; sm_status_out := 0; sm_sysex_at := 0; sm_sysex_len := 0 |});
        [exact K | apply cstep_m_status; lia | reflexivity | reflexivity | reflexivity | eassumption .. ].
Qed.

Theorem cstep_holds : cstep_stmt.
Proof.
  unfold cstep_stmt.
  intros MSET x1 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x26 x28 x29 x30 x31
    F fc m Sp body pos status bb j0 mj w8 w10 rest Q SEG Hpos Hst BA FR MI K.
  pose proof SEG as (S0 & S1 & B0 & B1 & L26).
  pose proof (bytes_at_bound _ _ _ _ BA) as BAb.
  unfold fr_head in FR.
  destruct (cstep_rw_split rsegs m Sp [CB 8 j0; C8 w8; C8 w10; C8 (Z_to_bv 64 (body + 1))] (CB 56 mj :: rest) FR)
    as [FR1 FR23].
  change (Sp + Z.of_nat (cells_size [CB 8 j0; C8 w8; C8 w10; C8 (Z_to_bv 64 (body + 1))])) with (Sp + 32) in FR23.
  destruct (cstep_rw_split rsegs m (Sp + 32) [CB 56 mj] rest FR23) as [FR2 FR3]. clear FR FR23.
  replace (Sp + 32 + Z.of_nat (cells_size [CB 56 mj])) with (Sp + 88) in FR3 by (cbn [cells_size csize]; lia).
  step. step. step. step.
  eapply evt_cut.
  { eapply MSET with (junk := mj).
    - rewrite !unsigned_lit by lia. exact FR2.
    - exact MI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU & WM
    & MI1 & RW1).
  rewrite !unsigned_lit in MU, RW1 by lia.
  replace (Sp + 32 + 56) with (Sp + 88) in MU by lia.
  change (Z.to_nat 56) with 56%nat in RW1. change (0 mod 256) with 0 in RW1.
  apply cstep_mz_cells in RW1.
  apply (rw_cells_transport rsegs [(Sp + 32, Sp + 88)] m m1) in FR1; [| exact MU | exact WM | cbn; lia].
  apply (rw_cells_transport rsegs [(Sp + 32, Sp + 88)] m m1) in FR3; [| exact MU | exact WM | cbn; lia].
  apply (bytes_at_transport rsegs [(Sp + 32, Sp + 88)] m m1) in BA; [| exact MU | cbn; lia].
  replace (ret_pc (Z_to_bv 64 77292)) with (Z_to_bv 64 77292) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  eapply cstep_body; try eassumption.
  unfold fr_head. apply (cstep_rw_app rsegs m1 Sp _ _ FR1).
  apply (cstep_rw_app rsegs m1 _ _ _ RW1).
  replace (Sp + 32 + Z.of_nat (cells_size (spec_msg_cells cstep_mz))) with (Sp + 88)
    by (rewrite spec_msg_cells_size; lia).
  exact FR3.
Qed.
