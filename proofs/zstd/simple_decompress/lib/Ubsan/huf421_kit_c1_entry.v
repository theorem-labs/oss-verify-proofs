(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Bytes.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require ZdWalkKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx41f RZ_huf_dx42_5.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Fixpoint c1_c8s_of (k : nat) (bs : list byte) : list cell :=
  match k with O => [] | S k' => C8 (le_bytes_to_word (firstn 8 bs)) :: c1_c8s_of k' (skipn 8 bs) end.

Lemma c1_c8s_of_props : forall k bs, length bs = (8 * k)%nat ->
  cells_wf (c1_c8s_of k bs) /\ cells_bytes (c1_c8s_of k bs) = bs /\ cells_size (c1_c8s_of k bs) = (8 * k)%nat.
Proof.
  induction k as [|k IH]; intros bs HL.
  - destruct bs; [|discriminate]. cbn. repeat split; try constructor.
  - cbn [c1_c8s_of]. assert (L2 : length (skipn 8 bs) = (8 * k)%nat) by (rewrite skipn_length; lia).
    destruct (IH _ L2) as (W & B & S'). split; [|split].
    + split; [exact I | exact W].
    + cbn [cells_bytes cbytes]. rewrite B, le8_of_bytes by (rewrite firstn_length; lia). apply firstn_skipn.
    + cbn [cells_size csize]. rewrite S'. lia.
Qed.

Lemma c1_cb_as_c8s : forall m A (k : nat) bs, rw_cells usegs m A [CB (8 * k) bs] -> rw_cells usegs m A (c1_c8s_of k bs).
Proof.
  intros m A k bs H. assert (HL : length bs = (8 * k)%nat).
  { destruct H as [[W _] _]. exact (proj1 W). }
  destruct (c1_c8s_of_props k bs HL) as (W & B & S').
  apply (InitMem.rw_cells_recast usegs m A _ _ H W).
  - rewrite B. cbn [cells_bytes cbytes]. rewrite app_nil_r. reflexivity.
  - rewrite S'. cbn [cells_size csize]. lia.
Qed.

Lemma c1_frame400 : forall m A bs, rw_cells usegs m A [CB 400 bs] ->
  (exists w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : word,
     rw_cells usegs m A [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                         C8 w14; C8 w15; C8 w16]) /\
  (exists j4, rw_cells usegs m (A + 136) [CB 40 j4]) /\ (exists j3, rw_cells usegs m (A + 176) [CB 40 j3]) /\
  (exists j2, rw_cells usegs m (A + 216) [CB 40 j2]) /\ (exists j1, rw_cells usegs m (A + 256) [CB 40 j1]) /\
  (exists u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 : word,
     rw_cells usegs m (A + 296) [C8 u0; C8 u1; C8 u2; C8 u3; C8 u4; C8 u5; C8 u6; C8 u7; C8 u8; C8 u9; C8 u10; C8 u11; C8 u12]).
Proof.
  intros m A bs H.
  destruct (cb_carve usegs m A 400 bs 136 40 H ltac:(lia) ltac:(lia) ltac:(lia)) as (j1 & j2 & j3 & H1 & H2 & H3).
  change (Z.to_nat 136) with 136%nat in H1, H3. change (Z.to_nat 40) with 40%nat in H2, H3.
  change (400 - 136 - 40)%nat with 224%nat in H3. replace (A + 136 + 40) with (A + 176) in H3 by lia.
  destruct (cb_carve usegs m (A + 176) 224 j3 40 40 H3 ltac:(lia) ltac:(lia) ltac:(lia)) as (j4 & j5 & j6 & H4 & H5 & H6).
  change (Z.to_nat 40) with 40%nat in H4, H5, H6. change (224 - 40 - 40)%nat with 144%nat in H6.
  replace (A + 176 + 40) with (A + 216) in H5 by lia. replace (A + 176 + 40 + 40) with (A + 256) in H6 by lia.
  destruct (cb_carve usegs m (A + 256) 144 j6 40 104 H6 ltac:(lia) ltac:(lia) ltac:(lia)) as (j7 & j8 & j9 & H7 & H8 & _).
  change (Z.to_nat 40) with 40%nat in H7. change (Z.to_nat 104) with 104%nat in H8.
  replace (A + 256 + 40) with (A + 296) in H8 by lia.
  pose proof (c1_cb_as_c8s m A 17 j1 H1) as F1. cbn [c1_c8s_of] in F1.
  pose proof (c1_cb_as_c8s m (A + 296) 13 j8 H8) as F2. cbn [c1_c8s_of] in F2.
  split; [do 17 eexists; exact F1|]. split; [eexists; exact H2|]. split; [eexists; exact H4|].
  split; [eexists; exact H5|]. split; [eexists; exact H7|]. do 13 eexists; exact F2.
Qed.

Lemma c1_le16 : forall x y, 0 <= x < 256 -> 0 <= y < 256 -> Z.lor (Z.shiftl x 8) y = 256 * x + y.
Proof.
  intros x y Hx Hy. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (ZdWalkKit.lor_add_disj 8 (x * 2^8) y) by first [lia | rewrite Z.mod_mul by lia; reflexivity]. lia.
Qed.

Lemma c1_sbuf_sub : forall SPV DST dcap lo mm SRC n src A k len,
  bytes_at usegs mm SRC src -> zlen src = n -> 4096 <= SRC -> SRC + n < 2^47 -> n < 2^32 ->
  (DST + dcap <= SRC \/ SRC + n <= DST) -> (SRC + n <= lo \/ SPV <= SRC) ->
  0 <= k -> 0 <= len -> k + len <= n -> A = SRC + k ->
  RZ_huf_dx41f.SBUF SPV DST dcap lo mm A len (firstn (Z.to_nat len) (skipn (Z.to_nat k) src)).
Proof.
  intros SPV DST dcap lo mm SRC n src A k len HB HL R0 R1' R2 D1 D2 HK HLEN HKL ->.
  assert (LEN : zlen (firstn (Z.to_nat len) (skipn (Z.to_nat k) src)) = len) by (rewrite firstn_length, skipn_length; lia).
  split; [|split; [exact LEN|]; repeat split; lia].
  rewrite <- (firstn_skipn (Z.to_nat k) src) in HB. apply bytes_at_app in HB as [_ HB].
  rewrite firstn_length, Nat.min_l in HB by lia. rewrite Z2Nat.id in HB by lia.
  rewrite <- (firstn_skipn (Z.to_nat len) (skipn (Z.to_nat k) src)) in HB. apply bytes_at_app in HB as [HB _]. exact HB.
Qed.

Lemma c1_dl_read : forall (dtb : list byte) tl rsv, nth_error dtb 2 = Some (Z_to_bv 8 tl) -> nth_error dtb 3 = Some (Z_to_bv 8 rsv) ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 ->
  extz false 2 (bytes_le_to_Z (firstn 2 (skipn (Z.to_nat 2) dtb))) = tl + 256 * rsv.
Proof.
  intros dtb tl rsv DT2 DT3 HTL HRSV.
  assert (E : firstn 2 (skipn (Z.to_nat 2) dtb) = [Z_to_bv 8 tl; Z_to_bv 8 rsv]).
  { change (Z.to_nat 2) with 2%nat.
    destruct dtb as [|y0 [|y1 [|y2 [|y3 r]]]]; cbn in DT2, DT3; try discriminate.
    injection DT2 as ->. injection DT3 as ->. reflexivity. }
  rewrite E. unfold extz. rewrite Bytes.bytes_le_to_Z_le_val. cbn [map Bytes.le_val].
  rewrite !Z_to_bv_unsigned, !bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 8) with 256; lia). lia.
Qed.

Section C1KIT.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.

  Notation EINVB := (RZ_huf_dx42_5.EINVB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation X42P := (RZ_huf_dx42_5.X42P ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).

  Lemma c1_einvb_chunks : forall mm (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 : word) csF cs4 cs3 cs2 cs1 csR,
    rw_cells usegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs mm lo (SPV + -912) ->
    rw_cells usegs mm (SPV + -912) csF -> cells_size csF = 136%nat ->
    rw_cells usegs mm (SPV + -776) cs4 -> cells_size cs4 = 40%nat ->
    rw_cells usegs mm (SPV + -736) cs3 -> cells_size cs3 = 40%nat ->
    rw_cells usegs mm (SPV + -696) cs2 -> cells_size cs2 = 40%nat ->
    rw_cells usegs mm (SPV + -656) cs1 -> cells_size cs1 = 40%nat ->
    rw_cells usegs mm (SPV + -616) [C8 u11; C8 u10; C8 u9; C8 u8; C8 u7; C8 u6; C8 u5; C8 u4; C8 u3; C8 u2; C8 u1; C8 u0;
                                    C8 (Z_to_bv 64 0x22090)] ->
    rw_cells usegs mm (SPV + -512) csR -> cells_size csR = 408%nat ->
    munch [(DST, DST + dcap); (SPV - 912, SPV)] m0 mm -> wmono usegs m0 mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) ->
    EINVB mm.
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 csF cs4 cs3 cs2 cs1 csR SV STK FA SF B4 S4 B3 S3 B2 S2 B1 S1 SA RS SR MU WM MI OUT.
    pose proof (stk_of_rw_cells usegs mm _ _ FA) as H1.
    pose proof (stk_of_rw_cells usegs mm _ _ B4) as H2.
    pose proof (stk_of_rw_cells usegs mm _ _ B3) as H3.
    pose proof (stk_of_rw_cells usegs mm _ _ B2) as H4.
    pose proof (stk_of_rw_cells usegs mm _ _ B1) as H5.
    pose proof (stk_of_rw_cells usegs mm _ _ RS) as H6.
    rewrite SF in H1. rewrite S4 in H2. rewrite S3 in H3. rewrite S2 in H4. rewrite S1 in H5. rewrite SR in H6.
    change (Z.of_nat 136) with 136 in H1. change (Z.of_nat 40) with 40 in H2, H3, H4, H5. change (Z.of_nat 408) with 408 in H6.
    replace (SPV + -912 + 136) with (SPV + -776) in H1 by lia.
    replace (SPV + -776 + 40) with (SPV + -736) in H2 by lia.
    replace (SPV + -736 + 40) with (SPV + -696) in H3 by lia.
    replace (SPV + -696 + 40) with (SPV + -656) in H4 by lia.
    replace (SPV + -656 + 40) with (SPV + -616) in H5 by lia.
    replace (SPV + -512 + 408) with (SPV + -104) in H6 by lia.
    unfold RZ_huf_dx42_5.EINVB. split; [exact OUT|]. split; [exact SV|]. split; [do 12 eexists; exact SA|].
    split; [|split; [exact H6|split; [exact MU|split; [exact WM|exact MI]]]].
    eapply (stk_merge usegs mm lo (SPV + -656)); [|exact H5|lia].
    eapply (stk_merge usegs mm lo (SPV + -696)); [|exact H4|lia].
    eapply (stk_merge usegs mm lo (SPV + -736)); [|exact H3|lia].
    eapply (stk_merge usegs mm lo (SPV + -776)); [|exact H2|lia].
    eapply (stk_merge usegs mm lo (SPV + -912)); [exact STK|exact H1|lia].
  Qed.

  Lemma c1_einvb_x42p : forall mm rest csF cs4 cs3 cs2 cs1,
    X42P mm rest -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) ->
    rw_cells usegs mm (SPV + -912) csF -> cells_size csF = 136%nat ->
    rw_cells usegs mm (SPV + -776) cs4 -> cells_size cs4 = 40%nat ->
    rw_cells usegs mm (SPV + -736) cs3 -> cells_size cs3 = 40%nat ->
    rw_cells usegs mm (SPV + -696) cs2 -> cells_size cs2 = 40%nat ->
    rw_cells usegs mm (SPV + -656) cs1 -> cells_size cs1 = 40%nat ->
    EINVB mm.
  Proof.
    intros mm rest csF cs4 cs3 cs2 cs1
      (SV & STK & (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & SA) & RS & MU & WM & AL)
      MI OUT FA SF B4 S4 B3 S3 B2 S2 B1 S1.
    exact (c1_einvb_chunks mm u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 csF cs4 cs3 cs2 cs1 [CB 408 rest]
             SV STK FA SF B4 S4 B3 S3 B2 S2 B1 S1 SA RS eq_refl MU WM MI OUT).
  Qed.

End C1KIT.
