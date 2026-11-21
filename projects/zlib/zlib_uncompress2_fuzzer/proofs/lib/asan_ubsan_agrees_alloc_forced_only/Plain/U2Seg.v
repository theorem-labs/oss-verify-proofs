(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* (tier 1, unc2 asan, 1.4): the plain uncompress2 segments at 1.4, ported from a worker w2 MrP7/S7U2Seg
   (a worker's 1.4 walk: frames LLVMFuzzerTestOneInput 32 at usp-32, uncompress2 48 at usp-80, uncompress2_z 160 at
   UU = usp-240, inflateInit_ 32 at usp-272) with this lineage's generalisation, as a worker's C33 port did for
   unc: usp = sp0 - 208, the caller's ra and s0 .. s5 as variables, F / fc for the fp state. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import base decidable list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only Require PropExec S7LibStmt.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Walk Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.CkP Require Import RegsFull BridgeKit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Plain Require Import PImg RMallocRep RMalloc_iface U2Kit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Plain Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Module OL := OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.S7LibStmt.

Lemma le8_lit : forall z, 0 <= z < 2^64 -> le8 (Z_to_bv 64 z) = Z_to_le_bytes 8 z.
Proof. intros z Hz. unfold le8, word_to_le_bytes. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma ovr_of_rdn_Z : forall (M : word -> option byte) a a' z,
  OP.rdn psegs M (Z_to_bv 64 a) 8 = Some (Z_to_le_bytes 8 z) -> 0 <= z < 2^64 -> a = a' ->
  ov_read_bytes psegs M (Z_to_bv 64 a') 8 = Some (le8 (Z_to_bv 64 z)).
Proof. intros M a a' z H Hz <-. rewrite ov_rdn, le8_lit by lia. exact H. Qed.

Lemma ovr_of_rdn_w : forall (M : word -> option byte) a a' (v : word),
  OP.rdn psegs M (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 v) -> a = a' ->
  ov_read_bytes psegs M (Z_to_bv 64 a') 8 = Some (le8 v).
Proof. intros M a a' v H <-. rewrite ov_rdn. exact H. Qed.

Ltac cell_fact H k :=
  lazymatch goal with |- OP.rdn _ ?m (Z_to_bv 64 ?E) ?n = Some _ =>
    lazymatch type of H with rw_cells ?segs m ?A ?cs =>
      let c := eval_cell_at cs k in
      lazymatch c with Some ?c0 =>
        let X := fresh "X" in
        pose proof (rw_cells_read_at segs m A cs k c0 n (wa (A + Z.of_nat k)) H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) ltac:(reflexivity)) as X;
        rewrite ov_rdn in X; cbv beta iota delta [cbytes] in X;
        replace E with (A + Z.of_nat k) by (cbn; lia);
        first [ exact X | rewrite le8_lit in X by lia; first [ exact X | replace_val X ] ]
      end end end
with replace_val X :=
  lazymatch type of X with _ = Some (Z_to_le_bytes _ ?z) =>
    lazymatch goal with |- _ = Some (Z_to_le_bytes _ ?z') => replace z' with z by lia; exact X end end.

Ltac br_false := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    let C := fresh "C" in assert (C : c = false);
    [ unfold bv_eqb; rewrite !unsigned_lit by lia; first [apply Z.eqb_neq; lia | apply negb_false_iff, Z.eqb_eq; lia] | rewrite C; cbv iota; clear C ] end.
Ltac br_true := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    let C := fresh "C" in assert (C : c = true);
    [ unfold bv_eqb; rewrite !unsigned_lit by lia; first [apply Z.eqb_eq; lia | apply negb_true_iff, Z.eqb_neq; lia] | rewrite C; cbv iota; clear C ] end.

Section SEG.
Context {rc : runConstT}.
Variable usp : Z.
Hypothesis USP : 0x7fff7f800000 <= usp < 2^64.

Abbreviation UU := (usp - 240).

(* the return point in LLVMFuzzerTestOneInput after `jal uncompress2` (1.4: 0x14d34 + 4) *)
Definition S7_UNC_RA : Z := 0x14d98.
(* 1.4: LLVMFuzzerTestOneInput saves its caller's ra (UU+232 = usp-8); uncompress2 saves ra (UU+200), its caller's s0
   (v0, UU+192) and s1 (v1, UU+184); uncompress2_z saves ra and s0 .. s4 at UU+152 .. UU+112, where its s0 / s1 are
   uncompress2's &sourceLen / &destLen (usp-24 / usp-16, in LLVMFuzzerTestOneInput's frame) and s2 .. s4 are the
   caller's s2 .. s4.  v5 is kept, unused, so the arity is the 1.3.1 one. *)
Record u2_frames (M : word -> option byte) (ra v0 v1 v2 v3 v4 v5 : word) : Prop := U2_FRAMES {
  uf_hra : OP.rdn psegs M (Z_to_bv 64 (UU + 232)) 8 = Some (word_to_le_bytes 8 ra);
  uf_wra : OP.rdn psegs M (Z_to_bv 64 (UU + 200)) 8 = Some (Z_to_le_bytes 8 S7_UNC_RA);
  uf_us0 : OP.rdn psegs M (Z_to_bv 64 (UU + 192)) 8 = Some (word_to_le_bytes 8 v0);
  uf_us1 : OP.rdn psegs M (Z_to_bv 64 (UU + 184)) 8 = Some (word_to_le_bytes 8 v1);
  uf_ura : OP.rdn psegs M (Z_to_bv 64 (UU + 152)) 8 = Some (Z_to_le_bytes 8 OL.S7_HARN_RA);
  uf_s0  : OP.rdn psegs M (Z_to_bv 64 (UU + 144)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (usp - 24)));
  uf_s1  : OP.rdn psegs M (Z_to_bv 64 (UU + 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (usp - 16)));
  uf_s2  : OP.rdn psegs M (Z_to_bv 64 (UU + 128)) 8 = Some (word_to_le_bytes 8 v2);
  uf_s3  : OP.rdn psegs M (Z_to_bv 64 (UU + 120)) 8 = Some (word_to_le_bytes 8 v3);
  uf_s4  : OP.rdn psegs M (Z_to_bv 64 (UU + 112)) 8 = Some (word_to_le_bytes 8 v4)
}.

(* 1.4: inflateInit_'s saved cells (its frame is UU-32 .. UU) and the z_stream fields uncompress2_z set (z_stream at UU). *)
Record u2_za_cells (M : word -> option byte) (q : Z) : Prop := U2_ZA_CELLS {
  uz_s2 : OP.rdn psegs M (Z_to_bv 64 (UU - 32)) 8 = Some (Z_to_le_bytes 8 OL.S7_BUF);
  uz_s1 : OP.rdn psegs M (Z_to_bv 64 (UU - 24)) 8 = Some (Z_to_le_bytes 8 (UU + 168));
  uz_s0 : OP.rdn psegs M (Z_to_bv 64 (UU - 16)) 8 = Some (Z_to_le_bytes 8 (UU + 176));
  uz_ra : OP.rdn psegs M (Z_to_bv 64 (UU - 8)) 8 = Some (Z_to_le_bytes 8 OL.S7_RA_II);
  uz_in : OP.rdn psegs M (Z_to_bv 64 (UU)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 q));
  uz_av : OP.rdn psegs M (Z_to_bv 64 (UU + 8)) 4 = Some (Z_to_le_bytes 4 0);
  uz_za : OP.rdn psegs M (Z_to_bv 64 (UU + 64)) 8 = Some (Z_to_le_bytes 8 OL.S7_ZCALLOC);
  uz_zf : OP.rdn psegs M (Z_to_bv 64 (UU + 72)) 8 = Some (Z_to_le_bytes 8 OL.S7_ZCFREE);
  uz_op : OP.rdn psegs M (Z_to_bv 64 (UU + 80)) 8 = Some (Z_to_le_bytes 8 0)
}.

(* 1.4: LLVMFuzzerTestOneInput -> uncompress2 -> uncompress2_z -> inflateInit_ -> zcalloc -> malloc's entry, with
   ra = 0x1510c (inflateInit_ after the zalloc call). No GOT premise at 1.4: inflateInit_ forms zcalloc / zcfree with
   auipc + addi. *)
Lemma u2_seg1_evt : forall (Q : machine_state -> Prop) (q payl lo : Z) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (x1 x3 x4 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  lo <= usp - 16384 -> 0 <= lo -> 0 <= payl < 2^26 -> 0 <= q < 2^64 -> 1 <= q ->
  stk psegs M lo usp -> mem_inv psegs M ->
  (forall (M1 : word -> option byte),
     munch [(usp - 272, usp)] M M1 -> wmono psegs M M1 -> mem_inv psegs M1 ->
     u2_frames M1 x1 x8 x9 x18 x19 x20 x21 -> u2_za_cells M1 q ->
     Q (MS (mkR (Z_to_bv 64 0x1516c) (Z_to_bv 64 (usp - 272)) x3 x4 x5 x6 x7 (Z_to_bv 64 (usp - 64)) (Z_to_bv 64 (usp - 240))
                (Z_to_bv 64 7176) (Z_to_bv 64 1) (Z_to_bv 64 7176) (Z_to_bv 64 0x17218) (Z_to_bv 64 112) x15 x16 x17
                (Z_to_bv 64 0x32eb0) (Z_to_bv 64 payl) (Z_to_bv 64 0x40000) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x1941c) fc None M1 (seg_rom psegs))) ->
  evt psegs Q (MS (mkR x1 (Z_to_bv 64 usp) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 q) (Z_to_bv 64 payl) x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x14d6c) fc None M (seg_rom psegs)).
Proof.
  intros Q q payl lo M F fc x1 x3 x4 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         LO LO0 PAYL QR Q1 ST MI HK.
  pose proof (munch_refl [(usp - 272, usp)] M) as MU.
  pose proof (wmono_refl psegs M) as WM.
  (* LLVMFuzzerTestOneInput: frame 32; buffer_length = 0x40000 at sp+16, size at sp+8; jal uncompress2 *)
  step. carve_frame 32%nat ST.
  do 10 step.
  (* uncompress2 (1.4): frame 48; ra, s0, s1; s0 = &sourceLen, s1 = &destLen; the copies at sp+16 (destLen) and
     sp+8 (sourceLen); jal uncompress2_z *)
  step. carve_frame 48%nat ST.
  replace (usp + -32 + -48) with (usp + -80) in * by lia.
  do 12 step.
  (* uncompress2_z: frame 160; the argument checks *)
  step. carve_frame 160%nat ST.
  replace (usp + -80 + -160) with (usp + -240) in * by lia.
  do 9 step. br_false.                (* 6 sd; mv s2,a0; li a0,-2; beqz a3 (&sourceLen) *)
  do 2 step. br_false.                (* mv s0,a1; beqz a1 (&destLen) *)
  do 6 step.                          (* mv s1,a3; ld s3; snez; seqz; and; bnez a1 *)
  (* the (sourceLen > 0 && source == NULL) test is false: source = q >= 1 *)
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    let C := fresh "C" in assert (C : c = false);
    [ rewrite v_sltiu_b2z; rewrite (unsigned_lit q) by lia;
      replace (bv_wrap 64 1) with 1 by reflexivity;
      replace (q <? 1) with false by (symmetry; apply Z.ltb_ge; lia);
      cbn [Z.b2z]; rewrite (unsigned_lit 0) by lia; rewrite Z.land_0_l;
      unfold bv_eqb; rewrite (unsigned_lit 0) by lia; reflexivity
    | rewrite C; cbv iota; clear C ] end.
  do 2 step. if_true.                 (* ld s4,0(s0); bnez s2 (dest) *)
  do 10 step.                         (* the z_stream fields; jal inflateInit_ *)
  (* inflateInit_: version and size checks; zalloc / zfree default to zcalloc / zcfree *)
  do 2 step. if_false. do 2 step. if_false. do 3 step. if_false. step. br_false.
  do 3 step. if_true.                 (* ld a3,64(a0); sd zero,48(a0); beqz a3 *)
  do 6 step. if_false.                (* auipc; addi; sd a3,64; sd zero,80; ld a1,72; bnez a1 *)
  do 4 step.                          (* auipc; addi; sd a1,72; j *)
  step. carve_frame 32%nat ST.
  replace (usp + -240 + -32) with (usp + -272) in * by lia.
  do 10 step.                         (* 4 sd; mv s1,a0; ld a0,80(a0); lui; addiw; li; jalr a3 *)
  do 4 step.                          (* zcalloc: mul; slli; srli; j malloc *)
  apply evt_done.
  lazymatch goal with |- Q (MS _ _ _ _ _ ?mx _) => apply (HK mx) end.
  - exact MU.
  - exact WM.
  - exact MI.
  - constructor; unfold OL.S7_HARN_RA, S7_UNC_RA.
    + cell_fact FR 24%nat.
    + cell_fact FR0 40%nat.
    + cell_fact FR0 32%nat.
    + cell_fact FR0 24%nat.
    + cell_fact FR1 152%nat.
    + cell_fact FR1 144%nat.
    + cell_fact FR1 136%nat.
    + cell_fact FR1 128%nat.
    + cell_fact FR1 120%nat.
    + cell_fact FR1 112%nat.
  - constructor; unfold OL.S7_BUF, OL.S7_RA_II, OL.S7_ZCALLOC, OL.S7_ZCFREE.
    + cell_fact FR2 0%nat.
    + cell_fact FR2 8%nat.
    + cell_fact FR2 16%nat.
    + cell_fact FR2 24%nat.
    + cell_fact FR1 0%nat.
    + cell_fact FR1 8%nat.
    + cell_fact FR1 64%nat.
    + cell_fact FR1 72%nat.
    + cell_fact FR1 80%nat.
Qed.

(* 1.4: from uncompress2's return point (0x14f04, after jal uncompress2_z) back to the fuzzer's caller (ra).
   uncompress2 writes *sourceLen and *destLen (LLVMFuzzerTestOneInput's cells at usp-24 and usp-16) from its copies,
   restores s0 / s1 (v0 / v1) and returns; then LLVMFuzzerTestOneInput's tail.  Its two frames are given as rw_cells
   (a load after the store needs cells the step transports). *)
Lemma u2_seg_ret_evt : forall (Q : machine_state -> Prop) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (w0 sl dl b0 bsl bdl ra v0 v1 : word)
    (x1 x3 x4 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  rw_cells psegs M (usp - 80) [C8 w0; C8 sl; C8 dl; C8 v1; C8 v0; C8 (Z_to_bv 64 S7_UNC_RA)] ->
  rw_cells psegs M (usp - 32) [C8 b0; C8 bsl; C8 bdl; C8 ra] ->
  (forall M1 : word -> option byte,
     munch [(usp - 24, usp - 8)] M M1 -> wmono psegs M M1 ->
     Q (MS (mkR ra (Z_to_bv 64 usp) x3 x4 x5 x6 x7 v0 v1 (Z_to_bv 64 0) sl dl x13 x14 x15 x16 x17
                x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (ret_pc ra) fc None M1 (seg_rom psegs))) ->
  evt psegs Q (MS (mkR x1 (Z_to_bv 64 (usp - 80)) x3 x4 x5 x6 x7 (Z_to_bv 64 (usp - 24)) (Z_to_bv 64 (usp - 16)) x10 x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x14f64) fc None M (seg_rom psegs)).
Proof.
  intros Q M F fc w0 sl dl b0 bsl bdl ra v0 v1 x1 x3 x4 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         FR0 FR HK.
  pose proof (munch_refl [(usp - 24, usp - 8)] M) as MU.
  pose proof (wmono_refl psegs M) as WM.
  unfold S7_UNC_RA in *.
  (* the two stores go through s0 / s1 into LLVMFuzzerTestOneInput's cells; the step finds a store's cell by its
     offset from the frame base (usp - 32), so the addresses are written as base + offset *)
  replace (Z_to_bv 64 (usp - 24)) with (Z_to_bv 64 (usp - 32 + 8)) by (f_equal; lia).
  replace (Z_to_bv 64 (usp - 16)) with (Z_to_bv 64 (usp - 32 + 16)) by (f_equal; lia).
  (* uncompress2's tail: ld a1,8(sp); ld a2,16(sp); sd a1,0(s0); sd a2,0(s1); ld ra,40(sp); ld s0,32(sp); ld s1,24(sp);
     addi sp,sp,48; ret *)
  do 9 step.
  (* LLVMFuzzerTestOneInput's tail: li a0,0; ld ra,24(sp); addi sp,sp,32; ret *)
  replace (usp - 80 + 48) with (usp - 32) in * by lia. do 4 step. apply evt_done.
  replace (usp - 32 + 32) with usp by lia.
  apply HK; assumption.
Qed.

(* 1.4: zalloc returned NULL. inflateInit_ (from 0x1510c) returns Z_MEM_ERROR, and uncompress2_z returns it at once
   to uncompress2 (0x14f04, S7_HARN_RA), restoring s0 (= usp-24), s1 (= usp-16) and s2 .. s4 (v2 .. v4). *)
Lemma u2_seg_null_evt : forall (Q : machine_state -> Prop) (q : Z) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32) (ra v0 v1 v2 v3 v4 v5 : word)
    (x1 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  u2_frames M ra v0 v1 v2 v3 v4 v5 -> u2_za_cells M q ->
  (forall y10 y13 : word,
     Q (MS (mkR (Z_to_bv 64 OL.S7_HARN_RA) (Z_to_bv 64 (usp - 80)) x3 x4 x5 x6 x7 (Z_to_bv 64 (usp - 24)) (Z_to_bv 64 (usp - 16)) y10 x11 x12 y13 x14 x15 x16 x17
                v2 v3 v4 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 OL.S7_HARN_RA) fc None M (seg_rom psegs))) ->
  evt psegs Q (MS (mkR x1 (Z_to_bv 64 (usp - 272)) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x1516c) fc None M (seg_rom psegs)).
Proof.
  intros Q q M F fc ra v0 v1 v2 v3 v4 v5 x1 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         [F_hra F_wra F_us0 F_us1 F_ura F_s0 F_s1 F_s2 F_s3 F_s4] [Z_s2 Z_s1 Z_s0 Z_ra _ _ _ _ _] HK.
  unfold OL.S7_HARN_RA, OL.S7_BUF, OL.S7_RA_II in *.
  (* inflateInit_'s frame (usp-272): s2, s1, s0, ra *)
  pose proof (ovr_of_rdn_Z M _ (usp - 272 + 24) _ Z_ra ltac:(lia) ltac:(lia)) as HR1.
  pose proof (ovr_of_rdn_Z M _ (usp - 272 + 16) _ Z_s0 ltac:(lia) ltac:(lia)) as HR2.
  pose proof (ovr_of_rdn_Z M _ (usp - 272 + 8) _ Z_s1 ltac:(lia) ltac:(lia)) as HR3.
  pose proof (ovr_of_rdn_Z M _ (usp - 272 + 0) _ Z_s2 ltac:(lia) ltac:(lia)) as HR4.
  (* uncompress2_z's frame (usp-240): ra, s0 .. s4 *)
  pose proof (ovr_of_rdn_Z M _ (usp - 240 + 152) _ F_ura ltac:(lia) ltac:(lia)) as HR5.
  pose proof (ovr_of_rdn_w M _ (usp - 240 + 144) _ F_s0 ltac:(lia)) as HR6.
  pose proof (ovr_of_rdn_w M _ (usp - 240 + 136) _ F_s1 ltac:(lia)) as HR7.
  pose proof (ovr_of_rdn_w M _ (usp - 240 + 128) _ F_s2 ltac:(lia)) as HR8.
  pose proof (ovr_of_rdn_w M _ (usp - 240 + 120) _ F_s3 ltac:(lia)) as HR9.
  pose proof (ovr_of_rdn_w M _ (usp - 240 + 112) _ F_s4 ltac:(lia)) as HR10.
  (* inflateInit_: beqz a0 (taken); li a3,-4; j; the epilogue (4 ld, addi, mv a0,a3, ret) *)
  step. if_true. do 2 step. do 7 step.
  replace (usp - 272 + 32) with (usp - 240) in * by lia.
  (* uncompress2_z at 0x14dc4: bnez a0 (taken); the epilogue (6 ld, addi, ret) *)
  step. if_true. do 8 step.
  apply evt_done.
  replace (usp - 240 + 160) with (usp - 80) by lia.
  apply HK.
Qed.

Lemma u2_seg_zw_evt : forall (Q : machine_state -> Prop) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  Q (MS (mkR (Z_to_bv 64 0x17070) x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 32768) (Z_to_bv 64 32768) (Z_to_bv 64 1) (Z_to_bv 64 0x17218) x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x1941c) fc None M (seg_rom psegs)) ->
  evt psegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 0) (Z_to_bv 64 32768) (Z_to_bv 64 1) (Z_to_bv 64 0x17218) x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x1706c) fc None M (seg_rom psegs)).
Proof.
  intros Q M F fc x1 x2 x3 x4 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 HK.
  do 5 step. apply evt_done. exact HK.
Qed.

Lemma u2_seg_ze1_evt : forall (Q : machine_state -> Prop) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32) (blk : word)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x12 x13 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  Q (MS (mkR (Z_to_bv 64 0x171e8) x2 x3 x4 x5 x6 x7 x8 x9 blk blk x12 x13 (Z_to_bv 64 0x17228) x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x192dc) fc None M (seg_rom psegs)) ->
  evt psegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 blk x12 x13 (Z_to_bv 64 0x17228) x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x171e4) fc None M (seg_rom psegs)).
Proof.
  intros Q M F fc blk x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x12 x13 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 HK.
  do 3 step. apply evt_done. exact HK.
Qed.

Lemma u2_seg_ze2_evt : forall (Q : machine_state -> Prop) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32) (blk : word)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x12 x13 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  Q (MS (mkR (Z_to_bv 64 0x17200) x2 x3 x4 x5 x6 x7 x8 x9 blk blk x12 x13 (Z_to_bv 64 0x17228) x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x192dc) fc None M (seg_rom psegs)) ->
  evt psegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 blk x12 x13 (Z_to_bv 64 0x17228) x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x171fc) fc None M (seg_rom psegs)).
Proof.
  intros Q M F fc blk x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x12 x13 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 HK.
  do 3 step. apply evt_done. exact HK.
Qed.

(* 1.4: the z_stream is at UU (1.3.1: UU + 8). *)
Lemma u2_seg_ze1b_evt : forall (Q : machine_state -> Prop) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32) (p : Z)
    (x1 x2 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  OL.end_cells_S7 M UU p -> 0 <= p < 2^64 ->
  Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 (UU)) x9 (Z_to_bv 64 0) (Z_to_bv 64 p) (Z_to_bv 64 (UU)) x13 (Z_to_bv 64 0x17228) x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x171fc) fc None M (seg_rom psegs)) ->
  evt psegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 (UU)) x9 x10 x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x171e8) fc None M (seg_rom psegs)).
Proof.
  intros Q M F fc p x1 x2 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         (_ & E_st & E_zf & E_op) PR HK.
  unfold OL.S7_ZCFREE in *.
  pose proof (ovr_of_rdn_Z M _ (UU + 56) _ E_st ltac:(lia) ltac:(lia)) as HR1.
  pose proof (ovr_of_rdn_Z M _ (UU + 72) _ E_zf ltac:(lia) ltac:(lia)) as HR2.
  pose proof (ovr_of_rdn_Z M _ (UU + 80) _ E_op ltac:(lia) ltac:(lia)) as HR3.
  do 5 step. apply evt_done. exact HK.
Qed.

End SEG.
