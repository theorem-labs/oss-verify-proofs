(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import base decidable list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only Require PropExec S8LibStmt.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Walk Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.CkP Require Import RegsFull BridgeKit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Plain Require Import PImg RMallocRep RMalloc_iface U2Kit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Plain Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Module OL := OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.S8LibStmt.

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

(* the return point in LLVMFuzzerTestOneInput after `jal uncompress2` (1.4: 0x14d8c + 4) *)
Definition S8_UNC_RA : Z := 0x14df0.
(* 1.4: LLVMFuzzerTestOneInput saves its caller's ra (UU+232 = usp-8); uncompress2 saves ra (UU+200), its caller's s0
   (v0, UU+192) and s1 (v1, UU+184); uncompress2_z saves ra and s0 .. s4 at UU+152 .. UU+112, where its s0 / s1 are
   uncompress2's &sourceLen / &destLen (usp-24 / usp-16, in LLVMFuzzerTestOneInput's frame) and s2 .. s4 are the
   caller's s2 .. s4.  v5 is kept, unused, so the arity is the 1.3.1 one. *)
Record u2_frames (M : word -> option byte) (ra v0 v1 v2 v3 v4 v5 : word) : Prop := U2_FRAMES {
  uf_hra : OP.rdn psegs M (Z_to_bv 64 (UU + 232)) 8 = Some (word_to_le_bytes 8 ra);
  uf_wra : OP.rdn psegs M (Z_to_bv 64 (UU + 200)) 8 = Some (Z_to_le_bytes 8 S8_UNC_RA);
  uf_us0 : OP.rdn psegs M (Z_to_bv 64 (UU + 192)) 8 = Some (word_to_le_bytes 8 v0);
  uf_us1 : OP.rdn psegs M (Z_to_bv 64 (UU + 184)) 8 = Some (word_to_le_bytes 8 v1);
  uf_ura : OP.rdn psegs M (Z_to_bv 64 (UU + 152)) 8 = Some (Z_to_le_bytes 8 OL.S8_HARN_RA);
  uf_s0  : OP.rdn psegs M (Z_to_bv 64 (UU + 144)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (usp - 24)));
  uf_s1  : OP.rdn psegs M (Z_to_bv 64 (UU + 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (usp - 16)));
  uf_s2  : OP.rdn psegs M (Z_to_bv 64 (UU + 128)) 8 = Some (word_to_le_bytes 8 v2);
  uf_s3  : OP.rdn psegs M (Z_to_bv 64 (UU + 120)) 8 = Some (word_to_le_bytes 8 v3);
  uf_s4  : OP.rdn psegs M (Z_to_bv 64 (UU + 112)) 8 = Some (word_to_le_bytes 8 v4)
}.

(* 1.4: inflateInit_'s saved cells (its frame is UU-32 .. UU) and the z_stream fields uncompress2_z set (z_stream at UU).
   qc = the source pointer the harness passes (q + k); s2 = dest = OL.za_dest_S8 zm UU (the harness buffer). *)
Record u2_za_cells (M : word -> option byte) (zm : bool) (qc : Z) : Prop := U2_ZA_CELLS {
  uz_s2 : OP.rdn psegs M (Z_to_bv 64 (UU - 32)) 8 = Some (Z_to_le_bytes 8 (OL.za_dest_S8 zm UU));
  uz_s1 : OP.rdn psegs M (Z_to_bv 64 (UU - 24)) 8 = Some (Z_to_le_bytes 8 (UU + 168));
  uz_s0 : OP.rdn psegs M (Z_to_bv 64 (UU - 16)) 8 = Some (Z_to_le_bytes 8 (UU + 176));
  uz_ra : OP.rdn psegs M (Z_to_bv 64 (UU - 8)) 8 = Some (Z_to_le_bytes 8 OL.S8_RA_II);
  uz_in : OP.rdn psegs M (Z_to_bv 64 (UU)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 qc));
  uz_av : OP.rdn psegs M (Z_to_bv 64 (UU + 8)) 4 = Some (Z_to_le_bytes 4 0);
  uz_za : OP.rdn psegs M (Z_to_bv 64 (UU + 64)) 8 = Some (Z_to_le_bytes 8 OL.S8_ZCALLOC);
  uz_zf : OP.rdn psegs M (Z_to_bv 64 (UU + 72)) 8 = Some (Z_to_le_bytes 8 OL.S8_ZCFREE);
  uz_op : OP.rdn psegs M (Z_to_bv 64 (UU + 80)) 8 = Some (Z_to_le_bytes 8 0)
}.

(* 1.4: from LLVMFuzzerTestOneInput's frame allocation (0x14d6c, after the prefix computed L = destLen, n' = sourceLen
   and qc = the source) -> uncompress2 -> uncompress2_z -> inflateInit_ -> zcalloc -> malloc's entry, with
   ra = 0x15174 (inflateInit_ after the zalloc call).  zm = (L =? 0).  No GOT premise at 1.4: inflateInit_ forms
   zcalloc / zcfree with auipc + addi. *)
Lemma u2_seg1_core : forall (Q : machine_state -> Prop) (lo L n' qc : Z) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (x1 x3 x4 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  lo <= usp - 16384 -> 0 <= lo -> 0 <= L <= 0x40000 -> 0 <= n' < 2^64 -> 1 <= qc < 2^64 ->
  stk psegs M lo usp -> mem_inv psegs M ->
  (forall (M1 : word -> option byte) (zm : bool),
     munch [(usp - 272, usp)] M M1 -> wmono psegs M M1 -> mem_inv psegs M1 ->
     u2_frames M1 x1 x8 x9 x18 x19 x20 x21 -> u2_za_cells M1 zm qc -> OL.za_left_S8 zm L ->
     Q (MS (mkR (Z_to_bv 64 0x151d4) (Z_to_bv 64 (usp - 272)) x3 x4 x5 x6 x7 (Z_to_bv 64 (usp - 64)) (Z_to_bv 64 (usp - 240))
                (Z_to_bv 64 7176) (Z_to_bv 64 1) (Z_to_bv 64 7176) (Z_to_bv 64 0x17280) (Z_to_bv 64 112) x15 x16 x17
                (Z_to_bv 64 OL.S8_BUF) (Z_to_bv 64 n') (Z_to_bv 64 L) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x19484) fc None M1 (seg_rom psegs))) ->
  evt psegs Q (MS (mkR x1 (Z_to_bv 64 usp) x3 x4 x5 x6 x7 x8 x9
                       (Z_to_bv 64 L) (Z_to_bv 64 n') (Z_to_bv 64 qc) x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x14dcc) fc None M (seg_rom psegs)).
Proof.
  intros Q lo L n' qc M F fc x1 x3 x4 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         LO LO0 HL HN HQC ST MI HK.
  pose proof (munch_refl [(usp - 272, usp)] M) as MU.
  pose proof (wmono_refl psegs M) as WM.
  (* LLVMFuzzerTestOneInput: frame 32; destLen = L at sp+16, sourceLen = n' at sp+8; jal uncompress2 *)
  step. carve_frame 32%nat ST.
  do 8 step.
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
  (* the (sourceLen > 0 && source == NULL) test is false: source = qc >= 1 *)
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    let C := fresh "C" in assert (C : c = false);
    [ rewrite v_sltiu_b2z; rewrite (unsigned_lit qc) by lia;
      replace (bv_wrap 64 1) with 1 by reflexivity;
      replace (qc <? 1) with false by (symmetry; apply Z.ltb_ge; lia);
      cbn [Z.b2z]; rewrite (unsigned_lit 0) by lia; rewrite Z.land_0_l;
      unfold bv_eqb; rewrite (unsigned_lit 0) by lia; reflexivity
    | rewrite C; cbv iota; clear C ] end.
  do 2 step. if_true.                 (* ld s4,0(s0); bnez s2 (dest = the harness buffer) *)
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
  lazymatch goal with |- Q (MS _ _ _ _ _ ?mx _) => apply (HK mx (L =? 0)) end.
  - exact MU.
  - exact WM.
  - exact MI.
  - constructor; unfold OL.S8_HARN_RA, S8_UNC_RA.
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
  - constructor; unfold OL.za_dest_S8, OL.S8_BUF, OL.S8_RA_II, OL.S8_ZCALLOC, OL.S8_ZCFREE.
    + destruct (L =? 0); cell_fact FR2 0%nat.
    + cell_fact FR2 8%nat.
    + cell_fact FR2 16%nat.
    + cell_fact FR2 24%nat.
    + cell_fact FR1 0%nat.
    + cell_fact FR1 8%nat.
    + cell_fact FR1 64%nat.
    + cell_fact FR1 72%nat.
    + cell_fact FR1 80%nat.
  - unfold OL.za_left_S8, OL.S8_BUF_N. destruct (Z.eqb_spec L 0); lia.
Qed.

(* the harness prefix (unchanged from 1.3.1): destLen = the product of the first one to three input bytes (8 when
   the input is empty), capped at 0x40000; the source and sourceLen skip those bytes *)
Ltac br_ltu_true := lazymatch goal with |- evt _ _ (MS _ _ (if bv_ltu ?a ?b then _ else _) _ _ _ _) =>
    let C := fresh "C" in assert (C : bv_ltu a b = true);
    [ unfold bv_ltu; rewrite !unsigned_lit by (first [lia | nia]); apply Z.ltb_lt; first [lia | nia] | rewrite C; cbv iota; clear C ] end.
Ltac br_ltu_false := lazymatch goal with |- evt _ _ (MS _ _ (if bv_ltu ?a ?b then _ else _) _ _ _ _) =>
    let C := fresh "C" in assert (C : bv_ltu a b = false);
    [ unfold bv_ltu; rewrite !unsigned_lit by (first [lia | nia]); apply Z.ltb_ge; first [lia | nia] | rewrite C; cbv iota; clear C ] end.

Lemma zxb_unsigned : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof.
  intros b. pose proof (bv_unsigned_in_range _ b) as R. change (bv_modulus 8) with 256 in R.
  unfold zxb. apply unsigned_lit. lia.
Qed.

(* 1.4: from LLVMFuzzerTestOneInput's entry (0x14d14) to malloc's entry.  uncompress2_z does not save s5, so the
   caller's s5 (x21) is still there at the malloc call; x19 = sourceLen (payl - k), x20 = left (1.4's order). *)
Lemma u2_seg1_evt : forall (Q : machine_state -> Prop) (q payl lo : Z) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32) (src : list byte)
    (x1 x3 x4 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  lo <= usp - 16384 -> 0 <= lo -> 0 <= payl < 2^26 -> 1 <= q -> q + payl < 2^64 ->
  stk psegs M lo usp -> mem_inv psegs M ->
  bytes_at psegs M q src -> length src = Z.to_nat payl ->
  (forall (M1 : word -> option byte) (k left : Z) (zm : bool) (y5 y6 y7 y8 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 : word),
     munch [(usp - 272, usp)] M M1 -> wmono psegs M M1 -> mem_inv psegs M1 ->
     u2_frames M1 x1 x8 x9 x18 x19 x20 x21 -> u2_za_cells M1 zm (q + k) ->
     0 <= k <= 3 -> k <= payl -> OL.za_left_S8 zm left ->
     Q (MS (mkR (Z_to_bv 64 0x151d4) (Z_to_bv 64 (usp - 272)) x3 x4 y5 y6 y7 y8 (Z_to_bv 64 (usp - 240))
                (Z_to_bv 64 7176) y11 y12 y13 y14 y15 y16 y17
                y18 (Z_to_bv 64 (payl - k)) (Z_to_bv 64 left) x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
           F (Z_to_bv 64 RMALLOC_SYM) fc None M1 (seg_rom psegs))) ->
  evt psegs Q (MS (mkR x1 (Z_to_bv 64 usp) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 q) (Z_to_bv 64 payl) x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x14d74) fc None M (seg_rom psegs)).
Proof.
  intros Q q payl lo M F fc src x1 x3 x4 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         LO LO0 PAYL Q0 QP ST MI SRC LSRC HK.
  (* the shared tail: from the frame allocation with destLen L, sourceLen payl - k and source q + k *)
  assert (FIN : forall (k L : Z) (y13 y14 : word), 0 <= k <= 3 -> k <= payl -> 0 <= L <= 0x40000 ->
            evt psegs Q (MS (mkR x1 (Z_to_bv 64 usp) x3 x4 x5 x6 x7 x8 x9
                                 (Z_to_bv 64 L) (Z_to_bv 64 (payl - k)) (Z_to_bv 64 (q + k)) y13 y14 x15 x16 x17
                                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x14dcc) fc None M (seg_rom psegs))).
  { intros k L y13 y14 K3 KP HL.
    eapply (u2_seg1_core Q lo L (payl - k) (q + k) M F fc); try eassumption; try lia.
    intros M1 zm MU1 WM1 MI1 UF1 UZ1 ZL1.
    apply (HK M1 k L zm); assumption. }
  step. step.
  destruct (Z.eqb_spec payl 0) as [P0|P0].
  -
    subst payl. if_true. do 3 step. do 4 step. step. if_true.
    replace q with (q + 0) at 1 by lia. change (Z_to_bv 64 0) with (Z_to_bv 64 (0 - 0)) at 1.
    apply (FIN 0 8); lia.
  - br_false.
    destruct src as [|b0 src]; [cbn in LSRC; lia|].
    pose proof (bytes_at_read psegs M q (b0 :: src) 0 1%nat SRC ltac:(lia) ltac:(cbn; lia)) as HR0. cbn [firstn skipn Z.to_nat] in HR0.
    pose proof (bv_unsigned_in_range _ b0) as R0. change (bv_modulus 8) with 256 in R0.
    step. step. step.
    destruct (Z.eqb_spec payl 1) as [P1|P1].
    +
      subst payl. br_false. do 3 step. do 4 step. step.
      rewrite ?zxb_unsigned. rewrite (unsigned_lit (bv_unsigned b0 * 1)) by lia.
      br_ltu_true.
      replace (bv_unsigned b0 * 1 * 1) with (bv_unsigned b0) by lia.
      change (Z_to_bv 64 0) with (Z_to_bv 64 (1 - 1)).
      apply (FIN 1 (bv_unsigned b0)); lia.
    + br_true.
      destruct src as [|m0 src]; [cbn in LSRC; lia|].
      pose proof (bytes_at_read psegs M q (b0 :: m0 :: src) 1 1%nat SRC ltac:(lia) ltac:(cbn; lia)) as HR1. cbn [firstn skipn Z.to_nat] in HR1.
      pose proof (bv_unsigned_in_range _ m0) as R1. change (bv_modulus 8) with 256 in R1.
      step. step. step.
      destruct (Z.eqb_spec payl 2) as [P2|P2].
      *
        subst payl. br_false. do 2 step. do 4 step. step.
        rewrite ?zxb_unsigned. rewrite (unsigned_lit (bv_unsigned b0 * bv_unsigned m0)) by nia.
        br_ltu_true.
        replace (bv_unsigned b0 * bv_unsigned m0 * 1) with (bv_unsigned b0 * bv_unsigned m0) by lia.
        change (Z_to_bv 64 0) with (Z_to_bv 64 (2 - 2)).
        apply (FIN 2 (bv_unsigned b0 * bv_unsigned m0)); nia.
      *
        br_true.
        destruct src as [|m1 src]; [cbn in LSRC; lia|].
        pose proof (bytes_at_read psegs M q (b0 :: m0 :: m1 :: src) 2 1%nat SRC ltac:(lia) ltac:(cbn; lia)) as HR2. cbn [firstn skipn Z.to_nat] in HR2.
        pose proof (bv_unsigned_in_range _ m1) as R2. change (bv_modulus 8) with 256 in R2.
        do 4 step. do 4 step.
        rewrite ?zxb_unsigned. rewrite (unsigned_lit (bv_unsigned b0 * bv_unsigned m0)) by nia.
        assert (PB2 : 0 <= bv_unsigned b0 * bv_unsigned m0 <= 65025) by nia.
        assert (PB3 : 0 <= bv_unsigned b0 * bv_unsigned m0 * bv_unsigned m1 <= 16581375) by nia.
        destruct (Z.ltb_spec (bv_unsigned b0 * bv_unsigned m0 * bv_unsigned m1) 0x40000) as [LT|GE].
        -- br_ltu_true.
           apply (FIN 3 (bv_unsigned b0 * bv_unsigned m0 * bv_unsigned m1)); nia.
        -- br_ltu_false. step.
           apply (FIN 3 0x40000); lia.
Qed.

(* 1.4: from uncompress2's return point (0x14f6c, after jal uncompress2_z) back to the fuzzer's caller (ra).
   uncompress2 writes *sourceLen and *destLen (LLVMFuzzerTestOneInput's cells at usp-24 and usp-16) from its copies,
   restores s0 / s1 (v0 / v1) and returns; then LLVMFuzzerTestOneInput's tail.  Its two frames are given as rw_cells
   (a load after the store needs cells the step transports). *)
Lemma u2_seg_ret_evt : forall (Q : machine_state -> Prop) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (w0 sl dl b0 bsl bdl ra v0 v1 : word)
    (x1 x3 x4 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  rw_cells psegs M (usp - 80) [C8 w0; C8 sl; C8 dl; C8 v1; C8 v0; C8 (Z_to_bv 64 S8_UNC_RA)] ->
  rw_cells psegs M (usp - 32) [C8 b0; C8 bsl; C8 bdl; C8 ra] ->
  (forall M1 : word -> option byte,
     munch [(usp - 24, usp - 8)] M M1 -> wmono psegs M M1 ->
     Q (MS (mkR ra (Z_to_bv 64 usp) x3 x4 x5 x6 x7 v0 v1 (Z_to_bv 64 0) sl dl x13 x14 x15 x16 x17
                x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (ret_pc ra) fc None M1 (seg_rom psegs))) ->
  evt psegs Q (MS (mkR x1 (Z_to_bv 64 (usp - 80)) x3 x4 x5 x6 x7 (Z_to_bv 64 (usp - 24)) (Z_to_bv 64 (usp - 16)) x10 x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x14fcc) fc None M (seg_rom psegs)).
Proof.
  intros Q M F fc w0 sl dl b0 bsl bdl ra v0 v1 x1 x3 x4 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         FR0 FR HK.
  pose proof (munch_refl [(usp - 24, usp - 8)] M) as MU.
  pose proof (wmono_refl psegs M) as WM.
  unfold S8_UNC_RA in *.
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

(* 1.4: zalloc returned NULL. inflateInit_ (from 0x15174) returns Z_MEM_ERROR, and uncompress2_z returns it at once
   to uncompress2 (0x14f6c, S8_HARN_RA), restoring s0 (= usp-24), s1 (= usp-16) and s2 .. s4 (v2 .. v4). *)
Lemma u2_seg_null_evt : forall (Q : machine_state -> Prop) (zm : bool) (qc : Z) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32) (ra v0 v1 v2 v3 v4 v5 : word)
    (x1 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  u2_frames M ra v0 v1 v2 v3 v4 v5 -> u2_za_cells M zm qc ->
  (forall y10 y13 : word,
     Q (MS (mkR (Z_to_bv 64 OL.S8_HARN_RA) (Z_to_bv 64 (usp - 80)) x3 x4 x5 x6 x7 (Z_to_bv 64 (usp - 24)) (Z_to_bv 64 (usp - 16)) y10 x11 x12 y13 x14 x15 x16 x17
                v2 v3 v4 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 OL.S8_HARN_RA) fc None M (seg_rom psegs))) ->
  evt psegs Q (MS (mkR x1 (Z_to_bv 64 (usp - 272)) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x151d4) fc None M (seg_rom psegs)).
Proof.
  intros Q zm qc M F fc ra v0 v1 v2 v3 v4 v5 x1 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         [F_hra F_wra F_us0 F_us1 F_ura F_s0 F_s1 F_s2 F_s3 F_s4] [Z_s2 Z_s1 Z_s0 Z_ra _ _ _ _ _] HK.
  unfold OL.S8_HARN_RA, OL.za_dest_S8, OL.S8_BUF, OL.S8_RA_II in *.
  (* inflateInit_'s frame (usp-272): s2, s1, s0, ra *)
  pose proof (ovr_of_rdn_Z M _ (usp - 272 + 24) _ Z_ra ltac:(lia) ltac:(lia)) as HR1.
  pose proof (ovr_of_rdn_Z M _ (usp - 272 + 16) _ Z_s0 ltac:(lia) ltac:(lia)) as HR2.
  pose proof (ovr_of_rdn_Z M _ (usp - 272 + 8) _ Z_s1 ltac:(lia) ltac:(lia)) as HR3.
  assert (DR : 0 <= (if zm then 0x32f10 + 0 * UU else 0x32f10) < 2 ^ 64) by (destruct zm; lia).
  pose proof (ovr_of_rdn_Z M _ (usp - 272 + 0) _ Z_s2 DR ltac:(lia)) as HR4.
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
  (* uncompress2_z at 0x14e2c: bnez a0 (taken); the epilogue (6 ld, addi, ret) *)
  step. if_true. do 8 step.
  apply evt_done.
  replace (usp - 240 + 160) with (usp - 80) by lia.
  apply HK.
Qed.

Lemma u2_seg_zw_evt : forall (Q : machine_state -> Prop) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  Q (MS (mkR (Z_to_bv 64 0x170d8) x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 32768) (Z_to_bv 64 32768) (Z_to_bv 64 1) (Z_to_bv 64 0x17280) x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x19484) fc None M (seg_rom psegs)) ->
  evt psegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 0) (Z_to_bv 64 32768) (Z_to_bv 64 1) (Z_to_bv 64 0x17280) x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x170d4) fc None M (seg_rom psegs)).
Proof.
  intros Q M F fc x1 x2 x3 x4 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 HK.
  do 5 step. apply evt_done. exact HK.
Qed.

Lemma u2_seg_ze1_evt : forall (Q : machine_state -> Prop) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32) (blk : word)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x12 x13 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  Q (MS (mkR (Z_to_bv 64 0x17250) x2 x3 x4 x5 x6 x7 x8 x9 blk blk x12 x13 (Z_to_bv 64 0x17290) x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x19344) fc None M (seg_rom psegs)) ->
  evt psegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 blk x12 x13 (Z_to_bv 64 0x17290) x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x1724c) fc None M (seg_rom psegs)).
Proof.
  intros Q M F fc blk x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x12 x13 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 HK.
  do 3 step. apply evt_done. exact HK.
Qed.

Lemma u2_seg_ze2_evt : forall (Q : machine_state -> Prop) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32) (blk : word)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x12 x13 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  Q (MS (mkR (Z_to_bv 64 0x17268) x2 x3 x4 x5 x6 x7 x8 x9 blk blk x12 x13 (Z_to_bv 64 0x17290) x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x19344) fc None M (seg_rom psegs)) ->
  evt psegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 blk x12 x13 (Z_to_bv 64 0x17290) x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x17264) fc None M (seg_rom psegs)).
Proof.
  intros Q M F fc blk x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x12 x13 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 HK.
  do 3 step. apply evt_done. exact HK.
Qed.

(* 1.4: the z_stream is at UU (1.3.1: UU + 8). *)
Lemma u2_seg_ze1b_evt : forall (Q : machine_state -> Prop) (zm : bool) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32) (p : Z)
    (x1 x2 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  OL.end_cells_S8 zm M UU p -> 0 <= p < 2^64 ->
  Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 (UU)) x9 (Z_to_bv 64 0) (Z_to_bv 64 p) (Z_to_bv 64 (UU)) x13 (Z_to_bv 64 0x17290) x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x17264) fc None M (seg_rom psegs)) ->
  evt psegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 (UU)) x9 x10 x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x17250) fc None M (seg_rom psegs)).
Proof.
  intros Q zm M F fc p x1 x2 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         (_ & E_st & E_zf & E_op) PR HK.
  unfold OL.S8_ZCFREE in *.
  pose proof (ovr_of_rdn_Z M _ (UU + 56) _ E_st ltac:(lia) ltac:(lia)) as HR1.
  pose proof (ovr_of_rdn_Z M _ (UU + 72) _ E_zf ltac:(lia) ltac:(lia)) as HR2.
  pose proof (ovr_of_rdn_Z M _ (UU + 80) _ E_op ltac:(lia) ltac:(lia)) as HR3.
  do 5 step. apply evt_done. exact HK.
Qed.

End SEG.
