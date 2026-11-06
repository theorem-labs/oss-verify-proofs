(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/FP.v; 609 of its 651 lines of code are new or changed and 349 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/crtA_conv.v, with its module paths changed; 862 of its 968 lines of code are new or changed and 545 lines of the source are left out. *)
(* crtB_loop: the convert-loop stage of the cgif-form walk of check_round_trip, image B (fuzz_decode.asan-ubsan,
   original pin): `crtB_loop : crtB_loop_stmt` of lib/B/Prog/crtB_cuts.v, the cut contract at CRT_LOOP_IN (+0x10c)
   from the one at CRT_LOOP_OUT (+0x26c), in the backward-chain form of the interface (template cgif
   origin/ossv/recipes proofs/cgif/cgif_file_fuzzer/lib/A/ACey.v:270-330).

   Two parts.
   (1) The footprint run of the two loops (CRT_LOOP_IN -> CRT_ILOOP .. CRT_LOOP_TAIL -> CRT_LOOP_OUT) as an
       ExecF.evtF run: crtB_loop_run.  Ported from the image-B donor records:
       - the five check lemmas bcl1_F .. bcl4_F, bcq8_F, crt_body_F, crt_inner_F, crt_outer_F and crt_sh1F from
         a working branch b04a1406048:proofs/libreac/fuzz_decode/lib/B/Prog/crt_loopF.v:33-525 (the
         footprint twin of the donor's crt_convert.v), pcs re-based on lib/B/Prog/crtB_iface.v (CRT_AT off);
       - the memory-side lemmas (the loop invariant crt_inv and its transport lemmas, crt_nn .. crt_inv_Q) from
         a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/B/Prog/crt_convert.v:141-397, with
         the invariant also keeping every present byte present (needed by the journal's mem_grows) and the frame's
         first four words as variables (each cut states its own frame words);
       - s24 / cv / conv_bytes / comb from lib/Prog/crt_convert.v:13-183 (the same text as the donor's
         lib/B/Prog/crt_enc.v:13-183; build-independent float algebra; this file does float steps, so nothing here
         loads lib/Lib/CrtEnc.v).
       Every offset was checked against the original image's listing
       (check_round_trip.fuzz_decode.asan-ubsan.s).
       Image-B facts walked here: every __asan_report_* RETURNS, so no report block is closed as terminal: the
       five report calls (+0x2fc .. +0x318) and the UBSan trap (+0x2ec) are excluded by refuting the guard of the
       branch into them (takeF false, the shadow facts of the blocks); the four slow paths +0x218 / +0x224 / +0x230
       / +0x23c (a partially poisoned last granule) are walked (both cases of each check lemma).
   (2) The cgif glue: the run is started at the cut's configuration by crtB_walk.crtB_run (the evtF -> SRr bridge,
       proved there), its premises read off the cut (the blocks' presence and shadow from cgif's AR laws, the pcm
       bytes from the inner journal, the frame from crtB_frame), and its end is the loop-out cut: the inner journal
       re-established by YCbq.v:636 ajournal_exec, the frame, the registers, crtB_rom_on and crtB_conv. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac
  Bytes ZBridge FP.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import AsanKA AsanKAProof ReacDecodeLib check_braid.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBAddr crtB_iface.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import FloatExact.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require crt_convert.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.
Module PCC := OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog.crt_convert.

(* ======================================================================================================== *)
(* Part 1: the footprint run of the convert loop                                                            *)
(* ======================================================================================================== *)

(* b04a1406048 crt_loopF.v:22-24. *)
Ltac takeF b := lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; solve_c]
  end.

(* Every pc in a statement below is a crtB_iface name; compute that one pc term to its value before stepping
   (the form of lib/B/Prog/crtB_segs.v crt_pc). *)
Ltac crt_pc := lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => let v := eval vm_compute in pc in change pc with v
  end.
Ltac cstep := crt_pc; step.

(* b04a1406048 crt_loopF.v:33-34. *)
Lemma align8_cover : forall a b c, a <= b -> b <= c -> a / 8 * 8 <= b /\ b + 1 <= c / 8 * 8 + 8.
Proof. intros a b c H1 H2. split; Z.div_mod_to_equations; lia. Qed.

(* b04a1406048 crt_loopF.v:39-50: the shadow byte of X + i lies in the 8-aligned cover of the shadow bytes of
   [X, X + n). *)
Lemma crt_sh1F : forall RNG X n,
  ExecF.rng RNG (shadow_addr X / 8 * 8)
    (shadow_addr (X + n - 1) / 8 * 8 + 8 - shadow_addr X / 8 * 8) ->
  forall i, 0 <= i < n -> ExecF.rng RNG (shadow_addr (X + i)) 1.
Proof.
  intros RNG X n H i Hi. unfold shadow_addr in *.
  assert (L1 : X / 8 <= (X + i) / 8) by (apply Z.div_le_mono; lia).
  assert (L2 : (X + i) / 8 <= (X + n - 1) / 8) by (apply Z.div_le_mono; lia).
  destruct (align8_cover (X / 8 + ASAN_K) ((X + i) / 8 + ASAN_K) ((X + n - 1) / 8 + ASAN_K)
             ltac:(lia) ltac:(lia)) as (A1 & A2).
  eapply ExecF.rng_sub; [exact H | lia | lia].
Qed.

(* ---- the five instrumented checks of the inner loop and the planar store (b04a1406048 crt_loopF.v:57-191) ---- *)

(* CRT_AT 0x170 -> 0x184: a2 := s9 + s1 (the pcm byte); its shadow byte (lb a1); slow path +0x218 (andi s3,a2,7;
   bge s3,a1 to the load1 report at +0x310: not taken, the byte is addressable; j +0x184). *)
Lemma bcl1_F : forall (RNG : ExecF.footprint)
  (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x25 + bv_unsigned x9 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  ExecF.rng RNG (A / 8 + ASAN_K) 1 ->
  (forall y11 y12 y19 : word, bv_unsigned y12 = A ->
     ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y11 y12 x13 x14 x15 x16 x17 x18 y19 x20 x21 x22
       x23 (Z_to_bv 64 ASAN_K) x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (CRT_AT 0x184)) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
    (Z_to_bv 64 ASAN_K) x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (CRT_AT 0x170)) fc None mm (seg_rom rsegs)).
Proof.
  intros until A. intros EA RA M SK RK CONT.
  pose proof (u64_range x25) as R25. pose proof (u64_range x9) as R9. unfold ASAN_K in *. crt_pc.
  step. gen_add x25 x9 w U. rewrite EA in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT. exact U.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, U, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT. exact U.
Qed.

(* CRT_AT 0x18c -> 0x1a8: s6 := s4 + s1; a5 := a2 + 1; shadow byte of a5 (lb s3); b0 := [s6] (lbu s7); slow path
   +0x224 (andi a2,a5,7; bge a2,s3 to the load1 report at +0x308: not taken; j +0x1a8). *)
Lemma bcl2_F : forall (RNG : ExecF.footprint)
  (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b0 : byte) (A Dd : Z),
  bv_unsigned x12 = A -> A + 1 < 2^64 ->
  mrd rsegs mm (wa ((A + 1) / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ (A + 1) mod 8 < bv_signed k) ->
  bv_unsigned x20 + bv_unsigned x9 = Dd -> Dd < 2^64 -> mrd rsegs mm (wa Dd) = Some b0 ->
  ExecF.rng RNG ((A + 1) / 8 + ASAN_K) 1 -> ExecF.rng RNG Dd 1 ->
  (forall y12 y15 y19 y22 : word, bv_unsigned y22 = Dd ->
     ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 y12 x13 x14 y15 x16 x17 x18 y19 x20 x21 y22
       (zxb b0) (Z_to_bv 64 ASAN_K) x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (CRT_AT 0x1a8)) fc None mm
       (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
    (Z_to_bv 64 ASAN_K) x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (CRT_AT 0x18c)) fc None mm (seg_rom rsegs)).
Proof.
  intros until Dd. intros E12 RA M SK Ed DB MD RK RD CONT.
  pose proof (u64_range x12) as R12. pose proof (u64_range x20) as R20. pose proof (u64_range x9) as R9.
  unfold ASAN_K in *. crt_pc.
  step. gen_add x20 x9 ws6 Us6. rewrite Ed in Us6.
  step. gen_addi x12 wa5 Ua5. rewrite E12 in Ua5.
  step. gen_shr wa5 g G. rewrite Ua5 in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw0 mm ws6 _ _ MD Us6) as R2. step. clear R2.
  step.
  pose proof (Z.mod_pos_bound (A + 1) 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT. exact Us6.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, Ua5, (lts_low ((A + 1) mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT. exact Us6.
Qed.

(* CRT_AT 0x1a8 -> 0x1bc: shadow byte of a1 = a2 + 2 (lb s3); b1 := [s6 + 1] (lbu a2); slow path +0x230 (andi a5,a1,7;
   bge a5,s3 to the load1 report at +0x300: not taken; j +0x1bc). *)
Lemma bcl3_F : forall (RNG : ExecF.footprint)
  (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b1 : byte) (A Dd : Z),
  bv_unsigned x11 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  bv_unsigned x22 = Dd -> mrd rsegs mm (wa (Dd + 1)) = Some b1 ->
  ExecF.rng RNG (A / 8 + ASAN_K) 1 -> ExecF.rng RNG (Dd + 1) 1 ->
  (forall y15 y19 : word,
     ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (zxb b1) x13 x14 y15 x16 x17 x18 y19 x20 x21
       x22 x23 (Z_to_bv 64 ASAN_K) x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (CRT_AT 0x1bc)) fc None mm
       (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
    (Z_to_bv 64 ASAN_K) x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (CRT_AT 0x1a8)) fc None mm (seg_rom rsegs)).
Proof.
  intros until Dd. intros E11 RA M SK Ed MD RK RD CONT.
  pose proof (u64_range x11) as R11. pose proof (u64_range x22) as R22. unfold ASAN_K in *. crt_pc.
  step. gen_shr x11 g G. rewrite E11 in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw mm x22 1 _ _ MD ltac:(lia)) as R2. step. clear R2.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, E11, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* CRT_AT 0x1c8 -> 0x1dc: shadow byte of a0 (the 4-byte float store; lb s3); b2 := [s6 + 2] (lb a1, signed); slow
   path +0x23c (andi a5,a0,7; addi a5,a5,3; bge a5,s3 to the store4 report at +0x2fc: not taken; j +0x1dc). *)
Lemma bcl4_F : forall (RNG : ExecF.footprint)
  (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b2 : byte) (A Dd : Z),
  bv_unsigned x10 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 + 3 < bv_signed k) ->
  bv_unsigned x22 = Dd -> mrd rsegs mm (wa (Dd + 2)) = Some b2 ->
  ExecF.rng RNG (A / 8 + ASAN_K) 1 -> ExecF.rng RNG (Dd + 2) 1 ->
  (forall y15 y19 : word,
     ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (sxb b2) x12 x13 x14 y15 x16 x17 x18 y19 x20 x21
       x22 x23 (Z_to_bv 64 ASAN_K) x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (CRT_AT 0x1dc)) fc None mm
       (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
    (Z_to_bv 64 ASAN_K) x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (CRT_AT 0x1c8)) fc None mm (seg_rom rsegs)).
Proof.
  intros until Dd. intros E10 RA M SK Ed MD RK RD CONT.
  pose proof (u64_range x10) as R10. pose proof (u64_range x22) as R22. unfold ASAN_K in *. crt_pc.
  step. gen_shr x10 g G. rewrite E10 in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw mm x22 2 _ _ MD ltac:(lia)) as R2. step. clear R2.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. step. rewrite land7, E10, (lts_sm (A mod 8 + 3) k ltac:(lia)), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* CRT_AT 0x13c -> 0x14c: shadow byte of a0 (the 8-byte planar[c] store; lbu a1); it is 0, so the bnez to the
   store8 report at +0x318 is not taken. *)
Lemma bcq8_F : forall (RNG : ExecF.footprint)
  (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x10 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k -> bv_unsigned k = 0 ->
  ExecF.rng RNG (A / 8 + ASAN_K) 1 ->
  (forall y11 : word,
     ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22
       x23 (Z_to_bv 64 ASAN_K) x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (CRT_AT 0x14c)) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
    (Z_to_bv 64 ASAN_K) x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (CRT_AT 0x13c)) fc None mm (seg_rom rsegs)).
Proof.
  intros until A. intros EA RA M HK RK CONT.
  pose proof (u64_range x10) as R10. unfold ASAN_K in *. crt_pc.
  step. gen_shr x10 g G. rewrite EA in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  replace (zxb k) with (Z_to_bv 64 0) by (unfold zxb; rewrite HK; reflexivity).
  step. apply CONT.
Qed.

(* ---- generic helpers (dc455613c81 crt_convert.v:150-165) ---- *)

Lemma byte_sgn0 : forall k : byte, bv_signed k = 0 -> bv_unsigned k = 0.
Proof.
  intros k H. pose proof (bv_unsigned_in_range 8 k) as R. change (bv_modulus 8) with 256 in R.
  unfold bv_signed, bv_swrap, bv_wrap in H. change (bv_half_modulus 8) with 128 in H.
  change (bv_modulus 8) with 256 in H. Z.div_mod_to_equations. lia.
Qed.

Lemma addr_byte_one : forall m p n i, addressable m p n -> 0 <= i < n ->
  app_mem (p + i) /\ exists b, mrd rsegs m (wa ((p + i) / 8 + ASAN_K)) = Some b /\ shadow_ok (p + i) (bv_signed b).
Proof.
  intros m p n i (H0 & H1 & H2 & H) Hi. destruct (H i Hi) as (Ha & b & Hb & Hok).
  split; [exact Ha | exists b; split; [exact Hb | exact Hok]].
Qed.

Lemma land3 : forall x, Z.land x 3 = x mod 4.
Proof. intros x. exact (Z.land_ones x 2 ltac:(lia)). Qed.

(* A write keeps every present byte present (the journal's mem_grows at the loop's end). *)
Lemma crt_write_grows : forall bs (m : word -> option byte) a x, m x <> None -> write_to_mem m a bs x <> None.
Proof.
  induction bs as [|b bs IH]; intros m a x H; cbn; [exact H|].
  apply IH. destruct (bv_eqb x a); [discriminate | exact H].
Qed.

(* The memory the loop may change: the two blocks and its own frame (dc455613c81 crt_iface.v:59). *)
Definition crtB_W (sp P Q nch ns : Z) : list ivl := [(P, P + 4 * nch * ns); (Q, Q + 8 * nch); (sp, sp + 160)].

(* The tactic tuning of dc455613c81 crt_convert.v:167-177: lia only, never a nia fallback; nonlinear goals are
   proved in small contexts. *)
Local Ltac rng ::= lia.
Local Ltac fct := try unfold wa; norm;
  first [ reflexivity | lia | (rewrite ?unsigned_lit_wrap; zb_fold_lits; Z.div_mod_to_equations; lia) ].
Local Ltac word_eq_tac ::= first [ exact eq_refl | (apply wa_of_var; first [assumption | fct])
  | f_equal; lia | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia
  | (norm; first [ reflexivity | f_equal; lia | lia ]) ].
Local Ltac wfct := rewrite ?land3, ?land7; first [ fct | fact ].

(* b04a1406048 crt_loopF.v:203-215: the stores and the frame loads go through computed addresses; StepF's acc_hint
   hook takes the access to a range hypothesis and normalises the address first. *)
Local Ltac acc_hint ::=
  lazymatch goal with
  | |- ExecF.acc_in ?RNG (?a, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      match goal with
      | HR : ExecF.rng RNG ?lo ?len |- _ =>
          apply (ExecF.rng_acc_varZ RNG lo len a n nz HR (@eq_refl Z nz)); norm; lia
      end
  end.

(* The loop under a footprint: the premises of dc455613c81 crt_convert.v's Section Loops (the frame's first four
   words f0 .. f24 as variables), the footprint RNG and its ranges (b04a1406048 crt_loopF.v:222-270). *)
Section LoopsF.
Variables (wsp gp tp t0 t1 t2 a6 a7 s2 s5 t3 t4 t5 t6 : word).
Variables (m0 : word -> option byte) (pb : Z -> byte).
Variables (sp pcm nch ns P Q : Z).
Variables (f0 f8 f16 f24 w32 vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : word).
Variable RNG : ExecF.footprint.

Hypothesis HN : 2 <= nch <= 127.
Hypothesis HNS : 1 <= ns <= 12.
Hypothesis HB : 3 * nch * ns <= 1440.
Hypothesis HS0 : HIGHMEM_BEG <= sp.
Hypothesis HS1 : sp + 160 <= APPMEM_END.
Hypothesis HP0 : 0 < P.
Hypothesis HP4 : P mod 4 = 0.
Hypothesis HQ0 : 0 < Q.
Hypothesis HQ8 : Q mod 8 = 0.
Hypothesis DPQ : P + 4 * nch * ns <= Q \/ Q + 8 * nch <= P.
Hypothesis DPC : P + 4 * nch * ns <= pcm \/ pcm + 3 * nch * ns <= P.
Hypothesis DQC : Q + 8 * nch <= pcm \/ pcm + 3 * nch * ns <= Q.
Hypothesis DPS : P + 4 * nch * ns <= sp \/ sp + 160 <= P.
Hypothesis DQS : Q + 8 * nch <= sp \/ sp + 160 <= Q.
Hypothesis DCS : pcm + 3 * nch * ns <= sp \/ sp + 160 <= pcm.
Hypothesis PB : forall i, 0 <= i < 3 * nch * ns -> mrd rsegs m0 (wa (pcm + i)) = Some (pb i).
Hypothesis APC : addressable m0 pcm (3 * nch * ns).
Hypothesis WP : wr_at rsegs m0 P (4 * nch * ns).
Hypothesis AP : addressable m0 P (4 * nch * ns).
Hypothesis WQ : wr_at rsegs m0 Q (8 * nch).
Hypothesis AQ : addressable m0 Q (8 * nch).
Hypothesis Hsp : bv_unsigned wsp = sp.
Hypothesis Ht0 : bv_unsigned t0 = 0.
Hypothesis Ht1 : bv_unsigned t1 = 4 * ns.
Hypothesis Ht2 : bv_unsigned t2 = 1.
Hypothesis Ha6 : bv_unsigned a6 = 18446744073709551615 - pcm.
Hypothesis Ha7 : bv_unsigned a7 = 0.
Hypothesis Hs2 : bv_unsigned s2 = ns.
Hypothesis Hs5 : bv_unsigned s5 = Q.
Hypothesis Ht3 : bv_unsigned t3 = 18446744073692774400.
Hypothesis Ht4 : bv_unsigned t4 = 3 * ns.
Hypothesis Ht5 : bv_unsigned t5 = 2305843009213693952.
Hypothesis Ht6 : bv_unsigned t6 = 3 * ns.
Hypothesis Hw32 : bv_unsigned w32 = 18446744073709551615 - P.
Hypothesis RP : ExecF.rng RNG P (4 * nch * ns).
Hypothesis RQ : ExecF.rng RNG Q (8 * nch).
Hypothesis RC : ExecF.rng RNG pcm (3 * nch * ns).
Hypothesis RSHP : forall i, 0 <= i < 4 * nch * ns -> ExecF.rng RNG (shadow_addr (P + i)) 1.
Hypothesis RSHQ : forall i, 0 <= i < 8 * nch -> ExecF.rng RNG (shadow_addr (Q + i)) 1.
Hypothesis RSHC : forall i, 0 <= i < 3 * nch * ns -> ExecF.rng RNG (shadow_addr (pcm + i)) 1.
Hypothesis RFR : ExecF.rng RNG (sp + 32) 24.

(* The frame at [sp, sp + 160): its own seven words (32(sp) = ~P, 40(sp) = nch, 48(sp) = P are the ones the loop
   loads) and the caller's s11 .. s0, ra (dc455613c81 crt_convert.v:221-224, crtB_iface.v crt_fr). *)
Local Notation FRAME :=
  [C8 f0; C8 f8; C8 f16; C8 f24; C8 w32; C8 (Z_to_bv 64 nch); C8 (Z_to_bv 64 P);
   C8 v11; C8 v10; C8 v9; C8 v8; C8 v7; C8 v6; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra].

(* The loop invariant (dc455613c81 crt_convert.v:226-230), with every present byte kept present. *)
Definition crt_inv (m : word -> option byte) (kp kq : Z) : Prop :=
  munch (crtB_W sp P Q nch ns) m0 m /\ wmono rsegs m0 m /\ (forall x, m0 x <> None -> m x <> None) /\
  rw_cells rsegs m (bv_unsigned wsp) FRAME /\
  (forall j, 0 <= j < kp -> bytes_at rsegs m (P + 4 * j) (Z_to_le_bytes 4 (PCC.cv pb j))) /\
  (forall c, 0 <= c < kq -> bytes_at rsegs m (Q + 8 * c) (le8 (Z_to_bv 64 (P + 4 * (c * ns))))).

(* ---- the memory-side lemmas (dc455613c81 crt_convert.v:232-397) ---- *)

Lemma crt_nn : 0 < nch * ns /\ nch * ns <= 480.
Proof. split; [apply Z.mul_pos_pos; lia | nia]. Qed.

Lemma crt_bnd : 0 <= P /\ P + 4 * nch * ns <= APPMEM_END /\ 0 <= Q /\ Q + 8 * nch <= APPMEM_END /\
  0 <= pcm /\ pcm + 3 * nch * ns <= APPMEM_END.
Proof.
  destruct AP as (A1 & _ & A3 & _). destruct AQ as (B1 & _ & B3 & _). destruct APC as (C1 & _ & C3 & _).
  repeat split; assumption.
Qed.

Lemma crt_app_P : forall x, P <= x < P + 4 * nch * ns -> app_mem x.
Proof.
  intros x Hx. destruct (addr_one m0 P (4 * nch * ns) (x - P) AP ltac:(lia)) as (Ha & _).
  replace (P + (x - P)) with x in Ha by lia. exact Ha.
Qed.

Lemma crt_app_Q : forall x, Q <= x < Q + 8 * nch -> app_mem x.
Proof.
  intros x Hx. destruct (addr_one m0 Q (8 * nch) (x - Q) AQ ltac:(lia)) as (Ha & _).
  replace (Q + (x - Q)) with x in Ha by lia. exact Ha.
Qed.

Lemma crt_app_F : forall x, sp <= x < sp + 160 -> app_mem x.
Proof. intros x Hx. unfold app_mem, HIGHMEM_BEG, APPMEM_END in *. lia. Qed.

Lemma crt_shadow_out : forall a, app_mem a -> outside (crtB_W sp P Q nch ns) (a / 8 + ASAN_K).
Proof.
  intros a Ha. unfold crtB_W. cbn [outside].
  split; [|split; [|split; [|exact I]]]; intros H.
  - exact (shadow_not_app a Ha (crt_app_P _ H)).
  - exact (shadow_not_app a Ha (crt_app_Q _ H)).
  - exact (shadow_not_app a Ha (crt_app_F _ H)).
Qed.

Lemma crt_out_pcm : forall i, 0 <= i < 3 * nch * ns -> outside (crtB_W sp P Q nch ns) (pcm + i).
Proof. intros i Hi. unfold crtB_W. cbn [outside]. repeat split; try exact I; lia. Qed.

Lemma crt_inv_addr : forall m kp kq p n, crt_inv m kp kq -> addressable m0 p n -> addressable m p n.
Proof.
  intros m kp kq p n (MU & _) A. eapply addr_munch; [exact A | exact MU |].
  intros i Hi. apply crt_shadow_out. destruct (addr_one m0 p n i A Hi) as (Ha & _). exact Ha.
Qed.

Lemma crt_inv_pcm : forall m kp kq (D : Z) i, crt_inv m kp kq -> 0 <= i -> i + 2 < 3 * nch * ns -> D = pcm + i ->
  mrd rsegs m (wa D) = Some (pb i) /\ mrd rsegs m (wa (D + 1)) = Some (pb (i + 1)) /\
  mrd rsegs m (wa (D + 2)) = Some (pb (i + 2)).
Proof.
  intros m kp kq D i Hinv Hi0 Hi2 ->. pose proof crt_bnd as (_ & _ & _ & _ & BC0 & BC1).
  destruct Hinv as (MU & _).
  assert (E : forall d, 0 <= d < 3 * nch * ns -> mrd rsegs m (wa (pcm + d)) = Some (pb d)).
  { intros d Hd. unfold mrd in *. rewrite (MU (wa (pcm + d))); [exact (PB d Hd)|].
    rewrite wa_unsigned by (unfold APPMEM_END in *; lia). apply crt_out_pcm. exact Hd. }
  split; [|split].
  - apply E. lia.
  - replace (pcm + i + 1) with (pcm + (i + 1)) by lia. apply E. lia.
  - replace (pcm + i + 2) with (pcm + (i + 2)) by lia. apply E. lia.
Qed.

Lemma crt_sh_pcm : forall m kp kq (D : Z) i, crt_inv m kp kq -> 0 <= i -> i + 2 < 3 * nch * ns -> D = pcm + i ->
  (exists k, mrd rsegs m (wa (D / 8 + ASAN_K)) = Some k /\ (bv_signed k = 0 \/ D mod 8 < bv_signed k)) /\
  (exists k, mrd rsegs m (wa ((D + 1) / 8 + ASAN_K)) = Some k /\ (bv_signed k = 0 \/ (D + 1) mod 8 < bv_signed k)) /\
  (exists k, mrd rsegs m (wa ((D + 2) / 8 + ASAN_K)) = Some k /\ (bv_signed k = 0 \/ (D + 2) mod 8 < bv_signed k)).
Proof.
  intros m kp kq D i Hinv Hi0 Hi2 ->.
  pose proof (crt_inv_addr m kp kq pcm (3 * nch * ns) Hinv APC) as AD.
  split; [|split].
  - destruct (addr_one m pcm (3 * nch * ns) i AD ltac:(lia)) as (_ & k & Mk & Sk). exists k. split; assumption.
  - destruct (addr_one m pcm (3 * nch * ns) (i + 1) AD ltac:(lia)) as (_ & k & Mk & Sk).
    replace (pcm + i + 1) with (pcm + (i + 1)) by lia. exists k. split; assumption.
  - destruct (addr_one m pcm (3 * nch * ns) (i + 2) AD ltac:(lia)) as (_ & k & Mk & Sk).
    replace (pcm + i + 2) with (pcm + (i + 2)) by lia. exists k. split; assumption.
Qed.

Lemma crt_sh_P4 : forall m kp kq (A : Z) k, crt_inv m kp kq -> 0 <= k < nch * ns -> A = P + 4 * k ->
  exists kb, mrd rsegs m (wa (A / 8 + ASAN_K)) = Some kb /\ (bv_signed kb = 0 \/ A mod 8 + 3 < bv_signed kb).
Proof.
  intros m kp kq A k Hinv Hk ->.
  pose proof (crt_inv_addr m kp kq P (4 * nch * ns) Hinv AP) as AD.
  destruct (addr_one m P (4 * nch * ns) (4 * k + 3) AD ltac:(nia)) as (_ & kb & Mk & Sk).
  assert (M4 : exists s, P + 4 * k = 4 * s).
  { exists (P / 4 + k). pose proof (Z.div_mod P 4 ltac:(lia)) as D. rewrite HP4 in D. lia. }
  destruct M4 as (s & Es).
  assert (E8 : (P + (4 * k + 3)) / 8 = (P + 4 * k) / 8 /\ (P + (4 * k + 3)) mod 8 = (P + 4 * k) mod 8 + 3).
  { replace (P + (4 * k + 3)) with (4 * s + 3) by lia. replace (P + 4 * k) with (4 * s) by lia.
    Z.div_mod_to_equations. lia. }
  destruct E8 as (E1 & E2). rewrite E1 in Mk. rewrite E2 in Sk. exists kb. split; assumption.
Qed.

Lemma crt_sh_Q8 : forall m kp kq (A : Z) c, crt_inv m kp kq -> 0 <= c < nch -> A = Q + 8 * c ->
  exists kb, mrd rsegs m (wa (A / 8 + ASAN_K)) = Some kb /\ bv_unsigned kb = 0.
Proof.
  intros m kp kq A c Hinv Hc ->.
  pose proof (crt_inv_addr m kp kq Q (8 * nch) Hinv AQ) as AD.
  destruct (addr_byte_one m Q (8 * nch) (8 * c + 7) AD ltac:(lia)) as (_ & kb & Mk & Sk).
  assert (E8 : (Q + (8 * c + 7)) / 8 = (Q + 8 * c) / 8 /\ (Q + (8 * c + 7)) mod 8 = 7).
  { Z.div_mod_to_equations. lia. }
  destruct E8 as (E1 & E2). rewrite E1 in Mk. unfold shadow_ok in Sk. rewrite E2 in Sk.
  exists kb. split; [exact Mk | apply byte_sgn0; lia].
Qed.

Lemma crt_stP : forall m kp kq (w : word) k, crt_inv m kp kq -> 0 <= k < nch * ns -> bv_unsigned w = P + 4 * k ->
  store_ok rsegs m w 4 = true.
Proof.
  intros m kp kq w k (_ & WM & _) Hk Hw.
  rewrite <- (wa_of_var w (P + 4 * k) Hw).
  exact (wr_at_store_ok rsegs m P (4 * nch * ns) (4 * k) 4%nat (wr_at_transport rsegs m0 m P _ WP WM)
           ltac:(lia) ltac:(cbn [Z.of_nat]; nia)).
Qed.

Lemma crt_stQ : forall m kp kq (w : word) c, crt_inv m kp kq -> 0 <= c < nch -> bv_unsigned w = Q + 8 * c ->
  store_ok rsegs m w 8 = true.
Proof.
  intros m kp kq w c (_ & WM & _) Hc Hw.
  rewrite <- (wa_of_var w (Q + 8 * c) Hw).
  exact (wr_at_store_ok rsegs m Q (8 * nch) (8 * c) 8%nat (wr_at_transport rsegs m0 m Q _ WQ WM)
           ltac:(lia) ltac:(cbn [Z.of_nat]; lia)).
Qed.

Lemma crt_inv_P : forall m kp kq (a : word) bs, crt_inv m kp kq -> 0 <= kp < nch * ns -> 0 <= kq <= nch ->
  bv_unsigned a = P + 4 * kp -> bs = Z_to_le_bytes 4 (PCC.cv pb kp) -> crt_inv (write_to_mem m a bs) (kp + 1) kq.
Proof.
  intros m kp kq a bs (MU & WM & PR & FR & HPd & HQd) Hk Hkq Ha ->.
  pose proof crt_nn as (NN0 & NN1). pose proof crt_bnd as (BP0 & BP1 & BQ0 & BQ1 & BC0 & BC1).
  unfold APPMEM_END in BP1, BQ1, BC1.
  rewrite <- (wa_of_var a (P + 4 * kp) Ha).
  assert (LEN : Z.of_nat (length (Z_to_le_bytes 4 (PCC.cv pb kp))) = 4)
    by (rewrite length_Z_to_le_bytes; reflexivity).
  split; [|split; [|split; [|split; [|split]]]].
  - apply munch_write; [exact MU | lia | rewrite LEN; lia |].
    unfold crtB_W. cbn [inside]. rewrite LEN. left. clear - Hk. lia.
  - apply wmono_write. exact WM.
  - intros x Hx. apply crt_write_grows. exact (PR x Hx).
  - apply rw_cells_frame; [exact FR | lia | rewrite LEN; lia |].
    cbn [cells_size csize Nat.add]. rewrite LEN, Hsp. clear - DPS Hk NN0 NN1 HNS HN. nia.
  - intros j Hj. destruct (Z.eq_dec j kp) as [->|Hne].
    + apply bytes_at_write_same; [lia | rewrite LEN; lia].
    + apply bytes_at_write_other; [apply HPd; lia | lia | rewrite LEN; lia |].
      rewrite !length_Z_to_le_bytes. lia.
  - intros c Hc. apply bytes_at_write_other; [apply HQd; lia | lia | rewrite LEN; lia |].
    rewrite LEN, length_le8. clear - DPQ Hk Hkq Hc NN0 NN1 HNS HN. nia.
Qed.

Lemma crt_inv_Q : forall m kp kq (a v : word) bs, crt_inv m kp kq -> 0 <= kq < nch -> 0 <= kp <= nch * ns ->
  bv_unsigned a = Q + 8 * kq -> bs = le8 v -> bv_unsigned v = P + 4 * (kq * ns) ->
  crt_inv (write_to_mem m a bs) kp (kq + 1).
Proof.
  intros m kp kq a v bs (MU & WM & PR & FR & HPd & HQd) Hc Hkp Ha -> Hv.
  pose proof crt_nn as (NN0 & NN1). pose proof crt_bnd as (BP0 & BP1 & BQ0 & BQ1 & BC0 & BC1).
  unfold APPMEM_END in BP1, BQ1, BC1.
  assert (CB : 0 <= kq * ns /\ kq * ns + ns <= nch * ns).
  { split; [apply Z.mul_nonneg_nonneg; lia|].
    replace (kq * ns + ns) with ((kq + 1) * ns) by ring. apply Z.mul_le_mono_nonneg_r; lia. }
  assert (Ev : v = Z_to_bv 64 (P + 4 * (kq * ns))) by (apply bv_eq; rewrite unsigned_lit by lia; exact Hv).
  rewrite <- (wa_of_var a (Q + 8 * kq) Ha).
  assert (LEN : Z.of_nat (length (le8 v)) = 8) by (rewrite length_le8; reflexivity).
  split; [|split; [|split; [|split; [|split]]]].
  - apply munch_write; [exact MU | lia | rewrite LEN; lia |].
    unfold crtB_W. cbn [inside]. rewrite LEN. right. left. lia.
  - apply wmono_write. exact WM.
  - intros x Hx. apply crt_write_grows. exact (PR x Hx).
  - apply rw_cells_frame; [exact FR | lia | rewrite LEN; lia |].
    cbn [cells_size csize Nat.add]. rewrite LEN, Hsp. clear - DQS Hc HN. lia.
  - intros j Hj. apply bytes_at_write_other; [apply HPd; lia | lia | rewrite LEN; lia |].
    rewrite LEN, length_Z_to_le_bytes. clear - DPQ Hj Hc Hkp CB NN0 NN1 HN HNS. nia.
  - intros c Hc'. destruct (Z.eq_dec c kq) as [->|Hne].
    + rewrite Ev. apply bytes_at_write_same; [lia | rewrite length_le8; lia].
    + apply bytes_at_write_other; [apply HQd; lia | lia | rewrite LEN; lia |].
      rewrite LEN, length_le8. lia.
Qed.

Local Notation ST pc ra s0 s1 a0 a1 a2 a3 a4 a5 s3 s4 s6 s7 s9 s10 s11 Fh fx mm :=
  (MS (mkR ra wsp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7
           (Z_to_bv 64 ASAN_K) s9 s10 s11 t3 t4 t5 t6)
      Fh (Z_to_bv 64 pc) fx None mm (seg_rom rsegs)).

(* One pass of the inner loop: CRT_ILOOP (the three pcm bytes, the conversion, the 4-byte store) to CRT_AT 0x210
   (b04a1406048 crt_loopF.v:308-389). *)
Lemma crt_body_F : forall (G : machine_state -> Prop) c j (ra s0 s1 a0 a1 a2 a3 a4 a5 s3 s4 s6 s7 s9 s10 s11 : word)
    (Fh : bvmap 5 word) (fx : bv 32) (m : word -> option byte),
  0 <= c < nch -> 0 <= j < ns ->
  bv_unsigned ra = P + 4 * (c * ns) ->
  bv_unsigned a3 = 3 * (c * ns) ->
  bv_unsigned s4 = pcm + 3 * (c * ns) ->
  bv_unsigned s9 = pcm + 3 * (c * ns) ->
  bv_unsigned s1 = 3 * j ->
  bv_unsigned a0 = P + 4 * (c * ns + j) ->
  bv_unsigned s10 = P + 4 * (c * ns + j) ->
  unbox_s (reg_get Fh (Z_to_bv 5 15)) = Z_to_bv 32 F2M23 ->
  frm0 fx -> crt_inv m (c * ns + j) (c + 1) ->
  (forall (s1' a0' a1' a2' a5' s3' s6' s7' s10' v : word) (fx' : bv 32) (m' : word -> option byte),
     bv_unsigned s1' = 3 * (j + 1) ->
     bv_unsigned a0' = P + 4 * (c * ns + j + 1) ->
     bv_unsigned s10' = P + 4 * (c * ns + j + 1) ->
     frm0 fx' -> crt_inv m' (c * ns + j + 1) (c + 1) ->
     ExecF.evtF rsegs RNG G (ST (CRT_AT 0x210) ra s0 s1' a0' a1' a2' a3 a4 a5' s3' s4 s6' s7' s9 s10' s11
                     (bvmap_set (Z_to_bv 5 14) v Fh) fx' m')) ->
  ExecF.evtF rsegs RNG G (ST CRT_ILOOP ra s0 s1 a0 a1 a2 a3 a4 a5 s3 s4 s6 s7 s9 s10 s11 Fh fx m).
Proof.
  intros G c j ra s0 s1 a0 a1 a2 a3 a4 a5 s3 s4 s6 s7 s9 s10 s11 Fh fx m
    Hc Hj Hra Ha3 Hs4 Hs9 Hs1 Ha0 Hs10 H5 Hfx Hinv K.
  pose proof crt_nn as (NN0 & NN1). pose proof crt_bnd as (BP0 & BP1 & BQ0 & BQ1 & BC0 & BC1).
  unfold APPMEM_END in BP1, BQ1, BC1.
  assert (B0 : 0 <= c * ns) by (apply Z.mul_nonneg_nonneg; lia).
  assert (B1 : c * ns + ns <= nch * ns)
    by (replace (c * ns + ns) with ((c + 1) * ns) by ring; apply Z.mul_le_mono_nonneg_r; lia).
  assert (BK : 0 <= c * ns + j < nch * ns) by lia.
  assert (BI : 0 <= 3 * (c * ns + j) /\ 3 * (c * ns + j) + 2 < 3 * nch * ns) by lia.
  assert (BP : 0 <= 4 * (c * ns + j) /\ 4 * (c * ns + j) + 4 <= 4 * nch * ns) by lia.
  destruct (crt_inv_pcm m _ _ (pcm + 3 * (c * ns + j)) (3 * (c * ns + j)) Hinv ltac:(lia) ltac:(lia) eq_refl)
    as (MD0 & MD1 & MD2).
  destruct (crt_sh_pcm m _ _ (pcm + 3 * (c * ns + j)) (3 * (c * ns + j)) Hinv ltac:(lia) ltac:(lia) eq_refl)
    as ((k0 & M0 & S0) & (k1 & M1 & S1) & (k2 & M2 & S2)).
  destruct (crt_sh_P4 m _ _ (P + 4 * (c * ns + j)) (c * ns + j) Hinv ltac:(lia) eq_refl) as (kP & MP & SP).
  pose proof (crt_stP m _ _ s10 (c * ns + j) Hinv ltac:(lia) Hs10) as HSt.
  (* +0x168 add a1,a3,s1 ; +0x16c bltu a6,a1 (pointer overflow of pcm + s1: not taken) *)
  cstep. step. takeF false.
  (* +0x170 .. +0x184 *)
  eapply bcl1_F with (A := pcm + 3 * (c * ns + j)) (k := k0);
    [fct | lia | exact M0 | exact S0 | apply (RSHC (3 * (c * ns + j))); lia |].
  intros y11 y12 y19 Ey12.
  (* +0x184 addi a1,a2,2 ; +0x188 bgeu t2,a1 (not taken) *)
  cstep. step. takeF false.
  (* +0x18c .. +0x1a8 *)
  eapply bcl2_F with (A := pcm + 3 * (c * ns + j)) (Dd := pcm + 3 * (c * ns + j)) (k := k1)
    (b0 := pb (3 * (c * ns + j))); [exact Ey12 | lia | exact M1 | exact S1 | fct | lia | exact MD0
    | replace (pcm + 3 * (c * ns + j) + 1) with (pcm + (3 * (c * ns + j) + 1)) by ring;
      apply (RSHC (3 * (c * ns + j) + 1)); lia
    | eapply ExecF.rng_sub; [exact RC | lia | lia] |].
  intros y12b y15 y19b y22 Ey22.
  (* +0x1a8 .. +0x1bc *)
  eapply bcl3_F with (A := pcm + 3 * (c * ns + j) + 2) (Dd := pcm + 3 * (c * ns + j)) (k := k2)
    (b1 := pb (3 * (c * ns + j) + 1)); [fct | lia | exact M2 | exact S2 | exact Ey22 | exact MD1
    | replace (pcm + 3 * (c * ns + j) + 2) with (pcm + (3 * (c * ns + j) + 2)) by ring;
      apply (RSHC (3 * (c * ns + j) + 2)); lia
    | eapply ExecF.rng_sub; [exact RC | lia | lia] |].
  intros y15b y19c.
  (* +0x1bc bltu a0,ra ; +0x1c0 beqz a0 ; +0x1c4 bnez a7 (the UBSan traps of the planes store: not taken) *)
  cstep. takeF false. step. takeF false. step. takeF false.
  (* +0x1c8 .. +0x1dc *)
  eapply bcl4_F with (A := P + 4 * (c * ns + j)) (Dd := pcm + 3 * (c * ns + j)) (k := kP)
    (b2 := pb (3 * (c * ns + j) + 2)); [exact Ha0 | lia | exact MP | exact SP | exact Ey22 | exact MD2
    | apply (RSHP (4 * (c * ns + j))); lia
    | eapply ExecF.rng_sub; [exact RC | lia | lia] |].
  intros y15c y19d.
  (* +0x1dc .. +0x200 : combine the three bytes, convert *)
  cstep. do 9 step.
  match goal with |- ExecF.evtF _ _ _ (MS _ _ _ ?fce _ _ _) =>
    assert (FRMc : frm0 fce) by (first [ assumption | apply frm0_accrue; exact Hfx ]) end.
  (* +0x204 fmul ; +0x208 fsw ; +0x20c addi ; the store's 4-byte range *)
  assert (RW4 : ExecF.rng RNG (P + 4 * (c * ns + j)) 4) by (eapply ExecF.rng_sub; [exact RP | lia | lia]).
  do 3 step.
  apply K; [fct | fct | fct | first [ assumption | apply frm0_accrue; exact FRMc ] |].
  eapply crt_inv_P; [exact Hinv | lia | lia | fct |].
  unfold PCC.cv. apply PCC.conv_bytes; [exact H5 | exact (PCC.comb _ _ _ t3 Ht3)].
Qed.

(* The inner loop CRT_ILOOP .. CRT_AT 0x210, run to its exit at CRT_LOOP_TAIL (b04a1406048 crt_loopF.v:391-432). *)
Lemma crt_inner_F : forall (G : machine_state -> Prop) c (ra s0 a3 a4 s4 s9 s11 : word),
  0 <= c < nch ->
  bv_unsigned ra = P + 4 * (c * ns) ->
  bv_unsigned a3 = 3 * (c * ns) ->
  bv_unsigned s4 = pcm + 3 * (c * ns) ->
  bv_unsigned s9 = pcm + 3 * (c * ns) ->
  (forall (s1' a0' a1' a2' a5' s3' s6' s7' s10' : word) (fx' : bv 32) (m' : word -> option byte)
          (Fh : bvmap 5 word),
     unbox_s (reg_get Fh (Z_to_bv 5 15)) = Z_to_bv 32 F2M23 ->
     frm0 fx' -> crt_inv m' ((c + 1) * ns) (c + 1) ->
     ExecF.evtF rsegs RNG G (ST CRT_LOOP_TAIL ra s0 s1' a0' a1' a2' a3 a4 a5' s3' s4 s6' s7' s9 s10' s11 Fh fx' m')) ->
  forall n j (s1 a0 a1 a2 a5 s3 s6 s7 s10 : word) (Fh : bvmap 5 word) (fx : bv 32) (m : word -> option byte),
  0 <= j -> j + Z.of_nat (S n) = ns ->
  bv_unsigned s1 = 3 * j ->
  bv_unsigned a0 = P + 4 * (c * ns + j) ->
  bv_unsigned s10 = P + 4 * (c * ns + j) ->
  unbox_s (reg_get Fh (Z_to_bv 5 15)) = Z_to_bv 32 F2M23 ->
  frm0 fx -> crt_inv m (c * ns + j) (c + 1) ->
  ExecF.evtF rsegs RNG G (ST CRT_ILOOP ra s0 s1 a0 a1 a2 a3 a4 a5 s3 s4 s6 s7 s9 s10 s11 Fh fx m).
Proof.
  intros G c ra s0 a3 a4 s4 s9 s11 Hc Hra Ha3 Hs4 Hs9 K n.
  induction n as [|n IH]; intros j s1 a0 a1 a2 a5 s3 s6 s7 s10 Fh fx m Hj0 Hjn Hs1 Ha0 Hs10 H5 Hfx Hinv.
  - apply (crt_body_F G c j ra s0 s1 a0 a1 a2 a3 a4 a5 s3 s4 s6 s7 s9 s10 s11 Fh fx m);
      try assumption; [lia|].
    intros s1' a0' a1' a2' a5' s3' s6' s7' s10' v fx' m' Hs1' Ha0' Hs10' Hfx' Hinv'.
    (* +0x210 bne t6,s1 : the last sample, not taken ; +0x214 j CRT_LOOP_TAIL *)
    cstep. takeF false. step.
    assert (Hub : unbox_s (reg_get (bvmap_set (Z_to_bv 5 14) v Fh) (Z_to_bv 5 15)) = Z_to_bv 32 F2M23)
      by (rewrite freg_get_other by reflexivity; exact H5).
    apply K with (Fh := bvmap_set (Z_to_bv 5 14) v Fh); [exact Hub | exact Hfx' |].
    replace ((c + 1) * ns) with (c * ns + j + 1) by lia. exact Hinv'.
  - apply (crt_body_F G c j ra s0 s1 a0 a1 a2 a3 a4 a5 s3 s4 s6 s7 s9 s10 s11 Fh fx m);
      try assumption; [lia|].
    intros s1' a0' a1' a2' a5' s3' s6' s7' s10' v fx' m' Hs1' Ha0' Hs10' Hfx' Hinv'.
    (* +0x210 bne t6,s1 : taken, back to CRT_ILOOP *)
    cstep. takeF true.
    assert (Hub : unbox_s (reg_get (bvmap_set (Z_to_bv 5 14) v Fh) (Z_to_bv 5 15)) = Z_to_bv 32 F2M23)
      by (rewrite freg_get_other by reflexivity; exact H5).
    apply (IH (j + 1) s1' a0' a1' a2' a5' s3' s6' s7' s10' (bvmap_set (Z_to_bv 5 14) v Fh) fx' m');
      [lia | lia | rewrite Hs1'; ring | rewrite Ha0'; f_equal; ring | rewrite Hs10'; f_equal; ring
       | exact Hub | exact Hfx' | ].
    replace (c * ns + (j + 1)) with (c * ns + j + 1) by ring. exact Hinv'.
Qed.

(* The outer loop CRT_LOOP_IN .. CRT_LOOP_TAIL, run to its exit at CRT_LOOP_OUT (b04a1406048 crt_loopF.v:434-525). *)
Lemma crt_outer_F : forall (G : machine_state -> Prop) n c (ra s0 s1 a0 a1 a2 a3 a4 a5 s3 s4 s6 s7 s9 s10 s11 : word)
    (Fh : bvmap 5 word) (fx : bv 32) (m : word -> option byte),
  0 <= c -> c + Z.of_nat (S n) = nch ->
  bv_unsigned a4 = c ->
  bv_unsigned a3 = 3 * (c * ns) ->
  bv_unsigned s0 = P + 4 * (c * ns) ->
  bv_unsigned s11 = P + 4 * (c * ns) ->
  bv_unsigned s4 = pcm + 3 * (c * ns) ->
  bv_unsigned s9 = pcm + 3 * (c * ns) ->
  unbox_s (reg_get Fh (Z_to_bv 5 15)) = Z_to_bv 32 F2M23 ->
  frm0 fx -> crt_inv m (c * ns) c ->
  (forall (ra' s0' s1' a0' a1' a2' a3' a4' a5' s3' s4' s6' s7' s9' s10' s11' : word)
          (Fh' : bvmap 5 word) (fx' : bv 32) (m' : word -> option byte),
     frm0 fx' -> crt_inv m' (nch * ns) nch ->
     ExecF.evtF rsegs RNG G (ST CRT_LOOP_OUT ra' s0' s1' a0' a1' a2' a3' a4' a5' s3' s4' s6' s7' s9' s10' s11' Fh' fx' m')) ->
  ExecF.evtF rsegs RNG G (ST CRT_LOOP_IN ra s0 s1 a0 a1 a2 a3 a4 a5 s3 s4 s6 s7 s9 s10 s11 Fh fx m).
Proof.
  intros G n. induction n as [|n IH];
    intros c ra s0 s1 a0 a1 a2 a3 a4 a5 s3 s4 s6 s7 s9 s10 s11 Fh fx m
      Hc0 Hcn Ha4 Ha3 Hs0 Hs11 Hs4 Hs9 H5 Hfx Hinv K.
  all: assert (Hc : 0 <= c < nch) by lia.
  all: pose proof crt_nn as (NN0 & NN1).
  all: pose proof crt_bnd as (BP0 & BP1 & BQ0 & BQ1 & BC0 & BC1).
  all: unfold APPMEM_END in BP1, BQ1, BC1.
  all: assert (B0 : 0 <= c * ns) by (apply Z.mul_nonneg_nonneg; lia).
  all: assert (B1 : c * ns + ns <= nch * ns)
         by (replace (c * ns + ns) with ((c + 1) * ns) by ring; apply Z.mul_le_mono_nonneg_r; lia).
  (* the frame range's bounds and the range of the 8-byte store at Q + 8c *)
  all: pose proof (ExecF.rng_bounds _ _ _ RFR) as RFRb.
  all: assert (RQ8 : ExecF.rng RNG (Q + 8 * c) 8) by (eapply ExecF.rng_sub; [exact RQ | lia | lia]).
  all: pose proof Hinv as HI.
  all: destruct Hinv as (MU & WM & PR & FR & HPd & HQd).
  all: destruct (crt_sh_Q8 m _ _ (Q + 8 * c) c HI Hc eq_refl) as (kq & MQ & SQ).
  (* +0x10c mul a0,a4,s2 ; +0x110 slli ra,a0,2 *)
  all: cstep. all: step.
  (* +0x114 ld a1,32(sp) *)
  all: step.
  (* +0x118 bltu a1,ra : the planes pointer-overflow trap, not taken *)
  all: step; takeF false.
  (* +0x11c add a0,a0,t5 ; +0x120 srli a0,a0,0x3e *)
  all: do 2 step.
  (* +0x124 bnez a0 : trap not taken *)
  all: step; takeF false.
  (* +0x128 slli a0,a4,3 ; +0x12c add a0,s5,a0 : a0 = Q + 8c *)
  all: do 2 step.
  (* +0x130 beqz a0 ; +0x134 bltu a0,s5 ; +0x138 bnez t0 : not taken *)
  all: step; takeF false.
  all: step; takeF false.
  all: step; takeF false.
  (* +0x13c .. +0x14c : the shadow byte of planar[c] *)
  all: eapply bcq8_F with (A := Q + 8 * c) (k := kq);
         [ fct | lia | exact MQ | exact SQ | apply (RSHQ (8 * c)); lia | ].
  all: intros y11.
  (* +0x14c ld a1,48(sp) ; +0x150 add ra,a1,ra : ra = P + 4cns *)
  all: cstep.
  all: step.
  all: pose proof (crt_stQ m _ _ (Z_to_bv 64 (Q + 8 * c)) c HI ltac:(lia) ltac:(apply unsigned_lit; lia)) as HSq.
  (* +0x154 sd ra,0(a0) : planar[c] := P + 4cns *)
  all: step.
  all: match goal with
       | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mw ?addr ?bs) _) =>
           assert (HIQ : crt_inv (write_to_mem mw addr bs) (c * ns) (c + 1))
             by (eapply crt_inv_Q; [exact HI | lia | lia | fct | reflexivity | fct])
       end.
  (* +0x158 blez s2 ; +0x15c li s1,0 ; +0x160 mv s10,s0 ; +0x164 mv a0,s11 *)
  all: step; takeF false.
  all: do 3 step.
  all: eapply (crt_inner_F G c) with (n := Z.to_nat (ns - 1)) (j := 0);
         [ exact Hc | fct | exact Ha3 | exact Hs4 | exact Hs9 | | lia
          | rewrite Nat2Z.inj_succ, Z2Nat.id by lia; lia
          | fct | fct | fct | exact H5 | assumption
          | replace (c * ns + 0) with (c * ns) by ring; exact HIQ ].
  - (* last channel: +0x24c .. +0x268, the bne not taken, fall through to CRT_LOOP_OUT *)
    intros s1' a0' a1' a2' a5' s3' s6' s7' s10' fx' m' Fh' H5' Hfx' Hinv'.
    pose proof Hinv' as HIe. unfold crt_inv in Hinv'.
    destruct Hinv' as (MU' & WM' & PR' & FR' & HPd' & HQd').
    cstep. do 6 step. step; takeF false.
    apply K; [exact Hfx' |].
    replace nch with (c + 1) by lia. exact HIe.
  - (* next channel: the bne taken, back to CRT_LOOP_IN *)
    intros s1' a0' a1' a2' a5' s3' s6' s7' s10' fx' m' Fh' H5' Hfx' Hinv'.
    pose proof Hinv' as HIe. unfold crt_inv in Hinv'.
    destruct Hinv' as (MU' & WM' & PR' & FR' & HPd' & HQd').
    cstep. do 6 step. step; takeF true.
    apply (IH (c + 1)); [ lia | lia | fct | fct | fct | fct | fct | fct | exact H5' | exact Hfx' | | ].
    + replace ((c + 1) * ns) with (c * ns + ns) by ring.
      replace ((c + 1) * ns) with (c * ns + ns) in HIe by ring. exact HIe.
    + intros ra2 s02 s12 a02 a12 a22 a32 a42 a52 s32 s42 s62 s72 s92 s102 s112 Fh2 fx2 m2 Hfx2 Hinv2.
      apply K; assumption.
Qed.

(* The two loops from CRT_LOOP_IN at channel 0 to CRT_LOOP_OUT, with the invariant's content at the exit
   (crt_outer_F at c = 0 from the empty invariant, as dc455613c81 crt_convert.v:658-668 starts it). *)
Lemma crtB_loop_run : forall (ra s0 s1 a0 a1 a2 a3 a4 a5 s3 s4 s6 s7 s9 s10 s11 : word) (Fh : bvmap 5 word)
    (fc : bv 32),
  bv_unsigned a3 = 0 -> bv_unsigned a4 = 0 -> bv_unsigned s0 = P -> bv_unsigned s11 = P ->
  bv_unsigned s4 = pcm -> bv_unsigned s9 = pcm ->
  unbox_s (reg_get Fh (Z_to_bv 5 15)) = Z_to_bv 32 F2M23 -> frm0 fc ->
  rw_cells rsegs m0 (bv_unsigned wsp) FRAME ->
  ExecF.evtF rsegs RNG
    (fun ms => exists (ra' s0' s1' a0' a1' a2' a3' a4' a5' s3' s4' s6' s7' s9' s10' s11' : word)
                      (Fh' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
       ms = ST CRT_LOOP_OUT ra' s0' s1' a0' a1' a2' a3' a4' a5' s3' s4' s6' s7' s9' s10' s11' Fh' fc' m' /\
       frm0 fc' /\ munch (crtB_W sp P Q nch ns) m0 m' /\ (forall x, m0 x <> None -> m' x <> None) /\
       rw_cells rsegs m' (bv_unsigned wsp) FRAME /\
       (forall j, 0 <= j < nch * ns -> bytes_at rsegs m' (P + 4 * j) (Z_to_le_bytes 4 (PCC.cv pb j))) /\
       (forall c, 0 <= c < nch -> bytes_at rsegs m' (Q + 8 * c) (le8 (Z_to_bv 64 (P + 4 * (c * ns))))))
    (ST CRT_LOOP_IN ra s0 s1 a0 a1 a2 a3 a4 a5 s3 s4 s6 s7 s9 s10 s11 Fh fc m0).
Proof using All.
  intros ra s0 s1 a0 a1 a2 a3 a4 a5 s3 s4 s6 s7 s9 s10 s11 Fh fc Ha3 Ha4 Hs0 Hs11 Hs4 Hs9 H5 Hfc FR.
  eapply (crt_outer_F _ (Z.to_nat (nch - 1)) 0);
    [ lia | rewrite Nat2Z.inj_succ, Z2Nat.id by lia; lia | exact Ha4 | rewrite Ha3; ring
    | rewrite Hs0; ring | rewrite Hs11; ring | rewrite Hs4; ring | rewrite Hs9; ring | exact H5 | exact Hfc
    | | ].
  - replace (0 * ns) with 0 by ring. unfold crt_inv.
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [intros x Hx; exact Hx|].
    split; [exact FR|]. split; intros; exfalso; lia.
  - intros ra' s0' s1' a0' a1' a2' a3' a4' a5' s3' s4' s6' s7' s9' s10' s11' Fh' fc' m' Hfc' Hinv'.
    apply evtF_done.
    destruct Hinv' as (MU' & WM' & PR' & FR' & HPd' & HQd').
    exists ra', s0', s1', a0', a1', a2', a3', a4', a5', s3', s4', s6', s7', s9', s10', s11', Fh', fc', m'.
    split; [reflexivity|]. split; [exact Hfc'|]. split; [exact MU'|]. split; [exact PR'|].
    split; [exact FR'|]. split; [exact HPd' | exact HQd'].
Qed.
End LoopsF.

(* ======================================================================================================== *)
(* Part 2: the cut contract at CRT_LOOP_IN from the one at CRT_LOOP_OUT                                      *)
(* ======================================================================================================== *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YCbq YC5d YGCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YG0v YK1b YI04 YP09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import check_round_trip_cg crtB_cuts crtB_glue.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require LeafCgKit crtB_walk.

Section CrtLoop.
Context {rc : YM05.RunCeil}.
Local Notation segs := decodesegsB0.
Variable B : asyms.
Variable MT : ameter_ops.
Variable RO_RD : list (Z * Z).

(* ---- small facts ---- *)

Lemma crtB_req_pos : forall n, 0 < n -> req_size n = n.
Proof. intros n Hn. unfold req_size. destruct (n =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity]. Qed.

Lemma crtB_req_ge : forall n, n <= req_size n.
Proof. intros n. unfold req_size. destruct (n =? 0) eqn:E; [apply Z.eqb_eq in E; lia | lia]. Qed.

Lemma crtB_byte_signed_small : forall b : byte, 0 <= bv_unsigned b < 128 -> bv_signed b = bv_unsigned b.
Proof.
  intros b Hb. unfold bv_signed, bv_swrap, bv_wrap. change (bv_half_modulus 8) with 128.
  change (bv_modulus 8) with 256. rewrite Z.mod_small by lia. lia.
Qed.

Lemma crtB_u8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hz.
Qed.

(* A byte cgif's view sees outside the image is present in the memory and not hidden. *)
Lemma crtB_aview_some : forall (H : word -> bool) (mem : word -> option byte) s v,
  0 <= s < 2 ^ 64 -> ~ in_img segs s -> aview segs H mem s = Some v ->
  H (Z_to_bv 64 s) = false /\ exists b, mem (Z_to_bv 64 s) = Some b /\ bv_unsigned b = v.
Proof.
  intros H mem s v Hs Hn Hv.
  destruct (aview_byte segs H mem s v Hv) as (b & Hb & -> & _).
  pose proof (seg_rom_none segs s Hs Hn) as Er.
  unfold YP09.mbyte, mrestrict in Hb. cbv beta in Hb.
  revert Hb. destruct (H (Z_to_bv 64 s)) eqn:EH; intros Hb.
  - rewrite Er in Hb. cbn in Hb. discriminate.
  - split; [reflexivity|]. revert Hb. destruct (mem (Z_to_bv 64 s)) as [b'|] eqn:Em; intros Hb.
    + cbn in Hb. injection Hb as ->. exists b. split; reflexivity.
    + rewrite Er in Hb. cbn in Hb. discriminate.
Qed.

(* cgif's view at a byte depends on that byte of the memory only. *)
Lemma crtB_aview_same : forall (H : word -> bool) (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> aview segs H m' a = aview segs H m a.
Proof. intros H m m' a E. unfold aview, YP09.mbyte, mrestrict. cbv beta. rewrite E. reflexivity. Qed.

(* Two blocks of a permutation of the live blocks are apart (YCbq.v:2586 sep_blocks_perm at any position). *)
Lemma crtB_sep_in : forall ly S (W : world segs) mem md x y L,
  AR_laws segs B -> AR segs B ly S W mem md ->
  Permutation (ablocks B ly S) (x :: L) -> In y L -> zdisjoint (block_rng x) (block_rng y).
Proof.
  intros ly S W mem md x y L LAWS HAR HP Hy. apply in_split in Hy as (l1 & l2 & ->).
  apply (sep_blocks_perm segs B LAWS ly S W mem md x y (l1 ++ l2) HAR).
  eapply Permutation_trans; [exact HP|]. apply perm_skip. apply Permutation_sym. apply Permutation_middle.
Qed.

(* ---- the shadow of a live block, read in decode's form (YG0d.v:430 AR_shadow_law, YG0v.v:37 block_shadow) ---- *)

(* The shadow byte of a byte a of a live block: visible, present, and saying a is addressable (decode's
   AsanCells.shadow_ok: 0, or the partial last granule's size with a below it). *)
Lemma crtB_shadow_byte : forall ly S (W : world segs) mem md p n a,
  AR_laws segs B -> AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) -> p <= a < p + req_size n ->
  w_H W (Z_to_bv 64 (AsanCells.shadow_addr a)) = false /\
  exists b, mem (Z_to_bv 64 (AsanCells.shadow_addr a)) = Some b /\ AsanCells.shadow_ok a (bv_signed b).
Proof.
  intros ly S W mem md p n a LAWS HAR Hin Ha.
  destruct (al_shadow _ _ LAWS ly S W mem md p n HAR Hin) as ((Hp8 & HN0 & HS) & _).
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (Hp16 & Hp4096 & Hpc & Happ & _).
  pose proof asan_consts as (C1 & _ & _ & _ & C5).
  set (N := req_size n) in *.
  assert (HNp : 0 < N) by lia.
  assert (Hg : 0 <= (a - p) / 8 < (N + 7) / 8) by (Z.div_mod_to_equations; lia).
  specialize (HS _ Hg).
  assert (Es : YG0v.shadow_of_addr SHADOW_OFF p + (a - p) / 8 = AsanCells.shadow_addr a).
  { unfold YG0v.shadow_of_addr, AsanCells.shadow_addr, SHADOW_OFF, ASAN_K. Z.div_mod_to_equations. lia. }
  rewrite Es in HS.
  assert (Hsa : 0 <= AsanCells.shadow_addr a < 2 ^ 64)
    by (unfold AsanCells.shadow_addr, ASAN_K; Z.div_mod_to_equations; lia).
  assert (Hni : ~ in_img segs (AsanCells.shadow_addr a)).
  { intros Hi. pose proof (crtB_segs_low _ Hi) as Hl. rewrite C5 in Hl.
    unfold AsanCells.shadow_addr, ASAN_K in Hl. Z.div_mod_to_equations. lia. }
  destruct (crtB_aview_some (w_H W) mem _ _ Hsa Hni HS) as (Hh & b & Hb & Ev).
  split; [exact Hh|]. exists b. split; [exact Hb|].
  assert (Hv7 : 0 <= (if (a - p) / 8 <? N / 8 then 0 else N mod 8) < 8)
    by (destruct ((a - p) / 8 <? N / 8); [lia | apply Z.mod_pos_bound; lia]).
  unfold AsanCells.shadow_ok.
  rewrite (crtB_byte_signed_small b) by (rewrite Ev; lia). rewrite Ev.
  destruct ((a - p) / 8 <? N / 8) eqn:Eg; [left; reflexivity|].
  apply Z.ltb_ge in Eg.
  destruct (Z.eq_dec (N mod 8) 0) as [Z0|NZ]; [left; exact Z0|right].
  split; [|lia]. Z.div_mod_to_equations. lia.
Qed.

(* A window of a live block is addressable in decode's form (AsanCells.addressable). *)
Lemma crtB_addressable : forall ly S (W : world segs) mem md p n x len,
  AR_laws segs B -> AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  p <= x -> 0 <= len -> x + len <= p + req_size n -> addressable mem x len.
Proof.
  intros ly S W mem md p n x len LAWS HAR Hin Hx Hl Hxl.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (Hp16 & Hp4096 & Hpc & Happ & _).
  pose proof asan_consts as (C1 & _).
  unfold addressable. split; [lia|]. split; [exact Hl|].
  split; [unfold APPMEM_END; lia|].
  intros i Hi. unfold addr_byte. split.
  - unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. lia.
  - destruct (crtB_shadow_byte ly S W mem md p n (x + i) LAWS HAR Hin ltac:(lia)) as (_ & b & Hb & Hok).
    exists b. split; [unfold mrd, wa; rewrite Hb; reflexivity | exact Hok].
Qed.

(* The shadow byte of every byte of a window of a live block is inside the run's footprint. *)
Lemma crtB_rng_shadow : forall ly S (W : world segs) mem md p n x len,
  AR_laws segs B -> AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  p <= x -> x + len <= p + req_size n ->
  forall i, 0 <= i < len ->
    ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) (AsanCells.shadow_addr (x + i)) 1.
Proof.
  intros ly S W mem md p n x len LAWS HAR Hin Hx Hxl i Hi.
  destruct (crtB_shadow_byte ly S W mem md p n (x + i) LAWS HAR Hin ltac:(lia)) as (Hh & _).
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (Hp16 & Hp4096 & Hpc & _).
  pose proof asan_consts as (C1 & _).
  apply crtB_rng_of_vis.
  - unfold AsanCells.shadow_addr, ASAN_K. Z.div_mod_to_equations. lia.
  - unfold AsanCells.shadow_addr, ASAN_K. Z.div_mod_to_equations. lia.
  - intros a Ha. replace a with (AsanCells.shadow_addr (x + i)) by lia. exact Hh.
Qed.

(* ---- the float the loop writes, read at the entry reader ---- *)

Lemma crtB_pb_range : forall (H : word -> bool) mem pcm i, 0 <= crtB_pb (aview segs H mem) pcm i < 256.
Proof.
  intros H mem pcm i. unfold crtB_pb.
  destruct (aview segs H mem (pcm + i)) as [v|] eqn:E; [|lia].
  destruct (aview_byte segs H mem (pcm + i) v E) as (b & _ & _ & Hr). exact Hr.
Qed.

(* lib/Prog/crt_convert.v's cv over the bytes of the entry reader is crtB_cuts' crtB_cv. *)
Lemma crtB_cv_eq : forall (H : word -> bool) mem pcm j,
  PCC.cv (fun i => Z_to_bv 8 (crtB_pb (aview segs H mem) pcm i)) j = crtB_cv (aview segs H mem) pcm j.
Proof.
  intros H mem pcm j. unfold PCC.cv, crtB_cv, PCC.s24, crtB_s24.
  rewrite !crtB_u8 by apply crtB_pb_range. reflexivity.
Qed.

(* ---- the stage ---- *)

Theorem crtB_loop : crtB_loop_stmt B MT RO_RD.
Proof.
  intros RULES HOUT.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs audio pcm nch ns bA nA bP nP T ch
    ly1 S1 W1 mem1 md1 regs1 P Q R fx1 v0 HPRE HMID HREGS
    H5 H6 H7 H16 H17 H28 H29 H30 H31 H13 H14 H8 H27 H20 H25 HFRM HF15 HFR HBL.
  pose proof RULES as (_ & _ & _ & LAWS & _).
  pose proof HPRE as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HN & HNS & HB3 & _ & _ & _ &
    HinP & HbP & HpP & _).
  pose proof HMID as (HJ & Hfrs1 & Hmo1 & HROM1).
  pose proof HJ as (HAR1 & _ & _ & _ & _ & _ & _ & _ & _ & J2 & _ & _ & _ & Jpres & Hstk & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof HREGS as (R2 & R3 & R4 & R18 & R21 & R24).
  pose proof HBL as (HPerm & HP0 & HQ0 & HR0).
  pose proof asan_consts as (C1 & _ & _ & _ & C5).
  assert (HDS : DEC_CRT_STK = 16544) by reflexivity.
  assert (NN : 0 < nch * ns /\ nch * ns <= 480) by (split; [apply Z.mul_pos_pos|]; nia).
  destruct NN as (NN0 & NN1).
  (* the three blocks and the pcm block at the loop's state *)
  set (Pb := (P, 4 * (nch * ns))). set (Qb := (Q, 8 * nch)). set (Rb := (R, 3 * (nch * ns))).
  assert (HinP1 : In Pb (ablocks B ly1 S1))
    by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | right; right; left; reflexivity]).
  assert (HinQ1 : In Qb (ablocks B ly1 S1))
    by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | right; left; reflexivity]).
  assert (HinB1 : In (bP, nP) (ablocks B ly1 S1))
    by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | right; right; right; exact HinP]).
  assert (HPermP : Permutation (ablocks B ly1 S1) (Pb :: Rb :: Qb :: ablocks B lyc Sc)).
  { eapply Permutation_trans; [exact HPerm|].
    eapply Permutation_trans; [apply perm_skip; apply perm_swap|]. apply perm_swap. }
  assert (HPermQ : Permutation (ablocks B ly1 S1) (Qb :: Rb :: Pb :: ablocks B lyc Sc)).
  { eapply Permutation_trans; [exact HPerm|]. apply perm_swap. }
  pose proof (crtB_sep_in _ _ _ _ _ _ _ _ LAWS HAR1 HPermP ltac:(right; left; reflexivity)) as DPQ0.
  pose proof (crtB_sep_in _ _ _ _ _ _ _ _ LAWS HAR1 HPermP ltac:(right; right; exact HinP)) as DPB0.
  pose proof (crtB_sep_in _ _ _ _ _ _ _ _ LAWS HAR1 HPermQ ltac:(right; right; exact HinP)) as DQB0.
  assert (NPc : ~ In Pb (ablocks B lyc Sc)).
  { intros Hc. pose proof (crtB_sep_in _ _ _ _ _ _ _ _ LAWS HAR1 HPermP ltac:(right; right; exact Hc)) as D.
    unfold zdisjoint, block_rng, Pb in D. cbn [fst snd] in D. rewrite crtB_req_pos in D by nia. lia. }
  assert (NQc : ~ In Qb (ablocks B lyc Sc)).
  { intros Hc. pose proof (crtB_sep_in _ _ _ _ _ _ _ _ LAWS HAR1 HPermQ ltac:(right; right; exact Hc)) as D.
    unfold zdisjoint, block_rng, Qb in D. cbn [fst snd] in D. rewrite crtB_req_pos in D by lia. lia. }
  unfold zdisjoint, block_rng, Pb, Qb in DPQ0, DPB0, DQB0. cbn [fst snd] in DPQ0, DPB0, DQB0.
  rewrite crtB_req_pos in DPQ0, DPB0 by nia. rewrite crtB_req_pos in DPQ0, DQB0 by lia.
  pose proof (crtB_req_ge nP) as HnP.
  destruct (al_blocks _ _ LAWS ly1 S1 W1 mem1 md1 _ _ HAR1 HinP1) as (HP16 & HP4096 & HPc & _ & HPpres & _).
  destruct (al_blocks _ _ LAWS ly1 S1 W1 mem1 md1 _ _ HAR1 HinQ1) as (HQ16 & HQ4096 & HQc & _ & HQpres & _).
  destruct (al_blocks _ _ LAWS ly1 S1 W1 mem1 md1 _ _ HAR1 HinB1) as (_ & HB4096 & HBc & _ & HBpres & _).
  rewrite crtB_req_pos in HPc, HPpres by nia. rewrite crtB_req_pos in HQc, HQpres by lia.
  (* the frame window [spZ regs - CRT_FRAME, spZ regs) of the inner journal's stack *)
  assert (Hsp' : bv_unsigned (YK11.getr regs1 (Z_to_bv 5 2)) = spZ regs - CRT_FRAME).
  { rewrite (R2 : YK11.getr regs1 (Z_to_bv 5 2) = w64 (spZ regs - CRT_FRAME)). apply unsigned_lit.
    unfold CRT_FRAME. lia. }
  (* the run: the loop from the cut's configuration *)
  set (pb := fun i => Z_to_bv 8 (crtB_pb (aview segs (w_H W) memc) pcm i)).
  eapply (@crtB_walk.crtB_run fx1 W1 regs1 mem1 md1 CRT_LOOP_IN).
  - unfold LCK.ms_of_regs.
    rewrite (R24 : YK11.getr regs1 (Z_to_bv 5 24) = Z_to_bv 64 ASAN_K).
    assert (Ureg : forall (r : Z) (v : Z), YK11.getr regs1 (Z_to_bv 5 r) = w64 v -> 0 <= v < 2 ^ 64 ->
              bv_unsigned (YK11.getr regs1 (Z_to_bv 5 r)) = v).
    { intros r v E Hv. rewrite E. apply unsigned_lit. exact Hv. }
    eapply (crtB_loop_run
      (YK11.getr regs1 (Z_to_bv 5 2)) (YK11.getr regs1 (Z_to_bv 5 3)) (YK11.getr regs1 (Z_to_bv 5 4))
      (YK11.getr regs1 (Z_to_bv 5 5)) (YK11.getr regs1 (Z_to_bv 5 6)) (YK11.getr regs1 (Z_to_bv 5 7))
      (YK11.getr regs1 (Z_to_bv 5 16)) (YK11.getr regs1 (Z_to_bv 5 17)) (YK11.getr regs1 (Z_to_bv 5 18))
      (YK11.getr regs1 (Z_to_bv 5 21)) (YK11.getr regs1 (Z_to_bv 5 28)) (YK11.getr regs1 (Z_to_bv 5 29))
      (YK11.getr regs1 (Z_to_bv 5 30)) (YK11.getr regs1 (Z_to_bv 5 31))
      mem1 pb (spZ regs - CRT_FRAME) pcm nch ns P Q
      v0 (w64 R) (w64 (3 * (nch * ns))) (w64 audio) (w64 (2 ^ 64 - 1 - P))
      (YKK.getr regs 1) (YKK.getr regs 8) (YKK.getr regs 9) (YKK.getr regs 18) (YKK.getr regs 19)
      (YKK.getr regs 20) (YKK.getr regs 21) (YKK.getr regs 22) (YKK.getr regs 23) (YKK.getr regs 24)
      (YKK.getr regs 25) (YKK.getr regs 26) (YKK.getr regs 27)
      (LCK.RNG_W (world segs) (@w_H segs) W1)).
    (* HN HNS HB *)
    + exact HN.
    + exact HNS.
    + exact HB3.
    (* HS0 HS1: the frame is in the high application memory *)
    + unfold HIGHMEM_BEG, CRT_FRAME. rewrite HDS in Hslo. lia.
    + unfold APPMEM_END, CRT_FRAME. lia.
    (* HP0 HP4 HQ0 HQ8 *)
    + exact HP0.
    + clear - HP16. Z.div_mod_to_equations. lia.
    + exact HQ0.
    + clear - HQ16. Z.div_mod_to_equations. lia.
    (* DPQ DPC DQC DPS DQS DCS *)
    + lia.
    + lia.
    + lia.
    + left. unfold CRT_FRAME. rewrite HDS in Hslo. lia.
    + left. unfold CRT_FRAME. rewrite HDS in Hslo. lia.
    + left. unfold CRT_FRAME. rewrite HDS in Hslo. lia.
    (* PB: the pcm bytes at the loop's state are the entry reader's *)
    + intros i Hi.
      destruct (HBpres (pcm + i) ltac:(lia)) as ((Hh & b & Hb) & _).
      assert (Hk : aview segs (w_H W1) mem1 (bP + (pcm + i - bP)) = aview segs (w_H W) memc (bP + (pcm + i - bP)))
        by (apply (J2 bP nP (pcm + i - bP)); [exact HinP | exact HinB1 | lia | apply YI04.inFP_nil]).
      replace (bP + (pcm + i - bP)) with (pcm + i) in Hk by ring.
      assert (Hv : aview segs (w_H W1) mem1 (pcm + i) = Some (bv_unsigned b))
        by (unfold aview, YP09.mbyte, mrestrict; cbv beta; rewrite Hh, Hb; reflexivity).
      unfold mrd, wa. rewrite Hb. f_equal. unfold pb, crtB_pb. rewrite <- Hk, Hv.
      symmetry. apply bv_eq. rewrite crtB_u8; [reflexivity|].
      pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr. exact Hr.
    (* APC WP AP WQ AQ *)
    + apply (crtB_addressable ly1 S1 W1 mem1 md1 bP nP pcm (3 * nch * ns) LAWS HAR1 HinB1); lia.
    + apply (crtB_wr_at_of (w_H W1) mem1 P (4 * nch * ns)); [lia | lia |].
      intros a Ha. exact (proj1 (HPpres a ltac:(lia))).
    + apply (crtB_addressable ly1 S1 W1 mem1 md1 P (4 * (nch * ns)) P (4 * nch * ns) LAWS HAR1 HinP1); [lia | lia|].
      rewrite crtB_req_pos by nia. lia.
    + apply (crtB_wr_at_of (w_H W1) mem1 Q (8 * nch)); [lia | lia |].
      intros a Ha. exact (proj1 (HQpres a ltac:(lia))).
    + apply (crtB_addressable ly1 S1 W1 mem1 md1 Q (8 * nch) Q (8 * nch) LAWS HAR1 HinQ1); [lia | lia|].
      rewrite crtB_req_pos by lia. lia.
    (* the registers *)
    + exact Hsp'.
    + apply Ureg; [exact H5 | lia].
    + apply Ureg; [exact H6 | lia].
    + apply Ureg; [exact H7 | lia].
    + rewrite (Ureg 16 (2 ^ 64 - 1 - pcm) H16) by lia. lia.
    + apply Ureg; [exact H17 | lia].
    + apply Ureg; [exact R18 | lia].
    + apply Ureg; [exact R21 | lia].
    + rewrite (Ureg 28 CRT_T3 H28) by (unfold CRT_T3; lia). unfold CRT_T3. lia.
    + apply Ureg; [exact H29 | lia].
    + rewrite (Ureg 30 CRT_T5 H30) by (unfold CRT_T5; lia). unfold CRT_T5. lia.
    + apply Ureg; [exact H31 | lia].
    + unfold w64. rewrite unsigned_lit by lia. lia.
    (* the footprint *)
    + apply (crtB_rng_of_apresent W1 mem1); [lia | lia |]. intros a Ha. exact (proj1 (HPpres a ltac:(lia))).
    + apply (crtB_rng_of_apresent W1 mem1); [lia | lia |]. intros a Ha. exact (proj1 (HQpres a ltac:(lia))).
    + apply (crtB_rng_of_apresent W1 mem1); [lia | lia |]. intros a Ha. exact (proj1 (HBpres a ltac:(lia))).
    + intros i Hi. apply (crtB_rng_shadow ly1 S1 W1 mem1 md1 P (4 * (nch * ns)) P (4 * nch * ns) LAWS HAR1 HinP1);
        [lia | rewrite crtB_req_pos by nia; lia | exact Hi].
    + intros i Hi. apply (crtB_rng_shadow ly1 S1 W1 mem1 md1 Q (8 * nch) Q (8 * nch) LAWS HAR1 HinQ1);
        [lia | rewrite crtB_req_pos by lia; lia | exact Hi].
    + intros i Hi. apply (crtB_rng_shadow ly1 S1 W1 mem1 md1 bP nP pcm (3 * nch * ns) LAWS HAR1 HinB1);
        [lia | lia | exact Hi].
    + apply (crtB_rng_of_apresent W1 mem1); [unfold CRT_FRAME; rewrite HDS in Hslo; lia | unfold CRT_FRAME; lia |].
      intros a Ha. apply Jpres. unfold CRT_FRAME in Ha. rewrite HDS. lia.
    (* the channel registers at channel 0, the float state, the frame *)
    + apply Ureg; [exact H13 | lia].
    + apply Ureg; [exact H14 | lia].
    + apply Ureg; [exact H8 | lia].
    + apply Ureg; [exact H27 | lia].
    + apply Ureg; [exact H20 | lia].
    + apply Ureg; [exact H25 | lia].
    + exact HF15.
    + exact HFRM.
    + rewrite Hsp'. exact HFR.
  - (* the loop's end: the loop-out cut *)
    intros ms' md' (ms0 & Hpost & Heqv) Hsbm.
    destruct Hpost as (ra' & s0' & s1' & a0' & a1' & a2' & a3' & a4' & a5' & s3' & s4' & s6' & s7' & s9' & s10' &
      s11' & Fh' & fc' & m' & -> & Hfc' & MU & PR & FR' & HPd & HQd).
    pose proof (@crtB_walk.crtB_ms_shape (YK11.mkFP Fh' fc') _ _ _ _ Heqv) as Eshape.
    rewrite Eshape.
    (* the bytes the loop may have changed *)
    set (Wr := fun a => P <= a < P + 4 * nch * ns \/ Q <= a < Q + 8 * nch \/
                        spZ regs - CRT_FRAME <= a < spZ regs - CRT_FRAME + 160).
    assert (HWo : forall a, ~ Wr a -> outside (crtB_W (spZ regs - CRT_FRAME) P Q nch ns) a).
    { intros a Ha. unfold crtB_W. cbn [outside].
      split; [intros E; apply Ha; left; exact E|].
      split; [intros E; apply Ha; right; left; exact E|].
      split; [intros E; apply Ha; right; right; exact E | exact I]. }
    apply (HOUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs audio pcm nch ns bA nA bP nP T ch
             ly1 S1 W1 m' md' (ms_regs ms') P Q R (YK11.mkFP Fh' fc') v0 (w64 (2 ^ 64 - 1 - P))).
    + exact HPRE.
    + split; [|split; [exact Hfrs1 | split; [exact Hmo1 |]]].
      * eapply (@ajournal_exec rc dec_B_sink_head segs B LAWS crtB_segs_low DEC_CRT_STK (spZ regs) [] lyc Sc W memc
                  mdc [] ly1 S1 W1 mem1 md1 3 m' md' Wr HJ).
        -- intros x Hx. unfold mrestrict. rewrite (MU x (HWo _ Hx)). reflexivity.
        -- intros x Hx. unfold mrestrict in *. revert Hx. destruct (w_H W1 x); intros Hx; [exact Hx | exact (PR x Hx)].
        -- intros x Hx. apply MU. apply HWo. intros HW.
           pose proof (u64_range x) as Rx.
           assert (Ex : Z_to_bv 64 (bv_unsigned x) = x) by apply Z_to_bv_bv_unsigned.
           destruct HW as [HW|[HW|HW]].
           ++ destruct (HPpres (bv_unsigned x) ltac:(lia)) as ((Hh & _) & _). rewrite Ex in Hh. congruence.
           ++ destruct (HQpres (bv_unsigned x) ltac:(lia)) as ((Hh & _) & _). rewrite Ex in Hh. congruence.
           ++ destruct (Jpres (bv_unsigned x) ltac:(unfold CRT_FRAME in HW; rewrite HDS; lia)) as (Hh & _).
              rewrite Ex in Hh. congruence.
        -- exact Hsbm.
        -- intros a [Ha|[Ha|Ha]].
           ++ right; right; left. exists P, (4 * (nch * ns)). split; [exact HinP1|]. split; [exact NPc|].
              rewrite crtB_req_pos by nia. lia.
           ++ right; right; left. exists Q, (8 * nch). split; [exact HinQ1|]. split; [exact NQc|].
              rewrite crtB_req_pos by lia. lia.
           ++ left. unfold CRT_FRAME in Ha. rewrite HDS. lia.
      * intros a Hro Hrom.
        assert (Hai : in_img segs a)
          by (destruct Hrom as (sg & Hin & _ & Hr); exists sg; split; [exact Hin | exact Hr]).
        pose proof (crtB_segs_low a Hai) as Hal. rewrite C5 in Hal.
        rewrite <- (HROM1 a Hro Hrom). apply crtB_aview_same. apply MU.
        rewrite unsigned_lit by lia. apply HWo. intros [HW|[HW|HW]].
        -- assert (Hd : exists p n, In (p, n) (ablocks B ly1 S1) /\ p <= a < p + req_size n).
           { exists P, (4 * (nch * ns)). split; [exact HinP1|]. rewrite crtB_req_pos by nia. lia. }
           exact (proj2 (al_client_img _ _ LAWS ly1 S1 W1 mem1 md1 a HAR1 (or_introl Hd)) Hai).
        -- assert (Hd : exists p n, In (p, n) (ablocks B ly1 S1) /\ p <= a < p + req_size n).
           { exists Q, (8 * nch). split; [exact HinQ1|]. rewrite crtB_req_pos by lia. lia. }
           exact (proj2 (al_client_img _ _ LAWS ly1 S1 W1 mem1 md1 a HAR1 (or_introl Hd)) Hai).
        -- unfold CRT_FRAME in HW. rewrite HDS in Hslo. lia.
    + unfold crtB_regs.
      split; [|split; [|split; [|split; [|split]]]];
        rewrite (crtB_walk.crtB_ms_reg _ _ _ _ _ _ _ ms' _ Heqv) by reflexivity.
      * exact R2.
      * exact R3.
      * exact R4.
      * exact R18.
      * exact R21.
      * reflexivity.
    + unfold crtB_frame. rewrite <- Hsp'. exact FR'.
    + exact HBL.
    + exact Hfc'.
    + split.
      * intros c Hc. exact (HQd c Hc).
      * intros j Hj. rewrite <- crtB_cv_eq. exact (HPd j Hj).
Qed.
End CrtLoop.

