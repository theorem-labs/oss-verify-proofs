From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import AsanKA AsanKAProof reac_frame_inspect_c reac_decode_c ReacDecodeLib reac_decode.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import reac_frame_inspect_F_c reac_frame_inspect_F reac_decode_F_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Footprint twin of reac_decode_holds (reac_decode.v). The proof follows reac_decode.v step for step, with StepF's
   step. The pure lemmas of reac_decode.v (bpre, INVD, SRC_rd, SRC_shr, DST_sho, ...) are used from there. Before each
   load of a shadow byte at h and of a data byte at w, the proof names the one-byte ranges [h, h+1) and [w, w+1), cut
   from the footprint premises, so that StepF's access check finds them. *)

Ltac st := step; nrm.

Ltac cnd b :=
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b; [cbv iota | symmetry; unfold bv_eqb, bv_ltu, bv_lts; usub; fold_lit_ux; solve_cond_rec]
  end.

Lemma bm1F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x18 + 4 = A ->
  A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 + 3 < bv_signed k) ->
  ExecF.rng RNG (A / 8 + 2147450880) 1 ->
  (forall y11 y12 y13 : word, ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y11 y12 y13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81804) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x817f0) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k A EA RA M SK RS CONT.
  pose proof (u64_range x18) as R18. unfold ASAN_K in M.
  step. gen_addi x18 w U. rewrite EA in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (ExecF.rng_sub' _ _ _ (bv_unsigned h) 1 RS ltac:(lia)) as RH.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. step. rewrite land7, U, (lts_sm (A mod 8 + 3) k ltac:(lia)), (proj2 (Z.ltb_lt _ _) C).
    apply CONT.
Qed.

Lemma bm2F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (v : word) (A : Z),
  bv_unsigned x18 + 8 = A ->
  A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 + 3 < bv_signed k) ->
  ov_read_bytes rsegs mm (Z_to_bv 64 (bv_unsigned x18 + 4)) 4 = Some (le4 v) ->
  ExecF.rng RNG (A / 8 + 2147450880) 1 ->
  ExecF.rng RNG (bv_unsigned x18 + 4) 4 ->
  (forall y11 y13 y14 : word, bv_unsigned y11 = A -> ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y11 (sx32 v) y13 y14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x8181c) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81804) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k v A EA RA M SK RV RS RW CONT.
  pose proof (u64_range x18) as R18. unfold ASAN_K in M.
  step. gen_addi x18 w U. rewrite EA in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (ExecF.rng_sub' _ _ _ (bv_unsigned h) 1 RS ltac:(lia)) as RH.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT. exact U.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. step. rewrite land7, U, (lts_sm (A mod 8 + 3) k ltac:(lia)), (proj2 (Z.ltb_lt _ _) C).
    apply CONT. exact U.
Qed.

Lemma bc1F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x11 = A ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  ExecF.rng RNG (A / 8 + 2147450880) 1 ->
  (forall y21 y22 : word, ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 y21 y22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x8190c) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x818fc) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k A EA M SK RS CONT.
  pose proof (u64_range x11) as RX. unfold ASAN_K in M.
  step. gen_shr x11 g G. rewrite EA in G.
  step. gen_addi g h H.
  pose proof (ExecF.rng_sub' _ _ _ (bv_unsigned h) 1 RS ltac:(lia)) as RH.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, EA, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

Lemma bc2F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (A D : Z),
  bv_unsigned x8 = A ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  bv_unsigned x11 = D ->
  mrd rsegs mm (wa D) = Some b ->
  ExecF.rng RNG (A / 8 + 2147450880) 1 ->
  ExecF.rng RNG D 1 ->
  (forall y21 y22 : word, ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (zxb b) x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 y21 y22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81920) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x8190c) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k b A D EA M SK ED MD RS RD CONT.
  pose proof (u64_range x8) as RX. unfold ASAN_K in M.
  step. gen_shr x8 g G. rewrite EA in G.
  step. gen_addi g h H.
  pose proof (ExecF.rng_sub' _ _ _ (bv_unsigned h) 1 RS ltac:(lia)) as RH.
  pose proof (ExecF.rng_sub' _ _ _ (bv_unsigned x11) 1 RD ltac:(lia)) as RW.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw0 mm x11 _ _ MD ED) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, EA, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

Lemma bc3F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x11 = A ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  ExecF.rng RNG (A / 8 + 2147450880) 1 ->
  (forall y22 y23 : word, ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 y22 y23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81948) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81938) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k A EA M SK RS CONT.
  pose proof (u64_range x11) as RX. unfold ASAN_K in M.
  step. gen_shr x11 g G. rewrite EA in G.
  step. gen_addi g h H.
  pose proof (ExecF.rng_sub' _ _ _ (bv_unsigned h) 1 RS ltac:(lia)) as RH.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, EA, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

Lemma bc4F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (A D : Z),
  bv_unsigned x10 = A ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  bv_unsigned x11 = D ->
  mrd rsegs mm (wa D) = Some b ->
  ExecF.rng RNG (A / 8 + 2147450880) 1 ->
  ExecF.rng RNG D 1 ->
  (forall y22 y23 : word, ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (zxb b) x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 y22 y23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x8195c) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81948) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k b A D EA M SK ED MD RS RD CONT.
  pose proof (u64_range x10) as RX. unfold ASAN_K in M.
  step. gen_shr x10 g G. rewrite EA in G.
  step. gen_addi g h H.
  pose proof (ExecF.rng_sub' _ _ _ (bv_unsigned h) 1 RS ltac:(lia)) as RH.
  pose proof (ExecF.rng_sub' _ _ _ (bv_unsigned x11) 1 RD ltac:(lia)) as RW.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw0 mm x11 _ _ MD ED) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, EA, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

Lemma bc5F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x10 = A ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  ExecF.rng RNG (A / 8 + 2147450880) 1 ->
  (forall y11 y22 : word, ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 y22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81984) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81974) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k A EA M SK RS CONT.
  pose proof (u64_range x10) as RX. unfold ASAN_K in M.
  step. gen_shr x10 g G. rewrite EA in G.
  step. gen_addi g h H.
  pose proof (ExecF.rng_sub' _ _ _ (bv_unsigned h) 1 RS ltac:(lia)) as RH.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, EA, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

Lemma bc6F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (A D : Z),
  bv_unsigned x8 + 2 = A ->
  A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  bv_unsigned x10 = D ->
  mrd rsegs mm (wa D) = Some b ->
  ExecF.rng RNG (A / 8 + 2147450880) 1 ->
  ExecF.rng RNG D 1 ->
  (forall y11 y22 y23 : word, ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (zxb b) y11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 y22 y23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x8199c) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81984) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k b A D EA RA M SK ED MD RS RD CONT.
  pose proof (u64_range x8) as R8. unfold ASAN_K in M.
  step. gen_addi x8 w U. rewrite EA in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (ExecF.rng_sub' _ _ _ (bv_unsigned h) 1 RS ltac:(lia)) as RH.
  pose proof (ExecF.rng_sub' _ _ _ (bv_unsigned x10) 1 RD ltac:(lia)) as RW.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw0 mm x10 _ _ MD ED) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, U, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

Section RDF.
Variables (RNG : ExecF.footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a1 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (raw out nch ns lo : Z).

Local Notation SP := (bv_unsigned sp).
Local Notation PD := (PostD ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a1 F fc m bs out nch ns lo).
Local Notation FRD mk junk :=
  (rw_cells rsegs mk (bv_unsigned sp + -96) [CB 24 junk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
Local Notation N := (3 * nch * ns).
Local Notation INV mk j := (INVD ra sp s0 s1 s2 s3 s4 s5 s6 s7 m bs raw out nch ns lo mk j).
Local Notation STATE pc mm x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x28 x29 x30 x31 :=
  (MS (mkR (Z_to_bv 64 0x817cc) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 x8 x9
        x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 s8 s9 s10 s11
        x28 x29 x30 x31)
      F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

Hypothesis Hsp : lo + 112 <= SP.
Hypothesis Hlo : 0 <= lo.
Hypothesis RSTK : ExecF.rng RNG (SP - 112) 112.

Lemma rd_exitF : forall (m1 : word -> option byte) (r : Z) (junk : list byte)
    (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word),
  FRD m1 junk -> stk rsegs m1 lo (SP + -96) -> wmono rsegs m m1 ->
  r = (if decode_ok (bv_unsigned a1) bs nch ns then ns else -1) ->
  (if decode_ok (bv_unsigned a1) bs nch ns
   then munch [(SP + -112, SP); (out, out + N)] m m1 /\ bytes_at rsegs m1 out (braid_out bs nch ns)
   else munch [(SP + -112, SP)] m m1) ->
  ExecF.evtF rsegs RNG PD (MS (mkR x1 (Z_to_bv 64 (SP + -96)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15
      x16 x17 x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x81a0c) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 r junk x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 HF ST WM Er HM.
  pose proof (u64_range sp) as Rsp.
  do 11 step.
  apply evtF_done. unfold PostD. exists x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, m1.
  split; [subst r; reflexivity|]. split; [exact WM|]. split.
  - pose proof (stk_release rsegs m1 lo (SP + -96) _ ST HF ltac:(lia)) as ST2.
    cbn [cells_size csize Nat.add] in ST2. replace (SP + -96 + Z.of_nat 96) with SP in ST2 by lia. exact ST2.
  - replace (SP - 112) with (SP + -112) by lia. exact HM.
Qed.

Hypothesis Hlen : length bs = 1492%nat.
Hypothesis Hraw : 0 <= raw.
Hypothesis Hraw2 : raw + 1492 <= 2^64.
Hypothesis Hout : 0 < out.
Hypothesis HoutN : out + N < 2^64.
Hypothesis Hnch : 0 < nch.
Hypothesis Hev : nch mod 2 = 0.
Hypothesis Hns : 0 < ns.
Hypothesis H480 : nch * ns <= 480.
Hypothesis HSEP : SEP sp raw out nch ns.
Hypothesis AR : addressable m raw 1492.
Hypothesis AO : addressable m out N.
Hypothesis APW : forall x, SP - 112 <= x < SP -> app_mem x.
Hypothesis OK : decode_ok (bv_unsigned a1) bs nch ns = true.
Hypothesis RR : ExecF.rng RNG raw 1492.
Hypothesis RSR : ExecF.rng RNG (raw / 8 + ASAN_K) ((raw + 1491) / 8 - raw / 8 + 1).
Hypothesis RO : ExecF.rng RNG out N.
Hypothesis RSO : ExecF.rng RNG (out / 8 + ASAN_K) ((out + N - 1) / 8 - out / 8 + 1).

(* The pure lemmas of reac_decode.v at this section's variables. *)
Local Notation bpre_lenS := (bpre_len bs nch ns Hlen Hnch).
Local Notation bw_extS := (bw_ext bs out nch ns Hlen Hout Hnch).
Local Notation src_boundS := (src_bound bs out nch ns Hlen Hout HoutN Hnch Hev Hns H480).
Local Notation SRC_rdS := (SRC_rd bs raw out nch ns Hlen Hout HoutN Hnch Hev Hns H480).
Local Notation SRC_shrS := (SRC_shr sp m bs raw out nch ns Hlen Hout HoutN Hnch Hev Hns H480 AR AO APW).
Local Notation DST_shoS := (DST_sho sp m bs out nch ns Hlen AO APW).

Ltac stf :=
  let D1 := fresh "D" in let D2 := fresh "D" in let D3 := fresh "D" in
  pose proof HSEP as [D1 [D2 D3]]; st; clear D1 D2 D3.

Ltac ostore :=
  rewrite ?le1_zxb;
  lazymatch goal with
  | |- ExecF.evtF ?sg ?RG ?Q (MS ?R ?Fr ?pc ?f ?rv (write_to_mem ?mk ?w [?b]) ?ro) =>
      let a := addr_expr w in
      lazymatch a with
      | out + ?q =>
          change (ExecF.evtF sg RG Q (MS R Fr pc f rv (write_to_mem mk (wa (out + q)) [b]) ro));
          match goal with BW : bytes_at _ mk out (bpre _ _ _ ?q0) |- _ =>
            apply (bw_extS mk q0 q) in BW; [ | lia | lia | lia ]
          end;
          match goal with H : Z.of_nat (length (bpre _ _ _ _)) = _ |- _ => clear H end;
          assert (LB : Z.of_nat (length (bpre bs nch ns (q + 1))) = q + 1) by (apply bpre_lenS; lia);
          let D1 := fresh "D" in let D2 := fresh "D" in let D3 := fresh "D" in
          pose proof HSEP as [D1 [D2 D3]];
          transport_chunks sg mk (out + q) [b]; footprint_after_store sg mk (out + q) [b];
          clear D1 D2 D3;
          let m2 := fresh "m" in set (m2 := write_to_mem mk (wa (out + q)) [b]) in *; clearbody m2
      end
  end.

Ltac rebundle :=
  lazymatch goal with H : rw_cells _ ?mm ?A (?c1 :: ?c2 :: ?c3 :: ?post) |- _ =>
    apply (rw_cells_merge rsegs mm A [] [c1; c2; c3] post) in H; cbn [app cells_size csize Nat.add] in H;
    split; [assumption|]; split; [eexists; exact H|]; split; [assumption|]; split; [assumption|];
    split; [assumption|]; split; [assumption|]; eassumption
  end.

(* The footprint goal of a shadow byte or of a data byte of the input or of the output buffer, from the range
   premises. SB (src_bound) or the row bounds give the index bounds. *)
Ltac rngF :=
  lazymatch goal with
  | |- ExecF.rng _ ((raw + ?e) / 8 + 2147450880) 1 =>
      apply (rng_shadow_byte RNG raw (raw + 1491) (raw + e) RSR); lia
  | |- ExecF.rng _ ((out + ?e) / 8 + 2147450880) 1 =>
      apply (rng_shadow_byte RNG out (out + N - 1) (out + e) RSO); lia
  | |- ExecF.rng _ (raw + ?e) 1 => apply (ExecF.rng_sub RNG raw 1492 (raw + e) 1 RR); lia
  | |- ExecF.rng _ (out + ?e) 1 => apply (ExecF.rng_sub RNG out N (out + e) 1 RO); lia
  end.

Lemma rd_innerF : forall (ch : Z) (x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 : word),
  0 <= ch < nch ->
  bv_unsigned x5 = 18446744073709551599 -> bv_unsigned x6 = 2 -> bv_unsigned x7 = 18446744073709551615 ->
  bv_unsigned x9 = ch - ch mod 2 -> bv_unsigned x12 = nch -> bv_unsigned x13 = ns -> bv_unsigned x14 = ch ->
  bv_unsigned x15 = raw + 50 -> bv_unsigned x16 = 18446744073709551608 -> bv_unsigned x17 = SP + -96 ->
  bv_unsigned x18 = ch mod 2 -> bv_unsigned x28 = 18446744073709551615 - (raw + 50) ->
  bv_unsigned x29 = 2147483646 -> bv_unsigned x30 = 18446744073709551607 ->
  (forall (m2 : word -> option byte) (y8 y10 y11 y20 y21 y22 y23 y31 : word),
     bv_unsigned y20 = out + 3 * (ch * ns + ns) - 3 -> INV m2 (3 * (ch * ns + ns)) ->
     ExecF.evtF rsegs RNG PD (STATE 0x819fc m2 x5 x6 x7 y8 x9 y10 y11 x12 x13 x14 x15 x16 x17 x18 y20 y21 y22 y23 x28 x29 x30 y31)) ->
  forall (K : nat) (s : Z) (m1 : word -> option byte) (x8 x10 x11 x20 x21 x22 x23 x31 : word),
  Z.to_nat (ns - s) = K -> 0 <= s < ns ->
  bv_unsigned x31 = s -> bv_unsigned x8 = out + 3 * (ch * ns + s) -> bv_unsigned x21 = out + 3 * (ch * ns + s) ->
  INV m1 (3 * (ch * ns + s)) ->
  ExecF.evtF rsegs RNG PD (STATE 0x81878 m1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x28 x29 x30 x31).
Proof.
  intros ch x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30
    Hch H5 H6 H7 H9 H12 H13 H14 H15 H16 H17 H18 H28 H29 H30 CONT K.
  apply wv in H5, H6, H7, H9, H12, H13, H14, H15, H16, H17, H18, H28, H29, H30.
  subst x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30.
  pose proof (geom_bounds nch ns ltac:(lia) ltac:(lia) H480) as GB.
  pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hm.
  assert (ch - ch mod 2 <= nch - 2) by (Z.div_mod_to_equations; lia).
  assert (0 <= ch - ch mod 2) by (Z.div_mod_to_equations; lia).
  pose proof (u64_range sp) as Rsp.
  induction K as [K IH] using lt_wf_ind.
  intros s m1 x8 x10 x11 x20 x21 x22 x23 x31 HK Hs H31 H8 H21 I0.
  pose proof (row_bounds s ns nch Hs ltac:(lia)) as RB1.
  pose proof (row_bounds ch nch ns Hch ltac:(lia)) as RB2.
  apply wv in H31, H8, H21. subst x31 x8 x21.
  destruct I0 as (BR & (junk & FR) & ST & WA & MU & WM & BW).
  assert (LB : Z.of_nat (length (bpre bs nch ns (3 * (ch * ns + s)))) = 3 * (ch * ns + s)) by (apply bpre_lenS; lia).
  st. st. st. cnd false.
  st. st. st. st. cnd false.
  st. st. st. st.
  st.
  destruct (Z.eqb_spec (ch mod 2) 0) as [EP|EP].
  - cnd false.
    st. stf. st. cnd false.
    stf. st. cnd false.
    st. st.
    st. st.
    stf. st. cnd false.
    st. st. cnd false.
    st.
    pose proof (src_boundS ch s 0 (3 + ch mod 2) Hch Hs ltac:(lia) eq_refl) as SB.
    destruct (SRC_shrS _ ch s 0 (3 + ch mod 2) MU Hch Hs ltac:(lia) eq_refl) as (k0 & MK & SK).
    eapply bc1F; [ | exact MK | exact SK | rngF | intros p21 p22 ]; [ ufin | ]. clear MK SK.
    destruct (DST_shoS _ (3 * (ch * ns + s) + 0) MU ltac:(lia)) as (k1 & MK & SK).
    pose proof (SRC_rdS _ ch s 0 (3 + ch mod 2) BR Hch Hs ltac:(lia) eq_refl) as RD.
    eapply bc2F; [ | exact MK | exact SK | | exact RD | rngF | rngF | intros q21 q22 ]; [ ufin | ufin | ].
    clear MK SK RD SB.
    pose proof (wr_at_store_ok rsegs _ out N (3 * (ch * ns + s) + 0) 1 WA ltac:(lia) ltac:(lia)) as HS.
    pose proof (ExecF.rng_sub' _ _ _ (out + (3 * (ch * ns + s) + 0)) 1 RO ltac:(lia)) as RW.
    st. clear HS RW. ostore.
    st. st. cnd false.
    st. st. cnd false.
    st.
    pose proof (src_boundS ch s 1 (5 * (ch mod 2)) Hch Hs ltac:(lia) eq_refl) as SB.
    destruct (SRC_shrS _ ch s 1 (5 * (ch mod 2)) MU Hch Hs ltac:(lia) eq_refl) as (k2 & MK & SK).
    eapply bc3F; [ | exact MK | exact SK | rngF | intros r22 r23 ]; [ ufin | ]. clear MK SK.
    destruct (DST_shoS _ (3 * (ch * ns + s) + 1) MU ltac:(lia)) as (k3 & MK & SK).
    pose proof (SRC_rdS _ ch s 1 (5 * (ch mod 2)) BR Hch Hs ltac:(lia) eq_refl) as RD.
    eapply bc4F; [ | exact MK | exact SK | | exact RD | rngF | rngF | intros u22 u23 ]; [ ufin | ufin | ].
    clear MK SK RD SB.
    pose proof (wr_at_store_ok rsegs _ out N (3 * (ch * ns + s) + 1) 1 WA ltac:(lia) ltac:(lia)) as HS.
    pose proof (ExecF.rng_sub' _ _ _ (out + (3 * (ch * ns + s) + 1)) 1 RO ltac:(lia)) as RW.
    st. clear HS RW. ostore.
    st. st. cnd false.
    st. st. cnd false.
    st.
    pose proof (src_boundS ch s 2 (1 + ch mod 2) Hch Hs ltac:(lia) eq_refl) as SB.
    destruct (SRC_shrS _ ch s 2 (1 + ch mod 2) MU Hch Hs ltac:(lia) eq_refl) as (k4 & MK & SK).
    eapply bc5F; [ | exact MK | exact SK | rngF | intros v11 v22 ]; [ ufin | ]. clear MK SK.
    destruct (DST_shoS _ (3 * (ch * ns + s) + 2) MU ltac:(lia)) as (k5 & MK & SK).
    pose proof (SRC_rdS _ ch s 2 (1 + ch mod 2) BR Hch Hs ltac:(lia) eq_refl) as RD.
    eapply bc6F; [ | | exact MK | exact SK | | exact RD | rngF | rngF | intros w11 w22 w23 ]; [ ufin | lia | ufin | ].
    clear MK SK RD SB.
    pose proof (wr_at_store_ok rsegs _ out N (3 * (ch * ns + s) + 2) 1 WA ltac:(lia) ltac:(lia)) as HS.
    pose proof (ExecF.rng_sub' _ _ _ (out + (3 * (ch * ns + s) + 2)) 1 RO ltac:(lia)) as RW.
    st. clear HS RW. ostore.
    st. st. st.
    st.
    brq BR'.
    + st. eapply CONT; [ ufin | eapply INVD_idx; [rebundle | lia] ].
    + eapply (IH (Z.to_nat (ns - (s + 1))) ltac:(lia) (s + 1)).
      all: lazymatch goal with
           | |- INV _ _ => eapply INVD_idx; [rebundle | lia]
           | _ => first [ reflexivity | lia | ufin ]
           end.
  - assert (E1 : ch mod 2 = 1) by lia. clear EP.
    cnd true.
    st. stf. st. cnd false.
    st. stf. st. cnd false.
    st.
    st. st.
    stf. st. cnd false.
    st. st. cnd false.
    st.
    pose proof (src_boundS ch s 0 (3 + ch mod 2) Hch Hs ltac:(lia) eq_refl) as SB.
    destruct (SRC_shrS _ ch s 0 (3 + ch mod 2) MU Hch Hs ltac:(lia) eq_refl) as (k0 & MK & SK).
    eapply bc1F; [ | exact MK | exact SK | rngF | intros p21 p22 ]; [ ufin | ]. clear MK SK.
    destruct (DST_shoS _ (3 * (ch * ns + s) + 0) MU ltac:(lia)) as (k1 & MK & SK).
    pose proof (SRC_rdS _ ch s 0 (3 + ch mod 2) BR Hch Hs ltac:(lia) eq_refl) as RD.
    eapply bc2F; [ | exact MK | exact SK | | exact RD | rngF | rngF | intros q21 q22 ]; [ ufin | ufin | ].
    clear MK SK RD SB.
    pose proof (wr_at_store_ok rsegs _ out N (3 * (ch * ns + s) + 0) 1 WA ltac:(lia) ltac:(lia)) as HS.
    pose proof (ExecF.rng_sub' _ _ _ (out + (3 * (ch * ns + s) + 0)) 1 RO ltac:(lia)) as RW.
    st. clear HS RW. ostore.
    st. st. cnd false.
    st. st. cnd false.
    st.
    pose proof (src_boundS ch s 1 (5 * (ch mod 2)) Hch Hs ltac:(lia) eq_refl) as SB.
    destruct (SRC_shrS _ ch s 1 (5 * (ch mod 2)) MU Hch Hs ltac:(lia) eq_refl) as (k2 & MK & SK).
    eapply bc3F; [ | exact MK | exact SK | rngF | intros r22 r23 ]; [ ufin | ]. clear MK SK.
    destruct (DST_shoS _ (3 * (ch * ns + s) + 1) MU ltac:(lia)) as (k3 & MK & SK).
    pose proof (SRC_rdS _ ch s 1 (5 * (ch mod 2)) BR Hch Hs ltac:(lia) eq_refl) as RD.
    eapply bc4F; [ | exact MK | exact SK | | exact RD | rngF | rngF | intros u22 u23 ]; [ ufin | ufin | ].
    clear MK SK RD SB.
    pose proof (wr_at_store_ok rsegs _ out N (3 * (ch * ns + s) + 1) 1 WA ltac:(lia) ltac:(lia)) as HS.
    pose proof (ExecF.rng_sub' _ _ _ (out + (3 * (ch * ns + s) + 1)) 1 RO ltac:(lia)) as RW.
    st. clear HS RW. ostore.
    st. st. cnd false.
    st. st. cnd false.
    st.
    pose proof (src_boundS ch s 2 (1 + ch mod 2) Hch Hs ltac:(lia) eq_refl) as SB.
    destruct (SRC_shrS _ ch s 2 (1 + ch mod 2) MU Hch Hs ltac:(lia) eq_refl) as (k4 & MK & SK).
    eapply bc5F; [ | exact MK | exact SK | rngF | intros v11 v22 ]; [ ufin | ]. clear MK SK.
    destruct (DST_shoS _ (3 * (ch * ns + s) + 2) MU ltac:(lia)) as (k5 & MK & SK).
    pose proof (SRC_rdS _ ch s 2 (1 + ch mod 2) BR Hch Hs ltac:(lia) eq_refl) as RD.
    eapply bc6F; [ | | exact MK | exact SK | | exact RD | rngF | rngF | intros w11 w22 w23 ]; [ ufin | lia | ufin | ].
    clear MK SK RD SB.
    pose proof (wr_at_store_ok rsegs _ out N (3 * (ch * ns + s) + 2) 1 WA ltac:(lia) ltac:(lia)) as HS.
    pose proof (ExecF.rng_sub' _ _ _ (out + (3 * (ch * ns + s) + 2)) 1 RO ltac:(lia)) as RW.
    st. clear HS RW. ostore.
    st. st. st.
    st.
    brq BR'.
    + st. eapply CONT; [ ufin | eapply INVD_idx; [rebundle | lia] ].
    + eapply (IH (Z.to_nat (ns - (s + 1))) ltac:(lia) (s + 1)).
      all: lazymatch goal with
           | |- INV _ _ => eapply INVD_idx; [rebundle | lia]
           | _ => first [ reflexivity | lia | ufin ]
           end.
Qed.

Lemma rd_outerF : forall (K : nat) (ch : Z) (m1 : word -> option byte)
    (x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x28 x29 x30 x31 : word),
  Z.to_nat (nch - ch) = K -> 0 <= ch < nch ->
  bv_unsigned x5 = 18446744073709551599 -> bv_unsigned x6 = 2 -> bv_unsigned x7 = 18446744073709551615 ->
  bv_unsigned x8 = out + 3 * (ch * ns) -> bv_unsigned x12 = nch -> bv_unsigned x13 = ns -> bv_unsigned x14 = ch ->
  bv_unsigned x15 = raw + 50 -> bv_unsigned x16 = 18446744073709551608 -> bv_unsigned x17 = SP + -96 ->
  bv_unsigned x28 = 18446744073709551615 - (raw + 50) -> bv_unsigned x29 = 2147483646 ->
  bv_unsigned x30 = 18446744073709551607 ->
  INV m1 (3 * (ch * ns)) ->
  ExecF.evtF rsegs RNG PD (STATE 0x81868 m1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x28 x29 x30 x31).
Proof.
  induction K as [K IH] using lt_wf_ind.
  intros ch m1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x28 x29 x30 x31
    HK Hch H5 H6 H7 H8 H12 H13 H14 H15 H16 H17 H28 H29 H30 I0.
  pose proof (row_bounds ch nch ns Hch ltac:(lia)) as RB2.
  pose proof (geom_bounds nch ns ltac:(lia) ltac:(lia) H480) as GB.
  pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hm.
  assert (0 <= ch - ch mod 2) by (Z.div_mod_to_equations; lia).
  pose proof (u64_range sp) as Rsp.
  apply wv in H5, H6, H7, H8, H12, H13, H14, H15, H16, H17, H28, H29, H30.
  subst x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x28 x29 x30.
  st. st. rewrite (land_2m2 ch) by lia. st. rewrite land1. st.
  eapply (rd_innerF ch) with (K := Z.to_nat (ns - 0)) (s := 0).
  all: lazymatch goal with
       | |- forall _ : word -> option byte, _ => idtac
       | |- INV _ _ => eapply INVD_idx; [exact I0 | lia]
       | _ => first [ lia | reflexivity | ufin ]
       end.
  intros m2 y8 y10 y11 y20 y21 y22 y23 y31 H20 I2. apply wv in H20. subst y20.
  st. st. st.
  brq BR.
  - assert (EN : nch * ns = ch * ns + ns) by (replace nch with (ch + 1) by lia; ring).
    st.
    destruct I2 as (BR2 & (junk2 & FR2) & ST2 & WA2 & MU2 & WM2 & BW2).
    eapply rd_exitF with (r := ns); [exact FR2 | exact ST2 | exact WM2 | rewrite OK; reflexivity | ].
    rewrite OK. split; [exact MU2|].
    replace (braid_out bs nch ns) with (bpre bs nch ns (3 * (ch * ns + ns))) by (unfold bpre, braid_out; do 3 f_equal; lia).
    exact BW2.
  - assert (EQ1 : (ch + 1) * ns = ch * ns + ns) by ring.
    eapply (IH (Z.to_nat (nch - (ch + 1))) ltac:(lia) (ch + 1)).
    all: lazymatch goal with
         | |- INV _ _ => eapply INVD_idx; [exact I2 | lia]
         | _ => first [ reflexivity | lia | (rewrite unsigned_lit by lia; lia) | ufin ]
         end.
Qed.

End RDF.

Ltac curmemF k := lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => k mm end.

Theorem reac_decode_holds_F : reac_frame_inspect_contract_F -> reac_decode_contract_F.
Proof.
  intros HI. unfold reac_decode_contract_F, REAC_DECODE, REAC_DECODE_D.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m bs raw mode out nch ns lo E0 E2 E3 Rraw Rmode Rout HB Rnch Rns HM ST LO DR DM HO APS1 APS2 CELLS SRW DC AR AM AO
    NR NM NO RSTK RGC RCK HRAW HMODE HOUT.
  subst a0 a2 a3.
  pose proof (u64_range sp) as Rsp.
  assert (Hlo : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold GOT_CELL_K, CELL_K in RGC, RCK.
  pose proof (conj HM CELLS) as PK. clear HM CELLS.
  carve_frame 96%nat ST.
  do 10 step.
  destruct PK as (HM & CELLS).
  unfold off_stk, GOT_CELL_K, MIDEND in DC.
  curmemF ltac:(fun mm => assert (CELLS1 : asan_cells mm)
    by (eapply asan_cells_munch; [exact CELLS | exact MU | unfold MIDEND, GOT_CELL_K; lia])).
  pose proof CELLS1 as (CK & GCK & _).
  unfold CELL_K, GOT_CELL_K, ASAN_K in CK, GCK.
  pose proof (rd_all _ _ _ GCK) as RDG. rewrite length_le8 in RDG.
  pose proof (rd_all _ _ _ CK) as RDS. rewrite length_le8 in RDS.
  do 3 step. step. step. clear RDG RDS CK GCK. step. step.
  curmemF ltac:(fun mm => eapply ExecF.evtF_cut;
    [eapply (HI RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm bs lo) |]).
  { rewrite unsigned_lit by lia. exact ST. }
  { unfold REAC_FRAME_INSPECT_FRAME. rewrite unsigned_lit by lia. lia. }
  { unfold REAC_FRAME_INSPECT_FRAME. intros L. destruct (HB L) as [LEN BB]. specialize (DR L). specialize (AR L).
    unfold off_stk in DR. rewrite (unsigned_lit raw) by lia. rewrite unsigned_lit by lia.
    pose proof (bytes_at_bound _ _ _ _ BB) as BBB. rewrite LEN in BBB.
    split; [exact LEN|]. split; [eapply bytes_tp; [exact MU | rewrite LEN; lia | exact BB]|].
    split; [exact (NR L)|].
    split; [unfold off_stk; usub; lia|].
    split; [replace (bv_unsigned sp + -96 - 16) with (bv_unsigned sp - 112) by lia; exact APS1|].
    split; [apply (app_win (bv_unsigned sp) 112); [lia | exact APS1 | exact APS2 | lia]|].
    split; [exact CELLS1|].
    split; [eapply shadow_rw_munch; [exact SRW | exact MU | exact WM | intros a Ha; apply win_shadow; assumption]|].
    split; [unfold off_stk, GOT_CELL_K; usub; lia|].
    split; [unfold off_stk, CELL_K; usub; lia|].
    eapply addr_win; [exact AR | exact MU | lia | exact APS1 | exact APS2]. }
  { unfold REAC_FRAME_INSPECT_FRAME. rewrite unsigned_lit by lia. apply (ExecF.rng_sub _ _ _ _ _ RSTK); lia. }
  { intros L. destruct (HRAW L) as [RR RSR]. rewrite (unsigned_lit raw) by lia.
    split; [exact RGC|]. split; [exact RCK|].
    split; [apply (ExecF.rng_sub _ _ _ _ _ RR); lia|].
    split; [apply (ExecF.rng_sub _ _ _ _ _ RR); lia|].
    split; apply (ExecF.rng_sub _ _ _ _ _ RSR); Z.div_mod_to_equations; lia. }
  intros ms' (a1' & a2' & a3' & a4' & m2 & -> & MU2 & WM2 & ST2).
  replace (ret_pc (Z_to_bv 64 530380)) with (Z_to_bv 64 530380) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  unfold REAC_FRAME_INSPECT_FRAME in MU2, ST2. rewrite unsigned_lit in MU2, ST2 by lia.
  assert (MU0 : munch [(bv_unsigned sp + -112, bv_unsigned sp)] m m2)
    by (eapply munch_trans; [eapply munch_wider; [ | | exact MU]; lia | eapply munch_wider; [ | | exact MU2]; lia]).
  assert (WM0 : wmono rsegs m m2) by (eapply wmono_trans; [exact WM | exact WM2]).
  pose proof (rw_cells_transport rsegs _ _ m2 _ _ FR MU2 WM2
    ltac:(cbn [disjoint_from cells_size csize]; split; [lia | exact I])) as FR2.
  clear FR MU2 WM2 ST MU WM CELLS1.
  step. rewrite inspect_valid_bit. step. step.
  destruct (inspect_wf (bv_unsigned a1) bs) eqn:W.
  2:{ if_true.
      assert (PO : decode_ok (bv_unsigned a1) bs nch ns = false) by (unfold decode_ok; rewrite W; reflexivity).
      eapply rd_exitF with (r := -1).
      all: first [ exact FR2 | exact ST2 | exact WM0 | lia | exact RSTK
                 | rewrite PO; first [reflexivity | exact MU0] ]. }
  if_false.
  assert (L : bv_unsigned a1 = 1492) by (unfold inspect_wf in W; rewrite !andb_true_iff, !Z.eqb_eq in W; tauto).
  destruct (HB L) as [LEN BB]. specialize (DR L). specialize (AR L). specialize (AM eq_refl).
  specialize (NR L). destruct (NM eq_refl) as [NM0 NM4].
  destruct (HRAW L) as [RR RSR]. destruct (HMODE eq_refl) as [RM RSM].
  assert (NR' : 0 < raw) by lia. assert (NM0' : 0 < mode) by lia. clear NR NM0 NM.
  unfold off_stk in DR, DM.
  pose proof (bytes_at_bound _ _ _ _ BB) as BBB. rewrite LEN in BBB.
  apply bytes_at_app in HM. destruct HM as [HM1 HM2]. rewrite length_le4 in HM2.
  replace (mode + 4 + Z.of_nat 4) with (mode + 8) in HM2 by lia.
  apply (bytes_tp m m2 _ _ _ _ MU0) in HM1; [| rewrite length_le4; lia].
  apply (bytes_tp m m2 _ _ _ _ MU0) in HM2; [| rewrite length_le4; lia].
  pose proof (bytes_at_bound _ _ _ _ HM2) as HMB. rewrite length_le4 in HMB.
  pose proof (rd_all _ _ _ HM1) as HR1. rewrite length_le4 in HR1.
  pose proof (rd_all _ _ _ HM2) as HR2. rewrite length_le4 in HR2.
  assert (MU0' : munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m2)
    by (eapply munch_wider; [ | | exact MU0]; lia).
  assert (AM2 : addressable m2 (mode + 4) 8)
    by (eapply addr_win; [exact AM | exact MU0' | lia | exact APS1 | exact APS2]).
  step. cnd false.
  step. step. cnd false.
  step. cnd false.
  st. rewrite (land3_0 mode) by lia.
  step. cnd false.
  destruct (addr_four m2 (mode + 4) 8 (mode + 4) AM2 ltac:(lia) ltac:(lia)) as (k1 & MK1 & SK1).
  eapply bm1F; [ rewrite unsigned_lit by lia; reflexivity | lia | exact MK1 | exact SK1
    | exact (rng_shadow_byte _ (mode + 4) (mode + 11) (mode + 4) RSM ltac:(lia) ltac:(lia)) | intros y11 y12 y13 ].
  destruct (addr_four m2 (mode + 4) 8 (mode + 8) AM2 ltac:(lia) ltac:(lia)) as (k2 & MK2 & SK2).
  eapply bm2F; [ rewrite unsigned_lit by lia; reflexivity | lia | exact MK2 | exact SK2
    | rewrite unsigned_lit by lia; exact HR1
    | exact (rng_shadow_byte _ (mode + 4) (mode + 11) (mode + 8) RSM ltac:(lia) ltac:(lia))
    | rewrite unsigned_lit by lia; apply (ExecF.rng_sub _ _ _ _ _ RM); lia
    | intros z11 z13 z14 Z11 ].
  apply wv in Z11. subst z11.
  rewrite sx32_lit by lia.
  step. rewrite lts0_lit by lia. brq BN.
  2:{ assert (PO : decode_ok (bv_unsigned a1) bs nch ns = false)
        by (apply not_true_iff_false; rewrite decode_ok_spec; lia).
      eapply rd_exitF with (r := -1).
      all: first [ exact FR2 | exact ST2 | exact WM0 | lia | exact RSTK
                 | rewrite PO; first [reflexivity | exact MU0] ]. }
  step. rewrite (unsigned_lit nch) by lia. rewrite land1.
  step. brq BE.
  2:{ assert (PO : decode_ok (bv_unsigned a1) bs nch ns = false)
        by (apply not_true_iff_false; rewrite decode_ok_spec; lia).
      eapply rd_exitF with (r := -1).
      all: first [ exact FR2 | exact ST2 | exact WM0 | lia | exact RSTK
                 | rewrite PO; first [reflexivity | exact MU0] ]. }
  pose proof (ExecF.rng_sub' _ _ _ (mode + 8) 4 RM ltac:(lia)) as RM8.
  step. rewrite sx32_lit by lia.
  clear RM8.
  step. rewrite lts0_lit by lia. brq BS.
  2:{ assert (PO : decode_ok (bv_unsigned a1) bs nch ns = false)
        by (apply not_true_iff_false; rewrite decode_ok_spec; lia).
      eapply rd_exitF with (r := -1).
      all: first [ exact FR2 | exact ST2 | exact WM0 | lia | exact RSTK
                 | rewrite PO; first [reflexivity | exact MU0] ]. }
  pose proof (prod_bound62 ns nch ltac:(lia) ltac:(lia)).
  step. rewrite (unsigned_lit ns), (unsigned_lit nch) by lia.
  step. step. brq BM.
  { assert (PO : decode_ok (bv_unsigned a1) bs nch ns = false)
        by (apply not_true_iff_false; rewrite decode_ok_spec; lia).
      eapply rd_exitF with (r := -1).
      all: first [ exact FR2 | exact ST2 | exact WM0 | lia | exact RSTK
                 | rewrite PO; first [reflexivity | exact MU0] ]. }
  assert (PO : decode_ok (bv_unsigned a1) bs nch ns = true)
    by (rewrite decode_ok_spec; split; [exact W|]; repeat split; lia).
  destruct (HO PO) as (HW & HoutN & DOR & DOS). specialize (AO PO). specialize (NO PO).
  destruct (HOUT PO) as [RO RSO].
  assert (NO' : 0 < out) by lia. clear NO. unfold off_stk in DOS.
  do 11 step.
  eapply rd_outerF with (K := Z.to_nat (nch - 0)) (ch := 0) (ra := ra) (sp := sp) (s0 := s0) (s1 := s1) (s2 := s2)
    (s3 := s3) (s4 := s4) (s5 := s5) (s6 := s6) (s7 := s7) (a1 := a1) (m := m) (bs := bs) (raw := raw) (out := out)
    (nch := nch) (ns := ns) (lo := lo).
  all: lazymatch goal with
       | |- context [INVD] => idtac
       | |- context [SEP] => unfold SEP; split; [|split]; lia
       | _ => first [ assumption | reflexivity | lia | ufin
                    | (intros x Hx; apply (app_win (bv_unsigned sp) 112); [lia | exact APS1 | exact APS2 | lia]) ]
       end.
  replace (3 * (0 * ns)) with 0 by lia.
  split; [|split; [eexists; exact FR2|split; [exact ST2|split; [|split; [|split; [exact WM0|]]]]]].
  - eapply bytes_tp; [exact MU0' | rewrite LEN; lia | exact BB].
  - eapply wr_at_transport; [exact HW | exact WM0].
  - apply munch_extend. exact MU0.
  - unfold bpre. change (Z.to_nat 0) with 0%nat. cbn [seq map].
    split; [lia|]. split; [cbn [length Z.of_nat]; lia|]. intros i Hi. cbn [length] in Hi. lia.
Qed.

(* The twin implies the original: take the footprint that allows every access. *)
Theorem reac_decode_holds_of_F : reac_frame_inspect_contract_F -> reac_decode_contract.
Proof.
  intros HI. unfold reac_decode_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m bs raw mode out nch ns lo E0 E2 E3 Rraw Rmode Rout HB Rnch Rns HM ST LO DR DM HO APS1 APS2 CELLS SRW DC AR AM AO
    NR NM NO.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  pose proof (bytes_at_bound _ _ _ _ HM) as HMB. rewrite length_app, !length_le4 in HMB.
  refine (reac_decode_holds_F HI ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
            s9 s10 s11 t3 t4 t5 t6 F fc m bs raw mode out nch ns lo E0 E2 E3 Rraw Rmode Rout HB Rnch Rns HM ST LO DR DM
            HO APS1 APS2 CELLS SRW DC AR AM AO NR NM NO _ _ _ _ _ _).
  - apply ExecF.rng_all; unfold REAC_DECODE_D in *; lia.
  - apply ExecF.rng_all; unfold GOT_CELL_K; lia.
  - apply ExecF.rng_all; unfold CELL_K; lia.
  - intros L. destruct (HB L) as [LEN BB]. pose proof (bytes_at_bound _ _ _ _ BB) as BBB. rewrite LEN in BBB.
    clear - Rraw BBB. split; apply ExecF.rng_all; unfold ASAN_K; Z.div_mod_to_equations; lia.
  - intros _. clear - Rmode HMB. split; apply ExecF.rng_all; unfold ASAN_K; Z.div_mod_to_equations; lia.
  - intros D. destruct (HO D) as (_ & HN & _). clear - Rout HN.
    split; apply ExecF.rng_all; unfold ASAN_K; Z.div_mod_to_equations; lia.
Qed.
