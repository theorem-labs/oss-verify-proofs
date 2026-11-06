From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import AsanKA AsanKAProof reac_frame_inspect_c reac_decode_plain_le_c ReacDecodeLib reac_decode_plain_le.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import reac_frame_inspect_F_c reac_frame_inspect_F reac_decode_plain_le_F_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Footprint twin of reac_decode_plain_le_holds (reac_decode_plain_le.v). The proof follows reac_decode_plain_le.v
   step for step, with StepF's step. The pure lemmas of reac_decode_plain_le.v (INV, INV_rd, INV_shr, INV_sho, ...)
   are used from there. Before each load of a shadow byte at h and of a data byte at w, the proof names the one-byte
   ranges [h, h+1) and [w, w+1), cut from the footprint premises, so that StepF's access check finds them. *)

Ltac st := step; nrm.

Ltac cnd b :=
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b; [cbv iota | symmetry; unfold bv_eqb, bv_ltu, bv_lts; usub; fold_lit_ux; solve_cond_rec]
  end.

Lemma pb_m1F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x18 + 4 = A ->
  A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 + 3 < bv_signed k) ->
  ExecF.rng RNG (A / 8 + 2147450880) 1 ->
  (forall y11 y12 y13 : word, ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y11 y12 y13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81af8) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81ae4) fc None mm (seg_rom rsegs)).
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

Lemma pb_m2F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (v : word) (A : Z),
  bv_unsigned x18 + 8 = A ->
  A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 + 3 < bv_signed k) ->
  ov_read_bytes rsegs mm (Z_to_bv 64 (bv_unsigned x18 + 4)) 4 = Some (le4 v) ->
  ExecF.rng RNG (A / 8 + 2147450880) 1 ->
  ExecF.rng RNG (bv_unsigned x18 + 4) 4 ->
  (forall y11 y12 y14 : word, bv_unsigned y11 = A -> ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y11 y12 (sx32 v) y14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81b10) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81af8) fc None mm (seg_rom rsegs)).
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

Lemma pb_c1F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x10 = A ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  ExecF.rng RNG (A / 8 + 2147450880) 1 ->
  (forall y12 y30 : word, ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 y12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 y30 x31) F (Z_to_bv 64 0x81b94) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81b84) fc None mm (seg_rom rsegs)).
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

Lemma pb_c2F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (A D : Z),
  bv_unsigned x8 = A ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  bv_unsigned x10 = D ->
  mrd rsegs mm (wa D) = Some b ->
  ExecF.rng RNG (A / 8 + 2147450880) 1 ->
  ExecF.rng RNG D 1 ->
  (forall y30 y31 : word, ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (zxb b) x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 y30 y31) F (Z_to_bv 64 0x81ba8) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81b94) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k b A D EA M SK ED MD RS RD CONT.
  pose proof (u64_range x8) as RX. unfold ASAN_K in M.
  step. gen_shr x8 g G. rewrite EA in G.
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
    step. step. rewrite land7, EA, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

Lemma pb_c3F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x12 = A ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  ExecF.rng RNG (A / 8 + 2147450880) 1 ->
  (forall y9 y31 : word, ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 y9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 y31) F (Z_to_bv 64 0x81bcc) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81bbc) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k A EA M SK RS CONT.
  pose proof (u64_range x12) as RX. unfold ASAN_K in M.
  step. gen_shr x12 g G. rewrite EA in G.
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

Lemma pb_c4F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (A D : Z),
  bv_unsigned x11 = A ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  bv_unsigned x12 = D ->
  mrd rsegs mm (wa D) = Some b ->
  ExecF.rng RNG (A / 8 + 2147450880) 1 ->
  ExecF.rng RNG D 1 ->
  (forall y9 y31 : word, ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 y9 x10 x11 (zxb b) x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 y31) F (Z_to_bv 64 0x81be0) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81bcc) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k b A D EA M SK ED MD RS RD CONT.
  pose proof (u64_range x11) as RX. unfold ASAN_K in M.
  step. gen_shr x11 g G. rewrite EA in G.
  step. gen_addi g h H.
  pose proof (ExecF.rng_sub' _ _ _ (bv_unsigned h) 1 RS ltac:(lia)) as RH.
  pose proof (ExecF.rng_sub' _ _ _ (bv_unsigned x12) 1 RD ltac:(lia)) as RW.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw0 mm x12 _ _ MD ED) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, EA, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

Lemma pb_c5F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x10 = A ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  ExecF.rng RNG (A / 8 + 2147450880) 1 ->
  (forall y11 y12 : word, ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y11 y12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81c04) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81bf4) fc None mm (seg_rom rsegs)).
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

Lemma pb_c6F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (A D : Z),
  bv_unsigned x8 + 2 = A ->
  A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  bv_unsigned x10 = D ->
  mrd rsegs mm (wa D) = Some b ->
  ExecF.rng RNG (A / 8 + 2147450880) 1 ->
  ExecF.rng RNG D 1 ->
  (forall y11 y12 y31 : word, bv_unsigned y11 = A -> ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (zxb b) y11 y12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 y31) F (Z_to_bv 64 0x81c1c) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81c04) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k b A D EA RA M SK ED MD RS RD CONT.
  pose proof (u64_range x8) as RX. unfold ASAN_K in M.
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
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT. exact U.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, U, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT. exact U.
Qed.

Section PLF.
Variables (RNG : ExecF.footprint) (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a1 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (raw mode out nch ns lo : Z)
  (jk : list byte).

Local Notation SP := (bv_unsigned sp).
Local Notation PC := (PostC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a1 F fc m bs out nch ns lo).
Local Notation FR mk := (rw_cells rsegs mk (bv_unsigned sp + -48) [CB 8 jk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
Local Notation N := (3 * nch * ns).
Local Notation IV mk j := (INV ra sp s0 s1 s2 s3 m bs raw out nch ns lo jk mk j).
Local Notation STATE pc mm x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 :=
  (MS (mkR (Z_to_bv 64 0x81ac0) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 x7 x8 x9
        x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 mode) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11
        x28 x29 x30 x31)
      F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

Hypothesis Hsp : lo + 64 <= SP.
Hypothesis Hlo : 0 <= lo.
Hypothesis RSTK : ExecF.rng RNG (SP - 64) 64.

Lemma pl_exitF : forall (m1 : word -> option byte) (r : Z)
    (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word),
  FR m1 -> stk rsegs m1 lo (SP + -48) -> wmono rsegs m m1 ->
  r = (if plain_ok (bv_unsigned a1) bs nch ns then ns else -1) ->
  (if plain_ok (bv_unsigned a1) bs nch ns
   then munch [(SP + -64, SP); (out, out + N)] m m1 /\ bytes_at rsegs m1 out (plain_out bs nch ns)
   else munch [(SP + -64, SP)] m m1) ->
  ExecF.evtF rsegs RNG PC (MS (mkR x1 (Z_to_bv 64 (SP + -48)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16
      x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x81c8c) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 r x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 HF ST WM Er HM.
  pose proof (u64_range sp) as Rsp.
  do 7 step.
  apply evtF_done. unfold PostC. exists x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, m1.
  split; [subst r; reflexivity|]. split; [exact WM|]. split.
  - pose proof (stk_release rsegs m1 lo (SP + -48) _ ST HF ltac:(lia)) as ST2.
    cbn [cells_size csize Nat.add] in ST2. replace (SP + -48 + Z.of_nat 48) with SP in ST2 by lia. exact ST2.
  - replace (SP - 64) with (SP + -64) by lia. exact HM.
Qed.

Hypothesis Hlen : length bs = 1492%nat.
Hypothesis Hraw : 0 <= raw.
Hypothesis Hraw2 : raw + 1492 <= 2^64.
Hypothesis Hout : 0 <= out.
Hypothesis Hout0 : out <> 0.
Hypothesis HoutN : out + N < 2^64.
Hypothesis Hnch : 0 < nch.
Hypothesis Hns : 0 < ns.
Hypothesis H480 : nch * ns <= 480.
Hypothesis DOR : out + N <= raw \/ raw + 1492 <= out.
Hypothesis DOS : out + N <= SP - 64 \/ SP <= out.
Hypothesis AR : addressable m raw 1492.
Hypothesis AO : addressable m out N.
Hypothesis APW : forall x, SP - 64 <= x < SP -> app_mem x.
Hypothesis OK : plain_ok (bv_unsigned a1) bs nch ns = true.
Hypothesis RR : ExecF.rng RNG raw 1492.
Hypothesis RSR : ExecF.rng RNG (raw / 8 + ASAN_K) ((raw + 1491) / 8 - raw / 8 + 1).
Hypothesis RO : ExecF.rng RNG out N.
Hypothesis RSO : ExecF.rng RNG (out / 8 + ASAN_K) ((out + N - 1) / 8 - out / 8 + 1).

(* The pure lemmas of reac_decode_plain_le.v at this section's variables. *)
Local Notation INV_rdS := (INV_rd ra sp s0 s1 s2 s3 m bs raw out nch ns lo jk Hlen Hraw Hraw2 Hout Hout0 Hnch Hns H480).
Local Notation INV_shrS :=
  (INV_shr ra sp s0 s1 s2 s3 m bs raw out nch ns lo jk Hlen Hraw Hraw2 Hout Hout0 Hnch Hns H480 AR AO APW).
Local Notation INV_shoS := (INV_sho ra sp s0 s1 s2 s3 m bs raw out nch ns lo jk Hlen Hout Hout0 AO APW).
Local Notation INV_wrS := (INV_wr ra sp s0 s1 s2 s3 m bs raw out nch ns lo jk Hlen Hout Hout0).
Local Notation INV_storeS :=
  (INV_store ra sp s0 s1 s2 s3 m bs raw out nch ns lo jk Hsp Hlo Hlen Hraw Hraw2 Hout Hout0 HoutN DOR DOS).
Local Notation INV_outS := (INV_out ra sp s0 s1 s2 s3 m bs raw out nch ns lo jk Hlen Hraw2 Hout Hout0 HoutN Hnch Hns).

Ltac do_store I0 I1 jj :=
  rewrite ?le1_zxb;
  lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mk ?a ?b) _) =>
    assert (I1 : IV (write_to_mem mk a b) (jj + 1)) by (eapply INV_storeS; [exact I0 | lia | lia | lia]);
    let m2 := fresh "m" in set (m2 := write_to_mem mk a b) in *; clearbody m2; clear I0
  end.

(* The footprint goal of a shadow byte or of a data byte of the input or of the output buffer, from the range
   premises and the index bounds in the context. *)
Ltac rngF :=
  lazymatch goal with
  | |- ExecF.rng _ ((raw + ?e) / 8 + 2147450880) 1 =>
      apply (rng_shadow_byte RNG raw (raw + 1491) (raw + e) RSR); lia
  | |- ExecF.rng _ ((out + ?e) / 8 + 2147450880) 1 =>
      apply (rng_shadow_byte RNG out (out + N - 1) (out + e) RSO); lia
  | |- ExecF.rng _ (raw + ?e) 1 => apply (ExecF.rng_sub RNG raw 1492 (raw + e) 1 RR); lia
  | |- ExecF.rng _ (out + ?e) 1 => apply (ExecF.rng_sub RNG out N (out + e) 1 RO); lia
  end.

Lemma pl_innerF : forall (ch : Z) (x5 x6 x7 x13 x14 x15 x16 x17 : word),
  0 <= ch < nch -> bv_unsigned x13 = nch -> bv_unsigned x14 = ns -> bv_unsigned x15 = ch ->
  bv_unsigned x16 = raw + 50 -> bv_unsigned x17 = 2 -> bv_unsigned x5 = 18446744073709551615 ->
  bv_unsigned x6 = 18446744073709551615 - (raw + 50) -> bv_unsigned x7 = 18446744073709551613 ->
  (forall (m2 : word -> option byte) (y8 y9 y10 y11 y12 y28 y29 y30 y31 : word),
     bv_unsigned y29 = out + 3 * (ch * ns + ns) - 3 -> IV m2 (3 * (ch * ns + ns)) ->
     ExecF.evtF rsegs RNG PC (STATE 0x81c30 m2 x5 x6 x7 y8 y9 y10 y11 y12 x13 x14 x15 x16 x17 y28 y29 y30 y31)) ->
  forall (K : nat) (s : Z) (m1 : word -> option byte) (x8 x9 x10 x11 x12 x28 x29 x30 x31 : word),
  Z.to_nat (ns - s) = K -> 0 <= s < ns ->
  bv_unsigned x28 = s -> bv_unsigned x8 = out + 3 * (ch * ns + s) -> bv_unsigned x30 = out + 3 * (ch * ns + s) ->
  IV m1 (3 * (ch * ns + s)) ->
  ExecF.evtF rsegs RNG PC (STATE 0x81b48 m1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31).
Proof.
  intros ch x5 x6 x7 x13 x14 x15 x16 x17 Hch H13 H14 H15 H16 H17 H5 H6 H7 CONT K.
  apply wv in H13, H14, H15, H16, H17, H5, H6, H7. subst x13 x14 x15 x16 x17 x5 x6 x7.
  assert (nch <= 480 /\ ns <= 480) by nia.
  induction K as [K IH] using lt_wf_ind.
  intros s m1 x8 x9 x10 x11 x12 x28 x29 x30 x31 HK Hs H28 H8 H30 I0.
  assert (s * nch <= (ns - 1) * nch) by nia.
  assert (ch * ns <= (nch - 1) * ns) by nia.
  assert (0 <= s * nch) by nia.
  assert (0 <= ch * ns) by nia.
  apply wv in H28, H8, H30. subst x28 x8 x30.
  st. st. st. cnd false.
  st. st. st. st. cnd false.
  st. st. st. st. cnd false.
  st. st. cnd false.
  st. st.
  destruct (INV_shrS m1 _ ch s 0 I0 Hch Hs ltac:(lia)) as (k0 & MK & SK).
  eapply pb_c1F; [ | exact MK | exact SK | rngF | intros p12 p30 ]; [ ufin | ]. clear MK SK.
  destruct (INV_shoS m1 _ (3 * (ch * ns + s) + 0) I0 ltac:(lia)) as (k1 & MK & SK).
  pose proof (INV_rdS m1 _ ch s 0 I0 Hch Hs ltac:(lia)) as RD.
  eapply pb_c2F; [ | exact MK | exact SK | | exact RD | rngF | rngF | intros q30 q31 ]; [ ufin | ufin | ].
  clear MK SK RD.
  pose proof (INV_wrS m1 _ (3 * (ch * ns + s) + 0) I0 ltac:(lia)) as HS.
  pose proof (ExecF.rng_sub' _ _ _ (out + (3 * (ch * ns + s) + 0)) 1 RO ltac:(lia)) as RW.
  st. clear HS RW.
  do_store I0 I1 (3 * (ch * ns + s) + 0).
  st. cnd false.
  st. st. cnd false.
  st.
  destruct (INV_shrS _ _ ch s 1 I1 Hch Hs ltac:(lia)) as (k2 & MK & SK).
  eapply pb_c3F; [ | exact MK | exact SK | rngF | intros r9 r31 ]; [ ufin | ]. clear MK SK.
  destruct (INV_shoS _ _ (3 * (ch * ns + s) + 1) I1 ltac:(lia)) as (k3 & MK & SK).
  pose proof (INV_rdS _ _ ch s 1 I1 Hch Hs ltac:(lia)) as RD.
  eapply pb_c4F; [ | exact MK | exact SK | | exact RD | rngF | rngF | intros u9 u31 ]; [ ufin | ufin | ].
  clear MK SK RD.
  pose proof (INV_wrS _ _ (3 * (ch * ns + s) + 1) I1 ltac:(lia)) as HS.
  pose proof (ExecF.rng_sub' _ _ _ (out + (3 * (ch * ns + s) + 1)) 1 RO ltac:(lia)) as RW.
  st. clear HS RW.
  do_store I1 I2 (3 * (ch * ns + s) + 1).
  st. cnd false.
  st. st. cnd false.
  st.
  destruct (INV_shrS _ _ ch s 2 I2 Hch Hs ltac:(lia)) as (k4 & MK & SK).
  eapply pb_c5F; [ | exact MK | exact SK | rngF | intros v11 v12 ]; [ ufin | ]. clear MK SK.
  destruct (INV_shoS _ _ (3 * (ch * ns + s) + 2) I2 ltac:(lia)) as (k5 & MK & SK).
  pose proof (INV_rdS _ _ ch s 2 I2 Hch Hs ltac:(lia)) as RD.
  eapply pb_c6F; [ | | exact MK | exact SK | | exact RD | rngF | rngF | intros w11 w12 w31 W11 ]; [ ufin | lia | ufin | ].
  clear MK SK RD W11.
  pose proof (INV_wrS _ _ (3 * (ch * ns + s) + 2) I2 ltac:(lia)) as HS.
  pose proof (ExecF.rng_sub' _ _ _ (out + (3 * (ch * ns + s) + 2)) 1 RO ltac:(lia)) as RW.
  st. clear HS RW.
  do_store I2 I3 (3 * (ch * ns + s) + 2).
  st. st. st. st.
  brq BR.
  - eapply CONT; [ ufin | eapply INV_idx; [exact I3 | lia] ].
  - eapply (IH (Z.to_nat (ns - (s + 1))) ltac:(lia) (s + 1)).
    all: lazymatch goal with
         | |- IV _ _ => eapply INV_idx; [exact I3 | lia]
         | _ => first [ reflexivity | lia | ufin ]
         end.
Qed.

Lemma pl_outerF : forall (K : nat) (ch : Z) (m1 : word -> option byte)
    (x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  Z.to_nat (nch - ch) = K -> 0 <= ch < nch ->
  bv_unsigned x8 = out + 3 * (ch * ns) -> bv_unsigned x13 = nch -> bv_unsigned x14 = ns -> bv_unsigned x15 = ch ->
  bv_unsigned x16 = raw + 50 -> bv_unsigned x17 = 2 -> bv_unsigned x5 = 18446744073709551615 ->
  bv_unsigned x6 = 18446744073709551615 - (raw + 50) -> bv_unsigned x7 = 18446744073709551613 ->
  IV m1 (3 * (ch * ns)) ->
  ExecF.evtF rsegs RNG PC (STATE 0x81b40 m1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31).
Proof.
  induction K as [K IH] using lt_wf_ind.
  intros ch m1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
    HK Hch H8 H13 H14 H15 H16 H17 H5 H6 H7 I0.
  assert (ch * ns <= (nch - 1) * ns) by nia.
  assert (0 <= ch * ns) by nia.
  assert (nch <= 480 /\ ns <= 480) by nia.
  apply wv in H8, H13, H14, H15, H16, H17, H5, H6, H7. subst x8 x13 x14 x15 x16 x17 x5 x6 x7.
  st. st.
  eapply (pl_innerF ch) with (K := Z.to_nat (ns - 0)) (s := 0).
  all: lazymatch goal with
       | |- forall _ : word -> option byte, _ => idtac
       | |- IV _ _ => eapply INV_idx; [exact I0 | lia]
       | _ => first [ lia | reflexivity | ufin ]
       end.
  intros m2 y8 y9 y10 y11 y12 y28 y29 y30 y31 H29 I2. apply wv in H29. subst y29.
  st. st. st. st.
  brq BR.
  - assert (EN : nch * ns = ch * ns + ns) by (replace nch with (ch + 1) by lia; ring).
    st.
    destruct I2 as (HB2 & HF2 & ST2 & HW2 & MU2 & WM2 & HP2).
    eapply pl_exitF with (r := ns); [exact HF2 | exact ST2 | exact WM2 | rewrite OK; reflexivity | ].
    rewrite OK. split; [exact MU2|]. apply INV_outS. apply (INV_idx _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 (3 * (ch * ns + ns))); [|lia].
    exact (conj HB2 (conj HF2 (conj ST2 (conj HW2 (conj MU2 (conj WM2 HP2)))))).
  - eapply (IH (Z.to_nat (nch - (ch + 1))) ltac:(lia) (ch + 1)).
    all: lazymatch goal with
         | |- IV _ _ => eapply INV_idx; [exact I2 | nia]
         | _ => first [ reflexivity | lia | (rewrite unsigned_lit by nia; nia) | ufin ]
         end.
Qed.

End PLF.

Ltac curmemF k := lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => k mm end.

Theorem reac_decode_plain_le_holds_F : reac_frame_inspect_contract_F -> reac_decode_plain_le_contract_F.
Proof.
  intros HI. unfold reac_decode_plain_le_contract_F, REAC_DECODE_PLAIN_LE, REAC_DECODE_PLAIN_LE_D.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m bs raw mode out nch ns lo E0 E2 E3 Rraw Rmode Rout HB Rnch Rns HM ST LO DR DM HO APS1 APS2 CELLS SRW DC AR AM AO
    NR NM NO RSTK RGC RCK HRAW HMODE HOUT.
  subst a0 a2 a3.
  pose proof (u64_range sp) as Rsp.
  assert (Hlo : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold GOT_CELL_K, CELL_K in RGC, RCK.
  pose proof (conj HM CELLS) as PK. clear HM CELLS.
  carve_frame 48%nat ST.
  do 6 step.
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
    split; [unfold off_stk; rewrite unsigned_lit by lia; lia|].
    split; [replace (bv_unsigned sp + -48 - 16) with (bv_unsigned sp - 64) by lia; exact APS1|].
    split; [apply (app_win (bv_unsigned sp) 64); [lia | exact APS1 | exact APS2 | lia]|].
    split; [exact CELLS1|].
    split; [eapply shadow_rw_munch; [exact SRW | exact MU | exact WM | intros a Ha; apply win_shadow; assumption]|].
    split; [unfold off_stk, GOT_CELL_K; rewrite unsigned_lit by lia; lia|].
    split; [unfold off_stk, CELL_K; rewrite unsigned_lit by lia; lia|].
    eapply addr_win; [exact AR | exact MU | lia | exact APS1 | exact APS2]. }
  { unfold REAC_FRAME_INSPECT_FRAME. rewrite unsigned_lit by lia. apply (ExecF.rng_sub _ _ _ _ _ RSTK); lia. }
  { intros L. destruct (HRAW L) as [RR RSR]. rewrite (unsigned_lit raw) by lia.
    split; [exact RGC|]. split; [exact RCK|].
    split; [apply (ExecF.rng_sub _ _ _ _ _ RR); lia|].
    split; [apply (ExecF.rng_sub _ _ _ _ _ RR); lia|].
    split; apply (ExecF.rng_sub _ _ _ _ _ RSR); Z.div_mod_to_equations; lia. }
  intros ms' (a1' & a2' & a3' & a4' & m2 & -> & MU2 & WM2 & ST2).
  replace (ret_pc (Z_to_bv 64 531136)) with (Z_to_bv 64 531136) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  unfold REAC_FRAME_INSPECT_FRAME in MU2, ST2. rewrite unsigned_lit in MU2, ST2 by lia.
  assert (MU0 : munch [(bv_unsigned sp + -64, bv_unsigned sp)] m m2)
    by (eapply munch_trans; [eapply munch_wider; [ | | exact MU]; lia | eapply munch_wider; [ | | exact MU2]; lia]).
  assert (WM0 : wmono rsegs m m2) by (eapply wmono_trans; [exact WM | exact WM2]).
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -48)
     [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 junk))))); C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    by (eapply rw_cells_transport; [exact FR | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize]; split; [lia | exact I]]).
  clear FR MU2 WM2 ST MU WM CELLS1.
  step. rewrite inspect_valid_bit. step. step.
  destruct (inspect_wf (bv_unsigned a1) bs) eqn:W.
  2:{ if_true.
      assert (PO : plain_ok (bv_unsigned a1) bs nch ns = false) by (unfold plain_ok; rewrite W; reflexivity).
      eapply pl_exitF with (r := -1).
      all: first [ exact FR2 | exact ST2 | exact WM0 | lia | exact RSTK
                 | rewrite PO; first [reflexivity | exact MU0] ]. }
  if_false.
  assert (L : bv_unsigned a1 = 1492) by (unfold inspect_wf in W; rewrite !andb_true_iff, !Z.eqb_eq in W; tauto).
  destruct (HB L) as [LEN BB]. specialize (DR L). specialize (AR L). specialize (AM eq_refl).
  specialize (NR L). destruct (NM eq_refl) as [NM0 NM4].
  destruct (HRAW L) as [RR RSR]. destruct (HMODE eq_refl) as [RM RSM].
  unfold off_stk in DR, DM.
  pose proof (bytes_at_bound _ _ _ _ BB) as BBB. rewrite LEN in BBB.
  apply bytes_at_app in HM. destruct HM as [HM1 HM2]. rewrite length_le4 in HM2.
  replace (mode + 4 + Z.of_nat 4) with (mode + 8) in HM2 by lia.
  apply (bytes_tp m m2 _ _ _ _ MU0) in HM1; [| rewrite length_le4; lia].
  apply (bytes_tp m m2 _ _ _ _ MU0) in HM2; [| rewrite length_le4; lia].
  pose proof (bytes_at_bound _ _ _ _ HM2) as HMB. rewrite length_le4 in HMB.
  pose proof (rd_all _ _ _ HM1) as HR1. rewrite length_le4 in HR1.
  pose proof (rd_all _ _ _ HM2) as HR2. rewrite length_le4 in HR2.
  assert (MU0' : munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m2)
    by (eapply munch_wider; [ | | exact MU0]; lia).
  assert (AM2 : addressable m2 (mode + 4) 8)
    by (eapply addr_win; [exact AM | exact MU0' | lia | exact APS1 | exact APS2]).
  step. cnd false.
  step. step. cnd false.
  step. cnd false.
  st. rewrite (land3_0 mode) by lia.
  step. cnd false.
  destruct (addr_four m2 (mode + 4) 8 (mode + 4) AM2 ltac:(lia) ltac:(lia)) as (k1 & MK1 & SK1).
  eapply pb_m1F; [ rewrite unsigned_lit by lia; reflexivity | lia | exact MK1 | exact SK1
    | exact (rng_shadow_byte _ (mode + 4) (mode + 11) (mode + 4) RSM ltac:(lia) ltac:(lia)) | intros y11 y12 y13 ].
  destruct (addr_four m2 (mode + 4) 8 (mode + 8) AM2 ltac:(lia) ltac:(lia)) as (k2 & MK2 & SK2).
  eapply pb_m2F; [ rewrite unsigned_lit by lia; reflexivity | lia | exact MK2 | exact SK2
    | rewrite unsigned_lit by lia; exact HR1
    | exact (rng_shadow_byte _ (mode + 4) (mode + 11) (mode + 8) RSM ltac:(lia) ltac:(lia))
    | rewrite unsigned_lit by lia; apply (ExecF.rng_sub _ _ _ _ _ RM); lia
    | intros z11 z12 z14 Z11 ].
  apply wv in Z11. subst z11.
  rewrite sx32_lit by lia.
  step. rewrite lts0_lit by lia. brq BN.
  2:{ assert (PO : plain_ok (bv_unsigned a1) bs nch ns = false)
        by (apply not_true_iff_false; rewrite plain_ok_spec; lia).
      eapply pl_exitF with (r := -1).
      all: first [ exact FR2 | exact ST2 | exact WM0 | lia | exact RSTK
                 | rewrite PO; first [reflexivity | exact MU0] ]. }
  pose proof (ExecF.rng_sub' _ _ _ (mode + 8) 4 RM ltac:(lia)) as RM8.
  step. rewrite sx32_lit by lia.
  clear RM8.
  step. rewrite lts0_lit by lia. brq BS.
  2:{ assert (PO : plain_ok (bv_unsigned a1) bs nch ns = false)
        by (apply not_true_iff_false; rewrite plain_ok_spec; lia).
      eapply pl_exitF with (r := -1).
      all: first [ exact FR2 | exact ST2 | exact WM0 | lia | exact RSTK
                 | rewrite PO; first [reflexivity | exact MU0] ]. }
  assert (0 <= ns * nch < 2^62) by nia.
  step. step. step. rewrite (unsigned_lit ns), (unsigned_lit nch) by lia. brq BM.
  { assert (PO : plain_ok (bv_unsigned a1) bs nch ns = false)
        by (apply not_true_iff_false; rewrite plain_ok_spec; lia).
      eapply pl_exitF with (r := -1).
      all: first [ exact FR2 | exact ST2 | exact WM0 | lia | exact RSTK
                 | rewrite PO; first [reflexivity | exact MU0] ]. }
  assert (PO : plain_ok (bv_unsigned a1) bs nch ns = true) by (rewrite plain_ok_spec; split; [exact W | lia]).
  destruct (HO PO) as (HW & HoutN & DOR & DOS). specialize (AO PO). specialize (NO PO). unfold off_stk in DOS.
  destruct (HOUT PO) as [RO RSO].
  do 6 step.
  destruct (geom_le nch ns BN BS ltac:(lia)) as (G1 & G2).
  assert (I0 : INV ra sp s0 s1 s2 s3 m bs raw out nch ns lo
                 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 junk))))) m2 0).
  { split; [|split; [exact FR2|split; [exact ST2|split; [|split; [|split; [exact WM0|]]]]]].
    - eapply bytes_tp; [exact MU0' | rewrite LEN; lia | exact BB].
    - eapply wr_at_transport; [exact HW | exact WM0].
    - apply munch_extend. exact MU0.
    - intros i Hi. lia. }
  eapply pl_outerF with (K := Z.to_nat (nch - 0)) (ch := 0) (ra := ra) (sp := sp) (s0 := s0) (s1 := s1) (s2 := s2)
    (s3 := s3) (a1 := a1) (m := m) (bs := bs) (raw := raw) (mode := mode) (out := out) (nch := nch) (ns := ns) (lo := lo)
    (jk := firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 junk))))).
  all: first [ assumption | reflexivity | lia
             | (eapply INV_idx; [exact I0 | lia])
             | (intros x Hx; apply (app_win (bv_unsigned sp) 64); [lia | exact APS1 | exact APS2 | lia])
             | ufin ].
Qed.

(* The twin implies the original: take the footprint that allows every access. *)
Theorem reac_decode_plain_le_holds_of_F : reac_frame_inspect_contract_F -> reac_decode_plain_le_contract.
Proof.
  intros HI. unfold reac_decode_plain_le_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m bs raw mode out nch ns lo E0 E2 E3 Rraw Rmode Rout HB Rnch Rns HM ST LO DR DM HO APS1 APS2 CELLS SRW DC AR AM AO
    NR NM NO.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  pose proof (bytes_at_bound _ _ _ _ HM) as HMB. rewrite length_app, !length_le4 in HMB.
  refine (reac_decode_plain_le_holds_F HI ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5
            s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs raw mode out nch ns lo E0 E2 E3 Rraw Rmode Rout HB Rnch Rns HM ST
            LO DR DM HO APS1 APS2 CELLS SRW DC AR AM AO NR NM NO _ _ _ _ _ _).
  - apply ExecF.rng_all; unfold REAC_DECODE_PLAIN_LE_D in *; lia.
  - apply ExecF.rng_all; unfold GOT_CELL_K; lia.
  - apply ExecF.rng_all; unfold CELL_K; lia.
  - intros L. destruct (HB L) as [LEN BB]. pose proof (bytes_at_bound _ _ _ _ BB) as BBB. rewrite LEN in BBB.
    clear - Rraw BBB. split; apply ExecF.rng_all; unfold ASAN_K; Z.div_mod_to_equations; lia.
  - intros _. clear - Rmode HMB. split; apply ExecF.rng_all; unfold ASAN_K; Z.div_mod_to_equations; lia.
  - intros D. destruct (HO D) as (_ & HN & _). clear - Rout HN.
    split; apply ExecF.rng_all; unfold ASAN_K; Z.div_mod_to_equations; lia.
Qed.
