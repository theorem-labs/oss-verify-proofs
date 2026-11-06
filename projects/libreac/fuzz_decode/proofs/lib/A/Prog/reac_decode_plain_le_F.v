From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import AsanKA AsanKAProof reac_frame_inspect_c
  reac_frame_inspect_F_c reac_decode_plain_le_c reac_decode_plain_le_F_c ReacDecodeLib reac_decode_plain_le reac_decode_F.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Footprint twin of reac_decode_plain_le_holds (A image, entry 0x816b0, frame 64 bytes). The proof follows
   reac_decode_plain_le.v step for step with StepF's step; each step's data accesses are discharged from the
   [rng] premises. The pure helper lemmas of reac_decode_plain_le.v (plain_ok_spec, plain_byte_at, idx_bounds,
   geom_le, win_out, win_shadow, addr_win) are reused by import, as are rng_one and rng_shadow_one of
   reac_decode_F.v; the lemmas whose conclusion is a run (the pl ones) and the invariant they carry are the F twins
   below. *)

Lemma pl_c1F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x10 = A -> mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k -> (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  ExecF.rng RNG (A / 8 + ASAN_K) 1 ->
  (forall y11 y12 : word, evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y11 y12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81774) fc None mm (seg_rom rsegs))) ->
  evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81764) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k A EA M SK RGS CONT.
  pose proof (u64_range x10) as R10. unfold ASAN_K in M, RGS.
  step. gen_shr x10 g G. rewrite EA in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, EA, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

Lemma pl_c2F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (A D : Z),
  bv_unsigned x8 + bv_unsigned x7 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k -> (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  bv_unsigned x28 + -2 = D -> mrd rsegs mm (wa D) = Some b ->
  ExecF.rng RNG (A / 8 + ASAN_K) 1 ->
  ExecF.rng RNG D 1 ->
  (forall y11 y29 y30 : word, bv_unsigned y11 = A -> evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y11 (zxb b) x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 y29 y30 x31) F (Z_to_bv 64 0x8178c) fc None mm (seg_rom rsegs))) ->
  evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81774) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k b A D EA RA M SK ED MD RGS RGD CONT.
  pose proof (u64_range x8) as R8. pose proof (u64_range x7) as R7. unfold ASAN_K in M, RGS.
  step. gen_add x8 x7 w U. rewrite EA in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw mm x28 (-2) _ _ MD ED) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT. exact U.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, U, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT. exact U.
Qed.

Lemma pl_c3F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x10 + 1 = A -> A < 2^64 -> mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  ExecF.rng RNG (A / 8 + ASAN_K) 1 ->
  (forall y12 y29 y30 : word, evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 y12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 y29 y30 x31) F (Z_to_bv 64 0x817a4) fc None mm (seg_rom rsegs))) ->
  evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81790) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k A EA RA M SK RGS CONT.
  pose proof (u64_range x10) as R10. unfold ASAN_K in M, RGS.
  step. gen_addi x10 w U. rewrite EA in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, U, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

Lemma pl_c4F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (A D : Z),
  bv_unsigned x11 + 1 = A -> A < 2^64 -> mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  bv_unsigned x28 + -1 = D -> mrd rsegs mm (wa D) = Some b ->
  ExecF.rng RNG (A / 8 + ASAN_K) 1 ->
  ExecF.rng RNG D 1 ->
  (forall y12 y30 y31 : word, evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 y12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 (zxb b) y30 y31) F (Z_to_bv 64 0x817bc) fc None mm (seg_rom rsegs))) ->
  evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x817a4) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k b A D EA RA M SK ED MD RGS RGD CONT.
  pose proof (u64_range x11) as R11. unfold ASAN_K in M, RGS.
  step. gen_addi x11 w U. rewrite EA in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw mm x28 (-1) _ _ MD ED) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, U, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

Lemma pl_c5F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x10 + 2 = A -> A < 2^64 -> mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  ExecF.rng RNG (A / 8 + ASAN_K) 1 ->
  (forall y12 y29 y30 : word, evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 y12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 y29 y30 x31) F (Z_to_bv 64 0x817d4) fc None mm (seg_rom rsegs))) ->
  evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x817c0) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k A EA RA M SK RGS CONT.
  pose proof (u64_range x10) as R10. unfold ASAN_K in M, RGS.
  step. gen_addi x10 w U. rewrite EA in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, U, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

Lemma pl_c6F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (A D : Z),
  bv_unsigned x11 + 2 = A -> A < 2^64 -> mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  bv_unsigned x28 = D -> mrd rsegs mm (wa D) = Some b ->
  ExecF.rng RNG (A / 8 + ASAN_K) 1 ->
  ExecF.rng RNG D 1 ->
  (forall y12 y30 y31 : word, evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 y12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 (zxb b) y30 y31) F (Z_to_bv 64 0x817ec) fc None mm (seg_rom rsegs))) ->
  evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x817d4) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k b A D EA RA M SK ED MD RGS RGD CONT.
  pose proof (u64_range x11) as R11. unfold ASAN_K in M, RGS.
  step. gen_addi x11 w U. rewrite EA in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw0 mm x28 _ _ MD ED) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, U, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

Lemma pl_m1F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x18 + 4 = A -> A < 2^64 -> mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 + 3 < bv_signed k) ->
  ExecF.rng RNG (A / 8 + ASAN_K) 1 ->
  (forall y11 y12 y13 : word, evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y11 y12 y13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81704) fc None mm (seg_rom rsegs))) ->
  evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x816f0) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k A EA RA M SK RGS CONT.
  pose proof (u64_range x18) as R18. unfold ASAN_K in M, RGS.
  step. gen_addi x18 w U. rewrite EA in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. step. rewrite land7, U, (lts_sm (A mod 8 + 3) k ltac:(lia)), (proj2 (Z.ltb_lt _ _) C).
    apply CONT.
Qed.

Lemma pl_m2F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (v : word) (A : Z),
  bv_unsigned x18 + 8 = A -> A < 2^64 -> mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 + 3 < bv_signed k) ->
  ov_read_bytes rsegs mm (Z_to_bv 64 (bv_unsigned x18 + 4)) 4 = Some (le4 v) ->
  ExecF.rng RNG (A / 8 + ASAN_K) 1 ->
  ExecF.rng RNG (A - 4) 4 ->
  (forall y11 y12 y14 : word, bv_unsigned y11 = A -> evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y11 y12 (zx32 v) y14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x8171c) fc None mm (seg_rom rsegs))) ->
  evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81704) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k v A EA RA M SK RV RGS RGD CONT.
  pose proof (u64_range x18) as R18. unfold ASAN_K in M, RGS.
  step. gen_addi x18 w U. rewrite EA in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
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

Section PLF.
Variable RNG : ExecF.footprint.
Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a1 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (raw mode out nch ns lo : Z)
  (jk : list byte).

Definition PostCF : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1
                  (Z_to_bv 64 (if plain_ok (bv_unsigned a1) bs nch ns then ns else -1))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp) /\
    (if plain_ok (bv_unsigned a1) bs nch ns
     then munch [(bv_unsigned sp - 64, bv_unsigned sp); (out, out + 3 * nch * ns)] m m' /\
          bytes_at rsegs m' out (plain_out bs nch ns)
     else munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m').

Local Notation SP := (bv_unsigned sp).
Local Notation FR mk := (rw_cells rsegs mk (bv_unsigned sp + -48) [CB 8 jk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
Local Notation N := (3 * nch * ns).
Local Notation STATE pc mm x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 :=
  (MS (mkR (Z_to_bv 64 0x816e4) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 x7 x8 (Z_to_bv 64 raw)
        x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 mode) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11
        x28 x29 x30 x31)
      F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

Hypothesis Hsp : lo + 64 <= SP.
Hypothesis Hlo : 0 <= lo.
(* the stack window of this frame and of the callee's frame under it *)
Hypothesis RGW : ExecF.rng RNG (SP - 64) 64.

Lemma pl_exitF : forall (m1 : word -> option byte) (r : Z)
    (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word),
  FR m1 -> stk rsegs m1 lo (SP + -48) -> wmono rsegs m m1 ->
  r = (if plain_ok (bv_unsigned a1) bs nch ns then ns else -1) ->
  (if plain_ok (bv_unsigned a1) bs nch ns
   then munch [(SP + -64, SP); (out, out + N)] m m1 /\ bytes_at rsegs m1 out (plain_out bs nch ns)
   else munch [(SP + -64, SP)] m m1) ->
  evtF rsegs RNG PostCF (MS (mkR x1 (Z_to_bv 64 (SP + -48)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16
      x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x81864) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 r x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 HF ST WM Er HM.
  pose proof (u64_range sp) as Rsp.
  do 7 step.
  apply evtF_done. unfold PostCF. exists x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, m1.
  split; [subst r; reflexivity|]. split; [exact WM|]. split.
  - pose proof (stk_release rsegs m1 lo (SP + -48) _ ST HF ltac:(lia)) as ST2.
    cbn [cells_size csize Nat.add] in ST2. replace (SP + -48 + Z.of_nat 48) with SP in ST2 by lia. exact ST2.
  - replace (SP - 64) with (SP + -64) by lia. exact HM.
Qed.

Hypothesis Hlen : length bs = 1492%nat.
Hypothesis Hraw : 0 <= raw.
Hypothesis Hraw2 : raw + 1492 <= 2^64.
Hypothesis Hout : 0 <= out.
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
(* the input buffer and its shadow bytes, the output buffer and its shadow bytes *)
Hypothesis RGR : ExecF.rng RNG raw 1492.
Hypothesis RGRS : ExecF.rng RNG (shadow_addr raw) (shadow_addr (raw + 1492 - 1) - shadow_addr raw + 1).
Hypothesis RGO : ExecF.rng RNG out N.
Hypothesis RGOS : ExecF.rng RNG (shadow_addr out) (shadow_addr (out + N - 1) - shadow_addr out + 1).

Lemma rngrPF : forall a, raw <= a < raw + 1492 -> ExecF.rng RNG a 1.
Proof. intros a Ha. eapply rng_one; [exact RGR | exact Ha]. Qed.

Lemma rngsPF : forall a, raw <= a < raw + 1492 -> ExecF.rng RNG (a / 8 + ASAN_K) 1.
Proof. intros a Ha. eapply rng_shadow_one; [exact RGRS | exact Ha]. Qed.

Lemma rngosPF : forall a, out <= a < out + N -> ExecF.rng RNG (a / 8 + ASAN_K) 1.
Proof. intros a Ha. eapply rng_shadow_one; [exact RGOS | exact Ha]. Qed.

Definition INVF (mk : word -> option byte) (j : Z) : Prop :=
  bytes_at rsegs mk raw bs /\ FR mk /\ stk rsegs mk lo (SP + -48) /\ wr_at rsegs mk out N /\
  munch [(SP + -64, SP); (out, out + N)] m mk /\ wmono rsegs m mk /\
  (forall i, 0 <= i < j -> mrd rsegs mk (Z_to_bv 64 (out + i)) = Some (plain_byte bs nch ns i)).

Lemma INV_idxF : forall mk j j', INVF mk j -> j = j' -> INVF mk j'.
Proof. intros; subst; assumption. Qed.

Lemma INV_addrF : forall mk j p n, INVF mk j -> addressable m p n -> addressable mk p n.
Proof.
  intros mk j p n (_ & _ & _ & _ & MU & _) A. eapply addr_munch; [exact A | exact MU |].
  intros i Hi. destruct A as (_ & _ & _ & HA). destruct (HA i Hi) as (Ha & _).
  pose proof (shadow_not_app _ Ha) as NA. cbn [outside]. split; [|split; [|exact I]].
  - intros W. apply NA, APW. lia.
  - intros W. apply NA. destruct AO as (_ & _ & _ & HO). destruct (HO ((p + i) / 8 + ASAN_K - out) ltac:(lia)) as (Ho & _).
    replace (out + ((p + i) / 8 + ASAN_K - out)) with ((p + i) / 8 + ASAN_K) in Ho by lia. exact Ho.
Qed.

Lemma INV_rdF : forall mk j ch s k, INVF mk j -> 0 <= ch < nch -> 0 <= s < ns -> 0 <= k < 3 ->
  mrd rsegs mk (wa (raw + (50 + 3 * (s * nch + ch) + k))) = Some (plain_byte bs nch ns (3 * (ch * ns + s) + k)).
Proof.
  intros mk j ch s k (HB & _) Hch Hs Hk. rewrite plain_byte_at by lia.
  assert (s * nch <= (ns - 1) * nch) by nia.
  pose proof (bytes_nth mk raw bs (Z.to_nat (50 + 3 * (s * nch + ch) + k)) HB ltac:(rewrite Hlen; lia)) as R.
  rewrite Z2Nat.id in R by lia. exact R.
Qed.

Lemma INV_shrF : forall mk j ch s k, INVF mk j -> 0 <= ch < nch -> 0 <= s < ns -> 0 <= k < 3 ->
  exists kb, mrd rsegs mk (wa ((raw + (50 + 3 * (s * nch + ch) + k)) / 8 + ASAN_K)) = Some kb /\
    (bv_signed kb = 0 \/ (raw + (50 + 3 * (s * nch + ch) + k)) mod 8 < bv_signed kb).
Proof.
  intros mk j ch s k I Hch Hs Hk.
  assert (s * nch <= (ns - 1) * nch) by nia.
  destruct (addr_one mk raw 1492 (50 + 3 * (s * nch + ch) + k) (INV_addrF mk j raw 1492 I AR) ltac:(lia))
    as (_ & kb & M & S). exists kb. split; assumption.
Qed.

Lemma INV_shoF : forall mk j q, INVF mk j -> 0 <= q < N ->
  exists kb, mrd rsegs mk (wa ((out + q) / 8 + ASAN_K)) = Some kb /\
    (bv_signed kb = 0 \/ (out + q) mod 8 < bv_signed kb).
Proof.
  intros mk j q I Hq.
  destruct (addr_one mk out N q (INV_addrF mk j out N I AO) Hq) as (_ & kb & M & S). exists kb. split; assumption.
Qed.

Lemma INV_wrF : forall mk j q, INVF mk j -> 0 <= q < N -> store_ok rsegs mk (Z_to_bv 64 (out + q)) 1 = true.
Proof.
  intros mk j q (_ & _ & _ & HW & _) Hq. change (Z_to_bv 64 (out + q)) with (wa (out + q)).
  apply (wr_at_store_ok rsegs mk out N q 1 HW); lia.
Qed.

Lemma INV_storeF : forall mk j0 j j2, INVF mk j0 -> j0 = j -> 0 <= j < N -> j2 = j + 1 ->
  INVF (write_to_mem mk (Z_to_bv 64 (out + j)) [plain_byte bs nch ns j]) j2.
Proof.
  intros mk j0 j j2 (HB & HF & ST & HW & MU & WM & HP) E Hj E2. subst j0 j2.
  change (Z_to_bv 64 (out + j)) with (wa (out + j)).
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - apply bytes_at_write_other; [exact HB | lia | cbn; lia | rewrite Hlen; cbn; lia].
  - apply rw_cells_frame; [exact HF | lia | cbn; lia | cbn; lia].
  - apply stk_write; [exact ST | lia | cbn; lia].
  - apply wr_at_write. exact HW.
  - apply munch_write; [exact MU | lia | cbn; lia | cbn [inside]; cbn; lia].
  - apply wmono_write. exact WM.
  - intros i Hi. change (wa (out + j)) with (Z_to_bv 64 (out + j)).
    rewrite mrd_write1 by lia.
    destruct (Z.eqb_spec (out + i) (out + j)) as [E|E].
    + replace i with j by lia. reflexivity.
    + apply HP. lia.
Qed.

Lemma INV_outF : forall mk, INVF mk N -> bytes_at rsegs mk out (plain_out bs nch ns).
Proof.
  intros mk (_ & _ & _ & _ & _ & _ & HP). unfold plain_out.
  apply bytes_at_of_fun; [lia | lia |]. intros i Hi. apply HP. lia.
Qed.

Ltac do_storePF I0 I1 jj :=
  rewrite ?le1_zxb;
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mk ?a ?b) _) =>
    assert (I1 : INVF (write_to_mem mk a b) (jj + 1)) by (eapply INV_storeF; [exact I0 | lia | lia | lia]);
    let m2 := fresh "m" in set (m2 := write_to_mem mk a b) in *; clearbody m2; clear I0
  end.

Lemma pl_innerF : forall (ch : Z) (x5 x6 x8 x13 x14 x15 x16 x17 : word),
  0 <= ch < nch -> bv_unsigned x5 = 3 * nch -> bv_unsigned x6 = raw + 52 + 3 * ch ->
  bv_unsigned x8 = out + 3 * (ch * ns) -> x13 = Z_to_bv 64 nch -> x14 = Z_to_bv 64 ns -> bv_unsigned x15 = ch ->
  bv_unsigned x16 = raw + 50 + 3 * ch -> bv_unsigned x17 = 3 * ns ->
  forall (K : nat) (s : Z) (m1 : word -> option byte) (x7 x10 x11 x12 x28 x29 x30 x31 : word),
  Z.to_nat (ns - s) = K -> 0 <= s < ns ->
  bv_unsigned x7 = 3 * s -> bv_unsigned x10 = raw + 50 + 3 * ch + 3 * nch * s ->
  bv_unsigned x28 = raw + 52 + 3 * ch + 3 * nch * s ->
  INVF m1 (3 * (ch * ns + s)) ->
  (forall (m2 : word -> option byte) (y7 y10 y11 y12 y28 y29 y30 y31 : word), bv_unsigned y7 = 3 * ns ->
     INVF m2 (3 * (ch * ns + ns)) ->
     evtF rsegs RNG PostCF (STATE 0x8184c m2 x5 x6 y7 x8 y10 y11 y12 x13 x14 x15 x16 x17 y28 y29 y30 y31)) ->
  evtF rsegs RNG PostCF (STATE 0x81764 m1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31).
Proof.
  intros ch x5 x6 x8 x13 x14 x15 x16 x17 Hch H5 H6 H8 E13 E14 H15 H16 H17 K.
  induction K as [K IH] using lt_wf_ind.
  intros s m1 x7 x10 x11 x12 x28 x29 x30 x31 HK Hs H7 H10 H28 I0 CONT.
  destruct (idx_bounds ch s nch ns Hch Hs) as (P1 & P2 & P3 & P4 & P5 & _).
  destruct (INV_shrF m1 _ ch s 0 I0 Hch Hs ltac:(lia)) as (k0 & MK & SK).
  eapply pl_c1F; [ | exact MK | exact SK | apply rngsPF; rgl | intros p11 p12 ]; [ lia | ]. clear MK SK.
  destruct (INV_shoF m1 _ (3 * (ch * ns + s) + 0) I0 ltac:(lia)) as (k1 & MK & SK).
  pose proof (INV_rdF m1 _ ch s 0 I0 Hch Hs ltac:(lia)) as RD.
  eapply pl_c2F; [ | | exact MK | exact SK | | exact RD | apply rngosPF; rgl | apply rngrPF; rgl
    | intros q11 q29 q30 Q11 ]; [ lia | lia | lia | ].
  clear MK SK RD. apply wv in Q11. subst q11.
  pose proof (INV_wrF m1 _ (3 * (ch * ns + s) + 0) I0 ltac:(lia)) as HS.
  step. clear HS.
  do_storePF I0 I1 (3 * (ch * ns + s) + 0).
  destruct (INV_shrF _ _ ch s 1 I1 Hch Hs ltac:(lia)) as (k2 & MK & SK).
  eapply pl_c3F; [ | | exact MK | exact SK | apply rngsPF; rgl | intros r12 r29 r30 ]; [ lia | lia | ].
  clear MK SK.
  destruct (INV_shoF _ _ (3 * (ch * ns + s) + 1) I1 ltac:(lia)) as (k3 & MK & SK).
  pose proof (INV_rdF _ _ ch s 1 I1 Hch Hs ltac:(lia)) as RD.
  eapply pl_c4F; [ | | exact MK | exact SK | | exact RD | apply rngosPF; rgl | apply rngrPF; rgl
    | intros u12 u30 u31 ];
    [ rewrite unsigned_lit by lia; lia | lia | lia | ]. clear MK SK RD.
  pose proof (INV_wrF _ _ (3 * (ch * ns + s) + 1) I1 ltac:(lia)) as HS.
  step. clear HS.
  do_storePF I1 I2 (3 * (ch * ns + s) + 1).
  destruct (INV_shrF _ _ ch s 2 I2 Hch Hs ltac:(lia)) as (k4 & MK & SK).
  eapply pl_c5F; [ | | exact MK | exact SK | apply rngsPF; rgl | intros v12 v29 v30 ]; [ lia | lia | ].
  clear MK SK.
  destruct (INV_shoF _ _ (3 * (ch * ns + s) + 2) I2 ltac:(lia)) as (k5 & MK & SK).
  pose proof (INV_rdF _ _ ch s 2 I2 Hch Hs ltac:(lia)) as RD.
  eapply pl_c6F; [ | | exact MK | exact SK | | exact RD | apply rngosPF; rgl | apply rngrPF; rgl
    | intros w12 w30 w31 ];
    [ rewrite unsigned_lit by lia; lia | lia | lia | ]. clear MK SK RD.
  pose proof (INV_wrF _ _ (3 * (ch * ns + s) + 2) I2 ltac:(lia)) as HS.
  step. clear HS.
  do_storePF I2 I3 (3 * (ch * ns + s) + 2).
  apply wv in H5, H7, H10, H28, H17. subst x5 x7 x10 x28 x17 x13 x14.
  step. step. step. step.
  brq BR.
  - eapply CONT; [rewrite unsigned_lit by lia; lia | eapply INV_idxF; [exact I3 | lia]].
  - step.
    eapply (IH (Z.to_nat (ns - (s + 1))) ltac:(lia) (s + 1));
      [ reflexivity | lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
      | rewrite unsigned_lit by lia; lia | eapply INV_idxF; [exact I3 | lia] | exact CONT ].
Qed.

Lemma pl_outerF : forall (K : nat) (ch : Z) (m1 : word -> option byte)
    (x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  Z.to_nat (nch - ch) = K -> 0 <= ch < nch ->
  bv_unsigned x5 = 3 * nch -> bv_unsigned x6 = raw + 52 + 3 * ch -> bv_unsigned x8 = out + 3 * (ch * ns) ->
  x13 = Z_to_bv 64 nch -> x14 = Z_to_bv 64 ns -> bv_unsigned x15 = ch -> bv_unsigned x16 = raw + 50 + 3 * ch ->
  bv_unsigned x17 = 3 * ns ->
  INVF m1 (3 * (ch * ns)) ->
  evtF rsegs RNG PostCF (STATE 0x81758 m1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31).
Proof.
  induction K as [K IH] using lt_wf_ind.
  intros ch m1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HK Hch H5 H6 H8 E13 E14 H15 H16 H17 I0.
  destruct (idx_bounds ch 0 nch ns Hch ltac:(lia)) as (P1 & P2 & _ & _ & _ & P6).
  destruct (geom_le nch ns Hnch Hns H480) as (G1 & G2).
  pose proof H6 as H6'. pose proof H16 as H16'.
  apply wv in H6', H16'. subst x6 x16.
  step. step. step.
  eapply (pl_innerF ch) with (K := Z.to_nat (ns - 0)) (s := 0);
    [ lia | exact H5 | rewrite unsigned_lit by lia; lia | exact H8 | exact E13 | exact E14 | exact H15
    | rewrite unsigned_lit by lia; lia | exact H17 | reflexivity | lia | rewrite unsigned_lit by lia; lia
    | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | eapply INV_idxF; [exact I0 | lia] | ].
  intros m2 y7 y10 y11 y12 y28 y29 y30 y31 H7' I2.
  apply wv in H7', H8, H15, H17, H5. subst y7 x8 x15 x17 x5 x13 x14.
  step. step. step. step. step.
  brq BR.
  - assert (EN : nch * ns = ch * ns + ns) by (replace nch with (ch + 1) by lia; ring).
    step.
    destruct I2 as (HB2 & HF2 & ST2 & HW2 & MU2 & WM2 & HP2).
    eapply pl_exitF with (r := ns); [exact HF2 | exact ST2 | exact WM2 | rewrite OK; reflexivity | ].
    rewrite OK. split; [exact MU2|]. apply INV_outF. apply (INV_idxF m2 (3 * (ch * ns + ns))); [|lia].
    exact (conj HB2 (conj HF2 (conj ST2 (conj HW2 (conj MU2 (conj WM2 HP2)))))).
  - eapply (IH (Z.to_nat (nch - (ch + 1))) ltac:(lia) (ch + 1));
      [ reflexivity | lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
      | rewrite unsigned_lit by lia; lia | reflexivity | reflexivity | rewrite unsigned_lit by lia; lia
      | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | eapply INV_idxF; [exact I2 | lia] ].
Qed.

End PLF.

Theorem reac_decode_plain_le_holds_F : reac_frame_inspect_contract_F -> reac_decode_plain_le_contract_F.
Proof.
  intros HI. unfold reac_decode_plain_le_contract_F, REAC_DECODE_PLAIN_LE, REAC_DECODE_PLAIN_LE_D.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m bs raw mode out nch ns lo E0 E2 E3 Rraw Rmode Rout HB Rnch Rns HM ST LO DR DM HO APS1 APS2 CELLS SRW DC AR AM AO
    RGW RGC RCK RGR RGRS RGM RGMS RGO RGOS.
  subst a0 a2 a3.
  unfold GOT_CELL_K in RGC. unfold CELL_K in RCK.
  pose proof (u64_range sp) as Rsp.
  assert (Hlo : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
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
  curmemF ltac:(fun mm => eapply evtF_cut;
    [eapply (HI RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm bs lo) |]).
  { rewrite unsigned_lit by lia. exact ST. }
  { unfold REAC_FRAME_INSPECT_FRAME. rewrite unsigned_lit by lia. lia. }
  { unfold REAC_FRAME_INSPECT_FRAME. intros L. destruct (HB L) as [LEN BB]. specialize (DR L). specialize (AR L).
    unfold off_stk in DR. rewrite (unsigned_lit raw) by lia. rewrite unsigned_lit by lia.
    pose proof (bytes_at_bound _ _ _ _ BB) as BBB. rewrite LEN in BBB.
    split; [exact LEN|]. split; [eapply bytes_tp; [exact MU | rewrite LEN; lia | exact BB]|].
    split; [unfold off_stk; rewrite unsigned_lit by lia; lia|].
    split; [replace (bv_unsigned sp + -48 - 16) with (bv_unsigned sp - 64) by lia; exact APS1|].
    split; [apply (app_win (bv_unsigned sp) 64); [lia | exact APS1 | exact APS2 | lia]|].
    split; [exact CELLS1|].
    split; [eapply shadow_rw_munch; [exact SRW | exact MU | exact WM | intros a Ha; apply win_shadow; assumption]|].
    split; [unfold off_stk, GOT_CELL_K; rewrite unsigned_lit by lia; lia|].
    split; [unfold off_stk, CELL_K; rewrite unsigned_lit by lia; lia|].
    eapply addr_win; [exact AR | exact MU | lia | exact APS1 | exact APS2]. }
  { unfold REAC_FRAME_INSPECT_FRAME. rewrite unsigned_lit by lia.
    eapply ExecF.rng_sub; [exact RGW | lia | lia]. }
  { intros L. exact RGC. }
  { intros L. exact RCK. }
  { intros L. rewrite unsigned_lit by lia. exact (RGR L). }
  { intros L. rewrite (unsigned_lit raw) by lia. exact (RGRS L). }
  intros ms' (a1' & a2' & a3' & a4' & m2 & -> & MU2 & WM2 & ST2).
  replace (ret_pc (Z_to_bv 64 530148)) with (Z_to_bv 64 530148) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
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
      all: first [ exact FR2 | exact ST2 | exact WM0 | assumption | lia
                 | rewrite PO; first [reflexivity | exact MU0] ]. }
  if_false.
  assert (L : bv_unsigned a1 = 1492) by (unfold inspect_wf in W; rewrite !andb_true_iff, !Z.eqb_eq in W; tauto).
  destruct (HB L) as [LEN BB]. specialize (DR L). specialize (AR L). specialize (AM eq_refl).
  specialize (RGR L). specialize (RGRS L). specialize (RGM eq_refl). specialize (RGMS eq_refl).
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
  destruct (addr_four m2 (mode + 4) 8 (mode + 4) AM2 ltac:(lia) ltac:(lia)) as (k1 & MK1 & SK1).
  eapply pl_m1F; [ rewrite unsigned_lit by lia; reflexivity | lia | exact MK1 | exact SK1
    | eapply rng_shadow_one; [exact RGMS | lia] | intros y11 y12 y13 ].
  destruct (addr_four m2 (mode + 4) 8 (mode + 8) AM2 ltac:(lia) ltac:(lia)) as (k2 & MK2 & SK2).
  eapply pl_m2F; [ rewrite unsigned_lit by lia; reflexivity | lia | exact MK2 | exact SK2
    | rewrite unsigned_lit by lia; exact HR1
    | eapply rng_shadow_one; [exact RGMS | lia]
    | eapply ExecF.rng_sub; [exact RGM | lia | lia]
    | intros z11 z12 z14 Z11 ].
  apply wv in Z11. subst z11.
  step. rewrite sextw_zx32 by lia.
  step. rewrite lts0_lit by lia. brq BN.
  2:{ assert (PO : plain_ok (bv_unsigned a1) bs nch ns = false)
        by (apply not_true_iff_false; rewrite plain_ok_spec; lia).
      eapply pl_exitF with (r := -1).
      all: first [ exact FR2 | exact ST2 | exact WM0 | assumption | lia
                 | rewrite PO; first [reflexivity | exact MU0] ]. }
  step. step. rewrite sextw_zx32 by lia.
  step. rewrite lts0_lit by lia. brq BS.
  2:{ assert (PO : plain_ok (bv_unsigned a1) bs nch ns = false)
        by (apply not_true_iff_false; rewrite plain_ok_spec; lia).
      eapply pl_exitF with (r := -1).
      all: first [ exact FR2 | exact ST2 | exact WM0 | assumption | lia
                 | rewrite PO; first [reflexivity | exact MU0] ]. }
  rewrite !zx32_lit by lia.
  assert (0 <= ns * nch < 2^62) by nia.
  step. step. step. rewrite (unsigned_lit ns), (unsigned_lit nch) by lia. brq BM.
  { assert (PO : plain_ok (bv_unsigned a1) bs nch ns = false)
        by (apply not_true_iff_false; rewrite plain_ok_spec; lia).
      eapply pl_exitF with (r := -1).
      all: first [ exact FR2 | exact ST2 | exact WM0 | assumption | lia
                 | rewrite PO; first [reflexivity | exact MU0] ]. }
  assert (PO : plain_ok (bv_unsigned a1) bs nch ns = true) by (rewrite plain_ok_spec; split; [exact W | lia]).
  destruct (HO PO) as (HW & HoutN & DOR & DOS). specialize (AO PO). unfold off_stk in DOS.
  specialize (RGO PO). specialize (RGOS PO).
  do 7 step.
  destruct (geom_le nch ns BN BS ltac:(lia)) as (G1 & G2).
  assert (I0 : INVF ra sp s0 s1 s2 s3 m bs raw out nch ns lo
                 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 junk))))) m2 0).
  { split; [|split; [exact FR2|split; [exact ST2|split; [|split; [|split; [exact WM0|]]]]]].
    - eapply bytes_tp; [exact MU0' | rewrite LEN; lia | exact BB].
    - eapply wr_at_transport; [exact HW | exact WM0].
    - apply munch_extend. exact MU0.
    - intros i Hi. lia. }
  eapply (pl_outerF RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a1 F fc m bs raw mode out nch ns lo
    (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 junk))))))
    with (K := Z.to_nat (nch - 0)) (ch := 0).
  all: first [ assumption | reflexivity | lia
             | (eapply INV_idxF; [exact I0 | lia])
             | (intros x Hx; apply (app_win (bv_unsigned sp) 64); [lia | exact APS1 | exact APS2 | lia])
             | (rewrite ?(unsigned_lit ns), ?(unsigned_lit nch) by lia; rewrite ?Z.shiftl_mul_pow2 by lia;
                rewrite ?unsigned_lit by lia; lia) ].
Qed.

(* The twin implies the original: take the footprint that admits every access. *)
Theorem reac_decode_plain_le_holds_of_F : reac_frame_inspect_contract_F -> reac_decode_plain_le_contract.
Proof.
  intros HI. pose proof (reac_decode_plain_le_holds_F HI) as T. unfold reac_decode_plain_le_contract_F in T.
  unfold reac_decode_plain_le_contract, REAC_DECODE_PLAIN_LE, REAC_DECODE_PLAIN_LE_D.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m bs raw mode out nch ns lo E0 E2 E3 Rraw Rmode Rout HB Rnch Rns HM ST LO DR DM HO APS1 APS2 CELLS SRW DC AR AM AO.
  pose proof (u64_range sp) as Rsp.
  assert (Hlo : 0 <= lo) by (destruct ST as [? _]; lia).
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (T ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m bs raw mode out nch ns lo);
    try assumption.
  - unfold REAC_DECODE_PLAIN_LE_D. apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; unfold GOT_CELL_K; lia.
  - apply ExecF.rng_all; unfold CELL_K; lia.
  - intros L. specialize (AR L). destruct AR as (A1 & A2 & A3 & _).
    apply ExecF.rng_all; unfold APPMEM_END in A3; lia.
  - intros L. specialize (AR L). destruct AR as (A1 & A2 & A3 & _).
    unfold shadow_addr, ASAN_K. unfold APPMEM_END in A3.
    apply ExecF.rng_all; Z.div_mod_to_equations; lia.
  - intros Hw. specialize (AM Hw). destruct AM as (A1 & A2 & A3 & _).
    apply ExecF.rng_all; unfold APPMEM_END in A3; lia.
  - intros Hw. specialize (AM Hw). destruct AM as (A1 & A2 & A3 & _).
    unfold shadow_addr, ASAN_K. unfold APPMEM_END in A3.
    apply ExecF.rng_all; Z.div_mod_to_equations; lia.
  - intros P. destruct (HO P) as (_ & HN & _). apply ExecF.rng_all; lia.
  - intros P. destruct (HO P) as (_ & HN & _). specialize (AO P). destruct AO as (A1 & A2 & _).
    unfold shadow_addr, ASAN_K. apply ExecF.rng_all; Z.div_mod_to_equations; lia.
Qed.
