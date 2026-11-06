From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import AsanKA AsanKAProof reac_frame_inspect_c reac_decode_c ReacDecodeLib.
Import ListNotations.
Open Scope Z_scope.

Lemma decode_ok_spec : forall len bs nch ns,
  decode_ok len bs nch ns = true <->
  inspect_wf len bs = true /\ 0 < nch /\ nch mod 2 = 0 /\ 0 < ns /\ nch * ns <= 480.
Proof.
  intros. unfold decode_ok. rewrite !andb_true_iff, !Z.ltb_lt, Z.eqb_eq, Z.leb_le. tauto.
Qed.

Definition boff (c k : Z) : Z := if k =? 0 then 3 + c else if k =? 1 then 5 * c else 1 + c.

Lemma braid_pos_boff : forall s ch nch k, 0 <= k < 3 ->
  braid_pos s ch nch k = 3 * (s * nch + (ch - ch mod 2)) + boff (ch mod 2) k.
Proof.
  intros s ch nch k Hk. unfold braid_pos, boff.
  pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hm.
  destruct (Z.eqb_spec (ch mod 2) 0) as [E|E];
  destruct (Z.eqb_spec k 0); destruct (Z.eqb_spec k 1); try rewrite E; lia.
Qed.

Lemma braid_byte_at : forall bs nch ns ch s k, 0 <= ch -> 0 <= s < ns -> 0 <= k < 3 ->
  braid_byte bs nch ns (3 * (ch * ns + s) + k) = nth (Z.to_nat (50 + braid_pos s ch nch k)) bs (Z_to_bv 8 0).
Proof.
  intros bs nch ns ch s k Hch Hs Hk. unfold braid_byte.
  destruct (braid_div ch s k ns Hch Hs Hk) as (D1 & D2 & D3 & D4). rewrite D1, D2, D3, D4. reflexivity.
Qed.


Lemma bm1 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x18 + 4 = A ->
  A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 + 3 < bv_signed k) ->
  (forall y11 y12 y13 : word, evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y11 y12 y13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81804) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x817f0) fc None mm (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k A EA RA M SK CONT.
  pose proof (u64_range x18) as R18. unfold ASAN_K in M.
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

Lemma bm2 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (v : word) (A : Z),
  bv_unsigned x18 + 8 = A ->
  A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 + 3 < bv_signed k) ->
  ov_read_bytes rsegs mm (Z_to_bv 64 (bv_unsigned x18 + 4)) 4 = Some (le4 v) ->
  (forall y11 y13 y14 : word, bv_unsigned y11 = A -> evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y11 (sx32 v) y13 y14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x8181c) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81804) fc None mm (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k v A EA RA M SK RV CONT.
  pose proof (u64_range x18) as R18. unfold ASAN_K in M.
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

Lemma bc1 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x11 = A ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  (forall y21 y22 : word, evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 y21 y22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x8190c) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x818fc) fc None mm (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k A EA M SK CONT.
  pose proof (u64_range x11) as RS. unfold ASAN_K in M.
  step. gen_shr x11 g G. rewrite EA in G.
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

Lemma bc2 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (A D : Z),
  bv_unsigned x8 = A ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  bv_unsigned x11 = D ->
  mrd rsegs mm (wa D) = Some b ->
  (forall y21 y22 : word, evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (zxb b) x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 y21 y22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81920) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x8190c) fc None mm (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k b A D EA M SK ED MD CONT.
  pose proof (u64_range x8) as RS. unfold ASAN_K in M.
  step. gen_shr x8 g G. rewrite EA in G.
  step. gen_addi g h H.
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

Lemma bc3 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x11 = A ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  (forall y22 y23 : word, evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 y22 y23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81948) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81938) fc None mm (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k A EA M SK CONT.
  pose proof (u64_range x11) as RS. unfold ASAN_K in M.
  step. gen_shr x11 g G. rewrite EA in G.
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

Lemma bc4 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (A D : Z),
  bv_unsigned x10 = A ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  bv_unsigned x11 = D ->
  mrd rsegs mm (wa D) = Some b ->
  (forall y22 y23 : word, evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (zxb b) x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 y22 y23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x8195c) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81948) fc None mm (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k b A D EA M SK ED MD CONT.
  pose proof (u64_range x10) as RS. unfold ASAN_K in M.
  step. gen_shr x10 g G. rewrite EA in G.
  step. gen_addi g h H.
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

Lemma bc5 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x10 = A ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  (forall y11 y22 : word, evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 y22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81984) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81974) fc None mm (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k A EA M SK CONT.
  pose proof (u64_range x10) as RS. unfold ASAN_K in M.
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

Lemma bc6 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (A D : Z),
  bv_unsigned x8 + 2 = A ->
  A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  bv_unsigned x10 = D ->
  mrd rsegs mm (wa D) = Some b ->
  (forall y11 y22 y23 : word, evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (zxb b) y11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 y22 y23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x8199c) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81984) fc None mm (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k b A D EA RA M SK ED MD CONT.
  pose proof (u64_range x8) as R8. unfold ASAN_K in M.
  step. gen_addi x8 w U. rewrite EA in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
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

Section RD.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a1 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (raw out nch ns lo : Z).

Definition PostD : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1
                  (Z_to_bv 64 (if decode_ok (bv_unsigned a1) bs nch ns then ns else -1))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp) /\
    (if decode_ok (bv_unsigned a1) bs nch ns
     then munch [(bv_unsigned sp - 112, bv_unsigned sp); (out, out + 3 * nch * ns)] m m' /\
          bytes_at rsegs m' out (braid_out bs nch ns)
     else munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m').

Local Notation SP := (bv_unsigned sp).
Local Notation FRD mk junk :=
  (rw_cells rsegs mk (bv_unsigned sp + -96) [CB 24 junk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
Local Notation N := (3 * nch * ns).
Local Notation STATE pc mm x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x28 x29 x30 x31 :=
  (MS (mkR (Z_to_bv 64 0x817cc) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 x8 x9
        x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 s8 s9 s10 s11
        x28 x29 x30 x31)
      F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

Hypothesis Hsp : lo + 112 <= SP.
Hypothesis Hlo : 0 <= lo.

Lemma rd_exit : forall (m1 : word -> option byte) (r : Z) (junk : list byte)
    (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word),
  FRD m1 junk -> stk rsegs m1 lo (SP + -96) -> wmono rsegs m m1 ->
  r = (if decode_ok (bv_unsigned a1) bs nch ns then ns else -1) ->
  (if decode_ok (bv_unsigned a1) bs nch ns
   then munch [(SP + -112, SP); (out, out + N)] m m1 /\ bytes_at rsegs m1 out (braid_out bs nch ns)
   else munch [(SP + -112, SP)] m m1) ->
  evt rsegs PostD (MS (mkR x1 (Z_to_bv 64 (SP + -96)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16
      x17 x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x81a0c) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 r junk x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 HF ST WM Er HM.
  pose proof (u64_range sp) as Rsp.
  do 11 step.
  apply evt_done. unfold PostD. exists x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, m1.
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
Definition SEP : Prop :=
  (out + N <= raw \/ raw + 1492 <= out) /\ (out + N <= SP + -112 \/ SP <= out) /\
  (raw + 1492 <= SP + -112 \/ SP <= raw).
Hypothesis HSEP : SEP.
Hypothesis AR : addressable m raw 1492.
Hypothesis AO : addressable m out N.
Hypothesis APW : forall x, SP - 112 <= x < SP -> app_mem x.
Hypothesis OK : decode_ok (bv_unsigned a1) bs nch ns = true.

Definition bpre (j : Z) : list byte := map (braid_byte bs nch ns) (map Z.of_nat (seq 0 (Z.to_nat j))).

Lemma bpre_len : forall j, 0 <= j -> Z.of_nat (length (bpre j)) = j.
Proof. intros j Hj. unfold bpre. rewrite length_mapseq. lia. Qed.

Lemma bpre_S : forall j, 0 <= j -> bpre (j + 1) = bpre j ++ [braid_byte bs nch ns j].
Proof.
  intros j Hj. unfold bpre. replace (Z.to_nat (j + 1)) with (Z.to_nat j + 1)%nat by lia.
  rewrite seq_app, !map_app. cbn [seq map Nat.add]. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma bw_ext : forall mk q0 q, bytes_at rsegs mk out (bpre q0) -> q0 = q -> 0 <= q -> out + q + 1 <= 2^64 ->
  bytes_at rsegs (write_to_mem mk (wa (out + q)) [braid_byte bs nch ns q]) out (bpre (q + 1)).
Proof.
  intros mk q0 q HB E Hq Hb. subst q0. pose proof (bpre_len q Hq) as L.
  rewrite bpre_S by lia. apply bytes_at_app. split.
  - apply bytes_at_write_other; [exact HB | lia | cbn [length]; lia | cbn [length]; lia].
  - rewrite L. apply bytes_at_write_same; cbn [length]; lia.
Qed.

Definition INVD (mk : word -> option byte) (j : Z) : Prop :=
  bytes_at rsegs mk raw bs /\ (exists junk, FRD mk junk) /\ stk rsegs mk lo (SP + -96) /\ wr_at rsegs mk out N /\
  munch [(SP + -112, SP); (out, out + N)] m mk /\ wmono rsegs m mk /\ bytes_at rsegs mk out (bpre j).

Lemma INVD_idx : forall mk j j', INVD mk j -> j = j' -> INVD mk j'.
Proof. intros; subst; assumption. Qed.

Lemma addr_m : forall mk p n, munch [(SP + -112, SP); (out, out + N)] m mk -> addressable m p n -> addressable mk p n.
Proof.
  intros mk p n MU A. eapply addr_munch; [exact A | exact MU |].
  intros i Hi. destruct A as (_ & _ & _ & HA). destruct (HA i Hi) as (Ha & _).
  pose proof (shadow_not_app _ Ha) as NA. cbn [outside]. split; [|split; [|exact I]].
  - intros W. apply NA, APW. lia.
  - intros W. apply NA. destruct AO as (_ & _ & _ & HO). destruct (HO ((p + i) / 8 + ASAN_K - out) ltac:(lia)) as (Ho & _).
    replace (out + ((p + i) / 8 + ASAN_K - out)) with ((p + i) / 8 + ASAN_K) in Ho by lia. exact Ho.
Qed.

Lemma src_bound : forall ch s k o, 0 <= ch < nch -> 0 <= s < ns -> 0 <= k < 3 -> o = boff (ch mod 2) k ->
  0 <= 50 + (3 * (s * nch + (ch - ch mod 2)) + o) < 1492.
Proof.
  intros ch s k o Hch Hs Hk Ho.
  pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hm.
  assert (s * nch <= (ns - 1) * nch) by nia.
  assert (0 <= s * nch) by nia.
  assert (ch - ch mod 2 <= nch - 2) by (Z.div_mod_to_equations; lia).
  assert (0 <= ch - ch mod 2) by (Z.div_mod_to_equations; lia).
  assert (0 <= o <= 5) by (subst o; unfold boff; destruct (k =? 0), (k =? 1); lia).
  nia.
Qed.

Lemma SRC_rd : forall mk ch s k o, bytes_at rsegs mk raw bs -> 0 <= ch < nch -> 0 <= s < ns -> 0 <= k < 3 ->
  o = boff (ch mod 2) k ->
  mrd rsegs mk (wa (raw + (50 + (3 * (s * nch + (ch - ch mod 2)) + o)))) = Some (braid_byte bs nch ns (3 * (ch * ns + s) + k)).
Proof.
  intros mk ch s k o HB Hch Hs Hk Ho.
  pose proof (src_bound ch s k o Hch Hs Hk Ho) as SB.
  rewrite braid_byte_at by lia. rewrite (braid_pos_boff s ch nch k Hk), <- Ho.
  pose proof (bytes_nth mk raw bs (Z.to_nat (50 + (3 * (s * nch + (ch - ch mod 2)) + o))) HB ltac:(rewrite Hlen; lia)) as R.
  rewrite Z2Nat.id in R by lia. exact R.
Qed.

Lemma SRC_shr : forall mk ch s k o, munch [(SP + -112, SP); (out, out + N)] m mk ->
  0 <= ch < nch -> 0 <= s < ns -> 0 <= k < 3 -> o = boff (ch mod 2) k ->
  exists kb, mrd rsegs mk (wa ((raw + (50 + (3 * (s * nch + (ch - ch mod 2)) + o))) / 8 + ASAN_K)) = Some kb /\
    (bv_signed kb = 0 \/ (raw + (50 + (3 * (s * nch + (ch - ch mod 2)) + o))) mod 8 < bv_signed kb).
Proof.
  intros mk ch s k o MU Hch Hs Hk Ho.
  pose proof (src_bound ch s k o Hch Hs Hk Ho) as SB.
  destruct (addr_one mk raw 1492 (50 + (3 * (s * nch + (ch - ch mod 2)) + o)) (addr_m mk raw 1492 MU AR) SB)
    as (_ & kb & M & S). exists kb. split; assumption.
Qed.

Lemma DST_sho : forall mk q, munch [(SP + -112, SP); (out, out + N)] m mk -> 0 <= q < N ->
  exists kb, mrd rsegs mk (wa ((out + q) / 8 + ASAN_K)) = Some kb /\
    (bv_signed kb = 0 \/ (out + q) mod 8 < bv_signed kb).
Proof.
  intros mk q MU Hq.
  destruct (addr_one mk out N q (addr_m mk out N MU AO) Hq) as (_ & kb & M & S). exists kb. split; assumption.
Qed.

Ltac stf :=
  let D1 := fresh "D" in let D2 := fresh "D" in let D3 := fresh "D" in
  pose proof HSEP as [D1 [D2 D3]]; st; clear D1 D2 D3.

Ltac ostore :=
  rewrite ?le1_zxb;
  lazymatch goal with
  | |- evt ?sg ?Q (MS ?R ?Fr ?pc ?f ?rv (write_to_mem ?mk ?w [?b]) ?ro) =>
      let a := addr_expr w in
      lazymatch a with
      | out + ?q =>
          change (evt sg Q (MS R Fr pc f rv (write_to_mem mk (wa (out + q)) [b]) ro));
          match goal with BW : bytes_at _ mk out (bpre ?q0) |- _ =>
            apply (bw_ext mk q0 q) in BW; [ | lia | lia | lia ]
          end;
          match goal with H : Z.of_nat (length (bpre _)) = _ |- _ => clear H end;
          assert (LB : Z.of_nat (length (bpre (q + 1))) = q + 1) by (apply bpre_len; lia);
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

Lemma rd_inner : forall (ch : Z) (x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 : word),
  0 <= ch < nch ->
  bv_unsigned x5 = 18446744073709551599 -> bv_unsigned x6 = 2 -> bv_unsigned x7 = 18446744073709551615 ->
  bv_unsigned x9 = ch - ch mod 2 -> bv_unsigned x12 = nch -> bv_unsigned x13 = ns -> bv_unsigned x14 = ch ->
  bv_unsigned x15 = raw + 50 -> bv_unsigned x16 = 18446744073709551608 -> bv_unsigned x17 = SP + -96 ->
  bv_unsigned x18 = ch mod 2 -> bv_unsigned x28 = 18446744073709551615 - (raw + 50) ->
  bv_unsigned x29 = 2147483646 -> bv_unsigned x30 = 18446744073709551607 ->
  (forall (m2 : word -> option byte) (y8 y10 y11 y20 y21 y22 y23 y31 : word),
     bv_unsigned y20 = out + 3 * (ch * ns + ns) - 3 -> INVD m2 (3 * (ch * ns + ns)) ->
     evt rsegs PostD (STATE 0x819fc m2 x5 x6 x7 y8 x9 y10 y11 x12 x13 x14 x15 x16 x17 x18 y20 y21 y22 y23 x28 x29 x30 y31)) ->
  forall (K : nat) (s : Z) (m1 : word -> option byte) (x8 x10 x11 x20 x21 x22 x23 x31 : word),
  Z.to_nat (ns - s) = K -> 0 <= s < ns ->
  bv_unsigned x31 = s -> bv_unsigned x8 = out + 3 * (ch * ns + s) -> bv_unsigned x21 = out + 3 * (ch * ns + s) ->
  INVD m1 (3 * (ch * ns + s)) ->
  evt rsegs PostD (STATE 0x81878 m1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x28 x29 x30 x31).
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
  assert (LB : Z.of_nat (length (bpre (3 * (ch * ns + s)))) = 3 * (ch * ns + s)) by (apply bpre_len; lia).
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
    destruct (SRC_shr _ ch s 0 (3 + ch mod 2) MU Hch Hs ltac:(lia) eq_refl) as (k0 & MK & SK).
    eapply bc1; [ | exact MK | exact SK | intros p21 p22 ]; [ ufin | ]. clear MK SK.
    destruct (DST_sho _ (3 * (ch * ns + s) + 0) MU ltac:(lia)) as (k1 & MK & SK).
    pose proof (SRC_rd _ ch s 0 (3 + ch mod 2) BR Hch Hs ltac:(lia) eq_refl) as RD.
    eapply bc2; [ | exact MK | exact SK | | exact RD | intros q21 q22 ]; [ ufin | ufin | ]. clear MK SK RD.
    pose proof (wr_at_store_ok rsegs _ out N (3 * (ch * ns + s) + 0) 1 WA ltac:(lia) ltac:(lia)) as HS.
    st. clear HS. ostore.
    st. st. cnd false.
    st. st. cnd false.
    st.
    destruct (SRC_shr _ ch s 1 (5 * (ch mod 2)) MU Hch Hs ltac:(lia) eq_refl) as (k2 & MK & SK).
    eapply bc3; [ | exact MK | exact SK | intros r22 r23 ]; [ ufin | ]. clear MK SK.
    destruct (DST_sho _ (3 * (ch * ns + s) + 1) MU ltac:(lia)) as (k3 & MK & SK).
    pose proof (SRC_rd _ ch s 1 (5 * (ch mod 2)) BR Hch Hs ltac:(lia) eq_refl) as RD.
    eapply bc4; [ | exact MK | exact SK | | exact RD | intros u22 u23 ]; [ ufin | ufin | ]. clear MK SK RD.
    pose proof (wr_at_store_ok rsegs _ out N (3 * (ch * ns + s) + 1) 1 WA ltac:(lia) ltac:(lia)) as HS.
    st. clear HS. ostore.
    st. st. cnd false.
    st. st. cnd false.
    st.
    destruct (SRC_shr _ ch s 2 (1 + ch mod 2) MU Hch Hs ltac:(lia) eq_refl) as (k4 & MK & SK).
    eapply bc5; [ | exact MK | exact SK | intros v11 v22 ]; [ ufin | ]. clear MK SK.
    destruct (DST_sho _ (3 * (ch * ns + s) + 2) MU ltac:(lia)) as (k5 & MK & SK).
    pose proof (SRC_rd _ ch s 2 (1 + ch mod 2) BR Hch Hs ltac:(lia) eq_refl) as RD.
    eapply bc6; [ | | exact MK | exact SK | | exact RD | intros w11 w22 w23 ]; [ ufin | lia | ufin | ]. clear MK SK RD.
    pose proof (wr_at_store_ok rsegs _ out N (3 * (ch * ns + s) + 2) 1 WA ltac:(lia) ltac:(lia)) as HS.
    st. clear HS. ostore.
    st. st. st.
    st.
    brq BR'.
    + st. eapply CONT; [ ufin | eapply INVD_idx; [rebundle | lia] ].
    + eapply (IH (Z.to_nat (ns - (s + 1))) ltac:(lia) (s + 1)).
      all: lazymatch goal with
           | |- INVD _ _ => eapply INVD_idx; [rebundle | lia]
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
    destruct (SRC_shr _ ch s 0 (3 + ch mod 2) MU Hch Hs ltac:(lia) eq_refl) as (k0 & MK & SK).
    eapply bc1; [ | exact MK | exact SK | intros p21 p22 ]; [ ufin | ]. clear MK SK.
    destruct (DST_sho _ (3 * (ch * ns + s) + 0) MU ltac:(lia)) as (k1 & MK & SK).
    pose proof (SRC_rd _ ch s 0 (3 + ch mod 2) BR Hch Hs ltac:(lia) eq_refl) as RD.
    eapply bc2; [ | exact MK | exact SK | | exact RD | intros q21 q22 ]; [ ufin | ufin | ]. clear MK SK RD.
    pose proof (wr_at_store_ok rsegs _ out N (3 * (ch * ns + s) + 0) 1 WA ltac:(lia) ltac:(lia)) as HS.
    st. clear HS. ostore.
    st. st. cnd false.
    st. st. cnd false.
    st.
    destruct (SRC_shr _ ch s 1 (5 * (ch mod 2)) MU Hch Hs ltac:(lia) eq_refl) as (k2 & MK & SK).
    eapply bc3; [ | exact MK | exact SK | intros r22 r23 ]; [ ufin | ]. clear MK SK.
    destruct (DST_sho _ (3 * (ch * ns + s) + 1) MU ltac:(lia)) as (k3 & MK & SK).
    pose proof (SRC_rd _ ch s 1 (5 * (ch mod 2)) BR Hch Hs ltac:(lia) eq_refl) as RD.
    eapply bc4; [ | exact MK | exact SK | | exact RD | intros u22 u23 ]; [ ufin | ufin | ]. clear MK SK RD.
    pose proof (wr_at_store_ok rsegs _ out N (3 * (ch * ns + s) + 1) 1 WA ltac:(lia) ltac:(lia)) as HS.
    st. clear HS. ostore.
    st. st. cnd false.
    st. st. cnd false.
    st.
    destruct (SRC_shr _ ch s 2 (1 + ch mod 2) MU Hch Hs ltac:(lia) eq_refl) as (k4 & MK & SK).
    eapply bc5; [ | exact MK | exact SK | intros v11 v22 ]; [ ufin | ]. clear MK SK.
    destruct (DST_sho _ (3 * (ch * ns + s) + 2) MU ltac:(lia)) as (k5 & MK & SK).
    pose proof (SRC_rd _ ch s 2 (1 + ch mod 2) BR Hch Hs ltac:(lia) eq_refl) as RD.
    eapply bc6; [ | | exact MK | exact SK | | exact RD | intros w11 w22 w23 ]; [ ufin | lia | ufin | ]. clear MK SK RD.
    pose proof (wr_at_store_ok rsegs _ out N (3 * (ch * ns + s) + 2) 1 WA ltac:(lia) ltac:(lia)) as HS.
    st. clear HS. ostore.
    st. st. st.
    st.
    brq BR'.
    + st. eapply CONT; [ ufin | eapply INVD_idx; [rebundle | lia] ].
    + eapply (IH (Z.to_nat (ns - (s + 1))) ltac:(lia) (s + 1)).
      all: lazymatch goal with
           | |- INVD _ _ => eapply INVD_idx; [rebundle | lia]
           | _ => first [ reflexivity | lia | ufin ]
           end.
Qed.

Lemma rd_outer : forall (K : nat) (ch : Z) (m1 : word -> option byte)
    (x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x28 x29 x30 x31 : word),
  Z.to_nat (nch - ch) = K -> 0 <= ch < nch ->
  bv_unsigned x5 = 18446744073709551599 -> bv_unsigned x6 = 2 -> bv_unsigned x7 = 18446744073709551615 ->
  bv_unsigned x8 = out + 3 * (ch * ns) -> bv_unsigned x12 = nch -> bv_unsigned x13 = ns -> bv_unsigned x14 = ch ->
  bv_unsigned x15 = raw + 50 -> bv_unsigned x16 = 18446744073709551608 -> bv_unsigned x17 = SP + -96 ->
  bv_unsigned x28 = 18446744073709551615 - (raw + 50) -> bv_unsigned x29 = 2147483646 ->
  bv_unsigned x30 = 18446744073709551607 ->
  INVD m1 (3 * (ch * ns)) ->
  evt rsegs PostD (STATE 0x81868 m1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x28 x29 x30 x31).
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
  eapply (rd_inner ch) with (K := Z.to_nat (ns - 0)) (s := 0).
  all: lazymatch goal with
       | |- forall _ : word -> option byte, _ => idtac
       | |- INVD _ _ => eapply INVD_idx; [exact I0 | lia]
       | _ => first [ lia | reflexivity | ufin ]
       end.
  intros m2 y8 y10 y11 y20 y21 y22 y23 y31 H20 I2. apply wv in H20. subst y20.
  st. st. st.
  brq BR.
  - assert (EN : nch * ns = ch * ns + ns) by (replace nch with (ch + 1) by lia; ring).
    st.
    destruct I2 as (BR2 & (junk2 & FR2) & ST2 & WA2 & MU2 & WM2 & BW2).
    eapply rd_exit with (r := ns); [exact FR2 | exact ST2 | exact WM2 | rewrite OK; reflexivity | ].
    rewrite OK. split; [exact MU2|].
    replace (braid_out bs nch ns) with (bpre (3 * (ch * ns + ns))) by (unfold bpre, braid_out; do 3 f_equal; lia).
    exact BW2.
  - assert (EQ1 : (ch + 1) * ns = ch * ns + ns) by ring.
    eapply (IH (Z.to_nat (nch - (ch + 1))) ltac:(lia) (ch + 1)).
    all: lazymatch goal with
         | |- INVD _ _ => eapply INVD_idx; [exact I2 | lia]
         | _ => first [ reflexivity | lia | (rewrite unsigned_lit by lia; lia) | ufin ]
         end.
Qed.

End RD.
Ltac curmem k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => k mm end.

Lemma win_out : forall s a, 0 <= s - 112 -> app_mem (s - 112) -> app_mem (s - 1) -> app_mem a ->
  outside [(s - 112, s)] (a / 8 + ASAN_K).
Proof.
  intros s a H0 H1 H2 Ha. cbn [outside]. split; [|exact I]. intros W.
  apply (shadow_not_app a Ha). apply (app_win s 112); [lia | exact H1 | exact H2 | lia].
Qed.

Lemma win_shadow : forall s a, app_mem (s - 112) -> app_mem (s - 1) -> in_shadow a -> outside [(s - 112, s)] a.
Proof.
  intros s a H1 H2 Ha. cbn [outside]. split; [|exact I]. intros W.
  apply (in_shadow_not_app a Ha). apply (app_win s 112); [lia | exact H1 | exact H2 | lia].
Qed.

Lemma addr_win : forall m m' s p n, addressable m p n -> munch [(s - 112, s)] m m' -> 0 <= s - 112 ->
  app_mem (s - 112) -> app_mem (s - 1) -> addressable m' p n.
Proof.
  intros m m' s p n A MU H0 H1 H2. eapply addr_munch; [exact A | exact MU |].
  intros i Hi. destruct (addr_one m p n i A Hi) as (Ha & _). apply win_out; assumption.
Qed.

Theorem reac_decode_holds : reac_frame_inspect_contract -> reac_decode_contract.
Proof.
  intros HI. unfold reac_decode_contract, REAC_DECODE, REAC_DECODE_D.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m bs raw mode out nch ns lo E0 E2 E3 Rraw Rmode Rout HB Rnch Rns HM ST LO DR DM HO APS1 APS2 CELLS SRW DC AR AM AO
    NR NM NO.
  subst a0 a2 a3.
  pose proof (u64_range sp) as Rsp.
  assert (Hlo : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (conj HM CELLS) as PK. clear HM CELLS.
  carve_frame 96%nat ST.
  do 10 step.
  destruct PK as (HM & CELLS).
  unfold off_stk, GOT_CELL_K, MIDEND in DC.
  curmem ltac:(fun mm => assert (CELLS1 : asan_cells mm)
    by (eapply asan_cells_munch; [exact CELLS | exact MU | unfold MIDEND, GOT_CELL_K; lia])).
  pose proof CELLS1 as (CK & GCK & _).
  unfold CELL_K, GOT_CELL_K, ASAN_K in CK, GCK.
  pose proof (rd_all _ _ _ GCK) as RDG. rewrite length_le8 in RDG.
  pose proof (rd_all _ _ _ CK) as RDS. rewrite length_le8 in RDS.
  do 3 step. step. step. clear RDG RDS CK GCK. step. step.
  curmem ltac:(fun mm => eapply evt_cut;
    [eapply (HI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm bs lo) |]).
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
      eapply rd_exit with (r := -1).
      all: first [ exact FR2 | exact ST2 | exact WM0 | lia | rewrite PO; first [reflexivity | exact MU0] ]. }
  if_false.
  assert (L : bv_unsigned a1 = 1492) by (unfold inspect_wf in W; rewrite !andb_true_iff, !Z.eqb_eq in W; tauto).
  destruct (HB L) as [LEN BB]. specialize (DR L). specialize (AR L). specialize (AM eq_refl).
  specialize (NR L). destruct (NM eq_refl) as [NM0 NM4].
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
  eapply bm1; [ rewrite unsigned_lit by lia; reflexivity | lia | exact MK1 | exact SK1 | intros y11 y12 y13 ].
  destruct (addr_four m2 (mode + 4) 8 (mode + 8) AM2 ltac:(lia) ltac:(lia)) as (k2 & MK2 & SK2).
  eapply bm2; [ rewrite unsigned_lit by lia; reflexivity | lia | exact MK2 | exact SK2
    | rewrite unsigned_lit by lia; exact HR1 | intros z11 z13 z14 Z11 ].
  apply wv in Z11. subst z11.
  rewrite sx32_lit by lia.
  step. rewrite lts0_lit by lia. brq BN.
  2:{ assert (PO : decode_ok (bv_unsigned a1) bs nch ns = false)
        by (apply not_true_iff_false; rewrite decode_ok_spec; lia).
      eapply rd_exit with (r := -1).
      all: first [ exact FR2 | exact ST2 | exact WM0 | lia | rewrite PO; first [reflexivity | exact MU0] ]. }
  step. rewrite (unsigned_lit nch) by lia. rewrite land1.
  step. brq BE.
  2:{ assert (PO : decode_ok (bv_unsigned a1) bs nch ns = false)
        by (apply not_true_iff_false; rewrite decode_ok_spec; lia).
      eapply rd_exit with (r := -1).
      all: first [ exact FR2 | exact ST2 | exact WM0 | lia | rewrite PO; first [reflexivity | exact MU0] ]. }
  step. rewrite sx32_lit by lia.
  step. rewrite lts0_lit by lia. brq BS.
  2:{ assert (PO : decode_ok (bv_unsigned a1) bs nch ns = false)
        by (apply not_true_iff_false; rewrite decode_ok_spec; lia).
      eapply rd_exit with (r := -1).
      all: first [ exact FR2 | exact ST2 | exact WM0 | lia | rewrite PO; first [reflexivity | exact MU0] ]. }
  pose proof (prod_bound62 ns nch ltac:(lia) ltac:(lia)).
  step. rewrite (unsigned_lit ns), (unsigned_lit nch) by lia.
  step. step. brq BM.
  { assert (PO : decode_ok (bv_unsigned a1) bs nch ns = false)
        by (apply not_true_iff_false; rewrite decode_ok_spec; lia).
      eapply rd_exit with (r := -1).
      all: first [ exact FR2 | exact ST2 | exact WM0 | lia | rewrite PO; first [reflexivity | exact MU0] ]. }
  assert (PO : decode_ok (bv_unsigned a1) bs nch ns = true)
    by (rewrite decode_ok_spec; split; [exact W|]; repeat split; lia).
  destruct (HO PO) as (HW & HoutN & DOR & DOS). specialize (AO PO). specialize (NO PO).
  assert (NO' : 0 < out) by lia. clear NO. unfold off_stk in DOS.
  do 11 step.
  eapply rd_outer with (K := Z.to_nat (nch - 0)) (ch := 0) (ra := ra) (sp := sp) (s0 := s0) (s1 := s1) (s2 := s2)
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
