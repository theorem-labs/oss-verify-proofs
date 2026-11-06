From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import AsanKA AsanKAProof reac_frame_inspect_c reac_decode_c ReacDecodeLib.
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

Lemma land_m8 : forall c, 0 <= c < 2^64 -> Z.land c 18446744073709551608 = 8 * (c / 8).
Proof.
  intros c Hc.
  replace 18446744073709551608 with (Z.land (Z.ones 64) (Z.lnot (Z.ones 3))) by reflexivity.
  rewrite Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. cbn. lia.
Qed.

Ltac usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end.

Lemma rc_m1 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x18 + 4 = A ->
  A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 + 3 < bv_signed k) ->
  (forall y11 y12 y13 : word, evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y11 y12 y13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81494) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81480) fc None mm (seg_rom rsegs)).
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

Lemma rc_m2 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (v : word) (A : Z),
  bv_unsigned x18 + 8 = A ->
  A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 + 3 < bv_signed k) ->
  ov_read_bytes rsegs mm (Z_to_bv 64 (bv_unsigned x18 + 4)) 4 = Some (le4 v) ->
  (forall y11 y12 y13 : word, bv_unsigned y11 = A -> evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y11 y12 y13 x14 x15 x16 (zx32 v) x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x814ac) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81494) fc None mm (seg_rom rsegs)).
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

Lemma rc_c1 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x29 + bv_unsigned x28 = A ->
  A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  (forall y10 y11 y21 : word, bv_unsigned y11 = A -> evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y10 y11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x10 y21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81538) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81520) fc None mm (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k A EA RA M SK CONT.
  pose proof (u64_range x29) as R29. pose proof (u64_range x28) as R28. unfold ASAN_K in M.
  step. gen_add x29 x28 w U. rewrite EA in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT. exact U.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, U, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT. exact U.
Qed.

Lemma rc_c2 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (A D : Z),
  bv_unsigned x8 = A ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  bv_unsigned x11 = D ->
  mrd rsegs mm (wa D) = Some b ->
  (forall y11 y21 : word, evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (zxb b) y11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 y21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x8154c) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81538) fc None mm (seg_rom rsegs)).
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

Lemma rc_c3 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x10 = A ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  (forall y11 y21 : word, evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 y21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81568) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81558) fc None mm (seg_rom rsegs)).
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

Lemma rc_c4 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (A D : Z),
  bv_unsigned x8 + 1 = A ->
  A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  bv_unsigned x10 = D ->
  mrd rsegs mm (wa D) = Some b ->
  (forall y11 y21 y22 : word, evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (zxb b) y11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 y21 y22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81580) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81568) fc None mm (seg_rom rsegs)).
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

Lemma rc_c5 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x11 = A ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  (forall y10 y21 : word, evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 y21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81598) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81588) fc None mm (seg_rom rsegs)).
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

Lemma rc_c6 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (A D : Z),
  bv_unsigned x8 + 2 = A ->
  A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  bv_unsigned x11 = D ->
  mrd rsegs mm (wa D) = Some b ->
  (forall y10 y21 y22 : word, evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y10 (zxb b) x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 y21 y22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x815b0) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81598) fc None mm (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k b A D EA RA M SK ED MD CONT.
  pose proof (u64_range x8) as R8. unfold ASAN_K in M.
  step. gen_addi x8 w U. rewrite EA in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw0 mm x11 _ _ MD ED) as R. step. clear R.
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
     then munch [(bv_unsigned sp - 80, bv_unsigned sp); (out, out + 3 * nch * ns)] m m' /\
          bytes_at rsegs m' out (braid_out bs nch ns)
     else munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m').

Local Notation SP := (bv_unsigned sp).
Local Notation FR mk := (rw_cells rsegs mk (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
Local Notation N := (3 * nch * ns).
Local Notation STATE pc mm x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31 :=
  (MS (mkR (Z_to_bv 64 0x81474) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 x6 x7 x8 (Z_to_bv 64 raw)
        x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 2147450880) x20 x21 x22 s7 s8 s9 s10 s11
        x28 x29 x30 x31)
      F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

Hypothesis Hsp : lo + 80 <= SP.
Hypothesis Hlo : 0 <= lo.

Lemma rd_exit : forall (m1 : word -> option byte) (r : Z)
    (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 : word),
  FR m1 -> stk rsegs m1 lo (SP + -64) -> wmono rsegs m m1 ->
  r = (if decode_ok (bv_unsigned a1) bs nch ns then ns else -1) ->
  (if decode_ok (bv_unsigned a1) bs nch ns
   then munch [(SP + -80, SP); (out, out + N)] m m1 /\ bytes_at rsegs m1 out (braid_out bs nch ns)
   else munch [(SP + -80, SP)] m m1) ->
  evt rsegs PostD (MS (mkR x1 (Z_to_bv 64 (SP + -64)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16
      x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x81628) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 r x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 HF ST WM Er HM.
  pose proof (u64_range sp) as Rsp.
  do 10 step.
  apply evt_done. unfold PostD. exists x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, m1.
  split; [subst r; reflexivity|]. split; [exact WM|]. split.
  - pose proof (stk_release rsegs m1 lo (SP + -64) _ ST HF ltac:(lia)) as ST2.
    cbn [cells_size csize Nat.add] in ST2. replace (SP + -64 + Z.of_nat 64) with SP in ST2 by lia. exact ST2.
  - replace (SP - 80) with (SP + -80) by lia. exact HM.
Qed.

Hypothesis Hlen : length bs = 1492%nat.
Hypothesis Hraw : 0 <= raw.
Hypothesis Hraw2 : raw + 1492 <= 2^64.
Hypothesis Hout : 0 <= out.
Hypothesis HoutN : out + N < 2^64.
Hypothesis Hnch : 0 < nch.
Hypothesis Hev : nch mod 2 = 0.
Hypothesis Hns : 0 < ns.
Hypothesis H480 : nch * ns <= 480.
Hypothesis DOR : out + N <= raw \/ raw + 1492 <= out.
Hypothesis DOS : out + N <= SP - 80 \/ SP <= out.
Hypothesis AR : addressable m raw 1492.
Hypothesis AO : addressable m out N.
Hypothesis APW : forall x, SP - 80 <= x < SP -> app_mem x.
Hypothesis OK : decode_ok (bv_unsigned a1) bs nch ns = true.

Definition INVD (mk : word -> option byte) (j : Z) : Prop :=
  bytes_at rsegs mk raw bs /\ FR mk /\ stk rsegs mk lo (SP + -64) /\ wr_at rsegs mk out N /\
  munch [(SP + -80, SP); (out, out + N)] m mk /\ wmono rsegs m mk /\
  (forall i, 0 <= i < j -> mrd rsegs mk (Z_to_bv 64 (out + i)) = Some (braid_byte bs nch ns i)).

Lemma INVD_idx : forall mk j j', INVD mk j -> j = j' -> INVD mk j'.
Proof. intros; subst; assumption. Qed.

Lemma INVD_addr : forall mk j p n, INVD mk j -> addressable m p n -> addressable mk p n.
Proof.
  intros mk j p n (_ & _ & _ & _ & MU & _) A. eapply addr_munch; [exact A | exact MU |].
  intros i Hi. destruct A as (_ & _ & _ & HA). destruct (HA i Hi) as (Ha & _).
  pose proof (shadow_not_app _ Ha) as NA. cbn [outside]. split; [|split; [|exact I]].
  - intros W. apply NA, APW. lia.
  - intros W. apply NA. destruct AO as (_ & _ & _ & HO). destruct (HO ((p + i) / 8 + ASAN_K - out) ltac:(lia)) as (Ho & _).
    replace (out + ((p + i) / 8 + ASAN_K - out)) with ((p + i) / 8 + ASAN_K) in Ho by lia. exact Ho.
Qed.

Lemma src_bound : forall ch s k o, 0 <= ch < nch -> 0 <= s < ns -> 0 <= k < 3 -> o = boff (ch mod 2) k ->
  0 <= 50 + (3 * (s * nch + (ch - ch mod 2)) + o) < 1492.
Proof using Hsp Hlo Hlen Hraw Hraw2 Hout HoutN Hnch Hev Hns H480 DOR DOS.
  intros ch s k o Hch Hs Hk Ho.
  pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hm.
  assert (s * nch <= (ns - 1) * nch) by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (0 <= s * nch) by (apply Z.mul_nonneg_nonneg; lia).
  assert (ch - ch mod 2 <= nch - 2) by (Z.div_mod_to_equations; lia).
  assert (0 <= ch - ch mod 2) by (Z.div_mod_to_equations; lia).
  assert (0 <= o <= 5) by (subst o; unfold boff; destruct (k =? 0), (k =? 1); lia).
  nia.
Qed.

Lemma INVD_rd : forall mk j ch s k o, INVD mk j -> 0 <= ch < nch -> 0 <= s < ns -> 0 <= k < 3 ->
  o = boff (ch mod 2) k ->
  mrd rsegs mk (wa (raw + (50 + (3 * (s * nch + (ch - ch mod 2)) + o)))) = Some (braid_byte bs nch ns (3 * (ch * ns + s) + k)).
Proof.
  intros mk j ch s k o (HB & _) Hch Hs Hk Ho.
  pose proof (src_bound ch s k o Hch Hs Hk Ho) as SB.
  rewrite braid_byte_at by lia. rewrite (braid_pos_boff s ch nch k Hk), <- Ho.
  pose proof (bytes_nth mk raw bs (Z.to_nat (50 + (3 * (s * nch + (ch - ch mod 2)) + o))) HB ltac:(rewrite Hlen; lia)) as R.
  rewrite Z2Nat.id in R by lia. exact R.
Qed.

Lemma INVD_shr : forall mk j ch s k o, INVD mk j -> 0 <= ch < nch -> 0 <= s < ns -> 0 <= k < 3 ->
  o = boff (ch mod 2) k ->
  exists kb, mrd rsegs mk (wa ((raw + (50 + (3 * (s * nch + (ch - ch mod 2)) + o))) / 8 + ASAN_K)) = Some kb /\
    (bv_signed kb = 0 \/ (raw + (50 + (3 * (s * nch + (ch - ch mod 2)) + o))) mod 8 < bv_signed kb).
Proof.
  intros mk j ch s k o I Hch Hs Hk Ho.
  pose proof (src_bound ch s k o Hch Hs Hk Ho) as SB.
  destruct (addr_one mk raw 1492 (50 + (3 * (s * nch + (ch - ch mod 2)) + o)) (INVD_addr mk j raw 1492 I AR) SB)
    as (_ & kb & M & S). exists kb. split; assumption.
Qed.

Lemma INVD_sho : forall mk j q, INVD mk j -> 0 <= q < N ->
  exists kb, mrd rsegs mk (wa ((out + q) / 8 + ASAN_K)) = Some kb /\
    (bv_signed kb = 0 \/ (out + q) mod 8 < bv_signed kb).
Proof.
  intros mk j q I Hq.
  destruct (addr_one mk out N q (INVD_addr mk j out N I AO) Hq) as (_ & kb & M & S). exists kb. split; assumption.
Qed.

Lemma INVD_wr : forall mk j q, INVD mk j -> 0 <= q < N -> store_ok rsegs mk (Z_to_bv 64 (out + q)) 1 = true.
Proof.
  intros mk j q (_ & _ & _ & HW & _) Hq. change (Z_to_bv 64 (out + q)) with (wa (out + q)).
  apply (wr_at_store_ok rsegs mk out N q 1 HW); lia.
Qed.

Lemma INVD_store : forall mk j0 j j2, INVD mk j0 -> j0 = j -> 0 <= j < N -> j2 = j + 1 ->
  INVD (write_to_mem mk (Z_to_bv 64 (out + j)) [braid_byte bs nch ns j]) j2.
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

Lemma INVD_out : forall mk, INVD mk N -> bytes_at rsegs mk out (braid_out bs nch ns).
Proof.
  intros mk (_ & _ & _ & _ & _ & _ & HP). unfold braid_out.
  apply bytes_at_of_fun; [lia | lia |]. intros i Hi. apply HP. lia.
Qed.

Ltac do_store I0 I1 jj :=
  rewrite ?le1_zxb;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mk ?a ?b) _) =>
    assert (I1 : INVD (write_to_mem mk a b) (jj + 1)) by (eapply INVD_store; [exact I0 | lia | lia | lia]);
    let m2 := fresh "m" in set (m2 := write_to_mem mk a b) in *; clearbody m2; clear I0
  end.

Lemma rd_inner : forall (ch : Z) (x5 x6 x7 x12 x13 x14 x15 x16 x17 x29 x30 x31 : word),
  0 <= ch < nch -> bv_unsigned x5 = raw + 50 -> bv_unsigned x17 = 3 * nch ->
  bv_unsigned x29 = raw + 50 + ch mod 2 + 3 -> bv_unsigned x30 = raw + 50 + ch mod 2 + 1 ->
  bv_unsigned x31 = 5 * (ch mod 2) ->
  (forall (m2 : word -> option byte) (y8 y10 y11 y18 y20 y21 y22 y28 : word),
     bv_unsigned y20 = out + 3 * (ch * ns + ns) - 3 -> INVD m2 (3 * (ch * ns + ns)) ->
     evt rsegs PostD (STATE 0x81614 m2 x5 x6 x7 y8 y10 y11 x12 x13 x14 x15 x16 x17 y18 y20 y21 y22 y28 x29 x30 x31)) ->
  forall (K : nat) (s : Z) (m1 : word -> option byte) (x8 x10 x11 x18 x20 x21 x22 x28 : word),
  Z.to_nat (ns - s) = K -> 0 <= s < ns ->
  bv_unsigned x8 = out + 3 * (ch * ns + s) -> bv_unsigned x10 = out + 3 * (ch * ns + s) ->
  bv_unsigned x18 = ns - s -> bv_unsigned x28 = 3 * (ch - ch mod 2) + 3 * nch * s ->
  INVD m1 (3 * (ch * ns + s)) ->
  evt rsegs PostD (STATE 0x81520 m1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31).
Proof.
  intros ch x5 x6 x7 x12 x13 x14 x15 x16 x17 x29 x30 x31 Hch H5 H17 H29 H30 H31 CONT K.
  apply wv in H5, H17, H29, H30, H31. subst x5 x17 x29 x30 x31.
  assert (nch <= 480 /\ ns <= 480) by nia.
  assert (ch * ns + ns <= nch * ns) by (rewrite <- (Z.mul_succ_l ch ns); apply Z.mul_le_mono_nonneg_r; lia).
  assert (0 <= ch * ns) by nia.
  pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hm.
  assert (ch - ch mod 2 <= nch - 2) by (Z.div_mod_to_equations; lia).
  assert (0 <= ch - ch mod 2) by (Z.div_mod_to_equations; lia).
  induction K as [K IH] using lt_wf_ind.
  intros s m1 x8 x10 x11 x18 x20 x21 x22 x28 HK Hs H8 H10 H18 H28 I0.
  assert (s * nch <= (ns - 1) * nch) by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (0 <= s * nch) by (apply Z.mul_nonneg_nonneg; lia).
  apply wv in H8, H10, H18, H28. subst x8 x10 x18 x28.
  destruct (INVD_shr m1 _ ch s 0 (3 + ch mod 2) I0 Hch Hs ltac:(lia) eq_refl) as (k0 & MK & SK).
  eapply rc_c1; [ | | exact MK | exact SK | intros p10 p11 p21 P11 ]; [ usub; lia | lia | ]. clear MK SK.
  apply wv in P11. subst p11.
  destruct (INVD_sho m1 _ (3 * (ch * ns + s) + 0) I0 ltac:(lia)) as (k1 & MK & SK).
  pose proof (INVD_rd m1 _ ch s 0 (3 + ch mod 2) I0 Hch Hs ltac:(lia) eq_refl) as RD.
  eapply rc_c2; [ | exact MK | exact SK | | exact RD | intros q11 q21 ]; [ usub; lia | usub; lia | ].
  clear MK SK RD.
  pose proof (INVD_wr m1 _ (3 * (ch * ns + s) + 0) I0 ltac:(lia)) as HS.
  step. step. clear HS.
  do_store I0 I1 (3 * (ch * ns + s) + 0).
  step.
  destruct (INVD_shr _ _ ch s 1 (5 * (ch mod 2)) I1 Hch Hs ltac:(lia) eq_refl) as (k2 & MK & SK).
  eapply rc_c3; [ | exact MK | exact SK | intros r11 r21 ]; [ usub; lia | ]. clear MK SK.
  destruct (INVD_sho _ _ (3 * (ch * ns + s) + 1) I1 ltac:(lia)) as (k3 & MK & SK).
  pose proof (INVD_rd _ _ ch s 1 (5 * (ch mod 2)) I1 Hch Hs ltac:(lia) eq_refl) as RD.
  eapply rc_c4; [ | | exact MK | exact SK | | exact RD | intros u11 u21 u22 ]; [ usub; lia | lia | usub; lia | ].
  clear MK SK RD.
  pose proof (INVD_wr _ _ (3 * (ch * ns + s) + 1) I1 ltac:(lia)) as HS.
  step. clear HS.
  do_store I1 I2 (3 * (ch * ns + s) + 1).
  step.
  destruct (INVD_shr _ _ ch s 2 (1 + ch mod 2) I2 Hch Hs ltac:(lia) eq_refl) as (k4 & MK & SK).
  eapply rc_c5; [ | exact MK | exact SK | intros v10 v21 ]; [ usub; lia | ]. clear MK SK.
  destruct (INVD_sho _ _ (3 * (ch * ns + s) + 2) I2 ltac:(lia)) as (k5 & MK & SK).
  pose proof (INVD_rd _ _ ch s 2 (1 + ch mod 2) I2 Hch Hs ltac:(lia) eq_refl) as RD.
  eapply rc_c6; [ | | exact MK | exact SK | | exact RD | intros w10 w21 w22 ]; [ usub; lia | lia | usub; lia | ].
  clear MK SK RD.
  pose proof (INVD_wr _ _ (3 * (ch * ns + s) + 2) I2 ltac:(lia)) as HS.
  step. clear HS.
  do_store I2 I3 (3 * (ch * ns + s) + 2).
  step. step. step. step. step.
  usub. brq BR.
  - eapply CONT; [ usub; lia | eapply INVD_idx; [exact I3 | lia] ].
  - step.
    eapply (IH (Z.to_nat (ns - (s + 1))) ltac:(lia) (s + 1));
      [ reflexivity | lia | usub; lia | usub; lia | usub; lia | usub; lia | eapply INVD_idx; [exact I3 | lia] ].
Qed.

Lemma rd_outer : forall (K : nat) (ch : Z) (m1 : word -> option byte)
    (x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31 : word),
  Z.to_nat (nch - ch) = K -> 0 <= ch < nch ->
  bv_unsigned x5 = raw + 50 -> bv_unsigned x8 = out + 3 * (ch * ns) ->
  x12 = Z_to_bv 64 nch -> x13 = Z_to_bv 64 ns -> bv_unsigned x14 = ns ->
  bv_unsigned x15 = ch -> bv_unsigned x16 = ch -> bv_unsigned x17 = 3 * nch ->
  INVD m1 (3 * (ch * ns)) ->
  evt rsegs PostD (STATE 0x814e8 m1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31).
Proof.
  induction K as [K IH] using lt_wf_ind.
  intros ch m1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31
    HK Hch H5 H8 E12 E13 H14 H15 H16 H17 I0.
  assert (ch * ns <= (nch - 1) * ns) by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (0 <= ch * ns) by nia.
  assert (nch <= 480 /\ ns <= 480) by nia.
  pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hm.
  assert (P : ch mod 2 = 0 \/ ch mod 2 = 1) by lia.
  apply wv in H5, H8, H14, H15, H16, H17. subst x5 x8 x12 x13 x14 x15 x16 x17.
  do 14 step.
  rewrite (unsigned_lit ch) by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (ch * 2 ^ 2)) by lia.
  rewrite land_m8, land_m2 by lia. rewrite !land1.
  assert (EQ5 : bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltiu (Z_to_bv 64 (ch mod 2)) 1)
    + -1))) 5)) = 5 * (ch mod 2)) by (destruct P as [P|P]; rewrite P; vm_compute; reflexivity).
  clear P.
  eapply (rd_inner ch) with (K := Z.to_nat (ns - 0)) (s := 0);
    [ lia | usub; lia | usub; lia | usub; lia | usub; lia | exact EQ5 | | reflexivity | lia
    | usub; lia | usub; lia | usub; lia
    | rewrite (unsigned_lit (8 * (ch * 2 ^ 2 / 8))) by (Z.div_mod_to_equations; lia);
      rewrite (unsigned_lit (2 * (ch / 2))) by (Z.div_mod_to_equations; lia);
      rewrite unsigned_lit by (Z.div_mod_to_equations; lia); Z.div_mod_to_equations; lia
    | eapply INVD_idx; [exact I0 | lia] ].
  intros m2 y8 y10 y11 y18 y20 y21 y22 y28 H20 I2. apply wv in H20. subst y20.
  step. step. rewrite (unsigned_lit ch) by lia. rewrite swrap32_id by lia.
  step. step.
  brq BR.
  - assert (EN : nch * ns = ch * ns + ns) by (replace nch with (ch + 1) by lia; ring).
    step.
    destruct I2 as (HB2 & HF2 & ST2 & HW2 & MU2 & WM2 & HP2).
    eapply rd_exit with (r := ns); [exact HF2 | exact ST2 | exact WM2 | rewrite OK; reflexivity | ].
    rewrite OK. split; [exact MU2|]. apply INVD_out. apply (INVD_idx m2 (3 * (ch * ns + ns))); [|lia].
    exact (conj HB2 (conj HF2 (conj ST2 (conj HW2 (conj MU2 (conj WM2 HP2)))))).
  - eapply (IH (Z.to_nat (nch - (ch + 1))) ltac:(lia) (ch + 1));
      [ reflexivity | lia | usub; lia | usub; nia | reflexivity | reflexivity | usub; lia
      | usub; lia | usub; lia | usub; lia | eapply INVD_idx; [exact I2 | nia] ].
Qed.

End RD.
Ltac curmem k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => k mm end.

Lemma win_out : forall s a, 0 <= s - 80 -> app_mem (s - 80) -> app_mem (s - 1) -> app_mem a ->
  outside [(s - 80, s)] (a / 8 + ASAN_K).
Proof.
  intros s a H0 H1 H2 Ha. cbn [outside]. split; [|exact I]. intros W.
  apply (shadow_not_app a Ha). apply (app_win s 80); [lia | exact H1 | exact H2 | lia].
Qed.

Lemma win_shadow : forall s a, app_mem (s - 80) -> app_mem (s - 1) -> in_shadow a -> outside [(s - 80, s)] a.
Proof.
  intros s a H1 H2 Ha. cbn [outside]. split; [|exact I]. intros W.
  apply (in_shadow_not_app a Ha). apply (app_win s 80); [lia | exact H1 | exact H2 | lia].
Qed.

Lemma addr_win : forall m m' s p n, addressable m p n -> munch [(s - 80, s)] m m' -> 0 <= s - 80 ->
  app_mem (s - 80) -> app_mem (s - 1) -> addressable m' p n.
Proof.
  intros m m' s p n A MU H0 H1 H2. eapply addr_munch; [exact A | exact MU |].
  intros i Hi. destruct (addr_one m p n i A Hi) as (Ha & _). apply win_out; assumption.
Qed.

Theorem reac_decode_holds : reac_frame_inspect_contract -> reac_decode_contract.
Proof.
  intros HI. unfold reac_decode_contract, REAC_DECODE, REAC_DECODE_D.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m bs raw mode out nch ns lo E0 E2 E3 Rraw Rmode Rout HB Rnch Rns HM ST LO DR DM HO APS1 APS2 CELLS SRW DC AR AM AO.
  subst a0 a2 a3.
  pose proof (u64_range sp) as Rsp.
  assert (Hlo : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (conj HM CELLS) as PK. clear HM CELLS.
  carve_frame 64%nat ST.
  do 9 step.
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
    split; [unfold off_stk; rewrite unsigned_lit by lia; lia|].
    split; [replace (bv_unsigned sp + -64 - 16) with (bv_unsigned sp - 80) by lia; exact APS1|].
    split; [apply (app_win (bv_unsigned sp) 80); [lia | exact APS1 | exact APS2 | lia]|].
    split; [exact CELLS1|].
    split; [eapply shadow_rw_munch; [exact SRW | exact MU | exact WM | intros a Ha; apply win_shadow; assumption]|].
    split; [unfold off_stk, GOT_CELL_K; rewrite unsigned_lit by lia; lia|].
    split; [unfold off_stk, CELL_K; rewrite unsigned_lit by lia; lia|].
    eapply addr_win; [exact AR | exact MU | lia | exact APS1 | exact APS2]. }
  intros ms' (a1' & a2' & a3' & a4' & m2 & -> & MU2 & WM2 & ST2).
  replace (ret_pc (Z_to_bv 64 529524)) with (Z_to_bv 64 529524) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  unfold REAC_FRAME_INSPECT_FRAME in MU2, ST2. rewrite unsigned_lit in MU2, ST2 by lia.
  assert (MU0 : munch [(bv_unsigned sp + -80, bv_unsigned sp)] m m2)
    by (eapply munch_trans; [eapply munch_wider; [ | | exact MU]; lia | eapply munch_wider; [ | | exact MU2]; lia]).
  assert (WM0 : wmono rsegs m m2) by (eapply wmono_trans; [exact WM | exact WM2]).
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    by (eapply rw_cells_transport; [exact FR | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize]; split; [lia | exact I]]).
  clear FR MU2 WM2 ST MU WM CELLS1.
  step. rewrite inspect_valid_bit. step. step.
  destruct (inspect_wf (bv_unsigned a1) bs) eqn:W.
  2:{ if_true.
      assert (PO : decode_ok (bv_unsigned a1) bs nch ns = false) by (unfold decode_ok; rewrite W; reflexivity).
      eapply rd_exit with (r := -1).
      all: first [ exact FR2 | exact ST2 | exact WM0 | rewrite PO; first [reflexivity | exact MU0] | lia ]. }
  if_false.
  assert (L : bv_unsigned a1 = 1492).
  { unfold inspect_wf in W. apply Z.eqb_eq.
    destruct (andb_prop _ _ W) as [W1 _]. destruct (andb_prop _ _ W1) as [W2 _].
    destruct (andb_prop _ _ W2) as [W3 _]. destruct (andb_prop _ _ W3) as [W4 _]. exact W4. }
  destruct (HB L) as [LEN BB]. specialize (DR L). specialize (AR L). specialize (AM eq_refl).
  unfold off_stk in DR, DM.
  pose proof (bytes_at_bound _ _ _ _ BB) as BBB. rewrite LEN in BBB.
  apply bytes_at_app in HM. destruct HM as [HM1 HM2]. rewrite length_le4 in HM2.
  replace (mode + 4 + Z.of_nat 4) with (mode + 8) in HM2 by lia.
  apply (bytes_tp m m2 _ _ _ _ MU0) in HM1; [| rewrite length_le4; lia].
  apply (bytes_tp m m2 _ _ _ _ MU0) in HM2; [| rewrite length_le4; lia].
  pose proof (bytes_at_bound _ _ _ _ HM2) as HMB. rewrite length_le4 in HMB.
  pose proof (rd_all _ _ _ HM1) as HR1. rewrite length_le4 in HR1.
  pose proof (rd_all _ _ _ HM2) as HR2. rewrite length_le4 in HR2.
  assert (MU0' : munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m2)
    by (eapply munch_wider; [ | | exact MU0]; lia).
  assert (AM2 : addressable m2 (mode + 4) 8)
    by (eapply addr_win; [exact AM | exact MU0' | lia | exact APS1 | exact APS2]).
  destruct (addr_four m2 (mode + 4) 8 (mode + 4) AM2 ltac:(lia) ltac:(lia)) as (k1 & MK1 & SK1).
  eapply rc_m1; [ rewrite unsigned_lit by lia; reflexivity | lia | exact MK1 | exact SK1 | intros y11 y12 y13 ].
  destruct (addr_four m2 (mode + 4) 8 (mode + 8) AM2 ltac:(lia) ltac:(lia)) as (k2 & MK2 & SK2).
  eapply rc_m2; [ rewrite unsigned_lit by lia; reflexivity | lia | exact MK2 | exact SK2
    | rewrite unsigned_lit by lia; exact HR1 | intros z11 z12 z13 Z11 ].
  apply wv in Z11. subst z11. clear SK1 SK2.
  step. rewrite sextw_zx32 by lia.
  step. rewrite lts0_lit by lia. brq BN.
  2:{ assert (PO : decode_ok (bv_unsigned a1) bs nch ns = false)
        by (apply not_true_iff_false; rewrite decode_ok_spec; lia).
      eapply rd_exit with (r := -1).
      all: first [ exact FR2 | exact ST2 | exact WM0 | rewrite PO; first [reflexivity | exact MU0] | lia ]. }
  step. rewrite (unsigned_lit nch) by lia. rewrite land1.
  step. brq BE.
  2:{ assert (PO : decode_ok (bv_unsigned a1) bs nch ns = false)
        by (apply not_true_iff_false; rewrite decode_ok_spec; lia).
      eapply rd_exit with (r := -1).
      all: first [ exact FR2 | exact ST2 | exact WM0 | rewrite PO; first [reflexivity | exact MU0] | lia ]. }
  step. step. rewrite sextw_zx32 by lia.
  step. rewrite lts0_lit by lia. brq BS.
  2:{ assert (PO : decode_ok (bv_unsigned a1) bs nch ns = false)
        by (apply not_true_iff_false; rewrite decode_ok_spec; lia).
      eapply rd_exit with (r := -1).
      all: first [ exact FR2 | exact ST2 | exact WM0 | rewrite PO; first [reflexivity | exact MU0] | lia ]. }
  rewrite !zx32_lit by lia.
  assert (0 <= ns * nch < 2^62).
  { split; [apply Z.mul_nonneg_nonneg; lia|].
    apply Z.le_lt_trans with ((2^31 - 1) * (2^31 - 1)); [apply Z.mul_le_mono_nonneg; lia | lia]. }
  step. step. step. rewrite (unsigned_lit ns), (unsigned_lit nch) by lia. brq BM.
  { assert (PO : decode_ok (bv_unsigned a1) bs nch ns = false)
        by (apply not_true_iff_false; rewrite decode_ok_spec; lia).
      eapply rd_exit with (r := -1).
      all: first [ exact FR2 | exact ST2 | exact WM0 | rewrite PO; first [reflexivity | exact MU0] | lia ]. }
  assert (PO : decode_ok (bv_unsigned a1) bs nch ns = true) by (rewrite decode_ok_spec; split; [exact W | lia]).
  destruct (HO PO) as (HW & HoutN & DOR & DOS). specialize (AO PO). unfold off_stk in DOS.
  do 5 step.
  assert (I0 : INVD ra sp s0 s1 s2 s3 s4 s5 s6 m bs raw out nch ns lo m2 0).
  { split; [|split; [exact FR2|split; [exact ST2|split; [|split; [|split; [exact WM0|]]]]]].
    - eapply bytes_tp; [exact MU0' | rewrite LEN; lia | exact BB].
    - eapply wr_at_transport; [exact HW | exact WM0].
    - apply munch_extend. exact MU0.
    - intros i Hi. lia. }
  clear DR DM DC.
  eapply rd_outer with (K := Z.to_nat (nch - 0)) (ch := 0) (ra := ra) (sp := sp) (s0 := s0) (s1 := s1) (s2 := s2)
    (s3 := s3) (s4 := s4) (s5 := s5) (s6 := s6) (a1 := a1) (m := m) (bs := bs) (raw := raw) (out := out)
    (nch := nch) (ns := ns) (lo := lo).
  all: first [ assumption | reflexivity
             | (intros x Hx; apply (app_win (bv_unsigned sp) 80); [lia | exact APS1 | exact APS2 | lia])
             | (usub; rewrite ?Z.shiftl_mul_pow2 by lia; usub; lia)
             | (rewrite ?(unsigned_lit ns), ?(unsigned_lit nch) by lia; rewrite ?Z.shiftl_mul_pow2 by lia;
                rewrite ?unsigned_lit by lia; lia)
             | (eapply INVD_idx; [exact I0 | lia])
             | lia ].
Qed.
