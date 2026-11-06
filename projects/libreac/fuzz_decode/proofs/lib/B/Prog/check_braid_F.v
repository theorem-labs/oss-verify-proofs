From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import AsanKA AsanKAProof ReacDecodeLib check_braid_c check_braid check_braid_F_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Footprint twin of check_braid_holds (B image, entry 0x81070): check_braid_holds_F proves check_braid_contract_F
   (check_braid_F_c.v), the run as an ExecF.evtF run under a footprint RNG that holds the frame [sp - 128, sp),
   the cells GOT_CELL_K and CELL_K, the audio and pcm buffers and their shadow bytes. The proof follows
   check_braid.v step for step, with StepF's step; the shadow-check helpers and the loop lemmas get _F twins with
   the rng premises of the bytes they load. Pure helpers are those of check_braid.v. *)

(* the shadow byte of byte i of a buffer [p, p + n) lies in the buffer's shadow range *)
Lemma shadow_sub : forall RNG p n i, 0 <= i < n ->
  ExecF.rng RNG (p / 8 + ASAN_K) ((p + n - 1) / 8 - p / 8 + 1) ->
  ExecF.rng RNG ((p + i) / 8 + ASAN_K) 1.
Proof.
  intros RNG p n i Hi H. eapply ExecF.rng_sub; [exact H | |].
  - pose proof (Z.div_le_mono p (p + i) 8 ltac:(lia) ltac:(lia)). lia.
  - pose proof (Z.div_le_mono (p + i) (p + n - 1) 8 ltac:(lia) ltac:(lia)). lia.
Qed.

Ltac takeF b := lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; solve_c]
  end.

(* pure shadow: addr x15, srli/lb x11, handler andi x12 ; 81150 -> 81160 *)
Lemma sc_p0_F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x15 = A -> A < 2^64 -> mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  ExecF.rng RNG (A / 8 + ASAN_K) 1 ->
  (forall y11 y12 : word, ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 2147450880) x10 y11 y12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81160) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 2147450880) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81150) fc None mm (seg_rom rsegs)).
Proof.
  intros until A. intros EA RA M SK RF CONT. pose proof (u64_range x15) as RS. unfold ASAN_K in M, RF.
  step. gen_shr x15 g G. rewrite EA in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step. pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, EA, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* pure shadow: addr x16, srli/lb x19, handler andi x13 ; 8117c -> 8118c *)
Lemma sc_a3_F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x16 = A -> A < 2^64 -> mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  ExecF.rng RNG (A / 8 + ASAN_K) 1 ->
  (forall y13 y19 : word, ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 2147450880) x10 x11 x12 y13 x14 x15 x16 x17 x18 y19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x8118c) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 2147450880) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x8117c) fc None mm (seg_rom rsegs)).
Proof.
  intros until A. intros EA RA M SK RF CONT. pose proof (u64_range x16) as RS. unfold ASAN_K in M, RF.
  step. gen_shr x16 g G. rewrite EA in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step. pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, EA, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* pure shadow: addr x16, srli/lb x12, handler andi x13 ; 811a0 -> 811b0 *)
Lemma sc_p1_F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x16 = A -> A < 2^64 -> mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  ExecF.rng RNG (A / 8 + ASAN_K) 1 ->
  (forall y12 y13 : word, ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 2147450880) x10 x11 y12 y13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x811b0) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 2147450880) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x811a0) fc None mm (seg_rom rsegs)).
Proof.
  intros until A. intros EA RA M SK RF CONT. pose proof (u64_range x16) as RS. unfold ASAN_K in M, RF.
  step. gen_shr x16 g G. rewrite EA in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step. pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, EA, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* shadow addr x14 (lb x16) + data x12 := byte at x11+1 ; handler andi x13 ; 811b0 -> 811c4 *)
Lemma sc_a0_F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (A D : Z),
  bv_unsigned x14 = A -> A < 2^64 -> mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  bv_unsigned x11 = D -> mrd rsegs mm (wa (D + 1)) = Some b ->
  ExecF.rng RNG (A / 8 + ASAN_K) 1 -> ExecF.rng RNG (D + 1) 1 ->
  (forall y13 y16 : word, ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 2147450880) x10 x11 (zxb b) y13 x14 x15 y16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x811c4) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 2147450880) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x811b0) fc None mm (seg_rom rsegs)).
Proof.
  intros until D. intros EA RA M SK ED MD RF RD CONT. pose proof (u64_range x14) as RS. pose proof (u64_range x11) as R11. unfold ASAN_K in M, RF.
  step. gen_shr x14 g G. rewrite EA in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw mm x11 1 _ _ MD ltac:(lia)) as R. step. clear R.
  step. pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, EA, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* pure shadow: addr x15, srli/lb x12, handler andi x13 ; 811d8 -> 811e8 *)
Lemma sc_p2_F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x15 = A -> A < 2^64 -> mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  ExecF.rng RNG (A / 8 + ASAN_K) 1 ->
  (forall y12 y13 : word, ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 2147450880) x10 x11 y12 y13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x811e8) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 2147450880) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x811d8) fc None mm (seg_rom rsegs)).
Proof.
  intros until A. intros EA RA M SK RF CONT. pose proof (u64_range x15) as RS. unfold ASAN_K in M, RF.
  step. gen_shr x15 g G. rewrite EA in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step. pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, EA, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* shadow addr x14 (lb x12) + data x11 := byte at x11+2 ; handler andi x13 ; 811ec -> 81200 *)
Lemma sc_a1_F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (A D : Z),
  bv_unsigned x14 = A -> A < 2^64 -> mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  bv_unsigned x11 = D -> mrd rsegs mm (wa (D + 2)) = Some b ->
  ExecF.rng RNG (A / 8 + ASAN_K) 1 -> ExecF.rng RNG (D + 2) 1 ->
  (forall y12 y13 : word, ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 2147450880) x10 (zxb b) y12 y13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81200) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 2147450880) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x811ec) fc None mm (seg_rom rsegs)).
Proof.
  intros until D. intros EA RA M SK ED MD RF RD CONT. pose proof (u64_range x14) as RS. pose proof (u64_range x11) as R11. unfold ASAN_K in M, RF.
  step. gen_shr x14 g G. rewrite EA in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw mm x11 2 _ _ MD ltac:(lia)) as R. step. clear R.
  step. pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, EA, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* pure shadow: addr x16, srli/lb x19, handler andi x21 ; 81214 -> 81224 *)
Lemma sc_a4_F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x16 = A -> A < 2^64 -> mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  ExecF.rng RNG (A / 8 + ASAN_K) 1 ->
  (forall y19 y21 : word, ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 2147450880) x10 x11 x12 x13 x14 x15 x16 x17 x18 y19 x20 y21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81224) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 2147450880) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81214) fc None mm (seg_rom rsegs)).
Proof.
  intros until A. intros EA RA M SK RF CONT. pose proof (u64_range x16) as RS. unfold ASAN_K in M, RF.
  step. gen_shr x16 g G. rewrite EA in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step. pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, EA, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* pure shadow: addr x16, srli/lb x12, handler andi x21 ; 81240 -> 81250 *)
Lemma sc_p1o_F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x16 = A -> A < 2^64 -> mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  ExecF.rng RNG (A / 8 + ASAN_K) 1 ->
  (forall y12 y21 : word, ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 2147450880) x10 x11 y12 x13 x14 x15 x16 x17 x18 x19 x20 y21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81250) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 2147450880) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81240) fc None mm (seg_rom rsegs)).
Proof.
  intros until A. intros EA RA M SK RF CONT. pose proof (u64_range x16) as RS. unfold ASAN_K in M, RF.
  step. gen_shr x16 g G. rewrite EA in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step. pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, EA, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* shadow addr x16 (lb x21) + data x12 := byte at x11+1 ; handler andi x13 ; 81254 -> 81268 *)
Lemma sc_a5_F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (A D : Z),
  bv_unsigned x16 = A -> A < 2^64 -> mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  bv_unsigned x11 = D -> mrd rsegs mm (wa (D + 1)) = Some b ->
  ExecF.rng RNG (A / 8 + ASAN_K) 1 -> ExecF.rng RNG (D + 1) 1 ->
  (forall y13 y21 : word, ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 2147450880) x10 x11 (zxb b) y13 x14 x15 x16 x17 x18 x19 x20 y21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81268) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 2147450880) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81254) fc None mm (seg_rom rsegs)).
Proof.
  intros until D. intros EA RA M SK ED MD RF RD CONT. pose proof (u64_range x16) as RS. pose proof (u64_range x11) as R11. unfold ASAN_K in M, RF.
  step. gen_shr x16 g G. rewrite EA in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw mm x11 1 _ _ MD ltac:(lia)) as R. step. clear R.
  step. pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, EA, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* pure shadow: addr x15, srli/lb x12, handler andi x13 ; 8127c -> 8128c *)
Lemma sc_p2o_F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x15 = A -> A < 2^64 -> mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  ExecF.rng RNG (A / 8 + ASAN_K) 1 ->
  (forall y12 y13 : word, ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 2147450880) x10 x11 y12 y13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x8128c) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 2147450880) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x8127c) fc None mm (seg_rom rsegs)).
Proof.
  intros until A. intros EA RA M SK RF CONT. pose proof (u64_range x15) as RS. unfold ASAN_K in M, RF.
  step. gen_shr x15 g G. rewrite EA in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step. pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, EA, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* shadow addr x14 (lb x12) + data x11 := byte at x11+2 ; handler andi x13 ; 81290 -> 812a4 *)
Lemma sc_a2o_F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (A D : Z),
  bv_unsigned x14 = A -> A < 2^64 -> mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  bv_unsigned x11 = D -> mrd rsegs mm (wa (D + 2)) = Some b ->
  ExecF.rng RNG (A / 8 + ASAN_K) 1 -> ExecF.rng RNG (D + 2) 1 ->
  (forall y12 y13 : word, ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 2147450880) x10 (zxb b) y12 y13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x812a4) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 2147450880) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81290) fc None mm (seg_rom rsegs)).
Proof.
  intros until D. intros EA RA M SK ED MD RF RD CONT. pose proof (u64_range x14) as RS. pose proof (u64_range x11) as R11. unfold ASAN_K in M, RF.
  step. gen_shr x14 g G. rewrite EA in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw mm x11 2 _ _ MD ltac:(lia)) as R. step. clear R.
  step. pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, EA, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

Section LoopsF.
Variables (RNG : ExecF.footprint) (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (audio pcm nch ns : Z) (t2 s0 t6 t3 t4 s2 s4 : word).
Hypothesis HN : 1 <= nch <= 127.
Hypothesis HS : 1 <= ns <= 127.
Hypothesis HA : 0 < audio < 2^63.
Hypothesis HP : 0 <= pcm < 2^63.
Hypothesis BR : braid_map m audio pcm nch ns.
Hypothesis AAD : addressable m audio (3 * nch * ns + 3 * (nch mod 2)).
Hypothesis APD : addressable m pcm (3 * nch * ns).
Hypothesis RGA : ExecF.rng RNG audio (3 * nch * ns + 3 * (nch mod 2)).
Hypothesis RGP : ExecF.rng RNG pcm (3 * nch * ns).
Hypothesis RGSA : ExecF.rng RNG (audio / 8 + ASAN_K) ((audio + (3 * nch * ns + 3 * (nch mod 2)) - 1) / 8 - audio / 8 + 1).
Hypothesis RGSP : ExecF.rng RNG (pcm / 8 + ASAN_K) ((pcm + 3 * nch * ns - 1) / 8 - pcm / 8 + 1).
Hypothesis Ht2 : bv_unsigned t2 = 18446744073709551615 - pcm.
Hypothesis Hs0 : bv_unsigned s0 = 3 * ns.
Hypothesis Ht6 : bv_unsigned t6 = 3 * nch.
Hypothesis Ht3 : bv_unsigned t3 = 1.
Hypothesis Ht4 : bv_unsigned t4 = 18446744073709551612.
Hypothesis Hs2 : bv_unsigned s2 = 18446744073709551615.
Hypothesis Hs4 : bv_unsigned s4 = 18446744073709551611.
Variable Q : machine_state -> Prop.

Local Notation ST pc ra t0 t1 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t5 :=
  (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 2147450880) (Z_to_bv 64 audio)
           a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Lemma body_F : forall ch s (ra t0 t1 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t5 : word),
  0 <= ch < nch -> 0 <= s < ns ->
  bv_unsigned t0 = 0 ->
  bv_unsigned t1 = ch ->
  bv_unsigned a7 = 3 * ns * ch ->
  bv_unsigned t5 = pcm + 3 * ns * ch ->
  bv_unsigned s6 = pcm + 3 * ns * ch ->
  bv_unsigned s8 = 3 * (2 * (ch / 2)) ->
  bv_unsigned s9 = ch mod 2 ->
  bv_unsigned s7 = 3 * s ->
  bv_unsigned s10 = audio + 3 * nch * s ->
  bv_unsigned s11 = audio + 3 * nch * s ->
  (forall (ra' t0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s7' s10' s11' : word),
     bv_unsigned t0' = 0 ->
     bv_unsigned a7' = 3 * ns * ch ->
     bv_unsigned s7' = 3 * (s + 1) ->
     bv_unsigned s10' = audio + 3 * nch * (s + 1) ->
     bv_unsigned s11' = audio + 3 * nch * (s + 1) ->
     ExecF.evtF rsegs RNG Q (ST 0x812c0 ra' t0' t1 a1' a2' a3' a4' a5' a6' a7' s3' s5' s6 s7' s8 s9 s10' s11' t5)) ->
  ExecF.evtF rsegs RNG Q (ST 0x81130 ra t0 t1 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t5).
Proof.
  intros ch s ra t0 t1 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t5
    Hch Hs Ht0 Ht1 Ha7 Ht5 Hs6 Hs8 Hs9 Hs7 Hs10 Hs11 K.
  assert (B1 : 0 <= ns * ch <= 16129) by nia.
  assert (B2 : 0 <= nch * s <= 16129) by nia.
  assert (Bnn : 3 * nch * ns <= 48387) by nia.
  assert (Hd1 : 0 <= ch / 2) by (apply Z.div_pos; lia).
  assert (Hd2 : 2 * (ch / 2) <= ch) by (pose proof (Z.mul_div_le ch 2 ltac:(lia)); lia).
  assert (Hm2 : 0 <= nch mod 2 < 2) by (apply Z.mod_pos_bound; lia).
  assert (Hpb : 2 * (ch / 2) + 2 <= nch + nch mod 2) by (apply pair_base_le; exact Hch).
  assert (B3 : nch * s + nch <= nch * ns) by nia.
  assert (BP0 : 0 <= 3 * ns * ch + 3 * s < 3 * nch * ns) by nia.
  assert (BP1 : 0 <= 3 * ns * ch + 3 * s + 1 < 3 * nch * ns) by nia.
  assert (BP2 : 0 <= 3 * ns * ch + 3 * s + 2 < 3 * nch * ns) by nia.
  assert (BA0 : 0 <= 3 * nch * s + 3 * (2 * (ch / 2)) < 3 * nch * ns + 3 * (nch mod 2)) by nia.
  assert (BA1 : 0 <= 3 * nch * s + 3 * (2 * (ch / 2)) + 1 < 3 * nch * ns + 3 * (nch mod 2)) by nia.
  assert (BA2 : 0 <= 3 * nch * s + 3 * (2 * (ch / 2)) + 2 < 3 * nch * ns + 3 * (nch mod 2)) by nia.
  assert (BA3 : 0 <= 3 * nch * s + 3 * (2 * (ch / 2)) + 3 < 3 * nch * ns + 3 * (nch mod 2)) by nia.
  assert (BA4 : 0 <= 3 * nch * s + 3 * (2 * (ch / 2)) + 4 < 3 * nch * ns + 3 * (nch mod 2)) by nia.
  assert (BA5 : 0 <= 3 * nch * s + 3 * (2 * (ch / 2)) + 5 < 3 * nch * ns + 3 * (nch mod 2)) by nia.
  assert (Bgp : 0 <= 3 * ns * ch + 3 * s < 2 ^ 31) by nia.
  assert (Bga : 0 <= 3 * nch * s + 3 * (2 * (ch / 2)) < 2 ^ 31) by nia.
  clear B1 B2 B3 Bnn Hd1 Hd2 Hpb.
  destruct (BR ch s 0 Hch Hs ltac:(lia)) as (b0 & P0 & A0).
  destruct (BR ch s 1 Hch Hs ltac:(lia)) as (b1 & P1 & A1).
  destruct (BR ch s 2 Hch Hs ltac:(lia)) as (b2 & P2 & A2).
  unfold braid_off in A0, A1, A2.
  pose proof (Zmod_even ch) as Hevm.
  (* 81130 add a4,s8,s11 : a4 = audio+g *)
  step. gen_add s8 s11 wa4 Ua4.
  assert (Ea4 : bv_unsigned wa4 = audio + (3 * nch * s + 3 * (2 * (ch / 2)))) by (rewrite Ua4, Hs8, Hs11; lia). clear Ua4.
  (* 81134 bltu a4,a0 : trap *)
  step. takeF false.
  (* 81138 seqz a1 ; 8113c xor a1,t3,a1 ; 81140 beqz a1 : trap *)
  step. step. step. takeF false.
  (* 81144 add a1,a7,s7 : a1 = p *)
  step. gen_add a7 s7 wp Up.
  assert (Ep : bv_unsigned wp = 3 * ns * ch + 3 * s) by (rewrite Up, Ha7, Hs7; lia). clear Up.
  (* 81148 bltu t2,a1 : trap *)
  step. takeF false.
  (* 8114c add a5,s6,s7 : a5 = pcm+p *)
  step. gen_add s6 s7 wa5 Ua5.
  assert (Ea5 : bv_unsigned wa5 = pcm + (3 * ns * ch + 3 * s)) by (rewrite Ua5, Hs6, Hs7; lia). clear Ua5.
  destruct (addr_one m pcm (3 * nch * ns) (3 * ns * ch + 3 * s) APD BP0) as (_ & kp0 & Mp0 & Sp0).
  eapply sc_p0_F with (A := pcm + (3 * ns * ch + 3 * s)) (k := kp0); [exact Ea5 | lia | exact Mp0 | exact Sp0 | exact (shadow_sub RNG pcm (3 * nch * ns) _ BP0 RGSP) |]. clear kp0 Mp0 Sp0.
  intros a1a a2a.
  (* 81160 add a1,t5,s7 : a1 = pcm+p *)
  step. gen_add t5 s7 wq Uq.
  assert (Eq : bv_unsigned wq = pcm + (3 * ns * ch + 3 * s)) by (rewrite Uq, Ht5, Hs7; lia). clear Uq.
  (* 81164 lbu a2,0(a1) : pcm[p] = b0 *)
  pose proof (rdw0 m wq _ _ P0 ltac:(nia)) as R. step. clear R P0.
  (* 81168 add ra,s10,s8 : ra = audio+g *)
  step. gen_add s10 s8 wr Ur.
  assert (Er : bv_unsigned wr = audio + (3 * nch * s + 3 * (2 * (ch / 2)))) by (rewrite Ur, Hs10, Hs8; lia). clear Ur.
  destruct (Z.even ch) eqn:Eev.
  - (* even *)
    assert (Hc2 : ch mod 2 = 0) by (rewrite Zmod_even, Eev; reflexivity). rewrite Hc2 in Hs9. clear Hc2.
    cbn [Z.eqb Pos.eqb] in A0, A1, A2.
    step. takeF false.
    step. takeF false.
    step. takeF false.
    (* 81178 addi a6,a4,3 *)
    step. gen_addi wa4 wa6 Ua6.
    assert (Ea6 : bv_unsigned wa6 = audio + (3 * nch * s + 3 * (2 * (ch / 2))) + 3) by (rewrite Ua6, Ea4; lia). clear Ua6.
    destruct (addr_one m audio (3 * nch * ns + 3 * (nch mod 2)) (3 * nch * s + 3 * (2 * (ch / 2)) + 3) AAD BA3) as (_ & ka0 & Ma0 & Sa0).
    eapply sc_a3_F with (A := audio + (3 * nch * s + 3 * (2 * (ch / 2)) + 3)) (k := ka0); [rewrite Ea6; lia | lia | exact Ma0 | exact Sa0 | exact (shadow_sub RNG audio (3 * nch * ns + 3 * (nch mod 2)) _ BA3 RGSA) |]. clear ka0 Ma0 Sa0 Ea6.
    intros a3a s3a.
    (* 8118c lbu a3,3(ra) : audio[g+3] = b0 *)
    pose proof (rdw m wr 3 _ _ A0 ltac:(nia)) as R. step. clear R A0.
    step. step. takeF false.
    step. takeF false.
    (* 8119c addi a6,a5,1 *)
    step. gen_addi wa5 wa6b Ua6b.
    assert (Ea6b : bv_unsigned wa6b = pcm + (3 * ns * ch + 3 * s) + 1) by (rewrite Ua6b, Ea5; lia). clear Ua6b.
    destruct (addr_one m pcm (3 * nch * ns) (3 * ns * ch + 3 * s + 1) APD BP1) as (_ & kp1 & Mp1 & Sp1).
    eapply sc_p1_F with (A := pcm + (3 * ns * ch + 3 * s + 1)) (k := kp1); [rewrite Ea6b; lia | lia | exact Mp1 | exact Sp1 | exact (shadow_sub RNG pcm (3 * nch * ns) _ BP1 RGSP) |]. clear kp1 Mp1 Sp1 Ea6b.
    intros a2b a3b.
    destruct (addr_one m audio (3 * nch * ns + 3 * (nch mod 2)) (3 * nch * s + 3 * (2 * (ch / 2))) AAD BA0) as (_ & ka1 & Ma1 & Sa1).
    eapply sc_a0_F with (A := audio + (3 * nch * s + 3 * (2 * (ch / 2)))) (b := b1) (D := pcm + 3 * (ch * ns + s));
      [exact Ea4 | lia | exact Ma1 | exact Sa1 | rewrite Eq; nia | exact P1 | exact (shadow_sub RNG audio (3 * nch * ns + 3 * (nch mod 2)) _ BA0 RGSA) | eapply ExecF.rng_sub; [exact RGP | lia | lia] |]. clear ka1 Ma1 Sa1 P1.
    intros a3c a6c.
    (* 811c4 lbu a3,0(ra) : audio[g+0] = b1 *)
    pose proof (rdw0 m wr _ _ A1 ltac:(nia)) as R. step. clear R A1.
    step. takeF false.
    step. step. takeF false.
    (* 811d4 addi a5,a5,2 *)
    step. gen_addi wa5 wa5b Ua5b.
    assert (Ea5b : bv_unsigned wa5b = pcm + (3 * ns * ch + 3 * s) + 2) by (rewrite Ua5b, Ea5; lia). clear Ua5b Ea5.
    destruct (addr_one m pcm (3 * nch * ns) (3 * ns * ch + 3 * s + 2) APD BP2) as (_ & kp2 & Mp2 & Sp2).
    eapply sc_p2_F with (A := pcm + (3 * ns * ch + 3 * s + 2)) (k := kp2); [rewrite Ea5b; lia | lia | exact Mp2 | exact Sp2 | exact (shadow_sub RNG pcm (3 * nch * ns) _ BP2 RGSP) |]. clear kp2 Mp2 Sp2 Ea5b.
    intros a2c a3d.
    (* 811e8 addi a4,a4,1 *)
    step. gen_addi wa4 wa4b Ua4b.
    assert (Ea4b : bv_unsigned wa4b = audio + (3 * nch * s + 3 * (2 * (ch / 2))) + 1) by (rewrite Ua4b, Ea4; lia). clear Ua4b Ea4.
    destruct (addr_one m audio (3 * nch * ns + 3 * (nch mod 2)) (3 * nch * s + 3 * (2 * (ch / 2)) + 1) AAD BA1) as (_ & ka2 & Ma2 & Sa2).
    eapply sc_a1_F with (A := audio + (3 * nch * s + 3 * (2 * (ch / 2)) + 1)) (b := b2) (D := pcm + 3 * (ch * ns + s));
      [rewrite Ea4b; lia | lia | exact Ma2 | exact Sa2 | rewrite Eq; nia | exact P2 | exact (shadow_sub RNG audio (3 * nch * ns + 3 * (nch mod 2)) _ BA1 RGSA) | eapply ExecF.rng_sub; [exact RGP | lia | lia] |]. clear ka2 Ma2 Sa2 Ea4b Eq P2.
    intros a2d a3e.
    (* 81200 lbu a2,1(ra) : audio[g+1] = b2 *)
    pose proof (rdw m wr 1 _ _ A2 ltac:(nia)) as R. step. clear R A2.
    do 7 step.
    apply K; fact.
  - (* odd *)
    assert (Hc2 : ch mod 2 = 1) by (rewrite Zmod_even, Eev; reflexivity). rewrite Hc2 in Hs9. clear Hc2.
    cbn [Z.eqb Pos.eqb] in A0, A1, A2.
    step. takeF true.
    step. takeF false.
    step. takeF false.
    (* 81210 addi a6,a4,4 *)
    step. gen_addi wa4 wa6 Ua6.
    assert (Ea6 : bv_unsigned wa6 = audio + (3 * nch * s + 3 * (2 * (ch / 2))) + 4) by (rewrite Ua6, Ea4; lia). clear Ua6.
    destruct (addr_one m audio (3 * nch * ns + 3 * (nch mod 2)) (3 * nch * s + 3 * (2 * (ch / 2)) + 4) AAD BA4) as (_ & ka0 & Ma0 & Sa0).
    eapply sc_a4_F with (A := audio + (3 * nch * s + 3 * (2 * (ch / 2)) + 4)) (k := ka0); [rewrite Ea6; lia | lia | exact Ma0 | exact Sa0 | exact (shadow_sub RNG audio (3 * nch * ns + 3 * (nch mod 2)) _ BA4 RGSA) |]. clear ka0 Ma0 Sa0 Ea6.
    intros s3a s5a.
    (* 81224 lbu a6,4(ra) : audio[g+4] = b0 *)
    pose proof (rdw m wr 4 _ _ A0 ltac:(nia)) as R. step. clear R A0.
    step. step. takeF false.
    step. takeF false.
    step. step. takeF false.
    (* 8123c addi a6,a5,1 *)
    step. gen_addi wa5 wa6b Ua6b.
    assert (Ea6b : bv_unsigned wa6b = pcm + (3 * ns * ch + 3 * s) + 1) by (rewrite Ua6b, Ea5; lia). clear Ua6b.
    destruct (addr_one m pcm (3 * nch * ns) (3 * ns * ch + 3 * s + 1) APD BP1) as (_ & kp1 & Mp1 & Sp1).
    eapply sc_p1o_F with (A := pcm + (3 * ns * ch + 3 * s + 1)) (k := kp1); [rewrite Ea6b; lia | lia | exact Mp1 | exact Sp1 | exact (shadow_sub RNG pcm (3 * nch * ns) _ BP1 RGSP) |]. clear kp1 Mp1 Sp1 Ea6b.
    intros a2b s5b.
    (* 81250 addi a6,a4,5 *)
    step. gen_addi wa4 wa6c Ua6c.
    assert (Ea6c : bv_unsigned wa6c = audio + (3 * nch * s + 3 * (2 * (ch / 2))) + 5) by (rewrite Ua6c, Ea4; lia). clear Ua6c.
    destruct (addr_one m audio (3 * nch * ns + 3 * (nch mod 2)) (3 * nch * s + 3 * (2 * (ch / 2)) + 5) AAD BA5) as (_ & ka1 & Ma1 & Sa1).
    eapply sc_a5_F with (A := audio + (3 * nch * s + 3 * (2 * (ch / 2)) + 5)) (b := b1) (D := pcm + 3 * (ch * ns + s));
      [rewrite Ea6c; lia | lia | exact Ma1 | exact Sa1 | rewrite Eq; nia | exact P1 | exact (shadow_sub RNG audio (3 * nch * ns + 3 * (nch mod 2)) _ BA5 RGSA) | eapply ExecF.rng_sub; [exact RGP | lia | lia] |]. clear ka1 Ma1 Sa1 Ea6c P1.
    intros a3c s5c.
    (* 81268 lbu a3,5(ra) : audio[g+5] = b1 *)
    pose proof (rdw m wr 5 _ _ A1 ltac:(nia)) as R. step. clear R A1.
    step. takeF false.
    step. step. takeF false.
    (* 81278 addi a5,a5,2 *)
    step. gen_addi wa5 wa5b Ua5b.
    assert (Ea5b : bv_unsigned wa5b = pcm + (3 * ns * ch + 3 * s) + 2) by (rewrite Ua5b, Ea5; lia). clear Ua5b Ea5.
    destruct (addr_one m pcm (3 * nch * ns) (3 * ns * ch + 3 * s + 2) APD BP2) as (_ & kp2 & Mp2 & Sp2).
    eapply sc_p2o_F with (A := pcm + (3 * ns * ch + 3 * s + 2)) (k := kp2); [rewrite Ea5b; lia | lia | exact Mp2 | exact Sp2 | exact (shadow_sub RNG pcm (3 * nch * ns) _ BP2 RGSP) |]. clear kp2 Mp2 Sp2 Ea5b.
    intros a2c a3d.
    (* 8128c addi a4,a4,2 *)
    step. gen_addi wa4 wa4b Ua4b.
    assert (Ea4b : bv_unsigned wa4b = audio + (3 * nch * s + 3 * (2 * (ch / 2))) + 2) by (rewrite Ua4b, Ea4; lia). clear Ua4b Ea4.
    destruct (addr_one m audio (3 * nch * ns + 3 * (nch mod 2)) (3 * nch * s + 3 * (2 * (ch / 2)) + 2) AAD BA2) as (_ & ka2 & Ma2 & Sa2).
    eapply sc_a2o_F with (A := audio + (3 * nch * s + 3 * (2 * (ch / 2)) + 2)) (b := b2) (D := pcm + 3 * (ch * ns + s));
      [rewrite Ea4b; lia | lia | exact Ma2 | exact Sa2 | rewrite Eq; nia | exact P2 | exact (shadow_sub RNG audio (3 * nch * ns + 3 * (nch mod 2)) _ BA2 RGSA) | eapply ExecF.rng_sub; [exact RGP | lia | lia] |]. clear ka2 Ma2 Sa2 Ea4b Eq P2.
    intros a2d a3e.
    (* 812a4 lbu a2,2(ra) : audio[g+2] = b2 *)
    pose proof (rdw m wr 2 _ _ A2 ltac:(nia)) as R. step. clear R A2.
    do 6 step.
    apply K; fact.
Qed.

Lemma inner_loop_F : forall ch (t1 t5 s6 s8 s9 : word),
  0 <= ch < nch -> bv_unsigned t1 = ch ->
  bv_unsigned t5 = pcm + 3 * ns * ch -> bv_unsigned s6 = pcm + 3 * ns * ch ->
  bv_unsigned s8 = 3 * (2 * (ch / 2)) -> bv_unsigned s9 = ch mod 2 ->
  (forall (ra t0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s10 s11 : word),
     bv_unsigned t0 = 0 -> bv_unsigned a7 = 3 * ns * ch ->
     ExecF.evtF rsegs RNG Q (ST 0x8134c ra t0 t1 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t5)) ->
  forall n s (ra t0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s10 s11 : word),
  0 <= s -> s + Z.of_nat (S n) = ns ->
  bv_unsigned t0 = 0 -> bv_unsigned a7 = 3 * ns * ch -> bv_unsigned s7 = 3 * s ->
  bv_unsigned s10 = audio + 3 * nch * s -> bv_unsigned s11 = audio + 3 * nch * s ->
  ExecF.evtF rsegs RNG Q (ST 0x81130 ra t0 t1 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t5).
Proof.
  intros ch t1 t5 s6 s8 s9 Hch Ht1 Ht5 Hs6 Hs8 Hs9 K n.
  induction n as [|n IH]; intros s ra t0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s10 s11 Hsz Hsn Ht0 Ha7 Hs7 Hs10 Hs11.
  - apply (body_F ch s ra t0 t1 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t5);
      try assumption; [lia|].
    intros ra' t0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s7' s10' s11' Ht0' Ha7' Hs7' Hs10' Hs11'.
    step. takeF false. step. apply K; [exact Ht0' | exact Ha7'].
  - apply (body_F ch s ra t0 t1 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t5);
      try assumption; [lia|].
    intros ra' t0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s7' s10' s11' Ht0' Ha7' Hs7' Hs10' Hs11'.
    step. takeF true. apply (IH (s + 1)); try assumption; lia.
Qed.
Lemma outer_loop_F : forall (w3 wc wn : word),
  ov_read_bytes rsegs m (wa (bv_unsigned sp)) 8 = Some (le8 w3) ->
  ov_read_bytes rsegs m (wa (bv_unsigned sp + 8)) 8 = Some (le8 wc) ->
  ov_read_bytes rsegs m (wa (bv_unsigned sp + 16)) 8 = Some (le8 wn) ->
  bv_unsigned w3 = 3 * ns -> bv_unsigned wc = nch -> bv_unsigned wn = ns ->
  ExecF.rng RNG (bv_unsigned sp) 24 ->
  (forall (ra t0 t1 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t5 : word),
     bv_unsigned t0 = 0 ->
     ExecF.evtF rsegs RNG Q (ST 0x8136c ra t0 t1 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t5)) ->
  forall k ch (ra t0 t1 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t5 : word),
  0 <= ch -> ch + Z.of_nat (S k) = nch ->
  bv_unsigned t0 = 0 -> bv_unsigned t1 = ch -> bv_unsigned a3 = ns ->
  bv_unsigned a7 = 3 * ns * ch -> bv_unsigned t5 = pcm + 3 * ns * ch -> bv_unsigned s6 = pcm + 3 * ns * ch ->
  ExecF.evtF rsegs RNG Q (ST 0x8110c ra t0 t1 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t5).
Proof.
  intros w3 wc wn Hsp0 Hsp8 Hsp16 Hw3 Hwc Hwn RSW K k.
  induction k as [|k IH];
    intros ch ra t0 t1 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t5 Hc0 Hck Ht0 Ht1 Ha3 Ha7 Ht5 Hs6.
  all: assert (Hch : 0 <= ch < nch) by lia.
  all: assert (B1 : 0 <= ns * ch <= 16129) by nia.
  all: assert (Hd1 : 0 <= ch / 2) by (apply Z.div_pos; lia).
  all: step; takeF false.
  all: do 8 step.
  all: eapply (inner_loop_F ch) with (n := Z.to_nat (ns - 1)) (s := 0) (t1 := t1) (t5 := t5) (s6 := s6);
    [ exact Hch | exact Ht1 | exact Ht5 | exact Hs6
    | rewrite Ht1; rewrite Z.shiftl_mul_pow2 by lia;
      rewrite (unsigned_lit (ch * 2 ^ 2)) by lia; rewrite (land_m8 (ch * 2 ^ 2)) by lia;
      rewrite (land_m2 ch) by lia;
      rewrite (unsigned_lit (8 * (ch * 2 ^ 2 / 8))) by (Z.div_mod_to_equations; lia);
      rewrite (unsigned_lit (2 * (ch / 2))) by (Z.div_mod_to_equations; lia);
      rewrite (unsigned_lit (8 * (ch * 2 ^ 2 / 8) - 2 * (ch / 2))) by (Z.div_mod_to_equations; lia);
      Z.div_mod_to_equations; lia
    | rewrite Ht1; rewrite (land_1u ch); rewrite (unsigned_lit (ch mod 2)) by (Z.div_mod_to_equations; lia); reflexivity
    |
    | lia
    | rewrite Nat2Z.inj_succ, Z2Nat.id by lia; lia
    | exact Ht0
    | exact Ha7
    | rewrite (unsigned_lit 0) by lia; lia
    | rewrite (unsigned_lit audio) by lia; lia
    | rewrite (unsigned_lit audio) by lia; lia ].
  - intros ra' t0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s7' s10' s11' Ht0' Ha7'.
    step.
    pose proof Hsp0 as RD0. rewrite Z_to_bv_bv_unsigned in RD0. step. clear RD0.
    do 3 step.
    pose proof Hsp16 as RD16. step. clear RD16.
    pose proof Hsp8 as RD8. step. clear RD8.
    step. takeF false. apply K. exact Ht0'.
  - intros ra' t0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s7' s10' s11' Ht0' Ha7'.
    step.
    pose proof Hsp0 as RD0. rewrite Z_to_bv_bv_unsigned in RD0. step. clear RD0.
    do 3 step.
    pose proof Hsp16 as RD16. step. clear RD16.
    pose proof Hsp8 as RD8. step. clear RD8.
    step. takeF true.
    apply (IH (ch + 1));
      [ lia | lia | exact Ht0'
      | rewrite (unsigned_lit (bv_unsigned t1 + 1)) by lia; rewrite Ht1; lia
      | exact Hwn
      | rewrite Hw3; rewrite ?Ha7';
        repeat (match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by nia end); nia
      | rewrite Hw3; rewrite ?Ht5;
        repeat (match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by nia end); nia
      | rewrite Hw3; rewrite ?Hs6;
        repeat (match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by nia end); nia ].
Qed.
End LoopsF.

Theorem check_braid_holds_F : check_braid_contract_F.
Proof.
  unfold check_braid_contract_F, CHECK_BRAID, CHECK_BRAID_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m audio pcm nch ns lo
    HN HS HA HP BR STK HLO DA DP CELLS APW1 APW2 DC AAD APD RFR RGC RCK RGA RGP RGSA RGSP.
  unfold GOT_CELL_K in RGC. unfold CELL_K in RCK.
  pose proof (u64_range sp) as Rsp.
  pose proof (proj1 STK) as Hlo0.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold off_stk, GOT_CELL_K, MIDEND in DC.
  carve_frame 128%nat STK.
  do 14 step.
  match goal with H : munch _ m ?m1 |- _ => assert (CELLS1 : asan_cells m1)
    by (eapply asan_cells_munch; [exact CELLS | exact H | unfold MIDEND, GOT_CELL_K; lia]) end.
  pose proof CELLS1 as (CK & GCK & _).
  unfold CELL_K, GOT_CELL_K, ASAN_K in CK, GCK.
  pose proof (rd_all _ _ _ GCK) as RDG. rewrite length_le8 in RDG.
  step. takeF false.
  do 5 step. step. do 3 step. step. do 2 step.
  do 2 step. step.
  match goal with H : munch _ m ?m2 |- _ => assert (CELLS2 : asan_cells m2)
    by (eapply asan_cells_munch; [exact CELLS | exact H | unfold MIDEND, GOT_CELL_K; lia]) end.
  pose proof CELLS2 as (CK2 & GCK2 & _).
  unfold CELL_K, GOT_CELL_K, ASAN_K in CK2.
  pose proof (rd_all _ _ _ CK2) as RDS. rewrite length_le8 in RDS.
  do 3 step. step. do 5 step.
  match goal with
  | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mF _) =>
    assert (BR1 : braid_map mF audio pcm nch ns)
      by exact (braid_transport m mF audio pcm nch ns (bv_unsigned sp - 128) (bv_unsigned sp) HN HS ltac:(lia) HP MU DA DP BR);
    assert (AAD1 : addressable mF audio (3 * nch * ns + 3 * (nch mod 2)))
      by exact (addr_transport m mF (bv_unsigned sp) audio (3 * nch * ns + 3 * (nch mod 2)) AAD MU ltac:(lia) APW1 APW2);
    assert (APD1 : addressable mF pcm (3 * nch * ns))
      by exact (addr_transport m mF (bv_unsigned sp) pcm (3 * nch * ns) APD MU ltac:(lia) APW1 APW2)
  end.
  pose proof (rw_cells_read_at rsegs _ _ _ 0%nat _ _ _ FR ltac:(cells_cbv; reflexivity) eq_refl eq_refl) as SP0.
  pose proof (rw_cells_read_at rsegs _ _ _ 8%nat _ _ _ FR ltac:(cells_cbv; reflexivity) eq_refl eq_refl) as SP8.
  pose proof (rw_cells_read_at rsegs _ _ _ 16%nat _ _ _ FR ltac:(cells_cbv; reflexivity) eq_refl eq_refl) as SP16.
  cbv [csize cbytes] in SP0, SP8, SP16.
  cbn [Z.of_nat] in SP0, SP8, SP16.
  rewrite Z.add_0_r in SP0.
    eapply outer_loop_F with (k := Z.to_nat (nch - 1)) (ch := 0);
    [ exact HN | exact HS | exact HA | exact HP | exact BR1 | exact AAD1 | exact APD1
    | exact RGA | exact RGP | exact RGSA | exact RGSP
    | fact | fact | fact | fact | fact | fact | fact
    | rewrite (unsigned_lit (bv_unsigned sp + -128)) by lia; exact SP0
    | rewrite (unsigned_lit (bv_unsigned sp + -128)) by lia; exact SP8
    | rewrite (unsigned_lit (bv_unsigned sp + -128)) by lia; exact SP16
    | fact | fact | fact
    | rewrite (unsigned_lit (bv_unsigned sp + -128)) by lia; eapply ExecF.rng_sub; [exact RFR | lia | lia]
    | intros raK t0K t1K a1K a2K a3K a4K a5K a6K a7K s3K s5K s6K s7K s8K s9K s10K s11K t5K Ht0K;
      step; takeF false; do 15 step;
      apply evtF_done; do 16 eexists; split; [reflexivity|]; split; [eassumption|]; split; [eassumption|];
      release_frame FR STK (bv_unsigned sp); exact STK
    | lia
    | rewrite Nat2Z.inj_succ, Z2Nat.id by lia; lia
    | fact | fact | fact | fact | fact | fact ].
Qed.

(* The twin implies the original: take the footprint that admits every access. *)
Theorem check_braid_holds_of_F : check_braid_contract.
Proof.
  unfold check_braid_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m audio pcm nch ns lo
    HN HS HA HP BR STK HLO DA DP CELLS APW1 APW2 DC AAD APD.
  pose proof (u64_range sp) as Rsp. pose proof (proj1 STK) as Hlo0.
  pose proof (proj1 (proj2 (proj2 AAD))) as BA. pose proof (proj1 (proj2 (proj2 APD))) as BP.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply check_braid_holds_F; try assumption;
    apply ExecF.rng_all; unfold CHECK_BRAID_FRAME, GOT_CELL_K, CELL_K, ASAN_K, APPMEM_END in *;
    Z.div_mod_to_equations; lia.
Qed.
