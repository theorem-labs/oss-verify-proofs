(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/FP.v; 609 of its 651 lines of code are new or changed and 349 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/crtA_conv.v; 206 of its 430 lines of code are new or changed and 427 lines of the source are left out. *)
(* crtA_loop: the footprint (lib/Lib/ExecF.v evtF) twin of the convert loop of check_round_trip in image A
   (fuzz_decode.asan), for the cgif-form walk of lib/A/Prog/check_round_trip_cg.v.  It states crt_loop_stmt_F and
   proves it as crt_loop_holds_F.

   PORT of the record of the same function,
   a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Prog/crt_loopF.v:1-470 (the walk) and
   a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Prog/crt_iface_F.v:25-61 (the statement
   crt_loop_stmt_F, which the record keeps in a separate interface file and which stands here at the head of the
   file that proves it).  Every lemma name, every proof and every comment is the record's.  Four things are not:
     - the ASan address predicates come from lib/A/AsanCells.v, not from the record's lib/A/AsanRT.v, which is not
       on this branch.  AsanCells.v is the verbatim split of that file's constants and address predicates, so the
       names and the bodies are the same.
     - no image address is spelled out.  Every program address is a name of lib/A/Prog/crtA_iface.v: CRT_LOOP_IN
       (= CRT_AT 0xd4) and CRT_LOOP_OUT (= CRT_AT 0x1f0) are the two ends of the loop, CRT_A5 is the value the
       lui a5 at +0xac writes, and each interior point is CRT_AT <offset from CRT_ENTRY>.  CRT_ENTRY =
       decode_sigma DS_check_round_trip is the entry the record walks from, so the record's convert loop is
       CRT_AT 0xd4 .. CRT_AT 0x1f0 here.
     - the memory-side lemmas of lib/A/Prog/crtA_conv.v take one fixed argument list, m0 pb P Q pcm nch ns
       HN .. DQC (crtA_conv.v closes them with `Proof using All`; see its header), so the Local Notations NN ..
       SHST8 below and the crt_inv_init call in crt_loop_holds_F pass that list instead of the record's per-lemma
       lists, and crt_outer_F is closed with `Proof using All` so that crt_loop_holds_F's argument list for it is
       fixed too.  No proof step is changed.
     - step is redefined locally as crt_lits followed by lib/Lib/StepF.v's step: inside the proofs each CRT_AT o
       is first computed to its value, so the walk runs on numeral pcs as the record's did (see crt_lits); and
       lia / nia are restored locally to the Stdlib definitions, as in crtA_conv.v (see after the imports). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac
  Bytes ZBridge FP.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import AsanKA AsanKAProof ReacDecodeLib check_braid
  crtA_iface crtA_conv crtA_loop_stmt.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import FloatExact.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Not in the record: as in crtA_conv.v, Requiring crtA_iface.v loads lib/Reusable/YM03.v, whose global
   `Ltac Lia.lia ::=` / `Ltac Lia.nia ::=` (YM03.v:182-189) the record's proofs were not built under; this file
   restores, for itself only, the record's tactics: lia as lib/Lib/LiaTwx2.v:187-190 defines it and nia as Stdlib
   defines it (YM03.v:180 lf_nia_orig).  With plain Stdlib lia instead, crt_body_F ran for an hour at 17-22 GB. *)
Local Ltac Lia.lia ::=
  first [ LiaTwx2.zify_prune; LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTwx2.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
Local Ltac Lia.nia ::= Zify.zify; xnia zchecker.

(* The statement crt_loop_stmt_F is in lib/A/Prog/crtA_loop_stmt.v (ported from
   a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Prog/crt_iface_F.v:25-61), so that its
   user lib/A/Prog/crtA_w_mid.v states against a committed text independent of this proof. *)

(* Footprint twin of the convert loop of check_round_trip (A image, +0xd4 -> +0x1f0): crt_loop_holds_F proves
   crt_loop_stmt_F (lib/A/Prog/crtA_loop_stmt.v), the run as an ExecF.evtF run under a footprint RNG that holds the P block, the
   Q block, the pcm bytes and the 8-aligned cover of the shadow bytes of the three blocks. The proof is the proof of
   crtA_conv.v step for step, with StepF's step: cl1_F, cl2_F, cl3_F, cls4_F and csh_q8_F take the 1-byte range of
   each shadow byte and of each data byte they load, crt_body_F the 4-byte range of its store at P + 4k, crt_outer_F
   the 8-byte range of its store at Q + 8c. The memory-side lemmas of crtA_conv.v (crt_inv and its transport
   lemmas) are build-independent and are used unchanged. *)

Ltac takeF b := lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; solve_c]
  end.

(* ---- the two range facts the loop needs out of the statement's six rng premises ---- *)

(* [a, c] inside the 8-aligned cover of [a, c]: a byte of the cover's first word is at or after a / 8 * 8, and a
   byte at or before c is before c / 8 * 8 + 8. *)
Lemma align8_cover : forall a b c, a <= b -> b <= c -> a / 8 * 8 <= b /\ b + 1 <= c / 8 * 8 + 8.
Proof. intros a b c H1 H2. split; Z.div_mod_to_equations; lia. Qed.

(* The shadow byte of X + i, for i in [0, n), lies in the 8-aligned cover of the shadow bytes of [X, X + n). *)
Lemma crt_sh1F : forall RNG X n i,
  ExecF.rng RNG (shadow_addr X / 8 * 8)
    (shadow_addr (X + n - 1) / 8 * 8 + 8 - shadow_addr X / 8 * 8) ->
  0 <= i < n ->
  ExecF.rng RNG ((X + i) / 8 + ASAN_K) 1.
Proof.
  intros RNG X n i H Hi. unfold shadow_addr in H.
  assert (L1 : X / 8 <= (X + i) / 8) by (apply Z.div_le_mono; lia).
  assert (L2 : (X + i) / 8 <= (X + n - 1) / 8) by (apply Z.div_le_mono; lia).
  destruct (align8_cover (X / 8 + ASAN_K) ((X + i) / 8 + ASAN_K) ((X + n - 1) / 8 + ASAN_K)
             ltac:(lia) ltac:(lia)) as (A1 & A2).
  eapply ExecF.rng_sub; [exact H | lia | lia].
Qed.

Local Ltac fct := try unfold wa; norm;
  first [ reflexivity | rng | (rewrite ?unsigned_lit_wrap; zb_fold_lits; Z.div_mod_to_equations; lia) ].
Local Ltac word_eq_tac ::= first [ exact eq_refl | f_equal; lia | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia
  | (norm; first [ reflexivity | f_equal; lia | lia ]) ].

(* Not in the record: as in crtA_conv.v, the statements name every pc as CRT_AT off, and inside the proofs only
   each step first replaces every CRT_AT o of the goal and of the hypotheses by its value, computed by vm_compute
   (no numeral is written here), so the walk runs on numeral pcs as the record's did.  The step body after
   crt_lits is lib/Lib/StepF.v's step. *)
Local Ltac crt_lits :=
  repeat match goal with
  | |- context [CRT_AT ?o] => let v := eval vm_compute in (CRT_AT o) in change (CRT_AT o) with v
  | H : context [CRT_AT ?o] |- _ => let v := eval vm_compute in (CRT_AT o) in change (CRT_AT o) with v in H
  end.
Local Ltac step ::= crt_lits; stepF_k ltac:(idtac).

(* =========================================================================
   Footprint twins of the convert-loop shadow checks (+0x10c..+0x164) of crtA_conv.v. Each takes the 1-byte
   range of the shadow byte it loads, and cl2, cl3, cls4 the 1-byte range of the data byte they load.
   ========================================================================= *)

(* CL1 @+0x10c -> +0x120 : addr a1 := t0 + t3, shadow/lb into a2, handler andi t5 *)
Lemma cl1_F : forall (RNG : ExecF.footprint)
  (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x5 + bv_unsigned x28 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  ExecF.rng RNG (A / 8 + ASAN_K) 1 ->
  (forall y11 y12 y30 : word, bv_unsigned y11 = A ->
     ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y11 y12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 2147450880) x25 x26 x27 x28 x29 y30 x31) F (Z_to_bv 64 (CRT_AT 0x120)) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 2147450880) x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (CRT_AT 0x10c)) fc None mm (seg_rom rsegs)).
Proof.
  intros until A. intros EA RA M SK RK CONT.
  pose proof (u64_range x5) as R5. pose proof (u64_range x28) as R28. unfold ASAN_K in M, RK.
  step. gen_add x5 x28 w U. rewrite EA in U.
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

(* CL2 @+0x120 -> +0x13c : t6 := s6+t3 ; shadow of a1+1 (lb s9) ; data b0 := [t6] (lbu t5) ; handler andi s10 *)
Lemma cl2_F : forall (RNG : ExecF.footprint)
  (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b0 : byte) (A Dd : Z),
  bv_unsigned x11 = A -> A + 1 < 2^64 ->
  mrd rsegs mm (wa ((A + 1) / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ (A + 1) mod 8 < bv_signed k) ->
  bv_unsigned x22 + bv_unsigned x28 = Dd -> Dd + 2 < 2^64 -> mrd rsegs mm (wa Dd) = Some b0 ->
  ExecF.rng RNG ((A + 1) / 8 + ASAN_K) 1 -> ExecF.rng RNG Dd 1 ->
  (forall y12 y25 y26 y31 : word, bv_unsigned y31 = Dd ->
     ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 y12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 2147450880) y25 y26 x27 x28 x29 (zxb b0) y31) F (Z_to_bv 64 (CRT_AT 0x13c)) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 2147450880) x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (CRT_AT 0x120)) fc None mm (seg_rom rsegs)).
Proof.
  intros until Dd. intros E11 RA M SK Ed DB MD RK RD CONT.
  pose proof (u64_range x11) as R11. pose proof (u64_range x22) as R22. pose proof (u64_range x28) as R28.
  unfold ASAN_K in M, RK.
  step. gen_add x22 x28 wt6 Ut6. rewrite Ed in Ut6.
  step. gen_addi x11 wa2 Ua2. rewrite E11 in Ua2.
  step. gen_shr wa2 g G. rewrite Ua2 in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw0 mm wt6 _ _ MD Ut6) as R2. step. clear R2.
  step.
  pose proof (Z.mod_pos_bound (A + 1) 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT. exact Ut6.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, Ua2, (lts_low ((A + 1) mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT. exact Ut6.
Qed.

(* CL3 @+0x13c -> +0x154 : a1 := a1+2 ; shadow of a1 (lb s9) ; data b1 := [t6+1] (lbu a2) ; handler andi s10 *)
Lemma cl3_F : forall (RNG : ExecF.footprint)
  (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b1 : byte) (A Dd : Z),
  bv_unsigned x11 = A -> A + 2 < 2^64 ->
  mrd rsegs mm (wa ((A + 2) / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ (A + 2) mod 8 < bv_signed k) ->
  bv_unsigned x31 = Dd -> mrd rsegs mm (wa (Dd + 1)) = Some b1 ->
  ExecF.rng RNG ((A + 2) / 8 + ASAN_K) 1 -> ExecF.rng RNG (Dd + 1) 1 ->
  (forall y11 y25 y26 : word, bv_unsigned y11 = A + 2 ->
     ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y11 (zxb b1) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 2147450880) y25 y26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (CRT_AT 0x154)) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 2147450880) x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (CRT_AT 0x13c)) fc None mm (seg_rom rsegs)).
Proof.
  intros until Dd. intros E11 RA M SK Ed MD RK RD CONT.
  pose proof (u64_range x11) as R11. pose proof (u64_range x31) as R31. unfold ASAN_K in M, RK.
  step. gen_addi x11 wa1 Ua1. rewrite E11 in Ua1.
  step. gen_shr wa1 g G. rewrite Ua1 in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw mm x31 1 _ _ MD ltac:(lia)) as R2. step. clear R2.
  step.
  pose proof (Z.mod_pos_bound (A + 2) 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT. exact Ua1.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, Ua1, (lts_low ((A + 2) mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT. exact Ua1.
Qed.

(* CLS4 @+0x154 -> +0x168 : shadow of a0 (store4; lb s9) ; data b2 := [t6+2] (lb a1, signed) ; handler andi t6 + addi 3 *)
Lemma cls4_F : forall (RNG : ExecF.footprint)
  (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b2 : byte) (A Dd : Z),
  bv_unsigned x10 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 + 3 < bv_signed k) ->
  bv_unsigned x31 = Dd -> mrd rsegs mm (wa (Dd + 2)) = Some b2 ->
  ExecF.rng RNG (A / 8 + ASAN_K) 1 -> ExecF.rng RNG (Dd + 2) 1 ->
  (forall y25 y31 : word,
     ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (sxb b2) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 2147450880) y25 x26 x27 x28 x29 x30 y31) F (Z_to_bv 64 (CRT_AT 0x168)) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 2147450880) x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (CRT_AT 0x154)) fc None mm (seg_rom rsegs)).
Proof.
  intros until Dd. intros E10 RA M SK Ed MD RK RD CONT.
  pose proof (u64_range x10) as R10. pose proof (u64_range x31) as R31. unfold ASAN_K in M, RK.
  step. gen_shr x10 g G. rewrite E10 in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw mm x31 2 _ _ MD ltac:(lia)) as R2. step. clear R2.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. step. rewrite land7, E10, (lts_sm (A mod 8 + 3) k ltac:(lia)), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* CSH_Q8 @+0xdc -> +0xec : 8-byte store shadow of a0 (lbu a1) ; shadow byte must be 0 *)
Lemma csh_q8_F : forall (RNG : ExecF.footprint)
  (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x10 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k -> bv_unsigned k = 0 ->
  ExecF.rng RNG (A / 8 + ASAN_K) 1 ->
  (forall y11 : word,
     ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 2147450880) x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (CRT_AT 0xec)) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 2147450880) x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 (CRT_AT 0xdc)) fc None mm (seg_rom rsegs)).
Proof.
  intros until A. intros EA RA M HK RK CONT.
  pose proof (u64_range x10) as R10. unfold ASAN_K in M, RK.
  step. gen_shr x10 g G. rewrite EA in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  replace (zxb k) with (Z_to_bv 64 0) by (unfold zxb; rewrite HK; reflexivity).
  step. apply CONT.
Qed.

(* The two stores of the loop write through a register the code computes (a0 = Q + 8c for the 8-byte store, t4 =
   P + 4k for the 4-byte store), so their access address is a nest of Z_to_bv terms that lia reads as one atom.
   StepF's acc_hint hook (StepF.v:184) takes the access to a range hypothesis and normalises the address first,
   with the same norm the store's own address equality uses. *)
Local Ltac acc_hint ::=
  lazymatch goal with
  | |- ExecF.acc_in ?RNG (?a, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      match goal with
      | HR : ExecF.rng RNG ?lo ?len |- _ =>
          apply (ExecF.rng_acc_varZ RNG lo len a n nz HR (@eq_refl Z nz)); norm; lia
      end
  end.

(* =========================================================================
   The convert loop (+0xd4..+0x1f0) under a footprint. The section carries the premises of crtA_conv.v's
   Section Loops, then the footprint RNG and the six rng premises crt_loop_stmt_F names.
   ========================================================================= *)
Section LoopsF.
Variables (ra sp gp tp s1 s4 s7 s11 : word) (m0 : word -> option byte) (pb : Z -> byte)
  (P Q pcm nch ns : Z).
Hypothesis HN : 2 <= nch <= 127.
Hypothesis HNS : 1 <= ns <= 12.
Hypothesis HB : 3 * nch * ns <= 1440.
Hypothesis HP0 : 0 < P.
Hypothesis HP1 : P + 4 * nch * ns < 2^63.
Hypothesis HP2 : P mod 16 = 0.
Hypothesis HQ0 : 0 < Q.
Hypothesis HQ1 : Q + 8 * nch < 2^63.
Hypothesis HQ2 : Q mod 16 = 0.
Hypothesis HC0 : 0 < pcm.
Hypothesis HC1 : pcm + 3 * nch * ns < 2^63.
Hypothesis PB : forall i, 0 <= i < 3 * nch * ns -> mrd rsegs m0 (wa (pcm + i)) = Some (pb i).
Hypothesis WP : wr_at rsegs m0 P (4 * nch * ns).
Hypothesis WQ : wr_at rsegs m0 Q (8 * nch).
Hypothesis ADP : addressable m0 P (4 * nch * ns).
Hypothesis ADQ : addressable m0 Q (8 * nch).
Hypothesis ADC : addressable m0 pcm (3 * nch * ns).
Hypothesis DPQ : P + 4 * nch * ns <= Q \/ Q + 8 * nch <= P.
Hypothesis DPC : P + 4 * nch * ns <= pcm \/ pcm + 3 * nch * ns <= P.
Hypothesis DQC : Q + 8 * nch <= pcm \/ pcm + 3 * nch * ns <= Q.
Variable G : machine_state -> Prop.
Variable RNG : ExecF.footprint.
Hypothesis RP : ExecF.rng RNG P (4 * nch * ns).
Hypothesis RQ : ExecF.rng RNG Q (8 * nch).
Hypothesis RC : ExecF.rng RNG pcm (3 * nch * ns).
Hypothesis RSP : ExecF.rng RNG (shadow_addr P / 8 * 8)
  (shadow_addr (P + 4 * nch * ns - 1) / 8 * 8 + 8 - shadow_addr P / 8 * 8).
Hypothesis RSQ : ExecF.rng RNG (shadow_addr Q / 8 * 8)
  (shadow_addr (Q + 8 * nch - 1) / 8 * 8 + 8 - shadow_addr Q / 8 * 8).
Hypothesis RSC : ExecF.rng RNG (shadow_addr pcm / 8 * 8)
  (shadow_addr (pcm + 3 * nch * ns - 1) / 8 * 8 + 8 - shadow_addr pcm / 8 * 8).

(* The memory-side lemmas of crtA_conv.v, at this section's premises.  The record gave each its own argument
   list (the premises its proof happened to use); crtA_conv.v closes every one of them with `Proof using All`
   ahead of the register words, so each takes the same list: m0 pb P Q pcm nch ns and HN .. DQC. *)
Local Notation INV := (crt_inv m0 pb P Q nch ns) (only parsing).
Local Notation NN := (crt_nn m0 pb P Q pcm nch ns HN HNS HB HP0 HP1 HP2 HQ0 HQ1 HQ2 HC0 HC1 PB WP WQ ADP ADQ ADC
  DPQ DPC DQC) (only parsing).
Local Notation INVPCM := (crt_inv_pcm m0 pb P Q pcm nch ns HN HNS HB HP0 HP1 HP2 HQ0 HQ1 HQ2 HC0 HC1 PB WP WQ ADP ADQ
  ADC DPQ DPC DQC) (only parsing).
Local Notation INVSTP := (crt_stP m0 pb P Q pcm nch ns HN HNS HB HP0 HP1 HP2 HQ0 HQ1 HQ2 HC0 HC1 PB WP WQ ADP ADQ ADC
  DPQ DPC DQC) (only parsing).
Local Notation INVSTQ := (crt_stQ m0 pb P Q pcm nch ns HN HNS HB HP0 HP1 HP2 HQ0 HQ1 HQ2 HC0 HC1 PB WP WQ ADP ADQ ADC
  DPQ DPC DQC) (only parsing).
Local Notation INVP := (crt_inv_P m0 pb P Q pcm nch ns HN HNS HB HP0 HP1 HP2 HQ0 HQ1 HQ2 HC0 HC1 PB WP WQ ADP ADQ ADC
  DPQ DPC DQC) (only parsing).
Local Notation INVQ := (crt_inv_Q m0 pb P Q pcm nch ns HN HNS HB HP0 HP1 HP2 HQ0 HQ1 HQ2 HC0 HC1 PB WP WQ ADP ADQ ADC
  DPQ DPC DQC) (only parsing).
Local Notation SHPCM := (crt_sh_pcm m0 pb P Q pcm nch ns HN HNS HB HP0 HP1 HP2 HQ0 HQ1 HQ2 HC0 HC1 PB WP WQ ADP ADQ
  ADC DPQ DPC DQC) (only parsing).
Local Notation SHST4 := (crt_sh_store4 m0 pb P Q pcm nch ns HN HNS HB HP0 HP1 HP2 HQ0 HQ1 HQ2 HC0 HC1 PB WP WQ ADP ADQ
  ADC DPQ DPC DQC) (only parsing).
Local Notation SHST8 := (crt_sh_store8 m0 pb P Q pcm nch ns HN HNS HB HP0 HP1 HP2 HQ0 HQ1 HQ2 HC0 HC1 PB WP WQ ADP ADQ
  ADC DPQ DPC DQC) (only parsing).

Local Notation CSTF pc t0 t1 t2 a0 a1 a2 a3 s6 s9 s10 t3 t4 t5 t6 Fh fc m :=
  (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 P) s1 a0 a1 a2 a3 (Z_to_bv 64 (4 * ns)) (Z_to_bv 64 18446744073692774400)
           (Z_to_bv 64 (3 * ns)) (Z_to_bv 64 (3 * ns)) (Z_to_bv 64 ns) (Z_to_bv 64 nch) s4 (Z_to_bv 64 Q) s6 s7
           (Z_to_bv 64 2147450880) s9 s10 s11 t3 t4 t5 t6)
      Fh (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Lemma crt_body_F : forall ch s (t0 t1 t2 a3 s6 a0 a1 a2 s9 s10 t3 t4 t5 t6 : word) (Fh : bvmap 5 word) (fc : bv 32) m,
  0 <= ch < nch -> 0 <= s < ns ->
  bv_unsigned t0 = pcm + 3 * ns * ch -> bv_unsigned s6 = pcm + 3 * ns * ch -> bv_unsigned a3 = ch ->
  bv_unsigned a0 = P + 4 * (ch * ns + s) -> bv_unsigned t4 = P + 4 * (ch * ns + s) -> bv_unsigned t3 = 3 * s ->
  unbox_s (reg_get Fh (Z_to_bv 5 15)) = Z_to_bv 32 F2M23 -> frm0 fc -> INV m (ch * ns + s) (ch + 1) ->
  (forall (a0' a1' a2' s9' s10' t3' t4' t5' t6' v : word) (fc' : bv 32) m',
     bv_unsigned a0' = P + 4 * (ch * ns + s + 1) -> bv_unsigned t3' = 3 * (s + 1) ->
     bv_unsigned t4' = P + 4 * (ch * ns + s + 1) -> frm0 fc' -> INV m' (ch * ns + s + 1) (ch + 1) ->
     ExecF.evtF rsegs RNG G (CSTF (CRT_AT 0x19c) t0 t1 t2 a0' a1' a2' a3 s6 s9' s10' t3' t4' t5' t6' (bvmap_set (Z_to_bv 5 14) v Fh) fc' m')) ->
  ExecF.evtF rsegs RNG G (CSTF (CRT_AT 0x10c) t0 t1 t2 a0 a1 a2 a3 s6 s9 s10 t3 t4 t5 t6 Fh fc m).
Proof.
  intros ch s t0 t1 t2 a3 s6 a0 a1 a2 s9 s10 t3 t4 t5 t6 Fh fc m
    Hch Hs Ht0 Hs6 Ha3 Ha0 Ht4 Ht3 H15 Hfc Hinv K.
  pose proof NN as NNf.
  assert (B1 : ch * ns <= (nch - 1) * ns) by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (B1' : (nch - 1) * ns = nch * ns - ns) by ring.
  assert (Hmc : 0 <= ch * ns) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Hk : 0 <= ch * ns + s < nch * ns) by lia.
  assert (Bn : 0 <= 3 * (ch * ns + s) + 2 < 3 * nch * ns)
    by (replace (3 * nch * ns) with (3 * (nch * ns)) by ring; lia).
  (* the ranges of the three data bytes, of the 4-byte store and of the four shadow bytes this body touches *)
  assert (RD0 : ExecF.rng RNG (pcm + 3 * (ch * ns + s)) 1)
    by (eapply ExecF.rng_sub; [exact RC | lia | lia]).
  assert (RD1 : ExecF.rng RNG (pcm + 3 * (ch * ns + s) + 1) 1)
    by (eapply ExecF.rng_sub; [exact RC | lia | lia]).
  assert (RD2 : ExecF.rng RNG (pcm + 3 * (ch * ns + s) + 2) 1)
    by (eapply ExecF.rng_sub; [exact RC | lia | lia]).
  assert (RW4 : ExecF.rng RNG (P + 4 * (ch * ns + s)) 4)
    by (eapply ExecF.rng_sub; [exact RP | lia | lia]).
  assert (RS0 : ExecF.rng RNG ((pcm + 3 * (ch * ns + s)) / 8 + ASAN_K) 1)
    by (apply (crt_sh1F RNG pcm (3 * nch * ns) (3 * (ch * ns + s)) RSC); lia).
  assert (RS1 : ExecF.rng RNG ((pcm + 3 * (ch * ns + s) + 1) / 8 + ASAN_K) 1)
    by (replace (pcm + 3 * (ch * ns + s) + 1) with (pcm + (3 * (ch * ns + s) + 1)) by ring;
        apply (crt_sh1F RNG pcm (3 * nch * ns) (3 * (ch * ns + s) + 1) RSC); lia).
  assert (RS2 : ExecF.rng RNG ((pcm + 3 * (ch * ns + s) + 2) / 8 + ASAN_K) 1)
    by (replace (pcm + 3 * (ch * ns + s) + 2) with (pcm + (3 * (ch * ns + s) + 2)) by ring;
        apply (crt_sh1F RNG pcm (3 * nch * ns) (3 * (ch * ns + s) + 2) RSC); lia).
  assert (RSW : ExecF.rng RNG ((P + 4 * (ch * ns + s)) / 8 + ASAN_K) 1)
    by (apply (crt_sh1F RNG P (4 * nch * ns) (4 * (ch * ns + s)) RSP); lia).
  pose proof (INVPCM m _ _ (3 * (ch * ns + s)) Hinv ltac:(lia)) as M0.
  pose proof (INVPCM m _ _ (3 * (ch * ns + s) + 1) Hinv ltac:(lia)) as M1.
  pose proof (INVPCM m _ _ (3 * (ch * ns + s) + 2) Hinv ltac:(lia)) as M2.
  destruct (SHPCM m _ _ (3 * (ch * ns + s)) Hinv ltac:(lia)) as (kp0 & Mp0 & Sp0).
  destruct (SHPCM m _ _ (3 * (ch * ns + s) + 1) Hinv ltac:(lia)) as (kp1 & Mp1 & Sp1).
  destruct (SHPCM m _ _ (3 * (ch * ns + s) + 2) Hinv ltac:(lia)) as (kp2 & Mp2 & Sp2).
  destruct (SHST4 m _ _ (ch * ns + s) Hinv Hk) as (ks & Ms & Ss).
  pose proof (INVSTP m (ch * ns + s) (ch + 1) t4 Hinv Hk Ht4) as HSt.
  (* cl1 : shadow pcm + 3k, addr t0+t3 *)
  eapply cl1_F with (A := pcm + 3 * (ch * ns + s)) (k := kp0);
    [ rewrite Ht0, Ht3; ring | lia | exact Mp0 | exact Sp0 | exact RS0 |].
  intros wa1 wa12 w30 Ea1.
  (* cl2 : shadow pcm + 3k + 1, data b0 at pcm+3k *)
  eapply cl2_F with (A := pcm + 3 * (ch * ns + s)) (Dd := pcm + 3 * (ch * ns + s)) (k := kp1) (b0 := pb (3 * (ch * ns + s)));
    [ exact Ea1 | lia | replace (pcm + 3 * (ch * ns + s) + 1) with (pcm + (3 * (ch * ns + s) + 1)) by ring; exact Mp1
    | replace (pcm + 3 * (ch * ns + s) + 1) with (pcm + (3 * (ch * ns + s) + 1)) by ring; exact Sp1
    | rewrite Hs6, Ht3; ring | lia | exact M0 | exact RS1 | exact RD0 |].
  intros w12 w25 w26 w31 Et6.
  (* cl3 : shadow pcm + 3k + 2, data b1 at pcm+3k+1 *)
  eapply cl3_F with (A := pcm + 3 * (ch * ns + s)) (Dd := pcm + 3 * (ch * ns + s)) (k := kp2) (b1 := pb (3 * (ch * ns + s) + 1));
    [ exact Ea1 | lia | replace (pcm + 3 * (ch * ns + s) + 2) with (pcm + (3 * (ch * ns + s) + 2)) by ring; exact Mp2
    | replace (pcm + 3 * (ch * ns + s) + 2) with (pcm + (3 * (ch * ns + s) + 2)) by ring; exact Sp2
    | exact Et6 | replace (pcm + 3 * (ch * ns + s) + 1) with (pcm + (3 * (ch * ns + s) + 1)) by ring; exact M1
    | exact RS2 | exact RD1 |].
  intros wa1b w25b w26b Ea1b.
  (* cls4 : shadow store target P+4k, data b2 at pcm+3k+2 *)
  eapply cls4_F with (A := P + 4 * (ch * ns + s)) (Dd := pcm + 3 * (ch * ns + s)) (k := ks) (b2 := pb (3 * (ch * ns + s) + 2));
    [ exact Ha0 | lia | exact Ms | exact Ss | exact Et6
    | replace (pcm + 3 * (ch * ns + s) + 2) with (pcm + (3 * (ch * ns + s) + 2)) by ring; exact M2
    | exact RSW | exact RD2 |].
  intros w25c w31c.
  (* assemble (9 int ops), then abstract the fcvt input before the FP store to keep it symbolic *)
  clear M0 M1 M2 Mp0 Mp1 Mp2 Sp0 Sp1 Sp2 Ms Ss NNf B1 B1' Hmc Bn RD0 RD1 RD2 RS0 RS1 RS2 RSW.
  do 10 step.
  match goal with |- context [fcvt_s_w ?md ?w] => remember w as W eqn:EW end.
  do 3 step.
  apply K; [ fct | fct | fct | assumption |].
  eapply INVP; [ exact Hinv | lia | lia | exact Ht4 |].
  unfold cv. apply conv_bytes;
    [ exact H15
    | rewrite EW; apply (comb _ _ _ (Z_to_bv 64 18446744073692774400)); apply unsigned_lit; lia ].
Qed.

Lemma crt_inner_F : forall ch (t0 t1 t2 a3 s6 : word),
  0 <= ch < nch ->
  bv_unsigned t0 = pcm + 3 * ns * ch -> bv_unsigned s6 = pcm + 3 * ns * ch -> bv_unsigned a3 = ch ->
  (forall (a0 a1 a2 s9 s10 t3 t4 t5 t6 : word) (Fh : bvmap 5 word) (fc : bv 32) m,
     unbox_s (reg_get Fh (Z_to_bv 5 15)) = Z_to_bv 32 F2M23 -> frm0 fc -> INV m ((ch + 1) * ns) (ch + 1) ->
     ExecF.evtF rsegs RNG G (CSTF (CRT_AT 0x1d8) t0 t1 t2 a0 a1 a2 a3 s6 s9 s10 t3 t4 t5 t6 Fh fc m)) ->
  forall n s (a0 a1 a2 s9 s10 t3 t4 t5 t6 : word) (Fh : bvmap 5 word) (fc : bv 32) m,
  0 <= s -> s + Z.of_nat (S n) = ns ->
  bv_unsigned a0 = P + 4 * (ch * ns + s) -> bv_unsigned t4 = P + 4 * (ch * ns + s) -> bv_unsigned t3 = 3 * s ->
  unbox_s (reg_get Fh (Z_to_bv 5 15)) = Z_to_bv 32 F2M23 -> frm0 fc -> INV m (ch * ns + s) (ch + 1) ->
  ExecF.evtF rsegs RNG G (CSTF (CRT_AT 0x10c) t0 t1 t2 a0 a1 a2 a3 s6 s9 s10 t3 t4 t5 t6 Fh fc m).
Proof.
  intros ch t0 t1 t2 a3 s6 Hch Ht0 Hs6 Ha3 K n.
  pose proof NN as NNf.
  assert (SB : 0 <= ch * ns) by (apply Z.mul_nonneg_nonneg; lia).
  assert (SB2 : (ch + 1) * ns = ch * ns + ns) by ring.
  induction n as [|n IH];
    intros s a0 a1 a2 s9 s10 t3 t4 t5 t6 Fh fc m Hs0 Hsn Ha0 Ht4 Ht3 H15 Hfc Hinv.
  - apply (crt_body_F ch s t0 t1 t2 a3 s6 a0 a1 a2 s9 s10 t3 t4 t5 t6 Fh fc m);
      try assumption; [lia |].
    intros a0' a1' a2' s9' s10' t3' t4' t5' t6' v fc' m' Ha0' Ht3' Ht4' Hfc' Hinv'.
    step. takeF false. step.
    apply K; [rewrite freg_get_other by reflexivity; exact H15 | exact Hfc' | replace ((ch + 1) * ns) with (ch * ns + s + 1) by lia; exact Hinv'].
  - apply (crt_body_F ch s t0 t1 t2 a3 s6 a0 a1 a2 s9 s10 t3 t4 t5 t6 Fh fc m);
      try assumption; [lia |].
    intros a0' a1' a2' s9' s10' t3' t4' t5' t6' v fc' m' Ha0' Ht3' Ht4' Hfc' Hinv'.
    step. takeF true.
    apply (IH (s + 1) a0' a1' a2' s9' s10' t3' t4' t5' t6' (bvmap_set (Z_to_bv 5 14) v Fh) fc' m');
      [lia | lia | rewrite Ha0'; lia | rewrite Ht4'; lia | rewrite Ht3'; lia | rewrite freg_get_other by reflexivity; exact H15
      | exact Hfc' | replace (ch * ns + (s + 1)) with (ch * ns + s + 1) by lia; exact Hinv'].
Qed.

Lemma crt_outer_F : forall n ch (t0 t1 t2 a3 s6 a0 a1 a2 s9 s10 t3 t4 t5 t6 : word) (Fh : bvmap 5 word) (fc : bv 32) m,
  0 <= ch -> ch + Z.of_nat (S n) = nch ->
  bv_unsigned t0 = pcm + 3 * ns * ch -> bv_unsigned s6 = pcm + 3 * ns * ch -> bv_unsigned a3 = ch ->
  bv_unsigned t1 = P + 4 * ns * ch -> bv_unsigned t2 = P + 4 * ns * ch ->
  unbox_s (reg_get Fh (Z_to_bv 5 15)) = Z_to_bv 32 F2M23 -> frm0 fc -> INV m (ch * ns) ch ->
  (forall (a0' a1' a2' a3' s6' t0' t1' t2' s9' s10' t3' t4' t5' t6' : word) (Fh' : bvmap 5 word) (fc' : bv 32) m',
     bv_unsigned a3' = nch -> frm0 fc' -> INV m' (nch * ns) nch ->
     ExecF.evtF rsegs RNG G (CSTF (CRT_AT 0x1f0) t0' t1' t2' a0' a1' a2' a3' s6' s9' s10' t3' t4' t5' t6' Fh' fc' m')) ->
  ExecF.evtF rsegs RNG G (CSTF (CRT_AT 0xd4) t0 t1 t2 a0 a1 a2 a3 s6 s9 s10 t3 t4 t5 t6 Fh fc m).
Proof using All.
  intros n. induction n as [|n IH];
    intros ch t0 t1 t2 a3 s6 a0 a1 a2 s9 s10 t3 t4 t5 t6 Fh fc m
      Hc0 Hcn Ht0 Hs6 Ha3 Ht1 Ht2 H15 Hfc Hinv K;
    pose proof NN as NNf;
    assert (Hch : 0 <= ch < nch) by lia;
    assert (B0 : 0 <= ch * ns) by (apply Z.mul_nonneg_nonneg; lia);
    assert (Bcns : ch * ns <= (nch - 1) * ns) by (apply Z.mul_le_mono_nonneg_r; lia);
    assert (Bcns' : (nch - 1) * ns = nch * ns - ns) by ring;
    assert (RQ8 : ExecF.rng RNG (Q + 8 * ch) 8) by (eapply ExecF.rng_sub; [exact RQ | lia | lia]);
    assert (RSQ8 : ExecF.rng RNG ((Q + 8 * ch) / 8 + ASAN_K) 1)
      by (apply (crt_sh1F RNG Q (8 * nch) (8 * ch) RSQ); lia);
    destruct (SHST8 m (ch * ns) ch ch Hinv Hch) as (kq0 & Mq & Sq);
    pose proof (INVSTQ m (ch * ns) ch Hinv Hch) as HSq;
    do 2 step;
    (eapply csh_q8_F with (A := Q + 8 * ch) (k := kq0);
       [ rewrite Ha3; repeat first [ rewrite Z.shiftl_mul_pow2 by lia | match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end ]; lia | lia | exact Mq | exact Sq | exact RSQ8 | ]);
    intros wq;
    do 3 step; step; step; takeF false; do 3 step;
    (eapply crt_inner_F with (ch := ch) (n := Z.to_nat (ns - 1)) (s := 0);
       [ exact Hch | exact Ht0 | exact Hs6 | exact Ha3
       | | lia | rewrite Nat2Z.inj_succ, Z2Nat.id by lia; lia
       | rewrite Ht2; f_equal; ring
       | rewrite Ht1; f_equal; ring | reflexivity | exact H15 | exact Hfc
       | replace (ch * ns + 0) with (ch * ns) by lia; eapply INVQ;
           [ exact Hinv | lia | lia
           | unfold wa; apply unsigned_lit; lia
           | rewrite Ha3; repeat first [ rewrite Z.shiftl_mul_pow2 by lia | match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end ]; lia ] ]);
    intros a0' a1' a2' s9' s10' t3' t4' t5' t6' Fh' fc' m' Hunbox' Hfc' Hinv';
    do 5 step; step.
  - takeF false.
    apply K; [ rewrite (unsigned_lit (bv_unsigned a3 + 1)) by lia; rewrite Ha3; lia | exact Hfc' | replace (ch + 1) with nch in Hinv' by lia; exact Hinv' ].
  - takeF true.
    apply (IH (ch + 1));
      [ lia
      | rewrite Nat2Z.inj_succ in Hcn |- *; lia
      | rewrite Ht0; rewrite unsigned_lit by nia; nia
      | rewrite Hs6; rewrite unsigned_lit by nia; nia
      | rewrite (unsigned_lit (bv_unsigned a3 + 1)) by lia; lia
      | rewrite Ht1; rewrite unsigned_lit by nia; nia
      | rewrite Ht2; rewrite unsigned_lit by nia; nia
      | exact Hunbox' | exact Hfc'
      | exact Hinv' | exact K ].
Qed.

End LoopsF.

(* The convert loop as crt_loop_stmt_F states it: crt_outer_F at ch = 0, with crt_inv_init as the starting invariant. *)
Theorem crt_loop_holds_F : crt_loop_stmt_F.
Proof.
  (* Not in the record: its CRT_A5 was the numeral, crtA_iface.v's is 2 ^ 64 - 2 ^ 24; compute it (and unfold
     ASAN_K) so that the statement's registers match crt_outer_F's numerals syntactically. *)
  unfold crt_loop_stmt_F, CRT_LOOP_IN, CRT_LOOP_OUT, ASAN_K.
  let v := eval vm_compute in CRT_A5 in change CRT_A5 with v.
  intros RNG ra sp gp tp s1 s4 s7 s11 a0 a1 a2 s9 s10 t3 t4 t5 t6 F fc m0 pb P Q pcm nch ns
    HN HNS HB HP0 HP1 HP2 HQ0 HQ1 HQ2 HC0 HC1 PB WP WQ ADP ADQ ADC DPQ DPC DQC H15 Hfc
    RP RQ RC RSP RSQ RSC.
  eapply (crt_outer_F ra sp gp tp s1 s4 s7 s11 m0 pb P Q pcm nch ns
            HN HNS HB HP0 HP1 HP2 HQ0 HQ1 HQ2 HC0 HC1 PB WP WQ ADP ADQ ADC DPQ DPC DQC
            _ RNG RP RQ RC RSP RSQ RSC
            (Z.to_nat (nch - 1)) 0
            (Z_to_bv 64 pcm) (Z_to_bv 64 P) (Z_to_bv 64 P) (Z_to_bv 64 0) (Z_to_bv 64 pcm)
            a0 a1 a2 s9 s10 t3 t4 t5 t6 F fc m0);
    [ lia
    | rewrite Nat2Z.inj_succ, Z2Nat.id by lia; lia
    | rewrite unsigned_lit by lia; lia
    | rewrite unsigned_lit by lia; lia
    | rewrite unsigned_lit by lia; lia
    | rewrite unsigned_lit by lia; lia
    | rewrite unsigned_lit by lia; lia
    | exact H15
    | exact Hfc
    | replace (0 * ns) with 0 by lia;
      apply (crt_inv_init m0 pb P Q pcm nch ns HN HNS HB HP0 HP1 HP2 HQ0 HQ1 HQ2 HC0 HC1 PB WP WQ ADP ADQ ADC
               DPQ DPC DQC)
    | ].
  intros a0' a1' a2' a3' s6' t0' t1' t2' s9' s10' t3' t4' t5' t6' Fh' fc' m' Ha3' Hfc' Hinv'.
  apply evtF_done.
  exists t0', t1', t2', a0', a1', a2', s6', s9', s10', t3', t4', t5', t6', Fh', fc', m'.
  split; [| split; [exact Hfc' | exact Hinv']].
  replace a3' with (Z_to_bv 64 nch) by (apply bv_eq; rewrite unsigned_lit by lia; rewrite Ha3'; reflexivity).
  reflexivity.
Qed.
