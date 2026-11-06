From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import AsanKA AsanKAProof reac_frame_inspect_c reac_decode_c reac_upstream_decode_c ReacDecodeLib.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import reac_upstream_decode_h reac_upstream_decode_if reac_upstream_decode_lib.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import reac_upstream_decode_F_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Footprint twin of reac_upstream_decode_holds (B image, entry 0x82038): reac_upstream_decode_holds_F proves
   reac_upstream_decode_contract_F (reac_upstream_decode_F_c.v), and reac_upstream_decode_holds_of_F gives the old
   contract back at the footprint RNG_all. The proofs follow reac_upstream_decode.v and the loop part
   reac_upstream_decode_lib.v step for step, with StepF's step; each data access goes to one of the rng premises.
   The pure lemmas of reac_upstream_decode_h.v and reac_upstream_decode_lib.v are used as they are. *)

(* ---- The tactics of the old proof, over ExecF.evtF ---- *)

(* A store of a computed value: the bytes as le8 (le4, le2, le1) of a word, so that the frame cells take them. *)
Ltac fixlitF :=
  try lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      rewrite (le8_lit z) by lia; mem_after_store_opt
  | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      rewrite (le4_lit z) by lia; mem_after_store_opt
  | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
      rewrite (le2_lit z) by lia; mem_after_store_opt
  | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
      rewrite (le1_zlit z) by lia; mem_after_store_opt
  end.

Ltac stp := stepF_k ltac:(fixlitF).
Ltac st := stp; nrm.

Ltac cnd b :=
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b; [cbv iota | symmetry; unfold bv_eqb, bv_ltu, bv_lts; usub; fold_lit_ux; solve_cond_rec]
  end.

Ltac pshadowF m0 addrreg EA M k SK MB :=
  let g := fresh "g" in let h := fresh "h" in let G := fresh "G" in let H := fresh "H" in
  let R := fresh "R" in let C := fresh "C" in
  stp; gen_shr addrreg g G; rewrite EA in G;
  stp; gen_addi g h H; rewrite G in H;
  pose proof (rdw0 m0 h _ _ M ltac:(lia)) as R; stp; clear R;
  stp;
  destruct SK as [C|C];
  [ rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]
  | rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb];
    stp; rewrite land7, EA; stp;
    rewrite (lts_low _ k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb] ].

(* ---- The instrumented checks of the loop body (reac_upstream_decode_lib.v, ul0 .. us2), with the accessed
   shadow byte (and source byte) in RNG ---- *)

Lemma ul0F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (P : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x13 + bv_unsigned x11 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  ExecF.rng RNG (A / 8 + ASAN_K) 1 ->
  (forall y10 y11 y20 : word, bv_unsigned y10 = A ->
     ExecF.evtF rsegs RNG P (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y10 y11 x12 x13 x14 (Z_to_bv 64 2147450880) x16 x17 x18 x19 y20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x82258) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG P (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 (Z_to_bv 64 2147450880) x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x82244) fc None mm (seg_rom rsegs)).
Proof.
  intros until A. intros EA RA M SK RK CONT.
  pose proof (u64_range x13) as R13. pose proof (u64_range x11) as R11. unfold ASAN_K in M, RK.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  stp. gen_add x13 x11 w U. rewrite EA in U.
  stp. gen_shr w g G. rewrite U in G.
  stp. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. stp. clear R.
  stp.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT. exact U.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    stp. stp. rewrite land7, U, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    stp. apply CONT. exact U.
Qed.

Lemma us0F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (P : machine_state -> Prop) (k b : byte) (Qa A3 : Z),
  bv_unsigned x12 = Qa -> Qa < 2^64 -> bv_unsigned x10 = A3 ->
  mrd rsegs mm (wa (Qa / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ Qa mod 8 < bv_signed k) ->
  mrd rsegs mm (wa A3) = Some b ->
  ExecF.rng RNG (Qa / 8 + ASAN_K) 1 -> ExecF.rng RNG A3 1 ->
  (forall y11 y20 : word,
     ExecF.evtF rsegs RNG P (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (zxb b) y11 x12 x13 x14 (Z_to_bv 64 2147450880) x16 x17 x18 x19 y20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x8226c) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG P (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 (Z_to_bv 64 2147450880) x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x82258) fc None mm (seg_rom rsegs)).
Proof.
  intros until A3. intros EQ RQ EA3 M SK Fsrc RK RB CONT.
  pose proof (u64_range x12) as R12. unfold ASAN_K in M, RK.
  pose proof (Z.mod_pos_bound Qa 8 ltac:(lia)) as MB.
  stp. gen_shr x12 g G. rewrite EQ in G.
  stp. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. stp. clear R.
  pose proof (rdw0 mm x10 _ _ Fsrc EA3) as R. stp. clear R.
  stp.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    stp. stp. rewrite land7, EQ, (lts_low (Qa mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    stp. apply CONT.
Qed.

Lemma ul1F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (P : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x13 + bv_unsigned x10 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  ExecF.rng RNG (A / 8 + ASAN_K) 1 ->
  (forall y10 y11 y21 : word, bv_unsigned y10 = A ->
     ExecF.evtF rsegs RNG P (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y10 y11 x12 x13 x14 (Z_to_bv 64 2147450880) x16 x17 x18 x19 x20 y21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x82294) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG P (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 (Z_to_bv 64 2147450880) x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x82280) fc None mm (seg_rom rsegs)).
Proof.
  intros until A. intros EA RA M SK RK CONT.
  pose proof (u64_range x13) as R13. pose proof (u64_range x10) as R10. unfold ASAN_K in M, RK.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  stp. gen_add x13 x10 w U. rewrite EA in U.
  stp. gen_shr w g G. rewrite U in G.
  stp. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. stp. clear R.
  stp.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT. exact U.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    stp. stp. rewrite land7, U, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    stp. apply CONT. exact U.
Qed.

Lemma us1F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (P : machine_state -> Prop) (k b : byte) (Qa A3 : Z),
  bv_unsigned x12 + 1 = Qa -> Qa < 2^64 -> bv_unsigned x10 = A3 ->
  mrd rsegs mm (wa (Qa / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ Qa mod 8 < bv_signed k) ->
  mrd rsegs mm (wa A3) = Some b ->
  ExecF.rng RNG (Qa / 8 + ASAN_K) 1 -> ExecF.rng RNG A3 1 ->
  (forall y11 y21 y22 : word,
     ExecF.evtF rsegs RNG P (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (zxb b) y11 x12 x13 x14 (Z_to_bv 64 2147450880) x16 x17 x18 x19 x20 y21 y22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x822ac) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG P (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 (Z_to_bv 64 2147450880) x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x82294) fc None mm (seg_rom rsegs)).
Proof.
  intros until A3. intros EQ RQ EA3 M SK Fsrc RK RB CONT.
  pose proof (u64_range x12) as R12. unfold ASAN_K in M, RK.
  pose proof (Z.mod_pos_bound Qa 8 ltac:(lia)) as MB.
  stp. gen_addi x12 w U. rewrite EQ in U.
  stp. gen_shr w g G. rewrite U in G.
  stp. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. stp. clear R.
  pose proof (rdw0 mm x10 _ _ Fsrc EA3) as R. stp. clear R.
  stp.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    stp. stp. rewrite land7, U, (lts_low (Qa mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    stp. apply CONT.
Qed.

Lemma ul2F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (P : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x13 + bv_unsigned x10 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  ExecF.rng RNG (A / 8 + ASAN_K) 1 ->
  (forall y10 y11 y21 : word, bv_unsigned y10 = A ->
     ExecF.evtF rsegs RNG P (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y10 y11 x12 x13 x14 (Z_to_bv 64 2147450880) x16 x17 x18 x19 x20 y21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x822d4) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG P (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 (Z_to_bv 64 2147450880) x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x822c0) fc None mm (seg_rom rsegs)).
Proof.
  intros until A. intros EA RA M SK RK CONT.
  pose proof (u64_range x13) as R13. pose proof (u64_range x10) as R10. unfold ASAN_K in M, RK.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  stp. gen_add x13 x10 w U. rewrite EA in U.
  stp. gen_shr w g G. rewrite U in G.
  stp. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. stp. clear R.
  stp.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT. exact U.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    stp. stp. rewrite land7, U, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    stp. apply CONT. exact U.
Qed.

Lemma us2F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (P : machine_state -> Prop) (k b : byte) (Qa A3 : Z),
  bv_unsigned x12 + 2 = Qa -> Qa < 2^64 -> bv_unsigned x10 = A3 ->
  mrd rsegs mm (wa (Qa / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ Qa mod 8 < bv_signed k) ->
  mrd rsegs mm (wa A3) = Some b ->
  ExecF.rng RNG (Qa / 8 + ASAN_K) 1 -> ExecF.rng RNG A3 1 ->
  (forall y11 y21 y22 : word,
     ExecF.evtF rsegs RNG P (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (zxb b) y11 x12 x13 x14 (Z_to_bv 64 2147450880) x16 x17 x18 x19 x20 y21 y22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x822ec) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG P (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 (Z_to_bv 64 2147450880) x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x822d4) fc None mm (seg_rom rsegs)).
Proof.
  intros until A3. intros EQ RQ EA3 M SK Fsrc RK RB CONT.
  pose proof (u64_range x12) as R12. unfold ASAN_K in M, RK.
  pose proof (Z.mod_pos_bound Qa 8 ltac:(lia)) as MB.
  stp. gen_addi x12 w U. rewrite EQ in U.
  stp. gen_shr w g G. rewrite U in G.
  stp. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. stp. clear R.
  pose proof (rdw0 mm x10 _ _ Fsrc EA3) as R. stp. clear R.
  stp.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    stp. stp. rewrite land7, U, (lts_low (Qa mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    stp. apply CONT.
Qed.

(* ---- The loop and the return path (reac_upstream_decode_lib.v, section UPL), over ExecF.evtF ---- *)

(* The three separation facts of the loop (DOR, DOS, DRS of reac_upstream_decode_lib.v). lia does not look into
   this definition, so the steps do not pay for its three disjunctions; only the stores unfold it, for that step. *)
Definition SEPU (sp : word) (raw out len nch : Z) : Prop :=
  (out + 36 * nch <= raw \/ raw + len <= out) /\
  (out + 36 * nch <= bv_unsigned sp - 96 \/ bv_unsigned sp <= out) /\
  (raw + len <= bv_unsigned sp - 96 \/ bv_unsigned sp <= raw).

Section UPLF.
Variables (RNG : ExecF.footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (raw out len lo : Z).

Local Notation SP := (bv_unsigned sp).
Local Notation POST := (PostU ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m bs raw out len lo).
Local Notation STATE pc mm x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 :=
  (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
        x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
      F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

Hypothesis Hsp : lo + 96 <= SP.
Hypothesis Hlo : 0 <= lo.
Hypothesis RS : ExecF.rng RNG (SP - 96) 96.

(* 82098: ld ra ; ld s0..s6 ; addi sp,sp,96 ; ret *)
Lemma up_exit_genF : forall (m1 : word -> option byte) (r : Z)
    (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 : word),
  FRU ra sp s0 s1 s2 s3 s4 s5 s6 m1 -> stk rsegs m1 lo (SP + -96) -> wmono rsegs m m1 ->
  r = (if up_ok raw out len bs then 12 else -1) ->
  (if up_ok raw out len bs
   then munch [(SP + -96, SP); (out, out + 36 * up_nch len)] m m1 /\
        bytes_at rsegs m1 out (braid_out bs (up_nch len) 12)
   else munch [(SP + -96, SP)] m m1) ->
  ExecF.evtF rsegs RNG POST (MS (mkR x1 (Z_to_bv 64 (SP + -96)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
      x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x82098) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 r x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 (junk & HF) ST WM Er HM.
  pose proof (u64_range sp) as Rsp.
  do 10 stp.
  apply evtF_done. unfold PostU. exists x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, m1.
  split; [subst r; reflexivity|]. split; [exact WM|]. split.
  - pose proof (stk_release rsegs m1 lo (SP + -96) _ ST HF ltac:(lia)) as ST2.
    cbn [cells_size csize Nat.add] in ST2. replace (SP + -96 + Z.of_nat 96) with SP in ST2 by lia. exact ST2.
  - replace (SP - 96) with (SP + -96) by lia. exact HM.
Qed.

Variable nch : Z.
Hypothesis Hnchdef : up_nch len = nch.
Hypothesis Hnch : 2 <= nch <= 40.
Hypothesis Hev : nch mod 2 = 0.
Hypothesis Hlen52 : len = 52 + 36 * nch.
Hypothesis Hlen : length bs = Z.to_nat len.
Hypothesis Hraw : 0 < raw.
Hypothesis Hraw2 : raw + len <= 2^64.
Hypothesis Hout : 0 < out.
Hypothesis HoutN : out + 36 * nch < 2^64.
Hypothesis HSEP : SEPU sp raw out len nch.
Hypothesis AR : addressable m raw len.
Hypothesis AO : addressable m out (36 * nch).
Hypothesis APW : forall x, SP - 96 <= x < SP -> app_mem x.
Hypothesis OK : up_ok raw out len bs = true.
Hypothesis RR : ExecF.rng RNG raw len.
Hypothesis RRS : ExecF.rng RNG (raw / 8 + ASAN_K) ((raw + len - 1) / 8 - raw / 8 + 1).
Hypothesis RO : ExecF.rng RNG out (36 * nch).
Hypothesis ROS : ExecF.rng RNG (out / 8 + ASAN_K) ((out + 36 * nch - 1) / 8 - out / 8 + 1).

Local Notation N := (36 * nch).
Local Notation INV := (INVU ra sp s0 s1 s2 s3 s4 s5 s6 m bs raw out lo nch).

(* One source byte, its shadow byte, and the shadow byte of one output byte lie in RNG. *)
Lemma rsrc_b : forall a, 0 <= a < len -> ExecF.rng RNG (raw + a) 1.
Proof. intros a Ha. eapply rng_sub; [exact RR | lia | lia]. Qed.

Lemma rsrc_sh : forall a, 0 <= a < len -> ExecF.rng RNG ((raw + a) / 8 + ASAN_K) 1.
Proof. intros a Ha. eapply rng_sub; [exact RRS | lia | lia]. Qed.

Lemma rdst_sh : forall q, 0 <= q < N -> ExecF.rng RNG ((out + q) / 8 + ASAN_K) 1.
Proof. intros q Hq. eapply rng_sub; [exact ROS | lia | lia]. Qed.

(* A store into the frame, with the separation facts present for that step only. *)
Ltac stf :=
  let D1 := fresh "D" in let D2 := fresh "D" in let D3 := fresh "D" in
  pose proof HSEP as (D1 & D2 & D3); st; clear D1 D2 D3.

(* A store of an output byte (reac_upstream_decode_lib.v, ostore); BWX and BPL are bw_ext and bpre_len at the
   section's facts. *)
Ltac ostoreF BWX BPL :=
  rewrite ?le1_zxb;
  lazymatch goal with
  | |- ExecF.evtF ?sg _ ?Q (MS ?R ?Fr ?pc ?f ?rv (write_to_mem ?mk ?w [braid_byte bs nch 12 ?q]) ?ro) =>
      replace w with (wa (out + q)) by (unfold wa; apply f_equal; lia);
      match goal with BW : bytes_at _ mk out (bpre bs nch ?q0) |- _ =>
        apply (BWX mk q0 q) in BW; [ | lia | lia | lia ]
      end;
      match goal with H : Z.of_nat (length (bpre bs nch _)) = _ |- _ => clear H end;
      assert (LB : Z.of_nat (length (bpre bs nch (q + 1))) = q + 1) by (apply BPL; lia);
      let D1 := fresh "D" in let D2 := fresh "D" in let D3 := fresh "D" in
      pose proof HSEP as (D1 & D2 & D3);
      transport_chunks sg mk (out + q) [braid_byte bs nch 12 q];
      footprint_after_store sg mk (out + q) [braid_byte bs nch 12 q];
      clear D1 D2 D3;
      let m2 := fresh "m" in set (m2 := write_to_mem mk (wa (out + q)) [braid_byte bs nch 12 q]) in *; clearbody m2
  end.

(* reac_upstream_decode_lib.v, rebundle. *)
Ltac rebundleF :=
  lazymatch goal with H : rw_cells _ ?mm ?A (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?post) |- _ =>
    apply (rw_cells_merge rsegs mm A [] [c1; c2; c3; c4] post) in H; cbn [app cells_size csize Nat.add] in H;
    split; [assumption|]; split; [eexists; exact H|]; split; [assumption|]; split; [assumption|];
    split; [assumption|]; split; [assumption|]; eassumption
  end.

Lemma up_innerF : forall (ch : Z) (x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word),
  0 <= ch < nch ->
  bv_unsigned x5 = SP + -88 -> bv_unsigned x6 = 18446744073709551599 -> bv_unsigned x7 = 18446744073709551615 ->
  bv_unsigned x9 = ch - ch mod 2 -> bv_unsigned x13 = raw + 50 -> bv_unsigned x14 = ch ->
  bv_unsigned x15 = 2147450880 -> bv_unsigned x16 = nch -> bv_unsigned x17 = 18446744073709551608 ->
  bv_unsigned x18 = ch mod 2 -> bv_unsigned x28 = 12 -> bv_unsigned x29 = 18446744073709551615 - (raw + 50) ->
  bv_unsigned x30 = 2147483646 -> bv_unsigned x31 = 18446744073709551607 ->
  (forall (m2 : word -> option byte) (y8 y10 y11 y12 y19 y20 y21 y22 : word),
     bv_unsigned y19 = out + 3 * (ch * 12 + 11) -> INV m2 (3 * (ch * 12 + 12)) ->
     ExecF.evtF rsegs RNG POST (STATE 0x8234c m2 x5 x6 x7 y8 x9 y10 y11 y12 x13 x14 x15 x16 x17 x18 y19 y20 y21 y22 x28 x29 x30 x31)) ->
  forall (K : nat) (s : Z) (m1 : word -> option byte) (x8 x10 x11 x12 x19 x20 x21 x22 : word),
  Z.to_nat (12 - s) = K -> 0 <= s < 12 ->
  bv_unsigned x8 = s -> bv_unsigned x12 = out + 3 * (ch * 12 + s) -> bv_unsigned x20 = out + 3 * (ch * 12 + s) ->
  INV m1 (3 * (ch * 12 + s)) ->
  ExecF.evtF rsegs RNG POST (STATE 0x821cc m1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31).
Proof.
  intros ch x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31
    Hch H5 H6 H7 H9 H13 H14 H15 H16 H17 H18 H28 H29 H30 H31 CONT K.
  pose proof HSEP as (DOR & DOS & DRS).
  pose proof (SRC_shr sp m bs raw out len lo Hsp Hlo nch Hnch Hev Hlen52 Hlen Hraw Hraw2 Hout HoutN DOR DOS DRS AR AO APW)
    as SRCSH.
  pose proof (SRC_rd sp bs raw out len lo Hsp Hlo nch Hnch Hev Hlen52 Hlen Hraw Hraw2 Hout HoutN DOR DOS DRS) as SRCRD.
  pose proof (src_bound sp bs raw out len lo Hsp Hlo nch Hnch Hev Hlen52 Hlen Hraw Hraw2 Hout HoutN DOR DOS DRS) as SRCB.
  pose proof (DST_sho sp m bs out len nch Hlen AO APW) as DSTSH.
  pose proof (bw_ext sp bs raw out len lo Hsp Hlo nch Hnch Hlen52 Hlen Hraw Hout DOR DOS DRS) as BWX.
  pose proof (bpre_len sp bs raw out len nch Hnch Hlen52 Hlen DOR DOS DRS) as BPL.
  pose proof (INVU_idx ra sp s0 s1 s2 s3 s4 s5 s6 m bs raw out len lo nch Hnchdef Hnch Hev Hlen52 HoutN DOR DOS AO)
    as INVI.
  clear DOR DOS DRS.
  pose proof (u64_range sp) as Rsp.
  apply wv in H5, H6, H7, H9, H13, H14, H15, H16, H17, H18, H28, H29, H30, H31.
  subst x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31.
  pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hm.
  assert (Hc2 : ch - ch mod 2 <= nch - 2) by (Z.div_mod_to_equations; lia).
  assert (Hc0 : 0 <= ch - ch mod 2) by (Z.div_mod_to_equations; lia).
  assert (Hc12 : 0 <= ch * 12 <= (nch - 1) * 12) by lia.
  assert (HLZ : Z.of_nat (length bs) = len) by (rewrite Hlen; lia).
  induction K as [K IH] using lt_wf_ind.
  intros s m1 x8 x10 x11 x12 x19 x20 x21 x22 HK Hs H8 H12 H20 I0.
  apply wv in H8, H12, H20. subst x8 x12 x20.
  (* s * nch is the one product; nia over this context is slow, so two monotonicity lemmas give its bounds. *)
  assert (Hsn : 0 <= s * nch <= 11 * nch)
    by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_r; lia]).
  assert (Hq : 0 <= 3 * (ch * 12 + s) /\ 3 * (ch * 12 + s) + 2 < N) by lia.
  destruct I0 as (BR & (junk & FR) & ST & WA & MU & WM & BW).
  assert (LB : Z.of_nat (length (bpre bs nch (3 * (ch * 12 + s)))) = 3 * (ch * 12 + s)) by (apply BPL; lia).
  (* 821cc mul a0,s0,a6 ; mulw a1,s0,a6 ; bne a1,a0 : trap *)
  st. st. st. cnd false.
  (* 821d8 sext.w a1,a0 ; add a0,a1,s1 ; addw a1,a1,s1 ; bne a1,a0 : trap *)
  st. st. st. st. cnd false.
  (* 821e8 mv s3,s4 ; sext.w a0,a0 ; slli a1,a0,1 ; add a0,a1,a0 ; bnez s2 *)
  st. st. st. st. st.
  destruct (Z.eqb_spec (ch mod 2) 0) as [EP|EP].
  (* even: 821fc addi a1,a0,3 ; sd a1,8(sp) ; bgeu t0,a7 : trap ; sd a0,16(sp) ; bltu t1,t0 : trap ;
     addi a0,a0,1 ; j 82234 *)
  1: (cnd false; st; stf; st; cnd false; stf; st; cnd false; st; st).
  (* odd: 82218 addi a1,a0,4 ; sd a1,8(sp) ; bltu t6,t0 : trap ; addi a1,a0,5 ; sd a1,16(sp) ; bltu t1,t0 : trap ;
     addi a0,a0,2 *)
  2: (cnd true; st; stf; st; cnd false; st; stf; st; cnd false; st).
  (* 82234 ld a1,8(sp) ; sd a0,24(sp) ; bltu t4,a1 : trap ; beq s3,t2 : trap *)
  all: st. all: stf. all: st. all: cnd false. all: st. all: cnd false.
  (* 82244 byte 0: load check of raw+50+off0 *)
  all: destruct (SRCSH _ ch s 0 (3 + ch mod 2) MU Hch Hs ltac:(lia) eq_refl) as (k0 & MK & SK).
  all: pose proof (SRCB ch s 0 (3 + ch mod 2) Hch Hs ltac:(lia) eq_refl) as SB.
  all: pose proof (rsrc_sh _ SB) as RK. all: pose proof (rsrc_b _ SB) as RB. all: clear SB.
  all: eapply ul0F; [ | | exact MK | exact SK | exact RK | intros p10 p11 p20 Ep10 ]; [ ufin | lia | ].
  all: clear MK SK RK.
  (* 82258 store check of out+j ; lbu *)
  all: destruct (DSTSH _ (3 * (ch * 12 + s) + 0) MU ltac:(lia)) as (ks & MS & SKs).
  all: pose proof (rdst_sh (3 * (ch * 12 + s) + 0) ltac:(lia)) as RQ.
  all: pose proof (SRCRD _ ch s 0 (3 + ch mod 2) BR Hch Hs ltac:(lia) eq_refl) as RD.
  all: eapply us0F; [ | | exact Ep10 | exact MS | exact SKs | exact RD | exact RQ | exact RB | intros q11 q20 ];
         [ ufin | lia | ].
  all: clear MS SKs RD Ep10 RQ RB.
  (* 8226c sb a0,0(s3) *)
  all: pose proof (wr_at_store_ok rsegs _ out N (3 * (ch * 12 + s) + 0) 1 WA ltac:(lia) ltac:(lia)) as HS.
  all: pose proof (rng_sub' _ _ _ (out + (3 * (ch * 12 + s) + 0)) 1 RO ltac:(lia)) as RW.
  all: st. all: clear HS RW. all: ostoreF BWX BPL.
  (* 82270 ld a0,16(sp) ; bltu t4,a0 : trap ; addi s4,s3,1 ; beq s4,t2 : trap *)
  all: st. all: st. all: cnd false. all: st. all: st. all: cnd false.
  (* 82280 byte 1 *)
  all: destruct (SRCSH _ ch s 1 (5 * (ch mod 2)) MU Hch Hs ltac:(lia) eq_refl) as (k1 & MK & SK).
  all: pose proof (SRCB ch s 1 (5 * (ch mod 2)) Hch Hs ltac:(lia) eq_refl) as SB.
  all: pose proof (rsrc_sh _ SB) as RK. all: pose proof (rsrc_b _ SB) as RB. all: clear SB.
  all: eapply ul1F; [ | | exact MK | exact SK | exact RK | intros r10 r11 r21 Er10 ]; [ ufin | lia | ].
  all: clear MK SK RK.
  all: destruct (DSTSH _ (3 * (ch * 12 + s) + 1) MU ltac:(lia)) as (ks1 & MS & SKs).
  all: pose proof (rdst_sh (3 * (ch * 12 + s) + 1) ltac:(lia)) as RQ.
  all: pose proof (SRCRD _ ch s 1 (5 * (ch mod 2)) BR Hch Hs ltac:(lia) eq_refl) as RD.
  all: eapply us1F; [ | | exact Er10 | exact MS | exact SKs | exact RD | exact RQ | exact RB | intros u11 u21 u22 ];
         [ ufin | lia | ].
  all: clear MS SKs RD Er10 RQ RB.
  (* 822ac sb a0,0(s4) *)
  all: pose proof (wr_at_store_ok rsegs _ out N (3 * (ch * 12 + s) + 1) 1 WA ltac:(lia) ltac:(lia)) as HS.
  all: pose proof (rng_sub' _ _ _ (out + (3 * (ch * 12 + s) + 1)) 1 RO ltac:(lia)) as RW.
  all: st. all: clear HS RW. all: ostoreF BWX BPL.
  (* 822b0 ld a0,24(sp) ; bltu t4,a0 : trap ; addi s4,s4,1 ; beq s4,t2 : trap *)
  all: st. all: st. all: cnd false. all: st. all: st. all: cnd false.
  (* 822c0 byte 2 *)
  all: destruct (SRCSH _ ch s 2 (1 + ch mod 2) MU Hch Hs ltac:(lia) eq_refl) as (k2 & MK & SK).
  all: pose proof (SRCB ch s 2 (1 + ch mod 2) Hch Hs ltac:(lia) eq_refl) as SB.
  all: pose proof (rsrc_sh _ SB) as RK. all: pose proof (rsrc_b _ SB) as RB. all: clear SB.
  all: eapply ul2F; [ | | exact MK | exact SK | exact RK | intros v10 v11 v21 Ev10 ]; [ ufin | lia | ].
  all: clear MK SK RK.
  all: destruct (DSTSH _ (3 * (ch * 12 + s) + 2) MU ltac:(lia)) as (ks2 & MS & SKs).
  all: pose proof (rdst_sh (3 * (ch * 12 + s) + 2) ltac:(lia)) as RQ.
  all: pose proof (SRCRD _ ch s 2 (1 + ch mod 2) BR Hch Hs ltac:(lia) eq_refl) as RD.
  all: eapply us2F; [ | | exact Ev10 | exact MS | exact SKs | exact RD | exact RQ | exact RB | intros w11 w21 w22 ];
         [ ufin | lia | ].
  all: clear MS SKs RD Ev10 RQ RB.
  (* 822ec sb a0,0(s4) *)
  all: pose proof (wr_at_store_ok rsegs _ out N (3 * (ch * 12 + s) + 2) 1 WA ltac:(lia) ltac:(lia)) as HS.
  all: pose proof (rng_sub' _ _ _ (out + (3 * (ch * 12 + s) + 2)) 1 RO ltac:(lia)) as RW.
  all: st. all: clear HS RW. all: ostoreF BWX BPL.
  (* 822f0 addiw s0,s0,1 ; addi a2,a2,3 ; addi s4,s4,1 ; bne s0,t3 *)
  all: st. all: st. all: st. all: st.
  all: brq BRq.
  all: lazymatch goal with
       | _ : ?sv + 1 = 12 |- _ =>
           (* 82300 j 8234c *)
           st; eapply CONT; [ ufin | eapply INVI; [rebundleF | lia] ]
       | _ : ?sv + 1 <> 12 |- _ =>
           eapply (IH (Z.to_nat (12 - (sv + 1))) ltac:(lia) (sv + 1));
           lazymatch goal with
           | |- INVU _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => eapply INVI; [rebundleF | lia]
           | _ => first [ reflexivity | lia | ufin ]
           end
       end.
Qed.

Lemma up_outer_genF : forall (K : nat) (ch : Z) (m1 : word -> option byte)
    (x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 : word),
  Z.to_nat (nch - ch) = K -> 0 <= ch < nch ->
  bv_unsigned x5 = SP + -88 -> bv_unsigned x6 = 18446744073709551599 -> bv_unsigned x7 = 18446744073709551615 ->
  bv_unsigned x12 = out + 3 * (ch * 12) -> bv_unsigned x13 = raw + 50 -> bv_unsigned x14 = ch ->
  bv_unsigned x15 = 2147450880 -> bv_unsigned x16 = nch -> bv_unsigned x17 = 18446744073709551608 ->
  bv_unsigned x28 = 12 -> bv_unsigned x29 = 18446744073709551615 - (raw + 50) -> bv_unsigned x30 = 2147483646 ->
  bv_unsigned x31 = 18446744073709551607 ->
  INV m1 (3 * (ch * 12)) ->
  ExecF.evtF rsegs RNG POST (STATE 0x821bc m1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31).
Proof.
  pose proof HSEP as (DOR & DOS & DRS).
  pose proof (INVU_idx ra sp s0 s1 s2 s3 s4 s5 s6 m bs raw out len lo nch Hnchdef Hnch Hev Hlen52 HoutN DOR DOS AO)
    as INVI.
  clear DOR DOS DRS.
  induction K as [K IH] using lt_wf_ind.
  intros ch m1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31
    HK Hch H5 H6 H7 H12 H13 H14 H15 H16 H17 H28 H29 H30 H31 I0.
  pose proof (u64_range sp) as Rsp.
  pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hm.
  assert (Hc0 : 0 <= ch - ch mod 2) by (Z.div_mod_to_equations; lia).
  apply wv in H5, H6, H7, H12, H13, H14, H15, H16, H17, H28, H29, H30, H31.
  subst x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31.
  (* 821bc li s0,0 ; and s1,a4,t5 ; andi s2,a4,1 ; mv s4,a2 *)
  st. st. rewrite (land_2m2 ch) by lia. st. rewrite land1. st.
  eapply (up_innerF ch) with (K := Z.to_nat (12 - 0)) (s := 0).
  all: lazymatch goal with
       | |- forall _ : word -> option byte, _ => idtac
       | |- INVU _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => eapply INVI; [exact I0 | lia]
       | _ => first [ lia | reflexivity | ufin ]
       end.
  intros m2 y8 y10 y11 y12 y19 y20 y21 y22 H19 I2. apply wv in H19. subst y19.
  (* 8234c addiw a4,a4,1 ; addi a2,s3,3 ; bne a4,a6 *)
  st. st. st.
  brq BR.
  - (* ch + 1 = nch: 82358 li a0,12 ; j 82098 *)
    st. st.
    destruct I2 as (BB2 & FR2 & ST2 & WA2 & MU2 & WM2 & BW2).
    eapply up_exit_genF with (r := 12); [ exact FR2 | exact ST2 | exact WM2 | rewrite OK; reflexivity | ].
    rewrite OK, Hnchdef. split; [exact MU2 |].
    replace (braid_out bs nch 12) with (bpre bs nch (3 * (ch * 12 + 12)))
      by (unfold bpre, braid_out; do 3 f_equal; lia).
    exact BW2.
  - eapply (IH (Z.to_nat (nch - (ch + 1))) ltac:(lia) (ch + 1)).
    all: lazymatch goal with
         | |- INVU _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => eapply INVI; [exact I2 | lia]
         | _ => first [ reflexivity | lia | ufin ]
         end.
Qed.

End UPLF.

(* reac_upstream_decode_if.v, UP_OUTER, with the footprint: the stack window, the input and its shadow bytes, the
   output and its shadow bytes. *)
Lemma up_outer_holdsF :
  forall (RNG : ExecF.footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
         (fc : bv 32) (m : word -> option byte) (bs : list byte) (raw out len lo nch : Z),
    lo + 96 <= bv_unsigned sp -> 0 <= lo ->
    up_nch len = nch -> 2 <= nch <= 40 -> nch mod 2 = 0 -> len = 52 + 36 * nch ->
    length bs = Z.to_nat len -> 0 < raw -> raw + len <= 2^64 -> 0 < out -> out + 36 * nch < 2^64 ->
    (out + 36 * nch <= raw \/ raw + len <= out) ->
    (out + 36 * nch <= bv_unsigned sp - 96 \/ bv_unsigned sp <= out) ->
    (raw + len <= bv_unsigned sp - 96 \/ bv_unsigned sp <= raw) ->
    addressable m raw len -> addressable m out (36 * nch) ->
    (forall x, bv_unsigned sp - 96 <= x < bv_unsigned sp -> app_mem x) ->
    up_ok raw out len bs = true ->
    ExecF.rng RNG (bv_unsigned sp - 96) 96 ->
    ExecF.rng RNG raw len -> ExecF.rng RNG (raw / 8 + ASAN_K) ((raw + len - 1) / 8 - raw / 8 + 1) ->
    ExecF.rng RNG out (36 * nch) -> ExecF.rng RNG (out / 8 + ASAN_K) ((out + 36 * nch - 1) / 8 - out / 8 + 1) ->
    forall (m1 : word -> option byte)
           (x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 : word),
    bv_unsigned x5 = bv_unsigned sp + -88 -> bv_unsigned x6 = 18446744073709551599 ->
    bv_unsigned x7 = 18446744073709551615 -> bv_unsigned x12 = out -> bv_unsigned x13 = raw + 50 ->
    bv_unsigned x14 = 0 -> bv_unsigned x15 = 2147450880 -> bv_unsigned x16 = nch ->
    bv_unsigned x17 = 18446744073709551608 -> bv_unsigned x28 = 12 ->
    bv_unsigned x29 = 18446744073709551615 - (raw + 50) -> bv_unsigned x30 = 2147483646 ->
    bv_unsigned x31 = 18446744073709551607 ->
    INVU ra sp s0 s1 s2 s3 s4 s5 s6 m bs raw out lo nch m1 0 ->
    ExecF.evtF rsegs RNG (PostU ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m bs raw out len lo)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x821bc) fc None m1 (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m bs raw out len lo nch
    Hsp Hlo Hnchdef Hnch Hev Hlen52 Hlen Hraw Hraw2 Hout HoutN DOR DOS DRS AR AO APW OK RS RR RRS RO ROS
    m1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31
    H5 H6 H7 H12 H13 H14 H15 H16 H17 H28 H29 H30 H31 I0.
  assert (HSEP : SEPU sp raw out len nch) by (split; [exact DOR | split; [exact DOS | exact DRS]]).
  clear DOR DOS DRS.
  eapply up_outer_genF with (nch := nch) (K := Z.to_nat (nch - 0)) (ch := 0).
  all: first [ eassumption | reflexivity | lia | (rewrite H12; lia) ].
Qed.

(* reac_upstream_decode_if.v, UP_FAIL, with the stack window in the footprint. *)
Lemma up_fail_holdsF :
  forall (RNG : ExecF.footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
         (fc : bv 32) (m : word -> option byte) (bs : list byte) (raw out len lo : Z),
    lo + 96 <= bv_unsigned sp -> 0 <= lo -> ExecF.rng RNG (bv_unsigned sp - 96) 96 ->
    forall (m1 : word -> option byte)
           (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 : word),
    FRU ra sp s0 s1 s2 s3 s4 s5 s6 m1 -> stk rsegs m1 lo (bv_unsigned sp + -96) -> wmono rsegs m m1 ->
    munch [(bv_unsigned sp + -96, bv_unsigned sp)] m m1 ->
    up_ok raw out len bs = false ->
    ExecF.evtF rsegs RNG (PostU ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m bs raw out len lo)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (-1)) x11 x12 x13 x14 x15
               x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x82098) fc None m1 (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m bs raw out len lo Hsp Hlo RS
    m1 x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 HF ST WM MU E.
  eapply up_exit_genF with (r := -1).
  all: first [ eassumption | (rewrite E; reflexivity) | (rewrite E; exact MU) ].
Qed.

(* ---- The entry part and the early returns (reac_upstream_decode.v), over ExecF.evtF ---- *)

(* reac_upstream_decode.v, clr8: drop the facts of the instrumented checks (shadow addresses a / 8, offsets
   a mod 8). It keeps the facts that mention a footprint range. *)
Ltac clr8 :=
  repeat match goal with
  | H : context [Z.div _ 8] |- _ =>
      lazymatch type of H with context [ExecF.rng _ _ _] => fail | _ => clear H end
  | H : context [Z.modulo _ 8] |- _ =>
      lazymatch type of H with context [ExecF.rng _ _ _] => fail | _ => clear H end
  end.

Ltac ufail UF :=
  eapply UF; first
  [ (apply not_true_iff_false; rewrite up_ok_true;
     intros (HUa & HUb & HUc & HUd & HUe & HUf & HUg);
     try (apply up_nch_pos in HUc; destruct HUc as (HVa & HVb & HVc & HVd & HVe));
     unfold inspect_byte in *; clr8; first [ lia | (Z.div_mod_to_equations; lia) ])
  | (unfold FRU; eexists; eassumption)
  | eassumption ].

Ltac regeq Ea0 :=
  lazymatch goal with
  | |- bv_unsigned (Z_to_bv 64 (Zneg _)) = _ => rewrite unsigned_lit_wrap; vm_compute; reflexivity
  | |- bv_unsigned (Z_to_bv 64 (Zpos _)) = _ => rewrite unsigned_lit_wrap; vm_compute; reflexivity
  | |- bv_unsigned (Z_to_bv 64 Z0) = _ => rewrite unsigned_lit_wrap; vm_compute; reflexivity
  | |- _ => rewrite ?Ea0; usub; rewrite ?Z.add_0_r, ?swrap32_id by lia; usub;
            rewrite ?zb_lxor_ones by lia; usub; lia
  end.

Theorem reac_upstream_decode_holds_F : reac_upstream_decode_contract_F.
Proof.
  unfold reac_upstream_decode_contract_F, REAC_UPSTREAM_DECODE, REAC_UPSTREAM_DECODE_D, DIV36_MAGIC_AT, DIV36_MAGIC.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m bs raw out lo E0 E2 Rraw Rout Rlen HMG HB HO ST LO DR DO DM APS1 APS2 CELLS SGOT AR AO
    RS RM RG RC RR RRS RO ROS.
  unfold GOT_CELL_K in RG. unfold CELL_K in RC. unfold ASAN_K in RRS, ROS.
  assert (Ea0 : bv_unsigned a0 = raw) by (rewrite E0; apply unsigned_lit; lia).
  assert (Ea2 : bv_unsigned a2 = out) by (rewrite E2; apply unsigned_lit; lia).
  pose proof (u64_range a1) as Ra1.
  set (len := bv_unsigned a1) in *.
  assert (A1 : a1 = Z_to_bv 64 len) by (symmetry; apply Z_to_bv_bv_unsigned).
  clearbody len. subst a1.
  lazymatch goal with |- ExecF.evtF _ _ _ ?st =>
    change (ExecF.evtF rsegs RNG (PostU ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m bs raw out len lo) st) end.
  pose proof (u64_range sp) as Rsp.
  assert (Hlo : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (conj HMG CELLS) as PK. clear HMG CELLS.
  pose proof (up_fail_holdsF RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m bs raw out len lo LO Hlo RS) as UF.
  carve_frame 96%nat ST.
  (* 82038 addi sp,sp,-96 ; 8203c .. 82058 save ra s0 s1 s2 s3 s4 s5 s6 *)
  do 9 stp.
  destruct PK as (HMG & CELLS).
  match goal with MU' : munch _ m ?mm |- _ => rename MU' into MU1; rename mm into m0 end.
  pose proof (bytes_tp m m0 _ _ 66360 (le8 (Z_to_bv 64 16397105843297379215)) MU1
    ltac:(rewrite length_le8; unfold off_stk in DM; lia) HMG) as HMG0.
  assert (CELLS0 : asan_cells m0) by
    (eapply asan_cells_munch; [exact CELLS | exact MU1 |
     unfold MIDEND, GOT_CELL_K; unfold off_stk, GOT_CELL_K, MIDEND in SGOT; lia]).
  pose proof CELLS0 as (CK & GCK & _).
  unfold CELL_K, GOT_CELL_K, ASAN_K in CK, GCK.
  pose proof (rd_all _ _ _ HMG0) as HRM. rewrite length_le8 in HRM.
  pose proof (rd_all _ _ _ GCK) as RDG. rewrite length_le8 in RDG.
  pose proof (rd_all _ _ _ CK) as RDS. rewrite length_le8 in RDS.
  (* 8205c mv a3,a0 ; 82060 li a4,124 ; 82064 li a0,-1 *)
  do 3 stp.
  (* 82068 bltu a1,a4 ; 8206c beqz a3 ; 82070 beqz a2 : early returns *)
  stp. brq B1. { ufail UF. }
  stp. if_cases B2. { zify_cond B2; ufail UF. }
  stp. if_cases B3. { zify_cond B3; ufail UF. }
  (* 82074 .. 82090 : q = (len - 52) / 36 and the remainder *)
  do 4 stp.
  replace (len + -52) with (len - 52) in * by lia.
  rewrite (unsigned_lit (len - 52)) by lia.
  stp.
  rewrite (unsigned_lit (Z.shiftr _ 64)) by (rewrite Z.shiftr_div_pow2 by lia; split;
    [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; nia]).
  rewrite div36 by lia.
  assert (QB : 2 <= (len - 52) / 36 < 2^27) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
  set (q := (len - 52) / 36) in *.
  stp. stp. stp.
  rewrite ?(unsigned_lit q) by lia. rewrite ?(unsigned_lit (q * 36)) by lia.
  rewrite ?(unsigned_lit (len - 52)) by lia.
  rewrite ?(unsigned_lit (len - 52 - q * 36)) by (subst q; Z.div_mod_to_equations; lia).
  (* 82094 beqz a5 : remainder test *)
  stp. brq B4. 2:{ ufail UF. }
  assert (M36 : (len - 52) mod 36 = 0) by (subst q; Z.div_mod_to_equations; lia).
  (* 820c0 addiw a4,a6,-41 ; 820c4 li a5,-39 ; 820c8 bltu a4,a5 : width test *)
  stp. rewrite (unsigned_lit q) by lia. stp. stp.
  rewrite width_test by lia.
  destruct ((2 <=? q) && (q <=? 40)) eqn:B5; cbn [negb].
  2:{ ufail UF. }
  apply andb_true_iff in B5. destruct B5 as [B5a B5b]. apply Z.leb_le in B5a, B5b.
  (* 820cc andi a4,a6,1 ; 820d0 bnez a4 : odd test *)
  stp. rewrite (unsigned_lit q) by lia. rewrite land1. stp. brq B6.
  2:{ ufail UF. }
  assert (UQ : up_nch len = q) by (apply up_nch_val; lia).
  assert (HLQ : len = 52 + 36 * q) by (subst q; Z.div_mod_to_equations; lia).
  clear M36. clearbody q.
  zify_cond B2. zify_cond B3.
  assert (RN : raw <> 0) by (rewrite Ea0 in B2; lia).
  assert (ON : out <> 0) by (rewrite Ea2 in B3; lia).
  assert (UQ0 : 0 <= up_nch len) by (rewrite UQ; lia).
  destruct (HB RN ON UQ0) as [LEN BB].
  specialize (AR RN ON UQ0).
  assert (RLT : raw + len <= 0x800000000000) by
    (destruct AR as (_ & _ & H & _); unfold APPMEM_END in H; exact H).
  (* DR stays folded (off_stk): lia does not pay for its disjunction in the steps below. *)
  specialize (DR RN ON UQ0).
  pose proof (bytes_at_bound _ _ _ _ BB) as BBB. rewrite LEN, Z2Nat.id in BBB by lia.
  pose proof (bytes_tp m m0 _ _ raw bs MU1 ltac:(rewrite LEN, Z2Nat.id by lia; unfold off_stk in DR; lia) BB) as BB0.
  assert (AR0 : addressable m0 raw len).
  { unfold off_stk in DR.
    eapply addr_munch; [exact AR | exact MU1 |].
    intros i Hi. destruct (addr_one m raw len i AR Hi) as (Hap & _).
    cbn [outside]. split; [|exact I]. intros W.
    apply (shadow_not_app (raw + i) Hap).
    apply (app_win (bv_unsigned sp) 96); [lia | exact APS1 | exact APS2 | lia]. }
  pose proof (bytes_nth m0 raw bs 12 BB0 ltac:(rewrite LEN; lia)) as F12. change (Z.of_nat 12) with 12 in F12.
  pose proof (bytes_nth m0 raw bs 13 BB0 ltac:(rewrite LEN; lia)) as F13. change (Z.of_nat 13) with 13 in F13.
  pose proof (bytes_nth m0 raw bs (Z.to_nat (len - 2)) BB0 ltac:(rewrite LEN; lia)) as F90.
  rewrite Z2Nat.id in F90 by lia.
  pose proof (bytes_nth m0 raw bs (Z.to_nat (len - 1)) BB0 ltac:(rewrite LEN; lia)) as F91.
  rewrite Z2Nat.id in F91 by lia.
  (* the input bytes raw+12, raw+13, raw+len-2, raw+len-1 and their shadow bytes are in RNG *)
  specialize (RR RN ON UQ0). specialize (RRS RN ON UQ0).
  assert (RB91 : ExecF.rng RNG (raw + (len - 1)) 1) by (eapply rng_sub; [exact RR | lia | lia]).
  assert (RK91 : ExecF.rng RNG ((raw + (len - 1)) / 8 + 2147450880) 1) by (eapply rng_sub; [exact RRS | lia | lia]).
  assert (RB90 : ExecF.rng RNG (raw + (len - 2)) 1) by (eapply rng_sub; [exact RR | lia | lia]).
  assert (RK90 : ExecF.rng RNG ((raw + (len - 2)) / 8 + 2147450880) 1) by (eapply rng_sub; [exact RRS | lia | lia]).
  assert (RB13 : ExecF.rng RNG (raw + 13) 1) by (eapply rng_sub; [exact RR | lia | lia]).
  assert (RK13 : ExecF.rng RNG ((raw + 13) / 8 + 2147450880) 1) by (eapply rng_sub; [exact RRS | lia | lia]).
  assert (RB12 : ExecF.rng RNG (raw + 12) 1) by (eapply rng_sub; [exact RR | lia | lia]).
  assert (RK12 : ExecF.rng RNG ((raw + 12) / 8 + 2147450880) 1) by (eapply rng_sub; [exact RRS | lia | lia]).
  (* 820d4 li a4,-12 ; 820d8 bgeu a3,a4 : overflow trap not taken *)
  stp. stp. cnd false.
  (* 820dc auipc ; 820e0 ld a4 (GOT cell) ; 820e4 ld a5 (shadow base 0x7fff8000) *)
  stp. stp. stp.
  (* Each check below takes the facts of its own byte only (its shadow byte, its offset mod 8, an rng fact at the
     loaded address), and clr8 drops them after the check: lia stays fast in every step. *)
  (* check 1: the byte at raw+12, after the instrumented check of its shadow byte *)
  destruct (addr_one m0 raw len 12 AR0 ltac:(lia)) as (_ & k12 & M12 & SK12). unfold ASAN_K in M12.
  pose proof (Z.mod_pos_bound (raw + 12) 8 ltac:(lia)) as MB12.
  stp. gen_addi a0 w12 U12. rewrite Ea0 in U12.
  pshadowF m0 w12 U12 M12 k12 SK12 MB12.
  all: assert (RW : ExecF.rng RNG (bv_unsigned w12) 1) by (rewrite U12; exact RB12).
  all: pose proof (rdw0 m0 w12 _ _ F12 ltac:(lia)) as R; stp; clear R RW.
  all: stp; stp; rewrite eqb_zxb by lia; brq B7; [|ufail UF].
  all: clear RB12 RK12; clr8.
  (* check 2: 82108 li a4,-14 ; 8210c bltu a4,a3 : trap not taken ; the byte at raw+13 *)
  all: stp; stp; cnd false.
  all: destruct (addr_one m0 raw len 13 AR0 ltac:(lia)) as (_ & k13 & M13 & SK13); unfold ASAN_K in M13.
  all: pose proof (Z.mod_pos_bound (raw + 13) 8 ltac:(lia)) as MB13.
  all: stp; gen_addi a0 w13 U13; rewrite Ea0 in U13.
  all: pshadowF m0 w13 U13 M13 k13 SK13 MB13.
  all: assert (RW : ExecF.rng RNG (bv_unsigned w13) 1) by (rewrite U13; exact RB13).
  all: pose proof (rdw0 m0 w13 _ _ F13 ltac:(lia)) as R; stp; clear R RW.
  all: stp; stp; rewrite eqb_zxb by lia; brq B8; [|ufail UF].
  all: clear RB13 RK13; clr8.
  (* check 3: 82130 addi a4,a1,-2 ; 82134 not a7,a3 ; 82138 bltu a7,a4 : trap not taken ; the byte at raw+len-2 *)
  all: stp; stp; rewrite ?Ea0, ?zb_lxor_ones by lia; stp; cnd false.
  all: destruct (addr_one m0 raw len (len - 2) AR0 ltac:(lia)) as (_ & k90 & M90 & SK90); unfold ASAN_K in M90.
  all: pose proof (Z.mod_pos_bound (raw + (len - 2)) 8 ltac:(lia)) as MB90.
  all: stp; rewrite ?(unsigned_lit (len + -2)) by lia.
  all: gen_addi a0 w3 U3; rewrite Ea0 in U3; replace (raw + (len + -2)) with (raw + (len - 2)) in U3 by lia.
  all: pshadowF m0 w3 U3 M90 k90 SK90 MB90.
  all: assert (RW : ExecF.rng RNG (bv_unsigned w3) 1) by (rewrite U3; exact RB90).
  all: pose proof (rdw0 m0 w3 _ _ F90 ltac:(lia)) as R; stp; clear R RW.
  all: stp; stp; rewrite eqb_zxb by lia; brq B9; [|ufail UF].
  all: clear RB90 RK90; clr8.
  (* check 4: 8215c addi a1,a1,-1 ; 82160 bltu a7,a1 : trap not taken ; the byte at raw+len-1 *)
  all: stp; stp; cnd false.
  all: destruct (addr_one m0 raw len (len - 1) AR0 ltac:(lia)) as (_ & k91 & M91 & SK91); unfold ASAN_K in M91.
  all: pose proof (Z.mod_pos_bound (raw + (len - 1)) 8 ltac:(lia)) as MB91.
  all: stp; rewrite ?(unsigned_lit (len + -1)) by lia.
  all: gen_addi a0 w4 U4; rewrite Ea0 in U4; replace (raw + (len + -1)) with (raw + (len - 1)) in U4 by lia.
  all: pshadowF m0 w4 U4 M91 k91 SK91 MB91.
  all: assert (RW : ExecF.rng RNG (bv_unsigned w4) 1) by (rewrite U4; exact RB91).
  all: pose proof (rdw0 m0 w4 _ _ F91 ltac:(lia)) as R; stp; clear R RW.
  all: stp; stp; rewrite eqb_zxb by lia; brq B10; [|ufail UF].
  all: clear RB91 RK91; clr8.
  (* every test passed: up_ok is true *)
  all: assert (OK : up_ok raw out len bs = true) by
    (rewrite up_ok_true; unfold inspect_byte; rewrite UQ; repeat split; lia).
  (* 82184 li a0,-51 ; 82188 bltu a0,a3 : trap not taken *)
  all: stp; stp; cnd false.
  (* 8218c .. 821b8 : the loop registers ; then the outer loop head 0x821bc *)
  all: do 12 stp.
  (* the facts of the output, for the loop *)
  all: destruct (HO OK) as (HW & HoutN' & DOR'); rewrite UQ in HW, HoutN', DOR'.
  all: specialize (DO OK); rewrite UQ in DO.
  all: specialize (AO OK); rewrite UQ in AO.
  all: specialize (RO OK); rewrite UQ in RO.
  all: specialize (ROS OK); rewrite UQ in ROS.
  all: assert (HW1 : wr_at rsegs m0 out (36 * q)) by (eapply wr_at_transport; [exact HW | exact WM]).
  all: eapply (up_outer_holdsF RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m bs raw out len lo q LO Hlo UQ
         ltac:(lia) B6 HLQ LEN ltac:(lia) ltac:(lia) ltac:(lia)
         HoutN' DOR' DO DR AR AO
         ltac:(intros x Hx; apply (app_win (bv_unsigned sp) 96); [lia | exact APS1 | exact APS2 | lia]) OK
         ltac:(eapply rng_sub; [exact RS | lia | lia]) RR RRS RO ROS).
  all: lazymatch goal with
       | |- INVU _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
           unfold INVU; split; [exact BB0|]; split; [unfold FRU; eexists; exact FR|]; split; [exact ST|];
           split; [exact HW1|]; split; [apply munch_extend; exact MU1|]; split; [exact WM|];
           change (bpre bs q 0) with (@nil byte); apply bytes_at_nil; lia
       | |- _ => idtac
       end.
  all: regeq Ea0.
Qed.

(* The twin gives the old contract back: take the footprint that admits every access. *)
Theorem reac_upstream_decode_holds_of_F : reac_upstream_decode_contract.
Proof.
  unfold reac_upstream_decode_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m bs raw out lo E0 E2 Rraw Rout Rlen HMG HB HO ST LO DR DO DM APS1 APS2 CELLS SGOT AR AO.
  pose proof (u64_range sp) as Rsp. pose proof (u64_range a1) as Ra1.
  assert (Hlo : 0 <= lo) by (destruct ST as [? _]; lia).
  apply (ExecF.evtF_evt rsegs RNG_all).
  apply reac_upstream_decode_holds_F; try assumption;
    unfold REAC_UPSTREAM_DECODE_D, DIV36_MAGIC_AT, GOT_CELL_K, CELL_K, ASAN_K in *.
  - apply rng_all; lia.
  - apply rng_all; lia.
  - apply rng_all; lia.
  - apply rng_all; lia.
  - intros HR HO' HN. destruct (AR HR HO' HN) as (_ & _ & H & _). unfold APPMEM_END in H. apply rng_all; lia.
  - intros HR HO' HN. apply rng_all; [Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia].
  - intros OK. destruct (HO OK) as (_ & HN & _). apply rng_all; lia.
  - intros OK. destruct (HO OK) as (_ & HN & _). apply up_ok_true in OK. destruct OK as (_ & _ & HU & _).
    apply rng_all; [Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia].
Qed.
