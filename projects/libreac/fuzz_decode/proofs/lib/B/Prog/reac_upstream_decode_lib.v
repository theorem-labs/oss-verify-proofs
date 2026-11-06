From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import AsanKA AsanKAProof reac_frame_inspect_c reac_decode_c reac_upstream_decode_c ReacDecodeLib.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import reac_upstream_decode_h reac_upstream_decode_if.
Import ListNotations.
Open Scope Z_scope.

(* The instrumented checks of the loop body. Each one reads the shadow byte k of address A at A / 8 + ASAN_K
   (the shadow base 2147450880 is in a5) and goes on when k = 0 or A mod 8 < k; the error path (a call of the
   report entry) is not reached. *)

(* 82244 add a0,a3,a1 ; srli a1,a0,3 ; add a1,a1,a5 ; lb a1 ; bnez a1 -> (82304 andi s4,a0,7 ; bge ; j) ; 82258 *)
Lemma ul0 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (P : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x13 + bv_unsigned x11 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  (forall y10 y11 y20 : word, bv_unsigned y10 = A ->
     evt rsegs P (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y10 y11 x12 x13 x14 (Z_to_bv 64 2147450880) x16 x17 x18 x19 y20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x82258) fc None mm (seg_rom rsegs))) ->
  evt rsegs P (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 (Z_to_bv 64 2147450880) x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x82244) fc None mm (seg_rom rsegs)).
Proof.
  intros until A. intros EA RA M SK CONT.
  pose proof (u64_range x13) as R13. pose proof (u64_range x11) as R11. unfold ASAN_K in M.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  step. gen_add x13 x11 w U. rewrite EA in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT. exact U.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, U, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT. exact U.
Qed.

(* 82258 srli a1,a2,3 ; add a1,a1,a5 ; lb a1 ; lbu a0,0(a0) ; bnez a1 -> (82310 andi s4,a2,7 ; bge ; j) ; 8226c *)
Lemma us0 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (P : machine_state -> Prop) (k b : byte) (Qa A3 : Z),
  bv_unsigned x12 = Qa -> Qa < 2^64 -> bv_unsigned x10 = A3 ->
  mrd rsegs mm (wa (Qa / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ Qa mod 8 < bv_signed k) ->
  mrd rsegs mm (wa A3) = Some b ->
  (forall y11 y20 : word,
     evt rsegs P (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (zxb b) y11 x12 x13 x14 (Z_to_bv 64 2147450880) x16 x17 x18 x19 y20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x8226c) fc None mm (seg_rom rsegs))) ->
  evt rsegs P (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 (Z_to_bv 64 2147450880) x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x82258) fc None mm (seg_rom rsegs)).
Proof.
  intros until A3. intros EQ RQ EA3 M SK Fsrc CONT.
  pose proof (u64_range x12) as R12. unfold ASAN_K in M.
  pose proof (Z.mod_pos_bound Qa 8 ltac:(lia)) as MB.
  step. gen_shr x12 g G. rewrite EQ in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw0 mm x10 _ _ Fsrc EA3) as R. step. clear R.
  step.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, EQ, (lts_low (Qa mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* 82280 add a0,a3,a0 ; srli a1,a0,3 ; add a1,a1,a5 ; lb a1 ; bnez a1 -> (8231c andi s5,a0,7 ; bge ; j) ; 82294 *)
Lemma ul1 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (P : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x13 + bv_unsigned x10 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  (forall y10 y11 y21 : word, bv_unsigned y10 = A ->
     evt rsegs P (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y10 y11 x12 x13 x14 (Z_to_bv 64 2147450880) x16 x17 x18 x19 x20 y21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x82294) fc None mm (seg_rom rsegs))) ->
  evt rsegs P (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 (Z_to_bv 64 2147450880) x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x82280) fc None mm (seg_rom rsegs)).
Proof.
  intros until A. intros EA RA M SK CONT.
  pose proof (u64_range x13) as R13. pose proof (u64_range x10) as R10. unfold ASAN_K in M.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  step. gen_add x13 x10 w U. rewrite EA in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT. exact U.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, U, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT. exact U.
Qed.

(* 82294 addi a1,a2,1 ; srli s5,a1,3 ; add s5,s5,a5 ; lb s5 ; lbu a0,0(a0) ; bnez s5 -> (82328 andi s6,a1,7 ; bge ; j) ; 822ac *)
Lemma us1 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (P : machine_state -> Prop) (k b : byte) (Qa A3 : Z),
  bv_unsigned x12 + 1 = Qa -> Qa < 2^64 -> bv_unsigned x10 = A3 ->
  mrd rsegs mm (wa (Qa / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ Qa mod 8 < bv_signed k) ->
  mrd rsegs mm (wa A3) = Some b ->
  (forall y11 y21 y22 : word,
     evt rsegs P (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (zxb b) y11 x12 x13 x14 (Z_to_bv 64 2147450880) x16 x17 x18 x19 x20 y21 y22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x822ac) fc None mm (seg_rom rsegs))) ->
  evt rsegs P (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 (Z_to_bv 64 2147450880) x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x82294) fc None mm (seg_rom rsegs)).
Proof.
  intros until A3. intros EQ RQ EA3 M SK Fsrc CONT.
  pose proof (u64_range x12) as R12. unfold ASAN_K in M.
  pose proof (Z.mod_pos_bound Qa 8 ltac:(lia)) as MB.
  step. gen_addi x12 w U. rewrite EQ in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw0 mm x10 _ _ Fsrc EA3) as R. step. clear R.
  step.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, U, (lts_low (Qa mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* 822c0 add a0,a3,a0 ; srli a1,a0,3 ; add a1,a1,a5 ; lb a1 ; bnez a1 -> (82334 andi s5,a0,7 ; bge ; j) ; 822d4 *)
Lemma ul2 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (P : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x13 + bv_unsigned x10 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  (forall y10 y11 y21 : word, bv_unsigned y10 = A ->
     evt rsegs P (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y10 y11 x12 x13 x14 (Z_to_bv 64 2147450880) x16 x17 x18 x19 x20 y21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x822d4) fc None mm (seg_rom rsegs))) ->
  evt rsegs P (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 (Z_to_bv 64 2147450880) x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x822c0) fc None mm (seg_rom rsegs)).
Proof.
  intros until A. intros EA RA M SK CONT.
  pose proof (u64_range x13) as R13. pose proof (u64_range x10) as R10. unfold ASAN_K in M.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  step. gen_add x13 x10 w U. rewrite EA in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT. exact U.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, U, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT. exact U.
Qed.

(* 822d4 addi a1,a2,2 ; srli s5,a1,3 ; add s5,s5,a5 ; lb s5 ; lbu a0,0(a0) ; bnez s5 -> (82340 andi s6,a1,7 ; bge ; j) ; 822ec *)
Lemma us2 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (P : machine_state -> Prop) (k b : byte) (Qa A3 : Z),
  bv_unsigned x12 + 2 = Qa -> Qa < 2^64 -> bv_unsigned x10 = A3 ->
  mrd rsegs mm (wa (Qa / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ Qa mod 8 < bv_signed k) ->
  mrd rsegs mm (wa A3) = Some b ->
  (forall y11 y21 y22 : word,
     evt rsegs P (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (zxb b) y11 x12 x13 x14 (Z_to_bv 64 2147450880) x16 x17 x18 x19 x20 y21 y22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x822ec) fc None mm (seg_rom rsegs))) ->
  evt rsegs P (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 (Z_to_bv 64 2147450880) x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x822d4) fc None mm (seg_rom rsegs)).
Proof.
  intros until A3. intros EQ RQ EA3 M SK Fsrc CONT.
  pose proof (u64_range x12) as R12. unfold ASAN_K in M.
  pose proof (Z.mod_pos_bound Qa 8 ltac:(lia)) as MB.
  step. gen_addi x12 w U. rewrite EQ in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw0 mm x10 _ _ Fsrc EA3) as R. step. clear R.
  step.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, U, (lts_low (Qa mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

Section UPL.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (raw out len lo : Z).

Local Notation SP := (bv_unsigned sp).
Local Notation POST := (PostU ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m bs raw out len lo).
Local Notation STATE pc mm x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 :=
  (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
        x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
      F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

Hypothesis Hsp : lo + 96 <= SP.
Hypothesis Hlo : 0 <= lo.

(* 82098: ld ra ; ld s0..s6 ; addi sp,sp,96 ; ret *)
Lemma up_exit_gen : forall (m1 : word -> option byte) (r : Z)
    (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 : word),
  FRU ra sp s0 s1 s2 s3 s4 s5 s6 m1 -> stk rsegs m1 lo (SP + -96) -> wmono rsegs m m1 ->
  r = (if up_ok raw out len bs then 12 else -1) ->
  (if up_ok raw out len bs
   then munch [(SP + -96, SP); (out, out + 36 * up_nch len)] m m1 /\
        bytes_at rsegs m1 out (braid_out bs (up_nch len) 12)
   else munch [(SP + -96, SP)] m m1) ->
  evt rsegs POST (MS (mkR x1 (Z_to_bv 64 (SP + -96)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
      x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x82098) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 r x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 (junk & HF) ST WM Er HM.
  pose proof (u64_range sp) as Rsp.
  do 10 step.
  apply evt_done. unfold PostU. exists x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, m1.
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
Hypothesis DOR : out + 36 * nch <= raw \/ raw + len <= out.
Hypothesis DOS : out + 36 * nch <= SP - 96 \/ SP <= out.
Hypothesis DRS : raw + len <= SP - 96 \/ SP <= raw.
Hypothesis AR : addressable m raw len.
Hypothesis AO : addressable m out (36 * nch).
Hypothesis APW : forall x, SP - 96 <= x < SP -> app_mem x.
Hypothesis OK : up_ok raw out len bs = true.

Local Notation N := (36 * nch).
Local Notation INV := (INVU ra sp s0 s1 s2 s3 s4 s5 s6 m bs raw out lo nch).

Lemma INVU_idx : forall mk j j', INV mk j -> j = j' -> INV mk j'.
Proof. intros; subst; assumption. Qed.

Lemma bpre_len : forall j, 0 <= j -> Z.of_nat (length (bpre bs nch j)) = j.
Proof. intros j Hj. unfold bpre. rewrite length_mapseq. lia. Qed.

Lemma bpre_S : forall j, 0 <= j -> bpre bs nch (j + 1) = bpre bs nch j ++ [braid_byte bs nch 12 j].
Proof.
  intros j Hj. unfold bpre. replace (Z.to_nat (j + 1)) with (Z.to_nat j + 1)%nat by lia.
  rewrite seq_app, !map_app. cbn [seq map Nat.add]. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma bw_ext : forall mk q0 q, bytes_at rsegs mk out (bpre bs nch q0) -> q0 = q -> 0 <= q -> out + q + 1 <= 2^64 ->
  bytes_at rsegs (write_to_mem mk (wa (out + q)) [braid_byte bs nch 12 q]) out (bpre bs nch (q + 1)).
Proof.
  intros mk q0 q HB E Hq Hb. subst q0. pose proof (bpre_len q Hq) as L.
  rewrite bpre_S by lia. apply bytes_at_app. split.
  - apply bytes_at_write_other; [exact HB | lia | cbn [length]; lia | cbn [length]; lia].
  - rewrite L. apply bytes_at_write_same; cbn [length]; lia.
Qed.

Lemma addr_m : forall mk p n, munch [(SP + -96, SP); (out, out + N)] m mk -> addressable m p n -> addressable mk p n.
Proof.
  intros mk p n MU A. eapply addr_munch; [exact A | exact MU |].
  intros i Hi. destruct A as (_ & _ & _ & HA). destruct (HA i Hi) as (Ha & _).
  pose proof (shadow_not_app _ Ha) as NA. cbn [outside]. split; [|split; [|exact I]].
  - intros W. apply NA, APW. lia.
  - intros W. apply NA. destruct AO as (_ & _ & _ & HO). destruct (HO ((p + i) / 8 + ASAN_K - out) ltac:(lia)) as (Ho & _).
    replace (out + ((p + i) / 8 + ASAN_K - out)) with ((p + i) / 8 + ASAN_K) in Ho by lia. exact Ho.
Qed.

Lemma src_bound : forall ch s k o, 0 <= ch < nch -> 0 <= s < 12 -> 0 <= k < 3 -> o = boff (ch mod 2) k ->
  0 <= 50 + (3 * (s * nch + (ch - ch mod 2)) + o) < len.
Proof.
  intros ch s k o Hch Hs Hk Ho.
  pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hm.
  assert (s * nch <= 11 * nch) by nia.
  assert (0 <= s * nch) by nia.
  assert (ch - ch mod 2 <= nch - 2) by (Z.div_mod_to_equations; lia).
  assert (0 <= ch - ch mod 2) by (Z.div_mod_to_equations; lia).
  assert (0 <= o <= 5) by (subst o; unfold boff; destruct (k =? 0), (k =? 1); lia).
  nia.
Qed.

Lemma SRC_rd : forall mk ch s k o, bytes_at rsegs mk raw bs -> 0 <= ch < nch -> 0 <= s < 12 -> 0 <= k < 3 ->
  o = boff (ch mod 2) k ->
  mrd rsegs mk (wa (raw + (50 + (3 * (s * nch + (ch - ch mod 2)) + o)))) = Some (braid_byte bs nch 12 (3 * (ch * 12 + s) + k)).
Proof.
  intros mk ch s k o HB Hch Hs Hk Ho.
  pose proof (src_bound ch s k o Hch Hs Hk Ho) as SB.
  rewrite braid_byte_at by lia. rewrite (braid_pos_boff s ch nch k Hk), <- Ho.
  pose proof (bytes_nth mk raw bs (Z.to_nat (50 + (3 * (s * nch + (ch - ch mod 2)) + o))) HB ltac:(rewrite Hlen; lia)) as R.
  rewrite Z2Nat.id in R by lia. exact R.
Qed.

Lemma SRC_shr : forall mk ch s k o, munch [(SP + -96, SP); (out, out + N)] m mk ->
  0 <= ch < nch -> 0 <= s < 12 -> 0 <= k < 3 -> o = boff (ch mod 2) k ->
  exists kb, mrd rsegs mk (wa ((raw + (50 + (3 * (s * nch + (ch - ch mod 2)) + o))) / 8 + ASAN_K)) = Some kb /\
    (bv_signed kb = 0 \/ (raw + (50 + (3 * (s * nch + (ch - ch mod 2)) + o))) mod 8 < bv_signed kb).
Proof.
  intros mk ch s k o MU Hch Hs Hk Ho.
  pose proof (src_bound ch s k o Hch Hs Hk Ho) as SB.
  destruct (addr_one mk raw len (50 + (3 * (s * nch + (ch - ch mod 2)) + o)) (addr_m mk raw len MU AR) SB)
    as (_ & kb & M & S). exists kb. split; assumption.
Qed.

Lemma DST_sho : forall mk q, munch [(SP + -96, SP); (out, out + N)] m mk -> 0 <= q < N ->
  exists kb, mrd rsegs mk (wa ((out + q) / 8 + ASAN_K)) = Some kb /\
    (bv_signed kb = 0 \/ (out + q) mod 8 < bv_signed kb).
Proof.
  intros mk q MU Hq.
  destruct (addr_one mk out N q (addr_m mk out N MU AO) Hq) as (_ & kb & M & S). exists kb. split; assumption.
Qed.

(* A store of an output byte: the prefix grows by one byte; the other facts move to the new memory. *)
Ltac ostore :=
  rewrite ?le1_zxb;
  lazymatch goal with
  | |- evt ?sg ?Q (MS ?R ?Fr ?pc ?f ?rv (write_to_mem ?mk ?w [braid_byte bs nch 12 ?q]) ?ro) =>
      replace w with (wa (out + q)) by (unfold wa; apply f_equal; lia);
      match goal with BW : bytes_at _ mk out (bpre bs nch ?q0) |- _ =>
        apply (bw_ext mk q0 q) in BW; [ | lia | lia | lia ]
      end;
      match goal with H : Z.of_nat (length (bpre bs nch _)) = _ |- _ => clear H end;
      assert (LB : Z.of_nat (length (bpre bs nch (q + 1))) = q + 1) by (apply bpre_len; lia);
      transport_chunks sg mk (out + q) [braid_byte bs nch 12 q];
      footprint_after_store sg mk (out + q) [braid_byte bs nch 12 q];
      let m2 := fresh "m" in set (m2 := write_to_mem mk (wa (out + q)) [braid_byte bs nch 12 q]) in *; clearbody m2
  end.

(* The frame after the three scratch stores is [CB 8; C8; C8; C8; saved registers]: merge the scratch back. *)
Ltac rebundle :=
  lazymatch goal with H : rw_cells _ ?mm ?A (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?post) |- _ =>
    apply (rw_cells_merge rsegs mm A [] [c1; c2; c3; c4] post) in H; cbn [app cells_size csize Nat.add] in H;
    split; [assumption|]; split; [eexists; exact H|]; split; [assumption|]; split; [assumption|];
    split; [assumption|]; split; [assumption|]; eassumption
  end.

Lemma up_inner : forall (ch : Z) (x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word),
  0 <= ch < nch ->
  bv_unsigned x5 = SP + -88 -> bv_unsigned x6 = 18446744073709551599 -> bv_unsigned x7 = 18446744073709551615 ->
  bv_unsigned x9 = ch - ch mod 2 -> bv_unsigned x13 = raw + 50 -> bv_unsigned x14 = ch ->
  bv_unsigned x15 = 2147450880 -> bv_unsigned x16 = nch -> bv_unsigned x17 = 18446744073709551608 ->
  bv_unsigned x18 = ch mod 2 -> bv_unsigned x28 = 12 -> bv_unsigned x29 = 18446744073709551615 - (raw + 50) ->
  bv_unsigned x30 = 2147483646 -> bv_unsigned x31 = 18446744073709551607 ->
  (forall (m2 : word -> option byte) (y8 y10 y11 y12 y19 y20 y21 y22 : word),
     bv_unsigned y19 = out + 3 * (ch * 12 + 11) -> INV m2 (3 * (ch * 12 + 12)) ->
     evt rsegs POST (STATE 0x8234c m2 x5 x6 x7 y8 x9 y10 y11 y12 x13 x14 x15 x16 x17 x18 y19 y20 y21 y22 x28 x29 x30 x31)) ->
  forall (K : nat) (s : Z) (m1 : word -> option byte) (x8 x10 x11 x12 x19 x20 x21 x22 : word),
  Z.to_nat (12 - s) = K -> 0 <= s < 12 ->
  bv_unsigned x8 = s -> bv_unsigned x12 = out + 3 * (ch * 12 + s) -> bv_unsigned x20 = out + 3 * (ch * 12 + s) ->
  INV m1 (3 * (ch * 12 + s)) ->
  evt rsegs POST (STATE 0x821cc m1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31).
Proof.
  intros ch x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31
    Hch H5 H6 H7 H9 H13 H14 H15 H16 H17 H18 H28 H29 H30 H31 CONT K.
  pose proof (u64_range sp) as Rsp.
  apply wv in H5, H6, H7, H9, H13, H14, H15, H16, H17, H18, H28, H29, H30, H31.
  subst x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31.
  pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hm.
  assert (Hc2 : ch - ch mod 2 <= nch - 2) by (Z.div_mod_to_equations; lia).
  assert (Hc0 : 0 <= ch - ch mod 2) by (Z.div_mod_to_equations; lia).
  assert (Hc12 : 0 <= ch * 12 <= (nch - 1) * 12) by nia.
  assert (HLZ : Z.of_nat (length bs) = len) by (rewrite Hlen; lia).
  induction K as [K IH] using lt_wf_ind.
  intros s m1 x8 x10 x11 x12 x19 x20 x21 x22 HK Hs H8 H12 H20 I0.
  apply wv in H8, H12, H20. subst x8 x12 x20.
  assert (Hsn : 0 <= s * nch <= 11 * nch) by nia.
  assert (Hq : 0 <= 3 * (ch * 12 + s) /\ 3 * (ch * 12 + s) + 2 < N) by nia.
  destruct I0 as (BR & (junk & FR) & ST & WA & MU & WM & BW).
  assert (LB : Z.of_nat (length (bpre bs nch (3 * (ch * 12 + s)))) = 3 * (ch * 12 + s)) by (apply bpre_len; lia).
  (* 821cc mul a0,s0,a6 ; mulw a1,s0,a6 ; bne a1,a0 : trap *)
  st. st. st. cnd false.
  (* 821d8 sext.w a1,a0 ; add a0,a1,s1 ; addw a1,a1,s1 ; bne a1,a0 : trap *)
  st. st. st. st. cnd false.
  (* 821e8 mv s3,s4 ; sext.w a0,a0 ; slli a1,a0,1 ; add a0,a1,a0 ; bnez s2 *)
  st. st. st. st. st.
  destruct (Z.eqb_spec (ch mod 2) 0) as [EP|EP].
  (* even: 821fc addi a1,a0,3 ; sd a1,8(sp) ; bgeu t0,a7 : trap ; sd a0,16(sp) ; bltu t1,t0 : trap ;
     addi a0,a0,1 ; j 82234 *)
  1: (cnd false; st; st; st; cnd false; st; st; cnd false; st; st).
  (* odd: 82218 addi a1,a0,4 ; sd a1,8(sp) ; bltu t6,t0 : trap ; addi a1,a0,5 ; sd a1,16(sp) ; bltu t1,t0 : trap ;
     addi a0,a0,2 *)
  2: (cnd true; st; st; st; cnd false; st; st; st; cnd false; st).
  (* 82234 ld a1,8(sp) ; sd a0,24(sp) ; bltu t4,a1 : trap ; beq s3,t2 : trap *)
  all: st. all: st. all: st. all: cnd false. all: st. all: cnd false.
  (* 82244 byte 0: load check of raw+50+off0 *)
  all: destruct (SRC_shr _ ch s 0 (3 + ch mod 2) MU Hch Hs ltac:(lia) eq_refl) as (k0 & MK & SK).
  all: eapply ul0; [ | | exact MK | exact SK | intros p10 p11 p20 Ep10 ]; [ ufin | lia | ]. all: clear MK SK.
  (* 82258 store check of out+j ; lbu *)
  all: destruct (DST_sho _ (3 * (ch * 12 + s) + 0) MU ltac:(lia)) as (ks & MS & SKs).
  all: pose proof (SRC_rd _ ch s 0 (3 + ch mod 2) BR Hch Hs ltac:(lia) eq_refl) as RD.
  all: eapply us0; [ | | exact Ep10 | exact MS | exact SKs | exact RD | intros q11 q20 ]; [ ufin | lia | ].
  all: clear MS SKs RD Ep10.
  (* 8226c sb a0,0(s3) *)
  all: pose proof (wr_at_store_ok rsegs _ out N (3 * (ch * 12 + s) + 0) 1 WA ltac:(lia) ltac:(lia)) as HS.
  all: st. all: clear HS. all: ostore.
  (* 82270 ld a0,16(sp) ; bltu t4,a0 : trap ; addi s4,s3,1 ; beq s4,t2 : trap *)
  all: st. all: st. all: cnd false. all: st. all: st. all: cnd false.
  (* 82280 byte 1 *)
  all: destruct (SRC_shr _ ch s 1 (5 * (ch mod 2)) MU Hch Hs ltac:(lia) eq_refl) as (k1 & MK & SK).
  all: eapply ul1; [ | | exact MK | exact SK | intros r10 r11 r21 Er10 ]; [ ufin | lia | ]. all: clear MK SK.
  all: destruct (DST_sho _ (3 * (ch * 12 + s) + 1) MU ltac:(lia)) as (ks1 & MS & SKs).
  all: pose proof (SRC_rd _ ch s 1 (5 * (ch mod 2)) BR Hch Hs ltac:(lia) eq_refl) as RD.
  all: eapply us1; [ | | exact Er10 | exact MS | exact SKs | exact RD | intros u11 u21 u22 ]; [ ufin | lia | ].
  all: clear MS SKs RD Er10.
  (* 822ac sb a0,0(s4) *)
  all: pose proof (wr_at_store_ok rsegs _ out N (3 * (ch * 12 + s) + 1) 1 WA ltac:(lia) ltac:(lia)) as HS.
  all: st. all: clear HS. all: ostore.
  (* 822b0 ld a0,24(sp) ; bltu t4,a0 : trap ; addi s4,s4,1 ; beq s4,t2 : trap *)
  all: st. all: st. all: cnd false. all: st. all: st. all: cnd false.
  (* 822c0 byte 2 *)
  all: destruct (SRC_shr _ ch s 2 (1 + ch mod 2) MU Hch Hs ltac:(lia) eq_refl) as (k2 & MK & SK).
  all: eapply ul2; [ | | exact MK | exact SK | intros v10 v11 v21 Ev10 ]; [ ufin | lia | ]. all: clear MK SK.
  all: destruct (DST_sho _ (3 * (ch * 12 + s) + 2) MU ltac:(lia)) as (ks2 & MS & SKs).
  all: pose proof (SRC_rd _ ch s 2 (1 + ch mod 2) BR Hch Hs ltac:(lia) eq_refl) as RD.
  all: eapply us2; [ | | exact Ev10 | exact MS | exact SKs | exact RD | intros w11 w21 w22 ]; [ ufin | lia | ].
  all: clear MS SKs RD Ev10.
  (* 822ec sb a0,0(s4) *)
  all: pose proof (wr_at_store_ok rsegs _ out N (3 * (ch * 12 + s) + 2) 1 WA ltac:(lia) ltac:(lia)) as HS.
  all: st. all: clear HS. all: ostore.
  (* 822f0 addiw s0,s0,1 ; addi a2,a2,3 ; addi s4,s4,1 ; bne s0,t3 *)
  all: st. all: st. all: st. all: st.
  all: brq BRq.
  all: lazymatch goal with
       | _ : ?sv + 1 = 12 |- _ =>
           (* 82300 j 8234c *)
           st; eapply CONT; [ ufin | eapply INVU_idx; [rebundle | lia] ]
       | _ : ?sv + 1 <> 12 |- _ =>
           eapply (IH (Z.to_nat (12 - (sv + 1))) ltac:(lia) (sv + 1));
           lazymatch goal with
           | |- INVU _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => eapply INVU_idx; [rebundle | lia]
           | _ => first [ reflexivity | lia | ufin ]
           end
       end.
Qed.

Lemma up_outer_gen : forall (K : nat) (ch : Z) (m1 : word -> option byte)
    (x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 : word),
  Z.to_nat (nch - ch) = K -> 0 <= ch < nch ->
  bv_unsigned x5 = SP + -88 -> bv_unsigned x6 = 18446744073709551599 -> bv_unsigned x7 = 18446744073709551615 ->
  bv_unsigned x12 = out + 3 * (ch * 12) -> bv_unsigned x13 = raw + 50 -> bv_unsigned x14 = ch ->
  bv_unsigned x15 = 2147450880 -> bv_unsigned x16 = nch -> bv_unsigned x17 = 18446744073709551608 ->
  bv_unsigned x28 = 12 -> bv_unsigned x29 = 18446744073709551615 - (raw + 50) -> bv_unsigned x30 = 2147483646 ->
  bv_unsigned x31 = 18446744073709551607 ->
  INV m1 (3 * (ch * 12)) ->
  evt rsegs POST (STATE 0x821bc m1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31).
Proof.
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
  eapply (up_inner ch) with (K := Z.to_nat (12 - 0)) (s := 0).
  all: lazymatch goal with
       | |- forall _ : word -> option byte, _ => idtac
       | |- INVU _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => eapply INVU_idx; [exact I0 | lia]
       | _ => first [ lia | reflexivity | ufin ]
       end.
  intros m2 y8 y10 y11 y12 y19 y20 y21 y22 H19 I2. apply wv in H19. subst y19.
  (* 8234c addiw a4,a4,1 ; addi a2,s3,3 ; bne a4,a6 *)
  st. st. st.
  brq BR.
  - (* ch + 1 = nch: 82358 li a0,12 ; j 82098 *)
    st. st.
    destruct I2 as (BB2 & FR2 & ST2 & WA2 & MU2 & WM2 & BW2).
    eapply up_exit_gen with (r := 12); [ exact FR2 | exact ST2 | exact WM2 | rewrite OK; reflexivity | ].
    rewrite OK, Hnchdef. split; [exact MU2 |].
    replace (braid_out bs nch 12) with (bpre bs nch (3 * (ch * 12 + 12)))
      by (unfold bpre, braid_out; do 3 f_equal; lia).
    exact BW2.
  - eapply (IH (Z.to_nat (nch - (ch + 1))) ltac:(lia) (ch + 1)).
    all: lazymatch goal with
         | |- INVU _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => eapply INVU_idx; [exact I2 | lia]
         | _ => first [ reflexivity | lia | ufin ]
         end.
Qed.

End UPL.

Lemma up_outer_holds : UP_OUTER.
Proof.
  unfold UP_OUTER.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m bs raw out len lo nch
    Hsp Hlo Hnchdef Hnch Hev Hlen52 Hlen Hraw Hraw2 Hout HoutN DOR DOS DRS AR AO APW OK
    m1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31
    H5 H6 H7 H12 H13 H14 H15 H16 H17 H28 H29 H30 H31 I0.
  eapply up_outer_gen with (nch := nch) (K := Z.to_nat (nch - 0)) (ch := 0).
  all: first [ eassumption | reflexivity | lia | (rewrite H12; lia) | (eapply INVU_idx; [exact I0 | lia]) ].
Qed.

Lemma up_exit_holds : UP_EXIT.
Proof.
  unfold UP_EXIT.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m bs raw out len lo Hsp Hlo
    m1 x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 HF ST WM OK MU BO.
  eapply up_exit_gen with (r := 12).
  all: first [ eassumption | (rewrite OK; reflexivity) | (rewrite OK; split; assumption) ].
Qed.

Lemma up_fail_holds : UP_FAIL.
Proof.
  unfold UP_FAIL.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m bs raw out len lo Hsp Hlo
    m1 x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 HF ST WM MU E.
  eapply up_exit_gen with (r := -1).
  all: first [ eassumption | (rewrite E; reflexivity) | (rewrite E; exact MU) ].
Qed.
