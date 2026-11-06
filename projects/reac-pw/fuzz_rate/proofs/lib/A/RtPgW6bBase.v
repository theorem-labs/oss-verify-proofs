(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6bBase.v at d1ed1a6d9011 for reac-pw/fuzz_rate's
   image A: module paths changed; the pcs, registers, real-frame cells, write set and image addresses are rate's
   (measured on fuzz_rate.asan); the block context, the input premise and the code table are lib/A/RtPgW6aBase.v's
   (w6_ctx, w6_in, w6_tbl), and the case entry adds the input's shadow hull and its distance from the frame's
   objects; the block post is RtPgSteps.rts_post. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, same loaded bytes): the BLOCK STATEMENTS of the
   walk piece "ent_build B" of LLVMFuzzerTestOneInput (0x80714): the cases 1, 4, 5 and 9 of ent_build's
   `switch (kind % 10)` (pod.h:285-296, 326-339, 367-377), each from its entry to the join J 0x81e00.
   Statement text only: no function is proved here (kind: segment lemma).

   ONE BLOCK PER CASE, so that a case is proved without the cut records of lib/A/RtPgSeg.v and the piece is the
   case's block between the two cut bridges of lib/A/RtPgEntBCut.v.
     w6b_c4  0x81668 .. J: v = fuzz_u8 % 3 (pod.h:327-330; `mul 0xab`, `srli 9`), e.type = 2, e.size = 4,
             e.body[0..4) = v (0x8199c .. 0x819b0); no byte left: 0x81994 (v = 0).
     w6b_c5  0x81804 .. J: n = min(fuzz_u8 % 32, left) (0x81824 .. 0x8182c), [R+0x100] := left (0x81830),
             memcpy(e.body, cursor, n) at 0x81844 (__asan_memcpy 0x51860), the NUL at e.body[n] unless kind & 0x80
             (`bltz s6` 0x8184c; an uninstrumented store), e.type = 8, e.size = n + (kind < 128) (pod.h:336-337,
             209-219), then 0x81c04 .. J; no byte left: 0x81b18 (n = 0).
     w6b_c9  0x81954 .. J: e.type = 14, body[0..4) = 14, body[4..8) = 8, memcpy(e.body + 8, s, 14) at 0x8197c
             (s = ent_build.s 0x21200, "reac.cfg.rate" and its NUL), e.size = 24 (pod.h:369-375); no input read.
     w6b_c1  0x817c4 .. J: i = fuzz_u8 % 9 (`mul 0x39`, `srli 9`), [R+0x100] := the cursor (0x81a38), the checked
             8-byte load of vocab[i] (0x81a60, .data.rel.ro 0x9bac0), the strlen wrapper at 0x81a68 (0x42194),
             l = min(len, 95), memcpy(e.body, vocab[i], l) at 0x81a90, the NUL, e.type = 8, e.size = l + 1, and with
             kind & 0x80 and len <= 93 the two checked byte stores 'x', 0 at e.body[l + 1], e.body[l + 2] and
             e.size = l + 3 (pod.h:286-294); no byte left: 0x81a2c (i = 0).
   THE STATE AT A CASE ENTRY (RtPgSeg.rs_L_D, checked against the code): s1 = R (x9) the real frame's base, sp = R,
   s2 = SHADOW_OFF (x18), s9 = c (x25) the cursor after the kind byte, a4 = c - 1 (x14), s8 = |r| (x24) what is left
   after it, a5 = |r| + 1 (x15), s7 = pp + 0x4000 (x23), s10 = -0x4001 (x26), s11 = pp (x27), s6 = the kind byte
   sign-extended (x22, not on case 9: `bltu a2,a1` 0x8130c jumps before 0x8132c); the cells the cases read:
   [R+0x60] = F + 0x100 (&e.body[8]), [R+0xb0] = pp + 0x4000, [R+0xc0] = pp, [R+0xe8] = vb (the shadow address of
   &pp->len, reloaded into s6), [R+0x108] = F + 0xf8 (&e.body), [R+0x118] = -0x4001, [R+0x138] = F + 0xf0 (&e);
   e = 104 zero bytes with its 13 shadow granules 0 (in scope).
   THE STATE AT J (RtPgSeg.rs_cut_J): s6 = vb, s7 = pp + 0x4000, s10 = -0x4001, s11 = pp, s9 = the cursor, s8 = what
   is left, e = Layout.ent_mem of the pod; the registers outside w6b_clob as at the entry; every byte outside w6b_wr
   as at the entry (the callees' stack below R, the spill cell [R+0x100, R+0x108) of cases 1 and 5, e). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgSteps RtPgW6aBase.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* image A's loaded segments, as RtPgSteps names them *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ======================================== the pcs ======================================== *)
Definition W6B_D1 : Z := 0x817c4.     (* jt_tgt 1 *)
Definition W6B_D4 : Z := 0x81668.     (* jt_tgt 4 *)
Definition W6B_D5 : Z := 0x81804.     (* jt_tgt 5 *)
(* case 9 is RtPgW6aBase.W6_D9 (0x81954, `bltu a2,a1` 0x8130c taken); the join is W6_J (0x81e00). The code table is
   W6_TLO .. W6_TLO + 4 * W6_TN = [0x8127c, 0x82280), which holds the four cases, their shared tails (0x81658 ..
   0x81664, 0x81994 .. 0x819b4, 0x81a2c .. 0x81b20, 0x81c04 .. 0x81c08, 0x81ce0 .. 0x81cec) and the slow blocks of
   their checks (0x82170 case 4, 0x821a0 case 1, 0x821ac case 5, 0x821d4 / 0x821e0 case 1's two byte stores). *)
(* the callees: __asan_memcpy (cases 1, 5, 9) and the strlen wrapper's trampoline (case 1) *)
Definition W6B_MEMCPY : Z := 0x51860.
Definition W6B_STRLEN : Z := 0x42194.
(* the image's data the cases read: ent_build.s (case 9's memcpy source, 14 bytes, .rodata) and ent_build.vocab
   (nine 8-byte pointer cells in .data.rel.ro, each the address of one vocab string in .rodata) *)
Definition W6B_S : Z := 0x21200.
Definition W6B_VOCAB : Z := 0x9bac0.
Definition w6b_vptr (i : Z) : Z :=
  nth (Z.to_nat i) [0x20fa0; 0x20fc0; 0x20fe0; 0x21000; 0x21020; 0x21040; 0x21080; 0x210a0; 0x210c0] 0.

(* the registers a case may change; the others (sp, gp, tp, s0, s1, s2, s3, s4, s5 among them) are kept. s6, s7, s10
   and s11 are changed and reloaded: their values at J are in w6b_J_R. *)
Definition w6b_clob : list (bv 5) :=
  [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
(* the bytes a case may change: its callees' stack below R, the spill cell R+0x100 (cases 1 and 5) and e *)
Definition w6b_wr (R F : Z) : Z -> Prop :=
  fun a => (R - T_SEG_STK <= a < R) \/ (R + 0x100 <= a < R + 0x108) \/ (F + 0xf0 <= a < F + 0x158).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation u8s l := (map (fun x : byte => bv_unsigned x) l).

(* ===================== the state at a case entry =====================
   kd is the kind byte, c the cursor after it, r the input after it. The context is RtPgW6aBase.w6_ctx (the harness's
   journal, the real frame [R, R + 0x1e0) in the journal's stack window, F the side-stack frame (3, pos), rom_view);
   the input is RtPgW6aBase.w6_in with its shadow hull (the memcpy of case 5 copies from it) and its distance from the
   frame's objects [F+0x20, F+0x158) (RtPgImgA hi_w1; case 5 copies into e). *)
Definition w6b_in (W : world rsegs) (memc : word -> option byte) (regs : bvmap 5 word) (R F c vb pp kd : Z)
(r : list byte) : Prop :=
getr regs 2 = w64 R /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 9 = w64 R /\ getr regs 18 = w64 SHADOW_OFF /\
getr regs 25 = w64 c /\ getr regs 14 = w64 (c - 1) /\ getr regs 24 = w64 (Z.of_nat (length r)) /\
getr regs 15 = w64 (Z.of_nat (length r) + 1) /\
getr regs 23 = w64 (pp + 0x4000) /\ getr regs 27 = w64 pp /\ getr regs 26 = w64 (-0x4001) /\
(kd mod 10 <> 9 -> getr regs 22 = w64 (kd - 256 * (kd / 128))) /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x60) 8 (F + 0x100) /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xb0) 8 (pp + 0x4000) /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xc0) 8 pp /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe8) 8 vb /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 (F + 0xf8) /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 (-0x4001 mod 2 ^ 64) /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 (F + 0xf0) /\
0 <= vb < 2 ^ 64 /\ 0 <= kd < 256 /\ 4096 <= pp /\ pp + 0x4000 < 2 ^ 64 /\
4096 <= F /\ F + 512 <= alloc_ceiling /\ F mod 32 = 0 /\ in_app F 512 /\
(forall i, 0 <= i < 104 -> mbyte rsegs (mrestrict (w_H W) memc) (F + 0xf0 + i) = Some (Z_to_bv 8 0)) /\
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (F + 0xf0) 104 /\
shadow_hull_vis (aview rsegs (w_H W) memc) (F + 0xf0) 104 /\
0 < c - 1 /\ w6_in W memc R c r /\
(0 < Z.of_nat (length r) -> shadow_hull_vis (aview rsegs (w_H W) memc) c (Z.of_nat (length r))) /\
(forall a, c <= a < c + Z.of_nat (length r) -> ~ (F + 0x20 <= a < F + 0x158)).

(* ===================== the state at J =====================
   rr = the kind byte :: r is the turn's input; (ed, r') = ent_build rr. *)
Definition w6b_J_R (R F c vb pp : Z) (r rr : list byte) : world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop :=
fun W2 regs2 mem2 =>
getr regs2 22 = w64 vb /\ getr regs2 23 = w64 (pp + 0x4000) /\ getr regs2 26 = w64 (-0x4001) /\
getr regs2 27 = w64 pp /\
getr regs2 25 = w64 (c + Z.of_nat (length r) - Z.of_nat (length (snd (ent_build rr)))) /\
getr regs2 24 = w64 (Z.of_nat (length (snd (ent_build rr)))) /\
garr8 rsegs (mrestrict (w_H W2) mem2) (F + 0xf0) (u8s (ent_mem (fst (ent_build rr)))).

(* ===================== the case block =====================
   P picks the case by kind % 10; X is what the case reads of the image besides the code. *)
Definition w6b_case_stmt (pc : Z) (P : Z -> Prop) (X : world rsegs -> (word -> option byte) -> Prop) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos c vb pp : Z)
  (b : byte) (r : list byte),
w6_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
P (bv_unsigned b) ->
w6b_in W memc regs R F c vb pp (bv_unsigned b) r ->
X W memc ->
SRr rsegs W (cfg_at rsegs pc regs memc mdc)
(rts_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6_J w6b_clob (w6b_wr R F)
  (w6b_J_R R F c vb pp r (b :: r))).

(* case 9 reads ent_build.s (a registered global of 14 bytes, the text "reac.cfg.rate" and its NUL) *)
Definition w6b_s_ok (W : world rsegs) (memc : word -> option byte) : Prop :=
rt_cstr rsegs (w_H W) memc W6B_S (u8s S9).
(* case 1 reads vocab[i] (the registered table of 72 bytes) and the string it points to *)
Definition w6b_vocab_ok (W : world rsegs) (memc : word -> option byte) : Prop :=
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF W6B_VOCAB 72 /\
(forall i, 0 <= i < 9 ->
  val_mem rsegs (mrestrict (w_H W) memc) (W6B_VOCAB + 8 * i) 8 (w6b_vptr i) /\
  rt_cstr rsegs (w_H W) memc (w6b_vptr i) (u8s (nth (Z.to_nat i) vocab []))).

Definition w6b_c4_stmt : Prop := w6b_case_stmt W6B_D4 (fun kd => kd mod 10 = 4) (fun _ _ => True).
Definition w6b_c5_stmt : Prop := w6b_case_stmt W6B_D5 (fun kd => kd mod 10 = 5) (fun _ _ => True).
Definition w6b_c9_stmt : Prop := w6b_case_stmt W6_D9 (fun kd => kd mod 10 = 9) w6b_s_ok.
Definition w6b_c1_stmt : Prop := w6b_case_stmt W6B_D1 (fun kd => kd mod 10 = 1) w6b_vocab_ok.

End d.
End b.
