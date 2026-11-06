(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6bBase.v at f3898085bda; for reac-pw/fuzz_headamp image A: module paths and the rl_ / rs_ prefixes renamed, every pc moved by the code's uniform shift +0xd20 over [0x80a80, 0x81af0), ent_build.vocab 0x9a500 -> 0x9c060 (its nine strings and ent_build.s at the same .rodata addresses, byte-equal), the real-frame cells by the plan's slot map (0xf8>0x118, 0xb0>0xd0, 0xf0>0x110, 0xc0>0xe0, 0x20>0x48, 0x70>0x98, 0x80>0xf0, the cursor's spill 0xc8>0x68), the frame for locals of class 4 (1024 bytes; objects [F+0x20, F+0x158)), the image strings as headamp's hd_cstr. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, same loaded bytes except .note.gnu.build-id): the BLOCK STATEMENTS of the
   walk piece "ent_build B" of LLVMFuzzerTestOneInput (0x80bc0): the cases 1, 4, 5 and 9 of ent_build's
   `switch (kind % 10)` (pod.h:285-296, 326-339, 367-377), each from its entry to the join J 0x8237c.
   Statement text only: no function is proved here (kind: segment lemma).

   ONE BLOCK PER CASE, stated in lib/A/HPgW6aBase.v's form (w6_ctx, w6_in, w6_post), so that a case is proved
   without the cut records of lib/A/HPgSeg.v and the piece is the case's block between the two cut bridges of
   lib/A/HPgEntBCut.v.
     w6b_c4  0x81b88 .. J: v = fuzz_u8 % 3 (pod.h:327-330); no byte left: 0x81ee8.
     w6b_c5  0x81d40 .. J: n = min(fuzz_u8 % 32, left), memcpy(e.body, cursor, n) at 0x81d84, the NUL unless
             kind & 0x80 (pod.h:336-337, 209-219); no byte left: 0x82068.
     w6b_c9  0x81ea4 .. J: e.type = 14, body[0..8) = 14, 8, memcpy(e.body + 8, s, 14) at 0x81ecc, e.size = 24
             (pod.h:369-375); no input read.
     w6b_c1  0x81cf8 .. J: i = fuzz_u8 % 9, the 8-byte load of vocab[i] (0x81fb8), strlen at 0x81fc0, memcpy at
             0x81fe8, the NUL, and with kind & 0x80 the two checked byte stores 'x', 0 (pod.h:286-294).
   THE STATE AT A CASE ENTRY (HPgSeg.hs_L_D, checked against the code; HPgW6aBase's header): s1 = R (x9) the real
   frame's base, sp = R, s7 = SHADOW_OFF (x23), s8 = c (x24) the cursor after the kind byte, a4 = c - 1 (x14),
   s9 = |r| (x25) what is left after it, s5 = pp + 0x4000 (x21), s11 = pp (x27), s4 = the kind byte
   sign-extended (x20, not on case 9: `bltu` 0x81838 jumps before 0x81840); [R+0x118] = |r| + 1, [R+0xd0] = vb (the
   shadow address the cases reload into s4), [R+0x110] = F + 0xf0 (&e), [R+0xe0] = F + 0xf8 (&e.body),
   [R+0x48] = F + 0x100 (&e.body[8]), [R+0x98] = pp + 0x4000, [R+0xf0] = pp; e = 104 zero bytes with its 13
   shadow granules 0 (in scope).
   THE STATE AT J (HPgSeg.hs_cut_J): s4 = vb, s9 = the cursor, s5 and s11 as at the entry, [R+0x118] = what is
   left, e = Layout.ent_mem of the pod; the registers outside w6b_clob as at the entry; every byte outside
   w6b_wr as at the entry (the callees' stack below R, R+0x68 (case 1's spill of the cursor), R+0x118, e). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgSteps HPgW6aBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ======================================== the pcs ======================================== *)
Definition W6B_D1 : Z := 0x81cf8.     (* jt_tgt 1 *)
Definition W6B_D4 : Z := 0x81b88.     (* jt_tgt 4 *)
Definition W6B_D5 : Z := 0x81d40.     (* jt_tgt 5 *)
Definition W6B_D9 : Z := 0x81ea4.     (* `bltu a2,a1` 0x81838 taken *)
(* the image's data the cases read: ent_build.s (case 9's memcpy source, 14 bytes) and ent_build.vocab (nine
   8-byte pointer cells in .data.rel.ro, each the address of one vocab string in .rodata) *)
Definition W6B_S : Z := 0x21120.
Definition W6B_VOCAB : Z := 0x9c060.
Definition w6b_vptr (i : Z) : Z :=
  nth (Z.to_nat i) [0x20ec0; 0x20ee0; 0x20f00; 0x20f20; 0x20f40; 0x20f60; 0x20fa0; 0x20fc0; 0x20fe0] 0.

(* the registers a case may change; the others (sp, gp, tp, s0, s1, s2, s3, s6, s7, s10 among them) are kept *)
Definition w6b_clob : list (bv 5) :=
  [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 20; 21; 24; 25; 27; 28; 29; 30; 31]%bv.
(* the bytes a case may change: its callees' stack below R, the cursor's spill cell R+0x68, in.n's cell R+0x118
   and e *)
Definition w6b_wr (R F : Z) : Z -> Prop :=
  fun a => (R - T_SEG_STK <= a < R) \/ (R + 0x68 <= a < R + 0x70) \/ (R + 0x118 <= a < R + 0x120) \/
           (F + 0xf0 <= a < F + 0x158).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Local Notation u8s l := (map (fun x : byte => bv_unsigned x) l).

(* ===================== the state at a case entry =====================
   kd is the kind byte, c the cursor after it, r the input after it. *)
Definition w6b_in (W : world rsegs) (memc : word -> option byte) (regs : bvmap 5 word) (R F c vb pp kd : Z)
(r : list byte) : Prop :=
getr regs 2 = w64 R /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 9 = w64 R /\ getr regs 23 = w64 SHADOW_OFF /\
getr regs 24 = w64 c /\ getr regs 14 = w64 (c - 1) /\ getr regs 25 = w64 (Z.of_nat (length r)) /\
getr regs 21 = w64 (pp + 0x4000) /\ getr regs 27 = w64 pp /\
(kd mod 10 <> 9 -> getr regs 20 = w64 (kd - 256 * (kd / 128))) /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 (Z.of_nat (length r) + 1) /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xd0) 8 vb /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x110) 8 (F + 0xf0) /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe0) 8 (F + 0xf8) /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x48) 8 (F + 0x100) /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x98) 8 (pp + 0x4000) /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf0) 8 pp /\
0 <= vb < 2 ^ 64 /\ 0 <= kd < 256 /\ 4096 <= pp /\ pp + 0x4000 < 2 ^ 64 /\
4096 <= F /\ F + 1024 <= alloc_ceiling /\ F mod 32 = 0 /\
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
getr regs2 20 = w64 vb /\ getr regs2 21 = w64 (pp + 0x4000) /\ getr regs2 27 = w64 pp /\
getr regs2 25 = w64 (c + Z.of_nat (length r) - Z.of_nat (length (snd (ent_build rr)))) /\
val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x118) 8 (Z.of_nat (length (snd (ent_build rr)))) /\
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
(w6_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6_J w6b_clob (w6b_wr R F)
  (w6b_J_R R F c vb pp r (b :: r))).

(* case 9 reads ent_build.s (a registered global of 14 bytes, the text "reac.cfg.rate" and its NUL) *)
Definition w6b_s_ok (W : world rsegs) (memc : word -> option byte) : Prop :=
hd_cstr rsegs (w_H W) memc W6B_S (u8s S9).
(* case 1 reads vocab[i] (the registered table of 72 bytes) and the string it points to *)
Definition w6b_vocab_ok (W : world rsegs) (memc : word -> option byte) : Prop :=
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF W6B_VOCAB 72 /\
(forall i, 0 <= i < 9 ->
  val_mem rsegs (mrestrict (w_H W) memc) (W6B_VOCAB + 8 * i) 8 (w6b_vptr i) /\
  hd_cstr rsegs (w_H W) memc (w6b_vptr i) (u8s (nth (Z.to_nat i) vocab []))).

Definition w6b_c4_stmt : Prop := w6b_case_stmt W6B_D4 (fun kd => kd mod 10 = 4) (fun _ _ => True).
Definition w6b_c5_stmt : Prop := w6b_case_stmt W6B_D5 (fun kd => kd mod 10 = 5) (fun _ _ => True).
Definition w6b_c9_stmt : Prop := w6b_case_stmt W6B_D9 (fun kd => kd mod 10 = 9) w6b_s_ok.
Definition w6b_c1_stmt : Prop := w6b_case_stmt W6B_D1 (fun kd => kd mod 10 = 1) w6b_vocab_ok.

End d.
End b.
