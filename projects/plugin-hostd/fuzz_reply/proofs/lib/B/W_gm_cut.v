(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the cut points of fuzz_reply's gesture_model walk on image B (asan-ubsan), lane
   W4, in the form of lib/A/W_gm_scan.v / lib/A/W_gm_found.v (A's proved cut lemmas gm_scan, gm_found) and the cgif
   loop walks of proofs/cgif/cgif_file_fuzzer/lib/A/AC8b.v.  A NEW WALK, not a relocation: B tests the scan loop at
   its top, decrements before the compare, and inserts UBSan trap branches to `unimp` (0x8621c).  FROZEN interface
   once pushed: change it only through lane W4's owner. *)
(* Modified by Theorem Labs, 2026-10: the meter texts of gm_scan_at and gm_found_at at the KF-COUNT kit's gm_cost H ln
   (statements only) *)
(* gesture_model (s, line, len) at 0x86048 on fuzz_reply.asan-ubsan (frame 48: ra, s0..s3 at sp+40 .. sp+8):
     0x86048-0x86060  prologue; s0 = line.
     0x86068          len < 14 -> 0x861bc (return).
     0x8606c-0x86090  s2 = len, s1 = s, s3 = SB (the GOT slot 0x9df50 holds the shadow cell), bcmp (line,
                      "param_gesture", 13) at 0x86090; != 0 -> 0x861bc.
     0x86098          TRAP `beqz s0` (line null) -> unimp; refuted by 4096 <= LINE.
     0x860a0          TRAP `bgeu s0, -13` (line + 13 wraps) -> unimp; refuted by LINE <= 140737479966720.
     0x860a4-0x860c0  line[13]'s load1 check, a3 = 32, line[13] != ' ' -> 0x861bc.
     0x860c4-0x860d4  a0 = 0 (j), a1 = ~line, a4 = -len, a2 = line + len, a5 = line + len - 1.
     0x860d8          LOOP HEAD (gm_scan_at): a6 = len + j, `beqz a6` -> 0x861bc; TRAP `bltu a4, s0` (line + len
                      wraps) -> unimp, refuted by LINE + len <= 140737479966720; line[len+j-1]'s load1 check, read it,
                      j -= 1; != ' ' -> 0x860d8, else `j 0x8611c`.
     0x8611c          FOUND (gm_found_at): s2 = len + j (the last space's index js); == 13 -> 0x861bc; TRAP
                      `bltu a1, s2 + 1` (line + js + 1 wraps) -> unimp, refuted by LINE + len <= 140737479966720;
                      a0 = line + js + 1 (the word), its length -j-1 = len - js - 1 against 3 / 5, bcmp with "end" (3)
                      / "begin" (5); TRAPS 0x86164 / 0x861dc `andi s1,7; bnez` (s misaligned) -> unimp, refuted by
                      HA mod 8 = 0; list_find at 0x86178 / 0x861f0; tail list_push 0x861a4 / tail list_drop 0x86218.
     0x861bc          epilogue, ret.
   The pieces are proved in a Section with exactly the hypotheses of lib/A/W_gesture_model.v (LAWS TL HG MTL ABCMP
   LFIND LPUSH LDROP HLITG HLITB HLITE HLITV, at B's kit); the scan piece additionally takes
   GMFOUND : gm_found_at B MT MMAX G (BASE + A_gm_found), and the composition GMSCAN : gm_scan_at ... (BASE + A_gm_loop).
   Both statements carry gm_spec's premise list (lib/B/W_contract.v) verbatim, then the facts the B traps test, then
   the machine state at the cut: B's register map is A's (s0 = LINE, s1 = HA, s2 = len, s3 = SB) and so is the frame
   (ra, s0, s1, s2, s3 of the caller at sp-8 .. sp-40 of the entry sp).
   PROBE (the entry walk of W_gesture_model.v, printed): the sstate at 0x860d8 is a0 = SLit 0,
   a1 = SAlu XOR (SOff 11 0) (SLit -1), a2 = SAlu ADD (SOff 11 0) (SOff 12 0), a3 = SLit 32,
   a4 = SAlu SUB (SLit 0) (SOff 12 0), a5 = SAlu ADD (SOff 11 -1) (SOff 12 0), s0 = SOff 11 0 (LINE), s1 = SOff 10 0
   (HA), s2 = SOff 12 0 (len), s3 = SOff 32 0 (SB), the frame region [sp-48, sp) with chunks ra, s0..s3 at -8 .. -40;
   from there the runner stops at 0x860dc `beqz a6` (SR_branch BC_EQ (SOff 12 0) (SLit 0)).  The body 0x860d8 ..
   0x86108 writes only a0 (j -= 1), a6, a7, t0, so the state at 0x8611c is the loop head's with a0 = js - len. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_contract W_rep W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Definition A_gesture_model : Z := AF_fr_gesture_model.     (* 0x86048 *)
Definition A_gesture_modelP : Z := BASE + A_gesture_model.
Definition A_gm_loop : Z := A_gesture_model + 0x90.        (* 0x860d8: the scan loop's head *)
Definition A_gm_found : Z := A_gesture_model + 0xd4.       (* 0x8611c: the last space found *)
Definition A_gm_ret : Z := A_gesture_model + 0x174.        (* 0x861bc: the shared epilogue *)
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable G : list (Z * Z).

(* LOOP HEAD 0x860d8: the bytes line[len+j .. len-1] are not spaces, 14 <= len + j, j <= 0;
   a0 = j, a1 = ~line, a2 = line + len, a3 = ' ', a4 = -len, a5 = line + len - 1. *)
Definition gm_scan_at (pc : Z) : Prop :=
forall W ly S regs mem md ch HA LINE (ln : list byte) H q k (j : Z) regsc memc mdc,
afn_pre SEGS B GM_STK ly S W regs mem md ch ->
getr regs 10 = w64 HA -> getr regs 11 = w64 LINE -> getr regs 12 = w64 (Z.of_nat (length ln)) ->
alist_at B ly S W mem (HA + 80) H true -> NoDup (texts H) ->
(forall a, HA + 80 <= a < HA + 96 -> inG G a) -> azs B (HA + 80) 16 ->
(HA + 80) mod 8 = 0 ->
garr8 SEGS (arm W mem) LINE (bzs ln) -> ~ In (Z_to_bv 8 0) ln -> Z.of_nat (length ln) <= APARTIAL ->
In (q, k) (ablocks B ly S) -> ~ In (q, k) (list_blks H) -> q <= LINE ->
LINE + Z.of_nat (length ln) <= q + req_size k ->
garr8 SEGS (arm W mem) (VAL A_lit_gesture) RelayModel.K_GESTURE ->
garr8 SEGS (arm W mem) (VAL A_lit_begin) RelayModel.W_BEGIN ->
garr8 SEGS (arm W mem) (VAL A_lit_end) RelayModel.W_END ->
rom_view SEGS W mem ->
(lp_grow H = true -> lp_vbytes H < MMAX) -> AREC * hl_cap H < 2 ^ 32 ->
blocks_bytes S + (if lp_grow H then lp_vbytes H else 0) + (Z.of_nat (length ln) + 1) <= LIVE_MAX ->
mo_ok MT S (gm_cost MT H ln) ->
firstn 13 (bzs ln) = RelayModel.K_GESTURE ->
nth 13 (bzs ln) 0 = RelayModel.SPACE ->
(* the facts B's UBSan traps test (each follows from the premises above; stated for the pieces) *)
4096 <= LINE -> LINE + Z.of_nat (length ln) <= 140737479966720 -> HA mod 8 = 0 ->
(* the machine state at the cut *)
spZ regsc = spZ regs - GM_FRAME ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 8 = w64 LINE -> getr regsc 9 = w64 HA ->
getr regsc 18 = w64 (Z.of_nat (length ln)) -> getr regsc 19 = w64 SB ->
(forall r, acallee_saved r -> 20 <= r <= 27 -> getr regsc (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
val_mem SEGS (arm W memc) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
val_mem SEGS (arm W memc) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) ->
val_mem SEGS (arm W memc) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
val_mem SEGS (arm W memc) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
val_mem SEGS (arm W memc) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
 aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) memc a) ->
@ajournal_gx _ SK SEGS B G 0 [] GM_STK (spZ regs) (blk_FP (list_blks H))
 ly S W mem md [] ly S W memc mdc 0 ->
getr regsc 10 = w64 j -> getr regsc 11 = w64 (2 ^ 64 - 1 - LINE) ->
getr regsc 12 = w64 (LINE + Z.of_nat (length ln)) -> getr regsc 13 = w64 32 ->
getr regsc 14 = w64 (2 ^ 64 - Z.of_nat (length ln)) ->
getr regsc 15 = w64 (LINE + Z.of_nat (length ln) - 1) ->
14 <= Z.of_nat (length ln) -> 13 < Z.of_nat (length ln) + j -> j <= 0 ->
(forall t, Z.of_nat (length ln) + j <= t < Z.of_nat (length ln) ->
 nth (Z.to_nat t) (bzs ln) 0 <> RelayModel.SPACE) ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 pc) memc (seg_rom SEGS)) mdc)
(gm_post B MT G regs ly S W mem md HA H ln).

(* FOUND 0x8611c: js is the index of the line's LAST space (13 <= js < len); a0 = js - len (the decremented j),
   a1 = ~line, a2 = line + len. *)
Definition gm_found_at (pc : Z) : Prop :=
forall W ly S regs mem md ch HA LINE (ln : list byte) H q k (js : Z) regsc memc mdc,
afn_pre SEGS B GM_STK ly S W regs mem md ch ->
getr regs 10 = w64 HA -> getr regs 11 = w64 LINE -> getr regs 12 = w64 (Z.of_nat (length ln)) ->
alist_at B ly S W mem (HA + 80) H true -> NoDup (texts H) ->
(forall a, HA + 80 <= a < HA + 96 -> inG G a) -> azs B (HA + 80) 16 ->
(HA + 80) mod 8 = 0 ->
garr8 SEGS (arm W mem) LINE (bzs ln) -> ~ In (Z_to_bv 8 0) ln -> Z.of_nat (length ln) <= APARTIAL ->
In (q, k) (ablocks B ly S) -> ~ In (q, k) (list_blks H) -> q <= LINE ->
LINE + Z.of_nat (length ln) <= q + req_size k ->
garr8 SEGS (arm W mem) (VAL A_lit_gesture) RelayModel.K_GESTURE ->
garr8 SEGS (arm W mem) (VAL A_lit_begin) RelayModel.W_BEGIN ->
garr8 SEGS (arm W mem) (VAL A_lit_end) RelayModel.W_END ->
rom_view SEGS W mem ->
(lp_grow H = true -> lp_vbytes H < MMAX) -> AREC * hl_cap H < 2 ^ 32 ->
blocks_bytes S + (if lp_grow H then lp_vbytes H else 0) + (Z.of_nat (length ln) + 1) <= LIVE_MAX ->
mo_ok MT S (gm_cost MT H ln) ->
firstn 13 (bzs ln) = RelayModel.K_GESTURE ->
nth 13 (bzs ln) 0 = RelayModel.SPACE ->
4096 <= LINE -> LINE + Z.of_nat (length ln) <= 140737479966720 -> HA mod 8 = 0 ->
spZ regsc = spZ regs - GM_FRAME ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 8 = w64 LINE -> getr regsc 9 = w64 HA ->
getr regsc 18 = w64 (Z.of_nat (length ln)) -> getr regsc 19 = w64 SB ->
(forall r, acallee_saved r -> 20 <= r <= 27 -> getr regsc (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
val_mem SEGS (arm W memc) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
val_mem SEGS (arm W memc) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) ->
val_mem SEGS (arm W memc) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
val_mem SEGS (arm W memc) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
val_mem SEGS (arm W memc) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
 aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) memc a) ->
@ajournal_gx _ SK SEGS B G 0 [] GM_STK (spZ regs) (blk_FP (list_blks H))
 ly S W mem md [] ly S W memc mdc 0 ->
RelayModel.last_space_from 0 (bzs ln) = Some (Z.to_nat js) ->
13 <= js < Z.of_nat (length ln) ->
getr regsc 10 = w64 (js - Z.of_nat (length ln)) -> getr regsc 11 = w64 (2 ^ 64 - 1 - LINE) ->
getr regsc 12 = w64 (LINE + Z.of_nat (length ln)) ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 pc) memc (seg_rom SEGS)) mdc)
(gm_post B MT G regs ly S W mem md HA H ln).

(* The arithmetic the pieces share: the trap facts from gm_spec's premises, and the bv forms of ~line and -len. *)
Lemma gm_ha8 : forall HA, (HA + 80) mod 8 = 0 -> HA mod 8 = 0.
Proof.
intros HA H. replace (HA + 80) with (HA + 10 * 8) in H by lia.
rewrite Z.mod_add in H by lia. exact H.
Qed.
Lemma gm_not_line : forall LINE, 0 <= LINE < 2 ^ 64 ->
bv_unsigned (w64 (2 ^ 64 - 1 - LINE)) = 2 ^ 64 - 1 - LINE.
Proof. intros LINE H. unfold w64. apply unsigned_lit_small. lia. Qed.
Lemma gm_neg_len : forall LEN, 0 < LEN < 2 ^ 64 ->
bv_unsigned (w64 (2 ^ 64 - LEN)) = 2 ^ 64 - LEN.
Proof. intros LEN H. unfold w64. apply unsigned_lit_small. lia. Qed.
End c.
End b.
End a.
