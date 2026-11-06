(* seg_D4 (the model-name case of LLVMFuzzerTestOneInput's B walk, 0x812b8..0x81598): the statements of the
   pieces another hand can prove on its own. Each is a closed Prop; a Theorem Labs lane uses them by name.
   - d4h_uoff_stmt / d4h_kill_stmt / d4h_ewclob_stmt: the arithmetic of the engine's branch conditions and of an
     atom's value after a call havoc (lib/Reusable/YP0m.v, YP0e.v, YI04.v, YN3v.v). No image, no walk.
   - d4h_block_read_stmt / d4h_frame_read_stmt: the four read premises the wrappers ask (src_ok, amem_range,
     range_addressable, shadow_hull_vis) for a sub-range of a heap block and of a class-4 side-stack frame.
   A hand proves `Lemma <name> : <stmt>` in its own file lib/B/Prog/LLVMFuzzerTestOneInput_seg_D4_hand_<part>.v
   and the lane Requires that file. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The unsigned value of an atom's offset. *)
Definition d4h_uoff_stmt : Prop :=
forall (E : env) (n : nat) (c v : Z), ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
U E (SOff n c) = v + c.
(* A branch condition over two symbolic values with known unsigned values. *)
Definition d4h_kill_stmt : Prop :=
forall (E : env) (a b : sv) (va vb : Z), U E a = va -> U E b = vb ->
branch_taken BC_NE (sv_denot E a) (sv_denot E b) = negb (va =? vb) /\
branch_taken BC_EQ (sv_denot E a) (sv_denot E b) = (va =? vb) /\
branch_taken BC_LTU (sv_denot E a) (sv_denot E b) = (va <? vb) /\
branch_taken BC_GEU (sv_denot E a) (sv_denot E b) = negb (va <? vb).
(* The value a caller-saved register's fresh atom has after a call (YI04.v CLOB, YN3v.v havoc). *)
Definition d4h_ewclob_stmt : Prop :=
forall (E : env) (K j : nat) (regs : bvmap 5 word) (r : bv 5) (v : Z),
(j < length CLOB)%nat -> nth j CLOB 0%bv = r -> getr regs r = Z_to_bv 64 v ->
ew (havoc E K (map (getr regs) CLOB)) (K + j)%nat = Z_to_bv 64 v.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
Section c.
Variable B : asyms.

(* The four read premises of the wrappers for m bytes inside a heap block. *)
Definition d4h_block_read_stmt : Prop :=
AR_laws SEGS B ->
forall ly S (W : world SEGS) mem md (regs : bvmap 5 word) p n a m,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p <= a -> a + m <= p + n -> 0 <= m ->
(forall b, a <= b < a + m -> aview SEGS (w_H W) mem b <> None) ->
(forall b, a <= b < a + m -> ~ (spZ regs - 2 * ESTACK <= b < spZ regs)) ->
src_ok SEGS W regs mem a m /\ amem_range a m /\
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a m /\
(0 < m -> shadow_hull_vis (aview SEGS (w_H W) mem) a m).

(* The same for m bytes inside a side-stack frame, whose shadow the caller supplies. *)
Definition d4h_frame_read_stmt : Prop :=
AR_laws SEGS B ->
forall ly S (W : world SEGS) mem md (regs : bvmap 5 word) cid pos a m,
AR SEGS B ly S W mem md -> In (cid, pos) (frames S) -> 0 <= cid ->
frame_addr ly cid pos <= a -> a + m <= frame_addr ly cid pos + fs_frame_bytes cid -> 0 <= m ->
(forall b, a <= b < a + m -> aview SEGS (w_H W) mem b <> None) ->
(forall b, a <= b < a + m -> ~ (spZ regs - 2 * ESTACK <= b < spZ regs)) ->
src_ok SEGS W regs mem a m /\ amem_range a m /\
(0 < m -> shadow_hull_vis (aview SEGS (w_H W) mem) a m).

End c.
End b.
End a.
