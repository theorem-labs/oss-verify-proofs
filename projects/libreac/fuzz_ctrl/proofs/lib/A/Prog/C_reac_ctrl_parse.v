(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* reac_ctrl_parse (0x83578) of fuzz_ctrl's ASan build (image A, libreac v1.9.0): its contract, in the caller-journal
   form (it writes the caller's `struct reac_ctrl_parsed` when o <> 0).  The function takes a side-stack frame of
   class 1, calls __asan_memset once, __asan_memcpy twice, the bcmp wrapper (through
   __interceptor_trampoline_bcmp) once and kind_of_link1 once; the return code and the 36 bytes it writes are the
   model `ctrlparse` (lib/Prog/RcParse.v).  Port of fuzz_grant's lib/A/Prog/CtrlParse.v.
   STATEMENTS ONLY: this file holds the Definitions three other lanes cite.  The walk `pb_reac_ctrl_parse` and the
   Section hypotheses it needs (AR_laws, PALib, the intrinsic realizers, the .str.4 globals) live in the proof file
   and are not stated here. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import APostBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import PaTable CtrlList CtrlPa CtrlImg.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcParse.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.
(* The concrete image instance: `pa_segs PI_ctrl` reduces to `tfibsegs` (CtrlImg.v:82-83), so every SEGS of this
   statement is written `tfibsegs` (AB1v.v:11) and CtrlCallerJ's tcj_* lemmas apply unchanged. *)
#[local] Notation VAL := (@pa_val _ ctrl_listing PI_ctrl).
#[local] Notation BASE := (@pa_val _ ctrl_listing PI_ctrl A_TEXT).
(* The entry slot of reac_ctrl_parse on the position-abstract listing (AF_reac_ctrl_parse = 0x269c, CtrlList.v:17). *)
Definition A_reac_ctrl_parseP : Z := BASE + AF_reac_ctrl_parse.
(* The machine stack the call needs: the window of the proved image-A run, REAC_CTRL_PARSE_K = 8800 of
   lib/A/Prog/reac_ctrl_parse_c.v:13 (4240 of its own frame plus the largest callee's K, the bcmp wrapper's 4560).
   The glue lifts that run's stretches, whose writes and visibility facts are all stated on [S - 8800, S), with
   bcmp INSIDE a lifted stretch, so the window is 8800 (route (a); image B's twin has the same value). Announced
   interface change of 2026-10-29 ~07:2xZ: was 160 + 2 * ESTACK = 8352, the cgif-form reading in which bcmp is
   applied by its own rule (abcmp_realizes, 2 * ESTACK); a caller now supplies 448 more bytes. *)
Definition REAC_CTRL_PARSE_STK : Z := 8800.
Section e.
Variable B : asyms.
Variables RLO RHI : Z.
Definition treac_ctrl_parse_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world tfibsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
(lyc : alayout) (Sc : astate) (W : world tfibsegs) (memc : word -> option byte) (k : Z)
(regs : bvmap 5 word) (n o : Z) (fr : list byte) : world tfibsegs -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom tfibsegs)) md2 /\
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
aregs_preserved regs regs2 /\ frames S2 = frames Sc /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
(exists ff, S2 = set_fs ff Sc) /\
getr regs2 10 = w64 (fst (ctrlparse n fr)) /\
(o <> 0 -> forall i, (i < 36)%nat ->
  aview tfibsegs (w_H W2) mem2 (o + Z.of_nat i) = Some (bv_unsigned (nth i (snd (ctrlparse n fr)) cp_z))) /\
acall_kept tfibsegs B lyc Sc W memc W2 mem2 (spZ regs - REAC_CTRL_PARSE_STK) (spZ regs) (fun a => o <= a < o + 36).
Definition treac_ctrl_parse_spec : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (f n o : Z) (fr : list byte),
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
arodata_okS tfibsegs B RLO RHI (aview tfibsegs (w_H W) memc) ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 f -> getr regs 11 = w64 n -> getr regs 12 = w64 o -> 0 <= n < 2 ^ 64 ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_CTRL_PARSE_STK -> spZ regs <= sp0 ->
count_cid 1 (frames Sc) < fs_frames 1 ->
(50 <= n -> exists Lf : Z, In (f, Lf) (ablocks B lyc Sc) /\ 50 <= req_size Lf) ->
(o <> 0 -> afobj tfibsegs B lyc Sc W memc o 36) ->
(o <> 0 -> forall a, o <= a < o + 36 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
length fr = 50%nat ->
(50 <= n -> forall i, (i < 50)%nat -> aview tfibsegs (w_H W) memc (f + Z.of_nat i) = Some (cp_v fr i)) ->
SRr tfibsegs W (cfg_at tfibsegs A_reac_ctrl_parseP regs memc mdc)
(treac_ctrl_parse_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs n o fr).
End e.
End b.
