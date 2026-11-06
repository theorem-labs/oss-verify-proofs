(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 199 of its 225 lines of code are new or changed and 492 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/m_file_s_hdra_m.v; 17 of its 47 lines of code are new or changed and 195 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A, 0x85ebc), segment S_MF_LONGP (LONG 0x86110 -> TAIL 0x86cf8; guide
   MF-CUTS-A.md section 4): the one point the segment is cut at, between its two proof files (the LONGP / KKNOCKP segment lane
   of the G2 walk owner's G2).
   LK_CALLP = 0x861e4 (AF_m_file + 0x328), where both arms of the long-line code meet before m_refuse:
     - every byte of the line blank: the blank-skip loop 0x86118-0x86144 runs to the line's end (s11 = s7), `j
       0x861e0`, 0x861e0 `mv s4,a7`; 136(s1) still holds cur;
     - a non-blank byte at index i: 0x863b4-0x863dc re-check its shadow, `mv s4,a7`, cur' = NULL when the byte is
       '[' else cur (`seqz` / `addi -1` / `and`), `sd` to 136(s1) at 0x863d8, `j 0x861e4`.
   LK_CALLPX_stmt states the point with the LONG cut's facts at the LONG state's memory memc and the memory memc' at
   0x861e4, which differs from memc only in the cur slot [s1 + 136, s1 + 144), holding cur'. The model is the long
   line's m_line (plain mfp_facts.v:572-576 m_line_long): (m_refuse mcc (line + 1) false, cur') with cur' = None
   when the first non-blank byte is '[' and cur otherwise.
   m_file_s_long_l.v proves LONG from LK_CALLPX (the loop and its two exits); m_file_s_long.v proves LK_CALLPX from
   TAIL (the m_refuse call, m_file_rf.v) and closes S_MF_LONGP. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* 0x861e4: m_refuse's argument set-up after both arms of the long-line code *)
Definition LK_CALLP : Z := AF_m_file + 0x328.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.

(* 0x861e4: the LONG cut's facts at the LONG state (memc, mdc; the cur slot holding cur), the registers at 0x861e4
   (s4 = the next line's address, s5 = c, s6 = line + 1, s8 = FAKE, and mf_regs_at), the long line's model with the
   new cursor cur', and the memory memc' (model mdc') at 0x861e4: the journal reaches it, it agrees with memc off the
   cur slot, and the cur slot holds cur' *)
Definition LK_CALLPX_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur cur' : option nat) (line p : Z) (rest : list Z) memc' mdc',
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur -> mf_regs_at B v lyc pos regs1 ->
getr regs1 24 = w64 (frame_addr lyc 1 pos) ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc cur line p rest ->
(512 <= length (mf_line rest))%nat ->
(cur' = cur \/ cur' = None) ->
mf_fin (m_refuse mcc (line + 1) false, cur') line rest = mf_final v ->
getr regs1 20 = w64 (mf_next p rest) -> getr regs1 22 = w64 (line + 1) -> getr regs1 21 = w64 (mv_c v) ->
ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
  (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc memc' mdc' 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) + 136 <= a < mf_s1 (mv_sp v) + 144) ->
 rdW Wc memc' a = rdW Wc memc a) ->
val_mem SEGS (mrestrict (w_H Wc) memc') (mf_s1 (mv_sp v) + 136) 8 (mf_cur_ptr (mv_c v) cur') ->
mf_at B v Wc regs1 memc' mdc' LK_CALLP.
End e.
End f.
End d.
