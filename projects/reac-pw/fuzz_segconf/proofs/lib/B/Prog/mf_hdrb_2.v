(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 147 of its 168 lines of code are new or changed and 497 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3; 0x86140), the segment S_MF_HDRB (HFIND 0x865c0 ->
   TAIL 0x86820, 113 owned instructions, 7 instrumented checks, 4 UBSan trap branches, 4 calls; the image-B m_file cut map section 4 and the image-B m_file segment table section 5): the points INSIDE the segment where the walk is
   cut, and the statement at each. Statement text only: no instruction is executed here. A walk lane of
   the image-B m_file-family owner's G2B. ADAPTED from image A's lib/A/Prog/m_file_s_hdrb_2.v (the image-A m_file-family lane,
   commit d8beabc2758c): the same cut kinds (the returns of the calls, the not-found arm, the
   new entry, the join) at image B's pcs, registers and frame cells (the image-B m_file cut map table C.1).
   The files of the segment:
     mf_hdrb_1.v  the model, byte-encoding, reader and footprint facts (image A's m_file_s_hdrb_1.v)
     mf_hdrb_2.v  THIS FILE: the inner cut points and their statements
     mf_hdrb_3.v  the callee premises (m_find's, the checked memset's and memcpy's) at a mid-segment state
     mf_hdrb_4.v  the model step of each path and what the tail's mf_loop needs
     mf_hdrb_5.v  the join and the short returns (JOIN -> TAIL, RREF1 -> JOIN, RMCPY -> JOIN, RREF2 -> TAIL)
     mf_hdrb_6.v  the checked memcpy of a new entry's name (RMSET -> RMCPY)
     mf_hdrb_7.v  the new entry's own code: c->n = n + 1, the traps 0x86b68 / 0x86b74, the checked memset (NEWE ->
                  RMSET)
     mf_hdrb_8.v  the not-found arm: c->n read, the test against 32, the overflow refusal (NFIND -> RREF2, NEWE)
     mf_hdrb_9.v  the found arm: the trap 0x865d4, g->gen and c->gen read, the gen test, m_refuse (RFIND -> JOIN,
                  RREF1, NFIND)
     mf_hdrb.v    the m_find call (HFIND -> RFIND) and `S_MF_HDRB_ok : S_MF_HDRB B`

   WHAT THE SEGMENT DOES (the neutral listing of m_file in image B, B.s line = (pc - 0x86140) / 4 + 2):
     0x865c0 a0 = s9 = c, a2 = s10 = |name| (a1 = the name since 0x865a8); 0x865c8 `jal m_find`.
     0x865cc `beqz a0, 0x86b04`: m_find's result.            [RFIND]
     FOUND (a0 = g = &c->seg[i]): 0x865d0 `andi a1,a0,3`, 0x865d4 `bnez` to the `unimp` 0x86e84 (the UBSan
       alignment trap of g->gen; g = c + 256 i with c mod 16 = 0, so not taken); s5 = g; the instrumented check of
       the 4-byte load of g->gen (a load of the shadow byte at ((g + 252) >> 3) + the shadow base and a compare,
       0x865e8; the slow path 0x86d24-0x86d30 and the error path, a call of errpath_load4 at 0x86f30, which the
       proof shows is not reached), the check of c->gen (the shadow byte address kept in 104(s1), 0x865f4; slow
       path 0x86d34-0x86d44, error path 0x86f34-0x86f38), the loads 0x865f8 (g->gen) and 0x86604 (c->gen, via
       56(s1)); 0x86608 `bne`: other gen goes to the join 0x86ba0; equal: 0x86614 `jal m_refuse(c, line + 1)`,
       back at 0x86618 `j 0x86ba0`.                               [RREF1 = 0x86618]
     NOT FOUND (a0 = 0) 0x86b04: the check of c->n (shadow byte at ((c + 0x2000) >> 3) + the shadow base, from
       s6 = c + 0x2000; slow path 0x86d58-0x86d64, error path 0x86f40-0x86f44), a3 = 32, the load 0x86b18 of n,
       0x86b1c `blt a0,a3`.                                         [NFIND = 0x86b04]
       n >= 32 (so n = 32): 0x86b20-0x86b3c the check, the load and the store of c->overflow (overflow + 1, via
         24(s1) = c + 0x2004; the store reuses the load's check); then the shared refusal block 0x86b40 `jal
         m_refuse(c, line + 1)` 0x86b48, back at 0x86b4c `sd zero,136(s1)` (cur = NULL), `j 0x867e4` (s10 =
         152(s1), `j` TAIL).                                       [RREF2 = 0x86b4c]
       n < 32 (0x86b54): the check of the store to c->n (the shadow byte address formed at 0x86b04-0x86b08, still
         in a1; slow path 0x86d78-0x86d84, error path 0x86f4c-0x86f50), c->n = n + 1 (0x86b60), 0x86b68 `bgeu
         a0,a1` (a1 = 33) to the `unimp` (the UBSan bound of c->seg[n]; 0 <= n < 32, not taken), a0 = 256 n,
         a1 = 16(s1) = ~c, 0x86b74 `bltu a1,a0` to the `unimp` (the UBSan pointer overflow of c + 256 n; c + 9236
         <= 2^64, not taken), s5 = g = c + 256 n, 0x86b88 `jal checked_memset(g, 0, 256)`. [NEWE = 0x86b54]
       back at 0x86b8c: a1 = 192(s1) = the name, a0 = s5, a2 = s10, 0x86b98 `jal checked_memcpy(g, name, |name|)`.
                                                                    [RMSET = 0x86b8c]
       back at 0x86b9c: s4 = 511, into the join.                    [RMCPY = 0x86b9c]
     JOIN 0x86ba0: `andi a0,s5,3`, 0x86ba4 `bnez` to the `unimp` (the alignment trap of g->gen; g = c + 256 i, not
       taken); the check of c->gen (104(s1), 0x86bac; slow path 0x86d00-0x86d10, error path 0x86f24-0x86f28);
       0x86bb4 cur = g (136(s1)); the check of the store g->gen (0x86bc4; slow path 0x86d14-0x86d20, error path
       0x86f2c); the load of c->gen (via 56(s1)), 0x86bd4 g->gen = c->gen; 0x86bd8 `j 0x867e4` (s10 = 152(s1),
       `j` TAIL 0x86820).                                           [JOIN = 0x86ba0]

   THE MODEL (SegModel, through m_file_m.v's mh_find): the segment computes mh_find mcc nm (line + 1) from the
   model mcc the block holds at HFIND; each path ends at the tail with that pair in the block and in 136(s1). The
   four paths are mf_hdrb_1.v's hb_mh_find_ne / hb_mh_find_eq (found), hb_mh_find_full (overflow) and
   hb_mh_find_new (the new entry).

   WHY THE CUT POINTS ARE WHERE THEY ARE: at RFIND, RREF1, RREF2, RMSET and RMCPY a call has just returned, so the
   walk re-seeds its symbolic state there anyway (m_file_sd.v's mf_seed). NFIND and NEWE split the not-found arm
   at its branch; NEWE carries the shadow byte address of c->n that the code formed at 0x86b04-0x86b08 (a1), in
   the shape the code formed it, because the check at 0x86b54 reads it. JOIN is the meeting point of three paths.

   THE MODEL AT A CUT (as image A's): mf_loop of the model mc0 the segment STARTED from (its text facts are over the
   CURRENT reader), and of the model mcc the block holds NOW only hb_mod: the cursor names an entry, n_kept has
   not gone below the entry's, and refused / overflow have gone up by at most one.
   IMAGE B'S DIFFERENCES FROM IMAGE A'S STATEMENTS: the registers (the image-B m_file cut map table C.1: c in s9, line + 1 in
   s11, 511 in s4, the name's length in s10, g in s5); the name is in 192(s1) after m_find (the memcpy reloads it
   at 0x86b8c), not in a register; the join stores cur = g itself (0x86bb4), so the cut points before it carry the
   head's cursor cur0 in 136(s1) (with hb_mod's mf_cur_ok of the current model) and g in s5; a RFIND cut (image A
   names the point and states nothing there). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_find_c m_refuse_c m_file_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ============================== the cut points inside the segment ==============================
   listing offset = AF_m_file + (pc - 0x86140), the offset the listing prints as `m_file+0x...` *)
(* 0x865cc, m_find returned: a0 is its result *)
Definition MFB_RFIND : Z := AF_m_file + 0x48c.
(* 0x86618, m_refuse returned on the found path (g->gen was c->gen): `j 0x86ba0` *)
Definition MFB_RREF1 : Z := AF_m_file + 0x4d8.
(* 0x86b04, m_find found nothing: the check and the load of c->n, the test against 32 *)
Definition MFB_NFIND : Z := AF_m_file + 0x9c4.
(* 0x86b4c, m_refuse returned on the overflow path (c->n was 32) *)
Definition MFB_RREF2 : Z := AF_m_file + 0xa0c.
(* 0x86b54, the new entry's own code (c->n was below 32) *)
Definition MFB_NEWE : Z := AF_m_file + 0xa14.
(* 0x86b8c, the checked memset of the new entry returned *)
Definition MFB_RMSET : Z := AF_m_file + 0xa4c.
(* 0x86b9c, the checked memcpy of its name returned *)
Definition MFB_RMCPY : Z := AF_m_file + 0xa5c.
(* 0x86ba0, the join of the three paths: cur = g, g->gen = c->gen, then the tail *)
Definition MFB_JOIN : Z := AF_m_file + 0xa60.

(* ===================================== what a cut carries =====================================
   the name the header named (MF_HFIND_stmt's three premises on nm, as one Prop; image A's hb_nm) *)
Definition hb_nm (rest : list Z) (o : nat) (nm : list Z) : Prop :=
(0 < length nm < 16)%nat /\ (o + length nm <= length (mf_line rest))%nat /\
firstn (length nm) (skipn o rest) = nm.
(* of the model mcc the block holds at a cut, against the model mc0 of the cut HFIND: the cursor names an entry,
   n_kept has not gone below the call's, and refused / overflow have gone up by at most one (this segment calls
   m_refuse at most once and raises overflow at most once). It is what the tail's mf_loop needs, because the text
   left at the tail is shorter by at least one byte. (Image A's hb_mod.) *)
Definition hb_mod (k0 : nat) (mc0 mcc : mconf) (cur : option nat) : Prop :=
mf_cur_ok mcc cur /\ (k0 <= length (mc_kept mcc))%nat /\
mc_refused mcc <= mc_refused mc0 + 1 /\ mc_overflow mcc <= mc_overflow mc0 + 1.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.

(* 0x86ba0, the join: the block holds mcc, s5 = g = &c->seg[i], 136(s1) still holds the head's cursor cur0
   (mf_cur_ok of mcc by hb_mod), s4 = 511, s11 = line + 1; what is left of the line is cur = g and the store
   g->gen = c->gen, which takes the model to m_upd mcc i (ms_with_gen (mc_gen mcc)) and the cursor to Some i.
   Reached from the found path (directly from 0x86608, or through m_refuse and RREF1) and from the new entry
   (RMCPY). *)
Definition MFB_JOIN_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mc0 mcc : mconf) (cur0 : option nat) (line p : Z) (rest : list Z) (i : nat),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur0 ->
mf_regs_at B v lyc pos regs1 ->
(length rest <= n)%nat -> rest <> [] ->
mf_loop v Wc memc mc0 cur0 line p rest -> hb_mod (mv_k0 v) mc0 mcc cur0 -> (i < length (mc_seg mcc))%nat ->
mf_fin (m_upd mcc i (ms_with_gen (mc_gen mcc)), Some i) line rest = mf_final v ->
getr regs1 21 = w64 (seg_spec.mseg_addr (mv_c v) i) -> getr regs1 20 = w64 511 ->
getr regs1 27 = w64 (line + 1) -> mf_np v memc Wc (mf_next p rest) ->
mf_at B v Wc regs1 memc mdc MFB_JOIN.

(* 0x86618, back from m_refuse on the found path: as the join (m_refuse keeps s4, s5, s11), one `j` before it *)
Definition MFB_RREF1_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mc0 mcc : mconf) (cur0 : option nat) (line p : Z) (rest : list Z) (i : nat),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur0 ->
mf_regs_at B v lyc pos regs1 ->
(length rest <= n)%nat -> rest <> [] ->
mf_loop v Wc memc mc0 cur0 line p rest -> hb_mod (mv_k0 v) mc0 mcc cur0 -> (i < length (mc_seg mcc))%nat ->
mf_fin (m_upd mcc i (ms_with_gen (mc_gen mcc)), Some i) line rest = mf_final v ->
getr regs1 21 = w64 (seg_spec.mseg_addr (mv_c v) i) -> getr regs1 20 = w64 511 ->
getr regs1 27 = w64 (line + 1) -> mf_np v memc Wc (mf_next p rest) ->
mf_at B v Wc regs1 memc mdc MFB_RREF1.

(* 0x86b9c, back from the checked memcpy of the name: the block holds the new entry with its name (mcc), s5 = g;
   the one instruction left before the join is s4 = 511 *)
Definition MFB_RMCPY_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mc0 mcc : mconf) (cur0 : option nat) (line p : Z) (rest : list Z) (i : nat),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur0 ->
mf_regs_at B v lyc pos regs1 ->
(length rest <= n)%nat -> rest <> [] ->
mf_loop v Wc memc mc0 cur0 line p rest -> hb_mod (mv_k0 v) mc0 mcc cur0 -> (i < length (mc_seg mcc))%nat ->
mf_fin (m_upd mcc i (ms_with_gen (mc_gen mcc)), Some i) line rest = mf_final v ->
getr regs1 21 = w64 (seg_spec.mseg_addr (mv_c v) i) ->
getr regs1 27 = w64 (line + 1) -> mf_np v memc Wc (mf_next p rest) ->
mf_at B v Wc regs1 memc mdc MFB_RMCPY.

(* 0x86b4c, back from m_refuse on the overflow path: the block holds mcc (overflow raised and the refusal kept),
   136(s1) still holds the head's cursor cur0, and the instructions left set it to NULL, load s10 from 152(s1)
   and go to the tail *)
Definition MFB_RREF2_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mc0 mcc : mconf) (cur0 : option nat) (line p : Z) (rest : list Z),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur0 ->
mf_regs_at B v lyc pos regs1 ->
(length rest <= n)%nat -> rest <> [] ->
mf_loop v Wc memc mc0 cur0 line p rest -> hb_mod (mv_k0 v) mc0 mcc None ->
mf_fin (mcc, None) line rest = mf_final v ->
getr regs1 20 = w64 511 -> getr regs1 27 = w64 (line + 1) -> mf_np v memc Wc (mf_next p rest) ->
mf_at B v Wc regs1 memc mdc MFB_RREF2.

(* 0x86b8c, back from the checked memset of the new entry: c->n is already |seg| + 1 and the 256 bytes of
   seg[|seg|] are zero, so the block holds mcc with one more entry, the empty one (mseg0 []); 136(s1) still holds
   the head's cursor. The raw zero bytes are carried beside the model because an mconf encoding does not fix the
   bytes of a name field past its NUL, and the memcpy that follows writes only the first |nm| of them.
   s5 = the new entry g, 192(s1) = the name, s10 = its length, s11 = line + 1. *)
Definition MFB_RMSET_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mc0 mcc : mconf) (cur0 : option nat) (line p : Z) (rest : list Z) (o : nat)
  (nm : list Z),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF (m_set_segs mcc (mc_seg mcc ++ [mseg0 []])) ->
mf_cells v lyc pos memc Wc cur0 -> mf_regs_at B v lyc pos regs1 ->
(length rest <= n)%nat -> rest <> [] ->
mf_loop v Wc memc mc0 cur0 line p rest -> hb_mod (mv_k0 v) mc0 mcc cur0 ->
hb_nm rest o nm -> (length (mc_seg mcc) < 32)%nat ->
sa_bytes (rdW Wc memc) (seg_spec.mseg_addr (mv_c v) (length (mc_seg mcc))) (repeat seg_spec.ZERO 256) ->
mf_fin (m_upd (m_set_segs mcc (mc_seg mcc ++ [mseg0 nm])) (length (mc_seg mcc)) (ms_with_gen (mc_gen mcc)),
        Some (length (mc_seg mcc))) line rest = mf_final v ->
getr regs1 21 = w64 (seg_spec.mseg_addr (mv_c v) (length (mc_seg mcc))) ->
mf_slot v memc Wc 192 (p + Z.of_nat o) -> getr regs1 26 = w64 (Z.of_nat (length nm)) ->
getr regs1 27 = w64 (line + 1) -> mf_np v memc Wc (mf_next p rest) ->
mf_at B v Wc regs1 memc mdc MFB_RMSET.

(* 0x86b54, the new entry (c->n < 32 at 0x86b1c): n + 1 is stored, the traps 0x86b68 / 0x86b74, g = c + 256 n,
   the entry is memset. The shadow byte address of c->n, formed at 0x86b04-0x86b08, is still in a1 and the check
   of the store at 0x86b54 reads it; a walk re-seeded here puts it back in the shape the code formed it in
   ((c + 0x2000 >> 3) + the shadow base). a0 = n (the sign-extended load of c->n, 0 <= n < 32). *)
Definition MFB_NEWE_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z) (o : nat)
  (nm : list Z),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur ->
mf_regs_at B v lyc pos regs1 ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc cur line p rest ->
hb_nm rest o nm -> m_find mcc nm = None -> (length (mc_seg mcc) < 32)%nat ->
mf_fin (mh_find mcc nm (line + 1)) line rest = mf_final v ->
getr regs1 10 = w64 (Z.of_nat (length (mc_seg mcc))) ->
getr regs1 11 = w64 (SHADOW_OFF + (mv_c v + seg_spec.MC_N) / 8) ->
mf_slot v memc Wc 192 (p + Z.of_nat o) -> getr regs1 26 = w64 (Z.of_nat (length nm)) ->
getr regs1 27 = w64 (line + 1) -> mf_np v memc Wc (mf_next p rest) ->
mf_at B v Wc regs1 memc mdc MFB_NEWE.

(* 0x86b04, m_find found nothing: the whole not-found arm (the check and the load of c->n, the test against 32,
   the overflow refusal or the new entry). The registers are HFIND's (m_find keeps s4, s9, s10, s11), less a1
   (the name is read from 192(s1) again at 0x86b8c). *)
Definition MFB_NFIND_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z) (o : nat)
  (nm : list Z),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur ->
mf_regs_at B v lyc pos regs1 ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc cur line p rest ->
hb_nm rest o nm -> m_find mcc nm = None ->
mf_fin (mh_find mcc nm (line + 1)) line rest = mf_final v ->
mf_slot v memc Wc 192 (p + Z.of_nat o) -> getr regs1 26 = w64 (Z.of_nat (length nm)) ->
getr regs1 20 = w64 511 -> getr regs1 27 = w64 (line + 1) -> mf_np v memc Wc (mf_next p rest) ->
mf_at B v Wc regs1 memc mdc MFB_NFIND.

(* 0x865cc, m_find returned: a0 = &c->seg[i] when the name is entry i's, else 0 (m_find_c.v's m_find_ptr); the
   rest as NFIND *)
Definition MFB_RFIND_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z) (o : nat)
  (nm : list Z),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur ->
mf_regs_at B v lyc pos regs1 ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc cur line p rest ->
hb_nm rest o nm ->
mf_fin (mh_find mcc nm (line + 1)) line rest = mf_final v ->
getr regs1 10 = w64 (m_find_ptr (mv_c v) mcc nm) ->
mf_slot v memc Wc 192 (p + Z.of_nat o) -> getr regs1 26 = w64 (Z.of_nat (length nm)) ->
getr regs1 20 = w64 511 -> getr regs1 27 = w64 (line + 1) -> mf_np v memc Wc (mf_next p rest) ->
mf_at B v Wc regs1 memc mdc MFB_RFIND.

End e.
End f.
End d.

(* ============================ the same statements at every FP state ============================
   m_refuse's post is apost_baseF (it reaches the snprintf wrapper), so the points after its call are reached at
   the FP state it returned; m_file_m.v's MF_<cut>_F has the same shape. *)
Section g. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Context {PI : PAImg seg_listing}.
Section i.
Variable B : asyms.
Definition MFB_JOIN_F (n : nat) : Prop := forall fx0 : YK11.FPState, MFB_JOIN_stmt (fx := fx0) B n.
Definition MFB_RREF1_F (n : nat) : Prop := forall fx0 : YK11.FPState, MFB_RREF1_stmt (fx := fx0) B n.
Definition MFB_RMCPY_F (n : nat) : Prop := forall fx0 : YK11.FPState, MFB_RMCPY_stmt (fx := fx0) B n.
Definition MFB_RREF2_F (n : nat) : Prop := forall fx0 : YK11.FPState, MFB_RREF2_stmt (fx := fx0) B n.
Definition MFB_RMSET_F (n : nat) : Prop := forall fx0 : YK11.FPState, MFB_RMSET_stmt (fx := fx0) B n.
Definition MFB_NEWE_F (n : nat) : Prop := forall fx0 : YK11.FPState, MFB_NEWE_stmt (fx := fx0) B n.
Definition MFB_NFIND_F (n : nat) : Prop := forall fx0 : YK11.FPState, MFB_NFIND_stmt (fx := fx0) B n.
Definition MFB_RFIND_F (n : nat) : Prop := forall fx0 : YK11.FPState, MFB_RFIND_stmt (fx := fx0) B n.
End i.
End h.
End g.
