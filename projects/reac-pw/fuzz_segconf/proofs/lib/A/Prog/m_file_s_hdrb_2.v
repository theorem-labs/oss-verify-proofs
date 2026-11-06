(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 134 of its 157 lines of code are new or changed and 495 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A, 0x85ebc), the segment S_MF_HDRB (HFIND 0x86abc -> TAIL 0x86cf8, 113
   instructions, 7 instrumented checks, 4 calls; MF-CUTS-A.md section 4): the points INSIDE the segment where the
   walk is cut, and the statement at each. Statement text only: no instruction is executed here.
   The HDRB segment lane of the G2 walk owner's G2. The files of the segment:
     m_file_s_hdrb_1.v  the model, byte-encoding, reader and footprint facts
     m_file_s_hdrb_2.v  THIS FILE: the inner cut points and their statements
     m_file_s_hdrb_3.v  the callee premises (m_find's, m_refuse's, the checked memset's and memcpy's) at a
                        mid-segment state
     m_file_s_hdrb_4.v  the model step of each of the segment's four paths
     m_file_s_hdrb_5.v  the join and the three short returns (JOIN -> TAIL, RREF1 -> JOIN, RREF2 -> TAIL,
                        RMCPY -> JOIN)
     m_file_s_hdrb_6.v  the checked memcpy of a new entry's name (RMSET -> RMCPY)
     m_file_s_hdrb_7.v  the not-found arm (m_find returned 0): c->n, the test against 32, the overflow refusal
                        and the new entry (n + 1, the checked memset)
     m_file_s_hdrb.v    the m_find call, the found arm, and `s_mf_hdrb : S_MF_HDRB B`

   WHAT THE SEGMENT DOES (listing dis/m_file.fuzz_segconf.asan.s, 0x86abc-0x86c80, slow paths 0x86dc0-0x86e40 and
   the error arms 0x87014-0x8703c; MF-CUTS-A.md section 4 "S_MF_HDRB"):
     0x86abc a0 = c (128(s1)), a1 = s5 = the name, a2 = s4 = its length; 0x86ac8 `jal m_find`.
     0x86acc `beqz a0`: m_find's result.
     FOUND (a0 = &c->seg[i]): 0x86ad0-0x86ae4 the instrumented check of g->gen (a load of the shadow byte at
       ((g + 252) >> 3) + the shadow base and a compare; the error path, a call of errpath_load4 at 0x87020, is not
       reached), 0x86ae8-0x86afc the same for c->gen (its shadow byte address is kept in 56(s1)), 0x86af0 / 0x86b04
       the two loads, 0x86b00 cur := g (136(s1)), 0x86b08 `bne`: g->gen <> c->gen goes to the join 0x86c50;
       equal: 0x86b14 `jal m_refuse(c, line + 1)`, back at 0x86b18, a3 := c + 0x23b0, to the join.
     NOT FOUND (a0 = 0): 0x86b8c-0x86ba0 the check and the load of c->n; 0x86ba4 `blt a0,s3` (s3 = 32).
       n >= 32: 0x86ba8-0x86bc4 the check, the load and the store of c->overflow (overflow + 1; the store reuses the
         load's check), then the shared refusal block 0x86bc8-0x86bd4 `jal m_refuse(c, line + 1)`, back at 0x86bd8,
         cur := 0, a7 := 144(s1), to the tail.
       n < 32: 0x86bfc-0x86c14 the check of the store and c->n := n + 1, 0x86c1c g := c + 256 n,
         0x86c2c `jal checked_memset(g, 0, 256)`, back at 0x86c30 cur := g, 0x86c44
         `jal checked_memcpy(g, name, |name|)`, back at 0x86c48 a3 := c + 0x23b0, s6 := s7 = line + 1, into the join.
     JOIN 0x86c50: a7 := 144(s1), the check and the load of c->gen, the check and the store of cur->gen, 0x86c80 to
       the tail.

   THE MODEL (SegModel, through m_file_m.v's mh_find): the segment computes mh_find mcc nm (line + 1) from the
   model mcc the block holds at HFIND; each path ends at the tail with that pair in the block and in 136(s1).
   The three paths are m_file_s_hdrb_1.v's hb_mh_find_eq / hb_mh_find_ne (found), hb_mh_find_full (overflow) and
   hb_mh_find_new (the new entry).

   WHY THE CUT POINTS ARE WHERE THEY ARE: at each of them a call has just returned, so the walk must re-seed its
   symbolic state anyway (m_file_sd.v's seed). There is NO cut inside an instrumented check: the shadow-byte
   address of the check at 0x86c00 is formed at 0x86b90-0x86b94, so the not-found arm runs from 0x86b8c to the
   memset call in one go (a re-seeded register would be an opaque atom and the token executor would no longer read
   the load as a check).

   THE MODEL AT A CUT: m_file_m.v's mf_loop bundles the text's facts with the model's (the cursor, n_kept, and the
   room the counters keep). After the m_refuse of this segment the model's refused has gone up by one, so mf_loop
   does not hold of the NEW model at the SAME text; it holds again at the next line, which is shorter (that is how
   the tail takes it). Each statement here therefore carries mf_loop of the model mc0 the segment STARTED from
   (its text facts are over the CURRENT reader) and, of the model mcc the block holds NOW, only hb_mod: the cursor
   names an entry, n_kept has not gone below the entry's, and refused / overflow have gone up by at most one. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_find_c m_refuse_c m_file_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ============================== the cut points inside the segment ==============================
   listing offset = AF_m_file + (pc - 0x85ebc), the offset the listing prints as `m_file+0x...` *)
(* 0x86acc, m_find returned: a0 is its result *)
Definition MFH_RFIND : Z := AF_m_file + 0xc10.
(* 0x86b18, m_refuse returned on the found path (g->gen was c->gen) *)
Definition MFH_RREF1 : Z := AF_m_file + 0xc5c.
(* 0x86b8c, m_find found nothing: the load of c->n *)
Definition MFH_NFIND : Z := AF_m_file + 0xcd0.
(* 0x86bd8, m_refuse returned on the overflow path (c->n was 32) *)
Definition MFH_RREF2 : Z := AF_m_file + 0xd1c.
(* 0x86c30, the checked memset of the new entry returned *)
Definition MFH_RMSET : Z := AF_m_file + 0xd74.
(* 0x86c48, the checked memcpy of its name returned *)
Definition MFH_RMCPY : Z := AF_m_file + 0xd8c.
(* 0x86c50, the join of the three paths: g->gen = c->gen, then the tail *)
Definition MFH_JOIN : Z := AF_m_file + 0xd94.
(* 0x86bfc, the new entry's own code (c->n was below 32) *)
Definition MFH_NEWE : Z := AF_m_file + 0xd40.

(* ===================================== what a cut carries =====================================
   the name the header named (MF_HFIND_stmt's three premises on nm, as one Prop) *)
Definition hb_nm (rest : list Z) (o : nat) (nm : list Z) : Prop :=
(0 < length nm < 16)%nat /\ (o + length nm <= length (mf_line rest))%nat /\
firstn (length nm) (skipn o rest) = nm.
(* of the model mcc the block holds at a cut, against the model mc0 of the cut HFIND: the cursor names an entry,
   n_kept has not gone below the call's, and refused / overflow have gone up by at most one (this segment calls
   m_refuse at most once and raises overflow at most once). It is what the tail's mf_loop needs, because the text
   left at the tail is shorter by at least one byte. *)
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

(* 0x86c50, the join: the block holds mcc, 136(s1) = &c->seg[i] and a3 = &c->gen; what is left of the line is the
   store g->gen = c->gen, which takes the model to m_upd mcc i (ms_with_gen (mc_gen mcc)). Reached from the found
   path (directly or through m_refuse) and from the new entry. *)
Definition MFH_JOIN_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mc0 mcc : mconf) (cur0 : option nat) (line p : Z) (rest : list Z) (i : nat),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc (Some i) ->
mf_regs_at B v lyc pos regs1 -> getr regs1 24 = w64 (frame_addr lyc 1 pos) ->
(length rest <= n)%nat -> rest <> [] ->
mf_loop v Wc memc mc0 cur0 line p rest -> hb_mod (mv_k0 v) mc0 mcc (Some i) ->
mf_fin (m_upd mcc i (ms_with_gen (mc_gen mcc)), Some i) line rest = mf_final v ->
getr regs1 13 = w64 (mv_c v + seg_spec.MC_GEN) ->
getr regs1 21 = w64 (mv_c v) -> getr regs1 22 = w64 (line + 1) ->
mf_np v memc Wc (mf_next p rest) ->
mf_at B v Wc regs1 memc mdc MFH_JOIN.

(* 0x86b18, back from m_refuse on the found path: as the join, but a3 is loaded by the two instructions left
   (0x86b18 `ld a3,48(s1)`, 0x86b1c `j 0x86c50`) *)
Definition MFH_RREF1_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mc0 mcc : mconf) (cur0 : option nat) (line p : Z) (rest : list Z) (i : nat),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc (Some i) ->
mf_regs_at B v lyc pos regs1 -> getr regs1 24 = w64 (frame_addr lyc 1 pos) ->
(length rest <= n)%nat -> rest <> [] ->
mf_loop v Wc memc mc0 cur0 line p rest -> hb_mod (mv_k0 v) mc0 mcc (Some i) ->
mf_fin (m_upd mcc i (ms_with_gen (mc_gen mcc)), Some i) line rest = mf_final v ->
getr regs1 21 = w64 (mv_c v) -> getr regs1 22 = w64 (line + 1) ->
mf_np v memc Wc (mf_next p rest) ->
mf_at B v Wc regs1 memc mdc MFH_RREF1.

(* 0x86bd8, back from m_refuse on the overflow path: the block holds mcc (overflow raised and the refusal kept),
   136(s1) still holds the cursor of the head, and the three instructions left set it to NULL, load a7 from
   144(s1) and go to the tail *)
Definition MFH_RREF2_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mc0 mcc : mconf) (cur0 : option nat) (line p : Z) (rest : list Z),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur0 ->
mf_regs_at B v lyc pos regs1 -> getr regs1 24 = w64 (frame_addr lyc 1 pos) ->
(length rest <= n)%nat -> rest <> [] ->
mf_loop v Wc memc mc0 cur0 line p rest -> hb_mod (mv_k0 v) mc0 mcc None ->
mf_fin (mcc, None) line rest = mf_final v ->
getr regs1 21 = w64 (mv_c v) -> getr regs1 22 = w64 (line + 1) ->
mf_np v memc Wc (mf_next p rest) ->
mf_at B v Wc regs1 memc mdc MFH_RREF2.

(* 0x86c30, back from the checked memset of the new entry: c->n is already |seg| + 1 and the 256 bytes of
   seg[|seg|] are zero, so the block holds mcc with one more entry, the empty one (mseg0 []); 136(s1) still holds
   the cursor of the head, and the instruction at 0x86c30 sets it to the new entry. The raw zero bytes are carried
   beside the model because an mconf encoding does not fix the bytes of a name field past its NUL, and the memcpy
   that follows writes only the first |nm| of them.
   s11 = the new entry, s5 = the name (m_find's argument, still there), s4 = its length, s6 = c, s7 = line + 1. *)
Definition MFH_RMSET_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mc0 mcc : mconf) (cur0 : option nat) (line p : Z) (rest : list Z) (o : nat)
  (nm : list Z),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF (m_set_segs mcc (mc_seg mcc ++ [mseg0 []])) ->
mf_cells v lyc pos memc Wc cur0 ->
mf_regs_at B v lyc pos regs1 -> getr regs1 24 = w64 (frame_addr lyc 1 pos) ->
(length rest <= n)%nat -> rest <> [] ->
mf_loop v Wc memc mc0 cur0 line p rest -> hb_mod (mv_k0 v) mc0 mcc cur0 ->
hb_nm rest o nm -> (length (mc_seg mcc) < 32)%nat ->
sa_bytes (rdW Wc memc) (seg_spec.mseg_addr (mv_c v) (length (mc_seg mcc))) (repeat seg_spec.ZERO 256) ->
mf_fin (m_upd (m_set_segs mcc (mc_seg mcc ++ [mseg0 nm])) (length (mc_seg mcc)) (ms_with_gen (mc_gen mcc)),
        Some (length (mc_seg mcc))) line rest = mf_final v ->
getr regs1 27 = w64 (seg_spec.mseg_addr (mv_c v) (length (mc_seg mcc))) ->
getr regs1 21 = w64 (p + Z.of_nat o) -> getr regs1 20 = w64 (Z.of_nat (length nm)) ->
getr regs1 22 = w64 (mv_c v) -> getr regs1 23 = w64 (line + 1) ->
mf_np v memc Wc (mf_next p rest) ->
mf_at B v Wc regs1 memc mdc MFH_RMSET.

(* 0x86c48, back from the checked memcpy of the name: the block holds the new entry with its name, 136(s1) names
   it, s5 = c, s6 = c (0x86c4c puts line + 1 back from s7), s7 = line + 1; the two instructions left load a3 and
   restore s6, then the join *)
Definition MFH_RMCPY_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mc0 mcc : mconf) (cur0 : option nat) (line p : Z) (rest : list Z) (i : nat),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc (Some i) ->
mf_regs_at B v lyc pos regs1 -> getr regs1 24 = w64 (frame_addr lyc 1 pos) ->
(length rest <= n)%nat -> rest <> [] ->
mf_loop v Wc memc mc0 cur0 line p rest -> hb_mod (mv_k0 v) mc0 mcc (Some i) ->
mf_fin (m_upd mcc i (ms_with_gen (mc_gen mcc)), Some i) line rest = mf_final v ->
getr regs1 21 = w64 (mv_c v) -> getr regs1 23 = w64 (line + 1) ->
mf_np v memc Wc (mf_next p rest) ->
mf_at B v Wc regs1 memc mdc MFH_RMCPY.

(* 0x86b8c, m_find found nothing: the whole not-found arm (the load of c->n, the test against 32, the overflow
   refusal or the new entry). The registers are the head's, less a0 (zero, tested at 0x86acc). *)
Definition MFH_NFIND_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z) (o : nat)
  (nm : list Z),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur ->
mf_regs_at B v lyc pos regs1 -> getr regs1 24 = w64 (frame_addr lyc 1 pos) ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc cur line p rest ->
hb_nm rest o nm -> m_find mcc nm = None ->
mf_fin (mh_find mcc nm (line + 1)) line rest = mf_final v ->
getr regs1 21 = w64 (p + Z.of_nat o) -> getr regs1 20 = w64 (Z.of_nat (length nm)) ->
getr regs1 22 = w64 (line + 1) -> getr regs1 23 = w64 (line + 1) ->
mf_np v memc Wc (mf_next p rest) ->
mf_at B v Wc regs1 memc mdc MFH_NFIND.

(* 0x86bfc, the new entry (c->n < 32 at 0x86ba4): n + 1 is stored, the entry is memset and its name copied.
   The shadow byte address of c->n, formed at 0x86b90-0x86b94, is still in a1 and the check of the store at
   0x86c00 reads it; it is therefore a premise here and a walk re-seeded at this point must put it back in the
   shape the code formed it in ((c + 0x2000 >> 3) + the shadow base), or the token executor no longer reads the
   load as a check. s5 = the name, s4 = its length, s6 = line + 1 (0x86bfc moves it to s7), s8 = FAKE. *)
Definition MFH_NEWE_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z) (rest : list Z) (o : nat)
  (nm : list Z),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur ->
mf_regs_at B v lyc pos regs1 -> getr regs1 24 = w64 (frame_addr lyc 1 pos) ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc cur line p rest ->
hb_nm rest o nm -> m_find mcc nm = None -> (length (mc_seg mcc) < 32)%nat ->
mf_fin (mh_find mcc nm (line + 1)) line rest = mf_final v ->
getr regs1 10 = w64 (Z.of_nat (length (mc_seg mcc))) ->
getr regs1 11 = w64 (SHADOW_OFF + (mv_c v + seg_spec.MC_N) / 8) ->
getr regs1 21 = w64 (p + Z.of_nat o) -> getr regs1 20 = w64 (Z.of_nat (length nm)) ->
getr regs1 22 = w64 (line + 1) ->
mf_np v memc Wc (mf_next p rest) ->
mf_at B v Wc regs1 memc mdc MFH_NEWE.

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
Definition MFH_JOIN_F (n : nat) : Prop := forall fx0 : YK11.FPState, MFH_JOIN_stmt (fx := fx0) B n.
Definition MFH_RREF1_F (n : nat) : Prop := forall fx0 : YK11.FPState, MFH_RREF1_stmt (fx := fx0) B n.
Definition MFH_RREF2_F (n : nat) : Prop := forall fx0 : YK11.FPState, MFH_RREF2_stmt (fx := fx0) B n.
Definition MFH_RMSET_F (n : nat) : Prop := forall fx0 : YK11.FPState, MFH_RMSET_stmt (fx := fx0) B n.
Definition MFH_RMCPY_F (n : nat) : Prop := forall fx0 : YK11.FPState, MFH_RMCPY_stmt (fx := fx0) B n.
Definition MFH_NFIND_F (n : nat) : Prop := forall fx0 : YK11.FPState, MFH_NFIND_stmt (fx := fx0) B n.
Definition MFH_NEWE_F (n : nat) : Prop := forall fx0 : YK11.FPState, MFH_NEWE_stmt (fx := fx0) B n.
End i.
End h.
End g.
