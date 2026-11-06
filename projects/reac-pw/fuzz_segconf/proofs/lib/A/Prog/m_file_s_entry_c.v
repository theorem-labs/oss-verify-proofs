(* S_MF_ENTRY's inner cut ENT_LBL, at the label test 0x85ff4 of m_file on fuzz_segconf.asan (image A, m_file at
   0x85ebc). lib/A/Prog/m_file_s_entry_2.v walks from the entry to it (the prologue, the class-1 frame request,
   the frame header and shadow stores); lib/A/Prog/m_file_s_entry_3.v walks on from it (the label arms, snprintf,
   gen++, the *text test, the set-up, and the hand-offs to MF_HEAD / MF_EXIT).
   A lane of the G2 walk owner. Closed against G2 FINAL (the image-A owner's contracts 6f783602b5e3). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaArt PaArtOwn PaNoChain PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtPFShared RtPFCmd RtFormat.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.


(* ======================= the cut at the label test 0x85ff4 (ENT_LBL) ======================= *)
(* The walk of S_MF_ENTRY is cut here: everything the prologue, the class-1 frame request and the frame's
   header / shadow stores leave behind, as facts (lib/A/Prog/m_file_s_entry_3.v walks on from here through the
   label arms, snprintf, gen++, the *text test and the two hand-offs).
   0x85ff4 `bnez s4`: s4 is the label argument; the two arms join at 0x86000. *)
Definition MF_LBL : Z := AF_m_file + 0x138.

Section c0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c1.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section c2.
Variable B : asyms.

(* the registers at 0x85ff4 (MF-CUTS-A.md section 3): s0 = sp0, sp = s1 = s1, s2 = the shadow base, s3 = s8 = FB,
   s4 = the label, s5 = c, s6 = c + 0x2000, s7 = &c->reading, s10 = shadow(FB), s11 = the text (ra is the frame
   request's return address by now; the entry's ra is in memory, mf_saved) *)
Definition ent_lbl_regs (v : mfv) (pos : Z) (regs1 : bvmap 5 word) : Prop :=
getr regs1 2 = w64 (mf_s1 (mv_sp v)) /\ getr regs1 3 = w64 (as_gp B) /\ getr regs1 4 = w64 (as_tp B) /\
getr regs1 8 = w64 (mv_sp v) /\ getr regs1 9 = w64 (mf_s1 (mv_sp v)) /\
getr regs1 18 = w64 SHADOW_OFF /\
getr regs1 19 = w64 (frame_addr (mv_ly v) 1 pos) /\ getr regs1 20 = w64 (mv_lp v) /\
getr regs1 21 = w64 (mv_c v) /\ getr regs1 22 = w64 (mv_c v + seg_spec.MC_N) /\
getr regs1 23 = w64 (mv_c v + seg_spec.MC_READING) /\ getr regs1 24 = w64 (frame_addr (mv_ly v) 1 pos) /\
getr regs1 26 = w64 (SHADOW_OFF + frame_addr (mv_ly v) 1 pos / 8) /\ getr regs1 27 = w64 (mv_t v).

(* what the prologue has written that a later cut reads (m_file_m.v's mf_core): the frame's flag pointer at
   FB + 120 (from the frame request), low.i's eight shadow bytes 0xf8 (0x85fb4-0x85fd8), the entry's ra and
   s0 .. s11 below sp0 *)
Definition ent_lbl_mem (v : mfv) (Wc : world SEGS) (memc : word -> option byte) (pos : Z) : Prop :=
val_mem SEGS (mrestrict (w_H Wc) memc) (frame_addr (mv_ly v) 1 pos + 120) 8 (flag_addr (mv_ly v) 1 pos) /\
(forall i, 4 <= i < 12 ->
 val_mem SEGS (mrestrict (w_H Wc) memc) (SHADOW_OFF + frame_addr (mv_ly v) 1 pos / 8 + i) 1 MF_LOW_OFF) /\
mf_saved (mrestrict (w_H Wc) memc) (mv_sp v) (mv_regs v).

(* the cut: the journal from the entry with the frame owned, the registers and the memory above, and the mconf
   block still holding the entry's model and bytes (no byte of it is written before 0x86014). The entry's other reader
   facts (the text, the label, the image) follow at this state from mf_cx and the journal (m_file_k.v's *_now_j
   lemmas; the journal keeps every block byte outside M_FILE_FP, which lies in the mconf block). *)
Definition ENT_LBL_stmt : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos,
mf_cx B v -> sa_frm0 -> lyc = mv_ly v -> (exists f, Sc = set_fs f (mv_S v)) ->
In (1, pos) (frames Sc) -> Permutation (ablocks B lyc Sc) (ablocks B (mv_ly v) (mv_S v)) ->
ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
  (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc memc mdc 0 ->
ent_lbl_regs v pos regs1 -> ent_lbl_mem v Wc memc pos ->
sa_mconf (rdW Wc memc) (mv_c v) (mv_mc v) ->
(* every byte of the mconf block is the entry's (the label may lie in the block, inside M_FILE_FP, where the
   journal keeps nothing) *)
(forall a, mv_c v <= a < mv_c v + seg_spec.SEG_M_SIZE -> rdW Wc memc a = rdW (mv_W v) (mv_mem v) a) ->
mf_at B v Wc regs1 memc mdc MF_LBL.
End c2.
End c1.
End c0.

Section g0. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section g1.
Context {PI : PAImg seg_listing}.
Section g2.
Variable B : asyms.
Definition ENT_LBL_F : Prop := forall fx0 : YK11.FPState, ENT_LBL_stmt (fx := fx0) B.
End g2.
End g1.
End g0.
