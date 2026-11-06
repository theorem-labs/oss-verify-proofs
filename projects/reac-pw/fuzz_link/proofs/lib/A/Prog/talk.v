(* talk on image A (fuzz_link.asan 0x8763c, 1924 bytes; listing offset AF_talk = 0x5470; listing
   (internal path) (internal record, sha256 5526460cb5be)): the walk of its contract
   lib/A/Prog/talk_c.v `talk_acontract` (link_amem.v `aleaf_rd`, K = TALK_AK = 4240, EV 0, SIDE []).

   The walk is cut into pieces whose statements are in lib/A/Prog/talk_defs.v; this file puts them together:
   - talk_entry.v tk_entry_ok: TK_ENTRY from TK_RET, TK_AT_CP1 and TK_CL0 (the entry +0x00 .. +0x12c, the two
     errno arms and the ring test);
   - talk_cp1.v   tk_cp1_ok:   TK_AT_CP1 from TK_CL0 (the call of checked_memcpy, then +0x130 .. +0x16c);
   - talk_chunk.v tk_cl0_ok:   TK_CL0 from TK_RET and TK_MSG (the chunk loop +0x16c, +0x1ac, +0x1c8, +0x1e0;
     tk_chunk_ok and tk_nxt_ok are its induction on the chunks left);
   - talk_msg.v   tk_msg_ok:   TK_MSG from TK_RET and TK_ATTR (the message loop +0x204);
   - talk_attr.v  tk_attr_ok:  TK_ATTR from TK_RET, TK_KIND and TK_TAKE_AL (the attribute loop +0x30c);
   - talk_kind.v  tk_kind_ok:  TK_KIND from TK_TAKE_KD (the inner LINKINFO walk +0x3f8);
   - talk_take.v  tk_take_al_ok, tk_take_kd_ok: the two inlined take_text arms (+0x3a0, +0x47c);
   - talk_ret.v   tk_ret_ok:   TK_RET (the epilogue +0xb4 and the apost).

   Section hypotheses: LAWS, TL (PALib), LV (LinkVals) are the image instance's facts; MEMCPY, checked_memcpy's
   contract, is discharged on the image by lib/A/AE2q.v (0x52d78).

   Proves talk (kind: function proof). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk talk_c talk_defs talk_kit talk_spec
talk_ret talk_chunk talk_cp1 talk_entry talk_msg talk_attr talk_kind talk_take.
Import ListNotations.
Open Scope Z_scope.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis LV : LinkVals.
Hypothesis MEMCPY : aintrin_realizes SEGS B OCpy (pa_sigma LS___asan_memcpy).

Theorem talk_aproof : forall rlo rhi, talk_acontract SK SEGS rlo rhi B.
Proof.
intros rlo rhi.
unfold talk_acontract, aleaf_rd.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HA HRD HP.
destruct HP as (mbs & kbs & req & HP').
pose (c := mkTKC G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs mbs kbs req rlo rhi).
assert (HC : tk_call SK B c) by exact (conj HA HP').
replace (cfg_at SEGS TALK_A regs memc mdc)
  with (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_talk)) memc (seg_rom SEGS)) mdc)
  by (unfold cfg_at, w64, TALK_A, AF_talk; rewrite (lv_text LV); reflexivity).
pose proof (tk_ret_ok SK B LAWS LV c HC) as RET.
pose proof (tk_take_al_ok SK B LAWS LV MEMCPY c HC) as TAL.
pose proof (tk_take_kd_ok SK B LAWS LV MEMCPY c HC) as TKD.
pose proof (tk_kind_ok SK B LAWS LV c HC TKD) as KIND.
pose proof (tk_attr_ok SK B LAWS LV c HC RET KIND TAL) as ATTR.
pose proof (tk_msg_ok SK B LAWS LV c HC RET ATTR) as MSG.
pose proof (tk_cl0_ok SK B LAWS LV c HC RET MSG) as CL0.
pose proof (tk_cp1_ok SK B LAWS LV MEMCPY c HC CL0) as CP1.
exact (tk_entry_ok SK B LAWS TL LV c HC RET CP1 CL0).
Qed.
End w.

Print Assumptions talk_aproof.

