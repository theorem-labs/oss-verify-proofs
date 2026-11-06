(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: __interceptor_vfprintf of fm.asan (0x457ec, frame 0x30, entered from musl vsnprintf
   through __wrap_vfprintf) ported from A/AE35.v's walk: the entry state with the read-only image cells in vpA_rodata's
   form, TryAsanInitFromRtl and the common_flags ()->check_printf test run through, REAL (vfprintf) read from 0x9b740,
   the epilogue and ret as in tfib_vprintf_icpt_E; the inline printf_common run is replaced by a kcall of the
   printf_common contract (apcommon_realizesU), musl vfprintf by a kcall of avfp_realizes; the vprintf entry part
   (tfib_vprintf_icpt_A) is not used; stated as FMsnprintfGI's avfpi_realizes over FMsnprintfI's snk_frame. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMsnprintfGvfi.v, with its module paths and module names changed; 491 of its 561 lines of code are new or changed and 337 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A (the asan build, pin 059dae63e07c): ___interceptor_fprintf 0x46e48 (frame 0x70) and its
   trampoline __interceptor_trampoline_fprintf 0x43084 (`j 0x46e48`) on link's memory FILE, at the contract
   LinkVfDefs.afprintf_mf_realizes (link's family link_vf_FF, the guard cells LA_GOT_GUARD -> LA_GUARD, every rlo rhi),
   from musl vfprintf's contract at 0x973e0 at a window Kv (the Section hypothesis AVF, as LinkVfBody.v) and
   printf_common's (LinkSnpPort.link_pcommon, window 2320). The body (listing
   (internal path) (internal record, sha256 220f0a9113ab)): +0x0 addi
   sp,sp,-0x70; +0x1c..+0x30 a6, a7, a2..a5 stored at sp+0x60, +0x68, +0x40..+0x58, so a2..a7 lie at the entry sp - 0x30
   .. sp - 0x8, right below the caller's slots; +0x34..+0x38 the va_list sp+0x40 at sp+8; +0x3c jal TryAsanInitFromRtl
   (0x5b214), +0x40 beqz (not taken: its fast path returns 1 when asan_inited 0xab118 = 1); +0x44..+0x48 aq at sp+0x18;
   +0x4c TryAsanInitFromRtl again, +0x50 beqz (not taken); +0x54..+0x60 the .got cell 0xa19c0 -> common_flags 0x13bf68,
   lbu check_printf 0x13bfbc = 1, +0x68 beqz (not taken); +0x7c jal printf_common (0x1ebfc, fmt, aq) (0x45fb4);
   +0x80..+0x88 REAL (vfprintf) from 0xa3738 = 0x973e0 and aq; +0xa0..+0xbc a0 = f, a1 = fmt, jalr; +0xc0..+0xd4 the
   epilogue. The cells come from AR's constant law (FMsnprintfGvfi0.vfi_rodata, the same three cells and
   TryAsanInitFromRtl's). The runs are new, over the table AE34.tbl_icpt (which holds 0x43044 .. 0x430e4, 0x46e48 .. +54
   words and 0x5b214 .. +40 words) and a stack region of SVRF = 0x80 bytes: the frame 0x70 (listing +0x0) and the 0x10
   of TryAsanInitFromRtl's frame below it (rt_0 +0x0 addi sp,sp,-0x10), both read off link's listings. The a2..a7 spill
   is read back from the runs' chunks (fp_spill) and joined with the caller's slots (FMsnprintfVa.words_at_app) into
   the argument words ws of fva_words, at sp - 0x30, the va_list musl vfprintf and printf_common get.
   The bound the donor asks is kept: ESTACK <= Kv. AR form throughout (the kit at U = [], ARU_nil). Written new. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YI00 YI16 YK06.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE20 AE2y.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import SnUpoison.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import FMH_Base FMsnprintfImg FMsnprintfK.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import PfFacts SnShared SnSx.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import FMsnprintfSk FMsnprintfVa.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import FMsnprintfGk0 FMsnprintfGt0 FMsnprintfGvfi0.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AMemFileSink AMemFile AD2l.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkVfDefs LinkPfPiece LinkVfInst.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkVfBundle.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require FMsnprintfFmI.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require LinkSnpPort.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG0q.
#[local] Ltac Zify.zify_pre_hook ::= try unfold YImgTop.IMG_TOP, YImgTop.IMG_LO in *.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the walk's symbolic states: atom 2 = the entry sp ---- *)
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* the stack region: the frame 0x70 and TryAsanInitFromRtl's 0x10 below it *)
Definition SVRF : Z := 0x80.
Definition RA_PCOM_FPI : Z := 0x46ec8. (* +0x80: the return from printf_common (+0x7c jal) *)
Definition RA_FP : Z := 0x46f08.       (* +0xc0: the return from REAL (vfprintf) (+0xbc jalr a3) *)
Definition fp_stk : YP09.region := YP09.mkRegion (Some 2%nat) (- SVRF) 0 (- SVRF) 0 [].
Definition fp_mem : smem := fp_stk :: map ro_region vfi_rodata.
Definition fp_p0 : sstate := mkSS LA_I_FPRINTF sr_atoms fp_mem None vfi_facts.
(* entry .. printf_common: prologue, the spill, TryAsanInitFromRtl twice, check_printf, aq *)
Definition fp_e1 : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs tbl_icpt FUEL A_PCOM fp_p0).
Lemma r_fp1 : sym_run_toN tfibsegs tbl_icpt FUEL A_PCOM fp_p0 = (fp_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition fp_r1 : YP09.region := Eval vm_compute in hd fp_stk (ss_mem fp_e1).
Definition fp_rest1 : smem := Eval vm_compute in tl (ss_mem fp_e1).
(* printf_common's return .. REAL (vfprintf) *)
Definition fp_s2 : sstate := kafter 32 fp_e1 RA_PCOM_FPI (-112) 0 0.
Definition fp_e2 : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs tbl_icpt FUEL A_VFP fp_s2).
Lemma r_fp2 : sym_run_toN tfibsegs tbl_icpt FUEL A_VFP fp_s2 = (fp_e2, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition fp_r2 : YP09.region := Eval vm_compute in hd fp_stk (ss_mem fp_e2).
Definition fp_rest2 : smem := Eval vm_compute in tl (ss_mem fp_e2).
(* the image cells are dropped before musl vfprintf (the epilogue reads none) *)
Definition fp_c3 : sstate := set_mem fp_e2 [fp_r2].
(* vfprintf's return .. ret *)
Definition fp_s3 : sstate := kafter 48 fp_c3 RA_FP (-112) 0 0.
Definition fp_e3 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tbl_icpt FUEL fp_s3).
Lemma r_fp3 : sym_runN tfibsegs tbl_icpt FUEL fp_s3 = (fp_e3, RS_stopped (SR_jalr (SOff 1 0))).
Proof. vm_compute. reflexivity. Qed.
(* the trampoline: its `j` is one step of the same table, ending at fp_p0 *)
Definition fpw_t0 : sstate := mkSS LA_W_FPRINTF sr_atoms fp_mem None vfi_facts.
Lemma r_fpw : sym_run_toN tfibsegs tbl_icpt FUEL LA_I_FPRINTF fpw_t0 = (fp_p0, RS_running).
Proof. vm_compute. reflexivity. Qed.

(* the shapes the proof reads off the states *)
Definition fpr_winb (t : option nat * Z * Z) : bool :=
match t with
| (Some 2%nat, lo, hi) => (- SVRF <=? lo) && (hi <=? 0)
| (_, lo, hi) => hi <=? lo
end.
Definition fpr_win (rs : smem) : bool := forallb fpr_winb (windows rs).
Definition fpr_stk0 (rs : smem) : bool :=
match rs with
| r :: _ => match YP09.r_base r with Some 2%nat => (YP09.r_wlo r =? - SVRF) && (YP09.r_whi r =? 0) | _ => false end
| [] => false
end.

Lemma fpw_win : fpr_win (ss_mem fpw_t0) = true. Proof. vm_compute. reflexivity. Qed.
Lemma fp0_win : fpr_win (ss_mem fp_p0) = true. Proof. vm_compute. reflexivity. Qed.
Lemma fp0_stk : fpr_stk0 (ss_mem fp_p0) = true. Proof. vm_compute. reflexivity. Qed.
Lemma fp1_pc : ss_pc fp_e1 = A_PCOM. Proof. vm_compute. reflexivity. Qed.
Lemma fp1_resv : ss_resv fp_e1 = None. Proof. vm_compute. reflexivity. Qed.
Lemma fp1_ra : sr_get (ss_regs fp_e1) 1 = SLit RA_PCOM_FPI. Proof. vm_compute. reflexivity. Qed.
Lemma fp1_sp : sr_get (ss_regs fp_e1) 2 = SOff 2 (-112). Proof. vm_compute. reflexivity. Qed.
Lemma fp1_r3 : sr_get (ss_regs fp_e1) 3 = SOff 3 0. Proof. vm_compute. reflexivity. Qed.
Lemma fp1_r4 : sr_get (ss_regs fp_e1) 4 = SOff 4 0. Proof. vm_compute. reflexivity. Qed.
Lemma fp1_r11 : sr_get (ss_regs fp_e1) 11 = SOff 11 0. Proof. vm_compute. reflexivity. Qed.
Lemma fp1_r12 : sr_get (ss_regs fp_e1) 12 = SOff 2 (-48). Proof. vm_compute. reflexivity. Qed.
Lemma fp1_mem : ss_mem fp_e1 = fp_r1 :: fp_rest1. Proof. vm_compute. reflexivity. Qed.
Lemma fp1_b : YP09.r_base fp_r1 = Some 2%nat. Proof. vm_compute. reflexivity. Qed.
Lemma fp1_lo : YP09.r_lo fp_r1 = - SVRF. Proof. vm_compute. reflexivity. Qed.
Lemma fp1_hi : YP09.r_hi fp_r1 = 0. Proof. vm_compute. reflexivity. Qed.
Lemma fp1_wlo : YP09.r_wlo fp_r1 = - SVRF. Proof. vm_compute. reflexivity. Qed.
Lemma fp1_whi : YP09.r_whi fp_r1 = 0. Proof. vm_compute. reflexivity. Qed.
Lemma fp1_at : ss_atoms_lt 32 fp_e1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma fp1_wf : regions_wf (ss_mem (kafter 32 fp_e1 RA_PCOM_FPI (-112) 0 0)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma fp1_nc : no_cdata (ss_mem (kafter 32 fp_e1 RA_PCOM_FPI (-112) 0 0)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma fp1_ma : mem_atoms_lt 32 (ss_mem (kafter 32 fp_e1 RA_PCOM_FPI (-112) 0 0)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma fp1_ci : forallb (chunk_inside fp_r1) (YP09.r_chunks fp_r1) = true. Proof. vm_compute. reflexivity. Qed.
Lemma fp1_far : forallb ro_far fp_rest1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma fp1_stk : fpr_stk0 (ss_mem fp_e1) = true. Proof. vm_compute. reflexivity. Qed.
(* a2..a7 at the entry sp - 0x30 .. sp - 0x8 *)
Lemma fp1_slots : forall i, (i < 6)%nat ->
  In (YP09.mkChunk (-48 + 8 * Z.of_nat i) (CVal 8 (SOff (12 + i) 0))) (YP09.r_chunks fp_r1).
Proof. intros i Hi. do 6 (destruct i as [|i]; [vm_compute; tauto|]). lia. Qed.
Lemma fp2_win : fpr_win (ss_mem fp_s2) = true. Proof. vm_compute. reflexivity. Qed.
Lemma fp2_stk : fpr_stk0 (ss_mem fp_e2) = true. Proof. vm_compute. reflexivity. Qed.
Lemma fp2_mem : ss_mem fp_e2 = fp_r2 :: fp_rest2. Proof. vm_compute. reflexivity. Qed.
Lemma fp2_b : YP09.r_base fp_r2 = Some 2%nat. Proof. vm_compute. reflexivity. Qed.
Lemma fp2_lo : YP09.r_lo fp_r2 = - SVRF. Proof. vm_compute. reflexivity. Qed.
Lemma fp2_hi : YP09.r_hi fp_r2 = 0. Proof. vm_compute. reflexivity. Qed.
Lemma fp2_wlo : YP09.r_wlo fp_r2 = - SVRF. Proof. vm_compute. reflexivity. Qed.
Lemma fp2_whi : YP09.r_whi fp_r2 = 0. Proof. vm_compute. reflexivity. Qed.
Lemma fp2_slots : forall i, (i < 6)%nat ->
  In (YP09.mkChunk (-48 + 8 * Z.of_nat i) (CVal 8 (SOff (12 + i) 0))) (YP09.r_chunks fp_r2).
Proof. intros i Hi. do 6 (destruct i as [|i]; [vm_compute; tauto|]). lia. Qed.
Lemma fp3c_pc : ss_pc fp_c3 = A_VFP. Proof. vm_compute. reflexivity. Qed.
Lemma fp3c_resv : ss_resv fp_c3 = None. Proof. vm_compute. reflexivity. Qed.
Lemma fp3c_mem : ss_mem fp_c3 = [fp_r2]. Proof. reflexivity. Qed.
Lemma fp3c_ra : sr_get (ss_regs fp_c3) 1 = SLit RA_FP. Proof. vm_compute. reflexivity. Qed.
Lemma fp3c_sp : sr_get (ss_regs fp_c3) 2 = SOff 2 (-112). Proof. vm_compute. reflexivity. Qed.
Lemma fp3c_r3 : sr_get (ss_regs fp_c3) 3 = SOff 3 0. Proof. vm_compute. reflexivity. Qed.
Lemma fp3c_r4 : sr_get (ss_regs fp_c3) 4 = SOff 4 0. Proof. vm_compute. reflexivity. Qed.
Lemma fp3c_r10 : sr_get (ss_regs fp_c3) 10 = SOff 10 0. Proof. vm_compute. reflexivity. Qed.
Lemma fp3c_r11 : sr_get (ss_regs fp_c3) 11 = SOff 11 0. Proof. vm_compute. reflexivity. Qed.
Lemma fp3c_r12 : sr_get (ss_regs fp_c3) 12 = SOff 2 (-48). Proof. vm_compute. reflexivity. Qed.
Lemma fp3c_at : ss_atoms_lt 48 fp_c3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma fp3c_wf : regions_wf (ss_mem (kafter 48 fp_c3 RA_FP (-112) 0 0)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma fp3c_nc : no_cdata (ss_mem (kafter 48 fp_c3 RA_FP (-112) 0 0)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma fp3c_ma : mem_atoms_lt 48 (ss_mem (kafter 48 fp_c3 RA_FP (-112) 0 0)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma fp3c_ci : forallb (chunk_inside fp_r2) (YP09.r_chunks fp_r2) = true. Proof. vm_compute. reflexivity. Qed.
Lemma fp3s_win : fpr_win (ss_mem fp_s3) = true. Proof. vm_compute. reflexivity. Qed.
Lemma fp3e_stk : fpr_stk0 (ss_mem fp_e3) = true. Proof. vm_compute. reflexivity. Qed.
Lemma fp3e_resv : ss_resv fp_e3 = None. Proof. vm_compute. reflexivity. Qed.
Lemma fp3e_ret : clookup tbl_icpt (ss_pc fp_e3) = Some RET_WORD_r. Proof. vm_compute. reflexivity. Qed.
Lemma fp3e_ra : sr_get (ss_regs fp_e3) 1 = SOff 1 0. Proof. vm_compute. reflexivity. Qed.
Lemma fp3e_r10 : sr_get (ss_regs fp_e3) 10 = SOff 52 0. Proof. vm_compute. reflexivity. Qed.
Lemma fp3e_kept : regs_kept fp_e3 = true. Proof. vm_compute. reflexivity. Qed.
End r.

(* ---- general lemmas of the walk over the region [sp - SVRF, sp) (FMsnprintfSvfi.v's svr_* at this region) ---- *)
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma fpr_win_sound : forall E rs a, fpr_win rs = true -> in_wrange E rs a ->
  bv_unsigned (ew E 2) - SVRF <= a < bv_unsigned (ew E 2).
Proof.
intros E rs a Hw Hin. destruct (in_wrange_windows E rs a Hin) as (b & lo & hi & Ht & Hr).
unfold fpr_win in Hw. rewrite forallb_forall in Hw. specialize (Hw _ Ht). unfold fpr_winb in Hw.
destruct b as [[|[|[|n]]]|]; cbn [base_val] in Hr; cbn in Hw; try (apply Z.leb_le in Hw; lia).
apply andb_prop in Hw as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. unfold SVRF in *. lia.
Qed.
Lemma fpr_present : forall (Hd : word -> bool) E rs ss1 ms1 (m : word -> option byte) a,
  fpr_win rs = true -> fpr_stk0 (ss_mem ss1) = true -> TFIB_IMG_END <= bv_unsigned (ew E 2) - SVRF ->
  frame_of E rs m (ms_mem ms1) -> st_ok tfibsegs E ss1 (restrict Hd ms1) ->
  0 <= a < 2 ^ 64 -> apresent Hd m a -> apresent Hd (ms_mem ms1) a.
Proof.
intros Hd E rs ss1 ms1 m a Hw Hs Hlo HF HS Ha Hp.
destruct (ss_mem ss1) as [|r1 rest] eqn:Hm; [discriminate|].
unfold fpr_stk0 in Hs. destruct (YP09.r_base r1) as [[|[|[|n]]]|] eqn:Hb; cbn in Hs; try discriminate.
apply andb_prop in Hs as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2.
assert (OUT : ~ (bv_unsigned (ew E 2) - SVRF <= a < bv_unsigned (ew E 2)) -> apresent Hd (ms_mem ms1) a).
{ intros Hn. apply (apresent_same Hd m); [|exact Hp]. apply HF. rewrite unsigned_lit_small by lia.
  intros Hin. exact (Hn (fpr_win_sound E rs a Hw Hin)). }
destruct (Z_lt_le_dec a (bv_unsigned (ew E 2) - SVRF)) as [L|L]; [apply OUT; lia|].
destruct (Z_lt_le_dec a (bv_unsigned (ew E 2))) as [L2|L2]; [|apply OUT; lia].
apply (st_ok_window_apresent Hd E ss1 ms1 0 r1 a HS); [rewrite Hm; reflexivity | rewrite Hb, H1, H2; cbn [base_val]; lia | lia].
Qed.
Hypothesis LAWS : AR_laws tfibsegs PcapB.
(* a run of the walk's own code keeps the frame over a window [sp - K, sp) that holds the stack region *)
Lemma fpr_run : forall ly S W mem0 md0 XW XP K sp mem md E ss ss1 ms1 mat,
  ly_stk_lo ly <= sp - K -> sp <= ly_stk_hi ly -> SVRF <= K -> TFIB_IMG_END <= sp - K -> sp <= 2 ^ 63 ->
  sw_frame PcapB ly S [] W mem0 md0 (sp - K) sp XW XP mem md ->
  fpr_win (ss_mem ss) = true -> fpr_stk0 (ss_mem ss1) = true -> bv_unsigned (ew E 2) = sp ->
  frame_of E (ss_mem ss) mem (ms_mem ms1) -> st_ok tfibsegs E ss1 (restrict (w_H W) ms1) ->
  sw_frame PcapB ly S [] W mem0 md0 (sp - K) sp XW XP (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat md).
Proof.
intros ly S W mem0 md0 XW XP K sp mem md E ss ss1 ms1 mat Hl Hh HK Hi H63 HF Hw Hs H2 HFo HS.
assert (HIE0 : 0 < TFIB_IMG_END) by reflexivity.
pose proof HF as (_ & _ & Hp & _ & _).
apply (sw_run PcapB LAWS ly S [] W mem0 md0 (sp - K) sp XW XP Hl Hh mem md (ms_mem ms1) mat E (ss_mem ss) HF).
- intros a Ha. pose proof (fpr_win_sound E _ a Hw Ha) as X. rewrite H2 in X. lia.
- exact HFo.
- intros a Ha. apply (fpr_present (w_H W) E (ss_mem ss) ss1 ms1 mem a Hw Hs); [rewrite H2; lia | exact HFo | exact HS | lia |].
  exact (Hp a Ha).
Qed.
End h.

(* ---- a2..a7, spilled at the entry sp - 0x30, read back from the stack region's chunks ---- *)
Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma fp_spill : forall (W : world tfibsegs) E ss ms r0 regs sp,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> nth_error (ss_mem ss) 0 = Some r0 ->
  YP09.r_base r0 = Some 2%nat -> bv_unsigned (ew E 2) = sp ->
  (forall i, (i < 6)%nat -> In (YP09.mkChunk (-48 + 8 * Z.of_nat i) (CVal 8 (SOff (12 + i) 0))) (YP09.r_chunks r0)) ->
  (forall n0, (n0 < 32)%nat -> ew E n0 = getr regs (Z_to_bv 5 (Z.of_nat n0))) ->
  words_at (aview tfibsegs (w_H W) (ms_mem ms)) (sp - 48) (map (argZ regs) [2; 3; 4; 5; 6; 7]).
Proof.
intros W E ss ms r0 regs sp HS H0 Hb E2 Hin EN i Hi. cbn [length map] in Hi |- *.
assert (ARGR : forall j, 0 <= argZ regs j < 2 ^ 64) by (intros j; unfold argZ; apply u64_range).
apply AF0x.val_mem_rdword; [do 6 (destruct i as [|i]; [cbn [nth map]; apply ARGR|]); lia|].
pose proof (g_slot W E ss ms 0 r0 _ 8%N _ (nth i (map (argZ regs) [2; 3; 4; 5; 6; 7]) 0) HS H0 (Hin i Hi)) as X.
rewrite Hb in X. cbn [base_val] in X. rewrite E2 in X.
replace (sp + (-48 + 8 * Z.of_nat i)) with (sp - 48 + 8 * Z.of_nat i) in X by lia.
apply X; [| change (8 * Z.of_N 8) with 64; do 6 (destruct i as [|i]; [cbn [nth map]; apply ARGR|]); lia | lia].
cbn [sv_denot].
do 6 (destruct i as [|i]; [cbn [nth map Nat.add]; rewrite EN by lia; unfold argZ;
  rewrite ?Z.add_0_r; repeat rewrite Z_to_bv_bv_unsigned; reflexivity|]). lia.
Qed.

(* the return `ret` at the end of the walk, in tbl_icpt *)
Lemma fp_ret : forall (W : world tfibsegs) E ss ms md Q,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  clookup tbl_icpt (ss_pc ss) = Some RET_WORD_r ->
  (forall mat', Q W (mkCfg (mkst (ms_regs ms) (v_jalr (getr (ms_regs ms) 1) 0) (ms_mem ms) (seg_rom tfibsegs))
     (with_vm_backing (m_vm_lazy md) mat' md))) ->
  SRr tfibsegs W (mkCfg ms md) Q.
Proof. intros. eapply (SRr_ret_at tfibsegs tbl_icpt tbl_icpt_ok AF0x.Hwx_tfa); eassumption. Qed.
End p.

Section v. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variables rlo rhi Kv : Z.
Hypothesis LAWS : AR_laws tfibsegs PcapB.
Hypothesis TB : PcapSyms PcapB.
Hypothesis HKv : ESTACK <= Kv.
(* musl vfprintf's contract on link's memory FILE (the interface with the seam lane) *)
Hypothesis AVF :
  avfprintf_mf_realizes tfibsegs PcapB link_amf rlo rhi link_vf_FF Kv LA_GOT_GUARD LA_GUARD LA_VFPRINTF.

(* the walk's entry state at pc (the body 0x46e48 or the trampoline 0x43084) *)
Lemma fpi_entry_ok : forall pc ly S W regs mem md,
  ARU tfibsegs PcapB ly S [] W mem md ->
  (forall a, spZ regs - SVRF <= a < spZ regs -> apresent (w_H W) mem a) ->
  spZ regs mod 16 = 0 -> 2 ^ 44 <= spZ regs - SVRF -> spZ regs <= 2 ^ 47 ->
  st_ok tfibsegs (Ereg regs []) (mkSS pc sr_atoms fp_mem None vfi_facts)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs))).
Proof.
intros pc ly S W regs mem md HA Hp H16 Hlo Hhi.
assert (HSVR : SVRF = 128) by reflexivity.
assert (EE2 : bv_unsigned (ew (Ereg regs []) 2) = spZ regs) by (rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl); reflexivity).
rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor.
  + unfold fp_stk. apply (region_ok_stack tfibsegs (Ereg regs []) _ 2 (spZ regs) (- SVRF)); [exact EE2 | lia | lia |].
    intros a Ha. apply apresent_writable. apply Hp. lia.
  + apply (vfi_ro_region_low vfi_rodata (Ereg regs []) (mrestrict (w_H W) (unpoison [] mem))); [vm_compute; reflexivity | |].
    * intros w Hw. unfold mrestrict. rewrite (ARU_mem_low tfibsegs PcapB ly S [] W mem md w HA Hw). reflexivity.
    * exact (rodata_ok PcapB TB vfi_rodata ly S (w_H W) (unpoison [] mem) (Ereg regs []) (vfi_rodata_chk ly)
        (ARU_ARm tfibsegs PcapB ly S [] W mem md HA)).
- apply pairwise_disjoint_of_extents. unfold fp_mem, fp_stk, vfi_rodata, icpt_rodata, ro_region, extent_of_region.
  cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite EE2.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. unfold vfi_facts. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite EE2. change (2 ^ 4) with 16. split; [|exact I]. split; [lia|]. split; [exact H16 | lia].
Qed.

(* the walk from a state that holds fp_p0 (the body's entry), with the frame of the window [sp - K, sp) since the
   contract's entry (regs, mem, md) *)
Lemma fpi_from : forall K ly S W regs mem md f fmt k fl om wend wpos wbase pos len pb xs ws T cval ms md0,
  0x70 + Kv <= K -> 0x70 + 2320 <= K ->
  mf_pre rlo rhi link_vf_FF K LA_GOT_GUARD LA_GUARD ly S W mem md (spZ regs) f fmt k fl om wend wpos wbase pos len
    pb ws T cval ->
  fva_words regs (aview tfibsegs (w_H W) mem) (spZ regs) xs ws ->
  spZ regs + 8 * Z.of_nat (length xs) <= 2 ^ 47 ->
  Forall (zdisjoint (spZ regs, 8 * Z.of_nat (length xs))) (vmf_out K (spZ regs) f) ->
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  YK0s.ret_ok (getr regs 1) -> getr regs 3 = w64 (as_gp PcapB) -> getr regs 4 = w64 (as_tp PcapB) ->
  getr regs 10 = w64 f -> getr regs 11 = w64 fmt ->
  st_ok tfibsegs (Ereg regs []) fp_p0 (restrict (w_H W) ms) ->
  sw_frame PcapB ly S [] W mem md (spZ regs - K) (spZ regs) (fun _ => False) (fun _ => False) (ms_mem ms) md0 ->
  SRr tfibsegs W (mkCfg ms md0) (vmf_post ly S W regs mem md K f k pb T fl om wend pos len).
Proof.
intros K ly S W regs mem md f fmt k fl om wend wpos wbase pos len pb xs ws T cval ms md0 HKK HKP HPRE (Hwseq & Hxs)
  H47x Xd Hfrm Hra G3 G4 G10 G11 HS0 F0.
pose proof (FMsnprintfFmI.FF_fmP_stable64 pf_link_piece) as STAB.
pose proof (FMsnprintfFmI.FF_fmP_mono pf_link_piece) as MONO.
assert (HES : ESTACK = 4096) by reflexivity.
pose proof HPRE as (HA & Hlo & Hhi & H16 & HK & Hp & Hblk & Hpw & Hk & Hdyn & Hpend & Hlpb & Hfit & Hro & Hgc & Hgv &
  XG1 & XG2 & XG3 & XG4 & Hgcd & Hgvd & HFF & HT).
pose proof (stk_kHighMemBeg PcapB ly S _ (ARU_ARm tfibsegs PcapB ly S [] W mem md HA)) as [K1 K2].
assert (HSVR : SVRF = 128) by reflexivity. assert (HIE : TFIB_IMG_END < kHighMemBeg) by reflexivity.
assert (KHB : kHighMemBeg = 0x10007fff8000) by reflexivity. assert (KHE : kHighMemEnd = 2 ^ 47) by reflexivity.
pose proof Hpw as P1. apply pairwise_vmf in P1. unfold zdisjoint in P1. cbn [fst snd] in P1.
pose proof Xd as Xd'. apply Forall_vmf in Xd' as [XD1 XD2]. unfold zdisjoint in XD1, XD2. cbn [fst snd] in XD1, XD2.
pose proof (amf_k_range _ f k Hk) as [FB0 FB1].
assert (Hlws : length ws = (6 + length xs)%nat) by (rewrite Hwseq, length_app; reflexivity).
assert (H16' : (spZ regs - 112) mod 16 = 0).
{ rewrite <- (Z_mod_plus_full (spZ regs - 112) 7 16). replace (spZ regs - 112 + 7 * 16) with (spZ regs) by lia. exact H16. }
assert (HLO : ly_stk_lo ly <= spZ regs - K) by lia.
assert (HIM : TFIB_IMG_END <= spZ regs - K) by lia.
assert (HSK : SVRF <= K) by lia.
assert (H63 : spZ regs <= 2 ^ 63) by lia.
assert (EEr : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew (Ereg regs []) i = getr regs r)
  by (intros i r Hi; exact (ew_Ereg_nat regs [] i r Hi)).
assert (EE2 : bv_unsigned (ew (Ereg regs []) 2) = spZ regs) by (rewrite (EEr 2%nat 2%bv eq_refl); reflexivity).
assert (EN : forall n0, (n0 < 32)%nat -> ew (Ereg regs []) n0 = getr regs (Z_to_bv 5 (Z.of_nat n0))).
{ intros n0 Hn0. apply ew_Ereg_nat. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
  rewrite Z.mod_small; lia. }
(* the caller's slots lie at or above the entry sp, so every step that changes only the window keeps them; with the
   spill read back from a state's stack region they are the argument words at sp - 0x30 *)
assert (XK : forall mem', (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - K <= a < spZ regs) ->
    aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
  words_at (aview tfibsegs (w_H W) mem') (spZ regs) xs).
{ intros mem' KEEP. apply (words_at_keep (aview tfibsegs (w_H W) mem)); [|exact Hxs].
  intros a Ha. apply KEEP; lia. }
assert (WS : forall mem', words_at (aview tfibsegs (w_H W) mem') (spZ regs - 48) (map (argZ regs) [2; 3; 4; 5; 6; 7]) ->
  words_at (aview tfibsegs (w_H W) mem') (spZ regs) xs ->
  words_at (aview tfibsegs (w_H W) mem') (spZ regs - 48) ws).
{ intros mem' Hsp Hx. rewrite Hwseq. apply words_at_app; [exact Hsp|].
  replace (spZ regs - 48 + 8 * Z.of_nat (length (map (argZ regs) [2; 3; 4; 5; 6; 7]))) with (spZ regs)
    by (rewrite length_map; cbn [length]; lia).
  exact Hx. }
assert (AW : spZ regs - 48 + 8 * Z.of_nat (length ws) = spZ regs + 8 * Z.of_nat (length xs)) by (rewrite Hlws; lia).
(* run 1: entry .. printf_common *)
eapply SRr_bind; [exact (icpt_phase_to W (Ereg regs []) A_PCOM fp_p0 fp_e1 RS_running ms md0 HS0 r_fp1)|].
intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & _).
assert (HS1' : st_ok tfibsegs (Ereg regs []) fp_e1 (restrict (w_H W) ms1)) by exact HS1. clear HS1.
set (md1 := with_vm_backing (m_vm_lazy md0) mat1 md0).
pose proof (fpr_run LAWS ly S W mem md (fun _ => False) (fun _ => False) K (spZ regs) (ms_mem ms) md0 (Ereg regs [])
  fp_p0 fp_e1
  ms1 mat1 HLO Hhi HSK HIM H63 F0 fp0_win fp1_stk EE2 HF1 HS1') as F1. fold md1 in F1.
pose proof F1 as (F1a & _ & F1p & F1f & F1m).
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - K <= a < spZ regs) ->
  aview tfibsegs (w_H W) (ms_mem ms1) a = aview tfibsegs (w_H W) mem a)
  by (intros a Ha Hn; exact (F1f a Ha Hn (fun X => X))).
pose proof (mf_keep rlo rhi link_vf_FF K LA_GOT_GUARD LA_GUARD ly S W mem md (ms_mem ms1) md1 (spZ regs) f fmt k fl om
  wend wpos wbase pos len pb ws T cval STAB HPRE F1a F1p KEEP1) as PRE1.
pose proof (WS _ (fp_spill W (Ereg regs []) fp_e1 ms1 fp_r1 regs (spZ regs) HS1' ltac:(rewrite fp1_mem; reflexivity)
  fp1_b EE2 fp1_slots EN) (XK _ KEEP1)) as Hws1.
assert (R1 : getr (ms_regs ms1) 1 = Z_to_bv 64 RA_PCOM_FPI) by exact (g_reg W _ fp_e1 ms1 1 _ HS1' fp1_ra).
assert (RA1 : raZ (ms_regs ms1) = RA_PCOM_FPI) by (unfold raZ; rewrite R1; apply unsigned_lit_small; unfold RA_PCOM_FPI; lia).
assert (Sp1 : spZ (ms_regs ms1) = spZ regs - 112).
{ unfold spZ at 1. rewrite (g_reg W _ fp_e1 ms1 2 _ HS1' fp1_sp). cbn [sv_denot]. rewrite EE2.
  rewrite unsigned_lit_small by lia. lia. }
assert (R13 : getr (ms_regs ms1) 3 = w64 (as_gp PcapB))
  by (rewrite (g_reg W _ fp_e1 ms1 3 _ HS1' fp1_r3), (sv_atom _ 3 regs 3 (EEr 3%nat 3%bv eq_refl)); exact G3).
assert (R14 : getr (ms_regs ms1) 4 = w64 (as_tp PcapB))
  by (rewrite (g_reg W _ fp_e1 ms1 4 _ HS1' fp1_r4), (sv_atom _ 4 regs 4 (EEr 4%nat 4%bv eq_refl)); exact G4).
assert (R111 : getr (ms_regs ms1) 11 = w64 fmt)
  by (rewrite (g_reg W _ fp_e1 ms1 11 _ HS1' fp1_r11), (sv_atom _ 11 regs 11 (EEr 11%nat 11%bv eq_refl)); exact G11).
assert (R112 : getr (ms_regs ms1) 12 = w64 (spZ regs - 48)).
{ rewrite (g_reg W _ fp_e1 ms1 12 _ HS1' fp1_r12). cbn [sv_denot]. rewrite EE2. reflexivity. }
pose proof (mf_pcom rlo rhi K 2320 LA_GOT_GUARD LA_GUARD ly S W (ms_mem ms1) md1 (spZ regs) (spZ (ms_regs ms1)) f fmt k
  fl om wend wpos wbase pos len pb ws T cval TB PRE1 ltac:(rewrite Sp1; lia) ltac:(rewrite Sp1; lia))
  as (Q1 & Q2 & Q3 & Q4).
assert (Hzd1 : zdisjoint (spZ regs - 48, 8 * Z.of_nat (length ws)) (spZ (ms_regs ms1) - 2320, 2320))
  by (unfold zdisjoint; cbn [fst snd]; rewrite Sp1; lia).
assert (Hap0 : 0 <= spZ regs - 48) by lia.
assert (Hap47 : spZ regs - 48 + 8 * Z.of_nat (length ws) <= 2 ^ 47) by lia.
(* call printf_common (ctx, fmt, aq) at sp - 0x70: the region's 16 bytes below the frame are the band, the rest of
   its window [sp - 0x70 - 2320, sp - SVRF) is XW *)
eapply SRr_bind.
{ apply (kcall W (Ereg regs []) fp_e1 ms1 md1 (spZ regs) SVRF fp_r1 fp_rest1 32 RA_PCOM_FPI (-112) 0 0 16
    (fun a => spZ regs - 112 - 2320 <= a < spZ regs - SVRF) (fun regs2 mem2 md2 => ARU tfibsegs PcapB ly S [] W mem2 md2)
    HS1' fp1_resv EE2 fp1_mem fp1_b fp1_lo fp1_hi ltac:(rewrite fp1_wlo; lia) ltac:(rewrite fp1_whi; lia) fp1_ra fp1_sp
    fp1_at fp1_wf fp1_nc fp1_ma fp1_ci);
    first [ lia
          | solve [intros a Hx Ha; cbv beta in Hx; lia]
          | solve [intros r a Hr Ha; destruct (ro_far_sound (Ereg regs []) _ r a fp1_far Hr) as [X _]; specialize (X Ha);
                   cbv beta; lia]
          | solve [intros r a Hr Ha; exfalso; destruct (ro_far_sound (Ereg regs []) _ r a fp1_far Hr) as [_ X]; exact (X Ha)]
          | solve [intros a Ha; apply F1p; lia]
          | idtac ].
  rewrite fp1_pc. eapply SRr_mono.
  { apply (LinkSnpPort.link_pcommon PcapB LAWS TB 2320 ltac:(lia) ly S [] W (ms_regs ms1) (ms_mem ms1) md1 fmt
      (spZ regs - 48) ws T);
      first [ assumption | lia | solve [intros a Ha; apply F1p; lia] | idtac ].
    apply (g_ecall_preU PcapB ly S [] W (ms_regs ms1) (ms_mem ms1) md1 F1a);
      first [ assumption | lia | solve [intros a Ha; apply F1p; lia] | solve [rewrite Sp1; exact H16']
            | solve [rewrite R1; apply ret_ok_lit; [unfold RA_PCOM_FPI; lia | reflexivity]] ]. }
  cbv beta. intros W' c' _ (-> & regs2 & mem2 & md2 & -> & HA2 & HP2' & Hsb2 & Hfr2 & Hpm2).
  split; [reflexivity|]. exists regs2, mem2, md2. rewrite RA1.
  split; [reflexivity|]. split; [exact HP2'|]. split; [exact Hsb2|].
  split; [intros a Ha Hn Hx; cbv beta in Hx; apply Hfr2; [exact Ha | rewrite Sp1; lia]|].
  split; [exact Hpm2 | exact HA2]. }
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & _ & Hfr2 & Hpm2 & HA2).
set (md2 := with_vm_backing (m_vm_lazy md1) mat2 md1) in *.
set (E2 := havoc (Ereg regs []) 32 (map (getr (ms_regs ms2)) CLOB)) in HS2.
assert (E2r : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> (i < 32)%nat -> ew E2 i = getr regs r).
{ intros i r Hi Hl. subst E2. rewrite ew_havoc_old by lia. exact (EEr i r Hi). }
assert (E22 : bv_unsigned (ew E2 2) = spZ regs) by (subst E2; rewrite ew_havoc_old by lia; exact EE2).
assert (E2N : forall n0, (n0 < 32)%nat -> ew E2 n0 = getr regs (Z_to_bv 5 (Z.of_nat n0))).
{ intros n0 Hn0. subst E2. rewrite ew_havoc_old by lia. exact (EN n0 Hn0). }
assert (F2 : sw_frame PcapB ly S [] W mem md (spZ regs - K) (spZ regs) (fun _ => False) (fun _ => False) (ms_mem ms2)
  md2).
{ apply (sw_step PcapB ly S [] W mem md _ _ _ _ (ms_mem ms1) md1 _ _ F1 HA2).
  - apply with_vm_backing_same.
  - intros a Ha. apply Hpm2. apply F1p. exact Ha.
  - intros a Ha Hn _. apply Hfr2; [exact Ha | lia | cbv beta; lia].
  - intros a _ Hpa _. exact (Hpm2 a Hpa). }
(* run 2: printf_common's return .. REAL (vfprintf) *)
eapply SRr_bind; [exact (icpt_phase_to W E2 A_VFP fp_s2 fp_e2 RS_running ms2 md2 HS2 r_fp2)|].
intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & _).
assert (HS3' : st_ok tfibsegs E2 fp_e2 (restrict (w_H W) ms3)) by exact HS3. clear HS3.
set (md3 := with_vm_backing (m_vm_lazy md2) mat3 md2).
pose proof (fpr_run LAWS ly S W mem md (fun _ => False) (fun _ => False) K (spZ regs) (ms_mem ms2) md2 E2 fp_s2 fp_e2
  ms3 mat3
  HLO Hhi HSK HIM H63 F2 fp2_win fp2_stk E22 HF3 HS3') as F3. fold md3 in F3.
pose proof F3 as (F3a & _ & F3p & F3f & F3m).
assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - K <= a < spZ regs) ->
  aview tfibsegs (w_H W) (ms_mem ms3) a = aview tfibsegs (w_H W) mem a)
  by (intros a Ha Hn; exact (F3f a Ha Hn (fun X => X))).
pose proof (mf_keep rlo rhi link_vf_FF K LA_GOT_GUARD LA_GUARD ly S W mem md (ms_mem ms3) md3 (spZ regs) f fmt k fl om
  wend wpos wbase pos len pb ws T cval STAB HPRE F3a F3p KEEP3) as PRE3.
pose proof (WS _ (fp_spill W E2 fp_e2 ms3 fp_r2 regs (spZ regs) HS3' ltac:(rewrite fp2_mem; reflexivity)
  fp2_b E22 fp2_slots E2N) (XK _ KEEP3)) as Hws3.
pose proof (st_ok_first E2 fp_e2 _ fp_r2 fp_rest2 HS3' fp2_mem) as HS3c. fold fp_c3 in HS3c.
assert (R31 : getr (ms_regs ms3) 1 = Z_to_bv 64 RA_FP) by exact (g_reg W _ fp_c3 ms3 1 _ HS3c fp3c_ra).
assert (RA3 : raZ (ms_regs ms3) = RA_FP) by (unfold raZ; rewrite R31; apply unsigned_lit_small; unfold RA_FP; lia).
assert (Sp3 : spZ (ms_regs ms3) = spZ regs - 112).
{ unfold spZ at 1. rewrite (g_reg W _ fp_c3 ms3 2 _ HS3c fp3c_sp). cbn [sv_denot]. rewrite E22.
  rewrite unsigned_lit_small by lia. lia. }
assert (R33 : getr (ms_regs ms3) 3 = w64 (as_gp PcapB))
  by (rewrite (g_reg W _ fp_c3 ms3 3 _ HS3c fp3c_r3), (sv_atom _ 3 regs 3 (E2r 3%nat 3%bv eq_refl ltac:(lia))); exact G3).
assert (R34 : getr (ms_regs ms3) 4 = w64 (as_tp PcapB))
  by (rewrite (g_reg W _ fp_c3 ms3 4 _ HS3c fp3c_r4), (sv_atom _ 4 regs 4 (E2r 4%nat 4%bv eq_refl ltac:(lia))); exact G4).
assert (R310 : getr (ms_regs ms3) 10 = w64 f)
  by (rewrite (g_reg W _ fp_c3 ms3 10 _ HS3c fp3c_r10), (sv_atom _ 10 regs 10 (E2r 10%nat 10%bv eq_refl ltac:(lia))); exact G10).
assert (R311 : getr (ms_regs ms3) 11 = w64 fmt)
  by (rewrite (g_reg W _ fp_c3 ms3 11 _ HS3c fp3c_r11), (sv_atom _ 11 regs 11 (E2r 11%nat 11%bv eq_refl ltac:(lia))); exact G11).
assert (R312 : getr (ms_regs ms3) 12 = w64 (spZ regs - 48)).
{ rewrite (g_reg W _ fp_c3 ms3 12 _ HS3c fp3c_r12). cbn [sv_denot]. rewrite E22. reflexivity. }
assert (Hret3 : YK0s.ret_ok (getr (ms_regs ms3) 1)) by (rewrite R31; apply ret_ok_lit; [unfold RA_FP; lia | reflexivity]).
(* musl vfprintf's premises at its window [sp - 0x70 - Kv, sp - 0x70), the argument words at sp - 0x30 *)
assert (PRE3s : mf_pre rlo rhi link_vf_FF Kv LA_GOT_GUARD LA_GUARD ly S W (ms_mem ms3) md3 (spZ (ms_regs ms3)) f fmt k
  fl om wend wpos wbase pos len pb ws T cval).
{ apply (mf_shrink rlo rhi link_vf_FF K Kv LA_GOT_GUARD LA_GUARD ly S W (ms_mem ms3) md3 (spZ regs) (spZ (ms_regs ms3))
    f fmt k fl om wend wpos wbase pos len pb ws T cval MONO PRE3); [lia | lia | exact HKv | rewrite Sp3; exact H16']. }
assert (Ad3 : Forall (zdisjoint (spZ regs - 48, 8 * Z.of_nat (length ws))) (vmf_out Kv (spZ (ms_regs ms3)) f)).
{ assert (HBLK : 0 < AMF_BLOCK) by reflexivity.
  apply Forall_vmf. unfold zdisjoint. cbn [fst snd]. rewrite Sp3, AW. split; lia. }
(* call musl vfprintf (f, fmt, va) at sp - 0x70: it returns at an FP state fx' *)
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E2 _ _ HS3c fp3c_resv) as Hshape3.
rewrite Hshape3, fp3c_pc.
apply (srr_fx_continue tfibsegs W _ (raZ (ms_regs ms3))
  (fun fx' regs' mem' md' => AR tfibsegs PcapB ly S W mem' md' /\ aregs_preserved (ms_regs ms3) regs' /\
     same_but_materialized md3 md' /\ getr regs' 10 = w64 (Z.of_nat (length T)) /\
     apf_file_post tfibsegs link_amf (mrestrict (w_H W) mem') f k pb T fl om wend pos len /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ (f <= a < f + AMF_BLOCK) ->
        ~ (spZ (ms_regs ms3) - Kv <= a < spZ (ms_regs ms3)) ->
        aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) (ms_mem ms3) a) /\
     (forall a, apresent (w_H W) (ms_mem ms3) a -> apresent (w_H W) mem' a))).
{ exact (mf_apply rlo rhi link_vf_FF Kv LA_GOT_GUARD LA_GUARD LA_VFPRINTF ly S W (ms_regs ms3) (ms_mem ms3) md3
    f fmt (spZ regs - 48) k fl om wend wpos wbase pos len pb ws T cval AVF PRE3s Hret3 R33 R34 R310 R311 R312 Hws3
    ltac:(rewrite Sp3; lia) Hap47 Ad3 Hfrm). }
intros fx' regs4 mem4 md4 Hf1 Hf2 (HA4 & HP4 & Hsb4 & H10 & HFP4 & Hfr4 & Hpm4).
rewrite RA3.
apply (proj2 (ARU_nil tfibsegs PcapB ly S W mem4 md4)) in HA4.
(* what musl vfprintf changed: the region's 16 bytes below the frame (the band), the rest of its window, the FILE *)
assert (FR4 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs + -112 - 16 <= a < spZ regs + -112) ->
  ~ ((spZ regs - 112 - Kv <= a < spZ regs - SVRF) \/ (f <= a < f + AMF_BLOCK)) ->
  aview tfibsegs (w_H W) mem4 a = aview tfibsegs (w_H W) (ms_mem ms3) a).
{ intros a Ha Hn Hx. apply Hfr4; [exact Ha | intros X; apply Hx; right; exact X | rewrite Sp3; lia]. }
set (E4 := havoc E2 48 (map (getr regs4) CLOB)).
(* the state after the call, at fx' *)
assert (HS4 : st_ok (fx:=fx') tfibsegs E4 (kafter 48 fp_c3 RA_FP (-112) 0 0)
  (restrict (w_H W) (mkst (fx:=fx') regs4 (Z_to_bv 64 RA_FP) mem4 (seg_rom tfibsegs)))).
{ apply (kcall_fx fx fx' W E2 fp_c3 ms3 (spZ regs) SVRF fp_r2 [] 48 RA_FP (-112) 0 0 16
    (fun a => (spZ regs - 112 - Kv <= a < spZ regs - SVRF) \/ (f <= a < f + AMF_BLOCK)) (fun _ => False) regs4 mem4
    HS3c fp3c_resv E22 fp3c_mem fp2_b fp2_lo fp2_hi ltac:(rewrite fp2_wlo; lia) ltac:(rewrite fp2_whi; lia)
    fp3c_at fp3c_wf fp3c_nc fp3c_ma fp3c_ci);
    first [ lia
          | solve [intros a Hx Ha; exfalso; cbv beta in Hx; lia]
          | solve [intros a Hx; destruct Hx]
          | solve [intros r a Hr; destruct Hr]
          | solve [intros a Ha; apply F3p; lia]
          | solve [intros a _ Hpa _; exact (Hpm4 a Hpa)]
          | exact HP4 | exact FR4 ]. }
assert (E4r : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> (i < 32)%nat -> ew E4 i = getr regs r).
{ intros i r Hi Hl. subst E4. rewrite ew_havoc_old by lia. exact (E2r i r Hi Hl). }
assert (E42 : bv_unsigned (ew E4 2) = spZ regs) by (subst E4; rewrite ew_havoc_old by lia; exact E22).
assert (F4 : sw_frame PcapB ly S [] W mem md (spZ regs - K) (spZ regs) (fun a => f <= a < f + AMF_BLOCK)
  (fun _ => False) mem4 md4).
{ apply (sw_step PcapB ly S [] W mem md _ _ _ _ (ms_mem ms3) md3 mem4 md4
    (sw_mono PcapB ly S [] W mem md _ _ (fun _ => False) (fun _ => False) _ _ _ _ F3 (fun a X => match X with end)
       (fun a X => match X with end)) HA4 Hsb4).
  - intros a Ha. apply Hpm4. apply F3p. exact Ha.
  - intros a Ha Hn Hx. cbv beta in Hx. apply FR4; [exact Ha | lia | intros [X|X]; [lia | exact (Hx X)]].
  - intros a _ Hpa _. exact (Hpm4 a Hpa). }
(* run 3: vfprintf's return .. ret, at fx' *)
unfold cfg_at, w64.
eapply SRr_bind; [exact (icpt_phase W E4 fp_s3 fp_e3 (RS_stopped (SR_jalr (SOff 1 0))) _ md4 HS4 r_fp3)|].
intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & _).
assert (HS5' : st_ok (fx:=fx') tfibsegs E4 fp_e3 (restrict (w_H W) ms5)) by exact HS5. clear HS5.
apply (fp_ret W E4 fp_e3 ms5 (with_vm_backing (m_vm_lazy md4) mat5 md4) _ HS5' fp3e_resv fp3e_ret).
intros mat'. rewrite (wvb_collapse (m_vm_lazy md4) mat' mat5 md4).
pose proof (fpr_run LAWS ly S W mem md (fun a => f <= a < f + AMF_BLOCK) (fun _ => False) K (spZ regs) mem4 md4 E4
  fp_s3 fp_e3
  ms5 mat' HLO Hhi HSK HIM H63 F4 fp3s_win fp3e_stk E42 HF5 HS5') as F5.
pose proof F5 as (F5a & F5s & _ & F5f & F5m).
assert (R51 : getr (ms_regs ms5) 1 = getr regs 1)
  by (rewrite (g_reg W _ fp_e3 ms5 1 _ HS5' fp3e_ra); exact (sv_atom _ 1 regs 1 (E4r 1%nat 1%bv eq_refl ltac:(lia)))).
assert (R510 : getr (ms_regs ms5) 10 = w64 (Z.of_nat (length T))).
{ rewrite (g_reg W _ fp_e3 ms5 10 _ HS5' fp3e_r10). cbn [sv_denot].
  pose proof (ew_havoc_new E2 48 (map (getr regs4) CLOB) 4 (Z_to_bv 64 0) ltac:(unfold CLOB; cbn [map length]; lia)) as X.
  cbn [Nat.add] in X. fold E4 in X. rewrite X. unfold CLOB. cbn [map nth]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
  exact H10. }
unfold vmf_post. split; [reflexivity|].
exists fx', (ms_regs ms5), (ms_mem ms5), (with_vm_backing (m_vm_lazy md4) mat' md4).
split.
{ unfold cfg_at. rewrite R51. unfold YK0s.ret_ok in Hra. rewrite Hra. unfold w64, raZ. rewrite Z_to_bv_bv_unsigned.
  reflexivity. }
split; [exact Hf1|]. split; [exact Hf2|].
split; [exact (proj1 (ARU_nil tfibsegs PcapB ly S W _ _) F5a)|].
split; [exact (vfi_preserved (w_H W) E4 fp_e3 ms5 regs HS5' fp3e_kept E4r)|].
split; [exact F5s|]. split; [exact R510|].
split.
{ apply (mf_post_keep W mem4 (ms_mem ms5) f k pb T fl om wend pos len Hlpb Hfit); [|exact HFP4].
  intros x Hx. apply (aview_same (w_H W) mem4 (ms_mem ms5) x). apply HF5. rewrite unsigned_lit_small by lia.
  intros Hw. pose proof (fpr_win_sound E4 _ _ fp3s_win Hw) as X. rewrite E42 in X. lia. }
split; [|exact (apresent_kept64 (w_H W) mem (ms_mem ms5) (fun a Ha Hpa => F5m a Ha Hpa (fun X => X)))].
intros a Ha Hn Hs. exact (F5f a Ha Hs Hn).
Qed.

(* ---- the contract at the body 0x46e48 ---- *)
Theorem fpi_mf_ok : forall K, 0x70 + Kv <= K -> 0x70 + 2320 <= K ->
  afprintf_mf_realizes tfibsegs PcapB link_amf rlo rhi link_vf_FF K LA_GOT_GUARD LA_GUARD LA_I_FPRINTF.
Proof.
intros K HKK HKP ly S W regs mem md f fmt k fl om wend wpos wbase pos len pb xs ws T cval HPRE HKlo HKp G10 G11
  Hblk Hpw Hk Hdyn Hpend Hlpb Hfit Hro Hgc Hgv XG1 XG2 XG3 XG4 Hgcd Hgvd Hfva H47x Xd HFF HT Hfrm.
change (SRr tfibsegs W (cfg_at tfibsegs LA_I_FPRINTF regs mem md)
  (vmf_post ly S W regs mem md K f k pb T fl om wend pos len)).
pose proof (mf_intro rlo rhi link_vf_FF K LA_GOT_GUARD LA_GUARD ly S W regs mem md f fmt k fl om wend wpos wbase pos
  len pb ws T cval ltac:(lia) HPRE HKlo HKp Hblk Hpw Hk Hdyn Hpend Hlpb Hfit Hro Hgc Hgv XG1 XG2 XG3 XG4 Hgcd Hgvd HFF
  HT) as P.
pose proof HPRE as (HAR & Hra & H16 & _ & Hhi & _ & G3 & G4).
pose proof P as (HA & _).
pose proof (stk_kHighMemBeg PcapB ly S _ (proj1 HAR)) as [K1 K2].
assert (HSVR : SVRF = 128) by reflexivity.
assert (KHB : kHighMemBeg = 0x10007fff8000) by reflexivity. assert (KHE : kHighMemEnd = 2 ^ 47) by reflexivity.
assert (Hp128 : forall a, spZ regs - SVRF <= a < spZ regs -> apresent (w_H W) mem a) by (intros a Ha; apply HKp; lia).
pose proof (fpi_entry_ok LA_I_FPRINTF ly S W regs mem md HA Hp128 H16 ltac:(lia) ltac:(lia)) as HS0.
pose proof (sw_init PcapB ly S [] W mem md (spZ regs - K) (spZ regs) (fun _ => False) (fun _ => False) HA HKp) as F0.
exact (fpi_from K ly S W regs mem md f fmt k fl om wend wpos wbase pos len pb xs ws T cval
  (mkst regs (Z_to_bv 64 LA_I_FPRINTF) mem (seg_rom tfibsegs)) md HKK HKP P Hfva H47x Xd Hfrm Hra G3 G4 G10 G11 HS0 F0).
Qed.

(* ---- the contract at the trampoline 0x43084: its `j` is the first step of the same walk ---- *)
Theorem fpi_mf_ok_w : forall K, 0x70 + Kv <= K -> 0x70 + 2320 <= K ->
  afprintf_mf_realizes tfibsegs PcapB link_amf rlo rhi link_vf_FF K LA_GOT_GUARD LA_GUARD LA_W_FPRINTF.
Proof.
intros K HKK HKP ly S W regs mem md f fmt k fl om wend wpos wbase pos len pb xs ws T cval HPRE HKlo HKp G10 G11
  Hblk Hpw Hk Hdyn Hpend Hlpb Hfit Hro Hgc Hgv XG1 XG2 XG3 XG4 Hgcd Hgvd Hfva H47x Xd HFF HT Hfrm.
change (SRr tfibsegs W (cfg_at tfibsegs LA_W_FPRINTF regs mem md)
  (vmf_post ly S W regs mem md K f k pb T fl om wend pos len)).
pose proof (mf_intro rlo rhi link_vf_FF K LA_GOT_GUARD LA_GUARD ly S W regs mem md f fmt k fl om wend wpos wbase pos
  len pb ws T cval ltac:(lia) HPRE HKlo HKp Hblk Hpw Hk Hdyn Hpend Hlpb Hfit Hro Hgc Hgv XG1 XG2 XG3 XG4 Hgcd Hgvd HFF
  HT) as P.
pose proof HPRE as (HAR & Hra & H16 & _ & Hhi & _ & G3 & G4).
pose proof P as (HA & _).
pose proof (stk_kHighMemBeg PcapB ly S _ (proj1 HAR)) as [K1 K2].
assert (HSVR : SVRF = 128) by reflexivity. assert (HIE : TFIB_IMG_END < kHighMemBeg) by reflexivity.
assert (KHB : kHighMemBeg = 0x10007fff8000) by reflexivity. assert (KHE : kHighMemEnd = 2 ^ 47) by reflexivity.
assert (Hp128 : forall a, spZ regs - SVRF <= a < spZ regs -> apresent (w_H W) mem a) by (intros a Ha; apply HKp; lia).
pose proof (fpi_entry_ok LA_W_FPRINTF ly S W regs mem md HA Hp128 H16 ltac:(lia) ltac:(lia)) as HT0.
pose proof (sw_init PcapB ly S [] W mem md (spZ regs - K) (spZ regs) (fun _ => False) (fun _ => False) HA HKp) as F0.
assert (EE2 : bv_unsigned (ew (Ereg regs []) 2) = spZ regs) by (rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl); reflexivity).
unfold cfg_at, w64.
eapply SRr_bind; [exact (icpt_phase_to W (Ereg regs []) LA_I_FPRINTF fpw_t0 fp_p0 RS_running _ md HT0 r_fpw)|].
intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & _).
assert (HS1' : st_ok tfibsegs (Ereg regs []) fp_p0 (restrict (w_H W) ms1)) by exact HS1. clear HS1.
pose proof (fpr_run LAWS ly S W mem md (fun _ => False) (fun _ => False) K (spZ regs) mem md (Ereg regs []) fpw_t0
  fp_p0 ms1 mat1
  ltac:(lia) Hhi ltac:(lia) ltac:(lia) ltac:(lia) F0 fpw_win fp0_stk EE2 HF1 HS1') as F1.
exact (fpi_from K ly S W regs mem md f fmt k fl om wend wpos wbase pos len pb xs ws T cval
  ms1 _ HKK HKP P Hfva H47x Xd Hfrm Hra G3 G4 G10 G11 HS1' F1).
Qed.

(* at the window 0x70 + Kv *)
Corollary fpi_mf_ok_win : 2320 <= Kv ->
  afprintf_mf_realizes tfibsegs PcapB link_amf rlo rhi link_vf_FF (0x70 + Kv) LA_GOT_GUARD LA_GUARD LA_I_FPRINTF /\
  afprintf_mf_realizes tfibsegs PcapB link_amf rlo rhi link_vf_FF (0x70 + Kv) LA_GOT_GUARD LA_GUARD LA_W_FPRINTF.
Proof. intros H. split; [apply fpi_mf_ok | apply fpi_mf_ok_w]; lia. Qed.
End v.

(* ---- at musl vfprintf's GXA window LVF_MUSL_STK = 5552: the body's window LFP_STK = 0x70 + 5552 ---- *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Corollary fpi_mf_ok_stk : AR_laws tfibsegs PcapB -> PcapSyms PcapB -> forall rlo rhi,
  avfprintf_mf_realizes tfibsegs PcapB link_amf rlo rhi link_vf_FF LVF_MUSL_STK LA_GOT_GUARD LA_GUARD LA_VFPRINTF ->
  afprintf_mf_realizes tfibsegs PcapB link_amf rlo rhi link_vf_FF LFP_STK LA_GOT_GUARD LA_GUARD LA_I_FPRINTF /\
  afprintf_mf_realizes tfibsegs PcapB link_amf rlo rhi link_vf_FF LFP_STK LA_GOT_GUARD LA_GUARD LA_W_FPRINTF.
Proof.
intros LAWS TB rlo rhi AVF.
exact (fpi_mf_ok_win rlo rhi LVF_MUSL_STK LAWS TB ltac:(unfold ESTACK, LVF_MUSL_STK; lia) AVF
  ltac:(unfold LVF_MUSL_STK; lia)).
Qed.

(* ---- at link's instance: PcapB's laws (YG0q.AR_laws_ok) and symbols (AD2l.PcapB_syms) ---- *)
Corollary fpi_mf_ok_PcapB : forall rlo rhi Kv, ESTACK <= Kv ->
  avfprintf_mf_realizes tfibsegs PcapB link_amf rlo rhi link_vf_FF Kv LA_GOT_GUARD LA_GUARD LA_VFPRINTF ->
  forall K, 0x70 + Kv <= K -> 0x70 + 2320 <= K ->
  afprintf_mf_realizes tfibsegs PcapB link_amf rlo rhi link_vf_FF K LA_GOT_GUARD LA_GUARD LA_I_FPRINTF.
Proof.
intros rlo rhi Kv HKv AVF.
exact (fpi_mf_ok rlo rhi Kv (YG0q.AR_laws_ok tfibsegs PcapB) PcapB_syms HKv AVF).
Qed.
Corollary fpi_mf_ok_w_PcapB : forall rlo rhi Kv, ESTACK <= Kv ->
  avfprintf_mf_realizes tfibsegs PcapB link_amf rlo rhi link_vf_FF Kv LA_GOT_GUARD LA_GUARD LA_VFPRINTF ->
  forall K, 0x70 + Kv <= K -> 0x70 + 2320 <= K ->
  afprintf_mf_realizes tfibsegs PcapB link_amf rlo rhi link_vf_FF K LA_GOT_GUARD LA_GUARD LA_W_FPRINTF.
Proof.
intros rlo rhi Kv HKv AVF.
exact (fpi_mf_ok_w rlo rhi Kv (YG0q.AR_laws_ok tfibsegs PcapB) PcapB_syms HKv AVF).
Qed.
Corollary fpi_mf_ok_stk_PcapB : forall rlo rhi,
  avfprintf_mf_realizes tfibsegs PcapB link_amf rlo rhi link_vf_FF LVF_MUSL_STK LA_GOT_GUARD LA_GUARD LA_VFPRINTF ->
  afprintf_mf_realizes tfibsegs PcapB link_amf rlo rhi link_vf_FF LFP_STK LA_GOT_GUARD LA_GUARD LA_I_FPRINTF /\
  afprintf_mf_realizes tfibsegs PcapB link_amf rlo rhi link_vf_FF LFP_STK LA_GOT_GUARD LA_GUARD LA_W_FPRINTF.
Proof. exact (fpi_mf_ok_stk (YG0q.AR_laws_ok tfibsegs PcapB) PcapB_syms). Qed.
End s.
