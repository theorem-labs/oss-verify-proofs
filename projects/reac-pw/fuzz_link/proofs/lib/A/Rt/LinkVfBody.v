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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Rt/LinkFpBody.v, with its addresses and numbers changed; 138 of its 382 lines of code are new or changed and 317 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A (the asan build, pin 059dae63e07c): ___interceptor_vfprintf 0x46a7c (frame 0x30) and its
   trampoline __interceptor_trampoline_vfprintf 0x4307c (`j 0x46a7c`) on link's memory FILE, at the contract
   LinkVfDefs.avfprintf_mf_realizes (link's family link_vf_FF, the guard cells LA_GOT_GUARD -> LA_GUARD, every rlo rhi),
   from
   - musl vfprintf's contract at 0x973e0, the same form at a window Kv (the Section hypothesis AVF; the seam lane proves
     it at Kv = LVF_MUSL_STK);
   - printf_common's contract at 0x45fb4 for link's pieces (LinkSnpPort.link_pcommon, window 2320, read-only image
     PCM_CR, whose consts_view LinkVfBundle.mf_pcom derives from arodata_okP and AR).
   The walk is FMsnprintfSvfi.v svfi_ok over the same code: its symbolic runs u0 .. u3 at 0x46a7c (a stack
   region of SVR = 64 bytes: the frame 0x30 and TryAsanInitFromRtl's 0x10 below it; TryAsanInitFromRtl's fast path,
   asan_inited = 1; check_printf = 1; REAL (vfprintf) read from 0xa3738 = 0x973e0), their shape facts and svfi_run are
   Required, not re-run; only the premise bundle is the memory FILE's (LinkVfBundle.v), where the donor carried
   vsnprintf's string FILE. The trampoline is one run of the same table from 0x4307c to 0x46a7c, which ends at u0.
   The bound the donor asks is kept: ESTACK <= Kv. AR form throughout (the kit at U = [], ARU_nil).
   Written new (no image-derived numeral is copied: the runs and SVR are Required from FMsnprintfSvfi.v). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import FMsnprintfSk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import FMsnprintfGk0 FMsnprintfGt0 FMsnprintfGvfi0.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import FMsnprintfSvfi.
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

(* ---- the trampoline: one step of the same table from 0x4307c ends at u0 ---- *)
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition vfw_t0 : sstate := mkSS LA_W_VFPRINTF sr_atoms svr_mem None vfi_facts.
Lemma r_vfw : sym_run_toN tfibsegs tbl_g FUEL A_VFPI vfw_t0 = (u0, RS_running). Proof. vm_compute. reflexivity. Qed.
Lemma vfw_win : svr_win (ss_mem vfw_t0) = true. Proof. vm_compute. reflexivity. Qed.
Lemma u0_stk : svr_stk0 (ss_mem u0) = true. Proof. vm_compute. reflexivity. Qed.
End r.

Section v. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variables rlo rhi Kv : Z.
Hypothesis LAWS : AR_laws tfibsegs PcapB.
Hypothesis TB : PcapSyms PcapB.
Hypothesis HKv : ESTACK <= Kv.
(* musl vfprintf's contract on link's memory FILE (the interface with the seam lane) *)
Hypothesis AVF :
  avfprintf_mf_realizes tfibsegs PcapB link_amf rlo rhi link_vf_FF Kv LA_GOT_GUARD LA_GUARD LA_VFPRINTF.

(* the walk's entry state at pc (the body 0x46a7c or the trampoline 0x4307c): the stack region [sp - 64, sp) present,
   the image cells vfi_rodata from AR's constant law *)
Lemma vfi_entry_ok : forall pc ly S W regs mem md,
  ARU tfibsegs PcapB ly S [] W mem md ->
  (forall a, spZ regs - SVR <= a < spZ regs -> apresent (w_H W) mem a) ->
  spZ regs mod 16 = 0 -> 2 ^ 44 <= spZ regs - SVR -> spZ regs <= 2 ^ 47 ->
  st_ok tfibsegs (Ereg regs []) (mkSS pc sr_atoms svr_mem None vfi_facts)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs))).
Proof.
intros pc ly S W regs mem md HA Hp H16 Hlo Hhi.
assert (HSVR : SVR = 64) by reflexivity.
assert (EE2 : bv_unsigned (ew (Ereg regs []) 2) = spZ regs) by (rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl); reflexivity).
rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor.
  + unfold svr_stk. apply (region_ok_stack tfibsegs (Ereg regs []) _ 2 (spZ regs) (- SVR)); [exact EE2 | lia | lia |].
    intros a Ha. apply apresent_writable. apply Hp. lia.
  + apply (vfi_ro_region_low vfi_rodata (Ereg regs []) (mrestrict (w_H W) (unpoison [] mem))); [vm_compute; reflexivity | |].
    * intros w Hw. unfold mrestrict. rewrite (ARU_mem_low tfibsegs PcapB ly S [] W mem md w HA Hw). reflexivity.
    * exact (rodata_ok PcapB TB vfi_rodata ly S (w_H W) (unpoison [] mem) (Ereg regs []) (vfi_rodata_chk ly)
        (ARU_ARm tfibsegs PcapB ly S [] W mem md HA)).
- apply pairwise_disjoint_of_extents. unfold svr_mem, svr_stk, vfi_rodata, icpt_rodata, ro_region, extent_of_region.
  cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite EE2.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. unfold vfi_facts. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite EE2. change (2 ^ 4) with 16. split; [|exact I]. split; [lia|]. split; [exact H16 | lia].
Qed.

(* the walk from a state that holds u0 (the body's entry), with the frame of the window [sp - K, sp) since the
   contract's entry (regs, mem, md) *)
Lemma vfi_from : forall K ly S W regs mem md f fmt ap k fl om wend wpos wbase pos len pb ws T cval ms md0,
  0x30 + Kv <= K -> 0x30 + 2320 <= K ->
  mf_pre rlo rhi link_vf_FF K LA_GOT_GUARD LA_GUARD ly S W mem md (spZ regs) f fmt k fl om wend wpos wbase pos len
    pb ws T cval ->
  words_at (aview tfibsegs (w_H W) mem) ap ws -> spZ regs <= ap -> ap + 8 * Z.of_nat (length ws) <= 2 ^ 47 ->
  Forall (zdisjoint (ap, 8 * Z.of_nat (length ws))) (vmf_out K (spZ regs) f) ->
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  YK0s.ret_ok (getr regs 1) -> getr regs 3 = w64 (as_gp PcapB) -> getr regs 4 = w64 (as_tp PcapB) ->
  getr regs 10 = w64 f -> getr regs 11 = w64 fmt -> getr regs 12 = w64 ap ->
  st_ok tfibsegs (Ereg regs []) u0 (restrict (w_H W) ms) ->
  sw_frame PcapB ly S [] W mem md (spZ regs - K) (spZ regs) (fun _ => False) (fun _ => False) (ms_mem ms) md0 ->
  SRr tfibsegs W (mkCfg ms md0) (vmf_post ly S W regs mem md K f k pb T fl om wend pos len).
Proof.
intros K ly S W regs mem md f fmt ap k fl om wend wpos wbase pos len pb ws T cval ms md0 HKK HKP HPRE Hws Hsap H47 Ad
  Hfrm Hra G3 G4 G10 G11 G12 HS0 F0.
pose proof (FMsnprintfFmI.FF_fmP_stable64 pf_link_piece) as STAB.
pose proof (FMsnprintfFmI.FF_fmP_mono pf_link_piece) as MONO.
assert (HES : ESTACK = 4096) by reflexivity.
pose proof HPRE as (HA & Hlo & Hhi & H16 & HK & Hp & Hblk & Hpw & Hk & Hdyn & Hpend & Hlpb & Hfit & Hro & Hgc & Hgv &
  XG1 & XG2 & XG3 & XG4 & Hgcd & Hgvd & HFF & HT).
pose proof (stk_kHighMemBeg PcapB ly S _ (ARU_ARm tfibsegs PcapB ly S [] W mem md HA)) as [K1 K2].
assert (HSVR : SVR = 64) by reflexivity. assert (HIE : TFIB_IMG_END < kHighMemBeg) by reflexivity.
assert (KHB : kHighMemBeg = 0x10007fff8000) by reflexivity. assert (KHE : kHighMemEnd = 2 ^ 47) by reflexivity.
pose proof Hpw as P1. apply pairwise_vmf in P1. unfold zdisjoint in P1. cbn [fst snd] in P1.
pose proof (amf_k_range _ f k Hk) as [FB0 FB1].
assert (H16' : (spZ regs - 48) mod 16 = 0).
{ rewrite <- (Z_mod_plus_full (spZ regs - 48) 3 16). replace (spZ regs - 48 + 3 * 16) with (spZ regs) by lia. exact H16. }
assert (HLO : ly_stk_lo ly <= spZ regs - K) by lia.
assert (HIM : TFIB_IMG_END <= spZ regs - K) by lia.
assert (HSK : SVR <= K) by lia.
assert (H63 : spZ regs <= 2 ^ 63) by lia.
assert (EEr : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew (Ereg regs []) i = getr regs r)
  by (intros i r Hi; exact (ew_Ereg_nat regs [] i r Hi)).
assert (EE2 : bv_unsigned (ew (Ereg regs []) 2) = spZ regs) by (rewrite (EEr 2%nat 2%bv eq_refl); reflexivity).
(* the argument words lie at or above the entry sp, so every step that changes only the window keeps them *)
assert (WK : forall mem', (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - K <= a < spZ regs) ->
    aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
  words_at (aview tfibsegs (w_H W) mem') ap ws).
{ intros mem' KEEP. apply (words_at_keep (aview tfibsegs (w_H W) mem)); [|exact Hws].
  intros a Ha. apply KEEP; lia. }
(* run 1: entry .. printf_common *)
eapply SRr_bind; [exact (g_phase_to W (Ereg regs []) A_PCOM u0 u1_e RS_running ms md0 HS0 r_u1)|].
intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1).
assert (HS1' : st_ok tfibsegs (Ereg regs []) u1_e (restrict (w_H W) ms1)) by exact HS1. clear HS1.
set (md1 := with_vm_backing (m_vm_lazy md0) mat1 md0).
pose proof (svfi_run PcapB LAWS ly S [] W mem md (fun _ => False) (fun _ => False) K (spZ regs) (ms_mem ms) md0
  (Ereg regs []) u0 u1_e
  ms1 mat1 HLO Hhi HSK HIM H63 F0 u0_win u1_stk EE2 HF1 HS1') as F1. fold md1 in F1.
pose proof F1 as (F1a & _ & F1p & F1f & F1m).
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - K <= a < spZ regs) ->
  aview tfibsegs (w_H W) (ms_mem ms1) a = aview tfibsegs (w_H W) mem a)
  by (intros a Ha Hn; exact (F1f a Ha Hn (fun X => X))).
pose proof (mf_keep rlo rhi link_vf_FF K LA_GOT_GUARD LA_GUARD ly S W mem md (ms_mem ms1) md1 (spZ regs) f fmt k fl om
  wend wpos wbase pos len pb ws T cval STAB HPRE F1a F1p KEEP1) as PRE1.
pose proof (WK _ KEEP1) as Hws1.
assert (R1 : getr (ms_regs ms1) 1 = Z_to_bv 64 RA_PCOM_VFPI) by exact (g_reg W _ u1_e ms1 1 _ HS1' u1_ra).
assert (RA1 : raZ (ms_regs ms1) = RA_PCOM_VFPI) by (unfold raZ; rewrite R1; apply unsigned_lit_small; unfold RA_PCOM_VFPI; lia).
assert (Sp1 : spZ (ms_regs ms1) = spZ regs - 48).
{ unfold spZ at 1. rewrite (g_reg W _ u1_e ms1 2 _ HS1' u1_sp). cbn [sv_denot]. rewrite EE2.
  rewrite unsigned_lit_small by lia. lia. }
assert (R13 : getr (ms_regs ms1) 3 = w64 (as_gp PcapB))
  by (rewrite (g_reg W _ u1_e ms1 3 _ HS1' u1_r3), (sv_atom _ 3 regs 3 (EEr 3%nat 3%bv eq_refl)); exact G3).
assert (R14 : getr (ms_regs ms1) 4 = w64 (as_tp PcapB))
  by (rewrite (g_reg W _ u1_e ms1 4 _ HS1' u1_r4), (sv_atom _ 4 regs 4 (EEr 4%nat 4%bv eq_refl)); exact G4).
assert (R111 : getr (ms_regs ms1) 11 = w64 fmt)
  by (rewrite (g_reg W _ u1_e ms1 11 _ HS1' u1_r11), (sv_atom _ 11 regs 11 (EEr 11%nat 11%bv eq_refl)); exact G11).
assert (R112 : getr (ms_regs ms1) 12 = w64 ap)
  by (rewrite (g_reg W _ u1_e ms1 12 _ HS1' u1_r12), (sv_atom _ 12 regs 12 (EEr 12%nat 12%bv eq_refl)); exact G12).
pose proof (mf_pcom rlo rhi K 2320 LA_GOT_GUARD LA_GUARD ly S W (ms_mem ms1) md1 (spZ regs) (spZ (ms_regs ms1)) f fmt k
  fl om wend wpos wbase pos len pb ws T cval TB PRE1 ltac:(rewrite Sp1; lia) ltac:(rewrite Sp1; lia))
  as (Q1 & Q2 & Q3 & Q4).
assert (Hzd1 : zdisjoint (ap, 8 * Z.of_nat (length ws)) (spZ (ms_regs ms1) - 2320, 2320))
  by (unfold zdisjoint; cbn [fst snd]; rewrite Sp1; lia).
assert (Hap0 : 0 <= ap) by lia.
(* call printf_common (ctx, fmt, aq) at sp - 0x30: the region's 16 bytes below the frame are the band, the rest of
   its window [sp - 0x30 - 2320, sp - SVR) is XW *)
eapply SRr_bind.
{ apply (kcall W (Ereg regs []) u1_e ms1 md1 (spZ regs) SVR u1_r0 u1_rest 32 RA_PCOM_VFPI (-48) 0 0 16
    (fun a => spZ regs - 48 - 2320 <= a < spZ regs - SVR) (fun regs2 mem2 md2 => ARU tfibsegs PcapB ly S [] W mem2 md2)
    HS1' u1_resv EE2 u1_mem u1_b u1_lo u1_hi ltac:(rewrite u1_wlo; lia) ltac:(rewrite u1_whi; lia) u1_ra u1_sp
    u1_at u1_wf u1_nc u1_ma u1_ci);
    first [ lia
          | solve [intros a Hx Ha; cbv beta in Hx; lia]
          | solve [intros r a Hr Ha; destruct (ro_far_sound (Ereg regs []) _ r a u1_far Hr) as [X _]; specialize (X Ha);
                   cbv beta; lia]
          | solve [intros r a Hr Ha; exfalso; destruct (ro_far_sound (Ereg regs []) _ r a u1_far Hr) as [_ X]; exact (X Ha)]
          | solve [intros a Ha; apply F1p; lia]
          | idtac ].
  rewrite u1_pc. eapply SRr_mono.
  { apply (LinkSnpPort.link_pcommon PcapB LAWS TB 2320 ltac:(lia) ly S [] W (ms_regs ms1) (ms_mem ms1) md1 fmt ap ws T);
      first [ assumption | lia | solve [intros a Ha; apply F1p; lia] | idtac ].
    apply (g_ecall_preU PcapB ly S [] W (ms_regs ms1) (ms_mem ms1) md1 F1a);
      first [ assumption | lia | solve [intros a Ha; apply F1p; lia] | solve [rewrite Sp1; exact H16']
            | solve [rewrite R1; apply ret_ok_lit; [unfold RA_PCOM_VFPI; lia | reflexivity]] ]. }
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
assert (F2 : sw_frame PcapB ly S [] W mem md (spZ regs - K) (spZ regs) (fun _ => False) (fun _ => False) (ms_mem ms2)
  md2).
{ apply (sw_step PcapB ly S [] W mem md _ _ _ _ (ms_mem ms1) md1 _ _ F1 HA2).
  - apply with_vm_backing_same.
  - intros a Ha. apply Hpm2. apply F1p. exact Ha.
  - intros a Ha Hn _. apply Hfr2; [exact Ha | lia | cbv beta; lia].
  - intros a _ Hpa _. exact (Hpm2 a Hpa). }
(* run 2: printf_common's return .. REAL (vfprintf) *)
eapply SRr_bind; [exact (g_phase_to W E2 A_VFP u2_s u2_e RS_running ms2 md2 HS2 r_u2)|].
intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3).
assert (HS3' : st_ok tfibsegs E2 u2_e (restrict (w_H W) ms3)) by exact HS3. clear HS3.
set (md3 := with_vm_backing (m_vm_lazy md2) mat3 md2).
pose proof (svfi_run PcapB LAWS ly S [] W mem md (fun _ => False) (fun _ => False) K (spZ regs) (ms_mem ms2) md2 E2
  u2_s u2_e ms3 mat3
  HLO Hhi HSK HIM H63 F2 u2_win u2_stk E22 HF3 HS3') as F3. fold md3 in F3.
pose proof F3 as (F3a & _ & F3p & F3f & F3m).
assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - K <= a < spZ regs) ->
  aview tfibsegs (w_H W) (ms_mem ms3) a = aview tfibsegs (w_H W) mem a)
  by (intros a Ha Hn; exact (F3f a Ha Hn (fun X => X))).
pose proof (mf_keep rlo rhi link_vf_FF K LA_GOT_GUARD LA_GUARD ly S W mem md (ms_mem ms3) md3 (spZ regs) f fmt k fl om
  wend wpos wbase pos len pb ws T cval STAB HPRE F3a F3p KEEP3) as PRE3.
pose proof (WK _ KEEP3) as Hws3.
pose proof (st_ok_first E2 u2_e _ u2_r0 u2_rest HS3' u2_mem) as HS3c. fold u3_c in HS3c.
assert (R31 : getr (ms_regs ms3) 1 = Z_to_bv 64 RA_VFP) by exact (g_reg W _ u3_c ms3 1 _ HS3c u3c_ra).
assert (RA3 : raZ (ms_regs ms3) = RA_VFP) by (unfold raZ; rewrite R31; apply unsigned_lit_small; unfold RA_VFP; lia).
assert (Sp3 : spZ (ms_regs ms3) = spZ regs - 48).
{ unfold spZ at 1. rewrite (g_reg W _ u3_c ms3 2 _ HS3c u3c_sp). cbn [sv_denot]. rewrite E22.
  rewrite unsigned_lit_small by lia. lia. }
assert (R33 : getr (ms_regs ms3) 3 = w64 (as_gp PcapB))
  by (rewrite (g_reg W _ u3_c ms3 3 _ HS3c u3c_r3), (sv_atom _ 3 regs 3 (E2r 3%nat 3%bv eq_refl ltac:(lia))); exact G3).
assert (R34 : getr (ms_regs ms3) 4 = w64 (as_tp PcapB))
  by (rewrite (g_reg W _ u3_c ms3 4 _ HS3c u3c_r4), (sv_atom _ 4 regs 4 (E2r 4%nat 4%bv eq_refl ltac:(lia))); exact G4).
assert (R310 : getr (ms_regs ms3) 10 = w64 f)
  by (rewrite (g_reg W _ u3_c ms3 10 _ HS3c u3c_r10), (sv_atom _ 10 regs 10 (E2r 10%nat 10%bv eq_refl ltac:(lia))); exact G10).
assert (R311 : getr (ms_regs ms3) 11 = w64 fmt)
  by (rewrite (g_reg W _ u3_c ms3 11 _ HS3c u3c_r11), (sv_atom _ 11 regs 11 (E2r 11%nat 11%bv eq_refl ltac:(lia))); exact G11).
assert (R312 : getr (ms_regs ms3) 12 = w64 ap)
  by (rewrite (g_reg W _ u3_c ms3 12 _ HS3c u3c_r12), (sv_atom _ 12 regs 12 (E2r 12%nat 12%bv eq_refl ltac:(lia))); exact G12).
assert (Hret3 : YK0s.ret_ok (getr (ms_regs ms3) 1)) by (rewrite R31; apply ret_ok_lit; [unfold RA_VFP; lia | reflexivity]).
(* musl vfprintf's premises at its window [sp - 0x30 - Kv, sp - 0x30) *)
assert (PRE3s : mf_pre rlo rhi link_vf_FF Kv LA_GOT_GUARD LA_GUARD ly S W (ms_mem ms3) md3 (spZ (ms_regs ms3)) f fmt k
  fl om wend wpos wbase pos len pb ws T cval).
{ apply (mf_shrink rlo rhi link_vf_FF K Kv LA_GOT_GUARD LA_GUARD ly S W (ms_mem ms3) md3 (spZ regs) (spZ (ms_regs ms3))
    f fmt k fl om wend wpos wbase pos len pb ws T cval MONO PRE3); [lia | lia | exact HKv | rewrite Sp3; exact H16']. }
assert (Ad3 : Forall (zdisjoint (ap, 8 * Z.of_nat (length ws))) (vmf_out Kv (spZ (ms_regs ms3)) f)).
{ pose proof Ad as Ad'. apply Forall_vmf in Ad' as [AD1 AD2]. apply Forall_vmf. split; [|exact AD2].
  unfold zdisjoint in *. cbn [fst snd] in *. rewrite Sp3. lia. }
(* call musl vfprintf (f, fmt, ap) at sp - 0x30: it returns at an FP state fx'. Nothing before it touched the FP
   state, so the walk's frm0_entry is its own; the arguments lie above sp >= sp - 0x30 *)
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E2 _ _ HS3c u3c_resv) as Hshape3.
rewrite Hshape3, u3c_pc.
apply (srr_fx_continue tfibsegs W _ (raZ (ms_regs ms3))
  (fun fx' regs' mem' md' => AR tfibsegs PcapB ly S W mem' md' /\ aregs_preserved (ms_regs ms3) regs' /\
     same_but_materialized md3 md' /\ getr regs' 10 = w64 (Z.of_nat (length T)) /\
     apf_file_post tfibsegs link_amf (mrestrict (w_H W) mem') f k pb T fl om wend pos len /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ (f <= a < f + AMF_BLOCK) ->
        ~ (spZ (ms_regs ms3) - Kv <= a < spZ (ms_regs ms3)) ->
        aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) (ms_mem ms3) a) /\
     (forall a, apresent (w_H W) (ms_mem ms3) a -> apresent (w_H W) mem' a))).
{ exact (mf_apply rlo rhi link_vf_FF Kv LA_GOT_GUARD LA_GUARD LA_VFPRINTF ly S W (ms_regs ms3) (ms_mem ms3) md3
    f fmt ap k fl om wend wpos wbase pos len pb ws T cval AVF PRE3s Hret3 R33 R34 R310 R311 R312 Hws3
    ltac:(rewrite Sp3; lia) H47 Ad3 Hfrm). }
intros fx' regs4 mem4 md4 Hf1 Hf2 (HA4 & HP4 & Hsb4 & H10 & HFP4 & Hfr4 & Hpm4).
rewrite RA3.
apply (proj2 (ARU_nil tfibsegs PcapB ly S W mem4 md4)) in HA4.
(* what musl vfprintf changed: the region's 16 bytes below the frame (the band), the rest of its window, the FILE *)
assert (FR4 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs + -48 - 16 <= a < spZ regs + -48) ->
  ~ ((spZ regs - 48 - Kv <= a < spZ regs - SVR) \/ (f <= a < f + AMF_BLOCK)) ->
  aview tfibsegs (w_H W) mem4 a = aview tfibsegs (w_H W) (ms_mem ms3) a).
{ intros a Ha Hn Hx. apply Hfr4; [exact Ha | intros X; apply Hx; right; exact X | rewrite Sp3; lia]. }
set (E4 := havoc E2 48 (map (getr regs4) CLOB)).
(* the state after the call, at fx' *)
assert (HS4 : st_ok (fx:=fx') tfibsegs E4 (kafter 48 u3_c RA_VFP (-48) 0 0)
  (restrict (w_H W) (mkst (fx:=fx') regs4 (Z_to_bv 64 RA_VFP) mem4 (seg_rom tfibsegs)))).
{ apply (kcall_fx fx fx' W E2 u3_c ms3 (spZ regs) SVR u2_r0 [] 48 RA_VFP (-48) 0 0 16
    (fun a => (spZ regs - 48 - Kv <= a < spZ regs - SVR) \/ (f <= a < f + AMF_BLOCK)) (fun _ => False) regs4 mem4
    HS3c u3c_resv E22 u3c_mem u2_b u2_lo u2_hi ltac:(rewrite u2_wlo; lia) ltac:(rewrite u2_whi; lia)
    u3c_at u3c_wf u3c_nc u3c_ma u3c_ci);
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
eapply SRr_bind; [exact (g_phase W E4 u3_s u3_e (RS_stopped (SR_jalr (SOff 1 0))) _ md4 HS4 r_u3)|].
intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5).
assert (HS5' : st_ok (fx:=fx') tfibsegs E4 u3_e (restrict (w_H W) ms5)) by exact HS5. clear HS5.
apply (g_ret W E4 u3_e ms5 (with_vm_backing (m_vm_lazy md4) mat5 md4) _ HS5' u3e_resv u3e_ret).
intros mat'. rewrite (wvb_collapse (m_vm_lazy md4) mat' mat5 md4).
pose proof (svfi_run PcapB LAWS ly S [] W mem md (fun a => f <= a < f + AMF_BLOCK) (fun _ => False) K (spZ regs) mem4
  md4 E4 u3_s u3_e
  ms5 mat' HLO Hhi HSK HIM H63 F4 u3s_win u3e_stk E42 HF5 HS5') as F5.
pose proof F5 as (F5a & F5s & _ & F5f & F5m).
assert (R51 : getr (ms_regs ms5) 1 = getr regs 1)
  by (rewrite (g_reg W _ u3_e ms5 1 _ HS5' u3e_ra); exact (sv_atom _ 1 regs 1 (E4r 1%nat 1%bv eq_refl ltac:(lia)))).
assert (R510 : getr (ms_regs ms5) 10 = w64 (Z.of_nat (length T))).
{ rewrite (g_reg W _ u3_e ms5 10 _ HS5' u3e_r10). cbn [sv_denot].
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
split; [exact (vfi_preserved (w_H W) E4 u3_e ms5 regs HS5' u3e_kept E4r)|].
split; [exact F5s|]. split; [exact R510|].
split.
{ apply (mf_post_keep W mem4 (ms_mem ms5) f k pb T fl om wend pos len Hlpb Hfit); [|exact HFP4].
  intros x Hx. apply (aview_same (w_H W) mem4 (ms_mem ms5) x). apply HF5. rewrite unsigned_lit_small by lia.
  intros Hw. pose proof (svr_win_sound E4 _ _ u3s_win Hw) as X. rewrite E42 in X. lia. }
split; [|exact (apresent_kept64 (w_H W) mem (ms_mem ms5) (fun a Ha Hpa => F5m a Ha Hpa (fun X => X)))].
intros a Ha Hn Hs. exact (F5f a Ha Hs Hn).
Qed.

(* ---- the contract at the body 0x46a7c ---- *)
Theorem vfi_mf_ok : forall K, 0x30 + Kv <= K -> 0x30 + 2320 <= K ->
  avfprintf_mf_realizes tfibsegs PcapB link_amf rlo rhi link_vf_FF K LA_GOT_GUARD LA_GUARD LA_I_VFPRINTF.
Proof.
intros K HKK HKP ly S W regs mem md f fmt ap k fl om wend wpos wbase pos len pb ws T cval HPRE HKlo HKp G10 G11 G12
  Hblk Hpw Hk Hdyn Hpend Hlpb Hfit Hro Hgc Hgv XG1 XG2 XG3 XG4 Hgcd Hgvd Hws Hsap H47 Ad HFF HT Hfrm.
change (SRr tfibsegs W (cfg_at tfibsegs LA_I_VFPRINTF regs mem md)
  (vmf_post ly S W regs mem md K f k pb T fl om wend pos len)).
pose proof (mf_intro rlo rhi link_vf_FF K LA_GOT_GUARD LA_GUARD ly S W regs mem md f fmt k fl om wend wpos wbase pos
  len pb ws T cval ltac:(lia) HPRE HKlo HKp Hblk Hpw Hk Hdyn Hpend Hlpb Hfit Hro Hgc Hgv XG1 XG2 XG3 XG4 Hgcd Hgvd HFF
  HT) as P.
pose proof HPRE as (HAR & Hra & H16 & _ & Hhi & _ & G3 & G4).
pose proof P as (HA & _).
pose proof (stk_kHighMemBeg PcapB ly S _ (proj1 HAR)) as [K1 K2].
assert (HSVR : SVR = 64) by reflexivity.
assert (KHB : kHighMemBeg = 0x10007fff8000) by reflexivity. assert (KHE : kHighMemEnd = 2 ^ 47) by reflexivity.
assert (Hp64 : forall a, spZ regs - SVR <= a < spZ regs -> apresent (w_H W) mem a) by (intros a Ha; apply HKp; lia).
pose proof (vfi_entry_ok A_VFPI ly S W regs mem md HA Hp64 H16 ltac:(lia) ltac:(lia)) as HS0.
pose proof (sw_init PcapB ly S [] W mem md (spZ regs - K) (spZ regs) (fun _ => False) (fun _ => False) HA HKp) as F0.
exact (vfi_from K ly S W regs mem md f fmt ap k fl om wend wpos wbase pos len pb ws T cval
  (mkst regs (Z_to_bv 64 A_VFPI) mem (seg_rom tfibsegs)) md HKK HKP P Hws Hsap H47 Ad Hfrm Hra G3 G4 G10 G11 G12 HS0 F0).
Qed.

(* ---- the contract at the trampoline 0x4307c: its `j` is the first step of the same walk ---- *)
Theorem vfi_mf_ok_w : forall K, 0x30 + Kv <= K -> 0x30 + 2320 <= K ->
  avfprintf_mf_realizes tfibsegs PcapB link_amf rlo rhi link_vf_FF K LA_GOT_GUARD LA_GUARD LA_W_VFPRINTF.
Proof.
intros K HKK HKP ly S W regs mem md f fmt ap k fl om wend wpos wbase pos len pb ws T cval HPRE HKlo HKp G10 G11 G12
  Hblk Hpw Hk Hdyn Hpend Hlpb Hfit Hro Hgc Hgv XG1 XG2 XG3 XG4 Hgcd Hgvd Hws Hsap H47 Ad HFF HT Hfrm.
change (SRr tfibsegs W (cfg_at tfibsegs LA_W_VFPRINTF regs mem md)
  (vmf_post ly S W regs mem md K f k pb T fl om wend pos len)).
pose proof (mf_intro rlo rhi link_vf_FF K LA_GOT_GUARD LA_GUARD ly S W regs mem md f fmt k fl om wend wpos wbase pos
  len pb ws T cval ltac:(lia) HPRE HKlo HKp Hblk Hpw Hk Hdyn Hpend Hlpb Hfit Hro Hgc Hgv XG1 XG2 XG3 XG4 Hgcd Hgvd HFF
  HT) as P.
pose proof HPRE as (HAR & Hra & H16 & _ & Hhi & _ & G3 & G4).
pose proof P as (HA & _).
pose proof (stk_kHighMemBeg PcapB ly S _ (proj1 HAR)) as [K1 K2].
assert (HSVR : SVR = 64) by reflexivity. assert (HIE : TFIB_IMG_END < kHighMemBeg) by reflexivity.
assert (KHB : kHighMemBeg = 0x10007fff8000) by reflexivity. assert (KHE : kHighMemEnd = 2 ^ 47) by reflexivity.
assert (Hp64 : forall a, spZ regs - SVR <= a < spZ regs -> apresent (w_H W) mem a) by (intros a Ha; apply HKp; lia).
pose proof (vfi_entry_ok LA_W_VFPRINTF ly S W regs mem md HA Hp64 H16 ltac:(lia) ltac:(lia)) as HT0.
pose proof (sw_init PcapB ly S [] W mem md (spZ regs - K) (spZ regs) (fun _ => False) (fun _ => False) HA HKp) as F0.
assert (EE2 : bv_unsigned (ew (Ereg regs []) 2) = spZ regs) by (rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl); reflexivity).
unfold cfg_at, w64.
eapply SRr_bind; [exact (g_phase_to W (Ereg regs []) A_VFPI vfw_t0 u0 RS_running _ md HT0 r_vfw)|].
intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1).
assert (HS1' : st_ok tfibsegs (Ereg regs []) u0 (restrict (w_H W) ms1)) by exact HS1. clear HS1.
pose proof (svfi_run PcapB LAWS ly S [] W mem md (fun _ => False) (fun _ => False) K (spZ regs) mem md (Ereg regs [])
  vfw_t0 u0 ms1 mat1
  ltac:(lia) Hhi ltac:(lia) ltac:(lia) ltac:(lia) F0 vfw_win u0_stk EE2 HF1 HS1') as F1.
exact (vfi_from K ly S W regs mem md f fmt ap k fl om wend wpos wbase pos len pb ws T cval
  ms1 _ HKK HKP P Hws Hsap H47 Ad Hfrm Hra G3 G4 G10 G11 G12 HS1' F1).
Qed.

(* at the window 0x30 + Kv *)
Corollary vfi_mf_ok_win : 2320 <= Kv ->
  avfprintf_mf_realizes tfibsegs PcapB link_amf rlo rhi link_vf_FF (0x30 + Kv) LA_GOT_GUARD LA_GUARD LA_I_VFPRINTF /\
  avfprintf_mf_realizes tfibsegs PcapB link_amf rlo rhi link_vf_FF (0x30 + Kv) LA_GOT_GUARD LA_GUARD LA_W_VFPRINTF.
Proof. intros H. split; [apply vfi_mf_ok | apply vfi_mf_ok_w]; lia. Qed.
End v.

(* ---- at musl vfprintf's GXA window LVF_MUSL_STK = 5552: the body's window LVF_STK = 0x30 + 5552 ---- *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Corollary vfi_mf_ok_stk : AR_laws tfibsegs PcapB -> PcapSyms PcapB -> forall rlo rhi,
  avfprintf_mf_realizes tfibsegs PcapB link_amf rlo rhi link_vf_FF LVF_MUSL_STK LA_GOT_GUARD LA_GUARD LA_VFPRINTF ->
  avfprintf_mf_realizes tfibsegs PcapB link_amf rlo rhi link_vf_FF LVF_STK LA_GOT_GUARD LA_GUARD LA_I_VFPRINTF /\
  avfprintf_mf_realizes tfibsegs PcapB link_amf rlo rhi link_vf_FF LVF_STK LA_GOT_GUARD LA_GUARD LA_W_VFPRINTF.
Proof.
intros LAWS TB rlo rhi AVF.
exact (vfi_mf_ok_win rlo rhi LVF_MUSL_STK LAWS TB ltac:(unfold ESTACK, LVF_MUSL_STK; lia) AVF
  ltac:(unfold LVF_MUSL_STK; lia)).
Qed.

(* ---- at link's instance: PcapB's laws (YG0q.AR_laws_ok) and symbols (AD2l.PcapB_syms) ---- *)
Corollary vfi_mf_ok_PcapB : forall rlo rhi Kv, ESTACK <= Kv ->
  avfprintf_mf_realizes tfibsegs PcapB link_amf rlo rhi link_vf_FF Kv LA_GOT_GUARD LA_GUARD LA_VFPRINTF ->
  forall K, 0x30 + Kv <= K -> 0x30 + 2320 <= K ->
  avfprintf_mf_realizes tfibsegs PcapB link_amf rlo rhi link_vf_FF K LA_GOT_GUARD LA_GUARD LA_I_VFPRINTF.
Proof.
intros rlo rhi Kv HKv AVF.
exact (vfi_mf_ok rlo rhi Kv (YG0q.AR_laws_ok tfibsegs PcapB) PcapB_syms HKv AVF).
Qed.
Corollary vfi_mf_ok_w_PcapB : forall rlo rhi Kv, ESTACK <= Kv ->
  avfprintf_mf_realizes tfibsegs PcapB link_amf rlo rhi link_vf_FF Kv LA_GOT_GUARD LA_GUARD LA_VFPRINTF ->
  forall K, 0x30 + Kv <= K -> 0x30 + 2320 <= K ->
  avfprintf_mf_realizes tfibsegs PcapB link_amf rlo rhi link_vf_FF K LA_GOT_GUARD LA_GUARD LA_W_VFPRINTF.
Proof.
intros rlo rhi Kv HKv AVF.
exact (vfi_mf_ok_w rlo rhi Kv (YG0q.AR_laws_ok tfibsegs PcapB) PcapB_syms HKv AVF).
Qed.
Corollary vfi_mf_ok_stk_PcapB : forall rlo rhi,
  avfprintf_mf_realizes tfibsegs PcapB link_amf rlo rhi link_vf_FF LVF_MUSL_STK LA_GOT_GUARD LA_GUARD LA_VFPRINTF ->
  avfprintf_mf_realizes tfibsegs PcapB link_amf rlo rhi link_vf_FF LVF_STK LA_GOT_GUARD LA_GUARD LA_I_VFPRINTF /\
  avfprintf_mf_realizes tfibsegs PcapB link_amf rlo rhi link_vf_FF LVF_STK LA_GOT_GUARD LA_GUARD LA_W_VFPRINTF.
Proof. exact (vfi_mf_ok_stk (YG0q.AR_laws_ok tfibsegs PcapB) PcapB_syms). Qed.
End s.
