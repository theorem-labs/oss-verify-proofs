(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMW_rd_pre_c4.v (a working branch e2e59892bef),
   re-walked on B: 0x81f2c .. 0x81f34 = A's same stretch + 0x290, uri_len in s1 (A s6); fuzz_free is called with
   s0 = rp = the entry sp, so its frame chain is one record (rdp_chain_rp), trace [0x81f38; 0x81e88] = B's CTX_fuzz_free. *)
(* lv2_locate_manifest_readings, PRE piece c4 (FMW_rd_pre_cuts.v rdp_seg_C4). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YCbm.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YC20 YI00 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_g3kit FMW_rd_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YCej.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_rd_cuts FMW_rd_ret.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_rd_pre_k FMW_rd_pre_cuts.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable CTX : list (list Z).
Hypothesis IMG : fm_img_facts tfibsegs B.
Hypothesis FREE : fuzz_free_spec tfibsegs B CTX_fuzz_free.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Abbreviation rdJ cx := (ajournal tfibsegs B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx)
  (cx_W cx) (cx_mem cx) (cx_md cx) []).

(* RD_C4 = 0x81f2c (after strstr) .. fuzz_free .. RD_C5 *)
Theorem rdp_C4_holds : rdp_seg_C5 B CTX -> rdp_seg_C4 B CTX.
Proof.
intros HC5 cx m1 lyM SM WM regs4 mem4 md4 res v HB HJ4 HR4 R4_9 R4_20 H10v Hv64 HPRO KE4 Hok HPo4 Hres Eab Hrb4 HG4 Hcf
  Hub HRv.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof g3_wx as Hwx. pose proof g3_segs_low as Hsegs.
pose proof HB as (HAN & HCX & HRO & H10 & H11 & H12 & Hpr16 & Htop16 & Hv & Hv63 & Ct & Cu & Kt & Ku & Hub255 & Htb & HG0 &
  Hlv & Hcnt & Hev & Hlb & HraN & HchN).
pose proof HAN as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof HG0 as (_ & _ & _ & _ & Hlive0 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFR : STK_readings = 16624) by reflexivity.
assert (FFF : STK_fuzz_free = 16416) by reflexivity.
assert (Esp : cx_sp cx = spZ (cx_regs cx)) by reflexivity.
assert (Hulen : cx_ulen cx = Z.of_nat (length (cx_ub cx))) by reflexivity.
pose proof HJ4 as (HARM & _).
set (h := res - 16) in *. set (n := cx_ulen cx + 3) in *.
assert (Eh : h = res - 16) by reflexivity. assert (En : n = cx_ulen cx + 3) by reflexivity.
assert (Hblk : In (h, n + 16) (ablocks B lyM SM)) by (rewrite Eab; apply in_or_app; right; left; reflexivity).
assert (Hnb : ~ In (h, n + 16) (ablocks B (cx_ly cx) (cx_S cx))) by exact (rdp_new_notin B _ _ _ _ _ _ _ h (n + 16) HARM Eab).
pose proof (rdp_blk_slack B _ _ _ _ _ h (n + 16) HARM Hblk ltac:(lia)) as [Hhi Hslack].
assert (H0h : 0 <= h) by lia. assert (H1h : h + 16 <= kHighMemEnd) by lia.
assert (U1 : rdp_U1 [(h, 16)]) by (right; exists h; split; [reflexivity | lia]).
(* ---- 0x81f2c: s5 = strstr's answer; a0 = whole; jal fuzz_free (s0 = rp = the entry sp: one frame record) ---- *)
pose proof (rdp_ssn_ok WM regs4 [] mem4 RD_C4) as HS.
srr_run_with rd_tbl_ok HS.
rdp_name HS msF.
assert (HmF : ms_mem msF = mem4) by (eapply frame_of_read_only; [|exact HF]; reflexivity).
clear HF HFr.
pose proof (rdp_regs_run cx _ regs4 _ msF HS ltac:(vm_compute; reflexivity) HR4) as HRF.
pose proof HRF as (F2 & F3 & F4 & F27 & F8 & _).
rreg HS (1%bv : bv 5) G1. rreg HS (10%bv : bv 5) G10. rreg HS (21%bv : bv 5) G21. rdp_keep HS regs4 (9%bv : bv 5) G9.
rewrite (ew_Ereg_nat regs4 [] 20 20%bv eq_refl), R4_20 in G10.
rewrite (ew_Ereg_nat regs4 [] 10 10%bv eq_refl), H10v in G21.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc]. rewrite HmF. rdp_cfg A_fuzz_free.
assert (HJ4s := ajournal_materialize tfibsegs B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat HJ4).
assert (Hsp3 : spZ (ms_regs msF) = cx_sp cx + 16 + -224)
  by (unfold spZ; rewrite F2; unfold w64, cx_F; rewrite unsigned_lit_small by lia; lia).
assert (HROM : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H WM) mem4)).
{ apply (rdp_arodata_unp B WM h mem4 H0h H1h). eapply rdp_arodata_kept; [exact HJ4 | exact HRO]. }
assert (KEU : forall a, cx_sp cx - 104 <= a < cx_sp cx + 16 ->
  aview tfibsegs (w_H WM) (unpoison [(res - HEAD, HEAD)] mem4) a = aview tfibsegs (w_H (cx_W cx)) m1 a).
{ intros a Ha. rewrite (rdp_aview_unp_hi (w_H WM) [(res - HEAD, HEAD)] mem4 a
    ltac:(right; exists h; unfold HEAD; split; [rewrite Eh; reflexivity | lia]) ltac:(lia)).
  exact (KE4 a Ha). }
eapply SRr_bind.
{ apply (FREE lyM SM WM (ms_regs msF) mem4 _ [(cx_sp cx, RD_NAMES_RA, bv_unsigned (getr (cx_regs cx) 8))] res n
    (cx_live cx + n) (Z.max (cx_peak cx) (cx_live cx + n)) (cx_cnt cx + 1) (cx_fail cx)).
  - unfold raZ. rewrite G1, unsigned_lit_small by lia. cbn [spine map fst snd]. left. reflexivity.
  - exact G10.
  - exact HG4.
  - right. split; [lia|]. split.
    { unfold afn_preU. split; [|split; [exact Hok | exact HPo4]].
      apply (afn_pre_at tfibsegs B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx)
        (cx_mem cx) (cx_md cx) [] lyM SM WM (unpoison [(res - HEAD, HEAD)] mem4) _ 1 (ms_regs msF) STK_fuzz_free (-224)
        [(cx_sp cx, RD_NAMES_RA, bv_unsigned (getr (cx_regs cx) 8))]
        HJ4s).
      - exact Hsp3.
      - reflexivity.
      - lia.
      - lia.
      - lia.
      - rewrite G1. vm_compute. reflexivity.
      - unfold raZ. rewrite G1, unsigned_lit_small by lia. lia.
      - rewrite F3. exact Hgp.
      - rewrite F4. exact Htp.
      - apply (rdp_chain_rp B CTX cx m1 lyM SM WM (unpoison [(res - HEAD, HEAD)] mem4) _ 1 (ms_regs msF) HB HJ4s HPRO KEU).
        + rewrite Hsp3. unfold cx_F. lia.
        + unfold s0Z. rewrite F8. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
    split; [exact HROM|]. split; [exact Hrb4 | lia].
  - pose proof HJ4 as (_ & _ & _ & _ & _ & _ & Hnev & _). unfold EV_names in Hev. lia. }
intros W5 c5 _ [(Hp0 & _) | (_ & (ly5 & S5 & regs5 & mem5 & md5 & -> & HJf & Hok5 & Hpo5 & HP5 & ((l1 & l2 & El1 & El2) & HG5)))];
  [lia|].
(* ---- the journal from readings' entry, the window closed ---- *)
assert (HJ5 : rdJ cx ly5 S5 W5 mem5 md5 EV_names).
{ refine (g3_ajsub_img_ok B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx)
    (cx_md cx) [] lyM SM WM (unpoison [(res - HEAD, HEAD)] mem4) _ 1 STK_fuzz_free (spZ (ms_regs msF))
    (ablocks_fp [(res - HEAD, n + HEAD)] ++ FM_PSTAT_FP) [] ly5 S5 W5 (unpoison [] mem5) md5 1 HJ4s HJf _ _ _).
  - rewrite Hsp3. lia.
  - lia.
  - intros a Ha. apply inFP_app in Ha as [Ha|Ha].
    + right; left. apply inFP_ablocks_fp_inv in Ha as (p & q & Hpq & Hra').
      destruct Hpq as [Hpq|[]]. injection Hpq as <- <-. unfold HEAD in Hra'.
      exists h, (n + 16). split; [exact Hblk|]. split; [exact Hnb | lia].
    + right; right. split; [exact Ha | exact (g3_pstat_img a Ha)]. }
rewrite G1. change (Z_to_bv 64 532280) with (Z_to_bv 64 RD_C5).
pose proof HJf as (_ & _ & _ & _ & _ & _ & _ & _ & Ff1 & _).
apply (HC5 cx m1 ly5 S5 W5 regs5 mem5 md5 v HB HJ5).
- exact (rdp_regs_pres cx _ _ HP5 HRF).
- rewrite (rdp_pres _ _ 9%bv HP5 ltac:(rdp_cs)), G9. exact R4_9.
- rewrite (rdp_pres _ _ 21%bv HP5 ltac:(rdp_cs)). exact G21.
- exact Hv64.
- exact HPRO.
- intros a Ha. rewrite <- (KE4 a Ha).
  change (aview tfibsegs (w_H W5) mem5 a) with (aview tfibsegs (w_H W5) (unpoison [] mem5) a).
  rewrite (Ff1 a ltac:(lia) ltac:(rewrite Hsp3; lia)).
  apply rdp_aview_unp_hi; [exact U1 | lia].
- rewrite El2.
  assert (P : Permutation (l1 ++ (res - HEAD, n + HEAD) :: l2)
    (ablocks B (cx_ly cx) (cx_S cx) ++ [(res - HEAD, n + HEAD)])).
  { rewrite <- El1, Eab. apply Permutation_refl. }
  pose proof (Permutation_app_inv _ _ _ _ _ P) as P2. rewrite app_nil_r in P2. exact P2.
- rewrite Z.add_simpl_r in HG5.
  replace (cx_live cx + cx_ulen cx + 3) with (cx_live cx + n) by lia. exact HG5.
- exact Hcf.
- exact Hub.
- exact HRv.
Qed.
End c.
