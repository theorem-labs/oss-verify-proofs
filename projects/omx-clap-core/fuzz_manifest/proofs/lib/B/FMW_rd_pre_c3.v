(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMW_rd_pre_c3.v (a working branch e2e59892bef),
   re-walked on B: 0x81f20 .. 0x81f28 = A's same stretch + 0x290, text in s6 (A s8), uri_len in s1 (A s6). *)
(* lv2_locate_manifest_readings, PRE piece c3 (FMW_rd_pre_cuts.v rdp_seg_C3). *)
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
Hypothesis STRSTR : astrstr_realizes tfibsegs B PC_strstr.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Abbreviation rdJ cx := (ajournal tfibsegs B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx)
  (cx_W cx) (cx_mem cx) (cx_md cx) []).

(* RD_C3 = 0x81f20 (after snprintf) .. strstr .. RD_C4 *)
Theorem rdp_C3_holds : rdp_seg_C4 B CTX -> rdp_seg_C3 B CTX.
Proof.
intros HC4 cx m1 lyM SM WM regs3 mem3 md3 res HB HJ3 HR3 R3_9 R3_20 HPRO KE3 Hok HPo3 Hres Eab Hrb Hby HRA Hhv HG Hcf Hub.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof g3_wx as Hwx. pose proof g3_segs_low as Hsegs.
pose proof HB as (HAN & HCX & HRO & H10 & H11 & H12 & Hpr16 & Htop16 & Hv & Hv63 & Ct & Cu & Kt & Ku & Hub255 & Htb & HG0 &
  Hlv & Hcnt & Hev & Hlb & HraN & HchN).
pose proof HAN as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Cu as ((_ & Hnzu) & _).
assert (FFR : STK_readings = 16624) by reflexivity.
assert (HSTKr : STK_RT_STRSTR = 8192) by reflexivity.
assert (Esp : cx_sp cx = spZ (cx_regs cx)) by reflexivity.
assert (Hulen : cx_ulen cx = Z.of_nat (length (cx_ub cx))) by reflexivity.
pose proof HJ3 as (HARM & _).
set (h := res - 16) in *. set (n := cx_ulen cx + 3) in *.
assert (Ehr : res = h + 16) by (unfold h; lia).
assert (En : n = cx_ulen cx + 3) by reflexivity.
assert (Hblk : In (h, n + 16) (ablocks B lyM SM)) by (rewrite Eab; apply in_or_app; right; left; reflexivity).
pose proof (rdp_blk_slack B _ _ _ _ _ h (n + 16) HARM Hblk ltac:(lia)) as [Hhi Hslack].
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARM Hblk) as (Hh16 & _).
assert (H0h : 0 <= h) by lia. assert (H1h : h + 16 <= kHighMemEnd) by lia.
assert (H8h : h mod 8 = 0).
{ pose proof (Z.div_mod h 16 ltac:(lia)) as D. rewrite Hh16, Z.add_0_r in D. rewrite D.
  replace (16 * (h / 16)) with ((2 * (h / 16)) * 8) by lia. apply Z.mod_mul. lia. }
(* ---- 0x81f20: strstr (text, whole) ---- *)
pose proof (rdp_ssn_ok WM regs3 [] mem3 RD_C3) as HS.
srr_run_with rd_tbl_ok HS.
rdp_name HS msT.
assert (HmT : ms_mem msT = mem3) by exact (frame_of_read_only _ (ss_mem (rdp_ssn RD_C3)) _ _ eq_refl HF).
clear HF HFr.
pose proof (rdp_regs_run cx _ regs3 _ msT HS ltac:(vm_compute; reflexivity) HR3) as HRT.
pose proof HRT as (T2 & T3 & T4 & T8 & _).
rreg HS (1%bv : bv 5) P1. rreg HS (10%bv : bv 5) P10. rreg HS (11%bv : bv 5) P11.
rdp_keep HS regs3 (20%bv : bv 5) P20. rdp_keep HS regs3 (21%bv : bv 5) P21. rdp_keep HS regs3 (9%bv : bv 5) P9.
rewrite (ew_Ereg_nat regs3 [] 22 22%bv eq_refl) in P10. rewrite (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HR3)))))) in P10.
rewrite (ew_Ereg_nat regs3 [] 20 20%bv eq_refl), R3_20 in P11.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc]. rewrite HmT.
assert (HJ3s := ajournal_materialize tfibsegs B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat HJ3).
destruct (rdp_img_win B IMG cx lyM SM WM mem3 _ 1 h HJ3 H0h H1h HRO) as (Hrv3 & _ & _ & _).
assert (Hsp2 : spZ (ms_regs msT) = cx_sp cx + 16 + -224) by (unfold spZ; rewrite T2; unfold w64, cx_F; rewrite unsigned_lit_small by lia; lia).
assert (HAR3 : AR tfibsegs B lyM SM WM (unpoison [(h, 16)] mem3) md3) by exact (proj1 HJ3).
assert (Hwh3 : cstr_ok tfibsegs WM mem3 res (rdp_out (cx_ub cx))).
{ rewrite Ehr. apply (rdp_whole_cstr B lyM SM WM mem3 md3 h (n + 16) (cx_ub cx) HAR3 Hblk ltac:(lia) Hub255 Hnzu).
  - rewrite <- Ehr. exact Hby.
  - rewrite <- Ehr. replace (n + 16 - 16) with n by lia. exact HRA.
  - rewrite <- Ehr. replace (n + 16 - 16) with n by lia. exact Hhv. }
eapply SRr_bind.
{ apply (rdp_aj_roU B PC_strstr STK_RT_STRSTR
    (fun v => (v = 0 /\ no_occ (cx_tb cx) (rdp_out (cx_ub cx))) \/
              (exists j, first_occ (cx_tb cx) (rdp_out (cx_ub cx)) j /\ v = cx_t cx + Z.of_nat j)) h
    WM (ms_regs msT) mem3 (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx)
    (cx_md cx) [] lyM SM _ 1 (-224) (Z_to_bv 64 532268) HJ3s H0h H1h Hok HPo3 Hsp2 eq_refl ltac:(lia)
    ltac:(unfold STK_RT_STRSTR, ESTACK; lia) ltac:(unfold STK_RT_STRSTR, ESTACK; lia)
    ltac:(rewrite T3; exact Hgp) ltac:(rewrite T4; exact Htp) P1 ltac:(vm_compute; reflexivity)).
  intros HPK.
  apply (STRSTR lyM SM [(h, 16)] WM (ms_regs msT) mem3 _ (cx_t cx) res (cx_tb cx) (rdp_out (cx_ub cx)) HPK Hrv3
    (rdp_img_winO B IMG cx lyM SM WM mem3 _ 1 h HJ3 H0h H1h HRO) P10 P11); [|exact Hwh3].
  apply (rdp_kept_win B IMG cx lyM SM WM mem3 _ 1 h (n + 16) (cx_t cx) (cx_tb cx) HJ3 Eab ltac:(lia) H0h H8h H1h HPo3 HRO Kt Ct). }
intros W'' c'' _ (-> & regs4 & mem4 & md4 & v & -> & HJ4 & HPo4 & HP4 & H10v & Hv64 & HRv & Hfr4 & Hpres4).
assert (KE4 : rdp_ke cx m1 WM mem4) by (intros a Ha; rewrite Hfr4 by lia; exact (KE3 a Ha)).
pose proof (rdp_regs_pres cx _ _ HP4 HRT) as HR4.
assert (R4_20 : getr regs4 20 = w64 res) by (rewrite (rdp_pres _ _ 20%bv HP4 ltac:(rdp_cs)), P20; exact R3_20).
assert (R4_9 : getr regs4 9 = w64 (cx_ulen cx)) by (rewrite (rdp_pres _ _ 9%bv HP4 ltac:(rdp_cs)), P9; exact R3_9).
(* ---- RD_C4 ---- *)
change (Z_to_bv 64 532268) with (Z_to_bv 64 RD_C4).
apply (HC4 cx m1 lyM SM WM regs4 mem4 md4 res v HB HJ4 HR4 R4_9 R4_20 H10v Hv64 HPRO KE4 Hok HPo4 Hres Eab).
- unfold fm_rblock in Hrb |- *. destruct Hrb as (Hin & Hm16 & Hn0 & Hvh).
  split; [exact Hin|]. split; [exact Hm16|]. split; [exact Hn0|].
  apply (g3_val_mem_kept WM WM mem3 mem4); [exact Hvh|]. intros i Hi. cbn in Hi. unfold HEAD in *. apply Hfr4; lia.
- apply (rdp_glob_low WM WM mem3 mem4 _ _ _ _ HG). intros a Ha. apply Hfr4; lia.
- exact Hcf.
- exact Hub.
- exact HRv.
Qed.
End c.
