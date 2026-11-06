(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMW_rd_pre_c2.v (a working branch e2e59892bef),
   re-walked on B: 0x81f00 .. 0x81f1c = A's same stretch + 0x290, uri_len in s1 (A s6). *)
(* lv2_locate_manifest_readings, PRE piece c2 (FMW_rd_pre_cuts.v rdp_seg_C2). *)
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
Hypothesis SNPRINTF : asnprintf_realizes tfibsegs B PC_snprintf.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Abbreviation rdJ cx := (ajournal tfibsegs B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx)
  (cx_W cx) (cx_mem cx) (cx_md cx) []).

(* RD_C2 = 0x81f00 (fuzz_malloc returned whole) .. snprintf .. RD_C3 *)
Theorem rdp_C2_holds : rdp_seg_C3 B CTX -> rdp_seg_C2 B CTX.
Proof.
intros HC3 cx m1 lyM SM WM regsM memM mdM res HB HJ HR R9 R21 R10 HPRO KE Hok Hpo Hres Eab Hrb HRA Hhv HG Hcf Hub.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof g3_wx as Hwx. pose proof g3_segs_low as Hsegs.
pose proof HB as (HAN & HCX & HRO & H10 & H11 & H12 & Hpr16 & Htop16 & Hv & Hv63 & Ct & Cu & Kt & Ku & Hub255 & Htb & HG0 &
  Hlv & Hcnt & Hev & Hlb & HraN & HchN).
pose proof HAN as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Cu as ((_ & Hnzu) & Hu4 & Hucl & _). pose proof Ct as (_ & Ht4 & Htcl & _).
assert (FFR : STK_readings = 16624) by reflexivity. assert (FPR : STK_RT_PRINTF = 12288) by reflexivity.
assert (HSO : SHADOW_OFF = 0x7fff8000) by reflexivity.
assert (Esp : cx_sp cx = spZ (cx_regs cx)) by reflexivity.
assert (Hulen : cx_ulen cx = Z.of_nat (length (cx_ub cx))) by reflexivity.
assert (Hub1 : (1 <= length (cx_ub cx))%nat) by (destruct (cx_ub cx); [contradiction | cbn; lia]).
pose proof HJ as (HARM & _).
set (h := res - 16) in *. set (n := cx_ulen cx + 3) in *.
assert (Ehr : res = h + 16) by (unfold h; lia).
assert (En : n = Z.of_nat (length (cx_ub cx)) + 3) by reflexivity.
assert (Hblk : In (h, n + 16) (ablocks B lyM SM)) by (rewrite Eab; apply in_or_app; right; left; reflexivity).
assert (Hnb : ~ In (h, n + 16) (ablocks B (cx_ly cx) (cx_S cx))) by exact (rdp_new_notin B _ _ _ _ _ _ _ h (n + 16) HARM Eab).
pose proof (rdp_blk_slack B _ _ _ _ _ h (n + 16) HARM Hblk ltac:(lia)) as [Hhi Hslack].
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARM Hblk) as (Hh16 & Hh4 & Hhc & Happ & Hbp & _).
assert (Hrq : req_size (n + 16) = n + 16)
  by (unfold req_size; destruct (Z.eqb_spec (n + 16) 0); [exfalso; lia | reflexivity]).
rewrite Hrq in Hhc, Hbp.
assert (H0h : 0 <= h) by lia. assert (H1h : h + 16 <= kHighMemEnd) by lia.
assert (H8h : h mod 8 = 0).
{ assert (D : h = 8 * (2 * (h / 16))) by (pose proof (Z.div_mod h 16 ltac:(lia)); lia).
  rewrite D, Z.mul_comm. apply Z.mod_mul. lia. }
assert (U1 : rdp_U1 [(h, 16)]) by (right; exists h; split; [reflexivity | lia]).
assert (DIS_u : forall x, cx_u cx <= x <= cx_u cx + Z.of_nat (length (cx_ub cx)) -> ~ (h <= x < h + (n + 16)))
  by exact (rdp_kept_disj B _ _ _ _ _ _ _ _ _ h (n + 16) HARM Eab ltac:(lia) Ku).
(* ---- 0x81f00: beqz a0 (whole <> NULL) ---- *)
pose proof (rdp_ssn_ok WM regsM [] memM RD_C2) as HS.
assert (E10 : ew (Ereg regsM []) 10 = Z_to_bv 64 res) by (rewrite (ew_Ereg_nat regsM [] 10 10%bv eq_refl); exact R10).
srr_branch_with rd_tbl_ok HS.
{ rewrite branch_eq_U, (U_atom _ 10 res E10 ltac:(lia)), U_SLit in Hc. change (zcanon 0) with 0 in Hc.
  apply Z.eqb_eq in Hc. exfalso; lia. }
clear Hc.
(* ---- s4 = whole; snprintf (whole, uri_len + 3, "<%s>", uri) ---- *)
srr_run_with rd_tbl_ok HS.
rdp_name HS msS.
assert (HmS : ms_mem msS = memM) by (eapply frame_of_read_only; [|exact HF]; vm_compute; reflexivity).
clear HF HFr.
pose proof (rdp_regs_run cx _ regsM _ msS HS ltac:(vm_compute; reflexivity) HR) as HRS.
pose proof HRS as (S2 & S3 & S4 & S8 & _).
rreg HS (1%bv : bv 5) Q1. rreg HS (10%bv : bv 5) Q10. rreg HS (11%bv : bv 5) Q11. rreg HS (12%bv : bv 5) Q12.
rreg HS (Z_to_bv 5 13) Q13. rreg HS (20%bv : bv 5) Q20. rdp_keep HS regsM (9%bv : bv 5) Q9.
rewrite (ew_Ereg_nat regsM [] 10 10%bv eq_refl), R10 in Q10. rewrite (ew_Ereg_nat regsM [] 21 21%bv eq_refl), R21 in Q11.
rewrite (ew_Ereg_nat regsM [] 18 18%bv eq_refl) in Q13. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HR)))))) in Q13.
rewrite (ew_Ereg_nat regsM [] 10 10%bv eq_refl), R10 in Q20.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc]. rewrite HmS.
assert (HJs := ajournal_materialize tfibsegs B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat HJ).
destruct (rdp_img_win B IMG cx lyM SM WM memM _ 1 h HJ H0h H1h HRO) as (HrvM & HcanM & HROM & HfmM).
assert (HuM : cstr_ok tfibsegs WM memM (cx_u cx) (cx_ub cx)).
{ apply (rdp_kept_win B IMG cx lyM SM WM memM _ 1 h (n + 16) (cx_u cx) (cx_ub cx) HJ Eab ltac:(lia) H0h H8h H1h Hpo HRO Ku Cu). }
assert (Hsp1 : spZ (ms_regs msS) = cx_sp cx + 16 + -224) by (unfold spZ; rewrite S2; unfold w64, cx_F; rewrite unsigned_lit_small by lia; lia).
eapply SRr_bind.
{ apply (rdp_aj_snU B PC_snprintf h res (rdp_out (cx_ub cx)) h (n + 16) WM (ms_regs msS) memM (STK_readings + 16)
    (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx) [] lyM SM _ 1 (-224)
    (Z_to_bv 64 532256) HJs H0h H1h Hok Hpo Hsp1 eq_refl ltac:(lia) ltac:(lia)
    ltac:(rewrite S3; exact Hgp) ltac:(rewrite S4; exact Htp) Q1 ltac:(vm_compute; reflexivity) Hblk Hnb ltac:(lia)
    ltac:(rewrite rdp_out_len; lia)).
  intros HPK.
  apply (SNPRINTF lyM SM [(h, 16)] WM (ms_regs msS) memM _ res n FMT_whole [FLit [60]; FStr; FLit [62]]
    (rdp_out (cx_ub cx)) HPK HrvM HcanM Q10).
  - exact Q11.
  - rewrite Q12. reflexivity.
  - left. reflexivity.
  - apply (rdp_cstr_unp WM memM h FMT_whole _ H0h H8h H1h); [| exact Hpo | exact (HfmM FMT_whole _ ltac:(left; reflexivity))].
    intros x Hx Hx2. cbn [fmt_bytes app length] in Hx. unfold FMT_whole in Hx.
    apply (blk_img tfibsegs B LAWS _ _ _ _ _ h (n + 16) x HARM Hblk); [rewrite Hrq; lia | apply rdp_img_ro; lia].
  - cbn [map frender]. rewrite Q13. unfold w64. rewrite unsigned_lit_small by lia.
    exists (cx_ub cx ++ [62]). split; [reflexivity|]. exists (cx_ub cx), [62].
    split; [exact HuM|]. split.
    { apply (rdp_rng_split (cx_u cx) (Z.of_nat (length (cx_ub cx))) h (n + 16) res n DIS_u); lia. }
    split; [reflexivity|]. exists []. split; reflexivity.
  - rewrite rdp_out_len. lia.
  - replace (Z.of_nat (length (rdp_out (cx_ub cx))) + 1) with n by (rewrite rdp_out_len; lia).
    unfold wdest_ok. split; [lia|]. split; [lia|].
    split; [apply (amem_range_of_block tfibsegs B LAWS _ _ _ _ _ h (n + 16) res n HARM Hblk); rewrite ?Hrq; lia|].
    split.
    { intros a Ha. destruct (Hbp a ltac:(lia)) as [Hpa Hown]. split; [|split; [exact Hown|]].
      - apply (apresent_writable tfibsegs). apply (proj1 (rdp_apresent_unp_hi _ _ memM a U1 ltac:(lia))). exact Hpa.
      - rewrite Hsp1. lia. }
    split; [exact HRA | intros _; exact Hhv].
  - replace (res + Z.of_nat (length (rdp_out (cx_ub cx))) + 1) with (res + n) by (rewrite rdp_out_len; lia).
    apply (rdp_blk_img_rng B _ _ _ _ _ h (n + 16) FM_canary 8 HARM Hblk rdp_img_canary ltac:(lia) res n); rewrite ?Hrq; lia.
  - lia.
  - intros a Ha. rewrite rdp_out_len in Ha.
    apply (rdp_blk_not_rom B _ _ _ _ _ h (n + 16) a HARM Hblk). rewrite Hrq. lia. }
intros W' c' _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HPo3 & HP3 & H10s & Hby & Hfr3 & Hpres3).
assert (Lout : Z.of_nat (length (rdp_out (cx_ub cx))) = n - 1) by (rewrite rdp_out_len; lia).
rewrite Lout in Hfr3.
assert (KE3 : rdp_ke cx m1 WM mem3) by (intros a Ha; rewrite Hfr3 by lia; exact (KE a Ha)).
pose proof (rdp_regs_pres cx _ _ HP3 HRS) as HR3.
assert (R3_20 : getr regs3 20 = w64 res) by (rewrite (rdp_pres _ _ 20%bv HP3 ltac:(rdp_cs)); exact Q20).
assert (R3_9 : getr regs3 9 = w64 (cx_ulen cx)) by (rewrite (rdp_pres _ _ 9%bv HP3 ltac:(rdp_cs)), Q9; exact R9).
(* ---- RD_C3 ---- *)
change (Z_to_bv 64 532256) with (Z_to_bv 64 RD_C3).
apply (HC3 cx m1 lyM SM WM regs3 mem3 md3 res HB HJ3 HR3 R3_9 R3_20 HPRO KE3 Hok HPo3 Hres Eab).
all: try change (cx_ulen cx + 3) with n.
- destruct Hrb as (Hin & Hm16 & Hn0 & Hvh). split; [exact Hin|]. split; [exact Hm16|]. split; [exact Hn0|].
  apply (g3_val_mem_kept WM WM memM mem3); [exact Hvh|]. intros i Hi. cbn in Hi. unfold HEAD in *. apply Hfr3; lia.
- exact Hby.
- eapply range_addressable_agree; [|exact HRA]. intros x Hx. change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x).
  pose proof (rdp_band x ltac:(lia)) as [B1 B2]. apply Hfr3; lia.
- intros s Hs. pose proof (rdp_band res ltac:(lia)) as [B1 B2]. pose proof (rdp_band (res + n - 1) ltac:(lia)) as [B3 B4].
  pose proof (Z.mul_div_le (shadow_addr (res + n - 1)) 8 ltac:(lia)).
  pose proof (Z.div_pos (shadow_addr res) 8 ltac:(lia) ltac:(lia)).
  rewrite Hfr3 by lia. exact (Hhv s Hs).
- apply (rdp_glob_low WM WM memM mem3 _ _ _ _ HG). intros a Ha. apply Hfr3; lia.
- exact Hcf.
- exact Hub.
Qed.
End c.
