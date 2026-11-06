(* has_prefixed (G2) loop segment tail, 0x82240..0x82254: at = strstr (at + 1, location) (0x82248); a hit goes back to
   the loop head 0x821b0, NULL returns 0 through 0x82254 `j 0x82280`. Kit lib/A/FMW_hp_kit.v. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI04 YN3v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YA0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC20 YI16 YI00 YM05 YG0q YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v ACeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_g2rt FMW_name_char FMW_hp_kit FMW_hp_model.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel has_prefixed_model.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Hypothesis TL : TfibLib B.
Hypothesis IMGF : fm_img_facts tfibsegs B.
Hypothesis ASTRSTR : astrstr_realizes tfibsegs B PC_strstr.

Lemma hp_seg_tail : seg_tail_ok B.
Proof.
unfold seg_tail_ok. intros cx a KZ KL lyc Sc W regs m mdc Hst _.
pose proof g2_segs_low as Hsegs. pose proof g2_wx as Hwx.
pose proof (hp_sp B cx a lyc Sc W regs m mdc Hst) as (Hsp1 & Hsp2 & Hspc).
pose proof Hst as (HE & HJ & Hab & Q3 & Q4 & Hsp & HF & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q23 & Q24 & Q26 & Q27 & Hmt & Hgl).
pose proof HE as (Hra & G3 & G4 & _ & _ & Hkt & Hkl & Hlb & Hq & Hplen & Hqp & Htmax & HRO).
pose proof (hp_cstr B IMGF cx a lyc Sc W regs m mdc Hst) as (Ht & Hl).
pose proof Ht as (_ & Ht4096 & Htcl & _).
pose proof (has_prefixed_model.mt_len _ _ _ Hmt) as Hlen.
assert (Hlb1 : (1 <= length (cx_lb cx))%nat) by (destruct (cx_lb cx); [contradiction | cbn; lia]).
ceil2.
assert (FFS : STK_has_prefixed = 8304) by reflexivity.
pose proof (hp_seat B cx a lyc Sc W regs m mdc HP_TAIL Hst) as HS.
assert (HAE : env_agree 32 (Ereg regs []) (Ereg regs [])) by apply env_agree_refl.
unfold cfg_at. change (w64 HP_TAIL) with (Z_to_bv 64 HP_TAIL).
(* 0x82240..0x82248: a0 = at + 1, a1 = lp, call strstr *)
aj_run tbl_hp_ok HS HJ.
{ apply awr_ok_nil. }
pose proof (gframe_of_frame tfibsegs W (Ereg regs []) _ 2 0 0 (spZ regs)
  (spZ (cx_regs0 cx) - STK_has_prefixed) (spZ (cx_regs0 cx) - 104) _ _ HFr ltac:(vm_compute; reflexivity)
  ltac:(rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl); reflexivity) ltac:(rewrite FFS; lia) ltac:(lia)) as GF1.
clear HF HFr HG.
rreg HS (1%bv : bv 5) R1. rreg HS (10%bv : bv 5) R10. rreg HS (11%bv : bv 5) R11. rreg HS (21%bv : bv 5) R21.
lazymatch goal with |- SRr _ _ (mkCfg ?msx ?mdx) _ =>
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) (Ereg regs []) _ msx HS eq_refl); cbn [ss_pc];
  set (MS := msx) in *; set (MD := mdx) in * end.
assert (KP : regs_keep HP_KEEP regs (ms_regs MS))
  by exact (regs_keep_of_st_ok HP_KEEP _ _ _ regs [] HS HAE ltac:(vm_compute; reflexivity)).
assert (Hst1 : hp_st B cx a lyc Sc W (ms_regs MS) (ms_mem MS) MD).
{ apply (hp_st_move B cx a a lyc Sc W regs m mdc _ _ _ Hst HJ GF1 KP); [| exact Hmt].
  rewrite R21, (ew_Ereg_nat regs [] 21 21%bv eq_refl). exact Q21. }
assert (HxS : getr (ms_regs MS) 10 = w64 (cx_t cx + Z.of_nat (S a))).
{ rewrite R10, (ew_Ereg_nat regs [] 21 21%bv eq_refl), Q21. unfold w64. rewrite unsigned_lit_small by lia.
  f_equal. lia. }
assert (Hy : getr (ms_regs MS) 11 = w64 (cx_lp cx)) by (rewrite R11, (ew_Ereg_nat regs [] 8 8%bv eq_refl); exact Q8).
change (mkCfg (mkst (ms_regs MS) (Z_to_bv 64 PC_strstr) (ms_mem MS) (seg_rom tfibsegs)) MD)
  with (cfg_at tfibsegs PC_strstr (ms_regs MS) (ms_mem MS) MD).
apply (hp_call_rt B cx a lyc Sc W (ms_regs MS) (ms_mem MS) MD STK_RT_STRSTR PC_strstr 0x8224c
  (fun v => (v = 0 /\ no_occ (skipn (S a) (cx_tb cx)) (cx_lb cx)) \/
            (exists j, first_occ (skipn (S a) (cx_tb cx)) (cx_lb cx) j /\ v = cx_t cx + Z.of_nat (S a) + Z.of_nat j))
  Hst1).
- unfold STK_RT_STRSTR, ESTACK. lia.
- exact R1.
- lia.
- reflexivity.
- intros HPK. destruct (hp_rom B IMGF cx a lyc Sc W (ms_regs MS) (ms_mem MS) MD Hst1) as (HN & HO).
  destruct (hp_cstr B IMGF cx a lyc Sc W (ms_regs MS) (ms_mem MS) MD Hst1) as (Ht1 & Hl1).
  exact (hp_strstr_ro B ASTRSTR lyc Sc W (ms_regs MS) (ms_mem MS) MD (cx_t cx + Z.of_nat (S a)) (cx_lp cx)
    (skipn (S a) (cx_tb cx)) (cx_lb cx) HPK HN HO HxS Hy (g2_cstr_suffix W (ms_mem MS) (cx_t cx) (cx_tb cx) (S a) ltac:(lia) Ht1) Hl1).
- (* back at 0x8224c with a0 = v *)
  intros regs2 m2 md2 v Hst2 HP2 Ha0 Hv HRv.
  pose proof (hp_seat B cx a lyc Sc W regs2 m2 md2 0x8224c Hst2) as HS2.
  pose proof Hst2 as (_ & HJ2 & _ & _ & _ & Hsp2' & _).
  assert (HAE2 : env_agree 32 (Ereg regs2 []) (Ereg regs2 [])) by apply env_agree_refl.
  unfold cfg_at. change (w64 0x8224c) with (Z_to_bv 64 0x8224c).
  (* 0x8224c mv s5,a0; 0x82250 bnez a0 *)
  aj_run tbl_hp_ok HS2 HJ2.
  { apply awr_ok_nil. }
  pose proof (gframe_of_frame tfibsegs W (Ereg regs2 []) _ 2 0 0 (spZ regs)
    (spZ (cx_regs0 cx) - STK_has_prefixed) (spZ (cx_regs0 cx) - 104) _ _ HFr ltac:(vm_compute; reflexivity)
    ltac:(rewrite (ew_Ereg_nat regs2 [] 2 2%bv eq_refl); fold (spZ regs2); lia)
    ltac:(rewrite FFS; lia) ltac:(lia)) as GF2.
  clear HF HFr HG.
  assert (U10 : U (Ereg regs2 []) (SOff 10 0) = v).
  { apply (U_atom (Ereg regs2 []) 10 v); [rewrite (ew_Ereg_nat regs2 [] 10 10%bv eq_refl); exact Ha0 | exact Hv]. }
  srr_branch_with tbl_hp_ok HS2.
  + (* v <> 0: the next occurrence at S a + j; loop head *)
    rewrite branch_ne_U, U10, U_SLit in Hc. change (zcanon 0) with 0 in Hc.
    apply negb_true_iff, Z.eqb_neq in Hc.
    destruct HRv as [(Hv0 & _) | (j & Hfo & Hvj)]; [contradiction|].
    aj_run_to tbl_hp_ok HS2 HJ2 HP_HEAD.
    { apply awr_ok_nil. }
    pose proof (gframe_of_frame tfibsegs W (Ereg regs2 []) _ 2 0 0 (spZ regs)
      (spZ (cx_regs0 cx) - STK_has_prefixed) (spZ (cx_regs0 cx) - 104) _ _ HFr ltac:(vm_compute; reflexivity)
      ltac:(rewrite (ew_Ereg_nat regs2 [] 2 2%bv eq_refl); fold (spZ regs2); lia)
      ltac:(rewrite FFS; lia) ltac:(lia)) as GF3.
    clear HF HFr HG.
    rreg HS2 (21%bv : bv 5) S21.
    lazymatch goal with |- SRr _ _ (mkCfg ?msx ?mdx) _ =>
      rewrite (st_ok_restrict_mkst tfibsegs (w_H W) (Ereg regs2 []) _ msx HS2 eq_refl); cbn [ss_pc];
      set (MS2 := msx) in *; set (MD2 := mdx) in * end.
    assert (KP2 : regs_keep HP_KEEP regs2 (ms_regs MS2))
      by exact (regs_keep_of_st_ok HP_KEEP _ _ _ regs2 [] HS2 HAE2 ltac:(vm_compute; reflexivity)).
    assert (Hst3 : hp_st B cx (S a + j) lyc Sc W (ms_regs MS2) (ms_mem MS2) MD2).
    { apply (hp_st_move B cx a (S a + j) lyc Sc W regs2 m2 md2 _ _ _ Hst2 HJ2
        (gframe_seq tfibsegs W _ _ _ _ _ GF2 GF3) KP2).
      - rewrite S21, (ew_Ereg_nat regs2 [] 10 10%bv eq_refl), Ha0, Hvj. f_equal. lia.
      - exact (first_occ_mt (cx_tb cx) (cx_lb cx) (S a) j ltac:(lia) Hfo). }
    exact (KL j Hfo lyc Sc W (ms_regs MS2) (ms_mem MS2) MD2 Hst3 I).
  + (* v = 0: no further occurrence; `j 0x82280`, return 0 *)
    rewrite branch_ne_U, U10, U_SLit in Hc. change (zcanon 0) with 0 in Hc.
    apply negb_false_iff, Z.eqb_eq in Hc.
    assert (Hno : no_occ (skipn (S a) (cx_tb cx)) (cx_lb cx)).
    { destruct HRv as [(_ & Hno) | (j & _ & Hvj)]; [exact Hno | lia]. }
    aj_run_to tbl_hp_ok HS2 HJ2 A_hp_epi.
    { apply awr_ok_nil. }
    pose proof (gframe_of_frame tfibsegs W (Ereg regs2 []) _ 2 0 0 (spZ regs)
      (spZ (cx_regs0 cx) - STK_has_prefixed) (spZ (cx_regs0 cx) - 104) _ _ HFr ltac:(vm_compute; reflexivity)
      ltac:(rewrite (ew_Ereg_nat regs2 [] 2 2%bv eq_refl); fold (spZ regs2); lia)
      ltac:(rewrite FFS; lia) ltac:(lia)) as GF3.
    clear HF HFr HG.
    rreg HS2 (10%bv : bv 5) S10.
    lazymatch goal with |- SRr _ _ (mkCfg ?msx ?mdx) _ =>
      rewrite (st_ok_restrict_mkst tfibsegs (w_H W) (Ereg regs2 []) _ msx HS2 eq_refl); cbn [ss_pc];
      set (MS2 := msx) in *; set (MD2 := mdx) in * end.
    assert (KP2 : regs_keep [2; 3; 4]%bv regs2 (ms_regs MS2))
      by exact (regs_keep_of_st_ok [2; 3; 4]%bv _ _ _ regs2 [] HS2 HAE2 ltac:(vm_compute; reflexivity)).
    apply (hp_ret_step B TL cx a lyc Sc W regs2 m2 md2 _ _ _ Hst2 HJ2 (gframe_seq tfibsegs W _ _ _ _ _ GF2 GF3) KP2).
    rewrite S10, (ew_Ereg_nat regs2 [] 10 10%bv eq_refl), Ha0, Hc, (KZ Hno). reflexivity.
Qed.
End s.
