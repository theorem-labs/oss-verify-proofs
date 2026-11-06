(* check_reject_clean_starved 0x80e44 (fuzz_manifest.c:226-234), 23 instructions: s2 := fuzz_alloc_live();
   fuzz_alloc_fail(0); lv2_locate_manifest_names (text, uri); fuzz_alloc_fail(SIZE_MAX); then the tail call
   check_reject_clean(s2). The reader's one allocation fails and it holds nothing (names_spec, case 2), so g_live is
   back at live_before and check_reject_clean's abort is dead. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI16 YK06 YM05 YG0q YC20.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v FMupoison FMPstat FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_K FMW_kit FMW_kitS.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition sv_tbl : ctable := Eval vm_compute in build_table tfibsegs A_check_reject_clean_starved 23 TEmpty.
Lemma sv_tbl_ok : table_ok tfibsegs sv_tbl.
Proof.
assert (E : sv_tbl = build_table tfibsegs A_check_reject_clean_starved 23 TEmpty) by (vm_cast_no_check (eq_refl sv_tbl)).
rewrite E. apply build_table_ok0. unfold A_check_reject_clean_starved. lia.
Qed.
(* the registers at the tail call: sp back up, ra and s0..s2 reloaded, the rest kept *)
Definition sv_expect (r : bv 5) : sv :=
  match bv_unsigned r with 2 => SOff 2 32 | 8 => SOff 33 0 | 9 => SOff 34 0 | 18 => SOff 35 0
  | z => SOff (Z.to_nat z) 0 end.
Definition sv_X : list Z := [2; 8; 9; 18].
(* fuzz_alloc_fail(SIZE_MAX) leaves g_fail_at at SIZE_MAX *)
Lemma fail_max : forall c, 0 <= c -> (if c + SIZE_MAXZ <? 2 ^ 64 then c + SIZE_MAXZ else SIZE_MAXZ) = SIZE_MAXZ.
Proof. intros c Hc. destruct (Z.ltb_spec (c + SIZE_MAXZ) (2 ^ 64)); unfold SIZE_MAXZ in *; lia. Qed.
(* the saved word at off from the entry sp, read off the call-site region *)
Ltac sv_slot HR0 Usp off n v :=
  apply (fmw_field _ _ 2 _ _ _ _ _ _ off 8%N (SOff n 0) v HR0 Usp ltac:(cbn; tauto)); [| apply u64_range | cbn; lia].
(* the frame left by a resumed run (fss_ret 32 cs) as same_below *)
Ltac sv_sb HF E m1 m2 Esp cs :=
  change (frame_of E [fstk_ret 32 cs] m1 m2) in HF;
  apply (same_below_frame1 E _ m1 m2 alloc_ceiling HF); [cbn [fstk_ret YP09.r_base YP09.r_wlo base_val]; rewrite Esp; lia | lia].
(* the saved-register chunks of the call-site region, for the state after the call *)
Ltac sv_chk HSc Esp regsN :=
  pose proof (fmw_region_nth _ _ _ 0 _ HSc eq_refl) as HRk; cbn [ms_mem restrict] in HRk;
  destruct HRk as (_ & _ & _ & Hcsk); cbn [YP09.r_base YP09.r_chunks base_val] in Hcsk; rewrite Esp in Hcsk;
  eapply (fmw_chunks_extra _ regsN); [repeat (apply Forall_cons; [do 2 eexists; reflexivity|]); apply Forall_nil | exact Hcsk].

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable CTXn : list (list Z).
Hypothesis LIVE : fuzz_alloc_live_spec tfibsegs B.
Hypothesis FAIL : fuzz_alloc_fail_spec tfibsegs B.
Hypothesis NAMES : names_spec tfibsegs B CTXn.
Hypothesis HCTX : In [0x80e7c] CTXn.
Hypothesis CRC : check_reject_clean_spec tfibsegs B.
Hypothesis IMG : fm_img_facts tfibsegs B.

Theorem check_reject_clean_starved_holds : forall CTX, check_reject_clean_starved_spec tfibsegs B CTX.
Proof.
intros CTX ly S W regs mem md ch t u tb ub live peak cnt fail HPRE _ H10 H11 Ht Hu Hkt Hku Hlu Hlt HG HQ HL Hev Hlv.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
destruct HPRE as [HAP HRO].
pose proof (fmw_sp B _ ly S W regs mem md ch HAP) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof HQ as (Hfail & Hc0 & Hc1).
pose proof Hu as (_ & Hu4 & Hucl & _).
assert (FS : STK_check_reject_clean_starved = ltac:(let v := eval vm_compute in STK_check_reject_clean_starved in exact v))
  by reflexivity.
assert (FN : STK_names = ltac:(let v := eval vm_compute in STK_names in exact v)) by reflexivity.
assert (FA : STK_fuzz_alloc = 16) by reflexivity. assert (FC : STK_check_reject_clean = 32) by reflexivity.
unfold EV_check_reject_clean_starved in Hev.
pose proof (fmw_entry B STK_check_reject_clean_starved 32 ly S W regs mem md ch A_check_reject_clean_starved HAP
  ltac:(lia) ltac:(vm_compute; reflexivity)) as HS.
pose proof (ajournal_init tfibsegs B STK_check_reject_clean_starved FM_PSTAT_FP ly S W regs mem md ch HAP) as HJ.
set (E := Ereg regs []) in HS.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl); reflexivity).
assert (Us0 : bv_unsigned (w64 u) = u) by (unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
unfold cfg_at. change (w64 A_check_reject_clean_starved) with (Z_to_bv 64 A_check_reject_clean_starved).
aj_run_to sv_tbl_ok HS HJ A_fuzz_alloc_live.
{ awr_ok_tac. exact Usp. }
(* ======== call 1: fuzz_alloc_live at 0x80e60 ======== *)
assert (SB1 : same_below mem (ms_mem ms) alloc_ceiling).
{ change (frame_of E [fstk 32] mem (ms_mem ms)) in HF.
  apply (same_below_frame1 E (fstk 32) mem (ms_mem ms) alloc_ceiling HF); [|lia].
  cbn [fstk YP09.r_base YP09.r_wlo base_val]. rewrite Usp. lia. }
pose proof (fmw_reg_lit _ E _ ms 1%bv 0x80e64 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as R1.
pose proof (fmw_reg_off _ E _ ms 2%bv 2 (-32) (spZ regs) HS ltac:(vm_compute; reflexivity) Usp ltac:(lia)) as R2.
pose proof (fmw_reg_atom _ regs [] _ ms 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl) as R3.
pose proof (fmw_reg_atom _ regs [] _ ms 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl) as R4.
pose proof (fmw_reg_atom _ regs [] _ ms 8%bv 11%bv 11 HS ltac:(vm_compute; reflexivity) eq_refl) as R8.
assert (Hspc : spZ (ms_regs ms) = spZ regs - 32) by (unfold spZ at 1; rewrite R2; lia).
assert (HROc : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W) (ms_mem ms)))
  by exact (arodata_below B W mem (ms_mem ms) SB1 HRO).
assert (HPREc : fpre tfibsegs B STK_fuzz_alloc ly S W (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md) []).
{ split; [|exact HROc].
  apply (afn_pre_at tfibsegs B STK_check_reject_clean_starved (spZ regs) FM_PSTAT_FP ly S W mem md [] ly S W (ms_mem ms) _ 0
    (ms_regs ms) STK_fuzz_alloc (-32) [] HJ); try lia.
  - rewrite R1. apply ret_ok_even. rewrite unsigned_lit_small by lia. reflexivity.
  - unfold raZ. rewrite R1, unsigned_lit_small by lia. lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - apply achain_low. unfold s0Z. rewrite R8, H11, Us0. lia. }
pose proof (cstr_ok_below W mem (ms_mem ms) t tb SB1 Ht) as Htc.
pose proof (cstr_ok_below W mem (ms_mem ms) u ub SB1 Hu) as Huc.
pose proof (fmw_region_nth E _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
assert (V1 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (spZ regs + -8) (N.to_nat 8) (bv_unsigned (getr regs 1))).
{ sv_slot HR0 Usp (-8) 1%nat (bv_unsigned (getr regs 1)). rewrite fmw_SOff0; subst E; rewrite (ew_Ereg_nat regs [] 1 1%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned. }
assert (V8 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (spZ regs + -16) (N.to_nat 8) (bv_unsigned (getr regs 8))).
{ sv_slot HR0 Usp (-16) 8%nat (bv_unsigned (getr regs 8)). rewrite fmw_SOff0; subst E; rewrite (ew_Ereg_nat regs [] 8 8%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned. }
assert (V9 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (spZ regs + -24) (N.to_nat 8) (bv_unsigned (getr regs 9))).
{ sv_slot HR0 Usp (-24) 9%nat (bv_unsigned (getr regs 9)). rewrite fmw_SOff0; subst E; rewrite (ew_Ereg_nat regs [] 9 9%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned. }
assert (V18 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (spZ regs + -32) (N.to_nat 8) (bv_unsigned (getr regs 18))).
{ sv_slot HR0 Usp (-32) 18%nat (bv_unsigned (getr regs 18)). rewrite fmw_SOff0; subst E; rewrite (ew_Ereg_nat regs [] 18 18%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned. }
clear HR0.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms HS eq_refl). cbn [ss_pc].
eapply SRr_bind;
  [exact (LIVE ly S W (ms_regs ms) (ms_mem ms) _ [] live peak cnt fail HPREc (fm_glob_below W mem (ms_mem ms) _ _ _ _ SB1 HG)) |].
intros W1 c1 Hwle1 (ly1 & S1 & regs1 & mem1 & md1 & -> & HJc1 & HP1 & H10a & Hbl1 & GL1).
set (extra := [getr regs 1; getr regs 8; getr regs 9; getr regs 18]).
set (cs := [YP09.mkChunk 24 (CVal 8 (SOff 32 0)); YP09.mkChunk 16 (CVal 8 (SOff 33 0));
            YP09.mkChunk 8 (CVal 8 (SOff 34 0)); YP09.mkChunk 0 (CVal 8 (SOff 35 0))]).
assert (CHK : Forall (YP09.chunk_ok tfibsegs (Ereg regs1 extra) (mrestrict (w_H W) (ms_mem ms)) (spZ regs - 32)) cs).
{ constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
  - apply (chunk_ok_val tfibsegs _ _ _ 24 8%N (SOff 32 0) (bv_unsigned (getr regs 1)));
      [rewrite fmw_SOff0; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; cbn [nth extra]; symmetry; apply Z_to_bv_bv_unsigned
      | apply u64_range | cbn; lia | replace (spZ regs - 32 + 24) with (spZ regs + -8) by lia; exact V1].
  - apply (chunk_ok_val tfibsegs _ _ _ 16 8%N (SOff 33 0) (bv_unsigned (getr regs 8)));
      [rewrite fmw_SOff0; change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; cbn [nth extra]; symmetry; apply Z_to_bv_bv_unsigned
      | apply u64_range | cbn; lia | replace (spZ regs - 32 + 16) with (spZ regs + -16) by lia; exact V8].
  - apply (chunk_ok_val tfibsegs _ _ _ 8 8%N (SOff 34 0) (bv_unsigned (getr regs 9)));
      [rewrite fmw_SOff0; change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; cbn [nth extra]; symmetry; apply Z_to_bv_bv_unsigned
      | apply u64_range | cbn; lia | replace (spZ regs - 32 + 8) with (spZ regs + -24) by lia; exact V9].
  - apply (chunk_ok_val tfibsegs _ _ _ 0 8%N (SOff 35 0) (bv_unsigned (getr regs 18)));
      [rewrite fmw_SOff0; change 35%nat with (32 + 3)%nat; rewrite ew_Ereg_extra; cbn [nth extra]; symmetry; apply Z_to_bv_bv_unsigned
      | apply u64_range | cbn; lia | replace (spZ regs - 32 + 0) with (spZ regs + -32) by lia; exact V18]. }
destruct (fmw_after_call B STK_check_reject_clean_starved (spZ regs) FM_PSTAT_FP ly S W mem md ly S W (ms_mem ms) _ 0
  STK_fuzz_alloc [] 32 (ms_regs ms) ly1 S1 W1 regs1 mem1 md1 0 extra cs 0x80e64 HJ HJc1
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HP1 Hspc ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(reflexivity) ltac:(vm_compute; reflexivity) ltac:(repeat constructor; cbn; lia) CHK) as [HJ1 HS1].
pose proof (kept_step (w_H W) regs regs [] _ ms regs1 sv_X (kept_refl regs sv_X) HS ltac:(vm_compute; reflexivity) HP1) as HK1.
assert (K8a : getr regs1 8 = w64 u) by exact (fmw_carry _ regs [] _ ms regs1 8%bv 11 _ HS ltac:(vm_compute; reflexivity)
  ltac:(rewrite (ew_Ereg_nat regs [] 11 11%bv eq_refl); exact H11) HP1 ltac:(fmw_cs_side)).
assert (K9a : getr regs1 9 = w64 t) by exact (fmw_carry _ regs [] _ ms regs1 9%bv 10 _ HS ltac:(vm_compute; reflexivity)
  ltac:(rewrite (ew_Ereg_nat regs [] 10 10%bv eq_refl); exact H10) HP1 ltac:(fmw_cs_side)).
rename HS into HSc0. clear HJ HF HFr CHK.
rewrite R1.
assert (E1 : bv_unsigned (ew (Ereg regs1 extra) 2) = spZ regs + -32).
{ rewrite (ew_Ereg_nat regs1 extra 2 2%bv eq_refl), (fmw_pres _ _ 2%bv HP1 ltac:(fmw_cs_side)). lia. }
assert (Hinc1 : forall x, In x (ablocks B ly S) -> In x (ablocks B ly1 S1)) by (rewrite Hbl1; auto).
pose proof (arodata_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc1 nil_closed nil_not_roP HROc) as HRO1.
pose proof (cstr_ok_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t tb IMG HJc1 Hinc1 nil_img HRO1 Hkt Htc) as Ht1.
pose proof (cstr_ok_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ u ub IMG HJc1 Hinc1 nil_img HRO1 Hku Huc) as Hu1.
pose proof (cstr_kept_kept B ly S ly1 S1 t tb Hinc1 Hkt) as Hkt1.
pose proof (cstr_kept_kept B ly S ly1 S1 u ub Hinc1 Hku) as Hku1.
aj_run_to sv_tbl_ok HS1 HJ1 A_fuzz_alloc_fail.
{ fmw_awr_ret E1 32. }
(* ======== call 2: fuzz_alloc_fail(0) at 0x80e6c ======== *)
assert (SB2 : same_below mem1 (ms_mem ms0) alloc_ceiling) by (sv_sb HF (Ereg regs1 extra) mem1 (ms_mem ms0) E1 cs).
pose proof (fmw_reg_lit _ _ _ ms0 1%bv 0x80e70 HS1 ltac:(vm_compute; reflexivity) ltac:(lia)) as R1b.
pose proof (fmw_reg_off _ _ _ ms0 2%bv 2 0 (spZ regs + -32) HS1 ltac:(vm_compute; reflexivity) E1 ltac:(lia)) as R2b.
pose proof (fmw_reg_lit _ _ _ ms0 10%bv 0 HS1 ltac:(vm_compute; reflexivity) ltac:(lia)) as R10b.
pose proof (fmw_reg_atom _ regs1 extra _ ms0 3%bv 3%bv 3 HS1 ltac:(vm_compute; reflexivity) eq_refl) as R3b.
pose proof (fmw_reg_atom _ regs1 extra _ ms0 4%bv 4%bv 4 HS1 ltac:(vm_compute; reflexivity) eq_refl) as R4b.
pose proof (fmw_reg_atom _ regs1 extra _ ms0 8%bv 8%bv 8 HS1 ltac:(vm_compute; reflexivity) eq_refl) as R8b.
assert (Hspc2 : spZ (ms_regs ms0) = spZ regs - 32) by (unfold spZ at 1; rewrite R2b; lia).
assert (HRO1c : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W1) (ms_mem ms0)))
  by exact (arodata_below B W1 mem1 (ms_mem ms0) SB2 HRO1).
assert (HPREc2 : fpre tfibsegs B STK_fuzz_alloc ly1 S1 W1 (ms_regs ms0) (ms_mem ms0)
  (with_vm_backing (m_vm_lazy md1) mat0 md1) []).
{ split; [|exact HRO1c].
  apply (afn_pre_at tfibsegs B STK_check_reject_clean_starved (spZ regs) FM_PSTAT_FP ly S W mem md [] _ _ _ _ _ _
    (ms_regs ms0) STK_fuzz_alloc (-32) [] HJ1); try lia.
  - rewrite R1b. apply ret_ok_even. rewrite unsigned_lit_small by lia. reflexivity.
  - unfold raZ. rewrite R1b, unsigned_lit_small by lia. lia.
  - rewrite R3b. rewrite (kept_get _ _ _ 3%bv HK1 ltac:(fmw_cs_side) ltac:(fmw_notin)). exact Hgp.
  - rewrite R4b. rewrite (kept_get _ _ _ 4%bv HK1 ltac:(fmw_cs_side) ltac:(fmw_notin)). exact Htp.
  - apply achain_low. unfold s0Z. rewrite R8b, K8a, Us0. lia. }
rewrite (st_ok_restrict_mkst tfibsegs (w_H W1) (Ereg regs1 extra) _ ms0 HS1 eq_refl). cbn [ss_pc].
eapply SRr_bind;
  [exact (FAIL ly1 S1 W1 (ms_regs ms0) (ms_mem ms0) _ [] live peak cnt fail 0 HPREc2
     (fm_glob_below W1 mem1 (ms_mem ms0) _ _ _ _ SB2 GL1) ltac:(rewrite R10b; reflexivity) ltac:(lia)) |].
intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJc2 & HP2 & Hbl2 & GL2).
replace (if cnt + 0 <? 2 ^ 64 then cnt + 0 else SIZE_MAXZ) with cnt in GL2
  by (rewrite Z.add_0_r; destruct (Z.ltb_spec cnt (2 ^ 64)); lia).
assert (CHK2 : Forall (YP09.chunk_ok tfibsegs (Ereg regs2 extra) (mrestrict (w_H W1) (ms_mem ms0)) (spZ regs - 32)) cs)
  by (sv_chk HS1 E1 regs2).
destruct (fmw_after_call B STK_check_reject_clean_starved (spZ regs) FM_PSTAT_FP ly S W mem md ly1 S1 W1 (ms_mem ms0) _ _
  STK_fuzz_alloc FM_PSTAT_FP 32 (ms_regs ms0) ly2 S2 W2 regs2 mem2 md2 0 extra cs 0x80e70 HJ1 HJc2
  ltac:(intros a Ha; exact Ha) HP2 Hspc2 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(reflexivity) ltac:(vm_compute; reflexivity) ltac:(repeat constructor; cbn; lia) CHK2) as [HJ2 HS2].
pose proof (kept_step (w_H W1) regs regs1 extra _ ms0 regs2 sv_X HK1 HS1 ltac:(vm_compute; reflexivity) HP2) as HK2.
assert (K8b : getr regs2 8 = w64 u) by exact (fmw_carry _ regs1 extra _ ms0 regs2 8%bv 8 _ HS1 ltac:(vm_compute; reflexivity)
  ltac:(rewrite (ew_Ereg_nat regs1 extra 8 8%bv eq_refl); exact K8a) HP2 ltac:(fmw_cs_side)).
assert (K9b : getr regs2 9 = w64 t) by exact (fmw_carry _ regs1 extra _ ms0 regs2 9%bv 9 _ HS1 ltac:(vm_compute; reflexivity)
  ltac:(rewrite (ew_Ereg_nat regs1 extra 9 9%bv eq_refl); exact K9a) HP2 ltac:(fmw_cs_side)).
assert (K18b : getr regs2 18 = w64 live) by exact (fmw_carry _ regs1 extra _ ms0 regs2 18%bv 10 _ HS1
  ltac:(vm_compute; reflexivity) ltac:(rewrite (ew_Ereg_nat regs1 extra 10 10%bv eq_refl); exact H10a) HP2 ltac:(fmw_cs_side)).
rename HS1 into HSc1. clear HJ1 HF HFr CHK2.
rewrite R1b.
assert (E2 : bv_unsigned (ew (Ereg regs2 extra) 2) = spZ regs + -32).
{ rewrite (ew_Ereg_nat regs2 extra 2 2%bv eq_refl), (fmw_pres _ _ 2%bv HP2 ltac:(fmw_cs_side)). unfold spZ in Hspc2. lia. }
assert (Hinc2 : forall x, In x (ablocks B ly1 S1) -> In x (ablocks B ly2 S2)) by (rewrite Hbl2; auto).
pose proof (arodata_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc2 pstat_closed pstat_not_roP HRO1c) as HRO2.
pose proof (cstr_ok_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t tb IMG HJc2 Hinc2 pstat_img HRO2 Hkt1
  (cstr_ok_below W1 mem1 (ms_mem ms0) t tb SB2 Ht1)) as Ht2.
pose proof (cstr_ok_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ u ub IMG HJc2 Hinc2 pstat_img HRO2 Hku1
  (cstr_ok_below W1 mem1 (ms_mem ms0) u ub SB2 Hu1)) as Hu2.
pose proof (cstr_kept_kept B ly1 S1 ly2 S2 t tb Hinc2 Hkt1) as Hkt2.
pose proof (cstr_kept_kept B ly1 S1 ly2 S2 u ub Hinc2 Hku1) as Hku2.
aj_run_to sv_tbl_ok HS2 HJ2 A_names.
{ fmw_awr_ret E2 32. }
(* ======== call 3: lv2_locate_manifest_names at 0x80e78 ======== *)
assert (SB3 : same_below mem2 (ms_mem ms1) alloc_ceiling) by (sv_sb HF (Ereg regs2 extra) mem2 (ms_mem ms1) E2 cs).
pose proof (fmw_reg_lit _ _ _ ms1 1%bv 0x80e7c HS2 ltac:(vm_compute; reflexivity) ltac:(lia)) as R1c.
pose proof (fmw_reg_off _ _ _ ms1 2%bv 2 0 (spZ regs + -32) HS2 ltac:(vm_compute; reflexivity) E2 ltac:(lia)) as R2c.
pose proof (fmw_reg_atom _ regs2 extra _ ms1 3%bv 3%bv 3 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R3c.
pose proof (fmw_reg_atom _ regs2 extra _ ms1 4%bv 4%bv 4 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R4c.
pose proof (fmw_reg_atom _ regs2 extra _ ms1 8%bv 8%bv 8 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R8c.
pose proof (fmw_reg_atom _ regs2 extra _ ms1 10%bv 9%bv 9 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R10c.
pose proof (fmw_reg_atom _ regs2 extra _ ms1 11%bv 8%bv 8 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R11c.
assert (Hspc3 : spZ (ms_regs ms1) = spZ regs - 32) by (unfold spZ at 1; rewrite R2c; lia).
assert (HRO2c : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W2) (ms_mem ms1)))
  by exact (arodata_below B W2 mem2 (ms_mem ms1) SB3 HRO2).
assert (HPREc3 : fpre tfibsegs B STK_names ly2 S2 W2 (ms_regs ms1) (ms_mem ms1)
  (with_vm_backing (m_vm_lazy md2) mat1 md2) []).
{ split; [|exact HRO2c].
  apply (afn_pre_at tfibsegs B STK_check_reject_clean_starved (spZ regs) FM_PSTAT_FP ly S W mem md [] _ _ _ _ _ _
    (ms_regs ms1) STK_names (-32) [] HJ2); try lia.
  - rewrite R1c. apply ret_ok_even. rewrite unsigned_lit_small by lia. reflexivity.
  - unfold raZ. rewrite R1c, unsigned_lit_small by lia. lia.
  - rewrite R3c. rewrite (kept_get _ _ _ 3%bv HK2 ltac:(fmw_cs_side) ltac:(fmw_notin)). exact Hgp.
  - rewrite R4c. rewrite (kept_get _ _ _ 4%bv HK2 ltac:(fmw_cs_side) ltac:(fmw_notin)). exact Htp.
  - apply achain_low. unfold s0Z. rewrite R8c, K8b, Us0. lia. }
assert (HRAc3 : raZ (ms_regs ms1) = 0x80e7c) by (unfold raZ; rewrite R1c, unsigned_lit_small by lia; reflexivity).
assert (Hnev : st_nev S2 + EV_names <= EV_MAX).
{ pose proof HJ2 as (_ & _ & _ & _ & _ & _ & Hnv & _). lia. }
assert (Hbb : blocks_bytes S2 + LIVE_names <= LIVE_MAX).
{ rewrite (bb_eq B ly S ly2 S2 ltac:(rewrite Hbl2, Hbl1; reflexivity)). exact Hlv. }
rewrite (st_ok_restrict_mkst tfibsegs (w_H W2) (Ereg regs2 extra) _ ms1 HS2 eq_refl). cbn [ss_pc].
eapply SRr_bind;
  [exact (NAMES ly2 S2 W2 (ms_regs ms1) (ms_mem ms1) _ [] t u tb ub live peak cnt cnt HPREc3
     ltac:(rewrite HRAc3; exact HCTX) ltac:(rewrite R10c; exact K9b) ltac:(rewrite R11c; exact K8b)
     (cstr_ok_below W2 mem2 (ms_mem ms1) t tb SB3 Ht2) (cstr_ok_below W2 mem2 (ms_mem ms1) u ub SB3 Hu2)
     Hkt2 Hku2 Hlu Hlt (fm_glob_below W2 mem2 (ms_mem ms1) _ _ _ _ SB3 GL2) HL ltac:(lia) Hnev Hbb) |].
intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJc3 & HP3 & (res & H10r & Hperm3 & HNR3)).
pose proof (names_res_starved W3 mem3 tb ub live peak cnt res HNR3) as GL3.
assert (CHK3 : Forall (YP09.chunk_ok tfibsegs (Ereg regs3 extra) (mrestrict (w_H W2) (ms_mem ms1)) (spZ regs - 32)) cs)
  by (sv_chk HS2 E2 regs3).
destruct (fmw_after_call B STK_check_reject_clean_starved (spZ regs) FM_PSTAT_FP ly S W mem md ly2 S2 W2 (ms_mem ms1) _ _
  STK_names FM_PSTAT_FP 32 (ms_regs ms1) ly3 S3 W3 regs3 mem3 md3 EV_names extra cs 0x80e7c HJ2 HJc3
  ltac:(intros a Ha; exact Ha) HP3 Hspc3 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(reflexivity) ltac:(vm_compute; reflexivity) ltac:(repeat constructor; cbn; lia) CHK3) as [HJ3 HS3].
pose proof (kept_step (w_H W2) regs regs2 extra _ ms1 regs3 sv_X HK2 HS2 ltac:(vm_compute; reflexivity) HP3) as HK3.
assert (K8c : getr regs3 8 = w64 u) by exact (fmw_carry _ regs2 extra _ ms1 regs3 8%bv 8 _ HS2 ltac:(vm_compute; reflexivity)
  ltac:(rewrite (ew_Ereg_nat regs2 extra 8 8%bv eq_refl); exact K8b) HP3 ltac:(fmw_cs_side)).
assert (K18c : getr regs3 18 = w64 live) by exact (fmw_carry _ regs2 extra _ ms1 regs3 18%bv 18 _ HS2
  ltac:(vm_compute; reflexivity) ltac:(rewrite (ew_Ereg_nat regs2 extra 18 18%bv eq_refl); exact K18b) HP3 ltac:(fmw_cs_side)).
rename HS2 into HSc2. clear HJ2 HF HFr CHK3.
rewrite R1c.
assert (E3 : bv_unsigned (ew (Ereg regs3 extra) 2) = spZ regs + -32).
{ rewrite (ew_Ereg_nat regs3 extra 2 2%bv eq_refl), (fmw_pres _ _ 2%bv HP3 ltac:(fmw_cs_side)). unfold spZ in Hspc3. lia. }
pose proof (arodata_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc3 pstat_closed pstat_not_roP HRO2c) as HRO3.
aj_run_to sv_tbl_ok HS3 HJ3 A_fuzz_alloc_fail.
{ fmw_awr_ret E3 32. }
(* ======== call 4: fuzz_alloc_fail(SIZE_MAX) at 0x80e80 ======== *)
assert (SB4 : same_below mem3 (ms_mem ms2) alloc_ceiling) by (sv_sb HF (Ereg regs3 extra) mem3 (ms_mem ms2) E3 cs).
pose proof (fmw_reg_lit _ _ _ ms2 1%bv 0x80e84 HS3 ltac:(vm_compute; reflexivity) ltac:(lia)) as R1d.
pose proof (fmw_reg_off _ _ _ ms2 2%bv 2 0 (spZ regs + -32) HS3 ltac:(vm_compute; reflexivity) E3 ltac:(lia)) as R2d.
pose proof (fmw_reg_lit _ _ _ ms2 10%bv SIZE_MAXZ HS3 ltac:(vm_compute; reflexivity) ltac:(unfold SIZE_MAXZ; lia)) as R10d.
pose proof (fmw_reg_atom _ regs3 extra _ ms2 3%bv 3%bv 3 HS3 ltac:(vm_compute; reflexivity) eq_refl) as R3d.
pose proof (fmw_reg_atom _ regs3 extra _ ms2 4%bv 4%bv 4 HS3 ltac:(vm_compute; reflexivity) eq_refl) as R4d.
pose proof (fmw_reg_atom _ regs3 extra _ ms2 8%bv 8%bv 8 HS3 ltac:(vm_compute; reflexivity) eq_refl) as R8d.
assert (Hspc4 : spZ (ms_regs ms2) = spZ regs - 32) by (unfold spZ at 1; rewrite R2d; lia).
assert (HRO3c : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W3) (ms_mem ms2)))
  by exact (arodata_below B W3 mem3 (ms_mem ms2) SB4 HRO3).
assert (HPREc4 : fpre tfibsegs B STK_fuzz_alloc ly3 S3 W3 (ms_regs ms2) (ms_mem ms2)
  (with_vm_backing (m_vm_lazy md3) mat2 md3) []).
{ split; [|exact HRO3c].
  apply (afn_pre_at tfibsegs B STK_check_reject_clean_starved (spZ regs) FM_PSTAT_FP ly S W mem md [] _ _ _ _ _ _
    (ms_regs ms2) STK_fuzz_alloc (-32) [] HJ3); try lia.
  - rewrite R1d. apply ret_ok_even. rewrite unsigned_lit_small by lia. reflexivity.
  - unfold raZ. rewrite R1d, unsigned_lit_small by lia. lia.
  - rewrite R3d. rewrite (kept_get _ _ _ 3%bv HK3 ltac:(fmw_cs_side) ltac:(fmw_notin)). exact Hgp.
  - rewrite R4d. rewrite (kept_get _ _ _ 4%bv HK3 ltac:(fmw_cs_side) ltac:(fmw_notin)). exact Htp.
  - apply achain_low. unfold s0Z. rewrite R8d, K8c, Us0. lia. }
rewrite (st_ok_restrict_mkst tfibsegs (w_H W3) (Ereg regs3 extra) _ ms2 HS3 eq_refl). cbn [ss_pc].
eapply SRr_bind;
  [exact (FAIL ly3 S3 W3 (ms_regs ms2) (ms_mem ms2) _ [] live peak _ _ SIZE_MAXZ HPREc4
     (fm_glob_below W3 mem3 (ms_mem ms2) _ _ _ _ SB4 GL3) ltac:(rewrite R10d; reflexivity) ltac:(unfold SIZE_MAXZ; lia)) |].
intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJc4 & HP4 & Hbl4 & GL4).
rewrite fail_max in GL4 by (destruct (length ub =? 0)%nat; lia).
assert (CHK4 : Forall (YP09.chunk_ok tfibsegs (Ereg regs4 extra) (mrestrict (w_H W3) (ms_mem ms2)) (spZ regs - 32)) cs)
  by (sv_chk HS3 E3 regs4).
destruct (fmw_after_call B STK_check_reject_clean_starved (spZ regs) FM_PSTAT_FP ly S W mem md ly3 S3 W3 (ms_mem ms2) _ _
  STK_fuzz_alloc FM_PSTAT_FP 32 (ms_regs ms2) ly4 S4 W4 regs4 mem4 md4 0 extra cs 0x80e84 HJ3 HJc4
  ltac:(intros a Ha; exact Ha) HP4 Hspc4 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(reflexivity) ltac:(vm_compute; reflexivity) ltac:(repeat constructor; cbn; lia) CHK4) as [HJ4 HS4].
pose proof (kept_step (w_H W3) regs regs3 extra _ ms2 regs4 sv_X HK3 HS3 ltac:(vm_compute; reflexivity) HP4) as HK4.
assert (K18d : getr regs4 18 = w64 live) by exact (fmw_carry _ regs3 extra _ ms2 regs4 18%bv 18 _ HS3
  ltac:(vm_compute; reflexivity) ltac:(rewrite (ew_Ereg_nat regs3 extra 18 18%bv eq_refl); exact K18c) HP4 ltac:(fmw_cs_side)).
rename HS3 into HSc3. clear HJ3 HF HFr CHK4.
rewrite R1d.
assert (E4 : bv_unsigned (ew (Ereg regs4 extra) 2) = spZ regs + -32).
{ rewrite (ew_Ereg_nat regs4 extra 2 2%bv eq_refl), (fmw_pres _ _ 2%bv HP4 ltac:(fmw_cs_side)). unfold spZ in Hspc4. lia. }
pose proof (arodata_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc4 pstat_closed pstat_not_roP HRO3c) as HRO4.
aj_run_to sv_tbl_ok HS4 HJ4 A_check_reject_clean.
{ fmw_awr_ret E4 32. }
(* ======== the tail call of check_reject_clean at 0x80e9c ======== *)
assert (SB5 : same_below mem4 (ms_mem ms3) alloc_ceiling) by (sv_sb HF (Ereg regs4 extra) mem4 (ms_mem ms3) E4 cs).
pose proof (fmw_reg_extra _ regs4 extra _ ms3 1%bv 0 HS4 ltac:(vm_compute; reflexivity)) as RT1. cbn [nth extra] in RT1.
pose proof (fmw_reg_off _ _ _ ms3 2%bv 2 32 (spZ regs + -32) HS4 ltac:(vm_compute; reflexivity) E4 ltac:(lia)) as RT2.
pose proof (fmw_reg_atom _ regs4 extra _ ms3 10%bv 18%bv 18 HS4 ltac:(vm_compute; reflexivity) eq_refl) as RT10.
pose proof (fmw_reg_extra _ regs4 extra _ ms3 8%bv 1 HS4 ltac:(vm_compute; reflexivity)) as RT8. cbn [nth extra] in RT8.
assert (HspT : spZ (ms_regs ms3) = spZ regs) by (unfold spZ at 1; rewrite RT2; lia).
assert (HPT : aregs_preserved regs (ms_regs ms3)).
{ apply (fmw_preserved _ _ _ ms3 regs sv_expect HS4); [vm_compute; reflexivity|]. fmw_cs_cases_k sv_expect E4 HK4. }
assert (HPREt : fpre tfibsegs B STK_check_reject_clean ly4 S4 W4 (ms_regs ms3) (ms_mem ms3)
  (with_vm_backing (m_vm_lazy md4) mat3 md4) ch).
{ split; [|exact (arodata_below B W4 mem4 (ms_mem ms3) SB5 HRO4)].
  apply (afn_pre_at tfibsegs B STK_check_reject_clean_starved (spZ regs) FM_PSTAT_FP ly S W mem md [] _ _ _ _ _ _
    (ms_regs ms3) STK_check_reject_clean 0 ch HJ4); try lia.
  - rewrite RT1. exact Hra.
  - unfold raZ. rewrite RT1. exact Hra4.
  - rewrite (fmw_pres _ _ 3%bv HPT ltac:(fmw_cs_side)). exact Hgp.
  - rewrite (fmw_pres _ _ 4%bv HPT ltac:(fmw_cs_side)). exact Htp.
  - rewrite HspT. unfold s0Z. rewrite RT8. fold (s0Z regs).
    exact (fmw_achain_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4 Hch). }
rewrite (st_ok_restrict_mkst tfibsegs (w_H W4) (Ereg regs4 extra) _ ms3 HS4 eq_refl). cbn [ss_pc].
eapply SRr_bind;
  [exact (CRC ly4 S4 W4 (ms_regs ms3) (ms_mem ms3) _ ch live peak _ _ HPREt
     (fm_glob_below W4 mem4 (ms_mem ms3) _ _ _ _ SB5 GL4) ltac:(rewrite RT10, K18d; reflexivity)) |].
intros W5 c5 Hwle5 (ly5 & S5 & regs5 & mem5 & md5 & -> & HJc5 & HP5 & Hbl5 & GL5).
apply SRr_ret. unfold fpost, apost_base.
exists ly5, S5, regs5, mem5, md5.
split; [rewrite RT1; reflexivity|].
split.
{ rewrite HspT in HJc5.
  exact (ajournal_sub_incl B STK_check_reject_clean_starved (spZ regs) FM_PSTAT_FP ly S W mem md [] _ _ _ _ _ _
    STK_check_reject_clean (spZ regs) [] [] ly5 S5 W5 mem5 md5 0 HJ4 HJc5 ltac:(lia) ltac:(lia)
    ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))). }
split; [exact (aregs_preserved_trans _ _ _ HPT HP5)|].
split; [|exact GL5].
rewrite Hbl5, Hbl4, <- Hbl1, <- Hbl2. exact Hperm3.
Qed.
End W.
