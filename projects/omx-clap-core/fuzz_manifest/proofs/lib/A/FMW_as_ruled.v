(* as_ruled 0x81880 (fuzz_manifest.c:244-251), 21 instructions: s2 := lv2_locate_manifest_names (text, uri);
   a0 := expected (text, uri); abort when s2 <> a0. With no reader allocation set to fail (quiet), names_spec answers
   ManifestModel.names, as expected_spec does, so the abort is dead. *)
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

Definition ar_tbl : ctable := Eval vm_compute in build_table tfibsegs A_as_ruled 21 TEmpty.
Lemma ar_tbl_ok : table_ok tfibsegs ar_tbl.
Proof.
assert (E : ar_tbl = build_table tfibsegs A_as_ruled 21 TEmpty) by (vm_cast_no_check (eq_refl ar_tbl)).
rewrite E. apply build_table_ok0. unfold A_as_ruled. lia.
Qed.
Definition ar_expect (r : bv 5) : sv :=
  match bv_unsigned r with 2 => SOff 2 32 | 8 => SOff 33 0 | 9 => SOff 34 0 | 18 => SOff 35 0
  | z => SOff (Z.to_nat z) 0 end.
(* the saved word at off from the entry sp, read off the call-site region *)
Ltac ar_slot HR0 Usp off n v :=
  apply (fmw_field _ _ 2 _ _ _ _ _ _ off 8%N (SOff n 0) v HR0 Usp ltac:(cbn; tauto)); [| apply u64_range | cbn; lia].

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable CTXn : list (list Z).
Hypothesis NAMES : names_spec tfibsegs B CTXn.
Hypothesis HCTX : In [0x818a0] CTXn.
Hypothesis EXP : expected_spec tfibsegs B.
Hypothesis IMG : fm_img_facts tfibsegs B.

Theorem as_ruled_holds : forall CTX, as_ruled_spec tfibsegs B CTX.
Proof.
intros CTX ly S W regs mem md ch t u tb ub live peak cnt fail HPRE _ H10 H11 Ht Hu Hkt Hku Hlu Hlt HG HQ HL Hev Hlv.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
destruct HPRE as [HAP HRO].
pose proof (fmw_sp B _ ly S W regs mem md ch HAP) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof HQ as (Hfail & Hc0 & Hc1).
pose proof Hu as (_ & Hu4 & Hucl & _).
assert (FS : STK_as_ruled = ltac:(let v := eval vm_compute in STK_as_ruled in exact v)) by reflexivity.
assert (FN : STK_names = ltac:(let v := eval vm_compute in STK_names in exact v)) by reflexivity.
assert (FE : STK_expected = ltac:(let v := eval vm_compute in STK_expected in exact v)) by reflexivity.
pose proof (fmw_entry B STK_as_ruled 32 ly S W regs mem md ch A_as_ruled HAP ltac:(lia) ltac:(vm_compute; reflexivity)) as HS.
pose proof (ajournal_init tfibsegs B STK_as_ruled FM_PSTAT_FP ly S W regs mem md ch HAP) as HJ.
set (E := Ereg regs []) in HS.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl); reflexivity).
unfold cfg_at. change (w64 A_as_ruled) with (Z_to_bv 64 A_as_ruled).
aj_run_to ar_tbl_ok HS HJ A_names.
{ awr_ok_tac. exact Usp. }
(* ---- the call of lv2_locate_manifest_names at 0x8189c ---- *)
assert (SB1 : same_below mem (ms_mem ms) alloc_ceiling).
{ change (frame_of E [fstk 32] mem (ms_mem ms)) in HF.
  apply (same_below_frame1 E (fstk 32) mem (ms_mem ms) alloc_ceiling HF); [|lia].
  cbn [fstk YP09.r_base YP09.r_wlo base_val]. rewrite Usp. lia. }
pose proof (fmw_reg_lit _ E _ ms 1%bv 0x818a0 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as R1.
pose proof (fmw_reg_off _ E _ ms 2%bv 2 (-32) (spZ regs) HS ltac:(vm_compute; reflexivity) Usp ltac:(lia)) as R2.
pose proof (fmw_reg_atom _ regs [] _ ms 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl) as R3.
pose proof (fmw_reg_atom _ regs [] _ ms 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl) as R4.
pose proof (fmw_reg_atom _ regs [] _ ms 8%bv 11%bv 11 HS ltac:(vm_compute; reflexivity) eq_refl) as R8.
pose proof (fmw_reg_atom _ regs [] _ ms 9%bv 10%bv 10 HS ltac:(vm_compute; reflexivity) eq_refl) as R9.
pose proof (fmw_reg_atom _ regs [] _ ms 10%bv 10%bv 10 HS ltac:(vm_compute; reflexivity) eq_refl) as R10.
pose proof (fmw_reg_atom _ regs [] _ ms 11%bv 11%bv 11 HS ltac:(vm_compute; reflexivity) eq_refl) as R11.
assert (Hspc : spZ (ms_regs ms) = spZ regs - 32) by (unfold spZ at 1; rewrite R2; lia).
assert (Us0 : bv_unsigned (w64 u) = u) by (unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (HROc : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W) (ms_mem ms)))
  by exact (arodata_below B W mem (ms_mem ms) SB1 HRO).
assert (HPREc : fpre tfibsegs B STK_names ly S W (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md) []).
{ split; [|exact HROc].
  apply (afn_pre_at tfibsegs B STK_as_ruled (spZ regs) FM_PSTAT_FP ly S W mem md [] ly S W (ms_mem ms) _ 0
    (ms_regs ms) STK_names (-32) [] HJ); try lia.
  - rewrite R1. apply ret_ok_even. rewrite unsigned_lit_small by lia. reflexivity.
  - unfold raZ. rewrite R1, unsigned_lit_small by lia. lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - apply achain_low. unfold s0Z. rewrite R8, H11, Us0. lia. }
assert (HRAc : raZ (ms_regs ms) = 0x818a0) by (unfold raZ; rewrite R1, unsigned_lit_small by lia; reflexivity).
pose proof (fm_glob_below W mem (ms_mem ms) live peak cnt fail SB1 HG) as HGc.
pose proof (cstr_ok_below W mem (ms_mem ms) t tb SB1 Ht) as Htc.
pose proof (cstr_ok_below W mem (ms_mem ms) u ub SB1 Hu) as Huc.
pose proof (fmw_region_nth E _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
assert (V1 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (spZ regs + -8) (N.to_nat 8) (bv_unsigned (getr regs 1))).
{ ar_slot HR0 Usp (-8) 1%nat (bv_unsigned (getr regs 1)). rewrite fmw_SOff0; subst E; rewrite (ew_Ereg_nat regs [] 1 1%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned. }
assert (V8 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (spZ regs + -16) (N.to_nat 8) (bv_unsigned (getr regs 8))).
{ ar_slot HR0 Usp (-16) 8%nat (bv_unsigned (getr regs 8)). rewrite fmw_SOff0; subst E; rewrite (ew_Ereg_nat regs [] 8 8%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned. }
assert (V9 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (spZ regs + -24) (N.to_nat 8) (bv_unsigned (getr regs 9))).
{ ar_slot HR0 Usp (-24) 9%nat (bv_unsigned (getr regs 9)). rewrite fmw_SOff0; subst E; rewrite (ew_Ereg_nat regs [] 9 9%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned. }
assert (V18 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (spZ regs + -32) (N.to_nat 8) (bv_unsigned (getr regs 18))).
{ ar_slot HR0 Usp (-32) 18%nat (bv_unsigned (getr regs 18)). rewrite fmw_SOff0; subst E; rewrite (ew_Ereg_nat regs [] 18 18%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned. }
clear HR0.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms HS eq_refl). cbn [ss_pc].
eapply SRr_bind;
  [exact (NAMES ly S W (ms_regs ms) (ms_mem ms) _ [] t u tb ub live peak cnt fail HPREc
     ltac:(rewrite HRAc; exact HCTX) ltac:(rewrite R10; exact H10) ltac:(rewrite R11; exact H11) Htc Huc Hkt Hku Hlu Hlt
     HGc HL ltac:(lia) Hev Hlv) |].
intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJc & HP2 & (res & H10c & Hperm2 & HNR)).
destruct (names_res_quiet W2 mem2 tb ub live peak cnt fail res HNR HQ) as [Hres HG2].
(* ---- back at 0x818a0 ---- *)
set (extra := [getr regs 1; getr regs 8; getr regs 9; getr regs 18]).
set (cs := [YP09.mkChunk 24 (CVal 8 (SOff 32 0)); YP09.mkChunk 16 (CVal 8 (SOff 33 0));
            YP09.mkChunk 8 (CVal 8 (SOff 34 0)); YP09.mkChunk 0 (CVal 8 (SOff 35 0))]).
assert (CHK : Forall (YP09.chunk_ok tfibsegs (Ereg regs2 extra) (mrestrict (w_H W) (ms_mem ms)) (spZ regs - 32)) cs).
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
destruct (fmw_after_call B STK_as_ruled (spZ regs) FM_PSTAT_FP ly S W mem md ly S W (ms_mem ms) _ 0 STK_names FM_PSTAT_FP 32
  (ms_regs ms) ly2 S2 W2 regs2 mem2 md2 EV_names extra cs 0x818a0 HJ HJc ltac:(intros a Ha; exact Ha)
  HP2 Hspc ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(reflexivity) ltac:(vm_compute; reflexivity) ltac:(repeat constructor; cbn; lia) CHK) as [HJ2 HS2].
rename HS into HSc. clear HJ HF HFr CHK.
rewrite R1.
assert (E2 : bv_unsigned (ew (Ereg regs2 extra) 2) = spZ regs + -32).
{ rewrite (ew_Ereg_nat regs2 extra 2 2%bv eq_refl), (fmw_pres _ _ 2%bv HP2 ltac:(fmw_cs_side)). lia. }
(* what the caller keeps across lv2_locate_manifest_names *)
assert (Hinc : forall x, In x (ablocks B ly S) -> In x (ablocks B ly2 S2))
  by (intros x Hx; exact (Permutation_in x (Permutation_sym Hperm2) Hx)).
pose proof (arodata_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc pstat_closed pstat_not_roP HROc) as HRO2.
pose proof (cstr_ok_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t tb IMG HJc Hinc pstat_img HRO2 Hkt Htc) as Ht2.
pose proof (cstr_ok_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ u ub IMG HJc Hinc pstat_img HRO2 Hku Huc) as Hu2.
pose proof (cstr_kept_kept B ly S ly2 S2 t tb Hinc Hkt) as Hkt2.
pose proof (cstr_kept_kept B ly S ly2 S2 u ub Hinc Hku) as Hku2.
aj_run_to ar_tbl_ok HS2 HJ2 A_expected.
{ fmw_awr_ret E2 32. }
(* ---- the call of expected at 0x818ac ---- *)
assert (SB2 : same_below mem2 (ms_mem ms0) alloc_ceiling).
{ change (frame_of (Ereg regs2 extra) [fstk_ret 32 cs] mem2 (ms_mem ms0)) in HF.
  apply (same_below_frame1 _ (fstk_ret 32 cs) mem2 (ms_mem ms0) alloc_ceiling HF); [|lia].
  cbn [fstk_ret YP09.r_base YP09.r_wlo base_val]. rewrite E2. lia. }
pose proof (fmw_reg_lit _ _ _ ms0 1%bv 0x818b0 HS2 ltac:(vm_compute; reflexivity) ltac:(lia)) as R1'.
pose proof (fmw_reg_off _ _ _ ms0 2%bv 2 0 (spZ regs + -32) HS2 ltac:(vm_compute; reflexivity) E2 ltac:(lia)) as R2'.
pose proof (fmw_reg_atom _ regs2 extra _ ms0 3%bv 3%bv 3 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R3'.
pose proof (fmw_reg_atom _ regs2 extra _ ms0 4%bv 4%bv 4 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R4'.
pose proof (fmw_reg_atom _ regs2 extra _ ms0 8%bv 8%bv 8 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R8'.
pose proof (fmw_reg_atom _ regs2 extra _ ms0 10%bv 9%bv 9 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R10'.
pose proof (fmw_reg_atom _ regs2 extra _ ms0 11%bv 8%bv 8 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R11'.
pose proof (fmw_reg_atom _ regs2 extra _ ms0 18%bv 10%bv 10 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R18'.
assert (K8 : getr regs2 8 = w64 u) by (rewrite (fmw_pres _ _ 8%bv HP2 ltac:(fmw_cs_side)), R8; exact H11).
assert (K9 : getr regs2 9 = w64 t) by (rewrite (fmw_pres _ _ 9%bv HP2 ltac:(fmw_cs_side)), R9; exact H10).
assert (Hspe : spZ (ms_regs ms0) = spZ regs - 32) by (unfold spZ at 1; rewrite R2'; lia).
assert (HPREe : fpre tfibsegs B STK_expected ly2 S2 W2 (ms_regs ms0) (ms_mem ms0)
  (with_vm_backing (m_vm_lazy md2) mat0 md2) []).
{ split; [|exact (arodata_below B W2 mem2 (ms_mem ms0) SB2 HRO2)].
  apply (afn_pre_at tfibsegs B STK_as_ruled (spZ regs) FM_PSTAT_FP ly S W mem md [] _ _ _ _ _ _
    (ms_regs ms0) STK_expected (-32) [] HJ2); try lia.
  - rewrite R1'. apply ret_ok_even. rewrite unsigned_lit_small by lia. reflexivity.
  - unfold raZ. rewrite R1', unsigned_lit_small by lia. lia.
  - rewrite R3', (fmw_pres _ _ 3%bv HP2 ltac:(fmw_cs_side)), R3. exact Hgp.
  - rewrite R4', (fmw_pres _ _ 4%bv HP2 ltac:(fmw_cs_side)), R4. exact Htp.
  - apply achain_low. unfold s0Z. rewrite R8', K8, Us0. lia. }
rewrite (st_ok_restrict_mkst tfibsegs (w_H W2) (Ereg regs2 extra) _ ms0 HS2 eq_refl). cbn [ss_pc].
eapply SRr_bind;
  [exact (EXP ly2 S2 W2 (ms_regs ms0) (ms_mem ms0) _ [] t u tb ub live _ _ _ HPREe
     (fm_glob_below W2 mem2 (ms_mem ms0) _ _ _ _ SB2 HG2)
     ltac:(rewrite R10'; exact K9) ltac:(rewrite R11'; exact K8)
     (cstr_ok_below W2 mem2 (ms_mem ms0) t tb SB2 Ht2) (cstr_ok_below W2 mem2 (ms_mem ms0) u ub SB2 Hu2)
     Hkt2 Hku2 Hlu Hlt) |].
intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJe & HP3 & H10e & Hbl3 & HG3).
(* ---- back at 0x818b0 ---- *)
assert (CHK2 : Forall (YP09.chunk_ok tfibsegs (Ereg regs3 extra) (mrestrict (w_H W2) (ms_mem ms0)) (spZ regs - 32)) cs).
{ pose proof (fmw_region_nth _ _ _ 0 _ HS2 eq_refl) as HR2. cbn [ms_mem restrict] in HR2.
  destruct HR2 as (_ & _ & _ & Hcs2). cbn [YP09.r_base YP09.r_chunks base_val] in Hcs2. rewrite E2 in Hcs2.
  apply (fmw_chunks_extra regs2 regs3 extra); [|exact Hcs2].
  repeat (apply Forall_cons; [do 2 eexists; reflexivity|]). apply Forall_nil. }
destruct (fmw_after_call B STK_as_ruled (spZ regs) FM_PSTAT_FP ly S W mem md ly2 S2 W2 (ms_mem ms0) _ _ STK_expected [] 32
  (ms_regs ms0) ly3 S3 W3 regs3 mem3 md3 0 extra cs 0x818b0 HJ2 HJe ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))
  HP3 Hspe ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(reflexivity) ltac:(vm_compute; reflexivity) ltac:(repeat constructor; cbn; lia) CHK2) as [HJ3 HS3].
rename HS2 into HSe. clear HJ2 HF HFr CHK2.
rewrite R1'.
assert (E3 : bv_unsigned (ew (Ereg regs3 extra) 2) = spZ regs + -32).
{ rewrite (ew_Ereg_nat regs3 extra 2 2%bv eq_refl), (fmw_pres _ _ 2%bv HP3 ltac:(fmw_cs_side)). unfold spZ in Hspe. lia. }
aj_run ar_tbl_ok HS3 HJ3.
{ fmw_awr_ret E3 32. }
(* 0x818b0: bne s2, a0: both are the rule's answer *)
assert (Hn : 0 <= ManifestModel.names tb ub < 2 ^ 64) by (destruct (names_01 tb ub) as [-> | ->]; lia).
assert (E18 : ew (Ereg regs3 extra) 18 = Z_to_bv 64 (ManifestModel.names tb ub)).
{ rewrite (ew_Ereg_nat regs3 extra 18 18%bv eq_refl), (fmw_pres _ _ 18%bv HP3 ltac:(fmw_cs_side)), R18', H10c, Hres.
  reflexivity. }
assert (E10 : ew (Ereg regs3 extra) 10 = Z_to_bv 64 (ManifestModel.names tb ub))
  by (rewrite (ew_Ereg_nat regs3 extra 10 10%bv eq_refl); exact H10e).
eapply SRr_sym_branch with (c := BC_NE) (a := SOff 18 0) (b := SOff 10 0); [exact HS3 | |].
- intros Hb _. exfalso. rewrite branch_ne_U in Hb.
  rewrite (U_atom _ 18 _ E18 Hn), (U_atom _ 10 _ E10 Hn), Z.eqb_refl in Hb. discriminate Hb.
- intros _ HS4. clear HS3.
  aj_run ar_tbl_ok HS4 HJ3.
  { fmw_awr_ret E3 32. }
  fmw_ret2 ar_tbl_ok ar_expect HS4 HJ3 HSc HP2 HSe HP3 E3 Hra LAWS HSL.
  split; [rewrite Hbl3; exact Hperm2|]. fmw_sb E3.
  apply (fm_glob_below W3 mem3); [eassumption | exact HG3].
Qed.
End W.
