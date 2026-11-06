(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMW_check_reject_clean.v, made by a Theorem Labs lane's twin.py: check_reject_clean is instruction-identical on B (0x80e14 -> 0x80f68, offset 0x154; branch / call targets masked), so the walk carries over; imports by B4b's rule. Mapped pcs: 0x80e14->0x80f68, 0x80e24->0x80f78, 0x80e28->0x80f7c, 0x80e28->0x80f7c, 0x80e28->0x80f7c. *)
(* check_reject_clean 0x80f68 (fuzz_manifest.c:217-223), 12 instructions: s0 := live_before; fuzz_alloc_live();
   `bne a0, s0, abort`. Under fuzz_alloc_live_spec the call returns g_live = live_before, so the abort is dead. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI16 YK06 YM05 YG0q YC20.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_K.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition crc_tbl : ctable := Eval vm_compute in build_table tfibsegs A_check_reject_clean 12 TEmpty.
Lemma crc_tbl_ok : table_ok tfibsegs crc_tbl.
Proof.
assert (E : crc_tbl = build_table tfibsegs A_check_reject_clean 12 TEmpty) by (vm_cast_no_check (eq_refl crc_tbl)).
rewrite E. apply build_table_ok0. unfold A_check_reject_clean. lia.
Qed.
(* the callee-saved registers at the return: sp back up by the frame, s0 reloaded, the rest untouched *)
Definition crc_expect (r : bv 5) : sv :=
  match bv_unsigned r with 2 => SOff 2 16 | 8 => SOff 33 0 | z => SOff (Z.to_nat z) 0 end.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis LIVE : fuzz_alloc_live_spec tfibsegs B.

Theorem check_reject_clean_holds : check_reject_clean_spec tfibsegs B.
Proof.
intros ly S W regs mem md ch live peak cnt fail HPRE HG H10.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
destruct HPRE as [HAP HRO].
pose proof (fmw_sp B _ ly S W regs mem md ch HAP) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof HG as (_ & _ & _ & _ & Rl & Rp & Rc & Rf).
assert (FS : STK_check_reject_clean = 32) by reflexivity. assert (FA : STK_fuzz_alloc = 16) by reflexivity.
pose proof (fmw_entry B STK_check_reject_clean 16 ly S W regs mem md ch A_check_reject_clean HAP
  ltac:(lia) ltac:(vm_compute; reflexivity)) as HS.
pose proof (ajournal_init tfibsegs B STK_check_reject_clean [] ly S W regs mem md ch HAP) as HJ.
set (E := Ereg regs []) in HS.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl); reflexivity).
unfold cfg_at. change (w64 A_check_reject_clean) with (Z_to_bv 64 A_check_reject_clean).
aj_run_to crc_tbl_ok HS HJ A_fuzz_alloc_live.
{ awr_ok_tac. exact Usp. }
(* ---- the call of fuzz_alloc_live at 0x80f78 ---- *)
assert (SB1 : same_below mem (ms_mem ms) alloc_ceiling).
{ change (frame_of E [fstk 16] mem (ms_mem ms)) in HF.
  apply (same_below_frame1 E (fstk 16) mem (ms_mem ms) alloc_ceiling HF); [|lia].
  cbn [fstk YP09.r_base YP09.r_wlo base_val]. rewrite Usp. lia. }
pose proof (fmw_reg_lit _ E _ ms 1%bv 0x80f7c HS ltac:(vm_compute; reflexivity) ltac:(lia)) as R1.
pose proof (fmw_reg_off _ E _ ms 2%bv 2 (-16) (spZ regs) HS ltac:(vm_compute; reflexivity) Usp ltac:(lia)) as R2.
pose proof (fmw_reg_atom _ regs [] _ ms 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl) as R3.
pose proof (fmw_reg_atom _ regs [] _ ms 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl) as R4.
pose proof (fmw_reg_atom _ regs [] _ ms 8%bv 10%bv 10 HS ltac:(vm_compute; reflexivity) eq_refl) as R8.
assert (Hspc : spZ (ms_regs ms) = spZ regs - 16) by (unfold spZ at 1; rewrite R2; lia).
assert (HPREc : fpre tfibsegs B STK_fuzz_alloc ly S W (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md) []).
{ split.
  - apply (afn_pre_at tfibsegs B STK_check_reject_clean (spZ regs) [] ly S W mem md [] ly S W (ms_mem ms) _ 0
      (ms_regs ms) STK_fuzz_alloc (-16) [] HJ); try lia.
    + rewrite R1. apply ret_ok_even. rewrite unsigned_lit_small by lia. reflexivity.
    + unfold raZ. rewrite R1, unsigned_lit_small by lia. lia.
    + rewrite R3. exact Hgp.
    + rewrite R4. exact Htp.
    + apply achain_low. unfold s0Z. rewrite R8, H10. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - exact (arodata_below B W mem (ms_mem ms) SB1 HRO). }
pose proof (fm_glob_below W mem (ms_mem ms) live peak cnt fail SB1 HG) as HGc.
pose proof (fmw_region_nth E _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
pose proof (fmw_field E _ 2 (spZ regs) _ _ _ _ _ (-8) 8%N (SOff 1 0) (raZ regs) HR0 Usp ltac:(cbn; tauto)
  ltac:(rewrite fmw_SOff0; subst E; rewrite (ew_Ereg_nat regs [] 1 1%bv eq_refl); unfold raZ; symmetry; apply Z_to_bv_bv_unsigned)
  ltac:(unfold raZ; apply u64_range) ltac:(cbn; lia)) as Vra.
pose proof (fmw_field E _ 2 (spZ regs) _ _ _ _ _ (-16) 8%N (SOff 8 0) (s0Z regs) HR0 Usp ltac:(cbn; tauto)
  ltac:(rewrite fmw_SOff0; subst E; rewrite (ew_Ereg_nat regs [] 8 8%bv eq_refl); unfold s0Z; symmetry; apply Z_to_bv_bv_unsigned)
  ltac:(unfold s0Z; apply u64_range) ltac:(cbn; lia)) as Vs0.
clear HR0.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms HS eq_refl). cbn [ss_pc].
eapply SRr_bind; [exact (LIVE ly S W (ms_regs ms) (ms_mem ms) _ [] live peak cnt fail HPREc HGc) |].
intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJc & HP2 & H10c & Hbl2 & HG2).
(* ---- back at 0x80f7c ---- *)
set (extra := [getr regs 1; getr regs 8]).
set (cs := [YP09.mkChunk 8 (CVal 8 (SOff 32 0)); YP09.mkChunk 0 (CVal 8 (SOff 33 0))]).
assert (CHK : Forall (YP09.chunk_ok tfibsegs (Ereg regs2 extra) (mrestrict (w_H W) (ms_mem ms)) (spZ regs - 16)) cs).
{ constructor; [|constructor; [|constructor]].
  - apply (chunk_ok_val tfibsegs _ _ _ 8 8%N (SOff 32 0) (raZ regs)).
    + rewrite fmw_SOff0. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. cbn [nth extra].
      unfold raZ. symmetry. apply Z_to_bv_bv_unsigned.
    + unfold raZ. apply u64_range.
    + cbn; lia.
    + replace (spZ regs - 16 + 8) with (spZ regs + -8) by lia. exact Vra.
  - apply (chunk_ok_val tfibsegs _ _ _ 0 8%N (SOff 33 0) (s0Z regs)).
    + rewrite fmw_SOff0. change 33%nat with (32 + 1)%nat. rewrite ew_Ereg_extra. cbn [nth extra].
      unfold s0Z. symmetry. apply Z_to_bv_bv_unsigned.
    + unfold s0Z. apply u64_range.
    + cbn; lia.
    + replace (spZ regs - 16 + 0) with (spZ regs + -16) by lia. exact Vs0. }
destruct (fmw_after_call B STK_check_reject_clean (spZ regs) [] ly S W mem md ly S W (ms_mem ms) _ 0 STK_fuzz_alloc [] 16
  (ms_regs ms) ly2 S2 W2 regs2 mem2 md2 0 extra cs 0x80f7c HJ HJc ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))
  HP2 Hspc ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(reflexivity) ltac:(vm_compute; reflexivity) ltac:(repeat constructor; cbn; lia) CHK) as [HJ2 HS2].
rename HS into HSc. clear HJ HF HFr CHK.
rewrite R1.
assert (E2 : bv_unsigned (ew (Ereg regs2 extra) 2) = spZ regs + -16).
{ rewrite (ew_Ereg_nat regs2 extra 2 2%bv eq_refl). rewrite (fmw_pres _ _ 2%bv HP2 ltac:(unfold acallee_saved; vm_compute; lia)). lia. }
aj_run crc_tbl_ok HS2 HJ2.
{ unfold fss_ret; cbn [ss_mem].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -16); [reflexivity | exact E2 | cbn; lia | cbn; lia | apply awr_ok_nil]. }
assert (E10' : ew (Ereg regs2 extra) 10 = Z_to_bv 64 live) by (rewrite (ew_Ereg_nat regs2 extra 10 10%bv eq_refl); exact H10c).
assert (E8' : ew (Ereg regs2 extra) 8 = Z_to_bv 64 live).
{ rewrite (ew_Ereg_nat regs2 extra 8 8%bv eq_refl), (fmw_pres _ _ 8%bv HP2 ltac:(unfold acallee_saved; vm_compute; lia)).
  rewrite R8. exact H10. }
eapply SRr_sym_branch with (c := BC_NE) (a := SOff 10 0) (b := SOff 8 0); [exact HS2 | |].
- intros Hb _. exfalso. rewrite branch_ne_U in Hb.
  rewrite (U_atom _ 10 live E10' ltac:(lia)), (U_atom _ 8 live E8' ltac:(lia)), Z.eqb_refl in Hb. discriminate Hb.
- intros _ HS3. clear HS2.
  aj_run crc_tbl_ok HS3 HJ2.
  { cbn [add_cond ss_mem].
    eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -16); [reflexivity | exact E2 | cbn; lia | cbn; lia | apply awr_ok_nil]. }
  rewrite ?wvb_collapse in HJ2.
  assert (SB2 : same_below mem2 (ms_mem ms0) alloc_ceiling).
  { change (frame_of (Ereg regs2 extra) [fstk_ret 16 cs] mem2 (ms_mem ms0)) in HF.
    apply (same_below_frame1 _ (fstk_ret 16 cs) mem2 (ms_mem ms0) alloc_ceiling HF); [|lia].
    cbn [fstk_ret YP09.r_base YP09.r_wlo base_val]. rewrite E2. lia. }
  assert (SB3 : same_below (ms_mem ms0) (ms_mem ms1) alloc_ceiling).
  { cbn [add_cond ss_mem] in HF0.
    eapply (same_below_frame1 _ _ (ms_mem ms0) (ms_mem ms1) alloc_ceiling HF0); [|lia].
    cbn [YP09.r_base YP09.r_wlo base_val]. rewrite E2. lia. }
  pose proof (fmw_reg_extra _ regs2 extra _ ms1 1%bv 0 HS3 ltac:(vm_compute; reflexivity)) as R1F.
  cbn [nth extra] in R1F.
  eapply (SRr_ret_at tfibsegs crc_tbl crc_tbl_ok fm_wx); [exact HS3 | reflexivity | vm_compute; reflexivity |].
  intros mat2.
  assert (Hpc : v_jalr (getr (ms_regs ms1) 1) 0 = getr regs 1) by (rewrite R1F; exact Hra).
  rewrite Hpc. unfold fpost, apost_base.
  exists ly2, S2, (ms_regs ms1), (ms_mem ms1), (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md2) mat1 md2)) mat2
    (with_vm_backing (m_vm_lazy md2) mat1 md2)).
  split; [reflexivity|].
  split; [apply (ajournal_materialize tfibsegs B LAWS HSL); exact HJ2|].
  split.
  { apply (fmw_preserved _ _ _ ms1 regs crc_expect HS3); [vm_compute; reflexivity|].
    fmw_cs_cases crc_expect HSc HP2 E2. }
  split; [exact Hbl2|].
  apply (fm_glob_below W2 mem2); [exact (same_below_trans _ _ _ _ SB2 SB3) | exact HG2].
Qed.
End W.

