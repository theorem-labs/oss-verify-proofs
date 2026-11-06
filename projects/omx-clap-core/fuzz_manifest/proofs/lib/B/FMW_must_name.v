(* must_name 0x81a9c (fm.asan-ubsan only, pin ca61e5c9eabc0050), 11 instructions. Image A has no such function: its
   check_round_trip inlines the same check four times (A 0x80f4c, 0x81000, 0x8102c, 0x81058). On image B the check is
   outlined, and check_round_trip calls it at four sites (return addresses 0x810a0, 0x81150, 0x81178, 0x811a0 =
   CTX_must_name of lib/ReusableB/YCej.v). It is part of G6 (check_round_trip), its only caller.

     0x81a9c  addi sp,sp,-16
     0x81aa0  sd   ra,8(sp)
     0x81aa4  jal  lv2_locate_manifest_names 0x81e74      (return address 0x81aa8, in CTX_lv2_locate_manifest_names)
     0x81aa8  li   a1,1
     0x81aac  bne  a0,a1,0x81abc
     0x81ab0  ld   ra,8(sp)
     0x81ab4  addi sp,sp,16
     0x81ab8  ret
     0x81abc  jal  0x59bdc                                 (the abort path: before_abort, then abort 0x88db0)
     0x81ac0  jal  0x88db0
     0x81ac4  unimp

   The contract: names_spec's premises, plus the facts that make names answer 1 (a non-empty uri, no reader
   allocation set to fail, and the rule's answer ManifestModel.names tb ub = 1). Then the abort path is not taken and
   must_name returns a0 = 1 with names_spec's effect on the statics (names_res ... 1). Its window is its own frame
   (16) above names' window. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YC20.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YCbq YC5d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YCej.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Definition A_must_name : Z := 0x81a9c.
Definition MN_FRAME : Z := 16.
Definition STK_must_name : Z := MN_FRAME + STK_names.

(* the window check_round_trip's budget gives a must_name call: as_ruled's window already covers it *)
Lemma STK_must_name_le_as_ruled : STK_must_name <= STK_as_ruled.
Proof.
unfold STK_must_name, MN_FRAME, STK_as_ruled. lia.
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

Definition must_name_spec (CTX : list (list Z)) : Prop :=
  forall ly S W regs mem md ch t u (tb ub : list Z) live peak cnt fail,
  fpre tfibsegs B STK_must_name ly S W regs mem md ch -> In (raZ regs :: spine ch) CTX ->
  getr regs 10 = w64 t -> getr regs 11 = w64 u ->
  cstr_ok tfibsegs W mem t tb -> cstr_ok tfibsegs W mem u ub -> cstr_kept B ly S t tb -> cstr_kept B ly S u ub ->
  (length ub <= 255)%nat -> Z.of_nat (length tb) <= MANIFEST_MAX ->
  fm_glob tfibsegs W mem live peak cnt fail -> live + Z.of_nat (length ub) + 3 < 2 ^ 33 -> cnt + 1 < 2 ^ 33 ->
  st_nev S + EV_names <= EV_MAX -> blocks_bytes S + LIVE_names <= LIVE_MAX ->
  ub <> [] -> cnt <> fail -> ManifestModel.names tb ub = 1 ->
  SRr tfibsegs W (cfg_at tfibsegs A_must_name regs mem md)
    (fpost tfibsegs B STK_must_name FM_PSTAT_FP regs ly S W mem md EV_names (fun ly' S' W' regs' mem' md' =>
       getr regs' 10 = w64 1 /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
       names_res tfibsegs tb ub live peak cnt fail 1 W' mem')).
End c.

(* ---- the proof: frame 16 (ra at entry sp - 8), the call of lv2_locate_manifest_names, `bne a0, 1` not taken ---- *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_K.

Definition mn_tbl : ctable := Eval vm_compute in build_table tfibsegs A_must_name 11 TEmpty.
Lemma mn_tbl_ok : table_ok tfibsegs mn_tbl.
Proof.
assert (E : mn_tbl = build_table tfibsegs A_must_name 11 TEmpty) by (vm_cast_no_check (eq_refl mn_tbl)).
rewrite E. apply build_table_ok0. unfold A_must_name. lia.
Qed.
(* the callee-saved registers at the ret: sp back up by the frame, the rest their entry atoms *)
Definition mn_expect (r : bv 5) : sv :=
  match bv_unsigned r with 2 => SOff 2 16 | z => SOff (Z.to_nat z) 0 end.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable CTXn : list (list Z).
Hypothesis NAMES : names_spec tfibsegs B CTXn.
Hypothesis HCTX : In [0x81aa8] CTXn.

(* must_name leaves s0 as its caller's, so lv2_locate_manifest_names runs on the caller's frame chain: its context is
   0x81aa8 :: spine ch. CTX_must_name holds one-element contexts only, which makes ch empty. *)
Theorem must_name_holds : must_name_spec B CTX_must_name.
Proof.
intros ly S W regs mem md ch t u tb ub live peak cnt fail HPRE HCX H10 H11 Ht Hu Hkt Hku Hlu Hlt HG HL HC Hev Hlv
  Hub Hcf Hnm.
assert (Hch0 : ch = []).
{ destruct ch as [|r ch']; [reflexivity|]. exfalso.
  unfold CTX_must_name, spine in HCX. cbn [map] in HCX.
  repeat (destruct HCX as [HCX|HCX]; [apply (f_equal (@length Z)) in HCX; cbn [length] in HCX; lia|]).
  destruct HCX. }
subst ch. clear HCX.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
destruct HPRE as [HAP HRO].
pose proof (fmw_sp B _ ly S W regs mem md [] HAP) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (_ & _ & _ & _ & _ & _ & _ & Htop & _).
assert (FS : STK_must_name = ltac:(let v := eval vm_compute in STK_must_name in exact v)) by reflexivity.
assert (FN : STK_names = ltac:(let v := eval vm_compute in STK_names in exact v)) by reflexivity.
pose proof (fmw_entry B STK_must_name 16 ly S W regs mem md [] A_must_name HAP ltac:(lia) ltac:(vm_compute; reflexivity))
  as HS.
pose proof (ajournal_init tfibsegs B STK_must_name FM_PSTAT_FP ly S W regs mem md [] HAP) as HJ.
set (E := Ereg regs []) in HS.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl); reflexivity).
unfold cfg_at. change (w64 A_must_name) with (Z_to_bv 64 A_must_name).
aj_run_to mn_tbl_ok HS HJ A_names.
{ awr_ok_tac. exact Usp. }
(* ---- the call of lv2_locate_manifest_names at 0x81aa4: sp = entry sp - 16, ra = 0x81aa8, a0/a1/s0 the entry's ---- *)
assert (SB1 : same_below mem (ms_mem ms) alloc_ceiling).
{ change (frame_of E [fstk 16] mem (ms_mem ms)) in HF.
  apply (same_below_frame1 E (fstk 16) mem (ms_mem ms) alloc_ceiling HF); [|lia].
  cbn [fstk YP09.r_base YP09.r_wlo base_val]. rewrite Usp. lia. }
pose proof (fmw_reg_lit _ E _ ms 1%bv 0x81aa8 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as R1.
pose proof (fmw_reg_off _ E _ ms 2%bv 2 (-16) (spZ regs) HS ltac:(vm_compute; reflexivity) Usp ltac:(lia)) as R2.
pose proof (fmw_reg_atom _ regs [] _ ms 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl) as R3.
pose proof (fmw_reg_atom _ regs [] _ ms 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl) as R4.
pose proof (fmw_reg_atom _ regs [] _ ms 8%bv 8%bv 8 HS ltac:(vm_compute; reflexivity) eq_refl) as R8.
pose proof (fmw_reg_atom _ regs [] _ ms 10%bv 10%bv 10 HS ltac:(vm_compute; reflexivity) eq_refl) as R10.
pose proof (fmw_reg_atom _ regs [] _ ms 11%bv 11%bv 11 HS ltac:(vm_compute; reflexivity) eq_refl) as R11.
assert (Hspc : spZ (ms_regs ms) = spZ regs - 16) by (unfold spZ at 1; rewrite R2; lia).
assert (HROc : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W) (ms_mem ms)))
  by exact (arodata_below B W mem (ms_mem ms) SB1 HRO).
(* the callee's chain: s0 is the entry's, its chain [] is kept over the run and holds at the lower sp *)
assert (HCHc : achain ly (aview tfibsegs (w_H W) (ms_mem ms)) (spZ (ms_regs ms)) (s0Z (ms_regs ms)) []).
{ replace (s0Z (ms_regs ms)) with (s0Z regs) by (unfold s0Z; rewrite R8; reflexivity).
  apply (achain_lower ly _ (spZ regs)); [|lia].
  exact (fmw_achain_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hch). }
assert (HPREc : fpre tfibsegs B STK_names ly S W (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md) []).
{ split; [|exact HROc].
  apply (afn_pre_at tfibsegs B STK_must_name (spZ regs) FM_PSTAT_FP ly S W mem md [] ly S W (ms_mem ms) _ 0
    (ms_regs ms) STK_names (-16) [] HJ); try lia.
  - rewrite R1. apply ret_ok_even. rewrite unsigned_lit_small by lia. reflexivity.
  - unfold raZ. rewrite R1, unsigned_lit_small by lia. lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - exact HCHc. }
assert (HRAc : raZ (ms_regs ms) = 0x81aa8) by (unfold raZ; rewrite R1, unsigned_lit_small by lia; reflexivity).
pose proof (fm_glob_below W mem (ms_mem ms) live peak cnt fail SB1 HG) as HGc.
pose proof (cstr_ok_below W mem (ms_mem ms) t tb SB1 Ht) as Htc.
pose proof (cstr_ok_below W mem (ms_mem ms) u ub SB1 Hu) as Huc.
pose proof (fmw_region_nth E _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
pose proof (fmw_field E _ 2 (spZ regs) _ _ _ _ _ (-8) 8%N (SOff 1 0) (raZ regs) HR0 Usp ltac:(cbn; tauto)
  ltac:(rewrite fmw_SOff0; subst E; rewrite (ew_Ereg_nat regs [] 1 1%bv eq_refl); unfold raZ; symmetry; apply Z_to_bv_bv_unsigned)
  ltac:(unfold raZ; apply u64_range) ltac:(cbn; lia)) as Vra.
clear HR0.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms HS eq_refl). cbn [ss_pc].
eapply SRr_bind;
  [exact (NAMES ly S W (ms_regs ms) (ms_mem ms) _ [] t u tb ub live peak cnt fail HPREc
     ltac:(rewrite HRAc; exact HCTX) ltac:(rewrite Hspc; lia) ltac:(rewrite R10; exact H10) ltac:(rewrite R11; exact H11)
     Htc Huc Hkt Hku Hlu Hlt HGc HL HC Hev Hlv) |].
intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJc & HP2 & (res & H10c & Hperm2 & HNR)).
(* uri non-empty and no allocation set to fail: names answers the rule, which is 1 *)
destruct HNR as [(Hu0 & _) | [(_ & Hcf0 & _) | (_ & _ & Hres & HG2)]]; [contradiction | contradiction |].
assert (Hr1 : res = 1) by lia. clear Hres. subst res.
(* ---- back at 0x81aa8 ---- *)
set (extra := [getr regs 1]).
set (cs := [YP09.mkChunk 8 (CVal 8 (SOff 32 0))]).
assert (CHK : Forall (YP09.chunk_ok tfibsegs (Ereg regs2 extra) (mrestrict (w_H W) (ms_mem ms)) (spZ regs - 16)) cs).
{ constructor; [|constructor].
  apply (chunk_ok_val tfibsegs _ _ _ 8 8%N (SOff 32 0) (raZ regs)).
  - rewrite fmw_SOff0. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. cbn [nth extra].
    unfold raZ. symmetry. apply Z_to_bv_bv_unsigned.
  - unfold raZ. apply u64_range.
  - cbn; lia.
  - replace (spZ regs - 16 + 8) with (spZ regs + -8) by lia. exact Vra. }
destruct (fmw_after_call B STK_must_name (spZ regs) FM_PSTAT_FP ly S W mem md ly S W (ms_mem ms) _ 0 STK_names FM_PSTAT_FP 16
  (ms_regs ms) ly2 S2 W2 regs2 mem2 md2 EV_names extra cs 0x81aa8 HJ HJc ltac:(intros a Ha; exact Ha)
  HP2 Hspc ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(reflexivity) ltac:(vm_compute; reflexivity) ltac:(repeat constructor; cbn; lia) CHK) as [HJ2 HS2].
rename HS into HSc. clear HJ HF HFr CHK.
rewrite R1.
assert (E2 : bv_unsigned (ew (Ereg regs2 extra) 2) = spZ regs + -16).
{ rewrite (ew_Ereg_nat regs2 extra 2 2%bv eq_refl), (fmw_pres _ _ 2%bv HP2 ltac:(fmw_cs_side)). lia. }
aj_run mn_tbl_ok HS2 HJ2.
{ fmw_awr_ret E2 16. }
(* 0x81aac: bne a0, a1 with a0 = 1 (names' answer) and a1 = 1 (li a1, 1): not taken *)
assert (E10 : ew (Ereg regs2 extra) 10 = Z_to_bv 64 1)
  by (rewrite (ew_Ereg_nat regs2 extra 10 10%bv eq_refl); exact H10c).
assert (U10 : U (Ereg regs2 extra) (SOff 10 0) = 1) by (apply U_atom; [exact E10 | lia]).
assert (U1 : U (Ereg regs2 extra) (SLit 1) = 1) by (apply U_lit; lia).
eapply SRr_sym_branch with (c := BC_NE) (a := SOff 10 0) (b := SLit 1); [exact HS2 | |].
- intros Hb _. exfalso. rewrite branch_ne_U, U10, U1 in Hb. discriminate Hb.
- intros _ HS4. clear HS2.
  aj_run mn_tbl_ok HS4 HJ2.
  { fmw_awr_ret E2 16. }
  fmw_ret mn_tbl_ok mn_expect HS4 HJ2 HSc HP2 E2 Hra LAWS HSL.
  split.
  { lazymatch type of HS4 with st_ok _ _ _ (restrict _ ?msf) =>
      rewrite (fmw_reg_atom _ regs2 extra _ msf 10%bv 10%bv 10 HS4 ltac:(vm_compute; reflexivity) eq_refl) end.
    exact H10c. }
  split; [exact Hperm2|]. fmw_sb E2.
  unfold names_res. right; right.
  split; [exact Hub|]. split; [exact Hcf|]. split; [lia|].
  apply (fm_glob_below W2 mem2); [eassumption | exact HG2].
Qed.
End W.
