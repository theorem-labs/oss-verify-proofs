(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMW_check_bounded_alloc.v, made by a Theorem Labs lane's twin.py: check_bounded_alloc is instruction-identical on B (0x80db4 -> 0x80f04, offset 0x150; branch / call targets masked), so the walk carries over; imports by B4b's rule. Mapped pcs: 0x80db4->0x80f04. *)
(* check_bounded_alloc 0x80f04 (fuzz_manifest.c:191-197), 9 instructions: `addi a1, a1, 3; bltu a1, a0, abort`. Under
   held <= ul + 3 the abort branch is dead; the function returns with nothing changed but its stack window. *)
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

Definition cba_tbl : ctable := Eval vm_compute in build_table tfibsegs A_check_bounded_alloc 9 TEmpty.
Lemma cba_tbl_ok : table_ok tfibsegs cba_tbl.
Proof.
assert (E : cba_tbl = build_table tfibsegs A_check_bounded_alloc 9 TEmpty) by (vm_cast_no_check (eq_refl cba_tbl)).
rewrite E. apply build_table_ok0. unfold A_check_bounded_alloc. lia.
Qed.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

Theorem check_bounded_alloc_holds : check_bounded_alloc_spec tfibsegs B.
Proof.
intros ly S W regs mem md ch held ul live peak cnt fail HPRE HG H10 H11 Hheld Hul.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
destruct HPRE as [HAP _].
pose proof (fmw_sp B _ ly S W regs mem md ch HAP) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (fmw_entry B STK_check_bounded_alloc 16 ly S W regs mem md ch A_check_bounded_alloc HAP
  ltac:(unfold STK_check_bounded_alloc; lia) ltac:(vm_compute; reflexivity)) as HS.
pose proof (ajournal_init tfibsegs B STK_check_bounded_alloc [] ly S W regs mem md ch HAP) as HJ.
set (E := Ereg regs []) in HS.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl); reflexivity).
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs [] 1 1%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 held) by (subst E; rewrite (ew_Ereg_nat regs [] 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 ul) by (subst E; rewrite (ew_Ereg_nat regs [] 11 11%bv eq_refl); exact H11).
unfold cfg_at. change (w64 A_check_bounded_alloc) with (Z_to_bv 64 A_check_bounded_alloc).
aj_run cba_tbl_ok HS HJ.
{ awr_ok_tac. exact Usp. }
eapply SRr_sym_branch with (c := BC_LTU) (a := SOff 11 3) (b := SOff 10 0); [exact HS | |].
- intros Hb _. exfalso. rewrite branch_ltu_U in Hb.
  rewrite (U_atom_off E 11 ul 3 E11 ltac:(lia) ltac:(lia)), (U_atom E 10 held E10 ltac:(lia)) in Hb.
  apply Z.ltb_lt in Hb. lia.
- intros _ HS2. clear HS.
  aj_run cba_tbl_ok HS2 HJ.
  { awr_ok_tac. exact Usp. }
  rewrite ?wvb_collapse in HJ.
  assert (SB1 : same_below mem (ms_mem ms) alloc_ceiling).
  { change (frame_of E [fstk 16] mem (ms_mem ms)) in HF.
    apply (same_below_frame1 E (fstk 16) mem (ms_mem ms) alloc_ceiling HF); [|lia].
    cbn [fstk YP09.r_base YP09.r_wlo base_val]. rewrite Usp. unfold STK_check_bounded_alloc in *. lia. }
  assert (SB2 : same_below (ms_mem ms) (ms_mem ms0) alloc_ceiling).
  { cbn [add_cond ss_mem] in HF0.
    eapply (same_below_frame1 E _ (ms_mem ms) (ms_mem ms0) alloc_ceiling HF0); [|lia].
    cbn [YP09.r_base YP09.r_wlo base_val]. rewrite Usp. unfold STK_check_bounded_alloc in *. lia. }
  rreg HS2 (1%bv : bv 5) R1.
  eapply (SRr_ret_at tfibsegs cba_tbl cba_tbl_ok fm_wx); [exact HS2 | reflexivity | vm_compute; reflexivity |].
  intros mat2.
  assert (Hpc : v_jalr (getr (ms_regs ms0) 1) 0 = getr regs 1).
  { rewrite R1; rewrite ?fmw_SOff0, ?E1; first [exact Hra | subst E; rewrite (ew_Ereg_nat regs [] 1 1%bv eq_refl); exact Hra]. }
  rewrite Hpc. unfold fpost, apost_base.
  exists ly, S, (ms_regs ms0), (ms_mem ms0), (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md) mat0 md)) mat2
    (with_vm_backing (m_vm_lazy md) mat0 md)).
  split; [reflexivity|].
  split; [apply (ajournal_materialize tfibsegs B LAWS HSL); exact HJ|].
  split; [eapply (aregs_preserved_of_st_ok tfibsegs _ E _ _ regs [] HS2); [apply env_agree_refl | vm_compute; reflexivity]|].
  split; [reflexivity|].
  apply (fm_glob_below W mem); [exact (same_below_trans _ _ _ _ SB1 SB2) | exact HG].
Qed.
End W.

