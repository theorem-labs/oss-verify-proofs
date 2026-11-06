(* check_bounded_alloc, image B: fs.asan-ubsan (sha256 5ac5ce0954f8...) entry 0x81618 (lib/B/FSH_Base.v
   A_check_bounded_alloc; fs.c:157-163), 13 words over lib/B/YB1w.v's range 0x81618 .. 0x8164c (MEASURED, capstone):
   `addi sp, sp, -16; sd ra, 8(sp); srli a1, a1, 2; slli a2, a1, 1; add a1, a2, a1; addi a1, a1, 3;
   bltu a1, a0, 0x81640; ld ra, 8(sp); addi sp, sp, 16; ret`, then the abort path `jal 0x5a1ec` (__asan_handle_no_return,
   the A twin's 0x5a17c) and `jal 0x8cca8` (abort, YB1w tfib_A_abort), and the
   padding word `unimp` at 0x81648. The same code as image A's 0x81560, moved by +0xb8.
   UBSan: NO __ubsan_handle_* call in the range (every jal in it is listed above). The bound n / 4 * 3 + 3 is computed in
   size_t, and unsigned wrap is not undefined behaviour, so the build emits no check on it; the only branch out of the
   straight line is the bltu to the abort path, ruled out by the premise `held <= b64_alloc_bound n`.
   a1 at the branch 0x81630 is n / 4 * 3 + 3 (no wrap: n < 2^64); under held <= n / 4 * 3 + 3 the branch to the abort path
   is not taken, and the function returns at 0x8163c with memory changed only in its 16-byte stack window.
   The decode table is lib/B/FSW_check_bounded_alloc_tbl.v.
   Ported from: lib/A/FSH_check_bounded_alloc.v (a working branch 3694074f8f1), the same walk over lib/B's walk
   kit lib/B/FSW_K.v (same lemma names) and lib/B's image files (YB1v, YB1w, FSH_Base, FSH_Rt, FSH_Fn_checks). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v FSH_Base FSH_Rt FSH_Fn_checks FSW_K FSW_check_bounded_alloc_tbl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* a1 at the branch 0x81630, as the engine leaves it: ((n >> 2) << 1) + (n >> 2) + 3 *)
Definition cba_a1 : sv :=
  SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (SAlu ALU_SRL (SOff 11 0) (SLit 2)) (SLit 1))
                             (SAlu ALU_SRL (SOff 11 0) (SLit 2)))
               (SLit 3).
Lemma cba_a1_U : forall E n, ew E 11 = Z_to_bv 64 n -> 0 <= n < 2 ^ 64 -> U E cba_a1 = b64_alloc_bound n.
Proof.
intros E n Hn Hr. unfold cba_a1, b64_alloc_bound. rewrite !U_SAlu. cbn [zalu_raw].
rewrite (U_atom E 11 n Hn Hr), !U_SLit.
replace (Z.land (zcanon 2) 63) with 2 by reflexivity. replace (Z.land (zcanon 1) 63) with 1 by reflexivity.
replace (zcanon 3) with 3 by reflexivity.
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.shiftl_mul_pow2 by lia.
change (2 ^ 2) with 4. change (2 ^ 1) with 2.
assert (Hq : 0 <= n / 4 < 2 ^ 62) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (zcanon_small (n / 4)) by lia.
rewrite (zcanon_small (n / 4 * 2)) by lia.
rewrite (zcanon_small (n / 4 * 2 + n / 4)) by lia.
rewrite zcanon_small by lia.
lia.
Qed.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* FSH_Fn_checks.v Section c's image facts; the walk does not use them *)
Hypothesis IMG : fs_img_facts tfibsegs B.

(* SK is generic: the walk never reaches the sink, so the theorem holds at B's sink FSH_Base.fsB_sink_head too *)
Theorem check_bounded_alloc_proof : @check_bounded_alloc_spec fx rc SK tfibsegs B.
Proof.
intros ly S U W regs mem md ch held n live peak cnt fail HPRE _ Hglob H10 H11 Hheld Hn Hle.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fs_segs_low as HSL. pose proof fs_wx as HWX.
destruct HPRE as [HAPU _].
pose proof (fsw_sp B _ ly S U W regs mem md ch HAPU) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _).
pose proof HAPU as (HAP & _ & _).
pose proof HAP as (HAR & Hra & _).
assert (FS : STK_check_bounded_alloc = 16) by reflexivity.
pose proof (fsw_entry B STK_check_bounded_alloc 16 ly S U W regs mem md ch A_check_bounded_alloc HAPU
  ltac:(lia) ltac:(vm_compute; reflexivity)) as HS.
pose proof (ajournal_init tfibsegs B STK_check_bounded_alloc [] ly S W regs (unpoison U mem) md ch HAP) as HJ.
pose proof (fsw_ARU B _ ly S U W regs mem md ch HAPU) as HARU.
set (E := Ereg regs []) in HS.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 held) by (subst E; rewrite (ew_Ereg_nat regs [] 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 n) by (subst E; rewrite (ew_Ereg_nat regs [] 11 11%bv eq_refl); exact H11).
unfold cfg_at. change (w64 A_check_bounded_alloc) with (Z_to_bv 64 A_check_bounded_alloc).
(* ---- 0x81618 .. the branch at 0x81630 ---- *)
fsw_aj_runU cba_tbl_ok HS HJ HARU.
{ awr_ok_tac. exact Usp. }
assert (SB1 : same_below mem (ms_mem ms) alloc_ceiling).
{ change (frame_of E [fstk 16] mem (ms_mem ms)) in HF.
  apply (same_below_frame1 E (fstk 16) mem (ms_mem ms) alloc_ceiling HF); [|lia].
  cbn [fstk YP09.r_base YP09.r_wlo base_val]. rewrite Usp. lia. }
eapply SRr_sym_branch with (c := BC_LTU) (a := cba_a1) (b := SOff 10 0); [exact HS | |].
- (* taken: the abort path 0x81640; ruled out by held <= b64_alloc_bound n *)
  intros Hb _. exfalso. rewrite branch_ltu_U in Hb.
  rewrite (cba_a1_U E n E11 Hn), (U_atom E 10 held E10 Hheld) in Hb.
  apply Z.ltb_lt in Hb. lia.
- intros _ HS2. clear HS.
  (* ---- not taken: 0x81634 .. the return at 0x8163c ---- *)
  fsw_aj_runU cba_tbl_ok HS2 HJ HARU.
  { awr_ok_tac. exact Usp. }
  rewrite ?wvb_collapse in HJ.
  assert (SB2 : same_below (ms_mem ms) (ms_mem ms0) alloc_ceiling).
  { cbn [add_cond ss_mem] in HF0.
    eapply (same_below_frame1 E _ (ms_mem ms) (ms_mem ms0) alloc_ceiling HF0); [|lia].
    cbn [YP09.r_base YP09.r_wlo base_val]. rewrite Usp. lia. }
  pose proof (fsw_reg_atom _ regs [] _ ms0 1%bv 1%bv 1 HS2 ltac:(vm_compute; reflexivity) eq_refl) as R1.
  eapply (SRr_ret_at tfibsegs cba_tbl cba_tbl_ok fs_wx); [exact HS2 | reflexivity | vm_compute; reflexivity |].
  intros mat2.
  assert (Hpc : v_jalr (YK11.getr (ms_regs ms0) 1) 0 = YK11.getr regs 1) by (rewrite R1; exact Hra).
  rewrite Hpc. unfold fpostU.
  do 5 eexists. split; [reflexivity|].
  split; [apply (ajournal_materialize tfibsegs B LAWS HSL); exact HJ|].
  split; [exact (proj1 (proj2 HARU))|].
  split; [exact (proj2 (proj2 HARU))|].
  split; [eapply (aregs_preserved_of_st_ok tfibsegs _ E _ _ regs [] HS2); [apply env_agree_refl | vm_compute; reflexivity]|].
  split; [reflexivity|].
  exact (fs_glob_below W mem (ms_mem ms0) live peak cnt fail (same_below_trans _ _ _ _ SB1 SB2) Hglob).
Qed.
End W.
