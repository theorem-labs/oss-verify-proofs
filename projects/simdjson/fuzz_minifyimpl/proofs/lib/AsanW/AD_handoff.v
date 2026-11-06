(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Bytes InitMem Mem Cells Frame.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim STree Monad Stdio Driver Adapter Prog AsanCtrl AsanEmbed HarnessM ProgA AsanProgDeps AsanHandoff.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import ExecF ITreeA SysStepF Shadow ModelX.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AS Require Import MainExport MainFactsAsan MainEntry.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib Require Import TopLevel AsanMainU.     (* [comment removed for export] *)
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AImg ABase ABytes RtCells AProto AMalloc_iface AU_kit AU_iface AHarnessU_iface AIos_iface
     F_syscalls StdioFiles Stdio_kit Stdio_iface MonadF Strnlen_iface AExit F_module_dtor_pre F_module_dtor ADriver_iface AD_kit AD_ctx AD_main_A AD_main_B4 AD_main_C AD_main AMain_asm AFake_iface ALayout ARepInit_kit AD_handoff0 AD_hokit AD_handoff_exit AD_handoff_ios AD_handoff_client
     AAtexit_iface.   (* [comment removed for export] *)
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Set Keyed Unification.   (* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {XP : ExitParams}.
Definition UDRV : list (list Z) :=
  [[AMALLOC_PC; 0xb0a0c]; [AMALLOC_PC; 0xb0a60]; [AFREE_PC; 0xb0a84]; [AFREE_PC; 0xb0bb4];
   [AMALLOC_PC; 0xb0cec]; [AFREE_PC; 0xb0d80]; [AMALLOC_PC]; [AFREE_PC];
   [AMALLOC_PC; AOPNEW_RET];                  (* [comment removed for export] *)
   [AFREE_PC; AVECDEL_RET];                   (* [comment removed for export] *)
   [AFREE_PC; 0xb2e04]; [AFREE_PC; 0xb1df0; 0xb13b0; ATRUN_RET]; [AFREE_PC; 0xb151c; ATRUN_RET]]%Z.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition LDRV (V : nat -> Z) (w : bool) : alayout := mkALayout (LV V) w UDRV (fun _ => None) (fun _ => None).   (* [comment removed for export] *)

Lemma HU_LDRV : forall V w, HU (LDRV V w).
Proof. intros V w. unfold HU, HU_TRACES, LDRV, UDRV. cbn [al_U]. repeat constructor; cbn; tauto. Qed.   (* [comment removed for export] *)
Lemma HUX_LDRV : forall V w, HUX (LDRV V w).
Proof. intros V w. unfold HUX, LDRV, UDRV. cbn [al_U]. cbn; tauto. Qed.

(* [comment removed for export] *)
Definition RSTK0 (usp : Z) : region := mkRegion (ALO usp) (usp + -112) (ALO usp - usp mod 64) (usp - usp mod 64).

Section Handoff.
  Variable AI : AMallocIface.
  Variable rng_fs : alayout -> footprint -> Prop.
  Variable A0 : (nat -> Z) -> alw.
  Hypothesis A0I : A0_init_stmt A0.

  (* [comment removed for export] *)
  Definition aheap_init_stmt : Prop :=
    forall en inp w V m ms mo,
      valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input_either inp -> main_open en inp w V m ms mo ->
      atop_of (en_sp en) = ATOP ->
      AHEAP AI (LDRV V w) (RNG0 A0 V mo) (aps_m (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) ATOP)) [] m.
  Hypothesis AHEAP_INIT : aheap_init_stmt.

  (* [comment removed for export] *)
  Definition aresv_init_stmt : Prop :=
    forall en inp w V m ms mo,
      valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input_either inp -> main_open en inp w V m ms mo ->
      aresv_ok (LDRV V w) (resv_of V).
  Hypothesis ARESV_INIT : aresv_init_stmt.

  (* [comment removed for export] *)
  Definition rng_fs_init_stmt : Prop :=          (* [comment removed for export] *)
    forall V w mo, Forall (pfact_ok V) asan_pure_facts -> 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP ->
      rng_fs (LDRV V w) (RNG0 A0 V mo).
  Hypothesis RNGFS_INIT : rng_fs_init_stmt.

  (* [comment removed for export] *)
  Hypothesis XSLO_H : xp_SLO <= ATOP + 4096.
  Hypothesis XSHI_H : ATOP + 8388608 <= xp_SHI.
  (* [comment removed for export] *)

  Lemma A0I' : forall V (p : word), bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> A0 V p.
  Proof. intros V p H1 H2. apply A0I; assumption. Qed.

  Theorem apat_main_extract : forall en inp w V m ms mo,
    valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input_either inp -> main_open en inp w V m ms mo ->
    atop_of (en_sp en) = ATOP ->
    xp_ICPT m -> xp_ICPTR (RNG0 A0 V mo) ->
    exists L, apat_mainA AI rng_fs L (RNG0 A0 V mo) inp (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) ATOP) ms.
  Proof.
    intros en inp w V m ms mo VE VI AM HA XPI XPR. exists (LDRV V w).
    pose proof (AHEAP_INIT en inp w V m ms mo VE VI AM HA) as AH. pose proof (ARESV_INIT en inp w V m ms mo VE VI AM) as ARK.
    destruct en as [sp brk0 mbase rdraw]. rewrite (valid_entry_either _ _ _ _ _ _ _ _ VI) in VE. destruct VE as (VSP & _ & _ & FITS). cbn [en_sp en_draw] in *.
    destruct VSP as (SPLO & SPHI & SP16). unfold sp_window_lo in SPLO. unfold sp_window_hi in SPHI. unfold entry_stack_fits, sp_window_hi in FITS.
    pose proof VI as (VARGV & VENVP & _).
    destruct AM as (Hms & HVR & PIN & HMF & HPF & MI & ST & HID & SH0 & AMOD). cbn [en_sp en_brk en_draw] in *.
    apply Forall_app in HMF as [HM HMW]. apply Forall_app in HPF as [HP HPW].
    destruct PIN as (PV0 & PV6 & PV10 & USP & PV1 & PV2 & PV3 & PV7 & PV4 & PV5 & PV8 & PV9).
    unfold atop_of in HA.
    set (usp := bv_unsigned sp) in *.
    set (argv := in_argv inp) in *. set (envp := in_envp inp) in *.
    set (RNG := RNG0 A0 V mo).
    assert (HAT : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP) by (rewrite USP; exact HA).   (* [comment removed for export] *)
    assert (USP3 : 32768 * V 0%nat + (16 * V 6%nat + 4096 * V 10%nat) = usp) by (clear - USP; lia).                  (* [comment removed for export] *)
    pose proof (A0I' V) as AL. change (A0 V) with (A0 V) in AL.
    assert (RNGE : RNG = fp_ok (m_vm_lazy (MX mo [])) (A0 V)) by reflexivity.
    (* [comment removed for export] *)
    pose proof (tid_range V HP) as TID.
    pose proof (argc_pos := proj1 VARGV). cbv beta in argc_pos.
    assert (SPAN24 : usp + 24 <= 2^47).
    { unfold entry_stack_span in FITS. pose proof (Run.total_arg_bytes_nonneg argv). pose proof (Run.total_arg_bytes_nonneg envp). subst argv envp. lia. }
    assert (USPLO : ATOP + 8388608 <= usp) by (subst usp; lia).
    assert (GEO : ATOP <= ALO usp /\ ALO usp + 8388608 - 4096 = usp /\ KHIGH <= ALO usp) by (unfold ALO, KHIGH in *; lia).
    destruct GEO as (G1 & G2 & G3).
    assert (SPG : usp = al_sp0 (LDRV V w)) by (unfold LDRV; rewrite LV_sp0; lia).
    assert (TOPR : usp - 160 <= al_top (LDRV V w) <= 2^47).
    { unfold al_top. rewrite <- SPG. unfold page_round_up_Z, page_size. Z.div_mod_to_equations. lia. }
    assert (TOPR' : al_top (LDRV V w) <= usp + 3935) by (unfold al_top; rewrite <- SPG; unfold page_round_up_Z, page_size; Z.div_mod_to_equations; lia).
    assert (BOT : ATOP + 4096 <= ALO usp) by (unfold ALO; lia).
    assert (M64 : 0 <= usp mod 64 < 64 /\ (usp - usp mod 64) mod 64 = 0 /\ (ALO usp - usp mod 64) mod 64 = 0).
    { unfold ALO. Z.div_mod_to_equations. lia. }
    destruct M64 as (M64a & M64b & M64c).
    (* [comment removed for export] *)
    assert (IMGHI : usp + Z.of_nat (length (entry_stack_image a_phdrs sp argv envp (in_uid inp) (in_hwcap inp) rdraw)) <= 2^64).
    { (* [comment removed for export] *)
      pose proof (length_entry_stack_image a_phdrs sp argv envp (in_uid inp) (in_hwcap inp) rdraw) as ILS.
      pose proof (build_stack_bytes_length a_phdrs sp argv envp (in_uid inp) (in_hwcap inp) rdraw) as BL.
      pose proof (raw_len_nonneg argv envp) as (R1 & R2 & R3 & R4).
      unfold entry_stack_span in FITS. unfold raw_len, struct_size, Lib.InitMem.argc, Lib.InitMem.envc in BL.
      change (Z.of_nat auxv_size) with 160 in FITS. clear - ILS BL R2 R3 R4 FITS SPHI. lia. }
    assert (SPLO' : stack_max_size <= usp) by (unfold stack_max_size; lia).
    assert (HID' : forall z, str_base sp argv envp <= z < str_base sp argv envp + Z.of_nat (length (SBLK argv envp)) ->
                     m (wa z) = wrap_mem a_phdrs sp argv envp (in_uid inp) (in_hwcap inp) rdraw (wa z)).   (* [comment removed for export] *)
    { intros z Hz. apply HID. unfold hidden_arg. cbn [en_sp en_draw in_argv in_envp in_uid in_hwcap]. right.
      rewrite SBLK_length in Hz. unfold str_base, struct_size, Lib.InitMem.argc, Lib.InitMem.envc in Hz.
      unfold Wblk. cbn [en_sp en_draw in_argv in_envp in_uid in_hwcap]. rewrite build_stack_bytes_length.
      pose proof (raw_len_nonneg argv envp) as (_ & R2 & R3 & R4).
      unfold raw_len, struct_size, Lib.InitMem.argc, Lib.InitMem.envc. unfold pad_len, raw_len, struct_size, Lib.InitMem.argc, Lib.InitMem.envc in Hz, R4 |- *.
      subst argv envp usp. Z.div_mod_to_equations. lia. }
    (* [comment removed for export] *)
    assert (A0S : exists s0, nth_error argv 0 = Some s0 /\ nth 0 argv [] = s0).
    { subst argv. destruct (in_argv inp) as [|a l]; [cbn in argc_pos; lia|]. exists a. split; reflexivity. }
    destruct A0S as (s0 & Hn0 & En0).
    destruct (arg_pack V sp argv envp (in_uid inp) (in_hwcap inp) rdraw m HM HP SPLO' IMGHI SP16 USPLO HAT FITS VARGV HID' 0 s0 Hn0)
      as (off0 & slack0 & RA0 & Hp0 & Ho0 & BY0 & SL0 & P024 & SC0 & LT0 & IR0 & RLO0 & RLO0' & RHI0 & END0).
    assert (Eoff0 : off0 = 0).
    { subst argv. destruct (in_argv inp) as [|a l]; [discriminate|]. cbn in Hp0. injection Hp0. lia. }
    (* [comment removed for export] *)
    assert (A1S : exists P1 (slack1 : list byte) (RA1 : region),
              2 <= Z.of_nat (length argv) ->
              P1 = str_base sp argv envp + Z.of_nat (length s0) + 1
              /\ bytes_at asegs m P1 (nth 1 argv [] ++ Z_to_bv 8 0 :: slack1)
              /\ (- (P1 + Z.of_nat (length (nth 1 argv [])) + 1)) mod 8 <= zlength slack1
              /\ usp + 24 <= P1
              /\ shclean m (r_lo RA1) (r_hi RA1) (r_rlo RA1) (r_rhi RA1) /\ r_lo RA1 < r_hi RA1
              /\ inreg RA1 P1 (Z.of_nat (length (nth 1 argv [])) + 1 + zlength slack1)
              /\ usp + -112 <= r_rlo RA1 /\ ATOP <= r_rlo RA1 /\ r_rhi RA1 <= 2^47
              /\ P1 + Z.of_nat (length (nth 1 argv [])) + 1 + zlength slack1 <= 2^47).
    { destruct (nth_error argv 1) as [s1|] eqn:Hn1.
      - destruct (arg_pack V sp argv envp (in_uid inp) (in_hwcap inp) rdraw m HM HP SPLO' IMGHI SP16 USPLO HAT FITS VARGV HID' 1 s1 Hn1)
          as (off1 & slack1 & RA1 & Hp1 & Ho1 & BY1 & SL1 & P124 & SC1 & LT1 & IR1 & RLO1 & RLO1' & RHI1 & END1).
        assert (En1 : nth 1 argv [] = s1) by (apply nth_error_nth; exact Hn1).
        assert (Eoff1 : off1 = Z.of_nat (length s0) + 1).
        { clear - Hp1 Hn0 Hn1. destruct argv as [|a [|b l]]; try discriminate. cbn in Hn0, Hp1. injection Hn0 as ->. injection Hp1. lia. }
        exists (str_base sp argv envp + off1), slack1, RA1. intros _. rewrite En1. subst off1.
        repeat match goal with |- _ /\ _ => split end; try assumption. all: lia.
      - exists 0, [], RA0. intros H2. exfalso. apply nth_error_None in Hn1. lia. }
    destruct A1S as (P1 & slack1 & RA1 & A1F).
    (* [comment removed for export] *)
    unfold apat_mainA.
    exists usp, (V 44%nat), (Z_to_bv 64 (usp + 8)), (Z_to_bv 64 (Z.of_nat (length argv))), (Z_to_bv 64 AMAIN), (Z_to_bv 64 (usp + 8 * Z.of_nat (length argv) + 16)),
           (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0).
    exists (RSTK0 usp), (Z_to_bv 64 (V 45%nat)), (str_base sp argv envp), P1, slack0, slack1, RA0, RA1.   (* [comment removed for export] *)
    unfold RSTK0. cbn [r_lo r_hi r_rlo r_rhi].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [exact SP16|]. split; [exact USPLO|]. split; [exact SPAN24|].
    split; [lia|]. split; [exact SPG|]. split; [exact BOT|].
    (* [comment removed for export] *)
    do 8 (split; [unfold LDRV, UDRV; cbn; tauto|]). split; [apply HU_LDRV|].
    split; [apply HUX_LDRV|]. split; [unfold ALO; clear - XSLO_H USPLO HA; lia|]. split; [clear - XSHI_H HA; lia|].
    split; [subst argv; exact VARGV|].
    (* [comment removed for export] *)
    unfold AENTRY. subst ms.
    exists (Z_to_bv 64 (V 2425%nat)), (Z_to_bv 64 (V 2426%nat)), (Z_to_bv 64 (V 2427%nat)),
           (Z_to_bv 64 (usp + 8 * Z.of_nat (length argv) + 16)), (Z_to_bv 64 0x6000000000000000),
           (Z_to_bv 64 (V 2428%nat)), (Z_to_bv 64 (V 2429%nat)), (Z_to_bv 64 (V 2430%nat)), (Z_to_bv 64 (V 2431%nat)),
           (Z_to_bv 64 (V 2432%nat)), (Z_to_bv 64 (V 2433%nat)), (Z_to_bv 64 (V 2434%nat)), (Z_to_bv 64 (V 2435%nat)), m.   (* [comment removed for export] *)
    split. { unfold ASTAGE2_RET, AMAIN_PC, AMAIN, ATP, MainEntry.ARA, MainEntry.AGP, MainEntry.ATP, MainEntry.AMAIN. subst argv. replace (usp + -48) with (usp - 48) by lia. reflexivity. }
    (* [comment removed for export] *)
    split. { destruct (stk_split _ _ (usp - 8388608) (ALO usp) usp ST ltac:(unfold ALO; lia)) as [_ ST2]. exact ST2. }
    split; [exact MI|].
    (* [comment removed for export] *)
    pose proof (exit_cells_init V m HM) as (E1 & E2 & E3 & _ & E5 & E6 & _ & E8 & E9 & _ & E11 & E12 & E13 & E14 & E15 & E16 & _).
    split. { unfold ASTAT. split; [| split; [| exact XPI]].
             - unfold ASTATc. split; [exact E1|]. split; [exact E2|]. split; [do 4 eexists; exact E3|]. split; [exact E5|]. split; [exact E6|]. split; [exact E8|].
               split; [exact E9|]. split; [eexists; exact E11|]. split; [exact E12|]. split; [exact E13|]. split; [exact E14|]. split; [exact E15|]. split; [exact E16|].
               split; [ho_cells V m HM|]. exact (mdtor_stat_of_pre _ (mdtor_pre_init V m HM)).
             - unfold ios_cells. split; [exact (ios_char_shared_init V m HM)|]. split; [exact (ios_cout_init V m HM)|]. split; [exact (ios_clog_init V m HM)|].
               split; [exact (ios_wide_shared_init V m HM)|]. split; [exact (ios_wcout_init V m HM)| exact (ios_wclog_init V m HM)]. }
    (* [comment removed for export] *)
    split; [exact (stderr_wfile0_init V m HM)|].
    split; [exact (ssp_guard_init V m HM)|].
    split. { (* [comment removed for export] *)
             destruct (atrun_cells0_init' V m HM) as [TI TN]. split; [exact TI|]. split; [exact TN|].
             unfold aincb. aimg V m HM 0x6a2a14 [C1 (Z_to_bv 8 0)] HCB. exact HCB. }      (* [comment removed for export] *)
    split; [exact (harness_inv0_init V m HM)|].
    split; [exact (rodata_sh0_init' V m HM)|].
    split. { unfold rclean. cbn [r_lo r_hi r_rlo r_rhi]. split; [| lia]. apply (stack_shclean_init V m HM HP HAT); unfold ALO, Shadow.KEND in *; lia. }
    split; [exact (rclean_stdout_buf_init V m HM)|].
    split; [exact (rclean_stage_init V m HM)|].                                  (* [comment removed for export] *)
    split. { exists (Z_to_bv 64 0). rewrite errno_addr_ATP. exact (errno_init V m HM). }
    split; [exact (stdout_file_init V m HM)|].
    split; [split; reflexivity|].                                                 (* [comment removed for export] *)
    split. { split; [exact ARK| reflexivity]. }                                   (* [comment removed for export] *)
    (* [comment removed for export] *)
    split; [exact AH|].
    (* [comment removed for export] *)
    pose proof (argv_ptrs_init V m HM) as [AP0 AP1].
    split. { unfold AARGV. split; [| split].
      - rewrite USP3 in AP0. cbn [u64s]. rewrite app_nil_r.
        replace (str_base sp argv envp) with (32768 * V 0%nat + (8 * V 1%nat + (8 * V 2%nat + (16 * V 6%nat + 4096 * V 10%nat))) + 184); [exact AP0|].
        unfold str_base, struct_size, Lib.InitMem.argc, Lib.InitMem.envc. subst argv envp. rewrite PV1, PV2. fold usp. lia.
      - unfold astring. fold argv. rewrite En0. rewrite Eoff0, Z.add_0_r in *.
        repeat match goal with |- _ /\ _ => split end; try assumption.
        + unfold F_fmt_fp_lib.zb. rewrite (zbytes_map_unsigned' s0). exact BY0.
        + destruct (arg_facts 0 argv VARGV 0) as [F _]. rewrite En0 in F. exact F.
        + unfold zlength in *. rewrite length_map. exact SL0.
        + destruct (arg_facts 0 argv VARGV 0) as [_ F]. rewrite En0 in F. exact F.
        + unfold rclean. split; [exact SC0| exact LT0].
        + unfold zlength in *. rewrite length_map. exact IR0.
        + clear - RLO0. lia.                                                    (* [comment removed for export] *)
      - intros HARGC2. fold argv. destruct (A1F HARGC2) as (EP1 & BY1 & SL1 & P124 & SC1 & LT1 & IR1 & RLO1 & RLO1' & RHI1 & END1). split.
        + rewrite USP3 in AP1. cbn [u64s]. rewrite app_nil_r.
          replace P1 with (Z.b2z ((1 mod two64) <? (V 1%nat mod two64)) * (32768 * V 0%nat + (8 * V 1%nat + (8 * V 2%nat + (V 3%nat + (16 * V 6%nat + 4096 * V 10%nat)))) + 185)); [exact AP1|].
          rewrite EP1. unfold str_base, struct_size, Lib.InitMem.argc, Lib.InitMem.envc. rewrite <- En0 in *. rewrite PV3. subst argv envp. rewrite PV1, PV2. fold usp.
          unfold two64. rewrite (Z.mod_small 1) by lia. rewrite Z.mod_small by lia.
          replace (1 <? Z.of_nat (length (in_argv inp))) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z]. lia.
        + unfold astring.
          repeat match goal with |- _ /\ _ => split end; try assumption.
          * unfold F_fmt_fp_lib.zb. rewrite (zbytes_map_unsigned' (nth 1 argv [])). exact BY1.
          * destruct (arg_facts 0 argv VARGV 1) as [F _]. exact F.
          * unfold zlength in *. rewrite length_map. exact SL1.
          * destruct (arg_facts 0 argv VARGV 1) as [_ F]. exact F.
          * unfold rclean. split; [exact SC1| exact LT1].
          * unfold zlength in *. rewrite length_map. exact IR1.
          * clear - RLO1. lia. }
    (* [comment removed for export] *)
    split. { unfold RNGS. subst RNG. unfold RNG0, rrng, RFMT, RBstdout. cbn [r_rlo r_rhi].
      pose proof (rng_stackside (m_vm_lazy (MX mo [])) (A0 V) V AL HP HAT) as RS. pose proof (rng_stackside_sh (m_vm_lazy (MX mo [])) (A0 V) V AL HP HAT) as RSS.
      pose proof (rng_image (m_vm_lazy (MX mo [])) (A0 V) V AL) as RI. pose proof (rng_image_sh (m_vm_lazy (MX mo [])) (A0 V) V AL) as RIS.
      unfold MainEntry.ACEIL in *. fold argv. rewrite En0. rewrite Eoff0, Z.add_0_r in *.
      repeat match goal with |- _ /\ _ => split end.
      - apply RS; lia.
      - apply RS; lia.
      - apply RI; lia.
      - apply RIS; lia.
      - apply RNGFS_INIT; [exact HP| exact HAT].
      - apply RSS; rewrite !shad_div; unfold AsanEmbed.ASHOFF; clear - SPLO SPHI HA G2 BOT M64a; Z.div_mod_to_equations; lia.   (* [comment removed for export] *)
      - replace (shad 0x10000) with 2147459072 by reflexivity. replace (shad 0x23680) with 2147469008 by reflexivity. apply RIS; lia.   (* [comment removed for export] *)
      - replace (shad 0x6c5a00) with 2148338496 by reflexivity. replace (shad 0x6c5e40) with 2148338632 by reflexivity. apply RIS; lia.   (* [comment removed for export] *)
      - intros b Hb. apply rng_empty. exact Hb.
      - apply RS; unfold zlength in *; rewrite ?length_map; lia.
      - destruct SC0 as (_ & HL0 & _). unfold hull64, Shadow.KEND in HL0.
        apply RSS; rewrite !shad_div; unfold AsanEmbed.ASHOFF; clear - RLO0' RHI0; Z.div_mod_to_equations; lia.   (* [comment removed for export] *)
      - intros HARGC2. destruct (A1F HARGC2) as (EP1 & BY1 & SL1 & P124 & SC1 & LT1 & IR1 & RLO1 & RLO1' & RHI1 & END1).
        unfold MainEntry.ACEIL in RLO1'. split.
        + apply RS; unfold zlength in *; rewrite ?length_map; lia.
        + destruct SC1 as (_ & HL1 & _). unfold hull64, Shadow.KEND in HL1.
          apply RSS; rewrite !shad_div; unfold AsanEmbed.ASHOFF; clear - RLO1' RHI1; Z.div_mod_to_equations; lia.   (* [comment removed for export] *)
      - exact XPR. }
    (* [comment removed for export] *)
    split. { pose proof (stage2_word_init V m HM) as S2W. rewrite USP3 in S2W. exact S2W. }
    exact (astg_init V m HM).
  Qed.

  (* [comment removed for export] *)
  Hypothesis rng_fs_mono : forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R'.
  Hypothesis DRV_CI : forall iv, In iv drv_img_ranges -> In iv (aci AI).
  Hypothesis URI_CI : forall iv, In iv uri_img_ranges -> In iv (aci AI).
  Hypothesis DMALLOC : dmalloc_stmt AI.
  Hypothesis DFREE : dfree_stmt AI.
  Hypothesis HSTRN : strnlen_a_stmt.
  Hypothesis TRUN : atarget_run_stmtA AI rng_fs.          (* [comment removed for export] *)
  Hypothesis AEXIT : forall code (s : APS) RNG ms (Q : Empty_set -> APS -> footprint -> machine_state -> Prop),
    aat_exit AI code s RNG ms -> implMA RNG (mbind (client_exitA AAllocAsan) (fun _ => exit_model (ioA AAllocAsan) code)) s Q ms.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Theorem adrv_closed_at : forall en inp w V m ms mo,
    valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input_either inp -> main_open en inp w V m ms mo ->
    atop_of (en_sp en) = ATOP ->
    xp_ICPT m -> xp_ICPTR (RNG0 A0 V mo) ->
    implS asegs (RNG0 A0 V mo) (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) ATOP) ASTAGE (argv_Z (in_argv inp)))
          (epostF TT) ms.
  Proof.
    intros en inp w V m ms mo VE VI AM HA XPI XPR.
    destruct (apat_main_extract en inp w V m ms mo VE VI AM HA XPI XPR) as [L HP].
    exact (adrv_of_walks_at AI rng_fs rng_fs_mono DRV_CI URI_CI DMALLOC DFREE (ashenv_law_holds AI) HSTRN TRUN AEXIT A0 inp V mo ms L HP).
  Qed.
End Handoff.

(* [comment removed for export] *)
Lemma afake_rng_init : forall A0, A0_init_stmt A0 -> rng_fs_init_stmt afake_rng A0.
Proof.
  intros A0 A0I V w mo HP HAT. unfold afake_rng, LDRV, al_fake, al_dtls, FAKESZ, RNG0. cbn [al_V LV Nat.eqb].
  (* [comment removed for export] *)
  pf V HP (PVar 377 1735 34359733495) P393. pf V HP (PVar 310 1 34359736319) P310.
  pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 6 0 255) P6. pf V HP (PVar 10 0 7) P10.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 377)) 11571200 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW393.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW310.
  assert (B393 : 4096 <= 4096 * V 377%nat /\ 4096 * V 377%nat + 11571200 <= ATOP) by (clear - P393 P0 P6 P10 DW393 HAT; lia).
  assert (B310 : 4096 <= 4096 * V 310%nat /\ 4096 * V 310%nat + 4096 <= ATOP) by (clear - P310 P0 P6 P10 DW310 HAT; lia).
  pose proof (fun p => A0I V p) as AL.
  destruct (rng_fake (m_vm_lazy (MX mo [])) (A0 V) V AL B393) as [R1 R2].
  split; [exact R1|]. split; [exact R2|]. exact (rng_dtls (m_vm_lazy (MX mo [])) (A0 V) V AL B310).
Qed.
End CANSEC1.

(* [comment removed for export] *)
Definition XT (V : nat -> Z) : Z := 4096 * V 207%nat.
Definition xp_init_fam_stmt {rc : runConstT} (XPf : Z -> ExitParams) (A0 : (nat -> Z) -> alw) : Prop :=
  forall en inp w V m ms mo,
    valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input_either inp -> main_open en inp w V m ms mo ->
    atop_of (en_sp en) = ATOP ->
    @xp_ICPT rc (XPf (XT V)) m /\ @xp_ICPTR rc (XPf (XT V)) (RNG0 A0 V mo).
(* [comment removed for export] *)
