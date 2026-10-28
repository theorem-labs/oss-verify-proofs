(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Bytes InitMem Mem Cells Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim STree Monad Stdio Driver Adapter Prog AsanCtrl AsanEmbed Harness ProgA AsanProgDeps AsanHandoff.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF ITreeA SysStepF Shadow ModelX.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AS Require Import MainExport MainFactsAsan MainEntryAsan.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib Require Import TopLevel AsanMain.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase ABytes RtCells AProto AMalloc_iface AProg_kit AHarness_iface
     F_syscalls StdioFiles Stdio_kit Stdio_iface MonadF Strnlen_iface AExit F_module_dtor ADriver_iface AD_kit AD_ctx AD_main_A AD_main_B4 AD_main_C AD_main AD_main_pack AMain_asm AFake_iface ALayout ARepInit_kit AD_handoff0 AD_handoff_hi.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition UDRV : list (list Z) :=
  [[AMALLOC_PC; 0x825dc]; [AMALLOC_PC; 0x82630]; [AFREE_PC; 0x82654]; [AFREE_PC; 0x82784];
   [AMALLOC_PC; ATRUN_MALLOC_RA]; [AFREE_PC; ATRUN_FREE_RA]; [AMALLOC_PC]; [AFREE_PC];   (* [comment removed for export] *)
   (* [comment removed for export] *)
   [AMALLOC_PC; AFMALLOC_RET]; [AMALLOC_PC; ACDCTX_MRET]; [AFREE_PC; AFREEB_RET];
   [AFREE_PC; AFREEP_RET]; [AFREE_PC; AFDCTX_FRET]]%Z.

(* [comment removed for export] *)
Definition LDRV (V : nat -> Z) (w : bool) : alayout := mkALayout (LV V) w UDRV.   (* [comment removed for export] *)

Lemma HU_LDRV : forall V w, HU (LDRV V w).
Proof. intros V w. unfold HU, LDRV, UDRV. cbn [al_U]. repeat split; cbn; tauto. Qed.

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
      valid_entry (mkImage bsegs b_init_pc b_phdrs) en inp -> valid_input_either inp -> bmain_open en inp w V m ms mo ->
      atop_of (en_sp en) = ATOP ->
      AHEAP AI (LDRV V w) (RNG0 A0 V mo) (aps_m (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) ATOP)) [] m.
  Hypothesis AHEAP_INIT : aheap_init_stmt.

  (* [comment removed for export] *)
  Definition aresv_init_stmt : Prop :=
    forall en inp w V m ms mo,
      valid_entry (mkImage bsegs b_init_pc b_phdrs) en inp -> valid_input_either inp -> bmain_open en inp w V m ms mo ->
      aresv_ok (LDRV V w) (resv_of V).
  Hypothesis ARESV_INIT : aresv_init_stmt.

  (* [comment removed for export] *)
  Definition rng_fs_init_stmt : Prop :=          (* [comment removed for export] *)
    forall V w mo, Forall (pfact_ok V) both_pure_facts -> 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP ->
      rng_fs (LDRV V w) (RNG0 A0 V mo).
  Hypothesis RNGFS_INIT : rng_fs_init_stmt.

  Lemma A0I' : forall V (p : word), bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V both_vis) p -> A0 V p.
  Proof. intros V p H1 H2. apply A0I; assumption. Qed.

  Theorem apat_main_extract : forall en inp w V m ms mo,
    valid_entry (mkImage bsegs b_init_pc b_phdrs) en inp -> valid_input_either inp -> bmain_open en inp w V m ms mo ->
    atop_of (en_sp en) = ATOP ->
    exists L, apat_mainA AI rng_fs L (RNG0 A0 V mo) inp (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) ATOP) ms.
  Proof.
    intros en inp w V m ms mo VE VI AM HA. exists (LDRV V w).
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
    assert (IMGHI : usp + Z.of_nat (length (entry_stack_image b_phdrs sp argv envp (in_uid inp) (in_hwcap inp) rdraw)) <= 2^64).
    { (* [comment removed for export] *)
      pose proof (length_entry_stack_image b_phdrs sp argv envp (in_uid inp) (in_hwcap inp) rdraw) as ILS.
      pose proof (build_stack_bytes_length b_phdrs sp argv envp (in_uid inp) (in_hwcap inp) rdraw) as BL.
      pose proof (raw_len_nonneg argv envp) as (R1 & R2 & R3 & R4).
      unfold entry_stack_span in FITS. unfold raw_len, struct_size, Lib.InitMem.argc, Lib.InitMem.envc in BL.
      change (Z.of_nat auxv_size) with 160 in FITS. clear - ILS BL R2 R3 R4 FITS SPHI. lia. }
    assert (SPLO' : stack_max_size <= usp) by (unfold stack_max_size; lia).
    assert (HID' : forall z, str_base sp argv envp <= z < str_base sp argv envp + Z.of_nat (length (SBLK argv envp)) ->
                     m (wa z) = wrap_mem b_phdrs sp argv envp (in_uid inp) (in_hwcap inp) rdraw (wa z)).   (* [comment removed for export] *)
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
              /\ bytes_at bsegs m P1 (nth 1 argv [] ++ Z_to_bv 8 0 :: slack1)
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
    exists usp, (V 44%nat), (Z_to_bv 64 (usp + 8)), (Z_to_bv 64 (Z.of_nat (length argv))), (Z_to_bv 64 BMAIN), (Z_to_bv 64 (usp + 8 * Z.of_nat (length argv) + 16)),
           (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0).
    exists (RSTK0 usp), (Z_to_bv 64 (V 45%nat)), (str_base sp argv envp), P1, slack0, slack1, RA0, RA1.   (* [comment removed for export] *)
    unfold RSTK0. cbn [r_lo r_hi r_rlo r_rhi].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [exact SP16|]. split; [exact USPLO|]. split; [exact SPAN24|].
    split; [lia|]. split; [exact SPG|]. split; [exact BOT|].
    (* [comment removed for export] *)
    do 8 (split; [unfold LDRV, UDRV; cbn; tauto|]). split; [apply HU_LDRV|].
    split; [subst argv; exact VARGV|].
    (* [comment removed for export] *)
    unfold AENTRY. subst ms.
    exists (Z_to_bv 64 (V 1128%nat)), (Z_to_bv 64 (V 1129%nat)), (Z_to_bv 64 (V 1130%nat)),
           (Z_to_bv 64 (usp + 8 * Z.of_nat (length argv) + 16)), (Z_to_bv 64 0x6000000000000000),
           (Z_to_bv 64 (V 1131%nat)), (Z_to_bv 64 (V 1132%nat)), (Z_to_bv 64 (V 1133%nat)), (Z_to_bv 64 (V 1134%nat)),
           (Z_to_bv 64 (V 1135%nat)), (Z_to_bv 64 (V 1136%nat)), (Z_to_bv 64 (V 1137%nat)), (Z_to_bv 64 (V 1138%nat)), m.
    split. { unfold ASTAGE2_RET, AMAIN_PC, BMAIN, ATP, MainEntryAsan.BRA, MainEntryAsan.BGP, MainEntryAsan.BTP, MainEntryAsan.BMAIN. subst argv. replace (usp + -48) with (usp - 48) by lia. reflexivity. }
    (* [comment removed for export] *)
    split. { destruct (stk_split _ _ (usp - 8388608) (ALO usp) usp ST ltac:(unfold ALO; lia)) as [_ ST2]. exact ST2. }
    split; [exact MI|].
    (* [comment removed for export] *)
    pose proof (astat_cells V m HM) as AC. pose proof (gdescs_init V m HM) as GD.
    pose proof (astat_shG V m HM) as SHG. pose proof (astat_shD V m HM) as SHD. pose proof (astat_shB V m HM) as SHB.
    decompose [and] AC.
    split. { (* [comment removed for export] *)
             pose proof (aatexit_cells0_init V m HM) as [ATX ICB]. split; [| split; [exact ATX | intros E; discriminate E]].
             unfold ASTAT0. repeat match goal with |- _ /\ _ => split end; try assumption. }
    (* [comment removed for export] *)
    split; [exact (stderr_wfile0_init V m HM)|].
    split; [exact (ssp_guard_init V m HM)|].
    split; [exact (atrun_cells0_init V m HM)|].                               (* [comment removed for export] *)
    split. { exact (harness_invA_init V m HM). }                               (* [comment removed for export] *)
    split; [exact (rodata_sh0_init' V m HM)|].
    split. { unfold rclean. cbn [r_lo r_hi r_rlo r_rhi]. split; [| lia]. apply (stack_shclean_init V m HM HP HAT); unfold ALO, Shadow.KEND in *; lia. }
    split; [exact (rclean_stdout_buf_init V m HM)|].
    split; [exact (rclean_stage_init V m HM)|].                                  (* [comment removed for export] *)
    split. { exists (Z_to_bv 64 0). rewrite errno_addr_ATP. exact (errno_init V m HM). }
    split; [exact (stdout_file_init V m HM)|].
    split; [reflexivity|].
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
      unfold MainEntryAsan.ACEIL in *. fold argv. rewrite En0. rewrite Eoff0, Z.add_0_r in *.
      repeat match goal with |- _ /\ _ => split end.
      - apply RS; lia.
      - apply RS; lia.
      - apply RI; lia.
      - apply RIS; lia.
      - apply RNGFS_INIT; [exact HP| exact HAT].
      - apply RSS; rewrite !shad_div; unfold AsanEmbed.ASHOFF; clear - SPLO SPHI HA G2 BOT M64a; Z.div_mod_to_equations; lia.   (* [comment removed for export] *)
      - replace (shad 0x10000) with 2147459072 by reflexivity. replace (shad 0x210c0) with 2147467800 by reflexivity. apply RIS; lia.   (* [comment removed for export] *)
      - replace (shad 0x623380) with 2148255344 by reflexivity. replace (shad 0x623800) with 2148255488 by reflexivity. apply RIS; lia.   (* [comment removed for export] *)
      - intros b Hb. apply rng_empty. exact Hb.
      - apply RS; unfold zlength in *; rewrite ?length_map; lia.
      - destruct SC0 as (_ & HL0 & _). unfold hull64, Shadow.KEND in HL0.
        apply RSS; rewrite !shad_div; unfold AsanEmbed.ASHOFF; clear - RLO0' RHI0; Z.div_mod_to_equations; lia.   (* [comment removed for export] *)
      - intros HARGC2. destruct (A1F HARGC2) as (EP1 & BY1 & SL1 & P124 & SC1 & LT1 & IR1 & RLO1 & RLO1' & RHI1 & END1).
        unfold MainEntryAsan.ACEIL in RLO1'. split.
        + apply RS; unfold zlength in *; rewrite ?length_map; lia.
        + destruct SC1 as (_ & HL1 & _). unfold hull64, Shadow.KEND in HL1.
          apply RSS; rewrite !shad_div; unfold AsanEmbed.ASHOFF; clear - RLO1' RHI1; Z.div_mod_to_equations; lia. }   (* [comment removed for export] *)
    (* [comment removed for export] *)
    split. { pose proof (stage2_word_init V m HM) as S2W. rewrite USP3 in S2W. exact S2W. }
    exact (astg_init V m HM).
  Qed.

  (* [comment removed for export] *)
  Hypothesis rng_fs_mono : forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R'.
  Hypothesis DRV_CI : forall iv, In iv drv_img_ranges -> In iv (aci AI).
  Hypothesis CLI_CI : forall iv, In iv cli_img_ranges -> In iv (aci AI).
  Hypothesis CI_WF : forall iv, In iv (aci AI) -> 0 <= fst iv.
  Hypothesis DMALLOC : dmalloc_stmt AI.
  Hypothesis DFREE : dfree_stmt AI.
  Hypothesis DFREEN : dfree_null_stmt AI.
  Hypothesis FUZZ : fuzz_oneA_stmt AI rng_fs.
  Hypothesis HSTRN : strnlen_a_stmt.

  Theorem adrv_closed : adrv_stmt A0.
  Proof.
    eapply adrv_of_walks; first [ exact apat_main_extract | exact (ashenv_law_holds AI) | eassumption ].
  Qed.
End Handoff.

(* [comment removed for export] *)
Lemma afake_rng_init : forall A0, A0_init_stmt A0 -> rng_fs_init_stmt afake_rng A0.
Proof.
  intros A0 A0I V w mo HP HAT. unfold afake_rng, LDRV, al_fake, al_dtls, FAKESZ, RNG0. cbn [al_V LV Nat.eqb].
  (* [comment removed for export] *)
  pf V HP (PVar 377 1573 34359733495) P393. pf V HP (PVar 310 1 34359736319) P310.
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
