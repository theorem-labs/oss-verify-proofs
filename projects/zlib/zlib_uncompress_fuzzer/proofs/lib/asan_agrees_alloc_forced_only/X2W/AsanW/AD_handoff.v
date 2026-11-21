(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Bytes InitMem Mem Cells Frame.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import DrvAgree.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import Prelim STree Monad Stdio Driver Adapter Prog AsanCtrl AsanEmbed ProgA AsanProgDeps. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.X2W.Spec Require Import AsanHandoff.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import ExecF ITreeA SysStepF Shadow ModelX.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS Require Import MainExport MainFactsAsan. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.X2W.AS Require Import MainEntry.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only Require Import TopLevel. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.X2W Require Import AsanMain.     (* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW Require Import AImg ABase ABytes RtCells AProto AMalloc_iface AUri_kit AHarness_iface F_syscalls StdioFiles Stdio_kit Stdio_iface MonadF Strnlen_iface AExit F_module_dtor ADriver_iface AD_kit AD_ctx AD_main_A AD_main_B4 AD_main_C. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.X2W.AsanW Require Import AD_main AMain_asm. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW Require Import AFake_iface ALayout ARepInit_kit. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.X2W.AsanW Require Import AD_handoff0.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac div8_goal := repeat match goal with |- context [?x / 8] =>
    lazymatch goal with _ : 8 * (x / 8) <= x |- _ => fail | _ => idtac end;
    pose proof (Z.mul_div_le x 8 ltac:(lia)); pose proof (Z.mul_succ_div_gt x 8 ltac:(lia)) end.

Section CANSEC1. Context {rc : runConstT}.
Definition UDRV : list (list Z) :=
  [[AMALLOC_PC; 0x8c4d4]; [AMALLOC_PC; 0x8c528]; [AFREE_PC; 0x8c54c]; [AFREE_PC; 0x8c67c];
   [AMALLOC_PC; 0x8c7b4]; [AFREE_PC; 0x8c848]; [AMALLOC_PC]; [AFREE_PC];
   [AMALLOC_PC; RA_INIT_ZALLOC]; [AMALLOC_PC; RA_UW_ZALLOC; 0x8ced0; 0x8d00c]; [AMALLOC_PC; RA_UW_ZALLOC; 0x8cf14; 0x8d00c]; [AFREE_PC; RA_END_ZFREE_W]; [AFREE_PC; RA_END_ZFREE_S]]%Z.        (* [comment removed for export] *)

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
      valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input_either inp -> amain_open en inp w V m ms mo ->
      atop_of (en_sp en) = ATOP ->
      AHEAP AI (LDRV V w) (AMain_asm.RNG0 A0 V mo) (aps_m (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) ATOP)) [] m.
  Hypothesis AHEAP_INIT : aheap_init_stmt.

  (* [comment removed for export] *)
  Definition aresv_init_stmt : Prop :=
    forall en inp w V m ms mo,
      valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input_either inp -> amain_open en inp w V m ms mo ->
      aresv_ok (LDRV V w) (resv_of V).
  Hypothesis ARESV_INIT : aresv_init_stmt.

  (* [comment removed for export] *)
  Definition rng_fs_init_stmt : Prop :=          (* [comment removed for export] *)
    forall V w mo, Forall (pfact_ok V) asan_pure_facts -> 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP ->
      rng_fs (LDRV V w) (AMain_asm.RNG0 A0 V mo).
  Hypothesis RNGFS_INIT : rng_fs_init_stmt.

  Lemma A0I' : forall V (p : word), bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> A0 V p.
  Proof. intros V p H1 H2. apply A0I; assumption. Qed.

  Theorem apat_main_extract : forall en inp w V m ms mo,
    valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input_either inp -> amain_open en inp w V m ms mo ->
    atop_of (en_sp en) = ATOP ->
    exists L, apat_mainA AI rng_fs L (AMain_asm.RNG0 A0 V mo) inp (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) ATOP) ms.
  Proof.
    intros en inp w V m ms mo VE VI AM HA. exists (LDRV V w).
    pose proof (AHEAP_INIT en inp w V m ms mo VE VI AM HA) as AH. pose proof (ARESV_INIT en inp w V m ms mo VE VI AM) as ARK.
    destruct en as [sp brk0 mbase rdraw]. rewrite (valid_entry_either _ _ _ _ _ _ _ _ VI) in VE. destruct VE as (VSP & _ & _ & FITS & LOK). cbn [en_sp en_draw en_mmap_base] in *.
    (* a worker : the launch conjunct gives the block's geometry, the stack VMA's end (page aligned,
       at most 2^47) and the image's no-wrap bound *)
    pose proof (geom_of_launch Sv48 inp sp brk0 mbase rdraw LOK) as GEOM.
    pose proof (top_of_launch inp sp brk0 mbase rdraw LOK) as THI. change sp_window_hi with (2^47) in THI.
    assert (T8 : bv_unsigned (ed_top rdraw) mod 8 = 0).
    { pose proof LOK as LOK0. cbn [entry_launch_ok_va] in LOK0. destruct LOK0 as ((TM & _ & _) & _ & _).
      unfold page_size in TM. Z.div_mod_to_equations. lia. }
    pose proof (entry_stack_image_no_wrap Sv48 inp mbase a_phdrs (Z_to_bv 64 (Z.of_N a_init_pc)) sp brk0 rdraw LOK) as NW.
    destruct VSP as (SPLO & SPHI & SP16). unfold sp_window_lo in SPLO. unfold sp_window_hi in SPHI. unfold entry_stack_fits, sp_window_hi in FITS.
    pose proof VI as (VARGV & VENVP & _).
    destruct AM as (Hms & HVR & PIN & HMF & HPF & HAF & MI & ST & HID & SH0 & AMOD).   (* a worker : + HAF *) cbn [en_sp en_brk en_draw] in *.
    apply Forall_app in HMF as [HM HMW]. apply Forall_app in HPF as [HP HPW].
    destruct PIN as (PV0 & PV6 & PV10 & USP & PV1 & PV2 & PV3 & PV7 & PV4 & PV5 & PV8 & PV9 & PV11).   (* + V 11 *)
    unfold atop_of in HA.
    set (usp := bv_unsigned sp) in *.
    set (argv := in_argv inp) in *. set (envp := in_envp inp) in *.
    set (RNG := AMain_asm.RNG0 A0 V mo).
    assert (HAT : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP) by (rewrite USP; exact HA).   (* [comment removed for export] *)
    assert (USP3 : 32768 * V 0%nat + (16 * V 6%nat + 4096 * V 10%nat) = usp) by (clear - USP; lia).                  (* [comment removed for export] *)
    pose proof (A0I' V) as AL. change (A0 V) with (A0 V) in AL.
    assert (RNGE : RNG = fp_ok (m_vm_lazy (MX mo [])) (A0 V)) by reflexivity.
    (* [comment removed for export] *)
    pose proof (tid_range V HP) as TID.
    pose proof (argc_pos := proj1 VARGV). cbv beta in argc_pos.
    assert (SPAN24 : usp + 24 <= 2^47).
    { (* a worker : usp + 24 <= str_base <= the stack VMA's end <= 2^47 *)
      pose proof (sb_ge inp mbase a_phdrs (Z_to_bv 64 (Z.of_N a_init_pc)) sp rdraw GEOM) as SG. unfold str_base in SG. pose proof (lsb_eq (in_argv inp) (in_envp inp) (in_execfn inp)).
      pose proof (total_arg_bytes_nonneg (in_argv inp)). pose proof (total_arg_bytes_nonneg (in_envp inp)). subst usp argv envp. lia. }
    assert (USPLO : ATOP + 8388608 <= usp) by (subst usp; lia).
    assert (GEO : ATOP <= ALO usp /\ ALO usp + 6144512 = usp /\ KHIGH <= ALO usp) by (unfold ALO, KHIGH in *; lia).   (* a worker : a worker's ALO *)
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
    assert (IMGHI : usp + Z.of_nat (length (entry_stack_image inp mbase a_phdrs (Z_to_bv 64 (Z.of_N a_init_pc)) sp rdraw)) <= 2^64) by (subst usp; lia).
    (* a worker : amain_at's hidden range reaches the whole strings block *)
    assert (HID' : forall z, str_base (ed_top rdraw) argv envp (in_execfn inp) <= z < str_base (ed_top rdraw) argv envp (in_execfn inp) + Z.of_nat (length (SBLK inp)) ->
                     m (wa z) = wrap_mem inp mbase a_phdrs (Z_to_bv 64 (Z.of_N a_init_pc)) sp rdraw (wa z)).
    { intros z Hz. apply HID. unfold hidden_arg. cbn [en_sp en_draw]. right.
      rewrite SBLK_end in Hz. unfold Wpad. cbn [en_sp en_draw].
      pose proof (pad_len_eq _ _ _ _ _ _ GEOM) as PL. unfold str_base, head_len in *. subst argv envp usp. lia. }
    (* a worker : str_base in amain_at's variables (V 4 = the pad, V 11 = the parity, 27 + 2 r auxv pairs) *)
    assert (SBV : str_base (ed_top rdraw) argv envp (in_execfn inp) = 32768 * V 0%nat + (8 * V 1%nat + (8 * V 2%nat + (V 4%nat + (16 * V 6%nat + (4096 * V 10%nat + 8 * V 11%nat))))) + (472 + 32 * AsanPlanCore.APC.rseq_z (kb_rseq (in_kernel inp)))).
    { pose proof (pad_len_eq _ _ _ _ _ _ GEOM) as PL. pose proof (head_len_eq (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp)) as HL.
      assert (AXC : Z.of_nat (auxv_count (kb_rseq (in_kernel inp))) = 27 + 2 * AsanPlanCore.APC.rseq_z (kb_rseq (in_kernel inp)))
        by (unfold auxv_count, AsanPlanCore.APC.rseq_z; destruct (kb_rseq (in_kernel inp)); reflexivity).
      unfold Wpad in PV4. cbn [en_sp en_draw] in PV4. unfold gap_len in HL. unfold argc, envc in HL.
      unfold str_base. subst argv envp usp. rewrite PV1, PV2, PV4, PV11. lia. }
    (* [comment removed for export] *)
    assert (A0S : exists s0, nth_error argv 0 = Some s0 /\ nth 0 argv [] = s0).
    { subst argv. destruct (in_argv inp) as [|a l]; [cbn in argc_pos; lia|]. exists a. split; reflexivity. }
    destruct A0S as (s0 & Hn0 & En0).
    destruct (arg_pack V inp mbase a_phdrs (Z_to_bv 64 (Z.of_N a_init_pc)) sp rdraw m HM HP GEOM IMGHI T8 THI USPLO HAT HID' 0 s0 Hn0)
      as (off0 & slack0 & RA0 & Hp0 & Ho0 & BY0 & SL0 & P024 & SC0 & LT0 & IR0 & RLO0 & RLO0' & RHI0 & END0).
    fold argv envp in Hp0, BY0, SL0, P024, IR0, END0.   (* a worker : arg_pack states its block over in_argv inp *)
    assert (Eoff0 : off0 = 0).
    { subst argv. destruct (in_argv inp) as [|a l]; [discriminate|]. cbn in Hp0. injection Hp0. lia. }
    (* [comment removed for export] *)
    assert (A1S : exists P1 (slack1 : list byte) (RA1 : region),
              2 <= Z.of_nat (length argv) ->
              P1 = str_base (ed_top rdraw) argv envp (in_execfn inp) + Z.of_nat (length s0) + 1
              /\ bytes_at asegs m P1 (nth 1 argv [] ++ Z_to_bv 8 0 :: slack1)
              /\ (- (P1 + Z.of_nat (length (nth 1 argv [])) + 1)) mod 8 <= zlength slack1
              /\ usp + 24 <= P1
              /\ shclean m (r_lo RA1) (r_hi RA1) (r_rlo RA1) (r_rhi RA1) /\ r_lo RA1 < r_hi RA1
              /\ inreg RA1 P1 (Z.of_nat (length (nth 1 argv [])) + 1 + zlength slack1)
              /\ usp + -112 <= r_rlo RA1 /\ ATOP <= r_rlo RA1 /\ r_rhi RA1 <= 2^47
              /\ P1 + Z.of_nat (length (nth 1 argv [])) + 1 + zlength slack1 <= 2^47).
    { destruct (nth_error argv 1) as [s1|] eqn:Hn1.
      - destruct (arg_pack V inp mbase a_phdrs (Z_to_bv 64 (Z.of_N a_init_pc)) sp rdraw m HM HP GEOM IMGHI T8 THI USPLO HAT HID' 1 s1 Hn1)
          as (off1 & slack1 & RA1 & Hp1 & Ho1 & BY1 & SL1 & P124 & SC1 & LT1 & IR1 & RLO1 & RLO1' & RHI1 & END1).
        assert (En1 : nth 1 argv [] = s1) by (apply nth_error_nth; exact Hn1).
        assert (Eoff1 : off1 = Z.of_nat (length s0) + 1).
        { clear - Hp1 Hn0 Hn1. subst argv. destruct (in_argv inp) as [|a [|b l]]; try discriminate. cbn in Hn0, Hp1. injection Hn0 as ->. injection Hp1. lia. }
        exists (str_base (ed_top rdraw) argv envp (in_execfn inp) + off1), slack1, RA1. intros _. rewrite En1. subst off1.
        repeat match goal with |- _ /\ _ => split end; try assumption. all: lia.
      - exists 0, [], RA0. intros H2. exfalso. apply nth_error_None in Hn1. lia. }
    destruct A1S as (P1 & slack1 & RA1 & A1F).
    (* [comment removed for export] *)
    unfold apat_mainA.
    exists usp, (V 44%nat), (Z_to_bv 64 (usp + 8)), (Z_to_bv 64 (Z.of_nat (length argv))), (Z_to_bv 64 AMAIN), (Z_to_bv 64 (usp + 8 * Z.of_nat (length argv) + 16)),
           (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0).
    exists (RSTK0 usp), (Z_to_bv 64 (V 45%nat)), (str_base (ed_top rdraw) argv envp (in_execfn inp)), P1, slack0, slack1, RA0, RA1.   (* [comment removed for export] *)
    unfold RSTK0. cbn [r_lo r_hi r_rlo r_rhi].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [exact SP16|]. split; [exact USPLO|]. split; [exact SPAN24|].
    split; [lia|]. split; [exact SPG|]. split; [exact BOT|].
    (* [comment removed for export] *)
    do 8 (split; [unfold LDRV, UDRV; cbn; tauto|]). split; [apply HU_LDRV|].
    split; [subst argv; exact VARGV|].
    (* [comment removed for export] *)
    unfold AENTRY. subst ms.
    exists (Z_to_bv 64 (V 1032%nat)), (Z_to_bv 64 (V 1033%nat)), (Z_to_bv 64 (V 1034%nat)),
           (Z_to_bv 64 (usp + 8 * Z.of_nat (length argv) + 16)), (Z_to_bv 64 0x6000000000000000),
           (Z_to_bv 64 (V 1035%nat)), (Z_to_bv 64 (V 1036%nat)), (Z_to_bv 64 (V 1037%nat)), (Z_to_bv 64 (V 1038%nat)),
           (Z_to_bv 64 (V 1039%nat)), (Z_to_bv 64 (V 1040%nat)), (Z_to_bv 64 (V 1041%nat)), (Z_to_bv 64 (V 1042%nat)), m.
    split. { unfold ASTAGE2_RET, AMAIN_PC, AMAIN, ATP, MainEntry.ARA, MainEntry.AGP, MainEntry.ATP, MainEntry.AMAIN. subst argv. replace (usp + -48) with (usp - 48) by lia. reflexivity. }
    (* [comment removed for export] *)
    split. { destruct (stk_split _ _ (usp - ASTK) (ALO usp) usp ST ltac:(unfold ALO, ASTK; lia)) as [_ ST2]. exact ST2. }
    split; [exact MI|].
    (* [comment removed for export] *)
    pose proof (astat_cells V m HM) as AC. pose proof (gdesc_init V m HM) as (GD0 & GD1 & GD2 & GD3 & GD4 & GD5 & GD6 & GD7 & GD8 & GD9 & GD10 & GD11 & GD12 & GD13 & GD14 & GD15 & GD16 & GD17 & GD18 & GD19 & GD20 & GD21 & GD22 & GD23 & GD24 & GD25 & GD26 & GD27 & GD28 & GD29 & GD30 & GD31).
    pose proof (astat_shg0 V m HM) as GS0. pose proof (astat_shg1 V m HM) as GS1. pose proof (astat_shg2 V m HM) as GS2. pose proof (astat_shg3 V m HM) as GS3. pose proof (astat_shg4 V m HM) as GS4. pose proof (astat_shg5 V m HM) as GS5. pose proof (astat_shg6 V m HM) as GS6. pose proof (astat_shg7 V m HM) as GS7. pose proof (astat_shg8 V m HM) as GS8. pose proof (astat_shg9 V m HM) as GS9. pose proof (astat_shg10 V m HM) as GS10. pose proof (astat_shg11 V m HM) as GS11. pose proof (astat_shg12 V m HM) as GS12. pose proof (astat_shg13 V m HM) as GS13. pose proof (astat_shg14 V m HM) as GS14. pose proof (astat_shg15 V m HM) as GS15. pose proof (astat_shg16 V m HM) as GS16. pose proof (astat_shg17 V m HM) as GS17. pose proof (astat_shg18 V m HM) as GS18. pose proof (astat_shg19 V m HM) as GS19. pose proof (astat_shg20 V m HM) as GS20. pose proof (astat_shg21 V m HM) as GS21. pose proof (astat_shg22 V m HM) as GS22. pose proof (astat_shg23 V m HM) as GS23. pose proof (astat_shg24 V m HM) as GS24. pose proof (astat_shg25 V m HM) as GS25. pose proof (astat_shg26 V m HM) as GS26. pose proof (astat_shg27 V m HM) as GS27. pose proof (astat_shg28 V m HM) as GS28. pose proof (astat_shg29 V m HM) as GS29. pose proof (astat_shg30 V m HM) as GS30. pose proof (astat_shg31 V m HM) as GS31.
    pose proof (astat_shd V m HM) as GS32.
    decompose [and] AC.
    split. { unfold ASTAT. repeat match goal with |- _ /\ _ => split end; try assumption. }
    (* [comment removed for export] *)
    split; [exact (stderr_wfile0_init V m HM)|].
    split; [exact (ssp_guard_init V m HM)|].
    split; [split; [exact (atrun_cells0_init' V m HM)| split; [exact (aincb_init V m HM)| split; [exact (atx_cells1w_init V m HM)| exact (alibc_init V m HM)]]]|].      (* [comment removed for export] *)
    split; [exact (harness_sh_init V m HM)|].
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
    pose proof (argv_ptrs_init V m _ HAF) as [AP0 AP1].   (* a worker : from asan_argv_facts *)
    split. { unfold AARGV. split; [| split].
      - rewrite USP3 in AP0. cbn [u64s]. rewrite app_nil_r.
        rewrite SBV. exact AP0.
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
          replace P1 with (Z.b2z ((1 mod two64) <? (V 1%nat mod two64)) * (32768 * V 0%nat + (8 * V 1%nat + (8 * V 2%nat + (V 3%nat + (V 4%nat + (16 * V 6%nat + (4096 * V 10%nat + 8 * V 11%nat)))))) + (473 + 32 * AsanPlanCore.APC.rseq_z (kb_rseq (in_kernel inp))))); [exact AP1|].
          rewrite EP1, SBV.
          assert (L0 : Z.of_nat (length s0) = V 3%nat) by (rewrite PV3, <- En0; reflexivity).
          rewrite L0.
          assert (B1 : (1 mod two64) <? (V 1%nat mod two64) = true).
          { unfold two64. rewrite (Z.mod_small 1) by lia. rewrite (Z.mod_small (V 1%nat)) by (rewrite PV1; subst argv; lia).
            apply Z.ltb_lt. rewrite PV1. subst argv. lia. }
          rewrite B1. cbn [Z.b2z]. lia.
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
    split. { unfold RNGS. subst RNG. unfold AMain_asm.RNG0, rrng, RFMT, RBstdout. cbn [r_rlo r_rhi].
      pose proof (rng_stackside (m_vm_lazy (MX mo [])) (A0 V) V AL HP HAT) as RS. pose proof (rng_stackside_sh (m_vm_lazy (MX mo [])) (A0 V) V AL HP HAT) as RSS.
      pose proof (rng_image (m_vm_lazy (MX mo [])) (A0 V) V AL) as RI. pose proof (rng_image_sh (m_vm_lazy (MX mo [])) (A0 V) V AL) as RIS.
      unfold MainEntry.ACEIL in *. fold argv. rewrite En0. rewrite Eoff0, Z.add_0_r in *.
      repeat match goal with |- _ /\ _ => split end.
      - apply RS; lia.
      - apply RS; lia.
      - apply RI; lia.
      - apply RIS; lia.
      - apply RNGFS_INIT; [exact HP| exact HAT].
      - apply RSS; rewrite !shad_div; unfold AsanEmbed.ASHOFF; div8_goal; lia.
      - replace (shad 0x10000) with 2147459072 by reflexivity. replace (shad 0x22740) with 2147468520 by reflexivity. apply RIS; lia.   (* [comment removed for export] *)
      - replace (shad 0x67bec0) with 2148300760 by reflexivity. replace (shad 0x67c300) with 2148300896 by reflexivity. apply RIS; lia.   (* [comment removed for export] *)
      - intros b Hb. apply rng_empty. exact Hb.
      - apply RS; unfold zlength in *; rewrite ?length_map; lia.
      - destruct SC0 as (_ & HL0 & _). unfold hull64, Shadow.KEND in HL0.
        apply RSS; rewrite !shad_div; unfold AsanEmbed.ASHOFF; div8_goal; lia.
      - intros HARGC2. destruct (A1F HARGC2) as (EP1 & BY1 & SL1 & P124 & SC1 & LT1 & IR1 & RLO1 & RLO1' & RHI1 & END1).
        unfold MainEntry.ACEIL in RLO1'. split.
        + apply RS; unfold zlength in *; rewrite ?length_map; lia.
        + destruct SC1 as (_ & HL1 & _). unfold hull64, Shadow.KEND in HL1.
          apply RSS; rewrite !shad_div; unfold AsanEmbed.ASHOFF; div8_goal; lia. }
    (* [comment removed for export] *)
    split. { pose proof (stage2_word_init V m HM) as S2W. rewrite USP3 in S2W. exact S2W. }
    exact (astg_init V m HM).
  Qed.

  (* [comment removed for export] *)
  Hypothesis rng_fs_mono : forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R'.
  Hypothesis DRV_CI : forall iv, In iv drv_img_ranges -> In iv (aci AI).
  Hypothesis CI_WF : forall iv, In iv (aci AI) -> 0 <= fst iv.
  Hypothesis DMALLOC : dmalloc_stmt AI.
  Hypothesis DFREE : dfree_stmt AI.
  Hypothesis DFREEN : dfree_null_stmt AI.
  Hypothesis FUZZ : fuzz_oneA_stmt AI rng_fs.
  Hypothesis HSTRN : strnlen_a_stmt.

  Theorem adrv_closed : adrv_stmt A0.
  Proof.
    exact (adrv_of_walks AI rng_fs rng_fs_mono DRV_CI CI_WF DMALLOC DFREE DFREEN (ashenv_law_holds AI) FUZZ HSTRN A0 apat_main_extract).
  Qed.
End Handoff.

(* [comment removed for export] *)
Lemma afake_rng_init : forall A0, A0_init_stmt A0 -> rng_fs_init_stmt afake_rng A0.
Proof.
  intros A0 A0I V w mo HP HAT. unfold afake_rng, LDRV, al_fake, al_dtls, FAKESZ, AMain_asm.RNG0. cbn [al_V LV Nat.eqb].
  (* [comment removed for export] *)
  pf V HP (PVar 377 1662 34359733495) P393. pf V HP (PVar 310 1 34359736319) P310.
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
