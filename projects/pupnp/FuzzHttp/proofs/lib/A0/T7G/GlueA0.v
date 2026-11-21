(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the stack window below sp; the 27- or 29-pair auxv; the launch's input, mmap base and entry draw; the CONFIG_RSEQ value); and launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes Image Agree Ceiling RunWord InitStack.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Stdio.
From OSSVerify.pupnp.FuzzHttp.images Require Import Asan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import MainExport MainFactsAsan A0Img MainEntry A0Handoff.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts Globals IcptA0 AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ BridgeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import A0LZ AsanAcct.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require A0ShVis.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7 Require Import RealizeS SeamA0 A0Prog.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit GlobalsShadow Stdio_base Stdio_iface RDriverA_kit RDriverA_ctx RDriverA_main.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Malloc Require Import InitMem.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7G Require Import GlueKit GlueA0_T.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation z64 := (Z_to_bv 64 0).

Definition amain_at_V (V : nat -> Z) (en : ExecEntry) (inp : ProcInput) (ms : machine_state) (mo : Model) : Prop :=
  let usp := bv_unsigned (en_sp en) in
  let argc := Z.of_nat (length (in_argv inp)) in
  let envc := Z.of_nat (length (in_envp inp)) in
  exists (w : bool) (m : word -> option byte),
    ms = MS (mkR (Z_to_bv 64 ARA) (Z_to_bv 64 (usp - 48)) (Z_to_bv 64 AGP) (Z_to_bv 64 ATP)
                 (Z_to_bv 64 (V 1833%nat)) (Z_to_bv 64 (V 1834%nat)) (Z_to_bv 64 (V 1835%nat))
                 (Z_to_bv 64 (usp + 8)) (Z_to_bv 64 argc) (Z_to_bv 64 argc) (Z_to_bv 64 (usp + 8))
                 (Z_to_bv 64 (usp + 8 * argc + 16)) (Z_to_bv 64 0x6000000000000000)
                 (Z_to_bv 64 (V 1836%nat)) (Z_to_bv 64 (V 1837%nat)) (Z_to_bv 64 (V 1838%nat)) (Z_to_bv 64 (V 1839%nat))
                 (Z_to_bv 64 AMAIN) (Z_to_bv 64 (usp + 8 * argc + 16))
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 (V 1840%nat)) (Z_to_bv 64 (V 1841%nat)) (Z_to_bv 64 (V 1842%nat)) (Z_to_bv 64 (V 1843%nat)))
            bvmap_empty (Z_to_bv 64 AMAIN) (Z_to_bv 32 0) None m (seg_rom asegs)
    /\ (forall n, 0 <= V n < 2 ^ 64)

    /\ (V 0%nat = usp / 32768 /\ V 6%nat = usp mod 4096 / 16 /\ V 10%nat = usp mod 32768 / 4096
        /\ 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = usp
        /\ V 1%nat = argc /\ V 2%nat = envc
        /\ V 3%nat = Z.of_nat (length (nth 0 (in_argv inp) [])) /\ V 7%nat = Z.of_nat (length (nth 1 (in_argv inp) []))
        /\ V 4%nat = Wblk en inp /\ V 5%nat = bv_unsigned (en_brk en) / 4096 /\ V 8%nat = bv_unsigned (in_uid inp)
        /\ V 9%nat = bv_unsigned (in_hwcap inp))
    /\ Forall (mfact_ok asegs V m) (asan_mem_facts ++ asan_mem_facts_w w)
    /\ Forall (pfact_ok V) (asan_pure_facts ++ asan_pure_facts_w w)
    /\ mem_inv asegs m
    /\ stk asegs m (usp - 6144512) usp
    /\ bytes_at asegs m (usp + 8) (le8 (Z_to_bv 64 (str0 en inp)))
    /\ bytes_at asegs m (usp + 16)
         (le8 (Z_to_bv 64 (Z.b2z (1 <? argc) * (str0 en inp + Z.of_nat (length (nth 0 (in_argv inp) [])) + 1))))
    /\ (forall a, hidden_arg en inp a ->
          m (wa a) = wrap_mem inp (en_mmap_base en) a_phdrs (Z_to_bv 64 (Z.of_N a_init_pc)) (en_sp en) (en_draw en) (wa a))
    /\ ashadow0 V m

    /\ Forall (mfact_ok asegs V (mrestrict (a0_H0 V mo) m)) (asan_mem_facts ++ asan_mem_facts_w w)
    /\ amodel V (en_sp en) (in_fs inp) mo.
Lemma amain_at_split : forall en inp ms mo, amain_at en inp ms mo -> exists V, amain_at_V V en inp ms mo.
Proof. intros en inp ms mo (w & V & m & H). exists V, w, m. exact H. Qed.
Lemma amain_at_of_V : forall V en inp ms mo, amain_at_V V en inp ms mo -> amain_at en inp ms mo.
Proof. intros V en inp ms mo (w & m & H). exists w, V, m. exact H. Qed.

Definition alloc_init_stmt {HC : HasCeiling} (FI : fs_if) (AI : am_if FI) (V0 : nat -> Z) (sp : word) (fs : Fs.Fs) (mo : Model) : Prop :=
  forall (w : bool) (m : mem),
    Forall (mfact_ok asegs V0 (mrestrict (a0_H0 V0 mo) m)) (asan_mem_facts ++ asan_mem_facts_w w) ->
    Forall (pfact_ok V0) (asan_pure_facts ++ asan_pure_facts_w w) ->
    amodel V0 sp fs mo -> 32768 * V0 0%nat + 4096 * V0 10%nat + 16 * V0 6%nat = bv_unsigned sp -> alloc_ceiling = bv_unsigned sp - 8388608 ->
    (forall x : word, ashadow (bv_unsigned x) -> a0_H0 V0 mo x = false -> mrestrict (a0_H0 V0 mo) m x <> None) ->
    exists (s : aps FI AI) (st : fsstate FI),
      RHEAP_A FI AI s [] (mrestrict (a0_H0 V0 mo) m) /\ RFAKE FI st (mrestrict (a0_H0 V0 mo) m) /\ am_ghost FI AI s = (a0_H0 V0 mo, a0_P0 V0)
      /\ fs_live FI st = [] /\ am_nsec FI AI s = 0
      /\ am_vm FI AI s (m_vm (perase (a0_P0 V0) mo)).

Section GlueA0.
  Context {HC : HasCeiling} {HG : HasGuard}.
  Variable FI : fs_if.
  Variable AI : am_if FI.
  Variable PZ : mem -> Prop.
  Variable V0 : nat -> Z.
  Variables (sp0 : word) (fs0 : Fs.Fs) (mo0 : Model).

  Definition H_MAIN_G (inp : ProcInput) (en : ExecEntry) (ms : machine_state) (mo : Model) : Prop :=
    (amain_at_V V0 en inp ms mo /\ bytes_at asegs (ms_mem ms) ssp_guard (le8 guard_word))
    /\ (en_sp en = sp0 /\ in_fs inp = fs0 /\ mo = mo0).

  Hypothesis ALLOC_INIT : alloc_init_stmt FI AI V0 sp0 fs0 mo0.

  Hypothesis PZ_INIT : forall V (m : mem), Forall (mfact_ok asegs V m) asan_mem_facts -> PZ m.

  #[using="ALLOC_INIT PZ_INIT"] Theorem glue_A0 : forall inp en msF mo,
    valid_input inp -> valid_entry imgA0 en inp -> alloc_ceiling = bv_unsigned (en_sp en) - 8388608 -> H_MAIN_G inp en msF mo ->
    exists g, INVA (mkCfg msF mo) g
         /\ rat_mainA FI AI PZ (en_sp en) (in_argv inp) (in_envp inp) inp (en_mmap_base en) (en_draw en) (restrict (g_H g) msF) g
         /\ img_fits (en_sp en) (in_argv inp) (in_envp inp) inp (en_mmap_base en) (en_draw en).
  Proof.
    intros inp en msF mo VI VE CEIL [[AMA GP] (ESP & EFS & EMO)]. subst sp0 fs0 mo0.
    pose proof VI as (VARGV & VENVP & _).
    (* the launch facts: [valid_sp] and the block from sp to the stack top ([InitStack.launch_facts]) *)
    assert (VSPF : valid_sp (en_sp en) /\ img_fits (en_sp en) (in_argv inp) (in_envp inp) inp (en_mmap_base en) (en_draw en)).
    { pose proof (valid_input_va_size _ VI) as Hsv48. pose proof (valid_input_launch _ VI) as VL.
      destruct en as [sp brk mb dr]. rewrite (valid_entry_sv48 _ _ _ Hsv48) in VE. cbn [imgA0] in VE. cbn [en_sp en_mmap_base en_draw].
      destruct VE as (A & _ & _ & _ & LOK).
      destruct (launch_facts inp sp brk mb dr VL LOK) as (_ & LPAD & _ & LHI & _ & _).
      split; [exact A|]. unfold img_fits. split; [exact LPAD| exact LHI]. }
    destruct VSPF as [VSP IFIT].
    destruct AMA as (w & m & Hms & VR & PINS & HMF & HPF & MI & STK & C1 & C2 & HARG & SH0 & HMFr & AMo). set (V := V0) in *.
    destruct PINS as (P0 & P6 & P10 & PSP & P1 & P2 & P3 & P7 & P4 & P5 & P8 & P9).
    pose proof (fits_facts _ _ _ _ _ _ IFIT) as (FL & FS & FX1 & FX2 & FT1 & FT2 & FT3).
    (* argv[0]'s first byte: sp + C + W is the string base top - 8 - L *)
    assert (ESTR : str0 en inp = str_base (ed_top (en_draw en)) (in_argv inp) (in_envp inp) (in_execfn inp)).
    { pose proof IFIT as [PAD _]. unfold str0, Wblk, str_base, block_pad_len. unfold hsz, lstr in PAD |- *.
      change (la_rseq (launch_auxv inp (en_sp en) (en_mmap_base en))) with (kb_rseq (in_kernel inp)) in PAD.
      rewrite Z2Nat.id by lia. lia. }
    set (usp := bv_unsigned (en_sp en)) in *.
    pose proof (proj1 (Forall_app _ _ _) HMF) as [HMFc _].
    pose proof (proj1 (Forall_app _ _ _) HMFr) as [HMFrc _].
    pose proof (proj1 (Forall_app _ _ _) HPF) as [HPFc _].
    destruct (ALLOC_INIT w m HMFr HPF AMo PSP CEIL (fun x HA HX => A0ShVis.ashadow_present_r V m (a0_H0 V mo) HMFc SH0 x HA HX)) as (s & st & HP & RF & GH & FSL & NS0 & VM0).
    set (H0 := a0_H0 V mo) in *. set (mr := mrestrict H0 m) in *.
    exists (gh FI AI s). unfold gh. rewrite GH. cbn [fst snd g_H g_P].
    split.
    { split; [exact (a0_lzframe V _ _ mo AMo)|]. split; [| cbn [g_V cfg_model]; exact VM0]. intros a Ha Hz. rewrite Hms. cbn [ms_mem MS]. exact (a0_hzero_mem V mo m SH0 a Ha Hz). }
    split; [| exact IFIT].
    pose proof VSP as (SPLO & SPHI & SPAL). unfold sp_window_lo, sp_window_hi in SPLO, SPHI. fold usp in SPLO, SPHI, SPAL.
    assert (HSTK : forall a : word, usp - 8388608 <= bv_unsigned a -> H0 a = false).
    { intros a Ha. apply (a0_H0_false V (en_sp en) (in_fs inp) mo a AMo). left. exact Ha. }
    assert (0 <= argc (in_argv inp) /\ 0 <= envc (in_envp inp)) by (unfold argc, envc; lia).

    assert (EG : guard_word = Z_to_bv 64 (V 45%nat)).
    { mf V m HMFc (MRo (ZLit 6318512) 8 (ZV 45)) G. rewrite Hms in GP. cbn [ms_mem MS] in GP. unfold ssp_guard in GP.
      exact (bytes_at_le8_inj m _ _ _ GP G). }

    rewrite Hms. unfold rat_mainA, restrict. cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS].
    do 20 eexists. exists bvmap_empty, (Z_to_bv 32 0), (V 44%nat), z64, mr, s, st.
    split.
    { unfold MS, ARA, AGP, ATP, AMAIN, RATPA, envp_addr, argc. fold usp.
      replace (usp - 48) with (usp + -48) by lia.
      replace (usp + 8 * Z.of_nat (length (in_argv inp)) + 16) with (usp + 8 * (Z.of_nat (length (in_argv inp)) + 2)) by lia.
      reflexivity. }
    split; [vm_compute; reflexivity|].
    split; [apply mem_inv_mrestrict; exact MI|].
    split. { apply stk_mrestrict; [exact (proj1 (stk_split asegs m _ (usp + -48) _ STK ltac:(lia)))|]. intros a Ha. apply HSTK. rewrite wa_unsigned by lia. lia. }
    split; [exact (errno_init V mr HMFrc)|].
    split; [exact (exitc_init V mr HMFrc)|].
    split. { pf V HPFc (PVar 44 1 4194303) R. lia. }
    split; [apply a0_rw_image_wr_at; lia|].
    split; [rewrite EG; exact (mainc_init V mr HMFrc)|].
    split; [exact (stdout_file_init V mr HMFrc)|].
    split; [exact (stderr_wfile0_init V mr HMFrc)|].
    split; [exact (stdin_file_init V mr HMFrc)|].
    split; [exact (rsva_init V mr HMFrc)|].
    split.
    { destruct VARGV as (ARGC & _).
      rewrite ESTR in C1, C2.
      apply (imgk_init (en_sp en) inp (en_mmap_base en) (en_draw en) IFIT ltac:(lia)).
      - unfold mr. apply bytes_at_mrestrict; [exact C1|]. intros i Hi. rewrite length_le8 in Hi. apply HSTK. fold usp.
        rewrite wa_unsigned by lia. lia.
      - unfold mr. apply bytes_at_mrestrict; [exact C2|]. intros i Hi. rewrite length_le8 in Hi. apply HSTK. fold usp.
        rewrite wa_unsigned by lia. lia.
      - intros a Ha. unfold mr, mrestrict. rewrite HSTK by (rewrite wa_unsigned by lia; lia).
        apply HARG. unfold hidden_arg. right. rewrite ESTR. lia. }
    split; [exact HP|]. split; [exact RF|]. split; [exact (asan_env_init V mr HMFrc)|]. split; [unfold gh; rewrite GH; reflexivity|].
    split; [exact FSL|]. split; [exact NS0|].
    split. { apply (shz_init (en_sp en) (in_argv inp) (in_envp inp) inp (en_mmap_base en) (en_draw en) V mr HMFrc PSP);
               [fold usp in P6; rewrite P6; Z.div_mod_to_equations; lia | fold usp in P10; rewrite P10; Z.div_mod_to_equations; lia | exact CEIL | fold usp; lia]. }
    split; [exact (globals_shadow_init V mr HMFrc)| exact (PZ_INIT V mr HMFrc)].
  Qed.
End GlueA0.
