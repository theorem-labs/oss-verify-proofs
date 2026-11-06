(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode SysStep Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanHeap__SpecA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport MainFactsAsan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require KnTrans__AS. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainEntry__AS. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainFactsAsan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.MainLedgerAsan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require NodeSimX__EquivA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.ProgT.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AProto. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface AFake_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acalloc_iseg__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acallocS__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AInstanceF__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepInit_kit__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHandoffDefs. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.ACalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARealloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_acalloc_iseg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.AInstance OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.AInstanceM OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AInstanceF__A3W.AInstanceF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AInstanceF__A3W.AInstanceC OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHandoffDefs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_gotA Pcap_iface_ngA Fuzz_ifaceA GioaReal GioaAlloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_next_ex_allA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_all_closedA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.LeafA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_gotA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaAlloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_next_ex_allA__A3P.GioaFake OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.FoLeafReal OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesUnivA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_all_closedA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioLawsA StdioCompA Stdio_glueA Stdio_glue_pfA Stdio_glue_snA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_glue_foKitA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_glue_exitA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_glue_drvA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioLawsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioCompA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_pfA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_snA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_foA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_fcA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_exitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_sysA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_strA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_mkA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_strerrA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_drvA.     (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require Drv_ifaceA F_target_runA F_main_AA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require DrvKitA__A3D. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require F_module_dtorA ExitAllA ExitHeapA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require ComposeA__A3D. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require FakeInstA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require MainEntryA__A3D. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require GStatKit DrvStatA DrvLawsA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require StaticsA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require TlsObjA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require GioaInstA SetShadowInstA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require HarnCompA AtxCompA AtxIndepA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require StdioLawsInstA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require StdioInitA__A3D. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require StdioInstA StdioExitInstA StrerrCompA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.F_target_runA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.F_main_AA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.ExitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.F_module_dtorA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ExitAllA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ExitHeapA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ComposeA__A3D.ExitInitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.FakeInstA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ComposeA__A3D.ComposeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.MainEntryA__A3D.MainEntryA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.GStatKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvStatA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvLawsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ComposeA__A3D.DrvStatInitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.StaticsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.MainEntryA__A3D.StaticsInitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.TlsObjA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.MainEntryA__A3D.TlsObjInitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.GioaInstA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.SetShadowInstA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ComposeA__A3D.GioaMainA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.HarnCompA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.AtxCompA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.AtxIndepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.MainEntryA__A3D.HarnInitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.StdioLawsInstA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.StdioInitA__A3D.StdioInitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.StdioInstA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.StdioExitInstA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.StrerrCompA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.StdioInitA__A3D.StrerrInitA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section Run.
  (* [comment removed for export] *)
  Variables (en : ExecEntry) (inp : ProcInput) (lim : Z) (w : bool) (V : nat -> Z) (m : amem) (ms : machine_state) (mo : Model).
  Hypothesis AM : amain_open en inp lim w V m ms mo.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP.
  Hypothesis HTLS : tls_at V.
  Variables (U : list (list Z)) (lz : list (word * word)) (AL : word -> Prop).
  Hypothesis LU : (length U <= 4096)%nat.
  Hypothesis FU : Forall (fun u => (length u <= 254)%nat) U.
  Hypothesis A0I : forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> AL p.
  Hypothesis ASH0 : forall p : word, bv_unsigned p mod 4096 = 0 ->
     shad (al_space_beg (mkALayout (LV V) w U)) <= bv_unsigned p < shad (al_space_beg (mkALayout (LV V) w U)) + 17179869184 -> AL p.
  Hypothesis VI : valid_input inp.
  Hypothesis VSP : valid_sp (en_sp en).
  Hypothesis FITS : entry_stack_fits (en_sp en) (in_argv inp) (in_envp inp).

  (* [comment removed for export] *)
  Variable CI : list (Z * Z).
  Hypothesis CIB : ci_okb CI = true.
  Hypothesis CI_RS : exists iv, In iv CI /\ fst iv <= READ_STAGE /\ READ_STAGE + 65537 <= snd iv.
  Hypothesis CI_EXIT : Forall (fun k => exists iv, In iv CI /\ fst iv <= fst k /\ snd k <= snd iv) EXIT_CI_KEEP.
  Hypothesis CI_HARN : exists iv, In iv CI /\ fst iv <= OUTFILE_ADDR /\ OUTFILE_ADDR + 8 <= snd iv.
  Hypothesis CI_ATX : Forall (fun k => exists iv, In iv CI /\ fst iv <= fst k /\ snd k <= snd iv) ATX_DOM.       (* [comment removed for export] *)
  Hypothesis CI_ST1 : exists iv, In iv CI /\ fst iv <= 0xa9ab0 /\ 0xa9d80 <= snd iv.             (* [comment removed for export] *)
  Hypothesis CI_ST2 : exists iv, In iv CI /\ fst iv <= 0x601ca8 /\ 0x6024d0 <= snd iv.
  Hypothesis CI_ENV : Forall (fun k => exists iv, In iv CI /\ fst iv <= fst k /\ snd k <= snd iv) STDIO_ENV_CELLS.   (* [comment removed for export] *)
  Hypothesis CI_LOC : exists iv, In iv CI /\ fst iv <= 0x6018a8 /\ 0x6018b0 <= snd iv.            (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation TP := TP_real.
  Let HCPC : tp_cpc TP = OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_acalloc_iseg.ACALLOC_PC. Proof. reflexivity. Qed.
  Let HRPC : tp_rpc TP = OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARealloc_iface.AREALLOC_PC. Proof. reflexivity. Qed.
  Variable stk : stack_site -> Z.
  Hypothesis SITE_RS : stk SiteReadStage = READ_STAGE.
  Hypothesis U_DRV : incl drv_traces U.
  Hypothesis U_FUZZ : incl fuzz_traces U.

  Notation USP := (bv_unsigned (en_sp en)).
  Notation SBK := (build_stack_bytes a_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)).
  Notation L := (mkALayout (LV V) w U).
  Notation LO := (ATOP + 4096).
  Notation RNG := (fp_ok lz AL).
  Notation AI := (AI_of CI CIB).
  Notation AF := (afake_inst CI CIB).
  #[local] Notation cblk := (@cblock aptr).
  #[local] Notation PS := (PState aheap aptr).
  Notation s0 := (mkPS (aheap_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V)) (@libc_init aptr) None 6165744).

  Let HU : (length U <= Z.to_nat AUMAX)%nat. Proof. unfold AUMAX. lia. Qed.
  Let BTLS := inst_block_tls CI CIB.

  Let BAHM := inst_block_ahm CI CIB.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Cb.
  Variable cb : Z.
  Definition cs4 : list gcomp := [files_comp; env_comp; strerr_comp].   (* [comment removed for export] *)
  Definition cs_mine : list gcomp :=
    [args_comp USP (Z.of_nat (length SBK) - 16); unp_comp; exitci_comp; globals_comp; stdinp_comp; stacksh_comp; tlsobj_comp].
  Definition cs_mineX : list gcomp := atx_comp cb :: cs_mine.
  Definition cs_all : list gcomp := cs_mineX ++ harn_comp :: cs4.
  Notation GIOA := (GIOA_real AI (GSTAT_of cs_all)).
  #[using="CI_ST1 CI_ST2 CI_ENV CI_LOC BTLS BAHM"] Lemma CSOK4 : Forall (gcomp_ok AI) cs4.
  Proof. unfold cs4. apply Forall_cons; [exact (files_ok AI AF CI_ST1 CI_ST2)| apply Forall_cons; [exact (env_ok AI AF CI_ENV BAHM)| apply Forall_cons; [exact (strerr_ok AI AF BTLS CI_LOC)| apply Forall_nil]]]. Qed.
  #[using="Type"] Lemma INDEP4 : Forall harn_indep cs4.
  Proof. unfold cs4. apply Forall_cons; [exact files_harn_indep| apply Forall_cons; [exact env_harn_indep| apply Forall_cons; [exact strerr_harn_indep| apply Forall_nil]]]. Qed.
  #[using="en inp lim ms mo AM HAT HTLS LU A0I HU"] Lemma INIT4 : gconj cs4 L RNG s0 [] m.
  Proof.
    unfold cs4. cbn [gconj gc_P files_comp env_comp strerr_comp].
    split; [exact (files_init _ _ _ _ _ _ _ _ AM U HU L RNG s0 eq_refl)|].
    split; [exact (env_init _ _ _ _ _ _ _ _ AM HAT HTLS U lz AL HU A0I L s0 [] eq_refl)|]. split; [| exact I].
    exact (strerr_init _ _ _ _ _ _ _ _ AM HTLS U HU L RNG s0 []).
  Qed.

  #[using="lim w V m ms mo AM HAT U LU VSP FITS HU"] Lemma args_geo : ATOP + 64 <= USP /\ 16 <= Z.of_nat (length SBK) /\ USP + Z.of_nat (length SBK) <= 2^47.
  Proof.
    pose proof (me_atop _ _ _ _ _ _ _ _ AM HAT U HU) as A. (nd_pre (me_geometry _ _ _ _ _ _ _ _ AM HAT U HU VSP FITS) 6%nat; intros _ _ _ _ _ B47; nd_post).
    pose proof (raw_len_nonneg a_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)) as RN.
    pose proof (build_stack_bytes_length a_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)) as BL.
    split; [lia|]. split; [rewrite BL; unfold raw_len in *; lia| exact B47].
  Qed.

  #[using="lim w V m ms mo AM HAT U LU VSP FITS CI_EXIT CI_ATX HU BTLS"] Lemma cs_mine_ok : Forall (gcomp_ok AI) cs_mine.
  Proof.
    (nd_pre args_geo 3%nat; intros G1 G2 G3; nd_post). unfold cs_mine.
    apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]]]]].
    - apply (args_ok AI AF); [exact G1| lia].
    - apply (unp_ok AI AF).
    - apply (exitci_ok AI AF BTLS CI_EXIT).
    - apply (globals_ok AI AF).
    - apply (stdinp_ok AI AF).
    - apply (stacksh_ok AI AF).
    - apply (tlsobj_ok AI AF BTLS).
  Qed.
  #[using="lim w V m ms mo AM HAT U LU VSP FITS CI_EXIT CI_ATX HU BTLS"] Lemma cs_mineX_ok : Forall (gcomp_ok AI) cs_mineX.
  Proof. unfold cs_mineX. apply Forall_cons; [exact (atx_ok AI AF CI_ATX cb)| exact cs_mine_ok]. Qed.
  #[using="lim w V m ms mo AM HAT U LU VSP FITS CI_EXIT CI_ATX CI_HARN CI_ST1 CI_ST2 CI_ENV CI_LOC HU BTLS BAHM"] Lemma cs_all_ok : Forall (gcomp_ok AI) cs_all.
  Proof. unfold cs_all. apply Forall_app. split; [exact cs_mineX_ok|]. apply Forall_cons; [exact (harn_ok AI AF CI_HARN)| exact CSOK4]. Qed.

  (* [comment removed for export] *)
  #[using="lim w V m ms mo AM HAT U LU VSP FITS HU"] Lemma cs_mine_indep : Forall harn_indep cs_mine.
  Proof.
    (nd_pre args_geo 3%nat; intros G1 G2 G3; nd_post). pose proof atop_range as AR.
    unfold cs_mine.
    apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]]]]];
      (split; [intros L1 R1 s1 FB1 m1 o HPc; exact HPc|]); intros L1 s1 FB1 a Da R; unfold OUTFILE_ADDR in R; cbn [gc_dom args_comp unp_comp exitci_comp globals_comp stdinp_comp stacksh_comp tlsobj_comp] in Da.
    - destruct (args_dom_band USP (Z.of_nat (length SBK) - 16) G1 ltac:(lia) a Da) as [B _]. clear - B R AR. Z.div_mod_to_equations. lia.
    - unfold unp_dom, AIMSH_LO in Da. lia.
    - unfold exitci_dom, exit_dom in Da. destruct Da as [D|[(k & Hk & Rk)|D]].
      + pose proof ATPv_img as TI. lia.
      + unfold EXIT_CI_KEEP in Hk. repeat (destruct Hk as [<-|Hk]; [cbn [fst snd] in Rk; lia|]). destruct Hk.
      + unfold AIMSH_LO in D. lia.
    - unfold win_dom, AIMSH_LO in Da. lia.
    - unfold win_dom, AIMSH_LO in Da. lia.
    - destruct Da as [Da D47]. destruct (stacksh_band L1 a Da D47) as [B _]. clear - B R AR. Z.div_mod_to_equations. lia.
    - destruct (tlsobj_band a Da) as (B & _). lia.
  Qed.

  #[using="lim w V m ms mo AM HAT U LU VSP FITS HU"] Lemma cs_mineX_indep : Forall harn_indep cs_mineX.
  Proof. unfold cs_mineX. apply Forall_cons; [exact (atx_harn_indep cb)| exact cs_mine_indep]. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma in_mine : forall c, In c cs_mine -> In c cs_all.
  Proof. intros c Hc. unfold cs_all, cs_mineX. apply in_or_app. left. right. exact Hc. Qed.
  Definition GL_run : gia_laws (asan_fo site_frameA) GIOA fflagA_real :=
    GL_inst CI CIB cs_all cs_all_ok
      (in_mine globals_comp ltac:(unfold cs_mine; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ])) (in_mine stdinp_comp ltac:(unfold cs_mine; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ]))
      (in_mine stacksh_comp ltac:(unfold cs_mine; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ])) (in_mine tlsobj_comp ltac:(unfold cs_mine; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ])).
  Definition GH_run : gia_harn_laws GIOA :=
    gia_harn_laws_real AI CI_HARN cs_mineX cs4
      (proj2 (Forall_app _ _ _) (conj cs_mineX_ok CSOK4)) (proj2 (Forall_app _ _ _) (conj cs_mineX_indep INDEP4)).

  Definition GD_run : gia_drv_laws GIOA USP SBK :=
    GD_inst CI CIB cs_all cs_all_ok USP SBK (proj1 args_geo) (proj1 (proj2 args_geo)) (proj2 (proj2 args_geo)) CI_RS
      (in_mine (args_comp USP (Z.of_nat (length SBK) - 16)) ltac:(unfold cs_mine; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ])) (in_mine unp_comp ltac:(unfold cs_mine; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ])).
  Definition MALLOC_run := malloc_inst CI CIB cs_all cs_all_ok.
  Definition FREE_run := free_inst CI CIB cs_all cs_all_ok.
  Definition FREENULL_run := free_null_inst CI CIB cs_all cs_all_ok.
  Definition CALLOC_run := calloc_inst CI CIB cs_all cs_all_ok TP HCPC.
  Definition REALLOC_run := realloc_inst CI CIB cs_all cs_all_ok TP HRPC.
  Definition MALLOC_D_run := malloc_d_inst CI CIB cs_all cs_all_ok.
  Definition FREE_D_run := free_d_inst CI CIB cs_all cs_all_ok.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="lim w V m ms mo AM HAT U LU VSP FITS CI_EXIT CI_ATX CI_HARN CI_ST1 CI_ST2 CI_ENV CI_LOC HU BTLS BAHM"] Lemma GSL : gia_stdio_laws GIOA.
  Proof.
    (nd_pre args_geo 3%nat; intros G1 G2 G3; nd_post).
    assert (OKS : Forall (gcomp_ok AI) ((cs_mineX ++ [harn_comp]) ++ [env_comp; strerr_comp])).
    { apply Forall_app. split; [apply Forall_app; split; [exact cs_mineX_ok| apply Forall_cons; [exact (harn_ok AI AF CI_HARN)| apply Forall_nil]]|].
      apply Forall_cons; [exact (env_ok AI AF CI_ENV BAHM)| apply Forall_cons; [exact (strerr_ok AI AF BTLS CI_LOC)| apply Forall_nil]]. }
    assert (INS : Forall (stdio_indep AI) ((cs_mineX ++ [harn_comp]) ++ [env_comp; strerr_comp])).
    { apply Forall_app. split; [apply Forall_app; split|].
      - unfold cs_mineX, cs_mine. apply Forall_cons; [exact (atx_stdio_indep AI cb)|].
        apply Forall_cons; [apply (args_indep AI); lia|]. apply Forall_cons; [exact (unp_indep AI)|]. apply Forall_cons; [exact (exitci_indep AI BTLS)|].
        apply Forall_cons; [exact (globals_indep AI)|]. apply Forall_cons; [exact (stdinp_indep AI)|]. apply Forall_cons; [exact (stacksh_indep AI)|].
        apply Forall_cons; [exact (tlsobj_indep AI)| apply Forall_nil].
      - apply Forall_cons; [exact (harn_stdio_indep AI)| apply Forall_nil].
      - apply Forall_cons; [exact (env_indep AI BAHM)| apply Forall_cons; [exact (strerr_stdio_indep AI BTLS)| apply Forall_nil]]. }
    exact (gia_stdio_laws_real AI AF BTLS CI_ST1 CI_ST2 BAHM (cs_mineX ++ [harn_comp]) [env_comp; strerr_comp] OKS INS
             ltac:(apply in_or_app; right; left; reflexivity)
             ltac:(apply in_or_app; left; apply in_or_app; left; unfold cs_mineX, cs_mine; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ])
             ltac:(apply in_or_app; left; apply in_or_app; left; unfold cs_mineX, cs_mine; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ])
             (inst_ssc CI CIB)).
  Qed.
  (* [comment removed for export] *)
  Definition VPR : vprintf_d_stmt_o GIOA := vprintf_d_proofA (asan_fo site_frameA) GIOA fflagA_real GL_run GSL.
  Definition EPR_USAGE : eprintf_s_stmt_o GIOA FMT_USAGE 16 pieces_usage := eprintf_usage_proofA (asan_fo site_frameA) GIOA fflagA_real GL_run GSL.
  Definition EPR_OPEN : eprintf_s_stmt_o GIOA FMT_CANNOT_OPEN 20 pieces_cannot_open := eprintf_cannot_open_proofA (asan_fo site_frameA) GIOA fflagA_real GL_run GSL.
  Definition EPR_READ : eprintf_s_stmt_o GIOA FMT_READ_ERROR 22 pieces_read_error := eprintf_read_error_proofA (asan_fo site_frameA) GIOA fflagA_real GL_run GSL.
  Definition EPR_BIG : eprintf_i_stmt_o GIOA FMT_TOO_BIG 32 0x4000000 pieces_too_big := eprintf_too_big_proofA (asan_fo site_frameA) GIOA fflagA_real GL_run GSL.
  Definition EFW : efwrite_stmt_o GIOA := efwrite_proofA (asan_fo site_frameA) GIOA fflagA_real GL_run GSL.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="Type"] Lemma cs_all_strerr : cs_all = (cs_mineX ++ [harn_comp; files_comp; env_comp]) ++ strerr_comp :: [].
  Proof. unfold cs_all, cs4. rewrite <- app_assoc. reflexivity. Qed.
  #[using="lim w V m ms mo AM HAT U LU VSP FITS CI_EXIT CI_ATX CI_HARN CI_ST1 CI_ST2 CI_ENV CI_LOC HU BTLS BAHM"] Lemma GSE_run : gia_strerr_laws GIOA.
  Proof.
    (nd_pre args_geo 3%nat; intros G1 G2 G3; nd_post).
    assert (OKS : Forall (gcomp_ok AI) ((cs_mineX ++ [harn_comp; files_comp; env_comp]) ++ [])).
    { rewrite app_nil_r. apply Forall_app. split; [exact cs_mineX_ok|].
      apply Forall_cons; [exact (harn_ok AI AF CI_HARN)|]. apply Forall_cons; [exact (files_ok AI AF CI_ST1 CI_ST2)|].
      apply Forall_cons; [exact (env_ok AI AF CI_ENV BAHM)| apply Forall_nil]. }
    assert (TIS : Forall tlsbuf_indep ((cs_mineX ++ [harn_comp; files_comp; env_comp]) ++ [])).
    { rewrite app_nil_r. apply Forall_app. split.
      - unfold cs_mineX, cs_mine. apply Forall_cons; [exact (atx_tlsbuf cb)|].
        apply Forall_cons; [apply args_tlsbuf; lia|]. apply Forall_cons; [exact unp_tlsbuf|]. apply Forall_cons; [exact exitci_tlsbuf|].
        apply Forall_cons; [exact globals_tlsbuf|]. apply Forall_cons; [exact stdinp_tlsbuf|]. apply Forall_cons; [exact stacksh_tlsbuf|].
        apply Forall_cons; [exact tlsobj_tlsbuf| apply Forall_nil].
      - apply Forall_cons; [exact harn_tlsbuf|]. apply Forall_cons; [exact files_tlsbuf|]. apply Forall_cons; [exact env_tlsbuf| apply Forall_nil]. }
    pose proof cs_all_strerr as ECS.
    constructor.
    - intros L1 RNG1 s CL FB FL m1 G. rewrite ECS in G.
      exact (ge_cells_real AI (inst_lsan CI CIB) _ _ _ _ _ _ _ _ _ G).
    - intros L1 RNG1 s CL FB FL m1 m' W SP new G MU WM FW HSP LS NEW. split.
      + pose proof G as G0. rewrite ECS in G0. rewrite ECS.
        exact (strerr_frame_real AI _ _ OKS TIS _ _ _ _ _ _ _ _ W SP new G0 MU WM FW HSP LS NEW).
      + pose proof G as (AH & _).
        eapply agrees_on_weaken; [exact (gs_keeps _ GSL _ _ _ _ _ _ _ _ W [(ATP + 16, ATP + PCAP_TLS_ERRBUF + 256)] SP G MU WM
                                           ltac:(eapply Forall_impl; [| exact FW]; intros iv K; left; exact K) HSP)|].
        intros a KA. split; [exact KA|]. cbn [outside]. split; [| exact I]. intros Ra.
        apply (tls_not_client AI AF BTLS _ _ _ CL FB FL m1 a AH); [unfold PCAP_TLS_ERRBUF in Ra; lia|].
        unfold client_reg. destruct KA as [K|K]; [left; lia| right; exact K].
  Qed.

  #[using="Type"] Lemma EQB_run : forall p q : aptr, ho_eqb asan_ops p q = true <-> p = q.
  Proof. intros p q. exact (N.eqb_eq p q). Qed.
  (* [comment removed for export] *)
  Definition FOPEN : fopen_stmt_o asan_ops GIOA TP :=
    fopen_o_proofA asan_ops (asan_fo site_frameA) GIOA TP fflagA_real GL_run GSL (gr_addr AI _) EQB_run MALLOC_run TP_real_fopen.
  (* [comment removed for export] *)
  Definition REMOVE : remove_stmt_o GIOA := remove_o_proofA (asan_fo site_frameA) GIOA fflagA_real GL_run GSL.
  Definition UNLINK : unlink_stmt_o GIOA := unlink_o_proofA (asan_fo site_frameA) GIOA fflagA_real GL_run GSL.
  Definition CLOSE : close_stmt_o GIOA := close_o_proofA (asan_fo site_frameA) GIOA fflagA_real GL_run GSL.
  (* [comment removed for export] *)
  Definition FCLOSE : fclose_stmt_o asan_ops GIOA TP :=
    fclose_o_proofA asan_ops (asan_fo site_frameA) GIOA TP fflagA_real GL_run GSL (gr_addr AI _) EQB_run FREE_run FREENULL_run TP_real_fclose.
  Let GSP := inst_GS_pres CI CIB cs_all cs_all_ok.
  #[using="lim w V m ms mo AM HAT U LU VSP FITS CI_EXIT CI_ATX CI_HARN CI_ST1 CI_ST2 CI_ENV CI_LOC HCPC HRPC HU BTLS BAHM GSP"] Lemma FUZZ : fuzz_one_stmt asan_ops (asan_fo site_frameA) stk GIOA TP.
  Proof.
    (* [comment removed for export] *)
    eapply (fuzz_one_closedA asan_ops (asan_fo site_frameA) stk GIOA TP fflagA_real);
      lazymatch goal with
      | |- gia_laws _ _ _ => exact GL_run
      | |- gia_harn_laws _ => exact GH_run
      | |- gia_addr_law _ _ => exact (gr_addr AI _)
      | |- gia_perm_law _ => exact (gr_perm AI _)
      | |- gia_got_law _ => exact (gr_got AI _)
      | |- OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.LeafA.fo_leaf_laws _ => exact (asan_fo_leaf_laws site_frameA)
      | |- fenter_stmt_o _ _ _ 0 _ => exact (fenter_real AI AF _ GSP 0 STACK_MALLOC_0 (or_introl (conj eq_refl eq_refl)))
      | |- fenter_stmt_o _ _ _ 1 _ => exact (fenter_real AI AF _ GSP 1 STACK_MALLOC_1 (or_intror (conj eq_refl eq_refl)))
      | |- fret_inline_law _ _ _ => exact (fret_real AI AF _ GSP)
      | |- fenter7_stmt_o _ _ _ => exact (fenter7_real AI AF _ GSP)
      | |- ffree7_stmt_o _ _ _ => exact (ffree7_real AI AF _ GSP)
      | |- set_shadow_stmt _ 0xf8 => exact set_shadow_f8_inst
      | |- set_shadow_stmt _ 0x00 => exact set_shadow_00_inst
      | |- malloc_stmt_o _ _ => exact MALLOC_run
      | |- calloc_stmt_o _ _ _ => exact CALLOC_run
      | |- realloc_stmt_o _ _ _ => exact REALLOC_run
      | |- free_stmt_o _ _ => exact FREE_run
      | |- free_null_stmt_o _ => exact FREENULL_run
      | |- fopen_stmt_o _ _ _ => exact FOPEN
      | |- fclose_stmt_o _ _ _ => exact FCLOSE
      | |- fread_stmt_o _ _ => exact (fread_o_proofA asan_ops (asan_fo site_frameA) GIOA fflagA_real GL_run GSL (gr_addr AI _) EQB_run)
      | |- ferror_stmt_o _ _ => exact (ferror_o_proofA asan_ops (asan_fo site_frameA) GIOA fflagA_real GL_run GSL EQB_run)
      | |- fileno_stmt_o _ _ => exact (fileno_o_proofA asan_ops (asan_fo site_frameA) GIOA fflagA_real GL_run GSL EQB_run)
      | |- fwrite_stmt_o _ _ => exact (fwrite_o_proofA asan_ops (asan_fo site_frameA) GIOA fflagA_real GL_run GSL EQB_run)
      | |- remove_stmt_o _ => exact REMOVE
      | |- unlink_stmt_o _ => exact UNLINK
      | |- close_stmt_o _ => exact CLOSE
      | |- mkstemp_stmt_o _ => exact (mkstemp_o_proofA (asan_fo site_frameA) GIOA fflagA_real GL_run GSL)
      | |- printf_d_stmt_o _ FMT_FAILED_REMOVE _ => exact (printf_failed_remove_proofA (asan_fo site_frameA) GIOA fflagA_real GL_run GSL)
      | |- printf_d_stmt_o _ FMT_FAILED_OPEN _ => exact (printf_failed_open_proofA (asan_fo site_frameA) GIOA fflagA_real GL_run GSL)
      | |- fprintf_dd_stmt_o _ _ _ _ => exact (fprintf_packet_length_proofA asan_ops (asan_fo site_frameA) GIOA fflagA_real GL_run GSL EQB_run)
      | |- fprintf_s_stmt_o _ _ _ _ => exact (fprintf_couldnt_open_proofA asan_ops (asan_fo site_frameA) GIOA fflagA_real GL_run GSL EQB_run)
      | |- snprintf_spec_stmt _ => exact (snprintf_proofA (asan_fo site_frameA) GIOA fflagA_real GL_run GSL)
      | |- vsnprintf_spec_stmt _ => exact (vsnprintf_proofA (asan_fo site_frameA) GIOA fflagA_real GL_run GSL)
      | |- strlen_stmt _ => exact (strlen_proofA (asan_fo site_frameA) GIOA fflagA_real GL_run GSL)
      | |- strerror_r_stmt _ => exact (strerror_r_proofA (asan_fo site_frameA) GIOA fflagA_real GL_run GSL GSE_run)
      | |- ~ (_ <= _ < _) => unfold TP_real, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesUnivA.ACALLOC_PC, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesUnivA.AREALLOC_PC, ACLIENT_LO, ACLIENT_HI; cbn [tp_cpc tp_rpc]; lia
      | |- forall p q, ho_eqb _ p q = true <-> p = q => exact EQB_run
      end.
  Qed.
  End Cb.

  (* [comment removed for export] *)
  Notation GIOA := (GIOA_real AI (GSTAT_of (cs_all 0))).
  Notation GIOA1 := (GIOA_real AI (GSTAT_of (cs_all 1))).
  (* [comment removed for export] *)
  #[using="lim ms mo AM HAT HTLS LU A0I VSP FITS HU"] Lemma cs_all_init : gconj (cs_all 0) L RNG s0 [] m.
  Proof.
    pose proof (me_facts _ _ _ _ _ _ _ _ AM) as [HM HP].
    unfold cs_all. apply (proj2 (gconj_app _ _ _ _ _ _ _)). split.
    - unfold cs_mineX, cs_mine. cbn [gconj gc_P atx_comp args_comp unp_comp exitci_comp globals_comp stdinp_comp stacksh_comp tlsobj_comp].
      split; [exists false; exact (atx_init V m HM)|].
      split; [exact (args_init _ _ _ _ _ _ _ _ AM HAT HTLS U lz AL HU A0I VSP FITS L s0 [])|].
      split; [exact (unp_init _ _ _ _ _ _ _ _ AM U HU L RNG s0 [])|].
      split; [exists (V 44%nat); exact (exit_ci_init V m HM HP HTLS)|].
      split; [exact (globals_init _ _ _ _ _ _ _ _ AM U HU L RNG s0 [])|].
      split; [exact (stdinp_init _ _ _ _ _ _ _ _ AM U HU L RNG s0 [])|].
      split; [exact (stacksh_init _ _ _ _ _ _ _ _ AM HAT HTLS U lz AL HU A0I s0 [])|].
      split; [exact (tlsobj_init _ _ _ _ _ _ _ _ AM HTLS U lz AL HU A0I L s0 [])| exact I].
    - cbn [gconj]. split; [| exact INIT4]. cbn [gc_P harn_comp]. apply (harn_init _ _ _ _ _ _ _ _ AM). reflexivity.
  Qed.


  (* [comment removed for export] *)
  #[using="lim w V m ms mo AM HAT U LU VSP FITS CI_RS CI_EXIT CI_ATX CI_HARN CI_ST1 CI_ST2 CI_ENV CI_LOC HU BTLS BAHM"] Lemma atx_rest_ok : Forall (gcomp_ok AI) ([] ++ (cs_mine ++ harn_comp :: cs4)).
  Proof. cbn [app]. apply Forall_app. split; [exact cs_mine_ok|]. apply Forall_cons; [exact (harn_ok AI AF CI_HARN)| exact CSOK4]. Qed.
  #[using="lim w V m ms mo AM HAT U LU VSP FITS HU BTLS"] Lemma atx_rest_indep : Forall atx_indep ([] ++ (cs_mine ++ harn_comp :: cs4)).
  Proof.
    (nd_pre args_geo 3%nat; intros G1 G2 G3; nd_post). cbn [app]. apply Forall_app. split.
    - unfold cs_mine.
      apply Forall_cons; [apply args_atx; lia|]. apply Forall_cons; [exact unp_atx|]. apply Forall_cons; [exact exitci_atx|].
      apply Forall_cons; [exact globals_atx|]. apply Forall_cons; [exact stdinp_atx|]. apply Forall_cons; [exact stacksh_atx|].
      apply Forall_cons; [exact tlsobj_atx| apply Forall_nil].
    - apply Forall_cons; [exact harn_atx|]. unfold cs4.
      apply Forall_cons; [exact files_atx|]. apply Forall_cons; [exact env_atx|]. apply Forall_cons; [exact strerr_atx| apply Forall_nil].
  Qed.
  #[using="lim w V m ms mo AM HAT U LU VSP FITS CI_RS CI_EXIT CI_ATX CI_HARN CI_ST1 CI_ST2 CI_ENV CI_LOC HU BTLS BAHM"] Lemma GA_run : gia_atx_laws GIOA.
  Proof. exact (gia_atx_laws_real AI AF CI_ATX CI_RS BTLS [] (cs_mine ++ harn_comp :: cs4) atx_rest_ok atx_rest_indep). Qed.
  #[using="lim w V m ms mo AM HAT U LU VSP FITS CI_RS CI_EXIT CI_ATX CI_HARN CI_ST1 CI_ST2 CI_ENV CI_LOC HU BTLS BAHM"] Lemma GCB_run : gia_cb_laws GIOA GIOA1.
  Proof. exact (gia_cb_laws_real AI AF CI_ATX CI_RS BTLS [] (cs_mine ++ harn_comp :: cs4) atx_rest_ok atx_rest_indep). Qed.

  #[using="U_FUZZ"] Lemma TRF : traces_fuzz_one TP L RA_FUZZ [].
  Proof. apply (traces_fuzz_one_univ L). intros tr Htr. cbn [al_U]. exact (U_FUZZ tr Htr). Qed.

  (* [comment removed for export] *)
  Definition STDIO_EXIT_SXA : stdio_exit_stmtA (@s_stdio_exit aheap aptr) (SXA (H := aheap) (hptr := aptr)) 160 := stdio_exit_proofA.   (* [comment removed for export] *)
  Notation SX := (SX_real (H := aheap) (hptr := aptr)).
  Definition stdio_exit_frame : Z := 160.
  #[using="rc U LU HU"] Lemma stdio_exit_frame_nonneg : 0 <= stdio_exit_frame.
  Proof. unfold stdio_exit_frame. lia. Qed.
  #[using="Type"] Lemma stdio_exit_fits : 48 + MDTOR_DEPTH + stdio_exit_frame <= MAIN_STACK.
  Proof. vm_compute. discriminate. Qed.
  #[using="Type"] Lemma SX_frame : forall (s : PS) RNG1 sp (m1 m' : mem), SX s RNG1 m1 -> (ATOP + 4096 <= sp - 48 - MDTOR_DEPTH)%Z ->
    munch (AEXIT_W1 sp ++ MDTOR_W) m1 m' -> wmono asegs m1 m' -> SX s RNG1 m'.
  Proof. exact SX_real_frame. Qed.
  #[using="Type"] Lemma STDIO_EXIT : stdio_exit_stmtA (@s_stdio_exit aheap aptr) SX stdio_exit_frame.
  Proof. exact (stdio_exit_stmtA_anti _ _ _ _ SX_real_sxa STDIO_EXIT_SXA). Qed.
  #[using="lim m ms mo AM HAT LU VSP FITS CI_EXIT CI_ATX CI_HARN CI_ST1 CI_ST2 CI_ENV CI_LOC HU BTLS BAHM"] Lemma SX_of_gioa : forall RNG1 (s : PS) CL FB (m1 : mem), GIOA L RNG1 s CL FB [] m1 -> SX s RNG1 m1.
  Proof. intros RNG1 s CL FB m1 G. exact (SX_real_of_gioa (asan_fo site_frameA) GIOA fflagA_real (GL_run 0) (GSL 0) L RNG1 s CL FB [] m1 G). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="lim w V m ms mo AM HAT U LU VSP FITS CI_RS CI_EXIT CI_ATX CI_HARN CI_ST1 CI_ST2 CI_ENV CI_LOC HCPC HRPC HU BTLS BAHM"] Lemma TRUN_run : target_run_stmt_o asan_ops (asan_fo site_frameA) stk GIOA TP.
  Proof.
    (* [comment removed for export] *)
    exact (target_run_proof asan_ops (asan_fo site_frameA) stk GIOA TP fflagA_real USP SBK GIOA1 (GL_run 0) (GL_run 1) (GD_run 0) GA_run GCB_run
             (MALLOC_run 0) (FREE_run 0) (FREENULL_run 0) (FUZZ 1) (VPR 0)).
  Qed.

  #[using="lim m ms mo AM HAT LU VSP FITS CI_EXIT CI_ATX CI_HARN CI_ST1 CI_ST2 CI_ENV CI_LOC HU BTLS BAHM"] Lemma GX_run : forall RNG1 s CL FB m1, GIOA L RNG1 s CL FB [] m1 ->
    (exists t, exit_ci t m1) /\ (exists (Hh : aholes) st LB, AHEAP_P Hh L RNG1 st LB m1) /\ SX s RNG1 m1.
  Proof.
    intros RNG1 s CL FB m1 G. (pose proof G as ndP__; nd_pre ndP__ 7%nat; intros AH _ _ _ _ _ (_ & GC); nd_post).
    split; [exact (gconj_In _ _ _ _ _ _ _ GC (in_mine 0 exitci_comp ltac:(unfold cs_mine; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ])))|].
    split; [exists AHI, (ah_st (ps_heap s)), (LBof CL FB []); exact AH| exact (SX_of_gioa _ _ _ _ _ G)].
  Qed.

  #[using="U_DRV"] Lemma TRD_run : traces_drv L.
  Proof. intros tr Htr. cbn [al_U]. exact (U_DRV tr Htr). Qed.

  #[using="tlsI en lim w m mo AM HAT HTLS U LU FU A0I ASH0 VI VSP FITS CI CIB CI_RS CI_EXIT CI_ATX CI_HARN CI_ST1 CI_ST2 CI_ENV CI_LOC HCPC HRPC SITE_RS U_DRV U_FUZZ HU BTLS BAHM"] Theorem impl_run : forall Q, implMG RNG (prog_main asan_ops (asan_fo site_frameA) stk (argv_Z (in_argv inp))) s0 Q ms.
  Proof.
    intros Q. (nd_pre (me_geometry _ _ _ _ _ _ _ _ AM HAT U HU VSP FITS) 6%nat; intros M1 M2 M3 M4 M5 M6; nd_post).
    eapply (prog_main_impl asan_ops (asan_fo site_frameA) stk GIOA TP fflagA_real (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) L LO
              (GL_run 0) (GD_run 0) GA_run (MALLOC_D_run 0) (FREE_D_run 0) (EPR_USAGE 0) (EPR_OPEN 0) (EPR_READ 0) (EPR_BIG 0) (EFW 0) SITE_RS TRUN_run M1 M2 M3 M4 M5 M6 TRD_run TRF
              SX stdio_exit_frame stdio_exit_frame_nonneg stdio_exit_fits SX_frame STDIO_EXIT GX_run).
    eapply (main_entry_handoff _ _ _ _ _ _ _ _ AM HAT HTLS U lz AL HU A0I VI VSP FITS GIOA s0 []).
    exact (gioa_at_main _ _ _ _ _ _ _ _ AM HAT HTLS U lz AL LU FU A0I ASH0 CI CIB (cs_all 0) libc_init None 6165744 cs_all_init).
  Qed.
End Run.
End CANSEC1.

(* [comment removed for export] *)

From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require MainFactsAsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS.MainFactsAsan. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.KnTrans__AS.MainLedgerAsan.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.ProgT.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.ACalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARealloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_acalloc_iseg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.AInstance.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.AInstanceM.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AInstanceF__A3W.AInstanceF.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AInstanceF__A3W.AInstanceC.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHandoffDefs.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.AHandoffKit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.LeafA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_gotA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaReal.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GioaAlloc.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_next_ex_allA__A3P.GioaFake.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.FoLeafReal.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesUnivA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_all_closedA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioLawsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioCompA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_pfA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_snA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_foA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_fcA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_exitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_sysA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_strA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_mkA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_strerrA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_drvA.TwB.     (* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.Drv_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.F_target_runA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.F_main_AA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.ExitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.F_module_dtorA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ExitAllA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ExitHeapA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ComposeA__A3D.ExitInitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.FakeInstA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ComposeA__A3D.ComposeA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.MainEntryA__A3D.MainEntryA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.GStatKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvStatA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvLawsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ComposeA__A3D.DrvStatInitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.StaticsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.MainEntryA__A3D.StaticsInitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.TlsObjA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.MainEntryA__A3D.TlsObjInitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.GioaInstA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.SetShadowInstA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.ComposeA__A3D.GioaMainA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.HarnCompA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.MainEntryA__A3D.HarnInitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.StdioLawsInstA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.StdioInitA__A3D.StdioInitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.StdioInstA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.StdioExitInstA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.StrerrCompA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.StdioInitA__A3D.StrerrInitA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.AtxCompA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.AtxIndepA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.flia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section Run.
  (* [comment removed for export] *)
  Variables (en : ExecEntry) (inp : ProcInput) (lim : Z) (w : bool) (V : nat -> Z) (m : amem) (ms : machine_state) (mo : Model).
  Hypothesis AM : amain_open en inp lim w V m ms mo.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat - 8388608 = ATOP.
  Hypothesis HTLS : tls_at V.
  Variables (U : list (list Z)) (lz : list (word * word)) (AL : word -> Prop).
  Hypothesis LU : (length U <= 4096)%nat.
  Hypothesis FU : Forall (fun u => (length u <= 254)%nat) U.
  Hypothesis A0I : forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> AL p.
  Hypothesis ASH0 : forall p : word, bv_unsigned p mod 4096 = 0 ->
     shad (al_space_beg (mkALayout (LV V) w U)) <= bv_unsigned p < shad (al_space_beg (mkALayout (LV V) w U)) + 17179869184 -> AL p.
  Hypothesis VI : valid_input inp.
  Hypothesis VSP : valid_sp (en_sp en).
  Hypothesis FITS : entry_stack_fits (en_sp en) (in_argv inp) (in_envp inp).

  (* [comment removed for export] *)
  Variable CI : list (Z * Z).
  Hypothesis CIB : ci_okb CI = true.
  Hypothesis CI_RS : exists iv, In iv CI /\ fst iv <= READ_STAGE /\ READ_STAGE + 65537 <= snd iv.
  Hypothesis CI_EXIT : Forall (fun k => exists iv, In iv CI /\ fst iv <= fst k /\ snd k <= snd iv) EXIT_CI_KEEP.
  Hypothesis CI_HARN : exists iv, In iv CI /\ fst iv <= OUTFILE_ADDR /\ OUTFILE_ADDR + 8 <= snd iv.
  Hypothesis CI_ATX : Forall (fun k => exists iv, In iv CI /\ fst iv <= fst k /\ snd k <= snd iv) ATX_DOM.       (* [comment removed for export] *)
  Hypothesis CI_ST1 : exists iv, In iv CI /\ fst iv <= 0xa9e90 /\ 0xaa160 <= snd iv.             (* [comment removed for export] *)
  Hypothesis CI_ST2 : exists iv, In iv CI /\ fst iv <= 0x6020a8 /\ 0x6028d0 <= snd iv.
  Hypothesis CI_ENV : Forall (fun k => exists iv, In iv CI /\ fst iv <= fst k /\ snd k <= snd iv) STDIO_ENV_CELLS.   (* [comment removed for export] *)
  Hypothesis CI_LOC : exists iv, In iv CI /\ fst iv <= 0x601ca8 /\ 0x601cb0 <= snd iv.            (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation TP := TP_real.
  Let HCPC : tp_cpc TP = OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_acalloc_iseg.TwB.ACALLOC_PC. Proof. reflexivity. Qed.
  Let HRPC : tp_rpc TP = OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARealloc_iface.TwB.AREALLOC_PC. Proof. reflexivity. Qed.
  Variable stk : stack_site -> Z.
  Hypothesis SITE_RS : stk SiteReadStage = READ_STAGE.
  Hypothesis U_DRV : incl drv_traces U.
  Hypothesis U_FUZZ : incl fuzz_traces U.

  Notation USP := (bv_unsigned (en_sp en)).
  Notation SBK := (build_stack_bytes a_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)).
  Notation L := (mkALayout (LV V) w U).
  Notation LO := (ATOP + 4096).
  Notation RNG := (fp_ok lz AL).
  Notation AI := (AI_of CI CIB).
  Notation AF := (afake_inst CI CIB).
  #[local] Notation cblk := (@cblock aptr).
  #[local] Notation PS := (PState aheap aptr).
  Notation s0 := (mkPS (aheap_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V)) (@libc_init aptr) None 6166768).

  Let HU : (length U <= Z.to_nat AUMAX)%nat. Proof. unfold AUMAX. lia. Qed.
  Let BTLS := inst_block_tls CI CIB.

  Let BAHM := inst_block_ahm CI CIB.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Cb.
  Variable cb : Z.
  Definition cs4 : list gcomp := [files_comp; env_comp; strerr_comp].   (* [comment removed for export] *)
  Definition cs_mine : list gcomp :=
    [args_comp USP (Z.of_nat (length SBK) - 16); unp_comp; exitci_comp; globals_comp; stdinp_comp; stacksh_comp; tlsobj_comp].
  Definition cs_mineX : list gcomp := atx_comp cb :: cs_mine.
  Definition cs_all : list gcomp := cs_mineX ++ harn_comp :: cs4.
  Notation GIOA := (GIOA_real AI (GSTAT_of cs_all)).
  #[using="CI_ST1 CI_ST2 CI_ENV CI_LOC BTLS BAHM"] Lemma CSOK4 : Forall (gcomp_ok AI) cs4.
  Proof. unfold cs4. apply Forall_cons; [exact (files_ok AI AF CI_ST1 CI_ST2)| apply Forall_cons; [exact (env_ok AI AF CI_ENV BAHM)| apply Forall_cons; [exact (strerr_ok AI AF BTLS CI_LOC)| apply Forall_nil]]]. Qed.
  #[using="Type"] Lemma INDEP4 : Forall harn_indep cs4.
  Proof. unfold cs4. apply Forall_cons; [exact files_harn_indep| apply Forall_cons; [exact env_harn_indep| apply Forall_cons; [exact strerr_harn_indep| apply Forall_nil]]]. Qed.
  #[using="en inp lim ms mo AM HAT HTLS LU A0I HU"] Lemma INIT4 : gconj cs4 L RNG s0 [] m.
  Proof.
    unfold cs4. cbn [gconj gc_P files_comp env_comp strerr_comp].
    split; [exact (files_init _ _ _ _ _ _ _ _ AM U HU L RNG s0 eq_refl)|].
    split; [exact (env_init _ _ _ _ _ _ _ _ AM HAT HTLS U lz AL HU A0I L s0 [] eq_refl)|]. split; [| exact I].
    exact (strerr_init _ _ _ _ _ _ _ _ AM HTLS U HU L RNG s0 []).
  Qed.

  #[using="lim w V m ms mo AM HAT U LU VSP FITS HU"] Lemma args_geo : ATOP + 64 <= USP /\ 16 <= Z.of_nat (length SBK) /\ USP + Z.of_nat (length SBK) <= 2^47.
  Proof.
    pose proof (me_atop _ _ _ _ _ _ _ _ AM HAT U HU) as A. (nd_pre (me_geometry _ _ _ _ _ _ _ _ AM HAT U HU VSP FITS) 6%nat; intros _ _ _ _ _ B47; nd_post).
    pose proof (raw_len_nonneg a_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)) as RN.
    pose proof (build_stack_bytes_length a_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)) as BL.
    split; [lia|]. split; [rewrite BL; unfold raw_len in *; lia| exact B47].
  Qed.

  #[using="lim w V m ms mo AM HAT U LU VSP FITS CI_EXIT CI_ATX HU BTLS"] Lemma cs_mine_ok : Forall (gcomp_ok AI) cs_mine.
  Proof.
    (nd_pre args_geo 3%nat; intros G1 G2 G3; nd_post). unfold cs_mine.
    apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]]]]].
    - apply (args_ok AI AF); [exact G1| lia].
    - apply (unp_ok AI AF).
    - apply (exitci_ok AI AF BTLS CI_EXIT).
    - apply (globals_ok AI AF).
    - apply (stdinp_ok AI AF).
    - apply (stacksh_ok AI AF).
    - apply (tlsobj_ok AI AF BTLS).
  Qed.
  #[using="lim w V m ms mo AM HAT U LU VSP FITS CI_EXIT CI_ATX HU BTLS"] Lemma cs_mineX_ok : Forall (gcomp_ok AI) cs_mineX.
  Proof. unfold cs_mineX. apply Forall_cons; [exact (atx_ok AI AF CI_ATX cb)| exact cs_mine_ok]. Qed.
  #[using="lim w V m ms mo AM HAT U LU VSP FITS CI_EXIT CI_ATX CI_HARN CI_ST1 CI_ST2 CI_ENV CI_LOC HU BTLS BAHM"] Lemma cs_all_ok : Forall (gcomp_ok AI) cs_all.
  Proof. unfold cs_all. apply Forall_app. split; [exact cs_mineX_ok|]. apply Forall_cons; [exact (harn_ok AI AF CI_HARN)| exact CSOK4]. Qed.

  (* [comment removed for export] *)
  #[using="lim w V m ms mo AM HAT U LU VSP FITS HU"] Lemma cs_mine_indep : Forall harn_indep cs_mine.
  Proof.
    (nd_pre args_geo 3%nat; intros G1 G2 G3; nd_post). pose proof atop_range as AR.
    unfold cs_mine.
    apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]]]]];
      (split; [intros L1 R1 s1 FB1 m1 o HPc; exact HPc|]); intros L1 s1 FB1 a Da R; unfold OUTFILE_ADDR in R; cbn [gc_dom args_comp unp_comp exitci_comp globals_comp stdinp_comp stacksh_comp tlsobj_comp] in Da.
    - destruct (args_dom_band USP (Z.of_nat (length SBK) - 16) G1 ltac:(lia) a Da) as [B _]. clear - B R AR. Z.div_mod_to_equations. lia.
    - unfold unp_dom, AIMSH_LO in Da. lia.
    - unfold exitci_dom, exit_dom in Da. destruct Da as [D|[(k & Hk & Rk)|D]].
      + pose proof ATPv_img as TI. lia.
      + unfold EXIT_CI_KEEP in Hk. repeat (destruct Hk as [<-|Hk]; [cbn [fst snd] in Rk; lia|]). destruct Hk.
      + unfold AIMSH_LO in D. lia.
    - unfold win_dom, AIMSH_LO in Da. lia.
    - unfold win_dom, AIMSH_LO in Da. lia.
    - destruct Da as [Da D47]. destruct (stacksh_band L1 a Da D47) as [B _]. clear - B R AR. Z.div_mod_to_equations. lia.
    - destruct (tlsobj_band a Da) as (B & _). lia.
  Qed.

  #[using="lim w V m ms mo AM HAT U LU VSP FITS HU"] Lemma cs_mineX_indep : Forall harn_indep cs_mineX.
  Proof. unfold cs_mineX. apply Forall_cons; [exact (atx_harn_indep cb)| exact cs_mine_indep]. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma in_mine : forall c, In c cs_mine -> In c cs_all.
  Proof. intros c Hc. unfold cs_all, cs_mineX. apply in_or_app. left. right. exact Hc. Qed.
  Definition GL_run : gia_laws (asan_fo site_frameA) GIOA fflagA_real :=
    GL_inst CI CIB cs_all cs_all_ok
      (in_mine globals_comp ltac:(unfold cs_mine; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ])) (in_mine stdinp_comp ltac:(unfold cs_mine; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ]))
      (in_mine stacksh_comp ltac:(unfold cs_mine; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ])) (in_mine tlsobj_comp ltac:(unfold cs_mine; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ])).
  Definition GH_run : gia_harn_laws GIOA :=
    gia_harn_laws_real AI CI_HARN cs_mineX cs4
      (proj2 (Forall_app _ _ _) (conj cs_mineX_ok CSOK4)) (proj2 (Forall_app _ _ _) (conj cs_mineX_indep INDEP4)).

  Definition GD_run : gia_drv_laws GIOA USP SBK :=
    GD_inst CI CIB cs_all cs_all_ok USP SBK (proj1 args_geo) (proj1 (proj2 args_geo)) (proj2 (proj2 args_geo)) CI_RS
      (in_mine (args_comp USP (Z.of_nat (length SBK) - 16)) ltac:(unfold cs_mine; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ])) (in_mine unp_comp ltac:(unfold cs_mine; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ])).
  Definition MALLOC_run := malloc_inst CI CIB cs_all cs_all_ok.
  Definition FREE_run := free_inst CI CIB cs_all cs_all_ok.
  Definition FREENULL_run := free_null_inst CI CIB cs_all cs_all_ok.
  Definition CALLOC_run := calloc_inst CI CIB cs_all cs_all_ok TP HCPC.
  Definition REALLOC_run := realloc_inst CI CIB cs_all cs_all_ok TP HRPC.
  Definition MALLOC_D_run := malloc_d_inst CI CIB cs_all cs_all_ok.
  Definition FREE_D_run := free_d_inst CI CIB cs_all cs_all_ok.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="lim w V m ms mo AM HAT U LU VSP FITS CI_EXIT CI_ATX CI_HARN CI_ST1 CI_ST2 CI_ENV CI_LOC HU BTLS BAHM"] Lemma GSL : gia_stdio_laws GIOA.
  Proof.
    (nd_pre args_geo 3%nat; intros G1 G2 G3; nd_post).
    assert (OKS : Forall (gcomp_ok AI) ((cs_mineX ++ [harn_comp]) ++ [env_comp; strerr_comp])).
    { apply Forall_app. split; [apply Forall_app; split; [exact cs_mineX_ok| apply Forall_cons; [exact (harn_ok AI AF CI_HARN)| apply Forall_nil]]|].
      apply Forall_cons; [exact (env_ok AI AF CI_ENV BAHM)| apply Forall_cons; [exact (strerr_ok AI AF BTLS CI_LOC)| apply Forall_nil]]. }
    assert (INS : Forall (stdio_indep AI) ((cs_mineX ++ [harn_comp]) ++ [env_comp; strerr_comp])).
    { apply Forall_app. split; [apply Forall_app; split|].
      - unfold cs_mineX, cs_mine. apply Forall_cons; [exact (atx_stdio_indep AI cb)|].
        apply Forall_cons; [apply (args_indep AI); lia|]. apply Forall_cons; [exact (unp_indep AI)|]. apply Forall_cons; [exact (exitci_indep AI BTLS)|].
        apply Forall_cons; [exact (globals_indep AI)|]. apply Forall_cons; [exact (stdinp_indep AI)|]. apply Forall_cons; [exact (stacksh_indep AI)|].
        apply Forall_cons; [exact (tlsobj_indep AI)| apply Forall_nil].
      - apply Forall_cons; [exact (harn_stdio_indep AI)| apply Forall_nil].
      - apply Forall_cons; [exact (env_indep AI BAHM)| apply Forall_cons; [exact (strerr_stdio_indep AI BTLS)| apply Forall_nil]]. }
    exact (gia_stdio_laws_real AI AF BTLS CI_ST1 CI_ST2 BAHM (cs_mineX ++ [harn_comp]) [env_comp; strerr_comp] OKS INS
             ltac:(apply in_or_app; right; left; reflexivity)
             ltac:(apply in_or_app; left; apply in_or_app; left; unfold cs_mineX, cs_mine; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ])
             ltac:(apply in_or_app; left; apply in_or_app; left; unfold cs_mineX, cs_mine; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ])
             (inst_ssc CI CIB)).
  Qed.
  (* [comment removed for export] *)
  Definition VPR : vprintf_d_stmt_o GIOA := vprintf_d_proofA (asan_fo site_frameA) GIOA fflagA_real GL_run GSL.
  Definition EPR_USAGE : eprintf_s_stmt_o GIOA FMT_USAGE 16 pieces_usage := eprintf_usage_proofA (asan_fo site_frameA) GIOA fflagA_real GL_run GSL.
  Definition EPR_OPEN : eprintf_s_stmt_o GIOA FMT_CANNOT_OPEN 20 pieces_cannot_open := eprintf_cannot_open_proofA (asan_fo site_frameA) GIOA fflagA_real GL_run GSL.
  Definition EPR_READ : eprintf_s_stmt_o GIOA FMT_READ_ERROR 22 pieces_read_error := eprintf_read_error_proofA (asan_fo site_frameA) GIOA fflagA_real GL_run GSL.
  Definition EPR_BIG : eprintf_i_stmt_o GIOA FMT_TOO_BIG 32 0x4000000 pieces_too_big := eprintf_too_big_proofA (asan_fo site_frameA) GIOA fflagA_real GL_run GSL.
  Definition EFW : efwrite_stmt_o GIOA := efwrite_proofA (asan_fo site_frameA) GIOA fflagA_real GL_run GSL.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="Type"] Lemma cs_all_strerr : cs_all = (cs_mineX ++ [harn_comp; files_comp; env_comp]) ++ strerr_comp :: [].
  Proof. unfold cs_all, cs4. rewrite <- app_assoc. reflexivity. Qed.
  #[using="lim w V m ms mo AM HAT U LU VSP FITS CI_EXIT CI_ATX CI_HARN CI_ST1 CI_ST2 CI_ENV CI_LOC HU BTLS BAHM"] Lemma GSE_run : gia_strerr_laws GIOA.
  Proof.
    (nd_pre args_geo 3%nat; intros G1 G2 G3; nd_post).
    assert (OKS : Forall (gcomp_ok AI) ((cs_mineX ++ [harn_comp; files_comp; env_comp]) ++ [])).
    { rewrite app_nil_r. apply Forall_app. split; [exact cs_mineX_ok|].
      apply Forall_cons; [exact (harn_ok AI AF CI_HARN)|]. apply Forall_cons; [exact (files_ok AI AF CI_ST1 CI_ST2)|].
      apply Forall_cons; [exact (env_ok AI AF CI_ENV BAHM)| apply Forall_nil]. }
    assert (TIS : Forall tlsbuf_indep ((cs_mineX ++ [harn_comp; files_comp; env_comp]) ++ [])).
    { rewrite app_nil_r. apply Forall_app. split.
      - unfold cs_mineX, cs_mine. apply Forall_cons; [exact (atx_tlsbuf cb)|].
        apply Forall_cons; [apply args_tlsbuf; lia|]. apply Forall_cons; [exact unp_tlsbuf|]. apply Forall_cons; [exact exitci_tlsbuf|].
        apply Forall_cons; [exact globals_tlsbuf|]. apply Forall_cons; [exact stdinp_tlsbuf|]. apply Forall_cons; [exact stacksh_tlsbuf|].
        apply Forall_cons; [exact tlsobj_tlsbuf| apply Forall_nil].
      - apply Forall_cons; [exact harn_tlsbuf|]. apply Forall_cons; [exact files_tlsbuf|]. apply Forall_cons; [exact env_tlsbuf| apply Forall_nil]. }
    pose proof cs_all_strerr as ECS.
    constructor.
    - intros L1 RNG1 s CL FB FL m1 G. rewrite ECS in G.
      exact (ge_cells_real AI (inst_lsan CI CIB) _ _ _ _ _ _ _ _ _ G).
    - intros L1 RNG1 s CL FB FL m1 m' W SP new G MU WM FW HSP LS NEW. split.
      + pose proof G as G0. rewrite ECS in G0. rewrite ECS.
        exact (strerr_frame_real AI _ _ OKS TIS _ _ _ _ _ _ _ _ W SP new G0 MU WM FW HSP LS NEW).
      + pose proof G as (AH & _).
        eapply agrees_on_weaken; [exact (gs_keeps _ GSL _ _ _ _ _ _ _ _ W [(ATP + 16, ATP + PCAP_TLS_ERRBUF + 256)] SP G MU WM
                                           ltac:(eapply Forall_impl; [| exact FW]; intros iv K; left; exact K) HSP)|].
        intros a KA. split; [exact KA|]. cbn [outside]. split; [| exact I]. intros Ra.
        apply (tls_not_client AI AF BTLS _ _ _ CL FB FL m1 a AH); [unfold PCAP_TLS_ERRBUF in Ra; lia|].
        unfold client_reg. destruct KA as [K|K]; [left; lia| right; exact K].
  Qed.

  #[using="Type"] Lemma EQB_run : forall p q : aptr, ho_eqb asan_ops p q = true <-> p = q.
  Proof. intros p q. exact (N.eqb_eq p q). Qed.
  (* [comment removed for export] *)
  Definition FOPEN : fopen_stmt_o asan_ops GIOA TP :=
    fopen_o_proofA asan_ops (asan_fo site_frameA) GIOA TP fflagA_real GL_run GSL (gr_addr AI _) EQB_run MALLOC_run TP_real_fopen.
  (* [comment removed for export] *)
  Definition REMOVE : remove_stmt_o GIOA := remove_o_proofA (asan_fo site_frameA) GIOA fflagA_real GL_run GSL.
  Definition UNLINK : unlink_stmt_o GIOA := unlink_o_proofA (asan_fo site_frameA) GIOA fflagA_real GL_run GSL.
  Definition CLOSE : close_stmt_o GIOA := close_o_proofA (asan_fo site_frameA) GIOA fflagA_real GL_run GSL.
  (* [comment removed for export] *)
  Definition FCLOSE : fclose_stmt_o asan_ops GIOA TP :=
    fclose_o_proofA asan_ops (asan_fo site_frameA) GIOA TP fflagA_real GL_run GSL (gr_addr AI _) EQB_run FREE_run FREENULL_run TP_real_fclose.
  Let GSP := inst_GS_pres CI CIB cs_all cs_all_ok.
  #[using="lim w V m ms mo AM HAT U LU VSP FITS CI_EXIT CI_ATX CI_HARN CI_ST1 CI_ST2 CI_ENV CI_LOC HCPC HRPC HU BTLS BAHM GSP"] Lemma FUZZ : fuzz_one_stmt asan_ops (asan_fo site_frameA) stk GIOA TP.
  Proof.
    (* [comment removed for export] *)
    eapply (fuzz_one_closedA asan_ops (asan_fo site_frameA) stk GIOA TP fflagA_real);
      lazymatch goal with
      | |- gia_laws _ _ _ => exact GL_run
      | |- gia_harn_laws _ => exact GH_run
      | |- gia_addr_law _ _ => exact (gr_addr AI _)
      | |- gia_perm_law _ => exact (gr_perm AI _)
      | |- gia_got_law _ => exact (gr_got AI _)
      | |- OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.LeafA.TwB.fo_leaf_laws _ => exact (asan_fo_leaf_laws site_frameA)
      | |- fenter_stmt_o _ _ _ 0 _ => exact (fenter_real AI AF _ GSP 0 STACK_MALLOC_0 (or_introl (conj eq_refl eq_refl)))
      | |- fenter_stmt_o _ _ _ 1 _ => exact (fenter_real AI AF _ GSP 1 STACK_MALLOC_1 (or_intror (conj eq_refl eq_refl)))
      | |- fret_inline_law _ _ _ => exact (fret_real AI AF _ GSP)
      | |- fenter7_stmt_o _ _ _ => exact (fenter7_real AI AF _ GSP)
      | |- ffree7_stmt_o _ _ _ => exact (ffree7_real AI AF _ GSP)
      | |- set_shadow_stmt _ 0xf8 => exact set_shadow_f8_inst
      | |- set_shadow_stmt _ 0x00 => exact set_shadow_00_inst
      | |- malloc_stmt_o _ _ => exact MALLOC_run
      | |- calloc_stmt_o _ _ _ => exact CALLOC_run
      | |- realloc_stmt_o _ _ _ => exact REALLOC_run
      | |- free_stmt_o _ _ => exact FREE_run
      | |- free_null_stmt_o _ => exact FREENULL_run
      | |- fopen_stmt_o _ _ _ => exact FOPEN
      | |- fclose_stmt_o _ _ _ => exact FCLOSE
      | |- fread_stmt_o _ _ => exact (fread_o_proofA asan_ops (asan_fo site_frameA) GIOA fflagA_real GL_run GSL (gr_addr AI _) EQB_run)
      | |- ferror_stmt_o _ _ => exact (ferror_o_proofA asan_ops (asan_fo site_frameA) GIOA fflagA_real GL_run GSL EQB_run)
      | |- fileno_stmt_o _ _ => exact (fileno_o_proofA asan_ops (asan_fo site_frameA) GIOA fflagA_real GL_run GSL EQB_run)
      | |- fwrite_stmt_o _ _ => exact (fwrite_o_proofA asan_ops (asan_fo site_frameA) GIOA fflagA_real GL_run GSL EQB_run)
      | |- remove_stmt_o _ => exact REMOVE
      | |- unlink_stmt_o _ => exact UNLINK
      | |- close_stmt_o _ => exact CLOSE
      | |- mkstemp_stmt_o _ => exact (mkstemp_o_proofA (asan_fo site_frameA) GIOA fflagA_real GL_run GSL)
      | |- printf_d_stmt_o _ FMT_FAILED_REMOVE _ => exact (printf_failed_remove_proofA (asan_fo site_frameA) GIOA fflagA_real GL_run GSL)
      | |- printf_d_stmt_o _ FMT_FAILED_OPEN _ => exact (printf_failed_open_proofA (asan_fo site_frameA) GIOA fflagA_real GL_run GSL)
      | |- fprintf_dd_stmt_o _ _ _ _ => exact (fprintf_packet_length_proofA asan_ops (asan_fo site_frameA) GIOA fflagA_real GL_run GSL EQB_run)
      | |- fprintf_s_stmt_o _ _ _ _ => exact (fprintf_couldnt_open_proofA asan_ops (asan_fo site_frameA) GIOA fflagA_real GL_run GSL EQB_run)
      | |- snprintf_spec_stmt _ => exact (snprintf_proofA (asan_fo site_frameA) GIOA fflagA_real GL_run GSL)
      | |- vsnprintf_spec_stmt _ => exact (vsnprintf_proofA (asan_fo site_frameA) GIOA fflagA_real GL_run GSL)
      | |- strlen_stmt _ => exact (strlen_proofA (asan_fo site_frameA) GIOA fflagA_real GL_run GSL)
      | |- strerror_r_stmt _ => exact (strerror_r_proofA (asan_fo site_frameA) GIOA fflagA_real GL_run GSL GSE_run)
      | |- ~ (_ <= _ < _) => unfold TP_real, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesUnivA.TwB.ACALLOC_PC, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesUnivA.TwB.AREALLOC_PC, ACLIENT_LO, ACLIENT_HI; cbn [tp_cpc tp_rpc]; lia
      | |- forall p q, ho_eqb _ p q = true <-> p = q => exact EQB_run
      end.
  Qed.
  End Cb.

  (* [comment removed for export] *)
  Notation GIOA := (GIOA_real AI (GSTAT_of (cs_all 0))).
  Notation GIOA1 := (GIOA_real AI (GSTAT_of (cs_all 1))).
  (* [comment removed for export] *)
  #[using="lim ms mo AM HAT HTLS LU A0I VSP FITS HU"] Lemma cs_all_init : gconj (cs_all 0) L RNG s0 [] m.
  Proof.
    pose proof (me_facts _ _ _ _ _ _ _ _ AM) as [HM HP].
    unfold cs_all. apply (proj2 (gconj_app _ _ _ _ _ _ _)). split.
    - unfold cs_mineX, cs_mine. cbn [gconj gc_P atx_comp args_comp unp_comp exitci_comp globals_comp stdinp_comp stacksh_comp tlsobj_comp].
      split; [exists false; exact (atx_init V m HM)|].
      split; [exact (args_init _ _ _ _ _ _ _ _ AM HAT HTLS U lz AL HU A0I VSP FITS L s0 [])|].
      split; [exact (unp_init _ _ _ _ _ _ _ _ AM U HU L RNG s0 [])|].
      split; [exists (V 44%nat); exact (exit_ci_init V m HM HP HTLS)|].
      split; [exact (globals_init _ _ _ _ _ _ _ _ AM U HU L RNG s0 [])|].
      split; [exact (stdinp_init _ _ _ _ _ _ _ _ AM U HU L RNG s0 [])|].
      split; [exact (stacksh_init _ _ _ _ _ _ _ _ AM HAT HTLS U lz AL HU A0I s0 [])|].
      split; [exact (tlsobj_init _ _ _ _ _ _ _ _ AM HTLS U lz AL HU A0I L s0 [])| exact I].
    - cbn [gconj]. split; [| exact INIT4]. cbn [gc_P harn_comp]. apply (harn_init _ _ _ _ _ _ _ _ AM). reflexivity.
  Qed.


  (* [comment removed for export] *)
  #[using="lim w V m ms mo AM HAT U LU VSP FITS CI_RS CI_EXIT CI_ATX CI_HARN CI_ST1 CI_ST2 CI_ENV CI_LOC HU BTLS BAHM"] Lemma atx_rest_ok : Forall (gcomp_ok AI) ([] ++ (cs_mine ++ harn_comp :: cs4)).
  Proof. cbn [app]. apply Forall_app. split; [exact cs_mine_ok|]. apply Forall_cons; [exact (harn_ok AI AF CI_HARN)| exact CSOK4]. Qed.
  #[using="lim w V m ms mo AM HAT U LU VSP FITS HU BTLS"] Lemma atx_rest_indep : Forall atx_indep ([] ++ (cs_mine ++ harn_comp :: cs4)).
  Proof.
    (nd_pre args_geo 3%nat; intros G1 G2 G3; nd_post). cbn [app]. apply Forall_app. split.
    - unfold cs_mine.
      apply Forall_cons; [apply args_atx; lia|]. apply Forall_cons; [exact unp_atx|]. apply Forall_cons; [exact exitci_atx|].
      apply Forall_cons; [exact globals_atx|]. apply Forall_cons; [exact stdinp_atx|]. apply Forall_cons; [exact stacksh_atx|].
      apply Forall_cons; [exact tlsobj_atx| apply Forall_nil].
    - apply Forall_cons; [exact harn_atx|]. unfold cs4.
      apply Forall_cons; [exact files_atx|]. apply Forall_cons; [exact env_atx|]. apply Forall_cons; [exact strerr_atx| apply Forall_nil].
  Qed.
  #[using="lim w V m ms mo AM HAT U LU VSP FITS CI_RS CI_EXIT CI_ATX CI_HARN CI_ST1 CI_ST2 CI_ENV CI_LOC HU BTLS BAHM"] Lemma GA_run : gia_atx_laws GIOA.
  Proof. exact (gia_atx_laws_real AI AF CI_ATX CI_RS BTLS [] (cs_mine ++ harn_comp :: cs4) atx_rest_ok atx_rest_indep). Qed.
  #[using="lim w V m ms mo AM HAT U LU VSP FITS CI_RS CI_EXIT CI_ATX CI_HARN CI_ST1 CI_ST2 CI_ENV CI_LOC HU BTLS BAHM"] Lemma GCB_run : gia_cb_laws GIOA GIOA1.
  Proof. exact (gia_cb_laws_real AI AF CI_ATX CI_RS BTLS [] (cs_mine ++ harn_comp :: cs4) atx_rest_ok atx_rest_indep). Qed.

  #[using="U_FUZZ"] Lemma TRF : traces_fuzz_one TP L RA_FUZZ [].
  Proof. apply (traces_fuzz_one_univ L). intros tr Htr. cbn [al_U]. exact (U_FUZZ tr Htr). Qed.

  (* [comment removed for export] *)
  Definition STDIO_EXIT_SXA : stdio_exit_stmtA (@s_stdio_exit aheap aptr) (SXA (H := aheap) (hptr := aptr)) 160 := stdio_exit_proofA.   (* [comment removed for export] *)
  Notation SX := (SX_real (H := aheap) (hptr := aptr)).
  Definition stdio_exit_frame : Z := 160.
  #[using="rc U LU HU"] Lemma stdio_exit_frame_nonneg : 0 <= stdio_exit_frame.
  Proof. unfold stdio_exit_frame. lia. Qed.
  #[using="Type"] Lemma stdio_exit_fits : 48 + MDTOR_DEPTH + stdio_exit_frame <= MAIN_STACK.
  Proof. vm_compute. discriminate. Qed.
  #[using="Type"] Lemma SX_frame : forall (s : PS) RNG1 sp (m1 m' : mem), SX s RNG1 m1 -> (ATOP + 4096 <= sp - 48 - MDTOR_DEPTH)%Z ->
    munch (AEXIT_W1 sp ++ MDTOR_W) m1 m' -> wmono asegs m1 m' -> SX s RNG1 m'.
  Proof. exact SX_real_frame. Qed.
  #[using="Type"] Lemma STDIO_EXIT : stdio_exit_stmtA (@s_stdio_exit aheap aptr) SX stdio_exit_frame.
  Proof. exact (stdio_exit_stmtA_anti _ _ _ _ SX_real_sxa STDIO_EXIT_SXA). Qed.
  #[using="lim m ms mo AM HAT LU VSP FITS CI_EXIT CI_ATX CI_HARN CI_ST1 CI_ST2 CI_ENV CI_LOC HU BTLS BAHM"] Lemma SX_of_gioa : forall RNG1 (s : PS) CL FB (m1 : mem), GIOA L RNG1 s CL FB [] m1 -> SX s RNG1 m1.
  Proof. intros RNG1 s CL FB m1 G. exact (SX_real_of_gioa (asan_fo site_frameA) GIOA fflagA_real (GL_run 0) (GSL 0) L RNG1 s CL FB [] m1 G). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="lim w V m ms mo AM HAT U LU VSP FITS CI_RS CI_EXIT CI_ATX CI_HARN CI_ST1 CI_ST2 CI_ENV CI_LOC HCPC HRPC HU BTLS BAHM"] Lemma TRUN_run : target_run_stmt_o asan_ops (asan_fo site_frameA) stk GIOA TP.
  Proof.
    (* [comment removed for export] *)
    exact (target_run_proof asan_ops (asan_fo site_frameA) stk GIOA TP fflagA_real USP SBK GIOA1 (GL_run 0) (GL_run 1) (GD_run 0) GA_run GCB_run
             (MALLOC_run 0) (FREE_run 0) (FREENULL_run 0) (FUZZ 1) (VPR 0)).
  Qed.

  #[using="lim m ms mo AM HAT LU VSP FITS CI_EXIT CI_ATX CI_HARN CI_ST1 CI_ST2 CI_ENV CI_LOC HU BTLS BAHM"] Lemma GX_run : forall RNG1 s CL FB m1, GIOA L RNG1 s CL FB [] m1 ->
    (exists t, exit_ci t m1) /\ (exists (Hh : aholes) st LB, AHEAP_P Hh L RNG1 st LB m1) /\ SX s RNG1 m1.
  Proof.
    intros RNG1 s CL FB m1 G. (pose proof G as ndP__; nd_pre ndP__ 7%nat; intros AH _ _ _ _ _ (_ & GC); nd_post).
    split; [exact (gconj_In _ _ _ _ _ _ _ GC (in_mine 0 exitci_comp ltac:(unfold cs_mine; cbn [In]; solve [ repeat first [ left; reflexivity | right ] ])))|].
    split; [exists AHI, (ah_st (ps_heap s)), (LBof CL FB []); exact AH| exact (SX_of_gioa _ _ _ _ _ G)].
  Qed.

  #[using="U_DRV"] Lemma TRD_run : traces_drv L.
  Proof. intros tr Htr. cbn [al_U]. exact (U_DRV tr Htr). Qed.

  #[using="tlsI en lim w m mo AM HAT HTLS U LU FU A0I ASH0 VI VSP FITS CI CIB CI_RS CI_EXIT CI_ATX CI_HARN CI_ST1 CI_ST2 CI_ENV CI_LOC HCPC HRPC SITE_RS U_DRV U_FUZZ HU BTLS BAHM"] Theorem impl_run : forall Q, implMG RNG (prog_main asan_ops (asan_fo site_frameA) stk (argv_Z (in_argv inp))) s0 Q ms.
  Proof.
    intros Q. (nd_pre (me_geometry _ _ _ _ _ _ _ _ AM HAT U HU VSP FITS) 6%nat; intros M1 M2 M3 M4 M5 M6; nd_post).
    eapply (prog_main_impl asan_ops (asan_fo site_frameA) stk GIOA TP fflagA_real (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) L LO
              (GL_run 0) (GD_run 0) GA_run (MALLOC_D_run 0) (FREE_D_run 0) (EPR_USAGE 0) (EPR_OPEN 0) (EPR_READ 0) (EPR_BIG 0) (EFW 0) SITE_RS TRUN_run M1 M2 M3 M4 M5 M6 TRD_run TRF
              SX stdio_exit_frame stdio_exit_frame_nonneg stdio_exit_fits SX_frame STDIO_EXIT GX_run).
    eapply (main_entry_handoff _ _ _ _ _ _ _ _ AM HAT HTLS U lz AL HU A0I VI VSP FITS GIOA s0 []).
    exact (gioa_at_main _ _ _ _ _ _ _ _ AM HAT HTLS U lz AL LU FU A0I ASH0 CI CIB (cs_all 0) libc_init None 6166768 cs_all_init).
  Qed.
End Run.
End CANSEC1.
End TwB.
