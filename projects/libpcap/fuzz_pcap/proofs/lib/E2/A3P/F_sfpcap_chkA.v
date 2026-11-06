(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require SfKitA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_sfchk_epiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_exitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_sfchk_msegA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaRel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac plia_comp := first [ once ltac2:(LiaRel.lr_prune_sub ()); lia_tiers | once ltac2:(LiaRel.lr_prune_hub 5); lia_tiers
                              | once ltac2:(let _ := LiaRel.lr_prune_b 101 in ()); lia_tiers ].
Local Ltac transport_call_munch_tac ::= unfold sub_fp; cbn [outside]; intros; first [ plia_comp | slia ].
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
(* [comment removed for export] *)
Local Ltac oiv_lo_base k := lazymatch goal with |- (?lo0 <= ?lo)%Z /\ _ => d_split lo0 ltac:(fun X0 _ _ => d_split lo ltac:(fun X _ _ => constr_eq X0 X; k)) end.
Local Ltac oiv_orig :=
  first [ left; cbn [fst snd]; lia
        | right; right; left; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; lia
        | right; right; right; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; shr_consts; lia
        | right; left; first [ apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_tl; apply Exists_cons_hd ];
          cbn [cb_addr cb_size fst snd]; lia ].
Local Ltac own_iv1 ::=
  unfold own_ivA, iv_in_block, iv_in_frames, iv_in_frame_shadow;
  first [ right; right; left; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; oiv_lo_base ltac:(lia)
        | right; right; right; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; shr_consts; oiv_lo_base ltac:(lia)
        | right; left; first [ apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_tl; apply Exists_cons_hd ];
          cbn [cb_addr cb_size fst snd]; oiv_lo_base ltac:(lia)
        | oiv_orig ].
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.

Lemma land_m32A : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551584 = (x - x mod 32)%Z.
Proof. intros x Hx. exact (land_align_down x 5 Hx ltac:(lia)). Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section Chk.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FENTER1 : fenter_stmt_o FO GIOA fflagA 1 STACK_MALLOC_1.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis CHK_TAIL : chk_tail_stmt HO FO sites GIOA TP fflagA.

  Definition pcap_check_header_proofA__stmt : Prop := pcap_check_header_stmt HO FO sites GIOA TP.
  Section Sz2.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL trC lo MG FA EB ERR f magic ej ec fuel : ltac2:(SecDiet.SzSec.tyM 'pcap_check_header_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma pcap_check_header_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'pcap_check_header_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using CHK_TAIL FENTER1 FRET GL.
    intros PRE UC TR NF HinF -> -> -> -> -> HMG MGR MGL HEB HERR ECS OMG OERR DME OEB DEE DEM ERR4 EB8.
    (nd_pre PRE 12%nat; intros G ST LO BU SPT MI TPE ALN RSTK RIMG RISH RTLS; nd_post).
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as ((_ & GOT & _ & _ & SHB & SUA & _) & GSU). unfold GOT_UAR in GSU.
    unfold PCAP_L2_STACK in BU.
    assert (RSPW : rng RNG lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (proj1 OMG)) as (MGLO & MGHI).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (proj1 OERR)) as (ERLO & ERHI).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (proj1 OEB)) as (EBLO & EBHI).
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (proj1 OMG) ltac:(lia)) as MGBAND.
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (proj1 OERR) ltac:(lia)) as ERBAND.
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (proj1 OEB) ltac:(lia)) as EBBAND.
    pose proof MGBAND as MGBAND'. pose proof ERBAND as ERBAND'. pose proof EBBAND as EBBAND'.
    band_ind MGBAND bM. band_ind ERBAND bE. band_ind EBBAND bB.
    destruct magic as [|mg0 [|mg1 [|mg2 [|mg3 [|? ?]]]]]; try discriminate MGL. clear MGL.
    pose proof MGR as GR'. apply Forall_cons_iff in GR' as [GM0 GR']. apply Forall_cons_iff in GR' as [GM1 GR']. apply Forall_cons_iff in GR' as [GM2 GR']. apply Forall_cons_iff in GR' as [GM3 _].
    cbn [map] in HMG.
    assert (MG4 : rw_cells asegs m MG [C1 (b8 mg0); C1 (b8 mg1); C1 (b8 mg2); C1 (b8 mg3)]).
    { eapply rw_cells_recell; [exact HMG | cbn; repeat split; exact Logic.I | reflexivity]. }
    clear HMG.
    destruct (rw_cells_forget _ _ _ _ HERR) as [ecj HE]. clear HERR. cbn [cells_size] in HE. rewrite ECS in HE. change (4 + 0)%nat with 4%nat in HE.
    unfold Pcap.pcap_check_header. cbn [mo_bind mo_ret MOps e_fenter e_fret prims]. unfold PCAP_CHECK_HEADER_ENTRY.
    remember (bv_unsigned sp - 192 - (bv_unsigned sp - 192) mod 32)%Z as SPA eqn:ESPA.
    assert (SPAP : (bv_unsigned sp - 208 <= SPA <= bv_unsigned sp - 192 /\ SPA mod 32 = 0 /\ (bv_unsigned sp + -192) - (bv_unsigned sp + -192) mod 32 = SPA)%Z)
      by (rewrite ESPA; Z.div_mod_to_equations; lia).
    (nd_pre SPAP 3%nat; intros SPAB SPA32 ESPA'; nd_post).
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp - 208, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG.
    (* [comment removed for export] *)
    zstep.
    carve_frame 104%nat ST. carve_frame 88%nat ST.
    zstep.
    do 13 zstep.
    zstep.
    zstep.
    rewrite land_m32A by lia. rewrite ESPA'.
    release_frame FR0 ST (bv_unsigned sp + -104)%Z.
    destruct (stk_split asegs _ lo (SPA + 88) (bv_unsigned sp + -104) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve asegs _ lo (SPA + 88) 88 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
    change (Z.of_nat 88) with 88%Z in STL, FRA. replace (SPA + 88 - 88)%Z with SPA in STL, FRA by lia.
    assert (RSPA : rng RNG SPA (bv_unsigned sp - SPA)) by (eapply rng_sub'; [exact RSTK| lia]).
    (* [comment removed for export] *)
    do 7 zstep.
    (* [comment removed for export] *)
    do 2 zstep.
    zstep.
    replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
    zstep.
    zstep.
    zstep. if_false.
    do 2 zstep.
    (* [comment removed for export] *)
    assert (Gn : GIOA L RNG s (CL ++ []) FB FL m) by (rewrite app_nil_r; exact G).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FW0 : Forall (pcap_iv FL ([] : list (@cblock hptr))) [(bv_unsigned sp - 208, bv_unsigned sp)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]);
      assert (G0 : GIOA L RNG s (CL ++ []) FB FL mm) by (eapply (gl_frame _ _ _ GL); [exact Gn | exact MU | exact WM | exact FW0]);
      assert (AGa : agrees_on (client_keeps FL CL (bv_unsigned sp)) m mm)
        by (eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact Gn | exact MU | exact WM | | lia];
            apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil])
    end.
    rename MU into MU0. rename WM into WM0. clear FW0.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply (FENTER1 _ spa).
    { split; [rewrite app_nil_r in G0; exact G0|]. rewrite Hspa. split; [exact STL|]. split; [lia|]. split; [unfold FAKE_STACK; lia|]. split; [lia|].
      split; [assumption|]. split; [exact TPE|]. split; [Z.div_mod_to_equations; lia|].
      split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
    { reflexivity. }
    { unfold ff_size, ff_class. lia. }
    { apply NF. left. reflexivity. }
    { reflexivity. }
    intros Fb s1' m2 j0 j1 j2 fjunk t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' G1 OF1 LC1 TL1 MI1 ST1 AG1 Fb0 LJ FRC SHC.
    rewrite Hspa in *. clear Hspa. subst spa.
    change (ff_size FF_CHECK_HEADER) with 128%Z in *.
    change (Z.to_nat (128 - 32)) with 96%nat in *. change (Z.to_nat (128 / 8)) with 16%nat in *.
    apply sh_zero_cells in SHC. cbn [repeat] in SHC.
    replace (ret_pc (Z_to_bv 64 554684)) with (Z_to_bv 64 554684) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G1) as [FAll FND]. (pose proof (Forall_inv FAll) as ndP__; nd_pre ndP__ 8%nat; intros FBAND' FTOP' F64 _ FRNG FSRNG _ FSWR; nd_post).
    cbn [fb_addr fb_size fst snd] in FBAND', FTOP', F64, FRNG, FSRNG, FSWR. clear FAll.
    change (Z.shiftr 128 3) with 16%Z in FSRNG, FSWR.
    band_ind FBAND' bF.
    (* [comment removed for export] *)
    apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FR; [|lia]. apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FRA; [|lia].
    apply (agrees_stk _ _ _ _ _ AG1) in STG; [|intros a Ha; left; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG1) in MG4; [|intros a Ha; eapply clocA_keeps; [exact (proj1 OMG)| exact Ha]].
    apply (agrees_rw_cells _ _ _ _ _ AG1) in HE; [|intros a Ha; eapply clocA_keeps; [exact (proj1 OERR)| exact Ha]].
    apply (agrees_rw_cells _ _ _ _ _ AG1) in HEB; [|intros a Ha; eapply clocA_keeps; [exact (proj1 OEB)| exact Ha]].
    (nd_pre (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G1 (proj1 OMG) ltac:(lia)) 4%nat; intros kM kMr kM1 kM2; nd_post).
    (nd_pre (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G1 (proj1 OERR) ltac:(lia)) 4%nat; intros kE kEr kE1 kE2; nd_post).
    (nd_pre (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G1 (proj1 OEB) ltac:(lia)) 4%nat; intros kB kBr kB1 kB2; nd_post).
    cbn [fb_addr fb_size fst snd] in kM1, kM2, kE1, kE2, kB1, kB2.
    assert (AGb : agrees_on (client_keeps FL CL (bv_unsigned sp)) m m2).
    { eapply agrees_on_trans; [exact AGa|]. eapply client_keeps_weaken; [exact AG1| lia| intros a Ha; exact Ha| apply incl_refl]. }
    assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 16 <= 0x10007fff8000
                   /\ (Fb + 128 <= 0x7fff7000 \/ Z.shiftr Fb 3 + 2147450880 + 16 <= Fb))%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    pose proof (munch_refl [(bv_unsigned sp - 208, bv_unsigned sp); (Fb, Fb + 128); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 16); (ERR, ERR + 4); (EB, EB + 256)]%Z m2) as MU.
    pose proof (wmono_refl asegs m2) as WM.
    ienterG.
    (* [comment removed for export] *)
    do 2 zstep.
    zstep. if_true_by (nez_true Fb ltac:(lia)).
    burst_begin [(Fb, Fb + 128); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 16)]%Z [Fb; (Z.shiftr Fb 3 + 2147450880)%Z] MUb WMb.
    do 5 zstep. neg_lits.
    do 3 zstep.
    do 3 zstep.
    zstep. neg_lits.
    zstep.
    do 2 zstep.
    zstep. neg_lits.
    zstep_sh0. do 3 zstep.
    zstep.
    do 8 zstep.
    burst_end MUb WMb.
    (* [comment removed for export] *)
    assert (G1n : GIOA L RNG s1' (CL ++ []) FB ([(FF_CHECK_HEADER, Fb, 128%Z)] ++ FL) m2) by (rewrite app_nil_r; exact G1).
    assert (FW : Forall (own_ivA [(FF_CHECK_HEADER, Fb, 128%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(bv_unsigned sp - 208, bv_unsigned sp); (Fb, Fb + 128); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 16)]%Z) by own_ivs.
    assert (FX : Forall (cobj_iv FL CL) [(ERR, ERR + 4); (EB, EB + 256)]%Z) by cobj_ivs.
    assert (FXB : Forall (fun iv : Z * Z => ablk (fst iv) (snd iv)) [(ERR, ERR + 4); (EB, EB + 256)]%Z)
      by (apply Forall_cons; [exact ERBAND'| apply Forall_cons; [exact EBBAND'| apply Forall_nil]]).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ _ _ FW FX G1n MU WM ltac:(lia)) as [G2 AG2];
      assert (AGsh : agrees_on (in_frame_sh FL) m mm)
        by (eapply agrees_on_trans; [exact (keeps_frame_sh _ _ _ _ _ AGb)|]; exact (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G1 (incl_tl _ (incl_refl _)) AG2 FXB))
    end.
    (pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OERR G2 (incl_appl _ (incl_refl _)) (incl_tl _ (incl_refl _)) AGsh ltac:(lia)) as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ ERUNP ERRNG ERRSH _; nd_post).
    (pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OMG G2 (incl_appl _ (incl_refl _)) (incl_tl _ (incl_refl _)) AGsh ltac:(lia)) as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ MGUNP MGRNG MGRSH _; nd_post).
    (* [comment removed for export] *)
    unfold b8 in *.
    assert (RSP88 : rng RNG SPA 88) by (eapply rng_sub'; [exact RSPA| lia]).
    assert (SPALO : (17594333495296 <= SPA)%Z) by (atop_facts; lia).
    call magic_load_seq; [try eassumption .. | ]; [lia .. | ].
    lazymatch goal with HH : rw_cells asegs _ SPA _ |- _ => rename HH into FRA end.
    lazymatch goal with HH : rw_cells asegs _ ERR _ |- _ => rename HH into HE end.
    pose proof (magic_sx_range mg0 mg1 mg2 mg3 GM0 GM1 GM2 GM3) as WR.
    set (W := magic_sx mg0 mg1 mg2 mg3) in *.
    (* [comment removed for export] *)
    clear G2 AG2 AGsh.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ _ _ FW FX G1n MU WM ltac:(lia)) as [G5 AG5] end.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AGm : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m mm)
        by (eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGb|]; intros a (K & _); exact K| exact AG5]) end.
    assert (CTX : chk_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f [mg0; mg1; mg2; mg3] m).
    { unfold chk_ctx, PCAP_L2_STACK. do 5 (split; [first [assumption | lia]|]).
      split; [split; [exact RSTK| split; [exact RIMG| split; [exact RISH| exact RTLS]]]|].
      repeat (split; [first [assumption | reflexivity | lia]|]). first [assumption | lia]. }
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (INV : chk_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] (ps_outfile s) m RNG s1' [] mm)
        by (unfold chk_inv, chk_shadow; split; [apply fp_le_refl|]; split; [exact G5|]; repeat (split; [first [assumption | reflexivity]|]); assumption) end.
    pose proof (magic_cases mg0 mg1 mg2 mg3 GM0 GM1 GM2 GM3) as CASES. cbv zeta in CASES.
    destruct CASES as [C1' | [C2' | [C3' | [C4' | [C5' | [C6' | [NM1 NM2]]]]]]].
    7:{ (* [comment removed for export] *)
      pose proof (magic_none mg0 mg1 mg2 mg3 GM0 GM1 GM2 GM3 NM1 NM2) as NN. cbv zeta in NN. fold W in NN. (nd_pre NN 6%nat; intros N1 N2 N3 N4 N5 N6; nd_post).
      neg_lits. zstep.
      if_cases K1; [zify_cond K1; exfalso; lia|].
      do 3 zstep. neg_lits.
      if_cases K2; [zify_cond K2; exfalso; lia|].
      do 3 zstep. neg_lits.
      if_cases K3; [|zify_cond K3; exfalso; lia].
      eapply evtF_cut; [eapply magic_swap_seq; lia|]. cbv beta. intros ms' PO. destruct_exs PO. subst ms'.
      zstep.
      if_cases K4; [zify_cond K4; exfalso; lia|].
      do 4 zstep.
      if_cases K5; [zify_cond K5; exfalso; lia|].
      do 4 zstep.
      if_cases K6; [zify_cond K6; exfalso; lia|].
      zstep.
      apply evtF_done. rewrite NM1, NM2. cbv beta iota zeta. cbn [negb]. cbv beta iota zeta.
      subst POSTQ0 POSTQ.
      eapply (chk_exit FO GIOA TP fflagA GL FRET) with (fcs := [CB 96 fjunk]) (r := CH_NotMe);
        [exact CTX | exact INV | exact FRA | reflexivity | exact FRC | reflexivity | exact HE |].
      cbn [chk_result]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exists ej; exact HEB. }
    (* [comment removed for export] *)
    1:{ (destruct C1' as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); destruct ndR2__ as (-> & ndR3__); revert ndR3__; intros ->). subst W. change (magic_sx 212 195 178 161) with 18446744072127431636%Z.
      neg_lits. zstep. if_false.
      do 3 zstep. neg_lits. if_true.
      apply evtF_done.
      lazymatch goal with |- implMG _ ?c _ _ _ => change c with (chk_rest MOps (prims HO FO sites) f 0 TCPDUMP_MAGIC false) end.
      subst POSTQ0 POSTQ.
      lazymatch goal with |- implMG _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (CHK_TAIL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL trC lo MG FA EB ERR SPA Fb f [212; 195; 178; 161]%Z m RNG s1' mm) with (mi := TCPDUMP_MAGIC) (sw := false);
        [exact CTX | exact INV | left; reflexivity | exact LJ | exact FRA | exact FRC | exact HE | exact HEB] end. }
    1:{ (destruct C2' as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); destruct ndR2__ as (-> & ndR3__); revert ndR3__; intros ->). subst W. change (magic_sx 52 205 178 161) with 18446744072127434036%Z.
      neg_lits. zstep. if_false.
      do 3 zstep. neg_lits. if_false.
      do 3 zstep. neg_lits. if_false.
      apply evtF_done.
      lazymatch goal with |- implMG _ ?c _ _ _ => change c with (chk_rest MOps (prims HO FO sites) f 0 KUZNETZOV_TCPDUMP_MAGIC false) end.
      subst POSTQ0 POSTQ.
      lazymatch goal with |- implMG _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (CHK_TAIL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL trC lo MG FA EB ERR SPA Fb f [52; 205; 178; 161]%Z m RNG s1' mm) with (mi := KUZNETZOV_TCPDUMP_MAGIC) (sw := false);
        [exact CTX | exact INV | right; left; reflexivity | exact LJ | exact FRA | exact FRC | exact HE | exact HEB] end. }
    1:{ (destruct C3' as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); destruct ndR2__ as (-> & ndR3__); revert ndR3__; intros ->). subst W. change (magic_sx 77 60 178 161) with 18446744072127396941%Z.
      neg_lits. zstep. if_true.
      apply evtF_done.
      lazymatch goal with |- implMG _ ?c _ _ _ => change c with (chk_rest MOps (prims HO FO sites) f 0 NSEC_TCPDUMP_MAGIC false) end.
      subst POSTQ0 POSTQ.
      lazymatch goal with |- implMG _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (CHK_TAIL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL trC lo MG FA EB ERR SPA Fb f [77; 60; 178; 161]%Z m RNG s1' mm) with (mi := NSEC_TCPDUMP_MAGIC) (sw := false);
        [exact CTX | exact INV | right; right; reflexivity | exact LJ | exact FRA | exact FRC | exact HE | exact HEB] end. }
    1:{ (destruct C4' as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); destruct ndR2__ as (-> & ndR3__); revert ndR3__; intros ->). subst W. change (magic_sx 161 178 195 212) with 18446744072984179361%Z.
      neg_lits. zstep. if_false.
      do 3 zstep. neg_lits. if_false.
      do 3 zstep. neg_lits. if_true.
      sf_old_zstep.   (* [comment removed for export] *)
      do 14 zstep. neg_lits.
      zstep. if_true.
      do 2 zstep.
      apply evtF_done.
      lazymatch goal with |- implMG _ ?c _ _ _ => change c with (chk_rest MOps (prims HO FO sites) f 0 TCPDUMP_MAGIC true) end.
      subst POSTQ0 POSTQ.
      lazymatch goal with |- implMG _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (CHK_TAIL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL trC lo MG FA EB ERR SPA Fb f [161; 178; 195; 212]%Z m RNG s1' mm) with (mi := TCPDUMP_MAGIC) (sw := true);
        [exact CTX | exact INV | left; reflexivity | exact LJ | exact FRA | exact FRC | exact HE | exact HEB] end. }
    1:{ (destruct C5' as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); destruct ndR2__ as (-> & ndR3__); revert ndR3__; intros ->). subst W. change (magic_sx 161 178 205 52) with 885895841%Z.
      neg_lits. zstep. if_false.
      do 3 zstep. neg_lits. if_false.
      do 3 zstep. neg_lits. if_true.
      sf_old_zstep.   (* [comment removed for export] *)
      do 14 zstep. neg_lits.
      zstep. if_false.
      do 4 zstep. if_false.
      do 4 zstep. if_true.
      apply evtF_done.
      lazymatch goal with |- implMG _ ?c _ _ _ => change c with (chk_rest MOps (prims HO FO sites) f 0 KUZNETZOV_TCPDUMP_MAGIC true) end.
      subst POSTQ0 POSTQ.
      lazymatch goal with |- implMG _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (CHK_TAIL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL trC lo MG FA EB ERR SPA Fb f [161; 178; 205; 52]%Z m RNG s1' mm) with (mi := KUZNETZOV_TCPDUMP_MAGIC) (sw := true);
        [exact CTX | exact INV | right; left; reflexivity | exact LJ | exact FRA | exact FRC | exact HE | exact HEB] end. }
    1:{ (destruct C6' as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); destruct ndR2__ as (-> & ndR3__); revert ndR3__; intros ->). subst W. change (magic_sx 161 178 60 77) with 1295823521%Z.
      neg_lits. zstep. if_false.
      do 3 zstep. neg_lits. if_false.
      do 3 zstep. neg_lits. if_true.
      sf_old_zstep.   (* [comment removed for export] *)
      do 14 zstep. neg_lits.
      zstep. if_false.
      do 4 zstep. if_true.
      apply evtF_done.
      lazymatch goal with |- implMG _ ?c _ _ _ => change c with (chk_rest MOps (prims HO FO sites) f 0 NSEC_TCPDUMP_MAGIC true) end.
      subst POSTQ0 POSTQ.
      lazymatch goal with |- implMG _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (CHK_TAIL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL trC lo MG FA EB ERR SPA Fb f [161; 178; 60; 77]%Z m RNG s1' mm) with (mi := NSEC_TCPDUMP_MAGIC) (sw := true);
        [exact CTX | exact INV | right; right; reflexivity | exact LJ | exact FRA | exact FRC | exact HE | exact HEB] end. }
  Qed.
  End Sz2.
  Theorem pcap_check_header_proofA : ltac:(let t := eval cbv delta [pcap_check_header_proofA__stmt] in pcap_check_header_proofA__stmt in exact t).
  Proof using CHK_TAIL FENTER1 FRET GL. red. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL trC lo MG FA EB ERR f magic ej ec fuel. ltac2:(SecDiet.SzSec.closeP 'pcap_check_header_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Chk.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.SfKitA__A3P.SfKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_sfchk_epiA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_defsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_sfchk_exitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.F_sfchk_msegA.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac plia_comp := first [ once ltac2:(LiaRel.lr_prune_sub ()); lia_tiers | once ltac2:(LiaRel.lr_prune_hub 5); lia_tiers
                              | once ltac2:(let _ := LiaRel.lr_prune_b 101 in ()); lia_tiers ].
Local Ltac transport_call_munch_tac ::= unfold sub_fp; cbn [outside]; intros; first [ plia_comp | slia ].
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
(* [comment removed for export] *)
Local Ltac oiv_lo_base k := lazymatch goal with |- (?lo0 <= ?lo)%Z /\ _ => d_split lo0 ltac:(fun X0 _ _ => d_split lo ltac:(fun X _ _ => constr_eq X0 X; k)) end.
Local Ltac oiv_orig :=
  first [ left; cbn [fst snd]; lia
        | right; right; left; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; lia
        | right; right; right; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; shr_consts; lia
        | right; left; first [ apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_tl; apply Exists_cons_hd ];
          cbn [cb_addr cb_size fst snd]; lia ].
Local Ltac own_iv1 ::=
  unfold own_ivA, iv_in_block, iv_in_frames, iv_in_frame_shadow;
  first [ right; right; left; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; oiv_lo_base ltac:(lia)
        | right; right; right; apply Exists_cons_hd; cbn [fb_addr fb_size fst snd]; shr_consts; oiv_lo_base ltac:(lia)
        | right; left; first [ apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_hd | apply Exists_cons_tl; apply Exists_cons_tl; apply Exists_cons_hd ];
          cbn [cb_addr cb_size fst snd]; oiv_lo_base ltac:(lia)
        | oiv_orig ].
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.

Lemma land_m32A : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551584 = (x - x mod 32)%Z.
Proof. intros x Hx. exact (land_align_down x 5 Hx ltac:(lia)). Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section Chk.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FENTER1 : fenter_stmt_o FO GIOA fflagA 1 STACK_MALLOC_1.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis CHK_TAIL : chk_tail_stmt HO FO sites GIOA TP fflagA.

  Definition pcap_check_header_proofA__stmt : Prop := pcap_check_header_stmt HO FO sites GIOA TP.
  Section Sz2.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL trC lo MG FA EB ERR f magic ej ec fuel : ltac2:(SecDiet.SzSec.tyM 'pcap_check_header_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma pcap_check_header_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'pcap_check_header_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using CHK_TAIL FENTER1 FRET GL.
    intros PRE UC TR NF HinF -> -> -> -> -> HMG MGR MGL HEB HERR ECS OMG OERR DME OEB DEE DEM ERR4 EB8.
    (nd_pre PRE 12%nat; intros G ST LO BU SPT MI TPE ALN RSTK RIMG RISH RTLS; nd_post).
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as ((_ & GOT & _ & _ & SHB & SUA & _) & GSU). unfold GOT_UAR in GSU.
    unfold PCAP_L2_STACK in BU.
    assert (RSPW : rng RNG lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (proj1 OMG)) as (MGLO & MGHI).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (proj1 OERR)) as (ERLO & ERHI).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G (proj1 OEB)) as (EBLO & EBHI).
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (proj1 OMG) ltac:(lia)) as MGBAND.
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (proj1 OERR) ltac:(lia)) as ERBAND.
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G (proj1 OEB) ltac:(lia)) as EBBAND.
    pose proof MGBAND as MGBAND'. pose proof ERBAND as ERBAND'. pose proof EBBAND as EBBAND'.
    band_ind MGBAND bM. band_ind ERBAND bE. band_ind EBBAND bB.
    destruct magic as [|mg0 [|mg1 [|mg2 [|mg3 [|? ?]]]]]; try discriminate MGL. clear MGL.
    pose proof MGR as GR'. apply Forall_cons_iff in GR' as [GM0 GR']. apply Forall_cons_iff in GR' as [GM1 GR']. apply Forall_cons_iff in GR' as [GM2 GR']. apply Forall_cons_iff in GR' as [GM3 _].
    cbn [map] in HMG.
    assert (MG4 : rw_cells asegs m MG [C1 (b8 mg0); C1 (b8 mg1); C1 (b8 mg2); C1 (b8 mg3)]).
    { eapply rw_cells_recell; [exact HMG | cbn; repeat split; exact Logic.I | reflexivity]. }
    clear HMG.
    destruct (rw_cells_forget _ _ _ _ HERR) as [ecj HE]. clear HERR. cbn [cells_size] in HE. rewrite ECS in HE. change (4 + 0)%nat with 4%nat in HE.
    unfold Pcap.pcap_check_header. cbn [mo_bind mo_ret MOps e_fenter e_fret prims]. unfold PCAP_CHECK_HEADER_ENTRY.
    remember (bv_unsigned sp - 192 - (bv_unsigned sp - 192) mod 32)%Z as SPA eqn:ESPA.
    assert (SPAP : (bv_unsigned sp - 208 <= SPA <= bv_unsigned sp - 192 /\ SPA mod 32 = 0 /\ (bv_unsigned sp + -192) - (bv_unsigned sp + -192) mod 32 = SPA)%Z)
      by (rewrite ESPA; Z.div_mod_to_equations; lia).
    (nd_pre SPAP 3%nat; intros SPAB SPA32 ESPA'; nd_post).
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp - 208, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG.
    (* [comment removed for export] *)
    zstep.
    carve_frame 104%nat ST. carve_frame 88%nat ST.
    zstep.
    do 13 zstep.
    zstep.
    zstep.
    rewrite land_m32A by lia. rewrite ESPA'.
    release_frame FR0 ST (bv_unsigned sp + -104)%Z.
    destruct (stk_split asegs _ lo (SPA + 88) (bv_unsigned sp + -104) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve asegs _ lo (SPA + 88) 88 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
    change (Z.of_nat 88) with 88%Z in STL, FRA. replace (SPA + 88 - 88)%Z with SPA in STL, FRA by lia.
    assert (RSPA : rng RNG SPA (bv_unsigned sp - SPA)) by (eapply rng_sub'; [exact RSTK| lia]).
    (* [comment removed for export] *)
    do 7 zstep.
    (* [comment removed for export] *)
    do 2 zstep.
    zstep.
    replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
    zstep.
    zstep.
    zstep. if_false.
    do 2 zstep.
    (* [comment removed for export] *)
    assert (Gn : GIOA L RNG s (CL ++ []) FB FL m) by (rewrite app_nil_r; exact G).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FW0 : Forall (pcap_iv FL ([] : list (@cblock hptr))) [(bv_unsigned sp - 208, bv_unsigned sp)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]);
      assert (G0 : GIOA L RNG s (CL ++ []) FB FL mm) by (eapply (gl_frame _ _ _ GL); [exact Gn | exact MU | exact WM | exact FW0]);
      assert (AGa : agrees_on (client_keeps FL CL (bv_unsigned sp)) m mm)
        by (eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact Gn | exact MU | exact WM | | lia];
            apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil])
    end.
    rename MU into MU0. rename WM into WM0. clear FW0.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply (FENTER1 _ spa).
    { split; [rewrite app_nil_r in G0; exact G0|]. rewrite Hspa. split; [exact STL|]. split; [lia|]. split; [unfold FAKE_STACK; lia|]. split; [lia|].
      split; [assumption|]. split; [exact TPE|]. split; [Z.div_mod_to_equations; lia|].
      split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
    { reflexivity. }
    { unfold ff_size, ff_class. lia. }
    { apply NF. left. reflexivity. }
    { reflexivity. }
    intros Fb s1' m2 j0 j1 j2 fjunk t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' G1 OF1 LC1 TL1 MI1 ST1 AG1 Fb0 LJ FRC SHC.
    rewrite Hspa in *. clear Hspa. subst spa.
    change (ff_size FF_CHECK_HEADER) with 128%Z in *.
    change (Z.to_nat (128 - 32)) with 96%nat in *. change (Z.to_nat (128 / 8)) with 16%nat in *.
    apply sh_zero_cells in SHC. cbn [repeat] in SHC.
    replace (ret_pc (Z_to_bv 64 555900)) with (Z_to_bv 64 555900) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G1) as [FAll FND]. (pose proof (Forall_inv FAll) as ndP__; nd_pre ndP__ 8%nat; intros FBAND' FTOP' F64 _ FRNG FSRNG _ FSWR; nd_post).
    cbn [fb_addr fb_size fst snd] in FBAND', FTOP', F64, FRNG, FSRNG, FSWR. clear FAll.
    change (Z.shiftr 128 3) with 16%Z in FSRNG, FSWR.
    band_ind FBAND' bF.
    (* [comment removed for export] *)
    apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FR; [|lia]. apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FRA; [|lia].
    apply (agrees_stk _ _ _ _ _ AG1) in STG; [|intros a Ha; left; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG1) in MG4; [|intros a Ha; eapply clocA_keeps; [exact (proj1 OMG)| exact Ha]].
    apply (agrees_rw_cells _ _ _ _ _ AG1) in HE; [|intros a Ha; eapply clocA_keeps; [exact (proj1 OERR)| exact Ha]].
    apply (agrees_rw_cells _ _ _ _ _ AG1) in HEB; [|intros a Ha; eapply clocA_keeps; [exact (proj1 OEB)| exact Ha]].
    (nd_pre (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G1 (proj1 OMG) ltac:(lia)) 4%nat; intros kM kMr kM1 kM2; nd_post).
    (nd_pre (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G1 (proj1 OERR) ltac:(lia)) 4%nat; intros kE kEr kE1 kE2; nd_post).
    (nd_pre (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G1 (proj1 OEB) ltac:(lia)) 4%nat; intros kB kBr kB1 kB2; nd_post).
    cbn [fb_addr fb_size fst snd] in kM1, kM2, kE1, kE2, kB1, kB2.
    assert (AGb : agrees_on (client_keeps FL CL (bv_unsigned sp)) m m2).
    { eapply agrees_on_trans; [exact AGa|]. eapply client_keeps_weaken; [exact AG1| lia| intros a Ha; exact Ha| apply incl_refl]. }
    assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 16 <= 0x10007fff8000
                   /\ (Fb + 128 <= 0x7fff7000 \/ Z.shiftr Fb 3 + 2147450880 + 16 <= Fb))%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    pose proof (munch_refl [(bv_unsigned sp - 208, bv_unsigned sp); (Fb, Fb + 128); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 16); (ERR, ERR + 4); (EB, EB + 256)]%Z m2) as MU.
    pose proof (wmono_refl asegs m2) as WM.
    ienterG.
    (* [comment removed for export] *)
    do 2 zstep.
    zstep. if_true_by (nez_true Fb ltac:(lia)).
    zstep.   (* [comment removed for export] *)
    burst_begin [(Fb, Fb + 128); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 16)]%Z [Fb; (Z.shiftr Fb 3 + 2147450880)%Z] MUb WMb.
    do 5 zstep. neg_lits.
    do 3 zstep.
    do 3 zstep.
    zstep. neg_lits.
    zstep.
    zstep_sh0. zstep_sh0. zstep_sh0.
    do 9 zstep.
    burst_end MUb WMb.
    (* [comment removed for export] *)
    assert (G1n : GIOA L RNG s1' (CL ++ []) FB ([(FF_CHECK_HEADER, Fb, 128%Z)] ++ FL) m2) by (rewrite app_nil_r; exact G1).
    assert (FW : Forall (own_ivA [(FF_CHECK_HEADER, Fb, 128%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(bv_unsigned sp - 208, bv_unsigned sp); (Fb, Fb + 128); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 16)]%Z) by own_ivs.
    assert (FX : Forall (cobj_iv FL CL) [(ERR, ERR + 4); (EB, EB + 256)]%Z) by cobj_ivs.
    assert (FXB : Forall (fun iv : Z * Z => ablk (fst iv) (snd iv)) [(ERR, ERR + 4); (EB, EB + 256)]%Z)
      by (apply Forall_cons; [exact ERBAND'| apply Forall_cons; [exact EBBAND'| apply Forall_nil]]).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ _ _ FW FX G1n MU WM ltac:(lia)) as [G2 AG2];
      assert (AGsh : agrees_on (in_frame_sh FL) m mm)
        by (eapply agrees_on_trans; [exact (keeps_frame_sh _ _ _ _ _ AGb)|]; exact (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G1 (incl_tl _ (incl_refl _)) AG2 FXB))
    end.
    (pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OERR G2 (incl_appl _ (incl_refl _)) (incl_tl _ (incl_refl _)) AGsh ltac:(lia)) as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ ERUNP ERRNG ERRSH _; nd_post).
    (pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OMG G2 (incl_appl _ (incl_refl _)) (incl_tl _ (incl_refl _)) AGsh ltac:(lia)) as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ MGUNP MGRNG MGRSH _; nd_post).
    (* [comment removed for export] *)
    unfold b8 in *.
    assert (RSP88 : rng RNG SPA 88) by (eapply rng_sub'; [exact RSPA| lia]).
    assert (SPALO : (17594333495296 <= SPA)%Z) by (atop_facts; lia).
    call magic_load_seq; [try eassumption .. | ]; [lia .. | ].
    lazymatch goal with HH : rw_cells asegs _ SPA _ |- _ => rename HH into FRA end.
    lazymatch goal with HH : rw_cells asegs _ ERR _ |- _ => rename HH into HE end.
    pose proof (magic_sx_range mg0 mg1 mg2 mg3 GM0 GM1 GM2 GM3) as WR.
    set (W := magic_sx mg0 mg1 mg2 mg3) in *.
    (* [comment removed for export] *)
    clear G2 AG2 AGsh.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ _ _ FW FX G1n MU WM ltac:(lia)) as [G5 AG5] end.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AGm : agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ outside [(ERR, ERR + 4); (EB, EB + 256)]%Z a) m mm)
        by (eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGb|]; intros a (K & _); exact K| exact AG5]) end.
    assert (CTX : chk_ctx TP ra sp tp s0 L RNG CL FB FL trC lo MG FA EB ERR SPA Fb f [mg0; mg1; mg2; mg3] m).
    { unfold chk_ctx, PCAP_L2_STACK. do 5 (split; [first [assumption | lia]|]).
      split; [split; [exact RSTK| split; [exact RIMG| split; [exact RISH| exact RTLS]]]|].
      repeat (split; [first [assumption | reflexivity | lia]|]). first [assumption | lia]. }
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (INV : chk_inv GIOA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L RNG CL FB FL lo MG EB ERR SPA Fb [mg0; mg1; mg2; mg3] (ps_outfile s) m RNG s1' [] mm)
        by (unfold chk_inv, chk_shadow; split; [apply fp_le_refl|]; split; [exact G5|]; repeat (split; [first [assumption | reflexivity]|]); assumption) end.
    pose proof (magic_cases mg0 mg1 mg2 mg3 GM0 GM1 GM2 GM3) as CASES. cbv zeta in CASES.
    destruct CASES as [C1' | [C2' | [C3' | [C4' | [C5' | [C6' | [NM1 NM2]]]]]]].
    7:{ (* [comment removed for export] *)
      pose proof (magic_none mg0 mg1 mg2 mg3 GM0 GM1 GM2 GM3 NM1 NM2) as NN. cbv zeta in NN. fold W in NN. (nd_pre NN 6%nat; intros N1 N2 N3 N4 N5 N6; nd_post).
      neg_lits. zstep.
      if_cases K1; [zify_cond K1; exfalso; lia|].
      do 3 zstep. neg_lits.
      if_cases K2; [zify_cond K2; exfalso; lia|].
      do 3 zstep. neg_lits.
      if_cases K3; [|zify_cond K3; exfalso; lia].
      eapply evtF_cut; [eapply magic_swap_seq; lia|]. cbv beta. intros ms' PO. destruct_exs PO. subst ms'.
      zstep.
      if_cases K4; [zify_cond K4; exfalso; lia|].
      do 4 zstep.
      if_cases K5; [zify_cond K5; exfalso; lia|].
      do 4 zstep.
      if_cases K6; [zify_cond K6; exfalso; lia|].
      zstep.
      apply evtF_done. rewrite NM1, NM2. cbv beta iota zeta. cbn [negb]. cbv beta iota zeta.
      subst POSTQ0 POSTQ.
      eapply (chk_exit FO GIOA TP fflagA GL FRET) with (fcs := [CB 96 fjunk]) (r := CH_NotMe);
        [exact CTX | exact INV | exact FRA | reflexivity | exact FRC | reflexivity | exact HE |].
      cbn [chk_result]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exists ej; exact HEB. }
    (* [comment removed for export] *)
    1:{ (destruct C1' as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); destruct ndR2__ as (-> & ndR3__); revert ndR3__; intros ->). subst W. change (magic_sx 212 195 178 161) with 18446744072127431636%Z.
      neg_lits. zstep. if_false.
      do 3 zstep. neg_lits. if_true.
      apply evtF_done.
      lazymatch goal with |- implMG _ ?c _ _ _ => change c with (chk_rest MOps (prims HO FO sites) f 0 TCPDUMP_MAGIC false) end.
      subst POSTQ0 POSTQ.
      lazymatch goal with |- implMG _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (CHK_TAIL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL trC lo MG FA EB ERR SPA Fb f [212; 195; 178; 161]%Z m RNG s1' mm) with (mi := TCPDUMP_MAGIC) (sw := false);
        [exact CTX | exact INV | left; reflexivity | exact LJ | exact FRA | exact FRC | exact HE | exact HEB] end. }
    1:{ (destruct C2' as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); destruct ndR2__ as (-> & ndR3__); revert ndR3__; intros ->). subst W. change (magic_sx 52 205 178 161) with 18446744072127434036%Z.
      neg_lits. zstep. if_false.
      do 3 zstep. neg_lits. if_false.
      do 3 zstep. neg_lits. if_false.
      apply evtF_done.
      lazymatch goal with |- implMG _ ?c _ _ _ => change c with (chk_rest MOps (prims HO FO sites) f 0 KUZNETZOV_TCPDUMP_MAGIC false) end.
      subst POSTQ0 POSTQ.
      lazymatch goal with |- implMG _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (CHK_TAIL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL trC lo MG FA EB ERR SPA Fb f [52; 205; 178; 161]%Z m RNG s1' mm) with (mi := KUZNETZOV_TCPDUMP_MAGIC) (sw := false);
        [exact CTX | exact INV | right; left; reflexivity | exact LJ | exact FRA | exact FRC | exact HE | exact HEB] end. }
    1:{ (destruct C3' as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); destruct ndR2__ as (-> & ndR3__); revert ndR3__; intros ->). subst W. change (magic_sx 77 60 178 161) with 18446744072127396941%Z.
      neg_lits. zstep. if_true.
      apply evtF_done.
      lazymatch goal with |- implMG _ ?c _ _ _ => change c with (chk_rest MOps (prims HO FO sites) f 0 NSEC_TCPDUMP_MAGIC false) end.
      subst POSTQ0 POSTQ.
      lazymatch goal with |- implMG _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (CHK_TAIL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL trC lo MG FA EB ERR SPA Fb f [77; 60; 178; 161]%Z m RNG s1' mm) with (mi := NSEC_TCPDUMP_MAGIC) (sw := false);
        [exact CTX | exact INV | right; right; reflexivity | exact LJ | exact FRA | exact FRC | exact HE | exact HEB] end. }
    1:{ (destruct C4' as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); destruct ndR2__ as (-> & ndR3__); revert ndR3__; intros ->). subst W. change (magic_sx 161 178 195 212) with 18446744072984179361%Z.
      neg_lits. zstep. if_false.
      do 3 zstep. neg_lits. if_false.
      do 3 zstep. neg_lits. if_true.
      sf_old_zstep.   (* [comment removed for export] *)
      do 14 zstep. neg_lits.
      zstep. if_true.
      do 2 zstep.
      apply evtF_done.
      lazymatch goal with |- implMG _ ?c _ _ _ => change c with (chk_rest MOps (prims HO FO sites) f 0 TCPDUMP_MAGIC true) end.
      subst POSTQ0 POSTQ.
      lazymatch goal with |- implMG _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (CHK_TAIL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL trC lo MG FA EB ERR SPA Fb f [161; 178; 195; 212]%Z m RNG s1' mm) with (mi := TCPDUMP_MAGIC) (sw := true);
        [exact CTX | exact INV | left; reflexivity | exact LJ | exact FRA | exact FRC | exact HE | exact HEB] end. }
    1:{ (destruct C5' as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); destruct ndR2__ as (-> & ndR3__); revert ndR3__; intros ->). subst W. change (magic_sx 161 178 205 52) with 885895841%Z.
      neg_lits. zstep. if_false.
      do 3 zstep. neg_lits. if_false.
      do 3 zstep. neg_lits. if_true.
      sf_old_zstep.   (* [comment removed for export] *)
      do 14 zstep. neg_lits.
      zstep. if_false.
      do 4 zstep. if_false.
      do 4 zstep. if_true.
      apply evtF_done.
      lazymatch goal with |- implMG _ ?c _ _ _ => change c with (chk_rest MOps (prims HO FO sites) f 0 KUZNETZOV_TCPDUMP_MAGIC true) end.
      subst POSTQ0 POSTQ.
      lazymatch goal with |- implMG _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (CHK_TAIL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL trC lo MG FA EB ERR SPA Fb f [161; 178; 205; 52]%Z m RNG s1' mm) with (mi := KUZNETZOV_TCPDUMP_MAGIC) (sw := true);
        [exact CTX | exact INV | right; left; reflexivity | exact LJ | exact FRA | exact FRC | exact HE | exact HEB] end. }
    1:{ (destruct C6' as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); destruct ndR2__ as (-> & ndR3__); revert ndR3__; intros ->). subst W. change (magic_sx 161 178 60 77) with 1295823521%Z.
      neg_lits. zstep. if_false.
      do 3 zstep. neg_lits. if_false.
      do 3 zstep. neg_lits. if_true.
      sf_old_zstep.   (* [comment removed for export] *)
      do 14 zstep. neg_lits.
      zstep. if_false.
      do 4 zstep. if_true.
      apply evtF_done.
      lazymatch goal with |- implMG _ ?c _ _ _ => change c with (chk_rest MOps (prims HO FO sites) f 0 NSEC_TCPDUMP_MAGIC true) end.
      subst POSTQ0 POSTQ.
      lazymatch goal with |- implMG _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (CHK_TAIL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG s CL FB FL trC lo MG FA EB ERR SPA Fb f [161; 178; 60; 77]%Z m RNG s1' mm) with (mi := NSEC_TCPDUMP_MAGIC) (sw := true);
        [exact CTX | exact INV | right; right; reflexivity | exact LJ | exact FRA | exact FRC | exact HE | exact HEB] end. }
  Qed.
  End Sz2.
  Theorem pcap_check_header_proofA : ltac:(let t := eval cbv delta [pcap_check_header_proofA__stmt] in pcap_check_header_proofA__stmt in exact t).
  Proof using CHK_TAIL FENTER1 FRET GL. red. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL trC lo MG FA EB ERR f magic ej ec fuel. ltac2:(SecDiet.SzSec.closeP 'pcap_check_header_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Chk.
End CANSEC1.
End TwB.
