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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac join_a0 OK V ::=
  cbv beta delta [mkR];
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
      eapply (evtF_cut segs RNG (fun ms' => ms' = MS (bvmap_set (Z_to_bv 5 10) V R) F (Z_to_bv 64 OK) fc rv m ro));
      [ try (lazymatch goal with |- evtF ?s ?r ?Q' ?st => let QQ := fresh "QQj" in pose (QQ := Q'); change Q' with QQ end)
      | let ms' := fresh "ms'" in let H := fresh "Hj" in intros ms' H; subst ms'; simp_regs ]
  end.
Local Ltac join_done ::= apply evtF_done; lazymatch goal with |- ?q _ => tryif is_var q then unfold q else idtac end; simp_regs; reflexivity.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac sl_store_extra m m' a bs n Hn Ha Hl CH ::= sl_store_extra_std m m' a bs n Hn Ha Hl CH.   (* [comment removed for export] *)
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

(* [comment removed for export] *)
Local Ltac nlb_hyp A :=
  repeat match goal with
  | H : rw_cells _ _ A ?cs |- _ =>
      match cs with context [C1 (Z_to_bv 8 ?z)] =>
        is_Zlit z; let z' := eval vm_compute in (Z.modulo z 256) in
        tryif constr_eq z z' then fail else
        replace (Z_to_bv 8 z) with (Z_to_bv 8 z') in H by (apply (proj2 (bv_eq _ _ _)); reflexivity)
      end
  end.
Local Ltac mem_after_store_opt ::=
  norm_lit_store_bytes;
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store; try nlb_hyp A
      | _ => idtac
      end
  | _ => idtac
  end.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NextEx.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FENTER1 : fenter_stmt_o FO GIOA fflagA 1 STACK_MALLOC_1.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis OREAD : offline_read_stmt HO FO sites GIOA TP.

  Definition next_ex_proofA__stmt : Prop := pcap_next_ex_stmt HO FO sites GIOA TP.
  Section Sz2.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CLc PB FB FL trC lo P HP PKT p fuel hc pkc : ltac2:(SecDiet.SzSec.tyM 'next_ex_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma next_ex_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'next_ex_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FENTER1 FRET GL OREAD.
 intros PRE UC TR NF PC -> -> -> HHP Hhc HPK Hpk OHP OPK D1 AH AK.
    destruct TR as (TR1 & TR2).
    (nd_pre PRE 12%nat; intros G ST LO BU SPT MI TPE ALN RSTK RIMG RISH RTLS; nd_post).
    assert (RSPW : rng RNG lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| unfold PCAP_L4_STACK in BU; lia]).   (* [comment removed for export] *)
    pose proof (PCAPR_self_in _ _ _ _ _ PC) as HinP.
    (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinP)) as ndP__; nd_pre ndP__ 3%nat; intros (PBAND & P3 & PTOP & P2) P1 _; nd_post).
    cbn [cb_addr cb_size fst snd] in *.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as ((_ & GOT & _ & _ & SHB & SUA & _) & GSU). unfold GOT_UAR in GSU.
    pose proof (psize_pos p) as PS. unfold PCAP_L4_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (HPL : clocA FL (CLc ++ PB) HP 8) by (eapply clocA_incl; [exact (proj1 OHP)| apply incl_appl; apply incl_refl| apply incl_refl]).
    assert (PKL : clocA FL (CLc ++ PB) PKT 8) by (eapply clocA_incl; [exact (proj1 OPK)| apply incl_appl; apply incl_refl| apply incl_refl]).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G HPL) as (HPLO & HPHI). pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G PKL) as (PKLO & PKHI).
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G HPL ltac:(lia)) as HPBAND. pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G PKL ltac:(lia)) as PKBAND.
    (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (proj1 OHP) HinP ltac:(lia) ltac:(cbn [cb_size snd]; lia)) 4%nat; intros kHP kHPr kHP1 kHP2; nd_post).
    cbn [cb_addr cb_size fst snd] in kHP1, kHP2.
    pose proof HPBAND as HPBAND'. pose proof PKBAND as PKBAND'. band_ind HPBAND bH. band_ind PKBAND bK.
    band_ind PBAND bP.
    destruct (rw_cells_forget _ _ _ _ HPK) as [pkj HPc]. clear HPK. cbn [cells_size] in HPc. rewrite Hpk in HPc. change (8 + 0)%nat with 8%nat in HPc.
    destruct (rw_cells_forget _ _ _ _ HHP) as [hcj HH]. clear HHP. cbn [cells_size] in HH. rewrite Hhc in HH. change (8 + 0)%nat with 8%nat in HH.
    unfold Pcap.pcap_next_ex. cbn [mo_bind mo_ret MOps e_fenter e_fret prims]. unfold PCAP_NEXT_EX_ENTRY.
    remember (bv_unsigned sp - 96 - (bv_unsigned sp - 96) mod 32)%Z as SPA eqn:ESPA.
    assert (SPAP : (bv_unsigned sp - 112 <= SPA <= bv_unsigned sp - 96 /\ SPA mod 32 = 0 /\ (bv_unsigned sp + -96) - (bv_unsigned sp + -96) mod 32 = SPA)%Z)
      by (rewrite ESPA; Z.div_mod_to_equations; lia).
    (nd_pre SPAP 3%nat; intros SPAB SPA32 ESPA'; nd_post).
    assert (RSPA : rng RNG SPA (bv_unsigned sp - SPA)) by (eapply rng_sub'; [exact RSTK| unfold PCAP_L4_STACK in BU; lia]).   (* [comment removed for export] *)
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG.
    (* [comment removed for export] *)
    zstep.
    carve_frame 72%nat ST. carve_frame 24%nat ST.
    zstep.
    do 9 zstep.
    zstep.
    zstep.
    rewrite land_m32A by lia. rewrite ESPA'.
    release_frame FR0 ST (bv_unsigned sp + -72)%Z.
    destruct (stk_split asegs _ lo (SPA + 24) (bv_unsigned sp + -72) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve asegs _ lo (SPA + 24) 24 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
    change (Z.of_nat 24) with 24%Z in STL, FRA. replace (SPA + 24 - 24)%Z with SPA in STL, FRA by lia.
    do 3 zstep.
    do 4 zstep.
    zstep.
    replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
    zstep.
    zstep. if_false.
    do 3 zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FW : Forall (pcap_iv FL PB) [(bv_unsigned sp - 112, bv_unsigned sp)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]);
      assert (G0 : GIOA L RNG s (CLc ++ PB) FB FL mm) by (eapply (gl_frame _ _ _ GL); [exact G | exact MU | exact WM | exact FW]);
      assert (AGa : agrees_on (client_keeps FL CLc (bv_unsigned sp)) m mm)
        by (eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G | exact MU | exact WM | | lia];
            apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil])
    end.
    rename MU into MU0. rename WM into WM0. clear FW.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply (FENTER1 _ spa).
    { split; [exact G0|]. rewrite Hspa. split; [exact STL|]. split; [lia|]. split; [unfold FAKE_STACK; lia|]. split; [lia|].
      split; [assumption|]. split; [exact TPE|]. split; [Z.div_mod_to_equations; lia|].
      split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
    { reflexivity. }
    { unfold ff_size, ff_class. lia. }
    { apply NF. left. reflexivity. }
    { reflexivity. }
    intros Fb s1' m2 j0 j1 j2 fjunk t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' G1 OF1 LC1 TL1 MI1 ST1 AG1 Fb0 LJ FRC SHC.
    rewrite Hspa in *. clear Hspa. subst spa.
    change (ff_size FF_NEXT_EX) with 128%Z in *.
    change (Z.to_nat (128 - 32)) with 96%nat in *. change (Z.to_nat (128 / 8)) with 16%nat in *.
    apply sh_zero_cells in SHC. cbn [repeat] in SHC.
    replace (ret_pc (Z_to_bv 64 547300)) with (Z_to_bv 64 547300) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G1) as [FAll FND]. (pose proof (Forall_inv FAll) as ndP__; nd_pre ndP__ 8%nat; intros FBAND' FTOP' F64 _ FRNG FSRNG _ FSWR; nd_post).
    cbn [fb_addr fb_size fst snd] in FBAND', FTOP', F64, FRNG, FSRNG, FSWR. clear FAll.
    change (Z.shiftr 128 3) with 16%Z in FSRNG, FSWR.
    band_ind FBAND' bF.
    (* [comment removed for export] *)
    apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FR; [|lia]. apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FRA; [|lia].
    apply (agrees_stk _ _ _ _ _ AG1) in STG; [|intros a Ha; left; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG1) in HH; [|intros a Ha; eapply clocA_keeps; [exact HPL| exact Ha]].
    apply (agrees_rw_cells _ _ _ _ _ AG1) in HPc; [|intros a Ha; eapply clocA_keeps; [exact PKL| exact Ha]].
    (nd_pre (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G1 HPL ltac:(lia)) 4%nat; intros kH kHr kH1 kH2; nd_post).
    (nd_pre (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G1 PKL ltac:(lia)) 4%nat; intros kK kKr kK1 kK2; nd_post).
    cbn [fb_addr fb_size fst snd] in kH1, kH2, kK1, kK2.
    assert (AGb : agrees_on (client_keeps FL CLc (bv_unsigned sp)) m m2).
    { eapply agrees_on_trans; [exact AGa|]. eapply client_keeps_weaken; [exact AG1| lia| intros a Ha; apply in_block_app; left; exact Ha| apply incl_refl]. }
    assert (PC2 : PCAPR P p PB FB m2).
    { eapply PCAPR_agree; [exact AG1| intros a Ha; right; left; apply in_block_app; right; exact Ha|].
      eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU0| exact WM0| intros a _ Ho; exact Ho]| | exact PC].
      intros a Ha. pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G ltac:(apply in_block_app; left; apply in_block_app; right; exact Ha)).
      cbn [outside]. lia. }
    assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 16 <= 0x10007fff8000
                   /\ (Fb + 128 <= 0x7fff7000 \/ Z.shiftr Fb 3 + 2147450880 + 16 <= Fb))%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (Fb, Fb + 128); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 16); (HP, HP + 8)]%Z m2) as MU.
    pose proof (wmono_refl asegs m2) as WM.
    ienterG.
    (* [comment removed for export] *)
    do 4 zstep.
    if_true_by (nez_true Fb ltac:(lia)).
    burst_begin [(SPA, SPA + 24); (Fb, Fb + 128); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 16)]%Z [SPA; Fb; (Z.shiftr Fb 3 + 2147450880)%Z] MUb WMb.
    do 8 zstep. neg_lits.
    do 3 zstep.
    zstep. neg_lits.
    zstep.
    do 2 zstep.
    zstep. neg_lits.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with SH : rw_cells asegs mx (Z.shiftr Fb 3 + 2147450880)%Z _ |- _ =>
      pose proof (rw_cells_store_ok asegs mx _ _ 0%nat _ 1%nat SH ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as SOK end end.
    zstep. clear SOK. do 3 zstep.
    zstep.
    do 8 zstep.
    burst_end MUb WMb.
    (* [comment removed for export] *)
    zstep.
    do 3 zstep.
    (* [comment removed for export] *)
    assert (FW : Forall (own_ivA [(FF_NEXT_EX, Fb, 128%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(bv_unsigned sp - 112, bv_unsigned sp); (Fb, Fb + 128); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 16)]%Z) by own_ivs.
    assert (FX : Forall (cobj_iv FL CLc) [(HP, HP + 8)]%Z) by cobj_ivs.
    assert (FXB : Forall (fun iv : Z * Z => ablk (fst iv) (snd iv)) [(HP, HP + 8)]%Z) by (apply Forall_cons; [exact HPBAND'| apply Forall_nil]).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ _ _ (Forall_impl _ (own_ivA_PB _ PB _) FW) FX G1 MU WM ltac:(lia)) as [G2 AG2];
      assert (PC3 : PCAPR P p PB FB mm)
        by (eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU| exact WM| intros a _ Ho; exact Ho]| exact (pb_outside _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ FW FX G1) | exact PC2]);
      assert (AGsh : agrees_on (in_frame_sh FL) m mm)
        by (eapply agrees_on_trans; [exact (keeps_frame_sh _ _ _ _ _ AGb)|]; exact (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G1 (incl_tl _ (incl_refl _)) AG2 FXB))
    end.
    (pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OHP G2 (incl_appl _ (incl_refl _)) (incl_tl _ (incl_refl _)) AGsh ltac:(lia)) as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ HPUNP HPRNG HPRSH _; nd_post).
    replace (HP - HP mod 8)%Z with HP in HPRSH by lia. replace (8 + HP mod 8)%Z with 8%Z in HPRSH by lia.
    (pose proof PC3 as ndP__; nd_pre ndP__ 3%nat; intros Af HinF (B & Ib & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF); nd_post).
    (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G2 ltac:(apply in_or_app; left; apply in_or_app; right; exact HinP)) as ndP__; nd_pre ndP__ 6%nat; intros _ _ PUNP PRNG PRSH _; nd_post).
    (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G2 ltac:(apply in_or_app; right; exact HinF)) as ndP__; nd_pre ndP__ 3%nat; intros (FBAND & F3 & FTOP & F2) F1 _; nd_post).
    cbn [cb_addr cb_size fst snd] in PUNP, PRNG, PRSH, FBAND, F3, FTOP, F2, F1.
    apply pcap_cells_split4 in CELLS as (CA & CE & CH & CO); [|reflexivity].
    hide BUF. hide PRIV. hide IFS. hide CE. hide CH.
    unfold pc_pre, PCAP_PRIV_OFF in CA. unfold pc_ops in CO.
    ck0_at HPUNP HP; ck_go.
    do 2 zstep.
    ck0 PUNP; ck_go.
    do 3 zstep. if_false_by (eqz_false Af ltac:(lia)).
    zstep.
    ck0 PUNP; ck_go.
    do 2 zstep.
    zstep.
    (* [comment removed for export] *)
    clear G2 AG2 PC3 AGsh.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ _ _ (Forall_impl _ (own_ivA_PB _ PB _) FW) FX G1 MU WM ltac:(lia)) as [G3 AG3];
      assert (PC4 : PCAPR P p PB FB mm)
        by (eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU| exact WM| intros a _ Ho; exact Ho]| exact (pb_outside _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ FW FX G1) | exact PC2]);
      assert (AGsh : agrees_on (in_frame_sh FL) m mm)
        by (eapply agrees_on_trans; [exact (keeps_frame_sh _ _ _ _ _ AGb)|]; exact (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G1 (incl_tl _ (incl_refl _)) AG3 FXB));
      assert (UC3 : ucallerA depth_pcap_next_ex L mm sp s0 ra trC)
        by (eapply ucaller_keep; [exact UC| lia|]; intros a Ha;
            destruct (AGb a ltac:(lia) ltac:(left; lia)) as [E1 _]; destruct (AG3 a ltac:(lia) ltac:(split; [left; lia| cbn [outside]; lia])) as [E2 _]; congruence)
    end.
    pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OPK G3 (incl_appl _ (incl_refl _)) (incl_tl _ (incl_refl _)) AGsh ltac:(lia)) as OPK3.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G3) as [FAll3 _]. pose proof (Forall_inv FAll3) as FRM3. clear FAll3.
    pose proof (rw_cells_nth_C8 _ _ _ 7%nat _ FR eq_refl) as BS0. pose proof (rw_cells_nth_C8 _ _ _ 8%nat _ FR eq_refl) as BRA.
    cbn [firstn cells_size csize Nat.add] in BS0, BRA.
    replace (bv_unsigned sp + -72 + Z.of_nat 56)%Z with (bv_unsigned sp - 16)%Z in BS0 by lia.
    replace (bv_unsigned sp + -72 + Z.of_nat 64)%Z with (bv_unsigned sp - 8)%Z in BRA by lia.
    pose proof (unp_of_sh_bytes _ _ _ 4%nat 3%nat SHC ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) eq_refl ltac:(cbn; lia)) as UNPS.
    change (8 * Z.of_nat 4)%Z with 32%Z in UNPS. change (8 * Z.of_nat 3)%Z with 24%Z in UNPS.
    destruct (rw_cells_cut _ _ _ 4 FRC) as [FRC1 FRC']. cbn [firstn skipn cells_size csize Nat.add] in FRC1, FRC'.
    destruct (rw_cells_cut _ _ _ 3 FRC') as [FRU FRC2]. cbn [firstn skipn cells_size csize Nat.add] in FRU, FRC2. clear FRC'.
    replace (Fb + Z.of_nat 32)%Z with (Fb + 32)%Z in FRU, FRC2 by lia. replace (Fb + 32 + Z.of_nat 24)%Z with (Fb + 56)%Z in FRC2 by lia. clear FRC.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply implMG_bind.
    { eapply (OREAD _ spa);
        [ split; [exact G3|]; rewrite Hspa; split; [eassumption|]; split; [lia|]; split; [unfold PCAP_L3_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | eapply (ucaller_frame _ _ _ _ _ _ _ _ _ _ 0x85af8%Z UC3); [rewrite Hspa; lia| lia| Z.div_mod_to_equations; lia| exact BS0| exact BRA
                                                            | reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_pcap_next_ex, depth_offline_read; lia]
        | rewrite unsigned_lit by lia; exact TR1
        | apply nofr_cons; [eapply nofr_sub; [exact NF| intros f Hf; cbn in Hf |- *; clear - Hf; intuition]| cbn; clear; intuition congruence]
        | exact PC4 | reflexivity | reflexivity | reflexivity | reflexivity
        | exact FRU | exact HPc | reflexivity
        | split; [right; exists (FF_NEXT_EX, Fb, 128%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]|];
          eapply frameA_aobj; [exact FRM3| cbn [fb_addr fb_size fst snd]; lia| cbn [fb_addr fb_size fst snd]; lia| lia|];
          replace (Fb + 32 + 24)%Z with (Fb + 32 + 24)%Z by lia; exact UNPS
        | split; [eapply clocA_incl; [exact (proj1 OPK3)| apply incl_refl| apply incl_tl; apply incl_refl]| exact (proj2 OPK3)]
        | lia | Z.div_mod_to_equations; lia | exact AK ]. }
    intros [st p'] s2' RNG2 ms' PO. cbv beta iota in PO.
    (nd_pre PO 14%nat; intros FP2 a0v m6 PB1 pk' E OF2 MI2 ST2 AG4 G4 PC5 PCC5 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 4%nat; intros Hst HU1 HP1 Hpk1; nd_post).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 547576)) with (Z_to_bv 64 547576) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    cbn [app] in G4, AG4.
    (* [comment removed for export] *)
    repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP2) in HR end.
    assert (FRIN : forall a, (Fb <= a < Fb + 128)%Z -> in_frames ((FF_NEXT_EX, Fb, 128%Z) :: FL) a)
      by (intros a Ha; apply in_frames_In; exists (FF_NEXT_EX, Fb, 128%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]).
    apply (agrees_rw_cells _ _ _ _ _ AG4) in FR; [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; lia| lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG4) in FRA; [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; lia| lia]].
    apply (agrees_stk _ _ _ _ _ AG4) in STG; [|intros a Ha; split; [left; lia| lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG4) in FRC1; [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [right; right; left; apply FRIN; lia| lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG4) in FRC2; [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [right; right; left; apply FRIN; lia| lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG4) in SHC;
      [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [right; right; right; apply in_frame_sh_In; exists (FF_NEXT_EX, Fb, 128%Z);
          split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; change (Z.shiftr 128 3) with 16%Z; lia]| lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG4) in HH;
      [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [eapply clocA_keeps; [eapply clocA_incl; [exact (proj1 OHP)| apply incl_refl| apply incl_tl; apply incl_refl]| lia]| lia]].
    (* [comment removed for export] *)
    pose proof (rw_cells_uncut _ _ _ _ _ FRC1 (rw_cells_uncut _ _ _ _ _ HU1 FRC2 ltac:(cbn [cells_size csize Nat.add]; lia)) ltac:(cbn [cells_size csize Nat.add]; lia)) as FRC.
    cbn [app] in FRC. clear FRC1 FRC2 HU1 FRU.
    ienterG.
    (* [comment removed for export] *)
    join_a0 0x85b38%Z (Z_to_bv 64 (if st =? 0 then -2 else st)%Z).
    { destruct Hst as [-> | [-> | ->]]; cbn [Z.eqb].
      - zstep. if_true. join_done.
      - zstep. if_false. do 2 zstep. join_done.
      - zstep. if_true. join_done. }
    (* [comment removed for export] *)
    clear FW FX FXB MU WM.
    (* [comment removed for export] *)
    clear PRNG PRSH HPRNG HPRSH RIMG RISH RTLS kHP kHPr kHP1 kHP2 bP bPr bPhi bPlo bPimg P1 P2 P3 PTOP PS F1 F2 F3 FTOP FBAND.
    assert (FW : Forall (own_ivA [(FF_NEXT_EX, Fb, 128%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(Fb, Fb + 128); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 16)]%Z) by own_ivs.
    pose proof (munch_refl [(Fb, Fb + 128); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 16)]%Z m6) as MU. pose proof (wmono_refl asegs m6) as WM.
    (nd_pre (flag_facts _ _ _ GL _ _ _ _ _ _ _ _ _ _ G4) 6%nat; intros _ FLR FLB FLT _ (kF & kFr & kF1 & kF2); nd_post). band_ind FLB bG.
    (nd_pre (flag_apart_cloc _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ _ G4 (proj1 OHP) (incl_appl _ (incl_refl _)) (incl_tl _ (incl_refl _)) ltac:(lia)) 4%nat; intros iH iHr iH1 iH2; nd_post).
    (nd_pre (flag_apart_cloc _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ _ G4 (proj1 OPK) (incl_appl _ (incl_refl _)) (incl_tl _ (incl_refl _)) ltac:(lia)) 4%nat; intros iK iKr iK1 iK2; nd_post).
    zstep. neg_lits.
    do 3 zstep.
    do 3 zstep.
    zstep. if_false_by (eqz_false Fb ltac:(lia)).
    zstep. neg_lits.
    burst_begin [(Fb, Fb + 128); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 16)]%Z [Fb; (Z.shiftr Fb 3 + 2147450880)%Z] MUb WMb.
    do 4 zstep. zstep_sh0. do 11 zstep.
    burst_end MUb WMb.
    zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ [] _ (Forall_impl _ (own_ivA_PB _ PB1 _) FW) (Forall_nil _) G4 MU WM ltac:(lia)) as [G5 AG5];
      assert (AGP5 : agrees_on (fun a => in_block PB1 a) m6 mm)
        by (eapply agrees_on_of_munch; [exact MU| exact WM|]; intros a _ Ha; exact (pb_outside _ _ _ GL _ _ _ _ _ _ _ _ _ _ [] _ FW (Forall_nil _) G4 a Ha));
      pose proof (munch_refl [(fflagA L FF_NEXT_EX Fb, fflagA L FF_NEXT_EX Fb + 1)]%Z mm) as MU2; pose proof (wmono_refl asegs mm) as WM2
    end.
    (nd_pre (flag_facts _ _ _ GL _ _ _ _ _ _ _ _ _ _ G5) 6%nat; intros FLC _ _ _ FLNB _; nd_post).
    clear MU WM.
    zstep.
    apply evtF_done. eapply FRET; [exact G5 | unfold ff_class; lia | exact MU2 | exact WM2 | exact FLC |].
    intros s3' G6 OF3 LC3 TL3.
    clear FRNG FSRNG FLR kH kHr kH1 kH2 kK kKr kK1 kK2 iH iHr iH1 iH2 iK iKr iK1 iK2 bH bHr bHhi bHlo bHimg bK bKr bKhi bKlo bKimg bG bGr bGhi bGlo bGimg SHLO.
    zstep.
    do 12 zstep.
    (* [comment removed for export] *)
    clear STL ST1.
    release_frame FRA ST2 (SPA + 24)%Z.
    pose proof (stk_merge asegs _ _ _ _ ST2 STG ltac:(lia)) as ST3. clear ST2 STG.
    release_frame FR ST3 (bv_unsigned sp).
    destruct (flag_keeps _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ CLc (bv_unsigned sp) G5 MU2 WM2 (incl_appl _ (incl_refl _)) ltac:(lia)) as [AG6 AGP6].
    apply evtF_done. subst POSTQ1 POSTQ0 POSTQ. cbv beta iota.
    split; [exact FP2|].
    lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 (if st =? 0 then -2 else st)%Z), mm, PB1, pk' end.
    split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
    split; [congruence|]. split; [assumption|]. split; [exact ST3|].
    split.
    { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGb|]; intros a (K & _ & _); exact K|].
      eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG3|]; intros a (K & NH & _); split; [exact K| cbn [outside]; split; [exact NH| exact I]]|].
      eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG4|]; intros a (K & _ & NK); split; [| exact NK];
                               destruct K as [K|[K|[K|K]]]; [left; lia| right; left; exact K| right; right; left; apply in_frames_cons; exact K
                                                            | right; right; right; apply in_frame_sh_cons; exact K]|].
      eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG5|]; intros a (K & _); split; [exact K| exact I]|].
      eapply agrees_on_weaken; [exact AG6|]. intros a (K & _); exact K. }
    split; [exact G6|].
    assert (PBIN : forall a, in_block PB1 a -> in_block (CLc ++ PB1) a) by (intros a Ha; apply in_block_app; right; exact Ha).
    split. { intros Hne. eapply PCAPR_agree; [exact AGP6| exact PBIN|]. eapply PCAPR_agree; [exact AGP5| intros a Ha; exact Ha|].
             apply PC5. destruct Hst as [-> | [-> | ->]]; cbn [Z.eqb] in Hne; lia. }
    split. { intros He. eapply PCAPR_closable_agree; [exact AGP6| exact PBIN|]. eapply PCAPR_closable_agree; [exact AGP5| intros a Ha; exact Ha|].
             apply PCC5. destruct Hst as [-> | [-> | ->]]; cbn [Z.eqb] in He; lia. }
    split; [reflexivity|].
    split. { destruct Hst as [-> | [-> | ->]]; cbn [Z.eqb]; [left| right; left| right; right]; reflexivity. }
    split; [exact HH|]. split; [exact HP1| exact Hpk1].
  Qed.
  End Sz2.
  Theorem next_ex_proofA : ltac:(let t := eval cbv delta [next_ex_proofA__stmt] in next_ex_proofA__stmt in exact t).
  Proof using FENTER1 FRET GL OREAD. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CLc PB FB FL trC lo P HP PKT p fuel hc pkc. ltac2:(SecDiet.SzSec.closeP 'next_ex_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NextEx.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac join_a0 OK V ::=
  cbv beta delta [mkR];
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
      eapply (evtF_cut segs RNG (fun ms' => ms' = MS (bvmap_set (Z_to_bv 5 10) V R) F (Z_to_bv 64 OK) fc rv m ro));
      [ try (lazymatch goal with |- evtF ?s ?r ?Q' ?st => let QQ := fresh "QQj" in pose (QQ := Q'); change Q' with QQ end)
      | let ms' := fresh "ms'" in let H := fresh "Hj" in intros ms' H; subst ms'; simp_regs ]
  end.
Local Ltac join_done ::= apply evtF_done; lazymatch goal with |- ?q _ => tryif is_var q then unfold q else idtac end; simp_regs; reflexivity.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac sl_store_extra m m' a bs n Hn Ha Hl CH ::= sl_store_extra_std m m' a bs n Hn Ha Hl CH.   (* [comment removed for export] *)
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

(* [comment removed for export] *)
Local Ltac nlb_hyp A :=
  repeat match goal with
  | H : rw_cells _ _ A ?cs |- _ =>
      match cs with context [C1 (Z_to_bv 8 ?z)] =>
        is_Zlit z; let z' := eval vm_compute in (Z.modulo z 256) in
        tryif constr_eq z z' then fail else
        replace (Z_to_bv 8 z) with (Z_to_bv 8 z') in H by (apply (proj2 (bv_eq _ _ _)); reflexivity)
      end
  end.
Local Ltac mem_after_store_opt ::=
  norm_lit_store_bytes;
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store; try nlb_hyp A
      | _ => idtac
      end
  | _ => idtac
  end.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NextEx.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis FENTER1 : fenter_stmt_o FO GIOA fflagA 1 STACK_MALLOC_1.
  Hypothesis FRET : fret_inline_law FO GIOA fflagA.
  Hypothesis OREAD : offline_read_stmt HO FO sites GIOA TP.

  Definition next_ex_proofA__stmt : Prop := pcap_next_ex_stmt HO FO sites GIOA TP.
  Section Sz2.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CLc PB FB FL trC lo P HP PKT p fuel hc pkc : ltac2:(SecDiet.SzSec.tyM 'next_ex_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma next_ex_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'next_ex_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FENTER1 FRET GL OREAD.
 intros PRE UC TR NF PC -> -> -> HHP Hhc HPK Hpk OHP OPK D1 AH AK.
    destruct TR as (TR1 & TR2).
    (nd_pre PRE 12%nat; intros G ST LO BU SPT MI TPE ALN RSTK RIMG RISH RTLS; nd_post).
    assert (RSPW : rng RNG lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| unfold PCAP_L4_STACK in BU; lia]).   (* [comment removed for export] *)
    pose proof (PCAPR_self_in _ _ _ _ _ PC) as HinP.
    (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G ltac:(apply in_or_app; left; apply in_or_app; right; exact HinP)) as ndP__; nd_pre ndP__ 3%nat; intros (PBAND & P3 & PTOP & P2) P1 _; nd_post).
    cbn [cb_addr cb_size fst snd] in *.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as ((_ & GOT & _ & _ & SHB & SUA & _) & GSU). unfold GOT_UAR in GSU.
    pose proof (psize_pos p) as PS. unfold PCAP_L4_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (HPL : clocA FL (CLc ++ PB) HP 8) by (eapply clocA_incl; [exact (proj1 OHP)| apply incl_appl; apply incl_refl| apply incl_refl]).
    assert (PKL : clocA FL (CLc ++ PB) PKT 8) by (eapply clocA_incl; [exact (proj1 OPK)| apply incl_appl; apply incl_refl| apply incl_refl]).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G HPL) as (HPLO & HPHI). pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G PKL) as (PKLO & PKHI).
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G HPL ltac:(lia)) as HPBAND. pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G PKL ltac:(lia)) as PKBAND.
    (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G (proj1 OHP) HinP ltac:(lia) ltac:(cbn [cb_size snd]; lia)) 4%nat; intros kHP kHPr kHP1 kHP2; nd_post).
    cbn [cb_addr cb_size fst snd] in kHP1, kHP2.
    pose proof HPBAND as HPBAND'. pose proof PKBAND as PKBAND'. band_ind HPBAND bH. band_ind PKBAND bK.
    band_ind PBAND bP.
    destruct (rw_cells_forget _ _ _ _ HPK) as [pkj HPc]. clear HPK. cbn [cells_size] in HPc. rewrite Hpk in HPc. change (8 + 0)%nat with 8%nat in HPc.
    destruct (rw_cells_forget _ _ _ _ HHP) as [hcj HH]. clear HHP. cbn [cells_size] in HH. rewrite Hhc in HH. change (8 + 0)%nat with 8%nat in HH.
    unfold Pcap.pcap_next_ex. cbn [mo_bind mo_ret MOps e_fenter e_fret prims]. unfold PCAP_NEXT_EX_ENTRY.
    remember (bv_unsigned sp - 96 - (bv_unsigned sp - 96) mod 32)%Z as SPA eqn:ESPA.
    assert (SPAP : (bv_unsigned sp - 112 <= SPA <= bv_unsigned sp - 96 /\ SPA mod 32 = 0 /\ (bv_unsigned sp + -96) - (bv_unsigned sp + -96) mod 32 = SPA)%Z)
      by (rewrite ESPA; Z.div_mod_to_equations; lia).
    (nd_pre SPAP 3%nat; intros SPAB SPA32 ESPA'; nd_post).
    assert (RSPA : rng RNG SPA (bv_unsigned sp - SPA)) by (eapply rng_sub'; [exact RSTK| unfold PCAP_L4_STACK in BU; lia]).   (* [comment removed for export] *)
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG.
    (* [comment removed for export] *)
    zstep.
    carve_frame 72%nat ST. carve_frame 24%nat ST.
    zstep.
    do 9 zstep.
    zstep.
    zstep.
    rewrite land_m32A by lia. rewrite ESPA'.
    release_frame FR0 ST (bv_unsigned sp + -72)%Z.
    destruct (stk_split asegs _ lo (SPA + 24) (bv_unsigned sp + -72) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve asegs _ lo (SPA + 24) 24 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
    change (Z.of_nat 24) with 24%Z in STL, FRA. replace (SPA + 24 - 24)%Z with SPA in STL, FRA by lia.
    do 3 zstep.
    do 4 zstep.
    zstep.
    replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
    zstep.
    zstep. if_false.
    do 3 zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FW : Forall (pcap_iv FL PB) [(bv_unsigned sp - 112, bv_unsigned sp)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]);
      assert (G0 : GIOA L RNG s (CLc ++ PB) FB FL mm) by (eapply (gl_frame _ _ _ GL); [exact G | exact MU | exact WM | exact FW]);
      assert (AGa : agrees_on (client_keeps FL CLc (bv_unsigned sp)) m mm)
        by (eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G | exact MU | exact WM | | lia];
            apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil])
    end.
    rename MU into MU0. rename WM into WM0. clear FW.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply (FENTER1 _ spa).
    { split; [exact G0|]. rewrite Hspa. split; [exact STL|]. split; [lia|]. split; [unfold FAKE_STACK; lia|]. split; [lia|].
      split; [assumption|]. split; [exact TPE|]. split; [Z.div_mod_to_equations; lia|].
      split; [exact RSTK|]. split; [exact RIMG|]. split; [exact RISH| exact RTLS]. }
    { reflexivity. }
    { unfold ff_size, ff_class. lia. }
    { apply NF. left. reflexivity. }
    { reflexivity. }
    intros Fb s1' m2 j0 j1 j2 fjunk t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' G1 OF1 LC1 TL1 MI1 ST1 AG1 Fb0 LJ FRC SHC.
    rewrite Hspa in *. clear Hspa. subst spa.
    change (ff_size FF_NEXT_EX) with 128%Z in *.
    change (Z.to_nat (128 - 32)) with 96%nat in *. change (Z.to_nat (128 / 8)) with 16%nat in *.
    apply sh_zero_cells in SHC. cbn [repeat] in SHC.
    replace (ret_pc (Z_to_bv 64 547624)) with (Z_to_bv 64 547624) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G1) as [FAll FND]. (pose proof (Forall_inv FAll) as ndP__; nd_pre ndP__ 8%nat; intros FBAND' FTOP' F64 _ FRNG FSRNG _ FSWR; nd_post).
    cbn [fb_addr fb_size fst snd] in FBAND', FTOP', F64, FRNG, FSRNG, FSWR. clear FAll.
    change (Z.shiftr 128 3) with 16%Z in FSRNG, FSWR.
    band_ind FBAND' bF.
    (* [comment removed for export] *)
    apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FR; [|lia]. apply (keeps_rw_cells_stack _ _ _ _ _ _ _ AG1) in FRA; [|lia].
    apply (agrees_stk _ _ _ _ _ AG1) in STG; [|intros a Ha; left; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG1) in HH; [|intros a Ha; eapply clocA_keeps; [exact HPL| exact Ha]].
    apply (agrees_rw_cells _ _ _ _ _ AG1) in HPc; [|intros a Ha; eapply clocA_keeps; [exact PKL| exact Ha]].
    (nd_pre (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G1 HPL ltac:(lia)) 4%nat; intros kH kHr kH1 kH2; nd_post).
    (nd_pre (clocA_apart_frame _ _ _ GL _ _ _ _ _ _ _ _ _ _ G1 PKL ltac:(lia)) 4%nat; intros kK kKr kK1 kK2; nd_post).
    cbn [fb_addr fb_size fst snd] in kH1, kH2, kK1, kK2.
    assert (AGb : agrees_on (client_keeps FL CLc (bv_unsigned sp)) m m2).
    { eapply agrees_on_trans; [exact AGa|]. eapply client_keeps_weaken; [exact AG1| lia| intros a Ha; apply in_block_app; left; exact Ha| apply incl_refl]. }
    assert (PC2 : PCAPR P p PB FB m2).
    { eapply PCAPR_agree; [exact AG1| intros a Ha; right; left; apply in_block_app; right; exact Ha|].
      eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU0| exact WM0| intros a _ Ho; exact Ho]| | exact PC].
      intros a Ha. pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G ltac:(apply in_block_app; left; apply in_block_app; right; exact Ha)).
      cbn [outside]. lia. }
    assert (SHLO : (0x7fff8000 <= Z.shiftr Fb 3 + 2147450880 /\ Z.shiftr Fb 3 + 2147450880 + 16 <= 0x10007fff8000
                   /\ (Fb + 128 <= 0x7fff7000 \/ Z.shiftr Fb 3 + 2147450880 + 16 <= Fb))%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (Fb, Fb + 128); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 16); (HP, HP + 8)]%Z m2) as MU.
    pose proof (wmono_refl asegs m2) as WM.
    ienterG.
    (* [comment removed for export] *)
    do 4 zstep.
    if_true_by (nez_true Fb ltac:(lia)).
    burst_begin [(SPA, SPA + 24); (Fb, Fb + 128); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 16)]%Z [SPA; Fb; (Z.shiftr Fb 3 + 2147450880)%Z] MUb WMb.
    (* [comment removed for export] *)
    zstep.
    do 4 zstep. zstep. neg_lits.
    do 3 zstep.
    do 3 zstep.
    zstep. neg_lits.
    zstep.
    do 4 zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with SH : rw_cells asegs mx (Z.shiftr Fb 3 + 2147450880)%Z _ |- _ =>
      pose proof (rw_cells_store_ok asegs mx _ _ 0%nat _ 1%nat SH ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as SOK end end.
    zstep. clear SOK. do 3 zstep.
    do 4 zstep.
    burst_end MUb WMb.
    (* [comment removed for export] *)
    ub_null.
    zstep. ub_al 7%Z ltac:(al16 P2). zstep. if_false.
    do 5 zstep.
    ub_null.
    zstep. ub_al 7%Z ltac:(al8 AH). zstep. if_false.
    (* [comment removed for export] *)
    assert (FW : Forall (own_ivA [(FF_NEXT_EX, Fb, 128%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(bv_unsigned sp - 112, bv_unsigned sp); (Fb, Fb + 128); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 16)]%Z) by own_ivs.
    assert (FX : Forall (cobj_iv FL CLc) [(HP, HP + 8)]%Z) by cobj_ivs.
    assert (FXB : Forall (fun iv : Z * Z => ablk (fst iv) (snd iv)) [(HP, HP + 8)]%Z) by (apply Forall_cons; [exact HPBAND'| apply Forall_nil]).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ _ _ (Forall_impl _ (own_ivA_PB _ PB _) FW) FX G1 MU WM ltac:(lia)) as [G2 AG2];
      assert (PC3 : PCAPR P p PB FB mm)
        by (eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU| exact WM| intros a _ Ho; exact Ho]| exact (pb_outside _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ FW FX G1) | exact PC2]);
      assert (AGsh : agrees_on (in_frame_sh FL) m mm)
        by (eapply agrees_on_trans; [exact (keeps_frame_sh _ _ _ _ _ AGb)|]; exact (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G1 (incl_tl _ (incl_refl _)) AG2 FXB))
    end.
    (pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OHP G2 (incl_appl _ (incl_refl _)) (incl_tl _ (incl_refl _)) AGsh ltac:(lia)) as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ HPUNP HPRNG HPRSH _; nd_post).
    replace (HP - HP mod 8)%Z with HP in HPRSH by lia. replace (8 + HP mod 8)%Z with 8%Z in HPRSH by lia.
    (pose proof PC3 as ndP__; nd_pre ndP__ 3%nat; intros Af HinF (B & Ib & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF); nd_post).
    (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G2 ltac:(apply in_or_app; left; apply in_or_app; right; exact HinP)) as ndP__; nd_pre ndP__ 6%nat; intros _ _ PUNP PRNG PRSH _; nd_post).
    (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G2 ltac:(apply in_or_app; right; exact HinF)) as ndP__; nd_pre ndP__ 3%nat; intros (FBAND & F3 & FTOP & F2) F1 _; nd_post).
    cbn [cb_addr cb_size fst snd] in PUNP, PRNG, PRSH, FBAND, F3, FTOP, F2, F1.
    apply pcap_cells_split4 in CELLS as (CA & CE & CH & CO); [|reflexivity].
    hide BUF. hide PRIV. hide IFS. hide CE. hide CH.
    unfold pc_pre, PCAP_PRIV_OFF in CA. unfold pc_ops in CO.
    ck0 HPUNP; ck_go.
    do 2 zstep.
    ck0 PUNP; ck_go.
    do 3 zstep. if_false_by (eqz_false Af ltac:(lia)).
    ck0 PUNP; ck_go.                      (* [comment removed for export] *)
    do 2 zstep.
    zstep.
    (* [comment removed for export] *)
    clear G2 AG2 PC3 AGsh.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ _ _ (Forall_impl _ (own_ivA_PB _ PB _) FW) FX G1 MU WM ltac:(lia)) as [G3 AG3];
      assert (PC4 : PCAPR P p PB FB mm)
        by (eapply PCAPR_agree; [eapply agrees_on_of_munch; [exact MU| exact WM| intros a _ Ho; exact Ho]| exact (pb_outside _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ FW FX G1) | exact PC2]);
      assert (AGsh : agrees_on (in_frame_sh FL) m mm)
        by (eapply agrees_on_trans; [exact (keeps_frame_sh _ _ _ _ _ AGb)|]; exact (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ G1 (incl_tl _ (incl_refl _)) AG3 FXB));
      assert (UC3 : ucallerA depth_pcap_next_ex L mm sp s0 ra trC)
        by (eapply ucaller_keep; [exact UC| lia|]; intros a Ha;
            destruct (AGb a ltac:(lia) ltac:(left; lia)) as [E1 _]; destruct (AG3 a ltac:(lia) ltac:(split; [left; lia| cbn [outside]; lia])) as [E2 _]; congruence)
    end.
    pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ OPK G3 (incl_appl _ (incl_refl _)) (incl_tl _ (incl_refl _)) AGsh ltac:(lia)) as OPK3.
    destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G3) as [FAll3 _]. pose proof (Forall_inv FAll3) as FRM3. clear FAll3.
    pose proof (rw_cells_nth_C8 _ _ _ 7%nat _ FR eq_refl) as BS0. pose proof (rw_cells_nth_C8 _ _ _ 8%nat _ FR eq_refl) as BRA.
    cbn [firstn cells_size csize Nat.add] in BS0, BRA.
    replace (bv_unsigned sp + -72 + Z.of_nat 56)%Z with (bv_unsigned sp - 16)%Z in BS0 by lia.
    replace (bv_unsigned sp + -72 + Z.of_nat 64)%Z with (bv_unsigned sp - 8)%Z in BRA by lia.
    pose proof (unp_of_sh_bytes _ _ _ 4%nat 3%nat SHC ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia) eq_refl ltac:(cbn; lia)) as UNPS.
    change (8 * Z.of_nat 4)%Z with 32%Z in UNPS. change (8 * Z.of_nat 3)%Z with 24%Z in UNPS.
    destruct (rw_cells_cut _ _ _ 4 FRC) as [FRC1 FRC']. cbn [firstn skipn cells_size csize Nat.add] in FRC1, FRC'.
    destruct (rw_cells_cut _ _ _ 3 FRC') as [FRU FRC2]. cbn [firstn skipn cells_size csize Nat.add] in FRU, FRC2. clear FRC'.
    replace (Fb + Z.of_nat 32)%Z with (Fb + 32)%Z in FRU, FRC2 by lia. replace (Fb + 32 + Z.of_nat 24)%Z with (Fb + 56)%Z in FRC2 by lia. clear FRC.
    remember (Z_to_bv 64 SPA) as spa eqn:Espa.
    assert (Hspa : bv_unsigned spa = SPA) by (rewrite Espa; apply unsigned_lit; lia).
    apply evtF_done. eapply implMG_bind.
    { eapply (OREAD _ spa);
        [ split; [exact G3|]; rewrite Hspa; split; [eassumption|]; split; [lia|]; split; [unfold PCAP_L3_STACK; lia|]; split; [lia|];
          split; [assumption|]; split; [exact TPE|]; split; [Z.div_mod_to_equations; lia|];
          split; [exact RSTK|]; split; [exact RIMG|]; split; [exact RISH| exact RTLS]
        | eapply (ucaller_frame _ _ _ _ _ _ _ _ _ _ 0x85c48%Z UC3); [rewrite Hspa; lia| lia| Z.div_mod_to_equations; lia| exact BS0| exact BRA
                                                            | reflexivity| unfold ACLIENT_LO, ACLIENT_HI; lia| unfold depth_pcap_next_ex, depth_offline_read; lia]
        | rewrite unsigned_lit by lia; exact TR1
        | apply nofr_cons; [eapply nofr_sub; [exact NF| intros f Hf; cbn in Hf |- *; clear - Hf; intuition]| cbn; clear; intuition congruence]
        | exact PC4 | reflexivity | reflexivity | reflexivity | reflexivity
        | exact FRU | exact HPc | reflexivity
        | split; [right; exists (FF_NEXT_EX, Fb, 128%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]|];
          eapply frameA_aobj; [exact FRM3| cbn [fb_addr fb_size fst snd]; lia| cbn [fb_addr fb_size fst snd]; lia| lia|];
          replace (Fb + 32 + 24)%Z with (Fb + 32 + 24)%Z by lia; exact UNPS
        | split; [eapply clocA_incl; [exact (proj1 OPK3)| apply incl_refl| apply incl_tl; apply incl_refl]| exact (proj2 OPK3)]
        | lia | Z.div_mod_to_equations; lia | exact AK ]. }
    intros [st p'] s2' RNG2 ms' PO. cbv beta iota in PO.
    (nd_pre PO 14%nat; intros FP2 a0v m6 PB1 pk' E OF2 MI2 ST2 AG4 G4 PC5 PCC5 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 4%nat; intros Hst HU1 HP1 Hpk1; nd_post).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hspa in *. clear Hspa. subst spa.
    replace (ret_pc (Z_to_bv 64 547912)) with (Z_to_bv 64 547912) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    cbn [app] in G4, AG4.
    (* [comment removed for export] *)
    repeat match goal with HR : rng RNG _ _ |- _ => apply (rng_fp_le _ _ _ _ FP2) in HR end.
    assert (FRIN : forall a, (Fb <= a < Fb + 128)%Z -> in_frames ((FF_NEXT_EX, Fb, 128%Z) :: FL) a)
      by (intros a Ha; apply in_frames_In; exists (FF_NEXT_EX, Fb, 128%Z); split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; lia]).
    apply (agrees_rw_cells _ _ _ _ _ AG4) in FR; [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; lia| lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG4) in FRA; [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; lia| lia]].
    apply (agrees_stk _ _ _ _ _ AG4) in STG; [|intros a Ha; split; [left; lia| lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG4) in FRC1; [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [right; right; left; apply FRIN; lia| lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG4) in FRC2; [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [right; right; left; apply FRIN; lia| lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG4) in SHC;
      [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [right; right; right; apply in_frame_sh_In; exists (FF_NEXT_EX, Fb, 128%Z);
          split; [left; reflexivity| cbn [fb_addr fb_size fst snd]; change (Z.shiftr 128 3) with 16%Z; lia]| lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG4) in HH;
      [|intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [eapply clocA_keeps; [eapply clocA_incl; [exact (proj1 OHP)| apply incl_refl| apply incl_tl; apply incl_refl]| lia]| lia]].
    (* [comment removed for export] *)
    pose proof (rw_cells_uncut _ _ _ _ _ FRC1 (rw_cells_uncut _ _ _ _ _ HU1 FRC2 ltac:(cbn [cells_size csize Nat.add]; lia)) ltac:(cbn [cells_size csize Nat.add]; lia)) as FRC.
    cbn [app] in FRC. clear FRC1 FRC2 HU1 FRU.
    ienterG.
    (* [comment removed for export] *)
    join_a0 0x85c84%Z (Z_to_bv 64 (if st =? 0 then -2 else st)%Z).
    { destruct Hst as [-> | [-> | ->]]; cbn [Z.eqb].
      - zstep. if_true. join_done.
      - zstep. if_false. do 2 zstep. join_done.
      - zstep. if_true. join_done. }
    (* [comment removed for export] *)
    clear FW FX FXB MU WM.
    (* [comment removed for export] *)
    clear PRNG PRSH HPRNG HPRSH RIMG RISH RTLS kHP kHPr kHP1 kHP2 bP bPr bPhi bPlo bPimg P1 P2 P3 PTOP PS F1 F2 F3 FTOP FBAND.
    assert (FW : Forall (own_ivA [(FF_NEXT_EX, Fb, 128%Z)] ([] : list (@cblock hptr)) (bv_unsigned sp))
                   [(Fb, Fb + 128); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 16)]%Z) by own_ivs.
    pose proof (munch_refl [(Fb, Fb + 128); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 16)]%Z m6) as MU. pose proof (wmono_refl asegs m6) as WM.
    (nd_pre (flag_facts _ _ _ GL _ _ _ _ _ _ _ _ _ _ G4) 6%nat; intros _ FLR FLB FLT _ (kF & kFr & kF1 & kF2); nd_post). band_ind FLB bG.
    (nd_pre (flag_apart_cloc _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ _ G4 (proj1 OHP) (incl_appl _ (incl_refl _)) (incl_tl _ (incl_refl _)) ltac:(lia)) 4%nat; intros iH iHr iH1 iH2; nd_post).
    (nd_pre (flag_apart_cloc _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ _ G4 (proj1 OPK) (incl_appl _ (incl_refl _)) (incl_tl _ (incl_refl _)) ltac:(lia)) 4%nat; intros iK iKr iK1 iK2; nd_post).
    zstep. neg_lits.
    do 3 zstep.
    do 3 zstep.
    zstep. if_false_by (eqz_false Fb ltac:(lia)).
    zstep. neg_lits.
    burst_begin [(Fb, Fb + 128); (Z.shiftr Fb 3 + 2147450880, Z.shiftr Fb 3 + 2147450880 + 16)]%Z [Fb; (Z.shiftr Fb 3 + 2147450880)%Z] MUb WMb.
    do 4 zstep. zstep_sh0. do 11 zstep.
    burst_end MUb WMb.
    zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (own_writes _ _ _ GL _ _ _ _ _ _ _ _ _ mm _ [] _ (Forall_impl _ (own_ivA_PB _ PB1 _) FW) (Forall_nil _) G4 MU WM ltac:(lia)) as [G5 AG5];
      assert (AGP5 : agrees_on (fun a => in_block PB1 a) m6 mm)
        by (eapply agrees_on_of_munch; [exact MU| exact WM|]; intros a _ Ha; exact (pb_outside _ _ _ GL _ _ _ _ _ _ _ _ _ _ [] _ FW (Forall_nil _) G4 a Ha));
      pose proof (munch_refl [(fflagA L FF_NEXT_EX Fb, fflagA L FF_NEXT_EX Fb + 1)]%Z mm) as MU2; pose proof (wmono_refl asegs mm) as WM2
    end.
    (nd_pre (flag_facts _ _ _ GL _ _ _ _ _ _ _ _ _ _ G5) 6%nat; intros FLC _ _ _ FLNB _; nd_post).
    clear MU WM.
    zstep.
    apply evtF_done. eapply FRET; [exact G5 | unfold ff_class; lia | exact MU2 | exact WM2 | exact FLC |].
    intros s3' G6 OF3 LC3 TL3.
    clear FRNG FSRNG FLR kH kHr kH1 kH2 kK kKr kK1 kK2 iH iHr iH1 iH2 iK iKr iK1 iK2 bH bHr bHhi bHlo bHimg bK bKr bKhi bKlo bKimg bG bGr bGhi bGlo bGimg SHLO.
    zstep.
    do 12 zstep.
    (* [comment removed for export] *)
    clear STL ST1.
    release_frame FRA ST2 (SPA + 24)%Z.
    pose proof (stk_merge asegs _ _ _ _ ST2 STG ltac:(lia)) as ST3. clear ST2 STG.
    release_frame FR ST3 (bv_unsigned sp).
    destruct (flag_keeps _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ CLc (bv_unsigned sp) G5 MU2 WM2 (incl_appl _ (incl_refl _)) ltac:(lia)) as [AG6 AGP6].
    apply evtF_done. subst POSTQ1 POSTQ0 POSTQ. cbv beta iota.
    split; [exact FP2|].
    lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 (if st =? 0 then -2 else st)%Z), mm, PB1, pk' end.
    split. { unfold hpost_regs. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity. }
    split; [congruence|]. split; [assumption|]. split; [exact ST3|].
    split.
    { eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AGb|]; intros a (K & _ & _); exact K|].
      eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG3|]; intros a (K & NH & _); split; [exact K| cbn [outside]; split; [exact NH| exact I]]|].
      eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG4|]; intros a (K & _ & NK); split; [| exact NK];
                               destruct K as [K|[K|[K|K]]]; [left; lia| right; left; exact K| right; right; left; apply in_frames_cons; exact K
                                                            | right; right; right; apply in_frame_sh_cons; exact K]|].
      eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG5|]; intros a (K & _); split; [exact K| exact I]|].
      eapply agrees_on_weaken; [exact AG6|]. intros a (K & _); exact K. }
    split; [exact G6|].
    assert (PBIN : forall a, in_block PB1 a -> in_block (CLc ++ PB1) a) by (intros a Ha; apply in_block_app; right; exact Ha).
    split. { intros Hne. eapply PCAPR_agree; [exact AGP6| exact PBIN|]. eapply PCAPR_agree; [exact AGP5| intros a Ha; exact Ha|].
             apply PC5. destruct Hst as [-> | [-> | ->]]; cbn [Z.eqb] in Hne; lia. }
    split. { intros He. eapply PCAPR_closable_agree; [exact AGP6| exact PBIN|]. eapply PCAPR_closable_agree; [exact AGP5| intros a Ha; exact Ha|].
             apply PCC5. destruct Hst as [-> | [-> | ->]]; cbn [Z.eqb] in He; lia. }
    split; [reflexivity|].
    split. { destruct Hst as [-> | [-> | ->]]; cbn [Z.eqb]; [left| right; left| right; right]; reflexivity. }
    split; [exact HH|]. split; [exact HP1| exact Hpk1].
  Qed.
  End Sz2.
  Theorem next_ex_proofA : ltac:(let t := eval cbv delta [next_ex_proofA__stmt] in next_ex_proofA__stmt in exact t).
  Proof using FENTER1 FRET GL OREAD. red. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CLc PB FB FL trC lo P HP PKT p fuel hc pkc. ltac2:(SecDiet.SzSec.closeP 'next_ex_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NextEx.
End CANSEC1.
End TwB.
