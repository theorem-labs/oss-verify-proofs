(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AMalloc_iface. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnKA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnEA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnE2A__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnIA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnEA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_ngnE2A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnIA__A3P.F_ngnLA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextD__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextD__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.
Ltac apA lem := eapply lem; try eassumption.
Ltac transport H m' AG tac :=
  lazymatch type of H with rw_cells ?sg _ ?A ?cs =>
    let X := fresh in
    assert (X : rw_cells sg m' A cs) by (eapply agrees_rw_cells; [exact AG | exact H | tac]);
    clear H; rename X into H end.
(* [comment removed for export] *)
Ltac exit_sides FIN :=
  lazymatch goal with
  | |- OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_finalC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => FIN
  | |- is_ng _ = true => reflexivity
  | |- cells_size _ = _ => reflexivity
  | |- length (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.str_bytes _) = _ => rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.str_bytes_length; reflexivity
  | |- In _ client_globals => unfold client_globals; repeat (first [left; reflexivity | right])
  | |- fmt_ok _ _ = true => reflexivity
  | |- (length _ <= _)%nat => cbn; lia
  | |- Forall2 _ _ _ => cbn [length firstn]; repeat (constructor; [reflexivity|]); constructor
  | |- _ => lia
  end.


Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NgnThm.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  Hypothesis PP : post_process_stmt.
  Hypothesis ADJ : adjust_snapshot_stmt.
  Hypothesis RBLK : read_block_stmt HO FO sites GIOA TP.
  Hypothesis ADDIF : add_interface_stmt HO FO sites GIOA TP.

  Definition pcap_ng_next_packet_proofA__stmt : Prop := pcap_ng_next_packet_stmt HO FO sites GIOA TP.
  Section Sz1.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CLc PB FB FL trC lo P HA DA p fuel hcs dc : ltac2:(SecDiet.SzSec.tyM 'pcap_ng_next_packet_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  #[using="fflagA GL GPL SNPRINTF PP ADJ RBLK ADDIF"] Lemma pcap_ng_next_packet_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'pcap_ng_next_packet_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros PRE UC TR NF PC NG S16 -> -> -> HH Hh HD Hd OHA ODA HDA HA8 DA8.
    destruct PRE as (G & ST & LO & BU & SPT & MI & TPE & ALN & RSTK & RIMG & RISH & RTLS).
    unfold PCAP_L2_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof atop_range as AR.
    destruct p as [self rfile bufsize bufalloc buffer bufdata swapped vmaj vmin snapshot linktype ltext prec brk errbuf header priv].
    destruct priv as [sf|sx ix]; [discriminate NG|]. clear NG.
    pose proof PC as (Af & HinF & (B & I & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    cbn [pc_rfile] in HinF.
    rewrite EPB in G, PC.
    change {| pc_self := self; pc_rfile := rfile; pc_bufsize := bufsize; pc_bufalloc := bufalloc; pc_buffer := buffer; pc_bufdata := bufdata; pc_swapped := swapped;
              pc_version_major := vmaj; pc_version_minor := vmin; pc_snapshot := snapshot; pc_linktype := linktype; pc_linktype_ext := ltext;
              pc_tstamp_precision := prec; pc_break_loop := brk; pc_errbuf := errbuf; pc_header := header; pc_priv := PrivNg sx ix |} with (A3P.F_ngnEA.TwB.pv self rfile bufsize swapped vmaj vmin snapshot linktype ltext prec brk header buffer bufalloc bufdata errbuf sx ix) in *.
    set (pvv := A3P.F_ngnEA.TwB.pv self rfile bufsize swapped vmaj vmin snapshot linktype ltext prec brk header buffer bufalloc bufdata errbuf sx ix) in *.
    assert (HinP : In (self, P, 680%Z) ((CLc ++ pcap_blocks pvv P B I) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinP) as ((PBAND & P3 & PTOP & P2) & P1 & PUNP & PRNG & PRSH & PAR).
    cbn [cb_addr cb_size fst snd] in *.
    band_ind PBAND bP.
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G) as ((_ & GOT & _ & _ & SHB & _) & _).
    (* [comment removed for export] *)
    pose proof (proj1 OHA) as HLOC. pose proof (proj1 ODA) as DLOC.
    assert (HLOC' : clocA FL (CLc ++ pcap_blocks pvv P B I) HA 24) by (eapply clocA_incl; [exact HLOC | apply incl_appl, incl_refl | apply incl_refl]).
    assert (DLOC' : clocA FL (CLc ++ pcap_blocks pvv P B I) DA 8) by (eapply clocA_incl; [exact DLOC | apply incl_appl, incl_refl | apply incl_refl]).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G HLOC') as HALO.
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G DLOC') as DALO.
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G HLOC (or_introl eq_refl : In (self, P, 680%Z) (pcap_blocks pvv P B I)) ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kHP & kHPr & kHP1 & kHP2).
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G DLOC (or_introl eq_refl : In (self, P, 680%Z) (pcap_blocks pvv P B I)) ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kDP & kDPr & kDP1 & kDP2).
    cbn [cb_addr cb_size fst snd] in kHP1, kHP2, kDP1, kDP2.
    assert (HAP : (HA + 24 <= P \/ P + 680 <= HA)%Z) by lia.
    assert (DAP : (DA + 8 <= P \/ P + 680 <= DA)%Z) by lia.
    unfold next_packet_op, np_entry, is_ng. subst pvv. cbn [pc_priv pk_next_ng PK A3P.F_ngnEA.TwB.pv].
    rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA.TwB.pcap_ng_next_packet_KF HO FO sites).
    (* [comment removed for export] *)
    pose proof CELLS as CJ. unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, A3P.F_ngnEA.TwB.pv in CJ.
    cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_ng pk_cleanup_ng PK] in CJ.
    clear CELLS PRIV BUF PFX IFS.
    hide HH. hide HD.
    rng_sp_window RSTK sp RSPW.
    pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG. carve_frame 240%nat ST.
    apply (rw_cells_split_CB asegs _ _ [] 240 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 24; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB _ ?t] =>
      lazymatch t with firstn _ _ => idtac | skipn _ _ => idtac end; let j := fresh "jk" in pose (j := t); change t with j in FR; clearbody j end.
    do 14 zstep.
    do 2 zstep.
    zstep. if_cases G1; zify_cond G1. { exfalso. rewrite ?unsigned_lit in G1 by lia. lia. }   (* [comment removed for export] *)
    zstep.
    assert (L7 : Z.land P 7 = 0%Z) by (rewrite land7_mod; Z.div_mod_to_equations; lia).
    zstep. rewrite L7.
    zstep. if_false.   (* [comment removed for export] *)
    do 3 zstep.
    zstep. ck0 PUNP; ck_go.
    zstep. ck0 PUNP; ck_go.
    do 2 zstep.
    do 41 zstep.
    replace (Z.land (P + 96) 7) with 0%Z in FR by (change 7%Z with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    replace (Z.land (P + 100) 7) with 4%Z in FR by (change 7%Z with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    replace (Z.land (P + 56) 7) with 0%Z in FR by (change 7%Z with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    replace (Z.land (P + 648) 7) with 0%Z in FR by (change 7%Z with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    replace (P + 648 <? 1)%Z with false in FR by (symmetry; apply Z.ltb_ge; lia).
    change (Z.lor (Z.b2z false) (Z.b2z (0 <? 0)))%Z with 0%Z in FR.
    change (0 + 3)%Z with 3%Z in FR. change (4 + 3)%Z with 7%Z in FR.
    unhide HH. unhide HD.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AGP : agrees_on (fun a => outside [(bv_unsigned sp + -240, bv_unsigned sp)]%Z a) m mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]) end.
    apply (agrees_rw_cells _ _ _ _ _ AGP) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside fst snd]; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGP) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside fst snd]; lia].
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (G0 : GIOA L RNG s (CLc ++ pcap_blocks (A3P.F_ngnEA.TwB.pv self rfile bufsize swapped vmaj vmin snapshot linktype ltext prec brk header buffer bufalloc bufdata errbuf sx ix) P B I) FB FL mm)
        by (eapply (gl_frame _ _ _ GL); [exact G | exact MU | exact WM | apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]]);
      assert (PC0 : PCAPR (hptr:=hptr) P (A3P.F_ngnEA.TwB.pv self rfile bufsize swapped vmaj vmin snapshot linktype ltext prec brk header buffer bufalloc bufdata errbuf sx ix)
                          (pcap_blocks (A3P.F_ngnEA.TwB.pv self rfile bufsize swapped vmaj vmin snapshot linktype ltext prec brk header buffer bufalloc bufdata errbuf sx ix) P B I) FB mm)
        by (eapply PCAPR_agree; [exact AGP | | exact PC]; intros a Ha;
            pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G ltac:(apply in_block_app; left; apply in_block_app; right; exact Ha)); cbn [outside fst snd]; lia);
      assert (AG0 : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m mm)
        by (eapply agrees_on_weaken; [| intros a [K _]; exact K];
            eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G | exact MU | exact WM | | lia];
            apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil])
    end.
    apply evtF_done.
    (* [comment removed for export] *)
    subst POSTQ.
    eapply (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnIA__A3P.F_ngnLA.TwB.ngn_loop HO FO sites GIOA TP fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CLc FB FL lo P HA DA Af m (ps_outfile s)
              self rfile bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HinF HLOC DLOC trC
              PP OHA ODA HDA HA8 DA8 ADJ ADDIF RBLK GPL TR NF fuel) with (ccs := [CB 24 jk13]) (hcs := hcs) (dw := dc);
      [ apply fp_le_refl | exact ST | exact FR | reflexivity | assumption | exact G0 | exact PC0 | exact AG0 | exact HH | exact Hh | exact HD | exact Hd | reflexivity
      | eapply A3P.F_ngnEA.TwB.ngn_ucx_entry; [exact LO | exact BU | exact SPT | exact HALO | exact DALO | exact UC | exact S16 | exact (proj1 TR) | exact AG0] ].
  Qed.
  End Sz1.
  #[using="fflagA GL GPL SNPRINTF PP ADJ RBLK ADDIF"] Theorem pcap_ng_next_packet_proofA : ltac:(let t := eval cbv delta [pcap_ng_next_packet_proofA__stmt] in pcap_ng_next_packet_proofA__stmt in exact t).
  Proof. red. unfold next_packet_op_stmt_for. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CLc PB FB FL trC lo P HA DA p fuel hcs dc. ltac2:(SecDiet.SzSec.closeP 'pcap_ng_next_packet_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgnThm.
End CANSEC1.
