(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnKA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA.
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
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.

Definition NGN_FMT_TOO_SHORT_A : Z := 0x22520.    (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac apA lem := eapply lem; try eassumption.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NgnCtx.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (L : alayout) (RNG : footprint) (CLc FB : list (@cblock hptr)) (FL : list fblock) (lo P HA DA Af : Z) (m : mem) (o : option hptr).
  Variables (self f : hptr) (bufsize : Z) (swapped : bool) (vmaj vmin snapshot linktype ltext prec brk : Z) (header : pkthdr).
  Hypothesis LO : (ATOP + 4096 <= lo)%Z.
  Hypothesis BU : (lo + 57344 <= bv_unsigned sp)%Z.
  Hypothesis SPT : (bv_unsigned sp + 16 < al_top L /\ al_top L <= 2^47)%Z.
  Hypothesis RSTK : rng RNG lo (al_top L - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.
  Hypothesis RTLS : rng_atls RNG.
  Hypothesis TPE : tp = Z_to_bv 64 ATP.
  Hypothesis ALN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis HALO : (0x603000 <= HA /\ HA + 24 <= ATOP)%Z.
  Hypothesis DALO : (0x603000 <= DA /\ DA + 8 <= ATOP)%Z.
  Hypothesis HAP : (HA + 24 <= P \/ P + 680 <= HA)%Z.
  Hypothesis DAP : (DA + 8 <= P \/ P + 680 <= DA)%Z.
  Hypothesis HinF : In (f, Af, FILE_BLOCK) FB.

  Let POSTQ := next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CLc FB lo P HA DA m o.

  (* [comment removed for export] *)
  #[local] Abbreviation ngn_frameA := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_frameA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA).
  #[local] Abbreviation ngn_final := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_final GIOA sp L RNG CLc FB FL P HA DA m o).
  #[local] Abbreviation ngn_finalC := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_finalC GIOA sp L RNG CLc FB FL P HA DA m o).

  #[local] Abbreviation pcapT := (pcap hptr hptr).
  #[local] Abbreviation MR := (M (PState H hptr) ((Z + ng_found) * pcap hptr hptr)).

  (* [comment removed for export] *)
  Definition pv (bq : hptr) (alloc : Z) (data eb : list Z) (s : pcap_ng_sf) (i : option hptr) : pcap hptr hptr :=
    mkPcap self f bufsize alloc bq data swapped vmaj vmin snapshot linktype ltext prec brk eb header (PrivNg s i).

  (* [comment removed for export] *)
  Definition ccells (Bq rem bt : Z) (cpad : list byte) : list cell :=
    [C8 (Z_to_bv 64 (Bq + 8)); C8 (Z_to_bv 64 rem); C4 (Z_to_bv 64 bt); CB 4 cpad].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition ngn_ucx (m5 : mem) (x0 : word) : Prop :=
    exists trX : list Z, traces_read_block TP L 0x8cc90 trX /\
      forall spw : word, bv_unsigned spw = (bv_unsigned sp + -224)%Z -> ucallerA depth_read_block L m5 spw x0 (Z_to_bv 64 0x8cc90) trX.

  Lemma ngn_ucx_m1 : traces_read_block TP L 0x8cc90 [] -> forall m5, ngn_ucx m5 (Z_to_bv 64 (-1)).
  Proof using LO BU SPT.
    clear GL SNPRINTF RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HinF POSTQ.
    intros T0 m5. exists []. split; [exact T0|]. intros spw Hsp. unfold ucallerA.
    pose proof atop_range as AR.
    assert (E1 : bv_unsigned (Z_to_bv 64 (-1)) = (2^64 - 1)%Z) by reflexivity.
    split. { intros PC k _ _. apply uc_stop. rewrite E1. lia. }
    split; [cbn [length]; unfold depth_read_block; lia|]. split; [rewrite E1, Hsp; lia|].
    split; [rewrite unsigned_lit by lia; unfold ACLIENT_LO, ACLIENT_HI; lia|]. right. rewrite E1, Hsp. lia.
  Qed.

  Lemma ngn_ucx_entry : forall (trC : list Z) (m5 : mem),
    ucallerA depth_pcap_ng_next_packet L m sp s0 ra trC -> (bv_unsigned sp + 16 <= bv_unsigned s0)%Z -> traces_read_block TP L 0x8cc90 trC ->
    agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
    ngn_ucx m5 s0.
  Proof using LO BU SPT HALO DALO.
    clear GL SNPRINTF RSTK RIMG RISH RTLS TPE ALN HAP DAP HinF POSTQ.
    intros trC m5 (UC & LEN & S8 & RA & HS0) S16 T AG. exists trC. split; [exact T|]. intros spw Hsp.
    pose proof atop_range as AR.
    pose proof (bv_unsigned_in_range 64 s0) as RS0. unfold bv_modulus in RS0.
    split.
    { intros PC k HPC HK. specialize (UC PC k HPC HK).
      assert (UC' : uchain m5 (al_top L) PC (bv_unsigned sp) (bv_unsigned s0) k trC).
      { eapply uchain_frame; [exact UC|]. intros a Ha. apply AG; [lia|]. split; [left; lia|]. lia. }
      rewrite Hsp. inversion UC'; subst.
      - apply uc_stop. lia.
      - eapply uc_lowpc; eauto; lia.
      - eapply uc_step; eauto; lia. }
    split; [unfold depth_read_block, depth_pcap_ng_next_packet in *; lia|]. split; [rewrite Hsp; lia|].
    split; [rewrite unsigned_lit by lia; unfold ACLIENT_LO, ACLIENT_HI; lia|]. right. rewrite Hsp. lia.
  Qed.

  Definition ngn_headA (Q : pcapT -> PState H hptr -> footprint -> machine_state -> Prop) : Prop :=
    forall (ra' t0' t1' t2' x0 a0' a1' a2' a3' a4' a5' a6' a7' x11 t3' t4' t5' t6' : word) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (hcs : list cell) (dw : cell) (ccs : list cell),
      fp_le RNG RNG5 ->
      stk asegs m5 lo (bv_unsigned sp + -224) ->
      rw_cells asegs m5 (bv_unsigned sp + -224) (ngn_frameA ccs) -> cells_size ccs = 24%nat -> mem_inv asegs m5 ->
      GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells asegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells asegs m5 DA [dw] -> csize dw = 8%nat -> ps_outfile ps = o ->
      ngn_ucx m5 x0 ->
      Q (pv bq alloc data eb sx ix) ps RNG5
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -224)) gp tp t0' t1' t2' x0 (Z_to_bv 64 2147450880) a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 2) (Z_to_bv 64 (P + 216)) (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) (Z_to_bv 64 (P + 660))
                 (Z_to_bv 64 1) (Z_to_bv 64 168627466) (Z_to_bv 64 P) (Z_to_bv 64 Af) x11
                 t3' t4' t5' t6') F (Z_to_bv 64 NGN_LOOP_A) fc None m5 (seg_rom asegs)).

  (* [comment removed for export] *)
  #[using="FO fflagA GL SNPRINTF LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP"] Lemma ngn_snp_b8 :
    forall (ra' t0' t1' t2' a0' a3' a4' a5' a6' a7' x1 x2 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (PB' : list (@cblock hptr)) (p' : pcapT) (h : pkthdr) (hcs' : list cell) (dw : cell) (ccs : list cell)
           (FMTA : Z) (fs : string) (args : list farg) (e : list Z),
      stk asegs m5 lo (bv_unsigned sp + -224) ->
      rw_cells asegs m5 (bv_unsigned sp + -224) (ngn_frameA ccs) -> cells_size ccs = 24%nat -> mem_inv asegs m5 ->
      ngn_finalC m5 RNG5 ps PB' p' hcs' dw -> is_ng p' = true ->
      fmt_at m5 FMTA fs -> fmt_ok fs args = true -> (length args <= 3)%nat ->
      Forall2 (farg_word true L RNG5 FL (CLc ++ PB') (bv_unsigned sp + -224) (P + 216) 256 m5) args (firstn (length args) [a3'; a4'; a5']) ->
      implMG RNG5 (mret ((-1)%Z, h, set_errbuf e p')) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -224)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) x1
                 a0' (Z_to_bv 64 256) (Z_to_bv 64 FMTA) a3' a4' a5' a6' a7'
                 x2 (Z_to_bv 64 (P + 216)) x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x8d0ec) fc None m5 (seg_rom asegs)).
  Proof.
    intros until e. intros ST5 FR5 Hccs MI5 FIN NG5 FMT5 FOK LA FW.
    pose proof FIN as (FP5 & G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF5).
    hide FR5. hide HH. hide HD.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    ienterG. zstep. zstep. unhide FR5. unhide HH. unhide HD.
    apply evtF_done. subst POSTQ0.
    apA (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_snp rc tlsI H hptr FO GIOA fflagA).
  Qed.
  (* [comment removed for export] *)
  Lemma PCAPR_bufdata : forall (Lx : alayout) (RNGx : footprint) (ps : PState H hptr) (bq : hptr) (Bq Ix alloc : Z) (data data' eb : list Z) (sx : pcap_ng_sf)
                               (ix : option hptr) (m5 m6 : mem) (Q : Z -> Prop) (BS : list byte),
    GIOA Lx RNGx ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m5 ->
    PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
    agrees_on Q m5 m6 -> (forall a, (0 <= a < 2^64)%Z -> ~ (Bq <= a < Bq + alloc)%Z -> Q a) ->
    rw_cells asegs m6 Bq [CB (Z.to_nat alloc) BS] -> firstn (length data') BS = map b8 data' -> length data' = length data ->
    PCAPR (hptr:=hptr) P (pv bq alloc data' eb sx ix) (pcap_blocks (pv bq alloc data' eb sx ix) P Bq Ix) FB m6.
  Proof using GL.
    clear SNPRINTF LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HinF POSTQ.
    intros Lx RNGx ps bq Bq Ix alloc data data' eb sx ix m5 m6 Q BS G PC AG HQ BUF6 PFX6 LEN.
    destruct PC as (Afx & Hin & (Bx & Ix' & jx & padx & bsx & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof G as Ge. rewrite EPB in Ge.
    pose proof (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ Ge eq_refl) as [APB API].
    assert (HinP : In (self, P, 680%Z) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bx Ix') ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ Ge HinP) as ((_ & _ & PTOP & _) & P1 & _).
    cbn [cb_addr cb_size fst snd] in PTOP, P1.
    pose proof atop_range as AR.
    unfold pv, pcap_blocks, psize, is_ng in EPB, APB, API. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, APB, API.
    assert (EBX : Bx = Bq) by congruence. subst Bx. unfold PCAP_NG_SF_TOTAL in APB, API.
    exists Afx. split; [exact Hin|]. exists Bq, Ix', jx, padx, BS.
    split; [exact EPB|].
    split. { eapply agrees_rw_cells; [exact AG | exact CELLS |]. intros a Ha. rewrite pcap_cells_gen_size in Ha by reflexivity. apply HQ; lia. }
    split. { eapply agrees_rw_cells; [exact AG | exact PRIV |]. intros a Ha. pose proof (priv_cells_psize _ _ _ _ _ PRIV) as PZ.
             unfold psize, is_ng, pv, PCAP_PRIV_OFF, priv_cells in PZ, Ha. cbn [pc_priv] in PZ, Ha. unfold PCAP_NG_SF_TOTAL in PZ. apply HQ; lia. }
    split; [exact BUF6|]. split; [exact PFX6|].
    split. { eapply ifaces_ok_agree; [exact AG | | exact IFS]. intros sg q Hq a Ha. unfold pv in Hq. cbn [pc_priv] in Hq. injection Hq as E1 E2. subst sg ix.
             destruct (API sx q eq_refl) as [X1 X2].
             assert (HinI : In (q, Ix', (40 * ng_ifaces_size sx)%Z) ((CLc ++ pcap_blocks (pv bq alloc data eb sx (Some q)) P Bq Ix') ++ FB))
               by (apply in_or_app; left; apply in_or_app; right; right; right; left; reflexivity).
             pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ Ge HinI) as ((_ & _ & ITOP & _) & I1 & _). cbn [cb_addr cb_size fst snd] in ITOP, I1.
             apply HQ; lia. }
    unfold pcap_wf in WF |- *. unfold pv in WF |- *. cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor pc_linktype pc_linktype_ext pc_header pc_priv] in WF |- *.
    rewrite LEN. exact WF.
  Qed.
  (* [comment removed for export] *)
  Lemma CLc_not_PB : forall (Lx : alayout) (RNGx : footprint) (ps : PState H hptr) (PB : list (@cblock hptr)) (mx : mem) (a : Z),
    GIOA Lx RNGx ps (CLc ++ PB) FB FL mx -> in_block CLc a -> ~ in_block PB a.
  Proof using GL.
    clear SNPRINTF LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HinF POSTQ.
    intros Lx RNGx ps PB mx a G Ha Hb.
    pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G) as BA. apply blocks_apart_app_inv in BA as (BA & _ & _).
    apply blocks_apart_app_inv in BA as (_ & _ & BX).
    apply in_block_In in Ha as (b & Hb1 & Hb2). apply in_block_In in Hb as (b' & Hb1' & Hb2').
    specialize (BX b b' Hb1 Hb1'). unfold apart in BX. lia.
  Qed.
End NgnCtx.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
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
(* [comment removed for export] *)
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.

Definition NGN_FMT_TOO_SHORT_A : Z := 0x22520.    (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac apA lem := eapply lem; try eassumption.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NgnCtx.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (L : alayout) (RNG : footprint) (CLc FB : list (@cblock hptr)) (FL : list fblock) (lo P HA DA Af : Z) (m : mem) (o : option hptr).
  Variables (self f : hptr) (bufsize : Z) (swapped : bool) (vmaj vmin snapshot linktype ltext prec brk : Z) (header : pkthdr).
  Hypothesis LO : (ATOP + 4096 <= lo)%Z.
  Hypothesis BU : (lo + 57344 <= bv_unsigned sp)%Z.
  Hypothesis SPT : (bv_unsigned sp + 16 < al_top L /\ al_top L <= 2^47)%Z.
  Hypothesis RSTK : rng RNG lo (al_top L - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.
  Hypothesis RTLS : rng_atls RNG.
  Hypothesis TPE : tp = Z_to_bv 64 ATP.
  Hypothesis ALN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis HALO : (0x604000 <= HA /\ HA + 24 <= ATOP)%Z.
  Hypothesis DALO : (0x604000 <= DA /\ DA + 8 <= ATOP)%Z.
  Hypothesis HAP : (HA + 24 <= P \/ P + 680 <= HA)%Z.
  Hypothesis DAP : (DA + 8 <= P \/ P + 680 <= DA)%Z.
  Hypothesis HinF : In (f, Af, FILE_BLOCK) FB.

  Let POSTQ := next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CLc FB lo P HA DA m o.

  (* [comment removed for export] *)
  #[local] Abbreviation ngn_frameA := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_frameA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA).
  #[local] Abbreviation ngn_final := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_final GIOA sp L RNG CLc FB FL P HA DA m o).
  #[local] Abbreviation ngn_finalC := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_finalC GIOA sp L RNG CLc FB FL P HA DA m o).

  #[local] Abbreviation pcapT := (pcap hptr hptr).
  #[local] Abbreviation MR := (M (PState H hptr) ((Z + ng_found) * pcap hptr hptr)).

  (* [comment removed for export] *)
  Definition pv (bq : hptr) (alloc : Z) (data eb : list Z) (s : pcap_ng_sf) (i : option hptr) : pcap hptr hptr :=
    mkPcap self f bufsize alloc bq data swapped vmaj vmin snapshot linktype ltext prec brk eb header (PrivNg s i).

  (* [comment removed for export] *)
  Definition ccells (Bq rem bt : Z) (cpad : list byte) : list cell :=
    [C8 (Z_to_bv 64 (Bq + 8)); C8 (Z_to_bv 64 rem); C4 (Z_to_bv 64 bt); CB 4 cpad].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition ngn_ucx (m5 : mem) (x0 : word) : Prop :=
    exists trX : list Z, traces_read_block TP L 0x8ce3c trX /\
      forall spw : word, bv_unsigned spw = (bv_unsigned sp + -240)%Z -> ucallerA depth_read_block L m5 spw x0 (Z_to_bv 64 0x8ce3c) trX.

  Lemma ngn_ucx_m1 : traces_read_block TP L 0x8ce3c [] -> forall m5, ngn_ucx m5 (Z_to_bv 64 (-1)).
  Proof using LO BU SPT.
    clear GL SNPRINTF RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HinF POSTQ.
    intros T0 m5. exists []. split; [exact T0|]. intros spw Hsp. unfold ucallerA.
    pose proof atop_range as AR.
    assert (E1 : bv_unsigned (Z_to_bv 64 (-1)) = (2^64 - 1)%Z) by reflexivity.
    split. { intros PC k _ _. apply uc_stop. rewrite E1. lia. }
    split; [cbn [length]; unfold depth_read_block; lia|]. split; [rewrite E1, Hsp; lia|].
    split; [rewrite unsigned_lit by lia; unfold ACLIENT_LO, ACLIENT_HI; lia|]. right. rewrite E1, Hsp. lia.
  Qed.

  Lemma ngn_ucx_entry : forall (trC : list Z) (m5 : mem),
    ucallerA depth_pcap_ng_next_packet L m sp s0 ra trC -> (bv_unsigned sp + 16 <= bv_unsigned s0)%Z -> traces_read_block TP L 0x8ce3c trC ->
    agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
    ngn_ucx m5 s0.
  Proof using LO BU SPT HALO DALO.
    clear GL SNPRINTF RSTK RIMG RISH RTLS TPE ALN HAP DAP HinF POSTQ.
    intros trC m5 (UC & LEN & S8 & RA & HS0) S16 T AG. exists trC. split; [exact T|]. intros spw Hsp.
    pose proof atop_range as AR.
    pose proof (bv_unsigned_in_range 64 s0) as RS0. unfold bv_modulus in RS0.
    split.
    { intros PC k HPC HK. specialize (UC PC k HPC HK).
      assert (UC' : uchain m5 (al_top L) PC (bv_unsigned sp) (bv_unsigned s0) k trC).
      { eapply uchain_frame; [exact UC|]. intros a Ha. apply AG; [lia|]. split; [left; lia|]. lia. }
      rewrite Hsp. inversion UC'; subst.
      - apply uc_stop. lia.
      - eapply uc_lowpc; eauto; lia.
      - eapply uc_step; eauto; lia. }
    split; [unfold depth_read_block, depth_pcap_ng_next_packet in *; lia|]. split; [rewrite Hsp; lia|].
    split; [rewrite unsigned_lit by lia; unfold ACLIENT_LO, ACLIENT_HI; lia|]. right. rewrite Hsp. lia.
  Qed.

  Definition ngn_headA (Q : pcapT -> PState H hptr -> footprint -> machine_state -> Prop) : Prop :=
    forall (ra' t0' t1' t2' x0 a0' a1' a2' a3' a4' a5' a6' a7' x11 t3' t4' t5' t6' : word) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (hcs : list cell) (dw : cell) (ccs : list cell),
      fp_le RNG RNG5 ->
      stk asegs m5 lo (bv_unsigned sp + -240) ->
      rw_cells asegs m5 (bv_unsigned sp + -240) (ngn_frameA ccs) -> cells_size ccs = 24%nat -> mem_inv asegs m5 ->
      GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells asegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells asegs m5 DA [dw] -> csize dw = 8%nat -> ps_outfile ps = o ->
      ngn_ucx m5 x0 ->
      Q (pv bq alloc data eb sx ix) ps RNG5
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0' t1' t2' x0 (Z_to_bv 64 (P + 216)) a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) (Z_to_bv 64 2) (Z_to_bv 64 2147450880) (Z_to_bv 64 (P + 660))
                 (Z_to_bv 64 1) (Z_to_bv 64 168627466) (Z_to_bv 64 P) (Z_to_bv 64 Af) x11
                 t3' t4' t5' t6') F (Z_to_bv 64 NGN_LOOP_A) fc None m5 (seg_rom asegs)).

  (* [comment removed for export] *)
  #[using="FO fflagA GL SNPRINTF LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP"] Lemma ngn_snp_b8 :
    forall (ra' t0' t1' t2' a0' a3' a4' a5' a6' a7' x1 x2 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (PB' : list (@cblock hptr)) (p' : pcapT) (h : pkthdr) (hcs' : list cell) (dw : cell) (ccs : list cell)
           (FMTA : Z) (fs : string) (args : list farg) (e : list Z),
      stk asegs m5 lo (bv_unsigned sp + -240) ->
      rw_cells asegs m5 (bv_unsigned sp + -240) (ngn_frameA ccs) -> cells_size ccs = 24%nat -> mem_inv asegs m5 ->
      ngn_finalC m5 RNG5 ps PB' p' hcs' dw -> is_ng p' = true ->
      fmt_at m5 FMTA fs -> fmt_ok fs args = true -> (length args <= 3)%nat ->
      Forall2 (farg_word true L RNG5 FL (CLc ++ PB') (bv_unsigned sp + -240) (P + 216) 256 m5) args (firstn (length args) [a3'; a4'; a5']) ->
      implMG RNG5 (mret ((-1)%Z, h, set_errbuf e p')) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 a0' (Z_to_bv 64 256) (Z_to_bv 64 FMTA) a3' a4' a5' a6' a7'
                 x4 x5 x2 x1 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x8d9ec) fc None m5 (seg_rom asegs)).
  Proof.
    intros until e. intros ST5 FR5 Hccs MI5 FIN NG5 FMT5 FOK LA FW.
    pose proof FIN as (FP5 & G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF5).
    hide FR5. hide HH. hide HD.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    ienterG. zstep. zstep. unhide FR5. unhide HH. unhide HD.
    apply evtF_done. subst POSTQ0.
    apA (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_snp rc tlsI H hptr FO GIOA fflagA).
  Qed.
  (* [comment removed for export] *)
  Lemma PCAPR_bufdata : forall (Lx : alayout) (RNGx : footprint) (ps : PState H hptr) (bq : hptr) (Bq Ix alloc : Z) (data data' eb : list Z) (sx : pcap_ng_sf)
                               (ix : option hptr) (m5 m6 : mem) (Q : Z -> Prop) (BS : list byte),
    GIOA Lx RNGx ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m5 ->
    PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
    agrees_on Q m5 m6 -> (forall a, (0 <= a < 2^64)%Z -> ~ (Bq <= a < Bq + alloc)%Z -> Q a) ->
    rw_cells asegs m6 Bq [CB (Z.to_nat alloc) BS] -> firstn (length data') BS = map b8 data' -> length data' = length data ->
    PCAPR (hptr:=hptr) P (pv bq alloc data' eb sx ix) (pcap_blocks (pv bq alloc data' eb sx ix) P Bq Ix) FB m6.
  Proof using GL.
    clear SNPRINTF LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HinF POSTQ.
    intros Lx RNGx ps bq Bq Ix alloc data data' eb sx ix m5 m6 Q BS G PC AG HQ BUF6 PFX6 LEN.
    destruct PC as (Afx & Hin & (Bx & Ix' & jx & padx & bsx & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof G as Ge. rewrite EPB in Ge.
    pose proof (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ Ge eq_refl) as [APB API].
    assert (HinP : In (self, P, 680%Z) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bx Ix') ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ Ge HinP) as ((_ & _ & PTOP & _) & P1 & _).
    cbn [cb_addr cb_size fst snd] in PTOP, P1.
    pose proof atop_range as AR.
    unfold pv, pcap_blocks, psize, is_ng in EPB, APB, API. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, APB, API.
    assert (EBX : Bx = Bq) by congruence. subst Bx. unfold PCAP_NG_SF_TOTAL in APB, API.
    exists Afx. split; [exact Hin|]. exists Bq, Ix', jx, padx, BS.
    split; [exact EPB|].
    split. { eapply agrees_rw_cells; [exact AG | exact CELLS |]. intros a Ha. rewrite pcap_cells_gen_size in Ha by reflexivity. apply HQ; lia. }
    split. { eapply agrees_rw_cells; [exact AG | exact PRIV |]. intros a Ha. pose proof (priv_cells_psize _ _ _ _ _ PRIV) as PZ.
             unfold psize, is_ng, pv, PCAP_PRIV_OFF, priv_cells in PZ, Ha. cbn [pc_priv] in PZ, Ha. unfold PCAP_NG_SF_TOTAL in PZ. apply HQ; lia. }
    split; [exact BUF6|]. split; [exact PFX6|].
    split. { eapply ifaces_ok_agree; [exact AG | | exact IFS]. intros sg q Hq a Ha. unfold pv in Hq. cbn [pc_priv] in Hq. injection Hq as E1 E2. subst sg ix.
             destruct (API sx q eq_refl) as [X1 X2].
             assert (HinI : In (q, Ix', (40 * ng_ifaces_size sx)%Z) ((CLc ++ pcap_blocks (pv bq alloc data eb sx (Some q)) P Bq Ix') ++ FB))
               by (apply in_or_app; left; apply in_or_app; right; right; right; left; reflexivity).
             pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ Ge HinI) as ((_ & _ & ITOP & _) & I1 & _). cbn [cb_addr cb_size fst snd] in ITOP, I1.
             apply HQ; lia. }
    unfold pcap_wf in WF |- *. unfold pv in WF |- *. cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor pc_linktype pc_linktype_ext pc_header pc_priv] in WF |- *.
    rewrite LEN. exact WF.
  Qed.
  (* [comment removed for export] *)
  Lemma CLc_not_PB : forall (Lx : alayout) (RNGx : footprint) (ps : PState H hptr) (PB : list (@cblock hptr)) (mx : mem) (a : Z),
    GIOA Lx RNGx ps (CLc ++ PB) FB FL mx -> in_block CLc a -> ~ in_block PB a.
  Proof using GL.
    clear SNPRINTF LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HinF POSTQ.
    intros Lx RNGx ps PB mx a G Ha Hb.
    pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G) as BA. apply blocks_apart_app_inv in BA as (BA & _ & _).
    apply blocks_apart_app_inv in BA as (_ & _ & BX).
    apply in_block_In in Ha as (b & Hb1 & Hb2). apply in_block_In in Hb as (b' & Hb1' & Hb2').
    specialize (BX b b' Hb1 Hb1'). unfold apart in BX. lia.
  Qed.
End NgnCtx.
End CANSEC1.
End TwB.
