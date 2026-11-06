(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnKA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnEA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextD__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_hlenA__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require AiAuxB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_ngnE2A.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnKA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnEA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnEA.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextD__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NgnObj.
  Context {H hptr : Type} (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.

  (* [comment removed for export] *)
  #[using="rc tlsI FO fflagA GL"] Lemma clocA_not_PB : forall (L : alayout) (RNG : footprint) (ps : PState H hptr) (CLc PB FB : list (@cblock hptr)) (FL : list fblock) (mx : mem) (A n a : Z),
    GIOA L RNG ps (CLc ++ PB) FB FL mx -> clocA FL CLc A n -> A <= a < A + n -> ~ in_block PB a.
  Proof.
    intros L RNG ps CLc PB FB FL mx A n a G [(b & Hb & H1 & H2)|(fr & Hf & H1 & H2)] Ha Hin.
    - pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G) as BA. apply blocks_apart_app_inv in BA as (BA & _ & _).
      apply blocks_apart_app_inv in BA as (_ & _ & BX).
      apply in_block_In in Hin as (b' & Hb1' & Hb2'). specialize (BX b b' Hb Hb1'). unfold apart in BX. lia.
    - apply (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G).
      + apply in_frames_In. exists fr. split; [exact Hf| lia].
      + apply in_block_app. left. apply in_block_app. right. exact Hin.
  Qed.

  (* [comment removed for export] *)
  #[using="tlsI FO fflagA GL"] Lemma ksh_of_ag : forall (L : alayout) (RNG : footprint) (ps : PState H hptr) (CLx CLc FB : list (@cblock hptr)) (FL : list fblock) (m0 m mx : mem) (SP HA DA : Z),
    GIOA L RNG ps CLx FB FL m0 -> ablk HA (HA + 24) -> ablk DA (DA + 8) ->
    agrees_on (fun a => client_keeps FL CLc SP a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m mx ->
    agrees_on (in_frame_sh FL) m mx.
  Proof.
    intros L RNG ps CLx CLc FB FL m0 m mx SP HA DA G BH BD AG.
    eapply (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ [(HA, HA + 24); (DA, DA + 8)]%Z _ _ _ G (incl_refl _)).
    - eapply agrees_on_weaken; [exact AG|]. intros a [K O]. cbn [outside fst snd] in O. split; [exact K| tauto].
    - apply Forall_cons; [exact BH|]. apply Forall_cons; [exact BD| apply Forall_nil].
  Qed.

  (* [comment removed for export] *)
  #[using="tlsI FO fflagA GL"] Lemma cobj_now : forall (L : alayout) (RNG RNGx : footprint) (ps : PState H hptr) (CLc PB FB : list (@cblock hptr)) (FL : list fblock) (m mx : mem) (SP HA DA A n : Z),
    GIOA L RNGx ps (CLc ++ PB) FB FL mx -> clocA FL CLc HA 24 -> clocA FL CLc DA 8 ->
    agrees_on (fun a => client_keeps FL CLc SP a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m mx ->
    cobjA RNG m FL CLc A n -> 0 < n -> cobjA RNGx mx FL CLc A n.
  Proof.
    intros L RNG RNGx ps CLc PB FB FL m mx SP HA DA A n G HL DL AG O Hn.
    assert (HL' : clocA FL (CLc ++ PB) HA 24) by (eapply clocA_incl; [exact HL | apply incl_appl, incl_refl | apply incl_refl]).
    assert (DL' : clocA FL (CLc ++ PB) DA 8) by (eapply clocA_incl; [exact DL | apply incl_appl, incl_refl | apply incl_refl]).
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G HL' ltac:(lia)) as BH.
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G DL' ltac:(lia)) as BD.
    eapply (cobjA_keep _ _ _ GL); [exact O | exact G | apply incl_appl, incl_refl | apply incl_refl | | exact Hn].
    eapply ksh_of_ag; [exact G | exact BH | exact BD | exact AG].
  Qed.
  #[using="Type"] Lemma clocA_sub : forall (FL : list fblock) (CL : list (@cblock hptr)) A n A' n', clocA FL CL A n -> A <= A' -> A' + n' <= A + n -> clocA FL CL A' n'.
  Proof.
    intros FL CL A n A' n' [(b & Hb & H1 & H2)|(fr & Hf & H1 & H2)] HA HB; [left; exists b | right; exists fr]; (split; [assumption| lia]).
  Qed.

  (* [comment removed for export] *)
  #[using="tlsI FO fflagA GL"] Lemma keeps_facts : forall (L : alayout) (RNG : footprint) (ps : PState H hptr) (CLc PB FB : list (@cblock hptr)) (FL : list fblock) (mx : mem) (SP a : Z),
    GIOA L RNG ps (CLc ++ PB) FB FL mx -> client_keeps FL CLc SP a -> SP <= a \/ (0 < a < ATOP /\ ~ in_block PB a).
  Proof.
    intros L RNG ps CLc PB FB FL mx SP a G [Ha|[Ha|[Ha|Ha]]]; [left; exact Ha | right | right | right].
    - split; [exact (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G ltac:(apply in_block_app; left; apply in_block_app; left; exact Ha))|].
      intros Hin. pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G) as BA. apply blocks_apart_app_inv in BA as (BA & _ & _).
      apply blocks_apart_app_inv in BA as (_ & _ & BX).
      apply in_block_In in Ha as (b & Hb1 & Hb2). apply in_block_In in Hin as (b' & Hb1' & Hb2'). specialize (BX b b' Hb1 Hb1'). unfold apart in BX. lia.
    - split; [exact (gia_in_frames_below _ _ _ GL _ _ _ _ _ _ _ a G Ha)|].
      intros Hin. apply (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G Ha). apply in_block_app. left. apply in_block_app. right. exact Hin.
    - pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G Ha) as SB. pose proof atop_range as AR.
      split; [lia|]. intros Hin. apply in_block_In in Hin as (b & Hb1 & Hb2).
      destruct (gl_block _ _ _ GL _ _ _ _ _ _ _ b G ltac:(apply in_or_app; left; apply in_or_app; right; exact Hb1)) as ((BAND & _) & _).
      unfold ablk, AIMG_HI, KLS in BAND. lia.
  Qed.
End NgnObj.

Section NgnBuf.
  Context {H hptr : Type} (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Variables (CLc FB : list (@cblock hptr)) (FL : list fblock) (P : Z).
  Variables (self f : hptr) (bufsize : Z) (swapped : bool) (vmaj vmin snapshot linktype ltext prec brk : Z) (header : pkthdr).
  #[local] Abbreviation pv := (F_ngnEA.pv self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).

  (* [comment removed for export] *)
  #[using="rc tlsI FO fflagA GL"] Lemma PCAPR_bufdata2 : forall (Lx : alayout) (RNGx : footprint) (ps : PState H hptr) (bq : hptr) (Bq Ix alloc : Z) (data data' eb : list Z) (sx : pcap_ng_sf)
                                (ix : option hptr) (m5 m6 : mem) (Q : Z -> Prop) (BS : list byte),
    GIOA Lx RNGx ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m5 ->
    PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
    agrees_on Q m5 m6 -> (forall a, in_block (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) a -> ~ (Bq <= a < Bq + alloc)%Z -> Q a) ->
    rw_cells asegs m6 Bq [CB (Z.to_nat alloc) BS] -> firstn (length data') BS = map b8 data' -> length data' = length data ->
    PCAPR (hptr:=hptr) P (pv bq alloc data' eb sx ix) (pcap_blocks (pv bq alloc data' eb sx ix) P Bq Ix) FB m6.
  Proof.
    intros Lx RNGx ps bq Bq Ix alloc data data' eb sx ix m5 m6 Q BS G PC AG HQ BUF6 PFX6 LEN.
    destruct PC as (Afx & Hin & (Bx & Ix' & jx & padx & bsx & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof G as Ge. rewrite EPB in Ge. rewrite EPB in HQ.
    pose proof (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ Ge eq_refl) as [APB API].
    assert (HinP : In (self, P, 680%Z) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bx Ix') ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ Ge HinP) as ((_ & _ & PTOP & _) & P1 & _).
    cbn [cb_addr cb_size fst snd] in PTOP, P1.
    pose proof atop_range as AR.
    assert (INP : forall a, (P <= a < P + 680)%Z -> in_block (pcap_blocks (pv bq alloc data eb sx ix) P Bx Ix') a).
    { intros a Ha. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold psize, is_ng, F_ngnEA.pv. cbn [pc_priv]. unfold PCAP_NG_SF_TOTAL. lia. }
    unfold F_ngnEA.pv, pcap_blocks, psize, is_ng in EPB, APB, API. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, APB, API.
    assert (EBX : Bx = Bq) by congruence. subst Bx. unfold PCAP_NG_SF_TOTAL in APB, API.
    exists Afx. split; [exact Hin|]. exists Bq, Ix', jx, padx, BS.
    split; [exact EPB|].
    split. { eapply agrees_rw_cells; [exact AG | exact CELLS |]. intros a Ha. rewrite pcap_cells_gen_size in Ha by reflexivity. apply HQ; [apply INP; lia| lia]. }
    split. { eapply agrees_rw_cells; [exact AG | exact PRIV |]. intros a Ha. pose proof (priv_cells_psize _ _ _ _ _ PRIV) as PZ.
             unfold psize, is_ng, F_ngnEA.pv, PCAP_PRIV_OFF, priv_cells in PZ, Ha. cbn [pc_priv] in PZ, Ha. unfold PCAP_NG_SF_TOTAL in PZ. apply HQ; [apply INP; lia| lia]. }
    split; [exact BUF6|]. split; [exact PFX6|].
    split. { eapply ifaces_ok_agree; [exact AG | | exact IFS]. intros sg q Hq a Ha. unfold F_ngnEA.pv in Hq. cbn [pc_priv] in Hq. injection Hq as E1 E2. subst sg ix.
             destruct (API sx q eq_refl) as [X1 X2].
             assert (HinI : In (q, Ix', (40 * ng_ifaces_size sx)%Z) ((CLc ++ pcap_blocks (pv bq alloc data eb sx (Some q)) P Bq Ix') ++ FB))
               by (apply in_or_app; left; apply in_or_app; right; right; right; left; reflexivity).
             pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ Ge HinI) as ((_ & _ & ITOP & _) & I1 & _). cbn [cb_addr cb_size fst snd] in ITOP, I1.
             apply HQ; [| lia]. unfold pcap_blocks, in_block. apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd pc_priv F_ngnEA.pv]. lia. }
    unfold pcap_wf in WF |- *. unfold F_ngnEA.pv in WF |- *. cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor pc_linktype pc_linktype_ext pc_header pc_priv] in WF |- *.
    rewrite LEN. exact WF.
  Qed.
End NgnBuf.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnEA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NgnObj.
  Context {H hptr : Type} (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.

  (* [comment removed for export] *)
  #[using="rc tlsI FO fflagA GL"] Lemma clocA_not_PB : forall (L : alayout) (RNG : footprint) (ps : PState H hptr) (CLc PB FB : list (@cblock hptr)) (FL : list fblock) (mx : mem) (A n a : Z),
    GIOA L RNG ps (CLc ++ PB) FB FL mx -> clocA FL CLc A n -> A <= a < A + n -> ~ in_block PB a.
  Proof.
    intros L RNG ps CLc PB FB FL mx A n a G [(b & Hb & H1 & H2)|(fr & Hf & H1 & H2)] Ha Hin.
    - pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G) as BA. apply blocks_apart_app_inv in BA as (BA & _ & _).
      apply blocks_apart_app_inv in BA as (_ & _ & BX).
      apply in_block_In in Hin as (b' & Hb1' & Hb2'). specialize (BX b b' Hb Hb1'). unfold apart in BX. lia.
    - apply (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G).
      + apply in_frames_In. exists fr. split; [exact Hf| lia].
      + apply in_block_app. left. apply in_block_app. right. exact Hin.
  Qed.

  (* [comment removed for export] *)
  #[using="tlsI FO fflagA GL"] Lemma ksh_of_ag : forall (L : alayout) (RNG : footprint) (ps : PState H hptr) (CLx CLc FB : list (@cblock hptr)) (FL : list fblock) (m0 m mx : mem) (SP HA DA : Z),
    GIOA L RNG ps CLx FB FL m0 -> ablk HA (HA + 24) -> ablk DA (DA + 8) ->
    agrees_on (fun a => client_keeps FL CLc SP a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m mx ->
    agrees_on (in_frame_sh FL) m mx.
  Proof.
    intros L RNG ps CLx CLc FB FL m0 m mx SP HA DA G BH BD AG.
    eapply (keepsx_frame_sh _ _ _ GL _ _ _ _ _ _ _ _ _ [(HA, HA + 24); (DA, DA + 8)]%Z _ _ _ G (incl_refl _)).
    - eapply agrees_on_weaken; [exact AG|]. intros a [K O]. cbn [outside fst snd] in O. split; [exact K| tauto].
    - apply Forall_cons; [exact BH|]. apply Forall_cons; [exact BD| apply Forall_nil].
  Qed.

  (* [comment removed for export] *)
  #[using="tlsI FO fflagA GL"] Lemma cobj_now : forall (L : alayout) (RNG RNGx : footprint) (ps : PState H hptr) (CLc PB FB : list (@cblock hptr)) (FL : list fblock) (m mx : mem) (SP HA DA A n : Z),
    GIOA L RNGx ps (CLc ++ PB) FB FL mx -> clocA FL CLc HA 24 -> clocA FL CLc DA 8 ->
    agrees_on (fun a => client_keeps FL CLc SP a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m mx ->
    cobjA RNG m FL CLc A n -> 0 < n -> cobjA RNGx mx FL CLc A n.
  Proof.
    intros L RNG RNGx ps CLc PB FB FL m mx SP HA DA A n G HL DL AG O Hn.
    assert (HL' : clocA FL (CLc ++ PB) HA 24) by (eapply clocA_incl; [exact HL | apply incl_appl, incl_refl | apply incl_refl]).
    assert (DL' : clocA FL (CLc ++ PB) DA 8) by (eapply clocA_incl; [exact DL | apply incl_appl, incl_refl | apply incl_refl]).
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G HL' ltac:(lia)) as BH.
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G DL' ltac:(lia)) as BD.
    eapply (cobjA_keep _ _ _ GL); [exact O | exact G | apply incl_appl, incl_refl | apply incl_refl | | exact Hn].
    eapply ksh_of_ag; [exact G | exact BH | exact BD | exact AG].
  Qed.
  #[using="Type"] Lemma clocA_sub : forall (FL : list fblock) (CL : list (@cblock hptr)) A n A' n', clocA FL CL A n -> A <= A' -> A' + n' <= A + n -> clocA FL CL A' n'.
  Proof.
    intros FL CL A n A' n' [(b & Hb & H1 & H2)|(fr & Hf & H1 & H2)] HA HB; [left; exists b | right; exists fr]; (split; [assumption| lia]).
  Qed.

  (* [comment removed for export] *)
  #[using="tlsI FO fflagA GL"] Lemma keeps_facts : forall (L : alayout) (RNG : footprint) (ps : PState H hptr) (CLc PB FB : list (@cblock hptr)) (FL : list fblock) (mx : mem) (SP a : Z),
    GIOA L RNG ps (CLc ++ PB) FB FL mx -> client_keeps FL CLc SP a -> SP <= a \/ (0 < a < ATOP /\ ~ in_block PB a).
  Proof.
    intros L RNG ps CLc PB FB FL mx SP a G [Ha|[Ha|[Ha|Ha]]]; [left; exact Ha | right | right | right].
    - split; [exact (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G ltac:(apply in_block_app; left; apply in_block_app; left; exact Ha))|].
      intros Hin. pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G) as BA. apply blocks_apart_app_inv in BA as (BA & _ & _).
      apply blocks_apart_app_inv in BA as (_ & _ & BX).
      apply in_block_In in Ha as (b & Hb1 & Hb2). apply in_block_In in Hin as (b' & Hb1' & Hb2'). specialize (BX b b' Hb1 Hb1'). unfold apart in BX. lia.
    - split; [exact (gia_in_frames_below _ _ _ GL _ _ _ _ _ _ _ a G Ha)|].
      intros Hin. apply (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G Ha). apply in_block_app. left. apply in_block_app. right. exact Hin.
    - pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G Ha) as SB. pose proof atop_range as AR.
      split; [lia|]. intros Hin. apply in_block_In in Hin as (b & Hb1 & Hb2).
      destruct (gl_block _ _ _ GL _ _ _ _ _ _ _ b G ltac:(apply in_or_app; left; apply in_or_app; right; exact Hb1)) as ((BAND & _) & _).
      unfold ablk, AIMG_HI, KLS in BAND. lia.
  Qed.
End NgnObj.

Section NgnBuf.
  Context {H hptr : Type} (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Variables (CLc FB : list (@cblock hptr)) (FL : list fblock) (P : Z).
  Variables (self f : hptr) (bufsize : Z) (swapped : bool) (vmaj vmin snapshot linktype ltext prec brk : Z) (header : pkthdr).
  #[local] Abbreviation pv := (A3P.F_ngnEA.TwB.pv self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).

  (* [comment removed for export] *)
  #[using="rc tlsI FO fflagA GL"] Lemma PCAPR_bufdata2 : forall (Lx : alayout) (RNGx : footprint) (ps : PState H hptr) (bq : hptr) (Bq Ix alloc : Z) (data data' eb : list Z) (sx : pcap_ng_sf)
                                (ix : option hptr) (m5 m6 : mem) (Q : Z -> Prop) (BS : list byte),
    GIOA Lx RNGx ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m5 ->
    PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
    agrees_on Q m5 m6 -> (forall a, in_block (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) a -> ~ (Bq <= a < Bq + alloc)%Z -> Q a) ->
    rw_cells asegs m6 Bq [CB (Z.to_nat alloc) BS] -> firstn (length data') BS = map b8 data' -> length data' = length data ->
    PCAPR (hptr:=hptr) P (pv bq alloc data' eb sx ix) (pcap_blocks (pv bq alloc data' eb sx ix) P Bq Ix) FB m6.
  Proof.
    intros Lx RNGx ps bq Bq Ix alloc data data' eb sx ix m5 m6 Q BS G PC AG HQ BUF6 PFX6 LEN.
    destruct PC as (Afx & Hin & (Bx & Ix' & jx & padx & bsx & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof G as Ge. rewrite EPB in Ge. rewrite EPB in HQ.
    pose proof (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ Ge eq_refl) as [APB API].
    assert (HinP : In (self, P, 680%Z) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bx Ix') ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ Ge HinP) as ((_ & _ & PTOP & _) & P1 & _).
    cbn [cb_addr cb_size fst snd] in PTOP, P1.
    pose proof atop_range as AR.
    assert (INP : forall a, (P <= a < P + 680)%Z -> in_block (pcap_blocks (pv bq alloc data eb sx ix) P Bx Ix') a).
    { intros a Ha. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold psize, is_ng, A3P.F_ngnEA.TwB.pv. cbn [pc_priv]. unfold PCAP_NG_SF_TOTAL. lia. }
    unfold A3P.F_ngnEA.TwB.pv, pcap_blocks, psize, is_ng in EPB, APB, API. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, APB, API.
    assert (EBX : Bx = Bq) by congruence. subst Bx. unfold PCAP_NG_SF_TOTAL in APB, API.
    exists Afx. split; [exact Hin|]. exists Bq, Ix', jx, padx, BS.
    split; [exact EPB|].
    split. { eapply agrees_rw_cells; [exact AG | exact CELLS |]. intros a Ha. rewrite pcap_cells_gen_size in Ha by reflexivity. apply HQ; [apply INP; lia| lia]. }
    split. { eapply agrees_rw_cells; [exact AG | exact PRIV |]. intros a Ha. pose proof (priv_cells_psize _ _ _ _ _ PRIV) as PZ.
             unfold psize, is_ng, A3P.F_ngnEA.TwB.pv, PCAP_PRIV_OFF, priv_cells in PZ, Ha. cbn [pc_priv] in PZ, Ha. unfold PCAP_NG_SF_TOTAL in PZ. apply HQ; [apply INP; lia| lia]. }
    split; [exact BUF6|]. split; [exact PFX6|].
    split. { eapply ifaces_ok_agree; [exact AG | | exact IFS]. intros sg q Hq a Ha. unfold A3P.F_ngnEA.TwB.pv in Hq. cbn [pc_priv] in Hq. injection Hq as E1 E2. subst sg ix.
             destruct (API sx q eq_refl) as [X1 X2].
             assert (HinI : In (q, Ix', (40 * ng_ifaces_size sx)%Z) ((CLc ++ pcap_blocks (pv bq alloc data eb sx (Some q)) P Bq Ix') ++ FB))
               by (apply in_or_app; left; apply in_or_app; right; right; right; left; reflexivity).
             pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ Ge HinI) as ((_ & _ & ITOP & _) & I1 & _). cbn [cb_addr cb_size fst snd] in ITOP, I1.
             apply HQ; [| lia]. unfold pcap_blocks, in_block. apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd pc_priv A3P.F_ngnEA.TwB.pv]. lia. }
    unfold pcap_wf in WF |- *. unfold A3P.F_ngnEA.TwB.pv in WF |- *. cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor pc_linktype pc_linktype_ext pc_header pc_priv] in WF |- *.
    rewrite LEN. exact WF.
  Qed.
End NgnBuf.
End CANSEC1.
End TwB.
End F_ngnE2A.

(* [comment removed for export] *)
Module F_ngnBA.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnKA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnEA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnEA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_ngnE2A.
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
  | |- OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_finalC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => FIN
  | |- is_ng _ = true => reflexivity
  | |- cells_size _ = _ => reflexivity
  | |- length (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.str_bytes _) = _ => rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.str_bytes_length; reflexivity
  | |- In _ client_globals => unfold client_globals; repeat (first [left; reflexivity | right])
  | |- fmt_ok _ _ = true => reflexivity
  | |- (length _ <= _)%nat => cbn; lia
  | |- Forall2 _ _ _ => cbn [length firstn]; repeat (constructor; [reflexivity|]); constructor
  | |- _ => lia
  end.
Ltac name_field data off a b c d DRNG :=
  set (a := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 0%Z) in *; set (b := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 1%Z) in *; set (c := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 2%Z) in *; set (d := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 3%Z) in *;
  let Ra := fresh "R" a in let Rb := fresh "R" b in let Rc := fresh "R" c in let Rd := fresh "R" d in
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data off 0%Z DRNG ltac:(lia)) as Ra; pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data off 1%Z DRNG ltac:(lia)) as Rb;
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data off 2%Z DRNG ltac:(lia)) as Rc; pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data off 3%Z DRNG ltac:(lia)) as Rd;
  fold a in Ra; fold b in Rb; fold c in Rc; fold d in Rd.

(* [comment removed for export] *)
Definition firstn2_q8__stmt : Prop := forall data (bs : list byte) (k : nat) off,
  firstn (length data) bs = map b8 data -> Z.of_nat k = off -> (off + 2 <= Z.of_nat (length data))%Z ->
  firstn 2 (skipn k bs) = [b8 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 0); b8 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 1)].
Section Sz1.
Variables data bs k off : ltac2:(SecDiet.SzSec.tyM 'firstn2_q8__stmt "vvvv" @data).
#[using="Type"] Lemma firstn2_q8__body : ltac2:(SecDiet.SzSec.bodyP 'firstn2_q8__stmt "vvvv").
Proof.
  intros PFX Hk H1.
 subst off.
  destruct (zslice_2 (Z.of_nat k) data ltac:(lia) H1) as (x0 & x1 & E).
  destruct (get_u8_of_slice2 (Z.of_nat k) data x0 x1 ltac:(lia) H1 E) as [E0 E1].
  transitivity (map b8 (zslice (Z.of_nat k) 2 data)).
  - unfold zslice, zfirstn, zskipn. rewrite <- firstn_map, <- skipn_map, <- PFX. rewrite skipn_firstn_comm, firstn_firstn, Nat2Z.id. f_equal. lia.
  - rewrite E. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8. rewrite Z.add_0_r, E0, E1. reflexivity.
Qed.
End Sz1.
Lemma firstn2_q8 : ltac:(let t := eval cbv delta [firstn2_q8__stmt] in firstn2_q8__stmt in exact t).
Proof. intros data bs k off. ltac2:(SecDiet.SzSec.closeP 'firstn2_q8__body "vvvv"). Qed.

Lemma get_le16_q8' : forall data off, (0 <= off)%Z -> (off + 2 <= Z.of_nat (length data))%Z ->
  get_le16 data off = (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 0 + 256 * OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 1)%Z.
Proof.
  intros data off H0 H1. destruct (zslice_2 off data H0 H1) as (x0 & x1 & E).
  destruct (get_u8_of_slice2 off data x0 x1 H0 H1 E) as [E0 E1].
  rewrite (get_le16_of_slice off data x0 x1 E). unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8. rewrite Z.add_0_r, E0, E1. reflexivity.
Qed.

Ltac merge_all H :=
  lazymatch type of H with
  | rw_cells ?s ?m ?A ?cs =>
      change cs with ([] ++ cs ++ []) in H; apply (rw_cells_merge s m A [] cs []) in H;
      cbn [cells_size csize cells_bytes cbytes Nat.add app] in H
  end.
Lemma bytes_wr_rw_cellsA : forall {rc : runConstT} mx A l, bytes_at asegs mx A l -> wr_at asegs mx A (Z.of_nat (length l)) -> rw_cells asegs mx A [CB (length l) l].
Proof. intros rc mx A l HB HW. split; [split; [cbn; split; [reflexivity| exact Logic.I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact HB] | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r; exact HW]. Qed.

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
  Hypothesis HLOC : clocA FL CLc HA 24.
  Hypothesis DLOC : clocA FL CLc DA 8.

  Let POSTQ := next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CLc FB lo P HA DA m o.

  (* [comment removed for export] *)
  #[local] Abbreviation ngn_frameA := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_frameA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA).
  #[local] Abbreviation ngn_final := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_final GIOA sp L RNG CLc FB FL P HA DA m o).
  #[local] Abbreviation ngn_finalC := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_finalC GIOA sp L RNG CLc FB FL P HA DA m o).

  Hypothesis PP : post_process_stmt.
  Hypothesis OHA : cobjA RNG m FL CLc HA 24.
  Hypothesis ODA : cobjA RNG m FL CLc DA 8.
  Hypothesis HDA : (HA + 24 <= DA \/ DA + 8 <= HA)%Z.
  Hypothesis HA8 : (HA mod 8 = 0)%Z.
  Hypothesis DA8 : (DA mod 8 = 0)%Z.

  #[local] Abbreviation pcapT := (pcap hptr hptr).
  #[local] Abbreviation pv := (F_ngnEA.pv self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).

  (* [comment removed for export] *)
  Definition ngn_pp__stmt : Prop := forall (ra' t0' t1' t2' x0 a0' a1' a2' a3' a4' a5' a6' a7' x2 x3 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' ws wu : word) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc doff : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (sec usec cap len : Z) (dw : cell) (ccs' : list cell),
      fp_le RNG RNG5 ->
      stk asegs m5 lo (bv_unsigned sp + -224) ->
      rw_cells asegs m5 (bv_unsigned sp + -224) (ngn_frameA (C8 (Z_to_bv 64 (Bq + doff)) :: ccs')) -> cells_size ccs' = 16%nat -> mem_inv asegs m5 ->
      GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells asegs m5 HA [C8 ws; C8 wu; C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs m5 DA [dw] -> csize dw = 8%nat ->
      ws = Z_to_bv 64 sec -> wu = Z_to_bv 64 usec -> Forall (fun x => 0 <= x < 256)%Z data ->
      (0 <= doff <= Z.of_nat (length data))%Z -> (doff mod 4 = 0)%Z ->
      (0 <= cap <= Z.of_nat (length data) - doff)%Z -> (Z.of_nat (length data) < 2^31)%Z -> (0 <= len < 2^32)%Z -> ps_outfile ps = o -> (0 < alloc)%Z ->
      implMG RNG5 (let '(hdr, d) := pcapint_post_process linktype swapped (mkHdr sec usec cap len) (zskipn doff data) in
                   mret (1%Z, hdr, set_bufdata (zfirstn doff data ++ d) (pv bq alloc data eb sx ix))) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -224)) gp tp t0' t1' t2' x0 (Z_to_bv 64 2147450880) a0' a1' a2' a3' a4' a5' a6' a7'
                 x2 x3 (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) x6 x7 x8 x9 x10 x11
                 t3' t4' t5' t6') F (Z_to_bv 64 0x8d888) fc None m5 (seg_rom asegs)).
  Section Sz4.
  Variables ra' t0' t1' t2' x0 a0' a1' a2' a3' a4' a5' a6' a7' x2 x3 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' ws wu m5 RNG5 ps bq Bq Ix alloc doff data eb sx ix sec usec cap len dw ccs' : ltac2:(SecDiet.SzSec.tyM 'ngn_pp__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  #[using="rc tlsI FO fflagA GL LO BU SPT RSTK RIMG RISH HALO DALO HAP DAP HLOC DLOC PP OHA ODA HDA HA8 DA8"] Lemma ngn_pp__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_pp__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros FP5 ST5 FR5 Hccs MI5 G5 PC5 AG5 HH HD Hd -> -> DRNG Hdoff Hd4 Hcap Hl31 Hlen OF5 ALLOC0.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (rng_fp_le _ _ _ _ FP5 RSTK) as RSTK5. pose proof (rng_fp_le _ _ _ _ FP5 RIMG) as RIMG5. pose proof (rng_fp_le _ _ _ _ FP5 RISH) as RISH5.
    assert (RSPW : rng RNG5 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK5| lia]).
    pose proof atop_range as AR.
    (* [comment removed for export] *)
    pose proof (cobj_now FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G5 HLOC DLOC AG5 ODA ltac:(lia)) as (_ & (DA0 & DA47 & DUNP & DRNGf & DRSH & DAR & DBLK)).
    replace (DA - DA mod 8)%Z with DA in DRSH by lia. replace (8 + DA mod 8)%Z with 8%Z in DRSH by lia.
    band_ind DBLK bD.
    pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    assert (HinP : In (self, P, 680%Z) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    assert (HinB : In (bq, Bq, alloc) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; right; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinP) as ((PBAND & P3 & PTOP & P2) & P1 & PUNP & PRNG & PRSH & PAR).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinB) as ((BBAND & B3 & BTOP & B2) & B1 & BUNP & BRNG & BRSH & BAR).
    cbn [cb_addr cb_size fst snd] in *.
    pose proof (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ G5 eq_refl) as [APB API].
    pose proof WF as (W1' & W2' & W3 & W4 & _ & _ & _ & _ & W9' & _).
    unfold F_ngnEA.pv, pcap_blocks, psize, is_ng in EPB, APB. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, APB. unfold PCAP_NG_SF_TOTAL in APB.
    unfold F_ngnEA.pv in W3, W4, W9'. cbn [pc_bufalloc pc_bufdata pc_linktype] in W3, W4, W9'.
    assert (EBX : Bx' = Bq) by congruence. subst Bx'.
    band_ind PBAND bP. band_ind BBAND bB.
    (* [comment removed for export] *)
    assert (HinP2 : In (self, P, 680%Z) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) by (left; reflexivity).
    assert (HinB2 : In (bq, Bq, alloc) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) by (right; left; reflexivity).
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G5 DLOC HinP2 ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kDP & kDPr & kDP1 & kDP2).
    cbn [cb_addr cb_size fst snd] in kDP1, kDP2.
    assert (KHD : exists k, (0 <= k <= 1 /\ HA + 24 <= DA + k * 18446744073709551616 /\ DA + 8 <= HA + (1 - k) * 18446744073709551616)%Z)
      by (destruct HDA; [exists 0%Z | exists 1%Z]; lia).
    destruct KHD as (kHD & kHDr & kHD1 & kHD2).
    unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, F_ngnEA.pv in CELLS.
    cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_ng pk_cleanup_ng PK] in CELLS.
    unfold F_ngnEA.pv in BUF. cbn [pc_bufalloc] in BUF. cbn [pc_bufdata] in PFX.
    destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
    pose proof FR5 as FRJ. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_frameA in FRJ. cbn [app] in FRJ.
    hide BUF. hide PRIV. hide HH. hide FR5.
    pose proof (munch_refl [(DA, DA + 8)]%Z m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    ienterG.
    zstep. ck0 DUNP; ck_go.
    do 2 zstep.
    zstep. if_cases BRZ; zify_cond BRZ. { exfalso. rewrite ?unsigned_lit in BRZ by lia. lia. }
    ck0_at PUNP (P + 100)%Z; ck_go.
    ck0_at PUNP (P + 56)%Z; ck_go.
    rewrite (sx32_small linktype) by lia.
    zstep. rewrite (sx32_small (Z.b2z swapped)) by (destruct swapped; cbn; lia).
    zstep.
    unhide BUF. unhide PRIV. unhide HH. unhide FR5. clear FRJ.
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G5 DLOC HinB2 ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kDB & kDBr & kDB1 & kDB2).
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G5 HLOC HinB2 ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kHB & kHBr & kHB1 & kHB2).
    cbn [cb_addr cb_size fst snd] in kDB1, kDB2, kHB1, kHB2.
    assert (AGD : agrees_on (fun a => outside [(DA, DA + 8)]%Z a) m5 m0) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
    assert (T0 : forall A cs, rw_cells asegs m5 A cs -> (A + Z.of_nat (cells_size cs) <= DA \/ DA + 8 <= A)%Z -> rw_cells asegs m0 A cs).
    { intros A cs HC HA'. eapply agrees_rw_cells; [exact AGD | exact HC | intros a Ha; cbn [outside fst snd]; lia]. }
    (* [comment removed for export] *)
    apply (rw_cells_split_CB asegs m5 _ [] (Z.to_nat alloc) _ [] [Z.to_nat doff; length data - Z.to_nat doff; Z.to_nat alloc - length data]%nat) in BUF; [| cbn; lia].
    cbn [mk_CB_cells app] in BUF.
    destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.pfx_split data bsx' (Z.to_nat doff) PFX ltac:(lia)) as [E0 E1]. rewrite E0, E1 in BUF.
    destruct (rw_cells_cut _ _ _ 1 BUF) as [BD0 BUF']. cbn [firstn skipn cells_size csize Nat.add] in BD0, BUF'.
    destruct (rw_cells_cut _ _ _ 1 BUF') as [BD BT]. clear BUF BUF'. cbn [firstn skipn cells_size csize Nat.add] in BD, BT.
    replace (Bq + Z.of_nat (Z.to_nat doff + 0))%Z with (Bq + doff)%Z in BD, BT by lia.
    replace (Bq + doff + Z.of_nat (length data - Z.to_nat doff + 0))%Z with (Bq + Z.of_nat (length data))%Z in BT by lia.
    apply T0 in BD0; [| cbn [cells_size csize Nat.add]; lia].
    apply T0 in BD; [| cbn [cells_size csize Nat.add]; lia].
    apply T0 in BT; [| cbn [cells_size csize Nat.add]; lia].
    apply T0 in HH; [| cbn [cells_size csize Nat.add]; lia].
    apply T0 in FR5; [| unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_frameA; rewrite !cells_size_app; cbn [cells_size csize Nat.add]; rewrite Hccs; lia].
    clear T0.
    assert (DL' : clocA FL (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) DA 8) by (eapply clocA_incl; [exact DLOC | apply incl_appl, incl_refl | apply incl_refl]).
    assert (G5' : GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m0).
    { eapply (gl_client_frame _ _ _ GL); [exact G5 | exact MU | exact WM |]. apply Forall_cons; [exact (clocA_iv _ _ _ _ DL')| apply Forall_nil]. }
    assert (PC5' : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m0).
    { eapply PCAPR_agree; [exact AGD | | exact PC5]. intros a Ha. cbn [outside fst snd]. split; [| exact Logic.I]. intros Hr.
      exact (clocA_not_PB FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ a G5 DLOC Hr Ha). }
    assert (AG5' : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m0).
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGD|]. intros a [_ [_ Hn]]; cbn [outside fst snd]; lia. }
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G5') as (RT5 & _).
    pose proof (cobj_now FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G5' HLOC DLOC AG5' OHA ltac:(lia)) as (_ & OHA5).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5' HinB) as BBLK.
    clear MU WM AGD G5 AG5 PC5.
    assert (ZA : zarr m0 (Bq + doff) (zskipn doff data)).
    { unfold zskipn. split; [| split; [| apply Forall_range_skipn; exact DRNG]].
      - pose proof (rw_cells_bytes_at _ _ _ _ BD) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X. exact X.
      - eapply rw_cells_wr_at; [exact BD|]. cbn [cells_size csize Nat.add]. rewrite length_skipn. lia. }
    change (rw_cells asegs m0 HA (pkthdr_cells (Z_to_bv 64 sec) (Z_to_bv 64 usec) (mkHdr sec usec cap len))) in HH.
    assert (LD : Z.of_nat (length (zskipn doff data)) = (Z.of_nat (length data) - doff)%Z) by (unfold zskipn; rewrite length_skipn; lia).
    name_sp sp (-224)%Z.
    eapply evtF_cut.
    { eapply PP with (lo := lo) (HA := HA) (DA := (Bq + doff)%Z) (hdr := mkHdr sec usec cap len) (d := zskipn doff data) (linktype := linktype) (swapped := swapped)
                     (ws := Z_to_bv 64 sec) (wu := Z_to_bv 64 usec);
        [ rewrite Hsp; assumption | unfold PP_FRAME; rewrite Hsp; lia | exact LO | exact HH | exact ZA | assumption | exact RT5
        | reflexivity | reflexivity | reflexivity | reflexivity
        | lia | cbn [h_caplen]; lia | lia | cbn [h_len]; lia
        | exact OHA5
        | eapply blockA_aobj; [exact BBLK | cbn [cb_addr cb_size fst snd]; lia | cbn [cb_addr cb_size fst snd]; lia | lia]
        | lia | lia | lia | exact HA8 | clear - B2 Hd4; Z.div_mod_to_equations; lia
        | eapply rng_sub'; [exact RSTK5| rewrite Hsp; lia] | exact RIMG5 | exact RISH5 ]. }
    cbv beta. intros ms' PO. unfold post_process_post in PO. destruct_exs PO. destruct PO as (-> & MU6 & WM6 & MI6 & ST6 & HH6 & ZA6).
    rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 579792)) with (Z_to_bv 64 579792) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    cbn [h_caplen] in MU6. unfold PP_FRAME in MU6.
    lazymatch type of MU6 with munch _ _ ?mb => rename mb into m6 end.
    set (hdr' := fst (pcapint_post_process linktype swapped (mkHdr sec usec cap len) (zskipn doff data))) in *.
    set (d' := snd (pcapint_post_process linktype swapped (mkHdr sec usec cap len) (zskipn doff data))) in *.
    pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts.pp_length linktype swapped (mkHdr sec usec cap len) (zskipn doff data)) as LEN'. fold d' in LEN'.
    pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts.pp_sec linktype swapped (mkHdr sec usec cap len) (zskipn doff data)) as [SEC' USEC']. fold hdr' in SEC', USEC'. cbn [h_sec h_usec] in SEC', USEC'.
    pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts.pp_range linktype swapped (mkHdr sec usec cap len) (zskipn doff data) ltac:(cbn [h_caplen]; lia) ltac:(cbn [h_len]; lia) ltac:(lia)) as [RC' RL']. fold hdr' in RC', RL'.
    assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -224 - 48, bv_unsigned sp + -224); (HA + 20, HA + 24); (Bq + doff, Bq + doff + cap)]%Z a) m0 m6)
      by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
    apply (agrees_rw_cells _ _ _ _ _ AGS) in FR5; [| intros a Ha; unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_frameA in Ha; rewrite !cells_size_app in Ha; cbn [outside fst snd cells_size csize Nat.add] in *; rewrite Hccs in Ha; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in HD'; [| intros a Ha; cbn [outside fst snd cells_size csize Nat.add] in *; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in BT; [| intros a Ha; cbn [outside fst snd cells_size csize Nat.add] in *; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in BD0; [| intros a Ha; cbn [outside fst snd cells_size csize Nat.add] in *; lia].
    (* [comment removed for export] *)
    destruct ZA6 as (ZB & ZW & ZR).
    pose proof (bytes_wr_rw_cellsA _ _ _ ZB ltac:(rewrite zbytes_length; exact ZW)) as BD6. rewrite zbytes_length in BD6.
    pose proof (rw_cells_uncut _ _ _ _ _ BD6 BT ltac:(cbn [cells_size csize Nat.add]; rewrite LEN'; unfold zskipn; rewrite length_skipn; lia)) as BDT. cbn [app] in BDT.
    pose proof (rw_cells_uncut _ _ _ _ _ BD0 BDT ltac:(cbn [cells_size csize Nat.add]; lia)) as BUF6. cbn [app] in BUF6.
    merge_all BUF6.
    replace (Z.to_nat doff + (length d' + (Z.to_nat alloc - length data + 0)))%nat with (Z.to_nat alloc) in BUF6 by (rewrite LEN'; unfold zskipn; rewrite length_skipn; lia).
    rewrite app_nil_r in BUF6.
    rewrite (surjective_pairing (pcapint_post_process linktype swapped _ _)). fold hdr' d'.
    change (set_bufdata (zfirstn doff data ++ d') (pv bq alloc data eb sx ix)) with (pv bq alloc (zfirstn doff data ++ d') eb sx ix).
    assert (HL' : clocA FL (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) (HA + 20) 4).
    { eapply clocA_sub; [eapply clocA_incl; [exact HLOC | apply incl_appl, incl_refl | apply incl_refl] | lia | lia]. }
    pose proof (clocA_iv _ _ _ _ HL') as HIV. replace (HA + 20 + 4)%Z with (HA + 24)%Z in HIV by lia.
    assert (G6 : GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m6).
    { eapply (gl_client_frame _ _ _ GL); [exact G5' | exact MU6 | exact WM6 |].
      apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [exact HIV|]. apply Forall_cons; [| apply Forall_nil].
      right; left. unfold iv_in_block. apply Exists_exists. exists (bq, Bq, alloc). split; [apply in_or_app; right; exact HinB2| cbn [cb_addr cb_size fst snd]; lia]. }
    assert (LENX : length (zfirstn doff data ++ d') = length data).
    { unfold zfirstn. rewrite length_app, length_firstn, LEN'. unfold zskipn. rewrite length_skipn. lia. }
    assert (PFX6 : firstn (length (zfirstn doff data ++ d')) (map PcapRep.b8 (firstn (Z.to_nat doff) data) ++ zbytes d' ++ firstn (Z.to_nat alloc - length data) (skipn (length data - Z.to_nat doff) (skipn (Z.to_nat doff) bsx')))
                   = map b8 (zfirstn doff data ++ d')).
    { unfold zfirstn. rewrite length_app, length_firstn, map_app.
      replace (Nat.min (Z.to_nat doff) (length data) + length d')%nat with (length (map PcapRep.b8 (firstn (Z.to_nat doff) data) ++ zbytes d')) by (rewrite length_app, length_map, length_firstn, zbytes_length; lia).
      rewrite app_assoc, firstn_app, firstn_all, Nat.sub_diag. cbn [firstn]. rewrite app_nil_r. reflexivity. }
    assert (PC6 : PCAPR (hptr:=hptr) P (pv bq alloc (zfirstn doff data ++ d') eb sx ix) (pcap_blocks (pv bq alloc (zfirstn doff data ++ d') eb sx ix) P Bq Ix) FB m6).
    { eapply (@PCAPR_bufdata2 rc tlsI H hptr FO GIOA fflagA GL) with (m5 := m0) (data := data)
               (Q := fun a => outside [(bv_unsigned sp + -224 - 48, bv_unsigned sp + -224); (HA + 20, HA + 24); (Bq + doff, Bq + doff + cap)]%Z a);
        [exact G5' | exact PC5' | exact AGS | | exact BUF6 | exact PFX6 | exact LENX].
      intros a Hina Hnb. cbn [outside fst snd].
      pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G5' ltac:(apply in_block_app; left; apply in_block_app; right; exact Hina)) as AB.
      split; [lia|]. split; [| split; [lia| exact Logic.I]].
      intros Hr. exact (clocA_not_PB FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ a G5' HLOC ltac:(lia) Hina). }
    assert (AG6 : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
    { eapply agrees_on_trans; [exact AG5'|]. eapply agrees_on_weaken; [exact AGS|]. intros a [K [Hn1 Hn2]]. cbn [outside fst snd].
      destruct (keeps_facts FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ a G5' K) as [Ks|[Kb Kn]].
      - split; [lia|]. split; [lia|]. split; [lia| exact Logic.I].
      - split; [lia|]. split; [lia|]. split; [| exact Logic.I]. intros Hr. apply Kn.
        unfold pcap_blocks, in_block. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd pc_buffer pc_bufalloc F_ngnEA.pv]. lia. }
    apply evtF_done.
    eapply (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_ret_1 rc H hptr GIOA) with (PB' := pcap_blocks (pv bq alloc (zfirstn doff data ++ d') eb sx ix) P Bq Ix) (ccs := C8 (Z_to_bv 64 (Bq + doff)) :: ccs');
      try eassumption; [cbn [cells_size csize]; rewrite Hccs; reflexivity | ].
    split; [exact FP5|]. split; [exact G6|]. split; [exact PC6|]. split; [exact AG6|].
    split. { unfold hdr_cells. rewrite SEC', USEC'. exact HH6. }
    split; [reflexivity|]. split; [exact HD'|]. split; [reflexivity| exact OF5].
  Qed.
  End Sz4.
  #[using="rc tlsI FO fflagA GL LO BU SPT RSTK RIMG RISH HALO DALO HAP DAP HLOC DLOC PP OHA ODA HDA HA8 DA8"] Lemma ngn_pp : ltac:(let t := eval cbv delta [ngn_pp__stmt] in ngn_pp__stmt in exact t).
  Proof. intros ra' t0' t1' t2' x0 a0' a1' a2' a3' a4' a5' a6' a7' x2 x3 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' ws wu m5 RNG5 ps bq Bq Ix alloc doff data eb sx ix sec usec cap len dw ccs'. ltac2:(SecDiet.SzSec.closeP 'ngn_pp__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgnCtx.
End CANSEC1.
End F_ngnBA.

(* [comment removed for export] *)
Module F_ngnICA.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnKA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnEA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnEA.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextD__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3.
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
  | |- OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_finalC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => FIN
  | |- is_ng _ = true => reflexivity
  | |- cells_size _ = _ => reflexivity
  | |- length (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.str_bytes _) = _ => rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.str_bytes_length; reflexivity
  | |- In _ client_globals => unfold client_globals; repeat (first [left; reflexivity | right])
  | |- fmt_ok _ _ = true => reflexivity
  | |- (length _ <= _)%nat => cbn; lia
  | |- Forall2 _ _ _ => cbn [length firstn]; repeat (constructor; [reflexivity|]); constructor
  | |- _ => lia
  end.
Ltac name_field data off a b c d DRNG :=
  set (a := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 0%Z) in *; set (b := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 1%Z) in *; set (c := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 2%Z) in *; set (d := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 3%Z) in *;
  let Ra := fresh "R" a in let Rb := fresh "R" b in let Rc := fresh "R" c in let Rd := fresh "R" d in
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data off 0%Z DRNG ltac:(lia)) as Ra; pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data off 1%Z DRNG ltac:(lia)) as Rb;
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data off 2%Z DRNG ltac:(lia)) as Rc; pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data off 3%Z DRNG ltac:(lia)) as Rd;
  fold a in Ra; fold b in Rb; fold c in Rc; fold d in Rd.

(* [comment removed for export] *)
Lemma firstn2_q8 : forall data (bs : list byte) (k : nat) off,
  firstn (length data) bs = map b8 data -> Z.of_nat k = off -> (off + 2 <= Z.of_nat (length data))%Z ->
  firstn 2 (skipn k bs) = [b8 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 0); b8 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 1)].
Proof.
  intros data bs k off PFX Hk H1. subst off.
  destruct (zslice_2 (Z.of_nat k) data ltac:(lia) H1) as (x0 & x1 & E).
  destruct (get_u8_of_slice2 (Z.of_nat k) data x0 x1 ltac:(lia) H1 E) as [E0 E1].
  transitivity (map b8 (zslice (Z.of_nat k) 2 data)).
  - unfold zslice, zfirstn, zskipn. rewrite <- firstn_map, <- skipn_map, <- PFX. rewrite skipn_firstn_comm, firstn_firstn, Nat2Z.id. f_equal. lia.
  - rewrite E. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8. rewrite Z.add_0_r, E0, E1. reflexivity.
Qed.

Lemma get_le16_q8' : forall data off, (0 <= off)%Z -> (off + 2 <= Z.of_nat (length data))%Z ->
  get_le16 data off = (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 0 + 256 * OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 1)%Z.
Proof.
  intros data off H0 H1. destruct (zslice_2 off data H0 H1) as (x0 & x1 & E).
  destruct (get_u8_of_slice2 off data x0 x1 H0 H1 E) as [E0 E1].
  rewrite (get_le16_of_slice off data x0 x1 E). unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8. rewrite Z.add_0_r, E0, E1. reflexivity.
Qed.

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
  Hypothesis HLOC : clocA FL CLc HA 24.
  Hypothesis DLOC : clocA FL CLc DA 8.

  Let POSTQ := next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CLc FB lo P HA DA m o.

  (* [comment removed for export] *)
  #[local] Abbreviation ngn_frameA := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_frameA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA).
  #[local] Abbreviation ngn_final := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_final GIOA sp L RNG CLc FB FL P HA DA m o).
  #[local] Abbreviation ngn_finalC := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_finalC GIOA sp L RNG CLc FB FL P HA DA m o).

  Variable trC : list Z.
  Hypothesis ADDIF : add_interface_stmt HO FO sites GIOA TP.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis TR : traces_pcap_ng_next_packet TP L (bv_unsigned ra) trC.

  #[local] Abbreviation pcapT := (pcap hptr hptr).
  #[local] Abbreviation MR := (M (PState H hptr) ((Z + ng_found) * pcap hptr hptr)).
  #[local] Abbreviation pv := (F_ngnEA.pv self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).
  #[local] Abbreviation ngn_KF := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF H hptr).
  #[local] Abbreviation ngn_headA := (F_ngnEA.ngn_headA GIOA TP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CLc FB FL lo P HA DA Af m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).

  #[using="Type"] Lemma implMG_retb_l : forall {St A B} RNGx (a : A) (k : A -> Monad.M St B) s Q ms, implMG RNGx (k a) s Q ms -> implMG RNGx (mbind (mret a) k) s Q ms.
  Proof. intros St A B RNGx a k s Q ms HH. exact HH. Qed.

  (* [comment removed for export] *)
  #[using="rc tlsI fflagA GL LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HLOC DLOC trC ADDIF GPL TR"] Lemma ngn_idb_call : forall (LOOP : pcapT -> MR),
    ngn_headA (fun p' ps' RNG' ms' => implMG RNG' (mbind (LOOP p') ngn_KF) ps' POSTQ ms') ->
    forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x18 x19 x21 t3' t4' t5' t6' : word) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (bt : Z) (hcs : list cell) (dw : cell) (cpad : list byte),
      fp_le RNG RNG5 ->
      stk asegs m5 lo (bv_unsigned sp + -224) ->
      rw_cells asegs m5 (bv_unsigned sp + -224) (ngn_frameA [C8 (Z_to_bv 64 (Bq + 16)); C8 (Z_to_bv 64 (rem - 8)); C4 (Z_to_bv 64 bt); CB 4 cpad]) -> mem_inv asegs m5 ->
      GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells asegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells asegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (8 <= rem)%Z ->
      (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implMG RNG5 (mbind (mbind (add_interface MOps (prims HO FO sites) (pv bq alloc data eb sx ix) 8 (mkCursor 16 (rem - 8) bt))
                          (fun r => let '(ok, c, p, msg) := r in if ok then LOOP p else mret (inl (-1)%Z, set_errbuf msg p))) ngn_KF) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -224)) gp tp t0' t1' t2' (Z_to_bv 64 (P + 216)) (Z_to_bv 64 2147450880) a0' a1' a2' a3' a4' a5' a6' a7'
                 x18 x19 (Z_to_bv 64 (P + 56)) x21 (Z_to_bv 64 (P + 660))
                 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) (Z_to_bv 64 168627466) (Z_to_bv 64 P) (Z_to_bv 64 Af) (Z_to_bv 64 (Bq + 8))
                 t3' t4' t5' t6') F (Z_to_bv 64 0x8cea0) fc None m5 (seg_rom asegs)).
  Proof.
    intros LOOP HLOOP. intros until cpad. intros FP5 ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (rng_fp_le _ _ _ _ FP5 RSTK) as RSTK5.
    assert (RSPW : rng RNG5 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK5| lia]).
    pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof G5 as G5e. rewrite EPB in G5e.
    assert (HinP : In (self, P, 680%Z) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    assert (HinB : In (bq, Bq, alloc) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; right; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinP) as ((PBAND & P3 & PTOP & P2) & P1 & PUNP & PRNG & PRSH & PAR).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinB) as ((BBAND & B3 & BTOP & B2) & B1 & BUNP & BRNG & BRSH & BAR).
    cbn [cb_addr cb_size fst snd] in *.
    pose proof (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ G5 eq_refl) as [APB API].
    pose proof WF as (W1' & W2' & W3 & W4 & W5' & W6' & W7' & W8' & W9' & W10' & W11 & W12 & W13 & W14).
    unfold F_ngnEA.pv, pcap_blocks, psize, is_ng in EPB, APB. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, APB. unfold PCAP_NG_SF_TOTAL in APB.
    unfold F_ngnEA.pv in W3, W4, W13. cbn [pc_bufalloc pc_bufdata pc_priv] in W3, W4, W13.
    assert (EBX : Bx' = Bq) by congruence. subst Bx'.
    unfold F_ngnEA.pv in Hin. cbn [pc_rfile] in Hin.
    unfold F_ngnEA.pv in BUF. cbn [pc_bufalloc] in BUF. cbn [pc_bufdata] in PFX.
    pose proof PRIV as NG5. unfold priv_cells, F_ngnEA.pv, PCAP_PRIV_OFF in NG5. cbn [pc_priv] in NG5.
    (* [comment removed for export] *)
    apply pcap_cells_split4 in CELLS as (PRE & CE & HDR & OPS); [|reflexivity].
    apply (rw_cells_split_CB asegs m5 _ [] 304 _ [] [256; 48]%nat) in CE; [|reflexivity]. cbn [mk_CB_cells app] in CE.
    destruct (rw_cells_cut _ _ _ 1 CE) as [CE1 CE2]. clear CE. cbn [firstn skipn cells_size csize Nat.add] in CE1, CE2.
    replace (P + 216 + Z.of_nat 256)%Z with (P + 472)%Z in CE2 by lia.
    unfold pc_pre in PRE. destruct (rw_cells_cut _ _ _ 7 PRE) as [PRE0 PRE7]. destruct (rw_cells_cut _ _ _ 2 PRE7) as [P48 PRE9]. clear PRE PRE7.
    cbn [firstn skipn cells_size csize Nat.add app] in PRE0, P48, PRE9.
    replace (P + Z.of_nat 48)%Z with (P + 48)%Z in P48 by lia. replace (P + Z.of_nat 48 + Z.of_nat 12)%Z with (P + 60)%Z in PRE9 by lia.
    (* [comment removed for export] *)
    pose proof FR5 as FRJ. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_frameA in FRJ. cbn [app] in FRJ.
    destruct (rw_cells_cut _ _ _ 12 FRJ) as [F0 F4]. destruct (rw_cells_cut _ _ _ 4 F4) as [FCUR FS]. clear FRJ F4.
    cbn [firstn skipn cells_size csize Nat.add app] in F0, FCUR, FS.
    replace (bv_unsigned sp + -224 + Z.of_nat 96)%Z with (bv_unsigned sp + -128)%Z in FCUR by lia.
    replace (bv_unsigned sp + -224 + Z.of_nat 96 + Z.of_nat 24)%Z with (bv_unsigned sp + -104)%Z in FS by lia.
    hide F0. hide FCUR. hide FS. hide PRE0. hide P48. hide PRE9. hide CE1. hide CE2. hide HDR. hide OPS. hide NG5. hide BUF. hide HH. hide HD. hide FR5. hide PRIV. hide IFS.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    ienterG. do 5 zstep. zstep. clear MU WM.
    unhide F0. unhide FCUR. unhide FS. unhide PRE0. unhide P48. unhide PRE9. unhide CE1. unhide CE2. unhide HDR. unhide OPS. unhide NG5. unhide BUF. unhide HH. unhide HD. unhide FR5. unhide PRIV. unhide IFS.
  pose proof (rng_fp_le _ _ _ _ FP5 RIMG) as RIMG5. pose proof (rng_fp_le _ _ _ _ FP5 RISH) as RISH5. pose proof (rng_fp_le _ _ _ _ FP5 RTLS) as RTLS5.
  apply evtF_done. apply implMG_bind_assoc. name_sp sp (-224)%Z. eapply implMG_bind.
  { eapply ADDIF with (L := L) (st := ps) (C1 := CLc ++ [(self, P, PCAP_NG_SF_TOTAL); (bq, Bq, alloc)]) (C2 := []) (FB := FB) (FL := FL) (trC := []) (P := P) (B := Bq) (I := Ix')
                      (CUR := (bv_unsigned sp + -128)%Z) (EB := (P + 216)%Z) (lo := lo) (idb_off := 8%Z) (p := pv bq alloc data eb sx ix) (s := sx) (i := ix)
                      (c := mkCursor 16 (rem - 8) bt) (bs := bsx') (ej := firstn 256 (pj_g jx')) (pad := padx) (cpad := cpad).
    - split; [rewrite app_nil_r, <- app_assoc; cbn [app]; pose proof G5e as GX; unfold pcap_blocks, F_ngnEA.pv, psize, is_ng in GX; cbn [pc_self pc_buffer pc_bufalloc pc_priv] in GX; unfold IBLK; exact GX |].
      split; [rewrite Hsp; exact ST5|]. split; [exact LO|]. split; [unfold ADD_INTERFACE_STACK, STDIO_STACK; rewrite Hsp; lia|].
      split; [rewrite Hsp; lia|]. split; [exact MI5|]. split; [exact TPE|]. split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|].
      split; [exact RSTK5|]. split; [exact RIMG5|]. split; [exact RISH5| exact RTLS5].
    - eapply ucaller_data with (X := 577208%Z); [rewrite Hsp; rewrite unsigned_lit by lia; lia | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | unfold depth_add_interface; lia].
    - rewrite unsigned_lit by lia. exact (proj1 (proj2 (proj2 (proj2 TR)))).
    - intros ff [].
    - reflexivity.
    - rewrite app_nil_r; apply in_or_app; right; left; reflexivity.
    - rewrite app_nil_r; apply in_or_app; right; right; left; reflexivity.
    - unfold PCAP_NG_SF_TOTAL; cbn [pc_bufalloc F_ngnEA.pv]; exact APB.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact P48.
    - exact NG5.
    - exact IFS.
    - clear - W13; lia.
    - clear - W13; lia.
    - exact BUF.
    - exact PFX.
    - cbn [pc_bufdata pc_bufalloc F_ngnEA.pv]; lia.
    - exact DRNG.
    - exact FCUR.
    - rewrite Hsp. split; lia.
    - clear - ALN. Z.div_mod_to_equations. lia.
    - lia.
    - reflexivity.
    - reflexivity.
    - cbn [cur_remaining]; lia.
    - cbn [cur_off cur_remaining pc_bufdata F_ngnEA.pv]; lia.
    - cbn [cur_block_type]; exact Hbt.
    - exact CE1.
    - right; reflexivity. }
    intros [[[ok c5] p5] msg5] ps5 RNG6 ms5 PO. cbv beta in PO.
    destruct PO as (FP6 & a0v & m6 & s' & i' & I' & pad' & bs' & E & OF6 & MI6 & ST6 & AG6 & EP & G6 & NG6 & U1 & U2 & U3 & U4 & BUF6 & PFX6 & LEN6 & GR6 & -> & RM).
    unfold hpost_regs in E. destruct_exs E. subst ms5. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 577208)) with (Z_to_bv 64 577208) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    set (bd' := pc_bufdata p5) in *. clearbody bd'. subst p5.
    change (set_ng s' i' (set_bufdata bd' (pv bq alloc data eb sx ix))) with (pv bq alloc bd' eb s' i') in *.
    cbn [pc_bufdata pc_bufalloc F_ngnEA.pv] in LEN6. change (pc_bufalloc (pv bq alloc data eb sx ix)) with alloc in AG6, BUF6.
    unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL in AG6.
    assert (OF7 : ps_outfile ps5 = o) by (rewrite OF6; exact OF5).
    assert (FP7 : fp_le RNG RNG6) by (eapply fp_le_trans; [exact FP5 | exact FP6]).
    (* [comment removed for export] *)
    band_ind PBAND bP. band_ind BBAND bB. pose proof atop_range as AR.
    assert (HinB2 : In (bq, Bq, alloc) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) by (right; left; reflexivity).
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G5 HLOC HinB2 ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kH & kHr & kH1 & kH2).
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G5 DLOC HinB2 ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kD & kDr & kD1 & kD2).
    cbn [cb_addr cb_size fst snd] in kH1, kH2, kD1, kD2.
    assert (INP : forall a, (P <= a < P + 680)%Z -> client_keeps FL ((CLc ++ [(self, P, 680%Z); (bq, Bq, alloc)]) ++ []) (bv_unsigned sp + -224) a).
    { intros a Ha. right. left. rewrite app_nil_r. apply in_block_app. right. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. exact Ha. }
    assert (HLOC' : clocA FL ((CLc ++ [(self, P, 680%Z); (bq, Bq, alloc)]) ++ []) HA 24) by (eapply clocA_incl; [exact HLOC | rewrite app_nil_r; apply incl_appl, incl_refl | apply incl_refl]).
    assert (DLOC' : clocA FL ((CLc ++ [(self, P, 680%Z); (bq, Bq, alloc)]) ++ []) DA 8) by (eapply clocA_incl; [exact DLOC | rewrite app_nil_r; apply incl_appl, incl_refl | apply incl_refl]).
    (* [comment removed for export] *)
    transport F0 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; lia| lia]).
    transport FS m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; lia| lia]).
    transport HH m6 AG6 ltac:(intros a Ha; rewrite Hh in Ha; split; [eapply clocA_keeps; [exact HLOC'| lia]| lia]).
    transport HD m6 AG6 ltac:(intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; split; [eapply clocA_keeps; [exact DLOC'| lia]| lia]).
    transport PRE0 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; lia| lia]).
    transport P48 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; lia| lia]).
    transport PRE9 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; lia| lia]).
    transport CE2 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; lia| lia]).
    transport HDR m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add hdr_cells pc_header F_ngnEA.pv] in Ha; split; [apply INP; lia| lia]).
    transport OPS m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add pc_ops] in Ha; split; [apply INP; lia| lia]).
    pose proof (rw_cells_uncut _ _ _ _ _ PRE0 P48 ltac:(cbn; lia)) as PRE'. pose proof (rw_cells_uncut _ _ _ _ _ PRE' PRE9 ltac:(cbn; lia)) as PRE. clear PRE' PRE0 P48 PRE9.
    cbn [app] in PRE.
    assert (AG7 : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AG6|]. intros a [[Ha|[Ha|[Ha|Ha]]] _].
      - split; [left; lia| lia].
      - pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G5 ltac:(apply in_block_app; left; apply in_block_app; left; exact Ha)) as AB.
        pose proof (@F_ngnEA.CLc_not_PB rc tlsI H hptr FO GIOA fflagA GL CLc FB FL _ _ _ _ _ a G5 Ha) as NPB.
        assert (NP : ~ (P <= a < P + 680)%Z) by (intros Hr; apply NPB; unfold pcap_blocks, in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; unfold psize, is_ng, F_ngnEA.pv; cbn [pc_priv]; unfold PCAP_NG_SF_TOTAL; lia).
        assert (NB : ~ (Bq <= a < Bq + alloc)%Z) by (intros Hr; apply NPB; unfold pcap_blocks, in_block; apply Exists_cons_tl; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd pc_buffer pc_bufalloc F_ngnEA.pv]; lia).
        split; [right; left; rewrite app_nil_r; apply in_block_app; left; exact Ha| lia].
      - pose proof (gia_in_frames_below _ _ _ GL _ _ _ _ _ _ _ a G5 Ha) as AB.
        pose proof (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G5 Ha) as NBK.
        assert (NP : ~ (P <= a < P + 680)%Z) by (intros Hr; apply NBK; apply in_block_app; left; apply in_block_app; right; unfold pcap_blocks, in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; unfold psize, is_ng, F_ngnEA.pv; cbn [pc_priv]; unfold PCAP_NG_SF_TOTAL; lia).
        assert (NB : ~ (Bq <= a < Bq + alloc)%Z) by (intros Hr; apply NBK; apply in_block_app; left; apply in_block_app; right; unfold pcap_blocks, in_block; apply Exists_cons_tl; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd pc_buffer pc_bufalloc F_ngnEA.pv]; lia).
        split; [right; right; left; exact Ha| lia].
      - pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G5 Ha) as SBD.
        split; [right; right; right; exact Ha| lia]. }
    assert (PBE : pcap_blocks (pv bq alloc bd' eb s' i') P Bq I' = [(self, P, PCAP_NG_SF_TOTAL); (bq, Bq, alloc)] ++ IBLK i' I' s').
    { unfold pcap_blocks, IBLK, F_ngnEA.pv, psize, is_ng. cbn [pc_self pc_buffer pc_bufalloc pc_priv app]. destruct i'; reflexivity. }
    assert (G6' : GIOA L RNG6 ps5 (CLc ++ pcap_blocks (pv bq alloc bd' eb s' i') P Bq I') FB FL m6).
    { eapply GPL; [exact G6|]. rewrite PBE, app_nil_r, (app_assoc CLc). apply Permutation.Permutation_app_comm. }
    assert (WF' : pcap_wf (pv bq alloc bd' eb s' i')).
    { unfold pcap_wf, F_ngnEA.pv in WF |- *.
      cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor pc_linktype pc_linktype_ext pc_header pc_priv] in WF |- *.
      rewrite LEN6, U1, U2. clear - WF U3 U4. lia. }
    (* [comment removed for export] *)
    assert (JOIN : forall cs, rw_cells asegs m6 (P + 216) cs -> cells_size cs = 304%nat ->
              rw_cells asegs m6 P (pcap_cells_gen (pv bq alloc bd' eb s' i') P Bq (C8 (Z_to_bv 64 Afx)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) (set_pj_g (cells_bytes cs) jx'))).
    { intros cs HCS Hcs.
      exact (pcap_cells_join4 _ P (pv bq alloc bd' eb s' i') Bq (C8 (Z_to_bv 64 Afx)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) jx' cs header eq_refl PRE HCS Hcs HDR OPS). }
    cbv beta. ienterG.
    destruct ok; cbn [Z.b2z].
    - (* [comment removed for export] *)
      destruct RM as (HIF6 & (cpad' & HCUR6) & CR1' & CR2' & CR3' & CBT' & HEB6 & ->).
      pose proof (rw_cells_uncut _ _ _ _ _ HEB6 CE2 ltac:(cbn; lia)) as CE6.
      pose proof (JOIN _ CE6 eq_refl) as CELLS6.
      pose proof (rw_cells_uncut _ _ _ _ _ HCUR6 FS ltac:(cbn; lia)) as F46. pose proof (rw_cells_uncut _ _ _ _ _ F0 F46 ltac:(cbn; lia)) as FR6. clear F46.
      assert (PC6 : PCAPR (hptr:=hptr) P (pv bq alloc bd' eb s' i') (pcap_blocks (pv bq alloc bd' eb s' i') P Bq I') FB m6).
      { exists Afx. split; [exact Hin|]. eexists Bq, I', _, pad', bs'.
        split; [reflexivity|]. split; [exact CELLS6|]. split; [exact NG6|]. split; [exact BUF6|]. split; [exact PFX6|]. split; [exact HIF6| exact WF']. }
      hide FR6. hide CELLS6. hide NG6. hide BUF6. hide HH. hide HD. hide HCUR6. hide F0. hide FS. hide CE6. hide HEB6. hide CE2. hide HDR. hide OPS. hide PRE.
      pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
      do 4 zstep.
  zstep.
  if_true.
  unhide FR6. unhide CELLS6. unhide NG6. unhide BUF6. unhide HH. unhide HD.
  apply evtF_done.
  unfold F_ngnEA.ngn_headA in HLOOP. unfold NGN_LOOP_A in HLOOP.
  eapply HLOOP; [exact FP7 | exact ST6 | exact FR6 | reflexivity | exact MI6 | exact G6' | exact PC6 | exact AG7 | exact HH | exact Hh | exact HD | exact Hd | exact OF7 | apply (F_ngnEA.ngn_ucx_m1 TP sp L lo LO BU SPT); exact (proj1 (proj2 TR))].
      - (* [comment removed for export] *)
      destruct RM as (CLOS & (ccs' & HCUR6 & Hccs') & (junk6 & HEB6) & LENM & MOK).
      pose proof (rw_cells_uncut _ _ _ _ _ HEB6 CE2 ltac:(cbn [cells_size csize]; clear - LENM; lia)) as CE6. cbn [app] in CE6.
      pose proof (JOIN _ CE6 ltac:(cbn [cells_size csize]; clear - LENM; lia)) as CELLS6.
      pose proof (rw_cells_uncut _ _ _ _ _ HCUR6 FS ltac:(rewrite Hccs'; cbn; lia)) as F46. pose proof (rw_cells_uncut _ _ _ _ _ F0 F46 ltac:(cbn; lia)) as FR6. clear F46.
      assert (PC6 : PCAPR_closable (hptr:=hptr) P (set_errbuf msg5 (pv bq alloc bd' eb s' i')) (pcap_blocks (pv bq alloc bd' eb s' i') P Bq I') FB m6).
      { exists Afx. split; [exact Hin|]. eexists Bq, I', _, pad', bs'.
        split; [reflexivity|]. split; [exact CELLS6|]. split; [exact NG6|]. split; [exact BUF6|]. split; [exact PFX6|]. split; [| exact WF'].
        unfold ifaces_closable, F_ngnEA.pv. cbn [pc_priv set_errbuf]. unfold ng_ifaces_closable in CLOS. destruct i'; exact CLOS. }
      hide FR6. hide CELLS6. hide NG6. hide BUF6. hide HH. hide HD. hide HCUR6. hide F0. hide FS. hide CE6. hide HEB6. hide CE2. hide HDR. hide OPS. hide PRE.
      pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
      do 5 zstep. if_false.
      zstep.
      unhide FR6. unhide CELLS6. unhide NG6. unhide BUF6. unhide HH. unhide HD.
      apply evtF_done. apply implMG_retb_l. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF.
      eapply (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_ret_m1 rc H hptr GIOA) with (ccs := ccs') (PB' := pcap_blocks (pv bq alloc bd' eb s' i') P Bq I') (hcs' := hcs); try eassumption.
  split; [exact FP7|]. split; [exact G6'|]. split; [exact PC6|]. split; [exact AG7|]. split; [exact HH|]. split; [exact Hh|]. split; [exact HD|]. split; [exact Hd| exact OF7].
    Qed.
End NgnCtx.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnEA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
(* [comment removed for export] *)
(* [comment removed for export] *)
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
Ltac name_field data off a b c d DRNG :=
  set (a := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 0%Z) in *; set (b := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 1%Z) in *; set (c := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 2%Z) in *; set (d := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 3%Z) in *;
  let Ra := fresh "R" a in let Rb := fresh "R" b in let Rc := fresh "R" c in let Rd := fresh "R" d in
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data off 0%Z DRNG ltac:(lia)) as Ra; pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data off 1%Z DRNG ltac:(lia)) as Rb;
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data off 2%Z DRNG ltac:(lia)) as Rc; pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data off 3%Z DRNG ltac:(lia)) as Rd;
  fold a in Ra; fold b in Rb; fold c in Rc; fold d in Rd.

(* [comment removed for export] *)
Definition firstn2_q8__stmt : Prop := forall data (bs : list byte) (k : nat) off,
  firstn (length data) bs = map b8 data -> Z.of_nat k = off -> (off + 2 <= Z.of_nat (length data))%Z ->
  firstn 2 (skipn k bs) = [b8 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 0); b8 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 1)].
Section Sz1.
Variables data bs k off : ltac2:(SecDiet.SzSec.tyM 'firstn2_q8__stmt "vvvv" @data).
#[using="Type"] Lemma firstn2_q8__body : ltac2:(SecDiet.SzSec.bodyP 'firstn2_q8__stmt "vvvv").
Proof.
  intros PFX Hk H1.
 subst off.
  destruct (zslice_2 (Z.of_nat k) data ltac:(lia) H1) as (x0 & x1 & E).
  destruct (get_u8_of_slice2 (Z.of_nat k) data x0 x1 ltac:(lia) H1 E) as [E0 E1].
  transitivity (map b8 (zslice (Z.of_nat k) 2 data)).
  - unfold zslice, zfirstn, zskipn. rewrite <- firstn_map, <- skipn_map, <- PFX. rewrite skipn_firstn_comm, firstn_firstn, Nat2Z.id. f_equal. lia.
  - rewrite E. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8. rewrite Z.add_0_r, E0, E1. reflexivity.
Qed.
End Sz1.
Lemma firstn2_q8 : ltac:(let t := eval cbv delta [firstn2_q8__stmt] in firstn2_q8__stmt in exact t).
Proof. intros data bs k off. ltac2:(SecDiet.SzSec.closeP 'firstn2_q8__body "vvvv"). Qed.

Lemma get_le16_q8' : forall data off, (0 <= off)%Z -> (off + 2 <= Z.of_nat (length data))%Z ->
  get_le16 data off = (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 0 + 256 * OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 1)%Z.
Proof.
  intros data off H0 H1. destruct (zslice_2 off data H0 H1) as (x0 & x1 & E).
  destruct (get_u8_of_slice2 off data x0 x1 H0 H1 E) as [E0 E1].
  rewrite (get_le16_of_slice off data x0 x1 E). unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8. rewrite Z.add_0_r, E0, E1. reflexivity.
Qed.

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
  Hypothesis HLOC : clocA FL CLc HA 24.
  Hypothesis DLOC : clocA FL CLc DA 8.

  Let POSTQ := next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CLc FB lo P HA DA m o.

  (* [comment removed for export] *)
  #[local] Abbreviation ngn_frameA := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_frameA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA).
  #[local] Abbreviation ngn_final := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_final GIOA sp L RNG CLc FB FL P HA DA m o).
  #[local] Abbreviation ngn_finalC := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_finalC GIOA sp L RNG CLc FB FL P HA DA m o).

  Variable trC : list Z.
  Hypothesis ADDIF : add_interface_stmt HO FO sites GIOA TP.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis TR : traces_pcap_ng_next_packet TP L (bv_unsigned ra) trC.

  #[local] Abbreviation pcapT := (pcap hptr hptr).
  #[local] Abbreviation MR := (M (PState H hptr) ((Z + ng_found) * pcap hptr hptr)).
  #[local] Abbreviation pv := (A3P.F_ngnEA.TwB.pv self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).
  #[local] Abbreviation ngn_KF := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF H hptr).
  #[local] Abbreviation ngn_headA := (A3P.F_ngnEA.TwB.ngn_headA GIOA TP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CLc FB FL lo P HA DA Af m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).

  #[using="Type"] Lemma implMG_retb_l : forall {St A B} RNGx (a : A) (k : A -> Monad.M St B) s Q ms, implMG RNGx (k a) s Q ms -> implMG RNGx (mbind (mret a) k) s Q ms.
  Proof. intros St A B RNGx a k s Q ms HH. exact HH. Qed.

  (* [comment removed for export] *)
  Definition ngn_idb_call__stmt : Prop := forall (LOOP : pcapT -> MR),
    ngn_headA (fun p' ps' RNG' ms' => implMG RNG' (mbind (LOOP p') ngn_KF) ps' POSTQ ms') ->
    forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x9 x18 x20 t3' t4' t5' t6' : word) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (bt : Z) (hcs : list cell) (dw : cell) (cpad : list byte),
      fp_le RNG RNG5 ->
      stk asegs m5 lo (bv_unsigned sp + -240) ->
      rw_cells asegs m5 (bv_unsigned sp + -240) (ngn_frameA [C8 (Z_to_bv 64 (Bq + 16)); C8 (Z_to_bv 64 (rem - 8)); C4 (Z_to_bv 64 bt); CB 4 cpad]) -> mem_inv asegs m5 ->
      GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells asegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells asegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (8 <= rem)%Z ->
      (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implMG RNG5 (mbind (mbind (add_interface MOps (prims HO FO sites) (pv bq alloc data eb sx ix) 8 (mkCursor 16 (rem - 8) bt))
                          (fun r => let '(ok, c, p, msg) := r in if ok then LOOP p else mret (inl (-1)%Z, set_errbuf msg p))) ngn_KF) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0' t1' t2' (Z_to_bv 64 168627466) x9 a0' a1' a2' a3' a4' a5' a6' a7'
                 x18 (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) x20 (Z_to_bv 64 2147450880) (Z_to_bv 64 (P + 56))
                 (Z_to_bv 64 (P + 216)) (Z_to_bv 64 (P + 660)) (Z_to_bv 64 P) (Z_to_bv 64 Af) (Z_to_bv 64 (Bq + 8))
                 t3' t4' t5' t6') F (Z_to_bv 64 0x8d03c) fc None m5 (seg_rom asegs)).
  Section Sz4.
  Variables LOOP ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x9 x18 x20 t3' t4' t5' t6' m5 RNG5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw cpad : ltac2:(SecDiet.SzSec.tyM 'ngn_idb_call__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @LOOP).
  #[using="rc tlsI fflagA GL LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HLOC DLOC trC ADDIF GPL TR"] Lemma ngn_idb_call__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_idb_call__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros HLOOP.
 intros FP5 ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (rng_fp_le _ _ _ _ FP5 RSTK) as RSTK5.
    assert (RSPW : rng RNG5 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK5| lia]).
    pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof G5 as G5e. rewrite EPB in G5e.
    assert (HinP : In (self, P, 680%Z) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    assert (HinB : In (bq, Bq, alloc) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; right; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinP) as ((PBAND & P3 & PTOP & P2) & P1 & PUNP & PRNG & PRSH & PAR).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinB) as ((BBAND & B3 & BTOP & B2) & B1 & BUNP & BRNG & BRSH & BAR).
    cbn [cb_addr cb_size fst snd] in *.
    pose proof (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ G5 eq_refl) as [APB API].
    pose proof WF as (W1' & W2' & W3 & W4 & W5' & W6' & W7' & W8' & W9' & W10' & W11 & W12 & W13 & W14).
    unfold A3P.F_ngnEA.TwB.pv, pcap_blocks, psize, is_ng in EPB, APB. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, APB. unfold PCAP_NG_SF_TOTAL in APB.
    unfold A3P.F_ngnEA.TwB.pv in W3, W4, W13. cbn [pc_bufalloc pc_bufdata pc_priv] in W3, W4, W13.
    assert (EBX : Bx' = Bq) by congruence. subst Bx'.
    unfold A3P.F_ngnEA.TwB.pv in Hin. cbn [pc_rfile] in Hin.
    unfold A3P.F_ngnEA.TwB.pv in BUF. cbn [pc_bufalloc] in BUF. cbn [pc_bufdata] in PFX.
    pose proof PRIV as NG5. unfold priv_cells, A3P.F_ngnEA.TwB.pv, PCAP_PRIV_OFF in NG5. cbn [pc_priv] in NG5.
    (* [comment removed for export] *)
    apply pcap_cells_split4 in CELLS as (PRE & CE & HDR & OPS); [|reflexivity].
    apply (rw_cells_split_CB asegs m5 _ [] 304 _ [] [256; 48]%nat) in CE; [|reflexivity]. cbn [mk_CB_cells app] in CE.
    destruct (rw_cells_cut _ _ _ 1 CE) as [CE1 CE2]. clear CE. cbn [firstn skipn cells_size csize Nat.add] in CE1, CE2.
    replace (P + 216 + Z.of_nat 256)%Z with (P + 472)%Z in CE2 by lia.
    unfold pc_pre in PRE. destruct (rw_cells_cut _ _ _ 7 PRE) as [PRE0 PRE7]. destruct (rw_cells_cut _ _ _ 2 PRE7) as [P48 PRE9]. clear PRE PRE7.
    cbn [firstn skipn cells_size csize Nat.add app] in PRE0, P48, PRE9.
    replace (P + Z.of_nat 48)%Z with (P + 48)%Z in P48 by lia. replace (P + Z.of_nat 48 + Z.of_nat 12)%Z with (P + 60)%Z in PRE9 by lia.
    (* [comment removed for export] *)
    pose proof FR5 as FRJ. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_frameA in FRJ. cbn [app] in FRJ.
    destruct (rw_cells_cut _ _ _ 14 FRJ) as [F0 F4]. destruct (rw_cells_cut _ _ _ 4 F4) as [FCUR FS]. clear FRJ F4.
    cbn [firstn skipn cells_size csize Nat.add app] in F0, FCUR, FS.
    replace (bv_unsigned sp + -240 + Z.of_nat 112)%Z with (bv_unsigned sp + -128)%Z in FCUR by lia.
    replace (bv_unsigned sp + -240 + Z.of_nat 112 + Z.of_nat 24)%Z with (bv_unsigned sp + -104)%Z in FS by lia.
    hide F0. hide FCUR. hide FS. hide PRE0. hide P48. hide PRE9. hide CE1. hide CE2. hide HDR. hide OPS. hide NG5. hide BUF. hide HH. hide HD. hide FR5. hide PRIV. hide IFS.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    ienterG. do 5 zstep. zstep. clear MU WM.
    unhide F0. unhide FCUR. unhide FS. unhide PRE0. unhide P48. unhide PRE9. unhide CE1. unhide CE2. unhide HDR. unhide OPS. unhide NG5. unhide BUF. unhide HH. unhide HD. unhide FR5. unhide PRIV. unhide IFS.
  pose proof (rng_fp_le _ _ _ _ FP5 RIMG) as RIMG5. pose proof (rng_fp_le _ _ _ _ FP5 RISH) as RISH5. pose proof (rng_fp_le _ _ _ _ FP5 RTLS) as RTLS5.
  apply evtF_done. apply implMG_bind_assoc. name_sp sp (-240)%Z. eapply implMG_bind.
  { eapply ADDIF with (L := L) (st := ps) (C1 := CLc ++ [(self, P, PCAP_NG_SF_TOTAL); (bq, Bq, alloc)]) (C2 := []) (FB := FB) (FL := FL) (trC := []) (P := P) (B := Bq) (I := Ix')
                      (CUR := (bv_unsigned sp + -128)%Z) (EB := (P + 216)%Z) (lo := lo) (idb_off := 8%Z) (p := pv bq alloc data eb sx ix) (s := sx) (i := ix)
                      (c := mkCursor 16 (rem - 8) bt) (bs := bsx') (ej := firstn 256 (pj_g jx')) (pad := padx) (cpad := cpad).
    - split; [rewrite app_nil_r, <- app_assoc; cbn [app]; pose proof G5e as GX; unfold pcap_blocks, A3P.F_ngnEA.TwB.pv, psize, is_ng in GX; cbn [pc_self pc_buffer pc_bufalloc pc_priv] in GX; unfold IBLK; exact GX |].
      split; [rewrite Hsp; exact ST5|]. split; [exact LO|]. split; [unfold ADD_INTERFACE_STACK, STDIO_STACK; rewrite Hsp; lia|].
      split; [rewrite Hsp; lia|]. split; [exact MI5|]. split; [exact TPE|]. split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|].
      split; [exact RSTK5|]. split; [exact RIMG5|]. split; [exact RISH5| exact RTLS5].
    - eapply ucaller_data with (X := 577620%Z); [rewrite Hsp; rewrite unsigned_lit by lia; lia | reflexivity | unfold ACLIENT_LO, ACLIENT_HI; lia | unfold depth_add_interface; lia].
    - rewrite unsigned_lit by lia. exact (proj1 (proj2 (proj2 (proj2 TR)))).
    - intros ff [].
    - reflexivity.
    - rewrite app_nil_r; apply in_or_app; right; left; reflexivity.
    - rewrite app_nil_r; apply in_or_app; right; right; left; reflexivity.
    - unfold PCAP_NG_SF_TOTAL; cbn [pc_bufalloc A3P.F_ngnEA.TwB.pv]; exact APB.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact P48.
    - exact NG5.
    - exact IFS.
    - clear - W13; lia.
    - clear - W13; lia.
    - exact BUF.
    - exact PFX.
    - cbn [pc_bufdata pc_bufalloc A3P.F_ngnEA.TwB.pv]; lia.
    - exact DRNG.
    - exact FCUR.
    - rewrite Hsp. split; lia.
    - clear - ALN. Z.div_mod_to_equations. lia.
    - lia.
    - reflexivity.
    - reflexivity.
    - cbn [cur_remaining]; lia.
    - cbn [cur_off cur_remaining pc_bufdata A3P.F_ngnEA.TwB.pv]; lia.
    - cbn [cur_block_type]; exact Hbt.
    - exact CE1.
    - right; reflexivity. }
    intros [[[ok c5] p5] msg5] ps5 RNG6 ms5 PO. cbv beta in PO.
    destruct PO as (FP6 & a0v & m6 & s' & i' & I' & pad' & bs' & E & OF6 & MI6 & ST6 & AG6 & EP & G6 & NG6 & U1 & U2 & U3 & U4 & BUF6 & PFX6 & LEN6 & GR6 & -> & RM).
    unfold hpost_regs in E. destruct_exs E. subst ms5. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 577620)) with (Z_to_bv 64 577620) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    set (bd' := pc_bufdata p5) in *. clearbody bd'. subst p5.
    change (set_ng s' i' (set_bufdata bd' (pv bq alloc data eb sx ix))) with (pv bq alloc bd' eb s' i') in *.
    cbn [pc_bufdata pc_bufalloc A3P.F_ngnEA.TwB.pv] in LEN6. change (pc_bufalloc (pv bq alloc data eb sx ix)) with alloc in AG6, BUF6.
    unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL in AG6.
    assert (OF7 : ps_outfile ps5 = o) by (rewrite OF6; exact OF5).
    assert (FP7 : fp_le RNG RNG6) by (eapply fp_le_trans; [exact FP5 | exact FP6]).
    (* [comment removed for export] *)
    band_ind PBAND bP. band_ind BBAND bB. pose proof atop_range as AR.
    assert (HinB2 : In (bq, Bq, alloc) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) by (right; left; reflexivity).
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G5 HLOC HinB2 ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kH & kHr & kH1 & kH2).
    destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G5 DLOC HinB2 ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kD & kDr & kD1 & kD2).
    cbn [cb_addr cb_size fst snd] in kH1, kH2, kD1, kD2.
    assert (INP : forall a, (P <= a < P + 680)%Z -> client_keeps FL ((CLc ++ [(self, P, 680%Z); (bq, Bq, alloc)]) ++ []) (bv_unsigned sp + -240) a).
    { intros a Ha. right. left. rewrite app_nil_r. apply in_block_app. right. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. exact Ha. }
    assert (HLOC' : clocA FL ((CLc ++ [(self, P, 680%Z); (bq, Bq, alloc)]) ++ []) HA 24) by (eapply clocA_incl; [exact HLOC | rewrite app_nil_r; apply incl_appl, incl_refl | apply incl_refl]).
    assert (DLOC' : clocA FL ((CLc ++ [(self, P, 680%Z); (bq, Bq, alloc)]) ++ []) DA 8) by (eapply clocA_incl; [exact DLOC | rewrite app_nil_r; apply incl_appl, incl_refl | apply incl_refl]).
    (* [comment removed for export] *)
    transport F0 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; lia| lia]).
    transport FS m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; lia| lia]).
    transport HH m6 AG6 ltac:(intros a Ha; rewrite Hh in Ha; split; [eapply clocA_keeps; [exact HLOC'| lia]| lia]).
    transport HD m6 AG6 ltac:(intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; split; [eapply clocA_keeps; [exact DLOC'| lia]| lia]).
    transport PRE0 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; lia| lia]).
    transport P48 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; lia| lia]).
    transport PRE9 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; lia| lia]).
    transport CE2 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; lia| lia]).
    transport HDR m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add hdr_cells pc_header A3P.F_ngnEA.TwB.pv] in Ha; split; [apply INP; lia| lia]).
    transport OPS m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add pc_ops] in Ha; split; [apply INP; lia| lia]).
    pose proof (rw_cells_uncut _ _ _ _ _ PRE0 P48 ltac:(cbn; lia)) as PRE'. pose proof (rw_cells_uncut _ _ _ _ _ PRE' PRE9 ltac:(cbn; lia)) as PRE. clear PRE' PRE0 P48 PRE9.
    cbn [app] in PRE.
    assert (AG7 : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AG6|]. intros a [[Ha|[Ha|[Ha|Ha]]] _].
      - split; [left; lia| lia].
      - pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G5 ltac:(apply in_block_app; left; apply in_block_app; left; exact Ha)) as AB.
        pose proof (@A3P.F_ngnEA.TwB.CLc_not_PB rc tlsI H hptr FO GIOA fflagA GL CLc FB FL _ _ _ _ _ a G5 Ha) as NPB.
        assert (NP : ~ (P <= a < P + 680)%Z) by (intros Hr; apply NPB; unfold pcap_blocks, in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; unfold psize, is_ng, A3P.F_ngnEA.TwB.pv; cbn [pc_priv]; unfold PCAP_NG_SF_TOTAL; lia).
        assert (NB : ~ (Bq <= a < Bq + alloc)%Z) by (intros Hr; apply NPB; unfold pcap_blocks, in_block; apply Exists_cons_tl; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd pc_buffer pc_bufalloc A3P.F_ngnEA.TwB.pv]; lia).
        split; [right; left; rewrite app_nil_r; apply in_block_app; left; exact Ha| lia].
      - pose proof (gia_in_frames_below _ _ _ GL _ _ _ _ _ _ _ a G5 Ha) as AB.
        pose proof (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G5 Ha) as NBK.
        assert (NP : ~ (P <= a < P + 680)%Z) by (intros Hr; apply NBK; apply in_block_app; left; apply in_block_app; right; unfold pcap_blocks, in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; unfold psize, is_ng, A3P.F_ngnEA.TwB.pv; cbn [pc_priv]; unfold PCAP_NG_SF_TOTAL; lia).
        assert (NB : ~ (Bq <= a < Bq + alloc)%Z) by (intros Hr; apply NBK; apply in_block_app; left; apply in_block_app; right; unfold pcap_blocks, in_block; apply Exists_cons_tl; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd pc_buffer pc_bufalloc A3P.F_ngnEA.TwB.pv]; lia).
        split; [right; right; left; exact Ha| lia].
      - pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G5 Ha) as SBD.
        split; [right; right; right; exact Ha| lia]. }
    assert (PBE : pcap_blocks (pv bq alloc bd' eb s' i') P Bq I' = [(self, P, PCAP_NG_SF_TOTAL); (bq, Bq, alloc)] ++ IBLK i' I' s').
    { unfold pcap_blocks, IBLK, A3P.F_ngnEA.TwB.pv, psize, is_ng. cbn [pc_self pc_buffer pc_bufalloc pc_priv app]. destruct i'; reflexivity. }
    assert (G6' : GIOA L RNG6 ps5 (CLc ++ pcap_blocks (pv bq alloc bd' eb s' i') P Bq I') FB FL m6).
    { eapply GPL; [exact G6|]. rewrite PBE, app_nil_r, (app_assoc CLc). apply Permutation.Permutation_app_comm. }
    assert (WF' : pcap_wf (pv bq alloc bd' eb s' i')).
    { unfold pcap_wf, A3P.F_ngnEA.TwB.pv in WF |- *.
      cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor pc_linktype pc_linktype_ext pc_header pc_priv] in WF |- *.
      rewrite LEN6, U1, U2. clear - WF U3 U4. lia. }
    (* [comment removed for export] *)
    assert (JOIN : forall cs, rw_cells asegs m6 (P + 216) cs -> cells_size cs = 304%nat ->
              rw_cells asegs m6 P (pcap_cells_gen (pv bq alloc bd' eb s' i') P Bq (C8 (Z_to_bv 64 Afx)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) (set_pj_g (cells_bytes cs) jx'))).
    { intros cs HCS Hcs.
      exact (pcap_cells_join4 _ P (pv bq alloc bd' eb s' i') Bq (C8 (Z_to_bv 64 Afx)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) jx' cs header eq_refl PRE HCS Hcs HDR OPS). }
    cbv beta. ienterG.
    destruct ok; cbn [Z.b2z].
    - (* [comment removed for export] *)
      destruct RM as (HIF6 & (cpad' & HCUR6) & CR1' & CR2' & CR3' & CBT' & HEB6 & ->).
      pose proof (rw_cells_uncut _ _ _ _ _ HEB6 CE2 ltac:(cbn; lia)) as CE6.
      pose proof (JOIN _ CE6 eq_refl) as CELLS6.
      pose proof (rw_cells_uncut _ _ _ _ _ HCUR6 FS ltac:(cbn; lia)) as F46. pose proof (rw_cells_uncut _ _ _ _ _ F0 F46 ltac:(cbn; lia)) as FR6. clear F46.
      assert (PC6 : PCAPR (hptr:=hptr) P (pv bq alloc bd' eb s' i') (pcap_blocks (pv bq alloc bd' eb s' i') P Bq I') FB m6).
      { exists Afx. split; [exact Hin|]. eexists Bq, I', _, pad', bs'.
        split; [reflexivity|]. split; [exact CELLS6|]. split; [exact NG6|]. split; [exact BUF6|]. split; [exact PFX6|]. split; [exact HIF6| exact WF']. }
      hide FR6. hide CELLS6. hide NG6. hide BUF6. hide HH. hide HD. hide HCUR6. hide F0. hide FS. hide CE6. hide HEB6. hide CE2. hide HDR. hide OPS. hide PRE.
      pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
      do 6 zstep.   (* [comment removed for export] *)
  zstep.
  if_true.
  unhide FR6. unhide CELLS6. unhide NG6. unhide BUF6. unhide HH. unhide HD.
  apply evtF_done.
  unfold A3P.F_ngnEA.TwB.ngn_headA in HLOOP. unfold NGN_LOOP_A in HLOOP.
  eapply HLOOP; [exact FP7 | exact ST6 | exact FR6 | reflexivity | exact MI6 | exact G6' | exact PC6 | exact AG7 | exact HH | exact Hh | exact HD | exact Hd | exact OF7 | apply (A3P.F_ngnEA.TwB.ngn_ucx_m1 TP sp L lo LO BU SPT); exact (proj1 (proj2 TR))].
      - (* [comment removed for export] *)
      destruct RM as (CLOS & (ccs' & HCUR6 & Hccs') & (junk6 & HEB6) & LENM & MOK).
      pose proof (rw_cells_uncut _ _ _ _ _ HEB6 CE2 ltac:(cbn [cells_size csize]; clear - LENM; lia)) as CE6. cbn [app] in CE6.
      pose proof (JOIN _ CE6 ltac:(cbn [cells_size csize]; clear - LENM; lia)) as CELLS6.
      pose proof (rw_cells_uncut _ _ _ _ _ HCUR6 FS ltac:(rewrite Hccs'; cbn; lia)) as F46. pose proof (rw_cells_uncut _ _ _ _ _ F0 F46 ltac:(cbn; lia)) as FR6. clear F46.
      assert (PC6 : PCAPR_closable (hptr:=hptr) P (set_errbuf msg5 (pv bq alloc bd' eb s' i')) (pcap_blocks (pv bq alloc bd' eb s' i') P Bq I') FB m6).
      { exists Afx. split; [exact Hin|]. eexists Bq, I', _, pad', bs'.
        split; [reflexivity|]. split; [exact CELLS6|]. split; [exact NG6|]. split; [exact BUF6|]. split; [exact PFX6|]. split; [| exact WF'].
        unfold ifaces_closable, A3P.F_ngnEA.TwB.pv. cbn [pc_priv set_errbuf]. unfold ng_ifaces_closable in CLOS. destruct i'; exact CLOS. }
      hide FR6. hide CELLS6. hide NG6. hide BUF6. hide HH. hide HD. hide HCUR6. hide F0. hide FS. hide CE6. hide HEB6. hide CE2. hide HDR. hide OPS. hide PRE.
      pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
      do 7 zstep. if_false.
      zstep.
      unhide FR6. unhide CELLS6. unhide NG6. unhide BUF6. unhide HH. unhide HD.
      apply evtF_done. apply implMG_retb_l. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF.
      eapply (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_ret_m1 rc H hptr GIOA) with (ccs := ccs') (PB' := pcap_blocks (pv bq alloc bd' eb s' i') P Bq I') (hcs' := hcs); try eassumption.
  split; [exact FP7|]. split; [exact G6'|]. split; [exact PC6|]. split; [exact AG7|]. split; [exact HH|]. split; [exact Hh|]. split; [exact HD|]. split; [exact Hd| exact OF7].
  Qed.
  End Sz4.
  #[using="rc tlsI fflagA GL LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HLOC DLOC trC ADDIF GPL TR"] Lemma ngn_idb_call : ltac:(let t := eval cbv delta [ngn_idb_call__stmt] in ngn_idb_call__stmt in exact t).
  Proof. intros LOOP HLOOP ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x9 x18 x20 t3' t4' t5' t6' m5 RNG5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw cpad. ltac2:(SecDiet.SzSec.closeP 'ngn_idb_call__body "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgnCtx.
End CANSEC1.
End TwB.
End F_ngnICA.

(* [comment removed for export] *)
Module F_aiAA.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_hlenA__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_ngnE2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_hlenA__A3P.F_aiDA.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextD__S3.
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

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section AIA.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  #[local] Abbreviation pcapT := (PcapTypes.pcap hptr hptr).
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (L : alayout) (RNG : footprint) (st : PS) (C1 C2 FB : list cblk) (FL : list fblock) (P B I CUR EB lo idb_off : Z).
  Variables (p : pcapT) (s : pcap_ng_sf) (i : option hptr) (c : cursor) (bs ej pad cpad : list byte).
  Hypothesis G : GIOA L RNG st (C1 ++ IBLK i I s ++ C2) FB FL m.
  Hypothesis LO : (ATOP + 4096 <= lo)%Z.
  Hypothesis BU : (lo + 16512 <= bv_unsigned sp)%Z.
  Hypothesis SPT : (bv_unsigned sp + 16 < al_top L /\ al_top L <= 2^47)%Z.
  Hypothesis RSTK : rng RNG lo (al_top L - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.
  Hypothesis RTLS : rng_atls RNG.
  Hypothesis TPE : tp = Z_to_bv 64 ATP.
  Hypothesis ALN : (bv_unsigned sp mod 16 = 0)%Z.

  #[local] Abbreviation POSTQ := (add_interface_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P B CUR EB p s c bs ej m (ps_outfile st)).
  #[local] Abbreviation AGP := (ai_AGP FL sp C1 C2 P B CUR EB p m).
  #[local] Abbreviation FRAME := (ai_FRAME ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).

  (* [comment removed for export] *)
  Definition ai_exit__stmt : Prop := forall (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 : word)
      (m3 : mem) (RNG3 : footprint) (st3 : PS) (ok : bool) (c' : cursor) (p' : pcapT) (msg : list Z) (hd : list cell),
    fp_le RNG RNG3 ->
    mem_inv asegs m3 -> stk asegs m3 lo (bv_unsigned sp + -128) -> AGP m3 ->
    rw_cells asegs m3 (bv_unsigned sp + -128) hd -> cells_size hd = 24%nat -> FRAME m3 ->
    ai_REST GIOA L RNG3 FL C1 C2 FB P B CUR EB p s c ej (ps_outfile st) m3 st3 (ok, c', p', msg) ->
    evtF asegs RNG3 (POSTQ (ok, c', p', msg) st3 RNG3)
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' y0 y1 (Z_to_bv 64 (Z.b2z ok)) a1' a2' a3' a4' a5' a6' a7'
               y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 t3' t4' t5' t6') F (Z_to_bv 64 0x8c970) fc None m3 (seg_rom asegs)).
  Section Sz1.
  Variables ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 m3 RNG3 st3 ok c' p' msg hd : ltac2:(SecDiet.SzSec.tyM 'ai_exit__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  #[using="rc BU SPT RSTK"] Lemma ai_exit__body : ltac2:(SecDiet.SzSec.bodyP 'ai_exit__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros FP3 MI3 ST3 AG3 HD3 Hhd FR3 REST.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (RSPW : rng RNG3 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact (rng_fp_le _ _ _ _ FP3 RSTK)| lia]).
    pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    destruct (rw_cells_forget _ _ _ _ HD3) as [hj HD3']. clear HD3. rewrite Hhd in HD3'.
    unfold ai_FRAME in FR3.
    do 15 zstep.
    release_frame HD3' ST3 (bv_unsigned sp + -104)%Z. release_frame FR3 ST3 (bv_unsigned sp).
    apply evtF_done. unfold add_interface_post. split; [exact FP3|].
    destruct REST as (s' & i' & I' & pad' & bs' & OFr & E1 & G3 & NG3 & U1 & U2 & U3 & U4 & BUF3 & PFX3 & LEN3 & GR3 & RM).
    lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 (Z.b2z ok)), mm, s', i', I', pad', bs' end.
    split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
    split; [exact OFr|]. split; [assumption|]. split; [assumption|]. split; [exact AG3|].
    split; [exact E1|]. split; [exact G3|]. split; [exact NG3|]. split; [exact U1|]. split; [exact U2|]. split; [exact U3|]. split; [exact U4|].
    split; [exact BUF3|]. split; [exact PFX3|]. split; [exact LEN3|]. split; [exact GR3|]. split; [reflexivity|]. exact RM.
  Qed.
  End Sz1.
  #[using="rc BU SPT RSTK"] Lemma ai_exit : ltac:(let t := eval cbv delta [ai_exit__stmt] in ai_exit__stmt in exact t).
  Proof. intros ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 m3 RNG3 st3 ok c' p' msg hd. ltac2:(SecDiet.SzSec.closeP 'ai_exit__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis HinP : In (pc_self p, P, PCAP_NG_SF_TOTAL) (C1 ++ C2).
  Hypothesis HinB : In (pc_buffer p, B, pc_bufalloc p) (C1 ++ C2).
  Hypothesis P14 : (0 < P /\ P + 680 <= ATOP)%Z.
  Hypothesis B14 : (0 < B /\ B + pc_bufalloc p <= ATOP)%Z.
  Hypothesis LENB : (Z.of_nat (length (pc_bufdata p)) <= pc_bufalloc p < 2^32)%Z.
  Hypothesis CURS : (bv_unsigned sp <= CUR /\ CUR + 24 <= al_top L)%Z.
  (* [comment removed for export] *)
  Hypothesis EBL : clocA FL (C1 ++ C2) EB 256.
  Hypothesis EBP : (EB + 256 <= P + 648 \/ P + 680 <= EB)%Z.
  Hypothesis EBB : (EB + 256 <= B \/ B + pc_bufalloc p <= EB)%Z.

  #[local] Abbreviation AIREST_F := (ai_REST_F GIOA L).

  (* [comment removed for export] *)
  Definition airest_f_frame__stmt : Prop := forall (m3 m4 : mem) (RNG3 : footprint) (st' : PS) (c' : cursor) (p' : pcapT) (lo1 hi1 k : Z),
    AIREST_F RNG3 FL C1 C2 FB P B CUR p s (ps_outfile st) m3 st' c' p' -> munch [(lo1, hi1); (EB, EB + k)]%Z m3 m4 -> wmono asegs m3 m4 ->
    (ATOP + 4096 <= lo1)%Z -> (hi1 <= bv_unsigned sp + -128)%Z -> (0 <= k <= 256)%Z ->
    AIREST_F RNG3 FL C1 C2 FB P B CUR p s (ps_outfile st) m4 st' c' p'.
  Section Sz2.
  Variables m3 m4 RNG3 st' c' p' lo1 hi1 k : ltac2:(SecDiet.SzSec.tyM 'airest_f_frame__stmt "vvvvvvvvv" @m3).
  #[using="tlsI FO fflagA GL lo LO BU GPL P14 B14 LENB CURS EBL EBP EBB"] Lemma airest_f_frame__body : ltac2:(SecDiet.SzSec.bodyP 'airest_f_frame__stmt "vvvvvvvvv").
  Proof.
    intros (s' & i' & I' & pad' & bs' & OFr & E1 & G3 & NG3 & U1 & U2 & U3 & U4 & BUF3 & PFX3 & LEN3 & GR3 & IC3 & (ccs' & CC3 & Hccs')) MU WM L1 H1 HK.
    pose proof atop_range as AR.
    assert (AGS : agrees_on (fun a => outside [(lo1, hi1); (EB, EB + k)]%Z a) m3 m4) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
    assert (EBL3 : clocA FL (IBLK i' I' s' ++ C1 ++ C2) EB 256) by (eapply clocA_incl; [exact EBL | apply incl_appr, incl_refl | apply incl_refl]).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G3 EBL3) as (EBLO & EBHI).
    exists s', i', I', pad', bs'. split; [exact OFr|]. split; [exact E1|].
    split.
    { eapply (gl_client_frame _ _ _ GL); [exact G3 | exact MU | exact WM |].
      apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [| apply Forall_nil].
      apply (clocA_iv FL (IBLK i' I' s' ++ C1 ++ C2) EB k). eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_ngnE2A.clocA_sub; [exact EBL3 | lia | lia]. }
    unfold PCAP_PRIV_OFF in *.
    split; [transport NG3 m4 AGS ltac:(intros a Ha; unfold ng_cells in Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia); exact NG3|].
    split; [exact U1|]. split; [exact U2|]. split; [exact U3|]. split; [exact U4|].
    split; [transport BUF3 m4 AGS ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia); exact BUF3|].
    split; [exact PFX3|]. split; [exact LEN3|]. split; [exact GR3|].
    split.
    { destruct i' as [q|]; [| exact IC3]. destruct IC3 as [(junk & IB3) SZ]. split; [| exact SZ]. exists junk.
      assert (G3p : GIOA L RNG3 st' ((C1 ++ C2) ++ IBLK (Some q) I' s') FB FL m3) by (eapply GPL; [exact G3| apply Permutation.Permutation_app_comm]).
      destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G3p EBL (or_introl eq_refl : In (q, I', (40 * ng_ifaces_size s')%Z) (IBLK (Some q) I' s')) ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kI & kIr & kI1 & kI2).
      cbn [cb_addr cb_size fst snd] in kI1, kI2.
      assert (HinI : In (q, I', (40 * ng_ifaces_size s')%Z) ((IBLK (Some q) I' s' ++ C1 ++ C2) ++ FB)) by (apply in_or_app; left; left; reflexivity).
      pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G3 HinI) as ((IBAND & I3 & ITOP & I2) & I1 & _). cbn [cb_addr cb_size fst snd] in *.
      transport IB3 m4 AGS ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia). exact IB3. }
    exists ccs'. split; [| exact Hccs'].
    transport CC3 m4 AGS ltac:(intros a Ha; rewrite Hccs' in Ha; cbn [outside fst snd]; lia). exact CC3.
  Qed.
  End Sz2.
  #[using="tlsI FO fflagA GL lo LO BU GPL P14 B14 LENB CURS EBL EBP EBB"] Lemma airest_f_frame : ltac:(let t := eval cbv delta [airest_f_frame__stmt] in airest_f_frame__stmt in exact t).
  Proof. intros m3 m4 RNG3 st' c' p' lo1 hi1 k. ltac2:(SecDiet.SzSec.closeP 'airest_f_frame__body "vvvvvvvvv"). Qed.

  #[using="Type"] Lemma airest_f_done : forall (m' : mem) (RNG3 : footprint) (st' : PS) (c' : cursor) (p' : pcapT) (msg : list Z),
    AIREST_F RNG3 FL C1 C2 FB P B CUR p s (ps_outfile st) m' st' c' p' ->
    (exists junk'', rw_cells asegs m' EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk'']) ->
    (Z.of_nat (length msg) < 256)%Z -> Forall (fun z => 0 < z < 256)%Z msg ->
    ai_REST GIOA L RNG3 FL C1 C2 FB P B CUR EB p s c ej (ps_outfile st) m' st' (false, c', p', msg).
  Proof.
    intros m' RNG3 st' c' p' msg (s' & i' & I' & pad' & bs' & OFr & E1 & G3 & NG3 & U1 & U2 & U3 & U4 & BUF3 & PFX3 & LEN3 & GR3 & IC3 & CC3) HE HL HOK.
    exists s', i', I', pad', bs'. split; [exact OFr|]. split; [exact E1|]. split; [exact G3|]. split; [exact NG3|]. split; [exact U1|]. split; [exact U2|]. split; [exact U3|]. split; [exact U4|].
    split; [exact BUF3|]. split; [exact PFX3|]. split; [exact LEN3|]. split; [exact GR3|]. cbv iota. split; [exact IC3|]. split; [exact CC3|]. split; [exact HE|]. split; [exact HL| exact HOK].
  Qed.

  (* [comment removed for export] *)
  Hypothesis EBO : cobjA RNG m FL (C1 ++ C2) EB 256 \/ (P + 216 = EB)%Z.

  (* [comment removed for export] *)
  Definition ai_ksh__stmt : Prop := forall (m3 : mem), AGP m3 -> agrees_on (in_frame_sh FL) m m3.
  Section Sz4.
  Variables m3 : ltac2:(SecDiet.SzSec.tyM 'ai_ksh__stmt "v" @m3).
  #[using="rc tlsI H FO GIOA fflagA GL L RNG st FB I lo s i G LO BU HinP HinB CURS EBL"] Lemma ai_ksh__body : ltac2:(SecDiet.SzSec.bodyP 'ai_ksh__stmt "v").
  Proof.
    intros AG.
 pose proof atop_range as AR.
    assert (HinP' : In (pc_self p, P, PCAP_NG_SF_TOTAL) ((C1 ++ IBLK i I s ++ C2) ++ FB)).
    { apply in_or_app. left. apply in_app_iff in HinP as [X|X]; apply in_or_app; [left; exact X| right; apply in_or_app; right; exact X]. }
    assert (HinB' : In (pc_buffer p, B, pc_bufalloc p) ((C1 ++ IBLK i I s ++ C2) ++ FB)).
    { apply in_or_app. left. apply in_app_iff in HinB as [X|X]; apply in_or_app; [left; exact X| right; apply in_or_app; right; exact X]. }
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinP') as ((PBAND & _) & _). pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinB') as ((BBAND & _) & _).
    cbn [cb_addr cb_size fst snd] in PBAND, BBAND.
    assert (EBL0 : clocA FL (C1 ++ IBLK i I s ++ C2) EB 256).
    { eapply clocA_incl; [exact EBL | | apply incl_refl]. intros x Hx. apply in_app_iff in Hx as [X|X]; apply in_or_app; [left; exact X| right; apply in_or_app; right; exact X]. }
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G EBL0 ltac:(lia)) as EBAND.
    eapply agrees_on_weaken; [exact AG|]. intros a Ha.
    pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G Ha) as BD.
    split; [right; right; right; exact Ha|].
    pose proof (ablk_clear_band _ _ a PBAND ltac:(unfold KLS; lia)) as NP. pose proof (ablk_clear_band _ _ a BBAND ltac:(unfold KLS; lia)) as NB.
    pose proof (ablk_clear_band _ _ a EBAND ltac:(unfold KLS; lia)) as NE.
    unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL in *. lia.
  Qed.
  End Sz4.
  #[using="rc tlsI H FO GIOA fflagA GL L RNG st FB I lo s i G LO BU HinP HinB CURS EBL"] Lemma ai_ksh : ltac:(let t := eval cbv delta [ai_ksh__stmt] in ai_ksh__stmt in exact t).
  Proof. intros m3. ltac2:(SecDiet.SzSec.closeP 'ai_ksh__body "v"). Qed.

  Definition ai_eb_cobj__stmt : Prop := forall (RNG3 : footprint) (st3 : PS) (CL3 : list cblk) (m3 : mem),
    GIOA L RNG3 st3 CL3 FB FL m3 -> incl (C1 ++ C2) CL3 -> AGP m3 -> cobjA RNG3 m3 FL CL3 EB 256.
  Section Sz5.
  Variables RNG3 st3 CL3 m3 : ltac2:(SecDiet.SzSec.tyM 'ai_eb_cobj__stmt "vvvv" @RNG3).
  #[using="tlsI FO fflagA GL RNG st I lo s i G LO BU HinP HinB CURS EBL EBP EBB EBO"] Lemma ai_eb_cobj__body : ltac2:(SecDiet.SzSec.bodyP 'ai_eb_cobj__stmt "vvvv").
  Proof.
    intros G3 INC AG.
    destruct EBO as [O| <-].
    - pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ O G3 INC (incl_refl _) (ai_ksh _ AG) ltac:(lia)) as [LOC AO].
      split; [eapply clocA_incl; [exact LOC | exact INC | apply incl_refl]| exact AO].
    - assert (HinP3 : In (pc_self p, P, PCAP_NG_SF_TOTAL) (CL3 ++ FB)) by (apply in_or_app; left; apply INC; exact HinP).
      pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G3 HinP3) as PBLK.
      split; [left; exists (pc_self p, P, PCAP_NG_SF_TOTAL); split; [apply INC; exact HinP| cbn [cb_addr cb_size fst snd]; unfold PCAP_NG_SF_TOTAL; lia]|].
      eapply blockA_aobj; [exact PBLK | cbn [cb_addr cb_size fst snd]; lia | cbn [cb_addr cb_size fst snd]; unfold PCAP_NG_SF_TOTAL; lia | lia].
  Qed.
  End Sz5.
  #[using="tlsI FO fflagA GL RNG st I lo s i G LO BU HinP HinB CURS EBL EBP EBB EBO"] Lemma ai_eb_cobj : ltac:(let t := eval cbv delta [ai_eb_cobj__stmt] in ai_eb_cobj__stmt in exact t).
  Proof. intros RNG3 st3 CL3 m3. ltac2:(SecDiet.SzSec.closeP 'ai_eb_cobj__body "vvvv"). Qed.

  (* [comment removed for export] *)
  Definition ai_snp__stmt : Prop := forall (ra' t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 a3v a4v : word)
      (m3 : mem) (RNG3 : footprint) (st3 : PS) (fs : string) (args : list farg) (FMTA : Z) (msg : list Z) (c' : cursor) (p' : pcapT) (hd : list cell),
    fp_le RNG RNG3 -> mem_inv asegs m3 -> stk asegs m3 lo (bv_unsigned sp + -128) -> AGP m3 ->
    rw_cells asegs m3 (bv_unsigned sp + -128) hd -> cells_size hd = 24%nat -> FRAME m3 ->
    rw_cells asegs m3 EB [CB 256 ej] ->
    fmt_at m3 FMTA fs -> fmt_ok fs args = true -> (length args <= 3)%nat ->
    (forall (CL : list cblk) D dn, Forall2 (farg_word true L RNG3 FL CL (bv_unsigned sp + -128) D dn m3) args (firstn (length args) [a3v; a4v; a5'])) ->
    Fmt.snprintf 256 fs args = msg -> items_okb (fmt fs) = true -> Forall arg_ok args ->
    AIREST_F RNG3 FL C1 C2 FB P B CUR p s (ps_outfile st) m3 st3 c' p' ->
    evtF asegs RNG3 (POSTQ (false, c', p', msg) st3 RNG3)
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' y0 y1 (Z_to_bv 64 EB) (Z_to_bv 64 256) (Z_to_bv 64 FMTA) a3v a4v a5' a6' a7'
               y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 t3' t4' t5' t6') F (Z_to_bv 64 0x8c968) fc None m3 (seg_rom asegs)).
  Section Sz6.
  Variables ra' t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 a3v a4v m3 RNG3 st3 fs args FMTA msg c' p' hd : ltac2:(SecDiet.SzSec.tyM 'ai_snp__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  #[using="FO fflagA GL SNPRINTF I i G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO"] Lemma ai_snp__body : ltac2:(SecDiet.SzSec.bodyP 'ai_snp__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros FP3 MI3 ST3 AG3 HD3 Hhd FR3 HEB3 FAT FOK ALEN FW EMSG FIT AOK REST.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof atop_range as AR.
    pose proof REST as REST'. destruct REST' as (s' & i' & I' & pad' & bs' & _ & _ & G3 & _).
    pose proof (ai_eb_cobj _ _ _ _ G3 ltac:(apply incl_appr, incl_refl) AG3) as OEB.
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G3 (proj1 OEB)) as (EBLO & EBHI).
    pose proof (rng_fp_le _ _ _ _ FP3 RSTK) as RSTK3. pose proof (rng_fp_le _ _ _ _ FP3 RIMG) as RIMG3.
    pose proof (rng_fp_le _ _ _ _ FP3 RISH) as RISH3. pose proof (rng_fp_le _ _ _ _ FP3 RTLS) as RTLS3.
    unfold ai_FRAME in FR3.
    hide HD3. hide FR3. hide HEB3.
    pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    zstep. unhide HEB3. clear MU WM.
    name_sp sp (-128)%Z.
    eapply evtF_cut.
    { eapply SNPRINTF with (L := L) (s := st3) (CL := IBLK i' I' s' ++ C1 ++ C2) (FB := FB) (FL := FL) (lo := lo) (DST := EB) (n := 256%Z) (FMTA := FMTA) (fs := fs) (args := args) (junk := ej);
        [ split; [exact G3|]; split; [rewrite Hsp; exact ST3|]; split; [lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
          split; [rewrite Hsp; lia|]; split; [exact MI3|]; split; [exact TPE|]; split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|];
          split; [exact RSTK3|]; split; [exact RIMG3|]; split; [exact RISH3| exact RTLS3]
        | reflexivity | reflexivity | reflexivity | lia | exact FAT | exact FOK | exact ALEN | rewrite Hsp; apply FW | exact HEB3 | exact OEB ]. }
    cbv beta. intros ms' PO. destruct PO as (av4 & m4 & junk4 & E & MU4 & WM4 & MI4 & ST4 & -> & HEB4).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 575852)) with (Z_to_bv 64 575852) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    unfold STDIO_STACK in MU4.
    assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -128 - 16384, bv_unsigned sp + -128); (EB, EB + 256)]%Z a) m3 m4)
      by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho]).
    pose proof (airest_f_frame _ _ _ _ _ _ _ _ _ REST MU4 WM4 ltac:(lia) ltac:(lia) ltac:(lia)) as REST4.
    unhide HD3. unhide FR3.
    transport HD3 m4 AGS ltac:(intros a Ha; rewrite Hhd in Ha; cbn [outside fst snd]; lia).
    transport FR3 m4 AGS ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
    hide HD3. hide FR3. hide HEB4.
    pose proof (munch_refl ([] : list (Z * Z)) m4) as MU. pose proof (wmono_refl asegs m4) as WM.
    zstep.
    unhide HD3. unhide FR3. unhide HEB4.
    eapply (ai_exit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 RNG3 st3 false c' p' msg hd);
      [exact FP3 | exact MI4 | exact ST4 | | exact HD3 | exact Hhd | exact FR3 |].
    { eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_weaken; [exact AGS|]. intros a [[Ha|[Ha|[Ha|Ha]]] (_ & _ & Hn & _)]; cbn [outside fst snd].
      - lia.
      - pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G ltac:(apply in_block_app; left; apply in_block_app in Ha as [X|X]; apply in_block_app; [left; exact X| right; apply in_block_app; right; exact X])) as AB. lia.
      - pose proof (gia_in_frames_below _ _ _ GL _ _ _ _ _ _ _ a G Ha) as AB. lia.
      - pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G Ha) as SBD. lia. }
    apply (airest_f_done _ _ _ _ _ _ REST4).
    - exists junk4. pose proof (snprintf_length_le 256 fs args ltac:(lia)) as LS. rewrite EMSG in LS, HEB4.
      change (Z.to_nat 256) with 256%nat in HEB4. replace (256 - length msg - 1)%nat with (255 - length msg)%nat in HEB4 by lia. exact HEB4.
    - pose proof (snprintf_length_le 256 fs args ltac:(lia)) as LS. rewrite EMSG in LS. lia.
    - rewrite <- EMSG. apply snprintf_ok; [exact FIT| exact AOK].
  Qed.
  End Sz6.
  #[using="FO fflagA GL SNPRINTF I i G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO"] Lemma ai_snp : ltac:(let t := eval cbv delta [ai_snp__stmt] in ai_snp__stmt in exact t).
  Proof. intros ra' t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 a3v a4v m3 RNG3 st3 fs args FMTA msg c' p' hd. ltac2:(SecDiet.SzSec.closeP 'ai_snp__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ai_snp_b__stmt : Prop := forall (ra' t0' t1' t2' a0' a1' a5' a6' a7' t3' t4' t5' t6' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 a3v a4v : word)
      (m3 : mem) (RNG3 : footprint) (st3 : PS) (fs : string) (args : list farg) (FMTA : Z) (msg : list Z) (c' : cursor) (p' : pcapT) (h0 h2 : cell),
    fp_le RNG RNG3 -> mem_inv asegs m3 -> stk asegs m3 lo (bv_unsigned sp + -128) -> AGP m3 ->
    rw_cells asegs m3 (bv_unsigned sp + -128) [h0; C8 (Z_to_bv 64 EB); h2] -> csize h0 = 8%nat -> csize h2 = 8%nat -> FRAME m3 ->
    rw_cells asegs m3 EB [CB 256 ej] ->
    fmt_at m3 FMTA fs -> fmt_ok fs args = true -> (length args <= 3)%nat ->
    (forall (CL : list cblk) D dn, Forall2 (farg_word true L RNG3 FL CL (bv_unsigned sp + -128) D dn m3) args (firstn (length args) [a3v; a4v; a5'])) ->
    Fmt.snprintf 256 fs args = msg -> items_okb (fmt fs) = true -> Forall arg_ok args ->
    AIREST_F RNG3 FL C1 C2 FB P B CUR p s (ps_outfile st) m3 st3 c' p' ->
    evtF asegs RNG3 (POSTQ (false, c', p', msg) st3 RNG3)
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' y0 y1 a0' a1' (Z_to_bv 64 FMTA) a3v a4v a5' a6' a7'
               y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 t3' t4' t5' t6') F (Z_to_bv 64 0x8c960) fc None m3 (seg_rom asegs)).
  Section Sz7.
  Variables ra' t0' t1' t2' a0' a1' a5' a6' a7' t3' t4' t5' t6' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 a3v a4v m3 RNG3 st3 fs args FMTA msg c' p' h0 h2 : ltac2:(SecDiet.SzSec.tyM 'ai_snp_b__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  #[using="FO fflagA GL SNPRINTF I i G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO"] Lemma ai_snp_b__body : ltac2:(SecDiet.SzSec.bodyP 'ai_snp_b__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros FP3 MI3 ST3 AG3 HD3 Hh0 Hh2 FR3 HEB3 FAT FOK ALEN FW EMSG FIT AOK REST.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (RSPW : rng RNG3 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact (rng_fp_le _ _ _ _ FP3 RSTK)| lia]).
    destruct (rw_cells_cut _ _ _ 1 HD3) as [_ HDJ]. cbn [firstn skipn cells_size Nat.add] in HDJ. rewrite Hh0 in HDJ.
    destruct (rw_cells_cut _ _ _ 1 HDJ) as [HD8 _]. clear HDJ. cbn [firstn skipn] in HD8.
    replace (bv_unsigned sp + -128 + Z.of_nat (8 + 0))%Z with (bv_unsigned sp + -120)%Z in HD8 by lia.
    hide FR3. hide HEB3. hide HD3.
    pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    zstep. zstep. unhide FR3. unhide HEB3. unhide HD3. clear HD8 MU WM.
    eapply ai_snp with (hd := [h0; C8 (Z_to_bv 64 EB); h2]); try eassumption.
    cbn [cells_size csize Nat.add]. rewrite Hh0, Hh2. reflexivity.
  Qed.
  End Sz7.
  #[using="FO fflagA GL SNPRINTF I i G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO"] Lemma ai_snp_b : ltac:(let t := eval cbv delta [ai_snp_b__stmt] in ai_snp_b__stmt in exact t).
  Proof. intros ra' t0' t1' t2' a0' a1' a5' a6' a7' t3' t4' t5' t6' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 a3v a4v m3 RNG3 st3 fs args FMTA msg c' p' h0 h2. ltac2:(SecDiet.SzSec.closeP 'ai_snp_b__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ai_mcp__stmt : Prop := forall (ra' t0' t1' t2' a0' a3' a4' a5' a6' a7' t3' t4' t5' t6' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 : word)
      (m3 : mem) (RNG3 : footprint) (st3 : PS) (SRC n : Z) (str : string) (msg : list Z) (c' : cursor) (p' : pcapT) (h0 h2 : cell),
    fp_le RNG RNG3 -> mem_inv asegs m3 -> stk asegs m3 lo (bv_unsigned sp + -128) -> AGP m3 ->
    rw_cells asegs m3 (bv_unsigned sp + -128) [h0; C8 (Z_to_bv 64 EB); h2] -> csize h0 = 8%nat -> csize h2 = 8%nat -> FRAME m3 ->
    rw_cells asegs m3 EB [CB 256 ej] ->
    fmt_at m3 SRC str -> (Z.of_nat (String.length str) + 1 = n)%Z -> (n <= 256)%Z ->
    map b8 msg = map (fun ch => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii ch))) (String.list_ascii_of_string str) ->
    Forall (fun z => 0 < z < 256)%Z msg ->
    AIREST_F RNG3 FL C1 C2 FB P B CUR p s (ps_outfile st) m3 st3 c' p' ->
    evtF asegs RNG3 (POSTQ (false, c', p', msg) st3 RNG3)
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' y0 y1 a0' (Z_to_bv 64 SRC) (Z_to_bv 64 n) a3' a4' a5' a6' a7'
               y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 t3' t4' t5' t6') F (Z_to_bv 64 0x8c940) fc None m3 (seg_rom asegs)).
  Section Sz8.
  Variables ra' t0' t1' t2' a0' a3' a4' a5' a6' a7' t3' t4' t5' t6' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 m3 RNG3 st3 SRC n str msg c' p' h0 h2 : ltac2:(SecDiet.SzSec.tyM 'ai_mcp__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  #[using="rc tlsI FO fflagA GL I i G LO BU SPT RSTK RIMG RISH GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO"] Lemma ai_mcp__body : ltac2:(SecDiet.SzSec.bodyP 'ai_mcp__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros FP3 MI3 ST3 AG3 HD3 Hh0 Hh2 FR3 HEB3 (SRCB & SRCLO & SRCHI & SRCG) LN NB EMSG MOK REST.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof atop_range as AR.
    pose proof (rng_fp_le _ _ _ _ FP3 RSTK) as RSTK3. pose proof (rng_fp_le _ _ _ _ FP3 RIMG) as RIMG3. pose proof (rng_fp_le _ _ _ _ FP3 RISH) as RISH3.
    assert (RSPW : rng RNG3 lo (bv_unsigned sp + -128 - lo)) by (eapply rng_sub'; [exact RSTK3| lia]).
    assert (RSPX : rng RNG3 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK3| lia]).
    pose proof REST as REST'. destruct REST' as (s' & i' & I' & pad' & bs' & _ & _ & G3 & _).
    pose proof (ai_eb_cobj _ _ _ _ G3 ltac:(apply incl_appr, incl_refl) AG3) as OEB.
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G3 (proj1 OEB)) as (EBLO & EBHI).
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G3) as (RT3 & _).
    rewrite LN in SRCG. assert (SRCHI2 : (SRC + n <= 0x32000)%Z) by lia.
    pose proof (gia_global_mobjA _ _ _ GL _ _ _ _ _ _ _ _ _ G3 SRCG RIMG3 RISH3) as OSRC.
    assert (LM : length msg = String.length str).
    { apply (f_equal (@length _)) in EMSG. rewrite !length_map, length_list_ascii in EMSG. exact EMSG. }
    pose proof (rw_cells_split_CB _ _ _ [] _ _ [] [Z.to_nat n; (256 - Z.to_nat n)%nat] HEB3 ltac:(cbn; lia)) as HE'. clear HEB3. cbn [mk_CB_cells app] in HE'.
    destruct (rw_cells_cut _ _ _ 1 HE') as [HE1 HE2]. clear HE'. cbn [firstn skipn cells_size csize Nat.add] in HE1, HE2.
    lazymatch type of HE2 with rw_cells _ _ ?A _ => replace A with (EB + n)%Z in HE2 by lia end.
    unfold ai_FRAME in FR3.
    destruct (rw_cells_cut _ _ _ 1 HD3) as [_ HDJ]. cbn [firstn skipn cells_size Nat.add] in HDJ. rewrite Hh0 in HDJ.
    destruct (rw_cells_cut _ _ _ 1 HDJ) as [HD8 _]. clear HDJ. cbn [firstn skipn] in HD8.
    replace (bv_unsigned sp + -128 + Z.of_nat (8 + 0))%Z with (bv_unsigned sp + -120)%Z in HD8 by lia.
    hide HD3. hide FR3. hide HE2.
    pose proof (munch_refl [(bv_unsigned sp + -128 - 2224, bv_unsigned sp + -128); (EB, EB + n)]%Z m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    zstep. zstep.
    name_sp sp (-128)%Z.
    eapply evtF_cut.
    { eapply (asan_memcpy_specZ RNG3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 lo EB SRC n _ (firstn (Z.to_nat n) ej));
        [ reflexivity | reflexivity | reflexivity | exact MI3 | rewrite Hsp; exact ST3 | rewrite Hsp; lia | lia | exact RT3 | exact SRCB
        | rewrite length_app, length_map, length_list_ascii; cbn [length]; lia | lia | exact HE1
        | left; lia | exact OSRC
        | eapply mobjA_sub; [apply aobjA_mobjA; [exact (proj2 OEB) | lia] | lia | lia | lia]
        | lia | lia | exact RIMG3 | rewrite Hsp; exact RSPW ]. }
    cbv beta. intros ms' PO. destruct PO as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & m4 & -> & MU4 & WM4 & MI4 & ST4 & HE1' & _). clear HE1.
    rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 575816)) with (Z_to_bv 64 575816) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -128 - 2224, bv_unsigned sp + -128); (EB, EB + n)]%Z a) m3 m4) by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho]).
    pose proof (airest_f_frame _ _ _ _ _ _ _ _ _ REST MU4 WM4 ltac:(lia) ltac:(lia) ltac:(lia)) as REST4.
    unhide HD3. unhide FR3. unhide HE2.
    transport HD3 m4 AGS ltac:(intros a Ha; cbn [cells_size Nat.add] in Ha; rewrite Hh0, Hh2 in Ha; cbn [csize Nat.add outside fst snd] in Ha |- *; lia).
    transport FR3 m4 AGS ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
    transport HE2 m4 AGS ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
    clear MU WM HD8. pose proof (munch_refl ([] : list (Z * Z)) m4) as MU. pose proof (wmono_refl asegs m4) as WM.
    hide HD3. hide FR3. hide HE2. hide HE1'.
    do 2 zstep.
    unhide HD3. unhide FR3. unhide HE2. unhide HE1'.
    eapply (ai_exit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 RNG3 st3 false c' p' msg [h0; C8 (Z_to_bv 64 EB); h2]);
      [exact FP3 | exact MI4 | exact ST4 | | exact HD3 | cbn [cells_size csize Nat.add]; rewrite Hh0, Hh2; reflexivity | exact FR3 |].
    { eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_weaken; [exact AGS|]. intros a [[Ha|[Ha|[Ha|Ha]]] (_ & _ & Hn & _)]; cbn [outside fst snd].
      - lia.
      - pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G ltac:(apply in_block_app; left; apply in_block_app in Ha as [X|X]; apply in_block_app; [left; exact X| right; apply in_block_app; right; exact X])) as AB. lia.
      - pose proof (gia_in_frames_below _ _ _ GL _ _ _ _ _ _ _ a G Ha) as AB. lia.
      - pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G Ha) as SBD. lia. }
    apply (airest_f_done _ _ _ _ _ _ REST4).
    - lazymatch type of HE2 with rw_cells _ _ _ [CB _ ?j] => exists j end.
      pose proof (rw_cells_uncut _ _ _ _ _ HE1' HE2 ltac:(cbn [cells_size csize Nat.add]; lia)) as HEJ. cbn [app] in HEJ.
      eapply rw_cells_recell; [exact HEJ | pose proof (proj1 (proj1 HEJ)) as WF; cbn in WF |- *; rewrite ?length_app, ?length_map, ?length_list_ascii in *; cbn [length] in *; repeat split; try lia; tauto |].
      cbn [cells_bytes cbytes app]. rewrite EMSG. reflexivity.
    - rewrite LM. lia.
    - exact MOK.
  Qed.
  End Sz8.
  #[using="rc tlsI FO fflagA GL I i G LO BU SPT RSTK RIMG RISH GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO"] Lemma ai_mcp : ltac:(let t := eval cbv delta [ai_mcp__stmt] in ai_mcp__stmt in exact t).
  Proof. intros ra' t0' t1' t2' a0' a3' a4' a5' a6' a7' t3' t4' t5' t6' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 m3 RNG3 st3 SRC n str msg c' p' h0 h2. ltac2:(SecDiet.SzSec.closeP 'ai_mcp__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End AIA.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require AiAuxB.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.AiAuxB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_hlenA__A3P.F_aiDA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
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
(* [comment removed for export] *)
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.


Ltac apA lem := eapply lem; try eassumption.
Ltac transport H m' AG tac :=
  lazymatch type of H with rw_cells ?sg _ ?A ?cs =>
    let X := fresh in
    assert (X : rw_cells sg m' A cs) by (eapply agrees_rw_cells; [exact AG | exact H | tac]);
    clear H; rename X into H end.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section AIA.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  #[local] Abbreviation pcapT := (PcapTypes.pcap hptr hptr).
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (L : alayout) (RNG : footprint) (st : PS) (C1 C2 FB : list cblk) (FL : list fblock) (P B I CUR EB lo idb_off : Z).
  Variables (p : pcapT) (s : pcap_ng_sf) (i : option hptr) (c : cursor) (bs ej pad cpad : list byte).
  Hypothesis G : GIOA L RNG st (C1 ++ IBLK i I s ++ C2) FB FL m.
  Hypothesis LO : (ATOP + 4096 <= lo)%Z.
  Hypothesis BU : (lo + 16528 <= bv_unsigned sp)%Z.
  Hypothesis SPT : (bv_unsigned sp + 16 < al_top L /\ al_top L <= 2^47)%Z.
  Hypothesis RSTK : rng RNG lo (al_top L - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.
  Hypothesis RTLS : rng_atls RNG.
  Hypothesis TPE : tp = Z_to_bv 64 ATP.
  Hypothesis ALN : (bv_unsigned sp mod 16 = 0)%Z.

  #[local] Abbreviation POSTQ := (add_interface_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL C1 C2 FB lo P B CUR EB p s c bs ej m (ps_outfile st)).
  #[local] Abbreviation AGP := (ai_AGP FL sp C1 C2 P B CUR EB p m).
  #[local] Abbreviation FRAME := (ai_FRAME ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).

  (* [comment removed for export] *)
  Definition ai_exit__stmt : Prop := forall (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 : word)
      (m3 : mem) (RNG3 : footprint) (st3 : PS) (ok : bool) (c' : cursor) (p' : pcapT) (msg : list Z) (hd : list cell),
    fp_le RNG RNG3 ->
    mem_inv asegs m3 -> stk asegs m3 lo (bv_unsigned sp + -144) -> AGP m3 ->
    rw_cells asegs m3 (bv_unsigned sp + -144) hd -> cells_size hd = 40%nat -> FRAME m3 ->
    ai_REST GIOA L RNG3 FL C1 C2 FB P B CUR EB p s c ej (ps_outfile st) m3 st3 (ok, c', p', msg) ->
    evtF asegs RNG3 (POSTQ (ok, c', p', msg) st3 RNG3)
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1' t2' y0 y1 (Z_to_bv 64 (Z.b2z ok)) a1' a2' a3' a4' a5' a6' a7'
               y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 t3' t4' t5' t6') F (Z_to_bv 64 0x8caf4) fc None m3 (seg_rom asegs)).
  Section Sz1.
  Variables ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 m3 RNG3 st3 ok c' p' msg hd : ltac2:(SecDiet.SzSec.tyM 'ai_exit__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  #[using="rc BU SPT RSTK"] Lemma ai_exit__body : ltac2:(SecDiet.SzSec.bodyP 'ai_exit__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros FP3 MI3 ST3 AG3 HD3 Hhd FR3 REST.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (RSPW : rng RNG3 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact (rng_fp_le _ _ _ _ FP3 RSTK)| lia]).
    pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    destruct (rw_cells_forget _ _ _ _ HD3) as [hj HD3']. clear HD3. rewrite Hhd in HD3'.
    unfold ai_FRAME in FR3.
    do 15 zstep.
    release_frame HD3' ST3 (bv_unsigned sp + -104)%Z. release_frame FR3 ST3 (bv_unsigned sp).
    apply evtF_done. unfold add_interface_post. split; [exact FP3|].
    destruct REST as (s' & i' & I' & pad' & bs' & OFr & E1 & G3 & NG3 & U1 & U2 & U3 & U4 & BUF3 & PFX3 & LEN3 & GR3 & RM).
    lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => exists (Z_to_bv 64 (Z.b2z ok)), mm, s', i', I', pad', bs' end.
    split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
    split; [exact OFr|]. split; [assumption|]. split; [assumption|]. split; [exact AG3|].
    split; [exact E1|]. split; [exact G3|]. split; [exact NG3|]. split; [exact U1|]. split; [exact U2|]. split; [exact U3|]. split; [exact U4|].
    split; [exact BUF3|]. split; [exact PFX3|]. split; [exact LEN3|]. split; [exact GR3|]. split; [reflexivity|]. exact RM.
  Qed.
  End Sz1.
  #[using="rc BU SPT RSTK"] Lemma ai_exit : ltac:(let t := eval cbv delta [ai_exit__stmt] in ai_exit__stmt in exact t).
  Proof. intros ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 m3 RNG3 st3 ok c' p' msg hd. ltac2:(SecDiet.SzSec.closeP 'ai_exit__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis HinP : In (pc_self p, P, PCAP_NG_SF_TOTAL) (C1 ++ C2).
  Hypothesis HinB : In (pc_buffer p, B, pc_bufalloc p) (C1 ++ C2).
  Hypothesis P14 : (0 < P /\ P + 680 <= ATOP)%Z.
  Hypothesis B14 : (0 < B /\ B + pc_bufalloc p <= ATOP)%Z.
  Hypothesis LENB : (Z.of_nat (length (pc_bufdata p)) <= pc_bufalloc p < 2^32)%Z.
  Hypothesis CURS : (bv_unsigned sp <= CUR /\ CUR + 24 <= al_top L)%Z.
  (* [comment removed for export] *)
  Hypothesis EBL : clocA FL (C1 ++ C2) EB 256.
  Hypothesis EBP : (EB + 256 <= P + 648 \/ P + 680 <= EB)%Z.
  Hypothesis EBB : (EB + 256 <= B \/ B + pc_bufalloc p <= EB)%Z.

  #[local] Abbreviation AIREST_F := (ai_REST_F GIOA L).

  (* [comment removed for export] *)
  Definition airest_f_frame__stmt : Prop := forall (m3 m4 : mem) (RNG3 : footprint) (st' : PS) (c' : cursor) (p' : pcapT) (lo1 hi1 k : Z),
    AIREST_F RNG3 FL C1 C2 FB P B CUR p s (ps_outfile st) m3 st' c' p' -> munch [(lo1, hi1); (EB, EB + k)]%Z m3 m4 -> wmono asegs m3 m4 ->
    (ATOP + 4096 <= lo1)%Z -> (hi1 <= bv_unsigned sp + -144)%Z -> (0 <= k <= 256)%Z ->
    AIREST_F RNG3 FL C1 C2 FB P B CUR p s (ps_outfile st) m4 st' c' p'.
  Section Sz2.
  Variables m3 m4 RNG3 st' c' p' lo1 hi1 k : ltac2:(SecDiet.SzSec.tyM 'airest_f_frame__stmt "vvvvvvvvv" @m3).
  #[using="tlsI FO fflagA GL lo LO BU GPL P14 B14 LENB CURS EBL EBP EBB"] Lemma airest_f_frame__body : ltac2:(SecDiet.SzSec.bodyP 'airest_f_frame__stmt "vvvvvvvvv").
  Proof.
    intros (s' & i' & I' & pad' & bs' & OFr & E1 & G3 & NG3 & U1 & U2 & U3 & U4 & BUF3 & PFX3 & LEN3 & GR3 & IC3 & (ccs' & CC3 & Hccs')) MU WM L1 H1 HK.
    pose proof atop_range as AR.
    assert (AGS : agrees_on (fun a => outside [(lo1, hi1); (EB, EB + k)]%Z a) m3 m4) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
    assert (EBL3 : clocA FL (IBLK i' I' s' ++ C1 ++ C2) EB 256) by (eapply clocA_incl; [exact EBL | apply incl_appr, incl_refl | apply incl_refl]).
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G3 EBL3) as (EBLO & EBHI).
    exists s', i', I', pad', bs'. split; [exact OFr|]. split; [exact E1|].
    split.
    { eapply (gl_client_frame _ _ _ GL); [exact G3 | exact MU | exact WM |].
      apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [| apply Forall_nil].
      apply (clocA_iv FL (IBLK i' I' s' ++ C1 ++ C2) EB k). eapply AiAuxB.clocA_sub; [exact EBL3 | lia | lia]. }
    unfold PCAP_PRIV_OFF in *.
    split; [transport NG3 m4 AGS ltac:(intros a Ha; unfold ng_cells in Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia); exact NG3|].
    split; [exact U1|]. split; [exact U2|]. split; [exact U3|]. split; [exact U4|].
    split; [transport BUF3 m4 AGS ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia); exact BUF3|].
    split; [exact PFX3|]. split; [exact LEN3|]. split; [exact GR3|].
    split.
    { destruct i' as [q|]; [| exact IC3]. destruct IC3 as [(junk & IB3) SZ]. split; [| exact SZ]. exists junk.
      assert (G3p : GIOA L RNG3 st' ((C1 ++ C2) ++ IBLK (Some q) I' s') FB FL m3) by (eapply GPL; [exact G3| apply Permutation.Permutation_app_comm]).
      destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G3p EBL (or_introl eq_refl : In (q, I', (40 * ng_ifaces_size s')%Z) (IBLK (Some q) I' s')) ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kI & kIr & kI1 & kI2).
      cbn [cb_addr cb_size fst snd] in kI1, kI2.
      assert (HinI : In (q, I', (40 * ng_ifaces_size s')%Z) ((IBLK (Some q) I' s' ++ C1 ++ C2) ++ FB)) by (apply in_or_app; left; left; reflexivity).
      pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G3 HinI) as ((IBAND & I3 & ITOP & I2) & I1 & _). cbn [cb_addr cb_size fst snd] in *.
      transport IB3 m4 AGS ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia). exact IB3. }
    exists ccs'. split; [| exact Hccs'].
    transport CC3 m4 AGS ltac:(intros a Ha; rewrite Hccs' in Ha; cbn [outside fst snd]; lia). exact CC3.
  Qed.
  End Sz2.
  #[using="tlsI FO fflagA GL lo LO BU GPL P14 B14 LENB CURS EBL EBP EBB"] Lemma airest_f_frame : ltac:(let t := eval cbv delta [airest_f_frame__stmt] in airest_f_frame__stmt in exact t).
  Proof. intros m3 m4 RNG3 st' c' p' lo1 hi1 k. ltac2:(SecDiet.SzSec.closeP 'airest_f_frame__body "vvvvvvvvv"). Qed.

  #[using="Type"] Lemma airest_f_done : forall (m' : mem) (RNG3 : footprint) (st' : PS) (c' : cursor) (p' : pcapT) (msg : list Z),
    AIREST_F RNG3 FL C1 C2 FB P B CUR p s (ps_outfile st) m' st' c' p' ->
    (exists junk'', rw_cells asegs m' EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk'']) ->
    (Z.of_nat (length msg) < 256)%Z -> Forall (fun z => 0 < z < 256)%Z msg ->
    ai_REST GIOA L RNG3 FL C1 C2 FB P B CUR EB p s c ej (ps_outfile st) m' st' (false, c', p', msg).
  Proof.
    intros m' RNG3 st' c' p' msg (s' & i' & I' & pad' & bs' & OFr & E1 & G3 & NG3 & U1 & U2 & U3 & U4 & BUF3 & PFX3 & LEN3 & GR3 & IC3 & CC3) HE HL HOK.
    exists s', i', I', pad', bs'. split; [exact OFr|]. split; [exact E1|]. split; [exact G3|]. split; [exact NG3|]. split; [exact U1|]. split; [exact U2|]. split; [exact U3|]. split; [exact U4|].
    split; [exact BUF3|]. split; [exact PFX3|]. split; [exact LEN3|]. split; [exact GR3|]. cbv iota. split; [exact IC3|]. split; [exact CC3|]. split; [exact HE|]. split; [exact HL| exact HOK].
  Qed.

  (* [comment removed for export] *)
  Hypothesis EBO : cobjA RNG m FL (C1 ++ C2) EB 256 \/ (P + 216 = EB)%Z.

  (* [comment removed for export] *)
  Definition ai_ksh__stmt : Prop := forall (m3 : mem), AGP m3 -> agrees_on (in_frame_sh FL) m m3.
  Section Sz4.
  Variables m3 : ltac2:(SecDiet.SzSec.tyM 'ai_ksh__stmt "v" @m3).
  #[using="rc tlsI H FO GIOA fflagA GL L RNG st FB I lo s i G LO BU HinP HinB CURS EBL"] Lemma ai_ksh__body : ltac2:(SecDiet.SzSec.bodyP 'ai_ksh__stmt "v").
  Proof.
    intros AG.
 pose proof atop_range as AR.
    assert (HinP' : In (pc_self p, P, PCAP_NG_SF_TOTAL) ((C1 ++ IBLK i I s ++ C2) ++ FB)).
    { apply in_or_app. left. apply in_app_iff in HinP as [X|X]; apply in_or_app; [left; exact X| right; apply in_or_app; right; exact X]. }
    assert (HinB' : In (pc_buffer p, B, pc_bufalloc p) ((C1 ++ IBLK i I s ++ C2) ++ FB)).
    { apply in_or_app. left. apply in_app_iff in HinB as [X|X]; apply in_or_app; [left; exact X| right; apply in_or_app; right; exact X]. }
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinP') as ((PBAND & _) & _). pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G HinB') as ((BBAND & _) & _).
    cbn [cb_addr cb_size fst snd] in PBAND, BBAND.
    assert (EBL0 : clocA FL (C1 ++ IBLK i I s ++ C2) EB 256).
    { eapply clocA_incl; [exact EBL | | apply incl_refl]. intros x Hx. apply in_app_iff in Hx as [X|X]; apply in_or_app; [left; exact X| right; apply in_or_app; right; exact X]. }
    pose proof (clocA_ablk _ _ _ GL _ _ _ _ _ _ _ _ _ G EBL0 ltac:(lia)) as EBAND.
    eapply agrees_on_weaken; [exact AG|]. intros a Ha.
    pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G Ha) as BD.
    split; [right; right; right; exact Ha|].
    pose proof (ablk_clear_band _ _ a PBAND ltac:(unfold KLS; lia)) as NP. pose proof (ablk_clear_band _ _ a BBAND ltac:(unfold KLS; lia)) as NB.
    pose proof (ablk_clear_band _ _ a EBAND ltac:(unfold KLS; lia)) as NE.
    unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL in *. lia.
  Qed.
  End Sz4.
  #[using="rc tlsI H FO GIOA fflagA GL L RNG st FB I lo s i G LO BU HinP HinB CURS EBL"] Lemma ai_ksh : ltac:(let t := eval cbv delta [ai_ksh__stmt] in ai_ksh__stmt in exact t).
  Proof. intros m3. ltac2:(SecDiet.SzSec.closeP 'ai_ksh__body "v"). Qed.

  Definition ai_eb_cobj__stmt : Prop := forall (RNG3 : footprint) (st3 : PS) (CL3 : list cblk) (m3 : mem),
    GIOA L RNG3 st3 CL3 FB FL m3 -> incl (C1 ++ C2) CL3 -> AGP m3 -> cobjA RNG3 m3 FL CL3 EB 256.
  Section Sz5.
  Variables RNG3 st3 CL3 m3 : ltac2:(SecDiet.SzSec.tyM 'ai_eb_cobj__stmt "vvvv" @RNG3).
  #[using="tlsI FO fflagA GL RNG st I lo s i G LO BU HinP HinB CURS EBL EBP EBB EBO"] Lemma ai_eb_cobj__body : ltac2:(SecDiet.SzSec.bodyP 'ai_eb_cobj__stmt "vvvv").
  Proof.
    intros G3 INC AG.
    destruct EBO as [O| <-].
    - pose proof (cobjA_keep _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ _ O G3 INC (incl_refl _) (ai_ksh _ AG) ltac:(lia)) as [LOC AO].
      split; [eapply clocA_incl; [exact LOC | exact INC | apply incl_refl]| exact AO].
    - assert (HinP3 : In (pc_self p, P, PCAP_NG_SF_TOTAL) (CL3 ++ FB)) by (apply in_or_app; left; apply INC; exact HinP).
      pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G3 HinP3) as PBLK.
      split; [left; exists (pc_self p, P, PCAP_NG_SF_TOTAL); split; [apply INC; exact HinP| cbn [cb_addr cb_size fst snd]; unfold PCAP_NG_SF_TOTAL; lia]|].
      eapply blockA_aobj; [exact PBLK | cbn [cb_addr cb_size fst snd]; lia | cbn [cb_addr cb_size fst snd]; unfold PCAP_NG_SF_TOTAL; lia | lia].
  Qed.
  End Sz5.
  #[using="tlsI FO fflagA GL RNG st I lo s i G LO BU HinP HinB CURS EBL EBP EBB EBO"] Lemma ai_eb_cobj : ltac:(let t := eval cbv delta [ai_eb_cobj__stmt] in ai_eb_cobj__stmt in exact t).
  Proof. intros RNG3 st3 CL3 m3. ltac2:(SecDiet.SzSec.closeP 'ai_eb_cobj__body "vvvv"). Qed.

  (* [comment removed for export] *)
  Definition ai_snp__stmt : Prop := forall (ra' t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 a3v a4v : word)
      (m3 : mem) (RNG3 : footprint) (st3 : PS) (fs : string) (args : list farg) (FMTA : Z) (msg : list Z) (c' : cursor) (p' : pcapT) (hd : list cell),
    fp_le RNG RNG3 -> mem_inv asegs m3 -> stk asegs m3 lo (bv_unsigned sp + -144) -> AGP m3 ->
    rw_cells asegs m3 (bv_unsigned sp + -144) hd -> cells_size hd = 40%nat -> FRAME m3 ->
    rw_cells asegs m3 EB [CB 256 ej] ->
    fmt_at m3 FMTA fs -> fmt_ok fs args = true -> (length args <= 3)%nat ->
    (forall (CL : list cblk) D dn, Forall2 (farg_word true L RNG3 FL CL (bv_unsigned sp + -144) D dn m3) args (firstn (length args) [a3v; a4v; a5'])) ->
    Fmt.snprintf 256 fs args = msg -> items_okb (fmt fs) = true -> Forall arg_ok args ->
    AIREST_F RNG3 FL C1 C2 FB P B CUR p s (ps_outfile st) m3 st3 c' p' ->
    evtF asegs RNG3 (POSTQ (false, c', p', msg) st3 RNG3)
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1' t2' y0 y1 (Z_to_bv 64 EB) (Z_to_bv 64 256) (Z_to_bv 64 FMTA) a3v a4v a5' a6' a7'
               y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 t3' t4' t5' t6') F (Z_to_bv 64 0x8caec) fc None m3 (seg_rom asegs)).
  Section Sz6.
  Variables ra' t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 a3v a4v m3 RNG3 st3 fs args FMTA msg c' p' hd : ltac2:(SecDiet.SzSec.tyM 'ai_snp__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  #[using="FO fflagA GL SNPRINTF I i G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO"] Lemma ai_snp__body : ltac2:(SecDiet.SzSec.bodyP 'ai_snp__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros FP3 MI3 ST3 AG3 HD3 Hhd FR3 HEB3 FAT FOK ALEN FW EMSG FIT AOK REST.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof atop_range as AR.
    pose proof REST as REST'. destruct REST' as (s' & i' & I' & pad' & bs' & _ & _ & G3 & _).
    pose proof (ai_eb_cobj _ _ _ _ G3 ltac:(apply incl_appr, incl_refl) AG3) as OEB.
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G3 (proj1 OEB)) as (EBLO & EBHI).
    pose proof (rng_fp_le _ _ _ _ FP3 RSTK) as RSTK3. pose proof (rng_fp_le _ _ _ _ FP3 RIMG) as RIMG3.
    pose proof (rng_fp_le _ _ _ _ FP3 RISH) as RISH3. pose proof (rng_fp_le _ _ _ _ FP3 RTLS) as RTLS3.
    unfold ai_FRAME in FR3.
    hide HD3. hide FR3. hide HEB3.
    pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    zstep. unhide HEB3. clear MU WM.
    name_sp sp (-144)%Z.
    eapply evtF_cut.
    { eapply SNPRINTF with (L := L) (s := st3) (CL := IBLK i' I' s' ++ C1 ++ C2) (FB := FB) (FL := FL) (lo := lo) (DST := EB) (n := 256%Z) (FMTA := FMTA) (fs := fs) (args := args) (junk := ej);
        [ split; [exact G3|]; split; [rewrite Hsp; exact ST3|]; split; [lia|]; split; [unfold STDIO_STACK; rewrite Hsp; lia|];
          split; [rewrite Hsp; lia|]; split; [exact MI3|]; split; [exact TPE|]; split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|];
          split; [exact RSTK3|]; split; [exact RIMG3|]; split; [exact RISH3| exact RTLS3]
        | reflexivity | reflexivity | reflexivity | lia | exact FAT | exact FOK | exact ALEN | rewrite Hsp; apply FW | exact HEB3 | exact OEB ]. }
    cbv beta. intros ms' PO. destruct PO as (av4 & m4 & junk4 & E & MU4 & WM4 & MI4 & ST4 & -> & HEB4).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 576240)) with (Z_to_bv 64 576240) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    unfold STDIO_STACK in MU4.
    assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -144 - 16384, bv_unsigned sp + -144); (EB, EB + 256)]%Z a) m3 m4)
      by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho]).
    pose proof (airest_f_frame _ _ _ _ _ _ _ _ _ REST MU4 WM4 ltac:(lia) ltac:(lia) ltac:(lia)) as REST4.
    unhide HD3. unhide FR3.
    transport HD3 m4 AGS ltac:(intros a Ha; rewrite Hhd in Ha; cbn [outside fst snd]; lia).
    transport FR3 m4 AGS ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
    hide HD3. hide FR3. hide HEB4.
    pose proof (munch_refl ([] : list (Z * Z)) m4) as MU. pose proof (wmono_refl asegs m4) as WM.
    zstep.
    unhide HD3. unhide FR3. unhide HEB4.
    eapply (ai_exit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 RNG3 st3 false c' p' msg hd);
      [exact FP3 | exact MI4 | exact ST4 | | exact HD3 | exact Hhd | exact FR3 |].
    { eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_weaken; [exact AGS|]. intros a [[Ha|[Ha|[Ha|Ha]]] (_ & _ & Hn & _)]; cbn [outside fst snd].
      - lia.
      - pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G ltac:(apply in_block_app; left; apply in_block_app in Ha as [X|X]; apply in_block_app; [left; exact X| right; apply in_block_app; right; exact X])) as AB. lia.
      - pose proof (gia_in_frames_below _ _ _ GL _ _ _ _ _ _ _ a G Ha) as AB. lia.
      - pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G Ha) as SBD. lia. }
    apply (airest_f_done _ _ _ _ _ _ REST4).
    - exists junk4. pose proof (snprintf_length_le 256 fs args ltac:(lia)) as LS. rewrite EMSG in LS, HEB4.
      change (Z.to_nat 256) with 256%nat in HEB4. replace (256 - length msg - 1)%nat with (255 - length msg)%nat in HEB4 by lia. exact HEB4.
    - pose proof (snprintf_length_le 256 fs args ltac:(lia)) as LS. rewrite EMSG in LS. lia.
    - rewrite <- EMSG. apply snprintf_ok; [exact FIT| exact AOK].
  Qed.
  End Sz6.
  #[using="FO fflagA GL SNPRINTF I i G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO"] Lemma ai_snp : ltac:(let t := eval cbv delta [ai_snp__stmt] in ai_snp__stmt in exact t).
  Proof. intros ra' t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 a3v a4v m3 RNG3 st3 fs args FMTA msg c' p' hd. ltac2:(SecDiet.SzSec.closeP 'ai_snp__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ai_snp_b__stmt : Prop := forall (ra' t0' t1' t2' a0' a1' a5' a6' a7' t3' t4' t5' t6' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 a3v a4v : word)
      (m3 : mem) (RNG3 : footprint) (st3 : PS) (fs : string) (args : list farg) (FMTA : Z) (msg : list Z) (c' : cursor) (p' : pcapT) (hj h0 h2 h4 : cell),
    fp_le RNG RNG3 -> mem_inv asegs m3 -> stk asegs m3 lo (bv_unsigned sp + -144) -> AGP m3 ->
    rw_cells asegs m3 (bv_unsigned sp + -144) [hj; h0; C8 (Z_to_bv 64 EB); h2; h4] -> csize hj = 8%nat -> csize h0 = 8%nat -> csize h2 = 8%nat -> csize h4 = 8%nat -> FRAME m3 ->
    rw_cells asegs m3 EB [CB 256 ej] ->
    fmt_at m3 FMTA fs -> fmt_ok fs args = true -> (length args <= 3)%nat ->
    (forall (CL : list cblk) D dn, Forall2 (farg_word true L RNG3 FL CL (bv_unsigned sp + -144) D dn m3) args (firstn (length args) [a3v; a4v; a5'])) ->
    Fmt.snprintf 256 fs args = msg -> items_okb (fmt fs) = true -> Forall arg_ok args ->
    AIREST_F RNG3 FL C1 C2 FB P B CUR p s (ps_outfile st) m3 st3 c' p' ->
    evtF asegs RNG3 (POSTQ (false, c', p', msg) st3 RNG3)
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1' t2' y0 y1 a0' a1' (Z_to_bv 64 FMTA) a3v a4v a5' a6' a7'
               y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 t3' t4' t5' t6') F (Z_to_bv 64 0x8cae4) fc None m3 (seg_rom asegs)).
  Section Sz7.
  Variables ra' t0' t1' t2' a0' a1' a5' a6' a7' t3' t4' t5' t6' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 a3v a4v m3 RNG3 st3 fs args FMTA msg c' p' hj h0 h2 h4 : ltac2:(SecDiet.SzSec.tyM 'ai_snp_b__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  #[using="FO fflagA GL SNPRINTF I i G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO"] Lemma ai_snp_b__body : ltac2:(SecDiet.SzSec.bodyP 'ai_snp_b__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros FP3 MI3 ST3 AG3 HD3 Hhj Hh0 Hh2 Hh4 FR3 HEB3 FAT FOK ALEN FW EMSG FIT AOK REST.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (RSPW : rng RNG3 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact (rng_fp_le _ _ _ _ FP3 RSTK)| lia]).
    destruct (rw_cells_cut _ _ _ 2 HD3) as [_ HDJ]. cbn [firstn skipn cells_size Nat.add] in HDJ. rewrite Hhj, Hh0 in HDJ.
    destruct (rw_cells_cut _ _ _ 1 HDJ) as [HD8 _]. clear HDJ. cbn [firstn skipn] in HD8.
    replace (bv_unsigned sp + -144 + Z.of_nat (8 + (8 + 0)))%Z with (bv_unsigned sp + -128)%Z in HD8 by lia.   (* [comment removed for export] *)
    hide FR3. hide HEB3. hide HD3.
    pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    zstep. zstep. unhide FR3. unhide HEB3. unhide HD3. clear HD8 MU WM.
    eapply ai_snp with (hd := [hj; h0; C8 (Z_to_bv 64 EB); h2; h4]); try eassumption.
    cbn [cells_size csize Nat.add]. rewrite Hhj, Hh0, Hh2, Hh4. reflexivity.
  Qed.
  End Sz7.
  #[using="FO fflagA GL SNPRINTF I i G LO BU SPT RSTK RIMG RISH RTLS TPE ALN GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO"] Lemma ai_snp_b : ltac:(let t := eval cbv delta [ai_snp_b__stmt] in ai_snp_b__stmt in exact t).
  Proof. intros ra' t0' t1' t2' a0' a1' a5' a6' a7' t3' t4' t5' t6' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 a3v a4v m3 RNG3 st3 fs args FMTA msg c' p' hj h0 h2 h4. ltac2:(SecDiet.SzSec.closeP 'ai_snp_b__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ai_mcp__stmt : Prop := forall (ra' t0' t1' t2' a0' a3' a4' a5' a6' a7' t3' t4' t5' t6' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 : word)
      (m3 : mem) (RNG3 : footprint) (st3 : PS) (SRC n : Z) (str : string) (msg : list Z) (c' : cursor) (p' : pcapT) (hj h0 h2 h4 : cell),
    fp_le RNG RNG3 -> mem_inv asegs m3 -> stk asegs m3 lo (bv_unsigned sp + -144) -> AGP m3 ->
    rw_cells asegs m3 (bv_unsigned sp + -144) [hj; h0; C8 (Z_to_bv 64 EB); h2; h4] -> csize hj = 8%nat -> csize h0 = 8%nat -> csize h2 = 8%nat -> csize h4 = 8%nat -> FRAME m3 ->
    rw_cells asegs m3 EB [CB 256 ej] ->
    fmt_at m3 SRC str -> (Z.of_nat (String.length str) + 1 = n)%Z -> (n <= 256)%Z ->
    map b8 msg = map (fun ch => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii ch))) (String.list_ascii_of_string str) ->
    Forall (fun z => 0 < z < 256)%Z msg ->
    AIREST_F RNG3 FL C1 C2 FB P B CUR p s (ps_outfile st) m3 st3 c' p' ->
    evtF asegs RNG3 (POSTQ (false, c', p', msg) st3 RNG3)
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1' t2' y0 y1 a0' (Z_to_bv 64 SRC) (Z_to_bv 64 n) a3' a4' a5' a6' a7'
               y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 t3' t4' t5' t6') F (Z_to_bv 64 0x8cac4) fc None m3 (seg_rom asegs)).
  Section Sz8.
  Variables ra' t0' t1' t2' a0' a3' a4' a5' a6' a7' t3' t4' t5' t6' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 m3 RNG3 st3 SRC n str msg c' p' hj h0 h2 h4 : ltac2:(SecDiet.SzSec.tyM 'ai_mcp__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  #[using="rc tlsI FO fflagA GL I i G LO BU SPT RSTK RIMG RISH GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO"] Lemma ai_mcp__body : ltac2:(SecDiet.SzSec.bodyP 'ai_mcp__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros FP3 MI3 ST3 AG3 HD3 Hhj Hh0 Hh2 Hh4 FR3 HEB3 (SRCB & SRCLO & SRCHI & SRCG) LN NB EMSG MOK REST.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof atop_range as AR.
    pose proof (rng_fp_le _ _ _ _ FP3 RSTK) as RSTK3. pose proof (rng_fp_le _ _ _ _ FP3 RIMG) as RIMG3. pose proof (rng_fp_le _ _ _ _ FP3 RISH) as RISH3.
    assert (RSPW : rng RNG3 lo (bv_unsigned sp + -144 - lo)) by (eapply rng_sub'; [exact RSTK3| lia]).
    assert (RSPX : rng RNG3 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK3| lia]).
    pose proof REST as REST'. destruct REST' as (s' & i' & I' & pad' & bs' & _ & _ & G3 & _).
    pose proof (ai_eb_cobj _ _ _ _ G3 ltac:(apply incl_appr, incl_refl) AG3) as OEB.
    pose proof (clocA_below _ _ _ GL _ _ _ _ _ _ _ _ _ G3 (proj1 OEB)) as (EBLO & EBHI).
    pose proof (gl_rt _ _ _ GL _ _ _ _ _ _ _ G3) as (RT3 & _).
    rewrite LN in SRCG. assert (SRCHI2 : (SRC + n <= 0x32000)%Z) by lia.
    pose proof (gia_global_mobjA _ _ _ GL _ _ _ _ _ _ _ _ _ G3 SRCG RIMG3 RISH3) as OSRC.
    assert (LM : length msg = String.length str).
    { apply (f_equal (@length _)) in EMSG. rewrite !length_map, length_list_ascii in EMSG. exact EMSG. }
    pose proof (rw_cells_split_CB _ _ _ [] _ _ [] [Z.to_nat n; (256 - Z.to_nat n)%nat] HEB3 ltac:(cbn; lia)) as HE'. clear HEB3. cbn [mk_CB_cells app] in HE'.
    destruct (rw_cells_cut _ _ _ 1 HE') as [HE1 HE2]. clear HE'. cbn [firstn skipn cells_size csize Nat.add] in HE1, HE2.
    lazymatch type of HE2 with rw_cells _ _ ?A _ => replace A with (EB + n)%Z in HE2 by lia end.
    unfold ai_FRAME in FR3.
    destruct (rw_cells_cut _ _ _ 2 HD3) as [_ HDJ]. cbn [firstn skipn cells_size Nat.add] in HDJ. rewrite Hhj, Hh0 in HDJ.
    destruct (rw_cells_cut _ _ _ 1 HDJ) as [HD8 _]. clear HDJ. cbn [firstn skipn] in HD8.
    replace (bv_unsigned sp + -144 + Z.of_nat (8 + (8 + 0)))%Z with (bv_unsigned sp + -128)%Z in HD8 by lia.   (* [comment removed for export] *)
    hide HD3. hide FR3. hide HE2.
    pose proof (munch_refl [(bv_unsigned sp + -144 - 2224, bv_unsigned sp + -144); (EB, EB + n)]%Z m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    zstep. zstep.
    name_sp sp (-144)%Z.
    eapply evtF_cut.
    { eapply (asan_memcpy_specZ RNG3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 lo EB SRC n _ (firstn (Z.to_nat n) ej));
        [ reflexivity | reflexivity | reflexivity | exact MI3 | rewrite Hsp; exact ST3 | rewrite Hsp; lia | lia | exact RT3 | exact SRCB
        | rewrite length_app, length_map, length_list_ascii; cbn [length]; lia | lia | exact HE1
        | left; lia | exact OSRC
        | eapply mobjA_sub; [apply aobjA_mobjA; [exact (proj2 OEB) | lia] | lia | lia | lia]
        | lia | lia | exact RIMG3 | rewrite Hsp; exact RSPW ]. }
    cbv beta. intros ms' PO. destruct PO as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & m4 & -> & MU4 & WM4 & MI4 & ST4 & HE1' & _). clear HE1.
    rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 576204)) with (Z_to_bv 64 576204) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -144 - 2224, bv_unsigned sp + -144); (EB, EB + n)]%Z a) m3 m4) by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho]).
    pose proof (airest_f_frame _ _ _ _ _ _ _ _ _ REST MU4 WM4 ltac:(lia) ltac:(lia) ltac:(lia)) as REST4.
    unhide HD3. unhide FR3. unhide HE2.
    transport HD3 m4 AGS ltac:(intros a Ha; cbn [cells_size Nat.add] in Ha; rewrite Hhj, Hh0, Hh2, Hh4 in Ha; cbn [csize Nat.add outside fst snd] in Ha |- *; lia).
    transport FR3 m4 AGS ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
    transport HE2 m4 AGS ltac:(intros a Ha; cbn [cells_size csize Nat.add outside fst snd] in Ha |- *; lia).
    clear MU WM HD8. pose proof (munch_refl ([] : list (Z * Z)) m4) as MU. pose proof (wmono_refl asegs m4) as WM.
    hide HD3. hide FR3. hide HE2. hide HE1'.
    do 2 zstep.
    unhide HD3. unhide FR3. unhide HE2. unhide HE1'.
    eapply (ai_exit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 RNG3 st3 false c' p' msg [hj; h0; C8 (Z_to_bv 64 EB); h2; h4]);
      [exact FP3 | exact MI4 | exact ST4 | | exact HD3 | cbn [cells_size csize Nat.add]; rewrite Hhj, Hh0, Hh2, Hh4; reflexivity | exact FR3 |].
    { eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_weaken; [exact AGS|]. intros a [[Ha|[Ha|[Ha|Ha]]] (_ & _ & Hn & _)]; cbn [outside fst snd].
      - lia.
      - pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G ltac:(apply in_block_app; left; apply in_block_app in Ha as [X|X]; apply in_block_app; [left; exact X| right; apply in_block_app; right; exact X])) as AB. lia.
      - pose proof (gia_in_frames_below _ _ _ GL _ _ _ _ _ _ _ a G Ha) as AB. lia.
      - pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G Ha) as SBD. lia. }
    apply (airest_f_done _ _ _ _ _ _ REST4).
    - lazymatch type of HE2 with rw_cells _ _ _ [CB _ ?j] => exists j end.
      pose proof (rw_cells_uncut _ _ _ _ _ HE1' HE2 ltac:(cbn [cells_size csize Nat.add]; lia)) as HEJ. cbn [app] in HEJ.
      eapply rw_cells_recell; [exact HEJ | pose proof (proj1 (proj1 HEJ)) as WF; cbn in WF |- *; rewrite ?length_app, ?length_map, ?length_list_ascii in *; cbn [length] in *; repeat split; try lia; tauto |].
      cbn [cells_bytes cbytes app]. rewrite EMSG. reflexivity.
    - rewrite LM. lia.
    - exact MOK.
  Qed.
  End Sz8.
  #[using="rc tlsI FO fflagA GL I i G LO BU SPT RSTK RIMG RISH GPL HinP HinB P14 B14 LENB CURS EBL EBP EBB EBO"] Lemma ai_mcp : ltac:(let t := eval cbv delta [ai_mcp__stmt] in ai_mcp__stmt in exact t).
  Proof. intros ra' t0' t1' t2' a0' a3' a4' a5' a6' a7' t3' t4' t5' t6' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 m3 RNG3 st3 SRC n str msg c' p' hj h0 h2 h4. ltac2:(SecDiet.SzSec.closeP 'ai_mcp__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End AIA.
End CANSEC1.
End TwB.
End F_aiAA.
