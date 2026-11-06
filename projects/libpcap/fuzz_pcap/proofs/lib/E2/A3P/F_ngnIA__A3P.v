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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnE2A__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextD__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_chkD__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnTA F_ngnDA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require F_aiEA_body__B3P.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_ngnIA.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnKA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnEA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnE2A__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnEA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnI0A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_ngnICA.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextD__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_chkD__S3.
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
  Hypothesis ADJ : adjust_snapshot_stmt.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis TR : traces_pcap_ng_next_packet TP L (bv_unsigned ra) trC.

  #[local] Abbreviation pcapT := (pcap hptr hptr).
  #[local] Abbreviation MR := (M (PState H hptr) ((Z + ng_found) * pcap hptr hptr)).
  #[local] Abbreviation pv := (F_ngnEA.pv self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).
  #[local] Abbreviation ccells := (F_ngnEA.ccells).
  #[local] Abbreviation ngn_KF := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF H hptr).
  #[local] Abbreviation ngn_idbK := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA.ngn_idbK H hptr HO FO sites).
  #[local] Abbreviation ngn_headA := (F_ngnEA.ngn_headA GIOA TP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CLc FB FL lo P HA DA Af m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).

  #[using="Type"] Lemma implMG_retb_l : forall {St A B} RNGx (a : A) (k : A -> Monad.M St B) s Q ms, implMG RNGx (k a) s Q ms -> implMG RNGx (mbind (mret a) k) s Q ms.
  Proof. intros St A B RNGx a k s Q ms HH. exact HH. Qed.

  #[using="rc sp"] Lemma F_ngnSA_fmt_too_short : forall mx, mem_inv asegs mx -> fmt_at mx NGN_FMT_TOO_SHORT_A "block of type %u in pcapng dump file is too short"%string.
  Proof.
    intros mx MIx. unfold NGN_FMT_TOO_SHORT_A.
    split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs mx 0x22520 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "block of type %u in pcapng dump file is too short"%string) ++ [Z_to_bv 8 0])
                             MIx ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|].
    split; [lia|]. split; [cbn; lia|]. unfold client_globals. repeat (first [left; reflexivity | right]).
  Qed.

  (* [comment removed for export] *)
  Definition ngn_snp_a0__stmt : Prop := forall (ra' t0' t1' t2' x0 x1 a3' a4' a5' a6' a7' x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (PB' : list (@cblock hptr)) (p' : pcapT) (h : pkthdr) (hcs' : list cell) (dw : cell) (ccs : list cell)
           (FMTA : Z) (fs : string) (args : list farg) (e : list Z),
      stk asegs m5 lo (bv_unsigned sp + -224) ->
      rw_cells asegs m5 (bv_unsigned sp + -224) (ngn_frameA ccs) -> cells_size ccs = 24%nat -> mem_inv asegs m5 ->
      ngn_finalC m5 RNG5 ps PB' p' hcs' dw -> is_ng p' = true ->
      fmt_at m5 FMTA fs -> fmt_ok fs args = true -> (length args <= 3)%nat ->
      Forall2 (farg_word true L RNG5 FL (CLc ++ PB') (bv_unsigned sp + -224) (P + 216) 256 m5) args (firstn (length args) [a3'; a4'; a5']) ->
      implMG RNG5 (mret ((-1)%Z, h, set_errbuf e p')) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -224)) gp tp t0' t1' t2' x0 x1
                 (Z_to_bv 64 (P + 216)) (Z_to_bv 64 256) (Z_to_bv 64 FMTA) a3' a4' a5' a6' a7'
                 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x8d0d4) fc None m5 (seg_rom asegs)).
  Section Sz5.
  Variables ra' t0' t1' t2' x0 x1 a3' a4' a5' a6' a7' x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 RNG5 ps PB' p' h hcs' dw ccs FMTA fs args e : ltac2:(SecDiet.SzSec.tyM 'ngn_snp_a0__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  #[using="FO fflagA GL SNPRINTF LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP"] Lemma ngn_snp_a0__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_snp_a0__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros ST5 FR5 Hccs MI5 FIN NG5 FMT5 FOK LA FW.
    pose proof FIN as (FP5 & G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF5).
    hide FR5. hide HH. hide HD.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    ienterG. zstep. unhide FR5. unhide HH. unhide HD. clear MU WM.
    eapply (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_snp_call rc tlsI H hptr FO GIOA fflagA) with (RA := 0x8d0d8%Z) (ccs := ccs) (PB' := PB') (p' := p') (hcs' := hcs') (dw := dw) (fs := fs) (args := args); try eassumption; [lia | reflexivity |].
    intros m6 t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' ST6 FR6 MI6 FIN6.
    hide FR6.
    pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
    zstep. zstep. unhide FR6.
    apply evtF_done. subst POSTQ0.
    eapply (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_ret_m1 rc H hptr GIOA) with (ccs := ccs) (PB' := PB') (hcs' := hcs'); try eassumption. exact (FIN6 e).
  Qed.
  End Sz5.
  #[using="FO fflagA GL SNPRINTF LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP"] Lemma ngn_snp_a0 : ltac:(let t := eval cbv delta [ngn_snp_a0__stmt] in ngn_snp_a0__stmt in exact t).
  Proof. intros ra' t0' t1' t2' x0 x1 a3' a4' a5' a6' a7' x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 RNG5 ps PB' p' h hcs' dw ccs FMTA fs args e. ltac2:(SecDiet.SzSec.closeP 'ngn_snp_a0__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngn_idb_tail__stmt : Prop := forall (LOOP : pcapT -> MR),
    ngn_headA (fun p' ps' RNG' ms' => implMG RNG' (mbind (LOOP p') ngn_KF) ps' POSTQ ms') ->
    forall (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
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
      implMG RNG5 (mbind (let lt := get_le16 data 8 in
                          let sl := get_le32 data 12 in
                          if negb (linktype =? lt) then mret (inl (-1)%Z, set_errbuf (Msg.iface_type_differs lt) (pv bq alloc data eb sx ix))
                          else if negb (snapshot =? pcapint_adjust_snapshot linktype sl) then mret (inl (-1)%Z, set_errbuf (Msg.iface_snaplen_differs sl) (pv bq alloc data eb sx ix))
                          else mbind (add_interface MOps (prims HO FO sites) (pv bq alloc data eb sx ix) 8 (mkCursor 16 (rem - 8) bt))
                                     (fun r => let '(ok, c, p, msg) := r in if ok then LOOP p else mret (inl (-1)%Z, set_errbuf msg p))) ngn_KF) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -224)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 2147450880)
                 (Z_to_bv 64 (Z.shiftr (Bq + 8) 3)) a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 (Bq + 12)) (Z_to_bv 64 (P + 216)) (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) (Z_to_bv 64 (P + 660))
                 (Z_to_bv 64 1) (Z_to_bv 64 168627466) (Z_to_bv 64 P) (Z_to_bv 64 Af) (Z_to_bv 64 (Bq + 8))
                 t3' t4' t5' t6') F (Z_to_bv 64 0x8ce40) fc None m5 (seg_rom asegs)).
  Section Sz6.
  Variables LOOP : ltac2:(SecDiet.SzSec.tyM 'ngn_idb_tail__stmt "v" @LOOP).
  #[using="rc tlsI fflagA GL SNPRINTF LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HLOC DLOC trC ADDIF ADJ GPL TR"] Lemma ngn_idb_tail__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_idb_tail__stmt "v").
  Proof.
    intros HLOOP.
 intros until cpad. intros FP5 ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (rng_fp_le _ _ _ _ FP5 RSTK) as RSTK5.
    assert (RSPW : rng RNG5 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK5| lia]).
    pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    assert (HinP : In (self, P, 680%Z) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    assert (HinB : In (bq, Bq, alloc) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; right; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinP) as ((PBAND & P3 & PTOP & P2) & P1 & PUNP & PRNG & PRSH & PAR).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinB) as ((BBAND & B3 & BTOP & B2) & B1 & BUNP & BRNG & BRSH & BAR).
    cbn [cb_addr cb_size fst snd] in *.
    pose proof (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ G5 eq_refl) as [APB API].
    pose proof WF as (W1' & _ & W3 & W4 & _ & _ & _ & _ & W9' & _).
    unfold F_ngnEA.pv, pcap_blocks, psize, is_ng in EPB, APB. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, APB. unfold PCAP_NG_SF_TOTAL in APB.
    unfold F_ngnEA.pv in W3, W4, W1', W9'. cbn [pc_bufalloc pc_bufdata pc_snapshot pc_linktype] in W3, W4, W1', W9'. unfold INT_MAX in W1'.
    assert (EBX : Bx' = Bq) by congruence. subst Bx'.
    band_ind PBAND bP. band_ind BBAND bB.
    unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, F_ngnEA.pv in CELLS.
    cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_ng pk_cleanup_ng PK] in CELLS.
    unfold F_ngnEA.pv in BUF. cbn [pc_bufalloc] in BUF. cbn [pc_bufdata] in PFX.
    (* [comment removed for export] *)
    cbv zeta. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA.get_le16_q8' data 8) by lia. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.get_le32_q8 data 12) by lia.
    set (l0 := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data 8 0) in *. set (l1 := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data 8 1) in *.
    pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data 8 0 DRNG ltac:(lia)) as Rl0. pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data 8 1 DRNG ltac:(lia)) as Rl1. fold l0 in Rl0. fold l1 in Rl1.
    name_field data 12%Z n0 n1 n2 n3 DRNG.
    assert (LBS : length bsx' = Z.to_nat alloc) by (destruct BUF as [[WFB _] _]; cbn in WFB; lia).
    pose proof BUF as BUF0.
    apply (rw_cells_split_CB asegs m5 _ [] (Z.to_nat alloc) _ [] [8; 2; 2; 4; Z.to_nat alloc - 16]%nat) in BUF; [| cbn; lia]. cbn [mk_CB_cells app] in BUF.
    rewrite !skipn_skipn in BUF. cbn [Nat.add] in BUF.
    rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA.firstn2_q8 data bsx' 8 8 PFX eq_refl), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.firstn4_q8 data bsx' 12 12 PFX eq_refl) in BUF by lia. fold l0 l1 n0 n1 n2 n3 in BUF.
    assert (BUF4 : rw_cells asegs m5 Bq [CB 8 (firstn 8 bsx'); C2 (Z_to_bv 64 (l0 + 256 * l1)); CB 2 (firstn 2 (skipn 10 bsx')); C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); CB (Z.to_nat alloc - 16) (firstn (Z.to_nat alloc - 16) (skipn 16 bsx'))]).
    { eapply rw_cells_recell; [exact BUF | | ].
      { cbn. rewrite ?length_firstn, ?length_skipn. repeat split; try exact Logic.I; lia. }
      cbn [cells_bytes cbytes app]. rewrite (le2_lit l0 l1), (le4_lit n0 n1 n2 n3) by lia. reflexivity. }
    clear BUF.
    pose proof FR5 as FRJ. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_frameA in FRJ. cbn [app] in FRJ.
    pose proof (adjust_snapshot_range linktype (le4val n0 n1 n2 n3) ltac:(unfold le4val; lia)) as ADR. unfold INT_MAX in ADR.
    hide FR5. hide PRIV. hide IFS. hide HH. hide HD. hide BUF0.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    ienterG.
    ck0_at PUNP (P + 100)%Z; ck_go.
    ck0_at BUNP (Bq + 8)%Z; ck_go.
    rewrite (sx32_small linktype) by lia.
    zstep. rewrite (zx16_lit (l0 + 256 * l1)) by lia.
    zstep. if_cases BR; zify_cond BR; rewrite ?unsigned_lit in BR by lia.
    - (* [comment removed for export] *)
      replace (linktype =? l0 + 256 * l1) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv iota.
      do 5 zstep.
      unhide FR5. unhide PRIV. unhide IFS. unhide HH. unhide HD. unhide BUF0.
      assert (MSG : fmt_at m5 0x229a0 "an interface has a type %u different from the type of the first interface"%string).
      { split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m5 0x229a0 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "an interface has a type %u different from the type of the first interface"%string) ++ [Z_to_bv 8 0])
                               MI5 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|].
        split; [lia|]. split; [cbn; lia|]. unfold client_globals. repeat (first [left; reflexivity | right]). }
      apply evtF_done. apply implMG_retb_l. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF.
      eapply ngn_snp_a0 with (fs := "an interface has a type %u different from the type of the first interface"%string) (args := [AInt (l0 + 256 * l1)%Z]) (PB' := pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) (hcs' := hcs);
        try eassumption;
        exit_sides ltac:(split; [exact FP5|]; split; [exact G5|]; split; [apply PCAPR_closable_of; exact PC5|]; split; [exact AG5|]; split; [exact HH|]; split; [exact Hh|];
                         split; [exact HD|]; split; [exact Hd| exact OF5]).
    - (* [comment removed for export] *)
      replace (linktype =? l0 + 256 * l1) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb]. cbv iota.
      do 2 zstep.
      ck0_at PUNP (P + 96)%Z; ck_go.
      ck0 BUNP; ck_go.
      rewrite (sx32_small snapshot) by lia.
      zstep. rewrite (sx32_s32 (le4val n0 n1 n2 n3)) by (unfold le4val; lia).
      zstep.
      unhide FR5. unhide PRIV. unhide IFS. unhide HH. unhide HD. unhide BUF0.
      pose proof atop_range as AR.
      name_sp sp (-224)%Z.
      eapply evtF_cut;
        [ eapply (ADJ _ sp0) with (lo := lo) (lt := linktype) (snaplen := le4val n0 n1 n2 n3);
          [ assumption | rewrite Hsp; exact ST5 | reflexivity | lia | reflexivity | unfold le4val; lia ]
        | ].
      cbv beta. intros ms' PO. unfold leaf_post in PO. destruct_exs PO. destruct PO as (-> & MUc & WMc & MIc & STc & ->).
      rewrite Hsp in *.
      lazymatch type of MUc with munch _ _ ?mb => rename mb into m6 end.
      assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -224 - 0, bv_unsigned sp + -224)]%Z a) m5 m6) by (eapply agrees_on_of_munch; [exact MUc | exact WMc | intros a _ Ho; exact Ho]).
      assert (FW6 : Forall (pcap_iv FL (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) [(bv_unsigned sp + -224 - 0, bv_unsigned sp + -224)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]).
      assert (G6 : GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m6) by (eapply (gl_frame _ _ _ GL); [exact G5 | exact MUc | exact WMc | exact FW6]).
      assert (PC6 : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m6).
      { eapply PCAPR_agree; [exact AGS | | exact PC5]. intros a Ha.
        pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G5 ltac:(apply in_block_app; left; apply in_block_app; right; exact Ha)). cbn [outside fst snd]. lia. }
      assert (AG6 : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
      { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [| intros a [K _]; exact K].
        eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G5 | exact MUc | exact WMc | | lia].
        apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]. }
      transport_after_call asegs m5 m6 MUc WMc. clear MUc WMc MU WM.
      clear ST5. rename STc into ST5.
      unname_sp.
      replace (ret_pc (Z_to_bv 64 577180)) with (Z_to_bv 64 577180) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
      assert (FR6 : rw_cells asegs m6 (bv_unsigned sp + -224) (ngn_frameA [C8 (Z_to_bv 64 (Bq + 16)); C8 (Z_to_bv 64 (rem - 8)); C4 (Z_to_bv 64 bt); CB 4 cpad])) by exact FRJ.
      hide FR6. hide HH. hide HD. hide BUF0.
      zstep. if_cases BR2; zify_cond BR2; rewrite ?unsigned_lit in BR2 by lia.
      + (* [comment removed for export] *)
        replace (snapshot =? pcapint_adjust_snapshot linktype (le4val n0 n1 n2 n3)) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv iota.
        ck0_at BUNP (Bq + 12)%Z; ck_go.
        zstep. rewrite (sx32_lit n0 n1 n2 n3) by lia. do 4 zstep.
        unhide FR6. unhide HH. unhide HD. unhide BUF0.
        assert (MSG : fmt_at m6 0x22a20 "an interface has a snapshot length %u different from the snapshot length of the first interface"%string).
        { split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m6 0x22a20 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "an interface has a snapshot length %u different from the snapshot length of the first interface"%string) ++ [Z_to_bv 8 0])
                                 MIc ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|].
          split; [lia|]. split; [cbn; lia|]. unfold client_globals. repeat (first [left; reflexivity | right]). }
        apply evtF_done. apply implMG_retb_l. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF.
        eapply ngn_snp_a0 with (fs := "an interface has a snapshot length %u different from the snapshot length of the first interface"%string) (args := [AInt (sxv n0 n1 n2 n3)]) (PB' := pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) (hcs' := hcs);
          try eassumption;
          exit_sides ltac:(split; [exact FP5|]; split; [exact G6|]; split; [apply PCAPR_closable_of; exact PC6|]; split; [exact AG6|]; split; [exact HH|]; split; [exact Hh|];
                           split; [exact HD|]; split; [exact Hd| exact OF5]).
      + (* [comment removed for export] *)
        replace (snapshot =? pcapint_adjust_snapshot linktype (le4val n0 n1 n2 n3)) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb]. cbv iota.
        unhide FR6. unhide HH. unhide HD. unhide BUF0.
        apply evtF_done.
        eapply (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_ngnICA.ngn_idb_call rc tlsI H hptr HO FO sites GIOA TP fflagA GL) with (rem := rem) (hcs := hcs) (dw := dw); try eassumption.
  Qed.
  End Sz6.
  #[using="rc tlsI fflagA GL SNPRINTF LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HLOC DLOC trC ADDIF ADJ GPL TR"] Lemma ngn_idb_tail : ltac:(let t := eval cbv delta [ngn_idb_tail__stmt] in ngn_idb_tail__stmt in exact t).
  Proof. intros LOOP. ltac2:(SecDiet.SzSec.closeP 'ngn_idb_tail__body "v"). Qed.

  (* [comment removed for export] *)
  Definition ngn_idb__stmt : Prop := forall (LOOP : pcapT -> MR),
    ngn_headA (fun p' ps' RNG' ms' => implMG RNG' (mbind (LOOP p') ngn_KF) ps' POSTQ ms') ->
    forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x11 t3' t4' t5' t6' : word) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (bt : Z) (hcs : list cell) (dw : cell) (cpad : list byte),
      fp_le RNG RNG5 ->
      stk asegs m5 lo (bv_unsigned sp + -224) ->
      rw_cells asegs m5 (bv_unsigned sp + -224) (ngn_frameA (ccells Bq rem bt cpad)) -> mem_inv asegs m5 ->
      GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells asegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells asegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (0 <= rem)%Z ->
      (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implMG RNG5 (mbind (ngn_idbK LOOP (mkCursor 8 rem bt) (pv bq alloc data eb sx ix)) ngn_KF) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -224)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 2147450880) a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 2) (Z_to_bv 64 (P + 216)) (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) (Z_to_bv 64 (P + 660))
                 (Z_to_bv 64 1) (Z_to_bv 64 168627466) (Z_to_bv 64 P) (Z_to_bv 64 Af) x11
                 t3' t4' t5' t6') F (Z_to_bv 64 0x8cd94) fc None m5 (seg_rom asegs)).
  Section Sz7.
  Variables LOOP : ltac2:(SecDiet.SzSec.tyM 'ngn_idb__stmt "v" @LOOP).
  #[using="rc tlsI fflagA GL SNPRINTF LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HLOC DLOC trC ADDIF ADJ GPL TR"] Lemma ngn_idb__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_idb__stmt "v").
  Proof.
    intros HLOOP.
 intros until cpad. intros FP5 ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (rng_fp_le _ _ _ _ FP5 RSTK) as RSTK5.
    assert (RSPW : rng RNG5 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK5| lia]).
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA.ngn_idbK, get_from_block_data. cbn [cur_remaining cur_off cur_block_type].
    change (pc_swapped (pv bq alloc data eb sx ix)) with swapped. change (pc_bufdata (pv bq alloc data eb sx ix)) with data.
    pose proof FR5 as FRJ. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_frameA, F_ngnEA.ccells in FRJ. cbn [app] in FRJ.
    hide FR5. hide HH. hide HD.
    pose proof (munch_refl [(bv_unsigned sp + -224 + 96, bv_unsigned sp + -224 + 112)]%Z m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    ienterG. zstep.
    zstep.
    zstep. if_cases BR0; zify_cond BR0; rewrite ?unsigned_lit in BR0 by lia.
    - (* [comment removed for export] *)
      replace (rem <? 8) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      do 5 zstep.
      unhide FR5. unhide HH. unhide HD. apply evtF_done. apply implMG_retb_l. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF.
      eapply (@F_ngnEA.ngn_snp_b8 rc tlsI H hptr FO GIOA fflagA GL SNPRINTF) with (fs := "block of type %u in pcapng dump file is too short"%string) (args := [AInt 1]) (PB' := pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix);
        try eassumption; [ reflexivity | | reflexivity | apply F_ngnSA_fmt_too_short; exact MI5 | reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity| constructor] ].
      split; [exact FP5|]. split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [exact Hh|].
      split; [exact HD|]. split; [exact Hd| exact OF5].
    - (* [comment removed for export] *)
      replace (rem <? 8) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota. cbv beta. change (8 + 8)%Z with 16%Z. change (8 + 4)%Z with 12%Z.
      change (pc_linktype (pv bq alloc data eb sx ix)) with linktype. change (pc_snapshot (pv bq alloc data eb sx ix)) with snapshot.
      pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
      pose proof G5 as G5e. rewrite EPB in G5e.
      assert (HinP : In (self, P, 680%Z) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
      assert (HinB : In (bq, Bq, alloc) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; right; left; reflexivity).
      pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinP) as ((PBAND & P3 & PTOP & P2) & P1 & PUNP & PRNG & PRSH & PAR).
      pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinB) as ((BBAND & B3 & BTOP & B2) & B1 & BUNP & BRNG & BRSH & BAR).
      cbn [cb_addr cb_size fst snd] in *.
      pose proof (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ G5 eq_refl) as [APB API].
      pose proof WF as (W1' & _ & W3 & W4 & _).
      unfold F_ngnEA.pv, pcap_blocks, psize, is_ng in EPB, APB. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, APB. unfold PCAP_NG_SF_TOTAL in APB.
      unfold F_ngnEA.pv in W3, W4, W1'. cbn [pc_bufalloc pc_bufdata pc_snapshot] in W3, W4, W1'. unfold INT_MAX in W1'.
      assert (EBX : Bx' = Bq) by congruence. subst Bx'.
      band_ind PBAND bP. band_ind BBAND bB.
      unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, F_ngnEA.pv in CELLS.
      cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_ng pk_cleanup_ng PK] in CELLS.
      unfold F_ngnEA.pv in BUF. cbn [pc_bufalloc] in BUF. cbn [pc_bufdata] in PFX.
      (* [comment removed for export] *)
      set (l0 := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data 8 0) in *. set (l1 := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data 8 1) in *. set (r0 := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data 10 0) in *. set (r1 := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data 10 1) in *.
      pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data 8 0 DRNG ltac:(lia)) as Rl0. pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data 8 1 DRNG ltac:(lia)) as Rl1.
      pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data 10 0 DRNG ltac:(lia)) as Rr0. pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data 10 1 DRNG ltac:(lia)) as Rr1.
      fold l0 in Rl0. fold l1 in Rl1. fold r0 in Rr0. fold r1 in Rr1.
      name_field data 12%Z n0 n1 n2 n3 DRNG.
      assert (LBS : length bsx' = Z.to_nat alloc) by (destruct BUF as [[WFB _] _]; cbn in WFB; lia).
      apply (rw_cells_split_CB asegs m5 _ [] (Z.to_nat alloc) _ [] [8; 2; 2; 4; Z.to_nat alloc - 16]%nat) in BUF; [| cbn; lia]. cbn [mk_CB_cells app] in BUF.
      rewrite !skipn_skipn in BUF. cbn [Nat.add] in BUF.
      rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA.firstn2_q8 data bsx' 8 8 PFX eq_refl), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA.firstn2_q8 data bsx' 10 10 PFX eq_refl), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.firstn4_q8 data bsx' 12 12 PFX eq_refl) in BUF by lia.
      fold l0 l1 r0 r1 n0 n1 n2 n3 in BUF.
      replace (firstn (Z.to_nat alloc - 16) (skipn 16 bsx')) with (skipn 16 bsx') in BUF by (symmetry; apply firstn_all2; rewrite length_skipn; lia).
      assert (BUF4 : rw_cells asegs m5 Bq [CB 8 (firstn 8 bsx'); C2 (Z_to_bv 64 (l0 + 256 * l1)); CB 2 [b8 r0; b8 r1]; C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); CB (Z.to_nat alloc - 16) (skipn 16 bsx')]).
      { eapply rw_cells_recell; [exact BUF | | ].
        { cbn. rewrite ?length_firstn, ?length_skipn. repeat split; try exact Logic.I; lia. }
        cbn [cells_bytes cbytes app]. rewrite (le2_lit l0 l1), (le4_lit n0 n1 n2 n3) by lia. reflexivity. }
      clear BUF.
      hide PRIV. hide IFS.
      (* [comment removed for export] *)
      do 5 zstep.
      assert (AGF : agrees_on (fun a => outside [(bv_unsigned sp + -224 + 96, bv_unsigned sp + -224 + 112)]%Z a) m5 m1) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
      unhide FR5. unhide HH. unhide HD. unhide PRIV. unhide IFS. clear FR5.
      apply (agrees_rw_cells _ _ _ _ _ AGF) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside fst snd]; lia].
      apply (agrees_rw_cells _ _ _ _ _ AGF) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside fst snd]; lia].
      apply (agrees_rw_cells _ _ _ _ _ AGF) in PRIV; [| intros a Ha; pose proof (priv_cells_psize _ _ _ _ _ PRIV) as PZ; unfold psize, is_ng, F_ngnEA.pv, PCAP_PRIV_OFF, priv_cells in PZ, Ha; cbn [pc_priv] in PZ, Ha; unfold PCAP_NG_SF_TOTAL in PZ; cbn [outside fst snd]; lia].
      assert (FW6 : Forall (pcap_iv FL (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) [(bv_unsigned sp + -224 + 96, bv_unsigned sp + -224 + 112)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]).
      assert (G6 : GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m1) by (eapply (gl_frame _ _ _ GL); [exact G5 | exact MU | exact WM | exact FW6]).
      assert (PC6 : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m1).
      { eapply PCAPR_agree; [exact AGF | | exact PC5]. intros a Ha.
        pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G5 ltac:(apply in_block_app; left; apply in_block_app; right; exact Ha)). cbn [outside fst snd]. lia. }
      assert (AG6 : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m1).
      { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [| intros a [K _]; exact K].
        eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G5 | exact MU | exact WM | | lia].
        apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]. }
      clear MU WM AGF G5 PC5 AG5 IFS G5e.
      zstep. if_cases BRZ; zify_cond BRZ. { exfalso. rewrite ?unsigned_lit in BRZ by lia. lia. }
      ck0_at PUNP (P + 56)%Z; ck_go.
      zstep. rewrite (sx32_small (Z.b2z swapped)) by (destruct swapped; cbn; lia).
      do 2 zstep.
      assert (FR6 : rw_cells asegs m1 (bv_unsigned sp + -224) (ngn_frameA [C8 (Z_to_bv 64 (Bq + 16)); C8 (Z_to_bv 64 (rem - 8)); C4 (Z_to_bv 64 bt); CB 4 cpad])) by exact FRJ.
      zstep. if_cases BRS; zify_cond BRS.
      + (* [comment removed for export] *)
        lazymatch goal with |- context [if swapped then ?X else ?Y] => replace (if swapped then X else Y) with Y by (rewrite BRS; reflexivity) end.
        cbv zeta.
        change (pc_bufdata (pv bq alloc data eb sx ix)) with data.
        change (pc_linktype (pv bq alloc data eb sx ix)) with linktype. change (pc_snapshot (pv bq alloc data eb sx ix)) with snapshot.
        apply evtF_done.
        eapply (ngn_idb_tail LOOP HLOOP) with (rem := rem) (hcs := hcs) (dw := dw); try eassumption. lia.
      + (* [comment removed for export] *)
        lazymatch goal with |- context [if swapped then ?X else ?Y] => replace (if swapped then X else Y) with X by (rewrite BRS; reflexivity) end.
        cbv zeta.
        change (set_bufdata (swap_field 4 12 (swap_field 2 8 data)) (pv bq alloc data eb sx ix)) with (pv bq alloc (swap_field 4 12 (swap_field 2 8 data)) eb sx ix).
        rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_chkD__S3.F_ngnextI.idb_swap_data' data) by lia. fold l0 l1 r0 r1 n0 n1 n2 n3.
        set (data' := firstn 8 data ++ [l1; l0; r0; r1; n3; n2; n1; n0] ++ skipn 16 data).
        change (pc_bufdata (pv bq alloc data' eb sx ix)) with data'.
        change (pc_linktype (pv bq alloc data' eb sx ix)) with linktype. change (pc_snapshot (pv bq alloc data' eb sx ix)) with snapshot.
        assert (FRC : rw_cells asegs m1 (bv_unsigned sp + -136) [C8 (Z_to_bv 64 65280)]).
        { lazymatch type of FRJ with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?tl) =>
            pose proof (proj2 (proj1 (rw_cells_app asegs m1 _ [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10] (c11 :: tl)) FRJ)) as X;
            pose proof (proj1 (proj1 (rw_cells_app asegs m1 _ [c11] tl) X)) as X2 end.
          cbn [cells_size csize Nat.add] in X2. replace (bv_unsigned sp + -224 + Z.of_nat 88) with (bv_unsigned sp + -136) in X2 by lia. exact X2. }
        assert (HinB2 : In (bq, Bq, alloc) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) by (right; left; reflexivity).
        destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G6 HLOC HinB2 ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kH & kHr & kH1 & kH2).
        destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G6 DLOC HinB2 ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kD & kDr & kD1 & kD2).
        cbn [cb_addr cb_size fst snd] in kH1, kH2, kD1, kD2.
        hide FR6. hide HH. hide HD. hide PRIV. hide CELLS.
        eapply evtF_cut.
        { eapply (ngn_idb_swapA RNG5 sp gp tp F fc lo) with (l0 := l0) (l1 := l1) (n0 := n0) (n1 := n1) (n2 := n2) (n3 := n3) (Bq := Bq) (alloc := alloc) (bB := bB);
            [repeat (apply Forall_cons; [lia|]); apply Forall_nil | exact BUF4 | exact FRC | assumption | exact LO | exact BU | lia | exact RSPW | exact BUNP | exact BTOP
            | lia | exact B2 | exact B1 | exact bBr | exact bBhi | exact bBlo | exact bBimg | exact BRNG | exact BRSH]. }
        cbv beta. intros ms' (a1v & a2v & a3v & lv & m7 & -> & MU7 & WM7 & MI7 & HB7 & E1 & E0).
        assert (AGP : agrees_on (fun a => outside [(Bq + 8, Bq + 16)]%Z a) m1 m7) by (eapply agrees_on_of_munch; [exact MU7 | exact WM7 | intros a _ Ho; exact Ho]).
        unhide FR6. unhide HH. unhide HD. unhide PRIV. unhide CELLS.
        lazymatch goal with STX : stk asegs m1 _ _ |- _ => pose proof (agrees_stk _ _ _ _ _ AGP STX ltac:(intros a Ha; cbn [outside fst snd]; lia)) as ST7 end.
        apply (agrees_rw_cells _ _ _ _ _ AGP) in FR6; [| intros a Ha; unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_frameA in Ha; rewrite !cells_size_app in Ha; cbn [outside fst snd cells_size csize Nat.add] in Ha |- *; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside fst snd]; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside fst snd]; lia].
        assert (FW7 : Forall (pcap_iv FL (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) [(Bq + 8, Bq + 16)]%Z).
        { apply Forall_cons; [|apply Forall_nil]. right; left. unfold iv_in_block, pcap_blocks. apply Exists_cons_tl. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold F_ngnEA.pv. cbn [pc_buffer pc_bufalloc]. lia. }
        assert (G7 : GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m7) by (eapply (gl_frame _ _ _ GL); [exact G6 | exact MU7 | exact WM7 | exact FW7]).
        (* [comment removed for export] *)
        assert (BUF7 : rw_cells asegs m7 Bq [CB (Z.to_nat alloc) (firstn 8 bsx' ++ [b8 l1; b8 l0; b8 r0; b8 r1; b8 n3; b8 n2; b8 n1; b8 n0] ++ skipn 16 bsx')]).
        { assert (R7 : rw_cells asegs m7 Bq [CB 8 (firstn 8 bsx'); C2 (Z_to_bv 64 (l1 + 256 * l0)); CB 2 [b8 r0; b8 r1]; C4 (Z_to_bv 64 (le4val n3 n2 n1 n0)); CB (Z.to_nat alloc - 16) (skipn 16 bsx')]).
          { eapply rw_cells_recell; [exact HB7 | | ].
            { cbn. rewrite ?length_firstn, ?length_skipn. repeat split; try exact Logic.I; lia. }
            cbn [cells_bytes cbytes app]. rewrite (le2_of_val lv l1 l0 l1), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.le4_word_mod32 a1v (le4val n3 n2 n1 n0) E0) by lia. rewrite (le2_lit l1 l0), (le4_lit n3 n2 n1 n0) by lia. reflexivity. }
          pose proof (rw_cells_merge asegs m7 Bq [] _ [] ltac:(rewrite app_nil_r; exact R7)) as R8.
          lazymatch type of R8 with rw_cells _ _ _ ([] ++ [CB ?n ?bs]) =>
            replace n with (Z.to_nat alloc) in R8 by (cbn [cells_size csize]; lia);
            cbn [app cells_bytes cbytes] in R8 end.
          rewrite (le2_lit l1 l0), (le4_lit n3 n2 n1 n0), app_nil_r in R8 by lia. exact R8. }
        assert (LEN' : length data' = length data).
        { subst data'. change (skipn 16 data) with (skipn (8 + length [l1; l0; r0; r1; n3; n2; n1; n0]) data). apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.splice_length. cbn [length]. lia. }
        assert (PFX7 : firstn (length data') (firstn 8 bsx' ++ [b8 l1; b8 l0; b8 r0; b8 r1; b8 n3; b8 n2; b8 n1; b8 n0] ++ skipn 16 bsx') = map b8 data').
        { subst data'. change ([b8 l1; b8 l0; b8 r0; b8 r1; b8 n3; b8 n2; b8 n1; b8 n0] ++ skipn 16 bsx') with (map b8 [l1; l0; r0; r1; n3; n2; n1; n0] ++ skipn (8 + length [l1; l0; r0; r1; n3; n2; n1; n0]) bsx').
          change ([l1; l0; r0; r1; n3; n2; n1; n0] ++ skipn 16 data) with ([l1; l0; r0; r1; n3; n2; n1; n0] ++ skipn (8 + length [l1; l0; r0; r1; n3; n2; n1; n0]) data).
          apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.splice_pfx; [exact PFX | cbn [length]; lia | lia]. }
        assert (HQ7 : forall a, (0 <= a < 2^64)%Z -> ~ (Bq <= a < Bq + alloc)%Z -> outside [(Bq + 8, Bq + 16)]%Z a) by (intros a _ Hn; cbn [outside fst snd]; lia).
        assert (PC7 : PCAPR (hptr:=hptr) P (pv bq alloc data' eb sx ix) (pcap_blocks (pv bq alloc data' eb sx ix) P Bq Ix) FB m7).
        { eapply (@F_ngnEA.PCAPR_bufdata rc tlsI H hptr FO GIOA fflagA GL) with (m5 := m1) (data := data) (Q := fun a => outside [(Bq + 8, Bq + 16)]%Z a);
            [exact G6 | exact PC6 | exact AGP | exact HQ7 | exact BUF7 | exact PFX7 | exact LEN']. }
        assert (G7' : GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data' eb sx ix) P Bq Ix) FB FL m7) by exact G7.
        assert (AG7 : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m7).
        { eapply agrees_on_trans; [exact AG6|]. eapply agrees_on_weaken; [| intros a [K _]; exact K].
          eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G6 | exact MU7 | exact WM7 | | lia].
          apply Forall_cons; [|apply Forall_nil]. right; left. unfold iv_in_block, pcap_blocks. apply Exists_cons_tl. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold F_ngnEA.pv. cbn [pc_buffer pc_bufalloc]. lia. }
        assert (DRNG' : Forall (fun x => 0 <= x < 256)%Z data').
        { subst data'. change (skipn 16 data) with (skipn (8 + length [l1; l0; r0; r1; n3; n2; n1; n0]) data). apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.splice_Forall; [exact DRNG|].
          repeat (apply Forall_cons; [lia|]). apply Forall_nil. }
        apply evtF_done.
        eapply (ngn_idb_tail LOOP HLOOP) with (rem := rem) (hcs := hcs) (dw := dw) (data := data');
          [exact FP5 | exact ST7 | exact FR6 | exact MI7 | exact G7' | exact PC7 | exact AG7 | exact HH | exact Hh | exact HD | exact Hd | exact DRNG'
          | rewrite LEN'; exact LEN | exact L30 | lia | exact Hbt | exact OF5].
  Qed.
  End Sz7.
  #[using="rc tlsI fflagA GL SNPRINTF LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HLOC DLOC trC ADDIF ADJ GPL TR"] Lemma ngn_idb : ltac:(let t := eval cbv delta [ngn_idb__stmt] in ngn_idb__stmt in exact t).
  Proof. intros LOOP. ltac2:(SecDiet.SzSec.closeP 'ngn_idb__body "v"). Qed.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnEA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnI0A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_ngnICA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
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
  Hypothesis ADJ : adjust_snapshot_stmt.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis TR : traces_pcap_ng_next_packet TP L (bv_unsigned ra) trC.

  #[local] Abbreviation pcapT := (pcap hptr hptr).
  #[local] Abbreviation MR := (M (PState H hptr) ((Z + ng_found) * pcap hptr hptr)).
  #[local] Abbreviation pv := (A3P.F_ngnEA.TwB.pv self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).
  #[local] Abbreviation ccells := (A3P.F_ngnEA.TwB.ccells).
  #[local] Abbreviation ngn_KF := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF H hptr).
  #[local] Abbreviation ngn_idbK := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA.TwB.ngn_idbK H hptr HO FO sites).
  #[local] Abbreviation ngn_headA := (A3P.F_ngnEA.TwB.ngn_headA GIOA TP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CLc FB FL lo P HA DA Af m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).

  #[using="Type"] Lemma implMG_retb_l : forall {St A B} RNGx (a : A) (k : A -> Monad.M St B) s Q ms, implMG RNGx (k a) s Q ms -> implMG RNGx (mbind (mret a) k) s Q ms.
  Proof. intros St A B RNGx a k s Q ms HH. exact HH. Qed.

  #[using="rc sp"] Lemma F_ngnSA_fmt_too_short : forall mx, mem_inv asegs mx -> fmt_at mx NGN_FMT_TOO_SHORT_A "block of type %u in pcapng dump file is too short"%string.
  Proof.
    intros mx MIx. unfold NGN_FMT_TOO_SHORT_A.
    split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs mx 0x22520 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "block of type %u in pcapng dump file is too short"%string) ++ [Z_to_bv 8 0])
                             MIx ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|].
    split; [lia|]. split; [cbn; lia|]. unfold client_globals. repeat (first [left; reflexivity | right]).
  Qed.

  (* [comment removed for export] *)
  Definition ngn_snp_a0__stmt : Prop := forall (ra' t0' t1' t2' x0 x1 a3' a4' a5' a6' a7' x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (PB' : list (@cblock hptr)) (p' : pcapT) (h : pkthdr) (hcs' : list cell) (dw : cell) (ccs : list cell)
           (FMTA : Z) (fs : string) (args : list farg) (e : list Z),
      stk asegs m5 lo (bv_unsigned sp + -240) ->
      rw_cells asegs m5 (bv_unsigned sp + -240) (ngn_frameA ccs) -> cells_size ccs = 24%nat -> mem_inv asegs m5 ->
      ngn_finalC m5 RNG5 ps PB' p' hcs' dw -> is_ng p' = true ->
      fmt_at m5 FMTA fs -> fmt_ok fs args = true -> (length args <= 3)%nat ->
      Forall2 (farg_word true L RNG5 FL (CLc ++ PB') (bv_unsigned sp + -240) (P + 216) 256 m5) args (firstn (length args) [a3'; a4'; a5']) ->
      implMG RNG5 (mret ((-1)%Z, h, set_errbuf e p')) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0' t1' t2' x0 x3
                 (Z_to_bv 64 (P + 216)) (Z_to_bv 64 256) (Z_to_bv 64 FMTA) a3' a4' a5' a6' a7'
                 x4 x5 x2 x1 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x8d2d0) fc None m5 (seg_rom asegs)).
  Section Sz5.
  Variables ra' t0' t1' t2' x0 x1 a3' a4' a5' a6' a7' x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 RNG5 ps PB' p' h hcs' dw ccs FMTA fs args e : ltac2:(SecDiet.SzSec.tyM 'ngn_snp_a0__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  #[using="FO fflagA GL SNPRINTF LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP"] Lemma ngn_snp_a0__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_snp_a0__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
 intros ST5 FR5 Hccs MI5 FIN NG5 FMT5 FOK LA FW.
    pose proof FIN as (FP5 & G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF5).
    hide FR5. hide HH. hide HD.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    ienterG. zstep. unhide FR5. unhide HH. unhide HD. clear MU WM.
    eapply (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_snp_call rc tlsI H hptr FO GIOA fflagA) with (RA := 0x8d2d4%Z) (ccs := ccs) (PB' := PB') (p' := p') (hcs' := hcs') (dw := dw) (fs := fs) (args := args); try eassumption; [lia | reflexivity |].
    intros m6 t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' ST6 FR6 MI6 FIN6.
    hide FR6.
    pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
    zstep. zstep. unhide FR6.
    apply evtF_done. subst POSTQ0.
    eapply (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_ret_m1 rc H hptr GIOA) with (ccs := ccs) (PB' := PB') (hcs' := hcs'); try eassumption. exact (FIN6 e).
  Qed.
  End Sz5.
  #[using="FO fflagA GL SNPRINTF LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP"] Lemma ngn_snp_a0 : ltac:(let t := eval cbv delta [ngn_snp_a0__stmt] in ngn_snp_a0__stmt in exact t).
  Proof. intros ra' t0' t1' t2' x0 x1 a3' a4' a5' a6' a7' x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 RNG5 ps PB' p' h hcs' dw ccs FMTA fs args e. ltac2:(SecDiet.SzSec.closeP 'ngn_snp_a0__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngn_idb_tail__stmt : Prop := forall (LOOP : pcapT -> MR),
    ngn_headA (fun p' ps' RNG' ms' => implMG RNG' (mbind (LOOP p') ngn_KF) ps' POSTQ ms') ->
    forall (ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
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
      implMG RNG5 (mbind (let lt := get_le16 data 8 in
                          let sl := get_le32 data 12 in
                          if negb (linktype =? lt) then mret (inl (-1)%Z, set_errbuf (Msg.iface_type_differs lt) (pv bq alloc data eb sx ix))
                          else if negb (snapshot =? pcapint_adjust_snapshot linktype sl) then mret (inl (-1)%Z, set_errbuf (Msg.iface_snaplen_differs sl) (pv bq alloc data eb sx ix))
                          else mbind (add_interface MOps (prims HO FO sites) (pv bq alloc data eb sx ix) 8 (mkCursor 16 (rem - 8) bt))
                                     (fun r => let '(ok, c, p, msg) := r in if ok then LOOP p else mret (inl (-1)%Z, set_errbuf msg p))) ngn_KF) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 (Z_to_bv 64 (Z.shiftr (Bq + 8) 3)) (Z_to_bv 64 0) a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) (Z_to_bv 64 (Bq + 12)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (P + 660))
                 (Z_to_bv 64 1) (Z_to_bv 64 168627466) (Z_to_bv 64 P) (Z_to_bv 64 Af) (Z_to_bv 64 (Bq + 8))
                 t3' t4' t5' t6') F (Z_to_bv 64 0x8cfd0) fc None m5 (seg_rom asegs)).
  Section Sz6.
  Variables LOOP ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m5 RNG5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw cpad : ltac2:(SecDiet.SzSec.tyM 'ngn_idb_tail__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @LOOP).
  #[using="rc tlsI fflagA GL SNPRINTF LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HLOC DLOC trC ADDIF ADJ GPL TR"] Lemma ngn_idb_tail__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_idb_tail__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros HLOOP.
 intros FP5 ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (rng_fp_le _ _ _ _ FP5 RSTK) as RSTK5.
    assert (RSPW : rng RNG5 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK5| lia]).
    pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    assert (HinP : In (self, P, 680%Z) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    assert (HinB : In (bq, Bq, alloc) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; right; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinP) as ((PBAND & P3 & PTOP & P2) & P1 & PUNP & PRNG & PRSH & PAR).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinB) as ((BBAND & B3 & BTOP & B2) & B1 & BUNP & BRNG & BRSH & BAR).
    cbn [cb_addr cb_size fst snd] in *.
    pose proof (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ G5 eq_refl) as [APB API].
    pose proof WF as (W1' & _ & W3 & W4 & _ & _ & _ & _ & W9' & _).
    unfold A3P.F_ngnEA.TwB.pv, pcap_blocks, psize, is_ng in EPB, APB. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, APB. unfold PCAP_NG_SF_TOTAL in APB.
    unfold A3P.F_ngnEA.TwB.pv in W3, W4, W1', W9'. cbn [pc_bufalloc pc_bufdata pc_snapshot pc_linktype] in W3, W4, W1', W9'. unfold INT_MAX in W1'.
    assert (EBX : Bx' = Bq) by congruence. subst Bx'.
    band_ind PBAND bP. band_ind BBAND bB.
    unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, A3P.F_ngnEA.TwB.pv in CELLS.
    cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_ng pk_cleanup_ng PK] in CELLS.
    unfold A3P.F_ngnEA.TwB.pv in BUF. cbn [pc_bufalloc] in BUF. cbn [pc_bufdata] in PFX.
    (* [comment removed for export] *)
    cbv zeta. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA.TwB.get_le16_q8' data 8) by lia. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.get_le32_q8 data 12) by lia.
    set (l0 := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data 8 0) in *. set (l1 := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data 8 1) in *.
    pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data 8 0 DRNG ltac:(lia)) as Rl0. pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data 8 1 DRNG ltac:(lia)) as Rl1. fold l0 in Rl0. fold l1 in Rl1.
    name_field data 12%Z n0 n1 n2 n3 DRNG.
    assert (LBS : length bsx' = Z.to_nat alloc) by (destruct BUF as [[WFB _] _]; cbn in WFB; lia).
    pose proof BUF as BUF0.
    apply (rw_cells_split_CB asegs m5 _ [] (Z.to_nat alloc) _ [] [8; 2; 2; 4; Z.to_nat alloc - 16]%nat) in BUF; [| cbn; lia]. cbn [mk_CB_cells app] in BUF.
    rewrite !skipn_skipn in BUF. cbn [Nat.add] in BUF.
    rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA.TwB.firstn2_q8 data bsx' 8 8 PFX eq_refl), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.firstn4_q8 data bsx' 12 12 PFX eq_refl) in BUF by lia. fold l0 l1 n0 n1 n2 n3 in BUF.
    assert (BUF4 : rw_cells asegs m5 Bq [CB 8 (firstn 8 bsx'); C2 (Z_to_bv 64 (l0 + 256 * l1)); CB 2 (firstn 2 (skipn 10 bsx')); C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); CB (Z.to_nat alloc - 16) (firstn (Z.to_nat alloc - 16) (skipn 16 bsx'))]).
    { eapply rw_cells_recell; [exact BUF | | ].
      { cbn. rewrite ?length_firstn, ?length_skipn. repeat split; try exact Logic.I; lia. }
      cbn [cells_bytes cbytes app]. rewrite (le2_lit l0 l1), (le4_lit n0 n1 n2 n3) by lia. reflexivity. }
    clear BUF.
    pose proof FR5 as FRJ. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_frameA in FRJ. cbn [app] in FRJ.
    pose proof (adjust_snapshot_range linktype (le4val n0 n1 n2 n3) ltac:(unfold le4val; lia)) as ADR. unfold INT_MAX in ADR.
    hide FR5. hide PRIV. hide IFS. hide HH. hide HD. hide BUF0.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    ienterG.
    ck0_at PUNP (P + 100)%Z; ck_go.
    zstep. if_false.   (* [comment removed for export] *)
    ck0_at BUNP (Bq + 8)%Z; ck_go.
    rewrite (sx32_small linktype) by lia.
    zstep. rewrite (zx16_lit (l0 + 256 * l1)) by lia.
    zstep. if_cases BR; zify_cond BR; rewrite ?unsigned_lit in BR by lia.
    - (* [comment removed for export] *)
      replace (linktype =? l0 + 256 * l1) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv iota.
      do 5 zstep.
      unhide FR5. unhide PRIV. unhide IFS. unhide HH. unhide HD. unhide BUF0.
      assert (MSG : fmt_at m5 0x229a0 "an interface has a type %u different from the type of the first interface"%string).
      { split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m5 0x229a0 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "an interface has a type %u different from the type of the first interface"%string) ++ [Z_to_bv 8 0])
                               MI5 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|].
        split; [lia|]. split; [cbn; lia|]. unfold client_globals. repeat (first [left; reflexivity | right]). }
      apply evtF_done. apply implMG_retb_l. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF.
      eapply ngn_snp_a0 with (fs := "an interface has a type %u different from the type of the first interface"%string) (args := [AInt (l0 + 256 * l1)%Z]) (PB' := pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) (hcs' := hcs);
        try eassumption;
        exit_sides ltac:(split; [exact FP5|]; split; [exact G5|]; split; [apply PCAPR_closable_of; exact PC5|]; split; [exact AG5|]; split; [exact HH|]; split; [exact Hh|];
                         split; [exact HD|]; split; [exact Hd| exact OF5]).
    - (* [comment removed for export] *)
      replace (linktype =? l0 + 256 * l1) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb]. cbv iota.
      do 4 zstep.   (* [comment removed for export] *)
      ck0_at PUNP (P + 96)%Z; ck_go.
      ck0 BUNP; ck_go.
      rewrite (sx32_small snapshot) by lia.
      zstep. rewrite (sx32_s32 (le4val n0 n1 n2 n3)) by (unfold le4val; lia).
      zstep.
      unhide FR5. unhide PRIV. unhide IFS. unhide HH. unhide HD. unhide BUF0.
      pose proof atop_range as AR.
      name_sp sp (-240)%Z.
      eapply evtF_cut;
        [ eapply (ADJ _ sp0) with (lo := lo) (lt := linktype) (snaplen := le4val n0 n1 n2 n3);
          [ assumption | rewrite Hsp; exact ST5 | reflexivity | lia | reflexivity | unfold le4val; lia ]
        | ].
      cbv beta. intros ms' PO. unfold leaf_post in PO. destruct_exs PO. destruct PO as (-> & MUc & WMc & MIc & STc & ->).
      rewrite Hsp in *.
      lazymatch type of MUc with munch _ _ ?mb => rename mb into m6 end.
      assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -240 - 0, bv_unsigned sp + -240)]%Z a) m5 m6) by (eapply agrees_on_of_munch; [exact MUc | exact WMc | intros a _ Ho; exact Ho]).
      assert (FW6 : Forall (pcap_iv FL (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) [(bv_unsigned sp + -240 - 0, bv_unsigned sp + -240)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]).
      assert (G6 : GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m6) by (eapply (gl_frame _ _ _ GL); [exact G5 | exact MUc | exact WMc | exact FW6]).
      assert (PC6 : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m6).
      { eapply PCAPR_agree; [exact AGS | | exact PC5]. intros a Ha.
        pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G5 ltac:(apply in_block_app; left; apply in_block_app; right; exact Ha)). cbn [outside fst snd]. lia. }
      assert (AG6 : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
      { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [| intros a [K _]; exact K].
        eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G5 | exact MUc | exact WMc | | lia].
        apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]. }
      transport_after_call asegs m5 m6 MUc WMc. clear MUc WMc MU WM.
      clear ST5. rename STc into ST5.
      unname_sp.
      replace (ret_pc (Z_to_bv 64 577592)) with (Z_to_bv 64 577592) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
      assert (FR6 : rw_cells asegs m6 (bv_unsigned sp + -240) (ngn_frameA [C8 (Z_to_bv 64 (Bq + 16)); C8 (Z_to_bv 64 (rem - 8)); C4 (Z_to_bv 64 bt); CB 4 cpad])) by exact FRJ.
      hide FR6. hide HH. hide HD. hide BUF0.
      zstep. if_cases BR2; zify_cond BR2; rewrite ?unsigned_lit in BR2 by lia.
      + (* [comment removed for export] *)
        replace (snapshot =? pcapint_adjust_snapshot linktype (le4val n0 n1 n2 n3)) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv iota.
        ck0_at BUNP (Bq + 12)%Z; ck_go.
        zstep. rewrite (sx32_lit n0 n1 n2 n3) by lia. do 4 zstep.
        unhide FR6. unhide HH. unhide HD. unhide BUF0.
        assert (MSG : fmt_at m6 0x22a20 "an interface has a snapshot length %u different from the snapshot length of the first interface"%string).
        { split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m6 0x22a20 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "an interface has a snapshot length %u different from the snapshot length of the first interface"%string) ++ [Z_to_bv 8 0])
                                 MIc ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|].
          split; [lia|]. split; [cbn; lia|]. unfold client_globals. repeat (first [left; reflexivity | right]). }
        apply evtF_done. apply implMG_retb_l. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF.
        eapply ngn_snp_a0 with (fs := "an interface has a snapshot length %u different from the snapshot length of the first interface"%string) (args := [AInt (sxv n0 n1 n2 n3)]) (PB' := pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) (hcs' := hcs);
          try eassumption;
          exit_sides ltac:(split; [exact FP5|]; split; [exact G6|]; split; [apply PCAPR_closable_of; exact PC6|]; split; [exact AG6|]; split; [exact HH|]; split; [exact Hh|];
                           split; [exact HD|]; split; [exact Hd| exact OF5]).
      + (* [comment removed for export] *)
        replace (snapshot =? pcapint_adjust_snapshot linktype (le4val n0 n1 n2 n3)) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb]. cbv iota.
        unhide FR6. unhide HH. unhide HD. unhide BUF0.
        apply evtF_done.
        eapply (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_ngnICA.TwB.ngn_idb_call rc tlsI H hptr HO FO sites GIOA TP fflagA GL) with (rem := rem) (hcs := hcs) (dw := dw); try eassumption.
  Qed.
  End Sz6.
  #[using="rc tlsI fflagA GL SNPRINTF LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HLOC DLOC trC ADDIF ADJ GPL TR"] Lemma ngn_idb_tail : ltac:(let t := eval cbv delta [ngn_idb_tail__stmt] in ngn_idb_tail__stmt in exact t).
  Proof. intros LOOP HLOOP ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m5 RNG5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw cpad. ltac2:(SecDiet.SzSec.closeP 'ngn_idb_tail__body "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngn_idb__stmt : Prop := forall (LOOP : pcapT -> MR),
    ngn_headA (fun p' ps' RNG' ms' => implMG RNG' (mbind (LOOP p') ngn_KF) ps' POSTQ ms') ->
    forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x11 t3' t4' t5' t6' : word) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (bt : Z) (hcs : list cell) (dw : cell) (cpad : list byte),
      fp_le RNG RNG5 ->
      stk asegs m5 lo (bv_unsigned sp + -240) ->
      rw_cells asegs m5 (bv_unsigned sp + -240) (ngn_frameA (ccells Bq rem bt cpad)) -> mem_inv asegs m5 ->
      GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells asegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells asegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (0 <= rem)%Z ->
      (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implMG RNG5 (mbind (ngn_idbK LOOP (mkCursor 8 rem bt) (pv bq alloc data eb sx ix)) ngn_KF) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216)) a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) (Z_to_bv 64 2) (Z_to_bv 64 2147450880) (Z_to_bv 64 (P + 660))
                 (Z_to_bv 64 1) (Z_to_bv 64 168627466) (Z_to_bv 64 P) (Z_to_bv 64 Af) x11
                 t3' t4' t5' t6') F (Z_to_bv 64 0x8cf18) fc None m5 (seg_rom asegs)).
  Section Sz7.
  Variables LOOP ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x11 t3' t4' t5' t6' m5 RNG5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw cpad : ltac2:(SecDiet.SzSec.tyM 'ngn_idb__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @LOOP).
  #[using="rc tlsI fflagA GL SNPRINTF LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HLOC DLOC trC ADDIF ADJ GPL TR"] Lemma ngn_idb__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_idb__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros HLOOP.
 intros FP5 ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (rng_fp_le _ _ _ _ FP5 RSTK) as RSTK5.
    assert (RSPW : rng RNG5 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK5| lia]).
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA.TwB.ngn_idbK, get_from_block_data. cbn [cur_remaining cur_off cur_block_type].
    change (pc_swapped (pv bq alloc data eb sx ix)) with swapped. change (pc_bufdata (pv bq alloc data eb sx ix)) with data.
    pose proof FR5 as FRJ. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_frameA, A3P.F_ngnEA.TwB.ccells in FRJ. cbn [app] in FRJ.
    hide FR5. hide HH. hide HD.
    pose proof (munch_refl [(bv_unsigned sp + -240 + 112, bv_unsigned sp + -240 + 128)]%Z m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    ienterG. zstep.
    zstep.
    zstep. if_cases BR0; zify_cond BR0; rewrite ?unsigned_lit in BR0 by lia.
    - (* [comment removed for export] *)
      replace (rem <? 8) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      do 5 zstep.
      unhide FR5. unhide HH. unhide HD. apply evtF_done. apply implMG_retb_l. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF.
      eapply (@A3P.F_ngnEA.TwB.ngn_snp_b8 rc tlsI H hptr FO GIOA fflagA GL SNPRINTF) with (fs := "block of type %u in pcapng dump file is too short"%string) (args := [AInt 1]) (PB' := pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix);
        try eassumption; [ reflexivity | | reflexivity | apply F_ngnSA_fmt_too_short; exact MI5 | reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity| constructor] ].
      split; [exact FP5|]. split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [exact Hh|].
      split; [exact HD|]. split; [exact Hd| exact OF5].
    - (* [comment removed for export] *)
      replace (rem <? 8) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota. cbv beta. change (8 + 8)%Z with 16%Z. change (8 + 4)%Z with 12%Z.
      change (pc_linktype (pv bq alloc data eb sx ix)) with linktype. change (pc_snapshot (pv bq alloc data eb sx ix)) with snapshot.
      pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
      pose proof G5 as G5e. rewrite EPB in G5e.
      assert (HinP : In (self, P, 680%Z) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
      assert (HinB : In (bq, Bq, alloc) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; right; left; reflexivity).
      pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinP) as ((PBAND & P3 & PTOP & P2) & P1 & PUNP & PRNG & PRSH & PAR).
      pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinB) as ((BBAND & B3 & BTOP & B2) & B1 & BUNP & BRNG & BRSH & BAR).
      cbn [cb_addr cb_size fst snd] in *.
      pose proof (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ G5 eq_refl) as [APB API].
      pose proof WF as (W1' & _ & W3 & W4 & _).
      unfold A3P.F_ngnEA.TwB.pv, pcap_blocks, psize, is_ng in EPB, APB. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, APB. unfold PCAP_NG_SF_TOTAL in APB.
      unfold A3P.F_ngnEA.TwB.pv in W3, W4, W1'. cbn [pc_bufalloc pc_bufdata pc_snapshot] in W3, W4, W1'. unfold INT_MAX in W1'.
      assert (EBX : Bx' = Bq) by congruence. subst Bx'.
      band_ind PBAND bP. band_ind BBAND bB.
      unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, A3P.F_ngnEA.TwB.pv in CELLS.
      cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_ng pk_cleanup_ng PK] in CELLS.
      unfold A3P.F_ngnEA.TwB.pv in BUF. cbn [pc_bufalloc] in BUF. cbn [pc_bufdata] in PFX.
      (* [comment removed for export] *)
      set (l0 := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data 8 0) in *. set (l1 := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data 8 1) in *. set (r0 := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data 10 0) in *. set (r1 := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data 10 1) in *.
      pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data 8 0 DRNG ltac:(lia)) as Rl0. pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data 8 1 DRNG ltac:(lia)) as Rl1.
      pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data 10 0 DRNG ltac:(lia)) as Rr0. pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data 10 1 DRNG ltac:(lia)) as Rr1.
      fold l0 in Rl0. fold l1 in Rl1. fold r0 in Rr0. fold r1 in Rr1.
      name_field data 12%Z n0 n1 n2 n3 DRNG.
      assert (LBS : length bsx' = Z.to_nat alloc) by (destruct BUF as [[WFB _] _]; cbn in WFB; lia).
      apply (rw_cells_split_CB asegs m5 _ [] (Z.to_nat alloc) _ [] [8; 2; 2; 4; Z.to_nat alloc - 16]%nat) in BUF; [| cbn; lia]. cbn [mk_CB_cells app] in BUF.
      rewrite !skipn_skipn in BUF. cbn [Nat.add] in BUF.
      rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA.TwB.firstn2_q8 data bsx' 8 8 PFX eq_refl), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA.TwB.firstn2_q8 data bsx' 10 10 PFX eq_refl), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.firstn4_q8 data bsx' 12 12 PFX eq_refl) in BUF by lia.
      fold l0 l1 r0 r1 n0 n1 n2 n3 in BUF.
      replace (firstn (Z.to_nat alloc - 16) (skipn 16 bsx')) with (skipn 16 bsx') in BUF by (symmetry; apply firstn_all2; rewrite length_skipn; lia).
      assert (BUF4 : rw_cells asegs m5 Bq [CB 8 (firstn 8 bsx'); C2 (Z_to_bv 64 (l0 + 256 * l1)); CB 2 [b8 r0; b8 r1]; C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); CB (Z.to_nat alloc - 16) (skipn 16 bsx')]).
      { eapply rw_cells_recell; [exact BUF | | ].
        { cbn. rewrite ?length_firstn, ?length_skipn. repeat split; try exact Logic.I; lia. }
        cbn [cells_bytes cbytes app]. rewrite (le2_lit l0 l1), (le4_lit n0 n1 n2 n3) by lia. reflexivity. }
      clear BUF.
      hide PRIV. hide IFS.
      (* [comment removed for export] *)
      do 3 zstep.
      zstep. if_cases G1; zify_cond G1. { exfalso. rewrite ?unsigned_lit in G1 by lia. lia. }   (* [comment removed for export] *)
      do 3 zstep.
      assert (AGF : agrees_on (fun a => outside [(bv_unsigned sp + -240 + 112, bv_unsigned sp + -240 + 128)]%Z a) m5 m1) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
      unhide FR5. unhide HH. unhide HD. unhide PRIV. unhide IFS. clear FR5.
      apply (agrees_rw_cells _ _ _ _ _ AGF) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside fst snd]; lia].
      apply (agrees_rw_cells _ _ _ _ _ AGF) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside fst snd]; lia].
      apply (agrees_rw_cells _ _ _ _ _ AGF) in PRIV; [| intros a Ha; pose proof (priv_cells_psize _ _ _ _ _ PRIV) as PZ; unfold psize, is_ng, A3P.F_ngnEA.TwB.pv, PCAP_PRIV_OFF, priv_cells in PZ, Ha; cbn [pc_priv] in PZ, Ha; unfold PCAP_NG_SF_TOTAL in PZ; cbn [outside fst snd]; lia].
      assert (FW6 : Forall (pcap_iv FL (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) [(bv_unsigned sp + -240 + 112, bv_unsigned sp + -240 + 128)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]).
      assert (G6 : GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m1) by (eapply (gl_frame _ _ _ GL); [exact G5 | exact MU | exact WM | exact FW6]).
      assert (PC6 : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m1).
      { eapply PCAPR_agree; [exact AGF | | exact PC5]. intros a Ha.
        pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G5 ltac:(apply in_block_app; left; apply in_block_app; right; exact Ha)). cbn [outside fst snd]. lia. }
      assert (AG6 : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m1).
      { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [| intros a [K _]; exact K].
        eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G5 | exact MU | exact WM | | lia].
        apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]. }
      clear MU WM AGF G5 PC5 AG5 IFS G5e.
      ck0_at PUNP (P + 56)%Z; ck_go.
      zstep. rewrite (sx32_small (Z.b2z swapped)) by (destruct swapped; cbn; lia).
      do 3 zstep.
      assert (L3 : Z.land (Bq + 8) 3 = 0%Z) by (change 3%Z with (Z.ones 2); rewrite Z.land_ones by lia; Z.div_mod_to_equations; lia). rewrite L3.
      assert (FR6 : rw_cells asegs m1 (bv_unsigned sp + -240) (ngn_frameA [C8 (Z_to_bv 64 (Bq + 16)); C8 (Z_to_bv 64 (rem - 8)); C4 (Z_to_bv 64 bt); CB 4 cpad])) by exact FRJ.
      zstep. if_cases BRS; zify_cond BRS.
      + (* [comment removed for export] *)
        lazymatch goal with |- context [if swapped then ?X else ?Y] => replace (if swapped then X else Y) with Y by (rewrite BRS; reflexivity) end.
        cbv zeta.
        change (pc_bufdata (pv bq alloc data eb sx ix)) with data.
        change (pc_linktype (pv bq alloc data eb sx ix)) with linktype. change (pc_snapshot (pv bq alloc data eb sx ix)) with snapshot.
        apply evtF_done.
        eapply (ngn_idb_tail LOOP HLOOP) with (rem := rem) (hcs := hcs) (dw := dw); try eassumption. lia.
      + (* [comment removed for export] *)
        zstep. if_false.   (* [comment removed for export] *)
        lazymatch goal with |- context [if swapped then ?X else ?Y] => replace (if swapped then X else Y) with X by (rewrite BRS; reflexivity) end.
        cbv zeta.
        change (set_bufdata (swap_field 4 12 (swap_field 2 8 data)) (pv bq alloc data eb sx ix)) with (pv bq alloc (swap_field 4 12 (swap_field 2 8 data)) eb sx ix).
        rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_chkD__S3.F_ngnextI.idb_swap_data' data) by lia. fold l0 l1 r0 r1 n0 n1 n2 n3.
        set (data' := firstn 8 data ++ [l1; l0; r0; r1; n3; n2; n1; n0] ++ skipn 16 data).
        change (pc_bufdata (pv bq alloc data' eb sx ix)) with data'.
        change (pc_linktype (pv bq alloc data' eb sx ix)) with linktype. change (pc_snapshot (pv bq alloc data' eb sx ix)) with snapshot.
        assert (FRC : rw_cells asegs m1 (bv_unsigned sp + -136) [C8 (Z_to_bv 64 65280)]).
        { lazymatch type of FRJ with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?tl) =>
            pose proof (proj2 (proj1 (rw_cells_app asegs m1 _ [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12] (c13 :: tl)) FRJ)) as X;
            pose proof (proj1 (proj1 (rw_cells_app asegs m1 _ [c13] tl) X)) as X2 end.
          cbn [cells_size csize Nat.add] in X2. replace (bv_unsigned sp + -240 + Z.of_nat 104) with (bv_unsigned sp + -136) in X2 by lia. exact X2. }
        assert (HinB2 : In (bq, Bq, alloc) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) by (right; left; reflexivity).
        destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G6 HLOC HinB2 ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kH & kHr & kH1 & kH2).
        destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G6 DLOC HinB2 ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kD & kDr & kD1 & kD2).
        cbn [cb_addr cb_size fst snd] in kH1, kH2, kD1, kD2.
        hide FR6. hide HH. hide HD. hide PRIV. hide CELLS.
        eapply evtF_cut.
        { eapply (ngn_idb_swapA RNG5 sp gp tp F fc lo) with (l0 := l0) (l1 := l1) (n0 := n0) (n1 := n1) (n2 := n2) (n3 := n3) (Bq := Bq) (alloc := alloc) (bB := bB);
            [repeat (apply Forall_cons; [lia|]); apply Forall_nil | exact BUF4 | exact FRC | assumption | exact LO | exact BU | lia | exact RSPW | exact BUNP | exact BTOP
            | lia | exact B2 | exact B1 | exact bBr | exact bBhi | exact bBlo | exact bBimg | exact BRNG | exact BRSH]. }
        cbv beta. intros ms' (a2v & a3v & a4v & lv & w4 & m7 & -> & MU7 & WM7 & MI7 & HB7 & E1 & E0).
        assert (AGP : agrees_on (fun a => outside [(Bq + 8, Bq + 16)]%Z a) m1 m7) by (eapply agrees_on_of_munch; [exact MU7 | exact WM7 | intros a _ Ho; exact Ho]).
        unhide FR6. unhide HH. unhide HD. unhide PRIV. unhide CELLS.
        lazymatch goal with STX : stk asegs m1 _ _ |- _ => pose proof (agrees_stk _ _ _ _ _ AGP STX ltac:(intros a Ha; cbn [outside fst snd]; lia)) as ST7 end.
        apply (agrees_rw_cells _ _ _ _ _ AGP) in FR6; [| intros a Ha; unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_frameA in Ha; rewrite !cells_size_app in Ha; cbn [outside fst snd cells_size csize Nat.add] in Ha |- *; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside fst snd]; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside fst snd]; lia].
        assert (FW7 : Forall (pcap_iv FL (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) [(Bq + 8, Bq + 16)]%Z).
        { apply Forall_cons; [|apply Forall_nil]. right; left. unfold iv_in_block, pcap_blocks. apply Exists_cons_tl. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold A3P.F_ngnEA.TwB.pv. cbn [pc_buffer pc_bufalloc]. lia. }
        assert (G7 : GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m7) by (eapply (gl_frame _ _ _ GL); [exact G6 | exact MU7 | exact WM7 | exact FW7]).
        (* [comment removed for export] *)
        assert (BUF7 : rw_cells asegs m7 Bq [CB (Z.to_nat alloc) (firstn 8 bsx' ++ [b8 l1; b8 l0; b8 r0; b8 r1; b8 n3; b8 n2; b8 n1; b8 n0] ++ skipn 16 bsx')]).
        { assert (R7 : rw_cells asegs m7 Bq [CB 8 (firstn 8 bsx'); C2 (Z_to_bv 64 (l1 + 256 * l0)); CB 2 [b8 r0; b8 r1]; C4 (Z_to_bv 64 (le4val n3 n2 n1 n0)); CB (Z.to_nat alloc - 16) (skipn 16 bsx')]).
          { eapply rw_cells_recell; [exact HB7 | | ].
            { cbn. rewrite ?length_firstn, ?length_skipn. repeat split; try exact Logic.I; lia. }
            cbn [cells_bytes cbytes app]. rewrite (le2_of_val lv l1 l0 l1), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.le4_word_mod32 w4 (le4val n3 n2 n1 n0) E0) by lia. rewrite (le2_lit l1 l0), (le4_lit n3 n2 n1 n0) by lia. reflexivity. }
          pose proof (rw_cells_merge asegs m7 Bq [] _ [] ltac:(rewrite app_nil_r; exact R7)) as R8.
          lazymatch type of R8 with rw_cells _ _ _ ([] ++ [CB ?n ?bs]) =>
            replace n with (Z.to_nat alloc) in R8 by (cbn [cells_size csize]; lia);
            cbn [app cells_bytes cbytes] in R8 end.
          rewrite (le2_lit l1 l0), (le4_lit n3 n2 n1 n0), app_nil_r in R8 by lia. exact R8. }
        assert (LEN' : length data' = length data).
        { subst data'. change (skipn 16 data) with (skipn (8 + length [l1; l0; r0; r1; n3; n2; n1; n0]) data). apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.splice_length. cbn [length]. lia. }
        assert (PFX7 : firstn (length data') (firstn 8 bsx' ++ [b8 l1; b8 l0; b8 r0; b8 r1; b8 n3; b8 n2; b8 n1; b8 n0] ++ skipn 16 bsx') = map b8 data').
        { subst data'. change ([b8 l1; b8 l0; b8 r0; b8 r1; b8 n3; b8 n2; b8 n1; b8 n0] ++ skipn 16 bsx') with (map b8 [l1; l0; r0; r1; n3; n2; n1; n0] ++ skipn (8 + length [l1; l0; r0; r1; n3; n2; n1; n0]) bsx').
          change ([l1; l0; r0; r1; n3; n2; n1; n0] ++ skipn 16 data) with ([l1; l0; r0; r1; n3; n2; n1; n0] ++ skipn (8 + length [l1; l0; r0; r1; n3; n2; n1; n0]) data).
          apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.splice_pfx; [exact PFX | cbn [length]; lia | lia]. }
        assert (HQ7 : forall a, (0 <= a < 2^64)%Z -> ~ (Bq <= a < Bq + alloc)%Z -> outside [(Bq + 8, Bq + 16)]%Z a) by (intros a _ Hn; cbn [outside fst snd]; lia).
        assert (PC7 : PCAPR (hptr:=hptr) P (pv bq alloc data' eb sx ix) (pcap_blocks (pv bq alloc data' eb sx ix) P Bq Ix) FB m7).
        { eapply (@A3P.F_ngnEA.TwB.PCAPR_bufdata rc tlsI H hptr FO GIOA fflagA GL) with (m5 := m1) (data := data) (Q := fun a => outside [(Bq + 8, Bq + 16)]%Z a);
            [exact G6 | exact PC6 | exact AGP | exact HQ7 | exact BUF7 | exact PFX7 | exact LEN']. }
        assert (G7' : GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data' eb sx ix) P Bq Ix) FB FL m7) by exact G7.
        assert (AG7 : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m7).
        { eapply agrees_on_trans; [exact AG6|]. eapply agrees_on_weaken; [| intros a [K _]; exact K].
          eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G6 | exact MU7 | exact WM7 | | lia].
          apply Forall_cons; [|apply Forall_nil]. right; left. unfold iv_in_block, pcap_blocks. apply Exists_cons_tl. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold A3P.F_ngnEA.TwB.pv. cbn [pc_buffer pc_bufalloc]. lia. }
        assert (DRNG' : Forall (fun x => 0 <= x < 256)%Z data').
        { subst data'. change (skipn 16 data) with (skipn (8 + length [l1; l0; r0; r1; n3; n2; n1; n0]) data). apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.splice_Forall; [exact DRNG|].
          repeat (apply Forall_cons; [lia|]). apply Forall_nil. }
        apply evtF_done.
        eapply (ngn_idb_tail LOOP HLOOP) with (rem := rem) (hcs := hcs) (dw := dw) (data := data');
          [exact FP5 | exact ST7 | exact FR6 | exact MI7 | exact G7' | exact PC7 | exact AG7 | exact HH | exact Hh | exact HD | exact Hd | exact DRNG'
          | rewrite LEN'; exact LEN | exact L30 | lia | exact Hbt | exact OF5].
  Qed.
  End Sz7.
  #[using="rc tlsI fflagA GL SNPRINTF LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HLOC DLOC trC ADDIF ADJ GPL TR"] Lemma ngn_idb : ltac:(let t := eval cbv delta [ngn_idb__stmt] in ngn_idb__stmt in exact t).
  Proof. intros LOOP HLOOP ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x11 t3' t4' t5' t6' m5 RNG5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw cpad. ltac2:(SecDiet.SzSec.closeP 'ngn_idb__body "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgnCtx.
End CANSEC1.
End TwB.
End F_ngnIA.

(* [comment removed for export] *)
Module F_ngnSA.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnKA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnEA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnEA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnS0A.
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
  Variable trC : list Z.
  Hypothesis TR : traces_pcap_ng_next_packet TP L (bv_unsigned ra) trC.

  Let POSTQ := next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CLc FB lo P HA DA m o.

  (* [comment removed for export] *)
  #[local] Abbreviation ngn_frameA := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_frameA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA).
  #[local] Abbreviation ngn_final := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_final GIOA sp L RNG CLc FB FL P HA DA m o).
  #[local] Abbreviation ngn_finalC := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_finalC GIOA sp L RNG CLc FB FL P HA DA m o).

  #[local] Abbreviation pcapT := (pcap hptr hptr).
  #[local] Abbreviation MR := (M (PState H hptr) ((Z + ng_found) * pcap hptr hptr)).
  #[local] Abbreviation pv := (F_ngnEA.pv self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).
  #[local] Abbreviation ngn_KF := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF H hptr).
  #[local] Abbreviation ngn_shbK := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA.ngn_shbK H hptr).
  #[local] Abbreviation ngn_headA := (F_ngnEA.ngn_headA GIOA TP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CLc FB FL lo P HA DA Af m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).

  #[using="Type"] Lemma implMG_retb_l : forall {St A B} RNGx (a : A) (k : A -> Monad.M St B) s Q ms, implMG RNGx (k a) s Q ms -> implMG RNGx (mbind (mret a) k) s Q ms.
  Proof. intros St A B RNGx a k s Q ms HH. exact HH. Qed.

  #[using="rc sp"] Lemma fmt_too_short : forall mx, mem_inv asegs mx -> fmt_at mx NGN_FMT_TOO_SHORT_A "block of type %u in pcapng dump file is too short"%string.
  Proof.
    intros mx MIx. unfold NGN_FMT_TOO_SHORT_A.
    split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs mx 0x22520 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "block of type %u in pcapng dump file is too short"%string) ++ [Z_to_bv 8 0])
                             MIx ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|].
    split; [lia|]. split; [cbn; lia|]. unfold client_globals. repeat (first [left; reflexivity | right]).
  Qed.

  Definition ng_reset (sx : pcap_ng_sf) : pcap_ng_sf := mkNg (ng_user_tsresol sx) (ng_max_blocksize sx) 0 (ng_ifaces_size sx) [].

  (* [comment removed for export] *)
  #[using="rc tlsI FO fflagA GL sp lo LO BU"] Lemma PCAPR_reset : forall (Lx : alayout) (RNGx : footprint) (ps : PState H hptr) (bq : hptr) (Bq Ix alloc : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr)
                             (m6 m7 : mem) (Afx B I : Z) (j : pcap_junk) (pad bs : list byte),
    GIOA Lx RNGx ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m6 ->
    In (f, Afx, FILE_BLOCK) FB ->
    pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix = pcap_blocks (pv bq alloc data eb sx ix) P B I ->
    rw_cells asegs m7 P (pcap_cells (pv bq alloc data eb sx ix) P B Afx j) ->
    rw_cells asegs m7 (P + 648) (ng_cells (ng_reset sx) I pad) ->
    rw_cells asegs m7 B [CB (Z.to_nat alloc) bs] -> firstn (length data) bs = map b8 data ->
    ifaces_ok (pv bq alloc data eb sx ix) I m6 ->
    agrees_on (fun a => outside [(P + 660, P + 664)]%Z a) m6 m7 ->
    pcap_wf (pv bq alloc data eb sx ix) ->
    PCAPR (hptr:=hptr) P (pv bq alloc data eb (ng_reset sx) ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m7.
  Proof.
    intros Lx RNGx ps bq Bq Ix alloc data eb sx ix m6 m7 Afx B I j pad bs G Hin EPB CELLS PRIV BUF PFX IFS AG WF.
    pose proof (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ G eq_refl) as [APB API].
    exists Afx. split; [exact Hin|]. exists B, I, j, pad, bs.
    split; [exact EPB|]. split; [exact CELLS|]. split; [exact PRIV|]. split; [exact BUF|]. split; [exact PFX|].
    split.
    - unfold ifaces_ok in IFS |- *. unfold F_ngnEA.pv in IFS, API |- *. cbn [pc_priv] in IFS, API |- *. destruct ix as [q|].
      + destruct IFS as (js & tail & Ljs & CE & E1 & E2 & E3 & E4).
        rewrite <- (app_nil_r [CB (Z.to_nat (40 * (ng_ifaces_size sx - ng_ifcount sx))) tail]), app_assoc in CE.
        apply (rw_cells_merge asegs m6 I [] _ []) in CE. cbn [app] in CE. rewrite cells_size_app, ifs_cells_size in CE by (rewrite length_rev; lia).
        cbn [cells_size csize Nat.add] in CE. rewrite length_rev in CE.
        destruct (API sx q eq_refl) as [X1 X2]. unfold psize, is_ng in X1. cbn [pc_priv] in X1. unfold PCAP_NG_SF_TOTAL in X1.
        pose proof EPB as EPB'. unfold pcap_blocks, F_ngnEA.pv, psize, is_ng in EPB'. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB'.
        injection EPB' as EB EI.
        exists [], (cells_bytes (ifs_cells (rev (ng_ifaces sx)) js ++ [CB (Z.to_nat (40 * (ng_ifaces_size sx - ng_ifcount sx))) tail])).
        unfold ng_reset. cbn [ng_ifaces ng_ifcount ng_ifaces_size length rev ifs_cells app Z.of_nat].
        split; [reflexivity|]. split.
        * replace (Z.to_nat (40 * (ng_ifaces_size sx - 0))) with (40 * length (ng_ifaces sx) + (Z.to_nat (40 * (ng_ifaces_size sx - ng_ifcount sx)) + 0))%nat by lia.
          eapply agrees_rw_cells; [exact AG | exact CE |]. intros a Ha. cbn [cells_size csize Nat.add outside fst snd] in Ha |- *. clear - Ha X1 E1 E2 E3 EI. lia.
        * split; [reflexivity|]. split; [lia|]. split; [lia| apply Forall_nil].
      + unfold ng_reset. cbn [ng_ifaces ng_ifcount ng_ifaces_size]. clear - IFS. tauto.
    - unfold pcap_wf, ng_reset, F_ngnEA.pv in WF |- *.
      cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor pc_linktype pc_linktype_ext pc_header pc_priv
           ng_user_tsresol ng_max_blocksize ng_ifcount ng_ifaces_size] in WF |- *.
      clear - WF. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="rc tlsI FO fflagA GL SNPRINTF LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP trC TR"] Lemma ngn_shb_tail : forall (LOOP : pcapT -> MR),
    ngn_headA (fun p' ps' RNG' ms' => implMG RNG' (mbind (LOOP p') ngn_KF) ps' POSTQ ms') ->
    forall (ra' t0' t1' t2' a1' a3' a4' a5' a6' a7' x11 t3' t4' t5' t6' aw : word) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (hcs : list cell) (dw : cell) (ccs : list cell),
      fp_le RNG RNG5 ->
      stk asegs m5 lo (bv_unsigned sp + -224) ->
      rw_cells asegs m5 (bv_unsigned sp + -224) (ngn_frameA ccs) -> cells_size ccs = 24%nat -> mem_inv asegs m5 ->
      GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells asegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells asegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (16 <= rem)%Z ->
      ps_outfile ps = o -> (bv_unsigned aw mod 2^32 = get_le32 data 8)%Z ->
      implMG RNG5 (mbind (let bom := get_le32 data 8 in
                          if bom =? BYTE_ORDER_MAGIC then
                            let major := get_le16 data 12 in
                            if negb (major =? 1) then mret (inl (-1)%Z, set_errbuf (Msg.unknown_major major) (pv bq alloc data eb sx ix))
                            else LOOP (set_ng (ng_reset sx) ix (pv bq alloc data eb sx ix))
                          else if bom =? BYTE_ORDER_MAGIC_SWAPPED then mret (inl (-1)%Z, set_errbuf Msg.sections_byte_order (pv bq alloc data eb sx ix))
                          else mret (inl (-1)%Z, set_errbuf Msg.bad_byte_order_magic (pv bq alloc data eb sx ix))) ngn_KF) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -224)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 2147450880)
                 (Z_to_bv 64 (Bq + 12)) a1' aw a3' a4' a5' a6' a7'
                 (Z_to_bv 64 2) (Z_to_bv 64 (P + 216)) (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) (Z_to_bv 64 (P + 660))
                 (Z_to_bv 64 1) (Z_to_bv 64 168627466) (Z_to_bv 64 P) (Z_to_bv 64 Af) x11
                 t3' t4' t5' t6') F (Z_to_bv 64 0x8cd54) fc None m5 (seg_rom asegs)).
  Proof.
    intros LOOP HLOOP. intros until ccs. intros FP5 ST5 FR5 Hccs MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM OF5 Haw.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (rng_fp_le _ _ _ _ FP5 RSTK) as RSTK5.
    assert (RSPW : rng RNG5 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK5| lia]).
    pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    assert (HinP : In (self, P, 680%Z) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    assert (HinB : In (bq, Bq, alloc) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; right; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinP) as ((PBAND & P3 & PTOP & P2) & P1 & PUNP & PRNG & PRSH & PAR).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinB) as ((BBAND & B3 & BTOP & B2) & B1 & BUNP & BRNG & BRSH & BAR).
    cbn [cb_addr cb_size fst snd] in *.
    pose proof (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ G5 eq_refl) as [APB API].
    pose proof WF as (W1' & _ & W3 & W4 & _).
    unfold F_ngnEA.pv, pcap_blocks, psize, is_ng in EPB, APB. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, APB. unfold PCAP_NG_SF_TOTAL in APB.
    unfold F_ngnEA.pv in W3, W4, W1'. cbn [pc_bufalloc pc_bufdata pc_snapshot] in W3, W4, W1'. unfold INT_MAX in W1'.
    assert (EBX : Bx' = Bq) by congruence. subst Bx'.
    band_ind PBAND bP. band_ind BBAND bB.
    unfold F_ngnEA.pv in Hin. cbn [pc_rfile] in Hin.
    unfold F_ngnEA.pv in BUF. cbn [pc_bufalloc] in BUF. cbn [pc_bufdata] in PFX.
    (* [comment removed for export] *)
    cbv zeta. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.get_le32_q8 data 8) in Haw |- * by lia. rewrite (get_le16_q8' data 12) by lia.
    name_field data 8%Z b0 b1 b2 b3 DRNG.
    set (k0 := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data 12 0) in *. set (k1 := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data 12 1) in *.
    pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data 12 0 DRNG ltac:(lia)) as Rk0. pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data 12 1 DRNG ltac:(lia)) as Rk1. fold k0 in Rk0. fold k1 in Rk1.
    pose proof BUF as BUF0.
    assert (LBS : length bsx' = Z.to_nat alloc) by (destruct BUF as [[WFB _] _]; cbn in WFB; lia).
    apply (rw_cells_split_CB asegs m5 _ [] (Z.to_nat alloc) _ [] [8; 4; 2; Z.to_nat alloc - 14]%nat) in BUF; [| cbn; lia]. cbn [mk_CB_cells app] in BUF.
    rewrite !skipn_skipn in BUF. cbn [Nat.add] in BUF.
    rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.firstn4_q8 data bsx' 8 8 PFX eq_refl), (firstn2_q8 data bsx' 12 12 PFX eq_refl) in BUF by lia.
    fold b0 b1 b2 b3 k0 k1 in BUF.
    assert (BUF4 : rw_cells asegs m5 Bq [CB 8 (firstn 8 bsx'); C4 (Z_to_bv 64 (le4val b0 b1 b2 b3)); C2 (Z_to_bv 64 (k0 + 256 * k1)); CB (Z.to_nat alloc - 14) (firstn (Z.to_nat alloc - 14) (skipn 14 bsx'))]).
    { eapply rw_cells_recell; [exact BUF | | ].
      { cbn. rewrite ?length_firstn, ?length_skipn. repeat split; try exact Logic.I; lia. }
      cbn [cells_bytes cbytes app]. rewrite (le4_lit b0 b1 b2 b3), (le2_lit k0 k1) by lia. reflexivity. }
    clear BUF.
    pose proof PRIV as PRIVJ. unfold priv_cells, F_ngnEA.pv, PCAP_PRIV_OFF in PRIVJ. cbn [pc_priv] in PRIVJ. unfold ng_cells in PRIVJ.
    pose proof FR5 as FRJ. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_frameA in FRJ. cbn [app] in FRJ.
    pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.sxu_range' (le4val b0 b1 b2 b3) ltac:(unfold le4val; lia)) as SR. pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.sxu_range (le4val b0 b1 b2 b3) ltac:(unfold le4val; lia)) as (_ & SX2 & SX3).
    hide FR5. hide CELLS. hide PRIV. hide IFS. hide HH. hide HD. hide BUF0.
    pose proof (munch_refl [(P + 660, P + 664)]%Z m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    ienterG.
    zstep. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.sextw_word aw (le4val b0 b1 b2 b3) Haw).
    zstep.
  zstep. if_cases BR; zify_cond BR; rewrite ?unsigned_lit in BR by lia.
  - (* [comment removed for export] *)
    assert (NB : le4val b0 b1 b2 b3 <> 439041101%Z) by (destruct (Z_lt_dec (le4val b0 b1 b2 b3) (2^31)); [rewrite SX2 in BR by lia; lia | lia]).
    unfold BYTE_ORDER_MAGIC. replace (le4val b0 b1 b2 b3 =? 439041101) with false by (symmetry; apply Z.eqb_neq; exact NB). cbv iota.
    zstep. zstep.
    zstep. if_cases BR3; zify_cond BR3; rewrite ?unsigned_lit in BR3 by lia.
    + (* [comment removed for export] *)
      assert (NS : le4val b0 b1 b2 b3 <> 1295788826%Z) by (destruct (Z_lt_dec (le4val b0 b1 b2 b3) (2^31)); [rewrite SX2 in BR3 by lia; lia | lia]).
      unfold BYTE_ORDER_MAGIC_SWAPPED. replace (le4val b0 b1 b2 b3 =? 1295788826) with false by (symmetry; apply Z.eqb_neq; exact NS). cbv iota.
      do 3 zstep.
      unhide FR5. unhide CELLS. unhide PRIV. unhide IFS. unhide HH. unhide HD. unhide BUF0.
      assert (SRC : bytes_at asegs m5 0x22b00 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.str_bytes "the file has a section with a bad byte order magic field"))
        by (exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m5 0x22b00 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.str_bytes "the file has a section with a bad byte order magic field") MI5 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))).
      apply evtF_done. apply implMG_retb_l. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF.
      eapply ngn_mcp with (PB' := pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) (hcs' := hcs); try eassumption;
        exit_sides ltac:(split; [exact FP5|]; split; [exact G5|]; split; [apply PCAPR_closable_of; exact PC5|]; split; [exact AG5|]; split; [exact HH|]; split; [exact Hh|];
                         split; [exact HD|]; split; [exact Hd| exact OF5]).
    + (* [comment removed for export] *)
      assert (ES : le4val b0 b1 b2 b3 = 1295788826%Z) by (destruct (Z_lt_dec (le4val b0 b1 b2 b3) (2^31)); [rewrite SX2 in BR3 by lia; lia | specialize (SX3 ltac:(lia)); lia]).
      unfold BYTE_ORDER_MAGIC_SWAPPED. replace (le4val b0 b1 b2 b3 =? 1295788826) with true by (symmetry; apply Z.eqb_eq; exact ES). cbv iota.
      do 4 zstep.
      unhide FR5. unhide CELLS. unhide PRIV. unhide IFS. unhide HH. unhide HD. unhide BUF0.
      assert (SRC : bytes_at asegs m5 0x22aa0 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.str_bytes "the file has sections with different byte orders"))
        by (exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m5 0x22aa0 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.str_bytes "the file has sections with different byte orders") MI5 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))).
      apply evtF_done. apply implMG_retb_l. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF.
      eapply ngn_mcp with (PB' := pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) (hcs' := hcs); try eassumption;
        exit_sides ltac:(split; [exact FP5|]; split; [exact G5|]; split; [apply PCAPR_closable_of; exact PC5|]; split; [exact AG5|]; split; [exact HH|]; split; [exact Hh|];
                         split; [exact HD|]; split; [exact Hd| exact OF5]).
  - (* [comment removed for export] *)
    assert (EB : le4val b0 b1 b2 b3 = 439041101%Z) by (destruct (Z_lt_dec (le4val b0 b1 b2 b3) (2^31)); [rewrite SX2 in BR by lia; lia | specialize (SX3 ltac:(lia)); lia]).
    unfold BYTE_ORDER_MAGIC. replace (le4val b0 b1 b2 b3 =? 439041101) with true by (symmetry; apply Z.eqb_eq; exact EB). cbv iota. cbv zeta.
    ck0 BUNP; ck_go.
    zstep. rewrite (zx16_lit (k0 + 256 * k1)) by lia.
    zstep. if_cases BR2; zify_cond BR2; rewrite ?unsigned_lit in BR2 by lia.
    + (* [comment removed for export] *)
      replace (k0 + 256 * k1 =? 1) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv iota.
      do 3 zstep.
      unhide FR5. unhide CELLS. unhide PRIV. unhide IFS. unhide HH. unhide HD. unhide BUF0.
      assert (MSG : fmt_at m5 0x22b60 "unknown pcapng savefile major version number %u"%string).
      { split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m5 0x22b60 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "unknown pcapng savefile major version number %u"%string) ++ [Z_to_bv 8 0])
                               MI5 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|].
        split; [lia|]. split; [cbn; lia|]. unfold client_globals. repeat (first [left; reflexivity | right]). }
      apply evtF_done. apply implMG_retb_l. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF.
      eapply ngn_snp_b8 with (fs := "unknown pcapng savefile major version number %u"%string) (args := [AInt (k0 + 256 * k1)%Z]) (PB' := pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) (hcs' := hcs);
        try eassumption;
        exit_sides ltac:(split; [exact FP5|]; split; [exact G5|]; split; [apply PCAPR_closable_of; exact PC5|]; split; [exact AG5|]; split; [exact HH|]; split; [exact Hh|];
                         split; [exact HD|]; split; [exact Hd| exact OF5]).
  + (* [comment removed for export] *)
    replace (k0 + 256 * k1 =? 1) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb]. cbv iota.
    ck0 PUNP; ck_go.
    zstep. zstep.
  assert (AGP : agrees_on (fun a => outside [(P + 660, P + 664)]%Z a) m5 m0) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
  unhide FR5. unhide CELLS. unhide PRIV. unhide IFS. unhide HH. unhide HD. unhide BUF0.
  apply (agrees_rw_cells _ _ _ _ _ AGP) in FR5; [| intros a Ha; unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_frameA in Ha; rewrite !cells_size_app in Ha; cbn [outside fst snd cells_size csize Nat.add] in *; rewrite Hccs in Ha; lia].
  apply (agrees_rw_cells _ _ _ _ _ AGP) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside fst snd]; lia].
  apply (agrees_rw_cells _ _ _ _ _ AGP) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside fst snd]; lia].
  apply (agrees_rw_cells _ _ _ _ _ AGP) in CELLS; [| intros a Ha; rewrite pcap_cells_gen_size in Ha by reflexivity; cbn [outside fst snd]; lia].
  apply (agrees_rw_cells _ _ _ _ _ AGP) in BUF0; [| intros a Ha; cbn [outside fst snd cells_size csize Nat.add] in Ha |- *; lia].
  assert (FW6 : Forall (pcap_iv FL (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) [(P + 660, P + 664)]%Z).
  { apply Forall_cons; [|apply Forall_nil]. right; left. unfold iv_in_block, pcap_blocks. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold psize, is_ng, F_ngnEA.pv. cbn [pc_priv]. unfold PCAP_NG_SF_TOTAL. lia. }
  assert (G6 : GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m0) by (eapply (gl_frame _ _ _ GL); [exact G5 | exact MU | exact WM | exact FW6]).
  assert (PC6 : PCAPR (hptr:=hptr) P (pv bq alloc data eb (ng_reset sx) ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m0).
  { eapply (PCAPR_reset _ _ ps bq Bq Ix alloc data eb sx ix m5 m0 Afx Bq Ix' jx' padx bsx');
      [exact G5 | exact Hin | exact EPB | exact CELLS | exact PRIVJ | exact BUF0 | exact PFX | exact IFS | exact AGP | exact WF]. }
  assert (AG6 : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m0).
  { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [| intros a [K _]; exact K].
    eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G5 | exact MU | exact WM | | lia].
    apply Forall_cons; [|apply Forall_nil]. right; left. unfold iv_in_block, pcap_blocks. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold psize, is_ng, F_ngnEA.pv. cbn [pc_priv]. unfold PCAP_NG_SF_TOTAL. lia. }
  assert (G6' : GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb (ng_reset sx) ix) P Bq Ix) FB FL m0) by exact G6.
  assert (PC6' : PCAPR (hptr:=hptr) P (pv bq alloc data eb (ng_reset sx) ix) (pcap_blocks (pv bq alloc data eb (ng_reset sx) ix) P Bq Ix) FB m0) by exact PC6.
  apply evtF_done.
  change (set_ng (ng_reset sx) ix (pv bq alloc data eb sx ix)) with (pv bq alloc data eb (ng_reset sx) ix).
  unfold F_ngnEA.ngn_headA in HLOOP. unfold NGN_LOOP_A in HLOOP.
  eapply HLOOP; [exact FP5 | exact ST5 | exact FR5 | exact Hccs | assumption | exact G6' | exact PC6' | exact AG6 | exact HH | exact Hh | exact HD | exact Hd | exact OF5 | apply (F_ngnEA.ngn_ucx_m1 TP sp L lo LO BU SPT); exact (proj1 (proj2 TR))].
  Qed.

  #[using="rc tlsI FO fflagA GL SNPRINTF LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HLOC DLOC trC TR"] Lemma ngn_shb : forall (LOOP : pcapT -> MR),
    ngn_headA (fun p' ps' RNG' ms' => implMG RNG' (mbind (LOOP p') ngn_KF) ps' POSTQ ms') ->
    forall (ra' t0' t1' t2' a0' a1' a2' a4' a5' a6' a7' x11 t3' t4' t5' t6' : word) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (bt : Z) (hcs : list cell) (dw : cell) (cpad : list byte),
      fp_le RNG RNG5 ->
      stk asegs m5 lo (bv_unsigned sp + -224) ->
      rw_cells asegs m5 (bv_unsigned sp + -224) (ngn_frameA (ccells Bq rem bt cpad)) -> mem_inv asegs m5 ->
      GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells asegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells asegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (0 <= rem)%Z ->
      (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implMG RNG5 (mbind (ngn_shbK LOOP (mkCursor 8 rem bt) (pv bq alloc data eb sx ix)) ngn_KF) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -224)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 2147450880) a0' a1' a2' (Z_to_bv 64 (s32 bt)) a4' a5' a6' a7'
                 (Z_to_bv 64 2) (Z_to_bv 64 (P + 216)) (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) (Z_to_bv 64 (P + 660))
                 (Z_to_bv 64 1) (Z_to_bv 64 168627466) (Z_to_bv 64 P) (Z_to_bv 64 Af) x11
                 t3' t4' t5' t6') F (Z_to_bv 64 0x8cca8) fc None m5 (seg_rom asegs)).
  Proof.
    intros LOOP HLOOP. intros until cpad. intros FP5 ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (rng_fp_le _ _ _ _ FP5 RSTK) as RSTK5.
    assert (RSPW : rng RNG5 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK5| lia]).
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA.ngn_shbK, get_from_block_data. cbn [cur_remaining cur_off cur_block_type].
    change (pc_swapped (pv bq alloc data eb sx ix)) with swapped. change (pc_bufdata (pv bq alloc data eb sx ix)) with data.
    pose proof FR5 as FRJ. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_frameA, F_ngnEA.ccells in FRJ. cbn [app] in FRJ.
    hide FR5. hide HH. hide HD.
    pose proof (munch_refl [(bv_unsigned sp + -224 + 96, bv_unsigned sp + -224 + 112)]%Z m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    ienterG. zstep.
    zstep.
  zstep. if_cases BR0; zify_cond BR0; rewrite ?unsigned_lit in BR0 by lia.
  - (* [comment removed for export] *)
    replace (rem <? 16) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
    do 6 zstep.
    unhide FR5. unhide HH. unhide HD. apply evtF_done. apply implMG_retb_l. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF.
    eapply ngn_snp_b8 with (fs := "block of type %u in pcapng dump file is too short"%string) (args := [AInt 168627466]) (PB' := pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix);
      try eassumption; [ reflexivity | | reflexivity | apply fmt_too_short; exact MI5 | reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity| constructor] ].
    split; [exact FP5|]. split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [exact Hh|].
    split; [exact HD|]. split; [exact Hd| exact OF5].
  - (* [comment removed for export] *)
    replace (rem <? 16) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota. cbv beta.
    pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof G5 as G5e. rewrite EPB in G5e.
    assert (HinP : In (self, P, 680%Z) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    assert (HinB : In (bq, Bq, alloc) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; right; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinP) as ((PBAND & P3 & PTOP & P2) & P1 & PUNP & PRNG & PRSH & PAR).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinB) as ((BBAND & B3 & BTOP & B2) & B1 & BUNP & BRNG & BRSH & BAR).
    cbn [cb_addr cb_size fst snd] in *.
    pose proof (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ G5 eq_refl) as [APB API].
    pose proof WF as (W1' & _ & W3 & W4 & _).
    unfold F_ngnEA.pv, pcap_blocks, psize, is_ng in EPB, APB. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, APB. unfold PCAP_NG_SF_TOTAL in APB.
    unfold F_ngnEA.pv in W3, W4, W1'. cbn [pc_bufalloc pc_bufdata pc_snapshot] in W3, W4, W1'. unfold INT_MAX in W1'.
    assert (EBX : Bx' = Bq) by congruence. subst Bx'.
    band_ind PBAND bP. band_ind BBAND bB.
    unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, F_ngnEA.pv in CELLS.
    cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_ng pk_cleanup_ng PK] in CELLS.
    unfold F_ngnEA.pv in BUF. cbn [pc_bufalloc] in BUF. cbn [pc_bufdata] in PFX.
    (* [comment removed for export] *)
    name_field data 8%Z g0 g1 g2 g3 DRNG.
    set (j0 := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data 12 0) in *. set (j1 := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data 12 1) in *.
    pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data 12 0 DRNG ltac:(lia)) as Rj0. pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data 12 1 DRNG ltac:(lia)) as Rj1. fold j0 in Rj0. fold j1 in Rj1.
    assert (LBS : length bsx' = Z.to_nat alloc) by (destruct BUF as [[WFB _] _]; cbn in WFB; lia).
    apply (rw_cells_split_CB asegs m5 _ [] (Z.to_nat alloc) _ [] [8; 4; 2; Z.to_nat alloc - 14]%nat) in BUF; [| cbn; lia]. cbn [mk_CB_cells app] in BUF.
    rewrite !skipn_skipn in BUF. cbn [Nat.add] in BUF.
    rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.firstn4_q8 data bsx' 8 8 PFX eq_refl), (firstn2_q8 data bsx' 12 12 PFX eq_refl) in BUF by lia.
    fold g0 g1 g2 g3 j0 j1 in BUF.
    replace (firstn (Z.to_nat alloc - 14) (skipn 14 bsx')) with (skipn 14 bsx') in BUF by (symmetry; apply firstn_all2; rewrite length_skipn; lia).
    assert (BUF4 : rw_cells asegs m5 Bq [CB 8 (firstn 8 bsx'); C4 (Z_to_bv 64 (le4val g0 g1 g2 g3)); C2 (Z_to_bv 64 (j0 + 256 * j1)); CB (Z.to_nat alloc - 14) (skipn 14 bsx')]).
    { eapply rw_cells_recell; [exact BUF | | ].
      { cbn. rewrite ?length_firstn, ?length_skipn. repeat split; try exact Logic.I; lia. }
      cbn [cells_bytes cbytes app]. rewrite (le4_lit g0 g1 g2 g3), (le2_lit j0 j1) by lia. reflexivity. }
    clear BUF.
    hide PRIV. hide IFS.
    (* [comment removed for export] *)
    do 5 zstep.
    assert (AGF : agrees_on (fun a => outside [(bv_unsigned sp + -224 + 96, bv_unsigned sp + -224 + 112)]%Z a) m5 m1) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
    unhide FR5. unhide HH. unhide HD. unhide PRIV. unhide IFS. clear FR5.
    apply (agrees_rw_cells _ _ _ _ _ AGF) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside fst snd]; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGF) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside fst snd]; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGF) in PRIV; [| intros a Ha; pose proof (priv_cells_psize _ _ _ _ _ PRIV) as PZ; unfold psize, is_ng, F_ngnEA.pv, PCAP_PRIV_OFF, priv_cells in PZ, Ha; cbn [pc_priv] in PZ, Ha; unfold PCAP_NG_SF_TOTAL in PZ; cbn [outside fst snd]; lia].
    assert (FW6 : Forall (pcap_iv FL (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) [(bv_unsigned sp + -224 + 96, bv_unsigned sp + -224 + 112)]%Z)
      by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]).
    assert (G6 : GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m1) by (eapply (gl_frame _ _ _ GL); [exact G5 | exact MU | exact WM | exact FW6]).
    assert (PC6 : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m1).
    { eapply PCAPR_agree; [exact AGF | | exact PC5]. intros a Ha.
      pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G5 ltac:(apply in_block_app; left; apply in_block_app; right; exact Ha)). cbn [outside fst snd]. lia. }
    assert (IFS6 : ifaces_ok (pv bq alloc data eb sx ix) Ix' m1).
    { eapply ifaces_ok_agree; [exact AGF | | exact IFS]. intros sg q Hq a Ha. unfold F_ngnEA.pv in Hq. cbn [pc_priv] in Hq. injection Hq as E1 E2. subst sg ix.
      assert (HinI : In (q, Ix', (40 * ng_ifaces_size sx)%Z) ((CLc ++ pcap_blocks (pv bq alloc data eb sx (Some q)) P Bq Ix') ++ FB))
        by (apply in_or_app; left; apply in_or_app; right; right; right; left; reflexivity).
      pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5e HinI) as ((_ & _ & ITOP & _) & I1 & _). cbn [cb_addr cb_size fst snd] in ITOP, I1. cbn [outside fst snd]. lia. }
    assert (AG6 : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m1).
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [| intros a [K _]; exact K].
      eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G5 | exact MU | exact WM | | lia].
      apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]. }
    clear MU WM AGF G5 PC5 AG5 IFS G5e.
    zstep. if_cases BRZ; zify_cond BRZ. { exfalso. rewrite ?unsigned_lit in BRZ by lia. lia. }
    ck0_at PUNP (P + 56)%Z; ck_go.
    ck0 BUNP; ck_go.
  rewrite (sx32_small (Z.b2z swapped)) by (destruct swapped; cbn; lia).
  zstep. rewrite (sx32_lit g0 g1 g2 g3) by lia.
  zstep.
  assert (FR6 : rw_cells asegs m1 (bv_unsigned sp + -224) (ngn_frameA [C8 (Z_to_bv 64 (Bq + 24)); C8 (Z_to_bv 64 (rem + -16)); C4 (Z_to_bv 64 bt); CB 4 cpad])) by exact FRJ.
  zstep. if_cases BRS; zify_cond BRS.
    + (* [comment removed for export] *)
      lazymatch goal with |- context [if swapped then ?X else ?Y] => replace (if swapped then X else Y) with Y by (rewrite BRS; reflexivity) end.
      cbv zeta.
      change (ng_of (pv bq alloc data eb sx ix)) with sx. change (ng_ifaces_ptr_of (pv bq alloc data eb sx ix)) with ix.
      change (pc_bufdata (pv bq alloc data eb sx ix)) with data. fold (ng_reset sx).
      apply evtF_done.
  eapply (ngn_shb_tail LOOP HLOOP) with (aw := Z_to_bv 64 (sxv g0 g1 g2 g3)) (rem := rem) (hcs := hcs) (dw := dw);
          [exact FP5 | assumption | exact FR6 | reflexivity | assumption | exact G6 | exact PC6 | exact AG6 | exact HH | exact Hh | exact HD | exact Hd | exact DRNG
          | exact LEN | exact L30 | lia | exact OF5 | rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.get_le32_q8 data 8) by lia; fold g0 g1 g2 g3; rewrite unsigned_lit by (unfold sxv, le4val; Z.div_mod_to_equations; lia); apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.sxv_mod32; lia].
    + (* [comment removed for export] *)
      lazymatch goal with |- context [if swapped then ?X else ?Y] => replace (if swapped then X else Y) with X by (rewrite BRS; reflexivity) end.
      cbv zeta.
      change (set_bufdata (swap_field 2 12 (swap_field 4 8 data)) (pv bq alloc data eb sx ix)) with (pv bq alloc (swap_field 2 12 (swap_field 4 8 data)) eb sx ix).
      rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.shb_swap_data' data) by lia. fold g0 g1 g2 g3 j0 j1.
      set (data' := firstn 8 data ++ [g3; g2; g1; g0; j1; j0] ++ skipn 14 data).
      change (ng_of (pv bq alloc data' eb sx ix)) with sx. change (ng_ifaces_ptr_of (pv bq alloc data' eb sx ix)) with ix.
      change (pc_bufdata (pv bq alloc data' eb sx ix)) with data'. fold (ng_reset sx).
      assert (FRC : rw_cells asegs m1 (bv_unsigned sp + -136) [C8 (Z_to_bv 64 65280)]).
      { lazymatch type of FRJ with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?tl) =>
          pose proof (proj2 (proj1 (rw_cells_app asegs m1 _ [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10] (c11 :: tl)) FRJ)) as X;
          pose proof (proj1 (proj1 (rw_cells_app asegs m1 _ [c11] tl) X)) as X2 end.
        cbn [cells_size csize Nat.add] in X2. replace (bv_unsigned sp + -224 + Z.of_nat 88) with (bv_unsigned sp + -136) in X2 by lia. exact X2. }
      assert (HinB2 : In (bq, Bq, alloc) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) by (right; left; reflexivity).
      destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G6 HLOC HinB2 ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kH & kHr & kH1 & kH2).
      destruct (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G6 DLOC HinB2 ltac:(lia) ltac:(cbn [cb_size snd]; lia)) as (kD & kDr & kD1 & kD2).
      cbn [cb_addr cb_size fst snd] in kH1, kH2, kD1, kD2.
      hide FR6. hide HH. hide HD. hide PRIV. hide CELLS.
      eapply evtF_cut.
      { eapply (ngn_shb_swapA RNG5 sp gp tp F fc lo) with (g0 := g0) (g1 := g1) (g2 := g2) (g3 := g3) (j0 := j0) (j1 := j1) (Bq := Bq) (alloc := alloc) (bB := bB);
          [repeat (apply Forall_cons; [lia|]); apply Forall_nil | exact BUF4 | exact FRC | assumption | exact LO | exact BU | lia | exact RSPW | exact BUNP | exact BTOP
          | lia | exact B2 | exact B1 | exact bBr | exact bBhi | exact bBlo | exact bBimg | exact BRNG | exact BRSH]. }
      cbv beta. intros ms' (a1v & a2v & a3v & a4v & m7 & -> & MU7 & WM7 & MI7 & HB7 & E1 & E2).
  assert (AGP : agrees_on (fun a => outside [(Bq + 8, Bq + 14)]%Z a) m1 m7) by (eapply agrees_on_of_munch; [exact MU7 | exact WM7 | intros a _ Ho; exact Ho]).
        unhide FR6. unhide HH. unhide HD. unhide PRIV. unhide CELLS.
        lazymatch goal with STX : stk asegs m1 _ _ |- _ => pose proof (agrees_stk _ _ _ _ _ AGP STX ltac:(intros a Ha; cbn [outside fst snd]; lia)) as ST7 end.
        apply (agrees_rw_cells _ _ _ _ _ AGP) in FR6; [| intros a Ha; unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_frameA in Ha; rewrite !cells_size_app in Ha; cbn [outside fst snd cells_size csize Nat.add] in Ha |- *; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside fst snd]; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside fst snd]; lia].
        assert (FW7 : Forall (pcap_iv FL (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) [(Bq + 8, Bq + 14)]%Z).
        { apply Forall_cons; [|apply Forall_nil]. right; left. unfold iv_in_block, pcap_blocks. apply Exists_cons_tl. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold F_ngnEA.pv. cbn [pc_buffer pc_bufalloc]. lia. }
        assert (G7 : GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m7) by (eapply (gl_frame _ _ _ GL); [exact G6 | exact MU7 | exact WM7 | exact FW7]).
  (* [comment removed for export] *)
        assert (BUF7 : rw_cells asegs m7 Bq [CB (Z.to_nat alloc) (firstn 8 bsx' ++ [b8 g3; b8 g2; b8 g1; b8 g0; b8 j1; b8 j0] ++ skipn 14 bsx')]).
        { assert (R7 : rw_cells asegs m7 Bq [CB 8 (firstn 8 bsx'); C4 (Z_to_bv 64 (le4val g3 g2 g1 g0)); C2 (Z_to_bv 64 (j1 + 256 * j0)); CB (Z.to_nat alloc - 14) (skipn 14 bsx')]).
          { eapply rw_cells_recell; [exact HB7 | | ].
            { cbn. rewrite ?length_firstn, ?length_skipn. repeat split; try exact Logic.I; lia. }
            cbn [cells_bytes cbytes app]. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.le4_word_mod32 a2v (le4val g3 g2 g1 g0) E1), (le2_of_val a1v j1 j0 j1) by lia. rewrite (le4_lit g3 g2 g1 g0), (le2_lit j1 j0) by lia. reflexivity. }
          pose proof (rw_cells_merge asegs m7 Bq [] _ [] ltac:(rewrite app_nil_r; exact R7)) as R8.
          lazymatch type of R8 with rw_cells _ _ _ ([] ++ [CB ?n ?bs]) =>
            replace n with (Z.to_nat alloc) in R8 by (cbn [cells_size csize]; lia);
            cbn [app cells_bytes cbytes] in R8 end.
          rewrite (le4_lit g3 g2 g1 g0), (le2_lit j1 j0), app_nil_r in R8 by lia. exact R8. }
        assert (LEN' : length data' = length data).
        { subst data'. change (skipn 14 data) with (skipn (8 + length [g3; g2; g1; g0; j1; j0]) data). apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.splice_length. cbn [length]. lia. }
        assert (PFX7 : firstn (length data') (firstn 8 bsx' ++ [b8 g3; b8 g2; b8 g1; b8 g0; b8 j1; b8 j0] ++ skipn 14 bsx') = map b8 data').
        { subst data'. change ([b8 g3; b8 g2; b8 g1; b8 g0; b8 j1; b8 j0] ++ skipn 14 bsx') with (map b8 [g3; g2; g1; g0; j1; j0] ++ skipn (8 + length [g3; g2; g1; g0; j1; j0]) bsx').
          change ([g3; g2; g1; g0; j1; j0] ++ skipn 14 data) with ([g3; g2; g1; g0; j1; j0] ++ skipn (8 + length [g3; g2; g1; g0; j1; j0]) data).
          apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.splice_pfx; [exact PFX | cbn [length]; lia | lia]. }
        assert (HQ7 : forall a, (0 <= a < 2^64)%Z -> ~ (Bq <= a < Bq + alloc)%Z -> outside [(Bq + 8, Bq + 14)]%Z a) by (intros a _ Hn; cbn [outside fst snd]; lia).
      assert (PC7 : PCAPR (hptr:=hptr) P (pv bq alloc data' eb sx ix) (pcap_blocks (pv bq alloc data' eb sx ix) P Bq Ix) FB m7).
      { eapply (@F_ngnEA.PCAPR_bufdata rc tlsI H hptr FO GIOA fflagA GL) with (m5 := m1) (data := data) (Q := fun a => outside [(Bq + 8, Bq + 14)]%Z a);
          [exact G6 | exact PC6 | exact AGP | exact HQ7 | exact BUF7 | exact PFX7 | exact LEN']. }
      assert (G7' : GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data' eb sx ix) P Bq Ix) FB FL m7) by exact G7.
      assert (AG7 : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m7).
      { eapply agrees_on_trans; [exact AG6|]. eapply agrees_on_weaken; [| intros a [K _]; exact K].
        eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G6 | exact MU7 | exact WM7 | | lia].
        apply Forall_cons; [|apply Forall_nil]. right; left. unfold iv_in_block, pcap_blocks. apply Exists_cons_tl. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold F_ngnEA.pv. cbn [pc_buffer pc_bufalloc]. lia. }
      assert (DRNG' : Forall (fun x => 0 <= x < 256)%Z data').
      { subst data'. change (skipn 14 data) with (skipn (8 + length [g3; g2; g1; g0; j1; j0]) data). apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.splice_Forall; [exact DRNG|].
        repeat (apply Forall_cons; [lia|]). apply Forall_nil. }
      apply evtF_done.
      eapply (ngn_shb_tail LOOP HLOOP) with (aw := a2v) (rem := rem) (hcs := hcs) (dw := dw);
        [exact FP5 | exact ST7 | exact FR6 | reflexivity | exact MI7 | exact G7' | exact PC7 | exact AG7 | exact HH | exact Hh | exact HD | exact Hd | exact DRNG'
        | rewrite LEN'; exact LEN | exact L30 | lia | exact OF5 | rewrite E1; subst data'; symmetry; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.shb_splice_le32; lia].
  Qed.
End NgnCtx.
End CANSEC1.
End F_ngnSA.

(* [comment removed for export] *)
Module F_ngnLA.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnKA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnEA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnE2A__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnTA F_ngnDA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnEA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_ngnE2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnIA__A3P.F_ngnSA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_ngnICA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnIA__A3P.F_ngnIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_ngnBA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnTA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnDA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
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

Lemma signed_lit_s32 : forall x, bv_signed (Z_to_bv 64 (s32 x)) = s32 x.
Proof.
  intros x. pose proof (s32_range x) as R. rewrite zb_signed, unsigned_lit_wrap.
  destruct (Z_lt_dec (s32 x) 0).
  - replace ((s32 x) mod 2^64)%Z with (s32 x + 2^64)%Z by (Z.div_mod_to_equations; lia).
    replace (s32 x + 2 ^ 64 <? 2 ^ 63)%Z with false by (symmetry; apply Z.ltb_ge; lia). lia.
  - rewrite Z.mod_small by lia. replace (s32 x <? 2 ^ 63)%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
Lemma s32_cases : forall x, (0 <= x < 2^32 -> (x < 2^31 /\ s32 x = x) \/ (2^31 <= x /\ s32 x = x - 2^32))%Z.
Proof. intros x Hx. unfold s32. destruct (Z_lt_dec x (2^31)); [left | right]; split; try lia; Z.div_mod_to_equations; lia. Qed.

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
  Hypothesis PP : post_process_stmt.
  Hypothesis OHA : cobjA RNG m FL CLc HA 24.
  Hypothesis ODA : cobjA RNG m FL CLc DA 8.
  Hypothesis HDA : (HA + 24 <= DA \/ DA + 8 <= HA)%Z.
  Hypothesis HA8 : (HA mod 8 = 0)%Z.
  Hypothesis DA8 : (DA mod 8 = 0)%Z.
  Hypothesis ADJ : adjust_snapshot_stmt.
  Hypothesis ADDIF : add_interface_stmt HO FO sites GIOA TP.
  Hypothesis RBLK : read_block_stmt HO FO sites GIOA TP.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis TR : traces_pcap_ng_next_packet TP L (bv_unsigned ra) trC.
  Hypothesis NF : nofr frames_pcap_ng_next_packet FL.

  #[local] Abbreviation pcapT := (pcap hptr hptr).
  #[local] Abbreviation MR := (M (PState H hptr) ((Z + ng_found) * pcap hptr hptr)).
  #[local] Abbreviation pv := (F_ngnEA.pv self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).
  #[local] Abbreviation ccells := (F_ngnEA.ccells).
  #[local] Abbreviation ngn_KF := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF H hptr).
  #[local] Abbreviation ngn_blkK := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA.ngn_blkK H hptr HO FO sites).
  #[local] Abbreviation ngn_body := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA.ngn_body H hptr HO FO sites).
  #[local] Abbreviation ngn_headA := (F_ngnEA.ngn_headA GIOA TP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CLc FB FL lo P HA DA Af m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).

  #[using="Type"] Lemma implMG_retb_l : forall {St A B} RNGx (a : A) (k : A -> Monad.M St B) s Q ms, implMG RNGx (k a) s Q ms -> implMG RNGx (mbind (mret a) k) s Q ms.
  Proof. intros St A B RNGx a k s Q ms HH. exact HH. Qed.

  Ltac decide_eqb :=
    repeat (match goal with
            | |- context [Z.eqb ?x ?k] => first [ replace (Z.eqb x k) with false by (symmetry; apply Z.eqb_neq; lia)
                                                | replace (Z.eqb x k) with true by (symmetry; apply Z.eqb_eq; lia) ]
            end; cbv iota).

  (* [comment removed for export] *)
  #[using="rc tlsI fflagA GL SNPRINTF LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HLOC DLOC trC PP OHA ODA HDA HA8 DA8 ADJ ADDIF GPL TR"] Lemma ngn_dispatch : forall (LOOP : pcapT -> MR),
    ngn_headA (fun p' ps' RNG' ms' => implMG RNG' (mbind (LOOP p') ngn_KF) ps' POSTQ ms') ->
    forall (t0' t1' t2' x0 a1' a2' a3' a4' a5' a6' a7' x11 t3' t4' t5' t6' : word) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (bt : Z) (hcs : list cell) (dw : cell) (cpad : list byte),
      fp_le RNG RNG5 ->
      stk asegs m5 lo (bv_unsigned sp + -224) ->
      rw_cells asegs m5 (bv_unsigned sp + -224) (ngn_frameA (ccells Bq rem bt cpad)) -> mem_inv asegs m5 ->
      GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells asegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells asegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (0 <= rem)%Z ->
      (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implMG RNG5 (mbind (ngn_blkK LOOP (mkCursor 8 rem bt) (pv bq alloc data eb sx ix)) ngn_KF) ps POSTQ
        (MS (mkR (Z_to_bv 64 0x8cc90) (Z_to_bv 64 (bv_unsigned sp + -224)) gp tp t0' t1' t2' x0 (Z_to_bv 64 2147450880) (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 2) (Z_to_bv 64 (P + 216)) (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) (Z_to_bv 64 (P + 660))
                 (Z_to_bv 64 1) (Z_to_bv 64 168627466) (Z_to_bv 64 P) (Z_to_bv 64 Af) x11
                 t3' t4' t5' t6') F (Z_to_bv 64 0x8cc90) fc None m5 (seg_rom asegs)).
  Proof.
    intros LOOP HLOOP. intros until cpad. intros FP5 ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (rng_fp_le _ _ _ _ FP5 RSTK) as RSTK5.
    assert (RSPW : rng RNG5 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK5| lia]).
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA.ngn_blkK. cbn [cur_block_type]. unfold BT_EPB, BT_SPB, BT_PB, BT_IDB, BT_SHB.
    pose proof (s32_cases bt Hbt) as SC.
    pose proof FR5 as FRJ. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_frameA, F_ngnEA.ccells in FRJ. cbn [app] in FRJ.
    hide FR5. hide HH. hide HD.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    ienterG.
    zstep. zstep.
  if_false.
  zstep. if_false.
  zstep. rewrite (sx32_s32 bt) by lia.
  zstep.
  if_cases B3; zify_cond B3; rewrite ?signed_lit_s32 in B3; rewrite ?signed_lit in B3 by lia.
    - (* [comment removed for export] *)
      zstep. if_cases B4; zify_cond B4; rewrite ?unsigned_lit_wrap in B4.
      + (* [comment removed for export] *)
        zstep. if_cases B5; zify_cond B5; rewrite ?unsigned_lit_wrap in B5.
        * (* [comment removed for export] *)
          assert (NB : (bt <> 1 /\ bt <> 2 /\ bt <> 3 /\ bt <> 6 /\ bt <> 168627466)%Z).
          { destruct SC as [[LT E]|[GE E]]; rewrite E in B3, B4, B5; [rewrite Z.mod_small in B4, B5 by lia; lia|]. lia. }
          decide_eqb.
          unhide FR5. unhide HH. unhide HD. apply evtF_done.
          unfold F_ngnEA.ngn_headA in HLOOP. unfold NGN_LOOP_A in HLOOP.
          eapply HLOOP; [exact FP5 | exact ST5 | exact FR5 | reflexivity | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact Hh | exact HD | exact Hd | exact OF5
                        | apply (F_ngnEA.ngn_ucx_m1 TP sp L lo LO BU SPT); exact (proj1 (proj2 TR))].
        * (* [comment removed for export] *)
          assert (EB : (bt = 2)%Z) by (destruct SC as [[LT E]|[GE E]]; rewrite E in B5; [rewrite Z.mod_small in B5 by lia; lia| exfalso; Z.div_mod_to_equations; lia]).
          decide_eqb. zstep.
          unhide FR5. unhide HH. unhide HD. apply evtF_done.
  subst POSTQ0. eapply F_ngnDA.ngn_pb; try eassumption.
      + (* [comment removed for export] *)
        assert (EB : (bt = 1)%Z) by (destruct SC as [[LT E]|[GE E]]; rewrite E in B4; [rewrite Z.mod_small in B4 by lia; lia| exfalso; Z.div_mod_to_equations; lia]).
        decide_eqb.
        unhide FR5. unhide HH. unhide HD. apply evtF_done.
        subst POSTQ0. eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnIA__A3P.F_ngnIA.ngn_idb; try eassumption.
    - (* [comment removed for export] *)
      assert (LT31 : (bt < 2^31 /\ s32 bt = bt)%Z) by (destruct SC as [[LT E]|[GE E]]; [split; [exact LT| exact E]| exfalso; rewrite E in B3; lia]).
      destruct LT31 as [LT31 E32]. rewrite E32 in B3.
      zstep. if_cases B6; zify_cond B6; rewrite ?E32, ?unsigned_lit in B6 by lia.
      + (* [comment removed for export] *)
        zstep. zstep. if_cases B7; zify_cond B7; rewrite ?E32, ?unsigned_lit in B7 by lia.
        * (* [comment removed for export] *)
          decide_eqb.
          unhide FR5. unhide HH. unhide HD. apply evtF_done.
          subst POSTQ0. eapply F_ngnDA.ngn_spb; try eassumption.
        * zstep. zstep. if_cases B8; zify_cond B8; rewrite ?E32, ?unsigned_lit in B8 by lia.
          -- (* [comment removed for export] *)
             decide_eqb.
             unhide FR5. unhide HH. unhide HD. apply evtF_done.
             unfold F_ngnEA.ngn_headA in HLOOP. unfold NGN_LOOP_A in HLOOP.
             eapply HLOOP; [exact FP5 | exact ST5 | exact FR5 | reflexivity | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact Hh | exact HD | exact Hd | exact OF5
                           | apply (F_ngnEA.ngn_ucx_m1 TP sp L lo LO BU SPT); exact (proj1 (proj2 TR))].
          -- (* [comment removed for export] *)
             decide_eqb. zstep.
             unhide FR5. unhide HH. unhide HD. apply evtF_done.
             subst POSTQ0. eapply F_ngnDA.ngn_epb; try eassumption.
      + (* [comment removed for export] *)
        decide_eqb.
        unhide FR5. unhide HH. unhide HD. apply evtF_done.
        subst POSTQ0. eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnIA__A3P.F_ngnSA.ngn_shb; try eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="rc tlsI fflagA GL SNPRINTF LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HinF HLOC DLOC trC PP OHA ODA HDA HA8 DA8 ADJ ADDIF RBLK GPL TR NF"] Lemma ngn_loop_S : forall (LOOP : pcapT -> MR),
    ngn_headA (fun p' ps' RNG' ms' => implMG RNG' (mbind (LOOP p') ngn_KF) ps' POSTQ ms') ->
    ngn_headA (fun p' ps' RNG' ms' => implMG RNG' (mbind (mbind (read_block MOps (prims HO FO sites) (DStack SiteBhdrNextPacket 0) p') (ngn_body LOOP)) ngn_KF) ps' POSTQ ms').
  Proof.
    intros LOOP HLOOP. unfold F_ngnEA.ngn_headA. intros until ccs. intros FP5 ST5 FR5 Hccs MI5 G5 PC5 AG5 HH Hh HD Hd OF5 UCX. unfold NGN_LOOP_A.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (rng_fp_le _ _ _ _ FP5 RSTK) as RSTK5.
    assert (RSPW : rng RNG5 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK5| lia]).
    (pose proof PC5 as ndP__; nd_pre ndP__ 3%nat; intros Afx Hin (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF); nd_post).
    pose proof G5 as G5e. rewrite EPB in G5e.
    assert (HinP : In (self, P, 680%Z) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    assert (HinB : In (bq, Bq, alloc) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; right; left; reflexivity).
    (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinP) as ndP__; nd_pre ndP__ 6%nat; intros (PBAND & P3 & PTOP & P2) P1 PUNP PRNG PRSH PAR; nd_post).
    (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinB) as ndP__; nd_pre ndP__ 6%nat; intros (BBAND & B3 & BTOP & B2) B1 BUNP BRNG BRSH BAR; nd_post).
    cbn [cb_addr cb_size fst snd] in *.
    pose proof (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ G5 eq_refl) as [APB API].
    pose proof WF as (W1' & W2' & W3 & W4 & W5' & W6' & W7' & W8' & W9' & W10' & W11 & W12 & W13 & W14).
    unfold F_ngnEA.pv, pcap_blocks, psize, is_ng in EPB, APB. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, APB. unfold PCAP_NG_SF_TOTAL in APB.
    unfold F_ngnEA.pv in W3, W4, W13, W14. cbn [pc_bufalloc pc_bufdata pc_priv pc_bufsize] in W3, W4, W13, W14.
    assert (EBX : Bx' = Bq) by congruence. subst Bx'.
    unfold F_ngnEA.pv in Hin. cbn [pc_rfile] in Hin.
    unfold F_ngnEA.pv in BUF. cbn [pc_bufalloc] in BUF. cbn [pc_bufdata] in PFX.
    pose proof PRIV as NG. unfold priv_cells, F_ngnEA.pv, PCAP_PRIV_OFF in NG. cbn [pc_priv] in NG. unfold ng_cells in NG.
    assert (INP : forall a, (P <= a < P + 680)%Z -> client_keeps FL ((CLc ++ [(self, P, PCAP_NG_SF_TOTAL)]) ++ IBLK ix Ix' sx) (bv_unsigned sp + -224) a).
    { intros a Ha. right. left. apply in_block_app. left. apply in_block_app. right. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. exact Ha. }
    (* [comment removed for export] *)
    apply pcap_cells_split4 in CELLS as (PRE & CE & HDR & OPS); [|reflexivity].
    apply (rw_cells_split_CB asegs m5 _ [] 304 _ [] [256; 48]%nat) in CE; [|reflexivity]. cbn [mk_CB_cells app] in CE.
    destruct (rw_cells_cut _ _ _ 1 CE) as [CE1 CE2]. clear CE. cbn [firstn skipn cells_size csize Nat.add] in CE1, CE2.
    replace (P + 216 + Z.of_nat 256)%Z with (P + 472)%Z in CE2 by lia.
    unfold pc_pre in PRE.
    destruct (rw_cells_cut _ _ _ 3 PRE) as [PRE0 PRE3]. destruct (rw_cells_cut _ _ _ 2 PRE3) as [P20 PRE5].
    destruct (rw_cells_cut _ _ _ 2 PRE5) as [P32 PRE7]. destruct (rw_cells_cut _ _ _ 2 PRE7) as [P48 PRE9]. clear PRE PRE3 PRE5 PRE7.
    cbn [firstn skipn cells_size csize Nat.add app] in PRE0, P20, P32, P48, PRE9.
    replace (P + Z.of_nat 20)%Z with (P + 20)%Z in P20 by lia. replace (P + Z.of_nat 20 + Z.of_nat 12)%Z with (P + 32)%Z in P32 by lia.
    replace (P + Z.of_nat 20 + Z.of_nat 12 + Z.of_nat 16)%Z with (P + 48)%Z in P48 by lia.
    replace (P + Z.of_nat 20 + Z.of_nat 12 + Z.of_nat 16 + Z.of_nat 12)%Z with (P + 60)%Z in PRE9 by lia.
    destruct (rw_cells_cut _ _ _ 1 NG) as [NG0 NG1]. destruct (rw_cells_cut _ _ _ 1 NG1) as [NG656 NGR]. clear NG NG1.
    cbn [firstn skipn cells_size csize Nat.add app] in NG0, NG656, NGR.
    replace (P + 648 + Z.of_nat 8)%Z with (P + 656)%Z in NG656 by lia. replace (P + 648 + Z.of_nat 8 + Z.of_nat 4)%Z with (P + 660)%Z in NGR by lia.
    (* [comment removed for export] *)
    pose proof FR5 as FRJ. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_frameA in FRJ.
    destruct (proj1 (rw_cells_app asegs m5 _ _ _) FRJ) as [F0 F4]. destruct (proj1 (rw_cells_app asegs m5 _ _ _) F4) as [FCUR FS]. clear FRJ F4.
    cbn [cells_size csize Nat.add] in FCUR, FS. rewrite Hccs in FS.
    replace (bv_unsigned sp + -224 + Z.of_nat 96)%Z with (bv_unsigned sp + -128)%Z in FCUR, FS by lia.
    replace (bv_unsigned sp + -128 + Z.of_nat 24)%Z with (bv_unsigned sp + -104)%Z in FS by lia.
    hide F0. hide FCUR. hide FS. hide PRE0. hide P20. hide P32. hide P48. hide PRE9. hide CE1. hide CE2. hide HDR. hide OPS. hide NG0. hide NG656. hide NGR. hide BUF. hide HH. hide HD. hide FR5. hide PRIV. hide IFS.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    apply implMG_bind_assoc. ienterG. do 4 zstep. zstep. clear MU WM.
    unhide F0. unhide FCUR. unhide FS. unhide PRE0. unhide P20. unhide P32. unhide P48. unhide PRE9. unhide CE1. unhide CE2. unhide HDR. unhide OPS. unhide NG0. unhide NG656. unhide NGR. unhide BUF. unhide HH. unhide HD. unhide FR5. unhide PRIV. unhide IFS.
    pose proof (rng_fp_le _ _ _ _ FP5 RIMG) as RIMG5. pose proof (rng_fp_le _ _ _ _ FP5 RISH) as RISH5. pose proof (rng_fp_le _ _ _ _ FP5 RTLS) as RTLS5.
    (nd_pre UCX 3%nat; intros trX TRX UCX; nd_post).
    apply evtF_done. name_sp sp (-224)%Z. eapply implMG_bind.
    { eapply RBLK with (L := L) (st := ps) (C1 := CLc ++ [(self, P, PCAP_NG_SF_TOTAL)]) (C2 := IBLK ix Ix' sx) (FB := FB) (FL := FL) (trC := trX) (f := f) (Af := Af) (P := P) (B := Bq)
                      (CUR := (bv_unsigned sp + -128)%Z) (EB := (P + 216)%Z) (lo := lo) (p := pv bq alloc data eb sx ix) (s := sx) (i := ix)
                      (a_bhdr := DStack SiteBhdrNextPacket 0) (bs := bsx') (ej := firstn 256 (pj_g jx')) (ccs := ccs).
      - split; [rewrite <- app_assoc; cbn [app]; pose proof G5e as GX; unfold pcap_blocks, F_ngnEA.pv, psize, is_ng in GX; cbn [pc_self pc_buffer pc_bufalloc pc_priv] in GX; unfold IBLK; exact GX |].
        split; [rewrite Hsp; exact ST5|]. split; [exact LO|]. split; [unfold READ_BLOCK_STACK, PCAP_L1_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [exact MI5|]. split; [exact TPE|]. split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|].
        split; [exact RSTK5|]. split; [exact RIMG5|]. split; [exact RISH5| exact RTLS5].
      - apply UCX. exact Hsp.
      - rewrite unsigned_lit by lia. exact TRX.
      - exact NF.
      - exact HinF.
      - reflexivity.
      - reflexivity.
      - apply in_or_app; left; apply in_or_app; right; left; reflexivity.
      - exists SiteBhdrNextPacket. split; [reflexivity| apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA.site_bhdr_frame].
      - reflexivity.
      - reflexivity.
      - f_equal; lia.
      - reflexivity.
      - split; [exact P20|]. split; [exact P48|]. split; [exact NG656|]. cbn [pc_bufsize pc_bufalloc F_ngnEA.pv]. unfold pcap_wf, F_ngnEA.pv in WF. cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_priv] in WF. lia.
      - exact BUF.
      - exact PFX.
      - cbn [pc_bufdata pc_bufalloc F_ngnEA.pv]; lia.
      - exact FCUR.
      - exact Hccs.
      - rewrite Hsp. split; lia.
      - clear - ALN. Z.div_mod_to_equations. lia.
      - exact CE1.
      - right; reflexivity.
      - clear - P2. Z.div_mod_to_equations. lia. }
    intros rb st' RNG6 ms' PO. cbv beta in PO.
    (nd_pre PO 23%nat; intros FP6 a0v m6 p' B' bs' E OF6 MI6 ST6 AG6 G6 BH6 BUF6 PFX6 LEN6 PRIVE RFE SELFE BSZE SWE META RM; nd_post).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 576656)) with (Z_to_bv 64 576656) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    destruct p' as [self' f' bsz' alloc' bq' data' sw' vmaj' vmin' snap' lt' lte' prec' brk' eb' hdr' priv'].
    cbn [pc_priv pc_rfile pc_self pc_bufsize pc_swapped F_ngnEA.pv] in PRIVE, RFE, SELFE, BSZE, SWE.
    unfold same_meta in META. cbn [pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header F_ngnEA.pv] in META.
    (nd_pre META 9%nat; intros M1 M2 M3 M4 M5 M6 M7 M8 M9; nd_post). subst priv' f' self' bsz' sw' vmaj' vmin' snap' lt' lte' prec' brk' eb' hdr'.
    change ({| pc_self := self; pc_rfile := f; pc_bufsize := bufsize; pc_bufalloc := alloc'; pc_buffer := bq'; pc_bufdata := data'; pc_swapped := swapped;
               pc_version_major := vmaj; pc_version_minor := vmin; pc_snapshot := snapshot; pc_linktype := linktype; pc_linktype_ext := ltext;
               pc_tstamp_precision := prec; pc_break_loop := brk; pc_errbuf := eb; pc_header := header; pc_priv := PrivNg sx ix |})
      with (pv bq' alloc' data' eb sx ix) in *.
    cbn [pc_buffer pc_bufalloc pc_bufdata F_ngnEA.pv] in G6, BUF6, PFX6, LEN6, RM.
    (nd_pre BH6 7%nat; intros P20' P48' NG656' BR1 BR2 BR3 BR4; nd_post). cbn [pc_bufsize pc_swapped pc_bufalloc F_ngnEA.pv] in P20', P48', BR1, BR3, BR4.
    assert (OF7 : ps_outfile st' = o) by (rewrite OF6; exact OF5).
    assert (FP7 : fp_le RNG RNG6) by (eapply fp_le_trans; [exact FP5 | exact FP6]).
    pose proof atop_range as AR.
    assert (HLOC' : clocA FL ((CLc ++ [(self, P, PCAP_NG_SF_TOTAL)]) ++ IBLK ix Ix' sx) HA 24) by (eapply clocA_incl; [exact HLOC | rewrite <- app_assoc; apply incl_appl, incl_refl | apply incl_refl]).
    assert (DLOC' : clocA FL ((CLc ++ [(self, P, PCAP_NG_SF_TOTAL)]) ++ IBLK ix Ix' sx) DA 8) by (eapply clocA_incl; [exact DLOC | rewrite <- app_assoc; apply incl_appl, incl_refl | apply incl_refl]).
    (* [comment removed for export] *)
    transport F0 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; lia| lia]).
    transport FS m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; lia| lia]).
    transport HH m6 AG6 ltac:(intros a Ha; rewrite Hh in Ha; split; [eapply clocA_keeps; [exact HLOC'| lia]| lia]).
    transport HD m6 AG6 ltac:(intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; split; [eapply clocA_keeps; [exact DLOC'| lia]| lia]).
    transport PRE0 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; lia| lia]).
    transport P32 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; lia| lia]).
    transport PRE9 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; lia| lia]).
    transport CE2 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; lia| lia]).
    transport HDR m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add hdr_cells pc_header F_ngnEA.pv] in Ha; split; [apply INP; lia| lia]).
    transport OPS m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add pc_ops] in Ha; split; [apply INP; lia| lia]).
    transport NG0 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; lia| lia]).
    transport NGR m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; lia| lia]).
    assert (IFS6 : ifaces_ok (pv bq' alloc' data' eb sx ix) Ix' m6).
    { eapply ifaces_ok_agree; [exact AG6 | | exact IFS]. intros sg q Hq a Ha. unfold F_ngnEA.pv in Hq. cbn [pc_priv] in Hq. injection Hq as E1 E2. subst sg ix.
      destruct (API sx q eq_refl) as [X1 X2]. unfold psize, is_ng, F_ngnEA.pv in X1. cbn [pc_priv] in X1. unfold PCAP_NG_SF_TOTAL in X1.
      assert (EI : Ix = Ix') by congruence.
      assert (HinI : In (q, Ix, (40 * ng_ifaces_size sx)%Z) ((CLc ++ pcap_blocks (pv bq alloc data eb sx (Some q)) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; right; right; left; reflexivity).
      (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinI) as ndP__; nd_pre ndP__ 3%nat; intros (IBAND & I3 & ITOP & I2) I1 _; nd_post).
      cbn [cb_addr cb_size fst snd] in *.
      split; [right; left; apply in_block_app; right; unfold IBLK, in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; exact Ha|]. lia. }
    pose proof (rw_cells_uncut _ _ _ _ _ PRE0 P20' ltac:(cbn; lia)) as PREa. pose proof (rw_cells_uncut _ _ _ _ _ PREa P32 ltac:(cbn; lia)) as PREb.
    pose proof (rw_cells_uncut _ _ _ _ _ PREb P48' ltac:(cbn; lia)) as PREc. pose proof (rw_cells_uncut _ _ _ _ _ PREc PRE9 ltac:(cbn; lia)) as PRE.
    clear PREa PREb PREc PRE0 P20' P32 P48' PRE9 P20 P48. cbn [app] in PRE.
    pose proof (rw_cells_uncut _ _ _ _ _ NG0 NG656' ltac:(cbn; lia)) as NGa. pose proof (rw_cells_uncut _ _ _ _ _ NGa NGR ltac:(cbn; lia)) as NG6.
    clear NGa NG0 NG656' NGR NG656. cbn [app] in NG6.
    assert (AG7 : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AG6|]. intros a [[Ha|[Ha|[Ha|Ha]]] _].
      - split; [left; lia| lia].
      - pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G5 ltac:(apply in_block_app; left; apply in_block_app; left; exact Ha)) as AB.
        pose proof (@F_ngnEA.CLc_not_PB rc tlsI H hptr FO GIOA fflagA GL CLc FB FL _ _ _ _ _ a G5 Ha) as NPB.
        assert (NP : ~ (P <= a < P + 680)%Z) by (intros Hr; apply NPB; unfold pcap_blocks, in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; unfold psize, is_ng, F_ngnEA.pv; cbn [pc_priv]; unfold PCAP_NG_SF_TOTAL; lia).
        split; [right; left; apply in_block_app; left; apply in_block_app; left; exact Ha| lia].
      - pose proof (gia_in_frames_below _ _ _ GL _ _ _ _ _ _ _ a G5 Ha) as AB.
        pose proof (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G5 Ha) as NBK.
        assert (NP : ~ (P <= a < P + 680)%Z) by (intros Hr; apply NBK; apply in_block_app; left; apply in_block_app; right; unfold pcap_blocks, in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; unfold psize, is_ng, F_ngnEA.pv; cbn [pc_priv]; unfold PCAP_NG_SF_TOTAL; lia).
        split; [right; right; left; exact Ha| lia].
      - pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G5 Ha) as SBD.
        band_ind PBAND bP. split; [right; right; right; exact Ha| lia]. }
    assert (G6' : GIOA L RNG6 st' (CLc ++ pcap_blocks (pv bq' alloc' data' eb sx ix) P B' Ix') FB FL m6).
    { eapply GPL; [exact G6|]. unfold pcap_blocks, F_ngnEA.pv, psize, is_ng. cbn [pc_self pc_buffer pc_bufalloc pc_priv]. unfold IBLK.
      change (CLc ++ (self, P, PCAP_NG_SF_TOTAL) :: (bq', B', alloc') :: match ix with Some q => [(q, Ix', (40 * ng_ifaces_size sx)%Z)] | None => [] end)
        with (CLc ++ [(self, P, PCAP_NG_SF_TOTAL)] ++ (bq', B', alloc') :: match ix with Some q => [(q, Ix', (40 * ng_ifaces_size sx)%Z)] | None => [] end).
      rewrite (app_assoc CLc). apply Permutation.Permutation_cons_app. apply Permutation.Permutation_refl. }
    assert (WF' : pcap_wf (pv bq' alloc' data' eb sx ix)).
    { unfold pcap_wf, F_ngnEA.pv in WF |- *.
      cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor pc_linktype pc_linktype_ext pc_header pc_priv] in WF |- *.
      clear - WF BR3 BR4 LEN6. lia. }
    assert (JOIN : forall cs, rw_cells asegs m6 (P + 216) cs -> cells_size cs = 304%nat ->
              rw_cells asegs m6 P (pcap_cells_gen (pv bq' alloc' data' eb sx ix) P B' (C8 (Z_to_bv 64 Afx)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) (set_pj_g (cells_bytes cs) jx'))).
    { intros cs HCS Hcs.
      exact (pcap_cells_join4 _ P (pv bq' alloc' data' eb sx ix) B' (C8 (Z_to_bv 64 Afx)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) jx' cs header eq_refl PRE HCS Hcs HDR OPS). }
    (* [comment removed for export] *)
    assert (FIN : forall cs ccs', rw_cells asegs m6 (P + 216) cs -> cells_size cs = 304%nat ->
              rw_cells asegs m6 (bv_unsigned sp + -128) ccs' -> cells_size ccs' = 24%nat ->
              rw_cells asegs m6 (bv_unsigned sp + -224) (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_frameA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA ccs')
              /\ ngn_final m6 RNG6 st' (pcap_blocks (pv bq' alloc' data' eb sx ix) P B' Ix') (pv bq' alloc' data' eb sx ix) hcs dw).
    { intros cs ccs' HCS Hcs HCUR' Hccs'.
      split. { unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_frameA. eapply (rw_cells_uncut _ _ _ _ _ F0); [eapply (rw_cells_uncut _ _ _ _ _ HCUR' FS); rewrite Hccs'; cbn; lia | cbn; lia]. }
      split; [exact FP7|]. split; [exact G6'|]. split.
      { exists Afx. split; [exact Hin|]. eexists B', Ix', _, padx, bs'.
        split; [reflexivity|]. split; [exact (JOIN cs HCS Hcs)|]. split; [exact NG6|]. split; [exact BUF6|]. split; [exact PFX6|]. split; [exact IFS6| exact WF']. }
      split; [exact AG7|]. split; [exact HH|]. split; [exact Hh|]. split; [exact HD|]. split; [exact Hd| exact OF7]. }
    cbv beta. ienterG.
    destruct rb as [p'' | msg p'' | c p''].
    - (* [comment removed for export] *)
      (destruct RM as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 2%nat; intros HEB6 (ccs' & HCUR6 & Hccs'); nd_post).
      pose proof (rw_cells_uncut _ _ _ _ _ HEB6 CE2 ltac:(cbn; lia)) as CE6.
      destruct (FIN _ _ CE6 eq_refl HCUR6 Hccs') as [FR6 FIN6].
      hide FR6. hide FIN6. hide HH. hide HD. hide CE6. hide HEB6. hide CE2. hide HDR. hide OPS. hide PRE. hide NG6. hide BUF6. hide HCUR6. hide F0. hide FS. hide CE1. hide PRIV.
      pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
      zstep. zstep. if_false. zstep. if_true. zstep. zstep.
      unhide FR6. unhide FIN6. apply evtF_done. cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA.ngn_body]. apply implMG_retb_l. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF.
      subst POSTQ0. eapply (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_ret_0 rc H hptr GIOA) with (ccs := ccs') (PB' := pcap_blocks (pv bq' alloc' data' eb sx ix) P B' Ix') (hcs' := hcs); try eassumption.
    - (* [comment removed for export] *)
      (destruct RM as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 4%nat; intros (junk6 & HEB6) LENM MOK (ccs' & HCUR6 & Hccs'); nd_post).
      pose proof (rw_cells_uncut _ _ _ _ _ HEB6 CE2 ltac:(cbn [cells_size csize]; clear - LENM; lia)) as CE6. cbn [app] in CE6.
      destruct (FIN _ _ CE6 ltac:(cbn [cells_size csize]; clear - LENM; lia) HCUR6 Hccs') as [FR6 FIN6].
      hide FR6. hide FIN6. hide HH. hide HD. hide CE6. hide HEB6. hide CE2. hide HDR. hide OPS. hide PRE. hide NG6. hide BUF6. hide HCUR6. hide F0. hide FS. hide CE1. hide PRIV.
      pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
      zstep. zstep. if_true.
      unhide FR6. unhide FIN6. apply evtF_done. cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA.ngn_body]. apply implMG_retb_l. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF.
      subst POSTQ0. eapply (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_ret_m1 rc H hptr GIOA) with (ccs := ccs') (PB' := pcap_blocks (pv bq' alloc' data' eb sx ix) P B' Ix') (hcs' := hcs); try eassumption.
      (nd_pre FIN6 4%nat; intros FPx G7 PC7 REST; nd_post). split; [exact FPx|]. split; [exact G7|]. split; [| exact REST].
      apply PCAPR_closable_of in PC7. (nd_pre PC7 3%nat; intros Afy Hiny (By & Iy & jy & pady & bsy & EPBy & CEy & PRy & BUFy & PFXy & IFCy & WFy); nd_post).
      exists Afy. split; [exact Hiny|]. exists By, Iy, jy, pady, bsy.
      split; [exact EPBy|]. split; [exact CEy|]. split; [exact PRy|]. split; [exact BUFy|]. split; [exact PFXy|]. split; [| exact WFy].
      unfold ifaces_closable, F_ngnEA.pv in IFCy |- *. cbn [pc_priv set_errbuf] in IFCy |- *. exact IFCy.
    - (* [comment removed for export] *)
      (destruct RM as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 9%nat; intros HEB6 (cpad & HCUR6) COFF CR0 CR1 CR2 CBT LEND GRD; nd_post).
      destruct c as [coff crem cbt]. cbn [cur_off cur_remaining cur_block_type] in COFF, CR0, CR1, CR2, CBT, LEND, HCUR6. subst coff.
      pose proof (rw_cells_uncut _ _ _ _ _ HEB6 CE2 ltac:(cbn; lia)) as CE6.
      destruct (FIN _ _ CE6 eq_refl HCUR6 eq_refl) as [FR6 FIN6]. (nd_pre FIN6 4%nat; intros _ _ PC6 _; nd_post).
      apply evtF_done. cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA.ngn_body].
      subst POSTQ0. eapply (ngn_dispatch LOOP HLOOP); [exact FP7 | exact ST6 | exact FR6 | exact MI6 | exact G6' | exact PC6 | exact AG7 | exact HH | exact Hh | exact HD | exact Hd | exact GRD | exact LEND | exact CR2 | exact CR0 | exact CBT | exact OF7].
  Qed.

  (* [comment removed for export] *)
  #[using="rc tlsI fflagA GL SNPRINTF LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HinF HLOC DLOC trC PP OHA ODA HDA HA8 DA8 ADJ ADDIF RBLK GPL TR NF"] Lemma ngn_loop : forall fuel, ngn_headA (fun p' ps' RNG' ms' => implMG RNG' (mbind (ng_scan_blocks MOps (prims HO FO sites) fuel p') ngn_KF) ps' POSTQ ms').
  Proof.
    induction fuel as [|fuel IH].
    - unfold F_ngnEA.ngn_headA. intros. cbn [ng_scan_blocks].
      eapply (implMG_bind _ _ _ _ (fun _ _ _ _ => False)); [apply implMG_unr | intros a s' R' ms' X; exact (False_rect _ X)].
    - unfold F_ngnEA.ngn_headA. intros. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA.ng_scan_blocks_S.
      revert H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13. apply (ngn_loop_S _ IH).
  Qed.
End NgnCtx.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require F_aiEA_body__B3P.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnEA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_ngnE2A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiEA_body__B3P.F_ngnSA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_ngnICA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnIA__A3P.F_ngnIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnDA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
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

Lemma signed_lit_s32 : forall x, bv_signed (Z_to_bv 64 (s32 x)) = s32 x.
Proof.
  intros x. pose proof (s32_range x) as R. rewrite zb_signed, unsigned_lit_wrap.
  destruct (Z_lt_dec (s32 x) 0).
  - replace ((s32 x) mod 2^64)%Z with (s32 x + 2^64)%Z by (Z.div_mod_to_equations; lia).
    replace (s32 x + 2 ^ 64 <? 2 ^ 63)%Z with false by (symmetry; apply Z.ltb_ge; lia). lia.
  - rewrite Z.mod_small by lia. replace (s32 x <? 2 ^ 63)%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
Lemma s32_cases : forall x, (0 <= x < 2^32 -> (x < 2^31 /\ s32 x = x) \/ (2^31 <= x /\ s32 x = x - 2^32))%Z.
Proof. intros x Hx. unfold s32. destruct (Z_lt_dec x (2^31)); [left | right]; split; try lia; Z.div_mod_to_equations; lia. Qed.

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
  Hypothesis PP : post_process_stmt.
  Hypothesis OHA : cobjA RNG m FL CLc HA 24.
  Hypothesis ODA : cobjA RNG m FL CLc DA 8.
  Hypothesis HDA : (HA + 24 <= DA \/ DA + 8 <= HA)%Z.
  Hypothesis HA8 : (HA mod 8 = 0)%Z.
  Hypothesis DA8 : (DA mod 8 = 0)%Z.
  Hypothesis ADJ : adjust_snapshot_stmt.
  Hypothesis ADDIF : add_interface_stmt HO FO sites GIOA TP.
  Hypothesis RBLK : read_block_stmt HO FO sites GIOA TP.
  Hypothesis GPL : gia_perm_law GIOA.
  Hypothesis TR : traces_pcap_ng_next_packet TP L (bv_unsigned ra) trC.
  Hypothesis NF : nofr frames_pcap_ng_next_packet FL.

  #[local] Abbreviation pcapT := (pcap hptr hptr).
  #[local] Abbreviation MR := (M (PState H hptr) ((Z + ng_found) * pcap hptr hptr)).
  #[local] Abbreviation pv := (A3P.F_ngnEA.TwB.pv self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).
  #[local] Abbreviation ccells := (A3P.F_ngnEA.TwB.ccells).
  #[local] Abbreviation ngn_KF := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF H hptr).
  #[local] Abbreviation ngn_blkK := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA.TwB.ngn_blkK H hptr HO FO sites).
  #[local] Abbreviation ngn_body := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA.TwB.ngn_body H hptr HO FO sites).
  #[local] Abbreviation ngn_headA := (A3P.F_ngnEA.TwB.ngn_headA GIOA TP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CLc FB FL lo P HA DA Af m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).

  #[using="Type"] Lemma implMG_retb_l : forall {St A B} RNGx (a : A) (k : A -> Monad.M St B) s Q ms, implMG RNGx (k a) s Q ms -> implMG RNGx (mbind (mret a) k) s Q ms.
  Proof. intros St A B RNGx a k s Q ms HH. exact HH. Qed.

  Ltac decide_eqb :=
    repeat (match goal with
            | |- context [Z.eqb ?x ?k] => first [ replace (Z.eqb x k) with false by (symmetry; apply Z.eqb_neq; lia)
                                                | replace (Z.eqb x k) with true by (symmetry; apply Z.eqb_eq; lia) ]
            end; cbv iota).

  (* [comment removed for export] *)
  Definition ngn_dispatch__stmt : Prop := forall (LOOP : pcapT -> MR),
    ngn_headA (fun p' ps' RNG' ms' => implMG RNG' (mbind (LOOP p') ngn_KF) ps' POSTQ ms') ->
    forall (t0' t1' t2' x0 a1' a2' a3' a4' a5' a6' a7' x11 t3' t4' t5' t6' : word) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (bt : Z) (hcs : list cell) (dw : cell) (cpad : list byte),
      fp_le RNG RNG5 ->
      stk asegs m5 lo (bv_unsigned sp + -240) ->
      rw_cells asegs m5 (bv_unsigned sp + -240) (ngn_frameA (ccells Bq rem bt cpad)) -> mem_inv asegs m5 ->
      GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells asegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells asegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (0 <= rem)%Z ->
      (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implMG RNG5 (mbind (ngn_blkK LOOP (mkCursor 8 rem bt) (pv bq alloc data eb sx ix)) ngn_KF) ps POSTQ
        (MS (mkR (Z_to_bv 64 0x8ce3c) (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0' t1' t2' x0 (Z_to_bv 64 (P + 216)) (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) (Z_to_bv 64 2) (Z_to_bv 64 2147450880) (Z_to_bv 64 (P + 660))
                 (Z_to_bv 64 1) (Z_to_bv 64 168627466) (Z_to_bv 64 P) (Z_to_bv 64 Af) x11
                 t3' t4' t5' t6') F (Z_to_bv 64 0x8ce3c) fc None m5 (seg_rom asegs)).
  Section Sz4.
  Variables LOOP t0' t1' t2' x0 a1' a2' a3' a4' a5' a6' a7' x11 t3' t4' t5' t6' m5 RNG5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw cpad : ltac2:(SecDiet.SzSec.tyM 'ngn_dispatch__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @LOOP).
  #[using="rc tlsI fflagA GL SNPRINTF LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HLOC DLOC trC PP OHA ODA HDA HA8 DA8 ADJ ADDIF GPL TR"] Lemma ngn_dispatch__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_dispatch__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros HLOOP.
 intros FP5 ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (rng_fp_le _ _ _ _ FP5 RSTK) as RSTK5.
    assert (RSPW : rng RNG5 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK5| lia]).
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA.TwB.ngn_blkK. cbn [cur_block_type]. unfold BT_EPB, BT_SPB, BT_PB, BT_IDB, BT_SHB.
    pose proof (s32_cases bt Hbt) as SC.
    pose proof FR5 as FRJ. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_frameA, A3P.F_ngnEA.TwB.ccells in FRJ. cbn [app] in FRJ.
    hide FR5. hide HH. hide HD.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    ienterG.
    zstep. zstep.
  if_false.
  zstep. if_false.
  zstep. rewrite (sx32_s32 bt) by lia.
  zstep.
  if_cases B3; zify_cond B3; rewrite ?signed_lit_s32 in B3; rewrite ?signed_lit in B3 by lia.
    - (* [comment removed for export] *)
      zstep. if_cases B4; zify_cond B4; rewrite ?unsigned_lit_wrap in B4.
      + (* [comment removed for export] *)
        zstep. if_cases B5; zify_cond B5; rewrite ?unsigned_lit_wrap in B5.
        * (* [comment removed for export] *)
          assert (NB : (bt <> 1 /\ bt <> 2 /\ bt <> 3 /\ bt <> 6 /\ bt <> 168627466)%Z).
          { destruct SC as [[LT E]|[GE E]]; rewrite E in B3, B4, B5; [rewrite Z.mod_small in B4, B5 by lia; lia|]. lia. }
          decide_eqb.
          unhide FR5. unhide HH. unhide HD. apply evtF_done.
          unfold A3P.F_ngnEA.TwB.ngn_headA in HLOOP. unfold NGN_LOOP_A in HLOOP.
          eapply HLOOP; [exact FP5 | exact ST5 | exact FR5 | reflexivity | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact Hh | exact HD | exact Hd | exact OF5
                        | apply (A3P.F_ngnEA.TwB.ngn_ucx_m1 TP sp L lo LO BU SPT); exact (proj1 (proj2 TR))].
        * (* [comment removed for export] *)
          assert (EB : (bt = 2)%Z) by (destruct SC as [[LT E]|[GE E]]; rewrite E in B5; [rewrite Z.mod_small in B5 by lia; lia| exfalso; Z.div_mod_to_equations; lia]).
          decide_eqb. zstep.
          unhide FR5. unhide HH. unhide HD. apply evtF_done.
  subst POSTQ0. eapply A3P.F_ngnDA.TwB.ngn_pb; try eassumption.
      + (* [comment removed for export] *)
        assert (EB : (bt = 1)%Z) by (destruct SC as [[LT E]|[GE E]]; rewrite E in B4; [rewrite Z.mod_small in B4 by lia; lia| exfalso; Z.div_mod_to_equations; lia]).
        decide_eqb.
        unhide FR5. unhide HH. unhide HD. apply evtF_done.
        subst POSTQ0. eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnIA__A3P.F_ngnIA.TwB.ngn_idb; try eassumption.
    - (* [comment removed for export] *)
      assert (LT31 : (bt < 2^31 /\ s32 bt = bt)%Z) by (destruct SC as [[LT E]|[GE E]]; [split; [exact LT| exact E]| exfalso; rewrite E in B3; lia]).
      destruct LT31 as [LT31 E32]. rewrite E32 in B3.
      zstep. if_cases B6; zify_cond B6; rewrite ?E32, ?unsigned_lit in B6 by lia.
      + (* [comment removed for export] *)
        zstep. zstep. if_cases B7; zify_cond B7; rewrite ?E32, ?unsigned_lit in B7 by lia.
        * (* [comment removed for export] *)
          decide_eqb.
          unhide FR5. unhide HH. unhide HD. apply evtF_done.
          subst POSTQ0. eapply A3P.F_ngnDA.TwB.ngn_spb; try eassumption.
        * zstep. zstep. if_cases B8; zify_cond B8; rewrite ?E32, ?unsigned_lit in B8 by lia.
          -- (* [comment removed for export] *)
             decide_eqb.
             unhide FR5. unhide HH. unhide HD. apply evtF_done.
             unfold A3P.F_ngnEA.TwB.ngn_headA in HLOOP. unfold NGN_LOOP_A in HLOOP.
             eapply HLOOP; [exact FP5 | exact ST5 | exact FR5 | reflexivity | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact Hh | exact HD | exact Hd | exact OF5
                           | apply (A3P.F_ngnEA.TwB.ngn_ucx_m1 TP sp L lo LO BU SPT); exact (proj1 (proj2 TR))].
          -- (* [comment removed for export] *)
             decide_eqb. zstep.
             unhide FR5. unhide HH. unhide HD. apply evtF_done.
             subst POSTQ0. eapply A3P.F_ngnDA.TwB.ngn_epb; try eassumption.
      + (* [comment removed for export] *)
        decide_eqb.
        unhide FR5. unhide HH. unhide HD. apply evtF_done.
        subst POSTQ0. eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiEA_body__B3P.F_ngnSA.ngn_shb; try eassumption.
  Qed.
  End Sz4.
  #[using="rc tlsI fflagA GL SNPRINTF LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HLOC DLOC trC PP OHA ODA HDA HA8 DA8 ADJ ADDIF GPL TR"] Lemma ngn_dispatch : ltac:(let t := eval cbv delta [ngn_dispatch__stmt] in ngn_dispatch__stmt in exact t).
  Proof. intros LOOP HLOOP t0' t1' t2' x0 a1' a2' a3' a4' a5' a6' a7' x11 t3' t4' t5' t6' m5 RNG5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw cpad. ltac2:(SecDiet.SzSec.closeP 'ngn_dispatch__body "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngn_loop_S__stmt : Prop := forall (LOOP : pcapT -> MR),
    ngn_headA (fun p' ps' RNG' ms' => implMG RNG' (mbind (LOOP p') ngn_KF) ps' POSTQ ms') ->
    ngn_headA (fun p' ps' RNG' ms' => implMG RNG' (mbind (mbind (read_block MOps (prims HO FO sites) (DStack SiteBhdrNextPacket 0) p') (ngn_body LOOP)) ngn_KF) ps' POSTQ ms').
  Section Sz5.
  Variables LOOP ra' t0' t1' t2' x0 a0' a1' a2' a3' a4' a5' a6' a7' x11 t3' t4' t5' t6' m5 RNG5 ps bq Bq Ix alloc data eb sx ix hcs dw ccs : ltac2:(SecDiet.SzSec.tyM 'ngn_loop_S__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @LOOP).
  #[using="rc tlsI fflagA GL SNPRINTF LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HinF HLOC DLOC trC PP OHA ODA HDA HA8 DA8 ADJ ADDIF RBLK GPL TR NF"] Lemma ngn_loop_S__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_loop_S__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof.
    intros HLOOP.
 intros FP5 ST5 FR5 Hccs MI5 G5 PC5 AG5 HH Hh HD Hd OF5 UCX. unfold NGN_LOOP_A.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (rng_fp_le _ _ _ _ FP5 RSTK) as RSTK5.
    assert (RSPW : rng RNG5 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK5| lia]).
    (pose proof PC5 as ndP__; nd_pre ndP__ 3%nat; intros Afx Hin (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF); nd_post).
    pose proof G5 as G5e. rewrite EPB in G5e.
    assert (HinP : In (self, P, 680%Z) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    assert (HinB : In (bq, Bq, alloc) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; right; left; reflexivity).
    (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinP) as ndP__; nd_pre ndP__ 6%nat; intros (PBAND & P3 & PTOP & P2) P1 PUNP PRNG PRSH PAR; nd_post).
    (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinB) as ndP__; nd_pre ndP__ 6%nat; intros (BBAND & B3 & BTOP & B2) B1 BUNP BRNG BRSH BAR; nd_post).
    cbn [cb_addr cb_size fst snd] in *.
    pose proof (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ G5 eq_refl) as [APB API].
    pose proof WF as (W1' & W2' & W3 & W4 & W5' & W6' & W7' & W8' & W9' & W10' & W11 & W12 & W13 & W14).
    unfold A3P.F_ngnEA.TwB.pv, pcap_blocks, psize, is_ng in EPB, APB. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, APB. unfold PCAP_NG_SF_TOTAL in APB.
    unfold A3P.F_ngnEA.TwB.pv in W3, W4, W13, W14. cbn [pc_bufalloc pc_bufdata pc_priv pc_bufsize] in W3, W4, W13, W14.
    assert (EBX : Bx' = Bq) by congruence. subst Bx'.
    unfold A3P.F_ngnEA.TwB.pv in Hin. cbn [pc_rfile] in Hin.
    unfold A3P.F_ngnEA.TwB.pv in BUF. cbn [pc_bufalloc] in BUF. cbn [pc_bufdata] in PFX.
    pose proof PRIV as NG. unfold priv_cells, A3P.F_ngnEA.TwB.pv, PCAP_PRIV_OFF in NG. cbn [pc_priv] in NG. unfold ng_cells in NG.
    assert (INP : forall a, (P <= a < P + 680)%Z -> client_keeps FL ((CLc ++ [(self, P, PCAP_NG_SF_TOTAL)]) ++ IBLK ix Ix' sx) (bv_unsigned sp + -240) a).
    { intros a Ha. right. left. apply in_block_app. left. apply in_block_app. right. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. exact Ha. }
    (* [comment removed for export] *)
    apply pcap_cells_split4 in CELLS as (PRE & CE & HDR & OPS); [|reflexivity].
    apply (rw_cells_split_CB asegs m5 _ [] 304 _ [] [256; 48]%nat) in CE; [|reflexivity]. cbn [mk_CB_cells app] in CE.
    destruct (rw_cells_cut _ _ _ 1 CE) as [CE1 CE2]. clear CE. cbn [firstn skipn cells_size csize Nat.add] in CE1, CE2.
    replace (P + 216 + Z.of_nat 256)%Z with (P + 472)%Z in CE2 by lia.
    unfold pc_pre in PRE.
    destruct (rw_cells_cut _ _ _ 3 PRE) as [PRE0 PRE3]. destruct (rw_cells_cut _ _ _ 2 PRE3) as [P20 PRE5].
    destruct (rw_cells_cut _ _ _ 2 PRE5) as [P32 PRE7]. destruct (rw_cells_cut _ _ _ 2 PRE7) as [P48 PRE9]. clear PRE PRE3 PRE5 PRE7.
    cbn [firstn skipn cells_size csize Nat.add app] in PRE0, P20, P32, P48, PRE9.
    replace (P + Z.of_nat 20)%Z with (P + 20)%Z in P20 by lia. replace (P + Z.of_nat 20 + Z.of_nat 12)%Z with (P + 32)%Z in P32 by lia.
    replace (P + Z.of_nat 20 + Z.of_nat 12 + Z.of_nat 16)%Z with (P + 48)%Z in P48 by lia.
    replace (P + Z.of_nat 20 + Z.of_nat 12 + Z.of_nat 16 + Z.of_nat 12)%Z with (P + 60)%Z in PRE9 by lia.
    destruct (rw_cells_cut _ _ _ 1 NG) as [NG0 NG1]. destruct (rw_cells_cut _ _ _ 1 NG1) as [NG656 NGR]. clear NG NG1.
    cbn [firstn skipn cells_size csize Nat.add app] in NG0, NG656, NGR.
    replace (P + 648 + Z.of_nat 8)%Z with (P + 656)%Z in NG656 by lia. replace (P + 648 + Z.of_nat 8 + Z.of_nat 4)%Z with (P + 660)%Z in NGR by lia.
    (* [comment removed for export] *)
    pose proof FR5 as FRJ. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_frameA in FRJ.
    destruct (proj1 (rw_cells_app asegs m5 _ _ _) FRJ) as [F0 F4]. destruct (proj1 (rw_cells_app asegs m5 _ _ _) F4) as [FCUR FS]. clear FRJ F4.
    cbn [cells_size csize Nat.add] in FCUR, FS. rewrite Hccs in FS.
    replace (bv_unsigned sp + -240 + Z.of_nat 112)%Z with (bv_unsigned sp + -128)%Z in FCUR, FS by lia.
    replace (bv_unsigned sp + -128 + Z.of_nat 24)%Z with (bv_unsigned sp + -104)%Z in FS by lia.
    hide F0. hide FCUR. hide FS. hide PRE0. hide P20. hide P32. hide P48. hide PRE9. hide CE1. hide CE2. hide HDR. hide OPS. hide NG0. hide NG656. hide NGR. hide BUF. hide HH. hide HD. hide FR5. hide PRIV. hide IFS.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    apply implMG_bind_assoc. ienterG. do 4 zstep. zstep. clear MU WM.
    unhide F0. unhide FCUR. unhide FS. unhide PRE0. unhide P20. unhide P32. unhide P48. unhide PRE9. unhide CE1. unhide CE2. unhide HDR. unhide OPS. unhide NG0. unhide NG656. unhide NGR. unhide BUF. unhide HH. unhide HD. unhide FR5. unhide PRIV. unhide IFS.
    pose proof (rng_fp_le _ _ _ _ FP5 RIMG) as RIMG5. pose proof (rng_fp_le _ _ _ _ FP5 RISH) as RISH5. pose proof (rng_fp_le _ _ _ _ FP5 RTLS) as RTLS5.
    (nd_pre UCX 3%nat; intros trX TRX UCX; nd_post).
    apply evtF_done. name_sp sp (-240)%Z. eapply implMG_bind.
    { eapply RBLK with (L := L) (st := ps) (C1 := CLc ++ [(self, P, PCAP_NG_SF_TOTAL)]) (C2 := IBLK ix Ix' sx) (FB := FB) (FL := FL) (trC := trX) (f := f) (Af := Af) (P := P) (B := Bq)
                      (CUR := (bv_unsigned sp + -128)%Z) (EB := (P + 216)%Z) (lo := lo) (p := pv bq alloc data eb sx ix) (s := sx) (i := ix)
                      (a_bhdr := DStack SiteBhdrNextPacket 0) (bs := bsx') (ej := firstn 256 (pj_g jx')) (ccs := ccs).
      - split; [rewrite <- app_assoc; cbn [app]; pose proof G5e as GX; unfold pcap_blocks, A3P.F_ngnEA.TwB.pv, psize, is_ng in GX; cbn [pc_self pc_buffer pc_bufalloc pc_priv] in GX; unfold IBLK; exact GX |].
        split; [rewrite Hsp; exact ST5|]. split; [exact LO|]. split; [unfold READ_BLOCK_STACK, PCAP_L1_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [exact MI5|]. split; [exact TPE|]. split; [rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]|].
        split; [exact RSTK5|]. split; [exact RIMG5|]. split; [exact RISH5| exact RTLS5].
      - apply UCX. exact Hsp.
      - rewrite unsigned_lit by lia. exact TRX.
      - exact NF.
      - exact HinF.
      - reflexivity.
      - reflexivity.
      - apply in_or_app; left; apply in_or_app; right; left; reflexivity.
      - exists SiteBhdrNextPacket. split; [reflexivity| apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA.TwB.site_bhdr_frame].
      - reflexivity.
      - reflexivity.
      - f_equal; lia.
      - reflexivity.
      - split; [exact P20|]. split; [exact P48|]. split; [exact NG656|]. cbn [pc_bufsize pc_bufalloc A3P.F_ngnEA.TwB.pv]. unfold pcap_wf, A3P.F_ngnEA.TwB.pv in WF. cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_priv] in WF. lia.
      - exact BUF.
      - exact PFX.
      - cbn [pc_bufdata pc_bufalloc A3P.F_ngnEA.TwB.pv]; lia.
      - exact FCUR.
      - exact Hccs.
      - rewrite Hsp. split; lia.
      - clear - ALN. Z.div_mod_to_equations. lia.
      - exact CE1.
      - right; reflexivity.
      - clear - P2. Z.div_mod_to_equations. lia. }
    intros rb st' RNG6 ms' PO. cbv beta in PO.
    (nd_pre PO 23%nat; intros FP6 a0v m6 p' B' bs' E OF6 MI6 ST6 AG6 G6 BH6 BUF6 PFX6 LEN6 PRIVE RFE SELFE BSZE SWE META RM; nd_post).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 577084)) with (Z_to_bv 64 577084) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    destruct p' as [self' f' bsz' alloc' bq' data' sw' vmaj' vmin' snap' lt' lte' prec' brk' eb' hdr' priv'].
    cbn [pc_priv pc_rfile pc_self pc_bufsize pc_swapped A3P.F_ngnEA.TwB.pv] in PRIVE, RFE, SELFE, BSZE, SWE.
    unfold same_meta in META. cbn [pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header A3P.F_ngnEA.TwB.pv] in META.
    (nd_pre META 9%nat; intros M1 M2 M3 M4 M5 M6 M7 M8 M9; nd_post). subst priv' f' self' bsz' sw' vmaj' vmin' snap' lt' lte' prec' brk' eb' hdr'.
    change ({| pc_self := self; pc_rfile := f; pc_bufsize := bufsize; pc_bufalloc := alloc'; pc_buffer := bq'; pc_bufdata := data'; pc_swapped := swapped;
               pc_version_major := vmaj; pc_version_minor := vmin; pc_snapshot := snapshot; pc_linktype := linktype; pc_linktype_ext := ltext;
               pc_tstamp_precision := prec; pc_break_loop := brk; pc_errbuf := eb; pc_header := header; pc_priv := PrivNg sx ix |})
      with (pv bq' alloc' data' eb sx ix) in *.
    cbn [pc_buffer pc_bufalloc pc_bufdata A3P.F_ngnEA.TwB.pv] in G6, BUF6, PFX6, LEN6, RM.
    (nd_pre BH6 7%nat; intros P20' P48' NG656' BR1 BR2 BR3 BR4; nd_post). cbn [pc_bufsize pc_swapped pc_bufalloc A3P.F_ngnEA.TwB.pv] in P20', P48', BR1, BR3, BR4.
    assert (OF7 : ps_outfile st' = o) by (rewrite OF6; exact OF5).
    assert (FP7 : fp_le RNG RNG6) by (eapply fp_le_trans; [exact FP5 | exact FP6]).
    pose proof atop_range as AR.
    assert (HLOC' : clocA FL ((CLc ++ [(self, P, PCAP_NG_SF_TOTAL)]) ++ IBLK ix Ix' sx) HA 24) by (eapply clocA_incl; [exact HLOC | rewrite <- app_assoc; apply incl_appl, incl_refl | apply incl_refl]).
    assert (DLOC' : clocA FL ((CLc ++ [(self, P, PCAP_NG_SF_TOTAL)]) ++ IBLK ix Ix' sx) DA 8) by (eapply clocA_incl; [exact DLOC | rewrite <- app_assoc; apply incl_appl, incl_refl | apply incl_refl]).
    (* [comment removed for export] *)
    transport F0 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; lia| lia]).
    transport FS m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; lia| lia]).
    transport HH m6 AG6 ltac:(intros a Ha; rewrite Hh in Ha; split; [eapply clocA_keeps; [exact HLOC'| lia]| lia]).
    transport HD m6 AG6 ltac:(intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; split; [eapply clocA_keeps; [exact DLOC'| lia]| lia]).
    transport PRE0 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; lia| lia]).
    transport P32 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; lia| lia]).
    transport PRE9 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; lia| lia]).
    transport CE2 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; lia| lia]).
    transport HDR m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add hdr_cells pc_header A3P.F_ngnEA.TwB.pv] in Ha; split; [apply INP; lia| lia]).
    transport OPS m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add pc_ops] in Ha; split; [apply INP; lia| lia]).
    transport NG0 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; lia| lia]).
    transport NGR m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; lia| lia]).
    assert (IFS6 : ifaces_ok (pv bq' alloc' data' eb sx ix) Ix' m6).
    { eapply ifaces_ok_agree; [exact AG6 | | exact IFS]. intros sg q Hq a Ha. unfold A3P.F_ngnEA.TwB.pv in Hq. cbn [pc_priv] in Hq. injection Hq as E1 E2. subst sg ix.
      destruct (API sx q eq_refl) as [X1 X2]. unfold psize, is_ng, A3P.F_ngnEA.TwB.pv in X1. cbn [pc_priv] in X1. unfold PCAP_NG_SF_TOTAL in X1.
      assert (EI : Ix = Ix') by congruence.
      assert (HinI : In (q, Ix, (40 * ng_ifaces_size sx)%Z) ((CLc ++ pcap_blocks (pv bq alloc data eb sx (Some q)) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; right; right; left; reflexivity).
      (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinI) as ndP__; nd_pre ndP__ 3%nat; intros (IBAND & I3 & ITOP & I2) I1 _; nd_post).
      cbn [cb_addr cb_size fst snd] in *.
      split; [right; left; apply in_block_app; right; unfold IBLK, in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; exact Ha|]. lia. }
    pose proof (rw_cells_uncut _ _ _ _ _ PRE0 P20' ltac:(cbn; lia)) as PREa. pose proof (rw_cells_uncut _ _ _ _ _ PREa P32 ltac:(cbn; lia)) as PREb.
    pose proof (rw_cells_uncut _ _ _ _ _ PREb P48' ltac:(cbn; lia)) as PREc. pose proof (rw_cells_uncut _ _ _ _ _ PREc PRE9 ltac:(cbn; lia)) as PRE.
    clear PREa PREb PREc PRE0 P20' P32 P48' PRE9 P20 P48. cbn [app] in PRE.
    pose proof (rw_cells_uncut _ _ _ _ _ NG0 NG656' ltac:(cbn; lia)) as NGa. pose proof (rw_cells_uncut _ _ _ _ _ NGa NGR ltac:(cbn; lia)) as NG6.
    clear NGa NG0 NG656' NGR NG656. cbn [app] in NG6.
    assert (AG7 : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AG6|]. intros a [[Ha|[Ha|[Ha|Ha]]] _].
      - split; [left; lia| lia].
      - pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G5 ltac:(apply in_block_app; left; apply in_block_app; left; exact Ha)) as AB.
        pose proof (@A3P.F_ngnEA.TwB.CLc_not_PB rc tlsI H hptr FO GIOA fflagA GL CLc FB FL _ _ _ _ _ a G5 Ha) as NPB.
        assert (NP : ~ (P <= a < P + 680)%Z) by (intros Hr; apply NPB; unfold pcap_blocks, in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; unfold psize, is_ng, A3P.F_ngnEA.TwB.pv; cbn [pc_priv]; unfold PCAP_NG_SF_TOTAL; lia).
        split; [right; left; apply in_block_app; left; apply in_block_app; left; exact Ha| lia].
      - pose proof (gia_in_frames_below _ _ _ GL _ _ _ _ _ _ _ a G5 Ha) as AB.
        pose proof (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G5 Ha) as NBK.
        assert (NP : ~ (P <= a < P + 680)%Z) by (intros Hr; apply NBK; apply in_block_app; left; apply in_block_app; right; unfold pcap_blocks, in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; unfold psize, is_ng, A3P.F_ngnEA.TwB.pv; cbn [pc_priv]; unfold PCAP_NG_SF_TOTAL; lia).
        split; [right; right; left; exact Ha| lia].
      - pose proof (gia_in_frame_sh_band _ _ _ GL _ _ _ _ _ _ _ a G5 Ha) as SBD.
        band_ind PBAND bP. split; [right; right; right; exact Ha| lia]. }
    assert (G6' : GIOA L RNG6 st' (CLc ++ pcap_blocks (pv bq' alloc' data' eb sx ix) P B' Ix') FB FL m6).
    { eapply GPL; [exact G6|]. unfold pcap_blocks, A3P.F_ngnEA.TwB.pv, psize, is_ng. cbn [pc_self pc_buffer pc_bufalloc pc_priv]. unfold IBLK.
      change (CLc ++ (self, P, PCAP_NG_SF_TOTAL) :: (bq', B', alloc') :: match ix with Some q => [(q, Ix', (40 * ng_ifaces_size sx)%Z)] | None => [] end)
        with (CLc ++ [(self, P, PCAP_NG_SF_TOTAL)] ++ (bq', B', alloc') :: match ix with Some q => [(q, Ix', (40 * ng_ifaces_size sx)%Z)] | None => [] end).
      rewrite (app_assoc CLc). apply Permutation.Permutation_cons_app. apply Permutation.Permutation_refl. }
    assert (WF' : pcap_wf (pv bq' alloc' data' eb sx ix)).
    { unfold pcap_wf, A3P.F_ngnEA.TwB.pv in WF |- *.
      cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor pc_linktype pc_linktype_ext pc_header pc_priv] in WF |- *.
      clear - WF BR3 BR4 LEN6. lia. }
    assert (JOIN : forall cs, rw_cells asegs m6 (P + 216) cs -> cells_size cs = 304%nat ->
              rw_cells asegs m6 P (pcap_cells_gen (pv bq' alloc' data' eb sx ix) P B' (C8 (Z_to_bv 64 Afx)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) (set_pj_g (cells_bytes cs) jx'))).
    { intros cs HCS Hcs.
      exact (pcap_cells_join4 _ P (pv bq' alloc' data' eb sx ix) B' (C8 (Z_to_bv 64 Afx)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) jx' cs header eq_refl PRE HCS Hcs HDR OPS). }
    (* [comment removed for export] *)
    assert (FIN : forall cs ccs', rw_cells asegs m6 (P + 216) cs -> cells_size cs = 304%nat ->
              rw_cells asegs m6 (bv_unsigned sp + -128) ccs' -> cells_size ccs' = 24%nat ->
              rw_cells asegs m6 (bv_unsigned sp + -240) (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_frameA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA ccs')
              /\ ngn_final m6 RNG6 st' (pcap_blocks (pv bq' alloc' data' eb sx ix) P B' Ix') (pv bq' alloc' data' eb sx ix) hcs dw).
    { intros cs ccs' HCS Hcs HCUR' Hccs'.
      split. { unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_frameA. eapply (rw_cells_uncut _ _ _ _ _ F0); [eapply (rw_cells_uncut _ _ _ _ _ HCUR' FS); rewrite Hccs'; cbn; lia | cbn; lia]. }
      split; [exact FP7|]. split; [exact G6'|]. split.
      { exists Afx. split; [exact Hin|]. eexists B', Ix', _, padx, bs'.
        split; [reflexivity|]. split; [exact (JOIN cs HCS Hcs)|]. split; [exact NG6|]. split; [exact BUF6|]. split; [exact PFX6|]. split; [exact IFS6| exact WF']. }
      split; [exact AG7|]. split; [exact HH|]. split; [exact Hh|]. split; [exact HD|]. split; [exact Hd| exact OF7]. }
    cbv beta. ienterG.
    destruct rb as [p'' | msg p'' | c p''].
    - (* [comment removed for export] *)
      (destruct RM as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 2%nat; intros HEB6 (ccs' & HCUR6 & Hccs'); nd_post).
      pose proof (rw_cells_uncut _ _ _ _ _ HEB6 CE2 ltac:(cbn; lia)) as CE6.
      destruct (FIN _ _ CE6 eq_refl HCUR6 Hccs') as [FR6 FIN6].
      hide FR6. hide FIN6. hide HH. hide HD. hide CE6. hide HEB6. hide CE2. hide HDR. hide OPS. hide PRE. hide NG6. hide BUF6. hide HCUR6. hide F0. hide FS. hide CE1. hide PRIV.
      pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
      zstep. zstep. if_false. zstep. if_true. zstep. zstep.
      unhide FR6. unhide FIN6. apply evtF_done. cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA.TwB.ngn_body]. apply implMG_retb_l. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF.
      subst POSTQ0. eapply (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_ret_0 rc H hptr GIOA) with (ccs := ccs') (PB' := pcap_blocks (pv bq' alloc' data' eb sx ix) P B' Ix') (hcs' := hcs); try eassumption.
    - (* [comment removed for export] *)
      (destruct RM as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 4%nat; intros (junk6 & HEB6) LENM MOK (ccs' & HCUR6 & Hccs'); nd_post).
      pose proof (rw_cells_uncut _ _ _ _ _ HEB6 CE2 ltac:(cbn [cells_size csize]; clear - LENM; lia)) as CE6. cbn [app] in CE6.
      destruct (FIN _ _ CE6 ltac:(cbn [cells_size csize]; clear - LENM; lia) HCUR6 Hccs') as [FR6 FIN6].
      hide FR6. hide FIN6. hide HH. hide HD. hide CE6. hide HEB6. hide CE2. hide HDR. hide OPS. hide PRE. hide NG6. hide BUF6. hide HCUR6. hide F0. hide FS. hide CE1. hide PRIV.
      pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
      zstep. zstep. if_true.
      unhide FR6. unhide FIN6. apply evtF_done. cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA.TwB.ngn_body]. apply implMG_retb_l. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF.
      subst POSTQ0. eapply (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_ret_m1 rc H hptr GIOA) with (ccs := ccs') (PB' := pcap_blocks (pv bq' alloc' data' eb sx ix) P B' Ix') (hcs' := hcs); try eassumption.
      (nd_pre FIN6 4%nat; intros FPx G7 PC7 REST; nd_post). split; [exact FPx|]. split; [exact G7|]. split; [| exact REST].
      apply PCAPR_closable_of in PC7. (nd_pre PC7 3%nat; intros Afy Hiny (By & Iy & jy & pady & bsy & EPBy & CEy & PRy & BUFy & PFXy & IFCy & WFy); nd_post).
      exists Afy. split; [exact Hiny|]. exists By, Iy, jy, pady, bsy.
      split; [exact EPBy|]. split; [exact CEy|]. split; [exact PRy|]. split; [exact BUFy|]. split; [exact PFXy|]. split; [| exact WFy].
      unfold ifaces_closable, A3P.F_ngnEA.TwB.pv in IFCy |- *. cbn [pc_priv set_errbuf] in IFCy |- *. exact IFCy.
    - (* [comment removed for export] *)
      (destruct RM as (-> & ndR1__); destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 9%nat; intros HEB6 (cpad & HCUR6) COFF CR0 CR1 CR2 CBT LEND GRD; nd_post).
      destruct c as [coff crem cbt]. cbn [cur_off cur_remaining cur_block_type] in COFF, CR0, CR1, CR2, CBT, LEND, HCUR6. subst coff.
      pose proof (rw_cells_uncut _ _ _ _ _ HEB6 CE2 ltac:(cbn; lia)) as CE6.
      destruct (FIN _ _ CE6 eq_refl HCUR6 eq_refl) as [FR6 FIN6]. (nd_pre FIN6 4%nat; intros _ _ PC6 _; nd_post).
      apply evtF_done. cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA.TwB.ngn_body].
      subst POSTQ0. eapply (ngn_dispatch LOOP HLOOP); [exact FP7 | exact ST6 | exact FR6 | exact MI6 | exact G6' | exact PC6 | exact AG7 | exact HH | exact Hh | exact HD | exact Hd | exact GRD | exact LEND | exact CR2 | exact CR0 | exact CBT | exact OF7].
  Qed.
  End Sz5.
  #[using="rc tlsI fflagA GL SNPRINTF LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HinF HLOC DLOC trC PP OHA ODA HDA HA8 DA8 ADJ ADDIF RBLK GPL TR NF"] Lemma ngn_loop_S : ltac:(let t := eval cbv delta [ngn_loop_S__stmt] in ngn_loop_S__stmt in exact t).
  Proof. intros LOOP HLOOP ra' t0' t1' t2' x0 a0' a1' a2' a3' a4' a5' a6' a7' x11 t3' t4' t5' t6' m5 RNG5 ps bq Bq Ix alloc data eb sx ix hcs dw ccs. ltac2:(SecDiet.SzSec.closeP 'ngn_loop_S__body "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  #[using="rc tlsI fflagA GL SNPRINTF LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HinF HLOC DLOC trC PP OHA ODA HDA HA8 DA8 ADJ ADDIF RBLK GPL TR NF"] Lemma ngn_loop : forall fuel, ngn_headA (fun p' ps' RNG' ms' => implMG RNG' (mbind (ng_scan_blocks MOps (prims HO FO sites) fuel p') ngn_KF) ps' POSTQ ms').
  Proof.
    induction fuel as [|fuel IH].
    - unfold A3P.F_ngnEA.TwB.ngn_headA. intros. cbn [ng_scan_blocks].
      eapply (implMG_bind _ _ _ _ (fun _ _ _ _ => False)); [apply implMG_unr | intros a s' R' ms' X; exact (False_rect _ X)].
    - unfold A3P.F_ngnEA.TwB.ngn_headA. intros. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA.TwB.ng_scan_blocks_S.
      revert H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13. apply (ngn_loop_S _ IH).
  Qed.
End NgnCtx.
End CANSEC1.
End TwB.
End F_ngnLA.

(* [comment removed for export] *)
Module F_ngnMA.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnKA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnEA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnE2A__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnEA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_ngnE2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnIA__A3P.F_ngnLA.
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


Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
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
              pc_tstamp_precision := prec; pc_break_loop := brk; pc_errbuf := errbuf; pc_header := header; pc_priv := PrivNg sx ix |} with (F_ngnEA.pv self rfile bufsize swapped vmaj vmin snapshot linktype ltext prec brk header buffer bufalloc bufdata errbuf sx ix) in *.
    set (pvv := F_ngnEA.pv self rfile bufsize swapped vmaj vmin snapshot linktype ltext prec brk header buffer bufalloc bufdata errbuf sx ix) in *.
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
    unfold next_packet_op, np_entry, is_ng. subst pvv. cbn [pc_priv pk_next_ng PK F_ngnEA.pv].
    rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA.pcap_ng_next_packet_KF HO FO sites).
    (* [comment removed for export] *)
    pose proof CELLS as CJ. unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, F_ngnEA.pv in CJ.
    cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_ng pk_cleanup_ng PK] in CJ.
    clear CELLS PRIV BUF PFX IFS.
    hide HH. hide HD.
    rng_sp_window RSTK sp RSPW.
    pose proof (munch_refl [(bv_unsigned sp - 224, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ienterG. carve_frame 224%nat ST.
    apply (rw_cells_split_CB asegs _ _ [] 224 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 24; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB _ ?t] =>
      lazymatch t with firstn _ _ => idtac | skipn _ _ => idtac end; let j := fresh "jk" in pose (j := t); change t with j in FR; clearbody j end.
    do 14 zstep.
    do 3 zstep.
    do 2 zstep.
  ck0 PUNP; ck_go.
    do 3 zstep. ck0 PUNP; ck_go.
    do 2 zstep.
    do 35 zstep.
    replace (Z.land (P + 96) 7) with 0%Z in FR by (change 7%Z with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    replace (Z.land (P + 100) 7) with 4%Z in FR by (change 7%Z with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    replace (Z.land (P + 56) 7) with 0%Z in FR by (change 7%Z with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3)%Z with 8%Z; Z.div_mod_to_equations; lia).
    change (0 + 3)%Z with 3%Z in FR. change (4 + 3)%Z with 7%Z in FR.
    unhide HH. unhide HD.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AGP : agrees_on (fun a => outside [(bv_unsigned sp + -224, bv_unsigned sp)]%Z a) m mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]) end.
    apply (agrees_rw_cells _ _ _ _ _ AGP) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside fst snd]; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGP) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside fst snd]; lia].
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (G0 : GIOA L RNG s (CLc ++ pcap_blocks (F_ngnEA.pv self rfile bufsize swapped vmaj vmin snapshot linktype ltext prec brk header buffer bufalloc bufdata errbuf sx ix) P B I) FB FL mm)
        by (eapply (gl_frame _ _ _ GL); [exact G | exact MU | exact WM | apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]]);
      assert (PC0 : PCAPR (hptr:=hptr) P (F_ngnEA.pv self rfile bufsize swapped vmaj vmin snapshot linktype ltext prec brk header buffer bufalloc bufdata errbuf sx ix)
                          (pcap_blocks (F_ngnEA.pv self rfile bufsize swapped vmaj vmin snapshot linktype ltext prec brk header buffer bufalloc bufdata errbuf sx ix) P B I) FB mm)
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
    eapply (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnIA__A3P.F_ngnLA.ngn_loop HO FO sites GIOA TP fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CLc FB FL lo P HA DA Af m (ps_outfile s)
              self rfile bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HinF HLOC DLOC trC
              PP OHA ODA HDA HA8 DA8 ADJ ADDIF RBLK GPL TR NF fuel) with (ccs := [CB 24 jk11]) (hcs := hcs) (dw := dc);
      [ apply fp_le_refl | exact ST | exact FR | reflexivity | assumption | exact G0 | exact PC0 | exact AG0 | exact HH | exact Hh | exact HD | exact Hd | reflexivity
      | eapply F_ngnEA.ngn_ucx_entry; [exact LO | exact BU | exact SPT | exact HALO | exact DALO | exact UC | exact S16 | exact (proj1 TR) | exact AG0] ].
  Qed.
  End Sz1.
  #[using="fflagA GL GPL SNPRINTF PP ADJ RBLK ADDIF"] Theorem pcap_ng_next_packet_proofA : ltac:(let t := eval cbv delta [pcap_ng_next_packet_proofA__stmt] in pcap_ng_next_packet_proofA__stmt in exact t).
  Proof. red. unfold next_packet_op_stmt_for. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CLc PB FB FL trC lo P HA DA p fuel hcs dc. ltac2:(SecDiet.SzSec.closeP 'pcap_ng_next_packet_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgnThm.
End CANSEC1.
End F_ngnMA.
