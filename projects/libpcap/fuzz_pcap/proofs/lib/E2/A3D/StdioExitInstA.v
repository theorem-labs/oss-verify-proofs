(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require MonadF. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Import MonadG GIA Pcap_ifaceA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require DrvKitA__A3D. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require F_module_dtorA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.ExitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.F_module_dtorA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA StdioLawsA StdioCompA Stdio_glue_exitA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioLawsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioCompA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_exitA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section SXInst.
  Context {H hptr : Type}.
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation PS := (PState H hptr).

  (* [comment removed for export] *)
  Definition SX_real (s : PS) (RNG : footprint) (m : mem) : Prop :=
    exists FB : list cblk,
      STDIOR (ps_libc s) FB m
      /\ Forall (fun b : cblk => 0x603000 <= cb_addr b /\ cb_addr b + cb_size b <= ATOP /\ rng RNG (cb_addr b) (cb_size b)) FB
      /\ blocks_apart FB
      /\ (exists canary : word, ssp_cells m canary)
      /\ rw_cells asegs m 0x60184b [C1 (Z_to_bv 8 0)]
      /\ rng0 RNG
      /\ Forall (fun b : cblk => ablk (cb_addr b) (cb_addr b + cb_size b)) FB.

  #[using="Type"] Lemma SX_real_sxa : forall (s : PS) RNG m, SX_real s RNG m -> SXA s RNG m.
  Proof. intros s RNG m (FB & ST & FBF & AP & SSP & NL & R0 & _). exists FB. repeat (split; [assumption|]). exact R0. Qed.

  (* [comment removed for export] *)
  Definition sx_dom (FB : list cblk) (a : Z) : Prop :=
    stdio_static a \/ in_block FB a \/ (got_ssp <= a < got_ssp + 8) \/ (ssp_guard <= a < ssp_guard + 8) \/ a = 0x60184b.

  #[using="Type"] Lemma sx_dom_outside : forall (FB : list cblk) sp a,
    Forall (fun b : cblk => ablk (cb_addr b) (cb_addr b + cb_size b)) FB -> ATOP + 4096 <= sp - 48 - MDTOR_DEPTH ->
    sx_dom FB a -> outside (AEXIT_W1 sp ++ MDTOR_W) a.
  Proof.
    intros FB sp a BAND HSP D. pose proof atop_range as AR.
    assert (K : (0xa6160 <= a < 0xa6168) \/ (0xa9ab0 <= a < 0xa9d80) \/ (0x6015f8 <= a < 0x601600) \/ a = 0x60184b \/ (0x601ca8 <= a < 0x6024d0)
                \/ (0x603000 <= a < 0x7fff7000) \/ (0x10007fff8000 <= a < ATOP)).
    { destruct D as [[D|D]|[D|[D|[D|D]]]]; unfold got_ssp, ssp_guard in *; try lia.
      apply in_block_In in D as (b & Hb & Rb). pose proof (proj1 (Forall_forall _ _) BAND b Hb) as AB. cbv beta in AB.
      unfold ablk, AIMG_HI, KLS in AB. lia. }
    unfold AEXIT_W1, MDTOR_W, SHW_LO, SHW_LEN, MDTOR_DEPTH in *. cbn [app outside]. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma SX_real_frame : forall (s : PS) RNG1 sp (m1 m' : mem), SX_real s RNG1 m1 -> (ATOP + 4096 <= sp - 48 - MDTOR_DEPTH)%Z ->
    munch (AEXIT_W1 sp ++ MDTOR_W) m1 m' -> wmono asegs m1 m' -> SX_real s RNG1 m'.
  Proof.
    intros s RNG1 sp m1 m' (FB & ST & FBF & AP & (can & SSP1 & SSP2) & NL & R0 & BAND) HSP MU WM.
    assert (AG : agrees_on (sx_dom FB) m1 m').
    { eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a _ D. exact (sx_dom_outside FB sp a BAND HSP D). }
    exists FB. split.
    { eapply STDIOR_agree_dom; [exact ST|]. eapply agrees_on_weaken; [exact AG|]. intros a [D|D]; [left; exact D| right; left; exact D]. }
    split; [exact FBF|]. split; [exact AP|]. split.
    { exists can. split.
      - eapply agrees_rw_cells; [exact AG| exact SSP1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. right; right; left. lia.
      - eapply agrees_rw_cells; [exact AG| exact SSP2|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. right; right; right; left. lia. }
    split.
    { eapply agrees_rw_cells; [exact AG| exact NL|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. right; right; right; right. lia. }
    split; [exact R0| exact BAND].
  Qed.

  (* [comment removed for export] *)
  Section OfGioa.
    Context (FO : @FrameOps H hptr).
    Variable GIOA : alayout -> footprint -> PS -> list cblk -> list cblk -> list fblock -> mem -> Prop.
    Variable fflagA : alayout -> fframe -> Z -> Z.
    Hypothesis GL : gia_laws FO GIOA fflagA.
    Hypothesis GSL : gia_stdio_laws GIOA.

    #[using="tlsI FO fflagA GL GSL"] Lemma SX_real_of_gioa : forall L RNG1 (s : PS) CL FB FL (m1 : mem), GIOA L RNG1 s CL FB FL m1 -> SX_real s RNG1 m1.
    Proof.
      intros L RNG1 s CL FB FL m1 G.
      assert (BL : forall b, In b FB -> blockA RNG1 m1 b).
      { intros b Hb. apply (gl_block _ _ _ GL _ _ _ _ _ _ _ b G). apply in_or_app. right. exact Hb. }
      exists FB. split; [exact (gs_stdio _ GSL _ _ _ _ _ _ _ G)|].
      split.
      { apply Forall_forall. intros b Hb. (nd_pre (BL b Hb) 5%nat; intros (AB & N0 & TOP & _) _ _ RB _; nd_post).
        pose proof (ablk_lin _ _ AB) as (IMG & _). unfold AIMG_HI in IMG. split; [lia|]. split; [exact TOP| exact RB]. }
      split. { exact (proj1 (proj2 (blocks_apart_app_inv _ _ (gl_apart _ _ _ GL _ _ _ _ _ _ _ G)))). }
      split. { destruct (gs_ssp _ GSL L) as [can HC]. exists can. exact (HC _ _ _ _ _ _ G). }
      split. { exact (proj2 (gs_libc _ GSL _ _ _ _ _ _ _ G)). }
      split. { exact (gs_rng0 _ GSL _ _ _ _ _ _ _ G). }
      apply Forall_forall. intros b Hb. destruct (BL b Hb) as ((AB & _) & _). exact AB.
    Qed.
  End OfGioa.

  (* [comment removed for export] *)
  #[using="Type"] Lemma stdio_exit_stmtA_anti : forall (model : Monad.M PS unit) (SX SX' : PS -> footprint -> mem -> Prop) (frame : Z),
    (forall s RNG m, SX' s RNG m -> SX s RNG m) -> stdio_exit_stmtA model SX frame -> stdio_exit_stmtA model SX' frame.
  Proof.
    intros model SX SX' frame IMP HS. unfold stdio_exit_stmtA in *. intros.
    eapply HS; try eassumption. apply IMP. assumption.
  Qed.
End SXInst.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.ExitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.F_module_dtorA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioLawsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioCompA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_exitA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section SXInst.
  Context {H hptr : Type}.
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation PS := (PState H hptr).

  (* [comment removed for export] *)
  Definition SX_real (s : PS) (RNG : footprint) (m : mem) : Prop :=
    exists FB : list cblk,
      STDIOR (ps_libc s) FB m
      /\ Forall (fun b : cblk => 0x604000 <= cb_addr b /\ cb_addr b + cb_size b <= ATOP /\ rng RNG (cb_addr b) (cb_size b)) FB
      /\ blocks_apart FB
      /\ (exists canary : word, ssp_cells m canary)
      /\ rw_cells asegs m 0x601c4b [C1 (Z_to_bv 8 0)]
      /\ rng0 RNG
      /\ Forall (fun b : cblk => ablk (cb_addr b) (cb_addr b + cb_size b)) FB.

  #[using="Type"] Lemma SX_real_sxa : forall (s : PS) RNG m, SX_real s RNG m -> SXA s RNG m.
  Proof. intros s RNG m (FB & ST & FBF & AP & SSP & NL & R0 & _). exists FB. repeat (split; [assumption|]). exact R0. Qed.

  (* [comment removed for export] *)
  Definition sx_dom (FB : list cblk) (a : Z) : Prop :=
    stdio_static a \/ in_block FB a \/ (got_ssp <= a < got_ssp + 8) \/ (ssp_guard <= a < ssp_guard + 8) \/ a = 0x601c4b.

  #[using="Type"] Lemma sx_dom_outside : forall (FB : list cblk) sp a,
    Forall (fun b : cblk => ablk (cb_addr b) (cb_addr b + cb_size b)) FB -> ATOP + 4096 <= sp - 48 - MDTOR_DEPTH ->
    sx_dom FB a -> outside (AEXIT_W1 sp ++ MDTOR_W) a.
  Proof.
    intros FB sp a BAND HSP D. pose proof atop_range as AR.
    assert (K : (0xa6540 <= a < 0xa6548) \/ (0xa9e90 <= a < 0xaa160) \/ (0x6019f8 <= a < 0x601a00) \/ a = 0x601c4b \/ (0x6020a8 <= a < 0x6028d0)
                \/ (0x604000 <= a < 0x7fff7000) \/ (0x10007fff8000 <= a < ATOP)).
    { destruct D as [[D|D]|[D|[D|[D|D]]]]; unfold got_ssp, ssp_guard in *; try lia.
      apply in_block_In in D as (b & Hb & Rb). pose proof (proj1 (Forall_forall _ _) BAND b Hb) as AB. cbv beta in AB.
      unfold ablk, AIMG_HI, KLS in AB. lia. }
    unfold AEXIT_W1, MDTOR_W, SHW_LO, SHW_LEN, MDTOR_DEPTH in *. cbn [app outside]. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma SX_real_frame : forall (s : PS) RNG1 sp (m1 m' : mem), SX_real s RNG1 m1 -> (ATOP + 4096 <= sp - 48 - MDTOR_DEPTH)%Z ->
    munch (AEXIT_W1 sp ++ MDTOR_W) m1 m' -> wmono asegs m1 m' -> SX_real s RNG1 m'.
  Proof.
    intros s RNG1 sp m1 m' (FB & ST & FBF & AP & (can & SSP1 & SSP2) & NL & R0 & BAND) HSP MU WM.
    assert (AG : agrees_on (sx_dom FB) m1 m').
    { eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a _ D. exact (sx_dom_outside FB sp a BAND HSP D). }
    exists FB. split.
    { eapply STDIOR_agree_dom; [exact ST|]. eapply agrees_on_weaken; [exact AG|]. intros a [D|D]; [left; exact D| right; left; exact D]. }
    split; [exact FBF|]. split; [exact AP|]. split.
    { exists can. split.
      - eapply agrees_rw_cells; [exact AG| exact SSP1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. right; right; left. lia.
      - eapply agrees_rw_cells; [exact AG| exact SSP2|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. right; right; right; left. lia. }
    split.
    { eapply agrees_rw_cells; [exact AG| exact NL|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. right; right; right; right. lia. }
    split; [exact R0| exact BAND].
  Qed.

  (* [comment removed for export] *)
  Section OfGioa.
    Context (FO : @FrameOps H hptr).
    Variable GIOA : alayout -> footprint -> PS -> list cblk -> list cblk -> list fblock -> mem -> Prop.
    Variable fflagA : alayout -> fframe -> Z -> Z.
    Hypothesis GL : gia_laws FO GIOA fflagA.
    Hypothesis GSL : gia_stdio_laws GIOA.

    #[using="tlsI FO fflagA GL GSL"] Lemma SX_real_of_gioa : forall L RNG1 (s : PS) CL FB FL (m1 : mem), GIOA L RNG1 s CL FB FL m1 -> SX_real s RNG1 m1.
    Proof.
      intros L RNG1 s CL FB FL m1 G.
      assert (BL : forall b, In b FB -> blockA RNG1 m1 b).
      { intros b Hb. apply (gl_block _ _ _ GL _ _ _ _ _ _ _ b G). apply in_or_app. right. exact Hb. }
      exists FB. split; [exact (gs_stdio _ GSL _ _ _ _ _ _ _ G)|].
      split.
      { apply Forall_forall. intros b Hb. (nd_pre (BL b Hb) 5%nat; intros (AB & N0 & TOP & _) _ _ RB _; nd_post).
        pose proof (ablk_lin _ _ AB) as (IMG & _). unfold AIMG_HI in IMG. split; [lia|]. split; [exact TOP| exact RB]. }
      split. { exact (proj1 (proj2 (blocks_apart_app_inv _ _ (gl_apart _ _ _ GL _ _ _ _ _ _ _ G)))). }
      split. { destruct (gs_ssp _ GSL L) as [can HC]. exists can. exact (HC _ _ _ _ _ _ G). }
      split. { exact (proj2 (gs_libc _ GSL _ _ _ _ _ _ _ G)). }
      split. { exact (gs_rng0 _ GSL _ _ _ _ _ _ _ G). }
      apply Forall_forall. intros b Hb. destruct (BL b Hb) as ((AB & _) & _). exact AB.
    Qed.
  End OfGioa.

  (* [comment removed for export] *)
  #[using="Type"] Lemma stdio_exit_stmtA_anti : forall (model : Monad.M PS unit) (SX SX' : PS -> footprint -> mem -> Prop) (frame : Z),
    (forall s RNG m, SX' s RNG m -> SX s RNG m) -> stdio_exit_stmtA model SX frame -> stdio_exit_stmtA model SX' frame.
  Proof.
    intros model SX SX' frame IMP HS. unfold stdio_exit_stmtA in *. intros.
    eapply HS; try eassumption. apply IMP. assumption.
  Qed.
End SXInst.
End CANSEC1.
End TwB.
