(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw ExecF ITreeA Shadow StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABase AMalloc_iface RtCells. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require MonadF. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_cs__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_lock__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_read__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA Stdio_glueKitA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_lock OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdio_cs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_read__A3S.F_stdio_read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_toread OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fflush OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_read__A3S.F_stdio_exit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueKitA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require DrvKitA__A3D. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.ExitA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition STDIO_EXIT_FRAME : Z := 160.    (* [comment removed for export] *)

Section GlueExit.
  Context {rc : runConstT} {tlsI : ABase.atlsT}.
  Context {H hptr : Type}.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).

  (* [comment removed for export] *)
  Definition SXA (s : PS) (RNG : footprint) (m : mem) : Prop :=
    exists FB : list cblk,
      STDIOR (ps_libc s) FB m
      /\ Forall (fun b : cblk => 0x603000 <= cb_addr b /\ cb_addr b + cb_size b <= ATOP /\ rng RNG (cb_addr b) (cb_size b)) FB
      /\ blocks_apart FB
      /\ (exists canary : word, ssp_cells m canary)
      /\ rw_cells asegs m 0x60184b [C1 (Z_to_bv 8 0)]
      /\ rng0 RNG.

  (* [comment removed for export] *)
  #[local] Definition Pstat (sp : word) (a : Z) : Prop := stdio_static a \/ (bv_unsigned sp - 16 <= a < bv_unsigned sp).

  (* [comment removed for export] *)
  Definition loop_post (sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (st : PS) (J : Z) (lo : Z) (canary : word) (m : mem) : unit -> PS -> machine_state -> Prop :=
    fun _ st' ms' => st' = st /\
      exists (x1 t0 t1 t2 s0' a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0' s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 J) fc None m' (seg_rom asegs)
      /\ agrees_on (Pstat sp) m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + -16) /\ ssp_cells m' canary.

  (* [comment removed for export] *)
  Lemma exit_loop : forall fs (FB : list cblk) (prev : Z) (mi : mem) RNG (sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (st : PS) (lo : Z) (canary : word) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    files_R mi prev fs FB -> List.NoDup (map fst fs) ->
    Forall (fun b : cblk => 0x603000 <= cb_addr b /\ cb_addr b + cb_size b <= ATOP /\ rng RNG (cb_addr b) (cb_size b)) FB -> blocks_apart FB ->
    stk asegs mi lo (bv_unsigned sp + -16) -> lo <= bv_unsigned sp - STDIO_EXIT_FRAME -> ATOP + 4096 <= lo ->
    bv_unsigned sp <= 2^47 ->
    ssp_cells mi canary -> mem_inv asegs mi ->
    rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng0 RNG ->
    implAM RNG (close_files fs) st
      (loop_post sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st 0x9a5cc lo canary mi)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 (hd_addr FB)) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (if hd_addr FB =? 0 then 0x9a5cc else EXIT_LOOP)) fc None mi (seg_rom asegs)).
  Proof using Type. pin_using tt.
    induction fs as [|[q f] fs IH]; intros FB prev mi RNG sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st lo canary x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
      FS ND BO BA ST LO CLO SP47 SSP MI RSTK RIMG R0.
    - destruct FB as [|b FB']; [| exact (False_ind _ FS)]. cbn [hd_addr]. rewrite Z.eqb_refl. cbn [close_files].
      apply implAM_ret. apply evtF_done. split; [reflexivity|]. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. split; [intros a Ha Hp; split; [reflexivity| intros X; exact X]|]. split; [exact MI|]. split; [exact ST| exact SSP].
    - destruct FB as [|[[q' A] n] FB']; [exact (False_ind _ FS)|].
      cbn [files_R] in FS. destruct FS as (<- & -> & A0 & Ahi & FR & INV & REST).
      cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
      apply Forall_cons_iff in BO as [(K1 & K2 & K3) BO]. unfold cb_addr, cb_size, FILE_ALLOC in K1, K2, K3. cbn [fst snd] in K1, K2, K3.
      cbn [blocks_apart] in BA. destruct BA as [APA BA].
      cbn [hd_addr]. replace (A =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      pose proof (@ATOP_lo rc) as ATL.
      destruct FR as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP0 & RPHI & GLN).
      pose proof FL as (FLn & FLw & FLe & FLerr & FLsvb & FLperm).
      pose proof INV as (ICH & IFD & IBS & INN & INW & INR & IRB).
      unfold STDIO_EXIT_FRAME in LO.
      cbn [close_files].
      remember (Z_to_bv 64 (bv_unsigned sp + -16) : word) as sp0 eqn:Esp0.
      assert (Hsp : bv_unsigned sp0 = bv_unsigned sp + -16) by (rewrite Esp0; apply unsigned_lit; lia).
      assert (RSTK0 : rng RNG lo (bv_unsigned sp0 - lo)) by (eapply rng_sub'; [exact RSTK | lia]).
      assert (RFP : rng RNG A 232) by (eapply rng_sub'; [exact K3 | lia]).
      assert (RBUF : rng RNG (A + FILE_BUF_OFF) (f_bufsize f)) by (rewrite IBS; unfold BUFSIZ, FILE_BUF_OFF; eapply rng_sub'; [exact K3 | lia]).
      eapply implAM_bind.
      { eapply (exit_body RNG sp0 gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st A flags F_STDIO_CLOSE F_STDIO_READ (A + FILE_BUF_OFF) prev (hd_addr FB') tail lo canary mi);
          rewrite ?Hsp; first [ exact FC | exact FLsvb | exact BUF | exact BP | exact WB0 | exact WBL | (intros _; exact ICH) | exact RP0 | exact RPHI
                               | (rewrite ICH; exact IFD) | exact ST | exact SSP | exact MI | exact RFP | exact RIMG | exact RBUF | exact R0
                               | (rewrite <- Hsp; exact RSTK0)
                               | (rewrite ?IBS; unfold EXIT_DEPTH, BUFSIZ, FILE_BUF_OFF, got_ssp, ssp_guard; lia)
                               | match goal with |- ?g => idtac "XB side:" g end ]. }
      cbv beta. intros [] st1 ms1 (-> & PO).
      destruct PO as (x1' & v0 & v1 & v2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & v3 & v4 & v5 & v6 & m' & -> & MU & WM & MI' & ST' & NXC & SSP').
      rewrite Hsp in ST'. unfold ex_W, EXIT_DEPTH in MU. rewrite Hsp in MU.
      (* [comment removed for export] *)
      assert (HDR' : 0 <= hd_addr FB' < 2^64).
      { destruct FB' as [|[[q2 A2] n2] FB'']; cbn [hd_addr]; [lia|].
        destruct fs as [|[q2' f2] fs']; [exact (False_ind _ REST)|]. cbn [files_R] in REST. destruct REST as (_ & _ & A20 & A2hi & _). unfold FILE_ALLOC in A2hi. lia. }
      eapply implAM_evt. { eapply (exit_next RNG sp0 gp tp); [exact NXC | lia | lia | exact HDR' | exact MI' | eapply rng_sub'; [exact K3 | lia]]. }
      cbv beta. intros ms2 ->. rewrite Esp0.
      (* [comment removed for export] *)
      assert (AG : agrees_on (fun a => ~ (bv_unsigned sp - 16 - 144 <= a < bv_unsigned sp - 16) /\ ~ (A <= a < A + 232)) mi m').
      { eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha [N1 N2]. cbn [outside]. repeat split; lia. }
      assert (BKR : forall qb Ab nb, In (qb, Ab, nb) FB' -> 0x603000 <= Ab /\ Ab + nb <= ATOP /\ (A + 1264 <= Ab \/ Ab + nb <= A)).
      { intros qb Ab nb HbIn.
        pose proof (proj1 (Forall_forall _ _) BO _ HbIn) as (J1 & J2 & _). unfold cb_addr, cb_size in J1, J2. cbn [fst snd] in J1, J2.
        pose proof (proj1 (Forall_forall _ _) APA _ HbIn) as AP. unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP. lia. }
      assert (REST' : files_R m' A fs FB').
      { eapply files_R_agree; [exact REST| exact AG|]. intros a Hin.
        apply in_block_In in Hin as ([[qb Ab] nb] & HbIn & Hb). unfold cb_addr, cb_size in Hb. cbn [fst snd] in Hb.
        destruct (BKR _ _ _ HbIn) as (J1 & J2 & J3). lia. }
      eapply implAM_mono.
      { eapply (IH FB' A m' RNG); [exact REST'| exact ND| exact BO| exact BA| exact ST'| unfold STDIO_EXIT_FRAME; lia| exact CLO| exact SP47| exact SSP'| exact MI' | exact RSTK | exact RIMG | exact R0]. }
      cbv beta. intros [] st2 ms3 (-> & PO). destruct_exs PO. destruct PO as (-> & AG2 & MI2 & ST2 & SSP2).
      split; [reflexivity|]. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. split; [| split; [exact MI2| split; [exact ST2| exact SSP2]]].
      eapply agrees_on_trans; [| exact AG2]. eapply agrees_on_weaken; [exact AG|].
      intros a [Hs|Hs]; [| lia]. unfold stdio_static in Hs. lia.
  Qed.

  Lemma implAM_rd_lc : forall {B} RNG (k : libc_st hptr -> M PS B) (s : PS) Q ms,
    implAM RNG (k (ps_libc s)) s Q ms -> implAM RNG (mbind (rd_lc ps_libc) k) s Q ms.
  Proof using Type. pin_using tt. intros B RNG k s Q ms IM. exact IM. Qed.
  Lemma implAM_implMG_x : forall {A} RNG (c : M PS A) (s : PS) (Q : A -> PS -> machine_state -> Prop) ms,
    implAM RNG c s Q ms -> implMG RNG c s (fun a s' RNG' ms' => RNG' = RNG /\ Q a s' ms') ms.
  Proof using Type. pin_using tt. intros A RNG c s Q ms IM. exact IM. Qed.

  Definition stdio_exit_proofA__stmt : Prop := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.ExitA.stdio_exit_stmtA (s_stdio_exit (H:=H) (hptr:=hptr)) SXA STDIO_EXIT_FRAME.
  Section Sz4.
  Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo s : ltac2:(SecDiet.SzSec.tyM 'stdio_exit_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  Lemma stdio_exit_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'stdio_exit_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
 intros ST SX MI LO LOA SP47 SPAL -> RSTK RIMG RIMGSH RTLS.
    destruct SX as (FB & SR & BKS & BA & (canary & SSP) & NL & R0).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (@ATOP_lo rc) as ATL.
    unfold STDIO_EXIT_FRAME in LO.
    assert (GLO : 0x603000 <= lo) by lia.
    assert (HDR : 0 <= hd_addr FB < 2^64).
    { destruct FB as [|[[q1 A1] n1] FB']; cbn [hd_addr]; [lia|].
      destruct (lc_files (ps_libc s)) as [|[q1' f1] fs']; [exact (False_ind _ FS)|]. cbn [files_R] in FS. destruct FS as (_ & _ & A10 & A1hi & _). unfold FILE_ALLOC in A1hi. lia. }
    eapply implMG_mono with (Q := fun a s' RNG' ms' => RNG' = RNG /\ stdio_exit_post ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a s' RNG ms').
    2:{ intros a s' RNG' ms' [-> X]. exact X. }
    apply (implAM_implMG_x RNG).
    unfold s_stdio_exit, Stdio.stdio_exit. apply implAM_rd_lc.
    (* [comment removed for export] *)
    eapply implAM_evt.
    { eapply (exit_entry RNG ra sp gp (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (hd_addr FB) lo m);
        [exact OH | exact HDR | exact NL | exact ST | lia | lia | exact MI | exact RSTK | exact RIMG]. }
    cbv beta. intros ms1 PO. destruct PO as (x1 & b0 & b1 & b2 & b3 & m1 & -> & FR1 & MU1 & WM1 & MI1 & ST1).
    assert (AG1 : agrees_on (fun a => a < bv_unsigned sp - 32 \/ bv_unsigned sp <= a) m m1).
    { eapply agrees_on_of_munch; [exact MU1| exact WM1|]. intros a Ha Hp. cbn [outside]. split; [lia| exact I]. }
    assert (BKF : forall a, in_block FB a -> 0x603000 <= a < ATOP).
    { intros a Ha. apply in_block_In in Ha as (b & Hb & Rb). pose proof (proj1 (Forall_forall _ _) BKS _ Hb) as (J1 & J2 & _). lia. }
    assert (FS1 : files_R m1 0 (lc_files (ps_libc s)) FB).
    { eapply files_R_agree; [exact FS| exact AG1| intros a Ha; destruct (BKF a Ha); lia]. }
    assert (SSP1 : ssp_cells m1 canary).
    { destruct SSP as [G1 G2]. split; (eapply rw_cells_transport; [eassumption| exact MU1| exact WM1| unfold got_ssp, ssp_guard; cbn [disjoint_from cells_size csize Nat.add]; lia]). }
    (* [comment removed for export] *)
    eapply implAM_bind.
    { eapply (exit_loop (lc_files (ps_libc s)) FB 0 m1 RNG sp gp (Z_to_bv 64 ATP) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s lo canary);
        [exact FS1| exact ND| exact BKS| exact BA| exact ST1| unfold STDIO_EXIT_FRAME; lia| exact LOA| exact SP47| exact SSP1| exact MI1| exact RSTK| exact RIMG| exact R0]. }
    cbv beta. intros [] st2 ms2 (-> & PO). destruct_exs PO. destruct PO as (-> & AG2 & MI2 & ST2 & SSP2).
    lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
    (* [comment removed for export] *)
    assert (AG02 : agrees_on stdio_static m m2).
    { eapply agrees_on_trans; [| eapply agrees_on_weaken; [exact AG2| intros a Ha; left; exact Ha]].
      eapply agrees_on_weaken; [exact AG1|]. intros a Hs. unfold stdio_static in Hs. lia. }
    assert (U22 : rw_cells asegs m2 A_STDIN_USED [C8 (Z_to_bv 64 A_STDIN)])
      by (eapply agrees_rw_cells; [exact AG02 | exact U2 | intros a Ha; unfold stdio_static, A_STDIN_USED in *; sl_lit_sizes_in Ha; cbn in Ha; lia]).
    assert (U32 : rw_cells asegs m2 A_STDOUT_USED [C8 (Z_to_bv 64 A_STDOUT)])
      by (eapply agrees_rw_cells; [exact AG02 | exact U3 | intros a Ha; unfold stdio_static, A_STDOUT_USED in *; sl_lit_sizes_in Ha; cbn in Ha; lia]).
    assert (SIN2 : rw_cells asegs m2 A_STDIN stdin_cells).
    { eapply agrees_rw_cells; [exact AG02| exact SIN|]. unfold stdin_cells. rewrite file_cells_size. intros a Ha. unfold stdio_static, A_STDIN in *. lia. }
    pose proof SOI as (OCH & OFD & OBS & ONRD & ONWR & OEOF & ORB & _).
    assert (SO2 : FILE_R m2 (lc_stdout (ps_libc s)) A_STDOUT A_STDOUT_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0).
    { eapply FILE_R_agree; [exact SO| exact AG02| |]; intros a Ha; unfold stdio_static, A_STDOUT, A_STDOUT_BUF in *; [lia|]. rewrite OBS in Ha. unfold BUFSIZ in Ha. lia. }
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -16) [C8 s0; C8 ra]).
    { eapply agrees_rw_cells; [exact AG2| exact FR1|]. intros a Ha. right. cbn in Ha. lia. }
    (* [comment removed for export] *)
    eapply implAM_evt. { eapply (exit_stdin RNG (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 ATP)); [exact U22| exact SIN2| exact MI2| exact RIMG]. }
    cbv beta. intros ms3 (c0 & c1 & ->).
    (* [comment removed for export] *)
    destruct SO2 as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP0 & RPHI & GLN).
    pose proof FL as (FLn & FLw & FLe & FLerr & FLsvb & FLperm).
    remember (Z_to_bv 64 (bv_unsigned sp + -16) : word) as sp0 eqn:Esp0.
    assert (Hsp : bv_unsigned sp0 = bv_unsigned sp + -16) by (rewrite Esp0; apply unsigned_lit; lia).
    assert (RSTK0 : rng RNG lo (bv_unsigned sp0 - lo)) by (eapply rng_sub'; [exact RSTK | lia]).
    eapply implAM_bind.
    { eapply (exit_stdout RNG sp0 gp (Z_to_bv 64 ATP)) with (f := lc_stdout (ps_libc s)) (lo := lo) (canary := canary) (flags := flags) (mode := mode) (rp := rp) (tail := tail) (bufbytes := bufbytes) (m := m2) (st := s);
        rewrite ?Hsp; first [ exact U32 | exact FC | exact FLsvb | exact BUF | exact BP | exact WB0 | exact ORB | exact OCH | exact OBS | exact WBL | exact ST2 | exact SSP2 | exact MI2
                             | exact RIMG | exact R0 | (rewrite <- Hsp; exact RSTK0)
                             | (rewrite OFD; left; reflexivity) | (unfold EXIT_DEPTH; lia) | (unfold zlength in *; lia)
                             | match goal with |- ?g => idtac "XO side:" g end ]. }
    cbv beta. intros [] st4 ms4 (-> & PO). destruct_exs PO. destruct PO as (-> & MU4 & WM4 & MI4 & ST4 & SSP4).
    lazymatch type of MI4 with mem_inv _ ?mm => rename mm into m4 end.
    rewrite Hsp in ST4. unfold ex_W, EXIT_DEPTH in MU4. rewrite Hsp in MU4. rewrite Esp0.
    (* [comment removed for export] *)
    pose proof SEI as (ECH & EFD & EBS & ENRD & ENWR & EEOF & ERB & _).
    assert (SE4 : FILE_R m4 (lc_stderr (ps_libc s)) A_STDERR A_STDERR_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0).
    { eapply FILE_R_agree; [exact SE| |intros a Ha; exact Ha| intros a Ha; rewrite EBS in Ha; lia].
      eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG02| intros a Ha; unfold stdio_static, A_STDERR in *; lia]|].
      eapply agrees_on_of_munch; [exact MU4| exact WM4|]. intros a Ha Hp. unfold A_STDERR, A_STDOUT in *. cbn [outside]. lia. }
    assert (U14 : rw_cells asegs m4 A_STDERR_USED [C8 (Z_to_bv 64 A_STDERR)]).
    { eapply rw_cells_transport; [eapply agrees_rw_cells; [exact AG02 | exact U1 | intros a Ha; unfold stdio_static, A_STDERR_USED in *; sl_lit_sizes_in Ha; cbn in Ha; lia] | exact MU4| exact WM4| unfold A_STDERR_USED, A_STDOUT; cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    assert (FR4 : rw_cells asegs m4 (bv_unsigned sp + -16) [C8 s0; C8 ra]).
    { eapply rw_cells_transport; [exact FR2| exact MU4| exact WM4| unfold A_STDOUT; cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    destruct SE4 as (flags' & mode' & rp' & tail' & bufbytes' & FC' & FL' & BUF' & BP' & WB0' & WBL' & RR' & RP0' & RPHI' & GLN').
    assert (EWB : f_wbuf (lc_stderr (ps_libc s)) = []).
    { destruct (f_wbuf (lc_stderr (ps_libc s))) eqn:E; [reflexivity|]. exfalso. rewrite EBS in WBL'. unfold zlength in WBL'. cbn in WBL'. lia. }
    unfold close_file. rewrite EWB. apply implAM_retb. unfold sync_read_pos. rewrite ERB. apply implAM_ret.
    eapply evtF_mono.
    { eapply (exit_stderr RNG ra sp gp (Z_to_bv 64 ATP)) with (f := lc_stderr (ps_libc s)) (lo := lo); first
        [ exact U14 | exact FC' | exact EWB | exact ERB | exact FR4 | exact ST4 | exact MI4 | exact RSTK | exact RIMG | lia | (unfold zlength in *; lia)
        | match goal with |- ?g => idtac "XE side:" g end ]. }
    cbv beta. intros ms5 (d0 & d1 & -> & ST5).
    unfold stdio_exit_post. repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity | exact RIMG].
  Qed.
  End Sz4.
  Theorem stdio_exit_proofA : ltac:(let t := eval cbv delta [stdio_exit_proofA__stmt] in stdio_exit_proofA__stmt in exact t).
  Proof using Type. unfold stdio_exit_stmtA. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo s. ltac2:(SecDiet.SzSec.closeP 'stdio_exit_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End GlueExit.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_lock.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdio_cs.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_read__A3S.F_stdio_read.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_toread.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fflush.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_read__A3S.F_stdio_exit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueKitA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.ExitA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition STDIO_EXIT_FRAME : Z := 160.    (* [comment removed for export] *)

Section GlueExit.
  Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
  Context {H hptr : Type}.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).

  (* [comment removed for export] *)
  Definition SXA (s : PS) (RNG : footprint) (m : mem) : Prop :=
    exists FB : list cblk,
      STDIOR (ps_libc s) FB m
      /\ Forall (fun b : cblk => 0x604000 <= cb_addr b /\ cb_addr b + cb_size b <= ATOP /\ rng RNG (cb_addr b) (cb_size b)) FB
      /\ blocks_apart FB
      /\ (exists canary : word, ssp_cells m canary)
      /\ rw_cells asegs m 0x601c4b [C1 (Z_to_bv 8 0)]
      /\ rng0 RNG.

  (* [comment removed for export] *)
  #[local] Definition Pstat (sp : word) (a : Z) : Prop := stdio_static a \/ (bv_unsigned sp - 16 <= a < bv_unsigned sp).

  (* [comment removed for export] *)
  Definition loop_post (sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (st : PS) (J : Z) (lo : Z) (canary : word) (m : mem) : unit -> PS -> machine_state -> Prop :=
    fun _ st' ms' => st' = st /\
      exists (x1 t0 t1 t2 s0' a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0' s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 J) fc None m' (seg_rom asegs)
      /\ agrees_on (Pstat sp) m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + -16) /\ ssp_cells m' canary.

  (* [comment removed for export] *)
  Lemma exit_loop : forall fs (FB : list cblk) (prev : Z) (mi : mem) RNG (sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (st : PS) (lo : Z) (canary : word) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    files_R mi prev fs FB -> List.NoDup (map fst fs) ->
    Forall (fun b : cblk => 0x604000 <= cb_addr b /\ cb_addr b + cb_size b <= ATOP /\ rng RNG (cb_addr b) (cb_size b)) FB -> blocks_apart FB ->
    stk asegs mi lo (bv_unsigned sp + -16) -> lo <= bv_unsigned sp - STDIO_EXIT_FRAME -> ATOP + 4096 <= lo ->
    bv_unsigned sp <= 2^47 ->
    ssp_cells mi canary -> mem_inv asegs mi ->
    rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng0 RNG ->
    implAM RNG (close_files fs) st
      (loop_post sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st 0x9a9b0 lo canary mi)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 (hd_addr FB)) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (if hd_addr FB =? 0 then 0x9a9b0 else EXIT_LOOP)) fc None mi (seg_rom asegs)).
  Proof using Type. pin_using tt.
    induction fs as [|[q f] fs IH]; intros FB prev mi RNG sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st lo canary x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
      FS ND BO BA ST LO CLO SP47 SSP MI RSTK RIMG R0.
    - destruct FB as [|b FB']; [| exact (False_ind _ FS)]. cbn [hd_addr]. rewrite Z.eqb_refl. cbn [close_files].
      apply implAM_ret. apply evtF_done. split; [reflexivity|]. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. split; [intros a Ha Hp; split; [reflexivity| intros X; exact X]|]. split; [exact MI|]. split; [exact ST| exact SSP].
    - destruct FB as [|[[q' A] n] FB']; [exact (False_ind _ FS)|].
      cbn [files_R] in FS. destruct FS as (<- & -> & A0 & Ahi & FR & INV & REST).
      cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
      apply Forall_cons_iff in BO as [(K1 & K2 & K3) BO]. unfold cb_addr, cb_size, FILE_ALLOC in K1, K2, K3. cbn [fst snd] in K1, K2, K3.
      cbn [blocks_apart] in BA. destruct BA as [APA BA].
      cbn [hd_addr]. replace (A =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      pose proof (@ATOP_lo rc) as ATL.
      destruct FR as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP0 & RPHI & GLN).
      pose proof FL as (FLn & FLw & FLe & FLerr & FLsvb & FLperm).
      pose proof INV as (ICH & IFD & IBS & INN & INW & INR & IRB).
      unfold STDIO_EXIT_FRAME in LO.
      cbn [close_files].
      remember (Z_to_bv 64 (bv_unsigned sp + -16) : word) as sp0 eqn:Esp0.
      assert (Hsp : bv_unsigned sp0 = bv_unsigned sp + -16) by (rewrite Esp0; apply unsigned_lit; lia).
      assert (RSTK0 : rng RNG lo (bv_unsigned sp0 - lo)) by (eapply rng_sub'; [exact RSTK | lia]).
      assert (RFP : rng RNG A 232) by (eapply rng_sub'; [exact K3 | lia]).
      assert (RBUF : rng RNG (A + FILE_BUF_OFF) (f_bufsize f)) by (rewrite IBS; unfold BUFSIZ, FILE_BUF_OFF; eapply rng_sub'; [exact K3 | lia]).
      eapply implAM_bind.
      { eapply (exit_body RNG sp0 gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st A flags F_STDIO_CLOSE F_STDIO_READ (A + FILE_BUF_OFF) prev (hd_addr FB') tail lo canary mi);
          rewrite ?Hsp; first [ exact FC | exact FLsvb | exact BUF | exact BP | exact WB0 | exact WBL | (intros _; exact ICH) | exact RP0 | exact RPHI
                               | (rewrite ICH; exact IFD) | exact ST | exact SSP | exact MI | exact RFP | exact RIMG | exact RBUF | exact R0
                               | (rewrite <- Hsp; exact RSTK0)
                               | (rewrite ?IBS; unfold EXIT_DEPTH, BUFSIZ, FILE_BUF_OFF, got_ssp, ssp_guard; lia)
                               | match goal with |- ?g => idtac "XB side:" g end ]. }
      cbv beta. intros [] st1 ms1 (-> & PO).
      destruct PO as (x1' & v0 & v1 & v2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & v3 & v4 & v5 & v6 & m' & -> & MU & WM & MI' & ST' & NXC & SSP').
      rewrite Hsp in ST'. unfold ex_W, EXIT_DEPTH in MU. rewrite Hsp in MU.
      (* [comment removed for export] *)
      assert (HDR' : 0 <= hd_addr FB' < 2^64).
      { destruct FB' as [|[[q2 A2] n2] FB'']; cbn [hd_addr]; [lia|].
        destruct fs as [|[q2' f2] fs']; [exact (False_ind _ REST)|]. cbn [files_R] in REST. destruct REST as (_ & _ & A20 & A2hi & _). unfold FILE_ALLOC in A2hi. lia. }
      eapply implAM_evt. { eapply (exit_next RNG sp0 gp tp); [exact NXC | lia | lia | exact HDR' | exact MI' | eapply rng_sub'; [exact K3 | lia]]. }
      cbv beta. intros ms2 ->. rewrite Esp0.
      (* [comment removed for export] *)
      assert (AG : agrees_on (fun a => ~ (bv_unsigned sp - 16 - 144 <= a < bv_unsigned sp - 16) /\ ~ (A <= a < A + 232)) mi m').
      { eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha [N1 N2]. cbn [outside]. repeat split; lia. }
      assert (BKR : forall qb Ab nb, In (qb, Ab, nb) FB' -> 0x604000 <= Ab /\ Ab + nb <= ATOP /\ (A + 1264 <= Ab \/ Ab + nb <= A)).
      { intros qb Ab nb HbIn.
        pose proof (proj1 (Forall_forall _ _) BO _ HbIn) as (J1 & J2 & _). unfold cb_addr, cb_size in J1, J2. cbn [fst snd] in J1, J2.
        pose proof (proj1 (Forall_forall _ _) APA _ HbIn) as AP. unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP. lia. }
      assert (REST' : files_R m' A fs FB').
      { eapply files_R_agree; [exact REST| exact AG|]. intros a Hin.
        apply in_block_In in Hin as ([[qb Ab] nb] & HbIn & Hb). unfold cb_addr, cb_size in Hb. cbn [fst snd] in Hb.
        destruct (BKR _ _ _ HbIn) as (J1 & J2 & J3). lia. }
      eapply implAM_mono.
      { eapply (IH FB' A m' RNG); [exact REST'| exact ND| exact BO| exact BA| exact ST'| unfold STDIO_EXIT_FRAME; lia| exact CLO| exact SP47| exact SSP'| exact MI' | exact RSTK | exact RIMG | exact R0]. }
      cbv beta. intros [] st2 ms3 (-> & PO). destruct_exs PO. destruct PO as (-> & AG2 & MI2 & ST2 & SSP2).
      split; [reflexivity|]. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. split; [| split; [exact MI2| split; [exact ST2| exact SSP2]]].
      eapply agrees_on_trans; [| exact AG2]. eapply agrees_on_weaken; [exact AG|].
      intros a [Hs|Hs]; [| lia]. unfold stdio_static in Hs. lia.
  Qed.

  Lemma implAM_rd_lc : forall {B} RNG (k : libc_st hptr -> M PS B) (s : PS) Q ms,
    implAM RNG (k (ps_libc s)) s Q ms -> implAM RNG (mbind (rd_lc ps_libc) k) s Q ms.
  Proof using Type. pin_using tt. intros B RNG k s Q ms IM. exact IM. Qed.
  Lemma implAM_implMG_x : forall {A} RNG (c : M PS A) (s : PS) (Q : A -> PS -> machine_state -> Prop) ms,
    implAM RNG c s Q ms -> implMG RNG c s (fun a s' RNG' ms' => RNG' = RNG /\ Q a s' ms') ms.
  Proof using Type. pin_using tt. intros A RNG c s Q ms IM. exact IM. Qed.

  Definition stdio_exit_proofA__stmt : Prop := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.ExitA.TwB.stdio_exit_stmtA (s_stdio_exit (H:=H) (hptr:=hptr)) SXA STDIO_EXIT_FRAME.
  Section Sz4.
  Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo s : ltac2:(SecDiet.SzSec.tyM 'stdio_exit_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  Lemma stdio_exit_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'stdio_exit_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
 intros ST SX MI LO LOA SP47 SPAL -> RSTK RIMG RIMGSH RTLS.
    destruct SX as (FB & SR & BKS & BA & (canary & SSP) & NL & R0).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (@ATOP_lo rc) as ATL.
    unfold STDIO_EXIT_FRAME in LO.
    assert (GLO : 0x604000 <= lo) by lia.
    assert (HDR : 0 <= hd_addr FB < 2^64).
    { destruct FB as [|[[q1 A1] n1] FB']; cbn [hd_addr]; [lia|].
      destruct (lc_files (ps_libc s)) as [|[q1' f1] fs']; [exact (False_ind _ FS)|]. cbn [files_R] in FS. destruct FS as (_ & _ & A10 & A1hi & _). unfold FILE_ALLOC in A1hi. lia. }
    eapply implMG_mono with (Q := fun a s' RNG' ms' => RNG' = RNG /\ stdio_exit_post ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a s' RNG ms').
    2:{ intros a s' RNG' ms' [-> X]. exact X. }
    apply (implAM_implMG_x RNG).
    unfold s_stdio_exit, Stdio.stdio_exit. apply implAM_rd_lc.
    (* [comment removed for export] *)
    eapply implAM_evt.
    { eapply (exit_entry RNG ra sp gp (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (hd_addr FB) lo m);
        [exact OH | exact HDR | exact NL | exact ST | lia | lia | exact MI | exact RSTK | exact RIMG]. }
    cbv beta. intros ms1 PO. destruct PO as (x1 & b0 & b1 & b2 & b3 & m1 & -> & FR1 & MU1 & WM1 & MI1 & ST1).
    assert (AG1 : agrees_on (fun a => a < bv_unsigned sp - 32 \/ bv_unsigned sp <= a) m m1).
    { eapply agrees_on_of_munch; [exact MU1| exact WM1|]. intros a Ha Hp. cbn [outside]. split; [lia| exact I]. }
    assert (BKF : forall a, in_block FB a -> 0x604000 <= a < ATOP).
    { intros a Ha. apply in_block_In in Ha as (b & Hb & Rb). pose proof (proj1 (Forall_forall _ _) BKS _ Hb) as (J1 & J2 & _). lia. }
    assert (FS1 : files_R m1 0 (lc_files (ps_libc s)) FB).
    { eapply files_R_agree; [exact FS| exact AG1| intros a Ha; destruct (BKF a Ha); lia]. }
    assert (SSP1 : ssp_cells m1 canary).
    { destruct SSP as [G1 G2]. split; (eapply rw_cells_transport; [eassumption| exact MU1| exact WM1| unfold got_ssp, ssp_guard; cbn [disjoint_from cells_size csize Nat.add]; lia]). }
    (* [comment removed for export] *)
    eapply implAM_bind.
    { eapply (exit_loop (lc_files (ps_libc s)) FB 0 m1 RNG sp gp (Z_to_bv 64 ATP) s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s lo canary);
        [exact FS1| exact ND| exact BKS| exact BA| exact ST1| unfold STDIO_EXIT_FRAME; lia| exact LOA| exact SP47| exact SSP1| exact MI1| exact RSTK| exact RIMG| exact R0]. }
    cbv beta. intros [] st2 ms2 (-> & PO). destruct_exs PO. destruct PO as (-> & AG2 & MI2 & ST2 & SSP2).
    lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
    (* [comment removed for export] *)
    assert (AG02 : agrees_on stdio_static m m2).
    { eapply agrees_on_trans; [| eapply agrees_on_weaken; [exact AG2| intros a Ha; left; exact Ha]].
      eapply agrees_on_weaken; [exact AG1|]. intros a Hs. unfold stdio_static in Hs. lia. }
    assert (U22 : rw_cells asegs m2 A_STDIN_USED [C8 (Z_to_bv 64 A_STDIN)])
      by (eapply agrees_rw_cells; [exact AG02 | exact U2 | intros a Ha; unfold stdio_static, A_STDIN_USED in *; sl_lit_sizes_in Ha; cbn in Ha; lia]).
    assert (U32 : rw_cells asegs m2 A_STDOUT_USED [C8 (Z_to_bv 64 A_STDOUT)])
      by (eapply agrees_rw_cells; [exact AG02 | exact U3 | intros a Ha; unfold stdio_static, A_STDOUT_USED in *; sl_lit_sizes_in Ha; cbn in Ha; lia]).
    assert (SIN2 : rw_cells asegs m2 A_STDIN stdin_cells).
    { eapply agrees_rw_cells; [exact AG02| exact SIN|]. unfold stdin_cells. rewrite file_cells_size. intros a Ha. unfold stdio_static, A_STDIN in *. lia. }
    pose proof SOI as (OCH & OFD & OBS & ONRD & ONWR & OEOF & ORB & _).
    assert (SO2 : FILE_R m2 (lc_stdout (ps_libc s)) A_STDOUT A_STDOUT_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0).
    { eapply FILE_R_agree; [exact SO| exact AG02| |]; intros a Ha; unfold stdio_static, A_STDOUT, A_STDOUT_BUF in *; [lia|]. rewrite OBS in Ha. unfold BUFSIZ in Ha. lia. }
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -16) [C8 s0; C8 ra]).
    { eapply agrees_rw_cells; [exact AG2| exact FR1|]. intros a Ha. right. cbn in Ha. lia. }
    (* [comment removed for export] *)
    eapply implAM_evt. { eapply (exit_stdin RNG (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 ATP)); [exact U22| exact SIN2| exact MI2| exact RIMG]. }
    cbv beta. intros ms3 (c0 & c1 & ->).
    (* [comment removed for export] *)
    destruct SO2 as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP0 & RPHI & GLN).
    pose proof FL as (FLn & FLw & FLe & FLerr & FLsvb & FLperm).
    remember (Z_to_bv 64 (bv_unsigned sp + -16) : word) as sp0 eqn:Esp0.
    assert (Hsp : bv_unsigned sp0 = bv_unsigned sp + -16) by (rewrite Esp0; apply unsigned_lit; lia).
    assert (RSTK0 : rng RNG lo (bv_unsigned sp0 - lo)) by (eapply rng_sub'; [exact RSTK | lia]).
    eapply implAM_bind.
    { eapply (exit_stdout RNG sp0 gp (Z_to_bv 64 ATP)) with (f := lc_stdout (ps_libc s)) (lo := lo) (canary := canary) (flags := flags) (mode := mode) (rp := rp) (tail := tail) (bufbytes := bufbytes) (m := m2) (st := s);
        rewrite ?Hsp; first [ exact U32 | exact FC | exact FLsvb | exact BUF | exact BP | exact WB0 | exact ORB | exact OCH | exact OBS | exact WBL | exact ST2 | exact SSP2 | exact MI2
                             | exact RIMG | exact R0 | (rewrite <- Hsp; exact RSTK0)
                             | (rewrite OFD; left; reflexivity) | (unfold EXIT_DEPTH; lia) | (unfold zlength in *; lia)
                             | match goal with |- ?g => idtac "XO side:" g end ]. }
    cbv beta. intros [] st4 ms4 (-> & PO). destruct_exs PO. destruct PO as (-> & MU4 & WM4 & MI4 & ST4 & SSP4).
    lazymatch type of MI4 with mem_inv _ ?mm => rename mm into m4 end.
    rewrite Hsp in ST4. unfold ex_W, EXIT_DEPTH in MU4. rewrite Hsp in MU4. rewrite Esp0.
    (* [comment removed for export] *)
    pose proof SEI as (ECH & EFD & EBS & ENRD & ENWR & EEOF & ERB & _).
    assert (SE4 : FILE_R m4 (lc_stderr (ps_libc s)) A_STDERR A_STDERR_BUF F_STDIO_CLOSE 0 F_STDIO_SEEK 0 0).
    { eapply FILE_R_agree; [exact SE| |intros a Ha; exact Ha| intros a Ha; rewrite EBS in Ha; lia].
      eapply agrees_on_trans; [eapply agrees_on_weaken; [exact AG02| intros a Ha; unfold stdio_static, A_STDERR in *; lia]|].
      eapply agrees_on_of_munch; [exact MU4| exact WM4|]. intros a Ha Hp. unfold A_STDERR, A_STDOUT in *. cbn [outside]. lia. }
    assert (U14 : rw_cells asegs m4 A_STDERR_USED [C8 (Z_to_bv 64 A_STDERR)]).
    { eapply rw_cells_transport; [eapply agrees_rw_cells; [exact AG02 | exact U1 | intros a Ha; unfold stdio_static, A_STDERR_USED in *; sl_lit_sizes_in Ha; cbn in Ha; lia] | exact MU4| exact WM4| unfold A_STDERR_USED, A_STDOUT; cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    assert (FR4 : rw_cells asegs m4 (bv_unsigned sp + -16) [C8 s0; C8 ra]).
    { eapply rw_cells_transport; [exact FR2| exact MU4| exact WM4| unfold A_STDOUT; cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    destruct SE4 as (flags' & mode' & rp' & tail' & bufbytes' & FC' & FL' & BUF' & BP' & WB0' & WBL' & RR' & RP0' & RPHI' & GLN').
    assert (EWB : f_wbuf (lc_stderr (ps_libc s)) = []).
    { destruct (f_wbuf (lc_stderr (ps_libc s))) eqn:E; [reflexivity|]. exfalso. rewrite EBS in WBL'. unfold zlength in WBL'. cbn in WBL'. lia. }
    unfold close_file. rewrite EWB. apply implAM_retb. unfold sync_read_pos. rewrite ERB. apply implAM_ret.
    eapply evtF_mono.
    { eapply (exit_stderr RNG ra sp gp (Z_to_bv 64 ATP)) with (f := lc_stderr (ps_libc s)) (lo := lo); first
        [ exact U14 | exact FC' | exact EWB | exact ERB | exact FR4 | exact ST4 | exact MI4 | exact RSTK | exact RIMG | lia | (unfold zlength in *; lia)
        | match goal with |- ?g => idtac "XE side:" g end ]. }
    cbv beta. intros ms5 (d0 & d1 & -> & ST5).
    unfold stdio_exit_post. repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity | exact RIMG].
  Qed.
  End Sz4.
  Theorem stdio_exit_proofA : ltac:(let t := eval cbv delta [stdio_exit_proofA__stmt] in stdio_exit_proofA__stmt in exact t).
  Proof using Type. unfold stdio_exit_stmtA. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo s. ltac2:(SecDiet.SzSec.closeP 'stdio_exit_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End GlueExit.
End TwB.
