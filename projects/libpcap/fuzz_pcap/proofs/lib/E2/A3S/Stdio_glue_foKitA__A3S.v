(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Require OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Ox.F64_004.   (* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw ExecF ITreeA Shadow StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABase AMalloc_iface RtCells.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA MonadG.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require PcapRepA UnwKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_cs__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_lock__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_strerror__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_fopen.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_fopen__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA Stdio_glueKitA StdioLawsA Stdio_glueA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_read__A3S.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_ahm I_fflush I_fclose Stdio_glue_fcKitA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require KeepHyps.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_strlen.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require StrerrorTable.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require StrerrorData.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Fuzz_ifaceA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_mkstemp__A3S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module Stdio_glue_foKitA.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_cs__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_lock__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_strerror__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_fopen. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_fopen__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA Stdio_glueKitA StdioLawsA Stdio_glueA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_lock OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.F_fmodeflags OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_fopen OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_fopen OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioLawsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Lemma disjoint_from_Forall : forall W a n,
  Forall (fun iv : Z * Z => a + n <= fst iv \/ snd iv <= a) W -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n H; cbn; [exact I|].
  apply Forall_cons_iff in H. destruct H as [H1 H2]. cbn [fst snd] in H1. split; [Lia.lia|]. apply IH. exact H2.
Qed.
Lemma outside_of_Forall : forall (W : list (Z * Z)) a, Forall (fun iv => ~ (fst iv <= a < snd iv)) W -> outside W a.
Proof.
  induction W as [|[lo hi] W IH]; intros a H; cbn [outside]; [exact I|].
  apply Forall_cons_iff in H. destruct H as [H1 H2]. cbn [fst snd] in H1. split; [exact H1 | apply IH; exact H2].
Qed.

Section WithRc.
Context {rc : runConstT}.
(* [comment removed for export] *)
#[using="Type"] Lemma mode_lit_factsA : forall wr MODE md, mode_lit wr MODE md ->
  exists slack,
    ro_bytes asegs MODE (md ++ Z_to_bv 8 0 :: slack)
    /\ (0x10000 <= MODE /\ MODE + Z.of_nat (length md) + 1 + Z.of_nat (length slack) <= 0x32000)
    /\ ~ In (Z_to_bv 8 0) md
    /\ (- (MODE + Z.of_nat (length md) + 1)) mod 8 <= Z.of_nat (length slack)
    /\ (mode_m0 md = 114 \/ mode_m0 md = 119)
    /\ mode_m0 md = (if wr then 119 else 114)
    /\ fmodeflags md = (if wr then 577 else 0)
    /\ has_byte 43 md = false /\ has_byte 101 md = false
    /\ In (MODE, Z.of_nat (length md) + 1) client_globals.   (* [comment removed for export] *)
Proof.
  intros wr MODE md ML.
  assert (IG : In (MODE, Z.of_nat (length md) + 1) client_globals).
  { unfold mode_lit, STR_RB in ML. destruct wr; [destruct ML as [[-> ->] | [-> ->]] | destruct ML as [-> ->]];
      cbn [length]; unfold client_globals; repeat (first [left; reflexivity | right]). }
  unfold mode_lit, STR_RB in ML. destruct wr.
  - destruct ML as [[-> ->] | [-> ->]].
    + exists (repeat (Z_to_bv 8 0) 6).
      split; [apply ro_bytes_b_sound; vm_compute; reflexivity|]. cbn. repeat split; try exact IG; try Lia.lia; try reflexivity. intros [X|[]]. discriminate X. right; reflexivity.
    + exists (repeat (Z_to_bv 8 0) 5).
      split; [apply ro_bytes_b_sound; vm_compute; reflexivity|]. cbn. repeat split; try exact IG; try Lia.lia; try reflexivity. intros [X|[X|[]]]; discriminate X. right; reflexivity.
  - destruct ML as [-> ->].
    exists (repeat (Z_to_bv 8 0) 5).
    split; [apply ro_bytes_b_sound; vm_compute; reflexivity|]. cbn. repeat split; try exact IG; try Lia.lia; try reflexivity. intros [X|[X|[]]]; discriminate X. left; reflexivity.
Qed.
End WithRc.

Section GlueFo.
  Context {rc : runConstT} {tlsI : ABase.atlsT}.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GSL : gia_stdio_laws GIOA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  #[local] Abbreviation eqb := (ho_eqb HO).

  (* [comment removed for export] *)
  Lemma files_R_newhead : forall m m' fs (FB : list cblk) A,
    files_R m 0 fs FB ->
    (forall q1 A1 n1 f1 FB', FB = (q1, A1, n1) :: FB' ->
        FILE_R m f1 A1 (A1 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK 0 (hd_addr FB') -> heap_file_inv f1 ->
        FILE_R m' f1 A1 (A1 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK A (hd_addr FB')) ->
    (forall q2 A2 n2 f2 pv2 nx2, In (q2, A2, n2) (tl FB) ->
        FILE_R m f2 A2 (A2 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv2 nx2 -> heap_file_inv f2 ->
        FILE_R m' f2 A2 (A2 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv2 nx2) ->
    files_R m' A fs FB.
  Proof using Type. pin_using tt.
    intros m m' fs FB A FS HHD HTL.
    destruct fs as [|[q1 f1] fs]; destruct FB as [|[[q1' A1] n1] FB]; cbn in FS |- *; try exact FS.
    destruct FS as (-> & -> & B0 & Bhi & FR & INV & REST).
    split; [reflexivity|]. split; [reflexivity|]. split; [exact B0|]. split; [exact Bhi|].
    split; [exact (HHD q1 A1 FILE_ALLOC f1 FB eq_refl FR INV)|]. split; [exact INV|].
    eapply files_R_frame; [exact REST|]. intros q2 A2 n2 f2 pv2 nx2 HIN2. apply (HTL q2 A2 n2 f2 pv2 nx2). exact HIN2.
  Qed.

  (* [comment removed for export] *)
  Lemma fcells_split_prev : forall flags rp re cf we wp wb rf wf sf b bs pv nx fd md lbf tl,
    fcells flags rp re cf we wp wb rf wf sf b bs pv nx fd md lbf tl =
    [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 rp); C8 (Z_to_bv 64 re); C8 (Z_to_bv 64 cf);
     C8 (Z_to_bv 64 we); C8 (Z_to_bv 64 wp); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wb);
     C8 (Z_to_bv 64 rf); C8 (Z_to_bv 64 wf); C8 (Z_to_bv 64 sf); C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 bs)]
    ++ [C8 (Z_to_bv 64 pv)]
    ++ [C8 (Z_to_bv 64 nx); C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
        C4 md; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0); CB 80 tl].
  Proof using Type. pin_using tt. intros. reflexivity. Qed.

  Lemma FILE_R_prev_cell : forall m f Fp BA cf rf sf pv nx,
    FILE_R m f Fp BA cf rf sf pv nx -> rw_cells asegs m (Fp + 104) [C8 (Z_to_bv 64 pv)].
  Proof using Type. pin_using tt.
    intros m f Fp BA cf rf sf pv nx (flags & mode & rp & tail & bufbytes & FC & _).
    rewrite fcells_split_prev in FC. apply (proj1 (rw_cells_app asegs m Fp _ _)) in FC as [_ FC].
    apply (proj1 (rw_cells_app asegs m _ [_] _)) in FC as [FC _]. cbn [cells_size csize Nat.add] in FC.
    replace (Fp + Z.of_nat 104) with (Fp + 104) in FC by lia. exact FC.
  Qed.

  (* [comment removed for export] *)
  Definition FILE_R_set_prev__stmt : Prop := forall m m' f Fp BA cf rf sf pv pv' nx W,
    FILE_R m f Fp BA cf rf sf pv nx ->
    munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => (Fp + 232 <= fst iv \/ snd iv <= Fp) \/ (fst iv = Fp + 104 /\ snd iv = Fp + 112)) W ->
    Forall (fun iv : Z * Z => BA + f_bufsize f <= fst iv \/ snd iv <= BA) W ->
    0 <= f_bufsize f ->
    rw_cells asegs m' (Fp + 104) [C8 (Z_to_bv 64 pv')] ->
    FILE_R m' f Fp BA cf rf sf pv' nx.
  Section Sz5.
  Variables m m' f Fp BA cf rf sf pv pv' nx W : ltac2:(SecDiet.SzSec.tyM 'FILE_R_set_prev__stmt "vvvvvvvvvvvv" @m).
  Lemma FILE_R_set_prev__body : ltac2:(SecDiet.SzSec.bodyP 'FILE_R_set_prev__stmt "vvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros FR MU WM D1 D2 BS PC.
    destruct FR as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP).
    exists flags, mode, rp, tail, bufbytes.
    split; [| split; [exact FL | split; [| split; [exact BP | split; [exact WB0 | split; [exact WBL | split; [exact RR | exact RP]]]]]]].
    - rewrite fcells_split_prev in FC |- *.
      apply (proj1 (rw_cells_app asegs m Fp _ _)) in FC as [FCa FC]. apply (proj1 (rw_cells_app asegs m _ [_] _)) in FC as [_ FCb].
      cbn [cells_size csize Nat.add] in FCa, FCb |- *.
      apply (proj2 (rw_cells_app asegs m' Fp _ _)). split.
      + eapply rw_cells_transport; [exact FCa| exact MU| exact WM|]. cbn [cells_size csize Nat.add].
        apply disjoint_from_Forall. eapply Forall_impl; [| exact D1]. intros [lo hi]; cbn; lia.
      + apply (proj2 (rw_cells_app asegs m' _ [_] _)). cbn [cells_size csize Nat.add]. split.
        * replace (Fp + Z.of_nat 104) with (Fp + 104) by lia. exact PC.
        * eapply rw_cells_transport; [exact FCb| exact MU| exact WM|]. cbn [cells_size csize Nat.add].
          apply disjoint_from_Forall. eapply Forall_impl; [| exact D1]. intros [lo hi]; cbn; lia.
    - eapply rw_cells_transport; [exact BUF | exact MU | exact WM |]. cbn [cells_size csize Nat.add].
      apply disjoint_from_Forall. eapply Forall_impl; [| exact D2]. intros [lo hi]; cbn; lia.
  Qed.
  End Sz5.
  Lemma FILE_R_set_prev : ltac:(let t := eval cbv delta [FILE_R_set_prev__stmt] in FILE_R_set_prev__stmt in exact t).
  Proof using Type. intros m m' f Fp BA cf rf sf pv pv' nx W. ltac2:(SecDiet.SzSec.closeP 'FILE_R_set_prev__body "vvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma block_rangeA : forall L RNG (s : PS) CL FB FL m b, GIOA L RNG s CL FB FL m -> In b (CL ++ FB) ->
    0x603000 <= cb_addr b /\ 0 <= cb_size b /\ cb_addr b + cb_size b <= ATOP
    /\ (cb_addr b + cb_size b <= 0x7fff7000 \/ 0x10007fff8000 <= cb_addr b).
  Proof using GL. pin_using (fun (GL : unit) => tt).
    intros L RNG s CL FB FL m b G HIN.
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ b G HIN) as ((ABLK & N0 & TOP & _) & _).
    unfold ablk, AIMG_HI, KLS in ABLK. lia.
  Qed.

  (* [comment removed for export] *)
  Definition fopen_finishA__stmt : Prop := forall L RNG (sM : PS) (CL FB : list cblk) FL m3 m7 W q A fd (wr : bool) (fl : Z) junk2 SP,
    GIOA L RNG sM ((q, A, FILE_ALLOC) :: CL) FB FL m3 ->
    munch W m3 m7 -> wmono asegs m3 m7 ->
    Forall (fun iv : Z * Z => (ATOP + 4096 <= fst iv /\ snd iv <= SP) \/ (fst iv = A /\ snd iv = A + 232) \/ (fst iv = A_OFL_HEAD /\ snd iv = A_OFL_HEAD + 8)
                              \/ (FB <> [] /\ fst iv = hd_addr FB + 104 /\ snd iv = hd_addr FB + 112)) W ->
    ATOP + 4096 <= SP ->
    rw_cells asegs m7 A (file_cells (Z_to_bv 64 fl) 0 0 F_STDIO_CLOSE 0 0 0 F_STDIO_READ F_STDIO_WRITE F_STDIO_SEEK (A + 240) 1024 0 (hd_addr FB) fd
                          (Z_to_bv 64 0) 4294967295 (repeat (Z_to_bv 8 0) 80)) ->
    rw_cells asegs m7 (A + 232) [CB 1032 junk2] ->
    rw_cells asegs m7 A_OFL_LOCK [C4 (Z_to_bv 64 0)] -> rw_cells asegs m7 A_OFL_HEAD [C8 (Z_to_bv 64 A)] ->
    (hd_addr FB <> 0 -> rw_cells asegs m7 (hd_addr FB + 104) [C8 (Z_to_bv 64 A)]) ->
    fl = (if wr then 4 else 8) -> 3 <= fd <= 4096 ->
    GIOA L RNG (set_libc (set_files ((q, fdopen_file fd wr) :: lc_files (ps_libc sM)) (ps_libc sM)) sM) CL ((q, A, FILE_ALLOC) :: FB) FL m7
    /\ agrees_on (client_keeps FL CL SP) m3 m7.
  Section Sz7.
  Variables L RNG sM CL FB FL m3 m7 W q A fd wr fl junk2 SP : ltac2:(SecDiet.SzSec.tyM 'fopen_finishA__stmt "vvvvvvvvvvvvvvvv" @L).
  Lemma fopen_finishA__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_finishA__stmt "vvvvvvvvvvvvvvvv").
  Proof using EQB GL GSL HAL. pin_using (fun (EQB GL GSL HAL : unit) => tt).
    intros G MU WM HW CSP FC7 BLK7 OL7 OH7 OLDP7 -> HFD.
    pose proof (gs_stdio _ GSL _ _ _ _ _ _ _ G) as SR.
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    pose proof (@ATOP_lo rc) as ATL.
    pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G) as BA.
    pose proof (block_rangeA _ _ _ _ _ _ _ (q, A, FILE_ALLOC) G ltac:(apply in_or_app; left; left; reflexivity)) as (BK1 & _ & BK3 & BK4).
    unfold cb_addr, cb_size, FILE_ALLOC in BK1, BK3, BK4. cbn [fst snd] in BK1, BK3, BK4.
    assert (APb : forall b, In b (CL ++ FB) -> apart (q, A, FILE_ALLOC) b).
    { intros b Hb. cbn [app blocks_apart] in BA. destruct BA as [APc _]. exact (proj1 (Forall_forall _ _) APc _ Hb). }
    (* [comment removed for export] *)
    assert (FBn : forall q2 A2 n2, In (q2, A2, n2) FB -> n2 = FILE_ALLOC /\ 0x603000 <= A2 /\ A2 + 1264 <= ATOP /\ (A + 1264 <= A2 \/ A2 + 1264 <= A)).
    { intros q2 A2 n2 HIN. destruct (files_R_pick eqb EQB m3 0 _ FB q2 A2 n2 FS ND HIN) as (f & pv & nx & _ & _ & En & B0 & _). subst n2.
      pose proof (block_rangeA _ _ _ _ _ _ _ (q2, A2, FILE_ALLOC) G ltac:(apply in_or_app; right; exact HIN)) as (K1 & _ & K3 & _).
      pose proof (APb (q2, A2, FILE_ALLOC) ltac:(apply in_or_app; right; exact HIN)) as AP.
      unfold apart, cb_addr, cb_size, FILE_ALLOC in *. cbn [fst snd] in *. repeat split; lia. }
    (* [comment removed for export] *)
    assert (HDB : forall q1 A1' n1 FB', FB = (q1, A1', n1) :: FB' ->
              n1 = FILE_ALLOC /\ 0x603000 <= A1' /\ A1' + 1264 <= ATOP /\ (A + 1264 <= A1' \/ A1' + 1264 <= A) /\ Forall (apart (q1, A1', n1)) FB').
    { intros q1 A1' n1 FB' E. destruct (FBn q1 A1' n1 ltac:(rewrite E; left; reflexivity)) as (En & K1 & K2 & K3).
      split; [exact En|]. split; [exact K1|]. split; [exact K2|]. split; [exact K3|].
      pose proof (blocks_apart_app_inv _ _ BA) as (_ & BA2 & _). rewrite E in BA2. cbn [blocks_apart] in BA2. exact (proj1 BA2). }
    (* [comment removed for export] *)
    set (P37 := fun a : Z => ~ (ATOP + 4096 <= a < SP) /\ ~ (A <= a < A + 232) /\ ~ (A_OFL_HEAD <= a < A_OFL_HEAD + 8)
                             /\ ~ (FB <> [] /\ hd_addr FB + 104 <= a < hd_addr FB + 112)).
    assert (AG : agrees_on P37 m3 m7).
    { eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha (N1 & N2 & N3 & N4).
      eapply outside_of_Forall. eapply Forall_impl; [| exact HW]. intros [lo' hi'] Hiv; cbn [fst snd] in Hiv |- *.
      destruct Hiv as [X|[X|[X|(Xne & X1 & X2)]]]; [lia| lia| lia|]. intros Hin. apply N4. split; [exact Xne| lia]. }
    (* [comment removed for export] *)
    assert (HSt : forall a, stdio_static a -> ~ (A_OFL_HEAD <= a < A_OFL_HEAD + 8) -> P37 a).
    { intros a Hs Hn. unfold stdio_static, A_OFL_HEAD in *. subst P37. cbn beta.
      split; [lia|]. split; [lia|]. split; [exact Hn|].
      intros (Xne & Xr). destruct FB as [|[[q1 A1'] n1] FB']; [exact (Xne eq_refl)|]. cbn [hd_addr] in Xr.
      destruct (HDB q1 A1' n1 FB' eq_refl) as (_ & K4 & _). lia. }
    (* [comment removed for export] *)
    assert (HBl : forall q2 A2 n2 a, In (q2, A2, n2) FB -> A2 <= a < A2 + 1264 -> ~ (A2 = hd_addr FB /\ A2 + 104 <= a < A2 + 112) -> P37 a).
    { intros q2 A2 n2 a HIN Ha Hn. destruct (FBn _ _ _ HIN) as (-> & K1 & K2 & K3).
      subst P37. cbn beta. unfold A_OFL_HEAD. split; [lia|]. split; [lia|]. split; [lia|].
      intros (Xne & Xr). destruct FB as [|[[q1 A1'] n1] FB']; [exact (Xne eq_refl)|]. cbn [hd_addr] in Xr, Hn.
      destruct (HDB q1 A1' n1 FB' eq_refl) as (En1 & _ & _ & _ & APh).
      destruct HIN as [E|HIN].
      - injection E as <- <- _. apply Hn. split; [reflexivity| lia].
      - pose proof (proj1 (Forall_forall _ _) APh _ HIN) as AP2. unfold apart, cb_addr, cb_size in AP2. cbn [fst snd] in AP2. subst n1. unfold FILE_ALLOC in AP2. lia. }
    (* [comment removed for export] *)
    assert (SR7 : STDIOR (set_files ((q, fdopen_file fd wr) :: lc_files (ps_libc sM)) (ps_libc sM)) ((q, A, FILE_ALLOC) :: FB) m7).
    { unfold STDIOR. cbn [lc_stdout lc_stderr lc_files set_files hd_addr].
      pose proof SOI as (_ & _ & SObs & _). pose proof SEI as (_ & _ & SEbs & _).
      unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED in *.
      split. { eapply FILE_R_agree; [exact SO | exact AG | intros a Ha; apply HSt; [unfold stdio_static; lia| unfold A_OFL_HEAD; lia]
                                     | rewrite SObs; unfold BUFSIZ; intros a Ha; apply HSt; [unfold stdio_static; lia| unfold A_OFL_HEAD; lia]]. }
      split; [exact SOI|].
      split. { eapply FILE_R_agree; [exact SE | exact AG | intros a Ha; apply HSt; [unfold stdio_static; lia| unfold A_OFL_HEAD; lia]
                                     | rewrite SEbs; intros a Ha; apply HSt; [unfold stdio_static; lia| unfold A_OFL_HEAD; lia]]. }
      split; [exact SEI|].
      split. { eapply agrees_rw_cells; [exact AG | exact SIN |]. unfold stdin_cells. rewrite file_cells_size. intros a Ha; apply HSt; [unfold stdio_static; lia| unfold A_OFL_HEAD; lia]. }
      split; [eapply agrees_rw_cells; [exact AG | exact U1 | intros a Ha; cbn in Ha; apply HSt; [unfold stdio_static; lia| unfold A_OFL_HEAD; lia]]|].
      split; [eapply agrees_rw_cells; [exact AG | exact U2 | intros a Ha; cbn in Ha; apply HSt; [unfold stdio_static; lia| unfold A_OFL_HEAD; lia]]|].
      split; [eapply agrees_rw_cells; [exact AG | exact U3 | intros a Ha; cbn in Ha; apply HSt; [unfold stdio_static; lia| unfold A_OFL_HEAD; lia]]|].
      split; [exact OL7|]. split; [exact OH7|].
      split.
      - cbn [files_R]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [unfold FILE_ALLOC; lia|].
        split.
        { (* [comment removed for export] *)
          exists (Z_to_bv 64 (if wr then 4 else 8)), (Z_to_bv 64 0), 0, (repeat (Z_to_bv 8 0) 80), (firstn 1024 (skipn 8 junk2)).
          cbn [f_rbuf f_wbuf f_wactive f_bufsize f_fd f_nord f_nowr f_eof f_stdoutw f_lbf_nl fdopen_file wfn_of lbf_of zlength length Z.of_nat Z.add].
          split. { unfold fcells, FILE_BUF_OFF, BUFSIZ. exact FC7. }
          split. { unfold flags_ok. cbn [f_nord f_nowr f_eof f_chan]. unfold F_NORD, F_NOWR, F_EOF, F_ERR, F_SVB, F_PERM. destruct wr; rewrite unsigned_lit by lia; cbn; repeat split; reflexivity. }
          split. { pose proof (rw_cells_split_CB asegs m7 (A + 232) [] 1032 junk2 [] [8%nat; 1024%nat] BLK7 eq_refl) as B2.
                   cbn [app mk_CB_cells] in B2. apply rw_cells_split2 in B2 as [_ B2]. cbn [csize] in B2.
                   unfold FILE_BUF_OFF, BUFSIZ. replace (A + 232 + Z.of_nat 8) with (A + 240) in B2 by lia. exact B2. }
          split; [reflexivity|]. split; [intros _; reflexivity|]. split; [unfold BUFSIZ, zlength; cbn; lia|].
          split; [intros X; exfalso; exact (X eq_refl)|]. first [ assumption | (split; [lia|]; split; [unfold zlength; cbn; lia| reflexivity]) | (unfold zlength; cbn; lia)]. }
        split.
        { unfold heap_file_inv. cbn. destruct wr; cbn.
          all: split; [reflexivity|]; split; [lia|]; split; [reflexivity|]; split; [reflexivity|].
          all: split; [intros X; first [discriminate X | split; reflexivity] |]; split; [intros X; first [discriminate X | reflexivity]| apply Forall_nil]. }
        (* [comment removed for export] *)
        eapply files_R_newhead; [exact FS| |].
        + intros q1 A1' n1 f1 FB' E FR1 INV1.
          destruct (HDB q1 A1' n1 FB' E) as (En1 & KS & KC & AP1 & APh).
          pose proof INV1 as (_ & _ & BS1 & _).
          eapply (FILE_R_set_prev m3 m7 f1 A1' _ _ _ _ 0 A (hd_addr FB') W); [exact FR1| exact MU| exact WM| | | rewrite BS1; unfold BUFSIZ; lia|].
          * eapply Forall_impl; [| exact HW]. intros [lo' hi'] X; cbn [fst snd] in *.
            destruct X as [X|[X|[X|(Xne & X1 & X2)]]]; [left; lia| left; lia| left; unfold A_OFL_HEAD in X; lia| right]. rewrite E in X1, X2. cbn [hd_addr] in X1, X2. lia.
          * rewrite BS1. unfold BUFSIZ, FILE_BUF_OFF. eapply Forall_impl; [| exact HW]. intros [lo' hi'] X; cbn [fst snd] in *.
            destruct X as [X|[X|[X|(Xne & X1 & X2)]]]; [lia| lia| unfold A_OFL_HEAD in X; lia|]. rewrite E in X1, X2. cbn [hd_addr] in X1, X2. lia.
          * rewrite E in OLDP7. cbn [hd_addr] in OLDP7. apply OLDP7. lia.
        + intros q2 A2 n2 f2 pv2 nx2 HIN2 FR2 INV2.
          assert (HIN2' : In (q2, A2, n2) FB) by (destruct FB as [|b FB']; [exact HIN2| right; exact HIN2]).
          pose proof INV2 as (_ & _ & BS2 & _).
          assert (NH : A2 <> hd_addr FB).
          { destruct FB as [|[[q1 A1'] n1] FB']; [exact (False_ind _ HIN2)|]. cbn [hd_addr tl] in HIN2 |- *.
            destruct (HDB q1 A1' n1 FB' eq_refl) as (En1 & _ & _ & _ & APh).
            pose proof (proj1 (Forall_forall _ _) APh _ HIN2) as AP2. unfold apart, cb_addr, cb_size in AP2. cbn [fst snd] in AP2.
            destruct (FBn _ _ _ HIN2') as [-> _]. subst n1. unfold FILE_ALLOC in AP2. lia. }
          eapply FILE_R_agree; [exact FR2| exact AG| |].
          * intros a Ha. eapply (HBl q2 A2 n2 a HIN2'); [lia|]. intros [X _]. exact (NH X).
          * rewrite BS2. unfold BUFSIZ, FILE_BUF_OFF. intros a Ha. eapply (HBl q2 A2 n2 a HIN2'); [lia|]. intros [X _]. exact (NH X).
      - (* [comment removed for export] *)
        cbn [map fst]. apply List.NoDup_cons; [| exact ND].
        intros HIn. rewrite <- (files_R_toks m3 0 _ FB FS) in HIn. apply in_map_iff in HIn as ([[qb Ab] nb] & Eb & HbIn). cbn in Eb. subst qb.
        pose proof (HAL _ _ _ _ _ _ _ (q, A, FILE_ALLOC) G ltac:(apply in_or_app; left; left; reflexivity)) as E1.
        pose proof (HAL _ _ _ _ _ _ _ (q, Ab, nb) G ltac:(apply in_or_app; right; exact HbIn)) as E2.
        cbn [cb_tok cb_addr fst snd] in E1, E2.
        destruct (FBn _ _ _ HbIn) as (-> & _ & _ & AP). lia. }
    (* [comment removed for export] *)
    assert (HWA : Forall (stdio_ivA ((q, A, FILE_ALLOC) :: FB) SP) W).
    { eapply Forall_impl; [| exact HW]. intros [lo' hi'] X; cbn [fst snd] in X. unfold stdio_ivA; cbn [fst snd].
      destruct X as [X|[X|[X|(Xne & X1 & X2)]]].
      - left. exact X.
      - right; left. unfold iv_in_block. apply Exists_cons_hd. unfold cb_addr, cb_size, FILE_ALLOC; cbn [fst snd]. lia.
      - right; right; right; left. unfold A_OFL_HEAD in X. lia.
      - right; left. destruct FB as [|[[q1 A1'] n1] FB']; [exfalso; exact (Xne eq_refl)|]. cbn [hd_addr] in X1, X2.
        destruct (HDB q1 A1' n1 FB' eq_refl) as (En1 & _). unfold iv_in_block. apply Exists_cons_tl. apply Exists_cons_hd.
        unfold cb_addr, cb_size; cbn [fst snd]. subst n1. unfold FILE_ALLOC. lia. }
    (* [comment removed for export] *)
    assert (WBLK : forall lo' hi' a, In (lo', hi') W -> lo' <= a < hi' ->
              (ATOP + 4096 <= a < SP) \/ (A_OFL_HEAD <= a < A_OFL_HEAD + 8)
              \/ (in_block (((q, A, FILE_ALLOC) :: CL) ++ FB) a /\ ~ in_block CL a)).
    { intros lo' hi' a HIN Ha. pose proof (proj1 (Forall_forall _ _) HW _ HIN) as X. cbn [fst snd] in X.
      destruct X as [X|[X|[X|(Xne & X1 & X2)]]]; [left; lia | right; right | right; left; lia | right; right].
      - split.
        + apply in_block_In. exists (q, A, FILE_ALLOC). split; [apply in_or_app; left; left; reflexivity | unfold cb_addr, cb_size, FILE_ALLOC; cbn [fst snd]; lia].
        + intros K. apply in_block_In in K as (b & Hb & Rb). pose proof (APb b ltac:(apply in_or_app; left; exact Hb)) as AP.
          unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP. unfold cb_addr, cb_size in Rb. lia.
      - destruct FB as [|[[q1 A1'] n1] FB']; [exfalso; exact (Xne eq_refl)|]. cbn [hd_addr] in X1, X2.
        destruct (HDB q1 A1' n1 FB' eq_refl) as (En1 & _). subst n1. split.
        + apply in_block_In. exists (q1, A1', FILE_ALLOC). split; [apply in_or_app; right; left; reflexivity | unfold cb_addr, cb_size, FILE_ALLOC; cbn [fst snd]; lia].
        + intros K. apply in_block_In in K as (b & Hb & Rb).
          pose proof (blocks_apart_app_inv _ _ BA) as (_ & _ & BAX).
          pose proof (BAX b (q1, A1', FILE_ALLOC) ltac:(right; exact Hb) ltac:(left; reflexivity)) as AP.
          unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP. unfold cb_addr, cb_size in Rb. lia. }
    assert (ERR7 : exists e' : word, rw_cells asegs m7 (ATP + -164) [C4 e']).
    { destruct (gs_errno _ GSL _ _ _ _ _ _ _ G) as [e ERR]. exists e.
      eapply (agrees_rw_cells (fun a => ATP + -164 <= a < ATP + -160)); [| exact ERR | cbn [cells_size csize Nat.add]; intros a Ha; lia].
      eapply agrees_on_of_munch; [exact MU | exact WM |]. intros a Ha Hc.
      pose proof (@ATPv_hi rc tlsI) as TH. pose proof (@ATPv_img rc tlsI) as TI. unfold ATP in *.
      apply outside_of_Forall. apply Forall_forall. intros [lo' hi'] HIN. cbn [fst snd]. intros Hin.
      destruct (WBLK lo' hi' a HIN Hin) as [X|[X|[X _]]]; [lia | unfold A_OFL_HEAD in X; lia |].
      apply (gl_tls_apart _ _ _ GL _ _ _ _ _ _ _ a G (or_introl X)). unfold ATP. lia. }
    split.
    - eapply (gs_adopt _ GSL L RNG sM CL FB FL m3 m7 W SP _ q A); [exact G| exact MU| exact WM| exact HWA| exact CSP| exact ERR7| exact SR7].
    - (* [comment removed for export] *)
      eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hk.
      apply outside_of_Forall. apply Forall_forall. intros [lo' hi'] HIN. cbn [fst snd]. intros Hin.
      destruct (WBLK lo' hi' a HIN Hin) as [X|[X|[X NX]]].
      + destruct Hk as [K|[K|[K|K]]]; [lia| | |].
        * pose proof (gia_in_block_below FO GIOA fflagA GL _ _ _ _ _ _ _ a G ltac:(apply in_block_app; left; apply in_block_In; apply in_block_In in K as (b & Hb & Rb); exists b; split; [right; exact Hb | exact Rb])) as [_ B1]. lia.
        * pose proof (gia_in_frames_below FO GIOA fflagA GL _ _ _ _ _ _ _ a G K) as [_ B1]. lia.
        * pose proof (gia_in_frame_sh_band FO GIOA fflagA GL _ _ _ _ _ _ _ a G K) as [_ B1]. lia.
      + unfold A_OFL_HEAD in X. destruct Hk as [K|[K|[K|K]]]; [lia| | |].
        * apply in_block_In in K as (b & Hb & Rb).
          pose proof (block_rangeA _ _ _ _ _ _ _ b G ltac:(apply in_or_app; left; right; exact Hb)) as (K1 & _). lia.
        * apply in_frames_In in K as (fr & Hf & Rf).
          destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FA _]. pose proof (proj1 (Forall_forall _ _) FA fr Hf) as (BAND & _).
          unfold ablk, AIMG_HI, KLS in BAND. lia.
        * pose proof (gia_in_frame_sh_band FO GIOA fflagA GL _ _ _ _ _ _ _ a G K) as [B0 _]. lia.
      + destruct Hk as [K|[K|[K|K]]].
        * pose proof (gia_in_block_below FO GIOA fflagA GL _ _ _ _ _ _ _ a G X) as [_ B1]. lia.
        * exact (NX K).
        * exact (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G K X).
        * pose proof (gia_in_frame_sh_band FO GIOA fflagA GL _ _ _ _ _ _ _ a G K) as [B0 B1].
          apply in_block_In in X as (b & Hb & Rb).
          pose proof (block_rangeA _ _ _ _ _ _ _ b G Hb) as (_ & _ & _ & K4). lia.
  Qed.
  End Sz7.
  Lemma fopen_finishA : ltac:(let t := eval cbv delta [fopen_finishA__stmt] in fopen_finishA__stmt in exact t).
  Proof using EQB GL GSL HAL. intros L RNG sM CL FB FL m3 m7 W q A fd wr fl junk2 SP. ltac2:(SecDiet.SzSec.closeP 'fopen_finishA__body "vvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition robjA_factsA__stmt : Prop := forall L RNG (s : PS) CL FB FL m D n lo,
    GIOA L RNG s CL FB FL m -> robjA RNG m FL CL D n -> 0 < n <= 2^40 -> ATOP + 4096 <= lo ->
    0 < D /\ D + n + 8 <= lo /\ sobj RNG m D (D + n) /\ rng RNG D n.
  Section Sz8.
  Variables L RNG s CL FB FL m D n lo : ltac2:(SecDiet.SzSec.tyM 'robjA_factsA__stmt "vvvvvvvvvv" @L).
  Lemma robjA_factsA__body : ltac2:(SecDiet.SzSec.bodyP 'robjA_factsA__stmt "vvvvvvvvvv").
  Proof using GL. pin_using (fun (GL : unit) => tt).
    intros G [LOC MO] Hn LOA.
    pose proof MO as (D0 & _ & _ & RG & _ & _). pose proof (@ATOP_lo rc) as ATL.
    split; [exact D0|]. split; [| split; [apply mobjA_sobj; [exact MO | lia] | exact RG]].
    destruct LOC as [[(b & Hb & B1 & B2) | (fr & Hf & F1 & F2)] | (g & Hg & G1 & G2 & G3)].
    - pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ b G ltac:(apply in_or_app; left; exact Hb)) as ((_ & _ & TOP & _) & _). lia.
    - destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FA _]. pose proof (proj1 (Forall_forall _ _) FA fr Hf) as (BAND & _).
      unfold ablk, AIMG_HI, KLS in BAND. lia.
    - lia.
  Qed.
  End Sz8.
  Lemma robjA_factsA : ltac:(let t := eval cbv delta [robjA_factsA__stmt] in robjA_factsA__stmt in exact t).
  Proof using GL. intros L RNG s CL FB FL m D n lo. ltac2:(SecDiet.SzSec.closeP 'robjA_factsA__body "vvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma implMG_sysk : forall {A B} RNG (n : node) (dec : resp -> option A) (k : A -> M PS B) (s : PS) Q ms,
    match n with NMmap _ _ _ _ | NMunmap _ _ | NBrk _ | NMprotect _ _ _ => False | _ => True end ->
    evtF asegs RNG (fun ms1 => at_nodeA asegs n RNG ms1 /\
                            (forall rsp a, dec rsp = Some a -> implMG RNG (k a) s Q (nret ms1 rsp))) ms ->
    implMG RNG (mbind (msys n dec) k) s Q ms.
  Proof using Type. pin_using tt.
    intros A B RNG n dec k s Q ms Hn HE. unfold implMG, mbind, msys, ebind, enode in *. cbn [ITree.bind ITreeA.implF].
    apply evtS_of_evtF. eapply evtF_mono; [exact HE|]. intros ms1 [Hat Hk]. left. split; [exact Hat|].
    intros rsp RNG' HF.
    assert (ER : RNG' = RNG).
    { destruct HF as [HF _]. destruct n; try destruct Hn; cbn in HF; exact HF. }
    subst RNG'. destruct (dec rsp) as [a|] eqn:E; cbn [ITree.bind fst snd].
    - exact (Hk rsp a E).
    - apply implF_ret_unr.
  Qed.

  (* [comment removed for export] *)
  Definition live_block_factsA__stmt : Prop := forall L RNG (s : PS) CL FB FL m q A n lo,
    GIOA L RNG s CL FB FL m -> In (q, A, n) (CL ++ FB) -> ATOP + 4096 <= lo -> n <= 2^40 ->
    0 < A /\ 0 <= n /\ A + n <= lo /\ 0x603000 <= A /\ A + n <= ATOP /\ sobj RNG m A (A + n) /\ rng RNG A n.
  Section Sz10.
  Variables L RNG s CL FB FL m q A n lo : ltac2:(SecDiet.SzSec.tyM 'live_block_factsA__stmt "vvvvvvvvvvv" @L).
  Lemma live_block_factsA__body : ltac2:(SecDiet.SzSec.bodyP 'live_block_factsA__stmt "vvvvvvvvvvv").
  Proof using GL. pin_using (fun (GL : unit) => tt).
    intros G HIN LOA N40.
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ (q, A, n) G HIN) as (AR & A0 & UNP & RG & RSH & ARENA).
    unfold cb_addr, cb_size in *. cbn [fst snd] in *.
    destruct AR as (ABLK & N0 & ATOPB & _).
    assert (LOW : 0x603000 <= A) by (unfold ablk, AIMG_HI, KLS in ABLK; lia).
    split; [exact A0|]. split; [exact N0|]. split; [lia|]. split; [exact LOW|]. split; [exact ATOPB|]. split; [| exact RG].
    destruct ARENA as (RLO & RHI & R1 & R2 & R3 & R4 & R5 & R6 & WR & RS).
    split; [apply ablk_app_blk; [exact ABLK | lia]|]. split; [exact UNP|]. split; [lia|]. exists RLO, RHI. split; [repeat split; assumption|]. split; assumption.
  Qed.
  End Sz10.
  Lemma live_block_factsA : ltac:(let t := eval cbv delta [live_block_factsA__stmt] in live_block_factsA__stmt in exact t).
  Proof using GL. intros L RNG s CL FB FL m q A n lo. ltac2:(SecDiet.SzSec.closeP 'live_block_factsA__body "vvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition GIOA_errno_step__stmt : Prop := forall L RNG (s : PS) CL FB FL m m' W SP (l' : libc_st hptr) (e' : word),
    GIOA L RNG s CL FB FL m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => (ATOP + 4096 <= fst iv /\ snd iv <= SP) \/ (ATP + -164 <= fst iv /\ snd iv <= ATP + -160)) W -> ATOP + 4096 <= SP ->
    rw_cells asegs m' (ATP + -164) [C4 e'] ->
    lc_stdout l' = lc_stdout (ps_libc s) -> lc_stderr l' = lc_stderr (ps_libc s) -> lc_files l' = lc_files (ps_libc s) ->
    GIOA L RNG (set_libc l' s) CL FB FL m' /\ agrees_on (client_keeps FL CL SP) m m'.
  Section Sz11.
  Variables L RNG s CL FB FL m m' W SP l' e' : ltac2:(SecDiet.SzSec.tyM 'GIOA_errno_step__stmt "vvvvvvvvvvvv" @L).
  Lemma GIOA_errno_step__body : ltac2:(SecDiet.SzSec.bodyP 'GIOA_errno_step__stmt "vvvvvvvvvvvv").
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
    intros G MU WM HW HSP ERR' E1 E2 E3.
    assert (HW' : Forall (stdio_ivA FB SP) W).
    { eapply Forall_impl; [| exact HW]. intros iv [X|X]; [left; exact X | right; right; right; right; exact X]. }
    pose proof (gs_stdio _ GSL _ _ _ _ _ _ _ G) as SR.
    rewrite <- (app_nil_r W) in MU.
    split.
    - eapply (gs_step _ GSL L RNG s CL FB FL m m' W [] SP l'); [exact G | exact MU | exact WM | exact HW' | apply Forall_nil | exact HSP | exists e'; exact ERR' |].
      assert (SR' : STDIOR l' FB m) by (unfold STDIOR in SR |- *; rewrite E1, E2, E3; exact SR).
      eapply (STDIOR_agree l' FB m m' (fun a => stdio_static a \/ in_block FB a)); [exact SR' | | intros a Ha; left; exact Ha | intros a Ha; right; exact Ha].
      eapply agrees_on_of_munch; [exact MU | exact WM |]. intros a Ha Hc. rewrite app_nil_r.
      pose proof (@ATPv_hi rc tlsI) as TH. pose proof (@ATPv_imgk rc tlsI) as (TI1 & TI2). pose proof (@kt_rng rc tlsI) as ((KI & _) & _).
      pose proof (@ATOP_lo rc) as ATL.
      assert (NT : ~ (ATP + -164 <= a < ATP + -160) /\ a < ATOP + 4096).
      { destruct Hc as [Hs | Hb].
        - unfold stdio_static in Hs. unfold ATP. clear - Hs TH TI1 TI2 KI ATL. lia.
        - split.
          + intros X. assert (HB' : in_block (CL ++ FB) a) by (apply in_block_app; right; exact Hb).
            apply (gl_tls_apart _ _ _ GL _ _ _ _ _ _ _ a G (or_introl HB')). clear - X. lia.
          + apply in_block_In in Hb as (b & HIN & HR).
            pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ b G ltac:(apply in_or_app; right; exact HIN)) as ((_ & _ & TOP & _) & _). clear - HR TOP. lia. }
      destruct NT as [NT1 NT2]. clear - HW NT1 NT2.
      induction HW as [|[lo hi] W Hiv HW IH]; cbn [outside]; [exact I|]. split; [| exact IH]. cbn [fst snd] in Hiv. lia.
    - eapply agrees_on_weaken; [eapply (gs_keeps _ GSL L RNG s CL FB FL m m' W [] SP); [exact G | exact MU | exact WM | exact HW' | exact HSP]|].
      intros a Ha. split; [exact Ha | exact I].
  Qed.
  End Sz11.
  Lemma GIOA_errno_step : ltac:(let t := eval cbv delta [GIOA_errno_step__stmt] in GIOA_errno_step__stmt in exact t).
  Proof using GL GSL. intros L RNG s CL FB FL m m' W SP l' e'. ltac2:(SecDiet.SzSec.closeP 'GIOA_errno_step__body "vvvvvvvvvvvv"). Qed.

End GlueFo.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_lock.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.F_fmodeflags.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_fopen.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_fopen.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioLawsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Lemma disjoint_from_Forall : forall W a n,
  Forall (fun iv : Z * Z => a + n <= fst iv \/ snd iv <= a) W -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n H; cbn; [exact I|].
  apply Forall_cons_iff in H. destruct H as [H1 H2]. cbn [fst snd] in H1. split; [Lia.lia|]. apply IH. exact H2.
Qed.
Lemma outside_of_Forall : forall (W : list (Z * Z)) a, Forall (fun iv => ~ (fst iv <= a < snd iv)) W -> outside W a.
Proof.
  induction W as [|[lo hi] W IH]; intros a H; cbn [outside]; [exact I|].
  apply Forall_cons_iff in H. destruct H as [H1 H2]. cbn [fst snd] in H1. split; [exact H1 | apply IH; exact H2].
Qed.

Section WithRc.
Context {rc : runConstT}.
(* [comment removed for export] *)
#[using="Type"] Lemma mode_lit_factsA : forall wr MODE md, mode_lit wr MODE md ->
  exists slack,
    ro_bytes asegs MODE (md ++ Z_to_bv 8 0 :: slack)
    /\ (0x10000 <= MODE /\ MODE + Z.of_nat (length md) + 1 + Z.of_nat (length slack) <= 0x32000)
    /\ ~ In (Z_to_bv 8 0) md
    /\ (- (MODE + Z.of_nat (length md) + 1)) mod 8 <= Z.of_nat (length slack)
    /\ (mode_m0 md = 114 \/ mode_m0 md = 119)
    /\ mode_m0 md = (if wr then 119 else 114)
    /\ fmodeflags md = (if wr then 577 else 0)
    /\ has_byte 43 md = false /\ has_byte 101 md = false
    /\ In (MODE, Z.of_nat (length md) + 1) client_globals.   (* [comment removed for export] *)
Proof.
  intros wr MODE md ML.
  assert (IG : In (MODE, Z.of_nat (length md) + 1) client_globals).
  { unfold mode_lit, STR_RB in ML. destruct wr; [destruct ML as [[-> ->] | [-> ->]] | destruct ML as [-> ->]];
      cbn [length]; unfold client_globals; repeat (first [left; reflexivity | right]). }
  unfold mode_lit, STR_RB in ML. destruct wr.
  - destruct ML as [[-> ->] | [-> ->]].
    + exists (repeat (Z_to_bv 8 0) 6).
      split; [apply ro_bytes_b_sound; vm_compute; reflexivity|]. cbn. repeat split; try exact IG; try Lia.lia; try reflexivity. intros [X|[]]. discriminate X. right; reflexivity.
    + exists (repeat (Z_to_bv 8 0) 5).
      split; [apply ro_bytes_b_sound; vm_compute; reflexivity|]. cbn. repeat split; try exact IG; try Lia.lia; try reflexivity. intros [X|[X|[]]]; discriminate X. right; reflexivity.
  - destruct ML as [-> ->].
    exists (repeat (Z_to_bv 8 0) 5).
    split; [apply ro_bytes_b_sound; vm_compute; reflexivity|]. cbn. repeat split; try exact IG; try Lia.lia; try reflexivity. intros [X|[X|[]]]; discriminate X. left; reflexivity.
Qed.
End WithRc.

Section GlueFo.
  Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GSL : gia_stdio_laws GIOA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  #[local] Abbreviation eqb := (ho_eqb HO).

  (* [comment removed for export] *)
  Lemma files_R_newhead : forall m m' fs (FB : list cblk) A,
    files_R m 0 fs FB ->
    (forall q1 A1 n1 f1 FB', FB = (q1, A1, n1) :: FB' ->
        FILE_R m f1 A1 (A1 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK 0 (hd_addr FB') -> heap_file_inv f1 ->
        FILE_R m' f1 A1 (A1 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK A (hd_addr FB')) ->
    (forall q2 A2 n2 f2 pv2 nx2, In (q2, A2, n2) (tl FB) ->
        FILE_R m f2 A2 (A2 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv2 nx2 -> heap_file_inv f2 ->
        FILE_R m' f2 A2 (A2 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv2 nx2) ->
    files_R m' A fs FB.
  Proof using Type. pin_using tt.
    intros m m' fs FB A FS HHD HTL.
    destruct fs as [|[q1 f1] fs]; destruct FB as [|[[q1' A1] n1] FB]; cbn in FS |- *; try exact FS.
    destruct FS as (-> & -> & B0 & Bhi & FR & INV & REST).
    split; [reflexivity|]. split; [reflexivity|]. split; [exact B0|]. split; [exact Bhi|].
    split; [exact (HHD q1 A1 FILE_ALLOC f1 FB eq_refl FR INV)|]. split; [exact INV|].
    eapply files_R_frame; [exact REST|]. intros q2 A2 n2 f2 pv2 nx2 HIN2. apply (HTL q2 A2 n2 f2 pv2 nx2). exact HIN2.
  Qed.

  (* [comment removed for export] *)
  Lemma fcells_split_prev : forall flags rp re cf we wp wb rf wf sf b bs pv nx fd md lbf tl,
    fcells flags rp re cf we wp wb rf wf sf b bs pv nx fd md lbf tl =
    [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 rp); C8 (Z_to_bv 64 re); C8 (Z_to_bv 64 cf);
     C8 (Z_to_bv 64 we); C8 (Z_to_bv 64 wp); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wb);
     C8 (Z_to_bv 64 rf); C8 (Z_to_bv 64 wf); C8 (Z_to_bv 64 sf); C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 bs)]
    ++ [C8 (Z_to_bv 64 pv)]
    ++ [C8 (Z_to_bv 64 nx); C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
        C4 md; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0); CB 80 tl].
  Proof using Type. pin_using tt. intros. reflexivity. Qed.

  Lemma FILE_R_prev_cell : forall m f Fp BA cf rf sf pv nx,
    FILE_R m f Fp BA cf rf sf pv nx -> rw_cells asegs m (Fp + 104) [C8 (Z_to_bv 64 pv)].
  Proof using Type. pin_using tt.
    intros m f Fp BA cf rf sf pv nx (flags & mode & rp & tail & bufbytes & FC & _).
    rewrite fcells_split_prev in FC. apply (proj1 (rw_cells_app asegs m Fp _ _)) in FC as [_ FC].
    apply (proj1 (rw_cells_app asegs m _ [_] _)) in FC as [FC _]. cbn [cells_size csize Nat.add] in FC.
    replace (Fp + Z.of_nat 104) with (Fp + 104) in FC by lia. exact FC.
  Qed.

  (* [comment removed for export] *)
  Definition FILE_R_set_prev__stmt : Prop := forall m m' f Fp BA cf rf sf pv pv' nx W,
    FILE_R m f Fp BA cf rf sf pv nx ->
    munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => (Fp + 232 <= fst iv \/ snd iv <= Fp) \/ (fst iv = Fp + 104 /\ snd iv = Fp + 112)) W ->
    Forall (fun iv : Z * Z => BA + f_bufsize f <= fst iv \/ snd iv <= BA) W ->
    0 <= f_bufsize f ->
    rw_cells asegs m' (Fp + 104) [C8 (Z_to_bv 64 pv')] ->
    FILE_R m' f Fp BA cf rf sf pv' nx.
  Section Sz5.
  Variables m m' f Fp BA cf rf sf pv pv' nx W : ltac2:(SecDiet.SzSec.tyM 'FILE_R_set_prev__stmt "vvvvvvvvvvvv" @m).
  Lemma FILE_R_set_prev__body : ltac2:(SecDiet.SzSec.bodyP 'FILE_R_set_prev__stmt "vvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros FR MU WM D1 D2 BS PC.
    destruct FR as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP).
    exists flags, mode, rp, tail, bufbytes.
    split; [| split; [exact FL | split; [| split; [exact BP | split; [exact WB0 | split; [exact WBL | split; [exact RR | exact RP]]]]]]].
    - rewrite fcells_split_prev in FC |- *.
      apply (proj1 (rw_cells_app asegs m Fp _ _)) in FC as [FCa FC]. apply (proj1 (rw_cells_app asegs m _ [_] _)) in FC as [_ FCb].
      cbn [cells_size csize Nat.add] in FCa, FCb |- *.
      apply (proj2 (rw_cells_app asegs m' Fp _ _)). split.
      + eapply rw_cells_transport; [exact FCa| exact MU| exact WM|]. cbn [cells_size csize Nat.add].
        apply disjoint_from_Forall. eapply Forall_impl; [| exact D1]. intros [lo hi]; cbn; lia.
      + apply (proj2 (rw_cells_app asegs m' _ [_] _)). cbn [cells_size csize Nat.add]. split.
        * replace (Fp + Z.of_nat 104) with (Fp + 104) by lia. exact PC.
        * eapply rw_cells_transport; [exact FCb| exact MU| exact WM|]. cbn [cells_size csize Nat.add].
          apply disjoint_from_Forall. eapply Forall_impl; [| exact D1]. intros [lo hi]; cbn; lia.
    - eapply rw_cells_transport; [exact BUF | exact MU | exact WM |]. cbn [cells_size csize Nat.add].
      apply disjoint_from_Forall. eapply Forall_impl; [| exact D2]. intros [lo hi]; cbn; lia.
  Qed.
  End Sz5.
  Lemma FILE_R_set_prev : ltac:(let t := eval cbv delta [FILE_R_set_prev__stmt] in FILE_R_set_prev__stmt in exact t).
  Proof using Type. intros m m' f Fp BA cf rf sf pv pv' nx W. ltac2:(SecDiet.SzSec.closeP 'FILE_R_set_prev__body "vvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma block_rangeA : forall L RNG (s : PS) CL FB FL m b, GIOA L RNG s CL FB FL m -> In b (CL ++ FB) ->
    0x604000 <= cb_addr b /\ 0 <= cb_size b /\ cb_addr b + cb_size b <= ATOP
    /\ (cb_addr b + cb_size b <= 0x7fff7000 \/ 0x10007fff8000 <= cb_addr b).
  Proof using GL. pin_using (fun (GL : unit) => tt).
    intros L RNG s CL FB FL m b G HIN.
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ b G HIN) as ((ABLK & N0 & TOP & _) & _).
    unfold ablk, AIMG_HI, KLS in ABLK. lia.
  Qed.

  (* [comment removed for export] *)
  Definition fopen_finishA__stmt : Prop := forall L RNG (sM : PS) (CL FB : list cblk) FL m3 m7 W q A fd (wr : bool) (fl : Z) junk2 SP,
    GIOA L RNG sM ((q, A, FILE_ALLOC) :: CL) FB FL m3 ->
    munch W m3 m7 -> wmono asegs m3 m7 ->
    Forall (fun iv : Z * Z => (ATOP + 4096 <= fst iv /\ snd iv <= SP) \/ (fst iv = A /\ snd iv = A + 232) \/ (fst iv = A_OFL_HEAD /\ snd iv = A_OFL_HEAD + 8)
                              \/ (FB <> [] /\ fst iv = hd_addr FB + 104 /\ snd iv = hd_addr FB + 112)) W ->
    ATOP + 4096 <= SP ->
    rw_cells asegs m7 A (file_cells (Z_to_bv 64 fl) 0 0 F_STDIO_CLOSE 0 0 0 F_STDIO_READ F_STDIO_WRITE F_STDIO_SEEK (A + 240) 1024 0 (hd_addr FB) fd
                          (Z_to_bv 64 0) 4294967295 (repeat (Z_to_bv 8 0) 80)) ->
    rw_cells asegs m7 (A + 232) [CB 1032 junk2] ->
    rw_cells asegs m7 A_OFL_LOCK [C4 (Z_to_bv 64 0)] -> rw_cells asegs m7 A_OFL_HEAD [C8 (Z_to_bv 64 A)] ->
    (hd_addr FB <> 0 -> rw_cells asegs m7 (hd_addr FB + 104) [C8 (Z_to_bv 64 A)]) ->
    fl = (if wr then 4 else 8) -> 3 <= fd <= 4096 ->
    GIOA L RNG (set_libc (set_files ((q, fdopen_file fd wr) :: lc_files (ps_libc sM)) (ps_libc sM)) sM) CL ((q, A, FILE_ALLOC) :: FB) FL m7
    /\ agrees_on (client_keeps FL CL SP) m3 m7.
  Section Sz7.
  Variables L RNG sM CL FB FL m3 m7 W q A fd wr fl junk2 SP : ltac2:(SecDiet.SzSec.tyM 'fopen_finishA__stmt "vvvvvvvvvvvvvvvv" @L).
  Lemma fopen_finishA__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_finishA__stmt "vvvvvvvvvvvvvvvv").
  Proof using EQB GL GSL HAL. pin_using (fun (EQB GL GSL HAL : unit) => tt).
    intros G MU WM HW CSP FC7 BLK7 OL7 OH7 OLDP7 -> HFD.
    pose proof (gs_stdio _ GSL _ _ _ _ _ _ _ G) as SR.
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    pose proof (@ATOP_lo rc) as ATL.
    pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G) as BA.
    pose proof (block_rangeA _ _ _ _ _ _ _ (q, A, FILE_ALLOC) G ltac:(apply in_or_app; left; left; reflexivity)) as (BK1 & _ & BK3 & BK4).
    unfold cb_addr, cb_size, FILE_ALLOC in BK1, BK3, BK4. cbn [fst snd] in BK1, BK3, BK4.
    assert (APb : forall b, In b (CL ++ FB) -> apart (q, A, FILE_ALLOC) b).
    { intros b Hb. cbn [app blocks_apart] in BA. destruct BA as [APc _]. exact (proj1 (Forall_forall _ _) APc _ Hb). }
    (* [comment removed for export] *)
    assert (FBn : forall q2 A2 n2, In (q2, A2, n2) FB -> n2 = FILE_ALLOC /\ 0x604000 <= A2 /\ A2 + 1264 <= ATOP /\ (A + 1264 <= A2 \/ A2 + 1264 <= A)).
    { intros q2 A2 n2 HIN. destruct (files_R_pick eqb EQB m3 0 _ FB q2 A2 n2 FS ND HIN) as (f & pv & nx & _ & _ & En & B0 & _). subst n2.
      pose proof (block_rangeA _ _ _ _ _ _ _ (q2, A2, FILE_ALLOC) G ltac:(apply in_or_app; right; exact HIN)) as (K1 & _ & K3 & _).
      pose proof (APb (q2, A2, FILE_ALLOC) ltac:(apply in_or_app; right; exact HIN)) as AP.
      unfold apart, cb_addr, cb_size, FILE_ALLOC in *. cbn [fst snd] in *. repeat split; lia. }
    (* [comment removed for export] *)
    assert (HDB : forall q1 A1' n1 FB', FB = (q1, A1', n1) :: FB' ->
              n1 = FILE_ALLOC /\ 0x604000 <= A1' /\ A1' + 1264 <= ATOP /\ (A + 1264 <= A1' \/ A1' + 1264 <= A) /\ Forall (apart (q1, A1', n1)) FB').
    { intros q1 A1' n1 FB' E. destruct (FBn q1 A1' n1 ltac:(rewrite E; left; reflexivity)) as (En & K1 & K2 & K3).
      split; [exact En|]. split; [exact K1|]. split; [exact K2|]. split; [exact K3|].
      pose proof (blocks_apart_app_inv _ _ BA) as (_ & BA2 & _). rewrite E in BA2. cbn [blocks_apart] in BA2. exact (proj1 BA2). }
    (* [comment removed for export] *)
    set (P37 := fun a : Z => ~ (ATOP + 4096 <= a < SP) /\ ~ (A <= a < A + 232) /\ ~ (A_OFL_HEAD <= a < A_OFL_HEAD + 8)
                             /\ ~ (FB <> [] /\ hd_addr FB + 104 <= a < hd_addr FB + 112)).
    assert (AG : agrees_on P37 m3 m7).
    { eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha (N1 & N2 & N3 & N4).
      eapply outside_of_Forall. eapply Forall_impl; [| exact HW]. intros [lo' hi'] Hiv; cbn [fst snd] in Hiv |- *.
      destruct Hiv as [X|[X|[X|(Xne & X1 & X2)]]]; [lia| lia| lia|]. intros Hin. apply N4. split; [exact Xne| lia]. }
    (* [comment removed for export] *)
    assert (HSt : forall a, stdio_static a -> ~ (A_OFL_HEAD <= a < A_OFL_HEAD + 8) -> P37 a).
    { intros a Hs Hn. unfold stdio_static, A_OFL_HEAD in *. subst P37. cbn beta.
      split; [lia|]. split; [lia|]. split; [exact Hn|].
      intros (Xne & Xr). destruct FB as [|[[q1 A1'] n1] FB']; [exact (Xne eq_refl)|]. cbn [hd_addr] in Xr.
      destruct (HDB q1 A1' n1 FB' eq_refl) as (_ & K4 & _). lia. }
    (* [comment removed for export] *)
    assert (HBl : forall q2 A2 n2 a, In (q2, A2, n2) FB -> A2 <= a < A2 + 1264 -> ~ (A2 = hd_addr FB /\ A2 + 104 <= a < A2 + 112) -> P37 a).
    { intros q2 A2 n2 a HIN Ha Hn. destruct (FBn _ _ _ HIN) as (-> & K1 & K2 & K3).
      subst P37. cbn beta. unfold A_OFL_HEAD. split; [lia|]. split; [lia|]. split; [lia|].
      intros (Xne & Xr). destruct FB as [|[[q1 A1'] n1] FB']; [exact (Xne eq_refl)|]. cbn [hd_addr] in Xr, Hn.
      destruct (HDB q1 A1' n1 FB' eq_refl) as (En1 & _ & _ & _ & APh).
      destruct HIN as [E|HIN].
      - injection E as <- <- _. apply Hn. split; [reflexivity| lia].
      - pose proof (proj1 (Forall_forall _ _) APh _ HIN) as AP2. unfold apart, cb_addr, cb_size in AP2. cbn [fst snd] in AP2. subst n1. unfold FILE_ALLOC in AP2. lia. }
    (* [comment removed for export] *)
    assert (SR7 : STDIOR (set_files ((q, fdopen_file fd wr) :: lc_files (ps_libc sM)) (ps_libc sM)) ((q, A, FILE_ALLOC) :: FB) m7).
    { unfold STDIOR. cbn [lc_stdout lc_stderr lc_files set_files hd_addr].
      pose proof SOI as (_ & _ & SObs & _). pose proof SEI as (_ & _ & SEbs & _).
      unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED in *.
      split. { eapply FILE_R_agree; [exact SO | exact AG | intros a Ha; apply HSt; [unfold stdio_static; lia| unfold A_OFL_HEAD; lia]
                                     | rewrite SObs; unfold BUFSIZ; intros a Ha; apply HSt; [unfold stdio_static; lia| unfold A_OFL_HEAD; lia]]. }
      split; [exact SOI|].
      split. { eapply FILE_R_agree; [exact SE | exact AG | intros a Ha; apply HSt; [unfold stdio_static; lia| unfold A_OFL_HEAD; lia]
                                     | rewrite SEbs; intros a Ha; apply HSt; [unfold stdio_static; lia| unfold A_OFL_HEAD; lia]]. }
      split; [exact SEI|].
      split. { eapply agrees_rw_cells; [exact AG | exact SIN |]. unfold stdin_cells. rewrite file_cells_size. intros a Ha; apply HSt; [unfold stdio_static; lia| unfold A_OFL_HEAD; lia]. }
      split; [eapply agrees_rw_cells; [exact AG | exact U1 | intros a Ha; cbn in Ha; apply HSt; [unfold stdio_static; lia| unfold A_OFL_HEAD; lia]]|].
      split; [eapply agrees_rw_cells; [exact AG | exact U2 | intros a Ha; cbn in Ha; apply HSt; [unfold stdio_static; lia| unfold A_OFL_HEAD; lia]]|].
      split; [eapply agrees_rw_cells; [exact AG | exact U3 | intros a Ha; cbn in Ha; apply HSt; [unfold stdio_static; lia| unfold A_OFL_HEAD; lia]]|].
      split; [exact OL7|]. split; [exact OH7|].
      split.
      - cbn [files_R]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [unfold FILE_ALLOC; lia|].
        split.
        { (* [comment removed for export] *)
          exists (Z_to_bv 64 (if wr then 4 else 8)), (Z_to_bv 64 0), 0, (repeat (Z_to_bv 8 0) 80), (firstn 1024 (skipn 8 junk2)).
          cbn [f_rbuf f_wbuf f_wactive f_bufsize f_fd f_nord f_nowr f_eof f_stdoutw f_lbf_nl fdopen_file wfn_of lbf_of zlength length Z.of_nat Z.add].
          split. { unfold fcells, FILE_BUF_OFF, BUFSIZ. exact FC7. }
          split. { unfold flags_ok. cbn [f_nord f_nowr f_eof f_chan]. unfold F_NORD, F_NOWR, F_EOF, F_ERR, F_SVB, F_PERM. destruct wr; rewrite unsigned_lit by lia; cbn; repeat split; reflexivity. }
          split. { pose proof (rw_cells_split_CB asegs m7 (A + 232) [] 1032 junk2 [] [8%nat; 1024%nat] BLK7 eq_refl) as B2.
                   cbn [app mk_CB_cells] in B2. apply rw_cells_split2 in B2 as [_ B2]. cbn [csize] in B2.
                   unfold FILE_BUF_OFF, BUFSIZ. replace (A + 232 + Z.of_nat 8) with (A + 240) in B2 by lia. exact B2. }
          split; [reflexivity|]. split; [intros _; reflexivity|]. split; [unfold BUFSIZ, zlength; cbn; lia|].
          split; [intros X; exfalso; exact (X eq_refl)|]. first [ assumption | (split; [lia|]; split; [unfold zlength; cbn; lia| reflexivity]) | (unfold zlength; cbn; lia)]. }
        split.
        { unfold heap_file_inv. cbn. destruct wr; cbn.
          all: split; [reflexivity|]; split; [lia|]; split; [reflexivity|]; split; [reflexivity|].
          all: split; [intros X; first [discriminate X | split; reflexivity] |]; split; [intros X; first [discriminate X | reflexivity]| apply Forall_nil]. }
        (* [comment removed for export] *)
        eapply files_R_newhead; [exact FS| |].
        + intros q1 A1' n1 f1 FB' E FR1 INV1.
          destruct (HDB q1 A1' n1 FB' E) as (En1 & KS & KC & AP1 & APh).
          pose proof INV1 as (_ & _ & BS1 & _).
          eapply (FILE_R_set_prev m3 m7 f1 A1' _ _ _ _ 0 A (hd_addr FB') W); [exact FR1| exact MU| exact WM| | | rewrite BS1; unfold BUFSIZ; lia|].
          * eapply Forall_impl; [| exact HW]. intros [lo' hi'] X; cbn [fst snd] in *.
            destruct X as [X|[X|[X|(Xne & X1 & X2)]]]; [left; lia| left; lia| left; unfold A_OFL_HEAD in X; lia| right]. rewrite E in X1, X2. cbn [hd_addr] in X1, X2. lia.
          * rewrite BS1. unfold BUFSIZ, FILE_BUF_OFF. eapply Forall_impl; [| exact HW]. intros [lo' hi'] X; cbn [fst snd] in *.
            destruct X as [X|[X|[X|(Xne & X1 & X2)]]]; [lia| lia| unfold A_OFL_HEAD in X; lia|]. rewrite E in X1, X2. cbn [hd_addr] in X1, X2. lia.
          * rewrite E in OLDP7. cbn [hd_addr] in OLDP7. apply OLDP7. lia.
        + intros q2 A2 n2 f2 pv2 nx2 HIN2 FR2 INV2.
          assert (HIN2' : In (q2, A2, n2) FB) by (destruct FB as [|b FB']; [exact HIN2| right; exact HIN2]).
          pose proof INV2 as (_ & _ & BS2 & _).
          assert (NH : A2 <> hd_addr FB).
          { destruct FB as [|[[q1 A1'] n1] FB']; [exact (False_ind _ HIN2)|]. cbn [hd_addr tl] in HIN2 |- *.
            destruct (HDB q1 A1' n1 FB' eq_refl) as (En1 & _ & _ & _ & APh).
            pose proof (proj1 (Forall_forall _ _) APh _ HIN2) as AP2. unfold apart, cb_addr, cb_size in AP2. cbn [fst snd] in AP2.
            destruct (FBn _ _ _ HIN2') as [-> _]. subst n1. unfold FILE_ALLOC in AP2. lia. }
          eapply FILE_R_agree; [exact FR2| exact AG| |].
          * intros a Ha. eapply (HBl q2 A2 n2 a HIN2'); [lia|]. intros [X _]. exact (NH X).
          * rewrite BS2. unfold BUFSIZ, FILE_BUF_OFF. intros a Ha. eapply (HBl q2 A2 n2 a HIN2'); [lia|]. intros [X _]. exact (NH X).
      - (* [comment removed for export] *)
        cbn [map fst]. apply List.NoDup_cons; [| exact ND].
        intros HIn. rewrite <- (files_R_toks m3 0 _ FB FS) in HIn. apply in_map_iff in HIn as ([[qb Ab] nb] & Eb & HbIn). cbn in Eb. subst qb.
        pose proof (HAL _ _ _ _ _ _ _ (q, A, FILE_ALLOC) G ltac:(apply in_or_app; left; left; reflexivity)) as E1.
        pose proof (HAL _ _ _ _ _ _ _ (q, Ab, nb) G ltac:(apply in_or_app; right; exact HbIn)) as E2.
        cbn [cb_tok cb_addr fst snd] in E1, E2.
        destruct (FBn _ _ _ HbIn) as (-> & _ & _ & AP). lia. }
    (* [comment removed for export] *)
    assert (HWA : Forall (stdio_ivA ((q, A, FILE_ALLOC) :: FB) SP) W).
    { eapply Forall_impl; [| exact HW]. intros [lo' hi'] X; cbn [fst snd] in X. unfold stdio_ivA; cbn [fst snd].
      destruct X as [X|[X|[X|(Xne & X1 & X2)]]].
      - left. exact X.
      - right; left. unfold iv_in_block. apply Exists_cons_hd. unfold cb_addr, cb_size, FILE_ALLOC; cbn [fst snd]. lia.
      - right; right; right; left. unfold A_OFL_HEAD in X. lia.
      - right; left. destruct FB as [|[[q1 A1'] n1] FB']; [exfalso; exact (Xne eq_refl)|]. cbn [hd_addr] in X1, X2.
        destruct (HDB q1 A1' n1 FB' eq_refl) as (En1 & _). unfold iv_in_block. apply Exists_cons_tl. apply Exists_cons_hd.
        unfold cb_addr, cb_size; cbn [fst snd]. subst n1. unfold FILE_ALLOC. lia. }
    (* [comment removed for export] *)
    assert (WBLK : forall lo' hi' a, In (lo', hi') W -> lo' <= a < hi' ->
              (ATOP + 4096 <= a < SP) \/ (A_OFL_HEAD <= a < A_OFL_HEAD + 8)
              \/ (in_block (((q, A, FILE_ALLOC) :: CL) ++ FB) a /\ ~ in_block CL a)).
    { intros lo' hi' a HIN Ha. pose proof (proj1 (Forall_forall _ _) HW _ HIN) as X. cbn [fst snd] in X.
      destruct X as [X|[X|[X|(Xne & X1 & X2)]]]; [left; lia | right; right | right; left; lia | right; right].
      - split.
        + apply in_block_In. exists (q, A, FILE_ALLOC). split; [apply in_or_app; left; left; reflexivity | unfold cb_addr, cb_size, FILE_ALLOC; cbn [fst snd]; lia].
        + intros K. apply in_block_In in K as (b & Hb & Rb). pose proof (APb b ltac:(apply in_or_app; left; exact Hb)) as AP.
          unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP. unfold cb_addr, cb_size in Rb. lia.
      - destruct FB as [|[[q1 A1'] n1] FB']; [exfalso; exact (Xne eq_refl)|]. cbn [hd_addr] in X1, X2.
        destruct (HDB q1 A1' n1 FB' eq_refl) as (En1 & _). subst n1. split.
        + apply in_block_In. exists (q1, A1', FILE_ALLOC). split; [apply in_or_app; right; left; reflexivity | unfold cb_addr, cb_size, FILE_ALLOC; cbn [fst snd]; lia].
        + intros K. apply in_block_In in K as (b & Hb & Rb).
          pose proof (blocks_apart_app_inv _ _ BA) as (_ & _ & BAX).
          pose proof (BAX b (q1, A1', FILE_ALLOC) ltac:(right; exact Hb) ltac:(left; reflexivity)) as AP.
          unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP. unfold cb_addr, cb_size in Rb. lia. }
    assert (ERR7 : exists e' : word, rw_cells asegs m7 (ATP + -164) [C4 e']).
    { destruct (gs_errno _ GSL _ _ _ _ _ _ _ G) as [e ERR]. exists e.
      eapply (agrees_rw_cells (fun a => ATP + -164 <= a < ATP + -160)); [| exact ERR | cbn [cells_size csize Nat.add]; intros a Ha; lia].
      eapply agrees_on_of_munch; [exact MU | exact WM |]. intros a Ha Hc.
      pose proof (@ATPv_hi rc tlsI) as TH. pose proof (@ATPv_img rc tlsI) as TI. unfold ATP in *.
      apply outside_of_Forall. apply Forall_forall. intros [lo' hi'] HIN. cbn [fst snd]. intros Hin.
      destruct (WBLK lo' hi' a HIN Hin) as [X|[X|[X _]]]; [lia | unfold A_OFL_HEAD in X; lia |].
      apply (gl_tls_apart _ _ _ GL _ _ _ _ _ _ _ a G (or_introl X)). unfold ATP. lia. }
    split.
    - eapply (gs_adopt _ GSL L RNG sM CL FB FL m3 m7 W SP _ q A); [exact G| exact MU| exact WM| exact HWA| exact CSP| exact ERR7| exact SR7].
    - (* [comment removed for export] *)
      eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hk.
      apply outside_of_Forall. apply Forall_forall. intros [lo' hi'] HIN. cbn [fst snd]. intros Hin.
      destruct (WBLK lo' hi' a HIN Hin) as [X|[X|[X NX]]].
      + destruct Hk as [K|[K|[K|K]]]; [lia| | |].
        * pose proof (gia_in_block_below FO GIOA fflagA GL _ _ _ _ _ _ _ a G ltac:(apply in_block_app; left; apply in_block_In; apply in_block_In in K as (b & Hb & Rb); exists b; split; [right; exact Hb | exact Rb])) as [_ B1]. lia.
        * pose proof (gia_in_frames_below FO GIOA fflagA GL _ _ _ _ _ _ _ a G K) as [_ B1]. lia.
        * pose proof (gia_in_frame_sh_band FO GIOA fflagA GL _ _ _ _ _ _ _ a G K) as [_ B1]. lia.
      + unfold A_OFL_HEAD in X. destruct Hk as [K|[K|[K|K]]]; [lia| | |].
        * apply in_block_In in K as (b & Hb & Rb).
          pose proof (block_rangeA _ _ _ _ _ _ _ b G ltac:(apply in_or_app; left; right; exact Hb)) as (K1 & _). lia.
        * apply in_frames_In in K as (fr & Hf & Rf).
          destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FA _]. pose proof (proj1 (Forall_forall _ _) FA fr Hf) as (BAND & _).
          unfold ablk, AIMG_HI, KLS in BAND. lia.
        * pose proof (gia_in_frame_sh_band FO GIOA fflagA GL _ _ _ _ _ _ _ a G K) as [B0 _]. lia.
      + destruct Hk as [K|[K|[K|K]]].
        * pose proof (gia_in_block_below FO GIOA fflagA GL _ _ _ _ _ _ _ a G X) as [_ B1]. lia.
        * exact (NX K).
        * exact (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G K X).
        * pose proof (gia_in_frame_sh_band FO GIOA fflagA GL _ _ _ _ _ _ _ a G K) as [B0 B1].
          apply in_block_In in X as (b & Hb & Rb).
          pose proof (block_rangeA _ _ _ _ _ _ _ b G Hb) as (_ & _ & _ & K4). lia.
  Qed.
  End Sz7.
  Lemma fopen_finishA : ltac:(let t := eval cbv delta [fopen_finishA__stmt] in fopen_finishA__stmt in exact t).
  Proof using EQB GL GSL HAL. intros L RNG sM CL FB FL m3 m7 W q A fd wr fl junk2 SP. ltac2:(SecDiet.SzSec.closeP 'fopen_finishA__body "vvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition robjA_factsA__stmt : Prop := forall L RNG (s : PS) CL FB FL m D n lo,
    GIOA L RNG s CL FB FL m -> robjA RNG m FL CL D n -> 0 < n <= 2^40 -> ATOP + 4096 <= lo ->
    0 < D /\ D + n + 8 <= lo /\ sobj RNG m D (D + n) /\ rng RNG D n.
  Section Sz8.
  Variables L RNG s CL FB FL m D n lo : ltac2:(SecDiet.SzSec.tyM 'robjA_factsA__stmt "vvvvvvvvvv" @L).
  Lemma robjA_factsA__body : ltac2:(SecDiet.SzSec.bodyP 'robjA_factsA__stmt "vvvvvvvvvv").
  Proof using GL. pin_using (fun (GL : unit) => tt).
    intros G [LOC MO] Hn LOA.
    pose proof MO as (D0 & _ & _ & RG & _ & _). pose proof (@ATOP_lo rc) as ATL.
    split; [exact D0|]. split; [| split; [apply mobjA_sobj; [exact MO | lia] | exact RG]].
    destruct LOC as [[(b & Hb & B1 & B2) | (fr & Hf & F1 & F2)] | (g & Hg & G1 & G2 & G3)].
    - pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ b G ltac:(apply in_or_app; left; exact Hb)) as ((_ & _ & TOP & _) & _). lia.
    - destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FA _]. pose proof (proj1 (Forall_forall _ _) FA fr Hf) as (BAND & _).
      unfold ablk, AIMG_HI, KLS in BAND. lia.
    - lia.
  Qed.
  End Sz8.
  Lemma robjA_factsA : ltac:(let t := eval cbv delta [robjA_factsA__stmt] in robjA_factsA__stmt in exact t).
  Proof using GL. intros L RNG s CL FB FL m D n lo. ltac2:(SecDiet.SzSec.closeP 'robjA_factsA__body "vvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma implMG_sysk : forall {A B} RNG (n : node) (dec : resp -> option A) (k : A -> M PS B) (s : PS) Q ms,
    match n with NMmap _ _ _ _ | NMunmap _ _ | NBrk _ | NMprotect _ _ _ => False | _ => True end ->
    evtF asegs RNG (fun ms1 => at_nodeA asegs n RNG ms1 /\
                            (forall rsp a, dec rsp = Some a -> implMG RNG (k a) s Q (nret ms1 rsp))) ms ->
    implMG RNG (mbind (msys n dec) k) s Q ms.
  Proof using Type. pin_using tt.
    intros A B RNG n dec k s Q ms Hn HE. unfold implMG, mbind, msys, ebind, enode in *. cbn [ITree.bind ITreeA.implF].
    apply evtS_of_evtF. eapply evtF_mono; [exact HE|]. intros ms1 [Hat Hk]. left. split; [exact Hat|].
    intros rsp RNG' HF.
    assert (ER : RNG' = RNG).
    { destruct HF as [HF _]. destruct n; try destruct Hn; cbn in HF; exact HF. }
    subst RNG'. destruct (dec rsp) as [a|] eqn:E; cbn [ITree.bind fst snd].
    - exact (Hk rsp a E).
    - apply implF_ret_unr.
  Qed.

  (* [comment removed for export] *)
  Definition live_block_factsA__stmt : Prop := forall L RNG (s : PS) CL FB FL m q A n lo,
    GIOA L RNG s CL FB FL m -> In (q, A, n) (CL ++ FB) -> ATOP + 4096 <= lo -> n <= 2^40 ->
    0 < A /\ 0 <= n /\ A + n <= lo /\ 0x604000 <= A /\ A + n <= ATOP /\ sobj RNG m A (A + n) /\ rng RNG A n.
  Section Sz10.
  Variables L RNG s CL FB FL m q A n lo : ltac2:(SecDiet.SzSec.tyM 'live_block_factsA__stmt "vvvvvvvvvvv" @L).
  Lemma live_block_factsA__body : ltac2:(SecDiet.SzSec.bodyP 'live_block_factsA__stmt "vvvvvvvvvvv").
  Proof using GL. pin_using (fun (GL : unit) => tt).
    intros G HIN LOA N40.
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ (q, A, n) G HIN) as (AR & A0 & UNP & RG & RSH & ARENA).
    unfold cb_addr, cb_size in *. cbn [fst snd] in *.
    destruct AR as (ABLK & N0 & ATOPB & _).
    assert (LOW : 0x604000 <= A) by (unfold ablk, AIMG_HI, KLS in ABLK; lia).
    split; [exact A0|]. split; [exact N0|]. split; [lia|]. split; [exact LOW|]. split; [exact ATOPB|]. split; [| exact RG].
    destruct ARENA as (RLO & RHI & R1 & R2 & R3 & R4 & R5 & R6 & WR & RS).
    split; [apply ablk_app_blk; [exact ABLK | lia]|]. split; [exact UNP|]. split; [lia|]. exists RLO, RHI. split; [repeat split; assumption|]. split; assumption.
  Qed.
  End Sz10.
  Lemma live_block_factsA : ltac:(let t := eval cbv delta [live_block_factsA__stmt] in live_block_factsA__stmt in exact t).
  Proof using GL. intros L RNG s CL FB FL m q A n lo. ltac2:(SecDiet.SzSec.closeP 'live_block_factsA__body "vvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition GIOA_errno_step__stmt : Prop := forall L RNG (s : PS) CL FB FL m m' W SP (l' : libc_st hptr) (e' : word),
    GIOA L RNG s CL FB FL m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => (ATOP + 4096 <= fst iv /\ snd iv <= SP) \/ (ATP + -164 <= fst iv /\ snd iv <= ATP + -160)) W -> ATOP + 4096 <= SP ->
    rw_cells asegs m' (ATP + -164) [C4 e'] ->
    lc_stdout l' = lc_stdout (ps_libc s) -> lc_stderr l' = lc_stderr (ps_libc s) -> lc_files l' = lc_files (ps_libc s) ->
    GIOA L RNG (set_libc l' s) CL FB FL m' /\ agrees_on (client_keeps FL CL SP) m m'.
  Section Sz11.
  Variables L RNG s CL FB FL m m' W SP l' e' : ltac2:(SecDiet.SzSec.tyM 'GIOA_errno_step__stmt "vvvvvvvvvvvv" @L).
  Lemma GIOA_errno_step__body : ltac2:(SecDiet.SzSec.bodyP 'GIOA_errno_step__stmt "vvvvvvvvvvvv").
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
    intros G MU WM HW HSP ERR' E1 E2 E3.
    assert (HW' : Forall (stdio_ivA FB SP) W).
    { eapply Forall_impl; [| exact HW]. intros iv [X|X]; [left; exact X | right; right; right; right; exact X]. }
    pose proof (gs_stdio _ GSL _ _ _ _ _ _ _ G) as SR.
    rewrite <- (app_nil_r W) in MU.
    split.
    - eapply (gs_step _ GSL L RNG s CL FB FL m m' W [] SP l'); [exact G | exact MU | exact WM | exact HW' | apply Forall_nil | exact HSP | exists e'; exact ERR' |].
      assert (SR' : STDIOR l' FB m) by (unfold STDIOR in SR |- *; rewrite E1, E2, E3; exact SR).
      eapply (STDIOR_agree l' FB m m' (fun a => stdio_static a \/ in_block FB a)); [exact SR' | | intros a Ha; left; exact Ha | intros a Ha; right; exact Ha].
      eapply agrees_on_of_munch; [exact MU | exact WM |]. intros a Ha Hc. rewrite app_nil_r.
      pose proof (@ATPv_hi rc tlsI) as TH. pose proof (@ATPv_imgk rc tlsI) as (TI1 & TI2). pose proof (@kt_rng rc tlsI) as ((KI & _) & _).
      pose proof (@ATOP_lo rc) as ATL.
      assert (NT : ~ (ATP + -164 <= a < ATP + -160) /\ a < ATOP + 4096).
      { destruct Hc as [Hs | Hb].
        - unfold stdio_static in Hs. unfold ATP. clear - Hs TH TI1 TI2 KI ATL. lia.
        - split.
          + intros X. assert (HB' : in_block (CL ++ FB) a) by (apply in_block_app; right; exact Hb).
            apply (gl_tls_apart _ _ _ GL _ _ _ _ _ _ _ a G (or_introl HB')). clear - X. lia.
          + apply in_block_In in Hb as (b & HIN & HR).
            pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ b G ltac:(apply in_or_app; right; exact HIN)) as ((_ & _ & TOP & _) & _). clear - HR TOP. lia. }
      destruct NT as [NT1 NT2]. clear - HW NT1 NT2.
      induction HW as [|[lo hi] W Hiv HW IH]; cbn [outside]; [exact I|]. split; [| exact IH]. cbn [fst snd] in Hiv. lia.
    - eapply agrees_on_weaken; [eapply (gs_keeps _ GSL L RNG s CL FB FL m m' W [] SP); [exact G | exact MU | exact WM | exact HW' | exact HSP]|].
      intros a Ha. split; [exact Ha | exact I].
  Qed.
  End Sz11.
  Lemma GIOA_errno_step : ltac:(let t := eval cbv delta [GIOA_errno_step__stmt] in GIOA_errno_step__stmt in exact t).
  Proof using GL GSL. intros L RNG s CL FB FL m m' W SP l' e'. ltac2:(SecDiet.SzSec.closeP 'GIOA_errno_step__body "vvvvvvvvvvvv"). Qed.

End GlueFo.
End TwB.
End Stdio_glue_foKitA.

(* [comment removed for export] *)
Module Stdio_glue_fcA.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_cs__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_lock__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_read__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_ahm I_fflush I_fclose Stdio_repA Stdio_glueKitA Stdio_glue_fcKitA StdioLawsA Stdio_glueA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_lock OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdio_cs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_read__A3S.F_stdio_read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_toread OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fflush OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fclose OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_ahm OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fflush OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fclose OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_fcKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioLawsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_foKitA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section GlueFc.
  Context {rc : runConstT} {tlsI : ABase.atlsT}.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GSL : gia_stdio_laws GIOA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  #[local] Abbreviation eqb := (ho_eqb HO).
  (* [comment removed for export] *)
  Hypothesis FREE : free_stmt_o HO GIOA.
  Hypothesis FREENULL : free_null_stmt_o GIOA.
  Hypothesis TPFC : forall L ra trC, tp_fclose TP L ra trC -> In [AFREE_PC; 0x9a2ac] (al_U L) /\ In [AFREE_PC; 0x9a2a4] (al_U L).

  (* [comment removed for export] *)
  #[local] Notation spo_factsA := (Stdio_glueA.spo_factsA GIOA GSL).
  #[local] Notation errno_cell_kept := (Stdio_glueA.errno_cell_kept FO GIOA fflagA GL GSL).
  #[local] Notation block_rangeA := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_foKitA.block_rangeA FO GIOA fflagA GL).
  #[local] Notation live_block_factsA := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_foKitA.live_block_factsA FO GIOA fflagA GL).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition fclose_finishA__stmt : Prop := forall L RNG (s : PS) (CL F1 F2 : list cblk) FL m m4 W0 q A SP,
    GIOA L RNG s CL (F1 ++ (q, A, FILE_ALLOC) :: F2) FL m ->
    ps_outfile s <> Some q ->
    munch W0 m m4 -> wmono asegs m m4 ->
    Forall (fun iv : Z * Z => snd iv <= fst iv \/ (ATOP + 4096 <= fst iv /\ snd iv <= SP) \/ (A <= fst iv /\ snd iv <= A + 1264)
                              \/ (fst iv = A_OFL_HEAD /\ snd iv = A_OFL_HEAD + 8)
                              \/ (F1 <> [] /\ fst iv = last_addr 0 F1 + 112 /\ snd iv = last_addr 0 F1 + 120)
                              \/ (F2 <> [] /\ fst iv = hd_addr F2 + 104 /\ snd iv = hd_addr F2 + 112)) W0 ->
    ATOP + 4096 <= SP ->
    rw_cells asegs m4 A_OFL_LOCK [C4 (Z_to_bv 64 0)] -> rw_cells asegs m4 A_OFL_HEAD [C8 (Z_to_bv 64 (hd_addr (F1 ++ F2)))] ->
    (F1 <> [] -> rw_cells asegs m4 (last_addr 0 F1 + 112) [C8 (Z_to_bv 64 (hd_addr F2))]) ->
    (F2 <> [] -> rw_cells asegs m4 (hd_addr F2 + 104) [C8 (Z_to_bv 64 (last_addr 0 F1))]) ->
    GIOA L RNG (set_libc (set_files (files_remove eqb (lc_files (ps_libc s)) q) (ps_libc s)) s) ((q, A, FILE_ALLOC) :: CL) (F1 ++ F2) FL m4
    /\ agrees_on (client_keeps FL CL SP) m m4.
  Section Sz1.
  Variables L RNG s CL F1 F2 FL m m4 W0 q A SP : ltac2:(SecDiet.SzSec.tyM 'fclose_finishA__stmt "vvvvvvvvvvvvv" @L).
  Lemma fclose_finishA__body : ltac2:(SecDiet.SzSec.bodyP 'fclose_finishA__stmt "vvvvvvvvvvvvv").
  Proof using EQB GL GSL. pin_using (fun (EQB GL GSL : unit) => tt).
    intros G NOF MU0 WM HW0 CSP OL4 OH4 LP4 LN4.
    pose proof (munch_drop_empty _ _ _ MU0) as MU. pose proof (Forall_drop_empty _ _ HW0) as HW. cbv beta in HW.
    remember (@List.filter (Z * Z)%type (fun iv : Z * Z => fst iv <? snd iv) W0) as W eqn:EW. clear EW MU0 HW0.
    pose proof (gs_stdio _ GSL _ _ _ _ _ _ _ G) as SR.
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    pose proof (@ATOP_lo rc) as ATL.
    pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G) as BA.
    set (FB := F1 ++ (q, A, FILE_ALLOC) :: F2) in *.
    assert (INb : In (q, A, FILE_ALLOC) FB) by (subst FB; apply in_or_app; right; left; reflexivity).
    assert (INFB : forall b, In b (F1 ++ F2) -> In b FB).
    { intros b Hb. subst FB. apply in_app_or in Hb. apply in_or_app. destruct Hb as [X|X]; [left; exact X| right; right; exact X]. }
    pose proof (blocks_apart_app_inv _ _ BA) as (BAc & BAf & BAX).
    (* [comment removed for export] *)
    assert (FBn : forall q2 A2 n2, In (q2, A2, n2) FB -> n2 = FILE_ALLOC /\ 0 < A2).
    { intros q2 A2 n2 HIN. destruct (files_R_pick eqb EQB m 0 _ FB q2 A2 n2 FS ND HIN) as (f & pv & nx & _ & _ & En & B0 & _). split; [exact En| exact B0]. }
    assert (BKF : forall q2 A2 n2, In (q2, A2, n2) FB -> 0x603000 <= A2 /\ A2 + 1264 <= ATOP).
    { intros q2 A2 n2 HIN. destruct (FBn _ _ _ HIN) as [-> B0].
      pose proof (block_rangeA _ _ _ _ _ _ _ (q2, A2, FILE_ALLOC) G ltac:(apply in_or_app; right; exact HIN)) as (K1 & _ & K3 & _).
      unfold cb_addr, cb_size, FILE_ALLOC in K1, K3. cbn [fst snd] in K1, K3. lia. }
    (* [comment removed for export] *)
    assert (APF : forall q2 A2 n2 q3 A3 n3, In (q2, A2, n2) FB -> In (q3, A3, n3) FB -> A2 <> A3 -> A2 + 1264 <= A3 \/ A3 + 1264 <= A2).
    { intros q2 A2 n2 q3 A3 n3 HIN2 HIN3 NE. destruct (FBn _ _ _ HIN2) as [-> _]. destruct (FBn _ _ _ HIN3) as [-> _].
      destruct (blocks_apart_In _ _ _ BAf HIN2 HIN3) as [E|AP]; [exfalso; apply NE; injection E as E1 E2; exact E2|].
      unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP. exact AP. }
    assert (DIST : forall q2 A2 n2 q3 A3 n3, In (q2, A2, n2) FB -> In (q3, A3, n3) FB -> A2 = A3 -> q2 = q3).
    { intros q2 A2 n2 q3 A3 n3 HIN2 HIN3 E. destruct (FBn _ _ _ HIN2) as [-> _]. destruct (FBn _ _ _ HIN3) as [-> _].
      destruct (blocks_apart_In _ _ _ BAf HIN2 HIN3) as [E'|AP]; [injection E' as E1 E2; exact E1|].
      unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP. lia. }
    pose proof (BKF _ _ _ INb) as (BK1 & BK2).
    (* [comment removed for export] *)
    assert (HL : F1 <> [] -> exists ql nl, In (ql, last_addr 0 F1, nl) F1) by (intros NE; exact (last_addr_In 0 F1 NE)).
    assert (HN : F2 <> [] -> exists qn nn, In (qn, hd_addr F2, nn) F2) by (intros NE; exact (hd_addr_In F2 NE)).
    (* [comment removed for export] *)
    set (P4 := fun a : Z => ~ (ATOP + 4096 <= a < SP) /\ ~ (A <= a < A + 1264) /\ ~ (A_OFL_HEAD <= a < A_OFL_HEAD + 8)
                            /\ ~ (F1 <> [] /\ last_addr 0 F1 + 112 <= a < last_addr 0 F1 + 120)
                            /\ ~ (F2 <> [] /\ hd_addr F2 + 104 <= a < hd_addr F2 + 112)).
    assert (AG : agrees_on P4 m m4).
    { eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha (N1 & N2 & N3 & N4 & N5).
      eapply outside_of_Forall. eapply Forall_impl; [| exact HW]. intros [lo' hi'] Hiv; cbn [fst snd] in Hiv |- *.
      destruct Hiv as [X|[X|[X|[(Xne & X1 & X2)|(Xne & X1 & X2)]]]]; [lia| lia| lia| |].
      - intros Hin. apply N4. split; [exact Xne| lia].
      - intros Hin. apply N5. split; [exact Xne| lia]. }
    (* [comment removed for export] *)
    assert (HSt : forall a, stdio_static a -> ~ (A_OFL_HEAD <= a < A_OFL_HEAD + 8) -> P4 a).
    { intros a Hs Hn. unfold stdio_static, A_OFL_HEAD in *. subst P4. cbn beta.
      split; [lia|]. split; [lia|]. split; [exact Hn|]. split.
      - intros (Xne & Xr). destruct (HL Xne) as (ql & nl & HINl).
        destruct (BKF ql _ nl ltac:(subst FB; apply in_or_app; left; exact HINl)) as (K3 & _). lia.
      - intros (Xne & Xr). destruct (HN Xne) as (qn & nn & HINn).
        destruct (BKF qn _ nn ltac:(subst FB; apply in_or_app; right; right; exact HINn)) as (K3 & _). lia. }
    (* [comment removed for export] *)
    assert (SR4 : STDIOR (set_files (files_remove eqb (lc_files (ps_libc s)) q) (ps_libc s)) (F1 ++ F2) m4).
    { unfold STDIOR. cbn [lc_stdout lc_stderr lc_files set_files].
      pose proof SOI as (_ & _ & SObs & _). pose proof SEI as (_ & _ & SEbs & _).
      unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED in *.
      split. { eapply FILE_R_agree; [exact SO | exact AG | intros a Ha; apply HSt; [unfold stdio_static; lia| unfold A_OFL_HEAD; lia]
                                     | rewrite SObs; unfold BUFSIZ; intros a Ha; apply HSt; [unfold stdio_static; lia| unfold A_OFL_HEAD; lia]]. }
      split; [exact SOI|].
      split. { eapply FILE_R_agree; [exact SE | exact AG | intros a Ha; apply HSt; [unfold stdio_static; lia| unfold A_OFL_HEAD; lia]
                                     | rewrite SEbs; intros a Ha; apply HSt; [unfold stdio_static; lia| unfold A_OFL_HEAD; lia]]. }
      split; [exact SEI|].
      split. { eapply agrees_rw_cells; [exact AG | exact SIN |]. unfold stdin_cells. rewrite file_cells_size. intros a Ha; apply HSt; [unfold stdio_static; lia| unfold A_OFL_HEAD; lia]. }
      split; [eapply agrees_rw_cells; [exact AG | exact U1 | intros a Ha; cbn in Ha; apply HSt; [unfold stdio_static; lia| unfold A_OFL_HEAD; lia]]|].
      split; [eapply agrees_rw_cells; [exact AG | exact U2 | intros a Ha; cbn in Ha; apply HSt; [unfold stdio_static; lia| unfold A_OFL_HEAD; lia]]|].
      split; [eapply agrees_rw_cells; [exact AG | exact U3 | intros a Ha; cbn in Ha; apply HSt; [unfold stdio_static; lia| unfold A_OFL_HEAD; lia]]|].
      split; [exact OL4|]. split; [exact OH4|].
      split; [| apply (NoDup_files_remove eqb); exact ND].
      subst FB. eapply (files_R_unlink eqb EQB P4); [exact FS| exact ND| exact AG| | exact DIST| exact LP4| exact LN4| lia|].
      - intros q2 A2 n2 a HIN2 Ha Hn1 Hn2.
        assert (HIN2' : In (q2, A2, n2) (F1 ++ (q, A, FILE_ALLOC) :: F2)) by (apply INFB; exact HIN2).
        destruct (BKF _ _ _ HIN2') as (K1 & K2).
        assert (NA : A2 <> A).
        { intros E. pose proof (DIST q2 A2 n2 q A FILE_ALLOC HIN2' INb E) as Eq.
          (* [comment removed for export] *)
          pose proof (files_R_toks m 0 _ _ FS) as TK.
          assert (NDT : List.NoDup (map cb_tok (F1 ++ (q, A, FILE_ALLOC) :: F2))) by (rewrite TK; exact ND).
          rewrite map_app in NDT. cbn [map cb_tok fst snd] in NDT. apply List.NoDup_remove_1 in NDT as NDT'.
          apply (List.NoDup_remove_2 _ _ _ NDT). rewrite <- map_app. subst q2.
          change q with (cb_tok (q, A2, n2)). apply in_map. exact HIN2. }
        pose proof (APF _ _ _ _ _ _ HIN2' INb NA) as APA.
        subst P4. cbn beta. unfold A_OFL_HEAD. split; [lia|]. split; [lia|]. split; [lia|]. split.
        + intros (Xne & Xr). destruct (HL Xne) as (ql & nl & HINl).
          destruct (Z.eq_dec A2 (last_addr 0 F1)) as [E|NE]; [apply Hn1; split; [exact E| lia]|].
          pose proof (APF _ _ _ _ _ _ HIN2' (INFB _ (in_or_app F1 F2 _ (or_introl HINl))) NE) as AP. lia.
        + intros (Xne & Xr). destruct (HN Xne) as (qn & nn & HINn).
          destruct (Z.eq_dec A2 (hd_addr F2)) as [E|NE]; [apply Hn2; split; [exact E| lia]|].
          pose proof (APF _ _ _ _ _ _ HIN2' (INFB _ (in_or_app F1 F2 _ (or_intror HINn))) NE) as AP. lia.
      - intros q2 A2 n2 HIN2. destruct (BKF _ _ _ HIN2) as (K1 & _). lia. }
    (* [comment removed for export] *)
    assert (HWA : Forall (fun iv => (ATOP + 4096 <= fst iv /\ snd iv <= SP) \/ iv_in_block FB iv
                      \/ (0xa9ab0 <= fst iv /\ snd iv <= 0xa9d80) \/ (0x601ca8 <= fst iv /\ snd iv <= 0x6024d0)) W).
    { eapply Forall_impl; [| exact HW]. intros [lo' hi'] X; cbn [fst snd] in X |- *.
      destruct X as [X|[X|[X|[(Xne & X1 & X2)|(Xne & X1 & X2)]]]].
      - left. exact X.
      - right; left. unfold iv_in_block. apply Exists_exists. exists (q, A, FILE_ALLOC). split; [exact INb | unfold cb_addr, cb_size, FILE_ALLOC; cbn [fst snd]; lia].
      - right; right; right. unfold A_OFL_HEAD in X. lia.
      - right; left. destruct (HL Xne) as (ql & nl & HINl). destruct (FBn ql _ nl ltac:(subst FB; apply in_or_app; left; exact HINl)) as [Enl _].
        unfold iv_in_block. apply Exists_exists. exists (ql, last_addr 0 F1, nl).
        split; [subst FB; apply in_or_app; left; exact HINl | unfold cb_addr, cb_size; cbn [fst snd]; subst nl; unfold FILE_ALLOC; lia].
      - right; left. destruct (HN Xne) as (qn & nn & HINn). destruct (FBn qn _ nn ltac:(subst FB; apply in_or_app; right; right; exact HINn)) as [Enn _].
        unfold iv_in_block. apply Exists_exists. exists (qn, hd_addr F2, nn).
        split; [subst FB; apply in_or_app; right; right; exact HINn | unfold cb_addr, cb_size; cbn [fst snd]; subst nn; unfold FILE_ALLOC; lia]. }
    assert (HWS : Forall (stdio_ivA FB SP) W).
    { eapply Forall_impl; [| exact HWA]. intros iv [X|[X|[X|X]]]; unfold stdio_ivA; [left; exact X | right; left; exact X | right; right; left; exact X | right; right; right; left; exact X]. }
    assert (MUn : munch (W ++ []) m m4) by (rewrite app_nil_r; exact MU).
    split.
    - eapply (gs_release _ GSL L RNG s CL F1 F2 FL m m4 W SP _ q A); [exact G | exact MU | exact WM | exact HWS | exact CSP | exact NOF | | exact SR4].
      eapply (errno_cell_kept L RNG s CL FB FL m m4 W [] SP); [exact G | exact MUn | exact WM | exact HWA | apply Forall_nil].
    - eapply agrees_on_weaken; [eapply (gs_keeps _ GSL L RNG s CL FB FL m m4 W [] SP); [exact G | exact MUn | exact WM | exact HWS | exact CSP]|].
      intros a Ha. split; [exact Ha | exact I].
  Qed.
  End Sz1.
  Lemma fclose_finishA : ltac:(let t := eval cbv delta [fclose_finishA__stmt] in fclose_finishA__stmt in exact t).
  Proof using EQB GL GSL. intros L RNG s CL F1 F2 FL m m4 W0 q A SP. ltac2:(SecDiet.SzSec.closeP 'fclose_finishA__body "vvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition fclose_o_proofA__stmt : Prop := fclose_stmt_o HO GIOA TP.
  Section Sz2.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL F1 F2 FL trC f Af lo : ltac2:(SecDiet.SzSec.tyM 'fclose_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fclose_o_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'fclose_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using EQB FREE FREENULL GL GSL HAL TPFC. pin_using (fun (EQB FREE FREENULL GL GSL HAL TPFC : unit) => tt).
 intros SPO UC TPF -> NOF.
    pose proof SPO as (_ & _ & _ & _ & _ & _ & _ & SPAL & (RSTKF & _ & RIMGSH & _)).
    pose proof (spo_factsA _ _ _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & _ & ENV & LOA & LOB & SPT & TOP47 & Etp & RSTK & RIMG & RTLS & KLO & GLO).
    destruct (gs_ssp _ GSL L) as [canary SSPL]. pose proof (SSPL _ _ _ _ _ _ G) as SSP.
    destruct (TPFC _ _ _ TPF) as [TRF TRN].
    subst tp. unfold STDIO_STACK, FILE_BLOCK in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (@ATOP_lo rc) as ATL. pose proof (@ATOP_hi rc) as ATH.
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G) as BA.
    pose proof (blocks_apart_app_inv _ _ BA) as (BAc & BAf & BAX).
    pose proof (blocks_apart_app_inv _ _ BAf) as (BA1 & BA2 & BAX12). cbn [blocks_apart] in BA2. destruct BA2 as [APfF2 BA2'].
    pose proof (gs_rng0 _ GSL _ _ _ _ _ _ _ G) as R0.
    destruct (gs_libc _ GSL _ _ _ _ _ _ _ G) as [_ NL].
    (* [comment removed for export] *)
    destruct (files_R_mid eqb EQB m 0 _ F1 F2 f Af 1264 FS ND) as (fm & LK & INf & _ & A0 & Ahi & FR & INV & HPV & HNX).
    remember (last_addr 0 F1) as pv eqn:Epv. remember (hd_addr F2) as nx eqn:Enx.
    destruct FR as (flags & mode & rp & tail & bufbytes & FC & FL' & BUF & BP & WB0 & WBL & RR & RP0 & RPHI & GLN).
    pose proof FL' as (FLn & FLw & FLe & FLerr & FLsvb & FLperm).
    pose proof INV as (ICH & IFD & IBS & INN & INW & INR & IRB). rewrite ICH in FLperm.
    (* [comment removed for export] *)
    assert (BKF : forall q2 A2 n2, In (q2, A2, n2) (F1 ++ (f, Af, 1264) :: F2) ->
              n2 = 1264 /\ 0x603000 <= A2 /\ A2 + 1264 <= lo /\ rng RNG A2 1264).
    { intros q2 A2 n2 HIN. destruct (files_R_pick eqb EQB m 0 _ _ q2 A2 n2 FS ND HIN) as (f' & pv' & nx' & _ & _ & En & B0 & _).
      subst n2. unfold FILE_ALLOC in *.
      destruct (live_block_factsA L RNG s CL _ FL m q2 A2 1264 lo G ltac:(apply in_or_app; right; exact HIN) LOA ltac:(lia)) as (_ & _ & K2 & K3 & _ & _ & K6).
      split; [reflexivity|]. split; [exact K3|]. split; [exact K2 | exact K6]. }
    destruct (live_block_factsA L RNG s CL _ FL m f Af 1264 lo G ltac:(apply in_or_app; right; apply in_or_app; right; left; reflexivity) LOA ltac:(lia))
      as (_ & _ & FK2 & FK3 & FKT & SOF & RGF).
    assert (PVF : pv <> 0 -> (pv + 1264 <= Af \/ Af + 1264 <= pv) /\ pv + 1264 <= lo /\ (pv + 1264 <= 0x10000 \/ 0x603000 <= pv) /\ 0 < pv).
    { intros NE. assert (NE1 : F1 <> []) by (intros E; apply NE; rewrite Epv, E; reflexivity).
      destruct (last_addr_In 0 F1 NE1) as (ql & nl & HINl). rewrite <- Epv in HINl.
      destruct (BKF ql pv nl ltac:(apply in_or_app; left; exact HINl)) as (-> & K1 & K2 & _).
      pose proof (BAX12 _ _ HINl (or_introl eq_refl)) as AP. unfold apart, cb_addr, cb_size in AP. cbn [fst snd] in AP. lia. }
    assert (NXF : nx <> 0 -> (nx + 1264 <= Af \/ Af + 1264 <= nx) /\ nx + 1264 <= lo /\ (nx + 1264 <= 0x10000 \/ 0x603000 <= nx) /\ 0 < nx).
    { intros NE. assert (NE2 : F2 <> []) by (intros E; apply NE; rewrite Enx, E; reflexivity).
      destruct (hd_addr_In F2 NE2) as (qn & nn & HINn). rewrite <- Enx in HINn.
      destruct (BKF qn nx nn ltac:(apply in_or_app; right; right; exact HINn)) as (-> & K1 & K2 & _).
      pose proof (proj1 (Forall_forall _ _) APfF2 _ HINn) as AP. unfold apart, cb_addr, cb_size in AP. cbn [fst snd] in AP. lia. }
    assert (PN : pv <> 0 -> nx <> 0 -> pv + 1264 <= nx \/ nx + 1264 <= pv \/ pv = nx).
    { intros NE NE'. assert (NE1 : F1 <> []) by (intros E; apply NE; rewrite Epv, E; reflexivity).
      assert (NE2 : F2 <> []) by (intros E; apply NE'; rewrite Enx, E; reflexivity).
      destruct (last_addr_In 0 F1 NE1) as (ql & nl & HINl). rewrite <- Epv in HINl.
      destruct (hd_addr_In F2 NE2) as (qn & nn & HINn). rewrite <- Enx in HINn.
      destruct (BKF ql pv nl ltac:(apply in_or_app; left; exact HINl)) as (-> & _).
      destruct (BKF qn nx nn ltac:(apply in_or_app; right; right; exact HINn)) as (-> & _).
      pose proof (BAX12 _ _ HINl (or_intror HINn)) as AP. unfold apart, cb_addr, cb_size in AP. cbn [fst snd] in AP. lia. }
    assert (RPV : pv <> 0 -> rng RNG (pv + 112) 8).
    { intros NE. assert (NE1 : F1 <> []) by (intros E; apply NE; rewrite Epv, E; reflexivity).
      destruct (last_addr_In 0 F1 NE1) as (ql & nl & HINl). rewrite <- Epv in HINl.
      destruct (BKF ql pv nl ltac:(apply in_or_app; left; exact HINl)) as (_ & _ & _ & K). eapply rng_sub'; [exact K | lia]. }
    assert (RNX : nx <> 0 -> rng RNG (nx + 104) 8).
    { intros NE. assert (NE2 : F2 <> []) by (intros E; apply NE; rewrite Enx, E; reflexivity).
      destruct (hd_addr_In F2 NE2) as (qn & nn & HINn). rewrite <- Enx in HINn.
      destruct (BKF qn nx nn ltac:(apply in_or_app; right; right; exact HINn)) as (_ & _ & _ & K). eapply rng_sub'; [exact K | lia]. }
    assert (PV0 : 0 <= pv) by (destruct (Z.eq_dec pv 0) as [E|NE]; [lia| destruct (PVF NE); lia]).
    assert (PVHI : pv + 1264 < 2^63) by (destruct (Z.eq_dec pv 0) as [E|NE]; [lia| destruct (PVF NE); lia]).
    assert (NX0 : 0 <= nx) by (destruct (Z.eq_dec nx 0) as [E|NE]; [lia| destruct (NXF NE); lia]).
    assert (NXHI : nx + 1264 < 2^63) by (destruct (Z.eq_dec nx 0) as [E|NE]; [lia| destruct (NXF NE); lia]).
    assert (HDR : 0 <= hd_addr (F1 ++ (f, Af, 1264) :: F2) < 2^64).
    { destruct F1 as [|[[q1 A1] n1] F1']; cbn [hd_addr app]; [lia|].
      destruct (BKF q1 A1 n1 ltac:(left; reflexivity)) as (_ & K1 & K2 & _). lia. }
    assert (RGFp : rng RNG Af 232) by (eapply rng_sub'; [exact RGF | lia]).
    assert (RGB : rng RNG (Af + 240) 1024) by (eapply rng_sub'; [exact RGF | lia]).
    (* [comment removed for export] *)
    destruct (gs_ahm _ GSL _ _ _ _ _ _ _ G) as (T & AHM & TAL & TLO & THI & RT & TZ & TAP).
    pose proof (TAP (f, Af, 1264) ltac:(apply in_or_app; right; apply in_or_app; right; left; reflexivity)) as TAF. unfold cb_addr, cb_size in TAF. cbn [fst snd] in TAF.
    pose proof (ahm_idx_range Af) as IDX.
    set (BKT := T + 120 * ahm_idx Af).
    assert (BC : rw_cells asegs m BKT ahm_bucket0) by (apply ahm_zero_bucket; [exact TZ | exact IDX]).
    assert (RBK : rng RNG BKT 120) by (eapply rng_sub'; [exact RT | subst BKT; unfold AHM_BYTES; lia]).
    remember (Z_to_bv 64 (bv_unsigned sp + -96) : word) as spm eqn:Espm.
    assert (Hspm : bv_unsigned spm = bv_unsigned sp + -96) by (rewrite Espm; apply unsigned_lit; lia).
    remember (Z_to_bv 64 (bv_unsigned spm + -48) : word) as spf eqn:Espf.
    assert (Hspf : bv_unsigned spf = bv_unsigned spm + -48) by (rewrite Espf; apply unsigned_lit; lia).
    remember (Z_to_bv 64 (bv_unsigned spf + -80) : word) as spg eqn:Espg.
    assert (Hspg : bv_unsigned spg = bv_unsigned spf + -80) by (rewrite Espg; apply unsigned_lit; lia).
    unfold s_fclose, Stdio.fclose.
    eapply implMG_lookup_file; [exact LK|].
    unfold fclose_file. apply implMG_bind_assoc.
    (* [comment removed for export] *)
    set (Qff := fun (f1 : file_st) (s' : PS) (ms' : machine_state) => s' = s /\ tr_inv fm f1 /\
      exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mode2 : word) (jk junk : list byte) (mapw bkt idxw : word) (cr : byte) (rest : list byte) (m3 : mem),
        ms' = MS (mkR (Z_to_bv 64 0x9a220) spf gp (Z_to_bv 64 ATP) t0' t1' t2' (Z_to_bv 64 Af) (Z_to_bv 64 12297829382473034410) (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                     (Z_to_bv 64 711704) (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x9a220) fc None m3 (seg_rom asegs)
        /\ munch [(lo, bv_unsigned sp); (Af, Af + 232)] m m3 /\ wmono asegs m m3 /\ mem_inv asegs m3
        /\ stk asegs m3 lo (bv_unsigned spf)
        /\ rw_cells asegs m3 Af (fcells flags 0 0 F_STDIO_CLOSE 0 0 0 F_STDIO_READ (wfn_of f1) F_STDIO_SEEK (Af + FILE_BUF_OFF) (f_bufsize fm) pv nx (f_fd fm) mode2 (lbf_of f1) tail)
        /\ rw_cells asegs m3 (bv_unsigned spf) [CB 8 jk; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 711704); C8 (Z_to_bv 64 12297829382473034410); C8 (Z_to_bv 64 Af); C8 (Z_to_bv 64 0x49c84)]
        /\ rw_cells asegs m3 (bv_unsigned sp + -96) [CB 8 junk]
        /\ rw_cells asegs m3 (bv_unsigned sp + -88) (ahm_handle mapw bkt (Z_to_bv 64 0) Af idxw cr rest)
        /\ rw_cells asegs m3 (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    eapply implMG_bind with (Q1 := fun f1 s' RNG' ms' => RNG' = RNG /\ Qff f1 s' ms').
    { apply implAM_implMG.
      (* [comment removed for export] *)
      eapply implAM_evt.
      { unfold FCLOSE_ENTRY.
        eapply (fclose_i_pre RNG ra sp gp (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 (Z_to_bv 64 Af) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo Af T);
          first [ reflexivity | exact MI | exact ST | exact KLO | exact ENV | exact AHM | exact BC | exact TAL | exact TLO | exact RIMG | exact RSTK | exact RBK | lia ]. }
      cbv beta. intros ms0 MID. unfold fclose_i_mid in MID. fold BKT in MID.
      destruct MID as (u0 & u1 & u2 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & u3 & u4 & u5 & u6 & junk & m0 & -> & MU0b & WM0 & MI0 & ST0 & FRa0 & HC0 & FRs0 & BC0).
      assert (MU0 : munch [(bv_unsigned sp + -272, bv_unsigned sp)] m m0).
      { eapply (ahm_munch_restore _ m m0 BKT MU0b); [subst BKT; lia | subst BKT; unfold AHM_BYTES in THI; lia | exact BC | exact BC0 |].
        intros a Ha. cbn [outside] in Ha |- *. destruct (Z_lt_ge_dec a BKT) as [C1|C1]; [left; lia|]. destruct (Z_lt_ge_dec a (BKT + 8)) as [C2|C2]; [right; lia | left; lia]. }
      clear MU0b BC0.
      rewrite <- Espm. rewrite <- Hspm in ST0.
      (* [comment removed for export] *)
      assert (FC0 : rw_cells asegs m0 Af (fcells flags rp (rp + zlength (f_rbuf fm)) F_STDIO_CLOSE
                (if f_wactive fm then Af + FILE_BUF_OFF + f_bufsize fm else 0) (if f_wactive fm then Af + FILE_BUF_OFF + zlength (f_wbuf fm) else 0) (if f_wactive fm then Af + FILE_BUF_OFF else 0)
                F_STDIO_READ (wfn_of fm) F_STDIO_SEEK (Af + FILE_BUF_OFF) (f_bufsize fm) pv nx (f_fd fm) mode (lbf_of fm) tail)).
      { eapply rw_cells_transport; [exact FC | exact MU0 | exact WM0 |]. unfold fcells. rewrite file_cells_size. cbn [disjoint_from]. lia. }
      (* [comment removed for export] *)
      assert (RSTKM : rng RNG lo (bv_unsigned spm - lo)) by (eapply rng_sub'; [exact RSTK | lia]).
      eapply implAM_evt.
      { eapply (fclose_S1 RNG (Z_to_bv 64 0x49c84) spm gp (Z_to_bv 64 ATP) (Z_to_bv 64 Af) (Z_to_bv 64 12297829382473034410) (Z_to_bv 64 711704) (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 F fc Af lo);
          first [ exact ST0 | exact MI0 | exact RSTKM | exact RGFp | exact RIMG | lia ]. }
      cbv beta. intros ms1 PO1. destruct PO1 as (jk & m1 & -> & FR1 & MU1 & WM1 & MI1 & ST1).
      rewrite <- Espf. rewrite <- Hspf in ST1, FR1.
      (* [comment removed for export] *)
      assert (MU01 : munch [(lo, bv_unsigned sp)] m m1).
      { eapply munch_trans; [eapply munch_weaken; [| exact MU0] | eapply munch_weaken; [| exact MU1]]; unfold sub_fp; cbn [outside]; intros x Hx; (keep_hyps rc sp Af lo pv nx T x LOB Hx spm Hspm; lia). }
      pose proof (wmono_trans asegs _ _ _ WM0 WM1) as WM01.
      assert (IES1 : iesafe [(lo, bv_unsigned sp)]) by (apply iesafe_one_high; unfold KHIGH in KLO; lia).
      assert (ENV1 : icptenv m1) by (eapply icptenv_transport; [exact ENV | exact MU01 | exact WM01 | exact IES1]).
      assert (RSTKF1 : rng RNG lo (bv_unsigned spf - lo)) by (eapply rng_sub'; [exact RSTK | lia]).
      eapply implAM_evt.
      { unfold FFLUSH_ICPT.
        eapply (fflush_i_pre RNG) with (lo := lo); first [ exact MI1 | exact ST1 | exact KLO | exact ENV1 | exact RIMG | exact RSTKF1 | lia ]. }
      cbv beta. intros ms2 MID2. unfold fflush_i_mid in MID2.
      destruct MID2 as (v0 & v1 & v2 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & v3 & v4 & v5 & v6 & junk2 & m2 & -> & MU2 & WM2 & MI2 & ST2 & FR2).
      rewrite <- Espg. rewrite <- Hspg in ST2, FR2.
      (* [comment removed for export] *)
      assert (MU02 : munch [(lo, bv_unsigned sp)] m m2).
      { eapply munch_trans; [exact MU01 | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; intros x Hx; (keep_hyps rc sp Af lo pv nx T spm spf x LOB Hspm Hspf Hx; lia). }
      pose proof (wmono_trans asegs _ _ _ WM01 WM2) as WM02.
      assert (FC2 : rw_cells asegs m2 Af (fcells flags rp (rp + zlength (f_rbuf fm)) F_STDIO_CLOSE
                (if f_wactive fm then Af + FILE_BUF_OFF + f_bufsize fm else 0) (if f_wactive fm then Af + FILE_BUF_OFF + zlength (f_wbuf fm) else 0) (if f_wactive fm then Af + FILE_BUF_OFF else 0)
                F_STDIO_READ (wfn_of fm) F_STDIO_SEEK (Af + FILE_BUF_OFF) (f_bufsize fm) pv nx (f_fd fm) mode (lbf_of fm) tail)).
      { eapply rw_cells_transport; [exact FC | exact MU02 | exact WM02 |]. unfold fcells. rewrite file_cells_size. cbn [disjoint_from]. lia. }
      assert (BUF2 : rw_cells asegs m2 (Af + FILE_BUF_OFF) [CB (Z.to_nat (f_bufsize fm)) bufbytes]).
      { eapply rw_cells_transport; [exact BUF | exact MU02 | exact WM02 |]. rewrite IBS. unfold BUFSIZ, FILE_BUF_OFF. cbn [disjoint_from cells_size csize Nat.add]. lia. }
      assert (SSP2 : ssp_cells m2 canary).
      { destruct SSP as [GOT GUARD]. split; (eapply rw_cells_transport; [eassumption | exact MU02 | exact WM02 | unfold got_ssp, ssp_guard; cbn [disjoint_from cells_size csize Nat.add]; lia]). }
      assert (RSTKG : rng RNG lo (bv_unsigned spg - lo)) by (eapply rng_sub'; [exact RSTK | lia]).
      eapply implAM_post_evt.
      { eapply (fflush_spec (St:=PS) RNG) with (f := fm) (Fp := Af) (flags := flags) (rp := rp) (closefn := F_STDIO_CLOSE) (readfn := F_STDIO_READ)
            (B := Af + FILE_BUF_OFF) (prev := pv) (next := nx) (mode := mode) (tail := tail) (bufbytes := bufbytes) (lo := lo) (canary := canary) (sp := spg);
          first [ exact FC2 | exact FLsvb | exact BUF2 | exact BP | exact WB0 | exact WBL | (intros _; exact ICH) | exact RP0 | exact RPHI | reflexivity
                | (rewrite ICH; exact IFD) | exact ST2 | exact SSP2 | exact MI2 | exact RSTKG | exact RGFp | exact RIMG | exact R0 | exact GLO
                | (rewrite IBS; unfold BUFSIZ, FILE_BUF_OFF; first [exact RGB | (keep_hyps rc sp Af T FKT lo spg FK2; lia)])
                | (rewrite ?IBS; unfold FFLUSH_DEPTH, BUFSIZ, FILE_BUF_OFF, got_ssp, ssp_guard; (keep_hyps rc sp Af lo T spm spf spg LOB Hspm Hspf Hspg L SPT TOP47 A0 FK2 FK3; lia))
                | match goal with |- ?g => idtac "FF side:" g end ]. }
      cbv beta. intros f1 st2 ms3 (-> & TRI & PO3).
      destruct PO3 as (w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & mode2 & m3 & -> & MU3 & WM3 & MI3 & ST3 & FC3 & SSP3).
      unfold ff_W, FFLUSH_DEPTH in MU3.
      replace (ret_pc (Z_to_bv 64 0x49b0c)) with (Z_to_bv 64 0x49b0c : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
      (* [comment removed for export] *)
      assert (MU03 : munch [(lo, bv_unsigned sp); (Af, Af + 232)] m m3).
      { eapply munch_trans; [eapply munch_weaken; [| exact MU02] | eapply munch_weaken; [| exact MU3]]; unfold sub_fp; cbn [outside]; intros x Hx; (keep_hyps sp Af lo x Hx rc pv nx T spm spf spg LOB Hspm Hspf Hspg; lia). }
      pose proof (wmono_trans asegs _ _ _ WM02 WM3) as WM03.
      assert (AHM3 : rt_ahm m3 T) by (eapply rw_cells_transport; [exact AHM | exact MU03 | exact WM03 | cbn [disjoint_from cells_size csize Nat.add]; lia]).
      assert (BC3 : rw_cells asegs m3 BKT ahm_bucket0).
      { eapply rw_cells_transport; [exact BC | exact MU03 | exact WM03 |]. unfold ahm_bucket0. cbn [disjoint_from cells_size csize Nat.add]. subst BKT. unfold AHM_BYTES in *. (keep_hyps rc sp Af lo pv nx T LOA THI TAF IDX; lia). }
      assert (FR3 : rw_cells asegs m3 (bv_unsigned spg) [CB 56 junk2; C8 (Z_to_bv 64 12297829382473034410); C8 (Z_to_bv 64 Af); C8 (Z_to_bv 64 0x9a220)]).
      { eapply rw_cells_transport; [exact FR2 | exact MU3 | exact WM3 |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
      rewrite Hspg in ST3, FR3. rewrite Espg.
      eapply evtF_mono.
      { eapply (fflush_i_post RNG) with (sp := spf) (lo := lo) (fp := Af) (TABLE := T) (m := m3);
          first [ exact MI3 | exact ST3 | exact FR3 | exact AHM3 | exact BC3 | exact TAL | exact TLO | exact GLO | exact RIMG | exact RSTKF1 | exact RBK | lia
                | match goal with |- ?g => idtac "FFPOST side:" g end ]. }
      cbv beta. intros ms4 PO4. unfold fflush_i_post_post in PO4. fold BKT in PO4.
      destruct PO4 as (z0 & z1 & z2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & z3 & z4 & z5 & z6 & m4 & -> & MU4b & WM4 & MI4 & ST4 & BC4).
      assert (MU4 : munch [(bv_unsigned spf + -256, bv_unsigned spf)] m3 m4).
      { eapply (ahm_munch_restore _ m3 m4 BKT MU4b); [subst BKT; lia | subst BKT; unfold AHM_BYTES in THI; lia | exact BC3 | exact BC4 |].
        intros a Ha. cbn [outside] in Ha |- *. destruct (Z_lt_ge_dec a BKT) as [C1|C1]; [left; lia|]. destruct (Z_lt_ge_dec a (BKT + 8)) as [C2|C2]; [right; lia | left; lia]. }
      clear MU4b.
      replace (ret_pc (Z_to_bv 64 0x9a220)) with (Z_to_bv 64 0x9a220 : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
      (* [comment removed for export] *)
      assert (MU04 : munch [(lo, bv_unsigned spm); (Af, Af + 232)] m0 m4).
      { eapply munch_trans; [eapply munch_weaken; [| exact MU1] |].
        2:{ eapply munch_trans; [eapply munch_weaken; [| exact MU2] |].
            2:{ eapply munch_trans; [eapply munch_weaken; [| exact MU3] | eapply munch_weaken; [| exact MU4]]; unfold sub_fp; cbn [outside]; intros x Hx; (keep_hyps rc sp Af lo pv nx T spm spf spg x LOB Hspm Hspf Hspg Hx; lia). }
            unfold sub_fp; cbn [outside]; intros x Hx; (keep_hyps rc sp Af lo pv nx T spm spf x LOB Hspm Hspf Hx; lia). }
        unfold sub_fp; cbn [outside]; intros x Hx; lia. }
      pose proof (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 (wmono_trans asegs _ _ _ WM3 WM4))) as WM04.
      split; [reflexivity|]. split; [exact TRI|].
      exists z0, z1, z2, e1, e2, e3, e4, e5, e6, e7, z3, z4, z5, z6, mode2, jk, junk.
      eexists _, _, _, _, _, m4.
      split; [reflexivity|].
      split. { eapply munch_trans; [exact MU03 | eapply munch_weaken; [| exact MU4]]; unfold sub_fp; cbn [outside]; intros x Hx; (keep_hyps rc sp Af lo pv nx T spm spf x LOB Hspm Hspf Hx; lia). }
      split; [exact (wmono_trans asegs _ _ _ WM03 WM4)|]. split; [exact MI4|]. split; [exact ST4|].
      split. { eapply rw_cells_transport; [exact FC3 | exact MU4 | exact WM4 |]. unfold fcells. rewrite file_cells_size. cbn [disjoint_from]. lia. }
      split. { eapply (rw_cells_transport asegs [(lo, bv_unsigned spf); (Af, Af + 232)] m1 m4); [exact FR1 | | | cbn [disjoint_from cells_size csize Nat.add]; lia].
               - eapply munch_trans; [eapply munch_weaken; [| exact MU2] |].
                 2:{ eapply munch_trans; [eapply munch_weaken; [| exact MU3] | eapply munch_weaken; [| exact MU4]]; unfold sub_fp; cbn [outside]; intros x Hx; (keep_hyps rc sp Af lo pv nx T spm spf spg x LOB Hspm Hspf Hspg Hx; lia). }
                 unfold sub_fp; cbn [outside]; intros x Hx; (keep_hyps rc sp Af lo pv nx T spm spf x LOB Hspm Hspf Hx; lia).
               - exact (wmono_trans asegs _ _ _ WM2 (wmono_trans asegs _ _ _ WM3 WM4)). }
      split; [eapply rw_cells_transport; [exact FRa0 | exact MU04 | exact WM04 | cbn [disjoint_from cells_size csize Nat.add]; lia]|].
      split; [eapply rw_cells_transport; [exact HC0 | exact MU04 | exact WM04 | unfold ahm_handle; cbn [disjoint_from cells_size csize Nat.add]; lia]|].
      eapply rw_cells_transport; [exact FRs0 | exact MU04 | exact WM04 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    cbv beta. intros f1 s' RNG' ms' [-> QF]. unfold Qff in QF. clear Qff. destruct QF as (-> & TRI & QF).
    destruct QF as (z0 & z1 & z2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & z3 & z4 & z5 & z6 & mode2 & jk & junk & mapw & bkt & idxw & cr & rest & m4 & -> & MU4 & WM4 & MI4 & ST4 & FC4 & FR4 & FRa4 & HC4 & FRs4).
    pose proof TRI as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & _).
    assert (RSTKM : rng RNG lo (bv_unsigned spm - lo)) by (eapply rng_sub'; [exact RSTK | lia]).
    assert (RSTKF1 : rng RNG lo (bv_unsigned spf - lo)) by (eapply rng_sub'; [exact RSTK | lia]).
    (* [comment removed for export] *)
    eapply implMG_bind with (Q1 := fun (_ : unit) s' RNG' ms' => RNG' = RNG /\
              stdio_close_post (Z_to_bv 64 0x9a248) spf gp (Z_to_bv 64 ATP) (Z_to_bv 64 Af) (Z_to_bv 64 0) (Z_to_bv 64 711704) (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 F fc s lo m4 tt s' ms').
    { apply implAM_implMG. eapply implAM_evt.
      { rewrite Espf. eapply (fclose_S2 RNG) with (sp := spm) (Fp := Af) (lo := lo);
          first [ exact FC4 | exact MI4 | exact RSTKM | exact RGFp | exact RIMG | lia | match goal with |- ?g => idtac "S2 side:" g end ]. }
      cbv beta. intros ms5 ->. rewrite <- Espf. rewrite T1.
      eapply (stdio_close_spec (St:=PS) RNG) with (fd := f_fd fm) (lo := lo) (Fp := Af);
        first [ (unfold fcells in FC4; exact FC4) | reflexivity | exact IFD | exact ST4 | exact MI4 | exact RSTKF1 | exact RGFp | exact RIMG | exact GLO | lia
              | match goal with |- ?g => idtac "CL side:" g end ]. }
    cbv beta. intros [] s' RNG' ms' [-> (-> & PO5)].
    destruct PO5 as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m5 & -> & MU5 & WM5 & MI5 & ST5).
    replace (ret_pc (Z_to_bv 64 0x9a248)) with (Z_to_bv 64 0x9a248 : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    apply implMG_upd_lc.
    (* [comment removed for export] *)
    assert (MU05 : munch [(lo, bv_unsigned sp); (Af, Af + 232)] m m5).
    { eapply munch_trans; [exact MU4 | eapply munch_weaken; [| exact MU5]]; unfold sub_fp; cbn [outside]; intros x Hx; (keep_hyps rc sp Af lo pv nx T spm spf x LOB Hspm Hspf Hx; lia). }
    pose proof (wmono_trans asegs _ _ _ WM4 WM5) as WM05.
    assert (FC5 : rw_cells asegs m5 Af (fclose_cells flags F_STDIO_CLOSE F_STDIO_READ (wfn_of f1) F_STDIO_SEEK (Af + FILE_BUF_OFF) (f_bufsize fm) pv nx (f_fd fm) mode2 (lbf_of f1) tail)).
    { apply fclose_cells_recast; [| exact GLN]. unfold fcells in FC4. eapply rw_cells_transport; [exact FC4 | exact MU5 | exact WM5 | rewrite file_cells_size; cbn [disjoint_from]; lia]. }
    assert (NL5 : rw_cells asegs m5 NEED_LOCKS [C1 (Z_to_bv 8 0)]) by (unfold NEED_LOCKS; eapply rw_cells_transport; [exact NL | exact MU05 | exact WM05 | cbn [disjoint_from cells_size csize Nat.add]; lia]).
    assert (OL5 : rw_cells asegs m5 A_OFL_LOCK [C4 (Z_to_bv 64 0)]) by (unfold A_OFL_LOCK in *; eapply rw_cells_transport; [exact OL | exact MU05 | exact WM05 | cbn [disjoint_from cells_size csize Nat.add]; lia]).
    assert (OH5 : rw_cells asegs m5 A_OFL_HEAD [C8 (Z_to_bv 64 (hd_addr (F1 ++ (f, Af, 1264) :: F2)))]) by (unfold A_OFL_HEAD in *; eapply rw_cells_transport; [exact OH | exact MU05 | exact WM05 | cbn [disjoint_from cells_size csize Nat.add]; lia]).
    assert (KEEP5 : forall A cs, rw_cells asegs m4 A cs -> bv_unsigned spf <= A -> rw_cells asegs m5 A cs).
    { intros A cs HC HA. eapply rw_cells_transport; [exact HC | exact MU5 | exact WM5 |]. cbn [disjoint_from]. pose proof (rw_cells_bound _ _ _ _ HC). lia. }
    pose proof (KEEP5 _ _ FR4 ltac:(lia)) as FR5. pose proof (KEEP5 _ _ FRa4 ltac:(lia)) as FRa5. pose proof (KEEP5 _ _ HC4 ltac:(lia)) as HC5. pose proof (KEEP5 _ _ FRs4 ltac:(lia)) as FRs5.
    assert (PVC5 : pv <> 0 -> rw_cells asegs m5 (pv + 112) [C8 (Z_to_bv 64 Af)]).
    { intros NE. destruct (PVF NE) as (P1 & P2 & P3 & P4). destruct (HPV ltac:(intros E; apply NE; rewrite Epv, E; reflexivity)) as [PC _].
      eapply rw_cells_transport; [exact PC | exact MU05 | exact WM05 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    assert (NXC5 : nx <> 0 -> rw_cells asegs m5 (nx + 104) [C8 (Z_to_bv 64 Af)]).
    { intros NE. destruct (NXF NE) as (N1 & N2 & N3 & N4). destruct (HNX ltac:(intros E; apply NE; rewrite Enx, E; reflexivity)) as [NC _].
      eapply rw_cells_transport; [exact NC | exact MU05 | exact WM05 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    (* [comment removed for export] *)
    rewrite Espf. rewrite Hspf in ST5, FR5.
    apply implMG_from_evtF.
    eapply evtF_cut.
      { eapply (fclose_S3a RNG) with (sp := spm) (Fp := Af) (lo := lo);
          first [ exact FC5 | exact FLperm | exact NL5 | exact ST5 | exact MI5 | exact RSTKM | exact RGFp | exact RIMG | exact GLO | lia
                | match goal with |- ?g => idtac "S3a side:" g end ]. }
      cbv beta. intros ms6 PO6. destruct PO6 as (x1' & a1' & a2' & a3' & m6 & -> & MU6 & WM6 & MI6 & ST6).
      assert (MU6' : munch (fcW spm pv nx) m5 m6).
      { eapply munch_weaken; [| exact MU6]. unfold sub_fp, fcW. cbn [outside]. intros x (O1 & _). split; [exact O1 | exact I]. }
      assert (FC6 : rw_cells asegs m6 Af (fclose_cells flags F_STDIO_CLOSE F_STDIO_READ (wfn_of f1) F_STDIO_SEEK (Af + FILE_BUF_OFF) (f_bufsize fm) pv nx (f_fd fm) mode2 (lbf_of f1) tail)).
      { eapply rw_cells_transport; [exact FC5 | exact MU6 | exact WM6 | unfold fclose_cells; cbn [disjoint_from cells_size csize Nat.add]; lia]. }
      assert (OH6 : rw_cells asegs m6 A_OFL_HEAD [C8 (Z_to_bv 64 (hd_addr (F1 ++ (f, Af, 1264) :: F2)))]) by (unfold A_OFL_HEAD in *; eapply rw_cells_transport; [exact OH5 | exact MU6 | exact WM6 | cbn [disjoint_from cells_size csize Nat.add]; lia]).
      assert (PVC6 : pv <> 0 -> rw_cells asegs m6 (pv + 112) [C8 (Z_to_bv 64 Af)]).
      { intros NE. destruct (PVF NE) as (P1 & P2 & P3 & P4). eapply rw_cells_transport; [exact (PVC5 NE) | exact MU6 | exact WM6 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
      assert (NXC6 : nx <> 0 -> rw_cells asegs m6 (nx + 104) [C8 (Z_to_bv 64 Af)]).
      { intros NE. destruct (NXF NE) as (N1 & N2 & N3 & N4). eapply rw_cells_transport; [exact (NXC5 NE) | exact MU6 | exact WM6 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
      eapply evtF_cut.
      { eapply (fclose_S3b RNG) with (sp := spm) (Fp := Af) (lo := lo) (pv := pv) (nx := nx) (m0 := m5);
          first [ exact FC6 | exact PVC6 | exact NXC6 | exact OH6 | exact ST6 | exact MU6' | exact WM6 | exact MI6
                | exact PV0 | exact PVHI | exact PVF | exact NXF | exact PN | exact RPV | exact RSTKM | exact RGFp | exact RIMG | lia
                | match goal with |- ?g => idtac "S3b side:" g end ]. }
      cbv beta. intros ms7 PO7. destruct PO7 as (m7 & -> & FC7 & PVC7 & NXC7 & OH7 & ST7 & MU7 & WM7 & MI7).
      eapply evtF_cut.
      { eapply (fclose_S3c RNG) with (sp := spm) (Fp := Af) (lo := lo) (pv := pv) (nx := nx) (m0 := m5);
          first [ exact FC7 | exact PVC7 | exact NXC7 | exact OH7 | exact ST7 | exact MU7 | exact WM7 | exact MI7
                | exact NX0 | exact NXHI | exact PVF | exact NXF | exact PN | exact RNX | exact RSTKM | exact RGFp | exact RIMG | lia
                | match goal with |- ?g => idtac "S3c side:" g end ]. }
      cbv beta. intros ms8 PO8. destruct PO8 as (a1'' & m8 & -> & FC8 & PVC8 & NXC8 & OH8 & ST8 & MU8 & WM8 & MI8).
      eapply evtF_cut.
      { eapply (fclose_S3d RNG) with (sp := spm) (Fp := Af) (lo := lo) (pv := pv) (nx := nx) (m0 := m5);
          first [ exact FC8 | exact PVC8 | exact NXC8 | exact OH8 | exact HDR | exact ST8 | exact MU8 | exact WM8 | exact MI8
                | exact PVHI | exact NXHI | exact PVF | exact NXF | exact PN | exact RSTKM | exact RGFp | exact RIMG | lia
                | match goal with |- ?g => idtac "S3d side:" g end ]. }
      cbv beta. intros ms9 PO9. destruct PO9 as (a0'' & m9 & -> & FC9 & PVC9 & NXC9 & OH9 & ST9 & MU9 & WM9 & MI9).
      unfold fcW in MU9.
      assert (OL9 : rw_cells asegs m9 A_OFL_LOCK [C4 (Z_to_bv 64 0)]).
      { eapply rw_cells_transport; [exact OL5 | exact MU9 | exact WM9 |]. cbn [disjoint_from cells_size csize Nat.add]. unfold A_OFL_LOCK, A_OFL_HEAD.
        destruct (Z.eqb_spec pv 0) as [E|NE]; [| destruct (PVF NE) as (P1 & P2 & P3 & P4)];
        destruct (Z.eqb_spec nx 0) as [E'|NE']; try destruct (NXF NE') as (N1 & N2 & N3 & N4); (keep_hyps rc sp Af lo pv nx T spm LOA LOB Hspm E E' N3 P3; lia). }
      eapply evtF_cut.
      { eapply (fclose_S3e RNG) with (sp := spm) (Fp := Af) (lo := lo);
          first [ exact FC9 | exact OL9 | exact MI9 | exact RSTKM | exact RGFp | exact RIMG | exact GLO | lia
                | match goal with |- ?g => idtac "S3e side:" g end ]. }
      cbv beta. intros ms10 PO10. destruct PO10 as (b1 & b2 & b3 & b4 & b5 & ->). apply evtF_done.
    (* [comment removed for export] *)
    assert (MUT : munch [(lo, bv_unsigned sp); (Af, Af + 232); (bv_unsigned spm - 64, bv_unsigned spm - 48);
                         (pv + 112, pv + (if pv =? 0 then 112 else 120)); (nx + 104, nx + (if nx =? 0 then 104 else 112));
                         (A_OFL_HEAD, A_OFL_HEAD + 8)] m m9).
    { apply (munch_trans _ m m5 m9); [eapply munch_weaken; [| exact MU05] | eapply munch_weaken; [| exact MU9]];
        unfold sub_fp; cbn [outside]; intros x Hx; destruct (pv =? 0); destruct (nx =? 0); (keep_hyps rc sp Af lo pv nx T spm x Hx; lia). }
    pose proof (wmono_trans asegs _ _ _ WM05 WM9) as WMT.
    assert (NE1 : F1 <> [] -> pv <> 0).
    { intros NE E. destruct (last_addr_In 0 F1 NE) as (ql & nl & HINl). rewrite <- Epv, E in HINl.
      destruct (BKF ql 0 nl ltac:(apply in_or_app; left; exact HINl)) as (_ & K1 & _). lia. }
    assert (NE2 : F2 <> [] -> nx <> 0).
    { intros NE E. destruct (hd_addr_In F2 NE) as (qn & nn & HINn). rewrite <- Enx, E in HINn.
      destruct (BKF qn 0 nn ltac:(apply in_or_app; right; right; exact HINn)) as (_ & K1 & _). lia. }
    assert (OH9' : rw_cells asegs m9 A_OFL_HEAD [C8 (Z_to_bv 64 (hd_addr (F1 ++ F2)))]).
    { destruct F1 as [|[[q1 A1] n1] F1']; cbn [hd_addr app] in OH9 |- *.
      - rewrite Z.eqb_refl in OH9. rewrite <- Enx. exact OH9.
      - replace (A1 =? Af) with false in OH9; [exact OH9|]. symmetry. apply Z.eqb_neq.
        pose proof (BAX12 (q1, A1, n1) (f, Af, 1264) ltac:(left; reflexivity) ltac:(left; reflexivity)) as AP.
        destruct (BKF q1 A1 n1 ltac:(left; reflexivity)) as (-> & _).
        unfold apart, cb_addr, cb_size in AP. cbn [fst snd] in AP. (keep_hyps rc sp Af lo A1 pv nx T AP; lia). }
    assert (LP9 : F1 <> [] -> rw_cells asegs m9 (last_addr 0 F1 + 112) [C8 (Z_to_bv 64 (hd_addr F2))]).
    { intros NE. rewrite <- Epv, <- Enx. exact (PVC9 (NE1 NE)). }
    assert (LN9 : F2 <> [] -> rw_cells asegs m9 (hd_addr F2 + 104) [C8 (Z_to_bv 64 (last_addr 0 F1))]).
    { intros NE. rewrite <- Epv, <- Enx. exact (NXC9 (NE2 NE)). }
    assert (HWT : Forall (fun iv : Z * Z => snd iv <= fst iv \/ (ATOP + 4096 <= fst iv /\ snd iv <= bv_unsigned sp) \/ (Af <= fst iv /\ snd iv <= Af + 1264)
                            \/ (fst iv = A_OFL_HEAD /\ snd iv = A_OFL_HEAD + 8)
                            \/ (F1 <> [] /\ fst iv = last_addr 0 F1 + 112 /\ snd iv = last_addr 0 F1 + 120)
                            \/ (F2 <> [] /\ fst iv = hd_addr F2 + 104 /\ snd iv = hd_addr F2 + 112))
              [(lo, bv_unsigned sp); (Af, Af + 232); (bv_unsigned spm - 64, bv_unsigned spm - 48);
               (pv + 112, pv + (if pv =? 0 then 112 else 120)); (nx + 104, nx + (if nx =? 0 then 104 else 112)); (A_OFL_HEAD, A_OFL_HEAD + 8)]).
    { apply Forall_cons; [cbn [fst snd]; right; left; lia|].
      apply Forall_cons; [cbn [fst snd]; right; right; left; lia|].
      apply Forall_cons; [cbn [fst snd]; right; left; lia|].
      apply Forall_cons.
      { cbn [fst snd]. destruct (Z.eqb_spec pv 0) as [E|NE]; [left; lia|]. right; right; right; right; left.
        split; [intros EF; apply NE; rewrite Epv, EF; reflexivity|]. rewrite <- Epv. split; reflexivity. }
      apply Forall_cons.
      { cbn [fst snd]. destruct (Z.eqb_spec nx 0) as [E|NE]; [left; lia|]. right; right; right; right; right.
        split; [intros EF; apply NE; rewrite Enx, EF; reflexivity|]. rewrite <- Enx. split; reflexivity. }
      apply Forall_cons; [cbn [fst snd]; right; right; right; left; split; reflexivity | apply Forall_nil]. }
    destruct (fclose_finishA L RNG s CL F1 F2 FL m m9 _ f Af (bv_unsigned sp) G NOF MUT WMT HWT ltac:(lia) OL9 OH9' LP9 LN9) as [G9 AG9].
    (* [comment removed for export] *)
    assert (KEEP9 : forall A cs, rw_cells asegs m5 A cs -> bv_unsigned spm + -48 <= A -> rw_cells asegs m9 A cs).
    { intros A cs HC HA. eapply rw_cells_transport; [exact HC | exact MU9 | exact WM9 |]. pose proof (rw_cells_bound _ _ _ _ HC) as HB.
      cbn [disjoint_from]. unfold A_OFL_HEAD.
      destruct (Z.eqb_spec pv 0) as [E|NE]; [| destruct (PVF NE) as (P1 & P2 & P3 & P4)];
      destruct (Z.eqb_spec nx 0) as [E'|NE']; try destruct (NXF NE') as (N1 & N2 & N3 & N4); lia. }
    pose proof (KEEP9 _ _ FR5 ltac:(lia)) as FR9. pose proof (KEEP9 _ _ FRa5 ltac:(lia)) as FRa9. pose proof (KEEP9 _ _ HC5 ltac:(lia)) as HC9. pose proof (KEEP9 _ _ FRs5 ltac:(lia)) as FRs9.
    (* [comment removed for export] *)
    assert (EAF : bv_unsigned (Z_to_bv 64 Af : word) = Af) by (apply unsigned_lit; lia).
    rewrite <- Espf. rewrite <- Hspf in ST9, FR9.
    assert (SPOF : forall mm (sx : PS) CLx, GIOA L RNG sx CLx (F1 ++ F2) FL mm -> stk asegs mm lo (bv_unsigned spf) -> mem_inv asegs mm ->
              std_pre_o GIOA L RNG spf (Z_to_bv 64 ATP) sx CLx (F1 ++ F2) FL lo FREE_STACK mm).
    { intros mm sx CLx Gx STx MIx. split; [exact Gx|]. split; [exact STx|]. split; [exact LOA|]. split; [unfold FREE_STACK; lia|].
      split; [split; [lia | exact TOP47]|]. split; [exact MIx|]. split; [reflexivity|].
      split; [rewrite Hspf, Hspm; clear - SPAL; Z.div_mod_to_equations; lia|].
      split; [exact RSTKF|]. split; [exact RIMG|]. split; [exact RIMGSH | exact RTLS]. }
    assert (UNWF : forall mm X, In [AFREE_PC; X] (al_U L) -> 4096 <= X < 2^64 -> X <> AFREE_PC -> unw_okA L RNG mm lo AFREE_PC spf (Z_to_bv 64 Af) (Z_to_bv 64 X)).
    { intros mm X HIN HX NX. assert (EX : bv_unsigned (Z_to_bv 64 X : word) = X) by (apply unsigned_lit; lia).
      unfold unw_okA, aunw. rewrite EAF, EX. split; [| (keep_hyps rc sp Af lo pv nx T spm spf X LOA LOB FKT Hspm Hspf HX NX; lia)].
      exists []. left. split; [lia|]. split; [apply uc_stop; intros (Y & _); lia|]. split; [cbn [length]; lia|]. split; [exact HIN | exact RSTKF]. }
    eapply implMG_evtF.
    { unfold FREE_ENTRY'.
      eapply (FREENULL (Z_to_bv 64 0x9a2a4) spf gp (Z_to_bv 64 ATP)) with (L := L) (CL := (f, Af, FILE_ALLOC) :: CL) (FB := F1 ++ F2) (FL := FL) (lo := lo);
        [ apply SPOF; [exact G9 | exact ST9 | exact MI9] | reflexivity | apply UNWF; [exact TRN | lia | unfold AFREE_PC; lia] ]. }
    cbv beta. intros ms11 PO11. destruct PO11 as (a0v & m10 & REGS & MI10 & ST10 & AG10 & G10).
    unfold hpost_regs in REGS. destruct REGS as (g0 & g1 & g2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & g3 & g4 & g5 & g6 & ->).
    replace (ret_pc (Z_to_bv 64 0x9a2a4)) with (Z_to_bv 64 0x9a2a4 : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    (* [comment removed for export] *)
    eapply implMG_evtF.
    { rewrite Espf. eapply (fclose_S3f RNG) with (sp := spm) (Fp := Af) (lo := lo);
        first [ exact MI10 | exact RSTKM | exact RGFp | exact RIMG | lia | match goal with |- ?g => idtac "S3f side:" g end ]. }
    cbv beta. intros ms12 ->. rewrite <- Espf.
    eapply implMG_post_evtF.
    { unfold FREE_ENTRY'.
      eapply (FREE (Z_to_bv 64 FCLOSE_FREE_RA) spf gp (Z_to_bv 64 ATP)) with (L := L) (C1 := []) (C2 := CL) (FB := F1 ++ F2) (FL := FL) (q := f) (A := Af) (n := FILE_ALLOC) (lo := lo);
        [ apply SPOF; [exact G10 | exact ST10 | exact MI10] | reflexivity | apply UNWF; [exact TRF | unfold FCLOSE_FREE_RA; lia | unfold FCLOSE_FREE_RA, AFREE_PC; lia] ]. }
    cbv beta. intros [] sF RNG11 ms13 (FP11 & a0v' & m11 & REGS & OF11 & MI11 & ST11 & AG11 & G11).
    unfold hpost_regs in REGS. destruct REGS as (k0 & k1 & k2 & l1 & l2 & l3 & l4 & l5 & l6 & l7 & k3 & k4 & k5 & k6 & ->).
    replace (ret_pc (Z_to_bv 64 FCLOSE_FREE_RA)) with (Z_to_bv 64 FCLOSE_FREE_RA : word) by (unfold FCLOSE_FREE_RA; symmetry; apply ret_pc_even; [lia | reflexivity]).
    cbn [app] in AG11, G11.
    (* [comment removed for export] *)
    assert (KEEP11 : forall A cs, rw_cells asegs m9 A cs -> bv_unsigned spf <= A -> rw_cells asegs m11 A cs).
    { intros A cs HC HA. eapply keeps_rw_cells_stack; [exact AG11 | eapply keeps_rw_cells_stack; [exact AG10 | exact HC | exact HA] | exact HA]. }
    pose proof (KEEP11 _ _ FR9 ltac:(lia)) as FR11. pose proof (KEEP11 _ _ FRa9 ltac:(lia)) as FRa11. pose proof (KEEP11 _ _ HC9 ltac:(lia)) as HC11. pose proof (KEEP11 _ _ FRs9 ltac:(lia)) as FRs11.
    assert (RSTK11 : rng RNG11 lo (bv_unsigned sp - lo)) by (eapply rng_fp_le; [exact FP11 | exact RSTK]).
    assert (RSTKM11 : rng RNG11 lo (bv_unsigned spm - lo)) by (eapply rng_sub'; [exact RSTK11 | lia]).
    assert (RGFp11 : rng RNG11 Af 232) by (eapply rng_fp_le; [exact FP11 | exact RGFp]).
    assert (RIMG11 : rng_aimg RNG11) by (eapply rng_fp_le; [exact FP11 | exact RIMG]).
    rewrite Hspf in ST11, FR11. rewrite Espf.
    eapply evtF_cut.
    { eapply (fclose_S4 RNG11 (Z_to_bv 64 0x49c84) spm gp (Z_to_bv 64 ATP) (Z_to_bv 64 Af) (Z_to_bv 64 12297829382473034410) (Z_to_bv 64 711704) (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 F fc Af lo);
        first [ exact FR11 | exact ST11 | exact MI11 | exact RSTKM11 | exact RGFp11 | exact RIMG11 | lia | match goal with |- ?g => idtac "S4 side:" g end ]. }
    cbv beta. intros ms14 [-> ST14].
    replace (ret_pc (Z_to_bv 64 0x49c84)) with (Z_to_bv 64 0x49c84 : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    rewrite Hspm in ST14. rewrite Espm.
    eapply evtF_mono.
    { eapply (fclose_i_post RNG11) with (lo := lo) (fp := Af) (m := m11);
        first [ exact MI11 | exact ST14 | exact FRa11 | exact HC11 | exact FRs11 | (eapply rng_sub'; [exact RSTK11 | lia]) | lia
              | match goal with |- ?g => idtac "IPOST side:" g end ]. }
    cbv beta. intros ms15 [-> ST15].
    split; [exact FP11|].
    eexists _, m11. split; [unfold hpost_regs; repeat eexists; reflexivity|].
    split; [destruct s as [xh xl xo xt]; cbn [ps_outfile set_libc] in OF11 |- *; exact OF11|].
    split; [exact MI11|]. split; [exact ST15|].
    split; [| exact G11].
    eapply agrees_on_trans; [exact AG9|]. eapply agrees_on_trans.
    - eapply client_keeps_weaken; [exact AG10 | lia | intros a Ha; apply in_block_cons; exact Ha | apply incl_refl].
    - eapply client_keeps_weaken; [exact AG11 | lia | intros a Ha; exact Ha | apply incl_refl].
  Qed.
  End Sz2.
  Theorem fclose_o_proofA : ltac:(let t := eval cbv delta [fclose_o_proofA__stmt] in fclose_o_proofA__stmt in exact t).
  Proof using EQB FREE FREENULL GL GSL HAL TPFC. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL F1 F2 FL trC f Af lo. ltac2:(SecDiet.SzSec.closeP 'fclose_o_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End GlueFc.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_lock.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdio_cs.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_read__A3S.F_stdio_read.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_toread.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fflush.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fclose.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_ahm.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fflush.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fclose.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_fcKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioLawsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_foKitA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section GlueFc.
  Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GSL : gia_stdio_laws GIOA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  #[local] Abbreviation eqb := (ho_eqb HO).
  (* [comment removed for export] *)
  Hypothesis FREE : free_stmt_o HO GIOA.
  Hypothesis FREENULL : free_null_stmt_o GIOA.
  Hypothesis TPFC : forall L ra trC, tp_fclose TP L ra trC -> In [AFREE_PC; 0x9a690] (al_U L) /\ In [AFREE_PC; 0x9a688] (al_U L).

  (* [comment removed for export] *)
  #[local] Notation spo_factsA := (A3S.Stdio_glueA.TwB.spo_factsA GIOA GSL).
  #[local] Notation errno_cell_kept := (A3S.Stdio_glueA.TwB.errno_cell_kept FO GIOA fflagA GL GSL).
  #[local] Notation block_rangeA := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_foKitA.TwB.block_rangeA FO GIOA fflagA GL).
  #[local] Notation live_block_factsA := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_foKitA.TwB.live_block_factsA FO GIOA fflagA GL).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition fclose_finishA__stmt : Prop := forall L RNG (s : PS) (CL F1 F2 : list cblk) FL m m4 W0 q A SP,
    GIOA L RNG s CL (F1 ++ (q, A, FILE_ALLOC) :: F2) FL m ->
    ps_outfile s <> Some q ->
    munch W0 m m4 -> wmono asegs m m4 ->
    Forall (fun iv : Z * Z => snd iv <= fst iv \/ (ATOP + 4096 <= fst iv /\ snd iv <= SP) \/ (A <= fst iv /\ snd iv <= A + 1264)
                              \/ (fst iv = A_OFL_HEAD /\ snd iv = A_OFL_HEAD + 8)
                              \/ (F1 <> [] /\ fst iv = last_addr 0 F1 + 112 /\ snd iv = last_addr 0 F1 + 120)
                              \/ (F2 <> [] /\ fst iv = hd_addr F2 + 104 /\ snd iv = hd_addr F2 + 112)) W0 ->
    ATOP + 4096 <= SP ->
    rw_cells asegs m4 A_OFL_LOCK [C4 (Z_to_bv 64 0)] -> rw_cells asegs m4 A_OFL_HEAD [C8 (Z_to_bv 64 (hd_addr (F1 ++ F2)))] ->
    (F1 <> [] -> rw_cells asegs m4 (last_addr 0 F1 + 112) [C8 (Z_to_bv 64 (hd_addr F2))]) ->
    (F2 <> [] -> rw_cells asegs m4 (hd_addr F2 + 104) [C8 (Z_to_bv 64 (last_addr 0 F1))]) ->
    GIOA L RNG (set_libc (set_files (files_remove eqb (lc_files (ps_libc s)) q) (ps_libc s)) s) ((q, A, FILE_ALLOC) :: CL) (F1 ++ F2) FL m4
    /\ agrees_on (client_keeps FL CL SP) m m4.
  Section Sz1.
  Variables L RNG s CL F1 F2 FL m m4 W0 q A SP : ltac2:(SecDiet.SzSec.tyM 'fclose_finishA__stmt "vvvvvvvvvvvvv" @L).
  Lemma fclose_finishA__body : ltac2:(SecDiet.SzSec.bodyP 'fclose_finishA__stmt "vvvvvvvvvvvvv").
  Proof using EQB GL GSL. pin_using (fun (EQB GL GSL : unit) => tt).
    intros G NOF MU0 WM HW0 CSP OL4 OH4 LP4 LN4.
    pose proof (munch_drop_empty _ _ _ MU0) as MU. pose proof (Forall_drop_empty _ _ HW0) as HW. cbv beta in HW.
    remember (@List.filter (Z * Z)%type (fun iv : Z * Z => fst iv <? snd iv) W0) as W eqn:EW. clear EW MU0 HW0.
    pose proof (gs_stdio _ GSL _ _ _ _ _ _ _ G) as SR.
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    pose proof (@ATOP_lo rc) as ATL.
    pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G) as BA.
    set (FB := F1 ++ (q, A, FILE_ALLOC) :: F2) in *.
    assert (INb : In (q, A, FILE_ALLOC) FB) by (subst FB; apply in_or_app; right; left; reflexivity).
    assert (INFB : forall b, In b (F1 ++ F2) -> In b FB).
    { intros b Hb. subst FB. apply in_app_or in Hb. apply in_or_app. destruct Hb as [X|X]; [left; exact X| right; right; exact X]. }
    pose proof (blocks_apart_app_inv _ _ BA) as (BAc & BAf & BAX).
    (* [comment removed for export] *)
    assert (FBn : forall q2 A2 n2, In (q2, A2, n2) FB -> n2 = FILE_ALLOC /\ 0 < A2).
    { intros q2 A2 n2 HIN. destruct (files_R_pick eqb EQB m 0 _ FB q2 A2 n2 FS ND HIN) as (f & pv & nx & _ & _ & En & B0 & _). split; [exact En| exact B0]. }
    assert (BKF : forall q2 A2 n2, In (q2, A2, n2) FB -> 0x604000 <= A2 /\ A2 + 1264 <= ATOP).
    { intros q2 A2 n2 HIN. destruct (FBn _ _ _ HIN) as [-> B0].
      pose proof (block_rangeA _ _ _ _ _ _ _ (q2, A2, FILE_ALLOC) G ltac:(apply in_or_app; right; exact HIN)) as (K1 & _ & K3 & _).
      unfold cb_addr, cb_size, FILE_ALLOC in K1, K3. cbn [fst snd] in K1, K3. lia. }
    (* [comment removed for export] *)
    assert (APF : forall q2 A2 n2 q3 A3 n3, In (q2, A2, n2) FB -> In (q3, A3, n3) FB -> A2 <> A3 -> A2 + 1264 <= A3 \/ A3 + 1264 <= A2).
    { intros q2 A2 n2 q3 A3 n3 HIN2 HIN3 NE. destruct (FBn _ _ _ HIN2) as [-> _]. destruct (FBn _ _ _ HIN3) as [-> _].
      destruct (blocks_apart_In _ _ _ BAf HIN2 HIN3) as [E|AP]; [exfalso; apply NE; injection E as E1 E2; exact E2|].
      unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP. exact AP. }
    assert (DIST : forall q2 A2 n2 q3 A3 n3, In (q2, A2, n2) FB -> In (q3, A3, n3) FB -> A2 = A3 -> q2 = q3).
    { intros q2 A2 n2 q3 A3 n3 HIN2 HIN3 E. destruct (FBn _ _ _ HIN2) as [-> _]. destruct (FBn _ _ _ HIN3) as [-> _].
      destruct (blocks_apart_In _ _ _ BAf HIN2 HIN3) as [E'|AP]; [injection E' as E1 E2; exact E1|].
      unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP. lia. }
    pose proof (BKF _ _ _ INb) as (BK1 & BK2).
    (* [comment removed for export] *)
    assert (HL : F1 <> [] -> exists ql nl, In (ql, last_addr 0 F1, nl) F1) by (intros NE; exact (last_addr_In 0 F1 NE)).
    assert (HN : F2 <> [] -> exists qn nn, In (qn, hd_addr F2, nn) F2) by (intros NE; exact (hd_addr_In F2 NE)).
    (* [comment removed for export] *)
    set (P4 := fun a : Z => ~ (ATOP + 4096 <= a < SP) /\ ~ (A <= a < A + 1264) /\ ~ (A_OFL_HEAD <= a < A_OFL_HEAD + 8)
                            /\ ~ (F1 <> [] /\ last_addr 0 F1 + 112 <= a < last_addr 0 F1 + 120)
                            /\ ~ (F2 <> [] /\ hd_addr F2 + 104 <= a < hd_addr F2 + 112)).
    assert (AG : agrees_on P4 m m4).
    { eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha (N1 & N2 & N3 & N4 & N5).
      eapply outside_of_Forall. eapply Forall_impl; [| exact HW]. intros [lo' hi'] Hiv; cbn [fst snd] in Hiv |- *.
      destruct Hiv as [X|[X|[X|[(Xne & X1 & X2)|(Xne & X1 & X2)]]]]; [lia| lia| lia| |].
      - intros Hin. apply N4. split; [exact Xne| lia].
      - intros Hin. apply N5. split; [exact Xne| lia]. }
    (* [comment removed for export] *)
    assert (HSt : forall a, stdio_static a -> ~ (A_OFL_HEAD <= a < A_OFL_HEAD + 8) -> P4 a).
    { intros a Hs Hn. unfold stdio_static, A_OFL_HEAD in *. subst P4. cbn beta.
      split; [lia|]. split; [lia|]. split; [exact Hn|]. split.
      - intros (Xne & Xr). destruct (HL Xne) as (ql & nl & HINl).
        destruct (BKF ql _ nl ltac:(subst FB; apply in_or_app; left; exact HINl)) as (K3 & _). lia.
      - intros (Xne & Xr). destruct (HN Xne) as (qn & nn & HINn).
        destruct (BKF qn _ nn ltac:(subst FB; apply in_or_app; right; right; exact HINn)) as (K3 & _). lia. }
    (* [comment removed for export] *)
    assert (SR4 : STDIOR (set_files (files_remove eqb (lc_files (ps_libc s)) q) (ps_libc s)) (F1 ++ F2) m4).
    { unfold STDIOR. cbn [lc_stdout lc_stderr lc_files set_files].
      pose proof SOI as (_ & _ & SObs & _). pose proof SEI as (_ & _ & SEbs & _).
      unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED in *.
      split. { eapply FILE_R_agree; [exact SO | exact AG | intros a Ha; apply HSt; [unfold stdio_static; lia| unfold A_OFL_HEAD; lia]
                                     | rewrite SObs; unfold BUFSIZ; intros a Ha; apply HSt; [unfold stdio_static; lia| unfold A_OFL_HEAD; lia]]. }
      split; [exact SOI|].
      split. { eapply FILE_R_agree; [exact SE | exact AG | intros a Ha; apply HSt; [unfold stdio_static; lia| unfold A_OFL_HEAD; lia]
                                     | rewrite SEbs; intros a Ha; apply HSt; [unfold stdio_static; lia| unfold A_OFL_HEAD; lia]]. }
      split; [exact SEI|].
      split. { eapply agrees_rw_cells; [exact AG | exact SIN |]. unfold stdin_cells. rewrite file_cells_size. intros a Ha; apply HSt; [unfold stdio_static; lia| unfold A_OFL_HEAD; lia]. }
      split; [eapply agrees_rw_cells; [exact AG | exact U1 | intros a Ha; cbn in Ha; apply HSt; [unfold stdio_static; lia| unfold A_OFL_HEAD; lia]]|].
      split; [eapply agrees_rw_cells; [exact AG | exact U2 | intros a Ha; cbn in Ha; apply HSt; [unfold stdio_static; lia| unfold A_OFL_HEAD; lia]]|].
      split; [eapply agrees_rw_cells; [exact AG | exact U3 | intros a Ha; cbn in Ha; apply HSt; [unfold stdio_static; lia| unfold A_OFL_HEAD; lia]]|].
      split; [exact OL4|]. split; [exact OH4|].
      split; [| apply (NoDup_files_remove eqb); exact ND].
      subst FB. eapply (files_R_unlink eqb EQB P4); [exact FS| exact ND| exact AG| | exact DIST| exact LP4| exact LN4| lia|].
      - intros q2 A2 n2 a HIN2 Ha Hn1 Hn2.
        assert (HIN2' : In (q2, A2, n2) (F1 ++ (q, A, FILE_ALLOC) :: F2)) by (apply INFB; exact HIN2).
        destruct (BKF _ _ _ HIN2') as (K1 & K2).
        assert (NA : A2 <> A).
        { intros E. pose proof (DIST q2 A2 n2 q A FILE_ALLOC HIN2' INb E) as Eq.
          (* [comment removed for export] *)
          pose proof (files_R_toks m 0 _ _ FS) as TK.
          assert (NDT : List.NoDup (map cb_tok (F1 ++ (q, A, FILE_ALLOC) :: F2))) by (rewrite TK; exact ND).
          rewrite map_app in NDT. cbn [map cb_tok fst snd] in NDT. apply List.NoDup_remove_1 in NDT as NDT'.
          apply (List.NoDup_remove_2 _ _ _ NDT). rewrite <- map_app. subst q2.
          change q with (cb_tok (q, A2, n2)). apply in_map. exact HIN2. }
        pose proof (APF _ _ _ _ _ _ HIN2' INb NA) as APA.
        subst P4. cbn beta. unfold A_OFL_HEAD. split; [lia|]. split; [lia|]. split; [lia|]. split.
        + intros (Xne & Xr). destruct (HL Xne) as (ql & nl & HINl).
          destruct (Z.eq_dec A2 (last_addr 0 F1)) as [E|NE]; [apply Hn1; split; [exact E| lia]|].
          pose proof (APF _ _ _ _ _ _ HIN2' (INFB _ (in_or_app F1 F2 _ (or_introl HINl))) NE) as AP. lia.
        + intros (Xne & Xr). destruct (HN Xne) as (qn & nn & HINn).
          destruct (Z.eq_dec A2 (hd_addr F2)) as [E|NE]; [apply Hn2; split; [exact E| lia]|].
          pose proof (APF _ _ _ _ _ _ HIN2' (INFB _ (in_or_app F1 F2 _ (or_intror HINn))) NE) as AP. lia.
      - intros q2 A2 n2 HIN2. destruct (BKF _ _ _ HIN2) as (K1 & _). lia. }
    (* [comment removed for export] *)
    assert (HWA : Forall (fun iv => (ATOP + 4096 <= fst iv /\ snd iv <= SP) \/ iv_in_block FB iv
                      \/ (0xa9e90 <= fst iv /\ snd iv <= 0xaa160) \/ (0x6020a8 <= fst iv /\ snd iv <= 0x6028d0)) W).
    { eapply Forall_impl; [| exact HW]. intros [lo' hi'] X; cbn [fst snd] in X |- *.
      destruct X as [X|[X|[X|[(Xne & X1 & X2)|(Xne & X1 & X2)]]]].
      - left. exact X.
      - right; left. unfold iv_in_block. apply Exists_exists. exists (q, A, FILE_ALLOC). split; [exact INb | unfold cb_addr, cb_size, FILE_ALLOC; cbn [fst snd]; lia].
      - right; right; right. unfold A_OFL_HEAD in X. lia.
      - right; left. destruct (HL Xne) as (ql & nl & HINl). destruct (FBn ql _ nl ltac:(subst FB; apply in_or_app; left; exact HINl)) as [Enl _].
        unfold iv_in_block. apply Exists_exists. exists (ql, last_addr 0 F1, nl).
        split; [subst FB; apply in_or_app; left; exact HINl | unfold cb_addr, cb_size; cbn [fst snd]; subst nl; unfold FILE_ALLOC; lia].
      - right; left. destruct (HN Xne) as (qn & nn & HINn). destruct (FBn qn _ nn ltac:(subst FB; apply in_or_app; right; right; exact HINn)) as [Enn _].
        unfold iv_in_block. apply Exists_exists. exists (qn, hd_addr F2, nn).
        split; [subst FB; apply in_or_app; right; right; exact HINn | unfold cb_addr, cb_size; cbn [fst snd]; subst nn; unfold FILE_ALLOC; lia]. }
    assert (HWS : Forall (stdio_ivA FB SP) W).
    { eapply Forall_impl; [| exact HWA]. intros iv [X|[X|[X|X]]]; unfold stdio_ivA; [left; exact X | right; left; exact X | right; right; left; exact X | right; right; right; left; exact X]. }
    assert (MUn : munch (W ++ []) m m4) by (rewrite app_nil_r; exact MU).
    split.
    - eapply (gs_release _ GSL L RNG s CL F1 F2 FL m m4 W SP _ q A); [exact G | exact MU | exact WM | exact HWS | exact CSP | exact NOF | | exact SR4].
      eapply (errno_cell_kept L RNG s CL FB FL m m4 W [] SP); [exact G | exact MUn | exact WM | exact HWA | apply Forall_nil].
    - eapply agrees_on_weaken; [eapply (gs_keeps _ GSL L RNG s CL FB FL m m4 W [] SP); [exact G | exact MUn | exact WM | exact HWS | exact CSP]|].
      intros a Ha. split; [exact Ha | exact I].
  Qed.
  End Sz1.
  Lemma fclose_finishA : ltac:(let t := eval cbv delta [fclose_finishA__stmt] in fclose_finishA__stmt in exact t).
  Proof using EQB GL GSL. intros L RNG s CL F1 F2 FL m m4 W0 q A SP. ltac2:(SecDiet.SzSec.closeP 'fclose_finishA__body "vvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition fclose_o_proofA__stmt : Prop := fclose_stmt_o HO GIOA TP.
  Section Sz2.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL F1 F2 FL trC f Af lo : ltac2:(SecDiet.SzSec.tyM 'fclose_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fclose_o_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'fclose_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using EQB FREE FREENULL GL GSL HAL TPFC. pin_using (fun (EQB FREE FREENULL GL GSL HAL TPFC : unit) => tt).
 intros SPO UC TPF -> NOF.
    pose proof SPO as (_ & _ & _ & _ & _ & _ & _ & SPAL & (RSTKF & _ & RIMGSH & _)).
    pose proof (spo_factsA _ _ _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & _ & ENV & LOA & LOB & SPT & TOP47 & Etp & RSTK & RIMG & RTLS & KLO & GLO).
    destruct (gs_ssp _ GSL L) as [canary SSPL]. pose proof (SSPL _ _ _ _ _ _ G) as SSP.
    destruct (TPFC _ _ _ TPF) as [TRF TRN].
    subst tp. unfold STDIO_STACK, FILE_BLOCK in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (@ATOP_lo rc) as ATL. pose proof (@ATOP_hi rc) as ATH.
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G) as BA.
    pose proof (blocks_apart_app_inv _ _ BA) as (BAc & BAf & BAX).
    pose proof (blocks_apart_app_inv _ _ BAf) as (BA1 & BA2 & BAX12). cbn [blocks_apart] in BA2. destruct BA2 as [APfF2 BA2'].
    pose proof (gs_rng0 _ GSL _ _ _ _ _ _ _ G) as R0.
    destruct (gs_libc _ GSL _ _ _ _ _ _ _ G) as [_ NL].
    (* [comment removed for export] *)
    destruct (files_R_mid eqb EQB m 0 _ F1 F2 f Af 1264 FS ND) as (fm & LK & INf & _ & A0 & Ahi & FR & INV & HPV & HNX).
    remember (last_addr 0 F1) as pv eqn:Epv. remember (hd_addr F2) as nx eqn:Enx.
    destruct FR as (flags & mode & rp & tail & bufbytes & FC & FL' & BUF & BP & WB0 & WBL & RR & RP0 & RPHI & GLN).
    pose proof FL' as (FLn & FLw & FLe & FLerr & FLsvb & FLperm).
    pose proof INV as (ICH & IFD & IBS & INN & INW & INR & IRB). rewrite ICH in FLperm.
    (* [comment removed for export] *)
    assert (BKF : forall q2 A2 n2, In (q2, A2, n2) (F1 ++ (f, Af, 1264) :: F2) ->
              n2 = 1264 /\ 0x604000 <= A2 /\ A2 + 1264 <= lo /\ rng RNG A2 1264).
    { intros q2 A2 n2 HIN. destruct (files_R_pick eqb EQB m 0 _ _ q2 A2 n2 FS ND HIN) as (f' & pv' & nx' & _ & _ & En & B0 & _).
      subst n2. unfold FILE_ALLOC in *.
      destruct (live_block_factsA L RNG s CL _ FL m q2 A2 1264 lo G ltac:(apply in_or_app; right; exact HIN) LOA ltac:(lia)) as (_ & _ & K2 & K3 & _ & _ & K6).
      split; [reflexivity|]. split; [exact K3|]. split; [exact K2 | exact K6]. }
    destruct (live_block_factsA L RNG s CL _ FL m f Af 1264 lo G ltac:(apply in_or_app; right; apply in_or_app; right; left; reflexivity) LOA ltac:(lia))
      as (_ & _ & FK2 & FK3 & FKT & SOF & RGF).
    assert (PVF : pv <> 0 -> (pv + 1264 <= Af \/ Af + 1264 <= pv) /\ pv + 1264 <= lo /\ (pv + 1264 <= 0x10000 \/ 0x604000 <= pv) /\ 0 < pv).
    { intros NE. assert (NE1 : F1 <> []) by (intros E; apply NE; rewrite Epv, E; reflexivity).
      destruct (last_addr_In 0 F1 NE1) as (ql & nl & HINl). rewrite <- Epv in HINl.
      destruct (BKF ql pv nl ltac:(apply in_or_app; left; exact HINl)) as (-> & K1 & K2 & _).
      pose proof (BAX12 _ _ HINl (or_introl eq_refl)) as AP. unfold apart, cb_addr, cb_size in AP. cbn [fst snd] in AP. lia. }
    assert (NXF : nx <> 0 -> (nx + 1264 <= Af \/ Af + 1264 <= nx) /\ nx + 1264 <= lo /\ (nx + 1264 <= 0x10000 \/ 0x604000 <= nx) /\ 0 < nx).
    { intros NE. assert (NE2 : F2 <> []) by (intros E; apply NE; rewrite Enx, E; reflexivity).
      destruct (hd_addr_In F2 NE2) as (qn & nn & HINn). rewrite <- Enx in HINn.
      destruct (BKF qn nx nn ltac:(apply in_or_app; right; right; exact HINn)) as (-> & K1 & K2 & _).
      pose proof (proj1 (Forall_forall _ _) APfF2 _ HINn) as AP. unfold apart, cb_addr, cb_size in AP. cbn [fst snd] in AP. lia. }
    assert (PN : pv <> 0 -> nx <> 0 -> pv + 1264 <= nx \/ nx + 1264 <= pv \/ pv = nx).
    { intros NE NE'. assert (NE1 : F1 <> []) by (intros E; apply NE; rewrite Epv, E; reflexivity).
      assert (NE2 : F2 <> []) by (intros E; apply NE'; rewrite Enx, E; reflexivity).
      destruct (last_addr_In 0 F1 NE1) as (ql & nl & HINl). rewrite <- Epv in HINl.
      destruct (hd_addr_In F2 NE2) as (qn & nn & HINn). rewrite <- Enx in HINn.
      destruct (BKF ql pv nl ltac:(apply in_or_app; left; exact HINl)) as (-> & _).
      destruct (BKF qn nx nn ltac:(apply in_or_app; right; right; exact HINn)) as (-> & _).
      pose proof (BAX12 _ _ HINl (or_intror HINn)) as AP. unfold apart, cb_addr, cb_size in AP. cbn [fst snd] in AP. lia. }
    assert (RPV : pv <> 0 -> rng RNG (pv + 112) 8).
    { intros NE. assert (NE1 : F1 <> []) by (intros E; apply NE; rewrite Epv, E; reflexivity).
      destruct (last_addr_In 0 F1 NE1) as (ql & nl & HINl). rewrite <- Epv in HINl.
      destruct (BKF ql pv nl ltac:(apply in_or_app; left; exact HINl)) as (_ & _ & _ & K). eapply rng_sub'; [exact K | lia]. }
    assert (RNX : nx <> 0 -> rng RNG (nx + 104) 8).
    { intros NE. assert (NE2 : F2 <> []) by (intros E; apply NE; rewrite Enx, E; reflexivity).
      destruct (hd_addr_In F2 NE2) as (qn & nn & HINn). rewrite <- Enx in HINn.
      destruct (BKF qn nx nn ltac:(apply in_or_app; right; right; exact HINn)) as (_ & _ & _ & K). eapply rng_sub'; [exact K | lia]. }
    assert (PV0 : 0 <= pv) by (destruct (Z.eq_dec pv 0) as [E|NE]; [lia| destruct (PVF NE); lia]).
    assert (PVHI : pv + 1264 < 2^63) by (destruct (Z.eq_dec pv 0) as [E|NE]; [lia| destruct (PVF NE); lia]).
    assert (NX0 : 0 <= nx) by (destruct (Z.eq_dec nx 0) as [E|NE]; [lia| destruct (NXF NE); lia]).
    assert (NXHI : nx + 1264 < 2^63) by (destruct (Z.eq_dec nx 0) as [E|NE]; [lia| destruct (NXF NE); lia]).
    assert (HDR : 0 <= hd_addr (F1 ++ (f, Af, 1264) :: F2) < 2^64).
    { destruct F1 as [|[[q1 A1] n1] F1']; cbn [hd_addr app]; [lia|].
      destruct (BKF q1 A1 n1 ltac:(left; reflexivity)) as (_ & K1 & K2 & _). lia. }
    assert (RGFp : rng RNG Af 232) by (eapply rng_sub'; [exact RGF | lia]).
    assert (RGB : rng RNG (Af + 240) 1024) by (eapply rng_sub'; [exact RGF | lia]).
    (* [comment removed for export] *)
    destruct (gs_ahm _ GSL _ _ _ _ _ _ _ G) as (T & AHM & TAL & TLO & THI & RT & TZ & TAP).
    pose proof (TAP (f, Af, 1264) ltac:(apply in_or_app; right; apply in_or_app; right; left; reflexivity)) as TAF. unfold cb_addr, cb_size in TAF. cbn [fst snd] in TAF.
    pose proof (ahm_idx_range Af) as IDX.
    set (BKT := T + 120 * ahm_idx Af).
    assert (BC : rw_cells asegs m BKT ahm_bucket0) by (apply ahm_zero_bucket; [exact TZ | exact IDX]).
    assert (RBK : rng RNG BKT 120) by (eapply rng_sub'; [exact RT | subst BKT; unfold AHM_BYTES; lia]).
    remember (Z_to_bv 64 (bv_unsigned sp + -96) : word) as spm eqn:Espm.
    assert (Hspm : bv_unsigned spm = bv_unsigned sp + -96) by (rewrite Espm; apply unsigned_lit; lia).
    remember (Z_to_bv 64 (bv_unsigned spm + -48) : word) as spf eqn:Espf.
    assert (Hspf : bv_unsigned spf = bv_unsigned spm + -48) by (rewrite Espf; apply unsigned_lit; lia).
    remember (Z_to_bv 64 (bv_unsigned spf + -80) : word) as spg eqn:Espg.
    assert (Hspg : bv_unsigned spg = bv_unsigned spf + -80) by (rewrite Espg; apply unsigned_lit; lia).
    unfold s_fclose, Stdio.fclose.
    eapply implMG_lookup_file; [exact LK|].
    unfold fclose_file. apply implMG_bind_assoc.
    (* [comment removed for export] *)
    set (Qff := fun (f1 : file_st) (s' : PS) (ms' : machine_state) => s' = s /\ tr_inv fm f1 /\
      exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mode2 : word) (jk junk : list byte) (mapw bkt idxw : word) (cr : byte) (rest : list byte) (m3 : mem),
        ms' = MS (mkR (Z_to_bv 64 0x9a604) spf gp (Z_to_bv 64 ATP) t0' t1' t2' (Z_to_bv 64 Af) (Z_to_bv 64 12297829382473034410) (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                     (Z_to_bv 64 711808) (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x9a604) fc None m3 (seg_rom asegs)
        /\ munch [(lo, bv_unsigned sp); (Af, Af + 232)] m m3 /\ wmono asegs m m3 /\ mem_inv asegs m3
        /\ stk asegs m3 lo (bv_unsigned spf)
        /\ rw_cells asegs m3 Af (fcells flags 0 0 F_STDIO_CLOSE 0 0 0 F_STDIO_READ (wfn_of f1) F_STDIO_SEEK (Af + FILE_BUF_OFF) (f_bufsize fm) pv nx (f_fd fm) mode2 (lbf_of f1) tail)
        /\ rw_cells asegs m3 (bv_unsigned spf) [CB 8 jk; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 711808); C8 (Z_to_bv 64 12297829382473034410); C8 (Z_to_bv 64 Af); C8 (Z_to_bv 64 0x49cec)]
        /\ rw_cells asegs m3 (bv_unsigned sp + -96) [CB 8 junk]
        /\ rw_cells asegs m3 (bv_unsigned sp + -88) (ahm_handle mapw bkt (Z_to_bv 64 0) Af idxw cr rest)
        /\ rw_cells asegs m3 (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    eapply implMG_bind with (Q1 := fun f1 s' RNG' ms' => RNG' = RNG /\ Qff f1 s' ms').
    { apply implAM_implMG.
      (* [comment removed for export] *)
      eapply implAM_evt.
      { unfold FCLOSE_ENTRY.
        eapply (fclose_i_pre RNG ra sp gp (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 (Z_to_bv 64 Af) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo Af T);
          first [ reflexivity | exact MI | exact ST | exact KLO | exact ENV | exact AHM | exact BC | exact TAL | exact TLO | exact RIMG | exact RSTK | exact RBK | lia ]. }
      cbv beta. intros ms0 MID. unfold fclose_i_mid in MID. fold BKT in MID.
      destruct MID as (u0 & u1 & u2 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & u3 & u4 & u5 & u6 & junk & m0 & -> & MU0b & WM0 & MI0 & ST0 & FRa0 & HC0 & FRs0 & BC0).
      assert (MU0 : munch [(bv_unsigned sp + -272, bv_unsigned sp)] m m0).
      { eapply (ahm_munch_restore _ m m0 BKT MU0b); [subst BKT; lia | subst BKT; unfold AHM_BYTES in THI; lia | exact BC | exact BC0 |].
        intros a Ha. cbn [outside] in Ha |- *. destruct (Z_lt_ge_dec a BKT) as [C1|C1]; [left; lia|]. destruct (Z_lt_ge_dec a (BKT + 8)) as [C2|C2]; [right; lia | left; lia]. }
      clear MU0b BC0.
      rewrite <- Espm. rewrite <- Hspm in ST0.
      (* [comment removed for export] *)
      assert (FC0 : rw_cells asegs m0 Af (fcells flags rp (rp + zlength (f_rbuf fm)) F_STDIO_CLOSE
                (if f_wactive fm then Af + FILE_BUF_OFF + f_bufsize fm else 0) (if f_wactive fm then Af + FILE_BUF_OFF + zlength (f_wbuf fm) else 0) (if f_wactive fm then Af + FILE_BUF_OFF else 0)
                F_STDIO_READ (wfn_of fm) F_STDIO_SEEK (Af + FILE_BUF_OFF) (f_bufsize fm) pv nx (f_fd fm) mode (lbf_of fm) tail)).
      { eapply rw_cells_transport; [exact FC | exact MU0 | exact WM0 |]. unfold fcells. rewrite file_cells_size. cbn [disjoint_from]. lia. }
      (* [comment removed for export] *)
      assert (RSTKM : rng RNG lo (bv_unsigned spm - lo)) by (eapply rng_sub'; [exact RSTK | lia]).
      eapply implAM_evt.
      { eapply (fclose_S1 RNG (Z_to_bv 64 0x49cec) spm gp (Z_to_bv 64 ATP) (Z_to_bv 64 Af) (Z_to_bv 64 12297829382473034410) (Z_to_bv 64 711808) (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 F fc Af lo);
          first [ exact ST0 | exact MI0 | exact RSTKM | exact RGFp | exact RIMG | lia ]. }
      cbv beta. intros ms1 PO1. destruct PO1 as (jk & m1 & -> & FR1 & MU1 & WM1 & MI1 & ST1).
      rewrite <- Espf. rewrite <- Hspf in ST1, FR1.
      (* [comment removed for export] *)
      assert (MU01 : munch [(lo, bv_unsigned sp)] m m1).
      { eapply munch_trans; [eapply munch_weaken; [| exact MU0] | eapply munch_weaken; [| exact MU1]]; unfold sub_fp; cbn [outside]; intros x Hx; (keep_hyps rc sp Af lo pv nx T x LOB Hx spm Hspm; lia). }
      pose proof (wmono_trans asegs _ _ _ WM0 WM1) as WM01.
      assert (IES1 : iesafe [(lo, bv_unsigned sp)]) by (apply iesafe_one_high; unfold KHIGH in KLO; lia).
      assert (ENV1 : icptenv m1) by (eapply icptenv_transport; [exact ENV | exact MU01 | exact WM01 | exact IES1]).
      assert (RSTKF1 : rng RNG lo (bv_unsigned spf - lo)) by (eapply rng_sub'; [exact RSTK | lia]).
      eapply implAM_evt.
      { unfold FFLUSH_ICPT.
        eapply (fflush_i_pre RNG) with (lo := lo); first [ exact MI1 | exact ST1 | exact KLO | exact ENV1 | exact RIMG | exact RSTKF1 | lia ]. }
      cbv beta. intros ms2 MID2. unfold fflush_i_mid in MID2.
      destruct MID2 as (v0 & v1 & v2 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & v3 & v4 & v5 & v6 & junk2 & m2 & -> & MU2 & WM2 & MI2 & ST2 & FR2).
      rewrite <- Espg. rewrite <- Hspg in ST2, FR2.
      (* [comment removed for export] *)
      assert (MU02 : munch [(lo, bv_unsigned sp)] m m2).
      { eapply munch_trans; [exact MU01 | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; intros x Hx; (keep_hyps rc sp Af lo pv nx T spm spf x LOB Hspm Hspf Hx; lia). }
      pose proof (wmono_trans asegs _ _ _ WM01 WM2) as WM02.
      assert (FC2 : rw_cells asegs m2 Af (fcells flags rp (rp + zlength (f_rbuf fm)) F_STDIO_CLOSE
                (if f_wactive fm then Af + FILE_BUF_OFF + f_bufsize fm else 0) (if f_wactive fm then Af + FILE_BUF_OFF + zlength (f_wbuf fm) else 0) (if f_wactive fm then Af + FILE_BUF_OFF else 0)
                F_STDIO_READ (wfn_of fm) F_STDIO_SEEK (Af + FILE_BUF_OFF) (f_bufsize fm) pv nx (f_fd fm) mode (lbf_of fm) tail)).
      { eapply rw_cells_transport; [exact FC | exact MU02 | exact WM02 |]. unfold fcells. rewrite file_cells_size. cbn [disjoint_from]. lia. }
      assert (BUF2 : rw_cells asegs m2 (Af + FILE_BUF_OFF) [CB (Z.to_nat (f_bufsize fm)) bufbytes]).
      { eapply rw_cells_transport; [exact BUF | exact MU02 | exact WM02 |]. rewrite IBS. unfold BUFSIZ, FILE_BUF_OFF. cbn [disjoint_from cells_size csize Nat.add]. lia. }
      assert (SSP2 : ssp_cells m2 canary).
      { destruct SSP as [GOT GUARD]. split; (eapply rw_cells_transport; [eassumption | exact MU02 | exact WM02 | unfold got_ssp, ssp_guard; cbn [disjoint_from cells_size csize Nat.add]; lia]). }
      assert (RSTKG : rng RNG lo (bv_unsigned spg - lo)) by (eapply rng_sub'; [exact RSTK | lia]).
      eapply implAM_post_evt.
      { eapply (fflush_spec (St:=PS) RNG) with (f := fm) (Fp := Af) (flags := flags) (rp := rp) (closefn := F_STDIO_CLOSE) (readfn := F_STDIO_READ)
            (B := Af + FILE_BUF_OFF) (prev := pv) (next := nx) (mode := mode) (tail := tail) (bufbytes := bufbytes) (lo := lo) (canary := canary) (sp := spg);
          first [ exact FC2 | exact FLsvb | exact BUF2 | exact BP | exact WB0 | exact WBL | (intros _; exact ICH) | exact RP0 | exact RPHI | reflexivity
                | (rewrite ICH; exact IFD) | exact ST2 | exact SSP2 | exact MI2 | exact RSTKG | exact RGFp | exact RIMG | exact R0 | exact GLO
                | (rewrite IBS; unfold BUFSIZ, FILE_BUF_OFF; first [exact RGB | (keep_hyps rc sp Af T FKT lo spg FK2; lia)])
                | (rewrite ?IBS; unfold FFLUSH_DEPTH, BUFSIZ, FILE_BUF_OFF, got_ssp, ssp_guard; (keep_hyps rc sp Af lo T spm spf spg LOB Hspm Hspf Hspg L SPT TOP47 A0 FK2 FK3; lia))
                | match goal with |- ?g => idtac "FF side:" g end ]. }
      cbv beta. intros f1 st2 ms3 (-> & TRI & PO3).
      destruct PO3 as (w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & mode2 & m3 & -> & MU3 & WM3 & MI3 & ST3 & FC3 & SSP3).
      unfold ff_W, FFLUSH_DEPTH in MU3.
      replace (ret_pc (Z_to_bv 64 0x49b74)) with (Z_to_bv 64 0x49b74 : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
      (* [comment removed for export] *)
      assert (MU03 : munch [(lo, bv_unsigned sp); (Af, Af + 232)] m m3).
      { eapply munch_trans; [eapply munch_weaken; [| exact MU02] | eapply munch_weaken; [| exact MU3]]; unfold sub_fp; cbn [outside]; intros x Hx; (keep_hyps sp Af lo x Hx rc pv nx T spm spf spg LOB Hspm Hspf Hspg; lia). }
      pose proof (wmono_trans asegs _ _ _ WM02 WM3) as WM03.
      assert (AHM3 : rt_ahm m3 T) by (eapply rw_cells_transport; [exact AHM | exact MU03 | exact WM03 | cbn [disjoint_from cells_size csize Nat.add]; lia]).
      assert (BC3 : rw_cells asegs m3 BKT ahm_bucket0).
      { eapply rw_cells_transport; [exact BC | exact MU03 | exact WM03 |]. unfold ahm_bucket0. cbn [disjoint_from cells_size csize Nat.add]. subst BKT. unfold AHM_BYTES in *. (keep_hyps rc sp Af lo pv nx T LOA THI TAF IDX; lia). }
      assert (FR3 : rw_cells asegs m3 (bv_unsigned spg) [CB 56 junk2; C8 (Z_to_bv 64 12297829382473034410); C8 (Z_to_bv 64 Af); C8 (Z_to_bv 64 0x9a604)]).
      { eapply rw_cells_transport; [exact FR2 | exact MU3 | exact WM3 |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
      rewrite Hspg in ST3, FR3. rewrite Espg.
      eapply evtF_mono.
      { eapply (fflush_i_post RNG) with (sp := spf) (lo := lo) (fp := Af) (TABLE := T) (m := m3);
          first [ exact MI3 | exact ST3 | exact FR3 | exact AHM3 | exact BC3 | exact TAL | exact TLO | exact GLO | exact RIMG | exact RSTKF1 | exact RBK | lia
                | match goal with |- ?g => idtac "FFPOST side:" g end ]. }
      cbv beta. intros ms4 PO4. unfold fflush_i_post_post in PO4. fold BKT in PO4.
      destruct PO4 as (z0 & z1 & z2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & z3 & z4 & z5 & z6 & m4 & -> & MU4b & WM4 & MI4 & ST4 & BC4).
      assert (MU4 : munch [(bv_unsigned spf + -256, bv_unsigned spf)] m3 m4).
      { eapply (ahm_munch_restore _ m3 m4 BKT MU4b); [subst BKT; lia | subst BKT; unfold AHM_BYTES in THI; lia | exact BC3 | exact BC4 |].
        intros a Ha. cbn [outside] in Ha |- *. destruct (Z_lt_ge_dec a BKT) as [C1|C1]; [left; lia|]. destruct (Z_lt_ge_dec a (BKT + 8)) as [C2|C2]; [right; lia | left; lia]. }
      clear MU4b.
      replace (ret_pc (Z_to_bv 64 0x9a604)) with (Z_to_bv 64 0x9a604 : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
      (* [comment removed for export] *)
      assert (MU04 : munch [(lo, bv_unsigned spm); (Af, Af + 232)] m0 m4).
      { eapply munch_trans; [eapply munch_weaken; [| exact MU1] |].
        2:{ eapply munch_trans; [eapply munch_weaken; [| exact MU2] |].
            2:{ eapply munch_trans; [eapply munch_weaken; [| exact MU3] | eapply munch_weaken; [| exact MU4]]; unfold sub_fp; cbn [outside]; intros x Hx; (keep_hyps rc sp Af lo pv nx T spm spf spg x LOB Hspm Hspf Hspg Hx; lia). }
            unfold sub_fp; cbn [outside]; intros x Hx; (keep_hyps rc sp Af lo pv nx T spm spf x LOB Hspm Hspf Hx; lia). }
        unfold sub_fp; cbn [outside]; intros x Hx; lia. }
      pose proof (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 (wmono_trans asegs _ _ _ WM3 WM4))) as WM04.
      split; [reflexivity|]. split; [exact TRI|].
      exists z0, z1, z2, e1, e2, e3, e4, e5, e6, e7, z3, z4, z5, z6, mode2, jk, junk.
      eexists _, _, _, _, _, m4.
      split; [reflexivity|].
      split. { eapply munch_trans; [exact MU03 | eapply munch_weaken; [| exact MU4]]; unfold sub_fp; cbn [outside]; intros x Hx; (keep_hyps rc sp Af lo pv nx T spm spf x LOB Hspm Hspf Hx; lia). }
      split; [exact (wmono_trans asegs _ _ _ WM03 WM4)|]. split; [exact MI4|]. split; [exact ST4|].
      split. { eapply rw_cells_transport; [exact FC3 | exact MU4 | exact WM4 |]. unfold fcells. rewrite file_cells_size. cbn [disjoint_from]. lia. }
      split. { eapply (rw_cells_transport asegs [(lo, bv_unsigned spf); (Af, Af + 232)] m1 m4); [exact FR1 | | | cbn [disjoint_from cells_size csize Nat.add]; lia].
               - eapply munch_trans; [eapply munch_weaken; [| exact MU2] |].
                 2:{ eapply munch_trans; [eapply munch_weaken; [| exact MU3] | eapply munch_weaken; [| exact MU4]]; unfold sub_fp; cbn [outside]; intros x Hx; (keep_hyps rc sp Af lo pv nx T spm spf spg x LOB Hspm Hspf Hspg Hx; lia). }
                 unfold sub_fp; cbn [outside]; intros x Hx; (keep_hyps rc sp Af lo pv nx T spm spf x LOB Hspm Hspf Hx; lia).
               - exact (wmono_trans asegs _ _ _ WM2 (wmono_trans asegs _ _ _ WM3 WM4)). }
      split; [eapply rw_cells_transport; [exact FRa0 | exact MU04 | exact WM04 | cbn [disjoint_from cells_size csize Nat.add]; lia]|].
      split; [eapply rw_cells_transport; [exact HC0 | exact MU04 | exact WM04 | unfold ahm_handle; cbn [disjoint_from cells_size csize Nat.add]; lia]|].
      eapply rw_cells_transport; [exact FRs0 | exact MU04 | exact WM04 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    cbv beta. intros f1 s' RNG' ms' [-> QF]. unfold Qff in QF. clear Qff. destruct QF as (-> & TRI & QF).
    destruct QF as (z0 & z1 & z2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & z3 & z4 & z5 & z6 & mode2 & jk & junk & mapw & bkt & idxw & cr & rest & m4 & -> & MU4 & WM4 & MI4 & ST4 & FC4 & FR4 & FRa4 & HC4 & FRs4).
    pose proof TRI as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & _).
    assert (RSTKM : rng RNG lo (bv_unsigned spm - lo)) by (eapply rng_sub'; [exact RSTK | lia]).
    assert (RSTKF1 : rng RNG lo (bv_unsigned spf - lo)) by (eapply rng_sub'; [exact RSTK | lia]).
    (* [comment removed for export] *)
    eapply implMG_bind with (Q1 := fun (_ : unit) s' RNG' ms' => RNG' = RNG /\
              stdio_close_post (Z_to_bv 64 0x9a62c) spf gp (Z_to_bv 64 ATP) (Z_to_bv 64 Af) (Z_to_bv 64 0) (Z_to_bv 64 711808) (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 F fc s lo m4 tt s' ms').
    { apply implAM_implMG. eapply implAM_evt.
      { rewrite Espf. eapply (fclose_S2 RNG) with (sp := spm) (Fp := Af) (lo := lo);
          first [ exact FC4 | exact MI4 | exact RSTKM | exact RGFp | exact RIMG | lia | match goal with |- ?g => idtac "S2 side:" g end ]. }
      cbv beta. intros ms5 ->. rewrite <- Espf. rewrite T1.
      eapply (stdio_close_spec (St:=PS) RNG) with (fd := f_fd fm) (lo := lo) (Fp := Af);
        first [ (unfold fcells in FC4; exact FC4) | reflexivity | exact IFD | exact ST4 | exact MI4 | exact RSTKF1 | exact RGFp | exact RIMG | exact GLO | lia
              | match goal with |- ?g => idtac "CL side:" g end ]. }
    cbv beta. intros [] s' RNG' ms' [-> (-> & PO5)].
    destruct PO5 as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m5 & -> & MU5 & WM5 & MI5 & ST5).
    replace (ret_pc (Z_to_bv 64 0x9a62c)) with (Z_to_bv 64 0x9a62c : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    apply implMG_upd_lc.
    (* [comment removed for export] *)
    assert (MU05 : munch [(lo, bv_unsigned sp); (Af, Af + 232)] m m5).
    { eapply munch_trans; [exact MU4 | eapply munch_weaken; [| exact MU5]]; unfold sub_fp; cbn [outside]; intros x Hx; (keep_hyps rc sp Af lo pv nx T spm spf x LOB Hspm Hspf Hx; lia). }
    pose proof (wmono_trans asegs _ _ _ WM4 WM5) as WM05.
    assert (FC5 : rw_cells asegs m5 Af (fclose_cells flags F_STDIO_CLOSE F_STDIO_READ (wfn_of f1) F_STDIO_SEEK (Af + FILE_BUF_OFF) (f_bufsize fm) pv nx (f_fd fm) mode2 (lbf_of f1) tail)).
    { apply fclose_cells_recast; [| exact GLN]. unfold fcells in FC4. eapply rw_cells_transport; [exact FC4 | exact MU5 | exact WM5 | rewrite file_cells_size; cbn [disjoint_from]; lia]. }
    assert (NL5 : rw_cells asegs m5 NEED_LOCKS [C1 (Z_to_bv 8 0)]) by (unfold NEED_LOCKS; eapply rw_cells_transport; [exact NL | exact MU05 | exact WM05 | cbn [disjoint_from cells_size csize Nat.add]; lia]).
    assert (OL5 : rw_cells asegs m5 A_OFL_LOCK [C4 (Z_to_bv 64 0)]) by (unfold A_OFL_LOCK in *; eapply rw_cells_transport; [exact OL | exact MU05 | exact WM05 | cbn [disjoint_from cells_size csize Nat.add]; lia]).
    assert (OH5 : rw_cells asegs m5 A_OFL_HEAD [C8 (Z_to_bv 64 (hd_addr (F1 ++ (f, Af, 1264) :: F2)))]) by (unfold A_OFL_HEAD in *; eapply rw_cells_transport; [exact OH | exact MU05 | exact WM05 | cbn [disjoint_from cells_size csize Nat.add]; lia]).
    assert (KEEP5 : forall A cs, rw_cells asegs m4 A cs -> bv_unsigned spf <= A -> rw_cells asegs m5 A cs).
    { intros A cs HC HA. eapply rw_cells_transport; [exact HC | exact MU5 | exact WM5 |]. cbn [disjoint_from]. pose proof (rw_cells_bound _ _ _ _ HC). lia. }
    pose proof (KEEP5 _ _ FR4 ltac:(lia)) as FR5. pose proof (KEEP5 _ _ FRa4 ltac:(lia)) as FRa5. pose proof (KEEP5 _ _ HC4 ltac:(lia)) as HC5. pose proof (KEEP5 _ _ FRs4 ltac:(lia)) as FRs5.
    assert (PVC5 : pv <> 0 -> rw_cells asegs m5 (pv + 112) [C8 (Z_to_bv 64 Af)]).
    { intros NE. destruct (PVF NE) as (P1 & P2 & P3 & P4). destruct (HPV ltac:(intros E; apply NE; rewrite Epv, E; reflexivity)) as [PC _].
      eapply rw_cells_transport; [exact PC | exact MU05 | exact WM05 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    assert (NXC5 : nx <> 0 -> rw_cells asegs m5 (nx + 104) [C8 (Z_to_bv 64 Af)]).
    { intros NE. destruct (NXF NE) as (N1 & N2 & N3 & N4). destruct (HNX ltac:(intros E; apply NE; rewrite Enx, E; reflexivity)) as [NC _].
      eapply rw_cells_transport; [exact NC | exact MU05 | exact WM05 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    (* [comment removed for export] *)
    rewrite Espf. rewrite Hspf in ST5, FR5.
    apply implMG_from_evtF.
    eapply evtF_cut.
      { eapply (fclose_S3a RNG) with (sp := spm) (Fp := Af) (lo := lo);
          first [ exact FC5 | exact FLperm | exact NL5 | exact ST5 | exact MI5 | exact RSTKM | exact RGFp | exact RIMG | exact GLO | lia
                | match goal with |- ?g => idtac "S3a side:" g end ]. }
      cbv beta. intros ms6 PO6. destruct PO6 as (x1' & a1' & a2' & a3' & m6 & -> & MU6 & WM6 & MI6 & ST6).
      assert (MU6' : munch (fcW spm pv nx) m5 m6).
      { eapply munch_weaken; [| exact MU6]. unfold sub_fp, fcW. cbn [outside]. intros x (O1 & _). split; [exact O1 | exact I]. }
      assert (FC6 : rw_cells asegs m6 Af (fclose_cells flags F_STDIO_CLOSE F_STDIO_READ (wfn_of f1) F_STDIO_SEEK (Af + FILE_BUF_OFF) (f_bufsize fm) pv nx (f_fd fm) mode2 (lbf_of f1) tail)).
      { eapply rw_cells_transport; [exact FC5 | exact MU6 | exact WM6 | unfold fclose_cells; cbn [disjoint_from cells_size csize Nat.add]; lia]. }
      assert (OH6 : rw_cells asegs m6 A_OFL_HEAD [C8 (Z_to_bv 64 (hd_addr (F1 ++ (f, Af, 1264) :: F2)))]) by (unfold A_OFL_HEAD in *; eapply rw_cells_transport; [exact OH5 | exact MU6 | exact WM6 | cbn [disjoint_from cells_size csize Nat.add]; lia]).
      assert (PVC6 : pv <> 0 -> rw_cells asegs m6 (pv + 112) [C8 (Z_to_bv 64 Af)]).
      { intros NE. destruct (PVF NE) as (P1 & P2 & P3 & P4). eapply rw_cells_transport; [exact (PVC5 NE) | exact MU6 | exact WM6 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
      assert (NXC6 : nx <> 0 -> rw_cells asegs m6 (nx + 104) [C8 (Z_to_bv 64 Af)]).
      { intros NE. destruct (NXF NE) as (N1 & N2 & N3 & N4). eapply rw_cells_transport; [exact (NXC5 NE) | exact MU6 | exact WM6 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
      eapply evtF_cut.
      { eapply (fclose_S3b RNG) with (sp := spm) (Fp := Af) (lo := lo) (pv := pv) (nx := nx) (m0 := m5);
          first [ exact FC6 | exact PVC6 | exact NXC6 | exact OH6 | exact ST6 | exact MU6' | exact WM6 | exact MI6
                | exact PV0 | exact PVHI | exact PVF | exact NXF | exact PN | exact RPV | exact RSTKM | exact RGFp | exact RIMG | lia
                | match goal with |- ?g => idtac "S3b side:" g end ]. }
      cbv beta. intros ms7 PO7. destruct PO7 as (m7 & -> & FC7 & PVC7 & NXC7 & OH7 & ST7 & MU7 & WM7 & MI7).
      eapply evtF_cut.
      { eapply (fclose_S3c RNG) with (sp := spm) (Fp := Af) (lo := lo) (pv := pv) (nx := nx) (m0 := m5);
          first [ exact FC7 | exact PVC7 | exact NXC7 | exact OH7 | exact ST7 | exact MU7 | exact WM7 | exact MI7
                | exact NX0 | exact NXHI | exact PVF | exact NXF | exact PN | exact RNX | exact RSTKM | exact RGFp | exact RIMG | lia
                | match goal with |- ?g => idtac "S3c side:" g end ]. }
      cbv beta. intros ms8 PO8. destruct PO8 as (a1'' & m8 & -> & FC8 & PVC8 & NXC8 & OH8 & ST8 & MU8 & WM8 & MI8).
      eapply evtF_cut.
      { eapply (fclose_S3d RNG) with (sp := spm) (Fp := Af) (lo := lo) (pv := pv) (nx := nx) (m0 := m5);
          first [ exact FC8 | exact PVC8 | exact NXC8 | exact OH8 | exact HDR | exact ST8 | exact MU8 | exact WM8 | exact MI8
                | exact PVHI | exact NXHI | exact PVF | exact NXF | exact PN | exact RSTKM | exact RGFp | exact RIMG | lia
                | match goal with |- ?g => idtac "S3d side:" g end ]. }
      cbv beta. intros ms9 PO9. destruct PO9 as (a0'' & m9 & -> & FC9 & PVC9 & NXC9 & OH9 & ST9 & MU9 & WM9 & MI9).
      unfold fcW in MU9.
      assert (OL9 : rw_cells asegs m9 A_OFL_LOCK [C4 (Z_to_bv 64 0)]).
      { eapply rw_cells_transport; [exact OL5 | exact MU9 | exact WM9 |]. cbn [disjoint_from cells_size csize Nat.add]. unfold A_OFL_LOCK, A_OFL_HEAD.
        destruct (Z.eqb_spec pv 0) as [E|NE]; [| destruct (PVF NE) as (P1 & P2 & P3 & P4)];
        destruct (Z.eqb_spec nx 0) as [E'|NE']; try destruct (NXF NE') as (N1 & N2 & N3 & N4); (keep_hyps rc sp Af lo pv nx T spm LOA LOB Hspm E E' N3 P3; lia). }
      eapply evtF_cut.
      { eapply (fclose_S3e RNG) with (sp := spm) (Fp := Af) (lo := lo);
          first [ exact FC9 | exact OL9 | exact MI9 | exact RSTKM | exact RGFp | exact RIMG | exact GLO | lia
                | match goal with |- ?g => idtac "S3e side:" g end ]. }
      cbv beta. intros ms10 PO10. destruct PO10 as (b1 & b2 & b3 & b4 & b5 & ->). apply evtF_done.
    (* [comment removed for export] *)
    assert (MUT : munch [(lo, bv_unsigned sp); (Af, Af + 232); (bv_unsigned spm - 64, bv_unsigned spm - 48);
                         (pv + 112, pv + (if pv =? 0 then 112 else 120)); (nx + 104, nx + (if nx =? 0 then 104 else 112));
                         (A_OFL_HEAD, A_OFL_HEAD + 8)] m m9).
    { apply (munch_trans _ m m5 m9); [eapply munch_weaken; [| exact MU05] | eapply munch_weaken; [| exact MU9]];
        unfold sub_fp; cbn [outside]; intros x Hx; destruct (pv =? 0); destruct (nx =? 0); (keep_hyps rc sp Af lo pv nx T spm x Hx; lia). }
    pose proof (wmono_trans asegs _ _ _ WM05 WM9) as WMT.
    assert (NE1 : F1 <> [] -> pv <> 0).
    { intros NE E. destruct (last_addr_In 0 F1 NE) as (ql & nl & HINl). rewrite <- Epv, E in HINl.
      destruct (BKF ql 0 nl ltac:(apply in_or_app; left; exact HINl)) as (_ & K1 & _). lia. }
    assert (NE2 : F2 <> [] -> nx <> 0).
    { intros NE E. destruct (hd_addr_In F2 NE) as (qn & nn & HINn). rewrite <- Enx, E in HINn.
      destruct (BKF qn 0 nn ltac:(apply in_or_app; right; right; exact HINn)) as (_ & K1 & _). lia. }
    assert (OH9' : rw_cells asegs m9 A_OFL_HEAD [C8 (Z_to_bv 64 (hd_addr (F1 ++ F2)))]).
    { destruct F1 as [|[[q1 A1] n1] F1']; cbn [hd_addr app] in OH9 |- *.
      - rewrite Z.eqb_refl in OH9. rewrite <- Enx. exact OH9.
      - replace (A1 =? Af) with false in OH9; [exact OH9|]. symmetry. apply Z.eqb_neq.
        pose proof (BAX12 (q1, A1, n1) (f, Af, 1264) ltac:(left; reflexivity) ltac:(left; reflexivity)) as AP.
        destruct (BKF q1 A1 n1 ltac:(left; reflexivity)) as (-> & _).
        unfold apart, cb_addr, cb_size in AP. cbn [fst snd] in AP. (keep_hyps rc sp Af lo A1 pv nx T AP; lia). }
    assert (LP9 : F1 <> [] -> rw_cells asegs m9 (last_addr 0 F1 + 112) [C8 (Z_to_bv 64 (hd_addr F2))]).
    { intros NE. rewrite <- Epv, <- Enx. exact (PVC9 (NE1 NE)). }
    assert (LN9 : F2 <> [] -> rw_cells asegs m9 (hd_addr F2 + 104) [C8 (Z_to_bv 64 (last_addr 0 F1))]).
    { intros NE. rewrite <- Epv, <- Enx. exact (NXC9 (NE2 NE)). }
    assert (HWT : Forall (fun iv : Z * Z => snd iv <= fst iv \/ (ATOP + 4096 <= fst iv /\ snd iv <= bv_unsigned sp) \/ (Af <= fst iv /\ snd iv <= Af + 1264)
                            \/ (fst iv = A_OFL_HEAD /\ snd iv = A_OFL_HEAD + 8)
                            \/ (F1 <> [] /\ fst iv = last_addr 0 F1 + 112 /\ snd iv = last_addr 0 F1 + 120)
                            \/ (F2 <> [] /\ fst iv = hd_addr F2 + 104 /\ snd iv = hd_addr F2 + 112))
              [(lo, bv_unsigned sp); (Af, Af + 232); (bv_unsigned spm - 64, bv_unsigned spm - 48);
               (pv + 112, pv + (if pv =? 0 then 112 else 120)); (nx + 104, nx + (if nx =? 0 then 104 else 112)); (A_OFL_HEAD, A_OFL_HEAD + 8)]).
    { apply Forall_cons; [cbn [fst snd]; right; left; lia|].
      apply Forall_cons; [cbn [fst snd]; right; right; left; lia|].
      apply Forall_cons; [cbn [fst snd]; right; left; lia|].
      apply Forall_cons.
      { cbn [fst snd]. destruct (Z.eqb_spec pv 0) as [E|NE]; [left; lia|]. right; right; right; right; left.
        split; [intros EF; apply NE; rewrite Epv, EF; reflexivity|]. rewrite <- Epv. split; reflexivity. }
      apply Forall_cons.
      { cbn [fst snd]. destruct (Z.eqb_spec nx 0) as [E|NE]; [left; lia|]. right; right; right; right; right.
        split; [intros EF; apply NE; rewrite Enx, EF; reflexivity|]. rewrite <- Enx. split; reflexivity. }
      apply Forall_cons; [cbn [fst snd]; right; right; right; left; split; reflexivity | apply Forall_nil]. }
    destruct (fclose_finishA L RNG s CL F1 F2 FL m m9 _ f Af (bv_unsigned sp) G NOF MUT WMT HWT ltac:(lia) OL9 OH9' LP9 LN9) as [G9 AG9].
    (* [comment removed for export] *)
    assert (KEEP9 : forall A cs, rw_cells asegs m5 A cs -> bv_unsigned spm + -48 <= A -> rw_cells asegs m9 A cs).
    { intros A cs HC HA. eapply rw_cells_transport; [exact HC | exact MU9 | exact WM9 |]. pose proof (rw_cells_bound _ _ _ _ HC) as HB.
      cbn [disjoint_from]. unfold A_OFL_HEAD.
      destruct (Z.eqb_spec pv 0) as [E|NE]; [| destruct (PVF NE) as (P1 & P2 & P3 & P4)];
      destruct (Z.eqb_spec nx 0) as [E'|NE']; try destruct (NXF NE') as (N1 & N2 & N3 & N4); lia. }
    pose proof (KEEP9 _ _ FR5 ltac:(lia)) as FR9. pose proof (KEEP9 _ _ FRa5 ltac:(lia)) as FRa9. pose proof (KEEP9 _ _ HC5 ltac:(lia)) as HC9. pose proof (KEEP9 _ _ FRs5 ltac:(lia)) as FRs9.
    (* [comment removed for export] *)
    assert (EAF : bv_unsigned (Z_to_bv 64 Af : word) = Af) by (apply unsigned_lit; lia).
    rewrite <- Espf. rewrite <- Hspf in ST9, FR9.
    assert (SPOF : forall mm (sx : PS) CLx, GIOA L RNG sx CLx (F1 ++ F2) FL mm -> stk asegs mm lo (bv_unsigned spf) -> mem_inv asegs mm ->
              std_pre_o GIOA L RNG spf (Z_to_bv 64 ATP) sx CLx (F1 ++ F2) FL lo FREE_STACK mm).
    { intros mm sx CLx Gx STx MIx. split; [exact Gx|]. split; [exact STx|]. split; [exact LOA|]. split; [unfold FREE_STACK; lia|].
      split; [split; [lia | exact TOP47]|]. split; [exact MIx|]. split; [reflexivity|].
      split; [rewrite Hspf, Hspm; clear - SPAL; Z.div_mod_to_equations; lia|].
      split; [exact RSTKF|]. split; [exact RIMG|]. split; [exact RIMGSH | exact RTLS]. }
    assert (UNWF : forall mm X, In [AFREE_PC; X] (al_U L) -> 4096 <= X < 2^64 -> X <> AFREE_PC -> unw_okA L RNG mm lo AFREE_PC spf (Z_to_bv 64 Af) (Z_to_bv 64 X)).
    { intros mm X HIN HX NX. assert (EX : bv_unsigned (Z_to_bv 64 X : word) = X) by (apply unsigned_lit; lia).
      unfold unw_okA, aunw. rewrite EAF, EX. split; [| (keep_hyps rc sp Af lo pv nx T spm spf X LOA LOB FKT Hspm Hspf HX NX; lia)].
      exists []. left. split; [lia|]. split; [apply uc_stop; intros (Y & _); lia|]. split; [cbn [length]; lia|]. split; [exact HIN | exact RSTKF]. }
    eapply implMG_evtF.
    { unfold FREE_ENTRY'.
      eapply (FREENULL (Z_to_bv 64 0x9a688) spf gp (Z_to_bv 64 ATP)) with (L := L) (CL := (f, Af, FILE_ALLOC) :: CL) (FB := F1 ++ F2) (FL := FL) (lo := lo);
        [ apply SPOF; [exact G9 | exact ST9 | exact MI9] | reflexivity | apply UNWF; [exact TRN | lia | unfold AFREE_PC; lia] ]. }
    cbv beta. intros ms11 PO11. destruct PO11 as (a0v & m10 & REGS & MI10 & ST10 & AG10 & G10).
    unfold hpost_regs in REGS. destruct REGS as (g0 & g1 & g2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & g3 & g4 & g5 & g6 & ->).
    replace (ret_pc (Z_to_bv 64 0x9a688)) with (Z_to_bv 64 0x9a688 : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    (* [comment removed for export] *)
    eapply implMG_evtF.
    { rewrite Espf. eapply (fclose_S3f RNG) with (sp := spm) (Fp := Af) (lo := lo);
        first [ exact MI10 | exact RSTKM | exact RGFp | exact RIMG | lia | match goal with |- ?g => idtac "S3f side:" g end ]. }
    cbv beta. intros ms12 ->. rewrite <- Espf.
    eapply implMG_post_evtF.
    { unfold FREE_ENTRY'.
      eapply (FREE (Z_to_bv 64 FCLOSE_FREE_RA) spf gp (Z_to_bv 64 ATP)) with (L := L) (C1 := []) (C2 := CL) (FB := F1 ++ F2) (FL := FL) (q := f) (A := Af) (n := FILE_ALLOC) (lo := lo);
        [ apply SPOF; [exact G10 | exact ST10 | exact MI10] | reflexivity | apply UNWF; [exact TRF | unfold FCLOSE_FREE_RA; lia | unfold FCLOSE_FREE_RA, AFREE_PC; lia] ]. }
    cbv beta. intros [] sF RNG11 ms13 (FP11 & a0v' & m11 & REGS & OF11 & MI11 & ST11 & AG11 & G11).
    unfold hpost_regs in REGS. destruct REGS as (k0 & k1 & k2 & l1 & l2 & l3 & l4 & l5 & l6 & l7 & k3 & k4 & k5 & k6 & ->).
    replace (ret_pc (Z_to_bv 64 FCLOSE_FREE_RA)) with (Z_to_bv 64 FCLOSE_FREE_RA : word) by (unfold FCLOSE_FREE_RA; symmetry; apply ret_pc_even; [lia | reflexivity]).
    cbn [app] in AG11, G11.
    (* [comment removed for export] *)
    assert (KEEP11 : forall A cs, rw_cells asegs m9 A cs -> bv_unsigned spf <= A -> rw_cells asegs m11 A cs).
    { intros A cs HC HA. eapply keeps_rw_cells_stack; [exact AG11 | eapply keeps_rw_cells_stack; [exact AG10 | exact HC | exact HA] | exact HA]. }
    pose proof (KEEP11 _ _ FR9 ltac:(lia)) as FR11. pose proof (KEEP11 _ _ FRa9 ltac:(lia)) as FRa11. pose proof (KEEP11 _ _ HC9 ltac:(lia)) as HC11. pose proof (KEEP11 _ _ FRs9 ltac:(lia)) as FRs11.
    assert (RSTK11 : rng RNG11 lo (bv_unsigned sp - lo)) by (eapply rng_fp_le; [exact FP11 | exact RSTK]).
    assert (RSTKM11 : rng RNG11 lo (bv_unsigned spm - lo)) by (eapply rng_sub'; [exact RSTK11 | lia]).
    assert (RGFp11 : rng RNG11 Af 232) by (eapply rng_fp_le; [exact FP11 | exact RGFp]).
    assert (RIMG11 : rng_aimg RNG11) by (eapply rng_fp_le; [exact FP11 | exact RIMG]).
    rewrite Hspf in ST11, FR11. rewrite Espf.
    eapply evtF_cut.
    { eapply (fclose_S4 RNG11 (Z_to_bv 64 0x49cec) spm gp (Z_to_bv 64 ATP) (Z_to_bv 64 Af) (Z_to_bv 64 12297829382473034410) (Z_to_bv 64 711808) (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 F fc Af lo);
        first [ exact FR11 | exact ST11 | exact MI11 | exact RSTKM11 | exact RGFp11 | exact RIMG11 | lia | match goal with |- ?g => idtac "S4 side:" g end ]. }
    cbv beta. intros ms14 [-> ST14].
    replace (ret_pc (Z_to_bv 64 0x49cec)) with (Z_to_bv 64 0x49cec : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    rewrite Hspm in ST14. rewrite Espm.
    eapply evtF_mono.
    { eapply (fclose_i_post RNG11) with (lo := lo) (fp := Af) (m := m11);
        first [ exact MI11 | exact ST14 | exact FRa11 | exact HC11 | exact FRs11 | (eapply rng_sub'; [exact RSTK11 | lia]) | lia
              | match goal with |- ?g => idtac "IPOST side:" g end ]. }
    cbv beta. intros ms15 [-> ST15].
    split; [exact FP11|].
    eexists _, m11. split; [unfold hpost_regs; repeat eexists; reflexivity|].
    split; [destruct s as [xh xl xo xt]; cbn [ps_outfile set_libc] in OF11 |- *; exact OF11|].
    split; [exact MI11|]. split; [exact ST15|].
    split; [| exact G11].
    eapply agrees_on_trans; [exact AG9|]. eapply agrees_on_trans.
    - eapply client_keeps_weaken; [exact AG10 | lia | intros a Ha; apply in_block_cons; exact Ha | apply incl_refl].
    - eapply client_keeps_weaken; [exact AG11 | lia | intros a Ha; exact Ha | apply incl_refl].
  Qed.
  End Sz2.
  Theorem fclose_o_proofA : ltac:(let t := eval cbv delta [fclose_o_proofA__stmt] in fclose_o_proofA__stmt in exact t).
  Proof using EQB FREE FREENULL GL GSL HAL TPFC. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL F1 F2 FL trC f Af lo. ltac2:(SecDiet.SzSec.closeP 'fclose_o_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End GlueFc.
End TwB.
End Stdio_glue_fcA.

(* [comment removed for export] *)
Module Stdio_glue_foA.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_cs__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_lock__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_strerror__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_fopen. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_fopen__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_read__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA Stdio_glueKitA StdioLawsA Stdio_glueA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_lock OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.F_fmodeflags OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_fopen OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_fopen OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_read__A3S.F_stdio_read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioLawsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_foKitA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac sbl_is_big n := lazymatch n with S _ => let b := eval vm_compute in (Nat.leb 200 n) in lazymatch b with true => idtac end end.
Local Ltac sbl_pose_in H :=
  (let T := type of H in let T' := eval hnf in T in change T' in H);
  repeat match type of H with
  | context [repeat ?b ?n] => sbl_is_big n; let z := fresh "sblz" in pose (z := repeat b n); change (repeat b n) with z in H
  | context [CB ?n _] => sbl_is_big n; let x := fresh "sblv" in pose (x := n); change n with x in H
  end.
Local Ltac sbl_subst_all :=
  repeat match goal with
  | z := repeat _ ?n |- _ => sbl_is_big n; subst z
  | x := ?n |- _ => sbl_is_big n; subst x
  end.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Local Ltac at_nodeA_solve_nr :=
  at_nodeA_red; split_spine;
  first [ reflexivity | assumption | exact I
        | lazymatch goal with |- _ = _ \/ _ = _ => first [left; reflexivity | right; reflexivity] end
        | symmetry; apply Z_to_bv_bv_unsigned
        | lazymatch goal with
          | |- wr_at ?segs ?m ?A ?n =>
              match goal with H : rw_cells segs m A ?cs |- _ =>
                apply (rw_cells_wr_at segs m A cs n H); cbn [cells_size csize]; lia end
          | |- bytes_at ?segs ?m ?A ?bs =>
              match goal with
              | H : rw_cells segs m A ?cs |- _ =>
                apply (bytes_at_ext segs m A _ bs (rw_cells_bytes_at segs m A cs H));
                cbn [cells_bytes cbytes]; rewrite ?app_nil_r; reflexivity
              | H : ro_cells segs m A ?cs |- _ =>
                apply (bytes_at_ext segs m A _ bs (ro_cells_bytes_at segs m A cs H));
                cbn [cells_bytes cbytes]; rewrite ?app_nil_r; reflexivity
              end
          | |- _ /\ _ => split; at_nodeA_solve
          end
        | idtac ].
Section GlueFo.
  Context {rc : runConstT} {tlsI : ABase.atlsT}.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GSL : gia_stdio_laws GIOA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  #[local] Abbreviation eqb := (ho_eqb HO).
  (* [comment removed for export] *)
  Hypothesis MALLOC : malloc_stmt_o HO GIOA.
  Hypothesis TPFO : forall L ra trC, tp_fopen TP L ra trC -> In [AMALLOC_PC; 0x99bd0] (al_U L).

  (* [comment removed for export] *)
  #[local] Notation fopen_finishA := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_foKitA.fopen_finishA HO FO GIOA fflagA GL GSL HAL EQB).
  #[local] Notation robjA_factsA := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_foKitA.robjA_factsA FO GIOA fflagA GL).
  #[local] Notation live_block_factsA := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_foKitA.live_block_factsA FO GIOA fflagA GL).
  #[local] Notation GIOA_errno_step := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_foKitA.GIOA_errno_step FO GIOA fflagA GL GSL).

  Definition fopen_o_proofA__stmt : Prop := fopen_stmt_o HO GIOA TP.
  Section Sz1.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL trC lo NAME MODE name md wr : ltac2:(SecDiet.SzSec.tyM 'fopen_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fopen_o_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using EQB GL GSL HAL MALLOC TPFO. pin_using (fun (EQB GL GSL HAL MALLOC TPFO : unit) => tt).
 intros SPO UC TPF -> -> HNAME NNUL NLEN NOK NRO HMODE MLIT MRO.
 (* [comment removed for export] *)
 assert (NLENZ : (1 <= Z.of_nat (length name) <= 4095)%Z) by (clear - NLEN; lia). clear NLEN.
    pose proof SPO as (_ & _ & _ & _ & _ & _ & _ & SPAL & (RSTKF & _ & RIMGSH & _)).
    pose proof (spo_factsA GIOA GSL _ _ _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & _ & ENV & LOA & LOB & SPT & TOP47 & Etp & RSTK & RIMG & RTLS & KLO & GLO).
    (* [comment removed for export] *)
    destruct (gs_ssp _ GSL L) as [canary SSPL]. pose proof (SSPL _ _ _ _ _ _ G) as SSP.
    subst tp. unfold STDIO_STACK in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (@ATOP_lo rc) as ATL. pose proof (@ATOP_hi rc) as ATH.
    pose proof (@atp_range rc tlsI) as (_ & TPlo & TPhi & TPimg). pose proof (@ATPv_sh rc tlsI) as TPsh.
    assert (ETP : bv_unsigned (Z_to_bv 64 ATP : word) = ATP) by (apply unsigned_lit; unfold ATP; lia).
    destruct (mode_lit_factsA wr MODE md MLIT) as (slack & ROMD & MDR & NONUL & PAD & M0 & M0W & FMV & NOPLUS & NOE & MGLOB).
    pose proof (bytes_at_bound _ _ _ _ HNAME) as NB. rewrite length_app in NB. cbn [length] in NB.
    pose proof (bytes_at_bound _ _ _ _ HMODE) as MB. rewrite length_app in MB. cbn [length] in MB.
    assert (MDL : (1 <= length md <= 2)%nat) by (unfold mode_lit in MLIT; destruct wr; [destruct MLIT as [[_ ->]|[_ ->]] | destruct MLIT as [_ ->]]; cbn [length]; (keep_hyps rc sp NAME MODE name slack; lia)).
    destruct (robjA_factsA L RNG s CL FB FL m NAME (Z.of_nat (length name) + 1) lo G NRO ltac:(lia) LOA) as (N0 & NLO & SONAME & RGNAME).
    destruct (robjA_factsA L RNG s CL FB FL m MODE (Z.of_nat (length md) + 1) lo G MRO ltac:(lia) LOA) as (MD0 & MDLO & SOMODE & RGMODE).
    pose proof (gs_rodata _ GSL _ _ _ _ _ _ _ STR_RWA (STR_RWA + 4) G RIMG RIMGSH ltac:(left; unfold STR_RWA; lia) ltac:(lia)) as SORWA.
    destruct (gs_errno _ GSL _ _ _ _ _ _ _ G) as [errv ERR].
    assert (RERR : rng RNG (ATP + -164) 4) by (eapply rng_sub'; [exact RTLS | unfold ATP; lia]).
    assert (IESTP : iesafe [(ATP + -164, ATP + -160)]) by (unfold iesafe, ATP; cbn [disjoint_from]; repeat split; lia).
    assert (APWTP : appW [(ATP + -164, ATP + -160)]) by (constructor; [cbn [fst snd]; unfold KLOW, KHIGH, ATP; lia | constructor]).
    unfold s_fopen, Stdio.fopen.
    remember (Z_to_bv 64 (bv_unsigned sp + -2144) : word) as spm eqn:Espm.
    assert (Hspm : bv_unsigned spm = bv_unsigned sp + -2144) by (rewrite Espm; apply unsigned_lit; lia).
    assert (TPRM : ATP = 0x5e15b8) by (unfold ATP in *; lia).
    assert (TPLOM : ATP + -160 <= lo) by (unfold ATP in *; lia).
    assert (TP200M : 200 <= ATP) by (unfold ATP in *; lia).
    (* [comment removed for export] *)
    set (Qn := fun (r : sret) (s' : PS) (ms' : machine_state) => s' = s /\
      match r with
      | SErr e => 1 <= e <= 4095 /\ exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
          ms' = MS (mkR ra sp gp (Z_to_bv 64 ATP) t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (ret_pc ra) fc None m' (seg_rom asegs)
          /\ munch [(lo, bv_unsigned sp); (ATP + -164, ATP + -160)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
          /\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' (ATP + -164) [C4 (Z_to_bv 64 e)]
      | SVal fd => 3 <= fd <= 4096 /\ exists (x19 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' sv2 : word) (j0 : list byte) (m2 : mem),
          ms' = MS (mkR (Z_to_bv 64 0x99bd0) (Z_to_bv 64 (bv_unsigned spm + -96)) gp (Z_to_bv 64 ATP) t0' t1' t2' (Z_to_bv 64 MODE) (Z_to_bv 64 fd)
                       (Z_to_bv 64 1264) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 MODE) (Z_to_bv 64 ssp_guard) s4 s5 (Z_to_bv 64 (bv_unsigned sp + -2136))
                       s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (Z_to_bv 64 0x56178) fc None m2 (seg_rom asegs)
          /\ rw_cells asegs m2 (bv_unsigned spm + -32) [C8 (Z_to_bv 64 NAME); C8 (Z_to_bv 64 MODE); C8 sp; C8 (Z_to_bv 64 0x49778)]
          /\ rw_cells asegs m2 (bv_unsigned spm + -96) [CB 16 j0; C8 canary; C8 x19; C8 sv2; C8 (Z_to_bv 64 fd); C8 (Z_to_bv 64 MODE); C8 (Z_to_bv 64 0x9a858)]
          /\ rw_cells asegs m2 (ATP + -164) [C4 errv]
          /\ ssp_cells m2 canary
          /\ munch [(lo, bv_unsigned sp); (ATP + -164, ATP + -160)] m m2 /\ wmono asegs m m2 /\ mem_inv asegs m2
          /\ stk asegs m2 lo (bv_unsigned spm + -96)
          /\ stk asegs m2 (bv_unsigned spm) (bv_unsigned sp + -64)
          /\ rw_cells asegs m2 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      end).
    eapply implMG_bind with (Q1 := fun r s' RNG' ms' => RNG' = RNG /\ Qn r s' ms').
    { apply implAM_implMG. apply implAM_sys; [destruct wr; exact I|].
      (* [comment removed for export] *)
      eapply evtF_cut.
      { unfold FOPEN_ENTRY.
        eapply (fopen_i_pre RNG ra sp gp (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 (Z_to_bv 64 NAME) (Z_to_bv 64 MODE) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                  F fc m lo name [] md []);
          rewrite ?(unsigned_lit NAME), ?(unsigned_lit MODE) by (keep_hyps rc sp L lo NAME MODE name md slack LOB SPHI N0 NLO MDR; lia); rewrite ?length_app; cbn [length];
          first [ exact MI | exact ST | exact KLO | exact ENV | exact HNAME | exact HMODE | exact NNUL | exact NONUL | exact SONAME | exact SOMODE
                | exact RIMG | exact RSTK | exact RGNAME | exact RGMODE | (keep_hyps rc sp lo NAME MODE name md slack LOB N0 NLO MDLO; lia) | (left; lia) ]. }
      cbv beta. intros ms0 MID. unfold fopen_i_mid in MID.
      sbl_pose_in MID. destruct MID as (u0 & u1 & u2 & x12 & x13 & x14 & x15 & x16 & x17 & x19 & u3 & u4 & u5 & u6 & m0 & -> & MU0 & WM0 & MI0 & ST0 & STM0 & FR0). sbl_subst_all.
      rewrite <- Espm. rewrite <- Hspm in ST0, STM0.
      (* [comment removed for export] *)
      assert (ENV0 : icptenv m0) by (eapply icptenv_transport; [exact ENV | exact MU0 | exact WM0 | apply iesafe_one_high; unfold KHIGH in KLO; lia]).
      assert (APW0 : appW [(bv_unsigned sp + -2224, bv_unsigned sp)]) by (apply appW_one_high; lia).
      assert (SORWA0 : sobj RNG m0 STR_RWA (STR_RWA + 4)) by (eapply sobj_transport; [exact SORWA | exact MU0 | exact WM0 | exact APW0]).
      assert (SOMODE0 : sobj RNG m0 MODE (MODE + (Z.of_nat (length md) + 1))) by (eapply sobj_transport; [exact SOMODE | exact MU0 | exact WM0 | exact APW0]).
      assert (HNAME0 : bytes_at asegs m0 NAME (name ++ [Z_to_bv 8 0])).
      { eapply bytes_at_transport; [exact HNAME | exact MU0 |]. cbn [disjoint_from]. rewrite length_app. cbn [length]. lia. }
      assert (ERR0 : rw_cells asegs m0 (ATP + -164) [C4 errv]).
      { eapply rw_cells_transport; [exact ERR | exact MU0 | exact WM0 |]. cbn [disjoint_from cells_size csize Nat.add]. unfold ATP in *. lia. }
      assert (SSP0 : ssp_cells m0 canary).
      { destruct SSP as [GOT GUARD]. split; (eapply rw_cells_transport; [eassumption | exact MU0 | exact WM0 | unfold got_ssp, ssp_guard; cbn [disjoint_from cells_size csize Nat.add]; lia]). }
      assert (RSTKM : rng RNG lo (bv_unsigned spm - lo)) by (eapply rng_sub'; [exact RSTK | lia]).
      (* [comment removed for export] *)
      eapply evtF_cut.
      { eapply (fopen_S1 RNG (Z_to_bv 64 0x49778) spm gp (Z_to_bv 64 ATP) sp (Z_to_bv 64 MODE) (Z_to_bv 64 NAME) x19 s4 s5 (Z_to_bv 64 (bv_unsigned sp + -2136)) s7 s8 s9 s10 s11 F fc)
          with (lo := lo) (NAME := NAME) (MODE := MODE) (md := md) (slack := slack) (m := m0);
          rewrite ?ETP;
          first [ exact ROMD | exact ST0 | exact MI0 | exact MDR | exact NONUL | exact PAD | exact M0 | exact KLO | exact ENV0 | exact SORWA0 | exact SOMODE0
                | exact RIMG | exact RERR | exact IESTP | exact APWTP | exact RSTKM | exact TPRM | exact TPLOM | exact GLO | lia
                | match goal with |- ?g => idtac "S1 side:" g end ]. }
      cbv beta. intros ms1 PO1. unfold fopen_S1_post in PO1.
      sbl_pose_in PO1. destruct PO1 as (x1 & v0 & v1 & v2 & b4 & b5 & b6 & v3 & v4 & v5 & v6 & m1 & -> & FR1 & MU1 & WM1 & MI1 & ST1). sbl_subst_all.
      assert (HNAME1 : bytes_at asegs m1 NAME (name ++ [Z_to_bv 8 0])).
      { eapply bytes_at_transport; [exact HNAME0 | exact MU1 |]. cbn [disjoint_from]. rewrite length_app. cbn [length]. lia. }
      assert (ERR1 : rw_cells asegs m1 (ATP + -164) [C4 errv]).
      { eapply rw_cells_transport; [exact ERR0 | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
      assert (SSP1 : ssp_cells m1 canary).
      { destruct SSP0 as [GOT0 GUARD0]. split; (eapply rw_cells_transport; [eassumption | exact MU1 | exact WM1 | unfold got_ssp, ssp_guard; cbn [disjoint_from cells_size csize Nat.add]; lia]). }
      step_ecall. split.
      { destruct wr; cbn [open_name_ok] in NOK; rewrite FMV; at_nodeA_solve_nr.
        all: try (change (to_bytes (map bv_unsigned name)) with (to_bytes (of_bytes name)); rewrite to_of_bytes).
        all: first [ exact NNUL | exact NOK | exact (proj1 NOK) | exact (proj2 NOK)
                   | rewrite unsigned_lit by lia; exact HNAME1 | rewrite unsigned_lit by lia; exact RGNAME
                   | lazymatch goal with |- Z.ldiff _ _ = _ => vm_compute; reflexivity end
                   | match goal with |- ?g => idtac "ATNODE:" g end ]. }
      intros rsp a Hdec.
      assert (HD : match a with SErr e => rsp = efferr e /\ 1 <= e <= 4095 | SVal v => rsp = eff0 (Z_to_bv 64 v) /\ 3 <= v <= 4096 end).
      { assert (Hdec' : dec_open rsp = Some a) by (destruct wr; exact Hdec).
        unfold dec_open in Hdec'. apply dec_plain_Some in Hdec'. destruct a as [e|v]; [exact Hdec'|].
        sbl_pose_in Hdec'. destruct Hdec' as (E & OK & R'). sbl_subst_all. split; [exact E|]. apply andb_prop in OK. destruct OK as [O1 O2]. apply Z.leb_le in O1. apply Z.leb_le in O2. lia. }
      clear Hdec.
      (* [comment removed for export] *)
      assert (KEEPM : forall mm, munch [(lo, bv_unsigned spm); (ATP + -164, ATP + -160)] m0 mm -> wmono asegs m0 mm ->
                stk asegs mm (bv_unsigned spm) (bv_unsigned sp + -64)
                /\ rw_cells asegs mm (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
                /\ munch [(lo, bv_unsigned sp); (ATP + -164, ATP + -160)] m mm /\ wmono asegs m mm).
      { intros mm MUm WMm.
        split; [eapply stk_transport_disjoint; [exact STM0 | exact MUm | exact WMm |]; cbn [disjoint_from]; lia|].
        split; [eapply rw_cells_transport; [exact FR0 | exact MUm | exact WMm |]; cbn [disjoint_from cells_size csize Nat.add]; lia|].
        split; [| exact (wmono_trans asegs _ _ _ WM0 WMm)].
        eapply munch_trans; [eapply munch_weaken; [| exact MU0] | eapply munch_weaken; [| exact MUm]]; unfold sub_fp; cbn [outside]; intros x Hx; (keep_hyps rc tlsI sp lo NAME MODE name md slack x LOB Hx spm Hspm; lia). }
      destruct a as [e|fd].
      - (* [comment removed for export] *)
        destruct HD as [-> HE]. unfold efferr. sys_nret.
        eapply evtF_cut.
        { eapply (fopen_S2_fail RNG (Z_to_bv 64 0x49778) spm gp (Z_to_bv 64 ATP) sp (Z_to_bv 64 MODE) (Z_to_bv 64 NAME) x19 s4 s5 (Z_to_bv 64 (bv_unsigned sp + -2136)) s7 s8 s9 s10 s11 F fc)
            with (lo := lo) (NAME := NAME) (MODE := MODE) (md := md) (slack := slack) (m := m0) (e := e) (errv := errv);
            rewrite ?ETP;
            first [ exact FR1 | exact ERR1 | exact HE | exact ST1 | exact MI1 | exact MU1 | exact WM1 | exact KLO | exact ENV0 | exact SORWA0 | exact SOMODE0
                  | exact RIMG | exact RERR | exact IESTP | exact APWTP | exact RSTKM | exact TPRM | exact TPLOM | exact TP200M | exact GLO | lia
                  | match goal with |- ?g => idtac "S2F side:" g end ]. }
        cbv beta. intros ms2 PO2.
        sbl_pose_in PO2. destruct PO2 as (w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & m2 & -> & MU2 & WM2 & MI2 & ST2 & ERR2). sbl_subst_all.
        rewrite ETP in MU2, ERR2.
        destruct (KEEPM m2 MU2 WM2) as (STM2 & FR2 & MU02 & WM02).
        replace (ret_pc (Z_to_bv 64 0x49778)) with (Z_to_bv 64 0x49778 : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
        rewrite Hspm in ST2, STM2. rewrite Espm.
        eapply evtF_mono.
        { eapply (fopen_i_post RNG) with (lo := lo) (m := m2);
            first [ exact MI2 | exact ST2 | exact STM2 | exact FR2 | (eapply rng_sub'; [exact RSTK | lia]) | lia
                  | match goal with |- ?g => idtac "IPOST side:" g end ]. }
        cbv beta. intros ms3 [-> ST3].
        split; [reflexivity|]. split; [exact HE|].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [reflexivity|]. split; [exact MU02|]. split; [exact WM02|]. split; [exact MI2|]. split; [exact ST3 | exact ERR2].
      - (* [comment removed for export] *)
        destruct HD as [-> HFD]. unfold eff0. sys_nret.
        eapply evtF_mono.
        { eapply (fopen_S2_ok RNG (Z_to_bv 64 0x49778) spm gp (Z_to_bv 64 ATP) sp (Z_to_bv 64 MODE) (Z_to_bv 64 NAME) x19 s4 s5 (Z_to_bv 64 (bv_unsigned sp + -2136)) s7 s8 s9 s10 s11 F fc)
            with (lo := lo) (NAME := NAME) (MODE := MODE) (md := md) (slack := slack) (m := m0) (fd := fd) (canary := canary) (errv := errv);
            rewrite ?ETP;
            first [ exact ROMD | exact FR1 | exact ERR1 | exact SSP1 | exact HFD | exact ST1 | exact MI1 | exact MU1 | exact WM1
                  | exact MDR | exact NONUL | exact PAD | exact M0 | exact KLO | exact ENV0 | exact SORWA0 | exact SOMODE0
                  | exact RIMG | exact RERR | exact IESTP | exact APWTP | exact RSTKM | exact TPRM | exact TPLOM | exact TP200M | exact GLO | (keep_hyps rc sp lo NAME MODE name md slack spm LOB Hspm L SPT TOP47 SPHI N0 NLO; lia)
                  | (destruct wr; rewrite FMV; [right | left]; reflexivity)
                  | match goal with |- ?g => idtac "S2OK side:" g end ]. }
        cbv beta. intros ms2 PO2. unfold fopen_S2_post in PO2.
        sbl_pose_in PO2. destruct PO2 as (w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & sv2 & j0 & m2 & -> & FRO2 & FRI2 & ERR2 & SSP2 & MU2 & WM2 & MI2 & ST2). sbl_subst_all.
        rewrite ETP in MU2, ERR2.
        destruct (KEEPM m2 MU2 WM2) as (STM2 & FR2 & MU02 & WM02).
        split; [reflexivity|]. split; [exact HFD|].
        exists x19, w0, w1, w2, c1, c2, c3, c4, c5, c6, c7, w3, w4, w5, w6, sv2, j0, m2.
        split; [reflexivity|]. split; [exact FRO2|]. split; [exact FRI2|]. split; [exact ERR2|]. split; [exact SSP2|].
        split; [exact MU02|]. split; [exact WM02|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact STM2 | exact FR2]. }
    cbv beta. intros r s' RNG' ms' [-> QN]. unfold Qn in QN. clear Qn. destruct QN as [-> QN].
    destruct r as [e|fd].
    - (* [comment removed for export] *)
      destruct QN as (HE & w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & m' & -> & MU' & WM' & MI' & ST' & ERR').
      unfold set_errno. apply implMG_upd_lc. apply implMG_ret. apply evtF_done.
      split; [apply fp_le_refl|].
      eexists _, m'. split; [unfold hpost_regs; repeat eexists; reflexivity|]. split; [reflexivity|].
      split; [exact MI'|]. split; [exact ST'|].
      destruct (GIOA_errno_step L RNG s CL FB FL m m' _ (bv_unsigned sp) (set_errno_lc e (ps_libc s)) (Z_to_bv 64 e) G MU' WM') as [G' AG'];
        [ apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_cons; [right; cbn [fst snd]; lia | apply Forall_nil]]
        | lia | exact ERR' | reflexivity | reflexivity | reflexivity | ].
      split; [exact AG'|]. split; [reflexivity|]. split; [exact G'|].
      cbn [ps_libc set_libc set_errno_lc lc_errno]. split; [exact ERR' | lia].
    - (* [comment removed for export] *)
      destruct QN as (HFD & x19 & w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & sv2 & j0 & m2 & -> & FRO2 & FRI2 & ERR2 & SSP2 & MU2 & WM2 & MI2 & ST2 & STM2 & FR2).
      destruct (GIOA_errno_step L RNG s CL FB FL m m2 _ (bv_unsigned sp) (ps_libc s) errv G MU2 WM2) as [G2 AG2];
        [ apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_cons; [right; cbn [fst snd]; lia | apply Forall_nil]]
        | lia | exact ERR2 | reflexivity | reflexivity | reflexivity | ].
      rewrite set_libc_same in G2.
      remember (Z_to_bv 64 (bv_unsigned spm + -96) : word) as spc eqn:Espc.
      assert (Hspc : bv_unsigned spc = bv_unsigned spm + -96) by (rewrite Espc; apply unsigned_lit; lia).
      assert (EMD : bv_unsigned (Z_to_bv 64 MODE : word) = MODE) by (apply unsigned_lit; lia).
      assert (ERA : bv_unsigned (Z_to_bv 64 0x99bd0 : word) = 0x99bd0) by (apply unsigned_lit; lia).
      eapply implMG_bind.
      { eapply (MALLOC (Z_to_bv 64 0x99bd0) spc gp (Z_to_bv 64 ATP)) with (L := L) (CL := CL) (FB := FB) (FL := FL) (lo := lo) (n := FILE_ALLOC).
        - split; [exact G2|]. split; [rewrite Hspc; exact ST2|]. split; [exact LOA|]. split; [unfold MALLOC_STACK; lia|].
          split; [split; [lia | exact TOP47]|]. split; [exact MI2|]. split; [reflexivity|].
          split; [rewrite Hspc, Hspm; clear - SPAL; Z.div_mod_to_equations; lia|].
          split; [exact RSTKF|]. split; [exact RIMG|]. split; [exact RIMGSH | exact RTLS].
        - reflexivity.
        - unfold FILE_ALLOC. lia.
        - unfold unw_okA. rewrite EMD, ERA. split; [| unfold AMALLOC_PC; lia].
          exists []. left. split; [lia|]. split; [apply uc_stop; intros (X & _); lia|]. split; [cbn [length]; lia|].
          split; [exact (TPFO _ _ _ TPF) | exact RSTKF]. }
      cbv beta. intros po sM RNG3 ms3 (FP3 & a0v & m3 & REGS & OF3 & MI3 & ST3 & AG3 & RES).
      destruct po as [q|]; [| destruct RES].
      sbl_pose_in RES. destruct RES as (A & junk & -> & G3 & BLK). sbl_subst_all.
      unfold hpost_regs in REGS. sbl_pose_in REGS. destruct REGS as (y0 & y1 & y2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y3 & y4 & y5 & y6 & ->). sbl_subst_all.
      replace (ret_pc (Z_to_bv 64 0x99bd0)) with (Z_to_bv 64 0x99bd0 : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
      cbn beta iota.
      (* [comment removed for export] *)
      assert (FRO3 : rw_cells asegs m3 (bv_unsigned spm + -32) [C8 (Z_to_bv 64 NAME); C8 (Z_to_bv 64 MODE); C8 sp; C8 (Z_to_bv 64 0x49778)])
        by (eapply keeps_rw_cells_stack; [exact AG3 | exact FRO2 | lia]).
      assert (FRI3 : rw_cells asegs m3 (bv_unsigned spm + -96) [CB 16 j0; C8 canary; C8 x19; C8 sv2; C8 (Z_to_bv 64 fd); C8 (Z_to_bv 64 MODE); C8 (Z_to_bv 64 0x9a858)])
        by (eapply keeps_rw_cells_stack; [exact AG3 | exact FRI2 | lia]).
      assert (STM3 : stk asegs m3 (bv_unsigned spm) (bv_unsigned sp + -64)) by (eapply agrees_stk; [exact AG3 | exact STM2 | intros a Ha; left; lia]).
      assert (FR3 : rw_cells asegs m3 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
        by (eapply keeps_rw_cells_stack; [exact AG3 | exact FR2 | lia]).
      assert (AG03 : agrees_on (client_keeps FL CL (bv_unsigned sp)) m m3).
      { eapply agrees_on_trans; [exact AG2|]. eapply client_keeps_weaken; [exact AG3 | lia | intros a Ha; exact Ha | apply incl_refl]. }
      rewrite Hspc in ST3. rewrite Espc. clear Espc Hspc AG3.
      (* [comment removed for export] *)
      assert (RIMG3 : rng_aimg RNG3) by (eapply rng_fp_le; [exact FP3 | exact RIMG]).
      assert (RIMGSH3 : rng RNG3 0x7fffa000 779776) by (eapply rng_fp_le; [exact FP3 | exact RIMGSH]).
      assert (RSTK3 : rng RNG3 lo (bv_unsigned sp - lo)) by (eapply rng_fp_le; [exact FP3 | exact RSTK]).
      assert (RSTKM3 : rng RNG3 lo (bv_unsigned spm - lo)) by (eapply rng_sub'; [exact RSTK3 | lia]).
      assert (RERR3 : rng RNG3 (ATP + -164) 4) by (eapply rng_fp_le; [exact FP3 | exact RERR]).
      pose proof (fp_le_sobj _ _ _ _ _ FP3 SORWA) as SORWA3. pose proof (fp_le_sobj _ _ _ _ _ FP3 SOMODE) as SOMODE3e.
      pose proof (gs_env _ GSL _ _ _ _ _ _ _ G3) as ENV3.
      pose proof (SSPL _ _ _ _ _ _ G3) as SSP3.
      destruct (gs_libc _ GSL _ _ _ _ _ _ _ G3) as [THR3 NL3].
      pose proof (gs_stdio _ GSL _ _ _ _ _ _ _ G3) as SR3.
      pose proof SR3 as (SO3 & SOI3 & SE3 & SEI3 & SIN3 & U13 & U23 & U33 & OL3 & OH3 & FS3 & ND3).
      assert (SOMODE3 : sobj RNG3 m3 MODE (MODE + (Z.of_nat (length md) + 1))).
      { apply mobjA_sobj; [| lia]. eapply (gia_global_mobjA _ _ _ GL); [exact G3 | exact MGLOB | exact RIMG3 | exact RIMGSH3]. }
      destruct (live_block_factsA L RNG3 sM ((q, A, FILE_ALLOC) :: CL) FB FL m3 q A FILE_ALLOC lo G3 ltac:(left; reflexivity) LOA ltac:(unfold FILE_ALLOC; lia))
        as (A0 & _ & ALO & A3 & ATOPA & SOA & RGA).
      unfold FILE_ALLOC in ALO, ATOPA, SOA, RGA, BLK.
      pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G3) as BA3.
      (* [comment removed for export] *)
      assert (HDB : forall q1 Ah n1 FB', FB = (q1, Ah, n1) :: FB' ->
                n1 = FILE_ALLOC /\ 0x603000 <= Ah /\ Ah + 1264 <= lo /\ (A + 1264 <= Ah \/ Ah + 1264 <= A) /\ rng RNG3 Ah 1264
                /\ exists pvo : word, rw_cells asegs m3 (Ah + 104) [C8 pvo]).
      { intros q1 Ah n1 FB' E. subst FB.
        destruct (lc_files (ps_libc sM)) as [|[q1' f1] fs'] eqn:EFS; [exfalso; exact FS3|].
        cbn [files_R] in FS3. sbl_pose_in FS3. destruct FS3 as (Eq1 & -> & B0 & Bhi & FR1h & INV1 & REST1). sbl_subst_all.
        destruct (live_block_factsA L RNG3 sM ((q, A, FILE_ALLOC) :: CL) ((q1, Ah, FILE_ALLOC) :: FB') FL m3 q1 Ah FILE_ALLOC lo G3
                    ltac:(apply in_or_app; right; left; reflexivity) LOA ltac:(unfold FILE_ALLOC; lia)) as (_ & _ & K2 & K3 & _ & _ & K6).
        cbn [app blocks_apart] in BA3. destruct BA3 as [APc _].
        pose proof (proj1 (Forall_forall _ _) APc (q1, Ah, FILE_ALLOC) ltac:(apply in_or_app; right; left; reflexivity)) as AP.
        unfold apart, cb_addr, cb_size, FILE_ALLOC in AP, K2, K6. cbn [fst snd] in AP.
        split; [reflexivity|]. split; [exact K3|]. split; [exact K2|]. split; [lia|]. split; [exact K6|].
        exists (Z_to_bv 64 0). exact (FILE_R_prev_cell _ _ _ _ _ _ _ _ _ FR1h). }
      assert (HDR : 0 <= hd_addr FB /\ hd_addr FB + 232 < 2^63).
      { destruct FB as [|[[q1 Ah] n1] FB']; cbn [hd_addr]; [lia|]. destruct (HDB q1 Ah n1 FB' eq_refl) as (_ & K1 & K2 & _). lia. }
      (* [comment removed for export] *)
      eapply implMG_evtF.
      { eapply (fopen_S6 RNG3 (Z_to_bv 64 0x49778) spm gp (Z_to_bv 64 ATP) sp (Z_to_bv 64 MODE) (Z_to_bv 64 NAME) x19 s4 s5 (Z_to_bv 64 (bv_unsigned sp + -2136)) s7 s8 s9 s10 s11 F fc)
          with (lo := lo) (NAME := NAME) (MODE := MODE) (md := md) (slack := slack) (m := m) (P := A) (fd := fd) (canary := canary) (m2 := m3);
          rewrite ?ETP;
          first [ exact ROMD | exact BLK | exact FRO3 | exact FRI3 | exact SSP3 | exact HFD | exact ST3 | exact MI3 | exact ENV3 | exact SOMODE3 | exact SOA | exact RGA
                | exact MDR | exact NONUL | exact PAD | exact M0 | exact NOPLUS | exact NOE | exact KLO | exact ENV | exact SORWA3 | exact SOMODE3e
                | exact RIMG3 | exact RERR3 | exact IESTP | exact APWTP | exact RSTKM3 | exact TPRM | exact TPLOM | exact GLO | lia
                | match goal with |- ?g => idtac "S6 side:" g end ]. }
      cbv beta. intros ms4 PO4. unfold fopen_S6_post in PO4.
      sbl_pose_in PO4. destruct PO4 as (x1' & e0 & e1 & e2 & e4 & e5 & e6 & e7 & e8 & e9 & e10 & e11 & m4 & -> & FC4 & BLK4 & FRO4 & (sv2' & j0' & FRI4) & SSP4 & MU4 & WM4 & MI4 & ST4). sbl_subst_all.
      (* [comment removed for export] *)
      assert (THR4 : rw_cells asegs m4 0x601849 [C1 (Z_to_bv 8 0)]) by (eapply rw_cells_transport; [exact THR3 | exact MU4 | exact WM4 | cbn [disjoint_from cells_size csize Nat.add]; lia]).
      assert (NL4 : rw_cells asegs m4 NEED_LOCKS [C1 (Z_to_bv 8 0)]) by (unfold NEED_LOCKS; eapply rw_cells_transport; [exact NL3 | exact MU4 | exact WM4 | cbn [disjoint_from cells_size csize Nat.add]; lia]).
      assert (OL4 : rw_cells asegs m4 A_OFL_LOCK [C4 (Z_to_bv 64 0)]) by (unfold A_OFL_LOCK in *; eapply rw_cells_transport; [exact OL3 | exact MU4 | exact WM4 | cbn [disjoint_from cells_size csize Nat.add]; lia]).
      assert (OH4 : rw_cells asegs m4 A_OFL_HEAD [C8 (Z_to_bv 64 (hd_addr FB))]) by (unfold A_OFL_HEAD in *; eapply rw_cells_transport; [exact OH3 | exact MU4 | exact WM4 | cbn [disjoint_from cells_size csize Nat.add]; lia]).
      assert (HDF : hd_addr FB = 0 \/ (hd_addr FB <> 0 /\ (exists pvo : word, rw_cells asegs m4 (hd_addr FB + 104) [C8 pvo])
                     /\ hd_addr FB + 232 <= lo /\ (hd_addr FB + 232 <= A \/ A + 1264 <= hd_addr FB) /\ (hd_addr FB + 232 <= 0x10000 \/ 0x603000 <= hd_addr FB))).
      { destruct FB as [|[[q1 Ah] n1] FB']; [left; reflexivity | right]. cbn [hd_addr].
        destruct (HDB q1 Ah n1 FB' eq_refl) as (_ & K1 & K2 & K3 & _ & (pvo & PVC)).
        split; [lia|]. split; [| lia].
        exists pvo. eapply rw_cells_transport; [exact PVC | exact MU4 | exact WM4 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
      assert (RHD : hd_addr FB <> 0 -> rng RNG3 (hd_addr FB + 104) 8).
      { destruct FB as [|[[q1 Ah] n1] FB']; cbn [hd_addr]; [intros X; exfalso; exact (X eq_refl)|]. intros _.
        destruct (HDB q1 Ah n1 FB' eq_refl) as (_ & _ & _ & _ & K5 & _). eapply rng_sub'; [exact K5 | lia]. }
      assert (RPA : rng RNG3 A 232) by (eapply rng_sub'; [exact RGA | lia]).
      (* [comment removed for export] *)
      lazymatch goal with |- implMG _ _ _ ?Q _ => set (QF := Q) end.
      assert (FIN : forall (x1'' e0' e1' e2' a0' a1' a2' a3' e4' e5' e6' e7' e8' e9' e10' e11' : word),
        evtF asegs RNG3 (QF (Some q) (set_libc (set_files ((q, fdopen_file fd wr) :: lc_files (ps_libc sM)) (ps_libc sM)) sM) RNG3)
          (MS (mkR x1'' (Z_to_bv 64 (bv_unsigned spm + -96)) gp (Z_to_bv 64 ATP) e0' e1' e2' (Z_to_bv 64 A) (Z_to_bv 64 fd)
                   a0' a1' a2' a3' e4' e5' e6' e7' (Z_to_bv 64 MODE) (Z_to_bv 64 ssp_guard) s4 s5 (Z_to_bv 64 (bv_unsigned sp + -2136)) s7 s8 s9 s10 s11 e8' e9' e10' e11')
              F (Z_to_bv 64 0x99ce4) fc None m4 (seg_rom asegs))).
      { intros. subst QF. cbv beta.
        eapply evtF_cut.
        { eapply (fopen_S7 RNG3 (Z_to_bv 64 0x49778) spm gp (Z_to_bv 64 ATP) sp (Z_to_bv 64 MODE) (Z_to_bv 64 NAME) x19 s4 s5 (Z_to_bv 64 (bv_unsigned sp + -2136)) s7 s8 s9 s10 s11 F fc)
            with (lo := lo) (NAME := NAME) (MODE := MODE) (md := md) (slack := slack) (m := m) (hd := hd_addr FB) (m2 := m3)
                 (fl := if mode_m0 md =? 114 then 8 else 4) (P := A) (fd := fd) (canary := canary);
            rewrite ?ETP;
            first [ exact FC4 | exact BLK4 | exact FRO4 | exact FRI4 | exact SSP4 | exact THR4 | exact NL4 | exact OL4 | exact OH4 | exact HDF | exact RHD | exact RPA
                  | exact MU4 | exact WM4 | exact ST4 | exact MI4 | exact HFD
                  | exact KLO | exact ENV | exact SORWA3 | exact SOMODE3e | exact RIMG3 | exact RERR3 | exact IESTP | exact APWTP | exact RSTKM3 | exact TPRM | exact TPLOM | exact GLO | (keep_hyps rc sp lo NAME MODE name md slack spm LOB Hspm L SPT TOP47 SPHI N0 NLO A A0 A3 ALO hptr FB HDR; lia)
                  | (unfold sub_fp; cbn [outside]; intros x Hx; (keep_hyps rc hptr sp FB lo NAME MODE name md slack spm A x Hx; lia))
                  | match goal with |- ?g => idtac "S7 side:" g end ]. }
        cbv beta. intros ms7 PO7. unfold fopen_S7_post in PO7.
        sbl_pose_in PO7. destruct PO7 as (f0' & f1' & f2' & g1 & g2 & g3 & g4 & g5 & g6 & g7 & f3' & f4' & f5' & f6' & m7 & -> & FC7 & BLK7 & OL7 & OH7 & OLDP7 & SSP7 & MU7 & WM7 & MI7 & ST7). sbl_subst_all.
        (* [comment removed for export] *)
        assert (DJ7 : forall a n, bv_unsigned spm <= a -> 0 <= n -> disjoint_from [(lo, bv_unsigned spm); (A, A + 232); (A_OFL_HEAD, A_OFL_HEAD + 8); (hd_addr FB + 104, hd_addr FB + (if hd_addr FB =? 0 then 104 else 112))] a n).
        { intros a n Ha Hn. unfold A_OFL_HEAD. cbn [disjoint_from]. destruct HDF as [E | (NE & _ & K1 & _)].
          - rewrite E. cbn. lia.
          - replace (hd_addr FB =? 0) with false by (symmetry; apply Z.eqb_neq; exact NE). lia. }
        assert (STM7 : stk asegs m7 (bv_unsigned spm) (bv_unsigned sp + -64)).
        { eapply stk_transport_disjoint; [exact STM3 | exact MU7 | exact WM7 | apply DJ7; lia]. }
        assert (FR7 : rw_cells asegs m7 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
        { eapply rw_cells_transport; [exact FR3 | exact MU7 | exact WM7 | apply DJ7; cbn [cells_size csize Nat.add]; lia]. }
        replace (ret_pc (Z_to_bv 64 0x49778)) with (Z_to_bv 64 0x49778 : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
        rewrite Hspm in ST7, STM7. rewrite Espm.
        eapply evtF_mono.
        { eapply (fopen_i_post RNG3) with (lo := lo) (m := m7);
            first [ exact MI7 | exact ST7 | exact STM7 | exact FR7 | (eapply rng_sub'; [exact RSTK3 | lia]) | lia
                  | match goal with |- ?g => idtac "IPOST7 side:" g end ]. }
        cbv beta. intros ms8 [-> ST8].
        (* [comment removed for export] *)
        pose proof MU7 as MU37.
        assert (HWX : exists W', munch W' m3 m7
                  /\ Forall (fun iv : Z * Z => (ATOP + 4096 <= fst iv /\ snd iv <= bv_unsigned sp) \/ (fst iv = A /\ snd iv = A + 232) \/ (fst iv = A_OFL_HEAD /\ snd iv = A_OFL_HEAD + 8)
                                              \/ (FB <> [] /\ fst iv = hd_addr FB + 104 /\ snd iv = hd_addr FB + 112)) W').
        { revert MU37. destruct (Z.eqb_spec (hd_addr FB) 0) as [E|NE]; intros MU37.
          - exists [(lo, bv_unsigned spm); (A, A + 232); (A_OFL_HEAD, A_OFL_HEAD + 8)]. split.
            + eapply munch_weaken; [| exact MU37]. unfold sub_fp. intros x Ox. cbn [outside] in Ox |- *. sbl_pose_in Ox. destruct Ox as (O1 & O2 & O3 & _). sbl_subst_all.
              split; [exact O1|]. split; [exact O2|]. split; [exact O3|]. split; [lia | exact I].
            + apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [right; left; split; reflexivity|].
              apply Forall_cons; [right; right; left; split; reflexivity | apply Forall_nil].
          - exists [(lo, bv_unsigned spm); (A, A + 232); (A_OFL_HEAD, A_OFL_HEAD + 8); (hd_addr FB + 104, hd_addr FB + 112)]. split.
            + exact MU37.
            + apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [right; left; split; reflexivity|].
              apply Forall_cons; [right; right; left; split; reflexivity|]. apply Forall_cons; [| apply Forall_nil].
              right; right; right. cbn [fst snd]. split; [| split; reflexivity]. intros EFB. apply NE. rewrite EFB. reflexivity. }
        destruct HWX as (W' & MU7' & HW').
        assert (EFL7 : (if mode_m0 md =? 114 then 8 else 4) = (if wr then 4 else 8)) by (rewrite M0W; destruct wr; reflexivity).
        destruct (fopen_finishA L RNG3 sM CL FB FL m3 m7 W' q A fd wr _ (skipn 232 junk) (bv_unsigned sp) G3 MU7' WM7 HW' ltac:(lia) FC7 BLK7 OL7 OH7 OLDP7 EFL7 HFD) as [G7 AG7].
        split; [exact FP3|].
        eexists _, m7. split; [unfold hpost_regs; repeat eexists; reflexivity|].
        split; [destruct sM as [xh xl xo xt]; cbn [ps_outfile set_libc] in OF3 |- *; exact OF3|].
        split; [exact MI7|]. split; [exact ST8|].
        split; [eapply agrees_on_trans; [exact AG03 | exact AG7]|].
        exists A. split; [reflexivity | exact G7]. }
      destruct wr.
      + (* [comment removed for export] *)
        assert (EFL : (mode_m0 md =? 114) = false) by (rewrite M0W; reflexivity). rewrite EFL in FC4 |- *.
        apply implMG_bind_assoc. apply implMG_sysk; [exact I|].
        eapply evtF_cut.
        { eapply (fopen_br_w RNG3) with (sp := spm) (lo := lo) (NAME := NAME) (MODE := MODE) (md := md) (m := m) (fd := fd);
            rewrite ?ETP;
            first [ exact KLO | exact ENV | exact SORWA3 | exact SOMODE3e | exact RIMG3 | exact RERR3 | exact IESTP | exact APWTP | exact RSTKM3 | exact TPRM | lia
                  | match goal with |- ?g => idtac "BRW side:" g end ]. }
        cbv beta. intros ms5 ->.
        step_ecall. split. { at_nodeA_solve. }
        intros rsp a Hdec. unfold dec_ioctl in Hdec. apply dec_plain_Some in Hdec.
        destruct a as [e'|v]; [| destruct Hdec as (_ & X & _); discriminate X]. destruct Hdec as [-> HE'].
        cbn beta iota. apply implMG_retb. apply implMG_upd_lc. apply implMG_ret. unfold efferr. sys_nret.
        eapply evtF_cut.
        { eapply (fopen_ioctl_ret RNG3) with (sp := spm) (lo := lo) (NAME := NAME) (MODE := MODE) (md := md) (slack := slack) (m := m) (e := e');
            rewrite ?ETP;
            first [ exact HE' | exact KLO | exact ENV | exact SORWA3 | exact SOMODE3e | exact RIMG3 | exact RERR3 | exact IESTP | exact APWTP | exact RSTKM3 | exact TPRM | lia
                  | match goal with |- ?g => idtac "IOCTLRET side:" g end ]. }
        cbv beta. intros ms6 ->. apply FIN.
      + (* [comment removed for export] *)
        assert (EFL : (mode_m0 md =? 114) = true) by (rewrite M0W; reflexivity). rewrite EFL in FC4 |- *.
        apply implMG_retb. apply implMG_upd_lc. apply implMG_ret.
        eapply evtF_cut.
        { eapply (fopen_br_r RNG3) with (sp := spm) (lo := lo) (NAME := NAME) (MODE := MODE) (md := md) (m := m);
            rewrite ?ETP;
            first [ exact KLO | exact ENV | exact SORWA3 | exact SOMODE3e | exact RIMG3 | exact RERR3 | exact IESTP | exact APWTP | exact RSTKM3 | exact TPRM | lia
                  | match goal with |- ?g => idtac "BRR side:" g end ]. }
        cbv beta. intros ms5 ->. apply FIN.
  Qed.
  End Sz1.
  Theorem fopen_o_proofA : ltac:(let t := eval cbv delta [fopen_o_proofA__stmt] in fopen_o_proofA__stmt in exact t).
  Proof using EQB GL GSL HAL MALLOC TPFO. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL trC lo NAME MODE name md wr. ltac2:(SecDiet.SzSec.closeP 'fopen_o_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End GlueFo.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_lock.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.F_fmodeflags.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_fopen.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fopen__A3S.I_fopen.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_read__A3S.F_stdio_read.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioLawsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_foKitA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac sbl_is_big n := lazymatch n with S _ => let b := eval vm_compute in (Nat.leb 200 n) in lazymatch b with true => idtac end end.
Local Ltac sbl_pose_in H :=
  (let T := type of H in let T' := eval hnf in T in change T' in H);
  repeat match type of H with
  | context [repeat ?b ?n] => sbl_is_big n; let z := fresh "sblz" in pose (z := repeat b n); change (repeat b n) with z in H
  | context [CB ?n _] => sbl_is_big n; let x := fresh "sblv" in pose (x := n); change n with x in H
  end.
Local Ltac sbl_subst_all :=
  repeat match goal with
  | z := repeat _ ?n |- _ => sbl_is_big n; subst z
  | x := ?n |- _ => sbl_is_big n; subst x
  end.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section GlueFo.
  Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GSL : gia_stdio_laws GIOA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  #[local] Abbreviation eqb := (ho_eqb HO).
  (* [comment removed for export] *)
  Hypothesis MALLOC : malloc_stmt_o HO GIOA.
  Hypothesis TPFO : forall L ra trC, tp_fopen TP L ra trC -> In [AMALLOC_PC; 0x99fb4] (al_U L).

  (* [comment removed for export] *)
  #[local] Notation fopen_finishA := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_foKitA.TwB.fopen_finishA HO FO GIOA fflagA GL GSL HAL EQB).
  #[local] Notation robjA_factsA := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_foKitA.TwB.robjA_factsA FO GIOA fflagA GL).
  #[local] Notation live_block_factsA := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_foKitA.TwB.live_block_factsA FO GIOA fflagA GL).
  #[local] Notation GIOA_errno_step := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_foKitA.TwB.GIOA_errno_step FO GIOA fflagA GL GSL).

  Definition fopen_o_proofA__stmt : Prop := fopen_stmt_o HO GIOA TP.
  Section Sz1.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL trC lo NAME MODE name md wr : ltac2:(SecDiet.SzSec.tyM 'fopen_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fopen_o_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using EQB GL GSL HAL MALLOC TPFO. pin_using (fun (EQB GL GSL HAL MALLOC TPFO : unit) => tt).
 intros SPO UC TPF -> -> HNAME NNUL NLEN NOK NRO HMODE MLIT MRO.
 (* [comment removed for export] *)
 assert (NLENZ : (1 <= Z.of_nat (length name) <= 4095)%Z) by (clear - NLEN; lia). clear NLEN.
    pose proof SPO as (_ & _ & _ & _ & _ & _ & _ & SPAL & (RSTKF & _ & RIMGSH & _)).
    pose proof (spo_factsA GIOA GSL _ _ _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & _ & ENV & LOA & LOB & SPT & TOP47 & Etp & RSTK & RIMG & RTLS & KLO & GLO).
    (* [comment removed for export] *)
    destruct (gs_ssp _ GSL L) as [canary SSPL]. pose proof (SSPL _ _ _ _ _ _ G) as SSP.
    subst tp. unfold STDIO_STACK in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (@ATOP_lo rc) as ATL. pose proof (@ATOP_hi rc) as ATH.
    pose proof (@atp_range rc tlsI) as (_ & TPlo & TPhi & TPimg). pose proof (@ATPv_sh rc tlsI) as TPsh.
    assert (ETP : bv_unsigned (Z_to_bv 64 ATP : word) = ATP) by (apply unsigned_lit; unfold ATP; lia).
    destruct (mode_lit_factsA wr MODE md MLIT) as (slack & ROMD & MDR & NONUL & PAD & M0 & M0W & FMV & NOPLUS & NOE & MGLOB).
    pose proof (bytes_at_bound _ _ _ _ HNAME) as NB. rewrite length_app in NB. cbn [length] in NB.
    pose proof (bytes_at_bound _ _ _ _ HMODE) as MB. rewrite length_app in MB. cbn [length] in MB.
    assert (MDL : (1 <= length md <= 2)%nat) by (unfold mode_lit in MLIT; destruct wr; [destruct MLIT as [[_ ->]|[_ ->]] | destruct MLIT as [_ ->]]; cbn [length]; lia).
    destruct (robjA_factsA L RNG s CL FB FL m NAME (Z.of_nat (length name) + 1) lo G NRO ltac:(lia) LOA) as (N0 & NLO & SONAME & RGNAME).
    destruct (robjA_factsA L RNG s CL FB FL m MODE (Z.of_nat (length md) + 1) lo G MRO ltac:(lia) LOA) as (MD0 & MDLO & SOMODE & RGMODE).
    pose proof (gs_rodata _ GSL _ _ _ _ _ _ _ STR_RWA (STR_RWA + 4) G RIMG RIMGSH ltac:(left; unfold STR_RWA; lia) ltac:(lia)) as SORWA.
    destruct (gs_errno _ GSL _ _ _ _ _ _ _ G) as [errv ERR].
    assert (RERR : rng RNG (ATP + -164) 4) by (eapply rng_sub'; [exact RTLS | unfold ATP; lia]).
    assert (IESTP : iesafe [(ATP + -164, ATP + -160)]) by (unfold iesafe, ATP; cbn [disjoint_from]; repeat split; lia).
    assert (APWTP : appW [(ATP + -164, ATP + -160)]) by (constructor; [cbn [fst snd]; unfold KLOW, KHIGH, ATP; lia | constructor]).
    unfold s_fopen, Stdio.fopen.
    remember (Z_to_bv 64 (bv_unsigned sp + -2144) : word) as spm eqn:Espm.
    assert (Hspm : bv_unsigned spm = bv_unsigned sp + -2144) by (rewrite Espm; apply unsigned_lit; lia).
    assert (TPRM : ATP = 0x5e19b8) by (unfold ATP in *; lia).
    assert (TPLOM : ATP + -160 <= lo) by (unfold ATP in *; lia).
    assert (TP200M : 200 <= ATP) by (unfold ATP in *; lia).
    (* [comment removed for export] *)
    set (Qn := fun (r : sret) (s' : PS) (ms' : machine_state) => s' = s /\
      match r with
      | SErr e => 1 <= e <= 4095 /\ exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
          ms' = MS (mkR ra sp gp (Z_to_bv 64 ATP) t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (ret_pc ra) fc None m' (seg_rom asegs)
          /\ munch [(lo, bv_unsigned sp); (ATP + -164, ATP + -160)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
          /\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' (ATP + -164) [C4 (Z_to_bv 64 e)]
      | SVal fd => 3 <= fd <= 4096 /\ exists (x19 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' sv2 : word) (j0 : list byte) (m2 : mem),
          ms' = MS (mkR (Z_to_bv 64 0x99fb4) (Z_to_bv 64 (bv_unsigned spm + -96)) gp (Z_to_bv 64 ATP) t0' t1' t2' (Z_to_bv 64 MODE) (Z_to_bv 64 fd)
                       (Z_to_bv 64 1264) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 MODE) (Z_to_bv 64 ssp_guard) s4 s5 (Z_to_bv 64 (bv_unsigned sp + -2136))
                       s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (Z_to_bv 64 0x561e0) fc None m2 (seg_rom asegs)
          /\ rw_cells asegs m2 (bv_unsigned spm + -32) [C8 (Z_to_bv 64 NAME); C8 (Z_to_bv 64 MODE); C8 sp; C8 (Z_to_bv 64 0x497e0)]
          /\ rw_cells asegs m2 (bv_unsigned spm + -96) [CB 16 j0; C8 canary; C8 x19; C8 sv2; C8 (Z_to_bv 64 fd); C8 (Z_to_bv 64 MODE); C8 (Z_to_bv 64 0x9ac3c)]
          /\ rw_cells asegs m2 (ATP + -164) [C4 errv]
          /\ ssp_cells m2 canary
          /\ munch [(lo, bv_unsigned sp); (ATP + -164, ATP + -160)] m m2 /\ wmono asegs m m2 /\ mem_inv asegs m2
          /\ stk asegs m2 lo (bv_unsigned spm + -96)
          /\ stk asegs m2 (bv_unsigned spm) (bv_unsigned sp + -64)
          /\ rw_cells asegs m2 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      end).
    eapply implMG_bind with (Q1 := fun r s' RNG' ms' => RNG' = RNG /\ Qn r s' ms').
    { apply implAM_implMG. apply implAM_sys; [destruct wr; exact I|].
      (* [comment removed for export] *)
      eapply evtF_cut.
      { unfold FOPEN_ENTRY.
        eapply (fopen_i_pre RNG ra sp gp (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 (Z_to_bv 64 NAME) (Z_to_bv 64 MODE) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                  F fc m lo name [] md []);
          rewrite ?(unsigned_lit NAME), ?(unsigned_lit MODE) by (keep_hyps rc sp L lo NAME MODE name md slack LOB SPHI N0 NLO MDR; lia); rewrite ?length_app; cbn [length];
          first [ exact MI | exact ST | exact KLO | exact ENV | exact HNAME | exact HMODE | exact NNUL | exact NONUL | exact SONAME | exact SOMODE
                | exact RIMG | exact RSTK | exact RGNAME | exact RGMODE | (keep_hyps rc sp lo NAME MODE name md slack LOB N0 NLO MDLO; lia) | (left; lia) ]. }
      cbv beta. intros ms0 MID. unfold fopen_i_mid in MID.
      sbl_pose_in MID. destruct MID as (u0 & u1 & u2 & x12 & x13 & x14 & x15 & x16 & x17 & x19 & u3 & u4 & u5 & u6 & m0 & -> & MU0 & WM0 & MI0 & ST0 & STM0 & FR0). sbl_subst_all.
      rewrite <- Espm. rewrite <- Hspm in ST0, STM0.
      (* [comment removed for export] *)
      assert (ENV0 : icptenv m0) by (eapply icptenv_transport; [exact ENV | exact MU0 | exact WM0 | apply iesafe_one_high; unfold KHIGH in KLO; lia]).
      assert (APW0 : appW [(bv_unsigned sp + -2224, bv_unsigned sp)]) by (apply appW_one_high; lia).
      assert (SORWA0 : sobj RNG m0 STR_RWA (STR_RWA + 4)) by (eapply sobj_transport; [exact SORWA | exact MU0 | exact WM0 | exact APW0]).
      assert (SOMODE0 : sobj RNG m0 MODE (MODE + (Z.of_nat (length md) + 1))) by (eapply sobj_transport; [exact SOMODE | exact MU0 | exact WM0 | exact APW0]).
      assert (HNAME0 : bytes_at asegs m0 NAME (name ++ [Z_to_bv 8 0])).
      { eapply bytes_at_transport; [exact HNAME | exact MU0 |]. cbn [disjoint_from]. rewrite length_app. cbn [length]. lia. }
      assert (ERR0 : rw_cells asegs m0 (ATP + -164) [C4 errv]).
      { eapply rw_cells_transport; [exact ERR | exact MU0 | exact WM0 |]. cbn [disjoint_from cells_size csize Nat.add]. unfold ATP in *. lia. }
      assert (SSP0 : ssp_cells m0 canary).
      { destruct SSP as [GOT GUARD]. split; (eapply rw_cells_transport; [eassumption | exact MU0 | exact WM0 | unfold got_ssp, ssp_guard; cbn [disjoint_from cells_size csize Nat.add]; lia]). }
      assert (RSTKM : rng RNG lo (bv_unsigned spm - lo)) by (eapply rng_sub'; [exact RSTK | lia]).
      (* [comment removed for export] *)
      eapply evtF_cut.
      { eapply (fopen_S1 RNG (Z_to_bv 64 0x497e0) spm gp (Z_to_bv 64 ATP) sp (Z_to_bv 64 MODE) (Z_to_bv 64 NAME) x19 s4 s5 (Z_to_bv 64 (bv_unsigned sp + -2136)) s7 s8 s9 s10 s11 F fc)
          with (lo := lo) (NAME := NAME) (MODE := MODE) (md := md) (slack := slack) (m := m0);
          rewrite ?ETP;
          first [ exact ROMD | exact ST0 | exact MI0 | exact MDR | exact NONUL | exact PAD | exact M0 | exact KLO | exact ENV0 | exact SORWA0 | exact SOMODE0
                | exact RIMG | exact RERR | exact IESTP | exact APWTP | exact RSTKM | exact TPRM | exact TPLOM | exact GLO | lia
                | match goal with |- ?g => idtac "S1 side:" g end ]. }
      cbv beta. intros ms1 PO1. unfold fopen_S1_post in PO1.
      sbl_pose_in PO1. destruct PO1 as (x1 & v0 & v1 & v2 & b4 & b5 & b6 & v3 & v4 & v5 & v6 & m1 & -> & FR1 & MU1 & WM1 & MI1 & ST1). sbl_subst_all.
      assert (HNAME1 : bytes_at asegs m1 NAME (name ++ [Z_to_bv 8 0])).
      { eapply bytes_at_transport; [exact HNAME0 | exact MU1 |]. cbn [disjoint_from]. rewrite length_app. cbn [length]. lia. }
      assert (ERR1 : rw_cells asegs m1 (ATP + -164) [C4 errv]).
      { eapply rw_cells_transport; [exact ERR0 | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
      assert (SSP1 : ssp_cells m1 canary).
      { destruct SSP0 as [GOT0 GUARD0]. split; (eapply rw_cells_transport; [eassumption | exact MU1 | exact WM1 | unfold got_ssp, ssp_guard; cbn [disjoint_from cells_size csize Nat.add]; lia]). }
      step_ecall. split.
      { destruct wr; cbn [open_name_ok] in NOK; rewrite FMV; at_nodeA_solve_nr.
        all: try (change (to_bytes (map bv_unsigned name)) with (to_bytes (of_bytes name)); rewrite to_of_bytes).
        all: first [ exact NNUL | exact NOK | exact (proj1 NOK) | exact (proj2 NOK)
                   | rewrite unsigned_lit by lia; exact HNAME1 | rewrite unsigned_lit by lia; exact RGNAME
                   | lazymatch goal with |- Z.ldiff _ _ = _ => vm_compute; reflexivity end
                   | match goal with |- ?g => idtac "ATNODE:" g end ]. }
      intros rsp a Hdec.
      assert (HD : match a with SErr e => rsp = efferr e /\ 1 <= e <= 4095 | SVal v => rsp = eff0 (Z_to_bv 64 v) /\ 3 <= v <= 4096 end).
      { assert (Hdec' : dec_open rsp = Some a) by (destruct wr; exact Hdec).
        unfold dec_open in Hdec'. apply dec_plain_Some in Hdec'. destruct a as [e|v]; [exact Hdec'|].
        sbl_pose_in Hdec'. destruct Hdec' as (E & OK & R'). sbl_subst_all. split; [exact E|]. apply andb_prop in OK. destruct OK as [O1 O2]. apply Z.leb_le in O1. apply Z.leb_le in O2. lia. }
      clear Hdec.
      (* [comment removed for export] *)
      assert (KEEPM : forall mm, munch [(lo, bv_unsigned spm); (ATP + -164, ATP + -160)] m0 mm -> wmono asegs m0 mm ->
                stk asegs mm (bv_unsigned spm) (bv_unsigned sp + -64)
                /\ rw_cells asegs mm (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
                /\ munch [(lo, bv_unsigned sp); (ATP + -164, ATP + -160)] m mm /\ wmono asegs m mm).
      { intros mm MUm WMm.
        split; [eapply stk_transport_disjoint; [exact STM0 | exact MUm | exact WMm |]; cbn [disjoint_from]; lia|].
        split; [eapply rw_cells_transport; [exact FR0 | exact MUm | exact WMm |]; cbn [disjoint_from cells_size csize Nat.add]; lia|].
        split; [| exact (wmono_trans asegs _ _ _ WM0 WMm)].
        eapply munch_trans; [eapply munch_weaken; [| exact MU0] | eapply munch_weaken; [| exact MUm]]; unfold sub_fp; cbn [outside]; intros x Hx; (keep_hyps rc tlsI sp lo NAME MODE name md slack x LOB Hx spm Hspm; lia). }
      destruct a as [e|fd].
      - (* [comment removed for export] *)
        destruct HD as [-> HE]. unfold efferr. sys_nret.
        eapply evtF_cut.
        { eapply (fopen_S2_fail RNG (Z_to_bv 64 0x497e0) spm gp (Z_to_bv 64 ATP) sp (Z_to_bv 64 MODE) (Z_to_bv 64 NAME) x19 s4 s5 (Z_to_bv 64 (bv_unsigned sp + -2136)) s7 s8 s9 s10 s11 F fc)
            with (lo := lo) (NAME := NAME) (MODE := MODE) (md := md) (slack := slack) (m := m0) (e := e) (errv := errv);
            rewrite ?ETP;
            first [ exact FR1 | exact ERR1 | exact HE | exact ST1 | exact MI1 | exact MU1 | exact WM1 | exact KLO | exact ENV0 | exact SORWA0 | exact SOMODE0
                  | exact RIMG | exact RERR | exact IESTP | exact APWTP | exact RSTKM | exact TPRM | exact TPLOM | exact TP200M | exact GLO | lia
                  | match goal with |- ?g => idtac "S2F side:" g end ]. }
        cbv beta. intros ms2 PO2.
        sbl_pose_in PO2. destruct PO2 as (w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & m2 & -> & MU2 & WM2 & MI2 & ST2 & ERR2). sbl_subst_all.
        rewrite ETP in MU2, ERR2.
        destruct (KEEPM m2 MU2 WM2) as (STM2 & FR2 & MU02 & WM02).
        replace (ret_pc (Z_to_bv 64 0x497e0)) with (Z_to_bv 64 0x497e0 : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
        rewrite Hspm in ST2, STM2. rewrite Espm.
        eapply evtF_mono.
        { eapply (fopen_i_post RNG) with (lo := lo) (m := m2);
            first [ exact MI2 | exact ST2 | exact STM2 | exact FR2 | (eapply rng_sub'; [exact RSTK | lia]) | lia
                  | match goal with |- ?g => idtac "IPOST side:" g end ]. }
        cbv beta. intros ms3 [-> ST3].
        split; [reflexivity|]. split; [exact HE|].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [reflexivity|]. split; [exact MU02|]. split; [exact WM02|]. split; [exact MI2|]. split; [exact ST3 | exact ERR2].
      - (* [comment removed for export] *)
        destruct HD as [-> HFD]. unfold eff0. sys_nret.
        eapply evtF_mono.
        { eapply (fopen_S2_ok RNG (Z_to_bv 64 0x497e0) spm gp (Z_to_bv 64 ATP) sp (Z_to_bv 64 MODE) (Z_to_bv 64 NAME) x19 s4 s5 (Z_to_bv 64 (bv_unsigned sp + -2136)) s7 s8 s9 s10 s11 F fc)
            with (lo := lo) (NAME := NAME) (MODE := MODE) (md := md) (slack := slack) (m := m0) (fd := fd) (canary := canary) (errv := errv);
            rewrite ?ETP;
            first [ exact ROMD | exact FR1 | exact ERR1 | exact SSP1 | exact HFD | exact ST1 | exact MI1 | exact MU1 | exact WM1
                  | exact MDR | exact NONUL | exact PAD | exact M0 | exact KLO | exact ENV0 | exact SORWA0 | exact SOMODE0
                  | exact RIMG | exact RERR | exact IESTP | exact APWTP | exact RSTKM | exact TPRM | exact TPLOM | exact TP200M | exact GLO | (keep_hyps rc sp lo NAME MODE name md slack spm LOB Hspm L SPT TOP47 SPHI N0 NLO; lia)
                  | (destruct wr; rewrite FMV; [right | left]; reflexivity)
                  | match goal with |- ?g => idtac "S2OK side:" g end ]. }
        cbv beta. intros ms2 PO2. unfold fopen_S2_post in PO2.
        sbl_pose_in PO2. destruct PO2 as (w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & sv2 & j0 & m2 & -> & FRO2 & FRI2 & ERR2 & SSP2 & MU2 & WM2 & MI2 & ST2). sbl_subst_all.
        rewrite ETP in MU2, ERR2.
        destruct (KEEPM m2 MU2 WM2) as (STM2 & FR2 & MU02 & WM02).
        split; [reflexivity|]. split; [exact HFD|].
        exists x19, w0, w1, w2, c1, c2, c3, c4, c5, c6, c7, w3, w4, w5, w6, sv2, j0, m2.
        split; [reflexivity|]. split; [exact FRO2|]. split; [exact FRI2|]. split; [exact ERR2|]. split; [exact SSP2|].
        split; [exact MU02|]. split; [exact WM02|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact STM2 | exact FR2]. }
    cbv beta. intros r s' RNG' ms' [-> QN]. unfold Qn in QN. clear Qn. destruct QN as [-> QN].
    destruct r as [e|fd].
    - (* [comment removed for export] *)
      destruct QN as (HE & w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & m' & -> & MU' & WM' & MI' & ST' & ERR').
      unfold set_errno. apply implMG_upd_lc. apply implMG_ret. apply evtF_done.
      split; [apply fp_le_refl|].
      eexists _, m'. split; [unfold hpost_regs; repeat eexists; reflexivity|]. split; [reflexivity|].
      split; [exact MI'|]. split; [exact ST'|].
      destruct (GIOA_errno_step L RNG s CL FB FL m m' _ (bv_unsigned sp) (set_errno_lc e (ps_libc s)) (Z_to_bv 64 e) G MU' WM') as [G' AG'];
        [ apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_cons; [right; cbn [fst snd]; lia | apply Forall_nil]]
        | lia | exact ERR' | reflexivity | reflexivity | reflexivity | ].
      split; [exact AG'|]. split; [reflexivity|]. split; [exact G'|].
      cbn [ps_libc set_libc set_errno_lc lc_errno]. split; [exact ERR' | lia].
    - (* [comment removed for export] *)
      destruct QN as (HFD & x19 & w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & sv2 & j0 & m2 & -> & FRO2 & FRI2 & ERR2 & SSP2 & MU2 & WM2 & MI2 & ST2 & STM2 & FR2).
      destruct (GIOA_errno_step L RNG s CL FB FL m m2 _ (bv_unsigned sp) (ps_libc s) errv G MU2 WM2) as [G2 AG2];
        [ apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_cons; [right; cbn [fst snd]; lia | apply Forall_nil]]
        | lia | exact ERR2 | reflexivity | reflexivity | reflexivity | ].
      rewrite set_libc_same in G2.
      remember (Z_to_bv 64 (bv_unsigned spm + -96) : word) as spc eqn:Espc.
      assert (Hspc : bv_unsigned spc = bv_unsigned spm + -96) by (rewrite Espc; apply unsigned_lit; lia).
      assert (EMD : bv_unsigned (Z_to_bv 64 MODE : word) = MODE) by (apply unsigned_lit; lia).
      assert (ERA : bv_unsigned (Z_to_bv 64 0x99fb4 : word) = 0x99fb4) by (apply unsigned_lit; lia).
      eapply implMG_bind.
      { eapply (MALLOC (Z_to_bv 64 0x99fb4) spc gp (Z_to_bv 64 ATP)) with (L := L) (CL := CL) (FB := FB) (FL := FL) (lo := lo) (n := FILE_ALLOC).
        - split; [exact G2|]. split; [rewrite Hspc; exact ST2|]. split; [exact LOA|]. split; [unfold MALLOC_STACK; lia|].
          split; [split; [lia | exact TOP47]|]. split; [exact MI2|]. split; [reflexivity|].
          split; [rewrite Hspc, Hspm; clear - SPAL; Z.div_mod_to_equations; lia|].
          split; [exact RSTKF|]. split; [exact RIMG|]. split; [exact RIMGSH | exact RTLS].
        - reflexivity.
        - unfold FILE_ALLOC. lia.
        - unfold unw_okA. rewrite EMD, ERA. split; [| unfold AMALLOC_PC; lia].
          exists []. left. split; [lia|]. split; [apply uc_stop; intros (X & _); lia|]. split; [cbn [length]; lia|].
          split; [exact (TPFO _ _ _ TPF) | exact RSTKF]. }
      cbv beta. intros po sM RNG3 ms3 (FP3 & a0v & m3 & REGS & OF3 & MI3 & ST3 & AG3 & RES).
      destruct po as [q|]; [| destruct RES].
      sbl_pose_in RES. destruct RES as (A & junk & -> & G3 & BLK). sbl_subst_all.
      unfold hpost_regs in REGS. sbl_pose_in REGS. destruct REGS as (y0 & y1 & y2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y3 & y4 & y5 & y6 & ->). sbl_subst_all.
      replace (ret_pc (Z_to_bv 64 0x99fb4)) with (Z_to_bv 64 0x99fb4 : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
      cbn beta iota.
      (* [comment removed for export] *)
      assert (FRO3 : rw_cells asegs m3 (bv_unsigned spm + -32) [C8 (Z_to_bv 64 NAME); C8 (Z_to_bv 64 MODE); C8 sp; C8 (Z_to_bv 64 0x497e0)])
        by (eapply keeps_rw_cells_stack; [exact AG3 | exact FRO2 | lia]).
      assert (FRI3 : rw_cells asegs m3 (bv_unsigned spm + -96) [CB 16 j0; C8 canary; C8 x19; C8 sv2; C8 (Z_to_bv 64 fd); C8 (Z_to_bv 64 MODE); C8 (Z_to_bv 64 0x9ac3c)])
        by (eapply keeps_rw_cells_stack; [exact AG3 | exact FRI2 | lia]).
      assert (STM3 : stk asegs m3 (bv_unsigned spm) (bv_unsigned sp + -64)) by (eapply agrees_stk; [exact AG3 | exact STM2 | intros a Ha; left; lia]).
      assert (FR3 : rw_cells asegs m3 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
        by (eapply keeps_rw_cells_stack; [exact AG3 | exact FR2 | lia]).
      assert (AG03 : agrees_on (client_keeps FL CL (bv_unsigned sp)) m m3).
      { eapply agrees_on_trans; [exact AG2|]. eapply client_keeps_weaken; [exact AG3 | lia | intros a Ha; exact Ha | apply incl_refl]. }
      rewrite Hspc in ST3. rewrite Espc. clear Espc Hspc AG3.
      (* [comment removed for export] *)
      assert (RIMG3 : rng_aimg RNG3) by (eapply rng_fp_le; [exact FP3 | exact RIMG]).
      assert (RIMGSH3 : rng RNG3 0x7fffa000 780288) by (eapply rng_fp_le; [exact FP3 | exact RIMGSH]).
      assert (RSTK3 : rng RNG3 lo (bv_unsigned sp - lo)) by (eapply rng_fp_le; [exact FP3 | exact RSTK]).
      assert (RSTKM3 : rng RNG3 lo (bv_unsigned spm - lo)) by (eapply rng_sub'; [exact RSTK3 | lia]).
      assert (RERR3 : rng RNG3 (ATP + -164) 4) by (eapply rng_fp_le; [exact FP3 | exact RERR]).
      pose proof (fp_le_sobj _ _ _ _ _ FP3 SORWA) as SORWA3. pose proof (fp_le_sobj _ _ _ _ _ FP3 SOMODE) as SOMODE3e.
      pose proof (gs_env _ GSL _ _ _ _ _ _ _ G3) as ENV3.
      pose proof (SSPL _ _ _ _ _ _ G3) as SSP3.
      destruct (gs_libc _ GSL _ _ _ _ _ _ _ G3) as [THR3 NL3].
      pose proof (gs_stdio _ GSL _ _ _ _ _ _ _ G3) as SR3.
      pose proof SR3 as (SO3 & SOI3 & SE3 & SEI3 & SIN3 & U13 & U23 & U33 & OL3 & OH3 & FS3 & ND3).
      assert (SOMODE3 : sobj RNG3 m3 MODE (MODE + (Z.of_nat (length md) + 1))).
      { apply mobjA_sobj; [| lia]. eapply (gia_global_mobjA _ _ _ GL); [exact G3 | exact MGLOB | exact RIMG3 | exact RIMGSH3]. }
      destruct (live_block_factsA L RNG3 sM ((q, A, FILE_ALLOC) :: CL) FB FL m3 q A FILE_ALLOC lo G3 ltac:(left; reflexivity) LOA ltac:(unfold FILE_ALLOC; lia))
        as (A0 & _ & ALO & A3 & ATOPA & SOA & RGA).
      unfold FILE_ALLOC in ALO, ATOPA, SOA, RGA, BLK.
      pose proof (gl_apart _ _ _ GL _ _ _ _ _ _ _ G3) as BA3.
      (* [comment removed for export] *)
      assert (HDB : forall q1 Ah n1 FB', FB = (q1, Ah, n1) :: FB' ->
                n1 = FILE_ALLOC /\ 0x604000 <= Ah /\ Ah + 1264 <= lo /\ (A + 1264 <= Ah \/ Ah + 1264 <= A) /\ rng RNG3 Ah 1264
                /\ exists pvo : word, rw_cells asegs m3 (Ah + 104) [C8 pvo]).
      { intros q1 Ah n1 FB' E. subst FB.
        destruct (lc_files (ps_libc sM)) as [|[q1' f1] fs'] eqn:EFS; [exfalso; exact FS3|].
        cbn [files_R] in FS3. sbl_pose_in FS3. destruct FS3 as (Eq1 & -> & B0 & Bhi & FR1h & INV1 & REST1). sbl_subst_all.
        destruct (live_block_factsA L RNG3 sM ((q, A, FILE_ALLOC) :: CL) ((q1, Ah, FILE_ALLOC) :: FB') FL m3 q1 Ah FILE_ALLOC lo G3
                    ltac:(apply in_or_app; right; left; reflexivity) LOA ltac:(unfold FILE_ALLOC; lia)) as (_ & _ & K2 & K3 & _ & _ & K6).
        cbn [app blocks_apart] in BA3. destruct BA3 as [APc _].
        pose proof (proj1 (Forall_forall _ _) APc (q1, Ah, FILE_ALLOC) ltac:(apply in_or_app; right; left; reflexivity)) as AP.
        unfold apart, cb_addr, cb_size, FILE_ALLOC in AP, K2, K6. cbn [fst snd] in AP.
        split; [reflexivity|]. split; [exact K3|]. split; [exact K2|]. split; [lia|]. split; [exact K6|].
        exists (Z_to_bv 64 0). exact (FILE_R_prev_cell _ _ _ _ _ _ _ _ _ FR1h). }
      assert (HDR : 0 <= hd_addr FB /\ hd_addr FB + 232 < 2^63).
      { destruct FB as [|[[q1 Ah] n1] FB']; cbn [hd_addr]; [lia|]. destruct (HDB q1 Ah n1 FB' eq_refl) as (_ & K1 & K2 & _). lia. }
      (* [comment removed for export] *)
      eapply implMG_evtF.
      { eapply (fopen_S6 RNG3 (Z_to_bv 64 0x497e0) spm gp (Z_to_bv 64 ATP) sp (Z_to_bv 64 MODE) (Z_to_bv 64 NAME) x19 s4 s5 (Z_to_bv 64 (bv_unsigned sp + -2136)) s7 s8 s9 s10 s11 F fc)
          with (lo := lo) (NAME := NAME) (MODE := MODE) (md := md) (slack := slack) (m := m) (P := A) (fd := fd) (canary := canary) (m2 := m3);
          rewrite ?ETP;
          first [ exact ROMD | exact BLK | exact FRO3 | exact FRI3 | exact SSP3 | exact HFD | exact ST3 | exact MI3 | exact ENV3 | exact SOMODE3 | exact SOA | exact RGA
                | exact MDR | exact NONUL | exact PAD | exact M0 | exact NOPLUS | exact NOE | exact KLO | exact ENV | exact SORWA3 | exact SOMODE3e
                | exact RIMG3 | exact RERR3 | exact IESTP | exact APWTP | exact RSTKM3 | exact TPRM | exact TPLOM | exact GLO | lia
                | match goal with |- ?g => idtac "S6 side:" g end ]. }
      cbv beta. intros ms4 PO4. unfold fopen_S6_post in PO4.
      sbl_pose_in PO4. destruct PO4 as (x1' & e0 & e1 & e2 & e4 & e5 & e6 & e7 & e8 & e9 & e10 & e11 & m4 & -> & FC4 & BLK4 & FRO4 & (sv2' & j0' & FRI4) & SSP4 & MU4 & WM4 & MI4 & ST4). sbl_subst_all.
      (* [comment removed for export] *)
      assert (THR4 : rw_cells asegs m4 0x601c49 [C1 (Z_to_bv 8 0)]) by (eapply rw_cells_transport; [exact THR3 | exact MU4 | exact WM4 | cbn [disjoint_from cells_size csize Nat.add]; lia]).
      assert (NL4 : rw_cells asegs m4 NEED_LOCKS [C1 (Z_to_bv 8 0)]) by (unfold NEED_LOCKS; eapply rw_cells_transport; [exact NL3 | exact MU4 | exact WM4 | cbn [disjoint_from cells_size csize Nat.add]; lia]).
      assert (OL4 : rw_cells asegs m4 A_OFL_LOCK [C4 (Z_to_bv 64 0)]) by (unfold A_OFL_LOCK in *; eapply rw_cells_transport; [exact OL3 | exact MU4 | exact WM4 | cbn [disjoint_from cells_size csize Nat.add]; lia]).
      assert (OH4 : rw_cells asegs m4 A_OFL_HEAD [C8 (Z_to_bv 64 (hd_addr FB))]) by (unfold A_OFL_HEAD in *; eapply rw_cells_transport; [exact OH3 | exact MU4 | exact WM4 | cbn [disjoint_from cells_size csize Nat.add]; lia]).
      assert (HDF : hd_addr FB = 0 \/ (hd_addr FB <> 0 /\ (exists pvo : word, rw_cells asegs m4 (hd_addr FB + 104) [C8 pvo])
                     /\ hd_addr FB + 232 <= lo /\ (hd_addr FB + 232 <= A \/ A + 1264 <= hd_addr FB) /\ (hd_addr FB + 232 <= 0x10000 \/ 0x604000 <= hd_addr FB))).
      { destruct FB as [|[[q1 Ah] n1] FB']; [left; reflexivity | right]. cbn [hd_addr].
        destruct (HDB q1 Ah n1 FB' eq_refl) as (_ & K1 & K2 & K3 & _ & (pvo & PVC)).
        split; [lia|]. split; [| lia].
        exists pvo. eapply rw_cells_transport; [exact PVC | exact MU4 | exact WM4 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
      assert (RHD : hd_addr FB <> 0 -> rng RNG3 (hd_addr FB + 104) 8).
      { destruct FB as [|[[q1 Ah] n1] FB']; cbn [hd_addr]; [intros X; exfalso; exact (X eq_refl)|]. intros _.
        destruct (HDB q1 Ah n1 FB' eq_refl) as (_ & _ & _ & _ & K5 & _). eapply rng_sub'; [exact K5 | lia]. }
      assert (RPA : rng RNG3 A 232) by (eapply rng_sub'; [exact RGA | lia]).
      (* [comment removed for export] *)
      lazymatch goal with |- implMG _ _ _ ?Q _ => set (QF := Q) end.
      assert (FIN : forall (x1'' e0' e1' e2' a0' a1' a2' a3' e4' e5' e6' e7' e8' e9' e10' e11' : word),
        evtF asegs RNG3 (QF (Some q) (set_libc (set_files ((q, fdopen_file fd wr) :: lc_files (ps_libc sM)) (ps_libc sM)) sM) RNG3)
          (MS (mkR x1'' (Z_to_bv 64 (bv_unsigned spm + -96)) gp (Z_to_bv 64 ATP) e0' e1' e2' (Z_to_bv 64 A) (Z_to_bv 64 fd)
                   a0' a1' a2' a3' e4' e5' e6' e7' (Z_to_bv 64 MODE) (Z_to_bv 64 ssp_guard) s4 s5 (Z_to_bv 64 (bv_unsigned sp + -2136)) s7 s8 s9 s10 s11 e8' e9' e10' e11')
              F (Z_to_bv 64 0x9a0c8) fc None m4 (seg_rom asegs))).
      { intros. subst QF. cbv beta.
        eapply evtF_cut.
        { eapply (fopen_S7 RNG3 (Z_to_bv 64 0x497e0) spm gp (Z_to_bv 64 ATP) sp (Z_to_bv 64 MODE) (Z_to_bv 64 NAME) x19 s4 s5 (Z_to_bv 64 (bv_unsigned sp + -2136)) s7 s8 s9 s10 s11 F fc)
            with (lo := lo) (NAME := NAME) (MODE := MODE) (md := md) (slack := slack) (m := m) (hd := hd_addr FB) (m2 := m3)
                 (fl := if mode_m0 md =? 114 then 8 else 4) (P := A) (fd := fd) (canary := canary);
            rewrite ?ETP;
            first [ exact FC4 | exact BLK4 | exact FRO4 | exact FRI4 | exact SSP4 | exact THR4 | exact NL4 | exact OL4 | exact OH4 | exact HDF | exact RHD | exact RPA
                  | exact MU4 | exact WM4 | exact ST4 | exact MI4 | exact HFD
                  | exact KLO | exact ENV | exact SORWA3 | exact SOMODE3e | exact RIMG3 | exact RERR3 | exact IESTP | exact APWTP | exact RSTKM3 | exact TPRM | exact TPLOM | exact GLO | (keep_hyps rc sp lo NAME MODE name md slack spm LOB Hspm L SPT TOP47 SPHI N0 NLO A A0 A3 ALO hptr FB HDR; lia)
                  | (unfold sub_fp; cbn [outside]; intros x Hx; (keep_hyps rc hptr sp FB lo NAME MODE name md slack spm A x Hx; lia))
                  | match goal with |- ?g => idtac "S7 side:" g end ]. }
        cbv beta. intros ms7 PO7. unfold fopen_S7_post in PO7.
        sbl_pose_in PO7. destruct PO7 as (f0' & f1' & f2' & g1 & g2 & g3 & g4 & g5 & g6 & g7 & f3' & f4' & f5' & f6' & m7 & -> & FC7 & BLK7 & OL7 & OH7 & OLDP7 & SSP7 & MU7 & WM7 & MI7 & ST7). sbl_subst_all.
        (* [comment removed for export] *)
        assert (DJ7 : forall a n, bv_unsigned spm <= a -> 0 <= n -> disjoint_from [(lo, bv_unsigned spm); (A, A + 232); (A_OFL_HEAD, A_OFL_HEAD + 8); (hd_addr FB + 104, hd_addr FB + (if hd_addr FB =? 0 then 104 else 112))] a n).
        { intros a n Ha Hn. unfold A_OFL_HEAD. cbn [disjoint_from]. destruct HDF as [E | (NE & _ & K1 & _)].
          - rewrite E. cbn. lia.
          - replace (hd_addr FB =? 0) with false by (symmetry; apply Z.eqb_neq; exact NE). lia. }
        assert (STM7 : stk asegs m7 (bv_unsigned spm) (bv_unsigned sp + -64)).
        { eapply stk_transport_disjoint; [exact STM3 | exact MU7 | exact WM7 | apply DJ7; lia]. }
        assert (FR7 : rw_cells asegs m7 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
        { eapply rw_cells_transport; [exact FR3 | exact MU7 | exact WM7 | apply DJ7; cbn [cells_size csize Nat.add]; lia]. }
        replace (ret_pc (Z_to_bv 64 0x497e0)) with (Z_to_bv 64 0x497e0 : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
        rewrite Hspm in ST7, STM7. rewrite Espm.
        eapply evtF_mono.
        { eapply (fopen_i_post RNG3) with (lo := lo) (m := m7);
            first [ exact MI7 | exact ST7 | exact STM7 | exact FR7 | (eapply rng_sub'; [exact RSTK3 | lia]) | lia
                  | match goal with |- ?g => idtac "IPOST7 side:" g end ]. }
        cbv beta. intros ms8 [-> ST8].
        (* [comment removed for export] *)
        pose proof MU7 as MU37.
        assert (HWX : exists W', munch W' m3 m7
                  /\ Forall (fun iv : Z * Z => (ATOP + 4096 <= fst iv /\ snd iv <= bv_unsigned sp) \/ (fst iv = A /\ snd iv = A + 232) \/ (fst iv = A_OFL_HEAD /\ snd iv = A_OFL_HEAD + 8)
                                              \/ (FB <> [] /\ fst iv = hd_addr FB + 104 /\ snd iv = hd_addr FB + 112)) W').
        { revert MU37. destruct (Z.eqb_spec (hd_addr FB) 0) as [E|NE]; intros MU37.
          - exists [(lo, bv_unsigned spm); (A, A + 232); (A_OFL_HEAD, A_OFL_HEAD + 8)]. split.
            + eapply munch_weaken; [| exact MU37]. unfold sub_fp. intros x Ox. cbn [outside] in Ox |- *. sbl_pose_in Ox. destruct Ox as (O1 & O2 & O3 & _). sbl_subst_all.
              split; [exact O1|]. split; [exact O2|]. split; [exact O3|]. split; [lia | exact I].
            + apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [right; left; split; reflexivity|].
              apply Forall_cons; [right; right; left; split; reflexivity | apply Forall_nil].
          - exists [(lo, bv_unsigned spm); (A, A + 232); (A_OFL_HEAD, A_OFL_HEAD + 8); (hd_addr FB + 104, hd_addr FB + 112)]. split.
            + exact MU37.
            + apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [right; left; split; reflexivity|].
              apply Forall_cons; [right; right; left; split; reflexivity|]. apply Forall_cons; [| apply Forall_nil].
              right; right; right. cbn [fst snd]. split; [| split; reflexivity]. intros EFB. apply NE. rewrite EFB. reflexivity. }
        destruct HWX as (W' & MU7' & HW').
        assert (EFL7 : (if mode_m0 md =? 114 then 8 else 4) = (if wr then 4 else 8)) by (rewrite M0W; destruct wr; reflexivity).
        destruct (fopen_finishA L RNG3 sM CL FB FL m3 m7 W' q A fd wr _ (skipn 232 junk) (bv_unsigned sp) G3 MU7' WM7 HW' ltac:(lia) FC7 BLK7 OL7 OH7 OLDP7 EFL7 HFD) as [G7 AG7].
        split; [exact FP3|].
        eexists _, m7. split; [unfold hpost_regs; repeat eexists; reflexivity|].
        split; [destruct sM as [xh xl xo xt]; cbn [ps_outfile set_libc] in OF3 |- *; exact OF3|].
        split; [exact MI7|]. split; [exact ST8|].
        split; [eapply agrees_on_trans; [exact AG03 | exact AG7]|].
        exists A. split; [reflexivity | exact G7]. }
      destruct wr.
      + (* [comment removed for export] *)
        assert (EFL : (mode_m0 md =? 114) = false) by (rewrite M0W; reflexivity). rewrite EFL in FC4 |- *.
        apply implMG_bind_assoc. apply implMG_sysk; [exact I|].
        eapply evtF_cut.
        { eapply (fopen_br_w RNG3) with (sp := spm) (lo := lo) (NAME := NAME) (MODE := MODE) (md := md) (m := m) (fd := fd);
            rewrite ?ETP;
            first [ exact KLO | exact ENV | exact SORWA3 | exact SOMODE3e | exact RIMG3 | exact RERR3 | exact IESTP | exact APWTP | exact RSTKM3 | exact TPRM | lia
                  | match goal with |- ?g => idtac "BRW side:" g end ]. }
        cbv beta. intros ms5 ->.
        step_ecall. split. { at_nodeA_solve. }
        intros rsp a Hdec. unfold dec_ioctl in Hdec. apply dec_plain_Some in Hdec.
        destruct a as [e'|v]; [| destruct Hdec as (_ & X & _); discriminate X]. destruct Hdec as [-> HE'].
        cbn beta iota. apply implMG_retb. apply implMG_upd_lc. apply implMG_ret. unfold efferr. sys_nret.
        eapply evtF_cut.
        { eapply (fopen_ioctl_ret RNG3) with (sp := spm) (lo := lo) (NAME := NAME) (MODE := MODE) (md := md) (slack := slack) (m := m) (e := e');
            rewrite ?ETP;
            first [ exact HE' | exact KLO | exact ENV | exact SORWA3 | exact SOMODE3e | exact RIMG3 | exact RERR3 | exact IESTP | exact APWTP | exact RSTKM3 | exact TPRM | lia
                  | match goal with |- ?g => idtac "IOCTLRET side:" g end ]. }
        cbv beta. intros ms6 ->. apply FIN.
      + (* [comment removed for export] *)
        assert (EFL : (mode_m0 md =? 114) = true) by (rewrite M0W; reflexivity). rewrite EFL in FC4 |- *.
        apply implMG_retb. apply implMG_upd_lc. apply implMG_ret.
        eapply evtF_cut.
        { eapply (fopen_br_r RNG3) with (sp := spm) (lo := lo) (NAME := NAME) (MODE := MODE) (md := md) (m := m);
            rewrite ?ETP;
            first [ exact KLO | exact ENV | exact SORWA3 | exact SOMODE3e | exact RIMG3 | exact RERR3 | exact IESTP | exact APWTP | exact RSTKM3 | exact TPRM | lia
                  | match goal with |- ?g => idtac "BRR side:" g end ]. }
        cbv beta. intros ms5 ->. apply FIN.
  Qed.
  End Sz1.
  Theorem fopen_o_proofA : ltac:(let t := eval cbv delta [fopen_o_proofA__stmt] in fopen_o_proofA__stmt in exact t).
  Proof using EQB GL GSL HAL MALLOC TPFO. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL trC lo NAME MODE name md wr. ltac2:(SecDiet.SzSec.closeP 'fopen_o_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End GlueFo.
End TwB.
End Stdio_glue_foA.

(* [comment removed for export] *)
Module Stdio_glue_strA.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require PcapRepA Pcap_ifaceA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_strlen Stdio_repA Stdio_glueKitA StdioLawsA Stdio_glueA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strlen OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioLawsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_foKitA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section GlueStr.
  Context {rc : runConstT} {tlsI : ABase.atlsT}.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GSL : gia_stdio_laws GIOA.

  #[local] Notation spo_factsA := (Stdio_glueA.spo_factsA GIOA GSL).
  #[local] Notation robjA_factsA := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_foKitA.robjA_factsA FO GIOA fflagA GL).

  Theorem strlen_proofA : strlen_stmt GIOA.
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
    intros until slack. intros SPO -> HB NNUL LEN PAD RO RG.
    pose proof (spo_factsA _ _ _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & _ & ENV & LOA & LOB & SPT & TOP47 & Etp & RSTK & RIMG & RTLS & KLO & GLO).
    subst tp. unfold STDIO_STACK in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct (robjA_factsA L RNG s CL FB FL m P (Z.of_nat (length bs) + 1) lo G RO ltac:(lia) LOA) as (P0 & PLO & SOP & RGP).
    (* [comment removed for export] *)
    set (pad := (- (P + Z.of_nat (length bs) + 1)) mod 8) in *.
    assert (PADR : 0 <= pad < 8) by (subst pad; apply Z.mod_pos_bound; lia).
    set (slack' := firstn (Z.to_nat pad) slack).
    assert (LS' : Z.of_nat (length slack') = pad) by (subst slack'; rewrite length_firstn; lia).
    assert (HB' : bytes_at asegs m P (bs ++ Z_to_bv 8 0 :: slack')).
    { assert (E : bs ++ Z_to_bv 8 0 :: slack = (bs ++ Z_to_bv 8 0 :: slack') ++ skipn (Z.to_nat pad) slack).
      { subst slack'. rewrite <- app_assoc. cbn [app]. rewrite firstn_skipn. reflexivity. }
      rewrite E in HB. exact (proj1 (proj1 (bytes_at_app asegs m P _ _) HB)). }
    assert (EP : bv_unsigned (Z_to_bv 64 P : word) = P) by (apply unsigned_lit; lia).
    eapply evtF_mono.
    { unfold STRLEN_ENTRY.
      eapply (strlen_wb_spec RNG ra sp gp (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo bs slack');
        rewrite ?EP; rewrite ?length_app; cbn [length];
        first [ exact MI | exact ST | exact KLO | exact ENV | exact HB' | exact NNUL | exact SOP | exact RIMG | exact RSTK
              | (eapply rng_sub'; [exact RG | lia]) | lia | (left; lia) ]. }
    cbv beta. intros ms' PO. unfold strlen_i_post in PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m' & -> & MU & WM & MI' & ST' & _).
    eexists _, m'. split; [unfold hpost_regs; repeat eexists; reflexivity|].
    split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros x Hx; lia|].
    split; [exact WM|]. split; [exact MI'|]. split; [exact ST' | reflexivity].
  Qed.
End GlueStr.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strlen.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioLawsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_foKitA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section GlueStr.
  Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GSL : gia_stdio_laws GIOA.

  #[local] Notation spo_factsA := (A3S.Stdio_glueA.TwB.spo_factsA GIOA GSL).
  #[local] Notation robjA_factsA := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_foKitA.TwB.robjA_factsA FO GIOA fflagA GL).

  Theorem strlen_proofA : strlen_stmt GIOA.
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
    intros until slack. intros SPO -> HB NNUL LEN PAD RO RG.
    pose proof (spo_factsA _ _ _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & _ & ENV & LOA & LOB & SPT & TOP47 & Etp & RSTK & RIMG & RTLS & KLO & GLO).
    subst tp. unfold STDIO_STACK in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct (robjA_factsA L RNG s CL FB FL m P (Z.of_nat (length bs) + 1) lo G RO ltac:(lia) LOA) as (P0 & PLO & SOP & RGP).
    (* [comment removed for export] *)
    set (pad := (- (P + Z.of_nat (length bs) + 1)) mod 8) in *.
    assert (PADR : 0 <= pad < 8) by (subst pad; apply Z.mod_pos_bound; lia).
    set (slack' := firstn (Z.to_nat pad) slack).
    assert (LS' : Z.of_nat (length slack') = pad) by (subst slack'; rewrite length_firstn; lia).
    assert (HB' : bytes_at asegs m P (bs ++ Z_to_bv 8 0 :: slack')).
    { assert (E : bs ++ Z_to_bv 8 0 :: slack = (bs ++ Z_to_bv 8 0 :: slack') ++ skipn (Z.to_nat pad) slack).
      { subst slack'. rewrite <- app_assoc. cbn [app]. rewrite firstn_skipn. reflexivity. }
      rewrite E in HB. exact (proj1 (proj1 (bytes_at_app asegs m P _ _) HB)). }
    assert (EP : bv_unsigned (Z_to_bv 64 P : word) = P) by (apply unsigned_lit; lia).
    eapply evtF_mono.
    { unfold STRLEN_ENTRY.
      eapply (strlen_wb_spec RNG ra sp gp (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo bs slack');
        rewrite ?EP; rewrite ?length_app; cbn [length];
        first [ exact MI | exact ST | exact KLO | exact ENV | exact HB' | exact NNUL | exact SOP | exact RIMG | exact RSTK
              | (eapply rng_sub'; [exact RG | lia]) | lia | (left; lia) ]. }
    cbv beta. intros ms' PO. unfold strlen_i_post in PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m' & -> & MU & WM & MI' & ST' & _).
    eexists _, m'. split; [unfold hpost_regs; repeat eexists; reflexivity|].
    split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros x Hx; lia|].
    split; [exact WM|]. split; [exact MI'|]. split; [exact ST' | reflexivity].
  Qed.
End GlueStr.
End TwB.
End Stdio_glue_strA.

(* [comment removed for export] *)
Module Stdio_glue_strerrA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw ExecF ITreeA Shadow StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StrerrorTable StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require StrerrorData. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.StrerrorData.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABase AMalloc_iface RtCells. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require MonadF. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require PcapRepA Pcap_ifaceA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA Stdio_glueKitA StdioLawsA Stdio_glueA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_lock__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_strerror__A3S. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioLawsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_foKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_strerror OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.I_strerror OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.F_strerror_r OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.I_strerror_r.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition strerror_chk (k : nat) : bool :=
  if list_eq_dec Z.eq_dec (nth k strerror_msgZ [])
       (str (match table_lookup strerror_table (Z.of_nat k) with Some s => s | None => strerror_default end))
  then true else false.
Lemma strerror_chk_all : forallb strerror_chk (seq 0 132) = true.
Proof. vm_compute. reflexivity. Qed.
Definition strerror_tables_agree__stmt : Prop := forall e, (-2^31 <= e < 2^31)%Z -> strerror_msgb e = map (fun z => Z_to_bv 8 z) (Fmt.strerror e).
Section Sz2.
Variables e : ltac2:(SecDiet.SzSec.tyM 'strerror_tables_agree__stmt "v" @e).
#[using="Type"] Lemma strerror_tables_agree__body : ltac2:(SecDiet.SzSec.bodyP 'strerror_tables_agree__stmt "v").
Proof.
  intros He.
 unfold strerror_msgb, sr_msgb, strerror_e, Fmt.strerror, StrerrorTable.STRERROR_N.
  set (k := if ((0 <=? e) && (e <? 132))%Z then e else 0%Z).
  assert (Hk : (0 <= k < 132)%Z) by (subst k; destruct (Z.leb_spec 0 e), (Z.ltb_spec e 132); cbn; lia).
  f_equal.
  pose proof (proj1 (forallb_forall _ _) strerror_chk_all (Z.to_nat k) ltac:(apply in_seq; lia)) as C.
  unfold strerror_chk in C. rewrite Z2Nat.id in C by lia.
  destruct (list_eq_dec Z.eq_dec _ _) as [E|NE]; [exact E| discriminate C].
Qed.
End Sz2.
Lemma strerror_tables_agree : ltac:(let t := eval cbv delta [strerror_tables_agree__stmt] in strerror_tables_agree__stmt in exact t).
Proof. intros e. ltac2:(SecDiet.SzSec.closeP 'strerror_tables_agree__body "v"). Qed.
Lemma s32_id : forall e, (-2^31 <= e < 2^31)%Z -> s32 e = e.
Proof. intros e He. unfold s32. rewrite Z.mod_small by lia. lia. Qed.

Section GlueStrerr.
  Context {rc : runConstT} {tlsI : ABase.atlsT}.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GSL : gia_stdio_laws GIOA.

  (* [comment removed for export] *)
  Definition GLOBAL_LOCALE : Z := 0x601880.
  Definition strerr_cells (m : mem) : Prop :=
       rw_cells asegs m 0xa6108 [C8 (Z_to_bv 64 0x10)]                          (* [comment removed for export] *)
    /\ rw_cells asegs m (ATP + 16) [C4 (Z_to_bv 64 0)]                            (* [comment removed for export] *)
    /\ rw_cells asegs m (ATP + -48) [C8 (Z_to_bv 64 GLOBAL_LOCALE)]               (* [comment removed for export] *)
    /\ rw_cells asegs m (GLOBAL_LOCALE + 40) [C8 (Z_to_bv 64 0)]                  (* [comment removed for export] *)
    /\ exists old, rw_cells asegs m (ATP + PCAP_TLS_ERRBUF) [CB 256 old].         (* [comment removed for export] *)
  Record gia_strerr_laws : Prop := mkGSE {
    ge_cells : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m -> strerr_cells m;
    ge_frame : forall L RNG (s : PS) CL FB FL m m' W SP new,
                 GIOA L RNG s CL FB FL m -> munch (W ++ [(ATP + 16, ATP + PCAP_TLS_ERRBUF + 256)]) m m' -> wmono asegs m m' ->
                 Forall (fun iv => ATOP + 4096 <= fst iv /\ snd iv <= SP) W -> ATOP + 4096 <= SP ->
                 rw_cells asegs m' (ATP + 16) [C4 (Z_to_bv 64 0)] ->
                 rw_cells asegs m' (ATP + PCAP_TLS_ERRBUF) [CB 256 new] ->
                 GIOA L RNG s CL FB FL m' /\ agrees_on (client_keeps FL CL SP) m m'
  }.
  Hypothesis GSE : gia_strerr_laws.

  #[local] Notation spo_factsA := (Stdio_glueA.spo_factsA GIOA GSL).

  Definition strerror_r_proofA__stmt : Prop := strerror_r_stmt GIOA.
  Section Sz4.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo e : ltac2:(SecDiet.SzSec.tyM 'strerror_r_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma strerror_r_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'strerror_r_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GSL GSE. pin_using (fun (GL GSL GSE : unit) => tt).
 intros SPO -> -> -> He.
    pose proof SPO as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & RIMGSH & _)).
    pose proof (spo_factsA _ _ _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & _ & ENV & LOA & LOB & SPT & TOP47 & Etp & RSTK & RIMG & RTLS & KLO & GLO).
    subst tp. unfold STDIO_STACK in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct (ge_cells GSE _ _ _ _ _ _ _ G) as (GOTL & CNT & TLSL & LOC & [old DST]).
    unfold PCAP_TLS_ERRBUF, GLOBAL_LOCALE in *.
    (* [comment removed for export] *)
    pose proof (gl_tls _ _ _ GL _ _ _ _ _ _ _ G RTLS) as MOT.
    pose proof (mobjA_sobj _ _ _ _ MOT ltac:(lia)) as SOT0.
    pose proof atp_lin as ((TL & (KI & _) & _) & (TI1 & TI2) & _).
    pose proof ATPv_pg as TPG.
    unfold ATP in *.
    assert (SOB : sobj RNG m (ATPv + 20) (ATPv + 20 + 256)) by (eapply sobj_sub; [exact SOT0 | lia | lia | lia]).
    assert (SOH : sobj RNG m (ATPv + -184) (ATPv + 264)) by (eapply sobj_sub; [exact SOT0 | lia | lia | lia]).
    (* [comment removed for export] *)
    pose proof (gs_rodata _ GSL _ _ _ _ _ _ _ 0x234bc 0x23d70 G RIMG RIMGSH ltac:(right; lia) ltac:(lia)) as SOTAB.
    assert (EP : bv_unsigned (Z_to_bv 64 ATPv : word) = ATPv) by (apply unsigned_lit; lia).
    assert (AL1 : (ATPv + -184) mod 64 = 0) by (rewrite TI1; reflexivity).
    assert (AL2 : (ATPv + 264) mod 64 = 0) by (rewrite TI1; reflexivity).
    assert (RT1 : rng RNG (ATPv + -48) 8) by (eapply rng_sub'; [exact RTLS | lia]).
    assert (RT2 : rng RNG (ATPv + 16) 4) by (eapply rng_sub'; [exact RTLS | lia]).
    assert (RT3 : rng RNG (ATPv + 20) 256) by (eapply rng_sub'; [exact RTLS | lia]).
    assert (RT4 : rng RNG (6297728 + 40) 8) by (eapply rng_sub'; [exact RIMG | lia]).
    rewrite (s32_id e He).
    eapply evtF_mono.
    { unfold STRERROR_R_ENTRY.
      eapply (strerror_r_wb_spec RNG ra sp gp (Z_to_bv 64 ATPv) t0 t1 t2 s0 s1 (Z_to_bv 64 e) (Z_to_bv 64 (ATPv + 20)) (Z_to_bv 64 256)
                a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m e (ATPv + 20) 256 6297728 old lo (ATPv + -184) (ATPv + 264) kt_img);
        rewrite ?EP;
        first [ exact MI | exact ST | exact KLO | exact ENV | exact GOTL | exact CNT | exact TLSL | exact LOC | exact DST | reflexivity | exact He
              | exact SOB | exact SOTAB | exact SOH | exact AL1 | exact AL2 | exact RIMG | exact RSTK | exact RT1 | exact RT2 | exact RT3 | exact RT4
              | lia | (left; lia) | (right; lia) ]. }
    cbv beta. intros ms' PO. unfold strerror_r_i_post in PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m' & -> & MU & WM & MI' & ST' & CNT' & RES).
    rewrite EP in MU, CNT'.
    assert (MU2 : munch ([(bv_unsigned sp - 4400, bv_unsigned sp)] ++ [(ATPv + 16, ATPv + 20 + 256)]) m m').
    { eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [app outside]. intros x Hx. lia. }
    pose proof (strerror_msgb_length e) as ML.
    (* [comment removed for export] *)
    pose proof (rw_cells_merge asegs m' (ATPv + 20) [] _ [] ltac:(rewrite app_nil_r; exact RES)) as TLS'.
    cbn [cells_size csize cells_bytes cbytes Nat.add app] in TLS'.
    replace (length (strerror_msgb e) + 1 + (Z.to_nat 256 - (length (strerror_msgb e) + 1) + 0))%nat with 256%nat in TLS' by lia.
    rewrite !app_nil_r in TLS'.
    destruct (ge_frame GSE L RNG s CL FB FL m m' [(bv_unsigned sp - 4400, bv_unsigned sp)] (bv_unsigned sp) _ G MU2 WM
                ltac:(constructor; [cbn [fst snd]; lia | constructor]) ltac:(lia) CNT' TLS') as [G' AG].
    eexists _, m', (skipn (length (strerror_msgb e) + 1) old).
    split; [unfold hpost_regs; repeat eexists; reflexivity|].
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG|]. split; [exact G'|].
    rewrite <- (strerror_tables_agree e He).
    assert (EL : length (strerror e) = length (strerror_msgb e)) by (rewrite (strerror_tables_agree e He), length_map; reflexivity).
    rewrite EL.
    replace (255 - length (strerror_msgb e))%nat with (Z.to_nat 256 - (length (strerror_msgb e) + 1))%nat by lia.
    exact RES.
  Qed.
  End Sz4.
  Theorem strerror_r_proofA : ltac:(let t := eval cbv delta [strerror_r_proofA__stmt] in strerror_r_proofA__stmt in exact t).
  Proof using GL GSL GSE. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo e. ltac2:(SecDiet.SzSec.closeP 'strerror_r_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End GlueStrerr.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StrerrorTable OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.StrerrorData.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioLawsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_foKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_strerror.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.I_strerror.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.F_strerror_r.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.I_strerror_r.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition strerror_chk (k : nat) : bool :=
  if list_eq_dec Z.eq_dec (nth k strerror_msgZ [])
       (str (match table_lookup strerror_table (Z.of_nat k) with Some s => s | None => strerror_default end))
  then true else false.
Lemma strerror_chk_all : forallb strerror_chk (seq 0 132) = true.
Proof. vm_compute. reflexivity. Qed.
Definition strerror_tables_agree__stmt : Prop := forall e, (-2^31 <= e < 2^31)%Z -> strerror_msgb e = map (fun z => Z_to_bv 8 z) (Fmt.strerror e).
Section Sz2.
Variables e : ltac2:(SecDiet.SzSec.tyM 'strerror_tables_agree__stmt "v" @e).
#[using="Type"] Lemma strerror_tables_agree__body : ltac2:(SecDiet.SzSec.bodyP 'strerror_tables_agree__stmt "v").
Proof.
  intros He.
 unfold strerror_msgb, sr_msgb, strerror_e, Fmt.strerror, StrerrorTable.STRERROR_N.
  set (k := if ((0 <=? e) && (e <? 132))%Z then e else 0%Z).
  assert (Hk : (0 <= k < 132)%Z) by (subst k; destruct (Z.leb_spec 0 e), (Z.ltb_spec e 132); cbn; lia).
  f_equal.
  pose proof (proj1 (forallb_forall _ _) strerror_chk_all (Z.to_nat k) ltac:(apply in_seq; lia)) as C.
  unfold strerror_chk in C. rewrite Z2Nat.id in C by lia.
  destruct (list_eq_dec Z.eq_dec _ _) as [E|NE]; [exact E| discriminate C].
Qed.
End Sz2.
Lemma strerror_tables_agree : ltac:(let t := eval cbv delta [strerror_tables_agree__stmt] in strerror_tables_agree__stmt in exact t).
Proof. intros e. ltac2:(SecDiet.SzSec.closeP 'strerror_tables_agree__body "v"). Qed.
Lemma s32_id : forall e, (-2^31 <= e < 2^31)%Z -> s32 e = e.
Proof. intros e He. unfold s32. rewrite Z.mod_small by lia. lia. Qed.

Section GlueStrerr.
  Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GSL : gia_stdio_laws GIOA.

  (* [comment removed for export] *)
  Definition GLOBAL_LOCALE : Z := 0x601c80.
  Definition strerr_cells (m : mem) : Prop :=
       rw_cells asegs m 0xa64e8 [C8 (Z_to_bv 64 0x10)]                          (* [comment removed for export] *)
    /\ rw_cells asegs m (ATP + 16) [C4 (Z_to_bv 64 0)]                            (* [comment removed for export] *)
    /\ rw_cells asegs m (ATP + -48) [C8 (Z_to_bv 64 GLOBAL_LOCALE)]               (* [comment removed for export] *)
    /\ rw_cells asegs m (GLOBAL_LOCALE + 40) [C8 (Z_to_bv 64 0)]                  (* [comment removed for export] *)
    /\ exists old, rw_cells asegs m (ATP + PCAP_TLS_ERRBUF) [CB 256 old].         (* [comment removed for export] *)
  Record gia_strerr_laws : Prop := mkGSE {
    ge_cells : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m -> strerr_cells m;
    ge_frame : forall L RNG (s : PS) CL FB FL m m' W SP new,
                 GIOA L RNG s CL FB FL m -> munch (W ++ [(ATP + 16, ATP + PCAP_TLS_ERRBUF + 256)]) m m' -> wmono asegs m m' ->
                 Forall (fun iv => ATOP + 4096 <= fst iv /\ snd iv <= SP) W -> ATOP + 4096 <= SP ->
                 rw_cells asegs m' (ATP + 16) [C4 (Z_to_bv 64 0)] ->
                 rw_cells asegs m' (ATP + PCAP_TLS_ERRBUF) [CB 256 new] ->
                 GIOA L RNG s CL FB FL m' /\ agrees_on (client_keeps FL CL SP) m m'
  }.
  Hypothesis GSE : gia_strerr_laws.

  #[local] Notation spo_factsA := (A3S.Stdio_glueA.TwB.spo_factsA GIOA GSL).

  Definition strerror_r_proofA__stmt : Prop := strerror_r_stmt GIOA.
  Section Sz4.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo e : ltac2:(SecDiet.SzSec.tyM 'strerror_r_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma strerror_r_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'strerror_r_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GSL GSE. pin_using (fun (GL GSL GSE : unit) => tt).
 intros SPO -> -> -> He.
    pose proof SPO as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & RIMGSH & _)).
    pose proof (spo_factsA _ _ _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & _ & ENV & LOA & LOB & SPT & TOP47 & Etp & RSTK & RIMG & RTLS & KLO & GLO).
    subst tp. unfold STDIO_STACK in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct (ge_cells GSE _ _ _ _ _ _ _ G) as (GOTL & CNT & TLSL & LOC & [old DST]).
    unfold PCAP_TLS_ERRBUF, GLOBAL_LOCALE in *.
    (* [comment removed for export] *)
    pose proof (gl_tls _ _ _ GL _ _ _ _ _ _ _ G RTLS) as MOT.
    pose proof (mobjA_sobj _ _ _ _ MOT ltac:(lia)) as SOT0.
    pose proof atp_lin as ((TL & (KI & _) & _) & (TI1 & TI2) & _).
    pose proof ATPv_pg as TPG.
    unfold ATP in *.
    assert (SOB : sobj RNG m (ATPv + 20) (ATPv + 20 + 256)) by (eapply sobj_sub; [exact SOT0 | lia | lia | lia]).
    assert (SOH : sobj RNG m (ATPv + -184) (ATPv + 264)) by (eapply sobj_sub; [exact SOT0 | lia | lia | lia]).
    (* [comment removed for export] *)
    pose proof (gs_rodata _ GSL _ _ _ _ _ _ _ 0x234bc 0x23d70 G RIMG RIMGSH ltac:(right; lia) ltac:(lia)) as SOTAB.
    assert (EP : bv_unsigned (Z_to_bv 64 ATPv : word) = ATPv) by (apply unsigned_lit; lia).
    assert (AL1 : (ATPv + -184) mod 64 = 0) by (rewrite TI1; reflexivity).
    assert (AL2 : (ATPv + 264) mod 64 = 0) by (rewrite TI1; reflexivity).
    assert (RT1 : rng RNG (ATPv + -48) 8) by (eapply rng_sub'; [exact RTLS | lia]).
    assert (RT2 : rng RNG (ATPv + 16) 4) by (eapply rng_sub'; [exact RTLS | lia]).
    assert (RT3 : rng RNG (ATPv + 20) 256) by (eapply rng_sub'; [exact RTLS | lia]).
    assert (RT4 : rng RNG (6298752 + 40) 8) by (eapply rng_sub'; [exact RIMG | lia]).
    rewrite (s32_id e He).
    eapply evtF_mono.
    { unfold STRERROR_R_ENTRY.
      eapply (strerror_r_wb_spec RNG ra sp gp (Z_to_bv 64 ATPv) t0 t1 t2 s0 s1 (Z_to_bv 64 e) (Z_to_bv 64 (ATPv + 20)) (Z_to_bv 64 256)
                a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m e (ATPv + 20) 256 6298752 old lo (ATPv + -184) (ATPv + 264) kt_img);
        rewrite ?EP;
        first [ exact MI | exact ST | exact KLO | exact ENV | exact GOTL | exact CNT | exact TLSL | exact LOC | exact DST | reflexivity | exact He
              | exact SOB | exact SOTAB | exact SOH | exact AL1 | exact AL2 | exact RIMG | exact RSTK | exact RT1 | exact RT2 | exact RT3 | exact RT4
              | lia | (left; lia) | (right; lia) ]. }
    cbv beta. intros ms' PO. unfold strerror_r_i_post in PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m' & -> & MU & WM & MI' & ST' & CNT' & RES).
    rewrite EP in MU, CNT'.
    assert (MU2 : munch ([(bv_unsigned sp - 4400, bv_unsigned sp)] ++ [(ATPv + 16, ATPv + 20 + 256)]) m m').
    { eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [app outside]. intros x Hx. lia. }
    pose proof (strerror_msgb_length e) as ML.
    (* [comment removed for export] *)
    pose proof (rw_cells_merge asegs m' (ATPv + 20) [] _ [] ltac:(rewrite app_nil_r; exact RES)) as TLS'.
    cbn [cells_size csize cells_bytes cbytes Nat.add app] in TLS'.
    replace (length (strerror_msgb e) + 1 + (Z.to_nat 256 - (length (strerror_msgb e) + 1) + 0))%nat with 256%nat in TLS' by lia.
    rewrite !app_nil_r in TLS'.
    destruct (ge_frame GSE L RNG s CL FB FL m m' [(bv_unsigned sp - 4400, bv_unsigned sp)] (bv_unsigned sp) _ G MU2 WM
                ltac:(constructor; [cbn [fst snd]; lia | constructor]) ltac:(lia) CNT' TLS') as [G' AG].
    eexists _, m', (skipn (length (strerror_msgb e) + 1) old).
    split; [unfold hpost_regs; repeat eexists; reflexivity|].
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG|]. split; [exact G'|].
    rewrite <- (strerror_tables_agree e He).
    assert (EL : length (strerror e) = length (strerror_msgb e)) by (rewrite (strerror_tables_agree e He), length_map; reflexivity).
    rewrite EL.
    replace (255 - length (strerror_msgb e))%nat with (Z.to_nat 256 - (length (strerror_msgb e) + 1))%nat by lia.
    exact RES.
  Qed.
  End Sz4.
  Theorem strerror_r_proofA : ltac:(let t := eval cbv delta [strerror_r_proofA__stmt] in strerror_r_proofA__stmt in exact t).
  Proof using GL GSL GSE. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo e. ltac2:(SecDiet.SzSec.closeP 'strerror_r_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End GlueStrerr.
End TwB.
End Stdio_glue_strerrA.

(* [comment removed for export] *)
Module Stdio_glue_sysA.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require PcapRepA Pcap_ifaceA Fuzz_ifaceA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_read__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_cs__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA Stdio_glueKitA StdioLawsA Stdio_glueA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_read__A3S.F_stdio_read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_unlink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioLawsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_foKitA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section GlueSys.
  Context {rc : runConstT} {tlsI : ABase.atlsT}.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GSL : gia_stdio_laws GIOA.

  #[local] Notation spo_factsA := (Stdio_glueA.spo_factsA GIOA GSL).
  #[local] Notation cobjA_factsA := (Stdio_glueA.cobjA_factsA FO GIOA fflagA GL).
  #[local] Notation GIOA_errno_step := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_foKitA.GIOA_errno_step FO GIOA fflagA GL GSL).

  (* [comment removed for export] *)
  Definition sysret_tail_GIA__stmt : Prop := forall (ra sp gp : word) L RNG (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m m1 : mem) (s : PS) (CL FB : list cblk) FL (lo : Z) (J : Z) (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 r errv : word) (jk : list byte),
    std_pre_o GIOA L RNG sp (Z_to_bv 64 ATP) s CL FB FL lo STDIO_STACK m ->
    rw_cells asegs m (ATP + -164) [C4 errv] ->
    (J = 0xa3ef8 \/ J = 0x9ad8c \/ J = 0xa3e08) ->
    rw_cells asegs m1 (bv_unsigned sp + -16) [CB 8 jk; C8 ra] ->
    rw_cells asegs m1 (ATP + -164) [C4 errv] ->
    stk asegs m1 lo (bv_unsigned sp + -16) -> mem_inv asegs m1 ->
    munch [(bv_unsigned sp - 32, bv_unsigned sp); (ATP + -164, ATP + -160)] m m1 -> wmono asegs m m1 ->
    (exists e, (r = errno_ret e /\ 1 <= e <= 4095) \/ r = Z_to_bv 64 0) ->
    evtF asegs RNG (fun ms' => exists a0v m', hpost_regs ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
         /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
         /\ GIOA L RNG (set_libc (match errno_of r with Some e => set_errno_lc e (ps_libc s) | None => ps_libc s end) s) CL FB FL m'
         /\ a0v = Z_to_bv 64 (match errno_of r with Some _ => -1 | None => 0 end)
         /\ rw_cells asegs m' (ATP + -164) [C4 (match errno_of r with Some e => Z_to_bv 64 e | None => errv end)])
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 J) fc None m1 (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp L RNG s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 s CL FB FL lo J x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 r errv jk : ltac2:(SecDiet.SzSec.tyM 'sysret_tail_GIA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma sysret_tail_GIA__body : ltac2:(SecDiet.SzSec.bodyP 'sysret_tail_GIA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
 intros SPO ERR HJ FR1 ERR1 ST1 MI1 MU1 WM1 HR.
    pose proof (spo_factsA _ _ _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & _ & ENV & LOA & LOB & SPT & TOP47 & Etp & RSTK & RIMG & RTLS & KLO & GLO).
    unfold STDIO_STACK in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (@ATOP_lo rc) as ATL. pose proof (@atp_range rc tlsI) as (_ & TPlo & TPhi & TPimg).
    assert (ETP : bv_unsigned (Z_to_bv 64 ATP : word) = ATP) by (apply unsigned_lit; unfold ATP; lia).
    assert (RERR : rng RNG (ATP + -164) 4) by (eapply rng_sub'; [exact RTLS | unfold ATP; lia]).
    assert (TPLOM : ATP + -160 <= lo) by (unfold ATP in *; lia).
    assert (TP200M : 200 <= ATP) by (unfold ATP in *; lia).
    eapply evtF_mono.
    { eapply (sysret_tail RNG ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo errv) with (m0 := m) (J := J) (r := r);
        rewrite ?ETP;
        first [ exact HJ | exact FR1 | exact ERR1 | exact ST1 | exact MI1 | exact MU1 | exact WM1 | exact HR | exact RSTK | exact RERR | exact RIMG | exact GLO
              | exact TPLOM | exact TP200M | lia | match goal with |- ?g => idtac "TL side:" g end ]. }
    cbv beta. intros ms' PO. destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m' & -> & MU' & WM' & MI' & ST' & ERR').
    rewrite ETP in MU', ERR'.
    destruct (GIOA_errno_step L RNG s CL FB FL m m' _ (bv_unsigned sp) (match errno_of r with Some e => set_errno_lc e (ps_libc s) | None => ps_libc s end)
                (match errno_of r with Some e => Z_to_bv 64 e | None => errv end) G MU' WM') as [G' AG'];
      [ apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_cons; [right; cbn [fst snd]; lia | apply Forall_nil]]
      | lia | exact ERR' | destruct (errno_of r); reflexivity | destruct (errno_of r); reflexivity | destruct (errno_of r); reflexivity | ].
    eexists _, m'. split; [unfold hpost_regs; repeat eexists; reflexivity|].
    split; [exact MI'|]. split; [exact ST'|]. split; [exact AG'|]. split; [exact G'|]. split; [reflexivity | exact ERR'].
  Qed.
  End Sz1.
  Lemma sysret_tail_GIA : ltac:(let t := eval cbv delta [sysret_tail_GIA__stmt] in sysret_tail_GIA__stmt in exact t).
  Proof using GL GSL. intros ra sp gp L RNG s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 s CL FB FL lo J x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 r errv jk. ltac2:(SecDiet.SzSec.closeP 'sysret_tail_GIA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma set_libc_id : forall s : PS, set_libc (ps_libc s) s = s.
  Proof using Type. pin_using tt. intros s. destruct s; reflexivity. Qed.

  #[local] Definition WSE (sp : word) : list (Z * Z) := [(bv_unsigned sp - 32, bv_unsigned sp); (ATP + -164, ATP + -160)].
  Lemma munch_add_errno : forall (sp : word) m m1, munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m1 -> munch (WSE sp) m m1.
  Proof using Type. pin_using tt. intros sp m m1 MU. eapply munch_weaken; [| exact MU]. unfold sub_fp, WSE. cbn [outside]. intros x (O1 & O2 & _). split; [exact O1 | exact I]. Qed.

  (* [comment removed for export] *)
  Definition sys_factsA__stmt : Prop := forall L RNG (sp : word) (s : PS) CL FB FL lo m,
    std_pre_o GIOA L RNG sp (Z_to_bv 64 ATP) s CL FB FL lo STDIO_STACK m ->
    GIOA L RNG s CL FB FL m /\ stk asegs m lo (bv_unsigned sp) /\ mem_inv asegs m /\ ATOP + 4096 <= lo /\ lo + 0x4000 <= bv_unsigned sp
    /\ bv_unsigned sp + 16 < al_top L /\ al_top L <= 2^47 /\ rng RNG lo (bv_unsigned sp - lo) /\ rng_aimg RNG /\ 0x603000 <= lo
    /\ (exists errv : word, rw_cells asegs m (ATP + -164) [C4 errv]) /\ rng RNG (ATP + -164) 4 /\ ATP + -160 <= lo /\ 200 <= ATP
    /\ bv_unsigned (Z_to_bv 64 ATP : word) = ATP.
  Section Sz4.
  Variables L RNG sp s CL FB FL lo m : ltac2:(SecDiet.SzSec.tyM 'sys_factsA__stmt "vvvvvvvvv" @L).
  Lemma sys_factsA__body : ltac2:(SecDiet.SzSec.bodyP 'sys_factsA__stmt "vvvvvvvvv").
  Proof using GSL. pin_using (fun (GSL : unit) => tt).
    intros SPO.
    pose proof (spo_factsA _ _ _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & _ & ENV & LOA & LOB & SPT & TOP47 & Etp & RSTK & RIMG & RTLS & KLO & GLO).
    unfold STDIO_STACK in *.
    pose proof (@ATOP_lo rc) as ATL. pose proof (@atp_range rc tlsI) as (_ & TPlo & TPhi & TPimg).
    repeat (split; [first [assumption | exact (gs_errno _ GSL _ _ _ _ _ _ _ G) | (eapply rng_sub'; [exact RTLS | unfold ATP; lia]) | (unfold ATP in *; lia)]|]).
    apply unsigned_lit. unfold ATP. lia.
  Qed.
  End Sz4.
  Lemma sys_factsA : ltac:(let t := eval cbv delta [sys_factsA__stmt] in sys_factsA__stmt in exact t).
  Proof using GSL. intros L RNG sp s CL FB FL lo m. ltac2:(SecDiet.SzSec.closeP 'sys_factsA__body "vvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition unlink_o_proofA__stmt : Prop := unlink_stmt_o GIOA.
  Section Sz5.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo NAME name : ltac2:(SecDiet.SzSec.tyM 'unlink_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma unlink_o_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'unlink_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
 intros SPO -> HNAME NNUL NLEN NCR NOK.
 (* [comment removed for export] *)
 assert (NLENZ : (1 <= Z.of_nat (length name) <= 4095)%Z) by (clear - NLEN; lia). clear NLEN.
    pose proof SPO as (_ & _ & _ & _ & _ & _ & Etp & _). subst tp.
    destruct (sys_factsA _ _ _ _ _ _ _ _ _ SPO) as (G & ST & MI & LOA & LOB & SPT & TOP47 & RSTK & RIMG & GLO & (errv & ERR) & RERR & TPLOM & TP200M & ETP).
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (bytes_at_bound _ _ _ _ HNAME) as NB. rewrite length_app in NB. cbn [length] in NB.
    destruct (cobjA_factsA L RNG s CL FB FL m NAME (Z.of_nat (length name) + 1) lo G NCR ltac:(lia) LOA) as (N0 & NLO & _ & _ & _ & RGNAME & _).
    destruct NOK as (NS & ND1 & ND2 & NLM).
    unfold s_unlink, Stdio.unlink.
    apply implMG_sysk; [exact I|].
    eapply evtF_cut.
    { unfold UNLINK_ENTRY. eapply (unlink_S1 RNG ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo); rewrite ?ETP;
        first [ exact ST | exact MI | exact RSTK | exact RERR | exact RIMG | lia ]. }
    cbv beta. intros ms1 PO. destruct PO as (jk & m1 & -> & FR1 & MU1 & WM1 & MI1 & ST1).
    assert (HNAME1 : bytes_at asegs m1 NAME (name ++ [Z_to_bv 8 0])).
    { eapply bytes_at_transport; [exact HNAME | exact MU1 |]. cbn [disjoint_from]. rewrite length_app. cbn [length]. lia. }
    assert (ERR1 : rw_cells asegs m1 (ATP + -164) [C4 errv]).
    { eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    apply (munch_add_errno sp) in MU1. unfold WSE in MU1.
    step_ecall. split.
    { at_nodeA_solve.
      all: try (change (to_bytes (map bv_unsigned name)) with (to_bytes (of_bytes name)); rewrite to_of_bytes).
      all: first [ exact NNUL | exact NS | exact ND1 | exact ND2 | exact NLM | rewrite unsigned_lit by lia; exact HNAME1 | rewrite unsigned_lit by lia; exact RGNAME
                 | (intros E; apply (f_equal (@length byte)) in E; cbn in E; lia)
                 | match goal with |- ?g => idtac "ATNODE:" g end ]. }
    intros rsp a Hdec. unfold dec_unlink in Hdec. apply dec_plain_Some in Hdec.
    destruct a as [e|v].
    - destruct Hdec as [-> HE]. unfold set_errno. apply implMG_upd_lc. apply implMG_ret. unfold efferr. sys_nret.
      eapply evtF_mono.
      { eapply (sysret_tail_GIA ra sp gp L RNG s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 s CL FB FL lo) with (r := errno_ret e) (errv := errv);
          first [ exact SPO | exact ERR | (left; reflexivity) | exact FR1 | exact ERR1 | exact ST1 | exact MI1 | exact MU1 | exact WM1
                | (exists e; left; split; [reflexivity | exact HE]) ]. }
      cbv beta. intros ms' PO. destruct PO as (a0v & m' & RG & MI' & ST' & AG' & G' & -> & ERR'). rewrite (errno_of_errno_ret e HE) in *.
      split; [apply fp_le_refl|].
      eexists _, m'. split; [exact RG|]. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG'|]. split; [exact G'|]. split; [reflexivity | right; reflexivity].
    - destruct Hdec as (-> & Hv & _). apply Z.eqb_eq in Hv. subst v. apply implMG_ret. unfold eff0. sys_nret.
      eapply evtF_mono.
      { eapply (sysret_tail_GIA ra sp gp L RNG s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 s CL FB FL lo) with (r := Z_to_bv 64 0) (errv := errv);
          first [ exact SPO | exact ERR | (left; reflexivity) | exact FR1 | exact ERR1 | exact ST1 | exact MI1 | exact MU1 | exact WM1
                | (exists 1; right; reflexivity) ]. }
      cbv beta. intros ms' PO. destruct PO as (a0v & m' & RG & MI' & ST' & AG' & G' & -> & ERR'). rewrite (errno_of_lit 0) in * by lia.
      rewrite set_libc_id in G'.
      split; [apply fp_le_refl|].
      eexists _, m'. split; [exact RG|]. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG'|]. split; [exact G'|]. split; [reflexivity | left; reflexivity].
  Qed.
  End Sz5.
  Theorem unlink_o_proofA : ltac:(let t := eval cbv delta [unlink_o_proofA__stmt] in unlink_o_proofA__stmt in exact t).
  Proof using GL GSL. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo NAME name. ltac2:(SecDiet.SzSec.closeP 'unlink_o_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition remove_o_proofA__stmt : Prop := remove_stmt_o GIOA.
  Section Sz6.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo NAME name : ltac2:(SecDiet.SzSec.tyM 'remove_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma remove_o_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'remove_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
 intros SPO -> HNAME NNUL NLEN NCR NOK.
 (* [comment removed for export] *)
 assert (NLENZ : (1 <= Z.of_nat (length name) <= 4095)%Z) by (clear - NLEN; lia). clear NLEN.
    pose proof SPO as (_ & _ & _ & _ & _ & _ & Etp & _). subst tp.
    destruct (sys_factsA _ _ _ _ _ _ _ _ _ SPO) as (G & ST & MI & LOA & LOB & SPT & TOP47 & RSTK & RIMG & GLO & (errv & ERR) & RERR & TPLOM & TP200M & ETP).
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (bytes_at_bound _ _ _ _ HNAME) as NB. rewrite length_app in NB. cbn [length] in NB.
    destruct (cobjA_factsA L RNG s CL FB FL m NAME (Z.of_nat (length name) + 1) lo G NCR ltac:(lia) LOA) as (N0 & NLO & _ & _ & _ & RGNAME & _).
    destruct NOK as (NS & ND1 & ND2 & NLM).
    unfold s_remove, Stdio.remove.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (QF := Q) end.
    (* [comment removed for export] *)
    assert (FIN : forall (r : word) (m1 : mem) (jk : list byte) (a2' : word),
      (exists e, (r = errno_ret e /\ 1 <= e <= 4095) \/ r = Z_to_bv 64 0) ->
      rw_cells asegs m1 (bv_unsigned sp + -16) [CB 8 jk; C8 ra] ->
      munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
      stk asegs m1 lo (bv_unsigned sp + -16) ->
      implMG RNG (match (match errno_of r with Some e => SErr e | None => SVal 0 end : sret) with
                  | SErr e => set_errno ps_libc set_libc e ;;; mret (-1) | SVal _ => mret 0 end) s QF
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 r (Z_to_bv 64 NAME) a2' (Z_to_bv 64 (-21)) a4 a5 a6 (Z_to_bv 64 35)
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x9ad8c) fc None m1 (seg_rom asegs))).
    { intros r m1 jk a2' HR FR1 MU1 WM1 MI1 ST1. subst QF.
      assert (ERR1 : rw_cells asegs m1 (ATP + -164) [C4 errv]).
      { eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
      apply (munch_add_errno sp) in MU1. unfold WSE in MU1.
      destruct HR as (e & [[-> HE] | ->]).
      - rewrite (errno_of_errno_ret e HE). unfold set_errno. apply implMG_upd_lc. apply implMG_ret.
        eapply evtF_mono.
        { eapply (sysret_tail_GIA ra sp gp L RNG s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 s CL FB FL lo) with (r := errno_ret e) (errv := errv);
            first [ exact SPO | exact ERR | (right; left; reflexivity) | exact FR1 | exact ERR1 | exact ST1 | exact MI1 | exact MU1 | exact WM1
                  | (exists e; left; split; [reflexivity | exact HE]) ]. }
        cbv beta. intros ms' PO. destruct PO as (a0v & m' & RG & MI' & ST' & AG' & G' & -> & ERR'). rewrite (errno_of_errno_ret e HE) in *.
        split; [apply fp_le_refl|].
        eexists _, m'. split; [exact RG|]. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG'|]. split; [exact G'|]. split; [reflexivity|].
        right. split; [reflexivity|]. cbn [ps_libc set_libc set_errno_lc lc_errno]. split; [exact ERR' | lia].
      - rewrite (errno_of_lit 0) by lia. apply implMG_ret.
        eapply evtF_mono.
        { eapply (sysret_tail_GIA ra sp gp L RNG s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 s CL FB FL lo) with (r := Z_to_bv 64 0) (errv := errv);
            first [ exact SPO | exact ERR | (right; left; reflexivity) | exact FR1 | exact ERR1 | exact ST1 | exact MI1 | exact MU1 | exact WM1
                  | (exists 1; right; reflexivity) ]. }
        cbv beta. intros ms' PO. destruct PO as (a0v & m' & RG & MI' & ST' & AG' & G' & -> & ERR'). rewrite (errno_of_lit 0) in * by lia.
        rewrite set_libc_id in G'.
        split; [apply fp_le_refl|].
        eexists _, m'. split; [exact RG|]. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG'|]. split; [exact G'|]. split; [reflexivity | left; reflexivity]. }
    (* [comment removed for export] *)
    apply implMG_sysk; [exact I|].
    eapply evtF_cut. { unfold REMOVE_ENTRY. eapply (remove_S1 RNG ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo); rewrite ?ETP; first [ exact RSTK | exact RERR | exact RIMG | lia ]. }
    cbv beta. intros ms1 ->.
    step_ecall. split.
    { at_nodeA_solve.
      all: try (change (to_bytes (map bv_unsigned name)) with (to_bytes (of_bytes name)); rewrite to_of_bytes).
      all: first [ exact NNUL | exact NS | exact ND1 | exact ND2 | exact NLM | rewrite unsigned_lit by lia; exact HNAME | rewrite unsigned_lit by lia; exact RGNAME
                 | (intros E; apply (f_equal (@length byte)) in E; cbn in E; lia)
                 | match goal with |- ?g => idtac "ATNODE1:" g end ]. }
    intros rsp a Hdec. unfold dec_unlink in Hdec. apply dec_plain_Some in Hdec.
    destruct a as [e|v].
    - destruct Hdec as [-> HE]. unfold efferr. sys_nret.
      destruct (Z.eqb_spec e EISDIR) as [E21|NE21].
      + (* [comment removed for export] *)
        subst e. cbv iota beta.
        apply implMG_sysk; [exact I|].
        eapply evtF_cut.
        { eapply (remove_S2 RNG ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo); rewrite ?ETP;
            first [ exact ST | exact MI | exact RSTK | exact RERR | exact RIMG | (exists EISDIR; left; split; [reflexivity | unfold EISDIR; lia]) | lia ]. }
        cbv beta. intros ms2 [[_ ->] | [NE _]]; [| exfalso; exact (NE eq_refl)].
        step_ecall. split.
        { at_nodeA_solve.
          all: try (change (to_bytes (map bv_unsigned name)) with (to_bytes (of_bytes name)); rewrite to_of_bytes).
          all: first [ exact NNUL | exact NS | exact ND1 | exact ND2 | exact NLM | rewrite unsigned_lit by lia; exact HNAME | rewrite unsigned_lit by lia; exact RGNAME
                     | (intros E; apply (f_equal (@length byte)) in E; cbn in E; lia)
                     | match goal with |- ?g => idtac "ATNODE2:" g end ]. }
        intros rsp2 a2x Hdec2. unfold dec_unlink in Hdec2. apply dec_plain_Some in Hdec2.
        assert (HR2 : exists (r2 : word) (e2 : Z), (a2x = SErr e2 /\ r2 = errno_ret e2 /\ 1 <= e2 <= 4095) \/ (a2x = SVal 0 /\ r2 = Z_to_bv 64 0)).
        { destruct a2x as [e2|v2]; [destruct Hdec2 as [-> HE2]; exists (errno_ret e2), e2; left; repeat split; try reflexivity; lia|].
          destruct Hdec2 as (-> & Hv & _). apply Z.eqb_eq in Hv. subst v2. exists (Z_to_bv 64 0), 1. right. split; reflexivity. }
        destruct HR2 as (r2 & e2 & [(-> & -> & HE2) | (-> & ->)]).
        * destruct Hdec2 as [-> _]. unfold efferr. sys_nret.
          eapply implMG_evtF.
          { eapply (remove_S3 RNG ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo); rewrite ?ETP;
              first [ exact ST | exact MI | exact RSTK | exact RERR | exact RIMG | (exists e2; left; split; [reflexivity | exact HE2]) | lia ]. }
          cbv beta. intros ms3 PO. destruct PO as (jk & m1 & -> & FR1 & MU1 & WM1 & MI1 & ST1).
          pose proof (FIN (errno_ret e2) m1 jk (Z_to_bv 64 512) ltac:(exists e2; left; split; [reflexivity | exact HE2]) FR1 MU1 WM1 MI1 ST1) as X.
          rewrite (errno_of_errno_ret e2 HE2) in X. exact X.
        * destruct Hdec2 as (-> & _). unfold eff0. sys_nret.
          eapply implMG_evtF.
          { eapply (remove_S3 RNG ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo); rewrite ?ETP;
              first [ exact ST | exact MI | exact RSTK | exact RERR | exact RIMG | (exists 1; right; reflexivity) | lia ]. }
          cbv beta. intros ms3 PO. destruct PO as (jk & m1 & -> & FR1 & MU1 & WM1 & MI1 & ST1).
          pose proof (FIN (Z_to_bv 64 0) m1 jk (Z_to_bv 64 512) ltac:(exists 1; right; reflexivity) FR1 MU1 WM1 MI1 ST1) as X.
          rewrite (errno_of_lit 0) in X by lia. exact X.
      + (* [comment removed for export] *)
        cbv iota beta. apply implMG_retb.
        eapply implMG_evtF.
        { eapply (remove_S2 RNG ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo); rewrite ?ETP;
            first [ exact ST | exact MI | exact RSTK | exact RERR | exact RIMG | (exists e; left; split; [reflexivity | exact HE]) | lia ]. }
        cbv beta. intros ms2 [[E _] | [_ PO]].
        { exfalso. apply NE21. pose proof (f_equal bv_unsigned E) as E'. rewrite !errno_ret_unsigned in E' by (unfold EISDIR; lia). unfold two_pow_64, EISDIR in *. lia. }
        destruct PO as (jk & m1 & a2' & -> & FR1 & MU1 & WM1 & MI1 & ST1).
        pose proof (FIN (errno_ret e) m1 jk a2' ltac:(exists e; left; split; [reflexivity | exact HE]) FR1 MU1 WM1 MI1 ST1) as X.
        rewrite (errno_of_errno_ret e HE) in X. exact X.
    - destruct Hdec as (-> & Hv & _). apply Z.eqb_eq in Hv. subst v. unfold eff0. sys_nret. apply implMG_retb.
      eapply implMG_evtF.
      { eapply (remove_S2 RNG ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo); rewrite ?ETP;
          first [ exact ST | exact MI | exact RSTK | exact RERR | exact RIMG | (exists 1; right; reflexivity) | lia ]. }
      cbv beta. intros ms2 [[E _] | [_ PO]].
      { exfalso. pose proof (f_equal bv_unsigned E) as E'. rewrite unsigned_lit, errno_ret_unsigned in E' by (unfold EISDIR; lia). unfold two_pow_64, EISDIR in *. lia. }
      destruct PO as (jk & m1 & a2' & -> & FR1 & MU1 & WM1 & MI1 & ST1).
      pose proof (FIN (Z_to_bv 64 0) m1 jk a2' ltac:(exists 1; right; reflexivity) FR1 MU1 WM1 MI1 ST1) as X.
      rewrite (errno_of_lit 0) in X by lia. exact X.
  Qed.
  End Sz6.
  Theorem remove_o_proofA : ltac:(let t := eval cbv delta [remove_o_proofA__stmt] in remove_o_proofA__stmt in exact t).
  Proof using GL GSL. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo NAME name. ltac2:(SecDiet.SzSec.closeP 'remove_o_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition close_o_proofA__stmt : Prop := close_stmt_o GIOA.
  Section Sz7.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo fd : ltac2:(SecDiet.SzSec.tyM 'close_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma close_o_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'close_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
 intros SPO -> FD.
    pose proof SPO as (_ & _ & _ & _ & _ & _ & Etp & _). subst tp.
    destruct (sys_factsA _ _ _ _ _ _ _ _ _ SPO) as (G & ST & MI & LOA & LOB & SPT & TOP47 & RSTK & RIMG & GLO & (errv & ERR) & RERR & TPLOM & TP200M & ETP).
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    unfold s_close, Stdio.close.
    apply implMG_sysk; [exact I|].
    eapply evtF_cut.
    { unfold CLOSE_ENTRY. eapply (close_S1 RNG ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo); rewrite ?ETP;
        first [ exact ST | exact MI | exact RSTK | exact RERR | exact RIMG | lia ]. }
    cbv beta. intros ms1 PO. destruct PO as (jk & m1 & -> & FR1 & MU1 & WM1 & MI1 & ST1).
    assert (ERR1 : rw_cells asegs m1 (ATP + -164) [C4 errv]).
    { eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    apply (munch_add_errno sp) in MU1. unfold WSE in MU1.
    step_ecall. split. { at_nodeA_solve. }
    intros rsp a Hdec. unfold dec_close_ok in Hdec.
    destruct (dec_close rsp) as [[e|v]|] eqn:E; try discriminate Hdec.
    unfold dec_close in E. apply dec_plain_Some in E. destruct E as (-> & Hv & _). apply Z.eqb_eq in Hv. subst v.
    apply implMG_ret. unfold eff0. sys_nret.
    eapply evtF_cut. { eapply (close_S2 RNG sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo); rewrite ?ETP; first [ exact RSTK | exact RERR | exact RIMG | lia ]. }
    cbv beta. intros ms2 [a1' ->].
    eapply evtF_mono.
    { eapply (sysret_tail_GIA ra sp gp L RNG s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 s CL FB FL lo) with (r := Z_to_bv 64 0) (errv := errv);
        first [ exact SPO | exact ERR | (right; right; reflexivity) | exact FR1 | exact ERR1 | exact ST1 | exact MI1 | exact MU1 | exact WM1
              | (exists 1; right; reflexivity) ]. }
    cbv beta. intros ms' PO. destruct PO as (a0v & m' & RG & MI' & ST' & AG' & G' & -> & ERR'). rewrite (errno_of_lit 0) in * by lia.
    rewrite set_libc_id in G'.
    split; [apply fp_le_refl|].
    eexists _, m'. split; [exact RG|]. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG'|]. exact G'.
  Qed.
  End Sz7.
  Theorem close_o_proofA : ltac:(let t := eval cbv delta [close_o_proofA__stmt] in close_o_proofA__stmt in exact t).
  Proof using GL GSL. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo fd. ltac2:(SecDiet.SzSec.closeP 'close_o_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End GlueSys.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_read__A3S.F_stdio_read.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_unlink.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioLawsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_foKitA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section GlueSys.
  Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GSL : gia_stdio_laws GIOA.

  #[local] Notation spo_factsA := (A3S.Stdio_glueA.TwB.spo_factsA GIOA GSL).
  #[local] Notation cobjA_factsA := (A3S.Stdio_glueA.TwB.cobjA_factsA FO GIOA fflagA GL).
  #[local] Notation GIOA_errno_step := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_foKitA.TwB.GIOA_errno_step FO GIOA fflagA GL GSL).

  (* [comment removed for export] *)
  Definition sysret_tail_GIA__stmt : Prop := forall (ra sp gp : word) L RNG (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m m1 : mem) (s : PS) (CL FB : list cblk) FL (lo : Z) (J : Z) (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 r errv : word) (jk : list byte),
    std_pre_o GIOA L RNG sp (Z_to_bv 64 ATP) s CL FB FL lo STDIO_STACK m ->
    rw_cells asegs m (ATP + -164) [C4 errv] ->
    (J = 0xa42dc \/ J = 0x9b170 \/ J = 0xa41ec) ->
    rw_cells asegs m1 (bv_unsigned sp + -16) [CB 8 jk; C8 ra] ->
    rw_cells asegs m1 (ATP + -164) [C4 errv] ->
    stk asegs m1 lo (bv_unsigned sp + -16) -> mem_inv asegs m1 ->
    munch [(bv_unsigned sp - 32, bv_unsigned sp); (ATP + -164, ATP + -160)] m m1 -> wmono asegs m m1 ->
    (exists e, (r = errno_ret e /\ 1 <= e <= 4095) \/ r = Z_to_bv 64 0) ->
    evtF asegs RNG (fun ms' => exists a0v m', hpost_regs ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
         /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
         /\ GIOA L RNG (set_libc (match errno_of r with Some e => set_errno_lc e (ps_libc s) | None => ps_libc s end) s) CL FB FL m'
         /\ a0v = Z_to_bv 64 (match errno_of r with Some _ => -1 | None => 0 end)
         /\ rw_cells asegs m' (ATP + -164) [C4 (match errno_of r with Some e => Z_to_bv 64 e | None => errv end)])
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 J) fc None m1 (seg_rom asegs)).
  Section Sz1.
  Variables ra sp gp L RNG s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 s CL FB FL lo J x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 r errv jk : ltac2:(SecDiet.SzSec.tyM 'sysret_tail_GIA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma sysret_tail_GIA__body : ltac2:(SecDiet.SzSec.bodyP 'sysret_tail_GIA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
 intros SPO ERR HJ FR1 ERR1 ST1 MI1 MU1 WM1 HR.
    pose proof (spo_factsA _ _ _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & _ & ENV & LOA & LOB & SPT & TOP47 & Etp & RSTK & RIMG & RTLS & KLO & GLO).
    unfold STDIO_STACK in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (@ATOP_lo rc) as ATL. pose proof (@atp_range rc tlsI) as (_ & TPlo & TPhi & TPimg).
    assert (ETP : bv_unsigned (Z_to_bv 64 ATP : word) = ATP) by (apply unsigned_lit; unfold ATP; lia).
    assert (RERR : rng RNG (ATP + -164) 4) by (eapply rng_sub'; [exact RTLS | unfold ATP; lia]).
    assert (TPLOM : ATP + -160 <= lo) by (unfold ATP in *; lia).
    assert (TP200M : 200 <= ATP) by (unfold ATP in *; lia).
    eapply evtF_mono.
    { eapply (sysret_tail RNG ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo errv) with (m0 := m) (J := J) (r := r);
        rewrite ?ETP;
        first [ exact HJ | exact FR1 | exact ERR1 | exact ST1 | exact MI1 | exact MU1 | exact WM1 | exact HR | exact RSTK | exact RERR | exact RIMG | exact GLO
              | exact TPLOM | exact TP200M | lia | match goal with |- ?g => idtac "TL side:" g end ]. }
    cbv beta. intros ms' PO. destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m' & -> & MU' & WM' & MI' & ST' & ERR').
    rewrite ETP in MU', ERR'.
    destruct (GIOA_errno_step L RNG s CL FB FL m m' _ (bv_unsigned sp) (match errno_of r with Some e => set_errno_lc e (ps_libc s) | None => ps_libc s end)
                (match errno_of r with Some e => Z_to_bv 64 e | None => errv end) G MU' WM') as [G' AG'];
      [ apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_cons; [right; cbn [fst snd]; lia | apply Forall_nil]]
      | lia | exact ERR' | destruct (errno_of r); reflexivity | destruct (errno_of r); reflexivity | destruct (errno_of r); reflexivity | ].
    eexists _, m'. split; [unfold hpost_regs; repeat eexists; reflexivity|].
    split; [exact MI'|]. split; [exact ST'|]. split; [exact AG'|]. split; [exact G'|]. split; [reflexivity | exact ERR'].
  Qed.
  End Sz1.
  Lemma sysret_tail_GIA : ltac:(let t := eval cbv delta [sysret_tail_GIA__stmt] in sysret_tail_GIA__stmt in exact t).
  Proof using GL GSL. intros ra sp gp L RNG s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 s CL FB FL lo J x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 r errv jk. ltac2:(SecDiet.SzSec.closeP 'sysret_tail_GIA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma set_libc_id : forall s : PS, set_libc (ps_libc s) s = s.
  Proof using Type. pin_using tt. intros s. destruct s; reflexivity. Qed.

  #[local] Definition WSE (sp : word) : list (Z * Z) := [(bv_unsigned sp - 32, bv_unsigned sp); (ATP + -164, ATP + -160)].
  Lemma munch_add_errno : forall (sp : word) m m1, munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m1 -> munch (WSE sp) m m1.
  Proof using Type. pin_using tt. intros sp m m1 MU. eapply munch_weaken; [| exact MU]. unfold sub_fp, WSE. cbn [outside]. intros x (O1 & O2 & _). split; [exact O1 | exact I]. Qed.

  (* [comment removed for export] *)
  Definition sys_factsA__stmt : Prop := forall L RNG (sp : word) (s : PS) CL FB FL lo m,
    std_pre_o GIOA L RNG sp (Z_to_bv 64 ATP) s CL FB FL lo STDIO_STACK m ->
    GIOA L RNG s CL FB FL m /\ stk asegs m lo (bv_unsigned sp) /\ mem_inv asegs m /\ ATOP + 4096 <= lo /\ lo + 0x4000 <= bv_unsigned sp
    /\ bv_unsigned sp + 16 < al_top L /\ al_top L <= 2^47 /\ rng RNG lo (bv_unsigned sp - lo) /\ rng_aimg RNG /\ 0x604000 <= lo
    /\ (exists errv : word, rw_cells asegs m (ATP + -164) [C4 errv]) /\ rng RNG (ATP + -164) 4 /\ ATP + -160 <= lo /\ 200 <= ATP
    /\ bv_unsigned (Z_to_bv 64 ATP : word) = ATP.
  Section Sz4.
  Variables L RNG sp s CL FB FL lo m : ltac2:(SecDiet.SzSec.tyM 'sys_factsA__stmt "vvvvvvvvv" @L).
  Lemma sys_factsA__body : ltac2:(SecDiet.SzSec.bodyP 'sys_factsA__stmt "vvvvvvvvv").
  Proof using GSL. pin_using (fun (GSL : unit) => tt).
    intros SPO.
    pose proof (spo_factsA _ _ _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & _ & ENV & LOA & LOB & SPT & TOP47 & Etp & RSTK & RIMG & RTLS & KLO & GLO).
    unfold STDIO_STACK in *.
    pose proof (@ATOP_lo rc) as ATL. pose proof (@atp_range rc tlsI) as (_ & TPlo & TPhi & TPimg).
    repeat (split; [first [assumption | exact (gs_errno _ GSL _ _ _ _ _ _ _ G) | (eapply rng_sub'; [exact RTLS | unfold ATP; lia]) | (unfold ATP in *; lia)]|]).
    apply unsigned_lit. unfold ATP. lia.
  Qed.
  End Sz4.
  Lemma sys_factsA : ltac:(let t := eval cbv delta [sys_factsA__stmt] in sys_factsA__stmt in exact t).
  Proof using GSL. intros L RNG sp s CL FB FL lo m. ltac2:(SecDiet.SzSec.closeP 'sys_factsA__body "vvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition unlink_o_proofA__stmt : Prop := unlink_stmt_o GIOA.
  Section Sz5.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo NAME name : ltac2:(SecDiet.SzSec.tyM 'unlink_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma unlink_o_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'unlink_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
 intros SPO -> HNAME NNUL NLEN NCR NOK.
 (* [comment removed for export] *)
 assert (NLENZ : (1 <= Z.of_nat (length name) <= 4095)%Z) by (clear - NLEN; lia). clear NLEN.
    pose proof SPO as (_ & _ & _ & _ & _ & _ & Etp & _). subst tp.
    destruct (sys_factsA _ _ _ _ _ _ _ _ _ SPO) as (G & ST & MI & LOA & LOB & SPT & TOP47 & RSTK & RIMG & GLO & (errv & ERR) & RERR & TPLOM & TP200M & ETP).
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (bytes_at_bound _ _ _ _ HNAME) as NB. rewrite length_app in NB. cbn [length] in NB.
    destruct (cobjA_factsA L RNG s CL FB FL m NAME (Z.of_nat (length name) + 1) lo G NCR ltac:(lia) LOA) as (N0 & NLO & _ & _ & _ & RGNAME & _).
    destruct NOK as (NS & ND1 & ND2 & NLM).
    unfold s_unlink, Stdio.unlink.
    apply implMG_sysk; [exact I|].
    eapply evtF_cut.
    { unfold UNLINK_ENTRY. eapply (unlink_S1 RNG ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo); rewrite ?ETP;
        first [ exact ST | exact MI | exact RSTK | exact RERR | exact RIMG | lia ]. }
    cbv beta. intros ms1 PO. destruct PO as (jk & m1 & -> & FR1 & MU1 & WM1 & MI1 & ST1).
    assert (HNAME1 : bytes_at asegs m1 NAME (name ++ [Z_to_bv 8 0])).
    { eapply bytes_at_transport; [exact HNAME | exact MU1 |]. cbn [disjoint_from]. rewrite length_app. cbn [length]. lia. }
    assert (ERR1 : rw_cells asegs m1 (ATP + -164) [C4 errv]).
    { eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    apply (munch_add_errno sp) in MU1. unfold WSE in MU1.
    step_ecall. split.
    { at_nodeA_solve.
      all: try (change (to_bytes (map bv_unsigned name)) with (to_bytes (of_bytes name)); rewrite to_of_bytes).
      all: first [ exact NNUL | exact NS | exact ND1 | exact ND2 | exact NLM | rewrite unsigned_lit by lia; exact HNAME1 | rewrite unsigned_lit by lia; exact RGNAME
                 | (intros E; apply (f_equal (@length byte)) in E; cbn in E; lia)
                 | match goal with |- ?g => idtac "ATNODE:" g end ]. }
    intros rsp a Hdec. unfold dec_unlink in Hdec. apply dec_plain_Some in Hdec.
    destruct a as [e|v].
    - destruct Hdec as [-> HE]. unfold set_errno. apply implMG_upd_lc. apply implMG_ret. unfold efferr. sys_nret.
      eapply evtF_mono.
      { eapply (sysret_tail_GIA ra sp gp L RNG s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 s CL FB FL lo) with (r := errno_ret e) (errv := errv);
          first [ exact SPO | exact ERR | (left; reflexivity) | exact FR1 | exact ERR1 | exact ST1 | exact MI1 | exact MU1 | exact WM1
                | (exists e; left; split; [reflexivity | exact HE]) ]. }
      cbv beta. intros ms' PO. destruct PO as (a0v & m' & RG & MI' & ST' & AG' & G' & -> & ERR'). rewrite (errno_of_errno_ret e HE) in *.
      split; [apply fp_le_refl|].
      eexists _, m'. split; [exact RG|]. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG'|]. split; [exact G'|]. split; [reflexivity | right; reflexivity].
    - destruct Hdec as (-> & Hv & _). apply Z.eqb_eq in Hv. subst v. apply implMG_ret. unfold eff0. sys_nret.
      eapply evtF_mono.
      { eapply (sysret_tail_GIA ra sp gp L RNG s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 s CL FB FL lo) with (r := Z_to_bv 64 0) (errv := errv);
          first [ exact SPO | exact ERR | (left; reflexivity) | exact FR1 | exact ERR1 | exact ST1 | exact MI1 | exact MU1 | exact WM1
                | (exists 1; right; reflexivity) ]. }
      cbv beta. intros ms' PO. destruct PO as (a0v & m' & RG & MI' & ST' & AG' & G' & -> & ERR'). rewrite (errno_of_lit 0) in * by lia.
      rewrite set_libc_id in G'.
      split; [apply fp_le_refl|].
      eexists _, m'. split; [exact RG|]. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG'|]. split; [exact G'|]. split; [reflexivity | left; reflexivity].
  Qed.
  End Sz5.
  Theorem unlink_o_proofA : ltac:(let t := eval cbv delta [unlink_o_proofA__stmt] in unlink_o_proofA__stmt in exact t).
  Proof using GL GSL. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo NAME name. ltac2:(SecDiet.SzSec.closeP 'unlink_o_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition remove_o_proofA__stmt : Prop := remove_stmt_o GIOA.
  Section Sz6.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo NAME name : ltac2:(SecDiet.SzSec.tyM 'remove_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma remove_o_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'remove_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
 intros SPO -> HNAME NNUL NLEN NCR NOK.
 (* [comment removed for export] *)
 assert (NLENZ : (1 <= Z.of_nat (length name) <= 4095)%Z) by (clear - NLEN; lia). clear NLEN.
    pose proof SPO as (_ & _ & _ & _ & _ & _ & Etp & _). subst tp.
    destruct (sys_factsA _ _ _ _ _ _ _ _ _ SPO) as (G & ST & MI & LOA & LOB & SPT & TOP47 & RSTK & RIMG & GLO & (errv & ERR) & RERR & TPLOM & TP200M & ETP).
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (bytes_at_bound _ _ _ _ HNAME) as NB. rewrite length_app in NB. cbn [length] in NB.
    destruct (cobjA_factsA L RNG s CL FB FL m NAME (Z.of_nat (length name) + 1) lo G NCR ltac:(lia) LOA) as (N0 & NLO & _ & _ & _ & RGNAME & _).
    destruct NOK as (NS & ND1 & ND2 & NLM).
    unfold s_remove, Stdio.remove.
    lazymatch goal with |- implMG _ _ _ ?Q _ => set (QF := Q) end.
    (* [comment removed for export] *)
    assert (FIN : forall (r : word) (m1 : mem) (jk : list byte) (a2' : word),
      (exists e, (r = errno_ret e /\ 1 <= e <= 4095) \/ r = Z_to_bv 64 0) ->
      rw_cells asegs m1 (bv_unsigned sp + -16) [CB 8 jk; C8 ra] ->
      munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
      stk asegs m1 lo (bv_unsigned sp + -16) ->
      implMG RNG (match (match errno_of r with Some e => SErr e | None => SVal 0 end : sret) with
                  | SErr e => set_errno ps_libc set_libc e ;;; mret (-1) | SVal _ => mret 0 end) s QF
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 r (Z_to_bv 64 NAME) a2' (Z_to_bv 64 (-21)) a4 a5 a6 (Z_to_bv 64 35)
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x9b170) fc None m1 (seg_rom asegs))).
    { intros r m1 jk a2' HR FR1 MU1 WM1 MI1 ST1. subst QF.
      assert (ERR1 : rw_cells asegs m1 (ATP + -164) [C4 errv]).
      { eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
      apply (munch_add_errno sp) in MU1. unfold WSE in MU1.
      destruct HR as (e & [[-> HE] | ->]).
      - rewrite (errno_of_errno_ret e HE). unfold set_errno. apply implMG_upd_lc. apply implMG_ret.
        eapply evtF_mono.
        { eapply (sysret_tail_GIA ra sp gp L RNG s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 s CL FB FL lo) with (r := errno_ret e) (errv := errv);
            first [ exact SPO | exact ERR | (right; left; reflexivity) | exact FR1 | exact ERR1 | exact ST1 | exact MI1 | exact MU1 | exact WM1
                  | (exists e; left; split; [reflexivity | exact HE]) ]. }
        cbv beta. intros ms' PO. destruct PO as (a0v & m' & RG & MI' & ST' & AG' & G' & -> & ERR'). rewrite (errno_of_errno_ret e HE) in *.
        split; [apply fp_le_refl|].
        eexists _, m'. split; [exact RG|]. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG'|]. split; [exact G'|]. split; [reflexivity|].
        right. split; [reflexivity|]. cbn [ps_libc set_libc set_errno_lc lc_errno]. split; [exact ERR' | lia].
      - rewrite (errno_of_lit 0) by lia. apply implMG_ret.
        eapply evtF_mono.
        { eapply (sysret_tail_GIA ra sp gp L RNG s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 s CL FB FL lo) with (r := Z_to_bv 64 0) (errv := errv);
            first [ exact SPO | exact ERR | (right; left; reflexivity) | exact FR1 | exact ERR1 | exact ST1 | exact MI1 | exact MU1 | exact WM1
                  | (exists 1; right; reflexivity) ]. }
        cbv beta. intros ms' PO. destruct PO as (a0v & m' & RG & MI' & ST' & AG' & G' & -> & ERR'). rewrite (errno_of_lit 0) in * by lia.
        rewrite set_libc_id in G'.
        split; [apply fp_le_refl|].
        eexists _, m'. split; [exact RG|]. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG'|]. split; [exact G'|]. split; [reflexivity | left; reflexivity]. }
    (* [comment removed for export] *)
    apply implMG_sysk; [exact I|].
    eapply evtF_cut. { unfold REMOVE_ENTRY. eapply (remove_S1 RNG ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo); rewrite ?ETP; first [ exact RSTK | exact RERR | exact RIMG | lia ]. }
    cbv beta. intros ms1 ->.
    step_ecall. split.
    { at_nodeA_solve.
      all: try (change (to_bytes (map bv_unsigned name)) with (to_bytes (of_bytes name)); rewrite to_of_bytes).
      all: first [ exact NNUL | exact NS | exact ND1 | exact ND2 | exact NLM | rewrite unsigned_lit by lia; exact HNAME | rewrite unsigned_lit by lia; exact RGNAME
                 | (intros E; apply (f_equal (@length byte)) in E; cbn in E; lia)
                 | match goal with |- ?g => idtac "ATNODE1:" g end ]. }
    intros rsp a Hdec. unfold dec_unlink in Hdec. apply dec_plain_Some in Hdec.
    destruct a as [e|v].
    - destruct Hdec as [-> HE]. unfold efferr. sys_nret.
      destruct (Z.eqb_spec e EISDIR) as [E21|NE21].
      + (* [comment removed for export] *)
        subst e. cbv iota beta.
        apply implMG_sysk; [exact I|].
        eapply evtF_cut.
        { eapply (remove_S2 RNG ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo); rewrite ?ETP;
            first [ exact ST | exact MI | exact RSTK | exact RERR | exact RIMG | (exists EISDIR; left; split; [reflexivity | unfold EISDIR; lia]) | lia ]. }
        cbv beta. intros ms2 [[_ ->] | [NE _]]; [| exfalso; exact (NE eq_refl)].
        step_ecall. split.
        { at_nodeA_solve.
          all: try (change (to_bytes (map bv_unsigned name)) with (to_bytes (of_bytes name)); rewrite to_of_bytes).
          all: first [ exact NNUL | exact NS | exact ND1 | exact ND2 | exact NLM | rewrite unsigned_lit by lia; exact HNAME | rewrite unsigned_lit by lia; exact RGNAME
                     | (intros E; apply (f_equal (@length byte)) in E; cbn in E; lia)
                     | match goal with |- ?g => idtac "ATNODE2:" g end ]. }
        intros rsp2 a2x Hdec2. unfold dec_unlink in Hdec2. apply dec_plain_Some in Hdec2.
        assert (HR2 : exists (r2 : word) (e2 : Z), (a2x = SErr e2 /\ r2 = errno_ret e2 /\ 1 <= e2 <= 4095) \/ (a2x = SVal 0 /\ r2 = Z_to_bv 64 0)).
        { destruct a2x as [e2|v2]; [destruct Hdec2 as [-> HE2]; exists (errno_ret e2), e2; left; repeat split; try reflexivity; lia|].
          destruct Hdec2 as (-> & Hv & _). apply Z.eqb_eq in Hv. subst v2. exists (Z_to_bv 64 0), 1. right. split; reflexivity. }
        destruct HR2 as (r2 & e2 & [(-> & -> & HE2) | (-> & ->)]).
        * destruct Hdec2 as [-> _]. unfold efferr. sys_nret.
          eapply implMG_evtF.
          { eapply (remove_S3 RNG ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo); rewrite ?ETP;
              first [ exact ST | exact MI | exact RSTK | exact RERR | exact RIMG | (exists e2; left; split; [reflexivity | exact HE2]) | lia ]. }
          cbv beta. intros ms3 PO. destruct PO as (jk & m1 & -> & FR1 & MU1 & WM1 & MI1 & ST1).
          pose proof (FIN (errno_ret e2) m1 jk (Z_to_bv 64 512) ltac:(exists e2; left; split; [reflexivity | exact HE2]) FR1 MU1 WM1 MI1 ST1) as X.
          rewrite (errno_of_errno_ret e2 HE2) in X. exact X.
        * destruct Hdec2 as (-> & _). unfold eff0. sys_nret.
          eapply implMG_evtF.
          { eapply (remove_S3 RNG ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo); rewrite ?ETP;
              first [ exact ST | exact MI | exact RSTK | exact RERR | exact RIMG | (exists 1; right; reflexivity) | lia ]. }
          cbv beta. intros ms3 PO. destruct PO as (jk & m1 & -> & FR1 & MU1 & WM1 & MI1 & ST1).
          pose proof (FIN (Z_to_bv 64 0) m1 jk (Z_to_bv 64 512) ltac:(exists 1; right; reflexivity) FR1 MU1 WM1 MI1 ST1) as X.
          rewrite (errno_of_lit 0) in X by lia. exact X.
      + (* [comment removed for export] *)
        cbv iota beta. apply implMG_retb.
        eapply implMG_evtF.
        { eapply (remove_S2 RNG ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo); rewrite ?ETP;
            first [ exact ST | exact MI | exact RSTK | exact RERR | exact RIMG | (exists e; left; split; [reflexivity | exact HE]) | lia ]. }
        cbv beta. intros ms2 [[E _] | [_ PO]].
        { exfalso. apply NE21. pose proof (f_equal bv_unsigned E) as E'. rewrite !errno_ret_unsigned in E' by (unfold EISDIR; lia). unfold two_pow_64, EISDIR in *. lia. }
        destruct PO as (jk & m1 & a2' & -> & FR1 & MU1 & WM1 & MI1 & ST1).
        pose proof (FIN (errno_ret e) m1 jk a2' ltac:(exists e; left; split; [reflexivity | exact HE]) FR1 MU1 WM1 MI1 ST1) as X.
        rewrite (errno_of_errno_ret e HE) in X. exact X.
    - destruct Hdec as (-> & Hv & _). apply Z.eqb_eq in Hv. subst v. unfold eff0. sys_nret. apply implMG_retb.
      eapply implMG_evtF.
      { eapply (remove_S2 RNG ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo); rewrite ?ETP;
          first [ exact ST | exact MI | exact RSTK | exact RERR | exact RIMG | (exists 1; right; reflexivity) | lia ]. }
      cbv beta. intros ms2 [[E _] | [_ PO]].
      { exfalso. pose proof (f_equal bv_unsigned E) as E'. rewrite unsigned_lit, errno_ret_unsigned in E' by (unfold EISDIR; lia). unfold two_pow_64, EISDIR in *. lia. }
      destruct PO as (jk & m1 & a2' & -> & FR1 & MU1 & WM1 & MI1 & ST1).
      pose proof (FIN (Z_to_bv 64 0) m1 jk a2' ltac:(exists 1; right; reflexivity) FR1 MU1 WM1 MI1 ST1) as X.
      rewrite (errno_of_lit 0) in X by lia. exact X.
  Qed.
  End Sz6.
  Theorem remove_o_proofA : ltac:(let t := eval cbv delta [remove_o_proofA__stmt] in remove_o_proofA__stmt in exact t).
  Proof using GL GSL. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo NAME name. ltac2:(SecDiet.SzSec.closeP 'remove_o_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition close_o_proofA__stmt : Prop := close_stmt_o GIOA.
  Section Sz7.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo fd : ltac2:(SecDiet.SzSec.tyM 'close_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma close_o_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'close_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
 intros SPO -> FD.
    pose proof SPO as (_ & _ & _ & _ & _ & _ & Etp & _). subst tp.
    destruct (sys_factsA _ _ _ _ _ _ _ _ _ SPO) as (G & ST & MI & LOA & LOB & SPT & TOP47 & RSTK & RIMG & GLO & (errv & ERR) & RERR & TPLOM & TP200M & ETP).
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    unfold s_close, Stdio.close.
    apply implMG_sysk; [exact I|].
    eapply evtF_cut.
    { unfold CLOSE_ENTRY. eapply (close_S1 RNG ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo); rewrite ?ETP;
        first [ exact ST | exact MI | exact RSTK | exact RERR | exact RIMG | lia ]. }
    cbv beta. intros ms1 PO. destruct PO as (jk & m1 & -> & FR1 & MU1 & WM1 & MI1 & ST1).
    assert (ERR1 : rw_cells asegs m1 (ATP + -164) [C4 errv]).
    { eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    apply (munch_add_errno sp) in MU1. unfold WSE in MU1.
    step_ecall. split. { at_nodeA_solve. }
    intros rsp a Hdec. unfold dec_close_ok in Hdec.
    destruct (dec_close rsp) as [[e|v]|] eqn:E; try discriminate Hdec.
    unfold dec_close in E. apply dec_plain_Some in E. destruct E as (-> & Hv & _). apply Z.eqb_eq in Hv. subst v.
    apply implMG_ret. unfold eff0. sys_nret.
    eapply evtF_cut. { eapply (close_S2 RNG sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo); rewrite ?ETP; first [ exact RSTK | exact RERR | exact RIMG | lia ]. }
    cbv beta. intros ms2 [a1' ->].
    eapply evtF_mono.
    { eapply (sysret_tail_GIA ra sp gp L RNG s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 s CL FB FL lo) with (r := Z_to_bv 64 0) (errv := errv);
        first [ exact SPO | exact ERR | (right; right; reflexivity) | exact FR1 | exact ERR1 | exact ST1 | exact MI1 | exact MU1 | exact WM1
              | (exists 1; right; reflexivity) ]. }
    cbv beta. intros ms' PO. destruct PO as (a0v & m' & RG & MI' & ST' & AG' & G' & -> & ERR'). rewrite (errno_of_lit 0) in * by lia.
    rewrite set_libc_id in G'.
    split; [apply fp_le_refl|].
    eexists _, m'. split; [exact RG|]. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AG'|]. exact G'.
  Qed.
  End Sz7.
  Theorem close_o_proofA : ltac:(let t := eval cbv delta [close_o_proofA__stmt] in close_o_proofA__stmt in exact t).
  Proof using GL GSL. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo fd. ltac2:(SecDiet.SzSec.closeP 'close_o_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End GlueSys.
End TwB.
End Stdio_glue_sysA.

(* [comment removed for export] *)
Module Stdio_glue_mkA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw ExecF ITreeA Shadow StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABase AMalloc_iface RtCells. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require MonadF. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require PcapRepA Pcap_ifaceA Fuzz_ifaceA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_read__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_mkstemp__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA Stdio_glueKitA StdioLawsA Stdio_glueA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_read__A3S.F_stdio_read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_mkstemp__A3S.F_mkstemp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioLawsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_foKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_sysA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section GlueMk.
  Context {rc : runConstT} {tlsI : ABase.atlsT}.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GSL : gia_stdio_laws GIOA.

  #[local] Notation spo_factsA := (Stdio_glueA.spo_factsA GIOA GSL).
  #[local] Notation cobjA_factsA := (Stdio_glueA.cobjA_factsA FO GIOA fflagA GL).
  #[local] Notation clocA_factsA := (Stdio_glueA.clocA_factsA FO GIOA fflagA GL).
  #[local] Notation sys_factsA := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_sysA.sys_factsA GIOA GSL).

  (* [comment removed for export] *)
  Lemma tmpl_Z : map bv_unsigned (map PcapRepA.b8 TEMPLATE) = TEMPLATE.
  Proof using Type. pin_using tt. vm_compute. reflexivity. Qed.
  Lemma tmpl_TMPL0 : map PcapRepA.b8 TEMPLATE ++ [Z_to_bv 8 0] = TMPL0.
  Proof using Type. pin_using tt. vm_compute. reflexivity. Qed.
  Lemma tmpl_len : length (map PcapRepA.b8 TEMPLATE) = 29%nat.
  Proof using Type. pin_using tt. reflexivity. Qed.
  Lemma seal_TEMPLATE : seal_name TEMPLATE = Some TMPNAME.
  Proof using Type. pin_using tt. vm_compute. reflexivity. Qed.
  Lemma tmpn_bytes : TMPN0 = map PcapRepA.b8 TMPNAME ++ [Z_to_bv 8 0].
  Proof using Type. pin_using tt. vm_compute. reflexivity. Qed.
  Lemma tmpn_tobytes : to_bytes TMPNAME = TMPN.
  Proof using Type. pin_using tt. vm_compute. reflexivity. Qed.
  Lemma TMPN0_len : length TMPN0 = 25%nat.
  Proof using Type. pin_using tt. reflexivity. Qed.
  Lemma TMPN_nonul : ~ In (Z_to_bv 8 0) TMPN.
  Proof using Type. pin_using tt. unfold TMPN, TMPNAME. cbn. intuition discriminate. Qed.
  Lemma TMPNAME_range : Forall (fun z => 0 < z < 256) TMPNAME.
  Proof using Type. pin_using tt. unfold TMPNAME. cbn. repeat (constructor; [lia|]). constructor. Qed.
  Lemma TMPNAME_len : length TMPNAME = 24%nat.
  Proof using Type. pin_using tt. reflexivity. Qed.
  Lemma TMPNAME_path : Namei.path_has_slash (map PcapRepA.b8 TMPNAME) = false
                       /\ map PcapRepA.b8 TMPNAME <> Uapi.dot_path /\ map PcapRepA.b8 TMPNAME <> Namei.dotdot_path.
  Proof using Type. pin_using tt.
    split; [vm_compute; reflexivity|].
    split; intros E; apply (f_equal (@length byte)) in E; vm_compute in E; discriminate E.
  Qed.

  (* [comment removed for export] *)
  Definition GIOA_errno_step_x__stmt : Prop := forall L RNG (s : PS) CL FB FL m m' W SP D n (l' : libc_st hptr) (e' : word),
    GIOA L RNG s CL FB FL m -> munch (W ++ [(D, D + n)]) m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => (ATOP + 4096 <= fst iv /\ snd iv <= SP) \/ (ATP + -164 <= fst iv /\ snd iv <= ATP + -160)) W -> ATOP + 4096 <= SP ->
    clocA FL CL D n -> 0 <= n ->
    rw_cells asegs m' (ATP + -164) [C4 e'] ->
    lc_stdout l' = lc_stdout (ps_libc s) -> lc_stderr l' = lc_stderr (ps_libc s) -> lc_files l' = lc_files (ps_libc s) ->
    GIOA L RNG (set_libc l' s) CL FB FL m' /\ agrees_on (fun a => client_keeps FL CL SP a /\ ~ (D <= a < D + n)) m m'.
  Section Sz12.
  Variables L RNG s CL FB FL m m' W SP D n l' e' : ltac2:(SecDiet.SzSec.tyM 'GIOA_errno_step_x__stmt "vvvvvvvvvvvvvv" @L).
  Lemma GIOA_errno_step_x__body : ltac2:(SecDiet.SzSec.bodyP 'GIOA_errno_step_x__stmt "vvvvvvvvvvvvvv").
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
    intros G MU WM HW HSP LOC Hn ERR' E1 E2 E3.
    assert (HW' : Forall (stdio_ivA FB SP) W).
    { eapply Forall_impl; [| exact HW]. intros iv [X|X]; [left; exact X | right; right; right; right; exact X]. }
    pose proof (gs_stdio _ GSL _ _ _ _ _ _ _ G) as SR.
    destruct (clocA_factsA _ _ _ _ _ _ _ D n G LOC Hn) as (X1 & X2 & X3).
    split.
    - eapply (gs_step _ GSL L RNG s CL FB FL m m' W [(D, D + n)] SP l'); [exact G | exact MU | exact WM | exact HW' | | exact HSP | exists e'; exact ERR' |].
      { apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. replace (D + n - D) with n by lia. exact LOC. }
      assert (SR' : STDIOR l' FB m) by (unfold STDIOR in SR |- *; rewrite E1, E2, E3; exact SR).
      eapply (STDIOR_agree l' FB m m' (fun a => stdio_static a \/ in_block FB a)); [exact SR' | | intros a Ha; left; exact Ha | intros a Ha; right; exact Ha].
      eapply agrees_on_of_munch; [exact MU | exact WM |]. intros a Ha Hc.
      pose proof (@ATPv_hi rc tlsI) as TH. pose proof (@ATPv_imgk rc tlsI) as (TI1 & TI2). pose proof (@kt_rng rc tlsI) as ((KI & _) & _).
      pose proof (@ATOP_lo rc) as ATL.
      assert (NT : ~ (ATP + -164 <= a < ATP + -160) /\ a < ATOP + 4096 /\ ~ (D <= a < D + n)).
      { destruct Hc as [Hs | Hb].
        - unfold stdio_static in Hs. unfold ATP. clear - Hs TH TI1 TI2 KI ATL X1. lia.
        - split; [| split].
          + intros X. assert (HB' : in_block (CL ++ FB) a) by (apply in_block_app; right; exact Hb).
            apply (gl_tls_apart _ _ _ GL _ _ _ _ _ _ _ a G (or_introl HB')). clear - X. lia.
          + apply in_block_In in Hb as (b & HIN & HR).
            pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ b G ltac:(apply in_or_app; right; exact HIN)) as ((_ & _ & TOP & _) & _). clear - HR TOP. lia.
          + intros HD. apply in_block_In in Hb as (b & HIN & HR).
            destruct LOC as [(b' & HB' & B1 & B2) | (fr & HF & F1 & F2)].
            * destruct (blocks_apart_app_inv _ _ (gl_apart _ _ _ GL _ _ _ _ _ _ _ G)) as (_ & _ & AP).
              specialize (AP b' b HB' HIN). unfold apart in AP. clear - AP HR HD B1 B2. lia.
            * apply (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G).
              -- apply in_frames_In. exists fr. split; [exact HF | clear - HD F1 F2; lia].
              -- apply in_block_In. exists b. split; [apply in_or_app; right; exact HIN | exact HR]. }
      destruct NT as (NT1 & NT2 & NT3). apply outside_app. split.
      + clear - HW NT1 NT2. induction HW as [|[lo hi] W Hiv HW IH]; cbn [outside]; [exact I|]. split; [| exact IH]. cbn [fst snd] in Hiv. lia.
      + cbn [outside]. split; [exact NT3 | exact I].
    - eapply agrees_on_weaken; [eapply (gs_keeps _ GSL L RNG s CL FB FL m m' W [(D, D + n)] SP); [exact G | exact MU | exact WM | exact HW' | exact HSP]|].
      intros a [Ha Hn']. split; [exact Ha |]. cbn [outside]. split; [exact Hn' | exact I].
  Qed.
  End Sz12.
  Lemma GIOA_errno_step_x : ltac:(let t := eval cbv delta [GIOA_errno_step_x__stmt] in GIOA_errno_step_x__stmt in exact t).
  Proof using GL GSL. intros L RNG s CL FB FL m m' W SP D n l' e'. ltac2:(SecDiet.SzSec.closeP 'GIOA_errno_step_x__body "vvvvvvvvvvvvvv"). Qed.
  Definition mkstemp_o_proofA__stmt : Prop := mkstemp_stmt_o GIOA.
  Section Sz13.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo NAME n tmpl buf : ltac2:(SecDiet.SzSec.tyM 'mkstemp_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma mkstemp_o_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'mkstemp_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
 intros SPO -> BUF FST NNUL -> NLE NMAX NCR.
 (* [comment removed for export] *)
 assert (NMAXZ : (Z.of_nat n <= 4096)%Z) by (clear - NMAX; lia). clear NMAX.
    pose proof SPO as (_ & _ & _ & _ & _ & _ & Etp & _ & (_ & _ & RIMGSH & _)). subst tp.
    destruct (sys_factsA _ _ _ _ _ _ _ _ _ SPO) as (G & ST & MI & LOA & LOB & SPT & TOP47 & RSTK & RIMG & GLO & (errv & ERR) & RERR & TPLOM & TP200M & ETP).
    pose proof (spo_factsA _ _ _ _ _ _ _ _ _ _ _ SPO) as (_ & _ & _ & _ & (canary & (GOT & GUARD)) & ENV & _ & _ & _ & _ & _ & _ & _ & _ & KLO & _).
    unfold STDIO_STACK in *. rewrite tmpl_len in NLE, FST.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (@ATOP_lo rc) as ATL. pose proof (@atp_range rc tlsI) as (_ & TPlo & TPhi & TPimg).
    assert (TPRM : ATP = 0x5e15b8) by (unfold ATP in *; lia).
    destruct (cobjA_factsA L RNG s CL FB FL m NAME (Z.of_nat n) lo G NCR ltac:(lia) LOA) as (N0 & NLO & N5E & N47 & SON & RGNAME & IESN & _).
    pose proof (sobj_appW _ _ _ _ SON) as APWN.
    (* [comment removed for export] *)
    assert (NTLS : NAME + Z.of_nat n <= ATP + -200 \/ ATP + 304 <= NAME).
    { destruct NCR as [LOC _].
      destruct (Z_lt_le_dec (Z.max NAME (ATP + -200)) (Z.min (NAME + Z.of_nat n) (ATP + 304))) as [LT|GE]; [| lia].
      exfalso. apply (gl_tls_apart _ _ _ GL _ _ _ _ _ _ _ (Z.max NAME (ATP + -200)) G); [| lia].
      destruct LOC as [(b & HB & B1 & B2) | (fr & HF & F1 & F2)].
      - left. apply in_block_In. exists b. split; [apply in_or_app; left; exact HB | lia].
      - right. apply in_frames_In. exists fr. split; [exact HF | lia]. }
    (* [comment removed for export] *)
    pose proof (proj1 (proj1 BUF)) as WF. cbn [cells_wf cell_wf] in WF. destruct WF as [LB _].
    assert (LR : length (skipn 30 buf) = (n - 30)%nat) by (rewrite length_skipn; lia).
    pose proof (rw_cells_split_CB asegs m NAME [] n buf [] [30%nat; (n - 30)%nat] BUF ltac:(cbn; lia)) as BUF2.
    cbn [app mk_CB_cells] in BUF2. rewrite tmpl_TMPL0 in FST. change (29 + 1)%nat with 30%nat in FST. rewrite FST in BUF2.
    rewrite (firstn_all2 (n := (n - 30)%nat) (skipn 30 buf)) in BUF2 by lia.
    set (rest := skipn 30 buf) in *. clearbody rest.
    (* [comment removed for export] *)
    unfold s_mkstemp, Stdio.mkstemp. rewrite tmpl_Z, seal_TEMPLATE, tmpn_tobytes. unfold MKSTEMP_MODE.
    apply implMG_sysk; [exact I|].
    (* [comment removed for export] *)
    eapply evtF_cut.
    { unfold MKSTEMP_ENTRY. eapply (mk_S1 RNG ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc NAME lo n) with (rest := rest);
        first [ exact BUF2 | exact ST | exact MI | exact ENV | exact SON | exact IESN | exact APWN | exact RSTK | exact RIMG | exact RGNAME | exact KLO
              | lia | match goal with |- ?g => idtac "S1 side:" g end ]. }
    cbv beta. intros ms1 PO. destruct PO as (x1 & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & jk & m1 & -> & FR1 & MU1 & WM1 & MI1 & ST1).
    assert (BUF1 : rw_cells asegs m1 NAME [CB 30 TMPL0; CB (n - 30) rest]).
    { eapply rw_cells_transport; [exact BUF2| exact MU1| exact WM1|]. cbn. lia. }
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (mk_S2 RNG sp gp (Z_to_bv 64 ATP) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc NAME n) with (rest := rest);
        first [ exact BUF1 | exact MI1 | exact RGNAME | lia | match goal with |- ?g => idtac "S2 side:" g end ]. }
    cbv beta. intros ms2 (b4' & ->).
    (* [comment removed for export] *)
    assert (ENV1 : icptenv m1) by (eapply icptenv_transport; [exact ENV | exact MU1 | exact WM1 | solve_iesafe]).
    assert (SON1 : sobj RNG m1 NAME (NAME + Z.of_nat n)) by (eapply sobj_transport; [exact SON | exact MU1 | exact WM1 | solve_appW]).
    eapply evtF_cut.
    { eapply (mk_S3 RNG ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc NAME lo n) with (rest := rest) (jk := jk);
        first [ exact BUF1 | exact FR1 | exact ST1 | exact MI1 | exact ENV1 | exact SON1 | exact IESN | exact APWN | exact RSTK | exact RIMG
              | exact RGNAME | exact KLO | lia | match goal with |- ?g => idtac "S3 side:" g end ]. }
    cbv beta. intros ms3 PO. destruct PO as (x1' & v0 & v1 & v2 & a0' & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & BUF3 & FR3 & MU3 & WM3 & MI3 & ST3).
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (mk_S4 RNG ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc NAME lo n) with (sA := sp) (jk := jk);
        first [ exact FR3 | exact ST3 | exact MI3 | exact RSTK | exact RIMG | lia | match goal with |- ?g => idtac "S4 side:" g end ]. }
    cbv beta. intros ms4 (-> & ST4).
    (* [comment removed for export] *)
    assert (MU13 : munch [(bv_unsigned sp - 4432, bv_unsigned sp); (NAME, NAME + 30)] m m3).
    { apply (munch_trans _ m m1 m3); [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU3]]; unfold sub_fp; cbn [outside]; intros; lia. }
    assert (WM13 : wmono asegs m m3) by (eapply wmono_trans; [exact WM1| exact WM3]).
    assert (ERR3 : rw_cells asegs m3 (ATP + -164) [C4 errv]).
    { eapply rw_cells_transport; [exact ERR| exact MU13| exact WM13|]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    assert (GOT3 : rw_cells asegs m3 got_ssp [C8 (Z_to_bv 64 ssp_guard)]).
    { eapply rw_cells_transport; [exact GOT| exact MU13| exact WM13|]. unfold got_ssp, ssp_guard. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    assert (GUARD3 : rw_cells asegs m3 ssp_guard [C8 canary]).
    { eapply rw_cells_transport; [exact GUARD| exact MU13| exact WM13|]. unfold got_ssp, ssp_guard. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    assert (STR3 : bytes_at asegs m3 NAME (TMPN ++ [Z_to_bv 8 0])).
    { pose proof (proj2 (proj1 BUF3)) as X. cbn [cells_bytes cbytes] in X.
      rewrite <- TMPN0_eq, <- (app_assoc (TMPN ++ [Z_to_bv 8 0]) (skipn 25 SEALED0)) in X. apply (proj1 (bytes_at_app _ _ _ _ _)) in X as [X _].
      exact X. }
    (* [comment removed for export] *)
    eapply evtF_cut.
    { change 608824 with OPEN_ENTRY.
      eapply (open_w_S1 RNG ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary); rewrite ?ETP;
        first [ exact ST4 | exact MI3 | exact GOT3 | exact GUARD3 | exact RSTK | exact RERR | exact RIMG | exact TPRM | exact TPLOM | exact TP200M | exact GLO
              | lia | match goal with |- ?g => idtac "OW side:" g end ]. }
    cbv beta. intros ms5 PO. destruct PO as (jk5 & m5 & -> & FR5 & MU5 & WM5 & MI5 & ST5).
    assert (STR5 : bytes_at asegs m5 NAME (TMPN ++ [Z_to_bv 8 0])).
    { eapply bytes_at_transport; [exact STR3 | exact MU5 |]. cbn [disjoint_from]. rewrite length_app, TMPN_len. cbn [length]. lia. }
    assert (ERR5 : rw_cells asegs m5 (ATP + -164) [C4 errv]).
    { eapply rw_cells_transport; [exact ERR3 | exact MU5 | exact WM5 |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    assert (GUARD5 : rw_cells asegs m5 ssp_guard [C8 canary]).
    { eapply rw_cells_transport; [exact GUARD3 | exact MU5 | exact WM5 |]. unfold ssp_guard. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    unfold OPEN_ECALL.
    step_ecall. split.
    { at_nodeA_solve.
      all: first [ exact TMPN_nonul | (rewrite unsigned_lit by lia; exact STR5)
                 | (rewrite unsigned_lit by lia; rewrite TMPN_len; eapply rng_sub'; [exact RGNAME | lia])
                 | match goal with |- ?g => idtac "ATNODE:" g end ]. }
    intros rsp a Hdec. apply dec_plain_Some in Hdec.
    (* [comment removed for export] *)
    assert (MU5e : munch [(bv_unsigned sp - 112, bv_unsigned sp); (ATP + -164, ATP + -160)] m3 m5).
    { eapply munch_weaken; [| exact MU5]. unfold sub_fp. cbn [outside]. intros x (O1 & O2 & _). split; [exact O1 | exact I]. }
    assert (FSTn : firstn (length TMPNAME + 1) ((TMPN0 ++ skipn 25 SEALED0) ++ rest) = map PcapRepA.b8 TMPNAME ++ [Z_to_bv 8 0]).
    { rewrite TMPNAME_len. change (24 + 1)%nat with 25%nat. rewrite <- app_assoc, firstn_app, TMPN0_len, Nat.sub_diag, firstn_O, app_nil_r.
      rewrite firstn_all2 by (rewrite TMPN0_len; lia). exact tmpn_bytes. }
    assert (FIN : forall (m' : mem) (l' : libc_st hptr) (e' : word),
      munch [(bv_unsigned sp - 112, bv_unsigned sp); (ATP + -164, ATP + -160)] m3 m' -> wmono asegs m3 m' ->
      rw_cells asegs m' (ATP + -164) [C4 e'] ->
      lc_stdout l' = lc_stdout (ps_libc s) -> lc_stderr l' = lc_stderr (ps_libc s) -> lc_files l' = lc_files (ps_libc s) ->
      GIOA L RNG (set_libc l' s) CL FB FL m'
      /\ agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ ~ (NAME <= a < NAME + Z.of_nat n)) m m'
      /\ rw_cells asegs m' NAME [CB n ((TMPN0 ++ skipn 25 SEALED0) ++ rest)]).
    { intros m' l' e' MU' WM' ERR' E1 E2 E3.
      assert (MUT : munch ([(bv_unsigned sp - 4432, bv_unsigned sp); (ATP + -164, ATP + -160)] ++ [(NAME, NAME + Z.of_nat n)]) m m').
      { apply (munch_trans _ m m3 m'); [eapply munch_weaken; [| exact MU13] | eapply munch_weaken; [| exact MU']]; unfold sub_fp; cbn [app outside]; intros; lia. }
      assert (WMT : wmono asegs m m') by (eapply wmono_trans; [exact WM13 | exact WM']).
      destruct NCR as [LOC OBJ].
      destruct (GIOA_errno_step_x L RNG s CL FB FL m m' _ (bv_unsigned sp) NAME (Z.of_nat n) l' e' G MUT WMT) as [G' AG'];
        [ apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_cons; [right; cbn [fst snd]; lia | apply Forall_nil]]
        | lia | exact LOC | lia | exact ERR' | exact E1 | exact E2 | exact E3 | ].
      split; [exact G'|]. split; [exact AG'|].
      assert (B3' : rw_cells asegs m' NAME [CB 30 (TMPN0 ++ skipn 25 SEALED0); CB (n - 30) rest]).
      { eapply rw_cells_transport; [exact BUF3| exact MU'| exact WM'|]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
      eapply rw_cells_recast; [exact B3' | | |].
      - cbn [cells_wf cell_wf]. split; [| exact I]. rewrite !length_app. change (length TMPN0) with 25%nat. change (length (skipn 25 SEALED0)) with 5%nat. lia.
      - cbn [cells_bytes cbytes]. rewrite !app_nil_r. reflexivity.
      - cbn. lia. }
    destruct a as [e|fd].
    - (* [comment removed for export] *)
      destruct Hdec as [-> He]. unfold set_errno. apply implMG_upd_lc. apply implMG_ret. unfold efferr. sys_nret.
      eapply evtF_mono.
      { eapply (open_w_tail RNG ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo errv canary)
          with (m0 := m3) (r := errno_ret e) (rv := -1) (ev := Z_to_bv 64 e); rewrite ?ETP;
          first [ exact FR5 | exact ERR5 | exact GUARD5 | exact ST5 | exact MI5 | exact MU5e | exact WM5 | exact RSTK | exact RERR | exact RIMG
                | exact TPRM | exact TPLOM | exact TP200M | exact GLO
                | (left; exists e; split; [reflexivity | split; [exact He | split; reflexivity]]) | lia | match goal with |- ?g => idtac "TL side:" g end ]. }
      cbv beta. intros ms' PO. unfold openw_post in PO. rewrite ?ETP in PO.
      destruct PO as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m' & -> & MU' & WM' & MI' & ST' & ERR').
      destruct (FIN m' (set_errno_lc e (ps_libc s)) (Z_to_bv 64 e) MU' WM' ERR' eq_refl eq_refl eq_refl) as (G' & AG' & BUF').
      split; [apply fp_le_refl|].
      eexists _, m', _. split; [unfold hpost_regs; repeat eexists; reflexivity|]. split; [reflexivity|].
      split; [exact MI'|]. split; [exact ST'|]. split; [exact AG'|]. split; [exact G'|].
      cbn [fst snd]. split; [reflexivity|]. split; [left; reflexivity|].
      split; [exact BUF'|]. split; [exact FSTn|]. split; [exact TMPNAME_range|].
      split; [rewrite TMPNAME_len, tmpl_len; lia|]. intros _. exact TMPNAME_path.
    - (* [comment removed for export] *)
      destruct Hdec as (-> & Hfd & Hrange). apply andb_prop in Hfd as [Hfd3 Hfd]. apply Z.leb_le in Hfd3. apply Z.leb_le in Hfd.
      apply implMG_ret. unfold eff0. sys_nret.
      eapply evtF_mono.
      { eapply (open_w_tail RNG ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo errv canary)
          with (m0 := m3) (r := Z_to_bv 64 fd) (rv := fd) (ev := errv); rewrite ?ETP;
          first [ exact FR5 | exact ERR5 | exact GUARD5 | exact ST5 | exact MI5 | exact MU5e | exact WM5 | exact RSTK | exact RERR | exact RIMG
                | exact TPRM | exact TPLOM | exact TP200M | exact GLO
                | (right; exists fd; split; [reflexivity | split; [lia | split; reflexivity]]) | lia | match goal with |- ?g => idtac "TL side:" g end ]. }
      cbv beta. intros ms' PO. unfold openw_post in PO. rewrite ?ETP in PO.
      destruct PO as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m' & -> & MU' & WM' & MI' & ST' & ERR').
      destruct (FIN m' (ps_libc s) errv MU' WM' ERR' eq_refl eq_refl eq_refl) as (G' & AG' & BUF').
      rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_sysA.set_libc_id in G'.
      split; [apply fp_le_refl|].
      eexists _, m', _. split; [unfold hpost_regs; repeat eexists; reflexivity|]. split; [reflexivity|].
      split; [exact MI'|]. split; [exact ST'|]. split; [exact AG'|]. split; [exact G'|].
      cbn [fst snd]. split; [reflexivity|]. split; [right; lia|].
      split; [exact BUF'|]. split; [exact FSTn|]. split; [exact TMPNAME_range|].
      split; [rewrite TMPNAME_len, tmpl_len; lia|]. intros _. exact TMPNAME_path.
  Qed.
  End Sz13.
  Theorem mkstemp_o_proofA : ltac:(let t := eval cbv delta [mkstemp_o_proofA__stmt] in mkstemp_o_proofA__stmt in exact t).
  Proof using GL GSL. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo NAME n tmpl buf. ltac2:(SecDiet.SzSec.closeP 'mkstemp_o_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End GlueMk.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_read__A3S.F_stdio_read.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_mkstemp__A3S.F_mkstemp.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioLawsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_foKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_sysA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section GlueMk.
  Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GSL : gia_stdio_laws GIOA.

  #[local] Notation spo_factsA := (A3S.Stdio_glueA.TwB.spo_factsA GIOA GSL).
  #[local] Notation cobjA_factsA := (A3S.Stdio_glueA.TwB.cobjA_factsA FO GIOA fflagA GL).
  #[local] Notation clocA_factsA := (A3S.Stdio_glueA.TwB.clocA_factsA FO GIOA fflagA GL).
  #[local] Notation sys_factsA := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_sysA.TwB.sys_factsA GIOA GSL).

  (* [comment removed for export] *)
  Lemma tmpl_Z : map bv_unsigned (map A3P.PcapRepA.TwB.b8 TEMPLATE) = TEMPLATE.
  Proof using Type. pin_using tt. vm_compute. reflexivity. Qed.
  Lemma tmpl_TMPL0 : map A3P.PcapRepA.TwB.b8 TEMPLATE ++ [Z_to_bv 8 0] = TMPL0.
  Proof using Type. pin_using tt. vm_compute. reflexivity. Qed.
  Lemma tmpl_len : length (map A3P.PcapRepA.TwB.b8 TEMPLATE) = 29%nat.
  Proof using Type. pin_using tt. reflexivity. Qed.
  Lemma seal_TEMPLATE : seal_name TEMPLATE = Some TMPNAME.
  Proof using Type. pin_using tt. vm_compute. reflexivity. Qed.
  Lemma tmpn_bytes : TMPN0 = map A3P.PcapRepA.TwB.b8 TMPNAME ++ [Z_to_bv 8 0].
  Proof using Type. pin_using tt. vm_compute. reflexivity. Qed.
  Lemma tmpn_tobytes : to_bytes TMPNAME = TMPN.
  Proof using Type. pin_using tt. vm_compute. reflexivity. Qed.
  Lemma TMPN0_len : length TMPN0 = 25%nat.
  Proof using Type. pin_using tt. reflexivity. Qed.
  Lemma TMPN_nonul : ~ In (Z_to_bv 8 0) TMPN.
  Proof using Type. pin_using tt. unfold TMPN, TMPNAME. cbn. intuition discriminate. Qed.
  Lemma TMPNAME_range : Forall (fun z => 0 < z < 256) TMPNAME.
  Proof using Type. pin_using tt. unfold TMPNAME. cbn. repeat (constructor; [lia|]). constructor. Qed.
  Lemma TMPNAME_len : length TMPNAME = 24%nat.
  Proof using Type. pin_using tt. reflexivity. Qed.
  Lemma TMPNAME_path : Namei.path_has_slash (map A3P.PcapRepA.TwB.b8 TMPNAME) = false
                       /\ map A3P.PcapRepA.TwB.b8 TMPNAME <> Uapi.dot_path /\ map A3P.PcapRepA.TwB.b8 TMPNAME <> Namei.dotdot_path.
  Proof using Type. pin_using tt.
    split; [vm_compute; reflexivity|].
    split; intros E; apply (f_equal (@length byte)) in E; vm_compute in E; discriminate E.
  Qed.

  (* [comment removed for export] *)
  Definition GIOA_errno_step_x__stmt : Prop := forall L RNG (s : PS) CL FB FL m m' W SP D n (l' : libc_st hptr) (e' : word),
    GIOA L RNG s CL FB FL m -> munch (W ++ [(D, D + n)]) m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => (ATOP + 4096 <= fst iv /\ snd iv <= SP) \/ (ATP + -164 <= fst iv /\ snd iv <= ATP + -160)) W -> ATOP + 4096 <= SP ->
    clocA FL CL D n -> 0 <= n ->
    rw_cells asegs m' (ATP + -164) [C4 e'] ->
    lc_stdout l' = lc_stdout (ps_libc s) -> lc_stderr l' = lc_stderr (ps_libc s) -> lc_files l' = lc_files (ps_libc s) ->
    GIOA L RNG (set_libc l' s) CL FB FL m' /\ agrees_on (fun a => client_keeps FL CL SP a /\ ~ (D <= a < D + n)) m m'.
  Section Sz12.
  Variables L RNG s CL FB FL m m' W SP D n l' e' : ltac2:(SecDiet.SzSec.tyM 'GIOA_errno_step_x__stmt "vvvvvvvvvvvvvv" @L).
  Lemma GIOA_errno_step_x__body : ltac2:(SecDiet.SzSec.bodyP 'GIOA_errno_step_x__stmt "vvvvvvvvvvvvvv").
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
    intros G MU WM HW HSP LOC Hn ERR' E1 E2 E3.
    assert (HW' : Forall (stdio_ivA FB SP) W).
    { eapply Forall_impl; [| exact HW]. intros iv [X|X]; [left; exact X | right; right; right; right; exact X]. }
    pose proof (gs_stdio _ GSL _ _ _ _ _ _ _ G) as SR.
    destruct (clocA_factsA _ _ _ _ _ _ _ D n G LOC Hn) as (X1 & X2 & X3).
    split.
    - eapply (gs_step _ GSL L RNG s CL FB FL m m' W [(D, D + n)] SP l'); [exact G | exact MU | exact WM | exact HW' | | exact HSP | exists e'; exact ERR' |].
      { apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. replace (D + n - D) with n by lia. exact LOC. }
      assert (SR' : STDIOR l' FB m) by (unfold STDIOR in SR |- *; rewrite E1, E2, E3; exact SR).
      eapply (STDIOR_agree l' FB m m' (fun a => stdio_static a \/ in_block FB a)); [exact SR' | | intros a Ha; left; exact Ha | intros a Ha; right; exact Ha].
      eapply agrees_on_of_munch; [exact MU | exact WM |]. intros a Ha Hc.
      pose proof (@ATPv_hi rc tlsI) as TH. pose proof (@ATPv_imgk rc tlsI) as (TI1 & TI2). pose proof (@kt_rng rc tlsI) as ((KI & _) & _).
      pose proof (@ATOP_lo rc) as ATL.
      assert (NT : ~ (ATP + -164 <= a < ATP + -160) /\ a < ATOP + 4096 /\ ~ (D <= a < D + n)).
      { destruct Hc as [Hs | Hb].
        - unfold stdio_static in Hs. unfold ATP. clear - Hs TH TI1 TI2 KI ATL X1. lia.
        - split; [| split].
          + intros X. assert (HB' : in_block (CL ++ FB) a) by (apply in_block_app; right; exact Hb).
            apply (gl_tls_apart _ _ _ GL _ _ _ _ _ _ _ a G (or_introl HB')). clear - X. lia.
          + apply in_block_In in Hb as (b & HIN & HR).
            pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ b G ltac:(apply in_or_app; right; exact HIN)) as ((_ & _ & TOP & _) & _). clear - HR TOP. lia.
          + intros HD. apply in_block_In in Hb as (b & HIN & HR).
            destruct LOC as [(b' & HB' & B1 & B2) | (fr & HF & F1 & F2)].
            * destruct (blocks_apart_app_inv _ _ (gl_apart _ _ _ GL _ _ _ _ _ _ _ G)) as (_ & _ & AP).
              specialize (AP b' b HB' HIN). unfold apart in AP. clear - AP HR HD B1 B2. lia.
            * apply (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ a G).
              -- apply in_frames_In. exists fr. split; [exact HF | clear - HD F1 F2; lia].
              -- apply in_block_In. exists b. split; [apply in_or_app; right; exact HIN | exact HR]. }
      destruct NT as (NT1 & NT2 & NT3). apply outside_app. split.
      + clear - HW NT1 NT2. induction HW as [|[lo hi] W Hiv HW IH]; cbn [outside]; [exact I|]. split; [| exact IH]. cbn [fst snd] in Hiv. lia.
      + cbn [outside]. split; [exact NT3 | exact I].
    - eapply agrees_on_weaken; [eapply (gs_keeps _ GSL L RNG s CL FB FL m m' W [(D, D + n)] SP); [exact G | exact MU | exact WM | exact HW' | exact HSP]|].
      intros a [Ha Hn']. split; [exact Ha |]. cbn [outside]. split; [exact Hn' | exact I].
  Qed.
  End Sz12.
  Lemma GIOA_errno_step_x : ltac:(let t := eval cbv delta [GIOA_errno_step_x__stmt] in GIOA_errno_step_x__stmt in exact t).
  Proof using GL GSL. intros L RNG s CL FB FL m m' W SP D n l' e'. ltac2:(SecDiet.SzSec.closeP 'GIOA_errno_step_x__body "vvvvvvvvvvvvvv"). Qed.
  Definition mkstemp_o_proofA__stmt : Prop := mkstemp_stmt_o GIOA.
  Section Sz13.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo NAME n tmpl buf : ltac2:(SecDiet.SzSec.tyM 'mkstemp_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma mkstemp_o_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'mkstemp_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
 intros SPO -> BUF FST NNUL -> NLE NMAX NCR.
 (* [comment removed for export] *)
 assert (NMAXZ : (Z.of_nat n <= 4096)%Z) by (clear - NMAX; lia). clear NMAX.
    pose proof SPO as (_ & _ & _ & _ & _ & _ & Etp & _ & (_ & _ & RIMGSH & _)). subst tp.
    destruct (sys_factsA _ _ _ _ _ _ _ _ _ SPO) as (G & ST & MI & LOA & LOB & SPT & TOP47 & RSTK & RIMG & GLO & (errv & ERR) & RERR & TPLOM & TP200M & ETP).
    pose proof (spo_factsA _ _ _ _ _ _ _ _ _ _ _ SPO) as (_ & _ & _ & _ & (canary & (GOT & GUARD)) & ENV & _ & _ & _ & _ & _ & _ & _ & _ & KLO & _).
    unfold STDIO_STACK in *. rewrite tmpl_len in NLE, FST.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (@ATOP_lo rc) as ATL. pose proof (@atp_range rc tlsI) as (_ & TPlo & TPhi & TPimg).
    assert (TPRM : ATP = 0x5e19b8) by (unfold ATP in *; lia).
    destruct (cobjA_factsA L RNG s CL FB FL m NAME (Z.of_nat n) lo G NCR ltac:(lia) LOA) as (N0 & NLO & N5E & N47 & SON & RGNAME & IESN & _).
    pose proof (sobj_appW _ _ _ _ SON) as APWN.
    (* [comment removed for export] *)
    assert (NTLS : NAME + Z.of_nat n <= ATP + -200 \/ ATP + 304 <= NAME).
    { destruct NCR as [LOC _].
      destruct (Z_lt_le_dec (Z.max NAME (ATP + -200)) (Z.min (NAME + Z.of_nat n) (ATP + 304))) as [LT|GE]; [| lia].
      exfalso. apply (gl_tls_apart _ _ _ GL _ _ _ _ _ _ _ (Z.max NAME (ATP + -200)) G); [| lia].
      destruct LOC as [(b & HB & B1 & B2) | (fr & HF & F1 & F2)].
      - left. apply in_block_In. exists b. split; [apply in_or_app; left; exact HB | lia].
      - right. apply in_frames_In. exists fr. split; [exact HF | lia]. }
    (* [comment removed for export] *)
    pose proof (proj1 (proj1 BUF)) as WF. cbn [cells_wf cell_wf] in WF. destruct WF as [LB _].
    assert (LR : length (skipn 30 buf) = (n - 30)%nat) by (rewrite length_skipn; lia).
    pose proof (rw_cells_split_CB asegs m NAME [] n buf [] [30%nat; (n - 30)%nat] BUF ltac:(cbn; lia)) as BUF2.
    cbn [app mk_CB_cells] in BUF2. rewrite tmpl_TMPL0 in FST. change (29 + 1)%nat with 30%nat in FST. rewrite FST in BUF2.
    rewrite (firstn_all2 (n := (n - 30)%nat) (skipn 30 buf)) in BUF2 by lia.
    set (rest := skipn 30 buf) in *. clearbody rest.
    (* [comment removed for export] *)
    unfold s_mkstemp, Stdio.mkstemp. rewrite tmpl_Z, seal_TEMPLATE, tmpn_tobytes. unfold MKSTEMP_MODE.
    apply implMG_sysk; [exact I|].
    (* [comment removed for export] *)
    eapply evtF_cut.
    { unfold MKSTEMP_ENTRY. eapply (mk_S1 RNG ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc NAME lo n) with (rest := rest);
        first [ exact BUF2 | exact ST | exact MI | exact ENV | exact SON | exact IESN | exact APWN | exact RSTK | exact RIMG | exact RGNAME | exact KLO
              | lia | match goal with |- ?g => idtac "S1 side:" g end ]. }
    cbv beta. intros ms1 PO. destruct PO as (x1 & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & jk & m1 & -> & FR1 & MU1 & WM1 & MI1 & ST1).
    assert (BUF1 : rw_cells asegs m1 NAME [CB 30 TMPL0; CB (n - 30) rest]).
    { eapply rw_cells_transport; [exact BUF2| exact MU1| exact WM1|]. cbn. lia. }
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (mk_S2 RNG sp gp (Z_to_bv 64 ATP) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc NAME n) with (rest := rest);
        first [ exact BUF1 | exact MI1 | exact RGNAME | lia | match goal with |- ?g => idtac "S2 side:" g end ]. }
    cbv beta. intros ms2 (b4' & ->).
    (* [comment removed for export] *)
    assert (ENV1 : icptenv m1) by (eapply icptenv_transport; [exact ENV | exact MU1 | exact WM1 | solve_iesafe]).
    assert (SON1 : sobj RNG m1 NAME (NAME + Z.of_nat n)) by (eapply sobj_transport; [exact SON | exact MU1 | exact WM1 | solve_appW]).
    eapply evtF_cut.
    { eapply (mk_S3 RNG ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc NAME lo n) with (rest := rest) (jk := jk);
        first [ exact BUF1 | exact FR1 | exact ST1 | exact MI1 | exact ENV1 | exact SON1 | exact IESN | exact APWN | exact RSTK | exact RIMG
              | exact RGNAME | exact KLO | lia | match goal with |- ?g => idtac "S3 side:" g end ]. }
    cbv beta. intros ms3 PO. destruct PO as (x1' & v0 & v1 & v2 & a0' & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & BUF3 & FR3 & MU3 & WM3 & MI3 & ST3).
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (mk_S4 RNG ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc NAME lo n) with (sA := sp) (jk := jk);
        first [ exact FR3 | exact ST3 | exact MI3 | exact RSTK | exact RIMG | lia | match goal with |- ?g => idtac "S4 side:" g end ]. }
    cbv beta. intros ms4 (-> & ST4).
    (* [comment removed for export] *)
    assert (MU13 : munch [(bv_unsigned sp - 4432, bv_unsigned sp); (NAME, NAME + 30)] m m3).
    { apply (munch_trans _ m m1 m3); [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU3]]; unfold sub_fp; cbn [outside]; intros; lia. }
    assert (WM13 : wmono asegs m m3) by (eapply wmono_trans; [exact WM1| exact WM3]).
    assert (ERR3 : rw_cells asegs m3 (ATP + -164) [C4 errv]).
    { eapply rw_cells_transport; [exact ERR| exact MU13| exact WM13|]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    assert (GOT3 : rw_cells asegs m3 got_ssp [C8 (Z_to_bv 64 ssp_guard)]).
    { eapply rw_cells_transport; [exact GOT| exact MU13| exact WM13|]. unfold got_ssp, ssp_guard. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    assert (GUARD3 : rw_cells asegs m3 ssp_guard [C8 canary]).
    { eapply rw_cells_transport; [exact GUARD| exact MU13| exact WM13|]. unfold got_ssp, ssp_guard. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    assert (STR3 : bytes_at asegs m3 NAME (TMPN ++ [Z_to_bv 8 0])).
    { pose proof (proj2 (proj1 BUF3)) as X. cbn [cells_bytes cbytes] in X.
      rewrite <- TMPN0_eq, <- (app_assoc (TMPN ++ [Z_to_bv 8 0]) (skipn 25 SEALED0)) in X. apply (proj1 (bytes_at_app _ _ _ _ _)) in X as [X _].
      exact X. }
    (* [comment removed for export] *)
    eapply evtF_cut.
    { change 609820 with OPEN_ENTRY.
      eapply (open_w_S1 RNG ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary); rewrite ?ETP;
        first [ exact ST4 | exact MI3 | exact GOT3 | exact GUARD3 | exact RSTK | exact RERR | exact RIMG | exact TPRM | exact TPLOM | exact TP200M | exact GLO
              | lia | match goal with |- ?g => idtac "OW side:" g end ]. }
    cbv beta. intros ms5 PO. destruct PO as (jk5 & m5 & -> & FR5 & MU5 & WM5 & MI5 & ST5).
    assert (STR5 : bytes_at asegs m5 NAME (TMPN ++ [Z_to_bv 8 0])).
    { eapply bytes_at_transport; [exact STR3 | exact MU5 |]. cbn [disjoint_from]. rewrite length_app, TMPN_len. cbn [length]. lia. }
    assert (ERR5 : rw_cells asegs m5 (ATP + -164) [C4 errv]).
    { eapply rw_cells_transport; [exact ERR3 | exact MU5 | exact WM5 |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    assert (GUARD5 : rw_cells asegs m5 ssp_guard [C8 canary]).
    { eapply rw_cells_transport; [exact GUARD3 | exact MU5 | exact WM5 |]. unfold ssp_guard. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    unfold OPEN_ECALL.
    step_ecall. split.
    { at_nodeA_solve.
      all: first [ exact TMPN_nonul | (rewrite unsigned_lit by lia; exact STR5)
                 | (rewrite unsigned_lit by lia; rewrite TMPN_len; eapply rng_sub'; [exact RGNAME | lia])
                 | match goal with |- ?g => idtac "ATNODE:" g end ]. }
    intros rsp a Hdec. apply dec_plain_Some in Hdec.
    (* [comment removed for export] *)
    assert (MU5e : munch [(bv_unsigned sp - 112, bv_unsigned sp); (ATP + -164, ATP + -160)] m3 m5).
    { eapply munch_weaken; [| exact MU5]. unfold sub_fp. cbn [outside]. intros x (O1 & O2 & _). split; [exact O1 | exact I]. }
    assert (FSTn : firstn (length TMPNAME + 1) ((TMPN0 ++ skipn 25 SEALED0) ++ rest) = map A3P.PcapRepA.TwB.b8 TMPNAME ++ [Z_to_bv 8 0]).
    { rewrite TMPNAME_len. change (24 + 1)%nat with 25%nat. rewrite <- app_assoc, firstn_app, TMPN0_len, Nat.sub_diag, firstn_O, app_nil_r.
      rewrite firstn_all2 by (rewrite TMPN0_len; lia). exact tmpn_bytes. }
    assert (FIN : forall (m' : mem) (l' : libc_st hptr) (e' : word),
      munch [(bv_unsigned sp - 112, bv_unsigned sp); (ATP + -164, ATP + -160)] m3 m' -> wmono asegs m3 m' ->
      rw_cells asegs m' (ATP + -164) [C4 e'] ->
      lc_stdout l' = lc_stdout (ps_libc s) -> lc_stderr l' = lc_stderr (ps_libc s) -> lc_files l' = lc_files (ps_libc s) ->
      GIOA L RNG (set_libc l' s) CL FB FL m'
      /\ agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ ~ (NAME <= a < NAME + Z.of_nat n)) m m'
      /\ rw_cells asegs m' NAME [CB n ((TMPN0 ++ skipn 25 SEALED0) ++ rest)]).
    { intros m' l' e' MU' WM' ERR' E1 E2 E3.
      assert (MUT : munch ([(bv_unsigned sp - 4432, bv_unsigned sp); (ATP + -164, ATP + -160)] ++ [(NAME, NAME + Z.of_nat n)]) m m').
      { apply (munch_trans _ m m3 m'); [eapply munch_weaken; [| exact MU13] | eapply munch_weaken; [| exact MU']]; unfold sub_fp; cbn [app outside]; intros; lia. }
      assert (WMT : wmono asegs m m') by (eapply wmono_trans; [exact WM13 | exact WM']).
      destruct NCR as [LOC OBJ].
      destruct (GIOA_errno_step_x L RNG s CL FB FL m m' _ (bv_unsigned sp) NAME (Z.of_nat n) l' e' G MUT WMT) as [G' AG'];
        [ apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_cons; [right; cbn [fst snd]; lia | apply Forall_nil]]
        | lia | exact LOC | lia | exact ERR' | exact E1 | exact E2 | exact E3 | ].
      split; [exact G'|]. split; [exact AG'|].
      assert (B3' : rw_cells asegs m' NAME [CB 30 (TMPN0 ++ skipn 25 SEALED0); CB (n - 30) rest]).
      { eapply rw_cells_transport; [exact BUF3| exact MU'| exact WM'|]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
      eapply rw_cells_recast; [exact B3' | | |].
      - cbn [cells_wf cell_wf]. split; [| exact I]. rewrite !length_app. change (length TMPN0) with 25%nat. change (length (skipn 25 SEALED0)) with 5%nat. lia.
      - cbn [cells_bytes cbytes]. rewrite !app_nil_r. reflexivity.
      - cbn. lia. }
    destruct a as [e|fd].
    - (* [comment removed for export] *)
      destruct Hdec as [-> He]. unfold set_errno. apply implMG_upd_lc. apply implMG_ret. unfold efferr. sys_nret.
      eapply evtF_mono.
      { eapply (open_w_tail RNG ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo errv canary)
          with (m0 := m3) (r := errno_ret e) (rv := -1) (ev := Z_to_bv 64 e); rewrite ?ETP;
          first [ exact FR5 | exact ERR5 | exact GUARD5 | exact ST5 | exact MI5 | exact MU5e | exact WM5 | exact RSTK | exact RERR | exact RIMG
                | exact TPRM | exact TPLOM | exact TP200M | exact GLO
                | (left; exists e; split; [reflexivity | split; [exact He | split; reflexivity]]) | lia | match goal with |- ?g => idtac "TL side:" g end ]. }
      cbv beta. intros ms' PO. unfold openw_post in PO. rewrite ?ETP in PO.
      destruct PO as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m' & -> & MU' & WM' & MI' & ST' & ERR').
      destruct (FIN m' (set_errno_lc e (ps_libc s)) (Z_to_bv 64 e) MU' WM' ERR' eq_refl eq_refl eq_refl) as (G' & AG' & BUF').
      split; [apply fp_le_refl|].
      eexists _, m', _. split; [unfold hpost_regs; repeat eexists; reflexivity|]. split; [reflexivity|].
      split; [exact MI'|]. split; [exact ST'|]. split; [exact AG'|]. split; [exact G'|].
      cbn [fst snd]. split; [reflexivity|]. split; [left; reflexivity|].
      split; [exact BUF'|]. split; [exact FSTn|]. split; [exact TMPNAME_range|].
      split; [rewrite TMPNAME_len, tmpl_len; lia|]. intros _. exact TMPNAME_path.
    - (* [comment removed for export] *)
      destruct Hdec as (-> & Hfd & Hrange). apply andb_prop in Hfd as [Hfd3 Hfd]. apply Z.leb_le in Hfd3. apply Z.leb_le in Hfd.
      apply implMG_ret. unfold eff0. sys_nret.
      eapply evtF_mono.
      { eapply (open_w_tail RNG ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo errv canary)
          with (m0 := m3) (r := Z_to_bv 64 fd) (rv := fd) (ev := errv); rewrite ?ETP;
          first [ exact FR5 | exact ERR5 | exact GUARD5 | exact ST5 | exact MI5 | exact MU5e | exact WM5 | exact RSTK | exact RERR | exact RIMG
                | exact TPRM | exact TPLOM | exact TP200M | exact GLO
                | (right; exists fd; split; [reflexivity | split; [lia | split; reflexivity]]) | lia | match goal with |- ?g => idtac "TL side:" g end ]. }
      cbv beta. intros ms' PO. unfold openw_post in PO. rewrite ?ETP in PO.
      destruct PO as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m' & -> & MU' & WM' & MI' & ST' & ERR').
      destruct (FIN m' (ps_libc s) errv MU' WM' ERR' eq_refl eq_refl eq_refl) as (G' & AG' & BUF').
      rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glue_foKitA__A3S.Stdio_glue_sysA.TwB.set_libc_id in G'.
      split; [apply fp_le_refl|].
      eexists _, m', _. split; [unfold hpost_regs; repeat eexists; reflexivity|]. split; [reflexivity|].
      split; [exact MI'|]. split; [exact ST'|]. split; [exact AG'|]. split; [exact G'|].
      cbn [fst snd]. split; [reflexivity|]. split; [right; lia|].
      split; [exact BUF'|]. split; [exact FSTn|]. split; [exact TMPNAME_range|].
      split; [rewrite TMPNAME_len, tmpl_len; lia|]. intros _. exact TMPNAME_path.
  Qed.
  End Sz13.
  Theorem mkstemp_o_proofA : ltac:(let t := eval cbv delta [mkstemp_o_proofA__stmt] in mkstemp_o_proofA__stmt in exact t).
  Proof using GL GSL. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL lo NAME n tmpl buf. ltac2:(SecDiet.SzSec.closeP 'mkstemp_o_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End GlueMk.
End TwB.
End Stdio_glue_mkA.
