(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Import GIA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_cs__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section WithRc.
Context {rc : runConstT}.
Section Agree.
  Context {hptr : Type}.
  Notation cblk := (@cblock hptr).

  Lemma FILE_R_agree : forall P m m' f Fp BA closefn readfn seekfn prev next,
    FILE_R m f Fp BA closefn readfn seekfn prev next ->
    agrees_on P m m' ->
    (forall a, Fp <= a < Fp + 232 -> P a) -> (forall a, BA <= a < BA + f_bufsize f -> P a) ->
    FILE_R m' f Fp BA closefn readfn seekfn prev next.
  Proof using Type. pin_using tt.
    intros P m m' f Fp BA closefn readfn seekfn prev next FR AG HP1 HP2.
    destruct FR as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP).
    exists flags, mode, rp, tail, bufbytes.
    split; [| split; [exact FL | split; [| split; [exact BP | split; [exact WB0 | split; [exact WBL | split; [exact RR | exact RP]]]]]]].
    - eapply agrees_rw_cells; [exact AG | exact FC |]. unfold fcells. rewrite file_cells_size. intros a Ha. apply HP1. lia.
    - pose proof (rw_cells_bound _ _ _ _ BUF) as BB. cbn [cells_size csize Nat.add] in BB.
      eapply agrees_rw_cells; [exact AG | exact BUF |]. cbn [cells_size csize Nat.add]. intros a Ha. apply HP2. lia.
  Qed.

  Lemma files_R_agree : forall fs (FB : list cblk) P m m' prev,
    files_R m prev fs FB -> agrees_on P m m' ->
    (forall a, in_block FB a -> P a) ->
    files_R m' prev fs FB.
  Proof using Type. pin_using tt.
    induction fs as [|[q f] fs IH]; intros [|[[q' A] n] FB] P m m' prev H AG HP; cbn in H |- *; try exact H.
    destruct H as (-> & -> & A0 & Ahi & FR & INV & REST).
    pose proof INV as INV'. destruct INV as (_ & _ & BS & _).
    split; [reflexivity|]. split; [reflexivity|]. split; [exact A0|]. split; [exact Ahi|].
    split.
    { eapply FILE_R_agree; [exact FR | exact AG | |].
      + intros a Ha. apply HP. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold FILE_ALLOC. lia.
      + intros a Ha. apply HP. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. rewrite BS in Ha. unfold FILE_ALLOC, FILE_BUF_OFF, BUFSIZ in *. lia. }
    split; [exact INV'|].
    eapply IH; [exact REST | exact AG |]. intros a Ha. apply HP. unfold in_block in *. apply Exists_cons_tl. exact Ha.
  Qed.

  Lemma STDIOR_agree : forall (l : libc_st hptr) FB m m' P,
    STDIOR l FB m -> agrees_on P m m' ->
    (forall a, stdio_static a -> P a) -> (forall a, in_block FB a -> P a) ->
    STDIOR l FB m'.
  Proof using Type. pin_using tt.
    intros l FB m m' P SR AG HS HB.
    destruct SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    unfold stdio_static in HS.
    unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED, A_OFL_LOCK, A_OFL_HEAD in *.
    pose proof SOI as SOI'. pose proof SEI as SEI'.
    destruct SOI as (_ & _ & SObs & _). destruct SEI as (_ & _ & SEbs & _).
    unfold STDIOR. unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED, A_OFL_LOCK, A_OFL_HEAD.
    Ltac tra AG HS A := eapply agrees_rw_cells; [exact AG | exact A | intros a Ha; apply HS; cbn in Ha; lia].
    split. { eapply FILE_R_agree; [exact SO | exact AG | intros a Ha; apply HS; lia | rewrite SObs; unfold BUFSIZ; intros a Ha; apply HS; lia]. }
    split; [exact SOI'|].
    split. { eapply FILE_R_agree; [exact SE | exact AG | intros a Ha; apply HS; lia | rewrite SEbs; intros a Ha; apply HS; lia]. }
    split; [exact SEI'|].
    split. { eapply agrees_rw_cells; [exact AG | exact SIN |]. unfold stdin_cells. rewrite file_cells_size. intros a Ha; apply HS; lia. }
    split; [tra AG HS U1|]. split; [tra AG HS U2|]. split; [tra AG HS U3|]. split; [tra AG HS OL|]. split; [tra AG HS OH|].
    split; [| exact ND].
    eapply files_R_agree; [exact FS | exact AG | exact HB].
  Qed.
End Agree.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Files.
  Context {hptr : Type} (ptr_eqb : hptr -> hptr -> bool).
  Hypothesis EQB : forall p q, ptr_eqb p q = true <-> p = q.
  Notation cblk := (@cblock hptr).

  Lemma eqb_refl' : forall p, ptr_eqb p p = true.
  Proof using EQB. pin_using (fun (EQB : unit) => tt). intros p. apply (proj2 (EQB p p)). reflexivity. Qed.
  Lemma eqb_neq : forall p q, p <> q -> ptr_eqb p q = false.
  Proof using EQB. pin_using (fun (EQB : unit) => tt). intros p q NE. destruct (ptr_eqb p q) eqn:E; [|reflexivity]. exfalso. apply NE. apply (proj1 (EQB p q)). exact E. Qed.

  (* [comment removed for export] *)
  Lemma files_R_toks : forall m prev fs (FB : list cblk), files_R m prev fs FB -> map cb_tok FB = map fst fs.
  Proof using Type. pin_using tt.
    intros m prev fs; revert prev.
    induction fs as [|[q f] fs IH]; intros prev [|[[q' A] n] FB] H; cbn in H |- *; try reflexivity; try contradiction.
    destruct H as (-> & _ & _ & _ & _ & _ & REST). f_equal. eapply IH. exact REST.
  Qed.

  (* [comment removed for export] *)
  Lemma files_R_pick : forall m prev fs (FB : list cblk) q A n,
    files_R m prev fs FB -> List.NoDup (map fst fs) -> In (q, A, n) FB ->
    exists f pv nx,
      files_lookup ptr_eqb fs q = Some f /\ In (q, f) fs /\ n = FILE_ALLOC /\ 0 < A /\ A + FILE_ALLOC < 2^63
      /\ FILE_R m f A (A + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx
      /\ heap_file_inv f.
  Proof using EQB. pin_using (fun (EQB : unit) => tt).
    intros m prev fs; revert prev.
    induction fs as [|[q1 f1] fs IH]; intros prev [|[[q1' A1] n1] FB] q A n H ND HIN; cbn in H; try contradiction; try (exfalso; exact HIN).
    destruct H as (-> & -> & A0 & Ahi & FR & INV & REST).
    cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
    destruct HIN as [E | HIN].
    - injection E as <- <- <-. exists f1, prev, (hd_addr FB). cbn [files_lookup]. rewrite eqb_refl'.
      split; [reflexivity|]. split; [left; reflexivity|]. split; [reflexivity|]. split; [exact A0|]. split; [exact Ahi|]. split; [exact FR| exact INV].
    - destruct (IH A1 FB q A n REST ND HIN) as (f & pv & nx & LK & INf & En & B0 & Bhi & FRf & INVf).
      assert (NE : q1 <> q).
      { intros ->. apply NI. change q with (fst (q, f)). apply in_map. exact INf. }
      exists f, pv, nx. cbn [files_lookup]. rewrite (eqb_neq _ _ NE).
      split; [exact LK|]. split; [right; exact INf|]. split; [exact En|]. split; [exact B0|]. split; [exact Bhi|]. split; [exact FRf| exact INVf].
  Qed.

  (* [comment removed for export] *)
  Lemma files_R_frame : forall m m' prev fs (FB : list cblk),
    files_R m prev fs FB ->
    (forall q2 A2 n2 f2 pv nx, In (q2, A2, n2) FB ->
                     FILE_R m f2 A2 (A2 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx -> heap_file_inv f2 ->
                     FILE_R m' f2 A2 (A2 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx) ->
    files_R m' prev fs FB.
  Proof using Type. pin_using tt.
    intros m m' prev fs FB. revert prev FB.
    induction fs as [|[q3 f3] fs IH]; intros pv0 [|[[q3' A3] n3] FB] H HF; cbn in H |- *; try exact H.
    destruct H as (-> & -> & B0 & Bhi & FR3 & INV3 & REST3).
    split; [reflexivity|]. split; [reflexivity|]. split; [exact B0|]. split; [exact Bhi|].
    split; [exact (HF q3 A3 FILE_ALLOC f3 pv0 (hd_addr FB) (or_introl eq_refl) FR3 INV3)|]. split; [exact INV3|].
    apply IH; [exact REST3|]. intros q2 A2 n2 f2 pv nx HIN2. apply (HF q2 A2 n2 f2 pv nx (or_intror HIN2)).
  Qed.

  Lemma files_update_keys : forall fs q f', map fst (files_update ptr_eqb fs q f') = map fst fs.
  Proof using Type. pin_using tt.
    induction fs as [|[k g] fs IH]; intros q f'; cbn; [reflexivity|].
    destruct (ptr_eqb k q); cbn; [reflexivity| f_equal; apply IH].
  Qed.

  Lemma files_remove_keys : forall fs q, incl (map fst (files_remove ptr_eqb fs q)) (map fst fs).
  Proof using Type. pin_using tt.
    induction fs as [|[k g] fs IH]; intros q; cbn; [apply incl_refl|].
    destruct (ptr_eqb k q); cbn.
    - apply incl_tl, incl_refl.
    - apply incl_cons; [left; reflexivity| apply incl_tl, IH].
  Qed.

  Lemma files_lookup_In : forall fs q f, List.NoDup (map fst fs) -> In (q, f) fs -> files_lookup ptr_eqb fs q = Some f.
  Proof using EQB. pin_using (fun (EQB : unit) => tt).
    induction fs as [|[k g] fs IH]; intros q f ND HIN; [destruct HIN|].
    cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND]. cbn.
    destruct HIN as [E|HIN].
    - injection E as -> ->. rewrite eqb_refl'. reflexivity.
    - assert (NE : k <> q) by (intros ->; apply NI; change q with (fst (q, f)); apply in_map; exact HIN).
      rewrite (eqb_neq _ _ NE). apply IH; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma files_R_focus : forall m prev fs (FB : list cblk) q A n,
    files_R m prev fs FB -> List.NoDup (map fst fs) -> In (q, A, n) FB ->
    exists f pv nx,
      files_lookup ptr_eqb fs q = Some f /\ n = FILE_ALLOC /\ 0 < A /\ A + FILE_ALLOC < 2^63
      /\ FILE_R m f A (A + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx
      /\ heap_file_inv f
      /\ (forall m' f', FILE_R m' f' A (A + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx -> heap_file_inv f' ->
            (forall q2 A2 n2 f2 pv2 nx2, In (q2, A2, n2) FB -> q2 <> q ->
                     FILE_R m f2 A2 (A2 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv2 nx2 -> heap_file_inv f2 ->
                     FILE_R m' f2 A2 (A2 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv2 nx2) ->
            files_R m' prev (files_update ptr_eqb fs q f') FB).
  Proof using EQB. pin_using (fun (EQB : unit) => tt).
    intros m prev fs; revert prev.
    induction fs as [|[q1 f1] fs IH]; intros prev [|[[q1' A1] n1] FB] q A n H ND HIN; cbn in H; try contradiction; try (exfalso; exact HIN).
    destruct H as (-> & -> & A0 & Ahi & FR & INV & REST).
    cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
    pose proof (files_R_toks _ _ _ _ REST) as TK.
    destruct HIN as [E | HIN].
    - injection E as <- <- <-. exists f1, prev, (hd_addr FB). cbn [files_lookup files_update]. rewrite eqb_refl'.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact A0|]. split; [exact Ahi|]. split; [exact FR|]. split; [exact INV|].
      intros m' f' FR' INV' HF. cbn [files_R].
      split; [reflexivity|]. split; [reflexivity|]. split; [exact A0|]. split; [exact Ahi|]. split; [exact FR'|]. split; [exact INV'|].
      eapply files_R_frame; [exact REST|].
      intros q2 A2 n2 f2 pv2 nx2 HIN2. apply (HF q2 A2 n2 f2 pv2 nx2 (or_intror HIN2)).
      intros ->. apply NI. rewrite <- TK. change q1 with (cb_tok (q1, A2, n2)). apply in_map. exact HIN2.
    - destruct (IH A1 FB q A n REST ND HIN) as (f & pv & nx & LK & En & B0 & Bhi & FRf & INVf & UPD).
      assert (NE : q1 <> q).
      { intros ->. apply NI. rewrite <- TK. change q with (cb_tok (q, A, n)). apply in_map. exact HIN. }
      exists f, pv, nx. cbn [files_lookup files_update]. rewrite (eqb_neq _ _ NE).
      split; [exact LK|]. split; [exact En|]. split; [exact B0|]. split; [exact Bhi|]. split; [exact FRf|]. split; [exact INVf|].
      intros m' f' FR' INV' HF. cbn [files_R].
      split; [reflexivity|]. split; [reflexivity|]. split; [exact A0|]. split; [exact Ahi|].
      split; [exact (HF q1 A1 FILE_ALLOC f1 prev (hd_addr FB) (or_introl eq_refl) NE FR INV)|].
      split; [exact INV|].
      apply UPD; [exact FR'| exact INV'|].
      intros q2 A2 n2 f2 pv2 nx2 HIN2 NE2. apply (HF q2 A2 n2 f2 pv2 nx2); [right; exact HIN2| exact NE2].
  Qed.
End Files.
End WithRc.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section WithRc.
Context {rc : runConstT}.
Section Agree.
  Context {hptr : Type}.
  Notation cblk := (@cblock hptr).

  Lemma FILE_R_agree : forall P m m' f Fp BA closefn readfn seekfn prev next,
    FILE_R m f Fp BA closefn readfn seekfn prev next ->
    agrees_on P m m' ->
    (forall a, Fp <= a < Fp + 232 -> P a) -> (forall a, BA <= a < BA + f_bufsize f -> P a) ->
    FILE_R m' f Fp BA closefn readfn seekfn prev next.
  Proof using Type. pin_using tt.
    intros P m m' f Fp BA closefn readfn seekfn prev next FR AG HP1 HP2.
    destruct FR as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP).
    exists flags, mode, rp, tail, bufbytes.
    split; [| split; [exact FL | split; [| split; [exact BP | split; [exact WB0 | split; [exact WBL | split; [exact RR | exact RP]]]]]]].
    - eapply agrees_rw_cells; [exact AG | exact FC |]. unfold fcells. rewrite file_cells_size. intros a Ha. apply HP1. lia.
    - pose proof (rw_cells_bound _ _ _ _ BUF) as BB. cbn [cells_size csize Nat.add] in BB.
      eapply agrees_rw_cells; [exact AG | exact BUF |]. cbn [cells_size csize Nat.add]. intros a Ha. apply HP2. lia.
  Qed.

  Lemma files_R_agree : forall fs (FB : list cblk) P m m' prev,
    files_R m prev fs FB -> agrees_on P m m' ->
    (forall a, in_block FB a -> P a) ->
    files_R m' prev fs FB.
  Proof using Type. pin_using tt.
    induction fs as [|[q f] fs IH]; intros [|[[q' A] n] FB] P m m' prev H AG HP; cbn in H |- *; try exact H.
    destruct H as (-> & -> & A0 & Ahi & FR & INV & REST).
    pose proof INV as INV'. destruct INV as (_ & _ & BS & _).
    split; [reflexivity|]. split; [reflexivity|]. split; [exact A0|]. split; [exact Ahi|].
    split.
    { eapply FILE_R_agree; [exact FR | exact AG | |].
      + intros a Ha. apply HP. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold FILE_ALLOC. lia.
      + intros a Ha. apply HP. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. rewrite BS in Ha. unfold FILE_ALLOC, FILE_BUF_OFF, BUFSIZ in *. lia. }
    split; [exact INV'|].
    eapply IH; [exact REST | exact AG |]. intros a Ha. apply HP. unfold in_block in *. apply Exists_cons_tl. exact Ha.
  Qed.

  Lemma STDIOR_agree : forall (l : libc_st hptr) FB m m' P,
    STDIOR l FB m -> agrees_on P m m' ->
    (forall a, stdio_static a -> P a) -> (forall a, in_block FB a -> P a) ->
    STDIOR l FB m'.
  Proof using Type. pin_using tt.
    intros l FB m m' P SR AG HS HB.
    destruct SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    unfold stdio_static in HS.
    unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED, A_OFL_LOCK, A_OFL_HEAD in *.
    pose proof SOI as SOI'. pose proof SEI as SEI'.
    destruct SOI as (_ & _ & SObs & _). destruct SEI as (_ & _ & SEbs & _).
    unfold STDIOR. unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED, A_OFL_LOCK, A_OFL_HEAD.
    Ltac tra AG HS A := eapply agrees_rw_cells; [exact AG | exact A | intros a Ha; apply HS; cbn in Ha; lia].
    split. { eapply FILE_R_agree; [exact SO | exact AG | intros a Ha; apply HS; lia | rewrite SObs; unfold BUFSIZ; intros a Ha; apply HS; lia]. }
    split; [exact SOI'|].
    split. { eapply FILE_R_agree; [exact SE | exact AG | intros a Ha; apply HS; lia | rewrite SEbs; intros a Ha; apply HS; lia]. }
    split; [exact SEI'|].
    split. { eapply agrees_rw_cells; [exact AG | exact SIN |]. unfold stdin_cells. rewrite file_cells_size. intros a Ha; apply HS; lia. }
    split; [tra AG HS U1|]. split; [tra AG HS U2|]. split; [tra AG HS U3|]. split; [tra AG HS OL|]. split; [tra AG HS OH|].
    split; [| exact ND].
    eapply files_R_agree; [exact FS | exact AG | exact HB].
  Qed.
End Agree.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Files.
  Context {hptr : Type} (ptr_eqb : hptr -> hptr -> bool).
  Hypothesis EQB : forall p q, ptr_eqb p q = true <-> p = q.
  Notation cblk := (@cblock hptr).

  Lemma eqb_refl' : forall p, ptr_eqb p p = true.
  Proof using EQB. pin_using (fun (EQB : unit) => tt). intros p. apply (proj2 (EQB p p)). reflexivity. Qed.
  Lemma eqb_neq : forall p q, p <> q -> ptr_eqb p q = false.
  Proof using EQB. pin_using (fun (EQB : unit) => tt). intros p q NE. destruct (ptr_eqb p q) eqn:E; [|reflexivity]. exfalso. apply NE. apply (proj1 (EQB p q)). exact E. Qed.

  (* [comment removed for export] *)
  Lemma files_R_toks : forall m prev fs (FB : list cblk), files_R m prev fs FB -> map cb_tok FB = map fst fs.
  Proof using Type. pin_using tt.
    intros m prev fs; revert prev.
    induction fs as [|[q f] fs IH]; intros prev [|[[q' A] n] FB] H; cbn in H |- *; try reflexivity; try contradiction.
    destruct H as (-> & _ & _ & _ & _ & _ & REST). f_equal. eapply IH. exact REST.
  Qed.

  (* [comment removed for export] *)
  Lemma files_R_pick : forall m prev fs (FB : list cblk) q A n,
    files_R m prev fs FB -> List.NoDup (map fst fs) -> In (q, A, n) FB ->
    exists f pv nx,
      files_lookup ptr_eqb fs q = Some f /\ In (q, f) fs /\ n = FILE_ALLOC /\ 0 < A /\ A + FILE_ALLOC < 2^63
      /\ FILE_R m f A (A + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx
      /\ heap_file_inv f.
  Proof using EQB. pin_using (fun (EQB : unit) => tt).
    intros m prev fs; revert prev.
    induction fs as [|[q1 f1] fs IH]; intros prev [|[[q1' A1] n1] FB] q A n H ND HIN; cbn in H; try contradiction; try (exfalso; exact HIN).
    destruct H as (-> & -> & A0 & Ahi & FR & INV & REST).
    cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
    destruct HIN as [E | HIN].
    - injection E as <- <- <-. exists f1, prev, (hd_addr FB). cbn [files_lookup]. rewrite eqb_refl'.
      split; [reflexivity|]. split; [left; reflexivity|]. split; [reflexivity|]. split; [exact A0|]. split; [exact Ahi|]. split; [exact FR| exact INV].
    - destruct (IH A1 FB q A n REST ND HIN) as (f & pv & nx & LK & INf & En & B0 & Bhi & FRf & INVf).
      assert (NE : q1 <> q).
      { intros ->. apply NI. change q with (fst (q, f)). apply in_map. exact INf. }
      exists f, pv, nx. cbn [files_lookup]. rewrite (eqb_neq _ _ NE).
      split; [exact LK|]. split; [right; exact INf|]. split; [exact En|]. split; [exact B0|]. split; [exact Bhi|]. split; [exact FRf| exact INVf].
  Qed.

  (* [comment removed for export] *)
  Lemma files_R_frame : forall m m' prev fs (FB : list cblk),
    files_R m prev fs FB ->
    (forall q2 A2 n2 f2 pv nx, In (q2, A2, n2) FB ->
                     FILE_R m f2 A2 (A2 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx -> heap_file_inv f2 ->
                     FILE_R m' f2 A2 (A2 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx) ->
    files_R m' prev fs FB.
  Proof using Type. pin_using tt.
    intros m m' prev fs FB. revert prev FB.
    induction fs as [|[q3 f3] fs IH]; intros pv0 [|[[q3' A3] n3] FB] H HF; cbn in H |- *; try exact H.
    destruct H as (-> & -> & B0 & Bhi & FR3 & INV3 & REST3).
    split; [reflexivity|]. split; [reflexivity|]. split; [exact B0|]. split; [exact Bhi|].
    split; [exact (HF q3 A3 FILE_ALLOC f3 pv0 (hd_addr FB) (or_introl eq_refl) FR3 INV3)|]. split; [exact INV3|].
    apply IH; [exact REST3|]. intros q2 A2 n2 f2 pv nx HIN2. apply (HF q2 A2 n2 f2 pv nx (or_intror HIN2)).
  Qed.

  Lemma files_update_keys : forall fs q f', map fst (files_update ptr_eqb fs q f') = map fst fs.
  Proof using Type. pin_using tt.
    induction fs as [|[k g] fs IH]; intros q f'; cbn; [reflexivity|].
    destruct (ptr_eqb k q); cbn; [reflexivity| f_equal; apply IH].
  Qed.

  Lemma files_remove_keys : forall fs q, incl (map fst (files_remove ptr_eqb fs q)) (map fst fs).
  Proof using Type. pin_using tt.
    induction fs as [|[k g] fs IH]; intros q; cbn; [apply incl_refl|].
    destruct (ptr_eqb k q); cbn.
    - apply incl_tl, incl_refl.
    - apply incl_cons; [left; reflexivity| apply incl_tl, IH].
  Qed.

  Lemma files_lookup_In : forall fs q f, List.NoDup (map fst fs) -> In (q, f) fs -> files_lookup ptr_eqb fs q = Some f.
  Proof using EQB. pin_using (fun (EQB : unit) => tt).
    induction fs as [|[k g] fs IH]; intros q f ND HIN; [destruct HIN|].
    cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND]. cbn.
    destruct HIN as [E|HIN].
    - injection E as -> ->. rewrite eqb_refl'. reflexivity.
    - assert (NE : k <> q) by (intros ->; apply NI; change q with (fst (q, f)); apply in_map; exact HIN).
      rewrite (eqb_neq _ _ NE). apply IH; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma files_R_focus : forall m prev fs (FB : list cblk) q A n,
    files_R m prev fs FB -> List.NoDup (map fst fs) -> In (q, A, n) FB ->
    exists f pv nx,
      files_lookup ptr_eqb fs q = Some f /\ n = FILE_ALLOC /\ 0 < A /\ A + FILE_ALLOC < 2^63
      /\ FILE_R m f A (A + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx
      /\ heap_file_inv f
      /\ (forall m' f', FILE_R m' f' A (A + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx -> heap_file_inv f' ->
            (forall q2 A2 n2 f2 pv2 nx2, In (q2, A2, n2) FB -> q2 <> q ->
                     FILE_R m f2 A2 (A2 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv2 nx2 -> heap_file_inv f2 ->
                     FILE_R m' f2 A2 (A2 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv2 nx2) ->
            files_R m' prev (files_update ptr_eqb fs q f') FB).
  Proof using EQB. pin_using (fun (EQB : unit) => tt).
    intros m prev fs; revert prev.
    induction fs as [|[q1 f1] fs IH]; intros prev [|[[q1' A1] n1] FB] q A n H ND HIN; cbn in H; try contradiction; try (exfalso; exact HIN).
    destruct H as (-> & -> & A0 & Ahi & FR & INV & REST).
    cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
    pose proof (files_R_toks _ _ _ _ REST) as TK.
    destruct HIN as [E | HIN].
    - injection E as <- <- <-. exists f1, prev, (hd_addr FB). cbn [files_lookup files_update]. rewrite eqb_refl'.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact A0|]. split; [exact Ahi|]. split; [exact FR|]. split; [exact INV|].
      intros m' f' FR' INV' HF. cbn [files_R].
      split; [reflexivity|]. split; [reflexivity|]. split; [exact A0|]. split; [exact Ahi|]. split; [exact FR'|]. split; [exact INV'|].
      eapply files_R_frame; [exact REST|].
      intros q2 A2 n2 f2 pv2 nx2 HIN2. apply (HF q2 A2 n2 f2 pv2 nx2 (or_intror HIN2)).
      intros ->. apply NI. rewrite <- TK. change q1 with (cb_tok (q1, A2, n2)). apply in_map. exact HIN2.
    - destruct (IH A1 FB q A n REST ND HIN) as (f & pv & nx & LK & En & B0 & Bhi & FRf & INVf & UPD).
      assert (NE : q1 <> q).
      { intros ->. apply NI. rewrite <- TK. change q with (cb_tok (q, A, n)). apply in_map. exact HIN. }
      exists f, pv, nx. cbn [files_lookup files_update]. rewrite (eqb_neq _ _ NE).
      split; [exact LK|]. split; [exact En|]. split; [exact B0|]. split; [exact Bhi|]. split; [exact FRf|]. split; [exact INVf|].
      intros m' f' FR' INV' HF. cbn [files_R].
      split; [reflexivity|]. split; [reflexivity|]. split; [exact A0|]. split; [exact Ahi|].
      split; [exact (HF q1 A1 FILE_ALLOC f1 prev (hd_addr FB) (or_introl eq_refl) NE FR INV)|].
      split; [exact INV|].
      apply UPD; [exact FR'| exact INV'|].
      intros q2 A2 n2 f2 pv2 nx2 HIN2 NE2. apply (HF q2 A2 n2 f2 pv2 nx2); [right; exact HIN2| exact NE2].
  Qed.
End Files.
End WithRc.
End TwB.
