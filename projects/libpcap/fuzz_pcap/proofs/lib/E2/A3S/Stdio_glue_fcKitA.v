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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_cs__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA Stdio_glueKitA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueKitA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section WithRc.
Context {rc : runConstT}.
Section Relink.
  Lemma fcells_split_links : forall flags rp re cf we wp wb rf wf sf b bs pv nx fd md lbf tl,
    fcells flags rp re cf we wp wb rf wf sf b bs pv nx fd md lbf tl =
    [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 rp); C8 (Z_to_bv 64 re); C8 (Z_to_bv 64 cf);
     C8 (Z_to_bv 64 we); C8 (Z_to_bv 64 wp); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wb);
     C8 (Z_to_bv 64 rf); C8 (Z_to_bv 64 wf); C8 (Z_to_bv 64 sf); C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 bs)]
    ++ [C8 (Z_to_bv 64 pv)] ++ [C8 (Z_to_bv 64 nx)]
    ++ [C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
        C4 md; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0); CB 80 tl].
  Proof using Type. pin_using tt. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma FILE_R_link_cells : forall m f Fp BA cf rf sf pv nx,
    FILE_R m f Fp BA cf rf sf pv nx ->
    rw_cells asegs m (Fp + 104) [C8 (Z_to_bv 64 pv)] /\ rw_cells asegs m (Fp + 112) [C8 (Z_to_bv 64 nx)].
  Proof using Type. pin_using tt.
    intros m f Fp BA cf rf sf pv nx (flags & mode & rp & tail & bufbytes & FC & _).
    rewrite fcells_split_links in FC. apply (proj1 (rw_cells_app asegs m Fp _ _)) in FC as [_ FC].
    apply (proj1 (rw_cells_app asegs m _ [_] _)) in FC as [FP FC]. apply (proj1 (rw_cells_app asegs m _ [_] _)) in FC as [FN _].
    cbn [cells_size csize Nat.add] in FP, FN.
    replace (Fp + Z.of_nat 104) with (Fp + 104) in FP by lia.
    replace (Fp + Z.of_nat 104 + Z.of_nat 8) with (Fp + 112) in FN by lia.
    split; [exact FP| exact FN].
  Qed.

  (* [comment removed for export] *)
  Lemma FILE_R_relink : forall (P : Z -> Prop) m m' f Fp BA cf rf sf pv nx pv' nx',
    FILE_R m f Fp BA cf rf sf pv nx ->
    agrees_on P m m' ->
    (forall a, Fp <= a < Fp + 232 -> ~ (Fp + 104 <= a < Fp + 120) -> P a) ->
    (forall a, BA <= a < BA + f_bufsize f -> P a) ->
    rw_cells asegs m' (Fp + 104) [C8 (Z_to_bv 64 pv')] -> rw_cells asegs m' (Fp + 112) [C8 (Z_to_bv 64 nx')] ->
    FILE_R m' f Fp BA cf rf sf pv' nx'.
  Proof using Type. pin_using tt.
    intros P m m' f Fp BA cf rf sf pv nx pv' nx' FR AG HP1 HP2 PC NC.
    destruct FR as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP).
    exists flags, mode, rp, tail, bufbytes.
    split; [| split; [exact FL | split; [| split; [exact BP | split; [exact WB0 | split; [exact WBL | split; [exact RR | exact RP]]]]]]].
    - rewrite fcells_split_links in FC |- *.
      apply (proj1 (rw_cells_app asegs m Fp _ _)) in FC as [FCa FC]. apply (proj1 (rw_cells_app asegs m _ [_] _)) in FC as [_ FC].
      apply (proj1 (rw_cells_app asegs m _ [_] _)) in FC as [_ FCb].
      cbn [cells_size csize Nat.add] in FCa, FCb |- *.
      apply (proj2 (rw_cells_app asegs m' Fp _ _)). split.
      + eapply agrees_rw_cells; [exact AG| exact FCa|]. cbn [cells_size csize Nat.add]. intros a Ha. apply HP1; lia.
      + apply (proj2 (rw_cells_app asegs m' _ [_] _)). cbn [cells_size csize Nat.add]. split.
        * replace (Fp + Z.of_nat 104) with (Fp + 104) by lia. exact PC.
        * apply (proj2 (rw_cells_app asegs m' _ [_] _)). cbn [cells_size csize Nat.add]. split.
          -- replace (Fp + Z.of_nat 104 + Z.of_nat 8) with (Fp + 112) by lia. exact NC.
          -- eapply agrees_rw_cells; [exact AG| exact FCb|]. cbn [cells_size csize Nat.add]. intros a Ha. apply HP1; lia.
    - pose proof (rw_cells_bound _ _ _ _ BUF) as BB. cbn [cells_size csize Nat.add] in BB.
      eapply agrees_rw_cells; [exact AG | exact BUF |]. cbn [cells_size csize Nat.add]. intros a Ha. apply HP2. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma FILE_R_relink_same : forall (P : Z -> Prop) m m' f Fp BA cf rf sf pv nx,
    FILE_R m f Fp BA cf rf sf pv nx ->
    agrees_on P m m' ->
    (forall a, Fp <= a < Fp + 232 -> P a) -> (forall a, BA <= a < BA + f_bufsize f -> P a) ->
    FILE_R m' f Fp BA cf rf sf pv nx.
  Proof using Type. pin_using tt.
    intros P m m' f Fp BA cf rf sf pv nx FR AG HP1 HP2.
    pose proof (FILE_R_link_cells _ _ _ _ _ _ _ _ _ FR) as [PC NC].
    eapply FILE_R_relink; [exact FR| exact AG| intros a Ha _; apply HP1; exact Ha| exact HP2| |].
    - eapply agrees_rw_cells; [exact AG| exact PC|]. cbn. intros a Ha. apply HP1. lia.
    - eapply agrees_rw_cells; [exact AG| exact NC|]. cbn. intros a Ha. apply HP1. lia.
  Qed.
End Relink.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Unlink.
  Context {hptr : Type} (ptr_eqb : hptr -> hptr -> bool).
  Hypothesis EQB : forall p q, ptr_eqb p q = true <-> p = q.
  #[local] Notation cblk := (@cblock hptr).

  (* [comment removed for export] *)
  Fixpoint last_addr (prev : Z) (FB : list cblk) : Z :=
    match FB with [] => prev | (_, A, _) :: FB' => last_addr A FB' end.

  Lemma last_addr_app : forall prev (F1 F2 : list cblk), last_addr prev (F1 ++ F2) = last_addr (last_addr prev F1) F2.
  Proof using Type. pin_using tt. intros prev F1; revert prev. induction F1 as [|[[q A] n] F1 IH]; intros prev F2; cbn; [reflexivity| apply IH]. Qed.

  Lemma last_addr_In : forall prev (FB : list cblk), FB <> [] -> exists q n, In (q, last_addr prev FB, n) FB.
  Proof using Type. pin_using tt.
    intros prev FB; revert prev. induction FB as [|[[q A] n] FB IH]; intros prev NE; [exfalso; exact (NE eq_refl)|].
    cbn. destruct FB as [|b FB'].
    - exists q, n. left. reflexivity.
    - destruct (IH A ltac:(discriminate)) as (q' & n' & HIN). exists q', n'. right. exact HIN.
  Qed.

  Lemma hd_addr_app : forall (F1 F2 : list cblk), F1 <> [] -> hd_addr (F1 ++ F2) = hd_addr F1.
  Proof using Type. pin_using tt. intros [|[[q A] n] F1] F2 NE; [exfalso; exact (NE eq_refl)| reflexivity]. Qed.

  Lemma hd_addr_In : forall (FB : list cblk), FB <> [] -> exists q n, In (q, hd_addr FB, n) FB.
  Proof using Type. pin_using tt. intros [|[[q A] n] FB] NE; [exfalso; exact (NE eq_refl)|]. exists q, n. left. reflexivity. Qed.

  Lemma NoDup_files_remove : forall fs q, List.NoDup (map fst fs) -> List.NoDup (map fst (files_remove ptr_eqb fs q)).
  Proof using Type. pin_using tt.
    induction fs as [|[k g] fs IH]; intros q ND; cbn; [constructor|].
    cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
    destruct (ptr_eqb k q); [exact ND|]. cbn. constructor; [| apply IH; exact ND].
    intros HIn. apply NI. eapply (files_remove_keys ptr_eqb). exact HIn.
  Qed.

  (* [comment removed for export] *)
  Lemma files_R_mid : forall m prev fs (F1 F2 : list cblk) q A n,
    files_R m prev fs (F1 ++ (q, A, n) :: F2) -> List.NoDup (map fst fs) ->
    exists f,
      files_lookup ptr_eqb fs q = Some f /\ In (q, f) fs /\ n = FILE_ALLOC /\ 0 < A /\ A + FILE_ALLOC < 2^63
      /\ FILE_R m f A (A + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK (last_addr prev F1) (hd_addr F2)
      /\ heap_file_inv f
      /\ (F1 <> [] -> rw_cells asegs m (last_addr prev F1 + 112) [C8 (Z_to_bv 64 A)] /\ 0 < last_addr prev F1)
      /\ (F2 <> [] -> rw_cells asegs m (hd_addr F2 + 104) [C8 (Z_to_bv 64 A)] /\ 0 < hd_addr F2).
  Proof using EQB. pin_using (fun (EQB : unit) => tt).
    intros m prev fs F1; revert prev fs.
    induction F1 as [|[[q1 A1] n1] F1 IH]; intros prev fs F2 q A n FS ND.
    - cbn [app] in FS. destruct fs as [|[q' f] fs']; [exact (False_ind _ FS)|].
      cbn [files_R] in FS. destruct FS as (<- & -> & A0 & Ahi & FR & INV & REST).
      exists f. cbn [files_lookup last_addr]. rewrite (eqb_refl' ptr_eqb EQB).
      split; [reflexivity|]. split; [left; reflexivity|]. split; [reflexivity|]. split; [exact A0|]. split; [exact Ahi|].
      split; [exact FR|]. split; [exact INV|]. split; [intros NE; exfalso; exact (NE eq_refl)|].
      intros NE2. destruct F2 as [|[[q2 A2] n2] F2']; [exfalso; exact (NE2 eq_refl)|]. cbn [hd_addr].
      destruct fs' as [|[q2' f2] fs'']; [exact (False_ind _ REST)|]. cbn [files_R] in REST.
      destruct REST as (_ & _ & B0 & _ & FR2 & _). split; [| exact B0].
      exact (proj1 (FILE_R_link_cells _ _ _ _ _ _ _ _ _ FR2)).
    - cbn [app] in FS. destruct fs as [|[q1' f1] fs']; [exact (False_ind _ FS)|].
      cbn [files_R] in FS. destruct FS as (<- & -> & A10 & A1hi & FR1 & INV1 & REST).
      cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
      destruct (IH A1 fs' F2 q A n REST ND) as (f & LK & INf & En & A0 & Ahi & FR & INV & HP & HN).
      assert (NE : q1 <> q) by (intros ->; apply NI; change q with (fst (q, f)); apply in_map; exact INf).
      exists f. cbn [files_lookup]. rewrite (eqb_neq ptr_eqb EQB _ _ NE).
      split; [exact LK|]. split; [right; exact INf|]. split; [exact En|]. split; [exact A0|]. split; [exact Ahi|].
      split; [exact FR|]. split; [exact INV|]. split; [| exact HN].
      intros _. cbn [last_addr]. destruct F1 as [|b F1'].
      + cbn [last_addr app hd_addr] in FR1 |- *. split; [| exact A10]. exact (proj2 (FILE_R_link_cells _ _ _ _ _ _ _ _ _ FR1)).
      + apply HP. discriminate.
  Qed.

  (* [comment removed for export] *)
  Lemma files_remove_mid : forall m prev fs (F1 F2 : list cblk) q A n,
    files_R m prev fs (F1 ++ (q, A, n) :: F2) -> List.NoDup (map fst fs) ->
    exists fs1 f fs2, fs = fs1 ++ (q, f) :: fs2 /\ length fs1 = length F1 /\ files_remove ptr_eqb fs q = fs1 ++ fs2.
  Proof using EQB. pin_using (fun (EQB : unit) => tt).
    intros m prev fs F1; revert prev fs.
    induction F1 as [|[[q1 A1] n1] F1 IH]; intros prev fs F2 q A n FS ND.
    - cbn [app] in FS. destruct fs as [|[q' f] fs']; [exact (False_ind _ FS)|].
      cbn [files_R] in FS. destruct FS as (<- & _).
      exists [], f, fs'. cbn. rewrite (eqb_refl' ptr_eqb EQB). repeat split; reflexivity.
    - cbn [app] in FS. destruct fs as [|[q1' f1] fs']; [exact (False_ind _ FS)|].
      cbn [files_R] in FS. destruct FS as (<- & _ & _ & _ & _ & _ & REST).
      cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
      destruct (IH A1 fs' F2 q A n REST ND) as (fs1 & f & fs2 & -> & L & RM).
      assert (NE : q1 <> q).
      { intros ->. apply NI. rewrite map_app. apply in_or_app. right. left. reflexivity. }
      exists ((q1, f1) :: fs1), f, fs2. cbn. rewrite (eqb_neq ptr_eqb EQB _ _ NE), RM, L. repeat split; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma files_R_unlink : forall (P : Z -> Prop) m m' prev fs (F1 F2 : list cblk) q A n,
    files_R m prev fs (F1 ++ (q, A, n) :: F2) -> List.NoDup (map fst fs) ->
    agrees_on P m m' ->
    (forall q2 A2 n2 a, In (q2, A2, n2) (F1 ++ F2) -> A2 <= a < A2 + 1264 ->
          ~ (A2 = last_addr prev F1 /\ A2 + 112 <= a < A2 + 120) -> ~ (A2 = hd_addr F2 /\ A2 + 104 <= a < A2 + 112) -> P a) ->
    (forall q2 A2 n2 q3 A3 n3, In (q2, A2, n2) (F1 ++ (q, A, n) :: F2) -> In (q3, A3, n3) (F1 ++ (q, A, n) :: F2) -> A2 = A3 -> q2 = q3) ->
    (F1 <> [] -> rw_cells asegs m' (last_addr prev F1 + 112) [C8 (Z_to_bv 64 (hd_addr F2))]) ->
    (F2 <> [] -> rw_cells asegs m' (hd_addr F2 + 104) [C8 (Z_to_bv 64 (last_addr prev F1))]) ->
    prev <> A -> (forall q2 A2 n2, In (q2, A2, n2) (F1 ++ (q, A, n) :: F2) -> A2 <> prev) ->
    files_R m' prev (files_remove ptr_eqb fs q) (F1 ++ F2).
  Proof using EQB. pin_using (fun (EQB : unit) => tt).
    intros P m m' prev fs F1; revert prev fs.
    induction F1 as [|[[q1 A1] n1] F1 IH]; intros prev fs F2 q A n FS ND AG HP DIST LP LN PA PNA.
    - (* [comment removed for export] *)
      cbn [app] in FS |- *. destruct fs as [|[q' f] fs']; [exact (False_ind _ FS)|].
      cbn [files_R] in FS. destruct FS as (<- & -> & A0 & Ahi & FR & INV & REST).
      cbn [files_remove]. rewrite (eqb_refl' ptr_eqb EQB).
      cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
      cbn [last_addr] in LN, HP.
      destruct F2 as [|[[q2 A2] n2] F2']; destruct fs' as [|[q2' f2] fs'']; try exact (False_ind _ REST); [exact I|].
      cbn [files_R] in REST |- *. destruct REST as (<- & -> & B0 & Bhi & FR2 & INV2 & REST2).
      cbn [hd_addr] in LN, HP.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact B0|]. split; [exact Bhi|].
      pose proof INV2 as (_ & _ & BS2 & _).
      split.
      { pose proof (FILE_R_link_cells _ _ _ _ _ _ _ _ _ FR2) as [_ NC2].
        assert (A2P : A2 <> prev) by (eapply (PNA q2 A2 FILE_ALLOC); right; left; reflexivity).
        eapply (FILE_R_relink P); [exact FR2| exact AG| | | exact (LN ltac:(discriminate))|].
        - intros a Ha Hn. eapply (HP q2 A2 FILE_ALLOC a); [left; reflexivity| unfold FILE_ALLOC; lia| intros [X _]; exact (A2P X) | intros [_ X]; lia].
        - rewrite BS2. unfold BUFSIZ, FILE_BUF_OFF. intros a Ha. eapply (HP q2 A2 FILE_ALLOC a); [left; reflexivity| unfold FILE_ALLOC; lia| intros [X _]; exact (A2P X)| intros [_ X]; lia].
        - eapply agrees_rw_cells; [exact AG| exact NC2|]. cbn. intros a Ha.
          eapply (HP q2 A2 FILE_ALLOC a); [left; reflexivity| unfold FILE_ALLOC; lia| intros [X _]; exact (A2P X)| intros [_ X]; lia]. }
      split; [exact INV2|].
      eapply files_R_frame; [exact REST2|].
      intros q3 A3 n3 f3 pv3 nx3 HIN3 FR3 INV3. pose proof INV3 as (_ & _ & BS3 & _).
      assert (N3A : A3 <> A2).
      { intros E. pose proof (DIST q3 A3 n3 q2 A2 FILE_ALLOC ltac:(right; right; exact HIN3) ltac:(right; left; reflexivity) E) as Eq.
        subst q3 A3. apply List.NoDup_cons_iff in ND as [NI2 _]. apply NI2.
        pose proof (files_R_toks _ _ _ _ REST2) as TK. pose proof (in_map cb_tok _ _ HIN3) as X. cbn [cb_tok fst snd] in X. exact (eq_ind _ (fun l => In _ l) X _ TK). }
      assert (N3P : A3 <> prev) by (eapply PNA; right; right; exact HIN3).
      eapply (FILE_R_relink_same P); [exact FR3| exact AG| |].
      + intros a Ha. eapply (HP q3 A3 n3 a); [right; exact HIN3| lia| intros [X _]; exact (N3P X)| intros [X _]; exact (N3A X)].
      + rewrite BS3. unfold BUFSIZ, FILE_BUF_OFF. intros a Ha. eapply (HP q3 A3 n3 a); [right; exact HIN3| lia| intros [X _]; exact (N3P X)| intros [X _]; exact (N3A X)].
    - (* [comment removed for export] *)
      cbn [app] in FS |- *. destruct fs as [|[q1' f1] fs']; [exact (False_ind _ FS)|].
      cbn [files_R] in FS. destruct FS as (<- & -> & A10 & A1hi & FR1 & INV1 & REST).
      cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
      pose proof (files_R_mid m A1 fs' F1 F2 q A n REST ND) as (f & _ & INf & _).
      assert (NE : q1 <> q) by (intros ->; apply NI; change q with (fst (q, f)); apply in_map; exact INf).
      cbn [files_remove]. rewrite (eqb_neq ptr_eqb EQB _ _ NE). cbn [files_R].
      split; [reflexivity|]. split; [reflexivity|]. split; [exact A10|]. split; [exact A1hi|].
      pose proof INV1 as (_ & _ & BS1 & _).
      assert (A1A : A1 <> A).
      { intros E. pose proof (DIST q1 A1 FILE_ALLOC q A n ltac:(left; reflexivity) ltac:(apply in_or_app; right; left; reflexivity) E) as Eq. exact (NE Eq). }
      assert (A1F2 : F2 <> [] -> A1 <> hd_addr F2).
      { intros NE2 E. destruct (hd_addr_In F2 NE2) as (q2 & n2 & HIN2).
        pose proof (DIST q1 A1 FILE_ALLOC q2 (hd_addr F2) n2 ltac:(left; reflexivity) ltac:(apply in_or_app; right; right; exact HIN2) E) as Eq.
        subst q2. apply NI. pose proof (files_R_toks _ _ _ _ REST) as TK.
        pose proof (in_map cb_tok _ _ (in_or_app F1 ((q, A, n) :: F2) (q1, hd_addr F2, n2) (or_intror (or_intror HIN2)))) as X.
        cbn [cb_tok fst snd] in X. exact (eq_ind _ (fun l => In _ l) X _ TK). }
      split.
      { destruct F1 as [|[[q1b A1b] n1b] F1'].
        - (* [comment removed for export] *)
          cbn [last_addr app hd_addr] in FR1, LP |- *.
          pose proof (FILE_R_link_cells _ _ _ _ _ _ _ _ _ FR1) as [PC1 _].
          eapply (FILE_R_relink P); [exact FR1| exact AG| | | | exact (LP ltac:(discriminate))].
          + intros a Ha Hn. eapply (HP q1 A1 FILE_ALLOC a); [left; reflexivity| unfold FILE_ALLOC; lia| intros [_ X]; lia|].
            intros [E _]. exact (A1F2 ltac:(intros E2; rewrite E2 in E; cbn in E; lia) E).
          + rewrite BS1. unfold BUFSIZ, FILE_BUF_OFF. intros a Ha. eapply (HP q1 A1 FILE_ALLOC a); [left; reflexivity| unfold FILE_ALLOC; lia| intros [_ X]; lia| intros [_ X]; lia].
          + eapply agrees_rw_cells; [exact AG| exact PC1|]. cbn. intros a Ha.
            eapply (HP q1 A1 FILE_ALLOC a); [left; reflexivity| unfold FILE_ALLOC; lia| intros [_ X]; lia|].
            intros [X _]. exact (A1F2 ltac:(intros E2; rewrite E2 in X; cbn in X; lia) X).
        - (* [comment removed for export] *)
          cbn [last_addr app hd_addr] in FR1 |- *.
          assert (A1L : A1 <> last_addr A1b F1').
          { intros E. destruct (last_addr_In A1b F1' ) as (ql & nl & HINl).
            all: cycle 1.
            { pose proof (DIST q1 A1 FILE_ALLOC ql (last_addr A1b F1') nl ltac:(left; reflexivity) ltac:(right; right; apply in_or_app; left; exact HINl) E) as Eq.
              subst ql. apply NI. pose proof (files_R_toks _ _ _ _ REST) as TK.
              pose proof (in_map cb_tok _ _ (or_intror (in_or_app F1' ((q, A, n) :: F2) (q1, last_addr A1b F1', nl) (or_introl HINl)) : In (q1, last_addr A1b F1', nl) (((q1b, A1b, n1b) :: F1') ++ (q, A, n) :: F2))) as X.
              cbn [cb_tok fst snd] in X. exact (eq_ind _ (fun l => In _ l) X _ TK). }
            (* [comment removed for export] *)
            intros E'. subst F1'. cbn in E.
            pose proof (DIST q1 A1 FILE_ALLOC q1b A1b n1b ltac:(left; reflexivity) ltac:(right; left; reflexivity) E) as Eq.
            subst q1b. apply NI. pose proof (files_R_toks _ _ _ _ REST) as TK.
            pose proof (in_map cb_tok _ _ (or_introl eq_refl : In (q1, A1b, n1b) (((q1, A1b, n1b) :: []) ++ (q, A, n) :: F2))) as X.
            cbn [cb_tok fst snd] in X. exact (eq_ind _ (fun l => In _ l) X _ TK). }
          eapply (FILE_R_relink_same P); [exact FR1| exact AG| |].
          + intros a Ha. eapply (HP q1 A1 FILE_ALLOC a); [left; reflexivity| unfold FILE_ALLOC; lia| intros [X _]; exact (A1L X)| intros [X _]].
            exact (A1F2 ltac:(intros E2; rewrite E2 in X; cbn in X; lia) X).
          + rewrite BS1. unfold BUFSIZ, FILE_BUF_OFF. intros a Ha. eapply (HP q1 A1 FILE_ALLOC a); [left; reflexivity| unfold FILE_ALLOC; lia| intros [X _]; exact (A1L X)| intros [X _]].
            exact (A1F2 ltac:(intros E2; rewrite E2 in X; cbn in X; lia) X). }
      split; [exact INV1|].
      eapply (IH A1 fs' F2 q A n); [exact REST| exact ND| exact AG| | | intros _; exact (LP ltac:(discriminate))| exact LN| exact A1A|].
      + intros q2 A2 n2 a HIN2. apply (HP q2 A2 n2 a). right. exact HIN2.
      + intros q2 A2 n2 q3 A3 n3 HIN2 HIN3. apply (DIST q2 A2 n2 q3 A3 n3); right; assumption.
      + intros q2 A2 n2 HIN2 E. subst A2.
        pose proof (DIST q1 A1 FILE_ALLOC q2 A1 n2 ltac:(left; reflexivity) ltac:(right; exact HIN2) eq_refl) as Eq. subst q2.
        apply NI. pose proof (files_R_toks _ _ _ _ REST) as TK.
        pose proof (in_map cb_tok _ _ HIN2) as X. cbn [cb_tok fst snd] in X. exact (eq_ind _ (fun l => In _ l) X _ TK).
  Qed.
End Unlink.

Section DropEmpty.
  Lemma munch_drop_empty : forall (W : list (Z * Z)) m m', munch W m m' -> munch (@List.filter (Z * Z)%type (fun iv : Z * Z => fst iv <? snd iv) W) m m'.
  Proof using Type. pin_using tt.
    intros W m m' MU. eapply munch_weaken; [| exact MU]. unfold sub_fp. clear MU.
    induction W as [|[lo hi] W IH]; intros x Hx; cbn in *; [exact I|].
    destruct (lo <? hi) eqn:E; cbn in Hx.
    - destruct Hx as [H1 H2]. split; [exact H1| apply IH; exact H2].
    - apply Z.ltb_ge in E. split; [lia| apply IH; exact Hx].
  Qed.
  Lemma Forall_drop_empty : forall (Q : Z * Z -> Prop) W,
    Forall (fun iv => snd iv <= fst iv \/ Q iv) W -> Forall Q (@List.filter (Z * Z)%type (fun iv : Z * Z => fst iv <? snd iv) W).
  Proof using Type. pin_using tt.
    intros Q W HF. induction HF as [|iv W HQ HF IH]; cbn; [constructor|].
    destruct (fst iv <? snd iv) eqn:E; [| exact IH]. apply Z.ltb_lt in E.
    constructor; [| exact IH]. destruct HQ as [HQ|HQ]; [lia| exact HQ].
  Qed.

End DropEmpty.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueKitA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section WithRc.
Context {rc : runConstT}.
Section Relink.
  Lemma fcells_split_links : forall flags rp re cf we wp wb rf wf sf b bs pv nx fd md lbf tl,
    fcells flags rp re cf we wp wb rf wf sf b bs pv nx fd md lbf tl =
    [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 rp); C8 (Z_to_bv 64 re); C8 (Z_to_bv 64 cf);
     C8 (Z_to_bv 64 we); C8 (Z_to_bv 64 wp); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wb);
     C8 (Z_to_bv 64 rf); C8 (Z_to_bv 64 wf); C8 (Z_to_bv 64 sf); C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 bs)]
    ++ [C8 (Z_to_bv 64 pv)] ++ [C8 (Z_to_bv 64 nx)]
    ++ [C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
        C4 md; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0); CB 80 tl].
  Proof using Type. pin_using tt. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma FILE_R_link_cells : forall m f Fp BA cf rf sf pv nx,
    FILE_R m f Fp BA cf rf sf pv nx ->
    rw_cells asegs m (Fp + 104) [C8 (Z_to_bv 64 pv)] /\ rw_cells asegs m (Fp + 112) [C8 (Z_to_bv 64 nx)].
  Proof using Type. pin_using tt.
    intros m f Fp BA cf rf sf pv nx (flags & mode & rp & tail & bufbytes & FC & _).
    rewrite fcells_split_links in FC. apply (proj1 (rw_cells_app asegs m Fp _ _)) in FC as [_ FC].
    apply (proj1 (rw_cells_app asegs m _ [_] _)) in FC as [FP FC]. apply (proj1 (rw_cells_app asegs m _ [_] _)) in FC as [FN _].
    cbn [cells_size csize Nat.add] in FP, FN.
    replace (Fp + Z.of_nat 104) with (Fp + 104) in FP by lia.
    replace (Fp + Z.of_nat 104 + Z.of_nat 8) with (Fp + 112) in FN by lia.
    split; [exact FP| exact FN].
  Qed.

  (* [comment removed for export] *)
  Lemma FILE_R_relink : forall (P : Z -> Prop) m m' f Fp BA cf rf sf pv nx pv' nx',
    FILE_R m f Fp BA cf rf sf pv nx ->
    agrees_on P m m' ->
    (forall a, Fp <= a < Fp + 232 -> ~ (Fp + 104 <= a < Fp + 120) -> P a) ->
    (forall a, BA <= a < BA + f_bufsize f -> P a) ->
    rw_cells asegs m' (Fp + 104) [C8 (Z_to_bv 64 pv')] -> rw_cells asegs m' (Fp + 112) [C8 (Z_to_bv 64 nx')] ->
    FILE_R m' f Fp BA cf rf sf pv' nx'.
  Proof using Type. pin_using tt.
    intros P m m' f Fp BA cf rf sf pv nx pv' nx' FR AG HP1 HP2 PC NC.
    destruct FR as (flags & mode & rp & tail & bufbytes & FC & FL & BUF & BP & WB0 & WBL & RR & RP).
    exists flags, mode, rp, tail, bufbytes.
    split; [| split; [exact FL | split; [| split; [exact BP | split; [exact WB0 | split; [exact WBL | split; [exact RR | exact RP]]]]]]].
    - rewrite fcells_split_links in FC |- *.
      apply (proj1 (rw_cells_app asegs m Fp _ _)) in FC as [FCa FC]. apply (proj1 (rw_cells_app asegs m _ [_] _)) in FC as [_ FC].
      apply (proj1 (rw_cells_app asegs m _ [_] _)) in FC as [_ FCb].
      cbn [cells_size csize Nat.add] in FCa, FCb |- *.
      apply (proj2 (rw_cells_app asegs m' Fp _ _)). split.
      + eapply agrees_rw_cells; [exact AG| exact FCa|]. cbn [cells_size csize Nat.add]. intros a Ha. apply HP1; lia.
      + apply (proj2 (rw_cells_app asegs m' _ [_] _)). cbn [cells_size csize Nat.add]. split.
        * replace (Fp + Z.of_nat 104) with (Fp + 104) by lia. exact PC.
        * apply (proj2 (rw_cells_app asegs m' _ [_] _)). cbn [cells_size csize Nat.add]. split.
          -- replace (Fp + Z.of_nat 104 + Z.of_nat 8) with (Fp + 112) by lia. exact NC.
          -- eapply agrees_rw_cells; [exact AG| exact FCb|]. cbn [cells_size csize Nat.add]. intros a Ha. apply HP1; lia.
    - pose proof (rw_cells_bound _ _ _ _ BUF) as BB. cbn [cells_size csize Nat.add] in BB.
      eapply agrees_rw_cells; [exact AG | exact BUF |]. cbn [cells_size csize Nat.add]. intros a Ha. apply HP2. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma FILE_R_relink_same : forall (P : Z -> Prop) m m' f Fp BA cf rf sf pv nx,
    FILE_R m f Fp BA cf rf sf pv nx ->
    agrees_on P m m' ->
    (forall a, Fp <= a < Fp + 232 -> P a) -> (forall a, BA <= a < BA + f_bufsize f -> P a) ->
    FILE_R m' f Fp BA cf rf sf pv nx.
  Proof using Type. pin_using tt.
    intros P m m' f Fp BA cf rf sf pv nx FR AG HP1 HP2.
    pose proof (FILE_R_link_cells _ _ _ _ _ _ _ _ _ FR) as [PC NC].
    eapply FILE_R_relink; [exact FR| exact AG| intros a Ha _; apply HP1; exact Ha| exact HP2| |].
    - eapply agrees_rw_cells; [exact AG| exact PC|]. cbn. intros a Ha. apply HP1. lia.
    - eapply agrees_rw_cells; [exact AG| exact NC|]. cbn. intros a Ha. apply HP1. lia.
  Qed.
End Relink.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Unlink.
  Context {hptr : Type} (ptr_eqb : hptr -> hptr -> bool).
  Hypothesis EQB : forall p q, ptr_eqb p q = true <-> p = q.
  #[local] Notation cblk := (@cblock hptr).

  (* [comment removed for export] *)
  Fixpoint last_addr (prev : Z) (FB : list cblk) : Z :=
    match FB with [] => prev | (_, A, _) :: FB' => last_addr A FB' end.

  Lemma last_addr_app : forall prev (F1 F2 : list cblk), last_addr prev (F1 ++ F2) = last_addr (last_addr prev F1) F2.
  Proof using Type. pin_using tt. intros prev F1; revert prev. induction F1 as [|[[q A] n] F1 IH]; intros prev F2; cbn; [reflexivity| apply IH]. Qed.

  Lemma last_addr_In : forall prev (FB : list cblk), FB <> [] -> exists q n, In (q, last_addr prev FB, n) FB.
  Proof using Type. pin_using tt.
    intros prev FB; revert prev. induction FB as [|[[q A] n] FB IH]; intros prev NE; [exfalso; exact (NE eq_refl)|].
    cbn. destruct FB as [|b FB'].
    - exists q, n. left. reflexivity.
    - destruct (IH A ltac:(discriminate)) as (q' & n' & HIN). exists q', n'. right. exact HIN.
  Qed.

  Lemma hd_addr_app : forall (F1 F2 : list cblk), F1 <> [] -> hd_addr (F1 ++ F2) = hd_addr F1.
  Proof using Type. pin_using tt. intros [|[[q A] n] F1] F2 NE; [exfalso; exact (NE eq_refl)| reflexivity]. Qed.

  Lemma hd_addr_In : forall (FB : list cblk), FB <> [] -> exists q n, In (q, hd_addr FB, n) FB.
  Proof using Type. pin_using tt. intros [|[[q A] n] FB] NE; [exfalso; exact (NE eq_refl)|]. exists q, n. left. reflexivity. Qed.

  Lemma NoDup_files_remove : forall fs q, List.NoDup (map fst fs) -> List.NoDup (map fst (files_remove ptr_eqb fs q)).
  Proof using Type. pin_using tt.
    induction fs as [|[k g] fs IH]; intros q ND; cbn; [constructor|].
    cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
    destruct (ptr_eqb k q); [exact ND|]. cbn. constructor; [| apply IH; exact ND].
    intros HIn. apply NI. eapply (files_remove_keys ptr_eqb). exact HIn.
  Qed.

  (* [comment removed for export] *)
  Lemma files_R_mid : forall m prev fs (F1 F2 : list cblk) q A n,
    files_R m prev fs (F1 ++ (q, A, n) :: F2) -> List.NoDup (map fst fs) ->
    exists f,
      files_lookup ptr_eqb fs q = Some f /\ In (q, f) fs /\ n = FILE_ALLOC /\ 0 < A /\ A + FILE_ALLOC < 2^63
      /\ FILE_R m f A (A + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK (last_addr prev F1) (hd_addr F2)
      /\ heap_file_inv f
      /\ (F1 <> [] -> rw_cells asegs m (last_addr prev F1 + 112) [C8 (Z_to_bv 64 A)] /\ 0 < last_addr prev F1)
      /\ (F2 <> [] -> rw_cells asegs m (hd_addr F2 + 104) [C8 (Z_to_bv 64 A)] /\ 0 < hd_addr F2).
  Proof using EQB. pin_using (fun (EQB : unit) => tt).
    intros m prev fs F1; revert prev fs.
    induction F1 as [|[[q1 A1] n1] F1 IH]; intros prev fs F2 q A n FS ND.
    - cbn [app] in FS. destruct fs as [|[q' f] fs']; [exact (False_ind _ FS)|].
      cbn [files_R] in FS. destruct FS as (<- & -> & A0 & Ahi & FR & INV & REST).
      exists f. cbn [files_lookup last_addr]. rewrite (eqb_refl' ptr_eqb EQB).
      split; [reflexivity|]. split; [left; reflexivity|]. split; [reflexivity|]. split; [exact A0|]. split; [exact Ahi|].
      split; [exact FR|]. split; [exact INV|]. split; [intros NE; exfalso; exact (NE eq_refl)|].
      intros NE2. destruct F2 as [|[[q2 A2] n2] F2']; [exfalso; exact (NE2 eq_refl)|]. cbn [hd_addr].
      destruct fs' as [|[q2' f2] fs'']; [exact (False_ind _ REST)|]. cbn [files_R] in REST.
      destruct REST as (_ & _ & B0 & _ & FR2 & _). split; [| exact B0].
      exact (proj1 (FILE_R_link_cells _ _ _ _ _ _ _ _ _ FR2)).
    - cbn [app] in FS. destruct fs as [|[q1' f1] fs']; [exact (False_ind _ FS)|].
      cbn [files_R] in FS. destruct FS as (<- & -> & A10 & A1hi & FR1 & INV1 & REST).
      cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
      destruct (IH A1 fs' F2 q A n REST ND) as (f & LK & INf & En & A0 & Ahi & FR & INV & HP & HN).
      assert (NE : q1 <> q) by (intros ->; apply NI; change q with (fst (q, f)); apply in_map; exact INf).
      exists f. cbn [files_lookup]. rewrite (eqb_neq ptr_eqb EQB _ _ NE).
      split; [exact LK|]. split; [right; exact INf|]. split; [exact En|]. split; [exact A0|]. split; [exact Ahi|].
      split; [exact FR|]. split; [exact INV|]. split; [| exact HN].
      intros _. cbn [last_addr]. destruct F1 as [|b F1'].
      + cbn [last_addr app hd_addr] in FR1 |- *. split; [| exact A10]. exact (proj2 (FILE_R_link_cells _ _ _ _ _ _ _ _ _ FR1)).
      + apply HP. discriminate.
  Qed.

  (* [comment removed for export] *)
  Lemma files_remove_mid : forall m prev fs (F1 F2 : list cblk) q A n,
    files_R m prev fs (F1 ++ (q, A, n) :: F2) -> List.NoDup (map fst fs) ->
    exists fs1 f fs2, fs = fs1 ++ (q, f) :: fs2 /\ length fs1 = length F1 /\ files_remove ptr_eqb fs q = fs1 ++ fs2.
  Proof using EQB. pin_using (fun (EQB : unit) => tt).
    intros m prev fs F1; revert prev fs.
    induction F1 as [|[[q1 A1] n1] F1 IH]; intros prev fs F2 q A n FS ND.
    - cbn [app] in FS. destruct fs as [|[q' f] fs']; [exact (False_ind _ FS)|].
      cbn [files_R] in FS. destruct FS as (<- & _).
      exists [], f, fs'. cbn. rewrite (eqb_refl' ptr_eqb EQB). repeat split; reflexivity.
    - cbn [app] in FS. destruct fs as [|[q1' f1] fs']; [exact (False_ind _ FS)|].
      cbn [files_R] in FS. destruct FS as (<- & _ & _ & _ & _ & _ & REST).
      cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
      destruct (IH A1 fs' F2 q A n REST ND) as (fs1 & f & fs2 & -> & L & RM).
      assert (NE : q1 <> q).
      { intros ->. apply NI. rewrite map_app. apply in_or_app. right. left. reflexivity. }
      exists ((q1, f1) :: fs1), f, fs2. cbn. rewrite (eqb_neq ptr_eqb EQB _ _ NE), RM, L. repeat split; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma files_R_unlink : forall (P : Z -> Prop) m m' prev fs (F1 F2 : list cblk) q A n,
    files_R m prev fs (F1 ++ (q, A, n) :: F2) -> List.NoDup (map fst fs) ->
    agrees_on P m m' ->
    (forall q2 A2 n2 a, In (q2, A2, n2) (F1 ++ F2) -> A2 <= a < A2 + 1264 ->
          ~ (A2 = last_addr prev F1 /\ A2 + 112 <= a < A2 + 120) -> ~ (A2 = hd_addr F2 /\ A2 + 104 <= a < A2 + 112) -> P a) ->
    (forall q2 A2 n2 q3 A3 n3, In (q2, A2, n2) (F1 ++ (q, A, n) :: F2) -> In (q3, A3, n3) (F1 ++ (q, A, n) :: F2) -> A2 = A3 -> q2 = q3) ->
    (F1 <> [] -> rw_cells asegs m' (last_addr prev F1 + 112) [C8 (Z_to_bv 64 (hd_addr F2))]) ->
    (F2 <> [] -> rw_cells asegs m' (hd_addr F2 + 104) [C8 (Z_to_bv 64 (last_addr prev F1))]) ->
    prev <> A -> (forall q2 A2 n2, In (q2, A2, n2) (F1 ++ (q, A, n) :: F2) -> A2 <> prev) ->
    files_R m' prev (files_remove ptr_eqb fs q) (F1 ++ F2).
  Proof using EQB. pin_using (fun (EQB : unit) => tt).
    intros P m m' prev fs F1; revert prev fs.
    induction F1 as [|[[q1 A1] n1] F1 IH]; intros prev fs F2 q A n FS ND AG HP DIST LP LN PA PNA.
    - (* [comment removed for export] *)
      cbn [app] in FS |- *. destruct fs as [|[q' f] fs']; [exact (False_ind _ FS)|].
      cbn [files_R] in FS. destruct FS as (<- & -> & A0 & Ahi & FR & INV & REST).
      cbn [files_remove]. rewrite (eqb_refl' ptr_eqb EQB).
      cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
      cbn [last_addr] in LN, HP.
      destruct F2 as [|[[q2 A2] n2] F2']; destruct fs' as [|[q2' f2] fs'']; try exact (False_ind _ REST); [exact I|].
      cbn [files_R] in REST |- *. destruct REST as (<- & -> & B0 & Bhi & FR2 & INV2 & REST2).
      cbn [hd_addr] in LN, HP.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact B0|]. split; [exact Bhi|].
      pose proof INV2 as (_ & _ & BS2 & _).
      split.
      { pose proof (FILE_R_link_cells _ _ _ _ _ _ _ _ _ FR2) as [_ NC2].
        assert (A2P : A2 <> prev) by (eapply (PNA q2 A2 FILE_ALLOC); right; left; reflexivity).
        eapply (FILE_R_relink P); [exact FR2| exact AG| | | exact (LN ltac:(discriminate))|].
        - intros a Ha Hn. eapply (HP q2 A2 FILE_ALLOC a); [left; reflexivity| unfold FILE_ALLOC; lia| intros [X _]; exact (A2P X) | intros [_ X]; lia].
        - rewrite BS2. unfold BUFSIZ, FILE_BUF_OFF. intros a Ha. eapply (HP q2 A2 FILE_ALLOC a); [left; reflexivity| unfold FILE_ALLOC; lia| intros [X _]; exact (A2P X)| intros [_ X]; lia].
        - eapply agrees_rw_cells; [exact AG| exact NC2|]. cbn. intros a Ha.
          eapply (HP q2 A2 FILE_ALLOC a); [left; reflexivity| unfold FILE_ALLOC; lia| intros [X _]; exact (A2P X)| intros [_ X]; lia]. }
      split; [exact INV2|].
      eapply files_R_frame; [exact REST2|].
      intros q3 A3 n3 f3 pv3 nx3 HIN3 FR3 INV3. pose proof INV3 as (_ & _ & BS3 & _).
      assert (N3A : A3 <> A2).
      { intros E. pose proof (DIST q3 A3 n3 q2 A2 FILE_ALLOC ltac:(right; right; exact HIN3) ltac:(right; left; reflexivity) E) as Eq.
        subst q3 A3. apply List.NoDup_cons_iff in ND as [NI2 _]. apply NI2.
        pose proof (files_R_toks _ _ _ _ REST2) as TK. pose proof (in_map cb_tok _ _ HIN3) as X. cbn [cb_tok fst snd] in X. exact (eq_ind _ (fun l => In _ l) X _ TK). }
      assert (N3P : A3 <> prev) by (eapply PNA; right; right; exact HIN3).
      eapply (FILE_R_relink_same P); [exact FR3| exact AG| |].
      + intros a Ha. eapply (HP q3 A3 n3 a); [right; exact HIN3| lia| intros [X _]; exact (N3P X)| intros [X _]; exact (N3A X)].
      + rewrite BS3. unfold BUFSIZ, FILE_BUF_OFF. intros a Ha. eapply (HP q3 A3 n3 a); [right; exact HIN3| lia| intros [X _]; exact (N3P X)| intros [X _]; exact (N3A X)].
    - (* [comment removed for export] *)
      cbn [app] in FS |- *. destruct fs as [|[q1' f1] fs']; [exact (False_ind _ FS)|].
      cbn [files_R] in FS. destruct FS as (<- & -> & A10 & A1hi & FR1 & INV1 & REST).
      cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
      pose proof (files_R_mid m A1 fs' F1 F2 q A n REST ND) as (f & _ & INf & _).
      assert (NE : q1 <> q) by (intros ->; apply NI; change q with (fst (q, f)); apply in_map; exact INf).
      cbn [files_remove]. rewrite (eqb_neq ptr_eqb EQB _ _ NE). cbn [files_R].
      split; [reflexivity|]. split; [reflexivity|]. split; [exact A10|]. split; [exact A1hi|].
      pose proof INV1 as (_ & _ & BS1 & _).
      assert (A1A : A1 <> A).
      { intros E. pose proof (DIST q1 A1 FILE_ALLOC q A n ltac:(left; reflexivity) ltac:(apply in_or_app; right; left; reflexivity) E) as Eq. exact (NE Eq). }
      assert (A1F2 : F2 <> [] -> A1 <> hd_addr F2).
      { intros NE2 E. destruct (hd_addr_In F2 NE2) as (q2 & n2 & HIN2).
        pose proof (DIST q1 A1 FILE_ALLOC q2 (hd_addr F2) n2 ltac:(left; reflexivity) ltac:(apply in_or_app; right; right; exact HIN2) E) as Eq.
        subst q2. apply NI. pose proof (files_R_toks _ _ _ _ REST) as TK.
        pose proof (in_map cb_tok _ _ (in_or_app F1 ((q, A, n) :: F2) (q1, hd_addr F2, n2) (or_intror (or_intror HIN2)))) as X.
        cbn [cb_tok fst snd] in X. exact (eq_ind _ (fun l => In _ l) X _ TK). }
      split.
      { destruct F1 as [|[[q1b A1b] n1b] F1'].
        - (* [comment removed for export] *)
          cbn [last_addr app hd_addr] in FR1, LP |- *.
          pose proof (FILE_R_link_cells _ _ _ _ _ _ _ _ _ FR1) as [PC1 _].
          eapply (FILE_R_relink P); [exact FR1| exact AG| | | | exact (LP ltac:(discriminate))].
          + intros a Ha Hn. eapply (HP q1 A1 FILE_ALLOC a); [left; reflexivity| unfold FILE_ALLOC; lia| intros [_ X]; lia|].
            intros [E _]. exact (A1F2 ltac:(intros E2; rewrite E2 in E; cbn in E; lia) E).
          + rewrite BS1. unfold BUFSIZ, FILE_BUF_OFF. intros a Ha. eapply (HP q1 A1 FILE_ALLOC a); [left; reflexivity| unfold FILE_ALLOC; lia| intros [_ X]; lia| intros [_ X]; lia].
          + eapply agrees_rw_cells; [exact AG| exact PC1|]. cbn. intros a Ha.
            eapply (HP q1 A1 FILE_ALLOC a); [left; reflexivity| unfold FILE_ALLOC; lia| intros [_ X]; lia|].
            intros [X _]. exact (A1F2 ltac:(intros E2; rewrite E2 in X; cbn in X; lia) X).
        - (* [comment removed for export] *)
          cbn [last_addr app hd_addr] in FR1 |- *.
          assert (A1L : A1 <> last_addr A1b F1').
          { intros E. destruct (last_addr_In A1b F1' ) as (ql & nl & HINl).
            all: cycle 1.
            { pose proof (DIST q1 A1 FILE_ALLOC ql (last_addr A1b F1') nl ltac:(left; reflexivity) ltac:(right; right; apply in_or_app; left; exact HINl) E) as Eq.
              subst ql. apply NI. pose proof (files_R_toks _ _ _ _ REST) as TK.
              pose proof (in_map cb_tok _ _ (or_intror (in_or_app F1' ((q, A, n) :: F2) (q1, last_addr A1b F1', nl) (or_introl HINl)) : In (q1, last_addr A1b F1', nl) (((q1b, A1b, n1b) :: F1') ++ (q, A, n) :: F2))) as X.
              cbn [cb_tok fst snd] in X. exact (eq_ind _ (fun l => In _ l) X _ TK). }
            (* [comment removed for export] *)
            intros E'. subst F1'. cbn in E.
            pose proof (DIST q1 A1 FILE_ALLOC q1b A1b n1b ltac:(left; reflexivity) ltac:(right; left; reflexivity) E) as Eq.
            subst q1b. apply NI. pose proof (files_R_toks _ _ _ _ REST) as TK.
            pose proof (in_map cb_tok _ _ (or_introl eq_refl : In (q1, A1b, n1b) (((q1, A1b, n1b) :: []) ++ (q, A, n) :: F2))) as X.
            cbn [cb_tok fst snd] in X. exact (eq_ind _ (fun l => In _ l) X _ TK). }
          eapply (FILE_R_relink_same P); [exact FR1| exact AG| |].
          + intros a Ha. eapply (HP q1 A1 FILE_ALLOC a); [left; reflexivity| unfold FILE_ALLOC; lia| intros [X _]; exact (A1L X)| intros [X _]].
            exact (A1F2 ltac:(intros E2; rewrite E2 in X; cbn in X; lia) X).
          + rewrite BS1. unfold BUFSIZ, FILE_BUF_OFF. intros a Ha. eapply (HP q1 A1 FILE_ALLOC a); [left; reflexivity| unfold FILE_ALLOC; lia| intros [X _]; exact (A1L X)| intros [X _]].
            exact (A1F2 ltac:(intros E2; rewrite E2 in X; cbn in X; lia) X). }
      split; [exact INV1|].
      eapply (IH A1 fs' F2 q A n); [exact REST| exact ND| exact AG| | | intros _; exact (LP ltac:(discriminate))| exact LN| exact A1A|].
      + intros q2 A2 n2 a HIN2. apply (HP q2 A2 n2 a). right. exact HIN2.
      + intros q2 A2 n2 q3 A3 n3 HIN2 HIN3. apply (DIST q2 A2 n2 q3 A3 n3); right; assumption.
      + intros q2 A2 n2 HIN2 E. subst A2.
        pose proof (DIST q1 A1 FILE_ALLOC q2 A1 n2 ltac:(left; reflexivity) ltac:(right; exact HIN2) eq_refl) as Eq. subst q2.
        apply NI. pose proof (files_R_toks _ _ _ _ REST) as TK.
        pose proof (in_map cb_tok _ _ HIN2) as X. cbn [cb_tok fst snd] in X. exact (eq_ind _ (fun l => In _ l) X _ TK).
  Qed.
End Unlink.

Section DropEmpty.
  Lemma munch_drop_empty : forall (W : list (Z * Z)) m m', munch W m m' -> munch (@List.filter (Z * Z)%type (fun iv : Z * Z => fst iv <? snd iv) W) m m'.
  Proof using Type. pin_using tt.
    intros W m m' MU. eapply munch_weaken; [| exact MU]. unfold sub_fp. clear MU.
    induction W as [|[lo hi] W IH]; intros x Hx; cbn in *; [exact I|].
    destruct (lo <? hi) eqn:E; cbn in Hx.
    - destruct Hx as [H1 H2]. split; [exact H1| apply IH; exact H2].
    - apply Z.ltb_ge in E. split; [lia| apply IH; exact Hx].
  Qed.
  Lemma Forall_drop_empty : forall (Q : Z * Z -> Prop) W,
    Forall (fun iv => snd iv <= fst iv \/ Q iv) W -> Forall Q (@List.filter (Z * Z)%type (fun iv : Z * Z => fst iv <? snd iv) W).
  Proof using Type. pin_using tt.
    intros Q W HF. induction HF as [|iv W HQ HF IH]; cbn; [constructor|].
    destruct (fst iv <? snd iv) eqn:E; [| exact IH]. apply Z.ltb_lt in E.
    constructor; [| exact IH]. destruct HQ as [HQ|HQ]; [lia| exact HQ].
  Qed.

End DropEmpty.
End WithRc.
End TwB.
