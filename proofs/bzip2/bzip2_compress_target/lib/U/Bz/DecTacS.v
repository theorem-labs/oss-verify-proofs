(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts DecCut DecTac.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil}.


Section DJ.
  Variables (fr : Z) (A : act14).
  Hypothesis AOK : act_ok fr A.
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).
  Notation L16 := (b_ll16 (a_cx A)).
  Notation L4 := (b_ll4 (a_cx A)).

  (* [comment removed for export] *)
  Lemma dj_s_16 : b_small cx = 1 -> forall a n, S <= a -> a + n <= S + 64144 -> (a + n <= L16 \/ L16 + 200000 * b_n cx <= a).
  Proof. intros E a n H1 H2. pose proof (act_ll _ _ AOK E) as X. lia. Qed.
  Lemma dj_s_4 : b_small cx = 1 -> forall a n, S <= a -> a + n <= S + 64144 -> (a + n <= L4 \/ L4 + 50000 * b_n cx <= a).
  Proof. intros E a n H1 H2. pose proof (act_ll _ _ AOK E) as X. lia. Qed.
  (* [comment removed for export] *)
  Lemma dj_i_16 : b_small cx = 1 -> forall a n, 65536 <= a -> a + n <= 212992 -> (a + n <= L16 \/ L16 + 200000 * b_n cx <= a).
  Proof. intros E a n H1 H2. pose proof (act_img_ll _ _ AOK E) as [X _]. lia. Qed.
  Lemma dj_i_4 : b_small cx = 1 -> forall a n, 65536 <= a -> a + n <= 212992 -> (a + n <= L4 \/ L4 + 50000 * b_n cx <= a).
  Proof. intros E a n H1 H2. pose proof (act_img_ll _ _ AOK E) as [_ X]. lia. Qed.
  Lemma dj_i_s : forall a n lo hi, 65536 <= a -> a + n <= 212992 -> S <= lo -> hi <= S + 64144 -> (a + n <= lo \/ hi <= a).
  Proof. intros a n lo hi H1 H2 H3 H4. pose proof (act_img_s _ _ AOK) as X. lia. Qed.
  (* [comment removed for export] *)
  Lemma dj_p_16 : b_small cx = 1 -> forall a n, a = b_src cx -> 0 <= n <= b_len cx -> (a + n <= L16 \/ L16 + 200000 * b_n cx <= a).
  Proof. intros E a n H1 H2. pose proof (act_ll _ _ AOK E) as X. lia. Qed.
  Lemma dj_p_4 : b_small cx = 1 -> forall a n, a = b_src cx -> 0 <= n <= b_len cx -> (a + n <= L4 \/ L4 + 50000 * b_n cx <= a).
  Proof. intros E a n H1 H2. pose proof (act_ll _ _ AOK E) as X. lia. Qed.
  Lemma dj_p_s : forall a n lo hi, a = b_src cx -> 0 <= n <= b_len cx -> S <= lo -> hi <= S + 64144 -> (a + n <= lo \/ hi <= a).
  Proof. intros a n lo hi H1 H2 H3 H4. pose proof (act_sep_s_src _ _ AOK) as X. lia. Qed.
  Notation TT := (b_tt (a_cx A)).
  (* [comment removed for export] *)
  Lemma dj_s_tt : b_small cx = 0 -> forall a n, S <= a -> a + n <= S + 64144 -> (a + n <= TT \/ TT + 400000 * b_n cx <= a).
  Proof. intros E a n H1 H2. pose proof (act_tt _ _ AOK E) as X. lia. Qed.
  Lemma dj_i_tt : b_small cx = 0 -> forall a n, 65536 <= a -> a + n <= 212992 -> (a + n <= TT \/ TT + 400000 * b_n cx <= a).
  Proof. intros E a n H1 H2. pose proof (act_img_tt _ _ AOK E) as X. lia. Qed.
  Lemma dj_p_tt : b_small cx = 0 -> forall a n, a = b_src cx -> 0 <= n <= b_len cx -> (a + n <= TT \/ TT + 400000 * b_n cx <= a).
  Proof. intros E a n H1 H2. pose proof (act_tt _ _ AOK E) as X. lia. Qed.
  (* [comment removed for export] *)
  Lemma dj_tt_s : b_small cx = 0 -> forall n lo hi, n <= 400000 * b_n cx -> S <= lo -> hi <= S + 64144 -> (TT + n <= lo \/ hi <= TT).
  Proof. intros E n lo hi H1 H2 H3. pose proof (act_tt _ _ AOK E) as X. lia. Qed.
  Lemma dj_16_s : b_small cx = 1 -> forall n lo hi, n <= 200000 * b_n cx -> S <= lo -> hi <= S + 64144 -> (L16 + n <= lo \/ hi <= L16).
  Proof. intros E n lo hi H1 H2 H3. pose proof (act_ll _ _ AOK E) as X. lia. Qed.
  Lemma dj_4_s : b_small cx = 1 -> forall n lo hi, n <= 50000 * b_n cx -> S <= lo -> hi <= S + 64144 -> (L4 + n <= lo \/ hi <= L4).
  Proof. intros E n lo hi H1 H2 H3. pose proof (act_ll _ _ AOK E) as X. lia. Qed.
  Lemma dj_16_4 : b_small cx = 1 -> forall n hi, n <= 200000 * b_n cx -> hi <= L4 + 50000 * b_n cx -> (L16 + n <= L4 \/ hi <= L16).
  Proof. intros E n hi H1 H2. pose proof (act_ll _ _ AOK E) as X. lia. Qed.
  Lemma dj_4_16 : b_small cx = 1 -> forall n hi, n <= 50000 * b_n cx -> hi <= L16 + 200000 * b_n cx -> (L4 + n <= L16 \/ hi <= L4).
  Proof. intros E n hi H1 H2. pose proof (act_ll _ _ AOK E) as X. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma act_lin_core :
    0 < S /\ S + 64144 <= alloc_ceiling /\ alloc_ceiling <= a_lo A /\ a_lo A <= a_usp A - 1024 /\
    a_usp A < 18446744073709551616 /\ a_usp A <= b_strm cx /\ b_strm cx = b_sp cx /\ alloc_ceiling <= b_sp cx /\
    b_sp cx + 176 <= 140737488355328 /\ 0 < b_src cx /\ 0 <= b_len cx /\ b_src cx + b_len cx <= alloc_ceiling /\
    Z.of_nat (length (a_payload A)) = b_len cx /\ 1 <= b_n cx <= 9 /\ 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000.
  Proof.
    pose proof AOK as Y.
    cps_destruct Y as (CTX & LO1 & LO2 & USP & ST14 & HWF0 & BWF0 & PL & HS0 & HN0 & HSM0 & N1 & QS & QSRC & QLEN & QDST & QDLEN & USTRM & NZF & NZS & SM01).
    cps_destruct CTX as (LIN & AL & SEP).
    unfold ctx_lin in LIN. cbv zeta in LIN. bz_ceil; unfold IMG_HI_MAX, DSTATE_SIZE, CEILING, STACK_TOP in LIN.
    bz_ceil; unfold CEILING in LO2. unfold D14 in LO1.
    (* [comment removed for export] *)
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
  Qed.
  Lemma act_lin_tt : b_small cx = 0 -> 0 < TT /\ TT + 400000 * b_n cx <= alloc_ceiling.
  Proof. intros E. pose proof (act_tt _ _ AOK E). tauto. Qed.
  Lemma act_lin_ll : b_small cx = 1 -> 0 < L16 /\ L16 + 200000 * b_n cx <= alloc_ceiling /\ 0 < L4 /\ L4 + 50000 * b_n cx <= alloc_ceiling.
  Proof. intros E. pose proof (act_ll _ _ AOK E). tauto. Qed.
End DJ.

(* [comment removed for export] *)
Section DrestCfc.
  Variable segs : list Segment.
  Lemma disjoint_from_sub : forall W a n a' n', disjoint_from W a n -> (a <= a')%Z -> (a' + n' <= a + n)%Z -> (0 <= n')%Z ->
    disjoint_from W a' n'.
  Proof.
    induction W as [|[lo hi] W IH]; intros a n a' n' D H1 H2 H3; cbn in *; [exact I|].
    destruct D as [D1 D2]. split; [lia| eapply IH; eauto].
  Qed.
  Lemma drest_keep_cfc : forall W m m' S r cfc',
    drest_at segs m S r -> munch W m m' -> wmono segs m m' ->
    disjoint_from W (S + 68) 1024 -> disjoint_from W (S + 3196) 60840 ->
    u32arr segs m' (S + 2124) cfc' -> Z.of_nat (length cfc') = 257%Z ->
    drest_at segs m' S (DREST (r_unz r) cfc' (r_inUse r) (r_in16 r) (r_s2u r) (r_mtfa r) (r_mtfb r) (r_sel r) (r_selm r)
                            (r_len r) (r_lim r) (r_base r) (r_perm r) (r_minl r)).
  Proof.
    intros W m m' S r cfc' D MU WM D1 D2 AC LC.
    cps_destruct D as ((A1&L1)&(A2&L2)&(A3&L3)&(A4&L4)&(A5&L5)&(A6&L6)&(A7&L7)&(A8&L8)&(A9&L9)&(A10&L10)&(A11&L11)&(A12&L12)&(A13&L13)&(A14&L14)).
    unfold drest_at; cbn [r_unz r_cfc r_inUse r_in16 r_s2u r_mtfa r_mtfb r_sel r_selm r_len r_lim r_base r_perm r_minl].
    Ltac tr32 A L MU WM D := split; [eapply u32arr_transport; [exact A| exact MU| exact WM| rewrite L; eapply (disjoint_from_sub _ _ _ _ _ D); lia] | exact L].
    Ltac tr8 A L MU WM D := split; [eapply u8arr_transport; [exact A| exact MU| exact WM| rewrite L; eapply (disjoint_from_sub _ _ _ _ _ D); lia] | exact L].
    split; [tr32 A1 L1 MU WM D1|]. split; [split; [exact AC| exact LC]|]. split; [tr8 A3 L3 MU WM D2|]. split; [tr8 A4 L4 MU WM D2|].
    split; [tr8 A5 L5 MU WM D2|]. split; [tr8 A6 L6 MU WM D2|]. split; [tr32 A7 L7 MU WM D2|]. split; [tr8 A8 L8 MU WM D2|].
    split; [tr8 A9 L9 MU WM D2|]. split; [tr8 A10 L10 MU WM D2|]. split; [tr32 A11 L11 MU WM D2|]. split; [tr32 A12 L12 MU WM D2|].
    split; [tr32 A13 L13 MU WM D2| tr32 A14 L14 MU WM D2].
  Qed.
  (* [comment removed for export] *)
  Lemma drest_keep_mtf : forall W m m' S r mtfa' mtfb',
    drest_at segs m S r -> munch W m m' -> wmono segs m m' ->
    disjoint_from W (S + 68) 3656 -> disjoint_from W (S + 7884) 56152 ->
    u8arr segs m' (S + 3724) mtfa' -> Z.of_nat (length mtfa') = 4096%Z ->
    u32arr segs m' (S + 7820) mtfb' -> Z.of_nat (length mtfb') = 16%Z ->
    drest_at segs m' S (DREST (r_unz r) (r_cfc r) (r_inUse r) (r_in16 r) (r_s2u r) mtfa' mtfb' (r_sel r) (r_selm r)
                            (r_len r) (r_lim r) (r_base r) (r_perm r) (r_minl r)).
  Proof.
    intros W m m' S r mtfa' mtfb' D MU WM D1 D2 A6 L6 A7 L7.
    cps_destruct D as ((A1&L1)&(A2&L2)&(A3&L3)&(A4&L4)&(A5&L5)&(B6&M6)&(B7&M7)&(A8&L8)&(A9&L9)&(A10&L10)&(A11&L11)&(A12&L12)&(A13&L13)&(A14&L14)).
    unfold drest_at; cbn [r_unz r_cfc r_inUse r_in16 r_s2u r_mtfa r_mtfb r_sel r_selm r_len r_lim r_base r_perm r_minl].
    Ltac tr32' A L MU WM D := split; [eapply u32arr_transport; [exact A| exact MU| exact WM| rewrite L; eapply (disjoint_from_sub _ _ _ _ _ D); lia] | exact L].
    Ltac tr8' A L MU WM D := split; [eapply u8arr_transport; [exact A| exact MU| exact WM| rewrite L; eapply (disjoint_from_sub _ _ _ _ _ D); lia] | exact L].
    split; [tr32' A1 L1 MU WM D1|]. split; [tr32' A2 L2 MU WM D1|]. split; [tr8' A3 L3 MU WM D1|]. split; [tr8' A4 L4 MU WM D1|].
    split; [tr8' A5 L5 MU WM D1|]. split; [split; [exact A6| exact L6]|]. split; [split; [exact A7| exact L7]|]. split; [tr8' A8 L8 MU WM D2|].
    split; [tr8' A9 L9 MU WM D2|]. split; [tr8' A10 L10 MU WM D2|]. split; [tr32' A11 L11 MU WM D2|]. split; [tr32' A12 L12 MU WM D2|].
    split; [tr32' A13 L13 MU WM D2| tr32' A14 L14 MU WM D2].
  Qed.
End DrestCfc.
End ACeilS1.


(* [comment removed for export] *)
Ltac dj_conj AOK SM0 :=
  lazymatch goal with
  | |- (b_ll4 _ + _ <= b_ll16 _ \/ _)%Z => apply (dj_4_16 _ _ AOK SM0); lia
  | |- (b_ll16 _ + _ <= b_ll4 _ \/ _)%Z => apply (dj_16_4 _ _ AOK SM0); lia
  | |- (?a + _ <= b_ll16 _ \/ _)%Z =>
      lazymatch a with
      | (b_s _ + _)%Z => apply (dj_s_16 _ _ AOK SM0); lia
      | b_s _ => apply (dj_s_16 _ _ AOK SM0); lia
      | b_src _ => apply (dj_p_16 _ _ AOK SM0); lia
      | Zpos _ => apply (dj_i_16 _ _ AOK SM0); lia
      | _ => lia
      end
  | |- (?a + _ <= b_ll4 _ \/ _)%Z =>
      lazymatch a with
      | (b_s _ + _)%Z => apply (dj_s_4 _ _ AOK SM0); lia
      | b_s _ => apply (dj_s_4 _ _ AOK SM0); lia
      | b_src _ => apply (dj_p_4 _ _ AOK SM0); lia
      | Zpos _ => apply (dj_i_4 _ _ AOK SM0); lia
      | _ => lia
      end
  | |- (?a + _ <= b_tt _ \/ _)%Z =>
      lazymatch a with
      | (b_s _ + _)%Z => apply (dj_s_tt _ _ AOK SM0); lia
      | b_s _ => apply (dj_s_tt _ _ AOK SM0); lia
      | b_src _ => apply (dj_p_tt _ _ AOK SM0); lia
      | Zpos _ => apply (dj_i_tt _ _ AOK SM0); lia
      | _ => lia
      end
  | |- (?a + _ <= ?lo \/ _)%Z =>
      lazymatch a with
      | b_src _ => first [ lia | eapply (dj_p_s _ _ AOK); lia ]
      | Zpos _ => first [ eapply (dj_i_s _ _ AOK); lia | lia ]
      | b_tt _ => first [ lia | eapply (dj_tt_s _ _ AOK SM0); lia ]
      | b_ll16 _ => first [ lia | eapply (dj_16_s _ _ AOK SM0); lia ]
      | b_ll4 _ => first [ lia | eapply (dj_4_s _ _ AOK SM0); lia ]
      | _ => lia
      end
  | |- _ => lia
  end.
Ltac dj_all AOK SM0 :=
  lazymatch goal with
  | |- _ /\ _ => split; [dj_conj AOK SM0 | dj_all AOK SM0]
  | |- True => exact I
  | |- _ => dj_conj AOK SM0
  end.

(* [comment removed for export] *)
Ltac revive_sm H AOK SM0 MUL WML :=
  unfold hidden in H;
  lazymatch type of MUL with munch ?W ?me ?m' =>
  lazymatch type of H with
  | rw_cells ?segs me ?Ad ?cs =>
      apply (rw_cells_transport segs W me m' Ad cs) in H; [ | exact MUL | exact WML | cbn [disjoint_from]; simpl_sizes; dj_all AOK SM0 ]
  | u32arr ?segs me ?Ad ?ws =>
      apply (u32arr_transport segs W me m' Ad ws) in H; [ | exact MUL | exact WML | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; dj_all AOK SM0 ]
  | u8arr ?segs me ?Ad ?bs =>
      apply (u8arr_transport segs W me m' Ad bs) in H; [ | exact MUL | exact WML | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; dj_all AOK SM0 ]
  | bytes_at ?segs me ?Ad ?bs =>
      apply (bytes_at_transport segs W me m' Ad bs) in H; [ | exact MUL | cbn [disjoint_from]; simpl_sizes; dj_all AOK SM0 ]
  | drest_at ?segs me ?Sd ?r =>
      apply (drest_transport segs W me m' Sd r) in H;
      [ | exact MUL | exact WML | cbn [disjoint_from]; dj_all AOK SM0 | cbn [disjoint_from]; dj_all AOK SM0 | cbn [disjoint_from]; dj_all AOK SM0 ]
  | blk_at ?segs me ?cxx ?k =>
      apply (blk_at_transport segs W me m' cxx k) in H;
      [ | exact MUL | exact WML
        | let E := fresh "E" in
          intros ? ? [(E & -> & ->)|(E & [(-> & ->)|(-> & ->)])];
          first [ exfalso; clear -E SM0; congruence | cbn [disjoint_from]; dj_all AOK SM0 ]; try clear E ]
  end end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac revive_all_sm AOK SM0 MUL WML :=
  repeat lazymatch goal with H : hidden _ |- _ => first [ revive_sm H AOK SM0 MUL WML | fail 100 "cannot revive" H ] end.
(* [comment removed for export] *)
Ltac revive_all_smL AOK SM0 MUL WML LIN DP :=
  clear LIN;
  let L := fresh "LINs" in let L2 := fresh "LINm" in
  pose proof (act_lin_core _ _ AOK) as L;
  first [ pose proof (act_lin_ll _ _ AOK SM0) as L2 | pose proof (act_lin_tt _ _ AOK SM0) as L2 ];
  revive_all_sm AOK SM0 MUL WML;
  clear L L2; pose proof (act_lin _ _ _ AOK DP) as LIN; cbv zeta in LIN.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac oktrap :=
  first [ if_true_z | if_false_z
        | lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
            first [ replace c with true by reflexivity | replace c with false by reflexivity ]; cbv iota end ].
