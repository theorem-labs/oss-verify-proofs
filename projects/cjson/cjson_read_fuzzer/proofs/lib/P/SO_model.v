(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim Monad Stdio Driver.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition wv_init (buf s : list Z) : list (list Z) :=
  match buf with [] => [s] | _ => [buf; s] end.

Definition wv_total (iov : list (list Z)) : Z := zlength (concat iov).

(* [comment removed for export] *)
Definition wv_advance (iov : list (list Z)) (k : Z) : list (list Z) :=
  match iov with
  | [b0; b1] => if zlength b0 <? k then [skipn (Z.to_nat (k - zlength b0)) b1]
                else [skipn (Z.to_nat k) b0; b1]
  | [b1] => [skipn (Z.to_nat k) b1]
  | _ => iov
  end.

(* [comment removed for export] *)
Definition dec_wv (total : Z) (rsp : resp) : option Z :=
  match rsp with
  | mkEffectU r [] [] [] [] [] =>
      let k := bv_unsigned r in
      if ((total =? 0) && (k =? 0)) || ((1 <=? k) && (k <=? total)) then Some k else None
  | _ => None
  end.

Lemma dec_wv_Some : forall total rsp k, dec_wv total rsp = Some k ->
  rsp = eff0 (Z_to_bv 64 k) /\ ((total = 0 /\ k = 0) \/ (1 <= k <= total)) /\ 0 <= k < 2^64.
Proof.
  intros total [r ws zs us cps cis] k H. unfold dec_wv in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
  destruct cps; [|discriminate]. destruct cis; [|discriminate].
  pose proof (bv_unsigned_in_range 64 r) as R. unfold bv_modulus in R.
  lazymatch type of H with (if ?c then _ else _) = _ => destruct c eqn:C; [|discriminate] end.
  inversion H; subst. split.
  - unfold eff0. f_equal. symmetry. apply (proj2 (bv_eq _ _ _)). rewrite unsigned_lit; [reflexivity| exact R].
  - split; [| lia]. apply orb_true_iff in C. destruct C as [C|C]; apply andb_true_iff in C; destruct C as [C1 C2].
    + left. apply Z.eqb_eq in C1. apply Z.eqb_eq in C2. lia.
    + right. apply Z.leb_le in C1. apply Z.leb_le in C2. lia.
Qed.

Lemma dec_wv_val : forall total k, 0 <= total -> ((total = 0 /\ k = 0) \/ (1 <= k <= total)) -> total < 2^64 ->
  dec_wv total (eff0 (Z_to_bv 64 k)) = Some k.
Proof.
  intros total k HT HK HB. unfold dec_wv, eff0. cbn [eff_ret].
  rewrite unsigned_lit by lia.
  lazymatch goal with |- (if ?c then _ else _) = _ => replace c with true; [reflexivity|] end.
  symmetry. apply orb_true_iff. destruct HK as [[-> ->]|[H1 H2]]; [left; reflexivity| right].
  apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.

Section Stdio.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
Let M := @M St.

Definition wv_body (fd : Z) (iov : list (list Z)) : M (list (list Z) + unit)%type :=
  k <- msys (NWritev fd (map to_bytes iov)) (dec_wv (wv_total iov)) ;;
  if k =? wv_total iov then mret (inr tt) else mret (inl (wv_advance iov k)).

(* [comment removed for export] *)
Definition stdio_writev (fd : Z) (buf s : list Z) : M unit :=
  mloop (S (length buf + length s)) (wv_body fd) (wv_init buf s).

(* [comment removed for export] *)

Definition stdout_stdio_write (s : list Z) : M unit :=
  so <- rd_so get_so ;;
  stdio_writev 1 (so_buf so) s ;;;
  upd_so get_so set_so (fun so => mkStdout true [] (so_lbf_nl so) (so_first so)).

Definition stdout_writefn (s : list Z) : M unit :=
  so <- rd_so get_so ;;
  (if so_first so then
     upd_so get_so set_so (fun so => mkStdout (so_active so) (so_buf so) (so_lbf_nl so) false) ;;;
     r <- msys (NIoctl 1 TIOCGWINSZ) dec_ioctl ;;
     match r with
     | SErr _ => upd_so get_so set_so (fun so => mkStdout (so_active so) (so_buf so) false (so_first so))
     | SVal _ => munr
     end
   else mret tt) ;;;
  stdout_stdio_write s.

Definition stdout_fwritex (s : list Z) : M unit :=
  stdout_towrite get_so set_so ;;;
  so <- rd_so get_so ;;
  if STDOUT_BUFSIZ - zlength (so_buf so) <? zlength s
  then stdout_writefn s
  else if so_lbf_nl so then
    let i := after_last_nl s in
    (if 0 <? i then stdout_writefn (firstn (Z.to_nat i) s) else mret tt) ;;;
    upd_so get_so set_so (fun so => mkStdout (so_active so) (so_buf so ++ skipn (Z.to_nat i) s) (so_lbf_nl so) (so_first so))
  else
    upd_so get_so set_so (fun so => mkStdout (so_active so) (so_buf so ++ s) (so_lbf_nl so) (so_first so)).

Fixpoint out_pieces (ps : list (list Z)) : M unit :=
  match ps with
  | [] => mret tt
  | p :: ps' => stdout_fwritex p ;;; out_pieces ps'
  end.
Definition stdout_vprintf (pieces : list (list Z)) : M unit :=
  stdout_towrite get_so set_so ;;; out_pieces pieces.

Definition stdout_exit_flush : M unit :=
  so <- rd_so get_so ;;
  if (0 <? zlength (so_buf so)) then stdout_writefn [] else mret tt.

Fixpoint stderr_pieces (buf : list Z) (ps : list (list Z)) : M (list Z) :=
  match ps with
  | [] => mret buf
  | p :: ps' =>
      if INTERNAL_BUFSIZ - zlength buf <? zlength p
      then (stdio_writev 2 buf p ;;; stderr_pieces [] ps')
      else stderr_pieces (buf ++ p) ps'
  end.
Definition stderr_fprintf (pieces : list (list Z)) : M unit :=
  buf <- stderr_pieces [] pieces ;;
  stdio_writev 2 buf [].

Definition stderr_fwrite (s : list Z) : M unit :=
  if 0 <? zlength s then stdio_writev 2 [] s else mret tt.

(* [comment removed for export] *)
Definition s_diag (d : diag_msg) : M unit :=
  match d with
  | DUsage argv0 => stderr_fprintf (pieces_usage argv0)
  | DCannotOpen p => stderr_fprintf (pieces_cannot_open p)
  | DReadError p => stderr_fprintf (pieces_read_error p)
  | DOom => stderr_fwrite (concat pieces_oom)
  | DTooBig => stderr_fprintf pieces_too_big
  | DShortHdr => stderr_fwrite (concat pieces_short_hdr)
  | DCfgOverrun => stderr_fwrite (concat pieces_cfg_overrun)
  end.
Definition s_emit (s : list Z) : M unit := stdout_vprintf (pieces_emit s).
Definition io_S : IOStyle St := mkIO St s_diag s_emit stdout_exit_flush.

End Stdio.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wv_total_init : forall buf s, wv_total (wv_init buf s) = zlength buf + zlength s.
Proof. intros buf s. unfold wv_total, wv_init, zlength. destruct buf; cbn [concat]; rewrite ?app_nil_r, ?length_app; cbn [length]; lia. Qed.

Lemma wv_total_nonneg : forall iov, 0 <= wv_total iov.
Proof. intros. unfold wv_total, zlength. lia. Qed.

Lemma wv_advance_total : forall iov k,
  (length iov = 1%nat \/ length iov = 2%nat) -> 1 <= k <= wv_total iov ->
  wv_total (wv_advance iov k) = wv_total iov - k.
Proof.
  intros iov k Hl Hk. unfold wv_total, zlength in *.
  destruct iov as [|b0 [|b1 [|x l]]]; cbn [length] in Hl; try lia; cbn [wv_advance concat] in *;
    rewrite ?app_nil_r in *.
  - rewrite length_skipn. lia.
  - unfold zlength. rewrite length_app in Hk |- *. destruct (Z.ltb_spec (Z.of_nat (length b0)) k).
    + cbn [concat]. rewrite app_nil_r, length_skipn. lia.
    + cbn [concat]. rewrite app_nil_r, length_app, length_skipn. lia.
Qed.

Lemma wv_advance_shape : forall iov k, (length iov = 1%nat \/ length iov = 2%nat) ->
  (length (wv_advance iov k) = 1%nat \/ length (wv_advance iov k) = 2%nat).
Proof.
  intros iov k Hl. destruct iov as [|b0 [|b1 [|x l]]]; cbn [length] in Hl; try lia; cbn [wv_advance].
  - left; reflexivity.
  - destruct (zlength b0 <? k); [left| right]; reflexivity.
Qed.

Lemma wv_init_shape : forall buf s, length (wv_init buf s) = 1%nat \/ length (wv_init buf s) = 2%nat.
Proof. intros. unfold wv_init. destruct buf; [left| right]; reflexivity. Qed.

(* [comment removed for export] *)
Lemma wv_advance_concat : forall iov k,
  (length iov = 1%nat \/ length iov = 2%nat) -> 1 <= k <= wv_total iov ->
  concat (wv_advance iov k) = skipn (Z.to_nat k) (concat iov).
Proof.
  intros iov k Hl Hk. unfold wv_total, zlength in Hk.
  destruct iov as [|b0 [|b1 [|x l]]]; cbn [length] in Hl; try lia; cbn [wv_advance concat] in *; rewrite ?app_nil_r in *.
  - reflexivity.
  - unfold zlength. rewrite length_app in Hk. destruct (Z.ltb_spec (Z.of_nat (length b0)) k).
    + cbn [concat]. rewrite app_nil_r. rewrite skipn_app. rewrite (proj1 (skipn_all_iff (Z.to_nat k) b0)) by lia.
      cbn [app]. f_equal. lia.
    + cbn [concat]. rewrite app_nil_r. rewrite skipn_app. replace (Z.to_nat k - length b0)%nat with 0%nat by lia. reflexivity.
Qed.
