(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_unwind_chain RT_iface SitePaths.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition paths_from (f : Z) : list (list Z) :=
  match find (fun e => fst e =? f) PATHS with Some e => snd e | None => [] end.

Definition site_ctx (f : Z) (ras : list Z) : Prop := forall p, In p (paths_from f) -> In (p ++ ras) SITE_TRACES.

Definition path_memb (p : list Z) (l : list (list Z)) : bool := existsb (site_eqb p) l.

Lemma path_memb_In : forall p l, path_memb p l = true -> In p l.
Proof. intros p l H. unfold path_memb in H. apply existsb_exists in H as (t & Hin & E). apply site_eqb_eq in E. subst t. exact Hin. Qed.

(* [comment removed for export] *)
Definition site_ctxb (f : Z) (ras : list Z) : bool := forallb (fun p => site_memb (p ++ ras)) (paths_from f).

Lemma site_ctx_root : forall f ras, site_ctxb f ras = true -> site_ctx f ras.
Proof. intros f ras H p Hp. apply site_memb_In. exact (proj1 (forallb_forall _ _) H p Hp). Qed.

(* [comment removed for export] *)
Definition call_edgeb (f r g : Z) : bool := forallb (fun p => path_memb (p ++ [r]) (paths_from f)) (paths_from g).

Lemma site_ctx_call : forall f r g ras, call_edgeb f r g = true -> site_ctx f ras -> site_ctx g (r :: ras).
Proof.
  intros f r g ras H HF p Hp. pose proof (proj1 (forallb_forall _ _) H p Hp) as X. cbv beta in X. apply path_memb_In in X.
  pose proof (HF _ X) as Y. rewrite <- app_assoc in Y. exact Y.
Qed.

(* [comment removed for export] *)
Definition tail_edgeb (f g : Z) : bool := forallb (fun p => path_memb p (paths_from f)) (paths_from g).

Lemma site_ctx_tail : forall f g ras, tail_edgeb f g = true -> site_ctx f ras -> site_ctx g ras.
Proof. intros f g ras H HF p Hp. apply HF. apply path_memb_In. exact (proj1 (forallb_forall _ _) H p Hp). Qed.

(* [comment removed for export] *)
Definition leaf_edgeb (f r : Z) : bool := path_memb [r] (paths_from f).

Lemma site_ctx_leaf : forall f r ras, leaf_edgeb f r = true -> site_ctx f ras -> In (r :: ras) SITE_TRACES.
Proof. intros f r ras H HF. apply path_memb_In in H. exact (HF _ H). Qed.

(* [comment removed for export] *)
Definition leaf_tailb (f : Z) : bool := path_memb [] (paths_from f).

Lemma site_ctx_leaf_tail : forall f ras, leaf_tailb f = true -> site_ctx f ras -> In ras SITE_TRACES.
Proof. intros f ras H HF. apply path_memb_In in H. exact (HF _ H). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma unwind_ch_intro : forall (m : mem) (ra s0 sp : word) ras,
  In (bv_unsigned ra :: ras) SITE_TRACES -> uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> unwind_ch m ra s0 sp.
Proof. intros m ra s0 sp ras H1 H2. exists ras. split; assumption. Qed.

(* [comment removed for export] *)
Lemma uw_chain_nil : forall (m : mem) f fp, fp <= f \/ fp mod 8 <> 0 \/ 2 ^ 63 <= fp -> uw_chain USTACK_TOP m f fp [].
Proof. intros m f fp H. exact H. Qed.

(* [comment removed for export] *)
Lemma uw_chain_push : forall (m : mem) f' fp ra_e s0_e ras,
  f' + 16 <= fp -> fp mod 8 = 0 -> fp <= USTACK_TOP -> 0 <= s0_e < 2 ^ 64 ->
  rw_cells bsegs m (fp + -16) [C8 (Z_to_bv 64 s0_e); C8 (Z_to_bv 64 ra_e)] ->
  uw_chain USTACK_TOP m fp s0_e ras -> uw_chain USTACK_TOP m f' fp (ra_e :: ras).
Proof.
  intros m f' fp ra_e s0_e ras H1 H2 H3 H4 HC HU. cbn [uw_chain]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  exists s0_e. split; [exact H4|]. split; [exact HC | exact HU].
Qed.

(* [comment removed for export] *)
Lemma rw_cells_app_r : forall (m : mem) A pre post, rw_cells bsegs m A (pre ++ post) ->
  rw_cells bsegs m (A + Z.of_nat (cells_size pre)) post.
Proof.
  intros m A pre post ((Hwf & Hb) & Hw). apply cells_wf_app in Hwf as [Wp Wq].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb as [_ Hb2]. rewrite (cells_bytes_length pre Wp) in Hb2.
  split; [split; [exact Wq | exact Hb2]|].
  destruct Hw as (W1 & W2 & W3). rewrite cells_size_app, Nat2Z.inj_add in W2, W3.
  split; [lia|]. split; [lia|]. intros i Hi. replace (A + Z.of_nat (cells_size pre) + i) with (A + (Z.of_nat (cells_size pre) + i)) by lia.
  apply W3. lia.
Qed.

Lemma uw_chain_push_frame : forall (m : mem) f' fp N pre ra_e s0_e ras,
  Z.of_nat (cells_size pre) = N - 16 ->
  f' + 16 <= fp -> fp mod 8 = 0 -> fp <= USTACK_TOP -> 0 <= s0_e < 2 ^ 64 ->
  rw_cells bsegs m (fp + - N) (pre ++ [C8 (Z_to_bv 64 s0_e); C8 (Z_to_bv 64 ra_e)]) ->
  uw_chain USTACK_TOP m fp s0_e ras -> uw_chain USTACK_TOP m f' fp (ra_e :: ras).
Proof.
  intros m f' fp N pre ra_e s0_e ras HN H1 H2 H3 H4 HC HU. apply (uw_chain_push m f' fp ra_e s0_e ras H1 H2 H3 H4); [|exact HU].
  pose proof (rw_cells_app_r m _ _ _ HC) as X. rewrite HN in X. replace (fp + - N + (N - 16)) with (fp + -16) in X by lia. exact X.
Qed.

(* [comment removed for export] *)
Lemma uw_chain_above : forall (m m' : mem) ras f fp,
  uw_chain USTACK_TOP m f fp ras -> (forall a : word, f <= bv_unsigned a < USTACK_TOP -> m' a = m a) -> wmono bsegs m m' ->
  uw_chain USTACK_TOP m' f fp ras.
Proof.
  intros m m' ras. induction ras as [|r ras IH]; intros f fp HU AG WM; cbn [uw_chain] in *; [exact HU|].
  destruct HU as (H1 & H2 & H3 & fp' & Hfp' & HC & HU). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  exists fp'. split; [exact Hfp'|]. split.
  - destruct HC as ((Hwf & Hb) & Hw). split; [split; [exact Hwf|] | exact (wr_at_transport bsegs m m' _ _ Hw WM)].
    destruct Hb as (B1 & B2 & B3). split; [exact B1|]. split; [exact B2|]. intros i Hi. rewrite <- (B3 i Hi). unfold mrd.
    cbn [cells_bytes cbytes length app] in Hi, B2.
    assert (Hlen : (length (le8 (Z_to_bv 64 fp') ++ le8 (Z_to_bv 64 r) ++ []) = 16)%nat) by reflexivity.
    rewrite AG; [reflexivity|]. rewrite wa_unsigned by (unfold USTACK_TOP in *; lia). unfold USTACK_TOP in *. lia.
  - apply (IH fp fp' HU); [|exact WM]. intros a Ha. apply AG. lia.
Qed.

(* [comment removed for export] *)
Lemma uw_chain_munch : forall W (m m' : mem) ras f fp,
  uw_chain USTACK_TOP m f fp ras -> munch W m m' -> Forall (fun iv => snd iv <= f) W -> wmono bsegs m m' ->
  uw_chain USTACK_TOP m' f fp ras.
Proof.
  intros W m m' ras f fp HU MU HW WM. apply (uw_chain_above m m' ras f fp HU); [|exact WM].
  intros a Ha. apply MU. clear - HW Ha. induction W as [|[lo hi] W IH]; cbn [outside]; [exact I|].
  apply Forall_cons_iff in HW as [H1 H2]. cbn [snd] in H1. split; [lia | exact (IH H2)].
Qed.
