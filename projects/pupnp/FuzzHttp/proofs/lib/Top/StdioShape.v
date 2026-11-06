(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize Bridge.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation tsh := (tshape node nstep nexit).
Notation twf := (twfP node nstep nsafe).
Local Notation bind := (ITree.bind node).

Lemma t_eq_alt : forall (I : Type) (f g : I -> TSet), (forall i, t_eq (f i) (g i)) -> t_eq (t_alt f) (t_alt g).
Proof. intros I f g H tr. unfold t_alt. split; intros [i Hi]; exists i; apply H; exact Hi. Qed.

Lemma t_alt_const : forall (I : Type) (f : I -> TSet) (T : TSet), inhabited I -> (forall i, t_eq (f i) T) -> t_eq (t_alt f) T.
Proof.
  intros I f T [i0] H tr. unfold t_alt. split.
  - intros [i Hi]. apply (H i). exact Hi.
  - intros HT. exists i0. apply (H i0). exact HT.
Qed.

Lemma t_emit_app : forall a b T, t_eq (t_emit a (t_emit b T)) (t_emit (a ++ b) T).
Proof.
  intros a b T tr. unfold t_emit. split.
  - intros [Hp | (tr' & -> & [Hp | (tr'' & -> & HT)])].
    + left. apply is_prefix_app_r. exact Hp.
    + left. apply is_prefix_app_mono. exact Hp.
    + right. exists tr''. rewrite app_assoc. auto.
  - intros [Hp | (tr' & -> & HT)].
    + destruct (is_prefix_app_split _ _ _ Hp) as [Hp' | (tr' & -> & Hp')]; [left; exact Hp'|].
      right. exists tr'. auto.
    + right. exists (b ++ tr'). rewrite app_assoc. split; [reflexivity|]. right. exists tr'. auto.
Qed.

Lemma tshape_Keq : forall {R} (t : itree node R) mo (K K' : R -> Model -> TSet),
  (forall r mo', t_eq (K r mo') (K' r mo')) -> t_eq (tsh t mo K) (tsh t mo K').
Proof.
  induction t as [r | n k IH]; intros mo K K' H; cbn [tshape]; [apply H|].
  apply t_eq_alt. intros [[[[rsp mo'] evs] Hst] | [[code mo'] Hex]]; cbn; apply t_eq_emit; [apply IH; exact H | apply t_eq_refl].
Qed.

Lemma tshape_bind : forall {A B} (t : itree node A) (f : A -> itree node B) mo K,
  t_eq (tsh (bind t f) mo K) (tsh t mo (fun a mo' => tsh (f a) mo' K)).
Proof.
  induction t as [r | n k IH]; intros f mo K; cbn [tshape bind]; [apply t_eq_refl|].
  apply t_eq_alt. intros [[[[rsp mo'] evs] Hst] | [[code mo'] Hex]]; cbn; apply t_eq_emit; [apply IH | apply t_eq_refl].
Qed.

Lemma twfP_bind_inv : forall {A B} (t : itree node A) (f : A -> itree node B) mo P,
  twf t mo (fun a mo' => twf (f a) mo' P) <-> twf (bind t f) mo P.
Proof.
  induction t as [r | n k IH]; intros f mo P; cbn [twfP bind]; [tauto|].
  split; intros [Hs Hk]; split; try exact Hs; intros rsp mo' evs Hn; apply IH; eapply Hk; exact Hn.
Qed.

Section MonadShapes.
  Context {St : Type}.

  Definition kbind {A B} (f : A -> M St B) (K : exc (B * St) -> Model -> TSet) : exc (A * St) -> Model -> TSet :=
    fun r mo' => match r with Ok p => tsh (f (fst p) (snd p)) mo' K | Unr => K Unr mo' end.
  Definition pbind {A B} (f : A -> M St B) (P : exc (B * St) -> Model -> Prop) : exc (A * St) -> Model -> Prop :=
    fun r mo' => match r with Ok p => twf (f (fst p) (snd p)) mo' P | Unr => P Unr mo' end.

  #[using="Type"] Lemma tshape_mbind : forall {A B} (m : M St A) (f : A -> M St B) st mo K,
    t_eq (tsh (mbind m f st) mo K) (tsh (m st) mo (kbind f K)).
  Proof.
    intros A B m f st mo K. unfold mbind, ebind. eapply t_eq_trans; [apply tshape_bind|].
    apply tshape_Keq. intros [|[a s']] mo'; cbn; apply t_eq_refl.
  Qed.

  #[using="Type"] Lemma twfP_mbind : forall {A B} (m : M St A) (f : A -> M St B) st mo P,
    twf (m st) mo (pbind f P) -> twf (mbind m f st) mo P.
  Proof.
    intros A B m f st mo P H. unfold mbind, ebind. apply twfP_bind_inv.
    eapply twfP_mono; [exact H|]. intros [|[a s']] mo'; cbn; intros H'; exact H'.
  Qed.

  #[using="Type"] Lemma tshape_mret : forall {A} (a : A) (st : St) mo K, tsh (mret a st) mo K = K (Ok (a, st)) mo.
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma twfP_mret : forall {A} (a : A) (st : St) mo (P : _ -> _ -> Prop), P (Ok (a, st)) mo -> twf (mret a st) mo P.
  Proof. intros. exact H. Qed.
End MonadShapes.

Lemma advance_total : forall bufs k, (length bufs <= 2)%nat -> 0 <= k <= zlength (concat bufs) ->
  concat (advance bufs k) = skipn (Z.to_nat k) (concat bufs).
Proof.
  intros bufs k Hl Hk. unfold zlength in Hk.
  destruct bufs as [|b0 [|b1 [|b2 rest]]]; cbn [length] in Hl; try lia.
  - cbn. destruct (Z.to_nat k); reflexivity.
  - cbn [advance concat]. cbn [concat] in Hk. rewrite app_nil_r in Hk |- *. unfold zlength.
    destruct (Z.ltb_spec0 (Z.of_nat (length b0)) k); [exfalso; lia|]. cbn. rewrite app_nil_r. reflexivity.
  - cbn [advance concat]. cbn [concat] in Hk. rewrite !app_nil_r in Hk |- *. rewrite length_app in Hk. unfold zlength.
    destruct (Z.ltb_spec0 (Z.of_nat (length b0)) k).
    + cbn [concat]. rewrite app_nil_r. rewrite skipn_app.
      rewrite (skipn_all2 b0) by lia. cbn [app]. f_equal. lia.
    + cbn [concat]. rewrite app_nil_r. rewrite skipn_app.
      replace (Z.to_nat k - length b0)%nat with 0%nat by lia. reflexivity.
Qed.

Lemma advance_length : forall bufs k, (length (advance bufs k) <= length bufs)%nat.
Proof.
  intros [|b0 [|b1 rest]] k; cbn [advance length]; [lia| |]; destruct (zlength b0 <? k); cbn [length]; lia.
Qed.

Lemma concat_map_to_bytes : forall bufs, concat (map to_bytes bufs) = to_bytes (concat bufs).
Proof. intros. unfold to_bytes. rewrite concat_map. reflexivity. Qed.
Lemma to_bytes_length' : forall l, length (to_bytes l) = length l.
Proof. intros. unfold to_bytes. apply length_map. Qed.

Section Wloop.
  Context {St : Type}.

  #[using="Type"] Local Lemma wloop_unfold : forall fuel fd bufs (st : St),
    stdio_wloop (S fuel) fd bufs st
    = Vis (NWritev fd (map to_bytes bufs))
          (fun rsp => bind (match (match dec_writev (zlength (concat bufs)) rsp with
                                   | Some a => Some (a, st) | None => None end) with
                            | Some a => Ret (Ok a) | None => Ret Unr end)
                           (fun r => match r with
                                     | Unr => Ret Unr
                                     | Ok p => (if fst p =? zlength (concat bufs) then mret tt
                                               else stdio_wloop fuel fd (advance bufs (fst p))) (snd p)
                                     end)).
  Proof. reflexivity. Qed.

  #[using="Type"] Theorem twfP_stdio_wloop : forall fuel fd bufs (st : St) mo (P : exc (unit * St) -> Model -> Prop),
    minv mo -> (length bufs <= 2)%nat -> (length (concat bufs) < fuel)%nat -> Z.of_nat (length (concat bufs)) < 2^64 ->
    P (Ok (tt, st)) mo ->
    twf (stdio_wloop fuel fd bufs st) mo P.
  Proof.
    induction fuel as [|fuel IH]; intros fd bufs st mo P MI L2 FUEL BND HP; [lia|].
    rewrite wloop_unfold. cbn [twfP]. split; [exact I|].
    intros rsp mo' evs Hn.
    destruct (nstep_dec_writev fd (map to_bytes bufs) mo rsp mo' evs ltac:(rewrite concat_map_to_bytes, to_bytes_length'; lia) Hn)
      as (-> & k & D & Hk & Hk0 & ->).
    rewrite concat_map_to_bytes, to_bytes_length' in D, Hk, Hk0. unfold zlength. rewrite D. cbn [bind fst snd].
    destruct (Z.eqb_spec k (Z.of_nat (length (concat bufs)))) as [E|NE].
    - exact HP.
    - apply IH; try assumption.
      + pose proof (advance_length bufs k). lia.
      + rewrite advance_total by (unfold zlength; lia). rewrite length_skipn. lia.
      + rewrite advance_total by (unfold zlength; lia). rewrite length_skipn. lia.
  Qed.

  #[using="Type"] Theorem tshape_stdio_wloop : forall fuel fd bufs (st : St) mo (K : exc (unit * St) -> Model -> TSet),
    minv mo -> (length bufs <= 2)%nat -> (length (concat bufs) < fuel)%nat -> Z.of_nat (length (concat bufs)) < 2^64 ->
    K (Ok (tt, st)) mo [] ->
    t_eq (tsh (stdio_wloop fuel fd bufs st) mo K)
         (t_emit (map (WriteEv (Z_to_bv 64 fd)) (to_bytes (concat bufs))) (K (Ok (tt, st)) mo)).
  Proof.
    induction fuel as [|fuel IH]; intros fd bufs st mo K MI L2 FUEL BND HK; [lia|].
    rewrite wloop_unfold. cbn [tshape].
    apply t_alt_const.
    {
      destruct (concat bufs) as [|b bs] eqn:E.
      - constructor. left. exists (eff0 (Z_to_bv 64 0), mo, @nil event).
        cbn [fst snd]. cbn [nstep]. split; [reflexivity|]. left. rewrite concat_map_to_bytes, E. unfold eff0. rewrite strip_mk. repeat split; reflexivity.
      - constructor. left. exists (eff0 (Z_to_bv 64 1), mo, map (WriteEv (Z_to_bv 64 fd)) (firstn 1 (to_bytes (b :: bs)))).
        cbn [fst snd]. cbn [nstep]. split; [reflexivity|]. right. exists 1%nat. rewrite concat_map_to_bytes, E, to_bytes_length'. cbn [length].
        unfold eff0. rewrite strip_mk. split; [lia|]. split; reflexivity. }
    intros [[[[rsp mo'] evs] Hst] | [[code mo'] Hex]]; cbn [fst snd ni_evs].
    2:{ exfalso. cbn in Hex. exact Hex. }
    destruct (nstep_dec_writev fd (map to_bytes bufs) mo rsp mo' evs ltac:(rewrite concat_map_to_bytes, to_bytes_length'; lia) Hst)
      as (-> & k & D & Hk & Hk0 & ->).
    rewrite concat_map_to_bytes, to_bytes_length' in D, Hk, Hk0. rewrite concat_map_to_bytes. unfold zlength. rewrite D. cbn [bind fst snd].
    destruct (Z.eqb_spec k (Z.of_nat (length (concat bufs)))) as [E|NE].
    - cbn [tshape]. unfold mret. cbn [tshape].
      rewrite firstn_all2 by (rewrite to_bytes_length'; lia).
      rewrite <- (app_nil_r (map _ (to_bytes (concat bufs)))) at 2.
      eapply t_eq_trans; [| apply t_emit_app]. apply t_eq_emit. apply t_eq_sym. apply t_emit_nil_eq. exact HK.
    - eapply t_eq_trans.
      + apply t_eq_emit. apply IH; try assumption.
        * pose proof (advance_length bufs k). lia.
        * rewrite advance_total by (unfold zlength; lia). rewrite length_skipn. lia.
        * rewrite advance_total by (unfold zlength; lia). rewrite length_skipn. lia.
      + eapply t_eq_trans; [apply t_emit_app|].
        rewrite advance_total by (unfold zlength; lia). unfold to_bytes. rewrite <- skipn_map, <- map_app, firstn_skipn.
        apply t_eq_refl.
  Qed.

  #[using="Type"] Corollary twfP_stdio_writev : forall fd buf s (st : St) mo P,
    minv mo -> Z.of_nat (length buf + length s) < 2^64 -> P (Ok (tt, st)) mo ->
    twf (stdio_writev fd buf s st) mo P.
  Proof.
    intros fd buf s st mo P MI BND HP. unfold stdio_writev.
    destruct buf as [|b buf']; apply twfP_stdio_wloop; cbn [length concat]; rewrite ?app_nil_r, ?length_app; cbn [length]; try assumption; try lia.
  Qed.

  #[using="Type"] Corollary tshape_stdio_writev : forall fd buf s (st : St) mo K,
    minv mo -> Z.of_nat (length buf + length s) < 2^64 -> K (Ok (tt, st)) mo [] ->
    t_eq (tsh (stdio_writev fd buf s st) mo K)
         (t_emit (map (WriteEv (Z_to_bv 64 fd)) (to_bytes (buf ++ s))) (K (Ok (tt, st)) mo)).
  Proof.
    intros fd buf s st mo K MI BND HK. unfold stdio_writev.
    destruct buf as [|b buf'].
    - eapply t_eq_trans; [apply tshape_stdio_wloop; cbn [length concat]; rewrite ?app_nil_r; try assumption; cbn; lia|].
      cbn [concat app]. rewrite app_nil_r. apply t_eq_refl.
    - eapply t_eq_trans; [apply tshape_stdio_wloop; cbn [length concat]; rewrite ?app_nil_r, ?length_app; try assumption; cbn [length]; lia|].
      cbn [concat]. rewrite app_nil_r. apply t_eq_refl.
  Qed.
End Wloop.

Definition wr (fd : Z) (bytes : list Z) : list event := map (WriteEv (Z_to_bv 64 fd)) (to_bytes bytes).

Lemma wr_app : forall fd a b, wr fd (a ++ b) = wr fd a ++ wr fd b.
Proof. intros. unfold wr, to_bytes. rewrite !map_app. reflexivity. Qed.
Lemma wr_nil : forall fd, wr fd [] = [].
Proof. reflexivity. Qed.

Section StdoutShapes.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis get_set : forall s so, get_so (set_so so s) = so.
  Hypothesis set_set : forall s so so', set_so so' (set_so so s) = set_so so' s.
  Hypothesis set_get : forall s, set_so (get_so s) s = s.

  #[using="Type"] Lemma rd_so_bind : forall {B} (k : stdout_st -> M St B) st, mbind (rd_so get_so) k st = k (get_so st) st.
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma upd_so_bind : forall {B} f (k : unit -> M St B) st, mbind (upd_so get_so set_so f) k st = k tt (set_so (f (get_so st)) st).
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma upd_so_run : forall f st, upd_so get_so set_so f st = Ret (Ok (tt, set_so (f (get_so st)) st)).
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma mret_bind : forall {A B} (a : A) (k : A -> M St B) st, mbind (mret a) k st = k a st.
  Proof. reflexivity. Qed.

  Definition so_flushed (so : stdout_st) : stdout_st := mkStdout true [] (so_lbf_nl so) (so_first so).

  #[using="Type"] Lemma twfP_stdout_stdio_write : forall s st mo P,
    minv mo -> Z.of_nat (length (so_buf (get_so st)) + length s) < 2^64 ->
    P (Ok (tt, set_so (so_flushed (get_so st)) st)) mo ->
    twf (stdout_stdio_write get_so set_so s st) mo P.
  Proof.
    intros s st mo P MI BND HP. unfold stdout_stdio_write. rewrite rd_so_bind.
    apply twfP_mbind. apply twfP_stdio_writev; [exact MI | exact BND |]. cbn [pbind fst snd]. rewrite upd_so_run. exact HP.
  Qed.

  #[using="Type"] Lemma tshape_stdout_stdio_write : forall s st mo K,
    minv mo -> Z.of_nat (length (so_buf (get_so st)) + length s) < 2^64 ->
    K (Ok (tt, set_so (so_flushed (get_so st)) st)) mo [] ->
    t_eq (tsh (stdout_stdio_write get_so set_so s st) mo K)
         (t_emit (wr 1 (so_buf (get_so st) ++ s)) (K (Ok (tt, set_so (so_flushed (get_so st)) st)) mo)).
  Proof.
    intros s st mo K MI BND HK. unfold stdout_stdio_write. rewrite rd_so_bind.
    eapply t_eq_trans; [apply tshape_mbind|].
    eapply t_eq_trans; [apply tshape_stdio_writev; [exact MI | exact BND |]|].
    - cbn [kbind fst snd]. rewrite upd_so_run. exact HK.
    - cbn [kbind fst snd]. rewrite upd_so_run. cbn [tshape]. apply t_eq_refl.
  Qed.

  Definition so_after_write (so : stdout_st) : stdout_st :=
    mkStdout true [] (if so_first so then false else so_lbf_nl so) false.

  #[using="get_set set_set"] Lemma twfP_stdout_writefn : forall s st mo P,
    minv mo -> Z.of_nat (length (so_buf (get_so st)) + length s) < 2^64 ->
    P (Ok (tt, set_so (so_after_write (get_so st)) st)) mo ->
    twf (stdout_writefn get_so set_so s st) mo P.
  Proof.
    intros s st mo P MI BND HP. unfold stdout_writefn. rewrite rd_so_bind.
    apply twfP_mbind. unfold so_after_write in HP.
    destruct (so_first (get_so st)) eqn:FIRST.
    - rewrite upd_so_bind. apply twfP_mbind. cbn [twfP msys enode]. split; [exact I|].
      intros rsp mo' evs Hn. destruct (nstep_dec_ioctl _ _ _ _ _ _ Hn) as (D & -> & ->). rewrite D. cbn [bind twfP pbind fst snd].
      rewrite upd_so_run. cbn [twfP pbind fst snd]. rewrite !get_set, !set_set. cbn [so_active so_buf so_first].
      apply twfP_stdout_stdio_write; [exact MI | rewrite get_set; cbn [so_buf]; exact BND |].
      rewrite get_set, set_set. unfold so_flushed. cbn [so_lbf_nl so_first]. exact HP.
    - cbn [pbind fst snd twfP mret].
      apply twfP_stdout_stdio_write; [exact MI | exact BND |].
      unfold so_flushed. rewrite FIRST. exact HP.
  Qed.

  #[using="get_set set_set"] Lemma tshape_stdout_writefn : forall s st mo K,
    minv mo -> Z.of_nat (length (so_buf (get_so st)) + length s) < 2^64 ->
    K (Ok (tt, set_so (so_after_write (get_so st)) st)) mo [] ->
    t_eq (tsh (stdout_writefn get_so set_so s st) mo K)
         (t_emit (wr 1 (so_buf (get_so st) ++ s)) (K (Ok (tt, set_so (so_after_write (get_so st)) st)) mo)).
  Proof.
    intros s st mo K MI BND HK. unfold stdout_writefn. rewrite rd_so_bind.
    eapply t_eq_trans; [apply tshape_mbind|]. unfold so_after_write in HK |- *.
    destruct (so_first (get_so st)) eqn:FIRST.
    - rewrite upd_so_bind. eapply t_eq_trans; [apply tshape_mbind|].
      cbn [tshape msys enode].
      apply t_alt_const.
      { constructor. left. exists (efferr ENOTTY, mo, @nil event). cbn [fst snd nstep]. unfold efferr, eff0. rewrite strip_mk. repeat split; reflexivity. }
      intros [[[[rsp mo'] evs] Hst] | [[code mo'] Hex]]; cbn [fst snd ni_evs]. 2:{ exfalso. exact Hex. }
      cbn [fst snd] in Hst. destruct (nstep_dec_ioctl _ _ _ _ _ _ Hst) as (D & -> & ->). rewrite D. cbn [bind tshape kbind fst snd].
      rewrite upd_so_run. cbn [tshape kbind fst snd]. rewrite !get_set, !set_set. cbn [so_active so_buf so_first].
      set (st1 := set_so _ st).
      assert (BND1 : Z.of_nat (length (so_buf (get_so st1)) + length s) < 2^64) by (subst st1; rewrite get_set; cbn [so_buf]; exact BND).
      assert (HK1 : K (Ok (tt, set_so (so_flushed (get_so st1)) st1)) mo [])
        by (subst st1; rewrite get_set, set_set; unfold so_flushed; cbn [so_lbf_nl so_first]; exact HK).
      pose proof (tshape_stdout_stdio_write s st1 mo K MI BND1 HK1) as T1.
      eapply t_eq_trans; [apply t_emit_nil_eq; apply (proj2 (T1 [])); apply t_emit_has_nil|].
      eapply t_eq_trans; [exact T1|]. subst st1. rewrite !get_set, !set_set. unfold so_flushed. cbn [so_buf so_lbf_nl so_first]. apply t_eq_refl.
    - cbn [kbind fst snd tshape mret].
      eapply t_eq_trans; [apply tshape_stdout_stdio_write; [exact MI | exact BND |]|]; unfold so_flushed; rewrite FIRST; [exact HK | apply t_eq_refl].
  Qed.

  Definition so_towrite (so : stdout_st) : stdout_st :=
    if so_active so then so else mkStdout true [] (so_lbf_nl so) (so_first so).

  Definition fwx_run (so : stdout_st) (s : list Z) : list Z * stdout_st :=
    let so1 := so_towrite so in
    if STDOUT_BUFSIZ - zlength (so_buf so1) <? zlength s
    then (so_buf so1 ++ s, so_after_write so1)
    else if so_lbf_nl so1 then
      let i := after_last_nl s in
      if 0 <? i
      then (so_buf so1 ++ firstn (Z.to_nat i) s,
            let so2 := so_after_write so1 in
            mkStdout (so_active so2) (so_buf so2 ++ skipn (Z.to_nat i) s) (so_lbf_nl so2) (so_first so2))
      else ([], mkStdout (so_active so1) (so_buf so1 ++ skipn (Z.to_nat i) s) (so_lbf_nl so1) (so_first so1))
    else ([], mkStdout (so_active so1) (so_buf so1 ++ s) (so_lbf_nl so1) (so_first so1)).

  #[using="Type"] Lemma so_towrite_buf : forall so, (length (so_buf (so_towrite so)) <= length (so_buf so))%nat.
  Proof. intros so. unfold so_towrite. destruct (so_active so); cbn; lia. Qed.

  #[using="Type"] Lemma towrite_bind : forall {B} (k : unit -> M St B) st,
    mbind (stdout_towrite get_so set_so) k st = k tt (set_so (so_towrite (get_so st)) st).
  Proof. intros. unfold stdout_towrite, so_towrite. rewrite upd_so_bind. destruct (so_active (get_so st)); reflexivity. Qed.

  #[using="get_set set_set"] Lemma twfP_stdout_fwritex : forall s st mo P,
    minv mo -> Z.of_nat (length (so_buf (get_so st)) + length s) < 2^64 ->
    P (Ok (tt, set_so (snd (fwx_run (get_so st) s)) st)) mo ->
    twf (stdout_fwritex get_so set_so s st) mo P.
  Proof.
    intros s st mo P MI BND HP. unfold stdout_fwritex. rewrite towrite_bind, rd_so_bind. rewrite get_set.
    unfold fwx_run in HP. pose proof (so_towrite_buf (get_so st)) as LB.
    set (so1 := so_towrite (get_so st)) in *.
    destruct (STDOUT_BUFSIZ - zlength (so_buf so1) <? zlength s).
    - apply twfP_stdout_writefn; rewrite ?get_set, ?set_set; [exact MI | lia | exact HP].
    - destruct (so_lbf_nl so1) eqn:LBF.
      + destruct (0 <? after_last_nl s).
        * apply twfP_mbind. apply twfP_stdout_writefn; rewrite ?get_set, ?set_set; [exact MI | rewrite length_firstn; lia |].
          cbn [pbind fst snd]. rewrite upd_so_run. cbn [twfP]. rewrite get_set, set_set. exact HP.
        * rewrite mret_bind, upd_so_run. cbn [twfP]. rewrite get_set, set_set, LBF. exact HP.
      + rewrite upd_so_run. cbn [twfP]. rewrite get_set, set_set, LBF. exact HP.
  Qed.

  #[using="get_set set_set"] Lemma tshape_stdout_fwritex : forall s st mo K,
    minv mo -> Z.of_nat (length (so_buf (get_so st)) + length s) < 2^64 ->
    K (Ok (tt, set_so (snd (fwx_run (get_so st) s)) st)) mo [] ->
    t_eq (tsh (stdout_fwritex get_so set_so s st) mo K)
         (t_emit (wr 1 (fst (fwx_run (get_so st) s))) (K (Ok (tt, set_so (snd (fwx_run (get_so st) s)) st)) mo)).
  Proof.
    intros s st mo K MI BND HK. unfold stdout_fwritex. rewrite towrite_bind, rd_so_bind. rewrite get_set.
    unfold fwx_run in HK |- *. pose proof (so_towrite_buf (get_so st)) as LB.
    set (so1 := so_towrite (get_so st)) in *.
    destruct (STDOUT_BUFSIZ - zlength (so_buf so1) <? zlength s).
    - cbn [fst snd] in HK |- *. eapply t_eq_trans; [apply tshape_stdout_writefn; rewrite ?get_set, ?set_set; [exact MI | lia | exact HK]|].
      rewrite get_set, set_set. apply t_eq_refl.
    - destruct (so_lbf_nl so1) eqn:LBF.
      + destruct (0 <? after_last_nl s); cbn [fst snd] in HK |- *.
        * eapply t_eq_trans; [apply tshape_mbind|].
          eapply t_eq_trans; [apply tshape_stdout_writefn; rewrite ?get_set, ?set_set; [exact MI | rewrite length_firstn; lia |]|].
          -- cbn [kbind fst snd]. rewrite upd_so_run. cbn [tshape]. rewrite get_set, set_set. exact HK.
          -- cbn [kbind fst snd]. rewrite upd_so_run. cbn [tshape]. rewrite !get_set, !set_set. apply t_eq_refl.
        * rewrite mret_bind, upd_so_run. cbn [tshape]. rewrite get_set, set_set, LBF. apply t_eq_sym. apply t_emit_nil_eq. exact HK.
      + cbn [fst snd] in HK |- *. rewrite upd_so_run. cbn [tshape]. rewrite get_set, set_set, LBF. apply t_eq_sym. apply t_emit_nil_eq. exact HK.
  Qed.

  Fixpoint vp_run (so : stdout_st) (ps : list (list Z)) : list Z * stdout_st :=
    match ps with
    | [] => ([], so)
    | p :: ps' => let r1 := fwx_run so p in let r2 := vp_run (snd r1) ps' in (fst r1 ++ fst r2, snd r2)
    end.

  #[using="Type"] Lemma fwx_run_buf : forall so s, (length (so_buf (snd (fwx_run so s))) <= length (so_buf so) + length s)%nat.
  Proof.
    intros so s. unfold fwx_run. pose proof (so_towrite_buf so) as LB. set (so1 := so_towrite so) in *. clearbody so1.
    destruct (STDOUT_BUFSIZ - zlength (so_buf so1) <? zlength s); [cbn; lia|].
    destruct (so_lbf_nl so1); [destruct (0 <? after_last_nl s)|]; cbn [snd so_buf so_after_write]; rewrite ?length_app, ?length_skipn; cbn [length]; lia.
  Qed.
  #[using="Type"] Lemma vp_run_buf : forall ps so, (length (so_buf (snd (vp_run so ps))) <= length (so_buf so) + length (concat ps))%nat.
  Proof.
    induction ps as [|p ps IH]; intros so; cbn [vp_run snd concat]; [lia|].
    pose proof (fwx_run_buf so p). specialize (IH (snd (fwx_run so p))). rewrite length_app. cbn [snd] in *. lia.
  Qed.

  #[using="get_set set_set set_get"] Lemma twfP_out_pieces : forall ps st mo P,
    minv mo -> Z.of_nat (length (so_buf (get_so st)) + length (concat ps)) < 2^64 ->
    P (Ok (tt, set_so (snd (vp_run (get_so st) ps)) st)) mo ->
    twf (out_pieces get_so set_so ps st) mo P.
  Proof.
    induction ps as [|p ps IH]; intros st mo P MI BND HP; cbn [out_pieces vp_run fst snd] in HP |- *.
    - cbn [twfP mret]. rewrite set_get in HP. exact HP.
    - cbn [concat] in BND. rewrite length_app in BND.
      pose proof (fwx_run_buf (get_so st) p) as B1.
      set (st1 := set_so (snd (fwx_run (get_so st) p)) st).
      assert (B2 : Z.of_nat (length (so_buf (get_so st1)) + length (concat ps)) < 2^64) by (subst st1; rewrite get_set; lia).
      assert (HP2 : P (Ok (tt, set_so (snd (vp_run (get_so st1) ps)) st1)) mo) by (subst st1; rewrite get_set, set_set; exact HP).
      apply twfP_mbind. apply twfP_stdout_fwritex; [exact MI | lia |]. cbn [pbind fst snd]. fold st1.
      apply IH; [exact MI | exact B2 | exact HP2].
  Qed.

  #[using="get_set set_set set_get"] Lemma tshape_out_pieces : forall ps st mo K,
    minv mo -> Z.of_nat (length (so_buf (get_so st)) + length (concat ps)) < 2^64 ->
    K (Ok (tt, set_so (snd (vp_run (get_so st) ps)) st)) mo [] ->
    t_eq (tsh (out_pieces get_so set_so ps st) mo K)
         (t_emit (wr 1 (fst (vp_run (get_so st) ps))) (K (Ok (tt, set_so (snd (vp_run (get_so st) ps)) st)) mo)).
  Proof.
    induction ps as [|p ps IH]; intros st mo K MI BND HK; cbn [out_pieces vp_run fst snd] in HK |- *.
    - cbn [tshape mret]. rewrite set_get in HK |- *. apply t_eq_sym. apply t_emit_nil_eq. exact HK.
    - cbn [concat] in BND. rewrite length_app in BND. pose proof (fwx_run_buf (get_so st) p) as B1.
      eapply t_eq_trans; [apply tshape_mbind|].
      set (st1 := set_so (snd (fwx_run (get_so st) p)) st).
      assert (B2 : Z.of_nat (length (so_buf (get_so st1)) + length (concat ps)) < 2^64) by (subst st1; rewrite get_set; lia).
      assert (HK2 : K (Ok (tt, set_so (snd (vp_run (get_so st1) ps)) st1)) mo []) by (subst st1; rewrite get_set, set_set; exact HK).
      eapply t_eq_trans; [apply tshape_stdout_fwritex; [exact MI | lia |]|].
      + cbn [kbind fst snd]. fold st1. apply (proj2 (IH st1 mo K MI B2 HK2 [])). apply t_emit_has_nil.
      + cbn [kbind fst snd]. fold st1. rewrite wr_app. eapply t_eq_trans; [| apply t_emit_app]. apply t_eq_emit.
        eapply t_eq_trans; [apply (IH st1 mo K MI B2 HK2)|].
        subst st1. rewrite get_set, set_set. apply t_eq_refl.
  Qed.

  Definition vprintf_run (so : stdout_st) (ps : list (list Z)) : list Z * stdout_st := vp_run (so_towrite so) ps.

  #[using="get_set set_set set_get"] Theorem twfP_stdout_vprintf : forall ps st mo P,
    minv mo -> Z.of_nat (length (so_buf (get_so st)) + length (concat ps)) < 2^64 ->
    P (Ok (tt, set_so (snd (vprintf_run (get_so st) ps)) st)) mo ->
    twf (stdout_vprintf get_so set_so ps st) mo P.
  Proof.
    intros ps st mo P MI BND HP. unfold stdout_vprintf. rewrite towrite_bind. unfold vprintf_run in HP.
    pose proof (so_towrite_buf (get_so st)).
    apply twfP_out_pieces; [exact MI | rewrite get_set; lia | rewrite get_set, set_set; exact HP].
  Qed.

  #[using="get_set set_set set_get"] Theorem tshape_stdout_vprintf : forall ps st mo K,
    minv mo -> Z.of_nat (length (so_buf (get_so st)) + length (concat ps)) < 2^64 ->
    K (Ok (tt, set_so (snd (vprintf_run (get_so st) ps)) st)) mo [] ->
    t_eq (tsh (stdout_vprintf get_so set_so ps st) mo K)
         (t_emit (wr 1 (fst (vprintf_run (get_so st) ps))) (K (Ok (tt, set_so (snd (vprintf_run (get_so st) ps)) st)) mo)).
  Proof.
    intros ps st mo K MI BND HK. unfold stdout_vprintf. rewrite towrite_bind. unfold vprintf_run in HK |- *.
    pose proof (so_towrite_buf (get_so st)).
    eapply t_eq_trans; [apply tshape_out_pieces; [exact MI | rewrite get_set; lia | rewrite get_set, set_set; exact HK]|].
    rewrite get_set, set_set. apply t_eq_refl.
  Qed.

  Definition exit_flush_run (so : stdout_st) : list Z * stdout_st :=
    if 0 <? zlength (so_buf so) then (so_buf so, so_after_write so) else ([], so).

  #[using="get_set set_set set_get"] Theorem twfP_stdout_exit_flush : forall st mo P,
    minv mo -> Z.of_nat (length (so_buf (get_so st))) < 2^64 ->
    P (Ok (tt, set_so (snd (exit_flush_run (get_so st))) st)) mo ->
    twf (stdout_exit_flush get_so set_so st) mo P.
  Proof.
    intros st mo P MI BND HP. unfold stdout_exit_flush. rewrite rd_so_bind. unfold exit_flush_run in HP.
    destruct (0 <? zlength (so_buf (get_so st))); cbn [fst snd] in HP.
    - apply twfP_stdout_writefn; [exact MI | cbn [length]; lia |]. exact HP.
    - cbn [twfP mret]. rewrite set_get in HP. exact HP.
  Qed.

  #[using="get_set set_set set_get"] Theorem tshape_stdout_exit_flush : forall st mo K,
    minv mo -> Z.of_nat (length (so_buf (get_so st))) < 2^64 ->
    K (Ok (tt, set_so (snd (exit_flush_run (get_so st))) st)) mo [] ->
    t_eq (tsh (stdout_exit_flush get_so set_so st) mo K)
         (t_emit (wr 1 (fst (exit_flush_run (get_so st)))) (K (Ok (tt, set_so (snd (exit_flush_run (get_so st))) st)) mo)).
  Proof.
    intros st mo K MI BND HK. unfold stdout_exit_flush. rewrite rd_so_bind. unfold exit_flush_run in HK |- *.
    destruct (0 <? zlength (so_buf (get_so st))); cbn [fst snd] in HK |- *.
    - eapply t_eq_trans; [apply tshape_stdout_writefn; [exact MI | cbn [length]; lia | exact HK]|]. rewrite app_nil_r. apply t_eq_refl.
    - cbn [tshape mret]. rewrite set_get in HK |- *. apply t_eq_sym. apply t_emit_nil_eq. exact HK.
  Qed.
End StdoutShapes.

Section StderrShapes.
  Context {St : Type}.

  Fixpoint se_run (buf : list Z) (ps : list (list Z)) : list Z * list Z :=
    match ps with
    | [] => ([], buf)
    | p :: ps' =>
        if INTERNAL_BUFSIZ - zlength buf <? zlength p
        then let r := se_run [] ps' in (buf ++ p ++ fst r, snd r)
        else se_run (buf ++ p) ps'
    end.

  #[using="Type"] Lemma se_run_total : forall ps buf, fst (se_run buf ps) ++ snd (se_run buf ps) = buf ++ concat ps.
  Proof.
    induction ps as [|p ps IH]; intros buf; cbn [se_run concat]; [rewrite app_nil_r; reflexivity|].
    destruct (INTERNAL_BUFSIZ - zlength buf <? zlength p); cbn [fst snd].
    - rewrite <- !app_assoc. rewrite (IH []). reflexivity.
    - rewrite IH. rewrite app_assoc. reflexivity.
  Qed.

  #[using="Type"] Lemma se_run_len : forall ps buf, (length (snd (se_run buf ps)) <= length buf + length (concat ps))%nat.
  Proof.
    intros ps buf. pose proof (f_equal (@length Z) (se_run_total ps buf)) as E. rewrite !length_app in E. lia.
  Qed.

  #[using="Type"] Lemma twfP_stderr_pieces : forall ps buf (st : St) mo P,
    minv mo -> Z.of_nat (length buf + length (concat ps)) < 2^64 ->
    P (Ok (snd (se_run buf ps), st)) mo ->
    twf (stderr_pieces buf ps st) mo P.
  Proof.
    induction ps as [|p ps IH]; intros buf st mo P MI BND HP; cbn [stderr_pieces se_run] in HP |- *.
    - exact HP.
    - cbn [concat] in BND. rewrite length_app in BND.
      destruct (INTERNAL_BUFSIZ - zlength buf <? zlength p); cbn [fst snd] in HP.
      + apply twfP_mbind. apply twfP_stdio_writev; [exact MI | lia |]. cbn [pbind fst snd].
        apply IH; [exact MI | cbn [length]; lia | exact HP].
      + apply IH; [exact MI | rewrite length_app; lia | exact HP].
  Qed.

  #[using="Type"] Lemma tshape_stderr_pieces : forall ps buf (st : St) mo K,
    minv mo -> Z.of_nat (length buf + length (concat ps)) < 2^64 ->
    K (Ok (snd (se_run buf ps), st)) mo [] ->
    t_eq (tsh (stderr_pieces buf ps st) mo K)
         (t_emit (wr 2 (fst (se_run buf ps))) (K (Ok (snd (se_run buf ps), st)) mo)).
  Proof.
    induction ps as [|p ps IH]; intros buf st mo K MI BND HK; cbn [stderr_pieces se_run] in HK |- *.
    - cbn [tshape fst snd]. apply t_eq_sym. apply t_emit_nil_eq. exact HK.
    - cbn [concat] in BND. rewrite length_app in BND.
      destruct (INTERNAL_BUFSIZ - zlength buf <? zlength p); cbn [fst snd] in HK |- *.
      + eapply t_eq_trans; [apply tshape_mbind|].
        eapply t_eq_trans; [apply tshape_stdio_writev; [exact MI | lia |]|].
        * cbn [kbind fst snd]. apply (proj2 (IH [] st mo K MI ltac:(cbn [length]; lia) HK [])). apply t_emit_has_nil.
        * cbn [kbind fst snd]. rewrite app_assoc, wr_app. eapply t_eq_trans; [| apply t_emit_app]. apply t_eq_emit.
          apply IH; [exact MI | cbn [length]; lia | exact HK].
      + apply IH; [exact MI | rewrite length_app; lia | exact HK].
  Qed.

  #[using="Type"] Theorem twfP_stderr_fprintf : forall ps (st : St) mo P,
    minv mo -> Z.of_nat (length (concat ps)) < 2^64 ->
    P (Ok (tt, st)) mo ->
    twf (stderr_fprintf ps st) mo P.
  Proof.
    intros ps st mo P MI BND HP. unfold stderr_fprintf.
    apply twfP_mbind. apply twfP_stderr_pieces; [exact MI | cbn [length]; lia |]. cbn [pbind fst snd].
    pose proof (se_run_len ps []) as L. cbn [length] in L.
    apply twfP_stdio_writev; [exact MI | cbn [length]; lia | exact HP].
  Qed.

  #[using="Type"] Theorem tshape_stderr_fprintf : forall ps (st : St) mo K,
    minv mo -> Z.of_nat (length (concat ps)) < 2^64 ->
    K (Ok (tt, st)) mo [] ->
    t_eq (tsh (stderr_fprintf ps st) mo K)
         (t_emit (wr 2 (concat ps)) (K (Ok (tt, st)) mo)).
  Proof.
    intros ps st mo K MI BND HK. unfold stderr_fprintf.
    pose proof (se_run_len ps []) as L. cbn [length] in L.
    eapply t_eq_trans; [apply tshape_mbind|].
    eapply t_eq_trans; [apply tshape_stderr_pieces; [exact MI | cbn [length]; lia |]|].
    - cbn [kbind fst snd].
      assert (B2 : Z.of_nat (length (snd (se_run [] ps)) + length (@nil Z)) < 2^64) by (cbn [length]; lia).
      apply (proj2 (tshape_stdio_writev 2 _ [] st mo K MI B2 HK [])). apply t_emit_has_nil.
    - cbn [kbind fst snd]. eapply t_eq_trans; [apply t_eq_emit; apply tshape_stdio_writev; [exact MI | cbn [length]; lia | exact HK]|].
      eapply t_eq_trans; [apply t_emit_app|]. unfold wr, to_bytes. rewrite <- !map_app, app_nil_r.
      rewrite <- (app_nil_l (concat ps)). rewrite <- (se_run_total ps []). apply t_eq_refl.
  Qed.

  #[using="Type"] Theorem twfP_stderr_fwrite : forall s (st : St) mo P,
    minv mo -> Z.of_nat (length s) < 2^64 -> P (Ok (tt, st)) mo ->
    twf (stderr_fwrite s st) mo P.
  Proof.
    intros s st mo P MI BND HP. unfold stderr_fwrite.
    destruct (0 <? zlength s); [apply twfP_stdio_writev; [exact MI | cbn [length]; lia | exact HP] | exact HP].
  Qed.

  #[using="Type"] Theorem tshape_stderr_fwrite : forall s (st : St) mo K,
    minv mo -> Z.of_nat (length s) < 2^64 -> K (Ok (tt, st)) mo [] ->
    t_eq (tsh (stderr_fwrite s st) mo K) (t_emit (wr 2 s) (K (Ok (tt, st)) mo)).
  Proof.
    intros s st mo K MI BND HK. unfold stderr_fwrite.
    destruct (Z.ltb_spec0 0 (zlength s)).
    - eapply t_eq_trans; [apply tshape_stdio_writev; [exact MI | cbn [length]; lia | exact HK]|]. cbn [app]. apply t_eq_refl.
    - destruct s; [| unfold zlength in *; cbn [length] in *; lia]. cbn [tshape mret]. apply t_eq_sym. apply t_emit_nil_eq. exact HK.
  Qed.
End StderrShapes.

Example vprintf_run_emit_first : vprintf_run stdout_init pieces_emit = ([48; 10], mkStdout true [] false false).
Proof. vm_compute. reflexivity. Qed.

Lemma fwx_run_plain : forall buf s, zlength buf + zlength s <= STDOUT_BUFSIZ ->
  fwx_run (mkStdout true buf false false) s = ([], mkStdout true (buf ++ s) false false).
Proof.
  intros buf s H. unfold fwx_run, so_towrite. cbn [so_active so_buf so_lbf_nl so_first].
  replace (STDOUT_BUFSIZ - zlength buf <? zlength s) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma vp_run_plain : forall ps buf, zlength buf + zlength (concat ps) <= STDOUT_BUFSIZ ->
  vp_run (mkStdout true buf false false) ps = ([], mkStdout true (buf ++ concat ps) false false).
Proof.
  induction ps as [|p ps IH]; intros buf H.
  - cbn [vp_run concat]. rewrite app_nil_r. reflexivity.
  - cbn [concat] in H. unfold zlength in H. rewrite length_app, Nat2Z.inj_add in H.
    cbn [vp_run]. rewrite fwx_run_plain by (unfold zlength; lia). cbn [fst snd].
    rewrite IH by (unfold zlength; rewrite length_app, Nat2Z.inj_add; lia).
    cbn [fst snd app concat]. rewrite <- app_assoc. reflexivity.
Qed.

Lemma vprintf_run_emit_later : forall buf, zlength buf + 2 <= STDOUT_BUFSIZ ->
  vprintf_run (mkStdout true buf false false) pieces_emit = ([], mkStdout true (buf ++ [48; 10]) false false).
Proof.
  intros buf Hb. unfold vprintf_run, so_towrite. cbn [so_active].
  rewrite vp_run_plain by (exact Hb). reflexivity.
Qed.

Lemma exit_flush_run_nonempty : forall buf lbf first, buf <> [] ->
  exit_flush_run (mkStdout true buf lbf first) = (buf, mkStdout true [] (if first then false else lbf) false).
Proof.
  intros buf lbf first Hb. unfold exit_flush_run. cbn [so_buf].
  destruct buf; [congruence|]. unfold zlength. cbn [length].
  replace (0 <? Z.of_nat (S (length buf))) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
Lemma exit_flush_run_empty : forall a lbf first, exit_flush_run (mkStdout a [] lbf first) = ([], mkStdout a [] lbf first).
Proof. reflexivity. Qed.
