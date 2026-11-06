From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack
  ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import StatementKept SlotInv SlotSteps
  HarnessRep RelayRep relay_add_b_c op_add_c RelayRunT RelayRunF relay_finish_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require SlotRI3.
From Stdlib Require Import ZArith List Bool Lia Permutation.
Import ListNotations.
Local Open Scope Z_scope.

(* How a call moves the view's nc blocks from V (state L A) to V' (state L' A'): dels are the nc blocks it removes and
   adds the nc blocks it makes (address, size); B are the blocks it keeps, X the other blocks it makes and Y the other
   blocks it frees; gone are nc addresses with no block. The resource hypotheses of the slot passes give it to RI. *)
Definition nc_move (V : rview) (L : layout) (A : astate) (V' : rview) (L' : layout) (A' : astate)
    (dels adds : list (Z * Z)) : Prop :=
  exists R gone B X Y,
    Permutation (rv_nc V) (R ++ map fst dels ++ gone) /\ Permutation (rv_nc V') (R ++ map fst adds) /\
    Permutation (blocks L A) (B ++ dels ++ Y) /\ Permutation (blocks L' A') (B ++ adds ++ X) /\
    (forall q m, In (q, m) (blocks L' A') -> 0 <= m) /\
    (forall t, In t dels -> 0 <= snd t) /\ NoDup (map fst dels) /\
    (forall t, In t dels -> ~ In (fst t) R /\ forall m, ~ In (fst t, m) B) /\
    (forall t, In t Y -> ~ In (fst t) R /\ ~ In (fst t) (map fst dels)) /\
    (forall g, In g gone -> forall m, ~ In (g, m) (blocks L A)).

(* The nc blocks of a list (its array when the capacity is not 0) and of a source. *)
Definition arr_sz (l : hlist) : list (Z * Z) := if hl_cap l =? 0 then [] else [(hl_v l, 16 * hl_cap l)].

Definition src_dels (h : hsrc) : list (Z * Z) :=
  arr_sz (hs_pending h) ++ [(hs_partial h, PARTIAL_BYTES)] ++ arr_sz (hs_expected h) ++ arr_sz (hs_held h).

(* The nc blocks of a relay entry (its read buffer and its held-key array), and of a list of entries. *)
Definition entry_dels (e : rentry) : list (Z * Z) :=
  (if re_cap e =? 0 then [] else [(re_buf e, re_cap e)]) ++ (if re_hp e =? 0 then [] else [(re_hp e, re_kh e)]).

Definition ent_dels (es : list rentry) : list (Z * Z) :=
  concat (map (fun e => (if re_cap e =? 0 then [] else [(re_buf e, re_cap e)]) ++
                        (if re_hp e =? 0 then [] else [(re_hp e, re_kh e)])) es).

(* The output buffer q of CAP bytes grown to CAP' bytes (at the address q1). *)
Definition out_dels (q CAP CAP' : Z) : list (Z * Z) := if (CAP' =? CAP) || (CAP =? 0) then [] else [(q, CAP)].

Definition out_adds (q CAP CAP' : Z) : list (Z * Z) := if CAP' =? CAP then [] else [(q, CAP')].

(* The output buffer out (CAP bytes) after a call that can grow it to CAP' bytes and leaves it at q1. It stays when
   q1 = out and CAP' = CAP; otherwise the call freed (out, CAP) (when CAP <> 0) and made (q1, CAP'). The address is in
   the key because the contracts of relay_remove and relay_finish do not say that the buffer stays when CAP' = CAP. *)
Definition out_same (out CAP q1 CAP' : Z) : bool := (q1 =? out) && (CAP' =? CAP).

Definition out_move_dels (out CAP q1 CAP' : Z) : list (Z * Z) :=
  if out_same out CAP q1 CAP' || (CAP =? 0) then [] else [(out, CAP)].

Definition out_move_adds (out CAP q1 CAP' : Z) : list (Z * Z) :=
  if out_same out CAP q1 CAP' then [] else [(q1, CAP')].

(* A list array of CAP records at q, grown when it is full (N = CAP), to the array at q1. *)
Definition grow_dels (q N CAP : Z) : list (Z * Z) :=
  if (N =? CAP) && negb (CAP =? 0) then [(q, 16 * CAP)] else [].

Definition grow_adds (q N CAP : Z) : list (Z * Z) :=
  if N =? CAP then [(q, if CAP =? 0 then 128 else 32 * CAP)] else [].

(* The blocks op_add makes: the partial buffer, and the table on the first add (C = 0). *)
Definition entry_adds (q g C : Z) : list (Z * Z) :=
  (q, PARTIAL_BYTES) :: (if C =? 0 then [(g, SRC_TABLE)] else []).

Definition op0_adds (q : Z) (i : option nat) : list (Z * Z) :=
  match i with Some _ => [(q, PARTIAL_BYTES)] | None => [] end.

(* relay_finish at the exit (trace from the names known_at L A, the output buffer out): it grows the output buffer
   (CAP bytes to relay_finish_cap bytes, at q1, linked to the trace's last out address by the run's qs) and frees the
   nc blocks of the entries es. *)
Definition fin_RV_d (RI : res_inv) (E : sstart) (k : Z) (L : layout) (A : astate) (G out : Z) (es : list rentry)
    (hj : list (hsrc * nat)) (live : bool) (mx CAP : Z) (L' : layout) (A' : astate) (qs : list sptr) : Prop :=
  forall G' out' es' hj',
    (forall q m, In (q, m) (blocks L' A') -> In (q, m) (blocks L A) \/ In q (target_addrs G' out' es' hj')) ->
    pend_view hj' = pend_view hj -> ek_view hj' = ek_view hj -> (length es' <= 4)%nat -> (length hj' <= 4)%nat ->
    forall q1, (live = false -> q1 = out) ->
    (live = true ->
       live_at L' A' (resolveF qs (relay_finish_out (known_at L A) live mx 0 CAP es 0 (known_at L A out))) q1
         (relay_finish_cap live mx 0 CAP es)) ->
    nc_move (view_of G out es hj) L A (view_of G' out' es' hj') L' A'
      (out_move_dels out CAP q1 (relay_finish_cap live mx 0 CAP es) ++ ent_dels es)
      (out_move_adds out CAP q1 (relay_finish_cap live mx 0 CAP es)) ->
    List.NoDup (map fst (blocks L' A')) ->
    (forall p n n', In (p, n) (user_blocks A) -> In (p, n') (user_blocks A') ->
       In (ptr_addr L p) (rv_nc (view_of G out es hj)) ->
       ~ In (ptr_addr L p) (map fst (out_move_dels out CAP q1 (relay_finish_cap live mx 0 CAP es) ++ ent_dels es)) ->
       In (ptr_addr L' p) (rv_nc (view_of G' out' es' hj'))) ->
    SlotRI3.ncs (view_of G' out' es' hj') L' A' <= nc_wt es' hj' -> nc_wt es' hj' <= nc_wt es hj ->
    RI E k (view_of G' out' es' hj') L' A'.

(* ---- Lemmas to prove nc_move from a call's post (block lists, keys, sizes). ---- *)

Lemma mv_fst_uniq : forall (l : list (Z * Z)) a m m', List.NoDup (map fst l) -> In (a, m) l -> In (a, m') l -> m = m'.
Proof.
  induction l as [|[b k] l IH]; intros a m m' ND H1 H2; [destruct H1|].
  cbn [map fst] in ND. apply List.NoDup_cons_iff in ND as [NI ND].
  destruct H1 as [E1|H1]; destruct H2 as [E2|H2].
  - congruence.
  - exfalso. apply NI. apply in_map_iff. exists (a, m'). split; [cbn [fst]; congruence|exact H2].
  - exfalso. apply NI. apply in_map_iff. exists (a, m). split; [cbn [fst]; congruence|exact H1].
  - exact (IH a m m' ND H1 H2).
Qed.

Lemma mv_part : forall {X} (p : X -> bool) l, Permutation l (List.filter p l ++ List.filter (fun x => negb (p x)) l).
Proof.
  intros X p l. induction l as [|x l IH]; [constructor|]. simpl. destruct (p x); simpl.
  - apply perm_skip. exact IH.
  - apply Permutation_cons_app. exact IH.
Qed.

Lemma mv_inb : forall (x : Z) l, existsb (Z.eqb x) l = true <-> In x l.
Proof.
  intros x l. rewrite existsb_exists. split.
  - intros (y & Hy & E). apply Z.eqb_eq in E. subst y. exact Hy.
  - intros Hx. exists x. split; [exact Hx|apply Z.eqb_refl].
Qed.

Lemma mv_negb_in : forall (x : Z) l, In x l -> negb (existsb (Z.eqb x) l) = false.
Proof. intros x l H. rewrite (proj2 (mv_inb x l) H). reflexivity. Qed.

Lemma mv_negb_out : forall (x : Z) l, negb (existsb (Z.eqb x) l) = true -> ~ In x l.
Proof. intros x l H Hx. rewrite (mv_negb_in x l Hx) in H. discriminate. Qed.

Lemma mv_negb_nin : forall (x : Z) l, ~ In x l -> negb (existsb (Z.eqb x) l) = true.
Proof. intros x l H. destruct (existsb (Z.eqb x) l) eqn:X; [apply mv_inb in X; contradiction|reflexivity]. Qed.

Lemma mv_nodup_app : forall {X} (l l' : list X), List.NoDup l -> List.NoDup l' -> (forall a, In a l -> ~ In a l') ->
  List.NoDup (l ++ l').
Proof.
  intros X l l' H1 H2 H3. induction H1 as [|x l Hx Hl IH]; [exact H2|]. cbn [app]. constructor.
  - intros Hin. apply in_app_iff in Hin as [Hin|Hin]; [exact (Hx Hin)|exact (H3 x (or_introl eq_refl) Hin)].
  - apply IH. intros a Ha. apply H3. right. exact Ha.
Qed.

(* The blocks of a state split into the kept ones, the removed nc blocks dl and the other removed blocks. *)
Lemma mv_split3 : forall (l dl : list (Z * Z)) (keep : Z -> bool),
  List.NoDup (map fst l) -> List.NoDup (map fst dl) -> incl dl l -> (forall t, In t dl -> keep (fst t) = false) ->
  Permutation l (List.filter (fun t => keep (fst t)) l ++ dl ++
    List.filter (fun t => negb (existsb (Z.eqb (fst t)) (map fst dl))) (List.filter (fun t => negb (keep (fst t))) l)).
Proof.
  intros l dl keep ND0 NDd Inc Kd.
  eapply Permutation_trans; [apply (mv_part (fun t => keep (fst t)))|]. apply Permutation_app_head.
  eapply Permutation_trans;
    [apply (mv_part (fun t => existsb (Z.eqb (fst t)) (map fst dl)) (List.filter (fun t => negb (keep (fst t))) l))|].
  apply Permutation_app_tail. apply NoDup_Permutation.
  - apply List.NoDup_filter. apply List.NoDup_filter. exact (List.NoDup_map_inv _ _ ND0).
  - exact (List.NoDup_map_inv _ _ NDd).
  - intros t. rewrite !List.filter_In. split.
    + intros ((Ht & _) & Hx). apply mv_inb in Hx. apply in_map_iff in Hx as (d & Ed & Hd).
      assert (Hdl : In d l) by (apply Inc; exact Hd).
      destruct t as [ta tm]; destruct d as [da dm]. cbn [fst] in Ed. subst da.
      rewrite (mv_fst_uniq l ta tm dm ND0 Ht Hdl). exact Hd.
    + intros Hd. split; [split|].
      * apply Inc. exact Hd.
      * rewrite (Kd t Hd). reflexivity.
      * apply mv_inb. apply in_map. exact Hd.
Qed.

Lemma mv_map_fst_entry : forall e, map fst (entry_dels e) = entry_nc e.
Proof. intros e. unfold entry_dels, entry_nc. destruct (re_cap e =? 0); destruct (re_hp e =? 0); reflexivity. Qed.

Lemma mv_map_fst_src : forall h, map fst (src_dels h) = src_nc h.
Proof.
  intros h. unfold src_dels, src_nc, arr_sz, arr_nc.
  destruct (hl_cap (hs_pending h) =? 0); destruct (hl_cap (hs_expected h) =? 0); destruct (hl_cap (hs_held h) =? 0);
    reflexivity.
Qed.

(* nc_move from a call's post. keep x is true for the blocks of L A the call keeps. The call removes the nc blocks dels
   (keep is false on them) and other blocks (keep is false, not in R); L' A' has the kept blocks, the new nc blocks adds
   and other new blocks X. R is the part of the view that stays; gone are view addresses with no block in L A. *)
Lemma mv_build : forall (V V' : rview) (L : layout) (A : astate) (L' : layout) (A' : astate)
    (dels adds X : list (Z * Z)) (R gone : list Z) (keep : Z -> bool),
  List.NoDup (map fst (blocks L A)) -> List.NoDup (map fst (blocks L' A')) ->
  Permutation (rv_nc V) (R ++ map fst dels ++ gone) -> Permutation (rv_nc V') (R ++ map fst adds) ->
  incl dels (blocks L A) -> List.NoDup (map fst dels) -> (forall t, In t dels -> keep (fst t) = false) ->
  (forall x m, In (x, m) (blocks L A) -> keep x = false -> ~ In x R) ->
  (forall x m, In (x, m) (blocks L' A') -> (In (x, m) (blocks L A) /\ keep x = true) \/ In (x, m) (adds ++ X)) ->
  (forall x m, In (x, m) (blocks L A) -> keep x = true -> In (x, m) (blocks L' A')) ->
  incl (adds ++ X) (blocks L' A') -> List.NoDup (adds ++ X) ->
  (forall t, In t (adds ++ X) -> keep (fst t) = false \/ ~ In t (blocks L A)) ->
  (forall x m, In (x, m) (blocks L' A') -> 0 <= m) ->
  (forall t, In t dels -> 0 <= snd t) -> (forall g, In g gone -> forall m, ~ In (g, m) (blocks L A)) ->
  nc_move V L A V' L' A' dels adds.
Proof.
  intros V V' L A L' A' dels adds X R gone keep ND0 ND1 PV PV' Inc NDd Kd KR H1 H2 H3 NDa Ka Pos Dn Gn.
  exists R, gone, (List.filter (fun t => keep (fst t)) (blocks L A)), X,
    (List.filter (fun t => negb (existsb (Z.eqb (fst t)) (map fst dels)))
      (List.filter (fun t => negb (keep (fst t))) (blocks L A))).
  split; [exact PV|]. split; [exact PV'|].
  split; [exact (mv_split3 _ _ keep ND0 NDd Inc Kd)|].
  split.
  { apply NoDup_Permutation.
    - exact (List.NoDup_map_inv _ _ ND1).
    - apply mv_nodup_app; [apply List.NoDup_filter; exact (List.NoDup_map_inv _ _ ND0)|exact NDa|].
      intros a Ha Hb. apply List.filter_In in Ha as (Ha & Hk).
      destruct (Ka a Hb) as [Kf|NI]; [rewrite Kf in Hk; discriminate|exact (NI Ha)].
    - intros [x m]. rewrite in_app_iff, List.filter_In. cbn [fst]. split.
      + intros Hx. destruct (H1 x m Hx) as [(Hx0 & Hk)|Hx1]; [left; split; assumption|right; exact Hx1].
      + intros [(Hx0 & Hk)|Hx1]; [exact (H2 x m Hx0 Hk)|exact (H3 _ Hx1)]. }
  split; [exact Pos|]. split; [exact Dn|]. split; [exact NDd|].
  split.
  { intros [x m] Ht. cbn [fst]. split.
    - exact (KR x m (Inc _ Ht) (Kd _ Ht)).
    - intros m' Hm. apply List.filter_In in Hm as (_ & Hk). cbn [fst] in Hk. pose proof (Kd _ Ht) as Kx.
      cbn [fst] in Kx. rewrite Kx in Hk. discriminate. }
  split.
  { intros [x m] Ht. rewrite !List.filter_In in Ht. destruct Ht as ((Ht & Hk) & Hd). cbn [fst] in *. split.
    - apply negb_true_iff in Hk. exact (KR x m Ht Hk).
    - exact (mv_negb_out _ _ Hd). }
  exact Gn.
Qed.
