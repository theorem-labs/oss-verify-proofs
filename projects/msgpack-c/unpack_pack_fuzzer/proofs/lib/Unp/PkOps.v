(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem State MemProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Steps OpsBridge Tree Cost.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Seal.
Import ListNotations.
Import W64 Val Mem St MemP UB HeapOp TR.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module PK.

Definition CM_PK : Z := 3.
Definition K_ETOP : Z := 6.

Definition okids (o : obj) : list obj := match o with OArr _ ks | OMap _ ks => ks | _ => [] end.
Definition is_cont (o : obj) : bool := match o with OArr _ _ | OMap _ _ => true | _ => false end.
Definition is_mapo (o : obj) : bool := match o with OMap _ _ => true | _ => false end.

Definition obj_via (o : obj) : Z :=
  match o with
  | ONil => 0 | OBool b => (if b then 1 else 0) | OPos u => u | ONeg i => enc64 i | OF32 b | OF64 b => b
  | OStr _ n | OBin _ n | OExt _ n => n
  | OArr _ ks => Z.of_nat (length ks) | OMap _ ks => Z.of_nat (length ks) / 2
  end.

Fixpoint levels_ok (o : obj) (ls : list (obj * Z)) : Prop :=
  match ls with
  | [] => True
  | (c, s) :: rest => c = o /\ is_cont o = true /\ 0 <= s /\
      match nth_error (okids o) (Z.to_nat s) with
      | Some k => levels_ok k rest
      | None => rest = [] /\ okids o = [] /\ s = 0
      end
  end.

Definition elem_of (l : obj * Z) : pelem :=
  let (o, s) := l in
  match o with
  | OMap p kids => mkPE (p + 48 * (s / 2)) (Z.of_nat (length kids) / 2 - s / 2) true (Z.even s)
  | _ => mkPE (obj_ptr o + 24 * s) (Z.of_nat (length (okids o)) - s) false false
  end.

Definition lev_addr (l : obj * Z) : Z := obj_ptr (fst l) + OBJ_SIZE * snd l.

Definition lev_node (l : obj * Z) : option obj := nth_error (okids (fst l)) (Z.to_nat (snd l)).

Definition focus_addr (root : Z) (ls : list (obj * Z)) : Z :=
  match last_opt ls with None => root | Some l => lev_addr l end.
Definition focus_node (t : obj) (ls : list (obj * Z)) : option obj :=
  match last_opt ls with None => Some t | Some l => lev_node l end.

Definition pk10_tree (o : obj) : Z := 10 * Z.of_nat (obj_size o) + Cost.obj_bodies o.
Definition pk10_list (l : list obj) : Z := 10 * Z.of_nat (objs_size l) + Cost.objs_bodies l.
Definition own10 (o : obj) : Z := match o with OStr _ n | OBin _ n => 10 + n | OExt _ n => 11 + n | _ => 10 end.
Definition desc10 (o : obj) : Z := pk10_list (okids o).
Definition ahead10 (l : obj * Z) : Z := pk10_list (skipn (S (Z.to_nat (snd l))) (okids (fst l))).
Definition np_strict (ls : list (obj * Z)) : Z := fold_right (fun l acc => ahead10 l + acc) 0 ls.
Definition focus_term (fo : option obj) (fresh cfz : bool) : Z :=
  match fo with
  | None => 0
  | Some o => if fresh then pk10_tree o else if cfz then 0 else desc10 o
  end.
Definition np (t : obj) (ls : list (obj * Z)) (fresh cfz : bool) : Z :=
  match ls with
  | [] => desc10 t
  | _ => np_strict ls + focus_term (focus_node t ls) fresh cfz
  end.
Definition PKU_BASE : Z := 2 ^ 62.
Definition PKU_ST : Z := 2 ^ 56.
Definition PKU_SPAN : Z := 2 ^ 42.

Definition pku_val (w : window) : option (bool * Z) :=
  if (w_kind w =? 0) && (w_len w =? 0) then
    if (PKU_BASE <=? w_lo w) && (w_lo w <? PKU_BASE + PKU_SPAN) then Some (true, w_lo w - PKU_BASE)
    else if (PKU_BASE + PKU_ST <=? w_lo w) && (w_lo w <? PKU_BASE + PKU_ST + PKU_SPAN) then Some (false, w_lo w - (PKU_BASE + PKU_ST))
    else None
  else None.

Record pkargs := PA {
  a_root : Z; a_rootT : Z; a_n1 : Z; a_P1 : Z;
  a_c0 : Z;
  a_eb : Z; a_ee : Z; a_ecap : Z;
  a_tptr : Z; a_trest : Z; a_tmap : Z; a_tkey : Z;
  a_cf : Z; a_fT : Z; a_fN : Z; a_fP : Z }.

Definition decode_pk (ca : list word) : option pkargs :=
  match ca with
  | [root; rootT; n1; P1; _zh; c0; eb; ee; ecap; tptr; trest; tmap; tkey; cf; fT; fN; fP] =>
      Some (PA (bv_unsigned root) (bv_unsigned rootT) (bv_unsigned n1) (bv_unsigned P1) (bv_unsigned c0)
              (bv_unsigned eb) (bv_unsigned ee) (bv_unsigned ecap)
              (bv_unsigned tptr) (bv_unsigned trest) (bv_unsigned tmap) (bv_unsigned tkey)
              (bv_unsigned cf) (bv_unsigned fT) (bv_unsigned fN) (bv_unsigned fP))
  | _ => None
  end.

Definition b2Z (b : bool) : Z := if b then 1 else 0.

Record pkg := PKG {
  k_tree : obj;
  k_evec : vecg;
  k_zone : zoneg }.

Section WithSegs.
Variable segs : list Segment.

Definition link_pk (u : pkargs) (g : pkg) (ls : list (obj * Z)) : Prop :=
  obj_type (k_tree g) = a_rootT u /\ obj_cnt (k_tree g) = a_n1 u /\ obj_ptr (k_tree g) = a_P1 u /\
  z_head (k_zone g) = a_c0 u /\
  v_begin (k_evec g) = a_eb u /\ v_end (k_evec g) = a_ee u /\ v_capend (k_evec g) = a_ecap u /\
  match last_opt ls with
  | None => a_tptr u = 0 /\ a_trest u = 0 /\ a_tmap u = 0 /\ a_tkey u = 0
  | Some l => let e := elem_of l in a_tptr u = pe_ptr e /\ a_trest u = pe_rest e /\ a_tmap u = b2Z (pe_map e) /\ a_tkey u = b2Z (pe_key e)
  end /\
  (a_cf u <> 0 -> ls <> [] /\ a_cf u = focus_addr (a_root u) ls /\
     exists fo, focus_node (k_tree g) ls = Some fo /\ obj_type fo = a_fT u /\ obj_via fo = a_fN u /\ obj_ptr fo = a_fP u).

Definition ecap_ok (c : Z) : Prop := 0 < c /\ (pow2_b c = true /\ c <= 1024).

Definition pure_pk (g : pkg) (ls : list (obj * Z)) : Prop :=
  levels_ok (k_tree g) ls /\
  v_elt (k_evec g) = ELEM_SIZE /\ v_size (k_evec g) = Z.of_nat (length ls) /\
  ((v_begin (k_evec g) = 0 /\ v_cap (k_evec g) = 0 /\ ls = []) \/ (vec_valid (k_evec g) /\ ecap_ok (v_cap (k_evec g)))) /\
  v_capend (k_evec g) <= two64 /\
  (zone_valid (k_zone g) /\ (Cost.obj_depth (k_tree g) <= 1001)%nat).

Definition evec_blocks (g : pkg) : list (Z * Z) :=
  if v_begin (k_evec g) =? 0 then [] else [(v_begin (k_evec g), v_bytes (k_evec g))].
Definition owned (g : pkg) : list (Z * Z) := evec_blocks g ++ map chunk_block (z_chunks (k_zone g)).

Definition own_pk (g : pkg) (LB : blocks) : Prop :=
  (forall b, In b (owned g) -> In b LB) /\ ForallOrdPairs (fun b b' => rdisj (fst b) (snd b) (fst b') (snd b')) (owned g).

Definition etop_ok (g : pkg) (w : window) : Prop :=
  w_kind w = K_ETOP /\ v_begin (k_evec g) <> 0 /\
  v_begin (k_evec g) <= w_lo w /\ v_end (k_evec g) - ELEM_SIZE <= w_lo w /\ w_lo w + w_len w <= v_capend (k_evec g).
Definition wins_pk (g : pkg) (ws : list window) : Prop :=
  Forall (fun w => w_kind w <> K_STACK ->
            ((w_kind w = K_BLOCK \/ K_GHOST <= w_kind w) /\ forall b, In b (owned g) -> forall a, in_iv (w_iv w) a -> ~ in_iv b a)
            \/ (w_kind w <> K_BLOCK /\ etop_ok g w)) ws.

Definition in_zone_cells (z : zoneg) (root : Z) (t : obj) : Prop :=
  (forall c, In c (tl (obj_cells root t)) -> in_zone z c OBJ_SIZE) /\
  Forall (fun b => 0 <= snd b /\ in_zone z (fst b) (snd b)) (obj_bodies t).

Definition mem_pk (bm : bmem) (u : pkargs) (g : pkg) (ls : list (obj * Z)) : Prop :=
  tree_wf bm (k_zone g) (k_tree g) /\ kids_at bm (k_tree g) /\ in_zone_cells (k_zone g) (a_root u) (k_tree g) /\
  chunks_at bm (z_chunks (k_zone g)) /\
  (v_begin (k_evec g) <> 0 -> pelems_at bm (v_begin (k_evec g)) (map elem_of (removelast ls))).

Definition etop_present (g : pkg) (ws : list window) : Prop :=
  v_begin (k_evec g) <> 0 -> exists w, In w ws /\ etop_ok g w /\ 0 < w_len w.
Definition ghost_pk (g : pkg) (ws : list window) : Prop :=
  Seal.seal_ok ws (z_chunks (k_zone g)) /\ etop_present g ws.

Definition cost_pk (u : pkargs) (g : pkg) (ls : list (obj * Z)) (ws : list window) : Prop :=
  forall w fr v, In w ws -> pku_val w = Some (fr, v) -> np (k_tree g) ls fr (a_cf u =? 0) <= v.
Lemma cost_pk_ws : forall u g ls ws ws', cost_pk u g ls ws -> (forall w, In w ws' -> pku_val w <> None -> In w ws) -> cost_pk u g ls ws'.
Proof. intros u g ls ws ws' C H w fr v Hw PV. apply (C w fr v); [| exact PV]. apply H; [exact Hw| rewrite PV; discriminate]. Qed.
Lemma pku_val_kind : forall w p, pku_val w = Some p -> w_kind w = 0 /\ w_len w = 0.
Proof. intros w p H. unfold pku_val in H. destruct ((w_kind w =? 0) && (w_len w =? 0)) eqn:C; [| discriminate].
  apply andb_prop in C as [K L]. apply Z.eqb_eq in K. apply Z.eqb_eq in L. split; assumption. Qed.

Lemma pku_val_none_kind : forall w, w_kind w <> 0 -> pku_val w = None.
Proof. intros w K. unfold pku_val. destruct (Z.eqb_spec (w_kind w) 0) as [E|_]; [contradiction| reflexivity]. Qed.
Lemma cost_pk_sub : forall u g ls ws ws', cost_pk u g ls ws -> (forall w, In w ws' -> In w ws) -> cost_pk u g ls ws'.
Proof. intros u g ls ws ws' C H. apply (cost_pk_ws u g ls ws ws' C). intros w Hw _. exact (H w Hw). Qed.
Lemma cost_pk_app : forall u g ls ws new, cost_pk u g ls ws -> Forall (fun w => w_kind w <> 0 \/ w_len w <> 0) new -> cost_pk u g ls (ws ++ new).
Proof.
  intros u g ls ws new C HN. apply (cost_pk_ws u g ls ws); [exact C|]. intros w Hw NV. apply in_app_iff in Hw as [Hw|Hw]; [exact Hw|]. exfalso.
  destruct (pku_val w) as [pv|] eqn:PV; [| exact (NV eq_refl)]. destruct (pku_val_kind _ _ PV) as [K L0].
  destruct (proj1 (Forall_forall _ _) HN w Hw) as [X|X]; contradiction.
Qed.

Lemma cost_pk_args : forall u u' g g' ls ws, cost_pk u g ls ws -> k_tree g' = k_tree g -> (a_cf u' =? 0) = (a_cf u =? 0) -> cost_pk u' g' ls ws.
Proof. intros u u' g g' ls ws C T F w fr v Hw PV. rewrite T, F. exact (C w fr v Hw PV). Qed.

Definition pk_client (u : pkargs) (LB : blocks) (ws : list window) (m : word -> option byte) : Prop :=
  exists g ls, link_pk u g ls /\ pure_pk g ls /\ own_pk g LB /\ wins_pk g ws /\ mem_pk (bmem_of segs m) u g ls /\ ghost_pk g ws /\ cost_pk u g ls ws.

Definition cw_pk_holds (ca : list word) (LB : blocks) (ws : list window) (m : word -> option byte) : Prop :=
  match decode_pk ca with Some u => pk_client u LB ws m | None => False end.

Lemma owned_pos : forall g ls, pure_pk g ls -> forall b, In b (owned g) -> 0 < snd b.
Proof.
  intros g ls (_ & EL & _ & VE & _ & ZV) b Hb. unfold owned, evec_blocks in Hb. apply in_app_iff in Hb as [Hb|Hb].
  - destruct (Z.eqb_spec (v_begin (k_evec g)) 0) as [E|NE]; [destruct Hb|]. destruct Hb as [<-|[]]. cbn [snd].
    destruct VE as [(E0 & _)|[VV (CP & _)]]; [contradiction|]. unfold v_bytes. rewrite EL. unfold ELEM_SIZE. lia.
  - apply in_map_iff in Hb as (c & <- & Hc). cbn [snd chunk_block]. destruct ZV as ((_ & _ & V3 & _) & _). destruct (V3 c Hc) as (_ & _ & S).
    unfold CHUNK_HDR, CHUNK_SIZE0 in *. lia.
Qed.

Lemma own_pk_grow : forall g LB b n, own_pk g LB -> own_pk g ((b, n) :: LB).
Proof. intros g LB b n [O1 O2]. split; [| exact O2]. intros x Hx. right. exact (O1 x Hx). Qed.

Lemma wins_pk_grow : forall g LB ws b n, own_pk g LB -> wins_pk g ws ->
  (forall a, in_iv (b, n) a -> ~ in_user LB a) -> wins_pk g (ws ++ [Win b n K_BLOCK]).
Proof.
  intros g LB ws b n [O1 _] Wk FR. unfold wins_pk in *. apply Forall_app. split; [exact Wk|]. constructor; [|constructor].
  intros _. left. split; [left; reflexivity|]. intros ob Hob a Ha Hb. apply (FR a Ha). unfold in_user. apply in_ivs_In. exists ob. split; [exact (O1 ob Hob)| exact Hb].
Qed.

Lemma cw_pk_grow : forall ca LB ws m b n, cw_pk_holds ca LB ws m ->
  (forall a, in_iv (b, n) a -> ~ in_user LB a) ->
  cw_pk_holds ca ((b, n) :: LB) (ws ++ [Win b n K_BLOCK]) m.
Proof.
  intros ca LB ws m b n H FR. unfold cw_pk_holds in *. destruct (decode_pk ca) as [u|]; [|exact H].
  destruct H as (g & ls & L & P & O & Wk & M & GH & CO). exists g, ls. split; [exact L|]. split; [exact P|]. split; [| split; [| split; [exact M| split]]].
  - apply own_pk_grow. exact O.
  - eapply wins_pk_grow; eassumption.
  - destruct GH as [SE EP]. split.
    + apply Seal.seal_ok_app; [exact SE|]. constructor; [|constructor]. cbn [w_kind]. unfold K_BLOCK, Seal.K_TWIN. lia.
    + intros VB. destruct (EP VB) as (w & Hw & EW). exists w. split; [apply in_app_iff; left; exact Hw| exact EW].
  - apply (cost_pk_ws u g ls ws); [exact CO|]. intros w Hw NV. apply in_app_iff in Hw as [Hw|[<-|[]]]; [exact Hw|].
    exfalso. destruct (pku_val (Win b n K_BLOCK)) as [pv|] eqn:PV; [| exact (NV eq_refl)]. destruct (pku_val_kind _ _ PV) as [K _]. cbn [w_kind] in K. unfold K_BLOCK in K. lia.
Qed.

Lemma own_pk_free : forall g ls LB ws b n, pure_pk g ls -> own_pk g LB -> wins_pk g ws -> In (Win b n K_BLOCK) ws ->
  own_pk g (remove iv_eq_dec (b, n) LB).
Proof.
  intros g ls LB ws b n P [O1 O2] Wk Hin. split; [| exact O2].
  intros x Hx. apply in_in_remove; [| exact (O1 x Hx)]. intros E. subst x.
  pose proof (owned_pos g ls P _ Hx) as POS. cbn [snd] in POS.
  destruct (proj1 (Forall_forall _ _) Wk _ Hin ltac:(cbn [w_kind]; discriminate)) as [[_ D]|[NB _]].
  - apply (D (b, n) Hx b); unfold in_iv, w_iv; cbn [fst snd w_lo w_len]; lia.
  - apply NB. reflexivity.
Qed.

Lemma cw_pk_free : forall ca LB ws m b n ws', cw_pk_holds ca LB ws m -> In (Win b n K_BLOCK) ws ->
  (forall w, In w ws' <-> In w ws /\ w <> Win b n K_BLOCK) ->
  cw_pk_holds ca (remove iv_eq_dec (b, n) LB) ws' m.
Proof.
  intros ca LB ws m b n ws' H Hin Hws'. unfold cw_pk_holds in *. destruct (decode_pk ca) as [u|]; [|exact H].
  destruct H as (g & ls & L & P & O & Wk & M & GH & CO). exists g, ls. split; [exact L|]. split; [exact P|]. split; [| split; [| split; [exact M| split]]].
  4: { apply (cost_pk_ws u g ls ws); [exact CO|]. intros w Hw _. exact (proj1 (proj1 (Hws' w) Hw)). }
  - eapply own_pk_free; eassumption.
  - unfold wins_pk in *. apply Forall_forall. intros w Hw. apply Hws' in Hw as [Hw _]. exact (proj1 (Forall_forall _ _) Wk w Hw).
  - destruct GH as [SE EP]. split.
    + apply (Seal.seal_ok_ws ws); [exact SE|]. intros w Hw _. exact (proj1 (proj1 (Hws' w) Hw)).
    + intros VB. destruct (EP VB) as (w & Hw & EW). exists w. split; [| exact EW]. apply Hws'. split; [exact Hw|].
      intros X. subst w. destruct EW as ((K & _) & _). cbn [w_kind] in K. unfold K_ETOP, K_BLOCK in K. lia.
Qed.

Lemma in_zone_owned : forall g a n x, 0 <= n -> in_zone (k_zone g) a n -> a <= x < a + n ->
  exists b, In b (owned g) /\ in_iv b x.
Proof.
  intros g a n x Hn (c & Hc & IC) Hx. exists (chunk_block c). split.
  - unfold owned. apply in_app_iff. right. apply in_map. exact Hc.
  - unfold in_iv, chunk_block, in_chunk, chunk_lo, chunk_hi, CHUNK_HDR in *. cbn [fst snd]. lia.
Qed.

Section Frame.
  Variables (u : pkargs) (g : pkg) (ls : list (obj * Z)) (LB : blocks) (ws : list window) (m m' : word -> option byte).
  Hypothesis P : pure_pk g ls.
  Hypothesis O : own_pk g LB.
  Hypothesis W : wins_pk g ws.
  Hypothesis FR : forall a, 0 <= a < two64 -> in_user LB a -> ~ in_ws (heap_ws ws) a -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a).
  #[local] Notation bm := (bmem_of segs m).
  #[local] Notation bm' := (bmem_of segs m').

  Definition safe (a : Z) : Prop := forall w, In w ws -> etop_ok g w -> ~ in_iv (w_iv w) a.

  Lemma agree_byte : forall a ob, In ob (owned g) -> in_iv ob a -> safe a -> bm' a = bm a.
  Proof.
    intros a ob Hob Ha SF. unfold bmem_of.
    destruct ((0 <=? a) && (a <? two64)) eqn:RG; [|reflexivity].
    apply andb_prop in RG as [R1 R2]. apply Z.leb_le in R1. apply Z.ltb_lt in R2.
    unfold rb. rewrite (FR a ltac:(lia)); [reflexivity| |].
    - unfold in_user. apply in_ivs_In. exists ob. split; [exact (proj1 O ob Hob)| exact Ha].
    - intros X. unfold in_ws, heap_ws in X. apply in_ivs_In in X as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw).
      apply filter_In in Hw as [Hw NK]. destruct (Z.eqb_spec (w_kind w) K_STACK) as [|NK']; [discriminate|].
      destruct (proj1 (Forall_forall _ _) W w Hw NK') as [[_ D]|[_ ET]]; [exact (D ob Hob a Hin Ha)| exact (SF w Hw ET Hin)].
  Qed.

  Lemma agree_range : forall ob lo n, In ob (owned g) -> (forall x, lo <= x < lo + n -> in_iv ob x /\ safe x) -> agree_on bm bm' lo n.
  Proof. intros ob lo n Hob H x Hx. destruct (H x Hx) as [I S]. exact (agree_byte x ob Hob I S). Qed.

  Lemma evec_chunk_disj : forall c, v_begin (k_evec g) <> 0 -> In c (z_chunks (k_zone g)) ->
    rdisj (v_begin (k_evec g)) (v_bytes (k_evec g)) (fst c) (CHUNK_HDR + snd c).
  Proof.
    intros c NE Hc. destruct O as [O1 O2]. unfold owned, evec_blocks in O2. rewrite (proj2 (Z.eqb_neq _ _) NE) in O2.
    cbn [app] in O2. inversion O2 as [|x0 l F _]; subst.
    pose proof (proj1 (Forall_forall _ _) F (chunk_block c) (in_map _ _ _ Hc)) as D. cbn [fst snd] in D. exact D.
  Qed.

  Lemma safe_zone : forall a n x, 0 <= n -> in_zone (k_zone g) a n -> a <= x < a + n -> safe x.
  Proof.
    intros a n x Hn (c & Hc & IC) Hx w Hw (K & NE & E1 & E2 & E3) Hin.
    pose proof (evec_chunk_disj c NE Hc) as D.
    unfold rdisj, in_chunk, chunk_lo, chunk_hi, CHUNK_HDR, v_bytes, v_end, v_capend, in_iv, w_iv in *. cbn [fst snd] in *.
    destruct P as (_ & EL & _ & _ & _ & _). nia.
  Qed.

  Lemma agree_zone : forall a n, 0 <= n -> in_zone (k_zone g) a n -> agree_on bm bm' a n.
  Proof.
    intros a n Hn IZ x Hx. destruct (in_zone_owned g a n x Hn IZ Hx) as (ob & Hob & I).
    exact (agree_byte x ob Hob I (safe_zone a n x Hn IZ Hx)).
  Qed.

  Lemma mem_frame : mem_pk bm u g ls -> mem_pk bm' u g ls.
  Proof.
    intros (TW & KA & [IC IB] & CH & PE).
    pose proof P as (LV & EL & SZ & VE & CE & ZV).
    split; [| split; [| split; [exact (conj IC IB)| split]]].
    - apply (tree_wf_agree bm bm'); [| exact TW]. intros b Hb. pose proof (proj1 (Forall_forall _ _) IB b Hb) as [Hn IZ].
      exact (agree_zone _ _ Hn IZ).
    - apply (kids_at_frame bm bm' (a_root u)); [| exact KA]. intros c Hc. apply (agree_zone c OBJ_SIZE); [unfold OBJ_SIZE; lia| exact (IC c Hc)].
    - apply (chunks_at_frame bm); [| exact CH]. intros c Hc.
      apply (agree_range (chunk_block c)); [unfold owned; apply in_app_iff; right; apply in_map; exact Hc|].
      destruct ZV as ((_ & _ & V3 & _) & _). destruct (V3 c Hc) as (_ & _ & S3).
      intros x Hx. split; [unfold in_iv, chunk_block, CHUNK_HDR, CHUNK_SIZE0 in *; cbn [fst snd]; lia|].
      intros w Hw (K & NE & E1 & E2 & E3) Hin. pose proof (evec_chunk_disj c NE Hc) as D.
      unfold rdisj, CHUNK_HDR, CHUNK_SIZE0, v_bytes, v_end, v_capend, in_iv, w_iv in *. cbn [fst snd] in *. nia.
    - intros NE. specialize (PE NE). apply (pelems_at_frame bm); [| exact PE].
      rewrite length_map.
      assert (LEN : Z.of_nat (length (removelast ls)) <= Z.of_nat (length ls) - 1 \/ ls = []).
      { destruct ls as [|l0 ls0] using rev_ind; [right; reflexivity| left]. rewrite removelast_snoc, length_app. cbn [length]. lia. }
      destruct LEN as [LEN| ->]; [| cbn; intros x Hx; unfold ELEM_SIZE in Hx; cbn in Hx; lia].
      apply (agree_range (v_begin (k_evec g), v_bytes (k_evec g))).
      + unfold owned, evec_blocks. rewrite (proj2 (Z.eqb_neq _ _) NE). left; reflexivity.
      + destruct VE as [(E0 & _)|[(V1 & V2 & V3 & V4) (CP & _)]]; [contradiction|].
        intros x Hx. split; [unfold in_iv, v_bytes; cbn [fst snd]; rewrite EL in *; unfold ELEM_SIZE in *; nia|].
        intros w Hw (K & _ & E1 & E2 & E3) Hin. unfold v_end, v_capend, v_bytes, in_iv, w_iv, ELEM_SIZE in *. cbn [fst snd] in *.
        rewrite EL, SZ in *. nia.
  Qed.
End Frame.

Lemma cw_pk_frame : forall ca LB ws m m', cw_pk_holds ca LB ws m ->
  (forall a, 0 <= a < two64 -> in_user LB a -> ~ in_ws (heap_ws ws) a -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  cw_pk_holds ca LB ws m'.
Proof.
  intros ca LB ws m m' H FR. unfold cw_pk_holds in *. destruct (decode_pk ca) as [u|]; [|exact H].
  destruct H as (g & ls & L & P & O & Wk & M & GH & CO). exists g, ls. split; [exact L|]. split; [exact P|]. split; [exact O|]. split; [exact Wk|].
  split; [| split; [exact GH| exact CO]].
  exact (mem_frame u g ls LB ws m m' P O Wk FR M).
Qed.

End WithSegs.
End PK.
