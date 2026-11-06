(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Import STree Malloc.
From Ltac2 Require Ltac2.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Open Scope Z_scope.
Local Open Scope stree_scope.

Section ORACLE.
Context {O : Type}.
Variable pans : O -> aptr -> Z -> Z -> Z.     (* [comment removed for export] *)
Variable pupd : O -> ev -> Z -> O.            (* [comment removed for export] *)

Definition psel (o : O) (e : ev) : option Z :=
  match e with EPeek p c h => Some (pans o p c h) | _ => None end.
Definition prun {R} (o : O) (t : M R) : M (O * R) := eruns psel pupd o t.

(* [comment removed for export] *)
Definition KREL {X R1 R2} (RR : O * R1 -> R2 -> Prop)
  (k1 : mstate -> X -> M R1) (k2 : mstate -> X -> M R2) : Prop :=
  forall o st cst x, cst = strip st -> strel RR (prun o (k1 st x)) (k2 cst x).
Definition KREL0 {R1 R2} (RR : O * R1 -> R2 -> Prop)
  (k1 : mstate -> M R1) (k2 : mstate -> M R2) : Prop :=
  forall o st cst, cst = strip st -> strel RR (prun o (k1 st)) (k2 cst).
Definition BREL {R1 R2} (RR : O * R1 -> R2 -> Prop) (b1 : M R1) (b2 : M R2) : Prop :=
  forall o, strel RR (prun o b1) b2.
End ORACLE.
Arguments psel {O} pans o e.
Arguments prun {O} pans pupd {R} o t.
Arguments KREL {O} pans pupd {X R1 R2} RR k1 k2.
Arguments KREL0 {O} pans pupd {R1 R2} RR k1 k2.
Arguments BREL {O} pans pupd {R1 R2} RR b1 b2.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma strip_strip st : strip (strip st) = strip st.
Proof. reflexivity. Qed.

Lemma strip_wr8 p v st : strip (wr8 p v st) = strip st.
Proof. reflexivity. Qed.
Lemma strip_wr16 p v st : strip (wr16 p v st) = strip st.
Proof. reflexivity. Qed.
Lemma strip_wr32 p v st : strip (wr32 p v st) = strip st.
Proof. reflexivity. Qed.
Lemma strip_havoc p n st : strip (havoc p n st) = strip st.
Proof. unfold havoc. destruct (n <=? 0); reflexivity. Qed.
Lemma strip_set_tick t st : strip (set_tick t st) = strip st.
Proof. reflexivity. Qed.
Lemma strip_zero_hdrs p size i cnt st : strip (zero_hdrs p size i cnt st) = strip st.
Proof. revert i st; induction cnt; intros; simpl; auto. rewrite IHcnt. reflexivity. Qed.
Lemma strip_set_size p e n b st : strip (set_size p e n b st) = strip st.
Proof. unfold set_size. destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma strip_enframe_at st g idx n off :
  strip (fst (enframe_at st g idx n off)) = strip st.
Proof.
  unfold enframe_at. destruct (negb (off =? 0)); cbn -[set_size wr8 wr16 strip]; rewrite strip_set_size; reflexivity.
Qed.
Lemma strip_hdr_havoc b st : strip (hdr_havoc b st) = strip st.
Proof. reflexivity. Qed.
Lemma strip_nest_layout st g idx j size cnt : strip (nest_layout st g idx j size cnt) = strip st.
Proof.
  unfold nest_layout. destruct (enframe_at st g idx _ 0) as [st1 p] eqn:E.
  rewrite strip_zero_hdrs, strip_wr8. pose proof (strip_enframe_at st g idx (UNIT * size_class j - IB) 0) as H.
  rewrite E in H. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ctx_strip st : ctx (strip st) = ctx st. Proof. reflexivity. Qed.
Lemma s_ctx_strip st : s_ctx (strip st) = s_ctx st. Proof. reflexivity. Qed.
Lemma s_regions_strip st : s_regions (strip st) = s_regions st. Proof. reflexivity. Qed.
Lemma s_metas_strip st : s_metas (strip st) = s_metas st. Proof. reflexivity. Qed.
Lemma s_areas_strip st : s_areas (strip st) = s_areas st. Proof. reflexivity. Qed.
Lemma s_groups_strip st : s_groups (strip st) = s_groups st. Proof. reflexivity. Qed.
Lemma s_slots_strip st : s_slots (strip st) = s_slots st. Proof. reflexivity. Qed.
Lemma s_next_rid_strip st : s_next_rid (strip st) = s_next_rid st. Proof. reflexivity. Qed.
Lemma s_secret_strip st : s_secret (strip st) = s_secret st. Proof. reflexivity. Qed.
Lemma s_reserved_strip st : s_reserved (strip st) = s_reserved st. Proof. reflexivity. Qed.
Lemma active_strip st sc : active (strip st) sc = active st sc. Proof. reflexivity. Qed.
Lemma usage_strip st sc : usage (strip st) sc = usage st sc. Proof. reflexivity. Qed.
Lemma unmap_seq_strip st i : unmap_seq (strip st) i = unmap_seq st i. Proof. reflexivity. Qed.
Lemma bounces_strip st i : bounces (strip st) i = bounces st i. Proof. reflexivity. Qed.
Lemma get_meta_rec_strip st m : get_meta_rec (strip st) m = get_meta_rec st m. Proof. reflexivity. Qed.
Lemma get_group_strip st g : get_group (strip st) g = get_group st g. Proof. reflexivity. Qed.
Lemma group_active_idx_strip st g : group_active_idx (strip st) g = group_active_idx st g. Proof. reflexivity. Qed.
Lemma get_region_strip st r : get_region (strip st) r = get_region st r. Proof. reflexivity. Qed.
Lemma conc_strip st p : conc (strip st) p = conc st p. Proof. reflexivity. Qed.
Lemma live_ranges_strip st : live_ranges (strip st) = live_ranges st. Proof. reflexivity. Qed.
Lemma brk_pages_ok_strip st lo len : brk_pages_ok (strip st) lo len = brk_pages_ok st lo len. Proof. reflexivity. Qed.  (* [comment removed for export] *)
Lemma get_head_strip st h : get_head (strip st) h = get_head st h. Proof. destruct h; reflexivity. Qed.
Lemma is_bouncing_strip sc st : is_bouncing sc (strip st) = is_bouncing sc st. Proof. reflexivity. Qed.
Lemma okay_to_free_strip st g : okay_to_free (strip st) g = okay_to_free st g. Proof. reflexivity. Qed.
Lemma slot_of_strip st g i : slot_of (strip st) g i = slot_of st g i. Proof. reflexivity. Qed.

Lemma strip_upd_ctx f st : upd_ctx f (strip st) = strip (upd_ctx f st). Proof. reflexivity. Qed.
Lemma strip_upd_meta m f st : upd_meta m f (strip st) = strip (upd_meta m f st). Proof. reflexivity. Qed.
Lemma strip_put_meta m r st : put_meta m r (strip st) = strip (put_meta m r st). Proof. reflexivity. Qed.
Lemma strip_set_active sc v st : set_active sc v (strip st) = strip (set_active sc v st). Proof. reflexivity. Qed.
Lemma strip_set_head h v st : set_head h v (strip st) = strip (set_head h v st). Proof. destruct h; reflexivity. Qed.
Lemma strip_set_usage sc v st : set_usage sc v (strip st) = strip (set_usage sc v st). Proof. reflexivity. Qed.
Lemma strip_set_bounce i v st : set_bounce i v (strip st) = strip (set_bounce i v st). Proof. reflexivity. Qed.
Lemma strip_set_areas a st : set_areas a (strip st) = strip (set_areas a st). Proof. reflexivity. Qed.
Lemma strip_put_group g m ai st : put_group g m ai (strip st) = strip (put_group g m ai st). Proof. reflexivity. Qed.
Lemma strip_set_group_active_idx g ai st : set_group_active_idx g ai (strip st) = strip (set_group_active_idx g ai st).
Proof. unfold set_group_active_idx. rewrite get_group_strip. destruct (get_group st g); reflexivity. Qed.
Lemma strip_del_group g st : del_group g (strip st) = strip (del_group g st). Proof. reflexivity. Qed.
Lemma strip_add_slots m p s c st : add_slots m p s c (strip st) = strip (add_slots m p s c st). Proof. reflexivity. Qed.
Lemma strip_del_slots p s c st : del_slots p s c (strip st) = strip (del_slots p s c st). Proof. reflexivity. Qed.
Lemma strip_drop_region rid st : drop_region rid (strip st) = strip (drop_region rid st).
Proof. unfold drop_region, strip; cbn. rewrite delete_empty. reflexivity. Qed.
Lemma strip_new_region k b l st :
  new_region k b l (strip st) = (strip (fst (new_region k b l st)), snd (new_region k b l st)).
Proof. reflexivity. Qed.
Lemma strip_upd_region rid f st : upd_region rid f (strip st) = strip (upd_region rid f st).
Proof. unfold upd_region. rewrite get_region_strip. destruct (get_region st rid); reflexivity. Qed.
Lemma strip_step_seq st : step_seq (strip st) = strip (step_seq st).
Proof. unfold step_seq. rewrite ctx_strip. destruct (c_seq (ctx st) =? 255); reflexivity. Qed.
Lemma strip_record_seq sc st : record_seq sc (strip st) = strip (record_seq sc st).
Proof. unfold record_seq. destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma strip_account_bounce sc st : account_bounce sc (strip st) = strip (account_bounce sc st).
Proof. unfold account_bounce. rewrite !unmap_seq_strip, !bounces_strip, !ctx_strip.
  destruct (sc_in_seq_range sc); [|reflexivity]. destruct (negb _ && _); [|reflexivity]. destruct (_ <? 100); reflexivity. Qed.
Lemma strip_decay_bounces sc st : decay_bounces sc (strip st) = strip (decay_bounces sc st).
Proof. unfold decay_bounces. rewrite !bounces_strip. destruct (_ && _); reflexivity. Qed.
Lemma strip_dequeue h m st : dequeue h m (strip st) = strip (dequeue h m st).
Proof.
  unfold dequeue. rewrite !get_meta_rec_strip.
  destruct (negb _); [|rewrite strip_set_head; reflexivity].
  destruct (m_prev _); destruct (m_next _); rewrite ?strip_upd_meta, ?get_head_strip;
  destruct (optr_eqb _ _); rewrite ?strip_set_head, ?strip_upd_meta; reflexivity.
Qed.

Hint Rewrite ctx_strip s_ctx_strip s_regions_strip s_metas_strip s_areas_strip s_groups_strip s_slots_strip
  s_next_rid_strip s_secret_strip s_reserved_strip active_strip usage_strip unmap_seq_strip bounces_strip
  get_meta_rec_strip get_group_strip group_active_idx_strip get_region_strip conc_strip live_ranges_strip brk_pages_ok_strip
  get_head_strip is_bouncing_strip okay_to_free_strip slot_of_strip
  strip_upd_ctx strip_upd_meta strip_put_meta strip_set_active strip_set_head strip_set_usage strip_set_bounce
  strip_set_areas strip_put_group strip_set_group_active_idx strip_del_group strip_add_slots strip_del_slots
  strip_drop_region strip_new_region strip_upd_region strip_step_seq strip_record_seq strip_account_bounce
  strip_decay_bounces strip_dequeue
  strip_strip strip_wr8 strip_wr16 strip_wr32 strip_havoc strip_set_tick strip_zero_hdrs strip_set_size strip_nest_layout strip_hdr_havoc
  : strip_rw.
(* [comment removed for export] *)
Hint Rewrite <- strip_upd_ctx strip_upd_meta strip_put_meta strip_set_active strip_set_head strip_set_usage strip_set_bounce
  strip_set_areas strip_put_group strip_set_group_active_idx strip_del_group strip_add_slots strip_del_slots
  strip_drop_region strip_upd_region strip_step_seq strip_record_seq strip_account_bounce
  strip_decay_bounces strip_dequeue : strip_in.
Hint Rewrite strip_strip strip_wr8 strip_wr16 strip_wr32 strip_havoc strip_set_tick strip_zero_hdrs strip_set_size
  strip_nest_layout strip_enframe_at strip_hdr_havoc : strip_in.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Global Set Keyed Unification.
Ltac srw := autorewrite with strip_rw.

(* [comment removed for export] *)
Ltac strip_in1 :=
  first
  [ rewrite strip_nest_layout | rewrite strip_hdr_havoc | rewrite strip_enframe_at | rewrite strip_zero_hdrs | rewrite strip_set_size
  | rewrite strip_havoc | rewrite strip_wr32 | rewrite strip_wr16 | rewrite strip_wr8 | rewrite strip_set_tick
  | rewrite strip_strip
  | rewrite <- strip_dequeue | rewrite <- strip_step_seq | rewrite <- strip_record_seq
  | rewrite <- strip_account_bounce | rewrite <- strip_decay_bounces | rewrite <- strip_drop_region
  | rewrite <- strip_del_slots | rewrite <- strip_add_slots | rewrite <- strip_del_group
  | rewrite <- strip_set_group_active_idx | rewrite <- strip_put_group | rewrite <- strip_upd_region
  | rewrite <- strip_set_head | rewrite <- strip_set_active | rewrite <- strip_set_usage | rewrite <- strip_set_bounce
  | rewrite <- strip_upd_meta | rewrite <- strip_put_meta | rewrite <- strip_set_areas | rewrite <- strip_upd_ctx ].
Ltac solve_eq := repeat strip_in1; reflexivity.
(* [comment removed for export] *)
Ltac use_hyp :=
  match goal with
  | H : _ |- strel _ _ _ =>
      with_strategy opaque [am_take am_carve am_finish am_after_brk alloc_meta ta_fin try_avail ag_tail
                            alloc_group alloc_slot malloc_small_ctrl malloc_core
                            nontrivial_free free_group free_tail free_hdr queue free_meta activate_group
                            enframe_read_off enframe_full]
        (eapply H); (try assumption); (try solve_eq)
  end.
(* [comment removed for export] *)
Ltac not_numeric T :=
  lazymatch T with Z => fail | bool => fail | N => fail | nat => fail | (Z * Z)%type => fail | _ => idtac end.
Ltac scrut x :=
  match x with
  | context [if ?c then ?a else _] => let T := type of a in not_numeric T; scrut c
  | context [match ?y with _ => _ end] => let T := type of y in (lazymatch T with bool => fail | _ => idtac end); scrut y
  | _ => destruct x eqn:?
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Hint Rewrite get_meta_rec_strip strip_decay_bounces strip_upd_meta strip_upd_ctx strip_set_active active_strip ctx_strip group_active_idx_strip strip_strip usage_strip strip_set_group_active_idx strip_del_slots strip_del_group strip_new_region strip_step_seq strip_dequeue conc_strip brk_pages_ok_strip strip_set_areas s_areas_strip live_ranges_strip strip_upd_region strip_set_usage strip_record_seq strip_put_group strip_drop_region strip_add_slots strip_set_head strip_account_bounce slot_of_strip s_slots_strip s_secret_strip okay_to_free_strip is_bouncing_strip get_head_strip : strip_rw5.
(* [comment removed for export] *)
Module SRWCHK.
  Import Ltac2.
  (* [comment removed for export] *)
  Ltac2 table () : (constr * (unit -> unit)) list := [
    (constr:(@get_meta_rec), (fun () => ltac1:(rewrite get_meta_rec_strip)));
    (constr:(@decay_bounces), (fun () => ltac1:(rewrite strip_decay_bounces)));
    (constr:(@upd_meta), (fun () => ltac1:(rewrite strip_upd_meta)));
    (constr:(@upd_ctx), (fun () => ltac1:(rewrite strip_upd_ctx)));
    (constr:(@set_active), (fun () => ltac1:(rewrite strip_set_active)));
    (constr:(@active), (fun () => ltac1:(rewrite active_strip)));
    (constr:(@ctx), (fun () => ltac1:(rewrite ctx_strip)));
    (constr:(@group_active_idx), (fun () => ltac1:(rewrite group_active_idx_strip)));
    (constr:(@strip), (fun () => ltac1:(rewrite strip_strip)));
    (constr:(@usage), (fun () => ltac1:(rewrite usage_strip)));
    (constr:(@set_group_active_idx), (fun () => ltac1:(rewrite strip_set_group_active_idx)));
    (constr:(@del_slots), (fun () => ltac1:(rewrite strip_del_slots)));
    (constr:(@del_group), (fun () => ltac1:(rewrite strip_del_group)));
    (constr:(@new_region), (fun () => ltac1:(rewrite strip_new_region)));
    (constr:(@step_seq), (fun () => ltac1:(rewrite strip_step_seq)));
    (constr:(@dequeue), (fun () => ltac1:(rewrite strip_dequeue)));
    (constr:(@conc), (fun () => ltac1:(rewrite conc_strip)));
    (constr:(@brk_pages_ok), (fun () => ltac1:(rewrite brk_pages_ok_strip)));
    (constr:(@set_areas), (fun () => ltac1:(rewrite strip_set_areas)));
    (constr:(@s_areas), (fun () => ltac1:(rewrite s_areas_strip)));
    (constr:(@live_ranges), (fun () => ltac1:(rewrite live_ranges_strip)));
    (constr:(@upd_region), (fun () => ltac1:(rewrite strip_upd_region)));
    (constr:(@set_usage), (fun () => ltac1:(rewrite strip_set_usage)));
    (constr:(@record_seq), (fun () => ltac1:(rewrite strip_record_seq)));
    (constr:(@put_group), (fun () => ltac1:(rewrite strip_put_group)));
    (constr:(@drop_region), (fun () => ltac1:(rewrite strip_drop_region)));
    (constr:(@add_slots), (fun () => ltac1:(rewrite strip_add_slots)));
    (constr:(@set_head), (fun () => ltac1:(rewrite strip_set_head)));
    (constr:(@account_bounce), (fun () => ltac1:(rewrite strip_account_bounce)));
    (constr:(@slot_of), (fun () => ltac1:(rewrite slot_of_strip)));
    (constr:(@s_slots), (fun () => ltac1:(rewrite s_slots_strip)));
    (constr:(@s_secret), (fun () => ltac1:(rewrite s_secret_strip)));
    (constr:(@okay_to_free), (fun () => ltac1:(rewrite okay_to_free_strip)));
    (constr:(@is_bouncing), (fun () => ltac1:(rewrite is_bouncing_strip)));
    (constr:(@get_head), (fun () => ltac1:(rewrite get_head_strip))) ].
  Ltac2 heads () : constr list := List.map (fun p => match p with (h, _) => h end) (table ()).
  Ltac2 is_strip_app (sc : constr) (a : constr) : bool :=
    match Constr.Unsafe.kind a with
    | Constr.Unsafe.App g _ => Constr.equal g sc
    | _ => false
    end.
  Ltac2 rec first_in (f : constr -> constr option) (args : constr array) (k : int) : constr option :=
    if Int.ge k (Array.length args) then None
    else match f (Array.get args k) with Some h => Some h | None => first_in f args (Int.add k 1) end.
  (* [comment removed for export] *)
  Ltac2 rec first_head (hs : constr list) (sc : constr) (c : constr) : constr option :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.App f args =>
        if (if Array.exist (is_strip_app sc) args
            then (if List.exist (fun h => Constr.equal f h) hs then Constr.Unsafe.is_closed c else false)
            else false)
        then Some f
        else (match first_head hs sc f with Some h => Some h | None => first_in (first_head hs sc) args 0 end)
    | Constr.Unsafe.Lambda _ body => first_head hs sc body
    | Constr.Unsafe.Prod b body =>
        (match first_head hs sc (Constr.Binder.type b) with Some h => Some h | None => first_head hs sc body end)
    | Constr.Unsafe.LetIn _ v body => (match first_head hs sc v with Some h => Some h | None => first_head hs sc body end)
    | Constr.Unsafe.Case _ _ _ scrut brs =>
        (match first_head hs sc scrut with Some h => Some h | None => first_in (first_head hs sc) brs 0 end)
    | Constr.Unsafe.Cast c' _ _ => first_head hs sc c'
    | _ => None
    end.
  Ltac2 check (b : constr) : unit :=
    match first_head (heads ()) constr:(@strip) b with Some _ => () | None => Control.zero (Tactic_failure None) end.
  (* [comment removed for export] *)
  Ltac2 ctrl_side () : constr :=
    match Constr.Unsafe.kind (Control.goal ()) with
    | Constr.Unsafe.App _ args => Array.get args (Int.sub (Array.length args) 1)
    | _ => Control.zero (Tactic_failure None)
    end.
  Ltac2 rec loop (n : int) : unit :=
    if Int.le n 0 then Control.zero (Tactic_failure None) else
    let tbl := table () in
    match first_head (heads ()) constr:(@strip) (ctrl_side ()) with
    | None => ()
    | Some h =>
        let t := List.find (fun p => match p with (h', _) => Constr.equal h' h end) tbl in
        (match t with (_, run) => run () end); loop (Int.sub n 1)
    end.
End SRWCHK.
Local Ltac srw_redex b := let f := ltac2:(x |- SRWCHK.check (Option.get (Ltac1.to_constr x))) in f b.
(* [comment removed for export] *)
Local Ltac srw_tgt := ltac2:(SRWCHK.loop 200).
Local Ltac srw ::= lazymatch goal with
  | |- strel ?RR ?A ?B =>
      tryif srw_redex B then (let a := fresh "FULL__" in set (a := A); first [ srw_tgt | autorewrite with strip_rw5 ]; unfold a; clear a) else idtac
  | |- _ => autorewrite with strip_rw5
  end.
(* [comment removed for export] *)
Local Ltac solve_eq ::= first [ solve [ reflexivity ] | repeat strip_in1; reflexivity ].
Local Ltac use_cand T :=
  lazymatch T with
  | forall _, _ => idtac
  | @KREL _ _ _ _ _ _ _ _ _ => idtac
  | @KREL0 _ _ _ _ _ _ _ _ => idtac
  | @BREL _ _ _ _ _ _ _ _ => idtac
  | _ => fail
  end.
Local Ltac use_hyp ::=
  match goal with
  | H : ?T |- strel _ _ _ =>
      use_cand T;
      with_strategy opaque [am_take am_carve am_finish am_after_brk alloc_meta ta_fin try_avail ag_tail
                            alloc_group alloc_slot malloc_small_ctrl malloc_core
                            nontrivial_free free_group free_tail free_hdr queue free_meta activate_group
                            enframe_read_off enframe_full]
        (eapply H); (try assumption); (try solve_eq)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CPS.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Context {R1 R2 : Type} (RR : O * R1 -> R2 -> Prop).
Local Notation KREL := (KREL pans pupd).
Local Notation KREL0 := (KREL0 pans pupd).
Local Notation BREL := (BREL pans pupd).
Local Notation prun := (prun pans pupd).

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

End CPS.

Section TOP.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Local Notation KREL := (KREL pans pupd).
Local Notation BREL := (BREL pans pupd).

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint follow {R} (t : M R) (ans : list Z) : option R :=
  match t, ans with
  | SRet r, _ => Some r
  | SVis (EUndef _) _, _ => None
  | SVis _ k, a :: ans' => follow (k a) ans'
  | SVis _ _, [] => None
  end.

(* [comment removed for export] *)
Inductive reach : mstate -> list aptr -> list cptr -> Prop :=
| reach_init secret res : reach (minit secret res) [] []
| reach_malloc st L C n o ans o' st' p cst c :
    reach st L C ->
    follow ((prun pans pupd) o (malloc st n)) ans = Some (o', (st', Some p)) ->
    follow (cmalloc (strip st) n) ans = Some (cst, Some c) ->
    reach st' (p :: L) (c :: C)
| reach_malloc_null st L C n o ans o' st' cst :
    reach st L C ->
    follow ((prun pans pupd) o (malloc st n)) ans = Some (o', (st', None)) ->
    follow (cmalloc (strip st) n) ans = Some (cst, None) ->
    reach st' L C
| reach_free st L C i p c o ans o' st' :
    reach st L C ->
    nth_error L i = Some p -> nth_error C i = Some c ->
    follow ((prun pans pupd) o (free st (Some p))) ans = Some (o', st') ->
    reach st' (delete i L) (delete i C)
| reach_free_null st L C o ans o' st' :
    reach st L C ->
    follow ((prun pans pupd) o (free st None)) ans = Some (o', st') ->
    reach st' L C.

(* [comment removed for export] *)

End TOP.



