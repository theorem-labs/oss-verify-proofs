(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Bool String.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VCert VState2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive skind : Type :=
| SK_fake (cid : Z) (flag : sym)
| SK_arg
| SK_flag (owner : sym)
| SK_shadow (of_ : sym).

Record srgn := mkSR {
  sr_base : sym ;
  sr_disp : Z ;
  sr_kind : skind ;
  sr_lo : Z ; sr_hi : Z ;
  sr_w : list (Z * Z) ;
  sr_cells : list (Z * (Z * lin)) ;
  sr_nul : list (Z * Z) ;                    (* [comment removed for export] *)
  sr_b8 : option sym
}.

Definition rkind_of (k : skind) : rkind :=
  match k with
  | SK_fake cid fl => RK_fake cid fl
  | SK_arg => RK_arg
  | SK_flag o => RK_flag o
  | SK_shadow s => RK_shadow s
  end.

Definition vregion_of (s : srgn) : vregion :=
  mkVR (sr_base s) (sr_disp s) (rkind_of (sr_kind s)) (sr_lo s) (sr_hi s) (sr_w s) (cm_of_list (sr_cells s)) (sr_nul s) (sr_b8 s).

(* [comment removed for export] *)
Record cstate2 := mkCS2 {
  c1 : cstate ;
  cs_rgn : list srgn ;                       (* [comment removed for export] *)
  cs_divdef : list (sym * (lin * Z)) ;
  cs_live : list sym                         (* [comment removed for export] *)
}.

Definition cstate2_of_v1 (cs : cstate) : cstate2 := mkCS2 cs [] [] [].

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition shadow_w (wst : list (Z * Z)) : list (Z * Z) :=
  match wst with [] => [] | r :: _ => [(fst r / 8, snd r / 8)] end.

Definition SHF (P : vparams2) (cells : cellmap) : vregion :=
  let fr := vp_frame (p1 P) in
  mkVR SP8 (vp_shoff P) (RK_shadow SP0) (- (fr / 8) - 8) 1 (shadow_w (vp_wstack (p1 P))) cells [] None.

Definition SHD (P : vparams2) : vregion :=
  mkVR DATA8 (vp_shoff P) (RK_shadow DATA) (-8) 0 [] [] [] None.     (* [comment removed for export] *)

Definition FSR : vregion :=
  mkVR FSB 0 RK_fs 0 88 [(0, 88)] [] [] (Some FS8).

Definition has_asan (P : vparams2) : bool :=
  match vp_fs P with Some _ => true | None => false end.

(* [comment removed for export] *)
Definition std_regions (P : vparams2) : list vregion :=
  if has_asan P then [SHD P; FSR] else [].

Definition load_regions (P : vparams2) (l : list srgn) : list vregion :=
  (map vregion_of l ++ std_regions P)%list.

Definition load_cstate2 (P : vparams2) (cs : cstate2) (pc : Z) (ctx : list Z) : vstate2 :=
  mkVS2 (load_cstate (c1 cs) pc ctx)
        (load_regions P (cs_rgn cs))
        (cs_live cs)
        (pm_of_list (cs_divdef cs))
        [].

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition skind_syms (k : skind) : list sym :=
  match k with SK_fake _ fl => [fl] | SK_arg => [] | SK_flag o => [o] | SK_shadow s => [s] end.

Definition srgn_below_b (s : srgn) (b : positive) : bool :=
  Pos.ltb (sr_base s) b
  && forallb (fun x => Pos.ltb x b) (skind_syms (sr_kind s))
  && match sr_b8 s with Some x => Pos.ltb x b | None => true end
  && forallb (fun c : Z * (Z * lin) => match c with (_, (_, e)) => lin_below e b end) (sr_cells s).

Definition srgn_wf (s : srgn) : bool :=
  Z.leb (sr_lo s) (sr_hi s)
  && forallb (fun c : Z * (Z * lin) => match c with (off, (w, _)) => Z.leb (sr_lo s) off && Z.ltb 0 w && Z.leb (off + w) (sr_hi s) end) (sr_cells s)
  && forallb (fun r : Z * Z => Z.leb (sr_lo s) (fst r) && Z.leb (snd r) (sr_hi s)) (sr_w s)
  && forallb (fun r : Z * Z => Z.leb (sr_lo s) (fst r) && Z.leb (fst r) (snd r) && Z.ltb (snd r) (sr_hi s)) (sr_nul s).

(* [comment removed for export] *)
Definition reserved_base (s : sym) : bool :=
  Pos.eqb s SP0 || Pos.eqb s DATA || Pos.eqb s SP8 || Pos.eqb s DATA8 || Pos.eqb s FSB || Pos.eqb s FS8.

Fixpoint bases_distinct (l : list sym) : bool :=
  match l with
  | [] => true
  | x :: t => negb (existsb (Pos.eqb x) t) && bases_distinct t
  end.

Definition is_fake (s : srgn) : bool := match sr_kind s with SK_fake _ _ => true | _ => false end.
Definition is_flagk (s : srgn) : bool := match sr_kind s with SK_flag _ => true | _ => false end.

(* [comment removed for export] *)
Definition skind_struct_ok (l : list srgn) (s : srgn) : bool :=
  match sr_kind s with
  | SK_fake cid fl =>
      Z.eqb (sr_lo s) 0 && Z.eqb (sr_hi s) (fake_size cid) && Z.leb 0 cid && Z.leb cid 4 && Z.eqb (sr_disp s) 0
      && Pos.leb FIRST_FRESH2 (sr_base s)
  | SK_flag owner =>
      Z.eqb (sr_lo s) 0 && Z.eqb (sr_hi s) 1 && Z.eqb (sr_disp s) 0
      && match sr_cells s with [] => true | _ => false end
      && existsb (fun t => Pos.eqb (sr_base t) owner
                          && match sr_kind t with SK_fake _ fl => Pos.eqb fl (sr_base s) | _ => false end) l
  | SK_shadow of_ =>
      (Pos.eqb of_ SP0 && Pos.eqb (sr_base s) SP8)
      || existsb (fun t => Pos.eqb (sr_base t) of_
                          && match sr_kind t with
                             | SK_fake _ _ => true
                             | SK_arg => match sr_w s with [] => true | _ => false end   (* [comment removed for export] *)
                             | _ => false end
                          && match sr_b8 t with Some b => Pos.eqb b (sr_base s) | None => false end) l
  | SK_arg => Pos.leb 19 (sr_base s) && Pos.leb (sr_base s) 26 && Z.eqb (sr_disp s) 0
              && match sr_b8 s with None => true | Some q => Pos.eqb q (Pos.add (sr_base s) 49) end
  end.

(* [comment removed for export] *)
Fixpoint live_matches (l1 : list sym) (l2 : list srgn) : bool :=
  match l2 with
  | [] => match l1 with [] => true | _ => false end
  | s :: t => if is_fake s then match l1 with x :: l1' => Pos.eqb x (sr_base s) && live_matches l1' t | [] => false end
              else live_matches l1 t
  end.

Definition cstate2_wf_b (cs : cstate2) : bool :=
  let b := cs_next (c1 cs) in
  cstate_wf_f (c1 cs)   (* [comment removed for export] *)
  && Pos.leb FIRST_FRESH2 b
  && forallb (fun s => srgn_below_b s b && srgn_wf s) (cs_rgn cs)
  && forallb (fun s => negb (reserved_base (sr_base s)) || match sr_kind s with SK_shadow o => Pos.eqb o SP0 && Pos.eqb (sr_base s) SP8 | _ => false end) (cs_rgn cs)
  && bases_distinct (map sr_base (cs_rgn cs))
  && forallb (fun d : sym * (lin * Z) => match d with (s, (x, m)) => Pos.ltb s b && lin_below x b && Z.ltb 0 m end) (cs_divdef cs)
  && forallb (fun s => Pos.ltb s b) (cs_live cs)
  && live_matches (cs_live cs) (cs_rgn cs)
  && forallb (skind_struct_ok (cs_rgn cs)) (cs_rgn cs).

Lemma cstate2_wf_parts cs :
  cstate2_wf_b cs = true ->
  let b := cs_next (c1 cs) in
  cstate_wf (c1 cs) = true
  /\ (FIRST_FRESH2 <= b)%positive
  /\ (forall s, In s (cs_rgn cs) -> srgn_below_b s b = true /\ srgn_wf s = true)
  /\ (forall s, In s (cs_rgn cs) -> reserved_base (sr_base s) = false \/ (exists o, sr_kind s = SK_shadow o /\ o = SP0 /\ sr_base s = SP8))
  /\ bases_distinct (map sr_base (cs_rgn cs)) = true
  /\ (forall q x m, In (q, (x, m)) (cs_divdef cs) -> (q < b)%positive /\ lin_below x b = true /\ 0 < m)
  /\ (forall x, In x (cs_live cs) -> (x < b)%positive)
  /\ live_matches (cs_live cs) (cs_rgn cs) = true
  /\ (forall s, In s (cs_rgn cs) -> skind_struct_ok (cs_rgn cs) s = true).
Proof.
  unfold cstate2_wf_b. intros H.
  apply andb_prop in H as [H H9]. apply andb_prop in H as [H H8]. apply andb_prop in H as [H H7]. apply andb_prop in H as [H H6].
  apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  cbn zeta. split; [apply cstate_wf_f_sound; exact H1|]. split; [apply Pos.leb_le; exact H2|]. split.
  { intros s Hs. rewrite forallb_forall in H3. specialize (H3 _ Hs). apply andb_prop in H3 as [A B]. auto. }
  split.
  { intros s Hs. rewrite forallb_forall in H4. specialize (H4 _ Hs). apply Bool.orb_prop in H4 as [A|A].
    - left. now destruct (reserved_base (sr_base s)).
    - right. destruct (sr_kind s); try discriminate. apply andb_prop in A as [A1 A2]. apply Pos.eqb_eq in A1. apply Pos.eqb_eq in A2. eauto. }
  split; [exact H5|]. split.
  { intros q x m Hin. rewrite forallb_forall in H6. specialize (H6 _ Hin). cbn beta iota in H6.
    apply andb_prop in H6 as [A C]. apply andb_prop in A as [A B]. apply Pos.ltb_lt in A. apply Z.ltb_lt in C. auto. }
  split.
  { intros x Hx. rewrite forallb_forall in H7. specialize (H7 _ Hx). apply Pos.ltb_lt in H7. exact H7. }
  split; [exact H8|].
  intros s Hs. rewrite forallb_forall in H9. exact (H9 _ Hs).
Qed.

(* [comment removed for export] *)
Definition cstate2_iface_b (cs : cstate2) : bool :=
  cstate2_wf_b cs
  && match cs_live cs with [] => true | _ => false end
  && forallb (fun s => negb (is_fake s) && negb (is_flagk s)) (cs_rgn cs).

(* [comment removed for export] *)
(* [comment removed for export] *)

Record vcut2 := mkCut2 {
  cut2_pc : Z ;
  cut2_ctx : list Z ;
  cut2_states : list cstate2 ;
  cut2_ranks : list lin ;
  cut2_tapes : list (list Z)                  
}.

Record vunit2 := mkUnit2 {
  u1 : vunit ;                               (* [comment removed for export] *)
  u2_pre : cstate2 ;
  u2_cuts : list vcut2 ;
  u2_exits : list cstate2 ;
  u2_wrgn : list (Z * (Z * Z)) ;             (* [comment removed for export] *)
  u2_fdepth : Z ;                            (* [comment removed for export] *)
  u2_tape : list Z                           (* [comment removed for export] *)
}.

Definition vcert2 := list vunit2.

(* [comment removed for export] *)
Definition vcut2_of_v1 (c : vcut) : vcut2 :=
  mkCut2 (cut_pc c) (cut_ctx c) (map cstate2_of_v1 (cut_states c)) (cut_ranks c) [].

Definition vunit2_of_v1 (U : vunit) : vunit2 :=
  mkUnit2 U (cstate2_of_v1 (u_pre U)) (map vcut2_of_v1 (u_cuts U)) (map cstate2_of_v1 (u_exits U)) [] 0 [].

Definition vcert2_of_v1 (C : vcert) : vcert2 := map vunit2_of_v1 C.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma load_cstate2_v1 P cs pc ctx : v1 (load_cstate2 P cs pc ctx) = load_cstate (c1 cs) pc ctx.
Proof. reflexivity. Qed.

Lemma load_cstate2_of_v1 P cs pc ctx :
  has_asan P = false ->
  load_cstate2 P (cstate2_of_v1 cs) pc ctx = of_v1 (load_cstate cs pc ctx).
Proof.
  intros H1. unfold load_cstate2, cstate2_of_v1, load_regions, std_regions, of_v1. cbn.
  rewrite H1. reflexivity.
Qed.
