(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib LiaTuning.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require SepLinT.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts DecCut. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit.
From Ltac2 Require Ltac2.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Inductive dj_cache (P : Prop) : Prop := DjC : P -> dj_cache P.
Lemma dj_cache_elim : forall P : Prop, dj_cache P -> P. Proof. intros P [p]; exact p. Qed.

Module RSC.
  Import Ltac2.
  Ltac2 keep_shape (ty : constr) : bool :=
    lazy_match! ty with
    | Z.of_nat (length _) = _ => true
    | length _ = _ => true
    | act_ok _ _ => true
    | (_ \/ _) => true
    | b_small _ = _ => true
    | dpure _ _ _ _ _ => true
    | _ => false
    end.
  Ltac2 slim () : unit :=
    let ids := List.map_filter (fun h => let (id, _, ty) := h in if keep_shape ty then Some id else None) (Control.hyps ()) in
    Std.keep ids.
  Ltac2 slim1 () : unit := Control.enter slim.
  (* [comment removed for export] *)
  Ltac2 rec mem_id (i : ident) (l : ident list) : bool :=
    match l with [] => false | x :: r => if Ident.equal i x then true else mem_id i r end.
  Ltac2 rec locals_of (acc : ident list) (t : constr) : ident list :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.Var id => if mem_id id acc then acc else (if zt_is_local id then id :: acc else acc)
    | Constr.Unsafe.App h args => Array.fold_left locals_of (locals_of acc h) args
    | Constr.Unsafe.Cast c _ _ => locals_of acc c
    | Constr.Unsafe.Prod b c => locals_of (locals_of acc (Constr.Binder.type b)) c
    | _ => acc
    end.
  Ltac2 rec mentions (vs : ident list) (t : constr) : bool :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.Var id => mem_id id vs
    | Constr.Unsafe.App h args => if mentions vs h then true else Array.exist (mentions vs) args
    | Constr.Unsafe.Cast c _ _ => mentions vs c
    | Constr.Unsafe.Prod b c => if mentions vs (Constr.Binder.type b) then true else mentions vs c
    | _ => false
    end.
  Ltac2 slim_rel () : unit :=
    let gv := locals_of [] (Control.goal ()) in
    let ids := List.map_filter (fun h => let (id, _, ty) := h in
                 if keep_shape ty then Some id
                 else if zt_plain_arith ty then (if mentions gv ty then Some id else None)
                 else None) (Control.hyps ()) in
    Std.keep ids.
  Ltac2 slim_rel1 () : unit := Control.enter slim_rel.
End RSC.
(* [comment removed for export] *)
Ltac revive_slim_ctx_fast := first [ ltac2:(RSC.slim1 ()) | revive_slim_ctx ].

Ltac simpl_arr_sizes_occ :=
  repeat match goal with
  | |- context [length (u32s _)] => rewrite !u32s_length
  | |- context [length (u64s _)] => rewrite !u64s_length
  | |- context [length (upd _ _ _)] => rewrite !upd_length
  | H : context [length (u32s _)] |- _ => rewrite !u32s_length in H
  | H : context [length (u64s _)] |- _ => rewrite !u64s_length in H
  | H : context [length (upd _ _ _)] |- _ => rewrite !upd_length in H
  end.
(* [comment removed for export] *)
Lemma dj_sb : forall b a n l h : Z, ((a + n <=? l) || (h <=? a))%bool = true -> (b + a + n <= b + l \/ b + h <= b + a)%Z.
Proof. intros b a n l h H. apply Bool.orb_true_iff in H. destruct H as [H|H]; apply Z.leb_le in H; [left|right]; lia. Qed.
Lemma dj_sb_A0 : forall b n l h : Z, ((n <=? l) || (h <=? 0))%bool = true -> (b + n <= b + l \/ b + h <= b)%Z.
Proof. intros b n l h H. apply Bool.orb_true_iff in H. destruct H as [H|H]; apply Z.leb_le in H; [left|right]; lia. Qed.
Lemma dj_sb_l0 : forall b a n h : Z, ((a + n <=? 0) || (h <=? a))%bool = true -> (b + a + n <= b \/ b + h <= b + a)%Z.
Proof. intros b a n h H. apply Bool.orb_true_iff in H. destruct H as [H|H]; apply Z.leb_le in H; [left|right]; lia. Qed.
Lemma dj_sb_00 : forall b n h : Z, ((n <=? 0) || (h <=? 0))%bool = true -> (b + n <= b \/ b + h <= b)%Z.
Proof. intros b n h H. apply Bool.orb_true_iff in H. destruct H as [H|H]; apply Z.leb_le in H; [left|right]; lia. Qed.
(* [comment removed for export] *)
Ltac dj_pos_lit p := lazymatch p with xH => idtac | xO ?q => dj_pos_lit q | xI ?q => dj_pos_lit q end.
Ltac dj_closedZ t :=
  lazymatch t with
  | Z0 => idtac
  | Zpos ?p => dj_pos_lit p
  | Zneg ?p => dj_pos_lit p
  | Z.add ?x ?y => dj_closedZ x; dj_closedZ y
  | Z.sub ?x ?y => dj_closedZ x; dj_closedZ y
  | Z.mul ?x ?y => dj_closedZ x; dj_closedZ y
  end.
Ltac dj_sb_true t := let v := eval lazy in t in lazymatch v with true => idtac end.
Ltac dj_sb_conj :=
  lazymatch goal with
  | |- (?b + ?a + ?n <= ?b + ?l \/ ?b + ?h <= ?b + ?a)%Z =>
      dj_closedZ a; dj_closedZ n; dj_closedZ l; dj_closedZ h;
      dj_sb_true ((a + n <=? l) || (h <=? a))%bool; apply (dj_sb b a n l h); reflexivity
  | |- (?b + ?n <= ?b + ?l \/ ?b + ?h <= ?b)%Z =>
      dj_closedZ n; dj_closedZ l; dj_closedZ h;
      dj_sb_true ((n <=? l) || (h <=? 0))%bool; apply (dj_sb_A0 b n l h); reflexivity
  | |- (?b + ?a + ?n <= ?b \/ ?b + ?h <= ?b + ?a)%Z =>
      dj_closedZ a; dj_closedZ n; dj_closedZ h;
      dj_sb_true ((a + n <=? 0) || (h <=? a))%bool; apply (dj_sb_l0 b a n h); reflexivity
  | |- (?b + ?n <= ?b \/ ?b + ?h <= ?b)%Z =>
      dj_closedZ n; dj_closedZ h;
      dj_sb_true ((n <=? 0) || (h <=? 0))%bool; apply (dj_sb_00 b n h); reflexivity
  end.
(* [comment removed for export] *)
Ltac dj_sb_all :=
  lazymatch goal with
  | |- _ /\ _ => split; [ dj_sb_conj | dj_sb_all ]
  | |- True => exact I
  | |- _ => dj_sb_conj
  end.
(* [comment removed for export] *)
Ltac dj_conjs :=
  lazymatch goal with
  | |- _ /\ _ => split; [ first [ dj_sb_conj | lia | exact I ] | dj_conjs ]
  | |- True => exact I
  | |- _ => first [ dj_sb_conj | lia ]
  end.
(* [comment removed for export] *)
Ltac revive_dj_prep AOK SEPF :=
  pose proof alloc_ceiling_range;
  lin_pose15 (alin_core _ _ AOK);
  try match goal with SM : b_small _ = _ |- _ => first [ pose proof (alin_ll _ _ AOK SM) | pose proof (alin_tt _ _ AOK SM) ] end;
  try match goal with DP : dpure _ _ _ _ _ |- _ => pose proof (dpure_cf_len _ _ _ _ _ DP); clear DP end;
  pose proof SEPF.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac dj_len_norm :=
  repeat match goal with
  | |- context [Z.of_nat (@length ?T ?X)] =>
      first [ lazymatch goal with E : Z.of_nat (@length T X) = _ |- _ => rewrite E end
            | lazymatch goal with E : @length T X = _ |- _ => rewrite E end ]
  end.
Ltac dj_len_db := first [ progress (autorewrite with dj_len) | idtac ].
(* [comment removed for export] *)
Inductive dj_tried (P : Prop) : Prop := DjTried.
Ltac dj_blk_unbox :=
  repeat match goal with
  | D : dj_cache (?x + 64144 <= _ \/ _ <= ?x)%Z |- _ => pose proof (dj_cache_elim _ D); clear D
  end.
Ltac dj_seplin SEPF :=
  lazymatch goal with |- context [@length _ _] => dj_len_norm; dj_len_db | _ => idtac end;
  dj_blk_unbox;
  pose proof SEPF;
  SepLinT.sl_tslia ltac:(idtac; lia).
Ltac revive_dj_slim_new AOK SEPF :=
  cbn [disjoint_from];
  first
  [ solve [ dj_seplin SEPF ]
  | simpl_sizes;
    first
  [ solve [ dj_sb_all ]
  | solve [ revive_slim_ctx_fast; revive_dj_prep AOK SEPF; simpl_arr_sizes_occ; slia ]
  | solve [ first [ ltac2:(RSC.slim_rel1 ()) | fail ]; revive_dj_prep AOK SEPF; simpl_arr_sizes_occ; first [ slia | dj_conjs ] ] ] ].

(* [comment removed for export] *)
Ltac revive_old H MUL WML AOK :=
  unfold hidden in H;
  lazymatch type of MUL with munch ?W ?me ?m' =>
  lazymatch type of H with
  | rw_cells ?segs me ?A ?cs =>
      apply (rw_cells_transport segs W me m' A cs) in H; [ | exact MUL | exact WML
        | first [ revive_dj_slim AOK (act_img_s _ _ AOK)
                | let Y := fresh "IMGs" in pose proof (act_img_s _ _ AOK) as Y; cbn [disjoint_from]; simpl_sizes; slia ] ]
  | u32arr ?segs me ?A ?ws =>
      apply (u32arr_transport segs W me m' A ws) in H; [ | exact MUL | exact WML
        | first [ revive_dj_slim AOK (act_img_s _ _ AOK)
                | let Y := fresh "IMGs" in pose proof (act_img_s _ _ AOK) as Y; cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ] ]
  | u8arr ?segs me ?A ?bs =>
      apply (u8arr_transport segs W me m' A bs) in H; [ | exact MUL | exact WML
        | first [ revive_dj_slim AOK (act_img_s _ _ AOK)
                | let Y := fresh "IMGs" in pose proof (act_img_s _ _ AOK) as Y; cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ] ]
  | bytes_at ?segs me ?A ?bs =>
      apply (bytes_at_transport segs W me m' A bs) in H; [ | exact MUL
        | first [ revive_dj_slim AOK (act_sep_s_src _ _ AOK)
                | let Y := fresh "SEPsrc" in pose proof (act_sep_s_src _ _ AOK) as Y; cbn [disjoint_from]; simpl_sizes; slia ] ]
  | drest_at ?segs me ?S ?r =>
      apply (drest_transport segs W me m' S r) in H; [ | exact MUL | exact WML
        | first [ revive_dj_slim AOK I | cbn [disjoint_from]; slia ]
        | first [ revive_dj_slim AOK I | cbn [disjoint_from]; slia ]
        | first [ revive_dj_slim AOK I | cbn [disjoint_from]; slia ] ]
  | blk_at ?segs me ?cx ?k =>
      apply (blk_at_transport segs W me m' cx k) in H;
      [ | exact MUL | exact WML
        | let E := fresh "E" in
          intros ? ? [(E & -> & ->)|(E & [(-> & ->)|(-> & ->)])];
          [ pose proof (act_tt_s _ _ AOK E) as (? & ?)
          | cps_pose (act_ll_s _ _ AOK E) as (? & ? & ?)
          | cps_pose (act_ll_s _ _ AOK E) as (? & ? & ?) ];
          first [ revive_dj_slim AOK I | cbn [disjoint_from]; slia ] ]
  end end.

(* [comment removed for export] *)
Ltac dj_get P solver k :=
  lazymatch goal with
  | D : dj_cache P |- _ => k D
  | _ => let D := fresh "DJc" in
         assert (D : dj_cache P) by (apply DjC; solver);
         k D
  end.
Ltac dj_cells_n cs :=
  let n0 := eval cbv [cells_size csize Nat.add] in (cells_size cs) in
  lazymatch n0 with
  | context [cells_size] => constr:(Z.of_nat (cells_size cs))
  | context [csize] => constr:(Z.of_nat (cells_size cs))
  | _ => let n := eval cbv in (Z.of_nat n0) in n
  end.
(* [comment removed for export] *)
Ltac revive_new H MUL WML AOK :=
  unfold hidden in H;
  lazymatch type of MUL with munch ?W ?me ?m' =>
  lazymatch type of H with
  | rw_cells ?segs me ?A ?cs =>
      let n := dj_cells_n cs in
      dj_get (disjoint_from W A n)
        ltac:(first [ revive_dj_slim_new AOK (act_img_s _ _ AOK)
                    | let Y := fresh "IMGs" in pose proof (act_img_s _ _ AOK) as Y; cbn [disjoint_from]; simpl_sizes; slia
                    | revive_dj_slim AOK (act_img_s _ _ AOK) ])
        ltac:(fun D => apply (rw_cells_transport segs W me m' A cs) in H; [ | exact MUL | exact WML | exact (dj_cache_elim _ D) ])
  | u32arr ?segs me ?A ?ws =>
      dj_get (disjoint_from W A (4 * Z.of_nat (length ws)))
        ltac:(first [ revive_dj_slim_new AOK (act_img_s _ _ AOK)
                    | let Y := fresh "IMGs" in pose proof (act_img_s _ _ AOK) as Y; cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia
                    | revive_dj_slim AOK (act_img_s _ _ AOK) ])
        ltac:(fun D => apply (u32arr_transport segs W me m' A ws) in H; [ | exact MUL | exact WML | exact (dj_cache_elim _ D) ])
  | u8arr ?segs me ?A ?bs =>
      dj_get (disjoint_from W A (Z.of_nat (length bs)))
        ltac:(first [ revive_dj_slim_new AOK (act_img_s _ _ AOK)
                    | let Y := fresh "IMGs" in pose proof (act_img_s _ _ AOK) as Y; cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia
                    | revive_dj_slim AOK (act_img_s _ _ AOK) ])
        ltac:(fun D => apply (u8arr_transport segs W me m' A bs) in H; [ | exact MUL | exact WML | exact (dj_cache_elim _ D) ])
  | bytes_at ?segs me ?A ?bs =>
      dj_get (disjoint_from W A (Z.of_nat (length bs)))
        ltac:(first [ revive_dj_slim_new AOK (act_sep_s_src _ _ AOK)
                    | let Y := fresh "SEPsrc" in pose proof (act_sep_s_src _ _ AOK) as Y; cbn [disjoint_from]; simpl_sizes; slia
                    | revive_dj_slim AOK (act_sep_s_src _ _ AOK) ])
        ltac:(fun D => apply (bytes_at_transport segs W me m' A bs) in H; [ | exact MUL | exact (dj_cache_elim _ D) ])
  | drest_at ?segs me ?S ?r =>
      dj_get (disjoint_from W (S + 68) (4 * 256)) ltac:(first [ revive_dj_slim_new AOK I | cbn [disjoint_from]; slia | revive_dj_slim AOK I ]) ltac:(fun D1 =>
      dj_get (disjoint_from W (S + 2124) 1028) ltac:(first [ revive_dj_slim_new AOK I | cbn [disjoint_from]; slia | revive_dj_slim AOK I ]) ltac:(fun D2 =>
      dj_get (disjoint_from W (S + 3196) 60840) ltac:(first [ revive_dj_slim_new AOK I | cbn [disjoint_from]; slia | revive_dj_slim AOK I ]) ltac:(fun D3 =>
        apply (drest_transport segs W me m' S r) in H; [ | exact MUL | exact WML | exact (dj_cache_elim _ D1) | exact (dj_cache_elim _ D2) | exact (dj_cache_elim _ D3) ])))
  | blk_at ?segs me ?cx ?k =>
      dj_get (forall A n, blk_range cx A n -> disjoint_from W A n)
        ltac:(let E := fresh "E" in
              intros ? ? [(E & -> & ->)|(E & [(-> & ->)|(-> & ->)])];
              [ pose proof (act_tt_s _ _ AOK E) as (? & ?)
              | cps_pose (act_ll_s _ _ AOK E) as (? & ? & ?)
              | cps_pose (act_ll_s _ _ AOK E) as (? & ? & ?) ];
              first [ revive_dj_slim_new AOK I | cbn [disjoint_from]; slia | revive_dj_slim AOK I ])
        ltac:(fun D => apply (blk_at_transport segs W me m' cx k) in H; [ | exact MUL | exact WML | exact (dj_cache_elim _ D) ])
  end end.
Ltac dj_stack_ivl hi := lazymatch hi with bv_unsigned (a_sp _) => idtac | (bv_unsigned (a_sp _) + _)%Z => idtac end.
Ltac dj_blk_one S lo hi AOK :=
  tryif dj_stack_ivl hi then
  let P := constr:((S + 64144 <= lo \/ hi <= S)%Z) in
  lazymatch goal with
  | _ : dj_cache P |- _ => idtac
  | _ : dj_tried P |- _ => idtac
  | _ => first [ let D := fresh "DJb" in
                 assert (D : dj_cache P) by (apply DjC; first [ solve [ SepLinT.sl_tslia ltac:(idtac; lia) ]
                                                             | solve [ revive_slim_ctx_fast; revive_dj_prep AOK I; slia ] ])
               | let D := fresh "DJt" in assert (D : dj_tried P) by (exact (DjTried P)) ]
  end
  else idtac.
Ltac dj_blk_ivls S W AOK :=
  lazymatch W with
  | (?lo, ?hi) :: ?W' => dj_blk_one S lo hi AOK; dj_blk_ivls S W' AOK
  | _ => idtac
  end.
Ltac dj_blk_prefill MUL AOK :=
  lazymatch type of MUL with munch ?W ?me ?m' =>
  lazymatch type of AOK with act_ok _ ?A => dj_blk_ivls constr:(b_s (a_cx A)) W AOK end end.
Ltac revive_cached H MUL WML AOK :=
  first [ first [ dj_blk_prefill MUL AOK | idtac ]; revive_new H MUL WML AOK | revive_old H MUL WML AOK ].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac dpure_red T :=
  let T := eval unfold dpure in T in
  let T := eval cbv zeta in T in
  let T := eval cbn [dv_h dv_nbu dv_cf dv_d dv_j1 dv_snb dv_j2 dv_r dv_b dv_k] in T in
  let T := eval unfold dsh_wf, bzs_wf, w1_inv14, w1_view, bupd, bfields in T in
  let T := eval cbn [sh_strm sh_state sh_soch sh_p1 sh_solen sh_brand sh_p2 sh_rNToGo sh_rTPos sh_bsBuff sh_bsLive sh_n sh_small sh_p3
         sh_cbn sh_verb sh_origPtr sh_tPos sh_k0 sm_tt sm_ll16 sm_ll4 sm_sbcrc sm_sccrc sm_cbcrc sm_cccrc sm_nInUse
         bs_src bs_len bs_ai bs_til bs_tih bs_q1 bs_dst bs_dlen bs_av bs_tol bs_toh bs_q2 bs_S bs_bzalloc bs_bzfree bs_opaque] in T in
  T.
(* [comment removed for export] *)
Ltac curry_conj T P :=
  lazymatch T with
  | ?A /\ ?B => let r := curry_conj B P in curry_conj A r
  | _ => constr:(T -> P)
  end.

Section DpureF.
  Context {ACEIL__ : ACeil}.
  Variables (cx : bctx) (h0 : dsh) (b0 : bzs) (payload : list byte).
  Variables (x1 x2 : Z) (x3 : byte) (x4 : list byte) (x5 : Z) (x6 : byte) (x7 : list byte) (x8 x9 x10 x11 x12 : Z) (x13 : byte)
            (x14 : list byte) (x15 x16 x17 : Z) (x18 x19 : word).
  Variables (nbu : Z) (cf : list word) (d : dsm) (j1 : list byte) (snb : Z) (j2 : list byte) (r : drest).
  Variables (z1 z2 z3 : Z) (z4 z5 : word) (z6 : list byte) (z7 z8 z9 : Z) (z10 z11 : word) (z12 : list byte) (z13 : Z)
            (z14 z15 z16 : word) (k : blk).
  Notation VF := (DV (DSH x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19) nbu cf d j1 snb j2 r
                     (BZS z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16) k).

  (* [comment removed for export] *)
  Lemma dpure_elimF : forall P : Prop, dpure cx h0 b0 payload VF ->
    ltac:(let T := dpure_red (dpure cx h0 b0 payload VF) in let C := curry_conj T P in exact C) -> P.
  Proof.
    intros P DP K. unfold dpure in DP; cbv zeta in DP.
    cbn [dv_h dv_nbu dv_cf dv_d dv_j1 dv_snb dv_j2 dv_r dv_b dv_k] in DP.
    unfold dsh_wf, bzs_wf, w1_inv14, w1_view, bupd, bfields in DP.
    cbn [sh_strm sh_state sh_soch sh_p1 sh_solen sh_brand sh_p2 sh_rNToGo sh_rTPos sh_bsBuff sh_bsLive sh_n sh_small sh_p3
         sh_cbn sh_verb sh_origPtr sh_tPos sh_k0 sm_tt sm_ll16 sm_ll4 sm_sbcrc sm_sccrc sm_cbcrc sm_cccrc sm_nInUse
         bs_src bs_len bs_ai bs_til bs_tih bs_q1 bs_dst bs_dlen bs_av bs_tol bs_toh bs_q2 bs_S bs_bzalloc bs_bzfree bs_opaque] in DP.
    decompose [and] DP. apply K; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma dpure_introF :
    ltac:(let T := dpure_red (dpure cx h0 b0 payload VF) in let C := curry_conj T (dpure cx h0 b0 payload VF) in exact C).
  Proof.
    intros. unfold dpure; cbv zeta.
    cbn [dv_h dv_nbu dv_cf dv_d dv_j1 dv_snb dv_j2 dv_r dv_b dv_k].
    unfold dsh_wf, bzs_wf, w1_inv14, w1_view, bupd, bfields.
    cbn [sh_strm sh_state sh_soch sh_p1 sh_solen sh_brand sh_p2 sh_rNToGo sh_rTPos sh_bsBuff sh_bsLive sh_n sh_small sh_p3
         sh_cbn sh_verb sh_origPtr sh_tPos sh_k0 sm_tt sm_ll16 sm_ll4 sm_sbcrc sm_sccrc sm_cbcrc sm_cccrc sm_nInUse
         bs_src bs_len bs_ai bs_til bs_tih bs_q1 bs_dst bs_dlen bs_av bs_tol bs_toh bs_q2 bs_S bs_bzalloc bs_bzfree bs_opaque].
    repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.
End DpureF.

Section DpureV.
  Context {ACEIL__ : ACeil}.
  Variables (cx : bctx) (h0 : dsh) (b0 : bzs) (payload : list byte) (v : dv).
  (* [comment removed for export] *)
  Lemma dpure_elimV : forall P : Prop, dpure cx h0 b0 payload v ->
    ltac:(let T := dpure_red (dpure cx h0 b0 payload v) in let C := curry_conj T P in exact C) -> P.
  Proof.
    intros P DP K. unfold dpure in DP; cbv zeta in DP.
    unfold dsh_wf, bzs_wf, w1_inv14, w1_view, bupd, bfields in DP.
    decompose [and] DP. apply K; assumption.
  Qed.
End DpureV.

(* [comment removed for export] *)
Ltac dpure_clear_natlen := repeat match goal with H : @eq nat (@length _ _) _ |- _ => clear H end.
Ltac dpure_leaf :=
  first [ assumption | reflexivity
        | lazymatch goal with |- @eq nat _ _ => fail | |- _ => first [ dpure_clear_natlen; lia | lia ] end
        | congruence ].
Ltac dpure_from_new DP :=
  lazymatch type of DP with dpure _ _ _ _ _ =>
    first [ apply (dpure_elimF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DP)
          | apply (dpure_elimV _ _ _ _ _ _ DP) ];
    intros;
    apply dpure_introF; dpure_leaf
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac dpure_from_old DP :=
  lazymatch type of DP with dpure _ _ _ _ _ =>
    let X := fresh "DPX" in pose proof DP as X; unfold dpure in X; cbv zeta in X;
    cbn [dv_h dv_nbu dv_cf dv_d dv_j1 dv_snb dv_j2 dv_r dv_b dv_k] in X;
    unfold dsh_wf, bzs_wf, w1_inv14, w1_view, bupd, bfields in X;
    cbn [sh_strm sh_state sh_soch sh_p1 sh_solen sh_brand sh_p2 sh_rNToGo sh_rTPos sh_bsBuff sh_bsLive sh_n sh_small sh_p3
         sh_cbn sh_verb sh_origPtr sh_tPos sh_k0 sm_tt sm_ll16 sm_ll4 sm_sbcrc sm_sccrc sm_cbcrc sm_cccrc sm_nInUse
         bs_src bs_len bs_ai bs_til bs_tih bs_q1 bs_dst bs_dlen bs_av bs_tol bs_toh bs_q2 bs_S bs_bzalloc bs_bzfree bs_opaque] in X;
    decompose [and] X; clear X;
    unfold dpure; cbv zeta;
    cbn [dv_h dv_nbu dv_cf dv_d dv_j1 dv_snb dv_j2 dv_r dv_b dv_k];
    unfold dsh_wf, bzs_wf, w1_inv14, w1_view, bupd, bfields;
    cbn [sh_strm sh_state sh_soch sh_p1 sh_solen sh_brand sh_p2 sh_rNToGo sh_rTPos sh_bsBuff sh_bsLive sh_n sh_small sh_p3
         sh_cbn sh_verb sh_origPtr sh_tPos sh_k0 sm_tt sm_ll16 sm_ll4 sm_sbcrc sm_sccrc sm_cbcrc sm_cccrc sm_nInUse
         bs_src bs_len bs_ai bs_til bs_tih bs_q1 bs_dst bs_dlen bs_av bs_tol bs_toh bs_q2 bs_S bs_bzalloc bs_bzfree bs_opaque];
    repeat match goal with |- _ /\ _ => split end;
    first [ assumption | reflexivity | lia | congruence | idtac ]
  end.
Ltac dpure_from_fast DP := first [ solve [ dpure_from_new DP ] | dpure_from_old DP ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac open_dmem_red DM :=
  unfold dmem in DM;
  cbn [dv_h dv_nbu dv_cf dv_d dv_j1 dv_snb dv_j2 dv_r dv_b dv_k bupd
       sh_strm sh_state sh_soch sh_p1 sh_solen sh_brand sh_p2 sh_rNToGo sh_rTPos sh_bsBuff sh_bsLive sh_n sh_small sh_p3
       sh_cbn sh_verb sh_origPtr sh_tPos sh_k0 sm_tt sm_ll16 sm_ll4 sm_sbcrc sm_sccrc sm_cbcrc sm_cccrc sm_nInUse
       bs_src bs_len bs_ai bs_til bs_tih bs_q1 bs_dst bs_dlen bs_av bs_tol bs_toh bs_q2 bs_S bs_bzalloc bs_bzfree bs_opaque] in DM;
  cps_destruct DM as (HD & NBU & CF & MIDc & SAV & DR & STRM & BLK & PAY & GOT & SEV & RN).
