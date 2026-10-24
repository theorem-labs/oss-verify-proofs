(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac.
From Ltac2 Require Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sf_hide (P : Prop) := P.

Module SF2.
  Import Ltac2.
  (* [comment removed for export] *)
  Ltac2 rec plain_arith (neg : bool) (t : constr) : bool :=
    lazy_match! t with
    | Z.le _ _ => true | Z.lt _ _ => true | Z.ge _ _ => true | Z.gt _ _ => true
    | @eq _ _ _ => true
    | le _ _ => true | lt _ _ => true | ge _ _ => true | gt _ _ => true
    | N.le _ _ => true | N.lt _ _ => true | Z.divide _ _ => true
    | ?a /\ ?b => Bool.and (plain_arith neg a) (plain_arith neg b)
    | True => true | False => true
    | not ?a => Bool.and neg (plain_arith false a)
    | ?a -> False => Bool.and neg (plain_arith false a)
    | _ => false
    end.
  (* [comment removed for export] *)
  Ltac2 rec arith_logic (t : constr) : bool :=
    lazy_match! t with
    | ?a /\ ?b => Bool.and (arith_logic a) (arith_logic b)
    | ?a \/ ?b => Bool.and (arith_logic a) (arith_logic b)
    | ?a <-> ?b => Bool.and (arith_logic a) (arith_logic b)
    | not ?a => arith_logic a
    | ?a -> ?b => Bool.and (arith_logic a) (arith_logic b)
    | _ => plain_arith false t
    end.
  (* [comment removed for export] *)
  Ltac2 rec vars_of (acc : ident list) (c : constr) : ident list :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.Var id => id :: acc
    | Constr.Unsafe.App f args => Array.fold_left vars_of (vars_of acc f) args
    | Constr.Unsafe.Prod b body => vars_of (vars_of acc (Constr.Binder.type b)) body
    | Constr.Unsafe.Lambda b body => vars_of (vars_of acc (Constr.Binder.type b)) body
    | Constr.Unsafe.LetIn b v body => vars_of (vars_of (vars_of acc (Constr.Binder.type b)) v) body
    | Constr.Unsafe.Cast c _ _ => vars_of acc c
    | _ => acc
    end.
  Ltac2 rec meets (xs : ident list) (ys : ident list) : bool :=
    match xs with
    | [] => false
    | x :: xs' => if List.exist (Ident.equal x) ys then true else meets xs' ys
    end.
  (* [comment removed for export] *)
  Ltac2 bad_heads () : constr list :=
    [constr:(Z.to_nat); constr:(Z.min); constr:(Z.max); constr:(Z.abs); constr:(Nat.sub); constr:(Nat.min);
     constr:(Nat.max); constr:(Z.div); constr:(Z.modulo); constr:(Z.quot); constr:(Z.rem); constr:(Nat.div);
     constr:(Nat.modulo); constr:(Z.pow_pos); constr:(Z.sgn)].
  Ltac2 rec clean (bad : constr list) (c : constr) : bool :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.App f args =>
        if List.exist (Constr.equal f) bad then false
        else if clean bad f then Array.fold_left (fun b a => if b then clean bad a else false) true args else false
    | Constr.Unsafe.Constant _ _ => if List.exist (Constr.equal c) bad then false else true
    | Constr.Unsafe.Prod b body => if clean bad (Constr.Binder.type b) then clean bad body else false
    | Constr.Unsafe.Lambda _ _ => false
    | Constr.Unsafe.Case _ _ _ _ _ => false
    | Constr.Unsafe.LetIn _ _ _ => false
    | _ => true
    end.
  (* [comment removed for export] *)
  Ltac2 prune_with (keep : constr -> bool) : unit :=
    let hs := Control.hyps () in
    let ids := List.map_filter (fun h => let (id, body, ty) := h in
                  match body with
                  | Some _ => None
                  | None => if arith_logic ty then (if keep ty then None else Some id) else None
                  end) hs in
    match ids with [] => () | _ :: _ => Std.clear ids end.
  (* [comment removed for export] *)
  Ltac2 prune_plain () : unit := prune_with (fun ty => plain_arith false ty).
  (* [comment removed for export] *)
  Ltac2 prune_clean () : unit :=
    let bad := bad_heads () in prune_with (fun ty => if plain_arith false ty then clean bad ty else false).
  (* [comment removed for export] *)
  Ltac2 prune_rel () : unit :=
    let bad := bad_heads () in
    let gv := vars_of [] (Control.goal ()) in
    prune_with (fun ty => if plain_arith false ty then clean bad ty
                          else if plain_arith true ty then (if meets (vars_of [] ty) gv then clean bad ty else false)
                          else false).
  Ltac2 prune_plain1 () : unit := Control.enter prune_plain.
  Ltac2 prune_clean1 () : unit := Control.enter prune_clean.
  Ltac2 prune_neg () : unit := Control.enter prune_rel.
  Ltac zify_prune_plain := ltac2:(prune_plain1 ()).
  Ltac zify_prune_clean := ltac2:(prune_clean1 ()).
  Ltac zify_prune_neg := ltac2:(prune_neg ()).
  (* [comment removed for export] *)
  Ltac2 hide_poison () : unit :=
    let bad := bad_heads () in
    List.iter (fun h => let (id, body, ty) := h in
      match body with
      | Some _ => ()
      | None =>
          if arith_logic ty then
            (if (if plain_arith false ty then clean bad ty else false) then ()
             else let c := Control.hyp id in
                  ltac1:(c |- lazymatch type of c with ?T => change T with (sf_hide T) in c end) (Ltac1.of_constr c))
          else ()
      end) (Control.hyps ()).
  Ltac2 hide_poison1 () : unit := Control.enter hide_poison.
  Ltac sf_hide_poison := ltac2:(hide_poison1 ()).
End SF2.
Ltac zify_prune_neg := SF2.zify_prune_neg.
Ltac sf_hide_poison := SF2.sf_hide_poison.
Ltac sf_unhide := repeat match goal with H : sf_hide _ |- _ => unfold sf_hide in H end.
Ltac zify_prune_plain := SF2.zify_prune_plain.
Ltac zify_prune_clean := SF2.zify_prune_clean.
Ltac lia3 := first [ zify_prune_plain; Zify.zify; xlia zchecker
                   | zify_prune_neg; Zify.zify; xlia zchecker
                   | Zify.zify; xlia zchecker ].

(* [comment removed for export] *)
Ltac tlia := first [ Zify.zify; xlia zchecker
                   | sf_unhide;
                     first [ zify_prune_neg; Zify.zify; xlia zchecker
                           | zify_prune_plain; Zify.zify; xlia zchecker
                           | Zify.zify; xlia zchecker ] ].
Ltac tslia := first [ exact I | tlia | split; [ tlia | exact I ] ].

Section WithSegs.
Variable segs : list Segment.

Lemma bytes_at_write_other_n : forall m a bs c cs (n : Z),
  Z.of_nat (length bs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  bytes_at segs m c cs ->
  (c + Z.of_nat (length cs) <= a \/ a + n <= c)%Z ->
  bytes_at segs (write_to_mem m (wa a) bs) c cs.
Proof. intros m a bs c cs n <- Ha Hl H Hd. apply bytes_at_write_other; assumption. Qed.

Lemma rw_cells_frame_n : forall m A cs (a : Z) bs (n : Z),
  Z.of_nat (length bs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  rw_cells segs m A cs ->
  (A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z ->
  rw_cells segs (write_to_mem m (wa a) bs) A cs.
Proof. intros m A cs a bs n <- Ha Hl H Hd. apply rw_cells_frame; assumption. Qed.

Lemma ro_cells_frame_n : forall m A cs (a : Z) bs (n : Z),
  Z.of_nat (length bs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  ro_cells segs m A cs ->
  (A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z ->
  ro_cells segs (write_to_mem m (wa a) bs) A cs.
Proof. intros m A cs a bs n <- Ha Hl H Hd. apply ro_cells_frame; assumption. Qed.

Lemma u8arr_frame_n : forall m A bs a xs (n : Z),
  Z.of_nat (length xs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  u8arr segs m A bs ->
  (A + Z.of_nat (length bs) <= a \/ a + n <= A)%Z ->
  u8arr segs (write_to_mem m (wa a) xs) A bs.
Proof. intros m A bs a xs n <- Ha Hl H Hd. apply u8arr_frame; assumption. Qed.

Lemma u32arr_frame_n : forall m A ws a xs (n : Z),
  Z.of_nat (length xs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  u32arr segs m A ws ->
  (A + 4 * Z.of_nat (length ws) <= a \/ a + n <= A)%Z ->
  u32arr segs (write_to_mem m (wa a) xs) A ws.
Proof. intros m A ws a xs n <- Ha Hl H Hd. apply u32arr_frame; assumption. Qed.

Lemma u64arr_frame_n : forall m A ws a xs (n : Z),
  Z.of_nat (length xs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  u64arr segs m A ws ->
  (A + 8 * Z.of_nat (length ws) <= a \/ a + n <= A)%Z ->
  u64arr segs (write_to_mem m (wa a) xs) A ws.
Proof. intros m A ws a xs n <- Ha Hl H Hd. apply u64arr_frame; assumption. Qed.

Lemma u8ro_frame_n : forall m A bs a xs (n : Z),
  Z.of_nat (length xs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  u8ro segs m A bs ->
  (A + Z.of_nat (length bs) <= a \/ a + n <= A)%Z ->
  u8ro segs (write_to_mem m (wa a) xs) A bs.
Proof. intros m A bs a xs n <- Ha Hl H Hd. apply u8ro_frame; assumption. Qed.

Lemma stk_write_n : forall m lo hi a bs (n : Z),
  Z.of_nat (length bs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  stk segs m lo hi -> stk segs (write_to_mem m (wa a) bs) lo hi.
Proof. intros m lo hi a bs n <- Ha Hl H. apply stk_write; assumption. Qed.

End WithSegs.

Lemma munch_write_n : forall W m0 m a bs (n : Z),
  Z.of_nat (length bs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  munch W m0 m -> inside W a n ->
  munch W m0 (write_to_mem m (wa a) bs).
Proof. intros W m0 m a bs n <- Ha Hl H Hin. apply munch_write; assumption. Qed.

(* [comment removed for export] *)
Ltac is_natlit n := lazymatch n with O => idtac | S ?k => is_natlit k end.
Ltac cells_spine_closed cs :=
  lazymatch cs with
  | nil => idtac
  | cons ?c ?tl =>
      lazymatch c with C8 _ => idtac | C4 _ => idtac | C2 _ => idtac | C1 _ => idtac | CB ?n _ => is_natlit n end;
      cells_spine_closed tl
  end.
(* [comment removed for export] *)
Ltac literal_cell_sizes :=
  repeat match goal with
  | |- context [cells_size ?cs] =>
      cells_spine_closed cs;
      let n := eval cbv [cells_size csize Nat.add] in (cells_size cs) in
      change (cells_size cs) with n
  end.
Ltac literal_cell_sizes_in H :=
  repeat match type of H with
  | context [cells_size ?cs] =>
      cells_spine_closed cs;
      let n := eval cbv [cells_size csize Nat.add] in (cells_size cs) in
      change (cells_size cs) with n in H
  end.

(* [comment removed for export] *)
Ltac simpl_sizes_goal :=
  literal_cell_sizes;
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  try match goal with |- context [length (le8 _)] => rewrite !length_le8 end;
  try match goal with |- context [length (le4 _)] => rewrite !length_le4 end;
  try match goal with |- context [length (le2 _)] => rewrite !length_le2 end;
  try match goal with |- context [length (le1 _)] => rewrite !length_le1 end;
  try match goal with |- context [length (u32s _)] => rewrite !u32s_length end;
  try match goal with |- context [length (u64s _)] => rewrite !u64s_length end;
  try match goal with |- context [length (upd _ _ _)] => rewrite !upd_length end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac sf_is_nat_num n := lazymatch n with O => idtac | S ?k => sf_is_nat_num k end.
Ltac sf_fold_ofnat H :=
  repeat match type of H with context [Z.of_nat ?n] =>
    sf_is_nat_num n; let z := eval vm_compute in (Z.of_nat n) in progress change (Z.of_nat n) with z in H end.
Ltac store_facts a bs k :=
  let Hn := fresh "Hn_st" in let Ha := fresh "Ha_st" in let Hl := fresh "Hl_st" in
  let n0 := constr:(Z.of_nat (@length byte bs)) in
  let n1 := eval cbv [length app cbytes cells_bytes le8 le4 le2 le1 word_to_le_bytes Z_to_le_bytes
                      Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in n0 in
  let n := lazymatch n1 with Zpos _ => n1 | Z0 => n1 | _ => n0 end in
  first [ assert (Hn : Z.of_nat (@length byte bs) = n) by exact eq_refl
        | fail "store_facts: length of" bs "vs" n ];
  sf_hide_poison;
  first [ assert (Ha : (0 <= a)%Z) by tlia | sf_unhide; fail "store_facts: 0 <=" a ];
  first [ assert (Hl : (a + n <= 2^64)%Z)
            by first [ tlia | rewrite <- Hn; simpl_sizes; rewrite ?u32s_length, ?u64s_length, ?upd_length; tlia ]
        | sf_unhide; fail "store_facts:" a "+" n "<= 2^64" ];
  sf_fold_ofnat Ha; sf_fold_ofnat Hl;
  k n Hn Ha Hl;
  clear Hn Ha Hl; sf_unhide.

(* [comment removed for export] *)
Ltac transport_chunks_extra m a bs n Hn Ha Hl := idtac.
Ltac transport_call_extra segs W m m' MU WM := idtac.

Ltac transport_chunks_with segs m a bs n Hn Ha Hl :=
  (repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_write_other_n segs m a bs A2 bs2 n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_frame_n segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_frame_n segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_frame_n segs m A2 xs a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_frame_n segs m A2 xs a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_frame_n segs m A2 xs a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_frame_n segs m A2 xs a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  end);
  transport_chunks_extra m a bs n Hn Ha Hl.

Ltac footprint_after_store_with segs m a bs n Hn Ha Hl :=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write_n Wq mq m a bs n Hn Ha Hl) in MU; [ | cbn [inside]; tslia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write_n segs m loq hiq a bs n Hn Ha Hl) in STq
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

(* [comment removed for export] *)
Ltac transport_chunks_fast segs m a bs :=
  store_facts a bs ltac:(fun n Hn Ha Hl => transport_chunks_with segs m a bs n Hn Ha Hl).

(* [comment removed for export] *)
Ltac footprint_after_store_fast segs m a bs :=
  store_facts a bs ltac:(fun n Hn Ha Hl => footprint_after_store_with segs m a bs n Hn Ha Hl).

(* [comment removed for export] *)
Ltac mem_after_store_fast :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    let n := eval cbv in (csize c') in
    lazymatch goal with
    | H : rw_cells segs m A ?cs0 |- _ =>
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          let HB := fresh "HB" in
          pose proof (rw_cells_bound segs m A cs H) as HB; literal_cell_sizes_in HB; cbn [cells_size csize Nat.add] in HB; sf_fold_ofnat HB;
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
              [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          store_facts (A + Z.of_nat kn)%Z (cbytes c') ltac:(fun n' Hn Ha Hl =>
            transport_chunks_with segs m (A + Z.of_nat kn)%Z (cbytes c') n' Hn Ha Hl;
            footprint_after_store_with segs m (A + Z.of_nat kn)%Z (cbytes c') n' Hn Ha Hl);
          let m' := fresh "m" in
          remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
          clear Heqm; clear HB; try clear m; try rename H' into H
        end
    end
  end.

(* [comment removed for export] *)
Ltac disjoint_goal :=
  cbv [disjoint_from fst snd];
  simpl_sizes_goal;
  tslia.

Ltac transport_after_call_fast segs m m' MU WM :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  sf_hide_poison;
  (repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | disjoint_goal ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H;
              [ | eapply (munch_weaken W Wq m m');
                [ unfold sub_fp; cbn [outside];
                  (* [comment removed for export] *)
                  first [ intros; Zify.zify; xlia zchecker
                        | sf_unhide; zify_prune_plain; intros; Zify.zify; xlia zchecker
                        | intros; tslia ]
                | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end);
  transport_call_extra segs W m m' MU WM;
  sf_unhide.
