(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
Import ListNotations.

Module StoreFast.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import LiaTuning MState Mem Cells Exec Step Frame Arr Tac.
From Ltac2 Require Ltac2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
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

#[using="Type"] Lemma bytes_at_write_other_n : forall m a bs c cs (n : Z),
  Z.of_nat (length bs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  bytes_at segs m c cs ->
  (c + Z.of_nat (length cs) <= a \/ a + n <= c)%Z ->
  bytes_at segs (write_to_mem m (wa a) bs) c cs.
Proof. LiaFast.lf_pins LiaFast.u0. intros m a bs c cs n <- Ha Hl H Hd. apply bytes_at_write_other; assumption. Qed.

#[using="Type"] Lemma rw_cells_frame_n : forall m A cs (a : Z) bs (n : Z),
  Z.of_nat (length bs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  rw_cells segs m A cs ->
  (A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z ->
  rw_cells segs (write_to_mem m (wa a) bs) A cs.
Proof. LiaFast.lf_pins LiaFast.u0. intros m A cs a bs n <- Ha Hl H Hd. apply rw_cells_frame; assumption. Qed.

#[using="Type"] Lemma ro_cells_frame_n : forall m A cs (a : Z) bs (n : Z),
  Z.of_nat (length bs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  ro_cells segs m A cs ->
  (A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z ->
  ro_cells segs (write_to_mem m (wa a) bs) A cs.
Proof. LiaFast.lf_pins LiaFast.u0. intros m A cs a bs n <- Ha Hl H Hd. apply ro_cells_frame; assumption. Qed.

#[using="Type"] Lemma u8arr_frame_n : forall m A bs a xs (n : Z),
  Z.of_nat (length xs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  u8arr segs m A bs ->
  (A + Z.of_nat (length bs) <= a \/ a + n <= A)%Z ->
  u8arr segs (write_to_mem m (wa a) xs) A bs.
Proof. LiaFast.lf_pins LiaFast.u0. intros m A bs a xs n <- Ha Hl H Hd. apply u8arr_frame; assumption. Qed.

#[using="Type"] Lemma u32arr_frame_n : forall m A ws a xs (n : Z),
  Z.of_nat (length xs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  u32arr segs m A ws ->
  (A + 4 * Z.of_nat (length ws) <= a \/ a + n <= A)%Z ->
  u32arr segs (write_to_mem m (wa a) xs) A ws.
Proof. LiaFast.lf_pins LiaFast.u0. intros m A ws a xs n <- Ha Hl H Hd. apply u32arr_frame; assumption. Qed.

#[using="Type"] Lemma u64arr_frame_n : forall m A ws a xs (n : Z),
  Z.of_nat (length xs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  u64arr segs m A ws ->
  (A + 8 * Z.of_nat (length ws) <= a \/ a + n <= A)%Z ->
  u64arr segs (write_to_mem m (wa a) xs) A ws.
Proof. LiaFast.lf_pins LiaFast.u0. intros m A ws a xs n <- Ha Hl H Hd. apply u64arr_frame; assumption. Qed.

#[using="Type"] Lemma u8ro_frame_n : forall m A bs a xs (n : Z),
  Z.of_nat (length xs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  u8ro segs m A bs ->
  (A + Z.of_nat (length bs) <= a \/ a + n <= A)%Z ->
  u8ro segs (write_to_mem m (wa a) xs) A bs.
Proof. LiaFast.lf_pins LiaFast.u0. intros m A bs a xs n <- Ha Hl H Hd. apply u8ro_frame; assumption. Qed.

#[using="Type"] Lemma stk_write_n : forall m lo hi a bs (n : Z),
  Z.of_nat (length bs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  stk segs m lo hi -> stk segs (write_to_mem m (wa a) bs) lo hi.
Proof. LiaFast.lf_pins LiaFast.u0. intros m lo hi a bs n <- Ha Hl H. apply stk_write; assumption. Qed.

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
  k n Hn Ha Hl;
  clear Hn Ha Hl; sf_unhide.

(* [comment removed for export] *)
Ltac transport_chunks_extra m a bs n Hn Ha Hl := idtac.
Ltac transport_call_extra segs W m m' MU WM := idtac.

(* [comment removed for export] *)
Ltac transport_chunks_with_sc segs m a bs n Hn Ha Hl SC X b :=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ tr_lit H (bytes_at_write_other_lit segs m a bs X b A2 bs2 SC) b A2 constr:(Z.of_nat (@length byte bs2))
            | tr_sb H (bytes_at_write_other_sb segs m a bs X b) (bytes_at_write_other_sb0 segs m a bs X b) chk_sb b X A2 constr:(Z.of_nat (@length byte bs2)) SC
            | apply (bytes_at_write_other_n segs m a bs A2 bs2 n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ tr_lit H (rw_cells_frame_lit segs m a bs X b A2 cs2 SC) b A2 constr:(Z.of_nat (cells_size cs2))
            | tr_sb H (rw_cells_frame_sb segs m a bs X b) (rw_cells_frame_sb0 segs m a bs X b) chk_sb b X A2 constr:(Z.of_nat (cells_size cs2)) SC
            | apply (rw_cells_frame_n segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ tr_lit H (ro_cells_frame_lit segs m a bs X b A2 cs2 SC) b A2 constr:(Z.of_nat (cells_size cs2))
            | tr_sb H (ro_cells_frame_sb segs m a bs X b) (ro_cells_frame_sb0 segs m a bs X b) chk_sb b X A2 constr:(Z.of_nat (cells_size cs2)) SC
            | apply (ro_cells_frame_n segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ tr_lit H (u8arr_frame_lit segs m a bs X b A2 xs SC) b A2 constr:(Z.of_nat (@length byte xs))
            | tr_sb H (u8arr_frame_sb segs m a bs X b) (u8arr_frame_sb0 segs m a bs X b) chk_sb b X A2 constr:(Z.of_nat (@length byte xs)) SC
            | apply (u8arr_frame_n segs m A2 xs a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ tr_lit H (u32arr_frame_lit segs m a bs X b A2 xs SC) b A2 constr:((4 * Z.of_nat (@length word xs))%Z)
            | tr_sb H (u32arr_frame_sb segs m a bs X b) (u32arr_frame_sb0 segs m a bs X b) chk_sb b X A2 constr:((4 * Z.of_nat (@length word xs))%Z) SC
            | apply (u32arr_frame_n segs m A2 xs a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ tr_lit H (u64arr_frame_lit segs m a bs X b A2 xs SC) b A2 constr:((8 * Z.of_nat (@length word xs))%Z)
            | tr_sb H (u64arr_frame_sb segs m a bs X b) (u64arr_frame_sb0 segs m a bs X b) chk_sb b X A2 constr:((8 * Z.of_nat (@length word xs))%Z) SC
            | apply (u64arr_frame_n segs m A2 xs a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ tr_lit H (u8ro_frame_lit segs m a bs X b A2 xs SC) b A2 constr:(Z.of_nat (@length byte xs))
            | tr_sb H (u8ro_frame_sb segs m a bs X b) (u8ro_frame_sb0 segs m a bs X b) chk_sb b X A2 constr:(Z.of_nat (@length byte xs)) SC
            | apply (u8ro_frame_n segs m A2 xs a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : pristine m ?lo ?hi |- _ =>
      first [ tr_lit_pr H (pristine_write_other_lit m a bs X b lo hi SC) b lo hi
            | apply (pristine_write_other m lo hi a bs) in H; [ | exact Ha | rewrite Hn; exact Hl | rewrite Hn; tslia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  end.

Ltac transport_chunks_with segs m a bs n Hn Ha Hl :=
  store_ctx_of_facts true a bs Ha Hl ltac:(simpl_sizes_goal; tslia)
    ltac:(fun SC X b => transport_chunks_with_sc segs m a bs n Hn Ha Hl SC X b);
  transport_chunks_extra m a bs n Hn Ha Hl.

Ltac footprint_after_store_with segs m a bs n Hn Ha Hl :=
  store_ctx_of_facts false a bs Ha Hl ltac:(simpl_sizes_goal; tslia) ltac:(fun SC X b =>
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ let D := wdesc_of X Wq in
              lazymatch eval vm_compute in (chk_inside D b n) with true => idtac end;
              let WDH := fresh "dWD" in
              assert (WDH : wds_ok X Wq D) by
                (cbv beta iota delta [wds_ok wd_ok opt_holds wd_l wd_h wd_lo wd_hi];
                 repeat match goal with |- _ /\ _ => split end;
                 first [ exact I | reflexivity | symmetry; apply Z.add_0_r ]);
              apply (munch_write_wd Wq mq m a bs X b D SC WDH) in MU; [ | exact (@eq_refl bool true) ];
              clear WDH
            | apply (munch_write_n Wq mq m a bs n Hn Ha Hl) in MU; [ | cbn [inside]; tslia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write_n segs m loq hiq a bs n Hn Ha Hl) in STq
            | fail 100 "cannot transport stk hypothesis" STq ]
  end).

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
          pose proof (rw_cells_bound segs m A cs H) as HB; literal_cell_sizes_in HB; cbn [cells_size csize Nat.add] in HB;
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

Ltac transport_after_call_fast_orig segs m m' MU WM :=
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
  | H : pristine m ?lo ?hi |- _ =>
      first [ apply (pristine_transport W m m' lo hi) in H; [ | exact MU | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
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
Ltac transport_after_call_fast_cc segs m m' MU WM CC X B :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ tr_lits H (bytes_at_transport_lit segs m m' X B A2 bs2 CC) B A2 constr:(Z.of_nat (@length byte bs2))
            | tr_sb H (bytes_at_transport_sb segs m m' X B) (bytes_at_transport_sb0 segs m m' X B) chks_sb B X A2 constr:(Z.of_nat (@length byte bs2)) CC
            | apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ tr_lits H (rw_cells_transport_lit segs m m' X B A2 cs2 CC) B A2 constr:(Z.of_nat (cells_size cs2))
            | tr_sb H (rw_cells_transport_sb segs m m' X B) (rw_cells_transport_sb0 segs m m' X B) chks_sb B X A2 constr:(Z.of_nat (cells_size cs2)) CC
            | apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ tr_lits H (ro_cells_transport_lit segs m m' X B A2 cs2 CC) B A2 constr:(Z.of_nat (cells_size cs2))
            | tr_sb H (ro_cells_transport_sb segs m m' X B) (ro_cells_transport_sb0 segs m m' X B) chks_sb B X A2 constr:(Z.of_nat (cells_size cs2)) CC
            | apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ tr_lits H (u8arr_transport_lit segs m m' X B A2 xs CC) B A2 constr:(Z.of_nat (@length byte xs))
            | tr_sb H (u8arr_transport_sb segs m m' X B) (u8arr_transport_sb0 segs m m' X B) chks_sb B X A2 constr:(Z.of_nat (@length byte xs)) CC
            | apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ tr_lits H (u32arr_transport_lit segs m m' X B A2 xs CC) B A2 constr:((4 * Z.of_nat (@length word xs))%Z)
            | tr_sb H (u32arr_transport_sb segs m m' X B) (u32arr_transport_sb0 segs m m' X B) chks_sb B X A2 constr:((4 * Z.of_nat (@length word xs))%Z) CC
            | apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ tr_lits H (u64arr_transport_lit segs m m' X B A2 xs CC) B A2 constr:((8 * Z.of_nat (@length word xs))%Z)
            | tr_sb H (u64arr_transport_sb segs m m' X B) (u64arr_transport_sb0 segs m m' X B) chks_sb B X A2 constr:((8 * Z.of_nat (@length word xs))%Z) CC
            | apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ tr_lits H (u8ro_transport_lit segs m m' X B A2 xs CC) B A2 constr:(Z.of_nat (@length byte xs))
            | tr_sb H (u8ro_transport_sb segs m m' X B) (u8ro_transport_sb0 segs m m' X B) chks_sb B X A2 constr:(Z.of_nat (@length byte xs)) CC
            | apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | disjoint_goal ]
            | clear H ]
  | H : pristine m ?lo ?hi |- _ =>
      first [ tr_lits_pr H (pristine_transport_lit segs m m' X B lo hi CC) B lo hi
            | apply (pristine_transport W m m' lo hi) in H; [ | exact MU | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
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
  end.


(* [comment removed for export] *)
Ltac transport_after_call_fast segs m m' MU WM :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  sf_hide_poison;
  call_ctx_pose segs m m' MU WM ltac:(tlia)
    ltac:(fun CC X B => transport_after_call_fast_cc segs m m' MU WM CC X B;
                        transport_call_extra segs W m m' MU WM)
    ltac:(sf_unhide; transport_after_call_fast_orig segs m m' MU WM);
  sf_unhide.
End StoreFast.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition BIG_LIMBS : nat := 62.
Definition BIG_LEN_OFF : Z := 496.
Definition BIG_SIZE : Z := 504.          (* [comment removed for export] *)
Definition BIG_CAP : Z := 2 ^ 3968.      (* [comment removed for export] *)

Definition limbZ (ws : list word) (i : nat) : Z := bv_unsigned (nth i ws w0).

Lemma limbZ_range : forall ws i, 0 <= limbZ ws i < 2 ^ 64.
Proof. intros. unfold limbZ. pose proof (bv_unsigned_in_range 64 (nth i ws w0)) as H. unfold bv_modulus in H. exact H. Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition bigint_at (m : word -> option byte) (A : Z) (ws : list word) (len : Z) : Prop :=
  u64arr segs m A ws
  /\ length ws = BIG_LIMBS
  /\ rw_cells segs m (A + 496) [C2 (Z_to_bv 64 len)]
  /\ 0 <= len <= 62
  /\ A mod 8 = 0.

#[using="Type"] Lemma bigint_at_bound : forall m A ws len, bigint_at m A ws len -> 0 <= A /\ A + 498 <= 2 ^ 64.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m A ws len (AR & L & LC & _ & _).
  pose proof (u64arr_bound segs m A ws AR) as B1. rewrite L in B1. unfold BIG_LIMBS in B1.
  pose proof (rw_cells_bound segs m _ _ LC) as B2. cbn [cells_size csize Nat.add] in B2. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma bigint_at_transport : forall W m m' A ws len,
  bigint_at m A ws len -> munch W m m' -> wmono segs m m' ->
  disjoint_from W A 498 -> bigint_at m' A ws len.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros W m m' A ws len (AR & L & LC & Hle & Hal) MU WM D.
  split; [| split; [exact L| split; [| split; [exact Hle| exact Hal]]]].
  - eapply u64arr_transport; [exact AR | exact MU | exact WM |].
    rewrite L. unfold BIG_LIMBS. clear -D. induction W as [|[lo hi] W IH]; cbn in *; [exact I|]. destruct D; split; [lia| apply IH; assumption].
  - eapply rw_cells_transport; [exact LC | exact MU | exact WM |].
    cbn [cells_size csize Nat.add]. clear -D. induction W as [|[lo hi] W IH]; cbn in *; [exact I|]. destruct D; split; [lia| apply IH; assumption].
Qed.

End WithSegs.

(* [comment removed for export] *)
Lemma zx16_lit_small : forall z, 0 <= z < 2 ^ 16 -> zx16 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zx16. f_equal. rewrite unsigned_lit by lia. apply Z.mod_small. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint bval (ws : list word) (n : nat) : Z :=
  match n with
  | O => 0
  | S k => bval ws k + limbZ ws k * 2 ^ (64 * Z.of_nat k)
  end.

Lemma bval_0 : forall ws, bval ws 0 = 0. Proof. reflexivity. Qed.
Lemma bval_S : forall ws k, bval ws (S k) = bval ws k + limbZ ws k * 2 ^ (64 * Z.of_nat k).
Proof. reflexivity. Qed.

Lemma pow64_S : forall k : nat, 2 ^ (64 * Z.of_nat (S k)) = 2 ^ (64 * Z.of_nat k) * 2 ^ 64.
Proof. intros k. rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.

Lemma pow64_pos : forall k : nat, 0 < 2 ^ (64 * Z.of_nat k).
Proof. intros. apply Z.pow_pos_nonneg; lia. Qed.

Lemma bval_range : forall ws n, 0 <= bval ws n < 2 ^ (64 * Z.of_nat n).
Proof.
  intros ws n. induction n as [|n IH].
  - cbn. lia.
  - rewrite bval_S, pow64_S. pose proof (limbZ_range ws n). pose proof (pow64_pos n). nia.
Qed.

Lemma bval_nonneg : forall ws n, 0 <= bval ws n.
Proof. intros. apply bval_range. Qed.

(* [comment removed for export] *)
Lemma bval_ext : forall ws ws' n, (forall i, (i < n)%nat -> nth i ws w0 = nth i ws' w0) -> bval ws n = bval ws' n.
Proof.
  intros ws ws' n H. induction n as [|n IH]; [reflexivity|].
  rewrite !bval_S. rewrite IH by (intros; apply H; lia). unfold limbZ. rewrite H by lia. reflexivity.
Qed.

Lemma nth_upd_same : forall (ws : list word) i v, (i < length ws)%nat -> nth i (upd ws i v) w0 = v.
Proof.
  intros ws i v Hi. pose proof (nth_error_upd_same ws i v Hi) as H. apply nth_error_nth. exact H.
Qed.

Lemma nth_upd_other : forall (ws : list word) i j v, i <> j -> nth j (upd ws i v) w0 = nth j ws w0.
Proof.
  intros ws i j v Hij. destruct (nth_error ws j) as [x|] eqn:E.
  - pose proof (nth_error_upd_other ws i j v Hij) as H. rewrite E in H.
    rewrite (nth_error_nth _ _ _ H). symmetry. apply nth_error_nth. exact E.
  - apply nth_error_None in E.
    rewrite !nth_overflow; [reflexivity| lia |]. rewrite upd_length. lia.
Qed.

Lemma bval_upd_ge : forall ws n i v, (n <= i)%nat -> bval (upd ws i v) n = bval ws n.
Proof. intros ws n i v Hi. apply bval_ext. intros j Hj. apply nth_upd_other. lia. Qed.

Lemma bval_upd_lt : forall ws n i v, (i < n)%nat -> (i < length ws)%nat ->
  bval (upd ws i v) n = bval ws n + (bv_unsigned v - limbZ ws i) * 2 ^ (64 * Z.of_nat i).
Proof.
  intros ws n i v Hi Hl. induction n as [|n IH]; [lia|].
  rewrite !bval_S. destruct (Nat.eq_dec i n) as [->|Hne].
  - rewrite bval_upd_ge by lia. unfold limbZ. rewrite nth_upd_same by exact Hl. ring.
  - rewrite IH by lia. unfold limbZ. rewrite nth_upd_other by lia. ring.
Qed.

(* [comment removed for export] *)
Lemma bval_push : forall ws n v, (n < length ws)%nat ->
  bval (upd ws n v) (S n) = bval ws n + bv_unsigned v * 2 ^ (64 * Z.of_nat n).
Proof.
  intros ws n v Hn. rewrite bval_S, bval_upd_ge by lia. unfold limbZ. rewrite nth_upd_same by exact Hn. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition bnorm (ws : list word) (n : nat) : Prop := n = 0%nat \/ limbZ ws (n - 1) <> 0.

Lemma bnorm_0 : forall ws, bnorm ws 0. Proof. intros; left; reflexivity. Qed.

Lemma bnorm_top : forall ws n, (0 < n)%nat -> bnorm ws n -> limbZ ws (n - 1) <> 0.
Proof. intros ws n Hn [H|H]; [lia| exact H]. Qed.

Lemma bnorm_intro : forall ws n, limbZ ws (n - 1) <> 0 -> bnorm ws n.
Proof. intros; right; assumption. Qed.

(* [comment removed for export] *)
Lemma bnorm_lower : forall ws n, bnorm ws n -> (0 < n)%nat -> 2 ^ (64 * Z.of_nat (n - 1)) <= bval ws n.
Proof.
  intros ws n Hb Hn. destruct n as [|k]; [lia|]. replace (S k - 1)%nat with k in * by lia.
  rewrite bval_S. pose proof (bnorm_top ws (S k) ltac:(lia) Hb) as T. replace (S k - 1)%nat with k in T by lia.
  pose proof (limbZ_range ws k). pose proof (bval_nonneg ws k). pose proof (pow64_pos k). nia.
Qed.

(* [comment removed for export] *)
Lemma bnorm_len_le : forall ws n (L : nat), bnorm ws n -> bval ws n < 2 ^ (64 * Z.of_nat L) -> (n <= L)%nat.
Proof.
  intros ws n L Hb Hv. destruct (Nat.le_gt_cases n L) as [|Hgt]; [assumption|]. exfalso.
  destruct n as [|k]; [lia|].
  pose proof (bnorm_lower ws (S k) Hb ltac:(lia)) as Lo. replace (S k - 1)%nat with k in Lo by lia.
  assert (2 ^ (64 * Z.of_nat L) <= 2 ^ (64 * Z.of_nat k)) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Corollary bnorm_len_le_62 : forall ws n, bnorm ws n -> bval ws n < BIG_CAP -> (n <= 62)%nat.
Proof. intros ws n Hb Hv. apply (bnorm_len_le ws n 62 Hb). unfold BIG_CAP in Hv. exact Hv. Qed.

(* [comment removed for export] *)
Lemma bnorm_push : forall ws n v, (n < length ws)%nat -> bv_unsigned v <> 0 -> bnorm (upd ws n v) (S n).
Proof.
  intros ws n v Hn Hv. right. replace (S n - 1)%nat with n by lia. unfold limbZ. rewrite nth_upd_same by exact Hn. exact Hv.
Qed.

Lemma bnorm_upd_below : forall ws n i v, (i < n - 1)%nat -> bnorm ws n -> bnorm (upd ws i v) n.
Proof.
  intros ws n i v Hi [H|H]; [left; exact H| right]. unfold limbZ in *. rewrite nth_upd_other by lia. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mul_lo (x y cin : Z) : Z := ((x * y) mod 2 ^ 64 + cin) mod 2 ^ 64.
Definition mul_cout (x y cin : Z) : Z :=
  (x * y) / 2 ^ 64 + (if mul_lo x y cin <? (x * y) mod 2 ^ 64 then 1 else 0).

Lemma scalar_mul_step : forall x y cin,
  0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> 0 <= cin < 2 ^ 64 ->
  mul_lo x y cin + mul_cout x y cin * 2 ^ 64 = x * y + cin
  /\ 0 <= mul_cout x y cin < 2 ^ 64
  /\ 0 <= mul_lo x y cin < 2 ^ 64.
Proof.
  intros x y cin Hx Hy Hc. unfold mul_cout, mul_lo.
  set (p := x * y).
  assert (Hp : 0 <= p <= (2^64 - 1) * (2^64 - 1)) by (subst p; nia).
  pose proof (Z.div_mod p (2^64) ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound p (2^64) ltac:(lia)) as Hm.
  set (pl := p mod 2 ^ 64) in *. set (ph := p / 2 ^ 64) in *.
  assert (Hph : 0 <= ph <= 2^64 - 2).
  { split. { subst ph. apply Z.div_pos; lia. }
    assert (ph * 2^64 <= p) by lia. nia. }
  destruct (Z.lt_ge_cases (pl + cin) (2 ^ 64)) as [Hlt|Hge].
  - rewrite (Z.mod_small (pl + cin)) by lia.
    replace (pl + cin <? pl) with false by (symmetry; apply Z.ltb_ge; lia). lia.
  - rewrite <- (Z.mod_unique_pos (pl + cin) (2^64) 1 (pl + cin - 2^64)) by lia.
    replace (pl + cin - 2 ^ 64 <? pl) with true by (symmetry; apply Z.ltb_lt; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma shiftr64_div : forall z, Z.shiftr z 64 = z / 2 ^ 64.
Proof. intros. apply Z.shiftr_div_pow2. lia. Qed.

Lemma scalar_mul_eqs : forall x y cin,
  0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> 0 <= cin < 2 ^ 64 ->
  (x * y + cin) mod 2 ^ 64 = mul_lo x y cin /\ (x * y + cin) / 2 ^ 64 = mul_cout x y cin.
Proof.
  intros x y cin Hx Hy Hc.
  pose proof (scalar_mul_step x y cin Hx Hy Hc) as (E & Hco & Hlo).
  split.
  - rewrite <- E. rewrite Z.mod_add, Z.mod_small by lia. reflexivity.
  - rewrite <- E. rewrite Z.div_add, Z.div_small by lia. lia.
Qed.

(* [comment removed for export] *)
Definition add_lo (x y : Z) : Z := (x + y) mod 2 ^ 64.
Definition add_ov (x y : Z) : Z := if add_lo x y <? x then 1 else 0.

Lemma scalar_add_step : forall x y,
  0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  add_lo x y + add_ov x y * 2 ^ 64 = x + y /\ 0 <= add_lo x y < 2 ^ 64 /\ 0 <= add_ov x y <= 1.
Proof.
  intros x y Hx Hy. unfold add_ov, add_lo.
  destruct (Z.lt_ge_cases (x + y) (2 ^ 64)) as [Hlt|Hge].
  - rewrite Z.mod_small by lia. replace (x + y <? x) with false by (symmetry; apply Z.ltb_ge; lia). lia.
  - rewrite <- (Z.mod_unique_pos (x + y) (2^64) 1 (x + y - 2^64)) by lia.
    replace (x + y - 2 ^ 64 <? x) with true by (symmetry; apply Z.ltb_lt; lia). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition smul_inv (ws0 cur : list word) (y : Z) (i : nat) (c : Z) : Prop :=
  bval cur i + c * 2 ^ (64 * Z.of_nat i) = y * bval ws0 i
  /\ (forall j, (i <= j)%nat -> nth j cur w0 = nth j ws0 w0)
  /\ 0 <= c < 2 ^ 64
  /\ length cur = length ws0.

Lemma smul_inv_init : forall ws0 y, smul_inv ws0 ws0 y 0 0.
Proof. intros. split; [cbn; lia|]. split; [intros; reflexivity|]. split; [lia| reflexivity]. Qed.

Lemma smul_inv_step : forall ws0 cur y i c (lo : word),
  smul_inv ws0 cur y i c -> 0 <= y < 2 ^ 64 -> (i < length ws0)%nat ->
  bv_unsigned lo = mul_lo (limbZ ws0 i) y c ->
  smul_inv ws0 (upd cur i lo) y (S i) (mul_cout (limbZ ws0 i) y c).
Proof.
  intros ws0 cur y i c lo (Hv & Hagree & Hc & Hlen) Hy Hi Hlo.
  pose proof (scalar_mul_step (limbZ ws0 i) y c (limbZ_range ws0 i) Hy Hc) as (E & Hco & Hloo).
  split; [| split; [| split; [exact Hco| rewrite upd_length; exact Hlen]]].
  - rewrite bval_push by (rewrite Hlen; exact Hi). rewrite Hlo.
    rewrite bval_S, pow64_S.
    assert (bval cur i = y * bval ws0 i - c * 2 ^ (64 * Z.of_nat i)) as -> by lia.
    nia.
  - intros j Hj. rewrite nth_upd_other by lia. apply Hagree. lia.
Qed.

(* [comment removed for export] *)
Lemma smul_inv_finish_nocarry : forall ws0 cur y n,
  smul_inv ws0 cur y n 0 -> bval cur n = y * bval ws0 n.
Proof. intros ws0 cur y n (Hv & _). lia. Qed.

Lemma smul_inv_finish_carry : forall ws0 cur y n c,
  smul_inv ws0 cur y n c -> (n < length ws0)%nat ->
  bval (upd cur n (Z_to_bv 64 c)) (S n) = y * bval ws0 n.
Proof.
  intros ws0 cur y n c (Hv & Hag & Hc & Hlen) Hn.
  rewrite bval_push by (rewrite Hlen; exact Hn). rewrite unsigned_lit by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma smul_carry_room : forall ws0 cur y n c,
  smul_inv ws0 cur y n c -> c <> 0 -> y * bval ws0 n < BIG_CAP -> (n < 62)%nat.
Proof.
  intros ws0 cur y n c (Hv & _ & Hc & _) Hcnz Hcap. unfold BIG_CAP in Hcap.
  pose proof (bval_nonneg cur n).
  assert (2 ^ (64 * Z.of_nat n) <= y * bval ws0 n) by nia.
  destruct (Nat.lt_ge_cases n 62) as [|Hge]; [assumption|]. exfalso.
  assert (2 ^ (64 * 62) <= 2 ^ (64 * Z.of_nat n)) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma smul_top_nonzero : forall x y cin,
  0 < x < 2 ^ 64 -> 0 < y < 2 ^ 64 -> 0 <= cin < 2 ^ 64 ->
  mul_cout x y cin = 0 -> mul_lo x y cin <> 0.
Proof.
  intros x y cin Hx Hy Hc H0.
  pose proof (scalar_mul_step x y cin ltac:(lia) ltac:(lia) Hc) as (E & _ & _). rewrite H0 in E. nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma BIG_CAP_pos : 0 < BIG_CAP. Proof. unfold BIG_CAP. apply Z.pow_pos_nonneg; lia. Qed.

(* [comment removed for export] *)
Lemma pow5_split : forall e a, 0 <= a -> 135 * a <= e -> 5 ^ e = 5 ^ (135 * a) * 5 ^ (e - 135 * a).
Proof. intros e a Ha He. rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.

Lemma mul_lt_cap_mono : forall v a b, 0 <= v -> 0 <= a <= b -> v * b < BIG_CAP -> v * a < BIG_CAP.
Proof. intros v a b Hv Hab H. nia. Qed.

(* [comment removed for export] *)
Definition POW5_27 : Z := 7450580596923828125.          (* [comment removed for export] *)
Lemma POW5_27_eq : POW5_27 = 5 ^ 27. Proof. reflexivity. Qed.
Definition LARGE_POW5 : list Z :=                         (* [comment removed for export] *)
  [1414648277510068013; 9180637584431281687; 4539964771860779200; 10482974169319127550; 198276706040285095].
Lemma LARGE_POW5_val :
  nth 0 LARGE_POW5 0 + nth 1 LARGE_POW5 0 * 2^64 + nth 2 LARGE_POW5 0 * 2^128 + nth 3 LARGE_POW5 0 * 2^192 + nth 4 LARGE_POW5 0 * 2^256
  = 5 ^ 135.
Proof. vm_compute. reflexivity. Qed.
Definition SMALL_POW5 : list Z := Eval vm_compute in (map (fun k => 5 ^ Z.of_nat k) (seq 0 28)).
Lemma SMALL_POW5_nth : forall k, (k < 28)%nat -> nth k SMALL_POW5 0 = 5 ^ Z.of_nat k.
Proof.
  intros k Hk. do 28 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.
