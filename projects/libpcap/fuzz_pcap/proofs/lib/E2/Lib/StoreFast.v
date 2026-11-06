(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac.
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

#[using="Type"] Lemma bytes_at_write_other_n : forall m a bs c cs (n : Z),
  Z.of_nat (length bs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  bytes_at segs m c cs ->
  (c + Z.of_nat (length cs) <= a \/ a + n <= c)%Z ->
  bytes_at segs (write_to_mem m (wa a) bs) c cs.
Proof. intros m a bs c cs n <- Ha Hl H Hd. apply bytes_at_write_other; assumption. Qed.

#[using="Type"] Lemma rw_cells_frame_n : forall m A cs (a : Z) bs (n : Z),
  Z.of_nat (length bs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  rw_cells segs m A cs ->
  (A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z ->
  rw_cells segs (write_to_mem m (wa a) bs) A cs.
Proof. intros m A cs a bs n <- Ha Hl H Hd. apply rw_cells_frame; assumption. Qed.

#[using="Type"] Lemma ro_cells_frame_n : forall m A cs (a : Z) bs (n : Z),
  Z.of_nat (length bs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  ro_cells segs m A cs ->
  (A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z ->
  ro_cells segs (write_to_mem m (wa a) bs) A cs.
Proof. intros m A cs a bs n <- Ha Hl H Hd. apply ro_cells_frame; assumption. Qed.

#[using="Type"] Lemma u8arr_frame_n : forall m A bs a xs (n : Z),
  Z.of_nat (length xs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  u8arr segs m A bs ->
  (A + Z.of_nat (length bs) <= a \/ a + n <= A)%Z ->
  u8arr segs (write_to_mem m (wa a) xs) A bs.
Proof. intros m A bs a xs n <- Ha Hl H Hd. apply u8arr_frame; assumption. Qed.

#[using="Type"] Lemma u32arr_frame_n : forall m A ws a xs (n : Z),
  Z.of_nat (length xs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  u32arr segs m A ws ->
  (A + 4 * Z.of_nat (length ws) <= a \/ a + n <= A)%Z ->
  u32arr segs (write_to_mem m (wa a) xs) A ws.
Proof. intros m A ws a xs n <- Ha Hl H Hd. apply u32arr_frame; assumption. Qed.

#[using="Type"] Lemma u64arr_frame_n : forall m A ws a xs (n : Z),
  Z.of_nat (length xs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  u64arr segs m A ws ->
  (A + 8 * Z.of_nat (length ws) <= a \/ a + n <= A)%Z ->
  u64arr segs (write_to_mem m (wa a) xs) A ws.
Proof. intros m A ws a xs n <- Ha Hl H Hd. apply u64arr_frame; assumption. Qed.

#[using="Type"] Lemma u8ro_frame_n : forall m A bs a xs (n : Z),
  Z.of_nat (length xs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  u8ro segs m A bs ->
  (A + Z.of_nat (length bs) <= a \/ a + n <= A)%Z ->
  u8ro segs (write_to_mem m (wa a) xs) A bs.
Proof. intros m A bs a xs n <- Ha Hl H Hd. apply u8ro_frame; assumption. Qed.

#[using="Type"] Lemma stk_write_n : forall m lo hi a bs (n : Z),
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
Ltac is_natlit n := sl_is_natlit n.   (* [comment removed for export] *)
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
Ltac sl_store_extra_std m m' a bs n Hn Ha Hl CH :=
  let Hn0 := fresh "Hn_st" in let Ha0 := fresh "Ha_st" in let Hl0 := fresh "Hl_st" in let CH0 := fresh "CH_st" in
  assert (Hn0 : Z.of_nat (@length byte bs) = n) by exact Hn;
  assert (Ha0 : (0 <= a)%Z) by exact Ha;
  assert (Hl0 : (a + n <= 2^64)%Z) by (rewrite <- Hn0; exact Hl);
  pose proof CH as CH0; change m' with (write_to_mem m (wa a) bs) in CH0;
  transport_chunks_extra m a bs n Hn0 Ha0 Hl0;
  clear Hn0 Ha0 Hl0 CH0;
  repeat match goal with Hx : context [write_to_mem m (wa a) bs] |- _ => change (write_to_mem m (wa a) bs) with m' in Hx end.

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
          rmx_set (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) m';
          clear HB; try clear m; try rename H' into H
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac tlia_sf0 := first [ Zify.zify; xlia zchecker
                       | sf_unhide;
                         first [ zify_prune_neg; Zify.zify; xlia zchecker
                               | zify_prune_plain; Zify.zify; xlia zchecker
                               | Zify.zify; xlia zchecker ] ].
Ltac disjoint_goal_sf0 :=
  cbv [disjoint_from fst snd];
  simpl_sizes_goal;
  tslia.
Ltac sf_cheap_lia := Zify.zify; xlia zchecker.
Ltac sf_cheap_tslia := first [ exact I | sf_cheap_lia | split; [ sf_cheap_lia | exact I ] ].
Ltac sf_conj_refuted G :=
  lazymatch G with
  | ?A /\ ?B => first [ assert_succeeds (assert (~ A) by sf_cheap_lia) | sf_conj_refuted B ]
  | True => fail
  | ?A => assert_succeeds (assert (~ A) by sf_cheap_lia)
  end.
Ltac sf_lia_refuted := lazymatch goal with |- ?G => sf_conj_refuted G end.
(* [comment removed for export] *)
Ltac disjoint_goal_e3 :=
  cbv [disjoint_from fst snd];
  simpl_sizes_goal;
  tryif sl_syn_refuted then fail
  else first [ sf_cheap_tslia | tryif sf_lia_refuted then fail else tslia ].
Module DGS.
  Import Ltac2.
  (* [comment removed for export] *)
  Ltac2 rec dg_nor (c_or : constr) (t : constr) : int :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App f args =>
        let s := Array.fold_left (fun acc a => Int.add acc (dg_nor c_or a)) 0 args in
        if Constr.equal f c_or then Int.add s 1 else s
    | Constr.Unsafe.Prod b body => Int.add (dg_nor c_or (Constr.Binder.type b)) (dg_nor c_or body)
    | _ => 0
    end.
  (* [comment removed for export] *)
  Ltac2 rec dg_nconj (c_and : constr) (c_true : constr) (t : constr) : int :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App f args =>
        if Constr.equal f c_and then Int.add 1 (dg_nconj c_and c_true (Array.get args 1)) else 1
    | _ => if Constr.equal t c_true then 0 else 1
    end.
  (* [comment removed for export] *)
  Ltac2 dg_prod (c_or : constr) (c_and : constr) (g : constr) : int :=
    let c_hide := constr:(sf_hide) in
    let gv := SF2.vars_of [] g in
    List.fold_left (fun acc h =>
      let (_, body, ty0) := h in
      match body with
      | Some _ => acc
      | None =>
          let ty := match Constr.Unsafe.kind ty0 with
                    | Constr.Unsafe.App f args => if Constr.equal f c_hide then Array.get args 0 else ty0
                    | _ => ty0
                    end in
          match Constr.Unsafe.kind ty with
          | Constr.Unsafe.App f _ =>
              if (if Constr.equal f c_or then true else Constr.equal f c_and) then
                (if SF2.arith_logic ty then
                   (let k := dg_nor c_or ty in
                    if Int.equal k 0 then acc
                    else if SF2.meets (SF2.vars_of [] ty) gv then Int.mul acc (Int.add 1 k) else acc)
                 else acc)
              else acc
          | _ => acc
          end
      end) 1 (Control.hyps ()).
  (* [comment removed for export] *)
  Ltac2 dg_split_worth () : unit :=
    let g := Control.goal () in
    let c_or := constr:(or) in let c_and := constr:(and) in
    if Int.le 2 (dg_nconj c_and constr:(True) g) then (if Int.le 32 (dg_prod c_or c_and g) then () else Control.zero (Tactic_failure None))
    else Control.zero (Tactic_failure None).
  Ltac dg_split_worth := ltac2:(Control.enter dg_split_worth).
End DGS.
Ltac dg_conj :=
  lazymatch goal with
  | |- True => exact I
  | |- _ /\ _ => split; [ tlia | dg_conj ]
  | |- _ => tlia
  end.
Ltac disjoint_goal ::=
  cbv [disjoint_from fst snd];
  simpl_sizes_goal;
  tryif sl_syn_refuted then fail
  else first [ sf_cheap_tslia | tryif sf_lia_refuted then fail else first [ DGS.dg_split_worth; dg_conj | tslia ] ].

(* [comment removed for export] *)
Module FFRel.
  Import Ltac2.
  Ltac2 prune_rel2 () : unit :=
    let gv := SF2.vars_of [] (Control.goal ()) in
    SF2.prune_with (fun ty => if SF2.plain_arith false ty then true
                                        else SF2.meets (SF2.vars_of [] ty) gv).
  Ltac2 prune_rel2_1 () : unit := Control.enter prune_rel2.
End FFRel.
Ltac zify_prune_rel2 := ltac2:(FFRel.prune_rel2_1 ()).
(* [comment removed for export] *)
Ltac tlia ::= first [ Zify.zify; xlia zchecker
                    | sf_unhide;
                      first [ zify_prune_rel2; Zify.zify; xlia zchecker
                            | zify_prune_neg; Zify.zify; xlia zchecker
                            | zify_prune_plain; Zify.zify; xlia zchecker
                            | Zify.zify; xlia zchecker ] ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac store_facts_d0 a bs k :=
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
Ltac store_facts a bs k ::=
  let Hn := fresh "Hn_st" in let Ha := fresh "Ha_st" in let Hl := fresh "Hl_st" in
  let n0 := constr:(Z.of_nat (@length byte bs)) in
  let n1 := eval cbv [length app cbytes cells_bytes le8 le4 le2 le1 word_to_le_bytes Z_to_le_bytes
                      Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in n0 in
  let n := lazymatch n1 with Zpos _ => n1 | Z0 => n1 | _ => n0 end in
  first [ assert (Hn : Z.of_nat (@length byte bs) = n) by exact eq_refl
        | fail "store_facts: length of" bs "vs" n ];
  sf_hide_poison;
  first [ (* [comment removed for export] *)
          lazymatch a with
          | (?A + Z.of_nat ?kn)%Z =>
              lazymatch goal with
              | HB : (0 <= A /\ A + ?S <= 2 ^ 64)%Z |- _ =>
                  d_lit_size S; d_is_natlit kn; d_is_Zlit n;
                  d_true constr:(dchk (Z.of_nat kn) n S);
                  assert (Ha : (0 <= a)%Z) by exact (d_lb A S (Z.of_nat kn) n HB (@eq_refl bool true));
                  assert (Hl : (a + n <= 2^64)%Z) by exact (d_ub A S (Z.of_nat kn) n n HB (@eq_refl Z n) (@eq_refl bool true))
              end
          end
        | first [ assert (Ha : (0 <= a)%Z) by tlia | sf_unhide; fail "store_facts: 0 <=" a ];
          first [ assert (Hl : (a + n <= 2^64)%Z)
                    by first [ tlia | rewrite <- Hn; simpl_sizes; rewrite ?u32s_length, ?u64s_length, ?upd_length; tlia ]
                | sf_unhide; fail "store_facts:" a "+" n "<= 2^64" ] ];
  k n Hn Ha Hl;
  clear Hn Ha Hl; sf_unhide.

Ltac transport_chunks_with_d0 segs m a bs n Hn Ha Hl :=
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
Ltac footprint_after_store_with_d0 segs m a bs n Hn Ha Hl :=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write_n Wq mq m a bs n Hn Ha Hl) in MU; [ | cbn [inside]; tslia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write_n segs m loq hiq a bs n Hn Ha Hl) in STq
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

Ltac transport_chunks_with segs m a bs n Hn Ha Hl ::=
  (repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_write_other_n segs m a bs A2 bs2 n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ d_spine_closed cs2;
              d_disj segs (write_to_mem m (wa a) bs) a n A2 constr:(Z.of_nat (cells_size cs2)) ltac:(tslia)
                ltac:(fun t => apply (rw_cells_frame_n segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | exact t ])
                ltac:(fun _ => first [ apply (rw_cells_frame_n segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
                                     | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ])
            | apply (rw_cells_frame_n segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ d_spine_closed cs2;
              d_disj segs (write_to_mem m (wa a) bs) a n A2 constr:(Z.of_nat (cells_size cs2)) ltac:(tslia)
                ltac:(fun t => apply (ro_cells_frame_n segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | exact t ])
                ltac:(fun _ => first [ apply (ro_cells_frame_n segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
                                     | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ])
            | apply (ro_cells_frame_n segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
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
Ltac footprint_after_store_with segs m a bs n Hn Ha Hl ::=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ d_inside segs (write_to_mem m (wa a) bs) a n Wq ltac:(tslia)
                ltac:(fun t => apply (munch_write_n Wq mq m a bs n Hn Ha Hl) in MU; [ | exact t ])
                ltac:(fun _ => apply (munch_write_n Wq mq m a bs n Hn Ha Hl) in MU; [ | cbn [inside]; tslia ])
            | apply (munch_write_n Wq mq m a bs n Hn Ha Hl) in MU; [ | cbn [inside]; tslia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write_n segs m loq hiq a bs n Hn Ha Hl) in STq
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

(* [comment removed for export] *)
Ltac sf_ivl_prover := first [ sf_cheap_tslia | tryif sf_lia_refuted then fail else tslia ].
Ltac transport_after_call_fast_d0 segs m m' MU WM :=
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
                  first [ intros; Zify.zify; xlia zchecker
                        | sf_unhide; zify_prune_plain; intros; Zify.zify; xlia zchecker
                        | intros; tslia ]
                | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end);
  transport_call_extra segs W m m' MU WM;
  sf_unhide.
Ltac transport_after_call_fast segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  sf_hide_poison;
  (repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ d_spine_closed cs2;
              d_call_disj W A2 constr:(Z.of_nat (cells_size cs2)) ltac:(sf_ivl_prover)
                ltac:(fun t => apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | exact t ])
                ltac:(fun _ => first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | disjoint_goal ]
                                     | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ])
            | apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ d_spine_closed cs2;
              d_call_disj W A2 constr:(Z.of_nat (cells_size cs2)) ltac:(sf_ivl_prover)
                ltac:(fun t => apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact t ])
                ltac:(fun _ => first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | disjoint_goal ]
                                     | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ])
            | apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | disjoint_goal ]
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
                  first [ intros; Zify.zify; xlia zchecker
                        | sf_unhide; zify_prune_plain; intros; Zify.zify; xlia zchecker
                        | intros; tslia ]
                | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end);
  transport_call_extra segs W m m' MU WM;
  sf_unhide.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac transport_after_call_fast_e1 segs m m' MU WM :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  sf_hide_poison;
  (repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ d_spine_closed cs2;
              d_call_disj W A2 constr:(Z.of_nat (cells_size cs2)) ltac:(sf_ivl_prover)
                ltac:(fun t => apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | exact t ])
                ltac:(fun _ => first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | disjoint_goal ]
                                     | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ])
            | apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ d_spine_closed cs2;
              d_call_disj W A2 constr:(Z.of_nat (cells_size cs2)) ltac:(sf_ivl_prover)
                ltac:(fun t => apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact t ])
                ltac:(fun _ => first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | disjoint_goal ]
                                     | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ])
            | apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | disjoint_goal ]
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
                  first [ intros; Zify.zify; xlia zchecker
                        | sf_unhide; zify_prune_plain; intros; Zify.zify; xlia zchecker
                        | intros; tslia ]
                | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end);
  transport_call_extra segs W m m' MU WM;
  sf_unhide.

Ltac transport_after_call_fast segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  sf_hide_poison;
  (repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ d_spine_closed cs2;
              d_call_disjm m W A2 constr:(Z.of_nat (cells_size cs2)) ltac:(sf_ivl_prover) ltac:(sf_cheap_lia)
                ltac:(fun t => apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | exact t ])
                ltac:(fun _ => first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | disjoint_goal ]
                                     | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ])
            | apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ d_spine_closed cs2;
              d_call_disjm m W A2 constr:(Z.of_nat (cells_size cs2)) ltac:(sf_ivl_prover) ltac:(sf_cheap_lia)
                ltac:(fun t => apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact t ])
                ltac:(fun _ => first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | disjoint_goal ]
                                     | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ])
            | apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | disjoint_goal ]
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
                  first [ intros; Zify.zify; xlia zchecker
                        | sf_unhide; zify_prune_plain; intros; Zify.zify; xlia zchecker
                        | intros; tslia ]
                | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end);
  d_hull_clear;
  transport_call_extra segs W m m' MU WM;
  sf_unhide.

Ltac transport_chunks_with_e1 segs m a bs n Hn Ha Hl :=
  (repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_write_other_n segs m a bs A2 bs2 n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ d_spine_closed cs2;
              d_disj segs (write_to_mem m (wa a) bs) a n A2 constr:(Z.of_nat (cells_size cs2)) ltac:(tslia)
                ltac:(fun t => apply (rw_cells_frame_n segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | exact t ])
                ltac:(fun _ => first [ apply (rw_cells_frame_n segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
                                     | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ])
            | apply (rw_cells_frame_n segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ d_spine_closed cs2;
              d_disj segs (write_to_mem m (wa a) bs) a n A2 constr:(Z.of_nat (cells_size cs2)) ltac:(tslia)
                ltac:(fun t => apply (ro_cells_frame_n segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | exact t ])
                ltac:(fun _ => first [ apply (ro_cells_frame_n segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
                                     | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ])
            | apply (ro_cells_frame_n segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
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

Ltac transport_chunks_with segs m a bs n Hn Ha Hl ::=
  (repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_write_other_n segs m a bs A2 bs2 n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ d_spine_closed cs2;
              d_disjm segs m (write_to_mem m (wa a) bs) a n A2 constr:(Z.of_nat (cells_size cs2)) ltac:(tslia) ltac:(sf_cheap_lia)
                ltac:(fun t => apply (rw_cells_frame_n segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | exact t ])
                ltac:(fun _ => first [ apply (rw_cells_frame_n segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
                                     | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ])
            | apply (rw_cells_frame_n segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ d_spine_closed cs2;
              d_disjm segs m (write_to_mem m (wa a) bs) a n A2 constr:(Z.of_nat (cells_size cs2)) ltac:(tslia) ltac:(sf_cheap_lia)
                ltac:(fun t => apply (ro_cells_frame_n segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | exact t ])
                ltac:(fun _ => first [ apply (ro_cells_frame_n segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
                                     | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ])
            | apply (ro_cells_frame_n segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
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
  d_hull_clear;
  transport_chunks_extra m a bs n Hn Ha Hl.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Module SFC.
  Import Ltac2.
  (* [comment removed for export] *)
  Ltac2 Type memo := { mutable mh : (constant, int) FMap.t; mutable mi : (inductive, int) FMap.t;
                       mutable mb : (constant, bool) FMap.t; mbad : constr list }.
  Ltac2 memo_new () : memo := { mh := FMap.empty FSet.Tags.constant_tag; mi := FMap.empty FSet.Tags.inductive_tag;
                                mb := FMap.empty FSet.Tags.constant_tag; mbad := SF2.bad_heads () }.
  Ltac2 rec last_id (l : ident list) : ident option :=
    match l with [] => None | x :: r => match r with [] => Some x | _ :: _ => last_id r end end.
  Ltac2 label_code (r : Std.reference) : int :=
    match Control.case (fun () => Env.path r) with
    | Val p => let (l, _) := p in
        (match last_id l with
         | Some i => if List.exist (Ident.equal i) [@and; @or; @iff; @not; @le; @lt; @ge; @gt; @eq; @divide] then 9 else 0
         | None => 9
         end)
    | Err _ => 9
    end.
  Ltac2 is_c (c : constant) (r : Std.reference) : bool := match r with Std.ConstRef c0 => Constant.equal c c0 | _ => false end.
  Ltac2 is_i (i : inductive) (r : Std.reference) : bool := match r with Std.IndRef i0 => Ind.equal i i0 | _ => false end.
  Ltac2 const_code (c : constant) : int :=
    let r := Std.ConstRef c in
    if is_c c reference:(Z.le) then 1 else if is_c c reference:(Z.lt) then 1
    else if is_c c reference:(Z.ge) then 1 else if is_c c reference:(Z.gt) then 1
    else if is_c c reference:(lt) then 1 else if is_c c reference:(ge) then 1
    else if is_c c reference:(gt) then 1 else if is_c c reference:(N.le) then 1
    else if is_c c reference:(N.lt) then 1 else if is_c c reference:(Z.divide) then 1
    else if is_c c reference:(iff) then 5 else if is_c c reference:(not) then 6
    else label_code r.
  Ltac2 ind_code (i : inductive) : int :=
    let r := Std.IndRef i in
    if is_i i reference:(and) then 3 else if is_i i reference:(or) then 4
    else if is_i i reference:(eq) then 2 else if is_i i reference:(le) then 1
    else label_code r.
  (* [comment removed for export] *)
  Ltac2 code (m : memo) (t : constr) : int :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App f args =>
        let k := match Constr.Unsafe.kind f with
                 | Constr.Unsafe.Constant c _ =>
                     (match FMap.find_opt c (m.(mh)) with
                      | Some k => k
                      | None => let k := const_code c in m.(mh) := FMap.add c k (m.(mh)); k
                      end)
                 | Constr.Unsafe.Ind i _ =>
                     (match FMap.find_opt i (m.(mi)) with
                      | Some k => k
                      | None => let k := ind_code i in m.(mi) := FMap.add i k (m.(mi)); k
                      end)
                 | Constr.Unsafe.Constructor _ _ => 0
                 | Constr.Unsafe.Var _ => 0
                 | Constr.Unsafe.Rel _ => 0
                 | _ => 9
                 end in
        let n := Array.length args in
        if Int.equal k 0 then 0
        else if Int.equal k 9 then 9
        else if Int.equal k 2 then (if Int.equal n 3 then 2 else 9)
        else if Int.equal k 6 then (if Int.equal n 1 then 6 else 9)
        else (if Int.equal n 2 then k else 9)
    | _ => 9
    end.
  Ltac2 rec plain_arith_old (m : memo) (neg : bool) (t : constr) : bool :=
    lazy_match! t with
    | Z.le _ _ => true | Z.lt _ _ => true | Z.ge _ _ => true | Z.gt _ _ => true
    | @eq _ _ _ => true
    | le _ _ => true | lt _ _ => true | ge _ _ => true | gt _ _ => true
    | N.le _ _ => true | N.lt _ _ => true | Z.divide _ _ => true
    | ?a /\ ?b => Bool.and (plain_arith m neg a) (plain_arith m neg b)
    | True => true | False => true
    | not ?a => Bool.and neg (plain_arith m false a)
    | ?a -> False => Bool.and neg (plain_arith m false a)
    | _ => false
    end
  with plain_arith (m : memo) (neg : bool) (t : constr) : bool :=
    let k := code m t in
    if Int.equal k 0 then false
    else if Int.equal k 1 then true else if Int.equal k 2 then true
    else if Int.equal k 3 then
      (match Constr.Unsafe.kind t with
       | Constr.Unsafe.App _ args => Bool.and (plain_arith m neg (Array.get args 0)) (plain_arith m neg (Array.get args 1))
       | _ => plain_arith_old m neg t
       end)
    else if Int.equal k 4 then false else if Int.equal k 5 then false
    else if Int.equal k 6 then
      (match Constr.Unsafe.kind t with
       | Constr.Unsafe.App _ args => Bool.and neg (plain_arith m false (Array.get args 0))
       | _ => plain_arith_old m neg t
       end)
    else plain_arith_old m neg t.
  Ltac2 rec arith_logic_old (m : memo) (t : constr) : bool :=
    lazy_match! t with
    | ?a /\ ?b => Bool.and (arith_logic m a) (arith_logic m b)
    | ?a \/ ?b => Bool.and (arith_logic m a) (arith_logic m b)
    | ?a <-> ?b => Bool.and (arith_logic m a) (arith_logic m b)
    | not ?a => arith_logic m a
    | ?a -> ?b => Bool.and (arith_logic m a) (arith_logic m b)
    | _ => plain_arith m false t
    end
  with arith_logic (m : memo) (t : constr) : bool :=
    let k := code m t in
    if Int.equal k 0 then false
    else if Int.equal k 1 then true else if Int.equal k 2 then true
    else if Int.equal k 9 then arith_logic_old m t
    else
      (match Constr.Unsafe.kind t with
       | Constr.Unsafe.App _ args =>
           if Int.equal k 6 then arith_logic m (Array.get args 0)
           else Bool.and (arith_logic m (Array.get args 0)) (arith_logic m (Array.get args 1))
       | _ => arith_logic_old m t
       end).
  Ltac2 is_bad (m : memo) (f : constr) : bool :=
    match Constr.Unsafe.kind f with
    | Constr.Unsafe.Constant c _ =>
        (match FMap.find_opt c (m.(mb)) with
         | Some b => b
         | None => let b := List.exist (Constr.equal f) (m.(mbad)) in m.(mb) := FMap.add c b (m.(mb)); b
         end)
    | _ => List.exist (Constr.equal f) (m.(mbad))
    end.
  Ltac2 rec clean (m : memo) (c : constr) : bool :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.App f args =>
        let walk () := Array.fold_left (fun b a => if b then clean m a else false) true args in
        (match Constr.Unsafe.kind f with
         | Constr.Unsafe.Constant _ _ => if is_bad m f then false else walk ()
         | Constr.Unsafe.Cast _ _ _ => if is_bad m f then false else walk ()
         | Constr.Unsafe.Lambda _ _ => false
         | Constr.Unsafe.Case _ _ _ _ _ => false
         | Constr.Unsafe.LetIn _ _ _ => false
         | Constr.Unsafe.Prod _ _ => if clean m f then walk () else false
         | Constr.Unsafe.App _ _ => if is_bad m f then false else (if clean m f then walk () else false)
         | _ => walk ()
         end)
    | Constr.Unsafe.Constant _ _ => if is_bad m c then false else true
    | Constr.Unsafe.Prod b body => if clean m (Constr.Binder.type b) then clean m body else false
    | Constr.Unsafe.Lambda _ _ => false
    | Constr.Unsafe.Case _ _ _ _ _ => false
    | Constr.Unsafe.LetIn _ _ _ => false
    | _ => true
    end.
End SFC.
(* [comment removed for export] *)
Module SFP.
  Import Ltac2.
  Ltac2 prune_with (m : SFC.memo) (keep : constr -> bool) : unit :=
    let hs := Control.hyps () in
    let ids := List.map_filter (fun h => let (id, body, ty) := h in
                  match body with
                  | Some _ => None
                  | None => if SFC.arith_logic m ty then (if keep ty then None else Some id) else None
                  end) hs in
    match ids with [] => () | _ :: _ => Std.clear ids end.
  Ltac2 prune_plain () : unit := let m := SFC.memo_new () in prune_with m (fun ty => SFC.plain_arith m false ty).
  Ltac2 prune_clean () : unit :=
    let m := SFC.memo_new () in prune_with m (fun ty => if SFC.plain_arith m false ty then SFC.clean m ty else false).
  Ltac2 prune_rel () : unit :=
    let m := SFC.memo_new () in
    let gv := SF2.vars_of [] (Control.goal ()) in
    prune_with m (fun ty => if SFC.plain_arith m false ty then SFC.clean m ty
                            else if SFC.plain_arith m true ty then (if SF2.meets (SF2.vars_of [] ty) gv then SFC.clean m ty else false)
                            else false).
  Ltac2 prune_rel2 () : unit :=
    let m := SFC.memo_new () in
    let gv := SF2.vars_of [] (Control.goal ()) in
    prune_with m (fun ty => if SFC.plain_arith m false ty then true else SF2.meets (SF2.vars_of [] ty) gv).
  Ltac2 hide_poison () : unit :=
    let m := SFC.memo_new () in
    List.iter (fun h => let (id, body, ty) := h in
      match body with
      | Some _ => ()
      | None =>
          if SFC.arith_logic m ty then
            (if (if SFC.plain_arith m false ty then SFC.clean m ty else false) then ()
             else let c := Control.hyp id in
                  ltac1:(c |- lazymatch type of c with ?T => change T with (sf_hide T) in c end) (Ltac1.of_constr c))
          else ()
      end) (Control.hyps ()).
End SFP.
Ltac zify_prune_rel2_sf2 := ltac2:(FFRel.prune_rel2_1 ()).
Ltac zify_prune_plain ::= ltac2:(Control.enter SFP.prune_plain).
Ltac zify_prune_clean ::= ltac2:(Control.enter SFP.prune_clean).
Ltac zify_prune_neg ::= ltac2:(Control.enter SFP.prune_rel).
Ltac zify_prune_rel2 ::= ltac2:(Control.enter SFP.prune_rel2).
Ltac sf_hide_poison ::= ltac2:(Control.enter SFP.hide_poison).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Module ONED.
  Import Ltac2.
  Ltac2 is_or (t : constr) : bool :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App f args => if DH.is_ref f reference:(or) then Int.equal (Array.length args) 2 else false
    | _ => false
    end.
  Ltac2 rec count_shared (xs : ident list) (ys : ident list) (acc : int) : int :=
    match xs with
    | [] => acc
    | x :: rest => count_shared rest ys (if List.exist (Ident.equal x) ys then Int.add acc 1 else acc)
    end.
  Ltac2 rec dedup (xs : ident list) (acc : ident list) : ident list :=
    match xs with
    | [] => acc
    | x :: rest => if List.exist (Ident.equal x) acc then dedup rest acc else dedup rest (x :: acc)
    end.
  (* [comment removed for export] *)
  Ltac2 ors () : (ident * int) list :=
    let gv := dedup (SF2.vars_of [] (Control.goal ())) [] in
    List.map_filter (fun h =>
      let (id, body, ty) := h in
      match body with
      | Some _ => None
      | None => if is_or ty then (if SF2.arith_logic ty then Some (id, count_shared (dedup (SF2.vars_of [] ty) []) gv 0) else None) else None
      end) (Control.hyps ()).
  Ltac2 rec take (k : int) (l : 'a list) : 'a list :=
    if Int.le k 0 then [] else match l with [] => [] | x :: r => x :: take (Int.sub k 1) r end.
  Ltac2 rec insert (p : ident * int) (l : (ident * int) list) : (ident * int) list :=
    match l with
    | [] => [p]
    | q :: r => let (_, kp) := p in let (_, kq) := q in if Int.gt kp kq then p :: l else q :: insert p r
    end.
  Ltac2 rec sort (l : (ident * int) list) (acc : (ident * int) list) : (ident * int) list :=
    match l with [] => acc | p :: r => sort r (insert p acc) end.
  Ltac2 run () : unit :=
    let all := ors () in
    let shared := List.filter (fun p => let (_, k) := p in Int.gt k 0) (sort all []) in
    (* [comment removed for export] *)
    (match shared with _ :: _ :: _ => () | _ => Control.zero (Tactic_failure None) end);
    let ranked := take 3 shared in
    let ids := List.map (fun p => let (id, _) := p in id) all in
    let rec go (l : (ident * int) list) : unit :=
      match l with
      | [] => Control.zero (Tactic_failure None)
      | p :: rest =>
          let (keep, _) := p in
          Control.plus (fun () =>
              Control.once (fun () =>
                let drop := List.filter (fun i => Bool.neg (Ident.equal i keep)) ids in
                (match drop with [] => () | _ :: _ => Std.clear drop end);
                ltac1:(Zify.zify; xlia zchecker)))
            (fun _ => go rest)
      end in
    go ranked.
End ONED.
Ltac sf_one_disj := ltac2:(Control.enter ONED.run).
(* [comment removed for export] *)
Ltac sf_ivl_prover_e1 := first [ sf_cheap_tslia | tryif sf_lia_refuted then fail else tslia ].
Ltac dg_conj_e1 :=
  lazymatch goal with
  | |- True => exact I
  | |- _ /\ _ => split; [ tlia | dg_conj_e1 ]
  | |- _ => tlia
  end.
Ltac sf_ivl_prover ::= first [ sf_cheap_tslia | tryif sf_lia_refuted then fail else first [ sf_unhide; sf_one_disj | tslia ] ].
Ltac dg_conj ::=
  lazymatch goal with
  | |- True => exact I
  | |- _ /\ _ => split; [ first [ sf_unhide; sf_one_disj | tlia ] | dg_conj ]
  | |- _ => first [ sf_unhide; sf_one_disj | tlia ]
  end.
