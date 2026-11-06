(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Cells.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Exec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Step.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From Ltac2 Require Ltac2.
Module StoreFast.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac.

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
            | tr_sb H (bytes_at_write_other_sb segs m a bs X b) (bytes_at_write_other_sb0 segs m a bs X b) chk_sb b X A2 constr:(Z.of_nat (@length byte bs2))
            | apply (bytes_at_write_other_n segs m a bs A2 bs2 n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ tr_lit H (rw_cells_frame_lit segs m a bs X b A2 cs2 SC) b A2 constr:(Z.of_nat (cells_size cs2))
            | tr_sb H (rw_cells_frame_sb segs m a bs X b) (rw_cells_frame_sb0 segs m a bs X b) chk_sb b X A2 constr:(Z.of_nat (cells_size cs2))
            | apply (rw_cells_frame_n segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ tr_lit H (ro_cells_frame_lit segs m a bs X b A2 cs2 SC) b A2 constr:(Z.of_nat (cells_size cs2))
            | tr_sb H (ro_cells_frame_sb segs m a bs X b) (ro_cells_frame_sb0 segs m a bs X b) chk_sb b X A2 constr:(Z.of_nat (cells_size cs2))
            | apply (ro_cells_frame_n segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ tr_lit H (u8arr_frame_lit segs m a bs X b A2 xs SC) b A2 constr:(Z.of_nat (@length byte xs))
            | tr_sb H (u8arr_frame_sb segs m a bs X b) (u8arr_frame_sb0 segs m a bs X b) chk_sb b X A2 constr:(Z.of_nat (@length byte xs))
            | apply (u8arr_frame_n segs m A2 xs a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ tr_lit H (u32arr_frame_lit segs m a bs X b A2 xs SC) b A2 constr:((4 * Z.of_nat (@length word xs))%Z)
            | tr_sb H (u32arr_frame_sb segs m a bs X b) (u32arr_frame_sb0 segs m a bs X b) chk_sb b X A2 constr:((4 * Z.of_nat (@length word xs))%Z)
            | apply (u32arr_frame_n segs m A2 xs a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ tr_lit H (u64arr_frame_lit segs m a bs X b A2 xs SC) b A2 constr:((8 * Z.of_nat (@length word xs))%Z)
            | tr_sb H (u64arr_frame_sb segs m a bs X b) (u64arr_frame_sb0 segs m a bs X b) chk_sb b X A2 constr:((8 * Z.of_nat (@length word xs))%Z)
            | apply (u64arr_frame_n segs m A2 xs a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ tr_lit H (u8ro_frame_lit segs m a bs X b A2 xs SC) b A2 constr:(Z.of_nat (@length byte xs))
            | tr_sb H (u8ro_frame_sb segs m a bs X b) (u8ro_frame_sb0 segs m a bs X b) chk_sb b X A2 constr:(Z.of_nat (@length byte xs))
            | apply (u8ro_frame_n segs m A2 xs a bs n Hn Ha Hl) in H; [ | simpl_sizes_goal; tslia ]
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
(* [comment removed for export] *)
Ltac disjoint_split :=
  lazymatch goal with
  | |- True => exact I
  | |- _ /\ _ => split; [ tslia | disjoint_split ]
  | |- _ => tslia
  end.
Ltac disjoint_goal :=
  cbv [disjoint_from fst snd];
  simpl_sizes_goal;
  disjoint_split.

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
            | tr_sb H (bytes_at_transport_sb segs m m' X B) (bytes_at_transport_sb0 segs m m' X B) chks_sb B X A2 constr:(Z.of_nat (@length byte bs2))
            | apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ tr_lits H (rw_cells_transport_lit segs m m' X B A2 cs2 CC) B A2 constr:(Z.of_nat (cells_size cs2))
            | tr_sb H (rw_cells_transport_sb segs m m' X B) (rw_cells_transport_sb0 segs m m' X B) chks_sb B X A2 constr:(Z.of_nat (cells_size cs2))
            | apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ tr_lits H (ro_cells_transport_lit segs m m' X B A2 cs2 CC) B A2 constr:(Z.of_nat (cells_size cs2))
            | tr_sb H (ro_cells_transport_sb segs m m' X B) (ro_cells_transport_sb0 segs m m' X B) chks_sb B X A2 constr:(Z.of_nat (cells_size cs2))
            | apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ tr_lits H (u8arr_transport_lit segs m m' X B A2 xs CC) B A2 constr:(Z.of_nat (@length byte xs))
            | tr_sb H (u8arr_transport_sb segs m m' X B) (u8arr_transport_sb0 segs m m' X B) chks_sb B X A2 constr:(Z.of_nat (@length byte xs))
            | apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ tr_lits H (u32arr_transport_lit segs m m' X B A2 xs CC) B A2 constr:((4 * Z.of_nat (@length word xs))%Z)
            | tr_sb H (u32arr_transport_sb segs m m' X B) (u32arr_transport_sb0 segs m m' X B) chks_sb B X A2 constr:((4 * Z.of_nat (@length word xs))%Z)
            | apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ tr_lits H (u64arr_transport_lit segs m m' X B A2 xs CC) B A2 constr:((8 * Z.of_nat (@length word xs))%Z)
            | tr_sb H (u64arr_transport_sb segs m m' X B) (u64arr_transport_sb0 segs m m' X B) chks_sb B X A2 constr:((8 * Z.of_nat (@length word xs))%Z)
            | apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | disjoint_goal ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ tr_lits H (u8ro_transport_lit segs m m' X B A2 xs CC) B A2 constr:(Z.of_nat (@length byte xs))
            | tr_sb H (u8ro_transport_sb segs m m' X B) (u8ro_transport_sb0 segs m m' X B) chks_sb B X A2 constr:(Z.of_nat (@length byte xs))
            | apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | disjoint_goal ]
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

(* [comment removed for export] *)
From Stdlib Require Zify.
From Stdlib Require PreOmega.
From Ltac2 Require FSet.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaTuning.
Module LiaClosure.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.micromega.Lia.
Import Stdlib.micromega.Zify Stdlib.omega.PreOmega.
Import Ltac2.Ltac2 Ltac2.FSet.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaTuning StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

#[global] Set Default Proof Mode "Classic".

Module LC.
Import Ltac2.

Ltac2 Type vset := ident FSet.t.
Ltac2 vempty () : vset := FSet.empty FSet.Tags.ident_tag.

(* [comment removed for export] *)
Ltac2 Type budget := { mutable left : int }.
Ltac2 rec vars_acc_b (num : constr list) (bg : budget) (acc : vset) (t : constr) : vset :=
  if Int.le (bg.(left)) 0 then acc else
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Var id => FSet.add id acc
  | Constr.Unsafe.App f args =>
      (match Constr.Unsafe.kind f with
       | Constr.Unsafe.Constructor _ _ => if List.exist (Constr.equal f) num then acc
           else (bg.(left) := Int.sub (bg.(left)) 1; Array.fold_left (vars_acc_b num bg) acc args)
       | _ => (bg.(left) := Int.sub (bg.(left)) 1; Array.fold_left (vars_acc_b num bg) (vars_acc_b num bg acc f) args)
       end)
  | Constr.Unsafe.Prod b c => vars_acc_b num bg (vars_acc_b num bg acc (Constr.Binder.type b)) c
  | Constr.Unsafe.Lambda b c => vars_acc_b num bg (vars_acc_b num bg acc (Constr.Binder.type b)) c
  | Constr.Unsafe.LetIn b v c => vars_acc_b num bg (vars_acc_b num bg (vars_acc_b num bg acc (Constr.Binder.type b)) v) c
  | Constr.Unsafe.Cast c _ ty => vars_acc_b num bg (vars_acc_b num bg acc c) ty
  | Constr.Unsafe.Case _ _ _ scr brs => Array.fold_left (vars_acc_b num bg) (vars_acc_b num bg acc scr) brs
  | Constr.Unsafe.Proj _ _ c => vars_acc_b num bg acc c
  | _ => acc
  end.
Ltac2 numerals () : constr list := ['Zpos; 'Zneg; 'Npos; 'xI; 'xO].
Ltac2 vars_acc_n (num : constr list) (acc : vset) (t : constr) : vset := vars_acc_b num { left := 300 } acc t.
Ltac2 vars_acc (acc : vset) (t : constr) : vset := vars_acc_n (numerals ()) acc t.

(* [comment removed for export] *)
Ltac2 Type heads := { h_rel : constr list; h_not : constr; h_iff : constr; h_hide : constr;
                      h_and : constr; h_or : constr; h_eq : constr; h_le : constr;
                      h_true : constr; h_false : constr; h_types : constr list }.
Ltac2 mk_heads () : heads :=
  { h_rel := ['@Z.le; '@Z.lt; '@Z.ge; '@Z.gt; '@lt; '@ge; '@gt; '@N.le; '@N.lt; '@Z.divide];
    h_not := '@not; h_iff := '@iff; h_hide := '@sf_hide; h_and := '@and; h_or := '@or; h_eq := '@eq; h_le := '@le;
    h_true := 'True; h_false := 'False; h_types := ['Z; 'nat; 'N; 'bool] }.
Ltac2 cmem (c : constr) (l : constr list) : bool := List.exist (Constr.equal c) l.

(* [comment removed for export] *)
Ltac2 rec fast_plain (hd : heads) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      match Constr.Unsafe.kind h with
      | Constr.Unsafe.Constant _ _ =>
          if cmem h (hd.(h_rel)) then true
          else if Constr.equal h (hd.(h_hide)) then fast_plain hd (Array.get args 0)
          else false
      | Constr.Unsafe.Ind _ _ =>
          if Constr.equal h (hd.(h_and)) then (if fast_plain hd (Array.get args 0) then fast_plain hd (Array.get args 1) else false)
          else if Constr.equal h (hd.(h_eq)) then cmem (Array.get args 0) (hd.(h_types))
          else Constr.equal h (hd.(h_le))
      | _ => false
      end
  | Constr.Unsafe.Ind _ _ => if Constr.equal t (hd.(h_true)) then true else Constr.equal t (hd.(h_false))
  | _ => false
  end.

(* [comment removed for export] *)
Ltac2 rec fast_al (hd : heads) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      match Constr.Unsafe.kind h with
      | Constr.Unsafe.Constant _ _ =>
          if cmem h (hd.(h_rel)) then true
          else if Constr.equal h (hd.(h_not)) then fast_al hd (Array.get args 0)
          else if Constr.equal h (hd.(h_iff)) then (if fast_al hd (Array.get args 0) then fast_al hd (Array.get args 1) else false)
          else if Constr.equal h (hd.(h_hide)) then fast_al hd (Array.get args 0)
          else false
      | Constr.Unsafe.Ind _ _ =>
          if Constr.equal h (hd.(h_and)) then (if fast_al hd (Array.get args 0) then fast_al hd (Array.get args 1) else false)
          else if Constr.equal h (hd.(h_or)) then (if fast_al hd (Array.get args 0) then fast_al hd (Array.get args 1) else false)
          else if Constr.equal h (hd.(h_eq)) then cmem (Array.get args 0) (hd.(h_types))
          else Constr.equal h (hd.(h_le))
      | _ => false
      end
  | Constr.Unsafe.Prod b c => if fast_al hd (Constr.Binder.type b) then fast_al hd c else false
  | Constr.Unsafe.Ind _ _ => if Constr.equal t (hd.(h_true)) then true else Constr.equal t (hd.(h_false))
  | _ => false
  end.

Ltac2 meets (a : vset) (b : vset) : bool := Bool.neg (FSet.is_empty (FSet.inter a b)).

(* [comment removed for export] *)
Ltac2 rec closure (vs : vset) (cands : (ident * vset) list) (fuel : int) : vset :=
  if Int.le fuel 0 then vs else
  let (vs2, rest, changed) := List.fold_left (fun (acc : vset * (ident * vset) list * bool) (c : ident * vset) =>
      let (vs1, rest1, ch) := acc in
      let (id, hv) := c in
      if (if FSet.mem id vs1 then true else meets hv vs1)
      then (FSet.add id (FSet.union hv vs1), rest1, true)
      else (vs1, c :: rest1, ch)) (vs, [], false) cands in
  if changed then closure vs2 rest (Int.sub fuel 1) else vs2.

Ltac2 prune (logic : bool) (sec : bool) : unit :=
  let hd := mk_heads () in
  let num := numerals () in
  let vars (t : constr) := vars_acc_n num (vempty ()) t in
  let hs := Control.hyps () in
  let vg := vars (Control.goal ()) in
  (* [comment removed for export] *)
  let pc := List.map_filter (fun h => let (id, body, ty) := h in
      match body with
      | Some b => if cmem ty (hd.(h_types)) then Some (id, vars b) else None
      | None => if fast_plain hd ty then Some (id, vars ty) else None
      end) hs in
  (* [comment removed for export] *)
  let lc := if logic then List.map_filter (fun h => let (id, body, ty) := h in
      match body with
      | Some _ => None
      | None => if fast_plain hd ty then None else if fast_al hd ty then
                  (let hv := vars ty in if meets hv vg then Some (id, hv) else None) else None
      end) hs else [] in
  let vl := List.fold_left (fun (acc : vset) (c : ident * vset) => let (_, hv) := c in FSet.union hv acc) vg lc in
  let vs := closure vl pc 50 in
  (* [comment removed for export] *)
  let closed := List.map_filter (fun (c : ident * vset) => let (i, hv) := c in if FSet.is_empty hv then Some i else None) pc in
  let keep (id : ident) := if FSet.mem id vs then true
    else if List.exist (fun (c : ident * vset) => let (i, _) := c in Ident.equal i id) lc then true
    else List.exist (Ident.equal id) closed in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
      match body with
      | Some _ => None
      | None => if keep id then None
                else if zt_is_local id then (if zt_is_prop ty then Some id else None)
                else if sec then (if fast_al hd ty then Some id else None) else None
      end) hs in
  match ids with [] => () | _ :: _ => Std.clear ids end.
End LC.

Ltac lc_unhide := repeat match goal with H : sf_hide _ |- _ => unfold sf_hide in H end.
(* [comment removed for export] *)
Ltac lia0_prune := ltac2:(Control.enter (fun () => LC.prune false false)); lc_unhide.
Ltac lia0_prune_logic := ltac2:(Control.enter (fun () => LC.prune true false)); lc_unhide.
Ltac lia0_prune_s := ltac2:(Control.enter (fun () => LC.prune false true)); lc_unhide.
Ltac lia0_prune_logic_s := ltac2:(Control.enter (fun () => LC.prune true true)); lc_unhide.

(* [comment removed for export] *)
Ltac lia4 :=
  first [ lia0_prune_s; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | lia0_prune_logic_s; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | lia3 ].

(* [comment removed for export] *)
Ltac tlia4 :=
  first [ lia0_prune_s; Zify.zify; xlia zchecker
        | lia0_prune_logic_s; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker
        | sf_unhide;
          first [ zify_prune_neg; Zify.zify; xlia zchecker
                | zify_prune_plain; Zify.zify; xlia zchecker
                | Zify.zify; xlia zchecker ] ].

(* [comment removed for export] *)
Ltac lia4l :=
  first [ lia0_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | lia0_prune_logic; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | lia3 ].
Ltac tlia4l :=
  first [ lia0_prune; Zify.zify; xlia zchecker
        | lia0_prune_logic; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker
        | sf_unhide;
          first [ zify_prune_neg; Zify.zify; xlia zchecker
                | zify_prune_plain; Zify.zify; xlia zchecker
                | Zify.zify; xlia zchecker ] ].
End LiaClosure.

(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac.
Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Inductive sc_dj (A S A2 n2 : Z) : Prop := sc_djI : A2 + n2 <= A \/ A + S <= A2 -> sc_dj A S A2 n2.
Inductive sc_in (W : list ivl) (A S : Z) : Prop := sc_inI : inside W A S -> sc_in W A S.
Inductive sc_no (A S A2 n2 : Z) : Prop := sc_noI : sc_no A S A2 n2.
Inductive sc_noin (W : list ivl) (A S : Z) : Prop := sc_noinI : sc_noin W A S.
Inductive sc_hidden : Prop := sc_hiddenI : sc_hidden.

(* [comment removed for export] *)
Definition sc_fits (k n S : Z) : bool := (0 <=? k) && (0 <=? n) && (k + n <=? S).

Lemma sc_fits_spec : forall k n S, sc_fits k n S = true -> 0 <= k /\ 0 <= n /\ k + n <= S.
Proof.
  intros k n S H. unfold sc_fits in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1, H2, H3. lia.
Qed.

Lemma sc_bounds : forall A S k n, 0 <= A /\ A + S <= 2^64 -> sc_fits k n S = true ->
  0 <= A + k /\ A + k + n <= 2^64.
Proof. intros A S k n HB Hk. apply sc_fits_spec in Hk. lia. Qed.

Lemma sc_dj_sub : forall A S A2 n2 k n, sc_dj A S A2 n2 -> sc_fits k n S = true ->
  A2 + n2 <= A + k \/ A + k + n <= A2.
Proof. intros A S A2 n2 k n [HD] Hk. apply sc_fits_spec in Hk. lia. Qed.

Lemma sc_in_sub : forall W A S k n, sc_in W A S -> sc_fits k n S = true -> inside W (A + k) n.
Proof.
  intros W A S k n [HI] Hk. apply sc_fits_spec in Hk.
  induction W as [|[lo hi] W IH]; cbn in HI |- *; [exact HI|].
  destruct HI as [HI|HI]; [left; lia | right; apply IH; exact HI].
Qed.

(* [comment removed for export] *)
Section WithSegsE.
Variable segs : list Segment.
Lemma bytes_at_write_other_e : forall m m' a bs c cs (n : Z), m' = write_to_mem m (wa a) bs ->
  Z.of_nat (length bs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  bytes_at segs m c cs -> (c + Z.of_nat (length cs) <= a \/ a + n <= c)%Z -> bytes_at segs m' c cs.
Proof. intros m m' a bs c cs n -> Hn Ha Hl H Hd. eapply bytes_at_write_other_n; eauto. Qed.
Lemma wr_at_write_e : forall m m' A n a bs, m' = write_to_mem m a bs -> wr_at segs m A n -> wr_at segs m' A n.
Proof. intros m m' A n a bs -> H. apply wr_at_write. exact H. Qed.
Lemma rw_cells_frame_e : forall m m' A cs (a : Z) bs (n : Z), m' = write_to_mem m (wa a) bs ->
  Z.of_nat (length bs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  rw_cells segs m A cs -> (A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z -> rw_cells segs m' A cs.
Proof. intros m m' A cs a bs n -> Hn Ha Hl H Hd. eapply rw_cells_frame_n; eauto. Qed.
Lemma ro_cells_frame_e : forall m m' A cs (a : Z) bs (n : Z), m' = write_to_mem m (wa a) bs ->
  Z.of_nat (length bs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  ro_cells segs m A cs -> (A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z -> ro_cells segs m' A cs.
Proof. intros m m' A cs a bs n -> Hn Ha Hl H Hd. eapply ro_cells_frame_n; eauto. Qed.
Lemma u8arr_frame_e : forall m m' A bs a xs (n : Z), m' = write_to_mem m (wa a) xs ->
  Z.of_nat (length xs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  u8arr segs m A bs -> (A + Z.of_nat (length bs) <= a \/ a + n <= A)%Z -> u8arr segs m' A bs.
Proof. intros m m' A bs a xs n -> Hn Ha Hl H Hd. eapply u8arr_frame_n; eauto. Qed.
Lemma u32arr_frame_e : forall m m' A ws a xs (n : Z), m' = write_to_mem m (wa a) xs ->
  Z.of_nat (length xs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  u32arr segs m A ws -> (A + 4 * Z.of_nat (length ws) <= a \/ a + n <= A)%Z -> u32arr segs m' A ws.
Proof. intros m m' A ws a xs n -> Hn Ha Hl H Hd. eapply u32arr_frame_n; eauto. Qed.
Lemma u64arr_frame_e : forall m m' A ws a xs (n : Z), m' = write_to_mem m (wa a) xs ->
  Z.of_nat (length xs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  u64arr segs m A ws -> (A + 8 * Z.of_nat (length ws) <= a \/ a + n <= A)%Z -> u64arr segs m' A ws.
Proof. intros m m' A ws a xs n -> Hn Ha Hl H Hd. eapply u64arr_frame_n; eauto. Qed.
Lemma u8ro_frame_e : forall m m' A bs a xs (n : Z), m' = write_to_mem m (wa a) xs ->
  Z.of_nat (length xs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  u8ro segs m A bs -> (A + Z.of_nat (length bs) <= a \/ a + n <= A)%Z -> u8ro segs m' A bs.
Proof. intros m m' A bs a xs n -> Hn Ha Hl H Hd. eapply u8ro_frame_n; eauto. Qed.
Lemma stk_write_e : forall m m' lo hi a bs (n : Z), m' = write_to_mem m (wa a) bs ->
  Z.of_nat (length bs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  stk segs m lo hi -> stk segs m' lo hi.
Proof. intros m m' lo hi a bs n -> Hn Ha Hl H. eapply stk_write_n; eauto. Qed.
Lemma wmono_write_e : forall m0 m m' a bs, m' = write_to_mem m a bs -> wmono segs m0 m -> wmono segs m0 m'.
Proof. intros m0 m m' a bs -> H. apply wmono_write. exact H. Qed.
Lemma mem_inv_store_cbytes_e : forall m m' a c', m' = write_to_mem m a (cbytes c') ->
  mem_inv segs m -> cell_wf c' -> store_ok segs m a (csize c') = true -> mem_inv segs m'.
Proof. intros m m' a c' -> H1 H2 H3. apply mem_inv_store_cbytes; assumption. Qed.
Lemma rw_cells_write_e : forall m m' A cs k c c', m' = write_to_mem m (wa (A + Z.of_nat k)) (cbytes c') ->
  rw_cells segs m A cs -> cell_at cs k = Some c -> csize c' = csize c -> cell_wf c' ->
  rw_cells segs m' A (cell_upd cs k c').
Proof. intros m m' A cs k c c' -> H1 H2 H3 H4. exact (rw_cells_write segs m A cs k c c' H1 H2 H3 H4). Qed.
End WithSegsE.
Lemma munch_write_e : forall W m0 m m' a bs (n : Z), m' = write_to_mem m (wa a) bs ->
  Z.of_nat (length bs) = n -> (0 <= a)%Z -> (a + n <= 2^64)%Z ->
  munch W m0 m -> inside W a n -> munch W m0 m'.
Proof. intros W m0 m m' a bs n -> Hn Ha Hl H Hin. eapply munch_write_n; eauto. Qed.

(* [comment removed for export] *)
Lemma sc_wa1 : forall x c1 k c2, (c1 + k =? c2) = true -> Z_to_bv 64 (x + c2) = wa (x + c1 + k).
Proof. intros x c1 k c2 H. apply Z.eqb_eq in H. unfold wa. rewrite <- H, Z.add_assoc. reflexivity. Qed.
Lemma sc_wa2 : forall x k c2, (k =? c2) = true -> Z_to_bv 64 (x + c2) = wa (x + k).
Proof. intros x k c2 H. apply Z.eqb_eq in H. unfold wa. rewrite <- H. reflexivity. Qed.
Lemma sc_wa3 : forall x c1 k, (c1 + k =? 0) = true -> Z_to_bv 64 x = wa (x + c1 + k).
Proof. intros x c1 k H. apply Z.eqb_eq in H. unfold wa. rewrite <- Z.add_assoc, H, Z.add_0_r. reflexivity. Qed.
Lemma sc_wa4 : forall x k, (k =? 0) = true -> Z_to_bv 64 x = wa (x + k).
Proof. intros x k H. apply Z.eqb_eq in H. unfold wa. rewrite H, Z.add_0_r. reflexivity. Qed.
Ltac sc_natlit n := lazymatch n with O => constr:(true) | S ?k => sc_natlit k | _ => constr:(false) end.
Ltac sc_zlit_or_nat t :=
  lazymatch t with
  | Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac
  | Z.of_nat ?n => let b := sc_natlit n in lazymatch b with true => idtac end
  end.
Ltac sc_addr_eq :=
  lazymatch goal with
  | |- Z_to_bv 64 (?x + ?c2) = wa (?x + ?c1 + ?k) => sc_zlit_or_nat c2; sc_zlit_or_nat c1; sc_zlit_or_nat k; exact (sc_wa1 x c1 k c2 eq_refl)
  | |- Z_to_bv 64 (?x + ?c2) = wa (?x + ?k) => sc_zlit_or_nat c2; sc_zlit_or_nat k; exact (sc_wa2 x k c2 eq_refl)
  | |- Z_to_bv 64 ?x = wa (?x + ?c1 + ?k) => sc_zlit_or_nat c1; sc_zlit_or_nat k; exact (sc_wa3 x c1 k eq_refl)
  | |- Z_to_bv 64 ?x = wa (?x + ?k) => sc_zlit_or_nat k; exact (sc_wa4 x k eq_refl)
  end.
(* [comment removed for export] *)
Ltac addr_eq_tac_cached :=
  first [ sc_addr_eq
        | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(* [comment removed for export] *)
Ltac sc_spine_closed cs :=
  lazymatch cs with
  | nil => constr:(true)
  | cons ?c ?tl =>
      lazymatch c with
      | C8 _ => sc_spine_closed tl | C4 _ => sc_spine_closed tl | C2 _ => sc_spine_closed tl | C1 _ => sc_spine_closed tl
      | CB ?n _ => let b := sc_natlit n in lazymatch b with true => sc_spine_closed tl | false => constr:(false) end
      | _ => constr:(false)
      end
  | _ => constr:(false)
  end.
Ltac sc_key X :=
  lazymatch X with
  | Z.of_nat (cells_size ?cs) =>
      let b := sc_spine_closed cs in
      lazymatch b with
      | true => let v := eval cbv [cells_size csize Nat.add] in (cells_size cs) in
                eval vm_compute in (Z.of_nat v)
      | false => X
      end
  | _ => X
  end.

(* [comment removed for export] *)
Ltac sc_hide_once :=
  lazymatch goal with
  | _ : sc_hidden |- _ => idtac
  | _ => sf_hide_poison; let SCH := fresh "SCH" in assert (SCH : sc_hidden) by exact sc_hiddenI
  end.
Ltac sc_unhide :=
  lazymatch goal with
  | SCH : sc_hidden |- _ => clear SCH; sf_unhide
  | _ => idtac
  end.

(* [comment removed for export] *)
Ltac sc_gonly := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.

(* [comment removed for export] *)
Ltac sc_dj_ensure A S A2 X kyes kno :=
  first [ match goal with DJ : sc_dj A S A2 X |- _ => kyes DJ end
        | match goal with NO : sc_no A S A2 X |- _ => kno end
        | let DJ := fresh "SCdj" in
          tryif (sc_hide_once; assert (DJ : sc_dj A S A2 X) by (apply sc_djI; simpl_sizes_goal; first [ sc_gonly | tslia ]))
          then kyes DJ
          else (let NO := fresh "SCno" in assert (NO : sc_no A S A2 X) by exact (sc_noI A S A2 X); kno) ].

Ltac sc_in_ensure W A S kyes kno :=
  first [ match goal with IN : sc_in W A S |- _ => kyes IN end
        | match goal with NO : sc_noin W A S |- _ => kno end
        | let IN := fresh "SCin" in
          tryif (sc_hide_once; assert (IN : sc_in W A S) by (apply sc_inI; cbn [inside]; first [ sc_gonly | tslia ]))
          then kyes IN
          else (let NO := fresh "SCnoin" in assert (NO : sc_noin W A S) by exact (sc_noinI W A S); kno) ].

(* [comment removed for export] *)
Ltac transport_chunks_cached segs m m' Heqm a bs n Hn Ha Hl A S kn Hk :=
  (repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      let X := sc_key constr:(Z.of_nat (length bs2)) in
      sc_dj_ensure A S A2 X
        ltac:(fun DJ => apply (bytes_at_write_other_e segs m m' a bs A2 bs2 n Heqm Hn Ha Hl) in H;
                        [ | exact (sc_dj_sub A S A2 X (Z.of_nat kn) n DJ Hk) ])
        ltac:(first [ apply (bytes_at_write_other_e segs m m' a bs A2 bs2 n Heqm Hn Ha Hl) in H; [ | sc_hide_once; simpl_sizes_goal; tslia ]
                    | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ])
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write_e segs m m' A2 n2 (wa a) bs Heqm) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      let X := sc_key constr:(Z.of_nat (cells_size cs2)) in
      sc_dj_ensure A S A2 X
        ltac:(fun DJ => apply (rw_cells_frame_e segs m m' A2 cs2 a bs n Heqm Hn Ha Hl) in H;
                        [ | exact (sc_dj_sub A S A2 X (Z.of_nat kn) n DJ Hk) ])
        ltac:(first [ apply (rw_cells_frame_e segs m m' A2 cs2 a bs n Heqm Hn Ha Hl) in H; [ | sc_hide_once; simpl_sizes_goal; tslia ]
                    | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ])
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      let X := sc_key constr:(Z.of_nat (cells_size cs2)) in
      sc_dj_ensure A S A2 X
        ltac:(fun DJ => apply (ro_cells_frame_e segs m m' A2 cs2 a bs n Heqm Hn Ha Hl) in H;
                        [ | exact (sc_dj_sub A S A2 X (Z.of_nat kn) n DJ Hk) ])
        ltac:(first [ apply (ro_cells_frame_e segs m m' A2 cs2 a bs n Heqm Hn Ha Hl) in H; [ | sc_hide_once; simpl_sizes_goal; tslia ]
                    | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ])
  | H : u8arr segs m ?A2 ?xs |- _ =>
      let X := constr:(Z.of_nat (length xs)) in
      sc_dj_ensure A S A2 X
        ltac:(fun DJ => apply (u8arr_frame_e segs m m' A2 xs a bs n Heqm Hn Ha Hl) in H;
                        [ | exact (sc_dj_sub A S A2 X (Z.of_nat kn) n DJ Hk) ])
        ltac:(first [ apply (u8arr_frame_e segs m m' A2 xs a bs n Heqm Hn Ha Hl) in H; [ | sc_hide_once; simpl_sizes_goal; tslia ]
                    | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ])
  | H : u32arr segs m ?A2 ?xs |- _ =>
      let X := constr:(4 * Z.of_nat (length xs)) in
      sc_dj_ensure A S A2 X
        ltac:(fun DJ => apply (u32arr_frame_e segs m m' A2 xs a bs n Heqm Hn Ha Hl) in H;
                        [ | exact (sc_dj_sub A S A2 X (Z.of_nat kn) n DJ Hk) ])
        ltac:(first [ apply (u32arr_frame_e segs m m' A2 xs a bs n Heqm Hn Ha Hl) in H; [ | sc_hide_once; simpl_sizes_goal; tslia ]
                    | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ])
  | H : u64arr segs m ?A2 ?xs |- _ =>
      let X := constr:(8 * Z.of_nat (length xs)) in
      sc_dj_ensure A S A2 X
        ltac:(fun DJ => apply (u64arr_frame_e segs m m' A2 xs a bs n Heqm Hn Ha Hl) in H;
                        [ | exact (sc_dj_sub A S A2 X (Z.of_nat kn) n DJ Hk) ])
        ltac:(first [ apply (u64arr_frame_e segs m m' A2 xs a bs n Heqm Hn Ha Hl) in H; [ | sc_hide_once; simpl_sizes_goal; tslia ]
                    | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ])
  | H : u8ro segs m ?A2 ?xs |- _ =>
      let X := constr:(Z.of_nat (length xs)) in
      sc_dj_ensure A S A2 X
        ltac:(fun DJ => apply (u8ro_frame_e segs m m' A2 xs a bs n Heqm Hn Ha Hl) in H;
                        [ | exact (sc_dj_sub A S A2 X (Z.of_nat kn) n DJ Hk) ])
        ltac:(first [ apply (u8ro_frame_e segs m m' A2 xs a bs n Heqm Hn Ha Hl) in H; [ | sc_hide_once; simpl_sizes_goal; tslia ]
                    | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ])
  end);
  transport_chunks_extra m a bs n Hn Ha Hl;
  repeat match goal with Hx : context [write_to_mem m (wa a) bs] |- _ =>
    tryif constr_eq Hx Heqm then fail else rewrite <- Heqm in Hx end.

Ltac footprint_after_store_cached segs m m' Heqm a bs n Hn Ha Hl A S kn Hk :=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      sc_in_ensure Wq A S
        ltac:(fun IN => apply (munch_write_e Wq mq m m' a bs n Heqm Hn Ha Hl) in MU;
                        [ | exact (sc_in_sub Wq A S (Z.of_nat kn) n IN Hk) ])
        ltac:(first [ apply (munch_write_e Wq mq m m' a bs n Heqm Hn Ha Hl) in MU; [ | sc_hide_once; cbn [inside]; tslia ]
                    | fail 100 "store outside the declared footprint:" a ])
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write_e segs mq m m' (wa a) bs Heqm) in WMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write_e segs m m' loq hiq a bs n Heqm Hn Ha Hl) in STq
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

(* [comment removed for export] *)
Ltac sc_store_facts A S kn bs HB k :=
  let Hn := fresh "Hn_st" in let Ha := fresh "Ha_st" in let Hl := fresh "Hl_st" in let Hk := fresh "Hk_st" in
  let n0 := constr:(Z.of_nat (@length byte bs)) in
  let n := eval cbv [length app cbytes cells_bytes le8 le4 le2 le1 word_to_le_bytes Z_to_le_bytes
                     Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in n0 in
  lazymatch n with Zpos _ => idtac | Z0 => idtac end;
  assert (Hn : Z.of_nat (@length byte bs) = n) by exact eq_refl;
  assert (Hk : sc_fits (Z.of_nat kn) n S = true) by exact eq_refl;
  destruct (sc_bounds A S (Z.of_nat kn) n HB Hk) as [Ha Hl];
  k n Hn Ha Hl Hk;
  clear Hn Ha Hl Hk; sc_unhide.

(* [comment removed for export] *)
Ltac mem_after_store_cached :=
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
          tryif cells_spine_closed cs then
            (let Sn := eval cbv [cells_size csize Nat.add] in (cells_size cs) in
             let S := eval vm_compute in (Z.of_nat Sn) in
             let HB := fresh "HB" in
             assert (HB : (0 <= A /\ A + S <= 2^64)%Z) by exact (rw_cells_bound segs m A cs H);
             change bs with (cbytes c');
             let m' := fresh "m" in
             remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm in |- *;
             try lazymatch goal with
             | HI : mem_inv segs m |- _ =>
                 apply (mem_inv_store_cbytes_e segs m m' (wa (A + Z.of_nat kn)) c' Heqm) in HI;
                 [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
             end;
             let H' := fresh "CH" in
             pose proof (rw_cells_write_e segs m m' A cs kn c0 c' Heqm H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
             clear H;
             cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
             sc_store_facts A S kn (cbytes c') HB ltac:(fun n' Hn Ha Hl Hk =>
               transport_chunks_cached segs m m' Heqm (A + Z.of_nat kn)%Z (cbytes c') n' Hn Ha Hl A S kn Hk;
               footprint_after_store_cached segs m m' Heqm (A + Z.of_nat kn)%Z (cbytes c') n' Hn Ha Hl A S kn Hk);
             clear Heqm; clear HB; try clear m; try rename H' into H)
          else mem_after_store_fast
        end
    end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sc_subfp_nil : forall Wq, sub_fp [] Wq.
Proof. intros Wq x _. exact I. Qed.
Lemma sc_subfp_cons : forall l h W Wq, sc_in Wq l (h - l) -> sub_fp W Wq -> sub_fp ((l, h) :: W) Wq.
Proof.
  intros l h W Wq [HI] HS x Hx. cbn [outside]. split.
  - intros C. apply (inside_not_outside Wq l (h - l) x HI); [lia | exact Hx].
  - apply HS. exact Hx.
Qed.

(* [comment removed for export] *)
Ltac sc_sub_ensure W Wq :=
  lazymatch W with
  | [] => idtac
  | (?l, ?h) :: ?W' =>
      first [ match goal with _ : sc_in Wq l (h - l) |- _ => idtac end
            | match goal with _ : sc_noin Wq l (h - l) |- _ => idtac end
            | let IN := fresh "SCin" in assert (IN : sc_in Wq l (h - l)) by (apply sc_inI; cbn [inside]; first [ sc_gonly | tslia ])
            | let NO := fresh "SCnoin" in assert (NO : sc_noin Wq l (h - l)) by exact (sc_noinI Wq l (h - l)) ];
      sc_sub_ensure W' Wq
  end.
(* [comment removed for export] *)
Ltac sc_sub_solve Wq :=
  lazymatch goal with
  | |- sub_fp [] _ => exact (sc_subfp_nil Wq)
  | |- sub_fp ((?l, ?h) :: ?W') _ =>
      match goal with IN : sc_in Wq l (h - l) |- _ => refine (sc_subfp_cons l h W' Wq IN _); sc_sub_solve Wq end
  end.

(* [comment removed for export] *)
Ltac transport_after_call_cached segs m m' MU WM :=
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
      sc_sub_ensure W Wq;
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ sc_sub_solve Wq | exact MU ] ]
            | apply (munch_trans Wq mq m m') in H;
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
