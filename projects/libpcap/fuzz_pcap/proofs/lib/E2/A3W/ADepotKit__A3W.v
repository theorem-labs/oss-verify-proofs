(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec Exec Tac.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module ADepotKit.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma wr_at_app : forall segs m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
  wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
  intros segs m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i)%Z with (a + (n1 + i))%Z by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i)%Z with (a + n1 + (i - n1))%Z by lia. apply HB. lia.
Qed.

#[using="Type"] Lemma rw_cells_app : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite wr_at_app by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
    rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
    rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

#[using="Type"] Lemma bytes_eq_of_unsigned : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|b1 l1 IH]; intros [|b2 l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

#[using="Type"] Lemma rw_cells_recell_mid : forall segs m A pre mid post mid',
  rw_cells segs m A (pre ++ mid ++ post) -> cells_wf mid' ->
  map bv_unsigned (cells_bytes mid') = map bv_unsigned (cells_bytes mid) ->
  rw_cells segs m A (pre ++ mid' ++ post).
Proof.
  intros segs m A pre mid post mid' RW WF E.
  apply bytes_eq_of_unsigned in E.
  destruct RW as [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W23]. apply cells_wf_app in W23. destruct W23 as [W2 W3].
  assert (SZ : cells_size mid' = cells_size mid).
  { rewrite <- (cells_bytes_length mid' WF), <- (cells_bytes_length mid W2), E. reflexivity. }
  split; [split|].
  - apply cells_wf_app. split; [exact W1|]. apply cells_wf_app. split; assumption.
  - rewrite !cells_bytes_app in *. rewrite E. exact Hb.
  - rewrite !cells_size_app in *. rewrite SZ. exact Hw.
Qed.

#[using="Type"] Lemma Z_to_le_bytes_add : forall a b z, Z_to_le_bytes (a + b) z = Z_to_le_bytes a z ++ Z_to_le_bytes b (Z.shiftr z (8 * Z.of_nat a)).
Proof.
  induction a as [|a IH]; intros b z; cbn [Z_to_le_bytes Nat.add app].
  - rewrite Z.shiftr_0_r. reflexivity.
  - f_equal. rewrite IH. f_equal. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

#[using="Type"] Lemma le8_small_split : forall v, (0 <= v < 2^32)%Z -> le8 (Z_to_bv 64 v) = le4 (Z_to_bv 64 v) ++ le4 (Z_to_bv 64 0).
Proof.
  intros v Hv. unfold le8, le4, word_to_le_bytes. rewrite !unsigned_lit by lia.
  change 8%nat with (4 + 4)%nat at 1. rewrite Z_to_le_bytes_add. f_equal.
  change (8 * Z.of_nat 4)%Z with 32%Z. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rw_cells_C8_C4C4 : forall segs m A pre post v,
  rw_cells segs m A (pre ++ C8 (Z_to_bv 64 v) :: post) -> (0 <= v < 2^32)%Z ->
  rw_cells segs m A (pre ++ C4 (Z_to_bv 64 v) :: C4 (Z_to_bv 64 0) :: post).
Proof.
  intros segs m A pre post v H Hv.
  change (pre ++ C4 (Z_to_bv 64 v) :: C4 (Z_to_bv 64 0) :: post) with (pre ++ [C4 (Z_to_bv 64 v); C4 (Z_to_bv 64 0)] ++ post).
  eapply rw_cells_recell_mid with (mid := [C8 (Z_to_bv 64 v)]); [exact H | cbv; repeat split |].
  cbn [cells_bytes cbytes app]. rewrite app_nil_r. rewrite (le8_small_split v Hv). reflexivity.
Qed.
#[using="Type"] Lemma rw_cells_C4C4_C8 : forall segs m A pre post v,
  rw_cells segs m A (pre ++ C4 (Z_to_bv 64 v) :: C4 (Z_to_bv 64 0) :: post) -> (0 <= v < 2^32)%Z ->
  rw_cells segs m A (pre ++ C8 (Z_to_bv 64 v) :: post).
Proof.
  intros segs m A pre post v H Hv.
  change (pre ++ C8 (Z_to_bv 64 v) :: post) with (pre ++ [C8 (Z_to_bv 64 v)] ++ post).
  eapply rw_cells_recell_mid with (mid := [C4 (Z_to_bv 64 v); C4 (Z_to_bv 64 0)]); [exact H | cbv; repeat split |].
  cbn [cells_bytes cbytes app]. rewrite app_nil_r. rewrite (le8_small_split v Hv). reflexivity.
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma wr_at_app : forall segs m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
  wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
  intros segs m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i)%Z with (a + (n1 + i))%Z by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i)%Z with (a + n1 + (i - n1))%Z by lia. apply HB. lia.
Qed.

#[using="Type"] Lemma rw_cells_app : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite wr_at_app by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
    rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
    rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

#[using="Type"] Lemma bytes_eq_of_unsigned : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|b1 l1 IH]; intros [|b2 l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

#[using="Type"] Lemma rw_cells_recell_mid : forall segs m A pre mid post mid',
  rw_cells segs m A (pre ++ mid ++ post) -> cells_wf mid' ->
  map bv_unsigned (cells_bytes mid') = map bv_unsigned (cells_bytes mid) ->
  rw_cells segs m A (pre ++ mid' ++ post).
Proof.
  intros segs m A pre mid post mid' RW WF E.
  apply bytes_eq_of_unsigned in E.
  destruct RW as [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W23]. apply cells_wf_app in W23. destruct W23 as [W2 W3].
  assert (SZ : cells_size mid' = cells_size mid).
  { rewrite <- (cells_bytes_length mid' WF), <- (cells_bytes_length mid W2), E. reflexivity. }
  split; [split|].
  - apply cells_wf_app. split; [exact W1|]. apply cells_wf_app. split; assumption.
  - rewrite !cells_bytes_app in *. rewrite E. exact Hb.
  - rewrite !cells_size_app in *. rewrite SZ. exact Hw.
Qed.

#[using="Type"] Lemma Z_to_le_bytes_add : forall a b z, Z_to_le_bytes (a + b) z = Z_to_le_bytes a z ++ Z_to_le_bytes b (Z.shiftr z (8 * Z.of_nat a)).
Proof.
  induction a as [|a IH]; intros b z; cbn [Z_to_le_bytes Nat.add app].
  - rewrite Z.shiftr_0_r. reflexivity.
  - f_equal. rewrite IH. f_equal. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

#[using="Type"] Lemma le8_small_split : forall v, (0 <= v < 2^32)%Z -> le8 (Z_to_bv 64 v) = le4 (Z_to_bv 64 v) ++ le4 (Z_to_bv 64 0).
Proof.
  intros v Hv. unfold le8, le4, word_to_le_bytes. rewrite !unsigned_lit by lia.
  change 8%nat with (4 + 4)%nat at 1. rewrite Z_to_le_bytes_add. f_equal.
  change (8 * Z.of_nat 4)%Z with 32%Z. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rw_cells_C8_C4C4 : forall segs m A pre post v,
  rw_cells segs m A (pre ++ C8 (Z_to_bv 64 v) :: post) -> (0 <= v < 2^32)%Z ->
  rw_cells segs m A (pre ++ C4 (Z_to_bv 64 v) :: C4 (Z_to_bv 64 0) :: post).
Proof.
  intros segs m A pre post v H Hv.
  change (pre ++ C4 (Z_to_bv 64 v) :: C4 (Z_to_bv 64 0) :: post) with (pre ++ [C4 (Z_to_bv 64 v); C4 (Z_to_bv 64 0)] ++ post).
  eapply rw_cells_recell_mid with (mid := [C8 (Z_to_bv 64 v)]); [exact H | cbv; repeat split |].
  cbn [cells_bytes cbytes app]. rewrite app_nil_r. rewrite (le8_small_split v Hv). reflexivity.
Qed.
#[using="Type"] Lemma rw_cells_C4C4_C8 : forall segs m A pre post v,
  rw_cells segs m A (pre ++ C4 (Z_to_bv 64 v) :: C4 (Z_to_bv 64 0) :: post) -> (0 <= v < 2^32)%Z ->
  rw_cells segs m A (pre ++ C8 (Z_to_bv 64 v) :: post).
Proof.
  intros segs m A pre post v H Hv.
  change (pre ++ C8 (Z_to_bv 64 v) :: post) with (pre ++ [C8 (Z_to_bv 64 v)] ++ post).
  eapply rw_cells_recell_mid with (mid := [C4 (Z_to_bv 64 v); C4 (Z_to_bv 64 0)]); [exact H | cbv; repeat split |].
  cbn [cells_bytes cbytes app]. rewrite app_nil_r. rewrite (le8_small_split v Hv). reflexivity.
Qed.
End CANSEC1.
End TwB.
End ADepotKit.

(* [comment removed for export] *)
Module AFastTac.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From Ltac2 Require Ltac2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF StepF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module RL.
  Import Ltac2.
  (* [comment removed for export] *)
  Ltac2 vars (c : constr) : ident list := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.SF2.vars_of [] c.
  Ltac2 meets (xs : ident list) (ys : ident list) : bool := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.SF2.meets xs ys.
  Ltac2 arith (t : constr) : bool := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.SF2.arith_logic t.
  Ltac2 is_local (id : ident) : bool := match Env.get [id] with None => true | Some _ => false end.
  Ltac2 rec add_new (acc : ident list) (xs : ident list) : ident list :=
    match xs with
    | [] => acc
    | x :: xs' => if List.exist (Ident.equal x) acc then add_new acc xs' else add_new (x :: acc) xs'
    end.
  Ltac2 rec has_or (t : constr) : bool :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App f args =>
        if Constr.equal f '@or then true else Array.exist has_or args
    | Constr.Unsafe.Prod b body => if has_or (Constr.Binder.type b) then true else has_or body
    | _ => false
    end.
  (* [comment removed for export] *)
  Ltac2 rec close (cand : (ident * ident list) list) (vs : ident list) (n : int) : ident list :=
    if Int.le n 0 then vs else
    let vs' := List.fold_left (fun acc c => let (_, hv) := c in if meets hv vs then add_new acc hv else acc) vs cand in
    if Int.equal (List.length vs') (List.length vs) then vs else close cand vs' (Int.sub n 1).
  (* [comment removed for export] *)
  Ltac2 prune (nd : bool) (n : int) : unit :=
    let cand := List.map_filter (fun h => let (id, body, ty) := h in
                  match body with
                  | Some _ => None
                  | None => if is_local id then (if arith ty then Some (id, vars ty) else None) else None
                  end) (Control.hyps ()) in
    let vs := close cand (add_new [] (vars (Control.goal ()))) n in
    let drop := List.map_filter (fun c => let (id, hv) := c in if meets hv vs then None else Some id) cand in
    match drop with [] => () | _ :: _ => Std.clear drop end;
    (* [comment removed for export] *)
    if Bool.neg nd then () else
    let disj := List.map_filter (fun h => let (id, body, ty) := h in
                  match body with
                  | Some _ => None
                  | None => if is_local id then (if has_or ty then Some id else None) else None
                  end) (Control.hyps ()) in
    match disj with [] => () | _ :: _ => Std.clear disj end.
  Ltac2 prune2 () : unit := Control.enter (fun () => prune true 2).
  Ltac2 prune2d () : unit := Control.enter (fun () => prune false 2).
End RL.

Ltac rl_prune := ltac2:(RL.prune2 ()).
Ltac rl_prune_d := ltac2:(RL.prune2d ()).
(* [comment removed for export] *)
Ltac rlia := solve [ rl_prune; lia ].
(* [comment removed for export] *)
Ltac rlia_d := solve [ rl_prune_d; lia ].

(* [comment removed for export] *)
Ltac flia_rl := first [ sassumption | rlia | slim; lia | lia | assumption ].
(* [comment removed for export] *)
Ltac alia_rl := first [ rlia | lia | acc_enrich; lia ].

(* [comment removed for export] *)
Ltac slia_rl := first [ exact I | rlia_d | lia | split; [ first [ rlia_d | lia ] | exact I ] ].
(* [comment removed for export] *)
Ltac tlia_rl := first [ solve [ rl_prune_d; Zify.zify; xlia zchecker ]
                      | Zify.zify; xlia zchecker
                      | sf_unhide;
                        first [ zify_prune_neg; Zify.zify; xlia zchecker
                              | zify_prune_plain; Zify.zify; xlia zchecker
                              | zify_prune_rel2; Zify.zify; xlia zchecker
                              | Zify.zify; xlia zchecker ] ].

(* [comment removed for export] *)
Ltac solve_acc_with_rl H :=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_litZ' RNG lo len E n nz H (@eq_refl Z nz) (@eq_refl bool true)); rlia
      end
  | |- acc_in ?RNG (?x, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_varZ RNG lo len x n nz H (@eq_refl Z nz)); rlia
      end
  end.
(* [comment removed for export] *)
Ltac solve_acc1_rl :=
  first [ acc_hint
        | assumption
        | lazymatch goal with
          | |- acc_in ?RNG (Z_to_bv 64 ?E, _) =>
              is_closed_lits E;
              match goal with
              | H : rng RNG ?lo ?len |- _ => is_closed_lits lo; is_closed_lits len; solve_acc_lit H
              end
          end
        | lazymatch goal with
          | |- acc_in ?RNG (?a, _) =>
              let E := addr_expr a in let X := leftmost E in
              first [ match goal with
                      | H : rng RNG ?lo _ |- _ => let Y := leftmost lo in constr_eq X Y; solve_acc_with H
                      end
                    | is_var X;
                      match goal with
                      | H : rng RNG ?lo ?len |- _ => first [mentions len X | mentions lo X]; solve_acc_with H
                      end
                    | lazymatch X with bv_unsigned ?r => is_var r;
                        match goal with
                        | H : rng RNG ?lo ?len |- _ => first [mentions len X | mentions lo X]; solve_acc_with H
                        end
                      end ]
          end
        | (* [comment removed for export] *)
          lazymatch goal with
          | |- acc_in ?RNG _ => match goal with H : rng RNG _ _ |- _ => solve [ solve_acc_with_rl H ] end
          end
        | lazymatch goal with
          | |- acc_in ?RNG _ =>
              match goal with
              | H : rng RNG _ _ |- _ => solve_acc_with H
              end
          end
        | lazymatch goal with
          | |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
              let nz := eval cbv in (Z.of_nat n) in
              match goal with
              | H : rng RNG ?lo ?len |- _ => apply (rng_acc_wrapZ RNG lo len E n nz H (@eq_refl Z nz)); alia
              end
          end
        | lazymatch goal with |- acc_in _ (?a, ?n) => fail 0 "footprint: access" a "width" n "not covered by any [rng] hypothesis" end ].

(* [comment removed for export] *)
Ltac easm :=
  first [ lazymatch goal with
          | |- rw_cells ?s ?mm ?A _ => match goal with H : rw_cells s mm A _ |- _ => exact H end
          end
        | eassumption ].
End AFastTac.
