(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import StepFast.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import AWKit AWAuto.
Import ListNotations.
Open Scope Z_scope.

Definition hid (P : Prop) : Prop := P.
Ltac hide H := lazymatch type of H with ?T => change (hid T) in H end.
Ltac unhide H := unfold hid in H.

Ltac hide_mem_except keep :=
  repeat match goal with
  | H : rw_cells _ _ _ _ |- _ => tryif constr_eq H keep then fail else hide H
  | H : stk _ _ _ _ |- _ => hide H
  | H : munch _ _ _ |- _ => hide H
  | H : wmono _ _ _ |- _ => hide H
  end.
Ltac unhide_transport MUs WMs :=
  lazymatch type of MUs with munch ?Ws ?ma ?mb =>
  repeat match goal with
  | H : hid (rw_cells ?segs ma ?A2 ?cs2) |- _ =>
      unhide H; apply (rw_cells_transport segs Ws ma mb A2 cs2) in H; [ | exact MUs | exact WMs | dj_solve ]
  | H : hid (stk ?segs ma ?loq ?hiq) |- _ =>
      unhide H; apply (stk_transport_disjoint segs Ws ma mb loq hiq) in H; [ | exact MUs | exact WMs | dj_solve ]
  | H : hid (munch ?Wq ?mq ma) |- _ =>
      unhide H; apply (munch_trans Wq mq ma mb) in H; [ | eapply (munch_weaken Ws Wq ma mb); [ sub_fp_solve | exact MUs ] ]
  | H : hid (wmono ?segs ?mq ma) |- _ => unhide H; apply (wmono_trans segs mq ma mb) in H; [ | exact WMs ]
  end end.

Definition selw (i j k : nat) (yi yj v : word) : word := if Nat.eqb k i then yi else if Nat.eqb k j then yj else v.
Ltac gen2 CONT pcnew i j :=
  let v1 := reg_val 1 in let v2 := reg_val 2 in let v3 := reg_val 3 in let v4 := reg_val 4 in let v5 := reg_val 5 in let v6 := reg_val 6 in let v7 := reg_val 7 in let v8 := reg_val 8 in let v9 := reg_val 9 in let v10 := reg_val 10 in let v11 := reg_val 11 in let v12 := reg_val 12 in let v13 := reg_val 13 in let v14 := reg_val 14 in let v15 := reg_val 15 in let v16 := reg_val 16 in let v17 := reg_val 17 in let v18 := reg_val 18 in let v19 := reg_val 19 in let v20 := reg_val 20 in let v21 := reg_val 21 in let v22 := reg_val 22 in let v23 := reg_val 23 in let v24 := reg_val 24 in let v25 := reg_val 25 in let v26 := reg_val 26 in let v27 := reg_val 27 in let v28 := reg_val 28 in let v29 := reg_val 29 in let v30 := reg_val 30 in let v31 := reg_val 31 in
  lazymatch goal with |- evt ?sg ?P (MS _ ?F _ ?fc ?o ?mm ?ro) =>
    let T := constr:(forall yi yj : word, evt sg P (MS (mkR (selw i j 1%nat yi yj v1) (selw i j 2%nat yi yj v2) (selw i j 3%nat yi yj v3) (selw i j 4%nat yi yj v4) (selw i j 5%nat yi yj v5) (selw i j 6%nat yi yj v6) (selw i j 7%nat yi yj v7) (selw i j 8%nat yi yj v8) (selw i j 9%nat yi yj v9) (selw i j 10%nat yi yj v10) (selw i j 11%nat yi yj v11) (selw i j 12%nat yi yj v12) (selw i j 13%nat yi yj v13) (selw i j 14%nat yi yj v14) (selw i j 15%nat yi yj v15) (selw i j 16%nat yi yj v16) (selw i j 17%nat yi yj v17) (selw i j 18%nat yi yj v18) (selw i j 19%nat yi yj v19) (selw i j 20%nat yi yj v20) (selw i j 21%nat yi yj v21) (selw i j 22%nat yi yj v22) (selw i j 23%nat yi yj v23) (selw i j 24%nat yi yj v24) (selw i j 25%nat yi yj v25) (selw i j 26%nat yi yj v26) (selw i j 27%nat yi yj v27) (selw i j 28%nat yi yj v28) (selw i j 29%nat yi yj v29) (selw i j 30%nat yi yj v30) (selw i j 31%nat yi yj v31)) F (Z_to_bv 64 pcnew) fc o mm ro)) in
    let T' := eval cbv beta iota delta [selw Nat.eqb] in T in
    assert (CONT : T') end.

Lemma acc_loadw : forall (m : word -> option byte) APP w (a : word), 1 <= w -> APP mod 8 + w <= 8 -> 0 <= APP ->
  acc m (APP + w - 1) -> a = wa (sh APP) ->
  exists k, ov_read_bytes asegs m a 1 = Some [Z_to_bv 8 k] /\ (k = 0 \/ (0 < k < 8 /\ APP mod 8 + w - 1 < k)).
Proof.
  intros m APP w a W1 W8 AP HACC ->.
  assert (E : sh (APP + w - 1) = sh APP) by (unfold sh; f_equal; Z.div_mod_to_equations; lia).
  assert (E2 : (APP + w - 1) mod 8 = APP mod 8 + w - 1) by (Z.div_mod_to_equations; lia).
  destruct (acc_load m (APP + w - 1) (wa (sh APP)) HACC ltac:(rewrite E; reflexivity)) as (k & R & Hk).
  exists k. split; [exact R|]. rewrite E2 in Hk. exact Hk.
Qed.

Ltac recell FR i :=
  lazymatch type of FR with rw_cells ?segs ?m ?A ?cs =>
    let pre := eval cbv beta iota delta [firstn skipn] in (firstn i cs) in
    let post := eval cbv beta iota delta [firstn skipn] in (skipn (S i) cs) in
    lazymatch eval cbv beta iota delta [firstn skipn nth_error] in (nth_error cs i) with
    | Some (CB 8 ?b) => change (rw_cells segs m A (pre ++ CB 8 b :: post)) in FR; apply (rw_cells_CB_C8 segs m A pre b post) in FR; cbn [app] in FR
    | Some (CB 4 ?b) => change (rw_cells segs m A (pre ++ CB 4 b :: post)) in FR; apply (rw_cells_CB_C4 segs m A pre b post) in FR; cbn [app] in FR
    end end.

Ltac splitcb FR i sizes :=
  lazymatch type of FR with rw_cells ?segs ?m ?A ?cs =>
    let pre := eval cbv beta iota delta [firstn skipn] in (firstn i cs) in
    let post := eval cbv beta iota delta [firstn skipn] in (skipn (S i) cs) in
    lazymatch eval cbv beta iota delta [firstn skipn nth_error] in (nth_error cs i) with
    | Some (CB ?n ?b) => change (rw_cells segs m A (pre ++ CB n b :: post)) in FR;
        apply (rw_cells_split_CB segs m A pre n b post sizes) in FR; [| reflexivity]; cbn [app mk_CB_cells] in FR
    end end.

Ltac name_junk FR :=
  repeat lazymatch type of FR with
         | context [le_bytes_to_word ?b] => let w := fresh "jw" in remember (le_bytes_to_word b) as w in FR
         | context [CB _ (firstn ?a ?b)] => let j := fresh "jk" in remember (firstn a b) as j in FR
         | context [CB _ (skipn ?a ?b)] => let j := fresh "jk" in remember (skipn a b) as j in FR end;
  repeat match goal with E : _ = le_bytes_to_word _ |- _ => clear E | E : _ = firstn _ _ |- _ => clear E | E : _ = skipn _ _ |- _ => clear E end.
