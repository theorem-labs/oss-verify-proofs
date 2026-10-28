(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpTac.
Open Scope Z_scope.

Lemma land7_mod8 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land3_mod4 : forall x, Z.land x 3 = x mod 4.
Proof. intros x. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land1_mod2 : forall x, Z.land x 1 = x mod 2.
Proof. intros x. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. Qed.

Ltac ub_land K :=
  rewrite ?Z.land_lor_distr_l in K; rewrite ?land7_mod8, ?land3_mod4, ?land1_mod2 in K;
  repeat match goal with H : ?x mod 8 = 0 |- _ => rewrite H in K end; rewrite ?Z.lor_0_l, ?Z.lor_0_r in K;
  repeat match type of K with context [Z.lxor ?x 18446744073709551615] => rewrite (zb_lxor_ones x) in K by lia end.
Ltac ubr_by tac :=
  let KU := fresh "KU" in
  if_cases KU; zify_cond KU; ub_land KU; [ exfalso; tac | try clear KU ].
Ltac ubr := ubr_by lia.
Ltac ub_null := step; ubr.
Ltac ub_align := zstep; step; ubr.
Ltac ubr2 :=
  let KU := fresh "KU" in
  if_cases KU; zify_cond KU; ub_land KU; [ first [ (exfalso; lia) | fail 1 ] | ]; try clear KU.
Ltac ubr3 :=
  let KU := fresh "KU" in
  if_cases KU; zify_cond KU; ub_land KU; [ | exfalso; lia ]; try clear KU.

Ltac ucur_instr :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with
    | Some ?w => let d := eval vm_compute in (decode_any w) in
                 lazymatch d with Some (?i, _) => constr:(i) end
    end
  end.
Ltac uclosed_term c := match c with | context [?x] => is_var x; fail 1 | _ => idtac end.
Ltac ulit_branch :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
    first [ replace (if c then a else b) with a by (vm_compute; reflexivity)
          | replace (if c then a else b) with b by (vm_compute; reflexivity) ] end.
Ltac ulit_branch_safe :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => uclosed_term c; ulit_branch end.
Ltac unorm32 :=
  repeat match goal with
  | |- context [sx32 (Z_to_bv 64 ?e)] => rewrite (sx32_lit e) by lia
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia
  | |- context [bv_swrap 32 ?x] => rewrite (swrap32_id x) by lia
  end.
Ltac ucstep :=
  let i := ucur_instr in
  lazymatch i with
  | Load _ _ _ _ _ => step; try unorm32
  | Store _ _ _ _ => step; try fix_lit_store
  | Branch _ _ _ _ => step; try ulit_branch_safe
  | Op _ _ _ _ => zstep
  | OpImm _ _ _ _ => zstep
  | ShiftImm _ _ _ _ => zstep
  | OpImm32 _ _ _ => zstep; try unorm32
  | Op32 _ _ _ _ => zstep; try unorm32
  | _ => step
  end.
Ltac uat_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => constr_eq q p end.
Ltac uis_ms := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => idtac end.
Ltac uis_if := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => idtac end.
Ltac uwalk_to p := repeat (uis_ms; tryif uat_pc p then fail else ucstep).
Ltac ubr_lia :=
  let K := fresh "K" in
  if_cases K; zify_cond K; [ first [ (exfalso; lia) | fail 1 ] | ]; try clear K.
Ltac ubr_lia2 :=
  let K := fresh "K" in
  if_cases K; zify_cond K; [ | exfalso; lia ]; try clear K.
Ltac ubr_auto := first [ ubr_lia | ubr_lia2 ].
Ltac uwalk_lia_to p := repeat first [ (uis_ms; tryif uat_pc p then fail else ucstep) | (uis_if; ubr_auto) ].
Ltac uub_b2z :=
  rewrite ?land7_mod8, ?land3_mod4;
  repeat match goal with |- context [Z.b2z (?a <? ?b)] =>
    first [ replace (a <? b) with true by (symmetry; apply Z.ltb_lt; lia) | replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia) ] end;
  cbn [Z.b2z]; change (Z.lxor 1 0) with 1; change (Z.lxor 0 1) with 1; change (Z.lxor 1 1) with 0; change (Z.lxor 0 0) with 0.
Ltac uhas_b2z_if := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => lazymatch c with context [Z.b2z] => idtac end end.
Ltac uwalk_ub_to p := repeat first [ (uis_ms; tryif uat_pc p then fail else ucstep) | (uhas_b2z_if; uub_b2z; ulit_branch_safe) | (uis_if; first [ ubr_auto | ubr2 | ubr3 ]) ].
Ltac ushow_regs := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "pc=" pc end; let v1 := reg_val 1 in idtac "r1=" v1; let v2 := reg_val 2 in idtac "r2=" v2; let v3 := reg_val 3 in idtac "r3=" v3; let v4 := reg_val 4 in idtac "r4=" v4; let v5 := reg_val 5 in idtac "r5=" v5; let v6 := reg_val 6 in idtac "r6=" v6; let v7 := reg_val 7 in idtac "r7=" v7; let v8 := reg_val 8 in idtac "r8=" v8; let v9 := reg_val 9 in idtac "r9=" v9; let v10 := reg_val 10 in idtac "r10=" v10; let v11 := reg_val 11 in idtac "r11=" v11; let v12 := reg_val 12 in idtac "r12=" v12; let v13 := reg_val 13 in idtac "r13=" v13; let v14 := reg_val 14 in idtac "r14=" v14; let v15 := reg_val 15 in idtac "r15=" v15; let v16 := reg_val 16 in idtac "r16=" v16; let v17 := reg_val 17 in idtac "r17=" v17; let v18 := reg_val 18 in idtac "r18=" v18; let v19 := reg_val 19 in idtac "r19=" v19; let v20 := reg_val 20 in idtac "r20=" v20; let v21 := reg_val 21 in idtac "r21=" v21; let v22 := reg_val 22 in idtac "r22=" v22; let v23 := reg_val 23 in idtac "r23=" v23; let v24 := reg_val 24 in idtac "r24=" v24; let v25 := reg_val 25 in idtac "r25=" v25; let v26 := reg_val 26 in idtac "r26=" v26; let v27 := reg_val 27 in idtac "r27=" v27; let v28 := reg_val 28 in idtac "r28=" v28; let v29 := reg_val 29 in idtac "r29=" v29; let v30 := reg_val 30 in idtac "r30=" v30; let v31 := reg_val 31 in idtac "r31=" v31.
