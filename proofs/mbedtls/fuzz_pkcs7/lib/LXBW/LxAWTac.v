(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Mem MState Cells Step CellsX Frame PropExec Asn1Aux Arr Tac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Export CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AShadow AEvtA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac lx_hide H := lazymatch type of H with ?T => change (id T) in H end.
Ltac lx_unhide := repeat match goal with H : id ?T |- _ => change T in H end.
Ltac lx_unhide1 H := lazymatch type of H with id ?T => change T in H end.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_LxAWTac () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "Corelib.Numbers.BinNums.Z"; "Corelib.Lists.ListDef.Forall"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_N"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_base"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_size"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment"; "Corelib.Init.Datatypes.None"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wr_at"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "Stdlib.Lists.List.nth_error"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"].



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lxw_byte_range : forall (b : bv 8), 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. replace 256 with (bv_modulus 8) by (vm_compute; reflexivity). exact H. Qed.
Lemma lxw_b8_of_unsigned : forall (b : bv 8), Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

(* [comment removed for export] *)
Ltac lx_c1_norm :=
  repeat match goal with
         | H : context [C1 ?b] |- _ =>
             lazymatch b with
             | Z_to_bv _ _ => fail
             | _ => is_var b;
                    let u := fresh "u" in let Hu := fresh "Hu" in let R := fresh "Ru" in
                    pose proof (lxw_byte_range b) as R;
                    remember (bv_unsigned b) as u eqn:Hu in *;
                    rewrite <- (lxw_b8_of_unsigned b), <- Hu in H;
                    repeat match goal with K : context [C1 b] |- _ => rewrite <- (lxw_b8_of_unsigned b), <- Hu in K end;
                    try (rewrite <- (lxw_b8_of_unsigned b), <- Hu)
             end
         end.


(* [comment removed for export] *)
Lemma lxw_land_m8 : forall x, 0 <= x -> Z.land x (-8) = x / 8 * 8.
Proof.
  intros x Hx. change (-8) with (Z.lnot (Z.ones 3)). rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
Lemma lxw_land_m16 : forall x, 0 <= x -> Z.land x (-16) = x / 16 * 16.
Proof.
  intros x Hx. change (-16) with (Z.lnot (Z.ones 4)). rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition lx_noaceil : Prop := True.
Ltac lx_aceil :=
  lazymatch goal with
  | _ : lx_noaceil |- _ => try pose proof I    (* [comment removed for export] *)
  | _ : 0x7fff7f800000 <= ACEIL <= _ |- _ => idtac
  | |- _ => try pose proof aceil_bounds
  end.
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac lxw_arith T :=
  lazymatch T with
  | Z.le _ _ => idtac | Z.lt _ _ => idtac | Z.ge _ _ => idtac | Z.gt _ _ => idtac
  | @eq Z _ _ => idtac | @eq nat _ _ => idtac | @eq bool _ _ => idtac
  | ?A /\ ?B => lxw_arith A; lxw_arith B
  | ?A \/ ?B => lxw_arith A; lxw_arith B
  | ~ ?A => lxw_arith A
  | ?A -> False => lxw_arith A
  | True => idtac | False => idtac
  | id _ => fail
  | _ => fail
  end.

(* [comment removed for export] *)
Ltac lx_arith_ctx :=
  repeat match goal with
         | H : ?T |- _ => lazymatch type of T with Prop => tryif lxw_arith T then fail else clear H end
         end.

(* [comment removed for export] *)
Ltac lx_clear_seps :=
  repeat match goal with
         | H : _ = 0 \/ _ \/ _ |- _ => clear H
         | H : ?a + _ <= ?r \/ _ <= ?a |- _ => lazymatch r with Z0 => fail | _ => clear H end
         | H : (_ <= _ \/ _ <= _) /\ _ |- _ => clear H
         end.

Lemma lxw_zlow64_range : forall x, 0 <= zlow 64 x < 2^64.
Proof. intros x. unfold zlow. apply Z.mod_pos_bound. reflexivity. Qed.

Ltac lx_zlow_ranges :=
  rewrite ?lx_bvu64 in *;
  repeat match goal with
         | |- context [zlow 64 ?x] =>
             lazymatch goal with _ : 0 <= zlow 64 x < _ |- _ => fail | _ => pose proof (lxw_zlow64_range x) end
         | _ : context [zlow 64 ?x] |- _ =>
             lazymatch goal with _ : 0 <= zlow 64 x < _ |- _ => fail | _ => pose proof (lxw_zlow64_range x) end
         end.

(* [comment removed for export] *)
Ltac lx_arith := lx_arith_ctx; lx_clear_seps; lx_zlow_ranges; first [lia | unfold zlow, zswrap in *; lia].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac lx_bool_norm :=
  repeat match goal with
         | K : (if ?c then false else true) = true |- _ => destruct c eqn:?LXE; [discriminate K| clear K]
         | K : (if ?c then false else true) = false |- _ => destruct c eqn:?LXE; [clear K| discriminate K]
         | K : negb ?c = true |- _ => apply Bool.negb_true_iff in K
         | K : negb ?c = false |- _ => apply Bool.negb_false_iff in K
         end;
  repeat match goal with
         | K : (?a <? ?b) = true |- _ => apply Z.ltb_lt in K
         | K : (?a <? ?b) = false |- _ => apply Z.ltb_ge in K
         | K : (?a <=? ?b) = true |- _ => apply Z.leb_le in K
         | K : (?a <=? ?b) = false |- _ => apply Z.leb_gt in K
         | K : (?a =? ?b) = true |- _ => apply Z.eqb_eq in K
         | K : (?a =? ?b) = false |- _ => apply Z.eqb_neq in K
         end.

(* [comment removed for export] *)
Ltac lx_pow_lits :=
  repeat match goal with
         | |- context [Z.pow (Zpos ?a) (Zpos ?b)] => let v := eval vm_compute in (Z.pow (Zpos a) (Zpos b)) in change (Z.pow (Zpos a) (Zpos b)) with v in *
         | _ : context [Z.pow (Zpos ?a) (Zpos ?b)] |- _ => let v := eval vm_compute in (Z.pow (Zpos a) (Zpos b)) in change (Z.pow (Zpos a) (Zpos b)) with v in *
         end.

Ltac lx_shifts :=
  rewrite ?Z.shiftr_div_pow2 in * by (clear; lia);
  rewrite ?Z.shiftl_mul_pow2 in * by (clear; lia);
  lx_pow_lits.

(* [comment removed for export] *)
Ltac lx_dead_prep :=
  lx_arith_ctx; lx_bool_norm; lx_clear_seps; lx_shifts; lx_zlow_ranges; unfold zlow in *; lx_pow_lits;
  change ((-1) mod 18446744073709551616) with 18446744073709551615 in *;
  rewrite ?(Z.mod_small 18446744073709551615 18446744073709551616) in * by (clear; lia);
  rewrite ?(Z.mod_small 0 18446744073709551616) in * by (clear; lia).

(* [comment removed for export] *)
Ltac lx_mod_small_by tac :=
  repeat match goal with
         | K : context [?e mod 18446744073709551616] |- _ =>
             rewrite (Z.mod_small e 18446744073709551616) in * by tac
         | |- context [?e mod 18446744073709551616] =>
             rewrite (Z.mod_small e 18446744073709551616) in * by tac
         end.

Ltac lx_dead := lx_dead_prep; first [lia | nia].

(* [comment removed for export] *)
Ltac lx_klin := lx_bool_norm; unfold zlow in *;
  repeat match goal with K : context [?e mod 2 ^ 64] |- _ => rewrite (Z.mod_small e (2 ^ 64)) in K by lia end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac lx_dj :=
  cbn [disjoint_from cells_size csize Nat.add Nat.mul length List.app];
  rewrite ?Nat2Z.inj_add, ?Z2Nat.id by (clear; lia) || idtac;
  lx_aceil; intros;
  first [ lx_arith
        | repeat split; lx_arith ].

Ltac lx_tr_rw H MU WM := eapply rw_cells_transport; [exact H | exact MU | exact WM | lx_dj].
Ltac lx_tr_ro H MU := eapply ro_cells_transport; [exact H | exact MU | lx_dj].
Ltac lx_tr_stk H MU WM := eapply stk_transport_disjoint; [exact H | exact MU | exact WM | lx_dj].

(* [comment removed for export] *)
Ltac lx_subfp :=
  unfold sub_fp; cbn [outside]; lx_aceil;
  let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy; decompose [and] Hy; repeat split; try assumption; lx_arith.
Ltac lx_subfp_with tac := unfold sub_fp; cbn [outside]; intros ? ?; tac.

(* [comment removed for export] *)
Ltac lx_munch MU0 MUl :=
  eapply munch_trans; [ first [exact MU0 | eapply munch_weaken; [| exact MU0]; lx_subfp]
                      | first [exact MUl | eapply munch_weaken; [| exact MUl]; lx_subfp] ].
Ltac lx_munch3 MU0 MUl MUm :=
  eapply munch_trans; [ first [exact MU0 | eapply munch_weaken; [| exact MU0]; lx_subfp]
                      | lx_munch MUl MUm ].
Ltac lx_wmono WM0 WMl := eapply wmono_trans; [exact WM0 | exact WMl].
Ltac lx_wmono3 WM0 WMl WMm := eapply wmono_trans; [exact WM0 | lx_wmono WMl WMm].

(* [comment removed for export] *)
Ltac lx_release ST FR ST2 :=
  pose proof (stk_release _ _ _ _ _ ST FR ltac:(lx_arith)) as ST2;
  cbn [cells_size csize Nat.add Nat.mul] in ST2.

(* [comment removed for export] *)
Ltac lx_carve ST n ST' FR junk :=
  destruct (stk_carve _ _ _ _ n ST ltac:(lx_arith)) as [ST' [junk FR]].


(* [comment removed for export] *)
Ltac lx_fold_mkR :=
  lazymatch goal with
  | |- context [MS ?R _ _ _ _ _ _] =>
    lazymatch R with
    | TNode
        (TNode (TNode (TNode (TNode (TNode TEmpty (Some ?x31) TEmpty) (Some ?x15) TEmpty) (Some ?x7) (TNode TEmpty (Some ?x23) TEmpty)) (Some ?x3) (TNode (TNode TEmpty (Some ?x19) TEmpty) (Some ?x11) (TNode TEmpty (Some ?x27) TEmpty)))
           (Some ?x1) (TNode (TNode (TNode TEmpty (Some ?x17) TEmpty) (Some ?x9) (TNode TEmpty (Some ?x25) TEmpty)) (Some ?x5) (TNode (TNode TEmpty (Some ?x21) TEmpty) (Some ?x13) (TNode TEmpty (Some ?x29) TEmpty))))
        None
        (TNode (TNode (TNode (TNode TEmpty (Some ?x16) TEmpty) (Some ?x8) (TNode TEmpty (Some ?x24) TEmpty)) (Some ?x4) (TNode (TNode TEmpty (Some ?x20) TEmpty) (Some ?x12) (TNode TEmpty (Some ?x28) TEmpty))) (Some ?x2)
           (TNode (TNode (TNode TEmpty (Some ?x18) TEmpty) (Some ?x10) (TNode TEmpty (Some ?x26) TEmpty)) (Some ?x6) (TNode (TNode TEmpty (Some ?x22) TEmpty) (Some ?x14) (TNode TEmpty (Some ?x30) TEmpty)))) =>
        change R with (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    | _ => idtac
    end
  end.


(* [comment removed for export] *)
Ltac lx_wlit :=
  lazymatch goal with
  | |- Z_to_bv 64 ?x = Z_to_bv 64 ?y => lx_is_lit x; lx_is_lit y; apply bv_eq; vm_compute; reflexivity
  end.
Ltac lx_weq1 :=
  lazymatch goal with
  | |- Z_to_bv _ _ = Z_to_bv _ _ => first [lx_wlit | lx_weq]
  | |- @eq (bv _) _ _ => first [apply Z_to_bv_bv_unsigned | symmetry; apply Z_to_bv_bv_unsigned | lx_weq]
  end.
(* [comment removed for export] *)
Ltac lx_mseq := first [ reflexivity
                      | f_equal; f_equal; lx_weq1
                      | cbv [mkR]; repeat (first [ reflexivity | lx_weq1 | progress f_equal ]) ].

(* [comment removed for export] *)
Ltac lx_postw :=
  first [apply evtA_done | (apply aevtA_done; intros ?mo' [?HK' ?MF']) | idtac];
  hnf; lx_exs; lx_ands; [> lx_mseq | ..]; try assumption.

(* [comment removed for export] *)
Ltac lx_run pl := lx_fold_mkR; lx_run_tac pl; lx_tree.


(* [comment removed for export] *)
Ltac lx_is_zlit v := lazymatch v with Z0 => idtac | Zpos ?p => is_ground p | Zneg ?p => is_ground p end.
Ltac lx_stk_top_norm lo :=
  repeat match goal with ST : stk _ _ lo ?t |- _ =>
    match t with context [Z.of_nat ?k] => let v := eval cbv in (Z.of_nat k) in lx_is_zlit v; change (Z.of_nat k) with v in ST end end;
  repeat match goal with ST : stk _ _ lo (?a + ?b + ?c) |- _ => let v := eval cbv in (b + c) in lx_is_zlit v;
        lazymatch v with Z0 => replace (a + b + c) with a in ST by (clear; lia) | _ => replace (a + b + c) with (a + v) in ST by (clear; lia) end end.

(* [comment removed for export] *)
Ltac lx_stk_grow lo :=
  repeat match goal with
  | ST : stk _ ?mx lo ?x, FR : rw_cells _ ?mx ?y _ |- _ =>
      tryif constr_eq x y then idtac else (let E := fresh "E" in assert (E : y = x) by (clear; lia); rewrite E in FR; clear E);
      let ST2 := fresh "ST" in
      pose proof (stk_release _ _ _ _ _ ST FR ltac:(lx_arith)) as ST2; cbn [cells_size csize Nat.add Nat.mul] in ST2; clear ST FR
  | ST : stk _ ?mx lo ?x, ST' : stk _ ?mx ?y ?z |- _ =>
      tryif constr_eq x y then idtac else (let E := fresh "E" in assert (E : y = x) by (clear; lia); rewrite E in ST'; clear E);
      let ST2 := fresh "ST" in pose proof (stk_merge _ _ _ _ _ ST ST' ltac:(lx_arith)) as ST2; clear ST ST'
  end;
  (* [comment removed for export] *)
  lx_stk_top_norm lo.


(* [comment removed for export] *)
Ltac lx_index_of cs z :=
  lazymatch z with
  | Z0 => constr:(O)
  | Zpos _ => lazymatch cs with
              | cons ?c ?cs' => let z' := eval cbv in (z - Z.of_nat (csize c)) in let n := lx_index_of cs' z' in constr:(S n)
              end
  end.

(* [comment removed for export] *)
Ltac lx_adiff hi lo :=
  lazymatch hi with
  | ?b + ?o2 => lazymatch lo with
                | b + ?o1 => eval cbv in (o2 - o1)
                | b => o2
                end
  | ?b => lazymatch lo with b + ?o1 => eval cbv in (- o1) end
  end.

(* [comment removed for export] *)
Ltac lx_stk_grow_to lo top :=
  repeat match goal with
  | ST : stk _ ?mx lo ?x, FR : rw_cells _ ?mx ?y ?cs |- _ =>
      tryif constr_eq x y then idtac else (let E := fresh "E" in assert (E : y = x) by (clear; lia); rewrite E in FR; clear E);
      first [ let B := fresh "B" in
              assert (B : x + Z.of_nat (cells_size cs) <= top) by (cbn [cells_size csize Nat.add Nat.mul]; clear; lia); clear B
            | let d := lx_adiff top x in let n := lx_index_of cs d in
              let FRk := fresh "FRk" in chunk_split FR n FR FRk ];
      let ST2 := fresh "ST" in
      pose proof (stk_release _ _ _ _ _ ST FR ltac:(lx_arith)) as ST2; cbn [cells_size csize Nat.add Nat.mul] in ST2; clear ST FR
  | ST : stk _ ?mx lo ?x, ST' : stk _ ?mx ?y ?z |- _ =>
      tryif constr_eq x y then idtac else (let E := fresh "E" in assert (E : y = x) by (clear; lia); rewrite E in ST'; clear E);
      let B := fresh "B" in assert (B : z <= top) by (clear; lia); clear B;
      let ST2 := fresh "ST" in pose proof (stk_merge _ _ _ _ _ ST ST' ltac:(lx_arith)) as ST2; clear ST ST'
  end;
  lx_stk_top_norm lo;
  (* [comment removed for export] *)
  repeat match goal with FRk : rw_cells _ _ (?a + ?b + ?c) _ |- _ => let v := eval cbv in (b + c) in
        lazymatch v with Z0 => replace (a + b + c) with a in FRk by (clear; lia) | _ => replace (a + b + c) with (a + v) in FRk by (clear; lia) end end.

(* [comment removed for export] *)
Lemma lxw_land_m4096 : forall x, 0 <= x -> Z.land x (-4096) = x / 4096 * 4096.
Proof.
  intros x Hx. change (-4096) with (Z.lnot (Z.ones 12)). rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.


(* [comment removed for export] *)
Ltac lx_junk ST n fr FR :=
  lazymatch type of ST with stk _ ?mx ?a ?b =>
    destruct (stk_carve _ mx a b n ST ltac:(clear; lia)) as [_ [fr FR]];
    replace (b - Z.of_nat n) with a in FR by (clear; lia); clear ST end.


Ltac lx_addr_sub A n :=
  lazymatch A with
  | ?b + ?o => let o' := eval cbv in (o - Z.of_nat n) in constr:(b + o')
  | ?b => let o' := eval cbv in (- Z.of_nat n) in constr:(b + o')
  end.

(* [comment removed for export] *)
Ltac lx_junk_under lo A n fr FRa :=
  let A' := lx_addr_sub A n in
  match goal with
  | ST : stk _ ?mx lo A, FRc : rw_cells _ ?mx A _ |- _ =>
      let STlo := fresh "STlo" in let STj := fresh "STj" in
      destruct (stk_split _ mx lo A' A ST ltac:(lx_arith)) as [STlo STj]; clear ST;
      let FRj := fresh "FRj" in lx_junk STj n fr FRj; chunk_join FRj FRc FRa
  | STj : stk _ ?mx ?b A, FRc : rw_cells _ ?mx A _ |- _ =>
      tryif constr_eq b A' then idtac else (let E := fresh "E" in assert (E : b = A') by (clear; lia); rewrite E in STj; clear E);
      let FRj := fresh "FRj" in lx_junk STj n fr FRj; chunk_join FRj FRc FRa
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac lx_name_rw A H := match goal with K : rw_cells _ _ A _ |- _ => rename K into H end.
Ltac lx_name_ro A H := match goal with K : ro_cells _ _ A _ |- _ => rename K into H end.
Ltac lx_name_stk lo H := match goal with K : stk _ _ lo _ |- _ => rename K into H end.
Ltac lx_name_frame m H H' :=
  match goal with K : munch _ m ?mx, K' : wmono _ m ?mx' |- _ => constr_eq mx mx'; rename K into H; rename K' into H' end.

(* [comment removed for export] *)
Ltac lx_dedup :=
  repeat match goal with
  | H : ?T, H' : ?T |- _ => lazymatch type of T with Prop => clear H' end
  end.
Ltac lx_dedup_fast :=
  repeat match goal with
  | H : ?T, H' : ?T' |- _ => constr_eq T T'; lazymatch type of T with Prop => clear H' end
  end.

(* [comment removed for export] *)
Ltac lx_same := lazymatch goal with E : ?l = _ |- _ => is_var l; subst l; lx_dedup_fast end.

(* [comment removed for export] *)
Ltac lx_clear_mem mo := repeat match goal with H : context [mo] |- _ => clear H end; try clear mo.

(* [comment removed for export] *)
Ltac lx_weqs := repeat lazymatch goal with |- @eq (bv _) _ _ => lx_weq | |- _ => fail end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac lx_acc_run m0 mp :=
  lazymatch goal with MUl : munch _ mp ?mx, WMl : wmono _ mp ?mx' |- _ =>
    lazymatch goal with
    | MUa : id (munch ?W m0 mp), WMa : id (wmono ?sg m0 mp) |- _ =>
        lx_unhide1 MUa; lx_unhide1 WMa;
        let M := fresh "MUA" in let Wm := fresh "WMA" in
        assert (M : munch W m0 mx) by (lx_munch MUa MUl);
        assert (Wm : wmono sg m0 mx) by (lx_wmono WMa WMl);
        clear MUa WMa MUl WMl; lx_hide M; lx_hide Wm
    end end.
Ltac lx_acc_call m0 MUc WMc :=
  lazymatch type of MUc with munch _ ?mx ?m' =>
    lazymatch goal with MUa : id (munch ?W m0 mx), WMa : id (wmono ?sg m0 mx) |- _ =>
      lx_unhide1 MUa; lx_unhide1 WMa;
      transport_after_call sg mx m' MUc WMc;
      clear MUc WMc; lx_clear_mem mx; lx_hide MUa; lx_hide WMa end end.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma lxw_find_segment_none_above : ltac2:(CDefT.buildp (gd_tbl_LxAWTac ()) "Pl,(0.$1.)Pz,$2.Pn,$2.P,(3.$1.Ls,$1.(4.(5.(6.(7.R1.))(6.(8.R1.)))+65?000.)R3.)P,(4.+65?000.R3.)P,(9.=R3.)(:.(;.$1.)(<.R6.R5.R4.)(=.$1.))")
(* [comment removed for export] *).
Proof.
  induction l as [|s l IH]; intros z n HF Hz Hn; cbn; [reflexivity|].
  apply Forall_cons_iff in HF. destruct HF as [HS HL].
  destruct ((Z.of_N (seg_base s) <=? z) && (z + n <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool eqn:E.
  - apply andb_prop in E as [E1 E2]. apply Z.leb_le in E2. exfalso. clear - E2 HS Hz Hn. lia.
  - apply IH; assumption.
Qed.
Lemma lxw_asegs_end : Forall (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <= 0x65f000) asegs.
Proof.
  assert (E : List.map (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s)) asegs = [286720; 987136; 1011712; 6680576]) by (vm_compute; reflexivity).
  assert (G : forall l, List.map (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s)) l = [286720; 987136; 1011712; 6680576] ->
              Forall (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <= 0x65f000) l).
  { intros l H. destruct l as [|s1 [|s2 [|s3 [|s4 [|s5 l]]]]]; cbn in H; try discriminate.
    injection H as E1 E2 E3 E4. repeat constructor; lia. }
  exact (G _ E).
Qed.

(* [comment removed for export] *)
Lemma lxw_wr_at_cells : ltac2:(CDefT.buildp (gd_tbl_LxAWTac ()) "Pm,P,(>.&40.)(;.(>.&8.))PA,$2.Pn,$?.P,(4.+65?000.R2.)P,(10.$11.R4.R3.(12.R2.))(13.(0.(>.&8.))Lbs,(0.(>.&8.))(14.$11.R6.R5.(15.$16.(17.R4.R1.)(18.$16.))))")
(* [comment removed for export] *).
Proof.
  intros m A n HA (H0 & H1 & HW).
  set (f := fun i : nat => match m (wa (A + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end).
  exists (List.map f (seq 0 n)).
  assert (LEN : length (List.map f (seq 0 n)) = n) by (rewrite map_length, seq_length; reflexivity).
  split; [split; [cbn; rewrite LEN; tauto|]|].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [exact H0|]. split; [rewrite LEN; exact H1|].
    intros i Hi. rewrite LEN in Hi. rewrite (nth_error_map f), nth_error_seq. replace (i <? n)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi).
    cbn [option_map Nat.add].
    unfold mrd, f. specialize (HW (Z.of_nat i) ltac:(lia)). unfold wview in HW.
    destruct (m (wa (A + Z.of_nat i))) as [b|] eqn:E; [reflexivity|]. exfalso. apply HW.
    rewrite wa_unsigned by lia. rewrite (lxw_find_segment_none_above asegs) by (first [apply lxw_asegs_end | lia]). reflexivity.
  - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. split; [exact H0|]. split; [exact H1| exact HW].
Qed.

Lemma lxw_u64arr_app : ltac2:(CDefT.buildp (gd_tbl_LxAWTac ()) "Pm,P,(>.&40.)(;.(>.&8.))PA,$2.Pl1,(0.(>.&40.))Pl2,(0.(>.&40.))(19.(1:.$11.R4.R3.(1;.(>.&40.)R2.R1.))(1<.(1:.$11.R4.R3.R2.)(1:.$11.R4.(5.R3.(1=.+8.(12.(1>.(>.&40.)R2.))))R1.)))")
(* [comment removed for export] *).
Proof.
  intros m A l1 l2. unfold u64arr. rewrite u64s_app, app_length.
  pose proof (bytes_at_app asegs m A (u64s l1) (u64s l2)) as BA. rewrite u64s_length in BA.
  replace (A + Z.of_nat (8 * length l1)) with (A + 8 * Z.of_nat (length l1)) in BA by lia.
  replace (8 * Z.of_nat (length l1 + length l2)) with (8 * Z.of_nat (length l1) + 8 * Z.of_nat (length l2)) by lia.
  rewrite (CellsX.wr_at_app asegs m A (8 * Z.of_nat (length l1)) (8 * Z.of_nat (length l2))) by lia.
  tauto.
Qed.

Lemma lxw_u64arr_of_C8 : forall m A (v : word), rw_cells asegs m A [C8 v] -> u64arr asegs m A [v].
Proof. intros m A v [[_ HB] HW]. split; [exact HB| exact HW]. Qed.
(* [comment removed for export] *)
Lemma lxw_u32arr_cell : ltac2:(CDefT.buildp (gd_tbl_LxAWTac ()) "Pm,P,(>.&40.)(;.(>.&8.))PA,$2.Pws,(0.(>.&40.))Pi,$2.Pw,(>.&40.)P,(1?.$11.R5.R4.R3.)P,(:.(;.(>.&40.))(20.(>.&40.)R4.(21.R3.))(22.(>.&40.)R2.))P,(4.=R4.)(14.$11.R8.(5.R7.(1=.+4.R5.))(15.$16.(23.R4.)(18.$16.)))")
(* [comment removed for export] *).
Proof.
  intros m A ws i w [HB HW] HN Hi.
  destruct (u32s_split ws (Z.to_nat i) w HN) as (pre & post & E & Hlen & Hu & Hlp).
  pose proof HB as HB'. rewrite Hu in HB'. apply bytes_at_app in HB' as [_ HB2]. apply bytes_at_app in HB2 as [HB3 _].
  rewrite Hlp in HB3. replace (A + Z.of_nat (4 * Z.to_nat i)) with (A + 4 * i) in HB3 by lia.
  assert (HL : (Z.to_nat i < length ws)%nat) by (rewrite E, length_app; cbn; lia).
  split. { split; [cbn; tauto|]. cbn -[le4]. rewrite ?app_nil_r. exact HB3. }
  cbn [cells_size csize Nat.add].
  replace (4 * Z.of_nat (length ws)) with (4 * i + (4 + (4 * Z.of_nat (length ws) - 4 * i - 4))) in HW by lia.
  apply wr_at_app in HW; [|lia|lia]. destruct HW as [_ HW2]. apply wr_at_app in HW2; [|lia|lia]. destruct HW2 as [HW3 _]. exact HW3.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac lx_cells_eq :=
  first [ reflexivity
        | apply (f_equal2 cons); [ first [reflexivity | f_equal; first [lx_weq | apply Z_to_bv_bv_unsigned | symmetry; apply Z_to_bv_bv_unsigned] ] | lx_cells_eq ] ].
(* [comment removed for export] *)
Ltac lx_rwx K :=
  lazymatch goal with |- rw_cells _ _ ?a ?cs =>
    lazymatch type of K with rw_cells _ _ ?a' ?cs' =>
      (tryif constr_eq a a' then idtac else replace a with a' by (clear; lia));
      replace cs with cs'; [exact K | lx_cells_eq] end end.

(* [comment removed for export] *)
Ltac lx_deads := match goal with |- False => lx_dead | |- _ => idtac end.
(* [comment removed for export] *)
Ltac lx_mulc :=
  repeat match goal with
  | |- context [?v * ?k] => lx_is_zlit k; assert_fails (idtac; lx_is_zlit v); rewrite (Z.mul_comm v k)
  | H : context [?v * ?k] |- _ => lx_is_zlit k; assert_fails (idtac; lx_is_zlit v); rewrite (Z.mul_comm v k) in H
  end.
(* [comment removed for export] *)
Ltac lx_munchx := lazymatch goal with |- munch _ _ ?mx =>
  match goal with MUl : munch _ _ mx |- _ => first [exact MUl | eapply munch_weaken; [| exact MUl]; lx_subfp] end end.

(* [comment removed for export] *)
Ltac lx_stkx := lazymatch goal with |- stk _ _ ?lo ?t =>
  match goal with K : stk _ _ lo ?t' |- _ => first [exact K | replace t with t' by (clear; lia); exact K] end end.
(* [comment removed for export] *)
Ltac lx_close := first [assumption | eassumption | lx_munchx | lx_stkx | match goal with K : rw_cells _ _ _ _ |- _ => lx_rwx K end].
