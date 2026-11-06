(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface XRep XE_kit XE_assign.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac go1 := first [ step | if_false | if_true ].

(* [comment removed for export] *)
Ltac steps_to pc :=
  do 40 (lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => idtac
         | |- evt _ _ _ => go1
         end).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac call_assignA e :=
  let AS := fresh "AS" in
  pose proof assignA_spec as AS;
  unfold assignA_stmt, assign_stmt, assign_post, assign_W, P_EC_CTOR_HTTP, G_HTTP_CAT in AS;
  lazymatch goal with
  | |- evt _ _ (MS (mkR _ (Z_to_bv 64 ?spv) _ _ _ _ _ _ _ (Z_to_bv 64 ?D) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      lazymatch goal with
      | ST : stk _ _ ?lo _, HC : HttpCat _ ?g, TMP : rw_cells _ _ D [CB 24 ?junk] |- _ =>
          callZ (AS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D e lo g junk);
          [ exact TMP | exact HC | assumption | rewrite ?unsigned_lit by lia; exact ST
          | rewrite ?unsigned_lit by lia; lia | lia | rewrite ?unsigned_lit by lia; lia | lia | lia | assumption | clear AS ]
      end
  | |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      (* [comment removed for export] *)
      fail "call_assignA: state not in mkR form; use call_assignA_with spv D e lo g junk"
  end.

Ltac call_assignA_with spv D e lo g junk :=
  let AS := fresh "AS" in
  pose proof assignA_spec as AS;
  unfold assignA_stmt, assign_stmt, assign_post, assign_W, P_EC_CTOR_HTTP, G_HTTP_CAT in AS;
  callZ (AS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D e lo g junk);
  [ assumption | assumption | assumption | rewrite ?unsigned_lit by lia; assumption
  | rewrite ?unsigned_lit by lia; lia | lia | rewrite ?unsigned_lit by lia; lia | lia | lia | assumption | clear AS ].

(* [comment removed for export] *)
Ltac concretize_ec H :=
  unfold ErrCodeCells, EC_http, EC_http_loc, ec_make, ec_make_loc, EC_clear, wz in H;
  cbn [ec_val ec_cat ec_flags Z.eqb Z.add Pos.add] in H; unfold G_HTTP_CAT in H.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac expose_statics HC XS W2 :=
  let HCo := fresh "HCo" in let HCg := fresh "HCg" in
  destruct HC as [HCo HCg]; cbn [HttpCatCells HttpCatGuardCells] in HCo, HCg;
  unfold G_HTTP_CAT, G_HTTP_CAT_GUARD in HCo, HCg;
  lazymatch type of XS with XStatics ?mx =>
    pose proof (munch_refl W2 mx) as MU2nd; pose proof (wmono_refl rsegs mx) as WM2nd
  end.

(* [comment removed for export] *)
Ltac close_HttpCat_chunks := split; assumption.
Ltac close_HttpCat_transport HC MU2 WM2 :=
  eapply HttpCat_transport; [exact HC | exact MU2 | exact WM2 | unfold G_HTTP_CAT; cbn; lia | unfold G_HTTP_CAT_GUARD; cbn; lia].
Ltac close_XStatics XS MU2 WM2 :=
  eapply XStatics_transport; [exact XS | exact MU2 | exact WM2 | repeat constructor; cbn; lia].

(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac join_frame LOW HIGH base :=
  lazymatch type of LOW with rw_cells _ ?mx _ ?cs1 =>
  lazymatch type of HIGH with rw_cells _ _ ?ah ?cs2 =>
    let J := fresh "FRJ" in
    assert (J : rw_cells rsegs mx base (cs1 ++ cs2))
      by (apply (proj2 (rw_cells_app rsegs mx base cs1 cs2)); split; [exact LOW | cbn [cells_size csize Nat.add];
            lazymatch goal with |- rw_cells _ _ ?a _ => replace a with ah by lia end; exact HIGH]);
    clear LOW HIGH; cbn [app] in J; rename J into LOW
  end end.

(* [comment removed for export] *)
Ltac split_frame FR cs1 cs2 LOW HIGH :=
  lazymatch type of FR with rw_cells _ ?mx ?base _ =>
    apply (proj1 (rw_cells_app rsegs mx base cs1 cs2)) in FR;
    destruct FR as [LOW HIGH]; cbn [cells_size csize Nat.add] in HIGH;
    repeat match type of HIGH with
    | rw_cells _ _ (Z.add (Z.add ?b ?c) (Z.of_nat ?k)) _ =>
        let v := eval vm_compute in (c + Z.of_nat k)%Z in
        replace (Z.add (Z.add b c) (Z.of_nat k)) with (Z.add b v) in HIGH by lia
    | rw_cells _ _ (Z.add ?b (Z.of_nat ?k)) _ =>
        let v := eval vm_compute in (Z.of_nat k) in change (Z.of_nat k) with v in HIGH
    end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land1_odd : forall lc, 0 <= lc -> Z.odd lc = true -> Z.land lc 1 = 1.
Proof.
  intros lc H Ho. rewrite Z.land_ones with (n := 1) by lia. change (2^1) with 2.
  rewrite Zmod_odd. rewrite Ho. reflexivity.
Qed.
Lemma land1_even : forall lc, 0 <= lc -> Z.odd lc = false -> Z.land lc 1 = 0.
Proof.
  intros lc H Ho. rewrite Z.land_ones with (n := 1) by lia. change (2^1) with 2.
  rewrite Zmod_odd. rewrite Ho. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma odd_loc1 : forall loc, Z.even loc = true -> Z.odd (loc + 1) = true.
Proof. intros loc He. rewrite Z.odd_add. cbn. rewrite <- Z.negb_even, He. reflexivity. Qed.

(* [comment removed for export] *)
Ltac ec_low4 EC := let R := fresh "RD4" in pose proof (C8_read_low4 _ _ _ _ EC) as R; cbv delta [wa] in R.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma seqz_pred_ne1 : forall lc, 0 <= lc < 2^64 -> lc <> 1 -> (lc + -1 =? 0) = false.
Proof. intros lc H H1. apply Z.eqb_neq. lia. Qed.

