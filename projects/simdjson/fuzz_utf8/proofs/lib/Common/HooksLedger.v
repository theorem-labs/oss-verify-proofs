(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec AxSymExec3 AxSymExec3B AsanPlanCore. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import AsanPlanWhile. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AsanPlan. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import AsanPlanLedger AsanNodesIO ExecNodes ExecNodesW MoveNodes AsanNodesArg ImgParams MainDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Module HKL.
Import AX2. Import AX2B. Import APC. Import AP. Import APL.
Notation reL := with_ledger (only parsing).

Section S.
Context {fx : FPState}.

(* [comment removed for export] *)
Lemma ION_ret_with_reL : forall L cs r k nx f, ION.ret_with (reL L cs) r k nx f = reL L (ION.ret_with cs r k nx f).
Proof. intros. reflexivity. Qed.
Lemma ION_ret_simple_reL : forall L cs r, ION.ret_simple (reL L cs) r = reL L (ION.ret_simple cs r).
Proof. intros. reflexivity. Qed.

Lemma ION_dst_ok_reL : forall L cs n, ION.dst_ok (reL L cs) n = ION.dst_ok cs n.   Proof. intros. reflexivity. Qed.
Lemma ION_at_sys_reL : forall segs L cs n, ION.at_sys segs (reL L cs) n = ION.at_sys segs cs n.   Proof. intros. reflexivity. Qed.
Lemma ION_reg_is_reL : forall L cs r z, ION.reg_is (reL L cs) r z = ION.reg_is cs r z.   Proof. intros. reflexivity. Qed.
Lemma ION_cnt_ok_reL : forall L cs, ION.cnt_ok (reL L cs) = ION.cnt_ok cs.   Proof. intros. reflexivity. Qed.
Lemma ION_openat_args_ok_reL : forall segs L cs, ION.openat_args_ok segs (reL L cs) = ION.openat_args_ok segs cs.   Proof. intros. reflexivity. Qed.
Lemma set_kn_reL' : forall L cs k, set_kn (reL L cs) k = reL L (set_kn cs k).   Proof. intros. reflexivity. Qed.
Lemma with_ss_reL' : forall L cs ss, with_ss (reL L cs) ss = reL L (with_ss cs ss).   Proof. intros. reflexivity. Qed.
Lemma set_reg_reL' : forall L cs n e, set_reg (reL L cs) n e = reL L (set_reg cs n e).   Proof. intros. reflexivity. Qed.
Lemma set_pc_reL' : forall L cs p, set_pc (reL L cs) p = reL L (set_pc cs p).   Proof. intros. reflexivity. Qed.
Lemma add_kn_reL' : forall L cs k, add_kn (reL L cs) k = reL L (add_kn cs k).   Proof. intros. reflexivity. Qed.
Lemma bump_reL' : forall L cs d, bump (reL L cs) d = reL L (bump cs d).   Proof. intros. reflexivity. Qed.
Ltac hk_norm := rewrite ?ret_lit_reL, ?reg_lit_reL, ?reg_reL, ?pc_reL, ?kn_reL, ?nxt_reL, ?a_ss_reL, ?brk_reL, ?fd_reL, ?tidset_reL, ?props_reL,
                        ?ION_ret_with_reL, ?ION_ret_simple_reL, ?ION_dst_ok_reL, ?ION_at_sys_reL, ?ION_reg_is_reL, ?ION_openat_args_ok_reL, ?ION_cnt_ok_reL,
                        ?set_kn_reL', ?with_ss_reL', ?set_reg_reL', ?set_pc_reL', ?add_kn_reL', ?bump_reL'.
Ltac hk_walk H :=
  hk_norm;
  lazymatch type of H with
  | Some _ = Some _ => apply some_inj in H; subst; try reflexivity
  | None = Some _ => discriminate H
  | (if ?b then _ else _) = Some _ => destruct b; try discriminate H; hk_walk H
  | (match ?x with _ => _ end) = Some _ => destruct x; try discriminate H; hk_walk H
  end.

Ltac hk_walk3 HL H :=
  hk_norm;
  lazymatch type of H with
  | Some _ = Some _ =>
      let E1 := fresh "E" in let E2 := fresh "E" in let E3 := fresh "E" in
      apply some_inj in H; pose proof (f_equal (fun t => fst (fst t)) H) as E1; pose proof (f_equal (fun t => snd (fst t)) H) as E2;
      pose proof (f_equal snd H) as E3; cbn [fst snd] in E1, E2, E3; subst; try reflexivity
  | None = Some _ => discriminate H
  | (match after_call ?n ?c ?r ?v ?k with _ => _ end) = Some _ =>
      let Hac := fresh "Hac" in
      destruct (after_call n c r v k) eqn:Hac; [rewrite (after_call_reL n _ c r v k _ HL Hac) | discriminate H]; hk_walk3 HL H
  | (if ?b then _ else _) = Some _ => destruct b; try discriminate H; hk_walk3 HL H
  | (match ?x with _ => _ end) = Some _ => destruct x; try discriminate H; hk_walk3 HL H
  end.
Lemma ION_node_fresha_reL : forall L cs r logc base cs', ledger_vars_lt (nxt cs) L = true ->
  ION.node_fresha cs r logc base = Some cs' -> ION.node_fresha (reL L cs) r logc base = Some (reL L cs').
Proof.
  intros L cs r logc base cs' HL H. unfold ION.node_fresha in *. destruct base as [rb|]; cbv zeta in H; cbv zeta; hk_norm;
    (destruct (fresh_ok NX0 cs) eqn:F; [rewrite (fresh_ok_reL NX0 L cs F HL) | rewrite ?Bool.andb_false_r in H; discriminate H]);
    hk_walk H.
Qed.
Lemma ION_node_srlsharp_reL : forall L cs r, ION.node_srlsharp (reL L cs) r = lmap L (ION.node_srlsharp cs r).
Proof. intros. unfold ION.node_srlsharp. hk_norm. destruct (_ && _)%bool; [|reflexivity]. destruct (lin_of (reg cs r)); reflexivity. Qed.
Lemma ION_node_srlsharp2_reL : forall L cs r1 r2, ION.node_srlsharp2 (reL L cs) r1 r2 = lmap L (ION.node_srlsharp2 cs r1 r2).
Proof. intros. unfold ION.node_srlsharp2. hk_norm. destruct (_ && _)%bool; [|reflexivity]. destruct (lin_of (reg cs r1)), (lin_of (reg cs r2)); reflexivity. Qed.
Lemma ION_xn_reL : forall segs T id args L cs cs', ledger_vars_lt (nxt cs) L = true ->
  ION.xn segs T id args cs = Some cs' -> ION.xn segs T id args (reL L cs) = Some (reL L cs').
Proof.
  intros segs T id args L cs cs' HL H. unfold ION.xn in *.
  destruct id as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|id]]]]]]]]]]]]]]]]]]]]]]]]]; try discriminate H.
  1: { unfold ION.node_openat_err in *. hk_walk H. }
  1: { unfold ION.node_read in *. cbv zeta in H. cbv zeta. hk_walk H. }
  1: { unfold ION.node_read_havoc in *. cbv zeta in H. cbv zeta. hk_walk H. }
  1: { unfold ION.node_read_eof in *. cbv zeta in H. cbv zeta. hk_walk H. }
  1: { unfold ION.node_read_dir in *. cbv zeta in H. cbv zeta. hk_walk H. }
  1: { unfold ION.node_close in *. cbv zeta in H. cbv zeta. hk_walk H. }
  1: { unfold ION.node_ioctl in *. cbv zeta in H. cbv zeta. hk_walk H. }
  1: { unfold ION.node_read_havoc_short in *. cbv zeta in H. cbv zeta. hk_walk H. }
  1: { unfold ION.node_header_facts in *. cbv zeta in H. cbv zeta. hk_walk H. }
  1: { unfold ION.node_lensplit in *. cbv zeta in H. cbv zeta.
       destruct (fresh_ok NX0 cs) eqn:F; [rewrite (fresh_ok_reL NX0 L cs F HL) | cbn [andb] in H]; hk_walk H. }
  3: { unfold ION.node_droplenfacts in *. cbv zeta in H. cbv zeta. hk_walk H. }
  1: { repeat (match type of H with (match ?x with _ => _ end) = Some _ => destruct x; try discriminate H
                                  | (if ?x then _ else _) = Some _ => destruct x; try discriminate H end);
       exact (ION_node_fresha_reL L cs _ _ _ cs' HL H). }
  1: { repeat (match type of H with (match ?x with _ => _ end) = Some _ => destruct x; try discriminate H
                                  | (if ?x then _ else _) = Some _ => destruct x; try discriminate H end);
       first [ rewrite ION_node_srlsharp_reL, H; reflexivity | rewrite ION_node_srlsharp2_reL, H; reflexivity ]. }
Qed.

(* [comment removed for export] *)
Lemma EXN_node_tabread_reL : forall segs IT nx0 L cs args cs', ledger_vars_lt (nxt cs) L = true ->
  EXN.node_tabread segs IT nx0 cs args = Some cs' -> EXN.node_tabread segs IT nx0 (reL L cs) args = Some (reL L cs').
Proof.
  intros segs IT nx0 L cs args cs' HL H. unfold EXN.node_tabread in *. hk_norm.
  destruct (fresh_ok nx0 cs) eqn:F; [rewrite (fresh_ok_reL nx0 L cs F HL) | cbn [andb negb] in H; discriminate H].
  cbv zeta in H. cbv zeta. hk_walk H.
Qed.
Lemma EXN_xn_reL : forall segs IT nx0 id args L cs cs', ledger_vars_lt (nxt cs) L = true ->
  EXN.xn segs IT nx0 id args cs = Some cs' -> EXN.xn segs IT nx0 id args (reL L cs) = Some (reL L cs').
Proof.
  intros segs IT nx0 id args L cs cs' HL H. rewrite EXN.xn_unfold in *.
  repeat (match type of H with (match ?x with _ => _ end) = Some _ => destruct x; try discriminate H end).
  1: { exact (EXN_node_tabread_reL segs IT nx0 L cs args cs' HL H). }
  1: { unfold EXN.node_recon in *. destruct args; [|discriminate H]. hk_norm. destruct (rec_onb (kn cs)); hk_walk H. }
  1: { unfold EXN.node_recoff in *. hk_walk H. }
  1: { unfold EXN.node_brespell in *. cbv zeta in H. cbv zeta. hk_walk H. }
  1: { (* [comment removed for export] *)
       unfold EXN.node_namecell in *. destruct args as [|a [|e l]]; try discriminate H. destruct e; try discriminate H.
       destruct l; [|discriminate H]. destruct (split_lit a) as [ab ao]. hk_norm.
       destruct (fresh_ok nx0 cs) eqn:F; [rewrite (fresh_ok_reL nx0 L cs F HL) | cbn [andb] in H; discriminate H].
       cbv zeta in H. cbv zeta. hk_walk H. }
Qed.

(* [comment removed for export] *)
Lemma EXW_xn_reL : forall segs IT nx0 id args L cs cs', ledger_vars_lt (nxt cs) L = true ->
  EXW.xn segs IT nx0 id args cs = Some cs' -> EXW.xn segs IT nx0 id args (reL L cs) = Some (reL L cs').
Proof.
  intros segs IT nx0 id args L cs cs' HL H. unfold EXW.xn in *.
  repeat (match type of H with (match ?x with _ => _ end) = Some _ => destruct x; try discriminate H end).
  all: try exact (EXN_xn_reL segs IT nx0 _ args L cs cs' HL H).
  1: { unfold EXW.node_sxband in *. destruct args as [|a l]; try discriminate H. destruct a; try discriminate H.
       destruct l; try discriminate H. hk_norm. cbv zeta in H. cbv zeta. hk_walk H. }
  1: { unfold EXW.node_wop64 in *. destruct args as [|a l]; try discriminate H. destruct a; try discriminate H.
       destruct l; try discriminate H. hk_norm. cbv zeta in H. cbv zeta. hk_walk H. }
  1: { (* [comment removed for export] *)
       unfold EXW.node_zeroword in *. destruct args as [|a [|e l]]; try discriminate H. destruct e; try discriminate H.
       destruct l; [|discriminate H]. destruct (split_lit a) as [ab ao]. hk_norm. cbv zeta in H. cbv zeta. hk_walk H. }
Qed.

(* [comment removed for export] *)
Lemma MVN_xn_reL : forall IT A args L cs cs',
  MVN.xn IT A args cs = Some cs' -> MVN.xn IT A args (reL L cs) = Some (reL L cs').
Proof.
  intros IT A args L cs cs' H. unfold MVN.xn in *. cbv zeta in H. cbv zeta. hk_walk H.
Qed.

(* [comment removed for export] *)
Lemma AN_xe_reL : forall segs A nx0 G id args L cs fd ps cs', ledger_vars_lt (nxt cs) L = true ->
  AN.xe segs A nx0 G id args cs = Some (fd, ps, cs') -> AN.xe segs A nx0 G id args (reL L cs) = Some (fd, ps, reL L cs').
Proof.
  intros segs A nx0 G id args L cs fd ps cs' HL H. rewrite AN.xe_unfold in *. destruct id; [|discriminate H].
  unfold AN.node_stdio_write in *. cbv zeta in H. cbv zeta. hk_walk3 HL H.
Qed.
End S.

(* [comment removed for export] *)
Section Prod.
Context {fx : FPState}.
Variable ip : imgparams.
Lemma sysws_std_reL : forall y cs L, AP.sys_ws_std y (reL L cs) = AP.sys_ws_std y cs.   Proof. intros. reflexivity. Qed.
Lemma xnp_ws_reL : forall id args cs L, xnp_ws id args (reL L cs) = xnp_ws id args cs.   Proof. intros. reflexivity. Qed.
Lemma xe_ws_reL : forall id args cs L, AN.xe_ws id args (reL L cs) = AN.xe_ws id args cs.   Proof. intros. reflexivity. Qed.
Lemma xws_std_reL : forall x args cs L, AP.x_ws_std x args (reL L cs) = AP.x_ws_std x args cs.   Proof. intros. reflexivity. Qed.
Lemma XNp_reL : forall IT T id args cs cs' L,
  (xnp_extF id = true \/ xnp_ws id args cs <> None) -> ledger_vars_lt (nxt cs) L = true ->
  XNp ip IT T id args cs = Some cs' -> XNp ip IT T id args (reL L cs) = Some (reL L cs').
Proof.
  intros IT T id args cs cs' L Had HL H. unfold xnp_extF, xnp_ws in Had.
  do 118 (destruct id as [|id];    (* [comment removed for export] *)
    [ cbn [XNp Nat.ltb Nat.leb Nat.eqb andb orb] in H, Had |- *;
      first [ exfalso; destruct Had as [Had|Had]; [discriminate Had | apply Had; reflexivity]
            | exact (ION_xn_reL _ _ _ _ L cs cs' HL H)
            | exact (EXW_xn_reL _ _ _ _ _ L cs cs' HL H)
            | exact (MVN_xn_reL _ _ _ L cs cs' H)
            | discriminate H ]
    | ]).
  cbn [XNp Nat.ltb Nat.leb Nat.eqb andb orb] in H. discriminate H.
Qed.
Lemma XEp_reL : forall id args cs fd ps cs' L, AN.xe_ws id args cs <> None -> ledger_vars_lt (nxt cs) L = true ->
  XEp ip id args cs = Some (fd, ps, cs') -> XEp ip id args (reL L cs) = Some (fd, ps, reL L cs').
Proof. intros id args cs fd ps cs' L _ HL H. unfold XEp in *. exact (AN_xe_reL _ _ _ _ id args L cs fd ps cs' HL H). Qed.
End Prod.
End HKL.
