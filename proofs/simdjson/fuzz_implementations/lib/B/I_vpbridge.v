(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import ITree Nodes Decode RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim Monad Stdio Canon.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import PP_Printf_stdio_iface PP_Printf_pieces PP_Printf_bridge.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import X_bridge X_bridge2.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import RT_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Definition vso_get (so : stdout_st) : stdout_st := so.
Definition vso_set (so : stdout_st) (_ : stdout_st) : stdout_st := so.
Lemma vso_GS : forall x so, vso_get (vso_set so x) = so. Proof. reflexivity. Qed.
Lemma vso_SS : forall x so so', vso_set so' (vso_set so x) = vso_set so' x. Proof. reflexivity. Qed.

Definition emit_prog : @M stdout_st unit :=
  stdout_towrite vso_get vso_set ;;; outsk (OUT_stdout vso_get vso_set) pieces_emit_0 (mret tt).

Lemma zlength_zeros_out' : forall k, zlength (zeros_out k) = 2 * Z.of_nat k.
Proof.
  induction k as [|k IH]; [reflexivity|]. rewrite zeros_out_S. unfold zlength in *. rewrite length_app. cbn [length]. lia.
Qed.

Lemma OUT_pure : forall p so, so_active so = true -> zlength (so_buf so) + zlength p <= 1024 ->
  (so_lbf_nl so = false \/ after_last_nl p = 0) -> zlength p <= OUT_MAX ->
  OUT_stdout (fun so : stdout_st => so) (fun (so _ : stdout_st) => so) p so
  = Ret (Ok (tt, mkStdout true (so_buf so ++ p) (so_lbf_nl so) (so_first so))).
Proof.
  intros p so ACT FIT NL MX. unfold OUT_stdout.
  replace (OUT_MAX <? zlength p) with false by (symmetry; apply Z.ltb_ge; lia).
  unfold stdout_fwritex, stdout_towrite, upd_so, mupd, rd_so, mbind, mget, mret. cbn [ebind bind fst snd].
  rewrite ACT. unfold STDOUT_BUFSIZ.
  replace (1024 - zlength (so_buf so) <? zlength p) with false by (symmetry; apply Z.ltb_ge; lia).
  destruct (so_lbf_nl so) eqn:NLB.
  - destruct NL as [NL|NL]; [discriminate|]. rewrite NL. cbn [Z.ltb Z.compare]. cbn [ebind bind fst snd].
    change (Z.to_nat 0) with 0%nat. rewrite skipn_O. destruct so; cbn in *; subst; reflexivity.
  - cbn [ebind bind fst snd]. destruct so; cbn in *; subst; reflexivity.
Qed.

Lemma emit_prog_lines : forall k, (k < 500)%nat ->
  emit_prog (so_lines k) = Ret (Ok (tt, emit0_next (so_lines k))).
Proof.
  intros k Hk. unfold emit_prog, pieces_emit_0. cbn [outsk].
  unfold stdout_towrite, upd_so, mupd, mbind, mret. cbn [ebind bind fst snd].
  unfold so_lines, vso_get, vso_set. cbn [so_active so_buf so_lbf_nl so_first].
  pose proof (zlength_zeros_out' k) as ZL. unfold zlength in ZL.
  do 5 (rewrite OUT_pure;
    [ cbn [ebind bind fst snd]
    | reflexivity
    | cbn [so_buf]; rewrite ?app_nil_r; unfold zlength; rewrite ?length_app; cbn [length]; lia
    | left; reflexivity
    | unfold OUT_MAX, zlength; cbn; lia ]).
  unfold emit0_next, so_lines. cbn [so_first so_buf]. rewrite !app_nil_r, <- app_assoc. reflexivity.
Qed.

Lemma TT_emit_init : forall (T : unit * stdout_st -> TSet), T (tt, so_lines 0) [] ->
  t_eq (TT (emit_prog stdout_init) T) (t_emit (evw 1 [48; 10]) (T (tt, so_lines 0))).
Proof.
  intros T HT. unfold emit_prog, pieces_emit_0. cbn [outsk].
  unfold stdout_towrite, upd_so, mupd, mbind, mret. rewrite ebind_ret_ok. cbn [fst snd].
  unfold stdout_init, vso_get, vso_set. cbn [so_active so_buf so_lbf_nl so_first].
  do 4 (rewrite OUT_pure;
    [ rewrite ebind_ret_ok; cbn [fst snd]
    | reflexivity
    | cbn [so_buf]; rewrite ?app_nil_r; unfold zlength; cbn [length app]; lia
    | right; reflexivity
    | unfold OUT_MAX, zlength; cbn; lia ]).
  rewrite (@TT_ebind (unit * stdout_st) (unit * stdout_st)). cbn [TT fst snd].
  set (so4 := {| so_active := _ ; so_buf := _ ; so_lbf_nl := _ ; so_first := _ |}).
  assert (E4 : so4 = mkStdout true [48] true true) by reflexivity. rewrite E4. clear so4 E4.
  unfold OUT_stdout. replace (OUT_MAX <? zlength [10]) with false by reflexivity.
  unfold stdout_fwritex, stdout_towrite, upd_so, mupd, rd_so, mbind, mget, mret.
  rewrite !ebind_ret_ok. cbn [fst snd so_active so_buf so_lbf_nl so_first].
  change (STDOUT_BUFSIZ - zlength [48] <? zlength [10]) with false. change (0 <? after_last_nl [10]) with true. cbv iota beta.
  change (firstn (Z.to_nat (after_last_nl [10])) [10]) with [10]. change (skipn (Z.to_nat (after_last_nl [10])) [10]) with (@nil Z).
  rewrite (@TT_ebind (unit * stdout_st) (unit * stdout_st)). cbn [TT fst snd].
  unfold stdout_writefn, upd_so, mupd, rd_so, mbind, mget, mret. rewrite !ebind_ret_ok. cbn [fst snd so_active so_buf so_lbf_nl so_first].
  rewrite ebind_ret_ok. cbn [fst snd].
  rewrite (@TT_ebind (unit * stdout_st) (unit * stdout_st)).
  rewrite (@TT_ebind (sret * stdout_st) (unit * stdout_st)).
  unfold msys, enode. cbn [TT].
  replace (dec_ioctl (efferr ENOTTY)) with (Some (SErr ENOTTY)) by (vm_compute; reflexivity).
  cbn [TT fst snd so_active so_buf so_lbf_nl so_first].
  unfold stdout_stdio_write, rd_so, upd_so, mupd, mbind, mget, mret. rewrite ebind_ret_ok. cbn [fst snd so_active so_buf so_lbf_nl so_first].
  rewrite ebind_ret_ok. cbn [fst snd so_active so_buf so_lbf_nl so_first].
  rewrite (@TT_ebind (unit * stdout_st) (unit * stdout_st)). cbn [TT fst snd so_active so_buf so_lbf_nl so_first app].
  unfold stdio_writev. change (iov_start [48] [10]) with [[48]; [10]].
  eapply t_eq_trans.
  { apply (TT_wv_loop (WV_FUEL [[48]; [10]]) 1 [[48]; [10]] (mkStdout true [48] false false));
      [cbn; lia | unfold WV_FUEL, iov_total, zlength; cbn; lia | unfold iov_total, zlength; cbn; lia | ].
    exact HT. }
  apply t_eq_refl.
Qed.

Lemma tok_emit_init : tok [1] (emit_prog stdout_init).
Proof.
  unfold emit_prog, pieces_emit_0. cbn [outsk].
  unfold stdout_towrite, upd_so, mupd, mbind, mret. rewrite ebind_ret_ok. cbn [fst snd].
  unfold stdout_init, vso_get, vso_set. cbn [so_active so_buf so_lbf_nl so_first].
  do 4 (rewrite OUT_pure;
    [ rewrite ebind_ret_ok; cbn [fst snd]
    | reflexivity
    | cbn [so_buf]; rewrite ?app_nil_r; unfold zlength; cbn [length app]; lia
    | right; reflexivity
    | unfold OUT_MAX, zlength; cbn; lia ]).
  apply tok_ebind; [| intros x; exact I].
  set (so4 := {| so_active := _ ; so_buf := _ ; so_lbf_nl := _ ; so_first := _ |}).
  assert (E4 : so4 = mkStdout true [48] true true) by reflexivity. rewrite E4. clear so4 E4.
  unfold OUT_stdout. replace (OUT_MAX <? zlength [10]) with false by reflexivity.
  unfold stdout_fwritex, stdout_towrite, upd_so, mupd, rd_so, mbind, mget, mret.
  rewrite !ebind_ret_ok. cbn [fst snd so_active so_buf so_lbf_nl so_first].
  change (STDOUT_BUFSIZ - zlength [48] <? zlength [10]) with false. change (0 <? after_last_nl [10]) with true. cbv iota beta.
  change (firstn (Z.to_nat (after_last_nl [10])) [10]) with [10].
  apply tok_ebind; [| intros x; exact I].
  unfold stdout_writefn, upd_so, mupd, rd_so, mbind, mget, mret. rewrite !ebind_ret_ok. cbn [fst snd so_active so_buf so_lbf_nl so_first].
  rewrite ebind_ret_ok. cbn [fst snd].
  unfold msys, enode. rewrite !ebind_vis. cbn [tok]. split; [left; reflexivity|].
  replace (dec_ioctl (efferr ENOTTY)) with (Some (SErr ENOTTY)) by (vm_compute; reflexivity).
  rewrite !ebind_ret_ok. cbn [fst snd so_active so_buf so_lbf_nl so_first].
  unfold stdout_stdio_write, rd_so, upd_so, mupd, mbind, mget, mret. rewrite !ebind_ret_ok. cbn [fst snd so_active so_buf so_lbf_nl so_first].
  apply tok_ebind; [| intros x; exact I].
  unfold stdio_writev. change (iov_start [48] [10]) with [[48]; [10]].
  apply tok_wv_loop; [left; reflexivity | cbn; lia | unfold WV_FUEL, iov_total, zlength; cbn; lia | unfold iov_total, zlength; cbn; lia].
Qed.

Lemma TT_emit : forall so (T : unit * stdout_st -> TSet),
  (so = stdout_init \/ exists k, (k < 500)%nat /\ so = so_lines k) -> T (tt, emit0_next so) [] ->
  t_eq (TT (emit_prog so) T) (t_emit (evw 1 (emit0_out so)) (T (tt, emit0_next so))).
Proof.
  intros so T [-> | (k & Hk & ->)] HT.
  - exact (TT_emit_init T HT).
  - rewrite (emit_prog_lines k Hk). cbn [TT]. unfold emit0_out, so_lines. cbn [so_first evw map].
    apply t_eq_sym, t_emit_nil_eq. exact HT.
Qed.

Lemma tok_emit : forall so, (so = stdout_init \/ exists k, (k < 500)%nat /\ so = so_lines k) -> tok [1] (emit_prog so).
Proof.
  intros so [-> | (k & Hk & ->)].
  - exact tok_emit_init.
  - rewrite (emit_prog_lines k Hk). cbn. exact I.
Qed.

Definition leaf_so (so' : stdout_st) (r : exc (unit * stdout_st)) : Prop :=
  match r with Ok q => snd q = so' | Unr => True end.

Lemma leaves_emit_init : tforall (leaf_so (so_lines 0)) (emit_prog stdout_init).
Proof.
  unfold emit_prog, pieces_emit_0. cbn [outsk].
  unfold stdout_towrite, upd_so, mupd, mbind, mret. rewrite ebind_ret_ok. cbn [fst snd].
  unfold stdout_init, vso_get, vso_set. cbn [so_active so_buf so_lbf_nl so_first].
  do 4 (rewrite OUT_pure;
    [ rewrite ebind_ret_ok; cbn [fst snd]
    | reflexivity
    | cbn [so_buf]; rewrite ?app_nil_r; unfold zlength; cbn [length app]; lia
    | right; reflexivity
    | unfold OUT_MAX, zlength; cbn; lia ]).
  set (so4 := {| so_active := _ ; so_buf := _ ; so_lbf_nl := _ ; so_first := _ |}).
  assert (E4 : so4 = mkStdout true [48] true true) by reflexivity. rewrite E4. clear so4 E4.
  unfold ebind at 1. eapply (tforall_bind (leaf_so (so_lines 0))); [| intros [|[[] s']] H; cbn in *; [exact I| exact H]].
  unfold OUT_stdout. replace (OUT_MAX <? zlength [10]) with false by reflexivity.
  unfold stdout_fwritex, stdout_towrite, upd_so, mupd, rd_so, mbind, mget, mret.
  rewrite !ebind_ret_ok. cbn [fst snd so_active so_buf so_lbf_nl so_first].
  change (STDOUT_BUFSIZ - zlength [48] <? zlength [10]) with false. change (0 <? after_last_nl [10]) with true. cbv iota beta.
  change (firstn (Z.to_nat (after_last_nl [10])) [10]) with [10]. change (skipn (Z.to_nat (after_last_nl [10])) [10]) with (@nil Z).
  unfold ebind at 1. eapply (tforall_bind (leaf_so (so_lines 0))); [| intros [|[[] s']] H; cbn in *; [exact I| subst s'; reflexivity]].
  unfold stdout_writefn, upd_so, mupd, rd_so, mbind, mget, mret. rewrite !ebind_ret_ok. cbn [fst snd so_active so_buf so_lbf_nl so_first].
  rewrite ebind_ret_ok. cbn [fst snd].
  unfold ebind at 1. eapply (tforall_bind (leaf_so (mkStdout true [48] false false))).
  - unfold msys, enode, ebind. cbn [ITree.bind tforall]. intros x.
    destruct (dec_ioctl x) as [[e|v]|]; cbn; [reflexivity | exact I | exact I].
  - intros [|[[] s']] H; [exact I|]. cbn [leaf_so fst snd] in H. subst s'.
    unfold stdout_stdio_write, rd_so, upd_so, mupd, mbind, mget, mret. rewrite !ebind_ret_ok. cbn [fst snd so_active so_buf so_lbf_nl so_first].
    unfold ebind at 1. eapply tforall_bind; [apply stdio_writev_leaves|].
    intros [|[[] s']] H; [exact I|]. cbn [leaf_so fst snd] in H. subst s'. reflexivity.
Qed.

Lemma leaves_emit : forall so, (so = stdout_init \/ exists k, (k < 500)%nat /\ so = so_lines k) ->
  tforall (leaf_so (emit0_next so)) (emit_prog so).
Proof.
  intros so [-> | (k & Hk & ->)].
  - exact leaves_emit_init.
  - rewrite (emit_prog_lines k Hk). cbn. reflexivity.
Qed.
