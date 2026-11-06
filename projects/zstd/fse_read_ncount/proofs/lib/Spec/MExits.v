(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes HaltsTreeB.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad STree Malloc Stdio Adapter Driver.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import ProgDeps.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MExits.
Context {St : Type}.

Definition mexits (S : list word) {A} (m : Monad.M St A) : Prop := forall s, texits nexit S (m s).

Definition okP {A} (P : A -> Prop) (x : exc (A * St)) : Prop :=
  match x with Unr => True | Ok p => P (fst p) end.

Definition mpost {A} (P : A -> Prop) (m : Monad.M St A) : Prop := forall s, tleaves (okP P) (m s).

(* [comment removed for export] *)
Lemma mexits_ret S {A} (a : A) : mexits S (mret a).            Proof. intros s; exact I. Qed.
Lemma mexits_munr S {A} : mexits S (@munr St A).                Proof. intros s; exact I. Qed.
Lemma mexits_get S : mexits S (@mget St).                       Proof. intros s; exact I. Qed.
Lemma mexits_upd S (f : St -> St) : mexits S (mupd f).          Proof. intros s; exact I. Qed.

Lemma mexits_msys S {A} n (dec : resp -> option A) :
  match n with NExit _ => False | _ => True end -> mexits S (msys n dec).
Proof.
  intros Hn s. unfold msys, enode. apply texits_vis_noexit; [exact Hn|].
  intros r. destruct (dec r); exact I.
Qed.

Lemma mexits_bind S {A B} (m : Monad.M St A) (f : A -> Monad.M St B) :
  mexits S m -> (forall a, mexits S (f a)) -> mexits S (mbind m f).
Proof.
  intros Hm Hf s. unfold mbind, ebind. apply texits_bind; [apply Hm|].
  intros [|[a s']]; cbn; [exact I | apply Hf].
Qed.

Lemma mexits_bind_P S {A B} (P : A -> Prop) (m : Monad.M St A) (f : A -> Monad.M St B) :
  mexits S m -> mpost P m -> (forall a, P a -> mexits S (f a)) -> mexits S (mbind m f).
Proof.
  intros Hm Hp Hf s. unfold mbind, ebind. apply (texits_bind_P _ _ _ (okP P)); [apply Hm| apply Hp|].
  intros [|[a s']] H; cbn in *; [exact I | apply Hf; exact H].
Qed.

Lemma mexits_mloop S {X R} (body : X -> Monad.M St (X + R)) :
  (forall x, mexits S (body x)) -> forall fuel x, mexits S (mloop fuel body x).
Proof.
  intros Hb fuel. induction fuel as [|fuel IH]; intros x; cbn [mloop]; [apply mexits_munr|].
  apply mexits_bind; [apply Hb|]. intros [x'|r]; [apply IH | apply mexits_ret].
Qed.

Lemma mexits_if S {A} (b : bool) (m1 m2 : Monad.M St A) : mexits S m1 -> mexits S m2 -> mexits S (if b then m1 else m2).
Proof. intros; destruct b; assumption. Qed.

(* [comment removed for export] *)
Lemma mpost_ret {A} (P : A -> Prop) (a : A) : P a -> mpost P (mret a).   Proof. intros H s; exact H. Qed.
Lemma mpost_munr {A} (P : A -> Prop) : mpost P (@munr St A).            Proof. intros s; exact I. Qed.
Lemma mpost_get (P : St -> Prop) : (forall s, P s) -> mpost P (@mget St). Proof. intros H s; apply H. Qed.
Lemma mpost_upd (P : unit -> Prop) f : P tt -> mpost P (@mupd St f).   Proof. intros H s; exact H. Qed.

Lemma mpost_true {A} (m : Monad.M St A) : mpost (fun _ => True) m.
Proof. intros s. eapply tleaves_mono; [apply tleaves_true|]. intros [|p] _; exact I. Qed.

Lemma mpost_mono {A} (P P' : A -> Prop) (m : Monad.M St A) : mpost P m -> (forall a, P a -> P' a) -> mpost P' m.
Proof. intros Hm HP s. eapply tleaves_mono; [apply Hm|]. intros [|p]; cbn; auto. Qed.

Lemma mpost_msys {A} (P : A -> Prop) n (dec : resp -> option A) :
  (forall r a, dec r = Some a -> P a) -> mpost P (msys n dec).
Proof.
  intros H s. cbn. intros r. destruct (dec r) eqn:E; cbn; [eapply H; exact E | exact I].
Qed.

Lemma mpost_bind {A B} (P1 : A -> Prop) (P : B -> Prop) (m : Monad.M St A) (f : A -> Monad.M St B) :
  mpost P1 m -> (forall a, P1 a -> mpost P (f a)) -> mpost P (mbind m f).
Proof.
  intros Hm Hf s. unfold mbind, ebind. eapply (tleaves_bind _ (okP P1)); [apply Hm|].
  intros [|[a s']] H1; cbn in *; [exact I | apply Hf; exact H1].
Qed.

Lemma mpost_bind_t {A B} (P : B -> Prop) (m : Monad.M St A) (f : A -> Monad.M St B) :
  (forall a, mpost P (f a)) -> mpost P (mbind m f).
Proof. intros Hf. eapply mpost_bind; [apply mpost_true|]. intros a _; apply Hf. Qed.

Lemma mpost_mloop {X R} (P : R -> Prop) (body : X -> Monad.M St (X + R)) :
  (forall x, mpost (fun y => match y with inl _ => True | inr r => P r end) (body x)) ->
  forall fuel x, mpost P (mloop fuel body x).
Proof.
  intros Hb fuel. induction fuel as [|fuel IH]; intros x; cbn [mloop]; [apply mpost_munr|].
  eapply mpost_bind; [apply Hb|]. intros [x'|r] Hy; [apply IH | apply mpost_ret; exact Hy].
Qed.

Lemma mpost_if {A} (P : A -> Prop) (b : bool) (m1 m2 : Monad.M St A) : mpost P m1 -> mpost P m2 -> mpost P (if b then m1 else m2).
Proof. intros; destruct b; assumption. Qed.
End MExits.

Create HintDb mexits.
#[export] Hint Resolve mexits_ret mexits_munr mexits_get mexits_upd : mexits.
#[export] Hint Resolve mpost_munr mpost_true : mexits.

(* [comment removed for export] *)
Ltac mex :=
  lazymatch goal with
  | |- mexits _ (mret _) => apply mexits_ret
  | |- mexits _ munr => apply mexits_munr
  | |- mexits _ mget => apply mexits_get
  | |- mexits _ (mupd _) => apply mexits_upd
  | |- mexits _ (msys _ _) => apply mexits_msys; exact I
  | |- mexits _ (mbind _ _) => apply mexits_bind; [mex | intros ?; mex]
  | |- mexits _ (mloop _ _ _) => apply mexits_mloop; intros ?; mex
  | |- mexits _ (if ?b then _ else _) => first [apply mexits_if | destruct b]; mex
  | |- mexits _ (match ?x with _ => _ end) => destruct x; mex
  | |- mexits _ (let _ := ?x in _) => cbv zeta; mex
  | |- mexits _ _ => first [ assumption | solve [eauto 2 with mexits] | idtac ]
  | |- forall _, _ => intros ?; mex
  | |- _ => idtac
  end.

(* [comment removed for export] *)
Ltac mpo :=
  lazymatch goal with
  | |- mpost _ (mret _) => apply mpost_ret
  | |- mpost _ munr => apply mpost_munr
  | |- mpost _ (mbind _ _) =>
      first [ eapply mpost_bind; [ solve [ eauto 2 ] | intros ? Hp; mpo ]
            | apply mpost_bind_t; intros ?; mpo ]
  | |- mpost _ (if ?b then _ else _) => first [apply mpost_if | destruct b]; mpo
  | |- mpost _ (match ?x with _ => _ end) => destruct x; mpo
  | |- mpost _ (let _ := ?x in _) => cbv zeta; mpo
  | |- mpost _ _ => first [ assumption | solve [eauto 2 with mexits] | idtac ]
  | |- forall _, _ => intros ?; mpo
  | |- _ => idtac
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Alloc.
Variable S : list word.

Lemma ev_step_exits : forall atop e, mexits S (ev_step atop e).
Proof. intros atop e. unfold ev_step. destruct e; mex. Qed.

Lemma membed_exits : forall {R} atop (t : stree ev Z R), mexits S (membed atop t).
Proof.
  intros R atop t. induction t as [r | e k IH]; cbn [membed]; [apply mexits_ret|].
  apply mexits_bind; [apply ev_step_exits | exact IH].
Qed.

Lemma raw_malloc_exits : forall n, mexits S (raw_malloc n).
Proof. intros n. unfold raw_malloc. mex; try apply membed_exits. all: try (destruct a; mex). Qed.

Lemma raw_free_exits : forall p, mexits S (raw_free p).
Proof. intros p. unfold raw_free. mex; try apply membed_exits. Qed.
End Alloc.
#[export] Hint Resolve raw_malloc_exits raw_free_exits membed_exits ev_step_exits : mexits.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section StdioX.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
Variable S : list word.

Lemma stdio_write_loop_exits : forall fuel fd iov, mexits S (stdio_write_loop (St:=St) fuel fd iov).
Proof. induction fuel as [|fuel IH]; intros fd iov; cbn [stdio_write_loop]; mex. Qed.

Lemma stdio_write_exits : forall fd buf s, mexits S (stdio_write (St:=St) fd buf s).
Proof. intros fd buf s. unfold stdio_write. mex; apply stdio_write_loop_exits. Qed.

Lemma upd_so_exits : forall f, mexits S (upd_so get_so set_so f).
Proof. intros f. unfold upd_so. mex. Qed.

Lemma rd_so_exits : mexits S (rd_so get_so).
Proof. unfold rd_so. mex. Qed.

Local Hint Resolve stdio_write_loop_exits stdio_write_exits upd_so_exits rd_so_exits : mexits.

Lemma stdout_stdio_write_exits : forall l, mexits S (stdout_stdio_write get_so set_so l).
Proof. intros l. unfold stdout_stdio_write. mex. Qed.
Local Hint Resolve stdout_stdio_write_exits : mexits.

Lemma stdout_writefn_exits : forall l, mexits S (stdout_writefn get_so set_so l).
Proof. intros l. unfold stdout_writefn. mex. Qed.
Local Hint Resolve stdout_writefn_exits : mexits.

Lemma stdout_towrite_exits : mexits S (stdout_towrite get_so set_so).
Proof. unfold stdout_towrite. mex. Qed.
Local Hint Resolve stdout_towrite_exits : mexits.

Lemma stdout_fwritex_exits : forall l, mexits S (stdout_fwritex get_so set_so l).
Proof. intros l. unfold stdout_fwritex. mex. Qed.
Local Hint Resolve stdout_fwritex_exits : mexits.

Lemma out_pieces_exits : forall ps, mexits S (out_pieces get_so set_so ps).
Proof. induction ps as [|p ps IH]; cbn [out_pieces]; mex. Qed.
Local Hint Resolve out_pieces_exits : mexits.

Lemma stdout_vprintf_exits : forall ps, mexits S (stdout_vprintf get_so set_so ps).
Proof. intros ps. unfold stdout_vprintf. mex. Qed.

Lemma stdout_exit_flush_exits : mexits S (stdout_exit_flush get_so set_so).
Proof. unfold stdout_exit_flush. mex. Qed.

Lemma stderr_pieces_exits : forall ps buf, mexits S (stderr_pieces (St:=St) buf ps).
Proof. induction ps as [|p ps IH]; intros buf; cbn [stderr_pieces]; mex. Qed.
Local Hint Resolve stderr_pieces_exits : mexits.

Lemma stderr_fprintf_exits : forall ps, mexits S (stderr_fprintf (St:=St) ps).
Proof. intros ps. unfold stderr_fprintf. mex. Qed.

Lemma stderr_fwrite_exits : forall l, mexits S (stderr_fwrite (St:=St) l).
Proof. intros l. unfold stderr_fwrite. mex. Qed.

(* [comment removed for export] *)
Lemma s_diag_exits : forall d, mexits S (s_diag (St:=St) d).
Proof. intros d. unfold s_diag. destruct d; first [apply stderr_fprintf_exits | apply stderr_fwrite_exits]. Qed.

Lemma s_emit_exits : forall v, mexits S (s_emit get_so set_so v).
Proof. intros v. unfold s_emit. apply stdout_vprintf_exits. Qed.

Lemma io_S_diag_exits : forall d, mexits S (io_diag (io_S get_so set_so) d).   Proof. exact s_diag_exits. Qed.
Lemma io_S_emit_exits : forall v, mexits S (io_emit (io_S get_so set_so) v).   Proof. exact s_emit_exits. Qed.
Lemma io_S_exit_exits : mexits S (io_exit (io_S get_so set_so)).               Proof. exact stdout_exit_flush_exits. Qed.
End StdioX.
#[export] Hint Resolve stdio_write_loop_exits stdio_write_exits upd_so_exits rd_so_exits stdout_stdio_write_exits
  stdout_writefn_exits stdout_towrite_exits stdout_fwritex_exits out_pieces_exits stdout_vprintf_exits
  stdout_exit_flush_exits stderr_pieces_exits stderr_fprintf_exits stderr_fwrite_exits
  s_diag_exits s_emit_exits io_S_diag_exits io_S_emit_exits io_S_exit_exits : mexits.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AdapterX.
Context {St ptr : Type}.
Variable drv_malloc : Z -> Monad.M St (option ptr).
Variable drv_free : ptr -> Monad.M St unit.
Variable fuzz_one : list Z -> Monad.M St Z.
Variable emit : Z -> Monad.M St unit.
Variable S : list word.
Hypothesis MAL : forall n, mexits S (drv_malloc n).
Hypothesis FRE : forall p, mexits S (drv_free p).
Hypothesis FUZ : forall d, mexits S (fuzz_one d).
Hypothesis EMI : forall v, mexits S (emit v).
(* [comment removed for export] *)
Hypothesis FUZ0 : forall d, mpost (fun rc => rc = 0) (fuzz_one d).

Lemma run_calls_exits : forall n payload rc, mexits S (run_calls fuzz_one emit n payload rc).
Proof. induction n as [|n IH]; intros payload rc; cbn [run_calls]; mex. Qed.

Lemma run_calls_post : forall n payload rc, rc = 0 -> mpost (fun rc' => rc' = 0) (run_calls fuzz_one emit n payload rc).
Proof.
  induction n as [|n IH]; intros payload rc Hrc; cbn [run_calls]; [apply mpost_ret; exact Hrc|].
  eapply mpost_bind; [apply FUZ0|]. intros rc' Hrc'. mpo; try (apply IH; exact Hrc').
Qed.

Lemma target_run_exits : forall cfg payload, mexits S (target_run drv_malloc drv_free fuzz_one emit cfg payload).
Proof. intros cfg payload. unfold target_run. mex; try apply run_calls_exits. all: destruct a; mex; apply run_calls_exits. Qed.

Lemma target_run_post : forall cfg payload,
  mpost (fun c => c = 0 \/ c = 2) (target_run drv_malloc drv_free fuzz_one emit cfg payload).
Proof.
  intros cfg payload. unfold target_run. cbv zeta. apply mpost_bind_t. intros [owned|].
  - eapply mpost_bind; [apply run_calls_post; reflexivity|]. intros rc ->. mpo. left; reflexivity.
  - apply mpost_ret. right; reflexivity.
Qed.

Lemma target_alloc_init_exits : forall b, mexits S (target_alloc_init (St:=St) b).  Proof. intros b; apply mexits_ret. Qed.
Lemma target_alloc_count_exits : mexits S (target_alloc_count (St:=St)).          Proof. apply mexits_ret. Qed.
Lemma target_alloc_count_post : mpost (fun n => n = 0) (target_alloc_count (St:=St)). Proof. apply mpost_ret; reflexivity. Qed.
End AdapterX.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section DriverX.
Context {St ptr : Type}.
Variable io : IOStyle St.
Variable drv_malloc : Z -> Monad.M St (option ptr).
Variable drv_free : ptr -> Monad.M St unit.
Variable read_stage : Z.
Variable alloc_init : Z -> Monad.M St unit.
Variable run : Z -> list Z -> Monad.M St Z.
Variable alloc_count : Monad.M St Z.
Variable S : list word.
Hypothesis DIAG : forall d, mexits S (io_diag io d).
Hypothesis EMIT : forall v, mexits S (io_emit io v).
Hypothesis EXIT : mexits S (io_exit io).
Hypothesis MAL : forall n, mexits S (drv_malloc n).
Hypothesis FRE : forall p, mexits S (drv_free p).
Hypothesis AINIT : forall b, mexits S (alloc_init b).
Hypothesis RUN : forall c p, mexits S (run c p).
Hypothesis CNT : mexits S alloc_count.
Hypothesis RUN02 : forall c p, mpost (fun x => x = 0 \/ x = 2) (run c p).
Hypothesis CNT0 : mpost (fun n => n = 0) alloc_count.

Lemma read_loop_body_exits : forall fd path st, mexits S (read_loop_body io drv_malloc drv_free read_stage fd path st).
Proof. intros fd path st. unfold read_loop_body. mex. all: try (destruct a; mex). Qed.

Lemma read_all_exits : forall path, mexits S (read_all io drv_malloc drv_free read_stage path).
Proof. intros path. unfold read_all. mex; try apply read_loop_body_exits. all: try (destruct a; mex). Qed.

Lemma main_model_exits : forall argv, mexits S (main_model io drv_malloc drv_free read_stage alloc_init run alloc_count argv).
Proof. intros argv. unfold main_model. mex; try apply read_all_exits. all: try (destruct a; mex). Qed.

Lemma main_model_post : forall argv,
  mpost (fun c => c = 0 \/ c = 2) (main_model io drv_malloc drv_free read_stage alloc_init run alloc_count argv).
Proof.
  intros argv. unfold main_model.
  Local Ltac caseb := lazymatch goal with |- mpost _ (if ?b then _ else _) => destruct b end.
  caseb; [mpo; right; reflexivity|].
  apply mpost_bind_t. intros [|buf content]; [apply mpost_ret; right; reflexivity|].
  cbv zeta. caseb; [mpo; right; reflexivity|].
  caseb; [mpo; right; reflexivity|].
  apply mpost_bind_t; intros _.
  eapply mpost_bind; [apply RUN02|]. intros status Hst.
  eapply (mpost_bind (fun s' => s' = 0 \/ s' = 2)).
  - caseb; [| apply mpost_ret; exact Hst].
    eapply mpost_bind; [apply CNT0|]. intros n ->. apply mpost_ret. cbn. left; reflexivity.
  - intros st' Hst'. apply mpost_bind_t; intros _. apply mpost_ret. exact Hst'.
Qed.

(* [comment removed for export] *)
Lemma exit_model_exits : forall code,
  In (bv_and (Z_to_bv 64 code) (Z_to_bv 64 255)) S -> mexits S (exit_model io code).
Proof.
  intros code Hin s. unfold exit_model, mbind, ebind. apply texits_bind; [apply EXIT|].
  intros [|[u s']]; [exact I|]. cbn. split; [| intros r; exact I].
  intros mo c mo' [-> _]. exact Hin.
Qed.
End DriverX.
