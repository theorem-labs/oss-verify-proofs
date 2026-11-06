(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1cq X1d0.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require Import X1rw X1rv X1rs X1s9 X1rr X1sb.
Import ListNotations.
Import X1cq.Exc.
Open Scope Z_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

Ltac red_ops := cbn [ret bind unreachable lib_malloc lib_free out_stderr out_stdout msg_store X1sb.ops lib_free_opt].

Section TargetSafe.
Context {St ptr : Type}.
Variable raw_malloc : Z -> X1rv.M St (option ptr).
Variable raw_free : ptr -> X1rv.M St unit.
Variable get_so : St -> stdout_st.
Variable set_so : stdout_st -> St -> St.
Variable own : list ptr -> assn St.

Hypothesis Hdm : forall X n, 0 <= n ->
mspec (own X) (raw_malloc n)
(fun r s mo => match r with Some p => own (p :: X) s mo /\ n < 2^63 | None => own X s mo end).
Hypothesis Hdf : forall X p, mspec (own (p :: X)) (raw_free p) (fun _ => own X).
Hypothesis Hperm : forall X Y s mo, Permutation X Y -> own X s mo -> own Y s mo.
Hypothesis Herr : forall X bs, zlength bs <= INTERNAL_BUFSIZ ->
mspec (own X) (stderr_fprintf (St:=St) [bs]) (fun _ => own X).
Hypothesis Hout : forall X, mspec (own X) (stdout_vprintf get_so set_so pieces_emit_0) (fun _ => own X).

Let ops : target_ops (X1rv.M St) ptr := X1sb.ops raw_malloc raw_free get_so set_so.

Definition tok_blocks (t : token (ptr:=ptr)) : list ptr :=
match t with
| TokEOF | TokPem _ _ => []
| TokSection n => [n]
| TokField n v => [n; v]
end.
Definition fn_blocks (f : option ptr) : list ptr :=
match f with Some p => [p] | None => [] end.
Definition lx_blocks (lx : lexer (ptr:=ptr)) : list ptr := tok_blocks (lx_tok lx) ++ fn_blocks (lx_filename lx).

Definition lx_wf (d : list Z) (lx : lexer (ptr:=ptr)) : Prop :=
0 <= lx_at lx /\ 0 <= lx_remaining lx /\ lx_at lx + lx_remaining lx = zlength d /\ 0 <= lx_line lx.

Lemma mspec_ret_ops {A} (a : A) (P : assn St) (Q : A -> assn St) :
(forall s mo, P s mo -> Q a s mo) -> mspec P (ret ops a) Q.
Proof. intros H. cbn. apply mspec_ret. exact H. Qed.

Lemma mspec_bind_ops {A B} (m : X1rv.M St A) (f : A -> X1rv.M St B) P Q1 Q :
mspec P m Q1 -> (forall a, mspec (Q1 a) (f a) Q) -> mspec P (bind ops m f) Q.
Proof. intros. cbn. eapply mspec_bind; eauto. Qed.

Lemma mspec_lib_free_opt : forall X (p : option ptr),
mspec (own (fn_blocks p ++ X)) (lib_free_opt raw_free p) (fun _ => own X).
Proof.
intros X [p|]; cbn.
- apply Hdf.
- apply mspec_ret. auto.
Qed.

Lemma precond_text_short : forall e f,
In e [EXPR_FILENAME; EXPR_SECTION; EXPR_FIELD] -> In f [FUNC_INIT; FUNC_NEXT] ->
zlength (precond_text e f) <= INTERNAL_BUFSIZ.
Proof.
intros e f He Hf.
destruct He as [<-|[<-|[<-|[]]]]; destruct Hf as [<-|[<-|[]]]; vm_compute; congruence.
Qed.
Lemma reached_text_short : zlength (reached_text FUNC_NEXT) <= INTERNAL_BUFSIZ.
Proof. vm_compute. congruence. Qed.

Lemma clear_state_mspec : forall X lx,
mspec (own (lx_blocks lx ++ X)) (clear_state ops lx)
(fun lx' => fun s mo => own (lx_blocks lx' ++ X) s mo /\
lx' = mkLexer (lx_filename lx) (lx_line lx) (lx_at lx) (lx_remaining lx) false TokEOF).
Proof.
intros X lx. unfold clear_state.
apply (mspec_bind_ops _ _ _ (fun _ => own (fn_blocks (lx_filename lx) ++ X))).
- unfold lx_blocks. destruct (lx_tok lx) as [|n|n v|b l]; cbn [tok_blocks app]; red_ops.
+ apply mspec_ret. intros s mo H. exact H.
+ apply Hdf.
+ apply (mspec_bind _ _ _ (fun _ => own (v :: fn_blocks (lx_filename lx) ++ X))); [apply Hdf|]. intros u. apply Hdf.
+ apply mspec_ret. intros s mo H. exact H.
- intros u. apply mspec_ret_ops. intros s mo H. split; [|reflexivity]. unfold lx_blocks. cbn [tok_blocks app lx_tok lx_filename]. exact H.
Qed.

Lemma lexer_msg_mspec : forall X lx msg,
lx_complained lx = false -> lx_tok lx = TokEOF ->
mspec (own X) (lexer_msg ops lx msg)
(fun lx' => fun s mo => own X s mo /\
lx' = mkLexer (lx_filename lx) (lx_line lx) (lx_at lx) (lx_remaining lx) true TokEOF).
Proof.
intros X lx msg Hc Ht. unfold lexer_msg. rewrite Hc, Ht.
apply (mspec_bind_ops _ _ _ (fun _ => own X)).
- red_ops. apply mspec_ret. intros s mo H. exact H.
- intros u. apply mspec_ret_ops. intros s mo H. auto.
Qed.

Definition next_post (d : list Z) (X : list ptr) (lx : lexer (ptr:=ptr)) (r : next_result (ptr:=ptr)) : assn St :=
fun s mo => let '(ok, failed, lx') := r in
own (lx_blocks lx' ++ X) s mo /\ lx_wf d lx' /\ lx_filename lx' = lx_filename lx /\
(ok = true -> lx_remaining lx' < lx_remaining lx) /\
(ok = false -> tok_blocks (lx_tok lx') = []).

Lemma next_post_weaken : forall d X lx lx0 r s mo,
next_post d X lx r s mo -> lx_filename lx = lx_filename lx0 -> lx_remaining lx <= lx_remaining lx0 ->
next_post d X lx0 r s mo.
Proof.
intros d X lx lx0 [[ok failed] lx'] s mo (H1 & H2 & H3 & H4 & H5) Ef Er. unfold next_post.
splits; auto; [congruence|]. intros Hok. specialize (H4 Hok). lia.
Qed.

Ltac fin_post := unfold next_post, lx_blocks, lx_wf in *;
cbn [tok_blocks fn_blocks app lx_tok lx_filename lx_at lx_remaining lx_line lx_complained set_tok] in *;
splits; auto; try lia; try (intros; discriminate); try congruence.

Lemma pem_body_mspec : forall d X lx,
lx_wf d lx -> lx_tok lx = TokEOF -> lx_complained lx = false -> lx_remaining lx <> 0 ->
mspec (own (fn_blocks (lx_filename lx) ++ X)) (pem_body ops d lx) (next_post d X lx).
Proof.
intros d X lx (A1 & A2 & A3 & A4) Ht Hc NE0. unfold pem_body.
destruct (strnstr_end d (lx_at lx) (lx_remaining lx)) as [pos|] eqn:ES.
- apply mspec_ret_ops. intros s mo H.
pose proof (strnstr_end_some d _ _ _ ES) as (P1 & P2 & P3).
set (e1 := match memchr d (pos + 1) 10 (lx_remaining lx - (pos - lx_at lx) - 1) with
| Some e => e + 1 | None => lx_at lx + lx_remaining lx end) in *.
assert (HE : lx_at lx < e1 <= lx_at lx + lx_remaining lx).
{ subst e1. destruct (memchr d (pos + 1) 10 (lx_remaining lx - (pos - lx_at lx) - 1)) as [e|] eqn:EM.
- apply memchr_some in EM; [|lia]. lia.
- lia. }
pose proof (count_nl_bounds d (lx_at lx) e1 (lx_line lx) ltac:(lia)) as CN.
fin_post.
- eapply mspec_bind_ops.
+ apply lexer_msg_mspec; assumption.
+ intros lx'. apply mspec_pure. intros ->. apply mspec_ret_ops. intros s mo H. fin_post.
Qed.

Lemma split_line_facts : forall d lx end_ lx2,
lx_wf d lx -> lx_remaining lx <> 0 -> split_line d lx = (end_, lx2) ->
lx_at lx <= end_ <= zlength d /\ lx_wf d lx2 /\ lx_remaining lx2 < lx_remaining lx /\ end_ <= lx_at lx2 /\
lx_filename lx2 = lx_filename lx /\ lx_tok lx2 = lx_tok lx /\ lx_complained lx2 = lx_complained lx.
Proof.
intros d lx end_ lx2 (A1 & A2 & A3 & A4) NE0 HS. unfold split_line in HS.
destruct (memchr d (lx_at lx) 10 (lx_remaining lx)) as [e|] eqn:EM.
- apply memchr_some in EM; [|lia]. injection HS as <- <-. unfold lx_wf; cbn; splits; auto; lia.
- injection HS as <- <-. unfold lx_wf; cbn; splits; auto; lia.
Qed.

Lemma line_body_mspec : forall d X (k : lexer -> X1rv.M St next_result) lx end_ lx2,
lx_at lx <= end_ <= zlength d -> lx_wf d lx2 -> lx_remaining lx2 < lx_remaining lx -> end_ <= lx_at lx2 ->
lx_filename lx2 = lx_filename lx -> lx_tok lx2 = TokEOF -> lx_complained lx2 = false ->
mspec (own (fn_blocks (lx_filename lx2) ++ X)) (k lx2) (next_post d X lx2) ->
mspec (own (fn_blocks (lx_filename lx) ++ X)) (line_body ops d k lx end_ lx2) (next_post d X lx).
Proof.
intros d X k lx end_ lx2 B1 B2 B3 B3' B4 B5 B6 Hk. unfold line_body.
destruct lx2 as [fn2 ln2 at2 rem2 c2 tok2].
cbn [lx_filename lx_tok lx_complained lx_at lx_remaining lx_line] in *. subst fn2 tok2 c2.
pose proof B2 as (C1 & C2 & C3 & C4).
pose proof (skip_fwd_bounds d (lx_at lx) end_ ltac:(destruct B2; lia)) as SF.
set (line1 := skip_fwd d (lx_at lx) end_) in *.
pose proof (skip_back_bounds d line1 end_ ltac:(lia)) as SB.
set (end1 := skip_back d line1 end_) in *.
destruct ((line1 =? end1) || (znth d line1 =? 35)) eqn:EC.
{
eapply mspec_post; [exact Hk|].
intros r s mo H. eapply next_post_weaken; [exact H| reflexivity| cbn [lx_remaining]; lia]. }
assert (HB : line1 < end1).
{ apply Bool.orb_false_elim in EC. destruct EC as [EC1 _]. apply Z.eqb_neq in EC1. lia. }
destruct (znth d line1 =? 91) eqn:ESEC.
-
destruct (negb (znth d (end1 - 1) =? 93)) eqn:EBR.
+ eapply mspec_bind_ops; [apply lexer_msg_mspec; reflexivity|].
intros lx'. apply mspec_pure. intros ->. apply mspec_ret_ops. intros s mo H. fin_post.
+ eapply mspec_bind_ops.
{ red_ops. apply Hdm. lia. }
intros [p|]; red_ops.
* apply mspec_pure. intros _. apply mspec_ret_ops. intros s mo H. fin_post.
* eapply mspec_bind_ops.
-- red_ops. apply Herr. apply precond_text_short; cbn [In]; auto.
-- intros u. apply mspec_ret_ops. intros s mo H. fin_post.
-
destruct (memchr d line1 58 (end1 - line1)) as [colon|] eqn:ECOL.
+ apply memchr_some in ECOL; [|lia]. destruct ECOL as (D1 & D2 & D3).
pose proof (skip_fwd_bounds d (colon + 1) end1 ltac:(lia)) as SV.
pose proof (skip_back_bounds d line1 colon ltac:(lia)) as SC.
eapply mspec_bind_ops.
{ red_ops. apply Hdm. lia. }
intros [pn|]; red_ops.
* apply mspec_pure. intros _.
eapply mspec_bind_ops.
{ red_ops. apply Hdm. lia. }
intros [pv|]; red_ops.
-- apply mspec_pure. intros _. apply mspec_ret_ops. intros s mo H. fin_post.
eapply Hperm; [|exact H]. apply perm_swap.
-- apply (mspec_bind_ops _ _ _ (fun _ => own (fn_blocks (lx_filename lx) ++ X))); [apply Hdf|]. intros u.
eapply mspec_bind_ops.
{ red_ops. apply Herr. apply reached_text_short. }
intros u'. apply mspec_ret_ops. intros s mo H. fin_post.
* eapply mspec_bind_ops.
-- red_ops. apply Herr. apply precond_text_short; cbn [In]; auto.
-- intros u. apply mspec_ret_ops. intros s mo H. fin_post.
+ eapply mspec_bind_ops; [apply lexer_msg_mspec; reflexivity|].
intros lx'. apply mspec_pure. intros ->. apply mspec_ret_ops. intros s mo H. fin_post.
Qed.

Lemma next_loop_mspec : forall d X fuel lx,
lx_wf d lx -> lx_tok lx = TokEOF -> lx_complained lx = false ->
(Z.to_nat (lx_remaining lx) < fuel)%nat ->
mspec (own (fn_blocks (lx_filename lx) ++ X)) (next_loop ops d fuel lx) (next_post d X lx).
Proof.
intros d X fuel. induction fuel as [|fuel IH]; intros lx WF Ht Hc Hfuel; [lia|].
pose proof WF as (A1 & A2 & A3 & A4).
cbn [next_loop].
destruct (Z.eqb_spec (lx_remaining lx) 0) as [E0|NE0].
{ apply mspec_ret_ops. intros s mo H. fin_post. all: rewrite ?Ht; auto. }
destruct ((11 <=? lx_remaining lx) && strncmp_lit d (lx_at lx) PEM_BEGIN) eqn:EP.
- apply pem_body_mspec; assumption.
- destruct (split_line d lx) as [end_ lx2] eqn:HS.
destruct (split_line_facts d lx end_ lx2 WF NE0 HS) as (B1 & B2 & B3 & B3' & B4 & B5 & B6).
apply (line_body_mspec d X (next_loop ops d fuel) lx end_ lx2); auto; try congruence.
apply IH; auto; try congruence. destruct B2 as (?&?&?&?). lia.
Qed.

Lemma lexer_next_mspec : forall d X lx,
lx_wf d lx ->
mspec (own (lx_blocks lx ++ X)) (lexer_next ops d lx) (next_post d X lx).
Proof.
intros d X lx WF. unfold lexer_next. eapply mspec_bind_ops.
- apply clear_state_mspec.
- intros lx1. apply mspec_pure. intros ->. unfold lx_blocks; red_ops.
eapply mspec_post.
+ apply (next_loop_mspec d X); cbn; auto.
all: destruct WF as (?&?&?&?); unfold lx_wf in *; cbn in *; lia.
+ intros [[ok failed] lx'] s mo. unfold next_post; cbn [lx_filename lx_remaining]. intros H. exact H.
Qed.

Lemma lex_all_mspec : forall d X fuel lx,
lx_wf d lx -> (Z.to_nat (lx_remaining lx) < fuel)%nat ->
mspec (own (lx_blocks lx ++ X)) (lex_all ops d fuel lx)
(fun lx' => fun s mo => own (lx_blocks lx' ++ X) s mo /\ tok_blocks (lx_tok lx') = [] /\
lx_filename lx' = lx_filename lx).
Proof.
intros d X fuel. induction fuel as [|fuel IH]; intros lx WF Hfuel; [lia|].
cbn [lex_all]. eapply mspec_bind_ops; [apply lexer_next_mspec; exact WF|].
intros [[ok failed] lx']. unfold next_post.
destruct ok.
- apply mspec_pure. intros (WF' & Hfn & Hlt & _). specialize (Hlt eq_refl).
eapply mspec_post; [apply IH; [exact WF'|]|].
{ destruct WF as (?&?&?&?). destruct WF' as (?&?&?&?). lia. }
intros lx'' s mo (H1 & H2 & H3). splits; auto. congruence.
- apply mspec_pure. intros (WF' & Hfn & _ & Htok). specialize (Htok eq_refl).
apply mspec_ret_ops. intros s mo H. auto.
Qed.

Lemma Herr_precond : forall X e f,
In e [EXPR_FILENAME; EXPR_SECTION; EXPR_FIELD] -> In f [FUNC_INIT; FUNC_NEXT] ->
mspec (own X) (stderr_fprintf (St:=St) [precond_text e f]) (fun _ => own X).
Proof. intros X e f He Hf. apply Herr. apply precond_text_short; assumption. Qed.
Lemma Herr_reached : forall X,
mspec (own X) (stderr_fprintf (St:=St) [reached_text FUNC_NEXT]) (fun _ => own X).
Proof. intros X. apply Herr. apply reached_text_short. Qed.
Lemma fuzz_input_len : 0 <= zlength FUZZ_INPUT + 1 /\ zlength FUZZ_INPUT + 1 = 11.
Proof. vm_compute. split; congruence. Qed.

Lemma fuzz_one_mspec : forall d X,
mspec (own X) (fuzz_one ops d) (fun rc => fun s mo => own X s mo /\ rc = 0).
Proof.
intros d X. unfold fuzz_one.
apply (mspec_bind_ops _ _ _ (fun lx => fun s mo => own (lx_blocks lx ++ X) s mo /\ lx_wf d lx /\ lx_tok lx = TokEOF)).
-
unfold lexer_init.
apply (mspec_bind_ops _ _ _ (fun r s mo => match r with Some p => own (p :: X) s mo /\ zlength FUZZ_INPUT + 1 < 2^63 | None => own X s mo end)).
+ red_ops. apply Hdm. apply (proj1 fuzz_input_len).
+ intros r. apply (mspec_bind_ops _ _ _ (fun _ => own (fn_blocks r ++ X))).
* destruct r as [p|]; red_ops.
-- apply mspec_pure. intros _. apply mspec_ret. intros s mo H. exact H.
-- apply Herr_precond; cbn [In]; tauto.
* intros u. apply mspec_ret_ops. intros s mo H.
unfold lx_blocks, lx_wf; cbn [tok_blocks fn_blocks app lx_tok lx_filename lx_at lx_remaining lx_line]. splits; auto; unfold zlength; try lia.
- intros lx. apply mspec_pure. intros [WF Htok].
apply (mspec_bind_ops _ _ _ (fun lx' => fun s mo => own (lx_blocks lx' ++ X) s mo /\ tok_blocks (lx_tok lx') = [] /\ lx_filename lx' = lx_filename lx)).
+ apply lex_all_mspec; [exact WF|]. destruct WF as (?&?&?&?). lia.
+ intros lx'. apply mspec_pure. intros [Htok' Hfn].
apply (mspec_bind_ops _ _ _ (fun _ => own X)).
* unfold lexer_done. eapply mspec_bind_ops; [apply clear_state_mspec|].
intros lx1. apply mspec_pure. intros ->. unfold lx_blocks; red_ops. cbn [tok_blocks app lx_filename lx_tok].
apply mspec_lib_free_opt.
* intros u. apply mspec_ret_ops. intros s mo H. auto.
Qed.

Lemma run_calls_mspec : forall d X n rc,
rc = 0 ->
mspec (own X) (run_calls ops d n rc) (fun rc' => fun s mo => own X s mo /\ rc' = 0).
Proof.
intros d X n. induction n as [|n IH]; intros rc Hrc; cbn [run_calls].
- apply mspec_ret_ops. intros s mo H. auto.
- apply (mspec_bind_ops _ _ _ (fun rc' => fun s mo => own X s mo /\ rc' = 0)); [apply fuzz_one_mspec|].
intros rc'. apply mspec_pure. intros ->. apply (mspec_bind_ops _ _ _ (fun _ => own X)).
+ red_ops. apply Hout.
+ intros u. apply IH. reflexivity.
Qed.

Theorem target_run_mspec : forall X cfg payload,
mspec (own X) (X1sb.target_run raw_malloc raw_free get_so set_so cfg payload) (fun _ => own X).
Proof.
intros X cfg payload. unfold X1sb.target_run, X1rr.target_run.
apply (mspec_bind_ops _ _ _ (fun a => match a with None => own X | Some owned => own (fn_blocks owned ++ X) end)).
- destruct (zlength payload =? 0) eqn:EZ.
+ apply mspec_ret_ops. intros s mo H. cbn [fn_blocks app]. exact H.
+ apply (mspec_bind_ops _ _ _ (fun r s mo => match r with Some p => own (p :: X) s mo /\ zlength payload < 2^63 | None => own X s mo end)).
* red_ops. apply Hdm. unfold zlength. lia.
* intros [p|]; red_ops.
-- apply mspec_pure. intros _. apply mspec_ret. intros s mo H. exact H.
-- apply mspec_ret. intros s mo H. exact H.
- intros [owned|].
+ apply (mspec_bind_ops _ _ _ (fun rc => fun s mo => own (fn_blocks owned ++ X) s mo /\ rc = 0)); [apply run_calls_mspec; reflexivity|].
intros rc. apply mspec_pure. intros ->. apply (mspec_bind_ops _ _ _ (fun _ => own X)).
* apply mspec_lib_free_opt.
* intros u. apply mspec_ret_ops. intros s mo H. exact H.
+ apply mspec_ret_ops. intros s mo H. exact H.
Qed.

End TargetSafe.
