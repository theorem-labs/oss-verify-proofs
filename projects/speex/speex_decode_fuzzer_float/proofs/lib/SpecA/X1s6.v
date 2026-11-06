(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1d7 X1cx X1cy X1cq X1d0 X1cl X1ci.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require Import X1rw X1rv X1s9 X1rz X1rn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require X1rt.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require Import X1rr X1sb X1sc.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require Import X1s1 X1s2 X1s4 X1s3 X1s5.
Import ListNotations.
Import X1cq.Exc.
Open Scope Z_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
Ltac red_ops := cbn [ret bind unreachable lib_malloc lib_free out_stderr out_stdout msg_store X1sb.ops lib_free_opt].

Section TargetE.
Context {CE__ : Ceiling}.
Variable sel : option bool.
Variable X : list event -> Prop.

Let ops : target_ops (X1rv.M PState) bptr := X1sb.ops raw_malloc raw_free ps_so set_so_ps.

Lemma mspecE_ret_ops {A} (a : A) (P : assnE PState) (Q : A -> assnE PState) :
(forall s mo tr, P s mo tr -> Q a s mo tr) -> mspecE sel X P (ret ops a) Q.
Proof. intros H. cbn. apply mspecE_ret. exact H. Qed.

Lemma mspecE_bind_ops {A B} (m : X1rv.M PState A) (f : A -> X1rv.M PState B) P Q1 Q :
mspecE sel X P m Q1 -> (forall a, mspecE sel X (Q1 a) (f a) Q) -> mspecE sel X P (bind ops m f) Q.
Proof. intros. cbn. eapply mspecE_bind; eauto. Qed.

Lemma size_ok : forall n, n < 2^62 -> X1rt.size_overflows n = false.
Proof. intros n H. unfold X1rt.size_overflows. apply Z.leb_gt. lia. Qed.

Section Lexer.
Variable K : assnE PState.
Hypothesis HK : fstable K.
Variable d : list Z.
Hypothesis Hd : zlength d < 2^61.

Lemma malloc_ops_E : forall n, n < 2^62 ->
mspecE sel X K (lib_malloc ops n) (fun r s mo tr => K s mo tr /\ r <> None).
Proof. intros n Hn. red_ops. apply raw_malloc_E; [exact HK| apply size_ok; exact Hn]. Qed.

Lemma free_ops_E : forall p, mspecE sel X K (lib_free ops p) (fun _ => K).
Proof. intros [p|]; red_ops; [apply raw_free_E; exact HK| apply mspecE_ret; auto]. Qed.

Lemma clear_state_E : forall lx,
mspecE sel X K (clear_state ops lx)
(fun lx' s mo tr => K s mo tr /\ lx' = mkLexer (lx_filename lx) (lx_line lx) (lx_at lx) (lx_remaining lx) false TokEOF).
Proof.
intros lx. unfold clear_state. apply (mspecE_bind_ops _ _ _ (fun _ => K)).
- destruct (lx_tok lx) as [|n|n v|b l]; red_ops.
+ apply mspecE_ret. auto.
+ apply raw_free_E. exact HK.
+ eapply mspecE_seq; [apply raw_free_E; exact HK|]. intros _. apply raw_free_E. exact HK.
+ apply mspecE_ret. auto.
- intros u. apply mspecE_ret_ops. auto.
Qed.

Lemma lexer_msg_E : forall lx msg,
lx_complained lx = false -> lx_tok lx = TokEOF ->
mspecE sel X K (lexer_msg ops lx msg)
(fun lx' s mo tr => K s mo tr /\ lx' = mkLexer (lx_filename lx) (lx_line lx) (lx_at lx) (lx_remaining lx) true TokEOF).
Proof.
intros lx msg Hc Ht. unfold lexer_msg. rewrite Hc, Ht.
apply (mspecE_bind_ops _ _ _ (fun _ => K)).
- red_ops. apply mspecE_ret. auto.
- intros u. apply mspecE_ret_ops. auto.
Qed.

Definition next_postE (lx : lexer (ptr:=bptr)) (r : next_result (ptr:=bptr)) : assnE PState :=
fun s mo tr => let '(ok, failed, lx') := r in K s mo tr /\ lx_wf d lx' /\ lx_filename lx' = lx_filename lx.

Ltac fin_postE := unfold next_postE, lx_wf in *;
cbn [lx_tok lx_filename lx_at lx_remaining lx_line lx_complained set_tok] in *;
splits; auto; try lia; try congruence.

Lemma pem_body_E : forall lx,
lx_wf d lx -> lx_tok lx = TokEOF -> lx_complained lx = false -> lx_remaining lx <> 0 ->
mspecE sel X K (pem_body ops d lx) (next_postE lx).
Proof.
intros lx (A1 & A2 & A3 & A4) Ht Hc NE0. unfold pem_body.
destruct (strnstr_end d (lx_at lx) (lx_remaining lx)) as [pos|] eqn:ES.
- apply mspecE_ret_ops. intros s mo tr H.
pose proof (strnstr_end_some d _ _ _ ES) as (P1 & P2 & P3).
set (e1 := match memchr d (pos + 1) 10 (lx_remaining lx - (pos - lx_at lx) - 1) with
| Some e => e + 1 | None => lx_at lx + lx_remaining lx end) in *.
assert (HE : lx_at lx < e1 <= lx_at lx + lx_remaining lx).
{ subst e1. destruct (memchr d (pos + 1) 10 (lx_remaining lx - (pos - lx_at lx) - 1)) as [e|] eqn:EM.
- apply memchr_some in EM; [|lia]. lia.
- lia. }
pose proof (count_nl_bounds d (lx_at lx) e1 (lx_line lx) ltac:(lia)) as CN.
fin_postE.
- eapply mspecE_bind_ops.
+ apply lexer_msg_E; assumption.
+ intros lx'. apply mspecE_pure. intros ->. apply mspecE_ret_ops. intros s mo tr H. fin_postE.
Qed.

Lemma line_body_E : forall (k : lexer -> X1rv.M PState next_result) lx end_ lx2,
0 <= lx_at lx -> lx_at lx <= end_ <= zlength d -> lx_wf d lx2 -> end_ <= lx_at lx2 ->
lx_filename lx2 = lx_filename lx -> lx_tok lx2 = TokEOF -> lx_complained lx2 = false ->
mspecE sel X K (k lx2) (next_postE lx2) ->
mspecE sel X K (line_body ops d k lx end_ lx2) (next_postE lx).
Proof.
intros k lx end_ lx2 B0 B1 B2 B3' B4 B5 B6 Hk. unfold line_body.
destruct lx2 as [fn2 ln2 at2 rem2 c2 tok2].
cbn [lx_filename lx_tok lx_complained lx_at lx_remaining lx_line] in *. subst fn2 tok2 c2.
pose proof B2 as (C1 & C2 & C3 & C4).
pose proof (skip_fwd_bounds d (lx_at lx) end_ ltac:(destruct B2; lia)) as SF.
set (line1 := skip_fwd d (lx_at lx) end_) in *.
pose proof (skip_back_bounds d line1 end_ ltac:(lia)) as SB.
set (end1 := skip_back d line1 end_) in *.
destruct ((line1 =? end1) || (znth d line1 =? 35)) eqn:EC.
{ eapply mspecE_post; [exact Hk|].
intros [[ok failed] lx'] s mo tr H. unfold next_postE in *. destruct H as (H1 & H2 & H3). splits; auto. }
assert (HB : line1 < end1).
{ apply Bool.orb_false_elim in EC. destruct EC as [EC1 _]. apply Z.eqb_neq in EC1. lia. }
destruct (znth d line1 =? 91) eqn:ESEC.
- destruct (negb (znth d (end1 - 1) =? 93)) eqn:EBR.
+ eapply mspecE_bind_ops; [apply lexer_msg_E; reflexivity|].
intros lx'. apply mspecE_pure. intros ->. apply mspecE_ret_ops. intros s mo tr H. fin_postE.
+ eapply mspecE_bind_ops; [apply malloc_ops_E; lia|].
intros [p|]; red_ops.
* apply mspecE_pure. intros _. apply mspecE_ret_ops. intros s mo tr H. fin_postE.
* apply mspecE_pure. intros []. reflexivity.
- destruct (memchr d line1 58 (end1 - line1)) as [colon|] eqn:ECOL.
+ apply memchr_some in ECOL; [|lia]. destruct ECOL as (D1 & D2 & D3).
pose proof (skip_fwd_bounds d (colon + 1) end1 ltac:(lia)) as SV.
pose proof (skip_back_bounds d line1 colon ltac:(lia)) as SC.
eapply mspecE_bind_ops; [apply malloc_ops_E; lia|].
intros [pn|]; red_ops; [|apply mspecE_pure; intros []; reflexivity].
apply mspecE_pure. intros _.
eapply mspecE_bind_ops; [apply malloc_ops_E; lia|].
intros [pv|]; red_ops; [|apply mspecE_pure; intros []; reflexivity].
apply mspecE_pure. intros _. apply mspecE_ret_ops. intros s mo tr H. fin_postE.
+ eapply mspecE_bind_ops; [apply lexer_msg_E; reflexivity|].
intros lx'. apply mspecE_pure. intros ->. apply mspecE_ret_ops. intros s mo tr H. fin_postE.
Qed.

Lemma next_loop_E : forall fuel lx,
lx_wf d lx -> lx_tok lx = TokEOF -> lx_complained lx = false ->
mspecE sel X K (next_loop ops d fuel lx) (next_postE lx).
Proof.
intros fuel. induction fuel as [|fuel IH]; intros lx WF Ht Hc; [apply mspecE_munr|].
pose proof WF as (A1 & A2 & A3 & A4).
cbn [next_loop].
destruct (Z.eqb_spec (lx_remaining lx) 0) as [E0|NE0].
{ apply mspecE_ret_ops. intros s mo tr H. fin_postE. }
destruct ((11 <=? lx_remaining lx) && strncmp_lit d (lx_at lx) PEM_BEGIN) eqn:EP.
- apply pem_body_E; assumption.
- destruct (split_line d lx) as [end_ lx2] eqn:HS.
destruct (split_line_facts d lx end_ lx2 WF NE0 HS) as (B1 & B2 & B3 & B3' & B4 & B5 & B6).
apply (line_body_E (next_loop ops d fuel) lx end_ lx2); auto; try congruence.
apply IH; auto; congruence.
Qed.

Lemma lexer_next_E : forall lx, lx_wf d lx -> mspecE sel X K (lexer_next ops d lx) (next_postE lx).
Proof.
intros lx WF. unfold lexer_next. eapply mspecE_bind_ops; [apply clear_state_E|].
intros lx1. apply mspecE_pure. intros ->.
eapply mspecE_post.
- apply next_loop_E; cbn; auto.
- intros [[ok failed] lx'] s mo tr. unfold next_postE; cbn [lx_filename]. intros H. exact H.
Qed.

Lemma lex_all_E : forall fuel lx, lx_wf d lx ->
mspecE sel X K (lex_all ops d fuel lx) (fun lx' s mo tr => K s mo tr /\ lx_filename lx' = lx_filename lx).
Proof.
intros fuel. induction fuel as [|fuel IH]; intros lx WF; [apply mspecE_munr|].
cbn [lex_all]. eapply mspecE_bind_ops; [apply lexer_next_E; exact WF|].
intros [[ok failed] lx']. unfold next_postE. apply mspecE_pure. intros (WF' & Hfn).
destruct ok.
- eapply mspecE_post; [apply IH; exact WF'|]. intros lx'' s mo tr (H1 & H2). split; [exact H1| congruence].
- apply mspecE_ret_ops. intros s mo tr H. auto.
Qed.

Lemma fuzz_input_len11 : zlength FUZZ_INPUT + 1 = 11.
Proof. vm_compute. reflexivity. Qed.

Lemma fuzz_one_E : mspecE sel X K (fuzz_one ops d) (fun rc s mo tr => K s mo tr /\ rc = 0).
Proof.
unfold fuzz_one.
apply (mspecE_bind_ops _ _ _ (fun lx s mo tr => K s mo tr /\ lx_wf d lx)).
- unfold lexer_init.
eapply mspecE_bind_ops; [apply malloc_ops_E; rewrite fuzz_input_len11; lia|].
intros r. apply mspecE_pure. intros Hr. destruct r as [p|]; [|contradiction Hr; reflexivity].
apply (mspecE_bind_ops _ _ _ (fun _ => K)); [red_ops; apply mspecE_ret; auto|].
intros u. apply mspecE_ret_ops. intros s mo tr H. split; [exact H|].
unfold lx_wf; cbn [lx_at lx_remaining lx_line]. unfold zlength in *. lia.
- intros lx. apply mspecE_pure. intros WF.
apply (mspecE_bind_ops _ _ _ (fun lx' s mo tr => K s mo tr /\ lx_filename lx' = lx_filename lx)); [apply lex_all_E; exact WF|].
intros lx'. apply mspecE_pure. intros Hfn.
apply (mspecE_bind_ops _ _ _ (fun _ => K)).
+ unfold lexer_done. eapply mspecE_bind_ops; [apply clear_state_E|].
intros lx1. apply mspecE_pure. intros ->. apply free_ops_E.
+ intros u. apply mspecE_ret_ops. auto.
Qed.

End Lexer.

Definition so_after (j : nat) : stdout_st :=
match j with O => stdout_init | S j' => mkStdout true (zeros_out j') false false end.
Definition out_after (j : nat) : list Z := match j with O => [] | S _ => [48; 10] end.

Definition Km_ok (Km : Model -> Prop) : Prop := forall mo mo', Km mo -> m_fds mo' = m_fds mo -> m_fs mo' = m_fs mo -> Km mo'.

Lemma SoA_fstable : forall Km so tr0, Km_ok Km -> fstable (SoA ps_so Km so tr0).
Proof.
intros Km so tr0 HKm s mo tr s' mo' (H1 & H2 & H3) Hso Hfd Hfs. split; [eapply HKm; eauto|]. split; [congruence| exact H3].
Qed.

Lemma zlength_zeros_out : forall j, zlength (zeros_out j) = 2 * Z.of_nat j.
Proof.
induction j as [|j IH]; [reflexivity|]. rewrite zeros_out_S, zlen_app, IH. unfold zlength. cbn [length]. lia.
Qed.

Lemma zeros_out_app : forall j, zeros_out j ++ [48; 10] = zeros_out (S j).
Proof.
induction j as [|j IH]; [reflexivity|]. rewrite zeros_out_S. rewrite <- app_assoc, IH. reflexivity.
Qed.

Lemma Zdecimal_0 : Zdecimal 0 ++ [10] = [48; 10].
Proof. reflexivity. Qed.

Lemma run_calls_E : forall Km d n j tr0, Km_ok Km -> zlength d < 2^61 -> (j + n <= 500)%nat ->
mspecE sel X (SoA ps_so Km (so_after j) (tr0 ++ evw 1 (out_after j))) (run_calls ops d n 0)
(fun rc => fun s mo tr => SoA ps_so Km (so_after (j + n)) (tr0 ++ evw 1 (out_after (j + n))) s mo tr /\ rc = 0).
Proof.
intros Km d n. induction n as [|n IH]; intros j tr0 HKm Hd Hj; cbn [run_calls].
- apply mspecE_ret_ops. intros s mo tr H. rewrite Nat.add_0_r. auto.
- apply (mspecE_bind_ops _ _ _ (fun rc' s mo tr => SoA ps_so Km (so_after j) (tr0 ++ evw 1 (out_after j)) s mo tr /\ rc' = 0)).
{ apply fuzz_one_E; [apply SoA_fstable; exact HKm| exact Hd]. }
intros rc'. apply mspecE_pure. intros ->. red_ops. rewrite Zdecimal_0. cbn [pieces_emit_of].
eapply mspecE_seq with (R := SoA ps_so Km (so_after (S j)) (tr0 ++ evw 1 (out_after (S j)))).
+ destruct j as [|j].
* eapply mspecE_conseq; [apply (stdout_emit_first ps_so set_so_ps sel X (fun _ _ => eq_refl) Km tr0)| |].
{ intros s mo tr H. cbn [so_after out_after evw map] in H. rewrite app_nil_r in H. exact H. }
intros a s mo tr H. exact H.
* eapply mspecE_conseq; [apply (stdout_emit_next ps_so set_so_ps sel X (fun _ _ => eq_refl) Km (zeros_out j) (tr0 ++ evw 1 [48; 10]))| |].
{ rewrite zlength_zeros_out. unfold STDOUT_BUFSIZ. lia. }
{ intros s mo tr H. exact H. }
intros a s mo tr H. cbv beta in H. rewrite zeros_out_app in H. exact H.
+ intros _. replace (j + S n)%nat with (S j + n)%nat by lia. apply IH; auto; lia.
Qed.

Lemma calls_pos : forall cfg, (1 <= Z.to_nat (Z.land cfg 3 + 1) <= 4)%nat.
Proof.
intros cfg. change 3 with (Z.ones 2). rewrite Z.land_ones by lia.
pose proof (Z.mod_pos_bound cfg (2^2) ltac:(lia)) as H. change (2^2) with 4 in *. lia.
Qed.

Theorem target_run_E : forall Km cfg payload tr0, Km_ok Km -> zlength payload < 2^61 ->
mspecE sel X (SoA ps_so Km stdout_init tr0) (X1rz.run cfg payload)
(fun rc s mo tr => SoA ps_so Km (so_after (Z.to_nat (Z.land cfg 3 + 1))) (tr0 ++ evw 1 [48; 10]) s mo tr /\ rc = 0).
Proof.
intros Km cfg payload tr0 HKm Hd. unfold X1rz.run, X1sb.target_run, X1rr.target_run.
pose proof (SoA_fstable Km stdout_init tr0 HKm) as HK0.
apply (mspecE_bind_ops _ _ _ (fun a s mo tr => SoA ps_so Km stdout_init tr0 s mo tr /\ a <> None)).
- destruct (zlength payload =? 0).
+ apply mspecE_ret_ops. intros s mo tr H. split; [exact H| discriminate].
+ eapply mspecE_bind_ops; [apply malloc_ops_E; [exact HK0| lia]|].
intros r. apply mspecE_pure. intros Hr. destruct r as [p|]; [|contradiction Hr; reflexivity].
apply mspecE_ret_ops. intros s mo tr H. split; [exact H| discriminate].
- intros [owned|]; [|apply mspecE_pure; intros []; reflexivity].
apply mspecE_pure. intros _.
destruct (calls_pos cfg) as [Hc1 Hc2]. destruct (Z.to_nat (Z.land cfg 3 + 1)) as [|n] eqn:En; [lia|].
apply (mspecE_bind_ops _ _ _ (fun rc s mo tr => SoA ps_so Km (so_after (S n)) (tr0 ++ evw 1 [48; 10]) s mo tr /\ rc = 0)).
+ eapply mspecE_conseq; [apply (run_calls_E Km payload (S n) 0 tr0 HKm Hd); lia| |].
* intros s mo tr H. cbn [so_after out_after evw map]. rewrite app_nil_r. exact H.
* intros rc s mo tr [H ->]. split; [exact H| reflexivity].
+ intros rc. apply mspecE_pure. intros ->.
apply (mspecE_bind_ops _ _ _ (fun _ => SoA ps_so Km (so_after (S n)) (tr0 ++ evw 1 [48; 10]))).
* apply free_ops_E. apply SoA_fstable. exact HKm.
* intros u. apply mspecE_ret_ops. intros s mo tr H. auto.
Qed.

End TargetE.
