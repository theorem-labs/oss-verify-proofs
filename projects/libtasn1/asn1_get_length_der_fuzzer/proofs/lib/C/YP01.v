(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Trevor Hansen, 2026-11: module names. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs Run.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YK15 YN02.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YP0j YP0g YP0h YP0r YP0c YP07 YP04 YP05 YP02.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition RUNS (data : list byte) (fs : Fs) : TSet := wr ch_stdout (concat (repeat line0 (calls data))) (ex 0 fs).
Definition POST (data : list byte) (fs : Fs) : TSet :=
if dlen data <? HDR_MIN then diag msg_short fs
else if dlen data <? HDR_MIN + config_len data then diag msg_overrun fs
else if payload_len data =? 0 then RUNS data fs
else t_alt2 (ex (if count_mode data then 0 else 2) fs) (RUNS data fs).
Definition CLOSED_loaded (data : list byte) (fs : Fs) : TSet :=
t_alt2 (diag msg_oom fs) (if MAX_INPUT <=? dlen data then diag msg_refused fs else POST data fs).
Definition CLOSED_dir (p : list byte) (fs : Fs) : TSet := t_alt2 (diag msg_oom fs) (diag (msg_read_error p) fs).
Definition CLOSED_args (argv : list (list byte)) (fs : Fs) : TSet :=
match argv with
| [_; p] =>
match classify_open p fs with
| OpenFails => diag (msg_cannot_open p) fs
| OpenDir => t_alt2 (diag (msg_cannot_open p) fs) (CLOSED_dir p fs)
| OpenFile data => t_alt2 (diag (msg_cannot_open p) fs) (CLOSED_loaded data fs)
end
| _ => diag (msg_usage (nth 0 argv [])) fs
end.
Definition CLOSED (inp : ProcInput) : TSet := CLOSED_args (in_argv inp) (in_fs inp).
Fixpoint RP (data : list byte) (fs : Fs) (fuel : nat) (cap : Z) : TSet :=
match fuel with
| O => diag msg_refused fs
| S f => if dlen data <? cap then POST data fs
else if MAX_INPUT <=? cap then diag msg_refused fs
else t_alt2 (diag msg_oom fs) (RP data fs f (2 * cap))
end.
Lemma RP_S data fs f cap :
RP data fs (S f) cap = if dlen data <? cap then POST data fs
else if MAX_INPUT <=? cap then diag msg_refused fs
else t_alt2 (diag msg_oom fs) (RP data fs f (2 * cap)).
Proof. reflexivity. Qed.
Lemma RP_closed data fs :
t_eq (t_alt2 (diag msg_oom fs) (RP data fs READ_FUEL CAP0)) (CLOSED_loaded data fs).
Proof.
unfold CLOSED_loaded, READ_FUEL, CAP0. cbn [RP].
change (2 * 65536) with 131072. change (2 * 131072) with 262144. change (2 * 262144) with 524288.
change (2 * 524288) with 1048576. change (2 * 1048576) with 2097152. change (2 * 2097152) with 4194304.
change (2 * 4194304) with 8388608. change (2 * 8388608) with 16777216. change (2 * 16777216) with 33554432.
change (2 * 33554432) with 67108864. unfold MAX_INPUT. cbn [Z.leb Z.compare Pos.compare Pos.compare_cont].
intros tr. unfold t_alt2.
destruct (dlen data <? 65536) eqn:?; [|destruct (dlen data <? 131072) eqn:?; [|destruct (dlen data <? 262144) eqn:?;
[|destruct (dlen data <? 524288) eqn:?; [|destruct (dlen data <? 1048576) eqn:?; [|destruct (dlen data <? 2097152) eqn:?;
[|destruct (dlen data <? 4194304) eqn:?; [|destruct (dlen data <? 8388608) eqn:?; [|destruct (dlen data <? 16777216) eqn:?;
[|destruct (dlen data <? 33554432) eqn:?; [|destruct (dlen data <? 67108864) eqn:?]]]]]]]]]];
destruct (67108864 <=? dlen data) eqn:?; bool_hyps; try lia; tauto.
Qed.
Lemma cleaves_In_cpath {A} (t : itree astate A) l a : cleaves t = Some l -> In a l -> exists tr, cpath t tr a.
Proof.
revert l a. induction t as [a' | q s k IH | f]; intros l a Hc Hin; cbn in Hc.
- injection Hc as <-. destruct Hin as [<- | []]. exists []. reflexivity.
- destruct q; cbn [cleaves fallible] in Hc; try discriminate Hc;
first [ destruct (cleaves (k 0)) as [l0|] eqn:E0; [|discriminate Hc];
destruct (cleaves (k 1)) as [l1|] eqn:E1; [|discriminate Hc]; injection Hc as <-;
apply in_app_iff in Hin as [Hin | Hin];
[ destruct (IH 0 l0 a E0 Hin) as [tr Hp]; eexists ((_, 0) :: tr); cbn; split; [reflexivity|]; split; [left; reflexivity | exact Hp]
| destruct (IH 1 l1 a E1 Hin) as [tr Hp]; eexists ((_, 1) :: tr); cbn; split; [reflexivity|]; split; [right; reflexivity | exact Hp] ]
| destruct (IH 1 l a Hc Hin) as [tr Hp]; eexists ((_, 1) :: tr); cbn; split; [reflexivity|]; split; [reflexivity | exact Hp] ].
- injection Hc as <-. destruct Hin.
Qed.
Fixpoint nones (l : list (option sptr * astate)) : list astate :=
match l with [] => [] | (None, s) :: r => s :: nones r | _ :: r => nones r end.
Fixpoint somes (l : list (option sptr * astate)) : list (sptr * astate) :=
match l with [] => [] | (Some p, s) :: r => (p, s) :: somes r | _ :: r => somes r end.
Lemma In_nones l s : In s (nones l) <-> In (None, s) l.
Proof.
induction l as [|[[p|] s'] l IH]; cbn.
- tauto.
- rewrite IH. split; [intros H; right; exact H | intros [H|H]; [discriminate H | exact H]].
- rewrite IH. split; [intros [<-|H]; [left; reflexivity | right; exact H] | intros [H|H]; [injection H as <-; left; reflexivity | right; exact H]].
Qed.
Lemma In_somes l p s : In (p, s) (somes l) <-> In (Some p, s) l.
Proof.
induction l as [|[[p'|] s'] l IH]; cbn.
- tauto.
- rewrite IH. split; [intros [H|H]; [injection H as <- <-; left; reflexivity | right; exact H] | intros [H|H]; [injection H as <- <-; left; reflexivity | right; exact H]].
- rewrite IH. split; [intros H; right; exact H | intros [H|H]; [discriminate H | exact H]].
Qed.
Lemma step_malloc {R} (n : Z) (F : option sptr -> M R) (s : astate) l (K : R * astate -> TSet) (A B : TSet) :
cleaves (malloc n s) = Some l -> nones l <> [] -> somes l <> [] ->
(forall s', In s' (nones l) -> (exists tr, cpath (malloc n s) tr (None, s')) -> t_eq (tset (F None s') K) A) ->
(forall p s', In (p, s') (somes l) -> (exists tr, cpath (malloc n s) tr (Some p, s')) -> t_eq (tset (F (Some p) s') K) B) ->
t_eq (tset (bind (malloc n) F s) K) (t_alt2 A B).
Proof.
intros Hc HN HS HA HB. rewrite tset_mbind.
eapply t_eq_trans; [apply (tset_cleaves _ _ l Hc)|].
intros tr. rewrite tsum_In. unfold t_alt2. split.
- intros (T & Hin & HT). apply in_map_iff in Hin as ([[p|] s'] & <- & Hin).
+ right. apply (HB p s'); [apply In_somes, Hin | eapply cleaves_In_cpath; eauto | exact HT].
+ left. apply (HA s'); [apply In_nones, Hin | eapply cleaves_In_cpath; eauto | exact HT].
- intros [HT | HT].
+ assert (Hs' : exists s', In s' (nones l)) by (destruct (nones l) as [|s' r]; [congruence | exists s'; left; reflexivity]).
destruct Hs' as [s' Hs']. pose proof (proj1 (In_nones l s') Hs') as Hin.
exists (tset (F None s') K). split; [apply in_map_iff; exists (None, s'); auto|].
apply (HA s'); [exact Hs' | eapply cleaves_In_cpath; eauto | exact HT].
+ assert (Hs' : exists p s', In (p, s') (somes l)) by (destruct (somes l) as [|[p s'] r]; [congruence | exists p, s'; left; reflexivity]).
destruct Hs' as (p & s' & Hs'). pose proof (proj1 (In_somes l p s') Hs') as Hin.
exists (tset (F (Some p) s') K). split; [apply in_map_iff; exists (Some p, s'); auto|].
apply (HB p s'); [exact Hs' | eapply cleaves_In_cpath; eauto | exact HT].
Qed.
Lemma step_free {R} (b : sptr) (F : unit -> M R) (s s' : astate) (K : R * astate -> TSet) (B : TSet) :
cleaves (free (Some b) s) = Some [(tt, s')] ->
((exists tr, cpath (free (Some b) s) tr (tt, s')) -> t_eq (tset (F tt s') K) B) ->
t_eq (tset (bind (free (Some b)) F s) K) B.
Proof.
intros Hc HB. rewrite tset_mbind. eapply t_eq_trans; [apply (tset_cleaves _ _ _ Hc)|]. cbn [map tsum fst snd].
intros tr. unfold t_alt2, t_bot. split; [intros [H|[]] | intros H; left]; apply HB; try exact H; eapply cleaves_In_cpath; eauto; left; reflexivity.
Qed.
Lemma step_payload {R} N (n : Z) (F : option sptr -> M R) (s : astate) (K : R * astate -> TSet) (A B : TSet) :
WF s -> 25 <= N -> HNb N s = true -> 0 < n < MAX_INPUT ->
(n < MMAP_THRESHOLD -> size_to_class n < N /\ (size_to_class n < 32 -> size_to_class n + 1 < N)) ->
(forall s', t_eq (tset (F None s') K) A) -> (forall p s', t_eq (tset (F (Some p) s') K) B) ->
t_eq (tset (bind (malloc n) F s) K) (t_alt2 A B).
Proof.
intros HW HN Hb Hn Hsc HA HB. rewrite tset_mbind.
apply (tset_malloc_nonesome N); try assumption; try lia.
- apply HNb_HN; [lia | exact Hb].
- unfold size_overflows, MAX_INPUT in *. apply Z.leb_gt. lia.
Qed.
End d.
Ltac st_cases Hin :=
vm_compute in Hin; repeat (destruct Hin as [<- | Hin]); try contradiction.
Ltac pst_cases Hin :=
vm_compute in Hin; repeat (let E := fresh "E" in destruct Hin as [E | Hin]; [injection E as <- <- |]); try contradiction.
Ltac norm_caps :=
repeat match goal with |- context [2 * ?c] =>
lazymatch isZcst c with true => let v := eval vm_compute in (2 * c) in change (2 * c) with v end end.
Ltac decide_closed c := let v := eval vm_compute in c in change c with v; cbv beta iota.
Ltac leaf_refl := cbv beta iota; apply t_eq_refl.
Ltac payload_cases HW :=
lazymatch goal with |- t_eq (tset (bind (malloc (payload_len ?data)) _ ?s) _) _ =>
first
[
eapply (step_payload 48); [ exact HW | lia | vm_compute; reflexivity
| unfold payload_len, HDR_MIN, config_len, dlen, cfg_word, MAX_INPUT in *; bool_hyps; lia
| let H := fresh in intros H; pose proof (size_to_class_lt48 (payload_len data)); unfold payload_len, HDR_MIN, MAX_INPUT in *; bool_hyps; lia
| intros; leaf_refl | intros; leaf_refl ]
|
let Ec := fresh "Ec" in
destruct (payload_len data <=? 65516) eqn:Ec;
[ eapply (step_payload 44); [ exact HW | lia | vm_compute; reflexivity
| unfold payload_len, HDR_MIN, config_len, dlen, cfg_word, MAX_INPUT in *; bool_hyps; lia
| let H := fresh in intros H; pose proof (size_to_class_lt44 (payload_len data)); unfold payload_len, HDR_MIN, MAX_INPUT in *; bool_hyps; lia
| intros; leaf_refl | intros; leaf_refl ]
| let E := fresh "E" in
assert (E : payload_len data = 65517 \/ payload_len data = 65518 \/ payload_len data = 65519 \/ payload_len data = 65520
\/ payload_len data = 65521 \/ payload_len data = 65522 \/ payload_len data = 65523 \/ payload_len data = 65524
\/ payload_len data = 65525 \/ payload_len data = 65526 \/ payload_len data = 65527 \/ payload_len data = 65528
\/ payload_len data = 65529)
by (unfold payload_len, HDR_MIN, config_len, cfg_word in *; bool_hyps;
pose proof (Z.mod_pos_bound (dbyte data 0 + 256 * dbyte data 1) 32768 ltac:(lia)); lia);
repeat match goal with
| E : _ \/ _ |- _ => destruct E as [E | E]
end;
match goal with E : payload_len data = _ |- _ => rewrite E end;
(eapply step_malloc; [ solve_cleaves | vm_compute; discriminate | vm_compute; discriminate
| intros; leaf_refl | intros; leaf_refl ]) ] ]
end.
Ltac rwalk HW :=
norm_caps;
lazymatch goal with
| |- t_eq (tset (bind (read_phase (S _) _ _ _) _ _) _) _ => rewrite read_phase_S, RP_S; rwalk HW
| |- t_eq (tset (bind (read_phase O _ _ _) _ _) _) _ => rewrite read_phase_O; cbn [RP]; rwalk HW
| |- t_eq (tset (bind (read_phase ?f _ _ _) _ _) _) _ => (let v := eval cbv in f in change f with v); rwalk HW
| |- t_eq (tset (bind (ret _) _ _) _) _ => rewrite bind_ret_l; cbv beta iota; rwalk HW
| |- t_eq (tset (bind (bind _ _) _ _) _) _ => rewrite bind_assoc; rwalk HW
| |- t_eq (tset (bind (if _ then _ else _) _ _) _) _ => rewrite bind_if; rwalk HW
| |- t_eq (tset ((if ?c then _ else _) _) _) _ => unfold POST; jif c; rwalk HW
| |- t_eq (tset (if ?c then _ else _) _) _ => unfold POST; jif c; rwalk HW
| |- t_eq (tset (ret _ _) _) _ => leaf_refl
| |- t_eq (tset (IRet _) _) _ => leaf_refl
| |- t_eq (tset (bind (malloc (payload_len _)) _ _) _) _ => payload_cases HW
| |- t_eq (tset (bind (malloc ?n) _ ?s) _) (t_alt2 _ _) =>
eapply step_malloc;
[ solve_cleaves | vm_compute; discriminate | vm_compute; discriminate
| let s' := fresh "s" in let Hin := fresh "Hin" in let tr := fresh "tr" in let Hp := fresh "Hp" in
intros s' Hin [tr Hp]; clear Hp; st_cases Hin; rwalk HW
| let b := fresh "b" in let s' := fresh "s" in let Hin := fresh "Hin" in let tr := fresh "tr" in let Hp := fresh "Hp" in
let HW' := fresh "HW" in
intros b s' Hin [tr Hp]; pst_cases Hin;
(apply (malloc_leaf_wf _ _ _ _ _ HW) in Hp; [|lia]); rwalk Hp ]
| |- t_eq (tset (bind (free (Some ?b)) _ ?s) _) _ =>
eapply step_free;
[ solve_cleaves
| let tr := fresh "tr" in let Hp := fresh "Hp" in let HW' := fresh "HW" in
intros [tr Hp];
(apply (free_leaf_wf' _ _ _ _ _ HW) in Hp; [|vm_compute; reflexivity]); rwalk Hp ]
| |- ?g => idtac "rwalk: stuck"
end.
Section e. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Theorem loaded_closed_eq data fs : t_eq (SPEC_loaded data fs) (CLOSED_loaded data fs).
Proof.
eapply t_eq_trans; [|apply RP_closed].
unfold SPEC_loaded, driver_tree, driver_m, READ_FUEL, CAP0.
pose proof wf_init as HW0.
rwalk HW0.
Qed.
Theorem dir_closed_eq p fs : t_eq (SPEC_dir p fs) (CLOSED_dir p fs).
Proof.
unfold SPEC_dir, dir_m, CLOSED_dir, CAP0.
eapply step_malloc; [ solve_cleaves | vm_compute; discriminate | vm_compute; discriminate
| intros; leaf_refl | intros; leaf_refl ].
Qed.
Theorem spec_closed_eq inp : t_eq (SPEC inp) (CLOSED inp).
Proof.
unfold SPEC, CLOSED, SPEC_args, CLOSED_args.
destruct (in_argv inp) as [|a0 [|p [|x r]]]; [apply t_eq_refl | apply t_eq_refl | | apply t_eq_refl].
destruct (classify_open p (in_fs inp)).
- apply t_eq_refl.
- apply t_alt2_congr; [apply t_eq_refl | apply dir_closed_eq].
- apply t_alt2_congr; [apply t_eq_refl | apply loaded_closed_eq].
Qed.
End e.
