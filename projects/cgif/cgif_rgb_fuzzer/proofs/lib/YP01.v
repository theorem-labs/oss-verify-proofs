(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (free's munmap may be refused, so the driver's tree equality is split into loaded_sub, every leaf lands in the closed form, and loaded_sup, every closed-form trace is reached along one path; the walk tactic swalk fails on a stuck goal). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK15 YN02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0h YP0r YP0c YP07 YP04 YP05 YP02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
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
(* 08b1429: free asks KMunmap, which may be refused, so a free of a mapped chunk has two leaves and the read
   loop's leaf states double each round. The equality is therefore split: every leaf of the tree lands in the
   closed form (a generic leaves argument, no state enumeration), and every closed-form trace is reached along
   one chosen path (one leaf per free). *)
Definition tsub (A B : TSet) : Prop := forall tr, A tr -> B tr.
Lemma sub_alt2 (A B C : TSet) : tsub A C -> tsub B C -> tsub (t_alt2 A B) C.
Proof. intros HA HB tr [H|H]; [apply HA | apply HB]; exact H. Qed.
Lemma sub_teq (A B : TSet) : t_eq B A -> tsub A B.
Proof. intros H tr HA. apply (proj2 (H tr)). exact HA. Qed.
Lemma sub_bind_leaf {A R} {m : M A} {F : A -> M R} {s : astate} {l : list (A * astate)} {a : A} {s' : astate}
{K : R * astate -> TSet} {B : TSet} :
cleaves (m s) = Some l -> In (a, s') l ->
((exists tr, cpath (m s) tr (a, s')) -> tsub B (tset (F a s') K)) ->
tsub B (tset (bind m F s) K).
Proof.
intros Hc Hin HB tr HX. rewrite tset_mbind. apply (proj2 (tset_cleaves _ _ l Hc tr)).
rewrite tsum_In. exists (tset (F a s') K). split.
- apply in_map_iff. exists (a, s'). split; [reflexivity | exact Hin].
- apply HB; [eapply cleaves_In_cpath; eauto | exact HX].
Qed.
Lemma leaves_T {A} (t : itree astate A) : leaves (fun _ => True) t.
Proof. induction t as [a | q s k IH | f]; cbn; [exact I | intros z _; apply IH | exact I]. Qed.
Lemma leaves_mbind {A B} (P : A * astate -> Prop) (Q : B * astate -> Prop) (m : M A) (f : A -> M B) s :
leaves P (m s) -> (forall a s', P (a, s') -> leaves Q (f a s')) -> leaves Q (bind m f s).
Proof. intros H1 H2. unfold bind. eapply leaves_ibind; [exact H1|]. intros [a s'] Ha. exact (H2 a s' Ha). Qed.
Lemma tset_leaves_sub {A} (K : A -> TSet) (B : TSet) : forall t : itree astate A,
leaves (fun a => forall tr, K a tr -> B tr) t -> forall tr, tset t K tr -> B tr.
Proof.
induction t as [a | q s k IH | f]; intros Hl tr H; cbn in Hl, H.
- exact (Hl tr H).
- destruct (fallible q) eqn:Fq.
  + destruct H as [H|H]; [apply (IH 0) | apply (IH 1)]; try exact H; apply Hl; apply answer_ok_kernel; exact Fq.
  + apply (IH (canon q)); [apply Hl; apply canon_answer_ok | exact H].
- destruct H.
Qed.
(* what the read loop's result says about the input length; no state is involved *)
Definition RL (L : Z) (r : rd_result * astate) : Prop :=
match fst r with RdLoaded _ _ => L < MAX_INPUT | RdRefused => MAX_INPUT <= L | RdOOM => True end.
Lemma read_phase_RL : forall f L cap buf s j, 0 <= j -> MAX_INPUT = cap * 2 ^ j -> j < Z.of_nat f -> 0 < cap ->
leaves (RL L) (read_phase f L cap buf s).
Proof.
induction f as [|f IH]; intros L cap buf s j Hj HM Hf Hc; [lia|].
cbn [read_phase]. pose proof (Z.pow_pos_nonneg 2 j ltac:(lia) Hj) as Hp.
destruct (L <? cap) eqn:EL.
{ cbn [ret leaves]. unfold RL. cbn [fst]. apply Z.ltb_lt in EL. nia. }
destruct (MAX_INPUT <=? cap) eqn:EM.
{ cbn [ret leaves]. unfold RL. cbn [fst]. apply Z.ltb_ge in EL. apply Z.leb_le in EM. lia. }
apply Z.leb_gt in EM.
assert (Hj1 : 1 <= j) by (destruct (Z.eq_dec j 0) as [->|]; [rewrite Z.pow_0_r in HM; lia | lia]).
cbv beta iota. apply (leaves_mbind (fun _ => True)); [apply leaves_T|]. intros [nb|] s1 _; cbv beta iota.
- apply (leaves_mbind (fun _ => True)); [apply leaves_T|]. intros [] s2 _.
  apply (IH L (2 * cap) nb s2 (j - 1)); try lia.
  rewrite HM. replace j with (Z.succ (j - 1)) at 1 by lia. rewrite Z.pow_succ_r by lia. ring.
- cbn [ret leaves]. unfold RL. cbn [fst]. exact I.
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
Ltac pick_in := solve [repeat (first [left; reflexivity | right])].
(* a free that unmapped has two leaves (refused first, unmapped second); either reaches the closed form *)
Ltac pick_last := first [right; left; reflexivity | left; reflexivity].
Ltac sleaf := cbv beta iota; let tr := fresh "tr" in let H := fresh "H" in intros tr H; exact H.
Ltac swalk HW :=
norm_caps;
lazymatch goal with
| |- tsub _ (tset (bind (read_phase (S _) _ _ _) _ _) _) => rewrite read_phase_S, RP_S; swalk HW
| |- tsub _ (tset (bind (read_phase O _ _ _) _ _) _) => rewrite read_phase_O; cbn [RP]; swalk HW
| |- tsub _ (tset (bind (read_phase ?f _ _ _) _ _) _) => (let v := eval cbv in f in change f with v); swalk HW
| |- tsub _ (tset (bind (ret _) _ _) _) => rewrite bind_ret_l; cbv beta iota; swalk HW
| |- tsub _ (tset (bind (bind _ _) _ _) _) => rewrite bind_assoc; swalk HW
| |- tsub _ (tset (bind (if _ then _ else _) _ _) _) => rewrite bind_if; swalk HW
| |- tsub _ (tset ((if ?c then _ else _) _) _) => unfold POST; jif c; swalk HW
| |- tsub _ (tset (if ?c then _ else _) _) => unfold POST; jif c; swalk HW
| |- tsub _ (tset (ret _ _) _) => sleaf
| |- tsub _ (tset (IRet _) _) => sleaf
| |- tsub _ (tset (bind (malloc (payload_len _)) _ _) _) => apply sub_teq; payload_cases HW
| |- tsub (t_alt2 _ _) (tset (bind (malloc ?n) _ ?s) _) =>
apply sub_alt2;
[ eapply (sub_bind_leaf (a := None));
  [ solve_cleaves | pick_in
  | let tr := fresh "tr" in let Hp := fresh "Hp" in intros [tr Hp]; clear Hp; cbv beta iota; swalk HW ]
| eapply (sub_bind_leaf (a := Some _));
  [ solve_cleaves | pick_in
  | let tr := fresh "tr" in let Hp := fresh "Hp" in
    intros [tr Hp]; (apply (malloc_leaf_wf _ _ _ _ _ HW) in Hp; [|lia]); cbv beta iota; swalk Hp ] ]
| |- tsub _ (tset (bind (free (Some ?b)) _ ?s) _) =>
eapply (sub_bind_leaf (a := tt));
[ solve_cleaves | pick_last
| let tr := fresh "tr" in let Hp := fresh "Hp" in
  intros [tr Hp]; (apply (free_leaf_wf' _ _ _ _ _ HW) in Hp; [|vm_compute; reflexivity]); cbv beta iota; swalk Hp ]
| |- ?g => fail "swalk: stuck"
end.
Section e. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
(* every leaf lands in the closed form: RL carries the length facts; no allocator state is enumerated *)
Lemma loaded_sub data fs : tsub (SPEC_loaded data fs) (CLOSED_loaded data fs).
Proof.
unfold SPEC_loaded, driver_tree, driver_m, tsub. apply tset_leaves_sub.
apply (leaves_mbind (fun _ => True)); [apply leaves_T|]. intros [b0|] s1 _; cbv beta iota.
2: { cbn [ret leaves leaf_shape fst]. intros tr H. left. exact H. }
apply (leaves_mbind (RL (dlen data))).
{ apply (read_phase_RL _ _ _ _ _ 10); unfold MAX_INPUT, CAP0, READ_FUEL; first [lia | reflexivity]. }
intros r s2 HR. destruct r as [| |buf cap]; unfold RL in HR; cbn [fst] in HR; cbv beta iota.
- cbn [ret leaves leaf_shape fst]. intros tr H. left. exact H.
- cbn [ret leaves leaf_shape fst]. intros tr H. unfold CLOSED_loaded, t_alt2. right.
  rewrite (proj2 (Z.leb_le _ _) HR). exact H.
- apply (leaves_mono (fun a => forall tr, leaf_shape data fs a tr -> POST data fs tr)).
  { intros a Ha tr H. unfold CLOSED_loaded, t_alt2. right. rewrite (proj2 (Z.leb_gt _ _) HR). exact (Ha tr H). }
  unfold POST.
  destruct (dlen data <? HDR_MIN) eqn:E1; [cbn [ret leaves leaf_shape fst]; intros tr H; exact H|].
  destruct (dlen data <? HDR_MIN + config_len data) eqn:E2; [cbn [ret leaves leaf_shape fst]; intros tr H; exact H|].
  destruct (payload_len data =? 0) eqn:E3; [cbn [ret leaves leaf_shape fst]; intros tr H; exact H|].
  cbv beta iota. apply (leaves_mbind (fun _ => True)); [apply leaves_T|].
  intros [q|] s3 _; cbn [ret leaves leaf_shape fst]; intros tr H; unfold t_alt2; [right | left]; exact H.
Qed.
(* every closed-form trace is reached along one path: at each free the walk takes one leaf *)
Lemma loaded_sup data fs : tsub (t_alt2 (diag msg_oom fs) (RP data fs READ_FUEL CAP0)) (SPEC_loaded data fs).
Proof.
unfold SPEC_loaded, driver_tree, driver_m, READ_FUEL, CAP0.
pose proof wf_init as HW0.
swalk HW0.
Qed.
Theorem loaded_closed_eq data fs : t_eq (SPEC_loaded data fs) (CLOSED_loaded data fs).
Proof.
intros tr. split; [exact (loaded_sub data fs tr) | intros H; exact (loaded_sup data fs tr (proj2 (RP_closed data fs tr) H))].
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
