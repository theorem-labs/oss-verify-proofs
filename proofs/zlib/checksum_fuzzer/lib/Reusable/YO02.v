(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia FunctionalExtensionality.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK15 YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i YO0f YO0g YO0x YO0d YO0e YO05.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Fixpoint cleaves {A : Type} (t : itree astate A) : option (list A) :=
match t with
| IRet a => Some [a]
| IFail _ => Some []
| IAsk (KJunk _) _ _ => None
| IAsk q _ k => if fallible q then
match cleaves (k 0), cleaves (k 1) with
| Some l0, Some l1 => Some (l0 ++ l1)
| _, _ => None
end
else cleaves (k 1)
end.
Lemma cleaves_cpath {A} : forall (t : itree astate A) l tr a, cleaves t = Some l -> cpath t tr a -> In a l.
Proof.
induction t as [a' | q s k IH | f]; intros l tr a Hc Hp; cbn in *.
- injection Hc as <-. destruct tr; [left; exact Hp | destruct Hp].
- destruct tr as [|[q' z] tr']; [destruct Hp|]. destruct Hp as (-> & Hz & Hp).
unfold canswer in Hz.
destruct q; cbn [fallible] in *; try discriminate;
first [ destruct (cleaves (k 0)) as [l0|] eqn:E0; [|discriminate];
destruct (cleaves (k 1)) as [l1|] eqn:E1; [|discriminate]; injection Hc as <-;
apply in_app_iff; destruct Hz as [-> | ->]; [left; eapply IH; eauto | right; eapply IH; eauto]
| subst z; eapply IH; eauto ].
- destruct tr; [|destruct Hp]. injection Hc as <-. destruct Hp.
Qed.
Lemma gtree_mbind_leaves {A B} (m : M A) (f : A -> M B) s l :
gtree mgrant (m s) -> cleaves (m s) = Some l ->
(forall a s', In (a, s') l -> gtree mgrant (f a s')) ->
gtree mgrant (bind m f s).
Proof. intros Hg Hc Hf. apply gtree_mbind; [exact Hg|]. intros tr a s' Hp. apply Hf. eapply cleaves_cpath; eauto. Qed.
Lemma jinv_mbind_leaves {A B} (K : B * astate -> TSet) (m : M A) (f : A -> M B) s l :
jfree (m s) -> cleaves (m s) = Some l ->
(forall a s', In (a, s') l -> jinv K (f a s')) ->
jinv K (bind m f s).
Proof. intros Hj Hc Hf. apply jinv_mbind; [apply jfree_jinv; exact Hj|]. intros tr a s' Hp. apply Hf. eapply cleaves_cpath; eauto. Qed.
Lemma malloc_leaf_wf s n tr p s' : WF s -> 0 <= n -> cpath (malloc n s) tr (p, s') -> WF s'.
Proof. intros HW Hn Hp. eapply malloc_wf; [exact HW | exact Hn | apply cpath_yields; exact Hp]. Qed.
Lemma free_leaf_wf s b n tr s' : WF s -> In (b, n) (user_blocks s) -> cpath (free (Some b) s) tr (tt, s') -> WF s'.
Proof. intros HW Hin Hp. eapply free_wf; [exact HW | exact Hin | apply cpath_yields; exact Hp]. Qed.
Lemma jinv_malloc_nonesome (K : option sptr * astate -> TSet) s n (T0 T1 : TSet) :
WF s -> 0 <= n ->
(forall s', t_eq (K (None, s')) T0) -> (forall p s', t_eq (K (Some p, s')) T1) ->
jinv K (malloc n s).
Proof.
intros HW Hn H0 H1.
eapply tsim_jinv; [apply (malloc_tsim s s n HW HW (shape_eq_refl s) Hn)|].
intros [p s1] [p' s2] [_ R]; cbn [fst snd] in R |- *.
destruct p, p'; try contradiction.
- eapply t_eq_trans; [apply H1 | apply t_eq_sym; apply H1].
- eapply t_eq_trans; [apply H0 | apply t_eq_sym; apply H0].
Qed.
Lemma bind_assoc {A B C} (m : M A) (f : A -> M B) (g : B -> M C) s :
bind (bind m f) g s = bind m (fun a => bind (f a) g) s.
Proof.
unfold bind. generalize (m s). intros t. induction t as [[a s']| q s0 k IH | e]; cbn; [reflexivity| |reflexivity].
f_equal. apply functional_extensionality. intros z. apply IH.
Qed.
Lemma bind_ret_l {A B} (a : A) (f : A -> M B) s : bind (ret a) f s = f a s.
Proof. reflexivity. Qed.
Lemma bind_if {A B} (c : bool) (m1 m2 : M A) (f : A -> M B) s :
bind (if c then m1 else m2) f s = if c then bind m1 f s else bind m2 f s.
Proof. destruct c; reflexivity. Qed.
Lemma jinv_mbind_leaves' {A B} (K : B * astate -> TSet) (m : M A) (f : A -> M B) s l :
jfree (m s) -> cleaves (m s) = Some l ->
(forall a s', In (a, s') l -> (exists tr, cpath (m s) tr (a, s')) -> jinv K (f a s')) ->
jinv K (bind m f s).
Proof. intros Hj Hc Hf. apply jinv_mbind; [apply jfree_jinv; exact Hj|]. intros tr a s' Hp. apply Hf; [eapply cleaves_cpath; eauto | exists tr; exact Hp]. Qed.
Lemma gtree_mbind_leaves' {A B} (m : M A) (f : A -> M B) s l :
gtree mgrant (m s) -> cleaves (m s) = Some l ->
(forall a s', In (a, s') l -> (exists tr, cpath (m s) tr (a, s')) -> gtree mgrant (f a s')) ->
gtree mgrant (bind m f s).
Proof. intros Hg Hc Hf. apply gtree_mbind; [exact Hg|]. intros tr a s' Hp. apply Hf; [eapply cleaves_cpath; eauto | exists tr; exact Hp]. Qed.
End d.
Ltac solve_cleaves :=
lazymatch goal with |- cleaves ?t = Some ?l =>
let v := eval vm_compute in (cleaves t) in
lazymatch v with Some ?l' => unify l l' end; vm_compute; reflexivity end.
Ltac solve_In_blocks := vm_compute; repeat (first [left; reflexivity | right]).
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma free_leaf_wf' s b tr (u : unit) s' :
WF s -> existsb (fun bn => sptr_eqb (fst bn) b) (user_blocks s) = true ->
cpath (free (Some b) s) tr (u, s') -> WF s'.
Proof.
intros HW Hex Hp. destruct u. apply existsb_exists in Hex as ([b' n] & Hin & Hb). cbn in Hb. apply sptr_eqb_eq in Hb. subst b'.
eapply free_leaf_wf; eauto.
Qed.
Lemma if_app {A B} (c : bool) (f g : A -> B) (x : A) : (if c then f else g) x = if c then f x else g x.
Proof. destruct c; reflexivity. Qed.
Lemma read_phase_S f L cap buf :
read_phase (S f) L cap buf =
if L <? cap then ret (RdLoaded buf cap)
else if MAX_INPUT <=? cap then ret RdRefused
else bind (malloc (2 * cap)) (fun p => match p with
| None => ret RdOOM
| Some nb => bind (free (Some buf)) (fun _ => read_phase f L (2 * cap) nb)
end).
Proof. reflexivity. Qed.
Lemma read_phase_O L cap buf : read_phase O L cap buf = ret RdRefused.
Proof. reflexivity. Qed.
End h.
Ltac pair_subst Hin :=
let Ha := fresh "Ha" in
pose proof (f_equal fst Hin) as Ha; apply (f_equal snd) in Hin; cbn [fst snd] in Ha, Hin; subst.
Ltac in_cases Hin :=
repeat (destruct Hin as [Hin | Hin]; [pair_subst Hin | ]); [ .. | destruct Hin].
Ltac jif c :=
lazymatch c with
| context [dlen _] => destruct c eqn:?
| context [payload_len _] => destruct c eqn:?
| context [config_len _] => destruct c eqn:?
| _ => let v := eval vm_compute in c in
lazymatch v with true => change c with true | false => change c with false end; cbv beta iota
end.
Ltac jstep :=
lazymatch goal with
| |- jinv _ (IRet _) => exact I
| |- jinv _ (ret _ _) => exact I
| |- jinv _ (bind (ret _) _ _) => rewrite bind_ret_l; cbv beta iota
| |- jinv _ (bind (bind _ _) _ _) => rewrite bind_assoc
| |- jinv _ (bind (if ?c then _ else _) _ _) => rewrite bind_if
| |- jinv _ ((if ?c then _ else _) _) => jif c
| |- jinv _ ((match ?x with _ => _ end) _) => destruct x eqn:?
| |- jinv _ (if ?c then _ else _) => jif c
| |- jinv _ (bind (read_phase (S _) _ _ _) _ _) => rewrite read_phase_S
| |- jinv _ (bind (read_phase O _ _ _) _ _) => rewrite read_phase_O
| |- jinv _ (bind (read_phase ?f _ _ _) _ _) => let v := eval cbv in f in change f with v
| |- jinv _ (bind (malloc (payload_len _)) _ _) => idtac
| |- jinv _ (bind (malloc ?n) _ ?s) =>
eapply jinv_mbind_leaves';
[ vm_compute; repeat split
| solve_cleaves
| let a := fresh "a" in let s' := fresh "s" in let Hin := fresh "Hin" in let tr := fresh "tr" in let Hp := fresh "Hp" in
intros a s' Hin [tr Hp];
apply malloc_leaf_wf in Hp; [ | assumption | cbv; intro; discriminate ];
repeat match goal with H : WF s |- _ => clear H end;
in_cases Hin; cbv beta iota ]
| |- jinv _ (bind (free (Some ?b)) _ ?s) =>
eapply jinv_mbind_leaves';
[ vm_compute; repeat split
| solve_cleaves
| let a := fresh "a" in let s' := fresh "s" in let Hin := fresh "Hin" in let tr := fresh "tr" in let Hp := fresh "Hp" in
intros a s' Hin [tr Hp];
apply free_leaf_wf' in Hp; [ | assumption | vm_compute; reflexivity ];
repeat match goal with H : WF s |- _ => clear H end;
in_cases Hin; cbv beta iota ]
end.
Ltac jwalk := repeat (progress jstep).
Ltac bool_hyps :=
repeat match goal with
| H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
| H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
| H : (_ <=? _) = true |- _ => apply Z.leb_le in H
| H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
| H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
| H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
end.
