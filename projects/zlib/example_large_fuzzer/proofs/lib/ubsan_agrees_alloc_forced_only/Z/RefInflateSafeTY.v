(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ModelRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Strategy 100 [inflate_fast inflate_table it_step it_loop it_fill it_sort NEEDBITS_k DECODE_k codelens_while lenlens_while1 lenlens_while2].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma iterZ_ind2 : forall {A B} (P : A -> Prop) (Q : B -> Prop) (step : A -> A + B) (dflt : A -> B),
  (forall a, P a -> match step a with inl a' => P a' | inr b => Q b end) ->
  (forall a, P a -> Q (dflt a)) ->
  forall n a, P a -> Q (iterZ n step dflt a).
Proof.
  intros A B P Q step dflt Hs Hd n a Ha. rewrite iterZ_nat.
  revert a Ha. generalize (Z.to_nat n) as k. induction k as [|k IH]; intros a Ha; cbn [iterK_nat].
  - exact (Hd a Ha).
  - pose proof (Hs a Ha) as H. destruct (step a) as [a'|b]; [exact (IH a' H) | exact H].
Qed.

Lemma loopZ_ind : forall {A} (P : A -> Prop) (step : A -> bool * A),
  (forall a, P a -> P (snd (step a))) ->
  forall n a, P a -> P (loopZ n step a).
Proof.
  intros A P step Hs n a Ha. unfold loopZ.
  apply (iterZ_ind2 P P); [|intros a0 H0; exact H0|exact Ha].
  intros a0 H0. pose proof (Hs a0 H0) as H1. destruct (step a0) as [c a1]. cbn [snd] in H1. destruct c; exact H1.
Qed.

Lemma forZ_ind : forall {A} (P : A -> Prop) lo hi (body : Z -> A -> A),
  (forall i a, P a -> P (body i a)) -> forall a, P a -> P (forZ lo hi body a).
Proof.
  intros A P lo hi body Hb a Ha. unfold forZ.
  apply (loopZ_ind (fun ia : Z * A => P (snd ia))); [|cbn [snd]; exact Ha].
  intros [i x] Hx. cbn [snd] in Hx. destruct (i <? hi); cbn [snd]; [apply Hb; exact Hx | exact Hx].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ty16 (a : arr) : Prop := forall i, 0 <= arr_get a i < 2 ^ 16.
Definition ty32 (a : arr) : Prop := forall i, 0 <= arr_get a i < 2 ^ 32.

Lemma ty16_set : forall a i v, ty16 a -> 0 <= v < 2 ^ 16 -> ty16 (arr_set a i v).
Proof. intros a i v H Hv j. rewrite arr_get_set. destruct (_ && _); [exact Hv | apply H]. Qed.
Lemma ty32_set : forall a i v, ty32 a -> 0 <= v < 2 ^ 32 -> ty32 (arr_set a i v).
Proof. intros a i v H Hv j. rewrite arr_get_set. destruct (_ && _); [exact Hv | apply H]. Qed.
Lemma wrap16_ty : forall z, 0 <= wrap16 z < 2 ^ 16.
Proof. intros z. pose proof (wrap16_range z). change (2 ^ 16) with 65536 in *. lia. Qed.
Lemma code_pack_ty : forall op bits val, 0 <= code_pack op bits val < 2 ^ 32.
Proof.
  intros op bits val. unfold code_pack.
  pose proof (wrap8_range op). pose proof (wrap8_range bits). pose proof (wrap16_range val).
  change (2 ^ 8) with 256 in *. change (2 ^ 16) with 65536 in *. change (2 ^ 32) with 4294967296. lia.
Qed.
Lemma ty16_init : forall g base n, ty16 (iarr_u16_of g base n).
Proof.
  intros g base n i. unfold iarr_u16_of. rewrite arr_get_init. unfold init_u16.
  pose proof (wrap8_range (g (base + 2 * i))). pose proof (wrap8_range (g (base + 2 * i + 1))).
  change (2 ^ 8) with 256 in *. change (2 ^ 16) with 65536. lia.
Qed.
Lemma ty32_init : forall g base n, ty32 (iarr_u32_of g base n).
Proof.
  intros g base n i. unfold iarr_u32_of. rewrite arr_get_init. unfold init_u32, init_u16.
  pose proof (wrap8_range (g (base + 2 * (2 * i)))). pose proof (wrap8_range (g (base + 2 * (2 * i) + 1))).
  pose proof (wrap8_range (g (base + 2 * (2 * i + 1)))). pose proof (wrap8_range (g (base + 2 * (2 * i + 1) + 1))).
  change (2 ^ 8) with 256 in *. change (2 ^ 32) with 4294967296. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma it_fill_ty : forall here incr huff drop next fill tbl,
  0 <= here < 2 ^ 32 -> ty32 tbl -> ty32 (it_fill here incr huff drop next fill tbl).
Proof.
  intros here incr huff drop next fill tbl Hh Ht. unfold it_fill.
  apply (loopZ_ind (fun ft : Z * arr => ty32 (snd ft))); [|cbn [snd]; exact Ht].
  intros [fl tb] H. cbn [snd] in H. cbv zeta. destruct (negb _); cbn [snd]; apply ty32_set; assumption.
Qed.

Lemma it_step_ty : forall x st, ty32 (t_tbl st) -> ty16 (t_work st) ->
  match it_step x st with
  | ItCont st' | ItBreak st' | ItFail st' => ty32 (t_tbl st') /\ ty16 (t_work st')
  end.
Proof.
  intros x st Ht Hw. unfold it_step.
  destruct (if arr_get (t_work st) (t_sym st) + 1 <? it_match (x_ty x) then _ else _) as [hop hval].
  cbv zeta.
  assert (F : ty32 (it_fill (code_pack hop (wrap8 (t_len st - t_drop st)) hval) (shl32 1 (t_len st - t_drop st))
                               (t_huff st) (t_drop st) (t_next st) (shl32 1 (t_curr st)) (t_tbl st))).
  { apply it_fill_ty; [apply code_pack_ty | exact Ht]. }
  destruct (_ && (t_len st =? x_max x)); [cbn [t_tbl t_work]; split; assumption|].
  destruct (_ && negb _); [|cbn [t_tbl t_work]; split; assumption].
  destruct (it_not_enough _ _); cbn [t_tbl t_work]; [split; assumption|].
  split; [apply ty32_set; [exact F | apply code_pack_ty] | exact Hw].
Qed.

Lemma it_loop_ty : forall x codes st, ty32 (t_tbl st) -> ty16 (t_work st) ->
  match it_loop x codes st with inl st' | inr st' => ty32 (t_tbl st') /\ ty16 (t_work st') end.
Proof.
  intros x codes st Ht Hw. unfold it_loop.
  apply (iterZ_ind2 (fun st => ty32 (t_tbl st) /\ ty16 (t_work st))
                    (fun r : ItSt + ItSt => match r with inl st' | inr st' => ty32 (t_tbl st') /\ ty16 (t_work st') end));
    [| intros a Ha; exact Ha | split; assumption].
  intros a [Ha1 Ha2]. pose proof (it_step_ty x a Ha1 Ha2) as S. destruct (it_step x a); exact S.
Qed.

Lemma it_sort_ty : forall lens lens_ofs codes offs work, ty16 work -> ty16 (snd (it_sort lens lens_ofs codes (offs, work))).
Proof.
  intros lens lens_ofs codes offs work Hw. unfold it_sort.
  apply (forZ_ind (fun ow : arr * arr => ty16 (snd ow))); [|cbn [snd]; exact Hw].
  intros i [o w] H. cbn [snd] in H. cbv zeta. destruct (negb _); cbn [snd]; [apply ty16_set; [exact H | apply wrap16_ty] | exact H].
Qed.

Theorem inflate_table_typed : forall ty lens lens_ofs codes tbl table bits work,
  ty32 tbl -> ty16 work ->
  let '(ret, tbl', toff, bits', work') := inflate_table ty lens lens_ofs codes tbl table bits work in
  ty32 tbl' /\ ty16 work'.
Proof.
  intros ty lens lens_ofs codes tbl table bits work Ht Hw. unfold inflate_table. cbv zeta.
  destruct (it_find_max _ =? 0).
  { split; [apply ty32_set; [apply ty32_set; [exact Ht|]|]; apply code_pack_ty | exact Hw]. }
  destruct (it_left_check _) as [lft|]; [|split; assumption].
  destruct ((0 <? lft) && _); [split; assumption|].
  lazymatch goal with |- context [it_sort ?l ?o ?n (?f, ?w)] =>
    pose proof (it_sort_ty l o n f w Hw) as SW; destruct (it_sort l o n (f, w)) as [offs' work1] end.
  cbn [snd] in SW.
  destruct (it_not_enough _ _); [split; assumption|].
  lazymatch goal with |- context [it_loop ?x ?n ?st] =>
    pose proof (it_loop_ty x n st ltac:(cbn [t_tbl]; exact Ht) ltac:(cbn [t_work]; exact SW)) as L;
    destruct (it_loop x n st) as [st'|st'] end.
  - destruct L as [L1 L2]. split; [|exact L2]. destruct (negb (t_huff st' =? 0)); [apply ty32_set; [exact L1 | apply code_pack_ty] | exact L1].
  - exact L.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ATY (s : inflate_state) : Prop := ty16 (is_lens s) /\ ty16 (is_work s) /\ ty32 (is_codes s).

Definition wof {A} (res : ares A) : iw := match res with ARun _ w => w | ALeave w => w | ARet _ w => w end.
Definition ATYr {A} (res : ares A) : Prop := ATY (w_s (wof res)).

Lemma ATY_same : forall s s', ATY s -> is_lens s' = is_lens s -> is_work s' = is_work s -> is_codes s' = is_codes s -> ATY s'.
Proof. intros s s' H E1 E2 E3. unfold ATY. rewrite E1, E2, E3. exact H. Qed.

Section Rules.
  Context {A B : Type}.
  Lemma ATYr_bind : forall (m : AM A) (f : A -> AM B) w,
    ATYr (m w) -> (forall a w', ATY (w_s w') -> ATYr (f a w')) -> ATYr (abind m f w).
  Proof. intros m f w Hm Hf. unfold abind. unfold ATYr, wof in Hm. destruct (m w) as [a w'|w'|rc w']; [exact (Hf a w' Hm) | exact Hm | exact Hm]. Qed.
  Lemma ATYr_bind_run : forall (m : AM A) (f : A -> AM B) w a w',
    m w = ARun a w' -> ATYr (f a w') -> ATYr (abind m f w).
  Proof. intros m f w a w' E H. unfold abind. rewrite E. exact H. Qed.
End Rules.

(* [comment removed for export] *)
Lemma inflate_fast_arrs : forall w,
  is_lens (w_s (inflate_fast w)) = is_lens (w_s w) /\ is_work (w_s (inflate_fast w)) = is_work (w_s w)
  /\ is_codes (w_s (inflate_fast w)) = is_codes (w_s w).
Proof.
  intros [s c r]. unfold inflate_fast. cbn [w_s w_c w_r]. cbv zeta.
  lazymatch goal with |- context [iterZ ?n ?st ?d ?a] => generalize (iterZ n st d a); intros [f mm] end.
  destruct mm as [[md [mg|]]|]; cbn [w_s]; repeat split; reflexivity.
Qed.
Lemma fast_aty : forall w, ATY (w_s w) -> ATYr (amodify (fun w0 => LOAD (inflate_fast (RESTORE w0))) w).
Proof.
  intros w H. unfold ATYr, wof, amodify, LOAD. cbn [w_s wset_r].
  destruct (inflate_fast_arrs (RESTORE w)) as (E1 & E2 & E3).
  apply (ATY_same (w_s (RESTORE w))); [|exact E1|exact E2|exact E3].
  destruct w as [s c r]. unfold RESTORE. cbn [w_s w_c w_r]. cbn [w_s] in H. apply (ATY_same s _ H); reflexivity.
Qed.
Lemma restore_aty : forall w, ATY (w_s w) -> ATYr (amodify RESTORE w).
Proof. intros [s c r] H. unfold ATYr, wof, amodify, RESTORE. cbn [w_s w_c w_r]. cbn [w_s] in H. apply (ATY_same s _ H); reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac aty_arr :=
  first [ assumption
        | match goal with HA : ATY _ |- _ => first [exact (proj1 HA) | exact (proj1 (proj2 HA)) | exact (proj2 (proj2 HA))] end
        | apply ty16_set; [aty_arr | first [apply wrap16_ty | assumption]]
        | apply ty32_set; [aty_arr | first [apply code_pack_ty | assumption]]
        | apply ty16_init | apply ty32_init ].
Ltac aty_state := first [ assumption | unfold ATY; sacc; split; [aty_arr | split; aty_arr] ].

(* [comment removed for export] *)
Ltac aty_known := fail.

(* [comment removed for export] *)
Ltac aty_step :=
  cbv beta zeta;
  lazymatch goal with
  | |- forall a w, ATY (w_s w) -> _ => intros ? ? ?
  | |- ATYr (ARun _ _) => unfold ATYr, wof; aty_state
  | |- ATYr (ALeave _) => unfold ATYr, wof; aty_state
  | |- ATYr (ARet _ _) => unfold ATYr, wof; aty_state
  | |- ATYr (abind (gs _) _ _) => eapply ATYr_bind_run; [reflexivity|]
  | |- ATYr (abind (gr _) _ _) => eapply ATYr_bind_run; [reflexivity|]
  | |- ATYr (abind (gc _) _ _) => eapply ATYr_bind_run; [reflexivity|]
  | |- ATYr (abind aget _ _) => eapply ATYr_bind_run; [reflexivity|]
  | |- ATYr (abind (BITS _) _ _) => eapply ATYr_bind_run; [reflexivity|]
  | |- ATYr (abind HOLD _ _) => eapply ATYr_bind_run; [reflexivity|]
  | |- ATYr (abind _ _ _) => apply ATYr_bind; [| repeat match goal with HA : ATY _ |- _ => clear HA end]
  | |- ATYr ((if ?b then _ else _) _) => destruct b
  | |- ATYr (if ?b then _ else _) => destruct b
  | |- ATYr ((match inflate_table ?ty ?l ?o ?n ?t ?tb ?b ?wk with _ => _ end) _) =>
      let IT := fresh "IT" in
      pose proof (inflate_table_typed ty l o n t tb b wk ltac:(aty_arr) ltac:(aty_arr)) as IT;
      destruct (inflate_table ty l o n t tb b wk) as [[[[? ?] ?] ?] ?]; destruct IT as [? ?]
  | |- ATYr (match inflate_table ?ty ?l ?o ?n ?t ?tb ?b ?wk with _ => _ end) =>
      let IT := fresh "IT" in
      pose proof (inflate_table_typed ty l o n t tb b wk ltac:(aty_arr) ltac:(aty_arr)) as IT;
      destruct (inflate_table ty l o n t tb b wk) as [[[[? ?] ?] ?] ?]; destruct IT as [? ?]
  | |- ATYr ((match ?x with _ => _ end) _) => destruct x
  | |- ATYr (match ?x with _ => _ end) => destruct x
  | |- ATYr (amodify RESTORE _) => apply restore_aty; aty_state
  | |- ATYr (amodify _ _) => apply fast_aty; aty_state
  | |- ATYr _ =>
      first [ aty_known
            | match goal with K : forall w0, ATY (w_s w0) -> ATYr _ |- _ => apply K; aty_state end
            | match goal with K : forall x w0, ATY (w_s w0) -> ATYr _ |- _ => apply K; aty_state end
            | match goal with K : forall x y w0, ATY (w_s w0) -> ATYr _ |- _ => apply K; aty_state end
            | match goal with K : forall x y z w0, ATY (w_s w0) -> ATYr _ |- _ => apply K; aty_state end
            | progress (cbv beta zeta delta [aret aleave areturn aget agets gs gc gr us uc ur BITS HOLD DROPBITS INITBITS BYTEBITS
                                            set_mode set_msg go_bad set_adler_check CRC2 CRC4 aux set_back add_back set_lens
                                            PULLBYTE crc_input NEEDBITS DECODE1 DECODE2]) ]
  end.
Ltac aty := repeat aty_step.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma NEEDBITS_k_aty : forall k n w, ATY (w_s w) -> ATYr (NEEDBITS_k k n w).
Proof. induction k as [|k IH]; intros n w HA; cbn [NEEDBITS_k]; aty. Qed.
Lemma NEEDBITS_aty : forall n w, ATY (w_s w) -> ATYr (NEEDBITS n w).
Proof. intros n w HA. unfold NEEDBITS. apply NEEDBITS_k_aty. exact HA. Qed.

Lemma DECODE_k_aty : forall k p index need w, ATY (w_s w) -> ATYr (DECODE_k k p index need w).
Proof. induction k as [|k IH]; intros p index need w HA; cbn [DECODE_k]; aty. Qed.
Lemma DECODE1_aty : forall p n w, ATY (w_s w) -> ATYr (DECODE1 p n w).
Proof. intros p n w HA. unfold DECODE1. apply DECODE_k_aty. exact HA. Qed.
Lemma DECODE2_aty : forall p l w, ATY (w_s w) -> ATYr (DECODE2 p l w).
Proof. intros p l w HA. unfold DECODE2. apply DECODE_k_aty. exact HA. Qed.

Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  end.

Ltac aty_state ::= first [ assumption | unfold ATY; cbv delta [fixedtables]; sacc; split; [aty_arr | split; aty_arr] ].

Lemma lens_repeat_aty : forall copy len w, ATY (w_s w) -> ATYr (lens_repeat copy len w).
Proof.
  intros copy len w HA. unfold lens_repeat, us, ATYr, wof. cbn [w_s wset_s].
  lazymatch goal with |- context [loopZ ?n ?st ?a] =>
    assert (L : ty16 (fst (fst (loopZ n st a))));
    [ apply (loopZ_ind (fun x : arr * Z * Z => ty16 (fst (fst x))));
      [ intros [[l h] cp] H; cbn [fst] in H; destruct (negb (cp =? 0)); cbn [fst snd]; [apply ty16_set; [exact H | apply wrap16_ty] | exact H]
      | cbn [fst]; aty_arr ]
    | destruct (loopZ n st a) as [[l h] cp]; cbn [fst] in L ] end.
  aty_state.
Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  end.


(* [comment removed for export] *)
Lemma arm_DONE_aty : forall w, ATY (w_s w) -> ATYr (arm_DONE w).
Proof. intros w HA. unfold arm_DONE. aty. Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  | |- ATYr (arm_DONE _) => apply arm_DONE_aty; aty_state
  end.
Lemma arm_LENGTH_aty : forall w, ATY (w_s w) -> ATYr (arm_LENGTH w).
Proof. intros w HA. unfold arm_LENGTH. aty. Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  | |- ATYr (arm_DONE _) => apply arm_DONE_aty; aty_state
  | |- ATYr (arm_LENGTH _) => apply arm_LENGTH_aty; aty_state
  end.
Lemma arm_CHECK_aty : forall w, ATY (w_s w) -> ATYr (arm_CHECK w).
Proof. intros w HA. unfold arm_CHECK. aty. Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  | |- ATYr (arm_DONE _) => apply arm_DONE_aty; aty_state
  | |- ATYr (arm_LENGTH _) => apply arm_LENGTH_aty; aty_state
  | |- ATYr (arm_CHECK _) => apply arm_CHECK_aty; aty_state
  end.
Lemma arm_LIT_aty : forall w, ATY (w_s w) -> ATYr (arm_LIT w).
Proof. intros w HA. unfold arm_LIT. aty. Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  | |- ATYr (arm_DONE _) => apply arm_DONE_aty; aty_state
  | |- ATYr (arm_LENGTH _) => apply arm_LENGTH_aty; aty_state
  | |- ATYr (arm_CHECK _) => apply arm_CHECK_aty; aty_state
  | |- ATYr (arm_LIT _) => apply arm_LIT_aty; aty_state
  end.
Lemma arm_MATCH_aty : forall iv w, ATY (w_s w) -> ATYr (arm_MATCH iv w).
Proof. intros iv w HA. unfold arm_MATCH. aty. Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  | |- ATYr (arm_DONE _) => apply arm_DONE_aty; aty_state
  | |- ATYr (arm_LENGTH _) => apply arm_LENGTH_aty; aty_state
  | |- ATYr (arm_CHECK _) => apply arm_CHECK_aty; aty_state
  | |- ATYr (arm_LIT _) => apply arm_LIT_aty; aty_state
  | |- ATYr (arm_MATCH _ _) => apply arm_MATCH_aty; aty_state
  end.
Lemma arm_DISTEXT_aty : forall iv w, ATY (w_s w) -> ATYr (arm_DISTEXT iv w).
Proof. intros iv w HA. unfold arm_DISTEXT. aty. Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  | |- ATYr (arm_DONE _) => apply arm_DONE_aty; aty_state
  | |- ATYr (arm_LENGTH _) => apply arm_LENGTH_aty; aty_state
  | |- ATYr (arm_CHECK _) => apply arm_CHECK_aty; aty_state
  | |- ATYr (arm_LIT _) => apply arm_LIT_aty; aty_state
  | |- ATYr (arm_MATCH _ _) => apply arm_MATCH_aty; aty_state
  | |- ATYr (arm_DISTEXT _ _) => apply arm_DISTEXT_aty; aty_state
  end.
Lemma arm_DIST_aty : forall iv w, ATY (w_s w) -> ATYr (arm_DIST iv w).
Proof. intros iv w HA. unfold arm_DIST. aty. Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  | |- ATYr (arm_DONE _) => apply arm_DONE_aty; aty_state
  | |- ATYr (arm_LENGTH _) => apply arm_LENGTH_aty; aty_state
  | |- ATYr (arm_CHECK _) => apply arm_CHECK_aty; aty_state
  | |- ATYr (arm_LIT _) => apply arm_LIT_aty; aty_state
  | |- ATYr (arm_MATCH _ _) => apply arm_MATCH_aty; aty_state
  | |- ATYr (arm_DISTEXT _ _) => apply arm_DISTEXT_aty; aty_state
  | |- ATYr (arm_DIST _ _) => apply arm_DIST_aty; aty_state
  end.
Lemma arm_LENEXT_aty : forall iv w, ATY (w_s w) -> ATYr (arm_LENEXT iv w).
Proof. intros iv w HA. unfold arm_LENEXT. aty. Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  | |- ATYr (arm_DONE _) => apply arm_DONE_aty; aty_state
  | |- ATYr (arm_LENGTH _) => apply arm_LENGTH_aty; aty_state
  | |- ATYr (arm_CHECK _) => apply arm_CHECK_aty; aty_state
  | |- ATYr (arm_LIT _) => apply arm_LIT_aty; aty_state
  | |- ATYr (arm_MATCH _ _) => apply arm_MATCH_aty; aty_state
  | |- ATYr (arm_DISTEXT _ _) => apply arm_DISTEXT_aty; aty_state
  | |- ATYr (arm_DIST _ _) => apply arm_DIST_aty; aty_state
  | |- ATYr (arm_LENEXT _ _) => apply arm_LENEXT_aty; aty_state
  end.
Lemma arm_LEN_aty : forall iv w, ATY (w_s w) -> ATYr (arm_LEN iv w).
Proof. intros iv w HA. unfold arm_LEN. aty. Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  | |- ATYr (arm_DONE _) => apply arm_DONE_aty; aty_state
  | |- ATYr (arm_LENGTH _) => apply arm_LENGTH_aty; aty_state
  | |- ATYr (arm_CHECK _) => apply arm_CHECK_aty; aty_state
  | |- ATYr (arm_LIT _) => apply arm_LIT_aty; aty_state
  | |- ATYr (arm_MATCH _ _) => apply arm_MATCH_aty; aty_state
  | |- ATYr (arm_DISTEXT _ _) => apply arm_DISTEXT_aty; aty_state
  | |- ATYr (arm_DIST _ _) => apply arm_DIST_aty; aty_state
  | |- ATYr (arm_LENEXT _ _) => apply arm_LENEXT_aty; aty_state
  | |- ATYr (arm_LEN _ _) => apply arm_LEN_aty; aty_state
  end.
Lemma arm_LEN__aty : forall iv w, ATY (w_s w) -> ATYr (arm_LEN_ iv w).
Proof. intros iv w HA. unfold arm_LEN_. aty. Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  | |- ATYr (arm_DONE _) => apply arm_DONE_aty; aty_state
  | |- ATYr (arm_LENGTH _) => apply arm_LENGTH_aty; aty_state
  | |- ATYr (arm_CHECK _) => apply arm_CHECK_aty; aty_state
  | |- ATYr (arm_LIT _) => apply arm_LIT_aty; aty_state
  | |- ATYr (arm_MATCH _ _) => apply arm_MATCH_aty; aty_state
  | |- ATYr (arm_DISTEXT _ _) => apply arm_DISTEXT_aty; aty_state
  | |- ATYr (arm_DIST _ _) => apply arm_DIST_aty; aty_state
  | |- ATYr (arm_LENEXT _ _) => apply arm_LENEXT_aty; aty_state
  | |- ATYr (arm_LEN _ _) => apply arm_LEN_aty; aty_state
  | |- ATYr (arm_LEN_ _ _) => apply arm_LEN__aty; aty_state
  end.
Lemma codelens_body_aty : forall w, ATY (w_s w) -> ATYr (codelens_body w).
Proof. intros w HA. unfold codelens_body. aty. Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  | |- ATYr (arm_DONE _) => apply arm_DONE_aty; aty_state
  | |- ATYr (arm_LENGTH _) => apply arm_LENGTH_aty; aty_state
  | |- ATYr (arm_CHECK _) => apply arm_CHECK_aty; aty_state
  | |- ATYr (arm_LIT _) => apply arm_LIT_aty; aty_state
  | |- ATYr (arm_MATCH _ _) => apply arm_MATCH_aty; aty_state
  | |- ATYr (arm_DISTEXT _ _) => apply arm_DISTEXT_aty; aty_state
  | |- ATYr (arm_DIST _ _) => apply arm_DIST_aty; aty_state
  | |- ATYr (arm_LENEXT _ _) => apply arm_LENEXT_aty; aty_state
  | |- ATYr (arm_LEN _ _) => apply arm_LEN_aty; aty_state
  | |- ATYr (arm_LEN_ _ _) => apply arm_LEN__aty; aty_state
  | |- ATYr (codelens_body _) => apply codelens_body_aty; aty_state
  end.
Lemma codelens_while_aty : forall k w, ATY (w_s w) -> ATYr (codelens_while k w).
Proof. induction k as [|k IH]; intros w HA; cbn [codelens_while]; aty. Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  | |- ATYr (arm_DONE _) => apply arm_DONE_aty; aty_state
  | |- ATYr (arm_LENGTH _) => apply arm_LENGTH_aty; aty_state
  | |- ATYr (arm_CHECK _) => apply arm_CHECK_aty; aty_state
  | |- ATYr (arm_LIT _) => apply arm_LIT_aty; aty_state
  | |- ATYr (arm_MATCH _ _) => apply arm_MATCH_aty; aty_state
  | |- ATYr (arm_DISTEXT _ _) => apply arm_DISTEXT_aty; aty_state
  | |- ATYr (arm_DIST _ _) => apply arm_DIST_aty; aty_state
  | |- ATYr (arm_LENEXT _ _) => apply arm_LENEXT_aty; aty_state
  | |- ATYr (arm_LEN _ _) => apply arm_LEN_aty; aty_state
  | |- ATYr (arm_LEN_ _ _) => apply arm_LEN__aty; aty_state
  | |- ATYr (codelens_body _) => apply codelens_body_aty; aty_state
  | |- ATYr (codelens_while _ _) => apply codelens_while_aty; aty_state
  end.
Lemma arm_CODELENS_aty : forall iv flush w, ATY (w_s w) -> ATYr (arm_CODELENS iv flush w).
Proof. intros iv flush w HA. unfold arm_CODELENS. aty. Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  | |- ATYr (arm_DONE _) => apply arm_DONE_aty; aty_state
  | |- ATYr (arm_LENGTH _) => apply arm_LENGTH_aty; aty_state
  | |- ATYr (arm_CHECK _) => apply arm_CHECK_aty; aty_state
  | |- ATYr (arm_LIT _) => apply arm_LIT_aty; aty_state
  | |- ATYr (arm_MATCH _ _) => apply arm_MATCH_aty; aty_state
  | |- ATYr (arm_DISTEXT _ _) => apply arm_DISTEXT_aty; aty_state
  | |- ATYr (arm_DIST _ _) => apply arm_DIST_aty; aty_state
  | |- ATYr (arm_LENEXT _ _) => apply arm_LENEXT_aty; aty_state
  | |- ATYr (arm_LEN _ _) => apply arm_LEN_aty; aty_state
  | |- ATYr (arm_LEN_ _ _) => apply arm_LEN__aty; aty_state
  | |- ATYr (codelens_body _) => apply codelens_body_aty; aty_state
  | |- ATYr (codelens_while _ _) => apply codelens_while_aty; aty_state
  | |- ATYr (arm_CODELENS _ _ _) => apply arm_CODELENS_aty; aty_state
  end.
Lemma lenlens_while1_aty : forall k w, ATY (w_s w) -> ATYr (lenlens_while1 k w).
Proof. induction k as [|k IH]; intros w HA; cbn [lenlens_while1]; aty. Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  | |- ATYr (arm_DONE _) => apply arm_DONE_aty; aty_state
  | |- ATYr (arm_LENGTH _) => apply arm_LENGTH_aty; aty_state
  | |- ATYr (arm_CHECK _) => apply arm_CHECK_aty; aty_state
  | |- ATYr (arm_LIT _) => apply arm_LIT_aty; aty_state
  | |- ATYr (arm_MATCH _ _) => apply arm_MATCH_aty; aty_state
  | |- ATYr (arm_DISTEXT _ _) => apply arm_DISTEXT_aty; aty_state
  | |- ATYr (arm_DIST _ _) => apply arm_DIST_aty; aty_state
  | |- ATYr (arm_LENEXT _ _) => apply arm_LENEXT_aty; aty_state
  | |- ATYr (arm_LEN _ _) => apply arm_LEN_aty; aty_state
  | |- ATYr (arm_LEN_ _ _) => apply arm_LEN__aty; aty_state
  | |- ATYr (codelens_body _) => apply codelens_body_aty; aty_state
  | |- ATYr (codelens_while _ _) => apply codelens_while_aty; aty_state
  | |- ATYr (arm_CODELENS _ _ _) => apply arm_CODELENS_aty; aty_state
  | |- ATYr (lenlens_while1 _ _) => apply lenlens_while1_aty; aty_state
  end.
Lemma lenlens_while2_aty : forall k w, ATY (w_s w) -> ATYr (lenlens_while2 k w).
Proof. induction k as [|k IH]; intros w HA; cbn [lenlens_while2]; aty. Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  | |- ATYr (arm_DONE _) => apply arm_DONE_aty; aty_state
  | |- ATYr (arm_LENGTH _) => apply arm_LENGTH_aty; aty_state
  | |- ATYr (arm_CHECK _) => apply arm_CHECK_aty; aty_state
  | |- ATYr (arm_LIT _) => apply arm_LIT_aty; aty_state
  | |- ATYr (arm_MATCH _ _) => apply arm_MATCH_aty; aty_state
  | |- ATYr (arm_DISTEXT _ _) => apply arm_DISTEXT_aty; aty_state
  | |- ATYr (arm_DIST _ _) => apply arm_DIST_aty; aty_state
  | |- ATYr (arm_LENEXT _ _) => apply arm_LENEXT_aty; aty_state
  | |- ATYr (arm_LEN _ _) => apply arm_LEN_aty; aty_state
  | |- ATYr (arm_LEN_ _ _) => apply arm_LEN__aty; aty_state
  | |- ATYr (codelens_body _) => apply codelens_body_aty; aty_state
  | |- ATYr (codelens_while _ _) => apply codelens_while_aty; aty_state
  | |- ATYr (arm_CODELENS _ _ _) => apply arm_CODELENS_aty; aty_state
  | |- ATYr (lenlens_while1 _ _) => apply lenlens_while1_aty; aty_state
  | |- ATYr (lenlens_while2 _ _) => apply lenlens_while2_aty; aty_state
  end.
Lemma arm_LENLENS_aty : forall iv flush w, ATY (w_s w) -> ATYr (arm_LENLENS iv flush w).
Proof. intros iv flush w HA. unfold arm_LENLENS. aty. Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  | |- ATYr (arm_DONE _) => apply arm_DONE_aty; aty_state
  | |- ATYr (arm_LENGTH _) => apply arm_LENGTH_aty; aty_state
  | |- ATYr (arm_CHECK _) => apply arm_CHECK_aty; aty_state
  | |- ATYr (arm_LIT _) => apply arm_LIT_aty; aty_state
  | |- ATYr (arm_MATCH _ _) => apply arm_MATCH_aty; aty_state
  | |- ATYr (arm_DISTEXT _ _) => apply arm_DISTEXT_aty; aty_state
  | |- ATYr (arm_DIST _ _) => apply arm_DIST_aty; aty_state
  | |- ATYr (arm_LENEXT _ _) => apply arm_LENEXT_aty; aty_state
  | |- ATYr (arm_LEN _ _) => apply arm_LEN_aty; aty_state
  | |- ATYr (arm_LEN_ _ _) => apply arm_LEN__aty; aty_state
  | |- ATYr (codelens_body _) => apply codelens_body_aty; aty_state
  | |- ATYr (codelens_while _ _) => apply codelens_while_aty; aty_state
  | |- ATYr (arm_CODELENS _ _ _) => apply arm_CODELENS_aty; aty_state
  | |- ATYr (lenlens_while1 _ _) => apply lenlens_while1_aty; aty_state
  | |- ATYr (lenlens_while2 _ _) => apply lenlens_while2_aty; aty_state
  | |- ATYr (arm_LENLENS _ _ _) => apply arm_LENLENS_aty; aty_state
  end.
Lemma arm_TABLE_aty : forall iv flush w, ATY (w_s w) -> ATYr (arm_TABLE iv flush w).
Proof. intros iv flush w HA. unfold arm_TABLE. aty. Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  | |- ATYr (arm_DONE _) => apply arm_DONE_aty; aty_state
  | |- ATYr (arm_LENGTH _) => apply arm_LENGTH_aty; aty_state
  | |- ATYr (arm_CHECK _) => apply arm_CHECK_aty; aty_state
  | |- ATYr (arm_LIT _) => apply arm_LIT_aty; aty_state
  | |- ATYr (arm_MATCH _ _) => apply arm_MATCH_aty; aty_state
  | |- ATYr (arm_DISTEXT _ _) => apply arm_DISTEXT_aty; aty_state
  | |- ATYr (arm_DIST _ _) => apply arm_DIST_aty; aty_state
  | |- ATYr (arm_LENEXT _ _) => apply arm_LENEXT_aty; aty_state
  | |- ATYr (arm_LEN _ _) => apply arm_LEN_aty; aty_state
  | |- ATYr (arm_LEN_ _ _) => apply arm_LEN__aty; aty_state
  | |- ATYr (codelens_body _) => apply codelens_body_aty; aty_state
  | |- ATYr (codelens_while _ _) => apply codelens_while_aty; aty_state
  | |- ATYr (arm_CODELENS _ _ _) => apply arm_CODELENS_aty; aty_state
  | |- ATYr (lenlens_while1 _ _) => apply lenlens_while1_aty; aty_state
  | |- ATYr (lenlens_while2 _ _) => apply lenlens_while2_aty; aty_state
  | |- ATYr (arm_LENLENS _ _ _) => apply arm_LENLENS_aty; aty_state
  | |- ATYr (arm_TABLE _ _ _) => apply arm_TABLE_aty; aty_state
  end.
Lemma arm_COPY_aty : forall w, ATY (w_s w) -> ATYr (arm_COPY w).
Proof. intros w HA. unfold arm_COPY. aty. Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  | |- ATYr (arm_DONE _) => apply arm_DONE_aty; aty_state
  | |- ATYr (arm_LENGTH _) => apply arm_LENGTH_aty; aty_state
  | |- ATYr (arm_CHECK _) => apply arm_CHECK_aty; aty_state
  | |- ATYr (arm_LIT _) => apply arm_LIT_aty; aty_state
  | |- ATYr (arm_MATCH _ _) => apply arm_MATCH_aty; aty_state
  | |- ATYr (arm_DISTEXT _ _) => apply arm_DISTEXT_aty; aty_state
  | |- ATYr (arm_DIST _ _) => apply arm_DIST_aty; aty_state
  | |- ATYr (arm_LENEXT _ _) => apply arm_LENEXT_aty; aty_state
  | |- ATYr (arm_LEN _ _) => apply arm_LEN_aty; aty_state
  | |- ATYr (arm_LEN_ _ _) => apply arm_LEN__aty; aty_state
  | |- ATYr (codelens_body _) => apply codelens_body_aty; aty_state
  | |- ATYr (codelens_while _ _) => apply codelens_while_aty; aty_state
  | |- ATYr (arm_CODELENS _ _ _) => apply arm_CODELENS_aty; aty_state
  | |- ATYr (lenlens_while1 _ _) => apply lenlens_while1_aty; aty_state
  | |- ATYr (lenlens_while2 _ _) => apply lenlens_while2_aty; aty_state
  | |- ATYr (arm_LENLENS _ _ _) => apply arm_LENLENS_aty; aty_state
  | |- ATYr (arm_TABLE _ _ _) => apply arm_TABLE_aty; aty_state
  | |- ATYr (arm_COPY _) => apply arm_COPY_aty; aty_state
  end.
Lemma arm_COPY__aty : forall w, ATY (w_s w) -> ATYr (arm_COPY_ w).
Proof. intros w HA. unfold arm_COPY_. aty. Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  | |- ATYr (arm_DONE _) => apply arm_DONE_aty; aty_state
  | |- ATYr (arm_LENGTH _) => apply arm_LENGTH_aty; aty_state
  | |- ATYr (arm_CHECK _) => apply arm_CHECK_aty; aty_state
  | |- ATYr (arm_LIT _) => apply arm_LIT_aty; aty_state
  | |- ATYr (arm_MATCH _ _) => apply arm_MATCH_aty; aty_state
  | |- ATYr (arm_DISTEXT _ _) => apply arm_DISTEXT_aty; aty_state
  | |- ATYr (arm_DIST _ _) => apply arm_DIST_aty; aty_state
  | |- ATYr (arm_LENEXT _ _) => apply arm_LENEXT_aty; aty_state
  | |- ATYr (arm_LEN _ _) => apply arm_LEN_aty; aty_state
  | |- ATYr (arm_LEN_ _ _) => apply arm_LEN__aty; aty_state
  | |- ATYr (codelens_body _) => apply codelens_body_aty; aty_state
  | |- ATYr (codelens_while _ _) => apply codelens_while_aty; aty_state
  | |- ATYr (arm_CODELENS _ _ _) => apply arm_CODELENS_aty; aty_state
  | |- ATYr (lenlens_while1 _ _) => apply lenlens_while1_aty; aty_state
  | |- ATYr (lenlens_while2 _ _) => apply lenlens_while2_aty; aty_state
  | |- ATYr (arm_LENLENS _ _ _) => apply arm_LENLENS_aty; aty_state
  | |- ATYr (arm_TABLE _ _ _) => apply arm_TABLE_aty; aty_state
  | |- ATYr (arm_COPY _) => apply arm_COPY_aty; aty_state
  | |- ATYr (arm_COPY_ _) => apply arm_COPY__aty; aty_state
  end.
Lemma arm_STORED_aty : forall iv flush w, ATY (w_s w) -> ATYr (arm_STORED iv flush w).
Proof. intros iv flush w HA. unfold arm_STORED. aty. Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  | |- ATYr (arm_DONE _) => apply arm_DONE_aty; aty_state
  | |- ATYr (arm_LENGTH _) => apply arm_LENGTH_aty; aty_state
  | |- ATYr (arm_CHECK _) => apply arm_CHECK_aty; aty_state
  | |- ATYr (arm_LIT _) => apply arm_LIT_aty; aty_state
  | |- ATYr (arm_MATCH _ _) => apply arm_MATCH_aty; aty_state
  | |- ATYr (arm_DISTEXT _ _) => apply arm_DISTEXT_aty; aty_state
  | |- ATYr (arm_DIST _ _) => apply arm_DIST_aty; aty_state
  | |- ATYr (arm_LENEXT _ _) => apply arm_LENEXT_aty; aty_state
  | |- ATYr (arm_LEN _ _) => apply arm_LEN_aty; aty_state
  | |- ATYr (arm_LEN_ _ _) => apply arm_LEN__aty; aty_state
  | |- ATYr (codelens_body _) => apply codelens_body_aty; aty_state
  | |- ATYr (codelens_while _ _) => apply codelens_while_aty; aty_state
  | |- ATYr (arm_CODELENS _ _ _) => apply arm_CODELENS_aty; aty_state
  | |- ATYr (lenlens_while1 _ _) => apply lenlens_while1_aty; aty_state
  | |- ATYr (lenlens_while2 _ _) => apply lenlens_while2_aty; aty_state
  | |- ATYr (arm_LENLENS _ _ _) => apply arm_LENLENS_aty; aty_state
  | |- ATYr (arm_TABLE _ _ _) => apply arm_TABLE_aty; aty_state
  | |- ATYr (arm_COPY _) => apply arm_COPY_aty; aty_state
  | |- ATYr (arm_COPY_ _) => apply arm_COPY__aty; aty_state
  | |- ATYr (arm_STORED _ _ _) => apply arm_STORED_aty; aty_state
  end.
Lemma arm_TYPEDO_aty : forall iv flush w, ATY (w_s w) -> ATYr (arm_TYPEDO iv flush w).
Proof. intros iv flush w HA. unfold arm_TYPEDO. aty. Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  | |- ATYr (arm_DONE _) => apply arm_DONE_aty; aty_state
  | |- ATYr (arm_LENGTH _) => apply arm_LENGTH_aty; aty_state
  | |- ATYr (arm_CHECK _) => apply arm_CHECK_aty; aty_state
  | |- ATYr (arm_LIT _) => apply arm_LIT_aty; aty_state
  | |- ATYr (arm_MATCH _ _) => apply arm_MATCH_aty; aty_state
  | |- ATYr (arm_DISTEXT _ _) => apply arm_DISTEXT_aty; aty_state
  | |- ATYr (arm_DIST _ _) => apply arm_DIST_aty; aty_state
  | |- ATYr (arm_LENEXT _ _) => apply arm_LENEXT_aty; aty_state
  | |- ATYr (arm_LEN _ _) => apply arm_LEN_aty; aty_state
  | |- ATYr (arm_LEN_ _ _) => apply arm_LEN__aty; aty_state
  | |- ATYr (codelens_body _) => apply codelens_body_aty; aty_state
  | |- ATYr (codelens_while _ _) => apply codelens_while_aty; aty_state
  | |- ATYr (arm_CODELENS _ _ _) => apply arm_CODELENS_aty; aty_state
  | |- ATYr (lenlens_while1 _ _) => apply lenlens_while1_aty; aty_state
  | |- ATYr (lenlens_while2 _ _) => apply lenlens_while2_aty; aty_state
  | |- ATYr (arm_LENLENS _ _ _) => apply arm_LENLENS_aty; aty_state
  | |- ATYr (arm_TABLE _ _ _) => apply arm_TABLE_aty; aty_state
  | |- ATYr (arm_COPY _) => apply arm_COPY_aty; aty_state
  | |- ATYr (arm_COPY_ _) => apply arm_COPY__aty; aty_state
  | |- ATYr (arm_STORED _ _ _) => apply arm_STORED_aty; aty_state
  | |- ATYr (arm_TYPEDO _ _ _) => apply arm_TYPEDO_aty; aty_state
  end.
Lemma arm_TYPE_aty : forall iv flush w, ATY (w_s w) -> ATYr (arm_TYPE iv flush w).
Proof. intros iv flush w HA. unfold arm_TYPE. aty. Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  | |- ATYr (arm_DONE _) => apply arm_DONE_aty; aty_state
  | |- ATYr (arm_LENGTH _) => apply arm_LENGTH_aty; aty_state
  | |- ATYr (arm_CHECK _) => apply arm_CHECK_aty; aty_state
  | |- ATYr (arm_LIT _) => apply arm_LIT_aty; aty_state
  | |- ATYr (arm_MATCH _ _) => apply arm_MATCH_aty; aty_state
  | |- ATYr (arm_DISTEXT _ _) => apply arm_DISTEXT_aty; aty_state
  | |- ATYr (arm_DIST _ _) => apply arm_DIST_aty; aty_state
  | |- ATYr (arm_LENEXT _ _) => apply arm_LENEXT_aty; aty_state
  | |- ATYr (arm_LEN _ _) => apply arm_LEN_aty; aty_state
  | |- ATYr (arm_LEN_ _ _) => apply arm_LEN__aty; aty_state
  | |- ATYr (codelens_body _) => apply codelens_body_aty; aty_state
  | |- ATYr (codelens_while _ _) => apply codelens_while_aty; aty_state
  | |- ATYr (arm_CODELENS _ _ _) => apply arm_CODELENS_aty; aty_state
  | |- ATYr (lenlens_while1 _ _) => apply lenlens_while1_aty; aty_state
  | |- ATYr (lenlens_while2 _ _) => apply lenlens_while2_aty; aty_state
  | |- ATYr (arm_LENLENS _ _ _) => apply arm_LENLENS_aty; aty_state
  | |- ATYr (arm_TABLE _ _ _) => apply arm_TABLE_aty; aty_state
  | |- ATYr (arm_COPY _) => apply arm_COPY_aty; aty_state
  | |- ATYr (arm_COPY_ _) => apply arm_COPY__aty; aty_state
  | |- ATYr (arm_STORED _ _ _) => apply arm_STORED_aty; aty_state
  | |- ATYr (arm_TYPEDO _ _ _) => apply arm_TYPEDO_aty; aty_state
  | |- ATYr (arm_TYPE _ _ _) => apply arm_TYPE_aty; aty_state
  end.
Lemma arm_DICT_aty : forall iv flush w, ATY (w_s w) -> ATYr (arm_DICT iv flush w).
Proof. intros iv flush w HA. unfold arm_DICT. aty. Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  | |- ATYr (arm_DONE _) => apply arm_DONE_aty; aty_state
  | |- ATYr (arm_LENGTH _) => apply arm_LENGTH_aty; aty_state
  | |- ATYr (arm_CHECK _) => apply arm_CHECK_aty; aty_state
  | |- ATYr (arm_LIT _) => apply arm_LIT_aty; aty_state
  | |- ATYr (arm_MATCH _ _) => apply arm_MATCH_aty; aty_state
  | |- ATYr (arm_DISTEXT _ _) => apply arm_DISTEXT_aty; aty_state
  | |- ATYr (arm_DIST _ _) => apply arm_DIST_aty; aty_state
  | |- ATYr (arm_LENEXT _ _) => apply arm_LENEXT_aty; aty_state
  | |- ATYr (arm_LEN _ _) => apply arm_LEN_aty; aty_state
  | |- ATYr (arm_LEN_ _ _) => apply arm_LEN__aty; aty_state
  | |- ATYr (codelens_body _) => apply codelens_body_aty; aty_state
  | |- ATYr (codelens_while _ _) => apply codelens_while_aty; aty_state
  | |- ATYr (arm_CODELENS _ _ _) => apply arm_CODELENS_aty; aty_state
  | |- ATYr (lenlens_while1 _ _) => apply lenlens_while1_aty; aty_state
  | |- ATYr (lenlens_while2 _ _) => apply lenlens_while2_aty; aty_state
  | |- ATYr (arm_LENLENS _ _ _) => apply arm_LENLENS_aty; aty_state
  | |- ATYr (arm_TABLE _ _ _) => apply arm_TABLE_aty; aty_state
  | |- ATYr (arm_COPY _) => apply arm_COPY_aty; aty_state
  | |- ATYr (arm_COPY_ _) => apply arm_COPY__aty; aty_state
  | |- ATYr (arm_STORED _ _ _) => apply arm_STORED_aty; aty_state
  | |- ATYr (arm_TYPEDO _ _ _) => apply arm_TYPEDO_aty; aty_state
  | |- ATYr (arm_TYPE _ _ _) => apply arm_TYPE_aty; aty_state
  | |- ATYr (arm_DICT _ _ _) => apply arm_DICT_aty; aty_state
  end.
Lemma arm_DICTID_aty : forall iv flush w, ATY (w_s w) -> ATYr (arm_DICTID iv flush w).
Proof. intros iv flush w HA. unfold arm_DICTID. aty. Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  | |- ATYr (arm_DONE _) => apply arm_DONE_aty; aty_state
  | |- ATYr (arm_LENGTH _) => apply arm_LENGTH_aty; aty_state
  | |- ATYr (arm_CHECK _) => apply arm_CHECK_aty; aty_state
  | |- ATYr (arm_LIT _) => apply arm_LIT_aty; aty_state
  | |- ATYr (arm_MATCH _ _) => apply arm_MATCH_aty; aty_state
  | |- ATYr (arm_DISTEXT _ _) => apply arm_DISTEXT_aty; aty_state
  | |- ATYr (arm_DIST _ _) => apply arm_DIST_aty; aty_state
  | |- ATYr (arm_LENEXT _ _) => apply arm_LENEXT_aty; aty_state
  | |- ATYr (arm_LEN _ _) => apply arm_LEN_aty; aty_state
  | |- ATYr (arm_LEN_ _ _) => apply arm_LEN__aty; aty_state
  | |- ATYr (codelens_body _) => apply codelens_body_aty; aty_state
  | |- ATYr (codelens_while _ _) => apply codelens_while_aty; aty_state
  | |- ATYr (arm_CODELENS _ _ _) => apply arm_CODELENS_aty; aty_state
  | |- ATYr (lenlens_while1 _ _) => apply lenlens_while1_aty; aty_state
  | |- ATYr (lenlens_while2 _ _) => apply lenlens_while2_aty; aty_state
  | |- ATYr (arm_LENLENS _ _ _) => apply arm_LENLENS_aty; aty_state
  | |- ATYr (arm_TABLE _ _ _) => apply arm_TABLE_aty; aty_state
  | |- ATYr (arm_COPY _) => apply arm_COPY_aty; aty_state
  | |- ATYr (arm_COPY_ _) => apply arm_COPY__aty; aty_state
  | |- ATYr (arm_STORED _ _ _) => apply arm_STORED_aty; aty_state
  | |- ATYr (arm_TYPEDO _ _ _) => apply arm_TYPEDO_aty; aty_state
  | |- ATYr (arm_TYPE _ _ _) => apply arm_TYPE_aty; aty_state
  | |- ATYr (arm_DICT _ _ _) => apply arm_DICT_aty; aty_state
  | |- ATYr (arm_DICTID _ _ _) => apply arm_DICTID_aty; aty_state
  end.
Lemma arm_HCRC_aty : forall w, ATY (w_s w) -> ATYr (arm_HCRC w).
Proof. intros w HA. unfold arm_HCRC. aty. Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  | |- ATYr (arm_DONE _) => apply arm_DONE_aty; aty_state
  | |- ATYr (arm_LENGTH _) => apply arm_LENGTH_aty; aty_state
  | |- ATYr (arm_CHECK _) => apply arm_CHECK_aty; aty_state
  | |- ATYr (arm_LIT _) => apply arm_LIT_aty; aty_state
  | |- ATYr (arm_MATCH _ _) => apply arm_MATCH_aty; aty_state
  | |- ATYr (arm_DISTEXT _ _) => apply arm_DISTEXT_aty; aty_state
  | |- ATYr (arm_DIST _ _) => apply arm_DIST_aty; aty_state
  | |- ATYr (arm_LENEXT _ _) => apply arm_LENEXT_aty; aty_state
  | |- ATYr (arm_LEN _ _) => apply arm_LEN_aty; aty_state
  | |- ATYr (arm_LEN_ _ _) => apply arm_LEN__aty; aty_state
  | |- ATYr (codelens_body _) => apply codelens_body_aty; aty_state
  | |- ATYr (codelens_while _ _) => apply codelens_while_aty; aty_state
  | |- ATYr (arm_CODELENS _ _ _) => apply arm_CODELENS_aty; aty_state
  | |- ATYr (lenlens_while1 _ _) => apply lenlens_while1_aty; aty_state
  | |- ATYr (lenlens_while2 _ _) => apply lenlens_while2_aty; aty_state
  | |- ATYr (arm_LENLENS _ _ _) => apply arm_LENLENS_aty; aty_state
  | |- ATYr (arm_TABLE _ _ _) => apply arm_TABLE_aty; aty_state
  | |- ATYr (arm_COPY _) => apply arm_COPY_aty; aty_state
  | |- ATYr (arm_COPY_ _) => apply arm_COPY__aty; aty_state
  | |- ATYr (arm_STORED _ _ _) => apply arm_STORED_aty; aty_state
  | |- ATYr (arm_TYPEDO _ _ _) => apply arm_TYPEDO_aty; aty_state
  | |- ATYr (arm_TYPE _ _ _) => apply arm_TYPE_aty; aty_state
  | |- ATYr (arm_DICT _ _ _) => apply arm_DICT_aty; aty_state
  | |- ATYr (arm_DICTID _ _ _) => apply arm_DICTID_aty; aty_state
  | |- ATYr (arm_HCRC _) => apply arm_HCRC_aty; aty_state
  end.
Lemma name_like_aty : forall f w, ATY (w_s w) -> ATYr (name_like f w).
Proof. intros f w HA. unfold name_like. aty. Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  | |- ATYr (arm_DONE _) => apply arm_DONE_aty; aty_state
  | |- ATYr (arm_LENGTH _) => apply arm_LENGTH_aty; aty_state
  | |- ATYr (arm_CHECK _) => apply arm_CHECK_aty; aty_state
  | |- ATYr (arm_LIT _) => apply arm_LIT_aty; aty_state
  | |- ATYr (arm_MATCH _ _) => apply arm_MATCH_aty; aty_state
  | |- ATYr (arm_DISTEXT _ _) => apply arm_DISTEXT_aty; aty_state
  | |- ATYr (arm_DIST _ _) => apply arm_DIST_aty; aty_state
  | |- ATYr (arm_LENEXT _ _) => apply arm_LENEXT_aty; aty_state
  | |- ATYr (arm_LEN _ _) => apply arm_LEN_aty; aty_state
  | |- ATYr (arm_LEN_ _ _) => apply arm_LEN__aty; aty_state
  | |- ATYr (codelens_body _) => apply codelens_body_aty; aty_state
  | |- ATYr (codelens_while _ _) => apply codelens_while_aty; aty_state
  | |- ATYr (arm_CODELENS _ _ _) => apply arm_CODELENS_aty; aty_state
  | |- ATYr (lenlens_while1 _ _) => apply lenlens_while1_aty; aty_state
  | |- ATYr (lenlens_while2 _ _) => apply lenlens_while2_aty; aty_state
  | |- ATYr (arm_LENLENS _ _ _) => apply arm_LENLENS_aty; aty_state
  | |- ATYr (arm_TABLE _ _ _) => apply arm_TABLE_aty; aty_state
  | |- ATYr (arm_COPY _) => apply arm_COPY_aty; aty_state
  | |- ATYr (arm_COPY_ _) => apply arm_COPY__aty; aty_state
  | |- ATYr (arm_STORED _ _ _) => apply arm_STORED_aty; aty_state
  | |- ATYr (arm_TYPEDO _ _ _) => apply arm_TYPEDO_aty; aty_state
  | |- ATYr (arm_TYPE _ _ _) => apply arm_TYPE_aty; aty_state
  | |- ATYr (arm_DICT _ _ _) => apply arm_DICT_aty; aty_state
  | |- ATYr (arm_DICTID _ _ _) => apply arm_DICTID_aty; aty_state
  | |- ATYr (arm_HCRC _) => apply arm_HCRC_aty; aty_state
  | |- ATYr (name_like _ _) => apply name_like_aty; aty_state
  end.
Lemma arm_COMMENT_aty : forall w, ATY (w_s w) -> ATYr (arm_COMMENT w).
Proof. intros w HA. unfold arm_COMMENT. aty. Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  | |- ATYr (arm_DONE _) => apply arm_DONE_aty; aty_state
  | |- ATYr (arm_LENGTH _) => apply arm_LENGTH_aty; aty_state
  | |- ATYr (arm_CHECK _) => apply arm_CHECK_aty; aty_state
  | |- ATYr (arm_LIT _) => apply arm_LIT_aty; aty_state
  | |- ATYr (arm_MATCH _ _) => apply arm_MATCH_aty; aty_state
  | |- ATYr (arm_DISTEXT _ _) => apply arm_DISTEXT_aty; aty_state
  | |- ATYr (arm_DIST _ _) => apply arm_DIST_aty; aty_state
  | |- ATYr (arm_LENEXT _ _) => apply arm_LENEXT_aty; aty_state
  | |- ATYr (arm_LEN _ _) => apply arm_LEN_aty; aty_state
  | |- ATYr (arm_LEN_ _ _) => apply arm_LEN__aty; aty_state
  | |- ATYr (codelens_body _) => apply codelens_body_aty; aty_state
  | |- ATYr (codelens_while _ _) => apply codelens_while_aty; aty_state
  | |- ATYr (arm_CODELENS _ _ _) => apply arm_CODELENS_aty; aty_state
  | |- ATYr (lenlens_while1 _ _) => apply lenlens_while1_aty; aty_state
  | |- ATYr (lenlens_while2 _ _) => apply lenlens_while2_aty; aty_state
  | |- ATYr (arm_LENLENS _ _ _) => apply arm_LENLENS_aty; aty_state
  | |- ATYr (arm_TABLE _ _ _) => apply arm_TABLE_aty; aty_state
  | |- ATYr (arm_COPY _) => apply arm_COPY_aty; aty_state
  | |- ATYr (arm_COPY_ _) => apply arm_COPY__aty; aty_state
  | |- ATYr (arm_STORED _ _ _) => apply arm_STORED_aty; aty_state
  | |- ATYr (arm_TYPEDO _ _ _) => apply arm_TYPEDO_aty; aty_state
  | |- ATYr (arm_TYPE _ _ _) => apply arm_TYPE_aty; aty_state
  | |- ATYr (arm_DICT _ _ _) => apply arm_DICT_aty; aty_state
  | |- ATYr (arm_DICTID _ _ _) => apply arm_DICTID_aty; aty_state
  | |- ATYr (arm_HCRC _) => apply arm_HCRC_aty; aty_state
  | |- ATYr (name_like _ _) => apply name_like_aty; aty_state
  | |- ATYr (arm_COMMENT _) => apply arm_COMMENT_aty; aty_state
  end.
Lemma arm_NAME_aty : forall w, ATY (w_s w) -> ATYr (arm_NAME w).
Proof. intros w HA. unfold arm_NAME. aty. Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  | |- ATYr (arm_DONE _) => apply arm_DONE_aty; aty_state
  | |- ATYr (arm_LENGTH _) => apply arm_LENGTH_aty; aty_state
  | |- ATYr (arm_CHECK _) => apply arm_CHECK_aty; aty_state
  | |- ATYr (arm_LIT _) => apply arm_LIT_aty; aty_state
  | |- ATYr (arm_MATCH _ _) => apply arm_MATCH_aty; aty_state
  | |- ATYr (arm_DISTEXT _ _) => apply arm_DISTEXT_aty; aty_state
  | |- ATYr (arm_DIST _ _) => apply arm_DIST_aty; aty_state
  | |- ATYr (arm_LENEXT _ _) => apply arm_LENEXT_aty; aty_state
  | |- ATYr (arm_LEN _ _) => apply arm_LEN_aty; aty_state
  | |- ATYr (arm_LEN_ _ _) => apply arm_LEN__aty; aty_state
  | |- ATYr (codelens_body _) => apply codelens_body_aty; aty_state
  | |- ATYr (codelens_while _ _) => apply codelens_while_aty; aty_state
  | |- ATYr (arm_CODELENS _ _ _) => apply arm_CODELENS_aty; aty_state
  | |- ATYr (lenlens_while1 _ _) => apply lenlens_while1_aty; aty_state
  | |- ATYr (lenlens_while2 _ _) => apply lenlens_while2_aty; aty_state
  | |- ATYr (arm_LENLENS _ _ _) => apply arm_LENLENS_aty; aty_state
  | |- ATYr (arm_TABLE _ _ _) => apply arm_TABLE_aty; aty_state
  | |- ATYr (arm_COPY _) => apply arm_COPY_aty; aty_state
  | |- ATYr (arm_COPY_ _) => apply arm_COPY__aty; aty_state
  | |- ATYr (arm_STORED _ _ _) => apply arm_STORED_aty; aty_state
  | |- ATYr (arm_TYPEDO _ _ _) => apply arm_TYPEDO_aty; aty_state
  | |- ATYr (arm_TYPE _ _ _) => apply arm_TYPE_aty; aty_state
  | |- ATYr (arm_DICT _ _ _) => apply arm_DICT_aty; aty_state
  | |- ATYr (arm_DICTID _ _ _) => apply arm_DICTID_aty; aty_state
  | |- ATYr (arm_HCRC _) => apply arm_HCRC_aty; aty_state
  | |- ATYr (name_like _ _) => apply name_like_aty; aty_state
  | |- ATYr (arm_COMMENT _) => apply arm_COMMENT_aty; aty_state
  | |- ATYr (arm_NAME _) => apply arm_NAME_aty; aty_state
  end.
Lemma arm_EXTRA_aty : forall w, ATY (w_s w) -> ATYr (arm_EXTRA w).
Proof. intros w HA. unfold arm_EXTRA. aty. Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  | |- ATYr (arm_DONE _) => apply arm_DONE_aty; aty_state
  | |- ATYr (arm_LENGTH _) => apply arm_LENGTH_aty; aty_state
  | |- ATYr (arm_CHECK _) => apply arm_CHECK_aty; aty_state
  | |- ATYr (arm_LIT _) => apply arm_LIT_aty; aty_state
  | |- ATYr (arm_MATCH _ _) => apply arm_MATCH_aty; aty_state
  | |- ATYr (arm_DISTEXT _ _) => apply arm_DISTEXT_aty; aty_state
  | |- ATYr (arm_DIST _ _) => apply arm_DIST_aty; aty_state
  | |- ATYr (arm_LENEXT _ _) => apply arm_LENEXT_aty; aty_state
  | |- ATYr (arm_LEN _ _) => apply arm_LEN_aty; aty_state
  | |- ATYr (arm_LEN_ _ _) => apply arm_LEN__aty; aty_state
  | |- ATYr (codelens_body _) => apply codelens_body_aty; aty_state
  | |- ATYr (codelens_while _ _) => apply codelens_while_aty; aty_state
  | |- ATYr (arm_CODELENS _ _ _) => apply arm_CODELENS_aty; aty_state
  | |- ATYr (lenlens_while1 _ _) => apply lenlens_while1_aty; aty_state
  | |- ATYr (lenlens_while2 _ _) => apply lenlens_while2_aty; aty_state
  | |- ATYr (arm_LENLENS _ _ _) => apply arm_LENLENS_aty; aty_state
  | |- ATYr (arm_TABLE _ _ _) => apply arm_TABLE_aty; aty_state
  | |- ATYr (arm_COPY _) => apply arm_COPY_aty; aty_state
  | |- ATYr (arm_COPY_ _) => apply arm_COPY__aty; aty_state
  | |- ATYr (arm_STORED _ _ _) => apply arm_STORED_aty; aty_state
  | |- ATYr (arm_TYPEDO _ _ _) => apply arm_TYPEDO_aty; aty_state
  | |- ATYr (arm_TYPE _ _ _) => apply arm_TYPE_aty; aty_state
  | |- ATYr (arm_DICT _ _ _) => apply arm_DICT_aty; aty_state
  | |- ATYr (arm_DICTID _ _ _) => apply arm_DICTID_aty; aty_state
  | |- ATYr (arm_HCRC _) => apply arm_HCRC_aty; aty_state
  | |- ATYr (name_like _ _) => apply name_like_aty; aty_state
  | |- ATYr (arm_COMMENT _) => apply arm_COMMENT_aty; aty_state
  | |- ATYr (arm_NAME _) => apply arm_NAME_aty; aty_state
  | |- ATYr (arm_EXTRA _) => apply arm_EXTRA_aty; aty_state
  end.
Lemma arm_EXLEN_aty : forall w, ATY (w_s w) -> ATYr (arm_EXLEN w).
Proof. intros w HA. unfold arm_EXLEN. aty. Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  | |- ATYr (arm_DONE _) => apply arm_DONE_aty; aty_state
  | |- ATYr (arm_LENGTH _) => apply arm_LENGTH_aty; aty_state
  | |- ATYr (arm_CHECK _) => apply arm_CHECK_aty; aty_state
  | |- ATYr (arm_LIT _) => apply arm_LIT_aty; aty_state
  | |- ATYr (arm_MATCH _ _) => apply arm_MATCH_aty; aty_state
  | |- ATYr (arm_DISTEXT _ _) => apply arm_DISTEXT_aty; aty_state
  | |- ATYr (arm_DIST _ _) => apply arm_DIST_aty; aty_state
  | |- ATYr (arm_LENEXT _ _) => apply arm_LENEXT_aty; aty_state
  | |- ATYr (arm_LEN _ _) => apply arm_LEN_aty; aty_state
  | |- ATYr (arm_LEN_ _ _) => apply arm_LEN__aty; aty_state
  | |- ATYr (codelens_body _) => apply codelens_body_aty; aty_state
  | |- ATYr (codelens_while _ _) => apply codelens_while_aty; aty_state
  | |- ATYr (arm_CODELENS _ _ _) => apply arm_CODELENS_aty; aty_state
  | |- ATYr (lenlens_while1 _ _) => apply lenlens_while1_aty; aty_state
  | |- ATYr (lenlens_while2 _ _) => apply lenlens_while2_aty; aty_state
  | |- ATYr (arm_LENLENS _ _ _) => apply arm_LENLENS_aty; aty_state
  | |- ATYr (arm_TABLE _ _ _) => apply arm_TABLE_aty; aty_state
  | |- ATYr (arm_COPY _) => apply arm_COPY_aty; aty_state
  | |- ATYr (arm_COPY_ _) => apply arm_COPY__aty; aty_state
  | |- ATYr (arm_STORED _ _ _) => apply arm_STORED_aty; aty_state
  | |- ATYr (arm_TYPEDO _ _ _) => apply arm_TYPEDO_aty; aty_state
  | |- ATYr (arm_TYPE _ _ _) => apply arm_TYPE_aty; aty_state
  | |- ATYr (arm_DICT _ _ _) => apply arm_DICT_aty; aty_state
  | |- ATYr (arm_DICTID _ _ _) => apply arm_DICTID_aty; aty_state
  | |- ATYr (arm_HCRC _) => apply arm_HCRC_aty; aty_state
  | |- ATYr (name_like _ _) => apply name_like_aty; aty_state
  | |- ATYr (arm_COMMENT _) => apply arm_COMMENT_aty; aty_state
  | |- ATYr (arm_NAME _) => apply arm_NAME_aty; aty_state
  | |- ATYr (arm_EXTRA _) => apply arm_EXTRA_aty; aty_state
  | |- ATYr (arm_EXLEN _) => apply arm_EXLEN_aty; aty_state
  end.
Lemma arm_OS_aty : forall w, ATY (w_s w) -> ATYr (arm_OS w).
Proof. intros w HA. unfold arm_OS. aty. Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  | |- ATYr (arm_DONE _) => apply arm_DONE_aty; aty_state
  | |- ATYr (arm_LENGTH _) => apply arm_LENGTH_aty; aty_state
  | |- ATYr (arm_CHECK _) => apply arm_CHECK_aty; aty_state
  | |- ATYr (arm_LIT _) => apply arm_LIT_aty; aty_state
  | |- ATYr (arm_MATCH _ _) => apply arm_MATCH_aty; aty_state
  | |- ATYr (arm_DISTEXT _ _) => apply arm_DISTEXT_aty; aty_state
  | |- ATYr (arm_DIST _ _) => apply arm_DIST_aty; aty_state
  | |- ATYr (arm_LENEXT _ _) => apply arm_LENEXT_aty; aty_state
  | |- ATYr (arm_LEN _ _) => apply arm_LEN_aty; aty_state
  | |- ATYr (arm_LEN_ _ _) => apply arm_LEN__aty; aty_state
  | |- ATYr (codelens_body _) => apply codelens_body_aty; aty_state
  | |- ATYr (codelens_while _ _) => apply codelens_while_aty; aty_state
  | |- ATYr (arm_CODELENS _ _ _) => apply arm_CODELENS_aty; aty_state
  | |- ATYr (lenlens_while1 _ _) => apply lenlens_while1_aty; aty_state
  | |- ATYr (lenlens_while2 _ _) => apply lenlens_while2_aty; aty_state
  | |- ATYr (arm_LENLENS _ _ _) => apply arm_LENLENS_aty; aty_state
  | |- ATYr (arm_TABLE _ _ _) => apply arm_TABLE_aty; aty_state
  | |- ATYr (arm_COPY _) => apply arm_COPY_aty; aty_state
  | |- ATYr (arm_COPY_ _) => apply arm_COPY__aty; aty_state
  | |- ATYr (arm_STORED _ _ _) => apply arm_STORED_aty; aty_state
  | |- ATYr (arm_TYPEDO _ _ _) => apply arm_TYPEDO_aty; aty_state
  | |- ATYr (arm_TYPE _ _ _) => apply arm_TYPE_aty; aty_state
  | |- ATYr (arm_DICT _ _ _) => apply arm_DICT_aty; aty_state
  | |- ATYr (arm_DICTID _ _ _) => apply arm_DICTID_aty; aty_state
  | |- ATYr (arm_HCRC _) => apply arm_HCRC_aty; aty_state
  | |- ATYr (name_like _ _) => apply name_like_aty; aty_state
  | |- ATYr (arm_COMMENT _) => apply arm_COMMENT_aty; aty_state
  | |- ATYr (arm_NAME _) => apply arm_NAME_aty; aty_state
  | |- ATYr (arm_EXTRA _) => apply arm_EXTRA_aty; aty_state
  | |- ATYr (arm_EXLEN _) => apply arm_EXLEN_aty; aty_state
  | |- ATYr (arm_OS _) => apply arm_OS_aty; aty_state
  end.
Lemma arm_TIME_aty : forall w, ATY (w_s w) -> ATYr (arm_TIME w).
Proof. intros w HA. unfold arm_TIME. aty. Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  | |- ATYr (arm_DONE _) => apply arm_DONE_aty; aty_state
  | |- ATYr (arm_LENGTH _) => apply arm_LENGTH_aty; aty_state
  | |- ATYr (arm_CHECK _) => apply arm_CHECK_aty; aty_state
  | |- ATYr (arm_LIT _) => apply arm_LIT_aty; aty_state
  | |- ATYr (arm_MATCH _ _) => apply arm_MATCH_aty; aty_state
  | |- ATYr (arm_DISTEXT _ _) => apply arm_DISTEXT_aty; aty_state
  | |- ATYr (arm_DIST _ _) => apply arm_DIST_aty; aty_state
  | |- ATYr (arm_LENEXT _ _) => apply arm_LENEXT_aty; aty_state
  | |- ATYr (arm_LEN _ _) => apply arm_LEN_aty; aty_state
  | |- ATYr (arm_LEN_ _ _) => apply arm_LEN__aty; aty_state
  | |- ATYr (codelens_body _) => apply codelens_body_aty; aty_state
  | |- ATYr (codelens_while _ _) => apply codelens_while_aty; aty_state
  | |- ATYr (arm_CODELENS _ _ _) => apply arm_CODELENS_aty; aty_state
  | |- ATYr (lenlens_while1 _ _) => apply lenlens_while1_aty; aty_state
  | |- ATYr (lenlens_while2 _ _) => apply lenlens_while2_aty; aty_state
  | |- ATYr (arm_LENLENS _ _ _) => apply arm_LENLENS_aty; aty_state
  | |- ATYr (arm_TABLE _ _ _) => apply arm_TABLE_aty; aty_state
  | |- ATYr (arm_COPY _) => apply arm_COPY_aty; aty_state
  | |- ATYr (arm_COPY_ _) => apply arm_COPY__aty; aty_state
  | |- ATYr (arm_STORED _ _ _) => apply arm_STORED_aty; aty_state
  | |- ATYr (arm_TYPEDO _ _ _) => apply arm_TYPEDO_aty; aty_state
  | |- ATYr (arm_TYPE _ _ _) => apply arm_TYPE_aty; aty_state
  | |- ATYr (arm_DICT _ _ _) => apply arm_DICT_aty; aty_state
  | |- ATYr (arm_DICTID _ _ _) => apply arm_DICTID_aty; aty_state
  | |- ATYr (arm_HCRC _) => apply arm_HCRC_aty; aty_state
  | |- ATYr (name_like _ _) => apply name_like_aty; aty_state
  | |- ATYr (arm_COMMENT _) => apply arm_COMMENT_aty; aty_state
  | |- ATYr (arm_NAME _) => apply arm_NAME_aty; aty_state
  | |- ATYr (arm_EXTRA _) => apply arm_EXTRA_aty; aty_state
  | |- ATYr (arm_EXLEN _) => apply arm_EXLEN_aty; aty_state
  | |- ATYr (arm_OS _) => apply arm_OS_aty; aty_state
  | |- ATYr (arm_TIME _) => apply arm_TIME_aty; aty_state
  end.
Lemma arm_FLAGS_aty : forall w, ATY (w_s w) -> ATYr (arm_FLAGS w).
Proof. intros w HA. unfold arm_FLAGS. aty. Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  | |- ATYr (arm_DONE _) => apply arm_DONE_aty; aty_state
  | |- ATYr (arm_LENGTH _) => apply arm_LENGTH_aty; aty_state
  | |- ATYr (arm_CHECK _) => apply arm_CHECK_aty; aty_state
  | |- ATYr (arm_LIT _) => apply arm_LIT_aty; aty_state
  | |- ATYr (arm_MATCH _ _) => apply arm_MATCH_aty; aty_state
  | |- ATYr (arm_DISTEXT _ _) => apply arm_DISTEXT_aty; aty_state
  | |- ATYr (arm_DIST _ _) => apply arm_DIST_aty; aty_state
  | |- ATYr (arm_LENEXT _ _) => apply arm_LENEXT_aty; aty_state
  | |- ATYr (arm_LEN _ _) => apply arm_LEN_aty; aty_state
  | |- ATYr (arm_LEN_ _ _) => apply arm_LEN__aty; aty_state
  | |- ATYr (codelens_body _) => apply codelens_body_aty; aty_state
  | |- ATYr (codelens_while _ _) => apply codelens_while_aty; aty_state
  | |- ATYr (arm_CODELENS _ _ _) => apply arm_CODELENS_aty; aty_state
  | |- ATYr (lenlens_while1 _ _) => apply lenlens_while1_aty; aty_state
  | |- ATYr (lenlens_while2 _ _) => apply lenlens_while2_aty; aty_state
  | |- ATYr (arm_LENLENS _ _ _) => apply arm_LENLENS_aty; aty_state
  | |- ATYr (arm_TABLE _ _ _) => apply arm_TABLE_aty; aty_state
  | |- ATYr (arm_COPY _) => apply arm_COPY_aty; aty_state
  | |- ATYr (arm_COPY_ _) => apply arm_COPY__aty; aty_state
  | |- ATYr (arm_STORED _ _ _) => apply arm_STORED_aty; aty_state
  | |- ATYr (arm_TYPEDO _ _ _) => apply arm_TYPEDO_aty; aty_state
  | |- ATYr (arm_TYPE _ _ _) => apply arm_TYPE_aty; aty_state
  | |- ATYr (arm_DICT _ _ _) => apply arm_DICT_aty; aty_state
  | |- ATYr (arm_DICTID _ _ _) => apply arm_DICTID_aty; aty_state
  | |- ATYr (arm_HCRC _) => apply arm_HCRC_aty; aty_state
  | |- ATYr (name_like _ _) => apply name_like_aty; aty_state
  | |- ATYr (arm_COMMENT _) => apply arm_COMMENT_aty; aty_state
  | |- ATYr (arm_NAME _) => apply arm_NAME_aty; aty_state
  | |- ATYr (arm_EXTRA _) => apply arm_EXTRA_aty; aty_state
  | |- ATYr (arm_EXLEN _) => apply arm_EXLEN_aty; aty_state
  | |- ATYr (arm_OS _) => apply arm_OS_aty; aty_state
  | |- ATYr (arm_TIME _) => apply arm_TIME_aty; aty_state
  | |- ATYr (arm_FLAGS _) => apply arm_FLAGS_aty; aty_state
  end.
Lemma arm_HEAD_aty : forall iv w, ATY (w_s w) -> ATYr (arm_HEAD iv w).
Proof. intros iv w HA. unfold arm_HEAD. aty. Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  | |- ATYr (arm_DONE _) => apply arm_DONE_aty; aty_state
  | |- ATYr (arm_LENGTH _) => apply arm_LENGTH_aty; aty_state
  | |- ATYr (arm_CHECK _) => apply arm_CHECK_aty; aty_state
  | |- ATYr (arm_LIT _) => apply arm_LIT_aty; aty_state
  | |- ATYr (arm_MATCH _ _) => apply arm_MATCH_aty; aty_state
  | |- ATYr (arm_DISTEXT _ _) => apply arm_DISTEXT_aty; aty_state
  | |- ATYr (arm_DIST _ _) => apply arm_DIST_aty; aty_state
  | |- ATYr (arm_LENEXT _ _) => apply arm_LENEXT_aty; aty_state
  | |- ATYr (arm_LEN _ _) => apply arm_LEN_aty; aty_state
  | |- ATYr (arm_LEN_ _ _) => apply arm_LEN__aty; aty_state
  | |- ATYr (codelens_body _) => apply codelens_body_aty; aty_state
  | |- ATYr (codelens_while _ _) => apply codelens_while_aty; aty_state
  | |- ATYr (arm_CODELENS _ _ _) => apply arm_CODELENS_aty; aty_state
  | |- ATYr (lenlens_while1 _ _) => apply lenlens_while1_aty; aty_state
  | |- ATYr (lenlens_while2 _ _) => apply lenlens_while2_aty; aty_state
  | |- ATYr (arm_LENLENS _ _ _) => apply arm_LENLENS_aty; aty_state
  | |- ATYr (arm_TABLE _ _ _) => apply arm_TABLE_aty; aty_state
  | |- ATYr (arm_COPY _) => apply arm_COPY_aty; aty_state
  | |- ATYr (arm_COPY_ _) => apply arm_COPY__aty; aty_state
  | |- ATYr (arm_STORED _ _ _) => apply arm_STORED_aty; aty_state
  | |- ATYr (arm_TYPEDO _ _ _) => apply arm_TYPEDO_aty; aty_state
  | |- ATYr (arm_TYPE _ _ _) => apply arm_TYPE_aty; aty_state
  | |- ATYr (arm_DICT _ _ _) => apply arm_DICT_aty; aty_state
  | |- ATYr (arm_DICTID _ _ _) => apply arm_DICTID_aty; aty_state
  | |- ATYr (arm_HCRC _) => apply arm_HCRC_aty; aty_state
  | |- ATYr (name_like _ _) => apply name_like_aty; aty_state
  | |- ATYr (arm_COMMENT _) => apply arm_COMMENT_aty; aty_state
  | |- ATYr (arm_NAME _) => apply arm_NAME_aty; aty_state
  | |- ATYr (arm_EXTRA _) => apply arm_EXTRA_aty; aty_state
  | |- ATYr (arm_EXLEN _) => apply arm_EXLEN_aty; aty_state
  | |- ATYr (arm_OS _) => apply arm_OS_aty; aty_state
  | |- ATYr (arm_TIME _) => apply arm_TIME_aty; aty_state
  | |- ATYr (arm_FLAGS _) => apply arm_FLAGS_aty; aty_state
  | |- ATYr (arm_HEAD _ _) => apply arm_HEAD_aty; aty_state
  end.
Lemma arm_BAD_aty : forall w, ATY (w_s w) -> ATYr (arm_BAD w).
Proof. intros w HA. unfold arm_BAD. aty. Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  | |- ATYr (arm_DONE _) => apply arm_DONE_aty; aty_state
  | |- ATYr (arm_LENGTH _) => apply arm_LENGTH_aty; aty_state
  | |- ATYr (arm_CHECK _) => apply arm_CHECK_aty; aty_state
  | |- ATYr (arm_LIT _) => apply arm_LIT_aty; aty_state
  | |- ATYr (arm_MATCH _ _) => apply arm_MATCH_aty; aty_state
  | |- ATYr (arm_DISTEXT _ _) => apply arm_DISTEXT_aty; aty_state
  | |- ATYr (arm_DIST _ _) => apply arm_DIST_aty; aty_state
  | |- ATYr (arm_LENEXT _ _) => apply arm_LENEXT_aty; aty_state
  | |- ATYr (arm_LEN _ _) => apply arm_LEN_aty; aty_state
  | |- ATYr (arm_LEN_ _ _) => apply arm_LEN__aty; aty_state
  | |- ATYr (codelens_body _) => apply codelens_body_aty; aty_state
  | |- ATYr (codelens_while _ _) => apply codelens_while_aty; aty_state
  | |- ATYr (arm_CODELENS _ _ _) => apply arm_CODELENS_aty; aty_state
  | |- ATYr (lenlens_while1 _ _) => apply lenlens_while1_aty; aty_state
  | |- ATYr (lenlens_while2 _ _) => apply lenlens_while2_aty; aty_state
  | |- ATYr (arm_LENLENS _ _ _) => apply arm_LENLENS_aty; aty_state
  | |- ATYr (arm_TABLE _ _ _) => apply arm_TABLE_aty; aty_state
  | |- ATYr (arm_COPY _) => apply arm_COPY_aty; aty_state
  | |- ATYr (arm_COPY_ _) => apply arm_COPY__aty; aty_state
  | |- ATYr (arm_STORED _ _ _) => apply arm_STORED_aty; aty_state
  | |- ATYr (arm_TYPEDO _ _ _) => apply arm_TYPEDO_aty; aty_state
  | |- ATYr (arm_TYPE _ _ _) => apply arm_TYPE_aty; aty_state
  | |- ATYr (arm_DICT _ _ _) => apply arm_DICT_aty; aty_state
  | |- ATYr (arm_DICTID _ _ _) => apply arm_DICTID_aty; aty_state
  | |- ATYr (arm_HCRC _) => apply arm_HCRC_aty; aty_state
  | |- ATYr (name_like _ _) => apply name_like_aty; aty_state
  | |- ATYr (arm_COMMENT _) => apply arm_COMMENT_aty; aty_state
  | |- ATYr (arm_NAME _) => apply arm_NAME_aty; aty_state
  | |- ATYr (arm_EXTRA _) => apply arm_EXTRA_aty; aty_state
  | |- ATYr (arm_EXLEN _) => apply arm_EXLEN_aty; aty_state
  | |- ATYr (arm_OS _) => apply arm_OS_aty; aty_state
  | |- ATYr (arm_TIME _) => apply arm_TIME_aty; aty_state
  | |- ATYr (arm_FLAGS _) => apply arm_FLAGS_aty; aty_state
  | |- ATYr (arm_HEAD _ _) => apply arm_HEAD_aty; aty_state
  | |- ATYr (arm_BAD _) => apply arm_BAD_aty; aty_state
  end.
Lemma arm_MEM_aty : forall w, ATY (w_s w) -> ATYr (arm_MEM w).
Proof. intros w HA. unfold arm_MEM. aty. Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  | |- ATYr (arm_DONE _) => apply arm_DONE_aty; aty_state
  | |- ATYr (arm_LENGTH _) => apply arm_LENGTH_aty; aty_state
  | |- ATYr (arm_CHECK _) => apply arm_CHECK_aty; aty_state
  | |- ATYr (arm_LIT _) => apply arm_LIT_aty; aty_state
  | |- ATYr (arm_MATCH _ _) => apply arm_MATCH_aty; aty_state
  | |- ATYr (arm_DISTEXT _ _) => apply arm_DISTEXT_aty; aty_state
  | |- ATYr (arm_DIST _ _) => apply arm_DIST_aty; aty_state
  | |- ATYr (arm_LENEXT _ _) => apply arm_LENEXT_aty; aty_state
  | |- ATYr (arm_LEN _ _) => apply arm_LEN_aty; aty_state
  | |- ATYr (arm_LEN_ _ _) => apply arm_LEN__aty; aty_state
  | |- ATYr (codelens_body _) => apply codelens_body_aty; aty_state
  | |- ATYr (codelens_while _ _) => apply codelens_while_aty; aty_state
  | |- ATYr (arm_CODELENS _ _ _) => apply arm_CODELENS_aty; aty_state
  | |- ATYr (lenlens_while1 _ _) => apply lenlens_while1_aty; aty_state
  | |- ATYr (lenlens_while2 _ _) => apply lenlens_while2_aty; aty_state
  | |- ATYr (arm_LENLENS _ _ _) => apply arm_LENLENS_aty; aty_state
  | |- ATYr (arm_TABLE _ _ _) => apply arm_TABLE_aty; aty_state
  | |- ATYr (arm_COPY _) => apply arm_COPY_aty; aty_state
  | |- ATYr (arm_COPY_ _) => apply arm_COPY__aty; aty_state
  | |- ATYr (arm_STORED _ _ _) => apply arm_STORED_aty; aty_state
  | |- ATYr (arm_TYPEDO _ _ _) => apply arm_TYPEDO_aty; aty_state
  | |- ATYr (arm_TYPE _ _ _) => apply arm_TYPE_aty; aty_state
  | |- ATYr (arm_DICT _ _ _) => apply arm_DICT_aty; aty_state
  | |- ATYr (arm_DICTID _ _ _) => apply arm_DICTID_aty; aty_state
  | |- ATYr (arm_HCRC _) => apply arm_HCRC_aty; aty_state
  | |- ATYr (name_like _ _) => apply name_like_aty; aty_state
  | |- ATYr (arm_COMMENT _) => apply arm_COMMENT_aty; aty_state
  | |- ATYr (arm_NAME _) => apply arm_NAME_aty; aty_state
  | |- ATYr (arm_EXTRA _) => apply arm_EXTRA_aty; aty_state
  | |- ATYr (arm_EXLEN _) => apply arm_EXLEN_aty; aty_state
  | |- ATYr (arm_OS _) => apply arm_OS_aty; aty_state
  | |- ATYr (arm_TIME _) => apply arm_TIME_aty; aty_state
  | |- ATYr (arm_FLAGS _) => apply arm_FLAGS_aty; aty_state
  | |- ATYr (arm_HEAD _ _) => apply arm_HEAD_aty; aty_state
  | |- ATYr (arm_BAD _) => apply arm_BAD_aty; aty_state
  | |- ATYr (arm_MEM _) => apply arm_MEM_aty; aty_state
  end.
Lemma arm_SYNC_aty : forall w, ATY (w_s w) -> ATYr (arm_SYNC w).
Proof. intros w HA. unfold arm_SYNC. aty. Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  | |- ATYr (arm_DONE _) => apply arm_DONE_aty; aty_state
  | |- ATYr (arm_LENGTH _) => apply arm_LENGTH_aty; aty_state
  | |- ATYr (arm_CHECK _) => apply arm_CHECK_aty; aty_state
  | |- ATYr (arm_LIT _) => apply arm_LIT_aty; aty_state
  | |- ATYr (arm_MATCH _ _) => apply arm_MATCH_aty; aty_state
  | |- ATYr (arm_DISTEXT _ _) => apply arm_DISTEXT_aty; aty_state
  | |- ATYr (arm_DIST _ _) => apply arm_DIST_aty; aty_state
  | |- ATYr (arm_LENEXT _ _) => apply arm_LENEXT_aty; aty_state
  | |- ATYr (arm_LEN _ _) => apply arm_LEN_aty; aty_state
  | |- ATYr (arm_LEN_ _ _) => apply arm_LEN__aty; aty_state
  | |- ATYr (codelens_body _) => apply codelens_body_aty; aty_state
  | |- ATYr (codelens_while _ _) => apply codelens_while_aty; aty_state
  | |- ATYr (arm_CODELENS _ _ _) => apply arm_CODELENS_aty; aty_state
  | |- ATYr (lenlens_while1 _ _) => apply lenlens_while1_aty; aty_state
  | |- ATYr (lenlens_while2 _ _) => apply lenlens_while2_aty; aty_state
  | |- ATYr (arm_LENLENS _ _ _) => apply arm_LENLENS_aty; aty_state
  | |- ATYr (arm_TABLE _ _ _) => apply arm_TABLE_aty; aty_state
  | |- ATYr (arm_COPY _) => apply arm_COPY_aty; aty_state
  | |- ATYr (arm_COPY_ _) => apply arm_COPY__aty; aty_state
  | |- ATYr (arm_STORED _ _ _) => apply arm_STORED_aty; aty_state
  | |- ATYr (arm_TYPEDO _ _ _) => apply arm_TYPEDO_aty; aty_state
  | |- ATYr (arm_TYPE _ _ _) => apply arm_TYPE_aty; aty_state
  | |- ATYr (arm_DICT _ _ _) => apply arm_DICT_aty; aty_state
  | |- ATYr (arm_DICTID _ _ _) => apply arm_DICTID_aty; aty_state
  | |- ATYr (arm_HCRC _) => apply arm_HCRC_aty; aty_state
  | |- ATYr (name_like _ _) => apply name_like_aty; aty_state
  | |- ATYr (arm_COMMENT _) => apply arm_COMMENT_aty; aty_state
  | |- ATYr (arm_NAME _) => apply arm_NAME_aty; aty_state
  | |- ATYr (arm_EXTRA _) => apply arm_EXTRA_aty; aty_state
  | |- ATYr (arm_EXLEN _) => apply arm_EXLEN_aty; aty_state
  | |- ATYr (arm_OS _) => apply arm_OS_aty; aty_state
  | |- ATYr (arm_TIME _) => apply arm_TIME_aty; aty_state
  | |- ATYr (arm_FLAGS _) => apply arm_FLAGS_aty; aty_state
  | |- ATYr (arm_HEAD _ _) => apply arm_HEAD_aty; aty_state
  | |- ATYr (arm_BAD _) => apply arm_BAD_aty; aty_state
  | |- ATYr (arm_MEM _) => apply arm_MEM_aty; aty_state
  | |- ATYr (arm_SYNC _) => apply arm_SYNC_aty; aty_state
  end.
Lemma dispatch_aty : forall iv flush w, ATY (w_s w) -> ATYr (dispatch iv flush w).
Proof. intros iv flush w HA. unfold dispatch. aty. Qed.
Ltac aty_known ::=
  lazymatch goal with
  | |- ATYr (NEEDBITS _ _) => apply NEEDBITS_aty; aty_state
  | |- ATYr (DECODE1 _ _ _) => apply DECODE1_aty; aty_state
  | |- ATYr (DECODE2 _ _ _) => apply DECODE2_aty; aty_state
  | |- ATYr (lens_repeat _ _ _) => apply lens_repeat_aty; aty_state
  | |- ATYr (arm_DONE _) => apply arm_DONE_aty; aty_state
  | |- ATYr (arm_LENGTH _) => apply arm_LENGTH_aty; aty_state
  | |- ATYr (arm_CHECK _) => apply arm_CHECK_aty; aty_state
  | |- ATYr (arm_LIT _) => apply arm_LIT_aty; aty_state
  | |- ATYr (arm_MATCH _ _) => apply arm_MATCH_aty; aty_state
  | |- ATYr (arm_DISTEXT _ _) => apply arm_DISTEXT_aty; aty_state
  | |- ATYr (arm_DIST _ _) => apply arm_DIST_aty; aty_state
  | |- ATYr (arm_LENEXT _ _) => apply arm_LENEXT_aty; aty_state
  | |- ATYr (arm_LEN _ _) => apply arm_LEN_aty; aty_state
  | |- ATYr (arm_LEN_ _ _) => apply arm_LEN__aty; aty_state
  | |- ATYr (codelens_body _) => apply codelens_body_aty; aty_state
  | |- ATYr (codelens_while _ _) => apply codelens_while_aty; aty_state
  | |- ATYr (arm_CODELENS _ _ _) => apply arm_CODELENS_aty; aty_state
  | |- ATYr (lenlens_while1 _ _) => apply lenlens_while1_aty; aty_state
  | |- ATYr (lenlens_while2 _ _) => apply lenlens_while2_aty; aty_state
  | |- ATYr (arm_LENLENS _ _ _) => apply arm_LENLENS_aty; aty_state
  | |- ATYr (arm_TABLE _ _ _) => apply arm_TABLE_aty; aty_state
  | |- ATYr (arm_COPY _) => apply arm_COPY_aty; aty_state
  | |- ATYr (arm_COPY_ _) => apply arm_COPY__aty; aty_state
  | |- ATYr (arm_STORED _ _ _) => apply arm_STORED_aty; aty_state
  | |- ATYr (arm_TYPEDO _ _ _) => apply arm_TYPEDO_aty; aty_state
  | |- ATYr (arm_TYPE _ _ _) => apply arm_TYPE_aty; aty_state
  | |- ATYr (arm_DICT _ _ _) => apply arm_DICT_aty; aty_state
  | |- ATYr (arm_DICTID _ _ _) => apply arm_DICTID_aty; aty_state
  | |- ATYr (arm_HCRC _) => apply arm_HCRC_aty; aty_state
  | |- ATYr (name_like _ _) => apply name_like_aty; aty_state
  | |- ATYr (arm_COMMENT _) => apply arm_COMMENT_aty; aty_state
  | |- ATYr (arm_NAME _) => apply arm_NAME_aty; aty_state
  | |- ATYr (arm_EXTRA _) => apply arm_EXTRA_aty; aty_state
  | |- ATYr (arm_EXLEN _) => apply arm_EXLEN_aty; aty_state
  | |- ATYr (arm_OS _) => apply arm_OS_aty; aty_state
  | |- ATYr (arm_TIME _) => apply arm_TIME_aty; aty_state
  | |- ATYr (arm_FLAGS _) => apply arm_FLAGS_aty; aty_state
  | |- ATYr (arm_HEAD _ _) => apply arm_HEAD_aty; aty_state
  | |- ATYr (arm_BAD _) => apply arm_BAD_aty; aty_state
  | |- ATYr (arm_MEM _) => apply arm_MEM_aty; aty_state
  | |- ATYr (arm_SYNC _) => apply arm_SYNC_aty; aty_state
  | |- ATYr (dispatch _ _ _) => apply dispatch_aty; aty_state
  end.
