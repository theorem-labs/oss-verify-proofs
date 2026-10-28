(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bs X1c2.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Fixpoint leaves {R} (t : itree node R) (P : R -> Prop) : Prop :=
match t with
| Ret r => P r
| Vis n k => forall rsp, leaves (k rsp) P
end.

Lemma leaves_mono : forall {R} (t : itree node R) (P P' : R -> Prop), leaves t P -> (forall r, P r -> P' r) -> leaves t P'.
Proof. induction t as [r|n k IH]; intros P P' H HP; cbn in *; [auto|]. intros rsp. eapply IH; eauto. Qed.

Lemma leaves_true : forall {R} (t : itree node R), leaves t (fun _ => True).
Proof. induction t; cbn; auto. Qed.

Lemma leaves_bind : forall {A B} (t : itree node A) (f : A -> itree node B) (P : B -> Prop),
leaves t (fun a => leaves (f a) P) -> leaves (@bind node _ _ t f) P.
Proof. induction t as [r|n k IH]; intros f P H; cbn in *; [exact H|]. intros rsp. apply IH. apply H. Qed.

Definition eleaves {A} (t : itree node (exc A)) (P : A -> Prop) : Prop :=
leaves t (fun e => match e with Ok a => P a | Unr => True end).

Lemma eleaves_ebind : forall {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) (P : B -> Prop),
eleaves t (fun a => eleaves (f a) P) -> eleaves (ebind t f) P.
Proof.
intros A B t f P H. unfold eleaves, ebind in *. apply leaves_bind.
eapply leaves_mono; [exact H|]. intros [|a]; cbn; auto.
Qed.
Lemma eleaves_ret : forall {A} (a : A) (P : A -> Prop), P a -> eleaves (Ret (Ok a)) P.
Proof. intros A a P H. exact H. Qed.
Lemma eleaves_unr : forall {A} (P : A -> Prop), eleaves (Ret (@Unr A)) P.
Proof. intros. exact I. Qed.
Lemma eleaves_mono : forall {A} (t : itree node (exc A)) (P P' : A -> Prop), eleaves t P -> (forall a, P a -> P' a) -> eleaves t P'.
Proof. intros A t P P' H HP. unfold eleaves in *. eapply leaves_mono; [exact H|]. intros [|a]; cbn; auto. Qed.

Section WithSegs.
Context {RCEIL : RunCeiling}.
Variable segs : list Segment.

#[using="Type"] Lemma impl_leaves : forall {R} (t : itree node R) (P : R -> Prop) (Q : R -> machine_state -> Prop) ms,
leaves t P -> impl segs (at_node segs) t Q ms -> impl segs (at_node segs) t (fun r ms' => Q r ms' /\ P r) ms.
Proof.
induction t as [r|n k IH]; intros P Q ms HL H; cbn in *.
- eapply evt_mono; [exact H|]. intros ms' HQ. split; assumption.
- eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. apply IH; auto.
Qed.
#[using="Type"] Lemma implM_leaves : forall {St A} (c : M St A) s (P : A * St -> Prop) Q ms,
eleaves (c s) P -> implM segs c s Q ms -> implM segs c s (fun a s' ms' => Q a s' ms' /\ P (a, s')) ms.
Proof.
intros St A c s P Q ms HL H. unfold implM in *.
eapply impl_mono; [eapply impl_leaves; [exact HL | exact H] |].
intros [|[a s']] ms' [H1 H2]; cbn in *; auto.
Qed.
End WithSegs.

Section MLeaves.
Context {RCEIL : RunCeiling}.
Context {St : Type}.
Definition mleaves {A} (c : M St A) (s : St) (P : A * St -> Prop) : Prop := eleaves (c s) P.

#[using="Type"] Lemma mleaves_bind : forall {A B} (c : M St A) (f : A -> M St B) s (P : B * St -> Prop),
mleaves c s (fun p => mleaves (f (fst p)) (snd p) P) -> mleaves (mbind c f) s P.
Proof. intros A B c f s P H. unfold mleaves, mbind in *. apply eleaves_ebind. exact H. Qed.
#[using="Type"] Lemma mleaves_ret : forall {A} (a : A) s (P : A * St -> Prop), P (a, s) -> mleaves (mret a) s P.
Proof. intros. exact H. Qed.
#[using="Type"] Lemma mleaves_unr : forall {A} s (P : A * St -> Prop), mleaves (@munr St A) s P.
Proof. intros. exact I. Qed.
#[using="Type"] Lemma mleaves_eq : forall {A} (c : M St A) s t (P : A * St -> Prop), c s = t -> eleaves t P -> mleaves c s P.
Proof. intros A c s t P E H. unfold mleaves. rewrite E. exact H. Qed.
#[using="Type"] Lemma mleaves_mono : forall {A} (c : M St A) s (P P' : A * St -> Prop), mleaves c s P -> (forall p, P p -> P' p) -> mleaves c s P'.
Proof. intros A c s P P' H HP. unfold mleaves in *. eapply eleaves_mono; eauto. Qed.

#[using="Type"] Lemma mleaves_seq_any : forall {A B} (c : M St A) (f : A -> M St B) s (P : B * St -> Prop),
(forall a s', mleaves (f a) s' P) -> mleaves (mbind c f) s P.
Proof.
intros A B c f s P H. apply mleaves_bind. unfold mleaves, eleaves.
eapply leaves_mono; [apply leaves_true|]. intros [|[a s']] _; cbn; [exact I| apply H].
Qed.
End MLeaves.

Section BitsSim.
Context {RCEIL : RunCeiling}.
Context {ptr : Type}.
Implicit Types b : bits_st ptr.
Definition bits_sim b b' : Prop :=
sb_owner b' = sb_owner b /\ sb_chars b' = sb_chars b /\ sb_buf_size b' = sb_buf_size b.
#[using="Type"] Lemma bits_sim_refl : forall b, bits_sim b b. Proof. intros; repeat split; reflexivity. Qed.
#[using="Type"] Lemma bits_sim_trans : forall a b c, bits_sim a b -> bits_sim b c -> bits_sim a c.
Proof. intros a b c (A1 & A2 & A3) (B1 & B2 & B3). repeat split; congruence. Qed.
#[using="Type"] Lemma ub_sim : forall b n, bits_sim b (ub b n).
Proof. intros. unfold ub, speex_bits_unpack_unsigned. destruct (_ || _); repeat split; reflexivity. Qed.
#[using="Type"] Lemma adv_sim : forall b n, bits_sim b (speex_bits_advance b n).
Proof. intros. unfold speex_bits_advance. destruct (_ || _); repeat split; reflexivity. Qed.
End BitsSim.

Ltac bsim := first [ apply bits_sim_refl | apply ub_sim | apply adv_sim
| eapply bits_sim_trans; [ | first [apply ub_sim | apply adv_sim] ]; bsim ].

Section BitsSim2.
Context {RCEIL : RunCeiling}.
Context {ptr : Type}.
Implicit Types b : bits_st ptr.
#[using="Type"] Lemma skip_bits_sim : forall b, bits_sim b (skip_bits b).
Proof. intros. unfold skip_bits. bsim. Qed.
#[using="Type"] Lemma user_handler_bits_sim : forall b, bits_sim b (user_handler_bits b).
Proof. intros. unfold user_handler_bits. bsim. Qed.
#[using="Type"] Lemma stereo_handler_bits_sim : forall b, bits_sim b (stereo_handler_bits b).
Proof. intros. unfold stereo_handler_bits. bsim. Qed.
#[using="Type"] Lemma inband_bits_sim : forall sc b, bits_sim b (inband_bits sc b).
Proof.
intros. unfold inband_bits. cbv zeta. destruct (_ && _); [| bsim].
eapply bits_sim_trans; [apply ub_sim | apply stereo_handler_bits_sim].
Qed.
#[using="Type"] Lemma lsp_bits_sim : forall k b, bits_sim b (lsp_bits k b).
Proof. intros. destruct k; cbn [lsp_bits]; bsim. Qed.
#[using="Type"] Lemma ltp_bits_sim : forall k b, bits_sim b (ltp_bits k b).
Proof. intros. destruct k; cbn [ltp_bits]; [bsim|]. unfold ltp3_bits. bsim. Qed.
#[using="Type"] Lemma scb_bits_sim : forall n hs sb b, bits_sim b (scb_bits n hs sb b).
Proof.
induction n as [|n IH]; intros; cbn [scb_bits]; [apply bits_sim_refl|].
eapply bits_sim_trans; [| apply IH]. destruct (negb _); bsim.
Qed.
#[using="Type"] Lemma innov_bits_sim : forall k b, bits_sim b (innov_bits k b).
Proof. intros. destruct k; cbn [innov_bits]; [apply bits_sim_refl | apply scb_bits_sim]. Qed.
#[using="Type"] Lemma hsg_bits_sim : forall sm b, bits_sim b (hsg_bits sm b).
Proof. intros. unfold hsg_bits. destruct (_ =? 3); [bsim|]. destruct (_ =? 1); bsim. Qed.
End BitsSim2.

Section Pure.
Context {RCEIL : RunCeiling}.
Context {St ptr : Type}.
Local Notation unpackM := (@bits_unpack_unsigned_M St ptr).
Implicit Types b : bits_st ptr.

Definition segD_olp (sm : submode) b : Z :=
if negb (sm_lbr_pitch sm =? -1) then uv b 7 + 17 else 0.
Definition segD_b1 (sm : submode) b : bits_st ptr :=
if negb (sm_lbr_pitch sm =? -1) then ub b 7 else b.
Definition segD_b2 (sm : submode) b : bits_st ptr :=
if negb (sm_forced_pitch_gain sm =? 0) then ub (segD_b1 sm b) 4 else segD_b1 sm b.
Definition segD_b3 (sm : submode) b : bits_st ptr := ub (segD_b2 sm b) 5.
Definition segD_st (st : nb_state ptr) (sm : submode) b : nb_state ptr :=
if nb_submodeID st =? 1 then set_nb_dtx_enabled st (if uv (segD_b3 sm b) 4 =? 15 then 1 else 0)
else if 1 <? nb_submodeID st then set_nb_dtx_enabled st 0 else st.
Definition segD_bits (st : nb_state ptr) (sm : submode) b : bits_st ptr :=
if nb_submodeID st =? 1 then ub (segD_b3 sm b) 4 else segD_b3 sm b.

Definition nb_rest (sm : submode) (st1 : nb_state ptr) b : M St (Z * nb_state ptr * bits_st ptr) :=
b <- lsp_unquant unpackM (sm_lsp_unquant sm) b ;;
' (ol_pitch, b0) <- (if negb (sm_lbr_pitch sm =? -1)
then ' (p, b0) <- unpackM b 7 ;; mret (NB_PITCH_START + p, b0)
else mret (0, b)) ;;
b1 <- (if negb (sm_forced_pitch_gain sm =? 0) then ' (_, b1) <- unpackM b0 4 ;; mret b1 else mret b0) ;;
' (_, b2) <- unpackM b1 5 ;;
' (st, b3) <- (if nb_submodeID st1 =? 1
then ' (extra, b3) <- unpackM b2 4 ;;
mret (set_nb_dtx_enabled st1 (if extra =? 15 then 1 else 0), b3)
else mret (st1, b2)) ;;
' (st0, b4) <- nb_decode_subframes unpackM 4 0 sm ol_pitch
(if 1 <? nb_submodeID st then set_nb_dtx_enabled st 0 else st) b3 ;;
mret (0, set_nb_pitch_gain_buf_idx (set_nb_count_lost (set_nb_first st0 0) 0)
(if 2 <? nb_pitch_gain_buf_idx st0 + 1 then 0 else nb_pitch_gain_buf_idx st0 + 1), b4).

Definition nb_rest_pure (sm : submode) (st1 : nb_state ptr) b : option (nb_state ptr * bits_st ptr) :=
let b1 := lsp_bits (sm_lsp_unquant sm) b in
match subframes_pure 4 0 sm (segD_olp sm b1) (segD_st st1 sm b1) (segD_bits st1 sm b1) with
| Some (st3, b3) => Some (nb_end st3, b3)
| None => None
end.

#[using="Type"] Lemma nb_rest_run : forall sm st1 b s,
sm_ltp_unquant sm <> None -> sm_innovation_unquant sm <> None ->
nb_rest sm st1 b s = match nb_rest_pure sm st1 b with
| Some (st', b') => Ret (Ok ((0, st', b'), s))
| None => Ret Unr
end.
Proof.
intros sm st1 b s HK HI. unfold nb_rest, nb_rest_pure.
unfold mbind at 1. rewrite lsp_unquant_run, ebind_ret_ok. cbn [fst snd].
set (b1 := lsp_bits (sm_lsp_unquant sm) b). clearbody b1.
unfold mbind at 1.
assert (H1 : (if negb (sm_lbr_pitch sm =? -1) then ' (p, b0) <- unpackM b1 7 ;; mret (NB_PITCH_START + p, b0) else mret (0, b1)) s
= Ret (Ok ((segD_olp sm b1, segD_b1 sm b1), s))).
{ unfold segD_olp, segD_b1. destruct (negb (sm_lbr_pitch sm =? -1)); [| reflexivity].
unfold bits_unpack_unsigned_M, mbind, mret. rewrite unpack_eta, ebind_ret_ok. cbn [fst snd].
rewrite (Z.add_comm NB_PITCH_START). reflexivity. }
rewrite H1, ebind_ret_ok. cbn [fst snd]. clear H1.
unfold mbind at 1.
assert (H2 : (if negb (sm_forced_pitch_gain sm =? 0) then ' (_, b0) <- unpackM (segD_b1 sm b1) 4 ;; mret b0 else mret (segD_b1 sm b1)) s
= Ret (Ok (segD_b2 sm b1, s))).
{ unfold segD_b2. destruct (negb (sm_forced_pitch_gain sm =? 0)); [| reflexivity].
unfold bits_unpack_unsigned_M, mbind, mret. rewrite unpack_eta, ebind_ret_ok. reflexivity. }
rewrite H2, ebind_ret_ok. clear H2.
unfold mbind at 1. unfold bits_unpack_unsigned_M at 1. unfold mret at 1. rewrite unpack_eta, ebind_ret_ok. cbn [fst snd].
fold (segD_b3 sm b1).
unfold mbind at 1.
assert (H3 : (if nb_submodeID st1 =? 1
then ' (extra, b3) <- unpackM (segD_b3 sm b1) 4 ;; mret (set_nb_dtx_enabled st1 (if extra =? 15 then 1 else 0), b3)
else mret (st1, segD_b3 sm b1)) s
= Ret (Ok ((if nb_submodeID st1 =? 1 then (set_nb_dtx_enabled st1 (if uv (segD_b3 sm b1) 4 =? 15 then 1 else 0), ub (segD_b3 sm b1) 4)
else (st1, segD_b3 sm b1)), s))).
{ destruct (nb_submodeID st1 =? 1); [| reflexivity].
unfold bits_unpack_unsigned_M, mbind, mret. rewrite unpack_eta, ebind_ret_ok. reflexivity. }
rewrite H3, ebind_ret_ok. clear H3.
unfold segD_st, segD_bits.
destruct (Z.eqb_spec (nb_submodeID st1) 1) as [E1|E1]; cbn [fst snd].
1: replace (1 <? nb_submodeID (set_nb_dtx_enabled st1 (if uv (segD_b3 sm b1) 4 =? 15 then 1 else 0))) with false
by (symmetry; apply Z.ltb_ge; destruct st1; cbn in E1 |- *; lia).
all: unfold mbind at 1; rewrite nb_decode_subframes_run by assumption.
all: destruct (subframes_pure 4 0 sm _ _ _) as [[st3 b3]|]; rewrite ?ebind_ret_ok, ?ebind_ret_unr; reflexivity.
Qed.

#[using="Type"] Lemma subframe_pure_sim : forall sm olp sub st b st' b',
subframe_pure sm olp sub st b = Some (st', b') -> bits_sim b b'.
Proof.
intros sm olp sub st b st' b' H. unfold subframe_pure in H.
destruct (sm_ltp_unquant sm) as [k|]; [| discriminate]. destruct (sm_innovation_unquant sm) as [ki|]; [| discriminate].
cbv zeta in H.
match type of H with (if ?c then _ else _) = _ => destruct c end.
- destruct (voc_loop _ _ _); [| discriminate]. injection H as _ <-.
eapply bits_sim_trans; [apply ltp_bits_sim|]. eapply bits_sim_trans; [apply hsg_bits_sim|].
eapply bits_sim_trans; [apply innov_bits_sim|]. destruct (negb _); [apply innov_bits_sim | apply bits_sim_refl].
- injection H as _ <-.
eapply bits_sim_trans; [apply ltp_bits_sim|]. eapply bits_sim_trans; [apply hsg_bits_sim|].
eapply bits_sim_trans; [apply innov_bits_sim|]. destruct (negb _); [apply innov_bits_sim | apply bits_sim_refl].
Qed.
#[using="Type"] Lemma subframes_pure_sim : forall n sub sm olp st b st' b',
subframes_pure n sub sm olp st b = Some (st', b') -> bits_sim b b'.
Proof.
induction n as [|n IH]; intros sub sm olp st b st' b' H; cbn [subframes_pure] in H.
- injection H as _ <-. apply bits_sim_refl.
- destruct (subframe_pure sm olp sub st b) as [[st1 b1]|] eqn:E; [| discriminate].
eapply bits_sim_trans; [eapply subframe_pure_sim; exact E | eapply IH; exact H].
Qed.
#[using="Type"] Lemma nb_rest_pure_sim : forall sm st1 b st' b', nb_rest_pure sm st1 b = Some (st', b') -> bits_sim b b'.
Proof.
intros sm st1 b st' b' H. unfold nb_rest_pure in H. cbv zeta in H.
destruct (subframes_pure 4 0 sm _ _ _) as [[st3 b3]|] eqn:E; [| discriminate]. injection H as _ <-.
eapply bits_sim_trans; [apply lsp_bits_sim|].
eapply bits_sim_trans; [| eapply subframes_pure_sim; exact E].
unfold segD_bits, segD_b3, segD_b2, segD_b1.
repeat match goal with |- context [if ?c then _ else _] => destruct c end; bsim.
Qed.
End Pure.

Section Leaves.
Context {RCEIL : RunCeiling}.
Context {St ptr : Type}.
Variable spx_notify : list Z -> M St unit.
Local Notation unpackM := (@bits_unpack_unsigned_M St ptr).
Local Notation advanceM := (@bits_advance_M St ptr).
Local Notation remainingM := (@bits_remaining_M St ptr).
Implicit Types b : bits_st ptr.

Definition search_ok b (res : nb_search_res (ptr:=ptr)) : Prop :=
match res with
| NbReturn r b' => (r = -1 \/ r = -2) /\ bits_sim b b'
| NbMode m b' => bits_sim b b'
end.

Ltac mret_bind := apply mleaves_bind; apply mleaves_ret; cbv beta iota delta [fst snd].
Ltac munpack := apply mleaves_bind; unfold bits_unpack_unsigned_M at 1; apply mleaves_ret; rewrite unpack_eta; cbv beta iota delta [fst snd].
Ltac madvance := apply mleaves_bind; unfold bits_advance_M at 1; apply mleaves_ret; cbv beta iota delta [fst snd].
Ltac mremaining := apply mleaves_bind; unfold bits_remaining_M at 1; apply mleaves_ret; cbv beta iota delta [fst snd].

#[using="Type"] Lemma skip_leaves : forall b s P, (forall s', P (skip_bits b, s')) -> mleaves (nb_skip_wb_layer unpackM advanceM b) s P.
Proof.
intros b s P H. eapply mleaves_eq; [apply (nbs_skip_run (St:=St))|]. apply H.
Qed.

#[using="Type"] Lemma mleaves_bind_mono : forall {A B} (c : M St A) (f : A -> M St B) s (P : A * St -> Prop) (Q : B * St -> Prop),
mleaves c s P -> (forall a s', P (a, s') -> mleaves (f a) s' Q) -> mleaves (mbind c f) s Q.
Proof.
intros A B c f s P Q H K. apply mleaves_bind. eapply mleaves_mono; [exact H|]. intros [a s'] HP. apply K. exact HP.
Qed.
#[using="Type"] Lemma search_ok_trans : forall b b' res, bits_sim b b' -> search_ok b' res -> search_ok b res.
Proof.
intros b b' [r b2|m b2] S H; cbn in *; [destruct H as [H1 H2]; split; [exact H1|] |]; eapply bits_sim_trans; eauto.
Qed.
#[using="Type"] Lemma notify_then : forall {A} msg (a : A) s (P : A * St -> Prop), (forall s', P (a, s')) -> mleaves (spx_notify msg ;;; mret a) s P.
Proof. intros A msg a s P H. apply mleaves_seq_any. intros u s'. apply mleaves_ret. apply H. Qed.

#[using="Type"] Lemma wb_leaves : forall w b s,
mleaves (nbs_wb spx_notify w b) s (fun p => match fst p with inl b' => bits_sim b b' | inr res => search_ok b res end).
Proof.
intros w b s. unfold nbs_wb. destruct (negb (w =? 0)); [| apply mleaves_ret; cbn; apply bits_sim_refl].
apply mleaves_bind. unfold nbs_skip. apply skip_leaves. intros s1. cbv beta iota delta [fst snd].
mremaining. destruct (_ <? 5); [apply mleaves_ret; cbn; split; [auto| apply skip_bits_sim]|].
munpack. destruct (negb (uv (skip_bits b) 1 =? 0)); [| apply mleaves_ret; cbn; eapply bits_sim_trans; [apply skip_bits_sim | apply ub_sim]].
apply mleaves_bind. unfold nbs_skip. apply skip_leaves. intros s2. cbv beta iota delta [fst snd].
munpack. destruct (negb _).
- apply notify_then. intros s'. cbn. split; [auto|].
eapply bits_sim_trans; [apply skip_bits_sim|]. eapply bits_sim_trans; [apply ub_sim|]. eapply bits_sim_trans; [apply skip_bits_sim| apply ub_sim].
- apply mleaves_ret. cbn.
eapply bits_sim_trans; [apply skip_bits_sim|]. eapply bits_sim_trans; [apply ub_sim|]. eapply bits_sim_trans; [apply skip_bits_sim| apply ub_sim].
Qed.

#[using="Type"] Lemma search_leaves : forall fuel st b s,
mleaves (nb_mode_search spx_notify unpackM advanceM remainingM fuel st b) s (fun p => search_ok b (fst p)).
Proof.
induction fuel as [|fuel IH]; intros st b s; [apply mleaves_unr|].
rewrite (nb_mode_search_S (St:=St)).
mremaining. destruct (_ <? 5); [apply mleaves_ret; cbn; split; [auto| apply bits_sim_refl]|].
munpack.
eapply mleaves_bind_mono; [apply wb_leaves|]. intros [b'|res] s' H; cbn in H.
2: { apply mleaves_ret. cbn. eapply search_ok_trans; [apply ub_sim| exact H]. }

eapply mleaves_mono with (P := fun p => search_ok b' (fst p)).
2: { intros [res s2] HR. cbn in HR |- *. eapply search_ok_trans; [| exact HR]. eapply bits_sim_trans; [apply ub_sim| exact H]. }
unfold nbs_tail. mremaining. destruct (_ <? 4); [apply mleaves_ret; cbn; split; [auto| apply bits_sim_refl]|].
munpack. destruct (uv b' 4 =? 15); [apply mleaves_ret; cbn; split; [auto| apply ub_sim]|].
destruct (uv b' 4 =? 14).
{ apply mleaves_bind. eapply mleaves_eq; [apply (inband_run (St:=St))|]. cbn [fst snd Z.eqb negb].
eapply mleaves_mono; [apply IH|]. intros [res s2] HR. cbn in HR |- *.
eapply search_ok_trans; [| exact HR]. eapply bits_sim_trans; [apply ub_sim| apply inband_bits_sim]. }
destruct (uv b' 4 =? 13).
{ apply mleaves_bind. eapply mleaves_eq; [apply (user_handler_run (St:=St))|]. cbn [fst snd Z.eqb negb].
eapply mleaves_mono; [apply IH|]. intros [res s2] HR. cbn in HR |- *.
eapply search_ok_trans; [| exact HR]. eapply bits_sim_trans; [apply ub_sim| apply user_handler_bits_sim]. }
destruct (8 <? uv b' 4).
- apply notify_then. intros s2. cbn. split; [auto| apply ub_sim].
- apply mleaves_ret. cbn. apply ub_sim.
Qed.

#[using="Type"] Lemma nb_submodes_unq : forall m sm, submode_at nb_submodes m = Some sm ->
sm_ltp_unquant sm <> None /\ sm_innovation_unquant sm <> None.
Proof.
intros m sm H. unfold submode_at in H.
destruct (m <? 0); [discriminate|].
remember (Z.to_nat m) as n eqn:En. clear En.
do 16 (destruct n as [|n]; [cbn in H; first [discriminate | injection H as <-; split; discriminate] |]).
cbn in H. destruct n; discriminate.
Qed.

#[using="Type"] Theorem nb_decode_leaves : forall st b s,
mleaves (nb_decode spx_notify unpackM advanceM remainingM st b) s
(fun p => let '(r, st', b') := fst p in -2 <= r <= 0 /\ bits_sim b b').
Proof.
intros st b s. unfold nb_decode.
eapply mleaves_bind_mono with (P := fun p => search_ok b (fst p)).
{ destruct (negb _); [apply search_leaves | apply mleaves_ret; cbn; apply bits_sim_refl]. }
intros [r b'|m b'] s' H; cbn in H.
- apply mleaves_ret. cbn. destruct H as [[-> | ->] S]; (split; [lia| exact S]).
- cbv beta iota zeta.
destruct (submode_at nb_submodes (nb_submodeID (set_nb_submodeID st m))) as [sm|] eqn:ES.
+ destruct (nb_submodes_unq _ _ ES) as [HK HI].
change (mleaves (nb_rest sm (set_nb_submodeID st m) b') s' (fun p => let '(r, st', b'0) := fst p in -2 <= r <= 0 /\ bits_sim b b'0)).
eapply mleaves_eq; [apply nb_rest_run; assumption|].
destruct (nb_rest_pure sm (set_nb_submodeID st m) b') as [[st2 b2]|] eqn:ER; [| exact I].
cbn. split; [lia|]. eapply bits_sim_trans; [exact H| eapply nb_rest_pure_sim; exact ER].
+ apply mleaves_ret. cbn. split; [lia| exact H].
Qed.
End Leaves.

