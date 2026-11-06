(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bs X1c2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1qs X1nw X1qz X1r0 X1nt X1rg X1rh X1re
X1nv X1rb X1rf X1r1 X1od.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section HarnessSafe.
Context {St ptr : Type}.
Variable own : list ptr -> assn St.
Variable lib_malloc : Z -> M St (option ptr).
Variable lib_calloc : Z -> Z -> M St (option ptr).
Variable lib_realloc : ptr -> Z -> M St (option ptr).
Variable lib_free : ptr -> M St unit.
Variable spx_notify : list Z -> M St unit.
Variable spx_warning : list Z -> M St unit.

Hypothesis Hmal : forall X n, 0 <= n ->
mspec (own X) (lib_malloc n) (fun r s mo => match r with Some p => own (p :: X) s mo | None => own X s mo end).
Hypothesis Hcal : forall X n m, 0 <= n -> 0 <= m ->
mspec (own X) (lib_calloc n m) (fun r s mo => match r with Some p => own (p :: X) s mo | None => own X s mo end).
Variable reall : ptr -> Prop.
Hypothesis Hmal_big : forall X n, REALL_MIN <= n ->
mspec (own X) (lib_malloc n) (fun r s mo => match r with Some p => own (p :: X) s mo /\ reall p | None => own X s mo end).
Hypothesis Hcal_big : forall X n m, 0 <= n -> 0 <= m -> REALL_MIN <= n * m ->
mspec (own X) (lib_calloc n m) (fun r s mo => match r with Some p => own (p :: X) s mo /\ reall p | None => own X s mo end).
Hypothesis Hrea : forall X p n, reall p -> REALL_MIN <= n < MMAP_THRESHOLD ->
mspec (own (p :: X)) (lib_realloc p n) (fun r s mo => match r with Some q => own (q :: X) s mo /\ reall q | None => own (p :: X) s mo end).
Hypothesis Hfree : forall X p, mspec (own (p :: X)) (lib_free p) (fun _ => own X).
Hypothesis Hperm : forall X Y s mo, Permutation X Y -> own X s mo -> own Y s mo.
Hypothesis Hnotify : forall X msg, msg_ok msg -> mspec (own X) (spx_notify msg) (fun _ => own X).
Hypothesis Hwarning : forall X msg, msg_ok msg -> mspec (own X) (spx_warning msg) (fun _ => own X).

Hypothesis Hmal_some : forall n, 0 <= n < SOME_MAX -> mspecA (lib_malloc n) (fun r => r <> None).
Hypothesis Hcal_some : forall n m, 0 <= n -> 0 <= m -> n * m < SOME_MAX -> mspecA (lib_calloc n m) (fun r => r <> None).
Hypothesis Hrea_some : forall p n, 0 <= n < SOME_MAX -> mspecA (lib_realloc p n) (fun r => r <> None).

Local Abbreviation unpackM := (@bits_unpack_unsigned_M St ptr).
Local Abbreviation peekM := (@bits_peek_M St ptr).
Local Abbreviation advanceM := (@bits_advance_M St ptr).
Local Abbreviation remainingM := (@bits_remaining_M St ptr).

Local Abbreviation cleanupH := (cleanup lib_free (St:=St)).
Local Abbreviation process_headerH := (process_header lib_calloc lib_free spx_notify (St:=St)).
Local Abbreviation decode_loopH := (decode_loop spx_notify unpackM peekM advanceM remainingM).
Local Abbreviation packet_loopH := (packet_loop lib_calloc lib_realloc lib_free spx_notify spx_warning unpackM peekM advanceM remainingM).
Local Abbreviation page_loopH := (page_loop lib_malloc lib_calloc lib_realloc lib_free spx_notify spx_warning unpackM peekM advanceM remainingM).
Local Abbreviation chunk_loopH := (chunk_loop lib_malloc lib_calloc lib_realloc lib_free spx_notify spx_warning unpackM peekM advanceM remainingM).
Local Abbreviation LLVMFuzzerTestOneInputH :=
(LLVMFuzzerTestOneInput lib_malloc lib_calloc lib_realloc lib_free spx_notify spx_warning unpackM peekM advanceM remainingM).

#[using="Hperm"] Lemma own_perm {A} (X Y : list ptr) (m : M St A) Q :
Permutation Y X -> mspec (own Y) m Q -> mspec (own X) m Q.
Proof. intros HP Hm. eapply mspec_pre; [exact Hm|]. intros s mo H. eapply Hperm; [apply Permutation_sym; exact HP| exact H]. Qed.

Implicit Types h : hstate ptr.

Definition opt_dec_ptrs (o : option (dec_state ptr)) : list ptr :=
match o with Some d => dec_ptrs d | None => [] end.

Definition h_ptrs h : list ptr :=
sy_ptrs (h_oy h) ++ os_ptrs (h_os h) ++ sb_chars (h_bits h) :: opt_dec_ptrs (h_st h).

Definition pend h : Z := sy_fill (h_oy h) - sy_returned (h_oy h).
Definition consumed (L : Z) h : Z := (L - h_bytes_remaining h) - pend h.

Definition hinv_obj h : Prop :=
sync_ok reall (h_oy h) /\ os_ok reall (h_os h) /\ body_inv (h_os h) /\
(h_stream_init h = 0 -> h_os h = stream_zero) /\
(bits_ok (h_bits h) /\ reall (sb_chars (h_bits h)) /\ REALL_MIN <= sb_buf_size (h_bits h)) /\ sb_owner (h_bits h) <> 0 /\ 0 <= h_packet_count h /\
match h_st h with Some d => dec_wf d /\ h_packet_count h <> 0 | None => h_packet_count h = 0 end.

Definition hinv_budget (L : Z) h : Prop :=
0 <= h_bytes_remaining h <= L /\ L <= MAX_FUZZ_SIZE /\ 0 <= pend h /\ 0 <= consumed L h /\
os_lacing_fill (h_os h) <= consumed L h /\ os_body_fill (h_os h) <= consumed L h /\
os_lacing_storage (h_os h) <= 1568 + consumed L h /\ os_body_storage (h_os h) <= 17408 + 2 * consumed L h.

Definition hinv (L : Z) h : Prop := hinv_obj h /\ hinv_budget L h.

#[using="Hfree Hperm"] Lemma cleanup_spec : forall X h, hinv_obj h ->
mspec (own (h_ptrs h ++ X)) (cleanupH h) (fun _ => own X).
Proof.
intros X h (Hsy & Hos & Hbo & Hsi & Hb & Hown & Hpc & Hst). unfold cleanup, h_ptrs.
eapply mspec_seq with (R := own (sy_ptrs (h_oy h) ++ os_ptrs (h_os h) ++ sb_chars (h_bits h) :: X)).
{ unfold h_decoder_destroy. destruct (h_st h) as [d|]; cbn [opt_dec_ptrs].
- eapply own_perm; [| apply (speex_decoder_destroy_spec own lib_free Hfree)]. perm_solve.
- apply mspec_ret. intros s mo H. eapply Hperm; [|exact H]. perm_solve. }
intros _. eapply mspec_seq with (R := own (sy_ptrs (h_oy h) ++ os_ptrs (h_os h) ++ X)).
{ eapply own_perm; [| apply (speex_bits_destroy_spec own lib_free Hfree); exact Hown]. perm_solve. }
intros _. eapply mspec_seq with (R := own (sy_ptrs (h_oy h) ++ X)).
{ destruct (Z.eqb_spec (h_stream_init h) 0) as [Ez|Ez]; cbn [negb].
- rewrite (Hsi Ez). cbn. apply mspec_ret. intros s mo H. exact H.
- eapply mspec_bind. { eapply own_perm; [| apply (ogg_stream_clear_spec own lib_free Hfree (sy_ptrs (h_oy h) ++ X))]. perm_solve. }
intros os'. apply mspec_ret. intros s mo [H _]. exact H. }
intros _. eapply mspec_bind; [apply (ogg_sync_clear_spec own lib_free Hfree)|]. intros oy'. apply mspec_ret. intros s mo [H _]. exact H.
Qed.

Let PTH := speex_packet_to_header_spec own lib_calloc lib_free spx_notify Hcal Hfree Hnotify Hcal_some.
Let DINIT := speex_decoder_init_spec own lib_calloc lib_free Hcal Hfree Hperm Hcal_some.
Let DDEST := speex_decoder_destroy_spec own lib_free Hfree.
Let DEC := speex_decode_spec own spx_notify Hnotify.
Let BINIT := speex_bits_init_spec own lib_calloc reall Hcal_big.
Let BINIT_some := speex_bits_init_some lib_calloc Hcal_some.
Let BDEST := speex_bits_destroy_spec own lib_free Hfree.
Let BREAD := speex_bits_read_from_spec own lib_realloc spx_notify spx_warning reall Hrea Hnotify Hwarning.
Let OSCLR := ogg_stream_clear_spec own lib_free Hfree.
Let SYBUF := ogg_sync_buffer_spec2 own lib_malloc lib_realloc lib_free reall Hmal_big Hrea Hfree Hmal_some Hrea_some.
Let PAGEIN := ogg_stream_pagein_spec2 own lib_realloc lib_free reall Hrea Hfree Hperm.

#[using="Type"] Lemma speex_lib_get_mode_some : forall m, 0 <= m < 3 -> exists md, speex_lib_get_mode m = Some md.
Proof.
intros m Hm. unfold speex_lib_get_mode, X1rh.SPEEX_NB_MODES.
destruct (Z.ltb_spec m 0); [lia|]. destruct (Z.leb_spec 3 m); [lia|]. cbn [orb].
destruct (m =? 0); [eexists; reflexivity|]. destruct (m =? 1); eexists; reflexivity.
Qed.

#[using="Hcal Hfree Hperm Hnotify PTH DINIT DDEST"] Lemma process_header_spec : forall X h pdata bytes, h_st h = None ->
mspec (own (h_ptrs h ++ X)) (process_headerH h pdata bytes)
(fun r s mo => match r with
| None => own (h_ptrs h ++ X) s mo
| Some h' => own (h_ptrs h' ++ X) s mo /\
exists st nf ch ra ex fs, h' = set_header h st nf ch ra ex fs /\ dec_wf st
end).
Proof.
intros X h pdata bytes Hst. unfold process_header.
set (X' := h_ptrs h ++ X).
eapply mspec_bind; [apply PTH|]. intros [[blk hd]|].
2:{ apply mspec_ret. intros s mo H. exact H. }
apply mspec_pure. intros Hmode.
assert (FREE_RET : mspec (own (blk :: X')) (lib_free blk ;;; mret None)
(fun r s mo => match r with None => own X' s mo
| Some h' => own (h_ptrs h' ++ X) s mo /\ exists st nf ch ra ex fs, h' = set_header h st nf ch ra ex fs /\ dec_wf st end)).
{ eapply mspec_seq; [apply Hfree|]. intros _. apply mspec_ret. intros s mo H. exact H. }
apply mspec_if; intros Hrange; [exact FREE_RET|].
destruct (speex_lib_get_mode_some (hd_mode hd)) as [md ->].
{ unfold X1rg.SPEEX_NB_MODES in Hmode. lia. }
apply mspec_if; intros _; [exact FREE_RET|].
apply mspec_if; intros _; [exact FREE_RET|].
apply mspec_if; intros _; [exact FREE_RET|].
unfold h_decoder_init. eapply mspec_bind; [apply DINIT|]. intros [st|]; cbn [init_post].
2:{ exact FREE_RET. }
apply mspec_pure. intros Hwf.
assert (DFREE_RET : forall st', dec_rel st st' ->
mspec (own (dec_ptrs st ++ blk :: X')) (h_decoder_destroy lib_free st' ;;; lib_free blk ;;; mret None)
(fun r s mo => match r with None => own X' s mo
| Some h' => own (h_ptrs h' ++ X) s mo /\ exists st nf ch ra ex fs, h' = set_header h st nf ch ra ex fs /\ dec_wf st end)).
{ intros st' (Rp & Rw & Rd). unfold h_decoder_destroy. eapply mspec_seq; [rewrite <- Rp; apply DDEST|]. intros _. exact FREE_RET. }
destruct (ctl_cases st (CtlSetEnh 1) Hwf) as (v1 & st1 & -> & R1).
destruct (ctl_cases st1 CtlGetFrameSize ltac:(apply R1)) as (fs & st2 & -> & R2).
pose proof (dec_rel_trans _ _ _ R1 R2) as R02.
apply mspec_if; intros _; [apply DFREE_RET; exact R02|].
destruct (ctl_cases st2 (CtlSetSamplingRate (if h_rate h =? 0 then hd_rate hd else h_rate h)) ltac:(apply R2)) as (v3 & st3 & -> & R3).
pose proof (dec_rel_trans _ _ _ R02 R3) as R03.
apply mspec_if; intros _; [apply DFREE_RET; exact R03|].

set (chst := if negb _ then _ else _).
assert (Hch : exists ch st4, chst = (ch, st4) /\ dec_rel st st4).
{ subst chst. destruct (negb _).
- destruct (ctl_cases st3 CtlSetHandlerStereo ltac:(apply R3)) as (v4 & st4 & -> & R4). exists 2, st4. split; [reflexivity|].
eapply dec_rel_trans; [exact R03| exact R4].
- eexists _, st3. split; [reflexivity| exact R03]. }
destruct Hch as (ch & st4 & -> & R4).
apply mspec_if; intros _; [apply DFREE_RET; exact R4|].
eapply mspec_seq. { eapply own_perm; [| apply (Hfree (dec_ptrs st ++ X'))]. perm_solve. }
intros _. destruct (ctl_cases st4 CtlGetLookahead ltac:(apply R4)) as (v5 & st5 & -> & R5).
pose proof (dec_rel_trans _ _ _ R4 R5) as (Rp & Rw & Rd).
apply mspec_ret. intros s mo H. split.
- unfold X', h_ptrs in *. cbn [h_oy h_os h_bits h_st set_header opt_dec_ptrs]. rewrite Hst in H. cbn [opt_dec_ptrs] in H. rewrite Rp.
eapply Hperm; [|exact H]. perm_solve.
- eexists _, _, _, _, _, _. split; [reflexivity| exact Rw].
Qed.

#[using="Hnotify DEC"] Lemma decode_loop_spec : forall X n (d : dec_state ptr) (b : bits_st ptr), dec_wf d -> bits_ok b ->
mspec (own X) (decode_loopH n d b) (fun r s mo => own X s mo /\ dec_rel d (fst r) /\ bsame b (snd r)).
Proof.
intros X n. induction n as [|n IH]; intros d b Hwf Hok; cbn [decode_loop].
- apply mspec_ret. intros s mo H. split; [exact H|]. split; [apply dec_rel_refl; exact Hwf| apply bsame_refl; exact Hok].
- unfold h_decode. eapply mspec_bind; [apply DEC; [exact Hwf| exact Hok]|]. intros [[ret d1] b1]. cbn beta iota.
apply mspec_pure. intros [R1 S1].
apply mspec_if; intros _. { apply mspec_ret. intros s mo H. cbn. auto. }
unfold bits_remaining_M. eapply mspec_bind with (Q1 := fun _ => own X). { apply mspec_ret. intros s mo H. exact H. }
intros rem. apply mspec_if; intros _. { apply mspec_ret. intros s mo H. cbn. auto. }
eapply mspec_post; [apply IH; [apply R1| apply (bsame_ok _ _ S1)]|].
intros [d2 b2] s mo (H & R2 & S2). cbn in *. split; [exact H|]. split; [eapply dec_rel_trans; eauto| eapply bsame_trans; eauto].
Qed.

#[using="Type"] Lemma hinv_budget_frame : forall L h h',
h_oy h' = h_oy h -> h_bytes_remaining h' = h_bytes_remaining h ->
os_lacing_fill (h_os h') <= os_lacing_fill (h_os h) -> os_body_fill (h_os h') <= os_body_fill (h_os h) ->
os_lacing_storage (h_os h') <= os_lacing_storage (h_os h) -> os_body_storage (h_os h') <= os_body_storage (h_os h) ->
hinv_budget L h -> hinv_budget L h'.
Proof.
intros L h h' E1 E2 L1 L2 L3 L4 B. unfold hinv_budget, consumed, pend in *. rewrite E1, E2. lia.
Qed.

Definition pk_meas h : nat := Z.to_nat (os_lacing_fill (h_os h) - os_lacing_returned (h_os h)).

#[using="Hcal Hrea Hfree Hperm Hnotify Hwarning PTH DINIT DDEST DEC BREAD"] Lemma packet_loop_spec : forall L X fuel h packet_no,
hinv L h -> (pk_meas h < fuel)%nat ->
mspec (own (h_ptrs h ++ X)) (packet_loopH fuel h packet_no)
(fun r s mo => match r with
| Returned => own X s mo
| Cont h' => own (h_ptrs h' ++ X) s mo /\ hinv L h' /\ h_oy h' = h_oy h /\
h_bytes_remaining h' = h_bytes_remaining h /\ h_stream_init h' = h_stream_init h
end).
Proof.
intros L X fuel. induction fuel as [|fuel IH]; intros h packet_no Hinv Hfuel; [lia|].
pose proof Hinv as [(Hsy & Hos & Hbo & Hsi & Hb & Hown & Hpc & Hst) HB].
cbn [packet_loop].
apply mspec_if; intros _. { apply mspec_ret. intros s mo H. auto. }
pose proof Hos as (Hbl & Hsinv & Hbs0 & Hls0 & HRl).
pose proof (ogg_stream_packetout_total (h_os h) (stream_inv_lacing_inv _ Hsinv)) as Htot.
destruct (ogg_stream_packetout (h_os h)) as [[[r oop] os1]|] eqn:Epo; [|exfalso; apply Htot; reflexivity]. clear Htot.
pose proof (ogg_stream_packetout_frame (h_os h) r oop os1 Hsinv Epo) as (Hsinv1 & Fbd & Flv & Fgv & Fbs & Fls & Flf & Fbf & Fsn & Fret & Fr1 & Fnone).
pose proof (ogg_stream_packetout_body_inv (h_os h) r oop os1 Hsinv Hbo Epo) as (Hbo1 & Fbf' & Fbody & Hpkt).
assert (Eop : os_ptrs os1 = os_ptrs (h_os h)) by (unfold os_ptrs; rewrite Fbd, Flv, Fgv; reflexivity).

assert (INV1 : forall sser, let h1 := set_serialno (set_ogg h (h_oy h) os1) sser in
hinv L h1 /\ h_ptrs h1 = h_ptrs h /\ h_oy h1 = h_oy h /\ h_bytes_remaining h1 = h_bytes_remaining h /\
h_stream_init h1 = h_stream_init h /\ h_os h1 = os1 /\ h_st h1 = h_st h /\ h_bits h1 = h_bits h /\
h_packet_count h1 = h_packet_count h /\ h_nframes h1 = h_nframes h /\ h_extra_headers h1 = h_extra_headers h).
{ intros sser. cbv zeta. split; [split|].
- unfold hinv_obj; cbn. split; [exact Hsy|]. split.
{ unfold os_ok. split; [unfold os_blocks_ok; rewrite Fbd, Flv, Fgv; exact Hbl|]. split; [exact Hsinv1|]. rewrite Fbs, Fls. split; [lia|]. split; [lia|].
eapply os_reall_frame; [exact Fbd| exact Flv| exact Fgv| rewrite Fbs; lia| rewrite Fls; lia| exact HRl]. }
split; [exact Hbo1|]. split.
{ intros Hz. specialize (Hsi Hz). rewrite Hsi in Fnone. destruct (Fnone eq_refl) as [-> _]. reflexivity. }
split; [exact Hb|]. split; [exact Hown|]. split; [exact Hpc| exact Hst].
- eapply hinv_budget_frame; [..| exact HB]; cbn; try reflexivity; lia.
- unfold h_ptrs; cbn. rewrite Eop. repeat split; reflexivity. }
cbn beta iota.
apply mspec_if; intros Hr.
{ apply mspec_ret. intros s mo H. destruct (INV1 (h_speex_serialno h)) as (I1 & P1 & O1 & R1 & S1 & _).

split; [| split; [| split; [| split]]].
- unfold h_ptrs in *; cbn. rewrite Eop. exact H.
- destruct I1 as [A B]. split.
+ unfold hinv_obj in *; cbn in *. exact A.
+ unfold hinv_budget, consumed, pend in *; cbn in *. exact B.
- reflexivity. - reflexivity. - reflexivity. }
apply Bool.negb_false_iff in Hr. apply Z.eqb_eq in Hr. destruct (Fr1 Hr) as [Hop Hlt].
destruct oop as [op|]; [|exfalso; apply Hop; reflexivity]. clear Hop.
destruct Hpkt as (Poff & Pbytes & Pend & Plen).
change (h_speex_serialno (set_ogg h (h_oy h) os1)) with (h_speex_serialno h).
set (sser := if (5 <=? pk_bytes op) && list_eqb (ztake 5 (packet_data os1 op)) SPEEX_STR then os_serialno os1 else h_speex_serialno h).
destruct (INV1 sser) as (I1 & P1 & O1 & R1 & S1 & OS1 & ST1 & BI1 & PC1 & NF1 & EH1).
set (h1 := set_serialno (set_ogg h (h_oy h) os1) sser) in *.
apply mspec_if; intros _. { apply mspec_ret. intros s mo H. rewrite P1, O1, R1, S1. auto. }
rewrite <- P1.

eapply mspec_bind with
(Q1 := fun ro s mo => match ro with
| None => own X s mo
| Some (h', pn) => let h'' := incr_packet_count h' in
own (h_ptrs h'' ++ X) s mo /\ hinv L h'' /\
h_oy h'' = h_oy h /\ h_os h'' = os1 /\ h_bytes_remaining h'' = h_bytes_remaining h /\
h_stream_init h'' = h_stream_init h
end).
{ pose proof I1 as [(Qsy & Qos & Qbo & Qsi & Qb & Qown & Qpc & Qst) QB].
apply mspec_if; intros Hpc0.
-
apply Z.eqb_eq in Hpc0.
assert (HstN : h_st h1 = None). { rewrite PC1 in Hpc0. rewrite ST1. rewrite ST1, PC1 in Qst. destruct (h_st h) as [d|]; [|reflexivity].
exfalso. destruct Qst as [_ NZ]. exact (NZ Hpc0). }
eapply mspec_bind; [apply process_header_spec; exact HstN|]. intros [h2|]; cbn beta iota.
+ apply mspec_pure. intros (st & nf & ch & ra & ex & fs & -> & Hwf2).
apply mspec_ret. intros s mo H. cbv zeta. split; [exact H|]. split; [| subst h1; cbn; repeat split; reflexivity].
split.
* unfold hinv_obj. subst h1; cbn in *. split; [exact Qsy|]. split; [exact Qos|]. split; [exact Qbo|]. split; [exact Qsi|].
split; [exact Qb|]. split; [exact Qown|]. split; [lia|]. split; [exact Hwf2| lia].
* eapply hinv_budget_frame; [..| exact QB]; subst h1; cbn; first [reflexivity | lia].
+ eapply mspec_seq; [apply cleanup_spec; exact (proj1 I1)|]. intros _. apply mspec_ret. intros s mo H. exact H.
- apply mspec_if; intros Hextra.
+
apply mspec_ret. intros s mo H. cbv zeta. apply Z.eqb_neq in Hpc0.
assert (HstS : exists d, h_st h = Some d /\ dec_wf d).
{ rewrite ST1, PC1 in Qst. rewrite PC1 in Hpc0. destruct (h_st h) as [d|]; [exists d; split; [reflexivity| apply Qst]| lia]. }
destruct HstS as (d & Hd & Hwfd). rewrite PC1 in Hpc0.
split; [unfold h_ptrs in *; cbn; exact H|]. split; [| subst h1; cbn; repeat split; reflexivity].
split.
* unfold hinv_obj. subst h1. cbn. rewrite Hd. split; [exact Qsy|]. split; [exact Qos|]. split; [exact Qbo|]. split; [exact Qsi|].
split; [exact Qb|]. split; [exact Qown|]. split; [lia|]. split; [exact Hwfd| lia].
* eapply hinv_budget_frame; [..| exact QB]; subst h1; cbn; first [reflexivity | lia].
+
apply Z.eqb_neq in Hpc0.
assert (HstS : exists d, h_st h = Some d /\ dec_wf d).
{ rewrite ST1, PC1 in Qst. rewrite PC1 in Hpc0. destruct (h_st h) as [d|]; [exists d; split; [reflexivity| apply Qst]| lia]. }
destruct HstS as (d & Hd & Hwfd). rewrite PC1 in Hpc0.
pose proof QB as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
unfold h_ptrs at 1. rewrite ST1, Hd. cbn [opt_dec_ptrs].
eapply mspec_bind.
{ eapply own_perm; [| apply (BREAD (sy_ptrs (h_oy h1) ++ os_ptrs (h_os h1) ++ dec_ptrs d ++ X))]; [perm_solve| exact (proj1 Qb)| | exact (proj1 (proj2 Qb))| exact (proj2 (proj2 Qb))|].
- rewrite Plen. lia.
- intros _. rewrite OS1 in B6. unfold consumed, pend, MAX_FUZZ_SIZE, MMAP_THRESHOLD in *. lia. }
intros b'. cbn beta iota. apply mspec_pure. intros ((Qrl' & Qsz') & Qok' & Qown' & _).
eapply mspec_bind.
{ apply (decode_loop_spec _ _ d b' Hwfd Qok'). }
intros [d2 b2]. cbn beta iota. apply mspec_pure. intros [(Rp & Rw & Rd) S2]. cbn in Rp, Rw, Rd, S2.
pose proof S2 as (S2ok & S2c & S2n & S2o & S2s).
apply mspec_ret. intros s mo H. cbv zeta.
split; [| split; [| subst h1; cbn; repeat split; reflexivity]].
* unfold h_ptrs; subst h1; cbn. cbn in H. rewrite S2c, Rp. eapply Hperm; [|exact H]. perm_solve.
* split.
-- unfold hinv_obj; subst h1; cbn. split; [exact Qsy|]. split; [exact Qos|]. split; [exact Qbo|]. split; [exact Qsi|].
split; [split; [exact S2ok|]; rewrite S2c, S2s; split; [exact Qrl'| pose proof (proj2 (proj2 Qb)); lia]|].
split; [rewrite S2o, Qown'; exact Qown|]. split; [lia|]. split; [exact Rw| lia].
-- eapply hinv_budget_frame; [..| exact QB]; subst h1; cbn; first [reflexivity | lia]. }

intros [[h2 pn]|]; cbn beta iota.
2:{ apply mspec_ret. intros s mo H. exact H. }
apply mspec_pure. intros (I2 & O2 & OS2 & R2 & S2').
eapply mspec_post.
{ apply IH; [exact I2|]. unfold pk_meas in *. rewrite OS2. rewrite Flf. lia. }
intros [h3|] s mo; [|intros H; exact H]. intros (H & I3 & O3 & R3 & S3). rewrite O2 in O3. rewrite R2 in R3. rewrite S2' in S3. auto.
Qed.

#[using="Hmal_big"] Lemma malloc_olist : forall X n, REALL_MIN <= n -> mspec (own X) (lib_malloc n) (fun r s mo => own (olist r ++ X) s mo /\ oreall reall r).
Proof.
intros X n Hn. eapply mspec_post; [apply Hmal_big; exact Hn|].
intros [p|] s mo H; cbn; [destruct H as [H R]; split; [exact H| intros q E; injection E as <-; exact R] | split; [exact H| intros q E; discriminate E]].
Qed.

#[using="Hmal_big Hfree Hperm OSCLR"] Lemma ogg_stream_init_spec2 : forall X sn,
mspec (own X) (ogg_stream_init lib_malloc lib_free sn)
(fun r s mo => let '(rc, os) := r in own (os_ptrs os ++ X) s mo /\
(os = stream_zero \/
exists b l g, os = mkStream (Some b) [] 16384 0 0 (Some l) [] (Some g) [] 1024 0 0 0 0 0 0 sn 0 0 0 /\
(reall b /\ reall l /\ reall g))).
Proof.
intros X sn. unfold ogg_stream_init.
eapply mspec_bind; [apply malloc_olist; unfold REALL_MIN; lia|]. intros b. apply mspec_pure. intros Rb.
eapply mspec_bind; [apply malloc_olist; unfold REALL_MIN; lia|]. intros l. apply mspec_pure. intros Rl.
eapply mspec_bind; [apply malloc_olist; unfold REALL_MIN; lia|]. intros g. apply mspec_pure. intros Rg.
assert (CLR : forall (b l g : option ptr),
mspec (own (olist g ++ olist l ++ olist b ++ X))
(os' <- ogg_stream_clear lib_free (mkStream b [] 16384 0 0 l [] g [] 1024 0 0 0 0 0 0 0 0 0 0) ;; mret (-1, os'))
(fun r s mo => let '(rc, os) := r in own (os_ptrs os ++ X) s mo /\
(os = stream_zero \/ exists b' l' g', os = mkStream (Some b') [] 16384 0 0 (Some l') [] (Some g') [] 1024 0 0 0 0 0 0 sn 0 0 0 /\
(reall b' /\ reall l' /\ reall g')))).
{ intros b' l' g'. eapply mspec_bind.
{ eapply own_perm; [| apply (OSCLR X)]. unfold os_ptrs; cbn. perm_solve. }
intros os'. apply mspec_pure. intros ->. apply mspec_ret. intros s mo H. cbn. split; [exact H| left; reflexivity]. }
destruct b as [b|]; [|apply CLR]. destruct l as [l|]; [|apply CLR]. destruct g as [g|]; [|apply CLR].
apply mspec_ret. intros s mo H. split.
- unfold os_ptrs; cbn. cbn in H. eapply Hperm; [|exact H]. perm_solve.
- right. exists b, l, g. split; [reflexivity|]. split; [apply Rb; reflexivity|]. split; [apply Rl; reflexivity| apply Rg; reflexivity].
Qed.

#[using="Type"] Lemma ogg_stream_reset_serialno_frame : forall (os : stream_st ptr) sn r os',
ogg_stream_reset_serialno os sn = (r, os') ->
os_body_data os' = os_body_data os /\ os_lacing_vals os' = os_lacing_vals os /\ os_granule_vals os' = os_granule_vals os /\
os_body_storage os' = os_body_storage os /\ os_lacing_storage os' = os_lacing_storage os /\
(os_lacing_fill os' = 0 \/ os_lacing_fill os' = os_lacing_fill os) /\ (os_body_fill os' = 0 \/ os_body_fill os' = os_body_fill os) /\
(os_body_data os = None -> os' = os).
Proof.
intros os sn r os' E. unfold ogg_stream_reset_serialno, ogg_stream_check in E.
destruct (os_body_data os) eqn:Eb; inversion E; subst; cbn; rewrite ?Eb; repeat split; auto; try lia; intros; try discriminate.
Qed.

Definition pg_meas h : nat := Z.to_nat (pend h).

Definition os_le (c : Z) (os : stream_st ptr) : Prop :=
os_lacing_fill os <= c /\ os_body_fill os <= c /\ os_lacing_storage os <= 1568 + c /\ os_body_storage os <= 17408 + 2 * c.

#[using="Hcal Hmal_big Hrea Hfree Hperm Hnotify Hwarning PTH DINIT DDEST DEC BREAD OSCLR PAGEIN"] Lemma page_loop_spec : forall L X fuel h,
hinv L h -> (pg_meas h < fuel)%nat ->
mspec (own (h_ptrs h ++ X)) (page_loopH fuel h)
(fun r s mo => match r with
| Returned => own X s mo
| Cont h' => own (h_ptrs h' ++ X) s mo /\ hinv L h' /\ h_bytes_remaining h' = h_bytes_remaining h
end).
Proof.
intros L X fuel. induction fuel as [|fuel IH]; intros h Hinv Hfuel; [lia|].
pose proof Hinv as [(Hsy & Hos & Hbo & Hsi & Hb & Hown & Hpc & Hst) HB].
pose proof Hsy as (Hsy2 & Hsst & Hsnul & HsRl). pose proof Hsy2 as [Hsy1 _].
cbn [page_loop].
pose proof (ogg_sync_pageout_total (h_oy h) Hsy1) as Htot.
destruct (ogg_sync_pageout (h_oy h)) as [[[r oog] oy1]|] eqn:Epo; [|exfalso; apply Htot; reflexivity]. clear Htot.
pose proof (ogg_sync_pageout_frame (h_oy h) r oog oy1 Hsy1 Epo) as (Hsy1' & Ffill & Fbuf & Fdata & Fstor & Fret & Fpage).
pose proof (ogg_sync_pageout_inv2 (h_oy h) r oog oy1 Hsy2 Epo) as [Hsy2' Hog].
pose proof Hsy1' as (SR & _).
assert (Hsyok1 : sync_ok reall oy1). { split; [exact Hsy2'|]. unfold sy_reall. rewrite Fstor, Fdata. split; [exact Hsst|]. split; [exact Hsnul| exact HsRl]. }

set (h0 := set_ogg h oy1 (h_os h)).
assert (E0 : h_ptrs h0 = h_ptrs h). { unfold h_ptrs, sy_ptrs; subst h0; cbn. rewrite Fdata. reflexivity. }
assert (C0 : consumed L h <= consumed L h0 /\ 0 <= pend h0 /\ pend h0 + (sy_returned oy1 - sy_returned (h_oy h)) = pend h).
{ unfold consumed, pend; subst h0; cbn. rewrite Ffill. lia. }
assert (I0 : hinv L h0).
{ split.
- unfold hinv_obj; subst h0; cbn. repeat (split; [assumption|]). exact Hst.
- unfold hinv_budget in *; subst h0; cbn in *. destruct C0 as (C1 & C2 & C3). unfold consumed, pend in *; cbn in *. rewrite Ffill in *. lia. }
cbn beta iota.
apply mspec_if; intros Hr.
{ apply mspec_ret. intros s mo H. rewrite E0. split; [exact H|]. split; [exact I0| reflexivity]. }
apply Bool.negb_false_iff in Hr. apply Z.eqb_eq in Hr. subst r.
destruct oog as [og|]; [|exfalso; lia]. destruct Hog as [_ Hpg]. destruct Fpage as [Fp1 Fp2].
pose proof (page_ok_pagein_pre oy1 og Hsy1' Hpg) as PRE. cbv zeta in PRE. destruct PRE as (Plac & Pn26 & _ & Pbl & Phl & Phdr & Pbody).
pose proof (page_ok_body_len oy1 og Hsy1' Hpg) as (Pzs & Phl2 & _).
pose proof Hpg as (G0 & G1 & G2 & G3 & G4 & G5 & G6).
set (hdr := page_header oy1 og) in *. set (body := page_body oy1 og) in *.
assert (Hn255 : znth hdr 26 < 256). { pose proof (znth_bytes_ok hdr 26 Phdr). lia. }

assert (C0' : consumed L h + zlength hdr + zlength body <= consumed L h0 /\ consumed L h0 <= L /\ L <= MAX_FUZZ_SIZE).
{ destruct C0 as (C1 & C2 & C3). destruct HB as (B1 & B2 & B3 & B4 & _). unfold consumed in *. rewrite Phl, Pbl.
subst h0; cbn in *. lia. }
set (c := consumed L h) in *.
pose proof HB as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).

eapply mspec_bind with
(Q1 := fun h1 s mo => own (h_ptrs h1 ++ X) s mo /\ hinv_obj h1 /\ os_le c (h_os h1) /\
h_oy h1 = oy1 /\ h_bytes_remaining h1 = h_bytes_remaining h /\ h_stream_init h1 <> 0).
{ apply mspec_if; intros Hsi0.
- apply Z.eqb_eq in Hsi0. pose proof (Hsi Hsi0) as Ez.
eapply mspec_bind.
{ rewrite <- E0. apply (ogg_stream_init_spec2 (h_ptrs h0 ++ X)). }
intros [rc os1]. cbn beta iota. apply mspec_pure. intros Hos1.
apply mspec_ret. intros s mo H.
assert (OK1 : os_ok reall os1 /\ body_inv os1 /\ os_le c os1).
{ destruct Hos1 as [-> | (bb & ll & gg & -> & (Rbb & Rll & Rgg))].
- split; [apply stream_zero_ok|]. split; [apply stream_zero_body_inv|]. unfold os_le; cbn. lia.
- split. { unfold os_ok; cbn. split; [exact I|]. split; [unfold stream_inv; cbn; repeat split; lia|]. split; [lia|]. split; [lia|].
unfold os_reall; cbn. split; [intros q E; injection E as <-; exact Rbb|]. split; [intros q E; injection E as <-; exact Rll|].
split; [intros q E; injection E as <-; exact Rgg| intros _; lia]. }
split; [apply ogg_stream_init_body_inv|]. unfold os_le; cbn. lia. }
destruct OK1 as (OK1 & OB1 & OL1).
split; [| split; [| split; [exact OL1| subst h0; cbn; split; [reflexivity| split; [reflexivity| lia]]]]].
+ unfold h_ptrs in *; subst h0; cbn in *. rewrite Ez in H. unfold os_ptrs at 2 in H. cbn in H.
eapply Hperm; [|exact H]. perm_solve.
+ unfold hinv_obj; subst h0; cbn. split; [exact Hsyok1|]. split; [exact OK1|]. split; [exact OB1|]. split; [intros; lia|].
split; [exact Hb|]. split; [exact Hown|]. split; [exact Hpc| exact Hst].
- apply Z.eqb_neq in Hsi0. apply mspec_ret. intros s mo H. rewrite E0. split; [exact H|]. destruct I0 as [IO0 _]. split; [exact IO0|].
subst h0; cbn in *. split; [| split; [reflexivity| split; [reflexivity| exact Hsi0]]]. unfold os_le. subst c. lia. }
intros h1. apply mspec_pure. intros (RO & OL1 & O1 & R1 & SI1). pose proof RO as (Rsy & Ros & Rbo & Rsi & Rb & Rown & Rpc & Rst).

set (h2 := if negb _ then _ else h1).
assert (H2 : hinv_obj h2 /\ os_le c (h_os h2) /\ h_oy h2 = oy1 /\ h_bytes_remaining h2 = h_bytes_remaining h /\
h_ptrs h2 = h_ptrs h1 /\ h_stream_init h2 <> 0).
{ subst h2. destruct (negb (ogg_page_serialno hdr =? os_serialno (h_os h1))).
- destruct (ogg_stream_reset_serialno (h_os h1) (ogg_page_serialno hdr)) as [rr os2] eqn:Er.
pose proof (ogg_stream_reset_serialno_frame _ _ _ _ Er) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
pose proof Ros as (Rbl & Rinv & Rbs & Rls & RRl).
pose proof (ogg_stream_reset_serialno_inv _ _ _ _ Rinv Er) as Rinv2.
pose proof (ogg_stream_reset_serialno_body_inv _ _ _ _ Rbo Er) as Rbo2.
cbn. split; [| split; [| split; [exact O1| split; [exact R1| split; [| exact SI1]]]]].
+ unfold hinv_obj; cbn. split; [exact Rsy|]. split.
{ unfold os_ok. split; [unfold os_blocks_ok; rewrite Q1, Q2, Q3; exact Rbl|]. split; [exact Rinv2|]. rewrite Q4, Q5. split; [lia|]. split; [lia|].
eapply os_reall_frame; [exact Q1| exact Q2| exact Q3| rewrite Q4; lia| rewrite Q5; lia| exact RRl]. }
split; [exact Rbo2|]. split; [intros Hz; exfalso; exact (SI1 Hz)|].
split; [exact Rb|]. split; [exact Rown|]. split; [exact Rpc| exact Rst].
+ unfold os_le in *. rewrite Q4, Q5. pose proof Rinv2 as (W1 & W2 & _). pose proof (body_inv_fill_nonneg _ Rbo2). lia.
+ unfold h_ptrs, os_ptrs; cbn. rewrite Q1, Q2, Q3. reflexivity.
- split; [exact RO|]. split; [exact OL1|]. split; [exact O1|]. split; [exact R1|]. split; [reflexivity| exact SI1]. }
clearbody h2. destruct H2 as ((Tsy & Tos & Tbo & Tsi & Tb & Town & Tpc & Tst) & OL2 & O2 & R2 & P2 & SI2).
rewrite <- P2.

pose proof OL2 as (OL2a & OL2b & OL2c & OL2d). unfold c, consumed in OL2a, OL2b, OL2c, OL2d, C0'.
eapply mspec_bind.
{ eapply own_perm; [| apply (PAGEIN (sy_ptrs (h_oy h2) ++ sb_chars (h_bits h2) :: opt_dec_ptrs (h_st h2) ++ X) (h_os h2) hdr body Tos Tbo Plac Pn26 Pzs)].
- unfold h_ptrs. perm_solve.
- unfold MMAP_THRESHOLD, MAX_FUZZ_SIZE in *. lia.
- unfold MMAP_THRESHOLD, MAX_FUZZ_SIZE in *. lia. }
intros [rp os3]. cbn beta iota. apply mspec_pure. intros (POK & PBO & PLF & PBF & PLS & PBS).
set (h3 := set_ogg h2 (h_oy h2) os3).
assert (I3 : hinv L h3 /\ h_oy h3 = oy1 /\ h_bytes_remaining h3 = h_bytes_remaining h).
{ subst h3. split; [split|].
- unfold hinv_obj; cbn. split; [exact Tsy|]. split; [exact POK|]. split; [exact PBO|]. split; [intros Hz; exfalso; exact (SI2 Hz)|].
split; [exact Tb|]. split; [exact Town|]. split; [exact Tpc| exact Tst].
- unfold hinv_budget, consumed, pend in *; cbn. rewrite O2, R2. subst h0; cbn in *. unfold MAX_FUZZ_SIZE in *. lia.
- cbn. auto. }
destruct I3 as (I3 & O3 & R3).
apply (own_perm _ (h_ptrs h3 ++ X)). { subst h3. unfold h_ptrs; cbn. perm_solve. }
cbv zeta. fold h3.
destruct (granule_step h3 hdr) as [skip|].
2:{ eapply mspec_seq; [apply cleanup_spec; exact (proj1 I3)|]. intros _. apply mspec_ret. intros s mo H. exact H. }
set (h4 := set_granule h3 (ogg_page_granulepos hdr) skip).
assert (I4 : hinv L h4 /\ h_oy h4 = oy1 /\ h_bytes_remaining h4 = h_bytes_remaining h /\ h_ptrs h4 = h_ptrs h3).
{ subst h4 h3. destruct I3 as [IO IB]. split; [split|].
- unfold hinv_obj in *; cbn in *. exact IO.
- unfold hinv_budget, consumed, pend in *; cbn in *. exact IB.
- cbn. auto. }
destruct I4 as (I4 & O4 & R4 & P4). rewrite <- P4.
eapply mspec_bind.
{ apply (packet_loop_spec L X (packet_fuel (h_os h4)) h4 0 I4). unfold packet_fuel, pk_meas. lia. }
intros [h5|]; cbn beta iota.
2:{ apply mspec_ret. intros s mo H. exact H. }
apply mspec_pure. intros (I5 & O5 & R5 & S5).
eapply mspec_post.
{ apply IH; [exact I5|]. unfold pg_meas, pend in *. rewrite O5, O4. subst h0; cbn in *.
destruct C0 as (C1 & C2 & C3). rewrite Phl2 in C0'. pose proof (zlength_nonneg body). unfold consumed, pend in *; cbn in *. lia. }
intros [h6|] s mo; [|intros H; exact H]. intros (H & I6 & R6). split; [exact H|]. split; [exact I6|]. rewrite R6, R5, R4. reflexivity.
Qed.

#[using="Type"] Lemma bytes_ok_payload_ztake : forall n (l : list Z), bytes_ok l -> bytes_ok (ztake n l).
Proof. intros. apply bytes_ok_ztake. assumption. Qed.

#[using="Hcal Hmal_big Hrea Hfree Hperm Hnotify Hwarning PTH DINIT DDEST DEC BREAD OSCLR SYBUF PAGEIN"] Lemma chunk_loop_spec : forall L X payload fuel h,
zlength payload = L -> bytes_ok payload -> hinv L h -> (Z.to_nat (h_bytes_remaining h) < fuel)%nat ->
mspec (own (h_ptrs h ++ X)) (chunk_loopH fuel payload h)
(fun r s mo => match r with Returned => own X s mo | Cont h' => own (h_ptrs h' ++ X) s mo /\ hinv_obj h' end).
Proof.
intros L X payload fuel. induction fuel as [|fuel IH]; intros h HL Hpl Hinv Hfuel; [lia|].
pose proof Hinv as [(Hsy & Hos & Hbo & Hsi & Hb & Hown & Hpc & Hst) HB].
pose proof HB as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8). unfold consumed, pend in B3, B4, B5, B6, B7, B8.
cbn [chunk_loop].
set (nb := if CHUNK <? h_bytes_remaining h then CHUNK else h_bytes_remaining h).
assert (Hnb : 0 <= nb <= h_bytes_remaining h /\ nb <= CHUNK /\ (nb < h_bytes_remaining h -> nb = CHUNK)).
{ subst nb. unfold CHUNK. destruct (Z.ltb_spec 200 (h_bytes_remaining h)); lia. }
destruct Hnb as (Hnb1 & Hnb2 & Hnb3).
eapply mspec_bind.
{ eapply own_perm; [| apply (SYBUF (os_ptrs (h_os h) ++ sb_chars (h_bits h) :: opt_dec_ptrs (h_st h) ++ X) (h_oy h) nb ltac:(lia) Hsy)].
- unfold h_ptrs. perm_solve.
- unfold MMAP_THRESHOLD, MAX_FUZZ_SIZE, CHUNK in *. lia. }
intros [data oy1]. cbn beta iota. apply mspec_pure. intros [Hsyok1 Hcase].
pose proof Hsyok1 as (Hsy2' & Hst1 & Hnul1 & HRl1). pose proof Hsy2' as [Hsy1' _]. pose proof Hsy1' as (SA & SB & _).
set (h0 := set_ogg h oy1 (h_os h)).

assert (CONT : forall oy2, sync_inv2 oy2 -> 0 <= sy_storage oy2 -> (sy_data oy2 = None -> sy_storage oy2 = 0) ->
sy_data oy2 = sy_data oy1 -> sy_fill oy2 + nb <= zlength (sy_buf oy2) ->
0 <= sy_fill oy2 - sy_returned oy2 <= sy_fill (h_oy h) - sy_returned (h_oy h) ->
mspec (own (sy_ptrs oy1 ++ os_ptrs (h_os h) ++ sb_chars (h_bits h) :: opt_dec_ptrs (h_st h) ++ X))
(let '(r, oy) := ogg_sync_wrote oy2 nb in
let h1 := set_bytes_remaining h0 oy (h_bytes_remaining h - nb) in
o <- page_loopH (page_fuel (h_oy h1)) h1 ;;
match o with
| Returned => mret Returned
| Cont h2 => if h_bytes_remaining h2 <=? 0 then mret (Cont h2) else chunk_loopH fuel payload h2
end)
(fun r s mo => match r with Returned => own X s mo | Cont h' => own (h_ptrs h' ++ X) s mo /\ hinv_obj h' end)).
{ intros oy2 W1 W2 W3 W4 W5 W6.
destruct (ogg_sync_wrote oy2 nb) as [rw oy3] eqn:Ew.
pose proof (ogg_sync_wrote_inv oy2 nb rw oy3 (proj1 W1) ltac:(lia) W5 Ew) as (V1 & V2 & V3 & V4 & V5 & V6 & V7).
pose proof (ogg_sync_wrote_inv2 oy2 nb rw oy3 W1 ltac:(lia) W5 Ew) as V8.
cbv zeta. set (h1 := set_bytes_remaining h0 oy3 (h_bytes_remaining h - nb)).
assert (Hfill3 : sy_fill oy3 = sy_fill oy2 \/ sy_fill oy3 = sy_fill oy2 + nb).
{ destruct (Z.eq_dec rw 0) as [Er|Er]; [right; apply V3; exact Er| left]. rewrite (V4 Er). reflexivity. }
assert (I1 : hinv L h1).
{ split.
- unfold hinv_obj; subst h1 h0; cbn. split.
{ split; [exact V8|]. unfold sy_reall. rewrite V6, V7. split; [exact W2|]. split; [exact W3|]. rewrite W4. exact HRl1. }
repeat (split; [assumption|]). exact Hst.
- unfold hinv_budget, consumed, pend; subst h1 h0; cbn. rewrite V5. unfold MAX_FUZZ_SIZE in *. lia. }
assert (P1 : h_ptrs h1 = sy_ptrs oy1 ++ os_ptrs (h_os h) ++ sb_chars (h_bits h) :: opt_dec_ptrs (h_st h)).
{ subst h1 h0. unfold h_ptrs, sy_ptrs; cbn. rewrite V7, W4. reflexivity. }
apply (own_perm _ (h_ptrs h1 ++ X)). { rewrite P1. perm_solve. }
eapply mspec_bind. { apply (page_loop_spec L X (page_fuel (h_oy h1)) h1 I1). unfold page_fuel, pg_meas, pend. subst h1; cbn. lia. }
intros [h2|]; cbn beta iota.
2:{ apply mspec_ret. intros s mo H. exact H. }
apply mspec_pure. intros [I2 R2]. subst h1 h0. cbn in R2.
apply mspec_if; intros Hdone.
- apply mspec_ret. intros s mo H. split; [exact H| exact (proj1 I2)].
- apply IH; [exact HL| exact Hpl| exact I2|]. apply Z.leb_gt in Hdone. rewrite R2 in Hdone |- *. unfold CHUNK in *. lia. }
destruct Hcase as (Hret1 & Hfill1 & Hres).
destruct data as [[q off]|].
- destruct Hres as (-> & Hd1 & Hroom).
pose proof (sync_write_inv2 oy1 (ztake nb payload) Hsy2' (bytes_ok_ztake nb _ Hpl)) as SW2.
pose proof (sync_write_inv oy1 (ztake nb payload) Hsy1' (bytes_ok_ztake nb _ Hpl)) as (SW1 & SWlen & SWf & SWr & SWs).
cbn beta iota.
apply (CONT (sync_write oy1 (sy_fill oy1) (ztake nb payload)) SW2).
+ rewrite SWs. exact Hst1.
+ unfold sync_write; cbn. exact Hnul1.
+ reflexivity.
+ rewrite SWlen, SWf. rewrite zlength_ztake by lia. lia.
+ rewrite SWf, SWr. lia.
- rewrite Hres in *.
destruct (Z.ltb_spec 0 0); [lia|].
apply (CONT oy1 Hsy2' Hst1 Hnul1 eq_refl); lia.
Qed.

#[using="Hcal reall Hmal_big Hcal_big Hrea Hfree Hperm Hnotify Hwarning PTH DINIT DDEST DEC BINIT BINIT_some BREAD OSCLR SYBUF PAGEIN"] Theorem LLVMFuzzerTestOneInput_spec : forall X payload, bytes_ok payload ->
mspec (own X) (LLVMFuzzerTestOneInputH payload) (fun _ => own X).
Proof.
intros X payload Hpl. unfold LLVMFuzzerTestOneInput.
apply mspec_if; intros Hbig. { apply mspec_ret. intros s mo H. exact H. }
apply Z.ltb_ge in Hbig.
eapply mspec_bind; [apply mspec_some; [apply BINIT| apply BINIT_some]|]. intros [bits|]; cbn beta iota.
2:{ apply mspec_munr. }
apply mspec_pure. intros (Bok & Bown & Bnb & Brl & Bsz).
set (h := mkH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
assert (I : hinv (zlength payload) h).
{ pose proof (zlength_nonneg payload). split.
- unfold hinv_obj; subst h; cbn. split; [apply ogg_sync_init_ok|]. split; [apply stream_zero_ok|]. split; [apply stream_zero_body_inv|].
split; [intros _; reflexivity|]. split; [split; [exact Bok|]; split; [exact Brl| rewrite Bsz; unfold REALL_MIN, MAX_CHARS_PER_FRAME; lia]|].
split; [rewrite Bown; lia|]. split; [lia| reflexivity].
- unfold hinv_budget, consumed, pend; subst h; cbn. unfold MAX_FUZZ_SIZE in *. lia. }
assert (P : h_ptrs h = [sb_chars bits]) by reflexivity.
eapply mspec_bind.
{ eapply own_perm; [| apply (chunk_loop_spec (zlength payload) X payload (chunk_fuel (zlength payload)) h eq_refl Hpl I)].
- rewrite P. apply Permutation_refl.
- unfold chunk_fuel; subst h; cbn. lia. }
intros [h'|]; cbn beta iota.
- apply mspec_pure. intros IO'. eapply mspec_seq; [apply cleanup_spec; exact IO'|]. intros _. apply mspec_ret. intros s mo H. exact H.
- apply mspec_ret. intros s mo H. exact H.
Qed.
End HarnessSafe.
