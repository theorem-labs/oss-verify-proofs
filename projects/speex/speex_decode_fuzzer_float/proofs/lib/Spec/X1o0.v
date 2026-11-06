(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bt X1c1.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qy X1nw X1qz X1nt X1rg X1rh X1re X1od
X1r8 X1nu X1ob X1o3.
Import ListNotations.
Import X1bt.Exc.
Open Scope Z_scope.

Class Erasable (A : Type) : Type := mkErasable { erased : Type; erase : A -> erased }.
Arguments erased A {_}.
Arguments erase {A _} _.

Definition Er_id (A : Type) : Erasable A := {| erased := A; erase := fun x => x |}.
#[global] Instance Er_Z : Erasable Z := Er_id Z.
#[global] Instance Er_bool : Erasable bool := Er_id bool.
#[global] Instance Er_nat : Erasable nat := Er_id nat.
#[global] Instance Er_unit : Erasable unit := Er_id unit.
#[global] Instance Er_listZ : Erasable (list Z) := Er_id (list Z).
#[global] Instance Er_spx_header : Erasable spx_header := Er_id spx_header.
#[global] Instance Er_page : Erasable page := Er_id page.
#[global] Instance Er_packet : Erasable packet := Er_id packet.

#[global] Instance Er_prod {A B} `{Erasable A} `{Erasable B} : Erasable (A * B) :=
{| erased := (erased A * erased B)%type; erase := fun p => (erase (fst p), erase (snd p)) |}.
#[global] Instance Er_option {A} `{Erasable A} : Erasable (option A) :=
{| erased := option (erased A); erase := option_map erase |}.
#[global] Instance Er_sum {A B} `{Erasable A} `{Erasable B} : Erasable (A + B) :=
{| erased := (erased A + erased B)%type;
erase := fun v => match v with inl a => inl (erase a) | inr b => inr (erase b) end |}.

Definition Er_ptr (ptr : Type) : Erasable ptr := {| erased := unit; erase := fun _ => tt |}.

#[global] Instance Er_bits {ptr} : Erasable (bits_st ptr) := {| erased := bits_st unit; erase := pm_bits er |}.
#[global] Instance Er_sync {ptr} : Erasable (sync_st ptr) := {| erased := sync_st unit; erase := pm_sync er |}.
#[global] Instance Er_stream {ptr} : Erasable (stream_st ptr) := {| erased := stream_st unit; erase := pm_stream er |}.
#[global] Instance Er_nb {ptr} : Erasable (nb_state ptr) := {| erased := nb_state unit; erase := pm_nb er |}.
#[global] Instance Er_sbd {ptr} : Erasable (sbd_state ptr) := {| erased := sbd_state unit; erase := pm_sbd er |}.
#[global] Instance Er_dec {ptr} : Erasable (dec_state ptr) := {| erased := dec_state unit; erase := pm_dec er |}.
#[global] Instance Er_h {ptr} : Erasable (hstate ptr) := {| erased := hstate unit; erase := pm_h er |}.
#[global] Instance Er_outcome {ptr} : Erasable (outcome ptr) := {| erased := outcome unit; erase := pm_outcome er |}.

Definition pm_search {ptr ptr'} (f : ptr -> ptr') (r : nb_search_res (ptr:=ptr)) : nb_search_res (ptr:=ptr') :=
match r with NbReturn v b => NbReturn v (pm_bits f b) | NbMode m b => NbMode m (pm_bits f b) end.
#[global] Instance Er_search {ptr} : Erasable (nb_search_res (ptr:=ptr)) :=
{| erased := nb_search_res (ptr:=unit); erase := pm_search er |}.

Definition pm_snd {A B B'} (g : B -> B') (p : A * B) : A * B' := (fst p, g (snd p)).

Ltac rnorm :=
cbn [erase erased Er_id Er_Z Er_bool Er_nat Er_unit Er_listZ Er_spx_header Er_page Er_packet Er_prod Er_option Er_sum Er_ptr
Er_bits Er_sync Er_stream Er_nb Er_sbd Er_dec Er_h Er_outcome Er_search fst snd option_map er pm_snd
pm_bits pm_sync pm_stream pm_nb pm_sbd pm_dec pm_h pm_outcome pm_search
sb_chars sb_data sb_nbBits sb_charPtr sb_bitPtr sb_owner sb_overflow sb_buf_size
sy_data sy_buf sy_storage sy_fill sy_returned sy_unsynced sy_headerbytes sy_bodybytes
os_body_data os_body os_body_storage os_body_fill os_body_returned os_lacing_vals os_lacing os_granule_vals os_granules
os_lacing_storage os_lacing_fill os_lacing_packet os_lacing_returned os_header_fill os_e_o_s os_b_o_s os_serialno
os_pageno os_packetno os_granulepos
nb_blk nb_first nb_count_lost nb_sampling_rate nb_innov_save nb_pitch_gain_buf_idx nb_encode_submode
nb_submodeID nb_lpc_enh_enabled nb_stereo_cb nb_voc_offset nb_dtx_enabled nb_isWideband nb_highpass_enabled
sbd_blk sbd_mode sbd_full_frame_size sbd_frame_size sbd_subframeSize sbd_nbSubframes sbd_lpcSize sbd_first
sbd_sampling_rate sbd_lpc_enh_enabled sbd_g0_mem sbd_g1_mem sbd_excBuf sbd_old_qlsp sbd_interp_qlpc sbd_mem_sp
sbd_pi_gain sbd_exc_rms sbd_innov_save sbd_encode_submode sbd_submodeID
set_nb_first set_nb_count_lost set_nb_sampling_rate set_nb_innov_save set_nb_pitch_gain_buf_idx set_nb_submodeID
set_nb_lpc_enh_enabled set_nb_stereo_cb set_nb_voc_offset set_nb_dtx_enabled set_nb_isWideband
set_sbd_first set_sbd_sampling_rate set_sbd_lpc_enh_enabled set_sbd_innov_save set_sbd_submodeID
h_oy h_os h_bits h_st h_stream_init h_packet_count h_last_granule h_skip_samples h_nframes h_eos h_channels
h_rate h_extra_headers h_speex_serialno h_frame_size h_granule_frame_size h_bytes_remaining
set_ogg set_bits_st set_stream_init set_granule set_serialno incr_packet_count set_bytes_remaining set_header].

Section Rules.
Variable sel : option bool.
Variable X : list event -> Prop.
Context {St : Type}.
Variable K : St -> Model -> Prop.
Local Notation REL := (X1o3.REL sel X K).

Lemma REL_let {T T' A A'} (er : A -> A') (g : T -> T') (x : T) (x' : T') (f : T -> M St A) (f' : T' -> M pst A') :
x' = g x -> (forall t, REL er (f t) (f' (g t))) -> REL er (f x) (f' x').
Proof. intros -> H. apply H. Qed.

End Rules.

Create HintDb rel discriminated.
Create HintDb erw.

Ltac rel_call :=
first [ solve [auto 1 with rel nocore]
| match goal with H : _ |- _ => solve [apply H] end ].

Ltac rret_cases :=
repeat match goal with
| |- context [option_map _ ?x] => is_var x; destruct x
| |- context [match ?x with _ => _ end] =>
lazymatch x with option_map _ _ => fail | _ => idtac end;
first [ is_var x; destruct x | destruct x eqn:? ]
end.
Ltac rret := apply REL_ret; first [ reflexivity | rnorm; rret_cases; reflexivity ].

Ltac split_value t :=
match t with
| context [if ?cond then _ else _] =>
lazymatch cond with
| context [if _ then _ else _] => fail
| context [match _ with _ => _ end] => fail
| _ => first [ is_var cond; destruct cond | destruct cond eqn:? ]
end
| context [match ?y with _ => _ end] =>
lazymatch y with
| context [if _ then _ else _] => fail
| context [match _ with _ => _ end] => fail
| _ => first [ is_var y; destruct y | destruct y eqn:? ]
end
end.

Ltac rel1 :=
lazymatch goal with
| |- X1o3.REL _ _ _ _ ?c _ =>
lazymatch c with
| mret ?a => first [ rret | split_value a ]
| munr => apply REL_munr
| @mbind _ ?A ?B ?c1 _ =>
first [
lazymatch c1 with
| mbind _ _ => fail | (if _ then _ else _) => fail | (match _ with _ => _ end) => fail
| _ => split_value c1
end
| let e := constr:(@erase A _) in
eapply (REL_bind _ _ _ e); [ first [rel_call | idtac] | intros ? ] ]
| (if ?b then _ else _) =>
first [ split_value b | apply REL_if; intros ? | is_var b; destruct b | destruct b eqn:? ]
| (match ?x with _ => _ end) =>
first [ is_var x; destruct x
| split_value x
|
lazymatch goal with
| |- X1o3.REL _ _ _ _ _ (match ?x' with _ => _ end) =>
first [ constr_eq x x' | replace x' with x by reflexivity | idtac ]
| _ => idtac
end;
destruct x eqn:? ]
| _ => first [ rel_call | split_value c ]
end
end.
Ltac rstep := rnorm; cbv zeta; try (progress autorewrite with erw; rnorm); rel1.
Ltac rel := repeat rstep.
