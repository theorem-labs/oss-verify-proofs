(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2 Require Import TopLevel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma valid_input_sv48 : forall inp, valid_input inp -> in_va_size inp = Sv48.
Proof. intros inp H. unfold valid_input in H. decompose [and] H. assumption. Qed.   (* [comment removed for export] *)

Lemma valid_entry_sp : forall img en inp,
  valid_input inp -> valid_entry img en inp -> valid_sp (en_sp en).
Proof.
  intros [segs pc ph] [sp brk0 mbase rnd] inp Hvi Hve.
  apply (valid_entry_sv48 _ _ _ (valid_input_sv48 inp Hvi)) in Hve. cbn [en_sp]. exact (proj1 Hve).
Qed.

Lemma valid_entry_brk' : forall segs pc ph en inp,
  valid_entry (mkImage segs pc ph) en inp -> valid_brk segs (en_brk en).
Proof.
  intros segs pc ph [sp brk0 mbase rnd] inp Hve. unfold valid_entry in Hve. cbn [valid_entry_va en_brk] in *. tauto.
Qed.

(* [comment removed for export] *)
Lemma mo0_ceil : forall segs lim en inp, valid_sp (en_sp en) ->
  @alloc_ceiling (ceil_of_sp (en_sp en)) = page_round_down_Z (alloc_top (m_vmmaps (mo0 segs lim en inp))).
Proof.
  intros segs lim en inp Hsp. symmetry. apply alloc_top_ceil_of_sp; [exact Hsp|].
  unfold mo0. rewrite m_vmmaps_init_model. reflexivity.
Qed.

Lemma mo0_ceil_valid : forall segs pc ph lim en inp,
  valid_input inp -> valid_entry (mkImage segs pc ph) en inp ->
  @alloc_ceiling (ceil_of_sp (en_sp en)) = page_round_down_Z (alloc_top (m_vmmaps (mo0 segs lim en inp))).
Proof. intros segs pc ph lim en inp Hvi Hve. apply mo0_ceil. exact (valid_entry_sp _ _ _ Hvi Hve). Qed.

(* [comment removed for export] *)
Lemma entry_ceil_le_top : forall img en inp,
  valid_input inp -> valid_entry img en inp ->
  @alloc_ceiling (ceil_of_sp (en_sp en)) <= bv_unsigned (en_sp en) - 8388608.
Proof.
  intros img en inp Hvi Hve. pose proof (ceil_of_sp_le_top _ (valid_entry_sp _ _ _ Hvi Hve)) as H.
  rewrite stack_max_size_val in H. exact H.
Qed.
