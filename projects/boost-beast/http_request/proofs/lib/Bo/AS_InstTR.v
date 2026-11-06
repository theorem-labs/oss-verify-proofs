(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsIface AsCXXHeap AsStack0 AXPres AXFuzz_stmt AsDrvDefs AsTRList.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma TRLIST_len_nat : (length TRLIST <= 256)%nat.
Proof. pose proof TRLIST_length. lia. Qed.

(* [comment removed for export] *)
Ltac tr_closed :=
  first [ exact I
        | apply trace_okb_sound; vm_compute; reflexivity
        | apply pf_okb0_sound; vm_compute; reflexivity ].

Section ForInstance.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HTR : as_TR H = TRLIST.

  Lemma inst_incl_TR : incl TRLIST (as_TR H).
  Proof. rewrite HTR. apply incl_refl. Qed.

  Theorem inst_TR_laws : TR_laws H.
  Proof. unfold TR_laws. rewrite HTR. exact TRLIST_opnew. Qed.

  (* [comment removed for export] *)
  Theorem inst_afuzz_tr_ok : afuzz_tr_ok H.
  Proof. unfold afuzz_tr_ok. rewrite ?HTR. repeat split; tr_closed. Qed.

  Theorem inst_adrv_traces : adrv_traces H.
  Proof.
    unfold adrv_traces. rewrite !HTR. destruct TRLIST_driver as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
    split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [exact D4|]. split; [exact D5|]. split; [exact D6|].
    split; [| exact inst_afuzz_tr_ok].
    (* [comment removed for export] *)
    apply pf_okb0_sound. vm_compute. reflexivity.
  Qed.
End ForInstance.
