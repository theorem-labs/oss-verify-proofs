(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05s X0ae X09p.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0wl X110 X10c.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X110 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10c.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Tactic Notation "ogg_unpackL" hyp(Hc) "as" simple_intropattern(P) :=
lazymatch type of Hc with
| ASTA ?RT ?Σ' ?PMc ?Pm ?c =>
let ms := fresh "ms" in let Hc' := fresh "Hc" in let PO := fresh "PO" in
destruct (ASTA_unpack RT Σ' PMc Pm c Hc) as (ms & PO & Hc'); clear Hc; cbv beta in PO;
destruct PO as P;
repeat match goal with
| RS : ret_stL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => cps_ret RS
end;
repeat match goal with
| H : context [bv_unsigned (Z_to_bv 64 ?z)] |- _ =>
lazymatch type of H with bv_unsigned (Z_to_bv 64 _) = _ => fail | _ => idtac end;
rewrite (unsigned_lit z) in H by ulc
end;
let m' := lazymatch type of Hc' with ASTA _ _ _ (eq (MS _ _ _ _ _ ?mm _)) _ => mm end in
match goal with
| PRES : rt_pres_fp _ _ _ _ ?m m' |- _ => cps_unpack_tr PRES m
end
end.

Lemma sync_rep_transport : forall W (m m' : mem) A D (sy : sync_st bptr) bytes,
munch W m m' -> wmono bsegs m m' -> disjoint_from W A 32 -> disjoint_from W D (Z.of_nat (length bytes)) ->
sync_rep m A D sy bytes -> sync_rep m' A D sy bytes.
Proof.
intros W m m' A D sy bytes MU WM DA DD (SY & FOK & DAT & SEP). split; [| split; [exact FOK| split; [| exact SEP]]].
- apply (rw_cells_transport bsegs W m m' A _ SY MU WM). exact DA.
- unfold sync_data in *. destruct (sy_data sy); [| exact DAT]. destruct DAT as (X1 & ARR & X3 & X4 & X5).
split; [exact X1|]. split; [exact (u8arr_transport bsegs W m m' D bytes ARR MU WM DD)|]. exact (conj X3 (conj X4 X5)).
Qed.

Lemma sync_data_same : forall (m : mem) D (sy sy2 : sync_st bptr) bytes,
sy_data sy2 = sy_data sy -> sy_buf sy2 = sy_buf sy -> sy_storage sy2 = sy_storage sy -> sync_data m D sy bytes -> sync_data m D sy2 bytes.
Proof. intros m D sy sy2 bytes E1 E2 E3 H. unfold sync_data in *. rewrite E1, E2, E3. exact H. Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Tactic Notation "ogg_unpackL" hyp(Hc) "as" simple_intropattern(P) :=
lazymatch type of Hc with
| ASTA ?RT ?Σ' ?PMc ?Pm ?c =>
let ms := fresh "ms" in let Hc' := fresh "Hc" in let PO := fresh "PO" in
destruct (ASTA_unpack RT Σ' PMc Pm c Hc) as (ms & PO & Hc'); clear Hc; cbv beta in PO;
destruct PO as P;
repeat match goal with
| RS : ret_stL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => cps_ret RS
end;
repeat match goal with
| H : context [bv_unsigned (Z_to_bv 64 ?z)] |- _ =>
lazymatch type of H with bv_unsigned (Z_to_bv 64 _) = _ => fail | _ => idtac end;
rewrite (unsigned_lit z) in H by ulc
end;
let m' := lazymatch type of Hc' with ASTA _ _ _ (eq (MS _ _ _ _ _ ?mm _)) _ => mm end in
match goal with
| PRES : rt_pres_fp _ _ _ _ ?m m' |- _ => cps_unpack_tr PRES m
end
end.

Lemma sync_rep_transport : forall W (m m' : mem) A D (sy : sync_st bptr) bytes,
munch W m m' -> wmono asegs m m' -> disjoint_from W A 32 -> disjoint_from W D (Z.of_nat (length bytes)) ->
sync_rep m A D sy bytes -> sync_rep m' A D sy bytes.
Proof.
intros W m m' A D sy bytes MU WM DA DD (SY & FOK & DAT & SEP). split; [| split; [exact FOK| split; [| exact SEP]]].
- apply (rw_cells_transport asegs W m m' A _ SY MU WM). exact DA.
- unfold sync_data in *. destruct (sy_data sy); [| exact DAT]. destruct DAT as (X1 & ARR & X3 & X4 & X5).
split; [exact X1|]. split; [exact (u8arr_transport asegs W m m' D bytes ARR MU WM DD)|]. exact (conj X3 (conj X4 X5)).
Qed.

Lemma sync_data_same : forall (m : mem) D (sy sy2 : sync_st bptr) bytes,
sy_data sy2 = sy_data sy -> sy_buf sy2 = sy_buf sy -> sy_storage sy2 = sy_storage sy -> sync_data m D sy bytes -> sync_data m D sy2 bytes.
Proof. intros m D sy sy2 bytes E1 E2 E3 H. unfold sync_data in *. rewrite E1, E2, E3. exact H. Qed.
