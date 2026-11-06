(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1ck X1cv.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0j5 X0ec X001 X00b X000 X04b X07z X05o X05s X08k.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X19o X14x X0r0 X0ra X0qz X0v9 X0wl X0zb.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19o OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0qz OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zb.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition uw_site (m : mem) (site : Z) (s0 : word) (usp lo : Z) : Prop :=
exists ras, In (site :: ras) SITE_TRACES
/\ match ras with [] => not_frame lo (bv_unsigned s0) | _ :: _ => uw_chain USTACK_TOP m usp (bv_unsigned s0) ras end.

Lemma uw_site_ch : forall W (m m' : mem) site s0 usp usp' lo,
uw_site m site s0 usp lo -> munch W m m' -> wmono bsegs m m' -> Forall (fun iv => snd iv <= usp) W ->
lo <= usp' -> usp' <= usp -> 0 <= usp' < 2^64 -> 0 <= site < 2^64 ->
unwind_ch m' (Z_to_bv 64 site) s0 (Z_to_bv 64 usp').
Proof.
intros W m m' site s0 usp usp' lo (ras & IN & CH) MU WM BEL LO1 LO2 R1 R2.
exists ras. rewrite !unsigned_lit by lia. split; [exact IN|].
destruct ras as [|r ras].
- cbn [uw_chain]. exact (not_frame_stop lo _ usp' CH LO1).
- apply (uw_chain_sp USTACK_TOP m' usp usp' _ r ras); [| exact LO2].
apply (uw_chain_munch USTACK_TOP W m m' (r :: ras) usp _ CH MU WM). intros a Ha _. exact (below_disjoint W usp BEL a Ha).
Qed.

Lemma uw_site_nf : forall (m : mem) site s0 usp lo, In site ALLOC_RAS -> not_frame lo (bv_unsigned s0) -> uw_site m site s0 usp lo.
Proof.
intros m site s0 usp lo IN NF. exists []. split; [| exact NF].
unfold SITE_TRACES. apply in_or_app. left. apply in_map_iff. exists site. split; [reflexivity| exact IN].
Qed.

Ltac pres_ex_transport PRES WM tac :=
lazymatch type of PRES with
| rt_pres_ex ?live ?frames ?sp ?d ?n ?m ?m' =>
repeat match goal with
| H : rw_cells bsegs m ?A ?cs |- _ =>
first [ let H' := fresh "T" in
assert (H' : rw_cells bsegs m' A cs)
by (apply (rw_cells_agree bsegs m m' A cs H);
[ apply (agree_of_pres_ex live frames sp d n m m' _ PRES); intros ? ?Hx; cps_sizes Hx; split; [aclient_tac tac | tac] | exact WM ]);
clear H; rename H' into H
| idtac "note: dropping hypothesis (inside the destination range, or not client memory for this call):" H; clear H ]
| H : ro_cells bsegs m ?A ?cs |- _ =>
first [ let H' := fresh "T" in
assert (H' : ro_cells bsegs m' A cs)
by (apply (ro_cells_agree bsegs m m' A cs H); apply (agree_of_pres_ex live frames sp d n m m' _ PRES); intros ? ?Hx; cps_sizes Hx;
split; [aclient_tac tac | tac]);
clear H; rename H' into H
| idtac "note: dropping hypothesis (inside the destination range, or not client memory for this call):" H; clear H ]
end
end.

Ltac cps_pf_pres_ex PRES :=
lazymatch type of PRES with
| rt_pres_ex ?live ?frames ?sp ?d ?n ?m ?m' =>
lazymatch goal with
| PF : rt_pres_fp ?L0 ?F0 ?U0 ?W0 ?m0 m |- _ =>
let PF' := fresh "PF" in
assert (PF' : rt_pres_fp L0 F0 U0 W0 m0 m')
by (apply (pres_fp_trans L0 F0 U0 W0 m0 m m' PF);
let a := fresh "a" in let Ha := fresh "Ha" in let Ho := fresh "Ho" in
intros a Ha Ho; apply PRES;
[ apply (aclient_mono L0 F0 U0 live frames sp _ Ha);
[ first [ now auto | intros ? ?Hi; repeat match goal with E : _ = _ |- _ => rewrite E end; auto with datatypes ]
| first [ now auto | intros ? ?Hi; repeat match goal with E : _ = _ |- _ => rewrite E end; auto with datatypes ]
| ulc ]
|
cbn [outside] in Ho;
repeat match goal with NA : forall x, aclient L0 F0 U0 x -> _ |- _ => pose proof (NA _ Ha); clear NA end;
ulc ]);
clear PF; rename PF' into PF
| _ => idtac
end
end.

Tactic Notation "cps_unpack_ex" hyp(Hc) "as" simple_intropattern(P) :=
lazymatch type of Hc with
| ASTA ?RT ?Σ' ?PMc ?Pm ?c =>
let ms := fresh "ms" in let Hc' := fresh "Hc" in let PO := fresh "PO" in
destruct (ASTA_unpack RT Σ' PMc Pm c Hc) as (ms & PO & Hc'); clear Hc; cbv beta in PO;
destruct PO as P;
repeat match goal with
| RS : ret_stF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => cps_ret RS
| RS : ret_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => cps_ret RS
end;
repeat match goal with
| H : context [bv_unsigned (Z_to_bv 64 ?z)] |- _ => rewrite (unsigned_lit z) in H by ulc
end;
match goal with
| PRES : rt_pres_ex _ _ _ _ _ ?m ?m', WM : wmono bsegs ?m ?m' |- _ =>
pres_ex_transport PRES WM ltac:(ulc); cps_pf_pres_ex PRES;
try match goal with A : ART _ _ m |- _ => clear A end;
try match goal with MI : mem_inv bsegs m |- _ => clear MI end;
try match goal with ST : stk bsegs m _ _ |- _ => clear ST end
end
end.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition uw_site (m : mem) (site : Z) (s0 : word) (usp lo : Z) : Prop :=
exists ras, In (site :: ras) SITE_TRACES
/\ match ras with [] => not_frame lo (bv_unsigned s0) | _ :: _ => uw_chain USTACK_TOP m usp (bv_unsigned s0) ras end.

Lemma uw_site_ch : forall W (m m' : mem) site s0 usp usp' lo,
uw_site m site s0 usp lo -> munch W m m' -> wmono asegs m m' -> Forall (fun iv => snd iv <= usp) W ->
lo <= usp' -> usp' <= usp -> 0 <= usp' < 2^64 -> 0 <= site < 2^64 ->
unwind_ch m' (Z_to_bv 64 site) s0 (Z_to_bv 64 usp').
Proof.
intros W m m' site s0 usp usp' lo (ras & IN & CH) MU WM BEL LO1 LO2 R1 R2.
exists ras. rewrite !unsigned_lit by lia. split; [exact IN|].
destruct ras as [|r ras].
- cbn [uw_chain]. exact (not_frame_stop lo _ usp' CH LO1).
- apply (uw_chain_sp USTACK_TOP m' usp usp' _ r ras); [| exact LO2].
apply (uw_chain_munch USTACK_TOP W m m' (r :: ras) usp _ CH MU WM). intros a Ha _. exact (below_disjoint W usp BEL a Ha).
Qed.

Lemma uw_site_nf : forall (m : mem) site s0 usp lo, In site ALLOC_RAS -> not_frame lo (bv_unsigned s0) -> uw_site m site s0 usp lo.
Proof.
intros m site s0 usp lo IN NF. exists []. split; [| exact NF].
unfold SITE_TRACES. apply in_or_app. left. apply in_map_iff. exists site. split; [reflexivity| exact IN].
Qed.

Ltac pres_ex_transport PRES WM tac :=
lazymatch type of PRES with
| rt_pres_ex ?live ?frames ?sp ?d ?n ?m ?m' =>
repeat match goal with
| H : rw_cells asegs m ?A ?cs |- _ =>
first [ let H' := fresh "T" in
assert (H' : rw_cells asegs m' A cs)
by (apply (rw_cells_agree asegs m m' A cs H);
[ apply (agree_of_pres_ex live frames sp d n m m' _ PRES); intros ? ?Hx; cps_sizes Hx; split; [aclient_tac tac | tac] | exact WM ]);
clear H; rename H' into H
| idtac "note: dropping hypothesis (inside the destination range, or not client memory for this call):" H; clear H ]
| H : ro_cells asegs m ?A ?cs |- _ =>
first [ let H' := fresh "T" in
assert (H' : ro_cells asegs m' A cs)
by (apply (ro_cells_agree asegs m m' A cs H); apply (agree_of_pres_ex live frames sp d n m m' _ PRES); intros ? ?Hx; cps_sizes Hx;
split; [aclient_tac tac | tac]);
clear H; rename H' into H
| idtac "note: dropping hypothesis (inside the destination range, or not client memory for this call):" H; clear H ]
end
end.

Ltac cps_pf_pres_ex PRES :=
lazymatch type of PRES with
| rt_pres_ex ?live ?frames ?sp ?d ?n ?m ?m' =>
lazymatch goal with
| PF : rt_pres_fp ?L0 ?F0 ?U0 ?W0 ?m0 m |- _ =>
let PF' := fresh "PF" in
assert (PF' : rt_pres_fp L0 F0 U0 W0 m0 m')
by (apply (pres_fp_trans L0 F0 U0 W0 m0 m m' PF);
let a := fresh "a" in let Ha := fresh "Ha" in let Ho := fresh "Ho" in
intros a Ha Ho; apply PRES;
[ apply (aclient_mono L0 F0 U0 live frames sp _ Ha);
[ first [ now auto | intros ? ?Hi; repeat match goal with E : _ = _ |- _ => rewrite E end; auto with datatypes ]
| first [ now auto | intros ? ?Hi; repeat match goal with E : _ = _ |- _ => rewrite E end; auto with datatypes ]
| ulc ]
|
cbn [outside] in Ho;
repeat match goal with NA : forall x, aclient L0 F0 U0 x -> _ |- _ => pose proof (NA _ Ha); clear NA end;
ulc ]);
clear PF; rename PF' into PF
| _ => idtac
end
end.

Tactic Notation "cps_unpack_ex" hyp(Hc) "as" simple_intropattern(P) :=
lazymatch type of Hc with
| ASTA ?RT ?Σ' ?PMc ?Pm ?c =>
let ms := fresh "ms" in let Hc' := fresh "Hc" in let PO := fresh "PO" in
destruct (ASTA_unpack RT Σ' PMc Pm c Hc) as (ms & PO & Hc'); clear Hc; cbv beta in PO;
destruct PO as P;
repeat match goal with
| RS : ret_stF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => cps_ret RS
| RS : ret_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => cps_ret RS
end;
repeat match goal with
| H : context [bv_unsigned (Z_to_bv 64 ?z)] |- _ => rewrite (unsigned_lit z) in H by ulc
end;
match goal with
| PRES : rt_pres_ex _ _ _ _ _ ?m ?m', WM : wmono asegs ?m ?m' |- _ =>
pres_ex_transport PRES WM ltac:(ulc); cps_pf_pres_ex PRES;
try match goal with A : ART _ _ m |- _ => clear A end;
try match goal with MI : mem_inv asegs m |- _ => clear MI end;
try match goal with ST : stk asegs m _ _ |- _ => clear ST end
end
end.
