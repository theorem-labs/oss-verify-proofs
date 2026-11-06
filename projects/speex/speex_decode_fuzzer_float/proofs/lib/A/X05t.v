(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1df X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05s.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0wl.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma acc_agree_sh2 : forall (m m' : mem) o n, acc bsegs m o n ->
agree_on (fun x => exists i, 0 <= i < n /\ x = shad (o + i)) m m' -> acc bsegs m' o n.
Proof.
intros m m' o n H HA i Hi. destruct (H i Hi) as (b & Hb & Hok). exists b. split; [| exact Hok].
apply (bytes_at_agree bsegs m m' _ _ Hb). eapply agree_sub; [exact HA|]. intros x Hx. cbn [length] in Hx. exists i. split; [exact Hi| lia].
Qed.
Lemma frame_shadow_client2 : forall live frames sp f k o n i, In (f, k) frames -> f mod 8 = 0 -> fs_size k mod 8 = 0 -> 0 <= f ->
f <= o -> o + n <= f + fs_size k -> 0 <= i < n -> aclient live frames sp (shad (o + i)).
Proof.
intros live frames sp f k o n i Hin F8 S8 F0 Ho Hn Hi. right; right; right; right. exists f, k. split; [exact Hin|].
unfold shad. split.
- apply Z.add_le_mono_r. apply Z.div_le_mono; lia.
- apply Z.add_lt_mono_r. apply Z.div_lt_upper_bound; [lia|].
assert (E : f + fs_size k = 8 * ((f + fs_size k) / 8)) by (pose proof (Z.div_mod (f + fs_size k) 8 ltac:(lia)) as X; rewrite Zplus_mod, F8, S8 in X; cbn in X; lia).
lia.
Qed.
Lemma acc_pres_fp_frame : forall live frames sp W (m m' : mem) f k o no, rt_pres_fp live frames sp W m m' ->
In (f, k) frames -> f mod 8 = 0 -> fs_size k mod 8 = 0 -> 0 <= f -> f <= o -> o + no <= f + fs_size k ->
(forall i, 0 <= i < no -> outside W (shad (o + i))) ->
acc bsegs m o no -> acc bsegs m' o no.
Proof.
intros live frames sp W m m' f k o no PRES Hin F8 S8 F0 Ho Hn HO H. apply (acc_agree_sh2 m m' o no H).
apply (agree_of_pres_fp live frames sp W m m' _ PRES). intros x (i & Hi & ->).
split; [exact (frame_shadow_client2 live frames sp f k o no i Hin F8 S8 F0 Ho Hn Hi)| exact (HO i Hi)].
Qed.

Lemma acc_pres_ex_frame2 : forall live frames sp d n (m m' : mem) f k o no, rt_pres_ex live frames sp d n m m' ->
In (f, k) frames -> f mod 8 = 0 -> fs_size k mod 8 = 0 -> 0 <= f -> f <= o -> o + no <= f + fs_size k ->
(forall i, 0 <= i < no -> ~ (d <= shad (o + i) < d + n)) ->
acc bsegs m o no -> acc bsegs m' o no.
Proof.
intros live frames sp d n m m' f k o no PRES Hin F8 S8 F0 Ho Hn HD H. apply (acc_agree_sh2 m m' o no H).
apply (agree_of_pres_ex live frames sp d n m m' _ PRES). intros x (i & Hi & ->).
split; [exact (frame_shadow_client2 live frames sp f k o no i Hin F8 S8 F0 Ho Hn Hi)| exact (HD i Hi)].
Qed.
Lemma fs_size_mod8 : forall k, fs_size k mod 8 = 0.
Proof. intros k. unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia. replace (64 * 2 ^ Z.of_nat k) with (8 * 2 ^ Z.of_nat k * 8) by lia. apply Z_mod_mult. Qed.

Lemma shad_in_window : forall a, 0 <= a < 2^47 -> SH_LO <= shad a < SH_HI.
Proof.
intros a Ha. unfold shad, SHB, SH_LO, SH_HI.
assert (0 <= a / 8 < 17592186044416) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). lia.
Qed.

Tactic Notation "cps_unpack_lib" hyp(Hc) "as" simple_intropattern(P) :=
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
end
end.

Ltac cps_tr_lib PRES :=
pres_transport_g PRES ltac:(ulc);
lazymatch type of PRES with
| rt_pres_fp _ _ _ _ ?m _ =>
try match goal with A : ART _ _ m |- _ => clear A end;
try match goal with MI : mem_inv bsegs m |- _ => clear MI end;
try match goal with ST : stk bsegs m _ _ |- _ => clear ST end
end.

Ltac cps_pf_lib PRES SPL :=
lazymatch type of PRES with
| rt_pres_fp ?live ?frames ?sp ?W ?m ?m' =>
lazymatch goal with
| PF : rt_pres_fp ?L0 ?F0 ?U0 ?W0 ?m0 m |- _ =>
let PF' := fresh "PF" in
assert (PF' : rt_pres_fp L0 F0 U0 W0 m0 m')
by (apply (pres_fp_trans L0 F0 U0 W0 m0 m m' PF);
apply (pres_fp_of_pres_fp L0 F0 U0 W0 live frames sp W m m' PRES);
[ cps_incl | cps_incl | ulc
| let x := fresh "x" in let Hx := fresh "Hx" in let Ho := fresh "Ho" in
intros x Hx Ho; cbn [outside] in Ho |- *;
repeat (split; [ first [ tauto
| let Hs := fresh "Hs" in pose proof (SPL x Hx) as Hs;
lazymatch goal with |- ~ (?a <= x < ?b) =>
cut (x < a \/ b <= x); [ clear; lia | destruct Hs; [ right; ulc | left; ulc ] ] end ] | ]);
exact I ]);
clear PF; rename PF' into PF
end
end.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma acc_agree_sh2 : forall (m m' : mem) o n, acc asegs m o n ->
agree_on (fun x => exists i, 0 <= i < n /\ x = shad (o + i)) m m' -> acc asegs m' o n.
Proof.
intros m m' o n H HA i Hi. destruct (H i Hi) as (b & Hb & Hok). exists b. split; [| exact Hok].
apply (bytes_at_agree asegs m m' _ _ Hb). eapply agree_sub; [exact HA|]. intros x Hx. cbn [length] in Hx. exists i. split; [exact Hi| lia].
Qed.
Lemma frame_shadow_client2 : forall live frames sp f k o n i, In (f, k) frames -> f mod 8 = 0 -> fs_size k mod 8 = 0 -> 0 <= f ->
f <= o -> o + n <= f + fs_size k -> 0 <= i < n -> aclient live frames sp (shad (o + i)).
Proof.
intros live frames sp f k o n i Hin F8 S8 F0 Ho Hn Hi. right; right; right; right. exists f, k. split; [exact Hin|].
unfold shad. split.
- apply Z.add_le_mono_r. apply Z.div_le_mono; lia.
- apply Z.add_lt_mono_r. apply Z.div_lt_upper_bound; [lia|].
assert (E : f + fs_size k = 8 * ((f + fs_size k) / 8)) by (pose proof (Z.div_mod (f + fs_size k) 8 ltac:(lia)) as X; rewrite Zplus_mod, F8, S8 in X; cbn in X; lia).
lia.
Qed.
Lemma acc_pres_fp_frame : forall live frames sp W (m m' : mem) f k o no, rt_pres_fp live frames sp W m m' ->
In (f, k) frames -> f mod 8 = 0 -> fs_size k mod 8 = 0 -> 0 <= f -> f <= o -> o + no <= f + fs_size k ->
(forall i, 0 <= i < no -> outside W (shad (o + i))) ->
acc asegs m o no -> acc asegs m' o no.
Proof.
intros live frames sp W m m' f k o no PRES Hin F8 S8 F0 Ho Hn HO H. apply (acc_agree_sh2 m m' o no H).
apply (agree_of_pres_fp live frames sp W m m' _ PRES). intros x (i & Hi & ->).
split; [exact (frame_shadow_client2 live frames sp f k o no i Hin F8 S8 F0 Ho Hn Hi)| exact (HO i Hi)].
Qed.

Lemma acc_pres_ex_frame2 : forall live frames sp d n (m m' : mem) f k o no, rt_pres_ex live frames sp d n m m' ->
In (f, k) frames -> f mod 8 = 0 -> fs_size k mod 8 = 0 -> 0 <= f -> f <= o -> o + no <= f + fs_size k ->
(forall i, 0 <= i < no -> ~ (d <= shad (o + i) < d + n)) ->
acc asegs m o no -> acc asegs m' o no.
Proof.
intros live frames sp d n m m' f k o no PRES Hin F8 S8 F0 Ho Hn HD H. apply (acc_agree_sh2 m m' o no H).
apply (agree_of_pres_ex live frames sp d n m m' _ PRES). intros x (i & Hi & ->).
split; [exact (frame_shadow_client2 live frames sp f k o no i Hin F8 S8 F0 Ho Hn Hi)| exact (HD i Hi)].
Qed.
Lemma fs_size_mod8 : forall k, fs_size k mod 8 = 0.
Proof. intros k. unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia. replace (64 * 2 ^ Z.of_nat k) with (8 * 2 ^ Z.of_nat k * 8) by lia. apply Z_mod_mult. Qed.

Lemma shad_in_window : forall a, 0 <= a < 2^47 -> SH_LO <= shad a < SH_HI.
Proof.
intros a Ha. unfold shad, SHB, SH_LO, SH_HI.
assert (0 <= a / 8 < 17592186044416) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). lia.
Qed.

Tactic Notation "cps_unpack_lib" hyp(Hc) "as" simple_intropattern(P) :=
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
end
end.

Ltac cps_tr_lib PRES :=
pres_transport_g PRES ltac:(ulc);
lazymatch type of PRES with
| rt_pres_fp _ _ _ _ ?m _ =>
try match goal with A : ART _ _ m |- _ => clear A end;
try match goal with MI : mem_inv asegs m |- _ => clear MI end;
try match goal with ST : stk asegs m _ _ |- _ => clear ST end
end.

Ltac cps_pf_lib PRES SPL :=
lazymatch type of PRES with
| rt_pres_fp ?live ?frames ?sp ?W ?m ?m' =>
lazymatch goal with
| PF : rt_pres_fp ?L0 ?F0 ?U0 ?W0 ?m0 m |- _ =>
let PF' := fresh "PF" in
assert (PF' : rt_pres_fp L0 F0 U0 W0 m0 m')
by (apply (pres_fp_trans L0 F0 U0 W0 m0 m m' PF);
apply (pres_fp_of_pres_fp L0 F0 U0 W0 live frames sp W m m' PRES);
[ cps_incl | cps_incl | ulc
| let x := fresh "x" in let Hx := fresh "Hx" in let Ho := fresh "Ho" in
intros x Hx Ho; cbn [outside] in Ho |- *;
repeat (split; [ first [ tauto
| let Hs := fresh "Hs" in pose proof (SPL x Hx) as Hs;
lazymatch goal with |- ~ (?a <= x < ?b) =>
cut (x < a \/ b <= x); [ clear; lia | destruct Hs; [ right; ulc | left; ulc ] ] end ] | ]);
exact I ]);
clear PF; rename PF' into PF
end
end.
