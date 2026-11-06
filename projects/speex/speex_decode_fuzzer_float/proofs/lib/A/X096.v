(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05s X05l X05m X09f X069 X09e
X082 X08y X091 X08x X08u.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section NbAcc.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Lemma nbG_acc_pres2 : forall (Σ : rts RT) (m0 m m' : mem) sp W fp kp P n,
ART RT Σ m0 -> In (fp, kp) (rt_frames RT Σ) -> fp <= P -> P + n <= fp + fs_size kp - 8 ->
rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) sp W m m' -> (forall i, 0 <= i < n -> outside W (shad (P + i))) ->
acc asegs m P n -> acc asegs m' P n.
Proof using AF.
intros Σ m0 m m' sp W fp kp P n ART0 INF F1 F2 PRES OFF ACC i Hi. destruct (ACC i Hi) as (b & B & OK). exists b. split; [| exact OK].
pose proof (frame_facts RT AF Σ m0 fp kp ART0 INF) as (FP0 & FP64 & _ & _ & _ & _ & SA & S1 & S2 & _).
assert (FSZ : 0 <= fs_size kp) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (R : shad fp <= shad (P + i) < shad (fp + fs_size kp)).
{ unfold shad. split; [assert (fp / 8 <= (P + i) / 8) by (apply Z.div_le_mono; lia); lia|].
assert ((P + i) / 8 < (fp + fs_size kp) / 8); [| lia].
assert (E8 : (fp + fs_size kp) mod 8 = 0).
{ unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia. clear - FP64. set (q := 2 ^ Z.of_nat kp). assert (fp mod 8 = 0) by (Z.div_mod_to_equations; lia).
rewrite Z.add_mod, H by lia. change 64 with (8 * 8). rewrite <- Z.mul_assoc, Z.mul_comm, Z.mod_mul by lia. reflexivity. }
clear - E8 F2 Hi. Z.div_mod_to_equations. lia. }
apply (bytes_at_agree asegs m m' _ _ B). intros a Ha. cbn [length] in Ha.
apply PRES; [right; right; right; right; exists fp, kp; split; [exact INF| lia]|].
replace (bv_unsigned a) with (shad (P + i)) by lia. apply OFF. exact Hi.
Qed.

Lemma nbEH_off_shadow : forall (ST OUT A FF SF usp lo nout P n i : Z),
SF = FF / 8 + SHB -> FF mod 64 = 0 -> 0 <= P -> P + n <= 2^47 -> (P + n <= FF \/ FF + 2048 <= P) -> 0 <= i < n ->
(ST + 2968 <= SH_LO \/ SH_HI <= ST) -> (OUT + nout <= SH_LO \/ SH_HI <= OUT) -> (A + 48 <= SH_LO \/ SH_HI <= A) -> (FF + 2048 <= SH_LO \/ SH_HI <= FF) ->
SH_HI <= lo -> lo <= usp - 544 ->
outside [(ST, ST + 2968); (OUT, OUT + nout); (A, A + 48); (FF, FF + 2048); (SF, SF + 256); (usp - 544, usp)] (shad (P + i)).
Proof.
intros ST OUT A FF SF usp lo nout P n i ESF F64 P0 P1 PFA Hi SSH OSH ASH FSH LOS LOU.
assert (SW : SH_LO <= shad (P + i) < SH_HI) by (apply shad_window; unfold APP_TOP; Lia.lia).
assert (SHS : shad (P + i) < SF \/ SF + 256 <= shad (P + i)) by (unfold shad; rewrite ESF; clear - PFA Hi F64; Z.div_mod_to_equations; Lia.lia).
cbn [outside]. split; [clear - SW SSH; Lia.lia|]. split; [clear - SW OSH; Lia.lia|]. split; [clear - SW ASH; Lia.lia|]. split; [clear - SW FSH; Lia.lia|].
split; [clear - SHS; Lia.lia|]. split; [clear - SW LOS LOU; Lia.lia| exact I].
Qed.
End NbAcc.
