(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib Ju0MemcpyBase Ju0MemcpyAL Ju0MemcpyMIS Ju0MemcpyC1 Ju0MemcpyC2 Ju0MemcpyC3.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__musl_Ju0Memcpy () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.musl.Ju0MemcpyBase."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1nat"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3Z"; "4bvmap"; "5wbytes"; "6msteps"; "7at_"; "7ret_ok"; "8getr"; "8mkst"; "9keeps"]; [":memk"; ";loaded_segments"; "<add"; "<le"; "<lt"; "<min"; "<modulo"; "<of_nat"; "<sub"; "0bs"; "0dst"; "0fx"; "0i"; "0k"; "0mem0"; "0n"]; ["0q"; "0regs"; "0regs'"; "0ret"; "0rom"; "0src"; "=BV"; "=Z_to_bv"; "=bv"; "=bv_unsigned"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.
Section ALL.
Variable mem0 : word -> option byte.
Variables dst src : word.
Variable n : Z.
Variable bs : list byte.
Variable rom : word -> option byte.
Hypothesis HOK : mcH mem0 dst src n bs.
#[local] Notation MK := (memk mem0 dst bs).
#[local] Notation SB := (sb_ bs).
#[local] Notation B := (b_ bs).
Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.
Ltac mlw F D jj :=
chain_step; [reflexivity
| eapply (mc_lw _ _ _ _ _ HOK) with (j := jj);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
| step_simpl]; vnorm.
Ltac mlbu F D jj :=
chain_step; [reflexivity
| eapply (mc_lbu _ _ _ _ _ HOK) with (j := jj);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
| step_simpl]; vnorm.
Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
Ltac msw F D kk valtac :=
mk_at kk;
chain_step; [reflexivity
| eapply (mc_sw _ _ _ _ _ HOK) with (k := kk);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
| gres; rwH; reflexivity | valtac | lia | lia]
| step_simpl].
Ltac msb F D kk valtac :=
mk_at kk;
chain_step; [reflexivity
| eapply (mc_sb _ _ _ _ _ HOK) with (k := kk);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
| gres; rwH; reflexivity | valtac | lia | lia]
| step_simpl].
Ltac cond :=
rwH; unfold c_eq, c_ltu, bv_eqb, bv_ltu; rewrite ?u_andi by lia; imm_norm; unorm;
first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge];
rewrite ?land_3 by lia; lia.
Ltac mk_eq := match goal with |- context [mkst _ _ (MK ?a) _] =>
match goal with |- msteps _ _ (mkst _ _ (MK ?b) _) => replace (MK a) with (MK b) by (f_equal; lia) end end.
Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
Ltac conda := rwH; unfold at_; cond.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section SE.
Local Abbreviation SEC_T_al_finish := (ltac2:(TCodec.tc2 tcn__musl_Ju0Memcpy "RF&8y5'Q8yR0%211%5241'7&<r2%211'3&=r4(Q6+1(1%33?21%6251r3%93?21r5+;%93E17%<231&;vQ5%2218%A3G41r6+=%A3M1?%D231vJ%921E%H3N31r7+<%H3Q41F%K231&Q7&HvO%221F%42Q81%Q23Q861'2&Cz%221D%32E8%5221'4':&A&>vKr:+eXfD%Q=3QG1Q;/01QG&@vNvIr8%443Q021vQ4%<5;:721r1r9%948Q57L%@5?3215%C3B51&?%12A6%M231qR6R61%I2R71p0K1p0Q21p0Q=1p0QE1p0QN1p0R91pQLR=1pR8R@1pR4R@1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_al_finish) 0%nat 0%nat).
Variable ret : ltac:(sec_ty2 constr:(SEC_T_al_finish) 1%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_al_finish) 2%nat 0%nat).
Lemma al_finish : ltac:(sec_stmt2 constr:(SEC_T_al_finish) 3%nat 0%nat).
Proof.
intros Hret H1 H11 H13 H12 Hk.
set (m := ((n - k) mod 16)%Z).
pose proof (Z.mod_pos_bound (n - k) 16 ltac:(lia)) as Hm16.
destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
assert (0 <= Z.land m 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
assert (0 <= Z.land m 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 1)%Z by (apply Z.land_nonneg; lia).
assert (Hl16 : Z.land m 16 = 0%Z) by (destruct B16 as [E|E]; [exact E|exfalso; lia]).
eapply (runs_trans RSEGS _ (fun r => mkst r (0xaa310 : word) (MK (n - m)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m) /\ getr r 13 = at_ dst (n - m) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
{ destruct (al16_run _ _ _ _ _ rom HOK regs ret k H1 H11 H13 H12 Hk) as (r & R & P). exists r.
subst m. split; [exact R|]. decompose [and] P. repeat split; try assumption. }
cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
eapply (runs_trans RSEGS _ (fun r => mkst r (0xaa330 : word) (MK (n - m + Z.land m 8)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m + Z.land m 8) /\ getr r 13 = at_ dst (n - m + Z.land m 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
{ destruct (al8_run _ _ _ _ _ rom HOK r2 ret (n - m) m (Z.land m 8) S1 S11 S13 S12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r & R & P).
exists r. split; [exact R|]. decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption. }
cbv beta. intros r3 (T1 & T11 & T13 & T12 & K3).
eapply (runs_trans RSEGS _ (fun r => mkst r (0xaa574 : word) (MK (n - m + Z.land m 8 + Z.land m 4)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m + Z.land m 8 + Z.land m 4) /\ getr r 13 = at_ dst (n - m + Z.land m 8 + Z.land m 4) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
{ destruct (al4_run _ _ _ _ _ rom HOK r3 ret (n - m + Z.land m 8) m T1 T11 T13 T12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r & R & P).
exists r. split; [exact R|]. decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption. }
cbv beta. intros r4 (U1 & U11 & U13 & U12 & K4).
destruct (t2_run _ _ _ _ _ rom HOK r4 ret (n - m + Z.land m 8 + Z.land m 4) m Hret U1 U11 U13 U12 ltac:(lia) B2 B1 ltac:(lia) ltac:(lia)) as (r & R & P).
exists r. split; [exact R | eapply keeps_trans; eassumption].
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_mis_run := (ltac2:(TCodec.tc2 tcn__musl_Ju0Memcpy "S7&8y5'Q8yR0%211%5241'7&<r3%211'3&=r5(Q6+1(1%33?21%6251r4%93?21r6+;%93E17%<231&;vQ5%2218%A3G41r7+=%A3M1?%D231vJ%921E%H3N31r8+<%H3Q41F%K231&Q7&HvO%221F%42Q81%Q23Q861r9+?%Q23Q>1Q0%Q5231%:2Q>M%Q83Q>21'6%Q:3Q>HQ6+2%Q<3Q@J1+3%Q>3QBL1%6231%7261'2&Cz%221A%32BF%5221'4':&A&>vKr=+eX`4%QK3R51QI/01R5&@vNvIr;%443Q>21vQ4%<5;:721r1r<%948QC7Q:%@5?3215%C3B51&?%12A6%M231qR6RD1%I2RE1p0K1p0Q21p0Q;1p0QB1p0QM1p0R51p0R>1p0RI1pR2RM1pQLRN1pR8S11pR4S11")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_mis_run) 0%nat 0%nat).
Variable ret : ltac:(sec_ty2 constr:(SEC_T_mis_run) 1%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_mis_run) 2%nat 0%nat).
Variable q : ltac:(sec_ty2 constr:(SEC_T_mis_run) 3%nat 0%nat).
Lemma mis_run : ltac:(sec_stmt2 constr:(SEC_T_mis_run) 4%nat 0%nat).
Proof.
intros Hret H1 H11 H13 H12 H15 Hq Hk.
destruct (Z.lt_ge_cases (n - k) 32) as [Hsmall|Hbig].
-
destruct (bits_lt32 (n - k) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
assert (0 <= Z.land (n - k) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - k) 4)%Z by (apply Z.land_nonneg; lia).
assert (0 <= Z.land (n - k) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - k) 1)%Z by (apply Z.land_nonneg; lia).
assert (0 <= Z.land (n - k) 16)%Z by (apply Z.land_nonneg; lia).
eapply (runs_trans RSEGS _ (fun r => mkst r (0xaa20c : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k) /\ keeps regs r)).
+ eexists. split.
* stepn (ltac:(oF' 0xaa204%Z)) (ltac:(oD' 0xaa204%Z)).
stepb_ft (ltac:(oF' 0xaa208%Z)) (ltac:(oD' 0xaa208%Z)) ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
set (m := (n - k)%Z) in *.
eapply (runs_trans RSEGS _ (fun r => mkst r (0xaa574 : word) (MK (k + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
/\ getr r 13 = at_ dst (k + Z.land m 16 + Z.land m 8 + Z.land m 4) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
* destruct (t16_run _ _ _ _ _ rom HOK r1 ret k m R1 R11 R13 R12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
* cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
destruct (t2_run _ _ _ _ _ rom HOK r2 ret (k + Z.land m 16 + Z.land m 8 + Z.land m 4)%Z m Hret S1 S11 S13 S12
ltac:(lia) B2 B1 ltac:(lia) ltac:(lia)) as (r3 & RUN & K3).
exists r3. split; [exact RUN | eapply keeps_trans; eassumption].
-
eapply (runs_trans RSEGS _ (fun r => mkst r (0xaa228 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k)
/\ getr r 15 = Z_to_bv 64 q /\ keeps regs r)).
+ eexists. split.
* stepn (ltac:(oF' 0xaa204%Z)) (ltac:(oD' 0xaa204%Z)).
stepb_tk (ltac:(oF' 0xaa208%Z)) (ltac:(oD' 0xaa208%Z)) ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & R15 & K1).
assert (CASE : exists regs' m,
msteps RSEGS (mkst r1 (0xaa228 : word) (MK k) rom)
(mkst regs' (0xaa574 : word) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
/\ (0 <= m < 32)%Z
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
/\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps r1 regs').
{ destruct Hq as [-> | [-> | ->]].
- apply (c1_run _ _ _ _ _ rom HOK r1 ret k); try assumption; lia.
- apply (c2_run _ _ _ _ _ rom HOK r1 ret k); try assumption; lia.
- apply (c3_run _ _ _ _ _ rom HOK r1 ret k); try assumption; lia. }
destruct CASE as (r2 & m & RUN & Hm & S1 & S11 & S13 & S12 & K2).
destruct (bits_lt32 m Hm) as (B16 & B8 & B4 & B2 & B1 & Bsum).
assert (0 <= Z.land m 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 1)%Z by (apply Z.land_nonneg; lia).
destruct (t2_run _ _ _ _ _ rom HOK r2 ret (n - (Z.land m 2 + Z.land m 1))%Z m Hret S1 S11 S13 S12
ltac:(lia) B2 B1 ltac:(lia) ltac:(lia)) as (r3 & RUN3 & K3).
exists r3. split; [eapply msteps_trans; [exact RUN | exact RUN3] |].
eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_j_run := (ltac2:(TCodec.tc2 tcn__musl_Ju0Memcpy "RF&8y5'Q8yR0%211%5241'7&<r2%211'3&=r4(Q6+1(1%33?21%6251r3%93?21r5+;%93E17%<231&;vQ5%2218%A3G41r6+=%A3M1?%D231vJ%921E%H3N31r7+<%H3Q41F%K231&Q7&HvO%221F%42Q81%Q23Q861'2&Cz%221D%32E8%5221'4':&A&>vKr:+eX_L%Q=3QG1Q;/01QG&@vNvIr8%443Q021vQ4%<5;:721r1r9%948Q57L%@5?3215%C3B51&?%12A6%M231qR6R61%I2R71p0K1p0Q21p0Q=1p0QE1p0QN1p0R91pQLR=1pR8R@1pR4R@1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_j_run) 0%nat 0%nat).
Variable ret : ltac:(sec_ty2 constr:(SEC_T_j_run) 1%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_j_run) 2%nat 0%nat).
Lemma j_run : ltac:(sec_stmt2 constr:(SEC_T_j_run) 3%nat 0%nat).
Proof.
intros Hret H1 H11 H13 H12 Hk.
pose proof (u64_range dst).
set (q := ((bv_unsigned dst + k) mod 4)%Z).
pose proof (Z.mod_pos_bound (bv_unsigned dst + k) 4 ltac:(lia)) as Hq4.
destruct (Z.eq_dec q 0) as [Hq0|Hq0].
-
eapply (runs_trans RSEGS _ (fun r => mkst r (0xaa2d4 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k) /\ keeps regs r)).
+ eexists. split.
* stepn (ltac:(oF' 0xaa1fc%Z)) (ltac:(oD' 0xaa1fc%Z)).
stepb_tk (ltac:(oF' 0xaa200%Z)) (ltac:(oD' 0xaa200%Z)) ltac:(conda).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (al_finish r1 ret k Hret R1 R11 R13 R12 Hk) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
- eapply (runs_trans RSEGS _ (fun r => mkst r (0xaa204 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k)
/\ getr r 15 = Z_to_bv 64 q /\ keeps regs r)).
+ eexists. split.
* stepn (ltac:(oF' 0xaa1fc%Z)) (ltac:(oD' 0xaa1fc%Z)).
stepb_ft (ltac:(oF' 0xaa200%Z)) (ltac:(oD' 0xaa200%Z)) ltac:(conda).
apply mst_refl.
* cbv beta. post. unfold v_andi, at_. subst q. rewrite <- land_3 by lia. unorm.
change (bv_wrap 64 3) with 3%Z. reflexivity.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & R15 & K1).
destruct (mis_run r1 ret k q Hret R1 R11 R13 R12 R15 ltac:(lia) Hk) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
Qed.
End SE.
Lemma hl_loop : ltac2:(TCodec.tc2 tcn__musl_Ju0Memcpy "T0'0&8y5'Q8yR0%211%5241'7&<r2%211'3&=r4(Q6+1(1%33?21%6251r3%93?21r5+;%93E17%<231&;vQ5%2218%A3G41r6+=%A3M1?%D231vJ%921E%H3N31r7+<%H3Q41F%K231&Q7&HvO%221F%42Q81%Q23Q861r8+>%Q23Q>1Q0%Q5231&B%12FQ4%K2J1%Q:3Q@41r9+?%Q:3QF1Q8%Q=231%B2QFQ;%Q@3QF21&Cz%221@&D%12:F&5&F&Q9%12R0Q:r:%D221+4%6221%QN3R21<%911&Gr>%211%L21QO&Er;%Q82Q71%Q02>2%A21<%Q;2=1%6241%R;3R?81'4'2':&A&>vKr?+eX^<%RA3RK1R?/01RK&@vNvIr=%443R421vQ4%<5;:721r1%847R86QO%?5>2N14%B3A41&?%12@5%F231qR6S91%I2S:1p0K1p0Q81p0QC1p0QF1p0QJ1p0R11p0R:1p0RE1p0RM1p0S61p0SA1pQLSE1pR8SH1pR4SH1pQJSO1").
Proof.
induction i as [|i IH]; intros regs ret k Hret H1 H11 H13 H12 H14 H15 Hk Hkn Hal Hi.
-
pose proof (u64_range src).
destruct (Z.eq_dec ((bv_unsigned src + (k + 1)) mod 4) 0) as [Hz|Hz].
+ eapply (runs_trans RSEGS _ (fun r => mkst r (0xaa1fc : word) (MK (k + 1)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1)) /\ keeps regs r)).
* eexists. split.
-- mlbu (ltac:(oF' 0xaa1cc%Z)) (ltac:(oD' 0xaa1cc%Z)) k.
stepn (ltac:(oF' 0xaa1d0%Z)) (ltac:(oD' 0xaa1d0%Z)).
stepn (ltac:(oF' 0xaa1d4%Z)) (ltac:(oD' 0xaa1d4%Z)).
stepn (ltac:(oF' 0xaa1d8%Z)) (ltac:(oD' 0xaa1d8%Z)).
msb (ltac:(oF' 0xaa1dc%Z)) (ltac:(oD' 0xaa1dc%Z)) k ltac:(apply sb_val_plain).
stepn (ltac:(oF' 0xaa1e0%Z)) (ltac:(oD' 0xaa1e0%Z)).
stepn (ltac:(oF' 0xaa1e4%Z)) (ltac:(oD' 0xaa1e4%Z)).
stepb_tk (ltac:(oF' 0xaa1e8%Z)) (ltac:(oD' 0xaa1e8%Z)) ltac:(conda).
apply mst_refl.
-- cbv beta. post. unfold v_addi. unorm. f_equal. lia.
* cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (j_run r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
+ eapply (runs_trans RSEGS _ (fun r => mkst r (0xaa1fc : word) (MK (k + 1)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1)) /\ keeps regs r)).
* eexists. split.
-- mlbu (ltac:(oF' 0xaa1cc%Z)) (ltac:(oD' 0xaa1cc%Z)) k.
stepn (ltac:(oF' 0xaa1d0%Z)) (ltac:(oD' 0xaa1d0%Z)).
stepn (ltac:(oF' 0xaa1d4%Z)) (ltac:(oD' 0xaa1d4%Z)).
stepn (ltac:(oF' 0xaa1d8%Z)) (ltac:(oD' 0xaa1d8%Z)).
msb (ltac:(oF' 0xaa1dc%Z)) (ltac:(oD' 0xaa1dc%Z)) k ltac:(apply sb_val_plain).
stepn (ltac:(oF' 0xaa1e0%Z)) (ltac:(oD' 0xaa1e0%Z)).
stepn (ltac:(oF' 0xaa1e4%Z)) (ltac:(oD' 0xaa1e4%Z)).
stepb_ft (ltac:(oF' 0xaa1e8%Z)) (ltac:(oD' 0xaa1e8%Z)) ltac:(conda).
stepn (ltac:(oF' 0xaa1ec%Z)) (ltac:(oD' 0xaa1ec%Z)).
stepb_ft (ltac:(oF' 0xaa1f0%Z)) (ltac:(oD' 0xaa1f0%Z)) ltac:(cond).
stepn (ltac:(oF' 0xaa1f4%Z)) (ltac:(oD' 0xaa1f4%Z)).
apply mst_refl.
-- cbv beta. post. unfold v_addi. unorm. f_equal. lia.
* cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (j_run r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
-
pose proof (u64_range src).
eapply (runs_trans RSEGS _ (fun r => mkst r (0xaa1cc : word) (MK (k + 1)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1))
/\ getr r 14 = at_ src (k + 1 + 1) /\ getr r 15 = Z_to_bv 64 1 /\ keeps regs r)).
+ eexists. split.
* mlbu (ltac:(oF' 0xaa1cc%Z)) (ltac:(oD' 0xaa1cc%Z)) k.
stepn (ltac:(oF' 0xaa1d0%Z)) (ltac:(oD' 0xaa1d0%Z)).
stepn (ltac:(oF' 0xaa1d4%Z)) (ltac:(oD' 0xaa1d4%Z)).
stepn (ltac:(oF' 0xaa1d8%Z)) (ltac:(oD' 0xaa1d8%Z)).
msb (ltac:(oF' 0xaa1dc%Z)) (ltac:(oD' 0xaa1dc%Z)) k ltac:(apply sb_val_plain).
stepn (ltac:(oF' 0xaa1e0%Z)) (ltac:(oD' 0xaa1e0%Z)).
stepn (ltac:(oF' 0xaa1e4%Z)) (ltac:(oD' 0xaa1e4%Z)).
stepb_ft (ltac:(oF' 0xaa1e8%Z)) (ltac:(oD' 0xaa1e8%Z)) ltac:(conda).
stepn (ltac:(oF' 0xaa1ec%Z)) (ltac:(oD' 0xaa1ec%Z)).
stepb_tk (ltac:(oF' 0xaa1f0%Z)) (ltac:(oD' 0xaa1f0%Z)) ltac:(cond).
apply mst_refl.
* cbv beta. post. unfold v_addi. unorm. f_equal. lia.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
destruct (IH r1 ret (k + 1)%Z Hret R1 R11 R13 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
Qed.
Section SE.
Local Abbreviation SEC_T_ref_memcpy := (ltac2:(TCodec.tc2 tcn__musl_Ju0Memcpy "R6&8y5'Q8yR0%211%5241&<r1%211'3&=r3(Q6+1(1%33>21%6251r2%93>21r4+:%93D17%<231vJ%?3D21r5+;%?3J1=%B231vQ5%E3J21r6+<%E3Q01C%H231&Q7vO%22Q21%M3Q241'4'2':&A&>vKr8+eX]D%Q33Q<1Q1/01Q<vNvQ4%8576321r7&9vI%236Q01%=5<QA416%@3?61&?%12>QD%D231qR6QH1%G2QI1p0I1p0Q21p0Q91p0Q@1p0QK1pR8R01pR4R01")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_ref_memcpy) 0%nat 0%nat).
Variable ret : ltac:(sec_ty2 constr:(SEC_T_ref_memcpy) 1%nat 0%nat).
Theorem ref_memcpy : ltac:(sec_stmt2 constr:(SEC_T_ref_memcpy) 2%nat 0%nat).
Proof.
intros Hret H1 H10 H11 H12.
pose proof (u64_range src). pose proof (u64_range dst).
rewrite <- (memk_n _ _ _ _ _ HOK). change mem0 with (MK 0).
assert (H11' : getr regs 11 = at_ src 0) by (rewrite at_0; exact H11).
assert (H12' : getr regs 12 = Z_to_bv 64 (n - 0)) by (rewrite Z.sub_0_r; exact H12).
destruct (Z.eq_dec (bv_unsigned src mod 4) 0) as [Hs4|Hs4].
-
destruct (Z.eq_dec (bv_unsigned dst mod 4) 0) as [Hd4|Hd4].
+ eapply (runs_trans RSEGS _ (fun r => mkst r (0xaa2d4 : word) (MK 0) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0) /\ keeps regs r)).
* eexists. split.
-- stepn (ltac:(oF' 0xaa1b4%Z)) (ltac:(oD' 0xaa1b4%Z)).
stepb_tk (ltac:(oF' 0xaa1b8%Z)) (ltac:(oD' 0xaa1b8%Z)) ltac:(conda).
stepn (ltac:(oF' 0xaa2c8%Z)) (ltac:(oD' 0xaa2c8%Z)).
stepn (ltac:(oF' 0xaa2cc%Z)) (ltac:(oD' 0xaa2cc%Z)).
stepb_ft (ltac:(oF' 0xaa2d0%Z)) (ltac:(oD' 0xaa2d0%Z)) ltac:(cond).
apply mst_refl.
-- cbv beta. post. rewrite at_0. reflexivity.
* cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (al_finish r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
+ eapply (runs_trans RSEGS _ (fun r => mkst r (0xaa204 : word) (MK 0) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0)
/\ getr r 15 = Z_to_bv 64 (bv_unsigned dst mod 4) /\ keeps regs r)).
* eexists. split.
-- stepn (ltac:(oF' 0xaa1b4%Z)) (ltac:(oD' 0xaa1b4%Z)).
stepb_tk (ltac:(oF' 0xaa1b8%Z)) (ltac:(oD' 0xaa1b8%Z)) ltac:(conda).
stepn (ltac:(oF' 0xaa2c8%Z)) (ltac:(oD' 0xaa2c8%Z)).
stepn (ltac:(oF' 0xaa2cc%Z)) (ltac:(oD' 0xaa2cc%Z)).
stepb_tk (ltac:(oF' 0xaa2d0%Z)) (ltac:(oD' 0xaa2d0%Z)) ltac:(cond).
apply mst_refl.
-- cbv beta. post; try (rewrite at_0; reflexivity).
unfold v_andi. rewrite <- land_3 by lia. change (bv_wrap 64 3) with 3%Z. reflexivity.
* cbv beta. intros r1 (R1 & R11 & R13 & R12 & R15 & K1).
pose proof (Z.mod_pos_bound (bv_unsigned dst) 4 ltac:(lia)).
destruct (mis_run r1 ret 0 (bv_unsigned dst mod 4) Hret R1 R11 R13 R12 R15 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
-
destruct (Z.eq_dec n 0) as [Hn0z|Hn0z].
+ eapply (runs_trans RSEGS _ (fun r => mkst r (0xaa1fc : word) (MK 0) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0) /\ keeps regs r)).
* eexists. split.
-- stepn (ltac:(oF' 0xaa1b4%Z)) (ltac:(oD' 0xaa1b4%Z)).
stepb_ft (ltac:(oF' 0xaa1b8%Z)) (ltac:(oD' 0xaa1b8%Z)) ltac:(conda).
stepb_tk (ltac:(oF' 0xaa1bc%Z)) (ltac:(oD' 0xaa1bc%Z)) ltac:(cond).
stepn (ltac:(oF' 0xaa1f8%Z)) (ltac:(oD' 0xaa1f8%Z)).
apply mst_refl.
-- cbv beta. post. rewrite at_0. reflexivity.
* cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (j_run r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
+ set (i := Z.to_nat (Z.min n (4 - bv_unsigned src mod 4) - 1)).
pose proof (Z.mod_pos_bound (bv_unsigned src) 4 ltac:(lia)).
eapply (runs_trans RSEGS _ (fun r => mkst r (0xaa1cc : word) (MK 0) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0)
/\ getr r 14 = at_ src (0 + 1) /\ getr r 15 = Z_to_bv 64 1 /\ keeps regs r)).
* eexists. split.
-- stepn (ltac:(oF' 0xaa1b4%Z)) (ltac:(oD' 0xaa1b4%Z)).
stepb_ft (ltac:(oF' 0xaa1b8%Z)) (ltac:(oD' 0xaa1b8%Z)) ltac:(conda).
stepb_ft (ltac:(oF' 0xaa1bc%Z)) (ltac:(oD' 0xaa1bc%Z)) ltac:(cond).
stepn (ltac:(oF' 0xaa1c0%Z)) (ltac:(oD' 0xaa1c0%Z)).
stepn (ltac:(oF' 0xaa1c4%Z)) (ltac:(oD' 0xaa1c4%Z)).
stepn (ltac:(oF' 0xaa1c8%Z)) (ltac:(oD' 0xaa1c8%Z)).
apply mst_refl.
-- cbv beta. post. rewrite at_0. reflexivity.
* cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
destruct (hl_loop i r1 ret 0 Hret R1 R11 R13 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_0_r; exact Hs4)) as (r2 & RUN & K2).
{ subst i. rewrite Z.add_0_r, Z.sub_0_r. rewrite Z2Nat.id; lia. }
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
Qed.
End SE.
End ALL.
End FPX_1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
