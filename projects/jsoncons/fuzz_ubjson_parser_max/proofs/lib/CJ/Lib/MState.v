(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import PropExec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Lib_MState () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.DecodeC."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "LinuxProcessSemantics.Riscv.Sem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1bool"; "1false"; "1list"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2not"; "3Z"; "0F"; "4Segment"; "5fetch_word"; "5interp_eff"]; ["5is_ecall"; "5machine_result"; "5machine_state"; "5ms_fcsr"; "5ms_fregs"; "5ms_mem"; "5ms_pc_val"; "5ms_regs"; "5ms_resv"; "5ms_rom"; "5ms_svc_pending"; "5step"; "6decode_any"; "7instr"; "8bvmap"; "8bvmap_set"]; ["9Core"; "9core"; "9eff"; "9exec"; "9reg_get"; "9w0"; "9w1"; "0R"; ":MS"; ":interp_eff0"; ":lift_result"; ":ret_pc"; ";v_addi"; "<add"; "<le"; "<lt"]; ["<modulo"; "<pow"; "0a"; "0b"; "0fc"; "0i"; "0m"; "0ms"; "0p"; "0pc"; "0r"; "0r'"; "0ra"; "0ro"; "0rv"; "0segs"]; ["=Z_to_bv"; "=bv"; "=bv_add"; "=bv_and"; "=bv_not"; "=bv_unsigned"; "0sz"; "0t"; "0v"; "0w"; "0x"; "0z"]]).
Definition MS (R F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word)
(m ro : word -> option byte) : machine_state :=
{| ms_regs := R; ms_fregs := F; ms_pc_val := pc; ms_svc_pending := None;
ms_resv := rv; ms_fcsr := fc; ms_mem := m; ms_rom := ro |}.
Definition MSsvc (R F : bvmap 5 word) (pc : word) (x8 : word) (fc : bv 32) (rv : option word)
(m ro : word -> option byte) : machine_state :=
{| ms_regs := R; ms_fregs := F; ms_pc_val := pc; ms_svc_pending := Some x8;
ms_resv := rv; ms_fcsr := fc; ms_mem := m; ms_rom := ro |}.
Definition MS_of_core (c : core) (m ro : word -> option byte) : machine_state :=
MS (c_regs c) (c_fregs c) (c_pc c) (c_fcsr c) (c_resv c) m ro.
Lemma MS_eta : ltac2:(TCodec.tc2 tcn__CJ_Lib_MState "Q1'B'9'5'R1yR0%211%411&Jr1%211(0%116%;3631r2&Q8&G%113&D%115&F%117&C%119&H%11;&E%11=&I%11?%?7=;97531%M3NA1p0C1pS@Q01").
Proof. intros [] H; cbn in *; subst; reflexivity. Qed.
Fixpoint interp_eff0 (segs : list Segment) (t : eff) (m : word -> option byte)
: machine_result (core * (word -> option byte)) :=
match t with
| EDone c => MachineOk (c, m)
| EEbreak _ | EFault _ | EDefinedIllegal _ => MachineFault
| EIllegal _ | EEcall _ => MachineUnmodeled
| ELoad n a k =>
match ov_read_bytes segs m a (width_bytes n) with
| Some bs => interp_eff0 segs (k (bv_extract 0 n (le_bytes_to_word bs))) m
| None => MachineFault
end
| EStore n a v k =>
if store_ok segs m a (width_bytes n)
then interp_eff0 segs k (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))
else MachineFault
end.
Lemma interp_eff_eq0 : ltac2:(TCodec.tc2 tcn__CJ_Lib_MState "M'4'=%211'Q2'R1yR0%211'5y8%511%311p051'9'A'7'Q1%2215%411&?r3r2r1%43321&Q9%13543%=3831pS>?1pT@H1pT0J1").
Proof.
intros segs t. unfold interp_eff. induction t; intros m; cbn [interp_eff_accesses interp_eff0]; try reflexivity.
- destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|reflexivity].
rewrite <- H. unfold RiscvSemantics.drop_access_report.
destruct (interp_eff_accesses segs _ m) as [[v acc]| |]; reflexivity.
- destruct (store_ok segs m a (width_bytes n)); [|reflexivity].
rewrite <- IHt. unfold RiscvSemantics.drop_access_report.
destruct (interp_eff_accesses segs t _) as [[v' acc]| |]; reflexivity.
Qed.
Definition lift_result (ro : word -> option byte) (r : machine_result (core * (word -> option byte)))
: machine_result machine_state :=
match r with
| MachineOk (c, m') => MachineOk (MS_of_core c m' ro)
| MachineFault => MachineFault
| MachineUnmodeled => MachineUnmodeled
end.
Lemma step_gen : ltac2:(TCodec.tc2 tcn__CJ_Lib_MState "RC'4'=%211&Ny5'R1yR0%211%5241yQ0%511'5%115y8%911%411p091'M';'9%91:&>r;r8%3221(1r3%22A1%93841'2&@r4%211(3%?3521'7%12CB%J11&Lr5%211(6%14IH;@%B271%I3741'A'B%211&Kr>&Q8r=r<r:r9r7%6754Q232Q11%9281&Q:&Q9&Q3&R0%12QHO(Q0%15=<Q:;:%533J1%73A1Q;%92<1%QA3E;1p0I1p0Q41p0Q;1pT>QF1pS<QH1pTDR01pSLQK1pS>QL1pSNR11pS:R41pSDR81pJR81pR@R91pT0R@1").
Proof.
intros segs R F pc fc rv m ro w i sz Hf He Hd. rewrite <- interp_eff_eq0.
unfold RiscvSemantics.step, RiscvSemantics.step_accesses. cbn [ms_pc ms_pc_val MS]. rewrite Hf.
unfold RiscvSemantics.drop_access_report, RiscvSemantics.decode_exec_accesses. rewrite He, Hd.
cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom MS].
unfold interp_eff, RiscvSemantics.drop_access_report.
destruct (interp_eff_accesses segs (exec (Z_to_bv 64 sz) i _) m) as [[[c m'] acc]| |]; reflexivity.
Qed.
Lemma step_ecall_gen : forall segs R F pc fc rv m ro w,
fetch_word segs pc = Some w ->
is_ecall w = true ->
RiscvSemantics.step segs (MS R F pc fc rv m ro) =
MachineOk (MSsvc R F pc (if is_x0 17 then w0 else reg_get R 17) fc rv m ro).
Proof.
intros segs R F pc fc rv m ro w Hf He.
unfold RiscvSemantics.step, RiscvSemantics.step_accesses. cbn [ms_pc ms_pc_val MS]. rewrite Hf.
unfold RiscvSemantics.drop_access_report, RiscvSemantics.decode_exec_accesses. rewrite He. reflexivity.
Qed.
Lemma reg_get_set_same : ltac2:(TCodec.tc2 tcn__CJ_Lib_MState "C&Ny5'R1yR0%211%5241%415'9&Q4&Or2r1r3%45<9321%6214%83;14pTB<1pSF;1pR@=1").
Proof. intros. unfold reg_get. rewrite bvmap_get_set_same. reflexivity. Qed.
Lemma reg_get_set_other : ltac2:(TCodec.tc2 tcn__CJ_Lib_MState "J&Ny5'R1yR0%211%5241%415&:'9r3r2%33521%511&Q4&Or4r5%35@=271%5219%623:%<3@21p091pTBB1pSHA1pSFB1pR@D1").
Proof. intros. unfold reg_get. rewrite bvmap_get_set_other by assumption. reflexivity. Qed.
Lemma w0_lit : ltac2:(TCodec.tc2 tcn__CJ_Lib_MState "9'9'R1yR0%211&Q5&R0z%2251%83541"). Proof. reflexivity. Qed.
Lemma w1_lit : ltac2:(TCodec.tc2 tcn__CJ_Lib_MState "9'9'R1yR0%211&Q6&R0+1%2251%83541"). Proof. reflexivity. Qed.
Lemma lit_add_lit : ltac2:(TCodec.tc2 tcn__CJ_Lib_MState "C';'9'R1yR0%211&R2&R0r2%2251r1%4271%63831/018&Q=%1275%92<1%?3<41pS8A1pS6B1").
Proof.
intros. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.
Lemma v_addi_lit : ltac2:(TCodec.tc2 tcn__CJ_Lib_MState "A';'9'R1yR0%211&Q<&R0r2%2251r1%5221&Q=%1253%72:1%=3:41pS<?1pSB@1").
Proof.
intros p i. unfold v_addi. rewrite Z_to_bv_unsigned. apply bv_eq.
rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma v_addi_assoc : ltac2:(TCodec.tc2 tcn__CJ_Lib_MState "G'R1yR0%211';'9&Q<&R0&Q=&R5r3%2291r2%5221%72<1r1%:221%9252%:271%<2A1%?3A41pS8A1pS6B1pTFD1").
Proof.
intros. unfold v_addi. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.
Lemma v_addi_var : ltac2:(TCodec.tc2 tcn__CJ_Lib_MState "B'R1yR0%211';'9&Q<r2r1%3221&R0&Q=&R5%12;6%3216%52=1%;3=71pS8=1pTF?1").
Proof. reflexivity. Qed.
Lemma Z_to_bv_bv_unsigned : ltac2:(TCodec.tc2 tcn__CJ_Lib_MState ";'R1yR0%211'9&R0&R5r1%2261%4271%63713pTF81").
Proof. intros. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.
Lemma Z_to_bv_plus0 : ltac2:(TCodec.tc2 tcn__CJ_Lib_MState ">'R1yR0%211'9&R0&Q=&R5r1%2271z%5221%72:1%93:15pTF;1").
Proof. intros. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma unsigned_lit : ltac2:(TCodec.tc2 tcn__CJ_Lib_MState "G';'8&Q>zr1%3221&Q?&QA+2+R0%3221%5271%;271'9&R5yR0&R0r2%2231%5241%73D13p091pTHF1").
Proof. intros. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact H. Qed.
Lemma unsigned_lit_wrap : ltac2:(TCodec.tc2 tcn__CJ_Lib_MState "@';'9&R5yR0&R0r1%2231%5241&Q@&QA+2+R0%3221%5281%=3>71pTH?1").
Proof. intros. rewrite Z_to_bv_unsigned. reflexivity. Qed.
Definition ret_pc (ra : word) : word := bv_and ra (bv_not (Z_to_bv 64 1)).
Lemma ret_pc_fold : ltac2:(TCodec.tc2 tcn__CJ_Lib_MState "@'R1yR0%211'9&R3r1&R4&R0+1%2281%4291%73:61&Q;%118%;3<31pSJ=1").
Proof. reflexivity. Qed.
Lemma ret_pc_even : ltac2:(TCodec.tc2 tcn__CJ_Lib_MState "N';'8&Q>zr1%3221&Q?&QA+2+R0%3221%5271%;271'9&Q@r2%2218%43A1>'R1yR0%211&Q;&R0r3%2251%411%=3612p0:1p0@1pTHM1").
Proof.
intros z Hz He. unfold ret_pc. apply bv_eq. rewrite bv_and_unsigned, bv_not_unsigned, !Z_to_bv_unsigned.
rewrite !(bv_wrap_small 64 z) by (unfold bv_modulus; lia).
change (bv_wrap 64 (Z.lnot (bv_wrap 64 1))) with (Z.ones 64 - 1)%Z.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
destruct (Z.eq_dec i 0).
- subst i. rewrite (Z.bit0_eqb z). replace (z mod 2)%Z with 0%Z by lia. cbn. reflexivity.
- destruct (Z.ltb_spec0 i 64).
+ replace (Z.testbit (Z.ones 64 - 1) i) with true. { apply andb_true_r. }
symmetry. change (Z.ones 64 - 1)%Z with (Z.shiftl (Z.ones 63) 1). rewrite Z.shiftl_spec by lia. apply Z.ones_spec_low. lia.
+ rewrite (Z.bits_above_log2 z i); [reflexivity| lia |].
destruct (Z.eq_dec z 0). { subst. cbn. lia. }
apply Z.lt_le_trans with 64%Z; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.
