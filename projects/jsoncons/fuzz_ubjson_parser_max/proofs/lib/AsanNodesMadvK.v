(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Madvise.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim ShapeAlg SpinAlg Nodes StoreOk AgentLib AgentNodes RefNodes AsanAcctShape Scfg KitNodesS.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanNodesLibEK.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__AsanNodesMadvK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs."; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Madvise."; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Madvise."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.MmapSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1O"; "1Some"; "1bool"; "1option"; "1true"; "2I"; "2eq"; "3Z"; "0K"; "4check_syscall"; "5check_madvise"; "6check_result"; "7fetch_word"; "7is_ecall"; "7machine_state"]; ["7ms_gpr"; "8mkCfg"; "8sys_input"; "9Model"; "9SyscallEffect"; "9m_halted"; "9m_vmmaps"; "9page_size"; ":madvise_dontneed_next"; ":madvise_dontneed_ok"; ";int32"; "<bvmap"; "=zfill"; ">getr"; ">mkst"; ">regupd"]; [">v_addi"; "?TSet"; "@srealizes"; "Aadd"; "Alt"; "Amodulo"; "Apow"; "0a"; "0eff"; "0fxg"; "0len"; "0mem"; "0model"; "0ms"; "0pc"; "0regs"]; ["0rom"; "0scfg"; "0segs"; "BBV"; "BZ_to_bv"; "Bbv"; "Bbv_unsigned"; "0w"; "0x8"]]).
Section Madv.
Context {fxg : PropExec.FPState}.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Hypothesis Halloc : sc_alloc scfg = false.
Lemma madvise_check : ltac2:(TCodec.tc2 tcn__AsanNodesMadvK "Q7'?'QEyR0%211'C'D'7'8&QFr3%2281+W9%63521'<&:&BvQBr5r4%43321r2%7321<&;&@(1%2281u1%42:1&Ju2%72=1%311%:5751<G%K3D<1p0F1pRBN1pRJQ01pSBQ21pRLQ61").
Proof. intros ms x8 model eff Hno. unfold check_syscall. rewrite in_sysno_sys_input, Hno. reflexivity. Qed.
Lemma srz_madvise_lazy : ltac2:(TCodec.tc2 tcn__AsanNodesMadvK "TC&Ky5'QEyR0%211%5241'4y8%611%311p061'CyQ0%;11'8&Q1'7%;14&=vQBr8%3221(2r4%22;1%93841'3&>r5%211(5%?3521%J1L&Er7%211(0%11Q1%F3631&Mr<(QC+A(6%33Q;21%6251&QD+W9%22Q=1%Q13Q=41r=+:%;3QC19%>231%Q63QB1D&Q5&QF%12QFQ5&G%4221z%Q=3Q?21r?+;%G3QO1E%J231%D2QOQ>%QC3QO21&Q4r9%22:1r:+TP0%B221%QJ3QL1>&Q3%D2R9Q4r;%3221&Q6+2+R0%3221%?251rC+<%Q=3RE1Q;%Q@231+4%Q;2RF1%R:3RF31&I&Fr@%211r>%QB2RMQ>%63321%RB3R81R4'Q2vQA(A&NvQ9&OrE%QL2S7Q>%332QG1&Q0rD%221F&L%R22S=A%23QC1MrB%=5<8521&HrA%231QH6%B241%E4S5D1R6rF%D5C1A=Q6%F219%I4S9H1Mp051p0L1p0Q51p0Q=1p0QG1p0QL1p0R01p0R71p0R?1p0RE1p0S11p0S91p0S@1pDSK1pRFSM1pR@T81pS@T01pRJT31pS2T51pRHT61pRNT=1pS0T=1").
Proof.
intros regs pc mem rom model w a len K HF HE Hh H17 H10 Hal H11 Hlen Hll Hend H12 Hok Hc.
pose proof (u64_range a) as Hra.
assert (Hlen' : (len < 2 ^ 64)%Z) by lia.
eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
set (ms := epend regs pc mem rom (getr regs 17)).
assert (Hno : bv_unsigned (getr regs 17) = 233%Z) by (rewrite H17; apply u64_lit; lia).
assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (unfold ms; rewrite ms_gpr_epend1, H11; apply u64_lit; lia).
assert (H0 : ms_gpr ms 0 = a) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
assert (H2 : int32 (ms_gpr ms 2) = Z_to_bv 64 4) by (unfold ms; rewrite ms_gpr_epend2, H12; vm_compute; reflexivity).
assert (Hpr : page_round_up_Z len = len) by (apply AllocSim.page_round_up_Z_aligned; [lia | exact Hll]).
assert (Hchk : forall eff, check_syscall (sys_input segs ms (getr regs 17)) eff model
= match eff with
| mkEffectU r [] zs [] [] [] =>
if (w_is0 r && listNN_eqb zs [(a, Z_to_bv 64 len)])%bool
then CheckOk (madvise_dontneed_next model a (Z_to_bv 64 len)) [] else CheckReject
| _ => CheckReject
end).
{ intros eff. rewrite (madvise_check ms (getr regs 17) model eff Hno). unfold Madvise.check_madvise.
rewrite H0, H2, Hu1, Hpr.
replace (bv_unsigned a mod page_size =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact Hal).
cbn [negb]. change (madvise_dontneed_b (Z_to_bv 64 4)) with true. cbn [negb].
replace (w_is0 (ms_gpr ms 1)) with false.
2:{ symmetry. unfold w_is0. apply bv_eqb_neq. intro Hz. apply (f_equal bv_unsigned) in Hz. rewrite Hu1 in Hz.
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hz. lia. }
replace (two_pow_64 <=? bv_unsigned a + len)%Z with false by (symmetry; apply Z.leb_gt; unfold two_pow_64; lia).
rewrite Hok. reflexivity. }
eapply (srz_det_noacc segs scfg ms model (getr regs 17)
(mkEffectU (Z_to_bv 64 0) [] [(a, Z_to_bv 64 len)] [] [] [])
(madvise_dontneed_next model a (Z_to_bv 64 len)));
[exact Hh | reflexivity | rewrite Hno; reflexivity | | | | reflexivity |].
- intros eff m' evs. split.
+ intros Hck. rewrite Hchk in Hck. destruct eff as [r ws zs us cs ci].
destruct ws; [|discriminate]. destruct us; [|discriminate].
destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (w_is0 r) eqn:E0; [|discriminate].
destruct (listNN_eqb zs [(a, Z_to_bv 64 len)]) eqn:Hl; [|discriminate].
apply listNN_eqb_eq in Hl. subst zs. cbn [andb] in Hck. injection Hck as <- <-.
unfold w_is0 in E0. apply bv_eqb_eq in E0. subst r. repeat split; reflexivity.
+ intros (-> & -> & ->). rewrite Hchk. unfold w_is0. rewrite bv_eqb_refl.
rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
- intros eff Hck. rewrite Hchk in Hck. destruct eff as [r ws zs us cs ci].
destruct ws; [|discriminate]. destruct us; [destruct cs; [destruct ci; [|discriminate]|discriminate]|discriminate].
destruct (w_is0 r && listNN_eqb zs _)%bool; discriminate.
- exact Hh.
- unfold ms. rewrite adv_zeros1_epend. exact Hc.
Qed.
End Madv.
