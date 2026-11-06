(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec AgentLib AxSymExec3K AxSymExec3SoundK AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK Jb0DefsK Jb0PlanImagesK
HandoffBridgeK HandoffBInvK Jb0HandoffK Jb0HSK_0 Jb0HSK_1 Jb0MainTableK Jb0HandoffInstK Jb0DrvEntryK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SymExec2 SymExec2Sound SymRun SymDrive HeapIface HeapIfaceA As0DrvKitA Jb0DrvEntry.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Jb0DrvEntryInst () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Fs."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.As0DrvKitA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanInitK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundK.APSK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3K.AX2K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DefsK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DrvEntry."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DrvEntryK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0HSK_0."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0HSK_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0HandoffInstK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0HandoffK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A0"; "1None"; "1Some"; "1app"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "1true"; "2and"; "2eq"; "2ex"]; ["2not"; "3add"; "4lt"; "5firstn"; "5nth"; "6Z"; "0E"; "0ES"; "0EXTRA"; "0FULL"; "7Fs"; "8word_to_le_bytes"; "9FdEntry"; "9Model"; "9m_fds"; "9m_fs"]; [":bvmap"; "0MV"; "0R"; ";lzinv"; "<mrestrict"; "=LIMIT"; "=SINV0"; "=argH0"; ">cs_ok"; ">fds_std"; "?env"; "@cat_argv_ptr"; "Adefined"; "Bahid"; "CAPH0"; "CASAN0"]; ["CASEGS0"; "Denv_mainA"; "Dkn_mainA"; "Dsr_mainA"; "Eauxv_list"; "Edrv_chk"; "Elib_chk"; "Estk_chk"; "Exc_chk"; "FHS_0"; "GHS_1"; "HHSA"; "Ias0_A0"; "Jrdn"; "Jtotal_arg_bytes_nat"; "Kenv"]; ["Lknow_ok"; "Lregs_ok"; "Mloaded_segments"; "Nadd"; "Nle"; "Nlt"; "Nmodulo"; "Nmul"; "Nof_nat"; "Npow"; "Nsub"; "0a0s"; "0brk0"; "0can"; "0envp"; "0fs"]; ["0h"; "0hw"; "0hwz"; "0i"; "0j"; "0k"; "0model"; "0path"; "0rdraw"; "0rnd"; "0sp"; "OZ_to_bv"; "Obv"; "Obv_unsigned"; "0tid"; "0top"]; ["0uid"; "0uidz"]]).
Lemma drv_chk_0 : ltac2:(TCodec.tc2 tcn__Jb0DrvEntryInst "7'>'4&QE&QI%211(<%63521"). Proof. vm_compute. reflexivity. Qed.
Lemma drv_chk_1 : ltac2:(TCodec.tc2 tcn__Jb0DrvEntryInst "7'>'4&QE&QJ%211(<%63521"). Proof. vm_compute. reflexivity. Qed.
Lemma drv_chk_HSA : ltac2:(TCodec.tc2 tcn__Jb0DrvEntryInst "@'8&Br1u2%3221'>'4&QE&QKr2%211%411(<%83721p0:1pU2?1").
Proof. intros h Hh. destruct h as [|[|h]]; [exact drv_chk_0 | exact drv_chk_1 | lia]. Qed.
Lemma stk_chk_0 : ltac2:(TCodec.tc2 tcn__Jb0DrvEntryInst "7'>'4&QG&QI%211(<%63521"). Proof. vm_compute. reflexivity. Qed.
Lemma stk_chk_1 : ltac2:(TCodec.tc2 tcn__Jb0DrvEntryInst "7'>'4&QG&QJ%211(<%63521"). Proof. vm_compute. reflexivity. Qed.
Lemma stk_chk_HSA : ltac2:(TCodec.tc2 tcn__Jb0DrvEntryInst "@'8&Br1u2%3221'>'4&QG&QKr2%211%411(<%83721p0:1pU2?1").
Proof. intros h Hh. destruct h as [|[|h]]; [exact stk_chk_0 | exact stk_chk_1 | lia]. Qed.
Lemma lib_chk_0 : ltac2:(TCodec.tc2 tcn__Jb0DrvEntryInst "7'>'4&QF&QI%211(<%63521"). Proof. vm_compute. reflexivity. Qed.
Lemma lib_chk_1 : ltac2:(TCodec.tc2 tcn__Jb0DrvEntryInst "7'>'4&QF&QJ%211(<%63521"). Proof. vm_compute. reflexivity. Qed.
Lemma lib_chk_HSA : ltac2:(TCodec.tc2 tcn__Jb0DrvEntryInst "@'8&Br1u2%3221'>'4&QF&QKr2%211%411(<%83721p0:1pU2?1").
Proof. intros h Hh. destruct h as [|[|h]]; [exact lib_chk_0 | exact lib_chk_1 | lia]. Qed.
Lemma xc_chk_0 : ltac2:(TCodec.tc2 tcn__Jb0DrvEntryInst "7'>'4&QH&QI%211(<%63521"). Proof. vm_compute. reflexivity. Qed.
Lemma xc_chk_1 : ltac2:(TCodec.tc2 tcn__Jb0DrvEntryInst "7'>'4&QH&QJ%211(<%63521"). Proof. vm_compute. reflexivity. Qed.
Lemma xc_chk_HSA : ltac2:(TCodec.tc2 tcn__Jb0DrvEntryInst "@'8&Br1u2%3221'>'4&QH&QKr2%211%411(<%83721p0:1pU2?1").
Proof. intros h Hh. destruct h as [|[|h]]; [exact xc_chk_0 | exact xc_chk_1 | lia]. Qed.
Section FPX_1. Context {fx : PropExec.FPState}.
Section Inst.
Variable sp brk0 : word.
Variable rdraw : EntryDraw.
Variables a0s path : list byte.
Variable envp : list (list byte).
Variables uid hw : word.
Variable fs : Fs.Fs.
#[local] Notation argv := [a0s; path].
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
#[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 argv envp uid hw).
#[local] Notation argH := (argH0 APH0 sp rdraw argv envp uid hw).
#[local] Notation CSOK := (APSK.cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).
Variables BUDGET LENMAX KMAX : Z.
Hypothesis BUD : 0 <= BUDGET /\ 0 <= KMAX /\ 0 <= LENMAX < 2 ^ 62.
Variable EXTRA : list (Z * Z).
Hypothesis EXTRA_wf : A_wf EXTRA.
Hypothesis BUD_le : 16515072 + 2461316608 + A_bytes EXTRA + BUDGET <= AsanInitK.LIMIT.
Hypothesis GAP : AsanCeil.bottomup_floor + LENMAX + (17729665187840 + BUDGET) + (21 + KMAX) * (LENMAX + 4095) <= AsanCeil.alloc_ceiling.
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation envc := (Z.of_nat (length envp)).
#[local] Notation L0 := (Z.of_nat (length a0s)).
Theorem as0_main_entry : ltac2:(TCodec.tc2 tcn__Jb0DrvEntryInst "UA'8&Br1u2%3221'Q:&Q0y5'RLyR0%211%5241':y8%611%311p061'M'Q8&Q@&Q?&Q5&Q6&Q>vRJvRHvR<(5'7%11?vR;vRG(9%114%73531%83651vR>vS0vRA%A8@?>=4321&Q7%17BA@6543vR?r4&QKr6%211r3r2%O;NML:876321Q?';'E%2211%I11&QLvHr7%=11r5%53421&Q4&Q=%12QL?%321D'?'QO&QA&RK&R3&RM%12QMQ>&R7+8&R8&6%12Q>Q7%311%6251%:281+V8%<221%>2R81%82R4QD%:11%@261+V9%B221%D2R>1r8%G6R182Q9RG1'=&R1&QCr9%33RL21&R0&R2&QB%342S0QG1&Q3%Q72Q:Q<%2451Q;Q='>'L%QF2RN1%R=11&N%11QC&Q9%73421&J&O%11QH%;331R7%S61RE&QM&Q;%14RMRBRAR5&A&D%RH1S:%24RLR9RF1%Q@2S<1u1%6221%:4MR@81(2&3z%QN2SD1%S73SD1:%43SE:1%62S71%O3C81%R12SMA&QN&C%13S<RIS6%311%R211%R82QL1%Q73RJ71&R4%R61E%R<2:1+1%R>221+@%R@221&R9+2+Q?%3221%;251%R02=1%R12F1p0TH1pU<TM1%R42Q=1%R52QB1%R62QK1%R72QO1%R82R41tQ@S2R:1qUNTJ1%S52TK1qTLTL1%S72TM1tR4THS91t2SDS>1p0SI1pU>TJ1pQDTL1pR6U21pQ>U91p0U;1pU2U@1").
Proof.
intros h Hh E R FULL model HC A0 MV.
pose proof (as0_chk_HSA h Hh) as C0. pose proof (drv_chk_HSA h Hh) as CD. pose proof (lib_chk_HSA h Hh) as CL. pose proof (stk_chk_HSA h Hh) as CS.
pose proof (as0_inst_bud BUDGET EXTRA BUD_le h Hh) as BL.
pose proof (as0_inst_gap BUDGET LENMAX KMAX BUD GAP h Hh) as GP.
assert (G : exists can : word, rdn ASEGS MV (Z_to_bv 64 0x690b00) 8 = Some (word_to_le_bytes 8 can)
/\ rdn ASEGS MV (Z_to_bv 64 0x670ab0) 8 = Some (word_to_le_bytes 8 can)).
{ edestruct (ent_guard sp brk0 rdraw argv envp uid hw fs) as (can & G1 & G2); [ .. | exists can; exact (conj G1 G2)]; eassumption. }
destruct G as (can & G1 & G2). exists can.
assert (T : exists tid : word, 1 <= bv_unsigned tid <= 4194303
/\ rdn ASEGS MV (Z_to_bv 64 0x6709f8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x6709f8))
/\ rdn ASEGS MV (Z_to_bv 64 0x670a18) 4 = Some (word_to_le_bytes 4 tid)
/\ rdn ASEGS MV (Z_to_bv 64 0x670a90) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x690d88))
/\ rdn ASEGS MV (Z_to_bv 64 0x690d58) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (usp + 8 * envc + 40)))).
{ eapply (ent_libcells sp brk0 rdraw argv envp uid hw fs); try eassumption; reflexivity. }
destruct T as (tid & TR & T1 & T2 & T3 & T4). exists tid. cbv zeta.
assert (SR : 0x7fff80000000 <= usp <= 2 ^ 47 /\ usp mod 16 = 0).
{ destruct Hsp as (H1 & H2 & H3). unfold sp_window_lo, sp_window_hi in H1, H2. lia. }
assert (HB : 0 <= envc <= 256 /\ 0 <= L0 <= 131071).
{ pose proof Hve as [Hle _]. pose proof Hva as (_ & _ & Hfa & _). inversion Hfa as [|x l Hx _]; subst. lia. }
split; [|split; [|split; [|split; [|split]]]].
- apply (main_regs_okA sp envc L0 R).
eapply (ent_regs sp brk0 rdraw argv envp uid hw fs); try eassumption; reflexivity.
- apply (main_know_okA sp envc L0 R MV SR HB).
+ eapply (ent_stack_words sp brk0 rdraw argv envp uid hw fs); try eassumption; reflexivity.
+ eapply (ent_window sp brk0 rdraw argv envp uid hw fs); eassumption.
+ exact G1.
+ eapply (ent_img sp brk0 rdraw argv envp uid hw fs); eassumption.
+ exact TR.
+ exact (conj T1 (conj T2 (conj G2 (conj T3 T4)))).
+ change XC9_CELLS with XC9K. eapply (ent_xcells sp brk0 rdraw argv envp uid hw fs); try eassumption; first [reflexivity | exact (xc_chk_HSA h Hh)].
- unfold lzinv. eapply (ent_lz sp brk0 rdraw argv envp uid hw fs); eassumption.
- eapply (ent_model sp brk0 rdraw argv envp uid hw fs); eassumption.
- eapply (ent_model sp brk0 rdraw argv envp uid hw fs); eassumption.
- intros k Hk. refine ((fun X Y => conj (proj1 X) (conj (proj2 X) Y)) _ _).
+ eapply (ent_str sp brk0 rdraw argv envp uid hw fs); try eassumption; reflexivity.
+ eapply (ent_str_hi sp rdraw argv envp uid hw); try eassumption; reflexivity.
Qed.
Theorem as0_main_auxv : ltac2:(TCodec.tc2 tcn__Jb0DrvEntryInst "T1'8&Br1u2%3221'Q:&Q0y5'RLyR0%211%5241':y8%611%311p061'M'Q8&Q@&Q?&Q5&Q6&Q>vRJvRHvR<(5'7%11?vR;vRG(9%114%73531%83651vR>vS0vRA%A8@?>=4321&Q7%17BA@6543vR?r4&QKr6%211r3r2%O;NML:876321Q?'?'E'=uD%QE2QD1'>%Q<1K&QM&R2r8&RK&R3&RM%12QFQ7&R7+8&R8&6%12Q7Q0%311%6251%:281+Q8%<221%81J%;2:1%?231%A2R41u8%F4ED21(2&K&D&QDr5%231Q:Q6z%54Q4Q721%L2R?1%82;1%:2QM1%Q43Q3<1p0Q61pU:RM1&R4%129Q@&R5&R9+2+Q0%3221%52QF1%QB271%92AS5+R0%8271%:2S81%QG241%>2Q=QL+@%QA2QN1%A216%QL241%QM261%QN2<1%QO2F1qU6R11%R32R21qUDR31%R52R41qV4R51%R72R61p0R91pU>S:1pQDS<1pR6SB1pQ>SI1p0SK1pU2T01").
Proof.
intros h Hh E R FULL model HC.
pose proof (as0_chk_HSA h Hh) as C0. pose proof (drv_chk_HSA h Hh) as CD. pose proof (lib_chk_HSA h Hh) as CL. pose proof (stk_chk_HSA h Hh) as CS.
pose proof (as0_inst_bud BUDGET EXTRA BUD_le h Hh) as BL.
pose proof (as0_inst_gap BUDGET LENMAX KMAX BUD GAP h Hh) as GP.
eapply (ent_auxv sp brk0 rdraw argv envp uid hw fs); try eassumption; reflexivity.
Qed.
Theorem as0_main_stack_defined : ltac2:(TCodec.tc2 tcn__Jb0DrvEntryInst "R='8&Br1u2%3221'Q:&Q0y5'RLyR0%211%5241':y8%611%311p061'M'Q8&Q@&Q?&Q5&Q6&Q>vRJvRHvR<(5'7%11?vR;vRG(9%114%73531%83651vR>vS0vRA%A8@?>=4321&Q7%17BA@6543vR?r4&QKr6%211r3r2%O;NML:876321Q?'E'>&R6+TP0%22QD1z%53621&R4&R3&RM%12QCQ4%3218%52>1&Q<&R:%12B5%33E61p051p0<1pV0C1p0E1pU>QF1pQDQH1pR6QN1pQ>R51p0R71pU2R<1").
Proof.
intros h Hh E R FULL model HC top Hm Hle i Hi.
pose proof (as0_chk_HSA h Hh) as C0. pose proof (drv_chk_HSA h Hh) as CD. pose proof (stk_chk_HSA h Hh) as CS.
pose proof (as0_inst_bud BUDGET EXTRA BUD_le h Hh) as BL.
pose proof (as0_inst_gap BUDGET LENMAX KMAX BUD GAP h Hh) as GP.
eapply (ent_stack_defined_top sp brk0 rdraw argv envp uid hw fs); try eassumption; reflexivity.
Qed.
Theorem as0_main_str_defined : ltac2:(TCodec.tc2 tcn__Jb0DrvEntryInst "S0'8&Br1u2%3221'Q:&Q0y5'RLyR0%211%5241':y8%611%311p061'M'Q8&Q@&Q?&Q5&Q6&Q>vRJvRHvR<(5'7%11?vR;vRG(9%114%73531%83651vR>vS0vRA%A8@?>=4321&Q7%17BA@6543vR?r4&QKr6%211r3r2%O;NML:876321Q?'E'=&R4z%221QD&R5&R3&R8&6&D%L1Q>%24Q0>J1%42Q@1%611+1%9221+@%;221%=2R21%B2?1&@'>r7&RK&RM&Q;%14QDQ9Q8Q1%32R41%F21N%62R61%811(1%11R4%<3R431%>11p0@1pU8Q41p0RC1pU<RH1p0Q81pU>R91pQDR;1pR6RA1pQ>RH1p0RJ1pU2RO1").
Proof.
intros h Hh E R FULL model HC k Hk i Hi.
pose proof (as0_chk_HSA h Hh) as C0. pose proof (drv_chk_HSA h Hh) as CD. pose proof (stk_chk_HSA h Hh) as CS.
pose proof (as0_inst_bud BUDGET EXTRA BUD_le h Hh) as BL.
pose proof (as0_inst_gap BUDGET LENMAX KMAX BUD GAP h Hh) as GP.
eapply (ent_str_defined sp brk0 rdraw argv envp uid hw fs); try eassumption; reflexivity.
Qed.
End Inst.
End FPX_1.
