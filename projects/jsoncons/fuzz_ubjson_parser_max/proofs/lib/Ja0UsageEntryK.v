(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AgentLib BackingAlgebra AsanPlacement AsanCeil AxSymExec3K AxSymExec3SoundK AxSymRun3K
AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK Ja0DefsK Ja0PlanImagesK HandoffBridgeK HandoffLedgerK HandoffBInvK HandoffCellsK HandoffRolesK
Ja0HandoffK Ja0ArtCellsK Ja0DrvEntryK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIface HeapIfaceA ArtBridge CatExec ArgvEnv FileSim MemSplit RefLayout MuslStrlen.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ja0UsageEntryK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanInitK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanK.APK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundK.APSK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3K.AX2K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HandoffBridgeK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DefsK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DrvEntryK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0HandoffK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0UsageEntryK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0UsageEntryK.EntryG."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1O"; "1Some"; "1app"; "1bool"; "1cons"; "1false"; "1length"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"]; ["2ex"; "2not"; "3add"; "4nth"; "5Z"; "0E"; "0EXTRA"; "0FULL"; "6word_to_le_bytes"; "7entry_stack_image"; "8build_stack_bytes"; "0R"; "9mrestrict"; ":argH0"; ";e_sp0"; ";kn"]; ["<uE"; "=EVar"; "=edenot"; "=expr"; ">cat_argv_ptr"; "?VZ"; "?Wsb"; "?kfind_word"; "@ahid"; "AAPH0"; "AASEGS0"; "BDRV_REGS"; "BKE_ENVP"; "BKE_P0"; "BKE_SPK"; "Cas0_A0"]; ["EDRV_REGVG"; "Dtid_chk"; "Fgetr"; "Frdn"; "Fwrap_mem"; "GIn"; "Hadd"; "Hle"; "Hlt"; "Hmodulo"; "Hmul"; "Hof_nat"; "Hpow"; "Hsub"; "0argv"; "0cs"]; ["0e"; "0envp"; "0hw"; "0i"; "0model"; "0off"; "0r"; "0rdraw"; "0sp"; "IZ_to_bv"; "Ibv"; "Ibv_unsigned"; "0tid"; "0top"; "0uid"; "0v"]; ["0x"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition tid_chk (cs : acs) : bool :=
match kfind_word (kn cs) (ELit 0) 0x66ecd8 4 with Some v => existsb (kentry_eqb (KRange v 1 4194303)) (kn cs) | None => false end.
Section EntryG.
Variable sp brk0 : word.
Variable rdraw : EntryDraw.
Variable argv envp : list (list byte).
Variables uid hw : word.
Variable fs : Fs.Fs.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
#[local] Abbreviation SINV := (SINV0 APH0 sp rdraw brk0 argv envp uid hw).
#[local] Abbreviation argH := (argH0 APH0 sp rdraw argv envp uid hw).
#[local] Abbreviation CSOK := (cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).
Let AH := argH0_high APH0 sp rdraw argv envp uid hw Hsp Hva.
Variables BUDGET LENMAX KMAX : Z.
Hypothesis BUD : 0 <= BUDGET /\ 0 <= KMAX /\ 0 <= LENMAX < 2 ^ 62.
Variable EXTRA : list (Z * Z).
Hypothesis EXTRA_wf : A_wf EXTRA.
Variable cs : acs.
Hypothesis CHK0 : as0_chk cs = true.
Hypothesis CHKD : drv_chk cs = true.
Hypothesis BUD_le : a_eager cs + a_abytes cs + A_bytes EXTRA + BUDGET <= AsanInitK.LIMIT.
Hypothesis GAP : AsanCeil.bottomup_floor + LENMAX + (a_totsz cs + BUDGET)
+ (Z.of_nat (length (segments_reserved ASEGS0) + length (a_maps cs)) + KMAX) * (LENMAX + 4095) <= AsanCeil.alloc_ceiling.
Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : CSOK E cs R FULL model.
#[local] Abbreviation A0 := (as0_A0 EXTRA cs E).
#[local] Abbreviation Hx := (ahid A0 model).
#[local] Abbreviation MV := (mrestrict Hx FULL).
#[local] Abbreviation usp := (bv_unsigned sp).
#[local] Abbreviation argc := (Z.of_nat (length argv)).
#[local] Abbreviation envc := (Z.of_nat (length envp)).
#[local] Abbreviation L0 := (Z.of_nat (length (nth 0 argv []))).
Ltac LINEQ e Hn H :=
pose proof (hb_lin ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model e HC Hn) as H;
unfold LZ in H;
match type of H with context [lin_of ?x] => let l := eval vm_compute in (lin_of x) in change (lin_of x) with l in H end;
cbv [AX2SK.lden AX2SK.tden fst snd AX2SK.uE] in H; cbn [edenot] in H;
repeat match type of H with context [bv_unsigned (ev E ?n)] => change (bv_unsigned (ev E n)) with (VZ E n) in H end;
rewrite ?Z.add_0_r in H.
Lemma g_vals : ltac2:(TCodec.tc2 tcn__Ja0UsageEntryK "QI'>'?'D&Q5vEu1%3221&QK&7'8'R:y8%211%411vQN%7221%911%@3?;1u2%@2?1vR1%=281%?11%F3E41u3%F2E1&C(1(9%11A%44A3@1%G2C1%I11%Q03O81&QF&QJ+QPP0%Q22Q1:%3221+@u6%Q62Q51%7231%9251+TP0u:%Q;2Q:1%<231%>251&R;yR0vR8%3221%QD3QC51%QF2E1%QG2Q01%QH2Q71").
Proof. eapply (ent_vals sp brk0 rdraw argv envp uid hw fs); eassumption. Qed.
Lemma g_sp0 : ltac2:(TCodec.tc2 tcn__Ja0UsageEntryK ";'?'D&Q0vE&N%3221&R;yR0vR8%3221%:3951").
Proof. eapply (sp0_val sp brk0 rdraw argv envp uid hw fs); eassumption. Qed.
Lemma g_rng : ltac2:(TCodec.tc2 tcn__Ja0UsageEntryK "F'>&QG+SoonPPPPP0&R;yR0vR8%3221%6251&QL+2+Q?%3221%;261%=261'?'D&QI+@%22<1z%63521%E281").
Proof. destruct Hsp as (H1 & H2 & H3). unfold sp_window_lo, sp_window_hi in *. lia. Qed.
Lemma g_bounds : ltac2:(TCodec.tc2 tcn__Ja0UsageEntryK "Q6'>&QG+1&QK&7'8'R:y8%211%411vQN%7221%911%<2;1+QP0%>231%@231zvR1%?2:1%A11%D241+X0%F231%H231&C(1(9%11D%44D3C1%J2F1%L11%O2?1+SooO%Q1231%Q3231%Q42<1%Q52E1").
Proof.
pose proof Hve as [Hle _]. pose proof Hva as (Hac & _ & Hfa & _).
split; [exact Hac|]. split; [lia|]. split; [lia|].
destruct argv as [|a l]; [cbn in Hac; lia|]. inversion Hfa as [|x l' Hx _]; subst. cbn [nth]. exact Hx.
Qed.
Lemma g_vis_high : ltac2:(TCodec.tc2 tcn__Ja0UsageEntryK "L'R:yR0%211&QG&QM&R;vR8%2261+XPPP0%5221r1%62:1%9231'?'4&Q8&Q?vFvQOvE%43321vR4r2%83321(6%<3;21p0>1pU2I1").
Proof. eapply (vis_high sp brk0 rdraw argv envp uid hw fs); eassumption. Qed.
Lemma g_simg_top : ltac2:(TCodec.tc2 tcn__Ja0UsageEntryK "Q:'>&QG&QF&R;yR0vR8%3221&QK&7'R:y8%211&I&Q9vQNvR1vR>vR2vR7%776>54321%<291%>11%D2@1&QL+2+Q?%3221%J251&J%17@H?>=<;%F2C1%H11%O21;'?'D&QI+TP0%22?1z%63521%Q8281%Q92>1").
Proof. eapply (simg_top sp rdraw argv envp uid hw); eassumption. Qed.
Lemma gval_spk48 : ltac2:(TCodec.tc2 tcn__Ja0UsageEntryK "C'?'R:yR0%211&Q2vE&Q>-Q@%211%5241&R9&QM&R;vR8%22<1+Q@%5221%72?1%B3?91").
Proof.
destruct (drv_chk_parts cs CHKD) as (_ & _ & _ & L2 & _). destruct g_vals as (_ & _ & _ & U0). pose proof g_rng.
apply word_of_u. remember (bv_unsigned (edenot E (KE_SPK (-48)))) as x eqn:Ex. LINEQ (KE_SPK (-48)) L2 H0. rewrite <- Ex in H0. lia.
Qed.
Lemma gval_spk8 : ltac2:(TCodec.tc2 tcn__Ja0UsageEntryK "B'?'R:yR0%211&Q2vE&Q>+8%211%5241&R9&QF&R;vR8%22<1%4218%62>1%A3>81").
Proof.
destruct (drv_chk_parts cs CHKD) as (_ & _ & _ & _ & L3 & _). destruct g_vals as (_ & _ & _ & U0).
apply word_of_u. remember (bv_unsigned (edenot E (KE_SPK 8))) as x eqn:Ex. LINEQ (KE_SPK 8) L3 H0. rewrite <- Ex in H0. lia.
Qed.
Lemma gval_envp : ltac2:(TCodec.tc2 tcn__Ja0UsageEntryK "N'?'R:yR0%211&Q2vE&Q<%3221&R9&QF&R;vR8%22:1+@%5221&QJ+8&QK&7'8y8%D11%311vQN%6221%811%;2:1%B2=1%D2J1%M3JF1").
Proof.
destruct (drv_chk_parts cs CHKD) as (_ & _ & _ & _ & _ & L4 & _). destruct g_vals as (U1 & _ & _ & U0).
apply word_of_u. remember (bv_unsigned (edenot E KE_ENVP)) as x eqn:Ex. LINEQ KE_ENVP L4 H0. rewrite <- Ex in H0. lia.
Qed.
Lemma gval_p0 : ltac2:(TCodec.tc2 tcn__Ja0UsageEntryK "Q3'?'R:yR0%211&Q2vE&Q=%3221&R9&QF&R;vR8%22:1&QJ+8&QK&7'8y8%B11%311vQN%6221%811%;2:1%@2=1vR1%;271%=11%@2?1%E251+UH%G221%I2O1%Q23OK1").
Proof.
destruct (drv_chk_parts cs CHKD) as (_ & _ & _ & _ & _ & _ & L5 & _). destruct g_vals as (U1 & U2 & _ & U0).
apply word_of_u. remember (bv_unsigned (edenot E KE_P0)) as x eqn:Ex. LINEQ KE_P0 L5 H0. rewrite <- Ex in H0. lia.
Qed.
Lemma gval_argc : ltac2:(TCodec.tc2 tcn__Ja0UsageEntryK "F'?'R:yR0%211&Q2vE(Q1u1%211%5241&R9&QK&7'8y8%>11%311vQN%6221%811%:2B1%E3B<1").
Proof. destruct g_vals as (U1 & _). apply word_of_u. exact U1. Qed.
Definition DRV_REGVG : list (Z * Z) :=
[(1, 0x11315c); (2, usp - 48); (3, 0x10800); (4, 0x66ed80); (8, usp + 8); (9, argc); (10, argc); (11, usp + 8);
(12, usp + 16 + 8 * argc); (18, 0xa71ac); (19, usp + 16 + 8 * argc); (20, 0); (21, 0); (22, 0); (23, 0); (24, 0); (25, 0); (26, 0); (27, 0)].
Lemma g_reg : ltac2:(TCodec.tc2 tcn__Ja0UsageEntryK "M'D'Q3&QE'<%1243(;r2r1%348721&Q;%83621'?'R:yR0%211&QBvK&R9y5r3%3221%6251&Q2vE%221B%>3;41p0@1pT2J1pT>L1").
Proof. eapply (ent_reg sp brk0 rdraw argv envp uid hw fs); eassumption. Qed.
Section SE.
Local Abbreviation SEC_T_entg_regs := (ltac2:(TCodec.tc2 tcn__Ja0UsageEntryK "J'D&QE'<%1233(;r2r1%347721&Q@%83621'?'R:yR0%211&QBvK&R9y5r3%3221%6251%529@%<3921p0>1pU0H1pT>I1")) (only parsing).
Variable r : ltac:(sec_ty2 constr:(SEC_T_entg_regs) 0%nat 0%nat).
Variable v : ltac:(sec_ty2 constr:(SEC_T_entg_regs) 1%nat 0%nat).
Theorem entg_regs : ltac:(sec_stmt2 constr:(SEC_T_entg_regs) 2%nat 0%nat).
Proof.
intros Hin.
unfold DRV_REGVG in Hin.
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 1 (ELit 0x11315c)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 2 (KE_SPK (-48))) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact gval_spk48|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 3 (ELit 0x10800)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 4 (ELit 0x66ed80)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 8 (KE_SPK 8)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact gval_spk8|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 9 (EVar 1)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact gval_argc|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 10 (EVar 1)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact gval_argc|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 11 (KE_SPK 8)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact gval_spk8|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 12 (KE_ENVP)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact gval_envp|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 18 (ELit 0xa71ac)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 19 (KE_ENVP)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact gval_envp|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 20 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 21 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 22 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 23 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 24 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 25 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 26 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 27 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
destruct Hin.
Qed.
End SE.
Lemma g_stkword : ltac2:(TCodec.tc2 tcn__Ja0UsageEntryK "QF'D'Q3'?':%113&Q7&OvQO%211&Nr2u8%744321(2r1%22>1%>3<41'8'R:y8%211%411%C11&QC&Q:&L&Q8&Q?vFvE%332G1vR4%6221vG%9221&R9yR0&QF&R;vR8%2241r3%5221%8271%E4D:1Q1&H&Q2%12BQ5%32Q51%Q42L1%Q@3L61p0Q31pU0QC1pT<QE1").
Proof. eapply (ent_stkword sp brk0 rdraw argv envp uid hw fs); eassumption. Qed.
Theorem entg_stack_words : ltac2:(TCodec.tc2 tcn__Ja0UsageEntryK "QM'>'?':'8'R:y8%211%411%611&QC&Q:&L&Q8&Q?vFvQOvE%43321vR4%7221vG%:221&R9yR0&R;vR8%2231%5241u8%D4C821(2&H&QK&7vQN%22L1%411%?2>1%72:1%92Q01%Q73Q0;1&QF+8%22A1%F2E1%Q44Q3H1A&QJ%125;%72F1vR1%A2Q;1%C11%62:1%<251+UH%>221%Q22Q11%J2M1%L2QC1%QJ3QC>1%QL2D1").
Proof.
destruct (drv_chk_parts cs CHKD) as (_ & _ & _ & _ & _ & _ & _ & _ & K0 & K8 & _).
pose proof (g_stkword 0 _ K0) as H0. pose proof (g_stkword 8 _ K8) as H8.
rewrite Z.add_0_r, gval_argc in H0. rewrite gval_p0 in H8. auto.
Qed.
Lemma wsb_eqG : ltac2:(TCodec.tc2 tcn__Ja0UsageEntryK "Q8'?'D&QJ+8&Q6&Q9vR8vR7vQNvR1vR>vR2%877654321%;2:1&QM&QK&7'R:y8%211&J%17@?=<;:>%6231%811+@%;221&QF'8%119%=21E%?11%M2L1%@24G%B11%Q02O1%9241+UH%;221%H2=1%Q73Q6J1").
Proof.
destruct (bsb_ge APH0 sp rdraw argv envp uid hw) as [_ Hm]. unfold Wsb.
set (n := Z.of_nat (length (build_stack_bytes APH0 sp argv envp uid hw rdraw)) - 16 - (8 * argc + 8 * envc + 184)) in *.
pose proof (Z.div_mod n 8 ltac:(lia)) as D. rewrite Hm in D. lia.
Qed.
Theorem entg_strblock : ltac2:(TCodec.tc2 tcn__Ja0UsageEntryK "R3'R:yR0%211'>&QG&QF&R;vR8%2271&QJ+8&QK&7'8y8%?11%311vQN%6221%811%;2:1%@2=1vR1%;271%=11%@2?1%E251+UH%G221r1%H2M1%K231&QH&QM&J&Q9vR>vR2vR7%574Q0FA321%L2I1%N11%Q52Q21+@%;221%=2?1%Q;2?1'?':%11Q2&L&Q8&Q?vFvQOvE%43321vR4%7221vGr2%;3321&QD%18LQHQ>Q9KJI3%A3?31p0C1pU2R01").
Proof.
intros x Hxr. pose proof g_rng as SR. pose proof g_bounds as GB. unfold mrestrict. rewrite (g_vis_high x ltac:(lia)).
apply (hbi_argblock ASEGS0 ASAN0 APH0 sp rdraw brk0 argv envp uid hw fs E cs R FULL model HC).
rewrite hbi_argH. rewrite g_sp0. pose proof wsb_eqG as W.
apply andb_true_intro. split; [apply Z.leb_le; lia|]. apply orb_true_iff. left. apply orb_true_iff. right.
apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia].
Qed.
Theorem entg_str0 : ltac2:(TCodec.tc2 tcn__Ja0UsageEntryK "R5'>'?':'8'R:y8%211%411%611&QC&Q:&L&Q8&Q?vFvQOvE%43321vR4%7221vG%:221&Q4vR8vQNvR1(1%544321&B&7&C(9%11J%34J791%52L1u1%8221%L4K@:1(2&3(5&R9z%22Q61%43Q61<%63Q7<1%82Q71%Q>3Q7:1'D&R;yR0%221H&QF%423N&QJ+8&QK%L2QBQ1%211%5241%8271%Q02QFQ4%611%9281%<241+UH%>221%R23C@1%R42E1").
Proof.
pose proof g_rng as SR. pose proof g_bounds as GB.
assert (Hk' : (0 < length argv)%nat) by lia.
pose proof (u_cat_argv_ptr APH0 sp rdraw argv envp uid hw Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) 0%nat Hk') as Hu.
assert (CS : Z.of_nat (cat_struct_size argv envp) = 8 * argc + 8 * envc + 184).
{ unfold cat_struct_size, auxv_size. lia. }
pose proof (bsb_len_lower APH0 sp argv envp uid hw rdraw) as Hlow.
pose proof (total_arg_bytes_firstn_le 1%nat argv) as Hmono.
pose proof (total_arg_bytes_firstn_S argv 0%nat Hk') as Hstep.
pose proof (bsb_nw APH0 sp argv envp uid hw rdraw Hva Hve ltac:(unfold sp_window_hi; lia)) as Hnw.
assert (T0 : total_arg_bytes_nat (firstn 0 argv) = 0%nat) by reflexivity. rewrite T0 in Hu, Hstep.
split; [|rewrite Hu; lia].
rewrite <- (read_argv_cstr_k APH0 ASEGS0 sp argv envp 0%nat uid hw rdraw Hk' Hnw).
rewrite <- (rdn_wmem_stack ASEGS0 APH0 sp argv envp uid hw rdraw) by lia.
apply rdn_ext; [lia|]. intros x Hxr. unfold wmem. apply entg_strblock. lia.
Qed.
Theorem entg_str0_hi : ltac2:(TCodec.tc2 tcn__Ja0UsageEntryK "Q2&QG&QF&R;yR0&Q4vR8vQNvR1(1%544321%8271&QK&7'R:y8%211&C'8%113(9%115%543=?1%:271%<11%G2>1+1%I221+@%K221&QL+2+Q?%3221%Q1251").
Proof.
pose proof g_rng as SR. pose proof g_bounds as GB.
assert (Hk' : (0 < length argv)%nat) by lia.
pose proof (u_cat_argv_ptr APH0 sp rdraw argv envp uid hw Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) 0%nat Hk') as Hu.
pose proof (bsb_len_lower APH0 sp argv envp uid hw rdraw) as Hlow.
pose proof (total_arg_bytes_firstn_le 1%nat argv) as Hmono.
pose proof (total_arg_bytes_firstn_S argv 0%nat Hk') as Hstep.
assert (T0 : total_arg_bytes_nat (firstn 0 argv) = 0%nat) by reflexivity. rewrite T0 in Hu, Hstep.
destruct g_simg_top as (T1 & T2 & _). rewrite Hu. lia.
Qed.
Hypothesis CHKS : stk_chk cs = true.
#[local] Abbreviation SIMGx := (entry_stack_image APH0 sp argv envp uid hw rdraw).
#[local] Abbreviation LBx := (Z.of_nat (length (build_stack_bytes APH0 sp argv envp uid hw rdraw))).
Lemma g_argH_defined : ltac2:(TCodec.tc2 tcn__Ja0UsageEntryK "QC'R:yR0%211'>&QG&R;vR8%2261r1%4281%6231&QH&QF&QK&7y8%@11&I&Q9vQNvR1vR>vR2vR7%776B54321%;291%=11%?2D1%A2C1%J2C1'?'4&MvEr2%39AM<@?>=21(=%73621&A':%11HvGr3%211(0%11M%@3631%911p0;1p0D1pU2Q@1").
Proof. eapply (argH_defined sp brk0 rdraw argv envp uid hw fs); eassumption. Qed.
Section SE.
Local Abbreviation SEC_T_entg_stack_defined := (ltac2:(TCodec.tc2 tcn__Ja0UsageEntryK "Q='D'>&QGzr1%3221&QH&QK&7'R:y8%211&I&Q9vR8vQNvR1vR>vR2vR7%877654321%=2:1%?11%A2C1%G2C1&A'?':%11AvG&R9yR0&QF&R;%123Dr2%4221%7261%911(0%11M%?3=31%A11p0C1pT8Q<1")) (only parsing).
Variable i : ltac:(sec_ty2 constr:(SEC_T_entg_stack_defined) 0%nat 0%nat).
Theorem entg_stack_defined : ltac:(sec_stmt2 constr:(SEC_T_entg_stack_defined) 1%nat 0%nat).
Proof.
intros Hi.
pose proof g_rng as SR. pose proof g_bounds as GB. destruct g_simg_top as (T1 & T2 & _).
destruct (stk_chk_parts cs CHKS) as (CA & LA & LR & (bi & CB)).
destruct (drv_chk_parts cs CHKD) as (_ & _ & L1 & _ & _ & _ & _ & _ & K0 & K8 & K16 & _).
destruct (hbi_vals ASEGS0 ASAN0 APH0 sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit E cs R FULL model HC)
as (_ & _ & _ & _ & _ & _ & U4 & _).
destruct g_vals as (V1 & V2 & _ & V0).
pose proof wsb_eqG as WE.
destruct (bsb_ge APH0 sp rdraw argv envp uid hw) as [BG _].
assert (UX : bv_unsigned (Z_to_bv 64 (usp + i)) = usp + i) by (apply u_small; lia).
assert (KW : forall b off v d, kfind_word (kn cs) b off 8 = Some v -> lin_nowrapR (kn cs) b = true ->
(flat E (SA b off) 8 -> estart E (SA b off) = usp + d) -> d <= i < d + 8 -> FULL (Z_to_bv 64 (usp + i)) <> None).
{ intros b off v d Hk Hl Hst Hd.
destruct (hb_word_at ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok AH E cs R FULL model b off 8 v HC Hk)
as (_ & Hf & Hr & _).
rewrite (hb_adenot E _ _ Hf), (Hst Hf) in Hr.
apply (rdn_bytes_some ASEGS0 ASAN0 asan0_in_hull FULL _ 8 _ Hr).
- rewrite UX, u_small by lia. change (Z.of_nat 8) with 8. lia.
- rewrite UX. unfold in_hull. cbn [img_lo img_hi ASAN0]. apply andb_false_iff. right. apply Z.ltb_ge. lia. }
destruct (Z_lt_le_dec i 24) as [C1|C1].
{
assert (ST : forall off, flat E (SA e_sp0 off) 8 -> estart E (SA e_sp0 off) = usp + off)
by (intros off _; rewrite hb_estart; fold (uE E e_sp0); rewrite g_sp0; reflexivity).
destruct (Z_lt_le_dec i 8); [apply (KW e_sp0 0 _ 0 K0 L1 (ST 0)); lia|].
destruct (Z_lt_le_dec i 16); [apply (KW e_sp0 8 _ 8 K8 L1 (ST 8)); lia | apply (KW e_sp0 16 _ 16 K16 L1 (ST 16)); lia]. }
destruct (Z_lt_le_dec i (8 * argc + 8 * envc + 24)) as [C2|C2].
{ apply g_argH_defined; [rewrite UX; lia|]. rewrite hbi_argH, g_sp0, UX.
apply andb_true_intro. split; [apply Z.leb_le; lia|]. apply orb_true_iff. left. apply orb_true_iff. left.
apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]. }
destruct (Z_lt_le_dec i (8 * argc + 8 * envc + 184)) as [C3|C3].
{
assert (UA : uE E KE_AUX = usp + 8 * argc + 8 * envc).
{ unfold uE. remember (bv_unsigned (edenot E KE_AUX)) as s0 eqn:Es. LINEQ KE_AUX LA H. rewrite <- Es in H. lia. }
assert (ST : forall off, flat E (SA KE_AUX off) 8 -> estart E (SA KE_AUX off) = usp + (8 * argc + 8 * envc + off))
by (intros off _; rewrite hb_estart; fold (uE E KE_AUX); rewrite UA; ring).
set (k := (i - (8 * argc + 8 * envc)) / 8).
assert (Hk : i - (8 * argc + 8 * envc) = 8 * k + (i - (8 * argc + 8 * envc)) mod 8) by (apply Z.div_mod; lia).
pose proof (Z.mod_pos_bound (i - (8 * argc + 8 * envc)) 8 ltac:(lia)) as Hm.
assert (Hin : In (8 * k) AUX_OFFS).
{ assert (Hk3 : 3 <= k < 23) by lia. unfold AUX_OFFS.
assert (Hc : k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15
\/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22) by lia.
repeat (destruct Hc as [->|Hc]; [cbn [In]; tauto|]). subst k. rewrite Hc. cbn [In]. tauto. }
destruct (CA _ Hin) as (v & Hv).
apply (KW KE_AUX (8 * k) v (8 * argc + 8 * envc + 8 * k) Hv LA (ST (8 * k))). lia. }
destruct (Z_lt_le_dec i (LBx - 16)) as [C4|C4].
{ apply g_argH_defined; [rewrite UX; lia|]. rewrite hbi_argH, g_sp0, UX.
apply andb_true_intro. split; [apply Z.leb_le; lia|]. apply orb_true_iff. left. apply orb_true_iff. right.
apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]. }
destruct (Z_lt_le_dec i LBx) as [C5|C5].
{
assert (UR : uE E KE_RND = usp + 8 * argc + 8 * envc + 8 * Wsb APH0 sp rdraw argv envp uid hw).
{ unfold uE. remember (bv_unsigned (edenot E KE_RND)) as s0 eqn:Es. LINEQ KE_RND LR H. rewrite <- Es in H. rewrite U4 in H. lia. }
pose proof (hb_kn ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ HC (kfind_blob16_In _ _ _ _ CB)) as (Hf & _ & Hb).
assert (EL : elenZ E (ELit 16) = 16) by (unfold elenZ; cbn [edenot]; apply u64_lit; lia).
rewrite EL in Hb. rewrite hb_estart in Hb. fold (uE E KE_RND) in Hb. rewrite UR in Hb.
specialize (Hb (i - (LBx - 16)) ltac:(lia)).
replace (usp + 8 * argc + 8 * envc + 8 * Wsb APH0 sp rdraw argv envp uid hw + 184 + (i - (LBx - 16))) with (usp + i) in Hb by lia.
exact (mr_defined sp rdraw argv envp uid hw cs E FULL model _ _ Hb). }
apply g_argH_defined; [rewrite UX; lia|]. rewrite hbi_argH, g_sp0, UX.
apply andb_true_intro. split; [apply Z.leb_le; lia|]. apply orb_true_iff. right.
apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia].
Qed.
End SE.
Corollary entg_stack_defined_top : ltac2:(TCodec.tc2 tcn__Ja0UsageEntryK "Q='D'?&QIr1+TP0%3221z%63721&QGr2&QF&R;yR0vR8%3221%521;%8271'>%:2<?&QH&QMr4%2218%42D1%7261&A':'R:y8%211%411vG&R9%G2CH%22F1%411(0%118%Q53831%>11p0@1pT8Q91p0J1p0Q41pTLQ<1").
Proof.
intros top Hm Hle i Hi. apply entg_stack_defined. destruct g_simg_top as (T1 & T2 & T3).
pose proof (bsb_ge APH0 sp rdraw argv envp uid hw) as [G _]. pose proof g_bounds as GB.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
Theorem entg_str0_defined : ltac2:(TCodec.tc2 tcn__Ja0UsageEntryK "QD'D'>&QGzr1%3221&QH&QF&QK&7'R:y8%211&C'8%113(1vQN(9%117%745431%<291%>11+1%A221+@%C221%E2G1%K2G1&A'?':%11DvG&R9yR0&R;&Q4vR8vR1%342G1H%5261r2%Q4221%:291%<11(0%11Q3%B3@31%D11p0F1pT8QC1").
Proof.
intros i Hi. pose proof g_rng as SR. pose proof g_bounds as GB.
assert (Hk' : (0 < length argv)%nat) by lia.
pose proof (u_cat_argv_ptr APH0 sp rdraw argv envp uid hw Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) 0%nat Hk') as Hu.
pose proof (bsb_len_lower APH0 sp argv envp uid hw rdraw) as Hlow.
pose proof (total_arg_bytes_firstn_le 1%nat argv) as Hmono.
pose proof (total_arg_bytes_firstn_S argv 0%nat Hk') as Hstep.
assert (T0 : total_arg_bytes_nat (firstn 0 argv) = 0%nat) by reflexivity. rewrite T0 in Hu, Hstep.
destruct g_simg_top as (_ & T2 & _).
set (q := bv_unsigned (cat_argv_ptr sp argv envp 0)) in *.
replace (q + i) with (usp + (q - usp + i)) by ring.
apply entg_stack_defined. lia.
Qed.
Theorem entg_tid : ltac2:(TCodec.tc2 tcn__Ja0UsageEntryK "QE'?'4&QAvQO%211(=%63521'@'R:yR0%211'>&QG+1&R;r1%2271%5241+SoooO%7231%9231':'8y8%@11%311%511&QC&Q:&L&Q8&Q?vFvE%332O1vR4%6221vG%9221&R9+V]kVH%22Q01u4%@4?521(2&H%124O%32F1%Q@3F51%Q62M1qTJQ81%Q<2Q91p0Q>1").
Proof.
intros CT. unfold tid_chk in CT.
destruct (kfind_word (kn cs) (ELit 0) 0x66ecd8 4) as [v|] eqn:K2; [|discriminate].
exists (edenot E v).
pose proof (hb_knb ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ HC CT) as RG. cbn [kentry_ok] in RG.
split; [exact RG|].
eapply (ent_litcell sp brk0 rdraw argv envp uid hw fs); try eassumption. lia.
Qed.
End EntryG.
