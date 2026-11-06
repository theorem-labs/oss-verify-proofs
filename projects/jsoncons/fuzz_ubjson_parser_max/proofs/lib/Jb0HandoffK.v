(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AgentLib BackingAlgebra AsanPlacement AsanCeil AxSymExec3K AxSymExec3SoundK AxSymRun3K
AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK Jb0DefsK Jb0PlanImagesK HandoffBridgeK HandoffLedgerK HandoffBInvK ArtRuns ArtBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Jb0HandoffK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtBridge."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtRuns."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanInitK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanK.APK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundK.APSK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3K.AX2K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HandoffBInvK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HandoffLedgerK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DefsK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0HandoffK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0HandoffK.As0Handoff."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0BUDGET"; "1Some"; "1app"; "1bool"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"; "2ex"; "3Z"; "0E"; "0FULL"; "0KMAX"]; ["0LENMAX"; "4segments_reserved"; "5Model"; "5m_vmmaps"; "5vm_maps"; "5vm_noaccess"; "6bvmap"; "0R"; "7BInv"; "7bridge_static"; "8aev"; "9LIMIT"; "9SINV0"; "9argH0"; ":a_ghost"; ":a_hlz"]; [":a_hna"; ":a_maps"; ":a_vis"; ":am_base"; ":amap"; ":e_sp0"; ":kn"; ":no_fog"; ";cs_ok"; ";uE"; "<env"; "<expr"; "<xlo"; "=M_GAP"; "=M_HIGH"; "=M_LOW"]; [">hops_in_maps"; ">vis_off_band"; ">vis_sh_wr"; "?APH0"; "?ASAN0"; "?ASEGS0"; "Aas0_A0"; "Aas0_BASE"; "Aas0_RES"; "@RESm0"; "BIn"; "Bforallb"; "Clt"; "Csub"; "0argv"; "0b"]; ["0brk0"; "0cs"; "0envp"; "0fs"; "0hw"; "0lo"; "0m"; "0model"; "0rdraw"; "0s"; "0sp"; "Dbv"; "Dbv_unsigned"; "0uid"]]).
Definition M_KSPACE : amap := {| am_base := EMd M_MUL (ELit 4096) (EVar 224); am_len := ELit 0x2000011000; am_kind := KRW |}.
Definition M_PTRARR : amap := {| am_base := EMd M_MUL (ELit 4096) (EVar 250); am_len := ELit 0x800000; am_kind := KNONELAZY |}.
Definition RESm0 : list amap := [M_KSPACE; M_PTRARR].
Definition as0_chk (cs : acs) : bool :=
(no_fog (a_maps cs) && hops_in_maps (a_maps cs) (a_hna cs) && hops_in_maps (a_maps cs) (a_hlz cs)
&& forallb (vis_sh_wr ASAN0 (kn cs)) (a_vis cs) && forallb (vis_off_band (kn cs)) (a_vis cs ++ a_ghost cs)
&& existsb (amap_eqb M_LOW) (a_maps cs) && existsb (amap_eqb M_GAP) (a_maps cs) && existsb (amap_eqb M_HIGH) (a_maps cs)
&& forallb (fun m => existsb (amap_eqb m) (a_maps cs)) RESm0
&& forallb (fun m => match xlo (kn cs) (am_base m) with Some lo => Z.ltb 0 lo | None => false end) RESm0)%bool.
Lemma asan0_resv_pos : ltac2:(TCodec.tc2 tcn__Jb0HandoffK "F'R;yR0%211&QJ'7%1233(6r2r1%347721&A&QE%211%:3841&QLz&R<%12@:%4231p061pTDB1pT0C1").
Proof.
intros b s H. rewrite asan0_res_eq in H.
destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; rewrite u64_lit by lia; lia.
Qed.
Section As0Handoff.
Variable sp brk0 : word.
Variable rdraw : EntryDraw.
Variable argv envp : list (list byte).
Variables uid hw : word.
Variable fs : Fs.Fs.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
#[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 argv envp uid hw).
#[local] Notation argH := (argH0 APH0 sp rdraw argv envp uid hw).
#[local] Notation CSOK := (cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).
Let AH := argH0_high APH0 sp rdraw argv envp uid hw Hsp Hva.
Variables BUDGET LENMAX KMAX : Z.
Hypothesis BUD : 0 <= BUDGET /\ 0 <= KMAX /\ 0 <= LENMAX < 2 ^ 62.
Variable EXTRA : list (Z * Z).
Hypothesis EXTRA_wf : A_wf EXTRA.
Variable cs : acs.
Hypothesis CHK : as0_chk cs = true.
Hypothesis BUD_le : a_eager cs + a_abytes cs + A_bytes EXTRA + BUDGET <= AsanInitK.LIMIT.
Hypothesis GAP : AsanCeil.bottomup_floor + LENMAX + (a_totsz cs + BUDGET)
+ (Z.of_nat (length (segments_reserved ASEGS0) + length (a_maps cs)) + KMAX) * (LENMAX + 4095) <= AsanCeil.alloc_ceiling.
Lemma as0_chk_parts : ltac2:(TCodec.tc2 tcn__Jb0HandoffK "RD'9':'3&Q7&Q1vR1%211%411(8%83721&Q@&Q0%117%3271%=3<16&O%11;%72;1%A3@1:&QK'7'Q;%2211&QB&QD&Q6%11E%4231&Q2%11H%;3831%N3M1G&QA%117&2&N%11O%33?81%C3@51%Q63Q51O&QJ'Q4&Q?%3321Q5&Q=%5341Q7&Q>%7361Q9r1&QI%:3921r2%<3;1Q>p031pT>=1';'<'5%112&Q<&Q3r3%211%42Q51(1%129A%R13831&QLz%221E%R6241qT<?1%A2@1p0G1pT>Q11%R;2E1%R<2M1%R=2Q01%R>2Q31%R?2Q81%R@2QA1%RA2QO1%RB2R41%RC2R:1").
Proof.
unfold as0_chk in CHK. repeat (apply andb_prop in CHK as [CHK ?]).
repeat split; try assumption; try (apply hl_in_amapb; assumption).
- intros m Hm. apply hl_in_amapb. exact (proj1 (forallb_forall _ _) H0 m Hm).
- intros m Hm. pose proof (proj1 (forallb_forall _ _) H m Hm) as Hx. cbn beta in Hx.
destruct (xlo (kn cs) (am_base m)) as [lo|]; [|discriminate]. exists lo. split; [reflexivity | apply Z.ltb_lt; exact Hx].
Qed.
Definition as0_RES (E : env) : list (Z * Z) := RES_of RESm0 E.
Definition as0_BASE : Z := BASE_of cs EXTRA.
Definition as0_A0 (E : env) : list (Z * Z) := A0_of ASAN0 cs EXTRA E.
Theorem as0_bridge_static : ltac2:(TCodec.tc2 tcn__Jb0HandoffK "QO'Q:&Fy5'R;yR0%211%5241'5y8%611%311p061'B'Q8&QE&QD&K&L&QCvR:vR8vR0vQNvR2vR=vR4%9887654321&M%17:986543vR3r4vR1r3r2r1%F;EDC97654321'I&D&C%116%311&A%11L&E%115&QHr5%211&QM&Q9&Q5%2251+XPPP0%5221v0v@v?%E9Q;A?=:4321p0G1pT@Q?1pNQA1pQ@QG1pLQN1").
Proof.
intros E R FULL model HC. destruct as0_chk_parts as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
exact (hb_bridge_static ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok ltac:(cbn; unfold SHB_LO; lia) asan0_res_hull asan0_resv_pos
cs C1 C6 C7 C8 RESm0 C9 C10 BUDGET LENMAX KMAX BUD GAP E R FULL model HC).
Qed.
Theorem as0_binv_main : ltac2:(TCodec.tc2 tcn__Jb0HandoffK "R1'Q:&Fy5'R;yR0%211%5241'5y8%611%311p061'B'Q8&QE&QD&K&L&QCvR:vR8vR0vQNvR2vR=vR4%9887654321&M%17:986543vR3r4vR1r3r2r1%F;EDC97654321'H&D&C%116%311&A%11L&E%115&QM&Q9r5&Q5%3221+XPPP0%6221&QGv0(4'J%211&QF%11;%G;Q=CA?87631KJp0I1pT@QA1pNQC1pQ@QI1pLR01").
Proof.
intros E R FULL model HC. destruct as0_chk_parts as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
exact (hb_binv_main ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok asan0_shadow_ok AH ltac:(cbn; unfold SHB_LO; lia)
cs C1 C2 C3 C4 C5 C6 C8 BUDGET LENMAX KMAX BUD EXTRA EXTRA_wf BUD_le E R FULL model HC).
Qed.
End As0Handoff.
