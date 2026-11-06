(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core L5CoreKit
PmLayout PmLayoutU PmModel PmModelFacts PmStatics PmSpecs PmSpecsU PmStep PmKeep PmKitU PmTopU PmUHarnessStmts PmUHarnessKit PmUHarnessP.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmUHarness1 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.LibIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsU.PMU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmTopU.PMTU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmUHarnessStmts.PMUH."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.Arith.PeanoNat.Nat."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1bool"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "1true"; "2eq"; "3Z"; "0HI"; "0K"; "0KS"; "0L"; "0LB"]; ["4Model"; "4event"; "4m_halted"; "4m_vm_lazy"; "4m_vm_materialized"; "4m_vmmaps"; "5bvmap"; "0M"; "0M1"; "0R"; "0R1"; "6credit"; "6hi_heap"; "7SCFG"; "8lib_pre"; "8ls_state"]; ["9vstr"; ":cfg"; ";str_ctor_spec"; "<TopLS"; "<TopLay"; "=CSK"; "=H1"; ">FPState"; "?srealizes"; "@loaded_segments"; "0SCFG_P"; "Aeqb"; "BIn"; "Bexistsb"; "Cof_nat"; "0cr"]; ["0cr1"; "0fx"; "0fx1"; "0g"; "0k"; "0model"; "0model1"; "0payload"; "0ptr"; "0ra"; "0s"; "0sp"; "Dbv"; "0x"]]).
Module PMUH1.
Import PMU. Import PMUH.
Local Ltac lia := PMK.alia.
Section Stage.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMU.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKU.klayout_U L LY.
Let SF := PMKU.sfoot_U L LY.
Lemma CSK_in_KS : ltac2:(TCodec.tc2 tcn__PmUHarness1 "I'3'4%211&Q<r1&Q5%33521'9'1&Q=&Q;r2%211r3%53=21(8%93821p0;1pS:A1r4%A3C91p0?1pS:E1p051pLF1").
Proof. intros KS. intros H k Hk. apply L5K.In_of_mem. apply H. exact Hk. Qed.
Lemma stage1 : ltac2:(TCodec.tc2 tcn__PmUHarness1 "SO&Q2vQ:v>v;%43321'Q7&O&Q3%211'3'7':%2211%411&K'QLy8%211%911&Fy5yR0%711%4231'6%118p041'@'A%D11!pSL21'N&Q4%11Q0r;r:r9r8r7r6r5r4r3%<;:Q5987654321&L&E%114%35Q==<61'9%J1L&B%11:(0%11Q0%63531%Q>2Q2Q2%Q@11&C%11B(5%115%=3531%QF1Q9&D%11I%61Q<%B3421%81Q8%M11'Q0&Q6r@r?r>rDrB&Q>&2rA%22QO1%411rFrErGr2r1%@@RERD?>=<;6543Q>Q=Q<21'Q8&Q9&M%11RJ&Q1+V`fH%265QGQF1QEQD%74641Ep091pSFK1pS2RD1pS>R81pQBR:1pQFR>1pS6S11rC+V`eL%=6@2R61R5R4%B4A?1R4p051p0Q71p0Q:1p0Q@1p0QH1p0R01p0R51pJRC1pS<RH1pQ@RJ1pQDRN1pS@S41pSDS<1pSBS=1pSHS>1pS0S<1pQ0S>1pS8SD1pS4SH1p0SJ1").
Proof.
intros STR fx g LB cr sp ptr ra payload R M model K PRE HH Mh Ml Mm K0 KONT.
destruct PRE as [Rra RAok Rsp Rgp Rtp Ra0 Ra1 LEN PTR PAY STK CRED STAT].
cbn [ll_heap ll_stack ll_empty ll_credit ll_gp PMTU.TopLay] in *.
set (n := Z.of_nat (length payload)) in *.
destruct STK as (A16 & SLO & SHI & STOP & SOK & SDEF).
rewrite (ly_tp L LY) in Rtp. rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in Ra0. rewrite L5K.rl11 in Ra1.
assert (STK0 : L5C.stk (hl_sptop L) M sp 65536).
{ split; [exact A16|]. split; [lia|]. split; [lia|]. split; [lia|]. intros i Hi. apply SDEF. lia. }
pose proof (L5C.stk_writable RSEGS _ M sp 65536 STK0) as WR0.
assert (LBhi : forall b, In b LB -> fst b + snd b <= hl_ceil L).
{ intros b Hb. pose proof (proj1 (hio_wf L SCFG HI HIok LB cr M _ HH) b Hb) as ((Q0 & Q1 & Q2 & Q3 & Q4) & _). exact Q4. }
destruct STAT as (BASE & SLOC & SSYS & SERR).
cfeed P (PMUHP.huA_conc fx R M (fun j => match j with 2%nat => sp | _ => 0 end)) ltac:(first [PMK.sc]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ & MS & KS & A1 & A2 & A10 & A11 & A12 & C0 & C1)); PMK.pvz_clrT.
unfold PMSP.cfg.
apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x342bc R1 0x34488 M1 (fun a => sp - 16 <= a < sp - 16 + 16) K HH Mh Ml ltac:(lia) MS MG FRZ).
{ intros a Ha. apply (PMK.cwr_stack L LB M sp 65536 a STK0). lia. }
{ intros a. apply PMK.rng_dec. }
intros HH1.
assert (STK1 : L5C.stk (hl_sptop L) M1 (sp - 752) (65536 - 752)).
{ apply (PMK.stk_call L M1 sp 65536 (sp - 752) (65536 - 752)); [apply (L5C.stk_grows _ M M1 _ _ MG STK0)|lia|lia|lia|].
clear - A16. replace (sp - 752) with (sp + (-47) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
assert (EK1 : PMK.ek L LB sp 65536 [] M M1).
{ apply (PMK.ek_piece_in' RSEGS L KL LB sp 65536 [] M M1 _ FRZ); [lia|lia|exact LBhi|]. intros a Ha. left. lia. }
assert (CORE1 : PMUH.hcore L R M model sp ra LB R1 M1 model).
{ unfold PMUH.hcore, PMUH.fb, FRAME, SCR.
split; [exact A2|].
split. { intros k Hk. apply KS. revert k Hk. apply CSK_in_KS. intros k Hk. unfold CSK in Hk. cbn in Hk.
repeat (destruct Hk as [<-|Hk]; [vm_compute; reflexivity|]). destruct Hk. }
split. { replace (sp - 752 + 744) with (sp - 8) by lia. rewrite Rra, L5.unsigned_lit in C1 by lia. exact C1. }
split. { replace (sp - 752 + 736) with (sp - 16) by lia. exact C0. }
split; [exact STK1|].
split. { intros i Hi. apply MG. destruct STK0 as (_ & _ & _ & _ & D0). replace (sp - 752 + i) with (sp - 65536 + (64784 + i)) by lia. apply D0. lia. }
split; [lia|].
split. { intros a Ha. apply EK1. destruct Ha as (H1 & H2 & H3 & _). split; [exact H1|]. split; [exact H2|]. split; [exact H3| apply L5C.outside_nil]. }
split; [exact LBhi|].
split. { apply (PMKP.base_ok_keep RSEGS AD L KL SF LB sp 65536 [] M M1 EK1); first [exact BASE | intros a _; apply L5C.outside_nil]. }
split; [apply L5C.model_but_vm_refl| repeat split; assumption]. }
pose proof (ly_kpm L LY) as HK. pose proof (ly_bov L LY) as HB.
pose proof (PMF.pot_call_le L n HK HB ltac:(lia)) as (PC1 & PC2).
destruct CRED as (CR1 & CR2). unfold PMTU.TOPK, PMTU.TOPB in CR1, CR2. cbn [fst snd] in CR1, CR2, PC1, PC2.
assert (Hn0 : 0 <= n) by (unfold n; lia).
assert (A8 : (sp - 40) mod 8 = 0).
{ clear - A16. apply Z.mod_divide in A16; [|lia]. destruct A16 as (q & ->). replace (q * 16 - 40) with ((2 * q - 5) * 8) by lia. apply Z.mod_mul. lia. }
unfold PMU.str_ctor_spec, PMSP.str_ctor_spec in STR.
apply (STR fx1 R1 M1 model K LB cr (sp - 40) ptr n (sp - 752) 213720 HH1).
- repeat split; assumption.
- exact K0.
- unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [split; [lia| reflexivity]|]. split; [exact A2|].
split; [rewrite (KS 3%nat) by PMK.inl; exact Rgp|]. split; [rewrite (KS 4%nat) by PMK.inl; exact Rtp|].
apply (PMK.stk_call L M1 (sp - 752) (65536 - 752) (sp - 752) (PMSP.pm_scr 0) STK1); [lia| unfold PMSP.pm_scr; lia| unfold PMSP.pm_scr; lia|].
destruct STK1 as (X & _). exact X.
- rewrite L5K.rl10. exact A10.
- rewrite L5K.rl11, A11. exact Ra0.
- rewrite L5K.rl12, A12. exact Ra1.
- lia.
- lia.
- lia.
- exact A8.
- destruct CORE1 as (_ & _ & _ & _ & _ & DFR1 & _). unfold PMUH.fb, FRAME in DFR1. apply (L5.defined_sub M1 (sp - 752) 752 (sp - 40) 24 DFR1); lia.
- destruct PTR as [(E0 & _)|(Hp & Hin)]; [left; unfold n; rewrite E0; reflexivity|]. right. exists ptr, n. split; [exact Hin| lia].
- unfold PMSP.credit_le, PM.cost1. cbn [fst snd]. unfold PM.pot_call, PM.credit_add, PM.cost1, PM.pot_stack, PM.pot_text in PC1, PC2. cbn [fst snd PM.vs_cap] in PC1, PC2. lia.
- intros fx2 R2 M2 model2 s cr2 RP VS SZ SH LG HP CK MB HH2.
apply (KONT fx2 R2 M2 model2 cr2 s). unfold PMUH.H1.
assert (EKc : PMK.ek L LB (sp - 752) (PMSP.pm_scr 0) [(sp - 40, 24)] M1 M2) by (apply (PMK.ek_of_hpres L); exact HP).
split. { apply (PMUHK.hcore_call L LY R M model sp ra LB R1 M1 model R2 M2 model2 LB (PMSP.pm_scr 0) [(sp - 40, 24)] CORE1 RP HP (incl_refl LB)); [unfold PMSP.pm_scr, SCR, FRAME; lia| |exact MB].
intros a (r & [<-|[]] & Hr). unfold L5.in_rng in Hr. cbn [fst snd] in Hr. left. unfold PMUH.fb, FRAME. lia. }
split. { unfold PMUH.fb, FRAME. replace (sp - 752 + 712) with (sp - 40) by lia. exact VS. }
split; [exact SZ|].
split. { apply (PMUHK.hstat_keep L LY LB (sp - 752) (PMSP.pm_scr 0) [(sp - 40, 24)] M1 M2 EKc).
- intros a (r & [<-|[]] & Hr). unfold L5.in_rng in Hr. cbn [fst snd] in Hr. left. lia.
- apply (PMUHK.hstat_keep L LY LB sp 65536 [] M M1 EK1); [intros a (r & [] & _)|]. split; [exact SLOC| split; [exact SSYS| exact SERR]]. }
split; [exact HH2|].
split. { destruct CK as (CK1 & CK2). unfold PMSP.credit_keep, PMUH.P0, PMUH.rest1, PM.pot_call, PM.credit_add, PM.cost1, PMSP.cr0 in *. cbn [fst snd] in *. lia. }
intros c n' p E. destruct (Z_le_gt_dec n 22) as [X|X]; [rewrite (SH X) in E; discriminate| rewrite E in SZ; cbn in SZ; lia].
Qed.
End Stage.
End PMUH1.
