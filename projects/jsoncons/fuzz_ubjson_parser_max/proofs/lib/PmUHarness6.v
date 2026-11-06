(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core L5CoreKit
PmLayout PmLayoutU PmModel PmModelFacts PmStatics PmSpecs PmSpecsU PmStep PmKeep PmKitU PmTopU PmSpecsX PmUHarnessStmts PmUHarnessKit PmUHarnessP.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmUHarness6 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsU.PMU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmUHarnessStmts.PMUH."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1list"; "1nil"; "1option"; "2eq"; "3Z"; "0HI"; "0K"; "0L"; "0LB0"; "4Model"; "4event"; "5bvmap"; "0M"; "0M0"; "0M1"]; ["0R"; "0R0"; "0R1"; "6credit"; "7SCFG"; "8p_src"; "8p_tb"; "8pst"; "8strm"; "8vstr"; "9cfg"; ":vec_dtor_spec"; ";H5"; ";H6"; "<FPState"; "=srealizes"]; [">loaded_segments"; "0SCFG_P"; "?modulo"; "0be"; "0cr"; "0cr0"; "0fx"; "0fx1"; "0g"; "0model"; "0model0"; "0model1"; "0n"; "0p"; "0ra"; "0s"]; ["0s2"; "0sm"; "0sp"; "@bv"; "0x"]]).
Module PMUH6.
Import PMU. Import PMUH.
Local Ltac lia := PMK.alia.
Section Stage.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMU.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKU.klayout_U L LY.
Variable R0 : bvmap 5 word.
Variable M0 : word -> option byte.
Variable model0 : Model.
Variables (sp ra n : Z).
Variable LB0 : list (Z * Z).
Variable cr0 : credit.
Variable g : PMST.st.
Hypothesis Hn : 0 <= n < 2 ^ 26.
Hypothesis Hcr0 : PMSP.credit_le (512, 2 ^ 29 + 8 * n) cr0.
Hypothesis Hgp : getr R0 (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis Htp : getr R0 (reg 4) = Z_to_bv 64 (pa_tp AD).
Lemma m16_2 : ltac2:(TCodec.tc2 tcn__PmUHarness6 ">'5'4&Q2r1+@%3221z%63721r2+2%8221%:3;15p051pS:=1").
Proof. intros x. intros H. apply Z.mod_divide in H; [|lia]. destruct H as (q & ->). replace (q * 16) with ((q * 8) * 2) by lia. apply Z.mod_mul. lia. Qed.
Lemma stage6 : ltac2:(TCodec.tc2 tcn__PmUHarness6 "RM&KvQ1v8v6%43321'N&<y5'QCyR0%211%5241'3y8%611%311p061':&C'I'G'H'0'1';%211!pS:21&LvAv>vQ:vQBvQ>vQ<v9vQ5vQ8r:r9r8r7r6r5r4r3r2%CDQ=Q<BA@?>=<;:987654321(2%11I%411&Mr1r=r<r;&F%11C&E%11E%9EQJQIONMLKJIHG?>876531ED'O&Q0&D%11QO&J+V`k@%265HG1FE%74641Lp091pRHQE1pQ0QG1pQ6QM1pR@R41r>+V`jD%;6>2G1FE%@4?=1Q1p051p0M1p0Q11p@QF1pR8QL1pS4QN1pRLR01pS2R21pS0R31pR:R51pRDR71pLR91pQ2R?1pR>RF1p0RH1").
Proof using All.
intros VDT fx R M model cr s s2 p sm be K (CORE & VS & SZ & IA & PA & HST & EMONO & HH & CK) K0 KONT.
pose proof (PMUHK.hcore_facts L R0 M0 model0 sp ra LB0 R M model CORE) as (Hsp & Rsp & Rng & A16 & WR & STK).
pose proof STK as (A16f & SLO & SHI & STOP & _).
pose proof CORE as (_ & Hcs & _ & _ & _ & _ & SPT & _ & _ & BASE & _ & (Mh & Ml & Mm)).
set (LBX := PM.vs_own s2 ++ PM.vs_own s ++ LB0) in *.
set (LBc := PM.parser_own p ++ LBX) in *.
set (LB6 := PM.src_own (PM.p_src p) ++ PM.vs_own (PM.p_tb p) ++ LBX).
assert (BRc : PMUHK.brange L LBc) by (apply (PMUHK.brange_of_heap L HI LY HIok LBc LBc cr M _ HH); apply incl_refl).
assert (LBhic : forall x, In x LBc -> fst x + snd x <= hl_ceil L) by (intros (B & m) Hx; destruct (BRc B m Hx) as (_ & _ & Q); exact Q).
assert (SCx : 0 <= 65536 - 752) by lia.
unfold PMUH.fb, FRAME in PA.
destruct PA as (H0 & D & _ & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & _ & TB & VEC & _).
pose proof VEC as (V0 & V8 & V16 & Hk & Hlen & Hal & DB & _ & _ & EL).
set (b := PM.p_b p) in *. set (k := PM.p_k p) in *.
assert (Bv : In (b, 32 * 2 ^ k) LBc) by (unfold LBc, PM.parser_own, PM.src_own, PM.vec_own; cbn; auto).
assert (Bq : In (PM.sr_qc (PM.p_src p), PM.CHUNK) LBc) by (unfold LBc, PM.parser_own, PM.src_own; cbn; auto).
destruct (BRc _ _ Bv) as (Vb0 & Vb1 & Vb4). pose proof (PM.pow2_pos k ltac:(lia)) as P2k.
replace (sp - 752 + 40 + 360) with (sp - 352) in V0 by lia. replace (sp - 752 + 40 + 360 + 16) with (sp - 336) in V16 by lia.
pose proof (m16_2 b Hal) as Hal2.
cfeed P (PMUHP.huG_conc fx R M (fun j => match j with 2%nat => sp | _ => 0 end)) ltac:(first [PMK.sc]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ0 & MS & KS & A1 & A10 & C0 & C1)); PMK.pvz_clrT.
set (P := fun a => (sp - 712 <= a < sp - 712 + 8) \/ (sp - 744 <= a < sp - 744 + 8)).
assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha N. apply FRZ0; [exact Ha| intro X; apply N; left; exact X| intro X; apply N; right; exact X]. }
assert (PF : forall a, P a -> PMUH.fb sp <= a < PMUH.fb sp + 752) by (intros a [X|X]; unfold PMUH.fb, FRAME; lia).
unfold PMSP.cfg.
apply (PMK.spiece RSEGS L HI KL HIok LBc cr M model fx fx1 R 0x34354 R1 0x35928 M1 P K HH Mh Ml ltac:(lia) MS MG FRZ).
{ intros a Pa. apply PF in Pa. unfold PMUH.fb, FRAME in Pa. left. lia. }
{ intros a. apply PMK.or_dec; apply PMK.rng_dec. }
intros HH1.
assert (CORE1 : PMUH.hcore L R0 M0 model0 sp ra LB0 R1 M1 model).
{ apply (PMUHK.hcore_piece L LY R0 M0 model0 sp ra LB0 R M model R1 M1 P CORE MG FRZ); [intros a [X|X]; unfold PMUH.fb, FRAME; lia| rewrite (KS 2%nat) by PMK.inl; exact Rsp|].
intros k0 Hk0. apply KS. revert k0 Hk0. apply PMUH.CSK_in. vm_compute. reflexivity. }
assert (VS1 : PM.vstr_at RSEGS PMUH.T3 M1 (sp - 752 + 712) s).
{ eapply (PMUHK.vstr_keep_p L sp LBc M M1 P (65536 - 752) FRZ PF STK SCx BRc); [lia|lia| | |exact VS].
- intros i Hi [X|X]; lia.
- unfold LBc, LBX. apply incl_appr. apply incl_appr. apply incl_appl. apply incl_refl. }
assert (IA1 : PM.iss_at RSEGS AD PMUH.T3 M1 (sp - 752 + 440) s2 sm).
{ eapply (PMUHK.iss_keep_p L sp LBc M M1 P (65536 - 752) FRZ PF STK SCx BRc); [lia|lia| | |exact IA].
- intros i Hi [X|X]; lia.
- unfold LBc, LBX. apply incl_appr. apply incl_appl. apply incl_refl. }
assert (TB1 : PM.vstr_at RSEGS PMUH.T3 M1 (sp - 752 + 40 + 336) (PM.p_tb p)).
{ eapply (PMUHK.vstr_keep_p L sp LBc M M1 P (65536 - 752) FRZ PF STK SCx BRc); [lia|lia| | |exact TB].
- intros i Hi [X|X]; lia.
- unfold LBc, PM.parser_own. apply incl_appl. apply incl_appr. apply incl_appr. apply incl_refl. }
assert (SRC1 : PM.src_fields_at RSEGS PMUH.T3 M1 (sp - 752 + 40 + 24) (sp - 752 + 440) (sp - 752 + 440 + 16) (PM.p_src p)).
{ eapply (PMUHK.src_keep_p L sp LBc M M1 P (65536 - 752) FRZ PF STK SCx BRc); [lia|lia| |exact Bq|exact SRC]. intros i Hi [X|X]; lia. }
assert (NI1 : PM.nullis_at RSEGS AD PMUH.T3 M1 (sp - 752 + 40 + 32)).
{ eapply (PMUHK.nullis_keep_p M M1 P FRZ); [lia|lia| |exact NI]. intros i Hi [X|X]; lia. }
assert (HST1 : PMUH.hstat M1 true true be) by (apply (PMUHK.hstat_piece L LY sp LBc M M1 P FRZ PF true _ _ STK LBhic HST)).
assert (VEC1 : PM.vec_at RSEGS PMUH.T3 PMUH.T4 M1 (sp - 352) b k (PM.p_stk p)).
{ replace (sp - 352) with (sp - 752 + 40 + 360) by lia.
apply (PMF.vec_at_agree RSEGS M M1); [lia|lia|lia| pose proof (PMK.kl_img RSEGS L KL); lia| | |exact VEC].
- apply (PMUHK.agp M M1 P FRZ); [lia|lia|]. intros i Hi [X|X]; lia.
- apply (PMUHK.agp_block L sp LBc M M1 P (65536 - 752) FRZ PF STK SCx BRc _ _ Bv). }
pose proof (PMUHK.hcore_facts L R0 M0 model0 sp ra LB0 R1 M1 model CORE1) as (_ & Rsp1 & _ & _ & _ & STK1).
pose proof CORE1 as (_ & Hcs1 & _).
assert (SCd : 0 <= PMSP.pm_scr 0) by (unfold PMSP.pm_scr; lia).
assert (STKd : L5C.stk (hl_sptop L) M1 (sp - 752) (PMSP.pm_scr 0)).
{ apply (PMK.stk_call L M1 (sp - 752) (65536 - 752) (sp - 752) (PMSP.pm_scr 0) STK1); [lia| unfold PMSP.pm_scr; lia| unfold PMSP.pm_scr; lia| exact A16f]. }
unfold PMU.vec_dtor_spec, PMSX.vec_dtor_spec in VDT.
apply (VDT fx1 R1 M1 model K LBc cr (sp - 744) (sp - 352) b k (sp - 752) 213872 (PM.p_stk p) HH1).
{ repeat split; assumption. }
{ exact K0. }
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [split; [lia| reflexivity]|]. split; [exact Rsp1|].
split; [rewrite (Hcs1 3%nat) by (unfold CSK; cbn; auto); exact Hgp|]. split; [rewrite (Hcs1 4%nat) by (unfold CSK; cbn; auto); exact Htp|]. exact STKd. }
{ rewrite L5K.rl10. exact A10. }
{ lia. }
{ lia. }
{ exact C0. }
{ lia. }
{ lia. }
{ replace (sp - 352) with (sp - 752 + 50 * 8) by lia. rewrite Z.mod_add by lia. apply Z.mod_divide in A16f; [|lia]. destruct A16f as (q & ->). replace (q * 16) with ((q * 2) * 8) by lia. apply Z.mod_mul. lia. }
{ intros i Hi. apply MG. replace (sp - 352 + i) with (sp - 752 + 40 + (360 + i)) by lia. apply D. lia. }
{ exact VEC1. }
{ exact Bv. }
intros fx2 R2 M2 model2 RP HP MB HH2.
assert (ELB : lb_remove b LBc = LB6).
{ pose proof (proj1 (proj2 (hio_wf L SCFG HI HIok LBc cr M _ HH))) as ND.
unfold LBc, LB6, PM.parser_own, PM.src_own, PM.vec_own in *. cbn [app map fst] in *. fold b k in ND |- *.
cbn [lb_remove fst]. inversion ND as [|x0 l0 NI0 ND0].
destruct (Z.eqb (PM.sr_qc (PM.p_src p)) b) eqn:EQ; [apply Z.eqb_eq in EQ; exfalso; apply NI0; rewrite EQ; constructor|].
rewrite Z.eqb_refl. reflexivity. }
rewrite ELB in HP, HH2.
set (Wd := [(sp - 352, 24)] : list L5.range) in *.
assert (WCd : forall a, PMK.inW Wd a -> sp - 352 <= a < sp - 328).
{ intros a (r & Hin & Hr). destruct Hin as [<-|[]]. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
assert (EKd : PMK.ek L LB6 (sp - 752) (PMSP.pm_scr 0) Wd M1 M2) by (apply (PMK.ek_of_hpres L); exact HP).
assert (BR6 : PMUHK.brange L LB6) by (apply (PMUHK.brange_of_heap L HI LY HIok LB6 LB6 cr M2 _ HH2); apply incl_refl).
assert (WSTD : forall a, PMK.inW Wd a -> PMUH.fb sp <= a \/ 65536 <= a < 0xea000) by (intros a I; apply WCd in I; left; unfold PMUH.fb, FRAME; lia).
assert (N0 : forall i, ~ (sp - 352 <= i < sp - 328) -> ~ PMK.inW Wd i) by (intros i N I; apply N; apply WCd; exact I).
apply (KONT fx2 R2 M2 model2). unfold PMUH.H6, PMUH.fb, FRAME.
split. { apply (PMUHK.hcore_call L LY R0 M0 model0 sp ra LB0 R1 M1 model R2 M2 model2 LB6 (PMSP.pm_scr 0) Wd CORE1 RP HP);
[unfold LB6, LBX; apply incl_appr; apply incl_appr; apply incl_appr; apply incl_appr; apply incl_refl| unfold PMSP.pm_scr, SCR, FRAME; lia| |exact MB].
intros a I. left. apply WCd in I. unfold PMUH.fb, FRAME. lia. }
split. { eapply (PMUHK.vstr_keep L LY sp LB6 (PMSP.pm_scr 0) Wd M1 M2 EKd STKd SCd BR6 WSTD); [unfold PMUH.fb, FRAME; lia|unfold PMUH.fb, FRAME; lia| | |exact VS1].
- intros i Hi. apply N0. unfold PMUH.fb, FRAME in Hi. lia.
- unfold LB6, LBX. apply incl_appr. apply incl_appr. apply incl_appr. apply incl_appl. apply incl_refl. }
split; [exact SZ|].
split. { eapply (PMUHK.iss_keep L LY sp LB6 (PMSP.pm_scr 0) Wd M1 M2 EKd STKd SCd BR6 WSTD); [unfold PMUH.fb, FRAME; lia|unfold PMUH.fb, FRAME; lia| | |exact IA1].
- intros i Hi. apply N0. unfold PMUH.fb, FRAME in Hi. lia.
- unfold LB6, LBX. apply incl_appr. apply incl_appr. apply incl_appl. apply incl_refl. }
split. { replace (sp - 752 + 376) with (sp - 752 + 40 + 336) by lia.
eapply (PMUHK.vstr_keep L LY sp LB6 (PMSP.pm_scr 0) Wd M1 M2 EKd STKd SCd BR6 WSTD); [unfold PMUH.fb, FRAME; lia|unfold PMUH.fb, FRAME; lia| | |exact TB1].
- intros i Hi. apply N0. unfold PMUH.fb, FRAME in Hi. lia.
- unfold LB6. apply incl_appr. apply incl_appl. apply incl_refl. }
split. { replace (sp - 752 + 64) with (sp - 752 + 40 + 24) by lia. replace (sp - 752 + 456) with (sp - 752 + 440 + 16) by lia.
eapply (PMUHK.src_keep L LY sp LB6 (PMSP.pm_scr 0) Wd M1 M2 EKd STKd SCd BR6 WSTD); [unfold PMUH.fb, FRAME; lia|unfold PMUH.fb, FRAME; lia| | |exact SRC1].
- intros i Hi. apply N0. unfold PMUH.fb, FRAME in Hi. lia.
- unfold LB6, PM.src_own. cbn. auto. }
split. { replace (sp - 752 + 72) with (sp - 752 + 40 + 32) by lia.
eapply (PMUHK.nullis_keep L LY sp LB6 (PMSP.pm_scr 0) Wd M1 M2 EKd STKd SCd); [unfold PMUH.fb, FRAME; lia|unfold PMUH.fb, FRAME; lia| |exact NI1]. intros i Hi. apply N0. unfold PMUH.fb, FRAME in Hi. lia. }
split. { apply (PMUHK.hstat_keep L LY LB6 (sp - 752) (PMSP.pm_scr 0) Wd M1 M2 EKd); [|exact HST1]. intros a I. apply WCd in I. left. lia. }
split; [exact EMONO|]. split; [exact HH2| exact CK].
Qed.
End Stage.
End PMUH6.
