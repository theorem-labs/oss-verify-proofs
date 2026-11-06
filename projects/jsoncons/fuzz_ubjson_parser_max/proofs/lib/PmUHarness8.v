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
PmLayout PmLayoutU PmModel PmModelFacts PmStatics PmSpecs PmSpecsU PmStep PmKeep PmKitU PmTopU PmUHarnessStmts PmUHarnessKit PmUHarnessP.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmUHarness8 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Core.L5C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsU.PMU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmUHarness8.PMUH8.Stage."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmUHarnessStmts.PMUH."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1list"; "1nil"; "1option"; "2Z"; "0HI"; "0K"; "0L"; "0LB0"; "3Model"; "3event"; "4bvmap"; "0M"; "0M'"; "0M0"; "0M1"]; ["0R"; "0R0"; "0R1"; "5credit"; "6agree_on"; "8defined"; "8u64_at"; "7SCFG"; "9ADDR_U"; ":iosb_at"; ":strm"; ":vstr"; ";cfg"; "<ios_dtor_spec"; "<locale_dtor_spec"; "<opdel_spec"]; ["=H7b"; ">H7"; ">H8"; ">T3"; "?FPState"; "@srealizes"; "Aloaded_segments"; "0SCFG_P"; "Badd"; "Ble"; "Bpow"; "0be"; "0cr"; "0cr0"; "0fx"; "0fx1"]; ["0g"; "0model"; "0model0"; "0model1"; "0n"; "0o"; "0ra"; "0rdb"; "0s"; "0s2"; "0sm"; "0sp"; "0st"; "Cbv"; "0vp"; "0vp'"]; ["0x"]]).
Module PMUH8.
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
Lemma iosb_revptr : ltac2:(TCodec.tc2 tcn__PmUHarness8 "QH'QMyR0%211'3y8%511%311p051'4&Q9zr5%3221&Q8r6+TH%3221&Q:+2+R0%3221%<251&Dr9r8r7+8%>221+T@%746521&F&Q6%24198B&Er:%231<D&I&H&Q3r<%4893216A?Jr;%68;5431CBAp031p091p0=1p0A1p0J1p0Q41pSJQ91pS@Q:1pT0Q;1pSNQ<1pS<Q=1pLQ?1pJQ@1").
Proof. intros M M' o vp vp' rdb st.
intros Ho Ho' AG V D' (H0 & H32 & H36 & H40 & H48 & Z & D & _ & ST).
assert (S : forall a' n', o + 8 <= a' -> a' + n' <= o + 152 -> L5C.agree_on M M' a' n') by (intros a' n' X Y; apply (L5C.agree_on_sub M M' (o + 8) 144 a' n' AG); lia).
split; [exact V|].
split; [apply (PMF.u32_at_agree RSEGS M M'); [apply S; lia|lia|lia|exact H32]|].
split; [apply (PMF.u32_at_agree RSEGS M M'); [apply S; lia|lia|lia|exact H36]|].
split; [apply (L5C.u64_at_agree RSEGS M M'); [apply S; lia|lia|lia|exact H40]|].
split; [apply (L5C.u64_at_agree RSEGS M M'); [apply S; lia|lia|lia|exact H48]|].
split; [apply (PMF.zeros_at_agree M M'); [apply S; lia|exact Z]|].
split; [exact D'|]. split; [exact I| exact ST].
Qed.
Definition H7b (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr : credit) (s : PM.vstr) (be : bool) : Prop :=
PMUH.hcore L R0 M0 model0 sp ra LB0 R M model /\ PMUHK.vstr_at M (PMUH.fb sp + 712) s
/\ L5.u64_at RSEGS M (PMUH.fb sp + 464) (pa_classic_imp AD)
/\ (exists vp st, PM.iosb_at RSEGS AD PMUH.T3 M (PMUH.fb sp + 560) vp (PMUH.fb sp + 456) st)
/\ PMUH.hstat M true true be /\ (PMST.st_err g = true -> be = true)
/\ hi_heap HI (PM.vs_own s ++ LB0) cr M (m_vmmaps model)
/\ PMSP.credit_keep cr0 cr (PMUH.P0 L n) PMSP.cr0
/\ getr R (reg 1) = Z_to_bv 64 214012 /\ getr R (reg 10) = Z_to_bv 64 (sp - 288).
Lemma strbuf_gone : ltac2:(TCodec.tc2 tcn__PmUHarness8 "RF&OvQ7v7v5%43321'Q4&;y5'QMyR0%211%5241'3y8%611%311p061'9&C'K'J'0'1':%211!pT221&Q1vAv>vQBvQKvQFvQDv8vQ=vQ@r9r8r7r6r5r4r3r2%BCQ;Q:A@?>=<;:987654321(2%11H%411&Q0r1r<r;%46:9321?'Q5&Q6&G%11QH&L+`R_8%265CB1A@%74641Gp091pS8Q>1pQ0Q@1pQ6QF1pS0QM1r=+V`lDr:%<6?3C2B1%A4@>1Mp061p0I1p0M1p>QA1pRHQG1pSFQI1pSDQK1pSBQL1pRJQN1pS4R01pJR21pQ2R81pRNR?1p0RA1").
Proof using All.
intros OPD fx R M model cr s s2 sm be K (CORE & VS & SZ & IA & HST & EMONO & HH & CK) K0 KONT.
pose proof (PMUHK.hcore_facts L R0 M0 model0 sp ra LB0 R M model CORE) as (Hsp & Rsp & Rng & A16 & WR & STK).
pose proof STK as (A16f & SLO & SHI & STOP & _).
pose proof CORE as (_ & Hcs & _ & _ & _ & _ & SPT & _ & _ & BASE & _ & (Mh & Ml & Mm)).
pose proof BASE as (IMG & _). change (L5.img_clear M 65536 749856) in IMG.
set (LBc := PM.vs_own s2 ++ PM.vs_own s ++ LB0) in *.
assert (BRc : PMUHK.brange L LBc) by (apply (PMUHK.brange_of_heap L HI LY HIok LBc LBc cr M _ HH); apply incl_refl).
assert (LBhic : forall x, In x LBc -> fst x + snd x <= hl_ceil L) by (intros (B & m) Hx; destruct (BRc B m Hx) as (_ & _ & Q); exact Q).
assert (SCx : 0 <= 65536 - 752) by lia.
assert (INCs : incl (PM.vs_own s) LBc) by (unfold LBc; apply incl_appr; apply incl_appl; apply incl_refl).
unfold PMUH.fb, FRAME in IA.
destruct IA as (I0 & ID & _ & I16 & I24 & I32 & I40 & I48 & I64 & IVS & I104 & I112 & IOS & IEG & IG).
set (P := fun a => (sp - 312 <= a < sp - 312 + 8) \/ (sp - 296 <= a < sp - 296 + 8) \/ (sp - 192 <= a < sp - 192 + 8)).
assert (PF : forall a, P a -> PMUH.fb sp <= a < PMUH.fb sp + 752) by (intros a [X|[X|X]]; unfold PMUH.fb, FRAME; lia).
assert (PF6 : forall a, P a -> PMUH.fb sp <= a < PMUH.fb sp + 736) by (intros a [X|[X|X]]; unfold PMUH.fb, FRAME; lia).
assert (PDEC : forall a, {P a} + {~ P a}) by (intros a; apply PMK.or_dec; [apply PMK.rng_dec| apply PMK.or_dec; apply PMK.rng_dec]).
assert (AFTER : forall R1 M1, mem_grows M M1 -> (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
getr R1 (reg 2) = Z_to_bv 64 (PMUH.fb sp) -> (forall k, In k CSK -> getr R1 (reg k) = getr R (reg k)) -> L5.u64_at RSEGS M1 (sp - 192) 736016 ->
PMUH.hcore L R0 M0 model0 sp ra LB0 R1 M1 model /\ PMUHK.vstr_at M1 (PMUH.fb sp + 712) s /\ L5.u64_at RSEGS M1 (PMUH.fb sp + 464) (pa_classic_imp AD)
/\ PM.iosb_at RSEGS AD PMUH.T3 M1 (PMUH.fb sp + 560) 736016 (PMUH.fb sp + 456) (PM.sm_st sm) /\ PMUH.hstat M1 true true be).
{ intros R1 M1 MG FRZ Rsp1 KS1 C192.
split. { apply (PMUHK.hcore_piece L LY R0 M0 model0 sp ra LB0 R M model R1 M1 P CORE MG FRZ PF6 Rsp1 KS1). }
split. { eapply (PMUHK.vstr_keep_p L sp LBc M M1 P (65536 - 752) FRZ PF STK SCx BRc); [unfold PMUH.fb, FRAME; lia|unfold PMUH.fb, FRAME; lia| |exact INCs|exact VS].
intros i Hi [X|[X|X]]; unfold PMUH.fb, FRAME in Hi; lia. }
split. { unfold PMUH.fb, FRAME. eapply (PMUHK.u64_keep_p M M1 P FRZ); [lia|lia| |replace (sp - 752 + 464) with (sp - 752 + 440 + 24) by lia; exact I24]. intros i Hi [X|[X|X]]; lia. }
split. { unfold PMUH.fb, FRAME. replace (sp - 752 + 456) with (sp - 752 + 440 + 16) by lia. replace (sp - 752 + 560) with (sp - 752 + 440 + 120) by lia.
apply (iosb_revptr M M1 _ (pa_vp_iss_ios AD) 736016 _ _); [lia|lia| | | |exact IOS].
- apply (PMUHK.agp M M1 P FRZ); [lia|lia|]. intros i Hi [X|[X|X]]; lia.
- replace (sp - 752 + 440 + 120) with (sp - 192) by lia. exact C192.
- destruct IOS as (_ & _ & _ & _ & _ & _ & D & _). intros i Hi. apply MG. apply D. exact Hi. }
apply (PMUHK.hstat_piece L LY sp LBc M M1 P FRZ PF true _ _ STK LBhic HST). }
destruct IVS as (SD & _ & IVS). destruct s2 as [n2 | c2 n2 p2].
-
destruct IVS as (Hn2 & SB0).
pose proof (PMF.even_byte n2) as EVB.
cfeed PJ (PMUHP.huJs_conc fx R M (fun j => match j with 2%nat => sp | 35%nat => 2 * n2 | _ => 0 end)) ltac:(first [PMK.sc]).
PMK.pvz_hg ltac:(idtac; destruct PJ as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ0 & MS & KS & A1 & A8 & A10 & A11 & A12 & C296 & C192 & C312)); PMK.pvz_clrT.
assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha N. apply FRZ0; [exact Ha| intro X; apply N; left; exact X| intro X; apply N; right; left; exact X| intro X; apply N; right; right; exact X]. }
unfold PMSP.cfg.
apply (PMK.spiece RSEGS L HI KL HIok LBc cr M model fx fx1 R 0x34394 R1 0x809e8 M1 P K HH Mh Ml ltac:(lia) MS MG FRZ).
{ intros a Pa. apply PF in Pa. unfold PMUH.fb, FRAME in Pa. left. lia. }
{ exact PDEC. }
intros HH1.
destruct (AFTER R1 M1 MG FRZ) as (CORE1 & VS1 & LC1 & IOS1 & HST1); [rewrite (KS 2%nat) by PMK.inl; exact Rsp| |exact C192|].
{ intros k0 Hk0. apply KS. revert k0 Hk0. apply PMUH.CSK_in. vm_compute. reflexivity. }
apply (KONT fx1 R1 M1 model). unfold H7b.
split; [exact CORE1|]. split; [exact VS1|]. split; [exact LC1|]. split; [exists 736016, (PM.sm_st sm); exact IOS1|].
split; [exact HST1|]. split; [exact EMONO|]. split; [exact HH1|]. split; [exact CK|]. split; [exact A1| exact A10].
-
destruct IVS as (SW0 & SW8 & SW16 & Hn2 & Hc & Hc2 & SBP & _).
assert (Bt : In (p2, c2) LBc) by (unfold LBc, PM.vs_own; cbn; auto).
assert (Hc64 : 0 <= c2 + 1 < 2 ^ 64) by lia.
pose proof (PMF.u8_of_u64 RSEGS M _ _ Hc64 SW0) as SB0.
pose proof (PMF.odd_byte c2 Hc2 ltac:(lia)) as ODB.
pose proof (Z.mod_pos_bound (c2 + 1) 256 ltac:(lia)) as HVB.
set (vb := (c2 + 1) mod 256) in *.
destruct (BRc _ _ Bt) as (Pb0 & Pb1 & Pb4).
assert (Hp47 : p2 < 2 ^ 47) by lia.
cfeed PJ (PMUHP.huJl_conc fx R M (fun j => match j with 2%nat => sp | 35%nat => vb | 37%nat => p2 | _ => 0 end)) ltac:(first [PMK.sc]).
PMK.pvz_hg ltac:(idtac; destruct PJ as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ0 & MS & KS & A1 & A8 & A10 & A12 & C296 & C192 & C312)); PMK.pvz_clrT.
assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha N. apply FRZ0; [exact Ha| intro X; apply N; left; exact X| intro X; apply N; right; left; exact X| intro X; apply N; right; right; exact X]. }
unfold PMSP.cfg.
apply (PMK.spiece RSEGS L HI KL HIok LBc cr M model fx fx1 R 0x34394 R1 0x55454 M1 P K HH Mh Ml ltac:(lia) MS MG FRZ).
{ intros a Pa. apply PF in Pa. unfold PMUH.fb, FRAME in Pa. left. lia. }
{ exact PDEC. }
intros HH1.
destruct (AFTER R1 M1 MG FRZ) as (CORE1 & VS1 & LC1 & IOS1 & HST1); [rewrite (KS 2%nat) by PMK.inl; exact Rsp| |exact C192|].
{ intros k0 Hk0. apply KS. revert k0 Hk0. apply PMUH.CSK_in. vm_compute. reflexivity. }
clear AFTER.
pose proof (PMUHK.hcore_facts L R0 M0 model0 sp ra LB0 R1 M1 model CORE1) as (_ & Rsp1 & _ & _ & _ & STK1).
pose proof CORE1 as (_ & Hcs1 & _).
assert (STKd : L5C.stk (hl_sptop L) M1 (sp - 752) PMSP.OPDEL_SCR).
{ apply (PMK.stk_call L M1 (sp - 752) (65536 - 752) (sp - 752) PMSP.OPDEL_SCR STK1); [lia| unfold PMSP.OPDEL_SCR; lia| unfold PMSP.OPDEL_SCR; lia| exact A16f]. }
unfold PMU.opdel_spec, PMSP.opdel_spec, PMSP.opdel_spec_at in OPD.
apply (OPD fx1 R1 M1 model K LBc cr p2 c2 (sp - 752) 213988 HH1).
{ repeat split; assumption. }
{ exact K0. }
{ exact Bt. }
{ rewrite L5K.rl10. exact A10. }
{ rewrite L5K.rl1. exact A1. }
{ split; [lia| reflexivity]. }
{ rewrite L5K.rl2. exact Rsp1. }
{ rewrite L5K.rl4. rewrite (Hcs1 4%nat) by (unfold CSK; cbn; auto). exact Htp. }
{ exact STKd. }
intros fx2 R2 M2 model2 RP HP MB HH2.
set (LB8 := PM.vs_own s ++ LB0) in *.
assert (ELB : lb_remove p2 LBc = LB8).
{ unfold LBc, PM.vs_own at 1. cbn [app lb_remove fst]. rewrite Z.eqb_refl. reflexivity. }
rewrite ELB in HP, HH2.
assert (EKd : PMK.ek L LB8 (sp - 752) PMSP.OPDEL_SCR [] M1 M2) by (apply (PMK.ek_of_hpres L); exact HP).
assert (SCd : 0 <= PMSP.OPDEL_SCR) by (unfold PMSP.OPDEL_SCR; lia).
assert (BR8 : PMUHK.brange L LB8) by (apply (PMUHK.brange_of_heap L HI LY HIok LB8 LB8 cr M2 _ HH2); apply incl_refl).
assert (LBhi8 : forall x, In x LB8 -> fst x + snd x <= hl_ceil L) by (intros (B & m) Hx; destruct (BR8 B m Hx) as (_ & _ & Q); exact Q).
assert (WSTD : forall a, PMK.inW [] a -> PMUH.fb sp <= a \/ 65536 <= a < 958464) by (intros a (r & [] & _)).
assert (N0 : forall a, ~ PMK.inW [] a) by (intros a (r & [] & _)).
assert (CORE2 : PMUH.hcore L R0 M0 model0 sp ra LB0 R2 M2 model2).
{ apply (PMUHK.hcore_call L LY R0 M0 model0 sp ra LB0 R1 M1 model R2 M2 model2 LB8 PMSP.OPDEL_SCR [] CORE1 RP HP);
[unfold LB8; apply incl_appr; apply incl_refl| unfold PMSP.OPDEL_SCR, SCR, FRAME; lia| |exact MB].
intros a I. destruct (N0 a I). }
assert (VS2 : PMUHK.vstr_at M2 (PMUH.fb sp + 712) s).
{ eapply (PMUHK.vstr_keep L LY sp LB8 PMSP.OPDEL_SCR [] M1 M2 EKd STKd SCd BR8 WSTD); [unfold PMUH.fb, FRAME; lia|unfold PMUH.fb, FRAME; lia| | |exact VS1].
- intros i _. apply N0.
- unfold LB8. apply incl_appl. apply incl_refl. }
assert (LC2 : L5.u64_at RSEGS M2 (PMUH.fb sp + 464) (pa_classic_imp AD)).
{ eapply (PMUHK.u64_keep L LY sp LB8 PMSP.OPDEL_SCR [] M1 M2 EKd STKd SCd); [unfold PMUH.fb, FRAME; lia|unfold PMUH.fb, FRAME; lia| |exact LC1]. intros i _. apply N0. }
assert (IOS2 : PM.iosb_at RSEGS AD PMUH.T3 M2 (PMUH.fb sp + 560) 736016 (PMUH.fb sp + 456) (PM.sm_st sm)).
{ apply (PMF.iosb_at_agree RSEGS AD M1 M2); [unfold PMUH.fb, FRAME; lia|unfold PMUH.fb, FRAME; lia| |exact IOS1].
apply (PMUHK.ag_frame L LY sp LB8 PMSP.OPDEL_SCR [] M1 M2 EKd STKd SCd); [unfold PMUH.fb, FRAME; lia|unfold PMUH.fb, FRAME; lia|]. intros i _. apply N0. }
assert (HST2 : PMUH.hstat M2 true true be).
{ apply (PMUHK.hstat_keep L LY LB8 (sp - 752) PMSP.OPDEL_SCR [] M1 M2 EKd); [|exact HST1]. intros a I. destruct (N0 a I). }
pose proof (PMUHK.hcore_facts L R0 M0 model0 sp ra LB0 R2 M2 model2 CORE2) as (_ & Rsp2 & _ & _ & WR2 & STK2).
pose proof CORE2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BASE2 & _ & (Mh2 & Ml2 & Mm2)).
pose proof BASE2 as (IMG2 & _). change (L5.img_clear M2 65536 749856) in IMG2.
cfeed PK (PMUHP.huK_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | _ => 0 end)) ltac:(first [PMK.sc]).
PMK.pvz_hg ltac:(idtac; destruct PK as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & FR3 & FRZ3 & MS3 & KS3 & A1k & A10k & C296k)); PMK.pvz_clrT.
set (PK := fun a => sp - 296 <= a < sp - 296 + 8).
assert (PFK : forall a, PK a -> PMUH.fb sp <= a < PMUH.fb sp + 752) by (intros a X; unfold PK in X; unfold PMUH.fb, FRAME; lia).
apply (PMK.spiece RSEGS L HI KL HIok LB8 cr M2 model2 fx2 fx3 R2 0x343e4 R3 0x809e8 M3 PK K HH2 Mh2 Ml2 ltac:(lia) MS3 MG3 FRZ3).
{ intros a Pa. apply PFK in Pa. unfold PMUH.fb, FRAME in Pa. left. lia. }
{ intros a. apply PMK.rng_dec. }
intros HH3.
apply (KONT fx3 R3 M3 model2). unfold H7b.
split. { apply (PMUHK.hcore_piece L LY R0 M0 model0 sp ra LB0 R2 M2 model2 R3 M3 PK CORE2 MG3 FRZ3); [intros a X; unfold PK in X; unfold PMUH.fb, FRAME; lia| rewrite (KS3 2%nat) by PMK.inl; exact Rsp2|].
intros k0 Hk0. apply KS3. revert k0 Hk0. apply PMUH.CSK_in. vm_compute. reflexivity. }
split. { eapply (PMUHK.vstr_keep_p L sp LB8 M2 M3 PK (65536 - 752) FRZ3 PFK STK2 SCx BR8); [unfold PMUH.fb, FRAME; lia|unfold PMUH.fb, FRAME; lia| | |exact VS2].
- intros i Hi X. unfold PK in X. unfold PMUH.fb, FRAME in Hi. lia.
- unfold LB8. apply incl_appl. apply incl_refl. }
split. { eapply (PMUHK.u64_keep_p M2 M3 PK FRZ3); [unfold PMUH.fb, FRAME; lia|unfold PMUH.fb, FRAME; lia| |exact LC2]. intros i Hi X. unfold PK in X. unfold PMUH.fb, FRAME in Hi. lia. }
split. { exists 736016, (PM.sm_st sm). apply (PMF.iosb_at_agree RSEGS AD M2 M3); [unfold PMUH.fb, FRAME; lia|unfold PMUH.fb, FRAME; lia| |exact IOS2].
apply (PMUHK.agp M2 M3 PK FRZ3); [unfold PMUH.fb, FRAME; lia|unfold PMUH.fb, FRAME; lia|]. intros i Hi X. unfold PK in X. unfold PMUH.fb, FRAME in Hi. lia. }
split. { apply (PMUHK.hstat_piece L LY sp LB8 M2 M3 PK FRZ3 PFK true _ _ STK2 LBhi8 HST2). }
split; [exact EMONO|]. split; [exact HH3|]. split; [exact CK|]. split; [exact A1k| exact A10k].
Qed.
Lemma stage8 : ltac2:(TCodec.tc2 tcn__PmUHarness8 "RL&OvQ7v7v5%43321&N%1254&M%13765'Q4&;y5'QMyR0%211%5241'3y8%611%311p061'9&C'K'J'0'1':%211!pT221&Q1vAv>vQBvQKvQFvQDv8vQ=vQ@r9r8r7r6r5r4r3r2%BCQ?Q>A@?>=<;:987654321(2%11H%411&Q2r1r<r;%4AQGQFIHGFEDCBA:9321?'Q5&Q6&G%11QL&L+VaP@%265CB1A@%74641Gp091pS8Q>1pQ0Q@1pQ6QF1pS0QM1r=+V`lDr:%<6?3C2B1%A4@>1Mp061p0I1p0M1p>QA1pRHQG1pSFQI1pSDQK1pSBQL1pRJQN1pS4R01pJR21pQ2R81pRNR?1p0RA1p0RD1p0RG1").
Proof using All.
intros OPD LDT IDT fx R M model cr s s2 sm be K H7 K0 KONT.
apply (strbuf_gone OPD fx R M model cr s s2 sm be K H7 K0).
clear fx R M model H7. intros fx R M model (CORE & VS & LC & (vp & st & IOS) & HST & EMONO & HH & CK & A1 & A10).
pose proof (PMUHK.hcore_facts L R0 M0 model0 sp ra LB0 R M model CORE) as (Hsp & Rsp & Rng & A16 & WR & STK).
pose proof STK as (A16f & SLO & SHI & STOP & _).
pose proof CORE as (_ & Hcs & _ & _ & _ & _ & SPT & _ & _ & BASE & _ & MOK).
pose proof MOK as (Mh & Ml & Mm).
set (LBc := PM.vs_own s ++ LB0) in *.
assert (STK0 : L5C.stk (hl_sptop L) M (sp - 752) (PMSP.pm_scr 0)).
{ apply (PMK.stk_call L M (sp - 752) (65536 - 752) (sp - 752) (PMSP.pm_scr 0) STK); [lia| unfold PMSP.pm_scr; lia| unfold PMSP.pm_scr; lia| exact A16f]. }
unfold PMU.locale_dtor_spec, PMSP.locale_dtor_spec in LDT.
apply (LDT fx R M model K (sp - 752 + 464) (sp - 752) 214012 Mh Ml K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [split; [lia| reflexivity]|]. split; [exact Rsp|].
split; [rewrite (Hcs 3%nat) by (unfold CSK; cbn; auto); exact Hgp|]. split; [rewrite (Hcs 4%nat) by (unfold CSK; cbn; auto); exact Htp|]. exact STK0. }
{ rewrite L5K.rl10. rewrite A10. f_equal. lia. }
{ lia. }
{ lia. }
{ exact LC. }
intros fx1 R1 RP1.
assert (CORE1 : PMUH.hcore L R0 M0 model0 sp ra LB0 R1 M model).
{ apply (PMUHK.hcore_piece L LY R0 M0 model0 sp ra LB0 R M model R1 M (fun _ => False) CORE); [intros a X; exact X| intros a Ha _; reflexivity| intros a []| |].
- rewrite (PMK.cs_of_preserved R R1 2 RP1 ltac:(PMK.inl)). exact Rsp.
- intros k Hk. apply (PMK.cs_of_preserved R R1 k RP1). unfold CSK in Hk. cbn in Hk. repeat (destruct Hk as [<-|Hk]; [PMK.inl|]). destruct Hk. }
pose proof (PMUHK.hcore_facts L R0 M0 model0 sp ra LB0 R1 M model CORE1) as (_ & Rsp1 & _ & _ & _ & _).
cfeed PL (PMUHP.huL_conc fx1 R1 M (fun j => match j with 2%nat => sp | _ => 0 end)) ltac:(first [PMK.sc]).
PMK.pvz_hg ltac:(idtac; destruct PL as (fx2 & R2 & M2 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG2 & FR2 & FRZ2 & MS2 & KS2 & A1l & A10l & A11l)); PMK.pvz_clrT.
assert (EM : M2 = M) by (apply functional_extensionality; exact FR2). subst M2.
apply (PMK.spiece_ro RSEGS model fx1 fx2 R1 0x343fc R2 0x5c204 M K Mh Ml MS2).
assert (CORE2 : PMUH.hcore L R0 M0 model0 sp ra LB0 R2 M model).
{ apply (PMUHK.hcore_piece L LY R0 M0 model0 sp ra LB0 R1 M model R2 M (fun _ => False) CORE1 MG2); [intros a Ha _; reflexivity| intros a []| rewrite (KS2 2%nat) by PMK.inl; exact Rsp1|].
intros k Hk. apply KS2. revert k Hk. apply PMUH.CSK_in. vm_compute. reflexivity. }
pose proof (PMUHK.hcore_facts L R0 M0 model0 sp ra LB0 R2 M model CORE2) as (_ & Rsp2 & _ & _ & _ & _).
pose proof CORE2 as (_ & Hcs2 & _).
assert (SC1 : 0 <= PMSP.pm_scr 1) by (unfold PMSP.pm_scr; lia).
assert (STKc : L5C.stk (hl_sptop L) M (sp - 752) (PMSP.pm_scr 1)).
{ apply (PMK.stk_call L M (sp - 752) (65536 - 752) (sp - 752) (PMSP.pm_scr 1) STK); [lia| unfold PMSP.pm_scr; lia| unfold PMSP.pm_scr; lia| exact A16f]. }
unfold PMUH.fb, FRAME in IOS.
unfold PMU.ios_dtor_spec, PMSP.ios_dtor_spec in IDT.
apply (IDT fx2 R2 M model K LBc cr (sp - 752 + 560) vp (sp - 752 + 456) st (sp - 752) 214032 HH MOK K0).
{ unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1l|]. split; [split; [lia| reflexivity]|]. split; [exact Rsp2|].
split; [rewrite (Hcs2 3%nat) by (unfold CSK; cbn; auto); exact Hgp|]. split; [rewrite (Hcs2 4%nat) by (unfold CSK; cbn; auto); exact Htp|]. exact STKc. }
{ rewrite L5K.rl10. rewrite A10l. f_equal. lia. }
{ lia. }
{ lia. }
{ replace (sp - 752 + 560) with (sp - 752 + 70 * 8) by lia. rewrite Z.mod_add by lia. apply Z.mod_divide in A16f; [|lia]. destruct A16f as (q & ->). replace (q * 16) with ((q * 2) * 8) by lia. apply Z.mod_mul. lia. }
{ exact IOS. }
{ exact BASE. }
intros fx3 R3 M3 RP3 HP3 HH3.
set (W3 := [(sp - 752 + 560, 152)] : list L5.range) in *.
assert (WC3 : forall a, PMK.inW W3 a -> sp - 752 + 560 <= a < sp - 752 + 712).
{ intros a (r & Hin & Hr). destruct Hin as [<-|[]]. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
assert (EK3 : PMK.ek L LBc (sp - 752) (PMSP.pm_scr 1) W3 M M3) by (apply (PMK.ek_of_hpres L); exact HP3).
assert (BRc : PMUHK.brange L LBc) by (apply (PMUHK.brange_of_heap L HI LY HIok LBc LBc cr M3 _ HH3); apply incl_refl).
assert (WSTD : forall a, PMK.inW W3 a -> PMUH.fb sp <= a \/ 65536 <= a < 958464) by (intros a I; apply WC3 in I; left; unfold PMUH.fb, FRAME; lia).
apply (KONT fx3 R3 M3 model). unfold PMUH.H8, PMUH.hcore8.
split. { apply (PMUHK.hcore_call L LY R0 M0 model0 sp ra LB0 R2 M model R3 M3 model LBc (PMSP.pm_scr 1) W3 CORE2 RP3 HP3);
[unfold LBc; apply incl_appr; apply incl_refl| unfold PMSP.pm_scr, SCR, FRAME; lia| |apply L5C.model_but_vm_refl].
intros a I. left. apply WC3 in I. unfold PMUH.fb, FRAME. lia. }
split. { eapply (PMUHK.vstr_keep L LY sp LBc (PMSP.pm_scr 1) W3 M M3 EK3 STKc SC1 BRc WSTD); [unfold PMUH.fb, FRAME; lia|unfold PMUH.fb, FRAME; lia| | |exact VS].
- intros i Hi I. apply WC3 in I. unfold PMUH.fb, FRAME in Hi. lia.
- unfold LBc. apply incl_appl. apply incl_refl. }
split. { apply (PMUHK.hstat_keep L LY LBc (sp - 752) (PMSP.pm_scr 1) W3 M M3 EK3); [|exact HST]. intros a I. apply WC3 in I. left. lia. }
split; [exact EMONO|]. split; [exact HH3| exact CK].
Qed.
End Stage.
End PMUH8.
