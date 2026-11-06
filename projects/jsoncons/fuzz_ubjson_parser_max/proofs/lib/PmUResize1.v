(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit PmLayout PmLayoutU PmModel PmModelFacts PmStatics PmSpecs PmSpecsU PmStep PmKeep PmKitU PmFrame PmSReset PmSrcUMemmove PmTxtKitU PmUResizeP.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmUResize1 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmUResize1.PMURZ1.WithHeap.Call."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.Arith.PeanoNat.Nat."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0B"; "1app"; "1bool"; "1cons"; "1false"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"; "2not"]; ["2or"; "3Z"; "0HI"; "0K"; "0KS"; "0L"; "0LB"; "4Model"; "4m_vmmaps"; "5bvmap"; "0M"; "0M'"; "0M0"; "0P"; "0R"; "0R0"]; ["0R1"; "6credit"; "6credit_ok"; "6debit"; "6hi_heap"; "6hl_sptop"; "6model_but_vm"; "6regs_preserved"; "8defined"; "8u64_at"; "8u8_at"; "7SCFG"; "9VLong"; "9VShort"; "9pot_text"; "9tb_ok"]; ["9vs_cap"; "9vs_own"; "9vstr"; "9vstr_at"; ":T3"; ":cfg"; ":credit_keep"; ":credit_le"; ":model_ok"; ";kept0"; ";mem_ok"; ";rs_regs"; ";saves"; "<FPState"; "<getr"; "=srealizes"]; [">mem_grows"; "?loaded_segments"; "0S"; "0SCFG_P"; "@eqb"; "AIn"; "Aexistsb"; "Aforallb"; "Badd"; "Ble"; "Blt"; "Bmodulo"; "Bmul"; "Bof_nat"; "Bpow"; "Bsub"]; ["Btestbit"; "0a"; "0b0"; "0c"; "0cr'"; "0cr0"; "0fx"; "0k"; "0l"; "0m"; "0model"; "0model0"; "0n"; "0n0"; "0o"; "0p"]; ["0pc"; "0q"; "0s"; "0s'"; "CZ_to_bv"; "Cbv"; "Cbv_unsigned"; "0tg"; "0tg'"; "0x"; "0y"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMURZ1.
Import PMU.
Local Ltac lia := PMK.alia.
Local Ltac cdisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMU.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKU.klayout_U L LY.
Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LB : list (Z * Z)) (cr0 : credit).
Variables (o n S r tg : Z) (s : PM.vstr).
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (pa_tp AD).
Hypothesis K0 : K [].
Hypothesis STK0 : L5C.stk (hl_sptop L) M0 S 14336.
Hypothesis Ho1 : S <= o.
Hypothesis Ho2 : o + 24 <= hl_sptop L.
Hypothesis Ho3 : o mod 8 = 0.
Hypothesis Hn1 : 0 <= n <= PM.vs_size s + PM.CHUNK.
Hypothesis Hn2 : n < 2 ^ 26 + PM.CHUNK.
Hypothesis BRLB : PMFR.brange L LB.
Hypothesis OPN : PMU.opnew_spec L HI.
Hypothesis OPD : PMU.opdel_spec L HI.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (s' : PM.vstr) (tg' : Z) (cr' : credit),
regs_preserved R0 R' -> PM.vstr_at RSEGS PMSP.T3 M' o s' -> PM.vs_size s' = n -> PM.tb_ok s' tg' ->
(n <= PM.vs_cap s -> PM.vs_own s' = PM.vs_own s /\ tg' = tg) ->
L5C.hpres L LB S (PMSP.pm_scr 1) [(o, 24)] M0 M' ->
PMSP.credit_keep cr0 cr' (PM.pot_text L s tg) (PM.pot_text L s' tg') ->
model_but_vm model0 model' -> hi_heap HI (PM.vs_own s' ++ LB) cr' M' (m_vmmaps model') ->
srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.
Definition saves (M : word -> option byte) : Prop :=
L5.u64_at RSEGS M (S - 8) (bv_unsigned (getr R0 (reg 1))) /\ L5.u64_at RSEGS M (S - 16) (bv_unsigned (getr R0 (reg 8)))
/\ L5.u64_at RSEGS M (S - 24) (bv_unsigned (getr R0 (reg 9))) /\ L5.u64_at RSEGS M (S - 32) (bv_unsigned (getr R0 (reg 18)))
/\ L5.u64_at RSEGS M (S - 40) (bv_unsigned (getr R0 (reg 19))) /\ L5.u64_at RSEGS M (S - 48) (bv_unsigned (getr R0 (reg 20)))
/\ L5.u64_at RSEGS M (S - 56) (bv_unsigned (getr R0 (reg 21))) /\ L5.u64_at RSEGS M (S - 64) (bv_unsigned (getr R0 (reg 22)))
/\ L5.u64_at RSEGS M (S - 72) (bv_unsigned (getr R0 (reg 23))) /\ L5.u64_at RSEGS M (S - 80) (bv_unsigned (getr R0 (reg 24))).
Definition kept0 (R : bvmap 5 word) : Prop := forall x, In x [3; 4; 25; 26; 27]%nat -> getr R (reg x) = getr R0 (reg x).
Definition mem_ok (M : word -> option byte) : Prop :=
PMK.ek L LB S 14336 [(o, 24)] M0 M /\ PMK.dk L LB S 14336 M0 M /\ L5C.stk (hl_sptop L) M S 14336 /\ L5.defined M o 24.
Lemma sub_in : ltac2:(TCodec.tc2 tcn__PmUResize1 "J'6'7%211'>'3&R7&R6&R4r1%211r3%53:21qU@;1%83<15(<%<3;21&R5%13@97r2r5%43C21p041pU@E1p081pUBF1pQ:G1").
Proof. intros KS l. exact (PMSRS.sub_in KS l). Qed.
Lemma regs_back : ltac2:(TCodec.tc2 tcn__PmUResize1 "SG&Iy5'S5yR0%211%5241'>&QNr1&S4&R=u2%211%42<1%7261vR2%72=1%;3=31r2u8%:11%<2D1%?241&S6vO%B214%32G1%B2H1%F3H61r3u9%E11%G2O1%J241%K2:2%<2Q01%K2Q11%O3Q141r4uB%N11%Q02Q81%Q3241%Q42C2%E2Q91%Q42Q:1%Q83Q:41r5uC%Q711%Q92QA1%Q<241%Q=2L2%N2QB1%Q=2QC1%QA3QC41r6uD%Q@11%QB2QJ1%QE241%QF2Q52%Q72QK1%QF2QL1%QJ3QL41r7uE%QI11%QK2R31%QN241%QO2Q>2%Q@2R41%QO2R51%R33R541r8uF%R211%R42R<1%R7241%R82QG2%QI2R=1%R82R>1%R<3R>41r9uG%R;11%R=2RE1%R@241%RA2R02%R22RF1%RA2RG1%RE3RG41r:uH%RD11%RF2RN1%RI241%RJ2R92%R;2RO1%RJ2S01%RN3S041&QIr;%211&Q7r<%22RB1p041p081p0B1p0L1p0Q61p0Q@1p0QJ1p0R41p0R>1p0RH1p0S41pR2SA1").
Proof. intros R1.
intros E2 E8 E9 E18 E19 E20 E21 E22 E23 E24 KP. apply PMK.preserved_by_index. intros x Hx. unfold PMK.cs_all in Hx. cbn in Hx.
destruct Hx as [<-|Hx]; [rewrite E2, Rsp0; reflexivity|].
destruct Hx as [<-|Hx]; [apply KP; cbn; auto|]. destruct Hx as [<-|Hx]; [apply KP; cbn; auto|].
destruct Hx as [<-|Hx]; [rewrite E8; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite E9; apply Z_to_bv_bv_unsigned|].
destruct Hx as [<-|Hx]; [rewrite E18; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite E19; apply Z_to_bv_bv_unsigned|].
destruct Hx as [<-|Hx]; [rewrite E20; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite E21; apply Z_to_bv_bv_unsigned|].
destruct Hx as [<-|Hx]; [rewrite E22; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite E23; apply Z_to_bv_bv_unsigned|].
destruct Hx as [<-|Hx]; [rewrite E24; apply Z_to_bv_bv_unsigned|].
apply KP. destruct Hx as [<-|[<-|[<-|[]]]]; cbn; auto 10.
Qed.
Lemma finish_long : ltac2:(TCodec.tc2 tcn__PmUResize1 "V7'QM&Iy5'S5yR0%211%5241'9y8%611%311p061'G'A&Q1&QHr5%211'>&QNr8&S4&R=u2%211%42G1%7261&R?vR2+R@%3221%:2K1%>3K61r9u8%=11%?2Q21%B241vRN%B2Q31%F3Q331r:uD%E11%G2Q:1%J241r7%J2Q;1%N3Q;31r;uF%M11%O2QB1%Q2241vRL%Q22QC1%Q63QC31&QIr<%211&QL%113&QJr=%211&Q9&R1r>&R8+1%22E1%6454Q11r?+@%62Q41%:4931<'=&R9%129H&R:%12JA%5231+J%621@&R>+2+K%3221%;2E1%=261&R;%12C6z%R;3R@21&Q8rCrAr@%43321+TP0rB%H221%Q2272&Q5vE%211+XPPP0%R@221%O261&Q4vB(4';%12S4S4(:rD%24S7S71EvF%73521rF&HrE%211%>5=5K41&Q6vRK%2217&Q?(Q<%138R;:%321?&Q@vS2%211%QI2R@1'6%11GrHrG%I4SNSN21(8%11L%O3M31&QA%11<%SO3931vS7%T13T6L1%R8231p0?1&QFvRE&Q>%13QAE7%J3@S4A%33QC1Q4%645Q331'QO&Q;vR3%211&QErMrL+ZnYDrKrJ%66S554321vC%<4S7921p0>1p0F1p0Q:1p0Q?1p0QC1p0R31p0R;1p0R?1p0RE1p0RJ1p0S31p0S:1p0S?1p0SG1p0SK1p0SN1p0T21p0T;1p0TD1p0TM1p0U=1pU:UA1pVBUC1p2UD1pV4UE1pUFUG1pQFUI1pQNUO1pU>V61").
Proof. intros fx R M model q A tg' cr'.
intros MOK A2 A8 A20 A22 KP SV (EK & DK & STK & DO) W0 W16 Hn HA HAe DQ Hq0 Hq1 HH MB TBOK OWN CK.
assert (Hn2' : n < 67125248) by (unfold PM.CHUNK in Hn2; lia).
pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80).
pose proof (PMF.u8_of_u64 RSEGS M o (A + 1) ltac:(lia) W0) as B0. pose proof (PMF.odd_byte A HAe ltac:(lia)) as ODB.
assert (H33 : 0 <= (A + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (A + 1) 256 ltac:(lia)); lia).
pose proof (L5C.stk_writable RSEGS _ M S 14336 STK) as WR.
assert (WRo : L5.writable RSEGS M o 24) by (apply (L5C.writable_of_defined RSEGS M o 24 DO); lia).
assert (WRq : L5.writable RSEGS M (q + n) 1) by (apply (L5C.writable_of_defined RSEGS M (q + n) 1); [apply (L5.defined_sub M q A (q + n) 1 DQ); lia|lia|lia]).
assert (Dqo : q + n + 1 <= o \/ o + 24 <= q + n) by (left; lia).
assert (Dqf : q + n + 1 <= S - 80 \/ S - 80 + 80 <= q + n) by (left; lia).
pose proof (bv_unsigned_in_range 64 (getr R (reg 10))) as H10. change (bv_modulus 64) with (2 ^ 64) in H10.
pose proof (bv_unsigned_in_range 64 (getr R0 (reg 1))) as G1. change (bv_modulus 64) with (2 ^ 64) in G1.
pose proof (bv_unsigned_in_range 64 (getr R0 (reg 8))) as G8. change (bv_modulus 64) with (2 ^ 64) in G8.
pose proof (bv_unsigned_in_range 64 (getr R0 (reg 9))) as G9. change (bv_modulus 64) with (2 ^ 64) in G9.
pose proof (bv_unsigned_in_range 64 (getr R0 (reg 18))) as G18. change (bv_modulus 64) with (2 ^ 64) in G18.
pose proof (bv_unsigned_in_range 64 (getr R0 (reg 19))) as G19. change (bv_modulus 64) with (2 ^ 64) in G19.
pose proof (bv_unsigned_in_range 64 (getr R0 (reg 20))) as G20. change (bv_modulus 64) with (2 ^ 64) in G20.
pose proof (bv_unsigned_in_range 64 (getr R0 (reg 21))) as G21. change (bv_modulus 64) with (2 ^ 64) in G21.
pose proof (bv_unsigned_in_range 64 (getr R0 (reg 22))) as G22. change (bv_modulus 64) with (2 ^ 64) in G22.
pose proof (bv_unsigned_in_range 64 (getr R0 (reg 23))) as G23. change (bv_modulus 64) with (2 ^ 64) in G23.
pose proof (bv_unsigned_in_range 64 (getr R0 (reg 24))) as G24. change (bv_modulus 64) with (2 ^ 64) in G24.
pose proof (PMURZP.uapML_conc fx R M (fun j => match j with 2%nat => S | 10%nat => o | 33%nat => (A + 1) mod 256 | 35%nat => q | 38%nat => n
| 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
| 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19)) | 49%nat => bv_unsigned (getr R0 (reg 20))
| 50%nat => bv_unsigned (getr R0 (reg 21)) | 51%nat => bv_unsigned (getr R0 (reg 22)) | 52%nat => bv_unsigned (getr R0 (reg 23))
| 53%nat => bv_unsigned (getr R0 (reg 24)) | 54%nat => bv_unsigned (getr R (reg 10)) | _ => 0 end)) as PP.
cbn beta iota in PP.
assert (A10 : getr R (reg 10) = Z_to_bv 64 (bv_unsigned (getr R (reg 10)))) by (symmetry; apply Z_to_bv_bv_unsigned).
PMK.feed PP ltac:(first [PMK.sc]).
PMK.pvz_hg ltac:(idtac; destruct PP as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
destruct pvzP as (MG & _ & FRZ0 & MS & KS & E1 & E2 & E8 & E9 & _ & E18 & E19 & E20 & E21 & E22 & E23 & E24 & C0 & C8)); PMK.pvz_clrT.
set (P := fun a => (o + 8 <= a < o + 8 + 8) \/ (q + n <= a < q + n + 1)).
assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha N. apply FRZ0; [exact Ha|intro X; apply N; unfold P; lia|intro X; apply N; unfold P; lia]. }
unfold PMSP.cfg.
apply (PMK.spiece RSEGS L HI KL HIok ((q, A) :: LB) cr' M model fx fx1 R 0x57934 R1 0x57988 M1 P K HH Mh Ml ltac:(destruct STOP; lia) MS MG FRZ).
{ intros a Pa. unfold P in Pa. destruct Pa as [X|X];
[apply (PMK.cwr_stack L ((q, A) :: LB) M S 14336 a STK); lia
|apply (PMK.cwr_block L ((q, A) :: LB) q A a ltac:(left; reflexivity)); lia]. }
{ intros a. unfold P. apply PMK.or_dec; apply PMK.rng_dec. }
intros HH1.
assert (RA1 : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite E1, Z_to_bv_bv_unsigned; exact Rra0).
unfold PMK.cfg.
eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx1 R1 M1 0x57988 (ltac:(oW' 0x57988%Z)) r (ltac:(oF' 0x57988%Z)) ltac:(reflexivity) (ltac:(oD' 0x57988%Z)) RA1 Hr1 Hr2)|].
assert (AG : forall a m, 0 <= a -> a + m <= 2 ^ 64 -> (forall i, a <= i < a + m -> ~ P i) -> L5C.agree_on M M1 a m).
{ intros a0 m0 Ha0 Hm0 X i Hi. apply FRZ; [lia| apply X; exact Hi]. }
apply (KONT fx1 R1 M1 model (PM.VLong A n q) tg' cr'); [| | reflexivity | exact TBOK | | | exact CK | exact MB | exact HH1].
- apply regs_back; try assumption.
intros x Hx. rewrite (KS x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
- split; [intros i Hi; apply MG; apply DO; exact Hi|]. split; [exact I|].
split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AG; [lia|lia| intros i Hi X; unfold P in X; destruct X as [X|X]; cdisj; lia]|lia|lia|exact W0]|].
split; [exact C8|].
split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AG; [lia|lia| intros i Hi X; unfold P in X; destruct X as [X|X]; cdisj; lia]|lia|lia|exact W16]|].
split; [lia|]. split; [lia|]. split; [exact HAe|]. split; [intros i Hi; apply MG; apply DQ; exact Hi| exact I].
- intros X. destruct (OWN X) as (O1 & O2). split; [exact O1| exact O2].
- apply (PMK.hpres_of L LB S 14336 _ M0 M1).
+ apply (PMK.ek_trans L LB S 14336 _ M0 M M1 EK).
apply (PMK.ek_piece L LB S 14336 _ M M1 P FRZ). intros a Ha CA NE OW Pa. unfold P in Pa. destruct Pa as [X|X].
* apply (OW (o, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
* exact (PMSRS.own_not_client L HI HIok [(q, A)] LB cr' M _ q A a S 14336 HH ltac:(left; reflexivity) ltac:(lia) CA).
+ destruct (PMK.stk_grows L M M1 S 14336 MG STK) as (_ & _ & _ & _ & D1). exact D1.
+ apply (PMK.dk_trans L LB S 14336 M0 M M1 DK). apply PMK.dk_grows. exact MG.
Qed.
Lemma finish_short : ltac2:(TCodec.tc2 tcn__PmUResize1 "U2'QM&Iy5'S5yR0%211%5241'9y8%611%311p061'G'A&Q1&QHr3%211'>&QNr6&S4&R=u2%211%42G1%7261&R?vR2+R@%3221%:2K1%>3K61r7u8%=11%?2Q21%B241vRN%B2Q31%F3Q331r8uD%E11%G2Q:1%J241&R8+1%22:1%L2Q=1%Q03Q=51r9uF%O11%Q12QD1%Q4241vRL%Q42QE1%Q83QE31&QIr:%211&QL%113&QJr;%211&Q:&R1r<%3421Q0:'=&R9z%2219+WO%42;1%6231'3&R@%12;7(5%R03421%;2Q4K+F%=2M1%?231&Q4vBvFr=r@&Hr?%211%8576541&Q6vRK%2217&Q?(Q=%11Q=vS7%4221&Q@vS2%211%Q32QC1'6';%12S1S1%311(8%113&QA%11:%S23531p0:1&QFvRErA&Q>vE%231BE%332GF%746521'QO&Q;vR3%211&QErGrF+ZnYDrErD%66R454321vC%<4R6921p0>1p0G1p0Q61p0Q<1p0Q@1p0QJ1p0QO1p0R51p0R=1p0RB1p0RF1p0RI1p0RM1p0S61p0SA1p0SJ1p0T:1pU:T>1pU6T@1pUFTB1pQFTD1pQNTJ1pU>U11").
Proof. intros fx R M model b0 cr'.
intros MOK A2 A8 A20 A22 KP SV (EK & DK & STK & DO) B0 HB0 EVB Hn HH MB TBOK OWN CK.
pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80).
pose proof (L5C.stk_writable RSEGS _ M S 14336 STK) as WR.
assert (WRo : L5.writable RSEGS M o 24) by (apply (L5C.writable_of_defined RSEGS M o 24 DO); lia).
pose proof (bv_unsigned_in_range 64 (getr R (reg 10))) as H10. change (bv_modulus 64) with (2 ^ 64) in H10.
pose proof (bv_unsigned_in_range 64 (getr R0 (reg 1))) as G1. change (bv_modulus 64) with (2 ^ 64) in G1.
pose proof (bv_unsigned_in_range 64 (getr R0 (reg 8))) as G8. change (bv_modulus 64) with (2 ^ 64) in G8.
pose proof (bv_unsigned_in_range 64 (getr R0 (reg 9))) as G9. change (bv_modulus 64) with (2 ^ 64) in G9.
pose proof (bv_unsigned_in_range 64 (getr R0 (reg 18))) as G18. change (bv_modulus 64) with (2 ^ 64) in G18.
pose proof (bv_unsigned_in_range 64 (getr R0 (reg 19))) as G19. change (bv_modulus 64) with (2 ^ 64) in G19.
pose proof (bv_unsigned_in_range 64 (getr R0 (reg 20))) as G20. change (bv_modulus 64) with (2 ^ 64) in G20.
pose proof (bv_unsigned_in_range 64 (getr R0 (reg 21))) as G21. change (bv_modulus 64) with (2 ^ 64) in G21.
pose proof (bv_unsigned_in_range 64 (getr R0 (reg 22))) as G22. change (bv_modulus 64) with (2 ^ 64) in G22.
pose proof (bv_unsigned_in_range 64 (getr R0 (reg 23))) as G23. change (bv_modulus 64) with (2 ^ 64) in G23.
pose proof (bv_unsigned_in_range 64 (getr R0 (reg 24))) as G24. change (bv_modulus 64) with (2 ^ 64) in G24.
pose proof (PMURZP.uapMS_conc fx R M (fun j => match j with 2%nat => S | 10%nat => o | 33%nat => b0 | 38%nat => n
| 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
| 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19)) | 49%nat => bv_unsigned (getr R0 (reg 20))
| 50%nat => bv_unsigned (getr R0 (reg 21)) | 51%nat => bv_unsigned (getr R0 (reg 22)) | 52%nat => bv_unsigned (getr R0 (reg 23))
| 53%nat => bv_unsigned (getr R0 (reg 24)) | 54%nat => bv_unsigned (getr R (reg 10)) | _ => 0 end)) as PP.
cbn beta iota in PP.
assert (A10 : getr R (reg 10) = Z_to_bv 64 (bv_unsigned (getr R (reg 10)))) by (symmetry; apply Z_to_bv_bv_unsigned).
PMK.feed PP ltac:(first [PMK.sc]).
PMK.pvz_hg ltac:(idtac; destruct PP as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
destruct pvzP as (MG & _ & FRZ0 & MS & KS & E1 & E2 & E8 & E9 & _ & E18 & E19 & E20 & E21 & E22 & E23 & E24 & CN & CB)); PMK.pvz_clrT.
set (P := fun a => o <= a < o + 24).
assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha N. apply FRZ0; [exact Ha|intro X; apply N; unfold P; lia]. }
unfold PMSP.cfg.
apply (PMK.spiece RSEGS L HI KL HIok LB cr' M model fx fx1 R 0x57934 R1 0x57988 M1 P K HH Mh Ml ltac:(destruct STOP; lia) MS MG FRZ).
{ intros a Pa. unfold P in Pa. apply (PMK.cwr_stack L LB M S 14336 a STK); lia. }
{ intros a. unfold P. apply PMK.rng_dec. }
intros HH1.
assert (RA1 : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite E1, Z_to_bv_bv_unsigned; exact Rra0).
unfold PMK.cfg.
eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx1 R1 M1 0x57988 (ltac:(oW' 0x57988%Z)) r (ltac:(oF' 0x57988%Z)) ltac:(reflexivity) (ltac:(oD' 0x57988%Z)) RA1 Hr1 Hr2)|].
apply (KONT fx1 R1 M1 model (PM.VShort n) tg cr'); [| | reflexivity | exact TBOK | | | exact CK | exact MB | exact HH1].
- apply regs_back; try assumption.
intros x Hx. rewrite (KS x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
- split; [intros i Hi; apply MG; apply DO; exact Hi|]. split; [exact I|]. split; [lia| exact CB].
- intros X. split; [exact (OWN X)| reflexivity].
- apply (PMK.hpres_of L LB S 14336 _ M0 M1).
+ apply (PMK.ek_trans L LB S 14336 _ M0 M M1 EK).
apply (PMK.ek_piece L LB S 14336 _ M M1 P FRZ). intros a Ha CA NE OW Pa. unfold P in Pa.
apply (OW (o, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
+ destruct (PMK.stk_grows L M M1 S 14336 MG STK) as (_ & _ & _ & _ & D1). exact D1.
+ apply (PMK.dk_trans L LB S 14336 M0 M M1 DK). apply PMK.dk_grows. exact MG.
Qed.
Lemma saves_keep : ltac2:(TCodec.tc2 tcn__PmUResize1 "R2'S5yR0%211'9y8%511%311p051'A!p021'=&R9zr1%3221&R:&R>+2+R0%3221%5271%;271&?r3r2%211%411'>r5&S4%12N7%311r6%113%73M31p091p0?1pU4N1&R?vR2+R@%3221%O21M%L2N4%Q2221r4%11F%I11p041pU4Q:1+SoomohPPR@%Q821<+Q?%Q52Q41%Q;2?1%Q=241&QL%11Ip011p041p0;1p0H1pQLQE1pQHQI1pQFQJ1").
Proof. intros M M' P.
intros FRZ X HS (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80).
assert (AG : forall a, S - 80 <= a -> a + 8 <= S -> L5C.agree_on M M' a 8).
{ intros a H1 H2 i Hi. apply FRZ; [lia| apply X; lia]. }
unfold saves. repeat split; (eapply (L5C.u64_at_agree RSEGS M M'); [apply AG; lia|lia|lia|eassumption]).
Qed.
Lemma fit_short : ltac2:(TCodec.tc2 tcn__PmUResize1 "TI'QM&Iy5'S5yR0%211%5241'9y8%611%311p061'G'A&QHr3%211'>'QBvS2(Q=%116%53431vRL&R8r4%221;%:3>41&R9+1%2215+F%4291zr7%7221vS7%D3H14&QNr<&S4&R=u2%211%42Q:1%7261&R?vR2+R@%3221%:2Q>1%Q23Q>61r=u8%=11%?2QE1%B241vRN%B2QF1%Q:3QF31r>u9%E11%G2QM1%J241r:%J2QN1%QB3QN31r?u:%M11%O2R51%Q2241%Q12R5Q8%QI3R521r@uB%Q411%Q62R<1%Q9241%Q82R<L%R03R<21rAuG%Q;11%Q=2RC1%Q@241%Q?2RCQH%R73RC21&QIrB%211&QL%113&QJrC%211&Q:&R1rD&R<+2%221<%6454Q>1&Q4vBvFvRErE&H%11;%7565431&Q6vRK%2216'QO&Q;vR3%211&QErIrH+ZnPLrGrF%66K54321vC%<4M921p0>1p0B1p0K1p0Q31p0Q71p0Q:1p0Q>1p0QF1p0QN1p0R61p0R?1p0RH1p0S71p0S:1p0S>1p0SA1p0SE1p0SK1p0T21pUDT61pULT71pUFT91pQFT;1pQNTA1pU>TH1").
Proof. intros fx R M model n0 m.
intros MOK Es En Hm Hn Hn0 Etg A2 A8 A9 A10 A18 A23 KP SV MO B0 HH MB.
pose proof MO as (EK & DK & STK & DO). pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
pose proof (L5C.stk_writable RSEGS _ M S 14336 STK) as WR.
assert (WRo : L5.writable RSEGS M o 24) by (apply (L5C.writable_of_defined RSEGS M o 24 DO); lia).
cfeed PP (PMURZP.ufitS_conc fx R M (fun j => match j with 2%nat => S | 10%nat => o | 34%nat => n0 | 43%nat => m | _ => 0 end)) ltac:(first [PMK.sc]).
destruct PP as (fx1 & R1 & M1 & MG1 & FRw & _ & MS1 & KS1 & F1 & F10 & _ & F12 & F20 & F22).
assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
unfold PMSP.cfg.
apply (PMK.spiece_ro RSEGS model fx fx1 R 0x5781c R1 0xaa734 M K Mh Ml MS1).
destruct (PMTKU.fill_run fx1 R1 M (o + n0 + 1) m 358708 F10 F12 F1 ltac:(split; [lia| reflexivity]) ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(apply (L5.writable_sub RSEGS M o 24 (o + n0 + 1) m WRo); lia)) as (R3 & M3 & MS3 & MG3 & FR3 & D3 & KS3 & _).
set (P := fun a => o + n0 + 1 <= a < o + n0 + 1 + m).
apply (PMK.spiece RSEGS L HI KL HIok LB cr0 M model fx1 fx1 R1 0xaa734 R3 358708 M3 P K HH Mh Ml ltac:(destruct STOP; lia) MS3 MG3 FR3).
{ intros a Pa. unfold P in Pa. apply (PMK.cwr_stack L LB M S 14336 a STK); lia. }
{ intros a. unfold P. apply PMK.rng_dec. }
intros HH3.
assert (KSR : forall x, In x L5K.CS -> getr R3 (reg x) = getr R1 (reg x)) by exact KS3.
apply (finish_short fx1 R3 M3 model (2 * n0) cr0 MOK).
- rewrite (KSR 2%nat) by PMK.inl. rewrite (KS1 2%nat) by PMK.inl. exact A2.
- rewrite (KSR 8%nat) by PMK.inl. rewrite (KS1 8%nat) by PMK.inl. exact A8.
- rewrite (KSR 20%nat) by PMK.inl. exact F20.
- rewrite (KSR 22%nat) by PMK.inl. rewrite F22. f_equal. lia.
- intros x Hx. rewrite (KSR x) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
- apply (saves_keep M M3 P FR3); [intros a Ha X; unfold P in X; lia| lia| exact SV].
- split; [apply (PMK.ek_trans L LB S 14336 _ M0 M M3 EK); apply (PMK.ek_piece L LB S 14336 _ M M3 P FR3);
intros a Ha CA NE OW Pa; unfold P in Pa; apply (OW (o, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]|].
split; [apply (PMK.dk_trans L LB S 14336 M0 M M3 DK); apply PMK.dk_grows; exact MG3|].
split; [exact (PMK.stk_grows L M M3 S 14336 MG3 STK)|]. intros i Hi. apply MG3. apply DO. exact Hi.
- apply (L5C.u8_at_agree RSEGS M M3); [intros i Hi; apply FR3; [lia| unfold P; lia]|lia|lia|exact B0].
- lia.
- apply PMF.even_byte.
- lia.
- exact HH3.
- exact MB.
- subst tg. unfold PM.tb_ok. cbn. lia.
- intros _. rewrite Es. reflexivity.
- rewrite Es. unfold PMSP.credit_keep, PM.pot_text. cbn [PM.vs_cap]. lia.
Qed.
Lemma fit_long : ltac2:(TCodec.tc2 tcn__PmUResize1 "UN'QM&Iy5'S5yR0%211%5241'9y8%611%311p061'G'A&QHr5%211'>'QBvS2(Q<r4r3%33821%73651vRL&R8%12<5%;3?31&R9+1%221:&R?r8%2214%62:1&QNr<&S4&R=u2%211%42Q81%7261vR2+R@%>221%92Q;1%O3Q;51r=u8%<11%>2QB1%A241vRN%A2QC1%Q73QC31r>u9%D11%F2QJ1%I241%H2QJM%Q>3QJ21r?u:%K11%M2R11%Q0241%O2R1Q7%QE3R121r@uB%Q211%Q42R81%Q7241%Q62R8Q7%QL3R821&QIrA%211&QL%113&QJrB%211&Q9&R1rC%QO2:QK%4432Q41rD+@%R32Q71%84731Gz%R321<'=+J%R6218&R>+2+K%3221%R;2=1%8261&R;rE%2217%RL3S01>&Q8rHrF%332F1+TP0%RF218%RJ245&Q5vE%211+XPPP0%RI221%RM261&Q?vS7%22S:1&Q4vB(4';%12SESE(:rJ%24SHSHF1vF%73521vRErL&HrK%211%?5>6541&Q6vRK%2217'QO&Q;vR3%211&QErQ0rO+ZnPLrNrM%66R454321vC%<4R6921p0>1p0B1p0Q31p0Q71p0Q?1p0QB1p0QG1p0QL1p0R61p0R91p0R>1p0RD1p0RH1p0RK1p0RO1p0S71p0S?1p0SG1p0T01p0T>1p0TC1p0TG1p0TL1p0U51pUDU91pV0U:1pULU;1pU8U<1pUFU>1pQFU@1pQNUF1pU>UM1").
Proof. intros fx R M model c n0 p m.
intros MOK Es En Hm Hn A2 A8 A9 A10 A18 KP SV MO W0 W16 Hn0 Hc Hce DP Hp0 Hp1 TBOK HH MB.
pose proof MO as (EK & DK & STK & DO). pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
pose proof (L5C.stk_writable RSEGS _ M S 14336 STK) as WR.
assert (WRo : L5.writable RSEGS M o 24) by (apply (L5C.writable_of_defined RSEGS M o 24 DO); lia).
assert (Hn2' : n < 67125248) by (unfold PM.CHUNK in Hn2; lia).
cfeed PP (PMURZP.ufitL_conc fx R M (fun j => match j with 2%nat => S | 10%nat => o | 34%nat => n0 | 35%nat => p | 43%nat => m | _ => 0 end)) ltac:(first [PMK.sc]).
destruct PP as (fx1 & R1 & M1 & MG1 & FRw & _ & MS1 & KS1 & F1 & F10 & _ & F12 & F20 & F22).
assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
unfold PMSP.cfg.
apply (PMK.spiece_ro RSEGS model fx fx1 R 0x5781c R1 0xaa734 M K Mh Ml MS1).
destruct (PMTKU.fill_run fx1 R1 M (n0 + p) m 358708 F10 F12 F1 ltac:(split; [lia| reflexivity]) ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(apply (L5C.writable_of_defined RSEGS M (n0 + p) m); [apply (L5.defined_sub M p c (n0 + p) m DP); lia|lia|lia])) as (R3 & M3 & MS3 & MG3 & FR3 & D3 & KS3 & _).
set (P := fun a => n0 + p <= a < n0 + p + m).
apply (PMK.spiece RSEGS L HI KL HIok ((p, c) :: LB) cr0 M model fx1 fx1 R1 0xaa734 R3 358708 M3 P K HH Mh Ml ltac:(destruct STOP; lia) MS3 MG3 FR3).
{ intros a Pa. unfold P in Pa. apply (PMK.cwr_block L ((p, c) :: LB) p c a ltac:(left; reflexivity)); lia. }
{ intros a. unfold P. apply PMK.rng_dec. }
intros HH3.
assert (KSR : forall x, In x L5K.CS -> getr R3 (reg x) = getr R1 (reg x)) by exact KS3.
apply (finish_long fx1 R3 M3 model p c tg cr0 MOK).
- rewrite (KSR 2%nat) by PMK.inl. rewrite (KS1 2%nat) by PMK.inl. exact A2.
- rewrite (KSR 8%nat) by PMK.inl. rewrite (KS1 8%nat) by PMK.inl. exact A8.
- rewrite (KSR 20%nat) by PMK.inl. exact F20.
- rewrite (KSR 22%nat) by PMK.inl. rewrite F22. f_equal. lia.
- intros x Hx. rewrite (KSR x) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
- apply (saves_keep M M3 P FR3); [intros a Ha X; unfold P in X; lia| lia| exact SV].
- split; [apply (PMK.ek_trans L LB S 14336 _ M0 M M3 EK); apply (PMK.ek_piece L LB S 14336 _ M M3 P FR3);
intros a Ha CA NE OW Pa; unfold P in Pa;
exact (PMSRS.own_not_client L HI HIok [(p, c)] LB cr0 M _ p c a S 14336 HH ltac:(left; reflexivity) ltac:(lia) CA)|].
split; [apply (PMK.dk_trans L LB S 14336 M0 M M3 DK); apply PMK.dk_grows; exact MG3|].
split; [exact (PMK.stk_grows L M M3 S 14336 MG3 STK)|]. intros i Hi. apply MG3. apply DO. exact Hi.
- apply (L5C.u64_at_agree RSEGS M M3); [intros i Hi; apply FR3; [lia| unfold P; lia]|lia|lia|exact W0].
- apply (L5C.u64_at_agree RSEGS M M3); [intros i Hi; apply FR3; [lia| unfold P; lia]|lia|lia|exact W16].
- lia.
- lia.
- exact Hce.
- intros i Hi. apply MG3. apply DP. exact Hi.
- exact Hp0.
- exact Hp1.
- exact HH3.
- exact MB.
- rewrite Es in TBOK. unfold PM.tb_ok in *. cbn [PM.vs_cap] in *. exact TBOK.
- intros _. rewrite Es. split; reflexivity.
- rewrite Es. unfold PMSP.credit_keep, PM.pot_text. cbn [PM.vs_cap]. lia.
Qed.
Lemma grow_store : ltac2:(TCodec.tc2 tcn__PmUResize1 "W:'QM&Iy5'S5yR0%211%5241'9y8%611%311p061'G'A&QHr6%211'>vRL&R8r5%2261%53941&R9+1%221:zr8%5221&R:%12<?'=+Q@r7%;221&R>+2+K%3221%@261%9261&R;+8%22@1%K3O1B'@+ZnX@%N3Q2D1+ZnWL%Q03Q4F1&QNr?&S4&R=uG%211%42QF1%7261+F%72QG1%Q;3QG31r<%Q7214u:%;11%=2QO1%@2?1r:%@2R01%QD3R031%Q7281%Q82;1%Q92G1%L2J1r@u2%G11%I2R;1%L241&R?vR2+R@%3221%O2R?1%R33R?61rAu8%Q211%Q42RF1%Q7241vRN%Q72RG1%R;3RG31rBu9%Q:11%Q<2RN1%Q?241r>%Q?2RO1%RC3RO31rCuB%QB11%QD2S61%QG241%QF2S6Q0%RJ3S621rDuD%QI11%QK2S=1%QN241%QM2S=QN%S13S=21rEuE%R011%R22SD1%R5241%S73SC17rFuF%R611%R82SJ1%R;241%R:2SJS<%S>3SJ21&QIrG%211&QL%113&QJrH%211&Q8rI%231GN+TP0%SE21C%SJ2<D&Q5vE%211+XPPP0%R3221%SL261&Q4vB(4';%12T;T;(:%14T=T=DIvF%63421&Q3vRE%23@1NrL&HrK%211%@5?8541&Q6vRK%2217&Q?(Q<rJ%23Q2TI1vS7%TJ21TE%6231&Q@vS2%211%TE21U0&QF%G3Q5FB&Q>%13Q76:%>3EU5G%33Q91;%64K531'QO&R1&Q;vR3%211&QErQ3rQ2rQ1rQ0%56943Q221vC%<4;821p0>1p0F1p0K1p0Q31p0Q71p0QI1p0R11p0R41p0R81p0R<1p0R?1p0RC1p0RK1p0S21p0S:1p0SB1p0SK1p0T41p0T@1p0U>1p0UC1p0UN1p0V11p0V51p0V91p0V@1pV2VD1p2VE1p4VF1pUDVG1pULVH1pUFVJ1pQFVL1pQNW21pU>W91").
Proof. intros fx R M model n0 m B A pc.
intros MOK En Hm Hn0 HnA HA HA8 PC A2 A8 A9 A18 A20 A21 A22 KP SV MO DB HB0 HB1 HH MB TBOK GROW CK.
pose proof MO as (EK & DK & STK & DO). pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
pose proof (L5C.stk_writable RSEGS _ M S 14336 STK) as WR.
assert (WRo : L5.writable RSEGS M o 24) by (apply (L5C.writable_of_defined RSEGS M o 24 DO); lia).
assert (Hn2' : n < 67125248) by (unfold PM.CHUNK in Hn2; lia).
pose proof (bv_unsigned_in_range 64 (getr R (reg 10))) as G10. change (bv_modulus 64) with (2 ^ 64) in G10.
pose proof (bv_unsigned_in_range 64 (getr R (reg 24))) as G24. change (bv_modulus 64) with (2 ^ 64) in G24.
assert (A24 : getr R (reg 24) = Z_to_bv 64 (bv_unsigned (getr R (reg 24)))) by (symmetry; apply Z_to_bv_bv_unsigned).
assert (A10' : getr R (reg 10) = Z_to_bv 64 (bv_unsigned (getr R (reg 10)))) by (symmetry; apply Z_to_bv_bv_unsigned).
assert (STORED : exists fx1 R1 M1, msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 0xaa734) M1 (seg_rom RSEGS))
/\ mem_grows M M1 /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (o <= a < o + 24) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a))
/\ (forall x, In x [2; 3; 4; 8; 9; 18; 20; 21; 22; 25; 26; 27]%nat -> getr R1 (reg x) = getr R (reg x))
/\ getr R1 (reg 1) = Z_to_bv 64 358708 /\ getr R1 (reg 10) = Z_to_bv 64 (n0 + B) /\ getr R1 (reg 12) = Z_to_bv 64 m
/\ L5.u64_at RSEGS M1 (o + 16) B /\ L5.u64_at RSEGS M1 o (2 * (A / 2) + 1)).
{ destruct PC as [->|(-> & A23 & Hn022 & A10)].
- cfeed PP (PMURZP.upF_conc fx R M (fun j => match j with 2%nat => S | 10%nat => o | 34%nat => n0 | 38%nat => n | 40%nat => A | 41%nat => B
| 43%nat => m | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 24)) | _ => 0 end)) ltac:(first [PMK.sc]).
destruct PP as (fx1 & R1 & M1 & MG1 & _ & FR1 & MS1 & KS1 & F1 & F10 & _ & F12 & C16 & _ & C0).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros a Ha X; apply FR1; [exact Ha| lia]|].
split; [intros x Hx; apply KS1; revert x Hx; apply sub_in; vm_compute; reflexivity|].
split; [exact F1|]. split; [exact F10|]. split; [exact F12|]. split; [exact C16| exact C0].
- cfeed PP (PMURZP.upDS_conc fx R M (fun j => match j with 2%nat => S | 10%nat => o | 34%nat => n0 | 38%nat => n | 40%nat => A | 41%nat => B
| 43%nat => m | 56%nat => bv_unsigned (getr R (reg 24)) | _ => 0 end)) ltac:(first [PMK.sc]).
destruct PP as (fx1 & R1 & M1 & MG1 & _ & FR1 & MS1 & KS1 & F1 & F10 & _ & F12 & C16 & _ & C0).
exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|]. split; [intros a Ha X; apply FR1; [exact Ha| lia]|].
split; [intros x Hx; apply KS1; revert x Hx; apply sub_in; vm_compute; reflexivity|].
split; [exact F1|]. split; [exact F10|]. split; [exact F12|]. split; [exact C16| exact C0]. }
destruct STORED as (fx1 & R1 & M1 & MS1 & MG1 & FR1 & KS1 & F1 & F10 & F12 & C16 & C0).
set (P1 := fun a => o <= a < o + 24).
unfold PMSP.cfg.
apply (PMK.spiece RSEGS L HI KL HIok ((B, A) :: LB) (debit L cr0 A) M model fx fx1 R pc R1 0xaa734 M1 P1 K HH Mh Ml ltac:(destruct STOP; lia) MS1 MG1 FR1).
{ intros a Pa. unfold P1 in Pa. apply (PMK.cwr_stack L ((B, A) :: LB) M S 14336 a STK); lia. }
{ intros a. unfold P1. apply PMK.rng_dec. }
intros HH1.
assert (DB1 : L5.defined M1 B A) by (intros i Hi; apply MG1; apply DB; exact Hi).
destruct (PMTKU.fill_run fx1 R1 M1 (n0 + B) m 358708 F10 F12 F1 ltac:(split; [lia| reflexivity]) ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(apply (L5C.writable_of_defined RSEGS M1 (n0 + B) m); [apply (L5.defined_sub M1 B A (n0 + B) m DB1); lia|lia|lia])) as (R3 & M3 & MS3 & MG3 & FR3 & D3 & KS3 & _).
set (P3 := fun a => n0 + B <= a < n0 + B + m).
apply (PMK.spiece RSEGS L HI KL HIok ((B, A) :: LB) (debit L cr0 A) M1 model fx1 fx1 R1 0xaa734 R3 358708 M3 P3 K HH1 Mh Ml ltac:(destruct STOP; lia) MS3 MG3 FR3).
{ intros a Pa. unfold P3 in Pa. apply (PMK.cwr_block L ((B, A) :: LB) B A a ltac:(left; reflexivity)); lia. }
{ intros a. unfold P3. apply PMK.rng_dec. }
intros HH3.
assert (KSR : forall x, In x L5K.CS -> getr R3 (reg x) = getr R1 (reg x)) by exact KS3.
assert (MG13 : mem_grows M M3) by (intros x D; apply MG3; apply MG1; exact D).
assert (FR13 : forall a, 0 <= a < 2 ^ 64 -> ~ (o <= a < o + 24) -> ~ (n0 + B <= a < n0 + B + m) -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha X Y. rewrite FR3 by (exact Ha || exact Y). apply FR1; assumption. }
apply (finish_long fx1 R3 M3 model B A (tg + 1) (debit L cr0 A) MOK).
- rewrite (KSR 2%nat) by PMK.inl. rewrite (KS1 2%nat) by PMK.inl. exact A2.
- rewrite (KSR 8%nat) by PMK.inl. rewrite (KS1 8%nat) by PMK.inl. exact A8.
- rewrite (KSR 20%nat) by PMK.inl. rewrite (KS1 20%nat) by PMK.inl. exact A20.
- rewrite (KSR 22%nat) by PMK.inl. rewrite (KS1 22%nat) by PMK.inl. exact A22.
- intros x Hx. rewrite (KSR x) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
- destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80).
assert (AG : forall a, S - 80 <= a -> a + 8 <= S -> L5C.agree_on M M3 a 8).
{ intros a H1 H2 i Hi. apply FR13; lia. }
unfold saves. repeat split; (eapply (L5C.u64_at_agree RSEGS M M3); [apply AG; lia|lia|lia|eassumption]).
- split; [apply (PMK.ek_trans L LB S 14336 _ M0 M M3 EK)|].
{ apply (PMK.ek_piece L LB S 14336 _ M M3 (fun a => (o <= a < o + 24) \/ (n0 + B <= a < n0 + B + m))).
- intros a Ha X. apply FR13; [exact Ha| intro Y; apply X; left; exact Y| intro Y; apply X; right; exact Y].
- intros a Ha CA NE OW [X|X].
+ apply (OW (o, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
+ exact (PMSRS.own_not_client L HI HIok [(B, A)] LB _ M _ B A a S 14336 HH ltac:(left; reflexivity) ltac:(lia) CA). }
split; [apply (PMK.dk_trans L LB S 14336 M0 M M3 DK); apply PMK.dk_grows; exact MG13|].
split; [exact (PMK.stk_grows L M M3 S 14336 MG13 STK)|]. intros i Hi. apply MG13. apply DO. exact Hi.
- apply (L5C.u64_at_agree RSEGS M1 M3); [intros i Hi; apply FR3; [lia| unfold P3; lia]|lia|lia|].
replace (A + 1) with (2 * (A / 2) + 1) by lia. exact C0.
- apply (L5C.u64_at_agree RSEGS M1 M3); [intros i Hi; apply FR3; [lia| unfold P3; lia]|lia|lia|exact C16].
- lia.
- lia.
- lia.
- intros i Hi. apply MG3. apply DB1. exact Hi.
- exact HB0.
- exact HB1.
- exact HH3.
- exact MB.
- exact TBOK.
- intros X. exfalso. lia.
- exact CK.
Qed.
Lemma gan_short : ltac2:(TCodec.tc2 tcn__PmUResize1 "W8'QM&Iy5'S5yR0%211%5241'9y8%611%311p061'G'A&QHr5%211'>'QBvS2(Q=%116%53431vRL&R8r6%221;%:3>41&R9+1%2215'=zr8%6221+F%8231%6231&R:%12@>+Q@r7%>221&R>+2+K%3221%C261%A261&R;+8%22B1%Q33Q71D&QNr?&S4&R=u2%211%42QI1%7261&R?vR2+R@%3221%:2QM1%QA3QM61r@u8%=11%?2R41%B241vRN%B2R51%QI3R531rAu9%E11%G2R<1%J241r=%J2R=1%R13R=31rBu:%M11%O2RD1%Q2241%R73RC17rCuB%Q311%Q52RJ1%Q8241%Q72RJK%R>3RJ21rDuC%Q:11%Q<2S11%Q?241%R=2MR8%Q?2S21%RF3S231rEuE%QB11%QD2S91%QG241%QF2S9QG%RM3S921rFuF%QI11%QK2S@1%QN241%QM2S@RM%S43S@21rGuG%R011%R22SG1%R5241%R42SGRH%S;3SG21&QIrH%211&QL%113&QJrI%211&Q8rJ%231HO+TP0%S=21C%SB2<D&Q5vE%211+XPPP0%RB221%SD261&Q4vB(4';%12T8T8(:%14T:T:DIvF%63421&Q3vRE%23@1NrM&HrL%211%@5?8541&Q6vRK%2217&Q?(Q<rK%23Q2TA1vS7%TB21T=%6231&Q@%11TJ%T821TG&QF%F3Q4EA&Q>%13Q6TO9%=3DTLF%33Q81:%64J531'QO&R1&Q;vR3%211&QErQ4rQ3+ZnW4rQ2rQ1%66:54321vC%=4<921p0?1p0G1p0K1p0Q31p0Q71p0QI1p0R11p0R41p0R81p0R<1p0R?1p0RC1p0RK1p0S31p0S;1p0SD1p0SL1p0T31p0T<1p0TE1p0U41p0U91p0UC1p0UF1p0UN1p0V21p0V81p0V?1p2VC1p4VD1pUDVE1pULVF1pUFVH1pQFVJ1pQNW01pU>W71").
Proof. intros fx R M model n0 m B A.
intros MOK Es En Hm Hn0 HnA HA HA8 A2 A8 A9 A10 A18 A19 A21 A22 A23 KP SV MO DB HB0 HB1 HH MB TBOK GROW CK.
pose proof MO as (EK & DK & STK & DO). pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
pose proof (L5C.stk_writable RSEGS _ M S 14336 STK) as WR.
cfeed PP (PMURZP.upN_conc fx R M (fun j => match j with 2%nat => S | 34%nat => n0 | 41%nat => B | 42%nat => o + 1 | _ => 0 end)) ltac:(first [PMK.sc]).
destruct PP as (fx1 & R1 & M1 & MG1 & FRw & _ & EX).
assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
assert (MODE : (n0 - 0) mod 2 ^ 64 = n0) by (rewrite Z.sub_0_r; apply Z.mod_small; lia).
unfold PMSP.cfg.
destruct EX as [(MS1 & KS1 & F1 & F11 & F12 & F20 & F)|(MS1 & KS1 & F20 & F)]; rewrite MODE in F.
-
apply (PMK.spiece_ro RSEGS model fx fx1 R 0x578e4 R1 0xaa5b8 M K Mh Ml MS1).
assert (F10 : getr R1 (reg 10) = Z_to_bv 64 B) by (rewrite (KS1 10%nat) by PMK.inl; exact A10).
destruct (PMCPS.memmove_run fx1 R1 M B (o + 1) n0 358652 F10 F11 F12 F1 ltac:(split; [lia| reflexivity]) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(apply (L5C.writable_of_defined RSEGS M B n0); [apply (L5.defined_sub M B A B n0 DB); lia|lia|lia])
ltac:(apply (L5.defined_sub M o 24 (o + 1) n0 DO); lia)) as (R3 & M3 & MS3 & MG3 & FR3 & D3 & KS3 & R3_10).
set (P3 := fun a => B <= a < B + n0).
apply (PMK.spiece RSEGS L HI KL HIok ((B, A) :: LB) (debit L cr0 A) M model fx1 fx1 R1 0xaa5b8 R3 358652 M3 P3 K HH Mh Ml ltac:(destruct STOP; lia) MS3 MG3 FR3).
{ intros a Pa. unfold P3 in Pa. apply (PMK.cwr_block L ((B, A) :: LB) B A a ltac:(left; reflexivity)); lia. }
{ intros a. unfold P3. apply PMK.rng_dec. }
intros HH3.
assert (KSR : forall x, In x L5K.CS -> getr R3 (reg x) = getr R1 (reg x)) by exact KS3.
apply (grow_store fx1 R3 M3 model n0 m B A 0x578fc MOK En Hm ltac:(lia) HnA HA HA8).
+ right. split; [reflexivity|]. split; [rewrite (KSR 23%nat) by PMK.inl; rewrite (KS1 23%nat) by PMK.inl; exact A23|]. split; [lia| exact R3_10].
+ rewrite (KSR 2%nat) by PMK.inl. rewrite (KS1 2%nat) by PMK.inl. exact A2.
+ rewrite (KSR 8%nat) by PMK.inl. rewrite (KS1 8%nat) by PMK.inl. exact A8.
+ rewrite (KSR 9%nat) by PMK.inl. rewrite (KS1 9%nat) by PMK.inl. exact A9.
+ rewrite (KSR 18%nat) by PMK.inl. rewrite (KS1 18%nat) by PMK.inl. exact A18.
+ rewrite (KSR 20%nat) by PMK.inl. exact F20.
+ rewrite (KSR 21%nat) by PMK.inl. rewrite (KS1 21%nat) by PMK.inl. exact A21.
+ rewrite (KSR 22%nat) by PMK.inl. rewrite (KS1 22%nat) by PMK.inl. exact A22.
+ intros x Hx. rewrite (KSR x) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
+ apply (saves_keep M M3 P3 FR3); [intros a Ha X; unfold P3 in X; lia| lia| exact SV].
+ split; [apply (PMK.ek_trans L LB S 14336 _ M0 M M3 EK); apply (PMK.ek_piece L LB S 14336 _ M M3 P3 FR3);
intros a Ha CA NE OW Pa; unfold P3 in Pa;
exact (PMSRS.own_not_client L HI HIok [(B, A)] LB _ M _ B A a S 14336 HH ltac:(left; reflexivity) ltac:(lia) CA)|].
split; [apply (PMK.dk_trans L LB S 14336 M0 M M3 DK); apply PMK.dk_grows; exact MG3|].
split; [exact (PMK.stk_grows L M M3 S 14336 MG3 STK)|]. intros i Hi. apply MG3. apply DO. exact Hi.
+ intros i Hi. apply MG3. apply DB. exact Hi.
+ exact HB0.
+ exact HB1.
+ exact HH3.
+ exact MB.
+ exact TBOK.
+ exact GROW.
+ exact CK.
-
apply (PMK.spiece_ro RSEGS model fx fx1 R 0x578e4 R1 0x578fc M K Mh Ml MS1).
assert (En0 : n0 = 0) by lia.
apply (grow_store fx1 R1 M model n0 m B A 0x578fc MOK En Hm ltac:(lia) HnA HA HA8).
+ right. split; [reflexivity|]. split; [rewrite (KS1 23%nat) by PMK.inl; exact A23|]. split; [lia| rewrite (KS1 10%nat) by PMK.inl; rewrite A10; f_equal; lia].
+ rewrite (KS1 2%nat) by PMK.inl. exact A2.
+ rewrite (KS1 8%nat) by PMK.inl. exact A8.
+ rewrite (KS1 9%nat) by PMK.inl. exact A9.
+ rewrite (KS1 18%nat) by PMK.inl. exact A18.
+ exact F20.
+ rewrite (KS1 21%nat) by PMK.inl. exact A21.
+ rewrite (KS1 22%nat) by PMK.inl. exact A22.
+ intros x Hx. rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
+ exact SV.
+ exact MO.
+ exact DB.
+ exact HB0.
+ exact HB1.
+ exact HH.
+ exact MB.
+ exact TBOK.
+ exact GROW.
+ exact CK.
Qed.
Lemma gan_long_del : ltac2:(TCodec.tc2 tcn__PmUResize1 "WG'QM&Iy5'S5yR0%211%5241'9y8%611%311p061'G'A&QHr7%211'>vRL&R8r6r4%3221%63:51&R9+1r5%3221zr8%6221&R:%12>6'=+Q@%;21?&R>+2+K%3221%@2D1%8261&R;+8%22M1%L3Q01A+Jr=%H221%I22:%A221&QNrA&S4&R=u2%211%42QG1%7261&R?vR2+R@%3221%:2QK1%Q?3QK61rBu8%=11%?2R21%B241vRN%B2R31%QG3R331rCu9%E11%G2R:1%J241%I2R:O%QN3R:21rDuB%L11%N2RA1%Q1241r@%Q12RB1%R63RB31rEuC%Q411%Q62RI1%Q9241%R<3RH17rFuD%Q:11%Q<2RO1%Q?241r?%Q?2S01%RD3S031rGuE%QB11%QD2S71%QG241%RJ3S617rHuF%QH11%QJ2S=1%QM241%QL2S=RO%S13S=21rIuG%QO11%R12SD1%R4241%QM2JRO%R42SE1%S93SE31&QIrJ%211&QL%113&QJrK%211&Q8rL%231Q7Q=+TP0%S?21Q1%SE2LQ2&Q5vE%211+XPPP0%RB221%SF261%SG29>rN%SN2=1%SJ215&?rM%T43T8D1%311&Q4vB(4';%12T>T>(:%14T@T@ILrQ0%34TBTB?1vF%83621%93751&Q3vRE%23K1Q4rQ2&HrQ1%211%C5B8541&Q6vRK%2217&Q?(Q<%13LTNQ0vS7%TO21TI%5231&Q@vS2%211%TH21U5&QFrO%G3Q@F1&Q>%13QB7;%>34U;O%33QD1<%74K531'QO&R1&Q;vR3%211&QErQ9rQ8+ZnWLrQ7rQ6%66:54321vC%=4<921p0?1p0H1p0M1p0Q41p0Q81p0QM1p0R21p0R61p0R81p0R@1p0RC1p0RG1p0RK1p0RN1p0S21p0S;1p0SC1p0SJ1p0T31p0T:1p0TC1p0TK1p0U41p0UC1p0UI1p0UN1p0V81p0V;1p0V?1p0VD1p0VL1p2W01p4W11pUDW21pV0W31pULW41pU8W51pUFW71pQFW91pQNW?1pU>WF1").
Proof. intros fx R M model c n0 p m B A.
intros MOK En Hm Hn0 HnA HA HA8 Hc A2 A8 A9 A18 A19 A20 A21 A22 A23 KP SV MO DB HB0 HB1 Hp0 Hp1 NBp HH MB TBOK GROW CK.
pose proof MO as (EK & DK & STK & DO). pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
pose proof (L5C.stk_writable RSEGS _ M S 14336 STK) as WR.
cfeed PP (PMURZP.upDL_conc fx R M (fun j => match j with 2%nat => S | 37%nat => c - 1 | 42%nat => p | _ => 0 end)) ltac:(first [PMK.sc]).
destruct PP as (fx1 & R1 & M1 & MG1 & FRw & _ & MS1 & KS1 & F1 & F10 & _).
assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
unfold PMSP.cfg.
apply (PMK.spiece_ro RSEGS model fx fx1 R 0x578fc R1 0x55454 M K Mh Ml MS1).
set (LBc := (B, A) :: (p, c) :: LB).
assert (Ip : In (p, c) LBc) by (right; left; reflexivity).
assert (ELB : lb_remove p LBc = (B, A) :: LB).
{ unfold LBc. cbn [lb_remove fst]. destruct (Z.eqb_spec B p) as [X|_]; [exfalso; exact (NBp X)|]. rewrite Z.eqb_refl. reflexivity. }
assert (STKd : L5C.stk (hl_sptop L) M (S - 80) PMSP.OPDEL_SCR).
{ apply (PMK.stk_call L M S 14336 (S - 80) PMSP.OPDEL_SCR STK); [lia| unfold PMSP.OPDEL_SCR; lia| unfold PMSP.OPDEL_SCR; lia|].
replace (S - 80) with (S + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
unfold PMU.opdel_spec, PMSP.opdel_spec, PMSP.opdel_spec_at in OPD. cbn [pa_opdel AD] in OPD.
apply (OPD fx1 R1 M model K LBc (debit L cr0 A) p c (S - 80) 358672 HH MOK K0 Ip).
{ rewrite L5K.rl10. exact F10. }
{ rewrite L5K.rl1. exact F1. }
{ split; [lia| reflexivity]. }
{ rewrite L5K.rl2. rewrite (KS1 2%nat) by PMK.inl. exact A2. }
{ rewrite L5K.rl4. rewrite (KS1 4%nat) by PMK.inl. rewrite (KP 4%nat) by (cbn; auto). exact Rtp0. }
{ exact STKd. }
intros fx4 R4 M4 model4 RP4 HP4 MB4 HH4. rewrite ELB in HP4, HH4.
assert (C4 : forall x, In x [2; 8; 9; 18; 20; 21; 22]%nat -> getr R4 (reg x) = getr R (reg x)).
{ intros x Hx. rewrite (PMK.cs_of_preserved R1 R4 x RP4) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
apply KS1. revert x Hx. apply sub_in. vm_compute. reflexivity. }
assert (BRc : PMFR.brange L ((B, A) :: LB)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M4 _ HH4); apply incl_refl).
assert (EKd : PMK.ek L ((B, A) :: LB) (S - 80) PMSP.OPDEL_SCR [] M M4) by (apply (PMK.ek_of_hpres L); exact HP4).
assert (SC0 : 0 <= PMSP.OPDEL_SCR) by (unfold PMSP.OPDEL_SCR; lia).
assert (WHI : forall a, PMK.inW [] a -> S - 80 <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; destruct (PMFR.inW_nil a I)).
assert (MOK4 : PMSP.model_ok model4) by (apply (PMFR.model_ok_but_vm model model4 MOK MB4)).
apply (grow_store fx4 R4 M4 model4 n0 m B A 0x57910 MOK4 En Hm Hn0 HnA HA HA8 (or_introl eq_refl)).
- rewrite (C4 2%nat) by PMK.inl. exact A2.
- rewrite (C4 8%nat) by PMK.inl. exact A8.
- rewrite (C4 9%nat) by PMK.inl. exact A9.
- rewrite (C4 18%nat) by PMK.inl. exact A18.
- rewrite (C4 20%nat) by PMK.inl. exact A20.
- rewrite (C4 21%nat) by PMK.inl. exact A21.
- rewrite (C4 22%nat) by PMK.inl. exact A22.
- intros x Hx. rewrite (PMK.cs_of_preserved R1 R4 x RP4) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
- destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80).
unfold saves. repeat split; (apply (PMFR.u64_keep RSEGS L KL ((B, A) :: LB) (S - 80) PMSP.OPDEL_SCR [] M M4 EKd STKd SC0);
[lia|lia| intros i Hi I; destruct (PMFR.inW_nil i I)| eassumption]).
- split; [apply (PMK.ek_trans L LB S 14336 _ M0 M M4 EK)|].
{ apply (PMK.ek_callee_in' RSEGS L KL LB ((B, A) :: LB) S 14336 (S - 80) PMSP.OPDEL_SCR [(o, 24)] [] M M4 HP4); [intros x Hx; right; exact Hx
| unfold PMSP.OPDEL_SCR; lia| lia| lia| destruct STOP; lia| intros b Hb; apply (PMFR.brange_hi L _ BRc b); right; exact Hb| intros a I; destruct (PMFR.inW_nil a I)]. }
split; [apply (PMK.dk_trans L LB S 14336 M0 M M4 DK);
apply (PMK.dk_callee L LB ((B, A) :: LB) S 14336 (S - 80) PMSP.OPDEL_SCR [] M M4 HP4); [intros x Hx; right; exact Hx| unfold PMSP.OPDEL_SCR; lia| lia]|].
split; [apply (PMK.stk_after RSEGS L KL ((B, A) :: LB) M M4 S 14336 (S - 80) PMSP.OPDEL_SCR [] STK HP4); unfold PMSP.OPDEL_SCR; lia|].
apply (PMFR.defined_keep RSEGS L KL ((B, A) :: LB) (S - 80) PMSP.OPDEL_SCR [] M M4 EKd STKd SC0); [lia|lia| intros i Hi I; destruct (PMFR.inW_nil i I)| exact DO].
- apply (L5C.defined_agree M M4 B A); [apply (PMFR.ag_block RSEGS L KL ((B, A) :: LB) (S - 80) PMSP.OPDEL_SCR [] M M4 EKd STKd SC0 BRc WHI); left; reflexivity| exact DB].
- exact HB0.
- exact HB1.
- exact HH4.
- exact (L5C.model_but_vm_trans _ _ _ MB MB4).
- exact TBOK.
- exact GROW.
- exact CK.
Qed.
Lemma gan_long : ltac2:(TCodec.tc2 tcn__PmUResize1 "WO'QM&Iy5'S5yR0%211%5241'9y8%611%311p061'G'A&QHr7%211'>vRL&R8r6r4%3221%63:51&R9+1r5%3221'=zr8%7221&R:r9%2241%7241%42B:+Q@%>21B&R>+2+K%3221%C2G1%@261&R;+8%22Q01%O3Q31C+Jr=%K221%L22:%I221&QNrA&S4&R=u2%211%42QJ1%7261&R?vR2+R@%3221%:2QN1%QB3QN61rBu8%=11%?2R51%B241vRN%B2R61%QJ3R631rCu9%E11%G2R=1%J241%I2R=O%R13R=21rDu:%L11%N2RD1%Q1241%R73RC17rEuB%Q211%Q42RJ1%Q7241%Q62RJQ7%R>3RJ21rFuC%Q911%Q;2S11%Q>241%RD3S017rGuE%Q?11%QA2S71%QD241r?%QD2S81%RL3S831rHuF%QG11%QI2S?1%QL241%QK2S?S1%S33S?21rIuG%QN11%R02SF1%R3241%QL2JS1%R32SG1%S;3SG31&QIrJ%211&QL%113&QJrK%211&Q8rL%231Q7Q>+TP0%SA21Q3%SG2LQ4&Q5vE%211+XPPP0%RA221%SH261rOrM%>32@1%SL2<>%T2234%SN217'@%T52BErN%T2221rQ0%T9231%T521G%7241&Q4vB(4';%12TFTF(:%14THTHCOrQ1%34TJTJF1vF%83621%93751&Q3vRE%23Q11Q7rQ3&HrQ2%211%C5B8541&Q6vRK%2217&Q?(Q<%13OU6Q7vS7%U721U1%5231&Q@vS2%211%TO21U=&QF%F3QEEQ6&Q>%13QG6:%=3Q9UBN%33QI1;%64J531'QO&R1&Q;vR3%211&QErQ:rQ9+ZnW4rQ8rQ7%66:54321vC%=4<921p0?1p0G1p0L1p0Q31p0Q71p0QL1p0R51p0R81p0R:1p0R>1p0RF1p0RI1p0RM1p0S11p0S41p0S81p0SA1p0SI1p0T21p0T91p0TA1p0TH1p0U01p0U91p0UH1p0UN1p0V31p0V<1p0V>1p0VG1p0VL1p0W41p2W81p4W91pUDW:1pV0W;1pULW<1pU8W=1pUFW?1pQFWA1pQNWG1pU>WN1").
Proof. intros fx R M model c n0 p m B A.
intros MOK En Hm Hn0 HnA HA HA8 Hc A2 A8 A9 A10 A18 A19 A21 A22 A23 KP SV MO DB HB0 HB1 DP Hp0 Hp1 ABp HH MB TBOK GROW CK.
pose proof MO as (EK & DK & STK & DO). pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
assert (NBp : B <> p) by lia.
pose proof (L5C.stk_writable RSEGS _ M S 14336 STK) as WR.
cfeed PP (PMURZP.upN_conc fx R M (fun j => match j with 2%nat => S | 34%nat => n0 | 41%nat => B | 42%nat => p | _ => 0 end)) ltac:(first [PMK.sc]).
destruct PP as (fx1 & R1 & M1 & MG1 & FRw & _ & EX).
assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
assert (MODE : (n0 - 0) mod 2 ^ 64 = n0) by (rewrite Z.sub_0_r; apply Z.mod_small; lia).
unfold PMSP.cfg.
destruct EX as [(MS1 & KS1 & F1 & F11 & F12 & F20 & F)|(MS1 & KS1 & F20 & F)]; rewrite MODE in F.
- apply (PMK.spiece_ro RSEGS model fx fx1 R 0x578e4 R1 0xaa5b8 M K Mh Ml MS1).
assert (F10 : getr R1 (reg 10) = Z_to_bv 64 B) by (rewrite (KS1 10%nat) by PMK.inl; exact A10).
destruct (PMCPS.memmove_run fx1 R1 M B p n0 358652 F10 F11 F12 F1 ltac:(split; [lia| reflexivity]) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(apply (L5C.writable_of_defined RSEGS M B n0); [apply (L5.defined_sub M B A B n0 DB); lia|lia|lia])
ltac:(apply (L5.defined_sub M p c p n0 DP); lia)) as (R3 & M3 & MS3 & MG3 & FR3 & D3 & KS3 & R3_10).
set (P3 := fun a => B <= a < B + n0).
apply (PMK.spiece RSEGS L HI KL HIok ((B, A) :: (p, c) :: LB) (debit L cr0 A) M model fx1 fx1 R1 0xaa5b8 R3 358652 M3 P3 K HH Mh Ml ltac:(destruct STOP; lia) MS3 MG3 FR3).
{ intros a Pa. unfold P3 in Pa. apply (PMK.cwr_block L ((B, A) :: (p, c) :: LB) B A a ltac:(left; reflexivity)); lia. }
{ intros a. unfold P3. apply PMK.rng_dec. }
intros HH3.
assert (KSR : forall x, In x L5K.CS -> getr R3 (reg x) = getr R1 (reg x)) by exact KS3.
apply (gan_long_del fx1 R3 M3 model c n0 p m B A MOK En Hm ltac:(lia) HnA HA HA8 Hc).
+ rewrite (KSR 2%nat) by PMK.inl. rewrite (KS1 2%nat) by PMK.inl. exact A2.
+ rewrite (KSR 8%nat) by PMK.inl. rewrite (KS1 8%nat) by PMK.inl. exact A8.
+ rewrite (KSR 9%nat) by PMK.inl. rewrite (KS1 9%nat) by PMK.inl. exact A9.
+ rewrite (KSR 18%nat) by PMK.inl. rewrite (KS1 18%nat) by PMK.inl. exact A18.
+ rewrite (KSR 19%nat) by PMK.inl. rewrite (KS1 19%nat) by PMK.inl. exact A19.
+ rewrite (KSR 20%nat) by PMK.inl. exact F20.
+ rewrite (KSR 21%nat) by PMK.inl. rewrite (KS1 21%nat) by PMK.inl. exact A21.
+ rewrite (KSR 22%nat) by PMK.inl. rewrite (KS1 22%nat) by PMK.inl. exact A22.
+ rewrite (KSR 23%nat) by PMK.inl. rewrite (KS1 23%nat) by PMK.inl. exact A23.
+ intros x Hx. rewrite (KSR x) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
+ apply (saves_keep M M3 P3 FR3); [intros a Ha X; unfold P3 in X; lia| lia| exact SV].
+ split; [apply (PMK.ek_trans L LB S 14336 _ M0 M M3 EK); apply (PMK.ek_piece L LB S 14336 _ M M3 P3 FR3);
intros a Ha CA NE OW Pa; unfold P3 in Pa;
exact (PMSRS.own_not_client L HI HIok [(B, A); (p, c)] LB _ M _ B A a S 14336 HH ltac:(left; reflexivity) ltac:(lia) CA)|].
split; [apply (PMK.dk_trans L LB S 14336 M0 M M3 DK); apply PMK.dk_grows; exact MG3|].
split; [exact (PMK.stk_grows L M M3 S 14336 MG3 STK)|]. intros i Hi. apply MG3. apply DO. exact Hi.
+ intros i Hi. apply MG3. apply DB. exact Hi.
+ exact HB0.
+ exact HB1.
+ exact Hp0.
+ exact Hp1.
+ exact NBp.
+ exact HH3.
+ exact MB.
+ exact TBOK.
+ exact GROW.
+ exact CK.
- apply (PMK.spiece_ro RSEGS model fx fx1 R 0x578e4 R1 0x578fc M K Mh Ml MS1).
apply (gan_long_del fx1 R1 M model c n0 p m B A MOK En Hm ltac:(lia) HnA HA HA8 Hc).
+ rewrite (KS1 2%nat) by PMK.inl. exact A2.
+ rewrite (KS1 8%nat) by PMK.inl. exact A8.
+ rewrite (KS1 9%nat) by PMK.inl. exact A9.
+ rewrite (KS1 18%nat) by PMK.inl. exact A18.
+ rewrite (KS1 19%nat) by PMK.inl. exact A19.
+ exact F20.
+ rewrite (KS1 21%nat) by PMK.inl. exact A21.
+ rewrite (KS1 22%nat) by PMK.inl. exact A22.
+ rewrite (KS1 23%nat) by PMK.inl. exact A23.
+ intros x Hx. rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
+ exact SV.
+ exact MO.
+ exact DB.
+ exact HB0.
+ exact HB1.
+ exact Hp0.
+ exact Hp1.
+ exact NBp.
+ exact HH.
+ exact MB.
+ exact TBOK.
+ exact GROW.
+ exact CK.
Qed.
Lemma grow_credit : ltac2:(TCodec.tc2 tcn__PmUResize1 "QI'QB'A&Q?vS2vS7%3221&R9&Q@%115&R>+2+K%3221%7251&R<%1257r4%:11%<231'>r5%>11&R?+1%2281%63H41%D26>&QG&Q>vE%231KJvRE%5221'=&Q2r7%23751&QF&Q3%13:84r8&R8%12Q6C%?3>31%74=5>1+F%Q82Q:1%>231%?2<1p0A1p0H1p0J1p0Q21p0Q81p0QA1p2QF1pV8QH1").
Proof. intros s' A.
intros (T0 & T1 & _) Hc Hc' Ec HA (CR1 & CR2).
pose proof (ly_kpm L LY) as HK. pose proof (ly_bov L LY) as HB.
assert (Htg : tg <= 22).
{ destruct (Z.eq_dec tg 23) as [E|N]; [|lia]. rewrite E in T1. change (2 ^ 23) with 8388608 in T1. lia. }
pose proof (PMF.pot_text_step L s s' tg Hc') as (P1 & P2).
unfold PM.credit_add, PM.cost1, PM.pot_text in P1, P2, CR1, CR2 |- *. cbn [fst snd] in P1, P2, CR1, CR2 |- *. rewrite ?Ec in P1, P2 |- *.
split; [unfold credit_ok; split; nia|]. split; [|exact Htg].
unfold PMSP.credit_keep, debit. cbn [fst snd]. split; nia.
Qed.
Lemma grow_short : ltac2:(TCodec.tc2 tcn__PmUResize1 "TM'QM&Iy5'S5yR0%211%5241'9y8%611%311p061'G'A&QHr3%211'>'QBvS2(Q=%116%53431vRL&R8r4%221;%:3>41&R9+1%2215&R:+F%221:'=zr7%9221%:226%5221&Q?vS7%22G1&QG&Q>vE%231K5vRE%5221&QNr=&S4&R=u2%211%42QE1%7261&R?vR2+R@%3221%:2QI1%Q=3QI61r>u8%=11%?2R01%B241vRN%B2R11%QE3R131r?u9%E11%G2R81%J241r;%J2R91%QM3R931r@u:%M11%O2R@1%Q2241%Q12R@QA%R43R@21rAuB%Q411%Q62RG1%Q9241%Q82RGL%R;3RG21rBuG%Q;11%Q=2RN1%Q@241%Q?2RNR2%RB3RN21&QIrC%211&QL%113&QJrD%211&Q4vBvFrE&H%117%6554R331&Q6vRK%2216'QO&R1&Q;vR3%211&QErIrH+ZnR4rGrF%66:54321vC%=4<921p0?1p0C1p0K1p0O1p0Q21p0Q61p0Q>1p0QF1p0QN1p0R71p0R@1p0RO1p0S61p0S:1p0SA1p0SE1p0SI1p0SO1p0T61pUDT:1pULT;1pUFT=1pQFT?1pQNTE1pU>TL1").
Proof. intros fx R M model n0 m.
intros MOK Es En Hm Hn Hn0 TBOK CR A2 A8 A9 A10 A18 A23 KP SV MO HH MB.
pose proof MO as (EK & DK & STK & DO). pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
pose proof (L5C.stk_writable RSEGS _ M S 14336 STK) as WR.
assert (WRo : L5.writable RSEGS M o 24) by (apply (L5C.writable_of_defined RSEGS M o 24 DO); lia).
assert (Hn2' : n < 67125248) by (unfold PM.CHUNK in Hn2; lia).
assert (Hn1' : n <= 22 + 16384) by (rewrite Es in Hn1; cbn [PM.vs_size] in Hn1; unfold PM.CHUNK in Hn1; lia).
set (A := Z.lor (Z.max 44 n) 7 + 1).
destruct (PMF.tb_law_first n A ltac:(lia) Hn1' eq_refl) as (LAW & LA1 & LA2 & LA3 & LA4).
assert (EA : A = 8 * (Z.max 44 n / 8) + 8) by (unfold A; apply PMF.lor7; lia).
assert (REQ : exists fx2 R2, msteps RSEGS (@mkst fx R (Z_to_bv 64 0x57844) M (seg_rom RSEGS)) (@mkst fx2 R2 (Z_to_bv 64 0xaf0ec) M (seg_rom RSEGS))
/\ getr R2 (reg 1) = Z_to_bv 64 358628 /\ getr R2 (reg 10) = Z_to_bv 64 A /\ getr R2 (reg 19) = Z_to_bv 64 (o + 1) /\ getr R2 (reg 21) = Z_to_bv 64 A
/\ getr R2 (reg 22) = Z_to_bv 64 n /\ (forall x, In x [2; 3; 4; 8; 9; 18; 23; 25; 26; 27]%nat -> getr R2 (reg x) = getr R (reg x))).
{ cfeed PP (PMURZP.ugrowS_conc fx R M (fun j => match j with 2%nat => S | 10%nat => o | 34%nat => n0 | 43%nat => m | _ => 0 end)) ltac:(first [PMK.sc]).
destruct PP as (fx1 & R1 & M1 & MG1 & FRw & _ & EX).
assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
assert (MODE : (n0 + m) mod 2 ^ 64 = n) by (rewrite Z.mod_small; lia).
destruct EX as [(MS1 & KS1 & F10 & F11 & _ & F19 & F21 & F22 & F)|(MS1 & KS1 & F1 & F10 & _ & _ & F19 & F21 & F22 & _ & F)]; rewrite MODE in F.
- pose proof (PMURZP.urec_conc fx1 R1 M (fun j => match j with 2%nat => S | 39%nat => n0 + m | 40%nat => 8 * ((n0 + m) / 8) + 7 | _ => 0 end)) as PQ.
cbn beta iota in PQ.
assert (R1_2 : getr R1 (reg 2) = Z_to_bv 64 (S - 80)) by (rewrite (KS1 2%nat) by PMK.inl; exact A2).
PMK.feed PQ ltac:(first [PMK.sc]).
destruct PQ as (fx2 & R2 & M2 & MG2 & FRw2 & _ & MS2 & KS2 & G1 & G10 & G21 & _).
assert (EM : M2 = M) by (apply functional_extensionality; exact FRw2). subst M2.
assert (EA' : 8 * ((n0 + m) / 8) + 7 + 1 = A) by (rewrite EA, Z.max_r by lia; rewrite <- En; lia).
exists fx2, R2. split; [eapply msteps_trans; [exact MS1| exact MS2]|].
split; [exact G1|]. split; [rewrite G10, EA'; reflexivity|]. split; [rewrite (KS2 19%nat) by PMK.inl; exact F19|].
split; [rewrite G21, EA'; reflexivity|]. split; [rewrite (KS2 22%nat) by PMK.inl; rewrite F22, En; reflexivity|].
intros x Hx. rewrite (KS2 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KS1. revert x Hx. apply sub_in. vm_compute. reflexivity.
- exists fx1, R1. split; [exact MS1|]. assert (EA' : A = 48) by (rewrite EA, Z.max_l by lia; reflexivity).
split; [exact F1|]. split; [rewrite F10, EA'; reflexivity|]. split; [exact F19|]. split; [rewrite F21, EA'; reflexivity|].
split; [rewrite F22, En; reflexivity|].
intros x Hx. apply KS1. revert x Hx. apply sub_in. vm_compute. reflexivity. }
destruct REQ as (fx2 & R2 & MS2 & B1 & B10 & B19 & B21 & B22 & KS2).
unfold PMSP.cfg.
apply (PMK.spiece_ro RSEGS model fx fx2 R 0x57844 R2 0xaf0ec M K Mh Ml MS2).
destruct (grow_credit (PM.VLong A n 0) A TBOK ltac:(rewrite Es; cbn; lia) ltac:(rewrite Es; cbn; lia) eq_refl LA3 CR) as (CROK & CK & Htg).
assert (STKn : L5C.stk (hl_sptop L) M (S - 80) PMSP.OPNEW_SCR).
{ apply (PMK.stk_call L M S 14336 (S - 80) PMSP.OPNEW_SCR STK); [lia| unfold PMSP.OPNEW_SCR; lia| unfold PMSP.OPNEW_SCR; lia|].
replace (S - 80) with (S + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
unfold PMU.opnew_spec, PMSP.opnew_spec in OPN. cbn [pa_opnew AD] in OPN.
apply (OPN fx2 R2 M model K LB cr0 A (S - 80) 358628 HH MOK K0).
{ rewrite L5K.rl10. exact B10. }
{ lia. }
{ exact CROK. }
{ rewrite L5K.rl1. exact B1. }
{ split; [lia| reflexivity]. }
{ rewrite L5K.rl2. rewrite (KS2 2%nat) by PMK.inl. exact A2. }
{ rewrite L5K.rl4. rewrite (KS2 4%nat) by PMK.inl. rewrite (KP 4%nat) by (cbn; auto). exact Rtp0. }
{ exact STKn. }
intros fx3 R3 M3 model3 B R3_10 RP3 FB HP3 MB3 HH3. rewrite L5K.rl10 in R3_10.
destruct FB as ((FB0 & FB1 & FB2 & FB3 & FB4) & FBa & FBd).
assert (C3 : forall x, In x [2; 8; 9; 18; 19; 21; 22; 23]%nat -> getr R3 (reg x) = getr R2 (reg x)).
{ intros x Hx. apply (PMK.cs_of_preserved R2 R3 x RP3). revert x Hx. apply sub_in. vm_compute. reflexivity. }
assert (EKn : PMK.ek L LB (S - 80) PMSP.OPNEW_SCR [] M M3) by (apply (PMK.ek_of_hpres L); exact HP3).
assert (SC0 : 0 <= PMSP.OPNEW_SCR) by (unfold PMSP.OPNEW_SCR; lia).
assert (BRX : PMFR.brange L LB) by (apply (PMFR.brange_of_heap L HI HIok _ LB cr0 M _ HH); apply incl_refl).
assert (MOK3 : PMSP.model_ok model3) by (apply (PMFR.model_ok_but_vm model model3 MOK MB3)).
apply (gan_short fx3 R3 M3 model3 n0 m B A MOK3 Es En Hm Hn0 ltac:(lia) ltac:(lia) LA4).
- rewrite (C3 2%nat) by PMK.inl. rewrite (KS2 2%nat) by PMK.inl. exact A2.
- rewrite (C3 8%nat) by PMK.inl. rewrite (KS2 8%nat) by PMK.inl. exact A8.
- rewrite (C3 9%nat) by PMK.inl. rewrite (KS2 9%nat) by PMK.inl. exact A9.
- exact R3_10.
- rewrite (C3 18%nat) by PMK.inl. rewrite (KS2 18%nat) by PMK.inl. exact A18.
- rewrite (C3 19%nat) by PMK.inl. exact B19.
- rewrite (C3 21%nat) by PMK.inl. exact B21.
- rewrite (C3 22%nat) by PMK.inl. exact B22.
- rewrite (C3 23%nat) by PMK.inl. rewrite (KS2 23%nat) by PMK.inl. exact A23.
- intros x Hx. rewrite (PMK.cs_of_preserved R2 R3 x RP3) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
rewrite (KS2 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
- destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80).
unfold saves. repeat split; (apply (PMFR.u64_keep RSEGS L KL LB (S - 80) PMSP.OPNEW_SCR [] M M3 EKn STKn SC0);
[lia|lia| intros i Hi I; destruct (PMFR.inW_nil i I)| eassumption]).
- split; [apply (PMK.ek_trans L LB S 14336 _ M0 M M3 EK)|].
{ apply (PMK.ek_callee_in' RSEGS L KL LB LB S 14336 (S - 80) PMSP.OPNEW_SCR [(o, 24)] [] M M3 HP3 (incl_refl _));
[unfold PMSP.OPNEW_SCR; lia| lia| lia| destruct STOP; lia| exact (PMFR.brange_hi L LB BRX)| intros a I; destruct (PMFR.inW_nil a I)]. }
split; [apply (PMK.dk_trans L LB S 14336 M0 M M3 DK);
apply (PMK.dk_callee L LB LB S 14336 (S - 80) PMSP.OPNEW_SCR [] M M3 HP3 (incl_refl _)); [unfold PMSP.OPNEW_SCR; lia| lia]|].
split; [apply (PMK.stk_after RSEGS L KL LB M M3 S 14336 (S - 80) PMSP.OPNEW_SCR [] STK HP3); unfold PMSP.OPNEW_SCR; lia|].
apply (PMFR.defined_keep RSEGS L KL LB (S - 80) PMSP.OPNEW_SCR [] M M3 EKn STKn SC0); [lia|lia| intros i Hi I; destruct (PMFR.inW_nil i I)| exact DO].
- exact FBd.
- exact FB0.
- exact FB4.
- exact HH3.
- exact (L5C.model_but_vm_trans _ _ _ MB MB3).
- assert (Etg : tg = 0) by (rewrite Es in TBOK; destruct TBOK as (_ & _ & X); exact X).
rewrite Etg. split; [lia|]. split; [cbn; lia|]. split; [exact LAW| lia].
- rewrite Es. cbn. lia.
- rewrite Es in CK |- *. exact CK.
Qed.
Lemma grow_long : ltac2:(TCodec.tc2 tcn__PmUResize1 "V='QM&Iy5'S5yR0%211%5241'9y8%611%311p061'G'A&QHr5%211'>'QBvS2(Q<r4r3%33821%73651vRL&R8%12<5%;3?31&R9+1%221:&R:&R?r8%2215%421;'=z%:215r9%9271%5231&Q?vS7%22J1+Jr;%C221&R>+2+K%3221%H261%A261&R;r<%2217%Q93Q=1D&Q9&R1r?vRN+@%Q6221%64541B&Q8r@r>%332=1+TP0r=%Q;221%Q?256&Q5vE%211+XPPP0%Q=221%QB261&QG&Q>%137QOQ6vRE%4221&QNrE&S4&R=u2%211%42RI1%7261vR2+R@%QN221%92RL1%R@3RL51rFu8%<11%>2S31%A241%@2S3Q9%RG3S321rGu9%C11%E2S:1%H241rA%H2S;1%RO3S;31rHu:%K11%M2SB1%Q0241%O2SBRH%S63SB21rIuB%Q211%Q42SI1%Q7241%Q62SIQ7%S=3SI21rJuG%Q911%Q;2T01%Q>241%S32KS6%Q>2T11%SE3T131&QIrK%211&QL%113&QJrL%211&Q4vB(4';%12T6T6(:%14T8T8M=vF%63421rM&H%11=%<5;4R831&Q6vRK%2216'QO&Q;vR3%211&QErQ1rQ0+ZnR4rOrN%66S=54321vC%<4S?921p0>1p0B1p0Q01p0Q41p0Q71p0Q;1p0QD1p0QL1p0R41p0R=1p0RE1p0S31p0S91p0SA1p0SE1p0SJ1p0T21p0T71p0TA1p0TE1p0TL1p0U21p0U61p0U;1p0UD1pUDUH1pV0UI1pULUJ1pU8UK1pUFUM1pQFUO1pQNV51pU>V<1").
Proof. intros fx R M model c n0 p m.
intros MOK Es En Hm Hn Hn0 TBOK Hc Hce W16 DP Hp0 Hp1 CR A2 A8 A9 A10 A18 A23 KP SV MO HH MB.
pose proof MO as (EK & DK & STK & DO). pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
pose proof (L5C.stk_writable RSEGS _ M S 14336 STK) as WR.
assert (WRo : L5.writable RSEGS M o 24) by (apply (L5C.writable_of_defined RSEGS M o 24 DO); lia).
assert (Hn2' : n < 67125248) by (unfold PM.CHUNK in Hn2; lia).
assert (Hn1' : n <= c - 1 + 16384) by (rewrite Es in Hn1; cbn [PM.vs_size] in Hn1; unfold PM.CHUNK in Hn1; lia).
assert (TLAW : PM.tb_law c) by (rewrite Es in TBOK; destruct TBOK as (_ & _ & X & _); exact X).
set (A := Z.lor (Z.max (2 * (c - 1)) n) 7 + 1).
destruct (PMF.tb_law_step c n A TLAW ltac:(lia) ltac:(lia) Hn1' ltac:(lia) eq_refl) as (LAW & LA1 & LA2 & LA3 & LA4).
assert (EA : A = 8 * (Z.max (2 * (c - 1)) n / 8) + 8) by (unfold A; apply PMF.lor7; lia).
assert (REQ : exists fx2 R2, msteps RSEGS (@mkst fx R (Z_to_bv 64 0x57844) M (seg_rom RSEGS)) (@mkst fx2 R2 (Z_to_bv 64 0xaf0ec) M (seg_rom RSEGS))
/\ getr R2 (reg 1) = Z_to_bv 64 358628 /\ getr R2 (reg 10) = Z_to_bv 64 A /\ getr R2 (reg 19) = Z_to_bv 64 p /\ getr R2 (reg 21) = Z_to_bv 64 A
/\ getr R2 (reg 22) = Z_to_bv 64 n /\ (forall x, In x [2; 3; 4; 8; 9; 18; 23; 25; 26; 27]%nat -> getr R2 (reg x) = getr R (reg x))).
{ cfeed PP (PMURZP.ugrowL_conc fx R M (fun j => match j with 2%nat => S | 10%nat => o | 34%nat => n0 | 35%nat => p | 37%nat => c - 1 | 43%nat => m | _ => 0 end)) ltac:(first [PMK.sc]).
destruct PP as (fx1 & R1 & M1 & MG1 & FRw & _ & EX).
assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
assert (MODE : (n0 + m) mod 2 ^ 64 = n) by (rewrite Z.mod_small; lia).
assert (MODC : (2 * (c - 1)) mod 2 ^ 64 = 2 * (c - 1)) by (rewrite Z.mod_small; lia).
destruct EX as [(MS1 & KS1 & F10 & F11 & _ & F19 & F21 & F22 & F)|(MS1 & KS1 & F1 & F10 & _ & _ & F19 & F21 & F22 & _ & F)]; rewrite MODE, MODC in F.
- pose proof (PMURZP.urec_conc fx1 R1 M (fun j => match j with 2%nat => S | 39%nat => n0 + m | 40%nat => 8 * ((n0 + m) / 8) + 7 | _ => 0 end)) as PQ.
cbn beta iota in PQ.
assert (R1_2 : getr R1 (reg 2) = Z_to_bv 64 (S - 80)) by (rewrite (KS1 2%nat) by PMK.inl; exact A2).
PMK.feed PQ ltac:(first [PMK.sc]).
destruct PQ as (fx2 & R2 & M2 & MG2 & FRw2 & _ & MS2 & KS2 & G1 & G10 & G21 & _).
assert (EM : M2 = M) by (apply functional_extensionality; exact FRw2). subst M2.
assert (EA' : 8 * ((n0 + m) / 8) + 7 + 1 = A) by (rewrite EA, Z.max_r by lia; rewrite <- En; lia).
exists fx2, R2. split; [eapply msteps_trans; [exact MS1| exact MS2]|].
split; [exact G1|]. split; [rewrite G10, EA'; reflexivity|]. split; [rewrite (KS2 19%nat) by PMK.inl; exact F19|].
split; [rewrite G21, EA'; reflexivity|]. split; [rewrite (KS2 22%nat) by PMK.inl; rewrite F22, En; reflexivity|].
intros x Hx. rewrite (KS2 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KS1. revert x Hx. apply sub_in. vm_compute. reflexivity.
- exists fx1, R1. split; [exact MS1|]. assert (EA' : A = 8 * ((2 * (c - 1)) / 8) + 8) by (rewrite EA, Z.max_l by lia; reflexivity).
split; [exact F1|]. split; [rewrite F10, EA'; reflexivity|]. split; [exact F19|]. split; [rewrite F21, EA'; reflexivity|].
split; [rewrite F22, En; reflexivity|].
intros x Hx. apply KS1. revert x Hx. apply sub_in. vm_compute. reflexivity. }
destruct REQ as (fx2 & R2 & MS2 & B1 & B10 & B19 & B21 & B22 & KS2).
unfold PMSP.cfg.
apply (PMK.spiece_ro RSEGS model fx fx2 R 0x57844 R2 0xaf0ec M K Mh Ml MS2).
destruct (grow_credit (PM.VLong A n 0) A TBOK ltac:(rewrite Es; cbn; lia) ltac:(rewrite Es; cbn; lia) eq_refl LA3 CR) as (CROK & CK & Htg).
assert (STKn : L5C.stk (hl_sptop L) M (S - 80) PMSP.OPNEW_SCR).
{ apply (PMK.stk_call L M S 14336 (S - 80) PMSP.OPNEW_SCR STK); [lia| unfold PMSP.OPNEW_SCR; lia| unfold PMSP.OPNEW_SCR; lia|].
replace (S - 80) with (S + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
unfold PMU.opnew_spec, PMSP.opnew_spec in OPN. cbn [pa_opnew AD] in OPN.
apply (OPN fx2 R2 M model K ((p, c) :: LB) cr0 A (S - 80) 358628 HH MOK K0).
{ rewrite L5K.rl10. exact B10. }
{ lia. }
{ exact CROK. }
{ rewrite L5K.rl1. exact B1. }
{ split; [lia| reflexivity]. }
{ rewrite L5K.rl2. rewrite (KS2 2%nat) by PMK.inl. exact A2. }
{ rewrite L5K.rl4. rewrite (KS2 4%nat) by PMK.inl. rewrite (KP 4%nat) by (cbn; auto). exact Rtp0. }
{ exact STKn. }
intros fx3 R3 M3 model3 B R3_10 RP3 FB HP3 MB3 HH3. rewrite L5K.rl10 in R3_10.
destruct FB as ((FB0 & FB1 & FB2 & FB3 & FB4) & FBa & FBd).
assert (C3 : forall x, In x [2; 8; 9; 18; 19; 21; 22; 23]%nat -> getr R3 (reg x) = getr R2 (reg x)).
{ intros x Hx. apply (PMK.cs_of_preserved R2 R3 x RP3). revert x Hx. apply sub_in. vm_compute. reflexivity. }
assert (EKn : PMK.ek L ((p, c) :: LB) (S - 80) PMSP.OPNEW_SCR [] M M3) by (apply (PMK.ek_of_hpres L); exact HP3).
assert (SC0 : 0 <= PMSP.OPNEW_SCR) by (unfold PMSP.OPNEW_SCR; lia).
assert (BRX : PMFR.brange L ((p, c) :: LB)) by (apply (PMFR.brange_of_heap L HI HIok _ _ cr0 M _ HH); apply incl_refl).
assert (WHI : forall a, PMK.inW [] a -> S - 80 <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; destruct (PMFR.inW_nil a I)).
assert (ABp : B + A <= p \/ p + c <= B) by (exact (FBa (p, c) ltac:(left; reflexivity))).
assert (MOK3 : PMSP.model_ok model3) by (apply (PMFR.model_ok_but_vm model model3 MOK MB3)).
apply (gan_long fx3 R3 M3 model3 c n0 p m B A MOK3 En Hm Hn0 ltac:(lia) ltac:(lia) LA4 Hc).
- rewrite (C3 2%nat) by PMK.inl. rewrite (KS2 2%nat) by PMK.inl. exact A2.
- rewrite (C3 8%nat) by PMK.inl. rewrite (KS2 8%nat) by PMK.inl. exact A8.
- rewrite (C3 9%nat) by PMK.inl. rewrite (KS2 9%nat) by PMK.inl. exact A9.
- exact R3_10.
- rewrite (C3 18%nat) by PMK.inl. rewrite (KS2 18%nat) by PMK.inl. exact A18.
- rewrite (C3 19%nat) by PMK.inl. exact B19.
- rewrite (C3 21%nat) by PMK.inl. exact B21.
- rewrite (C3 22%nat) by PMK.inl. exact B22.
- rewrite (C3 23%nat) by PMK.inl. rewrite (KS2 23%nat) by PMK.inl. exact A23.
- intros x Hx. rewrite (PMK.cs_of_preserved R2 R3 x RP3) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
rewrite (KS2 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply KP. exact Hx.
- destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80).
unfold saves. repeat split; (apply (PMFR.u64_keep RSEGS L KL ((p, c) :: LB) (S - 80) PMSP.OPNEW_SCR [] M M3 EKn STKn SC0);
[lia|lia| intros i Hi I; destruct (PMFR.inW_nil i I)| eassumption]).
- split; [apply (PMK.ek_trans L LB S 14336 _ M0 M M3 EK)|].
{ apply (PMK.ek_callee_in' RSEGS L KL LB ((p, c) :: LB) S 14336 (S - 80) PMSP.OPNEW_SCR [(o, 24)] [] M M3 HP3); [intros x Hx; right; exact Hx
| unfold PMSP.OPNEW_SCR; lia| lia| lia| destruct STOP; lia| intros b Hb; apply (PMFR.brange_hi L _ BRX b); right; exact Hb| intros a I; destruct (PMFR.inW_nil a I)]. }
split; [apply (PMK.dk_trans L LB S 14336 M0 M M3 DK);
apply (PMK.dk_callee L LB ((p, c) :: LB) S 14336 (S - 80) PMSP.OPNEW_SCR [] M M3 HP3); [intros x Hx; right; exact Hx| unfold PMSP.OPNEW_SCR; lia| lia]|].
split; [apply (PMK.stk_after RSEGS L KL ((p, c) :: LB) M M3 S 14336 (S - 80) PMSP.OPNEW_SCR [] STK HP3); unfold PMSP.OPNEW_SCR; lia|].
apply (PMFR.defined_keep RSEGS L KL ((p, c) :: LB) (S - 80) PMSP.OPNEW_SCR [] M M3 EKn STKn SC0); [lia|lia| intros i Hi I; destruct (PMFR.inW_nil i I)| exact DO].
- exact FBd.
- exact FB0.
- exact FB4.
- apply (L5C.defined_agree M M3 p c); [apply (PMFR.ag_block RSEGS L KL ((p, c) :: LB) (S - 80) PMSP.OPNEW_SCR [] M M3 EKn STKn SC0 BRX WHI); left; reflexivity| exact DP].
- exact Hp0.
- exact Hp1.
- exact ABp.
- exact HH3.
- exact (L5C.model_but_vm_trans _ _ _ MB MB3).
- pose proof TBOK as (Tg0 & Tg1 & _). rewrite Es in Tg1. cbn [PM.vs_cap] in Tg1.
split; [lia|]. split; [cbn [PM.vs_cap]; rewrite Z.pow_add_r by lia; change (2 ^ 1) with 2; lia|]. split; [exact LAW| lia].
- rewrite Es. cbn. lia.
- rewrite Es in CK |- *. exact CK.
Qed.
Lemma sub_wrap1 : ltac2:(TCodec.tc2 tcn__PmUResize1 "Q2'A&R9zr2%3221r3%5213&R:&R>+2+QO%3221%5271'>&R;&R8&R<+_oooooooooooOr5%3221+R0%=2<1%8231r4%9221%;214&R?%1249%?3L31p0A1p0H1p0K1pU@Q01pVDQ11").
Proof. intros x k.
intros H0 H1 H2. replace (18446744073709551615 * x) with (- x + x * 2 ^ 64) by lia. rewrite Z_mod_plus_full.
rewrite Zplus_mod_idemp_l. replace (- x + k) with (k - x) by lia. apply Z.mod_small. lia.
Qed.
Lemma sub_wrap2 : ltac2:(TCodec.tc2 tcn__PmUResize1 "Q7'A&R9zr2%3221&R:r3%2214&R>+2+QO%3221%7261'>&R;&R8&R<+_oooooooooooOr5%3221+R0%=2<1%8231r4%:213%:231%<215%<21:%>217&R?%127<+1%3221%D3Q151p0F1p0L1p0Q01pVFQ51pVDQ61").
Proof. intros x y.
intros H0 H1 H2. rewrite (Z.mod_small y) by lia. rewrite (sub_wrap1 x y) by lia.
replace (y - x + 18446744073709551615) with ((y - x - 1) + 1 * 2 ^ 64) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Definition rs_regs (R : bvmap 5 word) : Prop :=
forall x, In x [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R (reg x) = getr R0 (reg x).
Lemma saves_of : ltac2:(TCodec.tc2 tcn__PmUResize1 "SJ'S5yR0%211'9y8%511%311p051&Q9&R1r1&R?vR2+R@%3221&S6&QNvO&S4y5&R=uH%211%5241%8271%:2H1%B4A@<1r2+R8%B2A1uG%;11%>2=1%A2@1%C2Q11%K4J861r3+R0%K2J1uF%D11%G2F1%J2I1%L2Q:1%Q44Q3861r4+QH%Q42Q31uE%M11%Q02O1%Q32Q21%Q52QC1%Q=4Q<861r5+Q@%Q=2Q<1uD%Q611%Q92Q81%Q<2Q;1%Q>2QL1%QF4QE861r6+Q8%QF2QE1uC%Q?11%QB2QA1%QE2QD1%QG2R51%QO4QN861r7+Q0%QO2QN1uB%QH11%QK2QJ1%QN2QM1%R02R>1%R84R7861r8+H%R82R71u9%R111%R42R31%R72R61%R92RG1%RA4R@861r9+@%RA2R@1u8%R:11%R=2R<1%R@2R?1%RB2S01%RJ4RI861r:+8%RJ2RI1u1%RC11%RF2RE1%RI2RH1%RK2S91%S34S2861&QLr;%211p041p0>1p0H1p0Q21p0Q<1p0QF1p0R01p0R:1p0RD1p0RN1pQFSB1").
Proof. intros M. intros. unfold saves. repeat split; assumption. Qed.
Lemma mem_ok_frame : ltac2:(TCodec.tc2 tcn__PmUResize1 "QH'S5yR0%211'9y8%511%311p051&QJr2%211&R0r3%2214'A'=&R9zr1%3221&R:&R>+2+R0%3221%5271%;271&?&R?vR2+R@%3221%@21G&R8%1234%?2J1%E241%:11'>r6&S4%12Q8M%311r7%113%73Q731p091p0E1pU4Q21r4%Q:11p031p0Q71p0Q;1pQHQ?1pQFQ@1").
Proof. intros M M'.
intros (EK & DK & STK & DO) MG FR.
split; [apply (PMK.ek_trans L LB S 14336 _ M0 M M' EK);
apply (PMK.ek_piece_in RSEGS L KL LB S 14336 _ M M' (fun a => S - 80 <= a < S - 80 + 80) FR STK (PMFR.brange_hi L LB BRLB)); intros a X; left; lia|].
split; [apply (PMK.dk_trans L LB S 14336 M0 M M' DK); apply PMK.dk_grows; exact MG|].
split; [exact (PMK.stk_grows L M M' S 14336 MG STK)|]. intros i Hi. apply MG. apply DO. exact Hi.
Qed.
Lemma append_short : ltac2:(TCodec.tc2 tcn__PmUResize1 "SI'QM&Iy5'S5yR0%211%5241'9y8%611%311p061'G'A&QHr3%211'>'QBvS2(Q=%116%53431vRL&R8r4%221;%:3>41&R9+1%2215'=zr6%6221+F%8231%6231&Q?vS7%22E1&QG&Q>vE%231I5vRE%5221&QNr<&S4&R=u:%211%42QC1%7261vRN%72QD1%Q83QD31r=u;%:11%<2QK1%?241r9%?2QL1%Q@3QL31&QKr>%211&QJ%113&Q:&R1r?&R<+2%221B%6454F1&Q4vBvFr@&H%11:%6554Q731&Q6vRK%2216'QO&Q;vR3%211&QErDrC+ZmmHrBrA%66J54321vC%<4L921p0>1p0B1p0J1p0Q21p0Q51p0Q91p0QB1p0QN1p0R51p0R91p0RA1p0RE1p0RK1p0S21pUDS61pULS71pUFS91pQFS;1pQNSA1pU>SH1").
Proof. intros fx R M model n0 m.
intros MOK Es En Hm Hn0 TBOK CR A10 A11 RR MO B0 HH MB.
pose proof MO as (EK & DK & STK & DO). pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
pose proof (L5C.stk_writable RSEGS _ M S 14336 STK) as WR.
assert (WRo : L5.writable RSEGS M o 24) by (apply (L5C.writable_of_defined RSEGS M o 24 DO); lia).
assert (Hn2' : n < 67125248) by (unfold PM.CHUNK in Hn2; lia).
assert (HO : bv_unsigned (getr R (reg 10)) = o) by (rewrite A10; apply L5.unsigned_lit; lia).
destruct (PMTKU.u64_of_defined RSEGS M o ltac:(lia) ltac:(lia) ltac:(apply (L5.defined_sub M o 24 o 8 DO); lia)) as (w & Hw & W0).
pose proof (PMTKU.u64_low_byte RSEGS M o w (2 * n0) W0 B0 Hw ltac:(lia)) as WL.
pose proof (PMTKU.short_size w n0 Hw WL Hn0) as HSS.
assert (TB0 : Z.testbit w 0 = false).
{ rewrite <- (Z.mod_pow2_bits_low w 8 0) by lia. change (2 ^ 8) with 256. rewrite WL. apply PMF.even_byte. }
assert (R2 : getr R (reg 2) = Z_to_bv 64 S) by (rewrite (RR 2%nat) by PMK.inl; exact Rsp0).
pose proof (PMURZP.uapS0_conc fx R M (fun j => match j with 2%nat => S | 33%nat => 2 * n0 | 36%nat => w | 43%nat => m | _ => 0 end)) as PP.
cbn beta iota in PP. rewrite HO in PP.
PMK.feed PP ltac:(first [PMK.sc | apply PMF.even_byte]).
destruct PP as (fx1 & R1 & M1 & MG1 & _ & FR1 & EX).
rewrite HSS in EX. rewrite (sub_wrap1 n0 22) in EX by lia.
assert (MO1 : mem_ok M1) by (apply (mem_ok_frame M M1 MO MG1); intros a Ha X; apply FR1; [exact Ha| exact X]).
assert (B01 : L5.u8_at RSEGS M1 o (2 * n0)) by (apply (L5C.u8_at_agree RSEGS M M1); [intros i Hi; apply FR1; lia|lia|lia|exact B0]).
set (P := fun a => S - 80 <= a < S - 80 + 80).
assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) by exact FR1.
unfold PMSP.cfg.
destruct EX as [(MS1 & KS1 & E2 & E8 & E9 & E10 & _ & E18 & E23 & F & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)
|(MS1 & KS1 & E2 & E8 & E9 & E10 & _ & E18 & E23 & F & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)].
- apply (PMK.spiece RSEGS L HI KL HIok LB cr0 M model fx fx1 R 0x577b8 R1 0x5781c M1 P K HH Mh Ml ltac:(destruct STOP; lia) MS1 MG1 FRZ).
{ intros a Pa. unfold P in Pa. apply (PMK.cwr_stack L LB M S 14336 a STK); lia. }
{ intros a. unfold P. apply PMK.rng_dec. }
intros HH1.
apply (fit_short fx1 R1 M1 model n0 m MOK Es En Hm ltac:(lia) ltac:(lia)).
+ rewrite Es in TBOK. destruct TBOK as (_ & _ & X). exact X.
+ exact E2.
+ rewrite E8, A10. reflexivity.
+ exact E9.
+ exact E10.
+ rewrite <- (Z_to_bv_bv_unsigned _ (getr R1 (reg 18))), E18. reflexivity.
+ exact E23.
+ intros x Hx. rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply RR. revert x Hx. apply sub_in. vm_compute. reflexivity.
+ apply saves_of; (rewrite <- (RR _) by PMK.inl; eassumption).
+ exact MO1.
+ exact B01.
+ exact HH1.
+ exact MB.
- apply (PMK.spiece RSEGS L HI KL HIok LB cr0 M model fx fx1 R 0x577b8 R1 0x57844 M1 P K HH Mh Ml ltac:(destruct STOP; lia) MS1 MG1 FRZ).
{ intros a Pa. unfold P in Pa. apply (PMK.cwr_stack L LB M S 14336 a STK); lia. }
{ intros a. unfold P. apply PMK.rng_dec. }
intros HH1.
apply (grow_short fx1 R1 M1 model n0 m MOK Es En Hm ltac:(lia) Hn0 TBOK CR).
+ exact E2.
+ rewrite E8, A10. reflexivity.
+ exact E9.
+ exact E10.
+ rewrite <- (Z_to_bv_bv_unsigned _ (getr R1 (reg 18))), E18. reflexivity.
+ exact E23.
+ intros x Hx. rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply RR. revert x Hx. apply sub_in. vm_compute. reflexivity.
+ apply saves_of; (rewrite <- (RR _) by PMK.inl; eassumption).
+ exact MO1.
+ exact HH1.
+ exact MB.
Qed.
Lemma append_long : ltac2:(TCodec.tc2 tcn__PmUResize1 "T5'QM&Iy5'S5yR0%211%5241'9y8%611%311p061'G'A&QHr5%211'>'QBvS2(Q<r4r3%33821%73651vRL&R8%12<5%;3?31&R9+1%221:&Q?vS7%22?1&QG&Q>vE%231C5vRE%5221&QNr=&S4&R=u:%211%42Q=1%7261vRN%72Q>1%Q23Q>31r>u;%:11%<2QE1%?241r8%?2QF1%Q:3QF31&QKr?%211&QJ%113&QC&R1&QDr@%45321DQB+TP0%Q:21M%Q>2D4&R?&Q5%11Q6+XPPP0%4221%QA261&Q4vB(4';%12R6R6(:rA%24R9R9I1vF%73521rC&HrB%211%>5=5QF41&Q6vRK%2217'QO&Q;vR3%211&QErGrF+ZmmHrErD%66Q954321vC%<4Q;921p0>1p0B1p0Q21p0Q:1p0Q=1p0QC1p0QF1p0QJ1p0R31p0R?1p0RF1p0RJ1p0RN1p0S31p0S<1pUDS@1pV0SA1pULSB1pU8SC1pUFSE1pQFSG1pQNSM1pU>T41").
Proof. intros fx R M model c n0 p m.
intros MOK Es En Hm TBOK CR A10 A11 RR MO VS Hp0 Hp1 HH MB.
pose proof MO as (EK & DK & STK & DO). pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
rewrite Es in VS. destruct VS as (_ & _ & W0 & W8 & W16 & Hnc & Hc & Hce & DP & _).
pose proof (L5C.stk_writable RSEGS _ M S 14336 STK) as WR.
assert (WRo : L5.writable RSEGS M o 24) by (apply (L5C.writable_of_defined RSEGS M o 24 DO); lia).
assert (Hn2' : n < 67125248) by (unfold PM.CHUNK in Hn2; lia).
assert (HO : bv_unsigned (getr R (reg 10)) = o) by (rewrite A10; apply L5.unsigned_lit; lia).
pose proof (PMF.u8_of_u64 RSEGS M o (c + 1) ltac:(lia) W0) as B0. pose proof (PMF.odd_byte c Hce ltac:(lia)) as ODB.
assert (H33 : 0 <= (c + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c + 1) 256 ltac:(lia)); lia).
assert (TB1 : Z.testbit (c + 1) 0 = true) by (rewrite <- (Z.mod_pow2_bits_low (c + 1) 8 0) by lia; exact ODB).
assert (EC : 2 * ((c + 1) / 2) = c) by (pose proof (Z.div_mod (c + 1) 2 ltac:(lia)) as X; rewrite Z.add_mod, Hce in X by lia; cbn in X; lia).
assert (R2 : getr R (reg 2) = Z_to_bv 64 S) by (rewrite (RR 2%nat) by PMK.inl; exact Rsp0).
pose proof (PMURZP.uapL0_conc fx R M (fun j => match j with 2%nat => S | 33%nat => (c + 1) mod 256 | 34%nat => n0 | 36%nat => c + 1 | 43%nat => m | _ => 0 end)) as PP.
cbn beta iota in PP. rewrite HO in PP.
PMK.feed PP ltac:(first [PMK.sc]).
destruct PP as (fx1 & R1 & M1 & MG1 & _ & FR1 & EX).
rewrite EC in EX. rewrite (sub_wrap2 n0 c) in EX by lia.
assert (MO1 : mem_ok M1) by (apply (mem_ok_frame M M1 MO MG1); intros a Ha X; apply FR1; [exact Ha| exact X]).
assert (W01 : L5.u64_at RSEGS M1 o (c + 1)) by (apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1; lia|lia|lia|exact W0]).
assert (W161 : L5.u64_at RSEGS M1 (o + 16) p) by (apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1; lia|lia|lia|exact W16]).
assert (DP1 : L5.defined M1 p c) by (intros i Hi; apply MG1; apply DP; exact Hi).
set (P := fun a => S - 80 <= a < S - 80 + 80).
assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) by exact FR1.
unfold PMSP.cfg.
destruct EX as [(MS1 & KS1 & E2 & E8 & E9 & E10 & _ & E18 & E23 & F & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)
|(MS1 & KS1 & E2 & E8 & E9 & E10 & _ & E18 & E23 & F & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)].
- apply (PMK.spiece RSEGS L HI KL HIok ((p, c) :: LB) cr0 M model fx fx1 R 0x577b8 R1 0x5781c M1 P K HH Mh Ml ltac:(destruct STOP; lia) MS1 MG1 FRZ).
{ intros a Pa. unfold P in Pa. apply (PMK.cwr_stack L ((p, c) :: LB) M S 14336 a STK); lia. }
{ intros a. unfold P. apply PMK.rng_dec. }
intros HH1.
apply (fit_long fx1 R1 M1 model c n0 p m MOK Es En Hm ltac:(lia)).
+ exact E2.
+ rewrite E8, A10. reflexivity.
+ exact E9.
+ exact E10.
+ exact E18.
+ intros x Hx. rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply RR. revert x Hx. apply sub_in. vm_compute. reflexivity.
+ apply saves_of; (rewrite <- (RR _) by PMK.inl; eassumption).
+ exact MO1.
+ exact W01.
+ exact W161.
+ lia.
+ exact Hc.
+ exact Hce.
+ exact DP1.
+ exact Hp0.
+ exact Hp1.
+ exact TBOK.
+ exact HH1.
+ exact MB.
- apply (PMK.spiece RSEGS L HI KL HIok ((p, c) :: LB) cr0 M model fx fx1 R 0x577b8 R1 0x57844 M1 P K HH Mh Ml ltac:(destruct STOP; lia) MS1 MG1 FRZ).
{ intros a Pa. unfold P in Pa. apply (PMK.cwr_stack L ((p, c) :: LB) M S 14336 a STK); lia. }
{ intros a. unfold P. apply PMK.rng_dec. }
intros HH1.
apply (grow_long fx1 R1 M1 model c n0 p m MOK Es En Hm ltac:(lia) ltac:(lia) TBOK Hc Hce W161 DP1 Hp0 Hp1 CR).
+ exact E2.
+ rewrite E8, A10. reflexivity.
+ exact E9.
+ exact E10.
+ exact E18.
+ exact E23.
+ intros x Hx. rewrite (KS1 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity). apply RR. revert x Hx. apply sub_in. vm_compute. reflexivity.
+ apply saves_of; (rewrite <- (RR _) by PMK.inl; eassumption).
+ exact MO1.
+ exact HH1.
+ exact MB.
Qed.
Lemma resize_entry : ltac2:(TCodec.tc2 tcn__PmUResize1 "R9'QM&QHvRK%211&Q4vB&2';'A%2211&QAvS2%211vF%83521vREvL&H%11@%?5>5431'>'S5yR0%211&QNvO&S4y5&R=u:%211%5241%8271vRN%82<1%?3<31u;%911%<2;1%?2>1vRL%?2C1%F3C31&QC&R1&QD%3521N=Q3&Q?vS7%22Q61&QG&Q>vE%231Q:5%421Q7'QO&Q;vR3%211&QEr8+ZoYD%36B2Q51Q>QLvC%94D621p0;1p0A1p0E1p0J1p0Q21p0QC1p0R41pU>R81").
Proof. intros fx.
intros MOK HH A10 A11 VS TBOK CR.
pose proof MOK as (Mh & Ml & Mm). pose proof STK0 as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
pose proof VS as (DO & _ & _).
assert (WRo : L5.writable RSEGS M0 o 24) by (apply (L5C.writable_of_defined RSEGS M0 o 24 DO); lia).
assert (HO : bv_unsigned (getr R0 (reg 10)) = o) by (rewrite A10; apply L5.unsigned_lit; lia).
assert (Hn2' : n < 67125248) by (unfold PM.CHUNK in Hn2; lia).
assert (MO0 : mem_ok M0).
{ split; [apply PMK.ek_refl|]. split; [apply PMK.dk_refl|]. split; [exact STK0| exact DO]. }
assert (RR0 : rs_regs R0) by (intros x _; reflexivity).
unfold PMSP.cfg.
assert (CASE : (exists n0, s = PM.VShort n0) \/ (exists c n0 p, s = PM.VLong c n0 p)) by (destruct s as [x|x y z]; [left; exists x | right; exists x, y, z]; reflexivity).
destruct CASE as [(n0 & Es)|(c & n0 & p & Es)]; rewrite Es in VS, HH.
-
destruct VS as (_ & _ & Hn0 & B0).
assert (Hn1' : n <= n0 + 16384) by (rewrite Es in Hn1; cbn [PM.vs_size] in Hn1; unfold PM.CHUNK in Hn1; lia).
pose proof (PMURZP.urzS_conc fx R0 M0 (fun j => match j with 2%nat => S | 33%nat => 2 * n0 | 37%nat => n | _ => 0 end)) as PP.
cbn beta iota in PP. rewrite HO in PP.
PMK.feed PP ltac:(first [PMK.sc | apply PMF.even_byte]).
destruct PP as (fx1 & R1 & M1 & MG1 & FRw & _ & EX).
assert (EM : M1 = M0) by (apply functional_extensionality; exact FRw). subst M1.
replace (2 * n0 / 2) with n0 in EX by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
destruct EX as [(MS1 & KS1 & F13 & _ & F)|(MS1 & KS1 & F11 & _ & _ & F)].
+
apply (PMK.spiece_ro RSEGS model0 fx fx1 R0 0x57d34 R1 0x57d48 M0 K Mh Ml MS1).
assert (R1_2 : getr R1 (reg 2) = Z_to_bv 64 S) by (rewrite (KS1 2%nat) by PMK.inl; exact Rsp0).
assert (R1_11 : getr R1 (reg 11) = Z_to_bv 64 n) by (rewrite (KS1 11%nat) by PMK.inl; exact A11).
assert (HO1 : bv_unsigned (getr R1 (reg 10)) = o) by (rewrite (KS1 10%nat) by PMK.inl; exact HO).
pose proof (PMURZP.urzTS_conc fx1 R1 M0 (fun j => match j with 2%nat => S | 37%nat => n | _ => 0 end)) as PT.
cbn beta iota in PT. rewrite HO1 in PT.
PMK.feed PT ltac:(first [PMK.sc]).
PMK.pvz_hg ltac:(idtac; destruct PT as (fx2 & R2 & M2 & pvzP); PMK.pvz_lin pvzP;
destruct pvzP as (MG2 & _ & FRZ0 & MS2 & KS2 & _ & _ & _ & CN & CB)); PMK.pvz_clrT.
set (P := fun a => o <= a < o + 24).
assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M2 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)).
{ intros a Ha N. apply FRZ0; [exact Ha| intro X; apply N; unfold P; lia]. }
apply (PMK.spiece RSEGS L HI KL HIok (PM.vs_own (PM.VShort n0) ++ LB) cr0 M0 model0 fx1 fx2 R1 0x57d48 R2 0x57d60 M2 P K HH Mh Ml ltac:(destruct STOP; lia) MS2 MG2 FRZ).
{ intros a Pa. unfold P in Pa. apply (PMK.cwr_stack L _ M0 S 14336 a STK0); lia. }
{ intros a. unfold P. apply PMK.rng_dec. }
intros HH2.
assert (RA2 : getr R2 (reg 1) = Z_to_bv 64 r) by (rewrite (KS2 1%nat) by PMK.inl; rewrite (KS1 1%nat) by PMK.inl; exact Rra0).
unfold PMK.cfg.
eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx2 R2 M2 0x57d60 (ltac:(oW' 0x57d60%Z)) r (ltac:(oF' 0x57d60%Z)) ltac:(reflexivity) (ltac:(oD' 0x57d60%Z)) RA2 Hr1 Hr2)|].
apply (KONT fx2 R2 M2 model0 (PM.VShort n) tg cr0); [| | reflexivity | | | | | apply L5C.model_but_vm_refl | exact HH2].
* apply PMK.preserved_by_index. intros x Hx. rewrite (KS2 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
apply KS1. revert x Hx. apply sub_in. vm_compute. reflexivity.
* split; [intros i Hi; apply MG2; apply DO; exact Hi|]. split; [exact I|]. split; [lia| exact CB].
* rewrite Es in TBOK. unfold PM.tb_ok in *. cbn [PM.vs_cap] in *. exact TBOK.
* intros _. rewrite Es. split; reflexivity.
* apply (PMK.hpres_of L LB S 14336 _ M0 M2).
-- apply (PMK.ek_piece L LB S 14336 _ M0 M2 P FRZ). intros a Ha CA NE OW Pa. unfold P in Pa.
apply (OW (o, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
-- destruct (PMK.stk_grows L M0 M2 S 14336 MG2 STK0) as (_ & _ & _ & _ & D2). exact D2.
-- apply PMK.dk_grows. exact MG2.
* rewrite Es. unfold PMSP.credit_keep, PM.pot_text. cbn [PM.vs_cap]. lia.
+
apply (PMK.spiece_ro RSEGS model0 fx fx1 R0 0x57d34 R1 0x577b8 M0 K Mh Ml MS1).
apply (append_short fx1 R1 M0 model0 n0 (n - n0) MOK Es ltac:(lia) ltac:(lia) Hn0 TBOK CR).
* rewrite (KS1 10%nat) by PMK.inl. exact A10.
* exact F11.
* intros x Hx. apply KS1. revert x Hx. apply sub_in. vm_compute. reflexivity.
* exact MO0.
* exact B0.
* exact HH.
* apply L5C.model_but_vm_refl.
-
pose proof VS as (_ & _ & W0 & W8 & W16 & Hnc & Hc & Hce & DP & _).
assert (Ip : In (p, c) (PM.vs_own (PM.VLong c n0 p) ++ LB)) by (left; reflexivity).
destruct (PMFR.brange_of_heap L HI HIok _ _ cr0 M0 _ HH (incl_refl _) p c Ip) as (Pp0 & Pp1 & Pp4).
pose proof (PMF.u8_of_u64 RSEGS M0 o (c + 1) ltac:(lia) W0) as B0. pose proof (PMF.odd_byte c Hce ltac:(lia)) as ODB.
assert (H33 : 0 <= (c + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c + 1) 256 ltac:(lia)); lia).
pose proof (PMURZP.urzL_conc fx R0 M0 (fun j => match j with 2%nat => S | 33%nat => (c + 1) mod 256 | 34%nat => n0 | 37%nat => n | _ => 0 end)) as PP.
cbn beta iota in PP. rewrite HO in PP.
PMK.feed PP ltac:(first [PMK.sc]).
destruct PP as (fx1 & R1 & M1 & MG1 & FRw & _ & EX).
assert (EM : M1 = M0) by (apply functional_extensionality; exact FRw). subst M1.
destruct EX as [(MS1 & KS1 & F11 & _ & _ & F)|(MS1 & KS1 & F13 & _ & F)].
+
apply (PMK.spiece_ro RSEGS model0 fx fx1 R0 0x57d34 R1 0x577b8 M0 K Mh Ml MS1).
apply (append_long fx1 R1 M0 model0 c n0 p (n - n0) MOK Es ltac:(lia) ltac:(lia) TBOK CR).
* rewrite (KS1 10%nat) by PMK.inl. exact A10.
* rewrite F11. f_equal. lia.
* intros x Hx. apply KS1. revert x Hx. apply sub_in. vm_compute. reflexivity.
* exact MO0.
* rewrite Es. exact VS.
* exact Pp0.
* exact Pp4.
* exact HH.
* apply L5C.model_but_vm_refl.
+
apply (PMK.spiece_ro RSEGS model0 fx fx1 R0 0x57d34 R1 0x57d48 M0 K Mh Ml MS1).
assert (R1_2 : getr R1 (reg 2) = Z_to_bv 64 S) by (rewrite (KS1 2%nat) by PMK.inl; exact Rsp0).
assert (R1_11 : getr R1 (reg 11) = Z_to_bv 64 n) by (rewrite (KS1 11%nat) by PMK.inl; exact A11).
assert (HO1 : bv_unsigned (getr R1 (reg 10)) = o) by (rewrite (KS1 10%nat) by PMK.inl; exact HO).
assert (WRp : L5.writable RSEGS M0 (p + n) 1) by (apply (L5C.writable_of_defined RSEGS M0 (p + n) 1); [apply (L5.defined_sub M0 p c (p + n) 1 DP); lia|lia|lia]).
assert (Dpo : p + n + 1 <= o \/ o + 24 <= p + n) by (left; lia).
pose proof (PMURZP.urzTL_conc fx1 R1 M0 (fun j => match j with 2%nat => S | 35%nat => p | 37%nat => n | _ => 0 end)) as PT.
cbn beta iota in PT. rewrite HO1 in PT.
PMK.feed PT ltac:(first [PMK.sc]).
PMK.pvz_hg ltac:(idtac; destruct PT as (fx2 & R2 & M2 & pvzP); PMK.pvz_lin pvzP;
destruct pvzP as (MG2 & _ & FRZ0 & MS2 & KS2 & _ & _ & CN & C8)); PMK.pvz_clrT.
set (P := fun a => (o + 8 <= a < o + 8 + 8) \/ (p + n <= a < p + n + 1)).
assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M2 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)).
{ intros a Ha N. apply FRZ0; [exact Ha| intro X; apply N; unfold P; lia| intro X; apply N; unfold P; lia]. }
apply (PMK.spiece RSEGS L HI KL HIok (PM.vs_own (PM.VLong c n0 p) ++ LB) cr0 M0 model0 fx1 fx2 R1 0x57d48 R2 0x57d84 M2 P K HH Mh Ml ltac:(destruct STOP; lia) MS2 MG2 FRZ).
{ intros a Pa. unfold P in Pa. destruct Pa as [X|X];
[apply (PMK.cwr_stack L _ M0 S 14336 a STK0); lia
|apply (PMK.cwr_block L _ p c a Ip); lia]. }
{ intros a. unfold P. apply PMK.or_dec; apply PMK.rng_dec. }
intros HH2.
assert (RA2 : getr R2 (reg 1) = Z_to_bv 64 r) by (rewrite (KS2 1%nat) by PMK.inl; rewrite (KS1 1%nat) by PMK.inl; exact Rra0).
unfold PMK.cfg.
eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx2 R2 M2 0x57d84 (ltac:(oW' 0x57d84%Z)) r (ltac:(oF' 0x57d84%Z)) ltac:(reflexivity) (ltac:(oD' 0x57d84%Z)) RA2 Hr1 Hr2)|].
assert (AG : forall a m, 0 <= a -> a + m <= 2 ^ 64 -> (forall i, a <= i < a + m -> ~ P i) -> L5C.agree_on M0 M2 a m).
{ intros a0 m0 Ha0 Hm0 X i Hi. apply FRZ; [lia| apply X; exact Hi]. }
apply (KONT fx2 R2 M2 model0 (PM.VLong c n p) tg cr0); [| | reflexivity | | | | | apply L5C.model_but_vm_refl | exact HH2].
* apply PMK.preserved_by_index. intros x Hx. rewrite (KS2 x) by (revert x Hx; apply sub_in; vm_compute; reflexivity).
apply KS1. revert x Hx. apply sub_in. vm_compute. reflexivity.
* split; [intros i Hi; apply MG2; apply DO; exact Hi|]. split; [exact I|].
split; [apply (L5C.u64_at_agree RSEGS M0 M2); [apply AG; [lia|lia| intros i Hi X; unfold P in X; destruct X as [X|X]; cdisj; lia]|lia|lia|exact W0]|].
split; [exact C8|].
split; [apply (L5C.u64_at_agree RSEGS M0 M2); [apply AG; [lia|lia| intros i Hi X; unfold P in X; destruct X as [X|X]; cdisj; lia]|lia|lia|exact W16]|].
split; [lia|]. split; [lia|]. split; [exact Hce|]. split; [intros i Hi; apply MG2; apply DP; exact Hi| exact I].
* rewrite Es in TBOK. unfold PM.tb_ok in *. cbn [PM.vs_cap] in *. exact TBOK.
* intros _. rewrite Es. split; reflexivity.
* apply (PMK.hpres_of L LB S 14336 _ M0 M2).
-- apply (PMK.ek_piece L LB S 14336 _ M0 M2 P FRZ). intros a Ha CA NE OW Pa. unfold P in Pa. destruct Pa as [X|X].
++ apply (OW (o, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
++ exact (PMSRS.own_not_client L HI HIok [(p, c)] LB cr0 M0 _ p c a S 14336 HH ltac:(left; reflexivity) ltac:(lia) CA).
-- destruct (PMK.stk_grows L M0 M2 S 14336 MG2 STK0) as (_ & _ & _ & _ & D2). exact D2.
-- apply PMK.dk_grows. exact MG2.
* rewrite Es. unfold PMSP.credit_keep, PM.pot_text. cbn [PM.vs_cap]. lia.
Qed.
End Call.
End WithHeap.
End PMURZ1.
