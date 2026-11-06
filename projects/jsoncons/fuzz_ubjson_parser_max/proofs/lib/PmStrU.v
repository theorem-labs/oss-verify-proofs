(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StreamSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit PmLayout PmLayoutU PmModel PmModelFacts PmStatics PmSpecs PmSpecsU PmStep PmKeep PmFrame PmKitU PmCertKitU PmSrcUMemmove PmStrUP.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmStrU () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5CoreKit.L5K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsU.PMU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStep.PMK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStrU.PMSTRU.Stage."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStrUP.PMSTUP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.Arith.PeanoNat.Nat."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0B"; "1bool"; "1cons"; "1fst"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1snd"; "1true"; "2and"; "2eq"; "2ex"; "2or"]; ["3Z"; "0HI"; "0KS"; "0L"; "0LB"; "4VmMaps"; "5bvmap"; "0M"; "0M1"; "0R"; "0R1"; "6credit"; "6hi_heap"; "6hl_sptop"; "7CS"; "8defined"]; ["8writable"; "9cr0"; "9credit_keep"; "9str_count"; ":opnew_spec"; ":str_ctor_spec"; ";cs_all"; "<case_spec"; "<head_ok"; "=KS_uscH23"; "=KS_uscHg"; "=KS_uscN"; "=KS_uscT"; "=KS_uscZ"; ">FPState"; ">getr"]; ["?loaded_segments"; "0SCFG_P"; "@eqb"; "AIn"; "Aexistsb"; "Badd"; "Ble"; "Blt"; "Bmodulo"; "Bof_nat"; "Bpow"; "Bsub"; "0VM"; "0c"; "0cr"; "0fx"]; ["0fx1"; "0k"; "0m"; "0n"; "0o"; "0ptr"; "0sp"; "CZ_to_bv"; "Cbv"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc. Local Ltac lia := L5FastLia.plia.
Module PMSTRU.
Import PMU.
Lemma cs_scZ : ltac2:(TCodec.tc2 tcn__PmStrU ":'5&QCr1&Q6%33421r2&Q=%63721p041pT491"). Proof. PMCKU.cs_all_tac. Qed.
Lemma cap_facts : ltac2:(TCodec.tc2 tcn__PmStrU "Q2'@'<&QF+Gr1%3221&QG&QJ+2+J%3221%5271%;271r2&Q3%112%:231%?282&QE+@%2271%C261%E251'=&QH%12:Az%43K21%J2=B%L221%M281%N2?1p0D1pT8Q11").
Proof. intros n.
intros Hn. unfold PMSP.str_count. destruct (Z.eqb_spec n 23) as [->|NE]; [cbn; Lia.lia|].
rewrite PMF.lor7 by Lia.lia. pose proof (Z.div_mod n 8 ltac:(Lia.lia)) as D. pose proof (Z.mod_pos_bound n 8 ltac:(Lia.lia)) as B.
replace (8 * (n / 8) + 8) with ((n / 8 + 1) * 2 * 2 * 2) by Lia.lia.
split; [Lia.lia|]. split; [Lia.lia|]. split; [|Lia.lia].
replace ((n / 8 + 1) * 2 * 2 * 2) with (((n / 8 + 1) * 4) * 2) by Lia.lia. apply Z.mod_mul. Lia.lia.
Qed.
Section Stage.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMU.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKU.klayout_U L LY.
Definition case_spec (C : Z -> Prop) : Prop :=
forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
(LB : list (Z * Z)) (cr : credit) (o ptr n sp r : Z),
C n ->
hi_heap HI LB cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> PMSP.entry AD L R M sp r 0 ->
getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 ptr -> getr R 12%bv = Z_to_bv 64 n ->
0 <= n < 2 ^ 26 -> sp <= o -> o + 24 <= hl_sptop L -> o mod 8 = 0 -> L5.defined M o 24 ->
(n = 0 \/ (exists B m, In (B, m) LB /\ B <= ptr /\ ptr + n <= B + m)) ->
PMSP.credit_le (PM.cost1 L (n + 16)) cr ->
(forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (s : PM.vstr) (cr' : credit),
regs_preserved R R' -> PM.vstr_at RSEGS PMSP.T3 M' o s -> PM.vs_size s = n ->
(n <= 22 -> s = PM.VShort n) -> (23 <= n -> exists p, s = PM.VLong (PMSP.str_count n) n p) ->
L5C.hpres L LB sp (PMSP.pm_scr 0) [(o, 24)] M M' ->
PMSP.credit_keep cr cr' (PM.cost1 L (n + 16)) PMSP.cr0 ->
model_but_vm model model' -> hi_heap HI (PM.vs_own s ++ LB) cr' M' (m_vmmaps model') ->
srealizes RSEGS SCFG (PMSP.cfg RSEGS R' r M' model') K) ->
srealizes RSEGS SCFG (PMSP.cfg RSEGS R (pa_str_ctor AD) M model) K.
Lemma credit_keep_none : ltac2:(TCodec.tc2 tcn__PmStrU "G&K'9'@%2211&QFz&3r1%23661%5241&:r2%23::1%9281&Q2r4r3&Q1%443321p061p0;1pSLB1pSNF1").
Proof. intros cr c. intros H1 H2. unfold PMSP.credit_keep, PMSP.cr0. cbn [fst snd]. lia. Qed.
Lemma case_zero : ltac2:(TCodec.tc2 tcn__PmStrU "8&Q7'@'=r1z%33421qT851%711").
Proof.
intros fx R M model K LB cr o ptr n sp r Hc HH (Mh & Ml & Mm) K0 ENT A10 A11 A12 Hn Hspo Hotop Ho8 DEFO SRCB CRED KONT. subst n.
destruct ENT as (Rra & (RA1 & RA2) & Rsp & Rgp & Rtp & STK).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl10 in A10. rewrite L5K.rl12 in A12.
pose proof (L5C.stk_floor _ _ _ _ STK) as FL. pose proof (L5C.stk_writable RSEGS _ M sp _ STK) as WR0.
pose proof STK as (S16 & SB & SC & SD & SW). unfold PMSP.pm_scr in *.
assert (WRO : L5.writable RSEGS M o 24) by (apply (L5C.writable_of_defined RSEGS M o 24 DEFO); lia).
pose proof (PMCKU.lb_hi L HI HIok LB cr M _ HH) as LBhi.
cfeed P (PMSTUP.uscZ_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | _ => 0 end)) ltac:(first [ PMK.sc ]).
destruct P as (fx1 & R1 & M1 & MG & FR & FRZ & MS & KS & B10 & B11 & C1 & C0).
unfold PMSP.cfg. cbn [pa_str_ctor AD PmLayoutU.ADDR_U].
set (P := fun a => sp - 48 <= a < sp \/ o <= a < o + 24).
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha NP. unfold P in NP. apply FRZ; [exact Ha| |]; intros X; apply NP; lia. }
apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x34488 R1 0x34544 M1 P K HH Mh Ml ltac:(lia) MS MG AG).
{ intros a Ha. apply (PMK.cwr_stack L LB M sp (12288 + 2048 * 0) a STK). unfold P in Ha. lia. }
{ intros a. unfold P. apply PMK.or_dec; apply PMK.rng_dec. }
intros HH1.
eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx1 R1 M1 0x34544 (ltac:(oW' 0x34544%Z)) r (ltac:(oF' 0x34544%Z)) ltac:(reflexivity) (ltac:(oD' 0x34544%Z)))|].
- rewrite (KS 1%nat) by (apply L5K.In_of_mem; vm_compute; reflexivity). exact Rra.
- exact RA1.
- exact RA2.
- apply (KONT fx1 R1 M1 model (PM.VShort 0) cr).
+ apply PMK.preserved_by_index. intros k Hk. apply KS. apply cs_scZ. exact Hk.
+ split; [apply (L5.defined_grows M M1 _ _ MG); exact DEFO|]. split; [exact I|]. split; [lia| exact C0].
+ reflexivity.
+ intros _. reflexivity.
+ intros X. lia.
+ apply PMK.hpres_of.
* apply (PMK.ek_piece_in RSEGS L KL LB sp (12288 + 2048 * 0) [(o, 24)] M M1 P AG STK LBhi).
intros a [X|X]; [left; lia| right; apply PMK.inW_here; exact X].
* apply (L5.defined_grows M M1 _ _ MG). exact SW.
* apply PMK.dk_grows. exact MG.
+ apply credit_keep_none; unfold PM.cost1; cbn [fst snd]; pose proof (ly_kpm L LY); pose proof (ly_bov L LY); lia.
+ apply L5C.model_but_vm_refl.
+ cbn [PM.vs_own app]. exact HH1.
Qed.
Lemma src_facts : ltac2:(TCodec.tc2 tcn__PmStrU "RF'4'9'@%2211%411&K'R8yR0%211'7y8%511%311p051'E&LvAr6r5r4r3%6554321&QF+1r2%3221'?'=z%23K91'>'<&QC(8r1%24Q1Q1;1r:%53Q221%@2>E&QE%12GF%22A7%D221%<251%=271qT6Q;1%@2Q<1q2Q=1%B2Q>1%G2D1+TP0%M21Q1%=2Q2Q1&QK&MvC%211+XPPP0%5221%Q5271&Or7%231Q<Q;r;%Q03QMM1%Q;2Q94%K25QA%Q=21J%Q5231%Q6251qT6R41%Q92R51q2R61%Q;2R71%Q;2<1%Q<2@1%Q=2I1p0L1p0QE1p0QJ1pT8R>1pT<R?1pSJR41pQ@R61pSNR?1pQ:RA1").
Proof. intros LB cr M VM ptr n.
intros HH Hn [E|(B & m & Hin & H1 & H2)]; [lia|].
pose proof (proj1 (hio_wf L SCFG HI HIok LB cr M VM HH) (B, m) Hin) as ((Q0 & Q1 & Q2 & Q3 & Q4) & DEF & _). cbn [fst snd] in *.
split; [lia|]. split; [lia|]. split; [apply (L5.defined_sub M B m); [exact DEF| lia| lia]|]. exists B, m. auto.
Qed.
Lemma case_short : ltac2:(TCodec.tc2 tcn__PmStrU "<&Q7'@'<&QF+1r1%3221+F%5231%7231qT891%;11").
Proof.
intros fx R M model K LB cr o ptr n sp r Hc HH (Mh & Ml & Mm) K0 ENT A10 A11 A12 Hn Hspo Hotop Ho8 DEFO SRCB CRED KONT.
destruct ENT as (Rra & (RA1 & RA2) & Rsp & Rgp & Rtp & STK).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl12 in A12.
pose proof (L5C.stk_floor _ _ _ _ STK) as FL. pose proof (L5C.stk_writable RSEGS _ M sp _ STK) as WR0.
pose proof STK as (S16 & SB & SC & SD & SW). unfold PMSP.pm_scr in *.
assert (WRO : L5.writable RSEGS M o 24) by (apply (L5C.writable_of_defined RSEGS M o 24 DEFO); lia).
pose proof (PMCKU.lb_hi L HI HIok LB cr M _ HH) as LBhi.
destruct (src_facts LB cr M _ ptr n HH ltac:(lia) SRCB) as (PT0 & PT1 & PDEF & _).
assert (CEIL : hl_ceil L <= sp - 12288) by (unfold hl_ceil; lia).
cfeed P (PMSTUP.uscS_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => n | 35%nat => ptr | _ => 0 end)) ltac:(first [ PMK.sc ]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ & MS & KS & B1 & B2 & B8 & B9 & B10 & B18 & B19 & C0 & S48 & S40 & S32 & S24 & S16b & S8)); PMK.pvz_clrT.
unfold PMSP.cfg. cbn [pa_str_ctor AD PmLayoutU.ADDR_U].
set (P1 := fun a => sp - 48 <= a < sp \/ o <= a < o + 24).
assert (AG1 : forall a, 0 <= a < 2 ^ 64 -> ~ P1 a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha NP. unfold P1 in NP. apply FRZ; [exact Ha| |]; intros X; apply NP; lia. }
assert (CW1 : forall a, P1 a -> PMK.cwr L LB a).
{ intros a Ha. apply (PMK.cwr_stack L LB M sp (12288 + 2048 * 0) a STK). unfold P1 in Ha. lia. }
assert (DEC1 : forall a, {P1 a} + {~ P1 a}) by (intros a; unfold P1; apply PMK.or_dec; apply PMK.rng_dec).
apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x34488 R1 0xaa5b8 M1 P1 K HH Mh Ml ltac:(lia) MS MG AG1 CW1 DEC1).
intros HH1.
destruct (PMCPS.memmove_run fx1 R1 M1 (o + 1) ptr n 214296) as (R2 & M2 & MS2 & MG2 & FR2 & DEF2 & KS2 & B10b).
{ exact B10. } { rewrite (KS 11%nat) by PMK.inl. exact A11. } { rewrite (KS 12%nat) by PMK.inl. exact A12. } { exact B1. }
{ split; [lia| reflexivity]. } { lia. } { lia. } { lia. } { lia. } { lia. } { right. lia. }
{ apply (L5.writable_grows RSEGS M M1 _ _ MG). apply (L5.writable_sub RSEGS M o 24); [exact WRO| lia| lia]. }
{ apply (L5.defined_grows M M1 _ _ MG). exact PDEF. }
assert (AG2 : forall a, 0 <= a < 2 ^ 64 -> ~ P1 a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
{ intros a Ha NP. apply FR2; [exact Ha|]. unfold P1 in NP. lia. }
assert (STK1 : L5C.stk (hl_sptop L) M1 sp (12288 + 2048 * 0)) by (apply (L5C.stk_grows _ M M1 _ _ MG STK)).
apply (PMK.spiece RSEGS L HI KL HIok LB cr M1 model fx1 fx1 R1 0xaa5b8 R2 214296 M2 P1 K HH1 Mh Ml ltac:(lia) MS2 MG2 AG2 CW1 DEC1).
intros HH2.
assert (AGf : forall a n0, sp - 48 <= a -> a + n0 <= sp -> L5C.agree_on M1 M2 a n0).
{ intros a n0 H1 H2 i Hi. apply FR2; lia. }
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 1))) as V1. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 8))) as V8.
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 9))) as V9. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 18))) as V18.
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 19))) as V19. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 20))) as V20.
change (bv_modulus 64) with (2 ^ 64) in *.
assert (T8 : L5.u64_at RSEGS M2 (sp - 8) (bv_unsigned (getr R (PMK.reg 1)))) by (apply (L5C.u64_at_agree RSEGS M1 M2); [apply AGf; lia|lia|lia|exact S8]).
assert (T16 : L5.u64_at RSEGS M2 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))) by (apply (L5C.u64_at_agree RSEGS M1 M2); [apply AGf; lia|lia|lia|exact S16b]).
assert (T24 : L5.u64_at RSEGS M2 (sp - 24) (bv_unsigned (getr R (PMK.reg 9)))) by (apply (L5C.u64_at_agree RSEGS M1 M2); [apply AGf; lia|lia|lia|exact S24]).
assert (T32 : L5.u64_at RSEGS M2 (sp - 32) (bv_unsigned (getr R (PMK.reg 18)))) by (apply (L5C.u64_at_agree RSEGS M1 M2); [apply AGf; lia|lia|lia|exact S32]).
assert (T40 : L5.u64_at RSEGS M2 (sp - 40) (bv_unsigned (getr R (PMK.reg 19)))) by (apply (L5C.u64_at_agree RSEGS M1 M2); [apply AGf; lia|lia|lia|exact S40]).
assert (T48 : L5.u64_at RSEGS M2 (sp - 48) (bv_unsigned (getr R (PMK.reg 20)))) by (apply (L5C.u64_at_agree RSEGS M1 M2); [apply AGf; lia|lia|lia|exact S48]).
assert (WR2 : L5.writable RSEGS M2 (sp - 48) 48).
{ apply (L5.writable_grows RSEGS M1 M2 _ _ MG2). apply (L5.writable_grows RSEGS M M1 _ _ MG). apply (L5.writable_sub RSEGS M (sp - (12288 + 2048 * 0)) (12288 + 2048 * 0)); [exact WR0|lia|lia]. }
assert (WT2 : L5.writable RSEGS M2 (o + 1 + n) 1).
{ apply (L5.writable_grows RSEGS M1 M2 _ _ MG2). apply (L5.writable_grows RSEGS M M1 _ _ MG). apply (L5.writable_sub RSEGS M o 24); [exact WRO|lia|lia]. }
pose proof (PMSTUP.uscT_conc fx1 R2 M2 (fun j => match j with 2%nat => sp | 34%nat => n | 39%nat => o + 1
| 44%nat => bv_unsigned (getr R (PMK.reg 1)) | 45%nat => bv_unsigned (getr R (PMK.reg 8)) | 46%nat => bv_unsigned (getr R (PMK.reg 9))
| 47%nat => bv_unsigned (getr R (PMK.reg 18)) | 48%nat => bv_unsigned (getr R (PMK.reg 19)) | 49%nat => bv_unsigned (getr R (PMK.reg 20)) | _ => 0 end)) as PT.
cbn beta iota in PT.
assert (R2sp : getr R2 (PMK.reg 2) = Z_to_bv 64 (sp - 48)) by (rewrite (KS2 2%nat) by PMK.inl; exact B2).
assert (R2s0 : getr R2 (PMK.reg 8) = Z_to_bv 64 n) by (rewrite (KS2 8%nat) by PMK.inl; exact B8).
assert (R2s3 : getr R2 (PMK.reg 19) = Z_to_bv 64 (o + 1)) by (rewrite (KS2 19%nat) by PMK.inl; exact B19).
PMK.feed PT ltac:(first [ PMK.sc ]).
PMK.pvz_hg ltac:(idtac; destruct PT as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & FR3 & FRZ3 & MS3 & KS3 & E1 & E2 & E8 & E9 & E10 & E18 & E19 & E20 & CT)); PMK.pvz_clrT.
assert (AG3 : forall a, 0 <= a < 2 ^ 64 -> ~ P1 a -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
{ intros a Ha NP. apply FRZ3; [exact Ha|]. unfold P1 in NP. lia. }
apply (PMK.spiece RSEGS L HI KL HIok LB cr M2 model fx1 fx3 R2 214296 R3 0x34544 M3 P1 K HH2 Mh Ml ltac:(lia) MS3 MG3 AG3 CW1 DEC1).
intros HH3.
eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx3 R3 M3 0x34544 (ltac:(oW' 0x34544%Z)) r (ltac:(oF' 0x34544%Z)) ltac:(reflexivity) (ltac:(oD' 0x34544%Z)))|].
- rewrite E1, Z_to_bv_bv_unsigned. exact Rra.
- exact RA1.
- exact RA2.
- assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ P1 a -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha NP. rewrite (AG3 a Ha NP), (AG2 a Ha NP). apply AG1; assumption. }
assert (MG03 : mem_grows M M3) by (intros x Hx; apply MG3, MG2, MG; exact Hx).
apply (KONT fx3 R3 M3 model (PM.VShort n) cr).
+ apply PMK.preserved_by_index. intros k Hk. unfold PMK.cs_all in Hk. cbn in Hk.
assert (CH : forall j, In j PMSTUP.KS_uscT -> In j L5K.CS -> In j PMSTUP.KS_uscS -> getr R3 (PMK.reg j) = getr R (PMK.reg j)).
{ intros j K1 K2 K3. rewrite (KS3 j K1), (KS2 j K2). apply KS. exact K3. }
destruct Hk as [<-|Hk]; [rewrite E2, Rsp; reflexivity|].
destruct Hk as [<-|Hk]; [apply CH; PMK.inl|].
destruct Hk as [<-|Hk]; [apply CH; PMK.inl|].
destruct Hk as [<-|Hk]; [rewrite E8; apply Z_to_bv_bv_unsigned|].
destruct Hk as [<-|Hk]; [rewrite E9; apply Z_to_bv_bv_unsigned|].
destruct Hk as [<-|Hk]; [rewrite E18; apply Z_to_bv_bv_unsigned|].
destruct Hk as [<-|Hk]; [rewrite E19; apply Z_to_bv_bv_unsigned|].
destruct Hk as [<-|Hk]; [rewrite E20; apply Z_to_bv_bv_unsigned|].
repeat (destruct Hk as [<-|Hk]; [apply CH; PMK.inl|]). destruct Hk.
+ split; [apply (L5.defined_grows M M3 _ _ MG03); exact DEFO|]. split; [exact I|]. split; [lia|].
apply (L5C.u8_at_agree RSEGS M2 M3); [|lia|lia|]. { intros i Hi. apply FRZ3; lia. }
apply (L5C.u8_at_agree RSEGS M1 M2); [|lia|lia|exact C0]. intros i Hi. apply FR2; lia.
+ reflexivity.
+ intros _. reflexivity.
+ intros X. lia.
+ apply PMK.hpres_of.
* apply (PMK.ek_piece_in RSEGS L KL LB sp (12288 + 2048 * 0) [(o, 24)] M M3 P1 AG STK LBhi).
intros a [X|X]; [left; lia| right; apply PMK.inW_here; exact X].
* apply (L5.defined_grows M M3 _ _ MG03). exact SW.
* apply PMK.dk_grows. exact MG03.
+ apply credit_keep_none; unfold PM.cost1; cbn [fst snd]; pose proof (ly_kpm L LY); pose proof (ly_bov L LY); lia.
+ apply L5C.model_but_vm_refl.
+ cbn [PM.vs_own app]. exact HH3.
Qed.
Definition head_ok (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (o ptr n sp : Z) (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) : Prop :=
mem_grows M M1
/\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (sp - 48 <= i < sp - 48 + 48) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
/\ msteps RSEGS (@mkst fx R (Z_to_bv 64 0x34488) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 0xaf0ec) M1 (seg_rom RSEGS))
/\ (forall k, In k [3; 4; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (PMK.reg k) = getr R (PMK.reg k))
/\ getr R1 (PMK.reg 1) = Z_to_bv 64 214260 /\ getr R1 (PMK.reg 2) = Z_to_bv 64 (sp - 48)
/\ getr R1 (PMK.reg 8) = Z_to_bv 64 n /\ getr R1 (PMK.reg 9) = Z_to_bv 64 ptr /\ getr R1 (PMK.reg 10) = Z_to_bv 64 (PMSP.str_count n)
/\ getr R1 (PMK.reg 18) = Z_to_bv 64 o /\ getr R1 (PMK.reg 20) = Z_to_bv 64 (PMSP.str_count n)
/\ L5.u64_at RSEGS M1 (sp - 48) (bv_unsigned (getr R (PMK.reg 20))) /\ L5.u64_at RSEGS M1 (sp - 40) (bv_unsigned (getr R (PMK.reg 19)))
/\ L5.u64_at RSEGS M1 (sp - 32) (bv_unsigned (getr R (PMK.reg 18))) /\ L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R (PMK.reg 9)))
/\ L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (PMK.reg 8))) /\ L5.u64_at RSEGS M1 (sp - 8) (bv_unsigned (getr R (PMK.reg 1))).
Lemma in9 : ltac2:(TCodec.tc2 tcn__PmStrU "Q='4'5%211&QCr1(2u3u4uEuFuGuHuIuJuK(6%11?%<3@31%=3A51%>3B71%?3C91%@3D;1%A3E=1%B3F?1%C3GA1%D3HC1%G3IF1'='1&QD&QBr2%211r3%53Q121(;%93821p0;1pT4Q51r4%Q53Q791p0?1pT4Q91p051pQ6Q:1").
Proof. intros KS. intros H k Hk. apply L5K.In_of_mem. apply H. exact Hk. Qed.
Ltac in9_tac := apply in9; intros k Hk; cbn in Hk; repeat (destruct Hk as [<-|Hk]; [vm_compute; reflexivity|]); destruct Hk.
Lemma in9_H23 : ltac2:(TCodec.tc2 tcn__PmStrU "N'5&QCr1(2u3u4uEuFuGuHuIuJuK(6%11>%<3?31%=3@51%>3A71%?3B91%@3C;1%A3D=1%B3E?1%C3FA1%D3GC1%G3HF1r2&Q9%J3K21p041pT4M1"). Proof. in9_tac. Qed.
Lemma in9_Hg : ltac2:(TCodec.tc2 tcn__PmStrU "N'5&QCr1(2u3u4uEuFuGuHuIuJuK(6%11>%<3?31%=3@51%>3A71%?3B91%@3C;1%A3D=1%B3E?1%C3FA1%D3GC1%G3HF1r2&Q:%J3K21p041pT4M1"). Proof. in9_tac. Qed.
Lemma in9_N : ltac2:(TCodec.tc2 tcn__PmStrU "N'5&QCr1(2u3u4uEuFuGuHuIuJuK(6%11>%<3?31%=3@51%>3A71%?3B91%@3C;1%A3D=1%B3E?1%C3FA1%D3GC1%G3HF1r2&Q;%J3K21p041pT4M1"). Proof. in9_tac. Qed.
Lemma in9_T : ltac2:(TCodec.tc2 tcn__PmStrU "N'5&QCr1(2u3u4uEuFuGuHuIuJuK(6%11>%<3?31%=3@51%>3A71%?3B91%@3C;1%A3D=1%B3E?1%C3FA1%D3GC1%G3HF1r2&Q<%J3K21p041pT4M1"). Proof. in9_tac. Qed.
Lemma in9_CS : ltac2:(TCodec.tc2 tcn__PmStrU "N'5&QCr1(2u3u4uEuFuGuHuIuJuK(6%11>%<3?31%=3@51%>3A71%?3B91%@3C;1%A3D=1%B3E?1%C3FA1%D3GC1%G3HF1r2&N%J3K21p041pT4M1"). Proof. in9_tac. Qed.
Lemma in9_cs : ltac2:(TCodec.tc2 tcn__PmStrU "N'5&QCr1(2u3u4uEuFuGuHuIuJuK(6%11>%<3?31%=3@51%>3A71%?3B91%@3C;1%A3D=1%B3E?1%C3FA1%D3GC1%G3HF1r2&Q6%J3K21p041pT4M1"). Proof. in9_tac. Qed.
Lemma head_long : ltac2:(TCodec.tc2 tcn__PmStrU "T1'Q>&Fy5'R8yR0%211%5241'7y8%611%311p061'@'<&QF+Gr2%3221&QG&QJ+2+J%3221%5271%;271zr4%=221+R0%:291%<241%B241'=&Q?r8&R7&QIu2%211%42Q51%7261r3%72Q61%;3Q631r9u:%:11%<2Q=1%?241r7%?2Q>1%C3Q>31r:u;%B11%D2QE1%G241%I3QD17r;u<%H11%J2QK1%M241%O3QJ1=+SoomohPPQ@%QC21@+TPPPPPPPP0%QE2B1%QG231&QH+@%22Q51%Q83QL1Q?&Q0&Q@r=&QK+Q@%22Q21%645412%R22L5&QEr>+H%3221%R721Cr?+8%C221%QI3R=1R0rAr@%C4B219'>&Q8rGrFrErDrCrBr1%8:765432<QMRF1qQBRL1%;2RM1qQFS31%=2S41qT2S;1%?2S<1p0A1p0E1p0J1p0Q01p0Q21p0Q:1p0Q?1p0QE1p0QL1p0R31p0R<1p0RI1p0S11pT>S>1pT8S?1pT<S@1pT:SA1pQ@SC1pQDSI1pT0T01").
Proof. intros fx R M o ptr n sp.
intros Hn Hp Rsp A10 A11 A12 Hsp S16 WR0 Hspo Hotop Ho8 WRO.
destruct (Z.eq_dec n 23) as [->|NE].
- cfeed P (PMSTUP.uscH23_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 35%nat => ptr | _ => 0 end)) ltac:(first [ PMK.sc ]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ & MS & KS & B1 & B2 & B8 & B9 & B10 & B11 & B18 & B20 & S48 & S40 & S32 & S24 & S16b & S8)); PMK.pvz_clrT.
exists fx1, R1, M1. unfold head_ok. change (PMSP.str_count 23) with 26.
split; [exact MG|]. split; [exact FRZ|]. split; [exact MS|]. split; [intros k Hk; apply KS; apply in9_H23; exact Hk|].
repeat (split; [assumption|]). assumption.
- assert (E : PMSP.str_count n = 8 * (n / 8) + 8).
{ unfold PMSP.str_count. destruct (Z.eqb_spec n 23); [Lia.lia|]. apply PMF.lor7. Lia.lia. }
pose proof (PMF.lor7 n ltac:(Lia.lia)) as E7. pose proof (cap_facts n Hn) as (F1 & F2 & _ & _). rewrite E in F1, F2.
cfeed P (PMSTUP.uscHg_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => n | 35%nat => ptr | _ => 0 end)) ltac:(first [ PMK.sc | Lia.lia ]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ & MS & KS & B1 & B2 & B8 & B9 & B10 & B11 & B18 & B20 & S48 & S40 & S32 & S24 & S16b & S8)); PMK.pvz_clrT.
exists fx1, R1, M1. unfold head_ok. rewrite E.
split; [exact MG|]. split; [exact FRZ|]. split; [exact MS|]. split; [intros k Hk; apply KS; apply in9_Hg; exact Hk|].
repeat (split; [assumption|]). assumption.
Qed.
Lemma case_long : ltac2:(TCodec.tc2 tcn__PmStrU ">&Q4vQAvCvA%43321&Q7'@&QF+Gr1%3221qT851%711p091").
Proof.
intros OPNEW fx R M model K LB cr o ptr n sp r Hc HH MOK K0 ENT A10 A11 A12 Hn Hspo Hotop Ho8 DEFO SRCB CRED KONT.
pose proof MOK as (Mh & Ml & Mm).
destruct ENT as (Rra & (RA1 & RA2) & Rsp & Rgp & Rtp & STK).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl12 in A12.
pose proof (L5C.stk_floor _ _ _ _ STK) as FL. pose proof (L5C.stk_writable RSEGS _ M sp _ STK) as WR0.
pose proof STK as (S16 & SB & SC & SD & SW). unfold PMSP.pm_scr in *.
assert (WRO : L5.writable RSEGS M o 24) by (apply (L5C.writable_of_defined RSEGS M o 24 DEFO); lia).
pose proof (PMCKU.lb_hi L HI HIok LB cr M _ HH) as LBhi.
destruct (src_facts LB cr M _ ptr n HH ltac:(lia) SRCB) as (PT0 & PT1 & PDEF & (Bs & ms & INs & Bs1 & Bs2)).
assert (CEIL : hl_ceil L <= sp - 12288) by (unfold hl_ceil; lia).
pose proof (cap_facts n ltac:(lia)) as (CF1 & CF2 & CF3 & CF4). set (cap := PMSP.str_count n) in *.
pose proof (ly_kpm L LY) as HK. pose proof (ly_bov L LY) as HB.
destruct (head_long fx R M o ptr n sp ltac:(lia) ltac:(lia) Rsp A10 A11 A12 ltac:(lia) S16
ltac:(apply (L5.writable_sub RSEGS M (sp - (12288 + 2048 * 0)) (12288 + 2048 * 0)); [exact WR0|lia|lia]) Hspo ltac:(lia) Ho8 WRO)
as (fx1 & R1 & M1 & MG & FRZ & MS & KS & B1 & B2 & B8 & B9 & B10 & B18 & B20 & S48 & S40 & S32 & S24 & S16b & S8).
fold cap in B10, B20.
unfold PMSP.cfg. cbn [pa_str_ctor AD PmLayoutU.ADDR_U].
set (P1 := fun a => sp - 48 <= a < sp).
assert (AG1 : forall a, 0 <= a < 2 ^ 64 -> ~ P1 a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha NP. unfold P1 in NP. apply FRZ; [exact Ha|]. lia. }
apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x34488 R1 0xaf0ec M1 P1 K HH Mh Ml ltac:(lia) MS MG AG1).
{ intros a Ha. apply (PMK.cwr_stack L LB M sp (12288 + 2048 * 0) a STK). unfold P1 in Ha. lia. }
{ intros a. unfold P1. apply PMK.rng_dec. }
intros HH1.
assert (STK1 : L5C.stk (hl_sptop L) M1 sp (12288 + 2048 * 0)) by (apply (L5C.stk_grows _ M M1 _ _ MG STK)).
assert (EK01 : PMK.ek L LB sp (12288 + 2048 * 0) [(o, 24)] M M1).
{ apply (PMK.ek_piece_in RSEGS L KL LB sp (12288 + 2048 * 0) [(o, 24)] M M1 P1 AG1 STK LBhi). intros a X. left. unfold P1 in X. lia. }
assert (SCn : 0 <= PMSP.OPNEW_SCR) by (unfold PMSP.OPNEW_SCR; lia).
assert (STKn : L5C.stk (hl_sptop L) M1 (sp - 48) PMSP.OPNEW_SCR).
{ apply (PMK.stk_call L M1 sp (12288 + 2048 * 0) (sp - 48) PMSP.OPNEW_SCR STK1); [lia| unfold PMSP.OPNEW_SCR; lia| exact SCn|].
replace (sp - 48) with (sp + (-3) * 16) by lia. rewrite Z.mod_add by lia. exact S16. }
unfold PMU.opnew_spec, PMSP.opnew_spec in OPNEW. cbn [pa_opnew pa_tp AD PmLayoutU.ADDR_U] in OPNEW.
apply (OPNEW fx1 R1 M1 model K LB cr cap (sp - 48) 214260 HH1 MOK K0).
{ rewrite L5K.rl10. exact B10. } { lia. }
{ destruct CRED as (CR1 & CR2). unfold PM.cost1 in CR1, CR2. cbn [fst snd] in CR1, CR2. unfold credit_ok. lia. }
{ rewrite L5K.rl1. exact B1. } { split; [lia| reflexivity]. } { rewrite L5K.rl2. exact B2. }
{ rewrite L5K.rl4. rewrite (KS 4%nat) by (cbn; auto). exact Rtp. } { exact STKn. }
intros fx2 R2 M2 model2 B A10b RP2 FRESH HP2 MB2 HH2. rewrite L5K.rl10 in A10b.
destruct (L5C.fresh_block_bounds L LB M2 B cap FRESH) as (FB0 & FBH & FB16 & _ & FBC).
destruct FRESH as (_ & FAP & FDEF).
pose proof (L5C.halted_but_vm _ _ MB2) as Mh2. rewrite Mh in Mh2. pose proof (L5C.lazy_but_vm _ _ MB2) as Ml2. rewrite Ml in Ml2.
assert (EKo : PMK.ek L LB (sp - 48) PMSP.OPNEW_SCR [] M1 M2) by (apply (PMK.ek_of_hpres L); exact HP2).
assert (BR : PMFR.brange L LB) by (apply (PMFR.brange_of_heap L HI HIok LB LB cr M _ HH (incl_refl _))).
assert (WHI0 : forall a, PMK.inW [] a -> sp - 48 <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a X; destruct (PMFR.inW_nil a X)).
assert (KEEP8 : forall a v, sp - 48 <= a -> a + 8 <= 2 ^ 64 -> L5.u64_at RSEGS M1 a v -> L5.u64_at RSEGS M2 a v).
{ intros a v H1 H2 C. apply (PMFR.u64_keep RSEGS L KL LB (sp - 48) PMSP.OPNEW_SCR [] M1 M2 EKo STKn SCn a v H1 H2); [|exact C]. intros i _. apply PMFR.inW_nil. }
assert (STK2 : L5C.stk (hl_sptop L) M2 sp (12288 + 2048 * 0)).
{ apply (PMK.stk_after RSEGS L KL LB M1 M2 sp (12288 + 2048 * 0) (sp - 48) PMSP.OPNEW_SCR [] STK1 HP2); [lia| unfold PMSP.OPNEW_SCR; lia| exact SCn]. }
assert (DEFO2 : L5.defined M2 o 24).
{ apply (PMFR.defined_keep RSEGS L KL LB (sp - 48) PMSP.OPNEW_SCR [] M1 M2 EKo STKn SCn o 24); [lia|lia| intros i _; apply PMFR.inW_nil|]. apply (L5.defined_grows M M1 _ _ MG). exact DEFO. }
assert (PDEF2 : L5.defined M2 ptr n).
{ apply (L5C.defined_agree M1 M2 ptr n); [|apply (L5.defined_grows M M1 _ _ MG); exact PDEF].
apply (L5C.agree_on_sub M1 M2 Bs ms); [|lia|lia]. apply (PMFR.ag_block RSEGS L KL LB (sp - 48) PMSP.OPNEW_SCR [] M1 M2 EKo STKn SCn BR WHI0 Bs ms INs). }
assert (EK12 : PMK.ek L LB sp (12288 + 2048 * 0) [(o, 24)] M1 M2).
{ apply (PMK.ek_callee_in RSEGS L KL LB LB sp (12288 + 2048 * 0) (sp - 48) PMSP.OPNEW_SCR [(o, 24)] [] M1 M1 M2 HP2 (incl_refl _)); [unfold PMSP.OPNEW_SCR; lia| lia| exact STK1| exact LBhi|].
intros a X. destruct (PMFR.inW_nil a X). }
pose proof (L5C.stk_writable RSEGS _ M2 sp _ STK2) as WR2.
assert (WRO2 : L5.writable RSEGS M2 o 24) by (apply (L5C.writable_of_defined RSEGS M2 o 24 DEFO2); lia).
assert (R2sp : getr R2 (PMK.reg 2) = Z_to_bv 64 (sp - 48)) by (rewrite (PMK.cs_of_preserved R1 R2 2 RP2 ltac:(PMK.inl)); exact B2).
assert (R2s0 : getr R2 (PMK.reg 8) = Z_to_bv 64 n) by (rewrite (PMK.cs_of_preserved R1 R2 8 RP2 ltac:(PMK.inl)); exact B8).
assert (R2s1 : getr R2 (PMK.reg 9) = Z_to_bv 64 ptr) by (rewrite (PMK.cs_of_preserved R1 R2 9 RP2 ltac:(PMK.inl)); exact B9).
assert (R2s2 : getr R2 (PMK.reg 18) = Z_to_bv 64 o) by (rewrite (PMK.cs_of_preserved R1 R2 18 RP2 ltac:(PMK.inl)); exact B18).
assert (R2s4 : getr R2 (PMK.reg 20) = Z_to_bv 64 cap) by (rewrite (PMK.cs_of_preserved R1 R2 20 RP2 ltac:(PMK.inl)); exact B20).
cfeed PN (PMSTUP.uscN_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => n | 35%nat => ptr | 36%nat => B | 37%nat => cap | _ => 0 end)) ltac:(first [ PMK.sc ]).
PMK.pvz_hg ltac:(idtac; destruct PN as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & FR3 & FRZ3 & MS3 & KS3 & D1 & D11 & D12 & D19 & D20 & O16 & O8 & O0)); PMK.pvz_clrT.
set (P3 := fun a => o <= a < o + 24).
assert (AG3 : forall a, 0 <= a < 2 ^ 64 -> ~ P3 a -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
{ intros a Ha NP. unfold P3 in NP. apply FRZ3; [exact Ha|]. lia. }
set (LB2 := (B, cap) :: LB) in *.
apply (PMK.spiece RSEGS L HI KL HIok LB2 (debit L cr cap) M2 model2 fx2 fx3 R2 214260 R3 0xaa5b8 M3 P3 K HH2 Mh2 Ml2 ltac:(lia) MS3 MG3 AG3).
{ intros a Ha. apply (PMK.cwr_stack L LB2 M2 sp (12288 + 2048 * 0) a STK2). unfold P3 in Ha. lia. }
{ intros a. unfold P3. apply PMK.rng_dec. }
intros HH3.
assert (EK23 : PMK.ek L LB sp (12288 + 2048 * 0) [(o, 24)] M2 M3).
{ apply (PMK.ek_piece_in RSEGS L KL LB sp (12288 + 2048 * 0) [(o, 24)] M2 M3 P3 AG3 STK2 LBhi). intros a X. right. apply PMK.inW_here. exact X. }
destruct (L5C.blocks_apart_in B cap LB Bs ms FAP INs) as [AP|AP].
all: destruct (PMCPS.memmove_run fx3 R3 M3 B ptr n 214296) as (R4 & M4 & MS4 & MG4 & FR4 & DEF4 & KS4 & D10);
[ rewrite (KS3 10%nat) by PMK.inl; exact A10b | exact D11 | exact D12 | exact D1 | split; [lia| reflexivity] | lia | lia | lia | lia | lia | lia
| apply (L5.writable_grows RSEGS M2 M3 _ _ MG3); apply (L5C.writable_of_defined RSEGS M2 B n); [apply (L5.defined_sub M2 B cap); [exact FDEF|lia|lia]|lia|lia]
| apply (L5.defined_grows M2 M3 _ _ MG3); exact PDEF2 | ].
all: set (P4 := fun a => B <= a < B + cap).
all: assert (AG4 : forall a, 0 <= a < 2 ^ 64 -> ~ P4 a -> M4 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)) by (intros a Ha NP; unfold P4 in NP; apply FR4; [exact Ha| lia]).
all: assert (CW4 : forall a, P4 a -> PMK.cwr L LB2 a) by (intros a Ha; apply (PMK.cwr_block L LB2 B cap a); [left; reflexivity| exact Ha]).
all: assert (DEC4 : forall a, {P4 a} + {~ P4 a}) by (intros a; unfold P4; apply PMK.rng_dec).
all: apply (PMK.spiece RSEGS L HI KL HIok LB2 (debit L cr cap) M3 model2 fx3 fx3 R3 0xaa5b8 R4 214296 M4 P4 K HH3 Mh2 Ml2 ltac:(lia) MS4 MG4 AG4 CW4 DEC4).
all: intros HH4.
all:
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 1))) as V1; pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 8))) as V8;
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 9))) as V9; pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 18))) as V18;
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 19))) as V19; pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 20))) as V20;
change (bv_modulus 64) with (2 ^ 64) in *.
all: assert (AGf : forall a v, sp - 48 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M2 a v -> L5.u64_at RSEGS M4 a v)
by (intros a v H1 H2 C; apply (L5C.u64_at_agree RSEGS M3 M4); [intros i Hi; apply AG4; [lia| unfold P4; lia]|lia|lia|];
apply (L5C.u64_at_agree RSEGS M2 M3); [intros i Hi; apply AG3; [lia| unfold P3; lia]|lia|lia| exact C]).
all: pose proof (AGf (sp - 8) _ ltac:(lia) ltac:(lia) (KEEP8 (sp - 8) _ ltac:(lia) ltac:(lia) S8)) as T8;
pose proof (AGf (sp - 16) _ ltac:(lia) ltac:(lia) (KEEP8 (sp - 16) _ ltac:(lia) ltac:(lia) S16b)) as T16;
pose proof (AGf (sp - 24) _ ltac:(lia) ltac:(lia) (KEEP8 (sp - 24) _ ltac:(lia) ltac:(lia) S24)) as T24;
pose proof (AGf (sp - 32) _ ltac:(lia) ltac:(lia) (KEEP8 (sp - 32) _ ltac:(lia) ltac:(lia) S32)) as T32;
pose proof (AGf (sp - 40) _ ltac:(lia) ltac:(lia) (KEEP8 (sp - 40) _ ltac:(lia) ltac:(lia) S40)) as T40;
pose proof (AGf (sp - 48) _ ltac:(lia) ltac:(lia) (KEEP8 (sp - 48) _ ltac:(lia) ltac:(lia) S48)) as T48.
all: assert (WR4 : L5.writable RSEGS M4 (sp - 48) 48)
by (apply (L5.writable_grows RSEGS M3 M4 _ _ MG4); apply (L5.writable_grows RSEGS M2 M3 _ _ MG3); apply (L5.writable_sub RSEGS M2 (sp - (12288 + 2048 * 0)) (12288 + 2048 * 0)); [exact WR2|lia|lia]).
all: assert (WT4 : L5.writable RSEGS M4 (B + n) 1)
by (apply (L5.writable_grows RSEGS M3 M4 _ _ MG4); apply (L5.writable_grows RSEGS M2 M3 _ _ MG3); apply (L5C.writable_of_defined RSEGS M2 (B + n) 1); [apply (L5.defined_sub M2 B cap); [exact FDEF|lia|lia]|lia|lia]).
all: assert (R4sp : getr R4 (PMK.reg 2) = Z_to_bv 64 (sp - 48)) by (rewrite (KS4 2%nat) by PMK.inl; rewrite (KS3 2%nat) by PMK.inl; exact R2sp).
all: assert (R4s0 : getr R4 (PMK.reg 8) = Z_to_bv 64 n) by (rewrite (KS4 8%nat) by PMK.inl; rewrite (KS3 8%nat) by PMK.inl; exact R2s0).
all: assert (R4s3 : getr R4 (PMK.reg 19) = Z_to_bv 64 B) by (rewrite (KS4 19%nat) by PMK.inl; exact D19).
all: pose proof (PMSTUP.uscT_conc fx3 R4 M4 (fun j => match j with 2%nat => sp | 34%nat => n | 39%nat => B
| 44%nat => bv_unsigned (getr R (PMK.reg 1)) | 45%nat => bv_unsigned (getr R (PMK.reg 8)) | 46%nat => bv_unsigned (getr R (PMK.reg 9))
| 47%nat => bv_unsigned (getr R (PMK.reg 18)) | 48%nat => bv_unsigned (getr R (PMK.reg 19)) | 49%nat => bv_unsigned (getr R (PMK.reg 20)) | _ => 0 end)) as PT;
cbn beta iota in PT.
all: PMK.feed PT ltac:(first [ PMK.sc ]).
all: PMK.pvz_hg ltac:(idtac; destruct PT as (fx5 & R5 & M5 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG5 & FR5 & FRZ5 & MS5 & KS5 & E1 & E2 & E8 & E9 & E10 & E18 & E19 & E20 & CT)); PMK.pvz_clrT.
all: assert (AG5 : forall a, 0 <= a < 2 ^ 64 -> ~ P4 a -> M5 (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)) by (intros a Ha NP; apply FRZ5; [exact Ha|]; unfold P4 in NP; lia).
all: apply (PMK.spiece RSEGS L HI KL HIok LB2 (debit L cr cap) M4 model2 fx3 fx5 R4 214296 R5 0x34544 M5 P4 K HH4 Mh2 Ml2 ltac:(lia) MS5 MG5 AG5 CW4 DEC4).
all: intros HH5.
all: eapply (L5.cps_of_msteps RSEGS); [exact Mh2| exact Ml2| apply (PMK.ret_to RSEGS fx5 R5 M5 0x34544 (ltac:(oW' 0x34544%Z)) r (ltac:(oF' 0x34544%Z)) ltac:(reflexivity) (ltac:(oD' 0x34544%Z))); [rewrite E1, Z_to_bv_bv_unsigned; exact Rra| exact RA1| exact RA2]|].
all: assert (MG25 : mem_grows M2 M5) by (intros x Hx; apply MG5, MG4, MG3; exact Hx).
all: assert (AG35 : forall a, 0 <= a < 2 ^ 64 -> ~ P4 a -> M5 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)) by (intros a Ha NP; rewrite (AG5 a Ha NP); apply AG4; assumption).
all: assert (EK35 : PMK.ek L LB sp (12288 + 2048 * 0) [(o, 24)] M3 M5)
by (intros a KA; apply AG35; [destruct KA as (X & _); exact X|]; unfold P4; apply (L5C.kept_not_fresh L LB sp (12288 + 2048 * 0) [(o, 24)] a B cap KA FAP FBH FBC LBhi)).
all: apply (KONT fx5 R5 M5 model2 (PM.VLong cap n B) (debit L cr cap)).
all: try (apply PMK.preserved_by_index; intros k Hk; unfold PMK.cs_all in Hk; cbn in Hk;
assert (CH : forall j, In j [3; 4; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R5 (PMK.reg j) = getr R (PMK.reg j))
by (intros j Hj; rewrite (KS5 j (in9_T j Hj)), (KS4 j (in9_CS j Hj)), (KS3 j (in9_N j Hj)), (PMK.cs_of_preserved R1 R2 j RP2 (in9_cs j Hj)); apply KS; exact Hj);
destruct Hk as [<-|Hk]; [rewrite E2, Rsp; reflexivity|];
destruct Hk as [<-|Hk]; [apply CH; cbn; auto|];
destruct Hk as [<-|Hk]; [apply CH; cbn; auto|];
destruct Hk as [<-|Hk]; [rewrite E8; apply Z_to_bv_bv_unsigned|];
destruct Hk as [<-|Hk]; [rewrite E9; apply Z_to_bv_bv_unsigned|];
destruct Hk as [<-|Hk]; [rewrite E18; apply Z_to_bv_bv_unsigned|];
destruct Hk as [<-|Hk]; [rewrite E19; apply Z_to_bv_bv_unsigned|];
destruct Hk as [<-|Hk]; [rewrite E20; apply Z_to_bv_bv_unsigned|];
repeat (destruct Hk as [<-|Hk]; [apply CH; cbn; auto 12|]); destruct Hk).
all: try (assert (KO : forall a v, o <= a -> a + 8 <= o + 24 -> L5.u64_at RSEGS M3 a v -> L5.u64_at RSEGS M5 a v)
by (intros a v H1 H2 C; apply (L5C.u64_at_agree RSEGS M3 M5); [intros i Hi; apply AG35; [lia| unfold P4; lia]|lia|lia|exact C]);
split; [apply (L5.defined_grows M2 M5 _ _ MG25); exact DEFO2|]; split; [exact I|];
split; [apply KO; [lia|lia|exact O0]|]; split; [apply KO; [lia|lia|exact O8]|]; split; [apply KO; [lia|lia|exact O16]|];
split; [lia|]; split; [lia|]; split; [exact CF3|]; split; [apply (L5.defined_grows M2 M5 _ _ MG25); exact FDEF| exact I]).
all: try reflexivity.
all: try (intros X; lia).
all: try (intros _; exists B; reflexivity).
all: try (apply PMK.hpres_of;
[ apply (PMK.ek_trans L LB sp (12288 + 2048 * 0) [(o, 24)] M M1 M5 EK01); apply (PMK.ek_trans L LB sp (12288 + 2048 * 0) [(o, 24)] M1 M2 M5 EK12);
apply (PMK.ek_trans L LB sp (12288 + 2048 * 0) [(o, 24)] M2 M3 M5 EK23 EK35)
| apply (L5.defined_grows M2 M5 _ _ MG25); destruct STK2 as (_ & _ & _ & _ & X); exact X
| apply (PMK.dk_trans L LB sp (12288 + 2048 * 0) M M1 M5); [apply PMK.dk_grows; exact MG|];
apply (PMK.dk_trans L LB sp (12288 + 2048 * 0) M1 M2 M5); [|apply PMK.dk_grows; exact MG25];
apply (PMK.dk_callee L LB LB sp (12288 + 2048 * 0) (sp - 48) PMSP.OPNEW_SCR [] M1 M2 HP2 (incl_refl _)); [unfold PMSP.OPNEW_SCR; lia| lia] ]).
all: try (unfold PMSP.credit_keep, PMSP.cr0, PM.cost1, debit; cbn [fst snd]; lia).
all: try exact MB2.
all: try (cbn [PM.vs_own app]; exact HH5).
Qed.
Theorem str_ctor_ok : ltac2:(TCodec.tc2 tcn__PmStrU "8&Q4vQAvCvA%43321&Q5%13543p031").
Proof.
intros OPNEW. unfold PMU.str_ctor_spec, PMSP.str_ctor_spec.
intros fx R M model K LB cr o ptr n sp r HH MOK K0 ENT A10 A11 A12 Hn.
destruct (Z.eq_dec n 0) as [E0|N0]; [apply (case_zero fx R M model K LB cr o ptr n sp r E0 HH MOK K0 ENT A10 A11 A12 Hn)|].
destruct (Z_le_gt_dec n 22) as [LE|GT].
- apply (case_short fx R M model K LB cr o ptr n sp r ltac:(lia) HH MOK K0 ENT A10 A11 A12 Hn).
- apply (case_long OPNEW fx R M model K LB cr o ptr n sp r ltac:(lia) HH MOK K0 ENT A10 A11 A12 Hn).
Qed.
End Stage.
End PMSTRU.
