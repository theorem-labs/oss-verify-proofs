(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StreamSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit PmLayout PmLayoutU PmModel PmStatics PmSpecs PmSpecsU PmStep PmParStep PmCertKitG PmB10UP PmB10UPz.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmB10U () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmB10U.PMB10U."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmB10U.PMB10U.Loop."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmB10UP.PMB10UP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmB10UPz.PMB10UPZ."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsU.PMU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStep.PMK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.Arith.PeanoNat.Nat."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1bool"; "1length"; "1list"; "1nat"; "1option"; "1true"; "2and"; "2eq"; "2ex"; "3Z"; "0IH"; "0KS"; "0L"; "4bvmap"]; ["0R"; "5KEEP"; "6goal_from"; "5head"; "7KS_ub10B_0"; "7KS_ub10B_1"; "7KS_ub10B_2"; "7KS_ub10B_3"; "7KS_ub10B_4"; "7KS_ub10B_5"; "7KS_ub10B_6"; "7KS_ub10B_7"; "7KS_ub10E_0"; "7KS_ub10E_1"; "7KS_ub10F_0"; "7KS_ub10F_1"]; ["7KS_ub10J"; "8KS_ub10Ez"; "9is_base10_spec"; ":cs_all"; ";FPState"; ";rdn"; "<loaded_segments"; "0SCFG_P"; "=eqb"; ">In"; ">existsb"; ">forallb"; "?add"; "?le"; "?lt"; "?mul"]; ["?of_nat"; "?pow"; "?sub"; "0bs"; "0c"; "0e"; "0fx"; "0j"; "0k"; "0p"; "0sp"; "@Z_to_bv"; "@bv"; "0t"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc. Local Ltac lia := L5FastLia.plia.
Module PMB10U.
Import PMU.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).
Definition KEEP : list nat := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma KEEP_in : ltac2:(TCodec.tc2 tcn__PmB10U "I'4'5%211'9'2&Q;&Q:&Q8r1%211r2%53:21qSB;1&A%93=21(7%=3<21&Q9%13A:5r4%33C:1p031pSBE1p071pLF1").
Proof. intros KS.
intros H k Hk. rewrite forallb_forall in H. specialize (H k Hk). apply existsb_exists in H. destruct H as (x & Hx & E). apply Nat.eqb_eq in E. subst x. exact Hx.
Qed.
Ltac kin := apply KEEP_in; vm_compute; reflexivity.
Lemma k_E0 : ltac2:(TCodec.tc2 tcn__PmB10U ":'5&Q9r1&A%33421r2&L%63721p041pSB91"). Proof. kin. Qed.
Lemma k_Ez : ltac2:(TCodec.tc2 tcn__PmB10U ":'5&Q9r1&A%33421r2&Q1%63721p041pSB91"). Proof. kin. Qed.
Lemma k_E1 : ltac2:(TCodec.tc2 tcn__PmB10U ":'5&Q9r1&A%33421r2&M%63721p041pSB91"). Proof. kin. Qed.
Lemma k_B0 : ltac2:(TCodec.tc2 tcn__PmB10U ":'5&Q9r1&A%33421r2&D%63721p041pSB91"). Proof. kin. Qed.
Lemma k_B1 : ltac2:(TCodec.tc2 tcn__PmB10U ":'5&Q9r1&A%33421r2&E%63721p041pSB91"). Proof. kin. Qed.
Lemma k_B2 : ltac2:(TCodec.tc2 tcn__PmB10U ":'5&Q9r1&A%33421r2&F%63721p041pSB91"). Proof. kin. Qed.
Lemma k_B3 : ltac2:(TCodec.tc2 tcn__PmB10U ":'5&Q9r1&A%33421r2&G%63721p041pSB91"). Proof. kin. Qed.
Lemma k_B4 : ltac2:(TCodec.tc2 tcn__PmB10U ":'5&Q9r1&A%33421r2&H%63721p041pSB91"). Proof. kin. Qed.
Lemma k_B5 : ltac2:(TCodec.tc2 tcn__PmB10U ":'5&Q9r1&A%33421r2&I%63721p041pSB91"). Proof. kin. Qed.
Lemma k_B6 : ltac2:(TCodec.tc2 tcn__PmB10U ":'5&Q9r1&A%33421r2&J%63721p041pSB91"). Proof. kin. Qed.
Lemma k_B7 : ltac2:(TCodec.tc2 tcn__PmB10U ":'5&Q9r1&A%33421r2&K%63721p041pSB91"). Proof. kin. Qed.
Lemma k_J : ltac2:(TCodec.tc2 tcn__PmB10U ":'5&Q9r1&A%33421r2&Q0%63721p041pSB91"). Proof. kin. Qed.
Lemma k_F0 : ltac2:(TCodec.tc2 tcn__PmB10U ":'5&Q9r1&A%33421r2&N%63721p041pSB91"). Proof. kin. Qed.
Lemma k_F1 : ltac2:(TCodec.tc2 tcn__PmB10U ":'5&Q9r1&A%33421r2&O%63721p041pSB91"). Proof. kin. Qed.
Lemma k_cs : ltac2:(TCodec.tc2 tcn__PmB10U ":'5&Q9r1&Q3%33421r2&A%63721p041pSB91"). Proof. intros k Hk. apply L5K.In_of_mem. unfold PMK.cs_all in Hk. cbn in Hk. repeat (destruct Hk as [<-|Hk]; [reflexivity|]). destruct Hk. Qed.
Lemma table_all : forallb (fun k => match rdn RSEGS (fun _ => None) (Z_to_bv 64 (80368 + 4 * Z.of_nat k)) 4 with Some bs => Nat.eqb (length bs) 4 | None => false end)
(seq 0 13) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma table_ok : ltac2:(TCodec.tc2 tcn__PmB10U "QA';'8&Q=zr1%3221&Q>+=%2241%8241':'4'QLy8%211%411'9'6%113&Q5&Q6yR0%:11(0%11:q031&QK&Q<+R^_@&Q?+4r3%3221%6251%82=1u4%A4@;21(1%12GQ2%G3E31'5&3%12LQ6%K3318%Q;251qS8N1%Q42O1p0Q61pSBQ@1").
Proof. intros k.
intros Hk. pose proof table_all as T. rewrite forallb_forall in T. specialize (T (Z.to_nat k) ltac:(apply in_seq; lia)).
rewrite Z2Nat.id in T by lia. destruct (rdn RSEGS (fun _ => None) (Z_to_bv 64 (80368 + 4 * k)) 4) as [bs|]; [|discriminate].
exists bs. split; [reflexivity| apply Nat.eqb_eq; exact T].
Qed.
Definition head (R : bvmap 5 word) (sp c e t : Z) : Prop :=
getr R (reg 2) = Z_to_bv 64 sp /\ getr R (reg 5) = Z_to_bv 64 80368 /\ getr R (reg 6) = Z_to_bv 64 c /\ getr R (reg 7) = Z_to_bv 64 t
/\ getr R (reg 10) = Z_to_bv 64 c /\ getr R (reg 11) = Z_to_bv 64 5 /\ getr R (reg 12) = Z_to_bv 64 e /\ getr R (reg 13) = Z_to_bv 64 10
/\ getr R (reg 14) = Z_to_bv 64 2 /\ getr R (reg 15) = Z_to_bv 64 1 /\ getr R (reg 16) = Z_to_bv 64 13 /\ getr R (reg 17) = Z_to_bv 64 8185.
Section Loop.
Variable M : word -> option byte.
Variables (sp p e : Z).
Hypothesis RO : L5.img_clear M 65536 749856.
Hypothesis DEF : L5.defined M p (e - p).
Hypothesis Hsp : 0 <= sp < 2 ^ 64.
Hypothesis Hp : 0 < p.
Hypothesis He : e <= 2 ^ 47.
Hypothesis Hn : e - p < 2 ^ 26.
Definition goal_from (fx : FPState) (R : bvmap 5 word) (pc : Z) : Prop :=
exists fx' R' pc', msteps RSEGS (st fx R pc M) (st fx' R' pc' M) /\ (pc' = 0x37e70 \/ pc' = 0x37e68) /\ (forall k, In k KEEP -> getr R' (reg k) = getr R (reg k)).
Lemma back_edge : ltac2:(TCodec.tc2 tcn__PmB10U "QE';'Q4&?y5'QLyR0%211%5241&Q>r4vQE%3221&Cr3vQJr5r2%5543271'8&Q=z%2218&QA+2+R0%3221%B2=1%9261&Br6+Vo`0%332@1p051p0@1p0G1pSLQ31pQ2M1pS>Q41vQI%D21H%E2IN%G221%N5ML=Q0J+VobL%@3?M1p0B1p041p061pSLQ@1pQ2Q:1pS>QA1pJ>1pS:QD1").
Proof. intros c IH fx R t.
intros Hc (R2 & R5 & R6 & R7 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17) Ht.
cfeed P (PMB10UP.ub10F_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => c | 34%nat => e | 36%nat => t | _ => 0 end)) ltac:(first [ PMK.sc ]).
destruct P as (fx1 & R1 & M1 & MG & FR & FRZ & EX). assert (EM : M1 = M) by (apply functional_extensionality; exact FR). subst M1.
destruct EX as [(MS & KS & LT)|(MS & KS & _ & _ & GE)].
- destruct (IH fx1 R1 t ltac:(lia)) as (fx2 & R2' & pc2 & MS2 & PC2 & KS2); [| exact Ht |].
{ repeat split; (rewrite (KS _) by PMK.inl; assumption). }
exists fx2, R2', pc2. split; [eapply msteps_trans; [exact MS| exact MS2]|]. split; [exact PC2|].
intros k Hk. rewrite (KS2 k Hk). apply KS. apply k_F0. exact Hk.
- exists fx1, R1, 0x37e68. split; [exact MS|]. split; [right; reflexivity|]. intros k Hk. apply KS. apply k_F1. exact Hk.
Qed.
Local Ltac back KSx kx tv c IH' :=
lazymatch goal with
| MS : msteps _ _ (@mkst ?fx1 ?R1 _ _ _) |- goal_from ?fx ?R _ =>
assert (HD1 : head R1 sp (c + 1) e tv) by (repeat split; first [ assumption | (rewrite (KSx _) by PMK.inl; assumption) ]);
destruct (back_edge (c + 1) IH' fx1 R1 tv ltac:(lia) HD1 ltac:(lia))
as (fx2 & R2' & pc2 & MS2 & PC2 & KS2);
exists fx2, R2', pc2; split; [eapply msteps_trans; [exact MS| exact MS2]|]; split; [exact PC2|];
intros k Hk; rewrite (KS2 k Hk); apply KSx; apply kx; exact Hk
end.
Local Ltac done KSx kx :=
lazymatch goal with
| MS : msteps _ _ (@mkst ?fx1 ?R1 _ _ _) |- _ =>
exists fx1, R1, 0x37e70; split; [exact MS|]; split; [left; reflexivity|]; intros k Hk; apply KSx; apply kx; exact Hk
end.
Lemma loop_ms : ltac2:(TCodec.tc2 tcn__PmB10U "QD'5'Q4&?y5'QLyR0%211%5241';'9&Q@r5%211&QBvQEr2%3221%83951'8&Q=vQIr3%3221&Q>%123:%7231&CvQJr4%35B21?8z%<213&QA+2+R0%3221%=281%C261&Br8r7+Vo`0%43321p061p0?1p0D1p0M1pSLQ71pS:Q81pQ2Q:1pS>QA1pS@QC1").
Proof.
induction j as [|j IH]; intros fx R c t Hj Hc HD Ht; [lia|].
assert (IH' : forall fx R t', c + 1 < e -> head R sp (c + 1) e t' -> 0 <= t' < 2 ^ 64 -> goal_from fx R 0x37e00).
{ intros fx' R' t' Hc' HD' Ht'. apply (IH fx' R' (c + 1) t'); [lia| lia| exact HD'| exact Ht']. }
pose proof HD as (R2 & R5 & R6 & R7 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17).
destruct (PMCG.u8_of_defined RSEGS M c ltac:(lia) ltac:(lia) ltac:(apply (L5.defined_sub M p (e - p)); [exact DEF| lia| lia])) as (b & Hb & U).
cfeed P (PMB10UP.ub10B_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => c | 34%nat => e | 36%nat => t | 37%nat => b | _ => 0 end)) ltac:(first [ PMK.sc | exact RO ]).
destruct P as (fx1 & R1 & M1 & MG & FR & FRZ & EX). assert (EM : M1 = M) by (apply functional_extensionality; exact FR). subst M1.
destruct EX as [(MS & KS & X6 & X7 & X10 & _)|[(MS & KS & X6 & X7 & X10 & _)|[(MS & KS & X6 & X10 & _)|[(MS & KS & X5 & X28 & _ & XI & _)|[(MS & KS & _)|[(MS & KS & _)|[(MS & KS & _)|(MS & KS & _)]]]]]]].
- back KS k_B0 5 c IH'.
- back KS k_B1 5 c IH'.
- back KS k_B2 t c IH'.
-
set (idx := Z.land ((b + 18446744073709551571) mod 2 ^ 64) 255) in *.
assert (Hidx : 0 <= idx) by (apply Z.land_nonneg; right; lia).
assert (EA : (((4 * idx) mod 2 ^ 64) + 80368) mod 2 ^ 64 = 80368 + 4 * idx) by (rewrite (Z.mod_small (4 * idx)) by lia; rewrite Z.mod_small by lia; lia).
rewrite EA in X5.
assert (G5 : getr R1 (PMK.reg 7) = Z_to_bv 64 (80368 + 4 * idx)) by (rewrite <- X5; symmetry; apply Z_to_bv_bv_unsigned).
destruct (table_ok idx ltac:(lia)) as (bs & TB & TL).
destruct (PMCG.lw_run RSEGS fx1 R1 M 0x37e34 (ltac:(oW' 0x37e34%Z)) 7%bv 7%bv 0%bv (80368 + 4 * idx) bs (ltac:(oF' 0x37e34%Z)) eq_refl (ltac:(oD' 0x37e34%Z))) as (v & MSl).
{ intros E5. discriminate. } { lia. } { lia. } { exact G5. } { lia. } { change (bv_signed (0%bv : bv 12)) with 0. lia. }
{ change (bv_signed (0%bv : bv 12)) with 0. rewrite Z.add_0_r. rewrite (PMCG.rdn_img RSEGS M 65536 749856 _ 4 RO) by lia. exact TB. }
{ exact TL. }
set (R2x := regupd R1 7%bv v) in MSl.
assert (RU : forall k, k <> 7%nat -> (k < 32)%nat -> getr R2x (PMK.reg k) = getr R1 (PMK.reg k)).
{ intros k Hk Hk32. unfold R2x. replace (7%bv : bv 5) with (PMK.reg 7) by (apply bv_eq; reflexivity). apply PMPX.regupd_other_idx; lia. }
assert (RV : getr R2x (PMK.reg 7) = Z_to_bv 64 (bv_unsigned v)).
{ unfold R2x. replace (7%bv : bv 5) with (PMK.reg 7) by (apply bv_eq; reflexivity). rewrite PMPX.regupd_same_idx by lia. symmetry. apply Z_to_bv_bv_unsigned. }
pose proof (bv_unsigned_in_range 64 v) as Vv. change (bv_modulus 64) with (2 ^ 64) in Vv.
cfeed PJ (PMB10UP.ub10J_conc fx1 R2x M (fun j => match j with 2%nat => sp | 33%nat => c | 34%nat => e | 36%nat => bv_unsigned v | _ => 0 end)) ltac:(first [ exact RV | (rewrite RU by lia; rewrite (KS _) by PMK.inl; assumption) | PMK.sc ]).
destruct PJ as (fx3 & R3 & M3 & _ & FR3 & _ & MS3 & KS3 & J6 & J10). assert (EM : M3 = M) by (apply functional_extensionality; exact FR3). subst M3.
assert (HD3 : head R3 sp (c + 1) e (bv_unsigned v)).
{ unfold head.
split; [rewrite (KS3 2%nat) by PMK.inl; rewrite RU by lia; rewrite (KS 2%nat) by PMK.inl; exact R2|].
split; [rewrite (KS3 5%nat) by PMK.inl; rewrite RU by lia; rewrite (KS 5%nat) by PMK.inl; exact R5|].
split; [exact J6|]. split; [rewrite (KS3 7%nat) by PMK.inl; exact RV|]. split; [exact J10|].
split; [rewrite (KS3 11%nat) by PMK.inl; rewrite RU by lia; rewrite (KS 11%nat) by PMK.inl; exact R11|].
split; [rewrite (KS3 12%nat) by PMK.inl; rewrite RU by lia; rewrite (KS 12%nat) by PMK.inl; exact R12|].
split; [rewrite (KS3 13%nat) by PMK.inl; rewrite RU by lia; rewrite (KS 13%nat) by PMK.inl; exact R13|].
split; [rewrite (KS3 14%nat) by PMK.inl; rewrite RU by lia; rewrite (KS 14%nat) by PMK.inl; exact R14|].
split; [rewrite (KS3 15%nat) by PMK.inl; rewrite RU by lia; rewrite (KS 15%nat) by PMK.inl; exact R15|].
split; [rewrite (KS3 16%nat) by PMK.inl; rewrite RU by lia; rewrite (KS 16%nat) by PMK.inl; exact R16|].
rewrite (KS3 17%nat) by PMK.inl; rewrite RU by lia; rewrite (KS 17%nat) by PMK.inl; exact R17. }
destruct (back_edge (c + 1) IH' fx3 R3 (bv_unsigned v) ltac:(lia) HD3 Vv)
as (fx4 & R4 & pc4 & MS4 & PC4 & KS4).
exists fx4, R4, pc4. split.
{ eapply msteps_trans; [exact MS|]. eapply msteps_trans; [exact MSl|]. eapply msteps_trans; [exact MS3| exact MS4]. }
split; [exact PC4|].
intros k Hk. rewrite (KS4 k Hk), (KS3 k (k_J k Hk)). rewrite RU.
+ apply KS. apply k_B3. exact Hk.
+ intros ->. cbn in Hk. repeat (destruct Hk as [Hk|Hk]; [discriminate Hk|]). destruct Hk.
+ unfold KEEP in Hk. cbn in Hk. repeat (destruct Hk as [<-|Hk]; [lia|]). destruct Hk.
- done KS k_B4.
- done KS k_B5.
- done KS k_B6.
- done KS k_B7.
Qed.
End Loop.
Section Stage.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Hypothesis LY : PMU.layout L.
Theorem is_base10_ok : ltac2:(TCodec.tc2 tcn__PmB10U "4&Q2vQ7v>%3221").
Proof.
unfold PMU.is_base10_spec, PMSP.is_base10_spec, PMSP.scan_spec.
intros fx R M model K p n sp r Mh Ml K0 ENT A10 A11 Hn Hp0 HpZ Hpn DEF _ BASE KONT.
destruct ENT as (Rra & (RA1 & RA2) & Rsp & Rgp & Rtp & STK).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11.
pose proof (L5C.stk_floor _ _ _ _ STK) as FL. pose proof STK as (S16 & SB & SC & SD & SW).
pose proof BASE as (RO & _ & _ & _). cbn [pa_rw_lo AD PmLayoutU.ADDR_U] in RO.
unfold PMSP.cfg. cbn [pa_is_base10 AD PmLayoutU.ADDR_U].
assert (FIN : forall fx' R' pc', msteps RSEGS (st fx R 0x37db8 M) (st fx' R' pc' M) -> (pc' = 0x37e70 \/ pc' = 0x37e68) ->
(forall k, In k KEEP -> getr R' (reg k) = getr R (reg k)) ->
srealizes RSEGS SCFG (mkCfg (st fx R 0x37db8 M) model) K).
{ intros fx' R' pc' MS PC KS. eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| exact MS|].
assert (R1' : getr R' (PMK.reg 1) = Z_to_bv 64 r) by (rewrite (KS 1%nat) by PMK.inl; exact Rra).
destruct PC as [->| ->].
- eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx' R' M 0x37e70 (ltac:(oW' 0x37e70%Z)) r (ltac:(oF' 0x37e70%Z)) ltac:(reflexivity) (ltac:(oD' 0x37e70%Z)) R1' RA1 RA2)|].
apply (KONT fx' R' M).
+ apply PMK.preserved_by_index. intros k Hk. apply KS. apply k_cs. exact Hk.
+ apply L5.frame_but_refl.
+ intros x Hx. exact Hx.
- eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx' R' M 0x37e68 (ltac:(oW' 0x37e68%Z)) r (ltac:(oF' 0x37e68%Z)) ltac:(reflexivity) (ltac:(oD' 0x37e68%Z)) R1' RA1 RA2)|].
apply (KONT fx' R' M).
+ apply PMK.preserved_by_index. intros k Hk. apply KS. apply k_cs. exact Hk.
+ apply L5.frame_but_refl.
+ intros x Hx. exact Hx. }
assert (Hsp : 0 <= sp < 2 ^ 64) by (unfold PMSP.pm_scr in *; lia).
destruct (Z.eq_dec p 0) as [Ep|Ep].
{ subst p. assert (En : n = 0) by (destruct HpZ as [E|E]; [exact E| lia]). subst n.
cfeed P (PMB10UPZ.ub10Ez_conc fx R M (fun j => match j with 2%nat => sp | _ => 0 end)) ltac:(first [ PMK.sc ]).
destruct P as (fx1 & R1 & M1 & MG & FR & FRZ & MS & KS & _). assert (EM : M1 = M) by (apply functional_extensionality; exact FR). subst M1.
apply (FIN fx1 R1 0x37e70 MS (or_introl eq_refl)). intros k Hk; apply KS; apply k_Ez; exact Hk. }
assert (Hp : 0 < p) by lia. clear HpZ.
cfeed P (PMB10UP.ub10E_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => p | 34%nat => n | _ => 0 end)) ltac:(first [ PMK.sc ]).
destruct P as (fx1 & R1 & M1 & MG & FR & FRZ & EX). assert (EM : M1 = M) by (apply functional_extensionality; exact FR). subst M1.
destruct EX as [(MS & KS & _)|(MS & KS & E5 & E6 & E7 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & Hn0)].
- apply (FIN fx1 R1 0x37e70 MS (or_introl eq_refl)). intros k Hk; apply KS; apply k_E0; exact Hk.
- rewrite Z.sub_0_r, Z.mod_small in Hn0 by lia.
destruct (loop_ms M sp p (p + n) RO ltac:(replace (p + n - p) with n by lia; exact DEF) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (Z.to_nat n) fx1 R1 p 0)
as (fx2 & R2 & pc2 & MS2 & PC2 & KS2).
{ rewrite Z2Nat.id by lia. lia. } { lia. }
{ unfold head. repeat split; first [ assumption | (rewrite (KS _) by PMK.inl; assumption) ]. }
{ lia. }
apply (FIN fx2 R2 pc2 ltac:(eapply msteps_trans; [exact MS| exact MS2]) PC2).
intros k Hk. rewrite (KS2 k Hk). apply KS. apply k_E1. exact Hk.
Qed.
End Stage.
End PMB10U.
