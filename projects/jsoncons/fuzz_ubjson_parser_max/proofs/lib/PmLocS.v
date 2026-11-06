(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StreamSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit PmLayout PmLayoutS PmModel PmStatics PmSpecs PmSpecsS PmStep PmKeep PmKitS PmCertKitS PmLocSIslandP PmLocSP.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmLocS () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLocSIslandP.PMLIP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLocSP.PMLP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsS.PMS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStatics.PMST."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStep.PMK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StreamSim."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1nat"; "1option"; "1true"; "2eq"; "0HI"; "0L"; "0M"; "3u64_at"; "3u8_at"; "4ADDR_S"; "5KS_liA"; "6KS_liB"; "6KS_liD"; "7locale_ctor_spec"; "7locale_dtor_spec"]; ["8loc_ok"; "9cs_all"; ":wseg_ok"; ";loaded_segments"; "0SCFG_P"; "<In"; "=to_nat"; "0k"; ">Z_to_bv"; ">bv"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMLOC.
Import PMS.
Lemma wseg_loc1 : ltac2:(TCodec.tc2 tcn__PmLocS ">'4'0&B&C&HyR0+hiTB%3221&F+QiN%211%93841(3%=3<21"). Proof. vm_compute. reflexivity. Qed.
Lemma wseg_loc2 : ltac2:(TCodec.tc2 tcn__PmLocS ">'4'0&B&C&HyR0+hlgH%3221&F+RH%211%93841(3%=3<21"). Proof. vm_compute. reflexivity. Qed.
Lemma cs_liA : ltac2:(TCodec.tc2 tcn__PmLocS ":'1&Er1&A%33421r2&;%63721p041pQ@91"). Proof. PMCK.cs_all_tac. Qed.
Lemma cs_liB : ltac2:(TCodec.tc2 tcn__PmLocS ":'1&Er1&A%33421r2&<%63721p041pQ@91"). Proof. PMCK.cs_all_tac. Qed.
Lemma cs_liD : ltac2:(TCodec.tc2 tcn__PmLocS ":'1&Er1&A%33421r2&=%63721p041pQ@91"). Proof. PMCK.cs_all_tac. Qed.
Section Stage.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.
Theorem locale_dtor_ok : ltac2:(TCodec.tc2 tcn__PmLocS "4&?vDv6%3221").
Proof.
unfold PMS.locale_dtor_spec, PMSP.locale_dtor_spec.
intros fx R M model K o sp r Mh Ml K0 ENT A10 Hspo Hotop CELL KONT.
destruct ENT as (Rra & (RA1 & RA2) & Rsp & Rgp & Rtp & STK).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl10 in A10.
pose proof (L5C.stk_floor _ _ _ _ STK) as FL. destruct STK as (S16 & SB & SC & SD & SW). unfold PMSP.pm_scr in *.
cfeed P (PMLP.liD_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | _ => 0 end)) ltac:(first [ PMK.sc | exact CELL ]).
destruct P as (fx1 & R1 & M1 & MG & FR & FRZ & MS & KS & B10 & B11).
assert (EM : M1 = M).
{ apply FunctionalExtensionality.functional_extensionality. intros a. apply FR. }
subst M1. unfold PMSP.cfg.
eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| exact MS|].
eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx1 R1 M 0x7f9b4 (ltac:(oW' 0x7f9b4%Z)) r (ltac:(oF' 0x7f9b4%Z)) ltac:(reflexivity) (ltac:(oD' 0x7f9b4%Z)))|].
- rewrite (KS 1%nat) by (apply L5K.In_of_mem; vm_compute; reflexivity). exact Rra.
- exact RA1.
- exact RA2.
- apply (KONT fx1 R1). apply PMK.preserved_by_index. intros k Hk. apply KS. apply cs_liD. exact Hk.
Qed.
Lemma loc_true : ltac2:(TCodec.tc2 tcn__PmLocS "K'IyR0%211'2y8%511%311p051&9&Cr1+hid@+1%544321&8r2+hid8+hje0%449321&@&:r3(3%44>321p061p0<1p@C1").
Proof. intros M. intros G P. split; [exact G| exact P]. Qed.
Theorem locale_ctor_ok : ltac2:(TCodec.tc2 tcn__PmLocS "5&>vDv6v5%43321").
Proof.
unfold PMS.locale_ctor_spec, PMSP.locale_ctor_spec.
intros fx R M model K LB cr o sp r b HH (Mh & Ml & Mm) K0 ENT A10 Hspo Hotop Ho8 DEFO BASE LOC KONT.
destruct ENT as (Rra & (RA1 & RA2) & Rsp & Rgp & Rtp & STK).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl10 in A10.
pose proof (L5C.stk_floor _ _ _ _ STK) as FL. pose proof (L5C.stk_writable RSEGS _ M sp _ STK) as WR0.
pose proof STK as (S16 & SB & SC & SD & SW). unfold PMSP.pm_scr in *.
assert (WRO : L5.writable RSEGS M o 8) by (apply (L5C.writable_of_defined RSEGS M o 8 DEFO); lia).
pose proof (PMCK.lb_hi L HI HIok LB cr M _ HH) as LBhi.
destruct BASE as (RO0 & (can & Hcan & CAN) & NL & LL).
destruct b.
-
destruct LOC as (G & P0).
cfeed P (PMLP.liB_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | _ => 0 end)) ltac:(first [ PMK.sc | exact G | exact P0 ]).
destruct P as (fx1 & R1 & M1 & MG & FR & FRZ & MS & KS & B10 & B11 & CO).
unfold PMSP.cfg.
apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x7f8bc R1 0x7f918 M1 (fun a => sp - 32 <= a < sp - 32 + 32 \/ o + 0 <= a < o + 0 + 8) K HH Mh Ml ltac:(lia) MS MG).
{ intros a Ha NP. apply FRZ; [exact Ha| |]; intros X; apply NP; [left|right]; exact X. }
{ intros a Ha. apply (PMK.cwr_stack L LB M sp (12288 + 2048 * 2) a STK). lia. }
{ intros a. apply PMK.or_dec; apply PMK.rng_dec. }
intros HH1.
eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx1 R1 M1 0x7f918 (ltac:(oW' 0x7f918%Z)) r (ltac:(oF' 0x7f918%Z)) ltac:(reflexivity) (ltac:(oD' 0x7f918%Z)))|].
+ rewrite (KS 1%nat) by (apply L5K.In_of_mem; vm_compute; reflexivity). exact Rra.
+ exact RA1.
+ exact RA2.
+ assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 32 <= a < sp) -> ~ (o <= a < o + 8) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha N1 N2. apply FRZ; [exact Ha| lia| lia]. }
apply (KONT fx1 R1 M1).
* apply PMK.preserved_by_index. intros k Hk. apply KS. apply cs_liB. exact Hk.
* exact CO.
* apply loc_true.
-- apply (L5C.u8_at_agree RSEGS M M1); [|lia|lia|exact G]. intros i Hi. apply AG; lia.
-- apply (L5C.u64_at_agree RSEGS M M1); [|lia|lia|exact P0]. intros i Hi. apply AG; lia.
* apply PMK.hpres_of.
-- apply (PMK.ek_piece_in RSEGS L KL LB sp (12288 + 2048 * 2) [(o, 8)] M M1 (fun a => sp - 32 <= a < sp \/ o <= a < o + 8)).
++ intros a Ha NP. apply AG; [exact Ha| |]; intros X; apply NP; [left|right]; exact X.
++ exact STK.
++ exact LBhi.
++ intros a [X|X]; [left; lia| right; apply PMK.inW_here; exact X].
-- apply (L5.defined_grows M M1 _ _ MG). exact SW.
-- apply PMK.dk_grows. exact MG.
* exact HH1.
-
cbn [PMST.loc_ok] in LOC. unfold PMST.img_clear_l in LOC.
assert (C1 : L5.img_clear M 812178 814032) by (apply (LOC (0xc6492, 0xc6bd0)); cbn; auto).
assert (C2 : L5.img_clear M 815864 815952) by (apply (LOC (0xc72f8, 0xc7350)); cbn; auto).
cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PmLayoutS.ADDR_S] in RO0, CAN, NL, LL.
pose proof (PMCK.writable_img M 812178 1854 wseg_loc1 ltac:(lia) ltac:(lia) ltac:(lia)) as W1.
pose proof (PMCK.writable_img M 815864 88 wseg_loc2 ltac:(lia) ltac:(lia) ltac:(lia)) as W2.
cfeed P (PMLIP.liA_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => can | _ => 0 end)) ltac:(first [ PMK.sc | exact C1 | exact C2 | exact W1 | exact W2 | exact CAN ]).
destruct P as (fx1 & R1 & M1 & MG & FR & FRZ & MS & KS & B10 & B11 & CO & CG & CP).
unfold PMSP.cfg.
apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x7f8bc R1 0x7f918 M1
(fun a => (sp - 1024 <= a < sp - 1024 + 1024 \/ o + 0 <= a < o + 0 + 8) \/ (0 + 812178 <= a < 0 + 812178 + 1854 \/ 0 + 815864 <= a < 0 + 815864 + 88)) K HH Mh Ml ltac:(lia) MS MG).
{ intros a Ha NP. apply FRZ; [exact Ha| | | |]; intros X; apply NP; [left; left|left; right|right; left|right; right]; exact X. }
{ intros a [Ha|[Ha|Ha]].
- apply (PMK.cwr_stack L LB M sp (12288 + 2048 * 2) a STK). lia.
- apply (PMKS.cwr_foot_S L LY LB (0xc6492, 0xc6bd0) a); [unfold pm_foot; cbn; auto| cbn [fst snd]; lia].
- apply (PMKS.cwr_foot_S L LY LB (0xc72f8, 0xc7350) a); [unfold pm_foot; cbn; auto| cbn [fst snd]; lia]. }
{ intros a. apply PMK.or_dec; apply PMK.or_dec; apply PMK.rng_dec. }
intros HH1.
eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx1 R1 M1 0x7f918 (ltac:(oW' 0x7f918%Z)) r (ltac:(oF' 0x7f918%Z)) ltac:(reflexivity) (ltac:(oD' 0x7f918%Z)))|].
+ rewrite (KS 1%nat) by (apply L5K.In_of_mem; vm_compute; reflexivity). exact Rra.
+ exact RA1.
+ exact RA2.
+ apply (KONT fx1 R1 M1).
* apply PMK.preserved_by_index. intros k Hk. apply KS. apply cs_liA. exact Hk.
* exact CO.
* apply loc_true; [exact CG| exact CP].
* apply PMK.hpres_of.
-- apply (PMK.ek_piece_in RSEGS L KL LB sp (12288 + 2048 * 2) ((o, 8) :: PMSP.loc_W AD) M M1
(fun a => (sp - 1024 <= a < sp \/ o <= a < o + 8) \/ (812178 <= a < 814032 \/ 815864 <= a < 815952))).
++ intros a Ha NP. apply FRZ; [exact Ha| | | |]; intros X; apply NP; [left; left|left; right|right; left|right; right]; lia.
++ exact STK.
++ exact LBhi.
++ intros a [[X|X]|[X|X]]; [left; lia| right; apply PMK.inW_here; exact X | right | right ].
** apply PMK.inW_next. exists (812178, 1854). split; [cbn; auto| unfold L5.in_rng; cbn [fst snd]; lia].
** apply PMK.inW_next. exists (815864, 88). split; [cbn; auto| unfold L5.in_rng; cbn [fst snd]; lia].
-- apply (L5.defined_grows M M1 _ _ MG). exact SW.
-- apply PMK.dk_grows. exact MG.
* exact HH1.
Qed.
End Stage.
End PMLOC.
