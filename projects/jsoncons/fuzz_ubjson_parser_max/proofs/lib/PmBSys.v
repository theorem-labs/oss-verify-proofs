(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StreamSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0 L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0 L5StepARB0 PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAb PmModelFactsA PmStep PmStepAB0 PmStepB2 PmBSysP.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := L5FastLia.plia.
Module PMBSY.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMB.ly_as0 L C LY.
Lemma writable_img M a n : wseg_ok RSEGS (Z_to_bv 64 a) (Z.to_nat n) = true -> 0 <= a -> 0 < n -> a + n <= 2 ^ 64 -> L5.writable RSEGS M a n.
Proof.
intros W Ha Hn Han d k Hd Hk. destruct k as [|k]. reflexivity.
eapply (store_ok_sub RSEGS M (Z_to_bv 64 a) _ (Z.to_nat n) (Datatypes.S k)).
- rewrite L5.unsigned_lit by lia. rewrite Z2Nat.id by lia. lia.
- apply store_ok_wseg. exact W.
- rewrite !L5.unsigned_lit by lia. lia.
- rewrite !L5.unsigned_lit by lia. rewrite Z2Nat.id by lia. lia.
Qed.
Theorem syscat_ok : PMB.syscat_spec L ar HI.
Proof.
unfold PMB.syscat_spec, PMSPA.syscat_spec.
intros fx R M model K LB FF LK Aw cr sp r b HH AM K0 ENT FRM FRS BASE SYS KONT.
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH).
pose proof RAok as (Hr1 & Hr2). pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
change (PMSPA.pm_scr 1) with 14336 in *.
assert (SP0 : 0 <= sp) by (unfold app_mem, FS_BYTES in *; lia).
pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
unfold PMSPA.cfg. cbn [pa_syscat PMB.AD ADDR_A].
cbn [pa_syscat_guard PMB.AD ADDR_A] in SYS.
destruct b.
-
cbn in SYS.
assert (VG : L5.u8_at RSEGS MV 6746864 1).
{ apply (proj2 (L5A.u8_at_vis H M 6746864 1 (VIMG 6746864 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact SYS. }
cfeed P (PMBSYP.asyA_conc fx R MV (fun j => match j with 2%nat => sp | _ => 0 end)) ltac:(first [assumption | exact Rsp | lia]).
destruct P as (fx1 & R1 & M1v & MG1 & FR1 & _ & MS1 & KS1 & A10).
assert (E1 : M1v = MV) by (apply functional_extensionality; exact FR1). subst M1v.
assert (R1ra : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS1 1%nat) by inl; exact Rra).
pose proof (PMK.ret_to RSEGS fx1 R1 MV 0xd6408 (ltac:(oW' 0xd6408%Z)) r (ltac:(oF' 0xd6408%Z)) eq_refl (ltac:(oD' 0xd6408%Z)) R1ra ltac:(lia) Hr2) as MS2.
apply (L5SAR.apiece_ro L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xd63f0 R1 r MV K HH AM).
{ eapply msteps_trans; [exact MS1| exact MS2]. }
{ intros a Ha. exact Ha. }
{ intros a Ha. reflexivity. }
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1'.
apply (KONT fx1 R1 M1 model1 LK Aw).
+ apply L5SAR.preserved_by_index. intros k Hk. apply KS1. unfold L5SAR.cs_all in Hk. repeat (destruct Hk as [<-|Hk]; [inl|]). destruct Hk.
+ exact A10.
+ unfold PMST.sys_ok. cbn [pa_syscat_guard PMB.AD ADDR_A]. apply (L5C.u8_at_agree RSEGS M M1); [intros i Hi; apply FR1'; lia | lia | lia | exact SYS].
+ change (PMSPA.pm_scr 1) with 14336. split; [intros a (Ha & _); apply FR1'; exact Ha|]. split.
* eapply L5C.defined_agree; [intros i Hi; apply FR1'; lia| exact SDEF].
* intros a Ha _ Hn. rewrite FR1' by exact Ha. exact Hn.
+ exact MRT1.
+ intros x Hx. exact Hx.
+ intros x Hx. exact Hx.
+ exact AM1.
+ exact HH1.
-
cbn in SYS.
assert (V0 : L5.img_clear MV 6746864 6746866) by (apply L5A.img_clear_mrestrict; exact SYS).
assert (V1 : L5.writable RSEGS MV 6746864 2) by (apply writable_img; [vm_compute; reflexivity| lia| lia| lia]).
assert (V2 : L5.writable RSEGS MV (sp - 16) 16).
{ apply (proj2 (L5A.writable_vis H M (sp - 16) 16 (VIS (sp - 16) 16 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
apply (L5C.writable_of_defined RSEGS). apply (L5.defined_sub M (sp - 14336) 14336); [exact SDEF| lia| lia]. lia. lia. }
cfeed P (PMBSYP.asyB_conc fx R MV (fun j => match j with 2%nat => sp | _ => 0 end)) ltac:(first [assumption | exact Rsp | unfold PMBSYP.aligned; lia | lia]).
destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A10 & _ & _ & G1 & G0).
assert (R1ra : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS1 1%nat) by inl; exact Rra).
pose proof (PMK.ret_to RSEGS fx1 R1 M1v 0xd6408 (ltac:(oW' 0xd6408%Z)) r (ltac:(oF' 0xd6408%Z)) eq_refl (ltac:(oD' 0xd6408%Z)) R1ra ltac:(lia) Hr2) as MS2.
apply (PMKB2.apiece_img L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xd63f0 R1 r M1v
(fun a => sp - 16 <= a < sp - 16 + 16 \/ 0 + 6746864 <= a < 0 + 6746864 + 2) K HH AM).
{ eapply msteps_trans; [exact MS1| exact MS2]. }
{ exact MG1. }
{ intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
{ intros a Ha [Wa|Wa].
- split; [|intros X; pose proof (PMB.ly_ro L C LY a X); lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia].
- split; [|apply (PMKB2.rt_ro_bss L C a LY); lia]. unfold aclientw, aclient_g. right; right; left.
rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia|].
intros [X|X].
+ apply (PMB.ly_static L C LY a); [|exact X]. unfold PMST.dep, pm_foot, pm_initc. left.
exists (0x66f2f0, 0x66f2f2). split; [cbn; tauto| cbn [fst snd]; lia].
+ pose proof (PMB.ly_ro L C LY a X). lia. }
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
apply (KONT fx1 R1 M1 model1 LK Aw).
+ apply L5SAR.preserved_by_index. intros k Hk. apply KS1. unfold L5SAR.cs_all in Hk. repeat (destruct Hk as [<-|Hk]; [inl|]). destruct Hk.
+ exact A10.
+ unfold PMST.sys_ok. cbn [pa_syscat_guard PMB.AD ADDR_A].
rewrite <- VIS1 in G0.
apply (proj1 (L5A.u8_at_vis H M1 6746864 1 (VIMG 6746864 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact G0.
+ change (PMSPA.pm_scr 1) with 14336. cbn [pa_syscat_guard PMB.AD ADDR_A].
assert (EK : L5SAR.ek L ar LB FF sp 14336 [(6746864, 2)] M M1).
{ apply (L5SAR.ek_piece L ar LB FF sp 14336 [(6746864, 2)] M M1 (fun a => (sp - 16 <= a < sp - 16 + 16) \/ (0 + 6746864 <= a < 0 + 6746864 + 2))).
{ intros a Ha N. apply FR1; [exact Ha| exact N]. }
intros a Ha Hc Ho [X|X].
- destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M (vml_of model) sp 14336 a HH SPT Hc) as [(Y1 & Y2)|Y]; [apply Y2; lia| exfalso; lia].
- apply (Ho (6746864, 2)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
apply (L5SAR.ahpres_of L ar LB FF sp 14336 [(6746864, 2)] M M1 EK).
* intros i Hi. apply MGM1. apply SDEF. exact Hi.
* apply (L5SAR.dk_grows L ar LB FF sp 14336 M M1 MGM1).
+ exact MRT1.
+ intros x Hx. exact Hx.
+ intros x Hx. exact Hx.
+ exact AM1.
+ exact HH1.
Qed.
End WithHeap.
End PMBSY.
