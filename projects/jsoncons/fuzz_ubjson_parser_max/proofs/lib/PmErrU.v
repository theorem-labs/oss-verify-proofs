(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StreamSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit PmLayout PmLayoutU PmModel PmStatics PmSpecs PmSpecsU PmStep PmKeep PmKitU PmCertKitU PmErrUP.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Ubsan.
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMERRU.
Import PMU.
Lemma wseg_errg : wseg_ok RSEGS (Z_to_bv 64 815792) (Z.to_nat 2) = true. Proof. vm_compute. reflexivity. Qed.
Lemma wseg_atexit : wseg_ok RSEGS (Z_to_bv 64 953592) (Z.to_nat 544) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cs_erA : forall k, In k PMK.cs_all -> In k PMERUP.KS_uerA. Proof. PMCKU.cs_all_tac. Qed.
Lemma cs_erB : forall k, In k PMK.cs_all -> In k PMERUP.KS_uerB. Proof. PMCKU.cs_all_tac. Qed.
Section Stage.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMU.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKU.klayout_U L LY.
Theorem make_ec_ok : PMU.make_ec_spec L HI.
Proof.
unfold PMU.make_ec_spec, PMSP.make_ec_spec.
intros fx R M model K LB cr o v sp r b HH (Mh & Ml & Mm) K0 ENT A10 A11 Hv Hspo Hotop Ho8 DEFO BASE ERR KONT.
destruct ENT as (Rra & (RA1 & RA2) & Rsp & Rgp & Rtp & STK).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11.
pose proof (L5C.stk_floor _ _ _ _ STK) as FL. pose proof (L5C.stk_writable RSEGS _ M sp _ STK) as WR0.
pose proof STK as (S16 & SB & SC & SD & SW). unfold PMSP.pm_scr in *.
assert (WRO : L5.writable RSEGS M o 16) by (apply (L5C.writable_of_defined RSEGS M o 16 DEFO); lia).
pose proof (PMCKU.lb_hi L HI HIok LB cr M _ HH) as LBhi.
destruct BASE as (RO0 & _ & NL & _).
cbn [pa_rw_lo pa_need_locks AD PmLayoutU.ADDR_U] in RO0, NL.
destruct ERR as (EG & EA). unfold PMST.atexit_st in EA. cbv zeta in EA.
destruct b; cbn [pa_errcat_guard pa_atexit pa_atexit_call pa_exit_guard pa_errcat_dtor pa_errcat_obj AD PmLayoutU.ADDR_U] in EG, EA.
-
cfeed P (PMERUP.uerA_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => v | _ => 0 end)) ltac:(first [ PMK.sc | exact EG ]).
destruct P as (fx1 & R1 & M1 & MG & FR & FRZ & MS & KS & C8 & C0).
unfold PMSP.cfg.
apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x370ac R1 0x37100 M1 (fun a => sp - 32 <= a < sp - 32 + 32 \/ o + 0 <= a < o + 0 + 16) K HH Mh Ml ltac:(lia) MS MG).
{ intros a Ha NP. apply FRZ; [exact Ha| |]; intros X; apply NP; [left|right]; exact X. }
{ intros a Ha. apply (PMK.cwr_stack L LB M sp (12288 + 2048 * 1) a STK). lia. }
{ intros a. apply PMK.or_dec; apply PMK.rng_dec. }
intros HH1.
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 32 <= a < sp) -> ~ (o <= a < o + 16) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha N1 N2. apply FRZ; [exact Ha| lia| lia]. }
eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx1 R1 M1 0x37100 (ltac:(oW' 0x37100%Z)) r (ltac:(oF' 0x37100%Z)) ltac:(reflexivity) (ltac:(oD' 0x37100%Z)))|].
+ rewrite (KS 1%nat) by (apply L5K.In_of_mem; vm_compute; reflexivity). exact Rra.
+ exact RA1.
+ exact RA2.
+ apply (KONT fx1 R1 M1).
* apply PMK.preserved_by_index. intros k Hk. apply KS. apply cs_erA. exact Hk.
* split; [apply PMCKU.u32_of_u64; exact C0|]. split; [exact C8|]. apply (L5.defined_grows M M1 _ _ MG). exact DEFO.
* split; cbn [pa_errcat_guard pa_atexit AD PmLayoutU.ADDR_U].
-- apply (L5C.u8_at_agree RSEGS M M1); [|lia|lia|exact EG]. intros i Hi. apply AG; lia.
-- apply (PMST.atexit_agree RSEGS AD addrs_wf_U M M1); [|unfold PMST.atexit_st; cbv zeta; cbn [pa_atexit pa_atexit_call pa_exit_guard pa_errcat_dtor pa_errcat_obj AD PmLayoutU.ADDR_U]; exact EA].
intros i Hi. cbn [pa_atexit AD PmLayoutU.ADDR_U] in Hi. apply AG; lia.
* apply PMK.hpres_of.
-- apply (PMK.ek_piece_in RSEGS L KL LB sp (12288 + 2048 * 1) [(o, 16)] M M1 (fun a => sp - 32 <= a < sp \/ o <= a < o + 16)).
++ intros a Ha NP. apply AG; [exact Ha| |]; intros X; apply NP; [left|right]; exact X.
++ exact STK.
++ exact LBhi.
++ intros a [X|X]; [left; lia| right; apply PMK.inW_here; exact X].
-- apply (L5.defined_grows M M1 _ _ MG). exact SW.
-- apply PMK.dk_grows. exact MG.
* exact HH1.
-
pose proof (PMCKU.writable_img M 815792 2 wseg_errg ltac:(lia) ltac:(lia) ltac:(lia)) as W1.
pose proof (PMCKU.writable_img M 953592 544 wseg_atexit ltac:(lia) ltac:(lia) ltac:(lia)) as W2.
destruct EA as (EA1 & EAS & EA2 & EAH & EA3 & EAF0 & EAF1 & EA4 & EAA0 & EAA1 & EA5).
assert (EA45 : L5.img_clear M 953632 953880) by (intros i Hi; destruct (Z_lt_dec i 953640); [apply EAF1; lia | apply EA4; lia]).
assert (EA67 : L5.img_clear M 953888 954136) by (intros i Hi; destruct (Z_lt_dec i 953896); [apply EAA1; lia | apply EA5; lia]).
cfeed P (PMERUP.uerB_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => v | _ => 0 end)) ltac:(first [ PMK.sc | exact EG | exact W1 | exact W2 ]).
destruct P as (fx1 & R1 & M1 & MG & FR & FRZ & MS & KS & B11 & B12 & B13 & C8 & C0 & G1 & G0 & SLOT & A1 & F1).
unfold PMSP.cfg.
set (P7 := fun a => (sp - 128 <= a < sp \/ o <= a < o + 16) \/ 815792 <= a < 815794 \/ 953600 <= a < 953604 \/ 953632 <= a < 953640 \/ 953888 <= a < 953896).
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ P7 a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha NP. unfold P7 in NP. apply FRZ; [exact Ha| | | | | |]; intros X; apply NP; lia. }
apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x370ac R1 0x37100 M1 P7 K HH Mh Ml ltac:(lia) MS MG AG).
{ intros a [[Ha|Ha]|Ha].
- apply (PMK.cwr_stack L LB M sp (12288 + 2048 * 1) a STK). lia.
- apply (PMK.cwr_stack L LB M sp (12288 + 2048 * 1) a STK). lia.
- destruct (PMK.rng_dec a 815792 815794) as [G|NG].
+ apply (PMKU.cwr_foot_S L LY LB (0xc72b0, 0xc72b2) a); [unfold pm_foot; cbn; auto| cbn [fst snd]; lia].
+ apply (PMKU.cwr_foot_S L LY LB (0xe8cf8, 0xe8cf8 + 544) a); [unfold pm_foot; cbn; auto 10| cbn [fst snd]; lia]. }
{ intros a. unfold P7. repeat apply PMK.or_dec; apply PMK.rng_dec. }
intros HH1.
eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx1 R1 M1 0x37100 (ltac:(oW' 0x37100%Z)) r (ltac:(oF' 0x37100%Z)) ltac:(reflexivity) (ltac:(oD' 0x37100%Z)))|].
+ rewrite (KS 1%nat) by (apply L5K.In_of_mem; vm_compute; reflexivity). exact Rra.
+ exact RA1.
+ exact RA2.
+
assert (CLR : forall lo hi, (forall i, lo <= i < hi -> M (Z_to_bv 64 i) = None) -> 0 <= lo -> hi <= 2 ^ 64 -> (forall i, lo <= i < hi -> ~ P7 i) -> L5.img_clear M1 lo hi).
{ intros lo hi CL Hlo Hhi NP i Hi. rewrite AG; [apply CL; exact Hi| lia| apply NP; exact Hi]. }
assert (U8 : forall a w, L5.u64_at RSEGS M a w -> 0 <= a -> a + 8 <= 2 ^ 64 -> (forall i, a <= i < a + 8 -> ~ P7 i) -> L5.u64_at RSEGS M1 a w).
{ intros a w U Ha H8 NP. apply (L5C.u64_at_agree RSEGS M M1); [|lia|lia|exact U]. intros i Hi. apply AG; [lia|]. apply NP. exact Hi. }
apply (KONT fx1 R1 M1).
* apply PMK.preserved_by_index. intros k Hk. apply KS. apply cs_erB. exact Hk.
* split; [apply PMCKU.u32_of_u64; exact C0|]. split; [exact C8|]. apply (L5.defined_grows M M1 _ _ MG). exact DEFO.
* split; cbn [pa_errcat_guard AD PmLayoutU.ADDR_U]; [exact G0|].
unfold PMST.atexit_st. cbv zeta. cbn [pa_atexit pa_atexit_call pa_exit_guard pa_errcat_dtor pa_errcat_obj AD PmLayoutU.ADDR_U].
split; [apply (CLR _ _ EA1); [lia|lia|intros i Hi; unfold P7; lia]|]. split; [exact SLOT|].
split; [apply (CLR _ _ EA2); [lia|lia|intros i Hi; unfold P7; lia]|]. split; [apply (U8 _ _ EAH); [lia|lia|intros i Hi; unfold P7; lia]|].
split; [apply (CLR _ _ EA3); [lia|lia|intros i Hi; unfold P7; lia]|]. split; [apply (U8 _ _ EAF0); [lia|lia|intros i Hi; unfold P7; lia]|].
split; [exact F1|].
split; [apply (CLR _ _ EA4); [lia|lia|intros i Hi; unfold P7; lia]|]. split; [apply (U8 _ _ EAA0); [lia|lia|intros i Hi; unfold P7; lia]|].
split; [exact A1|].
apply (CLR _ _ EA5); [lia|lia|intros i Hi; unfold P7; lia].
* apply PMK.hpres_of.
-- apply (PMK.ek_piece_in RSEGS L KL LB sp (12288 + 2048 * 1) ((o, 16) :: PMSP.err_W AD) M M1 P7 AG STK LBhi).
intros a [[X|X]|X]; [left; lia| right; apply PMK.inW_here; exact X| right; apply PMK.inW_next].
destruct (PMK.rng_dec a 815792 815794) as [G|NG].
++ exists (815792, 2). split; [cbn; auto| unfold L5.in_rng; cbn [fst snd]; lia].
++ exists (953592, 544). split; [cbn; auto| unfold L5.in_rng; cbn [fst snd]; lia].
-- apply (L5.defined_grows M M1 _ _ MG). exact SW.
-- apply PMK.dk_grows. exact MG.
* exact HH1.
Qed.
End Stage.
End PMERRU.
