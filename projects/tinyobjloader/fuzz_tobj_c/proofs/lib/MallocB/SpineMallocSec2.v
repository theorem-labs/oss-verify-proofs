(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9 RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.RebuildN.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition a1x : sv :=
  SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_AND (SAlu ALU_ADD (SVar V_NS) (SLit 4095)) (SLit 18446744073709547520)) (SLit 8191)) (SLit 18446744073709547520).

Lemma acost_step : forall V n, 0 <= V -> 0 <= n -> 4 * (acost (V + n) - acost V) >= 7 * n - 3.
Proof.
  intros V n HV Hn. unfold acost, ALPHA_NUM, ALPHA_DEN.
  pose proof (Z.div_mod (7 * (V + n) + 4 - 1) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (7 * (V + n) + 4 - 1) 4 ltac:(lia)).
  pose proof (Z.div_mod (7 * V + 4 - 1) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (7 * V + 4 - 1) 4 ltac:(lia)). lia.
Qed.

Definition IMG_S : list (Z * Z) := [(SEC_INST, 0xead04 - SEC_INST); (0xead08, 0xead30 - 0xead08); (0xe67b8, 8); (0x170320, 2)].
Lemma IMG_M_lo : forallb (fun r : Z * Z => (0x10000 <=? fst r) && (fst r + snd r <=? IMG_HI)) IMG_M = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma IMG_M_range : forall a, in_rangesZ IMG_M a -> 0x10000 <= a < IMG_HI.
Proof.
  intros a (b & n & Hr & Ha). pose proof (proj1 (forallb_forall _ _) IMG_M_lo (b, n) Hr) as X.
  apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2. cbn [fst snd] in X1, X2. lia.
Qed.

Lemma rtc_img_lo : forall z, cells_footb (rtc_cells_img RTC_A G0) z = true -> 0x10000 <= z.
Proof.
  intros z Hz. unfold cells_footb in Hz. apply existsb_exists in Hz as (c & Hc & Hin). unfold in_cellb in Hin.
  apply andb_prop in Hin as [X Y]. apply Z.leb_le in X.
  assert (L : forallb (fun c => 0x10000 <=? c_addr c) (rtc_cells_img RTC_A G0) = true) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  pose proof (proj1 (forallb_forall _ _) L c Hc) as L'. apply Z.leb_le in L'. lia.
Qed.

Definition rt_zoneG (G : ageom) (a : Z) : Prop :=
  (0x10000 <= a < IMG_HI) \/ (ag_thread G <= a < ag_thread G + 0x1000) \/ (ag_ctx G <= a < ag_ctx G + 0x1000)
  \/ (ag_dtls G <= a < ag_dtls G + 0x1000) \/ (ag_fsb G <= a < ag_fsb G + FS_total).
Lemma rt_zoneM_G : forall G a, rt_zoneM G a -> rt_zoneG G a.
Proof.
  intros G a [[[X Y]|R]|R]; unfold rt_zoneG.
  - left. pose proof (rtc_img_lo a Y). lia.
  - rewrite FS_total_val. lia.
  - left. exact (IMG_M_range a R).
Qed.
Lemma N_sec_zone : forall G rho k a,
  rw rho 151%positive = Z_to_bv 64 (ag_thread G) -> 0 <= ag_thread G < 2 ^ 64 ->
  In k N_sec -> fst (spec_range rho k) <= a < snd (spec_range rho k) -> rt_zoneG G a.
Proof.
  intros G rho k a E151 HT Hk Ha. unfold N_sec in Hk. unfold rt_zoneG, IMG_HI. unfold SEC_INST, ERRNO_A, vT in Hk.
  repeat (destruct Hk as [<-|Hk]; [cbn [spec_range fst snd eval] in Ha; rewrite ?E151, ?u64_lit in Ha by lia; lia|]). destruct Hk.
Qed.
Lemma N_m1_zoneG : forall G rho k a,
  geom_ok G -> rw rho 151%positive = Z_to_bv 64 (ag_thread G) -> rw rho 152%positive = Z_to_bv 64 (ag_ctx G) ->
  In k N_m1 -> fst (spec_range rho k) <= a < snd (spec_range rho k) -> rt_zoneG G a.
Proof. intros G rho k a HG E151 E152 Hk Ha. apply rt_zoneM_G. exact (N_m1_zone G rho k a HG E151 E152 Hk Ha). Qed.

Lemma carve_range : forall rho k, spec_small k -> obj_range rho (carve_obj k) = spec_range rho k.
Proof.
  intros rho [[[base lo] hi] cs] (S1 & S2 & S3 & _). cbn [carve_obj]. unfold carved. rewrite obj_range_mk by lia. reflexivity.
Qed.
Lemma N_sec_small : Forall spec_small N_sec.
Proof.
  unfold N_sec, spec_small. unfold SEC_INST, ERRNO_A.
  repeat apply Forall_cons; try apply Forall_nil; (split; [lia|]); (split; [lia|]); (split; [lia|]); unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia.
Qed.
Lemma ok_pframeA_liftKA : forall segs (ok : world -> Prop) (Kc : KcA) (Jx : jpredA),
  ok_pframeA segs ok (liftKA Kc) -> (forall rho tp tr md, Jx rho tp tr md -> Kc tr md) -> ok_pframeA segs ok Jx.
Proof. intros segs ok Kc Jx H HJ rho tp tr ms md x8 Hj. apply (H rho tp tr ms md x8). exact (HJ _ _ _ _ Hj). Qed.

Lemma sw_range_holds : forall segs rho ms objs o,
  Forall (obj_holds segs rho ms) objs -> In o objs -> skel o = (SVar 10, SVar V_DEPTH, SLit 0) -> holds rho F_sp_high ->
  140735332483072 <= fst (obj_range rho o) /\ snd (obj_range rho o) = bv_unsigned (rw rho 10%positive)
  /\ fst (obj_range rho o) <= snd (obj_range rho o).
Proof.
  intros segs rho ms objs o Hall Hin Hsk Hf.
  destruct o as [ob olo ohi ocs od]. cbn in Hsk. injection Hsk as -> -> ->.
  pose proof (proj1 (Forall_forall _ _) Hall _ Hin) as Ho.
  unfold obj_holds, obj_lo_of, obj_hi_of in Ho. cbn [ob_base ob_lo ob_hi] in Ho.
  destruct Ho as ((B1 & B2 & B3 & B4) & _).
  unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd].
  rewrite soff_lit in *. replace (snorm 0) with 0 in * by reflexivity.
  cbn [eval] in *. unfold holds, F_sp_high in Hf. cbn [eval] in Hf. rewrite add_val in Hf.
  rewrite u64_lit in Hf by lia.
  rewrite soff_snorm in *. unfold U in *. cbn [eval] in *.
  pose proof (urange (rw rho 10%positive)) as R10. pose proof (urange (rw rho V_DEPTH)) as R15.
  unfold snorm in *.
  rewrite (Z.mod_small (bv_unsigned (rw rho V_DEPTH)) (2 ^ 64)) in * by lia.
  destruct (Z.ltb_spec (bv_unsigned (rw rho V_DEPTH)) (2 ^ 63)).
  - assert (bv_unsigned (rw rho V_DEPTH) = 0) by lia. rewrite H0 in *. rewrite Z.add_0_r, Z.mod_small in Hf by lia. lia.
  - replace ((bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho V_DEPTH)) mod 2 ^ 64)
      with (bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho V_DEPTH) - 2 ^ 64) in Hf.
    2:{ symmetry. replace (bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho V_DEPTH)) with
          ((bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho V_DEPTH) - 2 ^ 64) + 1 * 2 ^ 64) at 1 by lia.
        rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    lia.
Qed.

Lemma skel_head : forall (objs : list sobj) o' l', map skel objs = map skel (o' :: l') ->
  exists o rest, objs = o :: rest /\ skel o = skel o' /\ map skel rest = map skel l'.
Proof.
  intros [|o rest] o' l' E; cbn in E; [discriminate|]. exists o, rest. split; [reflexivity|]. split; congruence.
Qed.

Section SEC2.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : forall a, in_rangesZ CST a -> in_rangesZ IMG_M a -> False.
Hypothesis HCSTS : forall a, in_rangesZ CST a -> in_rangesZ IMG_S a -> False.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := J_alloc_preT AInv W st A Kc (SVar 12).

Hypothesis law_res : forall A rho tp md, AInv A rho tp md -> vm_reserved (m_vmmaps md) = segments_reserved segsA.

Lemma JG_rigidS : forall A Kc rho rhoE tp tr md,
  JG W st A Kc rho rhoE tp tr md ->
  let nv := bv_unsigned (rw rho 12%positive) in let G := aa_geom A in
  rw rhoE 12%positive = rw rho 12%positive
  /\ rw rhoE 141%positive = Z_to_bv 64 (secneeded nv) /\ rw rhoE 142%positive = Z_to_bv 64 (secmapsize nv)
  /\ rw rhoE 151%positive = Z_to_bv 64 (ag_thread G) /\ rw rhoE 152%positive = Z_to_bv 64 (ag_ctx G)
  /\ rw rhoE 153%positive = Z_to_bv 64 (ag_stack_top G) /\ rw rhoE 154%positive = Z_to_bv 64 (ag_stack_bottom G)
  /\ rw rhoE 155%positive = Z_to_bv 64 (ag_spacebeg G) /\ rw rhoE 156%positive = Z_to_bv 64 (ag_spacebeg G + kSpaceSize)
  /\ rw rhoE 145%positive = Z_to_bv 64 (ag_pab G) /\ rw rhoE 146%positive = Z_to_bv 64 (aa_ptr_committed A / 8)
  /\ rw rhoE 147%positive = Z_to_bv 64 (Z.of_nat (length (aa_sec A)))
  /\ rm rhoE = rm rho /\ (forall l, rl rhoE l = rl rho l) /\ (forall i, (i < GW)%positive -> rw rhoE i = rw (rhoM_of A rho) i).
Proof.
  intros A Kc rho rhoE tp tr md [Hag _]. destruct Hag as (Hagw & Hagl & Hagm). cbn zeta.
  repeat match goal with |- _ /\ _ => split end;
    try (rewrite <- (Hagw _) by (unfold GW; lia); reflexivity).
  - apply functional_extensionality. intros a. symmetry. exact (Hagm a).
  - intros l. symmetry. exact (Hagl l).
  - intros i Hi. symmetry. exact (Hagw i Hi).
Qed.

Section C1.
Hypothesis CertS1 : check_cfgA segsA 4000%nat [0x706a0] GW [SS0 W st tmax] [ES1 W st tmax] = true.
Theorem sec_cert1 : forall (ok : world -> Prop) (A : AA) (Kc : KcA) rho tp (Q : assn),
  stopJ_stable W st -> Kc_ok Kc -> ok_frameA segs ok (J W st A Kc) ->
  (forall rhoX, triple segs ok (SPA segs (JG W st A Kc rho) (ES1 W st tmax) rhoX tp) Q) ->
  forall rhoE, triple segs ok (SPA segs (JG W st A Kc rho) (SS0 W st tmax) rhoE tp) Q.
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf HR rhoE.
  apply (cfg_soundA segs 4000%nat [0x706a0] GW [SS0 W st tmax] [ES1 W st tmax] (JG W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. exact (Hokf r t tr ms md msv' HJ HMI Hh Hp Hs).
  - apply JG_stable; [exact HUS | exact HKc].
  - exact CertS1.
  - intros E rhoX HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | apply HR].
  - left. reflexivity.
Qed.
End C1.

Section C2.
Hypothesis WC1 : swf (ax_S (CS1 W st tmax)) = true.
Hypothesis DC1 : state_diff (ax_S (ES1 W st tmax)) (ax_S (CS1 W st tmax)) = Some ([(a1x, SVar V_MS)], []).
Hypothesis NXC1 : ss_next (ax_S (CS1 W st tmax)) = ss_next (ax_S (ES1 W st tmax)).

Lemma sec_cs1 : forall A Kc rho tp w rhoX,
  SPA segs (JG W st A Kc rho) (ES1 W st tmax) rhoX tp w -> SPA segs (JG W st A Kc rho) (CS1 W st tmax) rhoX tp w.
Proof.
  intros A Kc rho tp w rhoX H. destruct w as [tr [ms md]].
  pose proof (JG_rigidS A Kc rho rhoX tp tr md (proj2 H)) as (E12 & E141 & E142 & _).
  destruct (proj2 H) as [_ HJ]. destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN. rewrite E12 in HN.
  set (nv := bv_unsigned (rw rho 12%positive)) in *.
  pose proof (round_up_ge' nv 8 ltac:(lia)) as RU1. pose proof (round_up_mod nv 8 ltac:(lia)) as RM1.
  pose proof (round_up_ge' (secneeded nv) PG ltac:(unfold PG; lia)) as RU2. pose proof (round_up_mod (secneeded nv) PG ltac:(unfold PG; lia)) as RM2.
  unfold PG in RU2, RM2.
  assert (NS : secneeded nv = round_up nv 8 + 4096) by reflexivity.
  assert (MS : secmapsize nv = round_up (secneeded nv) 4096 + 4096) by reflexivity.
  assert (EA : eval rhoX a1x = eval rhoX (SVar V_MS)).
  { unfold a1x, V_NS, V_MS. cbn [eval]. rewrite E141, E142. apply bv_eq.
    rewrite and_val, add_val, and_val, add_val, !u64_lit by lia.
    rewrite (Z.mod_small (secneeded nv + 4095)) by lia. rewrite <- round_up_land by lia.
    rewrite (Z.mod_small (round_up (secneeded nv) 4096 + 8191)) by lia.
    rewrite land_page by lia. rewrite MS.
    destruct (proj1 (Z.mod_divide (round_up (secneeded nv) 4096) 4096 ltac:(lia)) RM2) as [q Hq]. rewrite Hq.
    replace (q * 4096 + 8191) with (4095 + (q + 1) * 4096) by lia. rewrite Z.mod_add by lia. change (4095 mod 4096) with 4095. lia. }
  change (CS1 W st tmax) with (upd W st tmax (ES1 W st tmax) 0x706a0 [(11%nat, SVar V_MS)] [] false []). unfold upd. cbv zeta.
  revert WC1 DC1 NXC1. unfold CS1, upd. cbv zeta. intros WC1 DC1 NXC1.
  eapply SPA_restate; [exact WC1 | exact DC1 | exact NXC1 | | constructor | exact H].
  constructor; [exact EA | constructor].
Qed.
End C2.

Section C3.
Hypothesis IC1 : instr_at segsA (ss_pc (ax_S (CS1 W st tmax))) = Some Ecall.
Hypothesis R17 : reg_sv (ax_S (CS1 W st tmax)) 17 = SLit 222.
Hypothesis R11 : reg_sv (ax_S (CS1 W st tmax)) 11 = SVar V_MS.
Hypothesis R10 : reg_sv (ax_S (CS1 W st tmax)) 10 = SLit 0.
Hypothesis R12 : reg_sv (ax_S (CS1 W st tmax)) 12 = SLit 3.
Hypothesis R13 : reg_sv (ax_S (CS1 W st tmax)) 13 = SLit 34.
Hypothesis R14 : reg_sv (ax_S (CS1 W st tmax)) 14 = SLit 18446744073709551615.
Hypothesis R15 : reg_sv (ax_S (CS1 W st tmax)) 15 = SLit 0.
Hypothesis NX1 : ss_next (ax_S (CS1 W st tmax)) = NW2.
Hypothesis XC1 : ax_X (CS1 W st tmax) = [].
Hypothesis SK1 : map skel (ss_objs (ax_S (CS1 W st tmax))) = map skel (((sw_s1 :: unwind_objs W ++ A_globals) ++ RT_m1) ++ RT_sec).
Hypothesis FC1 : incl ((((unwind_factsS W st ++ pre_facts malloc_depth) ++ F_geom_fn) ++ F_s1) ++ F_fam tmax 8) (ss_facts (ax_S (CS1 W st tmax))).

Theorem sec_ecall : forall (ok : world -> Prop) (A : AA) (Kc : KcA) (Jo : word -> jpredA) rho tp (Q : assn),
  (st = UStopLeOrPc -> W = []) -> stopJ_stable W st -> Kc_ok Kc ->
  ok_frameA segs ok (liftKA Kc) -> ok_pframeA segs ok (liftKA Kc) ->
  (forall rhoX tr ms md a, smatch_pendingA segs rhoX tp (CS1 W st tmax) (tr, mkCfg ms md) -> JG W st A Kc rho rhoX tp tr md ->
     mmap_place_ok (ms_gpr ms 0) (ms_gpr ms 3) md (ms_gpr ms 1) a ->
     Jo a (rho_set_rw rhoX (ss_next (ax_S (CS1 W st tmax))) a) tp tr (with_vmmaps (mmap_rw_vm (m_vmmaps md) (ms_gpr ms 1) a) md)) ->
  (forall rhoX, triple segs ok (SPA segs (JG W st A Kc rho) (ES1f W st tmax) rhoX tp) Q) ->
  (forall rhoX (a : word), triple segs ok (SPA segs (Jo a) (ES1g W st tmax) (rho_set_rw rhoX (nxS W st tmax) a) tp) Q) ->
  forall rhoX, triple segs ok (SPA segs (JG W st A Kc rho) (CS1 W st tmax) rhoX tp) Q.
Proof.
  intros ok A Kc Jo rho tp Q HW HUS HKc Hokl Hokpl HJo HF HGR rhoX.
  set (nv := bv_unsigned (rw rho 12%positive)).
  assert (Hokf : ok_frameA segs ok (JG W st A Kc rho)).
  { intros r t tr ms md msv' [_ HJ]. apply (Hokl r t tr ms md msv'). destruct HJ as (_ & HK & _). exact HK. }
  assert (Hokp : ok_pframeA segs ok (JG W st A Kc rho)).
  { apply (ok_pframeA_liftKA segs ok Kc). exact Hokpl. intros r t tr md [_ HJ]. destruct HJ as (_ & HK & _). exact HK. }
  pose proof (JG_stable nW st A Kc rho HUS HKc) as HST.
  pose proof (topG_range (aa_geom A)) as ACV.

  apply (triple_pre_pure segs ok _ _ (rw rhoX 142%positive = Z_to_bv 64 (secmapsize nv) /\ 64513 <= nv < 2 ^ 39)).
  { intros w Hw. destruct w as [tr [ms md]]. pose proof (JG_rigidS A Kc rho rhoX tp tr md (proj2 Hw)) as (E12 & _ & E142 & _).
    split; [exact E142|]. destruct (proj2 Hw) as [_ HJ]. destruct HJ as (_ & _ & _ & _ & _ & HN & _). cbn [eval] in HN. rewrite E12 in HN.
    pose proof (fact_of_state nW st A Kc rho rhoX tp _ (CS1 W st tmax) (SPUle (SLit (rzf_lo 8)) (SVar 12)) Hw
                  ltac:(apply FC1; apply in_or_app; right; unfold F_fam; cbn; tauto)) as F.
    cbn [holds eval rzf_lo] in F. rewrite E12, u64_lit in F by lia. fold nv in F, HN. clear -F HN. lia. }
  intros [E142 Hnv].
  pose proof (round_up_ge' nv 8 ltac:(lia)) as RU1. pose proof (round_up_ge' (secneeded nv) PG ltac:(unfold PG; lia)) as RU2.
  pose proof (round_up_mod (secneeded nv) PG ltac:(unfold PG; lia)) as RM2. unfold PG in RU2, RM2.
  assert (NS : secneeded nv = round_up nv 8 + 4096) by reflexivity.
  assert (MS : secmapsize nv = round_up (secneeded nv) 4096 + 4096) by reflexivity.
  assert (BMS : nv + 8192 <= secmapsize nv <= nv + 12294 /\ secmapsize nv mod 4096 = 0).
  { rewrite MS. split; [lia|]. rewrite Z.add_mod, RM2 by lia. reflexivity. }
  apply triple1_triple.
  eapply triple1_seq_l.
  2: { apply triple_disj; [exact (HF rhoX)|]. apply triple_ex. intros a. exact (HGR rhoX a). }
  unfold ES1f, ES1g, nxS. replace (SLit (2 ^ 64 - 12)) with (SLit (bv_unsigned (errno_ret ENOMEM))) by reflexivity.
  change (mkObj (SVar (ss_next (ax_S (CS1 W st tmax)))) (SLit 0) (SVar V_MS) [] DZero) with (mmap_obj_sym (ss_next (ax_S (CS1 W st tmax))) (SVar V_MS)).
  assert (HST' : stableA segs (ss_next (ax_S (CS1 W st tmax))) (JG W st A Kc rho)).
  { rewrite NX1. eapply stableA_mono; [|exact HST]. unfold GW, NW2. clear; lia. }
  assert (HB11 : sv_below (ss_next (ax_S (CS1 W st tmax))) (SVar V_MS) = true) by (rewrite NX1; reflexivity).
  assert (HEV : bv_unsigned (eval rhoX (SVar V_MS)) = secmapsize nv).
  { cbn [eval]. unfold V_MS. rewrite E142. apply u64_lit. clear -BMS Hnv. lia. }
  apply (triple1_mmap_rw_symA segs ok (JG W st A Kc rho) (JG W st A Kc rho) Jo (CS1 W st tmax) rhoX tp (SVar V_MS) (secmapsize nv)
           Hokf Hokp HST' IC1 R17 R11 HB11 HEV (proj2 BMS) ltac:(clear -BMS Hnv; lia)).
  intros tr ms md Hsp HJG.
  destruct (pending_argsA segs rhoX tp (CS1 W st tmax) tr ms md Hsp) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5).
  rewrite R10 in Q0. rewrite R11 in Q1. rewrite R12 in Q2. rewrite R13 in Q3. rewrite R14 in Q4. rewrite R15 in Q5. cbn [eval] in Q0, Q1, Q2, Q3, Q4, Q5.
  split; [rewrite Q2, Q3, Q5; apply mmap_modeled_b_intro; reflexivity|].
  split; [rewrite Q3; reflexivity|].
  pose proof (JG_rigidS A Kc rho rhoX tp tr md HJG) as (E12 & E141 & _ & E151 & E152 & E153 & E154 & E155 & E156 & E145 & E146 & E147 & Erm & Erl & Elow).
  pose proof HJG as [_ HJ]. destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop).
  pose proof HA as (HG & HR & HFI & HRest & HM & HI3 & HBT).
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & _).
  pose proof (geom_top _ HG) as GTOP. pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HM))))))) as TOPm.

  split.
  { destruct (AInvA_budget A _ _ _ HA) as (PB & VL & V0 & K0 & F0). unfold headroom. rewrite VL.
    unfold budget_ok_alloc, limit_ok_alloc in HB. cbn [eval] in HB. rewrite E12 in HB. fold nv in HB.
    unfold budget_bound in PB. pose proof (acost_step (aa_V A) nv V0 ltac:(lia)) as AS. unfold BETA_M, BETA_F in *. clear -PB HB AS BMS Hnv. lia. }
  split; [exact HJG|].
  intros a Hpl.
  pose proof (mmap_len_sym segs rhoX tp (CS1 W st tmax) tr ms md (SVar V_MS) (secmapsize nv) Hsp R11 ltac:(cbn [eval]; unfold V_MS; rewrite E142; apply u64_lit; lia) (proj2 BMS) ltac:(lia)) as [_ HnZ].
  pose proof (law_res _ _ _ _ HA) as Hres.
  destruct (grant_facts_A _ _ md _ a Hpl Hres) as (Gal & Gpos & Gceil & Gimg & Gmaps). rewrite HnZ in Gceil, Gimg, Gmaps.
  pose proof (urange a) as Ra. set (ua := bv_unsigned a) in *.

  destruct HM as (VG & _). destruct VG as (_ & _ & MT & MC & MD & MF & _).
  assert (MISS : forall lo hi, in_maps (m_vmmaps md) lo hi -> forall x, ua <= x < ua + secmapsize nv -> ~ (lo <= x < hi)).
  { intros lo hi (e & He & Hlo & Hhi) x Hx Hin. destruct e as [b m]. cbn [fst snd] in Hlo, Hhi. apply (Gmaps b m He x Hx). lia. }
  pose proof (MISS _ _ MT) as MT'. pose proof (MISS _ _ MC) as MC'. pose proof (MISS _ _ MD) as MD'. pose proof (MISS _ _ MF) as MF'.
  assert (ZFREE : forall x, rt_zoneG (aa_geom A) x -> ~ (ua <= x < ua + secmapsize nv)).
  { intros x Hz Hx. destruct Hz as [Z1|[Z2|[Z3|[Z4|Z5]]]].
    - apply (Gimg x Hx). unfold IMG_HI in Z1. lia.
    - exact (MT' x Hx Z2). - exact (MC' x Hx Z3). - exact (MD' x Hx Z4). - exact (MF' x Hx Z5). }
  split; [|split; [|split]].
  -
    pose proof (smatch_pendingA_sp segs _ _ _ _ _ _ Hsp) as Hsm0.
    pose proof (smatch_pending_facts segs _ _ _ _ _ Hsm0) as HFall.
    assert (HFX : forall p, In p (unwind_factsS W st ++ pre_facts malloc_depth) -> holds rhoX p).
    { intros p Hp. refine (proj1 (Forall_forall _ _) HFall p (FC1 p _)). apply in_or_app; left. apply in_or_app; left. apply in_or_app; left. exact Hp. }
    assert (Hhigh : holds rhoX F_sp_high) by (apply HFX; apply in_or_app; right; cbn; tauto).
    assert (Hall : Forall (obj_holds segs rhoX (vms md tp ms)) (ss_objs (ax_S (CS1 W st tmax)))).
    { destruct Hsm0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). exact Hall. }
    destruct (skel_head _ sw_s1 (((unwind_objs W ++ A_globals) ++ RT_m1) ++ RT_sec) SK1) as (o0 & rest & EO & SK0 & SKR).
    rewrite EO in Hall. rewrite EO.
    pose proof (sw_range_holds segs rhoX _ _ o0 Hall ltac:(left; reflexivity) SK0 Hhigh) as (SW1 & SW2 & SW3).
    assert (SW0 : topG (aa_geom A) <= fst (obj_range rhoX o0)) by (rewrite (sw_lo_gen rhoX o0 SK0); exact Htop).
    assert (LNK : Forall (fun o => topG (aa_geom A) + 16 <= bv_unsigned (eval rhoX (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0) (unwind_objs W)).
    { apply (unwind_objs_above _ _ (topG (aa_geom A))); [|clear -SW0 SW2 SW3; lia|clear -ACV; lia]. apply Forall_forall. intros p Hp.
      assert (Hp' : In p (unwind_factsS W st)).
      { destruct st; [apply chain_pre_in; exact Hp|]. rewrite (HW eq_refl) in Hp. destruct Hp. }
      apply HFX. apply in_or_app; left. exact Hp'. }
    intros o Ho. pattern o. revert o Ho. apply (proj1 (Forall_forall (fun o => ranges_disjoint (obj_range rhoX o) (ua, ua + secmapsize nv)) (o0 :: rest))).
    constructor.
    { unfold ranges_disjoint. right; right; right. cbn [fst snd]. clear -SW0 Gceil TOPm GTOP. lia. }
    apply (Forall_ranges_skel rhoX (fun r => ranges_disjoint r (ua, ua + secmapsize nv)) _ _ SKR).
    rewrite <- !app_assoc. apply Forall_app. split.
    { eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B & L & Hh). cbn [ob_base ob_lo ob_hi] in B, L, Hh. subst olo ohi.
      unfold ranges_disjoint. rewrite obj_range_mk by (clear -B; lia). cbn [fst snd]. clear -B Gceil TOPm GTOP. lia. }
    apply Forall_app. split.
    { unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI. repeat apply Forall_cons; try apply Forall_nil;
        unfold ranges_disjoint; rewrite obj_range_mk by lia; cbn [fst snd eval]; rewrite u64_lit by lia.
      - destruct (Z_lt_dec (ua + secmapsize nv) (0xe4868 + 1)) as [L|L]; [lia|]. destruct (Z_lt_dec 0xe5608 (ua + 1)) as [L2|L2]; [lia|].
        exfalso. destruct (Z_le_dec ua 0xe4868); [apply (Gimg 0xe4868); lia | apply (Gimg ua); lia].
      - destruct (Z_lt_dec (ua + secmapsize nv) (0xee0b8 + 1)) as [L|L]; [lia|]. destruct (Z_lt_dec 0xee0c4 (ua + 1)) as [L2|L2]; [lia|].
        exfalso. destruct (Z_le_dec ua 0xee0b8); [apply (Gimg 0xee0b8); lia | apply (Gimg ua); lia]. }
    assert (ZR : forall lo hi, (forall x, lo <= x < hi -> rt_zoneG (aa_geom A) x) -> ranges_disjoint (lo, hi) (ua, ua + secmapsize nv)).
    { intros lo hi Hz. unfold ranges_disjoint. cbn [fst snd].
      destruct (Z_lt_dec (ua + secmapsize nv) (lo + 1)) as [L|L]; [lia|]. destruct (Z_lt_dec hi (ua + 1)) as [L2|L2]; [lia|].
      destruct (Z_le_dec hi lo) as [L3|L3]; [lia|]. exfalso.
      destruct (Z_le_dec ua lo); [apply (ZFREE lo); [apply Hz; lia | lia] | apply (ZFREE ua); [apply Hz; lia | lia]]. }
    apply Forall_app. split.
    { rewrite <- N_m1_ok. apply Forall_forall. intros o Ho'. apply in_map_iff in Ho' as (k & <- & Hk).
      rewrite (carve_range rhoX k (proj1 (Forall_forall _ _) N_m1_small k Hk)).
      destruct (spec_range rhoX k) as [lo hi] eqn:ER. apply ZR. intros x Hx. apply (N_m1_zoneG (aa_geom A) rhoX k x HG E151 E152 Hk). rewrite ER. exact Hx. }
    { unfold RT_sec. apply Forall_forall. intros o Ho'. apply in_map_iff in Ho' as (k & <- & Hk).
      rewrite (carve_range rhoX k (proj1 (Forall_forall _ _) N_sec_small k Hk)).
      destruct (spec_range rhoX k) as [lo hi] eqn:ER. apply ZR. intros x Hx. apply (N_sec_zone (aa_geom A) rhoX k x E151 ltac:(lia) Hk). rewrite ER. exact Hx. }
  -
    intros x Hx. apply (grant_no_ro_A a (secmapsize nv)); [exact Gimg | exact Hx].
  -
    rewrite XC1. intros r y [].
  -
    exact (HJo rhoX tr ms md a Hsp HJG Hpl).
Qed.
End C3.

Section C4.
Hypothesis CertSf : check_cfgA segsA 4000%nat [0x5e52c] GW [ES1f W st tmax] [ESn W st tmax] = true.
Theorem sec_certf : forall (ok : world -> Prop) (A : AA) (Kc : KcA) rho tp (Q : assn),
  stopJ_stable W st -> Kc_ok Kc -> ok_frameA segs ok (J W st A Kc) ->
  (forall rhoX, triple segs ok (SPA segs (JG W st A Kc rho) (ESn W st tmax) rhoX tp) Q) ->
  forall rhoE, triple segs ok (SPA segs (JG W st A Kc rho) (ES1f W st tmax) rhoE tp) Q.
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf HR rhoE.
  apply (cfg_soundA segs 4000%nat [0x5e52c] GW [ES1f W st tmax] [ESn W st tmax] (JG W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. exact (Hokf r t tr ms md msv' HJ HMI Hh Hp Hs).
  - apply JG_stable; [exact HUS | exact HKc].
  - exact CertSf.
  - intros E rhoX HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | apply HR].
  - left. reflexivity.
Qed.
End C4.

Lemma N_secc_coverb : forallb coverb N_secc = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma N_secc_small : Forall spec_small N_secc.
Proof.
  unfold N_secc, spec_small. unfold SEC_INST.
  repeat apply Forall_cons; try apply Forall_nil; (split; [lia|]); (split; [lia|]); (split; [lia|]); unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia.
Qed.
Lemma N_secn_small : Forall spec_small N_secn.
Proof.
  unfold N_secn, spec_small. unfold SEC_INST, ERRNO_A.
  repeat apply Forall_cons; try apply Forall_nil; (split; [lia|]); (split; [lia|]); (split; [lia|]); unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia.
Qed.
Lemma N_secc_sub : forall k, In k N_secc -> In k N_secn.
Proof. intros k Hk. unfold N_secc in Hk. unfold N_secn. cbn [In] in Hk |- *. tauto. Qed.
Lemma K_seci_in : In K_seci N_secn.
Proof. unfold K_seci, C_seci, N_secn. cbn [In]. tauto. Qed.

Lemma absorb_spec_view_sub : forall sgs rho S tr ms md objs R base lo hi cs rdv lo' hi',
  smatch sgs rho S (tr, mkCfg ms md) -> ss_objs S = objs ++ R -> In (carved base lo hi cs) R -> spec_small (base, lo, hi, cs) ->
  cells_in_view rho rdv (bv_unsigned (eval rho base)) cs ->
  (forall off, lo' <= off < hi' -> exists o n e, In (o, n, e) cs /\ o <= off < o + Z.of_nat n) ->
  forall z, bv_unsigned (eval rho base) + lo' <= z < bv_unsigned (eval rho base) + hi' ->
  rd_of sgs (rm (rho_absorb rho R ms)) (Z_to_bv 64 z) = rdv (Z_to_bv 64 z).
Proof.
  intros sgs rho S tr ms md objs R base lo hi cs rdv lo' hi' Hsm Ho Hin (S1 & S2 & S3 & S4) Hciv Hcov z Hz.
  destruct (absorb_carved_cells sgs rho S tr ms md objs R base lo hi cs Hsm Ho Hin ltac:(lia) ltac:(lia) ltac:(lia) S4) as [C _].
  rewrite eval_absorb in C |- * || idtac.
  replace z with (bv_unsigned (eval rho base) + (z - bv_unsigned (eval rho base))) by lia.
  apply (view_eq_cells (rho_absorb rho R ms) _ rdv (bv_unsigned (eval rho base)) cs lo' hi'); [exact C | | exact Hcov | lia].
  unfold cells_in_view in *. apply Forall_forall. intros [[o n] e] Hin' j Hj. rewrite eval_absorb. exact (proj1 (Forall_forall _ _) Hciv _ Hin' j Hj).
Qed.
Lemma C_seci_cov_lo : forall off, SEC_INST <= off < SEC_INST + 32 -> exists o n e, In (o, n, e) C_seci /\ o <= off < o + Z.of_nat n.
Proof.
  intros off Hoff. unfold C_seci, SEC_INST in *.
  destruct (Z_lt_dec off (0xeaa98 + 8)); [do 3 eexists; split; [cbn; left; reflexivity | cbn; lia]|].
  destruct (Z_lt_dec off (0xeaa98 + 16)); [do 3 eexists; split; [cbn; right; left; reflexivity | cbn; lia]|].
  destruct (Z_lt_dec off (0xeaa98 + 24)); [do 3 eexists; split; [cbn; right; right; left; reflexivity | cbn; lia]|].
  do 3 eexists; split; [cbn; right; right; right; left; reflexivity | cbn; lia].
Qed.
Lemma C_seci_cov_hi : forall off, SEC_INST + 48 <= off < SEC_INST + 64 -> exists o n e, In (o, n, e) C_seci /\ o <= off < o + Z.of_nat n.
Proof.
  intros off Hoff. unfold C_seci, SEC_INST in *.
  destruct (Z_lt_dec off (0xeaa98 + 56)); [do 3 eexists; split; [cbn; do 4 right; left; reflexivity | cbn; lia]|].
  do 3 eexists; split; [cbn; do 5 right; left; reflexivity | cbn; lia].
Qed.

Lemma N_secc_civ : forall A rho tp md,
  AInv A rho tp md ->
  rw rho 145%positive = Z_to_bv 64 (ag_pab (aa_geom A)) -> rw rho 146%positive = Z_to_bv 64 (aa_ptr_committed A / 8) ->
  rw rho 147%positive = Z_to_bv 64 (Z.of_nat (length (aa_sec A))) ->
  Forall (fun k : carve_spec => let '(base, lo, hi, cs) := k in cells_in_view rho (rd_of segs (rm rho)) (bv_unsigned (eval rho base)) cs) N_secc
  /\ cells_in_view rho (rd_of segs (rm rho)) (bv_unsigned (eval rho (SLit 0))) C_seci.
Proof.
  intros A rho tp md HA E145 E146 E147.
  pose proof HA as (HG & HR & HF & HRest & HM & _).
  destruct HRest as (_ & _ & _ & Hsec & _ & _ & _ & _ & HMI).
  destruct Hsec as (_ & _ & SC2 & SC3 & SC45 & I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9). destruct HMI as (HMIc & _ & _).
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HMIc))))) as HSAN.
  assert (IMG : forall z, z < 0x643000 -> maskv (fs_footb (aa_geom A)) (view segs (rm rho)) z = view segs (rm rho) z).
  { intros z Hz. apply maskv_out. apply fs_footb_img; [exact HG | exact Hz]. }
  assert (CI : forall a k v, a + Z.of_nat k <= 0x643000 -> cell_ok (maskv (fs_footb (aa_geom A)) (view segs (rm rho))) (mkACell a k v) ->
               cell_ok (view segs (rm rho)) (mkACell (0 + a) k v)).
  { intros a k v Ha Hc j Hj. specialize (Hc j Hj). cbn [c_addr c_w c_val] in Hc, Hj |- *. rewrite Z.add_0_l. rewrite IMG in Hc; [exact Hc | lia]. }
  unfold SEC_INST in *.
  pose proof (urange (rw rho 145%positive)) as U145. pose proof (urange (rw rho 146%positive)) as U146. pose proof (urange (rw rho 147%positive)) as U147.
  unfold N_secc, C_seci, SEC_INST. split.
  - repeat apply Forall_cons; try apply Forall_nil; cbv beta iota zeta; cbn [eval]; rewrite (u64_lit 0) by lia;
      unfold cells_in_view; repeat apply Forall_cons; try apply Forall_nil.
    + exact (civ_cell rho (rm rho) 0 0xead00 4 0 (SLit 0) (CI 0xead00 4%nat 0 ltac:(cbn; lia) I8) eq_refl ltac:(lia) ltac:(cbn; lia)).
    + exact (civ_cell rho (rm rho) 0 0xe67b8 8 0x1a309 (SLit 0x1a309) (CI 0xe67b8 8%nat 0x1a309 ltac:(cbn; lia) HSAN) eq_refl ltac:(lia) ltac:(cbn; lia)).
  - cbn [eval]. rewrite (u64_lit 0) by lia. unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
    + exact (civ_cell rho (rm rho) 0 0xeaa98 8 PG (SLit 4096) (CI 0xeaa98 8%nat PG ltac:(cbn; lia) I1) eq_refl ltac:(lia) ltac:(cbn; lia)).
    + refine (civ_cell rho (rm rho) 0 0xeaaa0 8 (ag_pab (aa_geom A)) (SVar V_PAB) (CI (0xeaa98 + 8) 8%nat (ag_pab (aa_geom A)) ltac:(cbn; lia) I2) _ ltac:(lia) ltac:(cbn; lia)). cbn [eval]. unfold V_PAB. exact E145.
    + refine (civ_cell rho (rm rho) 0 0xeaaa8 8 (ag_pab (aa_geom A)) (SVar V_PAB) (CI (0xeaa98 + 16) 8%nat (ag_pab (aa_geom A)) ltac:(cbn; lia) I3) _ ltac:(lia) ltac:(cbn; lia)). cbn [eval]. unfold V_PAB. exact E145.
    + exact (civ_cell rho (rm rho) 0 0xeaab0 8 kPtrArrayReserve (SLit (2 ^ 23)) (CI (0xeaa98 + 24) 8%nat kPtrArrayReserve ltac:(cbn; lia) I4) eq_refl ltac:(lia) ltac:(cbn; lia)).
    + refine (civ_cell rho (rm rho) 0 0xeaac8 8 (aa_ptr_committed A / 8) (SVar V_NRES) (CI (0xeaa98 + 48) 8%nat (aa_ptr_committed A / 8) ltac:(cbn; lia) I5) _ ltac:(lia) ltac:(cbn; lia)). cbn [eval]. unfold V_NRES. exact E146.
    + refine (civ_cell rho (rm rho) 0 0xeaad0 8 (Z.of_nat (length (aa_sec A))) (SVar V_NCH) (CI (0xeaa98 + 56) 8%nat (Z.of_nat (length (aa_sec A))) ltac:(cbn; lia) I6) _ ltac:(lia) ltac:(cbn; lia)). cbn [eval]. unfold V_NCH. exact E147.
Qed.

Section C5.
Hypothesis RN : R_n W st tmax = RT_m1 ++ map carve_obj N_secn.
Hypothesis WRn : swf (stRn_S W st tmax) = true.
Hypothesis DKRn : state_diff (ax_S (stKn W st tmax)) (stRn_S W st tmax) = Some ([(SLit TP_A, SVar 24)], []).
Hypothesis NXRn : ss_next (stRn_S W st tmax) = ss_next (ax_S (stKn W st tmax)).
Hypothesis ENTn : entailsA (stRn W st tmax) (L_malloc_null AE_A W st) (s_n W st tmax) = true.
Hypothesis IDn : wsub_id_below (s_n W st tmax) NF = true.

Theorem sec_null_finish : forall (A : AA) (Kc : KcA) rho tp w rhoY Posts,
  Kc_ok Kc -> In (L_malloc_null AE_A W st, JL_malloc_null AInv CST XGL A Kc) Posts ->
  SPA segs (JG W st A Kc rho) (ESn W st tmax) rhoY tp w ->
  LQPA segs NF rho tp Posts w.
Proof.
  intros A Kc rho tp w rhoY Posts HKc HPosts H. destruct w as [tr [ms md]].
  pose proof H as [HsmA [Hag HJ]]. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (JG_rigidS A Kc rho rhoY tp tr md (proj2 H)) as (E12 & E141 & E142 & E151 & E152 & E153 & E154 & E155 & E156 & E145 & E146 & E147 & Erm & Erl & Elow).
  destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN. rewrite E12 in HN.
  set (nv := bv_unsigned (rw rho 12%positive)) in *.
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HBT).
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & _). pose proof (topG_range (aa_geom A)) as ACV.

  set (KJ := (fun (_ : valuation) (_ : list word) (t : list event) (m : Model) => Kc t m) : jpredA).
  assert (Ha : SPA segs KJ (ESn W st tmax) rhoY tp (tr, mkCfg ms md)) by (split; [exact HsmA | exact HK]).
  assert (EOBJ : ss_objs (ax_S (ESn W st tmax)) = firstn (NOBJ W) (ss_objs (ax_S (ESn W st tmax))) ++ R_n W st tmax).
  { unfold R_n. symmetry. apply firstn_skipn. }
  pose proof (SPA_unobj segs KJ rhoY (ESn W st tmax) _ _ tp tr ms md EOBJ Ha (fun k => k)) as Hb.
  cbn zeta in Hb. set (R := R_n W st tmax) in *. set (rho3 := rho_absorb rhoY R (vms md tp ms)) in *.
  change (ax_setS (ESn W st tmax) (set_objs (ax_S (ESn W st tmax)) (firstn (NOBJ W) (ss_objs (ax_S (ESn W st tmax)))))) with (stKn W st tmax) in Hb.
  pose proof (proj1 (proj1 Ha)) as Hsm1. unfold virt in Hsm1. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm1.

  assert (AO : forall o, In o R -> _) by (intros o Ho; exact (absorb_obj rhoY _ tr (vms md tp ms) (vmd md) _ R o Hsm1 EOBJ Ho)).
  assert (NK : forall k, In k (N_m1 ++ N_secc) -> In (carve_obj k) R /\ spec_small k /\ spec_covered k
            /\ cells_in_view rhoY (rd_of segs (rm rhoY)) (fst (spec_range rhoY k) - (let '(_, lo, _, _) := k in lo)) (let '(_, _, _, cs) := k in cs)).
  { intros k Hk. apply in_app_or in Hk as [Hk|Hk].
    - split; [rewrite RN; apply in_or_app; left; rewrite <- N_m1_ok; apply in_map; exact Hk|].
      split; [exact (proj1 (Forall_forall _ _) N_m1_small k Hk)|].
      split; [apply coverb_sound; exact (proj1 (forallb_forall _ _) N_m1_coverb k Hk)|].
      pose proof (proj1 (Forall_forall _ _) (N_m1_civ AInvA_die A rhoY tp md HA E151 E152 E153 E154 E155 E156) k Hk) as CV. cbn beta in CV.
      destruct k as [[[base lo] hi] cs]. cbn [spec_range fst]. replace (bv_unsigned (eval rhoY base) + lo - lo) with (bv_unsigned (eval rhoY base)) by (clear; lia). exact CV.
    - split; [rewrite RN; apply in_or_app; right; apply in_map; exact (N_secc_sub k Hk)|].
      split; [exact (proj1 (Forall_forall _ _) N_secc_small k Hk)|].
      split; [apply coverb_sound; exact (proj1 (forallb_forall _ _) N_secc_coverb k Hk)|].
      pose proof (proj1 (Forall_forall _ _) (proj1 (N_secc_civ A rhoY tp md HA E145 E146 E147)) k Hk) as CV. cbn beta in CV.
      destruct k as [[[base lo] hi] cs]. cbn [spec_range fst]. replace (bv_unsigned (eval rhoY base) + lo - lo) with (bv_unsigned (eval rhoY base)) by (clear; lia). exact CV. }

  assert (ET : bv_unsigned (eval rhoY vT) = ag_thread (aa_geom A)) by (unfold vT; cbn [eval]; rewrite E151; apply u64_lit; lia).
  assert (INR : forall a, in_ranges rhoY R a ->
            (exists k, In k (N_m1 ++ N_secc) /\ fst (spec_range rhoY k) <= bv_unsigned a < snd (spec_range rhoY k))
            \/ znull (aa_geom A) (bv_unsigned a) \/ bv_unsigned a = 0x170321
            \/ (SEC_INST <= bv_unsigned a < SEC_INST + 32 \/ SEC_INST + 48 <= bv_unsigned a < SEC_INST + 64)).
  { intros a (o & HoR & Hr). rewrite RN in HoR. apply in_app_or in HoR as [HoR|HoR].
    - left. rewrite <- N_m1_ok in HoR. apply in_map_iff in HoR as (k & <- & Hk). exists k. split; [apply in_or_app; left; exact Hk|].
      rewrite (carve_range rhoY k (proj1 (Forall_forall _ _) N_m1_small k Hk)) in Hr. exact Hr.
    - apply in_map_iff in HoR as (k & <- & Hk). rewrite (carve_range rhoY k (proj1 (Forall_forall _ _) N_secn_small k Hk)) in Hr.
      unfold N_secn in Hk. cbn [In] in Hk. unfold znull.
      destruct Hk as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]; subst k; cbn [spec_range fst snd eval] in Hr; rewrite ?(u64_lit 0), ?ET in Hr by lia;
        unfold SEC_INST, ERRNO_A in *.
      +   clear -Hr. lia.
      + right; left. lia.
      + left. eexists. split; [apply in_or_app; right; cbn; left; reflexivity|]. cbn [spec_range fst snd eval]. rewrite (u64_lit 0) by lia. exact Hr.
      + right; left. lia.
      + left. eexists. split; [apply in_or_app; right; cbn; right; left; reflexivity|]. cbn [spec_range fst snd eval]. rewrite (u64_lit 0) by lia. exact Hr.
      + destruct (Z.eq_dec (bv_unsigned a) 0x170321); [right; right; left; assumption | right; left; lia].
      + right; left. lia.
      + right; left. lia. }

  set (vE := view segs (rm rhoY)). set (v3 := view segs (rm rho3)).
  assert (O1 : In (carve_obj (SLit 0, 0x170320, 0x170322, [(0x170320, 1%nat, SLit 1); (0x170321, 1%nat, SLit 1)])) R).
  { rewrite RN. apply in_or_app; right. apply in_map. unfold N_secn. cbn [In]. tauto. }
  assert (VO : forall z, ~ znull (aa_geom A) z -> v3 z = vE z).
  { intros z Hz. unfold v3, vE. destruct (Z_le_dec 0 z); [destruct (Z_lt_dec z (2 ^ 64))|].
    2,3: rewrite !view_out by (clear -n; lia) || rewrite !view_out by (clear -n l; lia); reflexivity.
    rewrite !view_in by (clear -l l0; lia).
    destruct (in_ranges_dec rhoY R (Z_to_bv 64 z)) as [Hin|Hout].
    - destruct (INR _ Hin) as [(k & Hk & Hr)|[Hc|[E1|SC]]]; rewrite ?u64_lit in * by (clear -l l0; lia).
      + unfold rho3. exact (absorb_specs_view rhoY _ tr (vms md tp ms) (vmd md) _ R (N_m1 ++ N_secc) (rd_of segs (rm rhoY)) Hsm1 EOBJ NK z k Hk Hr).
      + exfalso. exact (Hz Hc).
      +
        destruct (AO _ O1) as (_ & CE & _ & _). cbn [ob_cells carve_obj carved lit_cells map] in CE.
        destruct (CE _ ltac:(cbn; right; left; reflexivity)) as (_ & _ & CEj). pose proof (CEj 0%nat ltac:(cbn; lia)) as X. clear CEj.
        cbn [ob_base carved c_off c_width SymState.c_val eval] in X. change (Z.to_nat (Z.of_nat 1)) with 1%nat in X. change (Z.of_nat 0) with 0 in X.
        rewrite soff_lit_small, (u64_lit 0), Z.add_0_r in X by lia. rewrite Z.add_0_l in X. rewrite E1. unfold rho3.
        transitivity (Some (nth 0 (enc_bytes 1 (Z_to_bv 64 1)) (Z_to_bv 8 0))); [exact X|]. symmetry.
        destruct HRest as (_ & _ & _ & _ & _ & _ & _ & _ & (HMIc & _ & _)). pose proof (Forall_inv HMIc) as C9. specialize (C9 0%nat ltac:(cbn; lia)).
        cbn [c_addr c_w c_val Z.of_nat] in C9. rewrite Z.add_0_r in C9. rewrite maskv_out in C9 by (apply fs_footb_img; [exact HG | lia]). rewrite view_in in C9 by lia.
        exact C9.
      +
        pose proof (proj2 (N_secc_civ A rhoY tp md HA E145 E146 E147)) as CIVS.
        assert (HinS : In (carved (SLit 0) SEC_INST (SEC_INST + 64) C_seci) R).
        { rewrite RN. apply in_or_app; right. change (carved (SLit 0) SEC_INST (SEC_INST + 64) C_seci) with (carve_obj K_seci). apply in_map. exact K_seci_in. }
        assert (SMS : spec_small K_seci).
        { unfold K_seci, C_seci, spec_small, SEC_INST. split; [lia|]. split; [lia|]. split; [lia|]. unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia. }
        unfold rho3. destruct SC as [SC|SC].
        * apply (absorb_spec_view_sub segs rhoY _ tr (vms md tp ms) (vmd md) _ R (SLit 0) SEC_INST (SEC_INST + 64) C_seci (rd_of segs (rm rhoY)) SEC_INST (SEC_INST + 32) Hsm1 EOBJ HinS SMS CIVS C_seci_cov_lo).
          cbn [eval]. rewrite (u64_lit 0) by (clear; lia). clear -SC. lia.
        * apply (absorb_spec_view_sub segs rhoY _ tr (vms md tp ms) (vmd md) _ R (SLit 0) SEC_INST (SEC_INST + 64) C_seci (rd_of segs (rm rhoY)) (SEC_INST + 48) (SEC_INST + 64) Hsm1 EOBJ HinS SMS CIVS C_seci_cov_hi).
          cbn [eval]. rewrite (u64_lit 0) by (clear; lia). clear -SC. lia.
    - unfold rho3, rd_of. rewrite rm_absorb_out by exact Hout. reflexivity. }
  assert (PRES : forall z, znull (aa_geom A) z -> exists b, v3 z = Some b).
  { intros z Hz. unfold v3. unfold znull in Hz. unfold SEC_INST, ERRNO_A in Hz.
    assert (CS : (0xe1000 <= z < 0x643000) \/ (ag_thread (aa_geom A) + 2768 <= z < ag_thread (aa_geom A) + 3168)) by (clear -Hz; lia).
    destruct CS as [CS|CS].
    - rewrite view_in by lia. apply rd_of_imageA. exact CS.
    - assert (OS : In (carve_obj (vT, 2768, 3168, [])) R) by (rewrite RN; apply in_or_app; right; apply in_map; unfold N_secn; cbn [In]; tauto).
      destruct (AO _ OS) as (_ & _ & PR & _). unfold obj_lo_of, obj_hi_of in PR. cbn [ob_dflt carve_obj carved ob_base ob_lo ob_hi] in PR.
      rewrite !soff_lit_small in PR by lia. rewrite ET in PR.
      destruct (PR (or_introl eq_refl) (z - ag_thread (aa_geom A)) ltac:(clear -CS; lia)) as [x Hx].
      exists x. rewrite view_in by lia. replace z with (ag_thread (aa_geom A) + (z - ag_thread (aa_geom A))) by lia. exact Hx. }

  assert (Hc : SPA segs KJ (stRn W st tmax) rho3 tp (tr, mkCfg ms md)).
  { unfold stRn. eapply SPA_restate; [exact WRn | exact DKRn | exact NXRn | | constructor | exact Hb].
    constructor; [|constructor]. cbn [fst snd eval]. unfold tp_ok in Htp. apply bv_eq. rewrite u64_lit by (unfold TP_A; lia).
    unfold rho3. cbn [rho_absorb rw]. rewrite Htp. destruct (geom_old _ HG) as (_ & _ & _ & G4' & _). rewrite G4'. reflexivity. }

  pose proof (smatchA_entails segs _ _ _ rho3 tp _ ENTn (proj1 Hc)) as Hsm4.
  set (rho4 := rho_sub rho3 (s_n W st tmax)) in Hsm4.
  assert (Hlow : forall k, (k < NF)%positive -> rw rho4 k = rw rhoY k).
  { intros k Hk. unfold rho4. cbn [rho_sub rw]. rewrite (wsub_get_id _ _ _ IDn Hk). reflexivity. }
  assert (Erm4 : rm rho4 = rm rho3) by exact (rm_rho_sub' rho3 (s_n W st tmax)).
  pose proof (rhoM_agree A rho) as (RMw & RMl & RMm).

  apply (LQPA_intro segs NF rho tp _ (L_malloc_null AE_A W st) (JL_malloc_null AInv CST XGL A Kc) rho4 tp _ KJ).
  - exact HPosts.
  - split; [exact Hsm4 | exact HK].
  - split.
    + intros i Hi. rewrite (Hlow i Hi). rewrite (Elow i) by (unfold GW, NF in *; clear -Hi; lia). exact (RMw i Hi).
    + intros l. unfold rho4. cbn [rho_sub rl]. unfold rho3. cbn [rho_absorb rl]. rewrite (Erl l). reflexivity.
  - intros _. unfold JL_malloc_null. cbn [w_tr w_cfg cfg_model].
    exists (bumpVK A nv).
    assert (HA' : AInv (bumpVK A nv) rho4 tp md).
    { unfold AInv. apply (null_rebuild A rhoY rho4 tp md nv HA ltac:(clear -HN; lia)).
      - intros z Hz. rewrite Erm4. exact (VO z Hz).
      - intros z Hz. rewrite Erm4. exact (PRES z Hz). }
    split; [exact HA'|]. split; [reflexivity|]. split; [reflexivity|].
    split; [cbn [aa_V bumpVK]; subst nv; reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split.
    {
      rewrite Erm4, <- Erm.
      assert (RMO : forall a, 0 <= a < 2 ^ 64 -> ~ rt_zoneM (aa_geom A) a -> ~ znull (aa_geom A) a -> a <> 0x170321 -> ~ in_rangesZ IMG_S a ->
                      rm rho3 (Z_to_bv 64 a) = rm rhoY (Z_to_bv 64 a)).
      { intros a Ba Hz1 Hz2 Hz3 Hz4. unfold rho3. apply rm_absorb_out. intros Hin.
        destruct (INR _ Hin) as [(k & Hk & Hr)|[Hc'|[E1|SC]]]; rewrite ?u64_lit in * by exact Ba.
        - apply in_app_or in Hk as [Hk|Hk].
          + apply Hz1. exact (N_m1_zone (aa_geom A) rhoY k a HG E151 E152 Hk Hr).
          + apply Hz4. unfold N_secc in Hk. cbn [In] in Hk. unfold IMG_S, in_rangesZ. unfold SEC_INST, ERRNO_A in *.
            destruct Hk as [E|[E|[]]]; subst k; cbn [spec_range fst snd eval] in Hr; rewrite (u64_lit 0) in Hr by lia.
            * exists 0xeaa98, (0xead04 - 0xeaa98). split; [cbn; tauto | lia].
            * exists 0xe67b8, 8. split; [cbn; tauto | lia].
        - exact (Hz2 Hc').
        - exact (Hz3 E1).
        - apply Hz4. unfold IMG_S, in_rangesZ. unfold SEC_INST in *. exists 0xeaa98, (0xead04 - 0xeaa98). split; [cbn; tauto | clear -SC; lia]. }
      destruct HRest as (Hsep & _).
      assert (CA : forall a, client_addrA CST A a -> 0 <= a < 2 ^ 64 -> ~ errno_addrA a -> rm rho3 (Z_to_bv 64 a) = rm rhoY (Z_to_bv 64 a)).
      { intros a Hcl Ba NE. destruct (client_addr_bounds CST HCST A a _ HG HF Hsep Hcl) as [B1 B2].
        apply RMO; [exact Ba | exact (client_not_rtM CST HCST HCSTM A a _ HG HF Hsep Hcl) | | |].
        -
          intros Hz. pose proof (client_not_rt CST HCST A a _ HG HF Hsep Hcl) as NR. unfold znull in Hz. unfold rt_zone in NR.
          assert (HzI : (SEC_INST + 64 <= a < 0xead00) \/ (0xead08 <= a < 0xead30) \/ a = 0x170320 \/ (ERRNO_A <= a < ERRNO_A + 4) \/ (SEC_INST + 32 <= a < SEC_INST + 48))
            by (unfold SEC_INST, ERRNO_A in *; clear -Hz NR; lia).
          clear Hz. unfold SEC_INST, ERRNO_A in HzI.
          destruct (client_addr_cases CST A a _ HF Hcl) as [S|[L|[FR|[C|FL]]]].
          + clear -S HzI ACV. lia.
          + destruct L as (b & n & Hbn & Hx). destruct (Hsep b n Hbn) as (S1 & S2 & _). unfold IMG_HI in *. clear -Hx S2 HzI. lia.
          + destruct FR as (c & p & Hcp & Hp & _ & Hx). pose proof (fs_geom_nums (aa_geom A) c p HG Hcp Hp) as M. cbn zeta in M.
            rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. unfold IMG_HI in *. clear -Hx M HzI. lia.
          + apply (HCSTS a C). unfold IMG_S, in_rangesZ. unfold SEC_INST, ERRNO_A in *.
            destruct HzI as [Hz|[Hz|[Hz|[Hz|Hz]]]].
            * exists 0xeaa98, (0xead04 - 0xeaa98). split; [cbn; tauto | clear -Hz; lia].
            * exists 0xead08, (0xead30 - 0xead08). split; [cbn; tauto | clear -Hz; lia].
            * exists 0x170320, 2. split; [cbn; tauto | clear -Hz; lia].
            * exfalso. apply NE. unfold errno_addrA, ERRNO_A. clear -Hz. lia.
            * exists 0xeaa98, (0xead04 - 0xeaa98). split; [cbn; tauto | clear -Hz; lia].
          + destruct FL as (c & p & Hcp & Hp & _ & ->). pose proof (fs_geom_nums (aa_geom A) c p HG Hcp Hp) as M. cbn zeta in M.
            rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. unfold fs_flags in *. rewrite FS_kFlagsOffset_val in *. unfold IMG_HI in *. clear -M HzI. lia.
        - intros E1.
          destruct (client_addr_cases CST A a _ HF Hcl) as [S|[L|[FR|[C|FL]]]].
          + clear -S E1 ACV. lia.
          + destruct L as (b & n & Hbn & Hx). destruct (Hsep b n Hbn) as (S1 & S2 & _). unfold IMG_HI in *. clear -Hx S2 E1. lia.
          + destruct FR as (c & p & Hcp & Hp & _ & Hx). pose proof (fs_geom_nums (aa_geom A) c p HG Hcp Hp) as M. cbn zeta in M.
            rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. unfold IMG_HI in *. clear -Hx M E1. lia.
          + apply (HCSTS a C). unfold IMG_S, in_rangesZ. exists 0x170320, 2. split; [cbn; tauto | clear -E1; lia].
          + destruct FL as (c & p & Hcp & Hp & _ & ->). pose proof (fs_geom_nums (aa_geom A) c p HG Hcp Hp) as M. cbn zeta in M.
            rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. unfold fs_flags in *. rewrite FS_kFlagsOffset_val in *. unfold IMG_HI in *. clear -M E1. lia.
        - intros HI.
          assert (HIr : 0x10000 <= a < IMG_HI).
          { destruct HI as (b & n & Hbn & Hx). unfold IMG_S in Hbn. unfold SEC_INST, ERRNO_A, IMG_HI in *. cbn [In] in Hbn.
            destruct Hbn as [E|[E|[E|[E|[]]]]]; injection E; intros; subst; clear -Hx; lia. }
          unfold IMG_HI in HIr.
          exact (HCSTS a ltac:(destruct (client_addr_cases CST A a _ HF Hcl) as [S|[L|[FR|[C|FL]]]];
              [ clear -S HIr ACV; exfalso; lia
              | destruct L as (b & n & Hbn & Hx); destruct (Hsep b n Hbn) as (S1 & S2 & _); unfold IMG_HI in *; exfalso; clear -Hx S2 HIr; lia
              | destruct FR as (c & p & Hcp & Hp & _ & Hx); pose proof (fs_geom_nums (aa_geom A) c p HG Hcp Hp) as M; cbn zeta in M;
                rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M; unfold IMG_HI in *; exfalso; clear -Hx M HIr; lia
              | exact C
              | destruct FL as (c & p & Hcp & Hp & _ & ->); pose proof (fs_geom_nums (aa_geom A) c p HG Hcp Hp) as M; cbn zeta in M;
                rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M; unfold fs_flags in *; rewrite FS_kFlagsOffset_val in *; unfold IMG_HI in *; exfalso; clear -M HIr; lia ]) HI). }
      split.
      - intros a Ba Hcl. destruct Hcl as [(C1 & _ & NE)|[C1 _]]; [exact (CA a C1 Ba NE)|].
        pose proof (client_shadow_bounds CST XGL HCST HXGL A a _ HG HF Hsep C1) as B0. unfold SHADOW_OFF, HIGH_SHADOW_END in B0.
        apply RMO; [exact Ba | | | clear -B0; lia |].
        + unfold rt_zoneM, rt_zone, IMG_HI. intros [[R1|[R1|[R1|[R1|R1]]]]|R1].
          * destruct R1 as [R1 _]. clear -R1 B0. lia.
          * pose proof (geom_bands _ HG) as (WF & TB & CB & DB & _); rewrite FS_total_val in WF; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WF, TB, CB, DB. clear -R1 B0 TB. lia.
          * pose proof (geom_bands _ HG) as (WF & TB & CB & DB & _); rewrite FS_total_val in WF; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WF, TB, CB, DB. clear -R1 B0 CB. lia.
          * pose proof (geom_bands _ HG) as (WF & TB & CB & DB & _); rewrite FS_total_val in WF; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WF, TB, CB, DB. clear -R1 B0 DB. lia.
          * pose proof (geom_bands _ HG) as (WF & TB & CB & DB & _); rewrite FS_total_val in WF; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WF, TB, CB, DB. clear -R1 B0 WF. lia.
          * pose proof (IMG_M_range a R1) as IR. unfold IMG_HI in *. clear -IR B0. lia.
        + pose proof (geom_bands _ HG) as (WF & TB & CB & DB & _); rewrite FS_total_val in WF; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WF, TB, CB, DB. unfold znull, SEC_INST, ERRNO_A. clear -B0 TB. lia.
        + intros (b & n & Hbn & Hx). unfold IMG_S in Hbn. unfold SEC_INST, ERRNO_A in *. cbn [In] in Hbn.
          destruct Hbn as [E|[E|[E|[E|[]]]]]; injection E; intros; subst; clear -Hx B0; lia.
      - intros x j Hx Hj Hdef.
        assert (Bx : SHADOW_OFF <= Sh x < HIGH_SHADOW_END).
        { destruct Hx as [[C1 C2]|GX].
          - destruct (client_addr_bounds CST HCST A x _ HG HF Hsep C1) as [B _]. unfold Sh, SHADOW_OFF, HIGH_SHADOW_END. clear -B. lia.
          - destruct (HXGL x GX) as [X0 X1]. unfold IMG_HI, Sh, SHADOW_OFF, HIGH_SHADOW_END in *. clear -X0 X1. lia. }
        unfold SHADOW_OFF, HIGH_SHADOW_END in Bx.
        destruct (word_byte_range (Sh x) j ltac:(clear -Bx; lia) Hj) as (W1 & W2 & W3).
        unfold word_byte. rewrite RMO; [exact Hdef | clear -W1 W2 W3 Bx Hj; lia | | | clear -W1 W2 W3 Bx Hj; lia |].
        + unfold rt_zoneM, rt_zone, IMG_HI. intros [[R1|[R1|[R1|[R1|R1]]]]|R1].
          * destruct R1 as [R1 _]. clear -R1 W1 W2 W3 Bx Hj. lia.
          * pose proof (geom_bands _ HG) as (WF & TB & CB & DB & _); rewrite FS_total_val in WF; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WF, TB, CB, DB. clear -R1 W1 W2 W3 Bx Hj TB. lia.
          * pose proof (geom_bands _ HG) as (WF & TB & CB & DB & _); rewrite FS_total_val in WF; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WF, TB, CB, DB. clear -R1 W1 W2 W3 Bx Hj CB. lia.
          * pose proof (geom_bands _ HG) as (WF & TB & CB & DB & _); rewrite FS_total_val in WF; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WF, TB, CB, DB. clear -R1 W1 W2 W3 Bx Hj DB. lia.
          * pose proof (geom_bands _ HG) as (WF & TB & CB & DB & _); rewrite FS_total_val in WF; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WF, TB, CB, DB. clear -R1 W1 W2 W3 Bx Hj WF. lia.
          * pose proof (IMG_M_range _ R1) as IR. unfold IMG_HI in *. clear -IR W1 W2 W3 Bx Hj. lia.
        + pose proof (geom_bands _ HG) as (WF & TB & CB & DB & _); rewrite FS_total_val in WF; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WF, TB, CB, DB. unfold znull, SEC_INST, ERRNO_A. clear -W1 W2 W3 Bx Hj TB. lia.
        + intros (b & n & Hbn & Hy). unfold IMG_S in Hbn. unfold SEC_INST, ERRNO_A in *. cbn [In] in Hbn.
          destruct Hbn as [E|[E|[E|[E|[]]]]]; injection E; intros; subst; clear -Hy W1 W2 W3 Bx Hj; lia. }
    split; [exact HK|].
    intros c0 Hc0 Hor Hfr. unfold class_fresh in Hfr |- *. cbn [aa_cls bumpVK]. exact Hfr.
Qed.
End C5.

Section C6.
Hypothesis Wa : swf (SSa_S W st tmax) = true.
Hypothesis Da : state_diff (ax_S (E_s1 W st tmax 8)) (SSa_S W st tmax) = Some ([(neededx 8, SVar V_NS); (neededx 8, SVar V_NS)], []).
Hypothesis Wb : swf (SSb_S W st tmax) = true.
Hypothesis FB : forallb (sprop_below NW2) F_sgen = true.
Hypothesis CertS1 : check_cfgA segsA 4000%nat [0x706a0] GW [SS0 W st tmax] [ES1 W st tmax] = true.
Hypothesis WC1 : swf (ax_S (CS1 W st tmax)) = true.
Hypothesis DC1 : state_diff (ax_S (ES1 W st tmax)) (ax_S (CS1 W st tmax)) = Some ([(a1x, SVar V_MS)], []).
Hypothesis NXC1 : ss_next (ax_S (CS1 W st tmax)) = ss_next (ax_S (ES1 W st tmax)).
Hypothesis IC1 : instr_at segsA (ss_pc (ax_S (CS1 W st tmax))) = Some Ecall.
Hypothesis R17 : reg_sv (ax_S (CS1 W st tmax)) 17 = SLit 222.
Hypothesis R11 : reg_sv (ax_S (CS1 W st tmax)) 11 = SVar V_MS.
Hypothesis R10 : reg_sv (ax_S (CS1 W st tmax)) 10 = SLit 0.
Hypothesis R12 : reg_sv (ax_S (CS1 W st tmax)) 12 = SLit 3.
Hypothesis R13 : reg_sv (ax_S (CS1 W st tmax)) 13 = SLit 34.
Hypothesis R14 : reg_sv (ax_S (CS1 W st tmax)) 14 = SLit 18446744073709551615.
Hypothesis R15 : reg_sv (ax_S (CS1 W st tmax)) 15 = SLit 0.
Hypothesis NX1 : ss_next (ax_S (CS1 W st tmax)) = NW2.
Hypothesis XC1 : ax_X (CS1 W st tmax) = [].
Hypothesis SK1 : map skel (ss_objs (ax_S (CS1 W st tmax))) = map skel (((sw_s1 :: unwind_objs W ++ A_globals) ++ RT_m1) ++ RT_sec).
Hypothesis FC1 : incl ((((unwind_factsS W st ++ pre_facts malloc_depth) ++ F_geom_fn) ++ F_s1) ++ F_fam tmax 8) (ss_facts (ax_S (CS1 W st tmax))).
Hypothesis CertSf : check_cfgA segsA 4000%nat [0x5e52c] GW [ES1f W st tmax] [ESn W st tmax] = true.
Hypothesis RN : R_n W st tmax = RT_m1 ++ map carve_obj N_secn.
Hypothesis WRn : swf (stRn_S W st tmax) = true.
Hypothesis DKRn : state_diff (ax_S (stKn W st tmax)) (stRn_S W st tmax) = Some ([(SLit TP_A, SVar 24)], []).
Hypothesis NXRn : ss_next (stRn_S W st tmax) = ss_next (ax_S (stKn W st tmax)).
Hypothesis ENTn : entailsA (stRn W st tmax) (L_malloc_null AE_A W st) (s_n W st tmax) = true.
Hypothesis IDn : wsub_id_below (s_n W st tmax) NF = true.

Theorem sec_spine : forall (ok : world -> Prop) (A : AA) (Kc : KcA) (Jo : word -> jpredA) rho tp Posts,
  let Q := LQPA segs NF rho tp Posts in
  (st = UStopLeOrPc -> W = []) -> stopJ_stable W st -> Kc_ok Kc ->
  ok_frameA segs ok (liftKA Kc) -> ok_pframeA segs ok (liftKA Kc) ->
  In (L_malloc_null AE_A W st, JL_malloc_null AInv CST XGL A Kc) Posts ->
  (forall rhoX tr ms md a, smatch_pendingA segs rhoX tp (CS1 W st tmax) (tr, mkCfg ms md) -> JG W st A Kc rho rhoX tp tr md ->
     mmap_place_ok (ms_gpr ms 0) (ms_gpr ms 3) md (ms_gpr ms 1) a ->
     Jo a (rho_set_rw rhoX (ss_next (ax_S (CS1 W st tmax))) a) tp tr (with_vmmaps (mmap_rw_vm (m_vmmaps md) (ms_gpr ms 1) a) md)) ->
  (forall rhoX (a : word), triple segs ok (SPA segs (Jo a) (ES1g W st tmax) (rho_set_rw rhoX (nxS W st tmax) a) tp) Q) ->
  forall rhoE, triple segs ok (SPA segs (JG W st A Kc rho) (E_s1 W st tmax 8) rhoE tp) Q.
Proof.
  intros ok A Kc Jo rho tp Posts Q HW HUS HKc Hokl Hokpl HPosts HJo HOK rhoE.
  assert (Hokf : ok_frameA segs ok (J W st A Kc)).
  { intros r t tr ms md msv' HJ. apply (Hokl r t tr ms md msv'). destruct HJ as (_ & HK & _). exact HK. }
  eapply triple_conseq; [intros w Hw; exact (sec_inst nW st tmax Wa Da Wb FB A Kc rho tp w rhoE HW HUS HKc Hw) | intros w Hw; exact Hw |].
  apply (sec_cert1 CertS1 ok A Kc rho tp Q HUS HKc Hokf). intros rhoX.
  eapply triple_conseq; [intros w Hw; exact (sec_cs1 WC1 DC1 NXC1 A Kc rho tp w rhoX Hw) | intros w Hw; exact Hw |].
  apply (sec_ecall IC1 R17 R11 R10 R12 R13 R14 R15 NX1 XC1 SK1 FC1 ok A Kc Jo rho tp Q HW HUS HKc Hokl Hokpl HJo); [|exact HOK].
  intros rhoY. apply (sec_certf CertSf ok A Kc rho tp Q HUS HKc Hokf). intros rhoZ.
  eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
  intros w Hw. exact (sec_null_finish RN WRn DKRn NXRn ENTn IDn A Kc rho tp w rhoZ Posts HKc HPosts Hw).
Qed.
End C6.

Section C7.
Hypothesis Wa : swf (SSa_S W st tmax) = true.
Hypothesis Da : state_diff (ax_S (E_s1 W st tmax 8)) (SSa_S W st tmax) = Some ([(neededx 8, SVar V_NS); (neededx 8, SVar V_NS)], []).
Hypothesis Wb : swf (SSb_S W st tmax) = true.
Hypothesis FB : forallb (sprop_below NW2) F_sgen = true.
Hypothesis NXS0 : (GW <= ss_next (ax_S (SS0 W st tmax)))%positive.
Hypothesis ECertS1 : check_ecfgA segsA 4000%nat [0x706a0] GW [mkVNA (SS0 W st tmax) 1 (SLit 0)] [mkVNA (ES1 W st tmax) 0 (SLit 0)] = true.
Hypothesis WC1 : swf (ax_S (CS1 W st tmax)) = true.
Hypothesis DC1 : state_diff (ax_S (ES1 W st tmax)) (ax_S (CS1 W st tmax)) = Some ([(a1x, SVar V_MS)], []).
Hypothesis NXC1 : ss_next (ax_S (CS1 W st tmax)) = ss_next (ax_S (ES1 W st tmax)).
Hypothesis IC1 : instr_at segsA (ss_pc (ax_S (CS1 W st tmax))) = Some Ecall.
Hypothesis R17 : reg_sv (ax_S (CS1 W st tmax)) 17 = SLit 222.
Hypothesis R11 : reg_sv (ax_S (CS1 W st tmax)) 11 = SVar V_MS.
Hypothesis R12 : reg_sv (ax_S (CS1 W st tmax)) 12 = SLit 3.
Hypothesis R13 : reg_sv (ax_S (CS1 W st tmax)) 13 = SLit 34.
Hypothesis R14 : reg_sv (ax_S (CS1 W st tmax)) 14 = SLit 18446744073709551615.
Hypothesis R15 : reg_sv (ax_S (CS1 W st tmax)) 15 = SLit 0.
Hypothesis NX1 : ss_next (ax_S (CS1 W st tmax)) = NW2.
Hypothesis NXS1f : (GW <= ss_next (ax_S (ES1f W st tmax)))%positive.
Hypothesis ECertSf : check_ecfgA segsA 4000%nat [0x5e52c] GW [mkVNA (ES1f W st tmax) 1 (SLit 0)] [mkVNA (ESn W st tmax) 0 (SLit 0)] = true.
Hypothesis FC1 : incl ((((unwind_factsS W st ++ pre_facts malloc_depth) ++ F_geom_fn) ++ F_s1) ++ F_fam tmax 8) (ss_facts (ax_S (CS1 W st tmax))).
Hypothesis RN : R_n W st tmax = RT_m1 ++ map carve_obj N_secn.
Hypothesis WRn : swf (stRn_S W st tmax) = true.
Hypothesis DKRn : state_diff (ax_S (stKn W st tmax)) (stRn_S W st tmax) = Some ([(SLit TP_A, SVar 24)], []).
Hypothesis NXRn : ss_next (stRn_S W st tmax) = ss_next (ax_S (stKn W st tmax)).
Hypothesis ENTn : entailsA (stRn W st tmax) (L_malloc_null AE_A W st) (s_n W st tmax) = true.
Hypothesis IDn : wsub_id_below (s_n W st tmax) NF = true.

Lemma ecfg_cutS : forall fuel cutpcs g (cuts exits : list vnodeA) (Jx : jpredA) (Q : world -> Prop) tp (C : axst) rho,
  stableA segs g Jx ->
  (forall n, In n cuts -> (g <= ss_next (ax_S (vna_state n)))%positive) ->
  check_ecfgA segs fuel cutpcs g cuts exits = true ->
  (forall E rho', In E exits ->
     etriple segs (SPA segs Jx (vna_state E) rho' tp) (fun w => SPfamEA segs (map (to_enodeA Jx) cuts) tp (vmeasA E rho') w \/ Q w)) ->
  In (mkVNA C 1 (SLit 0)) cuts ->
  etriple segs (SPA segs Jx C rho tp) Q.
Proof. intros fuel cutpcs g cuts exits Jx Q tp C rho HS HN HC HE HI. exact (cfg_complete_autoA segs fuel cutpcs g cuts exits Jx Q tp HS HN HC HE (mkVNA C 1 (SLit 0)) rho HI). Qed.

Theorem esec_tail_null : forall (A : AA) (Kc : KcA) rho tp Posts,
  stopJ_stable W st -> Kc_ok Kc ->
  In (L_malloc_null AE_A W st, JL_malloc_null AInv CST XGL A Kc) Posts ->
  forall rhoX, etriple segs (SPA segs (JG W st A Kc rho) (ES1f W st tmax) rhoX tp) (LQPA segs NF rho tp Posts).
Proof.
  intros A Kc rho tp Posts HUS HKc HPosts rhoX.
  pose proof (JG_stable nW st A Kc rho HUS HKc) as HST.
  apply (ecfg_cutS 4000%nat [0x5e52c] GW [mkVNA (ES1f W st tmax) 1 (SLit 0)] [mkVNA (ESn W st tmax) 0 (SLit 0)] (JG W st A Kc rho) _ tp (ES1f W st tmax) rhoX HST).
  - intros n Hn. destruct Hn as [<-|[]]. cbn [vna_state]. exact NXS1f.
  - exact ECertSf.
  - intros E' rhoY HinE. destruct HinE as [<-|[]]. cbn [vna_state].
    intros w Hw. exists w. split; [apply wsteps_refl|]. right.
    exact (sec_null_finish RN WRn DKRn NXRn ENTn IDn A Kc rho tp w rhoY Posts HKc HPosts Hw).
  - left. reflexivity.
Qed.
End C7.

End SEC2.
