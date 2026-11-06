(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "False"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "true"; "nil"; "list"; "pair"; "prod"; "nat"; "app"; "option"; "Some"; "andb"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "NW"; "GW"; "win_hyp"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "L_stack_malloc"; "stack_malloc_contractA"; "stack_malloc_contractA_ex"; "KcA"; "JL_stack_malloc"; "Kc_ok"; "Pre_stack_mallocI"; "V_FLAG"; "J_stack_malloc_pre"; "J_stack_malloc_preT"; "Pre_stack_malloc"; "n_frames"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "valuation"; "SLit"; "swf"; "sobj"; "SVar"; "sprop_below"; "SAlu"; "rm"; "rw"; "ss_facts"; "SPUle"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "entailsA"; "xr_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "busyb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "withGA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "rho_absorb"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "ag_fsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue"; "s_fin"; "posof"; "s_0"; "s_b"; "st6"; "JC"; "X6"; "sa"; "st4"; "st5"; "Cfree0"; "sb"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "Cgen"; "loopheads"; "F_K"; "ffx"; "Cbusy"; "Efree"; "NWF"; "TP_A"; "X0"; "Cfree"; "Ebusy"; "P0"; "flagaddr"; "Ebusy0"; "F_found"; "F_geom"; "NIT"; "vH"; "vHINT"; "vK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractStackMalloc"; "sm_side"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "FS_total"; "fs_frame_size"; "@Corelib.Init.Peano"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@Stdlib.Lists.List"; "forallb"; "In"; "NoDup"; "@Corelib.Init.Nat"; "add"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractStackMalloc.SM2"; "sm_side"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue TopGlueA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.TopGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma rm_rho_sub : ltac2:(tb__ "0|0|
S25S43S0S38Q40A1ScS38Q8A1A1F_;S2cS42R2R1A2A1S2cR2A1A3Fs;Frho;").
Proof. reflexivity. Qed.
Lemma rw_absorb : ltac2:(tb__ "0|0|
S25S7S28A1S7dS15S0S38Q40A1S2dS41R4R3R2A3R1A2S2dR4R1A2A3Fk;Fms;FR;Frho;").
Proof. reflexivity. Qed.
Lemma andb3_true : ltac2:(tb__ "0|0|
S3S3S3S0S3SeSeR3R2A2R1A2S5A3S1S0S3R4S5A3S1S0S3R3S5A3S0S3R2S5A3A2A2F_;Fc;Fb;Fa;").
Proof. intros [|] [|] [|]; cbn; intuition congruence. Qed.

Section SM2.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (c : Z) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S20VAInv;Vc;VA;VKc;A4").

Section Win.
Variable hi : bool.

Lemma free_finish : ltac2:(tb__ "0|6|
S14S44S1aS25S14S25OF_;S25S7S38Q40A1A1S6eS1S53Z0M0R9A2S54R9ZbA2A2S1S53G0R6A2S53R6Z8A2A2S0S3S35RaRbS48RaRbR7A3A3SfA3S0S3S27S4fVhi;RcA2A1S5A3S0S3S27S4bVhi;RdA2A1S5A3S0ScS9S7S9S23S23A2M1A1M2S7S24A1M3A2M4A1S75S50Vhi;ReA2S4bVhi;ReA2A2SdG4S8G2G3S4G1S8S23S23S26S60A1S29P18A1A4S6G1A1A3S6S24A1A4A2A3S0S3S32S4dVhi;RfA2S17S16RfA2S47Vhi;RfA2A3S5A3S0S3S40S47Vhi;R10A2S3eA2S5A3S0S23S3fS47Vhi;R11A2P6eA2S5cR11A1A3S0S23S3fS47Vhi;R12A2S1eA2S65R12A1A3S0S3S33S5fS8S23S23S5cR13A1S26S72R13A1A1A4A2S5A3S57Vsegs;S3dRfS4cR14R13R12R11R10A5A2S5eVhi;R14A2ReRdRcA6S37Vsegs;S3eR12ReS4S9S30S36A2M5S8S30S36S17S16R15A2S1bVAInv;VCST;VXGL;R15R14R13A6A4S6G5A1A3RdA6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;FrhoE;FG0;Fi;Frho0;FKc;FA;Fc;").
Proof.
  intros c A Kc rho0 i G0 rhoE tp w Hc Hi Hfree W4 W6 D56 Hent Hid Hs110 Hs120 Hxb H.
  destruct w as [tr [ms md]]. destruct H as [HsmA [_ HJC]]. cbn [w_tr w_cfg cfg_model fst snd] in HJC.
  destruct (loop_facts c A Kc rho0 i rhoE tp tr md Hc HJC) as (HR & HA & HG & PR & EFL & N6 & N7 & N8 & N9 & N10 & FL).
  cbn zeta in EFL, N6, N7, FL. pose proof HJC as [_ HJ]. destruct HJ as (_ & HK & Htp & Hnf & Hsz & Htop).
  pose proof HR as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & RA & RC). pose proof (topG_range (aa_geom A)) as TG.

  pose proof (proj1 (geom_bands _ HG)) as WBF. rewrite FS_total_val in WBF. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WBF.
  set (fl := ag_fsb (aa_geom A) + 4096 + fs_flags_off_nat (Z.to_nat c) + posof A c i) in *.
  set (F := ag_fsb (aa_geom A)) in *. set (pos := posof A c i) in *. set (ff := fs_frame F c pos).
  pose proof (eval_ffx A c rho0 i rhoE Hc HG HR) as EFF. fold F pos ff in EFF. fold F in WBF.
  pose proof (fs_geom_nums (aa_geom A) c pos HG Hc ltac:(unfold NIT in PR; exact PR)) as NUM. cbn zeta in NUM. fold F ff in NUM.
  rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in NUM. destruct NUM as (M1 & M2 & M3 & M4 & M5 & _).
  assert (SZ8 : 0 <= fs_frame_size c / 8) by (apply Z.div_pos; lia).

  pose proof (smatch_facts_hold _ _ _ _ (proj1 HsmA)) as HFa. cbn [ax_S Efree ss_facts] in HFa.
  assert (Esh : bv_unsigned (eval rhoE (SAlu ALU_ADD (gsv (ffx c)) shb)) = Sh ff).
  { unfold shb. cbn [eval]. rewrite add_val, gsv_val, EFF. rewrite !u64_lit by (unfold SHADOW_OFF; lia). unfold Sh, SHADOW_OFF. rewrite Z.mod_small by lia. reflexivity. }
  assert (ShF : Sh (F + 36864) <= Sh ff) by (apply Sh_mono; lia).
  assert (ShE : Sh ff + fs_frame_size c / 8 <= Sh (F + 11571200)).
  { unfold Sh. replace (ff / 8 + SHADOW_OFF + fs_frame_size c / 8) with ((ff + fs_frame_size c) / 8 + SHADOW_OFF).
    - apply Z.add_le_mono_r. apply Z.div_le_mono; lia.
    - replace ff with (ff / 8 * 8) at 1 by (pose proof (Z.div_mod ff 8); pose proof (Z.mod_divide ff 64); lia).
      rewrite Z.div_add_l by lia. lia. }
  assert (ShLo : 0x800b7600 <= Sh (F + 36864)) by (unfold Sh, SHADOW_OFF; lia).
  assert (ShHi : Sh (F + 11571200) < 17594333495296) by (unfold Sh, SHADOW_OFF; lia).

  assert (Ha : SPA segs (fun _ _ t m => Kc t m) (mkAX (st2s hi c) [] base_sv) rhoE tp (tr, mkCfg ms md)).
  { change (mkAX (st2s hi c) [] base_sv) with
      (ax_setS (Efree hi c) (set_objs (ax_S (Efree hi c)) (select (ss_objs (ax_S (Efree hi c))) idxs_sm))).
    apply SPA_select; [split; [exact HsmA | exact HK] | reflexivity | |].
    - intros k Hk. unfold idxs_sm in Hk. cbn in Hk. cbn. intuition lia.
    - intros k Hk. cbn in Hk. unfold idxs_sm. cbn. lia. }

  pose proof (SPA_unobj segs (fun _ _ t m => Kc t m) rhoE (mkAX (st2s hi c) [] base_sv) (kept_sm c) (R_sm c) tp tr ms md eq_refl Ha (fun k => k)) as Hb.
  cbn zeta in Hb. set (rho3 := rho_absorb rhoE (R_sm c) (vms md tp ms)) in *.
  change (ax_setS (mkAX (st2s hi c) [] base_sv) (set_objs (ax_S (mkAX (st2s hi c) [] base_sv)) (kept_sm c))) with (mkAX (st3 hi c) [] base_sv) in Hb.
  pose proof (proj1 (proj1 Ha)) as Hsm2. unfold virt in Hsm2. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm2.

  assert (HinR : forall o, In o [O_fsh_h c hexp; O_flagc c 1; O_fshadow c (zero_cells (Z.to_nat (fs_frame_size c / 8 / 8)))] -> In o (R_sm c)).
  { intros o Ho. unfold R_sm, RT_objs. rewrite <- app_assoc. apply in_or_app. right. exact Ho. }
  pose proof (absorb_carved_cells segs rhoE (st2s hi c) tr (vms md tp ms) (vmd md) (kept_sm c) (R_sm c)
                (flagaddr c) 0 1 [(0, 1%nat, SLit 1)] Hsm2 eq_refl ltac:(apply HinR; right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold cells_inside; apply Forall_cons; [cbn; lia|apply Forall_nil])) as [CF _].
  pose proof (absorb_carved_cells segs rhoE (st2s hi c) tr (vms md tp ms) (vmd md) (kept_sm c) (R_sm c)
                vFSB (8 * c) (8 * c + 8) [(8 * c, 8%nat, hexp)] Hsm2 eq_refl ltac:(apply HinR; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold cells_inside; apply Forall_cons; [cbn; lia|apply Forall_nil])) as [CH _].
  assert (CI5 : forall k n, 8 * Z.of_nat k <= n -> cells_inside 0 n (zero_cells k)).
  { induction k as [|k IH]; intros n Hn; [constructor|]. cbn [zero_cells]. apply Forall_cons; [cbn; lia|]. apply IH. lia. }
  pose proof (absorb_carved_cells segs rhoE (st2s hi c) tr (vms md tp ms) (vmd md) (kept_sm c) (R_sm c)
                (SAlu ALU_ADD (gsv (ffx c)) shb) 0 (fs_frame_size c / 8) (zero_cells (Z.to_nat (fs_frame_size c / 8 / 8))) Hsm2 eq_refl
                ltac:(apply HinR; right; right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(apply CI5; rewrite Z2Nat.id by lia; pose proof (Z.div_mod (fs_frame_size c) 64); pose proof (Z.div_mod (fs_frame_size c / 8) 8); nia)) as [CS PS].
  cbn zeta in CS, PS. rewrite Esh in CS, PS. rewrite EFL in CF. unfold vFSB in CH. cbn [eval] in CH. rewrite R5, u64_lit in CH by lia. fold F in CH.
  fold rho3 in CF, CH, CS, PS.
  set (v3 := view segs (rm rho3)). set (vE := view segs (rm rhoE)).
  assert (VF : v3 fl = Some (Z_to_bv 8 1)).
  { unfold v3. rewrite view_in by lia. unfold cells_in_view in CF. apply Forall_inv in CF. specialize (CF 0%nat ltac:(lia)).
    rewrite nth0_enc1_one in CF. cbn [Z.of_nat] in CF. rewrite !Z.add_0_r in CF. exact CF. }
  assert (VS : forall z, Sh ff <= z < Sh ff + fs_frame_size c / 8 -> v3 z = Some (Z_to_bv 8 0)).
  { intros z Hz. unfold v3. rewrite view_in by (unfold Sh, SHADOW_OFF in *; lia).
    unfold cells_in_view in CS.
    pose proof (proj1 (Forall_forall _ _) CS (8 * Z.of_nat (Z.to_nat ((z - Sh ff) / 8)), 8%nat, SLit 0)
                  ltac:(apply zero_cells_in; pose proof (Z.div_mod (fs_frame_size c) 64); pose proof (Z.div_mod (fs_frame_size c / 8) 8);
                        pose proof (Z.div_mod (z - Sh ff) 8); pose proof (Z.mod_pos_bound (z - Sh ff) 8); nia)) as X.
    cbn zeta in X. specialize (X (Z.to_nat ((z - Sh ff) mod 8)) ltac:(pose proof (Z.mod_pos_bound (z - Sh ff) 8); lia)).
    rewrite nth_enc8_zero in X by (pose proof (Z.mod_pos_bound (z - Sh ff) 8); lia).
    replace (Sh ff + 8 * Z.of_nat (Z.to_nat ((z - Sh ff) / 8)) + Z.of_nat (Z.to_nat ((z - Sh ff) mod 8))) with z in X
      by (pose proof (Z.div_mod (z - Sh ff) 8); pose proof (Z.mod_pos_bound (z - Sh ff) 8); pose proof (Z.div_pos (z - Sh ff) 8); lia).
    exact X. }
  assert (VH : forall j, (j < 8)%nat -> v3 (F + 8 * c + Z.of_nat j) = Some (nth j (enc_bytes 8 (eval rhoE hexp)) (Z_to_bv 8 0))).
  { intros j Hj. unfold v3. rewrite view_in by lia. unfold cells_in_view in CH. apply Forall_inv in CH. rewrite ?eval_absorb in CH. exact (CH j Hj). }

  pose proof (N_fixed_small c) as NFS.
  assert (RNG : forall a, in_ranges rhoE (R_sm c) a -> let z := bv_unsigned a in
            (exists k, In k (N_fixed c) /\ fst (spec_range rhoE k) <= z < snd (spec_range rhoE k))
            \/ (F + 8 * c <= z < F + 8 * c + 8) \/ z = fl \/ (Sh ff <= z < Sh ff + fs_frame_size c / 8)).
  { intros a (o & Hin & Hr) z. subst z. unfold R_sm, RT_objs in Hin. rewrite <- app_assoc in Hin.
    apply in_app_or in Hin as [Hin|Hin].
    - left. rewrite <- (N_fixed_ok c) in Hin. apply in_map_iff in Hin as (k & <- & Hk). exists k. split; [exact Hk|].
      pose proof (proj1 (Forall_forall _ _) NFS k Hk) as Sk. destruct k as [[[base lo] hi_] cs]. cbn [carve_obj] in Hr.
      destruct Sk as (S1 & S2 & S3 & _). unfold carved in Hr. rewrite obj_range_mk in Hr by lia. cbn [fst snd ob_base spec_range] in Hr |- *. exact Hr.
    - right. pose proof (urange (rw rhoE 12%positive)).
      destruct Hin as [<-|[<-|[<-|[]]]]; unfold O_fsh_h, O_flagc, O_fshadow, carved in Hr; rewrite obj_range_mk in Hr by lia; cbn [fst snd ob_base] in Hr.
      + unfold vFSB in Hr. cbn [eval] in Hr. rewrite R5, u64_lit in Hr by lia. fold F in Hr. lia.
      + rewrite EFL in Hr. lia.
      + rewrite Esh in Hr. lia. }
  assert (V5 : forall z, ~ ((exists k, In k (N_fixed c) /\ fst (spec_range rhoE k) <= z < snd (spec_range rhoE k))
                         \/ (F + 8 * c <= z < F + 8 * c + 8) \/ z = fl \/ (Sh ff <= z < Sh ff + fs_frame_size c / 8)) -> v3 z = vE z).
  { intros z Hz. unfold v3, vE. destruct (Z_le_dec 0 z); [destruct (Z_lt_dec z (2 ^ 64))|].
    2,3: rewrite !view_out by lia; reflexivity.
    rewrite !view_in by lia. unfold rho3. unfold rd_of. rewrite rm_absorb_out; [reflexivity|].
    intros Hin'. apply Hz. pose proof (RNG _ Hin') as X. cbn zeta in X. rewrite u64_lit in X by lia. exact X. }
  assert (VRT : forall z k, In k (N_fixed c) -> fst (spec_range rhoE k) <= z < snd (spec_range rhoE k) -> v3 z = vE z).
  { intros z k Hk Hz.
    pose proof (proj1 (Forall_forall _ _) NFS k Hk) as Sk.
    pose proof (rt_civ A c rhoE tp md Hc HA R1 R2 R3 R4 R5 R6) as CIV. pose proof (proj1 (Forall_forall _ _) CIV k Hk) as Ck.
    assert (Bk : 0 <= fst (spec_range rhoE k) /\ snd (spec_range rhoE k) <= 2 ^ 64).
    { destruct k as [[[base lo] hi_] cs]. cbn [spec_range fst snd]. destruct Sk as (S1 & S2 & S3 & _).
      pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & _).
      unfold N_fixed, N_rt in Hk. cbn [removelast In] in Hk. unfold vT, vCTX, vFSB, vDTLS in Hk.
      repeat (destruct Hk as [E|Hk]; [injection E; intros; subst; cbn [eval]; rewrite ?R1, ?R2, ?R5, ?R6, ?u64_lit by lia; lia|]). destruct Hk. }
    unfold v3, vE. rewrite !view_in by lia. unfold rho3.
    eapply (absorb_specs_view rhoE (st2s hi c) tr (vms md tp ms) (vmd md) (kept_sm c) (R_sm c) (N_fixed c) (rd_of segs (rm rhoE)) Hsm2 eq_refl); [|exact Hk|exact Hz].
    intros k' Hk'. split; [|split; [exact (proj1 (Forall_forall _ _) NFS k' Hk')|split]].
    - unfold R_sm, RT_objs. rewrite <- app_assoc. apply in_or_app. left. rewrite <- (N_fixed_ok c). apply in_map. exact Hk'.
    - apply coverb_sound. exact (proj1 (forallb_forall _ _) (N_fixed_coverb c) k' Hk').
    - pose proof (proj1 (Forall_forall _ _) CIV k' Hk') as C'. destruct k' as [[[base lo] hi_] cs]. cbn [spec_range fst snd].
      cbn zeta in C'. replace (bv_unsigned (eval rhoE base) + lo - lo) with (bv_unsigned (eval rhoE base)) by lia. exact C'. }

  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & _). fold F in G1, G2, G3.
  assert (Hc3 : SPA segs (fun _ _ t m => Kc t m) (mkAX (st4 hi c) [] base_sv) rho3 tp (tr, mkCfg ms md)).
  { change (mkAX (st4 hi c) [] base_sv) with
      (ax_setS (mkAX (st3 hi c) [] base_sv) (let S := ax_S (mkAX (st3 hi c) [] base_sv) in
         mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S ++ [carved (flagaddr c) 0 1 [(0, 1%nat, SLit 1)]]) (ss_facts S) NWF (ss_lenient S))).
    assert (EFL3 : bv_unsigned (eval rho3 (flagaddr c)) = fl) by (unfold rho3; rewrite eval_absorb; exact EFL).
    assert (EFF3 : bv_unsigned (eval rho3 (ffx c)) = ff) by (unfold rho3; rewrite eval_absorb; exact EFF).
    eapply SPA_carve_obj; [exact Hb | exact W4 | cbv; discriminate | rewrite ?EFL3; try lia ..].
    all: rewrite ?EFL3; try lia.
    - unfold cells_inside. apply Forall_cons; [cbn; lia | apply Forall_nil].
    -
      pose proof (proj1 Hb) as (Hsm3 & _). unfold virt in Hsm3. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm3.
      pose proof (smatch_facts_hold _ _ _ _ Hsm3) as HFa3.
      assert (Hhigh : holds rho3 F_sp_high) by (apply (proj1 (Forall_forall _ _) HFa3); cbn [ss_facts ax_S st3]; unfold facts_E; apply in_or_app; right; apply in_or_app; right; unfold F_geom; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; unfold pre_facts; cbn; tauto).
      destruct (own_range rho3 (st3 hi c) _ _ _ Hsm3 ltac:(cbn; left; reflexivity) Hhigh) as [SW1 SW3].
      assert (SW0 : topG (aa_geom A) <= fst (obj_range rho3 O_own)) by (unfold O_own; rewrite own_lo; unfold rho3; rewrite !rw_absorb; exact Htop).
      cbn [ss_objs ax_S st3]. unfold kept_sm. unfold O_own in SW0, SW1, SW3 |- *. unfold O_frame, O_flagw, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI, carved.
      apply Forall_cons; [unfold ranges_disjoint; destruct (obj_range rho3 (mkObj (SVar 10) (SVar V_DEPTH) (SLit 0) _ _)) as [lo' hi']; cbn [fst snd] in *; lia|].
      pose proof (fs_frame_size_pos c ltac:(lia)).
      repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite obj_range_mk by lia; cbn [fst snd eval ob_base]; rewrite ?EFF3, ?u64_lit by lia; lia.
    - intros off Hoff. unfold v3 in VF. rewrite view_in in VF by lia. replace (fl + off) with fl by lia. eapply wok_rd_off_image; [lia | exact VF].
    - unfold cells_in_view. apply Forall_cons; [|apply Forall_nil]. intros j Hj. replace j with 0%nat by lia.
      rewrite nth0_enc1_one. cbn [Z.of_nat]. rewrite !Z.add_0_r. unfold v3 in VF. rewrite view_in in VF by lia. exact VF.
    - apply xwords_clear_nil. }

  assert (Hd : SPA segs (fun _ _ t m => Kc t m) (mkAX (st5 hi c) [] base_sv) rho3 tp (tr, mkCfg ms md)).
  { change (mkAX (st5 hi c) [] base_sv) with (ax_setS (mkAX (st4 hi c) [] base_sv) (set_objs (ax_S (mkAX (st4 hi c) [] base_sv)) (select (ss_objs (ax_S (mkAX (st4 hi c) [] base_sv))) [0;1;2;5;3;4]%nat))).
    apply SPA_select; [exact Hc3 | reflexivity | |]; intros k Hk; cbn in Hk |- *; lia. }
  assert (He : SPA segs (fun _ _ t m => Kc t m) (mkAX (st6 hi c) [] base_sv) rho3 tp (tr, mkCfg ms md)).
  { change (mkAX (st6 hi c) [] base_sv) with (ax_setS (mkAX (st5 hi c) [] base_sv) (st6 hi c)).
    eapply SPA_restate; [exact W6 | exact D56 | reflexivity | | constructor | exact Hd].
    constructor; [|constructor]. cbn [fst snd eval]. unfold tp_ok in Htp. apply bv_eq. rewrite u64_lit by (unfold TP_A; lia).
    unfold rho3. cbn [rho_absorb rw]. rewrite Htp. destruct (geom_old _ HG) as (_ & _ & _ & G4' & _). rewrite G4'. reflexivity. }

  assert (Hf : SPA segs (fun _ _ t m => Kc t m) (X6 hi c) rho3 tp (tr, mkCfg ms md)).
  { change (X6 hi c) with (ax_setX (mkAX (st6 hi c) [] base_sv) ((ffx c, SLit (fs_frame_size c)) :: ax_X (mkAX (st6 hi c) [] base_sv))).
    apply SPA_x_publish; [exact Hxb | | exact He].
    assert (EFF3 : bv_unsigned (eval rho3 (ffx c)) = ff) by (unfold rho3; rewrite eval_absorb; exact EFF).
    unfold xr_ok. cbn [fst snd ax_base base_sv eval]. rewrite EFF3. rewrite !u64_lit by (unfold SHADOW_OFF; lia). unfold SHADOW_OFF.
    assert (F8 : ff mod 8 = 0) by (apply Z.mod_divide; [lia|]; apply (Z.divide_trans _ 64); [exists 8; reflexivity| apply Z.mod_divide; lia]).
    split; [exact F8|]. split; [lia|].
    intros a Hra.
    assert (SA : Sh ff <= SHADOW_OFF + a / 8 < Sh ff + fs_frame_size c / 8).
    { unfold Sh. split; [pose proof (Z.div_le_mono ff a 8 ltac:(lia) ltac:(lia)); lia|].
      assert (a / 8 < (ff + fs_frame_size c) / 8); [|replace ff with (ff / 8 * 8) in H at 1 by (pose proof (Z.div_mod ff 8); lia); rewrite Z.div_add_l in H by lia; lia].
      apply Z.div_lt_upper_bound; [lia|]. replace (8 * ((ff + fs_frame_size c) / 8)) with (ff + fs_frame_size c); [lia|].
      pose proof (Z.div_mod (ff + fs_frame_size c) 8). assert ((ff + fs_frame_size c) mod 8 = 0); [|lia].
      rewrite Z.add_mod, F8 by lia. pose proof (fs_class_ok c Hc) as (_ & _ & _ & K3 & _). rewrite Z.add_0_l, Z.mod_mod by lia.
      apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ 64); [exists 8; reflexivity| apply Z.mod_divide; lia]. }
    unfold SHADOW_OFF in SA. unfold Sh, SHADOW_OFF in ShLo, ShHi, ShF, ShE.
    assert (WB : forall j, 0 <= j < 8 -> Sh ff <= (2147450880 + a / 8) / 8 * 8 + j < Sh ff + fs_frame_size c / 8).
    { intros j Hj. pose proof (fs_class_ok c Hc) as (_ & _ & _ & K3 & _).
      destruct (proj1 (Z.mod_divide ff 64 ltac:(lia)) M3) as [q Hq].
      destruct (proj1 (Z.mod_divide (fs_frame_size c) 64 ltac:(lia)) K3) as [q' Hq'].
      unfold Sh, SHADOW_OFF in SA |- *. rewrite Hq in SA |- *. rewrite Hq' in SA |- *.
      replace (q * 64 / 8) with (q * 8) in * by (symmetry; rewrite <- (Z.div_mul (q * 8) 8) by lia; f_equal; lia).
      replace (q' * 64 / 8) with (q' * 8) in * by (symmetry; rewrite <- (Z.div_mul (q' * 8) 8) by lia; f_equal; lia).
      pose proof (Z.div_mod (2147450880 + a / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (2147450880 + a / 8) 8 ltac:(lia)). nia. }
    assert (OUT : forall z, Sh ff <= z < Sh ff + fs_frame_size c / 8 -> outside_all rho3 (ss_objs (st6 hi c)) (Z_to_bv 64 z)).
    { intros z Hz. cbn [ss_objs st6 st5 st4 set_objs select map nth]. unfold kept_sm. cbn [app nth map].
      unfold O_own, O_frame, O_flagw, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI, carved, outside_all.
      pose proof (proj1 Hd) as (Hsm5 & _). unfold virt in Hsm5. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm5.
      pose proof (smatch_facts_hold _ _ _ _ Hsm5) as HFa5.
      assert (Hhigh : holds rho3 F_sp_high) by (apply (proj1 (Forall_forall _ _) HFa5); cbn [ss_facts ax_S st5 st4 set_objs]; unfold facts_E; apply in_or_app; right; apply in_or_app; right; unfold F_geom; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; unfold pre_facts; cbn; tauto).
      destruct (own_range rho3 (st5 hi c) _ _ _ Hsm5 ltac:(cbn; left; reflexivity) Hhigh) as [SW1 SW3].
      assert (SW0 : topG (aa_geom A) <= fst (obj_range rho3 O_own)) by (unfold O_own; rewrite own_lo; unfold rho3; rewrite !rw_absorb; exact Htop). unfold O_own in SW0.
      assert (EFL3 : bv_unsigned (eval rho3 (flagaddr c)) = fl) by (unfold rho3; rewrite eval_absorb; exact EFL).
      pose proof (fs_frame_size_pos c ltac:(lia)).
      apply Forall_cons; [cbn zeta; destruct (obj_range rho3 (mkObj (SVar 10) (SVar V_DEPTH) (SLit 0) _ _)) as [lo' hi']; cbn [fst snd] in *; rewrite u64_lit by (unfold Sh, SHADOW_OFF in *; lia); unfold Sh, SHADOW_OFF in *; lia|].
      repeat apply Forall_cons; try apply Forall_nil; cbn zeta; rewrite obj_range_mk by lia; cbn [fst snd eval ob_base];
        rewrite ?EFF3, ?EFL3; rewrite ?u64_lit by (unfold Sh, SHADOW_OFF in *; lia); unfold Sh, SHADOW_OFF in *; lia. }
    split; [clear -SA ShLo ShHi ShF ShE; unfold Sh, SHADOW_OFF in *; lia|]. split.
    { change (Z_to_bv 64 (2147450880 + a / 8)) with (shadow_addr 2147450880 a). unfold shadow_addr. apply OUT. exact SA. }
    split.
    { intros j Hj. split.
      - unfold word_byte. apply OUT. exact (WB j Hj).
      - unfold word_byte. pose proof (WB j Hj) as Wj. pose proof (VS _ Wj) as X. unfold v3 in X.
        assert (BW : 0x646000 <= (2147450880 + a / 8) / 8 * 8 + j < 2 ^ 64) by (clear -Wj ShLo ShHi ShF ShE; unfold Sh, SHADOW_OFF in *; lia).
        rewrite view_in in X by lia.
        pose proof (rd_off_image (rm rho3) _ _ BW X) as M. rewrite M. discriminate. }
    pose proof (VS _ SA) as X. unfold v3 in X.
    assert (BS : 0x646000 <= 2147450880 + a / 8 < 2 ^ 64) by (clear -SA ShLo ShHi ShF ShE; unfold Sh, SHADOW_OFF in *; lia).
    rewrite view_in in X by lia.
    pose proof (rd_off_image (rm rho3) _ _ BS X) as M.
    exists (Z_to_bv 8 0). unfold shadow_addr. split; [exact M | left; reflexivity]. }

  remember (s_fin hi c) as s eqn:Hs. clear Hs.
  pose proof (smatchA_entails segs _ _ _ rho3 tp _ Hent (proj1 Hf)) as Hsm4.
  set (rho4 := rho_sub rho3 s) in Hsm4.
  assert (Hlow : forall k, (k < NF)%positive -> rw rho4 k = rw rhoE k).
  { intros k Hk. unfold rho4. cbn [rho_sub rw]. rewrite (wsub_get_id _ _ _ Hid Hk). reflexivity. }
  assert (E110 : bv_unsigned (rw rho4 110%positive) = ff).
  { unfold rho4. cbn [rho_sub rw]. rewrite Hs110. unfold rho3. rewrite eval_absorb. exact EFF. }
  assert (E120 : bv_unsigned (rw rho4 V_FLAG) = fl).
  { unfold rho4. cbn [rho_sub rw]. rewrite Hs120. unfold rho3. rewrite eval_absorb. exact EFL. }
  assert (Erm4 : rm rho4 = rm rho3) by exact (rm_rho_sub rho3 s).

  exists (L_stack_malloc AE_A c), (JL_stack_malloc AInv CST XGL c A Kc), rho4, tp.
  split; [left; reflexivity|]. split; [|split; [exact Hsm4|]].
  { destruct RA as [RA1 RA2]. split; [intros k Hk; rewrite Hlow by exact Hk; rewrite <- RA1 by exact Hk; reflexivity|].
    intros l. unfold rho4, rho3. cbn. apply RA2. }
  cbn [w_tr w_cfg cfg_model fst snd].

  unfold NIT in PR.
  assert (VO : forall z, ~ (fs_hint_cell F c <= z < fs_hint_cell F c + 8 \/ z = fs_flags F c + pos \/ Sh ff <= z < Sh ff + fs_frame_size c / 8) ->
               view segs (rm rho3) z = view segs (rm rhoE) z).
  { intros z Hz. Time unfold fs_hint_cell, fs_flags in Hz. Time rewrite FS_kFlagsOffset_val in Hz. Time fold fl in Hz.
    Time (destruct (Z_le_dec 0 z); [destruct (Z_lt_dec z (2 ^ 64))|]).
    2,3: rewrite !view_out by lia; reflexivity.
    Time destruct (in_ranges_dec rhoE (R_sm c) (Z_to_bv 64 z)) as [Hri|Hrn].
    - Time pose proof (RNG _ Hri) as X. Time cbn zeta in X. Time rewrite u64_lit in X by lia.
      Time (destruct X as [(k & Hk & Hr)|[X|[X|X]]]; [exact (VRT z k Hk Hr) | exfalso; apply Hz; lia | exfalso; apply Hz; lia | exfalso; apply Hz; lia]).
    - Time rewrite !view_in by lia. Time unfold rho3, rd_of. Time rewrite rm_absorb_out by exact Hrn. reflexivity. }
  assert (RMO : forall a, 0 <= a < 2 ^ 64 ->
             ~ (fs_hint_cell F c <= a < fs_hint_cell F c + 8 \/ a = fs_flags F c + pos \/ Sh ff <= a < Sh ff + fs_frame_size c / 8) ->
             ~ rt_zone (aa_geom A) a -> rm rho3 (Z_to_bv 64 a) = rm rhoE (Z_to_bv 64 a)).
  { intros a Ba Hno Hrt. unfold fs_hint_cell, fs_flags in Hno. rewrite FS_kFlagsOffset_val in Hno. fold fl in Hno.
    unfold rho3. apply rm_absorb_out. intros Hrin.
    pose proof (RNG _ Hrin) as X. cbn zeta in X. rewrite u64_lit in X by lia.
    Time (destruct X as [(k & Hk & Hr)|[X|[X|X]]]; [| apply Hno; lia | apply Hno; lia | apply Hno; lia]).
    Time exact (Hrt (N_fixed_zone c A rho0 i rhoE k a Hc HG HR Hk Hr)). }
  Time assert (VF' : view segs (rm rho3) (fs_flags F c + pos) = Some (Z_to_bv 8 1)).
  { unfold fs_flags. rewrite FS_kFlagsOffset_val. fold fl. exact VF. }
  Time assert (VH' : forall j, (j < 8)%nat -> view segs (rm rho3) (fs_hint_cell F c + Z.of_nat j) = Some (nth j (enc_bytes 8 (eval rhoE hexp)) (Z_to_bv 8 0))).
  { intros j Hj. unfold fs_hint_cell. exact (VH j Hj). }
  Time destruct (sm_rebuild CST XGL HCST HXGL c A rhoE rho3 tp md pos (eval rhoE hexp) Hc HA PR Hfree VF' VS VH' VO RMO)
    as (A' & l1 & l2 & HA' & HL & E1 & E2 & Efl & HV & HKm & HKf & HGe & KEPT).
  Time unfold JL_stack_malloc. exists A', l1, l2.
  assert (Erm0 : rm rhoE = rm rho0) by exact RC.
  Time unfold V_RES. Time rewrite E110. Time rewrite E120.
  Time (split; [unfold AInv, AInvA in HA' |- *; rewrite Erm4; exact HA'|]).
  Time (split; [exact HL|]). Time (split; [exact E1|]). Time (split; [exact E2|]).
  Time (split; [unfold fl; etransitivity; [|exact Efl]; unfold fs_flags; rewrite FS_kFlagsOffset_val; reflexivity|]).
  split; [exact HV|]. split; [exact HKm|]. split; [exact HKf|]. split; [exact HGe|].
  Time (split; [rewrite Erm4, <- Erm0; exact KEPT|]). split; [exact HK | reflexivity].
Qed.

Lemma NoDup_map_seq : ltac2:(tb__ "0|0|
SaS14F_;SaSaSaSaS1S73R4R2A2S74R2S79R4R3A2A2A2S1S73R5R2A2S74R2S79R5R4A2A2A2S0S14R7R4A1R7R3A1A3S0SaR5R4A3F_;F_;F_;Fb;Fa;S78S14S7bSaS14R4S7cR3R2A2A4A2F_;Fn;Fs;Ff;").
Proof.
  intros f s n. revert s. induction n as [|n IH]; intros s Hinj; cbn; [constructor|].
  constructor.
  - intros Hin. apply in_map_iff in Hin as (b & E & Hb). apply in_seq in Hb.
    assert (b = s) by (apply (Hinj b s); try lia; auto). lia.
  - apply IH. intros a b Ha Hb E. apply Hinj; try lia; auto.
Qed.

Lemma pigeonhole9 : ltac2:(tb__ "0|1|
S44S14S1S53Z0R1A2M0S54R1ZbA2A2S73S22R3R2A2U8A2S14S1G0S54R1Z9A2A2S0S3S35R6R5S48R6R5R2A3A3S5A3F_;Fj;S2F_;F_;F_;Fc;FA;").
Proof.
  intros A c Hc Hn Hb.
  set (L := map (fun j => posof A c (Z.of_nat j)) (seq 0 9)).
  assert (M16 : 16 <= 2 ^ (14 - c)) by (change 16 with (2 ^ 4); apply Z.pow_le_mono_r; lia).
  assert (DIFF : forall a b : nat, (a < 9)%nat -> (b < 9)%nat -> (a < b)%nat -> posof A c (Z.of_nat a) <> posof A c (Z.of_nat b)).
  { intros a b Ha Hb' Hab E. rewrite !posof_mod in E by lia.
    pose proof (Zminus_mod (hint_of A c + Z.of_nat b) (hint_of A c + Z.of_nat a) (2 ^ (14 - c))) as X.
    rewrite <- E, Z.sub_diag in X. rewrite Z.mod_0_l in X by lia.
    replace (hint_of A c + Z.of_nat b - (hint_of A c + Z.of_nat a)) with (Z.of_nat b - Z.of_nat a) in X by lia.
    rewrite Z.mod_small in X by lia. lia. }
  assert (ND : List.NoDup L).
  { unfold L. apply NoDup_map_seq. intros a b Ha Hb' E.
    destruct (Nat.lt_trichotomy a b) as [LT|[EQ|GT]]; [exfalso; exact (DIFF a b ltac:(lia) ltac:(lia) LT E) | exact EQ | exfalso; exact (DIFF b a ltac:(lia) ltac:(lia) GT (eq_sym E))]. }
  assert (INC : incl L (map fst (fs_busy A c))).
  { intros p Hp. unfold L in Hp. apply in_map_iff in Hp as (j & <- & Hj). apply in_seq in Hj.
    specialize (Hb (Z.of_nat j) ltac:(lia)). unfold busyb in Hb. apply existsb_exists in Hb as ([p f] & Hin & E).
    cbn in E. apply Z.eqb_eq in E. subst p. apply in_map_iff. exists (posof A c (Z.of_nat j), f). split; [reflexivity | exact Hin]. }
  pose proof (NoDup_incl_length ND INC) as LEN. unfold L in LEN. rewrite !length_map, length_seq in LEN.
  unfold n_frames in Hn. unfold fs_busy, nthZ in LEN. lia.
Qed.

Section Contract.
Variable c : Z.
Hypothesis Hc : 0 <= c < 11.
Hypothesis HN : 11 <= NIT c.

Hypothesis Wa : ltac2:(tb__ "0|0|
S0S3S27S4eVc;A1A1S5A3").
Hypothesis Da : ltac2:(tb__ "0|4|
S0ScS9S7S9S23S23A2M0A1M1S7S24A1M2A2M3A1S75S31S21S16Vc;A2A1S4eVc;A1A2SdG3S8G1G2S4G0S8S23S23S29P18A1S26S60A1A4S6G0A1A3S6S24A1A4A2A3").
Hypothesis Wb : ltac2:(tb__ "0|0|
S0S3S27S52Vc;A1A1S5A3").
Hypothesis Fb0 : ltac2:(tb__ "0|0|
S0S3S76S24S2aS11A1SbS24S4S24S2fS29PcA1S26S72Vc;A1A1A2S6S24A1A3S68Vhi;A1A3A3S5A3").
Hypothesis Ent0 : ltac2:(tb__ "0|0|
S0S3S32S61Vhi;Vc;A2S59Vhi;S11Vc;S6S28A1S6S24A1A5S49Vhi;Vc;A2A3S5A3").
Hypothesis Id0 : ltac2:(tb__ "0|0|
S0S3S40S49Vhi;Vc;A2P9eA2S5A3").
Hypothesis G0158 : ltac2:(tb__ "0|0|
S0S23S3fS49Vhi;Vc;A2P9eA2S6bA3").
Hypothesis G0159 : ltac2:(tb__ "0|0|
S0S23S3fS49Vhi;Vc;A2P9fA2S26S69Vc;A1A1A3").
Hypothesis FbK : ltac2:(tb__ "0|0|
S0S3S76S24S2aS11A1SbS24S5bVc;A1S2eS31S59Vhi;S11Vc;S6S28A1S6S24A1A5A1A1A3A3S5A3").
Hypothesis Wbusy : ltac2:(tb__ "0|0|
S0S3S27S31S5dVhi;Vc;A2A1A1S5A3").
Hypothesis EntB : ltac2:(tb__ "0|0|
S0S3S32S66Vhi;Vc;A2S59Vhi;S11Vc;S6S28A1S6S24A1A5S4aVhi;Vc;A2A3S5A3").
Hypothesis IdB : ltac2:(tb__ "0|0|
S0S3S40S4aVhi;Vc;A2P9eA2S5A3").
Hypothesis GB158 : ltac2:(tb__ "0|0|
S0S23S3fS4aVhi;Vc;A2P9eA2S2bS7aS6aS26Z1A1A3A3").
Hypothesis GB159 : ltac2:(tb__ "0|0|
S0S23S3fS4aVhi;Vc;A2P9fA2S2bS7aS6cS26N1A1A3A3").
Hypothesis Wfree : ltac2:(tb__ "0|0|
S0S3S27S51Vhi;Vc;A2A1S5A3").
Hypothesis FbF : ltac2:(tb__ "0|0|
S0S3S76S24S2aS5fA1SbS24SbS24S5bVc;A1S67Vhi;Vc;A2A3S2eS31S59Vhi;S11Vc;S6S28A1S6S24A1A5A1A1A3A3S5A3").
Hypothesis W4 : ltac2:(tb__ "0|0|
S0S3S27S4fVhi;Vc;A2A1S5A3").
Hypothesis W6 : ltac2:(tb__ "0|0|
S0S3S27S4bVhi;Vc;A2A1S5A3").
Hypothesis D56 : ltac2:(tb__ "0|4|
S0ScS9S7S9S23S23A2M0A1M1S7S24A1M2A2M3A1S75S50Vhi;Vc;A2S4bVhi;Vc;A2A2SdG3S8G1G2S4G0S8S23S23S26S60A1S29P18A1A4S6G0A1A3S6S24A1A4A2A3").
Hypothesis EntF : ltac2:(tb__ "0|0|
S0S3S32S4dVhi;Vc;A2S17S16Vc;A2S47Vhi;Vc;A2A3S5A3").
Hypothesis IdF : ltac2:(tb__ "0|0|
S0S3S40S47Vhi;Vc;A2S3eA2S5A3").
Hypothesis GF110 : ltac2:(tb__ "0|0|
S0S23S3fS47Vhi;Vc;A2P6eA2S5cVc;A1A3").
Hypothesis GF120 : ltac2:(tb__ "0|0|
S0S23S3fS47Vhi;Vc;A2S1eA2S65Vc;A1A3").
Hypothesis XbF : ltac2:(tb__ "0|0|
S0S3S33S5fS8S23S23S5cVc;A1S26S72Vc;A1A1A4A2S5A3").
Hypothesis CertE : ltac2:(tb__ "0|1|
S0S3S3bS10U320S5aS12S4S30S64Vhi;Vc;A2S6S30A1M0A3S4S30S61Vhi;Vc;A2G0A3A6S5A3").
Hypothesis CertB : ltac2:(tb__ "0|1|
S0S3S3bS10Uc8S5aS12S4S30S5dVhi;Vc;A2S6S30A1M0A3S4S30S63Vhi;Vc;A2G0A3A6S5A3").
Hypothesis CertF : ltac2:(tb__ "0|1|
S0S3S3bS10U190S5aS12S4S30S62Vhi;Vc;A2S6S30A1M0A3S4S30S5eVhi;Vc;A2G0A3A6S5A3").

Hypothesis ECertE : ltac2:(tb__ "0|3|
S0S3S3cS10U320S5aS12S4S39S3aS64Vhi;Vc;A2Z1S26Z0M0A1M1A3S6S39A1M2A3S4S39S3aS61Vhi;Vc;A2G0G1A3G2A3A6S5A3").
Hypothesis ECertB : ltac2:(tb__ "0|3|
S0S3S3cS10Uc8S5aS12S4S39S3aS5dVhi;Vc;A2Z1S26Z0M0A1M1A3S6S39A1M2A3S4S39S3aS63Vhi;Vc;A2G0G1A3G2A3A6S5A3").
Hypothesis ECertF : ltac2:(tb__ "0|3|
S0S3S3cS10U190S5aS12S4S39S3aS62Vhi;Vc;A2Z1S26Z0M0A1M1A3S6S39A1M2A3S4S39S3aS5eVhi;Vc;A2G0G1A3G2A3A6S5A3").

Let QF (A : AA) (Kc : KcA) (rho0 : valuation) (tp : list word) : world -> Prop := ltac2:(tb__ "0|1|
S37Vsegs;S3eVrho0;Vtp;S4S9S30S36A2M0S8S30S36S17S16Vc;A2S1bVAInv;VCST;VXGL;Vc;VA;VKc;A6A4S6G0A1A3A5").

Lemma probes_sound : ltac2:(tb__ "0|1|
S6eOF_;S44S1aS25S7S38Q40A1A1SaS14S25S1cR6A1S58Vsegs;R9VJ;Vc;R8R7A3A3S13Vhi;S46S45R9A1A1S71A3S53Z0M0R5A2S0S14S55R6S56R7A1A2Z9A3S14S1S53G0R1A2S54R1R8A2A2S0S3S35ReVc;S48ReVc;R2A3A3S5A3F_;Fj;S70Vsegs;ReS57Vsegs;S4cVc;RdRcRbR8A5S59Vhi;S11Vc;S6S28A1S5bVc;A1A5R7RaA5VQF;RdRcRbRaA4A4F_;F_;F_;F_;F_;F_;Frho;Fi;Fk;Ftp;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 tp k. induction k as [|k IH]; intros i rho HKc Hokf Hwin Hi Hik Hprev.
  -
    eapply triple_conseq; [ | intros w Hw; exact Hw | eapply (triple_pure (X := False)); intros [] ].
    intros w Hw. split; [|exact Hw].
    destruct w as [tr [ms md]]. destruct Hw as [_ [HR HJ]]. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
    destruct HJ as (HA & HK & Htp & Hnf & Hsz & _).
    apply (pigeonhole9 A c Hc Hnf). intros j Hj. apply Hprev. lia.
  - assert (OKC : ok_frameA segs ok (JC c A Kc rho0 i)) by (intros r t tr ms md msv' [_ HJ]; eapply Hokf; eauto).
    destruct (busyb A c (posof A c i)) eqn:Hb.
    +
      eapply triple_conseq; [intros w Hw; exact (busy_carve hi c A Kc rho0 i rho tp w Hc Hb Wbusy Hw) | intros w Hw; exact Hw |].
      apply (cfg_soundA segs 200%nat loopheads GW [Cbusy hi c] [Ebusy hi c] (JC c A Kc rho0 i) ok (QF A Kc rho0 tp) tp OKC (JC_stableA c A Kc rho0 i HKc) CertB).
      * intros E rhoE [<-|[]].
        eapply triple_conseq; [ | intros w Hw; right; exact Hw | apply (IH (i + 1) (rho_sub rhoE (s_b hi c)) HKc Hokf Hwin ltac:(lia) ltac:(lia))].
        -- intros w Hw. apply (busy_step hi c A Kc rho0 i (fun _ => True) rhoE tp w Hc Hi ltac:(lia) Hb EntB IdB GB158 GB159 FbK).
           destruct Hw as [Hsm HJ]. split; [exact Hsm | split; [exact I | exact HJ]].
        -- intros j Hj. destruct (Z.eq_dec j i) as [->|]; [exact Hb | apply Hprev; lia].
      * left; reflexivity.
    +
      eapply triple_conseq; [intros w Hw; exact (free_carve hi c A Kc rho0 i rho tp w Hc Hb Wfree FbF Hwin Hw) | intros w Hw; exact Hw |].
      apply (cfg_soundA segs 400%nat loopheads GW [Cfree hi c] [Efree hi c] (JC c A Kc rho0 i) ok (QF A Kc rho0 tp) tp OKC (JC_stableA c A Kc rho0 i HKc) CertF).
      * intros E rhoE [<-|[]].
        eapply triple_conseq; [ | intros w Hw; exact Hw | apply triple_refl ].
        intros w Hw. right. apply (free_finish c A Kc rho0 i (fun _ => True) rhoE tp w Hc ltac:(lia) Hb W4 W6 D56 EntF IdF GF110 GF120 XbF).
        destruct Hw as [Hsm HJ]. split; [exact Hsm | split; [exact I | exact HJ]].
      * left; reflexivity.
Qed.

Lemma stack_malloc_contract_win : ltac2:(tb__ "0|1|
S6eOF_;S44S1aS25S7S38Q40A1A1S1cR3A1S58Vsegs;R6VJ;Vc;R5R4A3A3S13Vhi;S46S45R6A1A1S71A3S70Vsegs;R8S57Vsegs;VJ;Vc;R7R6A3S1dS16Vc;A2R5R4A5S37Vsegs;S3eR5R4S4S9S30S36A2M0S8S30S36S17S16Vc;A2S1bVAInv;VCST;VXGL;Vc;R7R6A6A4S6G0A1A3A5A4F_;F_;F_;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp HKc Hokf Hwin.
  assert (OKE : ok_frameA segs ok (JE c A Kc rho)) by (intros r t tr ms md msv' [_ HJ]; eapply Hokf; eauto).
  eapply triple_conseq; [ | intros w Hw; exact Hw |].
  { intros w Hw. pose proof (sm_instantiate hi c A Kc rho tp w Hc Wa Da Wb Fb0 Hwin Hw) as H1.
    assert (H2 : SPA segs (JE c A Kc rho) (P0 hi c) (rho1_of A c rho) tp w).
    { destruct H1 as [Hsm HJ]. split; [exact Hsm | split; [apply RV0_rho1 | exact HJ]]. }
    exact H2. }
  apply (cfg_soundA segs 800%nat loopheads GW [P0 hi c] [X0 hi c] (JE c A Kc rho) ok (QF A Kc rho tp) tp OKE (JE_stableA c A Kc rho HKc) CertE).
  - intros E rhoE [<-|[]].
    eapply triple_conseq; [ | intros w Hw; right; exact Hw
                          | apply (probes_sound ok A Kc rho tp 9%nat 0 (rho_sub rhoE (s_0 hi c)) HKc Hokf Hwin ltac:(lia) ltac:(reflexivity))].
    + intros w Hw. apply (entry_step hi c A Kc rho (fun _ => True) rhoE tp w Hc ltac:(lia) Ent0 Id0 G0158 G0159 FbK).
      destruct Hw as [Hsm HJ]. split; [exact Hsm | split; [exact I | exact HJ]].
    + intros j Hj. lia.
  - left; reflexivity.
Qed.

Lemma probes_complete : ltac2:(tb__ "0|1|
S44S1aS25S7S38Q40A1A1SaS14S25S1cR6A1S13Vhi;S46S45R8A1A1S71A3S53Z0M0R4A2S0S14S55R5S56R6A1A2Z9A3S14S1S53G0R1A2S54R1R7A2A2S0S3S35RdVc;S48RdVc;R2A3A3S5A3F_;Fj;S6fVsegs;S57Vsegs;S4cVc;RcRbRaR7A5S59Vhi;S11Vc;S6S28A1S5bVc;A1A5R6R9A5VQF;RcRbRaR9A4A3F_;F_;F_;F_;F_;Frho;Fi;Fk;Ftp;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 tp k. induction k as [|k IH]; intros i rho HKc Hwin Hi Hik Hprev.
  - intros w Hw. exfalso.
    destruct w as [tr [ms md]]. destruct Hw as [_ [HR HJ]]. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
    destruct HJ as (HA & HK & Htp & Hnf & Hsz & _).
    apply (pigeonhole9 A c Hc Hnf). intros j Hj. apply Hprev. lia.
  - destruct (busyb A c (posof A c i)) eqn:Hb.
    + eapply etriple_conseq; [intros w Hw; exact (busy_carve hi c A Kc rho0 i rho tp w Hc Hb Wbusy Hw) | intros w Hw; exact Hw |].
      change (Cbusy hi c) with (vna_state (mkVNA (Cbusy hi c) 1 (SLit 0))).
      apply (cfg_complete_autoA segs 200%nat loopheads GW [mkVNA (Cbusy hi c) 1 (SLit 0)] [mkVNA (Ebusy hi c) 0 (SLit 0)]
               (JC c A Kc rho0 i) (QF A Kc rho0 tp) tp (JC_stableA c A Kc rho0 i HKc)).
      * intros n [<-|[]]. cbv; congruence.
      * exact ECertB.
      * intros E rhoE [<-|[]]. cbn [vna_state].
        eapply etriple_conseq; [ | intros w Hw; right; exact Hw | apply (IH (i + 1) (rho_sub rhoE (s_b hi c)) HKc Hwin ltac:(lia) ltac:(lia))].
        -- intros w Hw. apply (busy_step hi c A Kc rho0 i (fun _ => True) rhoE tp w Hc Hi ltac:(lia) Hb EntB IdB GB158 GB159 FbK).
           destruct Hw as [Hsm HJ]. split; [exact Hsm | split; [exact I | exact HJ]].
        -- intros j Hj. destruct (Z.eq_dec j i) as [->|]; [exact Hb | apply Hprev; lia].
      * left; reflexivity.
    + eapply etriple_conseq; [intros w Hw; exact (free_carve hi c A Kc rho0 i rho tp w Hc Hb Wfree FbF Hwin Hw) | intros w Hw; exact Hw |].
      change (Cfree hi c) with (vna_state (mkVNA (Cfree hi c) 1 (SLit 0))).
      apply (cfg_complete_autoA segs 400%nat loopheads GW [mkVNA (Cfree hi c) 1 (SLit 0)] [mkVNA (Efree hi c) 0 (SLit 0)]
               (JC c A Kc rho0 i) (QF A Kc rho0 tp) tp (JC_stableA c A Kc rho0 i HKc)).
      * intros n [<-|[]]. cbv; congruence.
      * exact ECertF.
      * intros E rhoE [<-|[]]. cbn [vna_state].
        eapply etriple_conseq; [ | intros w Hw; exact Hw | apply etriple_refl ].
        intros w Hw. right. apply (free_finish c A Kc rho0 i (fun _ => True) rhoE tp w Hc ltac:(lia) Hb W4 W6 D56 EntF IdF GF110 GF120 XbF).
        destruct Hw as [Hsm HJ]. split; [exact Hsm | split; [exact I | exact HJ]].
      * left; reflexivity.
Qed.

Lemma stack_malloc_contract_ex_win : ltac2:(tb__ "0|1|
S44S1aS25S7S38Q40A1A1S1cR3A1S13Vhi;S46S45R5A1A1S71A3S6fVsegs;S57Vsegs;VJ;Vc;R6R5A3S1dS16Vc;A2R4R3A5S37Vsegs;S3eR4R3S4S9S30S36A2M0S8S30S36S17S16Vc;A2S1bVAInv;VCST;VXGL;Vc;R6R5A6A4S6G0A1A3A5A3F_;F_;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp HKc Hwin.
  eapply etriple_conseq; [ | intros w Hw; exact Hw |].
  { intros w Hw. pose proof (sm_instantiate hi c A Kc rho tp w Hc Wa Da Wb Fb0 Hwin Hw) as H1.
    assert (H2 : SPA segs (JE c A Kc rho) (P0 hi c) (rho1_of A c rho) tp w).
    { destruct H1 as [Hsm HJ]. split; [exact Hsm | split; [apply RV0_rho1 | exact HJ]]. }
    exact H2. }
  change (P0 hi c) with (vna_state (mkVNA (P0 hi c) 1 (SLit 0))).
  apply (cfg_complete_autoA segs 800%nat loopheads GW [mkVNA (P0 hi c) 1 (SLit 0)] [mkVNA (X0 hi c) 0 (SLit 0)]
           (JE c A Kc rho) (QF A Kc rho tp) tp (JE_stableA c A Kc rho HKc)).
  - intros n [<-|[]]. cbv; congruence.
  - exact ECertE.
  - intros E rhoE [<-|[]]. cbn [vna_state].
    eapply etriple_conseq; [ | intros w Hw; right; exact Hw
                           | apply (probes_complete A Kc rho tp 9%nat 0 (rho_sub rhoE (s_0 hi c)) HKc Hwin ltac:(lia) ltac:(reflexivity))].
    + intros w Hw. apply (entry_step hi c A Kc rho (fun _ => True) rhoE tp w Hc ltac:(lia) Ent0 Id0 G0158 G0159 FbK).
      destruct Hw as [Hsm HJ]. split; [exact Hsm | split; [exact I | exact HJ]].
    + intros j Hj. lia.
  - left; reflexivity.
Qed.
End Contract.
End Win.

Record sm_side (hi : bool) (c : Z) : Prop := mkSmSide {
  S_HN : 11 <= NIT c;
  S_Wa : swf (sa c) = true;
  S_Da : state_diff (ax_S (Pre_stack_mallocI AE_A c)) (sa c) = Some ([(SVar 24, SLit TP_A)], []);
  S_Wb : swf (sb c) = true;
  S_Fb0 : forallb (sprop_below NW) ([SPUle (SVar 12) (SLit (fs_frame_size c))] ++ F_geom hi) = true;
  S_Ent0 : entailsA (X0 hi c) (Cgen hi NW c [] []) (s_0 hi c) = true;
  S_Id0 : wsub_id_below (s_0 hi c) 158%positive = true;
  S_G0158 : wsub_get (s_0 hi c) 158%positive = vHINT;
  S_G0159 : wsub_get (s_0 hi c) 159%positive = SLit (NIT c);
  S_FbK : forallb (sprop_below NW) (F_K c ++ ss_facts (ax_S (Cgen hi NW c [] []))) = true;
  S_Wbusy : swf (ax_S (Cbusy hi c)) = true;
  S_EntB : entailsA (Ebusy0 hi c) (Cgen hi NW c [] []) (s_b hi c) = true;
  S_IdB : wsub_id_below (s_b hi c) 158%positive = true;
  S_GB158 : wsub_get (s_b hi c) 158%positive = SAlu ALU_ADD vH (SLit 1);
  S_GB159 : wsub_get (s_b hi c) 159%positive = SAlu ALU_ADD vK (SLit (-1));
  S_Wfree : swf (Cfree0 hi c) = true;
  S_FbF : forallb (sprop_below NWF) ((F_K c ++ F_found hi c) ++ ss_facts (ax_S (Cgen hi NW c [] []))) = true;
  S_W4 : swf (st4 hi c) = true;
  S_W6 : swf (st6 hi c) = true;
  S_D56 : state_diff (st5 hi c) (st6 hi c) = Some ([(SLit TP_A, SVar 24)], []);
  S_EntF : entailsA (X6 hi c) (L_stack_malloc AE_A c) (s_fin hi c) = true;
  S_IdF : wsub_id_below (s_fin hi c) NF = true;
  S_GF110 : wsub_get (s_fin hi c) 110%positive = ffx c;
  S_GF120 : wsub_get (s_fin hi c) V_FLAG = flagaddr c;
  S_XbF : xr_below NWF (ffx c, SLit (fs_frame_size c)) = true;
  S_CertE : check_cfgA segsA 800%nat loopheads GW [P0 hi c] [X0 hi c] = true;
  S_CertB : check_cfgA segsA 200%nat loopheads GW [Cbusy hi c] [Ebusy hi c] = true;
  S_CertF : check_cfgA segsA 400%nat loopheads GW [Cfree hi c] [Efree hi c] = true;

  S_ECertE : check_ecfgA segsA 800%nat loopheads GW [mkVNA (P0 hi c) 1 (SLit 0)] [mkVNA (X0 hi c) 0 (SLit 0)] = true;
  S_ECertB : check_ecfgA segsA 200%nat loopheads GW [mkVNA (Cbusy hi c) 1 (SLit 0)] [mkVNA (Ebusy hi c) 0 (SLit 0)] = true;
  S_ECertF : check_ecfgA segsA 400%nat loopheads GW [mkVNA (Cfree hi c) 1 (SLit 0)] [mkVNA (Efree hi c) 0 (SLit 0)] = true }.

Section All.
Variable c : Z.
Hypothesis Hc : 0 <= c < 11.
Hypothesis SIDE : ltac2:(tb__ "0|0|
S3S7eR1Vc;A2Fhi;").

Theorem stack_malloc_contractT : ltac2:(tb__ "0|1|
S6eOF_;S44S1aS25S7S38Q40A1A1S1cR3A1S58Vsegs;R6S1fVAInv;Vc;R5R4A4A3S70Vsegs;R7S57Vsegs;VJ;Vc;R6R5A3S1dS16Vc;A2R4R3A5S37Vsegs;S3eR4R3S4S9S30S36A2M0S8S30S36S17S16Vc;A2S1bVAInv;VCST;VXGL;Vc;R6R5A6A4S6G0A1A3A5A4F_;F_;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp HKc Hokf0.
  assert (Hokf : ok_frameA segs ok (J c A Kc)).
  { apply (ok_frameA_stack_malloc_T segs AInv); [|exact Hokf0]. intros A0 r r' t m H E. unfold AInv, AInvA in *. rewrite E. exact H. }

  apply (triple_by_pure _ _ (exists hi, win_hyp hi (ag_fsb (aa_geom A)) FS_total));
    [intros w [_ (HA & _)]; exact (win_hyp_cases _ _ (proj1 (geom_bands _ (proj1 HA)))) | intros [hi Hwin]].
  destruct (SIDE hi) as [HN Wa Da Wb Fb0 Ent0 Id0 G0158 G0159 FbK Wbusy EntB IdB GB158 GB159 Wfree FbF W4 W6 D56 EntF IdF GF110 GF120 XbF CertE CertB CertF _ _ _].
  exact (stack_malloc_contract_win hi c Hc HN Wa Da Wb Fb0 Ent0 Id0 G0158 G0159 FbK Wbusy EntB IdB GB158 GB159 Wfree FbF W4 W6 D56 EntF IdF GF110 GF120 XbF
           CertE CertB CertF ok A Kc rho tp HKc Hokf Hwin).
Qed.

Theorem stack_malloc_contract : ltac2:(tb__ "0|0|
S18Vsegs;S16VAInv;VCST;VXGL;Vc;A6").
Proof. apply stack_malloc_contractA_of_T. exact stack_malloc_contractT. Qed.

Theorem stack_malloc_contractT_ex : ltac2:(tb__ "0|1|
S44S1aS25S7S38Q40A1A1S1cR3A1S6fVsegs;S57Vsegs;VJ;Vc;R5R4A3S1dS16Vc;A2R3R2A5S37Vsegs;S3eR3R2S4S9S30S36A2M0S8S30S36S17S16Vc;A2S1bVAInv;VCST;VXGL;Vc;R5R4A6A4S6G0A1A3A5A3F_;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp HKc.
  apply (etriple_by_pure _ (exists hi, win_hyp hi (ag_fsb (aa_geom A)) FS_total));
    [intros w [_ (HA & _)]; exact (win_hyp_cases _ _ (proj1 (geom_bands _ (proj1 HA)))) | intros [hi Hwin]].
  destruct (SIDE hi) as [HN Wa Da Wb Fb0 Ent0 Id0 G0158 G0159 FbK Wbusy EntB IdB GB158 GB159 Wfree FbF W4 W6 D56 EntF IdF GF110 GF120 XbF _ _ _ ECertE ECertB ECertF].
  exact (stack_malloc_contract_ex_win hi c Hc HN Wa Da Wb Fb0 Ent0 Id0 G0158 G0159 FbK Wbusy EntB IdB GB158 GB159 Wfree FbF W4 W6 D56 EntF IdF GF110 GF120 XbF
           ECertE ECertB ECertF A Kc rho tp HKc Hwin).
Qed.

Theorem stack_malloc_contract_ex : ltac2:(tb__ "0|0|
S19Vsegs;S16VAInv;VCST;VXGL;Vc;A6").
Proof. apply stack_malloc_contractA_ex_of_T. exact stack_malloc_contractT_ex. Qed.
End All.
End SM2.

Section Instances.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.

Ltac sm_close := first [ lia | lazymatch goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end | (vm_compute; discriminate) | (vm_compute; congruence) ].

Ltac sm_sides := intros [|]; constructor; sm_close.
Lemma sm_side_0 : ltac2:(tb__ "0|0|
S3S6dR1Z0A2Fhi;"). Proof. Time sm_sides. Qed.
Lemma sm_side_1 : ltac2:(tb__ "0|0|
S3S6dR1Z1A2Fhi;"). Proof. Time sm_sides. Qed.
Lemma sm_side_2 : ltac2:(tb__ "0|0|
S3S6dR1Z2A2Fhi;"). Proof. Time sm_sides. Qed.
Lemma sm_side_3 : ltac2:(tb__ "0|0|
S3S6dR1Z3A2Fhi;"). Proof. Time sm_sides. Qed.
Lemma sm_side_5 : ltac2:(tb__ "0|0|
S3S6dR1Z5A2Fhi;"). Proof. Time sm_sides. Qed.
Lemma sm_side_6 : ltac2:(tb__ "0|0|
S3S6dR1Z6A2Fhi;"). Proof. Time sm_sides. Qed.

Theorem stack_malloc_contract_0 : ltac2:(tb__ "0|0|
S18S10S16S34S10A1VCST;VXGL;Z0A6").
Proof. exact (stack_malloc_contract CST XGL HCST HXGL 0 ltac:(lia) sm_side_0). Qed.
Theorem stack_malloc_contract_ex_0 : ltac2:(tb__ "0|0|
S19S10S16S34S10A1VCST;VXGL;Z0A6").
Proof. exact (stack_malloc_contract_ex CST XGL HCST HXGL 0 ltac:(lia) sm_side_0). Qed.
Theorem stack_malloc_contract_1 : ltac2:(tb__ "0|0|
S18S10S16S34S10A1VCST;VXGL;Z1A6").
Proof. exact (stack_malloc_contract CST XGL HCST HXGL 1 ltac:(lia) sm_side_1). Qed.
Theorem stack_malloc_contract_ex_1 : ltac2:(tb__ "0|0|
S19S10S16S34S10A1VCST;VXGL;Z1A6").
Proof. exact (stack_malloc_contract_ex CST XGL HCST HXGL 1 ltac:(lia) sm_side_1). Qed.
Theorem stack_malloc_contract_2 : ltac2:(tb__ "0|0|
S18S10S16S34S10A1VCST;VXGL;Z2A6").
Proof. exact (stack_malloc_contract CST XGL HCST HXGL 2 ltac:(lia) sm_side_2). Qed.
Theorem stack_malloc_contract_ex_2 : ltac2:(tb__ "0|0|
S19S10S16S34S10A1VCST;VXGL;Z2A6").
Proof. exact (stack_malloc_contract_ex CST XGL HCST HXGL 2 ltac:(lia) sm_side_2). Qed.
Theorem stack_malloc_contract_3 : ltac2:(tb__ "0|0|
S18S10S16S34S10A1VCST;VXGL;Z3A6").
Proof. exact (stack_malloc_contract CST XGL HCST HXGL 3 ltac:(lia) sm_side_3). Qed.
Theorem stack_malloc_contract_ex_3 : ltac2:(tb__ "0|0|
S19S10S16S34S10A1VCST;VXGL;Z3A6").
Proof. exact (stack_malloc_contract_ex CST XGL HCST HXGL 3 ltac:(lia) sm_side_3). Qed.
Theorem stack_malloc_contract_5 : ltac2:(tb__ "0|0|
S18S10S16S34S10A1VCST;VXGL;Z5A6").
Proof. exact (stack_malloc_contract CST XGL HCST HXGL 5 ltac:(lia) sm_side_5). Qed.
Theorem stack_malloc_contract_ex_5 : ltac2:(tb__ "0|0|
S19S10S16S34S10A1VCST;VXGL;Z5A6").
Proof. exact (stack_malloc_contract_ex CST XGL HCST HXGL 5 ltac:(lia) sm_side_5). Qed.
Theorem stack_malloc_contract_6 : ltac2:(tb__ "0|0|
S18S10S16S34S10A1VCST;VXGL;Z6A6").
Proof. exact (stack_malloc_contract CST XGL HCST HXGL 6 ltac:(lia) sm_side_6). Qed.
Theorem stack_malloc_contract_ex_6 : ltac2:(tb__ "0|0|
S19S10S16S34S10A1VCST;VXGL;Z6A6").
Proof. exact (stack_malloc_contract_ex CST XGL HCST HXGL 6 ltac:(lia) sm_side_6). Qed.

Theorem stack_malloc_contracts : ltac2:(tb__ "0|0|
S14S77S14R1S4S14Z0S4S14Z1S4S14Z2S4S14Z3S4S14Z5S4S14Z6S6S14A1A3A3A3A3A3A3A3S18S10S16S34S10A1VCST;VXGL;R2A6F_;Fc;").
Proof.
  intros c Hin. cbn in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
    [apply stack_malloc_contract_0 | apply stack_malloc_contract_1 | apply stack_malloc_contract_2
    | apply stack_malloc_contract_3 | apply stack_malloc_contract_5 | apply stack_malloc_contract_6].
Qed.
Theorem stack_malloc_contracts_ex : ltac2:(tb__ "0|0|
S14S77S14R1S4S14Z0S4S14Z1S4S14Z2S4S14Z3S4S14Z5S4S14Z6S6S14A1A3A3A3A3A3A3A3S19S10S16S34S10A1VCST;VXGL;R2A6F_;Fc;").
Proof.
  intros c Hin. cbn in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
    [apply stack_malloc_contract_ex_0 | apply stack_malloc_contract_ex_1 | apply stack_malloc_contract_ex_2
    | apply stack_malloc_contract_ex_3 | apply stack_malloc_contract_ex_5 | apply stack_malloc_contract_ex_6].
Qed.
End Instances.
