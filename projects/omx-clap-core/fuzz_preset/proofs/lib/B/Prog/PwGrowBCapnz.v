(* fuzz_preset, image B' (asan-ubsan d663f82d, the #102 pin), slice RD-GROW: SEGMENT of grow's walk - THE cap <> 0
   CLASS (and n < cap). Per record, against PwGrowB.v's statement layer (the kit's tgrow_specX, restated for the free /
   realloc move): arm 1 (n < cap, no call), the kids realloc
   fuzz_realloc (kids, 56 cap -> 112 cap) with its NULL arms (arms 2 / 3) and the array arm (4), and for an object
   the keys realloc fuzz_realloc (keys, 8 cap -> 16 cap) with its NULL arms (5 / 6) and arm 7 (by
   PwGrowBArm7.growB_seg_arm7). The cap = 0 class is PwGrowBCap0.v's growB_seg_cap0.
   History: written as the old image B's walk (2026-10-29, the old image-B branch), relocated to B' (alreloc
   c4338d, 1c70a2dd48da, audited AGREE), closed, and re-fitted to the kit's cut
   7cdbb61b5fa0.
   MEASURED in this walk: three unscoped lia ran 280-330 s each (HV5 / HV6 frame cases and the old-blocks
   disjointness), now scoped with clear - ..; the region-add disjointness goals use a VM-checked equation for the
   region list, not `vm_compute ss_mem` (its missing cast made a Qed run past 50 min); the keys call's branch
   hypothesis is matched by its environment E2. The Section repeats PwGrowB.v's Section c.
   THE FREE / REALLOC MOVE: the walk runs at RW := wle' SEGS RZ_cf (lifted once at its top); the kids / keys calls take
   their hull budgets from grow's (grow_hull_kids / grow_hull_keys), the arms state the hull use (grow_hull_none /
   grow_hull_one / grow_hull_two), the realloc's refused arm gives the world-free evidence, and the kids-refused
   exclusion is grow_excl_of_leaf of the kids call's OUTCOME. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI00 YI04 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YK06 YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC80xf YC1fPx YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm YC80xf_inv.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnAlloc PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PwGrowG PwGrowLive PRW_StepKit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetCfnB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PwGrowB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PwGrowBArm7.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YGcfRehidePost YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG00cf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {PG : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PG).
#[local] Notation VAL := (@pa_val _ B_prog_listing PG).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PG).
#[local] Notation BASE := (@pa_val _ B_prog_listing PG A_TEXT).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
(* the engine's laws at the harness head length (one named hypothesis, HL = cf_head) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* image facts of the instance (PAImg_prog.v's PI_prog_B meets each by computation) *)
Hypothesis HENT : SIGMA AS_grow = BASE + GROW_OFF_B.
Hypothesis HGOT : as_got_shadow B = VAL (A_OBJ 0).
Hypothesis HCELL : as_shadow_cell B = VAL (A_OBJ 12).
Hypothesis HGC : VAL (A_OBJ 0) + 8 <= VAL (A_OBJ 12) \/ VAL (A_OBJ 12) + 8 <= VAL (A_OBJ 0).
(* the runtime's errno cell is image bytes (YC1fP's PALib field pal_env, api_env; with HGOT / HCELL / HGC the PALib
   facts the walk reads) *)
Hypothesis HENV : api_env SEGS B.
Hypothesis HLH : @pa_lo _ B_prog_listing PG = YImgTop.IMG_LO_B /\ @pa_hi _ B_prog_listing PG = YImgTop.IMG_TOP_B.
(* the two image cells the walk reads lie in loaded segments (PI_prog_B: by computation) *)
Hypothesis HC0 : forall i, 0 <= i < 8 -> in_img SEGS (VAL (A_OBJ 0) + i).
Hypothesis HC12 : forall i, 0 <= i < 8 -> in_img SEGS (VAL (A_OBJ 12) + i).
(* the callee's text: the kit's tfuzz_realloc_specX at image B's instances, a STATED HYPOTHESIS until slice S1's walk *)
Hypothesis HREALLOC : @tfuzz_realloc_specX fx rc ci cp prh_img_B RL B_prog_listing PG B ARx SK.
#[local] Notation PST := (@prh_pst prh_img_B).
#[local] Existing Instance prh_img_B.
(* the alloc.c statics (the program's PST) are image bytes (prh_img_B's pi_g_* in a loaded segment: by computation) *)
Hypothesis HPST : forall a, Exists (in_zr a) PST -> in_img SEGS a.
(* ... and not read-only bytes (they are in a writable data segment, off the RELRO range: by computation at
   PI_prog_B). What carries the read-only view arodata_okP across the kids call to the keys call: the journal's image
   clause keeps an image byte only off PST (CawA102's finding, the same fact as its cwi_pst_rw) *)
Hypothesis HPSTRW : forall a, Exists (in_zr a) PST -> ~ in_roP SEGS pa_relro_lo pa_relro_hi a.

(* the runners and the branch rule over the world relation of the free / realloc move, wle' SEGS RZ_cf (the walk
   lifts once at its top: the journal starts at this R) *)
Definition RUNB := @paj_run_xfR fx rc SK B_prog_listing PL_prog_B PG B PST ARx _ LAWS (wle' SEGS RZ_cf)
  (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf).
(* the same runner carrying a memory invariant P (walk-S6's YC80xf_inv.v): the walk's P is the m-form keep
   `memnorm mem -> memnorm m`, kept ABSTRACT inside the walk (clearbody) and instantiated once at its top *)
Definition RUNBP (P : (word -> option byte) -> Prop) (PLAW : srr_inv_laws SEGS P) :=
  @paj_run_xf_invR fx rc SK B_prog_listing PL_prog_B PG B PST ARx _ LAWS P PLAW (wle' SEGS RZ_cf)
    (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf).
Definition BRB := @paj_branchR fx rc B_prog_listing PG (wle' SEGS RZ_cf).

(* THE cap <> 0 SEGMENT *)
Theorem growB_seg_capnz : forall CTX0 (D : grB_in),
  grB_pre B ARx CTX0 D -> gb_cap D <> 0 ->
  SRr' SEGS RZ_cf (gb_W D) (cfg_at SEGS (SIGMA AS_grow) (gb_regs D) (gb_mem D) (gb_md D))
    (grB_post (fx := fx) B ARx SK D).
Proof.
intros CTX0 D HPD Hcapnz.
destruct D as [ly S Hp W regs mem md ch e v ty num str kids keys n cap kb yb Lam peak cnt fail ran most own].
unfold grB_pre, grB_post, grB_QD, grB_FP in *.
cbn [gb_ly gb_S gb_Hp gb_W gb_regs gb_mem gb_md gb_ch gb_e gb_v gb_ty gb_num gb_str gb_kids gb_keys gb_n gb_cap
  gb_kb gb_yb gb_Lam gb_peak gb_cnt gb_fail gb_ran gb_most gb_own] in *.
destruct HPD as (HPRE & HUNIV & HCH0 & HROOM & HPKS & HPK24 & HHULL & H10 & Hv0 & Hv8 & HH & HSLOT & HAP & HWIN & HAT & HRA
  & HOLD & HLED & HCNT & HLIVE).
(* the live-set counts at the entry state, which is the kids realloc's call state (no allocator step before it): the
   text's two pkR premises at the first state of the all-granted list (pkR_prefix at j = 0, PwGrowG's grow_cnt_at) *)
assert (HSEC : YGcfRoomLive.sec_cnt S <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV)
  by exact (grow_cnt_at YGcfRoomLive.rl_sec_req S S _ 0 _ (Permutation_refl _) HPKS).
assert (HC24 : YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV)
  by exact (grow_cnt_at (PresetRoom.in_cls YG00.kBatchClass) S S _ 0 _ (Permutation_refl _) HPK24).
pose proof HPRE as (HPREX & HROD).
pose proof HPRE as (_ & _ & _ & _ & HFRM).
pose proof HPREX as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (He0 & He16 & Hetop & Hepres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : GROW_FR_B <= @STK_grow prh_img_B) by (apply Z.leb_le; vm_compute; reflexivity).
assert (Hvloc : grow_vloc B ly S regs e v) by exact (grow_vloc_of_at B ly S Hp W mem Lam peak cnt fail ran most own regs e v HLED HAT).
destruct (grow_vbounds B ARx LAWS ly S Hp W mem md (@STK_grow prh_img_B) GROW_FR_B regs e v HAR Hstk
  ltac:(unfold GROW_FR_B; lia) FS He0 Hetop Hvloc) as (Hv4096 & Hvhi & Hvstk & Hoff & Happ).
pose proof (range_apart_img _ _ HC0 Hoff) as Hd0. pose proof (range_apart_img _ _ HC12 Hoff) as Hd12.
destruct (growB_entry B ARx LAWS HGOT HCELL HGC HLH ly S Hp W regs mem md ch v ty num str kids keys n cap HPREX H10 Hv8 Hv4096 Hvhi Hvstk Hd0 Hd12
  Happ HH HRA) as [HS SHOK].
remember ([(v + 24, v + 40); (v + 48, v + 56)] ++ ablocks_fp (prhReader_ab (kids_blkR kids cap ++ keys_blkR ty keys cap)))
  as FP eqn:HFP.
pose proof (ajournal_x_init_WR (SK := SK) SEGS B PST ARx (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (@STK_grow prh_img_B) e FP
  ly S Hp W regs mem md ch HPREX HWIN) as HJ.
assert (HK : cj_keptR (SK := SK) SEGS B PST (wle' SEGS RZ_cf) (@STK_grow prh_img_B) (spZ regs) (grow_OR v) FP ly S W mem md
  ly S W mem md) by exact (cj_kept_reflR (SK := SK) SEGS B PST ARx (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) _ _ _ _ _ _ _ _ _).
unfold cfg_at. rewrite HENT.
unfold fpostWmR. change (fpostWR B ARx SK (wle' SEGS RZ_cf)) with (fpostW_xR (SK := SK) SEGS B PST ARx (wle' SEGS RZ_cf)).
(* THE m-FORM KEEP (fQmn): P := `memnorm mem -> memnorm m` is an invariant of the runs (srr_inv_laws_imp over
   srr_inv_laws_memnorm_k) and of the realloc call (srr_inv_call_imp: the callee's own m-form keep); it holds at
   entry, and at the ret it is the keep. Made opaque here, so no engine computation meets memnorm. *)
set (PM := fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m).
assert (PLAW : srr_inv_laws SEGS PM)
  by exact (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)).
assert (PCALL : srr_inv_call SEGS PM) by exact (srr_inv_call_imp SEGS mem).
assert (PEND : forall m, PM m -> YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) by (intros m Hm; exact Hm).
assert (HPM : PM mem) by (intros Hm; exact Hm).
clearbody PM.
set (E0 := Eimg (PI := PG) (Ereg regs (growB_extra ty kids keys n cap))) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E0) by (subst E0; apply Eimg_env).
assert (HA : env_agree A_LIM E0 E0) by (split; [intros; reflexivity | reflexivity]).
assert (U2 : bv_unsigned (ew E0 2) = spZ regs).
{ subst E0. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
assert (U10 : bv_unsigned (ew E0 10) = v).
{ subst E0. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), H10.
  unfold w64. apply unsigned_lit_small. lia. }
assert (UX : forall j w, (j < 6)%nat -> nth j (growB_extra ty kids keys n cap) (Z_to_bv 64 0) = Z_to_bv 64 w ->
  0 <= w < 2 ^ 64 -> bv_unsigned (ew E0 (32 + j)) = w).
{ intros j w Hj Hw Hr. subst E0. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra, Hw.
  apply unsigned_lit_small. exact Hr. }
pose proof HH as ((_ & HRW0) & (Hty & _) & _ & _ & (Hkids & _) & (Hkeys & _) & (Hn & _) & (Hcap & _)).
pose proof (UX 4%nat n ltac:(lia) eq_refl Hn) as U36. pose proof (UX 5%nat cap ltac:(lia) eq_refl Hcap) as U37.
pose proof (UX 2%nat kids ltac:(lia) eq_refl Hkids) as U34. pose proof (UX 3%nat keys ltac:(lia) eq_refl Hkeys) as U35.
pose proof (UX 0%nat SHADOW_OFF ltac:(lia) eq_refl ltac:(unfold SHADOW_OFF; lia)) as U32.
pose proof (UX 1%nat ty ltac:(lia) eq_refl ltac:(lia)) as U33.
cbn [Nat.add] in U32, U33, U34, U35, U36, U37. clear UX.
assert (HFR : forall x : word, ~ grow_wr GROW_FR_B (spZ regs) v (bv_unsigned x) ->
  mrestrict (w_H W) mem x = mrestrict (w_H W) mem x) by (intros; reflexivity).
assert (HA32 : env_agree 32 (Ereg regs (growB_extra ty kids keys n cap)) E0)
  by (subst E0; apply (agree_Ereg (PA := PG)); split; [intros; reflexivity | reflexivity]).
assert (E3 : ew E0 3 = getr regs 3)
  by (subst E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E0 4 = getr regs 4)
  by (subst E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (ET : ew E0 A_TEXT = Z_to_bv 64 BASE)
  by (subst E0; apply Eimg_img; unfold A_TEXT, A_LIM; lia).
clearbody E0.
assert (Hsp128 : YM05.alloc_ceiling + 128 <= spZ regs) by (assert (128 <= @STK_grow prh_img_B) by
  (apply Z.leb_le; vm_compute; reflexivity); lia).
(* run 1: entry to the bgeu n,cap *)
paj_run_tok_x_inv (RUNBP PM PLAW) HS HJ SHOK HPM growB_Bspan.
- apply (grow_awr_ok_fr _ _ (@STK_grow prh_img_B) GROW_FR_B e (spZ regs) FP _ _ S ly v); [unfold GROW_FR_B; lia | exact FS | exact He0 | | | ].
  + unfold GROW_FR_B; grow_wr_tac U2 U10.
  + intros a Ha. rewrite HFP. exact (grow_FP_v v ty kids keys cap a Ha).
  + exact Hvloc.
- destruct (grow_stretch B ARx SK LAWS (@STK_grow prh_img_B) GROW_FR_B E0 (ss_mem ss_growB0) W mem mem md (ms_mem ms)
    (with_vm_backing (m_vm_lazy md) mat md)
    (spZ regs) v FP ly S Hp W mem md ly S Hp ltac:(unfold GROW_FR_B; lia) FS HK HFR (mem_grows_refl _) HAR HAR
    Hceil Hslo Hshi HFr HG ltac:(unfold GROW_FR_B; grow_wr_tac U2 U10) (same_but_materialized_wvb_any md mat))
    as (HK1 & HFR1 & HGR1).
  clear HF HFr HG HK HFR.
  (* run 1 adds no fresh atom: its state is over E0 (measured; the type of HS says so) *)
  match type of HS with st_ok_pi _ _ E0 _ _ => idtac | _ => fail "run 1 changed the environment" end.
  psrr_branch_tok RUNB BRB HS SHOK growB_Bspan.
  + (* n >= cap *)
    assert (Heq : n = cap).
    { rewrite branch_geu_U in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
      rewrite !U_SOff, U36, U37, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
      destruct HSLOT as (_ & (Hnc & _) & _). lia. }
    pose proof HJ as (HARc & _).
    paj_run_tok_x_inv (RUNBP PM PLAW) HS HJ SHOK HPM growB_Bspan.
    * apply (grow_awr_ok_fr _ _ (@STK_grow prh_img_B) GROW_FR_B e (spZ regs) FP _ _ S ly v);
        [unfold GROW_FR_B; lia | exact FS | exact He0 | | | ].
      -- unfold GROW_FR_B; grow_wr_tac U2 U10.
      -- intros a Ha. rewrite HFP. exact (grow_FP_v v ty kids keys cap a Ha).
      -- exact Hvloc.
    * (* run 3 adds no fresh atom (measured) *)
      match type of HS with st_ok_pi _ _ E0 _ _ => idtac | _ => fail "run 3 changed the environment" end.
      destruct (grow_stretch B ARx SK LAWS (@STK_grow prh_img_B) GROW_FR_B E0 _ W mem (ms_mem ms)
        (with_vm_backing (m_vm_lazy md) mat md) (ms_mem ms0) _
        (spZ regs) v FP ly S Hp W mem md ly S Hp ltac:(unfold GROW_FR_B; lia) FS HK1 HFR1 HGR1 HAR HARc Hceil Hslo Hshi
        HFr HG ltac:(unfold GROW_FR_B; grow_wr_tac U2 U10)
        (same_but_materialized_wvb_any (with_vm_backing (m_vm_lazy md) mat md) mat0))
        as (HK2 & HFR2 & HGR2).
      clear HK1 HFR1 HGR1 HFr HG.
      psrr_branch_tok RUNB BRB HS SHOK growB_Bspan.
      -- (* cap <> 0: s6 := 2 cap; run 4 to the kids realloc (the runner's PTS_call AS_fuzz_realloc at i = 47) *)
         assert (Hcz : cap <> 0).
         { rewrite branch_ne_U in Hc0. apply negb_true_iff, Z.eqb_neq in Hc0.
           rewrite U_SOff, U37, Z.add_0_r, zcanon_id, U_lit in Hc0 by (unfold M64; lia). exact Hc0. }
         pose proof HJ as (HARc4 & _).
         paj_run_tok_x_inv (RUNBP PM PLAW) HS HJ SHOK HPM growB_Bspan.
         ++ apply (grow_awr_ok_fr _ _ (@STK_grow prh_img_B) GROW_FR_B e (spZ regs) FP _ _ S ly v);
              [unfold GROW_FR_B; lia | exact FS | exact He0 | | | ].
            ** unfold GROW_FR_B; grow_wr_tac U2 U10.
            ** intros a Ha. rewrite HFP. exact (grow_FP_v v ty kids keys cap a Ha).
            ** exact Hvloc.
         ++ (* THE KIDS REALLOC (i = 47): the stretch to the call memory, the chain at s0 = v + 48, then aj_call_xW_spR *)
            match type of HS with st_ok _ E0 _ _ => idtac | _ => fail "run 4 changed the environment" end.
            destruct (grow_stretch B ARx SK LAWS (@STK_grow prh_img_B) GROW_FR_B E0 _ W mem (ms_mem ms0)
              _ (ms_mem ms1) _ (spZ regs) v FP ly S Hp W mem md ly S Hp ltac:(unfold GROW_FR_B; lia) FS HK2 HFR2 HGR2
              HAR HARc4 Hceil Hslo Hshi HFr HG ltac:(unfold GROW_FR_B; grow_wr_tac U2 U10)
              (same_but_materialized_wvb_any _ mat1)) as (HK3 & HFR3 & HGR3).
            clear HK2 HFR2 HGR2 HFr HG.
            (* the node's fields at the CALL state, off its two symbolic regions (the entry values, by pj_hdrR) *)
            pose proof HH as (_ & _ & _ & _ & (_ & Vkids) & (_ & Vkeys) & (_ & Vn) & (_ & Vcap)).
            assert (RA : region_ok SEGS E0 (mrestrict (w_H W) (ms_mem ms1)) growB_vA)
              by exact (st_ok_region_nth SEGS E0 _ _ 1 growB_vA HS ltac:(vm_compute; reflexivity)).
            assert (RB : region_ok SEGS E0 (mrestrict (w_H W) (ms_mem ms1)) growB_vB)
              by exact (st_ok_region_nth SEGS E0 _ _ 2 growB_vB HS ltac:(vm_compute; reflexivity)).
            unfold growB_vA in RA. unfold growB_vB in RB.
            pose proof (field_of_region SEGS E0 _ 10 v _ 0 40 24 40 24 8 (SOff 34 0) kids RA U10 ltac:(cbn; tauto)
              ltac:(cbn [sv_denot]; rewrite U34, Z.add_0_r; reflexivity) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia)
              ltac:(cbn; lia)) as Vk2.
            pose proof (field_of_region SEGS E0 _ 10 v _ 0 40 24 40 32 8 (SOff 35 0) keys RA U10 ltac:(cbn; tauto)
              ltac:(cbn [sv_denot]; rewrite U35, Z.add_0_r; reflexivity) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia)
              ltac:(cbn; lia)) as Vy2.
            pose proof (field_of_region SEGS E0 _ 10 v _ 40 56 48 56 40 8 (SOff 36 0) n RB U10 ltac:(cbn; tauto)
              ltac:(cbn [sv_denot]; rewrite U36, Z.add_0_r; reflexivity) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia)
              ltac:(cbn; lia)) as Vn2.
            pose proof (field_of_region SEGS E0 _ 10 v _ 40 56 48 56 48 8 (SOff 37 0) cap RB U10 ltac:(cbn; tauto)
              ltac:(cbn [sv_denot]; rewrite U37, Z.add_0_r; reflexivity) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia)
              ltac:(cbn; lia)) as Vc2.
            (* v's 56 bytes are the entry's at the call: outside grow's windows by the stretches, inside them by the
               field values (grow has written none of them yet) *)
            assert (HVM1 : forall a, v <= a < v + 56 -> aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem a).
            { intros a Ha. pose proof Hvstk as Hvs96. unfold GROW_FR_B in Hvs96.
              assert (HOUT : ~ grow_wr GROW_FR_B (spZ regs) v a -> aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem a).
              { intros Hw. apply aview_eq_of. apply HFR3. rewrite unsigned_lit_small by lia. exact Hw. }
              destruct (Z_lt_ge_dec a (v + 24)) as [A0 | A0].
              { apply HOUT. unfold grow_wr, GROW_FR_B. intros [Hw | [Hw | Hw]]; lia. }
              destruct (Z_lt_ge_dec a (v + 32)) as [A1 | A1].
              { exact (aview_of_val_mem_eq (w_H W) mem (ms_mem ms1) (v + 24) kids Vkids Vk2 a ltac:(lia)). }
              destruct (Z_lt_ge_dec a (v + 40)) as [A2 | A2].
              { exact (aview_of_val_mem_eq (w_H W) mem (ms_mem ms1) (v + 32) keys Vkeys Vy2 a ltac:(lia)). }
              destruct (Z_lt_ge_dec a (v + 48)) as [A3 | A3].
              { exact (aview_of_val_mem_eq (w_H W) mem (ms_mem ms1) (v + 40) n Vn Vn2 a ltac:(lia)). }
              exact (aview_of_val_mem_eq (w_H W) mem (ms_mem ms1) (v + 48) cap Vcap Vc2 a ltac:(lia)). }
            (* the kit's entry chain (HCH0), transported to the call view with image A's achain_kept_hi *)
            assert (HCH2 : exists ch1, achain ly (aview SEGS (w_H W) (ms_mem ms1)) (spZ regs - GROW_FR_B) (v + 48) ch1).
            { destruct (Z_lt_ge_dec (v + 48) YM05.alloc_ceiling) as [Hlo48 | Hhi48].
              { exists []. apply achain_low. exact Hlo48. }
              assert (Hvsp : spZ regs <= v).
              { destruct Hvloc as [(b & m & Hinb & H1 & H2) | [(cid & pos & Hinf & H1 & H2) | Hx]].
                - destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hinb) as (_ & _ & Hbc & _).
                  assert (Hqm : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia). lia.
                - destruct (alx_sep _ _ _ LAWS _ _ _ _ _ _ HAR) as (_ & Hfr).
                  pose proof (proj1 (Forall_forall _ _) Hfr (cid, pos) Hinf) as (_ & Hfc). cbn [fst snd] in Hfc. lia.
                - lia. }
              destruct HCH0 as (ch0 & Hch0). exists ch0.
              assert (HS0 : @prh_s0 prh_img_B F_grow v = v + 48) by (vm_compute; reflexivity).
              rewrite HS0, <- GROW_FR_B_ok in Hch0.
              refine (achain_kept_hi _ _ _ _ _ _ Hch0 ltac:(lia) _).
              intros a Ha Hb.
              destruct (Z_lt_ge_dec a (v + 56)) as [A3 | A3]; [apply HVM1; lia |].
              apply aview_eq_of. apply HFR3. unfold grow_wr, GROW_FR_B.
              rewrite unsigned_lit_small by lia.
              intros [Hw | [Hw | Hw]]; lia. }
            destruct HCH2 as (ch1 & Hch1).
            (* the call state's registers: s0 = v + 48, a0 = kids, a1 = 112 cap (= 56 * cap2R cap) *)
            pose proof (st_ok_restrict_reg SEGS (w_H W) _ _ ms1 8%bv HS) as R8.
            pose proof (st_ok_restrict_reg SEGS (w_H W) _ _ ms1 10%bv HS) as R10.
            pose proof (st_ok_restrict_reg SEGS (w_H W) _ _ ms1 11%bv HS) as R11.
            match type of R8 with _ = sv_denot _ ?t => let t' := eval vm_compute in t in change t with t' in R8 end.
            match type of R10 with _ = sv_denot _ ?t => let t' := eval vm_compute in t in change t with t' in R10 end.
            match type of R11 with _ = sv_denot _ ?t => let t' := eval vm_compute in t in change t with t' in R11 end.
            pose proof HSLOT as (_ & (Hncap & Hcap54) & _ & Hpos).
            destruct (HLIVE Heq) as (Hnmax0 & HLv).
            destruct (HOLD Heq) as (Hkb & Hkbl & _).
            pose proof HROD as (HRO0 & Hhi0).
            pose proof cf_head_nonneg as Hh0.
            assert (Hc2 : cap2R cap = 2 * cap) by (unfold cap2R; rewrite (proj2 (Z.eqb_neq cap 0) Hcz); reflexivity).
            assert (Hsp1 : spZ (ms_regs ms1) = spZ regs - GROW_FR_B).
            { pose proof (st_ok_restrict_reg SEGS (w_H W) _ _ ms1 2%bv HS) as R2.
              match type of R2 with _ = sv_denot _ ?t => let t' := eval vm_compute in t in change t with t' in R2 end.
              unfold spZ at 1; rewrite R2; cbn [sv_denot]; rewrite U2, unsigned_lit_small by lia.
              unfold GROW_FR_B; lia. }
            assert (Hhic : spZ (ms_regs ms1) + 64 <= ly_stk_hi ly) by (rewrite Hsp1; unfold GROW_FR_B; lia).
            (* the read-only image view at the call memory: image bytes, apart from grow's frame and from v *)
            assert (HRODc : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) (ms_mem ms1))).
            { intros a Hro Ho He.
              assert (Himg : in_img SEGS a)
                by (destruct Hro as [(s & Hs & _ & Hlo & Hhi) | Hr]; [exists s; split; [exact Hs | lia] | apply pa_relro_img; exact Hr]).
              pose proof (pa_segs_low a Himg) as Hl. unfold kLowMemEnd in Hl.
              rewrite <- (HRO0 a Hro Ho He). apply aview_eq_of. apply HFR3. unfold grow_wr, GROW_FR_B.
              rewrite unsigned_lit_small by lia.
              intros [Hw | [Hw | Hw]]; [lia | exact (Hoff a ltac:(lia) Himg) | exact (Hoff a ltac:(lia) Himg)]. }
            assert (HMU : prh_malloc_univ B) by (eapply prh_univ_closure_malloc; [exact HUNIV | vm_compute; discriminate]).
            assert (HUR : In [cf_pc_realloc_ra0] (u_fix (as_universe B)) /\
                          In (prh_trace cf_pc_realloc_ra0 pi_ret_realloc []) (u_fix (as_universe B)))
              by (eapply prh_univ_closure_realloc; [exact HUNIV | vm_compute; discriminate]).
            assert (H10c : getr (ms_regs ms1) 10%bv = w64 kids) by (rewrite R10; cbn [sv_denot]; rewrite U34, Z.add_0_r; reflexivity).
            assert (H11c : getr (ms_regs ms1) 11%bv = w64 (56 * cap2R cap)).
            { rewrite R11. apply bv_eq.
              change (bv_unsigned (sv_denot E0 (SMd M_MUL (SOff 37 0) (SLit 112))))
                with (U E0 (SMd M_MUL (SOff 37 0) (SLit 112))).
              rewrite U_SMd, U_lit by lia. unfold U at 1. cbn [sv_denot]. rewrite U37, Z.add_0_r, unsigned_lit_small by lia.
              cbn [zmd_raw]. unfold w64. rewrite Hc2, unsigned_lit_small by lia.
              rewrite zcanon_id by (unfold M64; lia). lia. }
            assert (Hn0 : 0 <= 56 * cap2R cap) by (rewrite Hc2; lia).
            (* the kids call's live room: the text's per-event room at the first event (PwGrowLive's grow_room_kids) *)
            rewrite Heq in HLv.
            assert (HLIVEc : blocks_bytes S + (56 * cap2R cap + cf_head) <= LIVE_MAX) by exact (grow_room_kids B ly S _ _ HLv).
            (* the ledger at the call memory: its cells are apart from grow's writes *)
            assert (HLEDc : prh_ledger B ly S Hp W (ms_mem ms1) Lam peak cnt fail ran most own).
            { apply (prh_ledger_keep B ly S Hp W mem (ms_mem ms1) Lam peak cnt fail ran most own HLED).
              intros a Hca.
              destruct (grow_cell_apart B ARx LAWS HPST GROW_FR_B ly S Hp W mem md Lam peak cnt fail ran most own regs e v a
                ltac:(unfold GROW_FR_B; lia) HAR HLED HAT Hsp128 Hoff Hca) as (Ha64 & Hwa).
              apply HFR3. rewrite unsigned_lit_small by exact Ha64. exact Hwa. }
            (* the old kids block: a ledger entry (pj_slots_atR at 0 < cap), its bytes kept (a slot block of FP) *)
            assert (HinK : In (kids - cf_head, kids - cf_head + req_size (56 * cap + cf_head))
                             (ablocks_fp (prhReader_ab (kids_blkR kids cap ++ keys_blkR ty keys cap)))).
            { unfold ablocks_fp, prhReader_ab, kids_blkR. rewrite (proj2 (Z.eqb_neq cap 0) Hcz).
              cbn [app map fst snd]. left. reflexivity. }
            assert (HOLDc : In (kids, 56 * cap) Lam /\ bytes_at W (ms_mem ms1) kids kb /\ Z.of_nat (length kb) = 56 * cap).
            { split; [exact (proj1 (Hpos ltac:(lia))) |]. split; [|exact Hkbl].
              unfold bytes_at in *. apply (garr8R_frame SEGS _ _ _ _ Hkb). intros x Hx. rewrite Hkbl in Hx.
              assert (Hrq : 56 * cap + cf_head <= req_size (56 * cap + cf_head))
                by (unfold req_size; destruct (Z.eqb_spec (56 * cap + cf_head) 0); lia).
              destruct (grow_slot_apart B ARx LAWS GROW_FR_B ly S Hp W mem md Lam peak cnt fail ran most own regs e v ty kids keys n cap
                _ _ x ltac:(unfold GROW_FR_B; lia) ltac:(lia) HAR HLED HAT Hsp128 HSLOT HAP HinK ltac:(lia)) as (Hx64 & Hxw).
              unfold mbyte. rewrite HFR3; [reflexivity|]. rewrite unsigned_lit_small by exact Hx64. exact Hxw. }
            (* what the re-seat after the call needs from the call state: ra, the caller's journal there *)
            assert (R1 : getr (ms_regs ms1) 1%bv = Z_to_bv 64 (BASE + (GROW_OFF_B + 4 * 48))).
            { pose proof (st_ok_restrict_reg SEGS (w_H W) _ _ ms1 1%bv HS) as R1.
              match type of R1 with _ = sv_denot _ ?t => let t' := eval vm_compute in t in change t with t' in R1 end.
              rewrite R1. cbn [sv_denot]. change 240%nat with A_TEXT. rewrite ET.
              pose proof (@pa_val_range _ B_prog_listing PG A_TEXT) as HBr.
              rewrite unsigned_lit_small by lia. reflexivity. }
            (* fpre's return-address bound for the callee: the return slot i = 48 (growB_ret48_ceil) *)
            assert (Hra1 : raZ (ms_regs ms1) < YM05.alloc_ceiling) by (unfold raZ; rewrite R1; exact growB_ret48_ceil).
            pose proof HJ as (HARc5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRc & _).
            (* the old kids block is a live harness block, so kids is not NULL (kids = 0 <-> cap = 0 at cap <> 0) *)
            assert (Hk4096 : 4096 + cf_head <= kids).
            { pose proof HLEDc as (_ & _ & HFl & _).
              pose proof (proj1 (Forall_forall _ _) HFl (kids, 56 * cap) (proj1 HOLDc)) as (_ & Hb & _). cbn [fst snd] in Hb.
              destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HARc5 Hb) as (_ & H4 & _). lia. }
            assert (Hkids0 : kids <> 0) by (clear - Hk4096; pose proof cf_head_nonneg; lia).
            assert (HKC0 : kids = 0 <-> cap = 0) by (split; intros Hz; exfalso; [exact (Hkids0 Hz) | exact (Hcz Hz)]).
            (* THE HULL BUDGET of the kids call: its one event, from grow's budget at n = cap (PwGrowG's grow_hull_kids,
               the event in the realloc text's form by grow_hull_ev) *)
            assert (HHUK : PresetHullBudget.hull_budget S (if kids =? 0 then [PresetReqAt.HMal (56 * cap2R cap + cf_head)]
              else [PresetReqAt.HRe (56 * cap + cf_head) (56 * cap2R cap + cf_head)])).
            { rewrite (grow_hull_ev kids 56 cap HKC0). rewrite Heq in HHULL. exact (grow_hull_kids S (ty =? 6) cap HHULL). }
            eapply (SRr'_bind SEGS RZ_cf).
            { match type of HS with st_ok _ ?Ec ?ss4 (restrict _ ?ms4) =>
                eapply (aj_call_xW_spR (SK := SK) SEGS B PST ARx LAWS pa_segs_low (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf)
                  (wle'_trans SEGS RZ_cf) W Ec ss4 ms4 _ _ FP ly S Hp W mem md []
                  ly S Hp _ _ (@STK_fuzz_realloc prh_img_B) 0
                  (if kids =? 0 then [] else ablocks_fp [(kids - cf_head, 56 * cap + cf_head)])
                  (- GROW_FR_B - e) _ ch1 _ HS) end;
              [ vm_compute; reflexivity
              | exact HJ
              | (* sp at the call: reg 2 is SOff 2 (-96) *)
                match goal with |- spZ (ms_regs ?m) = _ =>
                  pose proof (st_ok_restrict_reg SEGS (w_H W) _ _ m 2%bv HS) as R2 end;
                match type of R2 with _ = sv_denot _ ?t => let t' := eval vm_compute in t in change t with t' in R2 end;
                unfold spZ at 1; rewrite R2; cbn [sv_denot]; rewrite U2, unsigned_lit_small by lia;
                unfold GROW_FR_B; lia
              | rewrite <- Zminus_mod_idemp_r, He16; vm_compute; reflexivity
              | unfold GROW_FR_B; lia
              | apply Z.leb_le; vm_compute; reflexivity
              | unfold GROW_FR_B;
                assert (Hs96 : @STK_grow prh_img_B = 96 + @STK_fuzz_realloc prh_img_B) by (vm_compute; reflexivity); lia
              | lia
              | reflexivity
              | unfold GROW_FR_B; lia
              | (* gp: reg 3 is the entry's *)
                match goal with |- getr (ms_regs ?m) _ = _ =>
                  rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ m 3%bv HS) end;
                match goal with |- sv_denot _ ?t = _ => let t' := eval vm_compute in t in change t with t' end;
                cbn [sv_denot]; rewrite E3, Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp
              | (* tp: reg 4 is the entry's *)
                match goal with |- getr (ms_regs ?m) _ = _ =>
                  rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ m 4%bv HS) end;
                match goal with |- sv_denot _ ?t = _ => let t' := eval vm_compute in t in change t with t' end;
                cbn [sv_denot]; rewrite E4, Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp
              | reflexivity
              | (* ret_ok of the return site BASE + GROW_OFF_B + 4 * 48: BASE is 4-aligned (pa_B_ok) *)
                unfold YK0s.ret_ok;
                match goal with |- v_jalr (getr (ms_regs ?m) _) _ = _ =>
                  rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ m 1%bv HS) end;
                match goal with |- v_jalr (sv_denot _ ?t) _ = _ =>
                  let t' := eval vm_compute in t in change t with t' end;
                cbn [sv_denot]; change 240%nat with A_TEXT; rewrite ET;
                pose proof (@pa_val_range _ B_prog_listing PG A_TEXT) as HBr;
                pose proof (@pa_B_ok _ B_prog_listing PG) as (HB0 & HB40 & HB4);
                assert (HUB : bv_unsigned (Z_to_bv 64 BASE) = BASE) by (apply unsigned_lit_small; lia);
                rewrite HUB; unfold v_jalr, jalr_tgtZ; rewrite unsigned_lit_small by lia; rewrite Z.add_0_r;
                rewrite land_m2_even; [reflexivity|];
                let k := eval vm_compute in (GROW_OFF_B + 4 * 48) in change k with (GROW_OFF_B + 4 * 48); unfold GROW_OFF_B;
                replace (BASE + (4 * 5731 + 4 * 48)) with ((2 * (BASE / 4) + 2 * 5731 + 2 * 48) * 2)
                  by (pose proof (Z.div_mod BASE 4 ltac:(lia)); lia);
                apply Z.mod_mul; lia
              | (* the return site BASE + GROW_OFF_B + 4 * 48 is above 4096 *)
                match goal with |- _ <= bv_unsigned (getr (ms_regs ?m) _) =>
                  rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ m 1%bv HS) end;
                match goal with |- _ <= bv_unsigned (sv_denot _ ?t) =>
                  let t' := eval vm_compute in t in change t with t' end;
                cbn [sv_denot]; change 240%nat with A_TEXT; rewrite ET;
                pose proof (@pa_val_range _ B_prog_listing PG A_TEXT) as HBr;
                pose proof (@pa_B_ok _ B_prog_listing PG) as (HB0 & HB40 & _);
                assert (HUB : bv_unsigned (Z_to_bv 64 BASE) = BASE) by (apply unsigned_lit_small; lia);
                rewrite HUB; rewrite unsigned_lit_small by lia; lia
              | (* the chain at s0 = v + 48: reg 8 is SOff 10 48 *)
                unfold s0Z; rewrite R8; cbn [sv_denot]; rewrite U10, unsigned_lit_small by lia;
                match goal with |- achain _ _ ?spx _ _ => replace spx with (spZ regs - GROW_FR_B) by lia end;
                exact Hch1
              | (* the callee: the kit's tfuzz_realloc_specX (HREALLOC) at the call state, through fpostW_x_of_apostR *)
                intros Hpre Hwin;
                eapply (SRr'_mono SEGS RZ_cf);
                [ refine (HREALLOC ly S Hp W (ms_regs ms1) (ms_mem ms1) _ ch1 kids
                    (56 * cap) (56 * cap2R cap) kb Lam peak cnt fail ran most own
                    (conj Hpre (conj HRODc (conj Hhic (conj Hra1 HFRM))))
                    HROOM HMU HSEC HC24 HHUK (proj1 HUR) (proj2 HUR)
                    H10c H11c Hn0 Hnmax0 HLEDc (or_intror HOLDc) (fun _ => HLIVEc))
                | intros W2 c2 _ HP2; apply fpostW_x_of_apostR; exact HP2 ]
              | (* fp_sub_x: the callee's footprint, the old kids block, lies in the kit's FP *)
                intros a Ha; left; rewrite HFP;
                destruct (Z.eqb_spec kids 0) as [Hk0 | Hk0]; [destruct Ha as (r & [] & _) |];
                destruct Ha as (r & Hr & Hb); exists r; split; [| exact Hb];
                apply in_or_app; right;
                cbn [ablocks_fp map In] in Hr; destruct Hr as [<- | []];
                apply in_map_iff; exists (kids - cf_head, 56 * cap + cf_head); split; [reflexivity|];
                unfold prhReader_ab; apply in_map_iff; exists (kids, 56 * cap); split; [reflexivity|];
                apply in_or_app; left; unfold kids_blkR; rewrite (proj2 (Z.eqb_neq cap 0) Hcz); left; reflexivity ]. }
            intros W2 c2 HW2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJ1 & _ & HP2 & HQ).
            (* the realloc's post (the cut's tfuzz_realloc_specX): its result, room_live_cf, its hull use HHU1, the position
               transfer of each outcome (HPOS0 on a NULL, HPOSR on a grant), its OUTCOME clause, its arms; and its m-form
               keep HMN1 *)
            destruct HQ as ((res & H10r & HRL2 & HHU1 & HPOS0 & _ & HPOSR & _ & HOUTR & HARMS) & HMN1).
            rewrite (grow_hull_ev kids 56 cap HKC0) in HHU1.
            (* the m-form keep across the call: the callee's own keep HMN1 (srr_inv_call) *)
            pose proof (PCALL _ _ HMN1 HPM) as HPM2. clear HPM. rename HPM2 into HPM.
            (* kids is not NULL (Hkids0): the callee's p = 0 arm is out *)
            destruct HARMS as [(Hk0 & _) | HARMS]; [lia |].
            (* the node across the call: its 56 bytes kept and present (PwGrowG's grow_v_kept) *)
            assert (HVK : forall a, v <= a < v + 56 ->
              aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) (ms_mem ms1) a /\ apresent (w_H W2) mem2 a).
            { apply (grow_v_kept B ARx SK LAWS ly S Hp W (ms_mem ms1) _ Lam peak cnt fail ran most own regs e v ty kids keys n cap
                _ _ _ ly2 S2 Hp2 W2 mem2 md2 k1 ltac:(lia) HARc5 HLEDc HAT Hsp128 Hv4096 ltac:(lia) Hoff
                ltac:(intros a Ha; apply HPRc; lia) HSLOT HAP HJ1 ltac:(unfold GROW_FR_B; lia)).
              intros r Hr. rewrite (proj2 (Z.eqb_neq kids 0) ltac:(lia)) in Hr.
              cbn [ablocks_fp map In] in Hr; destruct Hr as [<- | []].
              apply in_map_iff; exists (kids - cf_head, 56 * cap + cf_head); split; [reflexivity|].
              unfold prhReader_ab; apply in_map_iff; exists (kids, 56 * cap); split; [reflexivity|].
              apply in_or_app; left; unfold kids_blkR; rewrite (proj2 (Z.eqb_neq cap 0) Hcz); left; reflexivity. }
            pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & G1c & G2c & _).
            assert (Hbkids : In (kids - cf_head, 56 * cap + cf_head) (ablocks B ly S)).
            { pose proof HLEDc as (_ & _ & HFk & _).
              exact (proj1 (proj2 (proj1 (Forall_forall _ _) HFk (kids, 56 * cap) (proj1 HOLDc)))). }
            pose proof HJ2 as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES2 & _).
            destruct Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & Htop2' & Hslo2 & Hshi2 & _).
            destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HARc5) as (Kc1 & _ & Kg1 & _).
            destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HAR2) as (Kc2 & _ & Kg2 & _).
            rewrite HGOT, HCELL in Kg1, Kg2. rewrite HCELL in Kc1, Kc2.
            rewrite R1.
            (* RE-SEAT at the return site (i = 48): the caller-saved registers havocked into atoms 38...
               KEPT REGIONS: grow's frame (the callee's window is below it) and the two image cells (allocator
               constants at both states). The node's two regions are DROPPED here: a region whose window meets the
               shadow band needs a shadow-window entry (YCbn's cells_safe_b), i.e. v's shadow at the post state,
               which the callee's journal does not keep; the arms that read v again re-seat them with it. v's bytes
               themselves are kept as a memory fact (HVK). *)
            jafter_call_keep_pi HS 38%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 3; 4]%nat HS2.
            match type of HS2 with ?P -> _ => assert (HQ : P); [|specialize (HS2 HQ); clear HQ] end.
            { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
              - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite U2; intros a Ha.
                + apply (mbyte_of_aview SEGS). apply G1c; unfold GROW_FR_B in *; lia.
                + intros _. apply (apresent_writable SEGS). apply HPRES2. unfold GROW_FR_B in *; lia.
              - apply (region_kept_val_at E0 _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12)));
                [exact (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kg1)
                | exact (val_mem_of_rdword SEGS _ _ _ _ Kg2) | lia].
              - apply (region_kept_val_at E0 _ _ (A_OBJ 12) (VAL (A_OBJ 12)) 8 SHADOW_OFF);
                [exact (HEI (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kc1)
                | exact (val_mem_of_rdword SEGS _ _ _ _ Kc2) | lia]. }
            clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
            (* the environment after the call: the caller-saved registers are fresh atoms 38.. (below A_TEXT) *)
            set (E1 := havoc E0 38 (map (getr regs2) CLOB)) in HS.
            assert (HEI1' : img_env VAL A_LIM E1) by (subst E1; apply img_env_havoc; [exact HEI | cbv; lia]).
            (* a0 at the return site is the fresh atom 42 = the callee's result register *)
            pose proof (st_ok_pi_restrict_reg (w_H W2) E1 _ _ 10%bv HS) as R10r.
            match type of R10r with _ = sv_denot _ ?t => let t' := eval vm_compute in t in change t with t' in R10r end.
            cbn [ms_regs mkst] in R10r.
            assert (AGo : forall i, (i < 38)%nat -> ew E1 i = ew E0 i) by (intros i Hi; subst E1; apply ew_havoc_old; lia).
            assert (U2' : bv_unsigned (ew E1 2) = spZ regs) by (rewrite AGo by lia; exact U2).
            assert (U10' : bv_unsigned (ew E1 10) = v) by (rewrite AGo by lia; exact U10).
            assert (U34' : bv_unsigned (ew E1 34) = kids) by (rewrite AGo by lia; exact U34).
            assert (U35' : bv_unsigned (ew E1 35) = keys) by (rewrite AGo by lia; exact U35).
            assert (U36' : bv_unsigned (ew E1 36) = n) by (rewrite AGo by lia; exact U36).
            assert (U37' : bv_unsigned (ew E1 37) = cap) by (rewrite AGo by lia; exact U37).
            assert (ET' : ew E1 A_TEXT = Z_to_bv 64 BASE)
              by (subst E1; rewrite ew_havoc_above by (unfold A_TEXT; cbv; lia); exact ET).
            assert (HA1 : env_agree 32 (Ereg regs (growB_extra ty kids keys n cap)) E1)
              by (subst E1; apply env_agree_havoc_ge; [lia | exact HA32]).
            (* E1's body is no longer needed: opaque from here, so no later conversion unfolds the havoc (Qed cost) *)
            clearbody E1.
            (* grow_vloc at the callee's post state (PwGrowG grow_vloc2), for the runs after the call *)
            assert (HFPsub : forall r, In r (if kids =? 0 then [] else ablocks_fp [(kids - cf_head, 56 * cap + cf_head)]) ->
              In r (ablocks_fp (prhReader_ab (kids_blkR kids cap ++ keys_blkR ty keys cap)))).
            { intros r Hr. rewrite (proj2 (Z.eqb_neq kids 0) ltac:(lia)) in Hr.
              cbn [ablocks_fp map In] in Hr; destruct Hr as [<- | []].
              apply in_map_iff; exists (kids - cf_head, 56 * cap + cf_head); split; [reflexivity|].
              unfold prhReader_ab; apply in_map_iff; exists (kids, 56 * cap); split; [reflexivity|].
              apply in_or_app; left; unfold kids_blkR; rewrite (proj2 (Z.eqb_neq cap 0) Hcz); left; reflexivity. }
            assert (HVL2 : grow_vloc B ly2 S2 regs e v)
              by exact (grow_vloc2 B ARx SK LAWS ly S Hp W (ms_mem ms1) _ Lam peak cnt fail ran most own regs e v ty kids keys n cap
                   _ _ _ ly2 S2 Hp2 W2 mem2 md2 k1 ltac:(lia) HARc5 HLEDc HAT Hsp128 HSLOT HAP HJ1 HFPsub).
            (* the same, in the shape the runs' write premise takes: blocks of (ly2, S2), frames of S (own = []) *)
            assert (HVL2' : (exists b m, In (b, m) (ablocks B ly2 S2) /\ b <= v /\ v + 56 <= b + req_size m) \/
              (exists cid pos, In (cid, pos) (frames S) /\
                 frame_addr ly2 cid pos <= v /\ v + 56 <= frame_addr ly2 cid pos + fs_frame_bytes cid) \/
              (spZ regs <= v /\ v + 56 <= spZ regs + e)).
            { pose proof HJ1 as (_ & _ & _ & _ & _ & Hfrs1 & _).
              destruct HVL2 as [Hx | [Hx | Hx]]; [left; exact Hx | right; left | right; right; exact Hx].
              destruct Hx as (cid & pos & Hin & Hx1 & Hx2). exists cid, pos.
              rewrite Hfrs1 in Hin. cbn [app] in Hin. split; [exact Hin | split; [exact Hx1 | exact Hx2]]. }
            (* the kept relation from entry to the post state: the entry stretches, then the callee's journal *)
            rewrite ?wvb_collapse in HK3, HJ2, HJ1.
            assert (HKC : cj_keptR (SK := SK) SEGS B PST (wle' SEGS RZ_cf) (@STK_grow prh_img_B) (spZ regs) (grow_OR v) FP
              ly S W mem md ly2 S2 W2 mem2 md2).
            { eapply (cj_kept_transR (SK := SK) SEGS B PST ARx LAWS (wle' SEGS RZ_cf) (wle'_trans SEGS RZ_cf)
                (@STK_grow prh_img_B) (spZ regs)
                (@STK_fuzz_realloc prh_img_B + 0) (spZ regs + e + (- GROW_FR_B - e) + 0) (grow_OR v) FP _ FP
                ly S Hp W mem md ly S Hp W (ms_mem ms1) _ ly2 S2 W2 mem2 md2 HK3
                (cj_kept_of_journalR (SK := SK) SEGS B PST ARx (wle' SEGS RZ_cf) _ _ _ ly S Hp W (ms_mem ms1) _
                   ly2 S2 Hp2 W2 mem2 md2 _ (grow_OR v) HJ1)
                HAR HARc5); [ | | intros a Ha; left; exact Ha | ].
              - assert (Hs96 : @STK_grow prh_img_B = 96 + @STK_fuzz_realloc prh_img_B) by (vm_compute; reflexivity).
                unfold GROW_FR_B; lia.
              - unfold GROW_FR_B; lia.
              - intros a Ha. left. rewrite HFP.
                destruct Ha as (r & Hr & Hb). exists r. split; [| exact Hb].
                apply in_or_app. right. exact (HFPsub r Hr). }
            (* run 5: the return site to the `beqz a0` (i = 49). No shadow byte is read on it, so the empty window *)
            assert (SHOK0 : sh_ok SEGS growB_Bx [] E1 (mrestrict (w_H W2) mem2)) by (unfold sh_ok; apply Forall_nil).
            paj_run_tok_x_inv (RUNBP PM PLAW) HS HJ2 SHOK0 HPM growB_Bspan.
            ** (* the write premise is at the journal's states: blocks of (ly2, S2), frames of S (own = []) *)
               apply (grow_awr_ok_fr _ _ (@STK_grow prh_img_B) GROW_FR_B e (spZ regs) FP _ _ S ly2 v);
                 [unfold GROW_FR_B; lia | exact FS | exact He0 | | | ].
               --- unfold GROW_FR_B; grow_wr_tac U2' U10'.
               --- intros a Ha. rewrite HFP. exact (grow_FP_v v ty kids keys cap a Ha).
               --- exact HVL2'.
            ** (* run 5 adds no fresh atom (measured) *)
               match type of HS with st_ok_pi _ _ E1 _ _ => idtac | _ => fail "run 5 changed the environment" end.
               destruct (grow_stretch B ARx SK LAWS (@STK_grow prh_img_B) GROW_FR_B E1 _ W2 mem2 mem2
                 md2 (ms_mem ms2) _ (spZ regs) v FP ly S Hp W mem md ly2 S2 Hp2 ltac:(unfold GROW_FR_B; lia) FS
                 HKC ltac:(intros; reflexivity) (mem_grows_refl _) HAR HAR2
                 ltac:(rewrite Hslo2; exact Hceil) ltac:(rewrite Hslo2; exact Hslo) ltac:(rewrite Hshi2; exact Hshi)
                 HFr HG ltac:(unfold GROW_FR_B; grow_wr_tac U2' U10') (same_but_materialized_wvb_any md2 mat2))
                 as (HK5 & HFR5 & HGR5).
               (* v's bytes across run 5: the state has no region over v, so its only write range is the frame *)
               assert (HV5 : forall a, v <= a < v + 56 ->
                 aview SEGS (w_H W2) (ms_mem ms2) a = aview SEGS (w_H W2) mem2 a).
               { intros a Ha. pose proof Hvstk as Hvs96. unfold GROW_FR_B in Hvs96.
                 apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by lia.
                 intros (r & Hin & Hr); vm_compute in Hin;
                 repeat (destruct Hin as [Hin | Hin];
                   [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U2' in Hr; clear - Ha Hvs96 Hr; lia |]);
                 contradiction. }
               assert (HV5all : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - GROW_FR_B <= x < spZ regs) ->
                 aview SEGS (w_H W2) (ms_mem ms2) x = aview SEGS (w_H W2) mem2 x).
               { intros x Hx Hnf. unfold GROW_FR_B in Hnf.
                 apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by lia.
                 intros (r & Hin & Hr); vm_compute in Hin;
                 repeat (destruct Hin as [Hin | Hin];
                   [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U2' in Hr; lia |]);
                 contradiction. }
               psrr_branch_tok RUNB BRB HS SHOK0 growB_Bspan.
               --- (* a0 = 0: the kids realloc returned NULL (the chosen-failure or the refused arm) *)
                   pose proof HJ2 as (HARc6 & _).
                   paj_run_tok_x_inv (RUNBP PM PLAW) HS HJ2 SHOK0 HPM growB_Bspan.
                   +++ apply (grow_awr_ok_fr _ _ (@STK_grow prh_img_B) GROW_FR_B e (spZ regs) FP _ _ S ly2 v);
                         [unfold GROW_FR_B; lia | exact FS | exact He0 | | | ].
                       *** unfold GROW_FR_B; grow_wr_tac U2' U10'.
                       *** intros a Ha. rewrite HFP. exact (grow_FP_v v ty kids keys cap a Ha).
                       *** exact HVL2'.
                   +++ match type of HS with st_ok_pi _ _ E1 _ _ => idtac | _ => fail "run 6 changed the environment" end.
                       destruct (grow_stretch B ARx SK LAWS (@STK_grow prh_img_B) GROW_FR_B E1 _ W2 mem2 (ms_mem ms2)
                         _ (ms_mem ms3) _ (spZ regs) v FP ly S Hp W mem md ly2 S2 Hp2 ltac:(unfold GROW_FR_B; lia) FS
                         HK5 HFR5 HGR5 HAR HARc6 ltac:(rewrite Hslo2; exact Hceil) ltac:(rewrite Hslo2; exact Hslo)
                         ltac:(rewrite Hshi2; exact Hshi) HFr0 HG0 ltac:(unfold GROW_FR_B; grow_wr_tac U2' U10')
                         (same_but_materialized_wvb_any _ mat3)) as (HK6 & HFR6 & HGR6).
                       assert (HV6 : forall a, v <= a < v + 56 ->
                         aview SEGS (w_H W2) (ms_mem ms3) a = aview SEGS (w_H W2) mem2 a).
                       { intros a Ha. pose proof Hvstk as Hvs96. unfold GROW_FR_B in Hvs96.
                         rewrite <- (HV5 a Ha). apply aview_eq_of. apply HFr0.
                         rewrite unsigned_lit_small by lia.
                         intros (r & Hin & Hr); vm_compute in Hin;
                         repeat (destruct Hin as [Hin | Hin];
                           [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U2' in Hr; clear - Ha Hvs96 Hr; lia |]);
                         contradiction. }
                       (* the node at the RET memory: the entry header, by the three keeps *)
                       assert (HAG : pj_agreeR SEGS (mrestrict (w_H W) mem) (mrestrict (w_H W2) (ms_mem ms3))
                         (fun x => v <= x < v + 56)).
                       { intros x Hx. split.
                         - apply (mbyte_of_aview SEGS). rewrite (HV6 x Hx). rewrite (proj1 (HVK x Hx)). exact (HVM1 x Hx).
                         - intros _. apply (apresent_writable SEGS).
                           destruct (HVK x Hx) as (_ & Hpr2). unfold apresent in *.
                           split; [exact (proj1 Hpr2)|].
                           destruct (proj2 Hpr2) as (b & Hb).
                           destruct (mrestrict (w_H W2) (ms_mem ms3) (Z_to_bv 64 x)) as [b'|] eqn:Em;
                             [exists b'; unfold mrestrict in Em; destruct (w_H W2 (Z_to_bv 64 x)); [discriminate | exact Em] |].
                           exfalso. apply (HGR6 (Z_to_bv 64 x)); [| exact Em].
                           unfold mrestrict. rewrite (proj1 Hpr2). rewrite Hb. discriminate. }
                       assert (HHDR : pj_hdrR SEGS (mrestrict (w_H W2) (ms_mem ms3)) v ty num str kids keys n cap)
                         by exact (pj_hdrR_frame _ _ _ _ _ _ _ _ _ _ _ HH HAG).
                       (* the ledger at the ret memory, from the callee's, across grow's own (empty) writes *)
                       pose proof HLED as HLEDb. eapply prh_ledger_bounds in HLEDb.
                       destruct HLEDb as (_ & _ & Hcnt64 & _).
                       assert (Hmod : (cnt + 1) mod 2 ^ 64 = cnt + 1) by (apply Z.mod_small; lia).
                       assert (HLEDKEEP : forall Lm pk ct fl rn,
                         prh_ledger B ly2 S2 Hp2 W2 mem2 Lm pk ct fl rn most own ->
                         (forall a, prh_cell Lm a -> prh_cell Lam a) ->
                         prh_ledger B ly2 S2 Hp2 W2 (ms_mem ms3) Lm pk ct fl rn most own).
                       { intros Lm pk ct fl rn HL2 Hsub.
                         apply (prh_ledger_keep B ly2 S2 Hp2 W2 mem2 (ms_mem ms3) Lm pk ct fl rn most own HL2).
                         intros a Hca.
                         destruct (grow_cell_apart B ARx LAWS HPST GROW_FR_B ly S Hp W mem md Lam peak cnt fail ran most own regs e v a
                           ltac:(unfold GROW_FR_B; lia) HAR HLED HAT Hsp128 Hoff (Hsub a Hca)) as (Ha64 & Hwa).
                         apply HFR6. rewrite unsigned_lit_small by exact Ha64. exact Hwa. }
                       eapply (grow_ret B ARx SK LAWS PL_prog_B (@STK_grow prh_img_B) W2 E1 _ ms3 _ e FP regs
                         (growB_extra ty kids keys n cap) ly S Hp W mem md (grow_OR v) FP ly2 S2 Hp2 _ _
                         ltac:(apply Z.leb_le; vm_compute; reflexivity) HS);
                         [vm_compute; reflexivity | vm_compute; reflexivity | exact HA1 | vm_compute; reflexivity |
                          vm_compute; reflexivity | exact Hra | exact HJ2 | exact HK6 | | ].
                       *** rewrite HFP. intros a (r & Hr & Hb). exists r. split; [apply in_or_app; left; exact Hr | exact Hb].
                       *** intros mat'. cbv beta. unfold fQmn. cbv beta.
                           (* the m-form keep: P at the ret *)
                           split; [|exact (PEND _ HPM)].
                           split; [exact HRL2|].
                           (* the hull use: the kids call's alone, both NULL arms (PwGrowG's grow_hull_one) *)
                           split; [rewrite Heq; exact (grow_hull_one S S2 (ty =? 6) cap HHU1)|].
                           (* the two NULL arms share: ablocks unchanged, so blocks_bytes is unchanged, and the
                              slot blocks' bytes are kept from entry to the ret (grow writes none of them) *)
                           assert (HBB : forall (Hab : ablocks B ly2 S2 = ablocks B ly S),
                             blocks_bytes S2 <= blocks_bytes S +
                               PRH_Charge.prh_held (PRH_Charge.prhPg_gtrace (ty =? 6) n cap)).
                           { intros Hab.
                             rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly S), Hab.
                             assert (HGE0 : 0 <= PRH_Charge.prh_held (PRH_Charge.prhPg_gtrace (ty =? 6) n cap)).
                             { unfold PRH_Charge.prh_held, PRH_Charge.prhPg_gtrace, PjGrammar.grow.
                               replace (Nat.ltb (Z.to_nat n) (Z.to_nat cap)) with false
                                 by (symmetry; apply Nat.ltb_ge; lia).
                               replace (Nat.eqb (Z.to_nat cap) 0) with false by (symmetry; apply Nat.eqb_neq; lia).
                               destruct (ty =? 6); cbn; lia. }
                             lia. }
                           assert (HKEYSK : ablocks B ly2 S2 = ablocks B ly S -> ty = 6 ->
                             bytes_at W2 (ms_mem ms3) keys yb).
                           { intros Hab H6.
                             destruct (HOLD Heq) as (_ & _ & Hyb). destruct (Hyb H6) as (Hyb0 & Hybl).
                             destruct (Hpos ltac:(lia)) as (_ & Hky). pose proof (Hky H6) as HLky.
                             unfold prh_lin in HLky.
                             pose proof HLED as (_ & _ & HFl2 & _).
                             pose proof (proj1 (Forall_forall _ _) HFl2 (keys, 8 * cap) HLky) as (Hk8 & Hby & _).
                             cbn [fst snd] in Hk8, Hby.
                             assert (HinY : In (keys - cf_head, keys - cf_head + req_size (8 * cap + cf_head))
                               (ablocks_fp (prhReader_ab (kids_blkR kids cap ++ keys_blkR ty keys cap)))).
                             { unfold ablocks_fp, prhReader_ab, kids_blkR, keys_blkR.
                               rewrite (proj2 (Z.eqb_neq cap 0) Hcz), (proj2 (Z.eqb_eq ty 6) H6).
                               cbn [app map fst snd orb negb]. right. left. reflexivity. }
                             assert (Hrq8 : 8 * cap + cf_head <= req_size (8 * cap + cf_head))
                               by (unfold req_size; destruct (Z.eqb_spec (8 * cap + cf_head) 0); lia).
                             assert (HKEEPY : forall x, keys <= x < keys + 8 * cap ->
                               aview SEGS (w_H W2) (ms_mem ms3) x = aview SEGS (w_H W) mem x).
                             { intros x Hx.
                               destruct (grow_slot_apart B ARx LAWS GROW_FR_B ly S Hp W mem md Lam peak cnt fail ran most own
                                 regs e v ty kids keys n cap _ _ x ltac:(unfold GROW_FR_B; lia) ltac:(lia) HAR HLED HAT
                                 Hsp128 HSLOT HAP HinY ltac:(lia)) as (Hx64 & Hxw).
                               assert (Hcall : aview SEGS (w_H W) (ms_mem ms1) x = aview SEGS (w_H W) mem x)
                                 by (apply aview_eq_of; apply HFR3; rewrite unsigned_lit_small by exact Hx64; exact Hxw).
                               assert (Hpost : aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W) (ms_mem ms1) x).
                               { replace x with (keys - cf_head + (x - (keys - cf_head))) by lia.
                                 apply (G2c (keys - cf_head) (8 * cap + cf_head) (x - (keys - cf_head)) Hby
                                   ltac:(rewrite Hab; exact Hby) ltac:(lia)).
                                 intros ((lo2 & hi2) & Hr2 & Hlo2' & Hhi2'). cbn [fst snd] in Hlo2', Hhi2'.
                                 rewrite (proj2 (Z.eqb_neq kids 0) ltac:(lia)) in Hr2.
                                 cbn [ablocks_fp map In] in Hr2. destruct Hr2 as [Hr2 | []].
                                 injection Hr2 as <- <-.
                                 assert (Hneq : (kids - cf_head, 56 * cap + cf_head) <> (keys - cf_head, 8 * cap + cf_head)).
                                 { intros Heq2. injection Heq2 as _ Hk2. lia. }
                                 pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ _ HAR
                                   Hbkids Hby Hneq) as Hdj.
                                 unfold zdisjoint in Hdj; cbn [fst snd] in Hdj.
                                 assert (Hrq56 : 56 * cap + cf_head <= req_size (56 * cap + cf_head))
                                   by (unfold req_size; destruct (Z.eqb_spec (56 * cap + cf_head) 0); lia).
                                 clear - Hx Hlo2' Hhi2' Hdj Hrq56 Hrq8 Hh0; lia. }
                               assert (Hret : aview SEGS (w_H W2) (ms_mem ms3) x = aview SEGS (w_H W2) mem2 x)
                                 by (apply aview_eq_of; apply HFR6; rewrite unsigned_lit_small by exact Hx64; exact Hxw).
                               rewrite Hret, Hpost, Hcall. reflexivity. }
                             unfold bytes_at in *.
                             apply (garr8R_frame SEGS _ _ _ _ Hyb0).
                             intros x Hx. rewrite Hybl in Hx.
                             apply (mbyte_of_aview SEGS). apply HKEEPY. lia. }
                           (* a0 at the ret is s2 = -1 (i = 48 `li s2, -1`, i = 76 `mv a0, s2`) *)
                           assert (HA0m1 : getr (ms_regs ms3) 10%bv = w64 (-1)).
                           { pose proof (st_ok_pi_restrict_reg (w_H W2) E1 _ ms3 10%bv HS) as R10f.
                             match type of R10f with _ = sv_denot _ ?t =>
                               let t' := eval vm_compute in t in change t with t' in R10f end.
                             rewrite R10f. apply bv_eq. vm_compute. reflexivity. }
                           (* the old kids block's bytes across runs 5 and 6 (a slot block, apart from grow's writes) *)
                           assert (HKB3 : bytes_at W2 mem2 kids kb -> bytes_at W2 (ms_mem ms3) kids kb).
                           { intros Hk2'. unfold bytes_at in *. apply (garr8R_frame SEGS _ _ _ _ Hk2').
                             intros x Hx. rewrite Hkbl in Hx.
                             assert (Hrq' : 56 * cap + cf_head <= req_size (56 * cap + cf_head))
                               by (unfold req_size; destruct (Z.eqb_spec (56 * cap + cf_head) 0); lia).
                             destruct (grow_slot_apart B ARx LAWS GROW_FR_B ly S Hp W mem md Lam peak cnt fail ran most own regs e v
                               ty kids keys n cap _ _ x ltac:(unfold GROW_FR_B; lia) ltac:(lia) HAR HLED HAT Hsp128 HSLOT HAP
                               HinK ltac:(lia)) as (Hx64 & Hxw).
                             unfold mbyte. rewrite HFR6; [reflexivity|]. rewrite unsigned_lit_small by exact Hx64. exact Hxw. }
                           (* errno across runs 5 and 6: an image cell (HENV), off grow's frame and off v *)
                           assert (HERR3 : rd32 (aview SEGS (w_H W2) mem2) (as_errno B) 12 ->
                             rd32 (aview SEGS (w_H W2) (ms_mem ms3)) (as_errno B) 12).
                           { intros Hr2 k Hk. rewrite <- (Hr2 k Hk).
                             pose proof HENV as ((He0' & He4') & HEimg & _).
                             assert (Himg : in_img SEGS (as_errno B + Z.of_nat k)) by (apply HEimg; lia).
                             pose proof (pa_segs_low _ Himg) as Hl. unfold kLowMemEnd in Hl.
                             apply aview_eq_of. apply HFR6. rewrite unsigned_lit_small by lia.
                             unfold grow_wr, GROW_FR_B.
                             intros [Hw | [Hw | Hw]];
                               [lia | exact (Hoff (as_errno B + Z.of_nat k) ltac:(lia) Himg)
                               | exact (Hoff (as_errno B + Z.of_nat k) ltac:(lia) Himg)]. }
                           destruct HARMS as [(Hk0 & Hcf & Hres0 & HHp2 & Hab & Hkb2 & HL2)
                                             | [(Hk0 & Hcf & Hres0 & HPerm & Hab & Hkb2 & Hnullp & Herr & HL2) | HSUC]].
                           ---- (* the kids realloc is the CHOSEN FAILURE *)
                               split; [exact (HBB Hab)|]. right. left.
                               split; [exact Heq|]. split; [exact Hcf|].
                               split; [exact HA0m1|].
                               split; [exact HHp2|]. split; [exact Hab|].
                               split; [rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly S), Hab; reflexivity|].
                               split; [rewrite <- Hmod; exact (HLEDKEEP _ _ _ _ _ HL2 ltac:(intros a Hca; exact Hca))|].
                               split; [exact HHDR|].
                               split; [exact (HKB3 Hkb2)|].
                               split; [exact (HKEYSK Hab)|].
                               (* no event (outcomes [false]: prhPg_evs is []): live requests and position kept *)
                               replace (prhPg_evs (ty =? 6) n cap [false]) with (@nil PresetReqAt.hev)
                                 by (unfold prhPg_evs; rewrite Heq, Z.ltb_irrefl; reflexivity).
                               split; [exact (grow_live_keep B ly S ly2 S2 Hab) | exact (HPOS0 Hres0)].
                           ---- (* the kids realloc is REFUSED *)
                               split; [exact (HBB Hab)|]. right. right. left.
                               split; [exact Heq|]. split; [exact Hcf|].
                               split; [exact HA0m1|].
                               split; [exact HPerm|]. split; [exact Hab|].
                               split; [rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly S), Hab; reflexivity|].
                               split; [exact Hnullp|].
                               split; [exact (HERR3 Herr)|].
                               (* THE OUTCOME EXCLUSION (the text :919-926): a model run at the entry whose next events are the
                                  all-granted ones, the first a consumer event, makes fuzz_realloc's outcome clause give a
                                  grant at the kids call (cnt <> fail), but it returned NULL *)
                               split.
                               { intros sm x os i H0 hist Hpsm Hrun Hcons. rewrite Heq in Hrun, Hcons.
                                 pose proof (grow_run_split _ _ _ _ _ _ Hrun Hcons) as Hxs.
                                 destruct Hxs as (Hxr1 & Hxc1 & _).
                                 unfold prhPg_ev in Hxr1. rewrite (proj2 (Z.eqb_neq cap 0) Hcz) in Hxr1.
                                 destruct (HOUTR Hk0 sm x os i H0 hist Hpsm Hxr1 Hxc1 Hcf) as (Hxnz & _).
                                 exact (Hxnz Hres0). }
                               (* THE OUTCOME OF AN INJECTED READING (DEAD_PJPARSE; PwGrowG.grow_excl_of_leaf): the same
                                  leaf outcome at the model's grant list okk (fail - cnt) *)
                               split.
                               { apply (grow_excl_of_leaf (ty =? 6) n cap cnt fail S res Heq Hcf Hres0).
                                 intros sm x os i H0 hist Hpsm Hxr1 Hxc1 Hcf1.
                                 unfold prhPg_ev in Hxr1. rewrite (proj2 (Z.eqb_neq cap 0) Hcz) in Hxr1.
                                 destruct (HOUTR Hk0 sm x os i H0 hist Hpsm Hxr1 Hxc1 Hcf1) as (Hxnz & _). exact Hxnz. }
                               (* the ledger: fuzz_realloc's refused arm at k = 56 cap, n = 56 cap2R cap (the text :933-936) *)
                               split; [rewrite (proj2 (Z.eqb_neq cap 0) Hcz);
                                 exact (HLEDKEEP _ _ _ _ _ HL2 ltac:(intros a Hca; exact Hca))|].
                               split; [exact HHDR|].
                               split; [exact (HKB3 Hkb2)|].
                               split; [exact (HKEYSK Hab)|].
                               (* no event (outcomes [false]: prhPg_evs is []): live requests and position kept *)
                               replace (prhPg_evs (ty =? 6) n cap [false]) with (@nil PresetReqAt.hev)
                                 by (unfold prhPg_evs; rewrite Heq, Z.ltb_irrefl; reflexivity).
                               split; [exact (grow_live_keep B ly S ly2 S2 Hab) | exact (HPOS0 Hres0)].
                           ---- (* the SUCCESS arm is out: its result is a block address, and a0 = 0 here *)
                               exfalso.
                               destruct HSUC as (Hk0 & Hcf & Hres1 & Hres16 & l1 & l2 & HLam & Hnin & HHp & (b1 & b2 & Hb12 & Hfresh & HPb) & _).
                               assert (Hin2 : In (res - cf_head, 56 * cap2R cap + cf_head) (ablocks B ly2 S2))
                                 by (apply (Permutation_in _ (Permutation_sym HPb)); left; reflexivity).
                               destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR2 Hin2) as (_ & _ & Hceil' & _).
                               assert (Hrqs : 56 * cap2R cap + cf_head <= req_size (56 * cap2R cap + cf_head))
                                 by (unfold req_size; destruct (Z.eqb_spec (56 * cap2R cap + cf_head) 0); lia).
                               match goal with H : branch_taken BC_EQ _ _ = true |- _ => rename H into Hbeq end.
                               rewrite branch_eq_U in Hbeq. apply Z.eqb_eq in Hbeq. rewrite U_lit in Hbeq by lia.
                               unfold U in Hbeq. rewrite <- R10r, H10r in Hbeq. unfold w64 in Hbeq.
                               rewrite unsigned_lit_small in Hbeq by lia. lia.
               --- (* a0 <> 0: the kids moved (the callee's SUCCESS arm; the two NULL arms have res = 0) *)
                   match goal with H : branch_taken BC_EQ _ _ = false |- _ => rename H into Hbne end.
                   assert (Hres_ne : bv_unsigned (getr regs2 10%bv) <> 0).
                   { rewrite branch_eq_U in Hbne. apply Z.eqb_neq in Hbne. rewrite U_lit in Hbne by lia.
                     unfold U in Hbne. rewrite <- R10r in Hbne. exact Hbne. }
                   rewrite H10r in Hres_ne. unfold w64 in Hres_ne.
                   destruct HARMS as [(Hk0 & Hcf & Hres0 & _) | [(Hk0 & Hcf & Hres0 & _) | HSUC]];
                     [exfalso; apply Hres_ne; rewrite Hres0; reflexivity | exfalso; apply Hres_ne; rewrite Hres0; reflexivity |].
                   destruct HSUC as (Hk0 & Hcf & Hres1 & Hres16 & l1 & l2 & HLam & Hnin & HHp & (b1 & b2 & Hb12 & Hfresh & HPb)
                     & (rest & Hrestl & Hbres) & HRAres & Hhull & HL2).
                   (* the node's place at the post state (image A's grow_at_kept) *)
                   assert (HAT2 : prhReader_at B ly2 S2 ((res, 56 * cap2R cap) :: l1 ++ l2) regs e v 56).
                   { pose proof HJ1 as (_ & Hly1 & _ & _ & _ & Hfrs1 & _).
                     destruct Hly1 as (_ & _ & _ & _ & _ & HlyF & _).
                     apply (grow_at_kept B ARx ly S Hp W (ms_mem ms1) _ ly2 S2 Hp2 W2 mem2 md2 Lam l1 l2 regs e v
                       kids (56 * cap) (56 * cap2R cap) res b1 b2 HARc5 HAR2).
                     - intros a kk Hin. pose proof HLEDc as (_ & _ & HFk & _).
                       exact (proj1 (proj2 (proj1 (Forall_forall _ _) HFk (a, kk) Hin))).
                     - exact HAT.
                     - intros x Hx. apply (HAP (kids, 56 * cap) x); [| exact Hx].
                       apply in_or_app; left; unfold kids_blkR; rewrite (proj2 (Z.eqb_neq cap 0) Hcz); left; reflexivity.
                     - exact HLam.
                     - exact Hb12.
                     - exact HPb.
                     - rewrite Hfrs1. reflexivity.
                     - intros cid pos. unfold frame_addr. rewrite HlyF. reflexivity.
                     - exact Hfresh. }
                   (* v's shadow at the call memory: the entry's (HRA), grow writes no shadow byte *)
                   assert (HRAc : range_addressable (aview SEGS (w_H W) (ms_mem ms1)) SHADOW_OFF v 56).
                   { intros x Hx. destruct (HRA x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
                     rewrite <- Hs. unfold shadow_of_addr.
                     assert (Hx8 : 0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
                     apply aview_eq_of. apply HFR3. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
                     unfold grow_wr, GROW_FR_B. pose proof Hvstk as Hvs96. unfold GROW_FR_B in Hvs96.
                     intros [Hw | [Hw | Hw]];
                       [unfold SHADOW_OFF in *; lia
                       | exact (Happ (SHADOW_OFF + x / 8) ltac:(lia) ltac:(lia))
                       | exact (Happ (SHADOW_OFF + x / 8) ltac:(lia) ltac:(lia))]. }
                   (* the caller's window lies below the stack top: fwin's spZ + e <= ly_top and astk_ok's ly_top <= ly_stk_hi *)
                   assert (HSTKHI : spZ regs + e <= ly_stk_hi ly) by lia.
                   assert (HRA2 : range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF v 56).
                   { apply (grow_v_shadow2 B ARx SK LAWS ly S Hp W (ms_mem ms1) _ ly2 S2 Hp2 W2 mem2 md2 _ _ _ _ _ _ _ regs e v
                       _ _ _ k1 HARc5 HAR2 HL2 HAT2 ltac:(rewrite Hslo2; lia) ltac:(rewrite Hshi2; lia) HRAc HJ1).
                     intros a (r & Hr & Hlo & Hhi). rewrite (proj2 (Z.eqb_neq kids 0) ltac:(lia)) in Hr.
                     cbn [ablocks_fp map In] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Hlo, Hhi.
                     destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HARc5 Hbkids) as (_ & _ & _ & Happk & _).
                     exact (in_app_addr _ _ a Happk ltac:(lia)). }
                   (* the node's facts at the memory after run 5 (HV5all: run 5 writes only the frame) *)
                   assert (HRA5 : range_addressable (aview SEGS (w_H W2) (ms_mem ms2)) SHADOW_OFF v 56).
                   { intros x Hx. destruct (HRA2 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
                     rewrite <- Hs. unfold shadow_of_addr.
                     assert (Hx8 : 0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
                     apply HV5all; unfold GROW_FR_B, SHADOW_OFF in *; lia. }
                   assert (HVV5 : forall a k w, v <= a -> a + Z.of_nat k <= v + 56 ->
                     val_mem SEGS (mrestrict (w_H W) mem) a k w -> val_mem SEGS (mrestrict (w_H W2) (ms_mem ms2)) a k w).
                   { intros a k w H1 H2 Hv j Hj. specialize (Hv j Hj).
                     rewrite (mbyte_of_aview SEGS (w_H W) (w_H W2) mem (ms_mem ms2) (a + Z.of_nat j)); [exact Hv|].
                     rewrite (HV5 (a + Z.of_nat j) ltac:(lia)), (proj1 (HVK (a + Z.of_nat j) ltac:(lia))).
                     exact (HVM1 (a + Z.of_nat j) ltac:(lia)). }
                   assert (HPR5 : forall a, v <= a < v + 56 -> apresent (w_H W2) (ms_mem ms2) a).
                   { intros a Ha. destruct (proj2 (HVK a Ha)) as (Hh & b & Hb). split; [exact Hh|].
                     destruct (ms_mem ms2 (Z_to_bv 64 a)) as [b'|] eqn:Eb; [exists b'; reflexivity|].
                     exfalso. apply (HG (Z_to_bv 64 a)); unfold mrestrict; rewrite Hh; [rewrite Hb; discriminate | exact Eb]. }
                   assert (U32' : bv_unsigned (ew E1 32) = SHADOW_OFF) by (rewrite AGo by lia; exact U32).
                   assert (U33' : bv_unsigned (ew E1 33) = ty) by (rewrite AGo by lia; exact U33).
                   assert (SHOK2 : sh_ok SEGS growB_Bx growB_SH E1 (mrestrict (w_H W2) (ms_mem ms2))).
                   { unfold sh_ok, growB_SH. apply Forall_cons; [|apply Forall_nil]. split.
                     - unfold growB_Bx. cbn [she_m she_lo she_hi].
                       rewrite !U_SOff, U32', U10', !Z.add_0_r, !zcanon_id by (unfold M64, SHADOW_OFF; lia).
                       change (rd_of SEGS (mrestrict (w_H W2) (ms_mem ms2))) with (aview SEGS (w_H W2) (ms_mem ms2)).
                       exact HRA5.
                     - unfold app_apart, growB_Bx. cbn [she_m she_lo she_hi]. intros a Ha.
                       rewrite !U_SOff, U32', U10', !Z.add_0_r, !zcanon_id in * by (unfold M64, SHADOW_OFF; lia).
                       apply Happ. lia. }
                   pose proof HH as (_ & (Hty' & Vty') & _ & _ & (Hkids' & Vkids') & (Hkeys' & Vkeys') & (Hn' & Vn') & (Hcap' & Vcap')).
                   assert (UO0' : bv_unsigned (ew E1 (A_OBJ 0)) = VAL (A_OBJ 0)) by (apply HEI1'; unfold A_OBJ, A_TEXT, A_LIM; lia).
                   assert (UO12' : bv_unsigned (ew E1 (A_OBJ 12)) = VAL (A_OBJ 12)) by (apply HEI1'; unfold A_OBJ, A_TEXT, A_LIM; lia).
                   assert (UO0x : bv_unsigned (ew E1 241) = VAL (A_OBJ 0)) by exact UO0'.
                   assert (UO12x : bv_unsigned (ew E1 253) = VAL (A_OBJ 12)) by exact UO12'.
                   (* the node's two regions back, at the memory after run 5 *)
                   assert (RBok : region_ok SEGS E1 (mrestrict (w_H W2) (ms_mem ms2)) growB_vB).
                   { unfold growB_vB, region_ok.
                     cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U10'.
                     split; [lia|]. split; [lia|].
                     split; [intros o Ho; apply (apresent_writable SEGS); apply HPR5; lia|].
                     repeat apply Forall_cons; try apply Forall_nil.
                     - apply (chunk_ok_val SEGS E1 _ v 40 8 (SOff 36 0) n);
                         [cbn [sv_denot]; rewrite U36', Z.add_0_r; reflexivity | exact Hn' | lia | apply HVV5; [lia | cbn; lia | exact Vn']].
                     - apply (chunk_ok_val SEGS E1 _ v 48 8 (SOff 37 0) cap);
                         [cbn [sv_denot]; rewrite U37', Z.add_0_r; reflexivity | exact Hcap' | lia | apply HVV5; [lia | cbn; lia | exact Vcap']]. }
                   assert (RAok : region_ok SEGS E1 (mrestrict (w_H W2) (ms_mem ms2)) growB_vA).
                   { unfold growB_vA, region_ok.
                     cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U10'.
                     split; [lia|]. split; [lia|].
                     split; [intros o Ho; apply (apresent_writable SEGS); apply HPR5; lia|].
                     repeat apply Forall_cons; try apply Forall_nil.
                     - apply (chunk_ok_val SEGS E1 _ v 0 4 (SOff 33 0) ty);
                         [cbn [sv_denot]; rewrite U33', Z.add_0_r; reflexivity | exact Hty' | lia |].
                       rewrite Z.add_0_r. apply HVV5; [lia | cbn; lia | exact Vty'].
                     - apply (chunk_ok_val SEGS E1 _ v 24 8 (SOff 34 0) kids);
                         [cbn [sv_denot]; rewrite U34', Z.add_0_r; reflexivity | exact Hkids' | lia | apply HVV5; [lia | cbn; lia | exact Vkids']].
                     - apply (chunk_ok_val SEGS E1 _ v 32 8 (SOff 35 0) keys);
                         [cbn [sv_denot]; rewrite U35', Z.add_0_r; reflexivity | exact Hkeys' | lia | apply HVV5; [lia | cbn; lia | exact Vkeys']]. }
                   lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
                     pose proof (st_ok_pi_add_region E1 ssx _ growB_vB HS ltac:(vm_compute; reflexivity) RBok) as HS3 end.
                   match type of HS3 with ?P -> _ => assert (HD : P); [|specialize (HS3 HD); clear HD] end.
                   { apply all_disjoint_of_extents.
                    (* the region list by a VM-checked equation: `vm_compute ss_mem` recorded no cast, and the kernel's
                       lazy re-check of it made Qed run past 50 min (measured by bisection, 2026-10-29) *)
                    lazymatch goal with |- zall_disjoint _ (map _ ?rs) =>
                      let rs' := eval vm_compute in rs in replace rs with rs' by (vm_compute; reflexivity) end. unfold growB_vB.
                     cbn [map zall_disjoint]. unfold extent_of_region, zdisj.
                     cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val].
                     rewrite ?U2', ?U10', ?UO0', ?UO12', ?UO0x, ?UO12x. pose proof Hvstk as Hvs96. unfold GROW_FR_B in Hvs96.
                     repeat split; lia. }
                   clear HS. rename HS3 into HS.
                   lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
                     pose proof (st_ok_pi_add_region E1 ssx _ growB_vA HS ltac:(vm_compute; reflexivity) RAok) as HS3 end.
                   match type of HS3 with ?P -> _ => assert (HD : P); [|specialize (HS3 HD); clear HD] end.
                   { apply all_disjoint_of_extents.
                    (* the region list by a VM-checked equation: `vm_compute ss_mem` recorded no cast, and the kernel's
                       lazy re-check of it made Qed run past 50 min (measured by bisection, 2026-10-29) *)
                    lazymatch goal with |- zall_disjoint _ (map _ ?rs) =>
                      let rs' := eval vm_compute in rs in replace rs with rs' by (vm_compute; reflexivity) end. unfold growB_vA, growB_vB.
                     cbn [map zall_disjoint]. unfold extent_of_region, zdisj.
                     cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val].
                     rewrite ?U2', ?U10', ?UO0', ?UO12', ?UO0x, ?UO12x. pose proof Hvstk as Hvs96. unfold GROW_FR_B in Hvs96.
                     repeat split; lia. }
                   clear HS. rename HS3 into HS.
                   (* run 7: the v + 24 shadow check, the kids store, v's partial-granule check, `bne ty, 6` *)
                   pose proof HJ2 as (HARc7 & _).
                   paj_run_tok_x_inv (RUNBP PM PLAW) HS HJ2 SHOK2 HPM growB_Bspan.
                   +++ apply (grow_awr_ok_fr _ _ (@STK_grow prh_img_B) GROW_FR_B e (spZ regs) FP _ _ S ly2 v);
                         [unfold GROW_FR_B; lia | exact FS | exact He0 | | | ].
                       *** unfold GROW_FR_B; grow_wr_tac U2' U10'.
                       *** intros a Ha. rewrite HFP. exact (grow_FP_v v ty kids keys cap a Ha).
                       *** exact HVL2'.
                   +++ (* run 7 stops at i = 59 (`bne ty, 6`), over E1 (measured); the v + 24 and v shadow checks
                          (report sites 0x871ec, 0x871d0) are decided inside it by sh_ok growB_SH *)
                       match type of HS with st_ok_pi _ _ E1 _ _ => idtac | _ => fail "run 7 changed the environment" end.
                       destruct (grow_stretch B ARx SK LAWS (@STK_grow prh_img_B) GROW_FR_B E1 _ W2 mem2 (ms_mem ms2)
                         _ (ms_mem ms3) _ (spZ regs) v FP ly S Hp W mem md ly2 S2 Hp2 ltac:(unfold GROW_FR_B; lia) FS
                         HK5 HFR5 HGR5 HAR HARc7 ltac:(rewrite Hslo2; exact Hceil) ltac:(rewrite Hslo2; exact Hslo)
                         ltac:(rewrite Hshi2; exact Hshi) HFr0 HG0 ltac:(unfold GROW_FR_B; grow_wr_tac U2' U10')
                         (same_but_materialized_wvb_any _ mat3)) as (HK7 & HFR7 & HGR7).
                       (* the facts both ty arms share: the call's frame and layout, the node apart from the old kids
                          block, the new block apart from grow's writes (PwGrowG's grow_new_apart), and its range *)
                       pose proof HJ1 as (_ & Hly1 & _ & _ & _ & Hfrs1 & _).
                       destruct Hly1 as (_ & _ & _ & _ & _ & HlyF & _).
                       assert (HFRS2 : frames S2 = frames S) by (rewrite Hfrs1; reflexivity).
                       assert (HFA2 : forall cid pos, frame_addr ly2 cid pos = frame_addr ly cid pos)
                         by (intros cid pos; unfold frame_addr; rewrite HlyF; reflexivity).
                       assert (HAPk : forall y, pj_holdsR (kids, 56 * cap) y -> ~ (v <= y < v + 56)).
                       { intros y Hy. apply (HAP (kids, 56 * cap) y); [| exact Hy].
                         apply in_or_app; left; unfold kids_blkR; rewrite (proj2 (Z.eqb_neq cap 0) Hcz); left; reflexivity. }
                       assert (HNEW : forall x, res - cf_head <= x < res - cf_head + req_size (56 * cap2R cap + cf_head) ->
                         0 <= x < 2 ^ 64 /\ ~ grow_wr GROW_FR_B (spZ regs) v x)
                         by (intros x Hx; exact (grow_new_apart B ARx LAWS GROW_FR_B ly S Hp W (ms_mem ms1) _ ly2 S2 Hp2 W2
                               mem2 md2 Lam peak cnt fail ran most own l1 l2 regs e v kids (56 * cap) (56 * cap2R cap) res b1 b2 x
                               ltac:(unfold GROW_FR_B; lia) HARc5 HAR2 HLEDc HAT Hsp128 HAPk HLam Hb12 HPb HFRS2 HFA2
                               Hfresh Hx)).
                       assert (Hnew2 : In (res - cf_head, 56 * cap2R cap + cf_head) (ablocks B ly2 S2))
                         by (apply (Permutation_in _ (Permutation_sym HPb)); left; reflexivity).
                       destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR2 Hnew2) as (_ & Hn4096 & Hnc & _).
                       assert (Hrqn : 56 * cap2R cap + cf_head <= req_size (56 * cap2R cap + cf_head))
                         by (unfold req_size; destruct (Z.eqb_spec (56 * cap2R cap + cf_head) 0); lia).
                       assert (Hmod : (cnt + 1) mod 2 ^ 64 = cnt + 1).
                       { pose proof HLED as Hcnt64. eapply prh_ledger_bounds in Hcnt64. destruct Hcnt64 as (_ & _ & Hcnt64 & _). apply Z.mod_small. lia. }
                       assert (HLS : forall (la lb : list (Z * Z)) a k,
                         Ledger.lsum (la ++ (a, k) :: lb) = k + Ledger.lsum (la ++ lb)).
                       { intros la lb a k. induction la as [|[x y] la IH]; cbn [app Ledger.lsum]; [reflexivity | rewrite IH; lia]. }
                       (* the kids block's new address: a0 at the return site was the fresh atom 42 *)
                       assert (U42 : bv_unsigned (ew E1 42) = res).
                       { assert (HU : U E1 (SOff 42 0) = res)
                           by (unfold U; rewrite <- R10r, H10r; unfold w64; apply unsigned_lit_small; lia).
                         rewrite U_SOff, Z.add_0_r, zcanon_id in HU; [exact HU|].
                         pose proof (bv_unsigned_in_range _ (ew E1 42)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
                         unfold M64. lia. }
                       (* the node's header at the post state: the entry's, its 56 bytes kept by the call (HVK) *)
                       assert (HAGm2 : pj_agreeR SEGS (mrestrict (w_H W) mem) (mrestrict (w_H W2) mem2)
                         (fun x => v <= x < v + 56)).
                       { intros x Hx. split.
                         - apply (mbyte_of_aview SEGS). rewrite (proj1 (HVK x Hx)). exact (HVM1 x Hx).
                         - intros _. apply (apresent_writable SEGS). exact (proj2 (HVK x Hx)). }
                       assert (HHDR2 : pj_hdrR SEGS (mrestrict (w_H W2) mem2) v ty num str kids keys n cap)
                         by exact (pj_hdrR_frame _ _ _ _ _ _ _ _ _ _ _ HH HAGm2).
                       (* the ty branch at i = 59, `bne a0, a1` with a0 = the sign-extended type, a1 = 6 *)
                       (* the kids call's SUCCESS arm, as both ty arms read it: the blocks' bytes grew by 56 cap, the
                          ledger of the post state over Lam2 = (res, 56 cap2R cap) :: l1 ++ l2, the old kids bytes at
                          the head of the new block *)
                       assert (HBB2 : blocks_bytes S2 = blocks_bytes S + 56 * cap).
                       { rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly S), (bsum_perm _ _ HPb), Hb12.
                         rewrite bsum_cons, !bsum_app, bsum_cons. cbn [fst snd]. rewrite Hc2. lia. }
                       assert (HL2' : prh_ledger B ly2 S2 Hp2 W2 mem2 ((res, 56 * cap2R cap) :: l1 ++ l2)
                         (Z.max peak (Ledger.lsum ((res, 56 * cap2R cap) :: l1 ++ l2))) (cnt + 1) fail ran most own).
                       { cbn [Ledger.lsum]. rewrite (Z.add_comm (56 * cap2R cap)), <- Hmod. exact HL2. }
                       assert (HKB2 : bytes_at W2 mem2 res kb).
                       { assert (Hmin : Z.min (56 * cap) (56 * cap2R cap) = 56 * cap) by (rewrite Hc2; lia).
                         rewrite Hmin, <- Hkbl, Nat2Z.id, firstn_all in Hbres.
                         unfold bytes_at in *. apply garr8_app in Hbres as (Hb0 & _). exact Hb0. }
                       psrr_branch_tok RUNB BRB HS SHOK2 growB_Bspan.
                       *** (* ty <> 6 (arm 4, an array): run 8 from i = 72 - the v + 48 shadow check (report site
                              0x871f4, decided inside the run by sh_ok growB_SH), `li s2, 0`, `sd s6, 0(s0)` (v + 48 :=
                              2 cap), the epilogue - to the ret (i = 89) with a0 = 0 *)
                           assert (Hty6 : ty <> 6).
                           { intros H6. rewrite branch_ne_U in Hc1. rewrite U_SExt, U_SOff, U33', H6, U_lit in Hc1 by lia.
                             vm_compute in Hc1. discriminate. }
                           pose proof HJ2 as (HARc8 & _).
                           paj_run_tok_x_inv (RUNBP PM PLAW) HS HJ2 SHOK2 HPM growB_Bspan.
                           { apply (grow_awr_ok_fr _ _ (@STK_grow prh_img_B) GROW_FR_B e (spZ regs) FP _ _ S ly2 v);
                               [unfold GROW_FR_B; lia | exact FS | exact He0 | | | ].
                             - unfold GROW_FR_B; grow_wr_tac U2' U10'.
                             - intros a Ha. rewrite HFP. exact (grow_FP_v v ty kids keys cap a Ha).
                             - exact HVL2'. }
                           match type of HS with st_ok_pi _ _ E1 _ _ => idtac | _ => fail "run 8 changed the environment" end.
                           destruct (grow_stretch B ARx SK LAWS (@STK_grow prh_img_B) GROW_FR_B E1 _ W2 mem2 (ms_mem ms3)
                             _ (ms_mem ms4) _ (spZ regs) v FP ly S Hp W mem md ly2 S2 Hp2 ltac:(unfold GROW_FR_B; lia) FS
                             HK7 HFR7 HGR7 HAR HARc8 ltac:(rewrite Hslo2; exact Hceil) ltac:(rewrite Hslo2; exact Hslo)
                             ltac:(rewrite Hshi2; exact Hshi) HFr1 HG1 ltac:(unfold GROW_FR_B; grow_wr_tac U2' U10')
                             (same_but_materialized_wvb_any _ mat4)) as (HK8 & HFR8 & HGR8).
                           (* the grammar's charge of an array's grow: one realloc, 56 cap more user bytes *)
                           assert (HHELD : PjGrammar.held (PRH_Charge.prhPg_gtrace (ty =? 6) n cap) = 56 * cap /\
                                           PjGrammar.calls (PRH_Charge.prhPg_gtrace (ty =? 6) n cap) = 1%nat).
                           { rewrite (proj2 (Z.eqb_neq ty 6) Hty6). unfold PRH_Charge.prhPg_gtrace, PjGrammar.grow.
                             replace (Nat.ltb (Z.to_nat n) (Z.to_nat cap)) with false by (symmetry; apply Nat.ltb_ge; lia).
                             replace (Nat.eqb (Z.to_nat cap) 0) with false by (symmetry; apply Nat.eqb_neq; lia).
                             cbn -[Nat.mul]. split; [lia | reflexivity]. }
                           (* a0 at the ret is s2 = 0 (i = 74 `li s2, 0`, i = 76 `mv a0, s2`) *)
                           assert (HA00 : getr (ms_regs ms4) 10%bv = w64 0).
                           { pose proof (st_ok_pi_restrict_reg (w_H W2) E1 _ ms4 10%bv HS) as R10f.
                             match type of R10f with _ = sv_denot _ ?t =>
                               let t' := eval vm_compute in t in change t with t' in R10f end.
                             rewrite R10f. reflexivity. }
                           (* the ledger at the ret: the callee's (Lam' = the new block in front of l1 ++ l2), its cells
                              apart from grow's writes at the POST state (grow_cell_apart with HAT2) *)
                           assert (HLEDr : prh_ledger B ly2 S2 Hp2 W2 (ms_mem ms4) ((res, 56 * cap2R cap) :: l1 ++ l2)
                             (Z.max peak (Ledger.lsum ((res, 56 * cap2R cap) :: l1 ++ l2))) (cnt + 1) fail ran most own).
                           { apply (prh_ledger_keep B ly2 S2 Hp2 W2 mem2 (ms_mem ms4) _ _ _ _ _ _ _ HL2').
                             intros a Hca.
                             destruct (grow_cell_apart B ARx LAWS HPST GROW_FR_B ly2 S2 Hp2 W2 mem2 md2 _ _ _ _ _ _ _ regs e v a
                               ltac:(unfold GROW_FR_B; lia) HAR2 HL2' HAT2 Hsp128 Hoff Hca) as (Ha64 & Hwa).
                             apply HFR8. rewrite unsigned_lit_small by exact Ha64. exact Hwa. }
                           (* the old kids bytes at the new block (the callee's firstn (min k n) old = kb), kept across
                              runs 7 / 8: the new block is apart from grow's writes *)
                           assert (HKBr : bytes_at W2 (ms_mem ms4) res kb).
                           { unfold bytes_at in *. apply (garr8R_frame SEGS _ _ _ _ HKB2). intros x Hx.
                             destruct (HNEW x ltac:(rewrite Hkbl in Hx; rewrite Hc2 in *; lia)) as (Hx64 & Hxw).
                             unfold mbyte. rewrite HFR8; [reflexivity|]. rewrite unsigned_lit_small by exact Hx64. exact Hxw. }
                           (* its shadow, kept across runs 7 / 8: grow writes no shadow byte *)
                           assert (HSHK : forall s, SHADOW_OFF <= s < SHADOW_OFF + 2 ^ 44 ->
                             aview SEGS (w_H W2) (ms_mem ms4) s = aview SEGS (w_H W2) mem2 s).
                           { intros s Hs. apply aview_eq_of. apply HFR8. rewrite unsigned_lit_small by (unfold SHADOW_OFF in *; lia).
                             unfold grow_wr, GROW_FR_B. pose proof Hvstk as Hvs96. unfold GROW_FR_B in Hvs96.
                             intros [Hw | [Hw | Hw]];
                               [unfold SHADOW_OFF in *; lia | exact (Happ s ltac:(lia) Hs) | exact (Happ s ltac:(lia) Hs)]. }
                           assert (HVISr : prhReader_vis W2 (ms_mem ms4) res (56 * cap2R cap)).
                           { split.
                             - intros x Hx. destruct (HRAres x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
                               rewrite <- Hs. unfold shadow_of_addr. apply HSHK.
                               assert (Hx8 : 0 <= x / 8 < 2 ^ 44)
                                 by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
                               lia.
                             - intros Hpos0 s Hs. rewrite HSHK; [exact (Hhull Hpos0 s Hs)|]. unfold shadow_addr in Hs.
                               assert (Hr8 : 512 <= res / 8) by (apply Z.div_le_lower_bound; lia).
                               assert (Hr8' : (res + 56 * cap2R cap - 1) / 8 < 2 ^ 44 - 16)
                                 by (apply Z.div_lt_upper_bound; lia).
                               pose proof (Z.div_mod (SHADOW_OFF + res / 8) 8 ltac:(lia)) as D1.
                               pose proof (Z.mod_pos_bound (SHADOW_OFF + res / 8) 8 ltac:(lia)) as M1.
                               pose proof (Z.div_mod (SHADOW_OFF + (res + 56 * cap2R cap - 1) / 8) 8 ltac:(lia)) as D2.
                               pose proof (Z.mod_pos_bound (SHADOW_OFF + (res + 56 * cap2R cap - 1) / 8) 8 ltac:(lia)) as M2.
                               lia. }
                           (* the node's fields at the ret, off its two symbolic regions: v + 24 = atom 42 (the kids
                              store, run 7), v + 32 = keys, v + 48 = cap << 1 (the cap store, run 8) *)
                           assert (RAf : region_ok SEGS E1 (mrestrict (w_H W2) (ms_mem ms4)) (YP09.mkRegion (Some 10%nat) 0 40 24 40
                             [YP09.mkChunk 24 (CVal 8 (SOff 42 0)); YP09.mkChunk 0 (CVal 4 (SOff 33 0));
                              YP09.mkChunk 32 (CVal 8 (SOff 35 0))])).
                           { match type of HS with st_ok_pi _ _ _ ?ss _ =>
                               exact (st_ok_region_nth SEGS E1 (abs_ss VAL ss) (restrict (w_H W2) ms4) 0
                                 (YP09.mkRegion (Some 10%nat) 0 40 24 40
                                   [YP09.mkChunk 24 (CVal 8 (SOff 42 0)); YP09.mkChunk 0 (CVal 4 (SOff 33 0));
                                    YP09.mkChunk 32 (CVal 8 (SOff 35 0))]) HS ltac:(vm_compute; reflexivity)) end. }
                           assert (RBf : region_ok SEGS E1 (mrestrict (w_H W2) (ms_mem ms4)) (YP09.mkRegion (Some 10%nat) 40 56 48 56
                             [YP09.mkChunk 48 (CVal 8 (SAlu ALU_SLL (SOff 37 0) (SLit 1))); YP09.mkChunk 40 (CVal 8 (SOff 36 0))])).
                           { match type of HS with st_ok_pi _ _ _ ?ss _ =>
                               exact (st_ok_region_nth SEGS E1 (abs_ss VAL ss) (restrict (w_H W2) ms4) 1
                                 (YP09.mkRegion (Some 10%nat) 40 56 48 56
                                   [YP09.mkChunk 48 (CVal 8 (SAlu ALU_SLL (SOff 37 0) (SLit 1)));
                                    YP09.mkChunk 40 (CVal 8 (SOff 36 0))]) HS ltac:(vm_compute; reflexivity)) end. }
                           assert (U2cap : sv_denot E1 (SAlu ALU_SLL (SOff 37 0) (SLit 1)) = Z_to_bv 64 (cap2R cap)).
                           { apply bv_eq. rewrite (unsigned_lit_small (cap2R cap)) by lia.
                             change (bv_unsigned (sv_denot E1 (SAlu ALU_SLL (SOff 37 0) (SLit 1))))
                               with (U E1 (SAlu ALU_SLL (SOff 37 0) (SLit 1))).
                             rewrite U_SAlu, U_SOff, U37', U_lit by lia. rewrite Z.add_0_r. cbn [zalu_raw].
                             rewrite (zcanon_id cap) by (unfold M64; lia). change (Z.land 1 63) with 1.
                             rewrite Z.shiftl_mul_pow2 by lia. rewrite zcanon_id by (unfold M64; lia). lia. }
                           assert (HHDRr : pj_hdrR SEGS (mrestrict (w_H W2) (ms_mem ms4)) v ty num str res keys n (cap2R cap)).
                           { apply (grow_hdr_keep GROW_FR_B (w_H W2) mem2 (ms_mem ms4) (spZ regs) v ty num str kids keys n cap
                               res keys (cap2R cap) HHDR2 HFR8 HGR8 Hvstk ltac:(lia) ltac:(lia)).
                             - split; [lia|].
                               exact (field_of_region SEGS E1 _ 10 v _ 0 40 24 40 24 8 (SOff 42 0) res RAf U10' ltac:(cbn; tauto)
                                 ltac:(cbn [sv_denot]; rewrite U42, Z.add_0_r; reflexivity)
                                 ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)).
                             - split; [exact Hkeys'|].
                               exact (field_of_region SEGS E1 _ 10 v _ 0 40 24 40 32 8 (SOff 35 0) keys RAf U10' ltac:(cbn; tauto)
                                 ltac:(cbn [sv_denot]; rewrite U35', Z.add_0_r; reflexivity)
                                 ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)).
                             - split; [lia|].
                               exact (field_of_region SEGS E1 _ 10 v _ 40 56 48 56 48 8 (SAlu ALU_SLL (SOff 37 0) (SLit 1))
                                 (cap2R cap) RBf U10' ltac:(cbn; tauto) U2cap
                                 ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)). }
                           eapply (grow_ret B ARx SK LAWS PL_prog_B (@STK_grow prh_img_B) W2 E1 _ ms4 _ e FP regs
                             (growB_extra ty kids keys n cap) ly S Hp W mem md (grow_OR v) FP ly2 S2 Hp2 _ _
                             ltac:(apply Z.leb_le; vm_compute; reflexivity) HS);
                             [vm_compute; reflexivity | vm_compute; reflexivity | exact HA1 | vm_compute; reflexivity |
                              vm_compute; reflexivity | exact Hra | exact HJ2 | exact HK8 | | ].
                           { rewrite HFP. intros a (r & Hr & Hb). exists r. split; [apply in_or_app; left; exact Hr | exact Hb]. }
                           intros mat'. cbv beta. unfold fQmn. cbv beta.
                           split; [|exact (PEND _ HPM)].
                           split; [exact HRL2|].
                           (* the hull use: the kids call's alone, an array (PwGrowG's grow_hull_one) *)
                           split; [rewrite Heq; exact (grow_hull_one S S2 (ty =? 6) cap HHU1)|].
                           split; [unfold PRH_Charge.prh_held; destruct HHELD as (-> & ->); rewrite HBB2; lia|].
                           right; right; right; left.
                           split; [exact Heq|]. split; [exact Hcf|]. split; [exact Hty6|]. split; [exact HA00|].
                           exists res, ((res, 56 * cap2R cap) :: l1 ++ l2).
                           split; [exact Hres1|]. split; [exact Hres16|].
                           split.
                           { (* the swap: the old kids block out, the new one in; the rest (b1 ++ b2, the other heads,
                                l1 ++ l2) unchanged *)
                             unfold kids_blkR; rewrite (proj2 (Z.eqb_neq cap 0) Hcz).
                             split; [|split].
                             - exists (b1 ++ b2). unfold prhReader_ab; cbn [map fst snd app]. split.
                               + rewrite Hb12. apply Permutation_sym, Permutation_middle.
                               + exact HPb.
                             - exists (map (fun ak => fst ak - cf_head) (l1 ++ l2)). unfold prhReader_hd; cbn [map fst app].
                               split.
                               + pose proof HLED as (_ & _ & _ & HPH). eapply perm_trans; [exact HPH|].
                                 rewrite HLam, !map_app. cbn [map fst]. apply Permutation_sym, Permutation_middle.
                               + pose proof HL2 as (_ & _ & _ & HPH2). exact HPH2.
                             - exists (l1 ++ l2). cbn [app].
                               split; [rewrite HLam; apply Permutation_sym, Permutation_middle | reflexivity]. }
                           split; [exact HLEDr|].
                           split; [cbn [Ledger.lsum]; rewrite HLam, HLS; destruct HHELD as (-> & _); rewrite Hc2; clear - Hc2; lia|].
                           split; [exact HKBr|].
                           split; [exact HVISr|].
                           split; [exact HHDRr|].
                           (* the slots at the doubled capacity: 2 cap <= 2 ^ 54, the new block below alloc_ceiling *)
                           split.
                           { unfold pj_slots_atR. split; [exact (proj1 HSLOT)|].
                             (* lia in a small context only: in the walk's full context a bare lia searches every
                                disjunctive hypothesis (MEASURED: one such call ran 30 minutes) *)
                             split; [clear - Heq Hncap Hcap Hc2 Hnc Hrqn Hn4096 C1 Hh0; lia|].
                             split; [intros Hc0'; clear - Hc0' Hc2 Hcz; lia|].
                             intros _. split; [unfold prh_lin; left; reflexivity | intros H6; exfalso; exact (Hty6 H6)]. }
                           (* THE EXACT ADVANCE (outcomes [true]: E = the kids realloc's event, HRe (56 cap) (56 cap2R)) *)
                           replace (prhPg_evs (ty =? 6) n cap [true])
                             with [PresetReqAt.HRe (56 * cap + cf_head) (56 * cap2R cap + cf_head)]
                             by (unfold prhPg_evs, prhPg_ev; rewrite Heq, Z.ltb_irrefl, (proj2 (Z.eqb_neq ty 6) Hty6);
                                 cbn [nth andb]; rewrite (proj2 (Z.eqb_neq cap 0) Hcz); reflexivity).
                           split; [exact (grow_live_re B ly S ly2 S2 b1 b2 kids (56 * cap) res (56 * cap2R cap) Hb12 HPb) |
                                   exact (HPOSR ltac:(clear - Hres1 Hh0; lia) Hkids0)].
                       *** (* ty = 6 (arms 5 / 6 / 7, an object): run 9 from i = 60 - s1 := v + 32, the v + 32
                              shadow check (report site 0x871fc, decided inside the run by sh_ok growB_SH), a0 := keys,
                              a1 := s3 = 8 * cap2R cap - to the keys `jal fuzz_realloc` (i = 67) *)
                           assert (Hty6 : ty = 6).
                           { pose proof HSLOT as ([H5 | H6] & _); [|exact H6]. exfalso. rewrite branch_ne_U in Hc1.
                             rewrite U_SExt, U_SOff, U33', H5, U_lit in Hc1 by lia. vm_compute in Hc1. discriminate. }
                           pose proof HJ2 as (HARc9 & _).
                           paj_run_tok_x_inv (RUNBP PM PLAW) HS HJ2 SHOK2 HPM growB_Bspan.
                           { apply (grow_awr_ok_fr _ _ (@STK_grow prh_img_B) GROW_FR_B e (spZ regs) FP _ _ S ly2 v);
                               [unfold GROW_FR_B; lia | exact FS | exact He0 | | | ].
                             - unfold GROW_FR_B; grow_wr_tac U2' U10'.
                             - intros a Ha. rewrite HFP. exact (grow_FP_v v ty kids keys cap a Ha).
                             - exact HVL2'. }
                           match type of HS with st_ok _ E1 _ _ => idtac | _ => fail "run 9 changed the environment" end.
                           destruct (grow_stretch B ARx SK LAWS (@STK_grow prh_img_B) GROW_FR_B E1 _ W2 mem2 (ms_mem ms3)
                             _ (ms_mem ms4) _ (spZ regs) v FP ly S Hp W mem md ly2 S2 Hp2 ltac:(unfold GROW_FR_B; lia) FS
                             HK7 HFR7 HGR7 HAR HARc9 ltac:(rewrite Hslo2; exact Hceil) ltac:(rewrite Hslo2; exact Hslo)
                             ltac:(rewrite Hshi2; exact Hshi) HFr1 HG1 ltac:(unfold GROW_FR_B; grow_wr_tac U2' U10')
                             (same_but_materialized_wvb_any _ mat4)) as (HK9 & HFR9 & HGR9).
                           (* THE OLD KEYS BLOCK (pj_slots_atR at 0 < cap, ty = 6): a ledger entry, apart from the old
                              kids block, so not the kids realloc's: live at S2, its bytes kept to the keys call *)
                           assert (Hrq8 : 8 * cap + cf_head <= req_size (8 * cap + cf_head))
                             by (unfold req_size; destruct (Z.eqb_spec (8 * cap + cf_head) 0); lia).
                           assert (Hrq56 : 56 * cap + cf_head <= req_size (56 * cap + cf_head))
                             by (unfold req_size; destruct (Z.eqb_spec (56 * cap + cf_head) 0); lia).
                           assert (HLky : In (keys, 8 * cap) Lam) by exact (proj2 (Hpos ltac:(lia)) Hty6).
                           pose proof HLED as (_ & _ & HFl0 & _).
                           pose proof (proj1 (Forall_forall _ _) HFl0 (keys, 8 * cap) HLky) as (Hk8 & HbyS & Hhy & _).
                           cbn [fst snd] in Hk8, HbyS, Hhy.
                           assert (Hky12 : In (keys, 8 * cap) (l1 ++ l2)).
                           { pose proof HLky as HL0. rewrite HLam in HL0. apply in_app_or in HL0 as [H1 | [H2 | H3]];
                               [apply in_or_app; left; exact H1 | injection H2 as _ Hk; exfalso; clear - Hk Hcz; lia
                               | apply in_or_app; right; exact H3]. }
                           assert (HbyS2 : In (keys - cf_head, 8 * cap + cf_head) (ablocks B ly2 S2)).
                           { apply (Permutation_in _ (Permutation_sym HPb)). right.
                             pose proof HbyS as HB0. rewrite Hb12 in HB0. apply in_app_or in HB0 as [H1 | [H2 | H3]];
                               [apply in_or_app; left; exact H1 | injection H2 as _ Hk; exfalso; clear - Hk Hcz; lia
                               | apply in_or_app; right; exact H3]. }
                           assert (Hk4096' : 4096 + cf_head <= keys).
                           { destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR HbyS) as (_ & H4 & _). clear - H4. lia. }
                           assert (Hkeys0 : keys <> 0) by (clear - Hk4096' Hh0; lia).
                           assert (HinY : In (keys - cf_head, keys - cf_head + req_size (8 * cap + cf_head))
                             (ablocks_fp (prhReader_ab (kids_blkR kids cap ++ keys_blkR ty keys cap)))).
                           { unfold ablocks_fp, prhReader_ab, kids_blkR, keys_blkR.
                             rewrite (proj2 (Z.eqb_neq cap 0) Hcz), (proj2 (Z.eqb_eq ty 6) Hty6).
                             cbn [app map fst snd orb negb]. right. left. reflexivity. }
                           destruct (HOLD Heq) as (_ & _ & HY). destruct (HY Hty6) as (Hyb0 & Hybl).
                           assert (HKY4 : forall x, keys - cf_head <= x < keys - cf_head + req_size (8 * cap + cf_head) ->
                             aview SEGS (w_H W2) (ms_mem ms4) x = aview SEGS (w_H W) mem x).
                           { intros x Hx.
                             destruct (grow_slot_apart B ARx LAWS GROW_FR_B ly S Hp W mem md Lam peak cnt fail ran most own
                               regs e v ty kids keys n cap _ _ x ltac:(unfold GROW_FR_B; lia) ltac:(lia) HAR HLED HAT
                               Hsp128 HSLOT HAP HinY Hx) as (Hx64 & Hxw).
                             assert (Hcall : aview SEGS (w_H W) (ms_mem ms1) x = aview SEGS (w_H W) mem x)
                               by (apply aview_eq_of; apply HFR3; rewrite unsigned_lit_small by exact Hx64; exact Hxw).
                             assert (Hnf : ~ inFP (if kids =? 0 then [] else ablocks_fp [(kids - cf_head, 56 * cap + cf_head)]) x).
                             { rewrite (proj2 (Z.eqb_neq kids 0) Hkids0). intros (r & Hr & Hb).
                               cbn [ablocks_fp map In] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Hb.
                               assert (Hneq : (kids - cf_head, 56 * cap + cf_head) <> (keys - cf_head, 8 * cap + cf_head)).
                               { intros Heq2. injection Heq2 as _ Hk2. clear - Hk2 Hcz; lia. }
                               pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hbkids HbyS Hneq) as Hdj.
                               unfold zdisjoint in Hdj; cbn [fst snd] in Hdj. clear - Hdj Hx Hb; lia. }
                             assert (Hpost : aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W) (ms_mem ms1) x).
                             { assert (Hi : 0 <= x - (keys - cf_head) < req_size (8 * cap + cf_head)) by (clear - Hx; lia).
                               pose proof (G2c (keys - cf_head) (8 * cap + cf_head) (x - (keys - cf_head)) HbyS HbyS2 Hi) as HG2.
                               replace (keys - cf_head + (x - (keys - cf_head))) with x in HG2 by ring.
                               exact (HG2 Hnf). }
                             assert (Hret : aview SEGS (w_H W2) (ms_mem ms4) x = aview SEGS (w_H W2) mem2 x)
                               by (apply aview_eq_of; apply HFR9; rewrite unsigned_lit_small by exact Hx64; exact Hxw).
                             rewrite Hret, Hpost. exact Hcall. }
                           assert (HYB4 : bytes_at W2 (ms_mem ms4) keys yb).
                           { unfold bytes_at in *. apply (garr8R_frame SEGS _ _ _ _ Hyb0).
                             intros x Hx. rewrite Hybl in Hx.
                             assert (Hxr : keys - cf_head <= x < keys - cf_head + req_size (8 * cap + cf_head))
                               by (clear - Hx Hrq8 Hh0; lia).
                             apply (mbyte_of_aview SEGS). first [exact (HKY4 x Hxr) | exact (eq_sym (HKY4 x Hxr))]. }
                           (* the ledger at the keys call memory: the kids call's post ledger, its cells apart from grow's
                              writes at the post state *)
                           assert (HLEDk : prh_ledger B ly2 S2 Hp2 W2 (ms_mem ms4) ((res, 56 * cap2R cap) :: l1 ++ l2)
                             (Z.max peak (Ledger.lsum ((res, 56 * cap2R cap) :: l1 ++ l2))) (cnt + 1) fail ran most own).
                           { apply (prh_ledger_keep B ly2 S2 Hp2 W2 mem2 (ms_mem ms4) _ _ _ _ _ _ _ HL2').
                             intros a Hca.
                             destruct (grow_cell_apart B ARx LAWS HPST GROW_FR_B ly2 S2 Hp2 W2 mem2 md2 _ _ _ _ _ _ _ regs e v a
                               ltac:(unfold GROW_FR_B; lia) HAR2 HL2' HAT2 Hsp128 Hoff Hca) as (Ha64 & Hwa).
                             apply HFR9. rewrite unsigned_lit_small by exact Ha64. exact Hwa. }
                           (* the keys call state's registers: s0 = v + 48, a0 = keys (loaded from v + 32), a1 = s3 =
                              cap << 4 (= 8 * cap2R cap), ra = the return slot i = 68, sp = the entry's - 96 *)
                           pose proof (st_ok_restrict_reg SEGS (w_H W2) _ _ ms4 8%bv HS) as R8k.
                           pose proof (st_ok_restrict_reg SEGS (w_H W2) _ _ ms4 10%bv HS) as R10k.
                           pose proof (st_ok_restrict_reg SEGS (w_H W2) _ _ ms4 11%bv HS) as R11k.
                           pose proof (st_ok_restrict_reg SEGS (w_H W2) _ _ ms4 1%bv HS) as R1k.
                           pose proof (st_ok_restrict_reg SEGS (w_H W2) _ _ ms4 2%bv HS) as R2k.
                           match type of R8k with _ = sv_denot _ ?t => let t' := eval vm_compute in t in change t with t' in R8k end.
                           match type of R10k with _ = sv_denot _ ?t => let t' := eval vm_compute in t in change t with t' in R10k end.
                           match type of R11k with _ = sv_denot _ ?t => let t' := eval vm_compute in t in change t with t' in R11k end.
                           match type of R1k with _ = sv_denot _ ?t => let t' := eval vm_compute in t in change t with t' in R1k end.
                           match type of R2k with _ = sv_denot _ ?t => let t' := eval vm_compute in t in change t with t' in R2k end.
                           assert (H10k : getr (ms_regs ms4) 10%bv = w64 keys)
                             by (rewrite R10k; cbn [sv_denot]; rewrite U35', Z.add_0_r; reflexivity).
                           assert (H11k : getr (ms_regs ms4) 11%bv = w64 (8 * cap2R cap)).
                           { rewrite R11k. apply bv_eq. unfold w64.
                             rewrite (unsigned_lit_small (8 * cap2R cap)) by (clear - Hc2 Hcap Hcap54; lia).
                             change (bv_unsigned (sv_denot E1 (SAlu ALU_SLL (SOff 37 0) (SLit 4))))
                               with (U E1 (SAlu ALU_SLL (SOff 37 0) (SLit 4))).
                             rewrite U_SAlu, U_SOff, U37', U_lit by lia. rewrite Z.add_0_r. cbn [zalu_raw].
                             rewrite (zcanon_id cap) by (unfold M64; lia). change (Z.land 4 63) with 4.
                             rewrite Z.shiftl_mul_pow2 by lia. rewrite zcanon_id by (unfold M64; clear - Hcap Hcap54; lia).
                             clear - Hc2; lia. }
                           assert (R1k' : getr (ms_regs ms4) 1%bv = Z_to_bv 64 (BASE + (GROW_OFF_B + 4 * 68))).
                           { rewrite R1k. cbn [sv_denot]. change 240%nat with A_TEXT. rewrite ET'.
                             pose proof (@pa_val_range _ B_prog_listing PG A_TEXT) as HBr.
                             rewrite unsigned_lit_small by lia. reflexivity. }
                           assert (Hsp4 : spZ (ms_regs ms4) = spZ regs - GROW_FR_B).
                           { unfold spZ at 1; rewrite R2k; cbn [sv_denot]; rewrite U2', unsigned_lit_small by lia.
                             unfold GROW_FR_B; lia. }
                           assert (Hhic2 : spZ (ms_regs ms4) + 64 <= ly_stk_hi ly2) by (rewrite Hsp4, Hshi2; unfold GROW_FR_B; lia).
                           (* fpre's return-address bound: the return slot i = 68 (growB_ret68_ceil) *)
                           assert (Hra2 : raZ (ms_regs ms4) < YM05.alloc_ceiling)
                             by (unfold raZ; rewrite R1k'; exact growB_ret68_ceil).
                           (* the read-only image view at the keys call memory: the kids call's journal keeps an image
                              byte off PST (HPSTRW: no PST byte is read-only), and grow writes none *)
                           assert (HRODk : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) (ms_mem ms4))).
                           { intros a Hro Ho He.
                             assert (Himg : in_img SEGS a)
                               by (destruct Hro as [(s & Hs & _ & Hlo & Hhi) | Hr]; [exists s; split; [exact Hs | lia] | apply pa_relro_img; exact Hr]).
                             pose proof (pa_segs_low a Himg) as Hl. unfold kLowMemEnd in Hl.
                             rewrite <- (HRODc a Hro Ho He).
                             pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GIc & _).
                             transitivity (aview SEGS (w_H W2) mem2 a).
                             - apply aview_eq_of. apply HFR9. rewrite unsigned_lit_small by lia. unfold grow_wr, GROW_FR_B.
                               intros [Hw | [Hw | Hw]]; [lia | exact (Hoff a ltac:(lia) Himg) | exact (Hoff a ltac:(lia) Himg)].
                             - apply GIc; [exact Himg | exact Ho | exact He | intros Hp0; exact (HPSTRW a Hp0 Hro) |].
                               apply fp_spares_closed. rewrite (proj2 (Z.eqb_neq kids 0) Hkids0).
                               apply sink_closed_ablocks_fp. constructor; [cbn [fst]; clear - Hk4096 Hh0; lia | constructor]. }
                           (* the node's fields keys / n / cap at the keys call, off its two symbolic regions *)
                           assert (RA4 : region_ok SEGS E1 (mrestrict (w_H W2) (ms_mem ms4)) (YP09.mkRegion (Some 10%nat) 0 40 24 40
                             [YP09.mkChunk 24 (CVal 8 (SOff 42 0)); YP09.mkChunk 0 (CVal 4 (SOff 33 0));
                              YP09.mkChunk 32 (CVal 8 (SOff 35 0))]))
                             by exact (st_ok_region_nth SEGS E1 _ _ 0 _ HS ltac:(vm_compute; reflexivity)).
                           assert (RB4 : region_ok SEGS E1 (mrestrict (w_H W2) (ms_mem ms4)) growB_vB)
                             by exact (st_ok_region_nth SEGS E1 _ _ 1 growB_vB HS ltac:(vm_compute; reflexivity)).
                           unfold growB_vB in RB4.
                           pose proof (field_of_region SEGS E1 _ 10 v _ 0 40 24 40 32 8 (SOff 35 0) keys RA4 U10' ltac:(cbn; tauto)
                             ltac:(cbn [sv_denot]; rewrite U35', Z.add_0_r; reflexivity)
                             ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as Vy4.
                           pose proof (field_of_region SEGS E1 _ 10 v _ 40 56 48 56 48 8 (SOff 37 0) cap RB4 U10' ltac:(cbn; tauto)
                             ltac:(cbn [sv_denot]; rewrite U37', Z.add_0_r; reflexivity)
                             ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as Vc4.
                           pose proof HHDR2 as (_ & _ & _ & _ & (_ & Vkids2) & (_ & Vkeys2) & (_ & Vn2') & (_ & Vcap2)).
                           (* the chain at s0 = v + 48 at the keys call: the kids call's (Hch1), kept above v + 32 (the
                              node by its field values and HVK, above it by the stretches and the kids call's journal) *)
                           assert (HCHk : exists ch2, achain ly2 (aview SEGS (w_H W2) (ms_mem ms4)) (spZ regs - GROW_FR_B) (v + 48) ch2).
                           { destruct (Z_lt_ge_dec (v + 48) YM05.alloc_ceiling) as [Hlo48 | Hhi48].
                             { exists []. apply achain_low. exact Hlo48. }
                             assert (Hvsp : spZ regs <= v).
                             { destruct Hvloc as [(b & m & Hinb & H1 & H2) | [(cid & pos & Hinf & H1 & H2) | Hx]].
                               - destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hinb) as (_ & _ & Hbc & _).
                                 assert (Hqm : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia). lia.
                               - destruct (alx_sep _ _ _ LAWS _ _ _ _ _ _ HAR) as (_ & Hfr).
                                 pose proof (proj1 (Forall_forall _ _) Hfr (cid, pos) Hinf) as (_ & Hfc). cbn [fst snd] in Hfc. lia.
                               - lia. }
                             exists ch1. apply (achain_ly_top ly ly2 _ _ _ _ Htop2').
                             refine (achain_kept_hi _ _ _ _ _ _ Hch1 ltac:(lia) _).
                             intros a Ha Hb. pose proof Hvstk as Hvs96. unfold GROW_FR_B in Hvs96.
                             destruct (Z_lt_ge_dec a (v + 56)) as [A3 | A3].
                             - rewrite <- (proj1 (HVK a ltac:(lia))).
                               destruct (Z_lt_ge_dec a (v + 40)) as [A1 | A1];
                                 [exact (aview_of_val_mem_eq (w_H W2) mem2 (ms_mem ms4) (v + 32) keys Vkeys2 Vy4 a ltac:(lia)) |].
                               destruct (Z_lt_ge_dec a (v + 48)) as [A2 | A2];
                                 [apply aview_eq_of; apply HFR9; rewrite unsigned_lit_small by lia; unfold grow_wr, GROW_FR_B; lia |].
                               exact (aview_of_val_mem_eq (w_H W2) mem2 (ms_mem ms4) (v + 48) cap Vcap2 Vc4 a ltac:(lia)).
                             - transitivity (aview SEGS (w_H W2) mem2 a).
                               { apply aview_eq_of. apply HFR9. rewrite unsigned_lit_small by lia. unfold grow_wr, GROW_FR_B. lia. }
                               exact (G1c a ltac:(lia) ltac:(unfold GROW_FR_B; lia)). }
                           destruct HCHk as (ch2 & Hch2).
                           (* the callee's run position and live-set counts at its call state S2 *)
                           assert (Hr0 : res <> 0) by (clear - Hres1 Hh0; lia).
                           (* THE LIVE COUNTS at the keys call state S2: the text's pkR premises at the state after the kids call's event
                              (pkR_prefix at j = 1; S2's live requests are the entry's moved by the kids realloc) *)
                           assert (HLV2 : Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S2))
                             (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
                                [PresetReqAt.HRe (56 * cap + cf_head) (56 * cap2R cap + cf_head)]))
                             by exact (grow_live_re B ly S ly2 S2 b1 b2 kids (56 * cap) res (56 * cap2R cap) Hb12 HPb).
                           assert (HE1 : firstn 1 (prhPg_evs (ty =? 6) n cap []) =
                             [PresetReqAt.HRe (56 * cap + cf_head) (56 * cap2R cap + cf_head)])
                             by (unfold prhPg_evs, prhPg_ev; rewrite Heq, Z.ltb_irrefl, (proj2 (Z.eqb_neq cap 0) Hcz);
                                 reflexivity).
                           assert (HSEC2 : YGcfRoomLive.sec_cnt S2 <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV)
                             by (refine (grow_cnt_at YGcfRoomLive.rl_sec_req S S2 _ 1 _ _ HPKS); rewrite HE1; exact HLV2).
                           assert (HC242 : YGcfRoomLive.ccnt24 S2 <= PresetLiveBounds.L24 + PresetLiveBounds.DRV)
                             by (refine (grow_cnt_at (PresetRoom.in_cls YG00.kBatchClass) S S2 _ 1 _ _ HPK24); rewrite HE1;
                                 exact HLV2).
                           assert (Hn0k : 0 <= 8 * cap2R cap) by (clear - Hc2 Hcap; lia).
                           assert (Hnmaxk : 8 * cap2R cap + cf_head < cf_malloc_max) by (clear - Hnmax0 Hc2 Hcap; lia).
                           (* the keys call's live room: the text's per-event room at the second event, S2's live
                              requests being the entry's moved by the kids event (PwGrowLive's grow_room_keys) *)
                           assert (HLIVEk : blocks_bytes S2 + (8 * cap2R cap + cf_head) <= LIVE_MAX).
                           { pose proof HLv as HLv6. rewrite (proj2 (Z.eqb_eq ty 6) Hty6) in HLv6.
                             refine (grow_room_keys B ly2 S S2 cap HLv6 _). unfold prhPg_ev. rewrite (proj2 (Z.eqb_neq cap 0) Hcz). exact HLV2. }
                           assert (HOLDk : In (keys, 8 * cap) ((res, 56 * cap2R cap) :: l1 ++ l2) /\
                             bytes_at W2 (ms_mem ms4) keys yb /\ Z.of_nat (length yb) = 8 * cap)
                             by (split; [right; exact Hky12 | split; [exact HYB4 | exact Hybl]]).
                           pose proof HJ2 as (HARc10 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRc10 & _).
                           (* THE HULL BUDGET of the keys call (at S2): grow's budget less the kids call's use HHU1
                              (PwGrowG's grow_hull_keys), the event in the realloc text's form by grow_hull_ev *)
                           assert (HYC0 : keys = 0 <-> cap = 0)
                             by (split; intros Hz; exfalso; [exact (Hkeys0 Hz) | exact (Hcz Hz)]).
                           assert (HHUY : PresetHullBudget.hull_budget S2
                             (if keys =? 0 then [PresetReqAt.HMal (8 * cap2R cap + cf_head)]
                              else [PresetReqAt.HRe (8 * cap + cf_head) (8 * cap2R cap + cf_head)])).
                           { rewrite (grow_hull_ev keys 8 cap HYC0). rewrite Heq, (proj2 (Z.eqb_eq ty 6) Hty6) in HHULL.
                             exact (grow_hull_keys S S2 cap HHULL HHU1). }
                           (* THE KEYS REALLOC (i = 67): aj_call_xW_spR at the post state of the kids call *)
                           eapply (SRr'_bind SEGS RZ_cf).
                           { match type of HS with st_ok _ ?Ec ?ss4 (restrict _ ?ms4) =>
                               eapply (aj_call_xW_spR (SK := SK) SEGS B PST ARx LAWS pa_segs_low (wle' SEGS RZ_cf)
                                 (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf) W2 Ec ss4 ms4 _ _ FP ly S Hp W mem md []
                                 ly2 S2 Hp2 _ _ (@STK_fuzz_realloc prh_img_B) 0
                                 (if keys =? 0 then [] else ablocks_fp [(keys - cf_head, 8 * cap + cf_head)])
                                 (- GROW_FR_B - e) _ ch2 _ HS) end;
                             [ vm_compute; reflexivity
                             | exact HJ2
                             | rewrite Hsp4; unfold GROW_FR_B; lia
                             | rewrite <- Zminus_mod_idemp_r, He16; vm_compute; reflexivity
                             | unfold GROW_FR_B; lia
                             | apply Z.leb_le; vm_compute; reflexivity
                             | unfold GROW_FR_B;
                               assert (Hs96 : @STK_grow prh_img_B = 96 + @STK_fuzz_realloc prh_img_B) by (vm_compute; reflexivity); lia
                             | lia
                             | reflexivity
                             | unfold GROW_FR_B; lia
                             | (* gp: reg 3 is the entry's *)
                               match goal with |- getr (ms_regs ?m) _ = _ =>
                                 rewrite (st_ok_restrict_reg SEGS (w_H W2) _ _ m 3%bv HS) end;
                               match goal with |- sv_denot _ ?t = _ => let t' := eval vm_compute in t in change t with t' end;
                               cbn [sv_denot]; rewrite (AGo 3%nat ltac:(lia)), E3, Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp
                             | (* tp: reg 4 is the entry's *)
                               match goal with |- getr (ms_regs ?m) _ = _ =>
                                 rewrite (st_ok_restrict_reg SEGS (w_H W2) _ _ m 4%bv HS) end;
                               match goal with |- sv_denot _ ?t = _ => let t' := eval vm_compute in t in change t with t' end;
                               cbn [sv_denot]; rewrite (AGo 4%nat ltac:(lia)), E4, Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp
                             | reflexivity
                             | (* ret_ok of the return site BASE + GROW_OFF_B + 4 * 68: BASE is 4-aligned (pa_B_ok) *)
                               unfold YK0s.ret_ok; rewrite R1k';
                               pose proof (@pa_val_range _ B_prog_listing PG A_TEXT) as HBr;
                               pose proof (@pa_B_ok _ B_prog_listing PG) as (HB0 & HB40 & HB4);
                               unfold v_jalr, jalr_tgtZ; rewrite unsigned_lit_small by (unfold GROW_OFF_B; lia); rewrite Z.add_0_r;
                               rewrite land_m2_even; [reflexivity|]; unfold GROW_OFF_B;
                               replace (BASE + (4 * 5731 + 4 * 68)) with ((2 * (BASE / 4) + 2 * 5731 + 2 * 68) * 2)
                                 by (pose proof (Z.div_mod BASE 4 ltac:(lia)); lia);
                               apply Z.mod_mul; lia
                             | (* the return site BASE + GROW_OFF_B + 4 * 68 is above 4096 *)
                               rewrite R1k';
                               pose proof (@pa_val_range _ B_prog_listing PG A_TEXT) as HBr;
                               pose proof (@pa_B_ok _ B_prog_listing PG) as (HB0 & HB40 & _);
                               rewrite unsigned_lit_small by (unfold GROW_OFF_B; lia); unfold GROW_OFF_B; lia
                             | (* the chain at s0 = v + 48: reg 8 is SOff 10 48 *)
                               unfold s0Z; rewrite R8k; cbn [sv_denot]; rewrite U10', unsigned_lit_small by lia;
                               match goal with |- achain _ _ ?spx _ _ => replace spx with (spZ regs - GROW_FR_B) by lia end;
                               exact Hch2
                             | (* the callee: the kit's tfuzz_realloc_specX (HREALLOC) at the keys call state, through
                                  fpostW_x_of_apostR *)
                               intros Hpre Hwin;
                               eapply (SRr'_mono SEGS RZ_cf);
                               [ refine (HREALLOC ly2 S2 Hp2 W2 (ms_regs ms4)
                                  (ms_mem ms4) _ ch2 keys (8 * cap) (8 * cap2R cap) yb ((res, 56 * cap2R cap) :: l1 ++ l2)
                                  (Z.max peak (Ledger.lsum ((res, 56 * cap2R cap) :: l1 ++ l2))) (cnt + 1) fail ran most own
                                  (conj Hpre (conj HRODk (conj Hhic2 (conj Hra2 HFRM)))) HRL2 HMU HSEC2 HC242 HHUY
                                  (proj1 HUR) (proj2 HUR)
                                   H10k H11k Hn0k Hnmaxk HLEDk (or_intror HOLDk) (fun _ => HLIVEk))
                               | intros W3 c3 _ HP3; apply fpostW_x_of_apostR; exact HP3 ]
                             | (* fp_sub_x: the callee's footprint, the old keys block, lies in the kit's FP *)
                               intros a Ha; left; rewrite HFP;
                               destruct (Z.eqb_spec keys 0) as [Hy0 | Hy0]; [destruct Ha as (r & [] & _) |];
                               destruct Ha as (r & Hr & Hb); exists r; split; [| exact Hb];
                               apply in_or_app; right;
                               cbn [ablocks_fp map In] in Hr; destruct Hr as [<- | []]; exact HinY ]. }
                           intros W3 c3 HW3 (ly3 & S3 & Hp3 & regs3 & mem3 & md3 & k3 & -> & HJ3 & HJ1k & _ & HP3 & HQk).
                           (* the keys realloc's post: its result, room_live_cf, its hull use HHU2, the run position, its
                              arms; its m-form keep HMN2 *)
                           destruct HQk as ((res2 & H10r2 & HRL3 & HHU2 & HPOS0k & _ & HPOSRk & _ & HOUTRk & HARMSk) & HMN2).
                           rewrite (grow_hull_ev keys 8 cap HYC0) in HHU2.
                           pose proof (PCALL _ _ HMN2 HPM) as HPM3. clear HPM. rename HPM3 into HPM.
                           destruct HARMSk as [(Hy0 & _) | HARMSk]; [exfalso; exact (Hkeys0 Hy0) |].
                           (* the node across the keys call: its 56 bytes kept and present (grow_v_kept_fp; the old keys
                              block, the callee's footprint, is apart from v by grow_slot_v at the entry) *)
                           assert (HnFPk : forall a, v <= a < v + 56 ->
                             ~ inFP (if keys =? 0 then [] else ablocks_fp [(keys - cf_head, 8 * cap + cf_head)]) a).
                           { intros a Ha. rewrite (proj2 (Z.eqb_neq keys 0) Hkeys0). intros (r & Hr & Hb).
                             cbn [ablocks_fp map In] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Hb.
                             exact (grow_slot_v B ARx LAWS ly S Hp W mem md Lam peak cnt fail ran most own regs e v ty kids keys n cap _ _ a
                               (proj1 Hcap) HAR HLED HAT Hsp128 HSLOT HAP HinY Hb Ha). }
                           assert (HVKk : forall a, v <= a < v + 56 ->
                             aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) (ms_mem ms4) a /\ apresent (w_H W3) mem3 a)
                             by exact (grow_v_kept_fp B ARx SK LAWS ly2 S2 Hp2 W2 (ms_mem ms4) _ _ _ _ _ _ _ _ regs e v _ _ _
                                  ly3 S3 Hp3 W3 mem3 md3 k3 HARc10 HLEDk HAT2 Hsp128 Hv4096 ltac:(lia) Hoff
                                  ltac:(intros a Ha; apply HPRc10; lia) HJ1k ltac:(unfold GROW_FR_B; lia) HnFPk).
                           pose proof HJ1k as (_ & Hly1k & _ & _ & _ & Hfrs1k & _ & _ & G1k & G2k & _).
                           destruct Hly1k as (_ & _ & _ & _ & _ & HlyFk & _).
                           assert (HFRS3 : frames S3 = frames S2) by (rewrite Hfrs1k; reflexivity).
                           assert (HFA3 : forall cid pos, frame_addr ly3 cid pos = frame_addr ly2 cid pos)
                             by (intros cid pos; unfold frame_addr; rewrite HlyFk; reflexivity).
                           pose proof HJ3 as (HAR3 & Hly3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES3 & _).
                           destruct Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & Htop3' & Hslo3 & Hshi3 & _).
                           destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HARc10) as (Kc3a & _ & Kg3a & _).
                           destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HAR3) as (Kc3 & _ & Kg3 & _).
                           rewrite HGOT, HCELL in Kg3a, Kg3. rewrite HCELL in Kc3a, Kc3.
                           rewrite R1k'.
                           (* RE-SEAT at the return site (i = 68): the caller-saved registers havocked into atoms 54...
                              KEPT REGIONS: grow's frame and the two image cells (regions 2, 3, 4 at the keys call); the
                              node's two regions are dropped, as at the kids call *)
                           jafter_call_keep_pi HS 54%nat regs3 (mrestrict (w_H W3) mem3) HP3 [2; 3; 4]%nat HS3.
                           match type of HS3 with ?P -> _ => assert (HQ : P); [|specialize (HS3 HQ); clear HQ] end.
                           { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
                             - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite U2'; intros a Ha.
                               + apply (mbyte_of_aview SEGS). apply G1k; unfold GROW_FR_B in *; lia.
                               + intros _. apply (apresent_writable SEGS). apply HPRES3. unfold GROW_FR_B in *; lia.
                             - apply (region_kept_val_at E1 _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12)));
                                 [exact (HEI1' (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))
                                 | exact (val_mem_of_rdword SEGS _ _ _ _ Kg3a)
                                 | exact (val_mem_of_rdword SEGS _ _ _ _ Kg3) | lia].
                             - apply (region_kept_val_at E1 _ _ (A_OBJ 12) (VAL (A_OBJ 12)) 8 SHADOW_OFF);
                                 [exact (HEI1' (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))
                                 | exact (val_mem_of_rdword SEGS _ _ _ _ Kc3a)
                                 | exact (val_mem_of_rdword SEGS _ _ _ _ Kc3) | lia]. }
                           clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
                           (* the environment after the keys call: the caller-saved registers are fresh atoms 54.. *)
                           set (E2 := havoc E1 54 (map (getr regs3) CLOB)) in HS.
                           assert (HEI2' : img_env VAL A_LIM E2) by (subst E2; apply img_env_havoc; [exact HEI1' | cbv; lia]).
                           pose proof (st_ok_pi_restrict_reg (w_H W3) E2 _ _ 10%bv HS) as R10r2.
                           match type of R10r2 with _ = sv_denot _ ?t => let t' := eval vm_compute in t in change t with t' in R10r2 end.
                           cbn [ms_regs mkst] in R10r2.
                           assert (AGo2 : forall i, (i < 54)%nat -> ew E2 i = ew E1 i) by (intros i Hi; subst E2; apply ew_havoc_old; lia).
                           assert (U2'' : bv_unsigned (ew E2 2) = spZ regs) by (rewrite AGo2 by lia; exact U2').
                           assert (U10'' : bv_unsigned (ew E2 10) = v) by (rewrite AGo2 by lia; exact U10').
                           assert (U32'' : bv_unsigned (ew E2 32) = SHADOW_OFF) by (rewrite AGo2 by lia; exact U32').
                           assert (U33'' : bv_unsigned (ew E2 33) = ty) by (rewrite AGo2 by lia; exact U33').
                           assert (U35'' : bv_unsigned (ew E2 35) = keys) by (rewrite AGo2 by lia; exact U35').
                           assert (U36'' : bv_unsigned (ew E2 36) = n) by (rewrite AGo2 by lia; exact U36').
                           assert (U37'' : bv_unsigned (ew E2 37) = cap) by (rewrite AGo2 by lia; exact U37').
                           assert (U42'' : bv_unsigned (ew E2 42) = res) by (rewrite AGo2 by lia; exact U42).
                           assert (ET'' : ew E2 A_TEXT = Z_to_bv 64 BASE)
                             by (subst E2; rewrite ew_havoc_above by (unfold A_TEXT; cbv; lia); exact ET').
                           assert (HA2 : env_agree 32 (Ereg regs (growB_extra ty kids keys n cap)) E2)
                             by (subst E2; apply env_agree_havoc_ge; [lia | exact HA1]).
                           (* E2's body is no longer needed: opaque from here, so no later conversion unfolds the havoc (Qed cost) *)
                           clearbody E2.
                           (* grow_vloc at the keys call's post state (grow_vloc2_fp), for the runs after the call *)
                           assert (HFPsubk : forall r, In r (if keys =? 0 then [] else ablocks_fp [(keys - cf_head, 8 * cap + cf_head)]) ->
                             In r (ablocks_fp (prhReader_ab (kids_blkR kids cap ++ keys_blkR ty keys cap)))).
                           { intros r Hr. rewrite (proj2 (Z.eqb_neq keys 0) Hkeys0) in Hr.
                             cbn [ablocks_fp map In] in Hr; destruct Hr as [<- | []]. exact HinY. }
                           assert (HVL3 : grow_vloc B ly3 S3 regs e v)
                             by exact (grow_vloc2_fp B ARx SK ly2 S2 Hp2 W2 (ms_mem ms4) _ _ _ _ _ _ _ _ regs e v _ _ _
                                  ly3 S3 Hp3 W3 mem3 md3 k3 HLEDk HAT2 HJ1k HnFPk).
                           assert (HVL3' : (exists b m, In (b, m) (ablocks B ly3 S3) /\ b <= v /\ v + 56 <= b + req_size m) \/
                             (exists cid pos, In (cid, pos) (frames S) /\
                                frame_addr ly3 cid pos <= v /\ v + 56 <= frame_addr ly3 cid pos + fs_frame_bytes cid) \/
                             (spZ regs <= v /\ v + 56 <= spZ regs + e)).
                           { destruct HVL3 as [Hx | [Hx | Hx]]; [left; exact Hx | right; left | right; right; exact Hx].
                             destruct Hx as (cid & pos & Hin & Hx1 & Hx2). exists cid, pos.
                             rewrite HFRS3, HFRS2 in Hin. split; [exact Hin | split; [exact Hx1 | exact Hx2]]. }
                           (* the kept relation from entry to the keys call's post state *)
                           rewrite ?wvb_collapse in HK9, HJ3, HJ1k.
                           assert (HKC3 : cj_keptR (SK := SK) SEGS B PST (wle' SEGS RZ_cf) (@STK_grow prh_img_B) (spZ regs) (grow_OR v) FP
                             ly S W mem md ly3 S3 W3 mem3 md3).
                           { eapply (cj_kept_transR (SK := SK) SEGS B PST ARx LAWS (wle' SEGS RZ_cf) (wle'_trans SEGS RZ_cf)
                               (@STK_grow prh_img_B) (spZ regs)
                               (@STK_fuzz_realloc prh_img_B + 0) (spZ regs + e + (- GROW_FR_B - e) + 0) (grow_OR v) FP _ FP
                               ly S Hp W mem md ly2 S2 Hp2 W2 (ms_mem ms4) _ ly3 S3 W3 mem3 md3 HK9
                               (cj_kept_of_journalR (SK := SK) SEGS B PST ARx (wle' SEGS RZ_cf) _ _ _ ly2 S2 Hp2 W2 (ms_mem ms4) _
                                  ly3 S3 Hp3 W3 mem3 md3 _ (grow_OR v) HJ1k)
                               HAR HARc10); [ | | intros a Ha; left; exact Ha | ].
                             - assert (Hs96 : @STK_grow prh_img_B = 96 + @STK_fuzz_realloc prh_img_B) by (vm_compute; reflexivity).
                               unfold GROW_FR_B; lia.
                             - unfold GROW_FR_B; lia.
                             - intros a Ha. left. rewrite HFP.
                               destruct Ha as (r & Hr & Hb). exists r. split; [| exact Hb].
                               apply in_or_app. right. exact (HFPsubk r Hr). }
                           (* the facts every arm after the keys call shares: the old keys block among b1 ++ b2, the
                              kids swap (prhReader_swap), the grammar's charge of an object's grow, the counter *)
                           assert (HbyB12 : In (keys - cf_head, 8 * cap + cf_head) (b1 ++ b2)).
                           { pose proof HbyS as HB0. rewrite Hb12 in HB0. apply in_app_or in HB0 as [H1 | [H2 | H3]];
                               [apply in_or_app; left; exact H1 | injection H2 as _ Hk; exfalso; clear - Hk Hcz; lia
                               | apply in_or_app; right; exact H3]. }
                           assert (HSWAPk : forall ly' S' Hp',
                             Permutation (ablocks B ly' S') ((res - cf_head, 56 * cap2R cap + cf_head) :: b1 ++ b2) ->
                             Permutation Hp' (map (fun ak => fst ak - cf_head) ((res, 56 * cap2R cap) :: l1 ++ l2)) ->
                             prhReader_swap B ly S Hp Lam ly' S' Hp' ((res, 56 * cap2R cap) :: l1 ++ l2) (kids_blkR kids cap)
                               [(res, 56 * cap2R cap)]).
                           { intros ly' S' Hp' HPb' HPH'. unfold kids_blkR; rewrite (proj2 (Z.eqb_neq cap 0) Hcz).
                             split; [|split].
                             - exists (b1 ++ b2). unfold prhReader_ab; cbn [map fst snd app]. split.
                               + rewrite Hb12. apply Permutation_sym, Permutation_middle.
                               + exact HPb'.
                             - exists (map (fun ak => fst ak - cf_head) (l1 ++ l2)). unfold prhReader_hd; cbn [map fst app].
                               split.
                               + pose proof HLED as (_ & _ & _ & HPH). eapply perm_trans; [exact HPH|].
                                 rewrite HLam, !map_app. cbn [map fst]. apply Permutation_sym, Permutation_middle.
                               + exact HPH'.
                             - exists (l1 ++ l2). cbn [app].
                               split; [rewrite HLam; apply Permutation_sym, Permutation_middle | reflexivity]. }
                           assert (HHELDo : PjGrammar.held (PRH_Charge.prhPg_gtrace (ty =? 6) n cap) = 64 * cap /\
                                            PjGrammar.calls (PRH_Charge.prhPg_gtrace (ty =? 6) n cap) = 2%nat).
                           { rewrite (proj2 (Z.eqb_eq ty 6) Hty6). unfold PRH_Charge.prhPg_gtrace, PjGrammar.grow.
                             replace (Nat.ltb (Z.to_nat n) (Z.to_nat cap)) with false by (symmetry; apply Nat.ltb_ge; lia).
                             replace (Nat.eqb (Z.to_nat cap) 0) with false by (symmetry; apply Nat.eqb_neq; lia).
                             cbn -[Nat.mul]. split; [lia | reflexivity]. }
                           pose proof HLED as Hcnt64k. eapply prh_ledger_bounds in Hcnt64k. destruct Hcnt64k as (_ & _ & Hcnt64k & _).
                           assert (Hmod2 : (cnt + 1 + 1) mod 2 ^ 64 = cnt + 2)
                             by (rewrite Z.mod_small; [ring | clear - HCNT Hcnt64k; lia]).
                           (* the node's header at the keys call memory (kids = res, by the kids store of run 7) *)
                           assert (HHDRk4 : pj_hdrR SEGS (mrestrict (w_H W2) (ms_mem ms4)) v ty num str res keys n cap).
                           { apply (grow_hdr_keep GROW_FR_B (w_H W2) mem2 (ms_mem ms4) (spZ regs) v ty num str kids keys n cap
                               res keys cap HHDR2 HFR9 HGR9 Hvstk ltac:(lia) ltac:(lia)).
                             - split; [lia|].
                               exact (field_of_region SEGS E1 _ 10 v _ 0 40 24 40 24 8 (SOff 42 0) res RA4 U10' ltac:(cbn; tauto)
                                 ltac:(cbn [sv_denot]; rewrite U42, Z.add_0_r; reflexivity)
                                 ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)).
                             - split; [exact Hkeys'|]. exact Vy4.
                             - split; [exact Hcap'|]. exact Vc4. }
                           (* run 10: the return site to the `beqz a0` (i = 68); no shadow byte is read on it *)
                           assert (SHOK0k : sh_ok SEGS growB_Bx [] E2 (mrestrict (w_H W3) mem3)) by (unfold sh_ok; apply Forall_nil).
                           paj_run_tok_x_inv (RUNBP PM PLAW) HS HJ3 SHOK0k HPM growB_Bspan.
                           { apply (grow_awr_ok_fr _ _ (@STK_grow prh_img_B) GROW_FR_B e (spZ regs) FP _ _ S ly3 v);
                               [unfold GROW_FR_B; lia | exact FS | exact He0 | | | ].
                             - unfold GROW_FR_B; grow_wr_tac U2'' U10''.
                             - intros a Ha. rewrite HFP. exact (grow_FP_v v ty kids keys cap a Ha).
                             - exact HVL3'. }
                           match type of HS with st_ok_pi _ _ E2 _ _ => idtac | _ => fail "run 10 changed the environment" end.
                           destruct (grow_stretch B ARx SK LAWS (@STK_grow prh_img_B) GROW_FR_B E2 _ W3 mem3 mem3
                             md3 (ms_mem ms5) _ (spZ regs) v FP ly S Hp W mem md ly3 S3 Hp3 ltac:(unfold GROW_FR_B; lia) FS
                             HKC3 ltac:(intros; reflexivity) (mem_grows_refl _) HAR HAR3
                             ltac:(rewrite Hslo3; exact Hceil) ltac:(rewrite Hslo3; exact Hslo) ltac:(rewrite Hshi3; exact Hshi)
                             HFr2 HG2 ltac:(unfold GROW_FR_B; grow_wr_tac U2'' U10'') (same_but_materialized_wvb_any md3 mat5))
                             as (HK10 & HFR10 & HGR10).
                           psrr_branch_tok RUNB BRB HS SHOK0k growB_Bspan.
                           ---- (* a0 = 0: the keys realloc returned NULL (arm 5, the chosen failure; arm 6, refused):
                                   run 11 from i = 76 (`mv a0, s2` with s2 = -1) through the epilogue to the ret *)
                                pose proof HJ3 as (HARc11 & _).
                                paj_run_tok_x_inv (RUNBP PM PLAW) HS HJ3 SHOK0k HPM growB_Bspan.
                                { apply (grow_awr_ok_fr _ _ (@STK_grow prh_img_B) GROW_FR_B e (spZ regs) FP _ _ S ly3 v);
                                    [unfold GROW_FR_B; lia | exact FS | exact He0 | | | ].
                                  - unfold GROW_FR_B; grow_wr_tac U2'' U10''.
                                  - intros a Ha. rewrite HFP. exact (grow_FP_v v ty kids keys cap a Ha).
                                  - exact HVL3'. }
                                match type of HS with st_ok_pi _ _ E2 _ _ => idtac | _ => fail "run 11 changed the environment" end.
                                destruct (grow_stretch B ARx SK LAWS (@STK_grow prh_img_B) GROW_FR_B E2 _ W3 mem3 (ms_mem ms5)
                                  _ (ms_mem ms6) _ (spZ regs) v FP ly S Hp W mem md ly3 S3 Hp3 ltac:(unfold GROW_FR_B; lia) FS
                                  HK10 HFR10 HGR10 HAR HARc11 ltac:(rewrite Hslo3; exact Hceil) ltac:(rewrite Hslo3; exact Hslo)
                                  ltac:(rewrite Hshi3; exact Hshi) HFr3 HG3 ltac:(unfold GROW_FR_B; grow_wr_tac U2'' U10'')
                                  (same_but_materialized_wvb_any _ mat6)) as (HK11 & HFR11 & HGR11).
                                (* v's bytes across runs 10 and 11: the state has no region over v. Every lia here is
                                   SCOPED (clear - ..): the unscoped one ran away in this context (measured 2026-10-29,
                                   three marker builds: it case-splits every disjunctive hypothesis) *)
                                assert (UO0k : bv_unsigned (ew E2 241) = VAL (A_OBJ 0))
                                  by (apply HEI2'; unfold A_OBJ, A_TEXT, A_LIM; clear; lia).
                                assert (UO12k : bv_unsigned (ew E2 253) = VAL (A_OBJ 12))
                                  by (apply HEI2'; unfold A_OBJ, A_TEXT, A_LIM; clear; lia).
                                assert (HV11 : forall a, v <= a < v + 56 ->
                                  aview SEGS (w_H W3) (ms_mem ms6) a = aview SEGS (w_H W3) mem3 a).
                                { intros a Ha. pose proof Hvstk as Hvs96. unfold GROW_FR_B in Hvs96.
                                  transitivity (aview SEGS (w_H W3) (ms_mem ms5) a).
                                  - apply aview_eq_of. apply HFr3. rewrite unsigned_lit_small by (clear - Ha Hv4096 Hvhi; lia).
                                    intros (r & Hin & Hr); vm_compute in Hin;
                                    repeat (destruct Hin as [Hin | Hin];
                                      [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
                                       rewrite ?U2'', ?UO0k, ?UO12k in Hr; clear - Ha Hvs96 Hr Hd0 Hd12; lia |]);
                                    contradiction.
                                  - apply aview_eq_of. apply HFr2. rewrite unsigned_lit_small by (clear - Ha Hv4096 Hvhi; lia).
                                    intros (r & Hin & Hr); vm_compute in Hin;
                                    repeat (destruct Hin as [Hin | Hin];
                                      [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
                                       rewrite ?U2'', ?UO0k, ?UO12k in Hr; clear - Ha Hvs96 Hr Hd0 Hd12; lia |]);
                                    contradiction. }
                                assert (HAGk : pj_agreeR SEGS (mrestrict (w_H W2) (ms_mem ms4)) (mrestrict (w_H W3) (ms_mem ms6))
                                  (fun x => v <= x < v + 56)).
                                { intros x Hx. split.
                                  - apply (mbyte_of_aview SEGS). rewrite (HV11 x Hx). exact (proj1 (HVKk x Hx)).
                                  - intros _. apply (apresent_writable SEGS).
                                    destruct (HVKk x Hx) as (_ & Hpr3). unfold apresent in *.
                                    split; [exact (proj1 Hpr3)|].
                                    destruct (proj2 Hpr3) as (b & Hb).
                                    destruct (mrestrict (w_H W3) (ms_mem ms6) (Z_to_bv 64 x)) as [b'|] eqn:Em;
                                      [exists b'; unfold mrestrict in Em; destruct (w_H W3 (Z_to_bv 64 x)); [discriminate | exact Em] |].
                                    exfalso. apply (HGR11 (Z_to_bv 64 x)); [| exact Em].
                                    unfold mrestrict. rewrite (proj1 Hpr3). rewrite Hb. discriminate. }
                                assert (HHDRk6 : pj_hdrR SEGS (mrestrict (w_H W3) (ms_mem ms6)) v ty num str res keys n cap)
                                  by exact (pj_hdrR_frame _ _ _ _ _ _ _ _ _ _ _ HHDRk4 HAGk).
                                (* a0 at the ret is s2 = -1 (i = 48 `li s2, -1`, callee-saved across the keys call) *)
                                assert (HA0m1k : getr (ms_regs ms6) 10%bv = w64 (-1)).
                                { pose proof (st_ok_pi_restrict_reg (w_H W3) E2 _ ms6 10%bv HS) as R10f.
                                  match type of R10f with _ = sv_denot _ ?t =>
                                    let t' := eval vm_compute in t in change t with t' in R10f end.
                                  rewrite R10f. apply bv_eq. vm_compute. reflexivity. }
                                (* the ledger at the ret: the keys callee's (over Lam2), its cells apart from grow's writes *)
                                assert (HLEDKEEPk : forall pk ct fl rn,
                                  prh_ledger B ly3 S3 Hp3 W3 mem3 ((res, 56 * cap2R cap) :: l1 ++ l2) pk ct fl rn most own ->
                                  prh_ledger B ly3 S3 Hp3 W3 (ms_mem ms6) ((res, 56 * cap2R cap) :: l1 ++ l2) pk ct fl rn most own).
                                { intros pk ct fl rn HL3'.
                                  apply (prh_ledger_keep B ly3 S3 Hp3 W3 mem3 (ms_mem ms6) _ pk ct fl rn most own HL3').
                                  intros a Hca.
                                  destruct (grow_cell_apart B ARx LAWS HPST GROW_FR_B ly2 S2 Hp2 W2 mem2 md2 _ _ _ _ _ _ _ regs e v a
                                    ltac:(unfold GROW_FR_B; lia) HAR2 HL2' HAT2 Hsp128 Hoff Hca) as (Ha64 & Hwa).
                                  apply HFR11. rewrite unsigned_lit_small by exact Ha64. exact Hwa. }
                                (* the new kids block across the keys call (it is not the keys block: G2k) and runs 10 / 11 *)
                                assert (HKBk : In (res - cf_head, 56 * cap2R cap + cf_head) (ablocks B ly3 S3) ->
                                  forall x, res - cf_head <= x < res - cf_head + req_size (56 * cap2R cap + cf_head) ->
                                  aview SEGS (w_H W3) (ms_mem ms6) x = aview SEGS (w_H W2) mem2 x).
                                { intros Hin3 x Hx. destruct (HNEW x Hx) as (Hx64 & Hxw).
                                  assert (Hneq : (res - cf_head, 56 * cap2R cap + cf_head) <> (keys - cf_head, 8 * cap + cf_head))
                                    by (intros Heq2; apply Hfresh; rewrite Heq2; exact HbyB12).
                                  pose proof (sep_blocks_x SEGS B ARx LAWS ly2 S2 Hp2 W2 _ _ _ _ _ _ HARc10 Hnew2 HbyS2 Hneq) as Hdj.
                                  unfold zdisjoint in Hdj; cbn [fst snd] in Hdj.
                                  assert (Hnf : ~ inFP (if keys =? 0 then [] else ablocks_fp [(keys - cf_head, 8 * cap + cf_head)]) x).
                                  { rewrite (proj2 (Z.eqb_neq keys 0) Hkeys0). intros (r & Hr & Hb). cbn [ablocks_fp map In] in Hr.
                                    destruct Hr as [<- | []]. cbn [fst snd] in Hb. clear - Hdj Hx Hb; lia. }
                                  assert (Hi : 0 <= x - (res - cf_head) < req_size (56 * cap2R cap + cf_head)) by (clear - Hx; lia).
                                  pose proof (G2k (res - cf_head) (56 * cap2R cap + cf_head) (x - (res - cf_head)) Hnew2 Hin3 Hi) as HG2k.
                                  replace (res - cf_head + (x - (res - cf_head))) with x in HG2k by ring.
                                  transitivity (aview SEGS (w_H W3) mem3 x);
                                    [apply aview_eq_of; apply HFR11; rewrite unsigned_lit_small by exact Hx64; exact Hxw |].
                                  rewrite (HG2k Hnf). apply aview_eq_of. apply HFR9. rewrite unsigned_lit_small by exact Hx64. exact Hxw. }
                                (* the shadow across runs 10 / 11: grow writes no shadow byte *)
                                assert (HSHK11 : forall s, SHADOW_OFF <= s < SHADOW_OFF + 2 ^ 44 ->
                                  aview SEGS (w_H W3) (ms_mem ms6) s = aview SEGS (w_H W3) mem3 s).
                                { intros s Hs. apply aview_eq_of. apply HFR11. rewrite unsigned_lit_small by (unfold SHADOW_OFF in *; lia).
                                  unfold grow_wr, GROW_FR_B. pose proof Hvstk as Hvs96. unfold GROW_FR_B in Hvs96.
                                  intros [Hw | [Hw | Hw]];
                                    [unfold SHADOW_OFF in *; lia | exact (Happ s ltac:(lia) Hs) | exact (Happ s ltac:(lia) Hs)]. }
                                (* the old keys bytes across runs 10 / 11 (a slot block, apart from grow's writes) *)
                                assert (HYB6 : bytes_at W3 mem3 keys yb -> bytes_at W3 (ms_mem ms6) keys yb).
                                { intros Hy3. unfold bytes_at in *. apply (garr8R_frame SEGS _ _ _ _ Hy3). intros x Hx. rewrite Hybl in Hx.
                                  destruct (grow_slot_apart B ARx LAWS GROW_FR_B ly S Hp W mem md Lam peak cnt fail ran most own regs e v
                                    ty kids keys n cap _ _ x ltac:(unfold GROW_FR_B; lia) ltac:(lia) HAR HLED HAT Hsp128 HSLOT HAP
                                    HinY ltac:(clear - Hx Hrq8 Hh0; lia)) as (Hx64 & Hxw).
                                  unfold mbyte. rewrite HFR11; [reflexivity|]. rewrite unsigned_lit_small by exact Hx64. exact Hxw. }
                                (* errno across runs 10 / 11: an image cell, off grow's frame and off v *)
                                assert (HERR11 : rd32 (aview SEGS (w_H W3) mem3) (as_errno B) 12 ->
                                  rd32 (aview SEGS (w_H W3) (ms_mem ms6)) (as_errno B) 12).
                                { intros Hr3 k Hk. rewrite <- (Hr3 k Hk).
                                  pose proof HENV as ((He0' & He4') & HEimg & _).
                                  assert (Himg : in_img SEGS (as_errno B + Z.of_nat k)) by (apply HEimg; lia).
                                  pose proof (pa_segs_low _ Himg) as Hl. unfold kLowMemEnd in Hl.
                                  apply aview_eq_of. apply HFR11. rewrite unsigned_lit_small by lia.
                                  unfold grow_wr, GROW_FR_B.
                                  intros [Hw | [Hw | Hw]];
                                    [lia | exact (Hoff (as_errno B + Z.of_nat k) ltac:(lia) Himg)
                                    | exact (Hoff (as_errno B + Z.of_nat k) ltac:(lia) Himg)]. }
                                eapply (grow_ret B ARx SK LAWS PL_prog_B (@STK_grow prh_img_B) W3 E2 _ ms6 _ e FP regs
                                  (growB_extra ty kids keys n cap) ly S Hp W mem md (grow_OR v) FP ly3 S3 Hp3 _ _
                                  ltac:(apply Z.leb_le; vm_compute; reflexivity) HS);
                                  [vm_compute; reflexivity | vm_compute; reflexivity | exact HA2 | vm_compute; reflexivity |
                                   vm_compute; reflexivity | exact Hra | exact HJ3 | exact HK11 | | ].
                                { rewrite HFP. intros a (r & Hr & Hb). exists r. split; [apply in_or_app; left; exact Hr | exact Hb]. }
                                intros mat'. cbv beta. unfold fQmn. cbv beta.
                                split; [|exact (PEND _ HPM)].
                                split; [exact HRL3|].
                                (* the hull use: the kids call's, then the keys call's (PwGrowG's grow_hull_two) *)
                                split; [rewrite Heq, (proj2 (Z.eqb_eq ty 6) Hty6); exact (grow_hull_two S S2 S3 cap HHU1 HHU2)|].
                                destruct HARMSk as [(Hk0k & Hcfk & Hres0k & HHp3 & Hab3 & Hyb3 & HL3)
                                                   | [(Hk0k & Hcfk & Hres0k & HPerm3 & Hab3 & Hyb3 & Hnullp3 & Herr3 & HL3) | HSUCk]].
                                ++++ (* the keys realloc is the CHOSEN FAILURE (arm 5) *)
                                     pose proof HL3 as (_ & _ & HFl3 & HPH3).
                                     pose proof (proj1 (Forall_forall _ _) HFl3 (res, 56 * cap2R cap) (or_introl eq_refl))
                                       as (_ & Hin3 & Hhp3 & _). cbn [fst snd] in Hin3, Hhp3.
                                     assert (HVISk : prhReader_vis W3 (ms_mem ms6) res (56 * cap2R cap)).
                                     { destruct (grow_vis_law B ARx LAWS ly3 S3 Hp3 W3 mem3 md3 res (56 * cap2R cap) HAR3 Hin3 Hhp3 Hn0)
                                         as (HRA3r & Hhull3).
                                       split.
                                       - intros x Hx. destruct (HRA3r x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
                                         rewrite <- Hs. unfold shadow_of_addr. apply HSHK11.
                                         assert (Hx8 : 0 <= x / 8 < 2 ^ 44)
                                           by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
                                         lia.
                                       - intros Hpos0 s Hs. rewrite HSHK11; [exact (Hhull3 Hpos0 s Hs)|]. unfold shadow_addr in Hs.
                                         assert (Hr8 : 512 <= res / 8) by (apply Z.div_le_lower_bound; lia).
                                         assert (Hr8' : (res + 56 * cap2R cap - 1) / 8 < 2 ^ 44 - 16)
                                           by (apply Z.div_lt_upper_bound; lia).
                                         pose proof (Z.div_mod (SHADOW_OFF + res / 8) 8 ltac:(lia)) as D1.
                                         pose proof (Z.mod_pos_bound (SHADOW_OFF + res / 8) 8 ltac:(lia)) as M1.
                                         pose proof (Z.div_mod (SHADOW_OFF + (res + 56 * cap2R cap - 1) / 8) 8 ltac:(lia)) as D2.
                                         pose proof (Z.mod_pos_bound (SHADOW_OFF + (res + 56 * cap2R cap - 1) / 8) 8 ltac:(lia)) as M2.
                                         lia. }
                                     assert (HKBret : bytes_at W3 (ms_mem ms6) res kb).
                                     { unfold bytes_at in *. apply (garr8R_frame SEGS _ _ _ _ HKB2). intros x Hx.
                                       assert (Hxr : res - cf_head <= x < res - cf_head + req_size (56 * cap2R cap + cf_head))
                                         by (rewrite Hkbl in Hx; rewrite Hc2 in *; clear - Hx Hrqn Hh0 Hcap; lia).
                                       apply (mbyte_of_aview SEGS).
                                       first [exact (HKBk Hin3 x Hxr) | exact (eq_sym (HKBk Hin3 x Hxr))]. }
                                     split; [rewrite (blocks_bytes_bsum B ly3 S3), Hab3, <- (blocks_bytes_bsum B ly2 S2), HBB2;
                                             unfold PRH_Charge.prh_held; destruct HHELDo as (-> & ->); clear - Hh0 Hcap; lia|].
                                     right; right; right; right; left.
                                     split; [exact Heq|]. split; [exact Hcf|]. split; [exact Hty6|]. split; [exact Hcfk|].
                                     split; [exact HA0m1k|].
                                     exists res, ((res, 56 * cap2R cap) :: l1 ++ l2).
                                     split; [exact Hres1|]. split; [exact Hres16|].
                                     split; [apply HSWAPk; [rewrite Hab3; exact HPb | exact HPH3]|].
                                     split; [rewrite <- Hmod2; exact (HLEDKEEPk _ _ _ _ HL3)|].
                                     split; [exact HKBret|]. split; [exact HVISk|]. split; [exact (HYB6 Hyb3)|].
                                     split; [exact HHDRk6|].
                                     (* outcomes [true; false]: the kids realloc's event, none for the NULL keys call *)
                                     replace (prhPg_evs (ty =? 6) n cap [true; false])
                                       with [PresetReqAt.HRe (56 * cap + cf_head) (56 * cap2R cap + cf_head)]
                                       by (unfold prhPg_evs, prhPg_ev; rewrite Heq, Z.ltb_irrefl, (proj2 (Z.eqb_eq ty 6) Hty6);
                                           cbn [nth andb]; rewrite (proj2 (Z.eqb_neq cap 0) Hcz); reflexivity).
                                     split.
                                     { pose proof (grow_live_trans S S2 S3 _ [] HLV2 (grow_live_keep B ly2 S2 ly3 S3 Hab3)) as Hq.
                                       rewrite app_nil_r in Hq. exact Hq. }
                                     intros sm x os i H0 hist Hpsm Hrun.
                                     destruct (HPOSR Hr0 Hkids0 sm x os i H0 hist Hpsm Hrun) as (h2 & Hp2').
                                     destruct (HPOS0k Hres0k sm x os _ H0 h2 Hp2' eq_refl) as (h3 & Hp3').
                                     exists h3. rewrite Nat.add_0_r in Hp3'. exact Hp3'.
                                ++++ (* the keys realloc is REFUSED (arm 6) *)
                                     pose proof HL3 as (_ & _ & HFl3 & HPH3).
                                     pose proof (proj1 (Forall_forall _ _) HFl3 (res, 56 * cap2R cap) (or_introl eq_refl))
                                       as (_ & Hin3 & Hhp3 & _). cbn [fst snd] in Hin3, Hhp3.
                                     assert (HVISk : prhReader_vis W3 (ms_mem ms6) res (56 * cap2R cap)).
                                     { destruct (grow_vis_law B ARx LAWS ly3 S3 Hp3 W3 mem3 md3 res (56 * cap2R cap) HAR3 Hin3 Hhp3 Hn0)
                                         as (HRA3r & Hhull3).
                                       split.
                                       - intros x Hx. destruct (HRA3r x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
                                         rewrite <- Hs. unfold shadow_of_addr. apply HSHK11.
                                         assert (Hx8 : 0 <= x / 8 < 2 ^ 44)
                                           by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
                                         lia.
                                       - intros Hpos0 s Hs. rewrite HSHK11; [exact (Hhull3 Hpos0 s Hs)|]. unfold shadow_addr in Hs.
                                         assert (Hr8 : 512 <= res / 8) by (apply Z.div_le_lower_bound; lia).
                                         assert (Hr8' : (res + 56 * cap2R cap - 1) / 8 < 2 ^ 44 - 16)
                                           by (apply Z.div_lt_upper_bound; lia).
                                         pose proof (Z.div_mod (SHADOW_OFF + res / 8) 8 ltac:(lia)) as D1.
                                         pose proof (Z.mod_pos_bound (SHADOW_OFF + res / 8) 8 ltac:(lia)) as M1.
                                         pose proof (Z.div_mod (SHADOW_OFF + (res + 56 * cap2R cap - 1) / 8) 8 ltac:(lia)) as D2.
                                         pose proof (Z.mod_pos_bound (SHADOW_OFF + (res + 56 * cap2R cap - 1) / 8) 8 ltac:(lia)) as M2.
                                         lia. }
                                     assert (HKBret : bytes_at W3 (ms_mem ms6) res kb).
                                     { unfold bytes_at in *. apply (garr8R_frame SEGS _ _ _ _ HKB2). intros x Hx.
                                       assert (Hxr : res - cf_head <= x < res - cf_head + req_size (56 * cap2R cap + cf_head))
                                         by (rewrite Hkbl in Hx; rewrite Hc2 in *; clear - Hx Hrqn Hh0 Hcap; lia).
                                       apply (mbyte_of_aview SEGS).
                                       first [exact (HKBk Hin3 x Hxr) | exact (eq_sym (HKBk Hin3 x Hxr))]. }
                                     split; [rewrite (blocks_bytes_bsum B ly3 S3), Hab3, <- (blocks_bytes_bsum B ly2 S2), HBB2;
                                             unfold PRH_Charge.prh_held; destruct HHELDo as (-> & ->); clear - Hh0 Hcap; lia|].
                                     right; right; right; right; right; left.
                                     split; [exact Heq|]. split; [exact Hcf|]. split; [exact Hty6|]. split; [exact Hcfk|].
                                     split; [exact HA0m1k|].
                                     exists res, ((res, 56 * cap2R cap) :: l1 ++ l2).
                                     split; [exact Hres1|]. split; [exact Hres16|].
                                     split; [apply HSWAPk; [rewrite Hab3; exact HPb | exact HPH3]|].
                                     split.
                                     { exists S2. exact Hnullp3. }
                                     split; [exact (HERR11 Herr3)|].
                                     (* THE OUTCOME EXCLUSION (the text :1000-1007): at the entry position the kids event is granted
                                        (the kids realloc's position transfer HPOSR to S2), and the keys realloc's outcome
                                        clause there gives a grant (cnt + 1 <> fail), but it returned NULL *)
                                     split.
                                     { intros sm x os i H0 hist Hpsm Hrun Hcons.
                                       rewrite Heq, (proj2 (Z.eqb_eq ty 6) Hty6) in Hrun, Hcons.
                                       pose proof (grow_run_split _ _ _ _ _ _ Hrun Hcons) as Hxs.
                                       destruct Hxs as (Hxr1 & Hxc1 & Hxk). destruct (Hxk eq_refl) as (Hxr2 & Hxc2).
                                       unfold prhPg_ev in Hxr1, Hxr2. rewrite (proj2 (Z.eqb_neq cap 0) Hcz) in Hxr1, Hxr2.
                                       destruct (HPOSR Hr0 Hkids0 sm x os i H0 hist Hpsm Hxr1) as (Hxh2 & Hxp2).
                                       destruct (HOUTRk Hk0k sm x os _ H0 Hxh2 Hxp2 Hxr2 Hxc2 Hcfk) as (Hxnz & _).
                                       exact (Hxnz Hres0k). }
                                     (* the ledger: fuzz_realloc's refused arm at the keys call, k = 8 cap (the text :1015-1019) *)
                                     split; [rewrite (proj2 (Z.eqb_neq cap 0) Hcz); exact (HLEDKEEPk _ _ _ _ HL3)|].
                                     split; [exact HKBret|]. split; [exact HVISk|]. split; [exact (HYB6 Hyb3)|].
                                     split; [exact HHDRk6|].
                                     (* outcomes [true; false]: the kids realloc's event, none for the NULL keys call *)
                                     replace (prhPg_evs (ty =? 6) n cap [true; false])
                                       with [PresetReqAt.HRe (56 * cap + cf_head) (56 * cap2R cap + cf_head)]
                                       by (unfold prhPg_evs, prhPg_ev; rewrite Heq, Z.ltb_irrefl, (proj2 (Z.eqb_eq ty 6) Hty6);
                                           cbn [nth andb]; rewrite (proj2 (Z.eqb_neq cap 0) Hcz); reflexivity).
                                     split.
                                     { pose proof (grow_live_trans S S2 S3 _ [] HLV2 (grow_live_keep B ly2 S2 ly3 S3 Hab3)) as Hq.
                                       rewrite app_nil_r in Hq. exact Hq. }
                                     intros sm x os i H0 hist Hpsm Hrun.
                                     destruct (HPOSR Hr0 Hkids0 sm x os i H0 hist Hpsm Hrun) as (h2 & Hp2').
                                     destruct (HPOS0k Hres0k sm x os _ H0 h2 Hp2' eq_refl) as (h3 & Hp3').
                                     exists h3. rewrite Nat.add_0_r in Hp3'. exact Hp3'.
                                ++++ (* the SUCCESS arm is out: its result is a block address, and a0 = 0 here *)
                                     exfalso.
                                     destruct HSUCk as (Hk0k & Hcfk & Hres1k & _ & l1k & l2k & _ & _ & _ & (b1k & b2k & _ & _ & HPbk) & _).
                                     match goal with H : branch_taken BC_EQ _ _ = true |- _ => rename H into Hbeq end.
                                     rewrite branch_eq_U in Hbeq. apply Z.eqb_eq in Hbeq. rewrite U_lit in Hbeq by lia.
                                     unfold U in Hbeq. rewrite <- R10r2, H10r2 in Hbeq. unfold w64 in Hbeq.
                                     assert (Hres2r : 0 <= res2 < 2 ^ 64).
                                     {
                                       assert (Hin2k : In (res2 - cf_head, 8 * cap2R cap + cf_head) (ablocks B ly3 S3))
                                         by (apply (Permutation_in _ (Permutation_sym HPbk)); left; reflexivity).
                                       destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR3 Hin2k) as (_ & _ & Hceilk & _).
                                       assert (Hrqk : 8 * cap2R cap + cf_head <= req_size (8 * cap2R cap + cf_head))
                                         by (unfold req_size; destruct (Z.eqb_spec (8 * cap2R cap + cf_head) 0); lia).
                                       lia. }
                                     rewrite unsigned_lit_small in Hbeq by lia. lia.
                           ---- (* a0 <> 0: the keys moved (arm 7): run 12 from i = 69 - the v + 32 shadow check (report
                                   site 0x87204), `sd a0, 0(s1)` (v + 32 := the new keys block), the v + 48 shadow check
                                   (report site 0x871f4), `li s2, 0`, `sd s6, 0(s0)` (v + 48 := 2 cap), the epilogue - to the
                                   ret with a0 = 0; both checks are decided inside the run by sh_ok growB_SH *)
                                match goal with H : branch_taken BC_EQ (sv_denot E2 _) _ = false |- _ => rename H into Hbne2 end.
                                assert (Hres_ne2 : bv_unsigned (getr regs3 10%bv) <> 0).
                                { rewrite branch_eq_U in Hbne2. apply Z.eqb_neq in Hbne2. rewrite U_lit in Hbne2 by lia.
                                  unfold U in Hbne2. rewrite <- R10r2 in Hbne2. exact Hbne2. }
                                rewrite H10r2 in Hres_ne2. unfold w64 in Hres_ne2.
                                destruct HARMSk as [(Hk0k & Hcfk & Hres0k & _) | [(Hk0k & Hcfk & Hres0k & _) | HSUCk]];
                                  [exfalso; apply Hres_ne2; rewrite Hres0k; reflexivity | exfalso; apply Hres_ne2; rewrite Hres0k; reflexivity |].
                                destruct HSUCk as (Hk0k & Hcfk & Hres1k & Hres16k & l1k & l2k & HLamk & Hnink & HHpk
                                  & (b1k & b2k & Hb12k & Hfreshk & HPbk) & (restk & Hrestlk & Hbresk) & HRAresk & Hhullk & HL3).
                                (* the node's place at the keys call's post state (grow_at_kept, the keys block for the kids one) *)
                                assert (HAPy : forall y, pj_holdsR (keys, 8 * cap) y -> ~ (v <= y < v + 56)).
                                { intros y Hy. apply (HAP (keys, 8 * cap) y); [| exact Hy].
                                  apply in_or_app; right; unfold keys_blkR.
                                  rewrite (proj2 (Z.eqb_neq cap 0) Hcz), (proj2 (Z.eqb_eq ty 6) Hty6). cbn [orb negb]. left; reflexivity. }
                                assert (HAT3 : prhReader_at B ly3 S3 ((res2, 8 * cap2R cap) :: l1k ++ l2k) regs e v 56).
                                { apply (grow_at_kept B ARx ly2 S2 Hp2 W2 (ms_mem ms4) _ ly3 S3 Hp3 W3 mem3 md3
                                    ((res, 56 * cap2R cap) :: l1 ++ l2) l1k l2k regs e v keys (8 * cap) (8 * cap2R cap) res2 b1k b2k
                                    HARc10 HAR3).
                                  - intros a kk Hin. pose proof HLEDk as (_ & _ & HFk & _).
                                    exact (proj1 (proj2 (proj1 (Forall_forall _ _) HFk (a, kk) Hin))).
                                  - exact HAT2.
                                  - exact HAPy.
                                  - exact HLamk.
                                  - exact Hb12k.
                                  - exact HPbk.
                                  - exact HFRS3.
                                  - exact HFA3.
                                  - exact Hfreshk. }
                                (* v's shadow: at the keys call memory (grow writes none), across the keys call
                                   (grow_v_shadow2), across run 10 (it writes only the frame) *)
                                assert (HRA4 : range_addressable (aview SEGS (w_H W2) (ms_mem ms4)) SHADOW_OFF v 56).
                                { intros x Hx. destruct (HRA2 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
                                  rewrite <- Hs. unfold shadow_of_addr.
                                  assert (Hx8 : 0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
                                  apply aview_eq_of. apply HFR9. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
                                  unfold grow_wr, GROW_FR_B. pose proof Hvstk as Hvs96. unfold GROW_FR_B in Hvs96.
                                  intros [Hw | [Hw | Hw]];
                                    [unfold SHADOW_OFF in *; lia
                                    | exact (Happ (SHADOW_OFF + x / 8) ltac:(lia) ltac:(lia))
                                    | exact (Happ (SHADOW_OFF + x / 8) ltac:(lia) ltac:(lia))]. }
                                assert (HRA3 : range_addressable (aview SEGS (w_H W3) mem3) SHADOW_OFF v 56).
                                { apply (grow_v_shadow2 B ARx SK LAWS ly2 S2 Hp2 W2 (ms_mem ms4) _ ly3 S3 Hp3 W3 mem3 md3 _ _ _ _ _ _ _
                                    regs e v _ _ _ k3 HARc10 HAR3 HL3 HAT3 ltac:(rewrite Hslo3; lia) ltac:(rewrite Hshi3; lia) HRA4 HJ1k).
                                  intros a (r & Hr & Hlo & Hhi). rewrite (proj2 (Z.eqb_neq keys 0) Hkeys0) in Hr.
                                  cbn [ablocks_fp map In] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Hlo, Hhi.
                                  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HARc10 HbyS2) as (_ & _ & _ & Happk & _).
                                  exact (in_app_addr _ _ a Happk ltac:(lia)). }
                                assert (HV10all : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - GROW_FR_B <= x < spZ regs) ->
                                  aview SEGS (w_H W3) (ms_mem ms5) x = aview SEGS (w_H W3) mem3 x).
                                { intros x Hx Hnf. unfold GROW_FR_B in Hnf.
                                  apply aview_eq_of. apply HFr2. rewrite unsigned_lit_small by lia.
                                  intros (r & Hin & Hr); vm_compute in Hin;
                                  repeat (destruct Hin as [Hin | Hin];
                                    [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U2'' in Hr; lia |]);
                                  contradiction. }
                                assert (HRA5k : range_addressable (aview SEGS (w_H W3) (ms_mem ms5)) SHADOW_OFF v 56).
                                { intros x Hx. destruct (HRA3 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
                                  rewrite <- Hs. unfold shadow_of_addr.
                                  assert (Hx8 : 0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
                                  apply HV10all; unfold GROW_FR_B, SHADOW_OFF in *; lia. }
                                assert (SHOK3 : sh_ok SEGS growB_Bx growB_SH E2 (mrestrict (w_H W3) (ms_mem ms5))).
                                { unfold sh_ok, growB_SH. apply Forall_cons; [|apply Forall_nil]. split.
                                  - unfold growB_Bx. cbn [she_m she_lo she_hi].
                                    rewrite !U_SOff, U32'', U10'', !Z.add_0_r, !zcanon_id by (unfold M64, SHADOW_OFF; lia).
                                    change (rd_of SEGS (mrestrict (w_H W3) (ms_mem ms5))) with (aview SEGS (w_H W3) (ms_mem ms5)).
                                    exact HRA5k.
                                  - unfold app_apart, growB_Bx. cbn [she_m she_lo she_hi]. intros a Ha.
                                    rewrite !U_SOff, U32'', U10'', !Z.add_0_r, !zcanon_id in * by (unfold M64, SHADOW_OFF; lia).
                                    apply Happ. lia. }
                                (* the node's two regions back at the memory after run 10 (v + 24 = atom 42, the new kids block) *)
                                assert (HVV10 : forall a k w, v <= a -> a + Z.of_nat k <= v + 56 ->
                                  val_mem SEGS (mrestrict (w_H W2) (ms_mem ms4)) a k w ->
                                  val_mem SEGS (mrestrict (w_H W3) (ms_mem ms5)) a k w).
                                { intros a k w H1 H2 Hv j Hj. specialize (Hv j Hj).
                                  rewrite (mbyte_of_aview SEGS (w_H W2) (w_H W3) (ms_mem ms4) (ms_mem ms5) (a + Z.of_nat j)); [exact Hv|].
                                  pose proof Hvstk as Hvs96. unfold GROW_FR_B in Hvs96.
                                  rewrite (HV10all (a + Z.of_nat j) ltac:(lia) ltac:(unfold GROW_FR_B; lia)).
                                  exact (proj1 (HVKk (a + Z.of_nat j) ltac:(lia))). }
                                assert (HPR10 : forall a, v <= a < v + 56 -> apresent (w_H W3) (ms_mem ms5) a).
                                { intros a Ha. destruct (proj2 (HVKk a Ha)) as (Hh & b & Hb). split; [exact Hh|].
                                  destruct (ms_mem ms5 (Z_to_bv 64 a)) as [b'|] eqn:Eb; [exists b'; reflexivity|].
                                  exfalso. apply (HG2 (Z_to_bv 64 a)); unfold mrestrict; rewrite Hh; [rewrite Hb; discriminate | exact Eb]. }
                                pose proof HHDRk4 as (_ & (Hty4 & Vty4) & _ & _ & (Hkids4 & Vkids4) & (Hkeys4 & Vkeys4) & (Hn4 & Vn4)
                                  & (Hcap4 & Vcap4)).
                                assert (UO0'' : bv_unsigned (ew E2 (A_OBJ 0)) = VAL (A_OBJ 0)) by (apply HEI2'; unfold A_OBJ, A_TEXT, A_LIM; lia).
                                assert (UO12'' : bv_unsigned (ew E2 (A_OBJ 12)) = VAL (A_OBJ 12)) by (apply HEI2'; unfold A_OBJ, A_TEXT, A_LIM; lia).
                                assert (UO0y : bv_unsigned (ew E2 241) = VAL (A_OBJ 0)) by exact UO0''.
                                assert (UO12y : bv_unsigned (ew E2 253) = VAL (A_OBJ 12)) by exact UO12''.
                                assert (RBok3 : region_ok SEGS E2 (mrestrict (w_H W3) (ms_mem ms5)) growB_vB).
                                { unfold growB_vB, region_ok.
                                  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U10''.
                                  split; [lia|]. split; [lia|].
                                  split; [intros o Ho; apply (apresent_writable SEGS); apply HPR10; lia|].
                                  repeat apply Forall_cons; try apply Forall_nil.
                                  - apply (chunk_ok_val SEGS E2 _ v 40 8 (SOff 36 0) n);
                                      [cbn [sv_denot]; rewrite U36'', Z.add_0_r; reflexivity | exact Hn4 | lia | apply HVV10; [lia | cbn; lia | exact Vn4]].
                                  - apply (chunk_ok_val SEGS E2 _ v 48 8 (SOff 37 0) cap);
                                      [cbn [sv_denot]; rewrite U37'', Z.add_0_r; reflexivity | exact Hcap4 | lia | apply HVV10; [lia | cbn; lia | exact Vcap4]]. }
                                assert (RAok3 : region_ok SEGS E2 (mrestrict (w_H W3) (ms_mem ms5)) growB_vA2).
                                { unfold growB_vA2, region_ok.
                                  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U10''.
                                  split; [lia|]. split; [lia|].
                                  split; [intros o Ho; apply (apresent_writable SEGS); apply HPR10; lia|].
                                  repeat apply Forall_cons; try apply Forall_nil.
                                  - apply (chunk_ok_val SEGS E2 _ v 0 4 (SOff 33 0) ty);
                                      [cbn [sv_denot]; rewrite U33'', Z.add_0_r; reflexivity | exact Hty4 | lia |].
                                    rewrite Z.add_0_r. apply HVV10; [lia | cbn; lia | exact Vty4].
                                  - apply (chunk_ok_val SEGS E2 _ v 24 8 (SOff 42 0) res);
                                      [cbn [sv_denot]; rewrite U42'', Z.add_0_r; reflexivity | exact Hkids4 | lia
                                      | apply HVV10; [lia | cbn; lia | exact Vkids4]].
                                  - apply (chunk_ok_val SEGS E2 _ v 32 8 (SOff 35 0) keys);
                                      [cbn [sv_denot]; rewrite U35'', Z.add_0_r; reflexivity | exact Hkeys4 | lia
                                      | apply HVV10; [lia | cbn; lia | exact Vkeys4]]. }
                                lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
                                  pose proof (st_ok_pi_add_region E2 ssx _ growB_vB HS ltac:(vm_compute; reflexivity) RBok3) as HS3 end.
                                match type of HS3 with ?P -> _ => assert (HD : P); [|specialize (HS3 HD); clear HD] end.
                                { apply all_disjoint_of_extents.
                    (* the region list by a VM-checked equation: `vm_compute ss_mem` recorded no cast, and the kernel's
                       lazy re-check of it made Qed run past 50 min (measured by bisection, 2026-10-29) *)
                    lazymatch goal with |- zall_disjoint _ (map _ ?rs) =>
                      let rs' := eval vm_compute in rs in replace rs with rs' by (vm_compute; reflexivity) end. unfold growB_vB.
                                  cbn [map zall_disjoint]. unfold extent_of_region, zdisj.
                                  cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val].
                                  rewrite ?U2'', ?U10'', ?UO0'', ?UO12'', ?UO0y, ?UO12y. pose proof Hvstk as Hvs96. unfold GROW_FR_B in Hvs96.
                                  repeat split; lia. }
                                clear HS. rename HS3 into HS.
                                lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
                                  pose proof (st_ok_pi_add_region E2 ssx _ growB_vA2 HS ltac:(vm_compute; reflexivity) RAok3) as HS3 end.
                                match type of HS3 with ?P -> _ => assert (HD : P); [|specialize (HS3 HD); clear HD] end.
                                { apply all_disjoint_of_extents.
                    (* the region list by a VM-checked equation: `vm_compute ss_mem` recorded no cast, and the kernel's
                       lazy re-check of it made Qed run past 50 min (measured by bisection, 2026-10-29) *)
                    lazymatch goal with |- zall_disjoint _ (map _ ?rs) =>
                      let rs' := eval vm_compute in rs in replace rs with rs' by (vm_compute; reflexivity) end. unfold growB_vA2, growB_vB.
                                  cbn [map zall_disjoint]. unfold extent_of_region, zdisj.
                                  cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val].
                                  rewrite ?U2'', ?U10'', ?UO0'', ?UO12'', ?UO0y, ?UO12y. pose proof Hvstk as Hvs96. unfold GROW_FR_B in Hvs96.
                                  repeat split; lia. }
                                clear HS. rename HS3 into HS.
                                (* run 12 *)
                                pose proof HJ3 as (HARc12 & _).
                                paj_run_tok_x_inv (RUNBP PM PLAW) HS HJ3 SHOK3 HPM growB_Bspan.
                                { apply (grow_awr_ok_fr _ _ (@STK_grow prh_img_B) GROW_FR_B e (spZ regs) FP _ _ S ly3 v);
                                    [unfold GROW_FR_B; lia | exact FS | exact He0 | | | ].
                                  - unfold GROW_FR_B; grow_wr_tac U2'' U10''.
                                  - intros a Ha. rewrite HFP. exact (grow_FP_v v ty kids keys cap a Ha).
                                  - exact HVL3'. }
                                match type of HS with st_ok_pi _ _ E2 _ _ => idtac | _ => fail "run 12 changed the environment" end.
                                destruct (grow_stretch B ARx SK LAWS (@STK_grow prh_img_B) GROW_FR_B E2 _ W3 mem3 (ms_mem ms5)
                                  _ (ms_mem ms6) _ (spZ regs) v FP ly S Hp W mem md ly3 S3 Hp3 ltac:(unfold GROW_FR_B; lia) FS
                                  HK10 HFR10 HGR10 HAR HARc12 ltac:(rewrite Hslo3; exact Hceil) ltac:(rewrite Hslo3; exact Hslo)
                                  ltac:(rewrite Hshi3; exact Hshi) HFr3 HG3 ltac:(unfold GROW_FR_B; grow_wr_tac U2'' U10'')
                                  (same_but_materialized_wvb_any _ mat6)) as (HK12 & HFR12 & HGR12).
                                (* the ret: a0 = s2 = 0 (i = 74 `li s2, 0`, i = 76 `mv a0, s2`) *)
                                assert (HA007 : getr (ms_regs ms6) 10%bv = w64 0).
                                { pose proof (st_ok_pi_restrict_reg (w_H W3) E2 _ ms6 10%bv HS) as R10f.
                                  match type of R10f with _ = sv_denot _ ?t =>
                                    let t' := eval vm_compute in t in change t with t' in R10f end.
                                  rewrite R10f. reflexivity. }
                                (* the node's three written fields at the ret, off its two regions (v + 24 = atom 42 = the kids
                                   block, v + 32 = atom 58 = the keys block, v + 48 = cap << 1) *)
                                assert (RAf7 : region_ok SEGS E2 (mrestrict (w_H W3) (ms_mem ms6)) (YP09.mkRegion (Some 10%nat) 0 40 24 40
                                  [YP09.mkChunk 32 (CVal 8 (SOff 58 0)); YP09.mkChunk 0 (CVal 4 (SOff 33 0));
                                   YP09.mkChunk 24 (CVal 8 (SOff 42 0))])).
                                { match type of HS with st_ok_pi _ _ _ ?ss _ =>
                                    exact (st_ok_region_nth SEGS E2 (abs_ss VAL ss) (restrict (w_H W3) ms6) 0
                                      (YP09.mkRegion (Some 10%nat) 0 40 24 40
                                        [YP09.mkChunk 32 (CVal 8 (SOff 58 0)); YP09.mkChunk 0 (CVal 4 (SOff 33 0));
                                         YP09.mkChunk 24 (CVal 8 (SOff 42 0))]) HS ltac:(vm_compute; reflexivity)) end. }
                                assert (RBf7 : region_ok SEGS E2 (mrestrict (w_H W3) (ms_mem ms6)) (YP09.mkRegion (Some 10%nat) 40 56 48 56
                                  [YP09.mkChunk 48 (CVal 8 (SAlu ALU_SLL (SOff 37 0) (SLit 1))); YP09.mkChunk 40 (CVal 8 (SOff 36 0))])).
                                { match type of HS with st_ok_pi _ _ _ ?ss _ =>
                                    exact (st_ok_region_nth SEGS E2 (abs_ss VAL ss) (restrict (w_H W3) ms6) 1
                                      (YP09.mkRegion (Some 10%nat) 40 56 48 56
                                        [YP09.mkChunk 48 (CVal 8 (SAlu ALU_SLL (SOff 37 0) (SLit 1)));
                                         YP09.mkChunk 40 (CVal 8 (SOff 36 0))]) HS ltac:(vm_compute; reflexivity)) end. }
                                assert (Hin2k : In (res2 - cf_head, 8 * cap2R cap + cf_head) (ablocks B ly3 S3))
                                  by (apply (Permutation_in _ (Permutation_sym HPbk)); left; reflexivity).
                                destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR3 Hin2k) as (_ & _ & Hnck & _).
                                assert (Hrqk : 8 * cap2R cap + cf_head <= req_size (8 * cap2R cap + cf_head))
                                  by (unfold req_size; destruct (Z.eqb_spec (8 * cap2R cap + cf_head) 0) as [Hq | Hq];
                                      clear - Hq Hh0 Hc2 Hcap; lia).
                                pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
                                assert (Hres2b : 0 <= res2 < 2 ^ 64)
                                  by lia.
                                assert (U58 : sv_denot E2 (SOff 58 0) = Z_to_bv 64 res2)
                                  by (rewrite <- R10r2, H10r2; reflexivity).
                                assert (U2cap7 : sv_denot E2 (SAlu ALU_SLL (SOff 37 0) (SLit 1)) = Z_to_bv 64 (cap2R cap)).
                                { apply bv_eq. rewrite (unsigned_lit_small (cap2R cap)) by (clear - Hc2 Hcap Hcap54; lia).
                                  change (bv_unsigned (sv_denot E2 (SAlu ALU_SLL (SOff 37 0) (SLit 1))))
                                    with (U E2 (SAlu ALU_SLL (SOff 37 0) (SLit 1))).
                                  rewrite U_SAlu, U_SOff, U37'', U_lit by (clear - Hcap Hcap54; lia). rewrite Z.add_0_r. cbn [zalu_raw].
                                  rewrite (zcanon_id cap) by (unfold M64; clear - Hcap Hcap54; lia). change (Z.land 1 63) with 1.
                                  rewrite Z.shiftl_mul_pow2 by lia. rewrite zcanon_id by (unfold M64; clear - Hcap Hcap54; lia).
                                  clear - Hc2; lia. }
                                assert (RkF : rd_u64 SEGS (mrestrict (w_H W3) (ms_mem ms6)) (v + 24) res).
                                { split; [lia|].
                                  exact (field_of_region SEGS E2 _ 10 v _ 0 40 24 40 24 8 (SOff 42 0) res RAf7 U10'' ltac:(cbn; tauto)
                                    ltac:(cbn [sv_denot]; rewrite U42'', Z.add_0_r; reflexivity)
                                    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)). }
                                assert (RyF : rd_u64 SEGS (mrestrict (w_H W3) (ms_mem ms6)) (v + 32) res2).
                                { split; [exact Hres2b|].
                                  exact (field_of_region SEGS E2 _ 10 v _ 0 40 24 40 32 8 (SOff 58 0) res2 RAf7 U10'' ltac:(cbn; tauto)
                                    U58 ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)). }
                                assert (RcF : rd_u64 SEGS (mrestrict (w_H W3) (ms_mem ms6)) (v + 48) (cap2R cap)).
                                { split; [clear - Hc2 Hcap Hcap54; lia|].
                                  exact (field_of_region SEGS E2 _ 10 v _ 40 56 48 56 48 8 (SAlu ALU_SLL (SOff 37 0) (SLit 1)) (cap2R cap)
                                    RBf7 U10'' ltac:(cbn; tauto) U2cap7 ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia)
                                    ltac:(cbn; lia)). }
                                (* the node's header at the keys call's post memory: v's bytes are the keys call state's (HVKk) *)
                                assert (HAG3 : pj_agreeR SEGS (mrestrict (w_H W2) (ms_mem ms4)) (mrestrict (w_H W3) mem3)
                                  (fun x => v <= x < v + 56)).
                                { intros x Hx. split.
                                  - apply (mbyte_of_aview SEGS). exact (proj1 (HVKk x Hx)).
                                  - intros _. apply (apresent_writable SEGS). exact (proj2 (HVKk x Hx)). }
                                assert (HHDR3 : pj_hdrR SEGS (mrestrict (w_H W3) mem3) v ty num str res keys n cap)
                                  by exact (pj_hdrR_frame _ _ _ _ _ _ _ _ _ _ _ HHDRk4 HAG3).
                                (* the keys call's new block, apart from grow's writes (PwGrowG's grow_new_apart) *)
                                assert (HNEWk : forall x, res2 - cf_head <= x < res2 - cf_head + req_size (8 * cap2R cap + cf_head) ->
                                  0 <= x < 2 ^ 64 /\ ~ grow_wr GROW_FR_B (spZ regs) v x)
                                  by (intros x Hx; exact (grow_new_apart B ARx LAWS GROW_FR_B ly2 S2 Hp2 W2 (ms_mem ms4) _ ly3 S3 Hp3 W3
                                        mem3 md3 ((res, 56 * cap2R cap) :: l1 ++ l2) (Z.max peak (Ledger.lsum ((res, 56 * cap2R cap) :: l1 ++ l2)))
                                        (cnt + 1) fail ran most own l1k l2k regs e v keys (8 * cap) (8 * cap2R cap) res2 b1k b2k x
                                        ltac:(unfold GROW_FR_B; lia) HARc10 HAR3 HLEDk HAT2 Hsp128 HAPy HLamk Hb12k HPbk HFRS3 HFA3
                                        Hfreshk Hx)).
                                (* the new kids block's bytes at the keys call's post memory: apart from grow's writes (HNEW) and
                                   from the keys call's footprint (the old keys block), so the keys call kept them (G2k) *)
                                assert (Hneq7 : (res - cf_head, 56 * cap2R cap + cf_head) <> (keys - cf_head, 8 * cap + cf_head))
                                  by (intros Heq2; apply Hfresh; rewrite Heq2; exact HbyB12).
                                assert (Hin3 : In (res - cf_head, 56 * cap2R cap + cf_head) (ablocks B ly3 S3)).
                                { apply (Permutation_in _ (Permutation_sym HPbk)). right.
                                  assert (Hq : In (res - cf_head, 56 * cap2R cap + cf_head) (b1k ++ (keys - cf_head, 8 * cap + cf_head) :: b2k))
                                    by (rewrite <- Hb12k; exact Hnew2).
                                  apply in_app_or in Hq as [Hq | [Hq | Hq]]; apply in_or_app;
                                    [left; exact Hq | exfalso; apply Hneq7; symmetry; exact Hq | right; exact Hq]. }
                                assert (HKB3 : bytes_at W3 mem3 res kb).
                                { unfold bytes_at in *. apply (garr8R_frame SEGS _ _ _ _ HKB2). intros x Hx.
                                  assert (Hxr : res - cf_head <= x < res - cf_head + req_size (56 * cap2R cap + cf_head))
                                    by (rewrite Hkbl in Hx; rewrite Hc2 in *; clear - Hx Hrqn Hh0 Hcap; lia).
                                  destruct (HNEW x Hxr) as (Hx64 & Hxw).
                                  pose proof (sep_blocks_x SEGS B ARx LAWS ly2 S2 Hp2 W2 _ _ _ _ _ _ HARc10 Hnew2 HbyS2 Hneq7) as Hdj.
                                  unfold zdisjoint in Hdj; cbn [fst snd] in Hdj.
                                  assert (Hnf : ~ inFP (if keys =? 0 then [] else ablocks_fp [(keys - cf_head, 8 * cap + cf_head)]) x).
                                  { rewrite (proj2 (Z.eqb_neq keys 0) Hkeys0). intros (r & Hr & Hb). cbn [ablocks_fp map In] in Hr.
                                    destruct Hr as [<- | []]. cbn [fst snd] in Hb. clear - Hdj Hxr Hb; lia. }
                                  assert (Hi : 0 <= x - (res - cf_head) < req_size (56 * cap2R cap + cf_head)) by (clear - Hxr; lia).
                                  pose proof (G2k (res - cf_head) (56 * cap2R cap + cf_head) (x - (res - cf_head)) Hnew2 Hin3 Hi) as HG2k.
                                  replace (res - cf_head + (x - (res - cf_head))) with x in HG2k by ring.
                                  apply (mbyte_of_aview SEGS).
                                  rewrite (HG2k Hnf). apply aview_eq_of. apply HFR9. rewrite unsigned_lit_small by exact Hx64. exact Hxw. }
                                (* the new keys block's bytes: the old keys bytes at its head (the callee's firstn (min k n) old) *)
                                assert (HYB3 : bytes_at W3 mem3 res2 yb).
                                { assert (Hmin : Z.min (8 * cap) (8 * cap2R cap) = 8 * cap) by (rewrite Hc2; clear - Hcap; lia).
                                  rewrite Hmin, <- Hybl, Nat2Z.id, firstn_all in Hbresk.
                                  unfold bytes_at in *. apply garr8_app in Hbresk as (Hb0 & _). exact Hb0. }
                                (* the live requests and the position over the two calls' events (outcomes [true; true]) *)
                                assert (HEVS7 : prhPg_evs (ty =? 6) n cap [true; true] =
                                  [PresetReqAt.HRe (56 * cap + cf_head) (56 * cap2R cap + cf_head);
                                   PresetReqAt.HRe (8 * cap + cf_head) (8 * cap2R cap + cf_head)])
                                  by (unfold prhPg_evs, prhPg_ev; rewrite Heq, Z.ltb_irrefl, (proj2 (Z.eqb_eq ty 6) Hty6);
                                      cbn [nth andb]; rewrite (proj2 (Z.eqb_neq cap 0) Hcz); reflexivity).
                                assert (HLVF : Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S3))
                                  (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
                                     (prhPg_evs (ty =? 6) n cap [true; true]))).
                                { rewrite HEVS7.
                                  change [PresetReqAt.HRe (56 * cap + cf_head) (56 * cap2R cap + cf_head);
                                          PresetReqAt.HRe (8 * cap + cf_head) (8 * cap2R cap + cf_head)]
                                    with ([PresetReqAt.HRe (56 * cap + cf_head) (56 * cap2R cap + cf_head)] ++
                                          [PresetReqAt.HRe (8 * cap + cf_head) (8 * cap2R cap + cf_head)]).
                                  exact (grow_live_trans S S2 S3 _ _ HLV2
                                    (grow_live_re B ly2 S2 ly3 S3 b1k b2k keys (8 * cap) res2 (8 * cap2R cap) Hb12k HPbk)). }
                                assert (HPOSF : forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
                                  (i : nat) (H0 : list Z) (hist : list YG00.chunk),
                                  PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
                                  PRH_Base.prh_run_at sm x os i (prhPg_evs (ty =? 6) n cap [true; true]) ->
                                  exists hist', PresetRoomPos.iface_room_pos sm x os
                                    (i + length (prhPg_evs (ty =? 6)%Z n cap [true; true]))%nat H0 hist' S3).
                                { intros sm x os i H0 hist Hpsm Hrun. rewrite HEVS7 in Hrun |- *.
                                  change [PresetReqAt.HRe (56 * cap + cf_head) (56 * cap2R cap + cf_head);
                                          PresetReqAt.HRe (8 * cap + cf_head) (8 * cap2R cap + cf_head)]
                                    with ([PresetReqAt.HRe (56 * cap + cf_head) (56 * cap2R cap + cf_head)] ++
                                          [PresetReqAt.HRe (8 * cap + cf_head) (8 * cap2R cap + cf_head)]) in Hrun.
                                  apply PRH_Base.prh_run_at_app_iff in Hrun as (Hr1 & Hr2).
                                  destruct (HPOSR Hr0 Hkids0 sm x os i H0 hist Hpsm Hr1) as (h2 & Hp2').
                                  destruct (HPOSRk ltac:(clear - Hres1k Hh0; lia) Hkeys0 sm x os _ H0 h2 Hp2' Hr2) as (h3 & Hp3').
                                  exists h3. replace (i + length [PresetReqAt.HRe (56 * cap + cf_head) (56 * cap2R cap + cf_head);
                                    PresetReqAt.HRe (8 * cap + cf_head) (8 * cap2R cap + cf_head)])%nat
                                    with (i + length [PresetReqAt.HRe (56 * cap + cf_head) (56 * cap2R cap + cf_head)] +
                                          length [PresetReqAt.HRe (8 * cap + cf_head) (8 * cap2R cap + cf_head)])%nat
                                    by (cbn [length]; lia).
                                  exact Hp3'. }
                                (* the keys ledger at S3 in the segment's form *)
                                assert (HL3s : prh_ledger B ly3 S3 Hp3 W3 mem3 ((res2, 8 * cap2R cap) :: l1k ++ l2k)
                                  (Z.max (Z.max peak (Ledger.lsum ((res, 56 * cap2R cap) :: l1 ++ l2)))
                                     (Ledger.lsum ((res2, 8 * cap2R cap) :: l1k ++ l2k)))
                                  (cnt + 2) fail ran most own).
                                { replace (Ledger.lsum ((res2, 8 * cap2R cap) :: l1k ++ l2k))
                                    with (Ledger.lsum (l1k ++ l2k) + 8 * cap2R cap) by (cbn [Ledger.lsum]; clear; lia).
                                  rewrite <- Hmod2. exact HL3. }
                                (* the blocks' bytes: the keys block grew by 8 cap *)
                                assert (HBB3 : blocks_bytes S3 = blocks_bytes S2 + 8 * cap).
                                { rewrite (blocks_bytes_bsum B ly3 S3), (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ HPbk), Hb12k.
                                  rewrite bsum_cons, !bsum_app, bsum_cons. cbn [fst snd]. rewrite Hc2. clear; lia. }
                                (* the hidden heads: each call's old head was in the head set (the ledger's Hp permutation) *)
                                assert (HhpK : In (kids - cf_head) Hp).
                                { pose proof HLED as (_ & _ & _ & HPH). apply (Permutation_in _ (Permutation_sym HPH)).
                                  apply in_map_iff. exists (kids, 56 * cap). split; [reflexivity|].
                                  rewrite HLam. apply in_or_app; right; left; reflexivity. }
                                assert (HhpY : In (keys - cf_head) Hp2).
                                { pose proof HLEDk as (_ & _ & _ & HPH). apply (Permutation_in _ (Permutation_sym HPH)).
                                  apply in_map_iff. exists (keys, 8 * cap). split; [reflexivity|].
                                  rewrite HLamk. apply in_or_app; right; left; reflexivity. }
                                eapply (grow_ret B ARx SK LAWS PL_prog_B (@STK_grow prh_img_B) W3 E2 _ ms6 _ e FP regs
                                  (growB_extra ty kids keys n cap) ly S Hp W mem md (grow_OR v) FP ly3 S3 Hp3 _ _
                                  ltac:(apply Z.leb_le; vm_compute; reflexivity) HS);
                                  [vm_compute; reflexivity | vm_compute; reflexivity | exact HA2 | vm_compute; reflexivity |
                                   vm_compute; reflexivity | exact Hra | exact HJ3 | exact HK12 | | ].
                                { rewrite HFP. intros a (r & Hr & Hb). exists r. split; [apply in_or_app; left; exact Hr | exact Hb]. }
                                intros mat'. cbv beta. unfold fQmn. cbv beta.
                                split; [|exact (PEND _ HPM)].
                                split; [exact HRL3|].
                                (* the hull use: the kids call's, then the keys call's (PwGrowG's grow_hull_two) *)
                                split; [rewrite Heq, (proj2 (Z.eqb_eq ty 6) Hty6); exact (grow_hull_two S S2 S3 cap HHU1 HHU2)|].
                                (* THE ARM-7 SEGMENT (PwGrowBArm7.v) at Lr := l1 ++ l2, blr := b1 ++ b2, hlr := Hp without the old
                                   kids head, Lr2 := l1k ++ l2k, blr2 := b1k ++ b2k, hlr2 := Hp2 without the old keys head *)
                                assert (EK : kids_blkR kids cap = [(kids, 56 * cap)])
                                  by (unfold kids_blkR; rewrite (proj2 (Z.eqb_neq cap 0) Hcz); reflexivity).
                                assert (EY : keys_blkR ty keys cap = [(keys, 8 * cap)])
                                  by (unfold keys_blkR; rewrite (proj2 (Z.eqb_neq cap 0) Hcz), (proj2 (Z.eqb_eq ty 6) Hty6); reflexivity).
                                destruct (growB_seg_arm7 B ARx LAWS HPST ly S Hp regs e v ty num str kids keys n cap kb yb Lam peak cnt fail ran
                                  most own res (l1 ++ l2) (b1 ++ b2) (remove Z.eq_dec (kids - cf_head) Hp) ly2 S2 Hp2 W2 (ms_mem ms4) _ _ _ _
                                  res2 (l1k ++ l2k) (b1k ++ b2k) (remove Z.eq_dec (keys - cf_head) Hp2) ly3 S3 Hp3 W3 mem3 md3
                                  (ms_regs ms6) (ms_mem ms6)
                                  Heq ltac:(clear - Hcap; lia) ltac:(clear - Heq Hncap Hcap Hc2 Hnc Hrqn Hn4096 AC1 Hh0; lia)
                                  Hcf Hty6 Hcfk (proj2 (proj2 (proj2 HSLOT)))
                                  ltac:(rewrite EK; unfold prhReader_ab; cbn [map fst snd app]; rewrite Hb12;
                                        apply Permutation_sym, Permutation_middle)
                                  HPb
                                  ltac:(rewrite EK; unfold prhReader_hd; cbn [map fst app];
                                        exact (perm_remove_nodup Hp _ (ledger_hp_nodup B _ _ _ _ _ _ _ _ _ _ _ _ HLED) HhpK))
                                  HHp
                                  ltac:(rewrite EK, HLam; cbn [app]; apply Permutation_sym, Permutation_middle)
                                  Hres1 Hres16 HLEDk ltac:(rewrite HBB2, Hc2; clear - Hh0; lia)
                                  ltac:(rewrite EY, HLamk; cbn [app]; apply Permutation_sym, Permutation_middle)
                                  ltac:(rewrite EY; unfold prhReader_ab; cbn [map fst snd app]; rewrite Hb12k;
                                        apply Permutation_sym, Permutation_middle)
                                  HPbk
                                  ltac:(rewrite EY; unfold prhReader_hd; cbn [map fst app];
                                        exact (perm_remove_nodup Hp2 _ (ledger_hp_nodup B _ _ _ _ _ _ _ _ _ _ _ _ HLEDk) HhpY))
                                  HHpk HAR3 HL3s HAT3
                                  HKB3 ltac:(rewrite Hkbl, Hc2; clear - Hcap; lia)
                                  ltac:(intros a Ha; rewrite Hkbl in Ha;
                                        exact (proj2 (HNEW a ltac:(rewrite Hc2 in Hrqn |- *; clear - Ha Hrqn Hh0 Hcap; lia))))
                                  HYB3 ltac:(rewrite Hybl, Hc2; clear - Hcap; lia)
                                  ltac:(intros a Ha; rewrite Hybl in Ha;
                                        exact (proj2 (HNEWk a ltac:(rewrite Hc2 in Hrqk |- *; clear - Ha Hrqk Hh0 Hcap; lia))))
                                  (conj HRAresk Hhullk) Hres1k Hres16k ltac:(rewrite HBB3, Hc2; clear - Hh0; lia)
                                  HFR12 HGR12 HA007 HHDR3 RkF RyF RcF
                                  Hvstk Hv4096 Hvhi Hsp128 Hoff Happ
                                  HLVF HPOSF) as (HBND7 & HARM7).
                                split; [exact HBND7|].
                                right; right; right; right; right; right. exact HARM7.
            -- (* cap = 0: excluded on this class (it is PwGrowBCap0.v's growB_seg_cap0) *)
         exfalso. rewrite branch_ne_U in Hc0. apply negb_false_iff, Z.eqb_eq in Hc0.
         rewrite U_SOff, U37, Z.add_0_r, zcanon_id, U_lit in Hc0 by (unfold M64; lia). exact (Hcapnz Hc0).
  + (* n < cap: nothing done; the run reaches the ret with a0 = 0 *)
    assert (Hlt : n < cap).
    { rewrite branch_geu_U in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
      rewrite !U_SOff, U36, U37, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia). exact Hc. }
    pose proof HJ as (HARc & _).
    paj_run_tok_x_inv (RUNBP PM PLAW) HS HJ SHOK HPM growB_Bspan.
    * apply (grow_awr_ok_fr _ _ (@STK_grow prh_img_B) GROW_FR_B e (spZ regs) FP _ _ S ly v);
        [unfold GROW_FR_B; lia | exact FS | exact He0 | | | ].
      -- unfold GROW_FR_B; grow_wr_tac U2 U10.
      -- intros a Ha. rewrite HFP. exact (grow_FP_v v ty kids keys cap a Ha).
      -- exact Hvloc.
    * destruct (grow_stretch B ARx SK LAWS (@STK_grow prh_img_B) GROW_FR_B E0 _ W mem (ms_mem ms)
        (with_vm_backing (m_vm_lazy md) mat md) (ms_mem ms0) _
        (spZ regs) v FP ly S Hp W mem md ly S Hp ltac:(unfold GROW_FR_B; lia) FS HK1 HFR1 HGR1 HAR HARc Hceil Hslo Hshi
        HFr HG ltac:(unfold GROW_FR_B; grow_wr_tac U2 U10)
        (same_but_materialized_wvb_any (with_vm_backing (m_vm_lazy md) mat md) mat0))
        as (HK2 & HFR2 & HGR2).
      rewrite ?wvb_collapse in HK2, HJ.
      match type of HS with st_ok_pi _ _ E0 _ _ => idtac | _ => fail "run 2 changed the environment" end.
      eapply (grow_ret B ARx SK LAWS PL_prog_B (@STK_grow prh_img_B) W E0 _ ms0 _ e FP regs (growB_extra ty kids keys n cap)
        ly S Hp W mem md (grow_OR v) FP ly S Hp _ _ ltac:(apply Z.leb_le; vm_compute; reflexivity) HS);
        [vm_compute; reflexivity | vm_compute; reflexivity | exact HA32 | vm_compute; reflexivity |
        vm_compute; reflexivity | exact Hra | exact HJ | exact HK2 | | ].
      -- rewrite HFP. intros a (r & Hr & Hb). exists r. split; [apply in_or_app; left; exact Hr | exact Hb].
      -- intros mat'. cbv beta. unfold fQmn. cbv beta.
         split; [|exact (PEND _ HPM)].
         split; [exact HROOM|].
         (* no allocator call (n < cap): the hull use is the empty one, at the entry state *)
         split; [exact (grow_hull_none S (ty =? 6) n cap Hlt)|].
         (* the position does not move on this arm: no allocator call *)
         split.
         { unfold PRH_Charge.prh_held, PRH_Charge.prhPg_gtrace, PjGrammar.grow.
           replace (Nat.ltb (Z.to_nat n) (Z.to_nat cap)) with true by (symmetry; apply Nat.ltb_lt; lia).
           cbn. lia. }
         left. split; [exact Hlt|]. split.
         { pose proof (st_ok_pi_restrict_reg (w_H W) E0 _ ms0 10%bv HS) as R10.
           match type of R10 with _ = sv_denot _ ?t => let t' := eval vm_compute in t in change t with t' in R10 end.
           rewrite R10. reflexivity. }
         split; [reflexivity|]. split; [reflexivity|].
         (* no allocator call on this arm: the blocks' bytes are exactly kept *)
         split; [reflexivity|]. split.
         { apply (prh_ledger_keep B ly S Hp W mem (ms_mem ms0) Lam peak cnt fail ran most own HLED).
           intros a Hca.
           destruct (grow_cell_apart B ARx LAWS HPST GROW_FR_B ly S Hp W mem md Lam peak cnt fail ran most own regs e v a
             ltac:(unfold GROW_FR_B; lia) HAR HLED HAT Hsp128 Hoff Hca) as (Ha64 & Hwa).
           apply HFR2. rewrite unsigned_lit_small by exact Ha64. exact Hwa. }
                 split; cycle 1.
        { split.
          { intros lo hi x Hlh Hx.
            destruct (grow_slot_apart B ARx LAWS GROW_FR_B ly S Hp W mem md Lam peak cnt fail ran most own regs e v ty kids
              keys n cap lo hi x ltac:(unfold GROW_FR_B; lia) ltac:(lia) HAR HLED HAT Hsp128 HSLOT HAP Hlh Hx) as (Hx64 & Hxw).
            apply aview_eq_of. apply HFR2. rewrite unsigned_lit_small by exact Hx64. exact Hxw. }
          (* no allocator call (outcomes []): E = [], the live requests and the position kept *)
          replace (prhPg_evs (ty =? 6) n cap []) with (@nil PresetReqAt.hev)
            by (unfold prhPg_evs; rewrite (proj2 (Z.ltb_lt n cap) Hlt); reflexivity).
          split; [exact (grow_live_keep B ly S ly S eq_refl)|].
          intros sm x os i H0 hist Hpsm _. exists hist. cbn [length]. rewrite Nat.add_0_r. exact Hpsm. }
         assert (HR1 : region_ok SEGS E0 (mrestrict (w_H W) (ms_mem ms0)) growB_vA).
         { match type of HS with st_ok_pi _ _ _ ?ss _ =>
             exact (st_ok_region_nth SEGS E0 (abs_ss VAL ss) (restrict (w_H W) ms0) 1 growB_vA HS
               ltac:(vm_compute; reflexivity)) end. }
         assert (HR2 : region_ok SEGS E0 (mrestrict (w_H W) (ms_mem ms0)) growB_vB).
         { match type of HS with st_ok_pi _ _ _ ?ss _ =>
             exact (st_ok_region_nth SEGS E0 (abs_ss VAL ss) (restrict (w_H W) ms0) 2 growB_vB HS
               ltac:(vm_compute; reflexivity)) end. }
         unfold growB_vA in HR1. unfold growB_vB in HR2.
         apply (grow_hdr_keep GROW_FR_B (w_H W) mem (ms_mem ms0) (spZ regs) v ty num str kids keys n cap kids keys cap HH HFR2
           HGR2 Hvstk ltac:(lia) ltac:(lia)).
         ++ split; [exact Hkids|].
            exact (field_of_region SEGS E0 _ 10 v _ 0 40 24 40 24 8 (SOff 34 0) kids HR1 U10 ltac:(cbn; tauto)
              ltac:(cbn [sv_denot]; rewrite U34, Z.add_0_r; reflexivity) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia)
              ltac:(cbn; lia)).
         ++ split; [exact Hkeys|].
            exact (field_of_region SEGS E0 _ 10 v _ 0 40 24 40 32 8 (SOff 35 0) keys HR1 U10 ltac:(cbn; tauto)
              ltac:(cbn [sv_denot]; rewrite U35, Z.add_0_r; reflexivity) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia)
              ltac:(cbn; lia)).
         ++ split; [exact Hcap|].
            exact (field_of_region SEGS E0 _ 10 v _ 40 56 48 56 48 8 (SOff 37 0) cap HR2 U10 ltac:(cbn; tauto)
              ltac:(cbn [sv_denot]; rewrite U37, Z.add_0_r; reflexivity) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia)
              ltac:(cbn; lia)).
Qed.
End c.
