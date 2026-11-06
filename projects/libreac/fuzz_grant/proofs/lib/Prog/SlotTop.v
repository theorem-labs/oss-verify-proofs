From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import Contract FrameAPI Img0 AllocSlots AllocRoom.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require PropExec.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import LLVMFuzzerTestOneInput_c GrantSlotPlan PlainHalts
  SlotImg SlotIntegration SlotEntry SlotGlue SlotStGlue.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require RgNeeds_c.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Seg_head Seg_main Seg_nset Seg_set_turn Seg_unset_enter
  Seg_unset_turn Seg_admit Seg_sweep Seg_raw Seg_rawsweep Seg_sched_setup Seg_sched_turn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require BuildSweepLink SweepLink FinishLink ParseLink.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require memset memcpy bcmp kind_of_link1 ctrl_finish
  reac_ctrl_stamp_headamp reac_ctrl_build_grant_sweep reac_grant_build_sweep reac_ctrl_parse check_groupa
  reac_ctrl_headamp_record_verify reac_ctrl_checksum_verify reac_ctrl_identity_poll_block reac_headamp_default
  reac_grant_alloc_fits reac_grant_allocate reac_headamp_tx_init reac_headamp_tx_set reac_headamp_tx_effective
  reac_headamp_tx_next reac_headamp_tx_arm_scene reac_headamp_tx_set_resweep.
Import ListNotations.
Local Open Scope Z_scope.

(* The thirteen code segments of the slot, with every function they call instantiated by its proof;
   the one open function premise is the layout block of reac_ctrl_stamp_headamp. *)
Section Segs.
Variable LAY : RgNeeds_c.ctrl_lay_block_need.

Lemma slot_segs :
  seg_head /\ seg_init /\ seg_nset /\ seg_set_turn /\ seg_unset_enter /\ seg_unset_turn /\ seg_admit /\
  seg_sweep /\ seg_raw /\ seg_rawsweep /\ seg_sched_setup /\ seg_sched_turn /\ seg_epilogue.
Proof.
  pose proof memset.memset_holds as MSET.
  pose proof memcpy.memcpy_holds as MCPY.
  pose proof bcmp.bcmp_holds as BCMP.
  pose proof reac_headamp_tx_effective.reac_headamp_tx_effective_holds as EFF.
  pose proof reac_headamp_default.reac_headamp_default_holds as DFL.
  pose proof reac_grant_alloc_fits.reac_grant_alloc_fits_holds as FITS.
  pose proof (BuildSweepLink.build_sweep_link
    (reac_grant_build_sweep.reac_grant_build_sweep_holds EFF
      (SweepLink.sweep_link (reac_ctrl_build_grant_sweep.reac_ctrl_build_grant_sweep_holds MCPY MSET
        (reac_ctrl_stamp_headamp.reac_ctrl_stamp_headamp_holds LAY
          (FinishLink.ctrl_finish_link ctrl_finish.ctrl_finish_holds)))))) as BSN.
  pose proof (BuildSweepLink.check_groupa_link
    (check_groupa.check_groupa_holds MCPY
      (ParseLink.parse_link (reac_ctrl_parse.reac_ctrl_parse_holds MSET MCPY BCMP kind_of_link1.kind_of_link1_holds))
      EFF reac_ctrl_headamp_record_verify.reac_ctrl_headamp_record_verify_holds
      reac_ctrl_checksum_verify.reac_ctrl_checksum_verify_holds)) as GAN.
  split; [exact Seg_head.seg_head_holds|].
  split; [exact (Seg_main.seg_init_holds (reac_headamp_tx_init.reac_headamp_tx_init_holds MSET) MSET)|].
  split; [exact Seg_nset.seg_nset_holds|].
  split; [exact (Seg_set_turn.seg_set_turn_holds reac_headamp_tx_set.reac_headamp_tx_set_holds EFF DFL)|].
  split; [exact Seg_unset_enter.seg_unset_enter_holds|].
  split; [exact (Seg_unset_turn.seg_unset_turn_holds EFF DFL)|].
  split; [exact (Seg_admit.seg_admit_holds FITS reac_grant_allocate.reac_grant_allocate_holds)|].
  split; [exact (Seg_sweep.seg_sweep_holds BSN GAN DFL
                   (reac_ctrl_identity_poll_block.reac_ctrl_identity_poll_block_holds MCPY) BCMP)|].
  split; [exact Seg_raw.seg_raw_holds|].
  split; [exact (Seg_rawsweep.seg_rawsweep_holds BSN FITS)|].
  split; [exact (Seg_sched_setup.seg_sched_setup_holds reac_headamp_tx_arm_scene.reac_headamp_tx_arm_scene_holds
                   reac_headamp_tx_set_resweep.reac_headamp_tx_set_resweep_holds MSET)|].
  split; [exact (Seg_sched_turn.seg_sched_turn_holds reac_headamp_tx_next.reac_headamp_tx_next_holds EFF DFL)|].
  exact Seg_main.seg_epilogue_holds.
Qed.
End Segs.

(* The image facts the slot needs about the frame's symbols. *)
Section Img.
Variable B : malloc_syms.
Hypotheses (HB : ms_segs B = rsegs) (HGU : ms_guard B = 0x4f940) (HGG : ms_got_guard B = 0x1e358)
  (HCTX : ms_ctx B = 0x4f9d8) (HLOCK : ms_lock B = 0x4f9d0) (HLIBC : ms_libc B = 0x4f960)
  (HSZ : ms_size_classes B = 0x10698) (HSM : ms_small_cnt B = 0x106f8) (HMD : ms_med_cnt B = 0x10713)
  (HDB : ms_debruijn B = 0x1061c) (HTP : ms_tp B = 0x2f6d0) (HEO : ms_errno_off B = -164) (HVM : ms_vmlock B = None)
  (HDL : ms_debruijn_len B = 124).

Lemma sink_img_free : forall a, a = 0x4f961 \/ 0x4fd88 <= a < 0x4fd98 -> img_free B a.
Proof.
  intros a Ha. assert (VL : vml_len B = 0) by (unfold vml_len; rewrite HVM; reflexivity).
  unfold img_free, static_owned, errno_addr, CTX_SIZE.
  rewrite HCTX, HLOCK, HLIBC, HGG, HGU, HDB, HDL, HSZ, HSM, HMD, HTP, HEO, VL. change (Z.max 32 124) with 124.
  split; [apply (proj2 (in_img_rsegs B a HB)); lia | lia].
Qed.

Lemma row_off_holds : row_off B.
Proof.
  intros i Hi. assert (VL : vml_len B = 0) by (unfold vml_len; rewrite HVM; reflexivity).
  unfold static_owned, errno_addr, CTX_SIZE, CTRL_HEADAMP_ROW.
  rewrite HCTX, HLOCK, HLIBC, HGG, HGU, HDB, HDL, HSZ, HSM, HMD, HTP, HEO, VL. change (Z.max 32 124) with 124. lia.
Qed.
End Img.

(* The slot contract of LLVMFuzzerTestOneInput on the plain image, on the frame facts of FrameAPI.frame_plain. *)
Theorem grant_slot_sb : RgNeeds_c.ctrl_lay_block_need -> grant_slot_plain.
Proof.
  intros LAY B API LS SH SK ra empty HF rc fx j _.
  destruct HF as (HB & Hra & HMAL & HFRE & _ & _ & HERR & HGU & HGG & HCTX & HLOCK & HLIBC & HSZ & HSM & HMD & HDB &
                  HTP & HEO & _ & HVM & HDL & HOFLH & HOFLL & HTHR & HEMP & _ & _ & _ & _ & HLIBK & HDELTA & HROOM & HFA).
  pose proof (HFA rc fx) as FA. pose proof (HERR rc) as Herr.
  pose proof (slot_segs LAY) as (HEAD & INIT & NSET & STURN & UENT & UTURN & ADMIT & SWEEP & RAW & RAWSW & SSETUP &
                                 SCHED & EPI).
  unfold lib_contract_g.
  intros L A regs mem md p n pl b K PRE _ HGR HRO _ HFRM HK.
  rewrite HLIBK.
  pose proof (aa_laws (API rc)) as LAWS.
  pose proof FA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AX & _).
  pose proof PRE as ((HMR & _ & _ & _ & _ & _ & HSc0 & _ & _ & Htp0 & _) & _ & _ & _ & Hroom & _ & _ & _ & _ & HS47).
  assert (HA0 : forall q k, In (q, k) (user_blocks A) ->
            4096 <= ptr_addr L q /\ ptr_addr L q + k <= alloc_ceiling /\
            (forall i, 0 <= i < k -> ~ in_img B (ptr_addr L q + i))).
  { intros q k Hq. destruct (mr_blocks_range B _ LAWS L A mem md q k HMR Hq) as (H1 & H2).
    split; [exact H1|]. split; [exact H2|]. intros i Hi. exact (ax_blocks_img AX L A mem md q k i HMR Hq Hi). }
  destruct (@entry_holds fx rc LS B (API rc) SH SK HB FA L A regs mem md p n HA0 ra empty pl b PRE HGR HRO HEMP)
    as (S1 & N1).
  assert (UB : unit_binding B).
  { refine (conj HB (conj _ _)); [rewrite HMAL | rewrite HFRE]; reflexivity. }
  assert (HTPx : x_tp (xent regs p pl) = w64 (ms_tp B)).
  { unfold xent. cbn [x_tp]. change (PropExec.getr regs (Z_to_bv 5 4)) with (YK11.getr regs 4). exact Htp0. }
  set (R := fun c => exists s L' A' md', c = mkCfg s md' /\
              St B (API rc) L A regs mem md (xent regs p pl) s L' A' md' b /\ norm_at (Ep (xent regs p pl)) s).
  assert (KR : forall s L' A' md' b', St B (API rc) L A regs mem md (xent regs p pl) s L' A' md' b' ->
                 norm_at (Ep (xent regs p pl)) s -> res_end b b' -> R (mkCfg s md')).
  { intros s L' A' md' b' S' N' Hb. unfold res_end in Hb. subst b'. exists s, L', A', md'. auto. }
  assert (RB0 : sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ 128 <= sb_cap b <= CAPMAX).
  { destruct (HROOM b n Hroom) as (H1 & H2 & H3). rewrite H3. unfold CAPMAX. lia. }
  pose proof (@path_all fx rc B (API rc) HB FA Herr L A regs mem md p HA0 pl b
                HEAD INIT NSET STURN UENT UTURN ADMIT SWEEP RAW RAWSW SSETUP SCHED EPI
                (@seg_mallocT_holds fx rc B (API rc)) (@seg_mallocSW1_holds fx rc B (API rc))
                (@seg_mallocSW2_holds fx rc B (API rc)) (@seg_freeSW1_holds fx rc B (API rc))
                (@seg_freeSW2_holds fx rc B (API rc)) (@seg_freeT_holds fx rc B (API rc))
                (@st_malloc_holds fx rc B (API rc) HB FA Herr L A regs mem md)
                (@st_free_holds fx rc B (API rc) HB FA Herr L A regs mem md)
                UB HTPx (row_off_holds B HGU HGG HCTX HLOCK HLIBC HSZ HSM HMD HDB HTP HEO HVM HDL) HSc0 HS47
                RB0 R KR _ S1 N1) as PATH.
  assert (SKF : img_free B (@sk_threaded SK) /\ (forall k, 0 <= k < 4 -> img_free B (@sk_ofl_lock SK + k)) /\
                (forall k, 0 <= k < 8 -> img_free B (@sk_ofl_head SH + k))).
  { pose proof (sink_img_free B HB HGU HGG HCTX HLOCK HLIBC HSZ HSM HMD HDB HTP HEO HVM HDL) as SI.
    split; [apply SI; rewrite HTHR; lia|].
    split; [intros k Hk; apply SI; rewrite HOFLL; lia | intros k Hk; apply SI; rewrite HOFLH; lia]. }
  rewrite HB.
  apply (SR_realizes rsegs _ R _ PATH).
  intros c' (s & L' & A' & md' & -> & S' & N').
  destruct (@final_holds fx rc LS B (API rc) SH SK HB L A regs mem md p n HA0 ra empty pl b s L' A' md'
              PRE Hra HDELTA SKF S' N') as (Ecfg & POST).
  rewrite Ecfg. rewrite <- HB.
  apply HK. exists fx, L', A', (ms_regs s), (ms_mem s), md'.
  split; [reflexivity|]. split; [exact HFRM|]. split; [exact POST | exact I].
Qed.
