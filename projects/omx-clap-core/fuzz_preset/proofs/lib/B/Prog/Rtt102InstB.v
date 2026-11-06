(* B' TWIN (asan-ubsan d663f82d7f488d30, unstripped twin c90d4fa54d43160b) of lib/A/Prog/Rtt102InstA.v, by a name map:
   round_trip_text's body on image B is image A's instruction sequence with only pc-relative immediates changed
   (capstone over both twins' symtab bodies; every call site at the same offset), so the twin is the A' file with
   image A's listing / image / PrhImg / CfImg names replaced by image B's (A_prog_* -> B_prog_*, PI_prog_A /
   PL_prog_A -> _B, prh_img_A -> prh_img_B, CfImg_A -> CfImg_B, S1ImgA -> S1ImgB, IMG_LO / IMG_TOP -> IMG_LO_B /
   IMG_TOP_B, the A' stretch modules Rtt102*A -> Rtt102*B, the file's own *_A names -> *_B) and image B's own value
   for each image numeral the file states (a load offset, the function's listing offset, a witness address); every
   closed image check is re-run at B' by the build. The comments below are the A' file's: their addresses and slot
   numbers are image A's. *)
(* fuzz_preset, image A' (asan, sha256 1be0f53d96cb9d6c, unstripped twin bff8519bbe3ea0e4): round_trip_text's walk AT THE
   D2p INTERFACE RELATION. The kit's text tround_trip_text_specX at the instance the callee record uses (lib/A/PresetD2pAPf.v
   section 0b): ci := CfImg_B, cp := CfParams_preset, PI := PresetCfnB.preset_prh_img (= prh_img_B), RL :=
   prh_room_live_a8, L := B_prog_listing, PA := PI_prog_B, B := YD2l.TfibB, ARx := PresetCfnB.iface_ARx (= ARcf /\
   xs_placed_cf at CfParams_preset), SK := PresetCfnB.preset_sink_head; the universe closure CTX0 is a parameter
   (the record's PresetCfnB.iface_ctx0 at rtt_iface_B_at_ctx0; CrtFit's RTT quantifies it).
   rule 24: proves no function (kind: instance corollary of round_trip_text's A' walk, Rtt102TopB.rtt_text_B_cond).
   THE GENERIC WALK'S SECTION HYPOTHESES AT THIS INSTANCE:
   - DISCHARGED here, each by a cited theorem or by computation:
       LAWS / OWNLOW      YGcallcf.AR_laws_x_xs / ARx_owned_low_law_xs of YG0lawscf.AR_laws_ok_cf
       ASFX / FFLX / SFX  YGcallScf.astack_free_x_xs / frame_flag_x_xs / stack_free_x_any
       FFLP               the flag field of the laws (YCbqG.alx_flag)
       HW / HHEAD / HI_hull  CfParams_preset's head and meter caps (preset_head_wide; computation)
       PAL / pal_*        PALibB.exvi_eh_palib; computation at TfibB; FuzzAllocAccInstB102.acc_pal_pst_ok_B
       ASM1               FCm01xm.stack_malloc1_contract_xm at ARcf (FCifaceCf.fs_iface_ARcf), lifted to xs_placed_cf by
                          YGcallMxmn.astack_malloc_realizes_xm_conj (xs_placed_cf is kept by set_fs)
       SMX                YGcallScf.stack_malloc_x_any
       QM .. ACF          the cf instance (YGcallcf.v): QM_cf / QMm_cf / malloc_cf / cf_malloc_max / Wf_cf, WFL, AMX at
                          YCej.Tfib_universe_ok, QMQ_cf, QMR from QMm_cf_of_room (room_live_room, the meter, the
                          RELRO rows of CfAroPresetB.v), ACF by acall_pre_x_xs_cf
       APOST / POST_*     the KEEP free post of YGcallMxmnKeep.v: APOST_cf_keep, POST_AR_cf_keep, POST_J_cf_keep, proj2
       AMCPY / AIM        PRowCpy.prow_asan_memcpy_xm_B / PRowSet.prow_asan_memset_xm_B_lit
       STRCMP / STRLEN    PSstrRo.ps_strcmp_xrom_xs_B / ps_strlen_xrom_xs_B
       TFARO              FuzzAllocAccInstB102.fuzz_alloc_ran_out_holds_B_inst
       zs_aligned / img_shadow_vis_x / RTT_T_TRACE_AT  computation; AImgShadowVisCfB.tfib_img_shadow_vis_cf_B;
                          Rtt102TopB.rtt_t_trace_at_B
   - CARRIED as the named Hypotheses below, each with its owner: the kit's callee texts with no walk at this relation on the
     base (same, pj_free, fuzz_free, parse_noting, tx_put, tx_value, pj_write), the KEEP free row
     afree_realizes_cf_rh_keep, and the newline literal's image binding (kept_img at Rtt102TB.RTT_LITNL_B). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YGcallx YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0b YPsym YC4aP YC1fP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0ncf YG0dcf YG00cf YGcallcf YGcallScf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0lawscf YGcallMxmnKeep YGcfMallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require FCifaceCf YGcfRoomLive YGcfAroBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt PresetSecTotal PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnCheck PRH_FnAlloc PRH_FnEx PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnTx PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l YF0m YCej YCeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PALibB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require FCm01xm AImgShadowVisCfB CfAroPresetB PresetCfnB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PRowCpy PRowSet PSstrRo.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require FuzzAllocAccInstB102.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Rtt102TB Rtt102TopB.
Import ListNotations.
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope Z_scope.

#[local] Notation CP := CfParamsPreset.CfParams_preset.
#[local] Notation TA := YD2l.TfibB.
#[local] Notation CI := CfImgB.CfImg_B.
#[local] Existing Instance CfParamsPreset.CfParams_preset.
#[local] Existing Instance CfImgB.CfImg_B.

(* ---- closed checks at the A' record ---- *)
Lemma ri_head : @cf_head CP = PresetReqAt.HEAD.
Proof. vm_compute. reflexivity. Qed.
Lemma ri_hull : PresetSecTotal.SEC_N_CAP <= @YGcfNames.cf_kmax CP /\ PresetSecTotal.SEC_T_CAP <= @YGcfNames.cf_T_max CP.
Proof. vm_compute. split; discriminate. Qed.
Lemma ri_uar : IMG_LO_B <= as_uar_cell TA /\ as_uar_cell TA + 4 <= IMG_TOP_B.
Proof. split; apply Z.leb_le; vm_compute; reflexivity. Qed.
Lemma ri_zs : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow TA).
Proof.
apply Forall_forall. intros r Hr.
assert (Hb : forallb (fun r => (fst r mod 8 =? 0) && (snd r mod 8 =? 0)) (as_zero_shadow TA) = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in Hb. specialize (Hb r Hr). apply andb_true_iff in Hb as [H1 H2].
split; apply Z.eqb_eq; assumption.
Qed.

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation PA := (@PI_prog_B rc).
#[local] Notation SEGS := (@pa_segs rc B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma rc B_prog_listing PA).
#[local] Notation RLX := (@prh_room_live_a8 CP).
#[local] Notation ARI := (@PresetCfnB.iface_ARx rc B_prog_listing PA CI TA).
#[local] Notation SK0 := PresetCfnB.preset_sink_head.
#[local] Notation CTX := PresetCfnB.iface_ctx0.

Lemma ri_sm1 : SIGMA AS___asan_stack_malloc_1 = pc_stack_malloc (as_code TA) 1.
Proof. vm_compute. reflexivity. Qed.
Lemma ri_laws : AR_laws_x SEGS TA ARI (@cf_head CP).
Proof. exact (YGcallcf.AR_laws_x_xs SEGS TA (YG0lawscf.AR_laws_ok_cf SEGS TA)). Qed.
Lemma ri_ownlow : ARx_owned_low_law SEGS TA ARI.
Proof. exact (YGcallcf.ARx_owned_low_law_xs SEGS TA (YG0lawscf.AR_laws_ok_cf SEGS TA)). Qed.
Lemma ri_fflp : forall ly S Hp (W : world SEGS) mem md cid pos, ARI ly S Hp W mem md -> In (cid, pos) (frames S) ->
  apresent (w_H W) mem (flag_addr ly cid pos).
Proof. intros ly S Hp W mem md cid pos H Hin. exact (proj1 (alx_flag _ _ _ ri_laws ly S Hp W mem md cid pos H Hin)). Qed.
Lemma ri_isv : forall ly S Hp W mem md a, ARI ly S Hp W mem md -> IMG_LO_B <= a < IMG_TOP_B ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
Proof.
intros ly S Hp W mem md a [HAR _] Ha.
apply (AImgShadowVisCfB.tfib_img_shadow_vis_cf_B SEGS TA YD2l.TfibB_syms ly S Hp W mem md a HAR).
assert (E1 : @cf_img_lo CI = IMG_LO_B) by reflexivity. assert (E2 : @cf_img_top CI = IMG_TOP_B) by reflexivity.
rewrite E1, E2. exact Ha.
Qed.
Lemma ri_asm1 : YGcallMxmn.astack_malloc_realizes_xm (fx := fx) SEGS TA ARI 1.
Proof.
exact (YGcallMxmn.astack_malloc_realizes_xm_conj SEGS TA _ (fun ly S => YG0ncf.xs_placed_cf ly S) 1
  (fun ly S f H => YGcallScf.xs_placed_cf_set_fs ly S f H)
  (FCm01xm.stack_malloc1_contract_xm TA _ (FCifaceCf.fs_iface_ARcf SEGS TA (YG0lawscf.AR_laws_ok_cf SEGS TA))
     YD2l.TfibB_syms)).
Qed.
(* the call's trailing conjuncts on the state and the call memory at the cf instance: the non-primary room
   (room_live_room), the meter (CfParams_preset's cf_hull_ok IS hull_budget S []'s two bounds) and the read-only view
   (CfAroPresetB.v's four RELRO rows, YGcfAroBridge.arodata_ok_cf_of_P) *)
Lemma ri_qmr : forall ly S Hp W mem md, ARI ly S Hp W mem md -> qtight S -> YGcfRoomLive.room_live_cf (cp := CP) S ->
  PresetHullBudget.hull_budget (cp := CP) S [] ->
  arodata_okP SEGS (@pa_relro_lo _ B_prog_listing PA) (@pa_relro_hi _ B_prog_listing PA) TA (aview SEGS (w_H W) mem) ->
  YGcallcf.QMm_cf (ci := CI) (cp := CP) SEGS TA S mem.
Proof.
intros ly S Hp W mem md [HAR _] HQ HR HH HP.
apply (YGcallcf.QMm_cf_of_room SEGS TA ly S Hp W mem md HAR HQ (YGcfRoomLive.room_live_room S HR)).
- destruct HH as [H1 H2].
  assert (E1 : Z.of_nat (PresetSecTotal.nsec []) = 0) by reflexivity.
  assert (E2 : PresetSecTotal.tsec [] = 0) by reflexivity.
  rewrite E1 in H1. rewrite E2 in H2.
  change (nsec_cf S <= @cf_kmax CP /\ sec_T_cf S <= @cf_T_max CP). lia.
- apply (YGcfAroBridge.arodata_ok_cf_of_P SEGS TA W mem CfAroPresetB.relro_seg_preset_AU
    (CfAroPresetB.errno_relro_preset_AU TA YD2l.TfibB_syms) CfAroPresetB.relro_top_preset_AU
    CfAroPresetB.ro_reads_nw_preset_AU).
  assert (E1 : @cf_relro_lo CI = @pa_relro_lo _ B_prog_listing PA) by (vm_compute; reflexivity).
  assert (E2 : @cf_relro_hi CI = @pa_relro_hi _ B_prog_listing PA) by (vm_compute; reflexivity).
  rewrite E1, E2. exact HP.
Qed.

(* ---- the runtime rows, CITED (proved rows of record at any relation with the engine laws / at ARcf /\ xs_placed_cf),
   with the listing's pc of each wrapper by computation ---- *)
(* __asan_memcpy: a Theorem Labs lane's row PRowCpy.prow_asan_memcpy_xm_B (any ARx with AR_laws_x, TfibSyms) *)
Lemma ri_amcpy : forall fy : YK11.FPState, @YGcallMxmn.aintrin_realizes_xm fy SEGS TA ARI OCpy (SIGMA AS___asan_memcpy).
Proof.
intros fy. assert (E : SIGMA AS___asan_memcpy = pc_asan_memcpy (as_code TA)) by (vm_compute; reflexivity).
rewrite E. exact (PRowCpy.prow_asan_memcpy_xm_B (fx := fy) TA ARI _ ri_laws YD2l.TfibB_syms).
Qed.
(* __asan_memset: a Theorem Labs lane / the cf instance owner's row PRowSet.prow_asan_memset_xm_B_lit (at the listing's literal pc) *)
Lemma ri_aim : forall fy : YK11.FPState, @YGcallMxmn.aintrin_realizes_xm fy SEGS TA ARI OSet (SIGMA AS___asan_memset).
Proof.
intros fy. assert (E : SIGMA AS___asan_memset = 0x5296c) by (vm_compute; reflexivity).
rewrite E. exact (PRowSet.prow_asan_memset_xm_B_lit (fx := fy) TA ARI _ ri_laws YD2l.TfibB_syms).
Qed.
(* the strcmp / strlen wrappers over the read-only band: a Theorem Labs lane's PSstrRo rows at ARcf /\ xs_placed_cf, at any
   band bounds (here the listing's RELRO band) *)
Lemma ri_strcmp : forall fy : YK11.FPState,
  @YGcallMxmn.astrcmp_realizes_xrom fy SEGS TA ARI (@pa_relro_lo _ B_prog_listing PA) (@pa_relro_hi _ B_prog_listing PA)
    (SIGMA AS___wrap_strcmp).
Proof.
intros fy. assert (E : SIGMA AS___wrap_strcmp = @cf_pc_strcmp CI) by (vm_compute; reflexivity).
rewrite E. exact (PSstrRo.ps_strcmp_xrom_xs_B (fx := fy) TA YD2l.TfibB_syms _ _).
Qed.
Lemma ri_strlen : forall fy : YK11.FPState,
  @YGcallMxmn.astrlen_realizes_xrom fy SEGS TA ARI (@pa_relro_lo _ B_prog_listing PA) (@pa_relro_hi _ B_prog_listing PA)
    (SIGMA AS___wrap_strlen).
Proof.
intros fy. assert (E : SIGMA AS___wrap_strlen = @cf_pc_strlen CI) by (vm_compute; reflexivity).
rewrite E. exact (PSstrRo.ps_strlen_xrom_xs_B (fx := fy) TA YD2l.TfibB_syms _ _).
Qed.
(* fuzz_alloc_ran_out: its A' walk at the record, FuzzAllocAccInstB102.fuzz_alloc_ran_out_holds_B_inst (no premise) *)
Lemma ri_tfaro : forall fy : YK11.FPState,
  @tfuzz_alloc_ran_out_specX fy rc CP PresetCfnB.preset_prh_img RLX B_prog_listing PA TA ARI SK0.
Proof. intros fy. exact (FuzzAllocAccInstB102.fuzz_alloc_ran_out_holds_B_inst (fx := fy) (SK := SK0)). Qed.

(* ---- THE CARRIED PREMISES (no walk of record at this relation on the base), each with its owner; the kit's texts are
   written as the D2p record writes them (PresetD2pAPf.v section 0b: PI := preset_prh_img). The universe closure CTX0
   is the instance's parameter: the D2p record's is PresetCfnB.iface_ctx0 (rtt_iface_A_ctx0 below), CrtFit's RTT
   quantifies it. ---- *)
Variable CTX0 : list (list Z).
(* same: the kit's text (owner: the B' same walk's owner; its walk SameB_walk.same_holds_B is stated over the Section parameters B, ARx and SK) *)
Hypothesis TSAME : forall fy : YK11.FPState,
  @tsame_specX fy rc CP PresetCfnB.preset_prh_img RLX B_prog_listing PA TA ARI SK0 DOC_D.
(* pj_free: the D2p record's H_txt_pj_free_A *)
Hypothesis TPJF : forall fy : YK11.FPState,
  @tpj_free_specX fy rc CI CP PresetCfnB.preset_prh_img RLX B_prog_listing PA TA ARI SK0 CTX0 DOC_D.
(* the re-hiding free in its KEEP form (owner: the cf instance owner, YGcfMallocComposeKeep.afree_realizes_cf_rh_keep at TfibB) *)
Hypothesis AFK : forall fy : YK11.FPState,
  YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fy) SEGS TA.
(* fuzz_free: the kit's text (owner: its walk's row owner) *)
Hypothesis TFF : forall fy : YK11.FPState,
  @tfuzz_free_specX fy rc CP PresetCfnB.preset_prh_img RLX B_prog_listing PA TA ARI SK0.
(* parse_noting: the D2p record's H_txt_parse_noting_A *)
Hypothesis TPN : forall fy : YK11.FPState,
  @tparse_noting_specX fy rc CI CP PresetCfnB.preset_prh_img RLX B_prog_listing PA TA ARI SK0 CTX0.
(* the newline literal rendered() hands tx_put is a kept image literal (owned by the kit, image A's binding, PRH_FnTx.v
   TX-LIT) *)
Hypothesis LITNL : @kept_img rc B_prog_listing PA TA (@Rtt102TB.RTT_LITNL_B rc) 1.
(* tx_put, tx_value: the kit's texts (owner: the tx walks' row owner) *)
Hypothesis TXPUT : forall fy : YK11.FPState,
  @PRH_FnTx.ttx_put_specX fy rc CI CP PresetCfnB.preset_prh_img RLX B_prog_listing PA TA ARI SK0 CTX0.
Hypothesis TXVAL : forall fy : YK11.FPState,
  @PRH_FnTx.ttx_value_specX fy rc CI CP PresetCfnB.preset_prh_img RLX B_prog_listing PA TA ARI SK0 CTX0 DOC_D.
(* pj_write: the kit's text (owner: the writer walk's row owner) *)
Hypothesis TPJW : forall fy : YK11.FPState,
  @PRH_FnWriter.tpj_write_specX fy rc CI CP PresetCfnB.preset_prh_img RLX B_prog_listing PA TA ARI SK0 CTX0 DOC_D.

(* ---- THE INSTANCE: the kit's text at the D2p interface relation ---- *)
Theorem rtt_iface_B :
  @tround_trip_text_specX fx rc CI CP PresetCfnB.preset_prh_img RLX B_prog_listing PA TA ARI SK0 CTX0.
Proof.
exact (@Rtt102TopB.rtt_text_B_cond fx rc CI RLX (@prh_room_free_a8 CP) TA ARI SK0 CTX0
  ri_laws ri_ownlow
  (YGcallScf.astack_free_x_xs SEGS TA) (YGcallScf.frame_flag_x_xs SEGS TA) (YGcallScf.stack_free_x_any SEGS ARI)
  ri_fflp CfParamsPreset.preset_head_wide TSAME TPJF ri_amcpy ri_tfaro
  PALibB.exvi_eh_palib ri_sm1 ri_uar FuzzAllocAccInstB102.acc_pal_pst_ok_B ri_head ri_hull ri_asm1
  (YGcallScf.stack_malloc_x_any SEGS ARI)
  _ _ _ _ _ (YGcallcf.ARx_wf_law_xs SEGS TA) (YGcallcf.alloc_model_laws_x_cf TA YCej.Tfib_universe_ok)
  (YGcallcf.QMQ_cf SEGS TA)
  _ (YGcallMxmnKeep.POST_AR_cf_keep SEGS TA)
  (YGcallMxmnKeep.POST_J_cf_keep SEGS TA ri_laws YCeg.tfib_segs_low PALibB.exvi_eh_errno ri_ownlow)
  (fun stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' H => proj2 H)
  (fun fy => YGcallMxmnKeep.afree_realizes_x_cf_rh_keep (fx := fy) SEGS TA (AFK fy))
  ri_qmr (YGcallcf.acall_pre_x_xs_cf SEGS TA)
  ri_strcmp ri_strlen TFF TPN ri_zs ri_isv LITNL TXPUT TXVAL ri_aim TPJW
  (Rtt102TopB.rtt_t_trace_at_B TA eq_refl)).
Qed.
End i.

(* the D2p record's slot: the same theorem at its universe closure PresetCfnB.iface_ctx0 *)
Definition rtt_iface_B_at_ctx0 (fx : YK11.FPState) (rc : YM05.RunCeil) :=
  @rtt_iface_B fx rc PresetCfnB.iface_ctx0.

(* THE STATEMENT CHECK: implicits on, notations off - every FPState argument is the Section's fx, the instance is the
   D2p record's (CfImg_B, CfParams_preset, preset_prh_img, prh_room_live_a8, B_prog_listing, PI_prog_B, TfibB,
   iface_ARx, preset_sink_head; CTX0 the parameter, iface_ctx0 at the corollary) *)
Set Printing Implicit.
Unset Printing Notations.
Set Printing Width 4000.
Check @rtt_iface_B.
Check @rtt_iface_B_at_ctx0.
Set Printing Notations.
Unset Printing Implicit.
Print Assumptions rtt_iface_B.
Print Assumptions rtt_iface_B_at_ctx0.
