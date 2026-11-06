(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset, image B' (asan-ubsan, harness fix #102 pin sha256
   d663f82d7f488d30f8e8d7496cb814e595a2f3cbbf16bde81a65cb3ea9af0994, unstripped twin c90d4fa54d43160b): THE SEAM of the
   walk of LLVMFuzzerTestOneInput. The interface's slot statement preset_lib_x_stmt (lib/AU/PresetCfnB.v:1022), EXACTLY as
   the driver of record takes it (lib/AU/PresetD2pBPf.v:218, H_preset_lib_x_stmt_B), at the walk's fixed values:
     sm := ReaderRes.jr_strtod (the walk's ec_pre asks e_sm E = jr_strtod, lib/AU/Ent102CutsB.v:273),
     iface_room_np := YGcfRoomLive.room_live_cf at CfParams_preset (= the driver's np_live_B by conversion),
     A_MOD_AT / A_STAMP := Ent102InstB.ia_mod_at / ia_stamp (the literals ec_img_B fixes),
     MT := ameter_triv (the driver's: its mo_ok / mo_le are True).
   PROOF: the walk's composed top lib/AU/Prog/Ent102TopB.v entry_B_walk (its only premise is ec_hyps), at the B' instance
   (PI := preset_prh_img, RL := prh_room_live_a8, B := TfibB, SK := preset_sink_head, EC_RA := RA_LLVMF, EC_EMPTY :=
   ia_empty, EC_SIO := ia_sio), between the interface's pre and post:
   1. ec_hyps from the callee record (every ec_texts field IS the record's field by conversion, ec_frame_area is
      pcc_stack_malloc at LLVMF_FS_CLASS with pcc_stack_free), ec_img_B, the pre's universe conjunct (ech_univ), the
      budgets of Ent102PaySatB.ec_pay_sat_preset and the interface's preset_no_refusal (ech_noref);
   2. the pre gives ec_pre at E := MkEcx ly S W regs mem md p n pl cnt ran jr_strtod os (length (hruns ..)) H0 hist;
   3. entry_B_walk gives SRr from cut_start to cut_ret;
   4. at checksum_shape, LIBK pl (m_fs md) K is K (LL 0 (m_fs md) []), the leaf the contract's continuation is fed with;
   5. cut_ret gives the return configuration and preset_lib_post_x (the journal's ARx weakened to ARcf: ARx occurs only
      positively, as the journal's first conjunct; the budget 76 <= K_LLVMF = 140; the fd table and the file system
      from the journal's aos_step at the empty footprint).
   rule 24: no function proved (kind: interface seam; the function's walk is the cited Ent102TopB.entry_B_walk). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0o YK18 YA0i YA0n YG00 YG0f YG0n YG0d YCbq YI16 YM05 YO09 YC5d YCbp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqG YCbqGwild YGcfRoomLive YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Ent102CutsB PresetCfnB Ent102InstB Ent102PaySatB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset PresetHullPay.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.Prog Require Ent102TopB.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Theorem preset_lib_x_stmt_B_holds : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (XM_LIB XN_LIB : Z -> Z)
  (PAYLOAD_ROOM : list byte -> Prop),
  PresetCfnB.preset_lib_x_stmt (rc := rc) (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape)
    (L := Listing_prog.B_prog_listing) (PA := PAImg_prog.PI_prog_B (rc := rc)) (ci := CfImgB.CfImg_B) (fx := fx)
    ReaderRes.jr_strtod (YGcfRoomLive.room_live_cf (cp := CfParamsPreset.CfParams_preset)) YD2l.TfibB ameter_triv
    XM_LIB XN_LIB PAYLOAD_ROOM Ent102InstB.ia_mod_at Ent102InstB.ia_stamp.
Proof.
intros rc fx XM_LIB XN_LIB PAYLOAD_ROOM HCC.
(* the slot at the re-hiding relation (PresetCfnB.v preset_lib_contract_xR at R := wle' segs RZ_cf): the walk frees, so
   its top is at that relation and the contract's continuation takes `R W W'` there *)
unfold PresetCfnB.preset_lib_contract_xR.
intros ly S Hp W regs mem md p n pl cnt ran os H0 hist K HAI Hpre HK.
pose proof (PresetCfnB.preset_lib_pre_pay8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpre) as Hpay8.
(* the pre's last conjunct (PresetCfnB.v header item (13), astack_up_x at the entry) is Hup: it goes into the walk's
   ec_pre (Ent102CutsB.v), and segment L5b carries it to check_round_trip's call *)
destruct Hpre as (HA & Hs0 & Hfrm & Hra & Ha0 & Ha1 & Hpn & Hlen & Hgarr & Hfr & (Hnp & Hat & Hlos) & Hwild & Hbb & Haro &
  HHp & (HLR & HSIO) & Hc1 & Hc2 & _ & Hsorted & _ & Hxs & Hmn & Huniv & Hup).
subst Hp.
(* THE BUDGETS: Ent102PaySatB's closed witnesses at CfParams_preset *)
destruct (Ent102PaySatB.ec_pay_sat_preset rc Listing_prog.B_prog_listing (PAImg_prog.PI_prog_B (rc := rc)))
  as (ccut & lcut & Hcok & Hlok & Hpok).
(* 1. THE WALK'S HYPOTHESES at the instance *)
assert (HH : @Ent102CutsB.ec_hyps rc CfImgB.CfImg_B CfParamsPreset.CfParams_preset PresetCfnB.preset_prh_img
  (@PRH_Base.prh_room_live_a8 CfParamsPreset.CfParams_preset) Listing_prog.B_prog_listing
  (PAImg_prog.PI_prog_B (rc := rc)) YD2l.TfibB PresetCfnB.preset_sink_head PresetCfnB.RA_LLVMF Ent102InstB.ia_empty
  Ent102InstB.ia_mod_at Ent102InstB.ia_stamp Ent102InstB.ia_sio Ent102InstB.ia_sio_img ccut lcut).
{ pose proof (HCC fx) as C.
  refine {| Ent102CutsB.ech_frame_area := _; Ent102CutsB.ech_texts := _; Ent102CutsB.ech_img := _;
            Ent102CutsB.ech_univ := _; Ent102CutsB.ech_ccut_ok := Hcok; Ent102CutsB.ech_lcut_ok := Hlok;
            Ent102CutsB.ech_pay := Hpok; Ent102CutsB.ech_noref := _; Ent102CutsB.ech_hull_pay := _ |}.
  - (* the frame area: the record's memnorm-keeping class-1 frame call and its release *)
    split.
    + intros fy. exact (PresetCfnB.pcc_stack_malloc _ _ _ (HCC fy) _ PresetCfnB.llvmf_fs_class_ok).
    + exact (PresetCfnB.pcc_stack_free _ _ _ C).
  - (* the sixteen texts: the record's fields, by conversion (D1); the stack table by computation *)
    refine {|
      Ent102CutsB.et_fuzz_alloc_ran_out_reset := PresetCfnB.pcc_fuzz_alloc_ran_out_reset _ _ _ C;
      Ent102CutsB.et_fuzz_alloc_most := PresetCfnB.pcc_fuzz_alloc_most _ _ _ C;
      Ent102CutsB.et_check_no_overread := PresetCfnB.pcc_check_no_overread _ _ _ C;
      Ent102CutsB.et_fuzz_alloc_live := PresetCfnB.pcc_fuzz_alloc_live _ _ _ C;
      Ent102CutsB.et_fuzz_alloc_count := PresetCfnB.pcc_fuzz_alloc_count _ _ _ C;
      Ent102CutsB.et_fuzz_alloc_peak_reset := PresetCfnB.pcc_fuzz_alloc_peak_reset _ _ _ C;
      Ent102CutsB.et_parse_noting := PresetCfnB.pcc_parse_noting _ _ _ C;
      Ent102CutsB.et_fuzz_alloc_peak := PresetCfnB.pcc_fuzz_alloc_peak _ _ _ C;
      Ent102CutsB.et_check_bounded_alloc := PresetCfnB.pcc_check_bounded_alloc _ _ _ C;
      Ent102CutsB.et_fuzz_alloc_ran_out := PresetCfnB.pcc_fuzz_alloc_ran_out _ _ _ C;
      Ent102CutsB.et_check_as_written := PresetCfnB.pcc_check_as_written _ _ _ C;
      Ent102CutsB.et_pj_free := PresetCfnB.pcc_pj_free _ _ _ C;
      Ent102CutsB.et_check_reject_clean := PresetCfnB.pcc_check_reject_clean _ _ _ C;
      Ent102CutsB.et_check_reject_clean_starved := PresetCfnB.pcc_check_reject_clean_starved _ _ _ C;
      Ent102CutsB.et_read_members := PresetCfnB.pcc_read_members _ _ _ C;
      Ent102CutsB.et_check_round_trip := PresetCfnB.pcc_check_round_trip _ _ _ C;
      Ent102CutsB.et_stk := _ |}.
    apply Z.leb_le. vm_compute. reflexivity.
  - (* the image facts at the concrete instance *)
    exact Ent102InstB.ec_img_B.
  - (* the universe at the top's own context [[RA_LLVMF]]: the pre's conjunct before the last, six times *)
    constructor; exact Huniv.
  - (* no refusal at a consumer allocation: the interface's preset_no_refusal *)
    intros E U S0 n0 tr ns HW Hx Hf Hp0.
    exact (PresetCfnB.preset_no_refusal U (Ent102CutsB.e_sm E) (Ent102CutsB.e_x E) (Ent102CutsB.e_H0 E) S0 n0 tr ns
      HW Hx Hf Hp0).
  - (* THE HULL BUDGET AT A POSITION (route (b)), discharged ONCE here at cp := CfParams_preset: a position of at most 4
       calls leaves the cf layer's hull room for one call's sections (lib/A/PresetHullPay.v:73) *)
    exact PresetHullPay.hull_budget_of_room_pos. }
(* 2. THE PRE -> ec_pre at the entry context E (the run position of iface_room_pos_entry: index length (hruns ..)) *)
pose (E := @Ent102CutsB.MkEcx rc Listing_prog.B_prog_listing (PAImg_prog.PI_prog_B (rc := rc)) ly S W regs mem md p n
  pl cnt ran ReaderRes.jr_strtod os (length (PresetRun.hruns ReaderRes.jr_strtod (Ent102CutsB.ec_bytes pl) os)) H0 hist).
assert (HP : @Ent102CutsB.ec_pre fx rc CfImgB.CfImg_B CfParamsPreset.CfParams_preset PresetCfnB.preset_prh_img
  (@PRH_Base.prh_room_live_a8 CfParamsPreset.CfParams_preset) Listing_prog.B_prog_listing
  (PAImg_prog.PI_prog_B (rc := rc)) YD2l.TfibB PresetCfnB.RA_LLVMF Ent102InstB.ia_empty Ent102InstB.ia_sio E).
{ (* the entry ledger: g_most and g_own_ran_out at the values ledger_rest's last two conjuncts read *)
  pose proof HLR as (_ & _ & _ & _ & _ & _ & _ & (m & Hm1 & Hm2) & (o & Ho1 & Ho2)).
  assert (Hmost : @PRH_Base.prh_most rc PresetCfnB.preset_prh_img Listing_prog.B_prog_listing
    (PAImg_prog.PI_prog_B (rc := rc)) W mem m).
  { split; [|exact Hm1]. apply PresetCfnB.val_mem_of_aview.
    replace (@PRH_Base.pi_gz_most PresetCfnB.preset_prh_img) with 8%nat by (vm_compute; reflexivity).
    exact Hm2. }
  assert (Hown : @PRH_Base.prh_own rc PresetCfnB.preset_prh_img Listing_prog.B_prog_listing
    (PAImg_prog.PI_prog_B (rc := rc)) W mem o).
  { split; [|exact Ho1]. apply PresetCfnB.val_mem_of_aview.
    replace (@PRH_Base.pi_gz_own_ran_out PresetCfnB.preset_prh_img) with 1%nat by (vm_compute; reflexivity).
    exact Ho2. }
  destruct (@PresetCfnB.prh_ledger_nil_of_pinv rc Listing_prog.B_prog_listing (PAImg_prog.PI_prog_B (rc := rc))
    YD2l.TfibB ly S W mem cnt ran m o HLR Hmost Hown) as (pk & Hled).
  unfold Ent102CutsB.ec_pre. subst E.
  cbn [Ent102CutsB.e_ly Ent102CutsB.e_S Ent102CutsB.e_W Ent102CutsB.e_regs Ent102CutsB.e_mem Ent102CutsB.e_md
    Ent102CutsB.e_p Ent102CutsB.e_n Ent102CutsB.e_pl Ent102CutsB.e_cnt Ent102CutsB.e_ran Ent102CutsB.e_sm
    Ent102CutsB.e_os Ent102CutsB.e_i0 Ent102CutsB.e_H0 Ent102CutsB.e_hist0 Ent102CutsB.e_x].
  (* afn_pre_x at ARx := ARcf /\ xs_placed_cf, from afn_pre_cf (ARcf) and the pre's xs_placed_cf *)
  split.
  { unfold PresetCfnB.afn_pre_cf, YCbqG.afn_pre_x in HA |- *. destruct HA as (HAR & HAr).
    split; [split; [exact HAR | exact Hxs] | exact HAr]. }
  split; [exact Hs0|].
  split; [exact Hfrm|].
  split; [exact Hra|].
  split; [exact Ha0|].
  split; [exact Ha1|].
  split; [exact Hpn|].
  split; [exact Hlen|].
  split; [exact Hgarr|].
  split; [exact Hfr|].
  split; [exact Hnp|].
  (* the exact run position at the entry: iface_room_pos_entry at os' := [] *)
  split.
  { pose proof (PresetCfnB.iface_room_pos_entry _ _ os [] H0 hist S Hat) as Hp0. rewrite app_nil_r in Hp0.
    exact Hp0. }
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact Hbb|].
  split; [exact Haro|].
  split; [exists pk, m, o; exact Hled|].
  split; [exact HSIO|].
  split; [exact Hc1|].
  split; [exact Hc2|].
  (* the hull closed set: the slot pre's run room's third part *)
  split; [exact Hlos|].
  split; [exact Hmn|].
  (* the live real stack at the entry: the pre's last conjunct (tfibsegs = pa_segs PI_prog_B by conversion) *)
  split; [exact Hup|].
  split; [exact Hpay8|].
  exact Hwild. }
(* 3. THE WALK: entry_B_walk at E, from the slot call's configuration (cut_start E) *)
pose proof (@Ent102TopB.entry_B_walk fx rc CfImgB.CfImg_B PresetCfnB.preset_prh_img
  (@PRH_Base.prh_room_live_a8 CfParamsPreset.CfParams_preset) (PAImg_prog.PI_prog_B (rc := rc)) YD2l.TfibB
  PresetCfnB.preset_sink_head PresetCfnB.RA_LLVMF Ent102InstB.ia_empty Ent102InstB.ia_mod_at Ent102InstB.ia_stamp
  Ent102InstB.ia_sio Ent102InstB.ia_sio_img ccut lcut E HH W
  (@cfg_at fx (@YC4aP.pa_segs rc Listing_prog.B_prog_listing (PAImg_prog.PI_prog_B (rc := rc)))
    (@YC4aP.pa_sigma rc Listing_prog.B_prog_listing (PAImg_prog.PI_prog_B (rc := rc)) YPsym.AS_LLVMFuzzerTestOneInput)
    regs mem md)
  (conj HP (conj eq_refl eq_refl))) as HWk.
(* 4. SRr -> srealizes: at checksum_shape LIBK pl (m_fs md) K is the leaf K (LL 0 (m_fs md) []) *)
match goal with |- srealizes ?sg ?c _ => change (srealizes sg c (K (LL 0 (m_fs md) []))) end.
refine (HWk HAI (K (LL 0 (m_fs md) [])) _).
intros W' c' Hle HAI' Hret.
apply (HK (LL 0 (m_fs md) []) W' c' Hle HAI').
(* 5. cut_ret -> the return configuration and preset_lib_post_x *)
subst E.
destruct Hret as (ly' & S' & regs' & mem' & md' & k & peak' & cnt' & ran' & (fy & Hfz & Hfk & Hc') & (WS & HJ & Hwb) &
  Hpres & Ha0' & Hperm & (most' & own' & HLG) & Hcnt' & HSIO' & HRL' & (trp & hist' & Hpos) & Hpl & Hmn').
pose proof (YCbqG.ajxR_io HJ) as Hos.
pose proof (YCbqG.ajxR_ar HJ) as (HAR' & Hxs').
exists fy, ly', S', regs', mem', md', k.
split.
{ rewrite Hc'. cbn [Ent102CutsB.e_regs]. unfold cfg_at. rewrite Hra. reflexivity. }
split; [exact Hfz|].
split; [exact Hfk|].
unfold PresetCfnB.preset_lib_post_xR.
(* the journal: ARx = ARcf /\ xs_placed_cf weakened to ARcf (its only occurrence, the first conjunct); the budget *)
split.
{ exists WS. split.
  - unfold YCbqGwild.wbudget in *. pose proof Ent102CutsB.ec_wk_values as V.
    destruct V as (_ & _ & _ & _ & _ & _ & _ & _ & V1 & V2). rewrite V1 in Hwb. rewrite V2. lia.
  - unfold PresetCfnB.ajournal_cfwR, YCbqG.ajournal_xwR, YCbqG.ajournal_xbR in HJ |- *.
    destruct HJ as (_ & HJr). exact (conj HAR' HJr). }
(* the run room one model call later: room_live_cf and iface_room_post_of_pos_end at cut_ret's exact position *)
split.
{ split; [exact HRL'|]. destruct trp as [[o1 o2] o0].
  exact (PresetCfnB.iface_room_post_of_pos_end _ _ os o1 o2 o0 _ H0 hist' S' Hpos eq_refl). }
split; [exact Hpres|].
split; [exact Ha0'|].
split; [exact Hperm|].
(* the fd table and the file system: the journal's aos_step at the empty footprint (no sink token) *)
assert (Hcl : ~ YI16.sink_open_fp []) by (intros (r & Hin & _); destruct Hin).
destruct (YCbq.aos_step_closed [] md md' Hcl Hos) as (Efd & Efsys & _ & _).
split; [intros fd; unfold m_fds; rewrite Efd; reflexivity|].
split; [unfold m_fs; rewrite Efsys; reflexivity|].
split; [reflexivity|].
split; [reflexivity|].
split; [exact Hsorted|].
(* PINV at the end: the ledger at rest (Lam = []) and the stdio half *)
split.
{ exists cnt', ran'.
  destruct (@PresetCfnB.pinv_ledger_of_prh_ledger_nil rc Listing_prog.B_prog_listing (PAImg_prog.PI_prog_B (rc := rc))
    _ _ _ _ _ _ _ _ _ _ _ HLG) as (HLR' & _).
  split; [split; [exact HLR' | exact HSIO'] | exact Hcnt']. }
split; [exact I|].
split; [exact Hpl|].
split; [exact Hxs'|].
exact Hmn'.
Qed.

Print Assumptions preset_lib_x_stmt_B_holds.
Set Printing Implicit.
Check preset_lib_x_stmt_B_holds.
(* the slot pre as elaborated: its last conjunct's segs, spZ and binders (header item (13)) *)
Print PresetCfnB.preset_lib_pre_x.
Unset Printing Implicit.
