(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Ent102SeamA.v, with its module paths changed; 17 of its 184 lines of code are new or changed and 11 lines of the source are left out. *)
(* omx-clap-core/fuzz_preset, image A' (asan, harness fix #102 pin sha256
   1be0f53d96cb9d6c2d5c92820c254e9db28e4830054a02631390e27c9547dc44, unstripped twin bff8519bbe3ea0e4): THE SEAM of the
   walk of LLVMFuzzerTestOneInput. The interface's slot statement preset_lib_x_stmt (lib/A/PresetCfnA.v:1127), EXACTLY as
   the driver of record takes it (lib/A/PresetD2pAPf.v:277, H_preset_lib_x_stmt_A), at the walk's fixed values:
     sm := ReaderRes.jr_strtod (the walk's ec_pre asks e_sm E = jr_strtod, lib/A/Ent102CutsA.v:289),
     iface_room_np := YGcfRoomLive.room_live_cf at CfParams_preset (= the driver's np_live_A by conversion),
     A_MOD_AT / A_STAMP := Ent102InstA.ia_mod_at / ia_stamp (the literals ec_img_A fixes),
     MT := ameter_triv (the driver's: its mo_ok / mo_le are True).
   PROOF: the walk's composed top lib/A/Prog/Ent102TopA.v entry_A_walk (its only premise is ec_hyps), at the A' instance
   (PI := preset_prh_img, RL := prh_room_live_a8, B := TfibB, SK := preset_sink_head, EC_RA := RA_LLVMF, EC_EMPTY :=
   ia_empty, EC_SIO := ia_sio), between the interface's pre and post:
   1. ec_hyps from the callee record (every ec_texts field IS the record's field by conversion, ec_frame_area is
      pcc_stack_malloc at LLVMF_FS_CLASS with pcc_stack_free), ec_img_A, the pre's universe conjunct (ech_univ), the
      budgets of Ent102PaySat.ec_pay_sat_preset and the interface's preset_no_refusal (ech_noref);
   2. the pre gives ec_pre at E := MkEcx ly S W regs mem md p n pl cnt ran jr_strtod os (length (hruns ..)) H0 hist;
   3. entry_A_walk gives SRr from cut_start to cut_ret;
   4. at checksum_shape, LIBK pl (m_fs md) K is K (LL 0 (m_fs md) []), the leaf the contract's continuation is fed with;
   5. cut_ret gives the return configuration and preset_lib_post_xR at R := YA0nH.wle' segs RZ_cf (the journal's ARx
      weakened to ARcf: ARx occurs only positively, as the journal's first conjunct; the budget 76 <= K_LLVMF = 140; the
      fd table and the file system from the journal's aos_step at the empty footprint).
   rule 24: no function proved (kind: interface seam; the function's walk is the cited Ent102TopA.entry_A_walk). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0o YK18 YA0i YA0n YG00 YG0f YG0n YG0d YCbq YI16 YM05 YO09 YC5d YCbp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqG YCbqGwild YGcfRoomLive YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Base Ent102CutsA PresetCfnA Ent102InstA Ent102PaySat.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Listing_prog PAImg_prog CfParamsPreset CfImgA AD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetHullPay.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Ent102TopA.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Theorem preset_lib_x_stmt_A_holds : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (XM_LIB XN_LIB : Z -> Z)
  (PAYLOAD_ROOM : list byte -> Prop),
  PresetCfnA.preset_lib_x_stmt (rc := rc) (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape)
    (L := Listing_prog.A_prog_listing) (PA := PAImg_prog.PI_prog_A (rc := rc)) (ci := CfImgA.CfImg_A) (fx := fx)
    ReaderRes.jr_strtod (YGcfRoomLive.room_live_cf (cp := CfParamsPreset.CfParams_preset)) AD2l.TfibB ameter_triv
    XM_LIB XN_LIB PAYLOAD_ROOM Ent102InstA.ia_mod_at Ent102InstA.ia_stamp.
Proof.
intros rc fx XM_LIB XN_LIB PAYLOAD_ROOM HCC.
(* the slot at the re-hiding relation (PresetCfnA.v preset_lib_contract_xR at R := wle' segs RZ_cf): the walk frees, so
   its top is at that relation and the contract's continuation takes `R W W'` there *)
unfold PresetCfnA.preset_lib_contract_xR.
intros ly S Hp W regs mem md p n pl cnt ran os H0 hist K HAI Hpre HK.
pose proof (PresetCfnA.preset_lib_pre_pay8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpre) as Hpay8.
(* the pre's last conjunct (PresetCfnA.v header item (13), astack_up_x at the entry) is Hup: it goes into the walk's
   ec_pre (Ent102CutsA.v), and segment L5b carries it to check_round_trip's call *)
destruct Hpre as (HA & Hs0 & Hfrm & Hra & Ha0 & Ha1 & Hpn & Hlen & Hgarr & Hfr & (Hnp & Hat & Hlos) & Hwild & Hbb & Haro &
  HHp & (HLR & HSIO) & Hc1 & Hc2 & _ & Hsorted & _ & Hxs & Hmn & Huniv & Hup).
subst Hp.
(* THE BUDGETS: Ent102PaySat's closed witnesses at CfParams_preset *)
destruct (Ent102PaySat.ec_pay_sat_preset rc Listing_prog.A_prog_listing (PAImg_prog.PI_prog_A (rc := rc)))
  as (ccut & lcut & Hcok & Hlok & Hpok).
(* 1. THE WALK'S HYPOTHESES at the instance *)
assert (HH : @Ent102CutsA.ec_hyps rc CfImgA.CfImg_A CfParamsPreset.CfParams_preset PresetCfnA.preset_prh_img
  (@PRH_Base.prh_room_live_a8 CfParamsPreset.CfParams_preset) Listing_prog.A_prog_listing
  (PAImg_prog.PI_prog_A (rc := rc)) AD2l.TfibB PresetCfnA.preset_sink_head PresetCfnA.RA_LLVMF Ent102InstA.ia_empty
  Ent102InstA.ia_mod_at Ent102InstA.ia_stamp Ent102InstA.ia_sio Ent102InstA.ia_sio_img ccut lcut).
{ pose proof (HCC fx) as C.
  refine {| Ent102CutsA.ech_frame_area := _; Ent102CutsA.ech_texts := _; Ent102CutsA.ech_img := _;
            Ent102CutsA.ech_univ := _; Ent102CutsA.ech_ccut_ok := Hcok; Ent102CutsA.ech_lcut_ok := Hlok;
            Ent102CutsA.ech_pay := Hpok; Ent102CutsA.ech_noref := _; Ent102CutsA.ech_hull_pay := _ |}.
  - (* the frame area: the record's memnorm-keeping class-1 frame call and its release *)
    split.
    + intros fy. exact (PresetCfnA.pcc_stack_malloc _ _ _ (HCC fy) _ PresetCfnA.llvmf_fs_class_ok).
    + exact (PresetCfnA.pcc_stack_free _ _ _ C).
  - (* the sixteen texts: the record's fields, by conversion (D1); the stack table by computation *)
    refine {|
      Ent102CutsA.et_fuzz_alloc_ran_out_reset := PresetCfnA.pcc_fuzz_alloc_ran_out_reset _ _ _ C;
      Ent102CutsA.et_fuzz_alloc_most := PresetCfnA.pcc_fuzz_alloc_most _ _ _ C;
      Ent102CutsA.et_check_no_overread := PresetCfnA.pcc_check_no_overread _ _ _ C;
      Ent102CutsA.et_fuzz_alloc_live := PresetCfnA.pcc_fuzz_alloc_live _ _ _ C;
      Ent102CutsA.et_fuzz_alloc_count := PresetCfnA.pcc_fuzz_alloc_count _ _ _ C;
      Ent102CutsA.et_fuzz_alloc_peak_reset := PresetCfnA.pcc_fuzz_alloc_peak_reset _ _ _ C;
      Ent102CutsA.et_parse_noting := PresetCfnA.pcc_parse_noting _ _ _ C;
      Ent102CutsA.et_fuzz_alloc_peak := PresetCfnA.pcc_fuzz_alloc_peak _ _ _ C;
      Ent102CutsA.et_check_bounded_alloc := PresetCfnA.pcc_check_bounded_alloc _ _ _ C;
      Ent102CutsA.et_fuzz_alloc_ran_out := PresetCfnA.pcc_fuzz_alloc_ran_out _ _ _ C;
      Ent102CutsA.et_check_as_written := PresetCfnA.pcc_check_as_written _ _ _ C;
      Ent102CutsA.et_pj_free := PresetCfnA.pcc_pj_free _ _ _ C;
      Ent102CutsA.et_check_reject_clean := PresetCfnA.pcc_check_reject_clean _ _ _ C;
      Ent102CutsA.et_check_reject_clean_starved := PresetCfnA.pcc_check_reject_clean_starved _ _ _ C;
      Ent102CutsA.et_read_members := PresetCfnA.pcc_read_members _ _ _ C;
      Ent102CutsA.et_check_round_trip := PresetCfnA.pcc_check_round_trip _ _ _ C;
      Ent102CutsA.et_stk := _ |}.
    apply Z.leb_le. vm_compute. reflexivity.
  - (* the image facts at the concrete instance *)
    exact Ent102InstA.ec_img_A.
  - (* the universe at the top's own context [[RA_LLVMF]]: the pre's conjunct before the last, six times *)
    constructor; exact Huniv.
  - (* no refusal at a consumer allocation: the interface's preset_no_refusal *)
    intros E U S0 n0 tr ns HW Hx Hf Hp0.
    exact (PresetCfnA.preset_no_refusal U (Ent102CutsA.e_sm E) (Ent102CutsA.e_x E) (Ent102CutsA.e_H0 E) S0 n0 tr ns
      HW Hx Hf Hp0).
  - (* THE HULL BUDGET AT A POSITION (route (b)), discharged ONCE here at cp := CfParams_preset: a position of at most 4
       calls leaves the cf layer's hull room for one call's sections (lib/A/PresetHullPay.v:73) *)
    exact PresetHullPay.hull_budget_of_room_pos. }
(* 2. THE PRE -> ec_pre at the entry context E (the run position of iface_room_pos_entry: index length (hruns ..)) *)
pose (E := @Ent102CutsA.MkEcx rc Listing_prog.A_prog_listing (PAImg_prog.PI_prog_A (rc := rc)) ly S W regs mem md p n
  pl cnt ran ReaderRes.jr_strtod os (length (PresetRun.hruns ReaderRes.jr_strtod (Ent102CutsA.ec_bytes pl) os)) H0 hist).
assert (HP : @Ent102CutsA.ec_pre fx rc CfImgA.CfImg_A CfParamsPreset.CfParams_preset PresetCfnA.preset_prh_img
  (@PRH_Base.prh_room_live_a8 CfParamsPreset.CfParams_preset) Listing_prog.A_prog_listing
  (PAImg_prog.PI_prog_A (rc := rc)) AD2l.TfibB PresetCfnA.RA_LLVMF Ent102InstA.ia_empty Ent102InstA.ia_sio E).
{ (* the entry ledger: g_most and g_own_ran_out at the values ledger_rest's last two conjuncts read *)
  pose proof HLR as (_ & _ & _ & _ & _ & _ & _ & (m & Hm1 & Hm2) & (o & Ho1 & Ho2)).
  assert (Hmost : @PRH_Base.prh_most rc PresetCfnA.preset_prh_img Listing_prog.A_prog_listing
    (PAImg_prog.PI_prog_A (rc := rc)) W mem m).
  { split; [|exact Hm1]. apply PresetCfnA.val_mem_of_aview.
    replace (@PRH_Base.pi_gz_most PresetCfnA.preset_prh_img) with 8%nat by (vm_compute; reflexivity).
    exact Hm2. }
  assert (Hown : @PRH_Base.prh_own rc PresetCfnA.preset_prh_img Listing_prog.A_prog_listing
    (PAImg_prog.PI_prog_A (rc := rc)) W mem o).
  { split; [|exact Ho1]. apply PresetCfnA.val_mem_of_aview.
    replace (@PRH_Base.pi_gz_own_ran_out PresetCfnA.preset_prh_img) with 1%nat by (vm_compute; reflexivity).
    exact Ho2. }
  destruct (@PresetCfnA.prh_ledger_nil_of_pinv rc Listing_prog.A_prog_listing (PAImg_prog.PI_prog_A (rc := rc))
    AD2l.TfibB ly S W mem cnt ran m o HLR Hmost Hown) as (pk & Hled).
  unfold Ent102CutsA.ec_pre. subst E.
  cbn [Ent102CutsA.e_ly Ent102CutsA.e_S Ent102CutsA.e_W Ent102CutsA.e_regs Ent102CutsA.e_mem Ent102CutsA.e_md
    Ent102CutsA.e_p Ent102CutsA.e_n Ent102CutsA.e_pl Ent102CutsA.e_cnt Ent102CutsA.e_ran Ent102CutsA.e_sm
    Ent102CutsA.e_os Ent102CutsA.e_i0 Ent102CutsA.e_H0 Ent102CutsA.e_hist0 Ent102CutsA.e_x].
  (* afn_pre_x at ARx := ARcf /\ xs_placed_cf, from afn_pre_cf (ARcf) and the pre's xs_placed_cf *)
  split.
  { unfold PresetCfnA.afn_pre_cf, YCbqG.afn_pre_x in HA |- *. destruct HA as (HAR & HAr).
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
  { pose proof (PresetCfnA.iface_room_pos_entry _ _ os [] H0 hist S Hat) as Hp0. rewrite app_nil_r in Hp0.
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
  (* the live real stack at the entry: the pre's last conjunct (tfibsegs = pa_segs PI_prog_A by conversion) *)
  split; [exact Hup|].
  split; [exact Hpay8|].
  exact Hwild. }
(* 3. THE WALK: entry_A_walk at E, from the slot call's configuration (cut_start E) *)
pose proof (@Ent102TopA.entry_A_walk fx rc CfImgA.CfImg_A PresetCfnA.preset_prh_img
  (@PRH_Base.prh_room_live_a8 CfParamsPreset.CfParams_preset) (PAImg_prog.PI_prog_A (rc := rc)) AD2l.TfibB
  PresetCfnA.preset_sink_head PresetCfnA.RA_LLVMF Ent102InstA.ia_empty Ent102InstA.ia_mod_at Ent102InstA.ia_stamp
  Ent102InstA.ia_sio Ent102InstA.ia_sio_img ccut lcut E HH W
  (@cfg_at fx (@YC4aP.pa_segs rc Listing_prog.A_prog_listing (PAImg_prog.PI_prog_A (rc := rc)))
    (@YC4aP.pa_sigma rc Listing_prog.A_prog_listing (PAImg_prog.PI_prog_A (rc := rc)) YPsym.AS_LLVMFuzzerTestOneInput)
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
{ rewrite Hc'. cbn [Ent102CutsA.e_regs]. unfold cfg_at. rewrite Hra. reflexivity. }
split; [exact Hfz|].
split; [exact Hfk|].
unfold PresetCfnA.preset_lib_post_xR.
(* the journal: ARx = ARcf /\ xs_placed_cf weakened to ARcf (its only occurrence, the first conjunct); the budget *)
split.
{ exists WS. split.
  - unfold YCbqGwild.wbudget in *. pose proof Ent102CutsA.ec_wk_values as V.
    destruct V as (_ & _ & _ & _ & _ & _ & _ & _ & V1 & V2). rewrite V1 in Hwb. rewrite V2. lia.
  - unfold PresetCfnA.ajournal_cfwR, YCbqG.ajournal_xwR, YCbqG.ajournal_xbR in HJ |- *.
    destruct HJ as (_ & HJr). exact (conj HAR' HJr). }
(* the run room one model call later: room_live_cf and iface_room_post_of_pos_end at cut_ret's exact position *)
split.
{ split; [exact HRL'|]. destruct trp as [[o1 o2] o0].
  exact (PresetCfnA.iface_room_post_of_pos_end _ _ os o1 o2 o0 _ H0 hist' S' Hpos eq_refl). }
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
  destruct (@PresetCfnA.pinv_ledger_of_prh_ledger_nil rc Listing_prog.A_prog_listing (PAImg_prog.PI_prog_A (rc := rc))
    _ _ _ _ _ _ _ _ _ _ _ HLG) as (HLR' & _).
  split; [split; [exact HLR' | exact HSIO'] | exact Hcnt']. }
split; [exact I|].
split; [exact Hpl|].
split; [exact Hxs'|].
exact Hmn'.
Qed.

Print Assumptions preset_lib_x_stmt_A_holds.
Set Printing Implicit.
Check preset_lib_x_stmt_A_holds.
(* the slot pre as elaborated: its last conjunct's segs, spZ and binders (header item (13)) *)
Print PresetCfnA.preset_lib_pre_x.
Unset Printing Implicit.
