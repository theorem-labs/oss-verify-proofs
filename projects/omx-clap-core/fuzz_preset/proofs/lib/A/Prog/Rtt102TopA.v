(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PutStringB.v, with its module paths and module names changed; 139 of its 173 lines of code are new or changed and 224 lines of the source are left out. *)
(* fuzz_preset, image A' (asan, sha256 1be0f53d96cb9d6c, unstripped twin bff8519bbe3ea0e4): THE COMPOSITION of
   round_trip_text's walk ON THE #102 PINS (WalkRtt102 for the text owner), ON THE BATCH KIT'S CUT. The kit's text tround_trip_text_specX
   (lib/A/PRH_FnCheck.v:1172, blob c40cf3fdcd2a, of the batch kit head 7cdbb61b5fa0, merged into this lane at
   c46ea8f2977) at image A', from the seven stretch tops of the cut layer Rtt102Cut.v and its composition
   rtt_text_of_segs (Qed):
     X   Rtt102XA.rtt_seg_x_A        CK  Rtt102CKA.rtt_seg_ck_A     O2  Rtt102O2A.rtt_seg_o2_A
     CMP Rtt102CmpA.rtt_seg_cmp_A    F   Rtt102FA.rtt_seg_f_A       T   Rtt102TA.rtt_seg_t_A_cond
     E   Rtt102EA.rtt_seg_e_A
   THE FIVE NAMED PREMISES OF THE PRE-CUT TOP (f85f15b123a), AT THE CUT:
     RTT_UNIVEND_CLAUSE  VANISHED. It was parse_noting's `In (text + len) DW`; the cut's tparse_noting_specX
                         (PRH_FnCheck.v:596-730; :615-616 records the removal) takes no membership of the cursor end and
                         DW is gone, so CMP states RTT_SEG_CMP directly (RTT_UNIVEND_CLAUSE, rtt_at_cmp_ue,
                         rtt_seg_cmp_A_of_univend deleted).
     re_K0_REFUTE_PJW    DISCHARGED BY ONE CITATION: the cut's PRH_FnWriter.tpj_write_specX (blob d89d3c67b78c) IS
                         DeadK1's text with rp_sm := ReaderRes.jr_strtod and DW dropped (token diff, Rtt102EA.v
                         header); it is now the callee-text Section hypothesis TPJW, like TPJF / TFF / TPN.
     rtt_src_ceil        DISCHARGED, and its statement NO LONGER MATCHES the cut: the cut's src_rd (PRH_Base.v:1652)
                         asks `p + Z.of_nat (length l) <= alloc_ceiling`, with no `+ 8`; CMP proves that form at the
                         parse_noting call (HSRC_CEIL, Rtt102CmpPNA.v:847) from AR_laws_x's alx_blocks at the live text
                         block (q - cf_head, capw + cf_head) and len < capw. (Even the old `+ 8` form now follows from
                         LAWS: AR_laws_x gained field alx_blocks_ceil8, ARx_blocks_ceil8_law.)
     RTT_T_AMR8          DISCHARGED by LAWS: AR_laws_x's new field alx_blocks_hi (ARx_blocks_hi_law,
                         kHighMemBeg <= p -> kHighMemBeg + 16 <= p for a live block).
     RTT_T_TRACE_AT      THE ONE PREMISE LEFT, restated for the cut's state-free prhtx_trace (PRH_FnTx.v:193-196):
                         (U) the realloc site's universe fact `inU (as_universe B) (unwind_of_chain cf_pc_realloc_ra0
                         ((t, pi_ret_tx_realloc, t) :: ch))` alone (Rtt102TA.v RTT_T_TRACE_AT), owner a Theorem Labs lane /
                         the image binding of B, TRUE at A' (rtt_t_trace_at_A below, from WildRoomInstA.tx_trace_inU_A).
                         Its former second conjunct (S), the live real stack above the entry sp, is now the text's
                         own LAST PREMISE (the stack-premise text head 4b8f95c0455c, merged at fef9a8da787):
                         rtt_pre's 28th conjunct, read by Rtt102Cut.rtt_pre_up.
   VACUITY BEFORE 4b8f95c0455c (the record of 5f2e946f8533): STILL VACUOUS AT ITS INSTANCE, the exact clause
   RTT_T_TRACE_AT's (S) `forall D, rtt_pre D -> astack_up_x SEGS (ri_ly D) (ri_W D) (ri_sp D) (ri_mem D)`: tx_put's
   prhtx_trace asks `forall a, t - 16 <= a < ly_top ly -> aview .. <> None` at the record t = s1 + 24, rtt_pre gave
   presence only of [sp - STK, sp), and no AR_laws_x field can give [sp, ly_top) (YGcallStackUp.v's header), so (S)
   ranged over entry states with a hole above sp. The FIX (the text owner's ruling 10:58Z, landed as 4b8f95c0455c):
   tround_trip_text_specX takes `YGcallStackUp.astack_up_x segs ly W (spZ regs) mem` last, unguarded; the clause is
   now rtt_pre's own and RTT_T_TRACE_AT is (U) alone. The text's prh_univ_closure (4a / 4b, DW gone) is TRUE at A'
   (rtt_closure_at_A below, from PRH_Witness.prh_univ_closure_witness_A).
   VACUITY AFTER 4b8f95c0455c, RE-CHECKED ON THE MERGED TREE: GENUINE AT ITS INSTANCE as far as this walk can check.
   No named premise is false at A': the one left, RTT_T_TRACE_AT (U), is TRUE there (rtt_t_trace_at_A); the text's
   prh_univ_closure is TRUE there (rtt_closure_at_A); the text's wild room of prh_wk F_round_trip_text = 32 fits A''s
   universe (rtt_wild_room_init_A, re-derived from WildRoomInstA.A_wmax through K_LLVMF = 140). The new last premise
   astack_up_x is NOT FREE (the stack-up prover's control rtt_up_ctl_hole_A: false at any state hiding a byte of
   [sp, ly_top)) and is MET at the real check_round_trip call state given check_round_trip's own entry fact
   (YGcallStackUp.astack_up_at_xwR at Crt102Arms.v:1102-1109; first rtt_up_at_call_A, a witness at commit 5208cc4f6eb0); that entry fact is the
   chain 4b8f95c0455c lays up to LLVMFuzzerTestOneInput's slot pre (PresetCfnA.preset_lib_pre_x, owner: the driver interface owner),
   rooted at the initial state by YGcallStackUp.astack_up_init under the start-up residuals (a start-up proof still
   to write, as PRH_FnCheck.v's note on tcheck_round_trip_specX says). AT THE TRACE-AT STATE WITH THE ZONE PRESENT:
   each tx call's PRH_FnTx.prhtx_trace is DERIVED, not assumed - Rtt102TA.rtt_t_trace_of gives [rect - 16, sp) from
   the journal's window clause and [sp, ly_top) from rtt_pre_up through the journal's high-memory keep, and the
   unwinder trace from (U) at any tail - so no clause of the stretch quantifies over a state with a hole in the zone.
   What this walk does not witness are its Section hypotheses (callee texts, engine and frame-class laws, image
   binding of B), each with its owner in its stretch's header.
   The Section hypotheses are the UNION of the seven stretches' (callee texts, engine and frame-class laws, image
   binding of B; each owner and discharge route in its stretch's header); cp := CfParams_preset (CMP fixes it). Every
   stretch is applied BY POSITION with every instance argument named (PA := PI_prog_A, PI := prh_img_A, fx := the
   Section's fx), from the signatures Rtt102TopProbe.v prints.
   RULE 24, PORT OR WHY (WalkRtt102b.Rule24RttPort's record, the lane's
   r24-paragraph, with its per-file evidence table). proof-index round_trip_text exits 0 with released proofs
   for the plain build (lib/Prog, 0x149b4) and the UBSan build (lib/U/Prog, lib/U/Prog/CF, 0x14f2c) only; no ASan
   proof exists. Each round_trip_text_holds proves round_trip_text_contract: from reader_env, the ledger and
   rtt_rooms, the void function returns with doc's tree kept, the ledger advanced by wcalls + tcalls, and copy, when
   given, holding the read-back over new blocks sized by lsz (ttrace t). The CF copy proves it under SRCF's cut-free,
   uniform SR; round_trip_text_holds_w only replaces the pj_write_hyp premise by pj_write's contract. RttEntry and the
   seven RttStg* stages cut the body at callee returns (Tx1 at +40 after pj_write, End at +204 after fuzz_free); each
   stage runs RttRunsA / RttRunsB Exec.evt lemmas at absolute addresses over rsegs, framed by RttGlue's rstep algebra.
   A' runs a different function: the #102 source returns int, adds a failed field, two out_of_memory exits and
   parse_noting, and frees before same; ASan adds a fake frame and shadow stores. This walk also cuts at callee
   returns, so RT_PJW, RT_TXE, RT_O2 and T's inner seams fall at released stage points, but F and O2 cover new code,
   CMP spans Cmp, Same's free and Ff, CK spans Same's same and End's copy, and X adds the frame release. RttEntry,
   RttStg*, RttRunsA / RttRunsB and RttGlue are therefore NOT PORTED: their addresses, rsegs runs and AllocAPI /
   ResForm frame have no meaning under AR_laws_x, aview / shadow_addr, ajournal_x and the kit's prh_* text; this walk's
   Rtt102* files of similar role (Rtt102Cut for RttBase, the FR1Kit keeps for RttGlue, the stretches for RttEntry and
   the RttStg stages) are coincidences of role, not ports. The MODEL carries over: the kit's text restates the released
   contract's shape over the plain proof's WriterValue, PjRoundTrip and ReaderRes files (the same blobs), and this walk
   PORTS FROM lib/Prog/RttModel.v (blob 6e31c633f2b8 at the cut, the re-addressed released 9d18e09d2be0) its image-free
   wdoc_split (as Rtt102TGlue rtt_t_wdoc) and rtt_maxrun (as Rtt102CmpLib rcl_maxrun) by cited restatement, not by
   Require: RttModel.vo does build on the #102 pins (a target of this commit's build), but it Requires the plain image
   (Img0, Contract) and checks plain-image bytes (img_empty / img_nl), which would put the plain build into the A'
   walk's closure for two image-free equations. Step, chain and writer lemmas come from the unreleased old-pin H5Rtt
   walk (the H2H5 walk head 1934271f1f40). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive YGcallMx YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0dcf YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YSRrG YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt PresetSecTotal PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnCheck PRH_FnAlloc PRH_FnEx PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnTx PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
(* the instance witnesses below: A''s universe, code record, CfImg and the kit's closure witness *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require ACej AF0l CfImgA WildRoomInstA PRH_Witness.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Rtt102Cut.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Rtt102XA Rtt102CKA Rtt102O2A Rtt102FA Rtt102EA
  Rtt102CmpA Rtt102TA.
Import ListNotations.
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.

Section top. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
#[local] Existing Instance CfParamsPreset.CfParams_preset.
#[local] Existing Instance prh_img_A.
Context {RF : PrhRoomFree (cp := CfParamsPreset.CfParams_preset) (RL := RL)}.
#[local] Notation CP := CfParamsPreset.CfParams_preset.
#[local] Notation PA := (PI_prog_A).
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation PST := (@prh_pst prh_img_A).
(* the world relation of every journal of the walk (Rtt102Cut.v RZW) *)
#[local] Notation RZW := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variables (CTX0 : list (list Z)).

(* ---- the union of the seven stretches' Section hypotheses (text verbatim from each stretch) ---- *)
(* every stretch: the engine laws *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* X, E *)
Hypothesis OWNLOW : ARx_owned_low_law SEGS B ARx.
(* X: the inline release (YGcallSx.aj_flag_store_x's forms) *)
Hypothesis ASFX : forall ly S Hp W mem md mem' md' cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aview SEGS (w_H W) mem' (flag_addr ly cid pos) = Some 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> a <> flag_addr ly cid pos -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, aview SEGS (w_H W) mem a <> None -> aview SEGS (w_H W) mem' a <> None) ->
  m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
  (forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
  ARx ly (stack_free_state cid pos S) Hp W mem' md'.
Hypothesis FFLX : forall ly S Hp (W : world SEGS) mem md cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aowned B ly S (flag_addr ly cid pos) /\ (app_addr (flag_addr ly cid pos) /\ ~ in_img SEGS (flag_addr ly cid pos)).
Hypothesis SFX : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  exists l1 l2, frames S = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos S) = l1 ++ l2.
Hypothesis FFLP : forall ly S Hp (W : world SEGS) mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  apresent (w_H W) mem (flag_addr ly cid pos).
(* X, CK, F, E, CMP *)
Hypothesis HW : prh_head_wide.
(* CK: the callee texts *)
Hypothesis TSAME : forall fx' : YK11.FPState, tsame_specX (fx := fx') (PI := prh_img_A) (PA := PA) B ARx SK DOC_D.
Hypothesis TPJF : forall fx' : YK11.FPState,
  tpj_free_specX (fx := fx') (PI := prh_img_A) (PA := PA) B ARx SK CTX0 DOC_D.
Hypothesis AMCPY : forall fx' : YK11.FPState,
  YGcallMxmn.aintrin_realizes_xm (fx := fx') SEGS B ARx OCpy (SIGMA AS___asan_memcpy).
(* O2, F: fuzz_alloc_ran_out's text *)
Hypothesis TFARO : forall fx' : YK11.FPState,
  @tfuzz_alloc_ran_out_specX fx' rc CP prh_img_A RL A_prog_listing PA B ARx SK.
(* E, CMP: the image binding of B (PALib; at the A' binder palib_A) *)
Hypothesis PAL : PALib (L := A_prog_listing) (PI := PA) B.
(* E *)
Hypothesis pal_stack_malloc1 : SIGMA AS___asan_stack_malloc_1 = pc_stack_malloc (as_code B) 1.
Hypothesis pal_uar_img : IMG_LO <= as_uar_cell B /\ as_uar_cell B + 4 <= IMG_TOP.
(* E, CMP *)
Hypothesis pal_pst_static : forall a, Exists (in_zr a) PST ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis HHEAD : cf_head = PresetReqAt.HEAD.
(* CK, CMP: the meter caps of CfParams_preset cover the run's section bounds (the texts' hull budgets; at
   CfParams_preset: CrsSeg_W1.crs_W1_HI_hull, by computation) *)
Hypothesis HI_hull : PresetSecTotal.SEC_N_CAP <= @YGcfNames.cf_kmax CP /\
  PresetSecTotal.SEC_T_CAP <= @YGcfNames.cf_T_max CP.
(* E: frame class 1 *)
Hypothesis ASM1 : astack_malloc_realizes_xm SEGS B ARx RT_CID.
Hypothesis SMX : forall ly S Hp W mem md cid, ARx ly S Hp W mem md -> 0 <= cid <= 10 ->
  count_cid cid (frames S) < fs_frames cid ->
  exists pos S', apath (stack_malloc cid S) [] (PFake cid pos, S') /\ (exists f, S' = set_fs f S) /\
    frames S' = (cid, pos) :: frames S /\ ~ In (cid, pos) (frames S).
(* CMP: the free wrapper's call form, model and re-hiding call post with its three laws (Rtt102CmpFFA.v's block; at the
   cf instance APOST := YGcallMxmnKeep.APOST_cf_keep), the string wrappers, the callee texts *)
Variable QM : astate -> Prop.
Variable QMm : astate -> (word -> option byte) -> Prop.
Variable mt : Z -> list Z -> YG00.M sptr.
Variable nmax : Z.
Variable WFx : astate -> Prop.
Hypothesis WFL : ARx_wf_law SEGS ARx WFx.
Hypothesis AMX : alloc_model_laws_x B QM mt nmax YG00cf.free_cf WFx.
Hypothesis QMQ : forall S mem, QMm S mem -> QM S.
Variable APOST : Z -> alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model ->
  (Z -> Prop) -> alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop.
Hypothesis POST_AR : apost_ar_law SEGS ARx APOST.
Hypothesis POST_J : apost_j_law (rc := rc) (SK := SK) SEGS B ARx RZW APOST.
Hypothesis POST_MN : forall stk ly S Hp W regs mem md (E : Z -> Prop) ly' S' W' regs' mem' md',
  APOST stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' ->
  YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem'.
Hypothesis AFREE : forall fx' : YK11.FPState,
  afree_realizes_xR (fx := fx') SEGS B ARx QMm YG00cf.free_cf RZW APOST.
Hypothesis QMR : forall ly S Hp W mem md, ARx ly S Hp W mem md -> qtight S -> room_live_cf S ->
  PresetHullBudget.hull_budget S [] ->
  arodata_okP SEGS (@pa_relro_lo _ A_prog_listing PA) (@pa_relro_hi _ A_prog_listing PA) B (aview SEGS (w_H W) mem) ->
  QMm S mem.
Hypothesis ACF : forall ly S Hp W regs mem md ch, acall_pre_x SEGS B ARx QMm ly S Hp W regs mem md ch ->
  YG0dcf.acall_pre_cf SEGS B ly S Hp W regs mem md ch.
Hypothesis STRCMP : forall fx' : YK11.FPState,
  @YGcallMxmn.astrcmp_realizes_xrom fx' SEGS B ARx (@pa_relro_lo _ A_prog_listing PA) (@pa_relro_hi _ A_prog_listing PA)
    (SIGMA AS___wrap_strcmp).
Hypothesis STRLEN : forall fx' : YK11.FPState,
  @YGcallMxmn.astrlen_realizes_xrom fx' SEGS B ARx (@pa_relro_lo _ A_prog_listing PA) (@pa_relro_hi _ A_prog_listing PA)
    (SIGMA AS___wrap_strlen).
Hypothesis TFF : forall fx' : YK11.FPState,
  @tfuzz_free_specX fx' rc CP prh_img_A RL A_prog_listing PA B ARx SK.
Hypothesis TPN : forall fx0 : YK11.FPState,
  tparse_noting_specX (fx := fx0) (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx SK CTX0.

(* T: the image binding of B and the two tx texts (the cut's PRH_FnTx.v, with K0-DEAD-TXPUT / K0-DEAD-TXVALUE and the
   wild budget), the memset row (Rtt102TA.v Section f, text verbatim) *)
Hypothesis zs_aligned : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow B).
Hypothesis img_shadow_vis_x : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> IMG_LO <= a < IMG_TOP ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
Hypothesis rtt_t_litnl_img : kept_img (PA := PA) B Rtt102TA.RTT_LITNL_A 1.
Hypothesis TXPUT : forall fx' : YK11.FPState,
  PRH_FnTx.ttx_put_specX (fx := fx') (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx SK CTX0.
Hypothesis TXVAL : forall fx' : YK11.FPState,
  PRH_FnTx.ttx_value_specX (fx := fx') (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx SK CTX0 DOC_D.
Hypothesis AIM : forall fx', aintrin_realizes_xm (fx := fx') SEGS B ARx OSet (SIGMA AS___asan_memset).
(* E: pj_write's text, the cut's PRH_FnWriter.tpj_write_specX (= DeadK1's, which re_K0_REFUTE_PJW restated; retired) *)
Hypothesis TPJW : forall fx' : YK11.FPState,
  PRH_FnWriter.tpj_write_specX (fx := fx') (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx SK CTX0 DOC_D.

(* ---- THE A' COMPOSITION: the kit's text at image A' from the seven stretches, with the ONE named premise left ---- *)
Theorem rtt_text_A_cond :
  (* C-TXTRACE (U) alone, owner a Theorem Labs lane / the image binding of B; TRUE at A' (rtt_t_trace_at_A below) *)
  Rtt102TA.RTT_T_TRACE_AT (ci := ci) B ->
  tround_trip_text_specX (fx := fx) (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx SK CTX0.
Proof.
intros HTR.
apply (@rtt_text_of_segs fx rc ci CP prh_img_A RL A_prog_listing PA B ARx SK CTX0).
- exact (@Rtt102XA.rtt_seg_x_A rc ci CP RL SK B ARx CTX0 LAWS OWNLOW ASFX FFLX SFX FFLP HW fx).
- exact (@Rtt102CKA.rtt_seg_ck_A rc ci CP RL B ARx SK CTX0 LAWS HW fx TSAME TPJF AMCPY HI_hull).
- exact (@Rtt102O2A.rtt_seg_o2_A rc ci CP RL fx B ARx SK CTX0 LAWS TFARO).
- exact (@Rtt102CmpA.rtt_seg_cmp_A fx rc ci RL RF B ARx SK CTX0 LAWS PAL QM QMm mt nmax WFx WFL AMX QMQ APOST POST_AR
    POST_J POST_MN AFREE QMR ACF pal_pst_static HW STRCMP STRLEN TFF TPN HHEAD HI_hull).
- exact (@Rtt102FA.rtt_seg_f_A fx rc ci CP RL B ARx SK CTX0 LAWS HW TFARO).
- exact (@Rtt102TA.rtt_seg_t_A_cond fx rc ci CP SK RL B ARx LAWS HW zs_aligned img_shadow_vis_x rtt_t_litnl_img CTX0
    TXPUT TXVAL AIM HTR).
- exact (@Rtt102EA.rtt_seg_e_A fx rc ci CP RL SK B ARx LAWS PAL pal_stack_malloc1 pal_uar_img pal_pst_static HW HHEAD
    ASM1 OWNLOW SMX CTX0 TPJW).
Qed.

End top.

(* ---- THE INSTANCE WITNESSES (the vacuity re-check in the header). At A' - code record AF0l.Tfib_code, universe
   ACej.Tfib_universe, CfImg_A, the driver's context [[0x814dc]] - the text's universe closure is TRUE, so is the
   one named premise RTT_T_TRACE_AT, and the text's wild room of prh_wk F_round_trip_text = 32 fits A''s universe:
   at the initial depot it is within the driver's K_LLVMF = 140 slots, which WildRoomInstA.wild_room_init_A derives
   from A_wmax (u_wmax ACej.Tfib_universe) through wild_room_run_fits_A (4 * K_LLVMF <= A_wmax), so this lemma
   re-derives the fit from whatever A_wmax the base's ACej gives. ---- *)
Lemma rtt_closure_at_A : forall B : asyms,
  as_code B = AF0l.Tfib_code -> as_universe B = ACej.Tfib_universe ->
  @prh_univ_closure prh_img_A B CfImgA.CfImg_A [[0x814dc]].
Proof. exact PRH_Witness.prh_univ_closure_witness_A. Qed.
Lemma rtt_t_trace_at_A : forall B : asyms, as_universe B = ACej.Tfib_universe ->
  Rtt102TA.RTT_T_TRACE_AT (ci := CfImgA.CfImg_A) B.
Proof.
intros B Hu. unfold Rtt102TA.RTT_T_TRACE_AT. intros t ch. rewrite Hu.
replace (@cf_pc_realloc_ra0 CfImgA.CfImg_A) with 0x53c74 by (vm_compute; reflexivity).
replace (@pi_ret_tx_realloc prh_img_A) with 0x84db0 by (vm_compute; reflexivity).
exact (WildRoomInstA.tx_trace_inU_A t t ch).
Qed.
Lemma rtt_wild_room_init_A :
  YCbqGwild.wild_room ACej.Tfib_universe [] (prh_wk F_round_trip_text) (st_depot YG00.init_state).
Proof.
apply (YCbqGwild.wild_room_le _ _ YCbqGwild.K_LLVMF); [|exact WildRoomInstA.wild_room_init_A].
change (prh_wk F_round_trip_text) with 32%nat. unfold YCbqGwild.K_LLVMF. lia.
Qed.
Check WildRoomInstA.A_wmax.

(* THE STATEMENT CHECK (the text owner's rule): implicits on, notations off - every FPState argument is the Section's fx and
   every PA / PI argument names the A' instance (PI_prog_A / prh_img_A) *)
Set Printing Implicit.
Unset Printing Notations.
Set Printing Width 4000.
Check @rtt_text_A_cond.
Set Printing Notations.
Unset Printing Implicit.
Print Assumptions rtt_text_A_cond.
Print Assumptions rtt_closure_at_A.
Print Assumptions rtt_t_trace_at_A.
Print Assumptions rtt_wild_room_init_A.
