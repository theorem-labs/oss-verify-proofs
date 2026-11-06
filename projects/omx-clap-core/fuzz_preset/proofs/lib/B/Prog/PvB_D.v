(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/A/ACjr.v (equal, after the mapping, to the generic part of lib/YC4c.v) for libreac/fuzz_disco's program walk, over fuzz_disco's listing; mres_range states fuzz_disco.asan's image range as YImgTop's IMG_LO and IMG_TOP in place of cgif's literals; cgif's PC_INIT, lzw_MR, lzw_tabs and the kept_ctx/kept_ctx_m tactics of cgif's 72-byte LZW context block are left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoACjr.v, with its module paths changed; 136 of its 271 lines of code are new or changed and 109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/PRW_StepKit.v, with its module paths and module names changed; 1086 of its 1137 lines of code are new or changed and 220 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PvB_A.v, with its module names and numbers changed; 736 of its 797 lines of code are new or changed and 1076 lines of the source are left out. *)
(* fuzz_preset image B' (asan-ubsan, #102), parse_value 0x8637c: segment D, the DISPATCH, from the C1
   cut (B 0x86484, back from skip_ws) to the number arm cut N (0x86598) or the shared exit cut (0x8664c), over the
   ONE image-B program listing (lib/B/Listing_prog.v) with the PA-listing engine on YCbqG's ajournal_x.
   WHAT THE CODE DOES: q's alignment / shadow checks, p = q->p, end = q->end; p >= end -> s5 = -1 -> exit; else p's
   checks, c = *p and the dispatch on c: the double quote -> v's checks, v->type = 4, parse_string(q) (PvB_D_CStr.v);
   '[' / '{' -> parse_items(q, v, 0 / 1) (PvB_D_CItems.v); 't' / 'f' / 'n' -> literal(q, word, type, v) with the
   .rodata words (PvB_D_CLit.v); any other byte -> N. HOW: engine runs from a symbolic state seated at C1 (every run
   from C1 carries aj_memnorm, YSRrMemnorm's runner twin, which the N cut, each call state (PvB_D_Call.v pvd_cs) and
   the exit cut need); the string arm's type-word store by the caller-frame runner's memnorm twin (PvB_D_Fr.v
   paj_run_x_fr_inv); each call stop handed to its arm through PvB_D_Call.v's pvd_cs. KIT: the #102
   reading texts at kit tree preset-tree-at-2026-10-29T18-51-23Z.tsv (sha256 c6f0aa3569e3; internal record)
   (post-implication form; the ledger statics most / own; frm_zero in fpre) and the cut PvB_Defs.v / PvB_Room.v:
   the p >= end exit's room post is PvB_Room.v rp_nil over pv_reader0's room keep (no allocator step since entry),
   inside pv_Qm (PvB_D_Lit.v pvD_Qm_none); each call arm composes its callee's room post with that keep (rp_nil / rp_call).
   Listing offsets: PvB_Defs.v / PvB_D_Call.v (DERIVED: B pc - 0x816cc). Rule 24: proves no function (kind: segment
   lemma). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06 YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqG YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar PjTree PresetRoomPos PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YStrtodRowX.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PvB_Defs PvB_Model PvB_D_Lit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PvB_D_Kit PvB_D_Fr PvB_D_Call.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PvB_D_CLit PvB_D_CItems PvB_D_CStr.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Instance PIB : PrhImg := prh_img_B.

(* ---- the segment's symbolic state at C1: every register its own atom; atoms 20 = q (s4), 19 = v (s3), 23 = the
   shadow base (s7), 2 = sp; extras 32 = p1 (the cursor after the white space), 33 = end = text + len, 34 = the byte
   at p1 (any value when p1 = end). One region: the cursor's p and end words. ---- *)
Definition PVD_Bx : sv := SOff 23 0.
Definition PVD_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition pvd_qreg : YP09.region :=
  YP09.mkRegion (Some 20%nat) 0 24 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0))].
Definition pvd_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
            (20%nat, mkAF 4096 (2 ^ 47 - 24) 3); (32%nat, mkAF 4096 (2 ^ 47) 0); (33%nat, mkAF 4096 (2 ^ 47) 0) ] [] [].
Definition pvd_ss : sstate := mkSS AF_pv_skw_ret sr_atoms [pvd_qreg] None pvd_facts.
Definition pvd_SH : list shent := [mkSHE 20 0 24].

Section c.
Context {fx0 : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Notation PSTX := (@prh_pst prh_img_B).

(* ---- Section hypotheses: the kit rule (YCbqG's 16-field record at the harness head length, as the instance
   AR_laws_x_xs gives it) ---- *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* the callee text of the literal arm: the literal (lib/A/PRH_FnReader.v tliteral_specX) *)
Hypothesis TLIT : tliteral_specX (fx := fx0) (PI := PIB) (PA := PA) B ARx SK.
(* MARKED image fact, discharged at PI_prog_B: no read-only byte is one of alloc.c's statics (S1ImgB.v pst_not_ro_B) *)
Hypothesis RONP : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> ~ Exists (in_zr a) PSTX.
(* MARKED image fact, discharged at PI_prog_B; the record gap V3 (lib/A/PRH_FnParse.v:87): the three .rodata words
   literal compares ("true" .str.6, "false" .str.7, "null" .str.8) read as their C strings wherever the read-only band
   reads as the image *)
Hypothesis LITCS : forall ly S Hp W mem md c, ARx ly S Hp W mem md ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> (c = 116 \/ c = 102 \/ c = 110) ->
  cstr_ok W mem (VAL (A_OBJ 2) + pvd_word_off c) (pvd_lit_word c).
Let ARM_LIT : pvd_lit_goal (fx0 := fx0) B ARx := PvB_D_CLit.pvd_call_lit B ARx LAWS TLIT RONP LITCS.
(* the callee text of the container arms, parse_items's (lib/A/PRH_FnParse.v tparse_items_specX), is pvD_holds's
   premise AT THE ENTRY'S DEPTH pe_d en (parse_items is called at the same depth; every context CTX), not a Section
   hypothesis over every depth: so parse_value at d follows from parse_items at d, the step lib/A/VrdUnit.v's depth
   induction closes the pair with *)
Let ARM_ITEMS : pvd_items_goal (fx0 := fx0) B ARx := PvB_D_CItems.pvd_call_items B ARx LAWS RONP.
(* the callee text of the string arm: the kit's parse_string (lib/A/PRH_FnReader.v tparse_string_specX CTX0 CW at the batch kit
   the budgeted wild-room form) *)
Hypothesis TPSTR : forall CTX0 CW, tparse_string_specX (fx := fx0) (PI := PIB) (PA := PA) B ARx SK CTX0 CW.
(* MARKED instance fact, discharged at lib/A/CfParamsPreset.v (cf_head = 16, preset source/alloc.c:31): a harness
   block's hidden head holds its 8-byte size word (PRH_Base.v prh_head_wide; PvB_X.v takes it in this spelling) *)
Hypothesis HHEAD : 8 <= cf_head.
(* MARKED image fact, discharged at PI_prog_B: alloc.c's five statics are image bytes, neither the runtime's own
   statics nor errno (FuzzFreeB.v / OwnB.v pal_pst_ok, with YC80x.v's PST_ok) *)
Hypothesis PSTOK : forall a, Exists (in_zr a) PSTX ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
(* MARKED image fact, discharged at PI_prog_B: the image's shadow is mapped in every allocator state
   (img_shadow_vis_cf, lib/Reusable/YGcfAmx2.v, over ARx) *)
Hypothesis pvh_img_vis : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> IMG_LO_B <= a < IMG_TOP_B ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
(* MARKED image fact, discharged at PI_prog_B: the image's zero-shadow ranges are whole granules *)
Hypothesis pvh_zs_al : forall r, In r (as_zero_shadow B) -> fst r mod 8 = 0 /\ snd r mod 8 = 0.
(* MARKED instance fact, discharged at PI_prog_B (PAImg_prog.v: pa_lo := IMG_LO_B, pa_hi := IMG_TOP_B): the
   per-instance image bounds of the kit's kept_img / kept_at lie inside the B' image box the shadow-visibility fact
   covers (PvB_A_Home.v PA_BOX, same text; the string arm reads the text's home through it) *)
Hypothesis PA_BOX : IMG_LO_B <= @pa_lo _ B_prog_listing PA /\ @pa_hi _ B_prog_listing PA <= IMG_TOP_B.
(* MARKED instance fact, discharged at lib/A/CfParamsPreset.v (CfParams_preset: cf_head = 16, preset source
   alloc.c:31; PresetReqAt.HEAD = 16, fuzz/alloc.c:28): the model's harness head is the instance's, so the string
   arm's parse_string events are parse_value's (PRH_FnReader.prhPs_evs_model; PvB_D_CStr.v HHD) *)
Hypothesis HHD : cf_head = PresetReqAt.HEAD.
Let ARM_STR : pvd_str_goal (fx0 := fx0) B ARx :=
  PvB_D_CStr.pvd_call_str B ARx LAWS TPSTR HHEAD PSTOK RONP pvh_img_vis pvh_zs_al PA_BOX HHD.

(* the call state of an arm whose stretch from C1 writes nothing: the C1 facts carried to the call memory *)
Lemma pvd_cs_nw : forall en ret p1 Y fa fl pos lyc Sc k (W' : world SEGS) regsC memC regs mem md',
  pv_keep_regs en regsC Y fa -> getr regsC 9 = w64 Y -> getr regsC 19 = w64 (pe_v en) ->
  getr regsC 20 = w64 (pe_q en) ->
  pv_frame (pe_regs en) (pe_sp en) Y fa fl pv_shadow_live W' memC ->
  In (0, pos) (frames Sc) -> fa = frame_addr lyc 0 pos -> fl = flag_addr lyc 0 pos ->
  (forall a, pe_sp en <= a < pe_sp en + pe_e en -> ~ inFP (pe_FP en) a ->
     aview SEGS (w_H W') memC a = aview SEGS (w_H (pe_W en)) (pe_mem en) a) ->
  pv_chain en lyc W' memC Y -> pv_reader0 B en pos p1 lyc Sc W' memC ->
  ajournal_x (SK := SK) SEGS B PSTX ARx (pe_STK en + pe_e en) (pe_sp en + pe_e en) (pe_FP en)
    (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_mem en) (pe_md en) [(0, pos)] lyc Sc (pe_Hp en) W' mem md' k ->
  (forall r, In r ([2; 3; 4; 8; 9; 18; 19; 20; 23; 26; 27]%bv : list (bv 5)) -> getr regs r = getr regsC r) ->
  getr regs 24 = w64 (SHADOW_OFF + pe_q en / 8) -> getr regs 1 = Z_to_bv 64 (BASE + ret) ->
  (forall x, rdW W' mem x = rdW W' memC x) ->
  (forall a, apresent (w_H W') memC a -> apresent (w_H W') mem a) ->
  YAkMemnorm.memnorm SEGS mem ->
  pvd_cs B ARx en ret p1 Y fa fl pos lyc Sc k W' mem regs mem md'.
Proof.
intros en ret p1 Y fa fl pos lyc Sc k W' regsC memC regs mem md' HKR R9 R19 R20 HFRM HinF Efa Efl HWIN HCH HRD HJ
  KR R24 R1 HEQ HGR HMNm.
assert (AV : forall a, aview SEGS (w_H W') mem a = aview SEGS (w_H W') memC a) by (intros a; apply aview_eq_of; apply HEQ).
pose proof HKR as (K2 & K8 & K18 & K26 & K27 & K23 & K3 & K4).
unfold pvd_cs.
split.
{ unfold pv_keep_regs. rewrite !KR by (cbn; tauto).
  split; [exact K2|]. split; [exact K8|]. split; [exact K18|]. split; [exact K26|]. split; [exact K27|].
  split; [exact K23|]. split; [exact K3 | exact K4]. }
split; [rewrite KR by (cbn; tauto); exact R9|].
split; [rewrite KR by (cbn; tauto); exact R19|].
split; [rewrite KR by (cbn; tauto); exact R20|].
split; [exact R24|].
split; [exact R1|].
split.
{ split; [|split; [exact HinF|split; [exact Efa|split; [exact Efl|split; [exact HJ|]]]]].
  - apply (pvd_frame_tr _ _ _ _ _ _ W' memC); [intros a _; apply pvd_mbyte_eq, HEQ | intros a _; apply HGR | exact HFRM].
  - intros a Ha Hn. rewrite AV. exact (HWIN a Ha Hn). }
split.
{ intros rd' Hrd'. apply HCH. intros a Ha. rewrite (Hrd' a Ha). apply AV. }
split; [eapply pv_reader0_ext; [exact HEQ | exact HRD]|].
split; [intros x _; reflexivity|].
split; [intros a Ha; exact Ha | exact HMNm].
Qed.
(* a byte off a range of change reads the same *)
Lemma pvd_aview_off : forall (H : word -> bool) (m m' : word -> option byte) lo hi a,
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> mrestrict H m x = mrestrict H m' x) ->
  0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS H m a = aview SEGS H m' a.
Proof.
intros H m m' lo hi a Hrel Ha Hn. unfold aview, mbyte.
rewrite (Hrel (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. exact Hn.
Qed.

(* the call state of the string arm: the stretch from C1 wrote the node's type word [v, v + 4) only, apart from the
   frame's bytes *)
Lemma pvd_cs_v4 : forall en ret p1 Y fa fl pos lyc Sc k (W' : world SEGS) regsC memC regs mem md',
  pv_keep_regs en regsC Y fa -> getr regsC 9 = w64 Y -> getr regsC 19 = w64 (pe_v en) ->
  getr regsC 20 = w64 (pe_q en) ->
  pv_frame (pe_regs en) (pe_sp en) Y fa fl pv_shadow_live W' memC ->
  In (0, pos) (frames Sc) -> fa = frame_addr lyc 0 pos -> fl = flag_addr lyc 0 pos ->
  (forall a, pe_sp en <= a < pe_sp en + pe_e en -> ~ inFP (pe_FP en) a ->
     aview SEGS (w_H W') memC a = aview SEGS (w_H (pe_W en)) (pe_mem en) a) ->
  pv_chain en lyc W' memC Y -> pv_reader0 B en pos p1 lyc Sc W' memC ->
  ajournal_x (SK := SK) SEGS B PSTX ARx (pe_STK en + pe_e en) (pe_sp en + pe_e en) (pe_FP en)
    (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_mem en) (pe_md en) [(0, pos)] lyc Sc (pe_Hp en) W' mem md' k ->
  (forall r, In r ([2; 3; 4; 8; 9; 18; 19; 20; 23; 26; 27]%bv : list (bv 5)) -> getr regs r = getr regsC r) ->
  getr regs 24 = w64 (SHADOW_OFF + pe_q en / 8) -> getr regs 1 = Z_to_bv 64 (BASE + ret) ->
  (forall x : word, ~ (pe_v en <= bv_unsigned x < pe_v en + 4) -> rdW W' mem x = rdW W' memC x) ->
  (forall a, apresent (w_H W') memC a -> apresent (w_H W') mem a) ->
  (forall a, (Y <= a < pe_sp en \/ fa <= a < fa + 64 \/ SHADOW_OFF + fa / 8 <= a < SHADOW_OFF + fa / 8 + 8) ->
     mbyte SEGS (rdW W' mem) a = mbyte SEGS (rdW W' memC) a) ->
  0 <= pe_sp en -> pe_sp en + pe_e en <= 2 ^ 64 ->
  YAkMemnorm.memnorm SEGS mem ->
  pvd_cs B ARx en ret p1 Y fa fl pos lyc Sc k W' memC regs mem md'.
Proof.
intros en ret p1 Y fa fl pos lyc Sc k W' regsC memC regs mem md' HKR R9 R19 R20 HFRM HinF Efa Efl HWIN HCH HRD HJ
  KR R24 R1 HREL HGR HFB Hs0 Hs1 HMNm.
pose proof HKR as (K2 & K8 & K18 & K26 & K27 & K23 & K3 & K4).
unfold pvd_cs.
split.
{ unfold pv_keep_regs. rewrite !KR by (cbn; tauto).
  split; [exact K2|]. split; [exact K8|]. split; [exact K18|]. split; [exact K26|]. split; [exact K27|].
  split; [exact K23|]. split; [exact K3 | exact K4]. }
split; [rewrite KR by (cbn; tauto); exact R9|].
split; [rewrite KR by (cbn; tauto); exact R19|].
split; [rewrite KR by (cbn; tauto); exact R20|].
split; [exact R24|].
split; [exact R1|].
split.
{ split; [|split; [exact HinF|split; [exact Efa|split; [exact Efl|split; [exact HJ|]]]]].
  - apply (pvd_frame_tr _ _ _ _ _ _ W' memC); [exact HFB | intros a _; apply HGR | exact HFRM].
  - intros a Ha Hn.
    assert (Hv : ~ (pe_v en <= a < pe_v en + 4)).
    { intros Hva. apply Hn. exists (pe_v en, pe_v en + 56). split; [unfold pe_FP; right; right; left; reflexivity|].
      cbn [fst snd]. lia. }
    rewrite (pvd_aview_off (w_H W') mem memC (pe_v en) (pe_v en + 4) a HREL ltac:(lia) Hv). exact (HWIN a Ha Hn). }
split; [exact HCH|].
split; [exact HRD|].
split; [exact HREL|].
split; [exact HGR | exact HMNm].
Qed.

(* the dispatch runs plain SRr (it frees nothing); its continuations reach the record's relation (pv_FINK), and the
   string and container arms, whose callees free, conclude in it (YA0nH.SRr'): the dispatch hands them its plain exit
   continuation lifted (PvB_D_Call.pvd_kxR_of) and returns their conclusion (YA0n.SRr_ret) *)
Lemma pvD_holds : forall en W' ms mdc, pv_pre B ARx en ->
  (forall CTX CTX0 CW, tparse_items_specX (fx := fx0) (PI := PIB) (PA := PA) B ARx SK (pe_d en) CTX CTX0 CW) ->
  pv_at_C1 B ARx en W' ms mdc ->
  (forall W2 ms2 md2, pv_at_N B ARx en W2 ms2 md2 -> SRr SEGS W2 (mkCfg ms2 md2) (pv_FINK B ARx en)) ->
  (forall W2 ms2 md2, pv_at_exit B ARx en W2 ms2 md2 -> SRr SEGS W2 (mkCfg ms2 md2) (pv_FINK B ARx en)) ->
  SRr SEGS W' (mkCfg ms mdc) (pv_FINK B ARx en).
Proof.
intros en W' ms mdc HPRE TPI HC1 KN KX.
destruct HC1 as (regs & mem & Y & fa & fl & pos & lyc & Sc & k & Ems & HKR & R9 & R19 & R20 & HBODY & HCHAIN & HRD0 & HMN).
pose proof HBODY as (HFRM & HinF & Efa & Efl & HJ & HWIN).
pose proof HKR as (R2 & R8 & R18 & R26 & R27 & R23 & R3 & R4).
pose proof HFRM as (HYr & HY32 & HPR0 & Vsav & Vfa48 & Vmagic & Vdesc & Vpc & Vfl & HPRfa & Hshlen & Gsh).
(* pv_pre's parts by type (robust to the cut file's conjunct order) *)
assert (HFPRE : fpre B ARx (pe_STK en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_regs en) (pe_mem en) (pe_md en)
  (pe_ch en)) by (unfold pv_pre in HPRE; tauto).
assert (HRDP : rd_pre (fx := fx0) B (pe_STK en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_regs en)
  (pe_mem en) (pe_Lam en) (pe_peak en) (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en) (pe_own en) (pe_e en)
  (pe_q en) (pe_text en)
  (pe_len en) (pe_p en) (pe_d en) (pe_tb en) (pe_v en)) by (unfold pv_pre in HPRE; tauto).
assert (HROOMp : rd_room (pe_S en) (pe_gt en)) by (unfold pv_pre in HPRE; tauto).
assert (HFRB : Z.of_nat (length (frames (pe_S en))) + Z.of_nat (Nat.succ (PjGrammar.MAXD - pe_d en)) <= fs_frames 0)
  by (unfold pv_pre in HPRE; tauto).
pose proof HFPRE as (HAFN & HRO & Hhi64 & _).
pose proof HAFN as (HAR0 & Hra_ok & Hra4 & Hgp & Htp & Hstk0 & Hpres0 & Hchain & HQT0).
pose proof HRDP as (Hfrm0 & Hmuniv & Hruniv1 & Hruniv2 & Hcur0 & Hwin & Hqlo & Hqhi & Hqra & Hsrc & Hhome &
  Hmaxrun & Hnode & Hqv & Htv0 & Hvwin & HLED0 & Hdmax & Hcntb & Htxc).
pose proof Hwin as (He0 & He16 & Hetop & Hepres).
pose proof HRD0 as (Hfrs & Habl & Hbb & HROOMc & HCUR & HSRC & HHOME & HVEQ & HVRA & HLEDc & HRPc).
pose proof HCUR as (Vp1 & Vend & Vdep & Hqrw & Hq8 & Htx0 & Htx62 & Hp1r & Htblen & Gtb & Hqt & Hd32).
pose proof (ajx_ar HJ) as HAR. pose proof (ajx_ly HJ) as Hly. pose proof (ajx_secs HJ) as Hsecs.
pose proof (ajx_wle HJ) as Hwle. pose proof (ajx_io HJ) as Hio. pose proof (ajx_frs HJ) as Hfrs'.
pose proof (ajx_nev HJ) as Hnev. pose proof (ajx_k HJ) as Hk0. pose proof (ajx_hi HJ) as J1.
pose proof (ajx_blk HJ) as J2. pose proof (ajx_img HJ) as J3. pose proof (ajx_frm HJ) as J4.
pose proof (ajx_gone HJ) as Jgone. pose proof (ajx_pres HJ) as Hpres. pose proof (ajx_stk HJ) as Hstk.
pose proof (ajx_extra HJ) as J5. pose proof (ajx_qt HJ) as HQT.
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
pose proof Hstk as (Hsp16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
set (sp0 := pe_sp en) in *. set (ee := pe_e en) in *.
set (q := pe_q en) in *. set (v := pe_v en) in *. set (text := pe_text en) in *. set (len := pe_len en) in *.
change (spZ (pe_regs en)) with sp0 in *.
set (p1 := text + len - Z.of_nat (length (PjGrammar.skip (pe_rest en)))) in *.
set (c0 := hd 0 (PjGrammar.skip (pe_rest en))).
assert (HSTKe : pe_STK en = Z.of_nat (S (PjGrammar.MAXD - pe_d en)) * 320 + 16560) by reflexivity.
assert (HSTK : 176 <= pe_STK en) by (rewrite HSTKe; nia).
(* ---- bounds ---- *)
pose proof Hsrc as (Hsbytes & Htx4096 & Htxceil & Htxam & Htxra & Hsrcrest).
assert (Hq_lo : sp0 <= q) by exact Hqlo.
assert (Hsp_lo : YM05.alloc_ceiling + 176 <= sp0) by (clear -Hceil Hslo HSTK; lia).
assert (Hsp_hi : sp0 + ee <= 2 ^ 47) by (clear -Hshi H47; lia).
assert (Hq4096 : 4096 <= q) by (clear -Hq_lo Hsp_lo CC1; lia).
assert (Htx47 : text + len <= 2 ^ 47)
  by (clear -Htxam Htblen; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Htxam; lia).
assert (Hlen0 : 0 <= len) by (clear -Htblen; lia).
assert (Hp1lo : text <= p1 <= text + len) by exact Hp1r.
(* ---- the environment and the entry symbolic state ---- *)
set (xtra := [Z_to_bv 64 p1; Z_to_bv 64 (text + len); Z_to_bv 64 c0]).
set (E := Eimg (Ereg regs xtra)).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (Eof : forall n : nat, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs xtra) n).
{ intros n Hn. unfold E, Eimg. cbn [ew]. replace ((A_TEXT <=? n)%nat) with false by (symmetry; apply Nat.leb_gt; lia).
  reflexivity. }
assert (HAE : env_agree 32 (Ereg regs xtra) E).
{ unfold E. split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. }
assert (E2 : ew E 2 = w64 Y) by (rewrite (Eof 2%nat ltac:(cbv; lia)); exact R2).
assert (E19 : ew E 19 = w64 v) by (rewrite (Eof 19%nat ltac:(cbv; lia)); exact R19).
assert (E20 : ew E 20 = w64 q) by (rewrite (Eof 20%nat ltac:(cbv; lia)); exact R20).
assert (E23 : ew E 23 = w64 SHADOW_OFF) by (rewrite (Eof 23%nat ltac:(cbv; lia)); exact R23).
assert (E32 : ew E 32 = w64 p1).
{ rewrite (Eof 32%nat ltac:(cbv; lia)). unfold xtra. cbn [ew Ereg Nat.ltb Nat.leb nth Nat.sub]. reflexivity. }
assert (E33 : ew E 33 = w64 (text + len)).
{ rewrite (Eof 33%nat ltac:(cbv; lia)). unfold xtra. cbn [ew Ereg Nat.ltb Nat.leb nth Nat.sub]. reflexivity. }
assert (E34 : ew E 34 = w64 c0).
{ rewrite (Eof 34%nat ltac:(cbv; lia)). unfold xtra. cbn [ew Ereg Nat.ltb Nat.leb nth Nat.sub]. reflexivity. }
assert (U2 : bv_unsigned (ew E 2) = Y) by (rewrite E2; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = q) by (rewrite E20; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = SHADOW_OFF) by (rewrite E23; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = p1) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = text + len) by (rewrite E33; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E pvd_ss (restrict (w_H W') ms)).
{ rewrite Ems, restrict_mkst_fx. unfold pvd_ss.
  replace (Z_to_bv 64 (BASE + AF_pv_skw_ret)) with (Z_to_bv 64 (VAL A_TEXT + AF_pv_skw_ret)) by reflexivity.
  apply pa_entry_st_ok_full.
  - unfold E; apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold pvd_qreg, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (chunk_ok_val SEGS E _ q 0 8 (SOff 32 0) p1);
        [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | cbn; lia | zside | rewrite Z.add_0_r; exact Vp1].
    + apply (chunk_ok_val SEGS E _ q 8 8 (SOff 33 0) (text + len));
        [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | cbn; lia | zside | exact Vend].
  - cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok pvd_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U20, U23, U32, U33. change (2 ^ 5) with 32. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat split; try lia. }
assert (HBx : U E PVD_Bx = SHADOW_OFF) by (unfold PVD_Bx; rewrite U_SOff, U23; reflexivity).
assert (SHOK : sh_ok SEGS PVD_Bx pvd_SH E (rdW W' (ms_mem ms))).
{ rewrite Ems. cbn [ms_mem]. unfold pvd_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W') mem E PVD_Bx 20 q 24 q 0 24);
    [| exact HBx | exact (U_atom E 20 q E20 ltac:(lia)) | lia | lia |].
  - apply (pvd_stack_ra B ARx LAWS lyc Sc (pe_Hp en) W' mem mdc q 24 HAR).
    + destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _). rewrite Elo. lia.
    + destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _). rewrite Ehi. lia.
  - intros x Hx. unfold SHADOW_OFF in *. lia. }
(* ---- the runner ---- *)
(* the memory normal form aj_memnorm (YAkMemnorm.memnorm, by conversion) rides along every run from C1: the N cut
   carries it (runner twins YC1fPx.v paj_run_x_inv / paj_run_to_x_inv, laws YSRrMemnorm.srr_inv_laws_memnorm_k; engine
   set preset-tree-at-2026-10-29T12-55-44Z.tsv (sha256 7967f42d1cd6; internal record)) *)
pose (RUN := paj_run_x_inv (SK := SK) (PL := PL_prog_B) (PI := PA) B PSTX ARx LAWS (YAkMemnorm.memnorm SEGS)
  (srr_inv_laws_memnorm_k SEGS)).
pose (RUNTO := paj_run_to_x_inv (SK := SK) (PL := PL_prog_B) (PI := PA) B PSTX ARx LAWS (YAkMemnorm.memnorm SEGS)
  (srr_inv_laws_memnorm_k SEGS)).
pose (BR := paj_branch (PI := PA)).
subst ms.
assert (HPM : YAkMemnorm.memnorm SEGS mem) by exact HMN.
(* ---- B 0x86484 .. 0x864b8: q's UBSan / ASan checks, p = q->p, end = q->end, then `bgeu p, end` ---- *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM PVD_Bspan.
{ intros a (r & Hin & Hr). unfold pvd_ss in Hin. cbn [ss_mem In] in Hin.
  destruct Hin as [<- | []]. unfold pvd_qreg in Hr. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. lia. }
psrr_branch_tok RUN BR HS SHOK PVD_Bspan.
- (* ---- p1 >= end: s5 = -1, to the exit ---- *)
  rewrite branch_geu_U, (U_atom E 32 p1 E32 ltac:(lia)), (U_atom E 33 (text + len) E33 ltac:(lia)) in Hc.
  apply negb_true_iff, Z.ltb_ge in Hc.
  assert (Ep1d : p1 = text + len - Z.of_nat (length (PjGrammar.skip (pe_rest en)))) by reflexivity.
  assert (Hsk0 : PjGrammar.skip (pe_rest en) = []) by (apply length_zero_iff_nil; lia).
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM PVD_Bspan AF_pv_exit.
  { intros a (r & Hin & Hr). cbn [add_cond ss_mem In] in Hin.
    destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. lia. }
  rewrite ?wvb_collapse in HJ.
  (* no region has a write window: the memory is the C1 memory, byte for byte *)
  assert (EQ1 : forall x, rdW W' (ms_mem ms) x = rdW W' mem x).
  { apply (pvd_nowin E (ss_mem pvd_ss)); [|exact HFr]. intros a (r & Hin & Hr). unfold pvd_ss in Hin.
    cbn [ss_mem In] in Hin. destruct Hin as [<- | []]. unfold pvd_qreg in Hr.
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. lia. }
  assert (EQ2 : forall x, rdW W' (ms_mem ms0) x = rdW W' (ms_mem ms) x).
  { eapply pvd_nowin; [|exact HFr0]. intros a (r & Hin & Hr). cbn [add_cond ss_mem In] in Hin.
    destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. lia. }
  assert (EQ : forall x, rdW W' (ms_mem ms0) x = rdW W' mem x) by (intros x; rewrite EQ2, EQ1; reflexivity).
  assert (GR : forall a, apresent (w_H W') mem a -> apresent (w_H W') (ms_mem ms0) a)
    by (intros a Ha; apply (apresent_grows _ _ _ a HG0), (apresent_grows _ _ _ a HG), Ha).
  assert (AVEQ : forall a, aview SEGS (w_H W') (ms_mem ms0) a = aview SEGS (w_H W') mem a)
    by (intros a; unfold aview; rewrite (pvd_mbyte_eq _ _ EQ); reflexivity).
  assert (KR : forall r, In r [2; 3; 4; 8; 18; 23; 26; 27]%bv -> getr (ms_regs ms0) r = getr regs r).
  { intros r Hr. pose proof (regs_kept_of_st_ok_pi _ _ _ regs xtra [2; 3; 4; 8; 18; 23; 26; 27]%bv HS HAE
      ltac:(vm_compute; reflexivity) r Hr) as H. exact H. }
  prreg HS (21%bv : bv 5) R21.
  pmkst HS.
  apply KX.
  exists fx0, (ms_regs ms0), (ms_mem ms0), Y, fa, fl, pos, lyc, Sc, (pe_Hp en), k, (-1).
  split; [reflexivity|]. split; [exact Hfrm0|]. split; [intros r _; reflexivity|].
  split.
  { unfold pv_keep_regs. rewrite !KR by (cbn; tauto). repeat split; assumption. }
  split; [rewrite R21; apply bv_eq; vm_compute; reflexivity|].
  split.
  { apply pv_body_x_of.
    split; [|split; [exact HinF|split; [exact Efa|split; [exact Efl|split; [exact HJ|]]]]].
    - apply (pvd_frame_tr _ _ _ _ _ _ W' mem); [intros a _; apply pvd_mbyte_eq, EQ | intros a _; apply GR | exact HFRM].
    - intros a Ha Hn. rewrite AVEQ. exact (HWIN a Ha Hn). }
  (* the exit cut's memory normal form (the runs'); the run position (no allocator step since entry: pv_reader0's)
     is inside pv_Qm *)
  split; [|exact HPM].
  eapply (pvD_Qm_none B ARx LAWS en pos p1 lyc Sc W' (ms_mem ms0) HPRE Ep1d Hsk0).
  eapply pv_reader0_ext; [exact EQ | exact HRD0].
- (* ---- p1 < end: the byte c at p1 ---- *)
  rewrite branch_geu_U, (U_atom E 32 p1 E32 ltac:(lia)), (U_atom E 33 (text + len) E33 ltac:(lia)) in Hc.
  apply negb_false_iff, Z.ltb_lt in Hc.
  assert (Ep1d : p1 = text + len - Z.of_nat (length (PjGrammar.skip (pe_rest en)))) by reflexivity.
  destruct (pvd_cons_of_len (PjGrammar.skip (pe_rest en)) ltac:(lia)) as (c & y & Hsk).
  assert (Ec0 : c0 = c) by (change c0 with (hd 0 (PjGrammar.skip (pe_rest en))); rewrite Hsk; reflexivity).
  pose proof Hcur0 as (_ & _ & _ & _ & _ & _ & _ & Hp0r & _).
  assert (Hrest1 : rest_atR (pe_tb en) text p1 = c :: y).
  { rewrite Ep1d, <- Hsk. destruct (pvm_skip_rest (pe_tb en) text len (pe_p en) Htblen Hp0r) as [H _]. exact H. }
  pose proof Hrest1 as Hrestf.
  unfold rest_atR in Hrest1. destruct (pvd_nth_skipn _ _ _ _ Hrest1) as [Hnth Hjl].
  destruct (Gtb (Z.to_nat (p1 - text)) Hjl) as [Vc Hc8]. rewrite Hnth in Vc, Hc8.
  replace (text + Z.of_nat (Z.to_nat (p1 - text))) with p1 in Vc by lia.
  assert (EQ1 : forall x, rdW W' (ms_mem ms) x = rdW W' mem x).
  { apply (pvd_nowin E (ss_mem pvd_ss)); [|exact HFr]. intros a (r & Hin & Hr). unfold pvd_ss in Hin.
    cbn [ss_mem In] in Hin. destruct Hin as [<- | []]. unfold pvd_qreg in Hr.
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. lia. }
  assert (GR1 : forall a, apresent (w_H W') mem a -> apresent (w_H W') (ms_mem ms) a)
    by (intros a Ha; apply (apresent_grows _ _ _ a HG), Ha).
  assert (Hp1N : pe_text en + pe_len en - Z.of_nat (length (c :: y)) = p1) by (rewrite Ep1d, Hsk; reflexivity).
  assert (U34 : bv_unsigned (ew E 34) = c) by (rewrite E34, Ec0; apply unsigned_lit_small; lia).
  (* the byte at p1: a new region over atom 32, and p1's shadow entry *)
  pose proof (st_ok_pi_add_region E _ _
    (YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))]) HS ltac:(vm_compute; reflexivity))
    as HS2.
  lazymatch type of HS2 with ?A -> ?Bd -> _ => assert (HA2 : A); [|assert (HB2 : Bd); [|specialize (HS2 HA2 HB2)]] end.
  { unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict].
    rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ p1 0 1 (SOff 34 0) c);
      [cbn [sv_denot]; rewrite U34, Z.add_0_r; reflexivity | cbn; lia | zside |].
    rewrite Z.add_0_r. intros kk Hk. rewrite (pvd_mbyte_eq _ _ EQ1). exact (Vc kk Hk). }
  { cbn [all_disjoint ss_mem add_cond]. split; [|exact I]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U32, U20. lia. }
  pose proof (st_ok_pi_add_fact E _ _ 32%nat (mkAF 4096 (2 ^ 47 - 1) 0) HS2) as HS3.
  lazymatch type of HS3 with ?A -> _ => assert (HA3 : A); [|specialize (HS3 HA3)] end.
  { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U32. rewrite Z.pow_0_r, Z.mod_1_r. lia. }
  clear HS HS2 HA2 HB2 HA3. rename HS3 into HS.
  assert (SHOK2 : sh_ok SEGS PVD_Bx (pvd_SH ++ [mkSHE 32 0 1]) E (rdW W' (ms_mem ms))).
  { apply Forall_app. split; [exact SHOK|]. constructor; [|constructor].
    apply (shent_ok_of_range SEGS (w_H W') (ms_mem ms) E PVD_Bx 32 text len p1 0 1);
      [| exact HBx | exact (U_atom E 32 p1 E32 ltac:(lia)) | lia | lia |].
    - pose proof HSRC as (_ & _ & _ & _ & Htxra1 & _).
      intros x Hx. destruct (Htxra1 x ltac:(rewrite Htblen; exact Hx)) as (s & Hs & Hok). exists s. split; [|exact Hok].
      rewrite <- Hs. apply aview_eq_of. apply EQ1.
    - intros x Hx. clear -Hx Htxam Htblen Hc Hp1lo.
      unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia. }
  clear SHOK. rename SHOK2 into SHOK.
  (* ---- B 0x864bc .. 0x864d8: p's UBSan / ASan checks, c = *p, then `blt 109, c` ---- *)
  paj_run_tok_x_inv RUN HS HJ SHOK HPM PVD_Bspan.
  { intros a (r & Hin & Hr). cbn [add_atom ss_mem add_cond In] in Hin.
    destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia. }
  rename Hc into Hpend.
  (* rd_pre's text / node apartness is guarded by 0 < len (the batch kit): here text <= p1 < end *)
  assert (Htv : text + len <= v \/ v + 56 <= text) by (apply Htv0; clear - Hp1lo Hpend; lia).
  clear Htv0.
  assert (UCg : forall E' : env, ew E' 34 = ew E 34 -> U E' (SExt false 8 (SOff 34 0)) = c).
  { intros E' HE'. rewrite U_zext, (U_atom E' 34 c) by (first [rewrite HE', E34, Ec0; reflexivity | lia]).
    change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. lia. }
  (* bounds the leaves use, computed once *)
  assert (Bp1 : 0 <= p1 < 2 ^ 64) by (clear - Hp1lo Htx4096 Htx47; lia).
  assert (Bend : 0 <= text + len < 2 ^ 64) by (clear - Hp1lo Htx4096 Htx47; lia).
  assert (Bc : 0 <= c < 2 ^ 64) by (clear - Hc8; lia).
  assert (Bq : 0 <= q < 2 ^ 63) by (clear - Hq4096 Hq_lo Hsp_hi Hqhi He0; lia).
  assert (BSH : 0 <= SHADOW_OFF < 2 ^ 32) by (unfold SHADOW_OFF; pvd_closed).
  pose proof Hnode as (Hv4096 & Hv8 & Hvrw & Hvz & Hvat & Hvam & Hvown & Hvra).
  assert (Bv : 0 <= v < 2 ^ 64)
    by (clear - Hv4096 Hvam; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hvam; lia).
  assert (Bq64 : 0 <= q < 2 ^ 64) by (clear - Bq; lia).
  psrr_branch_tok RUN BR HS SHOK PVD_Bspan.
  + (* ---- c > 109: 'n', 't', '{' or a number byte ---- *)
    pvd_brc Hc UCg c Hc8. apply Z.ltb_lt in Hc.
    paj_run_tok_x_inv RUN HS HJ SHOK HPM PVD_Bspan; [pvd_awr0|].
    psrr_branch_tok RUN BR HS SHOK PVD_Bspan.
    * (* c = 110: 'n' *)
      pvd_brc Hc0 UCg c Hc8. apply Z.eqb_eq in Hc0.
      paj_run_tok_x_inv RUN HS HJ SHOK HPM PVD_Bspan; [pvd_awr0|].
      (* the call stop at `jal literal` (B 0x86644): a0 = q, a1 = "null", a2 = 0, a3 = v *)
      rewrite ?wvb_collapse in HJ.
      (pvd_eq_chain W' mem). (pvd_gr_chain W' mem).
      lazymatch goal with |- SRr _ _ {| cfg_ms := ?m; cfg_model := _ |} _ => rename m into msf end.
      lazymatch goal with H : forall x, mrestrict (w_H W') (ms_mem msf) x = mrestrict (w_H W') mem x |- _ =>
        rename H into HEQ end.
      lazymatch goal with H : forall a, apresent (w_H W') mem a -> apresent (w_H W') (ms_mem msf) a |- _ =>
        rename H into HGR end.
      assert (AVF : forall a, aview SEGS (w_H W') (ms_mem msf) a = aview SEGS (w_H W') mem a)
        by (intros a; apply aview_eq_of; apply HEQ).
      pvd_kept HS HAE regs xtra ([2; 3; 4; 8; 9; 18; 19; 20; 23; 26; 27]%bv : list (bv 5)) KRF.
      (pvd_reg HS (1%bv : bv 5) RRA). (pvd_reg HS (10%bv : bv 5) RA0).
      (pvd_reg HS (11%bv : bv 5) RA1). (pvd_reg HS (12%bv : bv 5) RA2).
      (pvd_reg HS (13%bv : bv 5) RA3). (pvd_reg HS (24%bv : bv 5) RS8).
      (pmkst HS).
      rewrite Hc0 in Hsk, Hp1N.
      apply (ARM_LIT en 110 y Y fa fl pos lyc Sc k W' (ms_regs msf) (ms_mem msf) _ HPRE Hsk
        (or_intror (or_intror eq_refl))).
      { apply (pvd_cs_nw en AF_pv_lit_ret _ Y fa fl pos lyc Sc k W' regs mem (ms_regs msf) (ms_mem msf) _ HKR R9 R19
          R20 HFRM HinF Efa Efl HWIN HCHAIN); [rewrite Hp1N; exact HRD0 | exact HJ | exact KRF | | | exact HEQ | exact HGR
          | exact HPM].
        - rewrite RS8, (pvd_denot_shx _ 20 23 q SHADOW_OFF); [reflexivity | | | exact Bq | exact BSH].
          + cbn [ew ewset Nat.eqb]. rewrite ?ew_havoc_old by pvd_nat. exact E20.
          + cbn [ew ewset Nat.eqb]. rewrite ?ew_havoc_old by pvd_nat. exact E23.
        - rewrite RRA. apply codeptr_val. assumption. }
      { rewrite RA0. apply pvd_U_w64; [|exact Bq64]. apply (U_atom _ 20 q); [|exact Bq64].
        cbn [ew ewset Nat.eqb]. rewrite ?ew_havoc_old by pvd_nat. exact E20. }
      { rewrite RA1, pvd_soff_img; [reflexivity | assumption | unfold A_TEXT, A_OBJ, A_LIM; split; pvd_nat]. }
      { rewrite RA2. reflexivity. }
      { rewrite RA3. apply pvd_U_w64; [|exact Bv]. apply (U_atom _ 19 v); [|exact Bv].
        cbn [ew ewset Nat.eqb]. rewrite ?ew_havoc_old by pvd_nat. exact E19. }
      exact KX.
    * pvd_brc Hc0 UCg c Hc8. apply Z.eqb_neq in Hc0.
      paj_run_tok_x_inv RUN HS HJ SHOK HPM PVD_Bspan; [pvd_awr0|].
      psrr_branch_tok RUN BR HS SHOK PVD_Bspan.
      -- (* c = 116: 't' *)
         pvd_brc Hc1 UCg c Hc8. apply Z.eqb_eq in Hc1.
         paj_run_tok_x_inv RUN HS HJ SHOK HPM PVD_Bspan; [pvd_awr0|].
         (* the call stop at `jal literal`: a0 = q, a1 = "true", a2 = 2, a3 = v *)
         rewrite ?wvb_collapse in HJ.
         (pvd_eq_chain W' mem). (pvd_gr_chain W' mem).
         lazymatch goal with |- SRr _ _ {| cfg_ms := ?m; cfg_model := _ |} _ => rename m into msf end.
         lazymatch goal with H : forall x, mrestrict (w_H W') (ms_mem msf) x = mrestrict (w_H W') mem x |- _ =>
           rename H into HEQ end.
         lazymatch goal with H : forall a, apresent (w_H W') mem a -> apresent (w_H W') (ms_mem msf) a |- _ =>
           rename H into HGR end.
         pvd_kept HS HAE regs xtra ([2; 3; 4; 8; 9; 18; 19; 20; 23; 26; 27]%bv : list (bv 5)) KRF.
         (pvd_reg HS (1%bv : bv 5) RRA). (pvd_reg HS (10%bv : bv 5) RA0).
         (pvd_reg HS (11%bv : bv 5) RA1). (pvd_reg HS (12%bv : bv 5) RA2).
         (pvd_reg HS (13%bv : bv 5) RA3). (pvd_reg HS (24%bv : bv 5) RS8).
         (pmkst HS).
         rewrite Hc1 in Hsk, Hp1N.
         apply (ARM_LIT en 116 y Y fa fl pos lyc Sc k W' (ms_regs msf) (ms_mem msf) _ HPRE Hsk (or_introl eq_refl)).
         { apply (pvd_cs_nw en AF_pv_lit_ret _ Y fa fl pos lyc Sc k W' regs mem (ms_regs msf) (ms_mem msf) _ HKR R9 R19
             R20 HFRM HinF Efa Efl HWIN HCHAIN); [rewrite Hp1N; exact HRD0 | exact HJ | exact KRF | | | exact HEQ | exact HGR
             | exact HPM].
           - rewrite RS8, (pvd_denot_shx _ 20 23 q SHADOW_OFF); [reflexivity | | | exact Bq | exact BSH].
             + cbn [ew ewset Nat.eqb]. rewrite ?ew_havoc_old by pvd_nat. exact E20.
             + cbn [ew ewset Nat.eqb]. rewrite ?ew_havoc_old by pvd_nat. exact E23.
           - rewrite RRA. apply codeptr_val. assumption. }
         { rewrite RA0. apply pvd_U_w64; [|exact Bq64]. apply (U_atom _ 20 q); [|exact Bq64].
           cbn [ew ewset Nat.eqb]. rewrite ?ew_havoc_old by pvd_nat. exact E20. }
         { rewrite RA1, pvd_soff_img; [reflexivity | assumption | unfold A_TEXT, A_OBJ, A_LIM; split; pvd_nat]. }
         { rewrite RA2. reflexivity. }
         { rewrite RA3. apply pvd_U_w64; [|exact Bv]. apply (U_atom _ 19 v); [|exact Bv].
           cbn [ew ewset Nat.eqb]. rewrite ?ew_havoc_old by pvd_nat. exact E19. }
         exact KX.
      -- pvd_brc Hc1 UCg c Hc8. apply Z.eqb_neq in Hc1.
         paj_run_tok_x_inv RUN HS HJ SHOK HPM PVD_Bspan; [pvd_awr0|].
         psrr_branch_tok RUN BR HS SHOK PVD_Bspan.
         ++ (* c <> 123: the number arm *)
            pvd_brc Hc2 UCg c Hc8. apply negb_true_iff, Z.eqb_neq in Hc2.
            assert (Hsix : c <> 123 /\ c <> 91 /\ c <> 34 /\ c <> 116 /\ c <> 102 /\ c <> 110)
              by (clear - Hc Hc0 Hc1 Hc2; lia).
            (* the branch state sits at `bne a1, a3, 86598` (0x86520) with its condition; one step to the cut *)
            (paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM PVD_Bspan AF_pv_num; [pvd_awr0|]).
            rewrite ?wvb_collapse in HJ.
            (pvd_eq_chain W' mem). (pvd_gr_chain W' mem).
            lazymatch goal with |- SRr _ _ {| cfg_ms := ?m; cfg_model := _ |} _ => rename m into msf end.
            lazymatch goal with H : forall x, mrestrict (w_H W') (ms_mem msf) x = mrestrict (w_H W') mem x |- _ =>
              rename H into HEQ end.
            lazymatch goal with H : forall a, apresent (w_H W') mem a -> apresent (w_H W') (ms_mem msf) a |- _ =>
              rename H into HGR end.
            assert (AVF : forall a, aview SEGS (w_H W') (ms_mem msf) a = aview SEGS (w_H W') mem a)
              by (intros a; apply aview_eq_of; apply HEQ).
            lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
              assert (HAEf : env_agree 32 (Ereg regs xtra) Ex) by ((pvd_agree HAE)) end.
            assert (KRF : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 23; 26; 27]%bv -> getr (ms_regs msf) r = getr regs r)
              by (intros r Hr; (exact (regs_kept_of_st_ok_pi _ _ _ regs xtra
                    [2; 3; 4; 8; 9; 18; 19; 20; 23; 26; 27]%bv HS HAEf ltac:(vm_compute; reflexivity) r Hr))).
            (pvd_reg HS (10%bv : bv 5) RA0). (pvd_reg HS (11%bv : bv 5) RA1).
            (pvd_reg HS (12%bv : bv 5) RA2). (pvd_reg HS (24%bv : bv 5) RS8).
            (pmkst HS). apply KN.
            exists (ms_regs msf), (ms_mem msf), Y, fa, fl, pos, lyc, Sc, k, c, y.
            split; [repeat f_equal; try (vm_compute; reflexivity)|].
            split; [unfold pv_keep_regs; rewrite !KRF by (cbn; tauto); repeat split; assumption|].
            split; [rewrite KRF by (cbn; tauto); exact R9|].
            split; [rewrite KRF by (cbn; tauto); exact R19|].
            split; [rewrite KRF by (cbn; tauto); exact R20|].
            split.
            { rewrite RS8, (pvd_denot_shx _ 20 23 q SHADOW_OFF); [reflexivity | | | exact Bq | exact BSH].
              - cbn [ew ewset Nat.eqb]. rewrite ?ew_havoc_old by pvd_nat. exact E20.
              - cbn [ew ewset Nat.eqb]. rewrite ?ew_havoc_old by pvd_nat. exact E23. }
            split; [exact Hsk|].
            split.
            { rewrite RA0, Hp1N. apply pvd_U_w64; [|exact Bp1]. apply (U_atom _ 32 p1); [|exact Bp1].
              cbn [ew ewset Nat.eqb]. rewrite ?ew_havoc_old by pvd_nat. exact E32. }
            split.
            { rewrite RA1. apply pvd_U_w64; [|exact Bc]. apply UCg.
              cbn [ew ewset Nat.eqb]. rewrite ?ew_havoc_old by pvd_nat. reflexivity. }
            split.
            { rewrite RA2. apply pvd_U_w64; [|exact Bend]. apply (U_atom _ 33 (text + len)); [|exact Bend].
              cbn [ew ewset Nat.eqb]. rewrite ?ew_havoc_old by pvd_nat. exact E33. }
            split; [exact (proj1 Hsix)|]. split; [exact (proj1 (proj2 Hsix))|].
            split; [exact (proj1 (proj2 (proj2 Hsix)))|]. split; [exact (proj1 (proj2 (proj2 (proj2 Hsix))))|].
            split; [exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsix)))))|].
            split; [exact (proj2 (proj2 (proj2 (proj2 (proj2 Hsix)))))|].
            split.
            { split; [|split; [exact HinF|split; [exact Efa|split; [exact Efl|split; [exact HJ|]]]]].
              - apply (pvd_frame_tr _ _ _ _ _ _ W' mem); [intros a _; apply pvd_mbyte_eq, HEQ | intros a _; apply HGR | exact HFRM].
              - intros a Ha Hn. rewrite AVF. exact (HWIN a Ha Hn). }
            split.
            { intros rd' Hrd'. apply HCHAIN. intros a Ha. rewrite (Hrd' a Ha). apply AVF. }
            split; [rewrite Hp1N; eapply pv_reader0_ext; [exact HEQ | exact HRD0] | exact HPM].
         ++ (* c = 123: '{' *)
            pvd_brc Hc2 UCg c Hc8. apply negb_false_iff, Z.eqb_eq in Hc2.
            paj_run_tok_x_inv RUN HS HJ SHOK HPM PVD_Bspan; [pvd_awr0|].
            (* the call stop at `jal parse_items`: a0 = q, a1 = v, a2 = 1 *)
            rewrite ?wvb_collapse in HJ.
            (pvd_eq_chain W' mem). (pvd_gr_chain W' mem).
            lazymatch goal with |- SRr _ _ {| cfg_ms := ?m; cfg_model := _ |} _ => rename m into msf end.
            lazymatch goal with H : forall x, mrestrict (w_H W') (ms_mem msf) x = mrestrict (w_H W') mem x |- _ =>
              rename H into HEQ end.
            lazymatch goal with H : forall a, apresent (w_H W') mem a -> apresent (w_H W') (ms_mem msf) a |- _ =>
              rename H into HGR end.
            pvd_kept HS HAE regs xtra ([2; 3; 4; 8; 9; 18; 19; 20; 23; 26; 27]%bv : list (bv 5)) KRF.
            (pvd_reg HS (1%bv : bv 5) RRA). (pvd_reg HS (10%bv : bv 5) RA0).
            (pvd_reg HS (11%bv : bv 5) RA1). (pvd_reg HS (12%bv : bv 5) RA2).
            (pvd_reg HS (24%bv : bv 5) RS8).
            (pmkst HS).
            rewrite Hc2 in Hsk, Hp1N.
            apply SRr_ret. unfold pv_FINK.
            apply (ARM_ITEMS en 123 y Y fa fl pos lyc Sc k W' (ms_regs msf) (ms_mem msf) _ HPRE TPI Hsk
              (or_introl eq_refl)).
            { apply (pvd_cs_nw en AF_pv_items_ret _ Y fa fl pos lyc Sc k W' regs mem (ms_regs msf) (ms_mem msf) _ HKR R9
                R19 R20 HFRM HinF Efa Efl HWIN HCHAIN); [rewrite Hp1N; exact HRD0 | exact HJ | exact KRF | | | exact HEQ
                | exact HGR | exact HPM].
              - rewrite RS8, (pvd_denot_shx _ 20 23 q SHADOW_OFF); [reflexivity | | | exact Bq | exact BSH].
                + cbn [ew ewset Nat.eqb]. rewrite ?ew_havoc_old by pvd_nat. exact E20.
                + cbn [ew ewset Nat.eqb]. rewrite ?ew_havoc_old by pvd_nat. exact E23.
              - rewrite RRA. apply codeptr_val. assumption. }
            { rewrite RA0. apply pvd_U_w64; [|exact Bq64]. apply (U_atom _ 20 q); [|exact Bq64].
              cbn [ew ewset Nat.eqb]. rewrite ?ew_havoc_old by pvd_nat. exact E20. }
            { rewrite RA1. apply pvd_U_w64; [|exact Bv]. apply (U_atom _ 19 v); [|exact Bv].
              cbn [ew ewset Nat.eqb]. rewrite ?ew_havoc_old by pvd_nat. exact E19. }
            { rewrite RA2. reflexivity. }
            exact (pvd_kxR_of B ARx en KX).
  + (* ---- c <= 109: the double quote, '[', 'f' or a number byte ---- *)
    pvd_brc Hc UCg c Hc8. apply Z.ltb_ge in Hc.
    paj_run_tok_x_inv RUN HS HJ SHOK HPM PVD_Bspan; [pvd_awr0|].
    psrr_branch_tok RUN BR HS SHOK PVD_Bspan.
    * (* c = 34: the double quote *)
      pvd_brc Hc0 UCg c Hc8. apply Z.eqb_eq in Hc0.
      (* ---- B 0x864e0 .. 0x8655c: v's UBSan nonnull / alignment checks and ASan shadow check, v->type = 4
         (`sw a0, 0(s3)`: v may lie in a caller's fake frame, so the caller-frame runner), `jal parse_string` ---- *)
      rewrite ?wvb_collapse in HJ.
      (pvd_eq_chain W' mem). (pvd_gr_chain W' mem).
      lazymatch type of HS with st_ok_pi _ _ ?Ec _ (restrict _ ?m) => rename m into msx; set (E1 := Ec) in * end.
      lazymatch goal with H : forall x, mrestrict (w_H W') (ms_mem msx) x = mrestrict (w_H W') mem x |- _ =>
        rename H into HEQx end.
      lazymatch goal with H : forall a, apresent (w_H W') mem a -> apresent (w_H W') (ms_mem msx) a |- _ =>
        rename H into HGRx end.
      assert (AVx : forall a, aview SEGS (w_H W') (ms_mem msx) a = aview SEGS (w_H W') mem a)
        by (intros a; apply aview_eq_of; apply HEQx).
      assert (E19x : ew E1 19 = w64 v)
        by (unfold E1; cbn [ew ewset Nat.eqb]; rewrite ?ew_havoc_old by pvd_nat; exact E19).
      assert (U19x : bv_unsigned (ew E1 19) = v) by (rewrite E19x; apply unsigned_lit_small; exact Bv).
      assert (U20x : bv_unsigned (ew E1 20) = q)
        by (unfold E1; cbn [ew ewset Nat.eqb]; rewrite ?ew_havoc_old by pvd_nat; rewrite E20;
            apply unsigned_lit_small; exact Bq64).
      assert (U32x : bv_unsigned (ew E1 32) = p1)
        by (unfold E1; cbn [ew ewset Nat.eqb]; rewrite ?ew_havoc_old by pvd_nat; rewrite E32;
            apply unsigned_lit_small; exact Bp1).
      assert (HBx1 : U E1 PVD_Bx = SHADOW_OFF).
      { unfold PVD_Bx. rewrite U_SOff. unfold E1. cbn [ew ewset Nat.eqb]. rewrite ?ew_havoc_old by pvd_nat.
        rewrite E23, unsigned_lit_small by (clear - BSH; lia). reflexivity. }
      assert (EFa : forall c' p', frame_addr lyc c' p' = frame_addr (pe_ly en) c' p').
      { intros c' p'. unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _).
        first [rewrite EF; reflexivity | rewrite <- EF; reflexivity]. }
      pose proof (pvd_v_wr B ARx LAWS en lyc Sc [(0, pos)] HPRE Habl EFa) as VWR.
      pose proof (st_ok_pi_add_region E1 _ _ (YP09.mkRegion (Some 19%nat) 0 56 0 4 []) HS ltac:(vm_compute; reflexivity))
        as HS2.
      lazymatch type of HS2 with ?A -> ?Bd -> _ => assert (HA2 : A); [|assert (HB2 : Bd); [|specialize (HS2 HA2 HB2)]] end.
      { unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict].
        rewrite U19x.
        split; [clear - Bv Hvam Hv4096; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hvam; lia|].
        split; [clear - Bv Hvam Hv4096; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hvam; lia|].
        split; [|constructor].
        intros o Ho. assert (Hvo : v <= v + o < v + 56) by (clear - Ho; lia).
        apply (pvl_wr _ (v + o) (Z_to_bv 8 0));
          [ clear - Bv Hvam Hvo Hv4096; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hvam; lia
          | exact (proj2 (VWR (v + o) Hvo)) |].
        apply pvl_byte0. rewrite AVx, (HVEQ (v + o) Hvo). exact (pvl_zero_at _ _ _ _ Hvz Hvo). }
      { cbn [all_disjoint ss_mem add_cond].
        repeat split; try exact I; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          rewrite ?U19x, ?U20x, ?U32x; clear - Hqv Htv Hp1lo Hpend; lia. }
      pose proof (st_ok_pi_add_fact E1 _ _ 19%nat (mkAF 4096 (2 ^ 47 - 56) 3) HS2) as HS3.
      lazymatch type of HS3 with ?A -> _ => assert (HA3 : A); [|specialize (HS3 HA3)] end.
      { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U19x. change (2 ^ 3) with 8.
        clear - Hv8 Hv4096 Hvam. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hvam. lia. }
      clear HS HS2 HA2 HB2 HA3. rename HS3 into HS.
      lazymatch type of SHOK with sh_ok _ _ ?SH _ _ =>
        assert (SHOK2 : sh_ok SEGS PVD_Bx (SH ++ [mkSHE 19 0 56]) E1 (rdW W' (ms_mem msx))) end.
      { apply Forall_app. split; [exact SHOK|]. constructor; [|constructor].
        apply (shent_ok_of_range SEGS (w_H W') (ms_mem msx) E1 PVD_Bx 19 v 56 v 0 56);
          [| exact HBx1 | exact (U_atom E1 19 v E19x Bv) | clear - Bv; lia | clear - Bv; lia |].
        - intros x Hx. destruct (HVRA x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
          rewrite <- Hs. apply AVx.
        - intros x Hx. clear - Hx Hvam Hv4096.
          unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia. }
      clear SHOK. rename SHOK2 into SHOK.
      pose (RUNF := paj_run_x_fr_inv (SK := SK) (PL := PL_prog_B) (PI := PA) B PSTX ARx LAWS (YAkMemnorm.memnorm SEGS)
        (srr_inv_laws_memnorm_k SEGS)).
      paj_run_tok_x_inv RUNF HS HJ SHOK HPM PVD_Bspan.
      { intros a (r & Hin & Hr). cbn [add_atom ss_mem add_cond In] in Hin.
        repeat (destruct Hin as [Hin | Hin];
          [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
           first [ rewrite U19x in Hr; exact (proj1 (VWR a ltac:(clear - Hr; lia)))
                 | exfalso; clear - Hr; lia ] |]).
        destruct Hin. }
      (* the call stop at `jal parse_string` (B 0x8655c): a0 = q, the type word stored *)
      lazymatch goal with |- SRr _ _ {| cfg_ms := ?m; cfg_model := _ |} _ => rename m into msf end.
      lazymatch goal with H : frame_of E1 _ (mrestrict (w_H W') (ms_mem msx)) (mrestrict (w_H W') (ms_mem msf)) |- _ =>
        rename H into HFrS end.
      lazymatch goal with H : mem_grows (mrestrict (w_H W') (ms_mem msx)) (mrestrict (w_H W') (ms_mem msf)) |- _ =>
        rename H into HGS end.
      assert (HREL : forall x : word, ~ (v <= bv_unsigned x < v + 4) -> rdW W' (ms_mem msf) x = rdW W' mem x).
      { intros x Hx. rewrite <- (HEQx x). apply HFrS. intros (r & Hin & Hr). cbn [add_atom ss_mem add_cond In] in Hin.
        repeat (destruct Hin as [Hin | Hin];
          [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
           first [ rewrite U19x in Hr; apply Hx; clear - Hr; lia | clear - Hr; lia ] |]).
        destruct Hin. }
      assert (HGRf : forall a, apresent (w_H W') mem a -> apresent (w_H W') (ms_mem msf) a)
        by (intros a Ha; apply (apresent_grows _ _ _ a HGS), HGRx, Ha).
      rewrite ?wvb_collapse in HJ.
      pvd_kept HS HAE regs xtra ([2; 3; 4; 8; 9; 18; 19; 20; 23; 26; 27]%bv : list (bv 5)) KRF.
      (pvd_reg HS (1%bv : bv 5) RRA). (pvd_reg HS (10%bv : bv 5) RA0).
      (pvd_reg HS (24%bv : bv 5) RS8).
      assert (VT4 : val_mem SEGS (rdW W' (ms_mem msf)) v 4 4).
      { exact (pvd_val E1 _ (restrict (w_H W') msf) 19 0 4 (SLit 4) 4 v v HS ltac:(vm_compute; reflexivity) U19x
          ltac:(clear; lia) ltac:(apply U_lit; clear; lia) ltac:(clear; lia) ltac:(clear; cbn; lia)). }
      destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 0 pos HAR HinF) as (Hfa0 & Hfac & _).
      assert (Efb : fs_frame_bytes 0 = 64) by reflexivity.
      rewrite <- Efa in Hfa0, Hfac. rewrite Efb in Hfac.
      assert (HFB : forall a, (Y <= a < sp0 \/ fa <= a < fa + 64 \/ SHADOW_OFF + fa / 8 <= a < SHADOW_OFF + fa / 8 + 8) ->
                 mbyte SEGS (rdW W' (ms_mem msf)) a = mbyte SEGS (rdW W' mem) a).
      { intros a Ha.
        assert (Ha64 : 0 <= a < 2 ^ 64)
          by (clear - Ha Hfa0 Hfac HYr Hsp_hi Hsp_lo CC1 He0; unfold SHADOW_OFF in *;
              destruct Ha as [Ha | [Ha | Ha]]; lia).
        assert (Hnv : ~ (v <= a < v + 4)).
        { intros Hva. destruct Ha as [Ha | [Ha | Ha]].
          - destruct (Hvown a ltac:(clear - Hva; lia)) as [_ Hn]. apply Hn.
            change (spZ (pe_regs en)) with sp0. clear - Ha HYr HSTK. lia.
          - apply (pvd_v_apart B ARx LAWS en lyc Sc _ _ _ _ pos HPRE HAR Hfrs Habl EFa a ltac:(clear - Hva; lia)).
            rewrite <- Efa, Efb. exact Ha.
          - clear - Ha Hva Hvam Hfac Hfa0 CC1.
            unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia. }
        unfold mbyte. rewrite (HREL (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha64. exact Hnv. }
      (pmkst HS).
      rewrite Hc0 in Hsk, Hp1N.
      apply SRr_ret. unfold pv_FINK.
      apply (ARM_STR en y Y fa fl pos lyc Sc k W' mem (ms_regs msf) (ms_mem msf) _ HPRE Hsk).
      { apply (pvd_cs_v4 en AF_pv_str_ret _ Y fa fl pos lyc Sc k W' regs mem (ms_regs msf) (ms_mem msf) _ HKR R9 R19
          R20 HFRM HinF Efa Efl HWIN HCHAIN); [rewrite Hp1N; exact HRD0 | exact HJ | exact KRF | | | exact HREL
          | exact HGRf | exact HFB | clear - Hsp_lo CC1; lia | clear - Hsp_hi; lia | exact HPM].
        - rewrite RS8, (pvd_denot_shx _ 20 23 q SHADOW_OFF); [reflexivity | | | exact Bq | exact BSH].
          + unfold E1. cbn [ew ewset Nat.eqb]. rewrite ?ew_havoc_old by pvd_nat. exact E20.
          + unfold E1. cbn [ew ewset Nat.eqb]. rewrite ?ew_havoc_old by pvd_nat. exact E23.
        - rewrite RRA. apply codeptr_val. assumption. }
      { exact VT4. }
      { rewrite RA0. apply pvd_U_w64; [|exact Bq64]. apply (U_atom _ 20 q); [|exact Bq64].
        unfold E1. cbn [ew ewset Nat.eqb]. rewrite ?ew_havoc_old by pvd_nat. exact E20. }
      exact (pvd_kxR_of B ARx en KX).
    * pvd_brc Hc0 UCg c Hc8. apply Z.eqb_neq in Hc0.
      paj_run_tok_x_inv RUN HS HJ SHOK HPM PVD_Bspan; [pvd_awr0|].
      psrr_branch_tok RUN BR HS SHOK PVD_Bspan.
      -- (* c = 91: '[' *)
         pvd_brc Hc1 UCg c Hc8. apply Z.eqb_eq in Hc1.
         paj_run_tok_x_inv RUN HS HJ SHOK HPM PVD_Bspan; [pvd_awr0|].
         (* the call stop at `jal parse_items`: a0 = q, a1 = v, a2 = 0 *)
         rewrite ?wvb_collapse in HJ.
         (pvd_eq_chain W' mem). (pvd_gr_chain W' mem).
         lazymatch goal with |- SRr _ _ {| cfg_ms := ?m; cfg_model := _ |} _ => rename m into msf end.
         lazymatch goal with H : forall x, mrestrict (w_H W') (ms_mem msf) x = mrestrict (w_H W') mem x |- _ =>
           rename H into HEQ end.
         lazymatch goal with H : forall a, apresent (w_H W') mem a -> apresent (w_H W') (ms_mem msf) a |- _ =>
           rename H into HGR end.
         pvd_kept HS HAE regs xtra ([2; 3; 4; 8; 9; 18; 19; 20; 23; 26; 27]%bv : list (bv 5)) KRF.
         (pvd_reg HS (1%bv : bv 5) RRA). (pvd_reg HS (10%bv : bv 5) RA0).
         (pvd_reg HS (11%bv : bv 5) RA1). (pvd_reg HS (12%bv : bv 5) RA2).
         (pvd_reg HS (24%bv : bv 5) RS8).
         (pmkst HS).
         rewrite Hc1 in Hsk, Hp1N.
         apply SRr_ret. unfold pv_FINK.
         apply (ARM_ITEMS en 91 y Y fa fl pos lyc Sc k W' (ms_regs msf) (ms_mem msf) _ HPRE TPI Hsk
           (or_intror eq_refl)).
         { apply (pvd_cs_nw en AF_pv_items_ret _ Y fa fl pos lyc Sc k W' regs mem (ms_regs msf) (ms_mem msf) _ HKR R9
             R19 R20 HFRM HinF Efa Efl HWIN HCHAIN); [rewrite Hp1N; exact HRD0 | exact HJ | exact KRF | | | exact HEQ
             | exact HGR | exact HPM].
           - rewrite RS8, (pvd_denot_shx _ 20 23 q SHADOW_OFF); [reflexivity | | | exact Bq | exact BSH].
             + cbn [ew ewset Nat.eqb]. rewrite ?ew_havoc_old by pvd_nat. exact E20.
             + cbn [ew ewset Nat.eqb]. rewrite ?ew_havoc_old by pvd_nat. exact E23.
           - rewrite RRA. apply codeptr_val. assumption. }
         { rewrite RA0. apply pvd_U_w64; [|exact Bq64]. apply (U_atom _ 20 q); [|exact Bq64].
           cbn [ew ewset Nat.eqb]. rewrite ?ew_havoc_old by pvd_nat. exact E20. }
         { rewrite RA1. apply pvd_U_w64; [|exact Bv]. apply (U_atom _ 19 v); [|exact Bv].
           cbn [ew ewset Nat.eqb]. rewrite ?ew_havoc_old by pvd_nat. exact E19. }
         { rewrite RA2. reflexivity. }
         exact (pvd_kxR_of B ARx en KX).
      -- pvd_brc Hc1 UCg c Hc8. apply Z.eqb_neq in Hc1.
         paj_run_tok_x_inv RUN HS HJ SHOK HPM PVD_Bspan; [pvd_awr0|].
         psrr_branch_tok RUN BR HS SHOK PVD_Bspan.
         ++ (* c <> 102: the number arm *)
            pvd_brc Hc2 UCg c Hc8. apply negb_true_iff, Z.eqb_neq in Hc2.
            assert (Hsix : c <> 123 /\ c <> 91 /\ c <> 34 /\ c <> 116 /\ c <> 102 /\ c <> 110)
              by (clear - Hc Hc0 Hc1 Hc2; lia).
            (* the branch state sits at `bne a1, a3, 86598` (0x864f0) with its condition; one step to the cut *)
            (paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM PVD_Bspan AF_pv_num; [pvd_awr0|]).
            rewrite ?wvb_collapse in HJ.
            (pvd_eq_chain W' mem). (pvd_gr_chain W' mem).
            lazymatch goal with |- SRr _ _ {| cfg_ms := ?m; cfg_model := _ |} _ => rename m into msf end.
            lazymatch goal with H : forall x, mrestrict (w_H W') (ms_mem msf) x = mrestrict (w_H W') mem x |- _ =>
              rename H into HEQ end.
            lazymatch goal with H : forall a, apresent (w_H W') mem a -> apresent (w_H W') (ms_mem msf) a |- _ =>
              rename H into HGR end.
            assert (AVF : forall a, aview SEGS (w_H W') (ms_mem msf) a = aview SEGS (w_H W') mem a)
              by (intros a; apply aview_eq_of; apply HEQ).
            lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
              assert (HAEf : env_agree 32 (Ereg regs xtra) Ex) by ((pvd_agree HAE)) end.
            assert (KRF : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 23; 26; 27]%bv -> getr (ms_regs msf) r = getr regs r)
              by (intros r Hr; (exact (regs_kept_of_st_ok_pi _ _ _ regs xtra
                    [2; 3; 4; 8; 9; 18; 19; 20; 23; 26; 27]%bv HS HAEf ltac:(vm_compute; reflexivity) r Hr))).
            (pvd_reg HS (10%bv : bv 5) RA0). (pvd_reg HS (11%bv : bv 5) RA1).
            (pvd_reg HS (12%bv : bv 5) RA2). (pvd_reg HS (24%bv : bv 5) RS8).
            (pmkst HS). apply KN.
            exists (ms_regs msf), (ms_mem msf), Y, fa, fl, pos, lyc, Sc, k, c, y.
            split; [repeat f_equal; try (vm_compute; reflexivity)|].
            split; [unfold pv_keep_regs; rewrite !KRF by (cbn; tauto); repeat split; assumption|].
            split; [rewrite KRF by (cbn; tauto); exact R9|].
            split; [rewrite KRF by (cbn; tauto); exact R19|].
            split; [rewrite KRF by (cbn; tauto); exact R20|].
            split.
            { rewrite RS8, (pvd_denot_shx _ 20 23 q SHADOW_OFF); [reflexivity | | | exact Bq | exact BSH].
              - cbn [ew ewset Nat.eqb]. rewrite ?ew_havoc_old by pvd_nat. exact E20.
              - cbn [ew ewset Nat.eqb]. rewrite ?ew_havoc_old by pvd_nat. exact E23. }
            split; [exact Hsk|].
            split.
            { rewrite RA0, Hp1N. apply pvd_U_w64; [|exact Bp1]. apply (U_atom _ 32 p1); [|exact Bp1].
              cbn [ew ewset Nat.eqb]. rewrite ?ew_havoc_old by pvd_nat. exact E32. }
            split.
            { rewrite RA1. apply pvd_U_w64; [|exact Bc]. apply UCg.
              cbn [ew ewset Nat.eqb]. rewrite ?ew_havoc_old by pvd_nat. reflexivity. }
            split.
            { rewrite RA2. apply pvd_U_w64; [|exact Bend]. apply (U_atom _ 33 (text + len)); [|exact Bend].
              cbn [ew ewset Nat.eqb]. rewrite ?ew_havoc_old by pvd_nat. exact E33. }
            split; [exact (proj1 Hsix)|]. split; [exact (proj1 (proj2 Hsix))|].
            split; [exact (proj1 (proj2 (proj2 Hsix)))|]. split; [exact (proj1 (proj2 (proj2 (proj2 Hsix))))|].
            split; [exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsix)))))|].
            split; [exact (proj2 (proj2 (proj2 (proj2 (proj2 Hsix)))))|].
            split.
            { split; [|split; [exact HinF|split; [exact Efa|split; [exact Efl|split; [exact HJ|]]]]].
              - apply (pvd_frame_tr _ _ _ _ _ _ W' mem); [intros a _; apply pvd_mbyte_eq, HEQ | intros a _; apply HGR | exact HFRM].
              - intros a Ha Hn. rewrite AVF. exact (HWIN a Ha Hn). }
            split.
            { intros rd' Hrd'. apply HCHAIN. intros a Ha. rewrite (Hrd' a Ha). apply AVF. }
            split; [rewrite Hp1N; eapply pv_reader0_ext; [exact HEQ | exact HRD0] | exact HPM].
         ++ (* c = 102: 'f' *)
            pvd_brc Hc2 UCg c Hc8. apply negb_false_iff, Z.eqb_eq in Hc2.
            paj_run_tok_x_inv RUN HS HJ SHOK HPM PVD_Bspan; [pvd_awr0|].
            (* the call stop at `jal literal`: a0 = q, a1 = "false", a2 = 1, a3 = v *)
            rewrite ?wvb_collapse in HJ.
            (pvd_eq_chain W' mem). (pvd_gr_chain W' mem).
            lazymatch goal with |- SRr _ _ {| cfg_ms := ?m; cfg_model := _ |} _ => rename m into msf end.
            lazymatch goal with H : forall x, mrestrict (w_H W') (ms_mem msf) x = mrestrict (w_H W') mem x |- _ =>
              rename H into HEQ end.
            lazymatch goal with H : forall a, apresent (w_H W') mem a -> apresent (w_H W') (ms_mem msf) a |- _ =>
              rename H into HGR end.
            pvd_kept HS HAE regs xtra ([2; 3; 4; 8; 9; 18; 19; 20; 23; 26; 27]%bv : list (bv 5)) KRF.
            (pvd_reg HS (1%bv : bv 5) RRA). (pvd_reg HS (10%bv : bv 5) RA0).
            (pvd_reg HS (11%bv : bv 5) RA1). (pvd_reg HS (12%bv : bv 5) RA2).
            (pvd_reg HS (13%bv : bv 5) RA3). (pvd_reg HS (24%bv : bv 5) RS8).
            (pmkst HS).
            rewrite Hc2 in Hsk, Hp1N.
            apply (ARM_LIT en 102 y Y fa fl pos lyc Sc k W' (ms_regs msf) (ms_mem msf) _ HPRE Hsk
              (or_intror (or_introl eq_refl))).
            { apply (pvd_cs_nw en AF_pv_lit_ret _ Y fa fl pos lyc Sc k W' regs mem (ms_regs msf) (ms_mem msf) _ HKR R9
                R19 R20 HFRM HinF Efa Efl HWIN HCHAIN); [rewrite Hp1N; exact HRD0 | exact HJ | exact KRF | | | exact HEQ
                | exact HGR | exact HPM].
              - rewrite RS8, (pvd_denot_shx _ 20 23 q SHADOW_OFF); [reflexivity | | | exact Bq | exact BSH].
                + cbn [ew ewset Nat.eqb]. rewrite ?ew_havoc_old by pvd_nat. exact E20.
                + cbn [ew ewset Nat.eqb]. rewrite ?ew_havoc_old by pvd_nat. exact E23.
              - rewrite RRA. apply codeptr_val. assumption. }
            { rewrite RA0. apply pvd_U_w64; [|exact Bq64]. apply (U_atom _ 20 q); [|exact Bq64].
              cbn [ew ewset Nat.eqb]. rewrite ?ew_havoc_old by pvd_nat. exact E20. }
            { rewrite RA1, pvd_soff_img; [reflexivity | assumption | unfold A_TEXT, A_OBJ, A_LIM; split; pvd_nat]. }
            { rewrite RA2. reflexivity. }
            { rewrite RA3. apply pvd_U_w64; [|exact Bv]. apply (U_atom _ 19 v); [|exact Bv].
              cbn [ew ewset Nat.eqb]. rewrite ?ew_havoc_old by pvd_nat. exact E19. }
            exact KX.
Qed.

End c.
