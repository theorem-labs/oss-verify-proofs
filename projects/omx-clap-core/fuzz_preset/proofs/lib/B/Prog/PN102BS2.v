(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset, image B' (asan-ubsan, harness fix #102, pin sha256
   d663f82d7f488d30f8e8d7496cb814e595a2f3cbbf16bde81a65cb3ea9af0994): SEGMENT S2 of the walk of parse_noting (the B' twin of row
   N10-PNA; cut table lib/B/Prog/PN102BCuts.v pn_seg_S2_stmt): from pn_cut_S2 (+0x28, fuzz_alloc_live returned) run
   +0x28 mv s1,a0; +0x2c mv a0,s3; +0x30 mv a1,s2; +0x34 mv a2,s0 and +0x38 jal pj_parse, close the call by the batch kit's text
   tpj_parse_specX (lib/A/PRH_FnPj.v 3aa72eee2204 :592-736, a working branch 03fcabb582d0; the
   statement's premise, at the CW pn_cw X) at window 0 with every premise discharged at the call state, and establish
   pn_cut_S3 at the return site +0x3c at pj_parse's float state, the journal at the budget pn_cw X.
   rule 24: proves function parse_noting (fuzz_preset, image B') (preparation; proof-index 03:20Z 0 named / 0 by
   address / 0 released; the rule-24 parse_noting check CONFIRM 03:25Z). This file: segment S2 of that walk.
   SHAPES: the call is lib/A/Prog/Ent102L2A.v l2_pno / l2_pno_post's (a working branch b1bc025047ea), the
   slot steps PN102BHelp.v's, the frame across the steps and the call PN102BKeep.v's, the call-state facts (the out
   node's slot, the text's bytes, shadow and ceiling, the grammar facts, the live requests, the requests within
   g_most, the reader's block sizes) PN102BS2Help.v's.
   The batch kit's CHANGES to the f97c segment: pj_parse takes CW in DW's slot - pn_cw X, arm 1 (text + len) for parse_items and
   arm 2 (the slot word, the cut S2's slot equation) for parse_string (PN102BCuts.v pn_cw_pj); its room
   `wild_room U CW 0 (st_depot S)` is the text's room [] 2 by YCbqGwild.wild_room_set (|pn_cw X| = 2,
   PN102BKeep.v pn_cw_len); `t0 + len < alloc_ceiling` from the text's home (PN102BS2Help.v pn2_text_ceil, AR_laws_x
   field 24); `RQ_pj_parse tb <= most` is the text's own; the post is budgeted (PN102BHelp.v pn_callFb), and the
   caller's journal is normalised to pn_cw X (YCbqGwild.ajournal_xw_norm, wbudget CW 0 makes the fresh part empty).
   pn_R's new conjuncts come from pj_parse's post: the outcome (ran = 0 at entry), prh_oks with g_most, the refusal
   peak, `ran' = 0 -> .. -> res = ck_read` (PN102BS2Help.v pn2_granted with pn2_reqs_le and the text's RQ <= most),
   the reader's block sizes (pn2_rd_blocks), the free order and pj_ncapR (verbatim).
   THE FREE / REALLOC MOVE: pj_parse frees, so its text concludes SRr' segs RZ_cf (SRrG at YA0nH.wle' segs RZ_cf) and
   its post fpostWFbm is at wle'. The four moves and the jal call nothing (plain SRr, lifted by YA0nH.SRr_SRr' under
   SRrG_bind); the caller's journal is lifted to wle' (YCbqG.ajournal_xwR_mono, YA0nH.wle_wle') and the call is
   PN102BHelp.v pn_callFb at wle'; the frame after it is PN102BKeep.v pn_frame_call (wle before, wle' after), the
   text's bytes are kept by PN102BS2Help.v pn2_text_keptR at pj_parse's journal; pj_parse's hull budget is the
   text's own (pp_hull: the state at the call is the entry's) and its hull use is pn_cut_S3's pn_hull.
   SECTION HYPOTHESIS: TB (the image binding of B), with its witness at B' below (YD2l.TfibB); it is used for the image
   hull of a text in the image (PN102BS2Help.v pn2_text_shadow).
   NUMERALS: 48 (the frame), 56 (struct pj), 4 (an instruction), 2 ^ 40 / 2 ^ 64 (the engine's code-span and word
   ranges). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK1d YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YM05 YI16 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetReqAt PresetRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnReader PRH_FnPj PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YF0m YD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PN102BCuts PN102BHelp PN102BKeep PN102BS2Help.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* the image binding TB at the real B' binding (YD2l.v, TfibB') *)
Lemma pn_seg_S2_TB_witness : YF0m.TfibSyms YD2l.TfibB.
Proof. exact YD2l.TfibB_syms. Qed.

(* a callee-saved register other than r is not the written register (pn2_cs_ne at a literal) *)
Ltac pn2_csne :=
  apply pn2_cs_ne; [assumption | let E := fresh "E" in intro E; vm_compute in E; subst; unfold acallee_saved in *; lia].

(* one `mv rd, rs` slot at offset k (addi rd, rs, 0) *)
Ltac pn2_mv W regs mem md k rdl rsl :=
  let Hpl := fresh "Hpl" in let Hd := fresh "Hd" in
  pn_fd k Hpl Hd;
  eapply (pn_step_addi W regs mem md _ k _ _ _ _ rdl (getr regs rsl) ltac:(unfold PN_S2, PN_RET in *; lia) Hpl Hd);
  [ vm_compute; reflexivity
  | apply bv_eq; vm_compute; reflexivity
  | lazymatch goal with |- v_addi (getr _ ?rs) (bv_signed ?im) = _ =>
      replace rs with rsl by (apply bv_eq; vm_compute; reflexivity);
      replace (bv_signed im) with 0 by (vm_compute; reflexivity) end; apply pn2_addi0
  | ].

Section I. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {SK : YI16.sink_head}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
#[local] Abbreviation CP := CfParams_preset.
#[local] Abbreviation PA := (@PI_prog_B rc).
#[local] Abbreviation SEGS := (@pa_segs rc B_prog_listing PA).
#[local] Abbreviation BASE := (@pa_val rc B_prog_listing PA A_TEXT).
#[local] Abbreviation SIGMA := (@pa_sigma rc B_prog_listing PA).
#[local] Abbreviation PST := (@prh_pst prh_img_B).
Variable B : asyms.
(* the image binding of B: witness pn_seg_S2_TB_witness above *)
Hypothesis TB : YF0m.TfibSyms B.
#[local] Abbreviation ARc := (fun ly S Hp (W : world SEGS) mem md =>
  ARcf (cp := CP) SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
#[local] Abbreviation CWX X := (pn_cw (PI := prh_img_B) (PA := PA) B X).

Theorem pn_seg_S2 : forall CTX0,
  pn_seg_S2_stmt (fx := fx) (cp := CP) (PI := prh_img_B) (RL := prh_room_live_a8 (cp := CP)) (PA := PA) B ARc SK CTX0.
Proof.
intros CTX0 HT X W' c HPRE Hcut.
pose proof (pn2_LAWS B) as LAWS.
destruct Hcut as (regs & mem & md & ly & S & Hp & k & Ec & HF & R8 & R18 & R19 & R10 & ES & EHp & Hab & HLED & HSLOT).
subst c S Hp.
(* the run to pj_parse's entry calls nothing (plain SRr, lifted into wle'); pj_parse's call and the return are at wle' *)
unfold SRr'.
lazymatch goal with |- SRrG _ _ ?W0 ?c0 ?Q0 =>
  apply (SRrG_bind SEGS (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf) W0 c0
    (fun W2 c2 => SRrG SEGS (wle' SEGS YGcfRehidePost.RZ_cf) W2 c2 Q0) Q0);
  [apply (SRr_SRr' SEGS YGcfRehidePost.RZ_cf) | intros W2 c2 _ H2; exact H2] end.
(* ---- the entry's facts ---- *)
pose proof (pp_fpre B ARc CTX0 X HPRE) as (HPX0 & HRO0 & Hstkhi0 & Hraceil0).
pose proof HPX0 as (HAR0 & _ & _ & Hgp0 & Htp0 & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil0 & Hslo0 & Hshi0 & H470 & Hbot0 & Htop0 & Htop20).
pose proof (pp_out B ARc CTX0 X HPRE) as HOUT.
pose proof HOUT as ((cid & pos & Hinf & Hf1 & Hf2) & (Hd0 & Hdc & _)).
pose proof (pp_doc8 B ARc CTX0 X HPRE) as Hd8.
pose proof (pn2_frame_geom B (px_ly X) (px_S X) (px_Hp X) (px_W X) (px_mem X) (px_md X) cid pos HAR0 Hinf)
  as (_ & _ & _ & _ & A4096 & _).
pose proof (pp_ledger B ARc CTX0 X HPRE) as HLED0.
pose proof (pp_home B ARc CTX0 X HPRE) as HOME0.
pose proof (pp_src B ARc CTX0 X HPRE) as HSRC0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pn_slot0_range as [Hs0 Hs1].
assert (HSTKv : STK_pj_parse + 48 <= STK_parse_noting /\ 0 <= STK_pj_parse) by (split; vm_compute; congruence).
assert (HFRv : ck_FRAMES_CAP - FR_parse_noting + Z.of_nat DOC_D <= fs_frames 0) by (vm_compute; congruence).
assert (Hra5v : 4096 <= BASE + (PN_SLOT0 + PN_S2 + 4 + 4 + 4 + 4 + 4) < 2 ^ 40) by (split; vm_compute; congruence).
(* ---- +0x28 .. +0x34: mv s1,a0; mv a0,s3; mv a1,s2; mv a2,s0 ---- *)
rewrite pn_cfg_eq.
pn2_mv W' regs mem md (PN_SLOT0 + PN_S2) (9%bv : bv 5) (10%bv : bv 5).
intros X1.
pn2_mv W' (regupd regs 9%bv (getr regs 10)) mem (with_vm_backing (m_vm_lazy md) X1 md) (PN_SLOT0 + PN_S2 + 4)
  (10%bv : bv 5) (19%bv : bv 5).
intros X2.
lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst ?r _ _ _) ?m) _ =>
  pn2_mv W' r mem m (PN_SLOT0 + PN_S2 + 4 + 4) (11%bv : bv 5) (18%bv : bv 5) end.
intros X3.
lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst ?r _ _ _) ?m) _ =>
  pn2_mv W' r mem m (PN_SLOT0 + PN_S2 + 4 + 4 + 4) (12%bv : bv 5) (8%bv : bv 5) end.
intros X4.
(* ---- +0x38 jal pj_parse ---- *)
pn_fdc (PN_SLOT0 + PN_S2 + 4 + 4 + 4 + 4) Hpl5.
lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst ?r _ _ _) ?m) _ =>
  apply (pn_step_call W' r mem m _ (PN_SLOT0 + PN_S2 + 4 + 4 + 4 + 4) AS_pj_parse _ (1%bv : bv 5)
    ltac:(unfold PN_S2, PN_RET in *; lia) Hpl5 ltac:(apply bv_eq; reflexivity)) end.
intros X5.
lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst ?r _ _ _) ?m) _ => set (regs5 := r); set (md5 := m) end.
(* ---- the registers at the call ---- *)
assert (E1 : getr regs5 1 = Z_to_bv 64 (BASE + (PN_SLOT0 + PN_S2 + 4 + 4 + 4 + 4 + 4)))
  by (unfold regs5; apply pn2_upd_same; reflexivity).
assert (E8 : getr regs5 8 = w64 (px_doc X)) by (unfold regs5; rewrite !pn2_upd_other by pn_regne; exact R8).
assert (E9 : getr regs5 9 = w64 (Ledger.lsum (px_Lam X))).
{ unfold regs5. rewrite !pn2_upd_other by pn_regne. rewrite pn2_upd_same by reflexivity. exact R10. }
assert (E10 : getr regs5 10 = w64 (px_text X)).
{ unfold regs5. rewrite !pn2_upd_other by pn_regne. rewrite pn2_upd_same by reflexivity.
  rewrite !pn2_upd_other by pn_regne. exact R19. }
assert (E11 : getr regs5 11 = w64 (pn_len X)).
{ unfold regs5. rewrite !pn2_upd_other by pn_regne. rewrite pn2_upd_same by reflexivity.
  rewrite !pn2_upd_other by pn_regne. exact R18. }
assert (E12 : getr regs5 12 = w64 (px_doc X)).
{ unfold regs5. rewrite !pn2_upd_other by pn_regne. rewrite pn2_upd_same by reflexivity.
  rewrite !pn2_upd_other by pn_regne. exact R8. }
(* ---- the frame at the call (registers written: s1 and three argument registers and ra; the model materialized;
   the journal still at the empty budget) *)
assert (HF5 : pn_frame (fx := fx) (PI := prh_img_B) (PA := PA) B ARc SK X fx W' regs5 mem md5 ly (px_S X) (px_Hp X) k []).
{ unfold md5.
  apply (pn_frame_step B LAWS X fx W' regs5 regs5 mem _ X5 ly _ _ k []); [|intros; reflexivity].
  apply (pn_frame_step B LAWS X fx W' regs5 regs5 mem _ X4 ly _ _ k []); [|intros; reflexivity].
  apply (pn_frame_step B LAWS X fx W' regs5 regs5 mem _ X3 ly _ _ k []); [|intros; reflexivity].
  apply (pn_frame_step B LAWS X fx W' regs5 regs5 mem _ X2 ly _ _ k []); [|intros; reflexivity].
  apply (pn_frame_step B LAWS X fx W' regs regs5 mem _ X1 ly _ _ k [] HF).
  intros r Hr H8 H9 H18 H19. unfold regs5. rewrite !pn2_upd_other by pn2_csne. reflexivity. }
pose proof HF5 as (HJ5 & Hsp5 & _ & _ & _ & _ & _ & Hcs5 & _ & _ & Hmn5 & Hro5).
pose proof (ajx_ar HJ5) as HAR5. pose proof (ajx_ly HJ5) as Hly5.
pose proof Hly5 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _ & Eshi & _).
unfold PN_FRAME in Hsp5.
assert (E3 : getr regs5 3 = w64 (as_gp B)).
{ transitivity (getr (px_regs X) 3); [|exact Hgp0].
  exact (Hcs5 3 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
assert (E4 : getr regs5 4 = w64 (as_tp B)).
{ transitivity (getr (px_regs X) 4); [|exact Htp0].
  exact (Hcs5 4 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
assert (Hra5 : raZ regs5 = BASE + (PN_SLOT0 + PN_S2 + 4 + 4 + 4 + 4 + 4)).
{ unfold raZ. rewrite E1. apply unsigned_lit_small. lia. }
assert (Hret : YK0s.ret_ok (getr regs5 1)).
{ rewrite E1. apply (ret_ok_codeptr_v (PI := PA)); [unfold PN_S2, PN_RET in *; lia | vm_compute; reflexivity]. }
assert (Hch : achain ly (aview SEGS (w_H W') mem) (spZ regs5) (s0Z regs5) []).
{ left. split; [|reflexivity]. left. unfold s0Z. rewrite E8. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Hsink : ~ YI16.sink_open_fp [(px_doc X, px_doc X + 56)]).
{ apply sink_closed_pos. constructor; [cbn [fst]; lia | constructor]. }
(* ---- pj_parse's premises at the call state ---- *)
assert (Hbl0 : forall x, In x (ablocks B (px_ly X) (px_S X)) -> In x (ablocks B ly (px_S X))).
{ intros x Hx. rewrite Hab. exact Hx. }
assert (P13 : prhReader_home B ly (px_S X) (px_Hp X) (px_Lam X) (px_text X) (pn_len X)).
{ destruct HOME0 as [Hk | (b & m & Hb & Hr)]; [left; exact Hk|]. right. exists b, m. rewrite Hab. exact (conj Hb Hr). }
assert (P17 : px_doc X < YM05.alloc_ceiling) by lia.
assert (P18 : forall a kk, In (a, kk) (px_Lam X) -> px_doc X + 56 <= a \/ a + kk <= px_doc X).
{ intros a kk Hin.
  destruct (pn2_lam_frame B (px_ly X) (px_S X) (px_Hp X) (px_W X) (px_mem X) (px_md X) (px_W X) (px_mem X)
    (px_Lam X) _ _ _ _ _ _ a kk cid pos HAR0 HLED0 Hin Hinf) as [h|h]; lia. }
assert (P19 : 0 < pn_len X -> px_text X + pn_len X <= px_doc X \/ px_doc X + 56 <= px_text X).
{ intros Hlen.
  destruct (pn2_home_frame B (px_ly X) (px_S X) (px_Hp X) (px_W X) (px_mem X) (px_md X) (px_W X) (px_mem X)
    (px_Lam X) _ _ _ _ _ _ (px_text X) (pn_len X) cid pos HAR0 HLED0 HOME0 Hlen Hinf) as [h|h]; lia. }
assert (Hfp : forall a, px_text X <= a < px_text X + pn_len X -> ~ inFP [(px_doc X, px_doc X + 56)] a).
{ intros a Ha Hf. apply (proj1 (inFP_cons _ _ _ _)) in Hf. destruct Hf as [Hf | Hf]; [|exact (inFP_nil _ Hf)].
  assert (Hlen : 0 < pn_len X) by lia. destruct (P19 Hlen); lia. }
assert (P12 : src_rd W' mem (px_text X) (px_tb X)).
{ eapply (pn2_src_kept B TB); [exact HJ5 | exact HLED0 | exact HLED | exact Hsink | exact Hbl0 | exact HOME0 |
    exact P13 | exact Hfp | exact HSRC0]. }
assert (P15 : fwin ly W' regs5 mem 0).
{ split; [lia|]. split; [reflexivity|]. split; [rewrite Hsp5, Etop; lia|]. intros a Ha; lia. }
assert (P16 : prhPj_slot B STK_pj_parse 0 ly (px_S X) (px_Lam X) W' regs5 mem (px_doc X)).
{ apply (pn2_doc_slot B STK_parse_noting (spZ (px_regs X)) (px_ly X) (px_S X) (px_Hp X) (px_W X) (px_mem X) (px_md X)
    ly (px_Hp X) W' mem md5 k (px_regs X) regs5 (px_Lam X) (px_doc X) STK_pj_parse HJ5 HAR0 HOUT Hd8).
  rewrite Hsp5. lia. }
assert (P24 : Z.of_nat (length (frames (px_S X))) + Z.of_nat DOC_D <= fs_frames 0).
{ pose proof (pp_frames B ARc CTX0 X HPRE). lia. }
(* The batch kit: the text ends below the ceiling (AR_laws_x field 24 at its home) *)
assert (PCEIL : px_text X + pn_len X < YM05.alloc_ceiling)
  by exact (pn2_text_ceil B ly (px_S X) (px_Hp X) W' mem md5 W' mem (px_Lam X) (px_peak X) (px_cnt X) (px_fail X)
    (px_ran X) (px_most X) (px_own X) (px_text X) (pn_len X) HAR5 HLED P13).
(* The batch kit: pj_parse's CW is pn_cw X (arm 1 text + len for parse_items, arm 2 the slot word for parse_string; the slot at
   the call sp - 48 = the entry sp - 96 is the entry's, the cut S2's slot equation) *)
assert (PCW : prh_cw_pj B (CWX X) W' mem regs5 (px_text X) (pn_len X)).
{ apply (pn_cw_pj (PI := prh_img_B) (PA := PA) B X W' mem regs5); [|exact HSLOT].
  rewrite Hsp5, pn_frame_B. unfold PN_FRAME. lia. }
(* The batch kit: its room is the text's room [] 2, the two fresh slots holding CW (YCbqGwild.wild_room_set) *)
assert (PWR : YCbqGwild.wild_room (as_universe B) (CWX X) 0 (st_depot (px_S X))).
{ apply YCbqGwild.wild_room_set. rewrite pn_cw_len.
  pose proof (pp_wild B ARc CTX0 X HPRE) as HW. rewrite pn_wk_B in HW. exact HW. }
(* ---- the call, at wle': the caller's journal lifted from wle ---- *)
change (mkCfg (@YK11.mkst fx regs5 (Z_to_bv 64 (SIGMA AS_pj_parse)) mem (YK11.seg_rom SEGS)) md5)
  with (cfg_at SEGS (SIGMA AS_pj_parse) regs5 mem md5).
apply SRr_ret. cbv beta.
assert (HJ5' : ajournal_xwR (SK := SK) SEGS B PST ARc (wle' SEGS YGcfRehidePost.RZ_cf) STK_parse_noting
    (spZ (px_regs X)) [(px_doc X, px_doc X + 56)] (px_ly X) (px_S X) (px_Hp X) (px_W X) (px_mem X) (px_md X) []
    ly (px_S X) (px_Hp X) W' mem md5 k []).
{ apply (ajournal_xwR_mono (SK := SK) SEGS B PST ARc (@wle SEGS));
    [exact (wle_wle' SEGS YGcfRehidePost.RZ_cf) | exact HJ5]. }
eapply (pn_callFb (fx := fx) (SK := SK) SEGS B PST ARc LAWS (@pa_segs_low _ _ PA) (wle' SEGS YGcfRehidePost.RZ_cf)
  (wle'_trans SEGS YGcfRehidePost.RZ_cf) W' regs5 mem md5
  STK_parse_noting (spZ (px_regs X)) [(px_doc X, px_doc X + 56)] (px_ly X) (px_S X) (px_Hp X) (px_W X) (px_mem X)
  (px_md X) [] ly (px_S X) (px_Hp X) k [] STK_pj_parse [(px_doc X, px_doc X + 56)] (-48) [] (SIGMA AS_pj_parse)
  (YCbqGwild.wbudget (CWX X) 0) _ _
  HJ5' ltac:(rewrite Hsp5; lia) ltac:(reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) Hret ltac:(lia) E3 E4 Hch).
- (* the callee: pj_parse's text at window 0, at CW := pn_cw X *)
  intros Hpre5.
  assert (P1 : fpre B ARc STK_pj_parse ly (px_S X) (px_Hp X) W' regs5 mem md5 []).
  { split; [exact Hpre5|]. split; [exact Hro5|]. split; [rewrite Hsp5, Eshi; lia|].
    split; [rewrite Hra5; lia | exact (pp_frm B ARc CTX0 X HPRE)]. }
  eapply (SRrG_mono SEGS (wle' SEGS YGcfRehidePost.RZ_cf)).
  + exact (HT (CWX X) (px_most X) (px_own X)
      ly (px_S X) (px_Hp X) W' regs5 mem md5 [] 0 (px_text X) (pn_len X) (px_doc X) (px_tb X) (px_Lam X) (px_peak X)
      (px_cnt X) (px_fail X) (px_ran X) P1 (Hmn5 (pp_mn B ARc CTX0 X HPRE)) (pp_univ B ARc CTX0 X HPRE)
      PCW PWR (pp_room B ARc CTX0 X HPRE) (pp_frm B ARc CTX0 X HPRE) E10 E11 E12 eq_refl P12 P13 PCEIL
      (pp_maxrun B ARc CTX0 X HPRE) P15 P16 P17 P18 P19
      HLED (pp_cnt B ARc CTX0 X HPRE) (pp_rq B ARc CTX0 X HPRE) (pp_most B ARc CTX0 X HPRE)
      (pp_live B ARc CTX0 X HPRE) P24 (pp_sec B ARc CTX0 X HPRE) (pp_c24 B ARc CTX0 X HPRE)
      (pp_hull B ARc CTX0 X HPRE)).
  + intros W2 c2 _ H2. exact (pn_fpostWF0b B ARc _ _ _ _ _ _ _ _ _ _ _ _ _ H2).
- (* the footprint is parse_noting's own *)
  apply pn_fp_sub_same.
- (* the return site +0x3c: pn_cut_S3 *)
  intros fx' W2 ly2 S2 Hp2 regs2 mem2 md2 k1 WS1 Hle Hz' Hfk' HPW HJc HJ1 HP (HQ & Hmn2).
  assert (Hsp5' : spZ regs5 = spZ (px_regs X) + -48) by lia.
  rewrite <- Hsp5' in HJ1.
  (* the caller's journal at the budget pn_cw X: pj_parse's budget WS1 has no trace outside CW *)
  assert (HJc' : ajournal_xwR (SK := SK) SEGS B PST ARc (wle' SEGS YGcfRehidePost.RZ_cf) STK_parse_noting
      (spZ (px_regs X)) [(px_doc X, px_doc X + 56)]
      (px_ly X) (px_S X) (px_Hp X) (px_W X) (px_mem X) (px_md X) [] ly2 S2 Hp2 W2 mem2 md2 (k + k1) (CWX X)).
  { pose proof (YCbqGwild.ajournal_xw_normR (SK := SK) SEGS B PST ARc (wle' SEGS YGcfRehidePost.RZ_cf)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ [] WS1 (CWX X) HJc) as HN.
    assert (Hnil : YCbqGwild.wild_fresh (CWX X) WS1 = []).
    { apply length_zero_iff_nil. unfold YCbqGwild.wbudget, YCbqGwild.wfresh in HPW. lia. }
    rewrite Hnil, app_nil_r in HN. exact HN. }
  pose proof (pn_frame_call B (@wle SEGS) (wle' SEGS YGcfRehidePost.RZ_cf) (wle' SEGS YGcfRehidePost.RZ_cf)
    X fx W' regs5 mem md5 ly (px_S X) (px_Hp X) k [] fx' W2 regs2 mem2 md2 ly2 S2 Hp2 k1
    WS1 (CWX X) STK_pj_parse [(px_doc X, px_doc X + 56)] HF5 HJc' HJ1 Hsink HP Hz' Hfk' Hmn2) as HF2.
  destruct HQ as (Hroom2 & Hhull2 & ok & res & tr & Lam' & peak' & cnt' & fail' & ran' & Hjr & Hoks & Hcnt & Hfa &
    Hpk & Hhp & Hcf & Hnr & Hled2 & Hpos & Hout & Hres).
  (* with DEAD_PJPARSE in the text, pj_parse's post carries the guarded injected-reading conjunct before its result arm
     (`match res with ..`); without it the result arm follows THE OUTCOME directly. The arm is read by its shape, so
     the segment builds on both texts. *)
  lazymatch type of Hres with _ /\ _ => destruct Hres as [_ Hres] | _ => idtac end.
  pose proof (pp_ran B ARc CTX0 X HPRE) as Hran0.
  rewrite Hran0 in Hoks.
  assert (Hbl2 : forall x, In x (ablocks B ly (px_S X)) -> In x (ablocks B ly2 S2)).
  { intros x Hx. destruct res as [t|].
    - destruct Hres as (_ & D & _ & _ & _ & _ & HabD & _ & _ & _).
      apply (Permutation_in _ (Permutation_sym HabD)). apply in_or_app. right. exact Hx.
    - destruct Hres as (_ & _ & HabN & _). apply (Permutation_in _ (Permutation_sym HabN)). exact Hx. }
  assert (Hby2 : bytes_at W2 mem2 (px_text X) (px_tb X)).
  { destruct P12 as (Hby & _). unfold bytes_at in *.
    apply (pn2_garr8_kept (w_H W') (w_H W2) mem mem2 _ _); [|exact Hby].
    intros i Hi. eapply (pn2_text_keptR B (wle' SEGS YGcfRehidePost.RZ_cf));
      [exact HJ1 | exact HLED | exact Hsink | exact Hbl2 | exact P13 | exact Hfp |].
    unfold pn_len. lia. }
  apply (SRrG_ret SEGS (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf)).
  exists fx', regs2, mem2, md2, ly2, S2, Hp2, (k + k1), Lam', peak', cnt', fail', ran', ok, res, tr.
  split.
  { rewrite pn_cfg_eq, E1.
    replace (PN_SLOT0 + PN_S3) with (PN_SLOT0 + PN_S2 + 4 + 4 + 4 + 4 + 4) by (unfold PN_S2, PN_S3; lia).
    reflexivity. }
  split; [exact HF2|].
  split; [transitivity (getr regs5 8); [exact (HP 8 ltac:(unfold acallee_saved; lia)) | exact E8]|].
  split; [transitivity (getr regs5 9); [exact (HP 9 ltac:(unfold acallee_saved; lia)) | exact E9]|].
  split; [exact Hhull2|]. split; [exact Hroom2|].
  unfold pn_R.
  split; [exact Hjr|].
  split.
  { (* the live requests, from the blocks (PN102BS2Help.v section 4) *)
    destruct res as [t|].
    - destruct Hres as (_ & D & _ & HDs & _ & _ & HabD & _ & _ & _).
      exact (pn2_live_some B ReaderRes.jr_strtod (px_tb X) ok t tr ly (px_S X) ly2 S2 D Hjr HDs HabD).
    - destruct Hres as (_ & _ & HabN & _).
      exact (pn2_live_none B ReaderRes.jr_strtod (px_tb X) ok tr ly (px_S X) ly2 S2 Hjr HabN). }
  split; [exact Hpos|].
  split.
  { (* THE OUTCOME: pj_parse's, with g_ran_out = 0 at entry *)
    intros sm x os i H0 hist Hr1 Hr2 Hr3 Hr4.
    destruct (Hout sm x os i H0 hist Hr1 Hr2 Hr3 Hr4) as (Er & Ej & Ee & Hh).
    split; [rewrite Er; exact Hran0|]. exact (conj Ej (conj Ee Hh)). }
  split; [exact Hoks|].
  split; [exact Hcnt|].
  split; [exact Hfa|].
  split; [exact Hpk|].
  split; [exact Hhp|].
  split; [exact Hcf|].
  split; [intros Hr; exact (pn2_ran_none _ _ _ _ _ _ _ _ _ _ Hjr Hoks Hr)|].
  split.
  { (* ran' = 0 and every request within g_most (the text's RQ_pj_parse tb <= most): no refusal *)
    intros H0 Hout'.
    assert (Hg : prh_granted ok (px_cnt X) (px_fail X) (PjGrammar.calls tr)).
    { apply (pn2_granted ok (px_cnt X) (px_fail X) (PjGrammar.calls tr) (prh_ev_reqs tr) (px_most X) ran' Hoks H0).
      intros i _. pose proof (pn2_reqs_le (px_tb X) ok res tr Hjr i) as Hle1.
      pose proof (pp_most B ARc CTX0 X HPRE) as Hle2. lia. }
    destruct (Hnr Hout' Hg) as (Er & Ec').
    split; [exact Er | unfold ck_ncalls; rewrite Ec'; reflexivity]. }
  split; [exact Hby2|].
  split; [exact Hled2|].
  destruct res as [t|].
  + destruct Hres as (Ha0 & D & HLD & HDs & HDn & Hnew & HabD & HFO & Hnode & Hcap).
    split; [exact Ha0|]. exists D.
    split; [exact HLD|]. split; [exact HDs|]. split; [exact HDn|].
    split; [intros Hh; exact (pn2_rd_blocks ReaderRes.jr_strtod (px_tb X) ok _ tr D _ Hjr HDs Hh)|].
    split; [exact HFO|].
    split; [intros a kk Hin; rewrite <- Hab; exact (Hnew a kk Hin)|].
    split; [|split; [exact Hnode | exact Hcap]].
    eapply Permutation_trans; [exact HabD|]. rewrite Hab. apply Permutation_app_comm.
  + destruct Hres as (Ha0 & HLP & HabN & Hz).
    split; [exact Ha0|]. split; [exact HLP|]. split; [rewrite <- Hab; exact HabN | exact Hz].
Qed.
End I.
