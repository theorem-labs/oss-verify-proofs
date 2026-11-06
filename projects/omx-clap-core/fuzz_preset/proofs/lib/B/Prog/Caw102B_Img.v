(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/ExUtf8RunB.v, with its module paths and module names changed; 116 of its 146 lines of code are new or changed and 664 lines of the source are left out. *)
(* fuzz_preset lib/B, the #102 re-walk of check_as_written on image B' (lane CawA102R for B', h-rw-pre-5): the
   INSTANCE WITNESS of every static image premise of the walk (the 16:45Z witness rule: an image premise counts only
   beside a lemma closed by vm_compute at the real image record), and the walk's top AT THE INSTANCE.
   rule 24: no function proved. rule 24: proves no function (kind: start-up facts of check_as_written's B' walk).
   The twin of lib/A/Prog/Caw102A_Img.v e03cdb950db1.
   WHAT:
   - one closed lemma per image premise of caw_B_top (Caw102B_Top.v), at PI_prog_B (lib/B/PAImg_prog.v 15fab93fe702:
     pa_segs = rsegs of lib/B/Img0.v = images.AsanUbsan's segments, pa_val = B_prog_val, pa_sigma = B_prog_sigma,
     pa_lo / pa_hi = IMG_LO_B / IMG_TOP_B of YImgTop.v d2a97d3111ce, the relro range B_prog_relro_lo / _hi) and the
     runtime record B := YD2l.TfibB (YD2l.v 95803a8b9493; its tables YF0l.v 4a405a3dba65 / YF0m.v f82202ebccdf):
     Hent (cawb_hent), Hpst (cawb_pst: cawb_owned + cawb_errno), Hpst_img / Hpst_rw / Hpst_wr (S1ImgB.v
     pst_in_img_B / pst_not_ro_B / pst_writable_B), Hret_free (cawb_ret_free), Hfree2 (cawb_free2), PAB (cawb_pab),
     Hown_obj (cawb_own), Hmal (cawb_mal), Hown_hi (cawb_hi); PAL is h-rw-man-5's PALibB.v 5baa19c890f7 exvi_eh_palib;
   - PAB is stated at IMG_LO_B (image B's own bound; the walk reads it as the base's lower bound, not as a box), and
     cawb_band_cf proves PI_prog_B's band [pa_lo, pa_hi) EQUAL to the generated per-instance class CfImgB.CfImg_B's
     [cf_img_lo, cf_img_top) (h-mani-a8's rule), the twin of h-rw-dec-2's cnbw_band_cf (Cno102B_Wit.v c8cda7ca7340,
     on origin/cold/h-rw-dec-2-p102-R7-7-wit 5c26ed6e511a; not cited, because the tree of record does not carry
     Cno102B_Wit.v or its Cno102B_* Requires);
   - caw_B_top_inst: caw_B_top at PI_prog_B / TfibB, its premises the callee texts and runtime rows only.
   BASE OF RECORD: the kit's cut 7cdbb61b5fa0 (text lib/A/PRH_FnCheck.v c40cf3fdcd2a
   :832-902), this row's lib/B/Prog/Caw102B.v (its statements); INT102-READY (prepared at batchprep
   92d5baf78806 on the batch kit's tip e45217a4c7ba). WHAT CHANGED and why: the text lost the run-word list DW, so caw_B_top_inst
   quantifies over CTX0 only; the room counts are the text's own entry premises (:862-863), so the named argument
   CAW_CNT is no longer a premise of caw_B_top_inst. Every image premise is still closed here at PI_prog_B.
   The statics prh_pst are lib/B/PRH_ImgB.v 3216eca68342's prh_img_B (the #102 B' record, confirmed by a Theorem Labs lane 17:37Z).
   WHICH IMAGE: images.AsanUbsan is the build's pinned binary; this file is evidence for #102 B' only through the
   pins102 route (PAU pau-preset-102). PAImg_prog's certificate does not build on the old pins.
   HOW: each fact by vm_compute on a goal with no Section variable; each byte-wise fact by S1ImgA.v's pst_allb idiom (a
   vm_compute-decided boolean over every byte of every prh_pst range, then pst_allb_sound).
   PLANTED-DEFECT CONTROLS (each decides FALSE, so each decider reads the data it claims to read): cawb_hent_planted
   (the entry one word off), cawb_ret_free_planted / cawb_free2_planted / cawb_mal_planted (the return sites one word
   off), cawb_own_planted (the object one byte off), cawb_hi_planted (the lo12 off by one), cawb_owned_planted (the
   first byte of the first owned static), cawb_errno_planted (errno's first byte), cawb_img_planted / cawb_wv_planted
   (IMG_TOP_B itself, above every segment), cawb_ro_planted (the first relro byte).
   Numerals: 116 / 160 (DERIVED: the free return sites, 4 * the slot inside the function, as the segment files);
   624 / 623 (DERIVED: the `lbu`'s lo12, Caw102B_WB1.v Hown_hi); 13 / 10 (DERIVED: object / hi indices); 4 (LENGTH:
   errno, and one word in the controls); 1 (LENGTH: one byte); 0 (none). No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YK0o YCbqG YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallx YGcallcf YG0lawscf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcfRoomLive YGcfRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetReqAt PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnEx PRH_FnAlloc PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1ImgCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Caw102B Caw102B_WB1 Caw102B_Top.
(* the records and the PALib instance: Required, not Imported, and cited by qualified name *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB CfAroPresetB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PALibB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YI5b.
#[global] Remove Hints YI5b.src0_sink_head : typeclass_instances.
(* stdpp, through the LPS modules, shadows several list lemma names; the lemmas used here are Stdlib's *)
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.

#[local] Existing Instance prh_img_B.
#[local] Abbreviation TB := YD2l.TfibB.
(* THE B' SEGMENTS AND LISTING BY FULLY QUALIFIED NAME (the lead's wrong-image trap, CrcBp 19:3xZ: a short `rsegs` /
   `Img0.rsegs` can resolve to the PLAIN image's lib/Img0.v when that file is loaded too); cawb_segs_B below checks by
   reflexivity that they are PI_prog_B's, the segments the walk states over *)
#[local] Abbreviation RSEGS_B := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Img0.rsegs.
#[local] Abbreviation RELRO_LO_B := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.PAImg_prog.B_prog_relro_lo.
#[local] Abbreviation RELRO_HI_B := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.PAImg_prog.B_prog_relro_hi.
#[local] Abbreviation SIGMA_B := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.PAImg_prog.B_prog_sigma.
#[local] Abbreviation VAL_B := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.PAImg_prog.B_prog_val.
Locate rsegs.
Locate Img0.rsegs.
Locate B_prog_val.

(* ---- the byte-wise decider of the owned statics (closed: prh_img_B, TfibB's table) ---- *)
Definition cawb_zr_b (P : list (Z * Z)) (a : Z) : bool :=
  existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) P.
Lemma cawb_zr_b_complete : forall P a, Exists (in_zr a) P -> cawb_zr_b P a = true.
Proof.
intros P a H. apply Exists_exists in H as (r & Hr & Ha). unfold in_zr in Ha. apply existsb_exists.
exists r. split; [exact Hr|]. apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

(* ---- the closed facts ---- *)
Lemma cawb_hent : SIGMA_B AS_check_as_written = VAL_B A_TEXT + AF_cawB.
Proof. vm_compute. reflexivity. Qed.
Lemma cawb_ret_free : In (VAL_B A_TEXT + (AF_cawB + 116)) (pi_ret_sites F_check_as_written RT_free).
Proof. vm_compute. left. reflexivity. Qed.
Lemma cawb_free2 : VAL_B A_TEXT + (AF_cawB + 160) = pi_ret_caw_free2.
Proof. vm_compute. reflexivity. Qed.
Lemma cawb_mal : VAL_B A_TEXT + (AF_cawB + CAWB_RET) = pi_ret_caw_malloc.
Proof. vm_compute. reflexivity. Qed.
Lemma cawb_own : VAL_B (A_OBJ 13) = pi_g_own_ran_out.
Proof. vm_compute. reflexivity. Qed.
Lemma cawb_hi : VAL_B (A_HI 10) + (-624) = VAL_B (A_OBJ 13).
Proof. vm_compute. reflexivity. Qed.
Lemma cawb_owned : pst_allb (fun a => negb (cawb_zr_b (as_owned_static TB) a)) (@prh_pst prh_img_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cawb_errno :
  pst_allb (fun a => negb ((as_errno TB <=? a) && (a <? as_errno TB + 4))) (@prh_pst prh_img_B) = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- planted-defect controls: each decider FAILS on a planted bad input ---- *)
Lemma cawb_hent_planted : SIGMA_B AS_check_as_written <> VAL_B A_TEXT + (AF_cawB + 4).
Proof. vm_compute. discriminate. Qed.
Lemma cawb_ret_free_planted : ~ In (VAL_B A_TEXT + (AF_cawB + 120)) (pi_ret_sites F_check_as_written RT_free).
Proof. vm_compute. intros [H | [H | H]]; [discriminate H | discriminate H | exact H]. Qed.
Lemma cawb_free2_planted : VAL_B A_TEXT + (AF_cawB + 164) <> pi_ret_caw_free2.
Proof. vm_compute. discriminate. Qed.
Lemma cawb_mal_planted : VAL_B A_TEXT + (AF_cawB + (CAWB_RET + 4)) <> pi_ret_caw_malloc.
Proof. vm_compute. discriminate. Qed.
Lemma cawb_own_planted : VAL_B (A_OBJ 13) + 1 <> pi_g_own_ran_out.
Proof. vm_compute. discriminate. Qed.
Lemma cawb_hi_planted : VAL_B (A_HI 10) + (-623) <> VAL_B (A_OBJ 13).
Proof. vm_compute. discriminate. Qed.
Lemma cawb_owned_planted :
  pst_allb (fun a => negb (cawb_zr_b (as_owned_static TB) a)) [(fst (hd (0, 0) (as_owned_static TB)), 1)] = false.
Proof. vm_compute. reflexivity. Qed.
Lemma cawb_errno_planted :
  pst_allb (fun a => negb ((as_errno TB <=? a) && (a <? as_errno TB + 4))) [(as_errno TB, 1)] = false.
Proof. vm_compute. reflexivity. Qed.
Lemma cawb_img_planted : pst_allb (in_img_b RSEGS_B) [(IMG_TOP_B, 1)] = false.
Proof. vm_compute. reflexivity. Qed.
Lemma cawb_wv_planted : pst_allb (wv_b RSEGS_B) [(IMG_TOP_B, 1)] = false.
Proof. vm_compute. reflexivity. Qed.
Lemma cawb_ro_planted :
  pst_allb (fun a => negb (in_ro_b RSEGS_B RELRO_LO_B RELRO_HI_B a)) [(RELRO_LO_B, 1)] = false.
Proof. vm_compute. reflexivity. Qed.

(* ---- Hpst at the instance: the statics are off TfibB's owned statics and off errno ---- *)
Lemma cawb_pst : forall a, Exists (in_zr a) (@prh_pst prh_img_B) ->
  ~ Exists (in_zr a) (as_owned_static TB) /\ ~ (as_errno TB <= a < as_errno TB + 4).
Proof.
intros a Ha. split.
- intros Ho. pose proof (pst_allb_sound _ _ a cawb_owned Ha) as H. cbv beta in H.
  rewrite (cawb_zr_b_complete _ _ Ho) in H. discriminate.
- intros He. pose proof (pst_allb_sound _ _ a cawb_errno Ha) as H. cbv beta in H.
  assert (Hb : ((as_errno TB <=? a) && (a <? as_errno TB + 4)) = true)
    by (apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  rewrite Hb in H. discriminate.
Qed.

(* ---- THE TOP AT THE INSTANCE: caw_B_top at PI_prog_B / TfibB and the generated cf class CfImgB.CfImg_B (the relro
   rows read it), its premises the callee texts and runtime rows only ---- *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Existing Instance CfImgB.CfImg_B.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_room_live_a8.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PI_prog_B).
#[local] Abbreviation ARcfxB := (fun ly S Hp W mem md => ARcf SEGS TB ly S Hp W mem md /\ xs_placed_cf ly S).

(* GUARDS (the wrong-image trap): the segments, listing values, entries and relro range stated over above ARE
   PI_prog_B's, the instance the walk's top is taken at *)
Lemma cawb_segs_B : @pa_segs _ B_prog_listing PI_prog_B = RSEGS_B /\ @pa_val _ B_prog_listing PI_prog_B = VAL_B /\
  @pa_sigma _ B_prog_listing PI_prog_B = SIGMA_B /\ @pa_relro_lo _ _ PI_prog_B = RELRO_LO_B /\
  @pa_relro_hi _ _ PI_prog_B = RELRO_HI_B.
Proof. repeat split; reflexivity. Qed.
Lemma cawb_pab : @pa_lo _ _ PI_prog_B = IMG_LO_B.
Proof. reflexivity. Qed.
(* PI_prog_B's band IS the generated class CfImg_B's (h-mani-a8's per-instance cf_img_* form at B') *)
Lemma cawb_band_cf :
  @pa_lo _ _ PI_prog_B = @cf_img_lo CfImgB.CfImg_B /\ @pa_hi _ _ PI_prog_B = @cf_img_top CfImgB.CfImg_B.
Proof. split; reflexivity. Qed.

Lemma cawb_pal : PALib (L := B_prog_listing) (PI := PI_prog_B) TB.
Proof. exact PALibB.exvi_eh_palib. Qed.

(* the cf layer's relro range IS PI_prog_B's (the range equation caw_B_top's Hrelro_eq asks), by computation *)
Lemma cawb_relro_eq : @cf_relro_lo CfImgB.CfImg_B = @pa_relro_lo _ _ PI_prog_B /\
  @cf_relro_hi CfImgB.CfImg_B = @pa_relro_hi _ _ PI_prog_B.
Proof. split; vm_compute; reflexivity. Qed.

(* the top at the instance: its premises the callee texts and the runtime rows only (the room counts are the text's
   own entry premises since the batch kit's text c40cf3fdcd2a, so the named argument CAW_CNT is gone); the free / malloc
   rows are their keep twins (YGcfMallocComposeKeep.v), the relro rows CfAroPresetB.v's facts at CfImg_B *)
Theorem caw_B_top_inst :
  (forall fz : YK11.FPState, tex_value_specX (fx := fz) TB ARcfxB SK DOC_D) ->
  (forall fz : YK11.FPState, tex_ws_specX (fx := fz) TB ARcfxB SK) ->
  (forall fz : YK11.FPState, tfuzz_alloc_ran_out_specX (fx := fz) TB ARcfxB SK) ->
  (forall fz : YK11.FPState, YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fz) SEGS TB) ->
  (forall fz : YK11.FPState, YGcfMallocComposeKeep.amalloc_realizes_cf_keep (fx := fz) SEGS TB) ->
  forall (CTX0 : list (list Z)), tcheck_as_written_specX (fx := fx) TB ARcfxB SK CTX0.
Proof.
intros TEXV TEXWS TRO AFREE AMALLOC CTX0.
eapply (@caw_B_top fx rc CfImgB.CfImg_B SK PI_prog_B TB).
all: first [ exact TEXV | exact TEXWS | exact TRO | exact AFREE | exact AMALLOC | exact cawb_hent
           | exact cawb_pal | exact cawb_pst | exact pst_in_img_B | exact pst_not_ro_B | exact cawb_ret_free
           | exact cawb_free2 | exact cawb_pab | exact cawb_own | exact pst_writable_B | exact cawb_mal | exact cawb_hi
           | exact CfAroPresetB.relro_seg_preset_AU | exact (CfAroPresetB.errno_relro_preset_AU TB YD2l.TfibB_syms)
           | exact CfAroPresetB.relro_top_preset_AU | exact cawb_relro_eq | exact CfAroPresetB.ro_reads_nw_preset_AU ].
Qed.
End w.

Print Assumptions caw_B_top_inst.
Print Assumptions cawb_band_cf.
