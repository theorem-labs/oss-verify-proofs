(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: SEGMENT PRO of the ASan walk of fuzz_reply's drain
   (fuzz_reply.asan 0x830dc .. 0x831f4, 71 instructions, no call), in the form of this lane's
   lib/A/W_send_line_entry.v (a segment into a loop head) and of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8b.v.  The statement is W_drain_cx.v dr_pro_stmt.

   The prologue saves the 13 callee-saved registers at 232(sp) .. 328(sp) of its 336-byte frame, keeps the
   relay entry s in s6 and its field addresses s->buf / s->used / s->cap in s10 / s11 / s9, spills
   &s->npartial, &s->overlong, &s->held to 208(sp) / 96(sp) / 128(sp), takes g_s by PAddHi (A_OBJ 22) into
   s2 with g_s >> 3 in s1 and (g_s + 4) >> 3 in s0, loads the shadow base from the GOT (A_OBJ 0 -> A_OBJ 32)
   into s5, and writes the shifted field addresses of g_s and the shadow addresses of s's cells into the
   frame.  No call, no shadow check, no store outside [sp0 - 336, sp0): every representation the outer loop's
   head carries lies below alloc_ceiling + 8 (a live block, the image band) and moves across the stores. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_drain_pro.v, with its module paths, module names and numbers changed; 1682 of its 1766 lines of code are new or changed and 1187 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PjGetB.v, with its module paths and module names changed; 617 of its 693 lines of code are new or changed and 1690 lines of the source are left out. *)
(* fuzz_preset, image B' (asan-ubsan, harness fix #102: pin sha256 d663f82d7f488d30, unstripped twin c90d4fa54d43160b):
   the SHARED STATEMENTS of the segment walk of check_as_written (B' entry 0x81f78, 69 slots; slot 555 of h-verbs-1's
   whole-program listing) against K0's text tcheck_as_written_specX. Lane CawB102 of h-rw-pre-5's #102 re-walk.
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).
   THE PLAN IS THE SPEC: a Theorem Labs lane's plan, the internal file PLAN-cno-caw-102.md section 5.4. This file STATES (the text's binders, its
   premises and post, the cut predicates and their continuations); the segment files Caw102B_WB*.v PROVE; WB1 and the
   top are this lane's since 19:2xZ (a Theorem Labs lane released).
   INPUTS, BY PATH (blobs):
    - base: the kit's cut, merged forward into this row's head, this
      lane's caw B' files over it; ready for the #102 integration (prepared on the #102 integration line and the batch tip,
      lead 03:0xZ). The kit, as the cut carries it, by path: lib/A/PRH_FnCheck.v
      c40cf3fdcd2a (tcheck_as_written_specX :832-902: NO run-word list DW (:841; PRH_Base.v :1179-1213); the ROOM
      COUNTS `sec_cnt S <= LSEC + DRV`, `ccnt24 S <= L24 + DRV` as entry premises after room_live_cf S (:862-863); a
      NEW post conjunct THE OUTCOME (:879-888): under a consumer window prh_cons_from .. i 2 at a run position i at S
      whose next events are the scratch pair, r = 0 and S' is the position i + 2), PRH_Base.v,
      PRH_Refute.v blob 23f7a37f01c9 (prh_refute_at), PresetRoomPosKeep.v,
      PresetRoomCounts.v, PresetFreeFo.v; the P'' engine as the cut carries it (lib/Reusable: YCbqG
      (journal read by ajx_*, built by ajx_intro), YG01 blob 845507e218b0 (admits / admits_fix),
      YGcallMxmn blob 3c08bbab8292, ...); YCej.v blob 71ae24321ba4 (the
      Univ form with the P'' set, owner 00:52Z). Every other image / start-up / generated file is the cut's (PRH_ImgB,
      YD2l, YF0l, YF0m, YImgCellsB, YB13, PALibB 5baa19c890f7, YImgTop, PresetCfnA / PresetCfnB).
    - Listing: #102 listings v3 (owner 16:28Z), origin/cold/h-verbs-1-listing-pins102 74dcda1eda12: lib/B/Listing_prog.v
      c97cc46b3e13 (d42e123915ae's listing 8bcc2c9e7809, header comment only changed; YPsym.v b6f5a85d234d).
      lib/B/PAImg_prog.v is NOT Required: the walk is PARAMETRIC over {PA : PAImg B_prog_listing} and uses the
      listing's own tables (PL_caw_B below); its instance PI_prog_B is witnessed in Caw102B_Img.v (pins102 only).
      Slot check on d42e123915ae (this lane, 13:1xZ): the 69 slots of caw B' are the pin's words or the same
      relocations as on 1678fc5f0191 but for the g_own_ran_out load 0x82024, PLdHi .. (A_OBJ 13) (13 = g_own_ran_out).
    - Engine and cf-instance files: the P'' set as the cut carries it (above); the lane kit files, by path:
      lib/A/Prog/H2CawPure.v af16a877672b (a working branch 1934271f1f4); PRW_StepKit.v 0df3991c13f4 is int102's.
   FORM (rulings 12:18Z-13:26Z): generic P, abstract in every proof; each segment is a CONTINUATION lemma over a generic
   Q: `caw_K_<next>R R C P Q -> caw_K_<this>R R C P Q` (an R form takes the world relation R first, a plain form drops it; the image-A' walk Caw102A_WA* has the same shape), the End segment concludes
   caw_post. The allocator relation is the cf instance ARcfx (as FuzzFreeB.v / H2CawF.v), the image parametric.
   THE ROOM COUNTS (CAW_CNT DISCHARGED BY CONVERSION): the batch text has them as entry premises (:862-863), caw_pre's
     23rd / 24th conjuncts in the text's order; caw_cnt C is literally their conjunction (caw_pre_cnt, Qed). The
     segments that need it (WB1 / WB2 / WB3) still take caw_cnt C after caw_pre C; the top supplies caw_pre_cnt.
   THE OUTCOME (:879-888): the refused arm is DEAD under the run hypothesis. caw_dead C (state-free: it names only the
     entry state) is proved at WB1's NULL arm from the malloc's granted NULL path (PRH_Refute.prh_refute_at) and carried
     by cut_end's r = 1 arm; the post's outcome conjunct follows from it there and from caw_prog C (caw_evs C) on the
     r = 0 arm. caw_pre is read BY NAME (caw_pre_* below), never positionally.
   THE OTHER INPUTS: the memnorm keep across __wrap_free is YGcallMxmnKeep.aj_free_x_ct_m_rh_keep's last conjunct (the segments
     take the runtime row YGcfMallocComposeKeep.afree_realizes_cf_rh_keep as a callee text); g_own_ran_out / g_most: EVERY cut carries `caw_ledger C ..
     own` LAST (the kit's Batch 2), 0 up to WB1's NULL-arm store, own at cut_end.
   THE RUN POSITION (f97c, the post-implication form; the cno B' base's cnb_prog shape, Cno102B_Base.v b5421fc37cbc
     :386, without its live-set conjunct): each cut carries caw_prog C E S for the events E made since entry: [] at
     cut_mal, caw_ev1 C = [HMal (size + 1)] at cut_ev / cut_ws, caw_evs C = [HMal (size + 1); HFr (size + 1)] at
     cut_oA / cut_oB / cut_ck, per arm at cut_end (r = 1 with [], r = 0 with caw_evs C), which IS the text's post.
   Numerals: 80 (LENGTH: the frame, `addi sp, sp, -0x50`), 8 / 16 / 24 / 32 / 40 / 48 / 56 / 64 / 72 (LENGTH: the
   frame's sd / ld offsets off sp, read on the listing), the cut offsets 68 .. 264 (DERIVED: 4 * the slot inside the
   function), 555 (DERIVED: caw's slot in the listing, = B_prog_slot AS_check_as_written of PAImg_prog.v 15fab93fe702
   :418; the image fact Hent of the segment files ties it to pa_sigma), register numbers (WORD). No ADDRESS. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetReqAt PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnEx PRH_FnAlloc PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_StepKit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YI5b.
(* the PLAIN build's sink head must never fill SK here (YC1fP.v:23-33 does the same): every SK below is explicit *)
#[global] Remove Hints YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the listing's own tables (PAImg_prog.v 4392ab2c09ba :177-181, the same terms; Required from no file that needs
   IMG_TOP_B): the engine's vm_compute needs a closed table, so the walk passes PL := PL_caw_B ---- *)
Definition B_prog_tpi_caw : ptree asym := ptree_of_list B_prog_listing.
Definition B_prog_tw_caw : ctable := Eval vm_compute in (tw_of 0 B_prog_listing).
Definition PL_caw_B : PAListing B_prog_listing :=
{| pl_tpi := B_prog_tpi_caw; pl_tpi_eq := eq_refl; pl_tw := B_prog_tw_caw; pl_tw_eq := ltac:(vm_compute; reflexivity);
pl_lim := ltac:(vm_compute; reflexivity); pl_len := ltac:(vm_compute; discriminate); pl_slot0 := ltac:(vm_compute; exact I) |}.

(* ---- the function's place in the listing and its cut offsets (DERIVED: 4 * the slot inside the function) ---- *)
Definition CAWB_SLOT : nat := 555.
Definition AF_cawB : Z := 4 * Z.of_nat CAWB_SLOT.
Definition CAWB_MAL : Z := 68.      (* 0x81fbc  jal __wrap_malloc          (WB0 -> WB1) *)
Definition CAWB_EV : Z := 76.       (* 0x81fc4  the scratch non-NULL       (WB1 -> WB2) *)
Definition CAWB_WS : Z := 136.      (* 0x82000  ex_value returned 0        (WB2 -> WB3) *)
Definition CAWB_OA : Z := 164.      (* 0x8201c  want := -1                 (WB2 / WB3 -> WB4) *)
Definition CAWB_OB : Z := 168.      (* 0x82020  the g_own_ran_out test     (WB3 / WB4a -> WB4) *)
Definition CAWB_CK : Z := 192.      (* 0x82038  the two property checks    (WB4 -> WB5) *)
Definition CAWB_END : Z := 224.     (* 0x82058  a0 := s1, the epilogue     (WB1 / WB4 / WB5 -> WB6) *)
Definition CAWB_FRAME : Z := 80.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {SK : YI16.sink_head}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
#[local] Existing Instance prh_room_live_a8.
Context {PA : PAImg B_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Abbreviation VAL := (@pa_val _ B_prog_listing PA).
#[local] Abbreviation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Abbreviation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Abbreviation STK := (STK_check_as_written (PI := prh_img_B)).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Section f.
Variable B : asyms.
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
#[local] Abbreviation AJ := (ajournal_x (SK := SK) SEGS B prh_pst ARcfx).
#[local] Abbreviation LEDGER := (prh_ledger B).

(* ---- the text's binders (tcheck_as_written_specX, PRH_FnCheck.v c40cf3fdcd2a :833 @7cdbb61b5fa0) and the call-context
   closure's argument (the run-word list DW is gone) ---- *)
Record cawB : Type := mkCawB {
  c_ly : alayout; c_S : astate; c_Hp : list Z; c_W : world SEGS;
  c_regs : bvmap 5 word; c_mem : word -> option byte; c_md : Model; c_ch : list (Z * Z * Z);
  c_data : Z; c_x : list Z; c_rc : Z; c_doc : Z; c_t : PjTree.jv; c_D : list (Z * Z);
  c_Lam : list (Z * Z); c_peak : Z; c_cnt : Z; c_fail : Z; c_ran : Z; c_most : Z;
  c_CTX0 : list (list Z)
}.
Definition c_size (C : cawB) : Z := Z.of_nat (length (c_x C)).
Definition c_sp (C : cawB) : Z := spZ (c_regs C).

(* ---- the text's 27 premises (PRH_FnCheck.v:1316-1363), in their order (the room counts :1343-1344, the hull budget :1349 and HPOS :1359-1362 are new) ---- *)
Definition caw_pre (C : cawB) : Prop :=
  fpre B ARcfx STK (c_ly C) (c_S C) (c_Hp C) (c_W C) (c_regs C) (c_mem C) (c_md C) (c_ch C) /\
  YAkMemnorm.memnorm SEGS (c_mem C) /\
  prh_univ_closure B (c_CTX0 C) /\
  getr (c_regs C) 10 = w64 (c_data C) /\ getr (c_regs C) 11 = w64 (c_size C) /\
  getr (c_regs C) 12 = w64 (c_rc C) /\ getr (c_regs C) 13 = w64 (c_doc C) /\
  - 2 ^ 31 <= c_rc C < 2 ^ 31 /\ 0 <= c_doc C < 2 ^ 64 /\
  c_size C <= 3 * 2 ^ 20 /\ 0 < c_data C /\ c_data C + c_size C < 2 ^ 62 /\
  src_rd (c_W C) (c_mem C) (c_data C) (c_x C) /\
  (0 < c_size C -> prhex_inblk B (c_ly C) (c_S C) (c_Hp C) (c_data C) (c_size C)) /\
  (c_rc C = 0 /\ ck_read (c_x C) = Some (c_t C) \/ c_rc C <> 0 /\ ck_read (c_x C) = None) /\
  (c_rc C = 0 -> ck_tree_ok (c_ly C) (c_S C) (c_Lam C) (c_W C) (c_mem C) (c_doc C) (c_t C) (c_D C)) /\
  LEDGER (c_ly C) (c_S C) (c_Hp C) (c_W C) (c_mem C) (c_Lam C) (c_peak C) (c_cnt C) (c_fail C) (c_ran C) (c_most C) 0 /\
  c_ran C = 0 /\
  blocks_bytes (c_S C) + LIVE_check_as_written (c_size C) <= LIVE_MAX /\ c_size C + 1 < cf_malloc_max /\
  Z.of_nat (length (frames (c_S C))) <= ck_FRAMES_CAP - FR_check_as_written /\
  room_live_cf (c_S C) /\
  YGcfRoomLive.sec_cnt (c_S C) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV /\
  YGcfRoomLive.ccnt24 (c_S C) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV /\
  (* the hull budget of the scratch pair and the run position at entry (HPOS): the text's two premises before
     ck_frm0, in its spelling *)
  PresetHullBudget.hull_budget (c_S C) [PresetReqAt.HMal (c_size C + 1); PresetReqAt.HFr (c_size C + 1)] /\
  (exists (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat)
     (rp_H0 : list Z) (rp_hist : list YG00.chunk),
     (length rp_os <= 4)%nat /\ PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist (c_S C) /\
     PRH_Base.prh_run_at rp_sm rp_x rp_os rp_i [PresetReqAt.HMal (c_size C + 1)]) /\
  ck_frm0.

(* ---- caw_pre BY NAME: one projection per conjunct, in the text's order ---- *)
Section pre_proj.
Variable C : cawB.
Hypothesis HP : caw_pre C.
Lemma caw_pre_fpre : fpre B ARcfx STK (c_ly C) (c_S C) (c_Hp C) (c_W C) (c_regs C) (c_mem C) (c_md C) (c_ch C).
Proof. destruct HP as (H & _). exact H. Qed.
Lemma caw_pre_mn : YAkMemnorm.memnorm SEGS (c_mem C).
Proof. destruct HP as (_ & H & _). exact H. Qed.
Lemma caw_pre_univ : prh_univ_closure B (c_CTX0 C).
Proof. destruct HP as (_ & _ & H & _). exact H. Qed.
Lemma caw_pre_r10 : getr (c_regs C) 10 = w64 (c_data C).
Proof. destruct HP as (_ & _ & _ & H & _). exact H. Qed.
Lemma caw_pre_r11 : getr (c_regs C) 11 = w64 (c_size C).
Proof. destruct HP as (_ & _ & _ & _ & H & _). exact H. Qed.
Lemma caw_pre_r12 : getr (c_regs C) 12 = w64 (c_rc C).
Proof. destruct HP as (_ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma caw_pre_r13 : getr (c_regs C) 13 = w64 (c_doc C).
Proof. destruct HP as (_ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma caw_pre_rc : - 2 ^ 31 <= c_rc C < 2 ^ 31.
Proof. destruct HP as (_ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma caw_pre_doc : 0 <= c_doc C < 2 ^ 64.
Proof. destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma caw_pre_size : c_size C <= 3 * 2 ^ 20.
Proof. destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma caw_pre_data0 : 0 < c_data C.
Proof. destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma caw_pre_data62 : c_data C + c_size C < 2 ^ 62.
Proof. destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma caw_pre_src : src_rd (c_W C) (c_mem C) (c_data C) (c_x C).
Proof. destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma caw_pre_inblk : 0 < c_size C -> prhex_inblk B (c_ly C) (c_S C) (c_Hp C) (c_data C) (c_size C).
Proof. destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma caw_pre_case : c_rc C = 0 /\ ck_read (c_x C) = Some (c_t C) \/ c_rc C <> 0 /\ ck_read (c_x C) = None.
Proof. destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma caw_pre_tree : c_rc C = 0 -> ck_tree_ok (c_ly C) (c_S C) (c_Lam C) (c_W C) (c_mem C) (c_doc C) (c_t C) (c_D C).
Proof. destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma caw_pre_ledger :
  LEDGER (c_ly C) (c_S C) (c_Hp C) (c_W C) (c_mem C) (c_Lam C) (c_peak C) (c_cnt C) (c_fail C) (c_ran C) (c_most C) 0.
Proof. destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma caw_pre_ran : c_ran C = 0.
Proof. destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma caw_pre_live : blocks_bytes (c_S C) + LIVE_check_as_written (c_size C) <= LIVE_MAX.
Proof. destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma caw_pre_max : c_size C + 1 < cf_malloc_max.
Proof. destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma caw_pre_frames : Z.of_nat (length (frames (c_S C))) <= ck_FRAMES_CAP - FR_check_as_written.
Proof. destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma caw_pre_room : room_live_cf (c_S C).
Proof.
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H.
Qed.
Lemma caw_pre_sec : YGcfRoomLive.sec_cnt (c_S C) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV.
Proof.
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _).
exact H.
Qed.
Lemma caw_pre_c24 : YGcfRoomLive.ccnt24 (c_S C) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.
Proof.
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _).
exact H.
Qed.
Lemma caw_pre_hull :
  PresetHullBudget.hull_budget (c_S C) [PresetReqAt.HMal (c_size C + 1); PresetReqAt.HFr (c_size C + 1)].
Proof.
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _).
exact H.
Qed.
Lemma caw_pre_hpos :
  exists (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat)
    (rp_H0 : list Z) (rp_hist : list YG00.chunk),
    (length rp_os <= 4)%nat /\ PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist (c_S C) /\
    PRH_Base.prh_run_at rp_sm rp_x rp_os rp_i [PresetReqAt.HMal (c_size C + 1)].
Proof.
destruct HP
  as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _).
exact H.
Qed.
Lemma caw_pre_frm0 : ck_frm0.
Proof.
destruct HP
  as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H).
exact H.
Qed.
End pre_proj.

(* ---- THE ROOM COUNTS (formerly the named argument CAW_CNT): the conjunction of the text's two count premises
   (PRH_FnCheck.v:1343-1344), discharged BY CONVERSION (caw_pre_cnt) ---- *)
Definition caw_cnt (C : cawB) : Prop :=
  YGcfRoomLive.sec_cnt (c_S C) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV /\
  YGcfRoomLive.ccnt24 (c_S C) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.
Lemma caw_pre_cnt : forall C, caw_pre C -> caw_cnt C.
Proof. intros C HP. exact (conj (caw_pre_sec C HP) (caw_pre_c24 C HP)). Qed.

(* ---- the scratch's run events: malloc (size + 1) granted, then its free (PresetRun.call_rest's pair) ---- *)
Definition caw_ev1 (C : cawB) : list PresetReqAt.hev := [PresetReqAt.HMal (c_size C + 1)].
Definition caw_evs (C : cawB) : list PresetReqAt.hev :=
  [PresetReqAt.HMal (c_size C + 1); PresetReqAt.HFr (c_size C + 1)].

(* ---- THE PROGRESS FACT a cut carries for the events E made since entry (the A' base's caw_prog; the cno B' base's
   cnb_prog without its live-set conjunct) ---- *)
Definition caw_prog (C : cawB) (E : list PresetReqAt.hev) (S3 : astate) : Prop :=
  forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
    PresetRoomPos.iface_room_pos sm x0 os i H0 hist (c_S C) -> PRH_Base.prh_run_at sm x0 os i E ->
    exists hist', PresetRoomPos.iface_room_pos sm x0 os (i + length E)%nat H0 hist' S3.
(* ---- THE OUTCOME's dead arm (PRH_FnCheck.v c40cf3fdcd2a :879-888): at any run position i at the ENTRY state whose
   next events are the scratch pair and whose allocation is a consumer event, the scratch was NOT refused (state-free;
   proved at WB1's NULL arm from the malloc's granted NULL path, PRH_Refute.prh_refute_at) ---- *)
Definition caw_dead (C : cawB) : Prop :=
  forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
    PresetRoomPos.iface_room_pos sm x0 os i H0 hist (c_S C) -> PRH_Base.prh_run_at sm x0 os i (caw_evs C) ->
    PRH_Base.prh_cons_from sm x0 os i (length (caw_evs C)) -> False.
Lemma caw_prog_entry : forall C, caw_prog C [] (c_S C).
Proof. intros C sm x0 os i H0 hist Hp _. exists hist. cbn [length]. rewrite Nat.add_0_r. exact Hp. Qed.
Lemma caw_firstn_app : forall {A : Type} (l E1 E2 : list A),
  firstn (length (E1 ++ E2)) l = E1 ++ E2 ->
  firstn (length E1) l = E1 /\ firstn (length E2) (skipn (length E1) l) = E2.
Proof.
intros A l E1 E2. revert l. induction E1 as [|e E1 IH]; intros l H.
- cbn [app length firstn skipn] in H |- *. split; [reflexivity | exact H].
- destruct l as [|y l]; cbn [app length firstn] in H; [discriminate H|].
  injection H as Hy H. subst y. destruct (IH l H) as [H1 H2].
  cbn [length firstn skipn]. split; [f_equal; exact H1 | exact H2].
Qed.
Lemma caw_skipn_add : forall {A : Type} (n m : nat) (l : list A), skipn n (skipn m l) = skipn (m + n) l.
Proof.
intros A n m. induction m as [|m IH]; intros l; [reflexivity|].
destruct l as [|y l]; cbn; [destruct n; reflexivity | exact (IH l)].
Qed.
Lemma caw_run_at_app : forall sm x0 os i (E1 E2 : list PresetReqAt.hev),
  PRH_Base.prh_run_at sm x0 os i (E1 ++ E2) ->
  PRH_Base.prh_run_at sm x0 os i E1 /\ PRH_Base.prh_run_at sm x0 os (i + length E1)%nat E2.
Proof.
intros sm x0 os i E1 E2 H. unfold PRH_Base.prh_run_at in *.
destruct (caw_firstn_app _ E1 E2 H) as [H1 H2]. split; [exact H1|].
rewrite <- caw_skipn_add. exact H2.
Qed.
Lemma caw_run_at_nth : forall sm x0 os i (e : PresetReqAt.hev) (E : list PresetReqAt.hev),
  PRH_Base.prh_run_at sm x0 os i (e :: E) -> nth_error (PresetRun.hruns sm x0 os) i = Some e.
Proof.
intros sm x0 os i e E. unfold PRH_Base.prh_run_at.
remember (PresetRun.hruns sm x0 os) as l eqn:El. clear El. revert l.
induction i as [|i IH]; intros l H; destruct l as [|z l]; cbn in H |- *; try discriminate.
- injection H as -> _. reflexivity.
- exact (IH l H).
Qed.

(* ---- the text's post body, VERBATIM at the record (PRH_FnCheck.v c40cf3fdcd2a :874-902): the ledger at own', THE
   OUTCOME under the run hypothesis, the position in the post-implication form keyed on the scratch's own grant ---- *)
Definition caw_Q (C : cawB) :
  alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
    room_live_cf S' /\ Hp' = c_Hp C /\ ablocks B ly' S' = ablocks B (c_ly C) (c_S C) /\
    exists own', LEDGER ly' S' Hp' W' mem' (c_Lam C) (c_peak C) (c_cnt C) (c_fail C) (c_ran C) (c_most C) own' /\
    bytes_at W' mem' (c_data C) (c_x C) /\
    exists r, getr regs' 10 = w64 r /\
     (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
        (H0 : list Z) (hist : list YG00.chunk),
        PresetRoomPos.iface_room_pos sm x0 os i H0 hist (c_S C) ->
        PRH_Base.prh_run_at sm x0 os i [PresetReqAt.HMal (c_size C + 1); PresetReqAt.HFr (c_size C + 1)] ->
        PRH_Base.prh_cons_from sm x0 os i (length [PresetReqAt.HMal (c_size C + 1); PresetReqAt.HFr (c_size C + 1)]) ->
        r = 0 /\ exists hist', PresetRoomPos.iface_room_pos sm x0 os
          (i + length [PresetReqAt.HMal (c_size C + 1); PresetReqAt.HFr (c_size C + 1)])%nat H0 hist' S') /\
     ((r = 1 /\ own' = 1 /\ (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
        (H0 : list Z) (hist : list YG00.chunk),
        PresetRoomPos.iface_room_pos sm x0 os i H0 hist (c_S C) -> PRH_Base.prh_run_at sm x0 os i (@nil PresetReqAt.hev) ->
        exists hist', PresetRoomPos.iface_room_pos sm x0 os (i + length (@nil PresetReqAt.hev))%nat H0 hist' S')) \/
      (r = 0 /\ own' = 0 /\
       (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
       (H0 : list Z) (hist : list YG00.chunk),
       PresetRoomPos.iface_room_pos sm x0 os i H0 hist (c_S C) ->
       PRH_Base.prh_run_at sm x0 os i [PresetReqAt.HMal (c_size C + 1); PresetReqAt.HFr (c_size C + 1)] ->
       exists hist', PresetRoomPos.iface_room_pos sm x0 os
         (i + length [PresetReqAt.HMal (c_size C + 1); PresetReqAt.HFr (c_size C + 1)])%nat H0 hist' S') /\
        (c_rc C = 0 -> pj_nodeR SEGS (rdW W' mem') (prh_lin (c_Lam C)) (c_doc C) (c_t C) (c_D C)))).
Definition caw_post (C : cawB) : world SEGS -> config -> Prop :=
  fpostF B ARcfx SK STK [] (c_regs C) (c_ly C) (c_S C) (c_Hp C) (c_W C) (c_mem C) (c_md C) (caw_Q C).

(* ---- what the cuts share ---- *)
(* the journal from entry: the function's own frame on the real stack, no fake frame, FP empty *)
Definition caw_J (C : cawB) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world SEGS)
  (mem3 : word -> option byte) (md3 : Model) (k : Z) : Prop :=
  AJ STK (c_sp C) [] (c_ly C) (c_S C) (c_Hp C) (c_W C) (c_mem C) (c_md C) [] ly3 S3 Hp3 W3 mem3 md3 k.
(* caw_J over a world relation R: ajournal_xR R in place of ajournal_x (AJ), every argument as caw_J's *)
Definition caw_JR (R : world SEGS -> world SEGS -> Prop) (C : cawB) (ly3 : alayout) (S3 : astate) (Hp3 : list Z)
  (W3 : world SEGS) (mem3 : word -> option byte) (md3 : Model) (k : Z) : Prop :=
  ajournal_xR (SK := SK) SEGS B prh_pst ARcfx R STK (c_sp C) [] (c_ly C) (c_S C) (c_Hp C) (c_W C) (c_mem C) (c_md C)
    [] ly3 S3 Hp3 W3 mem3 md3 k.
Lemma caw_J_R_wle : forall C ly3 S3 Hp3 W3 mem3 md3 k,
  caw_J C ly3 S3 Hp3 W3 mem3 md3 k = caw_JR (@wle SEGS) C ly3 S3 Hp3 W3 mem3 md3 k.
Proof. reflexivity. Qed.
(* gp, tp and the callee-saved registers the function never writes, at their entry values *)
Definition caw_kregs (C : cawB) (regs3 : bvmap 5 word) : Prop :=
  forall r : bv 5, In r [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs3 r = getr (c_regs C) r.
(* the prologue's four saves: ra at sp0 - 8, s0 at - 16, s1 at - 24, s2 at - 32 (B' 0x81f7c-0x81f88) *)
Definition caw_saved (C : cawB) (W3 : world SEGS) (mem3 : word -> option byte) : Prop :=
  val_mem SEGS (rdW W3 mem3) (c_sp C - 8) 8 (bv_unsigned (getr (c_regs C) 1)) /\
  val_mem SEGS (rdW W3 mem3) (c_sp C - 16) 8 (bv_unsigned (getr (c_regs C) 8)) /\
  val_mem SEGS (rdW W3 mem3) (c_sp C - 24) 8 (bv_unsigned (getr (c_regs C) 9)) /\
  val_mem SEGS (rdW W3 mem3) (c_sp C - 32) 8 (bv_unsigned (getr (c_regs C) 18)).
(* the scratch expected() took (__wrap_malloc (size + 1)), new since entry *)
Definition caw_scr (C : cawB) (ly3 : alayout) (S3 : astate) (scr : Z) : Prop :=
  4096 <= scr /\ ablocks B ly3 S3 = ablocks B (c_ly C) (c_S C) ++ [(scr, c_size C + 1)].
(* every cut after the prologue: the float state fy (ex_value's after its call), the journal, the registers kept,
   sp = sp0 - 80, s0 = rc, the saves, Hp, the room (the ledger is each cut's last conjunct, caw_ledger) *)
Definition caw_base (C : cawB) (fy : YK11.FPState) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world SEGS)
  (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) (k : Z) : Prop :=
  frm_zero (@YK11.fp_csr fy) /\ fregs_kept_x fx fy /\
  caw_J C ly3 S3 Hp3 W3 mem3 md3 k /\ caw_kregs C regs3 /\ spZ regs3 = c_sp C - CAWB_FRAME /\
  getr regs3 8 = w64 (c_rc C) /\ caw_saved C W3 mem3 /\ Hp3 = c_Hp C /\ room_live_cf S3.
(* caw_base over a world relation R: the journal conjunct caw_JR R, every other conjunct as caw_base's *)
Definition caw_baseR (R : world SEGS -> world SEGS -> Prop) (C : cawB) (fy : YK11.FPState) (ly3 : alayout)
  (S3 : astate) (Hp3 : list Z) (W3 : world SEGS) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model)
  (k : Z) : Prop :=
  frm_zero (@YK11.fp_csr fy) /\ fregs_kept_x fx fy /\
  caw_JR R C ly3 S3 Hp3 W3 mem3 md3 k /\ caw_kregs C regs3 /\ spZ regs3 = c_sp C - CAWB_FRAME /\
  getr regs3 8 = w64 (c_rc C) /\ caw_saved C W3 mem3 /\ Hp3 = c_Hp C /\ room_live_cf S3.
Lemma caw_base_R_wle : forall C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k,
  caw_base C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k = caw_baseR (@wle SEGS) C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k.
Proof. reflexivity. Qed.
(* the struct ex at sp + 8 = sp0 - 72: p, end, and the 8 bytes of depth + pad at sp0 - 56 *)
Definition caw_ex3 (C : cawB) (W3 : world SEGS) (mem3 : word -> option byte) (p : Z) : Prop :=
  val_mem SEGS (rdW W3 mem3) (c_sp C - 72) 8 p /\ val_mem SEGS (rdW W3 mem3) (c_sp C - 64) 8 (c_data C + c_size C).
(* the ledger at a cut (the kit's Batch 2, decff67d721f): the entry's values, the record's most, and own, the byte
   g_own_ran_out holds at the cut (prh_ledger_own reads it; a hand step writes it only at WB1's NULL-arm
   `sb 1, g_own_ran_out`). The same spelling as the A' base's caw_ledger; it replaces the caw_pst threading of
   61529ce7f9ec by citation. *)
Definition caw_ledger (C : cawB) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world SEGS)
  (mem3 : word -> option byte) (own : Z) : Prop :=
  LEDGER ly3 S3 Hp3 W3 mem3 (c_Lam C) (c_peak C) (c_cnt C) (c_fail C) (c_ran C) (c_most C) own.

(* ---- the cut predicates ---- *)
(* CAWB_MAL (B' 0x81fbc, the jal of __wrap_malloc; WB0's exit, WB1's entry): float state the entry's, s1 = doc, a0 =
   size + 1, s2 the entry's, the struct's first three words, no block or frame change, no event yet *)
Definition cut_mal (C : cawB) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world SEGS)
  (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) (k : Z) : Prop :=
  caw_base C fx ly3 S3 Hp3 W3 regs3 mem3 md3 k /\
  getr regs3 9 = w64 (c_doc C) /\ getr regs3 18 = getr (c_regs C) 18 /\ getr regs3 10 = w64 (c_size C + 1) /\
  caw_ex3 C W3 mem3 (c_data C) /\ val_mem SEGS (rdW W3 mem3) (c_sp C - 56) 8 0 /\
  ablocks B ly3 S3 = ablocks B (c_ly C) (c_S C) /\ frames S3 = frames (c_S C) /\
  caw_prog C [] S3 /\
  caw_ledger C ly3 S3 Hp3 W3 mem3 0 /\
  PresetHullBudget.hull_budget S3 [PresetReqAt.HMal (c_size C + 1); PresetReqAt.HFr (c_size C + 1)].
(* CAWB_EV (B' 0x81fc4, after `beqz a0` not taken; WB1's non-NULL exit, WB2's entry): a0 = scr, the new block, the
   malloc event made (caw_prog at caw_ev1) *)
Definition cut_ev (C : cawB) (fy : YK11.FPState) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world SEGS)
  (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) (k scr : Z) : Prop :=
  caw_base C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k /\
  getr regs3 9 = w64 (c_doc C) /\ getr regs3 18 = getr (c_regs C) 18 /\ getr regs3 10 = w64 scr /\
  caw_ex3 C W3 mem3 (c_data C) /\ val_mem SEGS (rdW W3 mem3) (c_sp C - 56) 8 0 /\
  caw_scr C ly3 S3 scr /\ frames S3 = frames (c_S C) /\ caw_prog C (caw_ev1 C) S3 /\
  caw_ledger C ly3 S3 Hp3 W3 mem3 0 /\
  PresetHullBudget.hull_budget S3 [PresetReqAt.HFr (c_size C + 1)].
(* CAWB_WS (B' 0x82000, ex_value returned 0, `beqz a0` taken; WB2 -> WB3): the struct after the reading (p = data +
   p', depth 0, scratch, differs dl'), the reading's result *)
Definition cut_ws (C : cawB) (fy : YK11.FPState) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world SEGS)
  (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) (k scr dl' : Z) (u : PjTree.jv) (rest : list Z)
  : Prop :=
  caw_base C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k /\
  getr regs3 9 = w64 (c_doc C) /\ getr regs3 18 = getr (c_regs C) 18 /\
  prhex_V 0 (c_x C) = Some (u, rest) /\
  caw_ex3 C W3 mem3 (c_data C + c_size C - Z.of_nat (length rest)) /\
  val_mem SEGS (rdW W3 mem3) (c_sp C - 56) 4 0 /\ val_mem SEGS (rdW W3 mem3) (c_sp C - 48) 8 scr /\
  val_mem SEGS (rdW W3 mem3) (c_sp C - 40) 4 dl' /\ (dl' = 0 \/ dl' = 1) /\
  (dl' = 1 <-> c_rc C = 0 /\ c_t C <> u) /\
  caw_scr C ly3 S3 scr /\ caw_prog C (caw_ev1 C) S3 /\
  caw_ledger C ly3 S3 Hp3 W3 mem3 0 /\
  PresetHullBudget.hull_budget S3 [PresetReqAt.HFr (c_size C + 1)].
(* cut_oA over a world relation R: caw_baseR R in place of caw_base *)
Definition cut_oAR (R : world SEGS -> world SEGS -> Prop) (C : cawB) (fy : YK11.FPState) (ly3 : alayout)
  (S3 : astate) (Hp3 : list Z) (W3 : world SEGS) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model)
  (k : Z) : Prop :=
  caw_baseR R C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k /\ c_rc C <> 0 /\
  ablocks B ly3 S3 = ablocks B (c_ly C) (c_S C) /\ caw_prog C (caw_evs C) S3 /\
  caw_ledger C ly3 S3 Hp3 W3 mem3 0.
(* CAWB_OA (B' 0x8201c, `addi s2, zero, -1` next; WB2's refused arm after its free, WB3's p != end arm after its free):
   the scratch freed (both events made: caw_prog at caw_evs), rc <> 0 *)
Definition cut_oA (C : cawB) (fy : YK11.FPState) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world SEGS)
  (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) (k : Z) : Prop :=
  caw_base C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k /\ c_rc C <> 0 /\
  ablocks B ly3 S3 = ablocks B (c_ly C) (c_S C) /\ caw_prog C (caw_evs C) S3 /\
  caw_ledger C ly3 S3 Hp3 W3 mem3 0.
Lemma cut_oA_R_wle : forall C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k,
  cut_oA C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k = cut_oAR (@wle SEGS) C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k.
Proof. reflexivity. Qed.
(* CAWB_OB (B' 0x82020, the out_of_memory () test; WB3's p == end arm through 0x82074, WB4a): s2 = want, and want
   agrees with rc as the two checks ask; the scratch freed, both events made *)
Definition caw_want (C : cawB) (want : Z) : Prop :=
  (want = -1 /\ c_rc C <> 0) \/ (want = 0 /\ c_rc C = 0).
(* cut_oB over a world relation R: caw_baseR R in place of caw_base *)
Definition cut_oBR (R : world SEGS -> world SEGS -> Prop) (C : cawB) (fy : YK11.FPState) (ly3 : alayout)
  (S3 : astate) (Hp3 : list Z) (W3 : world SEGS) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model)
  (k want : Z) : Prop :=
  caw_baseR R C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k /\ getr regs3 18 = w64 want /\ caw_want C want /\
  ablocks B ly3 S3 = ablocks B (c_ly C) (c_S C) /\ caw_prog C (caw_evs C) S3 /\
  caw_ledger C ly3 S3 Hp3 W3 mem3 0.
Definition cut_oB (C : cawB) (fy : YK11.FPState) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world SEGS)
  (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) (k want : Z) : Prop :=
  caw_base C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k /\ getr regs3 18 = w64 want /\ caw_want C want /\
  ablocks B ly3 S3 = ablocks B (c_ly C) (c_S C) /\ caw_prog C (caw_evs C) S3 /\
  caw_ledger C ly3 S3 Hp3 W3 mem3 0.
Lemma cut_oB_R_wle : forall C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want,
  cut_oB C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want = cut_oBR (@wle SEGS) C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want.
Proof. reflexivity. Qed.
(* cut_ck over a world relation R: caw_baseR R in place of caw_base *)
Definition cut_ckR (R : world SEGS -> world SEGS -> Prop) (C : cawB) (fy : YK11.FPState) (ly3 : alayout)
  (S3 : astate) (Hp3 : list Z) (W3 : world SEGS) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model)
  (k want : Z) : Prop :=
  caw_baseR R C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k /\ getr regs3 18 = w64 want /\ caw_want C want /\
  ablocks B ly3 S3 = ablocks B (c_ly C) (c_S C) /\ caw_prog C (caw_evs C) S3 /\
  caw_ledger C ly3 S3 Hp3 W3 mem3 0.
(* CAWB_CK (B' 0x82038, out_of_memory () was 0: the ledger's own byte is 0; WB4 -> WB5; both events made) *)
Definition cut_ck (C : cawB) (fy : YK11.FPState) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world SEGS)
  (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) (k want : Z) : Prop :=
  caw_base C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k /\ getr regs3 18 = w64 want /\ caw_want C want /\
  ablocks B ly3 S3 = ablocks B (c_ly C) (c_S C) /\ caw_prog C (caw_evs C) S3 /\
  caw_ledger C ly3 S3 Hp3 W3 mem3 0.
Lemma cut_ck_R_wle : forall C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want,
  cut_ck C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want = cut_ckR (@wle SEGS) C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want.
Proof. reflexivity. Qed.
(* CAWB_END (B' 0x82058, `mv a0, s1`; WB1's NULL arm, WB4's two out-of-memory arms, WB5): s1 = r, r = 1 exactly
   when own is 1, the byte the cut's ledger holds; the progress per arm, as the text's post: r = 1 (the scratch
   refused) made no event and is DEAD under the run hypothesis (caw_dead, the text's OUTCOME), r = 0 made both *)
Definition cut_end (C : cawB) (fy : YK11.FPState) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world SEGS)
  (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) (k own r : Z) : Prop :=
  caw_base C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k /\ getr regs3 9 = w64 r /\
  ((r = 1 /\ own = 1 /\ caw_prog C [] S3 /\ caw_dead C) \/ (r = 0 /\ own = 0 /\ caw_prog C (caw_evs C) S3)) /\
  ablocks B ly3 S3 = ablocks B (c_ly C) (c_S C) /\
  caw_ledger C ly3 S3 Hp3 W3 mem3 own.
(* cut_end over a world relation R: caw_baseR R in place of caw_base, every other conjunct as cut_end's *)
Definition cut_endR (R : world SEGS -> world SEGS -> Prop) (C : cawB) (fy : YK11.FPState) (ly3 : alayout)
  (S3 : astate) (Hp3 : list Z) (W3 : world SEGS) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model)
  (k own r : Z) : Prop :=
  caw_baseR R C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k /\ getr regs3 9 = w64 r /\
  ((r = 1 /\ own = 1 /\ caw_prog C [] S3 /\ caw_dead C) \/ (r = 0 /\ own = 0 /\ caw_prog C (caw_evs C) S3)) /\
  ablocks B ly3 S3 = ablocks B (c_ly C) (c_S C) /\
  caw_ledger C ly3 S3 Hp3 W3 mem3 own.
Lemma cut_end_R_wle : forall C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k own r,
  cut_end C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k own r = cut_endR (@wle SEGS) C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k own r.
Proof. reflexivity. Qed.

(* ---- the machine state at a cut ---- *)
Definition caw_cfg (fy : YK11.FPState) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) (off : Z)
  : config :=
  mkCfg (@YK11.mkst fy regs3 (Z_to_bv 64 (BASE + (AF_cawB + off))) mem3 (YK11.seg_rom SEGS)) md3.

(* ---- the continuations: from a cut, SRr to any Q with P kept (CawA102's form) ---- *)
(* the continuations over a world relation R: the cut's own R form where it has one (cut_oAR, cut_oBR, cut_ckR,
   cut_endR), and YA0nH.SRrG SEGS R in place of SRr SEGS *)
Definition caw_K_malR (R : world SEGS -> world SEGS -> Prop) (C : cawB) (P : (word -> option byte) -> Prop)
  (Q : world SEGS -> config -> Prop) : Prop :=
  forall ly3 S3 Hp3 W3 regs3 mem3 md3 k,
  cut_mal C ly3 S3 Hp3 W3 regs3 mem3 md3 k -> P mem3 ->
  YA0nH.SRrG SEGS R W3 (caw_cfg fx regs3 mem3 md3 CAWB_MAL) (fun W' c' => Q W' c' /\ P (ms_mem (cfg_ms c'))).
Definition caw_K_mal (C : cawB) (P : (word -> option byte) -> Prop) (Q : world SEGS -> config -> Prop) : Prop :=
  forall ly3 S3 Hp3 W3 regs3 mem3 md3 k,
  cut_mal C ly3 S3 Hp3 W3 regs3 mem3 md3 k -> P mem3 ->
  SRr SEGS W3 (caw_cfg fx regs3 mem3 md3 CAWB_MAL) (fun W' c' => Q W' c' /\ P (ms_mem (cfg_ms c'))).
Lemma caw_K_mal_R_wle : forall C P Q, caw_K_mal C P Q = caw_K_malR (@wle SEGS) C P Q.
Proof. reflexivity. Qed.
Definition caw_K_evR (R : world SEGS -> world SEGS -> Prop) (C : cawB) (P : (word -> option byte) -> Prop)
  (Q : world SEGS -> config -> Prop) : Prop :=
  forall fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr,
  cut_ev C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr -> P mem3 ->
  YA0nH.SRrG SEGS R W3 (caw_cfg fy regs3 mem3 md3 CAWB_EV) (fun W' c' => Q W' c' /\ P (ms_mem (cfg_ms c'))).
Definition caw_K_ev (C : cawB) (P : (word -> option byte) -> Prop) (Q : world SEGS -> config -> Prop) : Prop :=
  forall fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr,
  cut_ev C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr -> P mem3 ->
  SRr SEGS W3 (caw_cfg fy regs3 mem3 md3 CAWB_EV) (fun W' c' => Q W' c' /\ P (ms_mem (cfg_ms c'))).
Lemma caw_K_ev_R_wle : forall C P Q, caw_K_ev C P Q = caw_K_evR (@wle SEGS) C P Q.
Proof. reflexivity. Qed.
Definition caw_K_wsR (R : world SEGS -> world SEGS -> Prop) (C : cawB) (P : (word -> option byte) -> Prop)
  (Q : world SEGS -> config -> Prop) : Prop :=
  forall fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr dl' u rest,
  cut_ws C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr dl' u rest -> P mem3 ->
  YA0nH.SRrG SEGS R W3 (caw_cfg fy regs3 mem3 md3 CAWB_WS) (fun W' c' => Q W' c' /\ P (ms_mem (cfg_ms c'))).
Definition caw_K_ws (C : cawB) (P : (word -> option byte) -> Prop) (Q : world SEGS -> config -> Prop) : Prop :=
  forall fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr dl' u rest,
  cut_ws C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr dl' u rest -> P mem3 ->
  SRr SEGS W3 (caw_cfg fy regs3 mem3 md3 CAWB_WS) (fun W' c' => Q W' c' /\ P (ms_mem (cfg_ms c'))).
Lemma caw_K_ws_R_wle : forall C P Q, caw_K_ws C P Q = caw_K_wsR (@wle SEGS) C P Q.
Proof. reflexivity. Qed.
Definition caw_K_oAR (R : world SEGS -> world SEGS -> Prop) (C : cawB) (P : (word -> option byte) -> Prop)
  (Q : world SEGS -> config -> Prop) : Prop :=
  forall fy ly3 S3 Hp3 W3 regs3 mem3 md3 k,
  cut_oAR R C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k -> P mem3 ->
  YA0nH.SRrG SEGS R W3 (caw_cfg fy regs3 mem3 md3 CAWB_OA) (fun W' c' => Q W' c' /\ P (ms_mem (cfg_ms c'))).
Definition caw_K_oA (C : cawB) (P : (word -> option byte) -> Prop) (Q : world SEGS -> config -> Prop) : Prop :=
  forall fy ly3 S3 Hp3 W3 regs3 mem3 md3 k,
  cut_oA C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k -> P mem3 ->
  SRr SEGS W3 (caw_cfg fy regs3 mem3 md3 CAWB_OA) (fun W' c' => Q W' c' /\ P (ms_mem (cfg_ms c'))).
Lemma caw_K_oA_R_wle : forall C P Q, caw_K_oA C P Q = caw_K_oAR (@wle SEGS) C P Q.
Proof. reflexivity. Qed.
Definition caw_K_oBR (R : world SEGS -> world SEGS -> Prop) (C : cawB) (P : (word -> option byte) -> Prop)
  (Q : world SEGS -> config -> Prop) : Prop :=
  forall fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want,
  cut_oBR R C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want -> P mem3 ->
  YA0nH.SRrG SEGS R W3 (caw_cfg fy regs3 mem3 md3 CAWB_OB) (fun W' c' => Q W' c' /\ P (ms_mem (cfg_ms c'))).
Definition caw_K_oB (C : cawB) (P : (word -> option byte) -> Prop) (Q : world SEGS -> config -> Prop) : Prop :=
  forall fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want,
  cut_oB C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want -> P mem3 ->
  SRr SEGS W3 (caw_cfg fy regs3 mem3 md3 CAWB_OB) (fun W' c' => Q W' c' /\ P (ms_mem (cfg_ms c'))).
Lemma caw_K_oB_R_wle : forall C P Q, caw_K_oB C P Q = caw_K_oBR (@wle SEGS) C P Q.
Proof. reflexivity. Qed.
Definition caw_K_ckR (R : world SEGS -> world SEGS -> Prop) (C : cawB) (P : (word -> option byte) -> Prop)
  (Q : world SEGS -> config -> Prop) : Prop :=
  forall fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want,
  cut_ckR R C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want -> P mem3 ->
  YA0nH.SRrG SEGS R W3 (caw_cfg fy regs3 mem3 md3 CAWB_CK) (fun W' c' => Q W' c' /\ P (ms_mem (cfg_ms c'))).
Definition caw_K_ck (C : cawB) (P : (word -> option byte) -> Prop) (Q : world SEGS -> config -> Prop) : Prop :=
  forall fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want,
  cut_ck C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want -> P mem3 ->
  SRr SEGS W3 (caw_cfg fy regs3 mem3 md3 CAWB_CK) (fun W' c' => Q W' c' /\ P (ms_mem (cfg_ms c'))).
Lemma caw_K_ck_R_wle : forall C P Q, caw_K_ck C P Q = caw_K_ckR (@wle SEGS) C P Q.
Proof. reflexivity. Qed.
Definition caw_K_endR (R : world SEGS -> world SEGS -> Prop) (C : cawB) (P : (word -> option byte) -> Prop)
  (Q : world SEGS -> config -> Prop) : Prop :=
  forall fy ly3 S3 Hp3 W3 regs3 mem3 md3 k own r,
  cut_endR R C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k own r -> P mem3 ->
  YA0nH.SRrG SEGS R W3 (caw_cfg fy regs3 mem3 md3 CAWB_END) (fun W' c' => Q W' c' /\ P (ms_mem (cfg_ms c'))).
Definition caw_K_end (C : cawB) (P : (word -> option byte) -> Prop) (Q : world SEGS -> config -> Prop) : Prop :=
  forall fy ly3 S3 Hp3 W3 regs3 mem3 md3 k own r,
  cut_end C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k own r -> P mem3 ->
  SRr SEGS W3 (caw_cfg fy regs3 mem3 md3 CAWB_END) (fun W' c' => Q W' c' /\ P (ms_mem (cfg_ms c'))).
Lemma caw_K_end_R_wle : forall C P Q, caw_K_end C P Q = caw_K_endR (@wle SEGS) C P Q.
Proof. reflexivity. Qed.
(* caw_K_end_post over a world relation R: caw_K_endR R at the text's post caw_post, which is at wle' for every R
   (fpostF, PRH_Base.v) *)
Definition caw_K_end_postR (R : world SEGS -> world SEGS -> Prop) (C : cawB) (P : (word -> option byte) -> Prop)
  : Prop := caw_K_endR R C P (caw_post C).
(* the End segment's conclusion: the text's post (caw_post), P kept *)
Definition caw_K_end_post (C : cawB) (P : (word -> option byte) -> Prop) : Prop := caw_K_end C P (caw_post C).
Lemma caw_K_end_post_R_wle : forall C P, caw_K_end_post C P = caw_K_end_postR (@wle SEGS) C P.
Proof. reflexivity. Qed.

(* ---- facts every segment uses ---- *)
Lemma caw_req : forall z, 0 < z -> req_size z = z.
Proof. intros z Hz. unfold req_size. destruct (Z.eqb_spec z 0); lia. Qed.

Lemma caw_hblock : forall ly S Hp W mem Lam peak cnt fail ran most own a k,
  LEDGER ly S Hp W mem Lam peak cnt fail ran most own -> In (a, k) Lam -> prh_hblock B ly S Hp W mem a k.
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own a k HL Hin.
exact (proj1 (Forall_forall _ _) (prh_ledger_blocks B ly S Hp W mem Lam peak cnt fail ran most own HL) (a, k) Hin).
Qed.

(* the callee-saved registers are the entry's when sp, s0, s1, s2 are and the others never moved (H2CawR.v) *)
Ltac caw_inbv := repeat (first [left; apply bv_eq; reflexivity | right]).
Lemma caw_aregs : forall (regs regs' : bvmap 5 word),
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r) ->
  aregs_preserved regs regs'.
Proof.
intros regs regs' H r Hr. unfold acallee_saved in Hr.
assert (E : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
  r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
repeat (destruct E as [-> | E]; [apply H; caw_inbv |]). subst r. apply H; caw_inbv.
Qed.

(* the text's bytes and tree at any state the journal from entry reaches with the entry's blocks still live (H2CawBase
   caw_J_keep): the text lies in an entry block (or is empty), the tree's blocks are harness blocks of entry and its
   root lies in a fake frame of entry; FP is empty, so the journal keeps them *)
Lemma caw_J_keep : forall C ly3 S3 Hp3 W3 mem3 md3 k,
  caw_pre C -> caw_J C ly3 S3 Hp3 W3 mem3 md3 k ->
  (forall x, In x (ablocks B (c_ly C) (c_S C)) -> In x (ablocks B ly3 S3)) ->
  bytes_at W3 mem3 (c_data C) (c_x C) /\
  (c_rc C = 0 -> pj_nodeR SEGS (rdW W3 mem3) (prh_lin (c_Lam C)) (c_doc C) (c_t C) (c_D C)).
Proof.
intros C ly3 S3 Hp3 W3 mem3 md3 k Hpre HJ Hbl.
(* caw_pre and the journal read BY NAME *)
pose proof (caw_pre_fpre C Hpre) as [HPRE _]. pose proof (caw_pre_src C Hpre) as HSRC.
pose proof (caw_pre_inblk C Hpre) as HINB. pose proof (caw_pre_tree C Hpre) as HTREE.
pose proof (caw_pre_ledger C Hpre) as HL.
pose proof HPRE as (HAR & _).
unfold caw_J in HJ.
pose proof (ajx_ar HJ) as HAR3. pose proof (ajx_ly HJ) as Hly. pose proof (ajx_frs HJ) as Hfrs.
pose proof (ajx_hi HJ) as F1. pose proof (ajx_blk HJ) as F2. pose proof (ajx_img HJ) as F3. pose proof (ajx_frm HJ) as F4.
pose proof (AR_laws_x_xs SEGS B (AR_laws_ok_cf SEGS B)) as LAWS.
split.
- destruct HSRC as (HB & _). unfold bytes_at in *.
  destruct (Z.eq_dec (c_size C) 0) as [H0|H0].
  + unfold c_size in H0. destruct (c_x C) as [|c0 x0]; [intros j Hj; cbn in Hj; lia | cbn [length] in H0; lia].
  + destruct (HINB ltac:(unfold c_size in *; lia)) as (b & m & Hin & Hb & Hm & _).
    intros j Hj. destruct (HB j Hj) as [V R]. split; [|exact R].
    intros kk Hkk. assert (kk = 0%nat) by lia. subst kk. specialize (V 0%nat Hkk).
    cbn [Z.of_nat] in *. rewrite Z.add_0_r in *.
    rewrite (mbyte_of_aview SEGS (w_H (c_W C)) (w_H W3) (c_mem C) mem3); [exact V|].
    replace (c_data C + Z.of_nat j) with (b + (c_data C + Z.of_nat j - b)) by lia.
    apply (F2 b m); [exact Hin | exact (Hbl _ Hin) | | apply inFP_nil].
    unfold c_size in *. rewrite caw_req by lia. lia.
- intros Hrc. destruct (HTREE Hrc) as (HN & HDL & _ & (Hal & (cid & pos & Hfin & Hf1 & Hf2) & _)).
  apply (pj_nodeR_frame SEGS (c_t C) _ _ _ _ _ HN).
  intros x Hx. unfold pj_footR in Hx. destruct Hx as [Hx | ([a kk] & HinD & Hx)].
  + assert (Ea : aview SEGS (w_H W3) mem3 x = aview SEGS (w_H (c_W C)) (c_mem C) x).
    { apply (F4 cid pos x Hfin); [left; unfold frame_rng, in_zr; cbn [fst snd]; lia | apply inFP_nil]. }
    split; [exact (mbyte_of_aview SEGS _ _ _ _ x Ea)|].
    intros _. apply (apresent_writable SEGS).
    destruct (alx_layout SEGS B ARcfx LAWS _ _ _ _ _ _ ly3 HAR Hly) as (_ & Efr & _).
    assert (Hfin3 : In (cid, pos) (frames S3)) by (rewrite Hfrs; exact Hfin).
    destruct (alx_frames SEGS B ARcfx LAWS _ _ _ _ _ _ cid pos HAR3 Hfin3) as (_ & _ & Hpr & _).
    apply Hpr. rewrite Efr. lia.
  + destruct (caw_hblock _ _ _ _ _ _ _ _ _ _ _ _ a kk HL (HDL _ HinD)) as (Hk0 & Hab & _).
    unfold pj_holdsR in Hx; cbn [fst snd] in Hx.
    change (@cf_head CfParams_preset) with 16 in Hab.
    assert (Ea : aview SEGS (w_H W3) mem3 x = aview SEGS (w_H (c_W C)) (c_mem C) x).
    { replace x with (a - 16 + (x - (a - 16))) by lia.
      apply (F2 (a - 16) (kk + 16)); [exact Hab | exact (Hbl _ Hab) | rewrite caw_req by lia; lia | apply inFP_nil]. }
    split; [exact (mbyte_of_aview SEGS _ _ _ _ x Ea)|]. intros _.
    destruct (alx_blocks SEGS B ARcfx LAWS _ _ _ _ _ _ _ _ HAR3 (Hbl _ Hab)) as (_ & _ & _ & _ & Hpr & _).
    apply (apresent_writable SEGS). apply (proj1 (Hpr x ltac:(rewrite caw_req by lia; lia))).
Qed.
(* caw_J_keep over any world relation R (its journal conjuncts by name over R; none reads R): the text and the tree at
   a cut past the free, whose journal is at the re-hide relation *)
Lemma caw_J_keepR : forall (R : world SEGS -> world SEGS -> Prop) C ly3 S3 Hp3 W3 mem3 md3 k,
  caw_pre C -> caw_JR R C ly3 S3 Hp3 W3 mem3 md3 k ->
  (forall x, In x (ablocks B (c_ly C) (c_S C)) -> In x (ablocks B ly3 S3)) ->
  bytes_at W3 mem3 (c_data C) (c_x C) /\
  (c_rc C = 0 -> pj_nodeR SEGS (rdW W3 mem3) (prh_lin (c_Lam C)) (c_doc C) (c_t C) (c_D C)).
Proof.
intros R C ly3 S3 Hp3 W3 mem3 md3 k Hpre HJ Hbl.
(* caw_pre and the journal read BY NAME *)
pose proof (caw_pre_fpre C Hpre) as [HPRE _]. pose proof (caw_pre_src C Hpre) as HSRC.
pose proof (caw_pre_inblk C Hpre) as HINB. pose proof (caw_pre_tree C Hpre) as HTREE.
pose proof (caw_pre_ledger C Hpre) as HL.
pose proof HPRE as (HAR & _).
unfold caw_JR in HJ.
pose proof (ajxR_ar HJ) as HAR3. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_frs HJ) as Hfrs.
pose proof (ajxR_hi HJ) as F1. pose proof (ajxR_blk HJ) as F2. pose proof (ajxR_img HJ) as F3. pose proof (ajxR_frm HJ) as F4.
pose proof (AR_laws_x_xs SEGS B (AR_laws_ok_cf SEGS B)) as LAWS.
split.
- destruct HSRC as (HB & _). unfold bytes_at in *.
  destruct (Z.eq_dec (c_size C) 0) as [H0|H0].
  + unfold c_size in H0. destruct (c_x C) as [|c0 x0]; [intros j Hj; cbn in Hj; lia | cbn [length] in H0; lia].
  + destruct (HINB ltac:(unfold c_size in *; lia)) as (b & m & Hin & Hb & Hm & _).
    intros j Hj. destruct (HB j Hj) as [V Rj]. split; [|exact Rj].
    intros kk Hkk. assert (kk = 0%nat) by lia. subst kk. specialize (V 0%nat Hkk).
    cbn [Z.of_nat] in *. rewrite Z.add_0_r in *.
    rewrite (mbyte_of_aview SEGS (w_H (c_W C)) (w_H W3) (c_mem C) mem3); [exact V|].
    replace (c_data C + Z.of_nat j) with (b + (c_data C + Z.of_nat j - b)) by lia.
    apply (F2 b m); [exact Hin | exact (Hbl _ Hin) | | apply inFP_nil].
    unfold c_size in *. rewrite caw_req by lia. lia.
- intros Hrc. destruct (HTREE Hrc) as (HN & HDL & _ & (Hal & (cid & pos & Hfin & Hf1 & Hf2) & _)).
  apply (pj_nodeR_frame SEGS (c_t C) _ _ _ _ _ HN).
  intros x Hx. unfold pj_footR in Hx. destruct Hx as [Hx | ([a kk] & HinD & Hx)].
  + assert (Ea : aview SEGS (w_H W3) mem3 x = aview SEGS (w_H (c_W C)) (c_mem C) x).
    { apply (F4 cid pos x Hfin); [left; unfold frame_rng, in_zr; cbn [fst snd]; lia | apply inFP_nil]. }
    split; [exact (mbyte_of_aview SEGS _ _ _ _ x Ea)|].
    intros _. apply (apresent_writable SEGS).
    destruct (alx_layout SEGS B ARcfx LAWS _ _ _ _ _ _ ly3 HAR Hly) as (_ & Efr & _).
    assert (Hfin3 : In (cid, pos) (frames S3)) by (rewrite Hfrs; exact Hfin).
    destruct (alx_frames SEGS B ARcfx LAWS _ _ _ _ _ _ cid pos HAR3 Hfin3) as (_ & _ & Hpr & _).
    apply Hpr. rewrite Efr. lia.
  + destruct (caw_hblock _ _ _ _ _ _ _ _ _ _ _ _ a kk HL (HDL _ HinD)) as (Hk0 & Hab & _).
    unfold pj_holdsR in Hx; cbn [fst snd] in Hx.
    change (@cf_head CfParams_preset) with 16 in Hab.
    assert (Ea : aview SEGS (w_H W3) mem3 x = aview SEGS (w_H (c_W C)) (c_mem C) x).
    { replace x with (a - 16 + (x - (a - 16))) by lia.
      apply (F2 (a - 16) (kk + 16)); [exact Hab | exact (Hbl _ Hab) | rewrite caw_req by lia; lia | apply inFP_nil]. }
    split; [exact (mbyte_of_aview SEGS _ _ _ _ x Ea)|]. intros _.
    destruct (alx_blocks SEGS B ARcfx LAWS _ _ _ _ _ _ _ _ HAR3 (Hbl _ Hab)) as (_ & _ & _ & _ & Hpr & _).
    apply (apresent_writable SEGS). apply (proj1 (Hpr x ltac:(rewrite caw_req by lia; lia))).
Qed.

(* chain_pre with the empty chain: s0 holds rc (an int, sign-extended), never a frame pointer above sp (H2CawBase) *)
Lemma caw_chain : forall ly rd regs rc0, 4096 <= raZ regs -> getr regs 8 = w64 rc0 -> - 2 ^ 31 <= rc0 < 2 ^ 31 ->
  2 ^ 31 <= spZ regs -> ly_top ly <= 2 ^ 47 -> chain_pre ly rd regs [].
Proof.
intros ly rd regs rc0 Hra Hs0 Hrc Hsp Htop. split; [exact Hra|].
destruct (frame0_ok ly regs); [|reflexivity].
replace (bad_next (spZ regs) (ly_top ly) (s0Z regs)) with true; [reflexivity|]. symmetry.
unfold bad_next, s0Z. rewrite Hs0. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64).
destruct (Z_le_gt_dec 0 rc0) as [Hp|Hn].
- rewrite Z.mod_small by lia. apply orb_true_intro. left. apply orb_true_intro. left. apply Z.leb_le. lia.
- replace (rc0 mod 2 ^ 64) with (rc0 + 2 ^ 64) by (rewrite <- (Z.mod_small (rc0 + 2 ^ 64) (2 ^ 64)) by lia;
    rewrite Z.add_mod, Z.mod_same, Z.add_0_r, Z.mod_mod by lia; reflexivity).
  apply orb_true_intro. left. apply orb_true_intro. right. apply Z.leb_le. lia.
Qed.

(* the scratch is a new block, not one of entry's (H2CawBase caw_scr_new) *)
Lemma caw_scr_new : forall C ly3 S3 Hp3 W3 mem3 md3 scr, ARcfx ly3 S3 Hp3 W3 mem3 md3 -> caw_scr C ly3 S3 scr ->
  0 <= c_size C -> ~ In (scr, c_size C + 1) (ablocks B (c_ly C) (c_S C)).
Proof.
intros C ly3 S3 Hp3 W3 mem3 md3 scr HAR (Hs4 & E) Hn Hin.
pose proof (AR_laws_x_xs SEGS B (AR_laws_ok_cf SEGS B)) as LAWS.
assert (Hin' : In (scr, c_size C + 1) (ablocks B ly3 S3)) by (rewrite E; apply in_or_app; right; left; reflexivity).
destruct (alx_blocks SEGS B ARcfx LAWS _ _ _ _ _ _ _ _ HAR Hin') as (_ & _ & _ & _ & _ & Hpw).
rewrite E in Hpw. apply in_split in Hin as (l1 & l2 & El). rewrite El in Hpw.
pose proof (pairwise_In2 zdisjoint _ (scr, req_size (c_size C + 1)) (scr, req_size (c_size C + 1))
  (map (fun b : Z * Z => (fst b, req_size (snd b))) l1) (map (fun b : Z * Z => (fst b, req_size (snd b))) l2) [] Hpw
  ltac:(rewrite <- app_assoc, !map_app; reflexivity)) as D.
unfold zdisjoint in D. cbn [fst snd] in D. rewrite caw_req in D by lia. lia.
Qed.

(* the free of the scratch leaves exactly entry's blocks (H2CawBase caw_split_last) *)
Lemma caw_split_last : forall (l l1 l2 : list (Z * Z)) x, l ++ [x] = l1 ++ x :: l2 -> ~ In x l -> l1 = l /\ l2 = [].
Proof.
induction l as [|y l IH]; intros l1 l2 x E Hn.
- destruct l1 as [|z l1]; cbn in E.
  + inversion E. split; reflexivity.
  + inversion E as [[Ez E2]]. destruct l1; discriminate.
- destruct l1 as [|z l1]; cbn in E.
  + inversion E; subst. exfalso. apply Hn. left. reflexivity.
  + inversion E as [[Ey E2]]. subst z.
    destruct (IH l1 l2 x E2 (fun H => Hn (or_intror H))) as [-> ->]. split; reflexivity.
Qed.

(* ---- THE LIFTS to a world relation R that contains wle and is transitive: a wle base / End cut is one at R (the
   journal's world conjunct only, ajournal_xwR_mono), and a segment whose own cut is a wle form (WB0, WB1) runs, by its
   wle statement, to cuts at which its R continuations take over (the run's post records the cut reached) ---- *)
Section lift.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_wle : forall W W', wle W W' -> R W W'.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
(* an SRr run each of whose post states starts an SRrG run at R is an SRrG run at R *)
Lemma caw_SRr_SRrG_bind : forall W c (Q0 Q : world SEGS -> config -> Prop),
  SRr SEGS W c Q0 -> (forall W' c', Q0 W' c' -> YA0nH.SRrG SEGS R W' c' Q) -> YA0nH.SRrG SEGS R W c Q.
Proof.
intros W c Q0 Q H HK.
apply (YA0nH.SRrG_bind SEGS R R_trans W c Q0 Q (YA0nH.SRr_SRrG SEGS R R_wle W c Q0 H)).
intros W' c' _ HQ0. exact (HK W' c' HQ0).
Qed.
Lemma caw_base_R_lift : forall C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k,
  caw_base C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k -> caw_baseR R C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k.
Proof.
intros C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k (H1 & H2 & HJ & H4).
refine (conj H1 (conj H2 (conj _ H4))).
unfold caw_JR, ajournal_xR. unfold caw_J in HJ.
apply (ajournal_xwR_mono (SK := SK) SEGS B prh_pst _ (@wle SEGS) R R_wle). exact HJ.
Qed.
Lemma cut_end_R_lift : forall C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k own r,
  cut_end C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k own r -> cut_endR R C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k own r.
Proof.
intros C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k own r (HB & H).
exact (conj (caw_base_R_lift C fy ly3 S3 Hp3 W3 regs3 mem3 md3 k HB) H).
Qed.
(* WB0's form: a wle run that ends only at the malloc cut gives the same run with caw_K_malR at R *)
Lemma caw_K_mal_lift : forall C P (W : world SEGS) c,
  (forall Q, caw_K_mal C P Q -> SRr SEGS W c (fun W' c' => Q W' c' /\ P (ms_mem (cfg_ms c')))) ->
  forall Q, caw_K_malR R C P Q -> YA0nH.SRrG SEGS R W c (fun W' c' => Q W' c' /\ P (ms_mem (cfg_ms c'))).
Proof.
intros C P W c H Q KM.
apply (caw_SRr_SRrG_bind _ _ (fun W' c' => (exists ly3 S3 Hp3 regs3 mem3 md3 k,
  c' = caw_cfg fx regs3 mem3 md3 CAWB_MAL /\ cut_mal C ly3 S3 Hp3 W' regs3 mem3 md3 k) /\ P (ms_mem (cfg_ms c')))).
- apply H. intros ly3 S3 Hp3 W3 regs3 mem3 md3 k Hcut HPM.
  apply (SRr_ret SEGS). split; [|exact HPM].
  exists ly3, S3, Hp3, regs3, mem3, md3, k. split; [reflexivity | exact Hcut].
- intros W' c' ((ly3 & S3 & Hp3 & regs3 & mem3 & md3 & k & -> & Hcut) & HPM).
  exact (KM ly3 S3 Hp3 W' regs3 mem3 md3 k Hcut HPM).
Qed.
(* WB1's form: the malloc cut's wle continuation from the ev / End continuations gives the R one from their R forms
   (the End cut reached before any free lifts by cut_end_R_lift) *)
Lemma caw_K_mal_lift_ev_end : forall C P,
  (forall Q, caw_K_ev C P Q -> caw_K_end C P Q -> caw_K_mal C P Q) ->
  forall Q, caw_K_evR R C P Q -> caw_K_endR R C P Q -> caw_K_malR R C P Q.
Proof.
intros C P H Q KEV KEND ly3 S3 Hp3 W3 regs3 mem3 md3 k Hcut HPM.
apply (caw_SRr_SRrG_bind _ _ (fun W' c' =>
  ((exists fy ly4 S4 Hp4 regs4 mem4 md4 k4 scr,
      c' = caw_cfg fy regs4 mem4 md4 CAWB_EV /\ cut_ev C fy ly4 S4 Hp4 W' regs4 mem4 md4 k4 scr) \/
   (exists fy ly4 S4 Hp4 regs4 mem4 md4 k4 own r,
      c' = caw_cfg fy regs4 mem4 md4 CAWB_END /\ cut_end C fy ly4 S4 Hp4 W' regs4 mem4 md4 k4 own r)) /\
  P (ms_mem (cfg_ms c')))).
- refine (H _ _ _ ly3 S3 Hp3 W3 regs3 mem3 md3 k Hcut HPM).
  + intros fy ly4 S4 Hp4 W4 regs4 mem4 md4 k4 scr Hc HP4.
    apply (SRr_ret SEGS). split; [|exact HP4].
    left. exists fy, ly4, S4, Hp4, regs4, mem4, md4, k4, scr. split; [reflexivity | exact Hc].
  + intros fy ly4 S4 Hp4 W4 regs4 mem4 md4 k4 own r Hc HP4.
    apply (SRr_ret SEGS). split; [|exact HP4].
    right. exists fy, ly4, S4, Hp4, regs4, mem4, md4, k4, own, r. split; [reflexivity | exact Hc].
- intros W' c' [[(fy & ly4 & S4 & Hp4 & regs4 & mem4 & md4 & k4 & scr & -> & Hc)
                | (fy & ly4 & S4 & Hp4 & regs4 & mem4 & md4 & k4 & own & r & -> & Hc)] HP4].
  + exact (KEV fy ly4 S4 Hp4 W' regs4 mem4 md4 k4 scr Hc HP4).
  + exact (KEND fy ly4 S4 Hp4 W' regs4 mem4 md4 k4 own r
      (cut_end_R_lift C fy ly4 S4 Hp4 W' regs4 mem4 md4 k4 own r Hc) HP4).
Qed.
End lift.

End f.
End d.
