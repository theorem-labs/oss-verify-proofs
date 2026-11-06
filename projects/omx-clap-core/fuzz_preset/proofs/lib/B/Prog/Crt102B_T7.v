(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 996 of its 1069 lines of code are new or changed and 441 lines of the source are left out. *)
(* fuzz_preset, walk of check_round_trip on the #102 pins, IMAGE B' (asan-ubsan
   d663f82d7f488d30, unstripped twin c90d4fa54d43160b), FREE-PIECES-102 Part 7a row T7 = CRT-B-CEXIT (segment C
   +0x6f8 .. the exit `j` to X +0x80c, fuzzpreset.c new:756-768, round_trip_rewrite inlined):
   THE STRETCH C -> FF.

   rule 24: proves function check_round_trip (image B' of fuzz_preset; reuse search CONFIRMED by name:
   the R24 confirmation note R24-CONFIRM.md (sha256 b58eb5e2e5e3; internal record): released proofs plain/ubsan only, its address runs no evidence). This file proves its stretch C (+0x6f8) .. FF (+0x7f8).

   WHAT IS PROVED HERE (Qed): t7_stretch_C : T7_AT_FF -> T7_AT_C, the row's cut statements of Crt102B_T7_bd.v at
   this Section's variables: from every state crt_at_C_B describes at C, the run reaches a state the same predicate
   describes at FF (`ld a0, 0(s1)` before `jal fuzz_free`); the boundary's pure facts (the room position, kw, back's
   and copy's block sizes against tblk up to permutation, copy's depth) are carried through unchanged. The stretch is
   64 instructions, +0x6f8 .. +0x7f4 (crt.B.lst lines 447-510), with two calls of __wrap_strcmp and no store:
   - +0x6f8 .. +0x75c: back.keys[at] loaded through the key-slot alias, its shadow check +0x748 by the window t7_SH;
     the UBSan branches +0x72c ((at + 2^60) >> 61) and +0x730 (&keys[at] below keys) killed by arithmetic;
   - +0x75c jal __wrap_strcmp (back.keys[at], MOD_AT): the libc row STRCMP at s1 (t7_strcmp_call, aj_strcmp_at_xrom);
     it answers 0 since both strings are "modifiedAt" (cb7t_back_at's key; the read-only bytes crt_str_rom_B under
     HKMA), so +0x760 `bnez a0` -> abort is killed; the symbolic state resumed by st_ok_pi_after_call (every region
     lies at or above s1 or below the ceiling, off the callee's window [s1 - 2 * ESTACK, s1));
   - +0x764 .. +0x7f0: &kids[at] through the kid-slot alias (the run computes (at << 6) - (at << 3) + kids as
     at * 56 + kids), the UBSan branches +0x788 (&kids[at] below kids) and +0x7a4 (mulh overflow) killed by
     arithmetic, +0x784 / +0x7a8 / +0x7b0 decided by the engine, the shadow checks +0x7c0 / +0x7e0 and the type
     check +0x7cc (tag 4) by t7_SH and the kid's region;
   - +0x7f0 jal __wrap_strcmp (back.kids[at].str, STAMP): the same rule, answer 0 (both the stamp), +0x7f4 killed.
   At FF crt_at_C_B is rebuilt: the live state across the two callee windows (t7_live_keep; the ledger with g_most /
   g_own_ran_out kept by prh_ledger_kept_aview), the kept registers (callee-saved or not written), the spills above
   s1, the three trees below the ceiling (t7_agree_low), and back's free-order list by PRH_PjOrder.pj_foR_frame over
   the same footprint.
   Section hypotheses taken (texts of the internal file T7-CONTEXT.md): LAWS HPRE HTREE HKMA HKST BOK IMGVIS STRCMP.
   KB ROUND (Crt102Glue.v G3 / G4): C and FF are at kb = prh_wk F_check_round_trip (66), and the journal is at a budget
   WS with wbudget [] 66 WS. The runs keep WS (Crt102Kit.v crt_run_to_xw_inv), each strcmp keeps it (t7_strcmp_call:
   rebase / unbase around the empty-budget rule), and t7_live_keep takes the new journal at its WS with the budget, as
   the A' twin's cl_live_keep / cl_strcmp_call (Crt102Loops.v). t7_stretch_C's statement is unchanged.
   THE RE-HIDING MOVE: the journal (AJW) is at R := YA0nH.wle' SEGS
   YGcfRehidePost.RZ_cf and the step relation is YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf (Crt102Glue.v, the wle' contract);
   the branches are YSRrG.paj_branchR at R; strcmp goes through the engine's YGcallMxmn.aj_strcmp_at_xromR (the engine
   lemma is cited; no local copy t7_aj_strcmp_at_xromR is kept) lifted by YA0nH.SRr_SRr'.

   INPUTS OF RECORD: this tree's files below (the row's base was commit cbe6d10993c2, an ancestor of this tree; the
   contract texts at the kit tip 3ac20a5c9e30: Crt102Glue.v crt_at_C_B / crt_side / crt_live / crt_pos, PRH_Base.v
   prh_ledger .. ran most own, S1Ledger.v, PRH_PjOrder.v); lib/B/Prog/Crt102B_T7_bd.v (the row's cuts),
   Crt102B_T7_tree.v / Crt102B_T7_kit.v
   (this row). No row's file: t7_fdR_frame is Crt102Kit.v's crt102rw_fdR_frame statement over PRH_PjOrder.v, t7_sp
   restates Crt102KitB.v's cb4_sp, t7_keep is cb4_keep's body. PORTED with credit (statement and
   proof, A' -> B'): lib/A/Prog/Crt102Loops.v 70d17b8c1668 (cl_live_keep / cl_strcmp_call
   and their helpers); listing lib/B/Listing_prog.v 8bcc2c9e7809 (decoded by the row's crt prep,
   the row's PREP note, PREP.md (sha256 3e72b797012a; internal record)).

   NUMERALS. DERIVED: atom indices 64 .. 71 (S10Env's TE: 64 + the extras' positions) and their literal forms
   41 / 51 / 59 / 65 / 67 / 70 / 71 (= 32 + register 9 / 19 / 27, 64 + an extra's position, the engine's numbering);
   72 / 88 (the first atom above the C environment, and above the first call's 16 clobbered registers: the two
   calls' havoc windows), 4 (a0's position in CLOB); 27632 / 224 / 32 (STK_check_round_trip, the frame and the
   realignment, Crt102KitB.v cb4_sp); the spill
   offsets are the glue's CRT_SP_*_B; struct pj offsets the glue's PJ_OFF_* and CRT_OFF_*; 16 (the str field of a
   node). LENGTH: 8 / 24 / 56 / 72 / 512 (a word, the kid node's read window, a node and the kid stride, the spill
   window, the class-3 frame). BOUNDS: 2 ^ 46 / 2 ^ 47 / 2 ^ 54 / 4096, 2 ^ 60 / 61 and 56 / 63 (the UBSan checks'
   own constants, read off the listing at +0x71c / +0x728 and +0x78c / +0x798). No ADDRESS literal. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive YAkMemnorm YGcallMx YGcallMxmn YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos PresetReqAt PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue WriterApp PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env S1Ledger Crt102Glue Crt102Img Crt102Model.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB Crt102B_T7_kit Crt102B_T7_tree
  Crt102B_T7_bd.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Crt102ImgB.
(* the image-free kb runners and the journal's wild clause (Crt102Kit.v Section kbw), by qualified name *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Crt102Kit.
(* the re-hiding move's world relation and step relation (YA0nH.wle', YA0nH.SRr') at preset's
   zone RZ_cf, and the branch / bind over it (YSRrG), by qualified name *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost YSRrG.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the atoms this segment adds to S10Env's TE (0-31 entry regs, 32-63 current regs, 64- extras) ---- *)
Definition T7_SAVED : nat := 64.   (* 0(s1) *)
Definition T7_AT : nat := 65.      (* 0x40(s1), = cm_at ms *)
Definition T7_KEYS : nat := 66.    (* back.keys *)
Definition T7_KIDS : nat := 67.    (* back.kids *)
Definition T7_KX : nat := 68.      (* back.keys[at], the key string *)
Definition T7_SX : nat := 69.      (* back.kids[at].str, the stamp string *)
Definition T7_AKEY : nat := 70.    (* &back.keys[at] = keys + 8 at *)
Definition T7_AKID : nat := 71.    (* &back.kids[at] = kids + 56 at *)

Section t7. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
Context {RL : PrhRoomLive} {SK : YI16.sink_head}.
#[local] Notation PA := (PI_prog_B).
#[local] Notation PL := (PL_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (@prh_pst prh_img_B).
#[local] Notation STKC := (@STK_check_round_trip prh_img_B).

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
(* the journal at a wild-trace budget WS (YCbqG.v ajournal_xwR; kb round), at the re-hiding move's world relation *)
#[local] Notation RZW := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
#[local] Notation AJW := (ajournal_xwR (SK := SK) SEGS B PST ARx RZW).

Section g.
Variables (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
  (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk).
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z))
  (doc : Z) (t : PjTree.jv) (D : list (Z * Z)) (x : list Z)
  (Lam : list (Z * Z)) (peak cnt ran most : Z)
  (CTX0 : list (list Z)) (a_mod_at a_stamp : Z).
#[local] Notation sp0 := (spZ regs).
#[local] Notation sp1 := (@CRT_sp1 regs).
(* kb round: every state of this stretch (C, FF) is at kb = prh_wk F_check_round_trip (Crt102Glue.v G4); as the A'
   twin's livea (Crt102Loops.v), the notation carries the budget *)
#[local] Notation liveB := (@crt_live rc prh_img_B RL SK B_prog_listing PA B ARx
  ly S Hp W regs mem md doc t D Lam peak most (prh_wk F_check_round_trip)).
#[local] Notation atXB := (@crt_at_X_B fx rc prh_img_B RL SK B_prog_listing PA B ARx rp_sm rp_x rp_os rp_i rp_H0
  ly S Hp W regs mem md doc t D Lam peak cnt ran most).
#[local] Notation atCB := (@crt_at_C_B fx rc prh_img_B RL SK B_prog_listing PA B ARx rp_sm rp_x rp_os rp_i rp_H0
  ly S Hp W regs mem md doc t D Lam peak cnt most).
#[local] Notation QFb := (@QF fx rc prh_img_B RL SK B_prog_listing PA B ARx rp_sm rp_x rp_os rp_i rp_H0
  ly S Hp W regs mem md doc t D Lam peak cnt ran most).
#[local] Notation cfgB := (@crt_cfg rc B_prog_listing PA CRT_PC_B).
#[local] Notation bregsB := (@crt_bregs_B regs).
#[local] Notation spillB := (@crt_spill rc B_prog_listing PA regs).
#[local] Notation TEB := (TE (L := B_prog_listing) (PA := PA)).

(* NAMED SECTION HYPOTHESES, each with the context file's text (the internal file T7-CONTEXT.md) and its owner *)
(* LAWS: the allocator relation's laws; owner the engine, instance AR_laws_x_xs *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* HPRE / HTREE: tcheck_round_trip_specX's premises *)
Hypothesis HPRE : fpre B ARx STKC ly S Hp W regs mem md ch.
Hypothesis HTREE : ck_tree_ok ly S Lam W mem doc t D.
(* HKMA / HKST: tcheck_round_trip_specX's premises kept_img B a_mod_at .. / a_stamp .., at the instance's
   a_mod_at := CRT_MOD_AT_B, a_stamp := CRT_STAMP_B *)
Hypothesis HKMA : @kept_img _ B_prog_listing PA B (@CRT_MOD_AT_B _ PA) (Z.of_nat (length ck_MOD_AT) + 1).
Hypothesis HKST : @kept_img _ B_prog_listing PA B (@CRT_STAMP_B _ PA) (Z.of_nat (length ck_STAMP) + 1).
(* BOK: image B's start-up record YF0m ts_ok *)
Hypothesis BOK : asyms_ok B.
(* IMGVIS: the img_shadow_vis_cf form (lib/Reusable/YGcfAmx2.v:47) at ci := CfImgB.CfImg_B, i.e. over
   image B's band [cf_img_lo, cf_img_top), which is PI_prog_B's [pa_lo, pa_hi) (Crt102B_T7_tree.v cb7t_band_eq_B) *)
Hypothesis IMGVIS : forall ly S Hp (W : world SEGS) mem md a,
  ARx ly S Hp W mem md -> @cf_img_lo CfImgB.CfImg_B <= a < @cf_img_top CfImgB.CfImg_B ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
(* STRCMP: the libc row of __wrap_strcmp, the xrom form (its post keeps memnorm) *)
Hypothesis STRCMP : forall fxk : YK11.FPState,
  astrcmp_realizes_xrom (fx := fxk) SEGS B ARx RLO RHI (SIGMA AS___wrap_strcmp).

#[local] Notation AT_C := (@T7_AT_C fx rc RL SK B ARx rp_sm rp_x rp_os rp_i rp_H0
  ly S Hp W regs mem md doc t D Lam peak cnt ran most).
#[local] Notation AT_FF := (@T7_AT_FF fx rc RL SK B ARx rp_sm rp_x rp_os rp_i rp_H0
  ly S Hp W regs mem md doc t D Lam peak cnt ran most).

(* ---- the symbolic state at C (+0x6f8) ---- *)
Definition t7_Bx : sv := SOff (xr 27) 0.
Definition t7_SH : list shent := [mkSHE T7_AKEY 0 8; mkSHE T7_AKID 0 24].
Definition t7_rsp : YP09.region := YP09.mkRegion (Some (xr 9)) 0 72 0 0
  [YP09.mkChunk 0 (CVal 8 (SOff T7_SAVED 0));
   YP09.mkChunk CRT_SP_BACK (CVal 8 (SOff (xr 19) CRT_OFF_BACK));
   YP09.mkChunk CRT_SP_AT_B (CVal 8 (SOff T7_AT 0))].
Definition t7_rbk : YP09.region := YP09.mkRegion (Some (xr 19)) (CRT_OFF_BACK + PJ_OFF_KIDS) (CRT_OFF_BACK + PJ_OFF_KEYS + 8) 0 0
  [YP09.mkChunk (CRT_OFF_BACK + PJ_OFF_KIDS) (CVal 8 (SOff T7_KIDS 0));
   YP09.mkChunk (CRT_OFF_BACK + PJ_OFF_KEYS) (CVal 8 (SOff T7_KEYS 0))].
Definition t7_rkey : YP09.region := YP09.mkRegion (Some T7_AKEY) 0 8 0 0
  [YP09.mkChunk 0 (CVal 8 (SOff T7_KX 0))].
Definition t7_rkid : YP09.region := YP09.mkRegion (Some T7_AKID) 0 24 0 0
  [YP09.mkChunk 0 (CVal 4 (SLit 4)); YP09.mkChunk 16 (CVal 8 (SOff T7_SX 0))].
Definition t7_regions : smem := [t7_rsp; t7_rbk; t7_rkey; t7_rkid].
Definition t7_facts : facts :=
  mkFacts [(xr 9, mkAF (2 ^ 46) (2 ^ 47) 5); (xr 19, mkAF 4096 (2 ^ 47) 5);
           (xr 27, mkAF SHADOW_OFF SHADOW_OFF 0);
           (T7_AT, mkAF 0 (2 ^ 54) 0); (T7_KEYS, mkAF 4096 (2 ^ 47) 4); (T7_KIDS, mkAF 4096 (2 ^ 47) 4);
           (T7_AKEY, mkAF 4096 (2 ^ 47 - 4096) 3); (T7_AKID, mkAF 4096 (2 ^ 47 - 4096) 3);
           (T7_KX, mkAF 1 (2 ^ 47) 0); (T7_SX, mkAF 1 (2 ^ 47) 0); (T7_SAVED, mkAF 1 (2 ^ 47) 0)]
          []
          [(SAlu ALU_ADD (SAlu ALU_SLL (SOff T7_AT 0) (SLit 3)) (SOff T7_KEYS 0), SOff T7_AKEY 0);
           (SAlu ALU_ADD (SMd M_MUL (SOff T7_AT 0) (SLit 56)) (SOff T7_KIDS 0), SOff T7_AKID 0)].
Definition t7_ssC : sstate :=
  mkSS (CRT_PC_B + CRT_C_OFF_B) cur_atoms t7_regions None t7_facts.
#[local] Notation t7_E rg saved at_ keys kids kx sx akey akid :=
  (TEB regs rg (map (Z_to_bv 64) [saved; at_; keys; kids; kx; sx; akey; akid])).

(* ---- what the walk reads at C, as the reader layer gives it ---- *)
Definition t7_dat_bounds (F saved at_ keys kids kx sx : Z) : Prop :=
  4096 <= keys /\ keys mod 16 = 0 /\ 4096 <= kids /\ kids mod 16 = 0 /\
  0 <= at_ < 2 ^ 54 /\ 1 <= kx <= 2 ^ 47 /\ 1 <= sx <= 2 ^ 47 /\ 1 <= saved <= 2 ^ 47 /\
  4096 <= F /\ F mod 32 = 0 /\ 2 ^ 46 <= sp1 /\ sp1 + 72 <= 2 ^ 47 /\ sp1 mod 32 = 0 /\
  (* the three homes are apart, and all lie below the realigned sp: the caller gets this from the ledger and the
     frame laws (a fake frame and a live block are application memory below alloc_ceiling, and
     alloc_ceiling + STK_check_round_trip <= sp0) *)
  F + 512 <= sp1 /\ keys + 8 * at_ + 8 <= sp1 /\ kids + 56 * at_ + 56 <= sp1 /\
  keys + 8 * at_ + 4096 <= 2 ^ 47 /\ kids + 56 * at_ + 4096 <= 2 ^ 47 /\
  (F + 512 <= keys + 8 * at_ \/ keys + 8 * at_ + 8 <= F) /\
  (F + 512 <= kids + 56 * at_ \/ kids + 56 * at_ + 24 <= F) /\
  (keys + 8 * at_ + 8 <= kids + 56 * at_ \/ kids + 56 * at_ + 24 <= keys + 8 * at_).

Definition t7_dat (Wc : world SEGS) (memc : word -> option byte) (F saved at_ keys kids kx sx : Z) : Prop :=
  val_mem SEGS (mrestrict (w_H Wc) memc) (sp1 + CRT_SP_SAVED_B) 8 saved /\
  val_mem SEGS (mrestrict (w_H Wc) memc) (sp1 + CRT_SP_BACK) 8 (F + CRT_OFF_BACK) /\
  val_mem SEGS (mrestrict (w_H Wc) memc) (sp1 + CRT_SP_AT_B) 8 at_ /\
  val_mem SEGS (mrestrict (w_H Wc) memc) (F + CRT_OFF_BACK + PJ_OFF_KIDS) 8 kids /\
  val_mem SEGS (mrestrict (w_H Wc) memc) (F + CRT_OFF_BACK + PJ_OFF_KEYS) 8 keys /\
  val_mem SEGS (mrestrict (w_H Wc) memc) (keys + 8 * at_) 8 kx /\
  val_mem SEGS (mrestrict (w_H Wc) memc) (kids + 56 * at_) 4 4 /\
  val_mem SEGS (mrestrict (w_H Wc) memc) (kids + 56 * at_ + 16) 8 sx /\
  t7_dat_bounds F saved at_ keys kids kx sx.

(* ---- the symbolic state at C holds ---- *)
Lemma t7_more : forall rg (l : list Z) j, (64 + j < 240)%nat ->
  ew (TEB regs rg (map (Z_to_bv 64) l)) (64 + j) = Z_to_bv 64 (nth j l 0).
Proof.
intros rg l j Hj. rewrite (te_more_lt regs rg (map (Z_to_bv 64) l) j Hj).
exact (map_nth (Z_to_bv 64) l 0 j).
Qed.

Lemma t7_ew_reg : forall rg more (r : bv 5) k, Z.of_nat k = bv_unsigned r ->
  ew (TEB regs rg more) (xr k) = getr rg r.
Proof. intros rg more r k Hk. unfold xr. exact (te_cur regs rg more r k Hk). Qed.

Lemma t7_ew_ex : forall rg saved at_ keys kids kx sx akey akid,
  let E := t7_E rg saved at_ keys kids kx sx akey akid in
  ew E T7_SAVED = Z_to_bv 64 saved /\ ew E T7_AT = Z_to_bv 64 at_ /\ ew E T7_KEYS = Z_to_bv 64 keys /\
  ew E T7_KIDS = Z_to_bv 64 kids /\ ew E T7_KX = Z_to_bv 64 kx /\ ew E T7_SX = Z_to_bv 64 sx /\
  ew E T7_AKEY = Z_to_bv 64 akey /\ ew E T7_AKID = Z_to_bv 64 akid.
Proof.
intros rg saved at_ keys kids kx sx akey akid E. unfold E, t7_E.
change T7_SAVED with (64 + 0)%nat. change T7_AT with (64 + 1)%nat. change T7_KEYS with (64 + 2)%nat.
change T7_KIDS with (64 + 3)%nat. change T7_KX with (64 + 4)%nat. change T7_SX with (64 + 5)%nat.
change T7_AKEY with (64 + 6)%nat. change T7_AKID with (64 + 7)%nat.
repeat split; rewrite t7_more by lia; cbn [nth]; reflexivity.
Qed.


(* the atom values of the C environment, with the engine's own literal atom indices *)
Lemma t7_vals : forall (rg : bvmap 5 word) F saved at_ keys kids kx sx,
  bregsB rg F -> t7_dat_bounds F saved at_ keys kids kx sx ->
  let E := t7_E rg saved at_ keys kids kx sx (keys + 8 * at_) (kids + 56 * at_) in
  bv_unsigned (ew E 41) = sp1 /\ bv_unsigned (ew E 51) = F /\ bv_unsigned (ew E 59) = SHADOW_OFF /\
  bv_unsigned (ew E 64) = saved /\ bv_unsigned (ew E 65) = at_ /\ bv_unsigned (ew E 66) = keys /\
  bv_unsigned (ew E 67) = kids /\ bv_unsigned (ew E 68) = kx /\ bv_unsigned (ew E 69) = sx /\
  bv_unsigned (ew E 70) = keys + 8 * at_ /\ bv_unsigned (ew E 71) = kids + 56 * at_.
Proof.
intros rg F saved at_ keys kids kx sx HBR HB E.
pose proof (crt_bregs_B_sp HBR) as R2. pose proof (crt_bregs_B_gp HBR) as R3. pose proof (crt_bregs_B_tp HBR) as R4.
pose proof (crt_bregs_B_s0 HBR) as R8. pose proof (crt_bregs_B_s1 HBR) as R9. pose proof (crt_bregs_B_s2 HBR) as R18.
pose proof (crt_bregs_B_s4 HBR) as R20. pose proof (crt_bregs_B_s3 HBR) as R19. pose proof (crt_bregs_B_s7 HBR) as R23.
pose proof (crt_bregs_B_s9 HBR) as R25. pose proof (crt_bregs_B_s11 HBR) as R27.
destruct HB as (Hk0 & Hk16 & Hd0 & Hd16 & Hat & Hkx & Hsx & Hsvd & HF0 & HF32 & Hs46 & Hs47 & Hs32 &
  HFs & HKs & HDs & HK47 & HD47 & Hsep1 & Hsep2 & Hsep3).
destruct (t7_ew_ex rg saved at_ keys kids kx sx (keys + 8 * at_) (kids + 56 * at_))
  as (Esv & Eat & Ekeys & Ekids & Ekx & Esx & Eakey & Eakid).
cbv zeta in Esv, Eat, Ekeys, Ekids, Ekx, Esx, Eakey, Eakid.
cbv [T7_SAVED T7_AT T7_KEYS T7_KIDS T7_KX T7_SX T7_AKEY T7_AKID] in Esv, Eat, Ekeys, Ekids, Ekx, Esx, Eakey, Eakid.
unfold E.
split; [change 41%nat with (xr 9); rewrite (t7_ew_reg rg _ 9%bv 9 eq_refl), R9; apply unsigned_lit_small; lia|].
split; [change 51%nat with (xr 19); rewrite (t7_ew_reg rg _ 19%bv 19 eq_refl), R19; apply unsigned_lit_small; lia|].
split; [change 59%nat with (xr 27); rewrite (t7_ew_reg rg _ 27%bv 27 eq_refl), R27; apply unsigned_lit_small;
        unfold SHADOW_OFF; lia|].
split; [rewrite Esv; apply unsigned_lit_small; lia|].
split; [rewrite Eat; apply unsigned_lit_small; lia|].
split; [rewrite Ekeys; apply unsigned_lit_small; lia|].
split; [rewrite Ekids; apply unsigned_lit_small; lia|].
split; [rewrite Ekx; apply unsigned_lit_small; lia|].
split; [rewrite Esx; apply unsigned_lit_small; lia|].
split; [rewrite Eakey; apply unsigned_lit_small; lia | rewrite Eakid; apply unsigned_lit_small; lia].
Qed.

(* ---- the symbolic state at C (+0x6f8) holds of the machine state the boundary describes ---- *)
Lemma t7_entry : forall (fxk : YK11.FPState) (Wc : world SEGS) memc (rg : bvmap 5 word) F saved at_ keys kids kx sx,
  bregsB rg F -> t7_dat Wc memc F saved at_ keys kids kx sx ->
  st_ok_pi SEGS VAL (t7_E rg saved at_ keys kids kx sx (keys + 8 * at_) (kids + 56 * at_)) t7_ssC
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_B + CRT_C_OFF_B))) memc (YK11.seg_rom SEGS))).
Proof.
intros fxk Wc memc rg F saved at_ keys kids kx sx HBR HD.
pose proof (crt_bregs_B_sp HBR) as R2. pose proof (crt_bregs_B_gp HBR) as R3. pose proof (crt_bregs_B_tp HBR) as R4.
pose proof (crt_bregs_B_s0 HBR) as R8. pose proof (crt_bregs_B_s1 HBR) as R9. pose proof (crt_bregs_B_s2 HBR) as R18.
pose proof (crt_bregs_B_s4 HBR) as R20. pose proof (crt_bregs_B_s3 HBR) as R19. pose proof (crt_bregs_B_s7 HBR) as R23.
pose proof (crt_bregs_B_s9 HBR) as R25. pose proof (crt_bregs_B_s11 HBR) as R27.
destruct HD as (Dsv & Dbk & Dat & Dkids & Dkeys & Dkx & Dty & Dsx & HB).
pose proof HB as (Hk0 & Hk16 & Hd0 & Hd16 & Hat & Hkx & Hsx & Hsvd & HF0 & HF32 & Hs46 & Hs47 & Hs32 &
  HFs & HKs & HDs & HK47 & HD47 & Hsep1 & Hsep2 & Hsep3).
destruct (t7_ew_ex rg saved at_ keys kids kx sx (keys + 8 * at_) (kids + 56 * at_))
  as (Esv & Eat & Ekeys & Ekids & Ekx & Esx & Eakey & Eakid).
cbv zeta in Esv, Eat, Ekeys, Ekids, Ekx, Esx, Eakey, Eakid.
assert (E9 : bv_unsigned (ew (t7_E rg saved at_ keys kids kx sx (keys + 8 * at_) (kids + 56 * at_)) (xr 9)) = sp1).
{ rewrite (t7_ew_reg rg _ 9%bv 9 eq_refl), R9. apply unsigned_lit_small. lia. }
assert (E19 : bv_unsigned (ew (t7_E rg saved at_ keys kids kx sx (keys + 8 * at_) (kids + 56 * at_)) (xr 19)) = F).
{ rewrite (t7_ew_reg rg _ 19%bv 19 eq_refl), R19. apply unsigned_lit_small. lia. }
assert (E27 : bv_unsigned (ew (t7_E rg saved at_ keys kids kx sx (keys + 8 * at_) (kids + 56 * at_)) (xr 27)) = SHADOW_OFF).
{ rewrite (t7_ew_reg rg _ 27%bv 27 eq_refl), R27. apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
assert (Usv : bv_unsigned (ew (t7_E rg saved at_ keys kids kx sx (keys + 8 * at_) (kids + 56 * at_)) T7_SAVED) = saved) by (rewrite Esv; apply unsigned_lit_small; lia).
assert (Uat : bv_unsigned (ew (t7_E rg saved at_ keys kids kx sx (keys + 8 * at_) (kids + 56 * at_)) T7_AT) = at_) by (rewrite Eat; apply unsigned_lit_small; lia).
assert (Ukeys : bv_unsigned (ew (t7_E rg saved at_ keys kids kx sx (keys + 8 * at_) (kids + 56 * at_)) T7_KEYS) = keys) by (rewrite Ekeys; apply unsigned_lit_small; lia).
assert (Ukids : bv_unsigned (ew (t7_E rg saved at_ keys kids kx sx (keys + 8 * at_) (kids + 56 * at_)) T7_KIDS) = kids) by (rewrite Ekids; apply unsigned_lit_small; lia).
assert (Ukx : bv_unsigned (ew (t7_E rg saved at_ keys kids kx sx (keys + 8 * at_) (kids + 56 * at_)) T7_KX) = kx) by (rewrite Ekx; apply unsigned_lit_small; lia).
assert (Usx : bv_unsigned (ew (t7_E rg saved at_ keys kids kx sx (keys + 8 * at_) (kids + 56 * at_)) T7_SX) = sx) by (rewrite Esx; apply unsigned_lit_small; lia).
assert (Uakey : bv_unsigned (ew (t7_E rg saved at_ keys kids kx sx (keys + 8 * at_) (kids + 56 * at_)) T7_AKEY) = keys + 8 * at_)
  by (rewrite Eakey; apply unsigned_lit_small; lia).
assert (Uakid : bv_unsigned (ew (t7_E rg saved at_ keys kids kx sx (keys + 8 * at_) (kids + 56 * at_)) T7_AKID) = kids + 56 * at_)
  by (rewrite Eakid; apply unsigned_lit_small; lia).
apply ts_st_ok.
- apply te_regs_ok.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
  + apply (ts_rok (t7_E rg saved at_ keys kids kx sx (keys + 8 * at_) (kids + 56 * at_)) _ (xr 9) sp1); [exact E9 | lia | lia | intros o Ho; lia |].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    * apply (ts_chunk (t7_E rg saved at_ keys kids kx sx (keys + 8 * at_) (kids + 56 * at_)) _ sp1 0 8 (SOff T7_SAVED 0) saved);
        [cbn [sv_denot]; rewrite Usv, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      cbn [YP09.c_off]. change (N.to_nat 8) with 8%nat. exact Dsv.
    * apply (ts_chunk (t7_E rg saved at_ keys kids kx sx (keys + 8 * at_) (kids + 56 * at_)) _ sp1 CRT_SP_BACK 8 (SOff (xr 19) CRT_OFF_BACK) (F + CRT_OFF_BACK));
        [cbn [sv_denot]; rewrite E19; reflexivity | unfold CRT_OFF_BACK; cbn; lia | cbn; lia |].
      cbn [YP09.c_off]. change (N.to_nat 8) with 8%nat. exact Dbk.
    * apply (ts_chunk (t7_E rg saved at_ keys kids kx sx (keys + 8 * at_) (kids + 56 * at_)) _ sp1 CRT_SP_AT_B 8 (SOff T7_AT 0) at_);
        [cbn [sv_denot]; rewrite Uat, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      cbn [YP09.c_off]. change (N.to_nat 8) with 8%nat. exact Dat.
  + apply (ts_rok (t7_E rg saved at_ keys kids kx sx (keys + 8 * at_) (kids + 56 * at_)) _ (xr 19) F); [exact E19 | unfold CRT_OFF_BACK, PJ_OFF_KIDS; lia
      | unfold CRT_OFF_BACK, PJ_OFF_KEYS; lia | intros o Ho; lia |].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * apply (ts_chunk (t7_E rg saved at_ keys kids kx sx (keys + 8 * at_) (kids + 56 * at_)) _ F (CRT_OFF_BACK + PJ_OFF_KIDS) 8 (SOff T7_KIDS 0) kids);
        [cbn [sv_denot]; rewrite Ukids, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      cbn [YP09.c_off]. change (N.to_nat 8) with 8%nat. rewrite Z.add_assoc. exact Dkids.
    * apply (ts_chunk (t7_E rg saved at_ keys kids kx sx (keys + 8 * at_) (kids + 56 * at_)) _ F (CRT_OFF_BACK + PJ_OFF_KEYS) 8 (SOff T7_KEYS 0) keys);
        [cbn [sv_denot]; rewrite Ukeys, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      cbn [YP09.c_off]. change (N.to_nat 8) with 8%nat. rewrite Z.add_assoc. exact Dkeys.
  + apply (ts_rok (t7_E rg saved at_ keys kids kx sx (keys + 8 * at_) (kids + 56 * at_)) _ T7_AKEY (keys + 8 * at_)); [exact Uakey | lia | lia | intros o Ho; lia |].
    apply Forall_cons; [|apply Forall_nil].
    apply (ts_chunk (t7_E rg saved at_ keys kids kx sx (keys + 8 * at_) (kids + 56 * at_)) _ (keys + 8 * at_) 0 8 (SOff T7_KX 0) kx);
      [cbn [sv_denot]; rewrite Ukx, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
    cbn [YP09.c_off]. change (N.to_nat 8) with 8%nat. rewrite Z.add_0_r. exact Dkx.
  + apply (ts_rok (t7_E rg saved at_ keys kids kx sx (keys + 8 * at_) (kids + 56 * at_)) _ T7_AKID (kids + 56 * at_)); [exact Uakid | lia | lia | intros o Ho; lia |].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * apply (ts_chunk (t7_E rg saved at_ keys kids kx sx (keys + 8 * at_) (kids + 56 * at_)) _ (kids + 56 * at_) 0 4 (SLit 4) 4);
        [cbn [sv_denot]; reflexivity | cbn; lia | cbn; lia |].
      cbn [YP09.c_off]. change (N.to_nat 4) with 4%nat. rewrite Z.add_0_r. exact Dty.
    * apply (ts_chunk (t7_E rg saved at_ keys kids kx sx (keys + 8 * at_) (kids + 56 * at_)) _ (kids + 56 * at_) 16 8 (SOff T7_SX 0) sx);
        [cbn [sv_denot]; rewrite Usx, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      cbn [YP09.c_off]. change (N.to_nat 8) with 8%nat. exact Dsx.
- cbv [t7_regions]. cbn [pairwise_disjoint all_disjoint].
  cbv [extent_disjoint t7_rsp t7_rbk t7_rkey t7_rkid]. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite !ts_bv_some. rewrite E9, E19, Uakey, Uakid.
  unfold CRT_OFF_BACK, PJ_OFF_KIDS, PJ_OFF_KEYS.
  repeat split;
    first [ left; lia | right; lia
          | destruct Hsep1 as [Hs1|Hs1]; first [left; lia | right; lia]
          | destruct Hsep2 as [Hs2|Hs2]; first [left; lia | right; lia]
          | destruct Hsep3 as [Hs3|Hs3]; first [left; lia | right; lia] ].
- split; [|split; [exact I|]].
  2: { split; [|split; [|exact I]].
       - apply U_inj.
         rewrite !U_SAlu, !U_SLit, !U_SOff, !Z.add_0_r, Uat, Ukeys, Uakey.
         rewrite (YP0m.zcanon_small at_), (YP0m.zcanon_small keys), (YP0m.zcanon_small 3) by lia.
         cbn [zalu_raw]. change (Z.land 3 63) with 3. rewrite Z.shiftl_mul_pow2 by lia.
         rewrite (YP0m.zcanon_small (at_ * 2 ^ 3)) by lia.
         rewrite !YP0m.zcanon_small by lia. lia.
       - (* the kid slot: the run computes (at << 6) - (at << 3) + kids as at * 56 + kids *)
         apply U_inj.
         rewrite !U_SAlu, !U_SMd, !U_SLit, !U_SOff, !Z.add_0_r, Uat, Ukids, Uakid.
         rewrite (YP0m.zcanon_small at_), (YP0m.zcanon_small kids), (YP0m.zcanon_small 56) by lia.
         cbn [zmd_raw zalu_raw].
         rewrite (YP0m.zcanon_small (at_ * 56)) by lia.
         rewrite !YP0m.zcanon_small by lia. lia. }
  cbv [t7_facts]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E9, E19, E27, Uat, Ukeys, Ukids, Uakey, Uakid, Ukx, Usx, Usv.
  repeat split; try lia; try (unfold SHADOW_OFF; lia).
Qed.



(* a run over regions with empty write windows writes nothing: each region is read-only to it *)
Ltac t7_wr :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0' fp b0' bc ly' own') end;
  repeat first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|] ].


(* one run of the walk to the next stop (an undecided branch or a call), over RUNTO, with its two side goals *)
Ltac t7_step RUNTO HS HJ SHOK HPM :=
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM BAND_SPAN (CRT_PC_B + CRT_AB_OFF_B);
  lazymatch goal with
       | |- YA0nH.SRr' _ _ _ _ _ => idtac
       | |- awr_ok _ _ _ _ _ _ _ _ _ => t7_wr
       | |- ?g => fail 0 "t7_step: a side goal of the run is left:" g
       end.
(* ======================================================================================================== *)
(* SUPPORT OF THE STRETCH C -> FF. The live state across a change confined to a window of the real stack below s1,
   the strcmp call at s1, the read-back facts at C. PORTED (statement and proof, image A' -> B') from
   lib/A/Prog/Crt102Loops.v at 70d17b8c1668: cl_writable_mono / cl_agree / cl_ra_keep /
   cl_hull_keep :156-197, cl_own_cell / cl_most_cell / cl_ro_low :410-419, cl_doc_low / cl_blk_low :439-455,
   cl_live_keep :460-524, cl_strcmp_call :549-604. *)

(* a run whose regions all have empty write windows leaves the memory as it was *)
Lemma t7_nowr_eq : forall E rs (m m' : word -> option byte), frame_of E rs m m' ->
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> m' = m.
Proof.
intros E rs m m' HF Hrs. apply functional_extensionality. intros xw. apply HF.
intros (r & Hr & Ha). pose proof (proj1 (forallb_forall _ _) Hrs r Hr) as Hw. cbv beta in Hw.
apply Z.leb_le in Hw. lia.
Qed.

Lemma t7_ro_low : forall a, in_roP SEGS RLO RHI a -> 0 <= a < kLowMemEnd.
Proof.
intros a Hro. apply (@pa_segs_low _ _ PA).
destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.

(* the frame law of a freeable tree, from the contract kit's order list (PRH_PjOrder.v: pj_fdR_foR, pj_foR_lblk,
   pj_foR_frame, pj_foR_fdR); the statement of Crt102Kit.v's crt102rw_fdR_frame, written here over SEGS (this file
   Requires Crt102Kit.v only for its image-free kb runners, Section kbw) *)
Lemma t7_fdR_frame : forall d m m' lblk p Dl, pj_fdR SEGS m lblk d p Dl ->
  pj_agreeR SEGS m m' (pj_footR p Dl) -> pj_fdR SEGS m' lblk d p Dl.
Proof.
intros d m m' lblk p Dl H HA.
destruct (PRH_PjOrder.pj_fdR_foR SEGS m lblk d p Dl H) as (F & HF).
exact (proj1 (PRH_PjOrder.pj_foR_fdR SEGS m' lblk d p Dl F (PRH_PjOrder.pj_foR_frame SEGS d m m' lblk lblk p Dl F HF
  (PRH_PjOrder.pj_foR_lblk SEGS m lblk d p Dl F HF) HA))).
Qed.

(* the entry's stack facts (Crt102KitB.v cb4_sp's statement and proof, stated here so this file reads HPRE only) and
   the homes of the document and of a harness block *)
Lemma t7_sp : sp0 mod 16 = 0 /\ YM05.alloc_ceiling + 27632 <= sp0 /\ sp0 <= 2 ^ 47 /\
  sp0 - 255 <= sp1 <= sp0 - 224 /\ sp1 mod 32 = 0 /\ 0 <= sp1.
Proof.
pose proof HPRE as ((HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HSTKC : STKC = 27632) by (vm_compute; reflexivity). rewrite HSTKC in *.
pose proof (YM05.alloc_ceiling_val) as Hc.
unfold CRT_sp1, CRT_FRAME, CRT_ALIGN.
pose proof (Z.mul_div_le (sp0 - 224) 32 ltac:(lia)).
pose proof (Z.mod_pos_bound (sp0 - 224) 32 ltac:(lia)). pose proof (Z.div_mod (sp0 - 224) 32 ltac:(lia)).
split; [exact Hal16|]. split; [lia|]. split; [lia|].
split; [lia|]. split; [apply Z.mod_mul; lia|]. apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia.
Qed.
Lemma t7_doc_low : 4096 <= doc /\ doc + 56 <= YM05.alloc_ceiling.
Proof.
destruct HTREE as (_ & _ & _ & (_ & (cid & pos' & Hin & Hlo & Hhi) & _)).
destruct HPRE as ((HAR & _) & _).
destruct (frames_bounds_x _ _ _ LAWS ly S Hp W mem md cid pos' HAR Hin) as (F1 & F2 & _). lia.
Qed.
Lemma t7_blk_low : forall lyc Sc Hpc (Wc : world SEGS) memc mdc Lamc peakc cntc failc ranc mostc ownc a k,
  ARx lyc Sc Hpc Wc memc mdc -> prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc -> In (a, k) Lamc ->
  0 <= k /\ 4096 + cf_head <= a /\ a + k <= YM05.alloc_ceiling.
Proof.
intros lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc mostc ownc a k HAR HL Hin.
destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL Hin) as (Hk & Hb & _).
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HAR Hb) as (_ & B1 & B2 & _).
change (@cf_head CfParams_preset) with 16 in *.
assert (k + 16 <= req_size (k + 16)) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia). lia.
Qed.

(* ---- memory agreement: a view that agrees on a byte set and keeps every present byte present keeps a tree, a word,
   a shadow fact ---- *)
Lemma t7_writable_mono : forall (H : word -> bool) m m' a,
  (forall z, apresent H m z -> apresent H m' z) ->
  writable_at SEGS (mrestrict H m) a -> writable_at SEGS (mrestrict H m') a.
Proof.
intros H m m' a Hpm Hw. unfold writable_at, wview, mrestrict in *.
destruct (H (Z_to_bv 64 a)) eqn:EH; [exact Hw|].
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
- assert (Hpa : apresent H m a).
  { split; [exact EH|]. exists b. exact Em. }
  destruct (Hpm a Hpa) as [_ [b' Hb']]. rewrite Hb'. discriminate.
- destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
Lemma t7_agree : forall (H : word -> bool) m m' (X : Z -> Prop),
  (forall z, X z -> aview SEGS H m' z = aview SEGS H m z) ->
  (forall z, apresent H m z -> apresent H m' z) ->
  pj_agreeR SEGS (mrestrict H m) (mrestrict H m') X.
Proof.
intros H m m' X Hv Hpm z Hz. split.
- exact (mbyte_of_aview SEGS H H m m' z (Hv z Hz)).
- apply t7_writable_mono. exact Hpm.
Qed.
Lemma t7_ra_keep : forall (rd rd' : reader) p n,
  (forall z, SHADOW_OFF <= z < kHighMemBeg -> rd' z = rd z) -> 0 <= p -> p + n <= 2 ^ 47 ->
  range_addressable rd SHADOW_OFF p n -> range_addressable rd' SHADOW_OFF p n.
Proof.
intros rd rd' p n Hk H0 H1 Hr z Hz. destruct (Hr z Hz) as (s & Hs & Hok). exists s. split; [|exact Hok].
rewrite Hk; [exact Hs|]. unfold shadow_of_addr, SHADOW_OFF, kHighMemBeg in *.
assert (0 <= z / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia). lia.
Qed.
Lemma t7_hull_keep : forall (rd rd' : reader) p n,
  (forall z, SHADOW_OFF <= z < kHighMemBeg -> rd' z = rd z) -> 0 <= p -> p + n <= 2 ^ 47 -> 0 < n ->
  shadow_hull_vis rd p n -> shadow_hull_vis rd' p n.
Proof.
intros rd rd' p n Hk H0 H1 H2 Hh z Hz. rewrite Hk; [exact (Hh z Hz)|].
unfold shadow_addr, SHADOW_OFF, kHighMemBeg in *.
assert (0 <= p / 8) by (apply Z.div_pos; lia).
assert ((p + n - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
assert (Hlo : 0x7fff8000 / 8 <= (0x7fff8000 + p / 8) / 8) by (apply Z.div_le_mono; lia).
assert ((0x7fff8000 + (p + n - 1) / 8) / 8 * 8 <= 0x7fff8000 + (p + n - 1) / 8).
{ pose proof (Z.mul_div_le (0x7fff8000 + (p + n - 1) / 8) 8 ltac:(lia)). lia. }
change (0x7fff8000 / 8) with 268431360 in Hlo. lia.
Qed.

(* ---- THE LIVE STATE ACROSS A CHANGE CONFINED TO A WINDOW OF THE REAL STACK below s1 + 0x70 (a runtime row's
   2 * ESTACK window below s1): everything crt_live reads lies below the ceiling (the statics, the blocks, the fake
   frames and their shadow), in the thirteen saved words [sp0 - 104, sp0), or at s1 + 0x70 ---- *)
Lemma t7_live_keep : forall lyc Sc Hpc Wc memc memc' mdc mdc' kj kj' pos Dx Lamc peakc cntc ownc ranc lo hi
    {WS : list (list Z)},
  liveB lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc memc' mdc' kj' WS ->
  YCbqGwild.wbudget [] (prh_wk F_check_round_trip) WS ->
  YM05.alloc_ceiling <= lo -> hi <= sp1 + CRT_SP_F ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a) ->
  (forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS memc') ->
  liveB lyc Sc Hpc Wc memc' mdc' kj' pos Dx Lamc peakc cntc ownc ranc.
Proof.
intros lyc Sc Hpc Wc memc memc' mdc mdc' kj kj' pos Dx Lamc peakc cntc ownc ranc lo hi WS HL HJ' HB_HJ' Hlo Hhi Hav Hpr
  Hmn.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof t7_sp as (H16 & Hsp0 & H47 & Hs1 & Hs32 & Hs0). unfold CRT_SP_F in Hhi.
assert (Hlow : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. apply Hav; lia. }
assert (Hhigh : forall a, sp1 + 112 <= a < 2 ^ 64 -> aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. apply Hav; lia. }
assert (Hsh : forall z, SHADOW_OFF <= z < kHighMemBeg -> aview SEGS (w_H Wc) memc' z = aview SEGS (w_H Wc) memc z).
{ intros z Hz. apply Hlow. unfold SHADOW_OFF in Hz. lia. }
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPl.
pose proof (crt_live_blocks_perm HL) as HPb. pose proof (crt_live_dx_apart HL) as HDx.
pose proof (crt_live_saved HL) as HSV. pose proof (crt_live_frame HL) as HFR. pose proof (crt_live_fspill HL) as HSF.
pose proof (crt_live_copy_open HL) as HRC. pose proof (crt_live_copy_hull HL) as HHC.
pose proof (crt_side_ledger HSD) as HLD. pose proof (crt_side_peak HSD) as Hpk. pose proof (crt_side_room HSD) as HRL.
pose proof (crt_side_arodata HSD) as HRO. pose proof (crt_side_doc HSD) as HDOC.
pose proof (crt_side_doc_blocks HSD) as HDL.
pose proof HJ as (HARc & _).
refine {| crt_live_journal := ex_intro _ WS (conj HJ' HB_HJ'); crt_live_side := _; crt_live_lam_perm := HPl;
  crt_live_blocks_perm := HPb;
  crt_live_dx_apart := HDx; crt_live_saved := _; crt_live_frame := _; crt_live_fspill := _; crt_live_copy_open := _;
  crt_live_copy_hull := _; crt_live_memnorm := Hmn |}.
- refine {| crt_side_ledger := _; crt_side_peak := Hpk; crt_side_room := HRL; crt_side_arodata := _;
    crt_side_doc := _; crt_side_doc_blocks := HDL |}.
  + (* the ledger, g_most and g_own_ran_out included: the statics (prh_pst) and the blocks' heads lie below the
       ceiling *)
    apply (prh_ledger_kept_aview B lyc Sc Hpc Wc memc); [exact HLD | | | auto | apply Permutation_refl].
    * intros a Ha. apply Hlow. pose proof (pst_in_img_B a Ha) as Hi. pose proof (@pa_segs_low _ _ PA a Hi). lia.
    * intros a k i Hin Hi. destruct (t7_blk_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLD Hin) as (Hk & Ha & Hb).
      apply Hlow. change (@cf_head CfParams_preset) with 16 in *. lia.
  + intros a Hro Ho He. rewrite Hlow; [exact (HRO a Hro Ho He)|].
    pose proof (t7_ro_low a Hro). lia.
  + apply (pj_nodeR_frame SEGS t _ _ (prh_lin Lamc) doc D HDOC). apply t7_agree; [|exact Hpr].
    intros z [Hz | (b & Hb & Hz)]; apply Hlow.
    * pose proof t7_doc_low. lia.
    * destruct b as [a k]. unfold pj_holdsR in Hz. cbn [fst snd] in Hz.
      destruct (t7_blk_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARc HLD (HDL _ Hb)) as (_ & Ha & Hk).
      change (@cf_head CfParams_preset) with 16 in *. lia.
- intros j Hj. apply (ts_vm_av (w_H Wc) (w_H Wc) memc memc'); [|exact (HSV j Hj)].
  intros i Hi. apply Hhigh. lia.
- pose proof (crt_frame_listed HFR) as Hin. pose proof (crt_frame_flag_word HFR) as Hrd.
  pose proof (crt_frame_present HFR) as Hfp.
  refine {| crt_frame_listed := Hin; crt_frame_flag_word := _; crt_frame_present := _ |}.
  + destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hin) as (F1 & F2 & _).
    rewrite <- Hrd. apply ts_rdword_keep. intros j Hj. apply Hlow. change (fs_frame_bytes CRT_CID) with 512 in *. lia.
  + intros a Ha. apply Hpr. exact (Hfp a Ha).
- apply (ts_vm_av (w_H Wc) (w_H Wc) memc memc'); [|exact HSF].
  intros i Hi. apply Hhigh. unfold CRT_SP_F. lia.
- destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc (crt_frame_listed HFR))
    as (F1 & F2 & _).
  change (fs_frame_bytes CRT_CID) with 512 in F2.
  apply (t7_ra_keep (aview SEGS (w_H Wc) memc)); [exact Hsh | unfold CRT_OFF_COPY; lia | unfold CRT_OFF_COPY; lia | exact HRC].
- destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc (crt_frame_listed HFR))
    as (F1 & F2 & _).
  change (fs_frame_bytes CRT_CID) with 512 in F2.
  apply (t7_hull_keep (aview SEGS (w_H Wc) memc)); [exact Hsh | unfold CRT_OFF_COPY; lia | unfold CRT_OFF_COPY; lia | lia
    | exact HHC].
Qed.

(* a tree in harness blocks whose node lies below the ceiling keeps its bytes across such a change *)
Lemma t7_agree_low : forall lyc Sc Hpc (Wc : world SEGS) memc mdc Lamc peakc cntc failc ranc mostc ownc m m' p D',
  ARx lyc Sc Hpc Wc memc mdc -> prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc ->
  (forall bk, In bk D' -> In bk Lamc) -> 0 <= p -> p + 56 <= YM05.alloc_ceiling ->
  (forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H Wc) m' a = aview SEGS (w_H Wc) m a) ->
  (forall a, apresent (w_H Wc) m a -> apresent (w_H Wc) m' a) ->
  pj_agreeR SEGS (mrestrict (w_H Wc) m) (mrestrict (w_H Wc) m') (pj_footR p D').
Proof.
intros lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc mostc ownc m m' p D' HAR HLD HD Hp0 Hp1 Hlow Hpr.
apply t7_agree; [|exact Hpr].
intros z [Hz | ((a & k) & Hb & Hz)]; apply Hlow.
- lia.
- unfold pj_holdsR in Hz. cbn [fst snd] in Hz.
  destruct (t7_blk_low _ _ _ _ _ _ _ _ _ _ _ _ _ a k HAR HLD (HD _ Hb)) as (Hk & Ha & Hk2).
  change (@cf_head CfParams_preset) with 16 in Ha. lia.
Qed.

(* ---- two live harness blocks are apart, and apart from a live fake frame ---- *)
Lemma t7_blk_sep : forall lyc Sc Hpc (Wc : world SEGS) memc mdc Lamc peakc cntc failc ranc mostc ownc a k b l,
  ARx lyc Sc Hpc Wc memc mdc -> prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc ->
  In (a, k) Lamc -> In (b, l) Lamc -> k <> l -> a + k <= b \/ b + l <= a.
Proof.
intros lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc mostc ownc a k b l HAR HLD Ha Hb Hne.
pose proof HLD as (_ & Hnd & _).
assert (Hab : a <> b).
{ intros Eab. subst b. exact (Hne (prh_fst_unique Lamc a k l Hnd Ha Hb)). }
destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLD Ha) as (Hk0 & HinA & _).
destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLD Hb) as (Hl0 & HinB & _).
assert (Hch16 : @cf_head CfParams_preset = 16) by reflexivity. rewrite Hch16 in HinA, HinB.
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR HinA) as (_ & _ & _ & _ & _ & Hpw).
assert (Hz : zdisjoint (a - 16, req_size (k + 16)) (b - 16, req_size (l + 16))).
{ apply (pairwise_zdisjoint_split _ _ _ Hpw). apply in_split_2.
  - exact (in_map (fun bb => (fst bb, req_size (snd bb))) _ _ HinA).
  - exact (in_map (fun bb => (fst bb, req_size (snd bb))) _ _ HinB).
  - intros E. injection E as E1 _. lia. }
unfold zdisjoint in Hz. cbn [fst snd] in Hz.
assert (Hrk : req_size (k + 16) = k + 16) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia).
assert (Hrl : req_size (l + 16) = l + 16) by (unfold req_size; destruct (Z.eqb_spec (l + 16) 0); lia).
rewrite Hrk, Hrl in Hz. lia.
Qed.
Lemma t7_blk_frame : forall lyc Sc Hpc (Wc : world SEGS) memc mdc Lamc peakc cntc failc ranc mostc ownc a k cid pos,
  ARx lyc Sc Hpc Wc memc mdc -> prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc ->
  In (a, k) Lamc -> In (cid, pos) (frames Sc) ->
  a + k <= frame_addr lyc cid pos \/ frame_addr lyc cid pos + fs_frame_bytes cid <= a - 16.
Proof.
intros lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc mostc ownc a k cid pos HAR HLD Ha Hin.
destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLD Ha) as (Hk0 & HinA & _).
assert (Hch16 : @cf_head CfParams_preset = 16) by reflexivity. rewrite Hch16 in HinA.
pose proof (sep_block_frame_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR HinA Hin) as Hz.
unfold zdisjoint in Hz. cbn [fst snd] in Hz.
assert (Hr : req_size (k + 16) = k + 16) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia).
rewrite Hr in Hz. lia.
Qed.

(* ---- t7_dat at the C state, from crt_at_C_B: the spills, back's header words and its member at cm_at ms
   (Crt102B_T7_tree.v cb7t_back_at), the bounds from the ledger's blocks and the frame ---- *)
Lemma t7_dat_of_C : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg mms cset saved kw,
  atCB fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg mms cset saved kw ->
  exists keys kids cap kx kk sx sk,
    t7_dat Wc memc (frame_addr lyc CRT_CID pos) saved (Z.of_nat (cm_at mms)) keys kids kx sx /\
    Z.of_nat (cm_at mms) < cap /\ In (keys, 8 * cap) Lamc /\ In (kids, 56 * cap) Lamc /\
    In (kx, kk) Lamc /\ pj_cstrR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) kx kk ck_MOD_AT /\
    In (sx, sk) Lamc /\ pj_cstrR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) sx sk ck_STAMP /\
    frame_addr lyc CRT_CID pos + 512 <= YM05.alloc_ceiling /\
    keys + 8 * cap <= YM05.alloc_ceiling /\ kids + 56 * cap <= YM05.alloc_ceiling.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg mms cset saved kw HC.
pose proof (crt_at_C_B_obj HC) as Et. pose proof (crt_at_C_B_live HC) as HL. pose proof (crt_at_C_B_bregs HC) as HBR.
pose proof (crt_at_C_B_sp_saved HC) as HSPS. pose proof (crt_at_C_B_sp_back HC) as HSPB.
pose proof (crt_at_C_B_sp_at HC) as HSPA. pose proof (crt_at_C_B_saved_nz HC) as Hsv0.
pose proof (crt_at_C_B_back HC) as HNB.
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_live_lam_perm HL) as HPl.
pose proof (crt_side_ledger (crt_live_side HL)) as HLED.
pose proof HJ as (HARc & _).
pose proof (crt_frame_listed (crt_live_frame HL)) as Hfin.
assert (HDL : forall bk, In bk Dback -> In bk Lamc).
{ intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPl)). apply in_or_app. left. apply in_or_app. left.
  exact Hbk. }
assert (HSL : In (saved, kw) Lamc).
{ apply (Permutation_in _ (Permutation_sym HPl)). apply in_or_app. left. apply in_or_app. right. left. reflexivity. }
unfold crt_tc in HNB.
destruct (cb7t_back_at SEGS t mms Et _ _ _ _ HNB)
  as (num & kids & keys & n & cap & kx & kk & sx & sk & Dkid & num2 & Hh & Hc0 & Hatn & Hnc & Hlk & Hly & HinK & HinY
      & Hx & Hcx & Hinx & Hnk & Hinc & Hh2 & Hcs & Hins).
exists keys, kids, cap, kx, kk, sx, sk.
unfold prh_lin in Hlk, Hly.
destruct (cb7t_blk_bounds B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ lyc Sc Hpc Wc memc mdc keys (8 * cap) HLED HARc eq_refl
  eq_refl Hly) as (Yk0 & Y16 & Y4 & Yc & _).
destruct (cb7t_blk_bounds B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ lyc Sc Hpc Wc memc mdc kids (56 * cap) HLED HARc eq_refl
  eq_refl Hlk) as (Kk0 & K16 & K4 & Kc & _).
destruct (cb7t_blk_bounds B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ lyc Sc Hpc Wc memc mdc kx kk HLED HARc eq_refl eq_refl
  (HDL _ Hinx)) as (Xk0 & _ & X4 & Xc & _).
destruct (cb7t_blk_bounds B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ lyc Sc Hpc Wc memc mdc sx sk HLED HARc eq_refl eq_refl
  (HDL _ Hins)) as (Zk0 & _ & Z4 & Zc & _).
destruct (cb7t_blk_bounds B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ lyc Sc Hpc Wc memc mdc saved kw HLED HARc eq_refl eq_refl
  HSL) as (Vk0 & _ & V4 & Vc & _).
destruct (frames_bounds_x _ _ _ LAWS _ _ _ _ _ _ _ _ HARc Hfin) as (F1 & F2 & _).
destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ _ _ HARc Hfin) as (F32 & _).
assert (Hfb : fs_frame_bytes CRT_CID = 512) by (vm_compute; reflexivity).
rewrite Hfb in F2.
pose proof (t7_blk_frame _ _ _ _ _ _ _ _ _ _ _ _ _ keys (8 * cap) CRT_CID pos HARc HLED Hly Hfin) as SKF.
pose proof (t7_blk_frame _ _ _ _ _ _ _ _ _ _ _ _ _ kids (56 * cap) CRT_CID pos HARc HLED Hlk Hfin) as SDF.
rewrite Hfb in SKF, SDF.
pose proof (t7_blk_sep _ _ _ _ _ _ _ _ _ _ _ _ _ keys (8 * cap) kids (56 * cap) HARc HLED Hly Hlk ltac:(lia)) as SKK.
pose proof t7_sp as (Hs16 & Hsc & Hs47 & Hs1 & Hs32 & Hs0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof YM05.alloc_ceiling_lt as Hc47.
destruct Hh as (_ & _ & _ & _ & (_ & Hkids) & (_ & Hkeys) & _).
destruct Hx as (_ & Hkx).
destruct Hh2 as (_ & (_ & Hty) & _ & (_ & Hsxv) & _).
set (F := frame_addr lyc CRT_CID pos) in *. set (at_ := Z.of_nat (cm_at mms)) in *.
assert (Hat0 : 0 <= at_) by (unfold at_; lia).
split.
{ split; [exact HSPS|]. split; [exact HSPB|]. split; [exact HSPA|].
  split; [exact Hkids|]. split; [exact Hkeys|]. split; [exact Hkx|]. split; [exact Hty|]. split; [exact Hsxv|].
  unfold t7_dat_bounds.
  repeat split;
    first [ lia
          | destruct SKF as [Hq|Hq]; first [left; lia | right; lia]
          | destruct SDF as [Hq|Hq]; first [left; lia | right; lia]
          | destruct SKK as [Hq|Hq]; first [left; lia | right; lia] ]. }
split; [lia|]. split; [exact Hly|]. split; [exact Hlk|]. split; [exact (HDL _ Hinx)|]. split; [exact Hcx|].
split; [exact (HDL _ Hins)|]. split; [exact Hcs|]. split; [lia|]. split; lia.
Qed.

(* ---- the shadow windows t7_SH: the key slot and the kid's first 24 bytes, apart from the shadow ---- *)
Lemma t7_shok : forall E (m : word -> option byte) akey akid,
  bv_unsigned (ew E 59) = SHADOW_OFF -> bv_unsigned (ew E 70) = akey -> bv_unsigned (ew E 71) = akid ->
  range_addressable (fun y => option_map (fun b : byte => bv_unsigned b) (mbyte SEGS m y)) SHADOW_OFF akey 8 ->
  range_addressable (fun y => option_map (fun b : byte => bv_unsigned b) (mbyte SEGS m y)) SHADOW_OFF akid 24 ->
  in_app akey 8 -> in_app akid 24 ->
  sh_ok SEGS t7_Bx t7_SH E m.
Proof.
intros E m akey akid E59 E70 E71 R1 R2 A1 A2.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof YM05.alloc_ceiling_lt as Hc47.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in A1, A2.
assert (UB : U E t7_Bx = SHADOW_OFF).
{ change t7_Bx with (SOff 59 0). rewrite U_SOff, E59, Z.add_0_r. apply YP0m.zcanon_small. unfold SHADOW_OFF. lia. }
assert (U70 : U E (SOff 70 0) = akey) by (rewrite U_SOff, E70, Z.add_0_r; apply YP0m.zcanon_small; lia).
assert (U71 : U E (SOff 71 0) = akid) by (rewrite U_SOff, E71, Z.add_0_r; apply YP0m.zcanon_small; lia).
unfold sh_ok, t7_SH, T7_AKEY, T7_AKID.
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold shent_ok, app_apart; cbn [she_m she_lo she_hi];
  rewrite ?UB, ?U70, ?U71.
- split; [rewrite Z.add_0_r; exact R1|]. intros a Ha. unfold SHADOW_OFF. lia.
- split; [rewrite Z.add_0_r; exact R2|]. intros a Ha. unfold SHADOW_OFF. lia.
Qed.

(* ---- A strcmp FROM check_round_trip AT THE REALIGNED sp (the port of Crt102Loops.v cl_strcmp_call): YGcallMxmn.v's
   aj_strcmp_at_xrom over the libc row STRCMP. The continuation receives the callee's journal (the same allocator
   state), the kept registers, the result and its meaning, and the memory kept outside strcmp's 2 * ESTACK window
   below s1. The argument premises are the strcmp rule's, in the form Crt102B_T7_tree.v's cb7t_str_prem /
   cb7t_rom_prem_* deliver them. ---- *)
Definition t7_sarg (Wc : world SEGS) (rgT : bvmap 5 word) (m : word -> option byte) (x len : Z) : Prop :=
  0 < x /\ 0 <= len /\ len + 1 < 2 ^ 32 /\ x + len + 1 <= 2 ^ 63 /\
  first_byte SEGS Wc m x (len + 1) 0 len /\
  src_ok SEGS Wc rgT m x (len + 1) /\
  (forall a, x <= a <= x + len -> a < YM05.alloc_ceiling) /\
  YGcallMx.amem_range8 x (len + 1) /\
  range_addressable (aview SEGS (w_H Wc) m) SHADOW_OFF x (len + 1) /\
  shadow_hull_vis (aview SEGS (w_H Wc) m) x (len + 1) /\
  (forall a, x + len < a < x + len - (x + len) mod 8 + 8 -> aview SEGS (w_H Wc) m a <> None).

Lemma t7_strcmp_call : forall (fxk : YK11.FPState) Wc E ss ms mdc lyc Sc Hpc kj pos (off px py kx ky : Z) Q
    {WS : list (list Z)},
  @st_ok SEGS fxk E ss (restrict (w_H Wc) ms) -> ss_resv ss = None -> ss_pc ss = SIGMA AS___wrap_strcmp ->
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc (ms_mem ms) mdc kj WS ->
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H Wc) (ms_mem ms)) ->
  getr (ms_regs ms) 2 = w64 sp1 -> getr (ms_regs ms) 3 = getr regs 3 -> getr (ms_regs ms) 4 = getr regs 4 ->
  getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CRT_PC_B + off)) -> 0 <= off < 4096 -> off mod 2 = 0 ->
  getr (ms_regs ms) 10 = w64 px -> getr (ms_regs ms) 11 = w64 py ->
  t7_sarg Wc (ms_regs ms) (ms_mem ms) px kx -> t7_sarg Wc (ms_regs ms) (ms_mem ms) py ky ->
  (forall regs2 mem2 md2 (v : word),
     AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc mem2 md2 kj WS ->
     aregs_preserved (ms_regs ms) regs2 -> getr regs2 10 = v ->
     (v = w64 0 <-> kx = ky /\ forall i, 0 <= i < kx ->
        aview SEGS (w_H Wc) (ms_mem ms) (px + i) = aview SEGS (w_H Wc) (ms_mem ms) (py + i)) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 2 * ESTACK <= a < sp1) ->
        aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) (ms_mem ms) a) ->
     (forall a, apresent (w_H Wc) (ms_mem ms) a -> apresent (w_H Wc) mem2 a) ->
     (YAkMemnorm.memnorm SEGS (ms_mem ms) -> YAkMemnorm.memnorm SEGS mem2) ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc
       (mkCfg (@YK11.mkst fxk regs2 (Z_to_bv 64 (BASE + (CRT_PC_B + off))) mem2 (YK11.seg_rom SEGS)) md2) Q) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (mkCfg ms mdc) Q.
Proof.
intros fxk Wc E ss ms mdc lyc Sc Hpc kj pos off px py kx ky Q WS HS Hrv Hpcs HJ HRO R2 R3 R4 Hra Hoff Hoff2 X10 X11
  SX SY HK.
pose proof HPRE as ((HAR & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & HRO0 & Hhi & Hrac).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof YM05.alloc_ceiling_lt as Hc47.
pose proof t7_sp as (Hs16 & Hsc & Hs47 & Hs1 & Hs32 & Hs0).
assert (HSTKC : STKC = 27632) by (vm_compute; reflexivity).
destruct (cb7k_ret off Hoff Hoff2) as (Hr1 & Hr2 & Hr3).
set (o := sp1 - sp0).
assert (Hsp1 : spZ (ms_regs ms) = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hspz : spZ (ms_regs ms) = sp0 + o) by (unfold o; lia).
assert (Hes : ESTACK = 4096) by reflexivity.
destruct SX as (X0 & Xk0 & Xk32 & Xhi & Xfb & Xsrc & Xce & Xam & Xra & Xhv & Xtl).
destruct SY as (Y0 & Yk0 & Yk32 & Yhi & Yfb & Ysrc & Yce & Yam & Yra & Yhv & Ytl).
rewrite (st_ok_restrict_mkst SEGS _ _ _ _ HS Hrv). cbn [ss_pc setpc]. rewrite Hpcs.
(* kb round: strcmp's rule (YGcallMxmn.aj_strcmp_at_xromR at R := RZW) is at the empty budget: the journal rebased to the
   current depot (YCbqGwild.ajournal_xw_rebaseR) and stepped back to its budget WS after it
   (YCbqGwild.ajournal_xw_unbase0R), as the A' twin Crt102Loops.v cl_strcmp_call; the rule's plain SRr lifted to SRr'
   (YA0nH.SRr_SRr') *)
pose proof (Crt102Kit.crt_jw_wild B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as Hinc.
pose proof HJ as HJr. apply YCbqGwild.ajournal_xw_rebaseR in HJr.
eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ apply (YA0nH.SRr_SRr' SEGS YGcfRehidePost.RZ_cf).
  refine (YGcallMxmn.aj_strcmp_at_xromR (SK := SK) SEGS B PST ARx RLO RHI LAWS (@pa_segs_low rc B_prog_listing PA)
    RZW (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf)
    (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf) (SIGMA AS___wrap_strcmp) (STRCMP fxk) Wc (ms_regs ms) (ms_mem ms) STKC sp0 [] ly
    (set_depot (st_depot Sc) S) Hp W mem md [(CRT_CID, pos)]
    lyc Sc Hpc mdc kj px py kx ky o (getr (ms_regs ms) 1) HJr X10 X11 X0 Y0 Xk0 Xk32 Xhi Yk0 Yk32 Yhi
    Hspz _ _ _ _ _ eq_refl _ Xfb Yfb Xsrc Ysrc _ _ Xam Yam Xra Xhv Yra Yhv Xtl Ytl HRO).
  all: try (unfold o in *; lia).
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - rewrite Hra. apply (ret_ok_codeptr_v (PI := PA)); [exact Hr3 | exact Hr2].
  - intros a Ha. pose proof (Xce a Ha). unfold o. lia.
  - intros a Ha. pose proof (Yce a Ha). unfold o. lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP & Hv & Hcmp & Hfr & Hpr2 & Hmn).
eapply YCbqGwild.ajournal_xw_unbase0R in HJ2; [|exact Hinc].
replace (sp0 + o) with sp1 in Hfr by (unfold o; lia).
rewrite Hra. exact (HK regs2 mem2 md2 v HJ2 HP Hv Hcmp Hfr Hpr2 Hmn).
Qed.

(* ---- the two strings strcmp compares are the same string: the key's bytes (pj_cstrR) and the read-only string's
   (kept_img + arodata_okP + the image bytes) ---- *)
Lemma t7_rom_bytes : forall (Wc : world SEGS) memX y (s : list Z),
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H Wc) memX) ->
  @kept_img _ B_prog_listing PA B y (Z.of_nat (length s) + 1) ->
  (forall j, (j < length (s ++ [0%Z]))%nat ->
     option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom SEGS (Z_to_bv 64 (y + Z.of_nat j))) =
     Some (nth j (s ++ [0]) 0)) ->
  forall j, (j < length s)%nat -> aview SEGS (w_H Wc) memX (y + Z.of_nat j) = Some (nth j s 0).
Proof.
intros Wc memX y s HRO (Hlo & Hhi & HK) HROM j Hj.
destruct (HK (y + Z.of_nat j) ltac:(lia)) as (Hr & Ho & He & _).
rewrite (HRO _ Hr Ho He). rewrite (HROM j ltac:(rewrite length_app; cbn [length]; lia)).
rewrite app_nth1 by lia. reflexivity.
Qed.
Lemma t7_cmp0 : forall (Wc : world SEGS) memX lblk x k y (s : list Z) (v : word),
  pj_cstrR SEGS (mrestrict (w_H Wc) memX) lblk x k s ->
  (forall j, (j < length s)%nat -> aview SEGS (w_H Wc) memX (y + Z.of_nat j) = Some (nth j s 0)) ->
  (v = w64 0 <-> Z.of_nat (length s) = Z.of_nat (length s) /\ forall i, 0 <= i < Z.of_nat (length s) ->
     aview SEGS (w_H Wc) memX (x + i) = aview SEGS (w_H Wc) memX (y + i)) ->
  v = w64 0.
Proof.
intros Wc memX lblk px k y s v (_ & _ & _ & _ & Hg) Hy Hv. apply Hv. split; [reflexivity|].
intros i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia.
rewrite (cb7t_garr8_at SEGS (w_H Wc) memX px (s ++ [0]) (Z.to_nat i) Hg ltac:(rewrite length_app; cbn [length]; lia)).
rewrite (Hy (Z.to_nat i) ltac:(lia)). rewrite app_nth1 by lia. reflexivity.
Qed.

(* ---- the UBSan overflow test at +0x7a4: `mulh (at, 56) xor ((at * 56) >>a 63)` is 0 when at < 2 ^ 54 ---- *)
Lemma t7_mulh0 : forall E n a, bv_unsigned (ew E n) = a -> 0 <= a < 2 ^ 54 ->
  U E (SAlu ALU_SLTU (SLit 0) (SAlu ALU_XOR (SMd M_MULH (SOff n 0) (SLit 56))
    (SAlu ALU_SRA (SMd M_MUL (SOff n 0) (SLit 56)) (SLit 63)))) = 0.
Proof.
intros E n a Ha Hr.
assert (Ua : U E (SOff n 0) = a) by (rewrite U_SOff, Ha, Z.add_0_r; apply YP0m.zcanon_small; lia).
rewrite !U_SAlu, !U_SMd, !U_SLit, Ua.
rewrite (YP0m.zcanon_small 0), (YP0m.zcanon_small 56), (YP0m.zcanon_small 63) by lia.
cbn [zmd_raw zalu_raw].
rewrite (swrap64_id a), (swrap64_id 56) by (unfold half64; lia).
rewrite (YP0m.zcanon_small (a * 56)) by lia.
rewrite (swrap64_id (a * 56)) by (unfold half64; lia).
change (Z.land 63 63) with 63. change (Z.of_N 64) with 64.
rewrite !Z.shiftr_div_pow2 by lia.
rewrite (Z.div_small (a * 56) (2 ^ 64)) by lia. rewrite (Z.div_small (a * 56) (2 ^ 63)) by lia.
reflexivity.
Qed.

(* after a run whose regions have empty write windows: EM : the new memory is the reference memory; the run's
   frame facts are cleared and the new machine state takes the name `ms` *)
Ltac t7_mem EM :=
  repeat match goal with
  | H : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ => clear H
  | H : mem_grows _ _ |- _ => clear H
  end;
  let Ex := fresh "Ex" in
  lazymatch goal with
  | HF : frame_of _ ?rs (ms_mem ?mo) (ms_mem ?m1) |- _ =>
      pose proof (t7_nowr_eq _ rs (ms_mem mo) (ms_mem m1) HF ltac:(vm_compute; reflexivity)) as Ex; clear HF;
      rewrite EM in Ex; clear EM; rename Ex into EM; try clear mo; try rename m1 into ms
  | HF : frame_of _ ?rs ?m0 (ms_mem ?m1) |- _ =>
      pose proof (t7_nowr_eq _ rs m0 (ms_mem m1) HF ltac:(vm_compute; reflexivity)) as Ex; clear HF;
      rename Ex into EM; try rename m1 into ms
  end.

(* a register no run wrote and the calls kept (an atom below every havoc's window) keeps its C value
   (Crt102B_T4.v b8695a391ce4 cb4_keep / Crt102Arms.v arms_keep, the same body) *)
Ltac t7_keep HS := lazymatch goal with |- getr _ ?rr = _ =>
  let H := fresh in prreg HS rr H; rewrite H; repeat rewrite ew_ewset_other by lia; te_close end.

(* a register's symbolic value at a run's end (YC1fP.v prreg without its normalisation, which leaves an atom above a
   havoc's window as `nth .. (map ..) ..`) *)
Ltac t7_reg HS r H :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?Hh ?m) => pose proof (st_ok_pi_restrict_reg Hh E ss m r HS) as H
  | st_ok ?segs ?E ?ss (restrict ?Hh ?m) => pose proof (st_ok_restrict_reg segs Hh E ss m r HS) as H
  end;
  lazymatch type of H with _ = sv_denot _ (sr_get (ss_regs ?ss) _) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in H end.

(* an image atom's value (the read-only strings' addresses the run leaves in a1) *)
Lemma t7_img_den : forall E n z v, img_env VAL A_LIM E -> (A_TEXT <= n < A_LIM)%nat -> VAL n + z = v ->
  sv_denot E (SOff n z) = Z_to_bv 64 v.
Proof. intros E n z v HE Hn Hv. cbn [sv_denot]. rewrite (HE n Hn), Hv. reflexivity. Qed.

(* the last run of the stretch, to the cut FF *)
Ltac t7_step_to RUNTO HS HJ SHOK HPM stop :=
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM BAND_SPAN stop;
  lazymatch goal with
       | |- YA0nH.SRr' _ _ _ _ _ => idtac
       | |- awr_ok _ _ _ _ _ _ _ _ _ => t7_wr
       | |- ?g => fail 0 "t7_step_to: a side goal of the run is left:" g
       end.

(* ======================================================================================================== *)
(* THE STRETCH C (+0x6f8) -> FF (+0x7f8): 64 instructions, two __wrap_strcmp calls, no store. *)
Lemma t7_stretch_C : AT_FF -> AT_C.
Proof.
intros HFF. unfold T7_AT_FF in HFF. unfold T7_AT_C.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg mms cset saved kw HC.
destruct (t7_dat_of_C fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg mms cset saved kw HC)
  as (keys & kids & cap & kx & kk & sx & sk & HD & Hcap & HinY & HinK & Hinx & Hcx & Hins & Hcs & HFc & HYc & HKc).
pose proof (crt_at_C_B_obj HC) as Et. pose proof (crt_at_C_B_frm_zero HC) as HFZ.
pose proof (crt_at_C_B_fregs HC) as HFK. pose proof (crt_at_C_B_live HC) as HL. pose proof (crt_at_C_B_bregs HC) as HBR.
pose proof (crt_at_C_B_sp_saved HC) as HSPS. pose proof (crt_at_C_B_sp_back HC) as HSPB.
pose proof (crt_at_C_B_sp_at HC) as HSPA. pose proof (crt_at_C_B_back_open HC) as HRAB.
pose proof (crt_at_C_B_v_open HC) as HRAV. pose proof (crt_at_C_B_cset_range HC) as Hcs0.
pose proof (crt_at_C_B_cset_mod HC) as Hcs1. pose proof (crt_at_C_B_cnt HC) as Hcnt.
pose proof (crt_at_C_B_saved_nz HC) as Hsv0. pose proof (crt_at_C_B_copy HC) as HNC.
pose proof (crt_at_C_B_copy_fd HC) as HFD. pose proof (crt_at_C_B_back HC) as HNB. pose proof (crt_at_C_B_pos HC) as HPOS.
pose proof (crt_at_C_B_kw HC) as HKW. pose proof (crt_at_C_B_back_tblk HC) as HPMB.
pose proof (crt_at_C_B_back_fo HC) as HFOB. pose proof (crt_at_C_B_copy_tblk HC) as HPMC.
pose proof (crt_at_C_B_copy_fo HC) as HFOC. pose proof (crt_at_C_B_copy_depth HC) as HDEP.
set (F := frame_addr lyc CRT_CID pos) in *.
set (at_ := Z.of_nat (cm_at mms)) in *.
pose proof HD as (_ & _ & _ & _ & _ & _ & _ & _ & HB).
destruct (t7_vals rg F saved at_ keys kids kx sx HBR HB)
  as (E9 & E19 & E27 & Usv & Uat & Ukeys & Ukids & Ukx & Usx & Uakey & Uakid).
cbv zeta in E9, E19, E27, Usv, Uat, Ukeys, Ukids, Ukx, Usx, Uakey, Uakid.
pose proof HB as (Hk0 & Hk16 & Hd0 & Hd16 & Hat & Hkx & Hsx & Hsvd & HF0 & HF32 & Hs46 & Hs47 & Hs32 &
  HFs & HKs & HDs & HK47 & HD47 & Hsep1 & Hsep2 & Hsep3).
pose proof (crt_bregs_B_sp HBR) as B2. pose proof (crt_bregs_B_gp HBR) as B3. pose proof (crt_bregs_B_tp HBR) as B4.
pose proof (crt_bregs_B_s0 HBR) as B8. pose proof (crt_bregs_B_s1 HBR) as B9. pose proof (crt_bregs_B_s2 HBR) as B18.
pose proof (crt_bregs_B_s4 HBR) as B20. pose proof (crt_bregs_B_s3 HBR) as B19. pose proof (crt_bregs_B_s7 HBR) as B23.
pose proof (crt_bregs_B_s9 HBR) as B25. pose proof (crt_bregs_B_s11 HBR) as B27.
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPl.
pose proof (crt_live_blocks_perm HL) as HPb. pose proof (crt_live_dx_apart HL) as HDx.
pose proof (crt_live_saved HL) as HSV. pose proof (crt_live_frame HL) as HFRM. pose proof (crt_live_fspill HL) as HSPF.
pose proof (crt_live_copy_open HL) as HCR. pose proof (crt_live_copy_hull HL) as HCH.
pose proof (crt_live_memnorm HL) as HMNl.
pose proof (crt_side_ledger HSD) as HLED. pose proof (crt_side_peak HSD) as Hpk. pose proof (crt_side_room HSD) as HRL.
pose proof (crt_side_arodata HSD) as HRO. pose proof (crt_side_doc HSD) as HDOC.
pose proof (crt_side_doc_blocks HSD) as HDL.
pose proof HJ as (HARc & _).
assert (HDbk : forall bk, In bk Dback -> In bk Lamc).
{ intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPl)). apply in_or_app. left. apply in_or_app. left.
  exact Hbk. }
assert (HDcp : forall bk, In bk Dc -> In bk Lamc).
{ intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPl)). apply in_or_app. left. apply in_or_app. right.
  right. exact Hbk. }
pose proof t7_sp as (Hsp16 & Hspc & Hsp47 & Hsp1 & Hsp32 & Hsp0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof YM05.alloc_ceiling_lt as Hc47.
assert (Hes : ESTACK = 4096) by reflexivity.
destruct (t7_blk_low _ _ _ _ _ _ _ _ _ _ _ _ _ kx kk HARc HLED Hinx) as (_ & _ & Hkxc).
destruct (t7_blk_low _ _ _ _ _ _ _ _ _ _ _ _ _ sx sk HARc HLED Hins) as (_ & _ & Hsxc).
destruct (cb7t_blk_bounds B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ lyc Sc Hpc Wc memc mdc keys (8 * cap) HLED HARc eq_refl
  eq_refl HinY) as (_ & _ & _ & _ & YA & _).
destruct (cb7t_blk_bounds B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ lyc Sc Hpc Wc memc mdc kids (56 * cap) HLED HARc eq_refl
  eq_refl HinK) as (_ & _ & _ & _ & KA & _).
(* the shadow windows, at any ARx state of the walk (same allocator state, any memory) *)
assert (SHW : forall (E0 : env) memX mdX, ARx lyc Sc Hpc Wc memX mdX ->
  bv_unsigned (ew E0 59) = SHADOW_OFF -> bv_unsigned (ew E0 70) = keys + 8 * at_ ->
  bv_unsigned (ew E0 71) = kids + 56 * at_ -> sh_ok SEGS t7_Bx t7_SH E0 (mrestrict (w_H Wc) memX)).
{ intros E0 memX mdX HARX X59 X70 X71.
  apply (t7_shok E0 _ (keys + 8 * at_) (kids + 56 * at_) X59 X70 X71).
  - exact (cb7t_sh_win_keys B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ lyc Sc Hpc Wc memX mdX keys cap at_ HLED HARX eq_refl
      eq_refl HinY ltac:(lia)).
  - exact (cb7t_sh_win_kids B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ lyc Sc Hpc Wc memX mdX kids cap at_ HLED HARX eq_refl
      eq_refl HinK ltac:(lia)).
  - apply (in_app_sub _ _ _ _ YA); lia.
  - apply (in_app_sub _ _ _ _ KA); lia. }
pose proof (t7_entry fxk Wc memc rg F saved at_ keys kids kx sx HBR HD) as HS.
assert (HEI : img_env VAL A_LIM (t7_E rg saved at_ keys kids kx sx (keys + 8 * at_) (kids + 56 * at_)))
  by apply te_env.
pose proof (SHW _ memc mdc HARc E27 Uakey Uakid) as SHOK.
pose proof HMNl as HPM.
pose (RUNTO := @Crt102Kit.crt_run_to_xw_inv fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)) WS_HJ).
pose (BR := YSRrG.paj_branchR (fx := fxk) (L := B_prog_listing) (PI := PA) RZW).
unfold crt_cfg.
(* ---- +0x6f8 .. +0x72c ---- *)
t7_step RUNTO HS HJ SHOK HPM. t7_mem EM.
psrr_branch_tok RUNTO BR HS SHOK BAND_SPAN.
{ (* +0x72c bnez a2 -> unimp: (at + 2^60) >> 61 is 0, since at < 2^54 *)
  exfalso. rewrite branch_ne_U in Hc. apply negb_true_iff, Z.eqb_neq in Hc. apply Hc.
  rewrite !U_SAlu, !U_SLit, !U_SOff, Uat.
  rewrite (YP0m.zcanon_small (at_ + 1152921504606846976)) by lia.
  rewrite (YP0m.zcanon_small 61) by lia. cbn [zalu_raw]. change (Z.land 61 63) with 61.
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity. }
clear Hc. t7_step RUNTO HS HJ SHOK HPM. t7_mem EM.
psrr_branch_tok RUNTO BR HS SHOK BAND_SPAN.
{ (* +0x730 bltu a0, a1 -> unimp: &keys[at] = keys + 8 at does not wrap below keys *)
  exfalso. rewrite branch_ltu_U in Hc. apply Z.ltb_lt in Hc. revert Hc.
  rewrite ?U_SAlu, ?U_SLit, ?U_SOff, ?Z.add_0_r, ?Uakey, ?Ukeys.
  rewrite (YP0m.zcanon_small keys), (YP0m.zcanon_small (keys + 8 * at_)) by lia. lia. }
clear Hc. t7_step RUNTO HS HJ SHOK HPM. t7_mem EM.
(* ---- +0x75c jal __wrap_strcmp (back.keys[at], MOD_AT) ---- *)
assert (R1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CRT_PC_B + (CRT_CMP3_CALL_B + 4)))).
{ t7_reg HS (1%bv : bv 5) H1. rewrite H1. apply (codeptr_val _ _ HEI). }
assert (R2 : getr (ms_regs ms) 2 = w64 sp1) by (rewrite <- B2; t7_keep HS).
assert (R3 : getr (ms_regs ms) 3 = getr regs 3) by (rewrite <- B3; t7_keep HS).
assert (R4 : getr (ms_regs ms) 4 = getr regs 4) by (rewrite <- B4; t7_keep HS).
assert (R10 : getr (ms_regs ms) 10 = w64 kx).
{ t7_reg HS (10%bv : bv 5) H10. rewrite H10. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. te_close. }
assert (R11 : getr (ms_regs ms) 11 = w64 CRT_MOD_AT_B).
{ t7_reg HS (11%bv : bv 5) H11. rewrite H11.
  apply t7_img_den; [exact HEI | unfold A_TEXT, A_LIM; lia | vm_compute; reflexivity]. }
assert (HSP : YM05.alloc_ceiling + ESTACK <= spZ (ms_regs ms))
  by (unfold spZ; rewrite R2; unfold w64; rewrite unsigned_lit_small by lia; lia).
pose proof (cb7k_ret (CRT_CMP3_CALL_B + 4) ltac:(unfold CRT_CMP3_CALL_B; lia) eq_refl) as (_ & _ & Hrk1).
lazymatch type of HS with @st_ok _ _ _ ?ss1 _ =>
  assert (Hrv1 : ss_resv ss1 = None) by (vm_compute; reflexivity);
  assert (Hpc1 : ss_pc ss1 = SIGMA AS___wrap_strcmp) by (vm_compute; reflexivity) end.
(* eapply, not refine: a refine's elaboration of the `off mod 2 = 0` premise by eq_refl costs minutes *)
eapply (t7_strcmp_call fxk Wc _ _ ms _ lyc Sc Hpc kj pos (CRT_CMP3_CALL_B + 4) kx CRT_MOD_AT_B
  (Z.of_nat (length ck_MOD_AT)) (Z.of_nat (length ck_MOD_AT)) _ HS Hrv1 Hpc1).
{ exact HJ. }
{ rewrite EM. exact HRO. }
{ exact R2. } { exact R3. } { exact R4. } { exact R1. }
{ unfold CRT_CMP3_CALL_B; lia. } { reflexivity. } { exact R10. } { exact R11. }
{ rewrite EM. exact (cb7t_str_prem B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ lyc Sc Hpc Wc memc mdc (ms_regs ms) kx kk ck_MOD_AT
    HLED HARc eq_refl eq_refl Hcx HSP). }
{ rewrite EM. exact (cb7t_rom_prem_mod_at B ARx LAWS BOK IMGVIS lyc Sc Hpc Wc memc mdc (ms_regs ms) HARc HRO HKMA HSP). }
intros regs2 mem2 md2 v HJ2 HP Hv Hcmp Hfr Hpr Hmn.
rewrite EM in Hcmp, Hfr, Hpr, Hmn.
assert (Hv0 : v = w64 0).
{ apply (t7_cmp0 Wc memc (prh_lin Lamc) kx kk CRT_MOD_AT_B ck_MOD_AT v Hcx); [|exact Hcmp].
  apply (t7_rom_bytes Wc memc CRT_MOD_AT_B ck_MOD_AT HRO HKMA).
  exact (proj1 (crt_str_rom_B (PA := PA) cb7t_base_B eq_refl)). }
(* the symbolic state resumed at +0x760: the regions lie at or above s1 or below the ceiling, off strcmp's window *)
lazymatch type of HS with @st_ok _ _ ?E1 ?ss1 (restrict _ ?m1) =>
  let rs := eval vm_compute in (ss_mem ss1) in
  assert (HKR : Forall (region_kept SEGS E1 (ms_mem (restrict (w_H Wc) m1)) (mrestrict (w_H Wc) mem2)) rs);
  [ change (ms_mem (restrict (w_H Wc) m1)) with (mrestrict (w_H Wc) (ms_mem m1)); rewrite EM;
    repeat (apply Forall_cons; [split; cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
      [ intros a Ha; rewrite ?E9, ?E19, ?Uakey, ?Uakid in Ha; apply mbyte_of_aview; apply Hfr; lia
      | intros a Ha _; lia ] |]);
    apply Forall_nil
  | ];
  pose proof (st_ok_pi_after_call 72 E1 ss1 (restrict (w_H Wc) m1) regs2 (mrestrict (w_H Wc) mem2) rs
    (CRT_PC_B + (CRT_CMP3_CALL_B + 4)) HEI Hrk1 HS eq_refl ltac:(unfold A_TEXT; lia) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    (submem_refl _) ltac:(vm_compute; reflexivity) HP HKR) as HS2;
  let ss2 := eval vm_compute in (ss_after_call ss1 rs 72 (CRT_PC_B + (CRT_CMP3_CALL_B + 4))) in
  change (ss_after_call ss1 rs 72 (CRT_PC_B + (CRT_CMP3_CALL_B + 4))) with ss2 in HS2
end.
match type of HS2 with context C [@YK11.mkst ?f regs2 ?pc (mrestrict (w_H Wc) mem2) ?rom] =>
  let T := context C [restrict (w_H Wc) (@YK11.mkst f regs2 pc mem2 rom)] in
  assert (HS3 : T) by exact HS2 end.
clear HS HS2 HKR. rename HS3 into HS.
assert (HEIc1 : img_env VAL A_LIM (havoc (t7_E rg saved at_ keys kids kx sx (keys + 8 * at_) (kids + 56 * at_)) 72
  (map (getr regs2) CLOB))) by (apply img_env_havoc; [exact HEI | rewrite length_map; vm_compute; lia]).
lazymatch type of HS with st_ok_pi _ _ ?E2 _ _ =>
  assert (W59 : bv_unsigned (ew E2 59) = SHADOW_OFF) by (rewrite ew_havoc_old by lia; exact E27);
  assert (W70 : bv_unsigned (ew E2 70) = keys + 8 * at_) by (rewrite ew_havoc_old by lia; exact Uakey);
  assert (W71 : bv_unsigned (ew E2 71) = kids + 56 * at_) by (rewrite ew_havoc_old by lia; exact Uakid)
end.
pose proof (SHW _ mem2 md2 (proj1 HJ2) W59 W70 W71) as SHOK2.
assert (HPM2 : YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem2).
{ intros Hm0. apply Hmn. rewrite <- EM. exact (HPM Hm0). }
rename Hfr into K1. rename Hpr into P1.
clear HJ SHOK HPM EM R1 R2 R3 R4 R10 R11 HSP HP Hcmp W59 W70 W71.
try clear ms.
rename HJ2 into HJ. rename SHOK2 into SHOK. rename HPM2 into HPM.
(* ---- +0x760 .. the second call ---- *)
t7_step RUNTO HS HJ SHOK HPM. t7_mem EM.
psrr_branch_tok RUNTO BR HS SHOK BAND_SPAN.
{ (* +0x760 bnez a0 -> abort: strcmp (key, MOD_AT) answered 0 *)
  exfalso. rewrite branch_ne_U in Hc. apply negb_true_iff, Z.eqb_neq in Hc. apply Hc.
  lazymatch goal with |- U ?E2 (SOff ?n 0) = _ =>
    assert (A : ew E2 n = getr regs2 10)
      by exact (ew_havoc_new _ 72 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0) ltac:(rewrite length_map; vm_compute; lia))
  end.
  rewrite U_SOff, A, Hv, Hv0, U_SLit. reflexivity. }
clear Hc. t7_step RUNTO HS HJ SHOK HPM. t7_mem EM.
psrr_branch_tok RUNTO BR HS SHOK BAND_SPAN.
{ (* +0x788 bltu a0, a1 -> unimp: &kids[at] = kids + 56 at does not wrap below kids *)
  exfalso. rewrite branch_ltu_U in Hc. apply Z.ltb_lt in Hc. revert Hc.
  rewrite !U_SOff, !ew_havoc_old by lia. rewrite Uakid, Ukids, !Z.add_0_r.
  rewrite (YP0m.zcanon_small kids), (YP0m.zcanon_small (kids + 56 * at_)) by lia. lia. }
clear Hc. t7_step RUNTO HS HJ SHOK HPM. t7_mem EM.
psrr_branch_tok RUNTO BR HS SHOK BAND_SPAN.
{ (* +0x7a4 bnez a2 -> unimp: at * 56 does not overflow (its mulh and its sign word are both 0) *)
  exfalso. rewrite branch_ne_U in Hc. apply negb_true_iff, Z.eqb_neq in Hc. apply Hc.
  rewrite U_SLit. rewrite (t7_mulh0 _ 65 at_); [reflexivity | rewrite ew_havoc_old by lia; exact Uat | lia]. }
clear Hc. t7_step RUNTO HS HJ SHOK HPM. t7_mem EM.
(* ---- +0x7f0 jal __wrap_strcmp (back.kids[at].str, STAMP) ---- *)
assert (R1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CRT_PC_B + (CRT_CMP4_CALL_B + 4)))).
{ t7_reg HS (1%bv : bv 5) H1. rewrite H1. apply (codeptr_val _ _ HEIc1). }
assert (R2 : getr (ms_regs ms) 2 = w64 sp1) by (rewrite <- B2; t7_keep HS).
assert (R3 : getr (ms_regs ms) 3 = getr regs 3) by (rewrite <- B3; t7_keep HS).
assert (R4 : getr (ms_regs ms) 4 = getr regs 4) by (rewrite <- B4; t7_keep HS).
assert (R10 : getr (ms_regs ms) 10 = w64 sx).
{ t7_reg HS (10%bv : bv 5) H10. rewrite H10. cbn [sv_denot]. rewrite ew_havoc_old by lia.
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. te_close. }
assert (R11 : getr (ms_regs ms) 11 = w64 CRT_STAMP_B).
{ t7_reg HS (11%bv : bv 5) H11. rewrite H11.
  apply t7_img_den; [exact HEIc1 | unfold A_TEXT, A_LIM; lia | vm_compute; reflexivity]. }
assert (HSP : YM05.alloc_ceiling + ESTACK <= spZ (ms_regs ms))
  by (unfold spZ; rewrite R2; unfold w64; rewrite unsigned_lit_small by lia; lia).
pose proof (cb7k_ret (CRT_CMP4_CALL_B + 4) ltac:(unfold CRT_CMP4_CALL_B; lia) eq_refl) as (_ & _ & Hrk2).
pose proof HJ as (HARm & _). rewrite EM in HARm.
assert (HRO2 : arodata_okP SEGS RLO RHI B (aview SEGS (w_H Wc) mem2)).
{ intros a Hro Ho He. pose proof (t7_ro_low a Hro) as Hlw. unfold kLowMemEnd in Hlw.
  rewrite K1; [exact (HRO a Hro Ho He) | lia | lia]. }
assert (Hcs2 : pj_cstrR SEGS (mrestrict (w_H Wc) mem2) (prh_lin Lamc) sx sk ck_STAMP).
{ apply (pj_cstrR_frame SEGS _ _ _ _ _ _ Hcs). intros y Hy. apply mbyte_of_aview. apply K1; lia. }
lazymatch type of HS with @st_ok _ _ _ ?ss1 _ =>
  assert (Hrv2 : ss_resv ss1 = None) by (vm_compute; reflexivity);
  assert (Hpc2 : ss_pc ss1 = SIGMA AS___wrap_strcmp) by (vm_compute; reflexivity) end.
eapply (t7_strcmp_call fxk Wc _ _ ms _ lyc Sc Hpc kj pos (CRT_CMP4_CALL_B + 4) sx CRT_STAMP_B
  (Z.of_nat (length ck_STAMP)) (Z.of_nat (length ck_STAMP)) _ HS Hrv2 Hpc2).
{ exact HJ. }
{ rewrite EM. exact HRO2. }
{ exact R2. } { exact R3. } { exact R4. } { exact R1. }
{ unfold CRT_CMP4_CALL_B; lia. } { reflexivity. } { exact R10. } { exact R11. }
{ rewrite EM. exact (cb7t_str_prem B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ lyc Sc Hpc Wc mem2 _ (ms_regs ms) sx sk ck_STAMP
    HLED HARm eq_refl eq_refl Hcs2 HSP). }
{ rewrite EM. exact (cb7t_rom_prem_stamp B ARx LAWS BOK IMGVIS lyc Sc Hpc Wc mem2 _ (ms_regs ms) HARm HRO2 HKST HSP). }
intros regs3 mem3 md3 v3 HJ3 HP3 Hv3 Hcmp3 Hfr3 Hpr3 Hmn3.
rewrite EM in Hcmp3, Hfr3, Hpr3, Hmn3.
assert (Hv30 : v3 = w64 0).
{ apply (t7_cmp0 Wc mem2 (prh_lin Lamc) sx sk CRT_STAMP_B ck_STAMP v3 Hcs2); [|exact Hcmp3].
  apply (t7_rom_bytes Wc mem2 CRT_STAMP_B ck_STAMP HRO2 HKST).
  exact (proj2 (crt_str_rom_B (PA := PA) cb7t_base_B eq_refl)). }
lazymatch type of HS with @st_ok _ _ ?E1 ?ss1 (restrict _ ?m1) =>
  let rs := eval vm_compute in (ss_mem ss1) in
  assert (HKR : Forall (region_kept SEGS E1 (ms_mem (restrict (w_H Wc) m1)) (mrestrict (w_H Wc) mem3)) rs);
  [ change (ms_mem (restrict (w_H Wc) m1)) with (mrestrict (w_H Wc) (ms_mem m1)); rewrite EM;
    repeat (apply Forall_cons; [split; cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
      [ intros a Ha; rewrite ?ew_havoc_old in Ha by lia; rewrite ?E9, ?E19, ?Uakey, ?Uakid in Ha;
        apply mbyte_of_aview; apply Hfr3; lia
      | intros a Ha _; lia ] |]);
    apply Forall_nil
  | ];
  pose proof (st_ok_pi_after_call 88 E1 ss1 (restrict (w_H Wc) m1) regs3 (mrestrict (w_H Wc) mem3) rs
    (CRT_PC_B + (CRT_CMP4_CALL_B + 4)) HEIc1 Hrk2 HS eq_refl ltac:(unfold A_TEXT; lia) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    (submem_refl _) ltac:(vm_compute; reflexivity) HP3 HKR) as HS2;
  let ss2 := eval vm_compute in (ss_after_call ss1 rs 88 (CRT_PC_B + (CRT_CMP4_CALL_B + 4))) in
  change (ss_after_call ss1 rs 88 (CRT_PC_B + (CRT_CMP4_CALL_B + 4))) with ss2 in HS2
end.
match type of HS2 with context C [@YK11.mkst ?f regs3 ?pc (mrestrict (w_H Wc) mem3) ?rom] =>
  let T := context C [restrict (w_H Wc) (@YK11.mkst f regs3 pc mem3 rom)] in
  assert (HS3 : T) by exact HS2 end.
clear HS HS2 HKR. rename HS3 into HS.
assert (HEIc2 : img_env VAL A_LIM (havoc (havoc (t7_E rg saved at_ keys kids kx sx (keys + 8 * at_) (kids + 56 * at_)) 72
  (map (getr regs2) CLOB)) 88 (map (getr regs3) CLOB))) by (apply img_env_havoc; [exact HEIc1 | rewrite length_map; vm_compute; lia]).
lazymatch type of HS with st_ok_pi _ _ ?E3 _ _ =>
  assert (W59 : bv_unsigned (ew E3 59) = SHADOW_OFF) by (rewrite !ew_havoc_old by lia; exact E27);
  assert (W70 : bv_unsigned (ew E3 70) = keys + 8 * at_) by (rewrite !ew_havoc_old by lia; exact Uakey);
  assert (W71 : bv_unsigned (ew E3 71) = kids + 56 * at_) by (rewrite !ew_havoc_old by lia; exact Uakid)
end.
pose proof (SHW _ mem3 md3 (proj1 HJ3) W59 W70 W71) as SHOK3.
assert (HPM3 : YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem3).
{ intros Hm0. apply Hmn3. rewrite <- EM. exact (HPM Hm0). }
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 2 * ESTACK <= a < sp1) ->
  aview SEGS (w_H Wc) mem3 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hn. rewrite (Hfr3 a Ha Hn). exact (K1 a Ha Hn). }
assert (P2 : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) mem3 a) by (intros a Ha; exact (Hpr3 a (P1 a Ha))).
clear HJ SHOK HPM EM R1 R2 R3 R4 R10 R11 HSP HP3 Hcmp3 W59 W70 W71 HARm.
try clear ms.
rename HJ3 into HJ. rename SHOK3 into SHOK. rename HPM3 into HPM.
(* ---- +0x7f4 .. +0x7f8 ---- *)
t7_step RUNTO HS HJ SHOK HPM. t7_mem EM.
psrr_branch_tok RUNTO BR HS SHOK BAND_SPAN.
{ (* +0x7f4 bnez a0 -> abort: strcmp (stamp, STAMP) answered 0 *)
  exfalso. rewrite branch_ne_U in Hc. apply negb_true_iff, Z.eqb_neq in Hc. apply Hc.
  lazymatch goal with |- U ?E3 (SOff ?n 0) = _ =>
    assert (A : ew E3 n = getr regs3 10)
      by exact (ew_havoc_new _ 88 (map (getr regs3) CLOB) 4 (Z_to_bv 64 0) ltac:(rewrite length_map; vm_compute; lia))
  end.
  rewrite U_SOff, A, Hv3, Hv30, U_SLit. reflexivity. }
clear Hc. t7_step_to RUNTO HS HJ SHOK HPM (CRT_PC_B + CRT7_FF_OFF_B). t7_mem EM.
(* ---- +0x7f8 (FF): the boundary at the new memory and registers; t7_ext unchanged ---- *)
pmkst HS.
lazymatch goal with |- YA0nH.SRr' _ _ _ {| cfg_ms := mkst _ (Z_to_bv 64 (_ + ?n)) _ _; cfg_model := _ |} _ =>
  change n with (CRT_PC_B + CRT7_FF_OFF_B) end.
assert (KR : forall rr : bv 5, In rr [2; 3; 4; 8; 9; 18; 19; 20; 23; 25; 27]%bv -> getr (ms_regs ms) rr = getr rg rr).
{ intros rr Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [t7_keep HS |]). destruct Hr. }
rewrite EM in HJ, HPM.
apply (HFF fxk lyc Sc Hpc Wc (ms_mem ms) _ kj pos Dc Dback Lamc peakc cntc (ms_regs ms) mms cset saved kw).
rewrite EM.
assert (Klow : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H Wc) mem3 a = aview SEGS (w_H Wc) memc a)
  by (intros a Ha; apply K2; lia).
assert (Khigh : forall a, sp1 <= a < 2 ^ 64 -> aview SEGS (w_H Wc) mem3 a = aview SEGS (w_H Wc) memc a)
  by (intros a Ha; apply K2; lia).
refine {| crt_at_C_B_obj := Et; crt_at_C_B_frm_zero := HFZ; crt_at_C_B_fregs := HFK; crt_at_C_B_live := _;
  crt_at_C_B_bregs := _; crt_at_C_B_sp_saved := _; crt_at_C_B_sp_back := _; crt_at_C_B_sp_at := _;
  crt_at_C_B_back_open := _; crt_at_C_B_v_open := _; crt_at_C_B_cset_range := Hcs0; crt_at_C_B_cset_mod := Hcs1;
  crt_at_C_B_cnt := Hcnt; crt_at_C_B_saved_nz := Hsv0; crt_at_C_B_copy := _; crt_at_C_B_copy_fd := _;
  crt_at_C_B_back := _; crt_at_C_B_pos := HPOS; crt_at_C_B_kw := HKW; crt_at_C_B_back_tblk := HPMB;
  crt_at_C_B_back_fo := _; crt_at_C_B_copy_tblk := HPMC; crt_at_C_B_copy_fo := _; crt_at_C_B_copy_depth := HDEP |}.
{ exact (t7_live_keep lyc Sc Hpc Wc memc mem3 mdc _ kj kj pos _ Lamc peakc cntc 0 0 (sp1 - 2 * ESTACK) sp1
    HL HJ HB_HJ ltac:(lia) ltac:(unfold CRT_SP_F; lia) K2 P2 HPM). }
{ refine {| crt_bregs_B_sp := _; crt_bregs_B_gp := _; crt_bregs_B_tp := _; crt_bregs_B_s0 := _; crt_bregs_B_s1 := _;
    crt_bregs_B_s2 := _; crt_bregs_B_s4 := _; crt_bregs_B_s3 := _; crt_bregs_B_s7 := _; crt_bregs_B_s9 := _;
    crt_bregs_B_s11 := _ |}; rewrite KR by (cbv; tauto).
  - exact B2. - exact B3. - exact B4. - exact B8. - exact B9. - exact B18. - exact B20. - exact B19. - exact B23.
  - exact B25. - exact B27. }
{ unfold crt_spill; apply (ts_vm_av (w_H Wc) (w_H Wc) memc mem3);
    [intros j Hj; apply Khigh; unfold CRT_SP_SAVED_B; lia | exact HSPS]. }
{ unfold crt_spill; apply (ts_vm_av (w_H Wc) (w_H Wc) memc mem3);
    [intros j Hj; apply Khigh; unfold CRT_SP_BACK; lia | exact HSPB]. }
{ unfold crt_spill; apply (ts_vm_av (w_H Wc) (w_H Wc) memc mem3);
    [intros j Hj; apply Khigh; unfold CRT_SP_AT_B; lia | exact HSPA]. }
{ apply (range_addressable_agree (aview SEGS (w_H Wc) memc)); [|exact HRAB].
  intros y Hy; apply Klow; unfold shadow_of_addr, SHADOW_OFF, CRT_OFF_BACK in *; lia. }
{ apply (range_addressable_agree (aview SEGS (w_H Wc) memc)); [|exact HRAV].
  intros y Hy; apply Klow; unfold shadow_of_addr, SHADOW_OFF, CRT_OFF_V in *; lia. }
{ apply (pj_nodeR_frame SEGS _ _ _ _ _ _ HNC).
  apply (t7_agree_low lyc Sc Hpc Wc memc mdc Lamc peakc cntc SIZE_MAXZ 0 most 0 memc mem3 _ Dc HARc HLED HDcp);
    [unfold CRT_OFF_COPY; lia | unfold CRT_OFF_COPY; lia | exact Klow | exact P2]. }
{ apply (t7_fdR_frame _ _ _ _ _ _ HFD).
  apply (t7_agree_low lyc Sc Hpc Wc memc mdc Lamc peakc cntc SIZE_MAXZ 0 most 0 memc mem3 _ Dc HARc HLED HDcp);
    [unfold CRT_OFF_COPY; lia | unfold CRT_OFF_COPY; lia | exact Klow | exact P2]. }
{ apply (pj_nodeR_frame SEGS _ _ _ _ _ _ HNB).
  apply (t7_agree_low lyc Sc Hpc Wc memc mdc Lamc peakc cntc SIZE_MAXZ 0 most 0 memc mem3 _ Dback HARc HLED HDbk);
    [unfold CRT_OFF_BACK; lia | unfold CRT_OFF_BACK; lia | exact Klow | exact P2]. }
(* the room position and the pure facts of the C boundary (kw, back's and copy's block sizes, copy's depth) as they
   were; back's and copy's free orders over the new memory by the order list's frame law (PRH_PjOrder.pj_foR_frame) *)
{ destruct HFOB as (Fb & HFO & HFt). exists Fb. split; [|exact HFt].
  apply (PRH_PjOrder.pj_foR_frame SEGS DOC_D _ _ (prh_lin Lamc) (prh_lin Lamc) _ Dback Fb HFO);
    [intros a k Hak; exact (PRH_PjOrder.pj_foR_lblk SEGS _ _ _ _ _ _ HFO a k Hak)|].
  apply (t7_agree_low lyc Sc Hpc Wc memc mdc Lamc peakc cntc SIZE_MAXZ 0 most 0 memc mem3 _ Dback HARc HLED HDbk);
    [unfold CRT_OFF_BACK; lia | unfold CRT_OFF_BACK; lia | exact Klow | exact P2]. }
{ destruct HFOC as (Fc & HFOc & HFtc). exists Fc. split; [|exact HFtc].
  apply (PRH_PjOrder.pj_foR_frame SEGS DOC_D _ _ (prh_lin Lamc) (prh_lin Lamc) _ Dc Fc HFOc);
    [intros a k Hak; exact (PRH_PjOrder.pj_foR_lblk SEGS _ _ _ _ _ _ HFOc a k Hak)|].
  apply (t7_agree_low lyc Sc Hpc Wc memc mdc Lamc peakc cntc SIZE_MAXZ 0 most 0 memc mem3 _ Dc HARc HLED HDcp);
    [unfold CRT_OFF_COPY; lia | unfold CRT_OFF_COPY; lia | exact Klow | exact P2]. }
Qed.

End g.
End f.
End t7.
