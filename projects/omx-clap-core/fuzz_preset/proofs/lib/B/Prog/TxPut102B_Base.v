(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: for omx-clap-core/fuzz_preset, the CALLER-WINDOW call kit over YCbqG.v's journal
   ajournal_x (allocator invariant a parameter ARx, ghost head set Hp after S, program statics PST), generic: no image
   class, no address, no ledger. Credit: WalkS4, lib/A/Prog/PRW_CallerJ.v at 85a188622c5 (statements and proofs taken
   from there; changes below). Donors there: cj_kept from cgif_file_fuzzer lib/YC20.v:311-325 tlzw_kept and
   lib/YC8n.v:272-287 tlzw_kept_of_journal (origin/release/pau-projects-recipes), generalised to ajournal_x's keep
   clauses; aj_call_xW from YCbqGcall.v aj_call_x (cgif YCbq.v:1845-1883 aj_call, origin/ossv/recipes).
   What a walk of a function in the caller-window form needs:
   - fwin_x / fpostW_x / fpostWF_x: lib/A/PRH_Base.v's fwin / fpostW / fpostWF (K0) restated with the image segs and
     the statics PST as parameters, same bodies: PRH_Base.fpostW B ARx SK STK d FP .. is
     fpostW_x (SK := SK) pa_segs B prh_pst ARx STK d FP .. by unfolding (this file does not Require lib/A).
   - START: ajournal_x_init_W, the widened journal (STK + e) (sp + e) at the entry state.
   - CALL of a caller-window callee: aj_call_xW / aj_call_xWF (callee state in mkst form), aj_call_xW_sp /
     aj_call_xWF_sp (the entry form of YCbqGcall.v's aj_call_x_sp: st_ok, ss_resv, the machine state ms).
     The footprint side condition is YCbqG.v's own fp_sub_x (h-hpreset-7 9052c7a7d74 :688-691), whose fourth
     disjunct `sp0 - STK <= a < sp0` is the caller's window: WalkS4's fp_sub_xW is that predicate, so this file
     no longer states one and ajournal_x_sub_W (the name WalkS4's callers use) is YCbqG's ajournal_x_sub.
   - vrd_call_W: h-verbs-3's lib/A/VrdArm.v call rule (6d4cddbdff5), premise shape kept, as a corollary of
     aj_call_xW_sp at e1 := - o.
   - aj_call_xWF_d: WalkH6's caller-window float call rule (h-walk-identity's S8aCallW.v aj_call_xWF), verbatim: no
     fwin_x for the callee and no window-kept clause on either side.
   - END: cj_kept (the keep clauses of ajournal_x relative to the entry, the walker's window and its written cells OR
     exempted) across stretches (cj_kept_exec) and calls (cj_kept_of_journal), chained (cj_kept_trans), closed by
     fpostW_x_of_kept / fpostWF_x_of_kept; fpostW_x_of_apost: apost_base_x is fpostW_x at e = 0.
   Numerals: 16, 4096, 8, 4 and 2 ^ 64 are LENGTH; 0 is LENGTH (the empty window e = 0) or DERIVED (event count);
   register numbers 1, 3, 4 (ra, gp, tp) are WORD. No address literal; no image constant. *)
(* Modified by Theorem Labs, 2026-10: the kit over a world relation R (suffix R). A free or realloc of a live block can
   hide shadow again, so a walk that crosses one proves YA0nH.SRrG at a relation wider than wle with its journal at that
   relation (YCbqG.v ajournal_xR). cj_keptR is cj_kept with the world conjunct R W W2 (a copy of the body; the guard
   cj_kept_R_wle shows by reflexivity that cj_kept is cj_keptR at wle). The R forms of cj_kept_refl / cj_kept_exec /
   ajournal_x_init_W take R and its reflexivity, of cj_kept_trans / ajournal_x_sub_W R and its transitivity, of
   cj_kept_of_journal / fpostW_x_of_apost / fpostW_x_of_kept / fpostWF_x_of_kept R alone; the call rules
   aj_call_xWR / aj_call_xW_spR / aj_call_xWFR / aj_call_xWF_spR / vrd_call_WR / aj_call_xWF_dR take R and both laws
   first, then the plain rule's binders, with the journals, the callee's post (fpostW_xR / fpostWF_xR) and the
   conclusion at R. Each plain lemma is its R form at wle (wle_refl / wle_trans); its statement is unchanged.
   fpostW_x_R_lift: a plain fpostW_x (journal at wle) is fpostW_xR at every R that contains wle. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YCbqGcallW.v, with its module names changed; 482 of its 526 lines of code are new or changed and 767 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S4_PsFree.v, with its module paths and module names changed; 338 of its 374 lines of code are new or changed and 490 lines of the source are left out. *)
(* fuzz_preset lib/B, the #102 re-walk of tx_put on image B' (asan-ubsan build): the SHARED BASE of the segment
   lemmas. STATEMENTS ONLY: the entry record, the text's premises, the cut predicates and
   the segment statements; the segment files TxPut102B_S*.v prove them, TxPut102B_Top.v composes them.
   rule 24: proves function tx_put (reuse search: the internal file REWALK-102-PLAN.md section T3)
   PORT of the A' walk's lib/A/Prog/TxPut102A_Base.v (sha256 848cc1b66e6d; internal record), SAME cut
   structure and predicates, so the two images' walks state the same segments; the changes are the listing (B'), the
   PrhImg (prh_img_B), the listing tables (PLB102.v's PL_B102) and the DERIVED cut offsets of B'.
   THE IMAGE: B' = asan-ubsan pin sha256 d663f82d7f488d30 (unstripped twin c90d4fa54d43160b); listing
   lib/B/Listing_prog.v (sha256 416d90f8ab75; internal record) (lib/B/PAImg_prog.v
   (sha256 9d9fb9d40244; internal record) fails at :160 until IMG_TOP_B = 0x601000 lands, so this file is PARAMETRIC over
   {PA : PAImg B_prog_listing}). The text: the kit's lib/A/PRH_FnTx.v (sha256 b9cc6fd3c406; internal record) (ttx_put_specX
   :275-303; REBASED 2026-10-29 ~14:45Z onto the #102 tip, PRH_FnTx.v (sha256 00de73011bd4; internal record) :298-331, whose post
   takes the GROW's run event as a hypothesis), proved through the twin TxPutCall102.ttx_put_specX_ev.
   THE CODE (B' 0x851d0, slot 3777, 156 instructions, frame 112, 13 saved registers; DERIVED byte offsets):
     +0    prologue (ra +104, s0 +96 .. s11 +8); s0 = t; `andi a0, a0, 7; bnez -> +488 unimp` (UBSan alignment,
           NOT TAKEN: prhtx_place's t mod 8 = 0); s1 = n, s2 = s, s6 = the shadow base, s4 = t + 24,
           s8 = shadow (t + 24), the 4-byte load check (slow path +492, report +508 REFUTED), `lw a0, 0(s4)` = failed
     +112  bnez a0 -> +400 (A0 FAILED AT ENTRY)
     +116  s3 = t + 8 / s7 (report +544), s5 = t + 16 / s9 (report +552) load checks; a0 = n + t->n, a1 = a0 + 1,
           a2 = t->cap, s10 = t >> 3
     +176  bgeu a2, a1 -> +256 (FIT)                                             [S0 ends at END / FIT / GROW]
     +180  TP_PC_GROW: s11 = shadow (t), load check (report +592); a0 = t->b, a1 = 2 * a1; jal realloc (+200,
           AS___wrap_realloc); beqz a0 -> +460 (NULL); store check of t (report +600), `sd a0, 0(s0)`; load checks
           of t + 8 / t + 16 (+608 / +616); a0 = (t->n + n) * 2 + 2; `sd a0, 0(s5)` = t->cap           [S_GROW]
     +256  TP_PC_FIT: s10 = shadow (t), load checks of t / t + 8 (+560 / +568); a0 = t->n + t->b; UBSan b + len
           wrap / NULL (+288 bltu, +304 beqz -> +488 unimp, NOT TAKEN: 4096 <= b1, b1 + cap1 < 2 ^ 64);
           jal __asan_memcpy (+316); load check of t + 8 (+576); t->n := t->n + n; load check of t (+584);
           UBSan b + n' wrap / NULL and b = 0 (+356, +372, +376 -> +488, NOT TAKEN); 1-byte store check of
           b + n' (slow path +512, report +520 REFUTED); `sb zero, 0(a0)`                              [S_FIT]
     +400  TP_PC_END: the 13 restores, `addi sp, sp, 112`, ret (+456)                                [S_END]
     +460  TP_PC_NULL: `sb 1` to g_own_ran_out (A_OBJ 13, no ASan check; alias hint (A_HI 62) - 1564), 4-byte
           store check of t + 24 (slow path +524, report +540 REFUTED), `sw 1, 0(s4)` = failed, j +400 [S_NULL]
   THE FORM, THE ALLOCATOR, THE NAMED ARGUMENTS: TxPut102A_Base.v's header, unchanged. Numerals: the byte offsets
   0..624 are DERIVED (4 x slot inside the function), the rest as TxPut102A_Base.v. No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00cf YG01cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallx YGcallcf YGcallRx YGcallRcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRealloc ReallocP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YSRrMemnorm YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger TxModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRoomPosKeep PresetRun PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRealloc YGcfAmx2.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost YGcfAroBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstReallocKKeep YGcfReallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PLB102.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnTx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import TxPutCall102.
(* the PLAIN build's sink instance is loaded transitively here; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the function's cut offsets (DERIVED byte offsets inside tx_put, B' listing 8bcc2c9e7809) ---- *)
Definition TP_SLOT : nat := 3777.
Definition TP_OFF : Z := 4 * Z.of_nat TP_SLOT.
Definition TP_FRAME : Z := 112.
Definition TP_PC_GROW : Z := 180.   (* the grow block: the load check of t, then the realloc call *)
Definition TP_PC_FIT : Z := 256.    (* the rejoin: the memcpy, the length update and the NUL store *)
Definition TP_PC_END : Z := 400.    (* the epilogue *)
Definition TP_PC_NULL : Z := 460.   (* the refused grow: g_own_ran_out := 1, failed := 1, j END *)
Lemma TP_OFF_val : TP_OFF = 15108.
Proof. vm_compute. reflexivity. Qed.
Lemma TP_FRAME_val : pi_frame (PrhImg := prh_img_B) F_tx_put = TP_FRAME.
Proof. vm_compute. reflexivity. Qed.

(* the listing's own tables: PLB102.v's PL_B102 (B PAImg_prog.v 4392ab2c09ba :177-181 verbatim, renamed) *)

Section tp. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {PA : PAImg B_prog_listing}.
(* the image's generated per-function data (PRH_Img.v, #102 pins), the listing's tables, and the room instance prh_room_live_a8,
   bound ONCE here *)
#[local] Instance TP_PrhImg : PrhImg := prh_img_B.
#[local] Instance TP_PAListing : PAListing B_prog_listing := PL_B102.
#[local] Instance TP_RL : PrhRoomLive := prh_room_live_a8.
#[local] Notation segs := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable SK : YI16.sink_head.
Variable CTX0 : list (list Z).
(* the allocator relation of the walk (YGcallcf.v's): ARcf with the error-buffer extents placed *)
Definition ARcfx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop :=
  fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ xs_placed_cf ly S.

(* ---- THE IMAGE FACTS the walk reads of PA, each proved at the instance by computation (PAImg_prog.v's
   B_entry_tx_put and B_prog_val, and the object pin 13 = g_own_ran_out) ---- *)
Record tp_img : Prop := {
  tpi_base : BASE = B_prog_base;
  tpi_entry : SIGMA AS_tx_put = BASE + TP_OFF;
  tpi_realloc : SIGMA AS___wrap_realloc = cf_pc_wrap_realloc;
  (* NO field for __asan_memcpy: its text is taken at the listing's own `SIGMA AS___asan_memcpy`, as the AI of the
     earlier tx_put walk's template (blob 185d37e0973) and FuzzStrdup.v do, so no equation against
     `pc_asan_memcpy (as_code B)` is needed and
     tp_img stays a record of PA / CfImg facts, each closed at the instance by vm_compute. *)
  (* the shadow-base GOT word (A_OBJ 0) and cell (A_OBJ 12), their disjointness, api_env (YGcallRx's errno_low) and the
     wrapper entries (the finding on the A' prologue; B' has the same prologue: PLdHi (10) (10) 61 (A_OBJ 0)
     at slot 3797, then `ld s6, 0(a0)`); closed at the instance by PALibB.v's exvi_eh_palib through palib_core *)
  tpi_pal : PALibCore (PI := PA) B;
  tpi_own : VAL (A_OBJ 13) = pi_g_own_ran_out;
  (* the REFUSED arm's store (the TPA-NULL finding, 15:0xZ): the `sb` to g_own_ran_out goes through the
     auipc base A_HI 62 at -1564 (alias row B_alias_hints (SOff (A_HI 62) (-1564), SOff (A_OBJ 13) 0), Listing_prog.v
     8bcc2c9e7809 :7757; PAImg_prog.v's B_alias_hints_ok proves it at the instance) *)
  tpi_hi_own : VAL (A_HI 62) - 1564 = VAL (A_OBJ 13);
  (* the program-written statics are writable image bytes, outside the read-only view (Caw102A's two findings: the
     journal exempts prh_pst from its image clause, and the runtime rules keep a static only when in_img) *)
  tpi_pst_rw : forall a, Exists (in_zr a) prh_pst -> ~ in_roP segs (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) a;
  tpi_pst_img : forall a, Exists (in_zr a) prh_pst -> in_img segs a;
  (* and neither runtime-owned nor errno (the journal's PST write, YCbqG.v ajournal_x_pst_write) *)
  tpi_pst_owned : forall a, Exists (in_zr a) prh_pst -> ~ Exists (in_zr a) (as_owned_static B);
  tpi_pst_errno : forall a, Exists (in_zr a) prh_pst -> ~ (as_errno B <= a < as_errno B + 4);
  (* the A' GROW row's two findings (15:4xZ; A' TxPut102A_Base.v (sha256 62ed8c667f58; internal record), same names, appended in its order), both from
     tp_side after the realloc - GROW is the only row that carries src_rd and the ledger across an allocator call:
     - the harness head is at least one shadow granule wide (PRH_Base.v's prh_head_wide): prh_hblock reads 8 head
       bytes at a - cf_head and the call journal keeps only the bytes i < req_size (k + cf_head) of a live block.
       A CfParams fact: cf_head = 16 at the instance, by vm_compute;
     - the image's shadow is present in every ARcf state: YGcfAmx2.img_shadow_vis_cf VERBATIM, over the
       CfImg's own cf_img_lo / cf_img_top (the per-instance rule, 18:56Z): src_rd's shadow_hull_vis for an in_zs
       global or a kept_img string reads shadow bytes no ARcf or journal clause keeps across the realloc. A fact of
       the image binding of B: the instance derives it from TfibSyms B (TxPut102B_Wit.v), or cites
       tfib_img_shadow_vis_cf_B when it lands. *)
  tpi_head_wide : prh_head_wide;
  tpi_img_shvis : YGcfAmx2.img_shadow_vis_cf segs B;
  (* the instance's image bounds are the CfImg's (the per-instance kept_img / kept_at read pa_lo / pa_hi; a Theorem Labs walk's
     stand-in reads cf_img_lo / cf_img_top): proved equal at the instance by vm_compute *)
  tpi_img_bounds : @pa_lo _ B_prog_listing PA = cf_img_lo /\ @pa_hi _ B_prog_listing PA = cf_img_top;
  (* THE ALLOCATOR HULL AT THE GROW'S CALL (route (b): the text's premise length rp_os <= 4 is threaded to the call).
     Two CfParams facts at a run position of a run of at most 4 calls, each closed at the instance (CfParams_preset):
     the admission cf_hull_ok S that QMm_cf reads at the call (PresetHullPay.hull_ok_of_budget at the budget that
     PresetHullPay.hull_budget_of_room_pos gives for the empty list), and the realloc tree's entry headroom
     cf_hull_adm S n at the position's event HRe m n (PresetDrvHeadroomB.drv_cf_headroom_at_call_B), which the primed
     realloc row YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep takes after its trace premise *)
  tpi_hull_ok : forall sm x os i H0 hist S, (length os <= 4)%nat ->
    PresetRoomPos.iface_room_pos sm x os i H0 hist S -> cf_hull_ok S;
  tpi_hull_adm : forall sm x os i H0 hist S m n, (length os <= 4)%nat ->
    PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
    nth_error (PresetRun.hruns sm x os) i = Some (PresetReqAt.HRe m n) -> cf_hull_adm S n;
  (* THE CALL MEMORY'S RELRO FACT at the GROW's call (QMm_cf's last conjunct arodata_ok_cf, carried from the entry's
     arodata_okP by YGcallcf.arodata_ok_cf_of_journal_P): the CfImg's RELRO range and each cf_ro_reads range in one
     segment, errno apart from them, the listing's RELRO bounds the CfImg's and below 2 ^ 64, no program-written
     static at an aro_addr_cf address, and each cf_ro_reads range in a non-writable segment inside 2 ^ 64; image facts,
     each closed at the instance *)
  tpi_relro_seg : relro_seg_t segs;
  tpi_errno_relro : errno_relro_t B;
  tpi_relro_bounds : @pa_relro_lo _ _ PA = cf_relro_lo /\ @pa_relro_hi _ _ PA = cf_relro_hi /\ cf_relro_hi <= 2 ^ 64;
  tpi_relro_pst : forall a, aro_addr_cf a -> ~ Exists (in_zr a) prh_pst;
  tpi_ro_reads_nw : YGcfAroBridge.ro_reads_nw_t segs
}.
(* THE B' SLOT AUDIT (listing 8bcc2c9e7809 slots 3777 .. 3932, the whole function): its image-dependent reads are the
   typed GOT load `PHi (10) 61; PLdHi (10) (10) 61 (A_OBJ 0)` (slots 3796-3797: tpi_pal), the one auipc-plus-immediate
   pair `PHi (11) 62` + `sb a0, -1564(a1)` (slots 3892 / 3894: tpi_hi_own, tpi_own), `PCall AS___wrap_realloc`
   (slot 3827: tpi_realloc) and `PCall AS___asan_memcpy` (slot 3856: taken at SIGMA AS___asan_memcpy); the thirteen
   `PCall AS___asan_report_*` (slots 3904 .. 3932) and the `unimp` at slot 3899 are refuted / not taken. No other PHi,
   PLdHi or image-addressed slot. *)

Definition tp_pc (o : Z) : Z := BASE + TP_OFF + o.

(* ---- THE ENTRY DATA: every binder of ttx_put_specX (PRH_FnTx.v c798df739d78 :275-278) ---- *)
Record tp_in : Type := mkTpIn {
  tp_rp_sm : list Z -> Z * Z; tp_rp_x : list Z; tp_rp_os : list (option nat * option nat * option nat);
  tp_rp_i : nat; tp_rp_H0 : list Z; tp_rp_hist : list YG00.chunk;
  tp_ly : alayout; tp_S : astate; tp_Hp : list Z; tp_W : world segs;
  tp_regs : bvmap 5 word; tp_mem : word -> option byte; tp_md : Model; tp_ch : list (Z * Z * Z);
  tp_dw : Z; tp_t : Z; tp_s : Z; tp_n : Z; tp_b0 : Z; tp_len0 : Z; tp_cap0 : Z; tp_f0 : Z; tp_own : Z;
  tp_txt : list Z; tp_src : list Z; tp_Lam : list (Z * Z);
  tp_peak : Z; tp_cnt : Z; tp_fail : Z; tp_ran : Z; tp_most : Z
}.
Definition tp_sp0 (D : tp_in) : Z := spZ (tp_regs D).
(* the grow's request: 2 * (len0 + n + 1), and the capacity the DONE arm gives (TxModel.tx_cap1) *)
Definition tp_need (D : tp_in) : Z := tp_len0 D + tp_n D + 1.
Definition tp_req (D : tp_in) : Z := 2 * tp_need D.
Definition tp_cap1 (D : tp_in) : Z := TxModel.tx_cap1 (tp_len0 D) (tp_cap0 D) (tp_n D).
(* the number of this call's run events (prhtx_evs: one per grow), the batch-kit text's wild-room and consumer-window count *)
Definition tp_evk (D : tp_in) : nat := length (prhtx_evs (tp_len0 D) (tp_cap0 D) [tp_n D]).
Lemma tp_evk_grow : forall D, tp_cap0 D < tp_need D -> tp_evk D = 1%nat.
Proof.
intros D H. unfold tp_evk, tp_need in *. cbn [prhtx_evs].
destruct (tp_len0 D + tp_n D + 1 <=? tp_cap0 D) eqn:E; [apply Z.leb_le in E; lia | reflexivity].
Qed.
Lemma tp_evk_fit : forall D, tp_need D <= tp_cap0 D -> tp_evk D = 0%nat.
Proof.
intros D H. unfold tp_evk, tp_need in *. cbn [prhtx_evs].
destruct (tp_len0 D + tp_n D + 1 <=? tp_cap0 D) eqn:E; [reflexivity | apply Z.leb_gt in E; lia].
Qed.

(* ---- ttx_put_specX_ev's premises (lib/A/Prog/TxPutCall102.v, the shared twin of the ttx_put_specX, PRH_FnTx.v
   88468bf162d8 (the batch kit c23331281d07), with tp_live after the iface_room_pos premise) but its two new batch-kit
   premises (tp_k1pre below), at one record, in the twin's order, and the run-length premise (length rp_os <= 4) LAST (:238-240), so the positional reads of the earlier conjuncts do not move ---- *)
Definition tp_pre (D : tp_in) : Prop :=
  fpre B ARcfx STK_tx_put (tp_ly D) (tp_S D) (tp_Hp D) (tp_W D) (tp_regs D) (tp_mem D) (tp_md D) (tp_ch D) /\
  prh_univ_closure B CTX0 /\
  room_live_cf (tp_S D) /\
  PresetRoomPos.iface_room_pos (tp_rp_sm D) (tp_rp_x D) (tp_rp_os D) (tp_rp_i D) (tp_rp_H0 D) (tp_rp_hist D) (tp_S D) /\
  TxPutCall102.tp_live (tp_S D) /\
  getr (tp_regs D) 10 = w64 (tp_t D) /\ getr (tp_regs D) 11 = w64 (tp_s D) /\ getr (tp_regs D) 12 = w64 (tp_n D) /\
  fwin (tp_ly D) (tp_W D) (tp_regs D) (tp_mem D) (tp_dw D) /\
  prhtx_place (tp_ly D) (tp_S D) (tp_W D) (tp_regs D) (tp_mem D) (tp_dw D) (tp_t D) /\
  prhtx_trace B (tp_ly D) (tp_W D) (tp_mem D) (tp_t D) /\
  prhtx_rec (tp_W D) (tp_mem D) (tp_t D) (tp_b0 D) (tp_len0 D) (tp_cap0 D) (tp_f0 D) /\
  prhtx_inv B (tp_Lam D) (tp_ly D) (tp_S D) (tp_W D) (tp_mem D) (tp_b0 D) (tp_len0 D) (tp_cap0 D) (tp_txt D) /\
  src_rd (tp_W D) (tp_mem D) (tp_s D) (tp_src D) /\ Z.of_nat (length (tp_src D)) = tp_n D /\
  prhtx_kept B (tp_Lam D) (tp_ly D) (tp_S D) (tp_s D) (tp_n D) /\
  (forall a, tp_s D <= a < tp_s D + tp_n D ->
     ~ (tp_t D <= a < tp_t D + 28) /\ ~ (tp_b0 D <= a < tp_b0 D + tp_cap0 D)) /\
  tp_need D <= 2 ^ 28 /\
  prh_ledger B (tp_ly D) (tp_S D) (tp_Hp D) (tp_W D) (tp_mem D) (tp_Lam D)
    (tp_peak D) (tp_cnt D) (tp_fail D) (tp_ran D) (tp_most D) (tp_own D) /\
  (tp_f0 D = 0 -> tp_cap0 D < tp_len0 D + tp_n D + 1 ->
     nth_error (PresetRun.hruns (tp_rp_sm D) (tp_rp_x D) (tp_rp_os D)) (tp_rp_i D) =
     Some (if tp_cap0 D =? 0 then PresetReqAt.HMal (2 * (tp_len0 D + tp_n D + 1))
           else PresetReqAt.HRe (tp_cap0 D) (2 * (tp_len0 D + tp_n D + 1)))) /\
  blocks_bytes (tp_S D) - tp_cap0 D + LIVE_tx <= LIVE_MAX /\ tp_req D < cf_malloc_max /\
  (* the text's hull premise (THE RUN HAS AT MOST 4 CALLS), appended LAST so that the positional reads above keep
     their binders *)
  (length (tp_rp_os D) <= 4)%nat.
(* The batch-kit text's two new premises (PRH_FnTx.v 88468bf162d8), both GUARDED by f0 = 0 (TX-RUNAT-F0): the WILD ROOM for
   this call's own stored traces (one per grow), and the CONSUMER WINDOW over its own run events. Kept out of tp_pre so
   the rows' positional reads of tp_pre do not move; tp_text_of_walk puts them back in the text's order (the same as
   the A' Base). *)
Definition tp_k1pre (D : tp_in) : Prop :=
  (tp_f0 D = 0 -> YCbqGwild.wild_room (as_universe B) [] (tp_evk D) (st_depot (tp_S D))) /\
  (tp_f0 D = 0 -> PRH_Base.prh_cons_from (tp_rp_sm D) (tp_rp_x D) (tp_rp_os D) (tp_rp_i D) (tp_evk D)).
(* The batch-kit post's wild-trace budget (PRH_Base.wbudget_if): at most tp_evk D fresh wild traces, when entered unfailed *)
Definition tp_budget (D : tp_in) (WS : list (list Z)) : Prop := wbudget_if (tp_f0 D) [] (tp_evk D) WS.
Lemma tp_budget_nil : forall D, tp_budget D [].
Proof. intros D _. unfold wbudget, wfresh, wild_fresh. cbn. apply Nat.le_0_l. Qed.

(* THE RUN POSITION, in the two shapes the post conjuncts have (PRH_FnTx.v b6f264e13647 :325-330; the same
   definitions as the A' walk's lib/A/Prog/TxPut102A_Base.v (sha256 54dbf8e9f6e5; internal record), so the two walks keep one shape): keyed on the
   outcome f1, so ONE pair covers the fit, the grow and the refused arm. tp_pos_grow is the position ADVANCED by
   this call's own grow, under the hypothesis that the run's event at rp_i is that grow's (the hypothesis the text owner took
   from this walk's wording); tp_pos_keep is the position UNMOVED, for every outcome that makes no event. *)
Definition tp_pos_grow (D : tp_in) (S' : astate) (f1 : Z) : Prop :=
  tp_f0 D = 0 -> f1 = 0 -> tp_cap0 D < tp_need D ->
  exists hist', PresetRoomPos.iface_room_pos (tp_rp_sm D) (tp_rp_x D) (tp_rp_os D)
    (Datatypes.S (tp_rp_i D)) (tp_rp_H0 D) hist' S'.
Definition tp_pos_keep (D : tp_in) (S' : astate) (f1 : Z) : Prop :=
  ~ (tp_f0 D = 0 /\ f1 = 0 /\ tp_cap0 D < tp_need D) ->
  PresetRoomPos.iface_room_pos (tp_rp_sm D) (tp_rp_x D) (tp_rp_os D) (tp_rp_i D) (tp_rp_H0 D) (tp_rp_hist D) S'.
Definition tp_pos (D : tp_in) (S' : astate) (f1 : Z) : Prop :=
  tp_pos_grow D S' f1 /\ tp_pos_keep D S' f1.

(* ---- the text's post BODY (:315-331), with the regs' argument dropped: it does not occur in the text's body ---- *)
Definition tp_Q (D : tp_in) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
  (mem' : word -> option byte) : Prop :=
  exists b1 cap1 f1 own' (pre : list Z),
  prhtx_post B (tp_Lam D) (tp_regs D) (tp_dw D) (tp_ly D) (tp_S D) (tp_Hp D) ly' S' Hp' W' mem'
    (tp_t D) (tp_b0 D) (tp_cap0 D) b1 (tp_len0 D + Z.of_nat (length pre)) cap1 f1 (tp_txt D ++ pre) /\
  ((tp_f0 D = 0 /\ f1 = 0 /\ own' = tp_own D /\ pre = tp_src D /\ cap1 = tp_cap1 D) \/
   (tp_f0 D <> 0 /\ f1 = tp_f0 D /\ own' = tp_own D /\ pre = [] /\ b1 = tp_b0 D /\ cap1 = tp_cap0 D) \/
   (tp_f0 D = 0 /\ tp_cap0 D < tp_need D /\ f1 = 1 /\ own' = 1 /\ pre = [] /\ b1 = tp_b0 D /\ cap1 = tp_cap0 D /\
    prhtx_refused_at S' /\ rd32 (aview segs (w_H W') mem') (as_errno B) 12)) /\
  (* DEAD-TXPUT (the kit's text): entered unfailed, tx_put returns unfailed *)
  (tp_f0 D = 0 -> f1 = 0) /\
  bytes_at W' mem' (tp_s D) (tp_src D) /\
  room_live_cf S' /\ tp_pos_grow D S' f1 /\ tp_pos_keep D S' f1 /\
  prh_ledger B ly' S' Hp' W' mem' (tp_Lam D) (tp_peak D) (tp_cnt D) (tp_fail D) (tp_ran D) (tp_most D) own'.
Definition tp_Qb (D : tp_in) : alayout -> astate -> list Z -> world segs -> bvmap 5 word ->
  (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' _ mem' _ => tp_Q D ly' S' Hp' W' mem'.
Definition tp_cfg0 (D : tp_in) : config :=
  cfg_at segs (SIGMA AS_tx_put) (tp_regs D) (tp_mem D) (tp_md D).
(* the text's post, written in PRH_Base's R form at wle' segs RZ_cf (fpostWbm IS it: PRH_Base.fpostWbm_R_wle') *)
Definition tp_text_post (D : tp_in) : world segs -> config -> Prop :=
  fpostWbmR B ARcfx SK (wle' segs YGcfRehidePost.RZ_cf) (wbudget_if (tp_f0 D) [] (tp_evk D)) STK_tx_put (tp_dw D)
    (prhtx_fp (tp_t D) (tp_b0 D) (tp_cap0 D)) (tp_regs D)
    (tp_ly D) (tp_S D) (tp_Hp D) (tp_W D) (tp_mem D) (tp_md D) (tp_Qb D).
(* the same post WITHOUT the m-form's memnorm keep (fpostWbR, not fpostWbmR): what the END segment concludes at a
   generic P; the top adds the keep at P := tp_mn D (tp_text_post_of_W below), as the A' walk's interface does *)
Definition tp_text_postW (D : tp_in) : world segs -> config -> Prop :=
  fpostWbR B ARcfx SK (wle' segs YGcfRehidePost.RZ_cf) (wbudget_if (tp_f0 D) [] (tp_evk D)) STK_tx_put (tp_dw D)
    (prhtx_fp (tp_t D) (tp_b0 D) (tp_cap0 D)) (tp_regs D)
    (tp_ly D) (tp_S D) (tp_Hp D) (tp_W D) (tp_mem D) (tp_md D) (tp_Qb D).

(* THE RECORD IS THE TWIN TEXT: a walk of every record whose premises hold is TxPutCall102's ttx_put_specX_ev at
   ARcfx - the kit's ttx_put_specX verbatim with the one named premise tp_live (TxPutCall102.v's header): its conclusion is
   SRr' segs RZ_cf with the post's journal at wle' segs RZ_cf (tp_text_post is fpostWbm, which PRH_Base.v states at
   wle' segs RZ_cf), and its hull premise length rp_os <= 4 follows tp_live (tp_pre carries it last). This lemma
   checks that tp_pre, tp_k1pre and tp_text_post are the twin's, binder for binder; TxPutCall102.ttx_put_specX_of_ev
   carries it to the kit's text. *)
Lemma tp_text_of_walk :
  (forall D, tp_pre D -> tp_k1pre D -> SRr' segs YGcfRehidePost.RZ_cf (tp_W D) (tp_cfg0 D) (tp_text_post D)) ->
  TxPutCall102.ttx_put_specX_ev B ARcfx SK CTX0.
Proof.
intros HW rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch dw t s n b0 len0 cap0 f0 own txt src Lam
  peak cnt fail ran most H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25.
apply (HW (mkTpIn rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch dw t s n b0 len0 cap0 f0 own txt src
   Lam peak cnt fail ran most)).
- unfold tp_pre.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H9|]. split; [exact H10|]. split; [exact H11|]. split; [exact H12|]. split; [exact H13|].
  split; [exact H14|]. split; [exact H15|]. split; [exact H16|]. split; [exact H17|]. split; [exact H18|].
  split; [exact H19|]. split; [exact H20|]. split; [exact H21|]. split; [exact H22|]. split; [exact H23|].
  split; [exact H24|]. split; [exact H25 | exact H6].
- split; [exact H7 | exact H8].
Qed.


(* ---- WHAT EVERY CUT CARRIES ---- *)
(* the widened journal from entry: window STK_tx_put + dw below sp0 + dw, FP the record and the old buffer *)
Definition tp_FP (D : tp_in) : list (Z * Z) := prhtx_fp (tp_t D) (tp_b0 D) (tp_cap0 D).
(* at the wild-trace budget WS (YCbqG.ajournal_xw; WS = [] is ajournal_x): [] up to the GROW's realloc and that
   call's wild trace after it (the batch kit: the trace is wild, inU, so the call's post keeps it in the budget) *)
Definition tp_J (D : tp_in) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world segs)
  (mem3 : word -> option byte) (md3 : Model) (k : Z) (WS : list (list Z)) : Prop :=
  ajournal_xw (SK := SK) segs B prh_pst ARcfx (STK_tx_put + tp_dw D) (tp_sp0 D + tp_dw D) (tp_FP D)
    (tp_ly D) (tp_S D) (tp_Hp D) (tp_W D) (tp_mem D) (tp_md D) [] ly3 S3 Hp3 W3 mem3 md3 k WS.
(* the same journal over a world relation R (YCbqG.ajournal_xwR); tp_J is tp_JR at wle (tp_J_R_wle). tp_J keeps its
   own body because proof lines in the segment files unfold it. The cuts after the GROW's realloc (tp_at_FIT,
   tp_at_END) take it at wle' segs RZ_cf: the realloc frees the old buffer, and a free may hide shadow again *)
Definition tp_JR (R : world segs -> world segs -> Prop) (D : tp_in) (ly3 : alayout) (S3 : astate) (Hp3 : list Z)
  (W3 : world segs) (mem3 : word -> option byte) (md3 : Model) (k : Z) (WS : list (list Z)) : Prop :=
  ajournal_xwR (SK := SK) segs B prh_pst ARcfx R (STK_tx_put + tp_dw D) (tp_sp0 D + tp_dw D) (tp_FP D)
    (tp_ly D) (tp_S D) (tp_Hp D) (tp_W D) (tp_mem D) (tp_md D) [] ly3 S3 Hp3 W3 mem3 md3 k WS.
Lemma tp_J_R_wle : forall D ly3 S3 Hp3 W3 mem3 md3 k WS,
  tp_J D ly3 S3 Hp3 W3 mem3 md3 k WS = tp_JR (@wle segs) D ly3 S3 Hp3 W3 mem3 md3 k WS.
Proof. reflexivity. Qed.
(* the walk's own keep relative to the entry state, over the window it may disturb: STK_tx_put below sp0 - its own
   frame 112 PLUS the stack a callee may use. The A' GROW row's finding (14:5xZ): with a window of 112 this predicate is
   FALSE at the FIT and NULL cuts, because after the realloc (A' +192 / B' +200) and the __asan_memcpy (A' +288 / B' +316) the callee scratch
   [sp0 - STK_tx_put, sp0 - 112) is not kept - realloc_leaf_x / acall_kept_x / aj_intrin_at_x all exempt it through
   ascratch / ESTACK - and cj_kept_trans cannot repair it (it asks sp1 - STK1 <= sp2 - STK2). STK_tx_put is also the
   window YCbqGcallW.fpostW_x_of_kept takes at the return, so END is unchanged. Written cells OR: the record's 28
   bytes and the old buffer, both in FP. *)
Definition tp_OR (D : tp_in) : list (Z * Z) := tp_FP D.
Definition tp_K (D : tp_in) (ly3 : alayout) (S3 : astate) (W3 : world segs) (mem3 : word -> option byte)
  (md3 : Model) : Prop :=
  cj_kept (SK := SK) segs B prh_pst STK_tx_put (tp_sp0 D) (tp_OR D) (tp_FP D)
    (tp_ly D) (tp_S D) (tp_W D) (tp_mem D) (tp_md D) ly3 S3 W3 mem3 md3.
(* the same keep over R (YCbqGcallW.cj_keptR); tp_K is tp_KR at wle (tp_K_R_wle), and keeps its own body because
   proof lines unfold it. Its world conjunct is the journal's, so after the realloc it holds at wle' segs RZ_cf only *)
Definition tp_KR (R : world segs -> world segs -> Prop) (D : tp_in) (ly3 : alayout) (S3 : astate) (W3 : world segs)
  (mem3 : word -> option byte) (md3 : Model) : Prop :=
  cj_keptR (SK := SK) segs B prh_pst R STK_tx_put (tp_sp0 D) (tp_OR D) (tp_FP D)
    (tp_ly D) (tp_S D) (tp_W D) (tp_mem D) (tp_md D) ly3 S3 W3 mem3 md3.
Lemma tp_K_R_wle : forall D ly3 S3 W3 mem3 md3,
  tp_K D ly3 S3 W3 mem3 md3 = tp_KR (@wle segs) D ly3 S3 W3 mem3 md3.
Proof. reflexivity. Qed.
(* gp and tp, the only registers tx_put never writes and never restores *)
Definition tp_kregs (D : tp_in) (regs3 : bvmap 5 word) : Prop :=
  forall r : bv 5, In r [3; 4]%bv -> getr regs3 r = getr (tp_regs D) r.
(* the prologue's thirteen saved words, at sp0 - 8 .. sp0 - 104 *)
Definition tp_saved (D : tp_in) (W3 : world segs) (mem3 : word -> option byte) : Prop :=
  val_mem segs (rdW W3 mem3) (tp_sp0 D - 8) 8 (raZ (tp_regs D)) /\
  val_mem segs (rdW W3 mem3) (tp_sp0 D - 16) 8 (bv_unsigned (getr (tp_regs D) 8)) /\
  val_mem segs (rdW W3 mem3) (tp_sp0 D - 24) 8 (bv_unsigned (getr (tp_regs D) 9)) /\
  val_mem segs (rdW W3 mem3) (tp_sp0 D - 32) 8 (bv_unsigned (getr (tp_regs D) 18)) /\
  val_mem segs (rdW W3 mem3) (tp_sp0 D - 40) 8 (bv_unsigned (getr (tp_regs D) 19)) /\
  val_mem segs (rdW W3 mem3) (tp_sp0 D - 48) 8 (bv_unsigned (getr (tp_regs D) 20)) /\
  val_mem segs (rdW W3 mem3) (tp_sp0 D - 56) 8 (bv_unsigned (getr (tp_regs D) 21)) /\
  val_mem segs (rdW W3 mem3) (tp_sp0 D - 64) 8 (bv_unsigned (getr (tp_regs D) 22)) /\
  val_mem segs (rdW W3 mem3) (tp_sp0 D - 72) 8 (bv_unsigned (getr (tp_regs D) 23)) /\
  val_mem segs (rdW W3 mem3) (tp_sp0 D - 80) 8 (bv_unsigned (getr (tp_regs D) 24)) /\
  val_mem segs (rdW W3 mem3) (tp_sp0 D - 88) 8 (bv_unsigned (getr (tp_regs D) 25)) /\
  val_mem segs (rdW W3 mem3) (tp_sp0 D - 96) 8 (bv_unsigned (getr (tp_regs D) 26)) /\
  val_mem segs (rdW W3 mem3) (tp_sp0 D - 104) 8 (bv_unsigned (getr (tp_regs D) 27)).
(* the carry: the entry's premises, the journal and the keep from entry, the kept and saved registers, the frame
   pointer, Hp, and the read-only view (it rides through the journal's image clause) *)
Definition tp_carry (D : tp_in) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world segs)
  (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) (k : Z) (WS : list (list Z)) : Prop :=
  tp_pre D /\ tp_J D ly3 S3 Hp3 W3 mem3 md3 k WS /\ tp_K D ly3 S3 W3 mem3 md3 /\ tp_kregs D regs3 /\
  spZ regs3 = tp_sp0 D - TP_FRAME /\ tp_saved D W3 mem3 /\ Hp3 = tp_Hp D /\
  arodata_okP segs (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview segs (w_H W3) mem3).
(* the same carry over R (the journal tp_JR R and the keep tp_KR R); tp_carry is tp_carryR at wle (tp_carry_R_wle):
   the GROW cut, before the realloc, keeps tp_carry; the cuts after it take tp_carryR at wle' segs RZ_cf *)
Definition tp_carryR (R : world segs -> world segs -> Prop) (D : tp_in) (ly3 : alayout) (S3 : astate) (Hp3 : list Z)
  (W3 : world segs) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) (k : Z) (WS : list (list Z))
  : Prop :=
  tp_pre D /\ tp_JR R D ly3 S3 Hp3 W3 mem3 md3 k WS /\ tp_KR R D ly3 S3 W3 mem3 md3 /\ tp_kregs D regs3 /\
  spZ regs3 = tp_sp0 D - TP_FRAME /\ tp_saved D W3 mem3 /\ Hp3 = tp_Hp D /\
  arodata_okP segs (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview segs (w_H W3) mem3).
Lemma tp_carry_R_wle : forall D ly3 S3 Hp3 W3 regs3 mem3 md3 k WS,
  tp_carry D ly3 S3 Hp3 W3 regs3 mem3 md3 k WS = tp_carryR (@wle segs) D ly3 S3 Hp3 W3 regs3 mem3 md3 k WS.
Proof. reflexivity. Qed.
(* the shadow registers the body keeps live: s6 = the shadow base, s0 = t and the three checked offsets *)
Definition tp_shregs (D : tp_in) (regs3 : bvmap 5 word) : Prop :=
  getr regs3 22 = w64 SHADOW_OFF /\ getr regs3 8 = w64 (tp_t D) /\
  getr regs3 9 = w64 (tp_n D) /\ getr regs3 18 = w64 (tp_s D).
(* the state of the record and the buffer at a cut, with the buffer's capacity and base possibly moved *)
Definition tp_recat (D : tp_in) (W3 : world segs) (mem3 : word -> option byte) (b1 len1 cap1 f1 : Z) : Prop :=
  prhtx_rec W3 mem3 (tp_t D) b1 len1 cap1 f1.
(* the buffer's block facts WITHOUT its bytes (the bytes differ between the fit and the grow arm) *)
Definition tp_blk (D : tp_in) (ly3 : alayout) (S3 : astate) (W3 : world segs) (mem3 : word -> option byte)
  (b1 cap1 : Z) : Prop :=
  0 < cap1 /\ In (b1, cap1) (ablocks B ly3 S3) /\ 4096 <= b1 /\ b1 + cap1 + 8 <= YM05.alloc_ceiling /\
  amem_range b1 cap1 /\
  (forall a, b1 <= a < b1 + cap1 -> writable_at segs (rdW W3 mem3) a) /\
  range_addressable (aview segs (w_H W3) mem3) SHADOW_OFF b1 cap1 /\
  shadow_hull_vis (aview segs (w_H W3) mem3) b1 cap1 /\
  (forall a k, In (a, k) (tp_Lam D) -> a - cf_head <> b1).
(* what the ledger, the source window, the own cell and the room say at a cut (the run position is stated per cut:
   GROW is at the entry state, FIT and NULL carry tp_pos) *)
Definition tp_side (D : tp_in) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world segs)
  (mem3 : word -> option byte) (own3 : Z) : Prop :=
  prh_ledger B ly3 S3 Hp3 W3 mem3 (tp_Lam D) (tp_peak D) (tp_cnt D) (tp_fail D) (tp_ran D) (tp_most D) own3 /\
  src_rd W3 mem3 (tp_s D) (tp_src D) /\ room_live_cf S3.

(* ---- THE CUTS ---- *)
(* TP_PC_GROW (+180): failed was 0 and the buffer does not fit; a0 = t->b is not yet loaded, a1 = need, a2 = cap0;
   the state is the entry's but for tx_put's own frame *)
Definition tp_at_GROW (D : tp_in) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world segs)
  (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) (k : Z) : Prop :=
  tp_k1pre D /\ tp_carry D ly3 S3 Hp3 W3 regs3 mem3 md3 k [] /\ tp_shregs D regs3 /\
  tp_f0 D = 0 /\ tp_cap0 D < tp_need D /\
  ly3 = tp_ly D /\ S3 = tp_S D /\
  getr regs3 11 = w64 (tp_need D) /\ getr regs3 12 = w64 (tp_cap0 D) /\
  getr regs3 19 = w64 (tp_t D + 8) /\ getr regs3 21 = w64 (tp_t D + 16) /\ getr regs3 20 = w64 (tp_t D + 24) /\
  getr regs3 23 = w64 (SHADOW_OFF + (tp_t D + 8) / 8) /\ getr regs3 25 = w64 (SHADOW_OFF + (tp_t D + 16) / 8) /\
  getr regs3 24 = w64 (SHADOW_OFF + (tp_t D + 24) / 8) /\ getr regs3 26 = w64 (tp_t D / 8) /\
  tp_recat D W3 mem3 (tp_b0 D) (tp_len0 D) (tp_cap0 D) 0 /\
  prhtx_inv B (tp_Lam D) ly3 S3 W3 mem3 (tp_b0 D) (tp_len0 D) (tp_cap0 D) (tp_txt D) /\
  prhtx_trace B ly3 W3 mem3 (tp_t D) /\
  tp_side D ly3 S3 Hp3 W3 mem3 (tp_own D).
(* TP_PC_FIT (+256): the rejoin. The record holds (b1, len0, cap1, 0), the buffer holds txt in its first len0 bytes
   and has room for n + 1 more; the arm says whether the buffer moved (FIT: not; GROW-OK: the realloc's result). A
   post-call cut: its carry is at wle' segs RZ_cf *)
Definition tp_fitarm (D : tp_in) (ly3 : alayout) (S3 : astate) (b1 cap1 : Z) : Prop :=
  (tp_need D <= tp_cap0 D /\ b1 = tp_b0 D /\ cap1 = tp_cap0 D /\ ly3 = tp_ly D /\ S3 = tp_S D) \/
  (tp_cap0 D < tp_need D /\ cap1 = tp_req D /\
   prhtx_grow B (tp_ly D) (tp_S D) ly3 S3 (tp_b0 D) (tp_cap0 D) b1 cap1 /\
   blocks_bytes S3 <= blocks_bytes (tp_S D) + cap1 - tp_cap0 D).
Definition tp_at_FIT (D : tp_in) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world segs)
  (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) (k b1 cap1 : Z) : Prop :=
  exists WS, tp_budget D WS /\
  tp_carryR (wle' segs YGcfRehidePost.RZ_cf) D ly3 S3 Hp3 W3 regs3 mem3 md3 k WS /\ tp_shregs D regs3 /\
  tp_f0 D = 0 /\
  getr regs3 19 = w64 (tp_t D + 8) /\ getr regs3 21 = w64 (tp_t D + 16) /\
  getr regs3 23 = w64 (SHADOW_OFF + (tp_t D + 8) / 8) /\ getr regs3 25 = w64 (SHADOW_OFF + (tp_t D + 16) / 8) /\
  getr regs3 26 = w64 (tp_t D / 8) /\
  tp_recat D W3 mem3 b1 (tp_len0 D) cap1 0 /\
  tp_blk D ly3 S3 W3 mem3 b1 cap1 /\ bytes_at W3 mem3 b1 (tp_txt D) /\
  tp_need D <= cap1 /\
  (forall a, tp_s D <= a < tp_s D + tp_n D -> ~ (b1 <= a < b1 + cap1)) /\
  prhtx_kept B (tp_Lam D) ly3 S3 (tp_s D) (tp_n D) /\
  tp_fitarm D ly3 S3 b1 cap1 /\
  tp_side D ly3 S3 Hp3 W3 mem3 (tp_own D) /\ tp_pos D S3 0.
(* TP_PC_END (+400): the text's post body already holds at this state; the epilogue only restores and returns. A
   post-call cut: its carry is at wle' segs RZ_cf *)
Definition tp_at_END (D : tp_in) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world segs)
  (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) (k : Z) : Prop :=
  exists WS, tp_budget D WS /\
  tp_carryR (wle' segs YGcfRehidePost.RZ_cf) D ly3 S3 Hp3 W3 regs3 mem3 md3 k WS /\ tp_Q D ly3 S3 Hp3 W3 mem3.

(* the machine configuration at a cut of the function *)
Definition tp_cfg (o : Z) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) : config :=
  mkCfg (YK11.mkst regs3 (Z_to_bv 64 (tp_pc o)) mem3 (YK11.seg_rom segs)) md3.
(* a segment's post: the final post Q, and the invariant P at the end memory *)
Definition tp_QP (P : (word -> option byte) -> Prop) (Q : world segs -> config -> Prop) : world segs -> config -> Prop :=
  fun W' c' => Q W' c' /\ P (ms_mem (cfg_ms c')).

(* ---- THE SEGMENT STATEMENTS (generic P, generic final post Q; continuation form). The GROW segment's realloc frees
   the old buffer, so a run that reaches a cut after it ends at wle' segs RZ_cf: the continuations at the post-call
   cuts (tp_k_FIT, tp_k_END) and the segments conclude SRr' segs RZ_cf. The continuation at the pre-call GROW cut has
   the generic form tp_k_GROWR R (tp_k_GROW is it at wle); S0 takes it at wle' segs RZ_cf ---- *)
Section segs. Variable P : (word -> option byte) -> Prop.
Definition tp_k_GROWR (R : world segs -> world segs -> Prop) (Q : world segs -> config -> Prop) (D : tp_in) : Prop :=
  forall ly3 S3 Hp3 W3 regs3 mem3 md3 k,
    tp_at_GROW D ly3 S3 Hp3 W3 regs3 mem3 md3 k -> P mem3 ->
    SRrG segs R W3 (tp_cfg TP_PC_GROW regs3 mem3 md3) (tp_QP P Q).
Definition tp_k_GROW (Q : world segs -> config -> Prop) (D : tp_in) : Prop := tp_k_GROWR (@wle segs) Q D.
Lemma tp_k_GROW_R_wle : forall Q D, tp_k_GROW Q D = tp_k_GROWR (@wle segs) Q D.
Proof. reflexivity. Qed.
Definition tp_k_FIT (Q : world segs -> config -> Prop) (D : tp_in) : Prop :=
  forall ly3 S3 Hp3 W3 regs3 mem3 md3 k b1 cap1,
    tp_at_FIT D ly3 S3 Hp3 W3 regs3 mem3 md3 k b1 cap1 -> P mem3 ->
    SRr' segs YGcfRehidePost.RZ_cf W3 (tp_cfg TP_PC_FIT regs3 mem3 md3) (tp_QP P Q).
Definition tp_k_END (Q : world segs -> config -> Prop) (D : tp_in) : Prop :=
  forall ly3 S3 Hp3 W3 regs3 mem3 md3 k,
    tp_at_END D ly3 S3 Hp3 W3 regs3 mem3 md3 k -> P mem3 ->
    SRr' segs YGcfRehidePost.RZ_cf W3 (tp_cfg TP_PC_END regs3 mem3 md3) (tp_QP P Q).

(* S0 (+0 -> +332 / +248 / +172): the prologue, the shadow base, the 4-byte check of t + 24 and the FAILED test
   (A0 goes straight to the epilogue with the text's post body already true), the checks of t + 8 / t + 16, the
   need test *)
Definition tp_seg_S0 : Prop :=
  forall Q D, tp_pre D -> tp_k1pre D -> tp_img ->
  tp_k_END Q D -> tp_k_FIT Q D -> tp_k_GROWR (wle' segs YGcfRehidePost.RZ_cf) Q D ->
  P (ms_mem (cfg_ms (tp_cfg0 D))) ->
  SRr' segs YGcfRehidePost.RZ_cf (tp_W D) (tp_cfg0 D) (tp_QP P Q).
(* S_GROW (+172 -> +248 / +392): the load check of t, the realloc wrapper call (cap0 > 0: the rule over R,
   YGcallRkKeep.aj_realloc_at_x_cfR_keep; cap0 = 0: YGcallRxKeep.aj_realloc_null_at_x_keep), the NULL test, and on
   success the two stores of t->b and t->cap *)
Definition tp_seg_GROW : Prop :=
  forall Q D ly3 S3 Hp3 W3 regs3 mem3 md3 k,
  tp_at_GROW D ly3 S3 Hp3 W3 regs3 mem3 md3 k -> tp_img ->
  tp_k_FIT Q D -> P mem3 ->
  SRr' segs YGcfRehidePost.RZ_cf W3 (tp_cfg TP_PC_GROW regs3 mem3 md3) (tp_QP P Q).
(* S_FIT (+248 -> +332): the two load checks, __asan_memcpy (b1 + len0, s, n), t->n := len0 + n, the 1-byte store
   check and the NUL store; the DONE post body at the end state *)
Definition tp_seg_FIT : Prop :=
  forall Q D ly3 S3 Hp3 W3 regs3 mem3 md3 k b1 cap1,
  tp_at_FIT D ly3 S3 Hp3 W3 regs3 mem3 md3 k b1 cap1 -> tp_img ->
  tp_k_END Q D -> P mem3 ->
  SRr' segs YGcfRehidePost.RZ_cf W3 (tp_cfg TP_PC_FIT regs3 mem3 md3) (tp_QP P Q).
(* S_END (+400 -> ret +456): the thirteen restores, `addi sp, sp, 112` and ret; the text's caller-window post without the
   memnorm keep (tp_text_postW): at a generic P the keep is not provable; the top adds it at P := tp_mn D *)
Definition tp_seg_END : Prop :=
  forall D ly3 S3 Hp3 W3 regs3 mem3 md3 k,
  tp_at_END D ly3 S3 Hp3 W3 regs3 mem3 md3 k -> tp_img -> P mem3 ->
  SRr' segs YGcfRehidePost.RZ_cf W3 (tp_cfg TP_PC_END regs3 mem3 md3) (tp_QP P (tp_text_postW D)).
End segs.

(* ---- THE GROW ROW'S CLOSING STATEMENT: the realloc WRAPPER's callee texts at the listing's own entry
   SIGMA AS___wrap_realloc are named premises of the statement, BEFORE P. realloc(p, n) frees the old block inside the
   call, so its text is the cf layer's PRIMED row with room and the memnorm keep,
   YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep (run amreal' segs RZ_cf, leaf realloc_leaf_cf_rh with the keep,
   entry room ROOM_cf_k S (RK_realloc + k), entry headroom cf_hull_adm S n), for every headroom k: the text the rule
   over R YGcallRkKeep.aj_realloc_at_x_cfR_keep takes. realloc(NULL, n) frees nothing: its text is
   YGcfReallocComposeKeep.arealloc_null_realizes_cf_keep, the text YGcallRxKeep.aj_realloc_null_at_x_keep takes
   (through YGcallRxKeep.arealloc_null_realizes_x_cf_keep). The walk reads the keep after the call (srr_inv_call
   carries P across it). TxPut102B_Top.v takes them as named Variables, to be discharged from the instance's
   allocator rows. ---- *)
Definition tp_AREAL : Prop :=
  forall Hp k, YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep segs B Hp (SIGMA AS___wrap_realloc) k.
Definition tp_AREALN : Prop :=
  forall Hp, YGcfReallocComposeKeep.arealloc_null_realizes_cf_keep segs B Hp (SIGMA AS___wrap_realloc).
(* ARX_DEPOT: the depot of every ARcfx state has no repeats, which the batch kit admission at the call needs
   (YCbqGwild.wild_room_admits's NoDup premise). It is AR_laws_x's field 25 (YCbqG.v ARx_depot_nodup_law) at ARcfx:
   the statement keeps it as a binder, and TxPut102B_Inst.v gives it as the field's projection alx_depot_nodup of the
   cf laws. The same as the A' Base. *)
Definition tp_ARX_DEPOT : Prop := forall ly S Hp W mem md, ARcfx ly S Hp W mem md -> List.NoDup (st_depot S).
Definition tp_seg_GROW_stmt : Prop :=
  forall (AREAL : forall Hp k, YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep segs B Hp (SIGMA AS___wrap_realloc) k)
         (AREALN : forall Hp, YGcfReallocComposeKeep.arealloc_null_realizes_cf_keep segs B Hp (SIGMA AS___wrap_realloc))
         (ARX_DEPOT : forall ly S Hp W mem md, ARcfx ly S Hp W mem md -> List.NoDup (st_depot S))
         (P : (word -> option byte) -> Prop),
  srr_inv_laws segs P -> srr_inv_call segs P -> tp_seg_GROW P.

(* the instantiation at the top: the memnorm keep from the entry memory (YSRrMemnorm's carriers) pays fpostWm's
   memnorm conjunct *)
Definition tp_mn (D : tp_in) (m : word -> option byte) : Prop :=
  YAkMemnorm.memnorm segs (tp_mem D) -> YAkMemnorm.memnorm segs m.
Lemma tp_mn_laws : forall D, srr_inv_laws segs (tp_mn D).
Proof. intros D. exact (srr_inv_laws_imp segs (YAkMemnorm.memnorm segs) (tp_mem D) (srr_inv_laws_memnorm_k segs)). Qed.
Lemma tp_mn_call : forall D, srr_inv_call segs (tp_mn D).
Proof. intros D. exact (srr_inv_call_imp segs (tp_mem D)). Qed.
Lemma tp_mn_refl : forall D, tp_mn D (tp_mem D).
Proof. intros D H. exact H. Qed.
(* the top's last step: the END segment's post at P := tp_mn D is the text's m-form post *)
Lemma tp_text_post_of_W : forall D W' c', tp_QP (tp_mn D) (tp_text_postW D) W' c' -> tp_text_post D W' c'.
Proof.
intros D W' c' [(ly' & S' & Hp' & regs' & mem' & md' & k & WS & Ec & HPW & HJ & HK & HP & HQ) HM].
exists ly', S', Hp', regs', mem', md', k, WS. split; [exact Ec|]. split; [exact HPW|]. split; [exact HJ|].
split; [exact HK|]. split; [exact HP|]. split; [exact HQ|]. subst c'. exact HM.
Qed.
End tp.
Print Assumptions tp_text_of_walk.
Print Assumptions tp_text_post_of_W.
