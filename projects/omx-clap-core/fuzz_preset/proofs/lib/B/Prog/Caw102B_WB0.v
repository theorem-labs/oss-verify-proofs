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
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PjGetB.v, with its module paths and module names changed; 221 of its 280 lines of code are new or changed and 1707 lines of the source are left out. *)
(* fuzz_preset, image B' (asan-ubsan, harness fix #102): segment WB0 of the walk of check_as_written, the Entry
   (B' 0x81f78 -> 0x81fbc, call-free): the prologue, the struct ex's first three words and the two UBSan
   pointer-overflow branches, up to the jal of __wrap_malloc (CAWB_MAL, WB1's entry), in the continuation form of
   lib/B/Prog/Caw102B.v (lane CawB102 of a Theorem Labs lane; plan, the internal file PLAN-cno-caw-102.md section 5.4; re-proved on the Batch-2
   ledger base by CawDWB0, on the f97c re-keyed base by CawGWB0, lane CawA102R for B').
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).
   rule-24 CONFIRM: a Theorem Labs checker (the rule-24 lookup record), plan, the internal file PLAN-cno-caw-102.md section 2: proof-index lookup
   check_as_written rc=0, no walk keyed to B' caw 0x81f78 or the #102 pins.
   BASE OF RECORD (statements, not edited here): the kit's cut
   (ready for the #102 integration: the cut + this row's caw B' files; prepared at the batch-prep base on the batch
   tip), this row's lib/B/Prog/Caw102B.v (its statements: caw_pre and its
   projections caw_pre_*, cut_mal, caw_base, caw_prog, caw_prog_entry, caw_ledger, caw_K_mal, caw_hblock, caw_req);
   the cut's kit texts: lib/A/PRH_FnCheck.v c40cf3fdcd2a (tcheck_as_written_specX :832-902, ck_frm0), lib/A/PRH_Base.v
   (fpre with frm_zero (fp_csr fx) last, unchanged; prh_ledger .. ran most own, prh_pst, prh_run_at),
   the P'' journal of lib/Reusable/YCbqG.v (built here by ajournal_x_init, never destructed). Every base
   name with an implicit float state in a statement of this file gets the entry's, `(fx := fx)`.
   WHAT CHANGED (the batch-prep base, the batch tip), and why: the batch text has no run-word list DW (the base
   dropped cawB's c_DW; this segment never read it) and takes the ROOM COUNTS `sec_cnt S <= LSEC + DRV`, `ccnt24 S
   <= L24 + DRV` as entry premises after room_live_cf (:862-863); with the hull budget and HPOS after them caw_pre now has 27
   conjuncts (Caw102B.v:139-165) and ck_frm0 moved by four places, 23rd to 27th: the old positional destruct of caw_pre would mis-bind. HOW here: caw_pre is read BY NAME, one base
   projection per premise (caw_pre_fpre .. caw_pre_room, caw_pre_frm0), under the old hypothesis names; the two
   count premises are not read (this segment makes no malloc or free). caw_WB0's statement is unchanged.
   EARLIER (the re-keyed base): that base's tcheck_as_written_specX binds no run position at entry and
   states the position in the post-implication form, so the base dropped cawB's c_sm / c_rx / c_os / c_i / c_H0 /
   c_hist and caw_pre's run-events (caw_room_evs) and room-position (iface_room_pos) premises, and cut_mal carries the
   progress fact `caw_prog C [] S3` in place of the exact entry position: it is the base's caw_prog_entry C (the
   prologue makes no event and keeps the allocator state, S3 = c_S C, so any entry position i is a position i + 0 of
   S3). K0-FRM0-ENTRY: fpre gains frm_zero (fp_csr fx) last; the destruct of fpre names it (HFRM0); this segment is
   call-free and builds no callee fpre, and caw_base's frm_zero (fp_csr fx) at the cut takes caw_pre's ck_frm0 (HFRM).
   EARLIER (base dc2529c4c8b2, K0's Batch 2): caw_pst is removed; cut_mal ends in `caw_ledger C ly3 S3 Hp3 W3 mem3 0`
   (prh_ledger .. (c_ran C) (c_most C) 0), carried over the prologue by prh_ledger_kept_aview (S1Ledger.v): the aview
   of every prh_pst byte (g_most and g_own_ran_out among them) and of every Lam head at the cut is the entry's (KST,
   KO: the prologue writes only the frame [sp0 - 80, sp0); the statics lie below alloc_ceiling, caw_pst_low; the heads
   lie in entry blocks above 4096).
   INPUTS, BY PATH (the cut's): the engine s1b of int102 (8a01e111a410): YC1fPx.v 7814b594066f (paj_run_to_x_inv,
   paj_run_to_tok_x_inv), YC80x.v 14f84f225e8f (srr_inv_laws); lib/A/Prog/S1Ledger.v 8cf15eeb6311
   (prh_ledger_kept_aview :736); lib/B/PRH_ImgB.v 3216eca68342 (prh_img_B); lib/B/Listing_prog.v c97cc46b3e13.
   SECTION HYPOTHESES (owners): Hent, the image fact SIGMA AS_check_as_written = BASE + AF_cawB (discharged at
   PI_prog_B by the instantiation, h-mani-a2's IMG_TOP_B; the same Hent as Caw102B_Top.v). No other, and no new one.
   THE PROOF: the entry seat (cawB_entry, the pattern of PjGetB.v gs_entryB / the old CawB_Walk.v caw_entry_st_ok):
   the 80-byte frame below sp0 (atom 2) writable from fpre's window, the facts 2 ^ 46 <= sp0 <= 2 ^ 47 (16-aligned),
   1 <= data <= 2 ^ 62, 0 <= size <= 3 * 2 ^ 20; the journal ajournal_x_init; P at entry. Two runs of
   paj_run_to_tok_x_inv toward AF_cawB + CAWB_MAL, P kept by the runner (generic P, never instantiated):
     +0 .. +28 (stops at the bltu, undecided);
     +32 `bltu a2, a0` (a2 = data + size) to the trap 0x8207c: REFUTED by a branch step (paj_branch): data + size
       <u data is false from 0 <= size and data + size < 2 ^ 62 (caw_pre);
     +36 .. +64: `beqz a0` at +52 (a0 = snez data xor seqz (data + size)) to the trap 0x8207c: REFUTED by the engine
       (decided not taken) from atom 10's fact 1 <= data and the condition data + size >=u data the bltu step added;
     the state at +68 read back (caw_slot / cawB_reg_at / cawB_sp_at), the ledger at (c_most C) 0 kept by
     prh_ledger_kept_aview (the only writes are the frame [sp0 - 80, sp0); the statics and the harness heads lie
     below alloc_ceiling), the progress fact caw_prog_entry, and the continuation caw_K_mal applied at cut_mal.
   Numerals: 80 (LENGTH: the frame, CAWB_FRAME), 8 / 16 / 24 / 32 / 56 / 64 / 72 (LENGTH: the frame's words below
   sp0, read on the listing), 16 (DERIVED: cf_head), 2 ^ 46 / 2 ^ 47 (DERIVED: stack bounds), 2 ^ 62 / 3 * 2 ^ 20
   (the text's data / size bounds), register and atom numbers (WORD). No ADDRESS: the pc of the cut is
   AF_cawB + CAWB_MAL, the stop of the runs. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnEx PRH_FnAlloc PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_StepKit S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Caw102B.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YI5b.
#[global] Remove Hints YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the entry seat: the 80-byte frame below the entry sp (atom 2), no cell read before the prologue writes it; the
   facts: sp (atom 2), data (atom 10), size (atom 11) ---- *)
Definition cawB_rs0 : smem := [YP09.mkRegion (Some 2%nat) (- CAWB_FRAME) 0 (- CAWB_FRAME) 0 []].
Definition cawB_G0 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 1 (2 ^ 62) 0); (11%nat, mkAF 0 (3 * 2 ^ 20) 0)] [] [].
Definition ss_cawB0 : sstate := mkSS AF_cawB sr_atoms cawB_rs0 None cawB_G0.
Definition cawB_span : Z * Z := (0, 0).

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

Definition cawB_E (regs : bvmap 5 word) : env := @Eimg _ B_prog_listing PA (Ereg regs []).
Lemma cawB_E_reg : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (cawB_E regs) n = getr regs r.
Proof.
intros regs n r Hn. pose proof (u5_range r) as Hu. unfold cawB_E.
rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ n r Hn).
Qed.
(* the write premise of a stretch: its one write window is the frame [sp0 - 80, sp0) (atom 2 = sp0), inside the
   function's stack [sp0 - STK, sp0) *)
Ltac caw_awr Usp :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc ly' own') end;
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0);
  [ reflexivity | rewrite Z.add_0_r; exact Usp | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil ].
(* drop each zcanon whose argument is in range, innermost first (PjGetB.v pgl_zc) *)
Ltac caw_zc H :=
  repeat match type of H with context [zcanon ?x] => rewrite (zcanon_id x) in H by (unfold M64; lia) end.
Ltac caw_zcg := repeat match goal with |- context [zcanon ?x] => rewrite (zcanon_id x) by (unfold M64; lia) end.
(* a chunk in a concrete list *)
Ltac caw_in := cbn [In]; repeat (first [left; reflexivity | right]).
(* the write windows of a stretch's regions lie in the frame [sp0 - 80, sp0) *)
Ltac caw_win Usp :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr); vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr;
    unfold CAWB_FRAME; lia|]);
  destruct Hin.

(* alloc.c's statics (prh_img_B's generated addresses) lie below YM05.alloc_ceiling (PjGetB.v gs_pst_lowB) *)
Lemma caw_pst_low : forall a, Exists (in_zr a) (@prh_pst prh_img_B) -> 0 <= a < YM05.alloc_ceiling.
Proof.
intros a H. apply Exists_exists in H as (r & Hin & Hr). pose proof asan_consts as (C1 & _).
vm_compute in Hin. unfold in_zr in Hr.
repeat (destruct Hin as [<- | Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin.
Qed.
(* a stretch whose write windows lie inside [lo, hi) keeps every view outside it (S6PjCommon.v gs_keep_out) *)
Lemma caw_keep_out : forall E' rs (Wx : world SEGS) m m' lo hi,
  frame_of E' rs (mrestrict (w_H Wx) m) (mrestrict (w_H Wx) m') ->
  (forall a, in_wrange E' rs a -> lo <= a < hi) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H Wx) m' a = aview SEGS (w_H Wx) m a.
Proof.
intros E' rs Wx m m' lo hi HF Hw a Ha Hn.
unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. intros Hin. apply Hn. exact (Hw a Hin).
Qed.
(* a register of a state over the entry env: the entry register its atom names *)
Lemma cawB_reg_at : forall (H : word -> bool) ss ms regs (r : bv 5) n (r' : bv 5),
  st_ok_pi SEGS VAL (cawB_E regs) ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 ->
  Z.of_nat n = bv_unsigned r' -> getr (ms_regs ms) r = getr regs r'.
Proof.
intros H ss ms regs r n r' HS Hsr Hn.
rewrite (st_ok_pi_restrict_reg (PI := PA) H _ ss ms r HS), Hsr. cbn [sv_denot].
rewrite (cawB_E_reg regs n r' Hn), Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.
(* sp of a state whose sp is the entry sp - 80 *)
Lemma cawB_sp_at : forall (H : word -> bool) ss ms regs,
  st_ok_pi SEGS VAL (cawB_E regs) ss (restrict H ms) -> sr_get (ss_regs ss) 2%bv = SOff 2 (- CAWB_FRAME) ->
  CAWB_FRAME <= spZ regs -> spZ (ms_regs ms) = spZ regs - CAWB_FRAME.
Proof.
intros H ss ms regs HS Hsr Hsp. unfold spZ at 1.
rewrite (st_ok_pi_restrict_reg (PI := PA) H _ ss ms 2%bv HS), Hsr.
change (bv_unsigned (sv_denot (cawB_E regs) (SOff 2 (- CAWB_FRAME)))) with (U (cawB_E regs) (SOff 2 (- CAWB_FRAME))).
rewrite U_SOff, (cawB_E_reg regs 2 2%bv eq_refl). unfold CAWB_FRAME in *.
assert (R : 0 <= bv_unsigned (getr regs 2%bv) < 2 ^ 64) by exact (bv_unsigned_in_range 64 _).
unfold spZ in *. unfold zcanon, M64. apply Z.mod_small. lia.
Qed.
(* a word of the frame region (atom 2 = sp0, [sp0 - 80, sp0)) of a state *)
Lemma caw_slot : forall (H : word -> bool) E ss ms cs,
  st_ok_pi SEGS VAL E ss (restrict H ms) ->
  nth_error (ss_mem ss) 0 = Some (YP09.mkRegion (Some 2%nat) (- CAWB_FRAME) 0 (- CAWB_FRAME) 0 cs) ->
  forall od e v, In (YP09.mkChunk od (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS (mrestrict H (ms_mem ms)) (bv_unsigned (ew E 2) + od) 8 v.
Proof.
intros H E ss ms cs HS Hn od e v Hin He Hv.
assert (Hn' : nth_error (ss_mem (abs_ss VAL ss)) 0 =
  Some (YP09.mkRegion (Some 2%nat) (- CAWB_FRAME) 0 (- CAWB_FRAME) 0 cs)) by (destruct ss; exact Hn).
pose proof (st_ok_region_nth SEGS E (abs_ss VAL ss) (restrict H ms) 0 _ HS Hn') as RG.
exact (slot_of_region SEGS E _ _ cs _ _ _ _ od e v RG eq_refl Hin He Hv).
Qed.

Lemma cawB_entry : forall (W : world SEGS) regs mem data size,
  (forall a, spZ regs - CAWB_FRAME <= a < spZ regs -> apresent (w_H W) mem a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  getr regs 10 = w64 data -> getr regs 11 = w64 size -> 1 <= data <= 2 ^ 62 -> 0 <= size <= 3 * 2 ^ 20 ->
  st_ok_pi SEGS VAL (cawB_E regs) ss_cawB0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_cawB)) mem (seg_rom SEGS))).
Proof.
intros W regs mem data size Hpres Hsp Hal H10 H11 Hd Hs.
set (E := cawB_E regs).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs []) n)
  by (intros n Hn; subst E; unfold cawB_E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 data)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 size)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
rewrite restrict_mkst_fx. unfold ss_cawB0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold cawB_rs0. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Usp. unfold CAWB_FRAME. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hpres. unfold CAWB_FRAME. lia.
- unfold cawB_rs0. cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [|split; [exact I | exact I]].
  cbn [cawB_G0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E10, E11, !unsigned_lit_small by lia.
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Section f.
Variable B : asyms.
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
(* the image fact (discharged at PI_prog_B): check_as_written's entry is the listing's slot CAWB_SLOT *)
Hypothesis Hent : SIGMA AS_check_as_written = BASE + AF_cawB.

Lemma caw_WB0 : forall C P Q, srr_inv_laws SEGS P -> caw_pre (fx := fx) B C -> caw_K_mal (fx := fx) B C P Q ->
  P (c_mem C) ->
  SRr SEGS (c_W C) (cfg_at SEGS (SIGMA AS_check_as_written) (c_regs C) (c_mem C) (c_md C))
    (fun W' c' => Q W' c' /\ P (ms_mem (cfg_ms c'))).
Proof.
intros C P Q PLAW Hpre HK HP0.
(* caw_pre BY NAME (the base's projections; the two room-count premises are not read here) *)
pose proof (caw_pre_fpre (fx := fx) B C Hpre) as HFPRE. pose proof (caw_pre_mn (fx := fx) B C Hpre) as HMN.
pose proof (caw_pre_univ (fx := fx) B C Hpre) as HUC. pose proof (caw_pre_r10 (fx := fx) B C Hpre) as H10.
pose proof (caw_pre_r11 (fx := fx) B C Hpre) as H11. pose proof (caw_pre_r12 (fx := fx) B C Hpre) as H12.
pose proof (caw_pre_r13 (fx := fx) B C Hpre) as H13. pose proof (caw_pre_rc (fx := fx) B C Hpre) as Hrc.
pose proof (caw_pre_doc (fx := fx) B C Hpre) as Hdoc. pose proof (caw_pre_size (fx := fx) B C Hpre) as Hsz.
pose proof (caw_pre_data0 (fx := fx) B C Hpre) as Hd0. pose proof (caw_pre_data62 (fx := fx) B C Hpre) as Hds.
pose proof (caw_pre_src (fx := fx) B C Hpre) as HSRC. pose proof (caw_pre_inblk (fx := fx) B C Hpre) as HINB.
pose proof (caw_pre_case (fx := fx) B C Hpre) as HRD. pose proof (caw_pre_tree (fx := fx) B C Hpre) as HTREE.
pose proof (caw_pre_ledger (fx := fx) B C Hpre) as HL. pose proof (caw_pre_ran (fx := fx) B C Hpre) as Hran.
pose proof (caw_pre_live (fx := fx) B C Hpre) as HBB. pose proof (caw_pre_max (fx := fx) B C Hpre) as HMM.
pose proof (caw_pre_frames (fx := fx) B C Hpre) as HFR. pose proof (caw_pre_room (fx := fx) B C Hpre) as HROOM.
pose proof (caw_pre_frm0 (fx := fx) B C Hpre) as HFRM.
pose proof HFPRE as (HAFN & HROD & HTOP & HRAZ & HFRM0).
pose proof HAFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
lazymatch eval vm_compute in STK with ?n => assert (EST : STK = n) by (vm_compute; reflexivity) end.
assert (Hsize0 : 0 <= c_size C) by (unfold c_size; lia).
pose proof (AR_laws_x_xs SEGS B (AR_laws_ok_cf SEGS B)) as LAWS.
pose proof (cawB_entry (c_W C) (c_regs C) (c_mem C) (c_data C) (c_size C)
  ltac:(intros a Ha; apply Hpres; unfold CAWB_FRAME in Ha; lia) ltac:(lia) Hal16 H10 H11 ltac:(lia) ltac:(lia)) as HS.
pose proof (ajournal_x_init (SK := SK) SEGS B prh_pst ARcfx STK [] _ _ _ _ _ _ _ _ HAFN) as HJ.
assert (HEI : img_env VAL A_LIM (cawB_E (c_regs C))) by (unfold cawB_E; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SLit 0) [] (cawB_E (c_regs C)) (mrestrict (w_H (c_W C)) (c_mem C))) by constructor.
assert (Usp : bv_unsigned (ew (cawB_E (c_regs C)) 2) = spZ (c_regs C))
  by (rewrite (cawB_E_reg (c_regs C) 2 2%bv eq_refl); reflexivity).
assert (E10 : ew (cawB_E (c_regs C)) 10 = Z_to_bv 64 (c_data C)) by (rewrite (cawB_E_reg (c_regs C) 10 10%bv eq_refl); exact H10).
assert (E11 : ew (cawB_E (c_regs C)) 11 = Z_to_bv 64 (c_size C)) by (rewrite (cawB_E_reg (c_regs C) 11 11%bv eq_refl); exact H11).
pose (RUNTO := @paj_run_to_x_inv fx rc SK B_prog_listing PL_caw_B PA B prh_pst ARcfx _ LAWS P PLAW).
pose (BR := paj_branch (PI := PA)).
unfold cfg_at. rewrite Hent. change (w64 (BASE + AF_cawB)) with (Z_to_bv 64 (BASE + AF_cawB)).
(* ---- +0 .. +28: the frame, the four saves, s0 = rc, a2 = data + size, the struct's p; stops at bltu a2, a0 ---- *)
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HP0 cawB_span (AF_cawB + CAWB_MAL); [caw_awr Usp|].
rename HF into HF1, HFr into HFr1, HG into HG1.
(* +32 bltu a2, a0 (data + size below data), the UBSan pointer-overflow trap: REFUTED, 0 <= size and data + size < 2 ^ 62 *)
psrr_branch_tok RUNTO BR HS SHOK cawB_span.
{ exfalso. rewrite branch_ltu_U in Hc. apply Z.ltb_lt in Hc.
  rewrite U_SAlu, !U_SOff in Hc. cbn [zalu_raw] in Hc. rewrite E10, E11, !Z.add_0_r in Hc.
  rewrite !unsigned_lit_small in Hc by lia. caw_zc Hc. lia. }
clear Hc.
(* +36 .. +64: s1 = doc, a0 = (data != 0) xor (data + size == 0) and the second UBSan trap `beqz a0` (+52), DECIDED
   by the engine (not taken) from atom 10's fact 1 <= data and the condition data + size >=u data the bltu step
   added; the struct's end and depth, a0 = size + 1; stops at the jal of __wrap_malloc (+68) *)
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HP0 cawB_span (AF_cawB + CAWB_MAL); [caw_awr Usp|].
(* ---- the cut CAWB_MAL ---- *)
lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
  let rs := eval vm_compute in (ss_mem ss) in
  lazymatch rs with [YP09.mkRegion _ _ _ _ _ ?cs] =>
    pose proof (caw_slot _ _ ss _ cs HS ltac:(vm_compute; reflexivity)) as VS end;
  pose proof (cawB_sp_at _ ss _ _ HS ltac:(vm_compute; reflexivity) ltac:(unfold CAWB_FRAME; lia)) as HSP;
  pose proof (cawB_reg_at _ ss _ _ 8%bv 12 12%bv HS ltac:(vm_compute; reflexivity) eq_refl) as R8;
  pose proof (cawB_reg_at _ ss _ _ 9%bv 13 13%bv HS ltac:(vm_compute; reflexivity) eq_refl) as R9;
  pose proof (cawB_reg_at _ ss _ _ 18%bv 18 18%bv HS ltac:(vm_compute; reflexivity) eq_refl) as R18;
  assert (R10 : getr (ms_regs ms0) 10 = w64 (c_size C + 1))
    by (rewrite (st_ok_pi_restrict_reg (PI := PA) _ _ ss ms0 10%bv HS);
        change (sr_get (ss_regs ss) 10%bv) with (SOff 11 1); cbn [sv_denot]; rewrite E11;
        rewrite unsigned_lit_small by lia; reflexivity);
  assert (HAE : env_agree 32 (Ereg (c_regs C) []) (cawB_E (c_regs C)))
    by (split; [intros n Hn; unfold cawB_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]);
  pose proof (regs_kept_of_st_ok_pi (PI := PA) _ ss _ (c_regs C) [] ([3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv)
    HS HAE ltac:(vm_compute; reflexivity)) as KK
end.
(* the memory: only the frame window [sp0 - 80, sp0) changed *)
assert (KO : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (c_regs C) - CAWB_FRAME <= a < spZ (c_regs C)) ->
  aview SEGS (w_H (c_W C)) (ms_mem ms0) a = aview SEGS (w_H (c_W C)) (c_mem C) a).
{ intros a Ha Hn.
  rewrite (caw_keep_out _ _ (c_W C) (ms_mem ms) (ms_mem ms0) (spZ (c_regs C) - CAWB_FRAME) (spZ (c_regs C)) HFr
    ltac:(caw_win Usp) a Ha Hn).
  exact (caw_keep_out _ _ (c_W C) (c_mem C) (ms_mem ms) (spZ (c_regs C) - CAWB_FRAME) (spZ (c_regs C)) HFr1
    ltac:(caw_win Usp) a Ha Hn). }
(* the statics (prh_pst, alloc.c's) lie below alloc_ceiling, off the frame: their aview is the entry's *)
assert (KST : forall a, Exists (in_zr a) prh_pst ->
  aview SEGS (w_H (c_W C)) (ms_mem ms0) a = aview SEGS (w_H (c_W C)) (c_mem C) a).
{ intros a Ha. pose proof (caw_pst_low a Ha). apply KO; unfold CAWB_FRAME; lia. }
(* the ledger at the entry's values: the statics and the harness heads lie below alloc_ceiling, off the frame *)
assert (HL2 : prh_ledger B (c_ly C) (c_S C) (c_Hp C) (c_W C) (ms_mem ms0) (c_Lam C) (c_peak C) (c_cnt C)
  (c_fail C) (c_ran C) (c_most C) 0).
{ apply (prh_ledger_kept_aview B (c_ly C) (c_S C) (c_Hp C) (c_W C) (c_mem C) (c_ly C) (c_S C) (c_Hp C) (c_W C)
    (ms_mem ms0) (c_Lam C) (c_peak C) (c_cnt C) (c_fail C) (c_ran C) (c_most C) 0 HL).
  - exact KST.
  - intros a k i Hin Hi. change (@cf_head CfParams_preset) with 16.
    destruct (caw_hblock B _ _ _ _ _ _ _ _ _ _ _ _ a k HL Hin) as (Hk0 & Hab & _).
    change (@cf_head CfParams_preset) with 16 in Hab.
    destruct (alx_blocks SEGS B ARcfx LAWS _ _ _ _ _ _ _ _ HAR Hab) as (_ & H4096 & Hc & _).
    rewrite caw_req in Hc by lia. apply KO; unfold CAWB_FRAME; lia.
  - intros a k _ H. exact H.
  - apply Permutation_refl. }
(* the frame's words *)
assert (VR : forall (r : bv 5) n od, Z.of_nat n = bv_unsigned r -> In (YP09.mkChunk od (CVal 8 (SOff n 0))) [
    YP09.mkChunk (-8) (CVal 8 (SOff 1 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
    YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0))] ->
  val_mem SEGS (rdW (c_W C) (ms_mem ms0)) (c_sp C + od) 8 (bv_unsigned (getr (c_regs C) r))).
{ intros r n od Hn Hin. unfold c_sp. rewrite <- Usp.
  apply (VS od (SOff n 0)); [| | exact (bv_unsigned_in_range 64 _)].
  - destruct Hin as [E | [E | [E | [E | []]]]]; injection E as <- <-; caw_in.
  - cbn [sv_denot]. rewrite (cawB_E_reg _ n r Hn), Z.add_0_r. reflexivity. }
assert (V8 : val_mem SEGS (rdW (c_W C) (ms_mem ms0)) (c_sp C - 8) 8 (bv_unsigned (getr (c_regs C) 1)))
  by (rewrite <- Z.add_opp_r; exact (VR 1%bv 1%nat (-8) eq_refl ltac:(caw_in))).
assert (V16 : val_mem SEGS (rdW (c_W C) (ms_mem ms0)) (c_sp C - 16) 8 (bv_unsigned (getr (c_regs C) 8)))
  by (rewrite <- Z.add_opp_r; exact (VR 8%bv 8%nat (-16) eq_refl ltac:(caw_in))).
assert (V24 : val_mem SEGS (rdW (c_W C) (ms_mem ms0)) (c_sp C - 24) 8 (bv_unsigned (getr (c_regs C) 9)))
  by (rewrite <- Z.add_opp_r; exact (VR 9%bv 9%nat (-24) eq_refl ltac:(caw_in))).
assert (V32 : val_mem SEGS (rdW (c_W C) (ms_mem ms0)) (c_sp C - 32) 8 (bv_unsigned (getr (c_regs C) 18)))
  by (rewrite <- Z.add_opp_r; exact (VR 18%bv 18%nat (-32) eq_refl ltac:(caw_in))).
assert (V72 : val_mem SEGS (rdW (c_W C) (ms_mem ms0)) (c_sp C - 72) 8 (c_data C)).
{ replace (c_sp C - 72) with (bv_unsigned (ew (cawB_E (c_regs C)) 2) + -72) by (rewrite Usp; unfold c_sp; lia).
  apply (VS (-72) (SOff 10 0)); [caw_in | | lia].
  cbn [sv_denot]. rewrite E10, Z.add_0_r, unsigned_lit_small by lia. reflexivity. }
assert (V64 : val_mem SEGS (rdW (c_W C) (ms_mem ms0)) (c_sp C - 64) 8 (c_data C + c_size C)).
{ replace (c_sp C - 64) with (bv_unsigned (ew (cawB_E (c_regs C)) 2) + -64) by (rewrite Usp; unfold c_sp; lia).
  apply (VS (-64) (SAlu ALU_ADD (SOff 10 0) (SOff 11 0))); [caw_in | | lia].
  rewrite denot_lit_U. f_equal. rewrite U_SAlu, !U_SOff. cbn [zalu_raw]. rewrite E10, E11, !Z.add_0_r.
  rewrite !unsigned_lit_small by lia. caw_zcg. reflexivity. }
assert (V56 : val_mem SEGS (rdW (c_W C) (ms_mem ms0)) (c_sp C - 56) 8 0).
{ replace (c_sp C - 56) with (bv_unsigned (ew (cawB_E (c_regs C)) 2) + -56) by (rewrite Usp; unfold c_sp; lia).
  apply (VS (-56) (SLit 0)); [caw_in | reflexivity | lia]. }
(* the machine state at the cut, at the pc of the continuation *)
pmkst HS.
lazymatch goal with |- context [Z_to_bv 64 (BASE + ?n)] => change (BASE + n) with (BASE + (AF_cawB + CAWB_MAL)) end.
refine (HK (c_ly C) (c_S C) (c_Hp C) (c_W C) (ms_regs ms0) (ms_mem ms0) _ 0 _ HP0).
unfold cut_mal, caw_base, caw_saved, caw_ex3.
refine (conj (conj HFRM (conj _ (conj HJ (conj _ (conj _ (conj _ (conj (conj V8 (conj V16 (conj V24 V32)))
  (conj eq_refl HROOM)))))))) (conj _ (conj R18 (conj R10 (conj (conj V72 V64)
  (conj V56 (conj eq_refl (conj eq_refl (conj (caw_prog_entry C) (conj HL2 (caw_pre_hull (fx := fx) B C Hpre))))))))))).
- intros r _. reflexivity.
- intros r Hr. exact (KK r Hr).
- exact HSP.
- rewrite R8. exact H12.
- rewrite R9. exact H13.
Qed.

End f.
End d.

Print Assumptions caw_WB0.
