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
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PjGetB.v, with its module paths and module names changed; 489 of its 544 lines of code are new or changed and 1711 lines of the source are left out. *)
(* fuzz_preset, image B' (#102): check_as_written's out-of-memory segments WB4a and WB4 (Caw102B.v), lane CawA102R
   (for B'; first walked by lane CawB102; re-fitted to the batch-prep base by CawA102R.KWB34; now INT102-READY).
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).
   BASE OF RECORD: the kit's cut, this row's lib/B/Prog/Caw102B.v (its
   statements, unchanged here). The kit as the cut carries it, its texts by path:
   lib/A/PRH_FnAlloc.v 4d8aeba047e5 (tfuzz_alloc_ran_out_specX :175-183: binders most own; its premise `prh_ledger ..
   ran most own`, its post `room keep /\ getr regs' 10 = w64 ran /\ Hp' = Hp /\ S' = S /\ ablocks keep /\ prh_ledger
   .. ran most own`), lib/A/PRH_Base.v (fpre :988-1010, its last conjunct frm_zero (fp_csr fx),
   FRM0-ENTRY; the projection PRH_Base.prh_ledger_own, qualified: S1Ledger.v has a lemma of the same name),
   lib/A/PRH_FnCheck.v c40cf3fdcd2a (tcheck_as_written_specX :832-902, the base's text). Listing lib/B/Listing_prog.v
   c97cc46b3e13. Engine (the P'' set as the cut carries it): YCbqG.v (the journal
   read by the ajx_ projections), YCbqGcall.v c1fcd07d2537 (aj_call_x_sp), YC1fPx.v 7814b594066f, YC1fP.v 96e2e49ece5f,
   YSRrMemnorm.v 5ffa8525936b (srr_inv_call), lib/A/Prog/PRW_StepKit.v 0df3991c13f4 (pa_slot_lt_ceil_b). (Blobs derived
   by git hash-object in the worktree.)
   WHAT CHANGED ON THIS BASE AND WHY (the previous fit: this file cb479ef56a05 on the P'' journal,
   in the P'' trial):
   - caw_pre IS READ BY NAME: caw_pre is now the text's 27 premises (the batch's two room counts after room_live_cf,
     :862-863, then the hull budget and HPOS, Caw102B.v:139-165), so WB4's positional destruct of caw_pre is gone; it takes fpre, rc's range and c_ran C = 0 by the
     base's projections caw_pre_fpre / caw_pre_rc / caw_pre_ran.
   - THE OUTCOME: cut_end's r = 1 arm carries caw_dead C now; WB4's two arms to cut_end stay REFUTED (no arm builds
     cut_end), so KEND stays the statement's continuation argument and nothing more is owed there.
   - THE RUN-WORD LIST DW and THE ROOM COUNTS: WB4 reads neither (no allocator call runs in 0x8201c .. 0x82038; caw_cnt
     C is not a premise here, and B' caw_base does not carry it).
   The statements of caw_WB4a / caw_WB4 are unchanged.
   KEPT FROM THE EARLIER FITS: the cuts' run position is THE PROGRESS FACT caw_prog C (caw_evs C) S3 at cut_oA, cut_oB
   and cut_ck: WB4a's hand step leaves S3, and fuzz_alloc_ran_out keeps S (its post's S' = S), so each cut's caw_prog
   is the next cut's as it stands. FRM0-ENTRY: the callee fpre built for fuzz_alloc_ran_out (run at the cut's float
   state fy) takes its last conjunct frm_zero (fp_csr fy) from cut_oB's caw_base, first conjunct. The byte the load
   reads is PRH_Base.prh_ledger_own of cut_oB's ledger (own 0); the call's text takes and gives the ledger at (c_most
   C) 0, so cut_ck's ledger is the text's post ledger.
   WB4a (B' 0x8201c, cut_oA -> cut_oB): `addi s2, zero, -1`; want = -1 is caw_want's left arm (cut_oA's rc <> 0). The
   step writes no memory (frame_of_read_only), so cut_oA's ledger and caw_prog are cut_oB's.
   WB4 (B' 0x82020, cut_oB -> cut_ck): `auipc a0` + `lbu a0, g_own_ran_out` (the listing's PLdHi .. (A_OBJ 13) 0 SZ1),
   `addi s1, zero, 1`, `bnez a0` -> 0x82058 (REFUTED: a0 = the atom 33 = cut_oB's ledger own byte 0); `jal
   fuzz_alloc_ran_out` (0x82030), `bnez a0` -> 0x82058 (REFUTED: a0 = ran = c_ran C = 0 by caw_pre), else 0x82038. The
   load reads the static through ONE read-only region seated at A_OBJ 13 (one byte, the atom 33 = 0). The call by
   YCbqGcall.aj_call_x_sp with TRO at the current float state; its post gives a0 = ran, S' = S, Hp' = Hp, the ledger
   at (c_most C) 0, and the memnorm keep, which carries P by srr_inv_call; cut_ck with the same want (s2 is
   callee-saved), the ledger of the text's post (the hand steps before the call write no memory, so the text's entry
   ledger is cut_oB's at mem3), and cut_oB's caw_prog (S' = S).
   fpre at the call: afn_pre_x from the rule; arodata_okP kept from entry by the journal's image clause, which needs
   Hpst_rw (the alloc.c statics are not read-only image bytes); spZ + 64 <= ly_stk_hi from entry by layout_le; raZ <
   YM05.alloc_ceiling by PRW_StepKit.pa_slot_lt_ceil_b at the return slot; frm_zero (fp_csr fy) from caw_base (the
   call runs at the cut's float state); 4096 <= the return pc by the image law
   (alx_img, alx_layout_ok's lo_img: every segment starts at or above kImgLo). The empty chain: s0 = rc (an int,
   sign-extended) is below YM05.alloc_ceiling or above ly_top - 16.
   SECTION HYPOTHESES (owners): TRO : fuzz_alloc_ran_out's text tfuzz_alloc_ran_out_specX, float-generic [a Theorem Labs lane,
   discharged by the walk of fuzz_alloc_ran_out]; Hown_obj : 13 = g_own_ran_out in listing d42e123915ae (the static is
   1 byte, pi_gz_own_ran_out) [image fact, discharged at PI_prog_B by the instantiation]; Hpst_rw : the alloc.c statics
   are not read-only image bytes [image fact, a Theorem Labs lane's cwi_pst_rw, discharged at PI_prog_B by the instantiation].
   No new Section hypothesis in this re-fit (nor since the caw_pst base). The lemmas' P / PLAW / PCALL are the top's
   caw_mn_laws / caw_mn_call.
   Numerals: register numbers (WORD); 80 / 64 (LENGTH: the frame, fpre's stack top margin); 8 / 16 / 24 / 32 (LENGTH:
   the saves' offsets); 1 (LENGTH: the static's width; WORD: s1's value); 0 (WORD: the byte g_own_ran_out holds at the
   load, the ledger's own); 2 ^ 31 / 2 ^ 47 / 2 ^ 64 (WORD: rc's int range, the stack bound, the word); 32 / 33
   (DERIVED: the engine's atom numbering); 188 (DERIVED: the call's return offset, 4 * the slot). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YK0o YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallx YGcallcf YG0lawscf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetRodata.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnEx PRH_FnAlloc PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_StepKit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Caw102B.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YI5b.
#[global] Remove Hints YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* the read-only region of g_own_ran_out: base A_OBJ 13, one byte, its value the atom 33 *)
Definition cawO_rg : YP09.region := YP09.mkRegion (Some (A_OBJ 13)) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
(* the registers the segment never writes before its exits (sp, gp, tp, s0, s2 .. s11) *)
Definition cawO_kept : list (bv 5) := [2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition cawO_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {SK : YI16.sink_head}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
#[local] Existing Instance prh_room_live_a8.
Context {PA : PAImg B_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Abbreviation VAL := (@pa_val _ B_prog_listing PA).
#[local] Abbreviation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Abbreviation STK := (STK_check_as_written (PI := prh_img_B)).

(* the seats: every register its own atom, atom 32 the shadow base; at the load, atom 33 the byte own *)
Definition cawO_E0 (regs : bvmap 5 word) : env := @Eimg _ B_prog_listing PA (Ereg regs [Z_to_bv 64 SHADOW_OFF]).
Definition cawO_E (regs : bvmap 5 word) (own : Z) : env :=
  @Eimg _ B_prog_listing PA (Ereg regs [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 own]).
Lemma cawO_E_own : forall regs own, ew (cawO_E regs own) 33 = Z_to_bv 64 own.
Proof.
intros regs own. unfold cawO_E. rewrite Eimg_low by (unfold A_TEXT; lia).
change 33%nat with (32 + 1)%nat. rewrite ew_Ereg_extra. reflexivity.
Qed.

(* the seat at a cut with no region (WB4a's 0x8201c, WB4's return slot 0x82034) *)
Lemma cawO_seat0 : forall fy (W : world SEGS) regs mem pc,
  st_ok_pi (fx := fy) SEGS VAL (cawO_E0 regs) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (@YK11.mkst fy regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom SEGS))).
Proof.
intros fy W regs mem pc. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold cawO_E0. apply regs_ok_Eimg_Ereg.
- reflexivity.
- apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. exact I.
- split; [exact I | split; exact I].
Qed.

(* the seat at the load (cut_oB, 0x82020): the static's region, its byte own *)
Lemma cawO_seat : forall fy (W : world SEGS) regs mem own,
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 13)) 1 own -> 0 <= own < 256 ->
  st_ok_pi (fx := fy) SEGS VAL (cawO_E regs own) (mkSS (AF_cawB + CAWB_OB) sr_atoms [cawO_rg] None (mkFacts [] [] []))
    (restrict (w_H W) (@YK11.mkst fy regs (Z_to_bv 64 (BASE + (AF_cawB + CAWB_OB))) mem (YK11.seg_rom SEGS))).
Proof.
intros fy W regs mem own Hv Hown. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold cawO_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, cawO_rg.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  pose proof (@pa_val_range _ _ PA (A_OBJ 13)) as HR.
  assert (Hb : base_val (cawO_E regs own) (Some (A_OBJ 13)) = VAL (A_OBJ 13)).
  { cbn [base_val]. unfold cawO_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    apply unsigned_lit_small. exact HR. }
  rewrite Hb. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS (cawO_E regs own) _ (VAL (A_OBJ 13)) 0 1%N (SOff 33 0) own).
  + cbn [sv_denot]. rewrite cawO_E_own, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + cbn. lia.
  + cbn. lia.
  + rewrite Z.add_0_r. exact Hv.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [exact I | split; exact I].
Qed.

(* a callee-saved register is kept across a call (YG0d.v aregs_preserved, by the register's number) *)
Lemma cawO_pres : forall (regs regs' : bvmap 5 word) (r : bv 5), aregs_preserved regs regs' ->
  In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r.
Proof.
intros regs regs' r HP Hr.
pose proof (HP (bv_unsigned r)) as H. rewrite Z_to_bv_bv_unsigned in H. apply H.
cbn [In] in Hr. repeat (destruct Hr as [<- | Hr];
  [lazymatch goal with |- acallee_saved (bv_unsigned ?x) => let v := eval vm_compute in (bv_unsigned x) in
     change (bv_unsigned x) with v end; unfold acallee_saved; lia |]). destruct Hr.
Qed.

(* the empty chain at a call: s0 = rc, an int sign-extended, is below YM05.alloc_ceiling or above ly_top - 16 *)
Lemma cawO_achain : forall ly rd sp (regs : bvmap 5 word) rc0, getr regs 8 = w64 rc0 -> - 2 ^ 31 <= rc0 < 2 ^ 31 ->
  ly_top ly <= 2 ^ 47 -> achain ly rd sp (s0Z regs) [].
Proof.
intros ly rd sp regs rc0 H8 Hrc Htop. unfold s0Z. rewrite H8. unfold w64. rewrite Z_to_bv_unsigned.
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
pose proof (@YM05.alloc_ceiling_value rc) as [[HC _] _].
left. split; [|reflexivity].
destruct (Z_le_gt_dec 0 rc0) as [Hp|Hn].
- left. rewrite Z.mod_small by lia. lia.
- right. left. replace (rc0 mod 2 ^ 64) with (rc0 + 2 ^ 64) by (rewrite <- (Z.mod_small (rc0 + 2 ^ 64) (2 ^ 64)) by lia;
    rewrite Z.add_mod, Z.mod_same, Z.add_0_r, Z.mod_mod by lia; reflexivity). lia.
Qed.

Section f.
Variable B : asyms.
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
Let LAWS : AR_laws_x SEGS B ARcfx cf_head := AR_laws_x_xs SEGS B (AR_laws_ok_cf SEGS B).

(* a listing slot's pc is at or above kImgLo: its word is fetched from a segment, and every segment starts at or above
   the image's start, which the layout law puts at kImgLo *)
Lemma cawO_text_lo : forall ly S Hp (W : world SEGS) mem md k, ARcfx ly S Hp W mem md -> 0 <= k < 2 ^ 40 ->
  match plookup (@pl_tpi _ PL_caw_B) k with Some _ => true | None => false end = true ->
  kImgLo <= BASE + k.
Proof.
intros ly S Hp W mem md k HAR Hk40 Hk.
destruct (plookup (@pl_tpi _ PL_caw_B) k) as [e|] eqn:He; [|discriminate Hk].
pose proof (@pa_B_ok _ _ PA) as HB. rewrite <- (@pl_tpi_eq _ PL_caw_B) in He.
pose proof (cert_slot asym (clookup pa_tbl) pa_val pa_sigma B_prog_listing pa_cert k e He) as [Hc _].
unfold pi_slot_check in Hc.
destruct (clookup pa_tbl (pa_val A_TEXT + k)) as [wz|] eqn:Hf; [|discriminate].
pose proof (pa_tbl_ok _ _ Hf) as Hfw.
unfold fetch_word in Hfw. destruct (negb _); [discriminate|].
unfold code_read in Hfw.
destruct (find_segment pa_segs (bv_unsigned (Z_to_bv 64 (pa_val A_TEXT + k))) (Z.of_N 4)) as [sg|] eqn:Hfs;
  [|discriminate].
destruct (find_segment_hit _ _ _ _ Hfs) as (Hin & Hlo & _).
rewrite unsigned_lit_small in Hlo by lia.
destruct (alx_img SEGS B ARcfx LAWS ly S Hp W mem md HAR) as [Hsg _].
destruct (Hsg sg Hin) as [Hsg1 _].
destruct (lo_img ly (alx_layout_ok SEGS B ARcfx LAWS ly S Hp W mem md HAR)) as [Hi _].
lia.
Qed.

(* WB4a (0x8201c): s2 := -1, then the g_own_ran_out test with want = -1 (rc <> 0); one hand step that writes no memory,
   so cut_oA's ledger (own 0) and progress fact caw_prog C (caw_evs C) S3 are cut_oB's *)
Lemma caw_WB4a : forall C P Q, srr_inv_laws SEGS P -> caw_pre (fx := fx) B C -> caw_K_oB (fx := fx) B C P Q ->
  caw_K_oA (fx := fx) B C P Q.
Proof.
intros C P Q PLAW Hpre KOB fy ly3 S3 Hp3 W3 regs3 mem3 md3 k Hcut HPM.
destruct Hcut as (Hbase & Hrc0 & Eab & Hrp & HL).
pose proof Hbase as (Hfz & Hfk & HJ & Hk & Hsp & R8 & HSV & EHp & HROOM).
set (E := cawO_E0 regs3).
pose proof (cawO_seat0 fy W3 regs3 mem3 (AF_cawB + CAWB_OA)) as HS. fold E in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold cawO_E0; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W3) mem3)) by (unfold sh_ok; apply Forall_nil).
assert (HAE : env_agree 32 (Ereg regs3 [Z_to_bv 64 SHADOW_OFF]) E)
  by (subst E; unfold cawO_E0; split; [intros i Hi; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
pose (RUNTO := @paj_run_to_x_inv fy rc SK B_prog_listing PL_caw_B PA B prh_pst ARcfx _ LAWS P PLAW).
unfold caw_cfg.
(* addi s2, zero, -1; stop at 0x82020 *)
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM cawO_span (AF_cawB + CAWB_OB).
{ intros a (rg & Hin & _). destruct Hin. }
lazymatch type of HF with frame_of _ ?rs _ _ =>
  pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as EM1 end.
clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msn) =>
  rewrite (st_ok_pi_restrict_mkst (fx := fy) (L := B_prog_listing) (PI := PA) (w_H W3) E _ msn HS eq_refl) end.
cbn [ss_pc].
prreg HS (18%bv : bv 5) Q18.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msn) =>
  assert (HKP : forall rr, In rr [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
    getr (ms_regs msn) rr = getr regs3 rr)
  by (eapply (regs_kept_of_st_ok_pi (fx := fy) (L := B_prog_listing) (PI := PA) E _ (restrict (w_H W3) msn) regs3
      [Z_to_bv 64 SHADOW_OFF]); [exact HS | exact HAE | vm_compute; reflexivity]);
  lazymatch goal with |- context [Z_to_bv 64 (?b + ?p)] =>
    change (Z_to_bv 64 (b + p)) with (Z_to_bv 64 (BASE + (AF_cawB + CAWB_OB))) end;
  apply (KOB fy ly3 S3 Hp3 W3 (ms_regs msn) (ms_mem msn) _ k (-1)); [|exact HPM];
  rewrite EM1 in HJ |- *
end.
split; [|split; [|split; [left; split; [reflexivity | exact Hrc0] | split; [exact Eab | split; [exact Hrp | exact HL]]]]].
- split; [exact Hfz|]. split; [exact Hfk|]. split; [exact HJ|].
  split; [intros rr Hr; rewrite <- (Hk rr Hr); apply HKP; cbn [In] in Hr |- *; tauto|].
  split; [unfold spZ; rewrite (HKP 2%bv) by (left; reflexivity); exact Hsp|].
  split; [rewrite (HKP 8%bv) by (cbn; tauto); exact R8|].
  split; [exact HSV|]. split; [exact EHp|]. exact HROOM.
- rewrite Q18. apply bv_eq. reflexivity.
Qed.

(* the world relation past a free (the re-hide's zone) *)
#[local] Abbreviation RW := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
(* YC1fP.paj_branch over any world relation R (a branch takes no step: the case split on its condition) *)
Lemma wb4_branchR : forall (fz : YK11.FPState) (R : world SEGS -> world SEGS -> Prop) W E ss ms md Q c a b,
  st_ok_pi (fx := fz) SEGS VAL E ss (restrict (w_H W) ms) ->
  (branch_taken c (sv_denot E a) (sv_denot E b) = true ->
   st_ok_pi (fx := fz) SEGS VAL E (add_cond ss (mkAC c a b)) (restrict (w_H W) ms) ->
   YA0nH.SRrG SEGS R W (mkCfg ms md) Q) ->
  (branch_taken c (sv_denot E a) (sv_denot E b) = false ->
   st_ok_pi (fx := fz) SEGS VAL E (add_cond ss (mkAC (neg_bc c) a b)) (restrict (w_H W) ms) ->
   YA0nH.SRrG SEGS R W (mkCfg ms md) Q) ->
  YA0nH.SRrG SEGS R W (mkCfg ms md) Q.
Proof.
intros fz R W E ss ms md Q c a b HS HT HF.
destruct (branch_taken c (sv_denot E a) (sv_denot E b)) eqn:Hb.
- apply HT; [reflexivity|]. pose proof (st_ok_add_cond SEGS E _ _ c a b HS Hb) as H. destruct ss; exact H.
- apply HF; [reflexivity|]. pose proof (st_ok_add_cond_neg SEGS E _ _ c a b HS Hb) as H. destruct ss; exact H.
Qed.

(* caw_WB4a over RW: the same hand step by the R runner; the cuts' journals are at RW *)
Lemma caw_WB4aR : forall C P Q, srr_inv_laws SEGS P -> caw_pre (fx := fx) B C ->
  caw_K_oBR (fx := fx) B (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) C P Q ->
  caw_K_oAR (fx := fx) B (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) C P Q.
Proof.
intros C P Q PLAW Hpre KOB fy ly3 S3 Hp3 W3 regs3 mem3 md3 k Hcut HPM.
destruct Hcut as (Hbase & Hrc0 & Eab & Hrp & HL).
pose proof Hbase as (Hfz & Hfk & HJ & Hk & Hsp & R8 & HSV & EHp & HROOM).
unfold caw_JR in HJ.
set (E := cawO_E0 regs3).
pose proof (cawO_seat0 fy W3 regs3 mem3 (AF_cawB + CAWB_OA)) as HS. fold E in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold cawO_E0; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W3) mem3)) by (unfold sh_ok; apply Forall_nil).
assert (HAE : env_agree 32 (Ereg regs3 [Z_to_bv 64 SHADOW_OFF]) E)
  by (subst E; unfold cawO_E0; split; [intros i Hi; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
pose (RUNTO := @paj_run_to_x_invR fy rc SK B_prog_listing PL_caw_B PA B prh_pst ARcfx _ LAWS P PLAW RW
  (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)).
unfold caw_cfg.
(* addi s2, zero, -1; stop at 0x82020 *)
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM cawO_span (AF_cawB + CAWB_OB).
{ intros a (rg & Hin & _). destruct Hin. }
lazymatch type of HF with frame_of _ ?rs _ _ =>
  pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as EM1 end.
clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msn) =>
  rewrite (st_ok_pi_restrict_mkst (fx := fy) (L := B_prog_listing) (PI := PA) (w_H W3) E _ msn HS eq_refl) end.
cbn [ss_pc].
prreg HS (18%bv : bv 5) Q18.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msn) =>
  assert (HKP : forall rr, In rr [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
    getr (ms_regs msn) rr = getr regs3 rr)
  by (eapply (regs_kept_of_st_ok_pi (fx := fy) (L := B_prog_listing) (PI := PA) E _ (restrict (w_H W3) msn) regs3
      [Z_to_bv 64 SHADOW_OFF]); [exact HS | exact HAE | vm_compute; reflexivity]);
  lazymatch goal with |- context [Z_to_bv 64 (?b + ?p)] =>
    change (Z_to_bv 64 (b + p)) with (Z_to_bv 64 (BASE + (AF_cawB + CAWB_OB))) end;
  apply (KOB fy ly3 S3 Hp3 W3 (ms_regs msn) (ms_mem msn) _ k (-1)); [|exact HPM];
  rewrite EM1 in HJ |- *
end.
split; [|split; [|split; [left; split; [reflexivity | exact Hrc0] | split; [exact Eab | split; [exact Hrp | exact HL]]]]].
- split; [exact Hfz|]. split; [exact Hfk|]. split; [exact HJ|].
  split; [intros rr Hr; rewrite <- (Hk rr Hr); apply HKP; cbn [In] in Hr |- *; tauto|].
  split; [unfold spZ; rewrite (HKP 2%bv) by (left; reflexivity); exact Hsp|].
  split; [rewrite (HKP 8%bv) by (cbn; tauto); exact R8|].
  split; [exact HSV|]. split; [exact EHp|]. exact HROOM.
- rewrite Q18. apply bv_eq. reflexivity.
Qed.

(* the call's image facts and callee text (discharged at PI_prog_B / by the walk of fuzz_alloc_ran_out) *)
Hypothesis TRO : forall fz, tfuzz_alloc_ran_out_specX (fx := fz) B ARcfx SK.
(* 13 = g_own_ran_out in listing d42e123915ae (the static is 1 byte, pi_gz_own_ran_out) *)
Hypothesis Hown_obj : VAL (A_OBJ 13) = pi_g_own_ran_out.
(* the alloc.c statics are not read-only image bytes (CawA102's cwi_pst_rw): what carries arodata_okP across the
   calls by the journal *)
Hypothesis Hpst_rw : forall a, Exists (in_zr a) prh_pst -> ~ in_roP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) a.

(* WB4 (0x82020): the g_own_ran_out test and the fuzz_alloc_ran_out () test. No boundary premise: the byte the load
   reads is cut_oB's ledger own byte 0 (PRH_Base.prh_ledger_own), so the own <> 0 arm to the End is refuted; KEND stays
   the statement's continuation argument (no arm reaches it). At cut_ck, the ledger is the text's post ledger. *)
Lemma caw_WB4 : forall C P Q, srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  caw_pre (fx := fx) B C -> caw_K_end (fx := fx) B C P Q -> caw_K_ck (fx := fx) B C P Q ->
  caw_K_oB (fx := fx) B C P Q.
Proof.
intros C P Q PLAW PCALL Hpre KEND KCK fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want Hcut HPM.
destruct Hcut as (Hbase & R18 & Hw & Eab & Hrp & HL).
(* the cut's ledger: g_own_ran_out holds 0, the byte the load reads *)
pose proof (PRH_Base.prh_ledger_own B ly3 S3 Hp3 W3 mem3 _ _ _ _ _ _ _ HL) as (Hov & _).
pose proof Hbase as (Hfz & Hfk & HJ & Hk & Hsp & R8 & HSV & EHp & HROOM).
(* caw_pre read BY NAME (the base's caw_pre_* projections): fpre, rc's range, c_ran C = 0 *)
pose proof (caw_pre_fpre (fx := fx) B C Hpre) as HFPRE0. pose proof (caw_pre_rc (fx := fx) B C Hpre) as Hrc.
pose proof (caw_pre_ran (fx := fx) B C Hpre) as Hran0.
pose proof HFPRE0 as (HAFN0 & HROD0 & HTOP0 & _).
pose proof HAFN0 as (_ & _ & _ & Hgp0 & Htp0 & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil0 & Hslo0 & Hshi0 & H470 & _ & Htop0 & Htop20).
assert (EST : STK = 26800) by (vm_compute; reflexivity).
assert (ES1 : STK_fuzz_alloc_ran_out (PI := prh_img_B) = 0) by (vm_compute; reflexivity).
assert (EAF : AF_cawB = 2220) by (vm_compute; reflexivity).
pose proof (@pa_B_ok _ _ PA) as HBok.
assert (Hov1 : val_mem SEGS (mrestrict (w_H W3) mem3) (VAL (A_OBJ 13)) 1 0) by (rewrite Hown_obj; exact Hov).
set (E := cawO_E regs3 0).
pose proof (cawO_seat fy W3 regs3 mem3 0 Hov1 ltac:(lia)) as HS. fold E in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold cawO_E; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W3) mem3)) by (unfold sh_ok; apply Forall_nil).
assert (HAE : env_agree 32 (Ereg regs3 [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 0]) E)
  by (subst E; unfold cawO_E; split; [intros i Hi; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (U33 : U E (SExt false 8 (SOff 33 0)) = 0).
{ rewrite U_SExt. cbv beta iota. rewrite U_SOff. subst E. rewrite cawO_E_own, Z.add_0_r, unsigned_lit_small by lia.
  rewrite (zcanon_id 0) by (unfold M64; lia). change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia.
  apply zcanon_id. unfold M64. lia. }
pose (RUN := @paj_run_x_inv fy rc SK B_prog_listing PL_caw_B PA B prh_pst ARcfx _ LAWS P PLAW).
pose (RUNTO := @paj_run_to_x_inv fy rc SK B_prog_listing PL_caw_B PA B prh_pst ARcfx _ LAWS P PLAW).
pose (BR := @paj_branch fy rc B_prog_listing PA).
unfold caw_cfg.
(* auipc / lbu a0, g_own_ran_out / addi s1, zero, 1; stop at `bnez a0` (0x8202c) *)
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM cawO_span (AF_cawB + CAWB_END).
{ intros a (rg & Hin & Ha). cbn in Hin. destruct Hin as [<- | []]. cbn in Ha. lia. }
lazymatch type of HF with frame_of _ ?rs _ _ =>
  pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as EM1 end.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK cawO_span.
{ (* own <> 0: REFUTED, a0 = the atom 33 = cut_oB's ledger own byte 0 (U33) *)
  exfalso. rewrite branch_ne_U, U33, U_SLit in Hc. change (zcanon 0) with 0 in Hc. cbn in Hc. discriminate Hc. }
(* own = 0: the call of fuzz_alloc_ran_out *)
clear Hc.
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM cawO_span (AF_cawB + CAWB_CK).
{ intros a (rg & Hin & Ha). cbn in Hin. destruct Hin as [<- | []]. cbn in Ha. lia. }
lazymatch type of HF with frame_of _ ?rs _ _ =>
  pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as EM2 end.
clear HF HFr HG.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) => rename m into msc end.
assert (Emc : ms_mem msc = mem3) by (rewrite EM2, EM1; reflexivity).
assert (KC : forall rr, In rr cawO_kept -> getr (ms_regs msc) rr = getr regs3 rr)
  by (exact (regs_kept_of_st_ok SEGS E _ _ regs3 [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 0] cawO_kept HS HAE
    ltac:(vm_compute; reflexivity))).
prreg HS (1%bv : bv 5) R1.
assert (Usp : spZ (ms_regs msc) = c_sp C + - CAWB_FRAME).
{ unfold spZ. rewrite (KC 2%bv) by (left; reflexivity). unfold spZ in Hsp. lia. }
(* the journal read BY NAME (YCbqG's ajx_ projections), never positionally *)
unfold caw_J in HJ. pose proof (ajx_ar HJ) as HAR3. pose proof (ajx_ly HJ) as Hle3.
destruct Hle3 as (_ & _ & _ & _ & _ & _ & _ & _ & Ltop & _ & Lshi & _).
(* fpre of fuzz_alloc_ran_out at the call: the read-only view from entry, the stack top, the return address *)
assert (HROD1 : arodata_okP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview SEGS (w_H W3) (ms_mem msc))).
{ pose proof (ajx_img HJ) as F3.
  intros a Hro Hno Hne. rewrite (F3 a).
  - exact (HROD0 a Hro Hno Hne).
  - destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hr)].
  - exact Hno.
  - exact Hne.
  - intros Hq. exact (Hpst_rw a Hq Hro).
  - apply fp_spares_closed. intros (x & Hx & _). destruct Hx. }
assert (HTOP1 : spZ (ms_regs msc) + 64 <= ly_stk_hi ly3) by (rewrite Usp, Lshi; unfold c_sp, CAWB_FRAME; lia).
assert (HRAZ1 : raZ (ms_regs msc) < YM05.alloc_ceiling).
{ unfold raZ. rewrite R1, unsigned_lit_small by lia.
  pose proof (pa_slot_lt_ceil_b (PL := PL_caw_B) (PI := PA) (AF_cawB + 188) ltac:(lia)
    ltac:(vm_compute; reflexivity)) as HSL. lia. }
assert (HLED1 : prh_ledger B ly3 S3 Hp3 W3 (ms_mem msc) (c_Lam C) (c_peak C) (c_cnt C) (c_fail C) (c_ran C)
  (c_most C) 0) by (rewrite Emc; exact HL).
(* the call, by fuzz_alloc_ran_out's text at the current float state *)
eapply SRr_bind.
{ eapply (aj_call_x_sp (fx := fy) (SK := SK) SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) W3 _ _ msc STK (c_sp C) []
    (c_ly C) (c_S C) (c_Hp C) (c_W C) (c_mem C) (c_md C) [] ly3 S3 Hp3 _ k (STK_fuzz_alloc_ran_out (PI := prh_img_B)) []
    (- CAWB_FRAME) _ [] _ HS eq_refl HJ).
  - exact Usp.
  - unfold CAWB_FRAME. reflexivity.
  - unfold CAWB_FRAME. lia.
  - rewrite ES1. lia.
  - rewrite ES1, EST. unfold CAWB_FRAME. lia.
  - rewrite (KC 3%bv) by (cbn; tauto). rewrite (Hk 3%bv) by (cbn; tauto). exact Hgp0.
  - rewrite (KC 4%bv) by (cbn; tauto). rewrite (Hk 4%bv) by (cbn; tauto). exact Htp0.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - rewrite unsigned_lit_small by lia.
    pose proof (cawO_text_lo ly3 S3 Hp3 W3 (ms_mem msc) _ (AF_cawB + 188) HAR3 ltac:(lia)
      ltac:(vm_compute; reflexivity)) as Hlo.
    unfold kImgLo in Hlo. lia.
  - apply (cawO_achain ly3 _ _ (ms_regs msc) (c_rc C)); [rewrite (KC 8%bv) by (cbn; tauto); exact R8 | exact Hrc | lia].
  - intros HPRE1.
    (* FRM0-ENTRY: the call runs at the cut's float state fy, whose rounding mode caw_base gives as 0 (Hfz) *)
    exact (TRO fy ly3 S3 Hp3 W3 (ms_regs msc) (ms_mem msc) _ [] (c_Lam C) (c_peak C) (c_cnt C) (c_fail C) (c_ran C)
      (c_most C) 0 (conj HPRE1 (conj HROD1 (conj HTOP1 (conj HRAZ1 Hfz)))) HLED1).
  - intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJc & HP2 & HQ2).
destruct HQ2 as ((_ & H10 & EHp2 & ES2 & Eab2 & HL2) & HKN).
subst Hp2 S2.
assert (HPM2 : P mem2) by exact (PCALL _ _ HKN HPM).
(* the saves above the call's sp, kept by the callee's journal (its window is empty) *)
assert (HSV2 : caw_saved C W2 mem2).
{ pose proof (ajx_hi HJc) as KJc.
  rewrite ES1 in KJc.
  assert (KK : forall a, c_sp C - 32 <= a < c_sp C -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) mem3 a).
  { intros a Ha. rewrite <- Emc. apply KJc; unfold c_sp, CAWB_FRAME in *; lia. }
  destruct HSV as (V1 & V2 & V3 & V4).
  split; [|split; [|split]]; (eapply val_mem_kept; [|eassumption]); intros kk Hkk; apply KK; cbn in Hkk; lia. }
(* the seat at the return slot 0x82034, a0 = ran = 0 *)
lazymatch goal with |- SRr _ _ {| cfg_ms := YK11.mkst _ ?raw _ _ |} _ =>
  change raw with (Z_to_bv 64 (BASE + (AF_cawB + 188))) end.
set (E2 := cawO_E0 regs2).
pose proof (cawO_seat0 fy W2 regs2 mem2 (AF_cawB + 188)) as HS2. fold E2 in HS2.
pose proof (st_ok_pi_pin_reg' (fx := fy) (L := B_prog_listing) (PI := PA) E2 _ _ 10%bv 0 HS2
  ltac:(cbn [ms_regs restrict YK11.mkst]; rewrite H10, Hran0; reflexivity) eq_refl) as HS3.
clear HS2.
assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; unfold cawO_E0; apply Eimg_env).
assert (SHOK2 : sh_ok SEGS (SOff 32 0) [] E2 (mrestrict (w_H W2) mem2)) by (unfold sh_ok; apply Forall_nil).
assert (HAE2 : env_agree 32 (Ereg regs2 [Z_to_bv 64 SHADOW_OFF]) E2)
  by (subst E2; unfold cawO_E0; split; [intros i Hi; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
(* bnez a0 not taken (a0 = 0); stop at 0x82038 *)
paj_run_to_tok_x_inv RUNTO HS3 HJ2 SHOK2 HPM2 cawO_span (AF_cawB + CAWB_CK).
{ intros a (rg & Hin & _). destruct Hin. }
lazymatch type of HF with frame_of _ ?rs _ _ =>
  pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as EM3 end.
clear HF HFr HG.
lazymatch type of HS3 with st_ok_pi _ _ _ _ (restrict _ ?msn) =>
  rewrite (st_ok_pi_restrict_mkst (fx := fy) (L := B_prog_listing) (PI := PA) (w_H W2) E2 _ msn HS3 eq_refl) end.
cbn [ss_pc].
lazymatch type of HS3 with st_ok_pi _ _ _ _ (restrict _ ?msn) =>
  assert (KD : forall rr, In rr cawO_kept -> getr (ms_regs msn) rr = getr regs2 rr)
  by (eapply (regs_kept_of_st_ok_pi (fx := fy) (L := B_prog_listing) (PI := PA) E2 _ (restrict (w_H W2) msn) regs2
      [Z_to_bv 64 SHADOW_OFF]); [exact HS3 | exact HAE2 | vm_compute; reflexivity]);
  assert (KF : forall rr, In rr cawO_kept -> getr (ms_regs msn) rr = getr regs3 rr)
  by (intros rr Hr; rewrite (KD rr Hr), (cawO_pres _ _ rr HP2)
        by (unfold cawO_kept in Hr; cbn [In] in Hr |- *; tauto); apply KC; exact Hr);
  lazymatch goal with |- context [Z_to_bv 64 (?b + ?p)] =>
    change (Z_to_bv 64 (b + p)) with (Z_to_bv 64 (BASE + (AF_cawB + CAWB_CK))) end;
  apply (KCK fy ly2 S3 Hp3 W2 (ms_regs msn) (ms_mem msn) _ (k + k1) want); [|exact HPM2];
  rewrite EM3 in HJ2 |- *
end.
split; [|split; [|split; [exact Hw | split; [rewrite Eab2; exact Eab | split; [exact Hrp | exact HL2]]]]].
- split; [exact Hfz|]. split; [exact Hfk|]. split; [exact HJ2|].
  split; [intros rr Hr; rewrite <- (Hk rr Hr); apply KF; unfold cawO_kept; cbn [In] in Hr |- *; tauto|].
  split; [unfold spZ; rewrite (KF 2%bv) by (left; reflexivity); exact Hsp|].
  split; [rewrite (KF 8%bv) by (cbn; tauto); exact R8|].
  split; [exact HSV2|]. split; [exact EHp|]. exact HROOM.
- rewrite (KF 18%bv) by (cbn; tauto). exact R18.
Qed.

(* caw_WB4 over RW: the same walk by the R runners and wb4_branchR; the call of fuzz_alloc_ran_out by aj_call_x_spR at
   RW, its text TRO (an SRr fact at wle) lifted by YA0nH.SRr_SRrG and apost_base_x_R_lift *)
Lemma caw_WB4R : forall C P Q, srr_inv_laws SEGS P -> srr_inv_call SEGS P -> caw_pre (fx := fx) B C ->
  caw_K_endR (fx := fx) B (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) C P Q ->
  caw_K_ckR (fx := fx) B (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) C P Q ->
  caw_K_oBR (fx := fx) B (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) C P Q.
Proof.
intros C P Q PLAW PCALL Hpre KEND KCK fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want Hcut HPM.
destruct Hcut as (Hbase & R18 & Hw & Eab & Hrp & HL).
pose proof (PRH_Base.prh_ledger_own B ly3 S3 Hp3 W3 mem3 _ _ _ _ _ _ _ HL) as (Hov & _).
pose proof Hbase as (Hfz & Hfk & HJ & Hk & Hsp & R8 & HSV & EHp & HROOM).
unfold caw_JR in HJ.
pose proof (caw_pre_fpre (fx := fx) B C Hpre) as HFPRE0. pose proof (caw_pre_rc (fx := fx) B C Hpre) as Hrc.
pose proof (caw_pre_ran (fx := fx) B C Hpre) as Hran0.
pose proof HFPRE0 as (HAFN0 & HROD0 & HTOP0 & _).
pose proof HAFN0 as (_ & _ & _ & Hgp0 & Htp0 & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil0 & Hslo0 & Hshi0 & H470 & _ & Htop0 & Htop20).
assert (EST : STK = 26800) by (vm_compute; reflexivity).
assert (ES1 : STK_fuzz_alloc_ran_out (PI := prh_img_B) = 0) by (vm_compute; reflexivity).
assert (EAF : AF_cawB = 2220) by (vm_compute; reflexivity).
pose proof (@pa_B_ok _ _ PA) as HBok.
assert (Hov1 : val_mem SEGS (mrestrict (w_H W3) mem3) (VAL (A_OBJ 13)) 1 0) by (rewrite Hown_obj; exact Hov).
set (E := cawO_E regs3 0).
pose proof (cawO_seat fy W3 regs3 mem3 0 Hov1 ltac:(lia)) as HS. fold E in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold cawO_E; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W3) mem3)) by (unfold sh_ok; apply Forall_nil).
assert (HAE : env_agree 32 (Ereg regs3 [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 0]) E)
  by (subst E; unfold cawO_E; split; [intros i Hi; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (U33 : U E (SExt false 8 (SOff 33 0)) = 0).
{ rewrite U_SExt. cbv beta iota. rewrite U_SOff. subst E. rewrite cawO_E_own, Z.add_0_r, unsigned_lit_small by lia.
  rewrite (zcanon_id 0) by (unfold M64; lia). change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia.
  apply zcanon_id. unfold M64. lia. }
pose (RUN := @paj_run_x_invR fy rc SK B_prog_listing PL_caw_B PA B prh_pst ARcfx _ LAWS P PLAW RW
  (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)).
pose (RUNTO := @paj_run_to_x_invR fy rc SK B_prog_listing PL_caw_B PA B prh_pst ARcfx _ LAWS P PLAW RW
  (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)).
pose (BR := wb4_branchR fy RW).
unfold caw_cfg.
(* auipc / lbu a0, g_own_ran_out / addi s1, zero, 1; stop at `bnez a0` (0x8202c) *)
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM cawO_span (AF_cawB + CAWB_END).
{ intros a (rg & Hin & Ha). cbn in Hin. destruct Hin as [<- | []]. cbn in Ha. lia. }
lazymatch type of HF with frame_of _ ?rs _ _ =>
  pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as EM1 end.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK cawO_span.
{ (* own <> 0: REFUTED, a0 = the atom 33 = cut_oB's ledger own byte 0 (U33) *)
  exfalso. rewrite branch_ne_U, U33, U_SLit in Hc. change (zcanon 0) with 0 in Hc. cbn in Hc. discriminate Hc. }
(* own = 0: the call of fuzz_alloc_ran_out *)
clear Hc.
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM cawO_span (AF_cawB + CAWB_CK).
{ intros a (rg & Hin & Ha). cbn in Hin. destruct Hin as [<- | []]. cbn in Ha. lia. }
lazymatch type of HF with frame_of _ ?rs _ _ =>
  pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as EM2 end.
clear HF HFr HG.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) => rename m into msc end.
assert (Emc : ms_mem msc = mem3) by (rewrite EM2, EM1; reflexivity).
assert (KC : forall rr, In rr cawO_kept -> getr (ms_regs msc) rr = getr regs3 rr)
  by (exact (regs_kept_of_st_ok SEGS E _ _ regs3 [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 0] cawO_kept HS HAE
    ltac:(vm_compute; reflexivity))).
prreg HS (1%bv : bv 5) R1.
assert (Usp : spZ (ms_regs msc) = c_sp C + - CAWB_FRAME).
{ unfold spZ. rewrite (KC 2%bv) by (left; reflexivity). unfold spZ in Hsp. lia. }
(* the journal at RW read by name (YCbqG's ajxR_ projections) *)
pose proof (ajxR_ar HJ) as HAR3. pose proof (ajxR_ly HJ) as Hle3.
destruct Hle3 as (_ & _ & _ & _ & _ & _ & _ & _ & Ltop & _ & Lshi & _).
assert (HROD1 : arodata_okP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview SEGS (w_H W3) (ms_mem msc))).
{ pose proof (ajxR_img HJ) as F3.
  intros a Hro Hno Hne. rewrite (F3 a).
  - exact (HROD0 a Hro Hno Hne).
  - destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hr)].
  - exact Hno.
  - exact Hne.
  - intros Hq. exact (Hpst_rw a Hq Hro).
  - apply fp_spares_closed. intros (x & Hx & _). destruct Hx. }
assert (HTOP1 : spZ (ms_regs msc) + 64 <= ly_stk_hi ly3) by (rewrite Usp, Lshi; unfold c_sp, CAWB_FRAME; lia).
assert (HRAZ1 : raZ (ms_regs msc) < YM05.alloc_ceiling).
{ unfold raZ. rewrite R1, unsigned_lit_small by lia.
  pose proof (pa_slot_lt_ceil_b (PL := PL_caw_B) (PI := PA) (AF_cawB + 188) ltac:(lia)
    ltac:(vm_compute; reflexivity)) as HSL. lia. }
assert (HLED1 : prh_ledger B ly3 S3 Hp3 W3 (ms_mem msc) (c_Lam C) (c_peak C) (c_cnt C) (c_fail C) (c_ran C)
  (c_most C) 0) by (rewrite Emc; exact HL).
(* the call at RW; the callee's text at wle, lifted *)
eapply (YA0nH.SRrG_bind SEGS RW (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)).
{ eapply (aj_call_x_spR (fx := fy) (SK := SK) SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) RW
    (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf) W3 _ _ msc STK (c_sp C) []
    (c_ly C) (c_S C) (c_Hp C) (c_W C) (c_mem C) (c_md C) [] ly3 S3 Hp3 _ k (STK_fuzz_alloc_ran_out (PI := prh_img_B)) []
    (- CAWB_FRAME) _ [] _ HS eq_refl HJ).
  - exact Usp.
  - unfold CAWB_FRAME. reflexivity.
  - unfold CAWB_FRAME. lia.
  - rewrite ES1. lia.
  - rewrite ES1, EST. unfold CAWB_FRAME. lia.
  - rewrite (KC 3%bv) by (cbn; tauto). rewrite (Hk 3%bv) by (cbn; tauto). exact Hgp0.
  - rewrite (KC 4%bv) by (cbn; tauto). rewrite (Hk 4%bv) by (cbn; tauto). exact Htp0.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - rewrite unsigned_lit_small by lia.
    pose proof (cawO_text_lo ly3 S3 Hp3 W3 (ms_mem msc) _ (AF_cawB + 188) HAR3 ltac:(lia)
      ltac:(vm_compute; reflexivity)) as Hlo.
    unfold kImgLo in Hlo. lia.
  - apply (cawO_achain ly3 _ _ (ms_regs msc) (c_rc C)); [rewrite (KC 8%bv) by (cbn; tauto); exact R8 | exact Hrc | lia].
  - intros HPRE1.
    refine (YA0nH.SRrG_mono SEGS RW _ _ _ _
      (YA0nH.SRr_SRrG SEGS RW (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf) _ _ _
        (TRO fy ly3 S3 Hp3 W3 (ms_regs msc) (ms_mem msc) _ [] (c_Lam C) (c_peak C) (c_cnt C) (c_fail C) (c_ran C)
          (c_most C) 0 (conj HPRE1 (conj HROD1 (conj HTOP1 (conj HRAZ1 Hfz)))) HLED1)) _).
    intros W' c' _ H'.
    eapply apost_base_x_R_lift; [exact (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf) | exact H'].
  - intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJc & HP2 & HQ2).
destruct HQ2 as ((_ & H10 & EHp2 & ES2 & Eab2 & HL2) & HKN).
subst Hp2 S2.
assert (HPM2 : P mem2) by exact (PCALL _ _ HKN HPM).
assert (HSV2 : caw_saved C W2 mem2).
{ pose proof (ajxR_hi HJc) as KJc.
  rewrite ES1 in KJc.
  assert (KK : forall a, c_sp C - 32 <= a < c_sp C -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) mem3 a).
  { intros a Ha. rewrite <- Emc. apply KJc; unfold c_sp, CAWB_FRAME in *; lia. }
  destruct HSV as (V1 & V2 & V3 & V4).
  split; [|split; [|split]]; (eapply val_mem_kept; [|eassumption]); intros kk Hkk; apply KK; cbn in Hkk; lia. }
lazymatch goal with |- YA0nH.SRrG _ _ _ {| cfg_ms := YK11.mkst _ ?raw _ _ |} _ =>
  change raw with (Z_to_bv 64 (BASE + (AF_cawB + 188))) end.
set (E2 := cawO_E0 regs2).
pose proof (cawO_seat0 fy W2 regs2 mem2 (AF_cawB + 188)) as HS2. fold E2 in HS2.
pose proof (st_ok_pi_pin_reg' (fx := fy) (L := B_prog_listing) (PI := PA) E2 _ _ 10%bv 0 HS2
  ltac:(cbn [ms_regs restrict YK11.mkst]; rewrite H10, Hran0; reflexivity) eq_refl) as HS3.
clear HS2.
assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; unfold cawO_E0; apply Eimg_env).
assert (SHOK2 : sh_ok SEGS (SOff 32 0) [] E2 (mrestrict (w_H W2) mem2)) by (unfold sh_ok; apply Forall_nil).
assert (HAE2 : env_agree 32 (Ereg regs2 [Z_to_bv 64 SHADOW_OFF]) E2)
  by (subst E2; unfold cawO_E0; split; [intros i Hi; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
(* bnez a0 not taken (a0 = 0); stop at 0x82038 *)
paj_run_to_tok_x_inv RUNTO HS3 HJ2 SHOK2 HPM2 cawO_span (AF_cawB + CAWB_CK).
{ intros a (rg & Hin & _). destruct Hin. }
lazymatch type of HF with frame_of _ ?rs _ _ =>
  pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as EM3 end.
clear HF HFr HG.
lazymatch type of HS3 with st_ok_pi _ _ _ _ (restrict _ ?msn) =>
  rewrite (st_ok_pi_restrict_mkst (fx := fy) (L := B_prog_listing) (PI := PA) (w_H W2) E2 _ msn HS3 eq_refl) end.
cbn [ss_pc].
lazymatch type of HS3 with st_ok_pi _ _ _ _ (restrict _ ?msn) =>
  assert (KD : forall rr, In rr cawO_kept -> getr (ms_regs msn) rr = getr regs2 rr)
  by (eapply (regs_kept_of_st_ok_pi (fx := fy) (L := B_prog_listing) (PI := PA) E2 _ (restrict (w_H W2) msn) regs2
      [Z_to_bv 64 SHADOW_OFF]); [exact HS3 | exact HAE2 | vm_compute; reflexivity]);
  assert (KF : forall rr, In rr cawO_kept -> getr (ms_regs msn) rr = getr regs3 rr)
  by (intros rr Hr; rewrite (KD rr Hr), (cawO_pres _ _ rr HP2)
        by (unfold cawO_kept in Hr; cbn [In] in Hr |- *; tauto); apply KC; exact Hr);
  lazymatch goal with |- context [Z_to_bv 64 (?b + ?p)] =>
    change (Z_to_bv 64 (b + p)) with (Z_to_bv 64 (BASE + (AF_cawB + CAWB_CK))) end;
  apply (KCK fy ly2 S3 Hp3 W2 (ms_regs msn) (ms_mem msn) _ (k + k1) want); [|exact HPM2];
  rewrite EM3 in HJ2 |- *
end.
split; [|split; [|split; [exact Hw | split; [rewrite Eab2; exact Eab | split; [exact Hrp | exact HL2]]]]].
- split; [exact Hfz|]. split; [exact Hfk|]. split; [exact HJ2|].
  split; [intros rr Hr; rewrite <- (Hk rr Hr); apply KF; unfold cawO_kept; cbn [In] in Hr |- *; tauto|].
  split; [unfold spZ; rewrite (KF 2%bv) by (left; reflexivity); exact Hsp|].
  split; [rewrite (KF 8%bv) by (cbn; tauto); exact R8|].
  split; [exact HSV2|]. split; [exact EHp|]. exact HROOM.
- rewrite (KF 18%bv) by (cbn; tauto). exact R18.
Qed.

End f.
End d.

Print Assumptions caw_WB4a.
Print Assumptions caw_WB4.
Print Assumptions caw_WB4aR.
Print Assumptions caw_WB4R.
