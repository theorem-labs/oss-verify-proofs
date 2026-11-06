(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: segment C2ref of pj_parse's image-B' walk (fuzz_preset asan-ubsan, B' 0x862ec; the cuts of lib/B/Prog/pj_parse_defs.v,
   the kit cut preset-tree-at-2026-10-30T04-57-22Z.tsv (sha256 652fe98064b9; internal record)): from PJP_C2REF (+0x68) to PJP_C3 (+0x74), the refusal path
     +0x68  mv a0, s0        a0 := out
     +0x6c  jal pj_free      the kit's tpj_free_specX CTX0 DOC_D by YCbqGcallW.v aj_call_xW at callee window e1 = 0
                             (v = out <> 0, D = parse_value's new blocks, F its order list, Lam = Lam' = D ++ Lam_entry)
     +0x70  li a0, -1
   then pjp_seg_C3 (a Section-free premise, as every later segment). The three instructions are stepped concretely
   (YA0n.v SRr_step with YK14.v step_addi_at / step_jal_link; the words are read from the image table PI_prog_B,
   certified by the listing, and decoded by computation), so the memory does not move before the call.
   After the call: pjp_frame_kept_stmt (the caller window, the saved ra / s0, the frame, the cursor's shadow, the
   read-only view), the callee-saved registers by aregs_preserved, and the text's post's None arm: res := None
   (pjp_g_run with post res = None), Lam_final ~ Lam_entry (Permutation_app_inv_l over pj_free's ledger move and
   rd_ledger_move's), ablocks_final ~ ablocks_entry (rd_blocks_move, pj_free, pjp_g_ab_hbl), pj_zeroR out from
   pj_free's v <> 0 arm, the counters unchanged by pj_free.
   THE OPEN SITE OF THE EARLIER WALK IS CLOSED AGAINST THE KIT's TEXTS: pj_free (out) is the kit's tpj_free_specX (lib/A/PRH_FnPj.v
   blob 5aca5cbe2cfb :749-805, POST-IMPLICATION form, the order list F IN pj_free's ORDER, PRH_PjOrder.pj_foR); its
   class-24 bound (:761, under out <> 0) comes from the text's L24 premise through the cut's live-set move
   (pj_parse_counts.v pjc_cnt_run_parse); its prh_head_wide (:775) from the walk's prh_head16 (cf_head = HEAD = 16).
   The F and its tie `map (fun b => snd b + cf_head) F = PresetReqAt.pj_frees ok tl` are no named premise any more:
   they are the kit's parse_value post (the trees' free order, prhPv_frees 0 tl ok = pj_frees ok tl), carried by the cuts.
   The text's position transfer on the refused path (E = parse_value's events then the HBulk of pj_frees ok tl)
   closes through pj_free's transfer over prhPj_free_evs F (prhPj_free_evs_supply from the tie; at F = [] by stepping
   over the model's HBulk [], prhPj_bulk_nil_pos). The kit's OUTCOME conjunct closes by parse_value's outcome (the
   cut's pjp_outc) and pj_parse_frees.v pjf_frees_same (the refusal's HBulk under ok is the all-granted one).
   The memory overlay's normal form at C3 is pj_free's m-form keep (fpostWm) applied to the cut's (pjp_inv); fpre's
   return-address bound is the jal's own return site and its frm_zero (FRM0-ENTRY) the cut's.
   THE RE-HIDING MOVE AND THE HULL: pj_free's text concludes SRr' segs RZ_cf with its post at wle' (fpostWmR), and the
   cut's journal is at wle' (pjp_invR), so the call is YCbqGcallW.aj_call_xWR at wle' SEGS RZ_cf and the segment
   concludes SRr'; the three steps are SRr steps, lifted (YGcfRhLift.ra_rh_of_SRr). pj_free (out)'s hull budget
   hull_budget S [] is what pj_parse's budget leaves after parse_value's use (pj_parse_counts.v
   pjc_hull_budget_after_pv, from pjp_pre's budget and the cut's hull use); the text's hull use at C3 is parse_value's
   then pj_free's (none), widened to pj_parse's list (pjc_hull_used_pv).
   THE OUTCOME OF AN INJECTED READING (the text's GUARDED conjunct): parse_value's conjunct (the cut's pjp_inj), whose
   run list is the first part of pj_parse's under the same grant list (the refusal's HBulk follows it).
   proves no function (kind: segment lemma).
   Numerals: 48 / 56 / 32 / 16 / 64 / 4096 (LENGTH: pj_parse's frame, the struct pj, the cursor end, alignment, fpre's
   stack margin, the null page); 4 / 8 (DERIVED pc offsets of the next instruction); 224 / 512 / 16384 / 32 (DERIVED:
   the texts' peak bounds, MAXD); 2 ^ 40 / 2 ^ 64 (DERIVED bounds); register numbers 0, 1, 2, 3, 4, 8, 10 (WORD).
   No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YCbqGcallW FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost YGcfRhLift.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnPj PRH_FnParse.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import pj_parse_defs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require pj_parse_counts.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import pj_parse_glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt PresetRun PresetRoom PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive YGcfRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_PjOrder.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Open Scope Z_scope.
#[local] Existing Instance prh_img_B.

(* ---- small tactics: register disequality, callee-saved membership, the word at an offset and its decoding ---- *)
Ltac pjr_regne :=
  let E := fresh "E" in
  intros E; apply (f_equal (fun x : bv 5 => bv_unsigned x)) in E; vm_compute in E; discriminate E.
Ltac pjr_cs :=
  lazymatch goal with |- acallee_saved (bv_unsigned ?x) =>
    let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end;
  unfold acallee_saved; lia.
Ltac pjr_fd k Hl Hd :=
  let r := eval vm_compute in
    (clookup (@pa_tbl _ B_prog_listing PI_prog_B) (@pa_val _ B_prog_listing PI_prog_B A_TEXT + k)) in
  lazymatch r with
  | Some ?w =>
    assert (Hl : clookup (@pa_tbl _ B_prog_listing PI_prog_B) (@pa_val _ B_prog_listing PI_prog_B A_TEXT + k) = Some w)
      by (vm_compute; reflexivity);
    let dz := eval vm_compute in (decode_any (Z_to_bv 32 w)) in
    assert (Hd : decode_any (Z_to_bv 32 w) = dz) by (vm_compute; reflexivity)
  | _ => fail "pjr_fd: no image word at offset" k
  end.

(* ---- register facts ---- *)
Lemma pjr_getr2 : forall regs (r1 r2 r : bv 5) v1 v2, r <> r1 -> r <> r2 ->
  getr (regupd (regupd regs r1 v1) r2 v2) r = getr regs r.
Proof. intros regs r1 r2 r v1 v2 H1 H2. rewrite !getr_other by assumption. reflexivity. Qed.

Lemma pjr_pres : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). exact (HP _ Hr). Qed.

Lemma pjr_kept_facts : forall r, In r PJP_KEPT -> r <> (10%bv : bv 5) /\ r <> (1%bv : bv 5) /\ acallee_saved (bv_unsigned r).
Proof.
intros r Hr. unfold PJP_KEPT in Hr.
repeat (destruct Hr as [<- | Hr]; [split; [pjr_regne | split; [pjr_regne | pjr_cs]] |]).
all: try destruct Hr.
Qed.

(* ---- one concrete step at a listing offset k of image B: addi (mv / li) and jal ---- *)
Section h. Context {rc : YM05.RunCeil}.
#[local] Notation PA := PI_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).

Lemma pjr_step_addi : forall (fy : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k : Z) w (rd rs : bv 5) (imm : bv 12) (rd' : bv 5) (v : word),
  clookup (@pa_tbl _ B_prog_listing PA) (BASE + k) = Some w ->
  decode_any (Z_to_bv 32 w) = Some (OpImm ALU_ADD rd rs imm, 4%Z) ->
  bv_eqb rd (0%bv : bv 5) = false -> rd = rd' ->
  v_addi (getr regs rs) (bv_signed imm) = v ->
  (forall X, SRr SEGS W (mkCfg (@YK11.mkst fy (regupd regs rd' v) (v_addi (Z_to_bv 64 (BASE + k)) 4) mem
     (YK11.seg_rom SEGS)) (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (mkCfg (@YK11.mkst fy regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros fy W regs mem md Q k w rd rs imm rd' v Hl Hd Hrd Erd Hv HK. subst rd'.
eapply (SRr_step SEGS (@pa_wx _ B_prog_listing PA) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fy)).
  exact (step_addi_at (fx := fy) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
    (Z_to_bv 32 w) rd rs imm v (pa_fetch_ok (PI := PA) _ _ Hl) (not_ecall_of_decode _ _ _ Hd ltac:(discriminate))
    Hd Hrd Hv).
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fy)). apply HK.
Qed.

Lemma pjr_step_jal : forall (fy : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k : Z) w (rd : bv 5) (imm : bv 21) (rd' : bv 5) (ra pc' : word),
  clookup (@pa_tbl _ B_prog_listing PA) (BASE + k) = Some w ->
  decode_any (Z_to_bv 32 w) = Some (Jal rd imm, 4%Z) ->
  bv_eqb rd (0%bv : bv 5) = false -> rd = rd' ->
  v_addi (Z_to_bv 64 (BASE + k)) 4 = ra ->
  btgt (Z_to_bv 64 (BASE + k)) (bv_signed imm) = pc' ->
  (forall X, SRr SEGS W (mkCfg (@YK11.mkst fy (regupd regs rd' ra) pc' mem (YK11.seg_rom SEGS))
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (mkCfg (@YK11.mkst fy regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros fy W regs mem md Q k w rd imm rd' ra pc' Hl Hd Hrd Erd Era Hpc HK. subst rd' ra pc'.
eapply (SRr_step SEGS (@pa_wx _ B_prog_listing PA) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fy)).
  rewrite (step_jal_link (fx := fy) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
    (Z_to_bv 32 w) rd imm (pa_fetch_ok (PI := PA) _ _ Hl) (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd).
  rewrite Hrd. cbv beta iota. reflexivity.
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fy)). apply HK.
Qed.
End h.

(* ---- the segment ---- *)
Section c2r. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation PST := (prh_pst (PI := prh_img_B)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
(* the allocator laws the call rule and the journal's materialisation take (YCbqG.v AR_laws_x, head length HL) *)
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.
(* the glue facts this segment uses (pj_parse_defs.v; proved in lib/B/Prog/pj_parse_glue.v) *)
Hypothesis G_RUN : pjp_g_run.
Hypothesis G_NOREFUSE : pjp_g_norefuse.
Hypothesis G_CALLS : pjp_g_calls.
Hypothesis G_FAIL_AFTER : pjp_g_fail_after.
Hypothesis G_AB_HBL : pjp_g_ab_hbl.
(* CFHEAD-16, the walk's Section hypothesis (PRH_Base.v prh_head16; reflexivity at CfParams_preset): it gives
   pj_free's prh_head_wide (8 <= cf_head) *)
Hypothesis HH : prh_head16.
(* pj_free's order list under ok IS the all-granted one when the reading under ok is the all-granted reading
   (lib/B/Prog/pj_parse_frees.v pjf_frees_same, a pure model lemma) *)
Hypothesis G_FREES : forall (sm : list Z -> Z * Z) (x : list Z) (ok : list bool) res tr okr,
  PjGrammar.jr_value sm 0 x ok = (res, tr, okr) ->
  fst (PjGrammar.jr_value sm 0 x []) = (res, tr) ->
  PresetReqAt.pj_frees sm ok x = PresetReqAt.pj_frees sm [] x.

Theorem pjp_seg_C2ref_holds : forall CTX0 CW,
  pjp_texts B ARx CTX0 CW -> pjp_frame_kept_stmt B ARx -> pjp_seg_C3 B ARx CTX0 CW -> pjp_seg_C2ref B ARx CTX0 CW.
Proof.
intros CTX0 CW TXT KEEP HC3.
destruct TXT as (_ & _ & PJFREE & _).
unfold pjp_seg_C2ref. intros en Sb fy ly S Hp W regs mem md k HPRE HWB HC2.
(* the base state is the entry's with its depot moved (pjp_wb): its blocks are the entry's, by conversion *)
pose proof HWB as (dp & WS & ESb & _ & _). subst Sb.
pose proof (@pa_segs_low _ B_prog_listing PA) as Hsegs.
(* ---- the entry's facts ---- *)
pose proof HPRE as (HFPRE & HUNIV & _ & _ & _ & _ & _ & _ & _ & Hlen & _ & _ & _ & HFWIN & _ & _ & _ & _ & HLED0 &
  HCNT & _ & _ & _ & _ & _ & HPK24 & _ & _ & HHB0).
pose proof HFPRE as ((HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & Hqt0) & HROD0 & HSTKHI0 & _ & _).
pose proof Hstk0 as (Hal0 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop0 & Htop20).
pose proof HFWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof HLED0 as HLB0. apply prh_ledger_bounds in HLB0. destruct HLB0 as (_ & _ & [Hc0a Hc0b] & _ & _).
(* ---- the cut's facts ---- *)
destruct HC2 as (HINV & HROOM & HHUSE & ok & res & tr & D & F & Lam' & peak' & cnt' & fail' & ran' & HPV & HPOSPV &
  HOUTC & Hpost & HFO & HTIEF & HOUT & HINJ).
pose proof HINV as (Hfz & Hfk & HJ & Hwin & Hsp & Hra & Hs0 & H8 & Hkept & Hfpres & Hcur & Hrod & HMN).
destruct HPV as ((okr & Hjr) & HLED & HLM & HBM).
destruct HLM as (Hoks & Hcnt & Hfa & HpLam & Hsz & Hlsz & Hpeak).
destruct HBM as (Hnew & Hab & Hfrs & Hhp).
pose proof HOUT as (Hout4 & Houtc & Hplace & HoutLam & Hrw & Hamr & Hown & HRA & HHULL).
(* pj_free (out)'s class-24 bound (PRH_FnPj.v (sha256 5a71fd48f3a8; internal record) :619), position-free: the live set at this cut is the entry's moved by
   parse_value's events (the cut's pjp_pos_pv), inside the all-granted peak (pj_parse_counts.v pjc_cnt_run_parse) that
   the text's added L24 premise bounds *)
assert (HC24 : YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV).
{ pose proof (pj_parse_counts.pjc_cnt_run_parse ReaderRes.jr_strtod (PresetRoom.in_cls YG00.kBatchClass)
    (PresetRoom.rs_live (YGcfRoom.room_of_cf (je_S en))) (je_tl en) ok res tr okr Hjr) as Hc.
  rewrite <- (PresetReqAt.cnt_perm _ _ _ (proj2 HPOSPV)) in Hc.
  change (YGcfRoomLive.ccnt24 S) with
    (Z.of_nat (PresetReqAt.cnt (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf S)))).
  clear - Hc HPK24; lia. }
pose proof HJ as (HAR & Hly & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
(* ---- the stack numbers at prh_img_B ---- *)
assert (HSTKF : 0 <= STK_pj_free DOC_D) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HSTKB : STK_pj_free DOC_D + 48 <= STK_pj_parse) by (apply Z.leb_le; vm_compute; reflexivity).
assert (Hne0 : (je_out en =? 0) = false) by (apply Z.eqb_neq; lia).
(* ---- out and D's blocks lie below alloc_ceiling ---- *)
assert (HOUTLOW : je_out en + 56 <= YM05.alloc_ceiling).
{ destruct Hplace as [(b & m & Hbin & _ & Hb1 & Hb2) | (cid & pos & Hfin & Hf1 & Hf2)].
  - destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hbin) as (_ & _ & Hc & _).
    assert (Hm : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia). lia.
  - destruct (alx_sep SEGS B ARx LAWS _ _ _ _ _ _ HAR) as (_ & HF).
    pose proof (proj1 (Forall_forall _ _) HF (cid, pos) Hfin) as (_ & Hf). cbn [fst snd] in Hf. lia. }
assert (HDB : forall a' k', In (a', k') D -> In (a' - cf_head, k' + cf_head) (ablocks B ly S)).
{ intros a' k' Hin. eapply Permutation_in; [exact (Permutation_sym Hab) |]. apply in_or_app. left.
  unfold prhReader_ab. apply in_map_iff. exists (a', k'). split; [reflexivity | exact Hin]. }
assert (HFPD : forall a, inFP (ablocks_fp (prhPj_hbl D)) a ->
  exists a' k', In (a', k') D /\ a' - cf_head <= a < a' - cf_head + req_size (k' + cf_head)).
{ intros a (r & Hr & Hra'). unfold ablocks_fp, prhPj_hbl in Hr. rewrite map_map in Hr.
  apply in_map_iff in Hr as ((a' & k') & <- & Hin). cbn [fst snd] in Hra'. exists a', k'. split; [exact Hin | exact Hra']. }
(* ======== +0x68  mv a0, s0 ======== *)
unfold pjp_cfg.
(* the steps before the call are SRr steps: lifted once into SRr' SEGS RZ_cf, the continuations' relation *)
apply (YGcfRhLift.ra_rh_of_SRr SEGS YGcfRehidePost.RZ_cf).
pjr_fd PJP_C2REF Hl1 Hd1.
eapply (pjr_step_addi fy W regs mem md _ PJP_C2REF _ _ _ _ (10%bv : bv 5) (getr regs (8%bv : bv 5)) Hl1 Hd1).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ lazymatch goal with |- v_addi (getr _ ?rs) (bv_signed ?im) = _ =>
    replace rs with (8%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity);
    replace (bv_signed im) with 0 by (vm_compute; reflexivity) end.
  unfold v_addi. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. }
intros X1.
pose proof (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs (wle' SEGS YGcfRehidePost.RZ_cf)
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1 HJ) as HJ1.
replace (v_addi (Z_to_bv 64 (BASE + PJP_C2REF)) 4) with (Z_to_bv 64 (BASE + (PJP_C2REF + 4)))
  by (apply bv_eq; vm_compute; reflexivity).
(* ======== +0x6c  jal pj_free ======== *)
pjr_fd (PJP_C2REF + 4) Hl2 Hd2.
eapply (pjr_step_jal fy W _ mem _ _ (PJP_C2REF + 4) _ _ _ (1%bv : bv 5) (Z_to_bv 64 (BASE + (PJP_C2REF + 8)))
  (Z_to_bv 64 (@pa_sigma _ B_prog_listing PA AS_pj_free)) Hl2 Hd2).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X2.
pose proof (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs (wle' SEGS YGcfRehidePost.RZ_cf)
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X2 HJ1) as HJ2.
apply SRr_ret. cbv beta.
lazymatch goal with |- SRr' _ _ _ (mkCfg (@YK11.mkst _ ?r _ _ _) ?m) _ =>
  remember r as regsc eqn:Eregsc; set (mdc := m) in * end.
set (FP1 := if je_out en =? 0 then [] else (je_out en, je_out en + 56) :: ablocks_fp (prhPj_hbl D)).
assert (HFP1 : forall a, inFP FP1 a -> (je_out en <= a < je_out en + 56) \/
  exists a' k', In (a', k') D /\ a' - cf_head <= a < a' - cf_head + req_size (k' + cf_head)).
{ intros a Ha. unfold FP1 in Ha. rewrite Hne0 in Ha.
  change (inFP ((je_out en, je_out en + 56) :: ablocks_fp (prhPj_hbl D)) a) in Ha. apply inFP_cons in Ha.
  destruct Ha as [Ha | Ha]; [left; exact Ha | right; exact (HFPD a Ha)]. }
(* the call state's registers *)
assert (HSPC : spZ regsc = je_sp1 en).
{ unfold YG0d.spZ at 1. rewrite Eregsc, pjr_getr2 by pjr_regne. exact Hsp. }
assert (HS0LOW : s0Z regsc < YM05.alloc_ceiling).
{ unfold YG0d.s0Z. rewrite Eregsc, pjr_getr2 by pjr_regne. rewrite H8. try unfold w64.
  rewrite unsigned_lit_small by lia. lia. }
assert (HGP : getr regsc 3 = w64 (as_gp B)).
{ rewrite Eregsc, pjr_getr2 by pjr_regne. rewrite (Hkept 3%bv) by (unfold PJP_KEPT; left; reflexivity). exact Hgp0. }
assert (HTP : getr regsc 4 = w64 (as_tp B)).
{ rewrite Eregsc, pjr_getr2 by pjr_regne. rewrite (Hkept 4%bv) by (unfold PJP_KEPT; right; left; reflexivity).
  exact Htp0. }
assert (HRA1 : getr regsc 1 = Z_to_bv 64 (BASE + (PJP_C2REF + 8))) by (rewrite Eregsc; apply getr_same; pjr_regne).
assert (HRAW : YK0s.ret_ok (Z_to_bv 64 (BASE + (PJP_C2REF + 8)))).
{ apply (YC1fP.ret_ok_codeptr_v (PI := PA)); [split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity |].
  vm_compute. reflexivity. }
assert (HRA4 : 4096 <= bv_unsigned (Z_to_bv 64 (BASE + (PJP_C2REF + 8)))) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HSPO : spZ regsc = je_sp0 en + je_d en + (-48 - je_d en)) by (rewrite HSPC; unfold je_sp1, PJP_FR; lia).
assert (Hal : (-48 - je_d en) mod 16 = 0) by lia.
assert (Hneg : -48 - je_d en <= 0) by lia.
assert (Hbud : STK_pj_free DOC_D - (-48 - je_d en) <= STK_pj_parse + je_d en) by lia.
assert (He0 : 0 <= 0) by lia.
assert (Hetop : -48 - je_d en + 0 <= 0) by lia.
(* fpre's return-address bound: the `jal pj_free` return site, a code address below the shadow *)
assert (HRAc : raZ regsc < YM05.alloc_ceiling).
{ pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5).
  assert (HB : 0 <= BASE + (PJP_C2REF + 8) < kLowMemEnd)
    by (split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity).
  unfold raZ. rewrite HRA1, unsigned_lit_small by (rewrite CA5 in HB; lia). lia. }
(* pj_free (out)'s hull budget: pj_parse's budget less parse_value's use (pj_parse_counts.v) *)
assert (HHBF : PresetHullBudget.hull_budget S []).
{ exact (pj_parse_counts.pjc_hull_budget_after_pv ReaderRes.jr_strtod cp (je_S en) S (je_tl en) HHB0 HHUSE). }
(* ======== the call: pj_free's text at the callee window e1 = 0, by the rule over R at wle' SEGS RZ_cf ======== *)
eapply (SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ eapply (aj_call_xWR (fx := fy) (SK := SK) SEGS B PST ARx LAWS Hsegs (wle' SEGS YGcfRehidePost.RZ_cf)
    (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)
    W regsc mem (@pa_sigma _ B_prog_listing PA AS_pj_free)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (STK_pj_free DOC_D) 0 FP1 (-48 - je_d en) (Z_to_bv 64 (BASE + (PJP_C2REF + 8))) [] _
    HJ2 HSPO Hal Hneg HSTKF Hbud He0 eq_refl Hetop HGP HTP HRA1 HRAW HRA4 (achain_low _ _ _ _ HS0LOW)).
  - (* the callee: the kit's tpj_free_specX CTX0 DW DOC_D at d = 0, v = out, D, its order list F, Lam = Lam' *)
    intros HPRE1 HWIN1. unfold fpostW_xR.
    eapply (PJFREE fy (je_most en) (je_own en) ly S Hp W regsc mem _ [] 0 (je_out en) D F Lam' peak' cnt' fail' ran').
    + split; [exact HPRE1|]. split; [exact Hrod|].
      split; [rewrite HSPC, Eshi; unfold je_sp1, PJP_FR, je_sp0; lia | split; [exact HRAc | exact Hfz]].
    + exact HUNIV.
    + exact HROOM.
    + intros _. exact HC24.
    + intros _. exact HHBF.
    + rewrite Eregsc, getr_other, getr_same by pjr_regne. exact H8.
    + exact HWIN1.
    + right. split; [lia|]. split; [exact Houtc|]. split; [exact HFO|].
      split; [exact Hout4|].
      split; [destruct Hplace as [Hb | Hf]; [right; left; exact Hb | right; right; left; exact Hf]|].
      split; [exact Hrw|]. split; [exact Hamr|].
      split; [intros a Ha; split; [exact (Hown a Ha) | rewrite HSPC; unfold je_sp1, PJP_FR, je_sp0; lia]|].
      split; [exact HRA | exact HHULL].
    + unfold prh_head_wide. rewrite HH. unfold PresetReqAt.HEAD. lia.
    + exact HLED.
  - (* the footprint: out's header is the caller's FP, D's blocks are blocks made since the entry *)
    intros a Ha. destruct (HFP1 a Ha) as [Ho | (a' & k' & Hin & Hr)].
    + left. exists (je_out en, je_out en + 56). split; [left; reflexivity | cbn [fst snd]; lia].
    + right; left. exists (a' - cf_head), (k' + cf_head).
      split; [exact (HDB a' k' Hin)|]. split; [exact (Hnew a' k' Hin) | exact Hr]. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2' & HJc & HX & HP2 & HK).
unfold fQmn in HK. cbv beta in HK.
destruct HK as ((HROOM2 & HHUF & HPFP & LamF & HpF & HabF & HLEDF & _ & HZ & _) & HMK2).
(* ======== +0x70  li a0, -1 ======== *)
apply (YGcfRhLift.ra_rh_of_SRr SEGS YGcfRehidePost.RZ_cf).
pjr_fd (PJP_C2REF + 8) Hl3 Hd3.
eapply (pjr_step_addi fy W2 regs2 mem2 md2 _ (PJP_C2REF + 8) _ _ _ _ (10%bv : bv 5) (w64 (-1)) Hl3 Hd3).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X3.
replace (v_addi (Z_to_bv 64 (BASE + (PJP_C2REF + 8))) 4) with (Z_to_bv 64 (BASE + PJP_C3))
  by (apply bv_eq; vm_compute; reflexivity).
apply SRr_ret. cbv beta.
(* ======== PJP_C3: the later segment ======== *)
apply (HC3 en (set_depot dp (je_S en)) fy ly2 S2 Hp2 W2 (regupd regs2 (10%bv : bv 5) (w64 (-1))) mem2 (with_vm_backing (m_vm_lazy md2) X3 md2)
  (k + k1) HPRE HWB).
(* what pj_parse's frame keeps across the call (pjp_frame_kept_stmt at e1 = 0) *)
replace (je_sp0 en + je_d en + (-48 - je_d en) + 0) with (je_sp1 en + 0) in HJc by (unfold je_sp1, PJP_FR; lia).
pose proof (KEEP en (set_depot dp (je_S en)) fy ly S Hp W regsc mem mdc k (STK_pj_free DOC_D) 0 FP1 ly2 S2 Hp2 W2
  mem2 md2 k1 []) as KK.
lazymatch type of KK with ?P -> _ => assert (HINVc : P) end.
{ split; [exact Hfz|]. split; [exact Hfk|]. split; [exact HJ2|]. split; [exact Hwin|]. split; [exact HSPC|].
  split; [exact Hra|]. split; [exact Hs0|].
  split; [rewrite Eregsc, pjr_getr2 by pjr_regne; exact H8|].
  split; [intros r Hr; destruct (pjr_kept_facts r Hr) as (Hr10 & Hr1 & _);
          rewrite Eregsc, pjr_getr2 by assumption; exact (Hkept r Hr)|].
  split; [exact Hfpres|]. split; [exact Hcur|]. split; [exact Hrod | exact HMN]. }
assert (HSINK : ~ YI16.sink_open_fp FP1).
{ unfold FP1. rewrite Hne0. change (~ YI16.sink_open_fp ((je_out en, je_out en + 56) :: ablocks_fp (prhPj_hbl D))).
  apply sink_closed_cons; [cbn [fst]; lia|]. apply sink_closed_pos. apply Forall_forall.
  intros r Hr. unfold ablocks_fp, prhPj_hbl in Hr. rewrite map_map in Hr.
  apply in_map_iff in Hr as ((a' & k') & <- & Hin). cbn [fst].
  destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR (HDB a' k' Hin)) as (_ & H4096 & _). lia. }
assert (HFPOUT : forall a, inFP FP1 a -> ~ (je_sp1 en + 32 <= a < je_sp0 en + je_d en)).
{ intros a Ha. assert (Hlow : a < YM05.alloc_ceiling).
  { destruct (HFP1 a Ha) as [Ho | (a' & k' & Hin & Hr)]; [lia|].
    destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR (HDB a' k' Hin)) as (_ & _ & Hc & _). lia. }
  unfold je_sp1, PJP_FR, je_sp0. lia. }
destruct (KK HINVc HJc HSTKF ltac:(lia) Hd0 HSINK HFPOUT) as (KW & KRA & KS0 & KPR & KCUR & KROD).
split.
- (* pjp_inv at PJP_C3 *)
  split; [exact Hfz|]. split; [exact Hfk|].
  split; [exact (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs (wle' SEGS YGcfRehidePost.RZ_cf)
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X3 HJ2')|].
  split; [exact KW|].
  split; [unfold YG0d.spZ at 1; rewrite getr_other by pjr_regne; rewrite (pjr_pres regsc regs2 _ HP2) by pjr_cs;
          exact HSPC|].
  split; [exact KRA|]. split; [exact KS0|].
  split; [rewrite getr_other by pjr_regne; rewrite (pjr_pres regsc regs2 _ HP2) by pjr_cs;
          rewrite Eregsc, pjr_getr2 by pjr_regne; exact H8|].
  split; [intros r Hr; destruct (pjr_kept_facts r Hr) as (Hr10 & Hr1 & Hrc); rewrite getr_other by exact Hr10;
          rewrite (pjr_pres regsc regs2 r HP2 Hrc); rewrite Eregsc, pjr_getr2 by assumption; exact (Hkept r Hr)|].
  split; [exact KPR|]. split; [exact KCUR|]. split; [exact KROD|].
  (* the memory overlay at C3: pj_free's keep; the `li a0, -1` stores nothing *)
  exact (HMK2 HMN).
- (* the text's post, the None arm *)
  split; [exact HROOM2|].
  (* the hull use: parse_value's (the cut's), then pj_free's (none), inside pj_parse's list *)
  split; [apply (pj_parse_counts.pjc_hull_used_pv ReaderRes.jr_strtod);
          pose proof (PresetHullBudget.hull_used_app _ _ _ _ _ HHUSE HHUF) as U; rewrite app_nil_r in U; exact U|].
  exists ok, None, tr, LamF, peak', cnt', fail', ran'.
  split; [rewrite (G_RUN _ _ _ _ _ Hjr), Hpost; reflexivity|].
  split; [exact Hoks|].
  split; [rewrite Hcnt; apply Z.mod_small; pose proof (G_CALLS _ _ _ _ _ Hjr) as Hc; lia|].
  split; [apply G_FAIL_AFTER; exact Hfa|].
  split; [rewrite <- (pjg_gtrace (je_tl en)); exact Hpeak|].
  split; [assert (EM : Z.of_nat (PjGrammar.MAXD - 0) = 32) by reflexivity; lia|].
  split; [intros _; reflexivity|].
  split; [intros H1 H2; destruct (G_NOREFUSE _ _ _ _ _ _ _ Hjr H1 H2) as [E1 E2];
          split; [rewrite <- E1, Hpost; reflexivity | exact E2]|].
  split; [exact HLEDF|].
  (* the text's position transfer on the refused path: E = parse_evs tl ok = parse_value's events then the HBulk of
     pj_frees ok tl (PresetReqAt.v:300-305, post res = None). parse_value's transfer (the cut's pjp_pos_pv) takes the
     position to this cut's S after the reader's events; pj_free's transfer (its post, PRH_FnPj.v :794-798) moves
     it by prhPj_free_evs F from the run premise prhPj_free_evs_supply gives over the model's HBulk, by the cut's
     tie (map (fun b => snd b + cf_head) F = pj_frees ok tl, IN ORDER; parse_value's post); at F = [] the model's bulk
     is empty, pj_free makes no event, and the model's HBulk [] is stepped over (prhPj_bulk_nil_pos). The step is
     shared by the unconditional transfer and the outcome conjunct (HSTEP). *)
  assert (HSTEP : forall sm x os i H0 h2,
    PresetRoomPos.iface_room_pos sm x os i H0 h2 S ->
    PRH_Base.prh_run_at sm x os i [PresetReqAt.HBulk (PresetReqAt.pj_frees ReaderRes.jr_strtod ok (je_tl en))] ->
    exists h3, PresetRoomPos.iface_room_pos sm x os (i + 1)%nat H0 h3 S2).
  { intros sm x os i H0 h2 Hpos2 Hrun2.
    pose proof (prhPj_free_evs_supply sm x os _ F _ HTIEF Hrun2) as Hrun3.
    destruct (HPFP sm x os _ H0 h2 Hpos2 Hrun3) as (h3 & Hpos3).
    destruct F as [|b F'].
    - cbn [map] in HTIEF. rewrite <- HTIEF in Hrun2.
      cbn [prhPj_free_evs length] in Hpos3. rewrite Nat.add_0_r in Hpos3.
      apply prh_run_at_one in Hrun2.
      exists h3. replace (i + 1)%nat with (Datatypes.S i) by (clear; lia).
      exact (proj1 (prhPj_bulk_nil_pos sm x os _ H0 h3 S2 Hrun2) Hpos3).
    - cbn [prhPj_free_evs length] in Hpos3. exists h3. exact Hpos3. }
  assert (Ep : PresetReqAt.parse_evs ReaderRes.jr_strtod (je_tl en) ok =
               PresetReqAt.rd_hevs tr ++
               [PresetReqAt.HBulk (PresetReqAt.pj_frees ReaderRes.jr_strtod ok (je_tl en))]).
  { unfold PresetReqAt.parse_evs, PresetReqAt.rtr. rewrite (G_RUN _ _ _ _ _ Hjr). cbn [fst snd]. rewrite Hpost.
    reflexivity. }
  split.
  { intros sm x os i H0 hist Hpos Hrun.
    rewrite Ep in Hrun |- *. apply prh_run_at_app_iff in Hrun as (Hrun1 & Hrun2).
    destruct (proj1 HPOSPV sm x os i H0 hist Hpos Hrun1) as (h2 & Hpos2).
    destruct (HSTEP sm x os _ H0 h2 Hpos2 Hrun2) as (h3 & Hpos3).
    exists h3. rewrite length_app. cbn [length].
    replace (i + (length (PresetReqAt.rd_hevs tr) + 1))%nat with (i + length (PresetReqAt.rd_hevs tr) + 1)%nat
      by (clear; lia).
    exact Hpos3. }
  (* THE OUTCOME (the kit's conjunct): at a run whose next events are the all-granted reading's, with no injected failure in its
     window, parse_value's outcome conjunct (the cut's pjp_outc, over its own all-granted events, the first part)
     makes the reading the all-granted one (ran' = ran, (res, tr) its run), so the refusal's HBulk is the all-granted
     one too (G_FREES: pj_frees ok tl = pj_frees [] tl) and HSTEP moves the position past it *)
  split.
  { intros sm x os i H0 hist Hpos Hrun Hcons HwinO.
    assert (Egt : prhPv_gtrace 0 (je_tl en) = snd (PjGrammar.jr_run ReaderRes.jr_strtod (je_tl en) [])).
    { rewrite (pjg_gtrace (je_tl en)). reflexivity. }
    assert (Ep0 : PresetReqAt.parse_evs ReaderRes.jr_strtod (je_tl en) [] =
      PresetReqAt.rd_hevs (prhPv_gtrace 0 (je_tl en)) ++
      match fst (PjGrammar.jr_run ReaderRes.jr_strtod (je_tl en) []) with
      | Some _ => [] | None => [PresetReqAt.HBulk (PresetReqAt.pj_frees ReaderRes.jr_strtod [] (je_tl en))] end).
    { rewrite Egt. reflexivity. }
    rewrite Ep0 in Hrun, Hcons. apply prh_run_at_app_iff in Hrun as (Hrun1 & Hrun2).
    rewrite length_app in Hcons. apply prh_cons_from_app_iff in Hcons as (Hcons1 & _).
    assert (HwinO' : je_fail en < je_cnt en \/
      je_cnt en + Z.of_nat (PjGrammar.calls (prhPv_gtrace 0 (je_tl en))) <= je_fail en).
    { rewrite Egt. exact HwinO. }
    destruct (HOUTC sm x os i H0 hist Hpos Hrun1 Hcons1 HwinO') as (Eran & Efst & h2 & Hpos2).
    destruct (PjGrammar.jr_value ReaderRes.jr_strtod 0 (je_tl en) []) as [[res0 tr0] okr0] eqn:Ev0.
    cbn [fst] in Efst. injection Efst as -> ->.
    pose proof (G_RUN _ _ _ _ _ Ev0) as Er0. rewrite Hpost in Er0.
    assert (Efr : PresetReqAt.pj_frees ReaderRes.jr_strtod ok (je_tl en) =
                  PresetReqAt.pj_frees ReaderRes.jr_strtod [] (je_tl en)).
    { apply (G_FREES _ _ _ _ _ _ Hjr). rewrite Ev0. reflexivity. }
    assert (Etr : prhPv_gtrace 0 (je_tl en) = tr) by (unfold prhPv_gtrace; change prh_jr_strtod with ReaderRes.jr_strtod; rewrite Ev0; reflexivity).
    rewrite Er0 in Hrun2. cbn [fst] in Hrun2. rewrite Etr in Hpos2, Hrun2.
    rewrite <- Efr in Hrun2.
    destruct (HSTEP sm x os _ H0 h2 Hpos2 Hrun2) as (h3 & Hpos3).
    split; [exact Eran|]. split; [exact Er0|].
    split; [rewrite Ep, Ep0, Etr, Er0, <- Efr; reflexivity|].
    exists h3. rewrite Ep0, Etr, Er0, length_app. cbn [fst length].
    replace (i + (length (PresetReqAt.rd_hevs tr) + 1))%nat with (i + length (PresetReqAt.rd_hevs tr) + 1)%nat
      by (clear; lia).
    exact Hpos3. }
  (* THE OUTCOME OF AN INJECTED READING (the text's GUARDED conjunct): parse_value's (the cut's pjp_inj). Under the
     model's grant list the reading's events are parse_value's at that list, then the refusal's HBulk, so the run and
     consumer premises at pj_parse's list give them at parse_value's; the window is the same count *)
  split.
  { intros sm x os i H0 hist Hpos Hrun Hcons HwinI.
    assert (Egt : prhPv_gtrace 0 (je_tl en) = snd (PjGrammar.jr_run ReaderRes.jr_strtod (je_tl en) [])).
    { rewrite (pjg_gtrace (je_tl en)). reflexivity. }
    destruct (PjGrammar.jr_value ReaderRes.jr_strtod 0 (je_tl en) (PresetReqAt.okk (Z.to_nat (je_fail en - je_cnt en))))
      as [[resk trk] okrk] eqn:Evk.
    assert (Epk : exists Rk, PresetReqAt.parse_evs ReaderRes.jr_strtod (je_tl en)
        (PresetReqAt.okk (Z.to_nat (je_fail en - je_cnt en))) = PresetReqAt.rd_hevs trk ++ Rk).
    { unfold PresetReqAt.parse_evs, PresetReqAt.rtr. rewrite (G_RUN _ _ _ _ _ Evk). cbn [fst snd].
      eexists. reflexivity. }
    destruct Epk as (Rk & Epk).
    rewrite Epk in Hrun, Hcons. apply prh_run_at_app_iff in Hrun as (Hrun1 & _).
    rewrite length_app in Hcons. apply prh_cons_from_app_iff in Hcons as (Hcons1 & _).
    apply (HINJ sm x os i H0 hist Hpos).
    - rewrite Evk. exact Hrun1.
    - rewrite Evk. exact Hcons1.
    - rewrite Egt. exact HwinI. }
  split; [apply getr_same; pjr_regne|].
  split; [apply (Permutation_app_inv_l D); exact (Permutation_trans (Permutation_sym HpF) HpLam)|].
  split; [apply (Permutation_app_inv_l (prhPj_hbl D)); apply (Permutation_trans (Permutation_sym HabF));
          rewrite <- G_AB_HBL; exact Hab|].
  exact (HZ ltac:(lia)).
Qed.
End c2r.
