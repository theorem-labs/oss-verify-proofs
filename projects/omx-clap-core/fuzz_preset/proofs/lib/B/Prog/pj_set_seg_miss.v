(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: segment MISS of pj_set's image-B walk (fuzz_preset asan-ubsan, B 0x86e8c; the cuts of
   lib/B/Prog/pj_set_defs.v): the absent-key arm from PJS_MISS (+0x70) through grow's STATED text (the kit's restated
   tgrow_specX CTX0, lib/A/PRH_FnReader.v, pjs_texts' third conjunct) to the branch at +0x78.
     +0x70  mv a0, s1        a0 := obj
     +0x74  jal grow         the kit's tgrow_specX by YCbqGcallW.v aj_call_xWR at the re-hiding relation WLE' (YA0nH.wle'
                             over preset's zone, where grow's restated post fpostWmR ends; the cut's wle journal lifted
                             by ajournal_xwR_mono with wle_wle') at the callee window e1 = 48 + d (grow's text is at its
                             caller window e: e := 48 + d; the object is placed by prhReader_at at that e; grow's
                             footprint [(o+24,o+40); (o+48,o+56)] ++ the old slot blocks lies in pjs_FP); its hull
                             premise from the entry position (pj_set_glue.v pjs_hull_grow)
     +0x78  beqz a0, +0x30   a0 = 0 (n < cap, or both arrays moved): to PJS_DUP (+0xa8), whose segment statement
                             pjs_seg_dup is a premise; a0 = -1 (the kids realloc, or the keys realloc after the kids
                             moved, is the CHOSEN failure): falls through to PJS_FAIL (+0x7c), pjs_seg_fail
   grow's post is read BY NAME: each arm's top-level conjunctions are split (pjsm_split) and picked by type.
   THE DEAD REFUSAL ARM (pj_set_defs.v's header): grow's two REFUSED arms (the kids realloc refused; the keys realloc
   refused after the kids moved) are exfalso by their own exclusion clauses, applied at the entry position
   (ReaderRes.jr_strtod, js_x, js_os, js_i, js_H0, js_hist; S = js_S en at MISS) with the run premise of grow's
   all-granted events (pj_set_miss_lem.v pjm_set_grow_run) and their consumer premise from pjs_pre's prh_cons_from
   (pjm_set_grow_cons, by PRH_Base.prh_cons_from_sub). Grow's chosen-failure arms (cnt = fail; cnt + 1 = fail) give
   pjs_FAILc at the CHOSEN failure: the outcome cell prh_oks with ran' = ran (pjm_oks_chosen), the failure fact
   cnt + (c - 1) = fail and the granted peak Z.max peak (lsum Lam2).
   The array arm of grow's post is impossible (the object's tag is 6). grow's chain premise (its s0 = obj + 48,
   PRH_FnReader.v:352-361) holds by achain_low when obj + 48 < alloc_ceiling; otherwise the object lies in the caller's
   window (its other placements end below the ceiling) and the chain is the word obj->n at obj + 40 (an empty chain
   when n < 4096) or one record whose next frame pointer obj->keys lies below obj + 48 (keys is 0 or a harness block
   below the ceiling), so the unwinder stops: the premise holds from the bytes. grow's text (POST-IMPLICATION form)
   takes no position and no run premise; its two count premises (the peak of the secondary and class-24 live counts
   along its all-granted events prhPg_evs true n cap []) come from pjs_pre's position at js_i and its run premise
   (pj_set_miss_lem.v pjm_pk_of_pos): pjs_pre's run premise prhPj_set_evs, at the absent key, begins with rd_hevs
   (PjRoundTrip.grow_ev ..) = prhPg_evs true n cap [] at cf_head = HEAD (pjm_set_grow_run). Its room premise at
   n = cap (the tip's per-event form, PRH_Base.prh_live_evs over prhPg_evs true cap cap []) comes from pjs_pre's
   entry sum LIVE_pj_set at the call's blocks_bytes (pj_set_miss_lem.v pjm_grow_live). After the call the walk
   applies the arm's position implication at js_i, with the run premise of the arm's own events (a prefix of the
   all-granted ones: [] on the n < cap and kids-NULL arms, the kids realloc's event on the keys-NULL arm, both on the
   arm that moved both arrays). pjs_DUP's grow-related conjuncts come from grow's post (prhReader_swap, its ledger,
   its live-room bound; the position at js_i + c, c = 0 or 2) with pjs_pre's LIVE_pj_set; the object's member list
   after the move is pj_set_trans.v pjst_mems_move; the block lists in order are js_D = Dold ++ Dr (the cut's ED')
   and Do = Dnew ++ Dr.
   THE OBJECT'S ORDERED FREE LIST at DUP (pjs_DUP's last conjuncts): pjs_pre's ordered premise HFORD (at the entry
   memory) is framed to the MISS memory by MISS's entry agreement on pj_footR o D (PRH_PjOrder.pj_foR_frame),
   decomposed by pj_set_trans.v pjsf_obj_dest (its slot list over the old arrays, then the arrays); the map split
   (pjsf_slots_map, pjsf_arrz_eq) gives cap = ncap |ms|, hence cap2v = ncap (S |ms|) (pjm_ncap_S). The slot list is
   carried to the DUP memory by PRH_PjOrder.pf_oitemsR_frame when n < cap (grow kept the slot blocks' bytes) or by
   pjsf_oitems_move when n = cap (grow copied the arrays: the facts pjst_mems_move takes), and reassembled at the
   DUP header by pjsf_obj_intro (the arrays' requests by pjsf_arrz_of), over a permutation of Do (pjm_foR_perm).
   val's entry agreement (MISS's last conjunct) is carried across grow (val's footprint is off grow's) to DUP.
   Each failure arm keeps or advances the position, whence pjs_FAILc's class-24 bound pjs_PB (pjm_pb_of_pos), and
   owes pjs_FAILc's object freeable to the depth of the entry tree after pj_free(val): c < the length of the set
   trace there (c <= 2 < 3), so only that part is owed. grow's fpre's rounding-mode conjunct (FRM0-ENTRY) is the
   entry's (pjs_pre's fpre; pj_set never changes the float state). The memnorm keep of pjs_inv composes with grow's
   fpostWmR keep. The plain stretches (to the call, from the call to the branch's targets) are stepped under
   YGcfRhLift.ra_rh_of_SRr; the cuts after the call (pjs_DUP, pjs_FAILc) are at WLE'; pjs_FAILc's hull budget (the
   empty list's) is grow's budget less its use (PresetHullBudget.hull_budget_used with its post's hull_used).
   proves no function (kind: segment lemma).
   Numerals: 48 / 56 (LENGTH: pj_set's frame and the struct pj); 24 / 32 / 40 / 48 (LENGTH: field offsets); 96 (LENGTH:
   grow's frame, prh_img_B's pi_frame F_grow); 4096 (the unwinder's return-address floor, YG00.v fpchain); 4 / 8
   (DERIVED: pc offsets); register numbers 0, 1, 8, 9, 10, 18, 20 (WORD). No ADDRESS literal. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YCbqGcall YCbqGcallW FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06 YGcfFsVis.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetReqAt PresetReqAtNoMiss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnPj PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder PjFoMember.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import
S1ImgB pj_set_defs pj_set_glue pj_set_steps pj_set_trans pj_set_vis pj_set_miss_lem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost YGcfRhLift YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Open Scope Z_scope.
#[local] Existing Instance prh_img_B.

Section ms. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation PST := (prh_pst (PI := prh_img_B)).
#[local] Notation RZ := YGcfRehidePost.RZ_cf.
#[local] Notation WLE' := (YA0nH.wle' SEGS RZ).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis VIS : pjs_g_vis B ARx.
(* the hull budget at a run position (pj_set_defs.v pjs_g_hull) *)
Hypothesis HULL : @pjs_g_hull cp.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the top-level conjunctions of a hypothesis, split (the kit's ec_conj_split, lib/AU/Prog/Ent102CallB.v): grow's post is
   read by picking its conjuncts BY TYPE after this, never by position *)
Local Ltac pjsm_split H :=
  lazymatch type of H with
  | _ /\ _ =>
    let H1 := fresh "Em" in let H2 := fresh "Em" in destruct H as [H1 H2]; pjsm_split H1; pjsm_split H2
  | _ => idtac
  end.
(* a NoDup fact across the two spellings (Stdlib's List.NoDup and the tree's) *)
Local Ltac pjsm_nd H :=
  first [exact H | apply NoDup_ListNoDup; exact H | apply pjm_nd'; exact H | apply pjm_nd in H; exact H |
         apply NoDup_ListNoDup in H; exact H].

Theorem pjs_seg_miss_holds : forall CTX0 dd,
  pjs_texts B ARx CTX0 dd -> pjs_frame_kept_stmtR B ARx WLE' dd -> pjs_seg_dup B ARx CTX0 dd ->
  pjs_seg_fail B ARx CTX0 dd -> pjs_seg_miss B ARx CTX0 dd.
Proof.
intros CTX0 dd TXT KEEP HDUP HFAIL en ly S Hp W regs mem md k HPRE HCUT.
destruct TXT as (_ & _ & GROW & _ & _ & _).
pose proof HPRE as HPRE0.
pose proof (@pa_segs_low _ B_prog_listing PA) as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@cf_head_nonneg cp) as Hh0.
unfold pjs_pre in HPRE. cbv zeta in HPRE.
destruct HPRE as (HFPRE & HUNIV & HROOM0 & HPOS0 & HLOS & HCONS & _ & _ & _ & HFWIN & _ & _ & HCAP & _ & _ & _ & HWC & HDDW &
  HWO & HAPW & HDEPO & HDEPV & _ & _ & HKEY & HLED0 & HCNT3 & HKLEN & HMAX & HLIVE & _ & HFORD & HHEAD & HRUN).
pose proof HFPRE as ((HAR0 & _ & _ & Hgp0 & Htp0 & Hstk0 & _ & _ & _) & _ & HSTKHI0).
(* FRM0-ENTRY: the entry's rounding mode, which grow's fpre asks of the same fx *)
assert (HFRM : YK0o.frm_zero (@YK11.fp_csr fx)) by (destruct HFPRE as (_ & _ & _ & _ & H); exact H).
pose proof Hstk0 as (Hal0 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop0 & Htop20).
pose proof HFWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
destruct HCUT as (HINV & HDATA & HLED & Eab & EHp & ES & H9 & HNI & HNODE & HHDR & HNODEW & HAGR0 & HAGRW0).
pose proof HINV as (HJ & HWIN & Hsp & Hra & Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & H8 & H18 & H20 & HKEPT & HPRES & HROD & HMN).
pose proof (ajx_ar HJ) as HARc. pose proof (ajx_ly HJ) as Hly.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof HDATA as (HROOM & HPLO & HSLOTW & HCS & HKA).
assert (HSTKG : 0 <= STK_grow) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HSTKB : STK_grow + 48 <= STK_pj_set dd).
{ unfold STK_pj_set, zmaxl. cbn [fold_right].
  replace (pi_frame F_pj_set) with 48 by (vm_compute; reflexivity). lia. }
assert (HO4096 : 4096 <= js_o en) by (destruct HPLO as (H & _); exact H).
assert (HW4096 : 4096 <= js_w en) by (destruct HSLOTW as (H & _); exact H).
assert (Hsp0c : YM05.alloc_ceiling <= js_sp0 en) by (unfold js_sp0; lia).
(* ---- the object's node: its header fields are the cut's (one stored value per field) ---- *)
pose proof HNODE as HN1. cbn [pj_nodeR PjTree.tag] in HN1.
destruct HN1 as (HND & HNA & num0 & str0 & kids0 & keys0 & n0 & cap0 & Hh0' & Es0 & En0 & Hcn & Hcap0 & Di & ED & HMEMS).
destruct (pjm_hdr_det SEGS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HHDR Hh0') as (<- & <- & <- & <- & <- & <-).
assert (ED' : js_D en = (kids_blkR (js_kids en) (js_cap en) ++ keys_blkR 6 (js_keys en) (js_cap en)) ++ Di)
  by (rewrite pjm_old_eq; exact ED).
assert (Hn0 : 0 <= js_n en) by lia.
(* grow's entry premise: the model's events at the entry position begin with grow's, every realloc granted *)
assert (HRUNG : prh_run_at ReaderRes.jr_strtod (js_x en) (js_os en) (js_i en) (prhPg_evs true (js_n en) (js_cap en) []))
  by exact (pjm_set_grow_run _ _ _ _ (js_ms en) (js_kname en) (js_n en) (js_cap en) Hn0 ltac:(lia) HHEAD HNI HRUN).
(* ... and their consumer premise, from pjs_pre's (the run premise of grow's refused arms' exclusion clauses) *)
assert (HCONSG : prh_cons_from ReaderRes.jr_strtod (js_x en) (js_os en) (js_i en)
    (length (prhPg_evs true (js_n en) (js_cap en) [])))
  by exact (pjm_set_grow_cons _ _ _ _ (js_ms en) (js_kname en) (js_n en) (js_cap en) Hn0 ltac:(lia) HHEAD HNI HCONS).
assert (HPOSS : PresetRoomPos.iface_room_pos ReaderRes.jr_strtod (js_x en) (js_os en) (js_i en) (js_H0 en) (js_hist en)
  S) by (rewrite ES; exact HPOS0).
(* grow's hull budget: its all-granted events, from the entry position *)
assert (HHULLG : PresetHullBudget.hull_budget S (prhPg_evs true (js_n en) (js_cap en) [])).
{ apply (pjs_hull_grow HULL _ _ _ _ _ _ _ HLOS HPOSS); [lia | lia | exact HMAX]. }
(* grow's count premises: the peaks along its all-granted events, from the entry position and run premise *)
pose proof (pjm_pk_of_pos _ _ _ _ _ _ _ _ HPOSS HRUNG) as HPKG.
pose proof (pjm_node_nodup SEGS _ _ _ _ _ HNODEW) as (HNDw & _).
pose proof (pjst_node_lblk SEGS _ _ _ _ _ HNODE) as HDin.
pose proof (pjst_node_lblk SEGS _ _ _ _ _ HNODEW) as HDwin.
destruct (pjm_perm_lam (js_Lam en) (js_D en) (js_Dw en) HND HNDw HDDW HDin HDwin) as (Lr & HpLam).
(* ---- the object's ORDERED free list at MISS: the entry's ordered premise framed to this memory by MISS's entry
   agreement on the object's footprint (PRH_PjOrder.pj_foR_frame), decomposed into the slot list over the old arrays
   and the arrays (pj_set_trans.v pjsf_obj_dest; the ledger's block list is functional and has no block at 0); the
   map split at the arrays (pjsf_slots_map, pjsf_arrz_eq) makes the capacity the model's ---- *)
assert (HFN : forall a k k', prh_lin (js_Lam en) a k -> prh_lin (js_Lam en) a k' -> k = k')
  by exact (prh_lin_functional B ly S Hp W mem _ _ _ _ _ _ _ HLED).
assert (HNZ : forall a k, prh_lin (js_Lam en) a k -> a <> 0)
  by exact (prh_ledger_nonzero B ARx LAWS ly S Hp W mem md _ _ _ _ _ _ _ HARc HLED).
assert (HORD : forall d, (PjTree.depth (PjTree.JObj (js_ms en)) <= Datatypes.S d)%nat ->
  exists DiF FiF,
    PRH_PjOrder.pf_oitemsR SEGS (rdW W mem) (prh_lin (js_Lam en))
      (PRH_PjOrder.pj_foR SEGS (rdW W mem) (prh_lin (js_Lam en)) d) true (js_kids en) (js_keys en)
      (length (js_ms en)) DiF FiF /\
    Permutation Di DiF /\
    map (fun b => snd b + PresetReqAt.HEAD) FiF = PjFoMember.pfm_slots PresetReqAtNoMiss.kblk (js_ms en) /\
    js_cap en = Z.of_nat (PresetReqAt.ncap (length (js_ms en)))).
{ intros d Hd.
  destruct (HFORD HHEAD (Datatypes.S d) Hd) as (F0 & HFO0 & HM0).
  pose proof (PRH_PjOrder.pj_foR_frame SEGS (Datatypes.S d) _ (rdW W mem) _ (prh_lin (js_Lam en)) _ _ _ HFO0 HDin HAGR0)
    as HFO1.
  destruct (pjsf_obj_dest SEGS _ _ _ _ _ _ _ HFN HNZ HNODE HFO1)
    as (numF & kidsF & keysF & capF & DmF & DiF & FiF & HhF & HmF & HoF & HpF & Hcase).
  destruct (pjm_hdr_det SEGS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HHDR HhF) as (_ & _ & <- & <- & _ & <-).
  rewrite HHEAD in HM0. rewrite pjsf_fo_obj in HM0.
  exists DiF, FiF. split; [exact HoF|].
  destruct Hcase as [(Ec & Ems & ED0 & EF0) | (Hcp & _ & _ & _ & ED0 & EF0)].
  - (* no member and no array *)
    assert (EDi : Di = []) by (rewrite ED0, Ec in ED; cbn in ED; exact (eq_sym ED)).
    rewrite Ems in HmF, HoF. cbn [pj_memsR] in HmF. subst DmF.
    cbn [length PRH_PjOrder.pf_oitemsR] in HoF. destruct HoF as (-> & ->).
    split; [rewrite EDi; exact HpF|]. rewrite Ems, Ec. split; reflexivity.
  - (* the slot list, then the arrays: the arrays' requests are the model's at cap *)
    rewrite (proj2 (Z.eqb_neq (js_cap en) 0)) in ED by lia. cbn [app] in ED. rewrite ED0 in ED.
    assert (EDm : DmF = Di) by (injection ED; auto).
    split; [rewrite <- EDm; exact HpF|].
    rewrite EF0 in HM0.
    assert (Hlx : Nat.le (length (PresetReqAt.arrz true (PresetReqAt.ncap (length (js_ms en)))))
      (length [(js_kids en, 56 * js_cap en); (js_keys en, 8 * js_cap en)]))
      by (unfold PresetReqAt.arrz; destruct (PresetReqAt.ncap (length (js_ms en))); cbn [length]; lia).
    destruct (pjsf_slots_map SEGS _ _ _ _ _ _ _ _ _ _ _ _ HFN HNZ HmF HoF HM0 Hlx) as (HmapFi & HmapA).
    split; [exact HmapFi|].
    exact (proj1 (pjsf_arrz_eq _ _ _ _ HmapA)). }
(* the capacity is the model's (at any depth the tree fits) *)
assert (ECAP : js_cap en = Z.of_nat (PresetReqAt.ncap (length (js_ms en)))).
{ assert (Hd1 : (PjTree.depth (PjTree.JObj (js_ms en)) <=
    Datatypes.S (Nat.pred (PjTree.depth (PjTree.JObj (js_ms en)))))%nat) by (cbn [PjTree.depth Nat.pred]; lia).
  destruct (HORD _ Hd1) as (_ & _ & _ & _ & _ & E). exact E. }
(* ---- the old slot bytes grow's text names (kb, yb) ---- *)
set (KB := pjm_rdb SEGS (rdW W mem) (js_kids en) (Z.to_nat (56 * js_cap en))).
set (YB := pjm_rdb SEGS (rdW W mem) (js_keys en) (Z.to_nat (8 * js_cap en))).
assert (HKB : bytes_at (PA := PA) W mem (js_kids en) KB /\ Z.of_nat (length KB) = 56 * js_cap en).
{ split; [|unfold KB; rewrite pjm_rdb_len; lia].
  unfold bytes_at. apply pjm_rdb_garr8. intros j Hj.
  destruct Hcap0 as [(E0 & _ & _) | (Hc0 & Hkb & _)]; [rewrite E0 in Hj; cbn in Hj; lia|].
  exact (pjm_lam_some B ARx LAWS ly S Hp W mem md _ _ _ _ _ _ _ _ _ (Z.of_nat j) HARc HLED Hkb ltac:(lia)). }
assert (HYB : bytes_at (PA := PA) W mem (js_keys en) YB /\ Z.of_nat (length YB) = 8 * js_cap en).
{ split; [|unfold YB; rewrite pjm_rdb_len; lia].
  unfold bytes_at. apply pjm_rdb_garr8. intros j Hj.
  destruct Hcap0 as [(E0 & _ & _) | (Hc0 & _ & Hyb)]; [rewrite E0 in Hj; cbn in Hj; lia|].
  exact (pjm_lam_some B ARx LAWS ly S Hp W mem md _ _ _ _ _ _ _ _ _ (Z.of_nat j) HARc HLED Hyb ltac:(lia)). }
(* ======== +0x70  mv a0, s1 ======== *)
unfold pjs_cfg.
(* the plain stretch, under ra_rh_of_SRr (the cut is before pj_set's first free: wle) *)
apply YGcfRhLift.ra_rh_of_SRr.
pjs_fd PJS_MISS Hl1 Hd1.
eapply (pjs_step_addi W regs mem md _ PJS_MISS _ _ _ _ (10%bv : bv 5) (getr regs (9%bv : bv 5)) Hl1 Hd1).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ lazymatch goal with |- v_addi (getr _ ?rs) (bv_signed ?im) = _ =>
    replace rs with (9%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity);
    replace (bv_signed im) with 0 by (vm_compute; reflexivity) end.
  unfold v_addi. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. }
intros X1.
pose proof (ajournal_x_materialize (SK := SK) SEGS B PST ARx LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1 HJ) as HJ1.
replace (v_addi (Z_to_bv 64 (BASE + PJS_MISS)) 4) with (Z_to_bv 64 (BASE + (PJS_MISS + 4)))
  by (apply bv_eq; vm_compute; reflexivity).
(* ======== +0x74  jal grow ======== *)
pjs_fd (PJS_MISS + 4) Hl2 Hd2.
eapply (pjs_step_jal W _ mem _ _ (PJS_MISS + 4) _ _ _ (1%bv : bv 5) (Z_to_bv 64 (BASE + (PJS_MISS + 8)))
  (Z_to_bv 64 (@pa_sigma _ B_prog_listing PA AS_grow)) Hl2 Hd2).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X2.
pose proof (ajournal_x_materialize (SK := SK) SEGS B PST ARx LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X2 HJ1) as HJ2.
(* the cut's journal at WLE', where grow's restated post ends (the entry ghost set js_Hp named) *)
pose proof (ajournal_xwR_mono (SK := SK) SEGS B PST ARx (@wle SEGS) WLE' (YA0nH.wle_wle' SEGS RZ)
  _ _ _ _ _ (js_Hp en) _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HJ2R.
lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?r _ _ _) ?m) _ =>
  remember r as regsc eqn:Eregsc; set (mdc := m) in * end.
assert (HSPC : spZ regsc = js_sp1 en).
{ unfold YG0d.spZ at 1. rewrite Eregsc, !getr_other by pjs_regne. exact Hsp. }
assert (HS0LOW : s0Z regsc < YM05.alloc_ceiling).
{ unfold YG0d.s0Z. rewrite Eregsc, !getr_other by pjs_regne. rewrite H8. unfold w64.
  rewrite unsigned_lit_small by lia. lia. }
assert (HGP : getr regsc 3 = w64 (as_gp B)).
{ rewrite Eregsc, !getr_other by pjs_regne. rewrite (HKEPT 3%bv) by (unfold PJS_KEPT; left; reflexivity). exact Hgp0. }
assert (HTP : getr regsc 4 = w64 (as_tp B)).
{ rewrite Eregsc, !getr_other by pjs_regne. rewrite (HKEPT 4%bv) by (unfold PJS_KEPT; right; left; reflexivity).
  exact Htp0. }
assert (HRA1 : getr regsc 1 = Z_to_bv 64 (BASE + (PJS_MISS + 8)))
  by (rewrite Eregsc; apply getr_same; pjs_regne).
assert (HRAW : YK0s.ret_ok (Z_to_bv 64 (BASE + (PJS_MISS + 8)))).
{ apply (YC1fP.ret_ok_codeptr_v (PI := PA));
  [split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity | vm_compute; reflexivity]. }
assert (HRA4 : 4096 <= bv_unsigned (Z_to_bv 64 (BASE + (PJS_MISS + 8))))
  by (apply Z.leb_le; vm_compute; reflexivity).
assert (HSPO : spZ regsc = js_sp0 en + js_d en + (- 48 - js_d en))
  by (rewrite HSPC; unfold js_sp1, PJS_FR; lia).
assert (Ea0 : getr regsc 10 = w64 (js_o en)).
{ rewrite Eregsc, getr_other by pjs_regne. rewrite getr_same by pjs_regne. exact H9. }
set (FP1 := [(js_o en + 24, js_o en + 40); (js_o en + 48, js_o en + 56)] ++
  ablocks_fp (prhReader_ab (kids_blkR (js_kids en) (js_cap en) ++ keys_blkR 6 (js_keys en) (js_cap en)))).
(* grow's footprint is pj_set's own *)
assert (HFPsub : forall a, inFP FP1 a -> inFP (pjs_FP en) a).
{ intros a Ha. unfold FP1 in Ha. destruct (pjm_inFP_grow _ _ _ Ha) as [Hh | (a' & k' & Hin & Hx)].
  - exists (js_o en, js_o en + 56). split; [left; reflexivity | cbn [fst snd]; lia].
  - unfold pjs_FP. apply inFP_cons. right. apply inFP_cons. right.
    apply (pjm_hbl_inFP (js_D en ++ js_Dw en) a' k' a); [|exact Hx].
    apply in_or_app. left. rewrite ED'. apply in_or_app. left. exact Hin. }
(* ======== the call: grow's restated text, at WLE' and the callee window e1 = 48 + d ======== *)
apply SRr_ret.
eapply (YSRrG.SRr'_bind SEGS RZ).
{ eapply (aj_call_xWR (fx := fx) (SK := SK) SEGS B PST ARx LAWS Hsegs WLE' (YA0nH.wle'_refl SEGS RZ)
    (YA0nH.wle'_trans SEGS RZ) W regsc mem
    (@pa_sigma _ B_prog_listing PA AS_grow)
    (STK_pj_set dd + js_d en) (js_sp0 en + js_d en) (pjs_FP en)
    (js_ly en) (js_S en) (js_Hp en) (js_W en) (js_mem en) (js_md en) [] ly S Hp mdc k
    STK_grow (48 + js_d en) FP1 (- 48 - js_d en) (Z_to_bv 64 (BASE + (PJS_MISS + 8))) []
    _ HJ2R HSPO ltac:(lia) ltac:(lia) HSTKG ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    HGP HTP HRA1 HRAW HRA4 (achain_low _ _ _ _ HS0LOW)).
  - (* the callee: the kit's tgrow_specX CTX0 at e = 48 + d, v = obj, ty = 6; its post fpostWmR at WLE' is the call
       rule's fpostW_xR *)
    intros HPRE1 HWIN1. unfold fpostW_xR.
    eapply (GROW (js_most en) (js_own en)
      ly S Hp W regsc mem mdc [] (48 + js_d en) (js_o en) 6 (js_num en) (js_str en) (js_kids en)
      (js_keys en) (js_n en) (js_cap en) KB YB (js_Lam en) (js_peak en) (js_cnt en) (js_fail en) (js_ran en)).
    + split; [exact HPRE1|]. split; [exact HROD|].
      split; [rewrite HSPC, Eshi; unfold js_sp1, js_sp0, PJS_FR; lia|].
      split; [|exact HFRM].
      (* fpre's return-address bound: the jal's own return pc, a text address *)
      unfold YG0d.raZ. rewrite HRA1. pose proof (@YM05.alloc_ceiling_value rc) as [[ACm _] _].
      assert (EB : bv_unsigned (Z_to_bv 64 (BASE + (PJS_MISS + 8))) < 2 ^ 40)
        by (apply Z.ltb_lt; vm_compute; reflexivity).
      lia.
    + exact HUNIV.
    + (* the chain at grow's s0 = obj + 48 *)
      assert (Eg : prh_s0 F_grow (js_o en) = js_o en + 48) by reflexivity.
      assert (Ef : pi_frame F_grow = 96) by reflexivity.
      rewrite Eg, Ef.
      destruct (Z_lt_le_dec (js_o en + 48) YM05.alloc_ceiling) as [Hlow|Hhigh].
      { exists []. apply achain_low. exact Hlow. }
      (* above the ceiling the object is in the caller's window *)
      assert (Hcw : js_sp0 en <= js_o en).
      { destruct HPLO as (_ & Hat & _).
        destruct Hat as [(a & kk & Hin & H1 & H2) | [(b & m & Hbm & _ & H1 & H2) | [(cid & pos & Hcp & H1 & H2) | (H1 & H2)]]].
        - exfalso. destruct (pjm_lam_blk B ly S Hp W mem _ _ _ _ _ _ _ a kk HLED Hin) as (Hk0 & Hab).
          destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HARc Hab) as (_ & _ & Hcl & _).
          pose proof (pjs_req (kk + @cf_head cp) ltac:(lia)) as (Rq & _). lia.
        - exfalso. destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HARc Hbm) as (_ & _ & Hcl & _).
          pose proof (pjs_req m ltac:(lia)) as (Rq & _). lia.
        - exfalso. destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos HARc Hcp) as (_ & Hfc & _). lia.
        - unfold js_sp0. lia. }
      destruct (Z_lt_le_dec (js_o en + 48) (ly_top ly - 16)) as [Htl|Htl].
      2: { exists []. left. split; [right; left; lia | reflexivity]. }
      pose proof HHDR as (_ & _ & _ & _ & _ & HKY & HNN & _).
      assert (Rn : rdword (aview SEGS (w_H W) mem) (js_o en + 48 - 8) = Some (js_n en)).
      { replace (js_o en + 48 - 8) with (js_o en + 40) by lia. destruct HNN as (Rr & Hv). exact (pjm_rdword SEGS _ _ _ _ Rr Hv). }
      assert (Rk : rdword (aview SEGS (w_H W) mem) (js_o en + 48 - 16) = Some (js_keys en)).
      { replace (js_o en + 48 - 16) with (js_o en + 32) by lia. destruct HKY as (Rr & Hv). exact (pjm_rdword SEGS _ _ _ _ Rr Hv). }
      assert (Hkl : js_keys en <= js_o en + 48).
      { destruct Hcap0 as [(_ & _ & ->) | (_ & _ & Hkb)]; [lia|].
        destruct (pjm_lam_blk B ly S Hp W mem _ _ _ _ _ _ _ _ _ HLED Hkb) as (Hk0 & Hab).
        destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HARc Hab) as (_ & _ & Hcl & _).
        pose proof (pjs_req (8 * js_cap en + @cf_head cp) ltac:(lia)) as (Rq & _). lia. }
      assert (Hom8 : (js_o en + 48) mod 8 = 0).
      { destruct HPLO as (_ & _ & (Hal8 & _) & _). replace (js_o en + 48) with (js_o en + 6 * 8) by lia.
        rewrite Z.mod_add by lia. exact Hal8. }
      destruct (Z_lt_le_dec (js_n en) 4096) as [Hn4|Hn4].
      * exists []. right. split; [rewrite HSPC; unfold js_sp1, js_sp0, PJS_FR in *; lia|].
        split; [exact Htl|]. split; [exact Hom8|].
        split; [cbn [fpchain]; exists (js_n en); split; [exact Rn | lia]|]. constructor.
      * exists [(js_o en + 48, js_n en, js_keys en)]. right. split; [rewrite HSPC; unfold js_sp1, js_sp0, PJS_FR in *; lia|].
        split; [exact Htl|]. split; [exact Hom8|].
        split.
        { cbn [fpchain]. split; [reflexivity|]. split; [exact Hom8|]. split; [exact Rn|]. split; [exact Rk|].
          split; [lia|]. unfold bad_next.
          replace (js_keys en <=? js_o en + 48) with true by (symmetry; apply Z.leb_le; exact Hkl). reflexivity. }
        constructor; [cbn [fst]; rewrite HSPC; unfold js_sp1, js_sp0, PJS_FR in *; lia | constructor].
    + exact HROOM.
    + exact (proj1 HPKG).
    + exact (proj2 HPKG).
    + (* grow's hull budget at entry *)
      exact HHULLG.
    + exact Ea0.
    + lia.
    + destruct HPLO as (_ & _ & (Hal8 & _) & _). exact Hal8.
    + exact HHDR.
    + split; [right; reflexivity|]. split; [split; [exact Hcn | exact HCAP]|].
      split.
      { intros E0. destruct Hcap0 as [(_ & Hk & Hy) | (Hp0 & _)]; [split; [exact Hk | intros _; exact Hy] | lia]. }
      intros Hp0. destruct Hcap0 as [(E0 & _) | (_ & Hk & Hy)]; [lia | split; [exact Hk | intros _; exact Hy]].
    + intros b x Hb Hx. apply (HNA b x); [rewrite ED'; apply in_or_app; left; exact Hb | exact Hx].
    + exact HWIN1.
    + destruct HPLO as (_ & Hat & _).
      destruct Hat as [H|[H|[H|(H1 & H2)]]]; [left; exact H | right; left; exact H | right; right; left; exact H|].
      right; right; right. rewrite HSPC. unfold js_sp1, js_sp0, PJS_FR. unfold js_sp0 in Hsp0c. split; lia.
    + destruct HPLO as (_ & _ & _ & _ & _ & Hra'). exact Hra'.
    + intros _. split; [exact (proj1 HKB)|]. split; [exact (proj2 HKB)|]. intros _. exact HYB.
    + exact HLED.
    + lia.
    + (* grow's room at n = cap: the request bound, and the live room at each of its two events (the kit's per-event
         conjunct, PRH_Base.prh_live_evs) from the entry sum of both requests, which pjs_pre's LIVE_pj_set bounds
         (pj_set_miss_lem.v pjm_grow_live) *)
      intros Enc. split; [exact (HMAX Enc)|].
      rewrite Enc. apply pjm_grow_live; [lia|].
      rewrite (blocks_bytes_bsum B ly S), Eab, <- (blocks_bytes_bsum B (js_ly en) (js_S en)).
      unfold LIVE_pj_set in HLIVE. rewrite Enc, Z.eqb_refl in HLIVE. unfold js_klen in HLIVE. lia.
  - (* the footprint: the object's header and its old slot blocks are pj_set's own *)
    intros a Ha. left. exact (HFPsub a Ha). }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2' & HJc & HX & HP2 & HK).
cbv beta in HK. try unfold fQmn in HK. cbv beta in HK. destruct HK as (HK & HMN2).
(* the plain stretch to the branch's targets, under ra_rh_of_SRr *)
apply YGcfRhLift.ra_rh_of_SRr.
(* grow's post, BY NAME: the room, the hull use, the bytes bound, the arms *)
pjsm_split HK.
lazymatch goal with H : PresetHullBudget.hull_used S S2 _ |- _ => rename H into HHU end.
(* the hull budget left after grow's use: what pj_free (val) asks on the failure arms *)
assert (HHB2 : PresetHullBudget.hull_budget S2 []) by exact (PresetHullBudget.hull_budget_used _ _ _ HHULLG HHU).
lazymatch goal with H : room_live_cf S2 |- _ => rename H into HROOM2 end.
lazymatch goal with H : blocks_bytes S2 <= _ |- _ => rename H into HBB end.
lazymatch goal with H : (js_n en < js_cap en /\ _) \/ _ |- _ => rename H into HARM end.
replace (js_sp0 en + js_d en + (- 48 - js_d en) + (48 + js_d en)) with (js_sp0 en + js_d en) in HJc, HX
  by (unfold js_sp1, js_sp0, PJS_FR; lia).
replace (js_sp0 en + js_d en + (- 48 - js_d en)) with (js_sp1 en) in HX by (unfold js_sp1, PJS_FR; lia).
pose proof (ajxR_ar HJc) as HAR2. pose proof (ajxR_ly HJc) as Hly2. pose proof (ajxR_frs HJc) as Hfr2.
rewrite app_nil_l in Hfr2.
assert (Efa2 : forall cid pos, frame_addr ly2 cid pos = frame_addr ly cid pos).
{ intros cid pos. unfold frame_addr. destruct Hly2 as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
(* the caller's window and pj_set's frame are present after the call (the walk's own journal) *)
pose proof (ajxR_pres HJ2') as HPRES2.
assert (HPRW : forall a, js_sp1 en <= a < js_sp0 en + js_d en -> apresent (w_H W2) mem2 a).
{ intros a Ha. apply HPRES2. unfold js_sp1, js_sp0, PJS_FR in *. lia. }
(* grow's footprint: no sink, off pj_set's frame *)
assert (HSINK : ~ YI16.sink_open_fp FP1).
{ unfold FP1. apply sink_closed_app.
  - apply sink_closed_cons; [cbn [fst]; lia|]. apply sink_closed_cons; [cbn [fst]; lia|]. exact sink_closed_nil.
  - apply sink_closed_ablocks_fp. apply Forall_forall. intros [b m] Hb. cbn [fst].
    change (In (b, m) (prhPj_hbl (kids_blkR (js_kids en) (js_cap en) ++ keys_blkR 6 (js_keys en) (js_cap en)))) in Hb.
    apply pjm_hbl_inv in Hb.
    assert (Hb2 : In (b + cf_head, m - cf_head) (js_Lam en)) by (apply HDin; rewrite ED'; apply in_or_app; left; exact Hb).
    destruct (pjm_lam_blk B ly S Hp W mem _ _ _ _ _ _ _ _ _ HLED Hb2) as (_ & Hab).
    destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HARc Hab) as (_ & H4096 & _). lia. }
assert (HFPFR : forall a, js_sp1 en <= a < js_sp0 en -> ~ inFP FP1 a).
{ intros a Ha Hin. unfold FP1 in Hin. destruct (pjm_inFP_grow _ _ _ Hin) as [Hh | (a' & k' & Hin' & Hx)].
  - destruct HPLO as (_ & _ & _ & _ & Hown & _). destruct (Hown a ltac:(lia)) as (_ & Hn). apply Hn.
    unfold js_sp1, js_sp0, PJS_FR in *. lia.
  - assert (Hb2 : In (a', k') (js_Lam en)) by (apply HDin; rewrite ED'; apply in_or_app; left; exact Hin').
    destruct (pjm_lam_blk B ly S Hp W mem _ _ _ _ _ _ _ _ _ HLED Hb2) as (Hk0 & Hab).
    destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HARc Hab) as (_ & _ & Hcl & _).
    unfold js_sp1, js_sp0, PJS_FR in *. lia. }
assert (HFPWIN : forall a, js_sp0 en <= a < js_sp0 en + js_d en -> ~ inFP (pjs_FP en) a -> ~ inFP FP1 a)
  by (intros a _ Hn Hin; exact (Hn (HFPsub a Hin))).
destruct (KEEP en ly S Hp W regsc mem mdc k STK_grow FP1 ly2 S2 Hp2 W2 mem2 md2 k1
  ltac:(split; [exact HJ2R|]; split; [exact HWIN|];
        split; [exact HSPC|]; split; [exact Hra|]; split; [exact Hs0|]; split; [exact Hs1|];
        split; [exact Hs2|]; split; [exact Hs3|]; split; [exact Hs4|];
        split; [rewrite Eregsc, !getr_other by pjs_regne; exact H8|];
        split; [rewrite Eregsc, !getr_other by pjs_regne; exact H18|];
        split; [rewrite Eregsc, !getr_other by pjs_regne; exact H20|];
        split; [intros r Hr; rewrite Eregsc, !getr_other by pjs_kept_ne; exact (HKEPT r Hr)|];
        split; [exact HPRES|]; split; [exact HROD | exact HMN])
  HJc HX HFPFR HFPWIN HSTKG Hd0 HSINK) as (KW & KRA & KS0 & KS1 & KS2 & KS3 & KS4 & KPR & KROD).
(* ======== +0x78  beqz a0 ======== *)
pjs_fd (PJS_MISS + 8) Hl3 Hd3.
eapply (pjm_step_beq W2 regs2 mem2 md2 _ (PJS_MISS + 8) _ _ _ _ Hl3 Hd3).
intros X3.
pose proof (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs WLE' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X3 HJ2') as HJ3.
assert (HINV3 : pjs_invR B ARx WLE' dd en ly2 S2 Hp2 W2 regs2 mem2 (with_vm_backing (m_vm_lazy md2) X3 md2) (k + k1)).
{ split; [exact HJ3|].
  split; [intros a Ha Hfp; exact (KW a Ha Hfp)|].
  split; [rewrite (pjs_pres_sp regsc regs2 HP2); exact HSPC|].
  split; [exact KRA|]. split; [exact KS0|]. split; [exact KS1|]. split; [exact KS2|]. split; [exact KS3|].
  split; [exact KS4|].
  split; [rewrite (pjs_pres regsc regs2 (8%bv : bv 5) HP2 ltac:(pjs_cs));
          rewrite Eregsc, !getr_other by pjs_regne; exact H8|].
  split; [rewrite (pjs_pres regsc regs2 (18%bv : bv 5) HP2 ltac:(pjs_cs));
          rewrite Eregsc, !getr_other by pjs_regne; exact H18|].
  split; [rewrite (pjs_pres regsc regs2 (20%bv : bv 5) HP2 ltac:(pjs_cs));
          rewrite Eregsc, !getr_other by pjs_regne; exact H20|].
  split.
  { intros r Hr.
    assert (Hcs : acallee_saved (bv_unsigned r)).
    { unfold PJS_KEPT in Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [pjs_cs |]). destruct Hr. }
    rewrite (pjs_pres regsc regs2 r HP2 Hcs). rewrite Eregsc, !getr_other by pjs_kept_ne. exact (HKEPT r Hr). }
  split; [exact KPR|]. split; [exact KROD|]. intros Hm0. exact (HMN2 (HMN Hm0)). }
assert (H9' : getr regs2 9 = w64 (js_o en)).
{ rewrite (pjs_pres regsc regs2 (9%bv : bv 5) HP2 ltac:(pjs_cs)). rewrite Eregsc, !getr_other by pjs_regne. exact H9. }
(* ======== what the two exits share ======== *)
assert (HSTKF : 0 <= STK_pj_free dd) by (unfold STK_pj_free, zmaxl; cbn [fold_right];
  pose proof (pi_frame_nonneg F_pj_free); lia).
pose proof (ajx_ar HJ2) as HARm.
destruct pjs_glue_holds as (Hfd & _ & _ & _ & Hlen & _ & _ & _).
assert (HatO : prhReader_at B ly S (js_Lam en) (js_regs en) (js_d en) (js_o en) 56) by (destruct HPLO as (_ & H & _); exact H).
assert (HatW : prhReader_at B ly S (js_Lam en) (js_regs en) (js_d en) (js_w en) 56)
  by (destruct HSLOTW as (_ & H & _); exact H).
assert (HNDl : List.NoDup (js_D en)) by (apply pjm_nd; exact HND).
assert (HDoldD : forall a kk, In (a, kk) (kids_blkR (js_kids en) (js_cap en) ++ keys_blkR 6 (js_keys en) (js_cap en)) ->
  In (a, kk) (js_D en)) by (intros a kk H; rewrite ED'; apply in_or_app; left; exact H).
assert (HDiD : forall a kk, In (a, kk) Di -> In (a, kk) (js_D en))
  by (intros a kk H; rewrite ED'; apply in_or_app; right; exact H).
assert (HDiold : forall b, In b Di -> ~ In b (kids_blkR (js_kids en) (js_cap en) ++ keys_blkR 6 (js_keys en) (js_cap en))).
{ intros b Hb Ho. pose proof HNDl as HN'. rewrite ED' in HN'. exact (pjm_nodup_disj _ _ b HN' Ho Hb). }
assert (HSLOTS0 : pj_slots_atR (prh_lin (js_Lam en)) 6 (js_kids en) (js_keys en) (js_n en) (js_cap en)).
{ split; [right; reflexivity|]. split; [split; [exact Hcn | exact HCAP]|].
  split.
  { intros E0. destruct Hcap0 as [(_ & Hk & Hy) | (Hp0 & _)]; [split; [exact Hk | intros _; exact Hy] | lia]. }
  intros Hp0. destruct Hcap0 as [(E0 & _) | (_ & Hk & Hy)]; [lia | split; [exact Hk | intros _; exact Hy]]. }
(* what grow's footprint misses: val's header and blocks, the members' blocks, the key *)
assert (HwFP : forall x, js_w en <= x < js_w en + 56 -> ~ inFP FP1 x).
{ intros x Hx Hin. unfold FP1 in Hin. destruct (pjm_inFP_grow _ _ _ Hin) as [Hh | (a & kk & Ha & Hr)].
  - apply (HWO x Hx). left. lia.
  - assert (Hoff : forall y, js_w en <= y < js_w en + 56 -> ~ (a <= y < a + kk)).
    { intros y Hy Hy'. apply (HWO y Hy). right. exists (a, kk). split; [exact (HDoldD a kk Ha) | exact Hy']. }
    exact (pjm_at_off B ARx LAWS ly S Hp W mem md (js_Lam en) (js_peak en) (js_cnt en) (js_fail en) (js_ran en) (js_most en) (js_own en)
      (js_regs en) (js_d en) (js_w en) a kk HARc HLED HatW Hsp0c (HDin a kk (HDoldD a kk Ha)) Hoff x Hx Hr). }
assert (HDwFP : forall b x, In b (js_Dw en) -> pj_holdsR b x -> ~ inFP FP1 x).
{ intros [a' k'] x Hb Hx Hin. unfold FP1 in Hin. destruct (pjm_inFP_grow _ _ _ Hin) as [Hh | (a & kk & Ha & Hr)].
  - apply (HAPW (a', k') x Hb Hx). lia.
  - apply (pjm_lam_off B ARx LAWS ly S Hp W mem md _ _ _ _ _ _ _ a kk a' k' x HARc HLED (HDin a kk (HDoldD a kk Ha))
      (HDwin a' k' Hb)); [|exact Hx | exact Hr].
    intros E. apply (HDDW (a', k') Hb). rewrite E. exact (HDoldD a kk Ha). }
assert (HDiFP : forall b x, In b Di -> pj_holdsR b x -> ~ inFP FP1 x).
{ intros [a' k'] x Hb Hx Hin. unfold FP1 in Hin. destruct (pjm_inFP_grow _ _ _ Hin) as [Hh | (a & kk & Ha & Hr)].
  - apply (HNA (a', k') x (HDiD a' k' Hb) Hx). lia.
  - apply (pjm_lam_off B ARx LAWS ly S Hp W mem md _ _ _ _ _ _ _ a kk a' k' x HARc HLED (HDin a kk (HDoldD a kk Ha))
      (HDin a' k' (HDiD a' k' Hb))); [|exact Hx | exact Hr].
    intros E. apply (HDiold (a', k') Hb). rewrite E. exact Ha. }
assert (HkFP : forall x, js_k en <= x < js_k en + js_klen en + 1 -> ~ inFP FP1 x).
{ intros x Hx Hin. unfold FP1 in Hin. destruct (pjm_inFP_grow _ _ _ Hin) as [Hh | (a & kk & Ha & Hr)].
  - apply (proj1 (HKEY x Hx)). left. lia.
  - assert (Hoff : forall y, js_k en <= y < js_k en + (js_klen en + 1) -> ~ (a <= y < a + kk)).
    { intros y Hy Hy'. apply (proj1 (HKEY y ltac:(lia))). right. exists (a, kk). split; [exact (HDoldD a kk Ha) | exact Hy']. }
    exact (pjm_key_off B ARx LAWS ly S Hp W mem md (js_Lam en) _ _ _ _ _ _ (js_k en) (js_klen en + 1) a kk HARc HLED HKA
      ltac:(unfold js_klen; lia) (HDin a kk (HDoldD a kk Ha)) Hoff x ltac:(lia) Hr). }
assert (HFPs : forall x, inFP FP1 x -> x < kLowShadowBeg \/ kHighMemBeg <= x).
{ intros x Hin. unfold FP1 in Hin. destruct (pjm_inFP_grow _ _ _ Hin) as [Hh | (a & kk & Ha & Hr)].
  - apply (pjm_at_app B ARx LAWS ly S Hp W mem md _ _ _ _ _ _ _ (js_regs en) (js_d en) (js_o en) HARc HLED HatO Hsp0c). lia.
  - destruct (pjm_lam_blk B ly S Hp W mem _ _ _ _ _ _ _ a kk HLED (HDin a kk (HDoldD a kk Ha))) as (_ & Hab).
    destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HARc Hab) as (_ & _ & _ & Happ & _).
    pose proof (in_app_addr _ _ x Happ Hr) as (_ & Hx'). lia. }
(* the blocks holding the object's header, val's header and the key are none of the object's own *)
assert (HcO : forall a kk, In (a, kk) (js_Lam en) -> a <= js_o en -> js_o en + 56 <= a + kk -> ~ In (a, kk) (js_D en)).
{ intros a kk _ H1 H2 Hin. apply (HNA (a, kk) (js_o en) Hin); [unfold pj_holdsR; cbn [fst snd]; lia | lia]. }
assert (HcW : forall a kk, In (a, kk) (js_Lam en) -> a <= js_w en -> js_w en + 56 <= a + kk -> ~ In (a, kk) (js_D en)).
{ intros a kk _ H1 H2 Hin. apply (HWO (js_w en) ltac:(lia)). right. exists (a, kk).
  split; [exact Hin | unfold pj_holdsR; cbn [fst snd]; lia]. }
assert (HcK : forall a kk, In (a, kk) (js_Lam en) -> a <= js_k en -> js_k en + js_klen en + 1 <= a + kk ->
  ~ In (a, kk) (js_D en)).
{ intros a kk _ H1 H2 Hin. apply (proj1 (HKEY (js_k en) ltac:(unfold js_klen in *; lia))). right. exists (a, kk).
  split; [exact Hin | unfold pj_holdsR; cbn [fst snd]; unfold js_klen in *; lia]. }
(* what grow's journal keeps: val's footprint and the members' blocks *)
assert (HAGDi : pj_agreeR SEGS (rdW W mem) (rdW W2 mem2) (fun x => exists b, In b Di /\ pj_holdsR b x))
  by exact (pjm_blks_agree B ARx LAWS ly S Hp W mem mdc _ _ _ _ _ _ _ _ _ _ ly2 S2 Hp2 W2 mem2 md2 k1 Di HJc HLED
    (fun a kk H => HDin a kk (HDiD a kk H)) HDiFP).
assert (HAGW : pj_agreeR SEGS (rdW W mem) (rdW W2 mem2) (pj_footR (js_w en) (js_Dw en))).
{ apply (pjm_agree_foot SEGS).
  - apply (pjm_at_agree B ARx LAWS ly S Hp W mem mdc _ _ _ _ _ _ _ _ _ _ ly2 S2 Hp2 W2 mem2 md2 k1 (js_regs en) (js_d en)
      (js_w en) HJc HLED HatW HwFP).
    + intros x Hx Hn. apply HX; [unfold js_sp1, js_sp0, PJS_FR in *; lia | exact Hn].
    + intros x Hx. apply HPRW. unfold js_sp1, js_sp0, PJS_FR in *. lia.
  - exact (pjm_blks_agree B ARx LAWS ly S Hp W mem mdc _ _ _ _ _ _ _ _ _ _ ly2 S2 Hp2 W2 mem2 md2 k1 (js_Dw en) HJc HLED
      HDwin HDwFP). }
(* the object where grow moved nothing: its header from grow's post, its members over the old arrays *)
assert (HMOLD : forall peak2 cnt2 fail2 ran2 most2 own2,
  prh_ledger (PA := PA) B ly2 S2 Hp2 W2 mem2 (js_Lam en) peak2 cnt2 fail2 ran2 most2 own2 ->
  pj_hdrR SEGS (rdW W2 mem2) (js_o en) 6 (js_num en) (js_str en) (js_kids en) (js_keys en) (js_n en) (js_cap en) ->
  (forall j, 0 <= j < 56 * Z.of_nat (length (js_ms en)) ->
     mbyte SEGS (rdW W2 mem2) (js_kids en + j) = mbyte SEGS (rdW W mem) (js_kids en + j)) ->
  (forall j, 0 <= j < 8 * Z.of_nat (length (js_ms en)) ->
     mbyte SEGS (rdW W2 mem2) (js_keys en + j) = mbyte SEGS (rdW W mem) (js_keys en + j)) ->
  pj_nodeR SEGS (rdW W2 mem2) (prh_lin (js_Lam en)) (js_o en) (PjTree.JObj (js_ms en)) (js_D en)).
{ intros peak2 cnt2 fail2 ran2 most2 own2 HL2 Hh2 Ev Ek.
  rewrite Es0 in Hh2.
  apply (pjm_node_obj SEGS _ _ _ (js_num en) (js_kids en) (js_keys en) (js_n en) (js_cap en) _ Di _ Hh2 En0 Hcn Hcap0
    HND HNA ED).
  apply (pjst_mems_move SEGS (js_ms en) (rdW W mem) (rdW W2 mem2) (prh_lin (js_Lam en)) (prh_lin (js_Lam en))
    (js_kids en) (js_keys en) (js_kids en) (js_keys en) Di HMEMS Ev Ek).
  - intros x Hx. destruct Hcap0 as [(E0 & _ & _) | (Hc0 & Hkb & _)]; [lia|].
    apply (pjm_lam_writable B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ _ _ _ _ _ _ _ x HAR2 HL2 Hkb). lia.
  - destruct Hcap0 as [(_ & -> & _) | (_ & Hkb & _)]; [reflexivity|].
    destruct (prh_ledger_hblock B ly S Hp W mem _ _ _ _ _ _ _ _ _ HLED Hkb) as (_ & _ & _ & Hm16 & _). lia.
  - intros [a' k'] x Hb Hx Hk. destruct Hcap0 as [(E0 & _ & _) | (Hc0 & Hkb & _)]; [lia|].
    pose proof (pjs_req (56 * js_cap en + @cf_head cp) ltac:(lia)) as (Rq & _).
    apply (pjm_lam_off B ARx LAWS ly S Hp W mem md _ _ _ _ _ _ _ (js_kids en) (56 * js_cap en) a' k' x HARc HLED Hkb
      (HDin a' k' (HDiD a' k' Hb))); [| exact Hx | lia].
    intros E. apply (HDiold (a', k') Hb). rewrite E. apply in_or_app. left. unfold kids_blkR.
    rewrite (proj2 (Z.eqb_neq (js_cap en) 0)) by lia. left. reflexivity.
  - exact HAGDi.
  - intros a kk H. exact (HDin a kk (HDiD a kk H)). }
pose proof HKB as (HKBg & HKBl). pose proof HYB as (HYBg & HYBl).
(* the FAIL cut after the kids realloc is the CHOSEN failure (c = 1): nothing moved; the object is still its own tree *)
assert (HF1 : js_n en = js_cap en -> ablocks B ly2 S2 = ablocks B ly S ->
  prh_ledger (PA := PA) B ly2 S2 Hp2 W2 mem2 (js_Lam en) (js_peak en) (js_cnt en + 1) SIZE_MAXZ (js_ran en)
    (js_most en) (js_own en) ->
  pj_hdrR SEGS (rdW W2 mem2) (js_o en) 6 (js_num en) (js_str en) (js_kids en) (js_keys en) (js_n en) (js_cap en) ->
  bytes_at (PA := PA) W2 mem2 (js_kids en) KB -> bytes_at (PA := PA) W2 mem2 (js_keys en) YB ->
  js_cnt en = js_fail en -> pjs_PB S2 -> PresetHullBudget.hull_budget S2 [] ->
  pjs_FAILc B ARx dd en ly2 S2 Hp2 W2 regs2 mem2 (with_vm_backing (m_vm_lazy md2) X3 md2) (k + k1)).
{ intros Enc Eab2 HLED2 HHDR2 HBK HBY Ecf HPB HHB.
  assert (HDATA2 : pjs_data_c B dd en ly2 S2 (js_Lam en) W2 mem2).
  { apply (pjs_datac_kept B ARx LAWS VIS dd en ly S Hp W mem mdc (js_Lam en) (js_peak en) (js_cnt en) (js_fail en)
      (js_ran en) (js_most en) (js_own en) (STK_grow + (48 + js_d en)) (js_sp0 en + js_d en) FP1 ly2 S2 Hp2 W2 mem2 md2 k1
      (js_Lam en) (js_peak en) (js_cnt en + 1) SIZE_MAXZ (js_ran en) (js_most en) (js_own en) HARm HJc HLED HLED2 HFPs
      HSINK HkFP).
    - rewrite Eslo. unfold js_sp0 in *. lia.
    - rewrite Eshi. unfold js_sp0 in *. lia.
    - intros x Hx. apply HPRW. unfold js_sp1, js_sp0, PJS_FR in *. lia.
    - unfold js_sp0 in *. lia.
    - intros a kk p _ Hin _ _. exact Hin.
    - intros b m p _ Hbm HnL _ _. rewrite Eab2. split; [exact Hbm | exact HnL].
    - intros a kk Hin _ _. exact Hin.
    - exact HROOM2.
    - exact HDATA. }
  pose proof HDATA2 as (_ & (_ & HatO2 & _) & HSW2 & _).
  assert (HNODE2 : pj_nodeR SEGS (rdW W2 mem2) (prh_lin (js_Lam en)) (js_o en) (PjTree.JObj (js_ms en)) (js_D en)).
  { apply (HMOLD _ _ _ _ _ _ HLED2 HHDR2); intros j Hj.
    - exact (pjm_garr8_eq SEGS _ _ _ _ KB HKBg HBK j ltac:(lia)).
    - exact (pjm_garr8_eq SEGS _ _ _ _ YB HYBg HBY j ltac:(lia)). }
  assert (HNODEW2 : pj_nodeR SEGS (rdW W2 mem2) (prh_lin (js_Lam en)) (js_w en) (js_tv en) (js_Dw en))
    by exact (pjst_node_frame SEGS (js_tv en) _ _ _ _ _ _ HNODEW HAGW HDwin).
  split; [exact HINV3|]. split; [exact HROOM2|].
  exists (js_Lam en), (js_peak en), SIZE_MAXZ, (js_ran en), 1%nat, [false], (js_D en), Lr.
  split; [replace (js_cnt en + Z.of_nat 1) with (js_cnt en + 1) by lia; exact HLED2|].
  (* the outcome cell: the one failure is the chosen one, g_ran_out kept *)
  split; [apply pjm_oks_chosen; [lia | reflexivity | intros i Hi; exfalso; lia | lia]|].
  split; [split; [intros _; reflexivity | intros Hn; exfalso; apply Hn; lia]|].
  split; [exact HpLam|]. split; [exact HpLam|].
  split; [destruct (pjm_blocks_other B ly S Hp W mem _ _ _ _ _ _ _ HLED) as (other & Ho); exists other;
          split; [rewrite <- Eab; exact Ho | rewrite Eab2; exact Ho]|].
  split; [exact HNI|].
  split; [rewrite Hlen, (proj2 (Z.eqb_eq _ _) Enc); cbv iota; lia|].
  split; [reflexivity|].
  split; [intros i Hi; exfalso; lia|].
  (* THE FAILURE IS THE CHOSEN ONE, and the peak is the granted run's *)
  split; [lia|].
  split; [pose proof (prh_ledger_bounds B _ _ _ _ _ _ _ _ _ _ _ _ HLED) as (Hlp & _); lia|].
  split; [exact HPB|].
  split; [exists [], [], (js_D en); split; [apply Permutation_refl|]; split; [apply Permutation_refl|];
          split; [intros a kk []|]; left; repeat split|].
  split.
  { intros md0 ly3 S3 Hp3 W3 mem3 md3 k3 Lam3 HJf HXf HP3. split.
    - exact (Hfd SEGS _ _ _ _ _ _ (pjm_obl_node B ARx LAWS dd en ly2 S2 Hp2 W2 mem2 md2 (js_Lam en) _ _ _ _ _ _
        md0 ly3 S3 Hp3 W3 mem3 md3 k3 Lam3 Lr _ (js_D en)
        Hsp0c HSTKF HAR2 HLED2 HatO2 HDin HDwin HDDW HAPW HWO HJf HXf HNODE2 HP3) (le_n _)).
    - intros Ec. exfalso. rewrite Hlen, (proj2 (Z.eqb_eq _ _) Enc) in Ec. discriminate Ec. }
  split; [exact HNODEW2|]. split; [exact HSW2 | exact HHB]. }
assert (Hcap2 : js_cap en < cap2R (js_cap en) /\ (js_cap en <> 0 -> cap2R (js_cap en) = 2 * js_cap en))
  by (unfold cap2R; destruct (Z.eqb_spec (js_cap en) 0); lia).
(* ---- what survives grow's block swap (the arms that move a block): Dx left, Dn came ---- *)
assert (HSWAP : forall (Dx Dn Lam' Lam0 bl : list (Z * Z)) peak2 cnt2 fail2 ran2 most2 own2,
  (forall b, In b Dx -> In b (js_D en)) ->
  Permutation (js_Lam en) (Dx ++ Lam0) -> Permutation Lam' (Dn ++ Lam0) ->
  Permutation (ablocks B ly S) (prhPj_hbl Dx ++ bl) -> Permutation (ablocks B ly2 S2) (prhPj_hbl Dn ++ bl) ->
  prh_ledger (PA := PA) B ly2 S2 Hp2 W2 mem2 Lam' peak2 cnt2 fail2 ran2 most2 own2 ->
  (forall a kk p, p = js_o en \/ p = js_w en -> In (a, kk) (js_Lam en) -> a <= p -> p + 56 <= a + kk ->
     In (a, kk) Lam') /\
  (forall b m p, p = js_o en \/ p = js_w en -> In (b, m) (ablocks B ly S) -> ~ In (b + cf_head, m - cf_head) (js_Lam en) ->
     b <= p -> p + 56 <= b + m -> In (b, m) (ablocks B ly2 S2) /\ ~ In (b + cf_head, m - cf_head) Lam') /\
  (forall a kk, In (a, kk) (js_Lam en) -> a <= js_k en -> js_k en + js_klen en + 1 <= a + kk -> In (a, kk) Lam') /\
  (forall a kk, In (a, kk) Dn -> ~ In (a, kk) Dx -> 0 <= kk ->
     ~ In (a - cf_head, kk + cf_head) (ablocks B ly S) /\
     (forall x, js_o en <= x < js_o en + 56 -> ~ (a <= x < a + kk)) /\
     (forall x, js_w en <= x < js_w en + 56 -> ~ (a <= x < a + kk)))).
{ intros Dx Dn Lam' Lam0 bl peak2 cnt2 fail2 ran2 most2 own2 HDx HL1 HL2 Hb1 Hb2 HLED2'.
  assert (HSL' : forall a kk p, p = js_o en \/ p = js_w en -> In (a, kk) (js_Lam en) -> a <= p -> p + 56 <= a + kk ->
    In (a, kk) Lam').
  { intros a kk p Hp' Hin H1 H2. apply (pjm_swap_lam _ _ _ _ _ a kk HL1 HL2 Hin). intros Hx.
    destruct Hp' as [-> | ->]; [exact (HcO a kk Hin H1 H2 (HDx _ Hx)) | exact (HcW a kk Hin H1 H2 (HDx _ Hx))]. }
  assert (HSB' : forall b m p, p = js_o en \/ p = js_w en -> In (b, m) (ablocks B ly S) ->
    ~ In (b + cf_head, m - cf_head) (js_Lam en) -> b <= p -> p + 56 <= b + m ->
    In (b, m) (ablocks B ly2 S2) /\ ~ In (b + cf_head, m - cf_head) Lam').
  { intros b m p _ Hbm HnL H1 H2.
    exact (pjm_swap_blk B ARx LAWS ly S ly2 S2 Hp2 W2 mem2 md2 (js_Lam en) Lam' Lam0 Dx Dn bl b m HAR2 HL1 HL2 Hb1 Hb2
      Hbm HnL ltac:(lia)). }
  split; [exact HSL'|]. split; [exact HSB'|].
  split.
  { intros a kk Hin H1 H2. apply (pjm_swap_lam _ _ _ _ _ a kk HL1 HL2 Hin). intros Hx.
    exact (HcK a kk Hin H1 H2 (HDx _ Hx)). }
  intros a kk Hin Hnx Hk0.
  assert (Hfresh : ~ In (a - cf_head, kk + cf_head) (ablocks B ly S))
    by exact (pjm_swap_new B ARx LAWS ly S ly2 S2 Hp2 W2 mem2 md2 Dx Dn bl a kk HAR2 Hb1 Hb2 Hin Hnx ltac:(lia)).
  assert (Hab2 : In (a - cf_head, kk + cf_head) (ablocks B ly2 S2))
    by (apply (Permutation_in _ (Permutation_sym Hb2)); apply in_or_app; left; exact (pjm_hbl_in Dn a kk Hin)).
  pose proof (pjs_req (kk + @cf_head cp) ltac:(lia)) as (Rq & _).
  assert (Hoff : forall p, (p = js_o en \/ p = js_w en) ->
     prhReader_at B ly S (js_Lam en) (js_regs en) (js_d en) p 56 ->
     forall x, p <= x < p + 56 -> ~ (a <= x < a + kk)).
  { intros p Hp' Hat x Hx Hx'.
    refine (pjm_at_disj B ARx LAWS ly S Hp W mem md (js_Lam en) _ _ _ _ _ _ (js_regs en) (js_d en) p ly2 S2 Hp2 W2 mem2 md2
      (a - cf_head) (kk + cf_head) HARc HAR2 HLED Hat Hsp0c Hfr2 Efa2 Hab2 _ _ x Hx _); [| | lia].
    - intros a' k' Hin' H1 H2. split.
      + exact (proj2 (pjm_lam_blk B ly2 S2 Hp2 W2 mem2 _ _ _ _ _ _ _ a' k' HLED2' (HSL' a' k' p Hp' Hin' H1 H2))).
      + intros E. apply Hfresh. rewrite <- E. exact (proj2 (pjm_lam_blk B ly S Hp W mem _ _ _ _ _ _ _ a' k' HLED Hin')).
    - intros b m Hbm HnL H1 H2. split; [exact (proj1 (HSB' b m p Hp' Hbm HnL H1 H2))|].
      intros E. apply Hfresh. rewrite <- E. exact Hbm. }
  split; [exact Hfresh|].
  split; [exact (Hoff (js_o en) (or_introl eq_refl) HatO) | exact (Hoff (js_w en) (or_intror eq_refl) HatW)]. }
(* the FAIL cut after the kids moved and the keys realloc is the CHOSEN failure (c = 2) *)
assert (HF2 : forall k' Lam',
  js_n en = js_cap en -> 4096 + cf_head <= k' -> k' mod 16 = 0 ->
  prhReader_swap B ly S Hp (js_Lam en) ly2 S2 Hp2 Lam' (kids_blkR (js_kids en) (js_cap en))
    [(k', 56 * cap2R (js_cap en))] ->
  prh_ledger (PA := PA) B ly2 S2 Hp2 W2 mem2 Lam' (Z.max (js_peak en) (Ledger.lsum Lam')) (js_cnt en + 2) SIZE_MAXZ
    (js_ran en) (js_most en) (js_own en) ->
  bytes_at (PA := PA) W2 mem2 k' KB -> bytes_at (PA := PA) W2 mem2 (js_keys en) YB ->
  pj_hdrR SEGS (rdW W2 mem2) (js_o en) 6 (js_num en) (js_str en) k' (js_keys en) (js_n en) (js_cap en) ->
  js_cnt en <> js_fail en -> js_cnt en + 1 = js_fail en -> pjs_PB S2 -> PresetHullBudget.hull_budget S2 [] ->
  pjs_FAILc B ARx dd en ly2 S2 Hp2 W2 regs2 mem2 (with_vm_backing (m_vm_lazy md2) X3 md2) (k + k1)).
{ intros k' Lam' Enc Hk'1 Hk'2 HSW HLED2 HBK HBY HHDR2 Ecf Ecf1 HPB HHB.
  destruct HSW as ((bl & Hb1 & Hb2) & _ & (Lam0 & HL1 & HL2)).
  assert (HDx : forall b, In b (kids_blkR (js_kids en) (js_cap en)) -> In b (js_D en))
    by (intros b Hb; rewrite ED'; apply in_or_app; left; apply in_or_app; left; exact Hb).
  destruct (HSWAP _ _ Lam' Lam0 bl _ _ _ _ _ _ HDx HL1 HL2 Hb1 Hb2 HLED2) as (HSL & HSB & HSK & HNEW).
  assert (Hnx : ~ In (k', 56 * cap2R (js_cap en)) (kids_blkR (js_kids en) (js_cap en))).
  { unfold kids_blkR. destruct (Z.eqb_spec (js_cap en) 0) as [E0|E0]; [intros []|].
    intros [E|[]]. injection E as _ E. lia. }
  destruct (HNEW k' (56 * cap2R (js_cap en)) ltac:(left; reflexivity) Hnx ltac:(lia)) as (Hfresh & HoffO & HoffW).
  set (Do := (k', 56 * cap2R (js_cap en)) :: keys_blkR 6 (js_keys en) (js_cap en) ++ Di).
  assert (HrestD : forall b, In b (keys_blkR 6 (js_keys en) (js_cap en) ++ Di) -> In b (js_D en)).
  { intros b Hb. rewrite ED', <- app_assoc. apply in_or_app. right. exact Hb. }
  assert (HrestX : forall b, In b (keys_blkR 6 (js_keys en) (js_cap en) ++ Di) -> ~ In b (kids_blkR (js_kids en) (js_cap en))).
  { intros b Hb Hx. pose proof HNDl as HN'. rewrite ED', <- app_assoc in HN'. exact (pjm_nodup_disj _ _ b HN' Hx Hb). }
  assert (Hrest0 : forall b, In b (keys_blkR 6 (js_keys en) (js_cap en) ++ Di) -> In b Lam0).
  { intros [a kk] Hb. exact (pjm_swap_lam0 (js_Lam en) Lam0 _ (a, kk) HL1 (HDin a kk (HrestD _ Hb)) (HrestX _ Hb)). }
  assert (HL2in : forall b, In b Lam0 -> In b Lam')
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HL2)); right; exact Hb).
  assert (HkLam : In (k', 56 * cap2R (js_cap en)) Lam')
    by (apply (Permutation_in _ (Permutation_sym HL2)); left; reflexivity).
  assert (HNDL' : List.NoDup ((k', 56 * cap2R (js_cap en)) :: Lam0)).
  { pose proof HLED2 as (_ & HN2 & _). apply pjm_nd in HN2. apply NoDup_map_inv in HN2. exact (Permutation_NoDup HL2 HN2). }
  pose proof (proj1 (proj1 (NoDup_cons_iff _ _) HNDL')) as Hk0n.
  assert (HDoNd : NoDup Do).
  { apply pjm_nd'. unfold Do. apply (pjm_nodup_sub [(k', 56 * cap2R (js_cap en))] Lam0 _ HNDL').
    - pose proof HNDl as HN'. rewrite ED', <- app_assoc in HN'. exact (NoDup_app_remove_l _ _ HN').
    - intros b Hb. exact (Hrest0 b Hb). }
  assert (HDoL : forall a kk, In (a, kk) Do -> In (a, kk) Lam').
  { intros a kk [E|Hb]; [rewrite <- E; exact HkLam | exact (HL2in _ (Hrest0 _ Hb))]. }
  assert (HDwL : forall a kk, In (a, kk) (js_Dw en) -> In (a, kk) Lam').
  { intros a kk Hb. apply HL2in. apply (pjm_swap_lam0 (js_Lam en) Lam0 _ (a, kk) HL1 (HDwin a kk Hb)).
    intros Hx. exact (HDDW _ Hb (HDx _ Hx)). }
  assert (HDisDo : forall bk, In bk (js_Dw en) -> ~ In bk Do).
  { intros [a kk] Hb [E|Hr].
    - apply Hk0n. rewrite E. apply (pjm_swap_lam0 (js_Lam en) Lam0 _ (a, kk) HL1 (HDwin a kk Hb)).
      intros Hx. exact (HDDW _ Hb (HDx _ Hx)).
    - exact (HDDW _ Hb (HrestD _ Hr)). }
  assert (HWOo : forall x, js_w en <= x < js_w en + 56 -> ~ pj_footR (js_o en) Do x).
  { intros x Hx [Hh|((a, kk) & [E|Hb] & Hy)].
    - apply (HWO x Hx). left. exact Hh.
    - injection E as <- <-. exact (HoffW x Hx Hy).
    - apply (HWO x Hx). right. exists (a, kk). split; [exact (HrestD _ Hb) | exact Hy]. }
  assert (HApo : pj_apartR Do (js_o en)).
  { intros [a kk] x [E|Hb] Hy Hx.
    - injection E as <- <-. exact (HoffO x Hx Hy).
    - exact (HNA (a, kk) x (HrestD _ Hb) Hy Hx). }
  assert (HMEMS2 : pj_memsR SEGS (rdW W2 mem2) (prh_lin Lam') (pj_nodeR SEGS (rdW W2 mem2) (prh_lin Lam')) k'
    (js_keys en) (js_ms en) Di).
  { apply (pjst_mems_move SEGS (js_ms en) (rdW W mem) (rdW W2 mem2) (prh_lin (js_Lam en)) (prh_lin Lam')
      (js_kids en) (js_keys en) k' (js_keys en) Di HMEMS).
    - intros j Hj. exact (pjm_garr8_eq SEGS _ _ _ _ KB HKBg HBK j ltac:(lia)).
    - intros j Hj. exact (pjm_garr8_eq SEGS _ _ _ _ YB HYBg HBY j ltac:(lia)).
    - intros x Hx. apply (pjm_lam_writable B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ _ _ _ _ _ _ _ x HAR2 HLED2 HkLam). lia.
    - lia.
    - intros [a' k''] x Hb Hx Hk.
      assert (Hb' : In (a', k'') (keys_blkR 6 (js_keys en) (js_cap en) ++ Di)) by (apply in_or_app; right; exact Hb).
      pose proof (pjs_req (56 * cap2R (js_cap en) + @cf_head cp) ltac:(lia)) as (Rq & _).
      apply (pjm_lam_off B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ _ _ _ _ _ k' (56 * cap2R (js_cap en)) a' k'' x HAR2 HLED2
        HkLam (HL2in _ (Hrest0 _ Hb'))); [| exact Hx | lia].
      intros E. apply Hk0n. rewrite <- E. exact (Hrest0 _ Hb').
    - exact HAGDi.
    - intros a kk Hb. exact (HL2in _ (Hrest0 _ (in_or_app _ _ _ (or_intror Hb)))). }
  assert (HDATA2 : pjs_data_c B dd en ly2 S2 Lam' W2 mem2).
  { apply (pjs_datac_kept B ARx LAWS VIS dd en ly S Hp W mem mdc (js_Lam en) (js_peak en) (js_cnt en) (js_fail en)
      (js_ran en) (js_most en) (js_own en) (STK_grow + (48 + js_d en)) (js_sp0 en + js_d en) FP1 ly2 S2 Hp2 W2 mem2 md2 k1
      Lam' _ _ _ _ _ _ HARm HJc HLED HLED2 HFPs HSINK HkFP).
    - rewrite Eslo. unfold js_sp0 in *. lia.
    - rewrite Eshi. unfold js_sp0 in *. lia.
    - intros x Hx. apply HPRW. unfold js_sp1, js_sp0, PJS_FR in *. lia.
    - unfold js_sp0 in *. lia.
    - exact HSL.
    - exact HSB.
    - exact HSK.
    - exact HROOM2.
    - exact HDATA. }
  pose proof HDATA2 as (_ & (_ & HatO2 & _) & HSW2 & _).
  assert (HNODEW2 : pj_nodeR SEGS (rdW W2 mem2) (prh_lin Lam') (js_w en) (js_tv en) (js_Dw en))
    by exact (pjst_node_frame SEGS (js_tv en) _ _ _ _ _ _ HNODEW HAGW HDwL).
  split; [exact HINV3|]. split; [exact HROOM2|].
  exists Lam', (Z.max (js_peak en) (Ledger.lsum Lam')), SIZE_MAXZ, (js_ran en), 2%nat, [true; false], Do, Lr.
  split; [replace (js_cnt en + Z.of_nat 2) with (js_cnt en + 2) by lia; exact HLED2|].
  (* the outcome cell: the kids granted, the keys realloc the chosen failure, g_ran_out kept *)
  split; [apply pjm_oks_chosen; [lia | reflexivity | intros i Hi; replace i with 0%nat by lia; reflexivity | lia]|].
  split; [split; [intros _; reflexivity | intros Hn; exfalso; apply Hn; lia]|].
  split; [exact HpLam|].
  split.
  { assert (E0 : Permutation Lam0 ((keys_blkR 6 (js_keys en) (js_cap en) ++ Di) ++ js_Dw en ++ Lr)).
    { apply (Permutation_app_inv_l (kids_blkR (js_kids en) (js_cap en))).
      apply (Permutation_trans (Permutation_sym HL1)). apply (Permutation_trans HpLam). rewrite ED'.
      rewrite <- !app_assoc. apply Permutation_refl. }
    apply (Permutation_trans HL2). unfold Do. cbn [app]. apply perm_skip. exact E0. }
  split.
  { destruct (pjm_blocks_other B ly S Hp W mem _ _ _ _ _ _ _ HLED) as (other & Ho). exists other.
    split; [rewrite <- Eab; exact Ho|].
    exact (pjm_blocks_swap B ly S ly2 S2 (js_Lam en) Lam' Lam0 _ _ bl other HL1 HL2 Hb1 Hb2 Ho). }
  split; [exact HNI|].
  split; [rewrite Hlen, (proj2 (Z.eqb_eq _ _) Enc); cbv iota; lia|].
  split; [reflexivity|].
  split; [intros i Hi; replace i with 0%nat by lia; reflexivity|].
  (* THE FAILURE IS THE CHOSEN ONE, and the peak is the granted run's *)
  split; [lia|].
  split; [reflexivity|].
  split; [exact HPB|].
  split.
  { exists (kids_blkR (js_kids en) (js_cap en)), [(k', 56 * cap2R (js_cap en))],
      (keys_blkR 6 (js_keys en) (js_cap en) ++ Di).
    split; [rewrite ED', <- app_assoc; apply Permutation_refl|].
    split; [apply Permutation_refl|].
    split; [intros a kk [E|[]]; injection E as <- <-; rewrite <- Eab; exact Hfresh|].
    right; left. split; [exact Enc|]. split; [reflexivity|]. split; [reflexivity|]. exists k'. reflexivity. }
  split.
  { intros md0 ly3 S3 Hp3 W3 mem3 md3 k3 Lam3 HJf HXf HP3. split.
    - pose proof HHDR2 as Hh2. rewrite Es0 in Hh2.
      apply (pjm_obl_parts B ARx LAWS dd en ly2 S2 Hp2 W2 mem2 md2 Lam' _ _ _ _ _ _ md0 ly3 S3 Hp3 W3 mem3 md3 k3 Lam3 Lr
        (js_num en) k' (js_keys en) (js_n en) (js_cap en) (56 * cap2R (js_cap en)) (js_ms en) Di Do
        Hsp0c HSTKF HAR2 HLED2 HatO2 HDoL HDwL HDisDo HAPW HWOo HJf HXf Hh2 HMEMS2 En0 Hcn).
      + intros E0. destruct Hcap0 as [(_ & _ & Hy) | (Hp0 & _)]; [exact Hy | lia].
      + lia.
      + reflexivity.
      + exact HDoNd.
      + exact HApo.
      + exact HP3.
    - intros Ec. exfalso. rewrite Hlen, (proj2 (Z.eqb_eq _ _) Enc) in Ec. discriminate Ec. }
  split; [exact HNODEW2|]. split; [exact HSW2 | exact HHB]. }
(* the run premises of the arms' own events at the entry position, each a prefix of grow's all-granted events (the
   entry's run premise HRUNG): [] after a kids NULL, the kids realloc's event after a keys NULL, both when both moved *)
assert (HRUN0 : js_n en = js_cap en ->
  prh_run_at ReaderRes.jr_strtod (js_x en) (js_os en) (js_i en) (prhPg_evs true (js_n en) (js_cap en) [false])).
{ intros Enc. unfold prhPg_evs. rewrite (proj2 (Z.ltb_ge (js_n en) (js_cap en))) by lia.
  unfold prh_run_at. reflexivity. }
assert (HRUN1 : js_n en = js_cap en ->
  prh_run_at ReaderRes.jr_strtod (js_x en) (js_os en) (js_i en) (prhPg_evs true (js_n en) (js_cap en) [true; false])).
{ intros Enc.
  assert (E2 : prhPg_evs true (js_n en) (js_cap en) [] =
    prhPg_evs true (js_n en) (js_cap en) [true; false] ++ [prhPg_ev 8 (js_cap en)]).
  { unfold prhPg_evs. rewrite (proj2 (Z.ltb_ge (js_n en) (js_cap en))) by lia. reflexivity. }
  pose proof HRUNG as H. rewrite E2 in H. exact (proj1 (proj1 (prh_run_at_app_iff _ _ _ _ _ _) H)). }
assert (E11 : prhPg_evs true (js_n en) (js_cap en) [true; true] = prhPg_evs true (js_n en) (js_cap en) [])
  by (unfold prhPg_evs; reflexivity).
assert (HRUN2 : prh_run_at ReaderRes.jr_strtod (js_x en) (js_os en) (js_i en)
  (prhPg_evs true (js_n en) (js_cap en) [true; true]))
  by (rewrite E11; exact HRUNG).
(* the object's block list with its arrays in front, when it has arrays *)
assert (ED1 : 0 < js_cap en -> js_D en = (js_kids en, 56 * js_cap en) :: (js_keys en, 8 * js_cap en) :: Di).
{ intros Hc. rewrite ED. rewrite (proj2 (Z.eqb_neq (js_cap en) 0)) by lia. reflexivity. }
destruct HARM as [A1 | [A2 | [A3 | [A4 | [A5 | [A6 | A7]]]]]].
- (* n < cap: nothing done, a0 = 0: to DUP *)
  pjsm_split A1.
  lazymatch goal with H : js_n en < js_cap en |- _ => rename H into Hlt end.
  lazymatch goal with H : getr regs2 10 = w64 0 |- _ => rename H into HA0 end.
  lazymatch goal with H : ablocks B ly2 S2 = ablocks B ly S |- _ => rename H into Eab2 end.
  lazymatch goal with H : prh_ledger _ ly2 S2 Hp2 W2 mem2 _ _ _ _ _ _ _ |- _ => rename H into HLED2 end.
  lazymatch goal with H : pj_hdrR _ (rdW W2 mem2) _ _ _ _ _ _ _ _ |- _ => rename H into HHDR2 end.
  lazymatch goal with H : forall lo hi x, In (lo, hi) _ -> _ |- _ => rename H into HKEEP2 end.
  lazymatch goal with H : forall sm x os i H0 hist, PresetRoomPos.iface_room_pos sm x os i H0 hist S -> _ |- _ =>
    rename H into HPOS2 end.
  lazymatch goal with |- context [c_eq (getr ?R ?r1) (getr ?R ?r2)] =>
    replace (c_eq (getr R r1) (getr R r2)) with true
      by (replace r1 with (10%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity);
          replace r2 with (0%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity);
          rewrite HA0, getr_zero; vm_compute; reflexivity) end.
  cbv iota.
  lazymatch goal with |- context [btgt ?p ?i] =>
    replace (btgt p i) with (Z_to_bv 64 (BASE + PJS_DUP)) by (apply bv_eq; vm_compute; reflexivity) end.
  apply SRr_ret.
  apply (HDUP en ly2 S2 Hp2 W2 regs2 mem2 (with_vm_backing (m_vm_lazy md2) X3 md2) (k + k1) HPRE0).
  assert (HDATA2 : pjs_data_c B dd en ly2 S2 (js_Lam en) W2 mem2).
  { apply (pjs_datac_kept B ARx LAWS VIS dd en ly S Hp W mem mdc (js_Lam en) (js_peak en) (js_cnt en) (js_fail en)
      (js_ran en) (js_most en) (js_own en) (STK_grow + (48 + js_d en)) (js_sp0 en + js_d en) FP1 ly2 S2 Hp2 W2 mem2 md2 k1
      (js_Lam en) (js_peak en) (js_cnt en) (js_fail en) (js_ran en) (js_most en) (js_own en) HARm HJc HLED HLED2 HFPs HSINK HkFP).
    - rewrite Eslo. unfold js_sp0 in *. lia.
    - rewrite Eshi. unfold js_sp0 in *. lia.
    - intros x Hx. apply HPRW. unfold js_sp1, js_sp0, PJS_FR in *. lia.
    - unfold js_sp0 in *. lia.
    - intros a kk p _ Hin _ _. exact Hin.
    - intros b m p _ Hbm HnL _ _. rewrite Eab2. split; [exact Hbm | exact HnL].
    - intros a kk Hin _ _. exact Hin.
    - exact HROOM2.
    - exact HDATA. }
  assert (HNODE2 : pj_nodeR SEGS (rdW W2 mem2) (prh_lin (js_Lam en)) (js_o en) (PjTree.JObj (js_ms en)) (js_D en)).
  { apply (HMOLD _ _ _ _ _ _ HLED2 HHDR2).
    - intros j Hj. apply (mbyte_of_aview SEGS).
      destruct Hcap0 as [(E0 & _ & _) | (Hc0 & _ & _)]; [lia|].
      pose proof (pjm_req_eq (56 * js_cap en + @cf_head cp) ltac:(lia)) as Rq.
      apply (HKEEP2 (js_kids en - cf_head) (js_kids en - cf_head + req_size (56 * js_cap en + cf_head)));
        [|rewrite Rq; lia].
      unfold ablocks_fp, prhReader_ab. rewrite map_map. apply in_map_iff. exists (js_kids en, 56 * js_cap en).
      split; [reflexivity|]. apply in_or_app. left. unfold kids_blkR.
      rewrite (proj2 (Z.eqb_neq (js_cap en) 0)) by lia. left. reflexivity.
    - intros j Hj. apply (mbyte_of_aview SEGS).
      destruct Hcap0 as [(E0 & _ & _) | (Hc0 & _ & _)]; [lia|].
      pose proof (pjm_req_eq (8 * js_cap en + @cf_head cp) ltac:(lia)) as Rq.
      apply (HKEEP2 (js_keys en - cf_head) (js_keys en - cf_head + req_size (8 * js_cap en + cf_head)));
        [|rewrite Rq; lia].
      unfold ablocks_fp, prhReader_ab. rewrite map_map. apply in_map_iff. exists (js_keys en, 8 * js_cap en).
      split; [reflexivity|]. apply in_or_app. right. unfold keys_blkR.
      rewrite (proj2 (Z.eqb_neq (js_cap en) 0)) by lia. left. reflexivity. }
  assert (HNODEW2 : pj_nodeR SEGS (rdW W2 mem2) (prh_lin (js_Lam en)) (js_w en) (js_tv en) (js_Dw en))
    by exact (pjst_node_frame SEGS (js_tv en) _ _ _ _ _ _ HNODEW HAGW HDwin).
  (* the capacity after the append is the model's: room was left, so it is kept (pjm_ncap_S) *)
  assert (ECAP2 : js_cap en = Z.of_nat (PresetReqAt.ncap (Datatypes.S (length (js_ms en))))).
  { rewrite pjm_ncap_S, <- ECAP. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
  (* THE OBJECT'S ORDERED FREE LIST at DUP: the slot list carried across grow's no-op arm (it kept the slot blocks'
     bytes, and the members' blocks are off its footprint; PRH_PjOrder.pf_oitemsR_frame), reassembled at the unchanged
     header (pjsf_obj_intro) over a permutation of the entry's block list (pjm_foR_perm) *)
  assert (HORDD : forall nn, (PjTree.depth (PjTree.JObj (js_ms en)) <= nn)%nat ->
     exists F, PRH_PjOrder.pj_foR SEGS (rdW W2 mem2) (prh_lin (js_Lam en)) nn (js_o en) (js_D en) F /\
       map (fun b => snd b + PresetReqAt.HEAD) F =
         PjFoMember.pfm_slots PresetReqAtNoMiss.kblk (js_ms en) ++
         PresetReqAt.arrz true (PresetReqAt.ncap (Datatypes.S (length (js_ms en))))).
  { intros nn Hnn. destruct nn as [|d]; [exfalso; cbn [PjTree.depth] in Hnn; lia|].
    destruct (HORD d Hnn) as (DiF & FiF & HOI & HPDi & HMFi & _).
    destruct Hcap0 as [(E0 & _ & _) | (Hc0 & Hkb & Hyb)]; [lia|].
    assert (HDiFi : forall b, In b DiF -> In b Di)
      by (intros b Hb; exact (Permutation_in _ (Permutation_sym HPDi) Hb)).
    assert (HOI2 : PRH_PjOrder.pf_oitemsR SEGS (rdW W2 mem2) (prh_lin (js_Lam en))
        (PRH_PjOrder.pj_foR SEGS (rdW W2 mem2) (prh_lin (js_Lam en)) d) true (js_kids en) (js_keys en)
        (length (js_ms en)) DiF FiF).
    { apply (PRH_PjOrder.pf_oitemsR_frame SEGS d (rdW W mem) (rdW W2 mem2) (prh_lin (js_Lam en))
        (prh_lin (js_Lam en)) true (js_kids en) (js_keys en) (length (js_ms en)) DiF FiF HOI).
      - intros x kk Hx. exact (HDin x kk (HDiD x kk (HDiFi _ Hx))).
      - intros x [Hx | [(_ & Hx) | (b & Hb & Hx)]].
        + split.
          * apply (mbyte_of_aview SEGS).
            pose proof (pjm_req_eq (56 * js_cap en + @cf_head cp) ltac:(lia)) as Rq.
            apply (HKEEP2 (js_kids en - cf_head) (js_kids en - cf_head + req_size (56 * js_cap en + cf_head)));
              [|rewrite Rq; lia].
            unfold ablocks_fp, prhReader_ab. rewrite map_map. apply in_map_iff. exists (js_kids en, 56 * js_cap en).
            split; [reflexivity|]. apply in_or_app. left. unfold kids_blkR.
            rewrite (proj2 (Z.eqb_neq (js_cap en) 0)) by lia. left. reflexivity.
          * intros _. apply (pjm_lam_writable B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ _ _ _ _ _ _ _ x HAR2 HLED2 Hkb).
            lia.
        + split.
          * apply (mbyte_of_aview SEGS).
            pose proof (pjm_req_eq (8 * js_cap en + @cf_head cp) ltac:(lia)) as Rq.
            apply (HKEEP2 (js_keys en - cf_head) (js_keys en - cf_head + req_size (8 * js_cap en + cf_head)));
              [|rewrite Rq; lia].
            unfold ablocks_fp, prhReader_ab. rewrite map_map. apply in_map_iff. exists (js_keys en, 8 * js_cap en).
            split; [reflexivity|]. apply in_or_app. right. unfold keys_blkR.
            rewrite (proj2 (Z.eqb_neq (js_cap en) 0)) by lia. left. reflexivity.
          * intros _. apply (pjm_lam_writable B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ _ _ _ _ _ _ _ x HAR2 HLED2 Hyb).
            lia.
        + apply HAGDi. cbv beta. exists b. split; [exact (HDiFi _ Hb) | exact Hx]. }
    assert (HPF : Permutation (js_D en) ((js_kids en, 56 * js_cap en) :: (js_keys en, 8 * js_cap en) :: DiF))
      by (rewrite (ED1 Hc0); apply perm_skip; apply perm_skip; exact HPDi).
    assert (HNDF : List.NoDup ((js_kids en, 56 * js_cap en) :: (js_keys en, 8 * js_cap en) :: DiF))
      by exact (Permutation_NoDup HPF HNDl).
    assert (HOI3 : PRH_PjOrder.pf_oitemsR SEGS (rdW W2 mem2) (prh_lin (js_Lam en))
        (PRH_PjOrder.pj_foR SEGS (rdW W2 mem2) (prh_lin (js_Lam en)) d) true (js_kids en) (js_keys en)
        (Z.to_nat (js_n en)) DiF FiF) by (rewrite En0, Nat2Z.id; exact HOI2).
    pose proof HHDR2 as Hh2. rewrite Es0 in Hh2.
    assert (HFO2 := pjsf_obj_intro SEGS (rdW W2 mem2) (prh_lin (js_Lam en)) d (js_o en) (js_num en) (js_kids en)
      (js_keys en) (js_n en) (js_cap en) DiF FiF Hh2 ltac:(lia) Hc0 Hkb Hyb ltac:(pjsm_nd HNDF)
      ltac:(intros b x Hb; apply HNA; exact (Permutation_in _ (Permutation_sym HPF) Hb)) HOI3).
    exists (FiF ++ [(js_kids en, 56 * js_cap en); (js_keys en, 8 * js_cap en)]).
    split; [exact (pjm_foR_perm SEGS _ _ _ _ _ _ _ HFO2 (Permutation_sym HPF))|].
    rewrite map_app, HMFi. f_equal. rewrite ECAP2. exact (pjsf_arrz_of _ _ _ (pjm_ncap_S_pos _)). }
  split; [exact HINV3|]. split; [exact HROOM2|].
  exists (js_Lam en), (js_peak en), 0%nat, [], (js_D en), Lr, (js_kids en), (js_keys en), (js_cap en), [], [], (js_D en).
  split; [replace (js_cnt en + Z.of_nat 0) with (js_cnt en) by lia; exact HLED2|].
  (* the outcome cell: no allocation, nothing refused, g_ran_out kept *)
  split; [apply pjm_oks_granted; [intros i Hi; exfalso; lia | lia]|].
  split; [intros i Hi; exfalso; lia|].
  split; [lia|].
  split; [exact HpLam|].
  split; [exact HpLam|].
  split; [destruct (pjm_blocks_other B ly S Hp W mem _ _ _ _ _ _ _ HLED) as (other & Ho); exists other;
          split; [rewrite <- Eab; exact Ho | rewrite Eab2; exact Ho]|].
  split; [exact HNI|].
  split; [apply Permutation_refl|].
  split; [apply Permutation_refl|].
  split; [intros a kk []|].
  split; [left; split; [exact Hlt|]; repeat split|].
  split; [pose proof (prh_ledger_bounds B _ _ _ _ _ _ _ _ _ _ _ _ HLED) as (Hlp & _); lia|].
  split; [exact Hlt|].
  split.
  { (* grow's position implication at js_i: no event (n < cap), the position kept *)
    assert (Hh : exists h, PresetRoomPos.iface_room_pos ReaderRes.jr_strtod (js_x en) (js_os en)
        (js_i en + length (prhPg_evs true (js_n en) (js_cap en) []))%nat (js_H0 en) h S2)
      by exact (HPOS2 _ _ _ _ _ _ HPOSS HRUNG).
    assert (E0 : prhPg_evs true (js_n en) (js_cap en) [] = []).
    { unfold prhPg_evs. rewrite (proj2 (Z.ltb_lt (js_n en) (js_cap en))) by exact Hlt. reflexivity. }
    rewrite E0 in Hh. exact Hh. }
  split.
  { destruct (pjm_gtrace (js_n en) (js_cap en) ltac:(lia)) as (Gh & Gc).
    rewrite (proj2 (Z.eqb_neq (js_n en) (js_cap en))) in Gh, Gc by lia. cbv iota in Gh, Gc.
    unfold PRH_Charge.prh_held in HBB. change (6 =? 6) with true in HBB. rewrite Gh, Gc in HBB.
    rewrite (blocks_bytes_bsum B ly S), Eab, <- (blocks_bytes_bsum B (js_ly en) (js_S en)) in HBB.
    unfold LIVE_pj_set in HLIVE. rewrite (proj2 (Z.eqb_neq (js_n en) (js_cap en))) in HLIVE by lia.
    unfold js_klen in *. lia. }
  split; [exact HNODE2|].
  split; [exact HHDR2|].
  split; [exact HSLOTS0|].
  split; [exact H9'|].
  split; [exact HNODEW2|]. split; [exact HDATA2|].
  (* the block lists in order: nothing replaced, Dr = js_D *)
  split; [reflexivity|]. split; [reflexivity|].
  (* the capacities are the model's; the object's ordered free list; val's entry agreement, kept across grow *)
  split; [exact ECAP|]. split; [exact ECAP2|]. split; [exact HORDD|].
  exact (pjs_agree_trans _ _ _ _ HAGRW0 HAGW).
- (* the kids realloc is the CHOSEN failure: to FAIL, c = 1 *)
  pjsm_split A2.
  lazymatch goal with H : js_n en = js_cap en |- _ => rename H into Enc end.
  lazymatch goal with H : js_cnt en = js_fail en |- _ => rename H into Ecf end.
  lazymatch goal with H : getr regs2 10 = w64 (-1) |- _ => rename H into HA0 end.
  lazymatch goal with H : ablocks B ly2 S2 = ablocks B ly S |- _ => rename H into Eab2 end.
  lazymatch goal with H : prh_ledger _ ly2 S2 Hp2 W2 mem2 _ _ _ _ _ _ _ |- _ => rename H into HLED2 end.
  lazymatch goal with H : pj_hdrR _ (rdW W2 mem2) _ _ _ _ _ _ _ _ |- _ => rename H into HHDR2 end.
  lazymatch goal with H : bytes_at W2 mem2 (js_kids en) KB |- _ => rename H into HBK end.
  lazymatch goal with H : 6 = 6 -> bytes_at W2 mem2 (js_keys en) YB |- _ => rename H into HBY end.
  lazymatch goal with H : forall sm x os i H0 hist, PresetRoomPos.iface_room_pos sm x os i H0 hist S -> _ |- _ =>
    rename H into HPOS2 end.
  lazymatch goal with |- context [c_eq (getr ?R ?r1) (getr ?R ?r2)] =>
    replace (c_eq (getr R r1) (getr R r2)) with false
      by (replace r1 with (10%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity);
          replace r2 with (0%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity);
          rewrite HA0, getr_zero; vm_compute; reflexivity) end.
  cbv iota.
  replace (v_addi (Z_to_bv 64 (BASE + (PJS_MISS + 8))) 4) with (Z_to_bv 64 (BASE + PJS_FAIL))
    by (apply bv_eq; vm_compute; reflexivity).
  apply SRr_ret.
  apply (HFAIL en ly2 S2 Hp2 W2 regs2 mem2 (with_vm_backing (m_vm_lazy md2) X3 md2) (k + k1) HPRE0).
  apply (HF1 Enc Eab2 HLED2 HHDR2 HBK (HBY eq_refl) Ecf); [|exact HHB2].
  destruct (HPOS2 _ _ _ _ _ _ HPOSS (HRUN0 Enc)) as (h2 & Hh2). exact (pjm_pb_of_pos _ _ _ _ _ _ _ Hh2).
- (* the kids realloc is refused: DEAD, excluded at the entry position by the arm's own exclusion clause (the run
     premise of grow's all-granted events and their consumer premise, both from pjs_pre) *)
  exfalso. pjsm_split A3.
  match goal with H : forall sm x os i H0 hist, _ -> _ -> prh_cons_from _ _ _ _ _ -> False |- _ =>
    exact (H _ _ _ _ _ _ HPOSS HRUNG HCONSG) end.
- (* an array: impossible, the tag is 6 *)
  exfalso. pjsm_split A4.
  lazymatch goal with H : 6 <> 6 |- _ => exact (H eq_refl) end.
- (* the kids moved, the keys realloc is the CHOSEN failure: to FAIL, c = 2 *)
  pjsm_split A5.
  lazymatch goal with H : js_n en = js_cap en |- _ => rename H into Enc end.
  lazymatch goal with H : js_cnt en <> js_fail en |- _ => rename H into Ecf end.
  lazymatch goal with H : js_cnt en + 1 = js_fail en |- _ => rename H into Ecf1 end.
  lazymatch goal with H : getr regs2 10 = w64 (-1) |- _ => rename H into HA0 end.
  lazymatch goal with H : exists k' Lam', 4096 + cf_head <= k' /\ _ |- _ => destruct H as (k' & Lam' & HA5) end.
  pjsm_split HA5.
  lazymatch goal with H : 4096 + cf_head <= k' |- _ => rename H into Hk'1 end.
  lazymatch goal with H : k' mod 16 = 0 |- _ => rename H into Hk'2 end.
  lazymatch goal with H : prhReader_swap _ _ _ _ _ ly2 S2 Hp2 Lam' _ _ |- _ => rename H into HSW end.
  lazymatch goal with H : prh_ledger _ ly2 S2 Hp2 W2 mem2 Lam' _ _ _ _ _ _ |- _ => rename H into HLED2 end.
  lazymatch goal with H : bytes_at W2 mem2 k' KB |- _ => rename H into HBK end.
  lazymatch goal with H : bytes_at W2 mem2 (js_keys en) YB |- _ => rename H into HBY end.
  lazymatch goal with H : pj_hdrR _ (rdW W2 mem2) _ _ _ _ _ _ _ _ |- _ => rename H into HHDR2 end.
  lazymatch goal with H : forall sm x os i H0 hist, PresetRoomPos.iface_room_pos sm x os i H0 hist S -> _ |- _ =>
    rename H into HPOS2 end.
  lazymatch goal with |- context [c_eq (getr ?R ?r1) (getr ?R ?r2)] =>
    replace (c_eq (getr R r1) (getr R r2)) with false
      by (replace r1 with (10%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity);
          replace r2 with (0%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity);
          rewrite HA0, getr_zero; vm_compute; reflexivity) end.
  cbv iota.
  replace (v_addi (Z_to_bv 64 (BASE + (PJS_MISS + 8))) 4) with (Z_to_bv 64 (BASE + PJS_FAIL))
    by (apply bv_eq; vm_compute; reflexivity).
  apply SRr_ret.
  apply (HFAIL en ly2 S2 Hp2 W2 regs2 mem2 (with_vm_backing (m_vm_lazy md2) X3 md2) (k + k1) HPRE0).
  apply (HF2 k' Lam' Enc Hk'1 Hk'2 HSW HLED2 HBK HBY HHDR2 Ecf Ecf1); [|exact HHB2].
  destruct (HPOS2 _ _ _ _ _ _ HPOSS (HRUN1 Enc)) as (h2 & Hh2). exact (pjm_pb_of_pos _ _ _ _ _ _ _ Hh2).
- (* the kids moved, the keys realloc is refused: DEAD, excluded at the entry position by the arm's own exclusion
     clause *)
  exfalso. pjsm_split A6.
  lazymatch goal with H : exists k' Lam', 4096 + cf_head <= k' /\ _ |- _ => destruct H as (k' & Lam' & HA6) end.
  pjsm_split HA6.
  match goal with H : forall sm x os i H0 hist, _ -> _ -> prh_cons_from _ _ _ _ _ -> False |- _ =>
    exact (H _ _ _ _ _ _ HPOSS HRUNG HCONSG) end.
- (* both arrays moved, a0 = 0: to DUP *)
  pjsm_split A7.
  lazymatch goal with H : js_n en = js_cap en |- _ => rename H into Enc end.
  lazymatch goal with H : js_cnt en <> js_fail en |- _ => rename H into Ecf end.
  lazymatch goal with H : js_cnt en + 1 <> js_fail en |- _ => rename H into Ecf1 end.
  lazymatch goal with H : getr regs2 10 = w64 0 |- _ => rename H into HA0 end.
  lazymatch goal with H : exists k' y' Lam', 4096 + cf_head <= k' /\ _ |- _ => destruct H as (k' & y' & Lam' & HA7) end.
  pjsm_split HA7.
  lazymatch goal with H : prhReader_swap _ _ _ _ _ ly2 S2 Hp2 Lam' _ _ |- _ => rename H into HSW end.
  lazymatch goal with H : prh_ledger _ ly2 S2 Hp2 W2 mem2 Lam' _ _ _ _ _ _ |- _ => rename H into HLED2 end.
  lazymatch goal with H : Ledger.lsum Lam' = _ |- _ => rename H into HLS end.
  lazymatch goal with H : bytes_at W2 mem2 k' KB |- _ => rename H into HBK end.
  lazymatch goal with H : bytes_at W2 mem2 y' YB |- _ => rename H into HBY end.
  lazymatch goal with H : pj_hdrR _ (rdW W2 mem2) _ _ _ _ _ _ _ _ |- _ => rename H into HHDR2 end.
  lazymatch goal with H : pj_slots_atR (prh_lin Lam') _ k' y' _ _ |- _ => rename H into HSL2 end.
  lazymatch goal with H : forall sm x os i H0 hist, PresetRoomPos.iface_room_pos sm x os i H0 hist S -> _ |- _ =>
    rename H into HPOS2 end.
  lazymatch goal with |- context [c_eq (getr ?R ?r1) (getr ?R ?r2)] =>
    replace (c_eq (getr R r1) (getr R r2)) with true
      by (replace r1 with (10%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity);
          replace r2 with (0%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity);
          rewrite HA0, getr_zero; vm_compute; reflexivity) end.
  cbv iota.
  lazymatch goal with |- context [btgt ?p ?i] =>
    replace (btgt p i) with (Z_to_bv 64 (BASE + PJS_DUP)) by (apply bv_eq; vm_compute; reflexivity) end.
  apply SRr_ret.
  apply (HDUP en ly2 S2 Hp2 W2 regs2 mem2 (with_vm_backing (m_vm_lazy md2) X3 md2) (k + k1) HPRE0).
  destruct HSW as ((bl & Hb1 & Hb2) & _ & (Lam0 & HL1 & HL2)).
  assert (HDx : forall b, In b (kids_blkR (js_kids en) (js_cap en) ++ keys_blkR 6 (js_keys en) (js_cap en)) ->
    In b (js_D en)) by (intros [a kk] Hb; exact (HDoldD a kk Hb)).
  destruct (HSWAP _ _ Lam' Lam0 bl _ _ _ _ _ _ HDx HL1 HL2 Hb1 Hb2 HLED2) as (HSL & HSB & HSK & HNEW).
  assert (Hnxk : ~ In (k', 56 * cap2R (js_cap en)) (kids_blkR (js_kids en) (js_cap en) ++ keys_blkR 6 (js_keys en) (js_cap en))).
  { rewrite pjm_old_eq. destruct (Z.eqb_spec (js_cap en) 0) as [E0|E0]; [intros []|].
    intros [E|[E|[]]]; injection E as _ E; lia. }
  assert (Hnxy : ~ In (y', 8 * cap2R (js_cap en)) (kids_blkR (js_kids en) (js_cap en) ++ keys_blkR 6 (js_keys en) (js_cap en))).
  { rewrite pjm_old_eq. destruct (Z.eqb_spec (js_cap en) 0) as [E0|E0]; [intros []|].
    intros [E|[E|[]]]; injection E as _ E; lia. }
  destruct (HNEW k' (56 * cap2R (js_cap en)) ltac:(right; left; reflexivity) Hnxk ltac:(lia)) as (Hfk & HoOk & HoWk).
  destruct (HNEW y' (8 * cap2R (js_cap en)) ltac:(left; reflexivity) Hnxy ltac:(lia)) as (Hfy & HoOy & HoWy).
  set (Do := [(k', 56 * cap2R (js_cap en)); (y', 8 * cap2R (js_cap en))] ++ Di).
  assert (Hrest0 : forall b, In b Di -> In b Lam0).
  { intros [a kk] Hb. exact (pjm_swap_lam0 (js_Lam en) Lam0 _ (a, kk) HL1 (HDin a kk (HDiD a kk Hb)) (HDiold _ Hb)). }
  assert (HL2in : forall b, In b Lam0 -> In b Lam')
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HL2)); right; right; exact Hb).
  assert (HkLam : In (k', 56 * cap2R (js_cap en)) Lam')
    by (apply (Permutation_in _ (Permutation_sym HL2)); right; left; reflexivity).
  assert (HyLam : In (y', 8 * cap2R (js_cap en)) Lam')
    by (apply (Permutation_in _ (Permutation_sym HL2)); left; reflexivity).
  assert (HNDL' : List.NoDup ((y', 8 * cap2R (js_cap en)) :: (k', 56 * cap2R (js_cap en)) :: Lam0)).
  { pose proof HLED2 as (_ & HN2 & _). apply pjm_nd in HN2. apply NoDup_map_inv in HN2. exact (Permutation_NoDup HL2 HN2). }
  assert (HNDL'' : List.NoDup ((k', 56 * cap2R (js_cap en)) :: (y', 8 * cap2R (js_cap en)) :: Lam0))
    by exact (Permutation_NoDup (perm_swap _ _ _) HNDL').
  pose proof (proj1 (proj1 (NoDup_cons_iff _ _) HNDL'')) as Hk0n.
  pose proof (proj1 (proj1 (NoDup_cons_iff _ _) HNDL')) as Hy0n.
  assert (HDoNd : NoDup Do).
  { apply pjm_nd'. unfold Do. apply (pjm_nodup_sub [(k', 56 * cap2R (js_cap en)); (y', 8 * cap2R (js_cap en))] Lam0 Di HNDL'').
    - pose proof HNDl as HN'. rewrite ED' in HN'. exact (NoDup_app_remove_l _ _ HN').
    - intros b Hb. exact (Hrest0 b Hb). }
  assert (HApo : pj_apartR Do (js_o en)).
  { intros [a kk] x [E|[E|Hb]] Hy Hx.
    - injection E as <- <-. exact (HoOk x Hx Hy).
    - injection E as <- <-. exact (HoOy x Hx Hy).
    - exact (HNA (a, kk) x (HDiD a kk Hb) Hy Hx). }
  assert (HDwL : forall a kk, In (a, kk) (js_Dw en) -> In (a, kk) Lam').
  { intros a kk Hb. apply HL2in. apply (pjm_swap_lam0 (js_Lam en) Lam0 _ (a, kk) HL1 (HDwin a kk Hb)).
    intros Hx. exact (HDDW _ Hb (HDx _ Hx)). }
  assert (HMEMS2 : pj_memsR SEGS (rdW W2 mem2) (prh_lin Lam') (pj_nodeR SEGS (rdW W2 mem2) (prh_lin Lam')) k' y'
    (js_ms en) Di).
  { apply (pjst_mems_move SEGS (js_ms en) (rdW W mem) (rdW W2 mem2) (prh_lin (js_Lam en)) (prh_lin Lam')
      (js_kids en) (js_keys en) k' y' Di HMEMS).
    - intros j Hj. exact (pjm_garr8_eq SEGS _ _ _ _ KB HKBg HBK j ltac:(lia)).
    - intros j Hj. exact (pjm_garr8_eq SEGS _ _ _ _ YB HYBg HBY j ltac:(lia)).
    - intros x Hx. apply (pjm_lam_writable B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ _ _ _ _ _ _ _ x HAR2 HLED2 HkLam). lia.
    - lia.
    - intros [a' k''] x Hb Hx Hk.
      pose proof (pjs_req (56 * cap2R (js_cap en) + @cf_head cp) ltac:(lia)) as (Rq & _).
      apply (pjm_lam_off B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ _ _ _ _ _ k' (56 * cap2R (js_cap en)) a' k'' x HAR2 HLED2
        HkLam (HL2in _ (Hrest0 _ Hb))); [| exact Hx | lia].
      intros E. apply Hk0n. right. rewrite <- E. exact (Hrest0 _ Hb).
    - exact HAGDi.
    - intros a kk Hb. exact (HL2in _ (Hrest0 _ Hb)). }
  assert (HNODE2 : pj_nodeR SEGS (rdW W2 mem2) (prh_lin Lam') (js_o en) (PjTree.JObj (js_ms en)) Do).
  { pose proof HHDR2 as Hh2. rewrite Es0 in Hh2.
    destruct HSL2 as (_ & _ & _ & HSLp).
    apply (pjm_node_obj SEGS _ _ _ (js_num en) k' y' (js_n en) (cap2R (js_cap en)) _ Di _ Hh2 En0 ltac:(lia)).
    - right. destruct (HSLp ltac:(lia)) as (Hk & Hy). split; [lia|]. split; [exact Hk | exact (Hy eq_refl)].
    - exact HDoNd.
    - exact HApo.
    - unfold Do. rewrite (proj2 (Z.eqb_neq (cap2R (js_cap en)) 0)) by lia. reflexivity.
    - exact HMEMS2. }
  assert (HDATA2 : pjs_data_c B dd en ly2 S2 Lam' W2 mem2).
  { apply (pjs_datac_kept B ARx LAWS VIS dd en ly S Hp W mem mdc (js_Lam en) (js_peak en) (js_cnt en) (js_fail en)
      (js_ran en) (js_most en) (js_own en) (STK_grow + (48 + js_d en)) (js_sp0 en + js_d en) FP1 ly2 S2 Hp2 W2 mem2 md2 k1
      Lam' _ _ _ _ _ _ HARm HJc HLED HLED2 HFPs HSINK HkFP).
    - rewrite Eslo. unfold js_sp0 in *. lia.
    - rewrite Eshi. unfold js_sp0 in *. lia.
    - intros x Hx. apply HPRW. unfold js_sp1, js_sp0, PJS_FR in *. lia.
    - unfold js_sp0 in *. lia.
    - exact HSL.
    - exact HSB.
    - exact HSK.
    - exact HROOM2.
    - exact HDATA. }
  assert (HNODEW2 : pj_nodeR SEGS (rdW W2 mem2) (prh_lin Lam') (js_w en) (js_tv en) (js_Dw en))
    by exact (pjst_node_frame SEGS (js_tv en) _ _ _ _ _ _ HNODEW HAGW HDwL).
  destruct (pjm_gtrace (js_n en) (js_cap en) ltac:(lia)) as (Gh & Gc).
  rewrite (proj2 (Z.eqb_eq _ _) Enc) in Gh, Gc. cbv iota in Gh, Gc.
  change (6 =? 6) with true in HLS. rewrite Gh in HLS.
  (* the capacity after the append is the model's: the arrays were full, so it is cap2R's (pjm_ncap_S) *)
  assert (ECAP2 : cap2R (js_cap en) = Z.of_nat (PresetReqAt.ncap (Datatypes.S (length (js_ms en))))).
  { rewrite pjm_ncap_S, <- ECAP. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
  (* THE OBJECT'S ORDERED FREE LIST at DUP: the slot list moved with the arrays (pjsf_oitems_move: the facts
     pjst_mems_move takes above), reassembled at the new header (pjsf_obj_intro) over a permutation of Do *)
  assert (HORDD : forall nn, (PjTree.depth (PjTree.JObj (js_ms en)) <= nn)%nat ->
     exists F, PRH_PjOrder.pj_foR SEGS (rdW W2 mem2) (prh_lin Lam') nn (js_o en) Do F /\
       map (fun b => snd b + PresetReqAt.HEAD) F =
         PjFoMember.pfm_slots PresetReqAtNoMiss.kblk (js_ms en) ++
         PresetReqAt.arrz true (PresetReqAt.ncap (Datatypes.S (length (js_ms en))))).
  { intros nn Hnn. destruct nn as [|d]; [exfalso; cbn [PjTree.depth] in Hnn; lia|].
    destruct (HORD d Hnn) as (DiF & FiF & HOI & HPDi & HMFi & _).
    assert (HDiFi : forall b, In b DiF -> In b Di)
      by (intros b Hb; exact (Permutation_in _ (Permutation_sym HPDi) Hb)).
    assert (HOI2 : PRH_PjOrder.pf_oitemsR SEGS (rdW W2 mem2) (prh_lin Lam')
        (PRH_PjOrder.pj_foR SEGS (rdW W2 mem2) (prh_lin Lam') d) true k' y' (length (js_ms en)) DiF FiF).
    { apply (pjsf_oitems_move SEGS d (rdW W mem) (rdW W2 mem2) (prh_lin (js_Lam en)) (prh_lin Lam')
        (length (js_ms en)) (js_kids en) (js_keys en) k' y' DiF FiF HOI).
      - intros j Hj. exact (pjm_garr8_eq SEGS _ _ _ _ KB HKBg HBK j ltac:(lia)).
      - intros j Hj. exact (pjm_garr8_eq SEGS _ _ _ _ YB HYBg HBY j ltac:(lia)).
      - intros x Hx. apply (pjm_lam_writable B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ _ _ _ _ _ _ _ x HAR2 HLED2 HkLam).
        lia.
      - lia.
      - intros [a' k''] x Hb Hx Hk.
        pose proof (pjs_req (56 * cap2R (js_cap en) + @cf_head cp) ltac:(lia)) as (Rq & _).
        apply (pjm_lam_off B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ _ _ _ _ _ k' (56 * cap2R (js_cap en)) a' k'' x HAR2
          HLED2 HkLam (HL2in _ (Hrest0 _ (HDiFi _ Hb)))); [| exact Hx | lia].
        intros E. apply Hk0n. right. rewrite <- E. exact (Hrest0 _ (HDiFi _ Hb)).
      - apply (pjm_agree_sub SEGS _ _ _ _ HAGDi). intros x (b & Hb & Hx). cbv beta. exists b.
        split; [exact (HDiFi _ Hb) | exact Hx].
      - intros a kk Hb. exact (HL2in _ (Hrest0 _ (HDiFi _ Hb))). }
    assert (HPF : Permutation Do ((k', 56 * cap2R (js_cap en)) :: (y', 8 * cap2R (js_cap en)) :: DiF))
      by (unfold Do; cbn [app]; apply perm_skip; apply perm_skip; exact HPDi).
    assert (HNDF : List.NoDup ((k', 56 * cap2R (js_cap en)) :: (y', 8 * cap2R (js_cap en)) :: DiF))
      by (apply (Permutation_NoDup HPF); apply pjm_nd; exact HDoNd).
    assert (HOI3 : PRH_PjOrder.pf_oitemsR SEGS (rdW W2 mem2) (prh_lin Lam')
        (PRH_PjOrder.pj_foR SEGS (rdW W2 mem2) (prh_lin Lam') d) true k' y' (Z.to_nat (js_n en)) DiF FiF)
      by (rewrite En0, Nat2Z.id; exact HOI2).
    pose proof HHDR2 as Hh2. rewrite Es0 in Hh2.
    pose proof HSL2 as (_ & _ & _ & HSLp). destruct (HSLp ltac:(lia)) as (Hkl & Hyl).
    assert (HFO2 := pjsf_obj_intro SEGS (rdW W2 mem2) (prh_lin Lam') d (js_o en) (js_num en) k' y' (js_n en)
      (cap2R (js_cap en)) DiF FiF Hh2 ltac:(lia) ltac:(lia) Hkl (Hyl eq_refl) ltac:(pjsm_nd HNDF)
      ltac:(intros b x Hb; apply HApo; exact (Permutation_in _ (Permutation_sym HPF) Hb)) HOI3).
    exists (FiF ++ [(k', 56 * cap2R (js_cap en)); (y', 8 * cap2R (js_cap en))]).
    split; [exact (pjm_foR_perm SEGS _ _ _ _ _ _ _ HFO2 (Permutation_sym HPF))|].
    rewrite map_app, HMFi. f_equal. rewrite ECAP2. exact (pjsf_arrz_of _ _ _ (pjm_ncap_S_pos _)). }
  split; [exact HINV3|]. split; [exact HROOM2|].
  exists Lam', (Z.max (js_peak en) (Z.max (Ledger.lsum (js_Lam en) + 56 * (cap2R (js_cap en) - js_cap en))
    (Ledger.lsum Lam'))), 2%nat, [], Do, Lr, k', y', (cap2R (js_cap en)),
    (kids_blkR (js_kids en) (js_cap en) ++ keys_blkR 6 (js_keys en) (js_cap en)),
    [(k', 56 * cap2R (js_cap en)); (y', 8 * cap2R (js_cap en))], Di.
  split; [replace (js_cnt en + Z.of_nat 2) with (js_cnt en + 2) by lia; exact HLED2|].
  (* the outcome cell: both reallocs granted outside the failure window, g_ran_out kept *)
  split; [apply pjm_oks_granted; [intros i _; destruct i as [|[|i]]; reflexivity | lia]|].
  split; [intros i _; destruct i; reflexivity|].
  split; [lia|].
  split; [exact HpLam|].
  split.
  { assert (E0 : Permutation Lam0 (Di ++ js_Dw en ++ Lr)).
    { apply (Permutation_app_inv_l (kids_blkR (js_kids en) (js_cap en) ++ keys_blkR 6 (js_keys en) (js_cap en))).
      apply (Permutation_trans (Permutation_sym HL1)). apply (Permutation_trans HpLam). rewrite ED'.
      rewrite <- !app_assoc. apply Permutation_refl. }
    apply (Permutation_trans HL2). cbn [app]. apply (Permutation_trans (perm_swap _ _ _)).
    unfold Do. cbn [app]. apply perm_skip. apply perm_skip. exact E0. }
  split.
  { destruct (pjm_blocks_other B ly S Hp W mem _ _ _ _ _ _ _ HLED) as (other & Ho). exists other.
    split; [rewrite <- Eab; exact Ho|].
    exact (pjm_blocks_swap B ly S ly2 S2 (js_Lam en) Lam' Lam0 _ _ bl other HL1 HL2 Hb1 Hb2 Ho). }
  split; [exact HNI|].
  split; [rewrite ED'; apply Permutation_refl|].
  split; [apply Permutation_refl|].
  split; [intros a kk [E|[E|[]]]; injection E as <- <-; rewrite <- Eab; [exact Hfk | exact Hfy]|].
  split; [right; split; [exact Enc|]; repeat split|].
  split; [lia|].
  split; [lia|].
  split.
  { (* grow's position implication at js_i: both reallocs' events, the position at js_i + 2 *)
    assert (Hh : exists h, PresetRoomPos.iface_room_pos ReaderRes.jr_strtod (js_x en) (js_os en)
        (js_i en + length (prhPg_evs true (js_n en) (js_cap en) [true; true]))%nat (js_H0 en) h S2)
      by exact (HPOS2 _ _ _ _ _ _ HPOSS HRUN2).
    assert (L2 : length (prhPg_evs true (js_n en) (js_cap en) [true; true]) = 2%nat).
    { unfold prhPg_evs. rewrite (proj2 (Z.ltb_ge (js_n en) (js_cap en))) by lia. reflexivity. }
    rewrite L2 in Hh. exact Hh. }
  split.
  { unfold PRH_Charge.prh_held in HBB. change (6 =? 6) with true in HBB. rewrite Gh, Gc in HBB.
    rewrite (blocks_bytes_bsum B ly S), Eab, <- (blocks_bytes_bsum B (js_ly en) (js_S en)) in HBB.
    unfold LIVE_pj_set, LIVE_grow in HLIVE. rewrite (proj2 (Z.eqb_eq _ _) Enc) in HLIVE.
    change (6 =? 6) with true in HLIVE. cbv iota in HLIVE. unfold js_klen in *. lia. }
  split; [exact HNODE2|].
  split; [exact HHDR2|].
  split; [exact HSL2|].
  split; [exact H9'|].
  split; [exact HNODEW2|]. split; [exact HDATA2|].
  (* the block lists in order: js_D = (old kids ++ old keys) ++ Di (the cut's ED'), Do = the two new blocks ++ Di *)
  split; [exact ED'|]. split; [reflexivity|].
  (* the capacities are the model's; the object's ordered free list; val's entry agreement, kept across grow *)
  split; [exact ECAP|]. split; [exact ECAP2|]. split; [exact HORDD|].
  exact (pjs_agree_trans _ _ _ _ HAGRW0 HAGW).
Qed.

End ms.
