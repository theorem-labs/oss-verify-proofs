(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: segment RET of pj_set's image-A' walk (fuzz_preset asan, A 0x8685c; the cuts of
   lib/A/Prog/pj_setA_defs.v): from the cut pjsA_RET at the `beqz a0` (+0x3c) after pj_get, to the cut pjsA_MISS (the
   key is absent) or to the join pjsA_TAIL (the key is present), whose segment statements are premises.
     +0x3c  beqz a0, +52       a0 = 0 (pj_get's first result arm): taken, to PJSA_MISS (+0x70)
     +0x40  mv s3, a0          a0 = kids + 56 i, the member slot
     +0x44  jal pj_free        tpj_free_specX CTX0 dd (the post-implication form, no position at entry; its
                               prh_head_wide premise from pjsA_pre's cf_head = HEAD, pj_setA_defs.v pjsA_head_wide; it
                               concludes at the re-hiding relation, YA0nH.SRr' at RZ_cf over fpostWmR at WR) by
                               YCbqGcallW.v aj_call_xWR at WR (the RET journal lifted by ajournal_xwR_mono) at the
                               callee window e1 = 48 + d (v = the slot, D = Du: member i's blocks of the ENTRY
                               decomposition, F = Du's order list Fv)
     +0x48  li a2, 56
     +0x4c  mv a0, s3          then PJSA_TAIL (+0x50)
   pj_free's text is CITED, never unfolded, and its post is read BY NAME (its top-level conjunctions split and picked
   by type). Its order list Fv is lib/A/PjFoMember.v pj_foR_member at nn := dd: from pjsA_pre's
   ordered premise at S dd (the object's order list, requests fo (JObj ms) in order), framed to the RET memory by
   pjsA_RET's agreement on the object's footprint (PRH_PjOrder.pj_foR_frame), with kids = pj_hdrR's fifth conjunct at
   the RET memory, lblk functional (PRH_Base.prh_lin_functional) and no block at 0 (PRH_Base.prh_ledger_nonzero);
   its requests are fo vi, in order. The model's event of this arm is HBulk (fo vi) (pjrA_set_evs_hit: prhPj_mfind
   finds pj_get's first match); the run premise prhPj_free_evs Fv is PRH_FnPj.prhPj_free_evs_supply at Lb := fo vi;
   pj_free's class-24 bound (asked when v <> 0) is lib/Spec/PresetRoomCounts.v counts_of_room_pos_rl at the entry's
   position (S = jsA_S en); its hull budget (v <> 0 -> hull_budget S []) is pjsA_g_hull at the same position (a run of
   at most 4 calls, pjsA_pre's length premise; nothing is asked of the empty list); its fpre's frm_zero is the entry's.
   The steps before the call run plainly (YGcfRhLift.ra_rh_of_SRr), the call is bound at WR (YSRrG.SRr'_bind), the
   frame is kept by pjsA_frame_kept_stmtR at WR, and the two steps after it run plainly again. pjsA_TAIL's last
   clause (the arm's OBLIGATION) is
   discharged here: the contract's post, first arm, with the replaced member's tree and the new object tree built from the entry
   decomposition (pjrA_new_tree), the bytes carried entry -> cut (pjsA_RET's agreement) -> TAIL (pj_free's journal:
   the object's header and the blocks of D minus Du lie off pj_free's footprint) -> the contract's post state (the copy and the
   zeroing write only the slot and val's header); the new object's block sizes (a Permutation) from pjsA_pre's with
   member i's value sizes (a permutation of tblk vi: Fv is a permutation of Du, PRH_PjOrder.pj_foR_fdR, and fo vi of
   tblk vi, PresetReqAtNoMiss.fo_tblk) replaced by val's (pjrA_tblk_swap); THE NEW OBJECT'S ORDERED FREE LIST
   (FREEORD-COPY) from the entry's ordered list cut at member i, with val's ordered list (given at the entry
   memory, carried entry -> RET by pjsA_RET's agreement on val's footprint and RET -> TAIL by pj_free's journal,
   pjrA_tree_agree) moved into the slot (pjrA_new_fo); DEAD-PJSET and prh_granted's clause hold because res = 0 on
   this arm; the position at jsA_i + 1 is pj_free's post implication applied at the entry's position with the run
   premise prhPj_free_evs Fv, or, when Du holds no block (Fv = [], so fo vi = []), that and the model's empty bulk free
   stepped over by prhPj_bulk_nil_pos (pjrA_pos_after_free). The memnorm keep composes RET's with pj_free's fpostWm
   keep. pjsA_MISS takes both of pjsA_RET's agreements.
   proves no function (kind: segment lemma).
   Section premises beyond LAWS / VIS: HULL (pj_setA_defs.v pjsA_g_hull), HW8 (PRH_Base.v prh_head_wide, 8 <= cf_head;
   cf_head = 16 at preset's
   CfParams instance): the ledger at the contract's post state reads every harness block's head word at a - cf_head, which
   the copy into the kids block (member 0) and the zeroing of val (when val sits at its block's base) would
   overwrite for a head shorter than 8 bytes.
   Numerals: 48 / 56 (LENGTH: frame, struct); 6 (the object tag); 4 / 8 / 12 / 16 / 20 (DERIVED: pc offsets from the
   cut); register numbers 0, 1, 2, 3, 4, 8, 10, 12, 18, 19, 20 (WORD). No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YCbqGcall YCbqGcallW FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06 YGcfFsVis.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YSRrG YGcfRehidePost YGcfRhLift.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetReqAt PresetReqAtNoMiss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomCounts PresetHullBudget PresetSecTotal.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnPj PRH_FnAlloc PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PjFoMember.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1ImgA pj_setA_defs pj_setA_glue pj_setA_steps pj_setA_vis pj_setA_ret_lem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import pj_set_trans.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Open Scope Z_scope.
#[local] Existing Instance prh_img_A.

Section x. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation PST := (prh_pst (PI := prh_img_A)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis VIS : pjsA_g_vis B ARx.
(* a harness block's head word lies before its user bytes (see the header) *)
Hypothesis HW8 : @prh_head_wide cp.
(* the hull budget's instance fact (pj_setA_defs.v pjsA_g_hull) *)
Hypothesis HULL : @pjsA_g_hull cp.
#[local] Notation WR := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).
(* a callee post read BY NAME: its top-level conjunctions split, each picked by its type *)
Local Ltac pjrA_conj_split H :=
  lazymatch type of H with
  | _ /\ _ =>
    let H1 := fresh "Ec" in let H2 := fresh "Ec" in destruct H as [H1 H2]; pjrA_conj_split H1; pjrA_conj_split H2
  | _ => idtac
  end.

Theorem pjsA_seg_ret_holds : forall CTX0 dd,
  pjsA_texts B ARx CTX0 dd -> pjsA_frame_kept_stmtR B ARx WR dd -> pjsA_seg_tail B ARx CTX0 dd ->
  pjsA_seg_miss B ARx CTX0 dd -> pjsA_seg_ret B ARx CTX0 dd.
Proof.
intros CTX0 dd TXT KEEP HTAIL HMISS en ly S Hp W regs mem md k HPRE HCUT.
destruct TXT as (_ & PJFREE & _ & _ & _ & _).
pose proof HPRE as HPRE0.
pose proof (@pa_segs_low _ A_prog_listing PA) as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@cf_head_nonneg cp) as Hh0. pose proof HW8 as Hh8. unfold prh_head_wide in Hh8.
unfold pjsA_pre in HPRE. cbv zeta in HPRE.
destruct HPRE as (HFPRE & HUNIV & HROOM0 & HPOS0 & HLOS & _ & _ & _ & _ & HFWIN & HNODE0 & HHDR0 & Hcap54 & HSLOTO0 &
  HNODEW0 & HSLOTW0 & HWC & HDWD & HWFOOT & HAPW & HDEPO & HDEPV & _ & _ & _ & HLED0 & _ & _ & _ & _ & HTBLK0 &
  HFORD & HHEAD & HRUN0).
pose proof HFPRE as ((HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & Hqt0) & HROD0 & HSTKHI0).
(* the kit-FRM0-ENTRY: the entry's rounding mode, which pj_free's fpre asks of the same fx *)
assert (HFRM : YK0o.frm_zero (@YK11.fp_csr fx)) by (destruct HFPRE as (_ & _ & _ & _ & H); exact H).
pose proof Hstk0 as (Hal0 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop0 & Htop20).
pose proof HFWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
destruct HCUT as (HINV & HDC & HLED & Eab & EHp & ES & H9 & HNODE & HHDR & HNODEW & HAGR & HAGRW & z & Hz & Hres).
pose proof HINV as (HJ & HWIN & Hsp & Hra & Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & H8 & H18 & H20 & HKEPT & HPRES & HROD & HKN).
pose proof (ajx_ar HJ) as HARc. pose proof (ajx_ly HJ) as Hly.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
cbn [prhPj_get_res] in Hres.
unfold pjsA_cfg.
apply YGcfRhLift.ra_rh_of_SRr.
pjsA_fd PJSA_RET Hl1 Hd1.
destruct Hres as [(Hall & ->) | (i & vi & kidsg & Dig & Hnth & Hfirst & Hrdk & Ez & _ & _)].
{ (* ======== the key is absent: +0x3c beqz a0 is taken, to PJSA_MISS ======== *)
  eapply (pjrA_step_beq W regs mem md _ PJSA_RET _ _ _ _ (Z_to_bv 64 (BASE + PJSA_MISS)) true Hl1 Hd1).
  { lazymatch goal with |- c_eq (getr _ ?r1) (getr _ ?r2) = _ =>
      replace r1 with (10%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity);
      replace r2 with (0%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity) end.
    rewrite Hz, getr_zero. vm_compute. reflexivity. }
  { apply bv_eq. vm_compute. reflexivity. }
  intros X1.
  apply SRr_ret. cbv beta.
  apply (HMISS en ly S Hp W regs mem _ k HPRE0).
  split; [split; [exact (ajournal_x_materialize (SK := SK) SEGS B PST ARx LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    X1 HJ) | exact (proj2 HINV)]|].
  split; [exact HDC|]. split; [exact HLED|]. split; [exact Eab|]. split; [exact EHp|]. split; [exact ES|].
  split; [exact H9|].
  split.
  { intros Hin. apply in_map_iff in Hin as ([nm u] & Enm & Hin). cbn [fst] in Enm. exact (Hall nm u Hin Enm). }
  split; [exact HNODE|]. split; [exact HHDR|]. split; [exact HNODEW|]. split; [exact HAGR | exact HAGRW]. }
(* ======== the key is present: member i, at z = kids + 56 i ======== *)
destruct HDC as (HROOM & HPLO & HSLOTW & HCS & HKA).
pose proof HPLO as (Ho4096 & HoAt & HoRw & HoAmr & HoOwn & HoRa).
pose proof HSLOTW as (Hw4096 & HwAt & HwRw & HwAmr & HwOwn & HwRa & HwHull).
(* ---- the ENTRY decomposition of the object ---- *)
pose proof HNODE0 as HN0. cbn [pj_nodeR] in HN0.
destruct HN0 as (HndD & HapD & num0 & str0 & kids0 & keys0 & n0 & cap0 & HH0 & Es0 & En0 & Hnc0 & Hcap0 & Di0 & ED & HM0).
pose proof HH0 as (_ & _ & _ & _ & Hk0' & _ & _ & _).
pose proof HHDR0 as (_ & _ & _ & _ & Hk0 & _ & _ & _).
pose proof (pjrA_u64_fun _ _ _ _ _ Hk0' Hk0) as Ekids0.
pose proof HHDR as (_ & _ & _ & _ & HkR & _ & _ & _).
pose proof (pjrA_u64_fun _ _ _ _ _ Hrdk HkR) as Ekidsg.
subst kids0 kidsg str0 n0.
pose proof (pj_nth_lenR (jsA_ms en) i (jsA_kname en, vi) Hnth) as Hi.
assert (Hcp : 0 < cap0) by lia.
destruct Hcap0 as [(Hc0 & _) | (_ & HkL & HLy)]; [lia|].
rewrite (proj2 (Z.eqb_neq cap0 0)) in ED by lia. cbn [app] in ED.
destruct (pjst_mems_nth SEGS _ _ _ (jsA_ms en) (jsA_kids en) keys0 Di0 i (jsA_kname en) vi HM0 Hnth)
  as (D1 & x & kx & Du & D2 & EDi & HM1 & Hkx & Hcs & HNU & HM2).
subst Di0.
(* ---- the model's one event of this arm: the bulk free of fo vi ---- *)
pose proof (pjrA_set_evs_hit (jsA_ms en) i (jsA_kname en) vi (jsA_n en) (jsA_cap en) Hnth Hfirst) as Eevs.
assert (HRUN1 : prh_run_at ReaderRes.jr_strtod (jsA_x en) (jsA_os en) (jsA_i en) [PresetReqAt.HBulk (PresetReqAt.fo vi)])
  by (rewrite <- Eevs; exact HRUN0).
set (Dr := (jsA_kids en, 56 * cap0) :: (keys0, 8 * cap0) :: D1 ++ (x, kx) :: D2).
assert (PD : Permutation (jsA_D en) (Du ++ Dr)).
{ rewrite ED. unfold Dr.
  replace ((jsA_kids en, 56 * cap0) :: (keys0, 8 * cap0) :: D1 ++ (x, kx) :: Du ++ D2) with
    (((jsA_kids en, 56 * cap0) :: (keys0, 8 * cap0) :: D1 ++ [(x, kx)]) ++ Du ++ D2)
    by (cbn [app]; rewrite <- app_assoc; reflexivity).
  replace ((jsA_kids en, 56 * cap0) :: (keys0, 8 * cap0) :: D1 ++ (x, kx) :: D2) with
    (((jsA_kids en, 56 * cap0) :: (keys0, 8 * cap0) :: D1 ++ [(x, kx)]) ++ D2)
    by (cbn [app]; rewrite <- app_assoc; reflexivity).
  apply pjrA_perm_mid. }
assert (HndDuDr : NoDup (Du ++ Dr)) by exact (pjrA_nodup_perm _ _ HndD PD).
assert (HDuD : forall b, In b Du -> In b (jsA_D en)).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym PD)). apply in_or_app. left. exact Hb. }
assert (HDrD : forall b, In b Dr -> In b (jsA_D en)).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym PD)). apply in_or_app. right. exact Hb. }
assert (HDrNotDu : forall b, In b Dr -> ~ In b Du).
{ intros b Hb Hu. exact (pjrA_nodup_app_disj Du Dr b HndDuDr Hu Hb). }
assert (HDL : forall a kk, In (a, kk) (jsA_D en) -> In (a, kk) (jsA_Lam en))
  by (intros a kk Hb; exact (pjst_node_lblk SEGS _ _ _ _ _ HNODE0 a kk Hb)).
assert (HDwL : forall a kk, In (a, kk) (jsA_Dw en) -> In (a, kk) (jsA_Lam en))
  by (intros a kk Hb; exact (pjst_node_lblk SEGS _ _ _ _ _ HNODEW0 a kk Hb)).
pose proof (pjrA_node_nodup SEGS _ _ _ _ _ HNODEW0) as (HndDw & HapDw).
assert (HkidsD : In (jsA_kids en, 56 * cap0) (jsA_D en)) by (rewrite ED; left; reflexivity).
assert (HkeysD : In (keys0, 8 * cap0) (jsA_D en)) by (rewrite ED; right; left; reflexivity).
assert (HkNotIn : ~ In (jsA_kids en, 56 * cap0) ((keys0, 8 * cap0) :: D1 ++ (x, kx) :: Du ++ D2)).
{ pose proof HndD as HndD'. rewrite ED in HndD'. apply NoDup_ListNoDup in HndD'.
  apply NoDup_cons_iff in HndD' as [HkN _]. exact HkN. }
assert (HinTail : forall b, In b (D1 ++ (x, kx) :: D2) -> In b ((keys0, 8 * cap0) :: D1 ++ (x, kx) :: Du ++ D2)).
{ intros b Hb. right. apply in_app_or in Hb as [Hb | [<- | Hb]]; apply in_or_app;
    [left; exact Hb | right; left; reflexivity | right; right; apply in_or_app; right; exact Hb]. }
(* the kids block, a harness block of the ledger *)
destruct (pjrA_hb B ARx LAWS HW8 ly S Hp W mem md (jsA_Lam en) (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en)
  (jsA_kids en) (56 * cap0) HARc HLED HkL) as (_ & HkAB & Hkal & Hk4096 & Hkceil & HkRq & HkApp & HkPo).
assert (Hzr : jsA_kids en <= z /\ z + 56 <= jsA_kids en + 56 * cap0) by (rewrite Ez; lia).
assert (Hz8 : z mod 8 = 0) by (rewrite Ez; lia).
assert (Hsp0c : YM05.alloc_ceiling <= spZ (jsA_regs en)) by lia.
assert (HSP0 : jsA_sp0 en = spZ (jsA_regs en)) by reflexivity.
assert (HSP01 : jsA_sp1 en = jsA_sp0 en - 48) by reflexivity.
assert (HSTKF : 0 <= STK_pj_free dd) by (unfold STK_pj_free, zmaxl; cbn [fold_right];
  pose proof (pi_frame_nonneg F_pj_free); lia).
assert (HSTKB : STK_pj_free dd + 48 <= STK_pj_set dd).
{ unfold STK_pj_set, zmaxl. cbn [fold_right].
  replace (pi_frame F_pj_set) with 48 by (vm_compute; reflexivity). lia. }
assert (HSTKE : ESTACK + 48 <= STK_pj_set dd).
{ unfold STK_pj_set, zmaxl. cbn [fold_right].
  replace (pi_frame F_pj_set) with 48 by (vm_compute; reflexivity).
  assert (HE : STK_RT_ECALL = ESTACK) by reflexivity. lia. }
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HSPLO : YM05.alloc_ceiling <= jsA_sp1 en - ESTACK) by (unfold jsA_sp1, jsA_sp0, PJSA_FR; lia).
assert (HTOPW : jsA_sp0 en + jsA_d en <= 2 ^ 47) by (unfold jsA_sp0; lia).
(* member i's node at the cut memory, from the entry by the cut's agreement *)
assert (HNUc : pj_nodeR SEGS (rdW W mem) (prh_lin (jsA_Lam en)) (jsA_kids en + 56 * Z.of_nat i) vi Du).
{ apply (pj_nodeR_frame SEGS vi _ _ _ _ _ HNU).
  apply (pjrA_agree_sub SEGS _ _ _ _ HAGR). intros y [Hy | (b & Hb & Hy)].
  - right. exists (jsA_kids en, 56 * cap0). split; [exact HkidsD | unfold pj_holdsR; cbn [fst snd]; lia].
  - right. exists b. split; [exact (HDuD b Hb) | exact Hy]. }
(* the ledger's block predicate is functional and has no block at 0 (the entry's ledger; the RET ledger's list is
   the same) *)
assert (HFN0 : forall a kk kk', prh_lin (jsA_Lam en) a kk -> prh_lin (jsA_Lam en) a kk' -> kk = kk').
{ intros a kk kk' Hla Hlb. eapply (prh_lin_functional (PA := PA)); [exact HLED0 | exact Hla | exact Hlb]. }
assert (HNZ0 : forall a kk, prh_lin (jsA_Lam en) a kk -> a <> 0).
{ intros a kk Hla. eapply (prh_ledger_nonzero (PA := PA)); [exact LAWS | exact HAR0 | exact HLED0 | exact Hla]. }
(* pj_free's order list of member i at the RET (call) memory: pj_foR_member at nn := dd, from the
   entry's ordered list at S dd (pjsA_pre's ordered premise) framed to the RET memory by RET's agreement *)
destruct (HFORD HHEAD (Datatypes.S dd) HDEPO) as (F0 & HF0 & HmF0).
rewrite HHEAD in HmF0.
pose proof (pj_foR_frame SEGS _ _ _ _ (prh_lin (jsA_Lam en)) _ _ _ HF0 HDL HAGR) as HF0c.
destruct (PjFoMember.pj_foR_member SEGS (rdW W mem) (prh_lin (jsA_Lam en)) (jsA_o en) (jsA_ms en) (jsA_D en) F0 dd i
  (jsA_kname en) vi Du (jsA_kids en) HNODE HF0c HmF0 Hnth HNUc HkR HFN0 HNZ0) as (Fv & HFO & HmFv).
rewrite <- Ez in HFO.
(* member i's value sizes: Fv is a permutation of Du, and fo vi of tblk vi *)
assert (HTU : Permutation (map (fun b : Z * Z => snd b + cf_head) Du) (PresetReqAtNoMiss.tblk vi)).
{ rewrite HHEAD. eapply Permutation_trans.
  - apply Permutation_map. apply Permutation_sym. exact (proj2 (pj_foR_fdR SEGS _ _ _ _ _ _ HFO)).
  - rewrite HmFv. exact (PresetReqAtNoMiss.fo_tblk vi). }
(* the run premise of pj_free's position transfer: its order list's one bulk free, the model's event *)
assert (HRF : prh_run_at ReaderRes.jr_strtod (jsA_x en) (jsA_os en) (jsA_i en) (prhPj_free_evs Fv)).
{ eapply prhPj_free_evs_supply; [rewrite HHEAD; exact HmFv | exact HRUN1]. }
(* the model-run position at the call is the entry's (S = jsA_S en), and so is the class-24 bound *)
rewrite <- ES in HPOS0.
pose proof (proj2 (PresetRoomCounts.counts_of_room_pos_rl _ _ _ _ _ _ _ HPOS0)) as HC24.
(* pj_free's hull budget at the call: the empty list's, at the entry position (pj_setA_glue.v pjsA_hull_nil) *)
assert (HHB0 : PresetHullBudget.hull_budget S []) by exact (pjsA_hull_nil HULL _ _ _ _ _ _ S HLOS HPOS0).
(* ======== +0x3c  beqz a0: falls through (a0 = z <> 0) ======== *)
eapply (pjrA_step_beq W regs mem md _ PJSA_RET _ _ _ _ (Z_to_bv 64 (BASE + (PJSA_RET + 4))) false Hl1 Hd1).
{ lazymatch goal with |- c_eq (getr _ ?r1) (getr _ ?r2) = _ =>
    replace r1 with (10%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity);
    replace r2 with (0%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity) end.
  rewrite Hz, getr_zero. apply c_eq_0_false. unfold w64. rewrite unsigned_lit_small by lia. lia. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X1.
pose proof (ajournal_x_materialize (SK := SK) SEGS B PST ARx LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1 HJ) as HJ1.
(* ======== +0x40  mv s3, a0 ======== *)
pjsA_fd (PJSA_RET + 4) Hl2 Hd2.
eapply (pjsA_step_addi W regs mem _ _ (PJSA_RET + 4) _ _ _ _ (19%bv : bv 5) (getr regs (10%bv : bv 5)) Hl2 Hd2).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ lazymatch goal with |- v_addi (getr _ ?rs) (bv_signed ?im) = _ =>
    replace rs with (10%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity);
    replace (bv_signed im) with 0 by (vm_compute; reflexivity) end.
  unfold v_addi. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. }
intros X2.
pose proof (ajournal_x_materialize (SK := SK) SEGS B PST ARx LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X2 HJ1) as HJ2.
replace (v_addi (Z_to_bv 64 (BASE + (PJSA_RET + 4))) 4) with (Z_to_bv 64 (BASE + (PJSA_RET + 8)))
  by (apply bv_eq; vm_compute; reflexivity).
(* ======== +0x44  jal pj_free ======== *)
pjsA_fd (PJSA_RET + 8) Hl3 Hd3.
eapply (pjsA_step_jal W _ mem _ _ (PJSA_RET + 8) _ _ _ (1%bv : bv 5) (Z_to_bv 64 (BASE + (PJSA_RET + 12)))
  (Z_to_bv 64 (@pa_sigma _ A_prog_listing PA AS_pj_free)) Hl3 Hd3).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X3.
pose proof (ajournal_x_materialize (SK := SK) SEGS B PST ARx LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X3 HJ2) as HJ3.
pose proof (ajx_ar HJ3) as HARcc.
lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?r _ _ _) ?m) _ =>
  remember r as regsc eqn:Eregsc; set (mdc := m) in * end.
assert (HSPC : spZ regsc = jsA_sp1 en).
{ unfold YG0d.spZ at 1. rewrite Eregsc, !getr_other by pjsA_regne. exact Hsp. }
assert (HS0LOW : s0Z regsc < YM05.alloc_ceiling).
{ unfold YG0d.s0Z. rewrite Eregsc, !getr_other by pjsA_regne. rewrite H8. unfold w64.
  rewrite unsigned_lit_small by lia. lia. }
assert (HGP : getr regsc 3 = w64 (as_gp B)).
{ rewrite Eregsc, !getr_other by pjsA_regne. rewrite (HKEPT 3%bv) by (unfold PJSA_KEPT; left; reflexivity). exact Hgp0. }
assert (HTP : getr regsc 4 = w64 (as_tp B)).
{ rewrite Eregsc, !getr_other by pjsA_regne. rewrite (HKEPT 4%bv) by (unfold PJSA_KEPT; right; left; reflexivity).
  exact Htp0. }
assert (HRA1 : getr regsc 1 = Z_to_bv 64 (BASE + (PJSA_RET + 12)))
  by (rewrite Eregsc; apply getr_same; pjsA_regne).
assert (HRAW : YK0s.ret_ok (Z_to_bv 64 (BASE + (PJSA_RET + 12)))).
{ apply (YC1fP.ret_ok_codeptr_v (PI := PA));
  [split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity | vm_compute; reflexivity]. }
assert (HRA4 : 4096 <= bv_unsigned (Z_to_bv 64 (BASE + (PJSA_RET + 12))))
  by (apply Z.leb_le; vm_compute; reflexivity).
assert (HSPO : spZ regsc = jsA_sp0 en + jsA_d en + (- 48 - jsA_d en))
  by (rewrite HSPC; unfold jsA_sp1, PJSA_FR; lia).
assert (Ea0c : getr regsc 10 = w64 z) by (rewrite Eregsc, !getr_other by pjsA_regne; exact Hz).
assert (E19c : getr regsc 19 = w64 z).
{ rewrite Eregsc, getr_other by pjsA_regne. rewrite getr_same by pjsA_regne. exact Hz. }
assert (Hne0 : (z =? 0) = false) by (apply Z.eqb_neq; lia).
set (FP1 := if z =? 0 then [] else (z, z + 56) :: ablocks_fp (prhPj_hbl Du)).
assert (EFP1 : FP1 = (z, z + 56) :: ablocks_fp (prhPj_hbl Du)) by (unfold FP1; rewrite Hne0; reflexivity).
(* the footprint of pj_free: the slot and the allocator blocks of Du, all inside pj_set's own footprint *)
assert (HFPD : forall a' k' y, In (a', k') (jsA_D en) -> a' - cf_head <= y < a' - cf_head + req_size (k' + cf_head) ->
  inFP (pjsA_FP en) y).
{ intros a' k' y Hin Hy. unfold pjsA_FP. apply inFP_cons. right. apply inFP_cons. right.
  apply (pjrA_hbl_inFP (jsA_D en ++ jsA_Dw en) a' k' y); [apply in_or_app; left; exact Hin | exact Hy]. }
assert (HinFP1 : forall y, inFP FP1 y ->
  (z <= y < z + 56) \/ exists a' k', In (a', k') Du /\ a' - cf_head <= y < a' + k').
{ intros y Hy. rewrite EFP1 in Hy. apply inFP_cons in Hy. destruct Hy as [Hy | Hy]; [left; exact Hy | right].
  destruct (pjrA_inFP_hbl Du y Hy) as (a' & k' & Hin & Hr). exists a', k'. split; [exact Hin|].
  destruct (pjrA_hb B ARx LAWS HW8 ly S Hp W mem md (jsA_Lam en) (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en)
    a' k' HARc HLED (HDL _ _ (HDuD _ Hin))) as (_ & _ & _ & _ & _ & Rq & _). rewrite Rq in Hr. lia. }
assert (HFP1lo : forall y, inFP FP1 y -> 4096 <= y < YM05.alloc_ceiling /\ (y < kLowShadowBeg \/ kHighMemBeg <= y)).
{ intros y Hy. destruct (HinFP1 y Hy) as [Hy' | (a' & k' & Hin & Hr)].
  - unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HkApp |- *. lia.
  - destruct (pjrA_hb B ARx LAWS HW8 ly S Hp W mem md (jsA_Lam en) (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en)
      a' k' HARc HLED (HDL _ _ (HDuD _ Hin))) as (_ & _ & _ & H4 & Hc & _ & Happ & _).
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ |- *. lia. }
(* ======== the call: pj_free's text at the callee window e1 = 48 + d, bound at WR ======== *)
pose proof (ajournal_xwR_mono (SK := SK) SEGS B PST ARx (@wle SEGS) WR (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf)
  _ _ _ _ _ (jsA_Hp en) _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HJ3R.
apply SRr_ret. cbv beta.
eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ eapply (aj_call_xWR (fx := fx) (SK := SK) SEGS B PST ARx LAWS Hsegs WR
    (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf) W regsc mem
    (@pa_sigma _ A_prog_listing PA AS_pj_free)
    (STK_pj_set dd + jsA_d en) (jsA_sp0 en + jsA_d en) (pjsA_FP en)
    (jsA_ly en) (jsA_S en) (jsA_Hp en) (jsA_W en) (jsA_mem en) (jsA_md en) [] ly S Hp mdc k
    (STK_pj_free dd) (48 + jsA_d en) FP1 (- 48 - jsA_d en) (Z_to_bv 64 (BASE + (PJSA_RET + 12))) []
    _ HJ3R HSPO ltac:(lia) ltac:(lia) HSTKF ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    HGP HTP HRA1 HRAW HRA4 (achain_low _ _ _ _ HS0LOW)).
  - (* the callee: tpj_free_specX CTX0 dd (post-implication: no position at entry) at d = 48 + d, v = the
       slot, D = Du, F = Fv, Du's order list *)
    intros HPRE1 HWIN1. unfold fpostW_xR.
    eapply (PJFREE (jsA_most en) (jsA_own en)
      ly S Hp W regsc mem _ [] (48 + jsA_d en) z Du Fv (jsA_Lam en) (jsA_peak en)
      (jsA_cnt en) (jsA_fail en) (jsA_ran en)).
    + split; [exact HPRE1|]. split; [exact HROD|].
      split; [rewrite HSPC, Eshi; unfold jsA_sp1, jsA_sp0, PJSA_FR; lia|].
      split; [|exact HFRM].
      (* fpre's return address below the ceiling: the jal's own return pc, a literal of the listing *)
      unfold YG0d.raZ. rewrite HRA1. pose proof (@YM05.alloc_ceiling_value rc) as [[ACm _] _].
      assert (EB : bv_unsigned (Z_to_bv 64 (BASE + (PJSA_RET + 12))) < 2 ^ 40)
        by (apply Z.ltb_lt; vm_compute; reflexivity).
      lia.
    + exact HUNIV.
    + exact HROOM.
    + intros _. exact HC24.
    + intros _. exact HHB0.
    + exact Ea0c.
    + exact HWIN1.
    + right. split; [lia|]. split; [lia|].
      split; [exact HFO|].
      split; [lia|].
      split; [left; exists (jsA_kids en), (56 * cap0); split; [exact HkL | lia]|].
      split; [split; [exact Hz8 | intros y Hy; apply (apresent_writable SEGS); exact (proj1 (HkPo y ltac:(lia)))]|].
      split; [apply amem_range_high; [lia | unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HkApp; lia | lia]|].
      split; [intros y Hy; split; [exact (proj2 (HkPo y ltac:(lia))) |
              rewrite HSPC; unfold jsA_sp1, jsA_sp0, PJSA_FR; lia]|].
      destruct (pjsA_vis_lam B ARx LAWS ly S Hp W mem md (jsA_Lam en) (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en)
        (jsA_kids en) (56 * cap0) z 56 HARc HLED HkL ltac:(lia) ltac:(lia) ltac:(lia)) as [Hra' Hhull].
      split; [exact Hra' | exact Hhull].
    + exact (pjsA_head_wide HHEAD).
    + exact HLED.
  - (* the footprint: the slot and Du's blocks are pj_set's own *)
    intros a Ha. left. rewrite EFP1 in Ha. apply inFP_cons in Ha. destruct Ha as [Ha | Ha].
    + exact (HFPD (jsA_kids en) (56 * cap0) a HkidsD ltac:(rewrite HkRq; lia)).
    + destruct (pjrA_inFP_hbl Du a Ha) as (a' & k' & Hin & Hr). exact (HFPD a' k' a (HDuD _ Hin) Hr). }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2' & HJc & HX & HP2 & HK).
unfold fQmn in HK. cbv beta in HK.
(* pj_free's post, by name *)
pjrA_conj_split HK.
assert (HROOM2 : room_live_cf S2) by assumption.
assert (HPOS2 : forall sm x0 os i0 H0 hist, PresetRoomPos.iface_room_pos sm x0 os i0 H0 hist S ->
  PRH_Base.prh_run_at sm x0 os i0 (prhPj_free_evs Fv) ->
  exists hist', PresetRoomPos.iface_room_pos sm x0 os (i0 + length (prhPj_free_evs Fv))%nat H0 hist' S2)
  by assumption.
assert (HMN2 : YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem2) by assumption.
lazymatch goal with H : exists Lam', Permutation (jsA_Lam en) (Du ++ Lam') /\ _ |- _ => destruct H as (Lam3 & HQ3) end.
pjrA_conj_split HQ3.
assert (HpF : Permutation (jsA_Lam en) (Du ++ Lam3)) by assumption.
assert (HabF : Permutation (ablocks B ly S) (prhPj_hbl Du ++ ablocks B ly2 S2)) by assumption.
assert (HLED3 : prh_ledger (PA := PA) B ly2 S2 Hp2 W2 mem2 Lam3 (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en)
  (jsA_most en) (jsA_own en)) by assumption.
(* the model-run position after pj_free: its post's position implication applied at the entry's position (S is the
   entry's) with the run premise HRF of its own list, then this arm's one event (the empty bulk free stepped over
   when member i holds no block: Fv = [] gives fo vi = map hb [] = []) *)
assert (HPOSR : exists h, PresetRoomPos.iface_room_pos ReaderRes.jr_strtod (jsA_x en) (jsA_os en) (jsA_i en + 1)%nat
  (jsA_H0 en) h S2).
{ apply (pjrA_pos_after_free _ _ _ _ _ vi Fv S2 HRUN1);
    [|exact (HPOS2 ReaderRes.jr_strtod (jsA_x en) (jsA_os en) (jsA_i en) (jsA_H0 en) (jsA_hist en) HPOS0 HRF)].
  intros EF. rewrite EF in HmFv. cbn [map] in HmFv. symmetry. exact HmFv. }
replace (jsA_sp0 en + jsA_d en + (- 48 - jsA_d en) + (48 + jsA_d en)) with (jsA_sp0 en + jsA_d en) in HJc, HX
  by (unfold jsA_sp1, jsA_sp0, PJSA_FR; lia).
replace (jsA_sp0 en + jsA_d en + (- 48 - jsA_d en)) with (jsA_sp1 en) in HX by (unfold jsA_sp1, PJSA_FR; lia).
pose proof (ajxR_ar HJ2') as HAR2. pose proof (ajxR_ly HJ2') as Hly2. pose proof (ajxR_frs HJ2') as Hfr2. pose proof (ajxR_pres HJ2') as HPRES2.
assert (HPRW : forall a, jsA_sp1 en <= a < jsA_sp0 en + jsA_d en -> apresent (w_H W2) mem2 a).
{ intros a Ha. apply HPRES2. unfold jsA_sp1, jsA_sp0, PJSA_FR in *. lia. }
(* ---- pj_set's frame across the call ---- *)
assert (HSINK : ~ YI16.sink_open_fp FP1).
{ rewrite EFP1. apply sink_closed_cons; [cbn [fst]; lia|]. apply sink_closed_pos. apply Forall_forall.
  intros r Hr. unfold ablocks_fp, prhPj_hbl in Hr. rewrite map_map in Hr.
  apply in_map_iff in Hr as ((a' & k') & <- & Hin). cbn [fst].
  destruct (pjrA_hb B ARx LAWS HW8 ly S Hp W mem md (jsA_Lam en) (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en)
    a' k' HARc HLED (HDL _ _ (HDuD _ Hin))) as (_ & _ & _ & H4 & _). lia. }
assert (HFPFR : forall a, jsA_sp1 en <= a < jsA_sp0 en -> ~ inFP FP1 a).
{ intros a Ha Hin. destruct (HFP1lo a Hin) as ((_ & Hc) & _). lia. }
assert (HFPWIN : forall a, jsA_sp0 en <= a < jsA_sp0 en + jsA_d en -> ~ inFP (pjsA_FP en) a -> ~ inFP FP1 a).
{ intros a Ha _ Hin. destruct (HFP1lo a Hin) as ((_ & Hc) & _). lia. }
destruct (KEEP en ly S Hp W regsc mem mdc k (STK_pj_free dd) FP1 ly2 S2 Hp2 W2 mem2 md2 k1
  ltac:(split; [exact HJ3R|]; split; [exact HWIN|];
        split; [exact HSPC|]; split; [exact Hra|]; split; [exact Hs0|]; split; [exact Hs1|];
        split; [exact Hs2|]; split; [exact Hs3|]; split; [exact Hs4|];
        split; [rewrite Eregsc, !getr_other by pjsA_regne; exact H8|];
        split; [rewrite Eregsc, !getr_other by pjsA_regne; exact H18|];
        split; [rewrite Eregsc, !getr_other by pjsA_regne; exact H20|];
        split; [intros r Hr; rewrite Eregsc, !getr_other by pjsA_kept_ne; exact (HKEPT r Hr)|];
        split; [exact HPRES | split; [exact HROD | exact HKN]])
  HJc HX HFPFR HFPWIN HSTKF Hd0 HSINK) as (KW & KRA & KS0 & KS1 & KS2 & KS3 & KS4 & KPR & KROD).
(* ---- the ledger blocks across pj_free: Lam = Du ++ Lam3 ---- *)
assert (HL3 : forall b, In b (jsA_Lam en) -> ~ In b Du -> In b Lam3).
{ intros b Hb Hnu. apply (Permutation_in _ HpF) in Hb. apply in_app_or in Hb as [Hb|Hb]; [contradiction | exact Hb]. }
assert (HL3L : forall b, In b Lam3 -> In b (jsA_Lam en)).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym HpF)). apply in_or_app. right. exact Hb. }
assert (HDrL3 : forall a' k', In (a', k') Dr -> In (a', k') Lam3).
{ intros a' k' Hb. apply HL3; [exact (HDL _ _ (HDrD _ Hb)) | exact (HDrNotDu _ Hb)]. }
assert (HDwL3 : forall a' k', In (a', k') (jsA_Dw en) -> In (a', k') Lam3).
{ intros a' k' Hb. apply HL3; [exact (HDwL _ _ Hb) | intros Hu; exact (HDWD _ Hb (HDuD _ Hu))]. }
assert (HkL3 : In (jsA_kids en, 56 * cap0) Lam3) by (apply HDrL3; unfold Dr; left; reflexivity).
assert (HyL3 : In (keys0, 8 * cap0) Lam3) by (apply HDrL3; unfold Dr; right; left; reflexivity).
assert (HSLg : forall p, (forall b y, In b Du -> p <= y < p + 56 -> ~ pj_holdsR b y) ->
  forall a' k', In (a', k') (jsA_Lam en) -> a' <= p -> p + 56 <= a' + k' -> In (a', k') Lam3).
{ intros p Hp' a' k' Hin H1 H2. apply HL3; [exact Hin|]. intros Hu.
  apply (Hp' (a', k') p Hu ltac:(lia)). unfold pj_holdsR; cbn [fst snd]; lia. }
assert (HSBg : forall b m, In (b, m) (ablocks B ly S) -> ~ In (b + cf_head, m - cf_head) (jsA_Lam en) ->
  In (b, m) (ablocks B ly2 S2) /\ ~ In (b + cf_head, m - cf_head) Lam3).
{ intros b m Hbm HnL. split.
  - apply (Permutation_in _ HabF) in Hbm. apply in_app_or in Hbm as [Hbm|Hbm]; [|exact Hbm].
    exfalso. exact (HnL (HDL _ _ (HDuD _ (pjrA_hbl_in Du b m Hbm)))).
  - intros H3. exact (HnL (HL3L _ H3)). }
assert (HoDu : forall b y, In b Du -> jsA_o en <= y < jsA_o en + 56 -> ~ pj_holdsR b y).
{ intros b y Hb Hy Hh. exact (HapD b y (HDuD b Hb) Hh Hy). }
assert (HwDu : forall b y, In b Du -> jsA_w en <= y < jsA_w en + 56 -> ~ pj_holdsR b y).
{ intros b y Hb Hy Hh. apply (HWFOOT y Hy). right. exists b. split; [exact (HDuD b Hb) | exact Hh]. }
(* ---- val's and the object's headers, and val's blocks, off pj_free's footprint ---- *)
assert (HwFP1 : forall y, jsA_w en <= y < jsA_w en + 56 -> ~ inFP FP1 y).
{ intros y Hy Hf. destruct (HinFP1 y Hf) as [Hz' | (a' & k' & Hin & Hr)].
  - apply (HWFOOT y Hy). right. exists (jsA_kids en, 56 * cap0).
    split; [exact HkidsD | unfold pj_holdsR; cbn [fst snd]; lia].
  - exact (pjrA_place_off B ARx LAWS HW8 ly S Hp W mem md (jsA_Lam en) (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en)
      (jsA_regs en) (jsA_d en) (jsA_w en) a' k' HARc HLED HwAt Hsp0c (HDL _ _ (HDuD _ Hin))
      (fun y' Hy' Hy'' => HwDu (a', k') y' Hin Hy' Hy'') y Hy Hr). }
assert (HoFP1 : forall y, jsA_o en <= y < jsA_o en + 56 -> ~ inFP FP1 y).
{ intros y Hy Hf. destruct (HinFP1 y Hf) as [Hz' | (a' & k' & Hin & Hr)].
  - apply (HapD (jsA_kids en, 56 * cap0) y HkidsD); [unfold pj_holdsR; cbn [fst snd]; lia | exact Hy].
  - exact (pjrA_place_off B ARx LAWS HW8 ly S Hp W mem md (jsA_Lam en) (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en)
      (jsA_regs en) (jsA_d en) (jsA_o en) a' k' HARc HLED HoAt Hsp0c (HDL _ _ (HDuD _ Hin))
      (fun y' Hy' Hy'' => HoDu (a', k') y' Hin Hy' Hy'') y Hy Hr). }
assert (HDwOff : forall a' k' y, In (a', k') (jsA_Dw en) -> a' <= y < a' + k' ->
  ~ inFP FP1 y /\ ~ (z <= y < z + 56)).
{ intros a' k' y Hin Hy.
  assert (HneK : (a', k') <> (jsA_kids en, 56 * cap0)) by (intros E; rewrite E in Hin; exact (HDWD _ Hin HkidsD)).
  assert (Hzk : ~ (z <= y < z + 56)).
  { intros Hz'. apply (pjrA_lam_sep B ARx LAWS HW8 ly S Hp W mem md (jsA_Lam en) (jsA_peak en) (jsA_cnt en) (jsA_fail en)
      (jsA_ran en) (jsA_most en) (jsA_own en) a' k' (jsA_kids en) (56 * cap0) y HARc HLED (HDwL _ _ Hin) HkL HneK ltac:(lia)). lia. }
  split; [|exact Hzk].
  intros Hf. destruct (HinFP1 y Hf) as [Hz' | (a'' & k'' & Hin'' & Hr)]; [exact (Hzk Hz')|].
  assert (Hne2 : (a', k') <> (a'', k'')) by (intros E; rewrite E in Hin; exact (HDWD _ Hin (HDuD _ Hin''))).
  exact (pjrA_lam_sep B ARx LAWS HW8 ly S Hp W mem md (jsA_Lam en) (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en)
    a' k' a'' k'' y HARc HLED (HDwL _ _ Hin) (HDL _ _ (HDuD _ Hin'')) Hne2 ltac:(lia) Hr). }
(* ---- what pj_free keeps of the object's header and of val's ---- *)
assert (HoK : forall y, jsA_o en <= y < jsA_o en + 56 ->
  aview SEGS (w_H W2) mem2 y = aview SEGS (w_H W) mem y /\ apresent (w_H W2) mem2 y).
{ intros y Hy.
  destruct (pjrA_place_call B ARx LAWS HW8 ly S Hp W mem mdc (jsA_Lam en) (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en)
    (STK_pj_free dd + (48 + jsA_d en)) (jsA_sp0 en + jsA_d en) (jsA_sp1 en) FP1 ly2 S2 Hp2 W2 mem2 md2 k1
    Lam3 (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en) (jsA_regs en) (jsA_d en) (jsA_o en)
    HARcc HJc HLED HLED3 HX ltac:(intros a Ha; apply HPRW; lia) ltac:(lia) ltac:(lia)
    (HSLg (jsA_o en) HoDu) (fun b m Hbm HnL _ _ => proj1 (HSBg b m Hbm HnL)) HoAt y Hy) as [Hb Hp'].
  split; [exact (Hb (HoFP1 y Hy)) | exact Hp']. }
assert (HwK : forall y, jsA_w en <= y < jsA_w en + 56 ->
  aview SEGS (w_H W2) mem2 y = aview SEGS (w_H W) mem y /\ apresent (w_H W2) mem2 y).
{ intros y Hy.
  destruct (pjrA_place_call B ARx LAWS HW8 ly S Hp W mem mdc (jsA_Lam en) (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en)
    (STK_pj_free dd + (48 + jsA_d en)) (jsA_sp0 en + jsA_d en) (jsA_sp1 en) FP1 ly2 S2 Hp2 W2 mem2 md2 k1
    Lam3 (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en) (jsA_regs en) (jsA_d en) (jsA_w en)
    HARcc HJc HLED HLED3 HX ltac:(intros a Ha; apply HPRW; lia) ltac:(lia) ltac:(lia)
    (HSLg (jsA_w en) HwDu) (fun b m Hbm HnL _ _ => proj1 (HSBg b m Hbm HnL)) HwAt y Hy) as [Hb Hp'].
  split; [exact (Hb (HwFP1 y Hy)) | exact Hp']. }
(* ---- val at the TAIL state: its footprint as at the entry (RET's agreement, then pj_free's journal), its tree
   over Lam3 and its slot ---- *)
assert (HAGW2 : pj_agreeR SEGS (rdW W mem) (rdW W2 mem2) (pj_footR (jsA_w en) (jsA_Dw en))).
{ apply (pjrA_tree_agree B ARx LAWS ly S Hp W mem mdc (jsA_Lam en) (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en)
    (STK_pj_free dd + (48 + jsA_d en)) (jsA_sp0 en + jsA_d en) FP1 ly2 S2 Hp2 W2 mem2 md2 k1
    Lam3 (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en) (jsA_w en) (jsA_Dw en) HJc HLED HLED3).
  - intros y Hy. exact (proj1 (HwK y Hy)).
  - split; [exact (proj1 HwRw) | intros y Hy; apply (apresent_writable SEGS); exact (proj2 (HwK y Hy))].
  - exact HDwL.
  - exact HDwL3.
  - intros y ((a', k') & Hb & Hy). exact (proj1 (HDwOff a' k' y Hb Hy)). }
pose proof (pjrA_agree_trans SEGS _ _ _ _ HAGRW HAGW2) as HAGRW2.
assert (HNODEW2 : pj_nodeR SEGS (rdW W2 mem2) (prh_lin Lam3) (jsA_w en) (jsA_tv en) (jsA_Dw en))
  by exact (pjst_node_frame SEGS (jsA_tv en) _ _ _ _ (jsA_w en) (jsA_Dw en) HNODEW HAGW2 HDwL3).
assert (HPLW2 : pjsA_place B dd en ly2 S2 Lam3 W2 mem2 (jsA_w en)).
{ apply (pjsA_place_kept B ARx LAWS dd en ly S Hp W mem mdc (jsA_Lam en) (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en)
    (STK_pj_free dd + (48 + jsA_d en)) (jsA_sp0 en + jsA_d en) FP1 ly2 S2 Hp2 W2 mem2 md2 k1
    Lam3 (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en) (jsA_w en) HARcc HJc HLED HLED3).
  - intros y Hy. exact (proj2 (HFP1lo y Hy)).
  - lia.
  - lia.
  - intros y Hy. apply HPRW. lia.
  - exact (HSLg (jsA_w en) HwDu).
  - intros b m Hbm HnL _ _. exact (HSBg b m Hbm HnL).
  - exact (pjsA_place_of_slot B dd en ly S (jsA_Lam en) W mem (jsA_w en) HSLOTW). }
pose proof HPLW2 as (_ & HwAt2 & _).
assert (HSLOTW2 : prhPj_slot (PA := PA) B (STK_pj_set dd) (jsA_d en) ly2 S2 Lam3 W2 (jsA_regs en) mem2 (jsA_w en)).
{ apply (pjsA_slot_of_place B dd en ly2 S2 Lam3 W2 mem2 (jsA_w en) HPLW2).
  apply (pjsA_hull_low B ARx LAWS VIS ly2 S2 Hp2 W2 mem2 md2 Lam3 (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en)
    (jsA_regs en) (jsA_d en) (jsA_w en) HAR2 HLED3 HwAt2). lia. }
destruct (pjrA_at_where B ARx LAWS HW8 ly2 S2 Hp2 W2 mem2 md2 Lam3 (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en)
  (jsA_regs en) (jsA_d en) (jsA_w en) HAR2 HLED3 HwAt2) as [(_ & Hwceil & HwWh) | (Hc & _)]; [|lia].
(* ---- the destination slot at the TAIL state ---- *)
destruct (pjrA_hb B ARx LAWS HW8 ly2 S2 Hp2 W2 mem2 md2 Lam3 (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en)
  (jsA_kids en) (56 * cap0) HAR2 HLED3 HkL3) as (_ & HkAB2 & _ & _ & _ & _ & _ & HkPo2).
assert (HzAt2 : prhReader_at B ly2 S2 Lam3 (jsA_regs en) (jsA_d en) z 56)
  by (left; exists (jsA_kids en), (56 * cap0); split; [exact HkL3 | lia]).
assert (HSLOTZ2 : prhPj_slot (PA := PA) B (STK_pj_set dd) (jsA_d en) ly2 S2 Lam3 W2 (jsA_regs en) mem2 z).
{ split; [lia|]. split; [exact HzAt2|].
  split; [split; [exact Hz8 | intros y Hy; apply (apresent_writable SEGS); exact (proj1 (HkPo2 y ltac:(lia)))]|].
  split; [apply amem_range_high; [lia | unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HkApp; lia | lia]|].
  split; [intros y Hy; split; [exact (proj2 (HkPo2 y ltac:(lia))) | lia]|].
  destruct (pjsA_vis_lam B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 Lam3 (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en)
    (jsA_kids en) (56 * cap0) z 56 HAR2 HLED3 HkL3 ltac:(lia) ltac:(lia) ltac:(lia)) as [Hra' Hhull].
  split; [exact Hra' | exact Hhull]. }
(* ---- the object's header at the cut: below the ceiling, or in the caller's window ---- *)
assert (HoW : (4096 <= jsA_o en /\ jsA_o en + 56 <= YM05.alloc_ceiling) \/
  (jsA_sp0 en <= jsA_o en /\ jsA_o en + 56 <= jsA_sp0 en + jsA_d en)).
{ destruct (pjrA_at_where B ARx LAWS HW8 ly S Hp W mem md (jsA_Lam en) (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en)
    (jsA_regs en) (jsA_d en) (jsA_o en) HARc HLED HoAt) as [(H1 & H2 & _) | (H1 & H2)]; [left | right]; lia. }
(* ---- the bytes the new object tree keeps from the entry: the header, the slot arrays but member i's slot, the
   other members' blocks ---- *)
set (KR := fun y => jsA_o en <= y < jsA_o en + 56 \/ jsA_kids en <= y < jsA_kids en + 56 * Z.of_nat i \/
  jsA_kids en + 56 * Z.of_nat (Datatypes.S i) <= y < jsA_kids en + 56 * Z.of_nat (length (jsA_ms en)) \/
  keys0 <= y < keys0 + 8 * Z.of_nat (length (jsA_ms en)) \/
  exists b, In b (D1 ++ (x, kx) :: D2) /\ pj_holdsR b y).
assert (Hnekk : (keys0, 8 * cap0) <> (jsA_kids en, 56 * cap0)) by (intros E; apply HkNotIn; rewrite <- E; left; reflexivity).
assert (HKRc : forall y, KR y -> (jsA_o en <= y < jsA_o en + 56) \/
  (exists a' k', In (a', k') Dr /\ a' <= y < a' + k' /\ ~ (z <= y < z + 56))).
{ intros y Hy. unfold KR in Hy. destruct Hy as [Hy | [Hy | [Hy | [Hy | (b & Hb & Hy)]]]].
  - left. exact Hy.
  - right. exists (jsA_kids en), (56 * cap0). split; [unfold Dr; left; reflexivity|]. split; [lia|]. rewrite Ez. lia.
  - right. exists (jsA_kids en), (56 * cap0). split; [unfold Dr; left; reflexivity|]. split; [lia|]. rewrite Ez. lia.
  - right. exists keys0, (8 * cap0). split; [unfold Dr; right; left; reflexivity|]. split; [lia|].
    intros Hz'. apply (pjrA_lam_sep B ARx LAWS HW8 ly S Hp W mem md (jsA_Lam en) (jsA_peak en) (jsA_cnt en) (jsA_fail en)
      (jsA_ran en) (jsA_most en) (jsA_own en) keys0 (8 * cap0) (jsA_kids en) (56 * cap0) y HARc HLED (HDL _ _ HkeysD) HkL Hnekk ltac:(lia)). lia.
  - right. destruct b as [a' k']. unfold pj_holdsR in Hy. cbn [fst snd] in Hy. exists a', k'.
    assert (HbDr : In (a', k') Dr) by (unfold Dr; right; right; exact Hb).
    split; [exact HbDr|]. split; [exact Hy|].
    assert (Hne : (a', k') <> (jsA_kids en, 56 * cap0)) by (intros E; apply HkNotIn; rewrite <- E; exact (HinTail _ Hb)).
    intros Hz'. apply (pjrA_lam_sep B ARx LAWS HW8 ly S Hp W mem md (jsA_Lam en) (jsA_peak en) (jsA_cnt en) (jsA_fail en)
      (jsA_ran en) (jsA_most en) (jsA_own en) a' k' (jsA_kids en) (56 * cap0) y HARc HLED (HDL _ _ (HDrD _ HbDr)) HkL Hne ltac:(lia)). lia. }
assert (HKRfoot : forall y, KR y -> pj_footR (jsA_o en) (jsA_D en) y).
{ intros y Hy. destruct (HKRc y Hy) as [Ho | (a' & k' & Hb & Hy' & _)]; [left; exact Ho|].
  right. exists (a', k'). split; [exact (HDrD _ Hb) | exact Hy']. }
assert (HKR2 : forall y, KR y ->
  aview SEGS (w_H W2) mem2 y = aview SEGS (w_H W) mem y /\ apresent (w_H W2) mem2 y /\
  ~ (z <= y < z + 56) /\ ~ (jsA_w en <= y < jsA_w en + 56) /\ ~ (jsA_sp1 en - ESTACK <= y < jsA_sp1 en) /\
  0 <= y < 2 ^ 64).
{ intros y Hy.
  assert (Hnw : ~ (jsA_w en <= y < jsA_w en + 56)) by (intros Hw'; exact (HWFOOT y Hw' (HKRfoot y Hy))).
  destruct (HKRc y Hy) as [Ho | (a' & k' & Hb & Hy' & Hnz)].
  - destruct (HoK y Ho) as [Hv Hp'].
    split; [exact Hv|]. split; [exact Hp'|].
    split; [intros Hz'; apply (HapD (jsA_kids en, 56 * cap0) y HkidsD); [unfold pj_holdsR; cbn [fst snd]; lia | exact Ho]|].
    split; [exact Hnw|].
    destruct HoW as [(Ho1 & Ho2) | (Ho1 & Ho2)]; split; lia.
  - pose proof (HDL _ _ (HDrD _ Hb)) as HbL. pose proof (HDrL3 _ _ Hb) as HbL3.
    destruct (pjrA_hb B ARx LAWS HW8 ly S Hp W mem md (jsA_Lam en) (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en)
      a' k' HARc HLED HbL) as (_ & _ & _ & Hb4096 & Hbceil & _).
    destruct (pjrA_hb B ARx LAWS HW8 ly2 S2 Hp2 W2 mem2 md2 Lam3 (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en)
      a' k' HAR2 HLED3 HbL3) as (_ & _ & _ & _ & _ & _ & _ & Hbpo2).
    split.
    { apply (pjsA_lam_bytes B ARx ly S Hp W mem mdc (STK_pj_free dd + (48 + jsA_d en)) (jsA_sp0 en + jsA_d en) FP1
        ly2 S2 Hp2 W2 mem2 md2 k1 (jsA_Lam en) (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en)
        Lam3 (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en) a' k' y HJc HLED HLED3 HbL HbL3 Hy').
      intros Hf. destruct (HinFP1 y Hf) as [Hz' | (a'' & k'' & Hin'' & Hr)]; [exact (Hnz Hz')|].
      apply (pjrA_lam_sep B ARx LAWS HW8 ly S Hp W mem md (jsA_Lam en) (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en)
        a' k' a'' k'' y HARc HLED HbL (HDL _ _ (HDuD _ Hin''))
        ltac:(intros E; rewrite E in Hb; exact (HDrNotDu _ Hb Hin'')) ltac:(lia) Hr). }
    split; [exact (proj1 (Hbpo2 y ltac:(lia)))|].
    split; [exact Hnz|]. split; [exact Hnw|]. split; lia. }
(* ======== +0x48  li a2, 56 (a plain step) ======== *)
apply YGcfRhLift.ra_rh_of_SRr.
pjsA_fd (PJSA_RET + 12) Hl4 Hd4.
eapply (pjsA_step_addi W2 regs2 mem2 md2 _ (PJSA_RET + 12) _ _ _ _ (12%bv : bv 5) (w64 56) Hl4 Hd4).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X4.
pose proof (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X4 HJ2') as HJ4.
replace (v_addi (Z_to_bv 64 (BASE + (PJSA_RET + 12))) 4) with (Z_to_bv 64 (BASE + (PJSA_RET + 16)))
  by (apply bv_eq; vm_compute; reflexivity).
(* ======== +0x4c  mv a0, s3 ======== *)
pjsA_fd (PJSA_RET + 16) Hl5 Hd5.
eapply (pjsA_step_addi W2 _ mem2 _ _ (PJSA_RET + 16) _ _ _ _ (10%bv : bv 5) (getr regs2 (19%bv : bv 5)) Hl5 Hd5).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ lazymatch goal with |- v_addi (getr _ ?rs) (bv_signed ?im) = _ =>
    replace rs with (19%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity);
    replace (bv_signed im) with 0 by (vm_compute; reflexivity) end.
  rewrite getr_other by pjsA_regne. unfold v_addi. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. }
intros X5.
pose proof (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X5 HJ4) as HJ5.
replace (v_addi (Z_to_bv 64 (BASE + (PJSA_RET + 16))) 4) with (Z_to_bv 64 (BASE + PJSA_TAIL))
  by (apply bv_eq; vm_compute; reflexivity).
assert (E19 : getr regs2 (19%bv : bv 5) = w64 z)
  by (rewrite (pjsA_pres regsc regs2 (19%bv : bv 5) HP2 ltac:(pjsA_cs)); exact E19c).
(* ======== the cut TAIL ======== *)
apply SRr_ret. cbv beta.
apply (HTAIL en ly2 S2 Hp2 W2 _ mem2 _ (k + k1) HPRE0).
split.
{ (* the invariant at TAIL *)
  split; [exact HJ5|].
  split; [exact KW|].
  split; [unfold spZ at 1; rewrite !getr_other by pjsA_regne;
          rewrite (pjsA_pres regsc regs2 (2%bv : bv 5) HP2 ltac:(pjsA_cs)); exact HSPC|].
  split; [exact KRA|]. split; [exact KS0|]. split; [exact KS1|]. split; [exact KS2|]. split; [exact KS3|].
  split; [exact KS4|].
  split; [rewrite !getr_other by pjsA_regne; rewrite (pjsA_pres regsc regs2 (8%bv : bv 5) HP2 ltac:(pjsA_cs));
          rewrite Eregsc, !getr_other by pjsA_regne; exact H8|].
  split; [rewrite !getr_other by pjsA_regne; rewrite (pjsA_pres regsc regs2 (18%bv : bv 5) HP2 ltac:(pjsA_cs));
          rewrite Eregsc, !getr_other by pjsA_regne; exact H18|].
  split; [rewrite !getr_other by pjsA_regne; rewrite (pjsA_pres regsc regs2 (20%bv : bv 5) HP2 ltac:(pjsA_cs));
          rewrite Eregsc, !getr_other by pjsA_regne; exact H20|].
  split.
  { intros r Hr.
    assert (Hcs' : acallee_saved (bv_unsigned r)).
    { unfold PJSA_KEPT in Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [pjsA_cs |]). destruct Hr. }
    rewrite !getr_other by pjsA_kept_ne. rewrite (pjsA_pres regsc regs2 r HP2 Hcs').
    rewrite Eregsc, !getr_other by pjsA_kept_ne. exact (HKEPT r Hr). }
  split; [exact KPR|]. split; [exact KROD|].
  (* the memnorm keep: the cut's from the entry, then pj_free's (its text's fpostWm); li / mv write no memory *)
  intros HMN0. exact (HMN2 (HKN HMN0)). }
split; [exact HROOM2|].
exists z, Lam3, (jsA_peak en), (jsA_cnt en), (jsA_fail en), (jsA_ran en), 0%nat, [].
split; [rewrite getr_same by pjsA_regne; exact E19|].
split; [rewrite getr_other by pjsA_regne; rewrite getr_same by pjsA_regne; reflexivity|].
split; [exact HLED3|].
split; [lia|].
split; [split; [intros ii Hii; lia | split; [left; reflexivity | intros ii Hii; lia]]|].
split; [split; [intros Hc; lia | intros _; reflexivity]|].
split; [exact HNODEW2|].
split; [exact HSLOTW2|].
split; [exact HSLOTZ2|].
split; [intros y Hw' Hz'; apply (HWFOOT y Hw'); right; exists (jsA_kids en, 56 * cap0);
        split; [exact HkidsD | unfold pj_holdsR; cbn [fst snd]; lia]|].
split; [lia|]. split; [lia|].
split.
{ (* the two writes are permitted: the slot in the kids block, val in its block or fake frame *)
  intros a [Ha | Ha].
  - left. right. left. split.
    + exact (HFPD (jsA_kids en) (56 * cap0) a HkidsD ltac:(rewrite HkRq; lia)).
    + exists (jsA_kids en - cf_head), (56 * cap0 + cf_head). split; [exact HkAB2 | rewrite HkRq; lia].
  - destruct (HwWh a Ha) as (_ & _ & [(bb & nn & Hbn & Hr) | (cid & pos & Hcp' & Hr)]).
    + left. right. left.
      split; [exists (jsA_w en, jsA_w en + 56); split; [right; left; reflexivity | cbn [fst snd]; lia]|].
      exists bb, nn. split; [exact Hbn | exact Hr].
    + right.
      split; [exists (jsA_w en, jsA_w en + 56); split; [right; left; reflexivity | cbn [fst snd]; lia]|].
      exists cid, pos. split; [rewrite Hfr2 in Hcp'; exact Hcp' | exact Hr]. }
split; [intros a Ha; exact (aview_some_of_apresent SEGS _ _ a (proj1 (HwWh a Ha)))|].
split.
{ intros a [Ha | Ha].
  - exact (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ a HAR2 HkAB2 ltac:(rewrite HkRq; lia)).
  - exact (proj1 (proj2 (HwWh a Ha))). }
(* ======== the obligation: the contract's post, first arm ======== *)
intros mem' regs' md' Hcpy Hzero Hkeep Hpres' Ha0'.
split; [exact HROOM2|].
destruct (pjrA_perm_sub (jsA_D en ++ jsA_Dw en) (jsA_Lam en)) as (Lr & HLr).
{ apply pjrA_nodup_app; [exact HndD | exact HndDw | intros b Hb Hb'; exact (HDWD b Hb' Hb)]. }
{ intros [a' k'] Hb. apply in_app_or in Hb as [Hb|Hb]; [exact (HDL _ _ Hb) | exact (HDwL _ _ Hb)]. }
set (Do := (jsA_kids en, 56 * cap0) :: (keys0, 8 * cap0) :: D1 ++ (x, kx) :: jsA_Dw en ++ D2).
assert (PDo : Permutation Do (Dr ++ jsA_Dw en)).
{ unfold Do, Dr. cbn [app]. rewrite <- app_assoc. cbn [app]. apply perm_skip. apply perm_skip.
  apply Permutation_app_head. apply perm_skip. apply Permutation_app_comm. }
exists Lam3, (jsA_peak en), (jsA_fail en), (jsA_ran en), 0, 0%nat, [], Lr, Do.
split; [exact Ha0'|].
split.
{ (* the ledger at the contract's post state: the statics and every head word are off both writes *)
  replace (jsA_cnt en + Z.of_nat 0) with (jsA_cnt en) by lia.
  apply (prh_ledger_kept_aview B ly2 S2 Hp2 W2 mem2 ly2 S2 Hp2 W2 mem' Lam3 (jsA_peak en) (jsA_cnt en) (jsA_fail en)
    (jsA_ran en) (jsA_most en) (jsA_own en) HLED3).
  - intros a Ha. pose proof (pst_in_img_A a Ha) as Himg. pose proof (Hsegs a Himg) as Hlo.
    apply Hkeep; [lia | | | lia].
    + intros Hz'. exact (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ a HAR2 HkAB2 ltac:(rewrite HkRq; lia) Himg).
    + intros Hw'. exact (proj1 (proj2 (HwWh a Hw')) Himg).
  - intros a' k' ii Hin Hii.
    destruct (pjrA_hb B ARx LAWS HW8 ly2 S2 Hp2 W2 mem2 md2 Lam3 (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en)
      a' k' HAR2 HLED3 Hin) as (Hk0'' & _ & _ & H4' & Hc' & _).
    apply Hkeep; [lia | | | lia].
    + intros Hz'. apply (pjrA_place_head B ARx LAWS HW8 ly2 S2 Hp2 W2 mem2 md2 Lam3 (jsA_peak en) (jsA_cnt en)
        (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en) (jsA_regs en) (jsA_d en) z a' k' HAR2 HLED3 HzAt2 Hsp0c Hin _ Hz'). lia.
    + intros Hw'. apply (pjrA_place_head B ARx LAWS HW8 ly2 S2 Hp2 W2 mem2 md2 Lam3 (jsA_peak en) (jsA_cnt en)
        (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en) (jsA_regs en) (jsA_d en) (jsA_w en) a' k' HAR2 HLED3 HwAt2 Hsp0c Hin _ Hw'). lia.
  - intros a' k' _ Hab. exact Hab.
  - apply Permutation_refl. }
(* the outcome cell: the contract's prh_oks, no allocation on this arm *)
split; [split; [intros ii Hii; lia | split; [left; reflexivity | intros ii Hii; lia]]|].
split; [split; [intros Hc; lia | intros _; reflexivity]|].
split; [rewrite <- app_assoc in HLr; exact HLr|].
split.
{ (* Lam3 = Do ++ Lr: pj_free took exactly Du out of Lam *)
  apply (Permutation_app_inv_l Du).
  apply (Permutation_trans (Permutation_sym HpF)). apply (Permutation_trans HLr).
  apply (Permutation_trans (Permutation_app (Permutation_app PD (Permutation_refl (jsA_Dw en))) (Permutation_refl Lr))).
  rewrite <- !app_assoc. apply Permutation_app_head.
  rewrite app_assoc. apply Permutation_app; [apply Permutation_sym; exact PDo | apply Permutation_refl]. }
split.
{ (* the allocator blocks: the harness blocks move from Lam to Lam3, the others stay *)
  destruct (pjrA_perm_sub (prhPj_hbl (jsA_Lam en)) (ablocks B (jsA_ly en) (jsA_S en))) as (other & Hot).
  { apply pjrA_nodup_hbl. exact (proj1 (proj2 HLED0)). }
  { intros [bb mm] Hb. pose proof (pjrA_hbl_in _ _ _ Hb) as Hin.
    destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLED0 Hin) as (_ & Hab & _).
    replace (bb, mm) with (bb + cf_head - cf_head, mm - cf_head + cf_head) by (f_equal; lia). exact Hab. }
  exists other. split; [exact Hot|].
  apply (Permutation_app_inv_l (prhPj_hbl Du)).
  apply (Permutation_trans (Permutation_sym HabF)). rewrite Eab. apply (Permutation_trans Hot).
  rewrite app_assoc. apply Permutation_app; [|apply Permutation_refl].
  unfold prhPj_hbl. rewrite <- map_app. apply Permutation_map. exact HpF. }
split.
{ (* val reads 0 *)
  intros j Hj. rewrite repeat_length in Hj. rewrite nth_repeat. split; [|lia].
  intros kk Hkk. assert (kk = 0%nat) by lia. subst kk. cbn [Z.of_nat]. rewrite Z.add_0_r.
  pose proof (Hzero (Z.of_nat j) ltac:(lia)) as Hzj. unfold aview in Hzj.
  destruct (mbyte SEGS (mrestrict (w_H W2) mem') (jsA_w en + Z.of_nat j)) as [bb|] eqn:Eb;
    cbn [option_map] in Hzj; [|discriminate Hzj].
  injection Hzj as Hbb. f_equal. apply bv_eq. rewrite Hbb. vm_compute. reflexivity. }
(* the model-run position: the entry's plus this arm's one event (pj_free's, or the empty bulk free) *)
split; [intros _; rewrite Eevs; exact HPOSR|].
(* prh_granted's clause and DEAD-PJSET: res = 0 on this arm *)
split; [intros _ _; reflexivity|].
split; [intros _; reflexivity|].
left.
split; [apply in_map_iff; exists (jsA_kname en, vi); split; [reflexivity | exact (nth_error_In _ _ Hnth)]|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split.
{ exists i, vi, Du, Dr. split; [exact Hnth|]. split; [exact Hfirst|]. split; [exact HNU|].
  split; [exact PD | exact PDo]. }
(* what the new object tree and its ordered list share: val's header copied to the slot, val's blocks and the
   other bytes the object reads as before, the ledger blocks, the block list duplicate-free and off the header *)
assert (HCPY : forall j, 0 <= j < 56 -> mbyte SEGS (rdW W2 mem') (z + j) = mbyte SEGS (rdW W2 mem2) (jsA_w en + j))
  by (intros j Hj; exact (pjrA_mbyte_aview2 SEGS _ _ _ _ _ _ (Hcpy j Hj))).
assert (HRWZ : pj_rwR SEGS (rdW W2 mem') z).
{ split; [exact Hz8|]. intros y Hy. apply (apresent_writable SEGS). apply Hpres'. exact (proj1 (HkPo2 y ltac:(lia))). }
assert (HAPZ : pj_apartR (jsA_Dw en) z).
{ intros b y Hb Hh Hz'. destruct b as [a' k']. exact (proj2 (HDwOff a' k' y Hb Hh) Hz'). }
assert (HAW : pj_agreeR SEGS (rdW W2 mem2) (rdW W2 mem') (fun y => exists b, In b (jsA_Dw en) /\ pj_holdsR b y)).
{ apply (pjrA_agree_pres W2 W2 mem2 mem').
  + intros y ((a', k') & Hb & Hy). unfold pj_holdsR in Hy. cbn [fst snd] in Hy.
    destruct (pjrA_hb B ARx LAWS HW8 ly2 S2 Hp2 W2 mem2 md2 Lam3 (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en)
      a' k' HAR2 HLED3 (HDwL3 _ _ Hb)) as (_ & _ & _ & H4' & Hc' & _).
    apply Hkeep; [lia | exact (proj2 (HDwOff a' k' y Hb Hy)) | | lia].
    intros Hw'. exact (HapDw (a', k') y Hb Hy Hw').
  + intros y ((a', k') & Hb & Hy). unfold pj_holdsR in Hy. cbn [fst snd] in Hy.
    destruct (pjrA_hb B ARx LAWS HW8 ly2 S2 Hp2 W2 mem2 md2 Lam3 (jsA_peak en) (jsA_cnt en) (jsA_fail en) (jsA_ran en) (jsA_most en) (jsA_own en)
      a' k' HAR2 HLED3 (HDwL3 _ _ Hb)) as (_ & _ & _ & _ & _ & _ & _ & Hpo').
    apply Hpres'. exact (proj1 (Hpo' y ltac:(lia))). }
assert (HA0 : pj_agreeR SEGS (rdW (jsA_W en) (jsA_mem en)) (rdW W2 mem') KR).
{ apply (pjrA_agree_trans SEGS _ (rdW W mem)).
  + apply (pjrA_agree_sub SEGS _ _ _ _ HAGR). exact HKRfoot.
  + apply (pjrA_agree_pres W W2 mem mem').
    * intros y Hy. destruct (HKR2 y Hy) as (Hv & _ & Hnz & Hnw & Hns & Hr).
      rewrite (Hkeep y Hr Hnz Hnw Hns). exact Hv.
    * intros y Hy. apply Hpres'. exact (proj1 (proj2 (HKR2 y Hy))). }
assert (HL1 : forall a' k', In (a', k') (D1 ++ (x, kx) :: D2) -> prh_lin Lam3 a' k')
  by (intros a' k' Hb; apply HDrL3; unfold Dr; right; right; exact Hb).
assert (HndDo : NoDup ([(jsA_kids en, 56 * cap0); (keys0, 8 * cap0)] ++ D1 ++ (x, kx) :: jsA_Dw en ++ D2)).
{ apply (pjrA_nodup_perm (Dr ++ jsA_Dw en)); [|exact (Permutation_sym PDo)].
  apply pjrA_nodup_app; [exact (pjrA_nodup_app_r Du Dr HndDuDr) | exact HndDw |].
  intros b Hb Hb'. exact (HDWD b Hb' (HDrD b Hb)). }
assert (HapDo : pj_apartR ([(jsA_kids en, 56 * cap0); (keys0, 8 * cap0)] ++ D1 ++ (x, kx) :: jsA_Dw en ++ D2) (jsA_o en)).
{ intros b y Hb. change (In b Do) in Hb. apply (Permutation_in _ PDo) in Hb. apply in_app_or in Hb as [Hb|Hb].
  + exact (HapD b y (HDrD b Hb)).
  + exact (HAPW b y Hb). }
(* the new object: member i's value is val's tree at the slot *)
destruct pjsA_glue_holds as (_ & _ & Hmh & _).
rewrite (Hmh (jsA_ms en) i (jsA_kname en) vi (jsA_tv en) Hnth Hfirst).
unfold Do.
split.
{ apply (pjrA_new_tree SEGS (rdW (jsA_W en) (jsA_mem en)) (rdW W2 mem2) (rdW W2 mem') (prh_lin (jsA_Lam en)) (prh_lin Lam3)
    (jsA_o en) num0 (jsA_kids en) keys0 cap0 (jsA_ms en) i (jsA_kname en) vi (jsA_tv en) D1 x kx D2 (jsA_w en) z (jsA_Dw en)
    HH0 Hnc0 Hcp HkL3 HyL3 Hnth HM1 Hkx Hcs HM2 Ez HNODEW2 HCPY HRWZ HAPZ HAW HA0 HL1 HDwL3 HndDo HapDo). }
split.
{ (* its block sizes (a Permutation): the entry's with member i's value sizes replaced by val's *)
  intros HWT.
  replace ((jsA_kids en, 56 * cap0) :: (keys0, 8 * cap0) :: D1 ++ (x, kx) :: jsA_Dw en ++ D2) with
    (((jsA_kids en, 56 * cap0) :: (keys0, 8 * cap0) :: D1 ++ [(x, kx)]) ++ jsA_Dw en ++ D2)
    by (cbn [app]; rewrite <- app_assoc; reflexivity).
  apply (pjrA_tblk_swap _ (jsA_ms en) i (jsA_kname en) vi (jsA_tv en) _ Du D2 (jsA_Dw en) Hnth); [|exact HTU | exact HWT].
  replace (((jsA_kids en, 56 * cap0) :: (keys0, 8 * cap0) :: D1 ++ [(x, kx)]) ++ Du ++ D2) with (jsA_D en)
    by (rewrite ED; cbn [app]; rewrite <- app_assoc; reflexivity).
  exact HTBLK0. }
(* FREEORD-COPY: its ordered free list, from the entry's cut at member i with val's moved into the slot (val's
   list carried entry -> TAIL by HAGRW2) *)
intros _ HFWe nn Hnn. rewrite HHEAD in HFWe |- *.
apply (pjrA_new_fo SEGS (rdW (jsA_W en) (jsA_mem en)) (rdW W2 mem2) (rdW W2 mem') (prh_lin (jsA_Lam en)) (prh_lin Lam3)
  (jsA_o en) (jsA_kids en) keys0 cap0 (jsA_ms en) i (jsA_kname en) vi (jsA_tv en) D1 x kx Du D2 (jsA_w en) z (jsA_Dw en)
  HFN0 HNZ0).
- rewrite <- ED. exact HNODE0.
- intros nn0 Hnn0. rewrite <- ED. destruct (HFORD HHEAD nn0 Hnn0) as (F1 & HF1 & HmF1). exists F1.
  split; [exact HF1 | rewrite HHEAD in HmF1; exact HmF1].
- exact Hnth.
- exact HM1.
- exact HNU.
- exact HM2.
- exact Ez.
- intros nv Hnv. destruct (HFWe nv Hnv) as (Fw & HFw & HmFw). exists Fw. split; [|exact HmFw].
  exact (pj_foR_frame SEGS _ _ _ _ (prh_lin Lam3) _ _ _ HFw HDwL3 HAGRW2).
- exact HCPY.
- exact HRWZ.
- exact HAPZ.
- exact HAW.
- exact HA0.
- exact HL1.
- exact HkL3.
- exact HyL3.
- exact HDwL3.
- exact HndDo.
- exact HapDo.
- exact Hnn.
Qed.
End x.
