(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: segment C1 of pj_string's image-B walk (fuzz_preset asan-ubsan; the cuts of
   lib/B/Prog/pj_string_defs.v): from PJS_C1 (+0x68, `jal fuzz_strdup`, a0 = the string) through the call to the cut
   pjs_C2 at its return site (+0x6c), then the segment pjs_seg_C2 (a premise).
     +0x68  jal fuzz_strdup   stepped concretely (YA0n.v SRr_step / YK14.v step_jal_link; pj_parse_seg_c2ref.v's
                              pjr_step_jal), then the kit's tfuzz_strdup_specX (the kit's tip d607d12e4b0f,
                              lib/A/PRH_FnAlloc.v:517-558: the post-implication form with THE OUTCOME conjunct) by
                              YCbqGcallW.v aj_call_xW at the callee window e1 = 0 (the text is fpost:
                              fpostW_x_of_apost) with an EMPTY footprint; the chain from s0 = v is empty
                              (v < alloc_ceiling: achain_low).
   The callee's premises: fpre (PRH_Base.v: afn_pre_x from the call rule, the read-only view of the
   cut, the stack top of the entry, the return site below the ceiling, and FRM0-ENTRY frm_zero (fp_csr fx) from
   pj_string's own fpre - nothing here moves the float state), room_live_cf S, prh_malloc_univ (the
   prh_univ_closure_malloc from the closure, at image B's generated return site list), the two live-set conjuncts,
   the hull budget of its one malloc (pj_string_defs.v pjs_g_hull at pjs_pre's entry position and run of at most 4
   calls, the event within one call's counts by lib/A/PresetHullPay.v hull_nt_one_mal),
   a0, the cut's cstr_ok / kept_at / ledger, the bounds, and the live premise under the call's success flag
   (cnt <> fail ->, the tip's guard on both texts; pjs_pre's guarded sum hands it on). No position at entry: the
   call's allocator state is the entry's (S0), so the post's two position implications are applied at pj_string's
   entry position (pjs_pre's iface_room_pos at js_i, js_hist): E = [] needs prhPj_run_at_nil, E = [HMal ..] is the
   run's event at js_i (prh_run_at_one); that gives the cut pjs_C2's position. The post is read BY NAME
   (pjs1_conj_pick, the kit's ec_conj_pick). DEAD-PJSTRING: with cnt <> fail, the kit's run premise and prh_cons_from
   (pjs_run / pjs_cons) put the strdup's HMal at js_i as a consumer event, and the OUTCOME conjunct at the same
   position gives res <> 0.
   What the call keeps of pj_string's state (the callee's journal from the call, own = [], FP = []): the caller window,
   the frame words and the read-only view (its stack and image clauses); v's 56 bytes (its block clause for v in a
   block live at both states - fuzz_strdup frees none -, its frame clause for v in a caller's fake frame); v's
   writability and shadow by the laws at the return state (alx_hshadow for a harness block, whose base stays hidden;
   alx_shadow for another block, which holds no hidden head; the journal's frame-shadow clause for a fake frame).
   On success the new block is apart from v's block or frame (the laws' pairwise separation at the return state:
   ablocks there is the entry's with the new block appended) and 16-aligned, so its user bytes miss v and its head
   word misses v's str field.
   proves no function (kind: segment lemma). Section hypotheses: AR_laws_x SEGS B ARx cf_head; pjs_g_hull.
   Numerals: 32 / 56 / 24 / 16 / 8 (LENGTH: frame, node, slots, alignment, word); 64 (LENGTH: fpre's stack margin);
   4096 (LENGTH: the null page); 2 ^ 40 / 2 ^ 64 (LENGTH: code span, words); register numbers (WORD). No ADDRESS. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YC1fP YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetHullPay.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnAlloc PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger PjStringCommon.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB pj_string_defs pj_string_glue.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Open Scope Z_scope.
#[local] Existing Instance prh_img_B.

(* ---- small tactics (pj_parse_seg_c2ref.v's): register disequality, callee-saved membership, a listing word ---- *)
Ltac pjs1_regne :=
  let E := fresh "E" in
  intros E; apply (f_equal (fun x : bv 5 => bv_unsigned x)) in E; vm_compute in E; discriminate E.
Ltac pjs1_cs :=
  lazymatch goal with |- acallee_saved (bv_unsigned ?x) =>
    let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end;
  unfold acallee_saved; lia.
Ltac pjs1_fd k Hl Hd :=
  let r := eval vm_compute in
    (clookup (@pa_tbl _ B_prog_listing PI_prog_B) (@pa_val _ B_prog_listing PI_prog_B A_TEXT + k)) in
  lazymatch r with
  | Some ?w =>
    assert (Hl : clookup (@pa_tbl _ B_prog_listing PI_prog_B) (@pa_val _ B_prog_listing PI_prog_B A_TEXT + k) = Some w)
      by (vm_compute; reflexivity);
    let dz := eval vm_compute in (decode_any (Z_to_bv 32 w)) in
    assert (Hd : decode_any (Z_to_bv 32 w) = dz) by (vm_compute; reflexivity)
  | _ => fail "pjs1_fd: no image word at offset" k
  end.
(* a callee's post BY NAME (the kit's ec_conj_split / ec_conj_pick, lib/AU/Prog/Ent102CallB.v:168-174 at d607d12e4b0f):
   split the top-level conjunctions, then close the goal by its type, so a conjunct added to the post shifts nothing *)
Ltac pjs1_conj_split H :=
  lazymatch type of H with
  | _ /\ _ =>
    let H1 := fresh "Ec" in let H2 := fresh "Ec" in destruct H as [H1 H2]; pjs1_conj_split H1; pjs1_conj_split H2
  | _ => idtac
  end.
Ltac pjs1_conj_pick H := pjs1_conj_split H; assumption.

Lemma pjs1_pres : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). exact (HP _ Hr). Qed.

(* one concrete `jal` at a listing offset k of image B (pj_parse_seg_c2ref.v pjr_step_jal) *)
Section h. Context {rc : YM05.RunCeil}.
#[local] Notation PA := PI_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
Lemma pjs1_step_jal : forall (fy : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
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

Section call. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_B)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* the hull budget at a run position (pj_string_defs.v pjs_g_hull) *)
Hypothesis HULL : @pjs_g_hull cp.

Theorem pjs_seg_C1_holds : forall CTX0,
  pjs_texts (SK := SK) B ARx -> pjs_seg_C2 (SK := SK) B ARx CTX0 -> pjs_seg_C1 (SK := SK) B ARx CTX0.
Proof.
intros CTX0 TXT SEG2 en regs mem md k HPRE HCNT HC1.
destruct TXT as (_ & STRDUP).
pose proof (@pa_segs_low _ B_prog_listing PA) as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cf_head_nonneg as Hh0.
destruct (pjs_pre_v B ARx LAWS CTX0 en HPRE) as (HPL & Hv4096 & Hv56 & Hv8 & Hvamr & Hvimg & Hvpst & Hvhd).
pose proof HPRE as HPRE0.
destruct en as [ly0 S0 Hp0 W0 r0 mem0 md0 ch0 d v s cs Lam peak cnt fail ran most own rpsm rpx rpos rpi rpH0 rphist].
unfold pjs_cnt in HCNT. cbn [js_S] in HCNT. destruct HCNT as (HSEC & HC24).
unfold pjs_place in HPL.
unfold js_len, js_sp1, js_sp0 in *.
cbn [js_ly js_S js_Hp js_W js_regs js_mem js_md js_ch js_d js_v js_s js_cs js_Lam js_peak js_cnt js_fail js_ran js_most js_own] in *.
unfold pjs_pre in HPRE. cbv zeta in HPRE.
cbn [js_ly js_S js_Hp js_W js_regs js_mem js_md js_ch js_d js_v js_s js_cs js_Lam js_peak js_cnt js_fail js_ran js_most js_own]
  in HPRE.
destruct HPRE as (HFPRE & HUNIV & HROOM & HRP & HLOS & _ & _ & HFWIN & _ & HCEIL & _ & _ & HMAX & HLED0 & HLIVE).
(* fuzz_strdup's hull budget: its one malloc, paid from the entry position (the call's state is the entry's S0) *)
assert (HHULL : PresetHullBudget.hull_budget S0 [PresetReqAt.HMal (Z.of_nat (length cs) + 1 + cf_head)]).
{ destruct HULL as [HM HP].
  assert (HR : 0 <= Z.of_nat (length cs) + 1 + cf_head <= 2 ^ 30) by lia.
  destruct (PresetHullPay.hull_nt_one_mal _ HR) as [N T].
  exact (HP _ _ _ _ _ _ _ _ HLOS HRP N T). }
destruct HFPRE as ((HAR0 & Hret & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & HROD0 & HSTKHI & HRAC & HFRM).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
destruct HFWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
destruct HC1 as (HINV & H10 & HCSTR & HKAT & HLED).
unfold pjs_inv in HINV. unfold js_len, js_sp1, js_sp0 in HINV, HCSTR, HKAT.
cbn [js_ly js_S js_Hp js_W js_regs js_mem js_md js_ch js_d js_v js_s js_cs js_Lam js_peak js_cnt js_fail js_ran js_most js_own]
  in HINV, H10, HCSTR, HKAT, HLED.
destruct HINV as (HJ & HWIN & HSP & VRA & VS0 & VS1 & VS2 & H8 & H18 & HKEPT & HFPRES & HROD & HVB & HVW & HVRA & HMN).
unfold PJS_FR in *.
set (sp0 := spZ r0) in *.
assert (HSTKF : 0 <= STK_fuzz_strdup) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HSTKB : STK_fuzz_strdup + 32 <= STK_pj_string) by (apply Z.leb_le; vm_compute; reflexivity).
(* ======== +0x68  jal fuzz_strdup ======== *)
unfold pjs_cfg.
pjs1_fd PJS_C1 Hl1 Hd1.
eapply (pjs1_step_jal fx W0 regs mem md _ PJS_C1 _ _ _ (1%bv : bv 5) (Z_to_bv 64 (BASE + PJS_C2))
  (Z_to_bv 64 (@pa_sigma _ B_prog_listing PA AS_fuzz_strdup)) Hl1 Hd1).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X1.
pose proof (ajournal_x_materialize (SK := SK) SEGS B PST ARx LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1 HJ) as HJ1.
lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?r _ _ _) ?m) _ =>
  remember r as regsc eqn:Eregsc; set (mdc := m) in * end.
(* the call state's registers *)
assert (HSPC : spZ regsc = sp0 - 32).
{ unfold YG0d.spZ at 1. rewrite Eregsc, getr_other by pjs1_regne. exact HSP. }
assert (Hc8 : getr regsc 8 = w64 v) by (rewrite Eregsc, getr_other by pjs1_regne; exact H8).
assert (Hc18 : getr regsc 18 = w64 SHADOW_OFF) by (rewrite Eregsc, getr_other by pjs1_regne; exact H18).
assert (HS0LOW : s0Z regsc < YM05.alloc_ceiling).
{ unfold YG0d.s0Z. rewrite Hc8. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (HGP : getr regsc 3 = w64 (as_gp B)).
{ rewrite Eregsc, getr_other by pjs1_regne. rewrite (HKEPT 3%bv) by (unfold PJS_KEPT; left; reflexivity). exact Hgp. }
assert (HTP : getr regsc 4 = w64 (as_tp B)).
{ rewrite Eregsc, getr_other by pjs1_regne. rewrite (HKEPT 4%bv) by (unfold PJS_KEPT; right; left; reflexivity).
  exact Htp. }
assert (HRA1 : getr regsc 1 = Z_to_bv 64 (BASE + PJS_C2)) by (rewrite Eregsc; apply getr_same; pjs1_regne).
assert (HRAW : YK0s.ret_ok (Z_to_bv 64 (BASE + PJS_C2))).
{ apply (YC1fP.ret_ok_codeptr_v (PI := PA)); [split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity |].
  vm_compute. reflexivity. }
assert (HRA4 : 4096 <= bv_unsigned (Z_to_bv 64 (BASE + PJS_C2))) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HSPO : spZ regsc = sp0 + d + (-32 - d)) by (rewrite HSPC; lia).
assert (Hal : (-32 - d) mod 16 = 0) by lia.
assert (Hneg : -32 - d <= 0) by lia.
assert (Hbud : STK_fuzz_strdup - (-32 - d) <= STK_pj_string + d) by lia.
assert (He0 : 0 <= 0) by lia.
assert (Hetop : -32 - d + 0 <= 0) by lia.
(* ======== the call: the fuzz_strdup text at the callee window e1 = 0, footprint [] ======== *)
eapply SRr_bind.
{ eapply (aj_call_xW (fx := fx) (SK := SK) SEGS B PST ARx LAWS Hsegs W0 regsc mem
    (@pa_sigma _ B_prog_listing PA AS_fuzz_strdup)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STK_fuzz_strdup 0 [] (-32 - d) (Z_to_bv 64 (BASE + PJS_C2)) [] _
    HJ1 HSPO Hal Hneg HSTKF Hbud He0 eq_refl Hetop HGP HTP HRA1 HRAW HRA4 (achain_low _ _ _ _ HS0LOW)).
  - intros HPRE1 HWIN1. eapply SRr_mono.
    + apply (STRDUP ly0 S0 Hp0 W0 regsc mem mdc [] (pjs_sarg s) cs Lam peak cnt fail ran most own).
      * split; [exact HPRE1|]. split; [exact HROD|]. split; [rewrite HSPC; lia|].
        split; [|exact HFRM].
        unfold YG0d.raZ. rewrite HRA1. pose proof (@YM05.alloc_ceiling_value rc) as [[ACm _] _].
        assert (EB : bv_unsigned (Z_to_bv 64 (BASE + PJS_C2)) < 2 ^ 40) by (apply Z.ltb_lt; vm_compute; reflexivity).
        lia.
      * exact HROOM.
      * apply (prh_univ_closure_malloc B CTX0 HUNIV). vm_compute. discriminate.
      * exact HSEC.
      * exact HC24.
      * exact HHULL.
      * rewrite Eregsc, getr_other by pjs1_regne. exact H10.
      * exact HCSTR.
      * exact HKAT.
      * exact HMAX.
      * exact HLED.
      * intros Hnf. specialize (HLIVE Hnf). unfold LIVE_pj_string in HLIVE. lia.
    + cbv beta. intros W' c' _ H. apply fpostW_x_of_apost. exact H.
  - intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJc & _ & HP2 & HK).
destruct HK as (HKQ & HMN2). destruct HKQ as (res & HKQ). cbv beta in HKQ.
(* fuzz_strdup's post (tfuzz_strdup_specX, PRH_FnAlloc.v:532-558 at d607d12e4b0f), each conjunct picked BY ITS TYPE *)
assert (H10' : getr regs2 10 = w64 res) by pjs1_conj_pick HKQ.
assert (HROOM2 : room_live_cf S2) by pjs1_conj_pick HKQ.
assert (HRI0 : res = 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
    (i : nat) (H0 : list Z) (hist : list YG00.chunk),
    PresetRoomPos.iface_room_pos sm x os i H0 hist S0 -> PRH_Base.prh_run_at sm x os i [] ->
    exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (@nil PresetReqAt.hev))%nat H0 hist' S2)
  by pjs1_conj_pick HKQ.
assert (HRI1 : res <> 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
    (i : nat) (H0 : list Z) (hist : list YG00.chunk),
    PresetRoomPos.iface_room_pos sm x os i H0 hist S0 ->
    PRH_Base.prh_run_at sm x os i [PresetReqAt.HMal (Z.of_nat (length cs) + 1 + cf_head)] ->
    exists hist', PresetRoomPos.iface_room_pos sm x os
      (i + length [PresetReqAt.HMal (Z.of_nat (length cs) + 1 + cf_head)])%nat H0 hist' S2)
  by pjs1_conj_pick HKQ.
(* THE OUTCOME conjunct (PRH_FnAlloc.v:548-556 at d607d12e4b0f) *)
assert (HOUT : forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
    (i : nat) (H0 : list Z) (hist : list YG00.chunk),
    PresetRoomPos.iface_room_pos sm x os i H0 hist S0 ->
    PRH_Base.prh_run_at sm x os i [PresetReqAt.HMal (Z.of_nat (length cs) + 1 + cf_head)] ->
    PRH_Base.prh_cons_from sm x os i (length [PresetReqAt.HMal (Z.of_nat (length cs) + 1 + cf_head)]) ->
    cnt <> fail ->
    res <> 0 /\
    exists hist', PresetRoomPos.iface_room_pos sm x os
      (i + length [PresetReqAt.HMal (Z.of_nat (length cs) + 1 + cf_head)])%nat H0 hist' S2)
  by pjs1_conj_pick HKQ.
assert (HPOST : prh_alloc_post (PA := PA) B (Z.of_nat (length cs) + 1) ly0 S0 Hp0 W0 Lam peak cnt fail ran most own
    res ly2 S2 Hp2 W2 mem2) by pjs1_conj_pick HKQ.
assert (HBY : res <> 0 -> bytes_at (PA := PA) W2 mem2 res (cs ++ [0])) by pjs1_conj_pick HKQ.
clear HKQ.
(* the position at the return: the post's implications at pj_string's entry position (HRP, at the call's S0) *)
assert (HRP0 : res = 0 -> exists hist', PresetRoomPos.iface_room_pos rpsm rpx rpos rpi rpH0 hist' S2).
{ intros Hr0.
  destruct (HRI0 Hr0 rpsm rpx rpos rpi rpH0 rphist HRP (prhPj_run_at_nil rpsm rpx rpos rpi)) as (h' & Hh').
  cbn [length] in Hh'. rewrite Nat.add_0_r in Hh'. exists h'. exact Hh'. }
assert (HRP1 : res <> 0 -> nth_error (PresetRun.hruns rpsm rpx rpos) rpi =
    Some (PresetReqAt.HMal (Z.of_nat (length cs) + 1 + cf_head)) ->
  exists hist', PresetRoomPos.iface_room_pos rpsm rpx rpos (Datatypes.S rpi) rpH0 hist' S2).
{ intros Hr0 Hev.
  destruct (HRI1 Hr0 rpsm rpx rpos rpi rpH0 rphist HRP (proj2 (prh_run_at_one _ _ _ _ _) Hev)) as (h' & Hh').
  cbn [length] in Hh'. rewrite Nat.add_1_r in Hh'. exists h'. exact Hh'. }
pose proof (ajx_ar HJc) as HAR2. pose proof (ajx_ly HJc) as Hly2. pose proof (ajx_frs HJc) as Hfrs2. pose proof (ajx_hi HJc) as F1. pose proof (ajx_blk HJc) as F2. pose proof (ajx_img HJc) as F3. pose proof (ajx_frm HJc) as F4.
cbn [app] in Hfrs2.
destruct (pjs1_blocks B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ md2 HPOST HAR2) as (HBK & HNEW).
assert (Efa : forall cid pos, frame_addr ly2 cid pos = frame_addr ly0 cid pos).
{ intros cid pos. unfold frame_addr. destruct Hly2 as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
(* what the callee keeps at and above alloc_ceiling outside its own window [sp1 - STK1, sp1) *)
assert (KST : forall a, sp0 - 32 <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W0) mem a).
{ intros a Ha. apply F1; [lia|]. rewrite Z.add_0_r. lia. }
(* the callee-saved registers of the return state *)
assert (KREG : forall r, In r ((2%bv : bv 5) :: (8%bv : bv 5) :: (18%bv : bv 5) :: PJS_KEPT) ->
  getr regs2 r = getr regsc r).
{ intros r Hr. cbv [PJS_KEPT In] in Hr.
  repeat match type of Hr with _ \/ _ => destruct Hr as [Hr | Hr] | False => destruct Hr | _ = _ => subst r end;
  (apply pjs1_pres; [exact HP2 | pjs1_cs]). }
(* v's facts at the return state, by its place *)
assert (HV2 : garr8 SEGS (rdW W2 mem2) v (pjs_bytes 0) /\
  (forall a, v <= a < v + 56 -> writable_at SEGS (rdW W2 mem2) a) /\
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF v 56 /\
  ((res <> 0 -> (forall x, res <= x < res + Z.of_nat (length cs) + 1 -> ~ (v <= x < v + 56)) /\
      (forall x, res - cf_head <= x < res - cf_head + 8 -> ~ (v + 16 <= x < v + 24))))).
{ destruct HPL as [(a0 & k0 & Hin0 & Ha0 & Hk0) | [(b & m & Hin1 & Hnl & Hb & Hm) | (cid & pos & Hin2 & Hf & Hfm)]].
  - (* a harness block's user bytes *)
    destruct (prh_ledger_hblock B ly0 S0 Hp0 W0 mem0 Lam peak cnt fail ran a0 k0 most own HLED0 Hin0) as (Hk0p & Hab & Hhp & H16 & _).
    assert (Rq : 1 <= req_size (k0 + cf_head) /\ k0 + cf_head <= req_size (k0 + cf_head)) by (apply req_size_pos; lia).
    destruct (pjs1_hblock_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a0 k0 HPOST Hin0) as (Hab2 & Hhp2).
    destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hab2) as (Ha16 & _ & _ & _ & Hown2 & _).
    destruct (alx_hshadow SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hab2 Hhp2) as [Hbs _].
    split.
    { apply (pjs1_garr8_keep W0 W2 mem mem2 v _ HVB). rewrite pjs_bytes_len. intros x Hx.
      replace x with (a0 - cf_head + (x - (a0 - cf_head))) by lia.
      apply (F2 _ _ _ Hab Hab2); [lia | intros (r & [] & _)]. }
    split; [intros a Ha; apply (apresent_writable SEGS); exact (proj1 (Hown2 a ltac:(lia)))|].
    split; [exact (block_shadow_range _ SHADOW_OFF (a0 - cf_head + cf_head) (req_size (k0 + cf_head) - cf_head) v 56
                    Hbs ltac:(lia) ltac:(lia))|].
    intros Hr0. destruct (HNEW Hr0) as (Hnew & Hdj). pose proof (Hdj _ Hab) as Hd.
    destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hnew) as (Hn16 & _).
    assert (Rn : 1 <= req_size (Z.of_nat (length cs) + 1 + cf_head) /\
      Z.of_nat (length cs) + 1 + cf_head <= req_size (Z.of_nat (length cs) + 1 + cf_head)) by (apply req_size_pos; lia).
    unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    split; intros x Hx Hx'; lia.
  - (* another live allocator block *)
    assert (Rm : 1 <= req_size m /\ m <= req_size m) by (apply req_size_pos; lia).
    pose proof (HBK _ Hin1) as Hin1'.
    destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hin1') as (Hb16 & _ & _ & _ & Hown2 & _).
    assert (NOH : forall h, In h Hp2 -> ~ (b <= h < b + req_size m)).
    { intros h Hh Hr. destruct (pjs1_heads B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPOST h Hh) as [Hh0' | (Hr0 & ->)].
      - pose proof HLED0 as (_ & _ & _ & HPm).
        apply (Permutation_in _ HPm) in Hh0'. apply in_map_iff in Hh0' as ([a1 k1'] & Eh & Hin). cbn [fst] in Eh. subst h.
        destruct (prh_ledger_hblock B ly0 S0 Hp0 W0 mem0 Lam peak cnt fail ran a1 k1' most own HLED0 Hin) as (Hk1 & Hab1 & _).
        assert (Rq1 : 1 <= req_size (k1' + cf_head) /\ k1' + cf_head <= req_size (k1' + cf_head))
          by (apply req_size_pos; lia).
        assert (Hne : (b, m) <> (a1 - cf_head, k1' + cf_head)).
        { intros E. injection E as E1 E2. apply Hnl. rewrite E1, E2.
          replace (a1 - cf_head + cf_head) with a1 by lia. replace (k1' + cf_head - cf_head) with k1' by lia. exact Hin. }
        pose proof (sep_blocks_x SEGS B ARx LAWS ly0 S0 Hp0 W0 mem0 md0 _ _ _ _ HAR0 Hin1 Hab1 Hne) as Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
      - destruct (HNEW Hr0) as (_ & Hdj). pose proof (Hdj _ Hin1) as Hd.
        assert (Rn : 1 <= req_size (Z.of_nat (length cs) + 1 + cf_head)) by (apply req_size_pos; lia).
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
    destruct (alx_shadow SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 b m HAR2 Hin1' NOH) as [Hbs _].
    split.
    { apply (pjs1_garr8_keep W0 W2 mem mem2 v _ HVB). rewrite pjs_bytes_len. intros x Hx.
      replace x with (b + (x - b)) by lia.
      apply (F2 _ _ _ Hin1 Hin1'); [lia | intros (r & [] & _)]. }
    split; [intros a Ha; apply (apresent_writable SEGS); exact (proj1 (Hown2 a ltac:(lia)))|].
    split; [exact (block_shadow_range _ SHADOW_OFF b (req_size m) v 56 Hbs ltac:(lia) ltac:(lia))|].
    intros Hr0. destruct (HNEW Hr0) as (Hnew & Hdj). pose proof (Hdj _ Hin1) as Hd.
    destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hnew) as (Hn16 & _).
    assert (Rn : 1 <= req_size (Z.of_nat (length cs) + 1 + cf_head) /\
      Z.of_nat (length cs) + 1 + cf_head <= req_size (Z.of_nat (length cs) + 1 + cf_head)) by (apply req_size_pos; lia).
    unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    split; intros x Hx Hx'; lia.
  - (* a caller's fake frame *)
    assert (Hin2' : In (cid, pos) (frames S2)) by (rewrite Hfrs2; exact Hin2).
    destruct (alx_frames SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 cid pos HAR2 Hin2') as (_ & _ & Hfown & _).
    rewrite Efa in Hfown.
    destruct (frames_bounds_x SEGS B ARx LAWS ly0 S0 Hp0 W0 mem0 md0 cid pos HAR0 Hin2) as (Hf0 & Hfc & _).
    destruct (alx_frames SEGS B ARx LAWS ly0 S0 Hp0 W0 mem0 md0 cid pos HAR0 Hin2) as (Hf32 & _).
    assert (Hfs8 : fs_frame_bytes cid mod 8 = 0) by (apply pjs1_fsb8; lia).
    split.
    { apply (pjs1_garr8_keep W0 W2 mem mem2 v _ HVB). rewrite pjs_bytes_len. intros x Hx.
      apply (F4 cid pos x Hin2); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | intros (r & [] & _)]. }
    split; [intros a Ha; apply (apresent_writable SEGS); exact (proj1 (Hfown a ltac:(lia)))|].
    split.
    { eapply range_addressable_agree; [|exact HVRA]. intros x Hx.
      apply (F4 cid pos); [exact Hin2 | right | intros (r & [] & _)].
      unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd].
      set (f := frame_addr ly0 cid pos) in *. set (fb := fs_frame_bytes cid) in *. lia. }
    intros Hr0. destruct (HNEW Hr0) as (Hnew & _).
    destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hnew) as (Hn16 & _).
    pose proof (sep_block_frame_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ cid pos HAR2 Hnew Hin2') as Hd.
    rewrite Efa in Hd.
    assert (Rn : 1 <= req_size (Z.of_nat (length cs) + 1 + cf_head) /\
      Z.of_nat (length cs) + 1 + cf_head <= req_size (Z.of_nat (length cs) + 1 + cf_head)) by (apply req_size_pos; lia).
    unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    split; intros x Hx Hx'; lia. }
destruct HV2 as (HVB2 & HVW2 & HVRA2 & HAP2).
(* ======== the cut pjs_C2 at the return site ======== *)
refine (SEG2 _ ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1) HPRE0 _).
unfold pjs_C2, pjs_inv. unfold js_len, js_sp1, js_sp0.
cbn [js_ly js_S js_Hp js_W js_regs js_mem js_md js_ch js_d js_v js_s js_cs js_Lam js_peak js_cnt js_fail js_ran js_most js_own].
fold sp0. unfold PJS_FR.
split.
{ split; [exact HJ2|].
  split; [intros a Ha; rewrite KST by lia; exact (HWIN a Ha)|].
  split; [unfold YG0d.spZ at 1; rewrite (KREG 2%bv) by (cbn; tauto); exact HSPC|].
  split; [apply (pjs1_val_keep W0 W2 mem mem2 _ 8 _ VRA); intros x Hx; apply KST; change (Z.of_nat 8) with 8 in Hx; lia|].
  split; [apply (pjs1_val_keep W0 W2 mem mem2 _ 8 _ VS0); intros x Hx; apply KST; change (Z.of_nat 8) with 8 in Hx; lia|].
  split; [apply (pjs1_val_keep W0 W2 mem mem2 _ 8 _ VS1); intros x Hx; apply KST; change (Z.of_nat 8) with 8 in Hx; lia|].
  split; [apply (pjs1_val_keep W0 W2 mem mem2 _ 8 _ VS2); intros x Hx; apply KST; change (Z.of_nat 8) with 8 in Hx; lia|].
  split; [rewrite (KREG 8%bv) by (cbn; tauto); exact Hc8|].
  split; [rewrite (KREG 18%bv) by (cbn; tauto); exact Hc18|].
  split.
  { intros r Hr. rewrite (KREG r) by (right; right; right; exact Hr).
    rewrite Eregsc, getr_other; [exact (HKEPT r Hr)|].
    intros ->. cbv [PJS_KEPT In] in Hr.
    repeat (destruct Hr as [Hr | Hr]; [apply (f_equal (fun x : bv 5 => bv_unsigned x)) in Hr; vm_compute in Hr; discriminate Hr|]).
    destruct Hr. }
  split.
  { pose proof (ajx_pres HJ2) as Hpres2.
    intros a Ha. apply Hpres2. lia. }
  split.
  { intros a Hro Hos Her.
    rewrite (F3 a); [exact (HROD a Hro Hos Her) | | exact Hos | exact Her | | apply fp_spares_closed; intros (r & [] & _)].
    - destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
    - intros Hp'. exact (pst_not_ro_B a Hp' Hro). }
  split; [exact HVB2|]. split; [exact HVW2|]. split; [exact HVRA2|].
  intros H0. exact (HMN2 (HMN H0)). }
split; [exact HROOM2|].
exists res. split; [exact H10'|].
split; [cbn [js_sm js_x js_os js_i js_H0]; exact HRP0|].
split; [cbn [js_sm js_x js_os js_i js_H0]; exact HRP1|].
(* DEAD-PJSTRING: with no chosen failure the run's event at rpi is the strdup's HMal (the kit's run premise) and a
   consumer event (the kit's prh_cons_from), so fuzz_strdup's OUTCOME conjunct at the entry position (HRP, the call's S0)
   gives the grant *)
split.
{ intros Hc HRUN HCONS. unfold pjs_run, pjs_cons in HRUN, HCONS.
  cbn [js_sm js_x js_os js_i js_cs js_cnt js_fail] in HRUN, HCONS.
  assert (Ee : prhPj_string_evs (Z.of_nat (length cs)) cnt fail =
    [PresetReqAt.HMal (Z.of_nat (length cs) + 1 + cf_head)])
    by (unfold prhPj_string_evs; rewrite (proj2 (Z.eqb_neq cnt fail) Hc); reflexivity).
  rewrite Ee in HRUN, HCONS.
  exact (proj1 (HOUT rpsm rpx rpos rpi rpH0 rphist HRP HRUN HCONS Hc)). }
split; [exact HPOST|].
intros Hr0. destruct (HAP2 Hr0) as (HU & HH). split; [exact (HBY Hr0)|]. split; [exact HU | exact HH].
Qed.
End call.
