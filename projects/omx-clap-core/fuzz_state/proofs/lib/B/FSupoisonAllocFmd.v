(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AFfz.v, with its module paths changed and its addresses moved to omx-clap-core/fuzz_state's ASan build. *)
(* Modified by Theorem Labs, 2026-10: HU is tr_admit (as_universe B) S tr instead of In tr (as_universe B), and the depot walk gets the trace length; afree_drn takes In (call_trace ...) (as_universe B) \/ st_nev S < EV_MAX (tr_admit_call). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/AFfz.v, with its module paths and module names changed; 790 of its 1113 lines of code are new or changed and 235 lines of the source are left out. *)
(* fuzz_state: __interceptor_free's quarantine arms (no drain: lib/A/AFg2.v; with drain: lib/A/AFfz.v) under ARU for ANY set UP of user-poisoned heads outside the freed block. *)
(* Shared any-U allocator, within-budget units (cgif's EV_MAX 11,776, < 2 GiB per class); the cf form (fuzz_preset / fuzz_reply, YG0dcf.v) bridges to this. *)
(* Rule 24: no walk is proved from scratch; these are the released cgif_file_fuzzer walks (relocated as lib/A/AF*.v),
   ported to the weaker memory invariant (method: ALLOC-ARU-MAP-FREE.md).
   Port-from, text unchanged except where UP is threaded:
     lib/A/AFg2.v:95 TAILM, :279 afree_mid_arm, :409 afree_mid -> TAILMU, afree_mid_armU, afree_midU
     lib/A/AFfz.v:100 TAILD, :423 afree_drn_arm, :551 afree_drn -> TAILDU, afree_drn_armU, afree_drnU
     the arms' common text up to the enqueue call (AFg2.v:279-400 = AFfz.v:423-542) -> arm_prefix.
   Reused unchanged: the AFg1 facts (FH_ok, CONST_OUT, DFP_*, ENQ_PRE, MID_AG, ...) at mu := FSupoison.unpoison UP mem;
   the run segments AFgb.segA, AFgd.segB, AFgf.segCm1 and the depot call on the REAL configuration with the record
   FH_real (FH_ok rebuilt on mem); AFfl's state lemmas. The enqueue and drain calls go through FSupoisonAllocFK's
   enq_preU / enq_leafU and drain_preU / drain_leafU. Region condition: free_md_regions_off_ush (both walks fix the same
   byte classes: application memory, the image's shadow, the freed block's shadow).
   The trace premise is afree_realizesU's (In ... (as_universe B) \/ st_nev S < EV_MAX), turned into tr_admit by
   tr_admit_call; the depot call takes its length (tr_admit_len), as the donor AFg2.v / AFfz.v do. *)
(* Modified by Theorem Labs, 2026-10: the image-B port (fuzz_state.asan-ubsan) of lib/A/FSupoisonAllocFmd.v at 5cc58921ee2: each lib/A donor is its lib/B twin (AFxx -> YFxx, ABxx -> YBxx, AExx -> YExx), every statement is over B's tfibsegs (lib/B/YB1v.v), the kit is lib/B/FSupoisonAllocR / Rf / Rt; the pcs are by name: pc_free_ra0 Tfib_code, pc_wrap_free Tfib_code, A_Enqueue, A_StackDepotPut, PC_PUT_DRAIN_RA, PC_PUT_ENQ_RA. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1w YE3d YFeq YFgi YFex YFf0 YFfl YFfy YFfu.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YFfj.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YFew YFgm YFfw YFgb YFgd YFgf YFg1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YFfk.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YFeu.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0k.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB13.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison FSupoisonU.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSupoisonAllocR FSupoisonAllocFK.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
(* The pcs inside a function, by name: the entry is lib/B/YFeu.v / lib/B/YFew.v A_xxx or the lib/B/YB1w.v row, the offset is the B donor's pc minus that entry. *)
(* the return address of Put's Drain call (lib/B/YFfz.v:308). *)
Definition PC_PUT_DRAIN_RA : Z := tfib_A__ZN11__sanitizer10QuarantineIN6__asan18QuarantineCallbackENS1_9AsanChunkEE3PutEPNS_15QuarantineCacheIS2_EES2_PS3_m + 0xdc.
(* the return address of Put's Enqueue call (lib/B/YFfz.v:137). *)
Definition PC_PUT_ENQ_RA : Z := tfib_A__ZN11__sanitizer10QuarantineIN6__asan18QuarantineCallbackENS1_9AsanChunkEE3PutEPNS_15QuarantineCacheIS2_EES2_PS3_m + 0x1a4.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Local Open Scope am_scope.
Module FSP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.
Module FSU := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonU.
Module FAR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSupoisonAllocR.
Module FK := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSupoisonAllocFK.

(* A symbolic region that lies in application memory or is empty, for the regions of YFgm.REG0 and YFfw.SS_E:
   literal addresses below the shadow, the stack frame (atom 2), the freed block's header and first word (atom 10),
   the thread object (atom aT), the allocator cache (atom aC), the image word at aIM. *)
Definition rapp_b (r : YP09.region) : bool :=
  (YP09.r_hi r <=? YP09.r_lo r) ||
  match YP09.r_base r with
  | None => (0 <=? YP09.r_lo r) && (YP09.r_hi r <=? SHADOW_OFF)
  | Some k =>
    if (k =? 2)%nat then (- ASTACK <=? YP09.r_lo r) && (YP09.r_hi r <=? 0)
    else if (k =? 10)%nat then (-16 <=? YP09.r_lo r) && (YP09.r_hi r <=? 8)
    else if (k =? 32)%nat then (0 <=? YP09.r_lo r) && (YP09.r_hi r <=? kThreadObjSize)
    else if (k =? 33)%nat then (0 <=? YP09.r_lo r) && (YP09.r_hi r <=? 256)
    else if (k =? 37)%nat then (0 <=? YP09.r_lo r) && (YP09.r_hi r <=? 16)
    else false
  end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac cs_case HS HEn Htp kb :=
lazymatch goal with |- YK11.getr _ (Z_to_bv 5 ?k) = _ => replace (Z_to_bv 5 k) with kb by (apply bv_eq; reflexivity) end;
let RR := fresh "RR" in rreg HS kb RR; rewrite RR;
first [ rewrite HEn by (cbv; lia); first [ refine (YFgm.Er _ _ _ _ _ _ _ _ _ _ _ _ _); reflexivity | symmetry; refine (YFgm.Er _ _ _ _ _ _ _ _ _ _ _ _ _); reflexivity ]
| rewrite Htp; reflexivity | symmetry; rewrite Htp; reflexivity ].
Ltac inlist := cbn [In]; repeat (first [ left; reflexivity | right ]); fail.
Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (S : astate) (UP : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (p : sptr) (n : Z) (ch : list (Z * Z * Z)).
Local Notation mu := (FSP.unpoison UP mem).
Local Notation tr := (call_trace ly (pc_free_ra0 Tfib_code) regs ch).
Let sp0 : Z := bv_unsigned (YK11.getr regs 2).
Local Notation pa := (sptr_addr B ly p).
Local Notation nn := (req_size n).
(* FSupoisonU.acall_preU, split: the donor pre at mu and UP's two invariants. *)
Hypothesis PRE : acall_pre tfibsegs B ly S W regs mu md ch.
Hypothesis OKU : FSP.upoison_ok B ly S UP.
Hypothesis POU : FSP.upoisoned tfibsegs W mem UP.
Hypothesis HBLK : In (p, n) (blocks S).
(* afree_realizesU's premise: the ONLY source for the freed block's bytes and shadow being off UP. *)
Hypothesis HOUT : forall r, In r UP -> fst r + snd r <= pa \/ pa + nn <= fst r.
Hypothesis HA0 : YK11.getr regs 10 = w64 pa.
Hypothesis HU : tr_admit (as_universe B) S tr.
Hypothesis IA1 : tfib_ialloc_spec.
Hypothesis U1 : tfib_unwind_spec.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Hypothesis D1 : tfib_depot_spec B.
Hypothesis Q1 : FK.tfib_enqueue_spec_nbU B (need_new_batch (st_qthread S)).
Local Notation rd0 := (aview tfibsegs (w_H W) mu).
Local Notation q := (st_qthread S).
Lemma M : ARm B ly S rd0. Proof. exact (proj1 (proj1 PRE)). Qed.
Let WF : Wf (as_universe B) S := am_wf B ly S rd0 M.
Let LO : layout_ok ly := am_layout B ly S rd0 M.
Lemma ARU0 : FSP.ARU tfibsegs B ly S UP W mem md.
Proof. exact (FAR.ARU_intro B ly S UP W mem md (proj1 PRE) OKU POU). Qed.
Local Notation kk := (YFg1.kk S p).
Local Notation kk_facts := (YFg1.kk_facts B ly S W regs mu md p n ch PRE HBLK).
Local Notation Enn := (YFg1.Enn B ly S W regs mu md p n ch PRE HBLK).
Local Notation HB1 := (YFg1.HB1 B ly S W regs mu md p n ch PRE HBLK).
Local Notation HSP := (YFg1.HSP B ly S W regs mu md p n ch PRE).
Local Notation IMG := (YFg1.IMG B ly S W regs mu md ch PRE).
Local Notation p_facts := (YFg1.p_facts B ly S W regs mu md p n ch PRE HBLK).
Local Notation QB_facts := (YFg1.QB_facts B ly S W regs mu md p n ch PRE HBLK).
Local Notation hb1 := (YFg1.hb1 B ly W mu p).
Local Notation j1 := (YFg1.j1 ly W mu).
Local Notation j2 := (YFg1.j2 ly W mu).
Local Notation j3 := (YFg1.j3 B ly W mu p).
Local Notation E0 := (YFgm.E0 ly regs ch pa nn hb1 q j1 j2 j3).
Local Notation QBFv := (YFgm.QBFv nn q).
Local Notation E2 := (YFg1.E2 B ly S W regs mu p n ch).
Local Notation EaT := (YFg1.EaT B ly S W regs mu p n ch).
Local Notation EaQBF := (YFg1.EaQBF B ly S W regs mu p n ch).
Local Notation EaLEN := (YFg1.EaLEN B ly S W regs mu p n ch).
Local Notation FH_ok := (YFg1.FH_ok B TB ly S W regs mu md p n ch PRE HBLK HA0 IA1 U1 HTSD).
Local Notation CONST_OUT := (YFg1.CONST_OUT B TB ly S W regs mu md p n ch PRE HBLK HA0 IA1 U1 HTSD).
Local Notation DFP_RANGE := (YFg1.DFP_RANGE B TB ly S W regs mu md p n ch PRE HBLK HA0 IA1 U1 HTSD).
Local Notation DFP_OUT := (YFg1.DFP_OUT B TB ly S W regs mu md p n ch PRE HBLK HA0 IA1 U1 HTSD).
Local Notation ENQ_PRE := (YFg1.ENQ_PRE B TB ly S W regs mu md p n ch PRE HBLK HA0 HU IA1 U1 HTSD).
Local Notation MID_AG := (YFg1.MID_AG B TB ly S W regs mu md p n ch PRE HBLK).
Local Notation s1_wf := (YFg1.s1_wf B ly S W regs mu md p n ch PRE).
Local Notation kept_of_aview := (YFg1.kept_of_aview W).
Let s1 : astate := set_internal_inited true (set_nev (st_nev S + 1) S).
Let kk' : chunk := mkChunk (ck_beg kk) (ck_req kk) CQuarantined.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. Where UP is not (the walks' region condition).                                                                 *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Lemma OFF_APP : forall a, 0 <= a < 2 ^ 64 -> a < SHADOW_OFF \/ kHighMemBeg <= a -> FAR.offU UP a.
Proof. intros a Ha Hz. exact (FAR.offU_app B ly S UP W mem md a ARU0 Ha Hz). Qed.
Lemma OFF_LOW : forall a, 0 <= a < SHADOW_OFF -> FAR.offU UP a.
Proof. intros a Ha. exact (FAR.offU_low B ly S UP W mem md a ARU0 Ha). Qed.
(* A zone3 range is application memory (FSupoisonAllocFK.offU_zone3). *)
Local Notation OFF_Z3 := (FK.offU_zone3 B ly S UP W mem md ARU0).
Lemma OFF_SP : forall a, sp0 - ASTACK <= a < sp0 -> FAR.offU UP a.
Proof.
intros a Ha. pose proof HSP as HS'. apply (FAR.stack_offU B ly S UP W mem md a ARU0). unfold sp0 in *. lia.
Qed.
Lemma OFF_DEPSTK : forall a, sp0 - 2176 - DEP_STK <= a < sp0 - 2176 -> FAR.offU UP a.
Proof. intros a Ha. apply OFF_SP. unfold DEP_STK, ASTACK in *. lia. Qed.
(* The image's shadow (Tfib_const's shadow cells). *)
Lemma OFF_IMGSH : forall a, SHADOW_OFF + TFIB_IMG_LO / 8 <= a < SHADOW_OFF + TFIB_IMG_END / 8 -> FAR.offU UP a.
Proof.
intros a Ha. unfold TFIB_IMG_LO, TFIB_IMG_END in Ha. change (65536 / 8) with 8192 in Ha. change (6279168 / 8) with 784896 in Ha.
replace a with (shadow_addr ((a - SHADOW_OFF) * 8)).
- apply (FK.offU_img_shadow B LAWS ly S UP W mem md _ ARU0). unfold TFIB_IMG_LO, TFIB_IMG_END, SHADOW_OFF in *. lia.
- unfold shadow_addr. rewrite Z.div_mul by lia. lia.
Qed.
(* The freed block's shadow: off UP by the afree premise (FSupoisonAllocFK.ush_out_block_shadow). *)
Lemma OFF_FSH : forall a, YFgm.SPv pa <= a < YFgm.SPv pa + YFgm.CNT8v nn -> FAR.offU UP a.
Proof.
intros a Ha. pose proof p_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14).
pose proof QB_facts as (_ & _ & Q8).
unfold FAR.offU. rewrite Z.mod_small by (unfold kHighMemBeg, SHADOW_OFF in *; lia).
destruct (FSP.in_ush UP a) eqn:E; [|reflexivity]. exfalso.
apply (FK.ush_out_block_shadow B ly S UP pa nn a ltac:(lia) OKU HOUT E).
assert (Hc : pa = 8 * (pa / 8)) by (pose proof (Z.div_mod pa 8 ltac:(lia)); lia).
assert (Dv1 : (pa + nn - 1) / 8 = pa / 8 + (nn - 1) / 8)
  by (replace (pa + nn - 1) with (nn - 1 + pa / 8 * 8) by lia; rewrite Z.div_add by lia; lia).
assert (Dv2 : (nn + 7) / 8 = (nn - 1) / 8 + 1)
  by (replace (nn + 7) with (nn - 1 + 1 * 8) by lia; rewrite Z.div_add by lia; reflexivity).
unfold YFgm.SPv in Ha. rewrite P14 in Ha. rewrite Dv1. lia.
Qed.
(* The region condition of both walks: every byte whose value or presence is moved between mem and mu, and every
   byte of the walks' write windows, lies in one of these classes. *)
Definition free_md_fixed (a : Z) : Prop :=
  (0 <= a < 2 ^ 64 /\ (a < SHADOW_OFF \/ kHighMemBeg <= a)) \/
  (SHADOW_OFF + TFIB_IMG_LO / 8 <= a < SHADOW_OFF + TFIB_IMG_END / 8) \/
  (YFgm.SPv pa <= a < YFgm.SPv pa + YFgm.CNT8v nn).
Lemma free_md_regions_off_ush : forall a, free_md_fixed a -> FAR.offU UP a.
Proof.
intros a [[Ha Hz]|[Hi|Hf]]; [exact (OFF_APP a Ha Hz) | exact (OFF_IMGSH a Hi) | exact (OFF_FSH a Hf)].
Qed.
Lemma ush_not_off : forall s, FSP.in_ush UP s = true -> ~ FAR.offU UP s.
Proof.
intros s Hs O. unfold FAR.offU in O. pose proof (FSP.ush_range tfibsegs B ly S UP W mem md s ARU0 Hs) as R.
rewrite Z.mod_small in O by exact R. congruence.
Qed.
Lemma ush_low : forall s, FSP.in_ush UP s = true -> SHADOW_OFF <= s < kHighMemBeg.
Proof. intros s Hs. exact (proj2 (FSP.ush_facts tfibsegs B ly S UP W mem md s ARU0 Hs)). Qed.
Lemma OFF_WIN : forall a, YFgm.WIN ly regs pa a -> FAR.offU UP a.
Proof.
intros a Hw. destruct (YFgm.WIN_zone W ly regs mu ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FH_ok a Hw) as (Z1 & Z2 & Z3).
apply OFF_APP; [exact Z3|]. unfold kLowShadowBeg, SHADOW_OFF, kHighMemBeg in *. lia.
Qed.
Lemma OFF_WIN2 : forall a, YFgm.WIN2 ly regs pa a -> FAR.offU UP a.
Proof. intros a Hw. exact (OFF_WIN a (YFgm.WIN2_WIN ly regs pa a Hw)). Qed.
Lemma OFF_IZONE : forall a, YFgm.IZONE a -> FAR.offU UP a.
Proof. intros a Hz. apply OFF_LOW. unfold YFgm.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, SHADOW_OFF in *. lia. Qed.
Lemma DFP_OFF : forall a, depot_footprint B ly a -> FAR.offU UP a.
Proof.
pose proof (YFgm.LYB W ly regs mu ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FH_ok) as LB.
intros a Ha. unfold depot_footprint in Ha. rewrite (ts_depot _ TB), (ts_store _ TB) in Ha.
pose proof LB as (_ & _ & _ & _ & _ & _ & _ & _ & ZNB & _ & ZSB & _).
destruct Ha as [Ha|[Ha|[Ha|Ha]]].
- apply OFF_LOW. unfold TFIB_DEPOT, d_map1, SHADOW_OFF in *. lia.
- exact (OFF_Z3 _ _ a ZNB Ha).
- exact (OFF_Z3 _ _ a ZSB Ha).
- apply OFF_LOW. unfold TFIB_STORE, SHADOW_OFF in *. lia.
Qed.
(* Tfib_const's cells (YFfy.Tfib_const_loc): the image, the image's shadow, the thread object's head, the cache, the
   ly_D page. *)
Lemma CONST_OFF : Forall (fun c => forall i, 0 <= i < Z.max 1 (Z.of_nat (c_w c)) -> FAR.offU UP (aeval B ly (c_at c) + i)) (as_const B ly).
Proof.
rewrite (ts_const _ TB). apply Forall_forall. intros c Hc i Hi. pose proof FH_ok as FH.
pose proof (proj1 (forallb_forall _ _) (YFfy.Tfib_const_loc ly) c Hc) as K. unfold YFfy.const_loc_ok in K.
assert (LOW : forall a, YFfy.low_ok a (Z.max 1 (Z.of_nat (c_w c))) = true -> FAR.offU UP (a + i)).
{ intros a L. unfold YFfy.low_ok in L. set (w := Z.max 1 (Z.of_nat (c_w c))) in *.
assert (R : (TFIB_IMG_LO <= a /\ a + w <= TFIB_IAL_LO) \/ (TFIB_IAL_HI <= a /\ a + w <= TFIB_IAL_FLAG) \/ (TFIB_IAL_FLAG + 4 <= a /\ a + w <= TFIB_IMG_END) \/
(SHADOW_OFF + TFIB_IMG_LO / 8 <= a /\ a + w <= SHADOW_OFF + TFIB_IMG_END / 8)) by lia.
clear L. destruct R as [R|[R|[R|R]]].
1-3: apply OFF_LOW; unfold TFIB_IMG_LO, TFIB_IMG_END, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, SHADOW_OFF in *; lia.
apply OFF_IMGSH. lia. }
pose proof (YFgm.LYB W ly regs mu ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FH) as (ZT & _ & _ & _ & _ & _ & ZC & _).
destruct (c_at c); try discriminate K; cbn [aeval].
- apply LOW, K.
- apply (OFF_Z3 (ly_T ly) kThreadObjSize _ ZT). unfold kThreadObjSize. lia.
- apply (OFF_Z3 (ly_C ly) 256 _ ZC). lia.
- rewrite HTSD. apply LOW, K.
- rewrite (ts_inst _ TB). apply LOW, K.
- rewrite (ts_tp _ TB). apply LOW, K.
- pose proof (YFgm.LYBD W ly regs mu ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FH) as (ZD & _).
apply (OFF_Z3 (ly_D ly) 4096 _ ZD). lia.
Qed.
(* The regions of a symbolic state whose atoms below aHAVf are E0's (rapp_b). *)
Lemma rapp_off : forall (E : env) r a, (forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> rapp_b r = true ->
  base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r -> FAR.offU UP a.
Proof.
intros E r a HE Hb Ha. pose proof FH_ok as FH.
pose proof (YFgm.LYB W ly regs mu ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FH) as (ZT & T1 & _ & _ & _ & _ & ZC & C1 & _).
pose proof (YFgm.fh_Hp _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as ZP.
pose proof p_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & _).
unfold rapp_b in Hb. apply orb_true_iff in Hb as [Hb|Hb]; [apply Z.leb_le in Hb; lia|].
destruct (YP09.r_base r) as [k|] eqn:Eb; cbn [base_val] in Ha.
2:{ apply andb_true_iff in Hb as [L1 L2]. apply Z.leb_le in L1. apply Z.leb_le in L2. apply OFF_LOW. lia. }
destruct (k =? 2)%nat eqn:K2; [apply Nat.eqb_eq in K2; subst k|].
{ apply andb_true_iff in Hb as [L1 L2]. apply Z.leb_le in L1. apply Z.leb_le in L2.
rewrite (HE 2%nat ltac:(cbv; lia)), E2 in Ha. apply OFF_SP. unfold sp0. lia. }
destruct (k =? 10)%nat eqn:K10; [apply Nat.eqb_eq in K10; subst k|].
{ apply andb_true_iff in Hb as [L1 L2]. apply Z.leb_le in L1. apply Z.leb_le in L2.
rewrite (HE 10%nat ltac:(cbv; lia)), (YFgm.E10 ly regs ch pa nn hb1 q j1 j2 j3), HA0 in Ha. unfold w64 in Ha.
rewrite unsigned_lit_small in Ha by (clear - P1 P2 P5; ceil; unfold ASAN_CEIL in *; lia).
apply (OFF_Z3 (pa - 16) (YFgm.N8v nn + 16) a ZP). lia. }
destruct (k =? 32)%nat eqn:K32; [apply Nat.eqb_eq in K32; subst k|].
{ apply andb_true_iff in Hb as [L1 L2]. apply Z.leb_le in L1. apply Z.leb_le in L2.
rewrite (HE 32%nat ltac:(cbv; lia)), EaT in Ha. unfold w64 in Ha.
rewrite unsigned_lit_small in Ha by (clear - ZT T1; ceil; unfold zone3, kThreadObjSize, ASAN_CEIL in *; lia).
apply (OFF_Z3 (ly_T ly) kThreadObjSize a ZT). lia. }
destruct (k =? 33)%nat eqn:K33; [apply Nat.eqb_eq in K33; subst k|].
{ apply andb_true_iff in Hb as [L1 L2]. apply Z.leb_le in L1. apply Z.leb_le in L2.
rewrite (HE 33%nat ltac:(cbv; lia)) in Ha. change (ew E0 33) with (w64 (ly_C ly)) in Ha. unfold w64 in Ha.
rewrite unsigned_lit_small in Ha by (clear - ZC C1; ceil; unfold zone3, ASAN_CEIL in *; lia).
apply (OFF_Z3 (ly_C ly) 256 a ZC). lia. }
destruct (k =? 37)%nat eqn:K37; [apply Nat.eqb_eq in K37; subst k|]; [|discriminate Hb].
apply andb_true_iff in Hb as [L1 L2]. apply Z.leb_le in L1. apply Z.leb_le in L2.
rewrite (HE 37%nat ltac:(cbv; lia)) in Ha. change (ew E0 37) with (w64 (YFgm.IMv pa)) in Ha. unfold w64 in Ha.
rewrite unsigned_lit_small in Ha by (clear - P9; lia).
apply OFF_LOW. unfold SHADOW_OFF. lia.
Qed.
Lemma regions_off_of_b : forall (E : env) rs, (forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) ->
  forallb rapp_b rs = true -> FAR.regions_offU UP E rs.
Proof. intros E rs HE Hb r a Hr Ha. exact (rapp_off E r a HE (proj1 (forallb_forall _ _) Hb r Hr) Ha). Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. Seed transfer (mu -> real): YFgm.free_hyps on the real memory, values kept at their mu reading.              *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Lemma FH_real : YFgm.free_hyps W ly regs mem ch pa nn hb1 q j1 j2 j3 (st_internal_inited S).
Proof.
pose proof FH_ok as F. pose proof PRE as PRE'. destruct PRE' as (_ & _ & _ & _ & Hlo & _ & _ & _ & _ & _ & Hch & _).
pose proof p_facts as (P1 & P2 & P3 & P4 & P5 & _).
destruct F as [F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 F17 F18 F19 F20 F21 F22 F23].
constructor.
- exact F1.
- exact F2.
- exact F3.
- exact F4.
- exact F5.
- exact F6.
- exact F7.
- pose proof (FAR.chain_pre_real B ly S UP W regs mem md ch ARU0 ltac:(unfold ASTACK in Hlo; lia) Hch) as [_ CH].
unfold frame0_ok, spZ, s0Z in CH. exact CH.
- exact F9.
- exact F10.
- exact F11.
- exact F12.
- exact F13.
- exact F14.
- exact F15.
- intros a Ha. apply (FAR.apresent_of_unpoison _ UP _ a); [apply (OFF_Z3 (pa - 16) (YFgm.N8v nn + 16) a F9); lia | exact (F16 a Ha)].
- intros a Ha. apply (FAR.apresent_of_unpoison _ UP _ a); [exact (OFF_FSH a Ha) | exact (F17 a Ha)].
- exact F18.
- exact F19.
- destruct F20 as (I1 & I2 & I3 & I4).
assert (VL : forall a (w : nat) v, (forall k, (k < w)%nat -> 0 <= a + Z.of_nat k < SHADOW_OFF) ->
val_mem tfibsegs (mrestrict (w_H W) mu) a w v -> val_mem tfibsegs (mrestrict (w_H W) mem) a w v).
{ intros a w v Hr V. apply (FAR.val_mem_of_unpoison (w_H W) UP mem a w v); [intros k Hk; apply OFF_LOW; exact (Hr k Hk) | exact V]. }
split; [apply VL; [intros k Hk; unfold TFIB_IAL_FLAG, SHADOW_OFF; lia | exact I1]|].
split; [apply VL; [intros k Hk; unfold TFIB_IAL_FLAG, SHADOW_OFF; lia | exact I2]|].
split.
+ revert I3. destruct (st_internal_inited S); intros [I3a I3b]; split; (apply VL; [intros k Hk; unfold TFIB_IAL_W, SHADOW_OFF; lia | assumption]).
+ intros a Ha. rewrite <- (FAR.mbyte_unpoison (w_H W) UP mem a); [exact (I4 a Ha)|].
apply OFF_LOW. unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W, SHADOW_OFF in *. lia.
- exact F21.
- exact F22.
- apply (proj1 (FAR.st_ok_unpoison_iff UP E0 YFgm.SS0 (w_H W) regs (w64 (pc_wrap_free Tfib_code)) mem (YK11.seg_rom tfibsegs)
(regions_off_of_b E0 (ss_mem YFgm.SS0) (fun k _ => eq_refl) ltac:(vm_compute; reflexivity)))).
exact F23.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. Post transfers (real -> mu) for YFg1.ENQ_PRE / MID_AG.                                                        *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Lemma MEQI_u : forall m, YFgm.MEQI W ly regs mem pa m -> YFgm.MEQI W ly regs mu pa (FSP.unpoison UP m).
Proof.
intros m [MQ IP]. unfold YFgm.MEQI. split.
- intros x Hx Hz. unfold FSP.unpoison. rewrite (MQ x Hx Hz). reflexivity.
- unfold YFgm.IAL_POST in IP |- *. cbv zeta in IP |- *. destruct IP as (I1 & I2 & I3 & I4 & I5).
assert (VL : forall a (w : nat) v, (forall k, (k < w)%nat -> 0 <= a + Z.of_nat k < SHADOW_OFF) ->
val_mem tfibsegs (mrestrict (w_H W) m) a w v -> val_mem tfibsegs (mrestrict (w_H W) (FSP.unpoison UP m)) a w v).
{ intros a w v Hr V. apply (FAR.val_mem_to_unpoison (w_H W) UP m a w v); [intros k Hk; apply OFF_LOW; exact (Hr k Hk) | exact V]. }
split; [apply VL; [intros k Hk; unfold TFIB_IAL_FLAG, SHADOW_OFF; lia | exact I1]|].
split; [apply VL; [intros k Hk; unfold TFIB_IAL_FLAG, SHADOW_OFF; lia | exact I2]|].
split; [apply VL; [intros k Hk; unfold TFIB_IAL_W, SHADOW_OFF; lia | exact I3]|].
split; [apply VL; [intros k Hk; unfold TFIB_IAL_W, SHADOW_OFF; lia | exact I4]|].
intros a Ha. rewrite (FAR.mbyte_unpoison (w_H W) UP m a); [exact (I5 a Ha)|].
apply OFF_LOW. unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W, SHADOW_OFF in *. lia.
Qed.
Lemma DEPOK_u : forall z m4, aok s1 (KDepot tr) z ->
  depot_mem_ok B ly (depot_after z tr s1) (aview tfibsegs (w_H W) m4) ->
  depot_mem_ok B ly (depot_after z tr s1) (aview tfibsegs (w_H W) (FSP.unpoison UP m4)).
Proof.
intros z m4 AOK DEPOK. pose proof PRE as (_ & Hev & _).
eapply (YFfy.depot_mem_ok_agree B ly (depot_after z tr s1) (depot_after z tr s1)); [| exact (am_universe B ly S _ M) | reflexivity | | exact DEPOK].
- apply (WfP_weaken _ 1 1 1); try lia. exact (YFfl.sd_wf B ly S rd0 M z tr Hev AOK HU).
- intros a Ha. apply FAR.aview_unpoison. exact (DFP_OFF a Ha).
Qed.
Lemma CONST_u : forall m4, Forall (cell_holds B ly (aview tfibsegs (w_H W) m4)) (as_const B ly) ->
  Forall (cell_holds B ly (aview tfibsegs (w_H W) (FSP.unpoison UP m4))) (as_const B ly).
Proof.
intros m4 HC. apply Forall_forall. intros c Hc. eapply (cell_holds_agree B ly (aview tfibsegs (w_H W) m4)); [exact (proj1 (Forall_forall _ _) HC c Hc)|].
intros i Hi. apply FAR.aview_unpoison. exact (proj1 (Forall_forall _ _) CONST_OFF c Hc i Hi).
Qed.
Lemma SSE_u : forall E5 (msE : machine_state), (forall k0, (k0 < aHAVf)%nat -> ew E5 k0 = ew E0 k0) ->
  msE = YK11.mkst (ms_regs msE) (w64 A_Enqueue) (ms_mem msE) (YK11.seg_rom tfibsegs) ->
  st_ok tfibsegs E5 SS_E (restrict (w_H W) msE) ->
  st_ok tfibsegs E5 SS_E (restrict (w_H W) (YK11.mkst (ms_regs msE) (w64 A_Enqueue) (FSP.unpoison UP (ms_mem msE)) (YK11.seg_rom tfibsegs))).
Proof.
intros E5 msE HE Hsh HS.
apply (proj2 (FAR.st_ok_unpoison_iff UP E5 SS_E (w_H W) (ms_regs msE) (w64 A_Enqueue) (ms_mem msE) (YK11.seg_rom tfibsegs)
(regions_off_of_b E5 (ss_mem SS_E) HE ltac:(vm_compute; reflexivity)))).
rewrite Hsh in HS. exact HS.
Qed.
Lemma EQS_u : forall m4 mE, YFgf.EQS ly regs pa nn m4 mE -> YFgf.EQS ly regs pa nn (FSP.unpoison UP m4) (FSP.unpoison UP mE).
Proof.
intros m4 mE [Q4 QS]. unfold YFgf.EQS. split.
- intros x Hx Hs. unfold FSP.unpoison. rewrite (Q4 x Hx Hs). reflexivity.
- intros x Hs. rewrite (FAR.unpoison_offU_w UP mE x (OFF_FSH _ Hs)). exact (QS x Hs).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 4. UP's invariants across the walks.                                                                              *)
(* ---------------------------------------------------------------------------------------------------------------- *)
(* free quarantines (pa, n) only: every other live block stays live, so UP stays in live blocks. *)
Lemma OK_X : forall z, FSP.upoison_ok B ly (YFfl.S' S kk z tr) UP.
Proof.
intros z. apply (FK.upoison_ok_free B ly S ly (YFfl.S' S kk z tr) UP pa n OKU HOUT).
intros q0 m0 Hb NE. pose proof kk_facts as (Hf & Hk & Hst & Hu & Hr).
destruct (YFfl.SPLIT B ly S rd0 M kk Hk z tr) as (l1 & l2 & E & E' & _).
unfold ablocks, blocks in Hb |- *.
apply in_map_iff in Hb as ([q1 m1] & Eq & Hb). apply in_map_iff in Hb as (c & Ec & Hc). apply filter_In in Hc as [Hc Ha].
apply in_map_iff. exists (q1, m1). split; [exact Eq|]. apply in_map_iff. exists c. split; [exact Ec|]. apply filter_In. split; [|exact Ha].
rewrite E'. rewrite E in Hc. apply in_app_iff in Hc as [Hc|[<-|Hc]]; apply in_app_iff.
- left. exact Hc.
- exfalso. apply NE. cbn [fst snd] in Eq. cbn beta in Ec. injection Ec as E1 E2. rewrite <- Eq, <- E1, <- E2, Hu, Hr. reflexivity.
- right. apply in_cons. exact Hc.
Qed.
(* AR on the unpoisoned reading survives a run that keeps every byte outside a present, non-owned window. *)
Lemma AR_unpoison_frame : forall ly1 X1 (W1 : world tfibsegs) (m m' : word -> option byte) md1 md2 (P : Z -> Prop),
  AR tfibsegs B ly1 X1 W1 (FSP.unpoison UP m) md1 ->
  (forall a, P a \/ ~ P a) ->
  (forall x : word, ~ P (bv_unsigned x) -> m' x = m x) ->
  (forall a, P a -> ~ aowned B ly1 X1 a /\ apresent (w_H W1) m' a) ->
  m_vmmaps md2 = m_vmmaps md1 -> m_vm_lazy md2 = m_vm_lazy md1 -> eager_used md2 = eager_used md1 ->
  AR tfibsegs B ly1 X1 W1 (FSP.unpoison UP m') md2.
Proof.
intros ly1 X1 W1 m m' md1 md2 P HAR DEC FRm PP Ev1 Ev2 Ev3.
assert (PT : forall x : word, ~ P (bv_unsigned x) -> FSP.unpoison UP m' x = FSP.unpoison UP m x).
{ intros x Hx. unfold FSP.unpoison. destruct (FSP.in_ush UP (bv_unsigned x)); [reflexivity | exact (FRm x Hx)]. }
apply (AR_frame_law_ok tfibsegs B ly1 X1 W1 (FSP.unpoison UP m) md1 (FSP.unpoison UP m') md2 HAR).
- intros a Ha O. apply FSP.aview_at. apply PT. rewrite (FSP.wz a Ha). intros Pa. exact (proj1 (PP a Pa) O).
- intros a Hv. rewrite (FSP.aview_mod tfibsegs) in Hv |- *.
assert (Ha' : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
destruct (DEC (a mod 2 ^ 64)) as [Pa|Pa].
+ destruct (PP _ Pa) as [_ PR]. apply (FAR.apresent_to_unpoison _ UP) in PR. apply apresent_mbyte in PR as [b Hb].
unfold aview. rewrite Hb. cbn [option_map]. discriminate.
+ rewrite (FSP.aview_at tfibsegs (w_H W1) (FSP.unpoison UP m') (FSP.unpoison UP m)); [exact Hv|].
apply PT. rewrite (FSP.wz _ Ha'). exact Pa.
- exact Ev1.
- exact Ev2.
- exact Ev3.
- intros a Hb Hh. apply PT. intros Pa. destruct (PP _ Pa) as [_ [Hh' _]].
rewrite Z_to_bv_bv_unsigned in Hh'. congruence.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 5. The arms' common text (YFg2.v:277-398, YFfz.v:421-540) up to the enqueue call's return, threaded.             *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Lemma arm_prefix :
(forall z msE matE E5 (W5 : world tfibsegs) regs' mem' md' (X' : astate) nb,
 let X := YFfl.S' S kk z tr in let mdE := with_vm_backing (m_vm_lazy md) matE md in
 aok s1 (KDepot tr) z ->
 msE = YK11.mkst (ms_regs msE) (w64 A_Enqueue) (ms_mem msE) (YK11.seg_rom tfibsegs) ->
 (forall k0, (k0 < aHAVf)%nat -> ew E5 k0 = ew E0 k0) ->
 st_ok tfibsegs E5 SS_E (restrict (w_H W) msE) ->
 (forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem msE) a) ->
 AR tfibsegs B ly X W (FSP.unpoison UP (ms_mem msE)) mdE ->
 FSU.acall_postU tfibsegs B QSTACK ly X UP W (ms_regs msE) (ms_mem msE) mdE (fun _ => False) ly X' W5 regs' mem' md' ->
 st_qthread X' = qc_push (st_qthread X) kk' nb ->
 match nb with None => need_new_batch (st_qthread X) = false | Some _ => need_new_batch (st_qthread X) = true end ->
 st_chunks X' = st_chunks X -> st_qglobal X' = st_qglobal X -> st_fs X' = st_fs X ->
 (forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ ascratch B ASTACK regs a -> ~ (pa <= a < pa + nn) ->
  aview tfibsegs (w_H W) (ms_mem msE) a = aview tfibsegs (w_H W) mem a) ->
 amreal tfibsegs (maybe_drain X') W5 (cfg_at tfibsegs (raZ (ms_regs msE)) regs' mem' md') (FSU.free_leafU tfibsegs B ly S UP W regs mem md p n)) ->
amreal tfibsegs (free p tr S) W (cfg_at tfibsegs (pc_wrap_free Tfib_code) regs mem md) (FSU.free_leafU tfibsegs B ly S UP W regs mem md p n).
Proof.
intros K.
pose proof PRE as PRE'. destruct PRE' as (HAR & Hev & Hra & Hal & Hlo & Hbot & Hhi & HPRES & Hgp & Htp & Hch & HQT).
destruct HAR as (M0 & LED & BUD & MW & HSH).
pose proof kk_facts as (Hf & Hk & Hst & Hu & Hr). pose proof FH_ok as FH. pose proof FH_real as FHr.
pose proof (YFgm.LYB W ly regs mu ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FH) as LB.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
set (BODY := fun s' : astate =>
(match p with
| PNull => ret ()
| _ => s <- get;;
match find_user (st_chunks s) p with
| Some k0 =>
mcheck match ck_state k0 with CAllocated => true | CQuarantined => false end 1;;
depot_put tr;;
modify (fun s0 : astate => set_chunks (upd_chunk (st_chunks s0) {| ck_beg := ck_beg k0; ck_req := ck_req k0; ck_state := CQuarantined |}) s0);;
enqueue {| ck_beg := ck_beg k0; ck_req := ck_req k0; ck_state := CQuarantined |};; maybe_drain
| None => fail (FCheck 2)
end
end) s').
assert (SPLIT : amreal tfibsegs (BODY s1) W (cfg_at tfibsegs (pc_wrap_free Tfib_code) regs mem md) (FSU.free_leafU tfibsegs B ly S UP W regs mem md p n) ->
amreal tfibsegs (free p tr S) W (cfg_at tfibsegs (pc_wrap_free Tfib_code) regs mem md) (FSU.free_leafU tfibsegs B ly S UP W regs mem md p n)).
{ intros MAIN. unfold free. cbn [bind ret tick modify mcheck ibind get put set_nev set_internal_inited st_internal_inited].
destruct (st_internal_inited S) eqn:E; cbn [ibind ret modify].
- replace (set_nev (st_nev S + 1) S) with s1; [exact MAIN|]. unfold s1. generalize E. generalize S. clear. intros S0 E0. destruct S0; cbn in E0 |- *. subst. reflexivity.
- exact MAIN. }
apply SPLIT. clear SPLIT. subst BODY. cbn beta.
assert (PNN : p <> PNull).
{ intros Hp0. pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ WF) kk Hk) as [_ CK].
assert (HU0 : ck_user kk = PNull) by (rewrite Hu; exact Hp0). unfold ck_user in HU0. destruct (ck_beg kk); cbn in HU0; try discriminate; destruct CK. }
rewrite (match_nonnull p); [|exact PNN].
cbn [bind get ret ibind]. change (st_chunks s1) with (st_chunks S). rewrite Hf, Hst. cbn [mcheck ret ibind].
change {| ck_beg := ck_beg kk; ck_req := ck_req kk; ck_state := CQuarantined |} with kk'.
unfold depot_put. cbn [bind askz ibind].
apply amreal_ask_depot.
unfold cfg_at. rewrite <- (wvb_self md) at 1.
eapply SRr_bind; [exact (YFgb.segA W ly regs mem md ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) (m_vm_materialized md) FHr)|].
intros W1 c1 _ HU1.
eapply SRr_bind; [exact (YFgd.segB W ly regs mem md ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FHr W1 c1 HU1)|].
clear HU1. intros W2 c2 _ (-> & msD & matD & E3 & -> & HshD & HEn3 & HS & MEQD & TRQ & PRESD).
rewrite HshD. eapply SRr_bind.
{ assert (AGD : forall a, ~ YFgm.WIN ly regs pa a -> ~ YFgm.IZONE a -> 0 <= a < 2 ^ 64 ->
aview tfibsegs (w_H W) (ms_mem msD) a = aview tfibsegs (w_H W) mem a).
{ intros a Hw Hz Ha. apply aview_same. apply (proj1 MEQD); rewrite unsigned_lit_small by exact Ha; assumption. }
rreg HS (2%bv : bv 5) R2. rewrite (HEn3 2%nat ltac:(cbv; lia)), E2 in R2.
pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
apply (D1 W ly s1 (ms_regs msD) (ms_mem msD) _ (sp0 - 2112) tr LO IMG s1_wf (tr_admit_len _ _ _ (am_universe B ly S _ M) HU)).
-
apply Forall_forall. intros c Hc. eapply (cell_holds_agree B ly (aview tfibsegs (w_H W) mu)).
+ exact (proj1 (Forall_forall _ _) (am_const B ly S _ M) c Hc).
+ intros i Hi. destruct (proj1 (Forall_forall _ _) CONST_OUT c Hc i Hi) as (X1 & X2 & X3). rewrite (AGD _ X1 X2 X3).
symmetry. apply FAR.aview_unpoison. exact (proj1 (Forall_forall _ _) CONST_OFF c Hc i Hi).
-
assert (DM : depot_mem_ok B ly S (aview tfibsegs (w_H W) mu)).
{ split; [|split].
- apply Forall_forall. intros c Hc. apply (proj1 (Forall_forall _ _) (am_cells B ly S _ M)). unfold acells. rewrite !in_app_iff. tauto.
- exact (am_depot B ly S _ M).
- pose proof (am_junk B ly S _ M) as J. pose proof (am_areas B ly S _ M) as A. rewrite Forall_forall in J, A.
repeat apply Forall_cons; try apply Forall_nil;
first [ apply J; unfold ajunk; do 2 right; repeat (apply in_or_app; first [ left; inlist | right ]); inlist
| apply A; unfold aareas; repeat (apply in_or_app; first [ left; inlist | right ]); inlist ]. }
eapply (YFfy.depot_mem_ok_agree B ly S s1); [exact (am_wf B ly S _ M) | exact (am_universe B ly S _ M) | reflexivity | | exact DM].
intros a Ha. destruct (DFP_OUT a Ha) as (X1 & X2 & X3). rewrite (AGD a X1 X2 (DFP_RANGE a Ha)).
symmetry. apply FAR.aview_unpoison. exact (DFP_OFF a Ha).
- rreg HS (10%bv : bv 5) R; rewrite R, (HEn3 2%nat ltac:(cbv; lia)), E2. unfold sp0; f_equal; lia.
- rreg HS (11%bv : bv 5) R; rewrite R, (HEn3 36%nat ltac:(cbv; lia)), EaLEN. reflexivity.
- rreg HS (3%bv : bv 5) R; rewrite R, (HEn3 3%nat ltac:(cbv; lia)), (YFgm.Er ly regs ch pa nn hb1 q j1 j2 j3 3 3%bv eq_refl). exact Hgp.
- rreg HS (4%bv : bv 5) R; rewrite R. rewrite (ts_tp _ TB) in Htp. reflexivity.
- rreg HS (1%bv : bv 5) R; rewrite R. apply YK0s.ret_ok_even. reflexivity.
- intros i Hi. apply (TRQ i Hi).
- unfold sp0. replace (bv_unsigned (YK11.getr regs 2) - 2112) with (bv_unsigned (YK11.getr regs 2) + (-264) * 8) by lia. rewrite Z_mod_plus_full.
apply (mod0_factor _ 8 2); [lia|]. exact Hal.
- unfold spZ, ASTACK in *; unfold sp0; lia.
-   unfold spZ, ASTACK in *; unfold sp0; lia.
- right. rewrite R2. unfold w64. rewrite unsigned_lit_small by (unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, ASTACK, kHighMemBeg, kHighMemEnd in *; lia). unfold sp0; lia.
- rewrite R2. unfold w64. rewrite unsigned_lit_small by (unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, ASTACK, kHighMemBeg, kHighMemEnd in *; lia).
replace (bv_unsigned (YK11.getr regs 2) + -2176) with (bv_unsigned (YK11.getr regs 2) + (-136) * 16) by lia. rewrite Z_mod_plus_full. exact Hal.
- rewrite R2. unfold w64. rewrite unsigned_lit_small by (unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, ASTACK, kHighMemBeg, kHighMemEnd in *; lia). unfold spZ, ASTACK, DEP_STK in *; lia.
- rewrite R2. unfold w64. rewrite unsigned_lit_small by (unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, ASTACK, kHighMemBeg, kHighMemEnd in *; lia). unfold spZ in *; lia.
- intros a Ha. rewrite R2 in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, ASTACK, kHighMemBeg, kHighMemEnd in *; lia).
apply PRESD. unfold DEP_STK, ASTACK, sp0 in *. lia. }
intros W3 c3 _ (-> & z & regs4 & mem4 & mat4 & -> & AOK & HP4 & Hfr4 & Hpr4 & DEPOK & HC4). srr_norm_model.
apply SRr_ret. exists z. split; [exact AOK|].
rreg HS (1%bv : bv 5) Q1r. rreg HS (2%bv : bv 5) Q2.
rewrite Q2, (HEn3 2%nat ltac:(cbv; lia)), E2 in Hfr4.
pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
rewrite unsigned_lit_small in Hfr4 by (unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, ASTACK, kHighMemBeg, kHighMemEnd in *; lia). fold sp0 in Hfr4.
assert (Hfr4' : forall x : word, ~ (sp0 - 2176 - DEP_STK <= bv_unsigned x < sp0 - 2176) -> ~ depot_footprint B ly (bv_unsigned x) -> mem4 x = ms_mem msD x).
{ intros x Hx Hd. apply Hfr4; [clear - Hx; lia | exact Hd]. }
assert (DZ : forall x : word, ~ (sp0 - 2176 - DEP_STK <= bv_unsigned x < sp0 - 2176) -> ~ YFgm.DZONE ly (bv_unsigned x) -> mem4 x = ms_mem msD x).
{ intros x Hx Hd. apply Hfr4'; [exact Hx|]. intros Hf'. apply Hd. exact (proj2 (proj2 (DFP_OUT _ Hf'))). }
assert (TAIL : let sd := depot_after z tr s1 in
amreal tfibsegs ((modify (fun s0 : astate => set_chunks (upd_chunk (st_chunks s0) kk') s0);; enqueue kk';; maybe_drain) sd)
W (mkCfg (YK11.mkst regs4 (YK11.getr (ms_regs msD) 1) mem4 (YK11.seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat4 md))
(FSU.free_leafU tfibsegs B ly S UP W regs mem md p n)).
{ cbn zeta. apply amreal_mbind. cbn [modify amreal]. apply SRr_ret. cbn [fst snd].
change (set_chunks (upd_chunk (st_chunks (depot_after z tr s1)) kk') (depot_after z tr s1)) with (YFfl.S' S kk z tr).
set (X := YFfl.S' S kk z tr).
apply amreal_mbind. cbn beta.
rewrite Q1r. apply amreal_after_SRr. eapply SRr_mono.
{ apply (YFgf.segCm1 W ly regs mem md ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FHr msD E3 regs4 mem4 mat4).
split; [exact HshD|]. split; [exact HEn3|]. split; [exact HS|]. split; [exact HP4|]. split; [exact DZ|]. split; [exact Hpr4|]. split; [exact MEQD | exact PRESD]. }
intros W4 c4 _ (-> & msE & matE & E5 & -> & HshE & HEn5 & HS5 & EQE & PRESE).
(* The run's posts on the real memory, moved to mu (YFg1.ENQ_PRE is applied unchanged there). *)
pose proof (MEQI_u (ms_mem msD) MEQD) as MEQDu.
assert (Hfr4u : forall x : word, ~ (sp0 - 2176 - DEP_STK <= bv_unsigned x < sp0 - 2176) -> ~ depot_footprint B ly (bv_unsigned x) ->
FSP.unpoison UP mem4 x = FSP.unpoison UP (ms_mem msD) x).
{ intros x Hx Hd. unfold FSP.unpoison. rewrite (Hfr4' x Hx Hd). reflexivity. }
pose proof (EQS_u mem4 (ms_mem msE) EQE) as EQEu.
pose proof (ENQ_PRE z (YK11.mkst (ms_regs msD) (w64 A_StackDepotPut) (FSP.unpoison UP (ms_mem msD)) (YK11.seg_rom tfibsegs)) (FSP.unpoison UP mem4)
(YK11.mkst (ms_regs msE) (w64 A_Enqueue) (FSP.unpoison UP (ms_mem msE)) (YK11.seg_rom tfibsegs)) matE E5 AOK MEQDu Hfr4u
(DEPOK_u z mem4 AOK DEPOK) (CONST_u mem4 HC4) eq_refl HEn5 (SSE_u E5 msE HEn5 HshE HS5) EQEu
(fun a Ha => FAR.apresent_to_unpoison _ UP _ a (PRESE a Ha))) as EP.
pose proof (proj1 EP) as ARX.
(* UP's shadow bytes are outside every write window of the run (the region condition). *)
assert (UNCH : forall s, FSP.in_ush UP s = true -> ms_mem msE (Z_to_bv 64 s) = mem (Z_to_bv 64 s)).
{ intros s Hs. pose proof (FSP.ush_range tfibsegs B ly S UP W mem md s ARU0 Hs) as Rs.
assert (Ux : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit_small; exact Rs).
assert (NOT : forall P : Z -> Prop, (forall a, P a -> FAR.offU UP a) -> ~ P s) by (intros P HP X0; exact (ush_not_off s Hs (HP s X0))).
rewrite (proj1 EQE (Z_to_bv 64 s)); rewrite ?Ux; [| apply (NOT _ OFF_WIN2) | apply (NOT _ OFF_FSH)].
rewrite (Hfr4' (Z_to_bv 64 s)); rewrite ?Ux; [| apply (NOT _ OFF_DEPSTK) | apply (NOT _ DFP_OFF)].
apply (proj1 MEQD); rewrite ?Ux; [apply (NOT _ OFF_WIN) | apply (NOT _ OFF_IZONE)]. }
assert (EPU : FK.enq_preU B ly X UP W (ms_regs msE) (ms_mem msE) (with_vm_backing (m_vm_lazy md) matE md) kk').
{ unfold FK.enq_preU. split; [exact EP|]. split; [exact (OK_X z)|].
apply (FAR.upoisoned_keep UP W W mem (ms_mem msE) POU). intros s Hs. apply FSP.aview_at. exact (UNCH s Hs). }
rewrite HshE at 1. change (mkCfg (YK11.mkst (ms_regs msE) (w64 A_Enqueue) (ms_mem msE) (YK11.seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) matE md))
with (cfg_at tfibsegs A_Enqueue (ms_regs msE) (ms_mem msE) (with_vm_backing (m_vm_lazy md) matE md)).
eapply amreal_mono; [| exact (Q1 ly X UP W (ms_regs msE) (ms_mem msE) (with_vm_backing (m_vm_lazy md) matE md) kk' ltac:(subst X; rewrite (YFfl.S'_qthread S kk z tr); reflexivity) EPU)].
intros [[] X'] W5 c5 (regs' & mem' & md' & nb & -> & POST & HQ' & Hnb & HCK' & HQG' & HFS' & _). cbn [fst snd] in HQ', POST, HCK', HQG', HFS' |- *.
apply (K z msE matE E5 W5 regs' mem' md' X' nb AOK HshE HEn5 HS5 PRESE ARX POST HQ' Hnb HCK' HQG' HFS').
intros a Ha NO NS NB. pose proof (FAR.offU_not_owned B ly S UP W mem md a ARU0 Ha NO) as Oa.
rewrite <- (FAR.aview_unpoison (w_H W) UP (ms_mem msE) a Oa), <- (FAR.aview_unpoison (w_H W) UP mem a Oa).
apply (MID_AG (YK11.mkst (ms_regs msD) (w64 A_StackDepotPut) (FSP.unpoison UP (ms_mem msD)) (YK11.seg_rom tfibsegs)) (FSP.unpoison UP mem4) (FSP.unpoison UP (ms_mem msE)) MEQDu Hfr4u EQEu a Ha). intros HD.
destruct (YFfl.D_owned B TB ly S rd0 (aview tfibsegs (w_H W) (FSP.unpoison UP (ms_mem msE))) M kk hb1 Hk HB1 z tr sp0 (conj Hlo Hhi) IMG (proj1 ARX) a (proj1 Ha) HD) as [O|[O|O]].
- exact (NO O).
- destruct (YFfl.owned_S' B ly S rd0 M kk Hk z tr a O) as [O'|O']; [exact (NO O')|]. apply NB. rewrite Hu, <- Enn in O'. exact O'.
- apply NS. unfold ascratch. left. exact O. }
destruct AOK as [-> | [-> _]].
- cbn [Z.eqb ret ibind]. exact TAIL.
- cbn [Z.eqb bind get ret ibind].
destruct (depot_ids s1 + 1 <? kDepotIdsPerBlock); cbn [mcheck ret ibind]; [|exact I].
destruct (kStartFramesMax + depot_frames s1 + Z.of_nat (length tr) + 1 <? kStoreFramesPerBlock); cbn [mcheck ret put ibind]; [|exact I].
exact TAIL.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 6. free that needs no drain (lib/B/YFg2.v).                                                                       *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Section mid.
Hypothesis NODRAIN : qc_bytes (st_qthread S) + nn + (if need_new_batch (st_qthread S) then kBatchBytes else 0) <= kQuarantineCacheMax.
(* lib/B/YFg2.v:93 TAILM, any UP. *)
Lemma TAILMU : forall z msE matE E5 (W5 : world tfibsegs) regs' mem' md' (X' : astate) nb,
let X := YFfl.S' S kk z tr in let mdE := with_vm_backing (m_vm_lazy md) matE md in
aok s1 (KDepot tr) z ->
msE = YK11.mkst (ms_regs msE) (w64 A_Enqueue) (ms_mem msE) (YK11.seg_rom tfibsegs) ->
(forall k0, (k0 < aHAVf)%nat -> ew E5 k0 = ew E0 k0) ->
st_ok tfibsegs E5 SS_E (restrict (w_H W) msE) ->
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem msE) a) ->
AR tfibsegs B ly X W (FSP.unpoison UP (ms_mem msE)) mdE ->
FSU.acall_postU tfibsegs B QSTACK ly X UP W (ms_regs msE) (ms_mem msE) mdE (fun _ => False) ly X' W5 regs' mem' md' ->
st_qthread X' = qc_push (st_qthread X) kk' nb ->
match nb with None => need_new_batch (st_qthread X) = false | Some _ => need_new_batch (st_qthread X) = true end ->
st_chunks X' = st_chunks X -> st_qglobal X' = st_qglobal X ->
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ ascratch B ASTACK regs a -> ~ (pa <= a < pa + nn) ->
aview tfibsegs (w_H W) (ms_mem msE) a = aview tfibsegs (w_H W) mem a) ->
SRr tfibsegs W5 (cfg_at tfibsegs PC_PUT_ENQ_RA regs' mem' md') (FSU.free_leafU tfibsegs B ly S UP W regs mem md p n (tt, X')).
Proof.
intros z msE matE E5 W5 regs' mem' md' X' nb X mdE AOK HshE HEn5 HS PRESE ARX ((ARX' & LLE & WLE & CS & SIO & FR & PRS) & OKX' & POX') HQ' Hnb HCK' HQG' AGP.
pose proof PRE as PRE'. destruct PRE' as (HAR & Hev & Hra & Hal & Hlo & Hbot & Hhi & HPRES & Hgp & Htp & Hch & HQT). destruct HAR as (M0 & LED & BUD & MW & HSH).
pose proof kk_facts as (Hf & Hk & Hst & Hu & Hr). pose proof HSP as HSP'. pose proof FH_ok as FH.
pose proof (YFgm.LYB W ly regs mu ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FH) as LB.
pose proof p_facts as (P1 & P2 & _). pose proof QB_facts as (Qa & Qb & Q8).
pose proof Hwx_tfa as Hwx. assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
rreg HS (2%bv : bv 5) Q2. rewrite (HEn5 2%nat ltac:(cbv; lia)), E2 in Q2.
assert (SPE : spZ (ms_regs msE) = sp0 - 2208).
{ unfold spZ. rewrite Q2. unfold sp0, w64. rewrite unsigned_lit_small by (clear - Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK in *; unfold sp0 in *; lia). reflexivity. }
unfold ascratch in FR. rewrite SPE in FR, PRS.
assert (BV2 : bv_unsigned (ew E5 2) = sp0) by (rewrite (HEn5 2%nat ltac:(cbv; lia)), E2; reflexivity).
assert (NOWN : forall a, sp0 - ASTACK <= a < sp0 -> ~ aowned B ly X a /\ ~ aowned B ly X' a).
{ intros a Ha. split.
- apply (AR_stack_law_ok tfibsegs B ly X W (FSP.unpoison UP (ms_mem msE)) mdE a ARX). clear - Ha Hlo Hhi. unfold spZ, ASTACK in *. unfold sp0 in *. lia.
- apply (AR_stack_law_ok tfibsegs B ly X' W5 (FSP.unpoison UP mem') md' a ARX'). clear - Ha Hlo Hhi. unfold spZ, ASTACK in *. unfold sp0 in *. lia. }
assert (AGS : forall a, sp0 - 2208 <= a < sp0 -> aview tfibsegs (w_H W5) mem' a = aview tfibsegs (w_H W) (ms_mem msE) a).
{ intros a Ha. destruct (NOWN a ltac:(clear - Ha; unfold ASTACK; lia)) as [N1 N2].
pose proof (OFF_SP a ltac:(clear - Ha; unfold ASTACK; lia)) as Oa.
rewrite <- (FAR.aview_unpoison (w_H W5) UP mem' a Oa), <- (FAR.aview_unpoison (w_H W) UP (ms_mem msE) a Oa).
apply FR; [clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK in *; unfold sp0 in *; lia | exact N1 | exact N2 | | intros []].
unfold ascratch. rewrite (ts_errno _ TB). unfold TFIB_ERRNO, QSTACK. clear - Ha Hlo LB. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK in *. unfold sp0 in *. lia. }
assert (HP : regs_preserved (ms_regs msE) regs') by (intros r Hr'; apply CS; exact Hr').
lazymatch type of HS with st_ok _ _ ?ss ?ms0 =>
let m := eval vm_compute in (ss_mem ss) in
lazymatch m with ?r0 :: ?r1 :: ?r2 :: ?r3 :: ?r4 :: ?rest =>
pose proof (st_ok_after_call tfibsegs 112 E5 ss ms0 regs' (mrestrict (w_H W5) mem') (trim_lo r0 (-2208) :: r1 :: r2 :: r4 :: nil) PC_PUT_ENQ_RA HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(apply submem_keep; [apply subregion_trim_lo|]; apply submem_keep; [apply subregion_refl|]; apply submem_keep; [apply subregion_refl|];
apply submem_drop; apply submem_keep; [apply subregion_refl|]; apply submem_nil)
ltac:(vm_compute; reflexivity) HP) as HS1;
let rsv := eval vm_compute in (trim_lo r0 (-2208) :: r1 :: r2 :: r4 :: nil) in
change (trim_lo r0 (-2208) :: r1 :: r2 :: r4 :: nil) with rsv in HS1;
let ss2 := eval vm_compute in (ss_after_call ss rsv 112 PC_PUT_ENQ_RA) in
change (ss_after_call ss rsv 112 PC_PUT_ENQ_RA) with ss2 in HS1
end
end.
cbn [ms_mem restrict] in HS1.
lazymatch type of HS1 with Forall _ ?L -> _ =>
assert (KEPT : Forall (region_kept tfibsegs E5 (mrestrict (w_H W) (ms_mem msE)) (mrestrict (w_H W5) mem')) L);
[ repeat apply Forall_cons; try apply Forall_nil;
(apply kept_of_aview; cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; rewrite BV2;
[ intros a Ha; apply AGS; clear - Ha; lia
| intros a Ha; split; [apply AGS; clear - Ha; lia | clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK, TFIB_IMG_END in *; unfold sp0 in *; lia] ])
| specialize (HS1 KEPT); clear KEPT ]
end.
set (En6 := havoc E5 112 (map (YK11.getr regs') CLOB)) in HS1.
assert (HEn6 : forall k0, (k0 < aHAVf)%nat -> ew En6 k0 = ew E0 k0) by (intros k0 Hk0; subst En6; unfold aHAVf in Hk0; rewrite ew_havoc_old by lia; apply HEn5; exact Hk0).
assert (QB' : qc_bytes (st_qthread X') = QBFv).
{ rewrite HQ'. subst X. rewrite (YFfl.S'_qthread S kk z tr) in Hnb |- *. unfold YFgm.QBFv. change (st_qthread S) with q in *.
destruct nb; rewrite Hnb; cbn [qc_push qc_bytes]; change (ck_n kk') with (ck_n kk); rewrite <- Enn; lia. }
assert (RV : val_mem tfibsegs (mrestrict (w_H W5) mem') (ly_T ly + (t_qc + 24)) (N.to_nat 8) QBFv).
{ rewrite <- QB'. destruct ARX' as (MX' & _).
assert (C : cell_holds B ly (aview tfibsegs (w_H W5) (FSP.unpoison UP mem')) (z8 (aoff (AT t_qc) 24) (qc_bytes (st_qthread X')))).
{ apply (proj1 (Forall_forall _ _) (am_cells B ly X' _ MX')). unfold acells. rewrite !in_app_iff. do 4 right. left. unfold quar_cells, qc_cells. cbn. tauto. }
apply (FAR.val_mem_of_unpoison (w_H W5) UP mem').
{ intros k0 Hk0. apply (OFF_Z3 (ly_T ly) kThreadObjSize _ (proj1 LB)). change (N.to_nat 8) with 8%nat in Hk0. unfold t_qc, kThreadObjSize. lia. }
replace (ly_T ly + (t_qc + 24)) with (aeval B ly (aoff (AT t_qc) 24)) by (cbn; lia).
exact (cell_holds_val_mem B ly (w_H W5) (FSP.unpoison UP mem') _ 8 (ANum (qc_bytes (st_qthread X'))) C). }
apply (st_ok_add_region _ _ _ (YP09.mkRegion (Some 32%nat) (t_qc + 24) (t_qc + 32) 0 0 [YP09.mkChunk (t_qc + 24) (CVal 8 (SOff 50%nat 0))])) in HS1;
[ | reflexivity
| unfold YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem];
rewrite (HEn6 32%nat ltac:(cbv; lia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; lia);
split; [clear - LB; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, t_qc in *; lia|]; split; [clear - LB; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, t_qc in *; lia|]; split; [intros o Ho; lia|];
apply Forall_cons; [|apply Forall_nil];
eapply (chunk_ok_val tfibsegs En6 _ _ _ 8 (SOff 50%nat 0) QBFv);
[ cbn [sv_denot]; rewrite (HEn6 50%nat ltac:(cbv; lia)), EaQBF; unfold w64; rewrite Zbv_add_unsigned; f_equal; lia
| clear - Qa Qb Q8; unfold YFgm.QBFv, YFgm.QBMAX, kQuarantineCacheMax, kBatchBytes in *; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); destruct (need_new_batch q); lia
| cbn; lia | exact RV ]
| cbn [all_disjoint ss_mem]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite ?(HEn6 32%nat ltac:(cbv; lia)), ?(HEn6 2%nat ltac:(cbv; lia)), ?EaT, ?E2; unfold w64; rewrite unsigned_lit_small by (clear - LB; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; lia);
fold sp0; pose proof (YFgm.stack_ivs W ly regs mu ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FH) as (IT & _);
clear - IT LB; unfold kThreadObjSize, t_qc, ASTACK in *; repeat split; lia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
rewrite <- (restrict_mkst_fx (w_H W5)) in HS1. rename HS1 into HS'. clear HS. rename HS' into HS.
unfold cfg_at. rewrite <- (wvb_self md') at 1. change (w64 PC_PUT_ENQ_RA) with (Z_to_bv 64 PC_PUT_ENQ_RA).
srr_run_sh tfibtbl_rtF_ok HS.
rename HF into HF0. clear HFr.
srr_branch_sh tfibtbl_rtF_ok HS.
{ exfalso. match goal with H : branch_taken _ _ _ = true |- _ => rewrite branch_ltu_U in H; apply Z.ltb_lt in H; revert H end.
rewrite !U_zev by reflexivity. cbn [zev zalu_raw]. unfold rho_of. rewrite (HEn6 50%nat ltac:(cbv; lia)), EaQBF, Z.add_0_r.
unfold w64. rewrite unsigned_lit_small by (clear - Qa Qb Q8; unfold YFgm.QBFv, YFgm.QBMAX, kQuarantineCacheMax, kBatchBytes in *; destruct (need_new_batch q); lia).
rewrite !zcanon_id by (clear - Qa Qb Q8; unfold YFgm.QBFv, YFgm.QBMAX, kQuarantineCacheMax, kBatchBytes, M64 in *; destruct (need_new_batch q); lia).
pose proof NODRAIN as ND. change (st_qthread S) with q in ND. clear - ND. unfold YFgm.QBFv, kQuarantineCacheMax, kBatchBytes in *.
destruct (need_new_batch q); lia. }
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_sh tfibtbl_rtF_ok HS.
lazymatch type of HS with st_ok _ ?E _ (restrict _ ?msx) => set (En7 := E) in HS; rename msx into msR end.
assert (HEn7 : forall k0, (k0 < aHAVf)%nat -> ew En7 k0 = ew E0 k0) by (intros k0 Hk0; subst En7; unfold aHAVf in Hk0; rewrite ?ew_havoc_old by lia; apply HEn6; exact Hk0).
assert (FRT : forall x : word, ~ (sp0 - 2208 <= bv_unsigned x < sp0 - 2128) -> ~ (sp0 - 64 <= bv_unsigned x < sp0) -> ms_mem msR x = mem' x).
{ intros x Hx1 Hx2. rewrite (HF x); [apply (HF0 x)|].
all: intros Hw; destruct (in_wrange_windows _ _ _ Hw) as (b & lo & hi & Hin & Hrg);
lazymatch type of Hin with In _ (windows ?rs) => let ws := eval vm_compute in (windows rs) in change (windows rs) with ws in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [Hin|Hin];
[ injection Hin as <- <- <-; cbn [fst snd base_val] in Hrg; rewrite ?(HEn6 2%nat ltac:(cbv; lia)), ?E2, ?(HEn6 32%nat ltac:(cbv; lia)), ?EaT in Hrg; unfold w64 in Hrg;
rewrite ?unsigned_lit_small in Hrg by (clear - LB; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; lia); clear - Hx1 Hx2 Hrg; unfold ASTACK, t_qc in *; unfold sp0 in *; lia |]);
destruct Hin. }
clear HF HFr HF0.
assert (PRES' : forall a, sp0 - ASTACK <= a < sp0 -> ~ (sp0 - 2208 <= a < sp0 - 2128) -> ~ (sp0 - 64 <= a < sp0) -> apresent (w_H W5) mem' a).
{ intros a Ha N1 N2. pose proof (OFF_SP a Ha) as Oa.
destruct (Z_lt_le_dec a (sp0 - 2208)) as [L|L]; [destruct (Z_lt_le_dec a (sp0 - 2208 - QSTACK)) as [L2|L2]|].
2:{ apply (FAR.apresent_of_unpoison _ UP _ a Oa). apply PRS. clear - L L2. unfold QSTACK in *. lia. }
all: assert (EQa : aview tfibsegs (w_H W5) mem' a = aview tfibsegs (w_H W) (ms_mem msE) a)
by (destruct (NOWN a Ha) as [M1 M2];
rewrite <- (FAR.aview_unpoison (w_H W5) UP mem' a Oa), <- (FAR.aview_unpoison (w_H W) UP (ms_mem msE) a Oa);
apply FR; [clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK in *; unfold sp0 in *; lia | exact M1 | exact M2 | | intros []];
unfold ascratch; rewrite (ts_errno _ TB); unfold TFIB_ERRNO; first [clear - Ha L L2 N1 N2 Hlo LB | clear - Ha L N1 N2 Hlo LB]; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK, QSTACK in *; unfold sp0 in *; lia).
all: pose proof (PRESE a Ha) as P; apply apresent_mbyte in P as [b Hb];
assert (A : aview tfibsegs (w_H W) (ms_mem msE) a = Some (bv_unsigned b)) by (unfold aview; rewrite Hb; reflexivity);
rewrite <- EQa in A; apply aview_some in A as (b' & Hb' & _);
exact (mbyte_high_apresent (w_H W5) mem' a b' ltac:(clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK, TFIB_IMG_END in *; unfold sp0 in *; lia) Hb'). }
assert (PRESR : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W5) (ms_mem msR) a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 2208)) as [L1|L1]; [|destruct (Z_lt_le_dec a (sp0 - 2176)) as [L2|L2]; [|destruct (Z_lt_le_dec a (sp0 - 2128)) as [L3|L3]; [|destruct (Z_lt_le_dec a (sp0 - 64)) as [L4|L4]]]].
- apply (apresent_same (w_H W5) mem'); [apply FRT; rewrite unsigned_lit_small by (clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK in *; unfold sp0 in *; lia); clear - L1; lia | apply PRES'; [exact Ha | clear - L1; lia | clear - L1; lia]].
- eapply (st_ok_window_apresent (w_H W5) En7 _ _ 1 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn7 2%nat ltac:(cbv; lia)), E2; clear - L1 L2; unfold sp0; lia | clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK, TFIB_IMG_END in *; unfold sp0 in *; lia].
- eapply (st_ok_window_apresent (w_H W5) En7 _ _ 3 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn7 2%nat ltac:(cbv; lia)), E2; clear - L2 L3; unfold sp0; lia | clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK, TFIB_IMG_END in *; unfold sp0 in *; lia].
- apply (apresent_same (w_H W5) mem'); [apply FRT; rewrite unsigned_lit_small by (clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK in *; unfold sp0 in *; lia); clear - L3 L4; lia | apply PRES'; [exact Ha | clear - L3 L4; lia | clear - L3 L4; lia]].
- eapply (st_ok_window_apresent (w_H W5) En7 _ _ 4 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn7 2%nat ltac:(cbv; lia)), E2; clear - L4 Ha; unfold sp0; lia | clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK, TFIB_IMG_END in *; unfold sp0 in *; lia]. }
eapply (SRr_ret_at tfibsegs tfibtbl_rtF tfibtbl_rtF_ok Hwx W5 En7); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'.
rreg HS (1%bv : bv 5) Q1f. rewrite (HEn7 1%nat ltac:(cbv; lia)), (YFgm.E1 ly regs ch pa nn hb1 q j1 j2 j3) in Q1f.
exists ly, (ms_regs msR), (ms_mem msR), (with_vm_backing (m_vm_lazy md') mat' md'). split.
{ unfold cfg_at, raZ, w64. rewrite Q1f, Z_to_bv_bv_unsigned. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split.
2:{
pose proof (qmeter_tight _ HQT) as (T1 & T2 & T3). pose proof (YFfl.quar_S' B ly S rd0 M kk Hk Hst z tr) as [QX1 QX2].
pose proof (unq_push X X' kk' nb HCK' HQ' HQG' ltac:(intros ->; exact Hnb)) as UQ. unfold unq in UQ.
cbn [snd]. unfold qtight. rewrite QB', HQG'. split; [|split].
- clear - NODRAIN. unfold YFgm.QBFv. change (st_qthread S) with q in NODRAIN. destruct (need_new_batch q); unfold kBatchBytes in *; lia.
- subst X. rewrite (YFfl.S'_qglobal S kk z tr). exact T2.
- assert (QE : quar_n X' = quar_n X) by (unfold quar_n; rewrite HCK'; reflexivity).
change (ck_n kk') with (ck_n kk) in UQ. subst X. clear - QX1 QX2 UQ QE T3. lia. }
assert (AGT : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2208 <= a < sp0 - 2128) -> ~ (sp0 - 64 <= a < sp0) -> aview tfibsegs (w_H W5) (ms_mem msR) a = aview tfibsegs (w_H W5) mem' a).
{ intros a Ha N1 N2. apply aview_same. apply FRT; rewrite unsigned_lit_small by exact Ha; assumption. }
assert (PNN : p <> PNull).
{ intros Hp0. pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ WF) kk Hk) as [_ CK].
assert (HU0 : ck_user kk = PNull) by (rewrite Hu; exact Hp0). unfold ck_user in HU0. destruct (ck_beg kk); cbn in HU0; try discriminate; destruct CK. }
pose proof (lo_top ly LO) as (_ & _ & _ & _ & _ & _ & TL7).
split; [|split; [exact OKX'|]].
2:{ apply (FAR.upoisoned_keep UP W5 W5 mem' (ms_mem msR) POX'). intros s Hs.
pose proof (ush_low s Hs) as [Ls1 Ls2]. pose proof (FSP.ush_range tfibsegs B ly S UP W mem md s ARU0 Hs) as Rs.
apply AGT; [exact Rs | |]; intros Hw; clear - Hw Ls2 Hlo TL7; unfold spZ, ASTACK in *; unfold sp0 in *; lia. }
split; [|split; [apply layout_le_refl | split; [exact WLE | split; [|split; [|split]]]]].
-
apply (AR_unpoison_frame ly X' W5 mem' (ms_mem msR) md' _ (fun a => (sp0 - 2208 <= a < sp0 - 2128) \/ (sp0 - 64 <= a < sp0)) ARX').
+ intros a0. cbv beta. destruct (Z_lt_le_dec a0 (sp0 - 2208)); [right; lia|]. destruct (Z_lt_le_dec a0 (sp0 - 2128)); [left; left; lia|].
destruct (Z_lt_le_dec a0 (sp0 - 64)); [right; lia|]. destruct (Z_lt_le_dec a0 sp0); [left; right; lia | right; lia].
+ intros x Hx. cbv beta in Hx. apply FRT; intros Hw; apply Hx; [left | right]; exact Hw.
+ intros a Ha. cbv beta in Ha. split; [exact (proj2 (NOWN a ltac:(clear - Ha; unfold ASTACK; lia))) | apply PRESR; clear - Ha; unfold ASTACK; lia].
+ reflexivity.
+ reflexivity.
+ reflexivity.
-
intros r Hr'. unfold acallee_saved in Hr'.
assert (R : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
clear Hr'. rewrite (ts_tp _ TB) in Htp.
repeat match type of R with _ \/ _ => destruct R as [R|R] end; subst r;
[ cs_case HS HEn7 Htp (2%bv : bv 5) | cs_case HS HEn7 Htp (3%bv : bv 5) | cs_case HS HEn7 Htp (4%bv : bv 5) | cs_case HS HEn7 Htp (8%bv : bv 5) | cs_case HS HEn7 Htp (9%bv : bv 5)
| cs_case HS HEn7 Htp (18%bv : bv 5) | cs_case HS HEn7 Htp (19%bv : bv 5) | cs_case HS HEn7 Htp (20%bv : bv 5) | cs_case HS HEn7 Htp (21%bv : bv 5) | cs_case HS HEn7 Htp (22%bv : bv 5)
| cs_case HS HEn7 Htp (23%bv : bv 5) | cs_case HS HEn7 Htp (24%bv : bv 5) | cs_case HS HEn7 Htp (25%bv : bv 5) | cs_case HS HEn7 Htp (26%bv : bv 5) | cs_case HS HEn7 Htp (27%bv : bv 5) ].
-
clear - SIO. unfold same_io in SIO |- *. destruct md, md'. cbn in SIO |- *.
intuition congruence.
-
intros a Ha NO NO' NS NE. pose proof (FAR.offU_not_owned B ly S UP W mem md a ARU0 Ha NO) as Oa.
rewrite (FAR.aview_unpoison (w_H W5) UP (ms_mem msR) a Oa), (FAR.aview_unpoison (w_H W) UP mem a Oa).
rewrite AGT; [| exact Ha | intros Hs; apply NS; unfold ascratch; left; clear - Hs; unfold spZ, ASTACK; unfold sp0 in *; lia | intros Hs; apply NS; unfold ascratch; left; clear - Hs; unfold spZ, ASTACK; unfold sp0 in *; lia].
rewrite <- (FAR.aview_unpoison (w_H W5) UP mem' a Oa).
rewrite FR; [| exact Ha | | exact NO' | | intros []].
+ rewrite (FAR.aview_unpoison (w_H W) UP (ms_mem msE) a Oa).
apply AGP; [exact Ha | exact NO | exact NS |]. intros Hb. apply NE. exact (conj PNN Hb).
+ intros OX. destruct (YFfl.owned_S' B ly S rd0 M kk Hk z tr a OX) as [O|O]; [exact (NO O)|].
apply NE. split; [exact PNN|]. rewrite Hu, <- Enn in O. exact O.
+ intros Hs. apply NS. unfold ascratch in Hs |- *. destruct Hs as [Hs|Hs]; [left; clear - Hs; unfold spZ, QSTACK, ASTACK in *; unfold sp0 in *; lia | right; exact Hs].
-
intros a Ha. apply FAR.apresent_to_unpoison. apply PRESR. unfold spZ in Ha. exact Ha.
Qed.
(* lib/B/YFg2.v:277 afree_mid_arm, any UP. *)
Theorem afree_mid_armU :
amreal tfibsegs (free p tr S) W (cfg_at tfibsegs (pc_wrap_free Tfib_code) regs mem md) (FSU.free_leafU tfibsegs B ly S UP W regs mem md p n).
Proof.
apply arm_prefix.
intros z msE matE E5 W5 regs' mem' md' X' nb X mdE AOK HshE HEn5 HS5 PRESE ARX POST HQ' Hnb HCK' HQG' HFS' AGP.
unfold maybe_drain. cbn [bind get ibind].
replace (qc_bytes (st_qthread X') <=? kQuarantineCacheMax) with true.
2:{ symmetry. apply Z.leb_le. rewrite HQ'. subst X. rewrite (YFfl.S'_qthread S kk z tr) in Hnb |- *.
pose proof NODRAIN as ND. change (st_qthread S) with q in ND |- *.
destruct nb; rewrite Hnb in ND; cbn [qc_push qc_bytes]; change (ck_n kk') with (ck_n kk); rewrite <- Enn; clear - ND; lia. }
cbn [ret amreal].
rreg HS5 (1%bv : bv 5) Q1e.
unfold raZ. rewrite Q1e. rewrite unsigned_lit_small by lia.
exact (TAILMU z msE matE E5 W5 regs' mem' md' X' nb AOK HshE HEn5 HS5 PRESE ARX POST HQ' Hnb HCK' HQG' AGP).
Qed.
End mid.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 7. free with a drain (lib/B/YFfz.v).                                                                              *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Section drn.
Hypothesis DRAIN : kQuarantineCacheMax < qc_bytes (st_qthread S) + nn + (if need_new_batch (st_qthread S) then kBatchBytes else 0).
Hypothesis D0 : FK.tfib_drain_specU B.
(* lib/B/YFfz.v:98 TAILD, any UP. *)
Lemma TAILDU : forall z msE matE E5 (W5 : world tfibsegs) regs' mem' md' (X' : astate) nb,
let X := YFfl.S' S kk z tr in let mdE := with_vm_backing (m_vm_lazy md) matE md in
aok s1 (KDepot tr) z ->
msE = YK11.mkst (ms_regs msE) (w64 A_Enqueue) (ms_mem msE) (YK11.seg_rom tfibsegs) ->
(forall k0, (k0 < aHAVf)%nat -> ew E5 k0 = ew E0 k0) ->
st_ok tfibsegs E5 SS_E (restrict (w_H W) msE) ->
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem msE) a) ->
AR tfibsegs B ly X W (FSP.unpoison UP (ms_mem msE)) mdE ->
FSU.acall_postU tfibsegs B QSTACK ly X UP W (ms_regs msE) (ms_mem msE) mdE (fun _ => False) ly X' W5 regs' mem' md' ->
st_qthread X' = qc_push (st_qthread X) kk' nb ->
match nb with None => need_new_batch (st_qthread X) = false | Some _ => need_new_batch (st_qthread X) = true end ->
st_chunks X' = st_chunks X -> st_qglobal X' = st_qglobal X -> st_fs X' = st_fs X ->
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ ascratch B ASTACK regs a -> ~ (pa <= a < pa + nn) ->
aview tfibsegs (w_H W) (ms_mem msE) a = aview tfibsegs (w_H W) mem a) ->
amreal tfibsegs (drain_body X' X') W5 (cfg_at tfibsegs PC_PUT_ENQ_RA regs' mem' md') (FSU.free_leafU tfibsegs B ly S UP W regs mem md p n).
Proof.
intros z msE matE E5 W5 regs' mem' md' X' nb X mdE AOK HshE HEn5 HS PRESE ARX ((ARX' & LLE & WLE & CS & SIO & FR & PRS) & OKX' & POX') HQ' Hnb HCK' HQG' HFS' AGP.
pose proof PRE as PRE'. destruct PRE' as (HAR & Hev & Hra & Hal & Hlo & Hbot & Hhi & HPRES & Hgp & Htp & Hch & HQT). destruct HAR as (M0 & LED & BUD & MW & HSH).
pose proof kk_facts as (Hf & Hk & Hst & Hu & Hr). pose proof HSP as HSP'. pose proof FH_ok as FH.
pose proof (YFgm.LYB W ly regs mu ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FH) as LB.
pose proof p_facts as (P1 & P2 & _). pose proof QB_facts as (Qa & Qb & Q8).
pose proof Hwx_tfa as Hwx. assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
rreg HS (2%bv : bv 5) Q2. rewrite (HEn5 2%nat ltac:(cbv; lia)), E2 in Q2.
assert (SPE : spZ (ms_regs msE) = sp0 - 2208).
{ unfold spZ. rewrite Q2. unfold sp0, w64. rewrite unsigned_lit_small by (clear - Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK in *; unfold sp0 in *; lia). reflexivity. }
unfold ascratch in FR. rewrite SPE in FR, PRS.
assert (BV2 : bv_unsigned (ew E5 2) = sp0) by (rewrite (HEn5 2%nat ltac:(cbv; lia)), E2; reflexivity).
assert (NOWN : forall a, sp0 - ASTACK <= a < sp0 -> ~ aowned B ly X a /\ ~ aowned B ly X' a).
{ intros a Ha. split.
- apply (AR_stack_law_ok tfibsegs B ly X W (FSP.unpoison UP (ms_mem msE)) mdE a ARX). clear - Ha Hlo Hhi. unfold spZ, ASTACK in *. unfold sp0 in *. lia.
- apply (AR_stack_law_ok tfibsegs B ly X' W5 (FSP.unpoison UP mem') md' a ARX'). clear - Ha Hlo Hhi. unfold spZ, ASTACK in *. unfold sp0 in *. lia. }
assert (AGS : forall a, sp0 - 2208 <= a < sp0 -> aview tfibsegs (w_H W5) mem' a = aview tfibsegs (w_H W) (ms_mem msE) a).
{ intros a Ha. destruct (NOWN a ltac:(clear - Ha; unfold ASTACK; lia)) as [N1 N2].
pose proof (OFF_SP a ltac:(clear - Ha; unfold ASTACK; lia)) as Oa.
rewrite <- (FAR.aview_unpoison (w_H W5) UP mem' a Oa), <- (FAR.aview_unpoison (w_H W) UP (ms_mem msE) a Oa).
apply FR; [clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK in *; unfold sp0 in *; lia | exact N1 | exact N2 | | intros []].
unfold ascratch. rewrite (ts_errno _ TB). unfold TFIB_ERRNO, QSTACK. clear - Ha Hlo LB. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK in *. unfold sp0 in *. lia. }
assert (HP : regs_preserved (ms_regs msE) regs') by (intros r Hr'; apply CS; exact Hr').
lazymatch type of HS with st_ok _ _ ?ss ?ms0 =>
let m := eval vm_compute in (ss_mem ss) in
lazymatch m with ?r0 :: ?r1 :: ?r2 :: ?r3 :: ?r4 :: ?rest =>
pose proof (st_ok_after_call tfibsegs 112 E5 ss ms0 regs' (mrestrict (w_H W5) mem') (trim_lo r0 (-2208) :: r1 :: r2 :: r4 :: nil) PC_PUT_ENQ_RA HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(apply submem_keep; [apply subregion_trim_lo|]; apply submem_keep; [apply subregion_refl|]; apply submem_keep; [apply subregion_refl|];
apply submem_drop; apply submem_keep; [apply subregion_refl|]; apply submem_nil)
ltac:(vm_compute; reflexivity) HP) as HS1;
let rsv := eval vm_compute in (trim_lo r0 (-2208) :: r1 :: r2 :: r4 :: nil) in
change (trim_lo r0 (-2208) :: r1 :: r2 :: r4 :: nil) with rsv in HS1;
let ss2 := eval vm_compute in (ss_after_call ss rsv 112 PC_PUT_ENQ_RA) in
change (ss_after_call ss rsv 112 PC_PUT_ENQ_RA) with ss2 in HS1
end
end.
cbn [ms_mem restrict] in HS1.
lazymatch type of HS1 with Forall _ ?L -> _ =>
assert (KEPT : Forall (region_kept tfibsegs E5 (mrestrict (w_H W) (ms_mem msE)) (mrestrict (w_H W5) mem')) L);
[ repeat apply Forall_cons; try apply Forall_nil;
(apply kept_of_aview; cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; rewrite BV2;
[ intros a Ha; apply AGS; clear - Ha; lia
| intros a Ha; split; [apply AGS; clear - Ha; lia | clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK, TFIB_IMG_END in *; unfold sp0 in *; lia] ])
| specialize (HS1 KEPT); clear KEPT ]
end.
set (En6 := havoc E5 112 (map (YK11.getr regs') CLOB)) in HS1.
assert (HEn6 : forall k0, (k0 < aHAVf)%nat -> ew En6 k0 = ew E0 k0) by (intros k0 Hk0; subst En6; unfold aHAVf in Hk0; rewrite ew_havoc_old by lia; apply HEn5; exact Hk0).
assert (QB' : qc_bytes (st_qthread X') = QBFv).
{ rewrite HQ'. subst X. rewrite (YFfl.S'_qthread S kk z tr) in Hnb |- *. unfold YFgm.QBFv. change (st_qthread S) with q in *.
destruct nb; rewrite Hnb; cbn [qc_push qc_bytes]; change (ck_n kk') with (ck_n kk); rewrite <- Enn; lia. }
assert (RV : val_mem tfibsegs (mrestrict (w_H W5) mem') (ly_T ly + (t_qc + 24)) (N.to_nat 8) QBFv).
{ rewrite <- QB'. destruct ARX' as (MX' & _).
assert (C : cell_holds B ly (aview tfibsegs (w_H W5) (FSP.unpoison UP mem')) (z8 (aoff (AT t_qc) 24) (qc_bytes (st_qthread X')))).
{ apply (proj1 (Forall_forall _ _) (am_cells B ly X' _ MX')). unfold acells. rewrite !in_app_iff. do 4 right. left. unfold quar_cells, qc_cells. cbn. tauto. }
apply (FAR.val_mem_of_unpoison (w_H W5) UP mem').
{ intros k0 Hk0. apply (OFF_Z3 (ly_T ly) kThreadObjSize _ (proj1 LB)). change (N.to_nat 8) with 8%nat in Hk0. unfold t_qc, kThreadObjSize. lia. }
replace (ly_T ly + (t_qc + 24)) with (aeval B ly (aoff (AT t_qc) 24)) by (cbn; lia).
exact (cell_holds_val_mem B ly (w_H W5) (FSP.unpoison UP mem') _ 8 (ANum (qc_bytes (st_qthread X'))) C). }
apply (st_ok_add_region _ _ _ (YP09.mkRegion (Some 32%nat) (t_qc + 24) (t_qc + 32) 0 0 [YP09.mkChunk (t_qc + 24) (CVal 8 (SOff 50%nat 0))])) in HS1;
[ | reflexivity
| unfold YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem];
rewrite (HEn6 32%nat ltac:(cbv; lia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; lia);
split; [clear - LB; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, t_qc in *; lia|]; split; [clear - LB; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, t_qc in *; lia|]; split; [intros o Ho; lia|];
apply Forall_cons; [|apply Forall_nil];
eapply (chunk_ok_val tfibsegs En6 _ _ _ 8 (SOff 50%nat 0) QBFv);
[ cbn [sv_denot]; rewrite (HEn6 50%nat ltac:(cbv; lia)), EaQBF; unfold w64; rewrite Zbv_add_unsigned; f_equal; lia
| clear - Qa Qb Q8; unfold YFgm.QBFv, YFgm.QBMAX, kQuarantineCacheMax, kBatchBytes in *; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); destruct (need_new_batch q); lia
| cbn; lia | exact RV ]
| cbn [all_disjoint ss_mem]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite ?(HEn6 32%nat ltac:(cbv; lia)), ?(HEn6 2%nat ltac:(cbv; lia)), ?EaT, ?E2; unfold w64; rewrite unsigned_lit_small by (clear - LB; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; lia);
fold sp0; pose proof (YFgm.stack_ivs W ly regs mu ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FH) as (IT & _);
clear - IT LB; unfold kThreadObjSize, t_qc, ASTACK in *; repeat split; lia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
rewrite <- (restrict_mkst_fx (w_H W5)) in HS1. rename HS1 into HS'. clear HS. rename HS' into HS.
unfold cfg_at. rewrite <- (wvb_self md') at 1. change (w64 PC_PUT_ENQ_RA) with (Z_to_bv 64 PC_PUT_ENQ_RA).
apply amreal_after_SRr.
srr_run_sh tfibtbl_rtF_ok HS.
rename HF into HF0. clear HFr.
srr_branch_sh tfibtbl_rtF_ok HS.
2:{ exfalso. match goal with H : branch_taken _ _ _ = false |- _ => rewrite branch_ltu_U in H; apply Z.ltb_ge in H; revert H end.
rewrite !U_zev by reflexivity. cbn [zev zalu_raw]. unfold rho_of. rewrite (HEn6 50%nat ltac:(cbv; lia)), EaQBF, Z.add_0_r.
unfold w64. rewrite unsigned_lit_small by (clear - Qa Qb Q8; unfold YFgm.QBFv, YFgm.QBMAX, kQuarantineCacheMax, kBatchBytes in *; destruct (need_new_batch q); lia).
rewrite !zcanon_id by (clear - Qa Qb Q8; unfold YFgm.QBFv, YFgm.QBMAX, kQuarantineCacheMax, kBatchBytes, M64 in *; destruct (need_new_batch q); lia).
pose proof DRAIN as ND. change (st_qthread S) with q in ND. clear - ND. unfold YFgm.QBFv, kQuarantineCacheMax, kBatchBytes in *.
destruct (need_new_batch q); lia. }
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_sh tfibtbl_rtF_ok HS. rename HF into HF1. clear HFr.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msC end.
lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing _ ?mx _)) _ => rename mx into matC end.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W5) En6 _ _ HS eq_refl) as HshC; cbn [ss_pc] in HshC.
assert (FR1 : forall x : word, ~ (sp0 - 2208 <= bv_unsigned x < sp0 - 2128) -> ~ (sp0 - 64 <= bv_unsigned x < sp0) -> ms_mem msC x = mem' x).
{ intros x Hx1 Hx2. rewrite (HF1 x); [apply (HF0 x)|].
all: intros Hw; destruct (in_wrange_windows _ _ _ Hw) as (b & lo & hi & Hin & Hrg);
lazymatch type of Hin with In _ (windows ?rs) => let ws := eval vm_compute in (windows rs) in change (windows rs) with ws in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [Hin|Hin];
[ injection Hin as <- <- <-; cbn [fst snd base_val] in Hrg; rewrite ?(HEn6 2%nat ltac:(cbv; lia)), ?E2, ?(HEn6 32%nat ltac:(cbv; lia)), ?EaT in Hrg; unfold w64 in Hrg;
rewrite ?unsigned_lit_small in Hrg by (clear - LB; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; lia); clear - Hx1 Hx2 Hrg; unfold ASTACK, t_qc in *; unfold sp0 in *; lia |]);
destruct Hin. }
clear HF1 HF0.
assert (PRES' : forall a, sp0 - ASTACK <= a < sp0 -> ~ (sp0 - 2208 <= a < sp0 - 2128) -> ~ (sp0 - 64 <= a < sp0) -> apresent (w_H W5) mem' a).
{ intros a Ha N1 N2. pose proof (OFF_SP a Ha) as Oa.
destruct (Z_lt_le_dec a (sp0 - 2208)) as [L|L]; [destruct (Z_lt_le_dec a (sp0 - 2208 - QSTACK)) as [L2|L2]|].
2:{ apply (FAR.apresent_of_unpoison _ UP _ a Oa). apply PRS. clear - L L2. unfold QSTACK in *. lia. }
all: assert (EQa : aview tfibsegs (w_H W5) mem' a = aview tfibsegs (w_H W) (ms_mem msE) a)
by (destruct (NOWN a Ha) as [M1 M2];
rewrite <- (FAR.aview_unpoison (w_H W5) UP mem' a Oa), <- (FAR.aview_unpoison (w_H W) UP (ms_mem msE) a Oa);
apply FR; [clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK in *; unfold sp0 in *; lia | exact M1 | exact M2 | | intros []];
unfold ascratch; rewrite (ts_errno _ TB); unfold TFIB_ERRNO; first [clear - Ha L L2 N1 N2 Hlo LB | clear - Ha L N1 N2 Hlo LB]; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK, QSTACK in *; unfold sp0 in *; lia).
all: pose proof (PRESE a Ha) as P; apply apresent_mbyte in P as [b Hb];
assert (A : aview tfibsegs (w_H W) (ms_mem msE) a = Some (bv_unsigned b)) by (unfold aview; rewrite Hb; reflexivity);
rewrite <- EQa in A; apply aview_some in A as (b' & Hb' & _);
exact (mbyte_high_apresent (w_H W5) mem' a b' ltac:(clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK, TFIB_IMG_END in *; unfold sp0 in *; lia) Hb'). }
assert (PRESC : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W5) (ms_mem msC) a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 2208)) as [L1|L1]; [|destruct (Z_lt_le_dec a (sp0 - 2176)) as [L2|L2]; [|destruct (Z_lt_le_dec a (sp0 - 2128)) as [L3|L3]; [|destruct (Z_lt_le_dec a (sp0 - 64)) as [L4|L4]]]].
- apply (apresent_same (w_H W5) mem'); [apply FR1; rewrite unsigned_lit_small by (clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK in *; unfold sp0 in *; lia); clear - L1; lia | apply PRES'; [exact Ha | clear - L1; lia | clear - L1; lia]].
- eapply (st_ok_window_apresent (w_H W5) En6 _ _ 1 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn6 2%nat ltac:(cbv; lia)), E2; clear - L1 L2; unfold sp0; lia | clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK, TFIB_IMG_END in *; unfold sp0 in *; lia].
- eapply (st_ok_window_apresent (w_H W5) En6 _ _ 3 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn6 2%nat ltac:(cbv; lia)), E2; clear - L2 L3; unfold sp0; lia | clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK, TFIB_IMG_END in *; unfold sp0 in *; lia].
- apply (apresent_same (w_H W5) mem'); [apply FR1; rewrite unsigned_lit_small by (clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK in *; unfold sp0 in *; lia); clear - L3 L4; lia | apply PRES'; [exact Ha | clear - L3 L4; lia | clear - L3 L4; lia]].
- eapply (st_ok_window_apresent (w_H W5) En6 _ _ 4 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn6 2%nat ltac:(cbv; lia)), E2; clear - L4 Ha; unfold sp0; lia | clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK, TFIB_IMG_END in *; unfold sp0 in *; lia]. }
assert (AGC : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2208 <= a < sp0 - 2128) -> ~ (sp0 - 64 <= a < sp0) -> aview tfibsegs (w_H W5) (ms_mem msC) a = aview tfibsegs (w_H W5) mem' a).
{ intros a Ha N1 N2. apply aview_same. apply FR1; rewrite unsigned_lit_small by exact Ha; assumption. }
assert (WDEC : forall a, ((sp0 - 2208 <= a < sp0 - 2128) \/ (sp0 - 64 <= a < sp0)) \/ (~ (sp0 - 2208 <= a < sp0 - 2128) /\ ~ (sp0 - 64 <= a < sp0))).
{ intros a. clear. destruct (Z_lt_le_dec a (sp0 - 2208)); [right; lia|]. destruct (Z_lt_le_dec a (sp0 - 2128)); [left; lia|].
destruct (Z_lt_le_dec a (sp0 - 64)); [right; lia|]. destruct (Z_lt_le_dec a sp0); [left; lia | right; lia]. }
(* AR of the drain call's state, on the unpoisoned reading (the donor's ARC through AR_unpoison_frame). *)
assert (ARC : AR tfibsegs B ly X' W5 (FSP.unpoison UP (ms_mem msC)) (with_vm_backing (m_vm_lazy md') matC md')).
{ apply (AR_unpoison_frame ly X' W5 mem' (ms_mem msC) md' _ (fun a => (sp0 - 2208 <= a < sp0 - 2128) \/ (sp0 - 64 <= a < sp0)) ARX').
- intros a0. cbv beta. destruct (WDEC a0) as [C|[C1 C2]]; [left; exact C | right; intros [C'|C']; [exact (C1 C') | exact (C2 C')]].
- intros x Hx. cbv beta in Hx. apply FR1; intros Hw; apply Hx; [left | right]; exact Hw.
- intros a Ha. cbv beta in Ha. split; [exact (proj2 (NOWN a ltac:(clear - Ha; unfold ASTACK; lia))) | apply PRESC; clear - Ha; unfold ASTACK; lia].
- apply m_vmmaps_wvb.
- apply m_vm_lazy_wvb.
- apply eager_used_wvb. }
pose proof (lo_top ly LO) as (_ & _ & _ & _ & _ & _ & TL7).
apply SRr_ret. rewrite HshC.
rreg HS (1%bv : bv 5) C1. rreg HS (2%bv : bv 5) C2. rreg HS (3%bv : bv 5) C3. rreg HS (4%bv : bv 5) C4.
rreg HS (10%bv : bv 5) C10. rreg HS (11%bv : bv 5) C11. rreg HS (12%bv : bv 5) C12.
cbn [sv_denot] in C1, C2, C3, C4, C10, C11, C12.
rewrite (HEn6 2%nat ltac:(cbv; lia)), E2 in C2. fold sp0 in C2. rewrite (HEn6 32%nat ltac:(cbv; lia)), EaT in C11, C12. unfold w64 in C11, C12.
rewrite unsigned_lit_small in C11, C12 by (clear - LB; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; lia).
pose proof (qmeter_tight _ HQT) as (T1 & T2 & T3). pose proof (YFfl.quar_S' B ly S rd0 M kk Hk Hst z tr) as [QX1 QX2].
pose proof (unq_push X X' kk' nb HCK' HQ' HQG' ltac:(intros ->; exact Hnb)) as UQ. unfold unq in UQ.
assert (QE : quar_n X' = quar_n X) by (unfold quar_n; rewrite HCK'; reflexivity).
assert (WFX' : Wf (as_universe B) X') by (destruct ARX' as (MX' & _); exact (am_wf B ly X' _ MX')).
assert (DRX' : kQuarantineCacheMax < qc_bytes (st_qthread X')).
{ rewrite QB'. pose proof DRAIN as DR'. change (st_qthread S) with q in DR'. unfold YFgm.QBFv. exact DR'. }
assert (QLX' : qloose X').
{ unfold qloose. rewrite QB', HQG'. split; [|split].
+ clear - Qb. unfold YFgm.QBMAX, kQuarantineCacheMax, kBatchBytes in Qb. lia.
+ subst X. rewrite (YFfl.S'_qglobal S kk z tr). clear - T2. unfold kQuarantineMax in *. lia.
+ change (ck_n kk') with (ck_n kk) in UQ. subst X. clear - QX1 QX2 UQ QE T3. lia. }
eapply amreal_then_SRr.
{ eapply (amreal_apost _ (drain_body X' X') _ W5 _ _ (drain_body_apost (as_universe B) 0 0 0 X' WFX' QLX' DRX')).
apply (D0 ly X' UP W5 (ms_regs msC) (ms_mem msC) (with_vm_backing (m_vm_lazy md') matC md')).
unfold FK.drain_preU. split; [|split; [exact OKX'|]].
2:{ apply (FAR.upoisoned_keep UP W5 W5 mem' (ms_mem msC) POX'). intros s Hs.
pose proof (ush_low s Hs) as [Ls1 Ls2]. pose proof (FSP.ush_range tfibsegs B ly S UP W mem md s ARU0 Hs) as Rs.
apply AGC; [exact Rs | |]; intros Hw; clear - Hw Ls2 Hlo TL7; unfold spZ, ASTACK in *; unfold sp0 in *; lia. }
unfold drain_pre, spZ, raZ. rewrite C1, C2, C3, C4, C10, C11, C12. rewrite !unsigned_lit_small by (clear - Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK in *; unfold sp0 in *; lia).
splits.
- exact ARC.
- exact DRX'.
- exact QLX'.
- apply YK0s.ret_ok_even. reflexivity.
- clear; lia.
- replace (sp0 + -2208) with (sp0 + (-138) * 16) by lia. rewrite Z_mod_plus_full. exact Hal.
- clear - Hlo. unfold DSTACK, spZ, ASTACK in *. unfold sp0 in *. lia.
- clear - Hhi. unfold spZ in *. unfold sp0 in *. lia.
- intros a Ha. apply FAR.apresent_to_unpoison. apply PRESC. clear - Ha. unfold DSTACK, ASTACK in *. lia.
- rewrite (HEn6 3%nat ltac:(cbv; lia)), (YFgm.Er ly regs ch pa nn hb1 q j1 j2 j3 3 3%bv eq_refl). exact Hgp.
- rewrite (ts_tp _ TB). reflexivity.
- reflexivity.
- reflexivity.
- reflexivity. }
intros [[] X''] W6 c6 [(WX'' & FF6 & QT6 & QG6 & UQ6) (regs6 & mem6 & md6 & -> & (POST6 & OKX'' & POX'') & _)].
cbn [fst snd] in WX'', FF6, QT6, QG6, UQ6, POST6, OKX'', POX'' |- *.
pose proof POST6 as (ARX'' & LLE6 & WLE6 & CS6 & SIO6 & FR6 & PRS6).
unfold ascratch, spZ, raZ in FR6, PRS6 |- *. rewrite C2 in FR6, PRS6. rewrite C1.
rewrite !unsigned_lit_small in FR6, PRS6 |- * by (clear - Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK in *; unfold sp0 in *; lia).
assert (NOWN6 : forall a, sp0 - ASTACK <= a < sp0 -> ~ aowned B ly X' a /\ ~ aowned B ly X'' a).
{ intros a Ha. split.
- exact (proj2 (NOWN a Ha)).
- apply (AR_stack_law_ok tfibsegs B ly X'' W6 (FSP.unpoison UP mem6) md6 a ARX''). clear - Ha Hlo Hhi. unfold spZ, ASTACK in *. unfold sp0 in *. lia. }
assert (AGS6 : forall a, sp0 - 2208 <= a < sp0 -> aview tfibsegs (w_H W6) mem6 a = aview tfibsegs (w_H W5) (ms_mem msC) a).
{ intros a Ha. destruct (NOWN6 a ltac:(clear - Ha; unfold ASTACK; lia)) as [N1 N2].
pose proof (OFF_SP a ltac:(clear - Ha; unfold ASTACK; lia)) as Oa.
rewrite <- (FAR.aview_unpoison (w_H W6) UP mem6 a Oa), <- (FAR.aview_unpoison (w_H W5) UP (ms_mem msC) a Oa).
apply FR6; [clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK in *; unfold sp0 in *; lia | exact N1 | exact N2 | | intros []].
rewrite (ts_errno _ TB). unfold TFIB_ERRNO, DSTACK. clear - Ha Hlo LB. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK in *. unfold sp0 in *. lia. }
assert (BV2' : bv_unsigned (ew En6 2) = sp0) by (rewrite (HEn6 2%nat ltac:(cbv; lia)), E2; reflexivity).
assert (HP6 : regs_preserved (ms_regs msC) regs6) by (intros r Hr'; apply CS6; exact Hr').
lazymatch type of HS with st_ok _ _ ?ss ?ms0 =>
let m := eval vm_compute in (ss_mem ss) in
lazymatch m with ?r0 :: ?r1 :: ?r2 :: ?r3 :: ?r4 :: ?rest =>
pose proof (st_ok_after_call tfibsegs 128 En6 ss ms0 regs6 (mrestrict (w_H W6) mem6) (r1 :: r2 :: r3 :: r4 :: nil) PC_PUT_DRAIN_RA HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(apply submem_drop; apply submem_keep; [apply subregion_refl|]; apply submem_keep; [apply subregion_refl|]; apply submem_keep; [apply subregion_refl|];
apply submem_keep; [apply subregion_refl|]; apply submem_nil)
ltac:(vm_compute; reflexivity) HP6) as HS1;
let rsv := eval vm_compute in (r1 :: r2 :: r3 :: r4 :: nil) in
change (r1 :: r2 :: r3 :: r4 :: nil) with rsv in HS1;
let ss2 := eval vm_compute in (ss_after_call ss rsv 128 PC_PUT_DRAIN_RA) in
change (ss_after_call ss rsv 128 PC_PUT_DRAIN_RA) with ss2 in HS1
end
end.
cbn [ms_mem restrict] in HS1.
lazymatch type of HS1 with Forall _ ?L -> _ =>
assert (KEPT : Forall (region_kept tfibsegs En6 (mrestrict (w_H W5) (ms_mem msC)) (mrestrict (w_H W6) mem6)) L);
[ repeat apply Forall_cons; try apply Forall_nil;
(apply kept_of_aview2; cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; rewrite BV2';
[ intros a Ha; apply AGS6; clear - Ha; lia
| intros a Ha; split; [apply AGS6; clear - Ha; lia | clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK, TFIB_IMG_END in *; unfold sp0 in *; lia] ])
| specialize (HS1 KEPT); clear KEPT ]
end.
set (En7 := havoc En6 128 (map (YK11.getr regs6) CLOB)) in HS1.
assert (HEn7 : forall k0, (k0 < aHAVf)%nat -> ew En7 k0 = ew E0 k0) by (intros k0 Hk0; subst En7; unfold aHAVf in Hk0; rewrite ew_havoc_old by lia; apply HEn6; exact Hk0).
rewrite <- (restrict_mkst_fx (w_H W6)) in HS1. clear HS. rename HS1 into HS.
unfold cfg_at. rewrite <- (wvb_self md6) at 1.
srr_run_sh tfibtbl_rtF_ok HS.
lazymatch type of HS with st_ok _ ?E _ (restrict _ ?msx) => set (En8 := E) in HS; rename msx into msR end.
assert (HEn8 : forall k0, (k0 < aHAVf)%nat -> ew En8 k0 = ew E0 k0) by (intros k0 Hk0; subst En8; unfold aHAVf in Hk0; rewrite ?ew_havoc_old by lia; apply HEn7; exact Hk0).
assert (FRT : forall x : word, ~ (sp0 - 2208 <= bv_unsigned x < sp0 - 2128) -> ~ (sp0 - 64 <= bv_unsigned x < sp0) -> ms_mem msR x = mem6 x).
{ intros x Hx1 Hx2. apply HF. intros Hw. destruct (in_wrange_windows _ _ _ Hw) as (b & lo & hi & Hin & Hrg).
lazymatch type of Hin with In _ (windows ?rs) => let ws := eval vm_compute in (windows rs) in change (windows rs) with ws in Hin end.
cbn [In] in Hin.
repeat (destruct Hin as [Hin|Hin];
[ injection Hin as <- <- <-; cbn [fst snd base_val] in Hrg; rewrite ?(HEn7 2%nat ltac:(cbv; lia)), ?E2, ?(HEn7 32%nat ltac:(cbv; lia)), ?EaT in Hrg; unfold w64 in Hrg;
rewrite ?unsigned_lit_small in Hrg by (clear - LB; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; lia); clear - Hx1 Hx2 Hrg; unfold ASTACK, t_qc in *; unfold sp0 in *; lia |]).
destruct Hin. }
clear HF HFr.
assert (PRES6 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W6) mem6 a).
{ intros a Ha. pose proof (OFF_SP a Ha) as Oa.
destruct (Z_lt_le_dec a (sp0 - 2208)) as [L|L]; [destruct (Z_lt_le_dec a (sp0 - 2208 - DSTACK)) as [L2|L2]|].
2:{ apply (FAR.apresent_of_unpoison _ UP _ a Oa). apply PRS6. clear - L L2. lia. }
all: assert (EQa : aview tfibsegs (w_H W6) mem6 a = aview tfibsegs (w_H W5) (ms_mem msC) a)
by (first [ exact (AGS6 a ltac:(clear - Ha L; lia))
| destruct (NOWN6 a Ha) as [M1 M2];
rewrite <- (FAR.aview_unpoison (w_H W6) UP mem6 a Oa), <- (FAR.aview_unpoison (w_H W5) UP (ms_mem msC) a Oa);
apply FR6; [clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK in *; unfold sp0 in *; lia | exact M1 | exact M2 | | intros []];
rewrite (ts_errno _ TB); unfold TFIB_ERRNO; clear - Ha L L2 Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK, DSTACK in *; unfold sp0 in *; lia ]).
all: pose proof (PRESC a Ha) as P; apply apresent_mbyte in P as [b Hb];
assert (A : aview tfibsegs (w_H W5) (ms_mem msC) a = Some (bv_unsigned b)) by (unfold aview; rewrite Hb; reflexivity);
rewrite <- EQa in A; apply aview_some in A as (b' & Hb' & _);
exact (mbyte_high_apresent (w_H W6) mem6 a b' ltac:(clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK, TFIB_IMG_END in *; unfold sp0 in *; lia) Hb'). }
assert (PRESR : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W6) (ms_mem msR) a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 2208)) as [L1|L1]; [|destruct (Z_lt_le_dec a (sp0 - 2176)) as [L2|L2]; [|destruct (Z_lt_le_dec a (sp0 - 2128)) as [L3|L3]; [|destruct (Z_lt_le_dec a (sp0 - 64)) as [L4|L4]]]].
- apply (apresent_same (w_H W6) mem6); [apply FRT; rewrite unsigned_lit_small by (clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK in *; unfold sp0 in *; lia); clear - L1; lia | apply PRES6; exact Ha].
- eapply (st_ok_window_apresent (w_H W6) En8 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn8 2%nat ltac:(cbv; lia)), E2; clear - L1 L2; unfold sp0; lia | clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK, TFIB_IMG_END in *; unfold sp0 in *; lia].
- eapply (st_ok_window_apresent (w_H W6) En8 _ _ 2 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn8 2%nat ltac:(cbv; lia)), E2; clear - L2 L3; unfold sp0; lia | clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK, TFIB_IMG_END in *; unfold sp0 in *; lia].
- apply (apresent_same (w_H W6) mem6); [apply FRT; rewrite unsigned_lit_small by (clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK in *; unfold sp0 in *; lia); clear - L3 L4; lia | apply PRES6; exact Ha].
- eapply (st_ok_window_apresent (w_H W6) En8 _ _ 3 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn8 2%nat ltac:(cbv; lia)), E2; clear - L4 Ha; unfold sp0; lia | clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, ASTACK, TFIB_IMG_END in *; unfold sp0 in *; lia]. }
eapply (SRr_ret_at tfibsegs tfibtbl_rtF tfibtbl_rtF_ok Hwx W6 En8); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'.
rreg HS (1%bv : bv 5) Q1f. rewrite (HEn8 1%nat ltac:(cbv; lia)), (YFgm.E1 ly regs ch pa nn hb1 q j1 j2 j3) in Q1f.
srr_norm_model.
exists ly, (ms_regs msR), (ms_mem msR), (with_vm_backing (m_vm_lazy md6) mat' md6). split.
{ unfold cfg_at, raZ, w64. rewrite Q1f, Z_to_bv_bv_unsigned. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split.
2:{
cbn [snd]. unfold qtight. split; [exact QT6 | split].
- eapply Z.le_trans; [exact QG6|]. rewrite HQG'. subst X. rewrite (YFfl.S'_qglobal S kk z tr). clear - T2. unfold kQuarantineMax in *. lia.
- unfold unq in UQ6. change (ck_n kk') with (ck_n kk) in UQ. subst X. clear - QX1 QX2 UQ QE T3 UQ6. lia. }
assert (AGT : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2208 <= a < sp0 - 2128) -> ~ (sp0 - 64 <= a < sp0) -> aview tfibsegs (w_H W6) (ms_mem msR) a = aview tfibsegs (w_H W6) mem6 a).
{ intros a Ha N1 N2. apply aview_same. apply FRT; rewrite unsigned_lit_small by exact Ha; assumption. }
assert (PNN : p <> PNull).
{ intros Hp0. pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ WF) kk Hk) as [_ CK].
assert (HU0 : ck_user kk = PNull) by (rewrite Hu; exact Hp0). unfold ck_user in HU0. destruct (ck_beg kk); cbn in HU0; try discriminate; destruct CK. }
split; [|split; [exact OKX''|]].
2:{ apply (FAR.upoisoned_keep UP W6 W6 mem6 (ms_mem msR) POX''). intros s Hs.
pose proof (ush_low s Hs) as [Ls1 Ls2]. pose proof (FSP.ush_range tfibsegs B ly S UP W mem md s ARU0 Hs) as Rs.
apply AGT; [exact Rs | |]; intros Hw; clear - Hw Ls2 Hlo TL7; unfold spZ, ASTACK in *; unfold sp0 in *; lia. }
split; [|split; [apply layout_le_refl | split; [eapply wle_trans; [exact WLE | exact WLE6] | split; [|split; [|split]]]]].
-
apply (AR_unpoison_frame ly X'' W6 mem6 (ms_mem msR) md6 _ (fun a => (sp0 - 2208 <= a < sp0 - 2128) \/ (sp0 - 64 <= a < sp0)) ARX'').
+ intros a0. cbv beta. destruct (WDEC a0) as [C|[C1' C2']]; [left; exact C | right; intros [C'|C']; [exact (C1' C') | exact (C2' C')]].
+ intros x Hx. cbv beta in Hx. apply FRT; intros Hw; apply Hx; [left | right]; exact Hw.
+ intros a Ha. cbv beta in Ha. split; [exact (proj2 (NOWN6 a ltac:(clear - Ha; unfold ASTACK; lia))) | apply PRESR; clear - Ha; unfold ASTACK; lia].
+ reflexivity.
+ reflexivity.
+ reflexivity.
-
intros r Hr'. unfold acallee_saved in Hr'.
assert (R : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
clear Hr'. rewrite (ts_tp _ TB) in Htp.
repeat match type of R with _ \/ _ => destruct R as [R|R] end; subst r;
[ cs_case HS HEn8 Htp (2%bv : bv 5) | cs_case HS HEn8 Htp (3%bv : bv 5) | cs_case HS HEn8 Htp (4%bv : bv 5) | cs_case HS HEn8 Htp (8%bv : bv 5) | cs_case HS HEn8 Htp (9%bv : bv 5)
| cs_case HS HEn8 Htp (18%bv : bv 5) | cs_case HS HEn8 Htp (19%bv : bv 5) | cs_case HS HEn8 Htp (20%bv : bv 5) | cs_case HS HEn8 Htp (21%bv : bv 5) | cs_case HS HEn8 Htp (22%bv : bv 5)
| cs_case HS HEn8 Htp (23%bv : bv 5) | cs_case HS HEn8 Htp (24%bv : bv 5) | cs_case HS HEn8 Htp (25%bv : bv 5) | cs_case HS HEn8 Htp (26%bv : bv 5) | cs_case HS HEn8 Htp (27%bv : bv 5) ].
-
clear - SIO SIO6. unfold same_io in SIO, SIO6 |- *.
destruct md, md', md6. cbn in SIO, SIO6 |- *.
intuition congruence.
-
intros a Ha NO NO'' NS NE. pose proof (FAR.offU_not_owned B ly S UP W mem md a ARU0 Ha NO) as Oa.
rewrite (FAR.aview_unpoison (w_H W6) UP (ms_mem msR) a Oa), (FAR.aview_unpoison (w_H W) UP mem a Oa).
assert (NOX : ~ aowned B ly X a).
{ intros OX. destruct (YFfl.owned_S' B ly S rd0 M kk Hk z tr a OX) as [O|O]; [exact (NO O)|]. apply NE. split; [exact PNN|]. rewrite Hu, <- Enn in O. exact O. }
assert (NOX' : ~ aowned B ly X' a) by (intros O; apply NOX; exact (aowned_same_cf B ly X X' a HCK' HFS' O)).
assert (NS1 : ~ (sp0 - 2208 <= a < sp0 - 2128)) by (intros Hs; apply NS; unfold ascratch; left; clear - Hs; unfold spZ, ASTACK; unfold sp0 in *; lia).
assert (NS2 : ~ (sp0 - 64 <= a < sp0)) by (intros Hs; apply NS; unfold ascratch; left; clear - Hs; unfold spZ, ASTACK; unfold sp0 in *; lia).
rewrite (AGT a Ha NS1 NS2).
rewrite <- (FAR.aview_unpoison (w_H W6) UP mem6 a Oa).
rewrite FR6; [| exact Ha | exact NOX' | exact NO'' | | intros []].
2:{ intros [Hs|Hs]; apply NS; unfold ascratch; [left; clear - Hs; unfold spZ, DSTACK, ASTACK in *; unfold sp0 in *; lia | right; first [exact Hs | rewrite (ts_errno _ TB); exact Hs | rewrite (ts_errno _ TB) in Hs; exact Hs] ]. }
rewrite (FAR.aview_unpoison (w_H W5) UP (ms_mem msC) a Oa).
rewrite (AGC a Ha NS1 NS2).
rewrite <- (FAR.aview_unpoison (w_H W5) UP mem' a Oa).
rewrite FR; [| exact Ha | exact NOX | exact NOX' | | intros []].
2:{ intros [Hs|Hs]; apply NS; unfold ascratch; [left; clear - Hs; unfold spZ, QSTACK, ASTACK in *; unfold sp0 in *; lia | right; first [exact Hs | rewrite (ts_errno _ TB); exact Hs | rewrite (ts_errno _ TB) in Hs; exact Hs] ]. }
rewrite (FAR.aview_unpoison (w_H W) UP (ms_mem msE) a Oa).
apply AGP; [exact Ha | exact NO | exact NS |]. intros Hb. apply NE. exact (conj PNN Hb).
-
intros a Ha. apply FAR.apresent_to_unpoison. apply PRESR. unfold spZ in Ha. exact Ha.
Qed.
(* lib/B/YFfz.v:421 afree_drn_arm, any UP. *)
Theorem afree_drn_armU :
amreal tfibsegs (free p tr S) W (cfg_at tfibsegs (pc_wrap_free Tfib_code) regs mem md) (FSU.free_leafU tfibsegs B ly S UP W regs mem md p n).
Proof.
apply arm_prefix.
intros z msE matE E5 W5 regs' mem' md' X' nb X mdE AOK HshE HEn5 HS5 PRESE ARX POST HQ' Hnb HCK' HQG' HFS' AGP.
rewrite (maybe_drain_drain X').
2:{ rewrite HQ'. subst X. rewrite (YFfl.S'_qthread S kk z tr) in Hnb |- *.
pose proof DRAIN as DR. change (st_qthread S) with q in DR |- *.
destruct nb; rewrite Hnb in DR; cbn [qc_push qc_bytes]; change (ck_n kk') with (ck_n kk); rewrite <- Enn; clear - DR; lia. }
rreg HS5 (1%bv : bv 5) Q1e.
unfold raZ. rewrite Q1e. rewrite unsigned_lit_small by lia.
exact (TAILDU z msE matE E5 W5 regs' mem' md' X' nb AOK HshE HEn5 HS5 PRESE ARX POST HQ' Hnb HCK' HQG' HFS' AGP).
Qed.
End drn.
End e.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 8. The exported statements (contract of FSupoisonAllocF.v): AR_laws after B, UP after S, the U forms of the        *)
(*    donor's pre, leaf and enqueue / drain specs, afree_realizesU's range premise after the block premise.           *)
(* ---------------------------------------------------------------------------------------------------------------- *)
(* lib/B/YFg2.v:407 afree_mid, any UP. *)
Theorem afree_midU : forall B, AR_laws tfibsegs B -> TfibSyms B -> forall ly S UP W regs mem md p n ch,
FSU.acall_preU tfibsegs B ly S UP W regs mem md ch -> In (p, n) (blocks S) ->
(forall r, In r UP -> fst r + snd r <= sptr_addr B ly p \/ sptr_addr B ly p + req_size n <= fst r) ->
YK11.getr regs 10 = w64 (sptr_addr B ly p) ->
In (call_trace ly (pc_free_ra0 Tfib_code) regs ch) (as_universe B) \/ st_nev S < EV_MAX ->
qc_bytes (st_qthread S) + req_size n + (if need_new_batch (st_qthread S) then kBatchBytes else 0) <= kQuarantineCacheMax ->
tfib_ialloc_spec -> tfib_unwind_spec -> tfib_depot_spec B -> FK.tfib_enqueue_spec_nbU B (need_new_batch (st_qthread S)) -> ly_tsd ly = TFIB_TSD ->
amreal tfibsegs (free p (call_trace ly (pc_free_ra0 Tfib_code) regs ch) S) W (cfg_at tfibsegs (pc_wrap_free Tfib_code) regs mem md) (FSU.free_leafU tfibsegs B ly S UP W regs mem md p n).
Proof.
intros B LAWS TB ly S UP W regs mem md p n ch PREU HBLK HOUT HA0 HU ND IA1 U1 D1 Q1 HTSD.
destruct PREU as (PRE & OKU & POU).
pose proof (tr_admit_call _ _ _ _ _ _ HU) as HU'. eapply afree_mid_armU; eassumption.
Qed.
(* lib/B/YFfz.v:549 afree_drn, any UP. *)
Theorem afree_drnU : forall B, AR_laws tfibsegs B -> TfibSyms B -> forall ly S UP W regs mem md p n ch,
FSU.acall_preU tfibsegs B ly S UP W regs mem md ch -> In (p, n) (blocks S) ->
(forall r, In r UP -> fst r + snd r <= sptr_addr B ly p \/ sptr_addr B ly p + req_size n <= fst r) ->
YK11.getr regs 10 = w64 (sptr_addr B ly p) ->
In (call_trace ly (pc_free_ra0 Tfib_code) regs ch) (as_universe B) \/ st_nev S < EV_MAX ->
kQuarantineCacheMax < qc_bytes (st_qthread S) + req_size n + (if need_new_batch (st_qthread S) then kBatchBytes else 0) ->
tfib_ialloc_spec -> tfib_unwind_spec -> tfib_depot_spec B -> FK.tfib_enqueue_spec_nbU B (need_new_batch (st_qthread S)) -> FK.tfib_drain_specU B ->
ly_tsd ly = TFIB_TSD ->
amreal tfibsegs (free p (call_trace ly (pc_free_ra0 Tfib_code) regs ch) S) W (cfg_at tfibsegs (pc_wrap_free Tfib_code) regs mem md) (FSU.free_leafU tfibsegs B ly S UP W regs mem md p n).
Proof.
intros B LAWS TB ly S UP W regs mem md p n ch PREU HBLK HOUT HA0 HU DR IA1 U1 D1 Q1 D0 HTSD.
destruct PREU as (PRE & OKU & POU).
pose proof (tr_admit_call _ _ _ _ _ _ HU) as HU'. eapply afree_drn_armU; eassumption.
Qed.
End d.
