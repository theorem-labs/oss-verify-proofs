(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AFer.v, with its module paths changed, names TfibSyms -> BoxregSyms and its addresses moved to libreac/fuzz_boxreg's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/AFer.v, with its module paths changed; 340 of its 398 lines of code are new or changed and 588 lines of the source are left out. *)
(* Region condition and mu <-> real transfers for the any-U twins of free(NULL) (lib/A/AFg3.v over AFgn / AFh1) and of free with room in the last batch (lib/A/AFfu.v + AFfy.v over AFgi / AFga / AFgc / AFge), used by FSupoisonAllocFnc.v. *)
(* Shared any-U allocator, within-budget units (cgif's EV_MAX 11,776, < 2 GiB per class); the cf form (fuzz_preset / fuzz_reply, YG0dcf.v) bridges to this. *)
(* The machine runs on mem, where UP's shadow bytes read 0xf7; the donor's AR holds of mu = FSupoison.unpoison UP mem.
   - free_null_fixed / free_common_fixed: every byte whose value or presence the walks' seeds and posts move between
     the two readings, and every byte the runs write. free_null_regions_off_ush / free_common_regions_off_ush: none of
     them is a shadow byte of UP. The only premise about UP beyond ARU is afree_realizesU's own (every UP range lies
     outside the freed block [pa, pa + nn)); it is the only source for the freed block's shadow being off UP
     (FSupoisonAllocFK.ush_out_block_shadow).
   - fhn_real / fhc_real: the runs' hyps records (AFgn.free_hyps, AFgi.free_hyps) moved from mu to the real mem.
   - retn_unpoison / at_RET_unpoison / meqi_unpoison: the runs' posts moved from the real final memory to its
     unpoisoned reading, relative to mu.
   - ablocks_keep_le / ablocks_free_keep: the live blocks that keep UP's ranges stay live in free's new state, read
     at any layout above the old one. *)
(* Modified by Theorem Labs, 2026-10: the image-B port (fuzz_state.asan-ubsan) of lib/A/FSupoisonAllocFncR.v at 5cc58921ee2: each lib/A donor is its lib/B twin (AFxx -> YFxx, ABxx -> YBxx, AExx -> YExx), every statement is over B's tfibsegs (lib/B/YB1v.v), the kit is lib/B/FSupoisonAllocR / Rf / Rt; the pcs are by name: pc_wrap_free Tfib_code. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG0f YG0v YG0n YG0d YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1w YE3d YFeq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YFgn YFh1 YFgi YFge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison FSupoisonU.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSupoisonAllocR FSupoisonAllocFK.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module FSP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.
Module FSU := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonU.
Module FAR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSupoisonAllocR.
Module FK := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSupoisonAllocFK.
(* Picks the disjunct of a "fixed" goal that lia proves. *)
Ltac pick_disj := first [ left; lia | right; pick_disj | lia ].
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. Generic: presence through unpoison, a kept chunk, the configuration at the return address.                    *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Lemma apresent_unpoison_mono : forall (H : word -> bool) UP (m1 m2 : word -> option byte),
  (forall a, apresent H m1 a -> apresent H m2 a) ->
  forall a, apresent H (FSP.unpoison UP m1) a -> apresent H (FSP.unpoison UP m2) a.
Proof.
intros H UP m1 m2 MO a [Hh [b Hb]]. split; [exact Hh|]. unfold FSP.unpoison in *.
destruct (FSP.in_ush UP (bv_unsigned (Z_to_bv 64 a))) eqn:E; [eexists; reflexivity|].
destruct (MO a (conj Hh (ex_intro _ b Hb))) as [_ X]. exact X.
Qed.
Lemma ush_not_offU : forall UP s, FSP.in_ush UP s = true -> 0 <= s < 2 ^ 64 -> ~ FAR.offU UP s.
Proof. intros UP s E Hs O. unfold FAR.offU in O. rewrite Z.mod_small in O by lia. congruence. Qed.
Lemma in_upd_chunk_other : forall l k x, In x l -> ck_beg x <> ck_beg k -> In x (upd_chunk l k).
Proof.
induction l as [|k0 t IH]; intros k x Hx Hne; [destruct Hx|]. cbn [upd_chunk].
destruct (sptr_eqb (ck_beg k0) (ck_beg k)) eqn:E.
- apply sptr_eqb_spec in E. destruct Hx as [<-|Hx]; [exfalso; exact (Hne E) | right; exact Hx].
- destruct Hx as [<-|Hx]; [left; reflexivity | right; exact (IH k x Hx Hne)].
Qed.
Lemma nodup_beg_inj : forall (l : list chunk) a b, List.NoDup (map ck_beg l) -> In a l -> In b l -> ck_beg a = ck_beg b -> a = b.
Proof.
intros l a b ND Ha Hb E. destruct (In_split_beg l a Ha ND) as (l1 & l2 & -> & N1 & N2).
apply in_app_iff in Hb as [Hb|[Hb|Hb]].
- exfalso. apply N1. rewrite E. apply in_map. exact Hb.
- exact Hb.
- exfalso. apply N2. rewrite E. apply in_map. exact Hb.
Qed.
Lemma cfg_ra : forall (regs regs' : bvmap 5 word) (m : word -> option byte) md',
  mkCfg (YK11.mkst regs' (getr regs 1) m (seg_rom tfibsegs)) md' = cfg_at tfibsegs (raZ regs) regs' m md'.
Proof. intros regs regs' m md'. unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. Live blocks across free and across a layout above the old one.                                                *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Lemma sptr_addr_chunk_le : forall B ly ly' S x, Wf (as_universe B) S -> layout_le (length (st_secs S)) ly ly' ->
  In x (st_chunks S) -> sptr_addr B ly' (ck_user x) = sptr_addr B ly (ck_user x).
Proof.
intros B ly ly' S x WF LE Hx. apply (sptr_addr_le B ly ly' (length (st_secs S))); [exact LE|].
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ WF) x Hx) as [_ C]. unfold ck_user.
destruct (ck_beg x) as [|o|r o|c q]; cbn; try exact I. destruct C as (_ & _ & sm & Hsm & _). eapply nth_error_lt. exact Hsm.
Qed.
Lemma ablocks_chunk_in : forall B ly S x, In x (st_chunks S) -> ck_state x = CAllocated ->
  In (sptr_addr B ly (ck_user x), ck_req x) (ablocks B ly S).
Proof.
intros B ly S x Hx Hs. unfold ablocks, blocks. rewrite map_map.
apply (in_map (fun k => (sptr_addr B ly (ck_user k), ck_req k))). apply filter_In. split; [exact Hx|].
unfold is_alloc. rewrite Hs. reflexivity.
Qed.
Lemma ablocks_chunk_of : forall B ly S q m, In (q, m) (ablocks B ly S) ->
  exists x, In x (st_chunks S) /\ ck_state x = CAllocated /\ q = sptr_addr B ly (ck_user x) /\ m = ck_req x.
Proof.
intros B ly S q m H. unfold ablocks, blocks in H. rewrite map_map in H. apply in_map_iff in H as (x & E & Hx).
apply filter_In in Hx as [Hx Ha]. injection E as <- <-. exists x. split; [exact Hx|]. split; [|split; reflexivity].
unfold is_alloc in Ha. destruct (ck_state x); [reflexivity | discriminate].
Qed.
Lemma ablocks_keep_le : forall B ly ly' S S', Wf (as_universe B) S -> layout_le (length (st_secs S)) ly ly' ->
  (forall x, In x (st_chunks S) -> In x (st_chunks S')) ->
  forall q m, In (q, m) (ablocks B ly S) -> In (q, m) (ablocks B ly' S').
Proof.
intros B ly ly' S S' WF LE KEEP q m H. destruct (ablocks_chunk_of B ly S q m H) as (x & Hx & Hs & -> & ->).
rewrite <- (sptr_addr_chunk_le B ly ly' S x WF LE Hx). exact (ablocks_chunk_in B ly' S' x (KEEP x Hx) Hs).
Qed.
(* free of chunk k: every other live block of S stays live in a state that keeps S's other chunks. *)
Lemma ablocks_free_keep : forall B ly ly' S S' k, Wf (as_universe B) S -> layout_le (length (st_secs S)) ly ly' ->
  In k (st_chunks S) -> (forall x, In x (st_chunks S) -> ck_beg x <> ck_beg k -> In x (st_chunks S')) ->
  forall q m, In (q, m) (ablocks B ly S) -> (q, m) <> (sptr_addr B ly (ck_user k), ck_req k) ->
  In (q, m) (ablocks B ly' S').
Proof.
intros B ly ly' S S' k WF LE Hk KEEP q m H NE. destruct (ablocks_chunk_of B ly S q m H) as (x & Hx & Hs & -> & ->).
destruct (sptr_eqb (ck_beg x) (ck_beg k)) eqn:Eb.
- apply sptr_eqb_spec in Eb. exfalso. apply NE.
  rewrite (nodup_beg_inj (st_chunks S) x k (wf_chunks_nodup _ _ _ _ _ WF) Hx Hk Eb). reflexivity.
- assert (Eb' : ck_beg x <> ck_beg k) by (intros EE; rewrite EE, sptr_eqb_refl in Eb; discriminate).
  rewrite <- (sptr_addr_chunk_le B ly ly' S x WF LE Hx). exact (ablocks_chunk_in B ly' S' x (KEEP x Hx Eb') Hs).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. Where UP is not: a zone3 range and the image are application memory.                                          *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Lemma img_offU : forall B ly S UP W mem md a, FSP.ARU tfibsegs B ly S UP W mem md ->
  TFIB_IMG_LO <= a < TFIB_IMG_END -> FAR.offU UP a.
Proof.
intros B ly S UP W mem md a H Ha. apply (FAR.offU_low B ly S UP W mem md a H).
unfold TFIB_IMG_LO, TFIB_IMG_END, SHADOW_OFF in *. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 4. free(NULL): lib/B/YFg3.v over YFgn.free_hyps / YFh1.segN / YFh1.at_RETN.                                      *)
(* ---------------------------------------------------------------------------------------------------------------- *)
(* The bytes the null walk fixes: its stack window, the image (the seed's literal cells, TSD, TP, the internal
   allocator's IZONE), the thread object (its head cells and t_unwinding) and the C block. Its write window
   (YFgn.WIN plus YFgn.IZONE) lies inside. *)
Definition free_null_fixed (ly : alayout) (regs : bvmap 5 word) (a : Z) : Prop :=
  (spZ regs - ASTACK <= a < spZ regs) \/ (TFIB_IMG_LO <= a < TFIB_IMG_END) \/
  (ly_T ly <= a < ly_T ly + kThreadObjSize) \/ (ly_C ly <= a < ly_C ly + 256).

Lemma null_win_fixed : forall ly regs a, YFgn.WIN ly regs a \/ YFgn.IZONE a -> free_null_fixed ly regs a.
Proof.
intros ly regs a [[X|X]|X]; unfold free_null_fixed, spZ.
- left. exact X.
- right; right; left. unfold t_unwinding, kThreadObjSize in *. lia.
- right; left. unfold YFgn.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IMG_LO, TFIB_IMG_END in *. lia.
Qed.

Lemma free_null_regions_off_ush : forall B ly S UP W mem md regs ch ii,
  FSP.ARU tfibsegs B ly S UP W mem md -> YFgn.free_hyps W ly regs (FSP.unpoison UP mem) ch ii ->
  forall a, free_null_fixed ly regs a -> FAR.offU UP a.
Proof.
intros B ly S UP W mem md regs ch ii H FH a Ha.
pose proof (YFgn.LYB W ly regs (FSP.unpoison UP mem) ch ii FH) as (ZT & _ & _ & _ & _ & _ & ZC & _).
pose proof (YFgn.fh_Hsp W ly regs (FSP.unpoison UP mem) ch ii FH) as (S1 & S2 & S3).
unfold free_null_fixed, spZ in Ha. destruct Ha as [X|[X|[X|X]]].
- apply (FAR.stack_offU B ly S UP W mem md a H). unfold ASTACK in *. lia.
- exact (img_offU B ly S UP W mem md a H X).
- exact (FK.offU_zone3 B ly S UP W mem md H _ _ a ZT X).
- exact (FK.offU_zone3 B ly S UP W mem md H _ _ a ZC X).
Qed.

(* The run's hyps record on the real memory (Method step 2). *)
Lemma fhn_real : forall B ly S UP W mem md regs ch ii, FSP.ARU tfibsegs B ly S UP W mem md ->
  YFgn.free_hyps W ly regs (FSP.unpoison UP mem) ch ii -> YFgn.free_hyps W ly regs mem ch ii.
Proof.
intros B ly S UP W mem md regs ch ii H FH.
pose proof (free_null_regions_off_ush B ly S UP W mem md regs ch ii H FH) as OFF.
pose proof (YFgn.LYB W ly regs (FSP.unpoison UP mem) ch ii FH) as (ZT & ZT2 & _ & _ & _ & _ & ZC & ZC2 & _).
assert (VI : forall a (w : nat) v, TFIB_IMG_LO <= a -> a + Z.of_nat w <= TFIB_IMG_END ->
  val_mem tfibsegs (mrestrict (w_H W) (FSP.unpoison UP mem)) a w v -> val_mem tfibsegs (mrestrict (w_H W) mem) a w v).
{ intros a w v L1 L2 V. apply (FAR.val_mem_of_unpoison _ UP); [|exact V]. intros k Hk. apply OFF.
  unfold free_null_fixed. right; left. lia. }
pose proof FH as FH'. destruct FH' as [LY IMG Hp10 Htp Hra Hra4096 Hsp Hsp_al Hch HIAL IA1 U1 SEED].
constructor; try assumption.
- assert (CP : chain_pre ly (aview tfibsegs (w_H W) (FSP.unpoison UP mem)) regs ch) by (split; [exact Hra4096 | exact Hch]).
  destruct (FAR.chain_pre_real B ly S UP W regs mem md ch H ltac:(destruct Hsp as (HS1 & HS2 & HS3); unfold spZ, ASTACK in *; lia) CP) as [_ C]. exact C.
- destruct HIAL as (I1 & I2 & I3 & I4).
  split; [apply VI; [unfold TFIB_IAL_FLAG, TFIB_IMG_LO; lia | cbn [Z.of_nat]; unfold TFIB_IAL_FLAG, TFIB_IMG_END; lia | exact I1]|].
  split; [apply VI; [unfold TFIB_IAL_FLAG, TFIB_IMG_LO; lia | cbn [Z.of_nat]; unfold TFIB_IAL_FLAG, TFIB_IMG_END; lia | exact I2]|].
  split.
  + destruct ii; destruct I3 as [I3a I3b]; split;
    (apply VI; [unfold TFIB_IAL_W, TFIB_IMG_LO; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold TFIB_IAL_W, TFIB_IMG_END; lia | assumption]).
  + intros a Ha. rewrite <- (FAR.mbyte_unpoison (w_H W) UP mem a); [exact (I4 a Ha)|].
    apply OFF. unfold free_null_fixed. right; left.
    unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W, TFIB_IMG_LO, TFIB_IMG_END in *. lia.
- assert (RG : FAR.regions_offU UP (YFgn.E0 ly regs ch) (ss_mem YFgn.SS0)).
  { intros r a Hr Ha. apply OFF. change (ss_mem YFgn.SS0) with YFgn.REG0 in Hr.
    unfold YFgn.REG0, flit1, flit4, flit8, flits8, fatom8, aC, aT, aSHB in Hr. cbn [In] in Hr.
    assert (BT : 0 <= ly_T ly /\ ly_T ly + kThreadObjSize < 2 ^ 64) by (ceil; unfold zone3, kThreadObjSize, ASAN_CEIL in *; lia).
    assert (BC : 0 <= ly_C ly /\ ly_C ly + 256 < 2 ^ 64) by (ceil; unfold zone3, ASAN_CEIL in *; lia).
    repeat (destruct Hr as [<-|Hr];
      [cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val length Z.of_nat Pos.of_succ_nat Pos.succ] in Ha;
       rewrite ?(YFgn.E2 ly regs ch), ?(YFgn.EaT ly regs ch), ?(YFgn.EaC ly regs ch) in Ha; unfold w64 in Ha;
       rewrite ?unsigned_lit_small in Ha by (unfold kThreadObjSize in *; lia);
       unfold free_null_fixed, spZ, TFIB_IMG_LO, TFIB_IMG_END, TFIB_TP, TFIB_TSD, ASTACK, t_unwinding, kThreadObjSize in *;
       pick_disj|]).
    destruct Hr. }
  apply (proj1 (FAR.st_ok_unpoison_iff UP (YFgn.E0 ly regs ch) YFgn.SS0 (w_H W) regs (w64 (pc_wrap_free Tfib_code)) mem (seg_rom tfibsegs) RG)).
  exact SEED.
Qed.

(* The null run's post on the real final memory read on its unpoisoned version relative to mu (Method step 4), and
   UP's bytes still 0xf7 after the run: the run writes only YFgn.WIN and YFgn.IZONE. *)
Lemma retn_unpoison : forall B ly S UP W mem md regs ch ii W' c', FSP.ARU tfibsegs B ly S UP W mem md ->
  YFgn.free_hyps W ly regs (FSP.unpoison UP mem) ch ii -> YFh1.at_RETN W ly regs mem md W' c' ->
  exists regs' mem' mat, W' = W /\
    c' = mkCfg (YK11.mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
    YFh1.at_RETN W ly regs (FSP.unpoison UP mem) md W
      (mkCfg (YK11.mkst regs' (getr regs 1) (FSP.unpoison UP mem') (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md)) /\
    FSP.upoisoned tfibsegs W mem' UP.
Proof.
intros B ly S UP W mem md regs ch ii W' c' H FH (-> & regs' & mem' & mat & -> & RP & (MQ & IP) & UNW & PRES).
pose proof (free_null_regions_off_ush B ly S UP W mem md regs ch ii H FH) as OFF.
pose proof (YFgn.LYB W ly regs (FSP.unpoison UP mem) ch ii FH) as (ZT & _).
assert (VI : forall a (w : nat) v, TFIB_IMG_LO <= a -> a + Z.of_nat w <= TFIB_IMG_END ->
  val_mem tfibsegs (mrestrict (w_H W) mem') a w v -> val_mem tfibsegs (mrestrict (w_H W) (FSP.unpoison UP mem')) a w v).
{ intros a w v L1 L2 V. apply (FAR.val_mem_to_unpoison _ UP); [|exact V]. intros k Hk. apply OFF.
  unfold free_null_fixed. right; left. lia. }
exists regs', mem', mat. split; [reflexivity|]. split; [reflexivity|]. split.
- split; [reflexivity|]. exists regs', (FSP.unpoison UP mem'), mat. split; [reflexivity|]. split; [exact RP|].
  split; [split|split].
  + intros x Hx Hz. unfold FSP.unpoison. destruct (FSP.in_ush UP (bv_unsigned x)); [reflexivity | exact (MQ x Hx Hz)].
  + destruct IP as (I1 & I2 & I3 & I4 & I5).
    split; [apply VI; [unfold TFIB_IAL_FLAG, TFIB_IMG_LO; lia | cbn [Z.of_nat]; unfold TFIB_IAL_FLAG, TFIB_IMG_END; lia | exact I1]|].
    split; [apply VI; [unfold TFIB_IAL_FLAG, TFIB_IMG_LO; lia | cbn [Z.of_nat]; unfold TFIB_IAL_FLAG, TFIB_IMG_END; lia | exact I2]|].
    split; [apply VI; [unfold TFIB_IAL_W, TFIB_IMG_LO; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold TFIB_IAL_W, TFIB_IMG_END; lia | exact I3]|].
    split; [apply VI; [unfold TFIB_IAL_W, TFIB_IMG_LO; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold TFIB_IAL_W, TFIB_IMG_END; lia | exact I4]|].
    intros a Ha. rewrite (FAR.mbyte_unpoison (w_H W) UP mem' a); [exact (I5 a Ha)|].
    apply OFF. unfold free_null_fixed. right; left.
    unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W, TFIB_IMG_LO, TFIB_IMG_END in *. lia.
  + apply (FAR.val_mem_to_unpoison _ UP); [|exact UNW]. intros k Hk. apply OFF. unfold free_null_fixed.
    right; right; left. unfold t_unwinding, kThreadObjSize in *. lia.
  + intros a Ha. apply FAR.apresent_to_unpoison. exact (PRES a Ha).
- apply (FAR.upoisoned_keep UP W W mem mem' (FSP.ARU_poisoned tfibsegs B ly S UP W mem md H)). intros s Hs.
  pose proof (FSP.ush_range tfibsegs B ly S UP W mem md s H Hs) as Rs.
  apply FSP.aview_at. apply MQ; rewrite (FSP.wz s Rs); intros X;
  exact (ush_not_offU UP s Hs Rs (OFF s (null_win_fixed ly regs s ltac:(tauto)))).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 5. free with room in the last batch: lib/B/YFfu.v + YFfy.v over YFgi.free_hyps, YFga.segA, YFgc.segB,            *)
(*    YFge.segC / YFge.at_RET, with the depot call in between.                                                      *)
(* ---------------------------------------------------------------------------------------------------------------- *)
(* The bytes the common walk fixes: its stack window (the depot call's included), the image (literal cells, TSD, TP,
   IZONE, the depot's table and its store), the image's shadow (the globals' shadow cells of Tfib_const), the thread
   object, the C block, the D block, the depot's node and store blocks, the freed chunk's header and user words
   [pa - 16, pa + N8v), the primary space (the last batch), and the freed block's shadow [SPv, SPv + CNT8v). *)
Definition free_common_fixed (ly : alayout) (regs : bvmap 5 word) (pa nn : Z) (a : Z) : Prop :=
  (spZ regs - ASTACK <= a < spZ regs) \/ (TFIB_IMG_LO <= a < TFIB_IMG_END) \/
  (SHADOW_OFF + TFIB_IMG_LO / 8 <= a < SHADOW_OFF + TFIB_IMG_END / 8) \/
  (ly_T ly <= a < ly_T ly + kThreadObjSize) \/ (ly_C ly <= a < ly_C ly + 256) \/ (ly_D ly <= a < ly_D ly + 4096) \/
  (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize) \/
  (pa - 16 <= a < pa + YFgi.N8v nn) \/ (ly_space ly <= a < ly_space ly + kSpaceSize) \/
  (YFgi.SPv pa <= a < YFgi.SPv pa + YFgi.CNT8v nn).

(* The run's write window, the internal allocator's zone, the depot's zone, the depot call's stack window and the
   freed block's shadow lie in the fixed bytes. *)
Lemma win_fixed : forall W ly regs mem0 ch pa nn hb1 q lastb j1 j2 j3 ii,
  YFgi.free_hyps W ly regs mem0 ch pa nn hb1 q lastb j1 j2 j3 ii ->
  forall a, YFgi.WIN ly regs pa lastb a -> free_common_fixed ly regs pa nn a.
Proof.
intros W ly regs mem0 ch pa nn hb1 q lastb j1 j2 j3 ii FH a X.
pose proof (YFgi.derived_ranges W ly regs mem0 ch pa nn hb1 q lastb j1 j2 j3 ii FH) as DR.
pose proof (YFgi.N8_ge W ly regs mem0 ch pa nn hb1 q lastb j1 j2 j3 ii FH) as [N8a N8b].
unfold YFgi.WIN, YFgi.WINT, YFgi.WINB in X. unfold free_common_fixed, spZ.
unfold t_qc, t_unwinding, t_stats, kThreadObjSize, kBatchBytes, kSpaceSize, YFgi.SLOTv, YFgi.Bv, YFgi.BCv in *.
destruct X as [X|[[X|[X|X]]|[X|[X|[X|X]]]]]; pick_disj.
Qed.
Lemma izone_fixed : forall ly regs pa nn a, YFgi.IZONE a -> free_common_fixed ly regs pa nn a.
Proof.
intros ly regs pa nn a X. unfold free_common_fixed. right; left.
unfold YFgi.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IMG_LO, TFIB_IMG_END in *. lia.
Qed.
Lemma dzone_fixed : forall ly regs pa nn a, YFgi.DZONE ly a -> free_common_fixed ly regs pa nn a.
Proof.
intros ly regs pa nn a X. unfold YFgi.DZONE in X. unfold free_common_fixed, TFIB_IMG_LO, TFIB_IMG_END.
destruct X as [X|[X|X]]; pick_disj.
Qed.
Lemma dstack_fixed : forall ly regs pa nn a, spZ regs - 2176 - DEP_STK <= a < spZ regs - 2176 ->
  free_common_fixed ly regs pa nn a.
Proof. intros ly regs pa nn a X. unfold free_common_fixed. left. unfold DEP_STK, ASTACK in *. lia. Qed.
Lemma freed_fixed : forall ly regs pa nn a, YFgi.SPv pa <= a < YFgi.SPv pa + YFgi.CNT8v nn ->
  free_common_fixed ly regs pa nn a.
Proof. intros ly regs pa nn a X. unfold free_common_fixed. do 10 right. exact X. Qed.

Lemma free_common_regions_off_ush : forall B, AR_laws tfibsegs B ->
  forall ly S UP W mem md regs ch pa nn hb1 q lastb j1 j2 j3 ii,
  FSP.ARU tfibsegs B ly S UP W mem md -> (forall r, In r UP -> fst r + snd r <= pa \/ pa + nn <= fst r) ->
  YFgi.free_hyps W ly regs (FSP.unpoison UP mem) ch pa nn hb1 q lastb j1 j2 j3 ii ->
  forall a, free_common_fixed ly regs pa nn a -> FAR.offU UP a.
Proof.
intros B LAWS ly S UP W mem md regs ch pa nn hb1 q lastb j1 j2 j3 ii H OUT FH a Ha.
pose proof (YFgi.LYB W ly regs (FSP.unpoison UP mem) ch pa nn hb1 q lastb j1 j2 j3 ii FH)
  as (ZT & _ & P1 & P2 & P3 & P4 & ZC & _ & ZNB & _ & ZSB & _).
pose proof (YFgi.LYBD W ly regs (FSP.unpoison UP mem) ch pa nn hb1 q lastb j1 j2 j3 ii FH) as (ZD & _).
pose proof (YFgi.fh_Hp W ly regs (FSP.unpoison UP mem) ch pa nn hb1 q lastb j1 j2 j3 ii FH) as ZP.
pose proof (YFgi.fh_Hsp W ly regs (FSP.unpoison UP mem) ch pa nn hb1 q lastb j1 j2 j3 ii FH) as (S1 & S2 & S3).
pose proof (YFgi.fh_Hnn W ly regs (FSP.unpoison UP mem) ch pa nn hb1 q lastb j1 j2 j3 ii FH) as Hnn.
pose proof (YFgi.derived_ranges W ly regs (FSP.unpoison UP mem) ch pa nn hb1 q lastb j1 j2 j3 ii FH)
  as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & _).
unfold free_common_fixed, spZ in Ha. destruct Ha as [X|[X|[X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]]].
- apply (FAR.stack_offU B ly S UP W mem md a H). unfold ASTACK in *. lia.
- exact (img_offU B ly S UP W mem md a H X).
- change (TFIB_IMG_LO / 8) with 8192 in X. change (TFIB_IMG_END / 8) with 784896 in X.
  replace a with (shadow_addr (8 * (a - SHADOW_OFF)))
    by (unfold shadow_addr; rewrite (Z.mul_comm 8 (a - SHADOW_OFF)), Z.div_mul by lia; lia).
  apply (FK.offU_img_shadow B LAWS ly S UP W mem md _ H). unfold TFIB_IMG_LO, TFIB_IMG_END, SHADOW_OFF in *. lia.
- exact (FK.offU_zone3 B ly S UP W mem md H _ _ a ZT X).
- exact (FK.offU_zone3 B ly S UP W mem md H _ _ a ZC X).
- exact (FK.offU_zone3 B ly S UP W mem md H _ _ a ZD X).
- exact (FK.offU_zone3 B ly S UP W mem md H _ _ a ZNB X).
- exact (FK.offU_zone3 B ly S UP W mem md H _ _ a ZSB X).
- exact (FK.offU_zone3 B ly S UP W mem md H _ _ a ZP ltac:(unfold YFgi.N8v in *; lia)).
- apply (FAR.offU_high B ly S UP W mem md a H). ceil. unfold kSpaceSize, kPrimResvSize, kHighMemBeg, ASAN_CEIL in *. lia.
- unfold FAR.offU. rewrite Z.mod_small by (unfold YFgi.SPv, SHADOW_OFF, kHighMemBeg in *; lia).
  destruct (FSP.in_ush UP a) eqn:E; [|reflexivity]. exfalso.
  apply (FK.ush_out_block_shadow B ly S UP pa nn a ltac:(lia) (proj1 (proj2 H)) OUT E).
  assert (E1 : (pa + nn - 1) / 8 = pa / 8 + (nn - 1) / 8).
  { replace (pa + nn - 1) with ((nn - 1) + (pa / 8) * 8) by lia. rewrite Z.div_add by lia. lia. }
  pose proof (Z.div_mod (nn - 1) 8 ltac:(lia)) as M1. pose proof (Z.mod_pos_bound (nn - 1) 8 ltac:(lia)) as M2.
  rewrite E1. unfold YFgi.SPv, YFgi.CNT8v, YFgi.N8v in *. lia.
Qed.

(* The run's hyps record on the real memory (Method step 2). hb1, j1-j3 keep their mu values. *)
Lemma fhc_real : forall B, AR_laws tfibsegs B ->
  forall ly S UP W mem md regs ch pa nn hb1 q lastb j1 j2 j3 ii,
  FSP.ARU tfibsegs B ly S UP W mem md -> (forall r, In r UP -> fst r + snd r <= pa \/ pa + nn <= fst r) ->
  YFgi.free_hyps W ly regs (FSP.unpoison UP mem) ch pa nn hb1 q lastb j1 j2 j3 ii ->
  YFgi.free_hyps W ly regs mem ch pa nn hb1 q lastb j1 j2 j3 ii.
Proof.
intros B LAWS ly S UP W mem md regs ch pa nn hb1 q lastb j1 j2 j3 ii H OUT FH.
pose proof (free_common_regions_off_ush B LAWS ly S UP W mem md regs ch pa nn hb1 q lastb j1 j2 j3 ii H OUT FH) as OFF.
pose proof (YFgi.derived_ranges W ly regs (FSP.unpoison UP mem) ch pa nn hb1 q lastb j1 j2 j3 ii FH) as DR.
pose proof (YFgi.N8_ge W ly regs (FSP.unpoison UP mem) ch pa nn hb1 q lastb j1 j2 j3 ii FH) as [N8a N8b].
pose proof (YFgi.LYB W ly regs (FSP.unpoison UP mem) ch pa nn hb1 q lastb j1 j2 j3 ii FH)
  as (ZT & ZT2 & _ & _ & _ & _ & ZC & ZC2 & _).
assert (VI : forall a (w : nat) v, TFIB_IMG_LO <= a -> a + Z.of_nat w <= TFIB_IMG_END ->
  val_mem tfibsegs (mrestrict (w_H W) (FSP.unpoison UP mem)) a w v -> val_mem tfibsegs (mrestrict (w_H W) mem) a w v).
{ intros a w v L1 L2 V. apply (FAR.val_mem_of_unpoison _ UP); [|exact V]. intros k Hk. apply OFF.
  unfold free_common_fixed. right; left. lia. }
pose proof FH as FH'.
destruct FH' as [LY Hp10 Htp Hra Hra4096 Hsp Hsp_al Hch Hp IMG Hp_al Hnn Hhb1 Hhb1m Hp_static Hp_pres Hsh_pres Hq
  Hlastb HB HB_al HBp HB_pres Hjunk HIAL IA1 U1 SEED].
constructor; try assumption.
- assert (CP : chain_pre ly (aview tfibsegs (w_H W) (FSP.unpoison UP mem)) regs ch) by (split; [exact Hra4096 | exact Hch]).
  destruct (FAR.chain_pre_real B ly S UP W regs mem md ch H ltac:(destruct Hsp as (HS1 & HS2 & HS3); unfold spZ, ASTACK in *; lia) CP) as [_ C]. exact C.
- intros a Ha. apply (FAR.apresent_of_unpoison _ UP); [|exact (Hp_pres a Ha)]. apply OFF.
  unfold free_common_fixed. unfold YFgi.N8v in *. pick_disj.
- intros a Ha. apply (FAR.apresent_of_unpoison _ UP); [|exact (Hsh_pres a Ha)]. apply OFF.
  exact (freed_fixed ly regs pa nn a Ha).
- intros a Ha. apply (FAR.apresent_of_unpoison _ UP); [|exact (HB_pres a Ha)]. apply OFF.
  unfold free_common_fixed, kBatchBytes, kSpaceSize, YFgi.SLOTv, YFgi.Bv, YFgi.BCv in *. pick_disj.
- destruct HIAL as (I1 & I2 & I3 & I4).
  split; [apply VI; [unfold TFIB_IAL_FLAG, TFIB_IMG_LO; lia | cbn [Z.of_nat]; unfold TFIB_IAL_FLAG, TFIB_IMG_END; lia | exact I1]|].
  split; [apply VI; [unfold TFIB_IAL_FLAG, TFIB_IMG_LO; lia | cbn [Z.of_nat]; unfold TFIB_IAL_FLAG, TFIB_IMG_END; lia | exact I2]|].
  split.
  + destruct ii; destruct I3 as [I3a I3b]; split;
    (apply VI; [unfold TFIB_IAL_W, TFIB_IMG_LO; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold TFIB_IAL_W, TFIB_IMG_END; lia | assumption]).
  + intros a Ha. rewrite <- (FAR.mbyte_unpoison (w_H W) UP mem a); [exact (I4 a Ha)|].
    apply OFF. unfold free_common_fixed. right; left.
    unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W, TFIB_IMG_LO, TFIB_IMG_END in *. lia.
- assert (RG : FAR.regions_offU UP (YFgi.E0 ly regs ch pa nn hb1 q lastb j1 j2 j3) (ss_mem YFgi.SS0)).
  { intros r a Hr Ha. apply OFF. change (ss_mem YFgi.SS0) with YFgi.REG0 in Hr.
    unfold YFgi.REG0, flit1, flit4, flit8, flits8, fatom8, aC, aT, aSHB, aB, aSLOT in Hr. cbn [In] in Hr.
    assert (BT : 0 <= ly_T ly /\ ly_T ly + kThreadObjSize < 2 ^ 64) by (ceil; unfold zone3, kThreadObjSize, ASAN_CEIL in *; lia).
    assert (BC : 0 <= ly_C ly /\ ly_C ly + 256 < 2 ^ 64) by (ceil; unfold zone3, ASAN_CEIL in *; lia).
    assert (BP : 0 <= pa /\ pa + YFgi.N8v nn < 2 ^ 64) by (ceil; unfold zone3, ASAN_CEIL in *; lia).
    assert (BB : 0 <= YFgi.Bv ly lastb /\ YFgi.Bv ly lastb + kBatchBytes < 2 ^ 64)
      by (ceil; unfold kSpaceSize, kBatchBytes, kHighMemBeg, ASAN_CEIL in *; lia).
    assert (BS : 0 <= YFgi.SLOTv ly lastb /\ YFgi.SLOTv ly lastb + 8 < 2 ^ 64)
      by (ceil; unfold kSpaceSize, kBatchBytes, kHighMemBeg, ASAN_CEIL in *; lia).
    repeat (destruct Hr as [<-|Hr];
      [cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val length Z.of_nat Pos.of_succ_nat Pos.succ] in Ha;
       rewrite ?(YFgi.E2 ly regs ch pa nn hb1 q lastb j1 j2 j3), ?(YFgi.E10 ly regs ch pa nn hb1 q lastb j1 j2 j3), ?Hp10,
         ?(YFgi.EaT ly regs ch pa nn hb1 q lastb j1 j2 j3), ?(YFgi.EaC ly regs ch pa nn hb1 q lastb j1 j2 j3),
         ?(YFgi.EaB ly regs ch pa nn hb1 q lastb j1 j2 j3), ?(YFgi.EaSLOT ly regs ch pa nn hb1 q lastb j1 j2 j3) in Ha;
       unfold w64 in Ha;
       rewrite ?unsigned_lit_small in Ha by (unfold kThreadObjSize, kBatchBytes, YFgi.N8v in *; lia);
       unfold free_common_fixed, spZ, TFIB_IMG_LO, TFIB_IMG_END, TFIB_TP, TFIB_TSD, ASTACK, t_qc, t_unwinding, t_stats,
         kThreadObjSize, kBatchBytes, kSpaceSize, YFgi.SLOTv, YFgi.Bv, YFgi.BCv, YFgi.N8v in *;
       pick_disj|]).
    destruct Hr. }
  apply (proj1 (FAR.st_ok_unpoison_iff UP (YFgi.E0 ly regs ch pa nn hb1 q lastb j1 j2 j3) YFgi.SS0 (w_H W) regs
    (w64 (pc_wrap_free Tfib_code)) mem (seg_rom tfibsegs) RG)).
  exact SEED.
Qed.

(* The segB post's frame (MEQI) read on the unpoisoned readings. *)
Lemma meqi_unpoison : forall B, AR_laws tfibsegs B ->
  forall ly S UP W mem md regs ch pa nn hb1 q lastb j1 j2 j3 ii m,
  FSP.ARU tfibsegs B ly S UP W mem md -> (forall r, In r UP -> fst r + snd r <= pa \/ pa + nn <= fst r) ->
  YFgi.free_hyps W ly regs (FSP.unpoison UP mem) ch pa nn hb1 q lastb j1 j2 j3 ii ->
  YFgi.MEQI W ly regs mem pa lastb m ->
  YFgi.MEQI W ly regs (FSP.unpoison UP mem) pa lastb (FSP.unpoison UP m).
Proof.
intros B LAWS ly S UP W mem md regs ch pa nn hb1 q lastb j1 j2 j3 ii m H OUT FH (MQ & I1 & I2 & I3 & I4 & I5).
pose proof (free_common_regions_off_ush B LAWS ly S UP W mem md regs ch pa nn hb1 q lastb j1 j2 j3 ii H OUT FH) as OFF.
assert (VI : forall a (w : nat) v, TFIB_IMG_LO <= a -> a + Z.of_nat w <= TFIB_IMG_END ->
  val_mem tfibsegs (mrestrict (w_H W) m) a w v -> val_mem tfibsegs (mrestrict (w_H W) (FSP.unpoison UP m)) a w v).
{ intros a w v L1 L2 V. apply (FAR.val_mem_to_unpoison _ UP); [|exact V]. intros k Hk. apply OFF.
  unfold free_common_fixed. right; left. lia. }
split.
- intros x Hx Hz. unfold FSP.unpoison. destruct (FSP.in_ush UP (bv_unsigned x)); [reflexivity | exact (MQ x Hx Hz)].
- split; [apply VI; [unfold TFIB_IAL_FLAG, TFIB_IMG_LO; lia | cbn [Z.of_nat]; unfold TFIB_IAL_FLAG, TFIB_IMG_END; lia | exact I1]|].
  split; [apply VI; [unfold TFIB_IAL_FLAG, TFIB_IMG_LO; lia | cbn [Z.of_nat]; unfold TFIB_IAL_FLAG, TFIB_IMG_END; lia | exact I2]|].
  split; [apply VI; [unfold TFIB_IAL_W, TFIB_IMG_LO; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold TFIB_IAL_W, TFIB_IMG_END; lia | exact I3]|].
  split; [apply VI; [unfold TFIB_IAL_W, TFIB_IMG_LO; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold TFIB_IAL_W, TFIB_IMG_END; lia | exact I4]|].
  intros a Ha. rewrite (FAR.mbyte_unpoison (w_H W) UP m a); [exact (I5 a Ha)|].
  apply OFF. unfold free_common_fixed. right; left.
  unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W, TFIB_IMG_LO, TFIB_IMG_END in *. lia.
Qed.

(* segC's post on the real final memory, read on the unpoisoned readings (Method step 4), with the run's own frame
   (mem' = mem4 outside WIN2 and the freed block's shadow) kept for UP's 0xf7 bytes. *)
Lemma at_RET_unpoison : forall B, AR_laws tfibsegs B ->
  forall ly S UP W mem md regs ch pa nn hb1 q lastb j1 j2 j3 ii mem4 W' c',
  FSP.ARU tfibsegs B ly S UP W mem md -> (forall r, In r UP -> fst r + snd r <= pa \/ pa + nn <= fst r) ->
  YFgi.free_hyps W ly regs (FSP.unpoison UP mem) ch pa nn hb1 q lastb j1 j2 j3 ii ->
  YFge.at_RET W ly regs md pa nn hb1 q lastb mem4 W' c' ->
  exists regs' mem' mat, W' = W /\
    c' = mkCfg (YK11.mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
    YFge.at_RET W ly regs md pa nn hb1 q lastb (FSP.unpoison UP mem4) W
      (mkCfg (YK11.mkst regs' (getr regs 1) (FSP.unpoison UP mem') (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md)) /\
    (forall x : word, ~ YFgi.WIN2 ly regs pa lastb (bv_unsigned x) ->
       ~ (YFgi.SPv pa <= bv_unsigned x < YFgi.SPv pa + YFgi.CNT8v nn) -> mem' x = mem4 x).
Proof.
intros B LAWS ly S UP W mem md regs ch pa nn hb1 q lastb j1 j2 j3 ii mem4 W' c' H OUT FH
  (-> & regs' & mem' & mat & -> & CS & (EQ4 & SH) & PRES & PRESW & VALS).
pose proof (free_common_regions_off_ush B LAWS ly S UP W mem md regs ch pa nn hb1 q lastb j1 j2 j3 ii H OUT FH) as OFF.
pose proof (YFgi.derived_ranges W ly regs (FSP.unpoison UP mem) ch pa nn hb1 q lastb j1 j2 j3 ii FH) as DR.
pose proof (YFgi.N8_ge W ly regs (FSP.unpoison UP mem) ch pa nn hb1 q lastb j1 j2 j3 ii FH) as [N8a N8b].
assert (VT : forall a (w : nat) v, (forall k, (k < w)%nat -> free_common_fixed ly regs pa nn (a + Z.of_nat k)) ->
  val_mem tfibsegs (mrestrict (w_H W) mem') a w v -> val_mem tfibsegs (mrestrict (w_H W) (FSP.unpoison UP mem')) a w v).
{ intros a w v F V. apply (FAR.val_mem_to_unpoison _ UP); [|exact V]. intros k Hk. exact (OFF _ (F k Hk)). }
exists regs', mem', mat. split; [reflexivity|]. split; [reflexivity|]. split; [|exact EQ4].
split; [reflexivity|]. exists regs', (FSP.unpoison UP mem'), mat. split; [reflexivity|]. split; [exact CS|].
split; [split|split; [|split]].
- intros x Hx Hs. unfold FSP.unpoison. destruct (FSP.in_ush UP (bv_unsigned x)); [reflexivity | exact (EQ4 x Hx Hs)].
- intros x Hs. rewrite (FAR.unpoison_offU_w UP mem' x (OFF _ (freed_fixed ly regs pa nn _ Hs))). exact (SH x Hs).
- intros a Ha. apply FAR.apresent_to_unpoison. exact (PRES a Ha).
- intros a Ha. apply FAR.apresent_to_unpoison. exact (PRESW a Ha).
- cbv zeta in VALS |- *. destruct VALS as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10).
  unfold free_common_fixed, spZ, t_qc, t_unwinding, t_stats, kThreadObjSize, kBatchBytes, kSpaceSize,
    YFgi.SLOTv, YFgi.Bv, YFgi.BCv, YFgi.N8v in *.
  split; [apply VT; [intros k Hk; pick_disj | exact V1]|].
  split; [apply VT; [intros k Hk; pick_disj | exact V2]|].
  split; [apply VT; [intros k Hk; pick_disj | exact V3]|].
  split; [apply VT; [intros k Hk; pick_disj | exact V4]|].
  split; [apply VT; [intros k Hk; pick_disj | exact V5]|].
  split; [apply VT; [intros k Hk; pick_disj | exact V6]|].
  split; [apply VT; [intros k Hk; pick_disj | exact V7]|].
  split; [apply VT; [intros k Hk; pick_disj | exact V8]|].
  split; [apply VT; [intros k Hk; pick_disj | exact V9]|].
  apply VT; [intros k Hk; pick_disj | exact V10].
Qed.
End r.
