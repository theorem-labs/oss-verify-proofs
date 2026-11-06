(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMrcSecCutCf.v (commit 3d8ad2aeb77e, H4 cf instance set (reply-rccf); file sha256 dd916a5921b8) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 32 image addresses moved by code-verified function pairs (33 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py); 3 data addresses the tool read as sizes, by the same value MAPS prediction, and 1 pcs named in comments; 1 hand maps (each with its evidence: pinned image bytes, YImgTop, the unit AF twin); no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (lane B1, slice H4): H4's secondary CUT-READ field DMrcSecReads.rc_sec_cut_t at reply's
   image, at the cf layer's cut relation YGcfInstDrainR.ARXr_cf.
   rule 24: proves function __asan::QuarantineCallback::Recycle (0x33e30; RChunk secondary cut / map reads) at reply's cf relation,
   instance of H4's own transports; checker: git grep rc_sec_cut|rc_sec_mapr|rc_reads|rchunk_ok = 0 statements.

   WHAT.  [rc_sec_cut_of_cf]: for every B with TfibSyms B, every IOK with YGcfInstBase.IOK_ok B IOK (the instance
   object is the binary's allocator object, the premise rc_fh_cut_facts_cf takes, YGcfInstRcPrim.v:1160) and every
   Hp, rc_sec_cut_t B (ARXr_cf B IOK Hp): at the secondary arm's call, the instance object, the TSD slot, the image's
   constant cells and the whole cut record DMrcSecFc.sec_cut.
   [rc_sec_cut_nf_of_cf]: the same at the flag-free field DMrcSecNf.rc_sec_cut_nf_t (rcc_pre_sec, rcc_pre_x without
   st_cache_inited X = true, for rcc_pre_x): the derivation below reads no flag, so Section f takes rcc_pre_sec and
   [rc_sec_cut_of_cf] is that theorem through DMiface.rcc_pre_sec_of_x (Theorem Labs, 2026-10-30, lane B1, slice H4;
   rule 24: no function proved, the same reads at one pre conjunct less).

   HOW.  cgif's YFfc.v derives sec_cut from its concrete relation ARm (plus YFf4's MAPX / SX / SECX / LST).  This file
   redoes that derivation statement by statement over ARcfR:
   - ARm's record fields become ARmcfR's (amr_layout, amr_cells over acells_cf, amr_junk over ajunk_cf, amr_areas,
     amr_shadow over shadow_ok_weak_cf, amr_const, amr_tsd, amr_placed); cgif's chunk facts become RL.chunk_facts_cf, its
     map disjointness RL.secmaps_disjoint_cf and its secondaries record wf_sec_cf;
   - the image window img_cover comes from the cf ledger (alc_img) at tfibsegs' first and last segments, as
     YF0x.img_cover_of_ledger does from cgif's ledger;
   - the pre-state facts KFACTS / ARR / geom / MAPX / SECX / SX / sec_in_app are YGcfInstRcSec Section M's;
   - the image's constant cells are amr_const with TfibSyms' ts_const (as DMrcFhCf.cell_lit / cell_sym);
   - the stack facts come from rcc_pre_sec at KSTACK_CF = 2048 >= AFeu.KSTACK = 512;
   - the instance object is IOK_ok at the relation's IOK conjunct.
   The cgif-only size bounds (the map length's and the user size's) are not part of sec_cut (DMrcSecFc.v:10-12), so
   none is derived here. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1w AFeq AFex AFfu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YFfj.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AFew AFeu AFfm AFf3 AFff AFgu AFgx AFgv AFg8 AB13.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseDG AGif2reply DMspec DMiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AFf4 AFfc DMrcSecFc DMrcSecReads DMrcSecNf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG01cf YG03cf YG0ncf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfInstBase YGcfInstDrainR YGcfInstDrainRL YGcfInstRcSec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Local Open Scope am_scope.
Set Printing Depth 100. Set Printing Width 200.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac splits := repeat match goal with |- _ /\ _ => split end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : YGcfNames.CfImg} {cp : CfParams}.
Ltac numconst := ceil; unfold zone3, zone3cases, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kPtrArrayResv, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, KSTACK, TFIB_IMG_END, kBatchBytes, SHADOW_OFF, TFIB_TP, TFIB_TSD, TFIB_INST, A_ALLOCATOR, o_space, o_rinfo, o_sec, o_sec_chunks, o_sec_reserved, o_sec_n, o_sec_sorted, o_sec_stats, o_sec_mutex, kRegionInfoOff, kLowMemEnd, kChunkHeaderSize, kPage, AFgu.GFRAME, AFgx.GFRAME, GDEPTH in *.

Section f.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variable IOK : Z -> Prop.
Variable Hp : list Z.
Hypothesis HIOK : YGcfInstBase.IOK_ok B IOK.
Variables (inst : Z) (ly : alayout) (X : astate) (k : chunk) (cbp : Z) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model).
Variables (r : nat) (o : Z) (sm : secmap) (i : nat).
Local Notation ARXr := (@YGcfInstDrainR.ARXr_cf rc ci cp AImg_reply B IOK Hp).
Hypothesis PRE : @rcc_pre_sec AImg_reply B ARXr inst ly X k cbp W regs mem md.
Hypothesis Hb : ck_beg k = PSec r o.
Hypothesis Hsm : nth_error (st_secs X) r = Some sm.
Hypothesis Hi : nth_error (st_sec_arr X) i = Some r.
Hypothesis Hk : In k (st_chunks X).
Hypothesis Hst : ck_state k = CQuarantined.
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Notation H0 := (w_H W).
Local Notation rd0 := (aview tfibsegs (w_H W) mem).
Local Notation m0 := (mrestrict (w_H W) mem).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation Q := (ly_Q ly).
Local Notation arr := (st_sec_arr X).
Local Notation MAP := (AFg8.MAP ly r).
Local Notation LEN := (AFg8.LEN sm).
Local Notation nA := (AFg8.nA X).
Local Notation hdr := (AFfc.hdr B ly k).
Local Notation hb1 := (AFfc.hb1 B ly k W mem).
Local Notation HWv := (AFfc.HWv B ly k W mem).

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The cut relation's parts.                                                                                        *)
Lemma AR : ARXr inst ly X W mem md. Proof. exact (proj1 PRE). Qed.
Lemma MR : @YGcfInstDrainR.ARcfR rc ci cp tfibsegs B ly X Hp W mem md. Proof. exact (proj1 (proj2 AR)). Qed.
Lemma M : YGcfInstDrainR.ARmcfR B ly X Hp rd0. Proof. exact (proj1 MR). Qed.
Lemma LED : YG0ncf.ALedger_cf tfibsegs ly X md. Proof. exact (proj1 (proj2 MR)). Qed.
Lemma INST : inst = as_inst B. Proof. exact (HIOK inst (proj1 AR)). Qed.
Lemma LO : layout_ok ly. Proof. exact (YGcfInstDrainR.amr_layout _ _ _ _ _ M). Qed.
Lemma HTSD0 : ly_tsd ly = as_tsd B. Proof. exact (YGcfInstDrainR.amr_tsd _ _ _ _ _ M). Qed.
Lemma HTSD : ly_tsd ly = TFIB_TSD. Proof. rewrite HTSD0. exact (ts_tsd _ TB). Qed.
Lemma CONST : Forall (cell_holds B ly rd0) (as_const B ly). Proof. exact (YGcfInstDrainR.amr_const _ _ _ _ _ M). Qed.
Lemma AINST : as_inst B = A_ALLOCATOR. Proof. rewrite (ts_inst _ TB). reflexivity. Qed.

(* AF0x.img_cover_of_ledger over the cf ledger. *)
Lemma IMG : img_cover ly.
Proof.
pose proof LED as L. split.
- destruct (YG0ncf.alc_img _ _ _ _ L Asan.Asan_segment_000 ltac:(left; reflexivity)) as [H _].
  cbn in H. unfold TFIB_IMG_LO. lia.
- destruct (YG0ncf.alc_img _ _ _ _ L Asan.Asan_segment_003 ltac:(do 3 right; left; reflexivity)) as [_ H].
  cbn in H. unfold TFIB_IMG_END. lia.
Qed.

Lemma HSP : ly_stk_lo ly + KSTACK <= sp0 <= ly_stk_hi ly.
Proof. destruct PRE as (_ & _ & _ & _ & Hlo & Hcb1 & Hcb2 & _). unfold spZ in *. unfold sp0, KSTACK, KSTACK_CF in *. lia. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The chunk, the map and the layout (AFfc.v:75-150, AFf4.v:212-278).                                              *)
Lemma KF : YGcfInstDrainRL.RL.cfacts_cf B ly X k. Proof. exact (YGcfInstDrainRL.RL.chunk_facts_cf B ly X Hp _ k M Hk). Qed.

Lemma ELEN : LEN = sec_map_size (ck_req k) /\ o = kPage /\ sm_live sm = true.
Proof.
pose proof (YGcfInstDrainR.amr_wfr _ _ _ _ _ M) as WF.
pose proof (proj1 (Forall_forall _ _) (YG03cf.wfr_chunks _ _ _ _ _ WF) k Hk) as [Hn CK].
rewrite Hb in CK. destruct CK as (P1 & P2 & sm' & Q1 & Q2 & Q3 & Q4). rewrite Hsm in Q1. injection Q1 as <-.
unfold AFg8.LEN. repeat split; assumption.
Qed.

Lemma ZSEC : forall e, In e (sec_extents ly X) -> zone3 (fst e) (snd e) /\ page_aligned (fst e) /\ fst e + snd e <= ASAN_CEIL.
Proof.
intros [ex esz] He. pose proof (YGcfInstDrainR.amr_placed _ _ _ _ _ M) as [PL PD].
pose proof (proj1 (Forall_forall _ _) PL _ He) as (PA & IA & I3). cbn [fst snd] in PA, IA, I3 |- *.
pose proof (@YGcfInstRcSec.sec_in_app rc ci cp AImg_reply B ly X Hp W mem md MR _ He) as [_ SZ]. cbn [snd] in SZ.
split; [|split; [exact PA | exact I3]].
apply (zone3_intro ly ex esz IMG ltac:(lia) IA).
eapply (pairwise_In zdisjoint _ _ _ (sec_extents ly X) (static_extents ly) eq_refl PD He).
unfold static_extents. apply in_app_iff. right. right. left. reflexivity.
Qed.

Lemma GEOM : zone3 MAP LEN /\ MAP + LEN <= ASAN_CEIL /\ MAP mod 4096 = 0 /\ 8192 <= LEN /\ LEN mod 4096 = 0 /\
ck_base B ly k = MAP + kPage /\ ck_extent k = LEN - kPage.
Proof.
pose proof ELEN as (E & _).
pose proof (@YGcfInstRcSec.KFACTS rc ci cp AImg_reply B ly X Hp k r o sm W mem md MR Hk Hb Hsm) as (_ & _ & _ & _ & Gin & _ & Gbase & Gext & Gal).
pose proof (@YGcfInstRcSec.geom rc ci cp AImg_reply B ly X Hp k r o sm W mem md MR Hk Hb Hsm) as (_ & G2 & G3 & _ & G5 & _).
pose proof (ZSEC _ Gin) as (ZM & _ & _). cbn [fst snd] in ZM.
unfold YGcfInstRcSec.MAP, YGcfInstRcSec.LEN in *. unfold page_aligned in Gal. rewrite E. unfold AFg8.MAP. unfold kPage in *.
splits; assumption.
Qed.

Lemma RZ : ck_rz k = 2048.
Proof.
pose proof KF as (_ & _ & _ & _ & _ & _ & RQ & _ & CK). rewrite Hb in CK. destruct CK as (_ & FP & _).
unfold ck_rz. unfold from_primary, needed_primary, rounded_size, round_up, kMaxSize in FP. apply Z.leb_gt in FP.
unfold rz_size, rz_log in *.
destruct (ck_req k <=? 48) eqn:C0. { exfalso. apply Z.leb_le in C0. change (Z.shiftl 16 0) with 16 in FP. clear - FP C0 RQ. lia. }
destruct (ck_req k <=? 96) eqn:C1. { exfalso. apply Z.leb_le in C1. change (Z.shiftl 16 1) with 32 in FP. clear - FP C1 RQ. lia. }
destruct (ck_req k <=? 448) eqn:C2. { exfalso. apply Z.leb_le in C2. change (Z.shiftl 16 2) with 64 in FP. clear - FP C2 RQ. lia. }
destruct (ck_req k <=? 3968) eqn:C3. { exfalso. apply Z.leb_le in C3. change (Z.shiftl 16 3) with 128 in FP. clear - FP C3 RQ. lia. }
destruct (ck_req k <=? 16128) eqn:C4. { exfalso. apply Z.leb_le in C4. change (Z.shiftl 16 4) with 256 in FP. clear - FP C4 RQ. lia. }
destruct (ck_req k <=? 32256) eqn:C5. { exfalso. apply Z.leb_le in C5. change (Z.shiftl 16 5) with 512 in FP. clear - FP C5 RQ. lia. }
destruct (ck_req k <=? 64512) eqn:C6. { exfalso. apply Z.leb_le in C6. change (Z.shiftl 16 6) with 1024 in FP. clear - FP C6 RQ. lia. }
reflexivity.
Qed.

Lemma hdr_facts : hdr = MAP + 6128 /\ 1 <= ck_n k /\ hdr + 16 + ck_n k <= MAP + LEN /\ hdr mod 16 = 0 /\ 0 <= ck_req k.
Proof.
pose proof KF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _). pose proof GEOM as (M1 & M2 & M3 & M4 & M5 & M6 & M7). pose proof RZ as R.
unfold AFfc.hdr, ck_n, req_size. rewrite M6, R. unfold req_size in G8. rewrite R, M7 in G8.
split; [unfold kPage, kChunkHeaderSize; lia|]. split; [destruct (Z.eqb_spec (ck_req k) 0); lia|].
split; [unfold kPage, kChunkHeaderSize in *; destruct (Z.eqb_spec (ck_req k) 0); lia|].
split; [| lia]. apply Z.mod_divide in M3 as [q Hq]; [|lia]. rewrite Hq. apply Z.mod_divide; [lia|]. exists (q * 256 + 383). unfold kPage, kChunkHeaderSize. lia.
Qed.

(* AFf4.SX at the cf layout. *)
Lemma SXs : forall i0 j x0 y, nth_error (static_extents ly) i0 = Some x0 -> nth_error (static_extents ly) j = Some y -> i0 <> j -> zdisjoint x0 y.
Proof.
intros i0 j x0 y Hi0 Hj Hne. destruct (Nat.lt_ge_cases i0 j) as [L|L].
- exact (@YGcfInstRcSec.SX rc ci cp AImg_reply B ly X Hp W mem md MR i0 j x0 y L Hi0 Hj).
- apply zdisjoint_sym. apply (@YGcfInstRcSec.SX rc ci cp AImg_reply B ly X Hp W mem md MR j i0 y x0 ltac:(lia) Hj Hi0).
Qed.

(* AFf4.HIGH at the cf layout. *)
Lemma HIGH : kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ zone3 (ly_Q ly) (kPtrArrayResv) /\ ly_Q ly + kPtrArrayResv <= ASAN_CEIL /\
zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\ zone3 (ly_F ly) (kFakeStackSize) /\ ly_F ly + kFakeStackSize <= ASAN_CEIL /\
zone3 (ly_NB ly) (kNodesBlockSize) /\ ly_NB ly + kNodesBlockSize <= ASAN_CEIL /\ zone3 (ly_SB ly) (kStoreBlockSize) /\ ly_SB ly + kStoreBlockSize <= ASAN_CEIL /\
zone3 (ly_C ly) (256) /\ ly_C ly + 256 <= ASAN_CEIL /\ kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\
ly_prim ly <= ly_space ly /\ ly_space ly + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\ 4096 <= as_inst B /\ as_inst B + 3632 <= kLowMemEnd /\
ASAN_CEIL <= ly_stk_lo ly /\ as_inst B = TFIB_INST.
Proof.
pose proof (lo_high _ LO) as IP. unfold in_high in IP. cbn [fst snd] in IP.
pose proof (lo_app _ LO) as HA. pose proof (lo_disj _ LO) as HD.
assert (Z3 : forall i0 x0 sz, nth_error (owned_extents ly) i0 = Some (x0, sz) -> 0 <= sz -> zone3 x0 sz).
{ intros i0 x0 sz He Hsz. apply (zone3_intro ly x0 sz IMG Hsz (Forall_nth_f _ _ i0 _ HA He)).
assert (L : (i0 < 8)%nat) by (destruct (Nat.lt_ge_cases i0 8) as [X0|X0]; [exact X0|]; assert (X' : nth_error (owned_extents ly) i0 = None) by (apply nth_error_None; cbn; lia); rewrite X' in He; discriminate).
exact (pairwise_ij_f _ _ i0 (8 - i0) _ _ HD ltac:(unfold static_extents; rewrite nth_error_app1 by (cbn; lia); exact He)
ltac:(unfold static_extents; rewrite nth_error_app2 by (cbn; lia); replace (i0 + Datatypes.S (8 - i0) - length (owned_extents ly))%nat with 1%nat by (cbn; lia); reflexivity)). }
pose proof (Z3 1%nat _ _ eq_refl ltac:(unfold kPtrArrayResv; lia)) as ZQ. pose proof (Z3 2%nat _ _ eq_refl ltac:(unfold kThreadObjSize; lia)) as ZT.
pose proof (Z3 3%nat _ _ eq_refl ltac:(unfold kFakeStackSize; lia)) as ZF. pose proof (Z3 4%nat _ _ eq_refl ltac:(unfold kNodesBlockSize; lia)) as ZNB.
pose proof (Z3 5%nat _ _ eq_refl ltac:(unfold kStoreBlockSize; lia)) as ZSB. pose proof (Z3 6%nat _ _ eq_refl ltac:(lia)) as ZC. clear Z3 HA HD.
pose proof (lo_top _ LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof (lo_space_in _ LO) as [S1 S2]. pose proof (lo_stk_ceil _ LO) as CE.
pose proof (aso_cells _ (YGcfInstDrainR.amr_syms _ _ _ _ _ M)) as (I1 & I2 & _).
split; [clear - IP; lia|]. split; [clear - IP; lia|]. split; [exact ZQ|]. split; [clear - ZQ; unfold zone3 in ZQ; lia|].
split; [exact ZT|]. split; [clear - ZT; unfold zone3 in ZT; lia|]. split; [exact ZF|]. split; [clear - ZF; unfold zone3 in ZF; lia|].
split; [exact ZNB|]. split; [clear - ZNB; unfold zone3 in ZNB; lia|]. split; [exact ZSB|]. split; [clear - ZSB; unfold zone3 in ZSB; lia|].
split; [exact ZC|]. split; [clear - ZC; unfold zone3 in ZC; lia|]. clear ZQ ZT ZF ZNB ZSB ZC.
repeat split; try assumption; try lia. exact (ts_inst _ TB).
Qed.

Lemma HI : kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ zone3 Q kPtrArrayResv /\ Q + kPtrArrayResv <= ASAN_CEIL /\
zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\ zone3 (ly_C ly) 256 /\ ly_C ly + 256 <= ASAN_CEIL /\
kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\ ASAN_CEIL <= ly_stk_lo ly /\
ly_prim ly <= SB /\ SB + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\ SB mod 65536 = 0 /\
4096 <= as_inst B /\ as_inst B + 3632 <= kLowMemEnd /\ as_inst B = TFIB_INST /\
Q mod 4096 = 0 /\ T mod 4096 = 0 /\ ly_C ly mod 8 = 0 /\
(T + kThreadObjSize <= ly_prim ly \/ ly_prim ly + kPrimResvSize <= T) /\ (ly_C ly + 256 <= ly_prim ly \/ ly_prim ly + kPrimResvSize <= ly_C ly) /\
(Q + kPtrArrayResv <= ly_prim ly \/ ly_prim ly + kPrimResvSize <= Q) /\
(T + kThreadObjSize <= ly_C ly \/ ly_C ly + 256 <= T) /\ (T + kThreadObjSize <= Q \/ Q + kPtrArrayResv <= T) /\ (ly_C ly + 256 <= Q \/ Q + kPtrArrayResv <= ly_C ly).
Proof.
pose proof HIGH as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hF1 & hF2 & hN1 & hN2 & hB1 & hB2 & hC1 & hC2 & hS1 & hS2 & hSP1 & hSP2 & hI1 & hI2 & hCE & hIE).
pose proof hQ1 as (hQa & hQb & _). pose proof hT1 as (hTa & hTb & _). pose proof hC1 as (hCa & hCb & _).
pose proof (lo_Q_al ly LO) as QAL. pose proof (lo_T_al ly LO) as TAL. pose proof (lo_C_al ly LO) as CAL. pose proof (lo_space_al ly LO) as SAL. unfold page_aligned in QAL, TAL.
pose proof SXs as SX.
pose proof (SX 2%nat 0%nat _ _ eq_refl eq_refl ltac:(lia)) as D20. pose proof (SX 6%nat 0%nat _ _ eq_refl eq_refl ltac:(lia)) as D60. pose proof (SX 1%nat 0%nat _ _ eq_refl eq_refl ltac:(lia)) as D10.
pose proof (SX 2%nat 6%nat _ _ eq_refl eq_refl ltac:(lia)) as D26. pose proof (SX 2%nat 1%nat _ _ eq_refl eq_refl ltac:(lia)) as D21. pose proof (SX 6%nat 1%nat _ _ eq_refl eq_refl ltac:(lia)) as D61.
unfold zdisjoint in *. cbn [fst snd] in *.
repeat match goal with |- _ /\ _ => split end; first [exact hQ1 | exact hT1 | exact hC1 | assumption | lia].
Qed.

Lemma ARRF : In r arr /\ (i < length arr)%nat /\ List.NoDup arr /\ 1 <= nA <= 16384 /\ 0 <= Z.of_nat i < nA.
Proof.
pose proof (@YGcfInstRcSec.ARR rc ci cp AImg_reply B ly X Hp r i W mem md MR Hi) as (A1 & A2 & A3 & A4 & A5 & _).
unfold AFg8.nA. unfold YGcfInstRcSec.nA, YGcfInstRcSec.arr, YGcfInstRcSec.idx, kPtrArrayEntriesPerCommit in A1, A2, A3, A4, A5.
splits; first [exact A1 | exact A2 | exact A3 | lia].
Qed.

Lemma sec_size : forall y ry, In y (st_chunks X) -> ck_beg y = PSec ry kPage -> 8192 <= sec_map_size (ck_req y).
Proof.
intros y ry Hy Ey. pose proof (YGcfInstDrainRL.RL.chunk_facts_cf B ly X Hp _ y M Hy) as (_ & _ & _ & _ & _ & _ & _ & _ & CK).
rewrite Ey in CK. destruct CK as (_ & FP & _).
unfold sec_map_size, needed_size. rewrite FP. unfold from_primary in FP. apply Z.leb_gt in FP.
pose proof (round_up_ge (needed_primary (ck_req y) + rz_size (ck_req y)) kPage ltac:(unfold kPage; lia)) as [R1 _].
pose proof (rz_size_bounds (ck_req y)) as [RZ' _]. unfold kMaxSize, kPage in *. lia.
Qed.

Lemma slot_geom : forall j rj, nth_error arr j = Some rj ->
exists y, In y (st_chunks X) /\ ck_beg y = PSec rj kPage /\ In (ly_sec ly rj, sec_map_size (ck_req y)) (sec_extents ly X) /\
zone3 (ly_sec ly rj) (sec_map_size (ck_req y)) /\ ly_sec ly rj + sec_map_size (ck_req y) <= ASAN_CEIL /\ ly_sec ly rj mod 4096 = 0 /\ 8192 <= sec_map_size (ck_req y) /\
(ly_sec ly rj <> MAP -> ly_sec ly rj + sec_map_size (ck_req y) <= MAP \/ MAP + LEN <= ly_sec ly rj).
Proof.
intros j rj Hj. pose proof (YGcfInstDrainR.amr_wfr _ _ _ _ _ M) as WF. pose proof (YG03cf.wfr_secondary _ _ _ _ _ WF) as XS.
destruct (proj1 (YG01cf.wsc_arr_chunks _ XS rj) (nth_error_In _ _ Hj)) as (y & Hy & Ey). exists y.
pose proof (YGcfInstDrainRL.RL.chunk_facts_cf B ly X Hp _ y M Hy) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & CK). rewrite Ey in CK.
destruct CK as (_ & FP & CB & CE & CI & PA & _).
pose proof (ZSEC _ CI) as (I1 & _ & I2). cbn [fst snd] in I1, I2. unfold page_aligned in PA.
pose proof (sec_size y rj Hy Ey) as SZ.
splits; try assumption.
intros Hne. assert (Hne' : ck_beg y <> ck_beg k).
{ rewrite Ey, Hb. pose proof ELEN as (_ & Eo & _). rewrite Eo. intros E. injection E as E. apply Hne. unfold AFg8.MAP. rewrite E. reflexivity. }
pose proof (YGcfInstDrainRL.RL.secmaps_disjoint_cf B ly X Hp _ y k rj kPage r o M Hy Hk Ey Hb Hne') as DJ. pose proof ELEN as (E & _). unfold AFg8.MAP. rewrite E.
unfold zdisjoint in DJ. cbn [fst snd] in DJ. exact DJ.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The cells and the visible ranges (AFfc.v:151-176).                                                              *)
Lemma cell_lit : forall a (w : nat) x, AF0x.cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum x))) -> val_mem tfibsegs m0 a w x.
Proof.
intros a w x E. apply (AF0x.cell_holds_val_mem B ly H0 mem (ANum a) w (ANum x)).
apply (proj1 (Forall_forall _ _) CONST). rewrite (ts_const B TB ly). exact (AF0x.cell_lookup_In _ _ _ E).
Qed.
Lemma cell_sym : forall e (w : nat) e', AF0x.cell_lookup (Tfib_const ly) e = Some (ACell e w (AV e')) -> val_mem tfibsegs m0 (aeval B ly e) w (aeval B ly e').
Proof.
intros e w e' E. apply (AF0x.cell_holds_val_mem B ly H0 mem e w e').
apply (proj1 (Forall_forall _ _) CONST). rewrite (ts_const B TB ly). exact (AF0x.cell_lookup_In _ _ _ E).
Qed.
Lemma cell_state : forall cc e (w : nat) e', In cc (YG0ncf.acells_cf B ly X) -> cc = ACell e w (AV e') -> val_mem tfibsegs m0 (aeval B ly e) w (aeval B ly e').
Proof.
intros cc e w e' Hin ->. apply (AF0x.cell_holds_val_mem B ly H0 mem e w e').
exact (proj1 (Forall_forall _ _) (YGcfInstDrainR.amr_cells _ _ _ _ _ M) _ Hin).
Qed.
Lemma cell_stateZ : forall cc e (w : nat) x, In cc (YG0ncf.acells_cf B ly X) -> cc = ACell e w (AV (ANum x)) -> val_mem tfibsegs m0 (aeval B ly e) w x.
Proof. intros cc e w x Hin E. exact (cell_state cc e w (ANum x) Hin E). Qed.
Lemma vis_range : forall e len i', In (e, len) (YG0ncf.ajunk_cf B ly X) \/ In (e, len) (aareas X) ->
0 <= i' < len -> rd0 (aeval B ly e + i') <> None.
Proof.
intros e len i' Hin Hi'. destruct Hin as [Hin|Hin].
- exact (proj1 (Forall_forall _ _) (YGcfInstDrainR.amr_junk _ _ _ _ _ M) _ Hin i' Hi').
- exact (proj1 (Forall_forall _ _) (YGcfInstDrainR.amr_areas _ _ _ _ _ M) _ Hin i' Hi').
Qed.
Lemma sec_In : forall cc, In cc (sec_cells X) -> In cc (YG0ncf.acells_cf B ly X).
Proof. intros cc Hcc. unfold YG0ncf.acells_cf. rewrite !in_app_iff. do 3 right. left. exact Hcc. Qed.
Lemma hdr_In : forall cc, In cc (chunk_cells k) -> In cc (YG0ncf.acells_cf B ly X).
Proof. intros cc Hcc. unfold YG0ncf.acells_cf. rewrite !in_app_iff. do 2 right. left. apply in_flat_map. exists k. split; [exact Hk | exact Hcc]. Qed.
Lemma EA : forall d, aeval B ly (aoff (sptr_exp (ck_beg k)) d) = ck_base B ly k + d.
Proof. intros d. unfold ck_base, sptr_addr. rewrite Hb. cbn. lia. Qed.
Lemma EA2 : forall d d', aeval B ly (aoff (aoff (sptr_exp (ck_beg k)) d) d') = ck_base B ly k + d + d'.
Proof. intros d d'. unfold ck_base, sptr_addr. rewrite Hb. cbn. lia. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The values the walk reads (AFfc.v:177-423).                                                                     *)
Lemma inst_vals : val_mem tfibsegs m0 (A_ALLOCATOR + 32) 8 SB /\ val_mem tfibsegs m0 (A_ALLOCATOR + 64) 8 4096 /\
val_mem tfibsegs m0 (A_ALLOCATOR + 72) 8 Q /\ val_mem tfibsegs m0 (A_ALLOCATOR + 120) 8 nA.
Proof.
pose proof AINST as AI. splits.
- replace (A_ALLOCATOR + 32) with (aeval B ly (AInst o_space)) by (cbn; rewrite AI; reflexivity).
replace SB with (aeval B ly (ASp 0)) by (cbn; lia). apply cell_sym. vm_compute. reflexivity.
- apply cell_lit. vm_compute. reflexivity.
- replace (A_ALLOCATOR + 72) with (aeval B ly (AInst o_sec_chunks)) by (cbn; rewrite AI; reflexivity).
replace Q with (aeval B ly (AQ 0)) by (cbn; lia). apply cell_sym. vm_compute. reflexivity.
- replace (A_ALLOCATOR + 120) with (aeval B ly (AInst o_sec_n)) by (cbn; rewrite AI; reflexivity). unfold AFg8.nA.
eapply cell_stateZ; [apply sec_In; unfold sec_cells; right; left; reflexivity | reflexivity].
Qed.
Lemma mutex_bytes : forall a, A_ALLOCATOR + 680 <= a < A_ALLOCATOR + 684 -> mbyte tfibsegs m0 a = Some (Z_to_bv 8 0).
Proof.
intros a Ha. pose proof AINST as AI.
assert (C1 : val_mem tfibsegs m0 (as_inst B + o_sec_mutex) 1 0).
{ apply (cell_stateZ (z1 (AInst o_sec_mutex) 0) (AInst o_sec_mutex) 1 0); [|reflexivity]. apply sec_In. unfold sec_cells. do 2 right; left. reflexivity. }
assert (C2 : val_mem tfibsegs m0 0xa2d01 1 0) by (apply cell_lit; vm_compute; reflexivity).
assert (C3 : val_mem tfibsegs m0 0xa2d02 2 0) by (apply cell_lit; vm_compute; reflexivity).
rewrite AI in C1. unfold o_sec_mutex, A_ALLOCATOR, TFIB_INST in *.
assert (CASES : a = 666200 + 680 \/ a = 666881 + Z.of_nat 0 \/ a = 666882 + Z.of_nat 0 \/ a = 666882 + Z.of_nat 1) by lia.
destruct CASES as [-> |[-> |[-> | ->]]].
- pose proof (C1 0%nat ltac:(lia)) as E. rewrite Z.add_0_r in E. exact E.
- exact (C2 0%nat ltac:(lia)).
- exact (C3 0%nat ltac:(lia)).
- exact (C3 1%nat ltac:(lia)).
Qed.
Lemma mutex_val : val_mem tfibsegs m0 (A_ALLOCATOR + 680) 4 0.
Proof. intros kk Hkk. rewrite le_byte_zero. apply mutex_bytes. lia. Qed.
Lemma slot_val : forall j rj, nth_error arr j = Some rj ->
val_mem tfibsegs m0 (Q + 8 * Z.of_nat j) 8 (ly_sec ly rj) /\ (forall a, Q + 8 * Z.of_nat j <= a < Q + 8 * Z.of_nat j + 8 -> apresent H0 mem a).
Proof.
intros j rj Hj. pose proof HI as (_ & _ & hQ1 & hQ2 & _). pose proof ARRF as (_ & _ & _ & A4 & _). pose proof (nth_error_lt _ _ _ Hj) as JL.
assert (V : val_mem tfibsegs m0 (Q + 8 * Z.of_nat j) 8 (ly_sec ly rj)).
{ replace (Q + 8 * Z.of_nat j) with (aeval B ly (AQ (8 * Z.of_nat j))) by reflexivity.
replace (ly_sec ly rj) with (aeval B ly (ASec rj 0)) by (cbn; lia).
eapply cell_state; [|reflexivity]. apply sec_In. unfold sec_cells. do 3 right. apply in_app_iff. left.
apply in_map_iff. exists (j, rj). split; [reflexivity|]. apply YGcfInstRcSec.in_combine_seq0. exact Hj. }
split; [exact V|]. intros a Ha.
assert (JB : Z.of_nat j < nA) by (unfold AFg8.nA; clear - JL; lia).
apply vis_apresent_off; [apply (zone3_off_img _ _ _ hQ1); clear - Ha A4 JB; unfold kPtrArrayResv; lia|]. eapply val_mem_vis; [exact V | lia].
Qed.
Lemma maph_vals : val_mem tfibsegs m0 MAP 8 MAP /\ val_mem tfibsegs m0 (MAP + 8) 8 LEN /\ val_mem tfibsegs m0 (MAP + 16) 8 (needed_size (ck_req k)) /\
val_mem tfibsegs m0 (MAP + 24) 8 (Z.of_nat i) /\ (forall a, MAP <= a < MAP + 32 -> apresent H0 mem a).
Proof.
pose proof ELEN as (E & _). pose proof GEOM as (M1 & M2 & M3 & M4 & _). pose proof ARRF as (_ & _ & ND & _).
assert (IN : forall cc, In cc [ c8 (ASec r 0) (ASec r 0); z8 (ASec r 8) (sec_map_size (ck_req k)); z8 (ASec r 16) (needed_size (ck_req k)); z8 (ASec r 24) (index_ofZ (st_sec_arr X) r) ] ->
In cc (YG0ncf.acells_cf B ly X)).
{ intros cc Hcc. apply sec_In. unfold sec_cells. do 3 right. apply in_app_iff. right. apply in_flat_map. exists k. split; [exact Hk|]. rewrite Hb. exact Hcc. }
assert (V0 : val_mem tfibsegs m0 MAP 8 MAP).
{ unfold AFg8.MAP. replace (ly_sec ly r) with (aeval B ly (ASec r 0)) by (cbn; lia). eapply cell_state; [apply IN; left; reflexivity | reflexivity]. }
assert (V1 : val_mem tfibsegs m0 (MAP + 8) 8 LEN).
{ rewrite E. unfold AFg8.MAP. replace (ly_sec ly r + 8) with (aeval B ly (ASec r 8)) by reflexivity. eapply cell_stateZ; [apply IN; right; left; reflexivity | reflexivity]. }
assert (V2 : val_mem tfibsegs m0 (MAP + 16) 8 (needed_size (ck_req k))).
{ unfold AFg8.MAP. replace (ly_sec ly r + 16) with (aeval B ly (ASec r 16)) by reflexivity. eapply cell_stateZ; [apply IN; do 2 right; left; reflexivity | reflexivity]. }
assert (V3 : val_mem tfibsegs m0 (MAP + 24) 8 (Z.of_nat i)).
{ unfold AFg8.MAP. replace (ly_sec ly r + 24) with (aeval B ly (ASec r 24)) by reflexivity.
rewrite <- (YGcfInstRcSec.index_ofZ_nth arr i r ND Hi). eapply cell_stateZ; [apply IN; do 3 right; left; reflexivity | reflexivity]. }
splits; try assumption.
intros a Ha.
apply vis_apresent_off; [apply (zone3_off_img _ _ _ M1); clear - Ha M4; lia|].
destruct (Z_lt_le_dec a (MAP + 8)); [eapply val_mem_vis; [exact V0 | lia]|].
destruct (Z_lt_le_dec a (MAP + 16)); [replace a with (MAP + 8 + (a - (MAP + 8))) by lia; eapply val_mem_vis; [exact V1 | lia]|].
destruct (Z_lt_le_dec a (MAP + 24)); [replace a with (MAP + 16 + (a - (MAP + 16))) by lia; eapply val_mem_vis; [exact V2 | lia]|].
replace a with (MAP + 24 + (a - (MAP + 24))) by lia. eapply val_mem_vis; [exact V3 | lia].
Qed.
Lemma hb1_facts : rd0 (hdr + 1) = Some hb1 /\ 0 <= hb1 < 256.
Proof.
assert (C : cell_holds B ly rd0 (ACell (aoff (aoff (sptr_exp (ck_beg k)) (ck_rz k - kChunkHeaderSize)) 1) 1 (AVmask 127 17))).
{ apply (proj1 (Forall_forall _ _) (YGcfInstDrainR.amr_cells _ _ _ _ _ M)). apply hdr_In. unfold chunk_cells. apply in_app_iff. left. cbn. tauto. }
cbn [cell_holds c_at c_val c_w] in C. rewrite EA2 in C.
replace (ck_base B ly k + (ck_rz k - kChunkHeaderSize) + 1) with (hdr + 1) in C by (unfold AFfc.hdr; lia).
destruct C as (b & Hb' & Hm). unfold AFfc.hb1. rewrite Hb'.
destruct (aview_vis_byte H0 mem _ ltac:(rewrite Hb'; discriminate)) as (b' & E' & R' & _). rewrite Hb' in E'. injection E' as <-. auto.
Qed.
Lemma hw_val : val_mem tfibsegs m0 hdr 4 HWv /\ val_mem tfibsegs m0 (hdr + 4) 4 (ck_n k) /\ (forall a, hdr <= a < hdr + 8 -> apresent H0 mem a) /\ 0 <= HWv < 65536.
Proof.
pose proof hb1_facts as [HB HR]. pose proof hdr_facts as (H1 & _). pose proof GEOM as (M1 & M2 & _ & M4 & _).
assert (EH : aeval B ly (aoff (sptr_exp (ck_beg k)) (ck_rz k - kChunkHeaderSize)) = hdr) by (rewrite EA; unfold AFfc.hdr; lia).
assert (EH2 : forall d, aeval B ly (aoff (aoff (sptr_exp (ck_beg k)) (ck_rz k - kChunkHeaderSize)) d) = hdr + d) by (intros d; rewrite EA2; unfold AFfc.hdr; lia).
assert (V0 : val_mem tfibsegs m0 hdr 1 3).
{ rewrite <- EH. eapply cell_stateZ; [apply hdr_In; unfold chunk_cells; apply in_app_iff; left; left; reflexivity|]. unfold z1, c1, hdr_state. rewrite Hst. reflexivity. }
assert (V2 : val_mem tfibsegs m0 (hdr + 2) 2 0).
{ rewrite <- (EH2 2). eapply cell_stateZ; [apply hdr_In; unfold chunk_cells; apply in_app_iff; left; do 2 right; left; reflexivity|]. reflexivity. }
assert (V4 : val_mem tfibsegs m0 (hdr + 4) 4 (ck_n k)).
{ rewrite <- (EH2 4). eapply cell_stateZ; [apply hdr_In; unfold chunk_cells; apply in_app_iff; left; do 3 right; left; reflexivity|]. reflexivity. }
assert (W1 : val_mem tfibsegs m0 hdr 4 HWv).
{ intros i' Hi'. unfold AFfc.HWv.
assert (LB : forall v (w j : nat), YO0f.le_byte v w j = (v mod 2 ^ (8 * Z.of_nat w)) / 2 ^ (8 * Z.of_nat j) mod 256).
{ intros v w j. unfold YO0f.le_byte. rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
destruct i' as [|[|[|[|i']]]]; [| | | |lia].
- rewrite (V0 0%nat ltac:(lia)). do 2 f_equal. rewrite !LB. change (2 ^ (8 * Z.of_nat 1)) with 256. change (2 ^ (8 * Z.of_nat 4)) with 4294967296.
change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite !Z.div_1_r. Z.div_mod_to_equations. nia.
- change (Z.of_nat 1) with 1. rewrite (aview_byte _ _ _ _ HB). do 2 f_equal.
rewrite !LB. change (2 ^ (8 * Z.of_nat 4)) with 4294967296. change (2 ^ (8 * Z.of_nat 1)) with 256. Z.div_mod_to_equations. nia.
- replace (hdr + Z.of_nat 2) with (hdr + 2 + Z.of_nat 0) by lia. rewrite (V2 0%nat ltac:(lia)). do 2 f_equal.
rewrite !LB. change (2 ^ (8 * Z.of_nat 4)) with 4294967296. change (2 ^ (8 * Z.of_nat 2)) with 65536. change (2 ^ (8 * Z.of_nat 0)) with 1.
rewrite !Z.div_1_r. Z.div_mod_to_equations. nia.
- replace (hdr + Z.of_nat 3) with (hdr + 2 + Z.of_nat 1) by lia. rewrite (V2 1%nat ltac:(lia)). do 2 f_equal.
rewrite !LB. change (2 ^ (8 * Z.of_nat 4)) with 4294967296. change (2 ^ (8 * Z.of_nat 2)) with 65536.
change (2 ^ (8 * Z.of_nat 1)) with 256. change (2 ^ (8 * Z.of_nat 3)) with 16777216. Z.div_mod_to_equations. nia. }
splits; [exact W1 | exact V4 | | unfold AFfc.HWv; lia | unfold AFfc.HWv; lia].
intros a Ha. apply vis_apresent_off; [apply (zone3_off_img _ _ _ M1); pose proof hdr_facts as (_ & D2 & D3 & _); clear - Ha H1 M4 D2 D3; lia|].
destruct (Z_lt_le_dec a (hdr + 4)); [replace a with (hdr + (a - hdr)) by lia; eapply val_mem_vis; [exact W1 | lia] | replace a with (hdr + 4 + (a - (hdr + 4))) by lia; eapply val_mem_vis; [exact V4 | lia]].
Qed.
Lemma tls_vals : val_mem tfibsegs m0 0xa5920 1 1 /\ val_mem tfibsegs m0 0xa5924 4 0 /\ val_mem tfibsegs m0 (TFIB_TP - 88) 8 TFIB_TSD /\
val_mem tfibsegs m0 TFIB_TSD 8 (ly_C ly) /\ val_mem tfibsegs m0 (ly_C ly + 8) 4 0 /\ val_mem tfibsegs m0 (ly_C ly + 152) 8 T.
Proof.
splits.
- apply cell_lit. vm_compute. reflexivity.
- apply cell_lit. vm_compute. reflexivity.
- replace (TFIB_TP - 88) with (aeval B ly (ATp (-88))) by (cbn; rewrite (ts_tp B TB); lia).
replace TFIB_TSD with (aeval B ly (ATsd 0)) by (cbn; rewrite HTSD; lia). apply cell_sym. vm_compute. reflexivity.
- replace TFIB_TSD with (aeval B ly (ATsd 0)) by (cbn; rewrite HTSD; lia). replace (ly_C ly) with (aeval B ly (AC 0)) by (cbn; lia). apply cell_sym. vm_compute. reflexivity.
- replace (ly_C ly + 8) with (aeval B ly (AC 8)) by reflexivity. apply (cell_sym (AC 8) 4 (ANum 0)). vm_compute. reflexivity.
- replace (ly_C ly + 152) with (aeval B ly (AC 152)) by reflexivity. replace T with (aeval B ly (AT 0)) by (cbn; lia). apply cell_sym. vm_compute. reflexivity.
Qed.
Lemma const_vals :
val_mem tfibsegs m0 0x9d9c0 8 0x137be8 /\ val_mem tfibsegs m0 0x137c60 8 0xffffffffffffffff /\ val_mem tfibsegs m0 0x137c78 8 0 /\
val_mem tfibsegs m0 0x9d9d0 8 0xa60b8 /\ val_mem tfibsegs m0 0xa60b8 8 0x7fff8000 /\
val_mem tfibsegs m0 0x9d9d8 8 0xa6da8 /\ val_mem tfibsegs m0 0x9d9e0 8 0xa6db0 /\ val_mem tfibsegs m0 0x9d9e8 8 0xa6da0 /\
val_mem tfibsegs m0 0xa6da0 8 0x7fffffffffff /\ val_mem tfibsegs m0 0xa6da8 8 0 /\ val_mem tfibsegs m0 0xa6db0 8 0 /\
val_mem tfibsegs m0 0x9d9f0 8 0x9f870 /\ val_mem tfibsegs m0 0x9f870 8 0x96900 /\
val_mem tfibsegs m0 0x9d9b0 8 0x135b60 /\ val_mem tfibsegs m0 0x135b60 8 4096 /\ val_mem tfibsegs m0 0x9da10 8 1.
Proof. splits; (apply cell_lit; vm_compute; reflexivity). Qed.
Lemma vis_present : forall e len a, In (e, len) (YG0ncf.ajunk_cf B ly X) \/ In (e, len) (aareas X) ->
aeval B ly e <= a < aeval B ly e + len -> off_img a -> apresent H0 mem a.
Proof.
intros e len a Hin Ha Hhi.
assert (RV : range_vis B ly rd0 (e, len)).
{ destruct Hin as [Hin|Hin]; [exact (proj1 (Forall_forall _ _) (YGcfInstDrainR.amr_junk _ _ _ _ _ M) _ Hin) | exact (proj1 (Forall_forall _ _) (YGcfInstDrainR.amr_areas _ _ _ _ _ M) _ Hin)]. }
destruct (range_vis_mbyte B ly H0 mem e len (a - aeval B ly e) RV ltac:(lia)) as [b Hb'].
replace (aeval B ly e + (a - aeval B ly e)) with a in Hb' by lia. exact (mbyte_off_apresent H0 mem a b Hhi Hb').
Qed.
Lemma thread_present : forall a, T <= a < T + kThreadObjSize -> apresent H0 mem a.
Proof.
intros a Ha. pose proof HI as (_ & _ & _ & _ & F1 & F2 & _).
apply (vis_present (AT 0) kThreadObjSize).
- right. unfold aareas. do 3 (apply in_or_app; right). do 3 right. left. reflexivity.
- cbn [aeval]. lia.
- exact (zone3_off_img _ _ a F1 Ha).
Qed.
Lemma stack_present : forall a, sp0 - KSTACK <= a < sp0 -> apresent H0 mem a.
Proof.
destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & HP & _). intros a Ha. apply HP. unfold spZ. fold sp0. unfold KSTACK, KSTACK_CF in *. lia.
Qed.
Lemma shadow_vis : forall t, 0 <= t < LEN / 8 -> exists v, rd0 (SHAv MAP + t) = Some v.
Proof.
intros t Ht. pose proof GEOM as (M1 & M2 & M3 & M4 & M5 & _). pose proof ELEN as (E & _).
set (g := MAP + 8 * t).
assert (Hg : g mod 8 = 0). { subst g. apply Z.mod_divide in M3 as [q Hq]; [|lia]. rewrite Hq. apply Z.mod_divide; [lia|]. exists (q * 512 + t). lia. }
assert (ESA : shadow_addr g = SHAv MAP + t).
{ unfold shadow_addr, SHAv. subst g. apply Z.mod_divide in M3 as [q Hq]; [|lia]. rewrite Hq. replace (q * 4096) with ((q * 512) * 8) by lia.
replace (q * 512 * 8 + 8 * t) with ((q * 512 + t) * 8) by lia. rewrite !Z_div_mult by lia. lia. }
assert (SH : exists v, ashadow B ly X g = Some v).
{ unfold ashadow. destruct (find_chunk_at B ly (st_chunks X) g) as [y|]; [eexists; reflexivity|].
rewrite (in_rangesb_In g (fa_poison_ranges ly X) MAP (sec_map_size (ck_req k))); [eexists; reflexivity| |].
- unfold fa_poison_ranges. apply in_app_iff. right. apply in_flat_map. exists k. split; [exact Hk|]. rewrite Hb. left. reflexivity.
- rewrite <- E. subst g. pose proof (Z.mul_div_le LEN 8 ltac:(lia)). lia. }
(* shadow_ok_weak_cf: either the byte is the shadow value (or the head's poison), or a pending user range, still
   present; sec_cut only needs the byte present. *)
destruct SH as [v Hv]. rewrite <- ESA.
destruct (YGcfInstDrainR.amr_shadow _ _ _ _ _ M g v Hg Hv) as [E1 | [_ E1]]; [eexists; exact E1|].
destruct (rd0 (shadow_addr g)) as [w|] eqn:Ew; [exists w; reflexivity | exfalso; apply E1; first [exact Ew | reflexivity]].
Qed.
Lemma shadow_present : forall a, SHAv MAP <= a < SHAv MAP + CNTv LEN -> apresent H0 mem a.
Proof.
intros a Ha. pose proof GEOM as (M1 & M2 & M3 & M4 & M5 & _). unfold CNTv in Ha.
destruct (shadow_vis (a - SHAv MAP) ltac:(lia)) as [v Hv]. replace (SHAv MAP + (a - SHAv MAP)) with a in Hv by lia.
apply vis_apresent; [| rewrite Hv; discriminate]. unfold SHAv in *. clear - Ha M1 M2 M4. numconst.
pose proof (Z.div_pos MAP 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound LEN 8). Z.div_mod_to_equations. lia.
Qed.
Lemma tjunk_vals : forall a, (T + t_stats + 40 <= a /\ a + 8 <= T + t_stats + 56) \/ (T + t_stats + 88 <= a /\ a + 8 <= T + t_stats + 104) ->
exists w, 0 <= w < 2 ^ 64 /\ val_mem tfibsegs m0 a 8 w /\ rdword rd0 a = Some w.
Proof.
intros a Ha. apply vis_word. intros i' Hi'.
replace (a + i') with (aeval B ly (AT t_stats) + (a + i' - (T + t_stats))) by (cbn; lia).
apply (vis_range _ (t_unwinding - t_stats)); [|clear - Ha Hi'; numconst; lia]. left. unfold YG0ncf.ajunk_cf. right. right. rewrite !in_app_iff. do 5 right. left.
unfold thread_junk. right; right; left; reflexivity.
Qed.
Lemma junk_vals : (0 <= AFfc.j1 ly W mem < 2 ^ 64 /\ val_mem tfibsegs m0 (T + t_stats + 40) 8 (AFfc.j1 ly W mem)) /\
(0 <= AFfc.j2 ly W mem < 2 ^ 64 /\ val_mem tfibsegs m0 (T + t_stats + 48) 8 (AFfc.j2 ly W mem)).
Proof.
destruct (tjunk_vals (T + t_stats + 40) ltac:(lia)) as (w1 & R1 & V1 & E1). destruct (tjunk_vals (T + t_stats + 48) ltac:(lia)) as (w2 & R2 & V2 & E2).
unfold AFfc.j1, AFfc.j2, AFfc.jw. rewrite E1, E2. repeat split; assumption || lia.
Qed.
Lemma ijunk_vals : forall a, a = A_ALLOCATOR + 144 \/ a = A_ALLOCATOR + 152 \/ a = A_ALLOCATOR + 704 \/ a = A_ALLOCATOR + 712 ->
exists w, 0 <= w < 2 ^ 64 /\ val_mem tfibsegs m0 a 8 w /\ rdword rd0 a = Some w.
Proof.
intros a Ha. pose proof AINST as AI. apply vis_word. intros i' Hi'.
assert (SJ : forall d, 0 <= d < o_sec_mutex - o_sec_stats -> rd0 (aeval B ly (AInst o_sec_stats) + d) <> None).
{ intros d Hd. apply (vis_range _ (o_sec_mutex - o_sec_stats)); [|exact Hd]. left. unfold YG0ncf.ajunk_cf. right. right. rewrite !in_app_iff. do 3 right. left.
unfold sec_junk. right; left; reflexivity. }
assert (CJ : forall d, 0 <= d < 40 -> rd0 (aeval B ly (ANum (TFIB_INST + o_comb_stats)) + d) <> None).
{ intros d Hd. apply (vis_range _ 40); [|exact Hd]. left. unfold YG0ncf.ajunk_cf. right. right. rewrite !in_app_iff. do 7 right. apply (ts_junk_comb _ TB ly). }
cbn [aeval] in SJ, CJ. rewrite AI in SJ. unfold o_sec_stats, o_sec_mutex, o_comb_stats in *.
destruct Ha as [-> |[-> |[-> | ->]]].
- replace (A_ALLOCATOR + 144 + i') with (A_ALLOCATOR + 136 + (8 + i')) by lia. apply SJ. lia.
- replace (A_ALLOCATOR + 152 + i') with (A_ALLOCATOR + 136 + (16 + i')) by lia. apply SJ. lia.
- replace (A_ALLOCATOR + 704 + i') with (TFIB_INST + 688 + (16 + i')) by (numconst; lia). apply CJ. lia.
- replace (A_ALLOCATOR + 712 + i') with (TFIB_INST + 688 + (24 + i')) by (numconst; lia). apply CJ. lia.
Qed.
Lemma junkD_vals :
(0 <= AFfc.ji1 W mem < 2 ^ 64 /\ val_mem tfibsegs m0 (A_ALLOCATOR + 144) 8 (AFfc.ji1 W mem)) /\
(0 <= AFfc.ji2 W mem < 2 ^ 64 /\ val_mem tfibsegs m0 (A_ALLOCATOR + 152) 8 (AFfc.ji2 W mem)) /\
(0 <= AFfc.ji3 W mem < 2 ^ 64 /\ val_mem tfibsegs m0 (A_ALLOCATOR + 704) 8 (AFfc.ji3 W mem)) /\
(0 <= AFfc.ji4 W mem < 2 ^ 64 /\ val_mem tfibsegs m0 (A_ALLOCATOR + 712) 8 (AFfc.ji4 W mem)) /\
(0 <= AFfc.j5 ly W mem < 2 ^ 64 /\ val_mem tfibsegs m0 (T + t_stats + 88) 8 (AFfc.j5 ly W mem)) /\
(0 <= AFfc.j6 ly W mem < 2 ^ 64 /\ val_mem tfibsegs m0 (T + t_stats + 96) 8 (AFfc.j6 ly W mem)).
Proof.
destruct (ijunk_vals (A_ALLOCATOR + 144) ltac:(lia)) as (w1 & R1 & V1 & E1). destruct (ijunk_vals (A_ALLOCATOR + 152) ltac:(lia)) as (w2 & R2 & V2 & E2').
destruct (ijunk_vals (A_ALLOCATOR + 704) ltac:(lia)) as (w3 & R3 & V3 & E3). destruct (ijunk_vals (A_ALLOCATOR + 712) ltac:(lia)) as (w4 & R4 & V4 & E4).
destruct (tjunk_vals (T + t_stats + 88) ltac:(lia)) as (w5 & R5 & V5 & E5). destruct (tjunk_vals (T + t_stats + 96) ltac:(lia)) as (w6 & R6 & V6 & E6).
unfold AFfc.ji1, AFfc.ji2, AFfc.ji3, AFfc.ji4, AFfc.j5, AFfc.j6, AFfc.jw. rewrite E1, E2', E3, E4, E5, E6. repeat split; assumption || lia.
Qed.

(* AFf4.LST at the cf relation. *)
Lemma LST : exists y, In y (st_chunks X) /\ ck_beg y = PSec (AFf4.lastr X r) kPage /\ In (AFf4.lst ly X r, sec_map_size (ck_req y)) (sec_extents ly X) /\
zone3 (AFf4.lst ly X r) (sec_map_size (ck_req y)) /\ AFf4.lst ly X r + sec_map_size (ck_req y) <= ASAN_CEIL /\ AFf4.lst ly X r mod 4096 = 0 /\ 8192 <= sec_map_size (ck_req y) /\
(AFf4.own X i = false -> zdisjoint (AFf4.lst ly X r, sec_map_size (ck_req y)) (AFf4.MAP ly r, AFf4.LEN k)).
Proof.
pose proof (@YGcfInstRcSec.ARR rc ci cp AImg_reply B ly X Hp r i W mem md MR Hi) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
pose proof (YGcfInstDrainR.amr_wfr _ _ _ _ _ M) as WF. pose proof (YG03cf.wfr_secondary _ _ _ _ _ WF) as XS.
destruct (proj1 (YG01cf.wsc_arr_chunks _ XS (YGcfInstRcSec.lastr X r)) A7) as (y & Hy & Ey). exists y.
pose proof (YGcfInstDrainRL.RL.chunk_facts_cf B ly X Hp _ y M Hy) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & CK). rewrite Ey in CK.
destruct CK as (_ & FP & CB & CE & CI & PA & _).
pose proof (ZSEC _ CI) as (I1 & _ & I2). cbn [fst snd] in I1, I2. unfold page_aligned in PA.
pose proof (sec_size y _ Hy Ey) as SZ.
change (AFf4.lastr X r) with (YGcfInstRcSec.lastr X r). change (AFf4.lst ly X r) with (ly_sec ly (YGcfInstRcSec.lastr X r)).
splits; try assumption.
intros Ho. assert (Hne : ck_beg y <> ck_beg k).
{ rewrite Ey, Hb. pose proof ELEN as (_ & Eo & _). rewrite Eo. intros E. injection E as E. apply (proj2 A8) in E.
  change (YGcfInstRcSec.own X i) with (AFf4.own X i) in E. congruence. }
unfold AFf4.MAP, AFf4.LEN. exact (YGcfInstDrainRL.RL.secmaps_disjoint_cf B ly X Hp _ y k _ kPage r o M Hy Hk Ey Hb Hne).
Qed.

Local Notation lastr := (last (st_sec_arr X) r).
Local Notation lst := (AFg8.lst ly X r).
Local Notation own := (AFg8.own X i).
Lemma last_facts : nth_error arr (length arr - 1) = Some lastr /\
val_mem tfibsegs m0 (Q + 8 * (nA - 1)) 8 lst /\ (forall a, Q + 8 * (nA - 1) <= a < Q + 8 * (nA - 1) + 8 -> apresent H0 mem a) /\
val_mem tfibsegs m0 (lst + 24) 8 (nA - 1) /\ (forall a, lst + 24 <= a < lst + 32 -> apresent H0 mem a) /\
zone3 lst 8192 /\ lst + 8192 <= ASAN_CEIL /\ lst mod 4096 = 0 /\
(if own then Z.of_nat i = nA - 1 /\ lst = MAP else lst + 4096 <= MAP \/ MAP + LEN <= lst).
Proof.
pose proof ARRF as (A1 & A2 & A3 & A4 & A5). pose proof ELEN as (E & _).
assert (NE : st_sec_arr X <> []) by (destruct (st_sec_arr X); [cbn in A2; lia | discriminate]).
pose proof (YGcfInstRcSec.last_nth_error (st_sec_arr X) r NE) as HL.
assert (EL : Z.of_nat (length (st_sec_arr X) - 1) = nA - 1) by (unfold AFg8.nA; lia).
destruct (slot_val _ _ HL) as [SV SP]. rewrite EL in SV, SP.
destruct LST as (y2 & Hy2 & Ey2 & CI2 & L1 & L2 & L3 & SZ2 & DJL).
pose proof (@YGcfInstRcSec.ARR rc ci cp AImg_reply B ly X Hp r i W mem md MR Hi) as (_ & _ & _ & _ & _ & _ & _ & A8).
unfold AFf4.lst, AFf4.lastr, AFf4.arr in *. unfold AFg8.lst.
assert (V24 : val_mem tfibsegs m0 (ly_sec ly lastr + 24) 8 (nA - 1)).
{ replace (ly_sec ly lastr + 24) with (aeval B ly (ASec lastr 24)) by reflexivity. rewrite <- EL.
rewrite <- (YGcfInstRcSec.index_ofZ_nth (st_sec_arr X) (length (st_sec_arr X) - 1) lastr A3 HL).
eapply cell_stateZ; [|reflexivity]. apply sec_In. unfold sec_cells. do 3 right. apply in_app_iff. right. apply in_flat_map. exists y2. split; [exact Hy2|]. rewrite Ey2.
do 3 right. left. reflexivity. }
splits; try assumption.
- intros a Ha. apply vis_apresent_off; [apply (zone3_off_img _ _ _ L1); clear - Ha SZ2; lia|]. replace a with (ly_sec ly lastr + 24 + (a - (ly_sec ly lastr + 24))) by lia. eapply val_mem_vis; [exact V24 | lia].
- clear - L1 SZ2. unfold zone3, zone3cases in *. lia.
- lia.
- unfold AFg8.own, AFg8.idx. unfold YGcfInstRcSec.own, YGcfInstRcSec.idx, YGcfInstRcSec.nA, YGcfInstRcSec.lastr, YGcfInstRcSec.arr in A8.
unfold AFf4.own, AFf4.idx, AFf4.nA in DJL. unfold AFg8.nA.
destruct (Z.of_nat i =? Z.of_nat (length (st_sec_arr X)) - 1) eqn:EO.
+ split; [apply Z.eqb_eq in EO; exact EO|]. rewrite (proj1 A8 ltac:(first [exact EO | reflexivity])). reflexivity.
+ unfold AFf4.arr in DJL. specialize (DJL ltac:(first [exact EO | reflexivity])). unfold zdisjoint in DJL. cbn [fst snd] in DJL. unfold AFf4.MAP, AFf4.LEN in DJL. rewrite <- E in DJL.
unfold AFg8.MAP. clear - DJL SZ2. lia.
Qed.
Lemma qi_val : val_mem tfibsegs m0 (Q + 8 * Z.of_nat i) 8 MAP /\ (forall a, Q + 8 * Z.of_nat i <= a < Q + 8 * Z.of_nat i + 8 -> apresent H0 mem a).
Proof. exact (slot_val i r Hi). Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The first segment's premise record AFgu.free_hyps (AFfc.v:424-524).                                             *)
Local Notation E0 := (AFgu.E0 ly regs hdr nA Q).
Lemma E2 : ew E0 2 = getr regs 2. Proof. exact (AFgu.E2 ly regs hdr nA Q). Qed.
Lemma chunk_lit0 : forall a (w : BinNums.N) x, val_mem tfibsegs m0 a (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 0 (YP09.mkChunk a (CVal w (SLit x))).
Proof. intros a w x Hm Hx Hw. eapply chunk_ok_val; [reflexivity | exact Hx | exact Hw | rewrite Z.add_0_l; exact Hm]. Qed.
Lemma chunk_atom : forall base a (w : BinNums.N) k0 d x, ew E0 k0 = w64 (x - d) -> 0 <= x - d < 2 ^ 64 ->
val_mem tfibsegs m0 (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 base (YP09.mkChunk a (CVal w (SOff k0 d))).
Proof.
intros base a w k0 d x Hk0 Hr Hm Hx Hw. eapply chunk_ok_val; [| exact Hx | exact Hw | exact Hm].
cbn [sv_denot]. rewrite Hk0. unfold w64. rewrite Zbv_add_unsigned. f_equal. lia.
Qed.
Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Local Ltac r8 := change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia.
Lemma REG0_ok : Forall (region_ok tfibsegs E0 m0) AFgu.REG0.
Proof.
pose proof HI as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hC1 & hC2 & hS1 & hS2 & hCE & hSP1 & hSP2 & hSAL & hI1 & hI2 & hIE & _).
pose proof HSP as [S1 S2]. pose proof inst_vals as (V1 & V2 & V3 & V4). pose proof mutex_val as VM. pose proof ARRF as (_ & _ & _ & A4 & _).
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kSpaceSize, kPrimResvSize, kPtrArrayResv, KSTACK, kLowMemEnd in hP1, hP2, hQ1, hQ2, hS1, hS2, hCE, hSP1, hSP2, S1, S2, hI1, hI2.
unfold AFgu.REG0, AFgu.R_STK, AFgu.R_MUT, fatom8.
apply Forall_cons.
{   apply (region_ok_stack tfibsegs E0 m0 2 sp0 (- AFgu.GFRAME)); [rewrite E2; reflexivity | unfold AFgu.GFRAME; lia | lia |].
intros a Ha. apply apresent_writable; [unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END, AFgu.GFRAME in *; lia | apply stack_present; clear -Ha; unfold AFgu.GFRAME, KSTACK in *; lia]. }
apply Forall_cons.
{   reg_intro. unfold A_ALLOCATOR in *. split; [lia|]. split; [lia|]. split.
{ intros o' Ho'. apply rw_writable. lia. }
apply Forall_cons; [|apply Forall_nil]. apply chunk_lit0; [exact VM | cbn; lia | cbn; lia]. }
apply Forall_cons.
{   reg_intro. unfold A_ALLOCATOR in *. split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom 0 _ 8 32%nat 0 SB); [rewrite Z.sub_0_r; reflexivity | lia | rewrite Z.add_0_l; exact V1 | r8 | cbn; lia]. }
apply Forall_cons.
{   reg_intro. unfold A_ALLOCATOR in *. split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom 0 _ 8 34%nat 0 nA); [rewrite Z.sub_0_r; reflexivity | lia | rewrite Z.add_0_l; exact V4 | r8 | cbn; lia]. }
apply Forall_cons; [|apply Forall_nil].
{   reg_intro. unfold A_ALLOCATOR in *. split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom 0 _ 8 35%nat 0 Q); [rewrite Z.sub_0_r; reflexivity | lia | rewrite Z.add_0_l; exact V3 | r8 | cbn; lia]. }
Qed.
Lemma PAIRS_ok : pairwise_disjoint E0 AFgu.REG0.
Proof.
pose proof HI as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hC1 & hC2 & hS1 & hS2 & hCE & _). pose proof HSP as [S1 S2].
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
apply pairwise_disjoint_of_extents.
unfold AFgu.REG0, AFgu.R_STK, AFgu.R_MUT, fatom8, extent_of_region.
cbn [map fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite E2. fold sp0. numconst.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat split; first [clear; lia | clear - S1 hS1 hCE Usp; lia].
Qed.
Lemma FACTS_ok : atoms_ok E0 (f_atoms AFgu.FFA).
Proof.
pose proof HI as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hC1 & hC2 & hS1 & hS2 & hCE & hSP1 & hSP2 & hSAL & hI1 & hI2 & hIE & hQAL & _).
pose proof HSP as [S1 S2]. pose proof hdr_facts as (D1 & D2 & D3 & D4 & _). pose proof GEOM as (M1 & M2 & M3 & M4 & M5 & _). pose proof ARRF as (_ & _ & _ & A4 & _).
destruct PRE as (_ & _ & _ & Hal & _). unfold spZ in Hal. fold sp0 in Hal.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
assert (E2' : ew E0 2 = w64 sp0) by (rewrite E2; unfold sp0, w64; symmetry; apply Z_to_bv_bv_unsigned).
assert (AF : forall k0 Xv lo hi al, ew E0 k0 = w64 Xv -> 0 <= Xv < 2 ^ 64 -> lo <= Xv <= hi -> Xv mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E0 k0 (mkAF lo hi al)).
{ clear. intros k0 Xv lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by exact HX. repeat split; lia. }
cbn [AFgu.FFA f_atoms atoms_ok]. numconst.
split. { apply (AF 2%nat sp0); [exact E2'| | | |]. all: clear - CR0 Usp S1 S2 hS1 hS2 hCE Hal; first [lia | change (2 ^ 4) with 16; exact Hal]. }
split. { apply (AF 32%nat SB); [reflexivity| | | |]. all: clear - CR0 hSP1 hSP2 hP1 hP2 hSAL; first [lia | apply Z.mod_divide in hSAL as [q Hq]; [|lia]; apply Z.mod_divide; [lia|]; exists q; change (2 ^ 16) with 65536; lia]. }
split. { apply (AF 33%nat hdr); [reflexivity| | | |]. all: clear - CR0 D1 D2 D3 D4 M1 M2 M4; first [lia | change (2 ^ 4) with 16; exact D4]. }
split. { apply (AF 34%nat nA); [reflexivity| | | |]. all: clear - A4; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split; [|exact I]. { apply (AF 35%nat Q); [reflexivity| | | |]. all: clear - CR0 hQ1 hQ2 hQAL; first [lia | change (2 ^ 12) with 4096; exact hQAL]. }
Qed.
Lemma SEED_ok : st_ok tfibsegs E0 AFgu.SS0 (restrict (w_H W) (mkst regs (w64 A_RChunk) mem (seg_rom tfibsegs))).
Proof.
destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Htp & Ha0 & Ha1).
rewrite restrict_mkst_fx. unfold AFgu.SS0, AFgu.SR0, sr_set. cbn [bv_eqb]. unfold AFgu.E0, w64. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_pin; [apply regs_ok_Ereg | intros XX; discriminate |].
cbn [sv_denot]. fold (AFgu.E0 ly regs hdr nA Q). rewrite AFgu.EqM, Ha1. unfold w64, AFfc.hdr. rewrite Zbv_add_unsigned. f_equal. lia.
- vm_compute. reflexivity.
- cbn [ms_mem mkst]. exact REG0_ok.
- exact PAIRS_ok.
- split; [exact FACTS_ok | split; exact I].
Qed.
Lemma FH_A : AFgu.free_hyps W ly regs mem hdr nA Q.
Proof.
pose proof PRE as PRE'. destruct PRE' as (HAR & Hra & Hra4 & Hal & Hlo & Hcb1 & Hcb2 & Hcb3 & HPRES & HPRC & HVC & Hgp & Htp & Ha0 & Ha1).
unfold spZ, raZ in *. fold sp0 in Hal, Hlo, Hcb1, HPRES.
pose proof HI as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hC1 & hC2 & hS1 & hS2 & hCE & hSP1 & hSP2 & hSAL & hI1 & hI2 & hIE & hQAL & _).
pose proof hdr_facts as (D1 & D2 & D3 & D4 & _). pose proof GEOM as (M1 & M2 & M3 & M4 & M5 & _). pose proof ARRF as (_ & _ & _ & A4 & _).
pose proof inst_vals as (V1 & V2 & V3 & V4).
pose proof (@YGcfInstRcSec.MAPX rc ci cp AImg_reply B ly X Hp k r o sm W mem md MR Hk Hb Hsm 0 _ eq_refl) as DP. unfold zdisjoint in DP. cbn [fst snd] in DP.
pose proof ELEN as (E & _). unfold YGcfInstRcSec.MAP, YGcfInstRcSec.LEN in DP. rewrite <- E in DP. fold (AFg8.MAP ly r) in DP.
constructor.
- exact LO.
- exact IMG.
- rewrite Ha1. unfold AFfc.hdr. reflexivity.
- split; [unfold KSTACK, KSTACK_CF in *; lia | clear - Hcb1 Hcb2; lia].
- exact Hal.
- intros a Ha. apply HPRES. unfold KSTACK, KSTACK_CF in *. lia.
- pose proof M1 as M1'. unfold zone3 in M1'. split; [clear - D1 M1'; lia|]. split; [clear - D1 D2 D3 M2; lia|]. split; [exact D4|].
unfold AFg8.MAP in *. clear - DP M1' M2 M4 D1 D3 D2 hSP1 hSP2 hP1 hP2. numconst. lia.
- exact V1.
- split; [exact V4 | exact A4].
- split; [exact V3|]. split; [clear - hQ1; unfold zone3 in hQ1; lia|]. split; [clear - hQ1 hQ2 A4; numconst; lia | exact hQAL].
- exact mutex_val.
- exact SEED_ok.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The field's conclusion.                                                                                          *)
Lemma CUT : inst = as_inst B /\ ly_tsd ly = as_tsd B /\ Forall (cell_holds B ly rd0) (as_const B ly) /\
DMrcSecFc.sec_cut B ly X k W regs mem r o sm i.
Proof.
split; [exact INST|]. split; [exact HTSD0|]. split; [exact CONST|].
constructor.
- exact LO.
- exact IMG.
- exact Hk.
- exact HSP.
- exact HI.
- exact ARRF.
- exact GEOM.
- pose proof hdr_facts as (D1 & D2 & D3 & D4 & D5). splits; assumption.
- exact slot_geom.
- exact slot_val.
- exact ELEN.
- exact const_vals.
- exact inst_vals.
- exact junkD_vals.
- exact last_facts.
- exact maph_vals.
- exact qi_val.
- exact shadow_present.
- exact thread_present.
- exact tls_vals.
- exact hw_val.
- exact junk_vals.
- exact (@YGcfInstRcSec.MAPX rc ci cp AImg_reply B ly X Hp k r o sm W mem md MR Hk Hb Hsm).
- exact SXs.
- exact (@YGcfInstRcSec.SECX rc ci cp AImg_reply B ly X Hp W mem md MR).
- exact LST.
- exact FH_A.
Qed.
End f.

(* H4's secondary cut-read field at reply's image, at the cf cut relation, over rcc_pre_sec (DMrcSecNf.rc_sec_cut_nf_t). *)
Theorem rc_sec_cut_nf_of_cf : forall (B : asyms), TfibSyms B -> forall IOK Hp, YGcfInstBase.IOK_ok B IOK ->
DMrcSecNf.rc_sec_cut_nf_t B (@YGcfInstDrainR.ARXr_cf rc ci cp AImg_reply B IOK Hp).
Proof.
intros B TB IOK Hp HIOK. unfold DMrcSecNf.rc_sec_cut_nf_t.
intros inst ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi Hk Hst.
eapply CUT; eassumption.
Qed.

(* H4's secondary cut-read field at reply's image, at the cf cut relation. *)
Theorem rc_sec_cut_of_cf : forall (B : asyms), TfibSyms B -> forall IOK Hp, YGcfInstBase.IOK_ok B IOK ->
DMrcSecReads.rc_sec_cut_t B (@YGcfInstDrainR.ARXr_cf rc ci cp AImg_reply B IOK Hp).
Proof.
intros B TB IOK Hp HIOK. unfold DMrcSecReads.rc_sec_cut_t.
intros inst ly X k cbp W regs mem md r o sm i PRE.
exact (rc_sec_cut_nf_of_cf B TB IOK Hp HIOK inst ly X k cbp W regs mem md r o sm i (rcc_pre_sec_of_x _ _ _ _ _ _ _ _ _ _ _ PRE)).
Qed.
End d.
