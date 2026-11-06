(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DGfz.v (a working branch 30a1993588f, c5 + memnorm; file sha256 f72607ef7c18) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 22 image addresses moved by code-verified function pairs (21 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 2 pcs named in comments; 1 hand maps (agreloc-resolve-R.tsv, each with its evidence: pinned image bytes, YImgTop, the unit AF twin); no other numeral changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/DGfz.v, with its module paths, module names, addresses and numbers changed; 275 of its 813 lines of code are new or changed and 193 lines of the source are left out. *)
(* lib/B: the Deallocate drain arm at image B under the re-hide (WalkSigDrh.wsr_drn, the drain field CfF2a's record
   states PRIMED), at round 3 part 3; lib/A's MemnormDdrnRh.v at image B's addresses and module names: Quarantine::Drain recycles the popped chunks (DoRecycle, Recycle's secondary arm), and a secondary
   Recycle re-hides the dead map's shadow interior, so the arm runs at YG0dH.amreal' over YGcfRehidePost.RZ_cf and ends in
   the primed leaf YGcfMallocComposeERhBase.dealloc_leaf_raw_em_rh.  The interface is DIfaceRh.DIface_rh (DIface at the
   re-hide twins of its drain and Recycle fields; the walk reads neither) and the drain is the seam
   DIfaceRh.de_drain_m_rh_t (the field form of CfF2b's closed drain YGcfInstDrainTopRh.ds_drain_rh_cf), NOT the released
   MnDrain.de_drain_m_t, which a real recycle breaks.
   - [to_enq_rh]: DGg1.to_enq at amreal' (Deallocate's entry to Put's call of QuarantineCache::Enqueue; its
     segments re-hide nothing and lift by YA0nH.SRr_SRr').
   - [mid_walk_x_rh]: DGfz.mid_walk_x at amreal' (to_enq_rh, then the released Enqueue contract, lifted).
   - [TAILD_x_rh]: DGfz.TAILD_x over DIfaceRh.drain_spec_g_rh (Enqueue's return to Put's ret through Drain).  Drain's
     post is YGcfRehidePost.acall_post_x_rh; its dead set, read at Enqueue's return state, is moved to the entry state
     by YGcfRehidePost.dead_shadow_new_mono_l, and Put's stack frame is off it by dead_shadow_new_high.
   - [dealloc_drn_em_rh]: MemnormDmid.dealloc_drn_em over these, with the drain at [DRNrh].
   The scripts are DGg1's / DGfz's / MemnormDmid's at part 3 with the changes named above and DIface's field names
   renamed (di_ to DIfaceRh.dih_); the machine steps, the numerals and the image addresses are theirs, unchanged.
   rule 24: no function proved (kind: re-hide lift of an already proved walk composition). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1w YE3d YFeq DGbase YFex.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YFfj.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YFew DGgm DGfw DGgd DGgf YFeu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB13.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AllocG DeallocG AGif0n DMspec DGif0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif2reply ImgBaseDG DGif0reply DIfaceR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require DGg1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ErrnoG DGleafE ErrnoApart.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require AGif0reply DGfz MemnormT MemnormLocG MnEnq MemnormDmid.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YA0nH YG0dH YG0dHc YGcfAmx YGcfSecsStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfRehidePost DIfaceRh YGcfMallocComposeERhBase.
(* ErrnoG and ErrnoApart Require YA09, whose non-local [Ltac ::=] turns zify's euclidean-division
   conversion off in every file that Requires it; this file's proofs were written with it on (mid_walk_x's [lia] on
   the stack bounds fails without it), so it is turned back on here, for this file only. *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Ltac numc := ceil; unfold zone3, zone3cases, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize,
kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_unwinding, t_stats, DFSTACK, TFIB_IMG_END, DEP_STK, SHADOW_OFF,
TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W, TFIB_IAL_FLAG, TFIB_TP, TFIB_TSD in *.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Local Open Scope am_scope.
Set Printing Depth 100. Set Printing Width 200.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac cs_case HS HEn Htp kb :=
lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ => replace (Z_to_bv 5 k) with kb by (apply bv_eq; reflexivity) end;
let RR := fresh "RR" in rreg HS kb RR; rewrite RR;
first [ rewrite HEn by (cbv; lia); first [ refine (DGgm.Er _ _ _ _ _ _ _ _ _ _ _ _ _); reflexivity | symmetry; refine (DGgm.Er _ _ _ _ _ _ _ _ _ _ _ _ _); reflexivity ]
| rewrite Htp; reflexivity | symmetry; rewrite Htp; reflexivity ].
Lemma wvb_self : forall md, with_vm_backing (m_vm_lazy md) (m_vm_materialized md) md = md.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma qx_qthread : forall S k z tr, st_qthread (qx S k z tr) = st_qthread S.
Proof. intros S k z tr. unfold qx, depot_after, YFl0C.depot_after, dtick. destruct (z =? 0); reflexivity. Qed.

(* The free-less steps compose at the primed relation (DGbig.v's SRr'_bind_b / SRr'_ret_b). *)
Lemma SRr'_bind_d : forall (W : world tfibsegs) c (R Q : world tfibsegs -> config -> Prop),
YA0nH.SRr' tfibsegs YGcfRehidePost.RZ_cf W c R ->
(forall W' c', YA0nH.wle' tfibsegs YGcfRehidePost.RZ_cf W W' -> R W' c' -> YA0nH.SRr' tfibsegs YGcfRehidePost.RZ_cf W' c' Q) ->
YA0nH.SRr' tfibsegs YGcfRehidePost.RZ_cf W c Q.
Proof. exact (YA0nH.SRrG_bind tfibsegs (YA0nH.wle' tfibsegs YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans tfibsegs YGcfRehidePost.RZ_cf)). Qed.
Lemma SRr'_ret_d : forall (W : world tfibsegs) c (Q : world tfibsegs -> config -> Prop), Q W c -> YA0nH.SRr' tfibsegs YGcfRehidePost.RZ_cf W c Q.
Proof. exact (YA0nH.SRrG_ret tfibsegs (YA0nH.wle' tfibsegs YGcfRehidePost.RZ_cf) (YA0nH.wle'_refl tfibsegs YGcfRehidePost.RZ_cf)). Qed.

(* A released world step followed by a re-hiding one is a re-hiding step over the second one's set. *)
Lemma wle_wle_in_d : forall (segs : list Segment) (DS : Z -> Prop) (W1 W2 W3 : world segs),
  wle W1 W2 -> YA0nH.wle_in segs DS W2 W3 -> YA0nH.wle_in segs DS W1 W3.
Proof.
intros segs DS W1 W2 W3 H12 H23 a Ha. destruct (H23 a Ha) as [H2|H2]; [left; exact (H12 a H2) | right; exact H2].
Qed.

(* qx keeps st_secs, so every slot live at qx S k z tr is live at S with the same length (DGbig.v's qx_secs_live,
   r2-a e212e0532ab2, at the core's index-keyed dead_shadow_new). *)
Lemma qx_secs_live_d : forall S k z tr r sm0, nth_error (st_secs (qx S k z tr)) r = Some sm0 -> sm_live sm0 = true ->
exists sm2, nth_error (st_secs S) r = Some sm2 /\ sm_live sm2 = true /\ sm_len sm2 = sm_len sm0.
Proof.
intros S k z tr r sm0 H1 H2. exists sm0.
assert (QS : st_secs (qx S k z tr) = st_secs S) by (unfold qx, dtick, YFl0C.depot_after; destruct (z =? 0); reflexivity).
rewrite QS in H1. split; [exact H1|]. split; [exact H2 | reflexivity].
Qed.


Section e.
Variable B : asyms.
Hypothesis TS : TfibSyms B.
Variable U : list Z -> astate -> Prop.
Variable ft : sptr -> list Z -> M unit.
Variable ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable lpost : astate -> Prop.
Variable fpre : alayout -> astate -> world tfibsegs -> (word -> option byte) -> sptr -> Z -> Prop.
Variable dpost : Z -> alayout -> astate -> world tfibsegs -> list Z -> Z -> (word -> option byte) -> Prop.
Variable dbody : astate -> M unit.
Variable L24 : Z.
Variable QB : astate -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
(* DIface's memory predicate at Put's call of Enqueue (DGfz's MP). *)
Variable MP : (word -> option byte) -> Prop.
Hypothesis IF : DIfaceRh.DIface_rh B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP.
(* DGfz.MP_keep, the walk's keep law of MP: a memory equal to the seed's entry memory outside dmem_m's frame zones (the walk's stack
   window and thread / block cells DGif0.dwin_m, the depot zone, the internal allocator's zone, the block's shadow),
   over the seed's geometry DGgm.free_hyps, keeps MP.  cgif (MP := fun _ => True): trivial; cf: MP_keep_cf. *)
Hypothesis MP_keep : forall W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU (mem' : word -> option byte),
  DGgm.free_hyps W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU ->
  (forall x : word, ~ dwin_m ly (bv_unsigned (getr regs0 2)) p (bv_unsigned x) -> ~ dg_dzone ly (bv_unsigned x) ->
    ~ dg_izone (bv_unsigned x) -> ~ dshadow p nn (bv_unsigned x) -> mem' x = mem0 x) ->
  MP mem0 -> MP mem'.
(* The drain arm takes the raw frame (DGfz's [rawb] at true, as MemnormDmid.dealloc_drn_em instantiates it). *)
Local Notation rawb := true (only parsing).
Local Notation xr_raw := (DGfz.xr_raw B AOX true).
Local Notation Fshape := (DIfaceRh.dih_shape B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF).
Local Notation Fview := (DIfaceRh.dih_view B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF).
Local Notation Fdepot := (DIfaceRh.dih_depot B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF).
Local Notation Fdaok := (DIfaceRh.dih_dpost_aok B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF).

(* DGg1.to_enq at amreal' over RZ_cf (as DGbig.to_rcy is DGbig's): the free-less segments DGgd.segB, StackDepotPut
   and DGgf.segCm1 lift by YA0nH.SRr_SRr'; the continuation is at amreal'. *)
Lemma to_enq_rh : forall inst so bp ly S W regs mem md p n tr k hb1 j1 j2 j3 (Q : unit * astate -> world tfibsegs -> config -> Prop),
DeallocG.dealloc_pre tfibsegs B U ARX rpre fpre 1 inst so bp ly S W regs mem md p n tr -> In (p, n) (blocks S) ->
find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
0 <= hb1 < 256 -> val_mem tfibsegs (mrestrict (w_H W) mem) (sptr_addr B ly p - 16) 4 (2 + 256 * hb1) ->
DGgm.free_hyps W ly (dregs regs (sptr_addr B ly p) inst bp so) mem tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3 regs ->
(forall z (msE : machine_state) mat E5, aok (dtick S) (KDepot tr) z ->
  msE = mkst (ms_regs msE) (w64 0x360ec) (ms_mem msE) (seg_rom tfibsegs) ->
  (forall k0, (k0 < aHAVf)%nat ->
    ew E5 k0 = ew (DGgm.E0 ly (dregs regs (sptr_addr B ly p) inst bp so) tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3) k0) ->
  st_ok tfibsegs E5 DGfw.SS_E (restrict (w_H W) msE) ->
  dmem_m W ly (bv_unsigned (getr regs 2)) mem (sptr_addr B ly p) (req_size n) hb1 (dpost inst ly S W tr z) (ms_mem msE) ->
  YG0dH.amreal' tfibsegs YGcfRehidePost.RZ_cf ((enqueue (qk k) ;; dmd dbody) (qx S k z tr)) W (mkCfg msE (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
YG0dH.amreal' tfibsegs YGcfRehidePost.RZ_cf (ft p tr S) W (cfg_at tfibsegs 0x3191c regs mem md) Q.
Proof using IF TS.
intros inst so bp ly S W regs mem md p n tr k hb1 j1 j2 j3 Q PRE HBLK Hf Hst Hhb1 Hhdr FH HC.
destruct PRE as (HARX & HRP & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & Hpres & Hgp & Htp & Hr10 & Hr11 & Hr12 & Hr13 & Hr14 & Hr15 &
Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htrlen & PSO & PLEN & PBUF & Htr & Hp0 & HFP).
pose proof (dv_nonnull B W ly inst mem S p n (Fview inst ly S W mem md p n HARX HRP HFP HBLK)) as PNN.
rewrite (Fshape p n tr S k PNN HRP HBLK Hf Hst).
set (pa := sptr_addr B ly p) in *. set (nn := req_size n) in *. set (q := st_qthread S) in *.
set (regs0 := dregs regs pa inst bp so) in *.
unfold spZ, raZ in *.
assert (R2 : getr regs0 2%bv = getr regs 2%bv) by (unfold regs0; apply dregs_other; vm_compute; discriminate).
pose proof (DGg1.sp_facts_m W ly regs0 mem tr pa nn hb1 q j1 j2 j3 regs FH) as SPF. rewrite R2 in SPF. unfold DFSTACK in SPF.
assert (Usp : 0 <= bv_unsigned (getr regs 2) < 2 ^ 64) by apply u64_range.
assert (BP0 : bv_unsigned (getr regs0 12) = bp).
{ unfold regs0. rewrite dregs_12. unfold w64. apply unsigned_lit_small. clear - SPF Usp Hbp1 Hbp2. unfold kHighMemEnd, kHighMemBeg in *. lia. }
pose proof (DGgm.LYB W ly regs0 mem tr pa nn hb1 q j1 j2 j3 regs FH) as LB.
pose proof (DGgm.derived_ranges W ly regs0 mem tr pa nn hb1 q j1 j2 j3 regs FH) as DR.
pose proof (DGgm.N8_ge W ly regs0 mem tr pa nn hb1 q j1 j2 j3 regs FH) as [N8a N8b].
pose proof (DGgm.fh_Hp _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as ZP.
pose proof (DGgm.fh_Hp10 _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as Hp10.
pose proof (DGgm.fh_Hnn _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as Hnn.
unfold depot_put. cbn [bind askz ibind]. apply YG0dHc.amreal'_ask_depot.
unfold cfg_at. rewrite <- (wvb_self md) at 1.
eapply SRr'_bind_d; [exact (YA0nH.SRr_SRr' tfibsegs YGcfRehidePost.RZ_cf _ _ _ (DGgd.segB W ly regs0 mem md tr pa nn hb1 q j1 j2 j3 regs (m_vm_materialized md) FH))|].
intros W1 c1 _ (-> & msD & mat1 & E3 & -> & HshD & HEn3 & HS & MEQD & TRQ & PRESD).
rreg HS (1%bv : bv 5) Q1. rreg HS (2%bv : bv 5) Q2.
rewrite (HEn3 2%nat ltac:(cbv; lia)), (DGgm.E2 ly regs0 tr pa nn hb1 q j1 j2 j3) in Q2.
assert (SPD : bv_unsigned (getr (ms_regs msD) 2) = bv_unsigned (getr regs0 2) - 48).
{ rewrite Q2. unfold w64. rewrite unsigned_lit_small; [reflexivity|]. rewrite R2. clear - SPF Usp. numc. lia. }
rewrite HshD. eapply SRr'_bind_d.
{ apply YA0nH.SRr_SRr'. apply (Fdepot inst ly S W mem md tr (ms_regs msD) (ms_mem msD) (with_vm_backing (m_vm_lazy md) mat1 md) bp HARX Htr).
  - intros x Hx. apply (proj1 MEQD).
    + destruct Hx as [Hd|[Hc _]]; [exact (proj1 (DGg1.DZONE_out_m W ly regs0 mem tr pa nn hb1 q j1 j2 j3 regs FH _ Hd)) |
      exact (DGg1.CZONE_out_m W ly regs0 mem tr pa nn hb1 q j1 j2 j3 regs FH _ Hc)].
    + destruct Hx as [Hd|[_ Hi]]; [exact (proj1 (proj2 (DGg1.DZONE_out_m W ly regs0 mem tr pa nn hb1 q j1 j2 j3 regs FH _ Hd))) | exact Hi].
  - rreg HS (10%bv : bv 5) R. rewrite R, (HEn3 12%nat ltac:(cbv; lia)), (DGgm.E12 ly regs0 tr pa nn hb1 q j1 j2 j3).
    unfold regs0. rewrite dregs_12. reflexivity.
  - rreg HS (11%bv : bv 5) R. rewrite R, (HEn3 36%nat ltac:(cbv; lia)), (DGgm.EaLEN ly regs0 tr pa nn hb1 q j1 j2 j3). reflexivity.
  - rreg HS (3%bv : bv 5) R. rewrite R, (HEn3 3%nat ltac:(cbv; lia)), (DGgm.Er ly regs0 tr pa nn hb1 q j1 j2 j3 3 3%bv eq_refl).
    unfold regs0. rewrite dregs_other by (vm_compute; discriminate). exact Hgp.
  - rreg HS (4%bv : bv 5) R. rewrite R. reflexivity.
  - rreg HS (1%bv : bv 5) R. rewrite R. apply YK0s.ret_ok_even. reflexivity.
  - intros i Hi. pose proof (TRQ i Hi) as TQ. rewrite BP0 in TQ. exact TQ.
  - exact Hbp3.
  - clear - SPF Hbp1. lia.
  - exact Hbp2.
  - right. rewrite SPD, R2. lia.
  - rewrite SPD, R2. replace (bv_unsigned (getr regs 2) - 48) with (bv_unsigned (getr regs 2) + (-3) * 16) by lia.
    rewrite Z_mod_plus_full. exact Hal.
  - rewrite SPD, R2. clear - SPF. unfold DEP_STK, YFl0C.DEP_STK in *. lia.
  - rewrite SPD, R2. lia.
  - intros a Ha. rewrite SPD in Ha. apply PRESD. unfold DEP_STK, YFl0C.DEP_STK, DFSTACK in *. lia. }
intros W2 c2 _ (-> & z & regs4 & mem4 & mat4 & -> & HP4 & Hfr4 & Hpr4 & DP4). srr_norm_model.
rewrite SPD in Hfr4.
pose proof (Fdaok _ _ _ _ _ _ _ DP4) as AOK.
rewrite Q1. eapply SRr'_bind_d.
{ apply YA0nH.SRr_SRr'. apply (DGgf.segCm1 W ly regs0 mem md tr pa nn hb1 q j1 j2 j3 regs FH msD E3 regs4 mem4 mat4).
  split; [exact HshD|]. split; [exact HEn3|]. split; [exact HS|]. split; [exact HP4|]. split; [exact Hfr4|].
  split; [exact Hpr4|]. split; [exact MEQD | exact PRESD]. }
intros W3 c3 _ (-> & msE & matE & E5 & -> & HshE & HEn5 & HS5 & EQE & PRES5).
apply SRr'_ret_d. exists z. split; [exact AOK|].
assert (BT : bv_unsigned (ew E5 32) = ly_T ly).
{ rewrite (HEn5 32%nat ltac:(cbv; lia)), (DGgm.EaT ly regs0 tr pa nn hb1 q j1 j2 j3). unfold w64. apply unsigned_lit_small.
  destruct LB as (LB1 & LB2 & _). clear - LB1 LB2. numc. lia. }
assert (B10 : bv_unsigned (ew E5 10) = pa).
{ rewrite (HEn5 10%nat ltac:(cbv; lia)), (DGgm.E10 ly regs0 tr pa nn hb1 q j1 j2 j3), Hp10. unfold w64. apply unsigned_lit_small.
  clear - DR N8a. numc. lia. }
assert (R38 : rho_of E5 38%nat = 2 + 256 * hb1).
{ unfold rho_of. rewrite (HEn5 38%nat ltac:(cbv; lia)), (DGgm.EaHW ly regs0 tr pa nn hb1 q j1 j2 j3). unfold w64, DGgm.HWv.
  apply unsigned_lit_small. lia. }
assert (T1V : zev (rho_of E5) T1term = 3 + 256 * hb1) by (apply T1_val; [exact Hhb1 | exact R38]).
assert (OT : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> off_img a) by (intros a Ha; exact (zone3_off_img _ _ a (proj1 LB) Ha)).
assert (OP : forall a, pa - 16 <= a < pa + 8 -> off_img a) by (intros a Ha; apply (zone3_off_img _ _ a ZP); lia).
assert (DM : dmem_m W ly (bv_unsigned (getr regs0 2)) mem pa nn hb1 (dpost inst ly S W tr z) (ms_mem msE)).
{ apply (DGg1.dmem_m_ok W ly regs0 mem tr pa nn hb1 q j1 j2 j3 regs FH (dpost inst ly S W tr z) (ms_mem msD) mem4 (ms_mem msE)
    MEQD Hfr4 Hpr4 DP4 EQE PRES5).
  - intros a [[Ha|Ha]|[Ha|Ha]].
    + eapply (st_ok_window_apresent_off (w_H W) E5 _ _ 34 _ a HS5); [reflexivity
      | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BT; clear - Ha; unfold t_unwinding in *; lia
      | apply OT; clear - Ha; unfold kThreadObjSize, t_unwinding in *; lia].
    + eapply (st_ok_window_apresent_off (w_H W) E5 _ _ 35 _ a HS5); [reflexivity
      | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BT; clear - Ha; unfold t_stats in *; lia
      | apply OT; clear - Ha; unfold kThreadObjSize, t_stats in *; lia].
    + eapply (st_ok_window_apresent_off (w_H W) E5 _ _ 36 _ a HS5); [reflexivity
      | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite B10; clear - Ha; lia
      | apply OP; clear - Ha; lia].
    + eapply (st_ok_window_apresent_off (w_H W) E5 _ _ 37 _ a HS5); [reflexivity
      | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite B10; clear - Ha; lia
      | apply OP; clear - Ha; lia].
  - memv HS5 36%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite B10; lia | apply DGgf.denot_by_zev; [reflexivity | lia | exact T1V] | lia].
  - memv HS5 36%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite B10; lia
    | cbn [sv_denot]; rewrite (HEn5 39%nat ltac:(cbv; lia)), (DGgm.EaN ly regs0 tr pa nn hb1 q j1 j2 j3); unfold w64; rewrite Zbv_add_unsigned; f_equal; lia
    | lia].
  - memv HS5 34%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite BT; unfold t_unwinding; lia | reflexivity | lia]. }
rewrite R2 in DM.
pose proof AOK as AOK0.
destruct AOK as [-> | [-> _]].
- cbn [Z.eqb ret ibind]. eapply YG0dHc.amreal'_pure; [reflexivity|]. exact (HC 0 msE matE E5 AOK0 HshE HEn5 HS5 DM).
- cbn [Z.eqb bind get ret ibind].
  lazymatch goal with |- context [mcheck ?b1 469488] => destruct b1 end; cbn [mcheck ret ibind]; [|exact I].
  lazymatch goal with |- context [mcheck ?b2 460508] => destruct b2 end; cbn [mcheck ret put ibind]; [|exact I].
  eapply YG0dHc.amreal'_pure; [reflexivity|]. exact (HC 1 msE matE E5 AOK0 HshE HEn5 HS5 DM).
Qed.

Section f.
Variables (inst so bp : Z) (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (p : sptr) (n : Z) (tr : list Z).
Hypothesis PRE : dealloc_pre tfibsegs B U ARX rpre fpre 1 inst so bp ly S W regs mem md p n tr.
(* MP at Deallocate's entry memory (the walk's entry premise). *)
Hypothesis HMP : MP mem.
Hypothesis HBLK : In (p, n) (blocks S).
Hypothesis DRAIN : kQuarantineCacheMax < qc_bytes (st_qthread S) + req_size n + (if need_new_batch (st_qthread S) then kBatchBytes else 0).
Let pa : Z := sptr_addr B ly p.
Let nn : Z := req_size n.
Let regs0 : bvmap 5 word := dregs regs pa inst bp so.
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Notation q := (st_qthread S).
Local Notation T := (ly_T ly).

(* The machine at Enqueue's return into Put (0x360e0): the seed's symbolic state at the call (DGfw.SS_E over an
   env agreeing with the DGgm seed's E0), the enqueue's post (DIfaceRh.dih_enqueue) and the walk's agreement with the entry
   memory at the call. *)
Definition enq_ret (k : chunk) (hb1 j1 j2 j3 : Z) (z : Z) (msE : machine_state) (matE : list word) (E5 : env)
(W5 : world tfibsegs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (X' : astate) (nb : option Z) : Prop :=
let X := qx S k z tr in let mdE := with_vm_backing (m_vm_lazy md) matE md in
msE = mkst (ms_regs msE) (w64 0x360ec) (ms_mem msE) (seg_rom tfibsegs) /\
(forall k0, (k0 < aHAVf)%nat -> ew E5 k0 = ew (DGgm.E0 ly regs0 tr pa nn hb1 q j1 j2 j3) k0) /\
st_ok tfibsegs E5 DGfw.SS_E (restrict (w_H W) msE) /\
(forall a, sp0 - DFSTACK <= a < sp0 -> apresent (w_H W) (ms_mem msE) a) /\
acall_post_x B ARX AOX inst QSTACK ly X W (ms_regs msE) (ms_mem msE) mdE (fun _ => False) ly X' W5 regs' mem' md' /\
(rawb = true -> acall_raw_x B AOX inst QSTACK ly X W (ms_regs msE) (ms_mem msE) mdE (fun _ => False) ly X' W5 regs' mem' md') /\
st_qthread X' = qc_push (st_qthread X) (qk k) nb /\
match nb with None => need_new_batch (st_qthread X) = false | Some _ => need_new_batch (st_qthread X) = true end /\
st_chunks X' = st_chunks X /\ st_qglobal X' = st_qglobal X /\
(forall a, AOX ly X' a -> AOX ly X a) /\
(kQuarantineCacheMax < qc_bytes (st_qthread X') -> QB X' /\ Z.of_nat (length (all_batches X')) <= L24) /\
val_mem tfibsegs (mrestrict (w_H W5) mem') (ly_T ly + t_qc + 24) 8 (qc_bytes (st_qthread X')) /\
(forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ ascratch B DFSTACK_G regs (bv_unsigned x) -> ~ (pa <= bv_unsigned x < pa + nn) ->
  ms_mem msE x = mem x).

(* DGfz.leaf0x at YGcfRehidePost.dealloc_post_rh: leaf0 with the raw facts of Put's tail (TAILD_x_rh): Put's run to Drain keeps every byte off Put's 80-byte frame (the
   memory at Drain's call [memC] against Enqueue's return memory [mem5]), the drain's extra conjunct [XRd], and Put's
   run after Drain keeps every byte off the frame (the leaf's memory against Drain's return memory [mem6]). *)
Definition leaf0x_rh (XRd : fxrel) (X5 : astate) (W5 : world tfibsegs) (mem5 : word -> option byte)
(r : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
YGcfRehidePost.dealloc_post_rh tfibsegs B ARX AOX inst ly S W regs mem md (fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n)
  ly' (snd r) W' regs' mem' md' /\
(rawb = true -> forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ AOX ly' (snd r) (bv_unsigned x) ->
  ~ ascratch B DFSTACK_G regs (bv_unsigned x) ->
  ~ (p <> PNull /\ sptr_addr B ly p <= bv_unsigned x < sptr_addr B ly p + req_size n) -> mem' x = mem x) /\
lpost (snd r) /\
exists regsC memC mdC regs6 mem6 md6,
(forall x : word, ~ (sp0 - 80 <= bv_unsigned x < sp0) -> memC x = mem5 x) /\
XRd inst YFeuC.DSTACK ly X5 W5 regsC memC mdC (fun _ => False) ly (snd r) W' regs6 mem6 md6 /\
(forall x : word, ~ (sp0 - 80 <= bv_unsigned x < sp0) -> mem' x = mem6 x).


Section g.
Variables (k : chunk) (hb1 j1 j2 j3 : Z).
Hypothesis HK : find_user (st_chunks S) p = Some k.
Hypothesis HKS : ck_state k = CAllocated.
Hypothesis HKR : ck_req k = n.
Hypothesis PNN : p <> PNull.
Hypothesis FH : DGgm.free_hyps W ly regs0 mem tr pa nn hb1 q j1 j2 j3 regs.
Local Notation E0 := (DGgm.E0 ly regs0 tr pa nn hb1 q j1 j2 j3).
Local Notation QBFv := (DGgm.QBFv nn q).
Local Notation SOv := (bv_unsigned (getr regs0 13)).
Local Notation EaT := (DGgm.EaT ly regs0 tr pa nn hb1 q j1 j2 j3).
Local Notation EaQBF := (DGgm.EaQBF ly regs0 tr pa nn hb1 q j1 j2 j3).
Lemma R2 : getr regs0 2 = getr regs 2.
Proof. unfold regs0. apply dregs_other; intros X; vm_compute in X; discriminate X. Qed.
Lemma E2 : ew E0 2 = getr regs 2.
Proof. rewrite (DGgm.E2 ly regs0 tr pa nn hb1 q j1 j2 j3). exact R2. Qed.
Lemma E1 : ew E0 1 = getr regs 1.
Proof. rewrite (DGgm.E1 ly regs0 tr pa nn hb1 q j1 j2 j3). unfold regs0. apply dregs_other; intros X; vm_compute in X; discriminate X. Qed.
Lemma E3 : ew E0 3 = getr regs 3.
Proof. rewrite (DGgm.Er ly regs0 tr pa nn hb1 q j1 j2 j3 3 3%bv eq_refl). unfold regs0. apply dregs_other; intros X; vm_compute in X; discriminate X. Qed.
Lemma Htp0 : getr regs0 4 = w64 TFIB_TP. Proof. exact (DGgm.fh_Htp _ _ _ _ _ _ _ _ _ _ _ _ _ FH). Qed.
Lemma PREd : ARX inst ly S W mem md /\ rpre S n /\ YK0s.ret_ok (getr regs 1) /\ 4096 <= bv_unsigned (getr regs 1) /\
sp0 mod 16 = 0 /\ ly_stk_lo ly + DFSTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\
getr regs 3 = w64 (as_gp B) /\ U tr S /\ fpre ly S W mem p n.
Proof.
pose proof PRE as P. unfold dealloc_pre in P.
destruct P as (HARX & HRP & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & _ & Hgp & P).
do 17 (destruct P as [_ P]). destruct P as (HTU & _ & HFP).
unfold spZ, raZ, DFSTACK_G in *. fold sp0 in Hal, Hlo, Hbot, Hhi. unfold DFSTACK.
repeat (split; [assumption|]). exact HFP.
Qed.
Lemma TSTK : ly_T ly + kThreadObjSize <= ly_stk_lo ly \/ ly_stk_hi ly <= ly_T ly.
Proof.
pose proof (DGgm.fh_LY _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as LO.
pose proof (pairwise_nth zdisjoint _ 2 8 _ _ (lo_disj _ LO) eq_refl eq_refl ltac:(lia)) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.
Lemma Enn : nn = ck_n k. Proof. unfold nn, ck_n. rewrite HKR. reflexivity. Qed.

(* DGfz.TAILD_x under the re-hide: the drain contract is DIfaceRh.drain_spec_g_rh (amreal' over RZ_cf, the call post
   YGcfRehidePost.acall_post_x_rh), the walk is at amreal' and the leaf is leaf0x_rh.  The machine segments before
   and after Drain re-hide nothing (YA0nH.SRr_SRr', YG0dHc.amreal'_then_SRr).  The leaf's dead set is Drain's, read
   at Enqueue's return state X' and moved to the entry S by dead_shadow_new_mono_l (at the core's index-keyed set:
   Enqueue keeps st_secs, the premise [st_secs X' = ..] from mid_walk_x_rh, and qx keeps it, qx_secs_live_d); the stack
   frame's uses of Drain's view frame are off the dead set by dead_shadow_new_high. *)
Lemma TAILD_x_rh : forall (XRd : fxrel), DIfaceRh.drain_spec_g_rh B ARX AOX dbody L24 QB XRd -> xr_raw XRd ->
forall z msE matE E5 (W5 : world tfibsegs) regs' mem' md' (X' : astate) nb,
enq_ret k hb1 j1 j2 j3 z msE matE E5 W5 regs' mem' md' X' nb -> st_secs X' = st_secs (qx S k z tr) ->
YG0dH.amreal' tfibsegs YGcfRehidePost.RZ_cf (dmd dbody X') W5 (cfg_at tfibsegs 0x360e0 regs' mem' md') (leaf0x_rh XRd X' W5 mem').
Proof.
intros XRd DRNg XRdr z msE matE E5 W5 regs' mem' md' X' nb ER HSX.
unfold enq_ret in ER. cbv zeta in ER.
destruct ER as (HshE & HEn5 & HS & PRESE & (HA5 & LLE & WLE & CS & SIO & FR & PRS) & FRrb & HQ' & Hnb & HCK' & HQG' & HOWN' & HQL & HQB & AGPr).
set (X := qx S k z tr) in *. set (mdE := with_vm_backing (m_vm_lazy md) matE md) in *.
assert (AGP : forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly S a -> ~ ascratch B DFSTACK_G regs a -> ~ (pa <= a < pa + nn) ->
  aview tfibsegs (w_H W) (ms_mem msE) a = aview tfibsegs (w_H W) mem a).
{ intros a Ra N1 N2 N3. apply aview_same. apply AGPr; rewrite unsigned_lit_small by exact Ra; assumption. }
pose proof PREd as (HARX0 & HRP & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & Hgp & HTU & HFP).
pose proof (DGgm.LYB _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as LB.
pose proof (DGgm.fh_Hp _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as P1.
pose proof (DGgm.fh_Hqb _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as (Qa & Qb).
pose proof (DGgm.fh_Hnn _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as Hnn.
pose proof Hwx_tfa as Hwx. assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof (DGgm.fh_Hso _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as HSOF. rewrite R2 in HSOF. fold sp0 in HSOF.
assert (HXq : st_qthread X = q) by (subst X; apply qx_qthread).
assert (QB' : qc_bytes (st_qthread X') = QBFv).
{ rewrite HQ'. rewrite HXq in Hnb |- *. unfold DGgm.QBFv.
destruct nb; rewrite Hnb; cbn [qc_push qc_bytes]; unfold qk; change (ck_n {| ck_beg := ck_beg k; ck_req := ck_req k; ck_state := CQuarantined |}) with (ck_n k); rewrite <- Enn; lia. }
assert (DRX' : kQuarantineCacheMax < qc_bytes (st_qthread X')).
{ rewrite QB'. unfold DGgm.QBFv. exact DRAIN. }
destruct (HQL DRX') as [QLX' L24X'].
(* the drain branch of dmd *)
unfold dmd. cbn [bind get ibind]. replace (qc_bytes (st_qthread X') <=? kQuarantineCacheMax) with false by (symmetry; apply Z.leb_gt; exact DRX').
rreg HS (2%bv : bv 5) Q2. rewrite (HEn5 2%nat ltac:(cbv; lia)), E2 in Q2.
assert (SPE : spZ (ms_regs msE) = sp0 - 80).
{ unfold spZ. rewrite Q2. unfold sp0, w64. rewrite unsigned_lit_small by (clear - Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, DFSTACK in *; unfold sp0 in *; lia). reflexivity. }
unfold ascratch in FR. rewrite SPE in FR, PRS.
assert (BV2 : bv_unsigned (ew E5 2) = sp0) by (rewrite (HEn5 2%nat ltac:(cbv; lia)), E2; reflexivity).
assert (BV13 : bv_unsigned (ew E5 13) = SOv) by (rewrite (HEn5 13%nat ltac:(cbv; lia)), (DGgm.E13 ly regs0 tr pa nn hb1 q j1 j2 j3); reflexivity).
assert (NOWN : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> ~ AOX ly X a /\ ~ AOX ly X' a).
{ intros a Ha. split.
- intros O. destruct (DIfaceRh.dih_owned_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md p n k z tr a HARX0 HRP HBLK HK O) as [O'|O'].
  + exact (DIfaceRh.dih_stack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md a HARX0 Ha O').
  + pose proof (DGgm.fh_Hp_static _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as PST.
    pose proof (DGgm.N8_ge _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as (_ & N8b & _).
    assert (Hb : pa <= a < pa + nn) by exact O'.
    destruct (PST a ltac:(clear - Hb N8b; lia)) as [N1 _]. exact (N1 Ha).
- exact (DIfaceRh.dih_stack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly X' W5 mem' md' a HA5 Ha). }
assert (AGS : forall a, sp0 - 80 <= a < ly_stk_hi ly -> aview tfibsegs (w_H W5) mem' a = aview tfibsegs (w_H W) (ms_mem msE) a).
{ intros a Ha. destruct (NOWN a ltac:(clear - Ha Hlo; unfold DFSTACK in *; lia)) as [N1 N2]. apply FR; [clear - Ha Usp Hlo Hhi LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, kHighMemEnd, DFSTACK in *; unfold sp0 in *; lia | exact N1 | exact N2 | | intros []].
unfold ascratch. rewrite (ts_errno _ TS). unfold TFIB_ERRNO, QSTACK. clear - Ha Hlo LB. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, DFSTACK in *. unfold sp0 in *. lia. }
assert (HP : regs_preserved (ms_regs msE) regs') by (intros r Hr'; apply CS; exact Hr').
lazymatch type of HS with st_ok _ _ ?ss ?ms0 =>
let m := eval vm_compute in (ss_mem ss) in
lazymatch m with ?r0 :: ?r1 :: ?r2 :: ?r3 :: ?r4 :: ?rest =>
pose proof (st_ok_after_call tfibsegs 112 E5 ss ms0 regs' (mrestrict (w_H W5) mem') (trim_lo r0 (-80) :: r1 :: r2 :: r3 :: r4 :: nil) 0x360e0 HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(apply submem_keep; [apply subregion_trim_lo|]; apply submem_keep; [apply subregion_refl|]; apply submem_keep; [apply subregion_refl|];
apply submem_keep; [apply subregion_refl|]; apply submem_keep; [apply subregion_refl|]; apply submem_nil)
ltac:(vm_compute; reflexivity) HP) as HS1;
let rsv := eval vm_compute in (trim_lo r0 (-80) :: r1 :: r2 :: r3 :: r4 :: nil) in
change (trim_lo r0 (-80) :: r1 :: r2 :: r3 :: r4 :: nil) with rsv in HS1;
let ss2 := eval vm_compute in (ss_after_call ss rsv 112 0x360e0) in
change (ss_after_call ss rsv 112 0x360e0) with ss2 in HS1
end
end.
cbn [ms_mem restrict] in HS1.
lazymatch type of HS1 with Forall _ ?L -> _ =>
assert (KEPT : Forall (region_kept tfibsegs E5 (mrestrict (w_H W) (ms_mem msE)) (mrestrict (w_H W5) mem')) L);
[ repeat apply Forall_cons; try apply Forall_nil;
(apply kept_of_aview2; cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; rewrite ?BV2, ?BV13;
[ intros a Ha; apply AGS; clear - Ha HSOF; lia
| intros a Ha; split; [apply AGS; clear - Ha HSOF; lia | clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, DFSTACK, TFIB_IMG_END in *; unfold sp0 in *; lia] ])
| specialize (HS1 KEPT); clear KEPT ]
end.
set (En6 := havoc E5 112 (map (getr regs') CLOB)) in HS1.
assert (HEn6 : forall k0, (k0 < aHAVf)%nat -> ew En6 k0 = ew E0 k0) by (intros k0 Hk0; subst En6; unfold aHAVf in Hk0; rewrite ew_havoc_old by lia; apply HEn5; exact Hk0).
assert (RV : val_mem tfibsegs (mrestrict (w_H W5) mem') (ly_T ly + (t_qc + 24)) (N.to_nat 8) QBFv).
{ rewrite <- QB'. replace (ly_T ly + (t_qc + 24)) with (ly_T ly + t_qc + 24) by lia. exact HQB. }
apply (st_ok_add_region _ _ _ (YP09.mkRegion (Some 32%nat) (t_qc + 24) (t_qc + 32) 0 0 [YP09.mkChunk (t_qc + 24) (CVal 8 (SOff 50%nat 0))])) in HS1;
[ | reflexivity
| unfold YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem];
rewrite (HEn6 32%nat ltac:(cbv; lia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; lia);
split; [clear - LB; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, t_qc in *; lia|]; split; [clear - LB; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, t_qc in *; lia|]; split; [intros o Ho; lia|];
apply Forall_cons; [|apply Forall_nil];
eapply (chunk_ok_val tfibsegs En6 _ _ _ 8 (SOff 50%nat 0) QBFv);
[ cbn [sv_denot]; rewrite (HEn6 50%nat ltac:(cbv; lia)), EaQBF; unfold w64; rewrite Zbv_add_unsigned; f_equal; lia
| clear - Qa Qb Hnn; unfold DGgm.QBFv, DGgm.QBMAX, kQuarantineCacheMax, kBatchBytes in *; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); destruct (need_new_batch q); lia
| cbn; lia | exact RV ]
| cbn [all_disjoint ss_mem]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite ?(HEn6 32%nat ltac:(cbv; lia)), ?(HEn6 2%nat ltac:(cbv; lia)), ?(HEn6 13%nat ltac:(cbv; lia)), ?EaT, ?E2, ?(DGgm.E13 ly regs0 tr pa nn hb1 q j1 j2 j3); unfold w64; rewrite unsigned_lit_small by (clear - LB; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; lia);
fold sp0; pose proof (DGgm.stack_ivs _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as (IT & _); rewrite R2 in IT; fold sp0 in IT; pose proof TSTK as TK;
clear - IT LB TK HSOF Hlo Hhi; unfold kThreadObjSize, t_qc, DFSTACK in *; repeat split; lia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
rewrite <- (restrict_mkst_fx (w_H W5)) in HS1. rename HS1 into HS'. clear HS. rename HS' into HS.
unfold cfg_at. rewrite <- (wvb_self md') at 1. change (w64 0x360e0) with (Z_to_bv 64 0x360e0).
apply YG0dHc.amreal'_after_SRr'. apply YA0nH.SRr_SRr'.
srr_run_sh tfibtbl_rtF_ok HS.
rename HF into HF0. clear HFr.
srr_branch_sh tfibtbl_rtF_ok HS.
2:{ exfalso. match goal with H : branch_taken _ _ _ = false |- _ => rewrite branch_ltu_U in H; apply Z.ltb_ge in H; revert H end.
rewrite !U_zev by reflexivity. cbn [zev zalu_raw]. unfold rho_of. rewrite (HEn6 50%nat ltac:(cbv; lia)), EaQBF, Z.add_0_r.
unfold w64. rewrite unsigned_lit_small by (clear - Qa Qb Hnn; unfold DGgm.QBFv, DGgm.QBMAX, kQuarantineCacheMax, kBatchBytes in *; destruct (need_new_batch q); lia).
rewrite !zcanon_id by (clear - Qa Qb Hnn; unfold DGgm.QBFv, DGgm.QBMAX, kQuarantineCacheMax, kBatchBytes, M64 in *; destruct (need_new_batch q); lia).
pose proof DRAIN as ND. clear - ND. unfold DGgm.QBFv, kQuarantineCacheMax, kBatchBytes in *.
destruct (need_new_batch q); lia. }
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_sh tfibtbl_rtF_ok HS. rename HF into HF1. clear HFr.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msC end.
lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing _ ?mx _)) _ => rename mx into matC end.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W5) En6 _ _ HS eq_refl) as HshC; cbn [ss_pc] in HshC.
assert (FR1 : forall x : word, ~ (sp0 - 80 <= bv_unsigned x < sp0) -> ms_mem msC x = mem' x).
{ intros x Hx1. rewrite (HF1 x); [apply (HF0 x)|].
all: intros Hw; destruct (in_wrange_windows _ _ _ Hw) as (b & lo & hi & Hin & Hrg);
lazymatch type of Hin with In _ (windows ?rs) => let ws := eval vm_compute in (windows rs) in change (windows rs) with ws in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [Hin|Hin];
[ injection Hin as <- <- <-; cbn [fst snd base_val] in Hrg; rewrite ?(HEn6 2%nat ltac:(cbv; lia)), ?E2, ?(HEn6 32%nat ltac:(cbv; lia)), ?EaT in Hrg; unfold w64 in Hrg;
rewrite ?unsigned_lit_small in Hrg by (clear - LB; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; lia); clear - Hx1 Hrg; unfold DFSTACK, t_qc in *; unfold sp0 in *; lia |]);
destruct Hin. }
clear HF1 HF0.
assert (PRES' : forall a, sp0 - DFSTACK <= a < sp0 - 80 -> apresent (w_H W5) mem' a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 80 - QSTACK)) as [L2|L2].
2:{ apply PRS. clear - Ha L2. unfold QSTACK in *. lia. }
assert (EQa : aview tfibsegs (w_H W5) mem' a = aview tfibsegs (w_H W) (ms_mem msE) a).
{ destruct (NOWN a ltac:(clear - Ha Hlo Hhi; unfold DFSTACK in *; lia)) as [M1 M2]. apply FR; [clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, DFSTACK in *; unfold sp0 in *; lia | exact M1 | exact M2 | | intros []].
unfold ascratch; rewrite (ts_errno _ TS); unfold TFIB_ERRNO; clear - Ha L2 Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, DFSTACK, QSTACK in *; unfold sp0 in *; lia. }
pose proof (PRESE a ltac:(clear - Ha; lia)) as P; apply apresent_mbyte in P as [b Hb].
assert (A : aview tfibsegs (w_H W) (ms_mem msE) a = Some (bv_unsigned b)) by (unfold aview; rewrite Hb; reflexivity).
rewrite <- EQa in A; apply aview_some in A as (b' & Hb' & _).
exact (mbyte_high_apresent (w_H W5) mem' a b' ltac:(clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, DFSTACK, TFIB_IMG_END in *; unfold sp0 in *; lia) Hb'). }
assert (PRESC : forall a, sp0 - DFSTACK <= a < sp0 -> apresent (w_H W5) (ms_mem msC) a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 80)) as [L1|L1]; [|destruct (Z_lt_le_dec a (sp0 - 48)) as [L2|L2]].
- apply (apresent_same (w_H W5) mem'); [apply FR1; rewrite unsigned_lit_small by (clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, DFSTACK in *; unfold sp0 in *; lia); clear - L1; lia | apply PRES'; clear - Ha L1; lia].
- eapply (st_ok_window_apresent (w_H W5) En6 _ _ 1 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn6 2%nat ltac:(cbv; lia)), E2; clear - L1 L2; unfold sp0; lia | clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, DFSTACK, TFIB_IMG_END in *; unfold sp0 in *; lia].
- eapply (st_ok_window_apresent (w_H W5) En6 _ _ 3 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn6 2%nat ltac:(cbv; lia)), E2; clear - L2 Ha; unfold sp0; lia | clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, DFSTACK, TFIB_IMG_END in *; unfold sp0 in *; lia]. }
assert (AGC : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 80 <= a < sp0) -> aview tfibsegs (w_H W5) (ms_mem msC) a = aview tfibsegs (w_H W5) mem' a).
{ intros a Ha N1. apply aview_same. apply FR1; rewrite unsigned_lit_small by exact Ha; assumption. }
assert (WDEC : forall a, (sp0 - 80 <= a < sp0) \/ ~ (sp0 - 80 <= a < sp0)) by (intros a; clear; lia).
assert (VISC : forall a, aview tfibsegs (w_H W5) mem' a <> None -> aview tfibsegs (w_H W5) (ms_mem msC) a <> None).
{ intros a Hv HN. unfold aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
destruct (w_H W5 x) eqn:Hx; [exact (Hv HN)|].
destruct (seg_rom tfibsegs x) eqn:ROM; [destruct (ms_mem msC x); discriminate|].
destruct (ms_mem msC x) as [|] eqn:E'; [discriminate|]. clear HN.
destruct (mem' x) as [b0|] eqn:E0'; [clear Hv | exact (Hv eq_refl)].
set (a' := bv_unsigned x). assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
destruct (WDEC a') as [C|C].
- destruct (PRESC a' ltac:(clear - C; unfold DFSTACK; lia)) as [_ [bb Hb]]. rewrite Ex in Hb. congruence.
- rewrite (FR1 x C) in E'. congruence. }
assert (HSKC : forall a, in_band_rw a -> w_H W5 (w64 a) = true -> ms_mem msC (w64 a) = mem' (w64 a)).
{ intros a Ha Hx. unfold w64 in *.
assert (Ha' : 0 <= a < 2 ^ 64) by (clear - Ha; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; lia).
destruct (WDEC a) as [C|C].
- exfalso. destruct (PRESC a ltac:(clear - C; unfold DFSTACK; lia)) as [Hh _]. rewrite Hx in Hh. discriminate.
- apply FR1; rewrite unsigned_lit_small by exact Ha'; assumption. }
assert (ARC : ARX inst ly X' W5 (ms_mem msC) (with_vm_backing (m_vm_lazy md') matC md')).
{ apply (DIfaceRh.dih_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly X' W5 mem' md' (ms_mem msC) _ HA5).
- intros a Ha O. destruct (WDEC a) as [C|C]; [exfalso; exact (proj2 (NOWN a ltac:(clear - C Hlo Hhi; unfold DFSTACK in *; lia)) O) | exact (AGC a Ha C)].
- exact VISC.
- apply m_vmmaps_wvb.
- apply m_vm_lazy_wvb.
- apply eager_used_wvb.
- exact HSKC. }
apply SRr_ret. rewrite HshC.
rreg HS (1%bv : bv 5) C1. rreg HS (2%bv : bv 5) C2. rreg HS (3%bv : bv 5) C3. rreg HS (4%bv : bv 5) C4.
rreg HS (10%bv : bv 5) C10. rreg HS (11%bv : bv 5) C11. rreg HS (12%bv : bv 5) C12.
cbn [sv_denot] in C1, C2, C3, C4, C10, C11, C12.
rewrite (HEn6 2%nat ltac:(cbv; lia)), E2 in C2. fold sp0 in C2. rewrite (HEn6 32%nat ltac:(cbv; lia)), EaT in C11, C12. unfold w64 in C11, C12.
rewrite unsigned_lit_small in C11, C12 by (clear - LB; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; lia).
assert (DPRE : drain_pre_cf B ARX L24 QB inst ly X' W5 (ms_regs msC) (ms_mem msC) (with_vm_backing (m_vm_lazy md') matC md')).
{ unfold drain_pre_cf, spZ, raZ. change YFeuC.DSTACK with DSTACK. rewrite C1, C2, C3, C4, C11, C12. rewrite !unsigned_lit_small by (clear - Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, DFSTACK in *; unfold sp0 in *; lia).
split; [exact ARC|]. split; [exact DRX'|]. split; [exact QLX'|]. split; [exact L24X'|].
split; [apply YK0s.ret_ok_even; reflexivity|]. split; [clear; lia|].
split; [clear - Hal; unfold sp0 in *; Z.div_mod_to_equations; lia|].
split; [clear - Hlo; unfold DSTACK, spZ, DFSTACK in *; unfold sp0 in *; lia|].
split; [clear - Hhi; unfold spZ in *; unfold sp0 in *; lia|].
split; [intros a Ha; apply PRESC; clear - Ha; unfold DSTACK, DFSTACK in *; lia|].
split; [rewrite (HEn6 3%nat ltac:(cbv; lia)), E3; exact Hgp|].
split; [rewrite (ts_tp _ TS); reflexivity|].
split; [|split; reflexivity].
rewrite C10, (HEn6 11%nat ltac:(cbv; lia)), (DGgm.E11 ly regs0 tr pa nn hb1 q j1 j2 j3). unfold regs0. rewrite dregs_11.
pose proof (DIfaceRh.dih_inst _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md HARX0) as (I1 & I2 & _). unfold w64. rewrite unsigned_lit_small by lia. unfold o_quar. f_equal; lia. }
eapply YG0dHc.amreal'_then_SRr.
{ exact (YG0dHc.amreal'_apath_gflag tfibsegs YGcfRehidePost.RZ_cf _ _ _ _ (DRNg inst ly X' W5 (ms_regs msC) (ms_mem msC) (with_vm_backing (m_vm_lazy md') matC md') DPRE)). }
intros [[] X''] W6 c6 [(regs6 & mem6 & md6 & -> & POST6 & POST6x) (trc & HPATH6 & HG6)].
pose proof (XRdr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ POST6x) as POST6r. cbn [fst snd] in POST6, POST6r, POST6x |- *.
pose proof POST6 as (HA6 & LLE6 & WLE6 & CS6 & SIO6 & FR6 & PRS6).
assert (DSUB : forall a, YGcfRehidePost.dead_shadow_new ly X' X'' a -> YGcfRehidePost.dead_shadow_new ly S X'' a).
{ intros a Hd. apply (YGcfRehidePost.dead_shadow_new_mono_l ly X' S X'' a); [|exact Hd].
  intros r sm0 H1 H2. rewrite HSX in H1. exact (qx_secs_live_d S k z tr r sm0 H1 H2). }
change YFeuC.DSTACK with DSTACK in FR6, PRS6. change (@ImgBase.im_segs AImg_reply) with tfibsegs in FR6, PRS6.
assert (HLP : lpost X'').
{ exact (DIfaceRh.dih_lpost_d _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md p n tr k z nb X' W5 mem' md' trc (tt, X'') HARX0 HRP HBLK HTU HK HKS
  ltac:(rewrite HQ'; reflexivity) ltac:(exact Hnb) HCK' HQG' HA5 DRX' HPATH6 HG6). }
unfold ascratch, spZ, raZ in FR6, PRS6 |- *. rewrite C2 in FR6, PRS6. rewrite C1.
rewrite !unsigned_lit_small in FR6, PRS6 |- * by (clear - Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, DFSTACK in *; unfold sp0 in *; lia).
assert (NOWN6 : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> ~ AOX ly X' a /\ ~ AOX ly X'' a).
{ intros a Ha. split.
- exact (proj2 (NOWN a Ha)).
- exact (DIfaceRh.dih_stack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly X'' W6 mem6 md6 a HA6 Ha). }
assert (AGS6 : forall a, sp0 - 80 <= a < ly_stk_hi ly -> aview tfibsegs (w_H W6) mem6 a = aview tfibsegs (w_H W5) (ms_mem msC) a).
{ intros a Ha. destruct (NOWN6 a ltac:(clear - Ha Hlo; unfold DFSTACK in *; lia)) as [N1 N2]. apply FR6; [clear - Ha Usp Hlo Hhi LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, kHighMemEnd, DFSTACK in *; unfold sp0 in *; lia | exact N1 | exact N2 | | intros []
  | apply YGcfRehidePost.dead_shadow_new_high; clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, DFSTACK in *; unfold sp0 in *; lia].
rewrite (ts_errno _ TS). unfold TFIB_ERRNO, DSTACK. clear - Ha Hlo LB. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, DFSTACK in *. unfold sp0 in *. lia. }
assert (BV2' : bv_unsigned (ew En6 2) = sp0) by (rewrite (HEn6 2%nat ltac:(cbv; lia)), E2; reflexivity).
assert (BV13' : bv_unsigned (ew En6 13) = SOv) by (rewrite (HEn6 13%nat ltac:(cbv; lia)), (DGgm.E13 ly regs0 tr pa nn hb1 q j1 j2 j3); reflexivity).
assert (HP6 : regs_preserved (ms_regs msC) regs6) by (intros r Hr'; apply CS6; exact Hr').
lazymatch type of HS with st_ok _ _ ?ss ?ms0 =>
let m := eval vm_compute in (ss_mem ss) in
lazymatch m with ?r0 :: ?r1 :: ?r2 :: ?r3 :: ?r4 :: ?r5 :: ?rest =>
pose proof (st_ok_after_call tfibsegs 128 En6 ss ms0 regs6 (mrestrict (w_H W6) mem6) (r1 :: r2 :: r3 :: r4 :: r5 :: nil) 0x36018 HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(apply submem_drop; apply submem_keep; [apply subregion_refl|]; apply submem_keep; [apply subregion_refl|]; apply submem_keep; [apply subregion_refl|];
apply submem_keep; [apply subregion_refl|]; apply submem_keep; [apply subregion_refl|]; apply submem_nil)
ltac:(vm_compute; reflexivity) HP6) as HS1;
let rsv := eval vm_compute in (r1 :: r2 :: r3 :: r4 :: r5 :: nil) in
change (r1 :: r2 :: r3 :: r4 :: r5 :: nil) with rsv in HS1;
let ss2 := eval vm_compute in (ss_after_call ss rsv 128 0x36018) in
change (ss_after_call ss rsv 128 0x36018) with ss2 in HS1
end
end.
cbn [ms_mem restrict] in HS1.
lazymatch type of HS1 with Forall _ ?L -> _ =>
assert (KEPT : Forall (region_kept tfibsegs En6 (mrestrict (w_H W5) (ms_mem msC)) (mrestrict (w_H W6) mem6)) L);
[ repeat apply Forall_cons; try apply Forall_nil;
(apply kept_of_aview2; cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; rewrite ?BV2', ?BV13';
[ intros a Ha; apply AGS6; clear - Ha HSOF; lia
| intros a Ha; split; [apply AGS6; clear - Ha HSOF; lia | clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, DFSTACK, TFIB_IMG_END in *; unfold sp0 in *; lia] ])
| specialize (HS1 KEPT); clear KEPT ]
end.
set (En7 := havoc En6 128 (map (getr regs6) CLOB)) in HS1.
assert (HEn7 : forall k0, (k0 < aHAVf)%nat -> ew En7 k0 = ew E0 k0) by (intros k0 Hk0; subst En7; unfold aHAVf in Hk0; rewrite ew_havoc_old by lia; apply HEn6; exact Hk0).
rewrite <- (restrict_mkst_fx (w_H W6)) in HS1. clear HS. rename HS1 into HS.
unfold cfg_at. rewrite <- (wvb_self md6) at 1.
srr_run_sh tfibtbl_rtF_ok HS.
lazymatch type of HS with st_ok _ ?E _ (restrict _ ?msx) => set (En8 := E) in HS; rename msx into msR end.
assert (HEn8 : forall k0, (k0 < aHAVf)%nat -> ew En8 k0 = ew E0 k0) by (intros k0 Hk0; subst En8; unfold aHAVf in Hk0; rewrite ?ew_havoc_old by lia; apply HEn7; exact Hk0).
assert (FRT : forall x : word, ~ (sp0 - 80 <= bv_unsigned x < sp0) -> ms_mem msR x = mem6 x).
{ intros x Hx1. apply HF. intros Hw. destruct (in_wrange_windows _ _ _ Hw) as (b & lo & hi & Hin & Hrg).
lazymatch type of Hin with In _ (windows ?rs) => let ws := eval vm_compute in (windows rs) in change (windows rs) with ws in Hin end.
cbn [In] in Hin.
repeat (destruct Hin as [Hin|Hin];
[ injection Hin as <- <- <-; cbn [fst snd base_val] in Hrg; rewrite ?(HEn7 2%nat ltac:(cbv; lia)), ?E2, ?(HEn7 32%nat ltac:(cbv; lia)), ?EaT in Hrg; unfold w64 in Hrg;
rewrite ?unsigned_lit_small in Hrg by (clear - LB; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; lia); clear - Hx1 Hrg; unfold DFSTACK, t_qc in *; unfold sp0 in *; lia |]).
destruct Hin. }
clear HF HFr.
assert (PRES6 : forall a, sp0 - DFSTACK <= a < sp0 - 80 -> apresent (w_H W6) mem6 a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 80 - DSTACK)) as [L2|L2].
2:{ apply PRS6. clear - Ha L2. lia. }
assert (EQa : aview tfibsegs (w_H W6) mem6 a = aview tfibsegs (w_H W5) (ms_mem msC) a).
{ destruct (NOWN6 a ltac:(clear - Ha Hlo Hhi; unfold DFSTACK in *; lia)) as [M1 M2]; apply FR6; [clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, DFSTACK in *; unfold sp0 in *; lia | exact M1 | exact M2 | | intros []
  | apply YGcfRehidePost.dead_shadow_new_high; clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, DFSTACK in *; unfold sp0 in *; lia].
rewrite (ts_errno _ TS); unfold TFIB_ERRNO; clear - Ha L2 Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, DFSTACK, DSTACK in *; unfold sp0 in *; lia. }
pose proof (PRESC a ltac:(clear - Ha; lia)) as P; apply apresent_mbyte in P as [b Hb].
assert (A : aview tfibsegs (w_H W5) (ms_mem msC) a = Some (bv_unsigned b)) by (unfold aview; rewrite Hb; reflexivity).
rewrite <- EQa in A; apply aview_some in A as (b' & Hb' & _).
exact (mbyte_high_apresent (w_H W6) mem6 a b' ltac:(clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, DFSTACK, TFIB_IMG_END in *; unfold sp0 in *; lia) Hb'). }
assert (PRESR : forall a, sp0 - DFSTACK <= a < sp0 -> apresent (w_H W6) (ms_mem msR) a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 80)) as [L1|L1]; [|destruct (Z_lt_le_dec a (sp0 - 48)) as [L2|L2]].
- apply (apresent_same (w_H W6) mem6); [apply FRT; rewrite unsigned_lit_small by (clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, DFSTACK in *; unfold sp0 in *; lia); clear - L1; lia | apply PRES6; clear - Ha L1; lia].
- eapply (st_ok_window_apresent (w_H W6) En8 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn8 2%nat ltac:(cbv; lia)), E2; clear - L1 L2; unfold sp0; lia | clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, DFSTACK, TFIB_IMG_END in *; unfold sp0 in *; lia].
- eapply (st_ok_window_apresent (w_H W6) En8 _ _ 2 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn8 2%nat ltac:(cbv; lia)), E2; clear - L2 Ha; unfold sp0; lia | clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, DFSTACK, TFIB_IMG_END in *; unfold sp0 in *; lia]. }
eapply (SRr_ret_at tfibsegs tfibtbl_rtF tfibtbl_rtF_ok Hwx W6 En8); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'.
rreg HS (1%bv : bv 5) Q1f. rewrite (HEn8 1%nat ltac:(cbv; lia)), E1 in Q1f.
srr_norm_model.
exists ly, (ms_regs msR), (ms_mem msR), (with_vm_backing (m_vm_lazy md6) mat' md6). split.
{ unfold cfg_at, raZ, w64. rewrite Q1f, Z_to_bv_bv_unsigned. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split; [|split; [|split; [exact HLP | do 6 eexists; split; [exact FR1 | split; [exact POST6x | exact FRT]]]]].
(* the raw frame (rawb = true): Put's tail, the drain's raw post, Put's run to Drain, the enqueue's raw post, the
   walk's agreement at the Enqueue call *)
2:{ intros Hrb x NO NO'' NS NE.
pose proof (FRrb Hrb) as FRr. unfold acall_raw_x, ascratch in FRr. rewrite SPE in FRr.
pose proof (POST6r Hrb) as FR6r. unfold acall_raw_x in FR6r. change YFeuC.DSTACK with DSTACK in FR6r.
unfold ascratch, spZ in FR6r. rewrite C2 in FR6r.
rewrite !unsigned_lit_small in FR6r by (clear - Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, DFSTACK in *; unfold sp0 in *; lia).
pose proof (u64_range x) as Ha. set (a := bv_unsigned x) in *.
assert (NOX : ~ AOX ly X a).
{ intros OX. destruct (DIfaceRh.dih_owned_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md p n k z tr a HARX0 HRP HBLK HK OX) as [O|O]; [exact (NO O)|].
apply NE. split; [exact PNN | exact O]. }
assert (NOX' : ~ AOX ly X' a) by (intros O; apply NOX; exact (HOWN' a O)).
assert (NS1 : ~ (sp0 - 80 <= a < sp0)) by (intros Hs; apply NS; unfold ascratch; left; clear - Hs; unfold spZ, DFSTACK_G; unfold sp0 in *; lia).
rewrite (FRT x NS1).
rewrite FR6r; [| exact NOX' | exact NO'' | | intros []].
2:{ intros [Hs|Hs]; apply NS; unfold ascratch; [left; clear - Hs; unfold spZ, DSTACK, DFSTACK_G in *; unfold sp0 in *; lia | right; first [exact Hs | rewrite (ts_errno _ TS); exact Hs | rewrite (ts_errno _ TS) in Hs; exact Hs] ]. }
rewrite (FR1 x NS1).
rewrite FRr; [| exact NOX | exact NOX' | | intros []].
2:{ intros [Hs|Hs]; apply NS; unfold ascratch; [left; clear - Hs; unfold spZ, QSTACK, DFSTACK_G in *; unfold sp0 in *; lia | right; first [exact Hs | rewrite (ts_errno _ TS); exact Hs | rewrite (ts_errno _ TS) in Hs; exact Hs] ]. }
apply AGPr; [exact NO | exact NS |]. intros Hb. apply NE. exact (conj PNN Hb). }
assert (AGT : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 80 <= a < sp0) -> aview tfibsegs (w_H W6) (ms_mem msR) a = aview tfibsegs (w_H W6) mem6 a).
{ intros a Ha N1. apply aview_same. apply FRT; rewrite unsigned_lit_small by exact Ha; assumption. }
split; [|split; [apply layout_le_refl | split; [exact (wle_wle_in_d tfibsegs _ _ _ _ WLE (YA0nH.wle_in_mono tfibsegs _ _ _ _ DSUB WLE6)) | split; [|split; [|split]]]]].
-
apply (DIfaceRh.dih_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly X'' W6 mem6 md6 (ms_mem msR) _ HA6).
+ intros a Ha HO. apply AGT; [exact Ha|]. intros Hs. apply (DIfaceRh.dih_stack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly X'' W6 mem6 md6 a HA6); [|exact HO]. clear - Hs Hlo Hhi; unfold spZ, DFSTACK in *; unfold sp0 in *; lia.
+ intros a Hv HN. change (@ImgBase.im_segs AImg_reply) with tfibsegs in Hv, HN. unfold aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
destruct (w_H W6 x) eqn:Hx; [exact (Hv HN)|]. destruct (seg_rom tfibsegs x) eqn:ROM; [destruct (ms_mem msR x); discriminate|].
destruct (ms_mem msR x) as [|] eqn:E'; [discriminate|]. clear HN. destruct (mem6 x) as [b0|] eqn:EE0; [clear Hv | exact (Hv eq_refl)].
set (a' := bv_unsigned x). assert (Ha' : 0 <= a' < 2 ^ 64) by (subst a'; apply u64_range). assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
destruct (WDEC a') as [C|C].
* destruct (PRESR a' ltac:(clear - C; unfold DFSTACK; lia)) as [_ [bb Hb]]. rewrite Ex in Hb. congruence.
* rewrite (FRT x C) in E'. congruence.
+ reflexivity. + reflexivity. + reflexivity.
+
intros a Ha Hx. change (@ImgBase.im_segs AImg_reply) with tfibsegs in Hx. unfold w64 in *. apply FRT; rewrite unsigned_lit_small by (clear - Ha; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; lia).
intros C; (destruct (PRESR a ltac:(clear - C; unfold DFSTACK; lia)) as [Hh _]); unfold w64 in Hh; rewrite Hx in Hh; discriminate.
-
intros r Hr'. assert (HrZ : bv_unsigned (Z_to_bv 5 r) = r).
{ rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 5) with 32. unfold acallee_saved in Hr'. apply Z.mod_small. lia. }
rewrite <- (dregs_other regs pa inst bp so (Z_to_bv 5 r)) by (rewrite HrZ; unfold acallee_saved in Hr'; lia). fold regs0.
unfold acallee_saved in Hr'.
assert (R : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
clear Hr' HrZ. pose proof Htp0 as Htp.
repeat match type of R with _ \/ _ => destruct R as [R|R] end; subst r;
[ cs_case HS HEn8 Htp (2%bv : bv 5) | cs_case HS HEn8 Htp (3%bv : bv 5) | cs_case HS HEn8 Htp (4%bv : bv 5) | cs_case HS HEn8 Htp (8%bv : bv 5) | cs_case HS HEn8 Htp (9%bv : bv 5)
| cs_case HS HEn8 Htp (18%bv : bv 5) | cs_case HS HEn8 Htp (19%bv : bv 5) | cs_case HS HEn8 Htp (20%bv : bv 5) | cs_case HS HEn8 Htp (21%bv : bv 5) | cs_case HS HEn8 Htp (22%bv : bv 5)
| cs_case HS HEn8 Htp (23%bv : bv 5) | cs_case HS HEn8 Htp (24%bv : bv 5) | cs_case HS HEn8 Htp (25%bv : bv 5) | cs_case HS HEn8 Htp (26%bv : bv 5) | cs_case HS HEn8 Htp (27%bv : bv 5) ].
-
clear - SIO SIO6. unfold same_io in SIO, SIO6 |- *. subst mdE.
destruct md, md', md6. cbn in SIO, SIO6 |- *.
intuition congruence.
-
intros a Ha NO NO'' NS NE ND.
assert (NOX : ~ AOX ly X a).
{ intros OX. destruct (DIfaceRh.dih_owned_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md p n k z tr a HARX0 HRP HBLK HK OX) as [O|O]; [exact (NO O)|].
apply NE. split; [exact PNN | exact O]. }
assert (NOX' : ~ AOX ly X' a) by (intros O; apply NOX; exact (HOWN' a O)).
assert (NS1 : ~ (sp0 - 80 <= a < sp0)) by (intros Hs; apply NS; unfold ascratch; left; clear - Hs; unfold spZ, DFSTACK_G; unfold sp0 in *; lia).
rewrite (AGT a Ha NS1).
rewrite FR6; [| exact Ha | exact NOX' | exact NO'' | | intros [] | intros Hd; exact (ND (DSUB a Hd))].
2:{ intros [Hs|Hs]; apply NS; unfold ascratch; [left; clear - Hs; unfold spZ, DSTACK, DFSTACK_G in *; unfold sp0 in *; lia | right; first [exact Hs | rewrite (ts_errno _ TS); exact Hs | rewrite (ts_errno _ TS) in Hs; exact Hs] ]. }
rewrite (AGC a Ha NS1).
rewrite FR; [| exact Ha | exact NOX | exact NOX' | | intros []].
2:{ intros [Hs|Hs]; apply NS; unfold ascratch; [left; clear - Hs; unfold spZ, QSTACK, DFSTACK_G in *; unfold sp0 in *; lia | right; first [exact Hs | rewrite (ts_errno _ TS); exact Hs | rewrite (ts_errno _ TS) in Hs; exact Hs] ]. }
apply AGP; [exact Ha | exact NO | exact NS |]. intros Hb. apply NE. exact (conj PNN Hb).
-
intros a Ha. apply PRESR. unfold spZ, DFSTACK_G in Ha. exact Ha.
Qed.
End g.

(* DGfz.mid_walk_x at amreal' over RZ_cf: to_enq_rh, then the released Enqueue contract [ENQg] lifted
   (YG0dH.amreal_amreal'), continued at amreal'. *)
Lemma mid_walk_x_rh : forall (XRq : fxrel), enq_spec_g B U ARX AOX rpre lpost fpre dpost L24 QB MP XRq -> xr_raw XRq ->
  forall k hb1 j1 j2 j3,
  find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
  0 <= hb1 < 256 -> val_mem tfibsegs (mrestrict (w_H W) mem) (sptr_addr B ly p - 16) 4 (2 + 256 * hb1) ->
  DGgm.free_hyps W ly regs0 mem tr pa nn hb1 q j1 j2 j3 regs ->
  forall (Q : unit * astate -> world tfibsegs -> config -> Prop),
  (forall z msE matE E5 W5 regs' mem' md' X' nb, enq_ret k hb1 j1 j2 j3 z msE matE E5 W5 regs' mem' md' X' nb ->
     XRq inst YFewC.QSTACK ly (qx S k z tr) W (ms_regs msE) (ms_mem msE) (with_vm_backing (m_vm_lazy md) matE md)
       (fun _ => False) ly X' W5 regs' mem' md' ->
     (forall x : word, ~ dwin_m ly sp0 pa (bv_unsigned x) -> ~ dg_dzone ly (bv_unsigned x) -> ~ dg_izone (bv_unsigned x) ->
        ~ dshadow pa nn (bv_unsigned x) -> ms_mem msE x = mem x) ->
     st_secs X' = st_secs (qx S k z tr) ->
     YG0dH.amreal' tfibsegs YGcfRehidePost.RZ_cf (dmd dbody X') W5 (cfg_at tfibsegs 0x360e0 regs' mem' md') Q) ->
  YG0dH.amreal' tfibsegs YGcfRehidePost.RZ_cf (ft p tr S) W (cfg_at tfibsegs 0x3191c regs mem md) Q.
Proof.
intros XRq ENQg XRqr k hb1 j1 j2 j3 HK HKS Hhb1 Hhdr FH Q CONT.
pose proof PRE as P. unfold DeallocG.dealloc_pre in P.
destruct P as (HARX & HRP & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & Hpres & Hgp & Htp & Hr10 & Hr11 & Hr12 & Hr13 & Hr14 & Hr15 &
  Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htrlen & PSO & PLEN & PBUF & Htr & Hp0 & HFP).
pose proof (DGgm.derived_ranges _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as DR.
pose proof (DGgm.LYB _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as LB.
assert (RG3 : getr (dregs regs (sptr_addr B ly p) inst bp so) 3 = getr regs 3) by (apply dregs_other; vm_compute; discriminate).
assert (Upa : 0 <= sptr_addr B ly p < 2 ^ 64) by (change (sptr_addr B ly p) with pa; clear - DR; ceil; unfold ASAN_CEIL in *; lia).
apply (to_enq_rh inst so bp ly S W regs mem md p n tr k hb1 j1 j2 j3 Q PRE HBLK HK HKS Hhb1 Hhdr FH).
intros z msE mat E5 AOK HshE HEn5 HS5 DM.
pose proof DM as DM0. destruct DM as (_ & DMfr & _ & _ & DMps & _).
(* MP at Put's call: MP_keep over dmem_m's frame, from MP at Deallocate's entry (HMP) *)
assert (HMPE : MP (ms_mem msE)).
{ assert (RG2 : getr regs0 2 = getr regs 2) by (unfold regs0; apply dregs_other; vm_compute; discriminate).
  apply (MP_keep W ly regs0 mem tr pa nn hb1 q j1 j2 j3 regs (ms_mem msE) FH); [|exact HMP].
  intros x N1 N2 N3 N4. rewrite RG2 in N1. exact (DMfr x N1 N2 N3 N4). }
(* the registers at Enqueue's call *)
rreg HS5 (1%bv : bv 5) E1r. rreg HS5 (2%bv : bv 5) E2r. rreg HS5 (3%bv : bv 5) E3r. rreg HS5 (4%bv : bv 5) E4r.
rreg HS5 (10%bv : bv 5) E10r. rreg HS5 (11%bv : bv 5) E11r. rreg HS5 (13%bv : bv 5) E13r. rreg HS5 (14%bv : bv 5) E14r.
assert (BV2 : bv_unsigned (ew E5 2) = bv_unsigned (getr regs 2)).
{ rewrite (HEn5 2%nat ltac:(cbv; lia)), (DGgm.E2 ly (dregs regs (sptr_addr B ly p) inst bp so) tr
    (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3).
  rewrite dregs_other by (vm_compute; discriminate). reflexivity. }
assert (BV32 : bv_unsigned (ew E5 32) = ly_T ly).
{ rewrite (HEn5 32%nat ltac:(cbv; lia)). unfold w64. apply unsigned_lit_small.
  destruct LB as ((T1 & T2 & _) & _). clear - T1 T2. ceil. unfold ASAN_CEIL, kThreadObjSize in *. lia. }
assert (BV10 : bv_unsigned (ew E5 10) = sptr_addr B ly p).
{ rewrite (HEn5 10%nat ltac:(cbv; lia)), (DGgm.E10 ly (dregs regs (sptr_addr B ly p) inst bp so) tr
    (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3), dregs_10. unfold w64.
  apply unsigned_lit_small. exact Upa. }
assert (SPE : spZ (ms_regs msE) = bv_unsigned (getr regs 2) - 80).
{ unfold spZ. rewrite E2r, BV2. apply unsigned_lit_small.
  pose proof (u64_range (getr regs 2)) as U2. unfold spZ, DFSTACK_G in Hlo.
  destruct LB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L5).
  clear - Hlo U2 L5. unfold kHighMemBeg in *. lia. }
rewrite HshE at 1.
change (mkCfg (mkst (ms_regs msE) (w64 0x360ec) (ms_mem msE) (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md))
  with (cfg_at tfibsegs A_Enqueue (ms_regs msE) (ms_mem msE) (with_vm_backing (m_vm_lazy md) mat md)).
eapply YG0dH.amreal'_mbind.
{ (* Enqueue keeps st_secs (YGcfSecsStep.ss_enqueue); TAILD_x_rh's dead-set step reads it *)
  eapply (YG0dHc.amreal'_apostg tfibsegs YGcfRehidePost.RZ_cf _ (fun r => st_secs (snd r) = st_secs (qx S k z tr)));
    [intros trc r Hp _; exact (YGcfAmx.ipost_apath_amx _ _ trc r (YGcfSecsStep.ss_enqueue (qk k) (qx S k z tr)) Hp)|].
  apply YG0dH.amreal_amreal'. apply (ENQg inst ly S W mem md p n tr k z hb1 (bv_unsigned (getr regs 2))
    (ms_regs msE) (ms_mem msE) mat HARX HRP HFP HBLK Htr HK HKS
    ltac:(unfold DFSTACK, DGbaseC.DFSTACK, DFSTACK_G, spZ in *; clear - Hlo; lia)
    ltac:(unfold spZ in *; clear - Hhi; lia)
    ltac:(unfold spZ in *; clear - Hbot; lia)
    ltac:(unfold spZ in *; clear - Hal; lia)
    Hhb1 Hhdr DM0 HMPE).
  - rewrite E1r. apply YK0s.ret_ok_even. reflexivity.
  - unfold raZ. rewrite E1r. rewrite unsigned_lit_small by lia. lia.
  - exact SPE.
  - rewrite E3r, (HEn5 3%nat ltac:(cbv; lia)),
      (DGgm.Er ly (dregs regs (sptr_addr B ly p) inst bp so) tr (sptr_addr B ly p) (req_size n) hb1
         (st_qthread S) j1 j2 j3 3 3%bv eq_refl), RG3. exact Hgp.
  - rewrite E4r, (ts_tp B TS). reflexivity.
  - rewrite E10r, BV32. unfold w64, t_qc. f_equal; lia.
  - rewrite E11r, BV32. unfold w64, t_cache. f_equal; lia.
  - rewrite E13r, BV10. unfold w64, kChunkHeaderSize. f_equal; lia.
  - rewrite E14r, (HEn5 39%nat ltac:(cbv; lia)),
      (DGgm.EaN ly (dregs regs (sptr_addr B ly p) inst bp so) tr (sptr_addr B ly p) (req_size n) hb1
         (st_qthread S) j1 j2 j3). reflexivity. }
intros a s' W' c' [HSX HPOST']. cbn [snd] in HSX.
destruct HPOST' as (regsE' & memE' & mdE' & nb & -> & POST & POSTr & HQ' & Hnb & HCK' & HQG' & HAOX & HQCELL & HLPs & HDRN).
cbn [fst snd] in POST, POSTr, HQ', HCK', HQG', HAOX, HQCELL, HLPs, HDRN.
assert (RA : raZ (ms_regs msE) = 221408) by (unfold raZ; rewrite E1r; apply unsigned_lit_small; lia).
rewrite RA.
apply (CONT z msE mat E5 W' regsE' memE' mdE' s' nb); [| exact POSTr | exact DMfr | exact HSX].
unfold enq_ret. cbv zeta.
split; [exact HshE|]. split; [exact HEn5|]. split; [exact HS5|]. split; [exact DMps|].
split; [exact POST|]. split; [exact (XRqr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ POSTr)|]. split; [exact HQ'|]. split; [exact Hnb|]. split; [exact HCK'|]. split; [exact HQG'|].
split; [exact HAOX|]. split; [exact HDRN|]. split; [exact HQCELL|].
(* the walk's raw agreement with the entry memory at the call (dmem_m's frame, the owned set) *)
intros x NO NS NE. assert (Ra : 0 <= bv_unsigned x < 2 ^ 64) by apply u64_range.
apply DMfr.
- intros [Hs|[Hw|Hw]].
  + apply NS. left. unfold spZ, DFSTACK_G, DFSTACK, DGbaseC.DFSTACK in *. lia.
  + destruct (DIfaceRh.dih_owned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md p n k _ HARX HRP HBLK HK Ra
      ltac:(left; unfold DGgm.WINT, DGgmC.WINT in Hw; unfold DGgi.WINT, DGgiC.WINT; tauto)) as [O|O]; [exact (NO O) | exact (NE O)].
  + unfold DGgm.WINB, DGgmC.WINB in Hw. destruct Hw as [Hw|Hw].
    * destruct (DIfaceRh.dih_owned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md p n k _ HARX HRP HBLK HK Ra
        ltac:(right; left; exact Hw)) as [O|O]; [exact (NO O) | exact (NE O)].
    * destruct (DIfaceRh.dih_owned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md p n k _ HARX HRP HBLK HK Ra
        ltac:(right; right; left; exact Hw)) as [O|O]; [exact (NO O) | exact (NE O)].
- intros Hd. destruct (DIfaceRh.dih_owned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md p n k _ HARX HRP HBLK HK Ra
    ltac:(right; right; right; left; exact Hd)) as [O|O]; [exact (NO O) | exact (NE O)].
- intros Hi. exact (NO (DIfaceRh.dih_owned_i _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md _ HARX Hi)).
- intros Hs. destruct (DIfaceRh.dih_owned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md p n k _ HARX HRP HBLK HK Ra
    ltac:(right; right; right; right; exact Hs)) as [O|O]; [exact (NO O) | exact (NE O)].
Qed.
End f.

(* The drain arm's other premises: the released Enqueue contract at the keep (MnEnq.de_enqueue_m_t, MemnormDmid's
   ENQm), the drain under the re-hide (DIfaceRh.de_drain_m_rh_t), and ErrnoApart's image facts (MemnormDmid's EA rows). *)
Hypothesis ENQm : MnEnq.de_enqueue_m_t B U ARX AOX rpre lpost fpre dpost L24 QB MP.
Hypothesis DRNrh : DIfaceRh.de_drain_m_rh_t B ARX AOX dbody L24 QB.
Hypothesis EAimg : ErrnoApart.errno_in_img.
Hypothesis EAz3 : ErrnoApart.errno_apart_zone3_d.
Hypothesis EAdz : ErrnoApart.errno_apart_dzone_d.
Hypothesis EAiz : ErrnoApart.errno_apart_izone.

(* MemnormDmid.dealloc_drn_em under the re-hide: mid_walk_x_rh and TAILD_x_rh at MnEnq.acall_raw_em_x, the drain at
   DIfaceRh.de_drain_m_rh_t [DRNrh]; the leaf is YGcfMallocComposeERhBase.dealloc_leaf_raw_em_rh (WalkSigDrh's LEAFrh). *)
Theorem dealloc_drn_em_rh : forall inst so bp ly S W regs mem md p n tr,
DeallocG.dealloc_pre tfibsegs B U ARX rpre fpre 1 inst so bp ly S W regs mem md p n tr -> MP mem ->
In (p, n) (blocks S) ->
kQuarantineCacheMax < qc_bytes (st_qthread S) + req_size n + (if need_new_batch (st_qthread S) then kBatchBytes else 0) ->
YG0dH.amreal' tfibsegs YGcfRehidePost.RZ_cf (ft p tr S) W (cfg_at tfibsegs 0x3191c regs mem md)
(YGcfMallocComposeERhBase.dealloc_leaf_raw_em_rh tfibsegs B ft ARX AOX lpost inst ly S W regs mem md p n tr).
Proof.
intros inst so bp ly S W regs mem md p n tr PRE HMP HBLK DRAIN.
pose proof PRE as PRE0.
destruct PRE0 as (HARX & HRP & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & Hpres & Hgp & Htp & Hr10 & Hr11 & Hr12 & Hr13 & Hr14 & Hr15 &
Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htrlen & PSO & PLEN & PBUF & Htr & Hp0 & HFP).
(* copy of DGfz.v:724-728 *)
pose proof (DIfaceRh.dih_view _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md p n HARX HRP HFP HBLK) as DV.
destruct (dv_chunk _ _ _ _ _ _ _ _ DV) as (k & HK & HKS & _ & HKR).
pose proof (dv_nonnull _ _ _ _ _ _ _ _ DV) as PNN.
pose proof (DIfaceRh.dih_inst _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md HARX) as HIO.
destruct (DGg1.FH_m B TS U ARX rpre fpre inst so bp ly S W regs mem md p n tr PRE HBLK HIO DV) as (hb1 & j1 & j2 & j3 & Hhb1 & Hhdr & FH).
(* copy of DGfz.v:730-746 (errno's bytes apart from Put's frame and dmem_m's windows), with sp0 / pa / nn unfolded *)
pose proof (dv_n _ _ _ _ _ _ _ _ DV) as DN.
pose proof (dn_ly _ _ _ _ _ DN) as LY. pose proof (dn_img _ _ _ _ _ DN) as IMG.
destruct (dv_zone _ _ _ _ _ _ _ _ DV) as (Z3 & _ & _ & NN).
pose proof (DGgm.derived_ranges _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as (P0 & _).
assert (HSP : ly_stk_lo ly + DGbaseC.DFSTACK <= bv_unsigned (getr regs 2))
  by (unfold DGbaseC.DFSTACK, DFSTACK_G, spZ in *; lia).
assert (ER0 : 0 <= as_errno B /\ as_errno B + 4 <= 2 ^ 64).
{ destruct (EAimg B ly TS IMG) as [E1 _]. pose proof (ErrnoApart.errno_below_imgend EAimg B ly TS LY IMG) as E2.
  pose proof (lo_img ly LY) as (L1 & _). clear - E1 E2 L1. unfold kImgLo, kImgEnd in *. lia. }
assert (EW : forall x : word, as_errno B <= bv_unsigned x < as_errno B + 4 ->
  ~ (bv_unsigned (getr regs 2) - 80 <= bv_unsigned x < bv_unsigned (getr regs 2)) /\
  ~ dwin_m ly (bv_unsigned (getr regs 2)) (sptr_addr B ly p) (bv_unsigned x) /\ ~ dg_dzone ly (bv_unsigned x) /\
  ~ dg_izone (bv_unsigned x) /\ ~ dshadow (sptr_addr B ly p) (req_size n) (bv_unsigned x)).
{ intros x Hx. set (a := bv_unsigned x) in *.
  split; [intros Hs; exact (ErrnoApart.errno_apart_stack EAimg B ly (bv_unsigned (getr regs 2) - 80) (bv_unsigned (getr regs 2)) a TS LY IMG
    ltac:(clear - HSP; unfold DGbaseC.DFSTACK in *; lia) Hs Hx)|].
  split; [intros Hw; exact (ErrnoApart.errno_apart_dwin_m EAimg EAz3 B ly (bv_unsigned (getr regs 2)) (sptr_addr B ly p) (req_size n) a TS LY IMG HSP Z3 (proj1 NN) Hw Hx)|].
  split; [intros Hd; exact (EAdz B ly a TS LY IMG Hd Hx)|].
  split; [intros Hi; exact (EAiz B a TS Hi Hx)|].
  intros Hs. exact (ErrnoApart.errno_apart_dshadow EAimg B ly (sptr_addr B ly p) (req_size n) a TS LY IMG ltac:(clear - P0; lia) Hs Hx). }
assert (EB : forall i, 0 <= i < 4 -> bv_unsigned (w64 (as_errno B + i)) = as_errno B + i)
  by (intros i Hi; unfold w64; apply unsigned_lit_small; lia).
assert (RG2 : getr (dregs regs (sptr_addr B ly p) inst bp so) 2 = getr regs 2) by (apply dregs_other; vm_compute; discriminate).
assert (MAIN : YG0dH.amreal' tfibsegs YGcfRehidePost.RZ_cf (ft p tr S) W (cfg_at tfibsegs 0x3191c regs mem md)
  (fun r W' c' => exists ly' regs' mem' md',
    c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
    YGcfRehidePost.dealloc_post_rh tfibsegs B ARX AOX inst ly S W regs mem md
      (fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n) ly' (snd r) W' regs' mem' md' /\
    (true = true -> forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ AOX ly' (snd r) (bv_unsigned x) ->
      ~ ascratch B DFSTACK_G regs (bv_unsigned x) ->
      ~ (p <> PNull /\ sptr_addr B ly p <= bv_unsigned x < sptr_addr B ly p + req_size n) -> mem' x = mem x) /\
    ErrnoG.errno_kept B mem mem' /\ MemnormT.memnorm_keep tfibsegs mem mem' /\ lpost (snd r))).
{ apply (mid_walk_x_rh inst so bp ly S W regs mem md p n tr PRE HMP HBLK (MnEnq.acall_raw_em_x B AOX) ENQm
    (MemnormDmid.xr_raw_em B AOX) k hb1 j1 j2 j3 HK HKS Hhb1 Hhdr FH).
  intros z msE matE E5 W5 regs' mem' md' X' nb ER XE DMfr HSX.
  eapply YG0dH.amreal'_mono; [| exact (TAILD_x_rh inst so bp ly S W regs mem md p n tr PRE HBLK DRAIN k hb1 j1 j2 j3 HK HKS HKR PNN FH
    (MnEnq.acall_raw_em_x B AOX) DRNrh (MemnormDmid.xr_raw_em B AOX) z msE matE E5 W5 regs' mem' md' X' nb ER HSX)].
  intros r W' c' (ly' & regsR & memR & mdR & Hc & HP & HR & HL & regsC & memC & mdC & regs6 & mem6 & md6 & FR1 & XD & FRT).
  destruct XE as (_ & XEe & XEm). destruct XD as (_ & XDe & XDm).
  exists ly', regsR, memR, mdR. split; [exact Hc|]. split; [exact HP|]. split; [exact HR|].
  split.
  { (* errno: the walk's raw facts at errno's bytes and the two callees' errno conjuncts *)
    intros i Hi. assert (Ex : as_errno B <= bv_unsigned (w64 (as_errno B + i)) < as_errno B + 4) by (rewrite (EB i Hi); lia).
    destruct (EW _ Ex) as (N1 & N2 & N3 & N4 & N5).
    rewrite (FRT _ N1), (XDe i Hi), (FR1 _ N1), (XEe i Hi). exact (DMfr _ N2 N3 N4 N5). }
  split; [|exact HL].
  (* memnorm: dmem_m's frame, Enqueue's keep, Put's frame, Drain's keep, Put's frame *)
  assert (M1 : MemnormT.memnorm_keep tfibsegs mem (ms_mem msE)).
  { refine (MemnormDmid.memnorm_dmem_m W ly _ mem tr _ _ hb1 _ j1 j2 j3 regs (bv_unsigned (getr regs 2)) (ms_mem msE) FH _ DMfr).
    rewrite RG2. reflexivity. }
  assert (M3 : MemnormT.memnorm_keep tfibsegs mem' memC).
  { apply (MemnormDmid.mn_keep_stack ly (bv_unsigned (getr regs 2) - 80) (bv_unsigned (getr regs 2)) mem' memC LY);
      [unfold DFSTACK_G, spZ in *; lia | unfold spZ in *; lia | exact FR1]. }
  assert (M5 : MemnormT.memnorm_keep tfibsegs mem6 memR).
  { apply (MemnormDmid.mn_keep_stack ly (bv_unsigned (getr regs 2) - 80) (bv_unsigned (getr regs 2)) mem6 memR LY);
      [unfold DFSTACK_G, spZ in *; lia | unfold spZ in *; lia | exact FRT]. }
  exact (MemnormLocG.memnorm_keep_trans _ _ _ _ M1 (MemnormLocG.memnorm_keep_trans _ _ _ _ XEm
    (MemnormLocG.memnorm_keep_trans _ _ _ _ M3 (MemnormLocG.memnorm_keep_trans _ _ _ _ XDm M5)))). }
eapply YG0dH.amreal'_mono; [| exact (YG0dHc.amreal'_apath_gflag tfibsegs YGcfRehidePost.RZ_cf _ _ _ _ MAIN)].
intros r W' c' [(ly' & regs' & mem' & md' & Hc & Hpost & Hraw & He & Hm & Hlp) HPATH].
exists ly', regs', mem', md'. split; [exact Hc|].
split.
{ exact (conj Hpost (Hraw eq_refl)). }
split; [exact He|]. split; [exact Hm|]. split; [exact Hlp | exact HPATH].
Qed.
End e.
End d.
