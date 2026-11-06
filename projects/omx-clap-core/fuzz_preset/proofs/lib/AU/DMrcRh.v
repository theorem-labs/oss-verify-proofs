(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMrcRh.v (a working branch 5ad50e61fc6a, file sha256 d3814de1376e) onto omx-clap-core/fuzz_preset's asan-ubsan image (unstripped fuzz_preset.asan-ubsan, sha256 3b5e1a099b53); module paths changed; its 3 image addresses moved by code-verified function pairs (3 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 0 code pcs the tool read as sizes, by the internal file funcpair.py), and 1 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10-30: a Theorem Labs lane's delta to proofs/cgif/cgif_file_fuzzer/lib/DMrcRh.v (5ad50e61fc6a -> a working branch 9f12c64c854, file sha256 9c8e6156f0a5) applied at B' by a 3-way merge (base and theirs the two cgif texts, ours this file): the index-keyed dead_shadow_new (the cut's sc_ELEN gives LIVE). 0 conflicts; no numeral in the delta. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (F1 priming row R3, lane B1, slice H4; integrator a Theorem Labs lane): new file. rule 24: no function
   proved here (kind: F1 priming of an already proved walk, the secondary arm of __asan::QuarantineCallback::Recycle
   (0x348fc): lift to YA0nH.SRr' / YG0dH.amreal' and apply the core's re-hide step at the return).

   WHAT.  [rchunk_sec_mach_MX] is DMrcSecM.rchunk_sec_mach_M_g at ARXp := ARXsl with three more conjuncts kept from
   DMrcSecGv.at_RET: the return value is (tt, YFg8.X2v ...), the return world is YFg8.W2 (the munmap's refund of the map
   interval), and every byte of the madvised interior [PBv, PEv) of the dead map's shadow reads 0 (at_RET's SHD).  The
   prelude and the Section header are DMrcSecM.v's, verbatim, with its lemmas CUT / MAPR and the notation SC, the post
   relation of the step field named [ARXsl] and indexed by the slack (RSs : DMrcSecReads.rc_sec_step_g B ARXr ARXsl
   AOX: the post at ARXsl (YGcfRehidePost.rh_hi MAP LEN - YGcfRehidePost.rh_lo MAP)); the proof is DMrcSecM's, with the
   three conjuncts added at the return.
   WHY ARXsl.  At a real recycle the cut relation does not hold at the return state with the return world W2: the budget
   drops the dead hull, the world's allowance still counts it.  Only a loosened relation holds there (at the cf instance
   YGcfRehideAR.ARcfR_sl with slack rh_hi MAP LEN - rh_lo MAP); plain ARXr holds again in the re-hidden world.
   [rchunk_sec_rh] lifts MX to amreal' at the zone YGcfRehidePost.RZ_cf (YG0dH.amreal_amreal') and, at the return,
   takes the core's re-hide step YA0nR.SRr'_rehide_ret with h := shull (MAP, LEN), PB := rh_lo MAP, PE := rh_hi MAP LEN
   (YGcfRehidePost's; they are DMrcSecMat.PBv / PEv, [PBv_rh_lo] / [PEv_rh_hi]); its post is DMrcSec.rc_mach_sec with
   acall_post_x replaced by YGcfRehidePost.acall_post_x_rh over ARXr at the re-hidden world, every other conjunct
   unchanged (the machine part of MnRecycle.de_rchunk_m_t under the re-hide).  Every path takes the step (M2 makes the
   interior not empty), so no post is stated at W2 itself.  The newly hidden set is dead_shadow_new ly X X2v: slot r is
   a live extent at the entry state X (the chunk k) and dead at X2v.  The user view frame still holds at the re-hidden
   world, since a user byte of the primary space lies above the shadow interior.  The re-hidden world W' is not stated:
   the post holds of it.
   Section premises beyond DMrcSecM's (the cf side discharges them):
   - [HULL]: the shadow hull of the map is in the allowance at the call (the cf relation's asecA).
   - [SREAL]: the slot is a real secondary (0 <= sm_size sm), so that at the post it is in dead_shadow_new.
   - [M1]: the map is disjoint from every secondary extent of the post state.  Its alignment and static-extent parts,
     which the core's M1 premise also states, are derived here from the cut (sc_GEOM, sc_MAPX with sc_ELEN).
   - [M2]: kMaxSize + kPage <= LEN.  With it the interior is not empty (rh_lo MAP <= rh_hi MAP LEN).
   - [REHIDE]: rc_sec_rehide_t, the statement of the F1 core's YGcfRehideAR.ARcfR_rehide over the opaque relations, its
     premises in the core's order: the dead slot's identity at X2v, M1, M2, JUNK (every byte of as_junk B ly lies in a
     segment of tfibsegs; [junk_segs] gives it from TfibSyms' ts_junk), the hull in the allowance of the world W2'
     before the re-hide, ARXsl at the slack rh_hi MAP LEN - rh_lo MAP and (X2v, W2'), the interior mapped; its
     conclusion plain ARXr at the re-hidden world.  At the call W2' is YFg8.W2, the refund of the map interval, and HULL
     gives the hull there (the hull is not the map interval).
   [rchunk_sec_rh_nf] is the same theorem without the cache flag (the twin of DMrcSecNf.rchunk_sec_m_nf): its pre is
   DMiface.rcc_pre_sec, its fields DMrcSecNf's flag-free fields (the step DMrcSecNf.rc_sec_step_nf_g at ARXsl), its post
   rchunk_sec_rh's without the st_cache_inited conjunct and with DRq (snd r0) ks zs (from DMrcReads.rc_model_t).  It is
   rchunk_sec_rh at X1 = set_cache_inited true X over DMrcSecNf.ARXu ARXr / fun d => ARXu (ARXsl d) / AOXu AOX at the
   flag of X (the walk does not read the flag), as DMrcSecNf does it.  HULL, SREAL, M1, M2 and REHIDE are stated at X (no
   flag-restored form is needed): X2v at X1 differs from X2v at X only in the flag, and ARXu at the flag of X reads the
   relation at X2v of X (X2v_flag). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Logic.FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a YB1w YFeq YFex YFfu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFfj YFew YFeu YFfm YFf3 YFf4 YFff YFgu YFf5 YFgw YFfb YFg8 YFfc YB13.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG08 YG0g.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require DMwalkIF DMrcSecFc DMrcSecGv DMrcSecWalk DMrcSecF6 DMrcSecF7 DMrcSecF9 DMrcSecMun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require ErrnoG MemnormT MemnormLocG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require MemnormSafecgif DMrcReads DMrcSecReads DMrcConst.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DIfaceR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import DMwalkIF.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0v YFfn YA05 YG0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require DMrcSec DMrcSecMat DMrcSecMunM DMrcSecNf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YA0nR YG0dH YG0dHc YGcfRehidePost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kPtrArrayResv, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, KSTACK, TFIB_IMG_END, kBatchBytes, SHADOW_OFF, TFIB_TP, TFIB_TSD, TFIB_INST, A_ALLOCATOR, o_space, o_rinfo, o_sec, o_sec_chunks, o_sec_reserved, o_sec_n, o_sec_sorted, o_sec_stats, o_sec_mutex, kRegionInfoOff, kLowMemEnd, kChunkHeaderSize, kPage, YFgu.GFRAME, DMrcSecGv.GDEPTH in *.
Ltac splits := repeat match goal with |- _ /\ _ => split end.
Ltac inS := cbn [In]; repeat (first [left; reflexivity | right]).
Ltac numconst_hi := ceil; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kPtrArrayResv, kLowMemEnd, kPage, t_stats, A_ALLOCATOR, TFIB_INST, SHADOW_OFF, kHighShadowBeg, kHighShadowEnd in *.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The re-hide step's view and presence outside the interior [PB, PE). *)
Lemma aview_rehide_out {fx : YK11.FPState} {rc : YM05.RunCeil} : forall (segs : list Segment) (H : word -> bool) PB PE
  (m : word -> option byte) a, 0 <= a < 2 ^ 64 -> ~ (PB <= a < PE) ->
  aview segs (YA0nR.H_rehide H PB PE) m a = aview segs H m a.
Proof.
intros segs H PB PE m a Ha Hn. unfold aview, YP09.mbyte, mrestrict, YA0nR.H_rehide, YA0nR.in_ivb.
rewrite (YA0nR.u64_rh a Ha).
destruct (PB <=? a) eqn:E1; destruct (a <? PE) eqn:E2; cbn [andb]; rewrite ?orb_false_r; try reflexivity.
apply Z.leb_le in E1. apply Z.ltb_lt in E2. exfalso. lia.
Qed.

Lemma apresent_rehide_out : forall (H : word -> bool) PB PE (m : word -> option byte) a, 0 <= a < 2 ^ 64 -> ~ (PB <= a < PE) ->
  apresent H m a -> apresent (YA0nR.H_rehide H PB PE) m a.
Proof.
intros H PB PE m a Ha Hn [Hh Hb]. split; [|exact Hb]. unfold YA0nR.H_rehide, YA0nR.in_ivb. rewrite Hh, (YA0nR.u64_rh a Ha).
destruct (PB <=? a) eqn:E1; destruct (a <? PE) eqn:E2; cbn [andb orb]; try reflexivity.
apply Z.leb_le in E1. apply Z.ltb_lt in E2. exfalso. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The interior's arithmetic: DMrcSecMat.PBv / PEv are YGcfRehidePost.rh_lo / rh_hi; with M2 the hull and the interior
   have the step's shape; the interior lies in the shadow window, above the image and below the allocator ceiling. *)
Section a. Context {rc : YM05.RunCeil}.
Lemma PBv_rh_lo : forall m, DMrcSecMat.PBv m = YGcfRehidePost.rh_lo m.
Proof.
intros m. unfold DMrcSecMat.PBv, YGcfRehidePost.rh_lo, DMrcSecGv.SHAv, shadow_addr.
pose proof (Z.div_mod (SHADOW_OFF + m / 8 + 4095) 4096 ltac:(lia)). lia.
Qed.

Lemma PEv_rh_hi : forall m l, DMrcSecMat.PEv m l = YGcfRehidePost.rh_hi m l.
Proof.
intros m l. unfold DMrcSecMat.PEv, YGcfRehidePost.rh_hi, DMrcSecGv.SHEv, DMrcSecGv.SHAv, DMrcSecGv.CNTv, shadow_addr.
pose proof (Z.div_mod (SHADOW_OFF + m / 8 + l / 8) 4096 ltac:(lia)). lia.
Qed.

Lemma rh_shape_int : forall m l, 0 <= m -> m + l <= ASAN_CEIL -> kMaxSize + kPage <= l ->
  YA0nR.rh_shape (shull (m, l)) (DMrcSecMat.PBv m) (DMrcSecMat.PEv m l).
Proof.
intros m l H0 H1 H2. rewrite PBv_rh_lo, PEv_rh_hi. pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as C.
unfold kMaxSize, kPage in H2.
unfold YA0nR.rh_shape, shull, YGcfRehidePost.rh_lo, YGcfRehidePost.rh_hi, page_size. cbn [fst snd].
assert (S0 : 0 <= shadow_addr m) by (unfold shadow_addr, SHADOW_OFF; lia).
assert (S1 : shadow_addr m + l / 8 + 4095 < 2 ^ 64) by (unfold shadow_addr, SHADOW_OFF; lia).
assert (S2 : 8704 <= l / 8) by lia.
generalize dependent (shadow_addr m). intros s S0 S1.
splits; try (apply Z.mod_mul; lia); lia.
Qed.

Lemma int_WINS : forall m l a, 0 <= m -> 0 <= l -> m + l <= ASAN_CEIL -> DMrcSecMat.PBv m <= a < DMrcSecMat.PEv m l ->
  0 <= a < 2 ^ 64 /\ DMrcSecGv.SHAv m <= a < DMrcSecGv.SHAv m + DMrcSecGv.CNTv l.
Proof.
intros m l a H0 H1 H2 Ha. pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as C.
unfold DMrcSecMat.PBv, DMrcSecMat.PEv, DMrcSecGv.SHEv, DMrcSecGv.SHAv, DMrcSecGv.CNTv, SHADOW_OFF in *.
pose proof (Z.mod_pos_bound (2147450880 + m / 8 + 4095) 4096 ltac:(lia)).
pose proof (Z.mod_pos_bound (2147450880 + m / 8 + l / 8) 4096 ltac:(lia)).
lia.
Qed.

Lemma int_img : forall m a, 0 <= m -> DMrcSecMat.PBv m <= a -> YF0x.TFIB_IMG_END <= a.
Proof.
intros m a H0 Ha. unfold DMrcSecMat.PBv, DMrcSecGv.SHAv, SHADOW_OFF, YF0x.TFIB_IMG_END in *.
pose proof (Z.mod_pos_bound (2147450880 + m / 8 + 4095) 4096 ltac:(lia)). lia.
Qed.

Lemma int_ceil : forall m l, 0 <= m -> 0 <= l -> m + l <= ASAN_CEIL -> DMrcSecMat.PEv m l <= ASAN_CEIL.
Proof.
intros m l H0 H1 H2. pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as C.
unfold DMrcSecMat.PEv, DMrcSecGv.SHEv, DMrcSecGv.SHAv, DMrcSecGv.CNTv, SHADOW_OFF in *.
pose proof (Z.mod_pos_bound (2147450880 + m / 8 + l / 8) 4096 ltac:(lia)). lia.
Qed.

(* The interior lies below the high application memory (the primary allocator's space is there). *)
Lemma int_high : forall m l, 0 <= m -> 0 <= l -> m + l <= ASAN_CEIL -> DMrcSecMat.PEv m l <= 0x10007fff8000.
Proof.
intros m l H0 H1 H2. pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as C.
unfold DMrcSecMat.PEv, DMrcSecGv.SHEv, DMrcSecGv.SHAv, DMrcSecGv.CNTv, SHADOW_OFF in *.
pose proof (Z.mod_pos_bound (2147450880 + m / 8 + l / 8) 4096 ltac:(lia)). lia.
Qed.

(* The hull is not the map interval: it lies in the shadow, the map in the application range. *)
Lemma hull_ne : forall m l, zone3 m l -> 0 <= l -> shull (m, l) <> (m, m + l).
Proof.
intros m l (Z0 & Z1 & Z2) H0 E. apply (f_equal fst) in E. unfold shull, shadow_addr in E. cbn [fst] in E.
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as C.
unfold YF0x.zone3cases, YF0x.TFIB_IMG_LO, YF0x.TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

Lemma zone3_in_app : forall x sz, zone3 x sz -> in_app x sz.
Proof.
intros x sz (Z0 & Z1 & Z2). unfold in_app. split; [exact Z0|].
unfold YF0x.zone3cases, YF0x.TFIB_IMG_LO, YF0x.TFIB_IMG_END, kLowShadowBeg in *. lia.
Qed.
End a.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.
(* The core's JUNK premise at image B': ts_junk puts every junk range in [0xa2000, 0x601000), which the segments
   [0xa2000, 0xa4000) and [0xa4000, 0x601000) of tfibsegs tile (as DMrcSecCf.img_junk_cgif). *)
Lemma junk_segs : forall B ly, TfibSyms B -> forall r0, In r0 (as_junk B ly) -> forall j, 0 <= j < snd r0 ->
  exists sg, In sg tfibsegs /\ Z.of_N (seg_base sg) <= aeval B ly (fst r0) + j < Z.of_N (seg_base sg) + Z.of_N (seg_size sg).
Proof.
intros B ly TB r0 Hr j Hj.
destruct (ts_junk _ TB ly r0 Hr) as (z & Ez & Z1 & Z2). rewrite Ez. cbn [aeval]. unfold YImgTop.IMG_TOP in Z2.
destruct (Z_lt_le_dec (z + j) 671744) as [L|L].
- exists AsanUbsan.AsanUbsan_segment_002. split; [do 2 right; left; reflexivity | cbn; lia].
- exists AsanUbsan.AsanUbsan_segment_003. split; [do 3 right; left; reflexivity | cbn; lia].
Qed.

Section e.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable ARXsl : Z -> (Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop).
Variable AOX : alayout -> astate -> Z -> Prop.
Hypothesis RCs : DMrcSecReads.rc_sec_cut_t B ARXr.
Hypothesis RMs : DMrcSecReads.rc_sec_mapr_t B ARXr.
Hypothesis RSs : DMrcSecReads.rc_sec_step_g B ARXr ARXsl AOX.
Variables NMAXD LMAXD : Z.
Hypothesis NOK : DMwalkIF.nmaxd_ok NMAXD.
Hypothesis LOK : DMwalkIF.lmaxd_ok NMAXD LMAXD.
Variables (inst : Z) (ly : alayout) (X : astate) (k : chunk) (cbp : Z) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (r : nat) (o : Z) (sm : secmap) (i : nat).
Hypothesis PRE : rcc_pre_x B ARXr inst ly X k cbp W regs mem md.
Hypothesis Hb : ck_beg k = PSec r o.
Hypothesis Hsm : nth_error (st_secs X) r = Some sm.
Hypothesis Hi : nth_error (st_sec_arr X) i = Some r.
Hypothesis HN : ck_n k < NMAXD.
Hypothesis HE : ck_extent k <= LMAXD.
Hypothesis Hst : ck_state k = CQuarantined.
Hypothesis Hni : ~ In (ck_beg k) (map ck_beg (q_items X)).
Hypothesis Hkin : In k (st_chunks X).
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Notation T := (ly_T ly).
Local Notation Q := (ly_Q ly).
Local Notation MAP := (YFg8.MAP ly r).
Local Notation LEN := (YFg8.LEN sm).
Local Notation nA := (YFg8.nA X).
Local Notation idx := (YFg8.idx i).
Local Notation qi := (YFg8.qi ly i).
Local Notation lst := (YFg8.lst ly X r).
Local Notation own := (YFg8.own X i).
Local Notation vra := (DMrcSecF6.v regs 1%bv).
Local Notation vs0 := (DMrcSecF6.v regs 8%bv).
Local Notation vs1 := (DMrcSecF6.v regs 9%bv).
Local Notation vs2 := (DMrcSecF6.v regs 18%bv).
Local Notation X2v := (YFg8.X2v X k r sm i).
Local Notation W2 := (YFg8.W2 ly W r sm).
Lemma CUT : inst = as_inst B /\ ly_tsd ly = as_tsd B /\ Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (as_const B ly) /\
DMrcSecFc.sec_cut B ly X k W regs mem r o sm i.
Proof. exact (RCs inst ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi Hkin Hst). Qed.
Lemma MAPR : index_of (st_sec_arr X) r 0%nat = Some i /\
In (MAP, MAP + LEN) (w_A W) /\ In (w64 MAP, w64 LEN) (vm_maps (m_vmmaps md)) /\ amwf md /\
(forall PB kk, 0 < kk -> DMrcSecGv.SHAv MAP <= PB -> PB + kk <= DMrcSecGv.SHEv MAP LEN ->
 madvise_dontneed_ok (m_vmmaps md) (Z_to_bv 64 PB) (Z_to_bv 64 kk) = true).
Proof. exact (RMs inst ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi). Qed.
Local Notation SC := (proj2 (proj2 (proj2 CUT))).

(* rchunk_sec_mach_M_g at ARXsl (at the recycled slot's slack) with the return value, the return world (W2) and the zero
   shadow interior of the return memory. *)
Theorem rchunk_sec_mach_MX : amreal tfibsegs (recycle_chunk k X) W (cfg_at tfibsegs A_RChunk regs mem md)
  (fun (r0 : unit * astate) (W' : world tfibsegs) (c' : config) =>
   r0 = (tt, X2v) /\ W' = W2 /\
   DMrcSec.rc_mach_sec_g B (ARXsl (YGcfRehidePost.rh_hi MAP LEN - YGcfRehidePost.rh_lo MAP)) AOX inst ly X k W regs mem md r0 W' c' /\
   DMrcSecMat.mat_rec ly MAP LEN lst (m_vm_materialized md) (m_vm_materialized (cfg_model c')) /\
   DMrcSecMat.mat_gone MAP LEN (m_vm_materialized (cfg_model c')) /\
   exists regs' mem' md', c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
   forall a, DMrcSecMat.PBv MAP <= a < DMrcSecMat.PEv MAP LEN -> mem' (w64 a) = Some (Z_to_bv 8 0)).
Proof.
pose proof MAPR as (Hidx & INA & INV & MW & GATE).
pose proof (DMrcSecFc.GEOMw _ _ _ _ _ _ _ _ _ _ _ SC NMAXD LMAXD LOK HE) as (P1 & P2 & P3 & [L1 L1'] & L2 & _).
pose proof (DMrcSecFc.sc_Hk _ _ _ _ _ _ _ _ _ _ _ SC) as Hk.
pose proof (DMrcSecMun.SMALL B ly X k W regs mem r o sm i SC NMAXD LMAXD LOK HE) as SMALL.
pose proof (DMrcSecMunM.WALK_M B TB ly X k cbp W regs mem md r o sm i ARXr inst PRE SC NMAXD LMAXD NOK LOK HN HE Hi GATE) as WALK.
rewrite (YFg8.recycle_chunk_sec k X r o sm i (proj2 (mem_chunk_spec _ _) Hk) Hb Hsm Hidx SMALL). cbn [amreal].
eapply SRr_bind; [exact WALK|]. intros W1 c1 _ (regsD & memD & LNK & HM).
destruct HM as (-> & regs1 & mem1 & mat1 & -> & H17 & H10 & H11 & _ & _ & INNER). cbv zeta in INNER.
apply SRr_use_AI. cbn [cfg_model]. intros HAI. apply SRr_ret.
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md) in *.
set (c2 := mkCfg (mkst (regupd regs1 10 (w64 0)) (w64 0x653b8) (unfill (w64 MAP) (w64 LEN) mem1) (seg_rom tfibsegs))
  (munmap_model (w64 MAP) (w64 LEN) md1)).
assert (UM : bv_unsigned (w64 MAP) = MAP) by (unfold w64; apply unsigned_lit_small; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia).
assert (UL : bv_unsigned (w64 LEN) = LEN) by (unfold w64; apply unsigned_lit_small; lia).
assert (MW1 : amwf md1) by (apply (amwf_same md md1); [subst md1; apply m_vmmaps_wvb | subst md1; apply m_vm_lazy_wvb | exact MW]).
assert (INV1 : In (w64 MAP, w64 LEN) (vm_maps (m_vmmaps md1))) by (subst md1; rewrite m_vmmaps_wvb; exact INV).
destruct (in_split _ _ INV1) as (l1 & l2 & EVM).
exists unit, (fun _ => c2), (fun _ => 1), (fun _ => false), tt.
split.
{ pose proof (munmap_node tfibsegs regs1 (w64 0x653b4) mem1 (seg_rom tfibsegs) md1 (w64 MAP) LEN (AI_halted _ _ _ _ HAI) H17 H10
    ltac:(rewrite UM; unfold page_size; exact P3) H11 ltac:(lia)
    ltac:(rewrite UM, (YFg8.page_round_up_Z_aligned LEN) by lia; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, two_pow_64, TASK_SIZE, kHighMemBeg, ASAN_CEIL in *; lia)
    ltac:(rewrite (YFg8.page_round_up_Z_aligned LEN) by lia; exact (map_has_In _ _ _ INV1))) as ND.
  cbv zeta in ND. rewrite (YFg8.page_round_up_Z_aligned LEN) in ND by lia. exact ND. }
split. { intros [] _. cbn [cfg_model]. exact (munmap_AI tfibsegs (w_H W) (w_A W) md1 (w64 MAP, w64 LEN) l1 l2 HAI MW1 EVM
    ltac:(cbn [fst]; rewrite UM; unfold page_size; exact P3)
    ltac:(cbn [fst snd]; rewrite UM, UL; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia)). }
split. { intros []. cbn [aok]. reflexivity. }
split; [reflexivity|]. split; [reflexivity|]. split; [intros [] _; reflexivity|]. split; [intros [] XX; discriminate XX|].
intros [] _. cbn [amreal].
eapply SRr_bind; [exact INNER|]. intros W3 c3 _ HR. pose proof HR as ((-> & regs' & mem' & mat' & Ec3 & _) & _).
apply SRr_use_AI. intros HAI3. rewrite Ec3 in HAI3 |- *. cbn [cfg_model] in HAI3.
apply (SRr_world_le tfibsegs W W2).
{ apply wrefund_wle. }
{ intros _. cbn [cfg_model]. apply AI_refund_gen; [exact HAI3|]. intros p Hp. rewrite m_vm_lazy_wvb in Hp. unfold YFg8.iv. cbn [fst snd].
  pose proof (munmap_lazy_out (w64 MAP) (w64 LEN) md1 p ltac:(destruct MW1 as [(_ & _ & W3l & _) _]; intros q Hq; exact (W3l q Hq))
    ltac:(rewrite UM, UL; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia) Hp) as NL. rewrite UM, UL in NL. exact NL. }
apply SRr_ret. rewrite <- Ec3. destruct HR as (HRp & MR & MG). cbv beta.
split; [reflexivity|]. split; [reflexivity|].
split; [exact (DMrcSec.FINx_g B TB ARXr ARXsl AOX RCs RSs NMAXD LMAXD LOK inst ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi HE Hst Hni Hkin
  regsD memD mat1 c3 LNK HRp)|].
split; [exact MR|]. split; [exact MG|].
destruct HRp as (_ & regsR & memR & matR & EcR & _ & _ & _ & _ & _ & _ & SHDR & _).
exists regsR, memR. eexists. split; [rewrite EcR; reflexivity|].
intros a Ha. unfold DMrcSecGv.SHD in SHDR. apply SHDR.
destruct P1 as (P1a & _).
destruct (int_WINS MAP LEN a ltac:(lia) ltac:(lia) P2 Ha) as [Ua Wa].
unfold DMrcSecGv.WINS, w64. rewrite (YA0nR.u64_rh a Ua). exact Wa.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The premises of the re-hide at the return (the cf side discharges them). *)
Hypothesis HULL : In (shull (MAP, LEN)) (w_A W).
Hypothesis SREAL : YGcfRehidePost.sec_real sm.
Hypothesis M1 : Forall (zdisjoint (MAP, LEN)) (sec_extents ly X2v).
Hypothesis M2 : kMaxSize + kPage <= LEN.
(* The F1 core's YGcfRehideAR.ARcfR_rehide over the opaque relations, its binders and premises in the core's order, at
   the post state X2v (the walk's post state, YFg8.X2 (YFf3.X1 X k) r i sm by definition), the slot r and the map
   (MAP, LEN): from the loosened relation ARXsl at the slack rh_hi MAP LEN - rh_lo MAP and (X2v, W2'), W2' the world
   before the re-hide, plain ARXr at the re-hidden world. *)
Definition rc_sec_rehide_t : Prop :=
  forall (W2' : world tfibsegs) (mem' : word -> option byte) (md' : Model) (sm2 : secmap)
    (HO : H_off_segments tfibsegs (YA0nR.H_rehide (w_H W2') (YGcfRehidePost.rh_lo MAP) (YGcfRehidePost.rh_hi MAP LEN)))
    (HA : A_wf (YA0nR.A_rehide (w_A W2') (shull (MAP, LEN)) (YGcfRehidePost.rh_lo MAP) (YGcfRehidePost.rh_hi MAP LEN)))
    (H8 : forall a : Z, YG0f.in_band_rw a ->
      YA0nR.H_rehide (w_H W2') (YGcfRehidePost.rh_lo MAP) (YGcfRehidePost.rh_hi MAP LEN) (Z_to_bv 64 a) =
      YA0nR.H_rehide (w_H W2') (YGcfRehidePost.rh_lo MAP) (YGcfRehidePost.rh_hi MAP LEN) (Z_to_bv 64 (a - a mod 8))),
  nth_error (st_secs X2v) r = Some sm2 -> sm_live sm2 = false -> 0 <= sm_size sm2 -> in_app MAP LEN ->
  MAP = ly_sec ly r -> LEN = sm_len sm2 ->
  MAP mod page_size = 0 /\ Forall (zdisjoint (MAP, LEN)) (sec_extents ly X2v ++ static_extents ly) ->
  kMaxSize + kPage <= LEN ->
  (forall r0, In r0 (as_junk B ly) -> forall j, 0 <= j < snd r0 ->
    exists sg, In sg tfibsegs /\ Z.of_N (seg_base sg) <= aeval B ly (fst r0) + j < Z.of_N (seg_base sg) + Z.of_N (seg_size sg)) ->
  In (shull (MAP, LEN)) (w_A W2') ->
  ARXsl (YGcfRehidePost.rh_hi MAP LEN - YGcfRehidePost.rh_lo MAP) inst ly X2v W2' mem' md' ->
  (forall a, YGcfRehidePost.rh_lo MAP <= a < YGcfRehidePost.rh_hi MAP LEN -> mem' (w64 a) <> None) ->
  ARXr inst ly X2v (YA0nR.wrehide tfibsegs W2' (shull (MAP, LEN)) (YGcfRehidePost.rh_lo MAP) (YGcfRehidePost.rh_hi MAP LEN) HO HA H8)
    mem' md'.
Hypothesis REHIDE : rc_sec_rehide_t.

(* rc_mach_sec under the re-hide: acall_post_x_rh for acall_post_x, every other conjunct unchanged. *)
Theorem rchunk_sec_rh : YG0dH.amreal' tfibsegs YGcfRehidePost.RZ_cf (recycle_chunk k X) W (cfg_at tfibsegs A_RChunk regs mem md)
  (fun (r0 : unit * astate) (W' : world tfibsegs) (c' : config) => exists regs' mem' md',
   c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
   YGcfRehidePost.acall_post_x_rh B ARXr AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r0) W' regs' mem' md' /\
   acall_raw_x B AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r0) W' regs' mem' md' /\
   ErrnoG.errno_kept B mem mem' /\ MemnormT.memnorm_keep tfibsegs mem mem' /\
   (forall a, 0 <= a < 2 ^ 64 -> YFeuC.puser ly X a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) ->
    aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) /\
   (forall a, YFeuC.puser ly X a -> YFeuC.puser ly (snd r0) a) /\
   st_cache_inited (snd r0) = true /\ (forall a, AOX ly (snd r0) a -> AOX ly X a)).
Proof.
pose proof (DMrcSecFc.GEOMw _ _ _ _ _ _ _ _ _ _ _ SC NMAXD LMAXD LOK HE) as (G1 & G2 & G3 & [G4 G4'] & G5 & _).
pose proof (DMrcSecFc.sc_HI _ _ _ _ _ _ _ _ _ _ _ SC) as (hP1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & hCE & hPS & _).
pose proof (DMrcSecFc.sc_ELEN _ _ _ _ _ _ _ _ _ _ _ SC) as (EL & _ & LIVE).
pose proof PRE as (_ & _ & _ & _ & _ & HloCF & _).
assert (Usp : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; apply u64_range).
assert (G0 : 4096 <= MAP) by (destruct G1 as (G1a & _); exact G1a).
assert (INAPP : in_app MAP LEN) by exact (zone3_in_app _ _ G1).
assert (EPB : DMrcSecMat.PBv MAP = YGcfRehidePost.rh_lo MAP) by apply PBv_rh_lo.
assert (EPE : DMrcSecMat.PEv MAP LEN = YGcfRehidePost.rh_hi MAP LEN) by apply PEv_rh_hi.
assert (SH : YA0nR.rh_shape (shull (MAP, LEN)) (YGcfRehidePost.rh_lo MAP) (YGcfRehidePost.rh_hi MAP LEN))
  by (rewrite <- EPB, <- EPE; apply rh_shape_int; [lia | exact G2 | exact M2]).
assert (PEC : YGcfRehidePost.rh_hi MAP LEN <= ASAN_CEIL) by (rewrite <- EPE; apply int_ceil; [lia | lia | exact G2]).
(* a user byte of the primary space is above the interior *)
assert (PUHI : forall a, YFeuC.puser ly X a -> YGcfRehidePost.rh_hi MAP LEN <= a).
{ intros a (c & Hc & Ha). rewrite <- EPE. unfold region_base, region_off in Ha. rewrite Z.shiftl_mul_pow2 in Ha by lia.
  change (2 ^ 32) with 4294967296 in Ha. unfold kHighMemBeg in hP1.
  pose proof (int_high MAP LEN ltac:(lia) ltac:(lia) G2) as PH. lia. }
assert (HS : forall a : word, YGcfRehidePost.rh_lo MAP <= bv_unsigned a < YGcfRehidePost.rh_hi MAP LEN ->
  find_segment tfibsegs (bv_unsigned a) 1 = None).
{ intros a Ha. rewrite <- EPB, <- EPE in Ha. apply YF0x.tfib_find_segment_none_high. apply (int_img MAP); [lia | lia]. }
(* the dead real slot of the map at the post state *)
assert (SEC2 : nth_error (st_secs X2v) r = Some (mkSec (sm_len sm) (sm_size sm) false)).
{ unfold YFg8.X2v, YFg8.X2, YFg8.X1, YFf3.X1. cbn [st_secs set_sec_arr set_secs set_chunks].
  apply nth_error_lupd_same. exact (nth_error_lt _ _ _ Hsm). }
(* the set at the core's index key (YGcfRehidePost.dead_shadow_new): slot r held the live entry sm at the entry state X (Hsm, LIVE from
   the cut's sc_ELEN) and holds the dead entry of the same length at X2v (SEC2) *)
assert (DS : forall a, YGcfRehidePost.rh_lo MAP <= a < YGcfRehidePost.rh_hi MAP LEN -> YGcfRehidePost.dead_shadow_new ly X X2v a).
{ intros a Ha. exists r, (mkSec (sm_len sm) (sm_size sm) false), sm.
  split; [|split; [exact Hsm|split; [exact LIVE|split; [reflexivity|]]]].
  - split; [exact SEC2|]. split; [reflexivity|]. split; [exact SREAL|]. split; [exact INAPP|]. cbn [sm_len]. unfold YFg8.LEN in G4. lia.
  - cbn [sm_len]. exact Ha. }
(* the core's REHIDE premise M1, from M1 and the cut *)
assert (M1F : MAP mod page_size = 0 /\ Forall (zdisjoint (MAP, LEN)) (sec_extents ly X2v ++ static_extents ly)).
{ split; [unfold page_size; exact G3|]. apply Forall_app. split; [exact M1|].
  apply Forall_forall. intros y Hy. destruct (In_nth_error _ _ Hy) as [j Hj].
  pose proof (DMrcSecFc.sc_MAPX _ _ _ _ _ _ _ _ _ _ _ SC j y Hj) as D. rewrite EL. exact D. }
(* the hull is in the allowance of the return world W2 (the refund of the map interval, which is not the hull) *)
assert (HW2 : In (shull (MAP, LEN)) (w_A W2)).
{ unfold YFg8.W2, wrefund. cbn [w_A]. apply (proj2 (A_drop_In _ _ _)). split; [exact HULL|].
  exact (hull_ne MAP LEN G1 ltac:(lia)). }
apply (YG0dHc.amreal'_then_SRr' tfibsegs YGcfRehidePost.RZ_cf _ _ _ _ _
  (YG0dH.amreal_amreal' tfibsegs YGcfRehidePost.RZ_cf _ _ _ _ rchunk_sec_mach_MX)).
intros r0 W' c' (-> & -> & RM & _ & MG & regs1 & mem1 & md1 & Ec1 & ZR).
destruct RM as (regs' & mem' & md' & Ec & POST & RAW & ERR & MN & AV & PU & CI & AO).
rewrite Ec in Ec1. unfold cfg_at in Ec1. injection Ec1 as E1 E2 E3. subst regs1 mem1 md1. subst c'.
pose (HO := YA0nR.Hoff_rehide tfibsegs (w_H W2) (YGcfRehidePost.rh_lo MAP) (YGcfRehidePost.rh_hi MAP LEN) (w_Hoff W2) HS).
pose (HA := YA0nR.Awf_rehide (w_A W2) (shull (MAP, LEN)) (YGcfRehidePost.rh_lo MAP) (YGcfRehidePost.rh_hi MAP LEN) (w_Awf W2) SH).
(* preset's world carries w_H8 (YA0n.v:25): the re-hidden world's proof of it, from w_H8 W2 and the 8-aligned (page
   rounded) rh_lo / rh_hi, by YA0nR.H_rehide_H8 *)
assert (M8 : forall x, (x / 4096 * 4096) mod 8 = 0)
  by (intro x; replace (x / 4096 * 4096) with ((x / 4096 * 512) * 8) by ring; apply Z.mod_mul; lia).
pose (HB8 := YA0nR.H_rehide_H8 (w_H W2) (YGcfRehidePost.rh_lo MAP) (YGcfRehidePost.rh_hi MAP LEN)
  ltac:(unfold YGcfRehidePost.rh_lo; apply M8) ltac:(unfold YGcfRehidePost.rh_hi; apply M8) (w_H8 W2)).
(* the interior is mapped: the walk zeroed it *)
assert (NZ : forall a, YGcfRehidePost.rh_lo MAP <= a < YGcfRehidePost.rh_hi MAP LEN -> mem' (w64 a) <> None).
{ intros a Ha. rewrite <- EPB, <- EPE in Ha. rewrite (ZR a Ha). discriminate. }
apply (YA0nR.SRr'_rehide_ret tfibsegs YGcfRehidePost.RZ_cf W2 (shull (MAP, LEN)) (YGcfRehidePost.rh_lo MAP)
  (YGcfRehidePost.rh_hi MAP LEN) HO HA HB8).
- intros a Ha. exact (YGcfRehidePost.rh_interior_RZ MAP LEN a INAPP ltac:(unfold YFg8.LEN in *; lia) Ha).
- exact HW2.
- exact SH.
- exact HS.
- intros p Hp. rewrite <- EPB, <- EPE. exact (proj1 (MG p Hp)).
- apply (YA0nH.SRrG_ret tfibsegs (YA0nH.wle' tfibsegs YGcfRehidePost.RZ_cf) (YA0nH.wle'_refl tfibsegs YGcfRehidePost.RZ_cf)).
  cbv beta. cbn [snd] in *. exists regs', mem', md'. split; [reflexivity|].
  destruct POST as (PAR & PLL & PWLE & PREG & PIO & PFR & PPR).
  split.
  { split.
    { exact (REHIDE W2 mem' md' (mkSec (sm_len sm) (sm_size sm) false) HO HA HB8 SEC2 eq_refl SREAL INAPP eq_refl eq_refl M1F M2
        (junk_segs B ly TB) HW2 PAR NZ). }
    split; [exact PLL|].
    split.
    { intros a Ha. cbn [YA0nR.wrehide w_H] in Ha. unfold YA0nR.H_rehide in Ha. apply orb_true_iff in Ha as [Ha|Ha]; [left; exact Ha|right].
      unfold YA0nR.in_ivb in Ha. apply andb_true_iff in Ha as [Q1 Q2]. apply Z.leb_le in Q1. apply Z.ltb_lt in Q2. apply DS. lia. }
    split; [exact PREG|]. split; [exact PIO|].
    split.
    { intros a Ha N1 N2 N3 N4 N5. cbn [YA0nR.wrehide w_H].
      rewrite (aview_rehide_out _ _ _ _ _ a Ha (fun Hr => N5 (DS a Hr))). exact (PFR a Ha N1 N2 N3 N4). }
    intros a Ha. cbn [YA0nR.wrehide w_H]. unfold spZ in Usp, HloCF, Ha.
    apply apresent_rehide_out; [lia | lia | exact (PPR a Ha)]. }
  split; [exact RAW|]. split; [exact ERR|]. split; [exact MN|].
  split.
  { intros a Ha PUa NK. cbn [YA0nR.wrehide w_H].
    assert (NI : ~ (YGcfRehidePost.rh_lo MAP <= a < YGcfRehidePost.rh_hi MAP LEN)) by (pose proof (PUHI a PUa); lia).
    rewrite (aview_rehide_out _ _ _ _ _ a Ha NI). exact (AV a Ha PUa NK). }
  split; [exact PU|]. split; [exact CI | exact AO].
Qed.
End e.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Without the cache flag (DMrcSecNf's route, under the re-hide).                                                   *)

(* The munmap node (aok (KMunmapSec _ _) z is z = 1, whatever the snapshot) under amreal': its realization at snapshot
   s1 and answer v1 gives the one at s2 and v2, with the post at v1 (DMrcSecNf.amreal_unmap1 over amreal'). *)
Lemma amreal'_unmap1 {R} : forall (segs : list Segment) (RZ : Z -> Prop) r len (s1 s2 : astate) (v1 v2 : R) W c
  (Q : R -> world segs -> config -> Prop),
  YG0dH.amreal' segs RZ (IAsk (KMunmapSec r len) s1 (fun _ => IRet v1)) W c Q ->
  YG0dH.amreal' segs RZ (IAsk (KMunmapSec r len) s2 (fun _ => IRet v2)) W c (fun r0 W' c' => r0 = v2 /\ Q v1 W' c').
Proof.
intros segs RZ r len s1 s2 v1 v2 W c Q H. unfold YG0dH.amreal' in *. cbn [YG0dH.amrealG aok] in *.
eapply YA0nH.SRrG_mono; [exact H|]. intros W1 c1 _ (J & nx & bit & sp & i0 & Hn & Ht & Ha & Hs & Hb & Hr & Hz & Hc).
exists J, nx, bit, sp, i0. do 7 (split; [assumption|]).
intros j Hj. eapply YA0nH.SRrG_mono; [exact (Hc j Hj) | intros W' c' _ H1; exact (conj eq_refl H1)].
Qed.

(* The walk's post state at the flag-set state, with the flag of X put back, is the post state at X. *)
Lemma X2v_flag : forall X k r sm i,
  set_cache_inited (st_cache_inited X) (YFg8.X2v (set_cache_inited true X) k r sm i) = YFg8.X2v X k r sm i.
Proof. intros [] k r sm i. reflexivity. Qed.

Section nf.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable ARXsl : Z -> (Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop).
Variable AOX : alayout -> astate -> Z -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Variables NMAXD LMAXD : Z.
Hypothesis NOK : DMwalkIF.nmaxd_ok NMAXD.
Hypothesis LOK : DMwalkIF.lmaxd_ok NMAXD LMAXD.
Hypothesis RCnf : DMrcSecNf.rc_sec_cut_nf_t B ARXr.
Hypothesis RMnf : DMrcSecNf.rc_sec_mapr_nf_t B ARXr.
Hypothesis RSnf : DMrcSecNf.rc_sec_step_nf_g B ARXr ARXsl AOX.
Hypothesis RHD : DMrcReads.rc_head_t DRq.
Hypothesis RMD : DMrcReads.rc_model_t DRq.
Hypothesis RDS : DMwalkIF.drq_sizes DRq NMAXD LMAXD.
Variables (inst : Z) (ly : alayout) (X : astate) (k : chunk) (ks : list chunk) (zs : list Z) (cbp : Z) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (r : nat) (o : Z) (sm : secmap) (i : nat).
Hypothesis PRE : rcc_pre_sec B ARXr inst ly X k cbp W regs mem md.
Hypothesis RX : DRq X (k :: ks) zs.
Hypothesis Hb : ck_beg k = PSec r o.
Hypothesis Hsm : nth_error (st_secs X) r = Some sm.
Hypothesis Hi : nth_error (st_sec_arr X) i = Some r.
Local Notation MAP := (YFg8.MAP ly r).
Local Notation LEN := (YFg8.LEN sm).
Local Notation X2v := (YFg8.X2v X k r sm i).
(* rchunk_sec_rh's premises of the re-hide, the same text (at X; the cf side discharges them). *)
Hypothesis HULL : In (shull (MAP, LEN)) (w_A W).
Hypothesis SREAL : YGcfRehidePost.sec_real sm.
Hypothesis M1 : Forall (zdisjoint (MAP, LEN)) (sec_extents ly X2v).
Hypothesis M2 : kMaxSize + kPage <= LEN.
Hypothesis REHIDE : rc_sec_rehide_t B ARXr ARXsl inst ly X k r sm i.

(* rchunk_sec_rh's post without its st_cache_inited conjunct, with the model part DRq (snd r0) ks zs: the secondary arm
   of MnRecycle.de_rchunk_m_rh_t's post without the flag. *)
Theorem rchunk_sec_rh_nf : YG0dH.amreal' tfibsegs YGcfRehidePost.RZ_cf (recycle_chunk k X) W (cfg_at tfibsegs A_RChunk regs mem md)
  (fun (r0 : unit * astate) (W' : world tfibsegs) (c' : config) => exists regs' mem' md',
   c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
   YGcfRehidePost.acall_post_x_rh B ARXr AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r0) W' regs' mem' md' /\
   acall_raw_x B AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r0) W' regs' mem' md' /\
   ErrnoG.errno_kept B mem mem' /\ MemnormT.memnorm_keep tfibsegs mem mem' /\
   (forall a, 0 <= a < 2 ^ 64 -> YFeuC.puser ly X a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) ->
    aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) /\
   (forall a, YFeuC.puser ly X a -> YFeuC.puser ly (snd r0) a) /\
   DRq (snd r0) ks zs /\ (forall a, AOX ly (snd r0) a -> AOX ly X a)).
Proof.
pose proof (RDS X (k :: ks) zs k RX (or_introl eq_refl)) as [[_ HN] HE].
destruct (RHD X k ks zs RX) as (Hkin & Hst & Hni).
pose proof (RCnf inst ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi Hkin Hst) as (_ & _ & _ & SC).
pose proof (RMnf inst ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi) as (Hidx & _).
pose proof (DMrcSecMun.SMALL B ly X k W regs mem r o sm i SC NMAXD LMAXD LOK HE) as SMALL.
(* the pre at X1 = set_cache_inited true X, over the relation read at the flag of X *)
assert (PRE1 : rcc_pre_x B (DMrcSecNf.ARXu ARXr (st_cache_inited X)) inst ly (set_cache_inited true X) k cbp W regs mem md).
{ destruct PRE as (HA & P). split; [unfold DMrcSecNf.ARXu; rewrite DMrcSecNf.flag_eta; exact HA | split; [reflexivity | exact P]]. }
(* REHIDE at X1 over the relations read at the flag of X: they are ARXr / ARXsl at X2v (X2v_flag); the other premises
   do not read the flag *)
assert (RH1 : rc_sec_rehide_t B (DMrcSecNf.ARXu ARXr (st_cache_inited X)) (fun d => DMrcSecNf.ARXu (ARXsl d) (st_cache_inited X))
  inst ly (set_cache_inited true X) k r sm i).
{ intros W2' mem' md' sm2 HO HA HB8 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.
  cbv beta in H11. unfold DMrcSecNf.ARXu in H11 |- *. rewrite X2v_flag in H11 |- *.
  exact (REHIDE W2' mem' md' sm2 HO HA HB8 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12). }
pose proof (rchunk_sec_rh B TB (DMrcSecNf.ARXu ARXr (st_cache_inited X)) (fun d => DMrcSecNf.ARXu (ARXsl d) (st_cache_inited X))
  (DMrcSecNf.AOXu AOX (st_cache_inited X))
  (DMrcSecNf.RCu B ARXr RCnf _) (DMrcSecNf.RMu B ARXr RMnf _) (DMrcSecNf.RSu_g B ARXr ARXsl AOX RSnf _)
  NMAXD LMAXD NOK LOK inst ly (set_cache_inited true X) k cbp W regs mem md r o sm i PRE1 Hb Hsm Hi HN HE Hst Hni Hkin
  HULL SREAL M1 M2 RH1) as MR.
pose proof (RMD X k ks zs RX) as AP.
rewrite (YFg8.recycle_chunk_sec k X r o sm i (proj2 (mem_chunk_spec _ _) Hkin) Hb Hsm Hidx SMALL) in AP |- *.
rewrite (YFg8.recycle_chunk_sec k (set_cache_inited true X) r o sm i (proj2 (mem_chunk_spec _ _) Hkin) Hb Hsm Hidx SMALL) in MR.
pose proof (amreal'_unmap1 tfibsegs YGcfRehidePost.RZ_cf r (sm_len sm) _ (YFf3.X1 X k) _ (tt, YFg8.X2 (YFf3.X1 X k) r i sm) W _ _ MR) as MU.
pose proof (YG0dHc.amreal'_apost tfibsegs YGcfRehidePost.RZ_cf _ _ W _ _ AP MU) as A.
eapply YG0dH.amreal'_mono; [|exact A]. cbv beta.
intros r0 W' c' [DQ [-> Q1]].
(* X1 differs from X only in the flag: the post at X1 over ARXu / AOXu is the post at X over ARXr / AOX *)
clear - Q1 DQ. destruct X.
destruct Q1 as (regs' & mem' & md' & Hc & HP & HR & HE' & HK & HV & PU & _ & AO).
exists regs', mem', md'.
split; [exact Hc|]. split; [exact HP|]. split; [exact HR|]. split; [exact HE'|]. split; [exact HK|].
split; [exact HV|]. split; [exact PU|]. split; [exact DQ | exact AO].
Qed.
End nf.
End d.
