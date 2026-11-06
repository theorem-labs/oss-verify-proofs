(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DGg3.v (commit 84ee52cd012, file sha256 05a1be877b76) onto omx-clap-core/fuzz_preset's asan-ubsan image (unstripped fuzz_preset.asan-ubsan, sha256 3b5e1a099b53); module paths changed; its 8 image addresses moved by code-verified function pairs (8 port_addr_check 0767e70e074a MAPS predictions, each code one re-derived by the internal file funcpair.py; 0 code pcs the tool read as sizes, by the internal file funcpair.py; 1 the tool cannot place or places wrongly, read out of image B itself), and 1 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10-30: field round 3 part 3 (MP) from proofs/cgif/cgif_file_fuzzer/lib/DGg3.v applied by 3-way (base commit 5034424e29db, theirs e8a7dd66acf2; preset-side hunks kept), module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/AU/DGg3.v, with its module paths, module names, addresses and numbers changed; 10 of its 465 lines of code are new or changed and 13 lines of the source are left out. *)
(* DGg3.v (the NULL arm's walk) at round 3 part 3, over DIfaceRh.DIface_rh: the Hypothesis IF and its field names
   (the di_ prefix renamed to DIfaceRh.dih_) only.  The walk reads no drain or Recycle field; every script is DGg3's.
   For WalkSigDrh's instance at the primed top, whose interface instance is DIfaceRh.DIface_rh (CfF2a's
   YGcfInstFree.diface_rh_cf): a DIface_rh -> DIface projection cannot exist, and a released DIface at drain_body_cf would
   claim the released drain, which a real recycle breaks.
   rule 24: no function proved (kind: restatement of an already proved walk over a weaker interface record). *)
(* The NULL arm of the frame-generic Deallocate contract (DeallocG.dealloc_leaf_raw), over the interface the arms take
   from the allocator relation ARX.

   Ported from cgif_file's released free walk (afree_null, YFg3) with the caller's frame made abstract: the run
   starts at Deallocate's entry (0x318c4) with the virtual register file [DGif0.dregs] (atom 10 = the pointer, 0 here;
   aINST = 11 = this; aBP = 12 = the trace buffer; aSO = 13 = the stack object), the seed is DGgn.SS0, the walk is
   DGh1.segN to the early [ret], and the leaf's ARX / lpost come from the interface's NULL post, its frame clause
   from the owned set, its path clause from AGif0n.amreal_apath_gflag.

   C5: DeallocG's trace premise is [U tr S], the interface is DGif0.DIface over
   B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq, and DeallocG.dealloc_post_raw has a raw frame clause
   next to dealloc_post's aview one (proved here from the arm's raw memory facts, the aview clause following by
   YF0x.aview_same). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o YG0h.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1w AE3d AFeq AFex DGbase DGgn DGfx DGh1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AllocG DeallocG AGif0n AGif0reply DMspec DGif0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGif2reply ImgBaseDG DGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AFfu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ErrnoG DGleafE.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require DIfaceRh.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma wvb_self : forall md, with_vm_backing (m_vm_lazy md) (m_vm_materialized md) md = md.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma same_io_wvb : forall md mat, same_io md (with_vm_backing (m_vm_lazy md) mat md).
Proof. intros md mat. unfold same_io. destruct md; cbn; repeat split; reflexivity. Qed.
(* A byte of a value in memory, off the image, is the raw byte. *)
Lemma mbyte_off_raw : forall (H : word -> bool) (mem : word -> option byte) a b, off_img a ->
mbyte tfibsegs (mrestrict H mem) a = Some b -> mem (Z_to_bv 64 a) = Some b.
Proof.
intros H mem a b Ha Hb. unfold mbyte, mrestrict in Hb.
destruct (H (Z_to_bv 64 a)) eqn:HH; [rewrite (seg_rom_none_off a Ha) in Hb; discriminate|].
destruct (mem (Z_to_bv 64 a)) eqn:E; [exact Hb | rewrite (seg_rom_none_off a Ha) in Hb; discriminate].
Qed.

Section b.
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
Variable MP : (word -> option byte) -> Prop.
Hypothesis IF : DIfaceRh.DIface_rh B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP.

Section c.
Variables (inst so bp : Z) (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (n : Z) (tr : list Z).
Hypothesis PRE : DeallocG.dealloc_pre tfibsegs B U ARX rpre fpre 1 inst so bp ly S W regs mem md PNull n tr.
Let regs0 : bvmap 5 word := dregs regs 0 inst bp so.
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation m0 := (mrestrict (w_H W) mem).
Local Notation E0 := (DGgn.E0 ly regs0 tr).
Local Notation LENv := (DGgn.LENv tr).

Lemma PREd : ARX inst ly S W mem md /\ rpre S n /\ YK0s.ret_ok (getr regs 1) /\ 4096 <= bv_unsigned (getr regs 1) /\
sp0 mod 16 = 0 /\ ly_stk_lo ly + DFSTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\
(forall a, sp0 - DFSTACK <= a < sp0 -> apresent (w_H W) mem a) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 TFIB_TP /\ getr regs 10 = w64 inst /\ getr regs 11 = w64 0 /\
getr regs 12 = w64 0 /\ getr regs 13 = w64 0 /\ getr regs 14 = w64 so /\ getr regs 15 = w64 1 /\
sp0 <= so /\ so + 16 <= ly_stk_hi ly /\ so mod 8 = 0 /\ sp0 <= bp /\ bp + 8 * 30 <= ly_stk_hi ly /\ bp mod 8 = 0 /\
(1 <= length tr <= 30)%nat /\ val_mem tfibsegs m0 so 8 bp /\ val_mem tfibsegs m0 (so + 8) 8 (Z.of_nat (length tr)) /\
(forall i, (i < length tr)%nat -> val_mem tfibsegs m0 (bp + 8 * Z.of_nat i) 8 (nth i tr 0)).
Proof.
destruct PRE as (HARX & HRP & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & Hpres & Hgp & Htp & Hr10 & Hr11 & Hr12 & Hr13 & Hr14 & Hr15 &
Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htrlen & PSO & PLEN & PBUF & _).
unfold spZ, raZ, DFSTACK_G in *. rewrite (ts_tp B TS) in Htp. fold sp0 in Hal, Hlo, Hbot, Hhi, Hpres, Hso1, Hbp1.
unfold DFSTACK. repeat (split; [first [assumption | exact Hr11] |]). exact PBUF.
Qed.

Lemma LOv : dview_n B W ly inst mem.
Proof. destruct PREd as (HARX & HRP & _). exact (DIfaceRh.dih_view_n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md n HARX HRP). Qed.
Lemma IOv : inst_ok inst.
Proof. destruct PREd as (HARX & _). exact (DIfaceRh.dih_inst _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md HARX). Qed.

(* The layout's placement facts (YFf0.HIGH, from the layout alone). *)
Lemma HIGH : kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ zone3 (ly_Q ly) (kPtrArrayResv) /\ ly_Q ly + kPtrArrayResv <= ASAN_CEIL /\
zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\ zone3 (ly_F ly) (kFakeStackSize) /\ ly_F ly + kFakeStackSize <= ASAN_CEIL /\
zone3 (ly_NB ly) (kNodesBlockSize) /\ ly_NB ly + kNodesBlockSize <= ASAN_CEIL /\ zone3 (ly_SB ly) (kStoreBlockSize) /\ ly_SB ly + kStoreBlockSize <= ASAN_CEIL /\
zone3 (ly_C ly) (256) /\ ly_C ly + 256 <= ASAN_CEIL /\ kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\
ly_prim ly <= ly_space ly /\ ly_space ly + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\ ly_stk_lo ly mod 4096 = 0.
Proof.
pose proof (dn_ly _ _ _ _ _ LOv) as LO. pose proof (dn_img _ _ _ _ _ LOv) as IMG.
pose proof (lo_high _ LO) as IP. unfold in_high in IP. cbn [fst snd] in IP.
pose proof (lo_app _ LO) as HA. pose proof (lo_disj _ LO) as HD.
assert (Z3 : forall i x sz, nth_error (owned_extents ly) i = Some (x, sz) -> 0 <= sz -> zone3 x sz).
{ intros i x sz He Hsz. apply (zone3_intro ly x sz IMG Hsz (Forall_nth_f _ _ i _ HA He)).
assert (L : (i < 8)%nat) by (destruct (Nat.lt_ge_cases i 8) as [X|X]; [exact X|]; assert (X' : nth_error (owned_extents ly) i = None) by (apply nth_error_None; cbn; lia); rewrite X' in He; discriminate).
exact (pairwise_ij_f _ _ i (8 - i) _ _ HD ltac:(unfold static_extents; rewrite nth_error_app1 by (cbn; lia); exact He)
ltac:(unfold static_extents; rewrite nth_error_app2 by (cbn; lia); replace (i + Datatypes.S (8 - i) - length (owned_extents ly))%nat with 1%nat by (cbn; lia); reflexivity)). }
pose proof (Z3 1%nat _ _ eq_refl ltac:(unfold kPtrArrayResv; lia)) as ZQ. pose proof (Z3 2%nat _ _ eq_refl ltac:(unfold kThreadObjSize; lia)) as ZT.
pose proof (Z3 3%nat _ _ eq_refl ltac:(unfold kFakeStackSize; lia)) as ZF. pose proof (Z3 4%nat _ _ eq_refl ltac:(unfold kNodesBlockSize; lia)) as ZNB.
pose proof (Z3 5%nat _ _ eq_refl ltac:(unfold kStoreBlockSize; lia)) as ZSB. pose proof (Z3 6%nat _ _ eq_refl ltac:(lia)) as ZC. clear Z3 HA HD.
pose proof ZQ as (ZQ1 & ZQ2 & _). pose proof ZT as (ZT1 & ZT2 & _). pose proof ZF as (ZF1 & ZF2 & _). pose proof ZNB as (ZNB1 & ZNB2 & _). pose proof ZSB as (ZSB1 & ZSB2 & _). pose proof ZC as (ZC1 & ZC2 & _).
pose proof (lo_top _ LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof (lo_space_in _ LO) as [S1 S2].
unfold page_aligned in *. splits; try assumption; try lia.
Qed.
Lemma SX : forall i j x y, nth_error (static_extents ly) i = Some x -> nth_error (static_extents ly) j = Some y -> i <> j -> zdisjoint x y.
Proof.
pose proof (dn_ly _ _ _ _ _ LOv) as LO.
intros i j x y Hi Hj Hne. destruct (Nat.lt_ge_cases i j).
- exact (pairwise_nth zdisjoint _ i j x y (lo_disj _ LO) Hi Hj H).
- apply zdisjoint_sym. apply (pairwise_nth zdisjoint _ j i y x (lo_disj _ LO) Hj Hi). lia.
Qed.

Lemma cell_lit : forall a (w : nat) x, cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum x))) -> val_mem tfibsegs m0 a w x.
Proof.
intros a w x E. apply (cell_holds_val_mem B ly (w_H W) mem (ANum a) w (ANum x)).
apply (proj1 (Forall_forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (as_const B ly)) (dn_const _ _ _ _ _ LOv)).
rewrite (ts_const B TS ly). exact (cell_lookup_In _ _ _ E).
Qed.
Lemma cell_sym : forall e (w : nat) e', cell_lookup (Tfib_const ly) e = Some (ACell e w (AV e')) -> val_mem tfibsegs m0 (aeval B ly e) w (aeval B ly e').
Proof.
intros e w e' E. apply (cell_holds_val_mem B ly (w_H W) mem e w e').
apply (proj1 (Forall_forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (as_const B ly)) (dn_const _ _ _ _ _ LOv)).
rewrite (ts_const B TS ly). exact (cell_lookup_In _ _ _ E).
Qed.

(* The atoms of E0. *)
Lemma Usp : 0 <= sp0 < 2 ^ 64.
Proof. unfold sp0. apply u64_range. Qed.
Lemma STK64 : ly_stk_hi ly <= kHighMemEnd /\ kHighMemBeg <= ly_stk_lo ly.
Proof. pose proof HIGH as H. tauto. Qed.
Lemma R1 : getr regs0 1 = getr regs 1. Proof. unfold regs0. apply dregs_other; intros X; vm_compute in X; discriminate X. Qed.
Lemma R2 : getr regs0 2 = getr regs 2. Proof. unfold regs0. apply dregs_other; intros X; vm_compute in X; discriminate X. Qed.
Lemma R10 : getr regs0 10 = w64 0. Proof. unfold regs0. apply dregs_10. Qed.
Lemma R11 : getr regs0 11 = w64 inst. Proof. unfold regs0. apply dregs_11. Qed.
Lemma R12 : bv_unsigned (getr regs0 12) = bp.
Proof.
unfold regs0. rewrite dregs_12. apply w64_unsigned. pose proof PREd as (_ & _ & _ & _ & _ & Hlo & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hb1 & Hb2 & _).
pose proof STK64 as [K1 K2]. pose proof Usp. unfold kHighMemEnd, kHighMemBeg in *. lia.
Qed.
Lemma R13 : bv_unsigned (getr regs0 13) = so.
Proof.
unfold regs0. rewrite dregs_13. apply w64_unsigned. pose proof PREd as (_ & _ & _ & _ & _ & Hlo & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hs1 & Hs2 & _).
pose proof STK64 as [K1 K2]. pose proof Usp. unfold kHighMemEnd, kHighMemBeg in *. lia.
Qed.
Lemma EI : bv_unsigned (getr regs0 11) = inst.
Proof. rewrite R11. apply w64_unsigned. pose proof IOv as (I1 & I2 & _). lia. Qed.
Lemma ESP : bv_unsigned (ew E0 2) = sp0. Proof. rewrite (DGgn.E2 ly regs0 tr), R2. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The seed.                                                                                                        *)
Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Lemma val_mem_writable : forall a (w : nat) v o, val_mem tfibsegs m0 a w v -> a <= o < a + Z.of_nat w -> off_img o -> writable_at tfibsegs m0 o.
Proof. intros a w v o Hv Ho Ha. apply AFfu.vis_writable_off; [exact Ha|]. replace o with (a + (o - a)) by lia. eapply AFfu.val_mem_vis; [exact Hv | lia]. Qed.
Lemma chunk_lit : forall a (w : BinNums.N) x, val_mem tfibsegs m0 a (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 0 (YP09.mkChunk a (CVal w (SLit x))).
Proof. intros a w x Hm Hx Hw. eapply chunk_ok_val; [reflexivity | exact Hx | exact Hw | rewrite Z.add_0_l; exact Hm]. Qed.
Lemma chunk_lit_at : forall base a (w : BinNums.N) x, val_mem tfibsegs m0 (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 base (YP09.mkChunk a (CVal w (SLit x))).
Proof. intros base a w x Hm Hx Hw. eapply chunk_ok_val; [reflexivity | exact Hx | exact Hw | exact Hm]. Qed.
Lemma chunk_atom : forall base a (w : BinNums.N) k d x, ew E0 k = w64 (x - d) -> 0 <= x - d < 2 ^ 64 ->
val_mem tfibsegs m0 (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 base (YP09.mkChunk a (CVal w (SOff k d))).
Proof.
intros base a w k d x Hk Hr Hm Hx Hw. eapply chunk_ok_val; [| exact Hx | exact Hw | exact Hm].
cbn [sv_denot]. rewrite Hk. unfold w64. rewrite Zbv_add_unsigned. f_equal. lia.
Qed.
Local Ltac lit_region :=
reg_intro; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
repeat (apply Forall_cons; [apply chunk_lit; [apply cell_lit; vm_compute; reflexivity | cbn; lia | cbn; lia] |]); apply Forall_nil.

Lemma REG0_ok : Forall (region_ok tfibsegs E0 m0) DGgn.REG0.
Proof.
pose proof HIGH as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hF1 & hF2 & hNB1 & hNB2 & hSB1 & hSB2 & hC1 & hC2 & hS1 & hS2 & hSP1 & hSP2 & _). unfold zone3 in hQ1, hT1, hF1, hNB1, hSB1, hC1.
pose proof (lo_top ly (dn_ly _ _ _ _ _ LOv)) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof PREd as (_ & _ & _ & _ & _ & Hlo & Hbot & Hhi & HPRES & _ & _ & _ & _ & _ & _ & _ & _ & Hs1 & Hs2 & Hs3 & Hb1 & Hb2 & Hb3 & Htrlen & PSO & PLEN & _).
pose proof IOv as (IO1 & IO2 & IO3). pose proof (dn_inst _ _ _ _ _ LOv) as (HI1 & HI2). pose proof (dn_tsd _ _ _ _ _ LOv) as HTSD.
change (ly_tsd ly = TFIB_TSD) in HTSD.
pose proof (dn_unw _ _ _ _ _ LOv) as HUNW.
pose proof Usp as U2.
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kHighShadowBeg in hP1, hP2, hQ1, hQ2, hT1, hT2, hF1, hF2, hNB1, hNB2, hSB1, hSB2, hC1, hC2, hS1, hS2, hSP1, hSP2, T2, T4, T7.
unfold DGgn.REG0, DGgn.TAILG, R_soG, R_scrG, R_slotG, ilit8, flit1, flit4, flit8, flits8, fatom8.
cbn [map combine seq length Z.of_nat Pos.of_succ_nat Pos.succ fst snd Z.mul Z.add Pos.mul Pos.add].
unfold aSB, aSHB, aC, aT, aTOP, aINST, aSO, aBP, aLEN.
(* the stack object at aSO: the buffer pointer and the trace length *)
apply Forall_cons.
{ reg_intro. rewrite (DGgn.Er ly regs0 tr 13 13%bv eq_refl), R13.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply (chunk_atom so 0 8 12%nat 0 bp);
[ rewrite Z.sub_0_r, (DGgn.Er ly regs0 tr 12 12%bv eq_refl); unfold w64; rewrite <- R12; symmetry; apply Z_to_bv_bv_unsigned
| lia | rewrite Z.add_0_r; exact PSO | change (8 * Z.of_N 8) with 64; lia | cbn; lia ].
- apply (chunk_atom so 8 8 36%nat 0 (Z.of_nat (length tr))); [rewrite Z.sub_0_r; reflexivity | lia | exact PLEN | change (8 * Z.of_N 8) with 64; lia | cbn; lia]. }
(* the scratch window below the entry sp *)
apply Forall_cons.
{ apply (region_ok_stack tfibsegs E0 m0 2 sp0 (- DFSTACK)); [exact ESP | unfold DFSTACK in *; lia | lia |].
intros a Ha. apply apresent_writable; [unfold TFIB_IMG_END, DFSTACK in *; lia | apply HPRES; exact Ha]. }
(* the two empty slots *)
apply Forall_cons. { reg_intro. rewrite ESP. split; [lia|]. split; [lia|]. split; [intros o Ho; lia | apply Forall_nil]. }
apply Forall_cons. { reg_intro. rewrite ESP. split; [lia|]. split; [lia|]. split; [intros o Ho; lia | apply Forall_nil]. }
do 11 (apply Forall_cons; [lit_region|]).
apply Forall_cons. { reg_intro. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom 0 _ 8 40%nat 0 SHADOW_OFF); [reflexivity | unfold SHADOW_OFF; lia | | unfold SHADOW_OFF; cbn; lia | cbn; lia].
rewrite Z.add_0_l. apply cell_lit. vm_compute. reflexivity. }
do 11 (apply Forall_cons; [lit_region|]).
(* the instance's two quarantine fields *)
apply Forall_cons. { reg_intro. rewrite (DGgn.Er ly regs0 tr 11 11%bv eq_refl), EI. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply chunk_lit_at; [exact HI1 | cbn; lia | cbn; lia]. }
apply Forall_cons. { reg_intro. rewrite (DGgn.Er ly regs0 tr 11 11%bv eq_refl), EI. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply chunk_lit_at; [exact HI2 | cbn; lia | cbn; lia]. }
apply Forall_cons. { reg_intro. unfold TFIB_TP. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
apply chunk_lit; [| unfold TFIB_TSD; cbn; lia | cbn; lia].
replace (6132848 - 88) with (aeval B ly (ATp (-88))) by (cbn; rewrite (ts_tp B TS); reflexivity).
replace TFIB_TSD with (aeval B ly (ATsd 0)) by (cbn; rewrite HTSD; unfold TFIB_TSD; lia). apply cell_sym. vm_compute. reflexivity. }
apply Forall_cons. { reg_intro. unfold TFIB_TSD. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom 0 _ 8 33%nat 0 (ly_C ly)); [rewrite (DGgn.EaC ly regs0 tr); unfold w64; f_equal; lia | lia | | cbn; lia | cbn; lia].
rewrite Z.add_0_l. replace 6268952 with (aeval B ly (ATsd 0)) by (cbn; rewrite HTSD; reflexivity).
replace (ly_C ly) with (aeval B ly (AC 0)) by (cbn; lia). apply cell_sym. vm_compute. reflexivity. }
apply Forall_cons. { reg_intro. rewrite (DGgn.EaC ly regs0 tr). unfold w64. rewrite unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply chunk_lit_at; [| cbn; lia | cbn; lia]. replace (ly_C ly + 8) with (aeval B ly (AC 8)) by reflexivity. apply (cell_sym (AC 8) 4 (ANum 0)). vm_compute. reflexivity.
- apply (chunk_atom _ _ 8 32%nat 0 T); [rewrite (DGgn.EaT ly regs0 tr); unfold w64; f_equal; lia | lia | | cbn; lia | cbn; lia].
replace (ly_C ly + 152) with (aeval B ly (AC 152)) by reflexivity. replace T with (aeval B ly (AT 0)) by (cbn; lia).
apply cell_sym. vm_compute. reflexivity. }
apply Forall_cons. { reg_intro. rewrite (DGgn.EaT ly regs0 tr). unfold w64. rewrite unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
- apply (chunk_atom _ _ 8 33%nat 0 (ly_C ly)); [rewrite (DGgn.EaC ly regs0 tr); unfold w64; f_equal; lia | lia | | cbn; lia | cbn; lia].
replace (ly_T ly + 0) with (aeval B ly (AT 0)) by (cbn; lia). replace (ly_C ly) with (aeval B ly (AC 0)) by (cbn; lia). apply cell_sym. vm_compute. reflexivity.
- apply (chunk_atom _ _ 8 35%nat 0 (ly_top ly)); [rewrite (DGgn.EaTOP ly regs0 tr); unfold w64; f_equal; lia | lia | | cbn; lia | cbn; lia].
replace (ly_T ly + 8) with (aeval B ly (AT 8)) by (cbn; lia). replace (ly_top ly) with (aeval B ly (ATop 0)) by (cbn; lia). apply cell_sym. vm_compute. reflexivity.
- apply (chunk_atom _ _ 8 35%nat (- kStackSpan) (ly_top ly - kStackSpan)); [rewrite (DGgn.EaTOP ly regs0 tr); unfold w64; f_equal; lia | unfold kStackSpan; lia | | unfold kStackSpan; cbn; lia | cbn; lia].
replace (ly_T ly + 16) with (aeval B ly (AT 16)) by (cbn; lia). replace (ly_top ly - kStackSpan) with (aeval B ly (ATop (- kStackSpan))) by (cbn; lia).
apply cell_sym. vm_compute. reflexivity.
- apply chunk_lit_at; [| cbn; lia | cbn; lia]. replace (ly_T ly + 40) with (aeval B ly (AT 40)) by (cbn; lia). apply (cell_sym (AT 40) 1 (ANum 0)). vm_compute. reflexivity. }
apply Forall_cons; [|apply Forall_nil]. { reg_intro. rewrite (DGgn.EaT ly regs0 tr). unfold w64. rewrite unsigned_lit_small by lia. unfold t_unwinding.
unfold t_unwinding in HUNW.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (val_mem_writable _ _ _ _ HUNW); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; [lia|].
cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ho. apply (zone3_off_img _ _ _ hT1). unfold kThreadObjSize. lia. }
apply Forall_cons; [|apply Forall_nil]. apply chunk_lit_at; [exact HUNW | cbn; lia | cbn; lia]. }
Qed.

Lemma EaSO : ew E0 13 = w64 so.
Proof. rewrite (DGgn.Er ly regs0 tr 13 13%bv eq_refl). unfold w64. rewrite <- R13. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma EaBP : ew E0 12 = w64 bp.
Proof. rewrite (DGgn.Er ly regs0 tr 12 12%bv eq_refl). unfold w64. rewrite <- R12. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma EaINST : ew E0 11 = w64 inst.
Proof. rewrite (DGgn.Er ly regs0 tr 11 11%bv eq_refl). exact R11. Qed.
Lemma ESPw : ew E0 2 = w64 sp0.
Proof. rewrite (DGgn.E2 ly regs0 tr), R2. unfold sp0, w64. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma PAIRS_ok : pairwise_disjoint E0 DGgn.REG0.
Proof.
pose proof HIGH as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hF1 & hF2 & hNB1 & hNB2 & hSB1 & hSB2 & hC1 & hC2 & hS1 & hS2 & hSP1 & hSP2 & _).
unfold zone3 in hQ1, hT1, hF1, hNB1, hSB1, hC1.
pose proof PREd as (_ & _ & _ & _ & _ & S1 & _ & S2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hso1 & Hso2 & _).
pose proof IOv as (IO1 & IO2 & _).
pose proof (SX 2 6 _ _ eq_refl eq_refl ltac:(lia)) as DCT.
pose proof (SX 6 8 _ _ eq_refl eq_refl ltac:(lia)) as DCS.
pose proof (SX 2 8 _ _ eq_refl eq_refl ltac:(lia)) as DTS.
unfold zdisjoint in DCT, DCS, DTS. cbn [fst snd] in DCT, DCS, DTS.
pose proof Usp as Usp.
apply pairwise_disjoint_of_extents. unfold DGgn.REG0, DGgn.TAILG, R_soG, R_scrG, R_slotG, ilit8, flit1, flit4, flit8, flits8, fatom8, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val length Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Z.add Pos.mul Pos.add].
unfold aSB, aSHB, aC, aT, aTOP, aSO, aINST.
rewrite EaSO, EaINST, ESPw, (DGgn.EaT ly regs0 tr), (DGgn.EaC ly regs0 tr). unfold w64.
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, DFSTACK in *.
rewrite !unsigned_lit_small by lia.
clear - S1 S2 hT1 hT2 hC1 hC2 hS1 hS2 hSP1 hSP2 hP1 hP2 Usp DCT DCS DTS CR CR0 Hso1 Hso2 IO1 IO2.
unfold TFIB_TP, TFIB_TSD, t_unwinding in *. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in hT1, hC1.
repeat split;
first [ clear DCT DCS DTS hT1 hC1; lia
| clear - hT1 CR0; lia
| clear - hC1 CR0; lia
| clear - hC1 hC2 hT1 hT2 DCT; lia
| clear - hC1 hC2 S1 S2 hS1 hS2 Usp Hso1 Hso2 DCS; lia
| clear - hT1 hT2 S1 S2 hS1 hS2 Usp Hso1 Hso2 DTS; lia
| clear - hT1 IO1 IO2 CR0; lia
| clear - hC1 IO1 IO2 CR0; lia ].
Qed.

Lemma FACTS_ok : facts_ok E0 DGgn.FFG.
Proof.
pose proof HIGH as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hF1 & hF2 & hNB1 & hNB2 & hSB1 & hSB2 & hC1 & hC2 & hS1 & hS2 & hSP1 & hSP2 & _).
unfold zone3 in hQ1, hT1, hF1, hNB1, hSB1, hC1.
pose proof (lo_top ly (dn_ly _ _ _ _ _ LOv)) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof PREd as (_ & _ & _ & _ & Hal & S1 & _ & S2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htrlen & _).
pose proof IOv as (IO1 & IO2 & IO3).
pose proof (lo_space_al ly (dn_ly _ _ _ _ _ LOv)) as SAL. pose proof (lo_T_al ly (dn_ly _ _ _ _ _ LOv)) as TAL. pose proof (lo_C_al ly (dn_ly _ _ _ _ _ LOv)) as CAL.
unfold page_aligned in TAL, T3.
pose proof Usp as Usp.
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kHighShadowBeg, DFSTACK in
hP1, hP2, hQ1, hQ2, hT1, hT2, hF1, hF2, hNB1, hNB2, hSB1, hSB2, hC1, hC2, hS1, hS2, hSP1, hSP2, S1, S2, T2, T4, T7.
assert (AF : forall k X lo hi al, ew E0 k = w64 X -> 0 <= X < 2 ^ 64 -> lo <= X <= hi -> X mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E0 k (mkAF lo hi al)).
{ clear. intros k X lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by exact HX. repeat split; lia. }
unfold facts_ok, DGgn.FFG, DGgn.FFN, frame_facts. cbn [f_atoms f_conds f_alias tl app atoms_ok conds_ok alias_ok].
split; [|split; exact I].
unfold aSB, aSHB, aC, aT, aTOP, aLEN, aIM, aINST, aSO, aBP.
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, DFSTACK.
split. { apply (AF 2%nat sp0); [exact ESPw| | | |]. all: clear - CR0 Usp S1 S2 hS1 hS2 T4 Hal; first [lia | change (2 ^ 4) with 16; exact Hal]. }
split. { apply (AF 11%nat inst); [exact EaINST| | | |]. all: clear - IO1 IO2 IO3; first [lia | change (2 ^ 3) with 8; exact IO3]. }
split. { apply (AF 13%nat so); [exact EaSO| | | |]. all: clear - CR0 Usp S1 S2 hS1 hS2 T4 Hso1 Hso2 Hso3; first [lia | change (2 ^ 3) with 8; exact Hso3]. }
split. { apply (AF 12%nat bp); [exact EaBP| | | |]. all: clear - CR0 Usp S1 S2 hS1 hS2 T4 Hbp1 Hbp2 Hbp3; first [lia | change (2 ^ 3) with 8; exact Hbp3]. }
split. { apply (AF 32%nat T); [exact (DGgn.EaT ly regs0 tr)| | | |]. all: clear - CR0 hT1 hT2 TAL; first [lia | exact TAL]. }
split. { apply (AF 33%nat (ly_C ly)); [exact (DGgn.EaC ly regs0 tr)| | | |]. all: clear - CR0 hC1 hC2 CAL; first [lia | exact CAL]. }
split. { apply (AF 34%nat SB); [exact (DGgn.EaSB ly regs0 tr)| | | |]. all: clear - CR0 hSP1 hSP2 hP1 hP2 SAL; first [lia | exact SAL]. }
split. { apply (AF 35%nat (ly_top ly)); [exact (DGgn.EaTOP ly regs0 tr)| | | |]. all: clear - CR0 T1 T2 T3 T4 T7 hS1; unfold ly_bot, kStackSpan in *; first [lia | exact T3]. }
split. { apply (AF 36%nat LENv); [exact (DGgn.EaLEN ly regs0 tr)| | | |]. all: clear - Htrlen; unfold DGgn.LENv; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 37%nat 0xa72c0); [exact (DGgn.EaIM ly regs0 tr)| | | |]. all: clear; first [lia | reflexivity]. }
split; [|exact I]. { apply (AF 40%nat SHADOW_OFF); [exact (DGgn.EaSHB ly regs0 tr)| | | |]. all: clear; unfold SHADOW_OFF; first [lia | reflexivity]. }
Qed.

(* The machine registers at Deallocate's entry are REGS_GN over E0. *)
Lemma HUo : forall r : bv 5, bv_unsigned r <> 10 -> bv_unsigned r <> 11 -> bv_unsigned r <> 12 -> bv_unsigned r <> 13 -> getr regs r = getr regs0 r.
Proof. intros r H10 H11 H12 H13. unfold regs0. symmetry. apply dregs_other; assumption. Qed.
Lemma HU10 : getr regs 10 = getr regs0 11. Proof. rewrite R11. pose proof PREd as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma HU14 : getr regs 14 = getr regs0 13.
Proof. unfold regs0. rewrite dregs_13. pose proof PREd as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma HU11 : getr regs 11 = w64 0. Proof. pose proof PREd as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma HU12 : getr regs 12 = w64 0. Proof. pose proof PREd as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma HU13 : getr regs 13 = w64 0. Proof. pose proof PREd as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma HU15 : getr regs 15 = w64 1.
Proof. pose proof PREd as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma HUtp : getr regs 4 = w64 TFIB_TP. Proof. pose proof PREd as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Local Ltac reg_atom :=
cbn -[Z_to_bv getr];
repeat match goal with |- context [Z.of_nat ?k] => let y := eval cbv in (Z.of_nat k) in change (Z.of_nat k) with y end;
rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity.
Local Ltac reg_case :=
match goal with |- _ = sv_denot ?E (sr_get ?sr ?r) => let x := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with x end;
first
[ transitivity (Z_to_bv 64 0); [apply getr_zero | reflexivity]
| transitivity (getr regs0 11%bv); [exact HU10 | reg_atom]
| transitivity (getr regs0 13%bv); [exact HU14 | reg_atom]
| transitivity (w64 0); [exact HU11 | reflexivity]
| transitivity (w64 0); [exact HU12 | reflexivity]
| transitivity (w64 0); [exact HU13 | reflexivity]
| transitivity (w64 1); [exact HU15 | reflexivity]
| transitivity (w64 TFIB_TP); [exact HUtp | reflexivity]
| rewrite HUo by (let Hc := fresh "Hc" in intro Hc; vm_compute in Hc; discriminate Hc); reg_atom ].
Lemma REGS_ok : regs_ok E0 REGS_GN regs.
Proof.
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [reg_case|]).
destruct Hr.
Qed.

Lemma SEED_ok : st_ok tfibsegs E0 DGgn.SS0 (restrict (w_H W) (mkst regs (w64 A_Deallocate) mem (seg_rom tfibsegs))).
Proof.
rewrite restrict_mkst_fx. unfold DGgn.SS0, w64, st_ok.
cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]). split; [exact REGS_ok|]. split; [|exact FACTS_ok].
split; [vm_compute; reflexivity|]. split; [exact REG0_ok | exact PAIRS_ok].
Qed.

Lemma FH_ok : DGgn.free_hyps W ly regs0 mem tr regs.
Proof.
pose proof PREd as (HARX & HRP & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & Hpres & Hgp & Htp & Hr10 & Hr11 & Hr12 & Hr13 & Hr14 & Hr15 &
Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htrlen & PSO & PLEN & PBUF).
pose proof IOv as (IO1 & IO2 & IO3).
constructor.
- exact (dn_ly _ _ _ _ _ LOv).
- exact (dn_img _ _ _ _ _ LOv).
- exact R10.
- unfold regs0. rewrite dregs_other by (intros X; vm_compute in X; discriminate X). exact Htp.
- rewrite R1. exact Hra.
- rewrite R1. exact Hra4096.
- rewrite R2. fold sp0. unfold DFSTACK in *. lia.
- unfold DGgn.AL. rewrite R2. exact Hal.
- exact Htrlen.
- rewrite R13, R2. fold sp0. lia.
- rewrite R12, R2. fold sp0. lia.
- rewrite EI. lia.
- exact (dn_ial _ _ _ _ _ LOv).
- exact SEED_ok.
- rewrite R12. exact PBUF.
Qed.

(* The walk: the tick, then DGh1.segN from the seed to the early [ret]. *)
Lemma null_main : amreal tfibsegs (ft PNull tr S) W (cfg_at tfibsegs 0x318c4 regs mem md)
(fun r W' c' => r = (tt, dtick S) /\ DGh1.at_RETN W ly regs0 mem md W' c').
Proof.
pose proof PREd as (HARX & HRP & _).
rewrite (DIfaceRh.dih_shape_n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF n tr S HRP). cbn [ret amreal].
unfold cfg_at. rewrite <- (wvb_self md) at 1.
eapply SRr_mono; [exact (DGh1.segN W ly regs0 mem md tr regs (m_vm_materialized md) FH_ok) |].
intros W' c' _ HR. split; [reflexivity | exact HR].
Qed.

Lemma val_mem_aview : forall H m a (w : nat) v kk, val_mem tfibsegs (mrestrict H m) a w v -> (kk < w)%nat ->
aview tfibsegs H m (a + Z.of_nat kk) = Some (YG0f.le_byte v w kk).
Proof.
intros H m a w v kk Hv Hk. unfold aview. rewrite (Hv kk Hk). cbn [option_map]. change (YG0f.le_byte v w kk) with (YO0f.le_byte v w kk). f_equal. apply unsigned_lit_small8.
unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

(* null_arm_c with errno kept, on the raw memory and on the view: the same walk and frame; errno from MEQR (see the
   errno step below), the view from the raw bytes since the walk returns to the world it starts in. *)
Theorem null_arm_c_e : amreal tfibsegs (ft PNull tr S) W (cfg_at tfibsegs 0x318c4 regs mem md)
(DGleafE.dealloc_leaf_raw_ee B ft ARX AOX lpost inst ly S W regs mem md PNull n tr).
Proof.
pose proof PREd as (HARX & HRP & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & _).
pose proof PRE as PRE'. unfold DeallocG.dealloc_pre in PRE'.
do 27 (destruct PRE' as [_ PRE']). destruct PRE' as (HTU & _ & HFP).
pose proof (dn_unw _ _ _ _ _ LOv) as HUNW0. pose proof HIGH as (_ & _ & _ & _ & hT1 & _).
eapply amreal_mono; [| exact (amreal_apath_gflag tfibsegs _ _ _ _ null_main)].
intros r W' c' [[-> HR] HPATH].
destruct HR as (-> & regs' & mem' & mat & -> & RCS & MEQR & UNW & PRES').
rewrite R2 in PRES'. fold sp0 in PRES'.
assert (DM : dmem_n W ly sp0 mem mem').
{ split; [|split; [exact (proj2 MEQR) | split; [exact UNW | exact PRES']]].
  intros x N1 N2 N3. apply (proj1 MEQR x); [| exact N3].
  unfold DGgn.WIN. rewrite R2. fold sp0. intros [X|X]; [exact (N1 X) | exact (N2 X)]. }
destruct (DIfaceRh.dih_post_n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md n tr sp0 mem' mat HARX HRP HFP HTU
  ltac:(unfold DFSTACK, DGbaseC.DFSTACK in *; lia) Hhi Hbot Hal DM HPATH) as [HARX' HLP].
exists ly, regs', mem', (with_vm_backing (m_vm_lazy md) mat md).
split. { unfold cfg_at, raZ, w64. rewrite R1, Z_to_bv_bv_unsigned. reflexivity. }
split.
{ split; [exact HARX'|]. split; [apply layout_le_refl|]. split; [apply wle_refl|].
  split.
  { intros r Hr. assert (HrZ : bv_unsigned (Z_to_bv 5 r) = r).
    { rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 5) with 32. unfold acallee_saved in Hr. apply Z.mod_small. lia. }
    rewrite <- (dregs_other regs 0 inst bp so (Z_to_bv 5 r)) by (rewrite HrZ; unfold acallee_saved in Hr; lia). fold regs0.
    apply RCS. unfold callee_saved. unfold acallee_saved in Hr. exact Hr. }
  split; [apply same_io_wvb|].
  (* the raw frame, from the arm's raw memory facts; the aview clause follows *)
  assert (FRAWn : forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ AOX ly (dtick S) (bv_unsigned x) ->
    ~ ascratch B DeallocG.DFSTACK_G regs (bv_unsigned x) ->
    ~ (PNull <> PNull /\ sptr_addr B ly PNull <= bv_unsigned x < sptr_addr B ly PNull + req_size n) ->
    mem' x = mem x).
  { intros x NO NO' NS NE. assert (Ra : 0 <= bv_unsigned x < 2 ^ 64) by apply u64_range.
    destruct (Z.eq_dec (bv_unsigned x) (ly_T ly + t_unwinding)) as [Ea|Ea].
    - assert (OFF : off_img (bv_unsigned x))
        by (rewrite Ea; apply (zone3_off_img _ _ _ hT1); unfold kThreadObjSize, t_unwinding; lia).
      pose proof (UNW 0%nat ltac:(lia)) as V1. pose proof (HUNW0 0%nat ltac:(lia)) as V2.
      cbn [Z.of_nat] in V1, V2. rewrite Z.add_0_r in V1, V2. rewrite <- Ea in V1, V2.
      assert (Ex : Z_to_bv 64 (bv_unsigned x) = x) by apply Z_to_bv_bv_unsigned.
      rewrite <- Ex. rewrite (mbyte_off_raw _ _ _ _ OFF V1), (mbyte_off_raw _ _ _ _ OFF V2). reflexivity.
    - apply (proj1 MEQR x).
      + unfold DGgn.WIN. rewrite R2. fold sp0. intros [Hs|Hu].
        * apply NS. left. unfold spZ, DeallocG.DFSTACK_G. fold sp0. unfold DFSTACK in Hs. exact Hs.
        * apply Ea. lia.
      + intros Hi. apply NO. exact (DIfaceRh.dih_owned_i _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md _ HARX Hi). }
  split.
  { intros a Ra NO NO' NS NE. apply aview_same.
    assert (Ex : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; exact Ra).
    apply (FRAWn (Z_to_bv 64 a)); rewrite Ex; assumption. }
  split; [exact FRAWn|].
  intros a Ha. unfold spZ, DeallocG.DFSTACK_G in Ha. fold sp0 in Ha. unfold DFSTACK in PRES'. exact (PRES' a Ha). }
(* errno: its 4 bytes are outside MEQR's excluded set (DGgn.WIN, DGgn.IZONE). errno is in the image at TFIB_ERRNO
   (TfibSyms.ts_errno); the stack window is above kHighMemBeg, the unwinding byte is in the thread object, off the
   image (zone3), and IZONE ends below errno. *)
assert (ERR : ErrnoG.errno_kept B mem mem').
{ intros i Hi. pose proof STK64 as [_ K2].
  assert (EB : bv_unsigned (w64 (as_errno B + i)) = TFIB_ERRNO + i)
    by (rewrite (ts_errno _ TS); apply w64_unsigned; unfold TFIB_ERRNO; lia).
  apply (proj1 MEQR).
  - unfold DGgn.WIN. rewrite R2. fold sp0. rewrite EB. intros [Hs|Hu].
    + unfold TFIB_ERRNO, kHighMemBeg, DFSTACK in *. lia.
    + assert (OFF : off_img (TFIB_ERRNO + i))
        by (apply (zone3_off_img _ _ _ hT1); unfold kThreadObjSize, t_unwinding in *; lia).
      unfold off_img, TFIB_IMG_LO, TFIB_IMG_END, TFIB_ERRNO in OFF. lia.
  - unfold DGgn.IZONE. rewrite EB. unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_ERRNO. lia. }
split; [exact ERR|].
split.
{ intros a Ha. apply aview_same. pose proof (ERR (a - as_errno B) ltac:(lia)) as E.
  replace (as_errno B + (a - as_errno B)) with a in E by lia. unfold w64 in E. exact E. }
split; [exact HLP | exact HPATH].
Qed.

Theorem null_arm_c : amreal tfibsegs (ft PNull tr S) W (cfg_at tfibsegs 0x318c4 regs mem md)
(DeallocG.dealloc_leaf_raw tfibsegs B ft ARX AOX lpost inst ly S W regs mem md PNull n tr).
Proof.
eapply amreal_mono; [| exact null_arm_c_e].
intros r W' c' H. exact (ErrnoG.dealloc_leaf_raw_e_raw tfibsegs B ft ARX AOX lpost inst ly S W regs mem md PNull n tr r W' c'
  (DGleafE.leaf_raw_ee_raw_e B ft ARX AOX lpost inst ly S W regs mem md PNull n tr r W' c' H)).
Qed.
End c.

(* The NULL arm of the generic Deallocate statement. *)
Theorem dealloc_null_arm : forall inst so bp ly S W regs mem md p n tr,
DeallocG.dealloc_pre tfibsegs B U ARX rpre fpre 1 inst so bp ly S W regs mem md p n tr -> p = PNull ->
amreal tfibsegs (ft p tr S) W (cfg_at tfibsegs 0x318c4 regs mem md)
(DeallocG.dealloc_leaf_raw tfibsegs B ft ARX AOX lpost inst ly S W regs mem md p n tr).
Proof. intros inst so bp ly S W regs mem md p n tr PRE0 ->. exact (null_arm_c inst so bp ly S W regs mem md n tr PRE0). Qed.

(* dealloc_null_arm with errno kept, on the raw memory and on the view. *)
Theorem dealloc_null_arm_e : forall inst so bp ly S W regs mem md p n tr,
DeallocG.dealloc_pre tfibsegs B U ARX rpre fpre 1 inst so bp ly S W regs mem md p n tr -> p = PNull ->
amreal tfibsegs (ft p tr S) W (cfg_at tfibsegs 0x318c4 regs mem md)
(DGleafE.dealloc_leaf_raw_ee B ft ARX AOX lpost inst ly S W regs mem md p n tr).
Proof. intros inst so bp ly S W regs mem md p n tr PRE0 ->. exact (null_arm_c_e inst so bp ly S W regs mem md n tr PRE0). Qed.
End b.
End a.
About dealloc_null_arm.
