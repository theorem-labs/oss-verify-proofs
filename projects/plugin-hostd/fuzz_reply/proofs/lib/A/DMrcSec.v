(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMrcSec.v (commit 3d8ad2aeb77e, H4 stage B (slack-indexed post relation; DMrcDefs / DGif1Geo split; re-hide head); file sha256 66092c5b3261) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 2 image addresses moved by code-verified function pairs (3 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 1 pcs named in comments; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (lane B1, slice H4; interface DMwalkIF.v at dc3949af11c): the SECONDARY arm of
   __asan::QuarantineCallback::Recycle (0x33e30) over the opaque cut relation [ARXr]: the walk to the munmap
   (DMrcSecMun.WALK), the munmap ecall and the walk to the return (YFg8.plumbing's machine part), and the post of
   MnRecycle.de_rchunk_m_t from the fields DMrcSecReads.rc_sec_cut_t / rc_sec_mapr_t / rc_sec_step_t.
   rule 24: proves function __asan::QuarantineCallback::Recycle (secondary arm), at cgif_file_fuzzer's asan-ubsan image;
   reuse search LOOKUP-B1-drain.txt (sha256 c6e48b676fd5; internal record) (2026-10-29T23:07:48Z exit 0), rule-24 check B1LookupCheck CONFIRM.
   No recycle invariant enters the machine part (rchunk_sec_mach), so a direct caller of the secondary deallocate can use
   it with its own size premises; the model part (rchunk_sec_m) adds MnRecycle's DRq step from DMrcReads.rc_model_t.
   Section m defines rc_mach_sec_g, the machine post over a post relation [ARXp] (acall_post_x over ARXp).  Section e is
   the walk over the step field DMrcSecReads.rc_sec_step_g, whose post relation [ARXp] is indexed by the slack
   (FINx_g / rchunk_sec_mach_g: rc_mach_sec_g at ARXp (YGcfRehidePost.rh_hi MAP LEN - YGcfRehidePost.rh_lo MAP), the
   recycled slot's slack); Section i states rc_mach_sec / FINx / rchunk_sec_mach, their ARXp := fun _ => ARXr
   instances. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Logic.FunctionalExtensionality.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AFew AFeu AFfm AFf3 AFf4 AFff AFgu AFf5 AFgw AFfb AFg8 AFfc AB13.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG08 YG0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseDG AGif2reply DGif0reply DMspec DMiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require DMwalkIF DMrcSecFc DMrcSecGv DMrcSecWalk DMrcSecF6 DMrcSecF7 DMrcSecF9 DMrcSecMun.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ErrnoG MemnormT MemnormLocG MemnormSafereply DMrcReads DMrcSecReads DMrcConst.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfRehidePost.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import DIfaceR DMwalkIF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK0v YFfn YA05 YG0j.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kPtrArrayResv, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, KSTACK, TFIB_IMG_END, kBatchBytes, SHADOW_OFF, TFIB_TP, TFIB_TSD, TFIB_INST, A_ALLOCATOR, o_space, o_rinfo, o_sec, o_sec_chunks, o_sec_reserved, o_sec_n, o_sec_sorted, o_sec_stats, o_sec_mutex, kRegionInfoOff, kLowMemEnd, kChunkHeaderSize, kPage, AFgu.GFRAME, DMrcSecGv.GDEPTH in *.
Ltac splits := repeat match goal with |- _ /\ _ => split end.
Ltac inS := cbn [In]; repeat (first [left; reflexivity | right]).
Ltac numconst_hi := ceil; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kPtrArrayResv, kLowMemEnd, kPage, t_stats, A_ALLOCATOR, TFIB_INST, SHADOW_OFF, kHighShadowBeg, kHighShadowEnd in *.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.
(* The machine part of MnRecycle.de_rchunk_m_t's post (as DMrcPrim.rc_mach), the cut relation at the return ARXp. *)
Section m.
Variable B : asyms.
Variable ARXp : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variables (inst : Z) (ly : alayout) (X : astate) (k : chunk) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Definition rc_mach_sec_g (r0 : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
exists regs' mem' md',
  c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
  acall_post_x B ARXp AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r0) W' regs' mem' md' /\
  acall_raw_x B AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r0) W' regs' mem' md' /\
  ErrnoG.errno_kept B mem mem' /\
  MemnormT.memnorm_keep tfibsegs mem mem' /\
  (forall a, 0 <= a < 2 ^ 64 -> YFeuC.puser ly X a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) ->
   aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) /\
  (forall a, YFeuC.puser ly X a -> YFeuC.puser ly (snd r0) a) /\
  st_cache_inited (snd r0) = true /\ (forall a, AOX ly (snd r0) a -> AOX ly X a).
End m.

Section e.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable ARXp : Z -> (Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop).
Variable AOX : alayout -> astate -> Z -> Prop.
Hypothesis RCs : DMrcSecReads.rc_sec_cut_t B ARXr.
Hypothesis RMs : DMrcSecReads.rc_sec_mapr_t B ARXr.
Hypothesis RSs : DMrcSecReads.rc_sec_step_g B ARXr ARXp AOX.
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
Local Notation MAP := (AFg8.MAP ly r).
Local Notation LEN := (AFg8.LEN sm).
Local Notation nA := (AFg8.nA X).
Local Notation idx := (AFg8.idx i).
Local Notation qi := (AFg8.qi ly i).
Local Notation lst := (AFg8.lst ly X r).
Local Notation own := (AFg8.own X i).
Local Notation vra := (DMrcSecF6.v regs 1%bv).
Local Notation vs0 := (DMrcSecF6.v regs 8%bv).
Local Notation vs1 := (DMrcSecF6.v regs 9%bv).
Local Notation vs2 := (DMrcSecF6.v regs 18%bv).
Local Notation X2v := (AFg8.X2v X k r sm i).
Local Notation W2 := (AFg8.W2 ly W r sm).
(* the post relation at the recycled slot's slack *)
Local Notation ARXq := (ARXp (YGcfRehidePost.rh_hi MAP LEN - YGcfRehidePost.rh_lo MAP)).
Lemma CUT : inst = as_inst B /\ ly_tsd ly = as_tsd B /\ Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (as_const B ly) /\
DMrcSecFc.sec_cut B ly X k W regs mem r o sm i.
Proof. exact (RCs inst ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi Hkin Hst). Qed.
Lemma MAPR : index_of (st_sec_arr X) r 0%nat = Some i /\
In (MAP, MAP + LEN) (w_A W) /\ In (w64 MAP, w64 LEN) (vm_maps (m_vmmaps md)) /\ amwf md /\
(forall PB kk, 0 < kk -> DMrcSecGv.SHAv MAP <= PB -> PB + kk <= DMrcSecGv.SHEv MAP LEN ->
 madvise_dontneed_ok (m_vmmaps md) (Z_to_bv 64 PB) (Z_to_bv 64 kk) = true).
Proof. exact (RMs inst ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi). Qed.
Local Notation SC := (proj2 (proj2 (proj2 CUT))).
Lemma HTSD : ly_tsd ly = TFIB_TSD. Proof. rewrite (proj1 (proj2 CUT)). apply (ts_tsd _ TB). Qed.
Theorem FINx_g : forall regsD memD mat1 c', DMrcSecMun.LINKD ly W regs mem regsD memD ->
DMrcSecGv.at_RET W ly regsD memD MAP LEN idx nA qi lst vra vs0 vs1 vs2 own
  (munmap_model (w64 MAP) (w64 LEN) (with_vm_backing (m_vm_lazy md) mat1 md)) W c' ->
rc_mach_sec_g B ARXq AOX inst ly X k W regs mem md (tt, X2v) W2 c'.
Proof.
intros regsD memD mat1 c' LNK HR.
pose proof HR as HR0.
destruct HR as (_ & regs' & mem' & mat & Ec & CS & CSP & C8 & C9 & C18 & MEQ' & SHD' & PRS & PRS2 & VALS).
set (mdM := munmap_model (w64 MAP) (w64 LEN) (with_vm_backing (m_vm_lazy md) mat1 md)) in *.
rewrite Ec in HR0.
pose proof LNK as LNK0.
destruct LNK as (LSP & LSR & LMEM & LPRES).
pose proof PRE as PRE'. destruct PRE' as (_ & _ & Hra & Hra4 & Hal & HloCF & Hcb1 & Hcb2 & Hcb3 & HPRES & HPRC & HVC & Hgp & Htp & Ha0 & Ha1).
unfold spZ, raZ in *. fold sp0 in Hal, HloCF, Hcb1, HPRES.
assert (SPD : bv_unsigned (getr regsD 2) = sp0) by (rewrite LSP; reflexivity).
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
(* the walk's windows at regsD are the windows at regs *)
assert (W3E : forall a, DMrcSecGv.WIN3 ly regsD MAP LEN qi lst a <-> DMrcSecGv.WIN3 ly regs MAP LEN qi lst a).
{ intros a. unfold DMrcSecGv.WIN3, DMrcSecGv.WIN2, DMrcSecGv.WIN. rewrite SPD. fold sp0. tauto. }
(* off the windows, memory is the call's *)
assert (KEEP : forall x : word, ~ DMrcSecMun.WPRE ly regs (bv_unsigned x) -> ~ DMrcSecGv.WIN3 ly regs MAP LEN qi lst (bv_unsigned x) -> mem' x = mem x).
{ intros x N1 N2. rewrite (MEQ' x) by (rewrite W3E; exact N2). apply LMEM. exact N1. }
cbv zeta in VALS. pose proof VALS as (VMUT & _).
assert (CONST' : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem')) (as_const B ly))
  by exact (DMrcConst.rc_sec_const B TB ly X k W regs mem r o sm i mem' SC HTSD (proj1 (proj2 (proj2 CUT))) KEEP VMUT).
destruct (RSs inst ly X k cbp W regs mem md r o sm i regsD memD mat1 regs' mem' mat PRE Hb Hsm Hi
  (DMrcSecFc.sc_Hk _ _ _ _ _ _ _ _ _ _ _ SC) Hst Hni LNK0 HR0 CONST')
  as (AR2 & WOWN & AOX2 & PU2 & PUOFF & CI2).
pose proof (DMrcSecFc.sc_HI _ _ _ _ _ _ _ _ _ _ _ SC) as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hC1 & hC2 & hS1 & hS2 & hCE & _).
pose proof (DMrcSecFc.GEOMw _ _ _ _ _ _ _ _ _ _ _ SC NMAXD LMAXD LOK HE) as (GZ & GM2 & GM3 & [GL1 GL2] & GM5 & _).
pose proof (DMrcSecFc.sc_last_facts _ _ _ _ _ _ _ _ _ _ _ SC) as (_ & _ & _ & _ & _ & LZ1 & LZ2 & LZ3 & _).
pose proof (DMrcSecFc.sc_ARRF _ _ _ _ _ _ _ _ _ _ _ SC) as (_ & _ & _ & AN1 & AN2).
pose proof ASAN_CEIL_range as [CRr _].
(* every byte of the walk's windows is above the image's read-only part and below TASK_SIZE, and off the stack frame it
   is below the allocator ceiling, hence below the stack *)
assert (WINB : forall a, DMrcSecMun.WPRE ly regs a \/ DMrcSecGv.WIN3 ly regs MAP LEN qi lst a ->
  (0x9d000 <= a \/ off_img a) /\ a < TASK_SIZE /\ ((sp0 - DMrcSecGv.GDEPTH <= a < sp0) \/ a < ASAN_CEIL)).
{ intros a Hw. unfold DMrcSecMun.WPRE, DMrcSecGv.WIN3, DMrcSecGv.WIN2, DMrcSecGv.WIN, DMrcSecGv.WINS, DMrcSecGv.WINM,
    DMrcSecGv.SHAv, DMrcSecGv.CNTv in Hw. fold sp0 in Hw.
  unfold AFg8.qi, AFg8.idx, AFg8.nA in *.
  clear - Hw Usp HloCF Hcb1 Hcb2 hS1 hS2 hCE hT1 hT2 hQ1 hQ2 GZ GM2 GL1 LZ1 LZ2 AN1 AN2 CRr.
  assert (Z3 : forall x sz, zone3 x sz -> x <= a < x + sz -> off_img a /\ a < ASAN_CEIL).
  { intros x sz Zx Hx. split; [exact (zone3_off_img x sz a Zx Hx)|]. destruct Zx as (_ & Zx & _). lia. }
  destruct Hw as [[Hw|[Hw|Hw]]|[[Hw|[Hw|[Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]]]]|[Hw|Hw]]].
  all: first
   [ destruct (Z3 _ _ hT1 ltac:(unfold t_stats, kThreadObjSize in *; lia)) as [O C]
   | destruct (Z3 _ _ LZ1 ltac:(lia)) as [O C]
   | destruct (Z3 _ _ GZ ltac:(lia)) as [O C]
   | destruct (Z3 _ _ hQ1 ltac:(unfold kPtrArrayResv in *; lia)) as [O C]
   | idtac ].
  all: try (split; [right; exact O|]; split; [unfold TASK_SIZE; lia | right; exact C]).
  all: unfold KSTACK_CF, DMrcSecGv.GDEPTH, TASK_SIZE, off_img in *; numconst_hi; Z.div_mod_to_equations; lia. }
exists regs', mem', (with_vm_backing (m_vm_lazy mdM) mat mdM).
split; [rewrite Ec; reflexivity|].
assert (FRAME : forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly X a -> ~ ascratch B KSTACK_CF regs a ->
  aview tfibsegs (w_H W2) mem' a = aview tfibsegs (w_H W) mem a).
{ intros a Ha NO NS. unfold AFg8.W2. rewrite wrefund_H. apply aview_same. apply KEEP; rewrite unsigned_lit_small by exact Ha;
  intros Hw; (destruct (WOWN a Ha ltac:(first [left; exact Hw | right; exact Hw])) as [O|O]; [exact (NO O) | exact (NS O)]). }
split.
{ split; [exact AR2|]. split; [apply layout_le_refl|]. split; [apply wrefund_wle|].
  split.
  { intros rr Hr'. unfold acallee_saved in Hr'.
    destruct (Z.eq_dec rr 2) as [->|N2]; [etransitivity; [exact CSP | exact LSP]|].
    destruct (Z.eq_dec rr 8) as [->|N8]; [etransitivity; [exact C8 | unfold DMrcSecF6.v, w64; apply Z_to_bv_bv_unsigned]|].
    destruct (Z.eq_dec rr 9) as [->|N9]; [etransitivity; [exact C9 | unfold DMrcSecF6.v, w64; apply Z_to_bv_bv_unsigned]|].
    destruct (Z.eq_dec rr 18) as [->|N18]; [etransitivity; [exact C18 | unfold DMrcSecF6.v, w64; apply Z_to_bv_bv_unsigned]|].
    assert (R : rr = 3 \/ rr = 4 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
    assert (Hin : In (Z_to_bv 5 rr) DMrcSecGv.SREGS).
    { clear - R. unfold DMrcSecGv.SREGS. repeat match goal with R : _ \/ _ |- _ => destruct R as [R|R] end; subst rr; cbn [In];
      repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]). }
    etransitivity; [exact (CS _ Hin) | exact (LSR _ Hin)]. }
  split.
  { pose proof (same_io_munmap (w64 MAP) (w64 LEN) (with_vm_backing (m_vm_lazy md) mat1 md)) as IO2.
    pose proof (AFg8.same_io_wvb' (m_vm_lazy mdM) mat mdM) as IO3. fold mdM in IO2.
    clear - IO2 IO3. unfold same_io in *. destruct IO2 as (J1 & J2 & J3 & J4). destruct IO3 as (K1 & K2 & K3 & K4).
    cbn [with_vm_backing m_vmmaps m_vm_lazy] in *. repeat split; congruence. }
  split.
  { intros a Ha NO _ NS _. exact (FRAME a Ha NO NS). }
  intros a Ha. destruct (Z_lt_le_dec a (sp0 - DMrcSecGv.GDEPTH)) as [LOW|HIGH'].
  - unfold AFg8.W2. rewrite wrefund_H.
    assert (Ua : 0 <= a < 2 ^ 64) by (unfold spZ in Ha; fold sp0 in Ha; clear - Ha HloCF hS1 Usp; unfold KSTACK_CF in *; numconst_hi; lia).
    apply (apresent_same (w_H W) mem); [|apply HPRES; unfold spZ in Ha; fold sp0 in Ha; exact Ha].
    apply KEEP; rewrite unsigned_lit_small by exact Ua.
    + intros Hw. destruct (WINB a (or_introl Hw)) as [_ [_ [C|C]]]; [unfold DMrcSecGv.GDEPTH in *; lia|].
      unfold spZ in Ha. fold sp0 in Ha. clear - Ha C HloCF hCE. unfold KSTACK_CF in *. lia.
    + intros Hw. destruct (WINB a (or_intror Hw)) as [_ [_ [C|C]]]; [unfold DMrcSecGv.GDEPTH in *; lia|].
      unfold spZ in Ha. fold sp0 in Ha. clear - Ha C HloCF hCE. unfold KSTACK_CF in *. lia.
  - unfold AFg8.W2. rewrite wrefund_H. apply PRS. rewrite SPD. unfold spZ in Ha. fold sp0 in Ha. unfold DMrcSecGv.GDEPTH in *. lia. }
split.
{ intros x NO _ NS _. apply KEEP; intros Hw; (destruct (WOWN (bv_unsigned x) (u64_range x) ltac:(first [left; exact Hw | right; exact Hw])) as [O|O]; [exact (NO O) | exact (NS O)]). }
split.
{ intros ii Hii. assert (Ue : 0 <= as_errno B + ii < 2 ^ 64) by (rewrite (ts_errno _ TB); unfold TFIB_ERRNO; lia).
  apply KEEP; unfold w64; rewrite unsigned_lit_small by exact Ue; intros Hw;
  (destruct (WINB _ ltac:(first [left; exact Hw | right; exact Hw])) as [[R0|R0] [R1 [C|C]]];
   rewrite (ts_errno _ TB) in *;
   [ clear - C hS1 Hcb1 Hcb2 HloCF Hii Usp; unfold DMrcSecGv.GDEPTH, KSTACK_CF, TFIB_ERRNO in *; numconst_hi; lia
   | idtac
   | clear - C hS1 Hcb1 Hcb2 HloCF Hii Usp; unfold DMrcSecGv.GDEPTH, KSTACK_CF, TFIB_ERRNO in *; numconst_hi; lia
   | clear - R0 Hii; unfold off_img, TFIB_ERRNO, TFIB_IMG_LO, TFIB_IMG_END in *; lia ]).
  all: unfold DMrcSecMun.WPRE, DMrcSecGv.WIN3, DMrcSecGv.WIN2, DMrcSecGv.WIN, DMrcSecGv.WINS, DMrcSecGv.WINM, DMrcSecGv.SHAv, DMrcSecGv.CNTv, AFg8.qi, AFg8.idx, AFg8.nA in Hw;
    fold sp0 in Hw;
    (assert (NZ : forall x sz, zone3 x sz -> ~ (x <= TFIB_ERRNO + ii < x + sz)) by
       (intros x sz Zx Hx; pose proof (zone3_off_img x sz _ Zx Hx) as O; unfold off_img, TFIB_ERRNO, TFIB_IMG_LO, TFIB_IMG_END in O; lia));
    repeat match goal with Hw : _ \/ _ |- _ => destruct Hw as [Hw|Hw] end;
    first
     [ exact (NZ _ _ hT1 ltac:(unfold t_stats, kThreadObjSize in *; lia))
     | exact (NZ _ _ LZ1 ltac:(lia))
     | exact (NZ _ _ GZ ltac:(lia))
     | exact (NZ _ _ hQ1 ltac:(unfold kPtrArrayResv in *; lia))
     | clear - Hw Hii Usp HloCF hS1 Hcb1 Hcb2 GZ GL1; unfold KSTACK_CF, DMrcSecGv.GDEPTH, TFIB_ERRNO in *; numconst_hi; Z.div_mod_to_equations; lia ]. }
split.
{ apply (MemnormT.memnorm_frame tfibsegs (fun a => DMrcSecMun.WPRE ly regs a \/ DMrcSecGv.WIN3 ly regs MAP LEN qi lst a)).
  - intros x Hx. destruct (WINB _ Hx) as [[R0|R0] [R1 _]];
    [apply MemnormSafereply.mn_safe_rw; lia | apply MemnormSafereply.mn_safe_offimg; [unfold off_img in R0; lia | unfold TASK_SIZE in *; lia]].
  - intros x Nx. apply KEEP; intros Hw; apply Nx; [left | right]; exact Hw. }
split.
{ intros a Ha PU NK. destruct (PUOFF a PU NK) as [N1 N2]. unfold AFg8.W2. rewrite wrefund_H. apply aview_same. apply KEEP; rewrite unsigned_lit_small by exact Ha; assumption. }
split; [exact PU2|]. split; [exact CI2 | exact AOX2].
Qed.
Theorem rchunk_sec_mach_g : amreal tfibsegs (recycle_chunk k X) W (cfg_at tfibsegs A_RChunk regs mem md)
  (rc_mach_sec_g B ARXq AOX inst ly X k W regs mem md).
Proof.
pose proof MAPR as (Hidx & INA & INV & MW & GATE).
pose proof (DMrcSecFc.GEOMw _ _ _ _ _ _ _ _ _ _ _ SC NMAXD LMAXD LOK HE) as (P1 & P2 & P3 & [L1 L1'] & L2 & _).
pose proof (DMrcSecFc.sc_Hk _ _ _ _ _ _ _ _ _ _ _ SC) as Hk.
pose proof (DMrcSecMun.SMALL B ly X k W regs mem r o sm i SC NMAXD LMAXD LOK HE) as SMALL.
pose proof (DMrcSecMun.WALK B TB ly X k cbp W regs mem md r o sm i ARXr inst PRE SC NMAXD LMAXD NOK LOK HN HE Hi GATE) as WALK.
rewrite (AFg8.recycle_chunk_sec k X r o sm i (proj2 (mem_chunk_spec _ _) Hk) Hb Hsm Hidx SMALL). cbn [amreal].
eapply SRr_bind; [exact WALK|]. intros W1 c1 _ (regsD & memD & LNK & HM).
destruct HM as (-> & regs1 & mem1 & mat1 & -> & H17 & H10 & H11 & INNER). cbv zeta in INNER.
apply SRr_use_AI. cbn [cfg_model]. intros HAI. apply SRr_ret.
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md) in *.
set (c2 := mkCfg (mkst (regupd regs1 10 (w64 0)) (w64 0x65a18) (unfill (w64 MAP) (w64 LEN) mem1) (seg_rom tfibsegs))
  (munmap_model (w64 MAP) (w64 LEN) md1)).
assert (UM : bv_unsigned (w64 MAP) = MAP) by (unfold w64; apply unsigned_lit_small; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia).
assert (UL : bv_unsigned (w64 LEN) = LEN) by (unfold w64; apply unsigned_lit_small; lia).
assert (MW1 : amwf md1) by (apply (amwf_same md md1); [subst md1; apply m_vmmaps_wvb | subst md1; apply m_vm_lazy_wvb | exact MW]).
assert (INV1 : In (w64 MAP, w64 LEN) (vm_maps (m_vmmaps md1))) by (subst md1; rewrite m_vmmaps_wvb; exact INV).
destruct (in_split _ _ INV1) as (l1 & l2 & EVM).
exists unit, (fun _ => c2), (fun _ => 1), (fun _ => false), tt.
split.
{ pose proof (munmap_node tfibsegs regs1 (w64 0x65a14) mem1 (seg_rom tfibsegs) md1 (w64 MAP) LEN (AI_halted _ _ _ _ HAI) H17 H10
    ltac:(rewrite UM; unfold page_size; exact P3) H11 ltac:(lia)
    ltac:(rewrite UM, (AFg8.page_round_up_Z_aligned LEN) by lia; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, two_pow_64, TASK_SIZE, kHighMemBeg, ASAN_CEIL in *; lia)
    ltac:(rewrite (AFg8.page_round_up_Z_aligned LEN) by lia; exact (map_has_In _ _ _ INV1))) as ND.
  cbv zeta in ND. rewrite (AFg8.page_round_up_Z_aligned LEN) in ND by lia. exact ND. }
split. { intros [] _. cbn [cfg_model]. exact (munmap_AI tfibsegs (w_H W) (w_A W) md1 (w64 MAP, w64 LEN) l1 l2 HAI MW1 EVM
    ltac:(cbn [fst]; rewrite UM; unfold page_size; exact P3)
    ltac:(cbn [fst snd]; rewrite UM, UL; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia)). }
split. { intros []. cbn [aok]. reflexivity. }
split; [reflexivity|]. split; [reflexivity|]. split; [intros [] _; reflexivity|]. split; [intros [] XX; discriminate XX|].
intros [] _. cbn [amreal].
eapply SRr_bind; [exact INNER|]. intros W3 c3 _ HR. pose proof HR as (-> & regs' & mem' & mat' & Ec3 & _).
apply SRr_use_AI. intros HAI3. rewrite Ec3 in HAI3 |- *. cbn [cfg_model] in HAI3.
apply (SRr_world_le tfibsegs W W2).
{ apply wrefund_wle. }
{ intros _. cbn [cfg_model]. apply AI_refund_gen; [exact HAI3|]. intros p Hp. rewrite m_vm_lazy_wvb in Hp. unfold AFg8.iv. cbn [fst snd].
  pose proof (munmap_lazy_out (w64 MAP) (w64 LEN) md1 p ltac:(destruct MW1 as [(_ & _ & W3l & _) _]; intros q Hq; exact (W3l q Hq))
    ltac:(rewrite UM, UL; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia) Hp) as NL. rewrite UM, UL in NL. exact NL. }
apply SRr_ret. rewrite <- Ec3. exact (FINx_g regsD memD mat1 c3 LNK HR).
Qed.
End e.

(* The walk at ARXp := fun _ => ARXr: the cut relation at the return is the one at the call. *)
Section i.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Hypothesis RCs : DMrcSecReads.rc_sec_cut_t B ARXr.
Hypothesis RMs : DMrcSecReads.rc_sec_mapr_t B ARXr.
Hypothesis RSs : DMrcSecReads.rc_sec_step_t B ARXr AOX.
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
Local Notation MAP := (AFg8.MAP ly r).
Local Notation LEN := (AFg8.LEN sm).
Local Notation nA := (AFg8.nA X).
Local Notation idx := (AFg8.idx i).
Local Notation qi := (AFg8.qi ly i).
Local Notation lst := (AFg8.lst ly X r).
Local Notation own := (AFg8.own X i).
Local Notation vra := (DMrcSecF6.v regs 1%bv).
Local Notation vs0 := (DMrcSecF6.v regs 8%bv).
Local Notation vs1 := (DMrcSecF6.v regs 9%bv).
Local Notation vs2 := (DMrcSecF6.v regs 18%bv).
Local Notation X2v := (AFg8.X2v X k r sm i).
Local Notation W2 := (AFg8.W2 ly W r sm).
(* The machine part of MnRecycle.de_rchunk_m_t's post (as DMrcPrim.rc_mach). *)
Definition rc_mach_sec (r0 : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
  rc_mach_sec_g B ARXr AOX inst ly X k W regs mem md r0 W' c'.
Theorem FINx : forall regsD memD mat1 c', DMrcSecMun.LINKD ly W regs mem regsD memD ->
DMrcSecGv.at_RET W ly regsD memD MAP LEN idx nA qi lst vra vs0 vs1 vs2 own
  (munmap_model (w64 MAP) (w64 LEN) (with_vm_backing (m_vm_lazy md) mat1 md)) W c' ->
rc_mach_sec (tt, X2v) W2 c'.
Proof. exact (FINx_g B TB ARXr (fun _ => ARXr) AOX RCs RSs NMAXD LMAXD LOK inst ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi HE Hst Hni Hkin). Qed.
Theorem rchunk_sec_mach : amreal tfibsegs (recycle_chunk k X) W (cfg_at tfibsegs A_RChunk regs mem md) rc_mach_sec.
Proof.
exact (rchunk_sec_mach_g B TB ARXr (fun _ => ARXr) AOX RCs RMs RSs NMAXD LMAXD NOK LOK inst ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi HN HE
  Hst Hni Hkin).
Qed.
End i.
End d.
