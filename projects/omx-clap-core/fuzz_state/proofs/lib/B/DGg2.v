(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DGg2.v (a working branch ced28ed2383, file sha256 fa0235803725) onto omx-clap-core/fuzz_state's asan-ubsan image (fuzz_state.asan-ubsan, pinned sha256 5ac5ce0954f8; addresses read from its unstripped build b1566a1ca816); module paths changed; its 11 image addresses moved by code-verified function pairs (11 port_addr_check 16f8a030c869 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 4 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: moved from ced28ed2383 to a Theorem Labs lane's c5 install head a working branch 57e82b93d43 (cgif file sha256 d7743d4f7727; the errno-kept twins of ad994c27165, additive). By 3-way merge (base = agreloc of ced28ed2383, theirs = agreloc of 57e82b93d43 with port_addr_check 16f8a030c869 PREDICT rows for it, ours = this file's image-B rows and L edits). *)
(* The MID arm of the frame-generic Deallocate walk: QuarantineCache::Enqueue opens a new batch and the thread
   cache stays within its bound, so Quarantine::Put returns without draining.  Over the interface DGif0.DIface.

   Ported from cgif_file's released free walk (YFg2.afree_mid_arm / YFg2.TAILM), with the caller's frame made
   abstract: the run starts at Deallocate's entry (0x31c50); DGg1.to_enq carries it to Put's call of Enqueue
   (0x36420, the state DGfw.SS_E over the seed DGgm.SS0); Enqueue's post is the section's [ENQb]
   (DIfaceR.enq_spec_b rawb); the thread-cache test of
   [dmd] is false by the premise; Put's tail (0x36414 to its ret) is the released script with every stack offset
   moved by IFRAME = 2128 (Put's frame 2208 -> 80, QuarantineChunk's 2176 -> 48, and the free interceptor's
   top-of-frame region replaced by the seed's empty slot at the entry sp).  The leaf is DIfaceR.dealloc_leaf_b rawb:
   ARX by di_frame, the aview frame by chaining Put's tail, Enqueue's aview post and dmem_m, the raw frame (when
   rawb = true) by chaining Put's tail, Enqueue's raw post (ENQb's acall_raw_x conjunct) and dmem_m, the owned-set
   side conditions by di_owned / di_owned_i / di_owned_x.  One walk (mid_walk) serves the arm and its errno twin: it
   takes Enqueue's contract with any extra conjunct [XR] on its post (DIfaceR.enq_spec_g) and gives, beside the leaf's
   view post, Enqueue's [XR] and the raw frames around the call.

   dealloc_mid_e is the errno-kept twin (DGleafE.dealloc_leaf_b_e rawb, over ENQe : DGleafE.enq_spec_b_e rawb): errno
   is kept from Deallocate's entry to Enqueue's call by dmem_m's frame, across Enqueue by ENQe's errno conjunct, and
   from Enqueue's return to Put's ret by Put's tail's frame (Put's stack window).  errno lies apart from each zone
   those frames exclude by ErrnoApart's image facts, taken as section hypotheses (ErrnoApartcgif discharges them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFew.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1w YE3d YFeq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import AGif0n DeallocG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import DGbase DGgi DGgm DGfv DGfw.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DGif0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import AGif2cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DIfaceR.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require DGg1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require ErrnoG DGleafE ErrnoApart.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
(* ErrnoG Requires YA09, whose non-local [Ltac ... ::=] turns lia's euclidean-division conversion off for every file
   that Requires it; this file's proofs were written with it on (without this line the [lia] of mid_walk's Enqueue
   call fails with "No applicable tactic").  #[local]: the setting stays in this file. *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Local Open Scope am_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac numc := ceil; unfold zone3, zone3cases, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize,
kSpaceSize, kPrimResvSize, t_qc, t_cache, t_unwinding, t_stats, DFSTACK, DFSTACK_G, TFIB_IMG_END, QSTACK, TFIB_ERRNO in *.

(* The regions of DGfw.SS_E that QuarantineCache::Enqueue keeps: Put's frame above the callee's scratch (trimmed to
   Put's sp, 80 below Deallocate's entry sp), the caller's stack object, QuarantineChunk's frame and the seed's
   empty slot at the entry sp. *)
Definition r0E : YP09.region := Eval vm_compute in nth 0 (ss_mem DGfw.SS_E) (YP09.mkRegion None 0 0 0 0 []).
Definition r1E : YP09.region := Eval vm_compute in nth 1 (ss_mem DGfw.SS_E) (YP09.mkRegion None 0 0 0 0 []).
Definition r2E : YP09.region := Eval vm_compute in nth 2 (ss_mem DGfw.SS_E) (YP09.mkRegion None 0 0 0 0 []).
Definition r3E : YP09.region := Eval vm_compute in nth 3 (ss_mem DGfw.SS_E) (YP09.mkRegion None 0 0 0 0 []).
Definition r4E : YP09.region := Eval vm_compute in nth 4 (ss_mem DGfw.SS_E) (YP09.mkRegion None 0 0 0 0 []).
Definition RS_E : smem := [trim_lo r0E (-80); r1E; r2E; r4E].
Lemma SSE_mem : ss_mem DGfw.SS_E = r0E :: r1E :: r2E :: r3E :: r4E :: skipn 5 (ss_mem DGfw.SS_E).
Proof. vm_compute. reflexivity. Qed.
Lemma RS_E_sub : submem RS_E (ss_mem DGfw.SS_E).
Proof.
rewrite SSE_mem. unfold RS_E.
apply submem_keep; [apply subregion_trim_lo|].
apply submem_keep; [apply subregion_refl|].
apply submem_keep; [apply subregion_refl|].
apply submem_drop. apply submem_keep; [apply subregion_refl|]. apply submem_nil.
Qed.
Definition SS_T : sstate := Eval vm_compute in ss_after_call DGfw.SS_E RS_E 112 222228.
(* The thread cache's byte count, which Put reads after Enqueue returns. *)
Definition R_QBF : YP09.region :=
YP09.mkRegion (Some 32%nat) (t_qc + 24) (t_qc + 32) 0 0 [YP09.mkChunk (t_qc + 24) (CVal 8 (SOff 50%nat 0))].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma wvb_self : forall md, with_vm_backing (m_vm_lazy md) (m_vm_materialized md) md = md.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma aview_eq_mbyte : forall (H H' : word -> bool) (m m' : word -> option byte) a,
aview tfibsegs H' m' a = aview tfibsegs H m a -> mbyte tfibsegs (mrestrict H' m') a = mbyte tfibsegs (mrestrict H m) a.
Proof.
intros H H' m m' a E. unfold aview in E.
destruct (mbyte tfibsegs (mrestrict H' m') a) as [b'|], (mbyte tfibsegs (mrestrict H m) a) as [b|]; cbn in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma kept_of_aview : forall (E : env) (W W5 : world tfibsegs) (m m' : word -> option byte) r,
(forall a, base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
aview tfibsegs (w_H W5) m' a = aview tfibsegs (w_H W) m a) ->
(forall a, base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
aview tfibsegs (w_H W5) m' a = aview tfibsegs (w_H W) m a /\ TFIB_IMG_END <= a < 2 ^ 64) ->
region_kept tfibsegs E (mrestrict (w_H W) m) (mrestrict (w_H W5) m') r.
Proof.
intros E W W5 m m' r Hext Hwin. split.
- intros a Ha. apply aview_eq_mbyte. apply Hext. exact Ha.
- intros a Ha Hw. destruct (Hwin a Ha) as [EQ Hh]. apply apresent_writable; [exact Hh|].
pose proof (writable_high_apresent (w_H W) m a Hh Hw) as P. apply apresent_mbyte in P as [b Hb].
assert (A : aview tfibsegs (w_H W) m a = Some (bv_unsigned b)) by (unfold aview; rewrite Hb; reflexivity).
rewrite <- EQ in A. apply aview_some in A as (b' & Hb' & _). exact (mbyte_high_apresent (w_H W5) m' a b' Hh Hb').
Qed.
(* The callee-saved registers of the virtual regs0 are the entry registers' (DGfy's). *)
Lemma aregs_of_cs : forall regs pa inst bp so (regs' : bvmap 5 word),
(forall r : bv 5, In r CALLEE_SAVED -> getr regs' r = getr (dregs regs pa inst bp so) r) -> aregs_preserved regs regs'.
Proof.
intros regs pa inst bp so regs' RCS r Hr.
assert (HrZ : bv_unsigned (Z_to_bv 5 r) = r).
{ rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 5) with 32. unfold acallee_saved in Hr. apply Z.mod_small. lia. }
rewrite <- (dregs_other regs pa inst bp so (Z_to_bv 5 r)) by (rewrite HrZ; unfold acallee_saved in Hr; lia).
apply RCS. unfold acallee_saved in Hr.
assert (H18 : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
clear - H18.
assert (E5 : forall k : Z, 0 <= k < 32 -> forall b : bv 5, bv_unsigned b = k -> Z_to_bv 5 k = b) by (intros k Hk b Hb; apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 5) with 32; rewrite Z.mod_small by lia; symmetry; exact Hb).
destruct H18 as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
[ rewrite (E5 2 ltac:(lia) 2%bv eq_refl) | rewrite (E5 3 ltac:(lia) 3%bv eq_refl) | rewrite (E5 4 ltac:(lia) 4%bv eq_refl)
| rewrite (E5 8 ltac:(lia) 8%bv eq_refl) | rewrite (E5 9 ltac:(lia) 9%bv eq_refl) | rewrite (E5 18 ltac:(lia) 18%bv eq_refl)
| rewrite (E5 19 ltac:(lia) 19%bv eq_refl) | rewrite (E5 20 ltac:(lia) 20%bv eq_refl) | rewrite (E5 21 ltac:(lia) 21%bv eq_refl)
| rewrite (E5 22 ltac:(lia) 22%bv eq_refl) | rewrite (E5 23 ltac:(lia) 23%bv eq_refl) | rewrite (E5 24 ltac:(lia) 24%bv eq_refl)
| rewrite (E5 25 ltac:(lia) 25%bv eq_refl) | rewrite (E5 26 ltac:(lia) 26%bv eq_refl) | rewrite (E5 27 ltac:(lia) 27%bv eq_refl) ];
cbn [In CALLEE_SAVED]; tauto.
Qed.
Ltac cs_case HS HEn Htp :=
lazymatch goal with |- getr _ ?kb = _ => let RR := fresh "RR" in rreg HS kb RR; rewrite RR end;
first [ rewrite HEn by (cbv; lia); first [ refine (DGgm.Er _ _ _ _ _ _ _ _ _ _ _ _ _); reflexivity | symmetry; refine (DGgm.Er _ _ _ _ _ _ _ _ _ _ _ _ _); reflexivity ]
| rewrite Htp; reflexivity | symmetry; rewrite Htp; reflexivity ].

(* errno through a callee at the leaf's form (DGleafE.errno_kept_b): kept on the raw memory before the call and after
   its return, and at the leaf's form across the call. *)
Lemma errno_through : forall rawb (B : asyms) (W W' : world tfibsegs) (m0 m1 m2 m3 : word -> option byte),
ErrnoG.errno_kept B m0 m1 -> DGleafE.errno_kept_b rawb B W W' m1 m2 -> ErrnoG.errno_kept B m2 m3 ->
DGleafE.errno_kept_b rawb B W W' m0 m3.
Proof.
intros [|] B W W' m0 m1 m2 m3 E01 E12 E23.
- intros i Hi. rewrite (E23 i Hi), (E12 i Hi). exact (E01 i Hi).
- intros a Ha.
  assert (K : forall m m' : word -> option byte, ErrnoG.errno_kept B m m' -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
  { intros m m' E. pose proof (E (a - as_errno B) ltac:(lia)) as E'.
    replace (as_errno B + (a - as_errno B)) with a in E' by lia. unfold w64 in E'. exact E'. }
  exact (eq_trans (aview_same (w_H W') m2 m3 a (K _ _ E23))
    (eq_trans (E12 a Ha) (aview_same (w_H W) m0 m1 a (K _ _ E01)))).
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
(* [rawb = true]: the leaf's raw frame too (Enqueue's raw post from ENQb). *)
Variable rawb : bool.
Hypothesis IF : DIface B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq.
Hypothesis ENQb : enq_spec_b B U ARX AOX rpre lpost fpre dpost L24 QB rawb.
Local Notation Finst := (di_inst B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq IF).
Local Notation Fview := (di_view B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq IF).
Local Notation Fframe := (di_frame B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq IF).
Local Notation Fstack := (di_stack B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq IF).
Local Notation Fown := (di_owned B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq IF).
Local Notation Fown_i := (di_owned_i B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq IF).
Local Notation Fown_x := (di_owned_x B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq IF).

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Put's tail: from Enqueue's return (0x36414) to Put's ret, the released YFg2.TAILM script with the stack offsets
   moved by IFRAME.                                                                                                 *)
Lemma TAILM : forall (W W5 : world tfibsegs) (ly : alayout) (S X X' : astate) (regs : bvmap 5 word)
(mem : word -> option byte) (inst so bp : Z) (p : sptr) (n : Z) (tr : list Z) (hb1 j1 j2 j3 : Z)
(msE : machine_state) (mdE : Model) (E5 : env) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
DGgm.free_hyps W ly (dregs regs (sptr_addr B ly p) inst bp so) mem tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3 regs ->
msE = mkst (ms_regs msE) (w64 0x36420) (ms_mem msE) (seg_rom tfibsegs) ->
(forall k0, (k0 < aHAVf)%nat -> ew E5 k0 =
   ew (DGgm.E0 ly (dregs regs (sptr_addr B ly p) inst bp so) tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3) k0) ->
st_ok tfibsegs E5 DGfw.SS_E (restrict (w_H W) msE) ->
(forall a, bv_unsigned (getr regs 2) - DFSTACK <= a < bv_unsigned (getr regs 2) -> apresent (w_H W) (ms_mem msE) a) ->
(forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> ~ AOX ly X a /\ ~ AOX ly X' a) ->
acall_post_x B ARX AOX inst QSTACK ly X W (ms_regs msE) (ms_mem msE) mdE (fun _ => False) ly X' W5 regs' mem' md' ->
val_mem tfibsegs (mrestrict (w_H W5) mem') (ly_T ly + t_qc + 24) 8 (DGgm.QBFv (req_size n) (st_qthread S)) ->
DGgm.QBFv (req_size n) (st_qthread S) <= kQuarantineCacheMax ->
SRr tfibsegs W5 (cfg_at tfibsegs 0x36414 regs' mem' md')
(fun Wo co => Wo = W5 /\ exists regsR memR mat',
  co = cfg_at tfibsegs (bv_unsigned (getr regs 1)) regsR memR (with_vm_backing (m_vm_lazy md') mat' md') /\
  (forall r : bv 5, In r CALLEE_SAVED -> getr regsR r = getr (dregs regs (sptr_addr B ly p) inst bp so) r) /\
  (forall x : word, ~ (bv_unsigned (getr regs 2) - 80 <= bv_unsigned x < bv_unsigned (getr regs 2)) -> memR x = mem' x) /\
  (forall a, bv_unsigned (getr regs 2) - DFSTACK <= a < bv_unsigned (getr regs 2) -> apresent (w_H W5) memR a) /\
  (forall a, aview tfibsegs (w_H W5) mem' a <> None -> aview tfibsegs (w_H W5) memR a <> None)).
Proof.
intros W W5 ly S X X' regs mem inst so bp p n tr hb1 j1 j2 j3 msE mdE E5 regs' mem' md' FH HshE HEn5 HS PRESE NOWN POST RV HQBF.
pose proof Hwx_tfa as Hwx.
set (regs0 := dregs regs (sptr_addr B ly p) inst bp so) in *.
set (sp0 := bv_unsigned (getr regs 2)) in *.
destruct POST as (ARX' & LLE & WLE & CS & SIO & FR & PRS).
assert (R2 : getr regs0 2 = getr regs 2) by (unfold regs0; apply dregs_other; vm_compute; discriminate).
assert (R1 : getr regs0 1 = getr regs 1) by (unfold regs0; apply dregs_other; vm_compute; discriminate).
pose proof (DGgm.LYB W ly regs0 mem tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3 regs FH) as LB.
pose proof (DGgm.fh_Hsp _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as Hsp. rewrite R2 in Hsp. fold sp0 in Hsp.
pose proof (DGgm.fh_Hso _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as Hso. rewrite R2 in Hso. fold sp0 in Hso.
pose proof (DGgm.fh_Hra _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as Hra. rewrite R1 in Hra.
pose proof (DGgm.stack_ivs W ly regs0 mem tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3 regs FH) as SIV.
rewrite R2 in SIV. fold sp0 in SIV.
pose proof (DGgm.LYD W ly regs0 mem tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3 regs FH) as LYD.
cbn zeta in LYD. destruct LYD as (_ & (_ & _ & _ & TSTK) & _).
unfold zdisjoint in TSTK. cbn [fst snd] in TSTK.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
(* the registers at Enqueue's call *)
rreg HS (2%bv : bv 5) Q2.
rewrite (HEn5 2%nat ltac:(cbv; lia)), (DGgm.E2 ly regs0 tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3), R2 in Q2.
assert (SPE : spZ (ms_regs msE) = sp0 - 80).
{ unfold spZ. rewrite Q2. rewrite unsigned_lit_small; [reflexivity|]. clear - Usp Hsp LB. numc. lia. }
unfold ascratch in FR. rewrite SPE in FR, PRS.
assert (BE2 : bv_unsigned (ew (DGgm.E0 ly regs0 tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3) 2) = sp0)
  by (rewrite (DGgm.E2 ly regs0 tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3), R2; reflexivity).
assert (BE13 : bv_unsigned (ew (DGgm.E0 ly regs0 tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3) 13) = bv_unsigned (getr regs0 13))
  by (rewrite (DGgm.E13 ly regs0 tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3); reflexivity).
assert (BE32 : bv_unsigned (ew (DGgm.E0 ly regs0 tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3) 32) = ly_T ly).
{ unfold w64. apply unsigned_lit_small.
  destruct LB as ((T1 & T2 & _) & _). clear - T1 T2. ceil. unfold ASAN_CEIL, kThreadObjSize in *. lia. }
assert (BV2 : bv_unsigned (ew E5 2) = sp0) by (rewrite (HEn5 2%nat ltac:(cbv; lia)); exact BE2).
assert (BV13 : bv_unsigned (ew E5 13) = bv_unsigned (getr regs0 13)) by (rewrite (HEn5 13%nat ltac:(cbv; lia)); exact BE13).
assert (BV32 : bv_unsigned (ew E5 32) = ly_T ly) by (rewrite (HEn5 32%nat ltac:(cbv; lia)); exact BE32).
assert (NERR : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> ~ (as_errno B <= a < as_errno B + 4)).
{ intros a Ha. rewrite (ts_errno B TS). destruct LB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L5).
  clear - Ha L5. unfold TFIB_ERRNO, kHighMemBeg in *. lia. }
assert (AGS : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> sp0 - 80 <= a ->
  aview tfibsegs (w_H W5) mem' a = aview tfibsegs (w_H W) (ms_mem msE) a).
{ intros a Ha Hge. destruct (NOWN a Ha) as [N1 N2].
  apply FR; [clear - Ha LB Usp; numc; lia | exact N1 | exact N2 | | intros []].
  intros [Hs|Hs]; [clear - Hs Hge; unfold QSTACK in *; lia | exact (NERR a Ha Hs)]. }
assert (HP : regs_preserved (ms_regs msE) regs') by (intros r Hr'; apply CS; exact Hr').
pose proof (st_ok_after_call tfibsegs 112 E5 DGfw.SS_E (restrict (w_H W) msE) regs' (mrestrict (w_H W5) mem') RS_E 222228
  HS eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) RS_E_sub ltac:(vm_compute; reflexivity) HP) as HS1.
cbn [ms_mem restrict] in HS1.
assert (KEPT : Forall (region_kept tfibsegs E5 (mrestrict (w_H W) (ms_mem msE)) (mrestrict (w_H W5) mem')) RS_E).
{ unfold RS_E. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
  - apply (kept_of_aview E5 W W5); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi trim_lo r0E]; rewrite BV2.
    + intros a Ha. apply AGS; clear - Ha Hsp LB; [numc; lia | lia].
    + intros a Ha. split; [apply AGS; clear - Ha Hsp LB; [numc; lia | lia]|].
      clear - Ha Hsp LB Usp. numc. lia.
  - apply (kept_of_aview E5 W W5); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi r1E]; rewrite BV13.
    + intros a Ha. apply AGS; clear - Ha Hsp Hso LB; [numc; lia | lia].
    + intros a Ha. clear - Ha. lia.
  - apply (kept_of_aview E5 W W5); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi r2E]; rewrite BV2.
    + intros a Ha. apply AGS; clear - Ha Hsp LB; [numc; lia | lia].
    + intros a Ha. split; [apply AGS; clear - Ha Hsp LB; [numc; lia | lia]|].
      clear - Ha Hsp LB Usp. numc. lia.
  - apply (kept_of_aview E5 W W5); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi r4E]; rewrite BV2.
    + intros a Ha. clear - Ha. lia.
    + intros a Ha. clear - Ha. lia. }
specialize (HS1 KEPT). clear KEPT.
change (ss_after_call DGfw.SS_E RS_E 112 222228) with SS_T in HS1.
set (En6 := havoc E5 112 (map (getr regs') CLOB)) in HS1.
assert (HEn6 : forall k0, (k0 < aHAVf)%nat -> ew En6 k0 =
  ew (DGgm.E0 ly regs0 tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3) k0)
  by (intros k0 Hk0; subst En6; unfold aHAVf in Hk0; rewrite ew_havoc_old by lia; apply HEn5; exact Hk0).
assert (BW2 : bv_unsigned (ew En6 2) = sp0) by (rewrite (HEn6 2%nat ltac:(cbv; lia)); exact BE2).
assert (BW13 : bv_unsigned (ew En6 13) = bv_unsigned (getr regs0 13)) by (rewrite (HEn6 13%nat ltac:(cbv; lia)); exact BE13).
assert (BW32 : bv_unsigned (ew En6 32) = ly_T ly) by (rewrite (HEn6 32%nat ltac:(cbv; lia)); exact BE32).
assert (QB0 : 0 <= DGgm.QBFv (req_size n) (st_qthread S)).
{ pose proof (DGgm.fh_Hqb _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as [Q1 _].
  pose proof (DGgm.fh_Hnn _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as Q2'.
  unfold DGgm.QBFv in *. destruct (need_new_batch (st_qthread S)); unfold kBatchBytes in *; lia. }
(* the thread cache's byte count, which Put reads *)
apply (st_ok_add_region _ _ _ R_QBF) in HS1;
[ | reflexivity
| unfold R_QBF, YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem];
  rewrite BW32;
  split; [destruct LB as ((T1 & _) & _); clear - T1; unfold t_qc; lia|];
  split; [destruct LB as ((T1 & T2 & _) & _); clear - T1 T2; ceil; unfold ASAN_CEIL, kThreadObjSize, t_qc in *; lia|];
  split; [intros o Ho; lia|];
  apply Forall_cons; [|apply Forall_nil];
  eapply (chunk_ok_val tfibsegs En6 _ _ _ 8 (SOff 50%nat 0) (DGgm.QBFv (req_size n) (st_qthread S)));
  [ cbn [sv_denot]; rewrite (HEn6 50%nat ltac:(cbv; lia)),
      (DGgm.EaQBF ly regs0 tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3);
    unfold w64; rewrite Zbv_add_unsigned; f_equal; lia
  | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - QB0 HQBF; unfold kQuarantineCacheMax in *; lia
  | cbn; lia
  | change (N.to_nat 8) with 8%nat; eapply val_mem_addr; [exact RV | unfold t_qc; lia] ]
| unfold R_QBF, RS_E; cbn [all_disjoint ss_mem SS_T]; unfold extent_disjoint;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val trim_lo r0E r1E r2E r4E];
  rewrite BW2, BW13, BW32;
  destruct LB as ((T1 & T2 & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L1 & L2 & L3 & L4 & L5);
  clear - T1 T2 L1 L2 L3 L4 L5 Hsp Hso SIV TSTK Usp; destruct SIV as (IT & _);
  ceil; unfold ASAN_CEIL, kThreadObjSize, t_qc, DFSTACK, kHighMemBeg, kHighMemEnd in *;
  repeat split; lia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
rewrite <- (restrict_mkst_fx (w_H W5)) in HS1. clear HS. rename HS1 into HS.
unfold cfg_at. rewrite <- (wvb_self md') at 1. change (w64 0x36414) with (Z_to_bv 64 222228).
srr_run_sh tfibtbl_rtF_ok HS.
rename HF into HF0. clear HFr.
srr_branch_sh tfibtbl_rtF_ok HS.
{ exfalso. match goal with H : branch_taken _ _ _ = true |- _ => rewrite branch_ltu_U in H; apply Z.ltb_lt in H; revert H end.
rewrite !U_zev by reflexivity. cbn [zev zalu_raw]. unfold rho_of.
rewrite (HEn6 50%nat ltac:(cbv; lia)), (DGgm.EaQBF ly regs0 tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3), Z.add_0_r.
unfold w64. rewrite unsigned_lit_small by (clear - QB0 HQBF; unfold kQuarantineCacheMax in *; lia).
rewrite !zcanon_id by (clear - QB0 HQBF; unfold kQuarantineCacheMax, M64 in *; lia).
clear - QB0 HQBF. unfold kQuarantineCacheMax in *. lia. }
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_sh tfibtbl_rtF_ok HS.
lazymatch type of HS with st_ok _ ?E _ (restrict _ ?msx) => set (En7 := E) in HS; rename msx into msR end.
assert (HEn7 : forall k0, (k0 < aHAVf)%nat -> ew En7 k0 =
  ew (DGgm.E0 ly regs0 tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3) k0)
  by (intros k0 Hk0; subst En7; unfold aHAVf in Hk0; rewrite ?ew_havoc_old by lia; apply HEn6; exact Hk0).
(* the tail writes only Put's and QuarantineChunk's frames *)
assert (FRT : forall x : word, ~ (sp0 - 80 <= bv_unsigned x < sp0) -> ms_mem msR x = mem' x).
{ intros x Hx. rewrite (HF x); [apply (HF0 x)|].
all: intros Hw; destruct (in_wrange_windows _ _ _ Hw) as (b & lo & hi & Hin & Hrg);
lazymatch type of Hin with In _ (windows ?rs) => let ws := eval vm_compute in (windows rs) in change (windows rs) with ws in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [Hin|Hin];
[ injection Hin as <- <- <-; cbn [fst snd base_val] in Hrg;
  rewrite ?BW2, ?BW13, ?BW32 in Hrg; clear - Hx Hrg; lia |]);
destruct Hin. }
assert (PRES' : forall a, sp0 - DFSTACK <= a < sp0 -> ~ (sp0 - 80 <= a < sp0) -> apresent (w_H W5) mem' a).
{ intros a Ha N1. destruct (Z_lt_le_dec a (sp0 - 80 - QSTACK)) as [L|L]; [|apply PRS; clear - L N1 Ha; lia].
  assert (EQa : aview tfibsegs (w_H W5) mem' a = aview tfibsegs (w_H W) (ms_mem msE) a).
  { destruct (NOWN a ltac:(clear - Ha Hsp LB; numc; lia)) as [M1 M2].
    apply FR; [clear - Ha Hsp LB Usp; numc; lia | exact M1 | exact M2 | | intros []].
    intros [Hs|Hs]; [clear - Hs L; unfold QSTACK in *; lia | exact (NERR a ltac:(clear - Ha Hsp LB; numc; lia) Hs)]. }
  pose proof (PRESE a Ha) as P. apply apresent_mbyte in P as [b Hb].
  assert (A : aview tfibsegs (w_H W) (ms_mem msE) a = Some (bv_unsigned b)) by (unfold aview; rewrite Hb; reflexivity).
  rewrite <- EQa in A. apply aview_some in A as (b' & Hb' & _).
  exact (mbyte_high_apresent (w_H W5) mem' a b' ltac:(clear - Ha Hsp LB Usp; numc; lia) Hb'). }
assert (PRESR : forall a, sp0 - DFSTACK <= a < sp0 -> apresent (w_H W5) (ms_mem msR) a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 80)) as [L1|L1]; [|destruct (Z_lt_le_dec a (sp0 - 48)) as [L2|L2]].
  - apply (apresent_same (w_H W5) mem');
    [ apply FRT; rewrite unsigned_lit_small by (clear - Ha Hsp LB Usp; numc; lia); clear - L1; lia
    | apply PRES'; [exact Ha | clear - L1; lia] ].
  - eapply (st_ok_window_apresent (w_H W5) En7 _ _ 1 _ a HS);
    [ reflexivity
    | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn7 2%nat ltac:(cbv; lia)),
      (DGgm.E2 ly regs0 tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3), R2; fold sp0; clear - L1 L2; lia
    | clear - Ha Hsp LB Usp; numc; lia ].
  - eapply (st_ok_window_apresent (w_H W5) En7 _ _ 3 _ a HS);
    [ reflexivity
    | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn7 2%nat ltac:(cbv; lia)),
      (DGgm.E2 ly regs0 tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3), R2; fold sp0; clear - L2 Ha; lia
    | clear - Ha Hsp LB Usp; numc; lia ]. }
assert (VIS : forall a, aview tfibsegs (w_H W5) mem' a <> None -> aview tfibsegs (w_H W5) (ms_mem msR) a <> None).
{ intros a Hv HN. unfold aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
  destruct (w_H W5 x) eqn:Hx; [exact (Hv HN)|].
  destruct (seg_rom tfibsegs x) eqn:ROM; [destruct (ms_mem msR x); discriminate|].
  destruct (ms_mem msR x) as [|] eqn:E'; [discriminate|]. clear HN.
  destruct (mem' x) as [b0|] eqn:EE0; [clear Hv | exact (Hv eq_refl)].
  set (a' := bv_unsigned x). assert (Ha' : 0 <= a' < 2 ^ 64) by (subst a'; apply u64_range).
  assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
  destruct (Z_lt_le_dec a' (sp0 - 80)) as [C1|C1]; [|destruct (Z_lt_le_dec a' sp0) as [C2|C2]].
  - rewrite (FRT x ltac:(clear - C1; lia)) in E'. congruence.
  - destruct (PRESR a' ltac:(clear - C1 C2; unfold DFSTACK; lia)) as [_ [bb Hb]]. rewrite Ex in Hb. congruence.
  - rewrite (FRT x ltac:(clear - C2; lia)) in E'. congruence. }
eapply (SRr_ret_at tfibsegs tfibtbl_rtF tfibtbl_rtF_ok Hwx W5 En7); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'.
rreg HS (1%bv : bv 5) Q1f.
rewrite (HEn7 1%nat ltac:(cbv; lia)), (DGgm.E1 ly regs0 tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3), R1 in Q1f.
split; [reflexivity|]. exists (ms_regs msR), (ms_mem msR), mat'.
split.
{ unfold cfg_at, w64. rewrite Q1f, Z_to_bv_bv_unsigned. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split.
{ pose proof (DGgm.fh_Htp _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as Htp.
  intros r Hr. cbv [CALLEE_SAVED In] in Hr.
  repeat (destruct Hr as [<-|Hr]; [cs_case HS HEn7 Htp|]). destruct Hr. }
split; [exact FRT|]. split; [exact PRESR | exact VIS].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The walk to Put's ret, over Enqueue's contract with any extra conjunct [XR] on its post: the leaf's view post and
   lpost, and what the two forms of the arm compose their raw frame and errno from: Enqueue's [XR] at its call and
   return; the walk's raw frame given Enqueue's raw frame (acall_raw_x); dmem_m's frame (the memory at Enqueue's call
   against the entry memory); Put's tail's frame (the memory at Put's ret against Enqueue's return memory).          *)
Lemma mid_walk : forall (XR : fxrel), enq_spec_g B U ARX AOX rpre lpost fpre dpost L24 QB XR ->
forall inst so bp ly S W regs mem md p n tr,
DeallocG.dealloc_pre tfibsegs B U ARX rpre fpre 1 inst so bp ly S W regs mem md p n tr ->
In (p, n) (blocks S) -> need_new_batch (st_qthread S) = true ->
qc_bytes (st_qthread S) + req_size n + (if need_new_batch (st_qthread S) then kBatchBytes else 0) <= kQuarantineCacheMax ->
amreal tfibsegs (ft p tr S) W (cfg_at tfibsegs 0x31c50 regs mem md)
(fun r Wo co => exists regsR memR mdR,
  co = cfg_at tfibsegs (raZ regs) regsR memR mdR /\
  DeallocG.dealloc_post tfibsegs B ARX AOX inst ly S W regs mem md
    (fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n) ly (snd r) Wo regsR memR mdR /\
  lpost (snd r) /\
  exists X regsC memC mdC regsE memE mdE,
    XR inst YFewC.QSTACK ly X W regsC memC mdC (fun _ => False) ly (snd r) Wo regsE memE mdE /\
    (acall_raw_x B AOX inst YFewC.QSTACK ly X W regsC memC mdC (fun _ => False) ly (snd r) Wo regsE memE mdE ->
     forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ AOX ly (snd r) (bv_unsigned x) ->
     ~ ascratch B DFSTACK_G regs (bv_unsigned x) ->
     ~ (p <> PNull /\ sptr_addr B ly p <= bv_unsigned x < sptr_addr B ly p + req_size n) -> memR x = mem x) /\
    (forall x : word, ~ dwin_m ly (bv_unsigned (getr regs 2)) (sptr_addr B ly p) (bv_unsigned x) ->
     ~ dg_dzone ly (bv_unsigned x) -> ~ dg_izone (bv_unsigned x) ->
     ~ dshadow (sptr_addr B ly p) (req_size n) (bv_unsigned x) -> memC x = mem x) /\
    (forall x : word, ~ (bv_unsigned (getr regs 2) - 80 <= bv_unsigned x < bv_unsigned (getr regs 2)) ->
     memR x = memE x)).
Proof.
intros XR ENQ inst so bp ly S W regs mem md p n tr PRE HBLK HNB Hcache.
pose proof PRE as PRE0.
destruct PRE as (HARX & HRP & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & Hpres & Hgp & Htp & Hr10 & Hr11 & Hr12 & Hr13 & Hr14 & Hr15 &
Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htrlen & PSO & PLEN & PBUF & Htr & Hp0 & HFP).
pose proof (Finst _ _ _ _ _ _ HARX) as HIO.
pose proof (Fview inst ly S W mem md p n HARX HRP HFP HBLK) as DV.
pose proof DV as [DVn DVnn DVch DVhdr DVpres DVsh DVjunk DVzone DVqb DVbatch].
destruct DVch as (k & Hf & Hst & Hu & Hr).
destruct (DGg1.FH_m B TS U ARX rpre fpre inst so bp ly S W regs mem md p n tr PRE0 HBLK HIO DV)
  as (hb1 & j1 & j2 & j3 & Hhb1 & Hhdr & FH).
pose proof (DGgm.derived_ranges W ly (dregs regs (sptr_addr B ly p) inst bp so) mem tr (sptr_addr B ly p)
  (req_size n) hb1 (st_qthread S) j1 j2 j3 regs FH) as DR.
pose proof (DGgm.LYB W ly (dregs regs (sptr_addr B ly p) inst bp so) mem tr (sptr_addr B ly p)
  (req_size n) hb1 (st_qthread S) j1 j2 j3 regs FH) as LB.
assert (RG2 : getr (dregs regs (sptr_addr B ly p) inst bp so) 2 = getr regs 2) by (apply dregs_other; vm_compute; discriminate).
assert (RG3 : getr (dregs regs (sptr_addr B ly p) inst bp so) 3 = getr regs 3) by (apply dregs_other; vm_compute; discriminate).
assert (Upa : 0 <= sptr_addr B ly p < 2 ^ 64) by (clear - DR; ceil; unfold ASAN_CEIL in *; lia).
assert (Unn : 0 <= req_size n < 2 ^ 64) by (clear - DR; lia).
assert (NBLK : forall a, ly_stk_lo ly <= a < ly_stk_hi ly ->
  ~ (sptr_addr B ly p <= a < sptr_addr B ly p + req_size n)).
{ intros a Ha Hb. destruct DVzone as (_ & PST & _ & _).
  pose proof (div8_bounds (req_size n + 7) ltac:(clear - DR; lia)) as D8.
  destruct (PST a ltac:(unfold DGgi.N8v, DGgiC.N8v in *; clear - Hb D8; lia)) as [N1 _]. exact (N1 Ha). }
(* the walk to Put's ret *)
apply (DGg1.to_enq B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq IF TS
  inst so bp ly S W regs mem md p n tr k hb1 j1 j2 j3 _ PRE0 HBLK Hf Hst Hhb1 Hhdr FH).
intros z msE mat E5 AOK HshE HEn5 HS5 DM.
pose proof DM as DM0. destruct DM as (_ & DMfr & _ & _ & DMps & _).
(* the registers at Enqueue's call *)
rreg HS5 (1%bv : bv 5) E1r. rreg HS5 (2%bv : bv 5) E2r. rreg HS5 (3%bv : bv 5) E3r. rreg HS5 (4%bv : bv 5) E4r.
rreg HS5 (10%bv : bv 5) E10r. rreg HS5 (11%bv : bv 5) E11r. rreg HS5 (13%bv : bv 5) E13r. rreg HS5 (14%bv : bv 5) E14r.
assert (BV2 : bv_unsigned (ew E5 2) = bv_unsigned (getr regs 2)).
{ rewrite (HEn5 2%nat ltac:(cbv; lia)), (DGgm.E2 ly (dregs regs (sptr_addr B ly p) inst bp so) tr
    (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3), RG2. reflexivity. }
assert (BV32 : bv_unsigned (ew E5 32) = ly_T ly).
{ rewrite (HEn5 32%nat ltac:(cbv; lia)). unfold w64. apply unsigned_lit_small.
  destruct LB as ((T1 & T2 & _) & _). clear - T1 T2. ceil. unfold ASAN_CEIL, kThreadObjSize in *. lia. }
assert (BV10 : bv_unsigned (ew E5 10) = sptr_addr B ly p).
{ rewrite (HEn5 10%nat ltac:(cbv; lia)), (DGgm.E10 ly (dregs regs (sptr_addr B ly p) inst bp so) tr
    (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3), dregs_10. unfold w64.
  apply unsigned_lit_small. exact Upa. }
assert (SPE : spZ (ms_regs msE) = bv_unsigned (getr regs 2) - 80).
{ unfold spZ. rewrite E2r, BV2. apply unsigned_lit_small.
  pose proof (u64_range (getr regs 2)) as U2. unfold spZ in Hlo. clear - DR LB Hlo U2. numc. lia. }
rewrite HshE at 1.
change (mkCfg (mkst (ms_regs msE) (w64 0x36420) (ms_mem msE) (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md))
  with (cfg_at tfibsegs A_Enqueue (ms_regs msE) (ms_mem msE) (with_vm_backing (m_vm_lazy md) mat md)).
eapply amreal_mbind.
{ apply (ENQ inst ly S W mem md p n tr k z hb1 (bv_unsigned (getr regs 2)) (ms_regs msE) (ms_mem msE) mat
    HARX HRP HFP HBLK Htr Hf Hst
    ltac:(unfold DFSTACK, DGbaseC.DFSTACK, DFSTACK_G, spZ in *; clear - Hlo; lia)
    ltac:(unfold spZ in *; clear - Hhi; lia)
    ltac:(unfold spZ in *; clear - Hbot; lia)
    ltac:(unfold spZ in *; clear - Hal; lia)
    Hhb1 Hhdr DM0).
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
intros a s' W' c' HPOST'.
destruct HPOST' as (regsE' & memE' & mdE' & nb & -> & POST & POSTr & HQ' & Hnb & HCK' & HQG' & HAOX & HQCELL & HLPs & HDRN).
cbn [fst snd] in POST, POSTr, HQ', HCK', HQG', HAOX, HQCELL, HLPs, HDRN.
assert (Qsd : st_qthread (qx S k z tr) = st_qthread S).
{ unfold qx, depot_after, YFl0C.depot_after, dtick. destruct (z =? 0); reflexivity. }
assert (QB' : qc_bytes (st_qthread s') = DGgm.QBFv (req_size n) (st_qthread S)).
{ rewrite HQ', Qsd. rewrite Qsd in Hnb. destruct nb as [b|]; [|rewrite HNB in Hnb; discriminate].
  cbn [qc_push qc_bytes]. unfold DGgm.QBFv. rewrite HNB. unfold qk, ck_n. cbn [ck_req]. rewrite Hr. lia. }
assert (QBY : qc_bytes (st_qthread s') <= kQuarantineCacheMax) by (rewrite QB'; unfold DGgm.QBFv; exact Hcache).
assert (NOWN : forall b, ly_stk_lo ly <= b < ly_stk_hi ly -> ~ AOX ly (qx S k z tr) b /\ ~ AOX ly s' b).
{ intros b Hb.
  assert (NX : ~ AOX ly (qx S k z tr) b).
  { intros O. destruct (Fown_x inst ly S W mem md p n k z tr b HARX HRP HBLK Hf O) as [O'|O'];
    [exact (Fstack inst ly S W mem md b HARX Hb O') | exact (NBLK b Hb O')]. }
  split; [exact NX | intros O; exact (NX (HAOX b O))]. }
unfold dmd. cbn [bind get ibind].
replace (qc_bytes (st_qthread s') <=? kQuarantineCacheMax) with true
  by (symmetry; apply Z.leb_le; exact QBY).
cbn [ret amreal].
assert (RA : raZ (ms_regs msE) = 222228) by (unfold raZ; rewrite E1r; apply unsigned_lit_small; lia).
rewrite RA.
eapply SRr_mono.
{ apply (TAILM W W' ly S (qx S k z tr) s' regs mem inst so bp p n tr hb1 j1 j2 j3 msE
    (with_vm_backing (m_vm_lazy md) mat md) E5 regsE' memE' mdE' FH HshE HEn5 HS5 DMps NOWN POST
    ltac:(rewrite <- QB'; exact HQCELL) ltac:(unfold DGgm.QBFv; exact Hcache)). }
intros Wo co _ (-> & regsR & memR & mat' & -> & RCS & FRT & PRESR & VIS).
pose proof POST as (ARXe & LLE & WLE & CSe & SIO & FRv & PRSe).
assert (NOXx : forall x : word, ~ AOX ly S (bv_unsigned x) ->
  ~ (p <> PNull /\ sptr_addr B ly p <= bv_unsigned x < sptr_addr B ly p + req_size n) ->
  ~ AOX ly (qx S k z tr) (bv_unsigned x)).
{ intros x NO NE O. destruct (Fown_x inst ly S W mem md p n k z tr _ HARX HRP HBLK Hf O) as [O'|O'];
  [exact (NO O') | apply NE; split; [exact DVnn | exact O']]. }
assert (DMx : forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ ascratch B DFSTACK_G regs (bv_unsigned x) ->
  ~ (p <> PNull /\ sptr_addr B ly p <= bv_unsigned x < sptr_addr B ly p + req_size n) -> ms_mem msE x = mem x).
{ intros x NO NS NE. assert (Ra : 0 <= bv_unsigned x < 2 ^ 64) by apply u64_range.
  apply DMfr.
  - intros [Hs|[Hw|Hw]].
    + apply NS. left. unfold spZ, DFSTACK_G, DFSTACK, DGbaseC.DFSTACK in *. lia.
    + destruct (Fown inst ly S W mem md p n k _ HARX HRP HBLK Hf Ra
        ltac:(left; unfold DGgm.WINT, DGgmC.WINT in Hw; unfold DGgi.WINT, DGgiC.WINT; tauto)) as [O|O];
      [exact (NO O) | apply NE; split; [exact DVnn | exact O]].
    + unfold DGgm.WINB, DGgmC.WINB in Hw. destruct Hw as [Hw|Hw].
      * destruct (Fown inst ly S W mem md p n k _ HARX HRP HBLK Hf Ra ltac:(right; left; exact Hw)) as [O|O];
        [exact (NO O) | apply NE; split; [exact DVnn | exact O]].
      * destruct (Fown inst ly S W mem md p n k _ HARX HRP HBLK Hf Ra ltac:(right; right; left; exact Hw)) as [O|O];
        [exact (NO O) | apply NE; split; [exact DVnn | exact O]].
  - intros Hd. destruct (Fown inst ly S W mem md p n k _ HARX HRP HBLK Hf Ra
      ltac:(right; right; right; left; exact Hd)) as [O|O];
    [exact (NO O) | apply NE; split; [exact DVnn | exact O]].
  - intros Hi. exact (NO (Fown_i inst ly S W mem md _ HARX Hi)).
  - intros Hs. destruct (Fown inst ly S W mem md p n k _ HARX HRP HBLK Hf Ra
      ltac:(right; right; right; right; exact Hs)) as [O|O];
    [exact (NO O) | apply NE; split; [exact DVnn | exact O]]. }
assert (NSCR : forall x : word, ~ ascratch B DFSTACK_G regs (bv_unsigned x) ->
  ~ ascratch B QSTACK (ms_regs msE) (bv_unsigned x)).
{ intros x NS [Hs|Hs]; [rewrite SPE in Hs; apply NS; left; unfold spZ, DFSTACK_G, QSTACK in *; lia
  | apply NS; right; exact Hs]. }
assert (RAWC : acall_raw_x B AOX inst YFewC.QSTACK ly (qx S k z tr) W (ms_regs msE) (ms_mem msE)
    (with_vm_backing (m_vm_lazy md) mat md) (fun _ => False) ly s' W' regsE' memE' mdE' ->
  forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ AOX ly s' (bv_unsigned x) ->
  ~ ascratch B DFSTACK_G regs (bv_unsigned x) ->
  ~ (p <> PNull /\ sptr_addr B ly p <= bv_unsigned x < sptr_addr B ly p + req_size n) -> memR x = mem x).
{ intros FRraw x NO NO' NS NE. unfold acall_raw_x in FRraw.
  assert (NSS : ~ (bv_unsigned (getr regs 2) - 80 <= bv_unsigned x < bv_unsigned (getr regs 2)))
    by (intros Hw; apply NS; left; unfold spZ, DFSTACK_G; lia).
  rewrite (FRT x NSS). rewrite (FRraw x (NOXx x NO NE) NO' (NSCR x NS) ltac:(intros [])).
  exact (DMx x NO NS NE). }
exists regsR, memR, (with_vm_backing (m_vm_lazy mdE') mat' mdE').
split; [unfold raZ; reflexivity|].
split; [|split; [exact (HLPs QBY)|]].
2:{ exists (qx S k z tr), (ms_regs msE), (ms_mem msE), (with_vm_backing (m_vm_lazy md) mat md), regsE', memE', mdE'.
  split; [exact POSTr|]. split; [exact RAWC|]. split; [exact DMfr | exact FRT]. }
split.
{ apply (Fframe inst ly s' W' memE' mdE' memR (with_vm_backing (m_vm_lazy mdE') mat' mdE') ARXe).
  - intros b Rb HO. apply aview_same. apply FRT. rewrite unsigned_lit_small by exact Rb.
    intros Hw.
    assert (Hstk : ly_stk_lo ly <= b < ly_stk_hi ly)
      by (clear - Hw Hlo Hhi; unfold spZ, DFSTACK_G in *; lia).
    destruct (NOWN b Hstk) as [_ N2]. exact (N2 HO).
  - exact VIS.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros b Hband Hh. apply FRT. unfold w64. rewrite unsigned_lit_small.
    + clear - Hband Hlo LB. unfold in_band_rw, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hband.
      unfold spZ in Hlo. numc. lia.
    + clear - Hband. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *. lia. }
split; [apply layout_le_refl|]. split; [exact WLE|].
split; [exact (aregs_of_cs regs (sptr_addr B ly p) inst bp so regsR RCS)|].
split.
{ clear - SIO. unfold same_io in *. destruct md, mdE'. cbn in SIO |- *. intuition congruence. }
split.
{ intros b Rb NO NO' NS NE.
  assert (Ex : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit_small; exact Rb).
  transitivity (aview tfibsegs (w_H W') memE' b).
  { apply aview_same. apply (FRT (Z_to_bv 64 b)). rewrite Ex. intros Hw. apply NS. left. unfold spZ, DFSTACK_G. lia. }
  transitivity (aview tfibsegs (w_H W) (ms_mem msE) b).
  { apply FRv; [exact Rb | | exact NO' | | intros []].
    - rewrite <- Ex. apply (NOXx (Z_to_bv 64 b)); rewrite Ex; assumption.
    - rewrite <- Ex. apply (NSCR (Z_to_bv 64 b)). rewrite Ex. exact NS. }
  apply aview_same. apply (DMx (Z_to_bv 64 b)); rewrite Ex; assumption. }
intros b Hb. apply PRESR. unfold spZ, DFSTACK_G in Hb. unfold DFSTACK. exact Hb.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The arm.                                                                                                         *)
Theorem dealloc_mid : forall inst so bp ly S W regs mem md p n tr,
DeallocG.dealloc_pre tfibsegs B U ARX rpre fpre 1 inst so bp ly S W regs mem md p n tr ->
In (p, n) (blocks S) -> need_new_batch (st_qthread S) = true ->
qc_bytes (st_qthread S) + req_size n + (if need_new_batch (st_qthread S) then kBatchBytes else 0) <= kQuarantineCacheMax ->
amreal tfibsegs (ft p tr S) W (cfg_at tfibsegs 0x31c50 regs mem md)
(DIfaceR.dealloc_leaf_b B ft ARX AOX lpost rawb inst ly S W regs mem md p n tr).
Proof.
intros inst so bp ly S W regs mem md p n tr PRE HBLK HNB Hcache.
pose proof (mid_walk (rawif rawb (acall_raw_x B AOX)) ENQb inst so bp ly S W regs mem md p n tr PRE HBLK HNB Hcache)
  as MAIN.
eapply amreal_mono; [| exact (amreal_apath_gflag tfibsegs _ _ _ _ MAIN)].
intros r Wo co [(regsR & memR & mdR & -> & HPOST & HLP & X & regsC & memC & mdC & regsE & memE & mdE & HX & RAWC & _)
  HPATH].
exists ly, regsR, memR, mdR. split; [reflexivity|]. split; [exact HPOST|].
split; [intros Hrb; exact (RAWC (HX Hrb))|].
split; [exact HLP | exact HPATH].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The arm with errno kept: Enqueue's contract at the leaf's errno form, and ErrnoApart's image facts for the zones
   the frames exclude (dmem_m's window, the depot and internal allocator zones, the block's shadow, Put's stack
   window).                                                                                                         *)
Hypothesis ENQe : DGleafE.enq_spec_b_e B U ARX AOX rpre lpost fpre dpost L24 QB rawb.
Hypothesis EAimg : ErrnoApart.errno_in_img.
Hypothesis EAz3 : ErrnoApart.errno_apart_zone3_d.
Hypothesis EAdz : ErrnoApart.errno_apart_dzone_d.
Hypothesis EAiz : ErrnoApart.errno_apart_izone.

Theorem dealloc_mid_e : forall inst so bp ly S W regs mem md p n tr,
DeallocG.dealloc_pre tfibsegs B U ARX rpre fpre 1 inst so bp ly S W regs mem md p n tr ->
In (p, n) (blocks S) -> need_new_batch (st_qthread S) = true ->
qc_bytes (st_qthread S) + req_size n + (if need_new_batch (st_qthread S) then kBatchBytes else 0) <= kQuarantineCacheMax ->
amreal tfibsegs (ft p tr S) W (cfg_at tfibsegs 0x31c50 regs mem md)
(DGleafE.dealloc_leaf_b_e B ft ARX AOX lpost rawb inst ly S W regs mem md p n tr).
Proof.
intros inst so bp ly S W regs mem md p n tr PRE HBLK HNB Hcache.
pose proof (mid_walk (DGleafE.acall_e_b rawb B AOX) ENQe inst so bp ly S W regs mem md p n tr PRE HBLK HNB Hcache)
  as MAIN.
destruct PRE as (HARX & HRP & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & Hpres & Hgp & Htp & Hr10 & Hr11 & Hr12 & Hr13 & Hr14 & Hr15 &
Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htrlen & PSO & PLEN & PBUF & Htr & Hp0 & HFP).
destruct (Fview inst ly S W mem md p n HARX HRP HFP HBLK) as [[LY IMG _ _ _ _ _] _ _ _ _ _ _ (HZp & _ & _ & HNN) _ _].
assert (Hpa : 0 <= sptr_addr B ly p) by (destruct HZp as [Z0 _]; lia).
assert (HSP : ly_stk_lo ly + DGbaseC.DFSTACK <= bv_unsigned (getr regs 2))
  by (unfold DGbaseC.DFSTACK, DFSTACK_G, spZ in *; lia).
assert (EB : forall i, 0 <= i < 4 -> bv_unsigned (w64 (as_errno B + i)) = as_errno B + i)
  by (intros i Hi; rewrite (ts_errno B TS); unfold w64; apply unsigned_lit_small; unfold TFIB_ERRNO; lia).
eapply amreal_mono; [| exact (amreal_apath_gflag tfibsegs _ _ _ _ MAIN)].
intros r Wo co [(regsR & memR & mdR & -> & HPOST & HLP & X & regsC & memC & mdC & regsE & memE & mdE & HX & RAWC & DMC & FRT)
  HPATH].
(* errno from Deallocate's entry to Enqueue's call: outside dmem_m's window, the depot zone, the internal allocator's
   zone and the block's shadow *)
assert (ERRC : ErrnoG.errno_kept B mem memC).
{ intros i Hi. apply DMC; rewrite (EB i Hi); intros Hw.
  - apply (ErrnoApart.errno_apart_dwin_m EAimg EAz3 B ly _ _ _ _ TS LY IMG HSP HZp (proj1 HNN) Hw). lia.
  - apply (EAdz B ly _ TS LY IMG Hw). lia.
  - apply (EAiz B _ TS Hw). lia.
  - apply (ErrnoApart.errno_apart_dshadow EAimg B ly _ _ _ TS LY IMG Hpa Hw). lia. }
(* errno from Enqueue's return to Put's ret: outside Put's stack window *)
assert (ERRT : ErrnoG.errno_kept B memE memR).
{ intros i Hi. apply FRT. rewrite (EB i Hi). intros Hw.
  refine (ErrnoApart.errno_apart_stack EAimg B ly _ _ _ TS LY IMG _ Hw _); unfold DFSTACK_G, spZ in *; lia. }
exists ly, regsR, memR, mdR. split; [reflexivity|]. split; [exact HPOST|].
split; [intros Hrb; exact (RAWC (DGleafE.acall_e_b_raw _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HX Hrb))|].
split; [exact (errno_through rawb B W Wo mem memC memE memR ERRC
  (DGleafE.acall_e_b_errno _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HX) ERRT)|].
split; [exact HLP | exact HPATH].
Qed.
End e.
End d.
About dealloc_mid.
