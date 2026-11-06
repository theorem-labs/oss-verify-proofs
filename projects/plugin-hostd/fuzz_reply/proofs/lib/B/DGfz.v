(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DGfz.v (commit 30a1993588f, c5 + memnorm; file sha256 f72607ef7c18) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 22 image addresses moved by code-verified function pairs (21 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 2 pcs named in comments; 1 hand maps (agreloc-resolve-R.tsv, each with its evidence: pinned image bytes, YImgTop, the unit AF twin); no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from lib/A/DGfz.v (commit d2dafa219c1, file sha256 5c5f57524f89) onto plugin-hostd/fuzz_reply's asan-ubsan image (unstripped fuzz_reply.asan-ubsan, sha256 3389287e1d61; pin 10ffb5f9202a) by alreloc ced0368250cb6538 (A -> B, direct map 541d2a13b9d2): 23 numerals moved; module paths lib.A -> lib.B and the image twins A<r> -> Y<r>. *)
(* The drain arm of the frame-generic Deallocate contract (DIfaceR.dealloc_leaf_b rawb), over the interface
   DGif0.DIface and the section's Enqueue / Drain contracts [ENQb] / [DRNb] (DIfaceR.enq_spec_b / drain_spec_b rawb).

   Ported from cgif_file's released free walk (afree_drn, YFfz) with the caller's frame made abstract: after
   QuarantineCache::Enqueue returns into Put (0x360e0), the cache is over its bound, so Put calls
   Quarantine::Drain ([DRNb], a0 = inst + o_quar), then Put and Deallocate return.
   The leaf's ARX comes from the drain's post and the interface's frame law, its lpost from di_lpost_d (the drain
   tree's path), its aview frame from the enqueue's and the drain's aview frames, its raw frame (when rawb = true)
   from their raw conjuncts, di_owned_x and the walk's agreement at the Enqueue call, its path clause from
   AGif0n.amreal_apath_gflag.
   The walk from Deallocate's entry to Enqueue's return is DGg1.to_enq followed by [ENQb] (Lemma mid_walk).
   dealloc_drn_e is the errno-kept twin (DGleafE.dealloc_leaf_b_e rawb), over the errno-kept contracts [ENQe] / [DRNe]
   (DGleafE.enq_spec_b_e / drain_spec_b_e) and ErrnoApart's image facts: the same walk, through mid_walk_x / TAILD_x
   (mid_walk / TAILD with the raw facts their walks derive), composed by errno_chain. *)
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
(* ErrnoG and ErrnoApart Require YA09, whose non-local [Ltac ::=] turns zify's euclidean-division
   conversion off in every file that Requires it; this file's proofs were written with it on (mid_walk_x's [lia] on
   the stack bounds fails without it), so it is turned back on here, for this file only. *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
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
Lemma qx_qglobal : forall S k z tr, st_qglobal (qx S k z tr) = st_qglobal S.
Proof. intros S k z tr. unfold qx, depot_after, YFl0C.depot_after, dtick. destruct (z =? 0); reflexivity. Qed.

(* errno through the drain arm's walk, at the leaf's form: the walk's raw agreement on errno's bytes at each step
   (entry to Enqueue's call [memE], Enqueue's return [mem5] to Drain's call [memC], Drain's return [mem6] to the leaf
   [memR]), composed with the Enqueue's and the Drain's errno conjuncts (DGleafE.acall_e_b_errno). *)
Lemma errno_chain : forall (rb : bool) (B : asyms) (W W5 W6 : world tfibsegs) (mem memE mem5 memC mem6 memR : word -> option byte),
0 <= as_errno B -> as_errno B + 4 <= 2 ^ 64 ->
(forall x : word, as_errno B <= bv_unsigned x < as_errno B + 4 -> memE x = mem x /\ memC x = mem5 x /\ memR x = mem6 x) ->
DGleafE.errno_kept_b rb B W W5 memE mem5 -> DGleafE.errno_kept_b rb B W5 W6 memC mem6 ->
DGleafE.errno_kept_b rb B W W6 mem memR.
Proof.
intros [|] B W W5 W6 mem memE mem5 memC mem6 memR L0 L1 K EE ED.
- intros i Hi.
  assert (Ei : bv_unsigned (w64 (as_errno B + i)) = as_errno B + i) by (unfold w64; apply unsigned_lit_small; lia).
  destruct (K (w64 (as_errno B + i)) ltac:(rewrite Ei; lia)) as (A1 & A2 & A3).
  rewrite A3, (ED i Hi), A2, (EE i Hi), A1. reflexivity.
- intros a Ha.
  assert (Ea : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; lia).
  destruct (K (Z_to_bv 64 a) ltac:(rewrite Ea; lia)) as (A1 & A2 & A3).
  transitivity (aview tfibsegs (w_H W6) mem6 a); [exact (aview_same _ _ _ a A3)|].
  transitivity (aview tfibsegs (w_H W5) memC a); [exact (ED a Ha)|].
  transitivity (aview tfibsegs (w_H W5) mem5 a); [exact (aview_same _ _ _ a A2)|].
  transitivity (aview tfibsegs (w_H W) memE a); [exact (EE a Ha)|].
  exact (aview_same _ _ _ a A1).
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
(* DIface's memory predicate at Put's call of Enqueue; the walk takes it at Deallocate's entry memory (Section f's
   HMP) and carries it to the call by MP_keep. *)
Variable MP : (word -> option byte) -> Prop.
(* [rawb = true]: the leaf's raw frame too (the callees' raw posts from ENQb / DRNb). *)
Variable rawb : bool.
Hypothesis IF : DIface B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP.
Hypothesis ENQb : enq_spec_b B U ARX AOX rpre lpost fpre dpost L24 QB MP rawb.
Hypothesis DRNb : drain_spec_b B ARX AOX dbody L24 QB rawb.
(* The keep law of MP: a memory equal to the seed's entry memory outside dmem_m's frame zones (the walk's stack
   window and thread / block cells DGif0.dwin_m, the depot zone, the internal allocator's zone, the block's shadow),
   over the seed's geometry DGgm.free_hyps, keeps MP.  cgif (MP := fun _ => True): trivial; cf: MP_keep_cf. *)
Hypothesis MP_keep : forall W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU (mem' : word -> option byte),
  DGgm.free_hyps W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU ->
  (forall x : word, ~ dwin_m ly (bv_unsigned (getr regs0 2)) p (bv_unsigned x) -> ~ dg_dzone ly (bv_unsigned x) ->
    ~ dg_izone (bv_unsigned x) -> ~ dshadow p nn (bv_unsigned x) -> mem' x = mem0 x) ->
  MP mem0 -> MP mem'.
(* For the errno-kept twin (dealloc_drn_e): the Enqueue / Drain contracts with errno at the leaf's form, and
   ErrnoApart's image facts (errno lies in the image window, apart from an application zone, the depot zone and the
   internal allocator's zone). *)
Hypothesis ENQe : DGleafE.enq_spec_b_e B U ARX AOX rpre lpost fpre dpost L24 QB MP rawb.
Hypothesis DRNe : DGleafE.drain_spec_b_e B ARX AOX dbody L24 QB rawb.
Hypothesis EAimg : ErrnoApart.errno_in_img.
Hypothesis EAz3 : ErrnoApart.errno_apart_zone3_d.
Hypothesis EAdz : ErrnoApart.errno_apart_dzone_d.
Hypothesis EAiz : ErrnoApart.errno_apart_izone.

(* An extra callee conjunct that gives the raw one back (DIfaceR.rawif rawb acall_raw_x): the conjunct of [ENQb] /
   [DRNb] itself, and DGleafE.acall_e_b (DGleafE.acall_e_b_raw). *)
Definition xr_raw (XR : fxrel) : Prop :=
forall inst stk ly S W regs mem md E ly' S' W' regs' mem' md',
XR inst stk ly S W regs mem md E ly' S' W' regs' mem' md' ->
rawif rawb (acall_raw_x B AOX) inst stk ly S W regs mem md E ly' S' W' regs' mem' md'.

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

(* The leaf without its path clause (the arm adds it at the end through amreal_apath_gflag). *)
Definition leaf0 (r : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
dealloc_post tfibsegs B ARX AOX inst ly S W regs mem md (fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n)
  ly' (snd r) W' regs' mem' md' /\
(rawb = true -> forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ AOX ly' (snd r) (bv_unsigned x) ->
  ~ ascratch B DFSTACK_G regs (bv_unsigned x) ->
  ~ (p <> PNull /\ sptr_addr B ly p <= bv_unsigned x < sptr_addr B ly p + req_size n) -> mem' x = mem x) /\
lpost (snd r).

(* leaf0 with the raw facts of Put's tail (TAILD_x): Put's run to Drain keeps every byte off Put's 80-byte frame (the
   memory at Drain's call [memC] against Enqueue's return memory [mem5]), the drain's extra conjunct [XRd], and Put's
   run after Drain keeps every byte off the frame (the leaf's memory against Drain's return memory [mem6]). *)
Definition leaf0x (XRd : fxrel) (X5 : astate) (W5 : world tfibsegs) (mem5 : word -> option byte)
(r : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
dealloc_post tfibsegs B ARX AOX inst ly S W regs mem md (fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n)
  ly' (snd r) W' regs' mem' md' /\
(rawb = true -> forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ AOX ly' (snd r) (bv_unsigned x) ->
  ~ ascratch B DFSTACK_G regs (bv_unsigned x) ->
  ~ (p <> PNull /\ sptr_addr B ly p <= bv_unsigned x < sptr_addr B ly p + req_size n) -> mem' x = mem x) /\
lpost (snd r) /\
exists regsC memC mdC regs6 mem6 md6,
(forall x : word, ~ (sp0 - 80 <= bv_unsigned x < sp0) -> memC x = mem5 x) /\
XRd inst YFeuC.DSTACK ly X5 W5 regsC memC mdC (fun _ => False) ly (snd r) W' regs6 mem6 md6 /\
(forall x : word, ~ (sp0 - 80 <= bv_unsigned x < sp0) -> mem' x = mem6 x).

(* leaf0 with errno kept at the leaf's form (DGleafE.dealloc_leaf_b_e without its path clause). *)
Definition leaf0e (r : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
dealloc_post tfibsegs B ARX AOX inst ly S W regs mem md (fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n)
  ly' (snd r) W' regs' mem' md' /\
(rawb = true -> forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ AOX ly' (snd r) (bv_unsigned x) ->
  ~ ascratch B DFSTACK_G regs (bv_unsigned x) ->
  ~ (p <> PNull /\ sptr_addr B ly p <= bv_unsigned x < sptr_addr B ly p + req_size n) -> mem' x = mem x) /\
DGleafE.errno_kept_b rawb B W W' mem mem' /\
lpost (snd r).

(* The machine at Enqueue's return into Put (0x360e0): the seed's symbolic state at the call (DGfw.SS_E over an
   env agreeing with the DGgm seed's E0), the enqueue's post (di_enqueue) and the walk's agreement with the entry
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

(* TAILD with the raw facts its walk derives (leaf0x), over any drain contract whose extra conjunct [XRd] gives the
   raw one back (xr_raw). *)
Lemma TAILD_x : forall (XRd : fxrel), drain_spec_g B ARX AOX dbody L24 QB XRd -> xr_raw XRd ->
forall z msE matE E5 (W5 : world tfibsegs) regs' mem' md' (X' : astate) nb,
enq_ret k hb1 j1 j2 j3 z msE matE E5 W5 regs' mem' md' X' nb ->
amreal tfibsegs (dmd dbody X') W5 (cfg_at tfibsegs 0x360e0 regs' mem' md') (leaf0x XRd X' W5 mem').
Proof.
intros XRd DRNg XRdr z msE matE E5 W5 regs' mem' md' X' nb ER.
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
- intros O. destruct (di_owned_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md p n k z tr a HARX0 HRP HBLK HK O) as [O'|O'].
  + exact (di_stack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md a HARX0 Ha O').
  + pose proof (DGgm.fh_Hp_static _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as PST.
    pose proof (DGgm.N8_ge _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as (_ & N8b & _).
    assert (Hb : pa <= a < pa + nn) by exact O'.
    destruct (PST a ltac:(clear - Hb N8b; lia)) as [N1 _]. exact (N1 Ha).
- exact (di_stack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly X' W5 mem' md' a HA5 Ha). }
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
apply amreal_after_SRr.
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
{ apply (di_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly X' W5 mem' md' (ms_mem msC) _ HA5).
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
pose proof (di_inst _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md HARX0) as (I1 & I2 & _). unfold w64. rewrite unsigned_lit_small by lia. unfold o_quar. f_equal; lia. }
eapply amreal_then_SRr.
{ exact (amreal_apath_gflag tfibsegs _ _ _ _ (DRNg inst ly X' W5 (ms_regs msC) (ms_mem msC) (with_vm_backing (m_vm_lazy md') matC md') DPRE)). }
intros [[] X''] W6 c6 [(regs6 & mem6 & md6 & -> & POST6 & POST6x) (trc & HPATH6 & HG6)].
pose proof (XRdr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ POST6x) as POST6r. cbn [fst snd] in POST6, POST6r, POST6x |- *.
pose proof POST6 as (HA6 & LLE6 & WLE6 & CS6 & SIO6 & FR6 & PRS6).
change YFeuC.DSTACK with DSTACK in FR6, PRS6. change (@ImgBase.im_segs AImg_reply) with tfibsegs in FR6, PRS6.
assert (HLP : lpost X'').
{ exact (di_lpost_d _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md p n tr k z nb X' W5 mem' md' trc (tt, X'') HARX0 HRP HBLK HTU HK HKS
  ltac:(rewrite HQ'; reflexivity) ltac:(exact Hnb) HCK' HQG' HA5 DRX' HPATH6 HG6). }
unfold ascratch, spZ, raZ in FR6, PRS6 |- *. rewrite C2 in FR6, PRS6. rewrite C1.
rewrite !unsigned_lit_small in FR6, PRS6 |- * by (clear - Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, DFSTACK in *; unfold sp0 in *; lia).
assert (NOWN6 : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> ~ AOX ly X' a /\ ~ AOX ly X'' a).
{ intros a Ha. split.
- exact (proj2 (NOWN a Ha)).
- exact (di_stack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly X'' W6 mem6 md6 a HA6 Ha). }
assert (AGS6 : forall a, sp0 - 80 <= a < ly_stk_hi ly -> aview tfibsegs (w_H W6) mem6 a = aview tfibsegs (w_H W5) (ms_mem msC) a).
{ intros a Ha. destruct (NOWN6 a ltac:(clear - Ha Hlo; unfold DFSTACK in *; lia)) as [N1 N2]. apply FR6; [clear - Ha Usp Hlo Hhi LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, kHighMemEnd, DFSTACK in *; unfold sp0 in *; lia | exact N1 | exact N2 | | intros []].
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
{ destruct (NOWN6 a ltac:(clear - Ha Hlo Hhi; unfold DFSTACK in *; lia)) as [M1 M2]; apply FR6; [clear - Ha Usp Hlo LB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, spZ, kHighMemBeg, DFSTACK in *; unfold sp0 in *; lia | exact M1 | exact M2 | | intros []].
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
{ intros OX. destruct (di_owned_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md p n k z tr a HARX0 HRP HBLK HK OX) as [O|O]; [exact (NO O)|].
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
split; [|split; [apply layout_le_refl | split; [eapply wle_trans; [exact WLE | exact WLE6] | split; [|split; [|split]]]]].
-
apply (di_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly X'' W6 mem6 md6 (ms_mem msR) _ HA6).
+ intros a Ha HO. apply AGT; [exact Ha|]. intros Hs. apply (di_stack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly X'' W6 mem6 md6 a HA6); [|exact HO]. clear - Hs Hlo Hhi; unfold spZ, DFSTACK in *; unfold sp0 in *; lia.
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
intros a Ha NO NO'' NS NE.
assert (NOX : ~ AOX ly X a).
{ intros OX. destruct (di_owned_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md p n k z tr a HARX0 HRP HBLK HK OX) as [O|O]; [exact (NO O)|].
apply NE. split; [exact PNN | exact O]. }
assert (NOX' : ~ AOX ly X' a) by (intros O; apply NOX; exact (HOWN' a O)).
assert (NS1 : ~ (sp0 - 80 <= a < sp0)) by (intros Hs; apply NS; unfold ascratch; left; clear - Hs; unfold spZ, DFSTACK_G; unfold sp0 in *; lia).
rewrite (AGT a Ha NS1).
rewrite FR6; [| exact Ha | exact NOX' | exact NO'' | | intros []].
2:{ intros [Hs|Hs]; apply NS; unfold ascratch; [left; clear - Hs; unfold spZ, DSTACK, DFSTACK_G in *; unfold sp0 in *; lia | right; first [exact Hs | rewrite (ts_errno _ TS); exact Hs | rewrite (ts_errno _ TS) in Hs; exact Hs] ]. }
rewrite (AGC a Ha NS1).
rewrite FR; [| exact Ha | exact NOX | exact NOX' | | intros []].
2:{ intros [Hs|Hs]; apply NS; unfold ascratch; [left; clear - Hs; unfold spZ, QSTACK, DFSTACK_G in *; unfold sp0 in *; lia | right; first [exact Hs | rewrite (ts_errno _ TS); exact Hs | rewrite (ts_errno _ TS) in Hs; exact Hs] ]. }
apply AGP; [exact Ha | exact NO | exact NS |]. intros Hb. apply NE. exact (conj PNN Hb).
-
intros a Ha. apply PRESR. unfold spZ, DFSTACK_G in Ha. exact Ha.
Qed.

Lemma TAILD : forall z msE matE E5 (W5 : world tfibsegs) regs' mem' md' (X' : astate) nb,
enq_ret k hb1 j1 j2 j3 z msE matE E5 W5 regs' mem' md' X' nb ->
amreal tfibsegs (dmd dbody X') W5 (cfg_at tfibsegs 0x360e0 regs' mem' md') leaf0.
Proof.
intros z msE matE E5 W5 regs' mem' md' X' nb ER.
eapply amreal_mono; [| exact (TAILD_x (rawif rawb (acall_raw_x B AOX)) DRNb (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H => H)
  z msE matE E5 W5 regs' mem' md' X' nb ER)].
intros r W' c' (ly' & regsR & memR & mdR & Hc & HP & HR & HL & _).
exists ly', regsR, memR, mdR. exact (conj Hc (conj HP (conj HR HL))).
Qed.
End g.

(* The walk from Deallocate's entry to Enqueue's return: DGg1.to_enq to Put's call of QuarantineCache::Enqueue, then
   the Enqueue contract [ENQg] (any extra conjunct [XRq] that gives the raw one back, xr_raw), continued by any proof
   of the rest of the tree from Enqueue's return; the continuation also gets [XRq] and the walk's raw agreement with
   the entry memory at the call (dmem_m's frame). *)
Lemma mid_walk_x : forall (XRq : fxrel), enq_spec_g B U ARX AOX rpre lpost fpre dpost L24 QB MP XRq -> xr_raw XRq ->
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
     amreal tfibsegs (dmd dbody X') W5 (cfg_at tfibsegs 0x360e0 regs' mem' md') Q) ->
  amreal tfibsegs (ft p tr S) W (cfg_at tfibsegs 0x3191c regs mem md) Q.
Proof.
intros XRq ENQg XRqr k hb1 j1 j2 j3 HK HKS Hhb1 Hhdr FH Q CONT.
pose proof PRE as P. unfold DeallocG.dealloc_pre in P.
destruct P as (HARX & HRP & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & Hpres & Hgp & Htp & Hr10 & Hr11 & Hr12 & Hr13 & Hr14 & Hr15 &
  Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htrlen & PSO & PLEN & PBUF & Htr & Hp0 & HFP).
pose proof (DGgm.derived_ranges _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as DR.
pose proof (DGgm.LYB _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as LB.
assert (RG3 : getr (dregs regs (sptr_addr B ly p) inst bp so) 3 = getr regs 3) by (apply dregs_other; vm_compute; discriminate).
assert (Upa : 0 <= sptr_addr B ly p < 2 ^ 64) by (change (sptr_addr B ly p) with pa; clear - DR; ceil; unfold ASAN_CEIL in *; lia).
apply (DGg1.to_enq B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF TS
  inst so bp ly S W regs mem md p n tr k hb1 j1 j2 j3 Q PRE HBLK HK HKS Hhb1 Hhdr FH).
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
eapply YG0d.amreal_mbind.
{ apply (ENQg inst ly S W mem md p n tr k z hb1 (bv_unsigned (getr regs 2))
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
intros a s' W' c' HPOST'.
destruct HPOST' as (regsE' & memE' & mdE' & nb & -> & POST & POSTr & HQ' & Hnb & HCK' & HQG' & HAOX & HQCELL & HLPs & HDRN).
cbn [fst snd] in POST, POSTr, HQ', HCK', HQG', HAOX, HQCELL, HLPs, HDRN.
assert (RA : raZ (ms_regs msE) = 221408) by (unfold raZ; rewrite E1r; apply unsigned_lit_small; lia).
rewrite RA.
apply (CONT z msE mat E5 W' regsE' memE' mdE' s' nb); [| exact POSTr | exact DMfr].
unfold enq_ret. cbv zeta.
split; [exact HshE|]. split; [exact HEn5|]. split; [exact HS5|]. split; [exact DMps|].
split; [exact POST|]. split; [exact (XRqr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ POSTr)|]. split; [exact HQ'|]. split; [exact Hnb|]. split; [exact HCK'|]. split; [exact HQG'|].
split; [exact HAOX|]. split; [exact HDRN|]. split; [exact HQCELL|].
(* the walk's raw agreement with the entry memory at the call (dmem_m's frame, the owned set) *)
intros x NO NS NE. assert (Ra : 0 <= bv_unsigned x < 2 ^ 64) by apply u64_range.
apply DMfr.
- intros [Hs|[Hw|Hw]].
  + apply NS. left. unfold spZ, DFSTACK_G, DFSTACK, DGbaseC.DFSTACK in *. lia.
  + destruct (di_owned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md p n k _ HARX HRP HBLK HK Ra
      ltac:(left; unfold DGgm.WINT, DGgmC.WINT in Hw; unfold DGgi.WINT, DGgiC.WINT; tauto)) as [O|O]; [exact (NO O) | exact (NE O)].
  + unfold DGgm.WINB, DGgmC.WINB in Hw. destruct Hw as [Hw|Hw].
    * destruct (di_owned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md p n k _ HARX HRP HBLK HK Ra
        ltac:(right; left; exact Hw)) as [O|O]; [exact (NO O) | exact (NE O)].
    * destruct (di_owned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md p n k _ HARX HRP HBLK HK Ra
        ltac:(right; right; left; exact Hw)) as [O|O]; [exact (NO O) | exact (NE O)].
- intros Hd. destruct (di_owned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md p n k _ HARX HRP HBLK HK Ra
    ltac:(right; right; right; left; exact Hd)) as [O|O]; [exact (NO O) | exact (NE O)].
- intros Hi. exact (NO (di_owned_i _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md _ HARX Hi)).
- intros Hs. destruct (di_owned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md p n k _ HARX HRP HBLK HK Ra
    ltac:(right; right; right; right; exact Hs)) as [O|O]; [exact (NO O) | exact (NE O)].
Qed.

(* mid_walk_x over the section's Enqueue contract [ENQb]. *)
Lemma mid_walk : forall k hb1 j1 j2 j3,
  find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
  0 <= hb1 < 256 -> val_mem tfibsegs (mrestrict (w_H W) mem) (sptr_addr B ly p - 16) 4 (2 + 256 * hb1) ->
  DGgm.free_hyps W ly regs0 mem tr pa nn hb1 q j1 j2 j3 regs ->
  forall (Q : unit * astate -> world tfibsegs -> config -> Prop),
  (forall z msE matE E5 W5 regs' mem' md' X' nb, enq_ret k hb1 j1 j2 j3 z msE matE E5 W5 regs' mem' md' X' nb ->
     amreal tfibsegs (dmd dbody X') W5 (cfg_at tfibsegs 0x360e0 regs' mem' md') Q) ->
  amreal tfibsegs (ft p tr S) W (cfg_at tfibsegs 0x3191c regs mem md) Q.
Proof.
intros k hb1 j1 j2 j3 HK HKS Hhb1 Hhdr FH Q CONT.
apply (mid_walk_x (rawif rawb (acall_raw_x B AOX)) ENQb (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H => H)
  k hb1 j1 j2 j3 HK HKS Hhb1 Hhdr FH Q).
intros z msE matE E5 W5 regs' mem' md' X' nb ER _ _. exact (CONT z msE matE E5 W5 regs' mem' md' X' nb ER).
Qed.

Theorem drain_arm_c : amreal tfibsegs (ft p tr S) W (cfg_at tfibsegs 0x3191c regs mem md)
  (DIfaceR.dealloc_leaf_b B ft ARX AOX lpost rawb inst ly S W regs mem md p n tr).
Proof.
pose proof PREd as (HARX & HRP & _ & _ & _ & _ & _ & _ & _ & _ & HFP).
pose proof (di_view _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md p n HARX HRP HFP HBLK) as DV.
destruct (dv_chunk _ _ _ _ _ _ _ _ DV) as (k & HK & HKS & _ & HKR).
pose proof (dv_nonnull _ _ _ _ _ _ _ _ DV) as PNN.
pose proof (di_inst _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md HARX) as HIO.
destruct (DGg1.FH_m B TS U ARX rpre fpre inst so bp ly S W regs mem md p n tr PRE HBLK HIO DV) as (hb1 & j1 & j2 & j3 & Hhb1 & Hhdr & FH).
pose proof (mid_walk k hb1 j1 j2 j3 HK HKS Hhb1 Hhdr FH leaf0
  (fun z msE matE E5 W5 regs' mem' md' X' nb ER => TAILD k hb1 j1 j2 j3 HK HKS HKR PNN FH z msE matE E5 W5 regs' mem' md' X' nb ER)) as MAIN.
eapply amreal_mono; [| exact (amreal_apath_gflag tfibsegs _ _ _ _ MAIN)].
intros r W' c' [(ly' & regs' & mem' & md' & Hc & Hpost & Hraw & Hlp) HPATH].
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact Hpost|]. split; [exact Hraw|].
split; [exact Hlp | exact HPATH].
Qed.

(* drain_arm_c with errno kept at the leaf's form (DGleafE.dealloc_leaf_b_e), over the errno-kept Enqueue / Drain
   contracts [ENQe] / [DRNe]: the same walk (mid_walk_x, TAILD_x).  errno's bytes lie apart from Put's frame and from
   dmem_m's excluded windows (ErrnoApart), so the walk's raw facts keep them; the callees' errno conjuncts carry them
   across Enqueue and Drain (errno_chain). *)
Theorem drain_arm_c_e : amreal tfibsegs (ft p tr S) W (cfg_at tfibsegs 0x3191c regs mem md)
  (DGleafE.dealloc_leaf_b_e B ft ARX AOX lpost rawb inst ly S W regs mem md p n tr).
Proof.
pose proof PREd as (HARX & HRP & _ & _ & _ & Hlo & _ & _ & _ & _ & HFP).
pose proof (di_view _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md p n HARX HRP HFP HBLK) as DV.
destruct (dv_chunk _ _ _ _ _ _ _ _ DV) as (k & HK & HKS & _ & HKR).
pose proof (dv_nonnull _ _ _ _ _ _ _ _ DV) as PNN.
pose proof (di_inst _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md HARX) as HIO.
destruct (DGg1.FH_m B TS U ARX rpre fpre inst so bp ly S W regs mem md p n tr PRE HBLK HIO DV) as (hb1 & j1 & j2 & j3 & Hhb1 & Hhdr & FH).
(* errno's bytes: words in range, apart from Put's frame and from dmem_m's excluded windows (ErrnoApart) *)
pose proof (dv_n _ _ _ _ _ _ _ _ DV) as DN.
pose proof (dn_ly _ _ _ _ _ DN) as LY. pose proof (dn_img _ _ _ _ _ DN) as IMG.
destruct (dv_zone _ _ _ _ _ _ _ _ DV) as (Z3 & _ & _ & NN).
pose proof (DGgm.derived_ranges _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as (P0 & _).
assert (ER0 : 0 <= as_errno B /\ as_errno B + 4 <= 2 ^ 64).
{ destruct (EAimg B ly TS IMG) as [E1 _]. pose proof (ErrnoApart.errno_below_imgend EAimg B ly TS LY IMG) as E2.
  pose proof (lo_img ly LY) as (L1 & _). clear - E1 E2 L1. unfold kImgLo, kImgEnd in *. lia. }
assert (EW : forall x : word, as_errno B <= bv_unsigned x < as_errno B + 4 ->
  ~ (sp0 - 80 <= bv_unsigned x < sp0) /\ ~ dwin_m ly sp0 pa (bv_unsigned x) /\ ~ dg_dzone ly (bv_unsigned x) /\
  ~ dg_izone (bv_unsigned x) /\ ~ dshadow pa nn (bv_unsigned x)).
{ intros x Hx. set (a := bv_unsigned x) in *.
  split; [intros Hs; exact (ErrnoApart.errno_apart_stack EAimg B ly (sp0 - 80) sp0 a TS LY IMG
    ltac:(clear - Hlo; unfold DFSTACK in *; lia) Hs Hx)|].
  split; [intros Hw; exact (ErrnoApart.errno_apart_dwin_m EAimg EAz3 B ly sp0 pa nn a TS LY IMG Hlo Z3 (proj1 NN) Hw Hx)|].
  split; [intros Hd; exact (EAdz B ly a TS LY IMG Hd Hx)|].
  split; [intros Hi; exact (EAiz B a TS Hi Hx)|].
  intros Hs. exact (ErrnoApart.errno_apart_dshadow EAimg B ly pa nn a TS LY IMG ltac:(clear - P0; lia) Hs Hx). }
assert (MAIN : amreal tfibsegs (ft p tr S) W (cfg_at tfibsegs 0x3191c regs mem md) leaf0e).
{ apply (mid_walk_x (DGleafE.acall_e_b rawb B AOX) ENQe (DGleafE.acall_e_b_raw rawb B AOX) k hb1 j1 j2 j3 HK HKS Hhb1 Hhdr FH).
  intros z msE matE E5 W5 regs' mem' md' X' nb ER XE DMfr.
  eapply amreal_mono; [| exact (TAILD_x k hb1 j1 j2 j3 HK HKS HKR PNN FH (DGleafE.acall_e_b rawb B AOX) DRNe
    (DGleafE.acall_e_b_raw rawb B AOX) z msE matE E5 W5 regs' mem' md' X' nb ER)].
  intros r W' c' (ly' & regsR & memR & mdR & Hc & HP & HR & HL & regsC & memC & mdC & regs6 & mem6 & md6 & FR1 & XD & FRT).
  exists ly', regsR, memR, mdR. split; [exact Hc|]. split; [exact HP|]. split; [exact HR|]. split; [|exact HL].
  apply (errno_chain rawb B W W5 W' mem (ms_mem msE) mem' memC mem6 memR (proj1 ER0) (proj2 ER0)).
  - intros x Hx. destruct (EW x Hx) as (N1 & N2 & N3 & N4 & N5).
    split; [exact (DMfr x N2 N3 N4 N5)|]. split; [exact (FR1 x N1) | exact (FRT x N1)].
  - exact (DGleafE.acall_e_b_errno _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XE).
  - exact (DGleafE.acall_e_b_errno _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XD). }
eapply amreal_mono; [| exact (amreal_apath_gflag tfibsegs _ _ _ _ MAIN)].
intros r W' c' [(ly' & regs' & mem' & md' & Hc & Hpost & Hraw & He & Hlp) HPATH].
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact Hpost|]. split; [exact Hraw|]. split; [exact He|].
split; [exact Hlp | exact HPATH].
Qed.
End f.

(* The drain arm of the generic Deallocate statement. *)
Theorem dealloc_drn : forall inst so bp ly S W regs mem md p n tr,
DeallocG.dealloc_pre tfibsegs B U ARX rpre fpre 1 inst so bp ly S W regs mem md p n tr -> MP mem ->
In (p, n) (blocks S) ->
kQuarantineCacheMax < qc_bytes (st_qthread S) + req_size n + (if need_new_batch (st_qthread S) then kBatchBytes else 0) ->
amreal tfibsegs (ft p tr S) W (cfg_at tfibsegs 0x3191c regs mem md)
(DIfaceR.dealloc_leaf_b B ft ARX AOX lpost rawb inst ly S W regs mem md p n tr).
Proof.
intros inst so bp ly S W regs mem md p n tr PRE0 HMP0 HB DR.
exact (drain_arm_c inst so bp ly S W regs mem md p n tr PRE0 HMP0 HB DR).
Qed.

(* dealloc_drn with errno kept at the leaf's form (DGleafE.dealloc_leaf_b_e rawb), over the errno-kept Enqueue /
   Drain contracts [ENQe] / [DRNe] and ErrnoApart's image facts. *)
Theorem dealloc_drn_e : forall inst so bp ly S W regs mem md p n tr,
DeallocG.dealloc_pre tfibsegs B U ARX rpre fpre 1 inst so bp ly S W regs mem md p n tr -> MP mem ->
In (p, n) (blocks S) ->
kQuarantineCacheMax < qc_bytes (st_qthread S) + req_size n + (if need_new_batch (st_qthread S) then kBatchBytes else 0) ->
amreal tfibsegs (ft p tr S) W (cfg_at tfibsegs 0x3191c regs mem md)
(DGleafE.dealloc_leaf_b_e B ft ARX AOX lpost rawb inst ly S W regs mem md p n tr).
Proof.
intros inst so bp ly S W regs mem md p n tr PRE0 HMP0 HB DR.
exact (drain_arm_c_e inst so bp ly S W regs mem md p n tr PRE0 HMP0 HB DR).
Qed.
End e.
End d.
About dealloc_drn.
