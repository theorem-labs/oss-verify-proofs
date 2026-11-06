(* fuzz_state image B: the composed realloc contract.  a Theorem Labs lane's c5 composition (lib/Reusable/RGtop.v rg_realloc_all,
   relocated from proofs/cgif/cgif_file_fuzzer/lib/RGtop.v @ 2bd8ae006ef) at fs's image-B instance
   (lib/B/FSRealloc_inst.v fs_rg_realloc_all) with the five segments S1 / S2a / S2b / S3 / S4 discharged
   (lib/B/FSRealloc_S1.v .. FSRealloc_S4.v), and from it FSupoisonRealloc.FS_AREALLOC_BU, the contract fuzz_state's
   ALLOC lane assumes for image B (the B twin of FSW_realloc.v:496 fsw_aj_reallocU's FS_AREALLOC_AU premise).  What
   remains are a Theorem Labs lane's Allocate contract (AllocG.aalloc_realizes) and RAW Deallocate contract
   (DeallocG.adealloc_realizes_raw) at fs's pcA = tfib_A__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18Buffered
   StackTraceENS_9AllocTypeEb 0x31f64 / pcD = tfib_A__ZN6__asan9Allocator10DeallocateEPvmmPN11__sanitizer18Buffered
   StackTraceENS_9AllocTypeE 0x31c50 (YB1w's symbol names), for every user-poison set Up: the two named hypotheses.
   The B twin of a Theorem Labs lane's lib/A/FSRealloc_top.v (same route).

   Rule 24 (released-proof lookup): proves function __asan::Allocator::Reallocate chain composition on fs image B
   (fuzz_state.asan-ubsan sha256 5ac5ce0954f8...: __wrap_realloc 0x530e8 -> __interceptor_realloc 0x534e4 ->
   asan_realloc 0x328ec -> Allocator::Reallocate 0x32998).  proof-index, unpiped, 2026-10-29 ~03:55Z
   (internal path): `proof-index: end; 0x530e8: 0 named, 0 by address, 0 related,
   0 lemma(s), 0 by file name, an earlier delivery 0 named and 0 name(s) holding it`; the same for 0x534e4;
   `__asan::Allocator::Reallocate: 0 named, 32 by address, 0 related, 0 lemma(s), an earlier delivery 0 named and 0 name(s) holding
   it` (other units); control preset_base64_encode found.  Named cold branches: r24/1029/cold-search.md (725 refs) and
   b-check.md (1243 refs); second-agent checker a Theorem Labs lane: CONFIRM for image B.

   The pcs: FS_AREALLOC_BU (lib/B/FSupoisonRealloc.v) is stated at lib/B/FSH_ReallocModel.v's FS_AREALLOC_PC_B = 0x530e8
   (`j 0x534e4`, 3fc0006f) and FS_AREALLOC_IPC_B = 0x53620 (the return pc of the interceptor's second GetCurrentPc call
   0x5361c, 314200ef), the pcs of this instance (lib/B/FSRealloc_inst.v exports them).

   The bridge from RGtop's arealloc_realizes_all (ReallocG, at FS_ARX) to FSupoisonReallocG.arealloc_realizesU:
   - acall_preU reads the stack window and the frame chain through `unpoison Up mem`; realloc_pre reads them on the
     machine memory.  They agree there: the user-poisoned bytes are shadow bytes below kHighMemBeg
     (FSupoison.ush_facts), the stack lies at or above it (FSupoison.stk_kHighMemBeg);
   - rpre = Wf Un S /\ qmeter S /\ aregime3 S n: Wf from AR (am_wf), qmeter from acall_pre, aregime3 given;
   - rU from the trace premise (fs_rU_call), RSTACK's margin from the stack-margin premise, fpre is the range premise;
   - the leaf: rstage gives astageU (ARU from FS_ARX; the raw frame is dropped); the model half-posts realloc_mpost /
     realloc_fpost from the granted paths (YG07.malloc_gen, YG03.free_gen, rmodel's ik_malloc); a0 under the final
     layout and p's address under ly2 from AR_layout_law (the blocks' addresses do not move as the layout grows).
   No Axiom, no Admitted. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YP09 YP03.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG02 YG03 YG06 YG07 YG08 YG0k YG0l YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import AllocG DeallocG ReallocG RGtop.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1w YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSRealloc_inst.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require
FSRealloc_S1 FSRealloc_S2a FSRealloc_S2b FSRealloc_S3 FSRealloc_S4.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison FSupoisonU.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSH_ReallocModelG FSupoisonReallocG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSupoisonRealloc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI16.sink_head := _.
Fail Definition probe_SH : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI14.sink_syms := _.

Module FSPo := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.
Module FSUo := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonU.
Module FSR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSupoisonRealloc.

Lemma fs_map_eq_In {X Y} (f g : X -> Y) : forall l x, map f l = map g l -> In x l -> f x = g x.
Proof.
induction l as [|y l IH]; cbn; intros x E H; [destruct H|].
injection E as E1 E2. destruct H as [<-|H]; [exact E1 | exact (IH x E2 H)].
Qed.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Step 4: RGtop's rg_realloc_all at image B's instance, the five segments discharged.                               *)

Theorem fs_realloc_all : forall (B : asyms) (Up : list (Z * Z)), TfibSyms B ->
  aalloc_realizes tfibsegs B (FS_U B) YG00.malloc (FS_ARX B Up) (aowned B) FS_rpreA MALLOC_MAX LIVE_MAX qtight
    tfib_A__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb TFIB_OOM 8 1 1 ->
  adealloc_realizes_raw tfibsegs B (FS_U B) YG00.free (FS_ARX B Up) (aowned B) FS_rpreD qtight (FS_fpre B Up)
    tfib_A__ZN6__asan9Allocator10DeallocateEPvmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeE 1 ->
  arealloc_realizes_all tfibsegs B YG00.malloc YG00.free (FS_ARX B Up) (aowned B) (FS_rpre B) MALLOC_MAX LIVE_MAX qtight
    (FS_fpre B Up) (FS_rU B) FS_RFRAME FS_AREALLOC_PC_B FS_AREALLOC_IPC_B TFIB_INST TFIB_OOM.
Proof.
intros B Up TB HA HD.
exact (fs_rg_realloc_all B Up TB HA HD (FSRealloc_S1.fs_seg_pre B Up TB) (FSRealloc_S2a.fs_seg_mid_a B TB Up)
  (FSRealloc_S2b.fs_seg_mid_b B Up) (FSRealloc_S3.fs_seg_ret B Up TB) (FSRealloc_S4.fs_seg_nret B Up TB)).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The bridge's pieces.                                                                                              *)

Section h.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variable Up : list (Z * Z).
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* A stage at FS_ARX is a stage in FSupoisonReallocG's ARU form (its raw frame is not asked). *)
Lemma fs_astageU_of_rstage : forall ly S W regs mem md (E : Z -> Prop) ly' S' W' mem' md',
  rstage tfibsegs B (FS_ARX B Up) (aowned B) TFIB_INST ly S W regs mem md E ly' S' W' mem' md' ->
  FSupoisonReallocG.astageU tfibsegs B ASTACK ly S Up W regs mem md E ly' S' W' mem' md'.
Proof.
intros ly S W regs mem md E ly' S' W' mem' md' ((_ & HARU) & LLE & WLE & IO & FR & _ & PR).
exact (conj HARU (conj LLE (conj WLE (conj IO (conj FR PR))))).
Qed.

(* The inner malloc's half-post, from its granted path out of realloc_s1 S (the state after the entry step). *)
Lemma fs_mpost : forall S n tr q S2 trc,
  FS_rpre B S n -> 1 <= n < MALLOC_MAX -> blocks_bytes S + n <= LIVE_MAX -> FS_rU B tr S ->
  apath (YG00.malloc n tr (realloc_s1 S)) trc (q, S2) ->
  exists ns, FSH_ReallocModelG.realloc_mpost (as_universe B) S n ns (q, S2).
Proof.
intros S n tr q S2 trc (W0 & QM & R3) Hn Hl Htr Hp.
assert (Hn' : 0 <= n < MALLOC_MAX) by lia.
pose proof (fs_realloc_s1_wf (FS_Un B) S n W0 Hn' R3) as W1.
pose proof (fs_aregime3_s1 (FS_Un B) S n W0 Hn' R3) as R1.
pose proof (malloc_gen (FS_Un B) (realloc_s1 S) n tr (ts_universe B TB) W1 (aregime_ok _ R1) Hn' Hl
  (fs_rU_admit B tr S Htr)) as AT.
destruct (atok_apath _ _ _ _ _ AT Hp) as (ns & MP & BG & MG).
pose proof (apost_apath _ _ _ _ (ik_malloc n tr (realloc_s1 S)) Hp) as INI. unfold IK in INI. cbn [snd] in INI.
exists ns. split; [exact MP|]. split; [exact INI|]. intros BI. split; [exact (BG BI) | exact MG].
Qed.

(* The free of the old block's half-post, from the granted paths of the inner malloc (a block) and of the free. *)
Lemma fs_fpost : forall S n tr q S2 trc p n_old trc3 S3,
  FS_rpre B S n -> 1 <= n < MALLOC_MAX -> blocks_bytes S + n <= LIVE_MAX -> FS_rU B tr S ->
  In (p, n_old) (blocks S) ->
  apath (YG00.malloc n tr (realloc_s1 S)) trc (q, S2) -> q <> PNull ->
  apath (YG00.free p tr S2) trc3 (tt, S3) ->
  In (q, n) (blocks S2) /\ exists ns, FSH_ReallocModelG.realloc_fpost (as_universe B) S2 p n_old ns (tt, S3).
Proof.
intros S n tr q S2 trc p n_old trc3 S3 (W0 & QM & R3) Hn Hl Htr HBLK Hp HQ Hp3.
assert (Hn' : 0 <= n < MALLOC_MAX) by lia.
pose proof (fs_realloc_s1_wf (FS_Un B) S n W0 Hn' R3) as W1.
pose proof (fs_aregime3_s1 (FS_Un B) S n W0 Hn' R3) as R1.
pose proof (malloc_gen (FS_Un B) (realloc_s1 S) n tr (ts_universe B TB) W1 (aregime_ok _ R1) Hn' Hl
  (fs_rU_admit B tr S Htr)) as AT.
destruct (atok_apath _ _ _ _ _ AT Hp) as (ns & MP & BG & MG). cbn [snd] in BG, MG.
pose proof MP as (W2 & NE & _ & _ & BL & QTI).
pose proof (fs_aregime3_s2 (FS_Un B) S n S2 W0 Hn' R3 (qmeter_tight S QM) W2 NE QTI BG MG) as R2.
assert (BL2 : blocks S2 = blocks S ++ [(q, n)]).
{ destruct q as [|o|r o|c o]; [exfalso; exact (HQ eq_refl) | exact (proj1 BL) ..]. }
assert (HBLK2 : In (p, n_old) (blocks S2)) by (rewrite BL2; apply in_or_app; left; exact HBLK).
split; [rewrite BL2; apply in_or_app; right; left; reflexivity|].
assert (ADM : tr_admit (FS_Un B) S2 tr).
{ destruct Htr as [H|(L & H)]; [left; exact H | right; split; [exact L|]].
  rewrite NE. unfold realloc_s1. cbn [st_nev set_nev set_internal_inited]. lia. }
pose proof (free_gen (FS_Un B) S2 p n_old tr (ts_universe B TB) W2 (aregime_ok _ R2) (or_intror HBLK2) ADM) as AF.
destruct (atok_apath _ _ _ _ _ AF Hp3) as (ns3 & FP & FB & FG).
exists ns3. split; [exact FP|]. intros BI. split; [exact (FB BI) | exact FG].
Qed.

End h.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Step 5: FSupoisonRealloc.FS_AREALLOC_BU, from step 4 and the bridge.                                             *)

Theorem fs_arealloc_BU : forall B : asyms, TfibSyms B ->
  (forall Up, aalloc_realizes tfibsegs B (FS_U B) YG00.malloc (FS_ARX B Up) (aowned B) FS_rpreA MALLOC_MAX LIVE_MAX
     qtight tfib_A__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb TFIB_OOM 8 1 1) ->
  (forall Up, adealloc_realizes_raw tfibsegs B (FS_U B) YG00.free (FS_ARX B Up) (aowned B) FS_rpreD qtight
     (FS_fpre B Up) tfib_A__ZN6__asan9Allocator10DeallocateEPvmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeE 1) ->
  FSR.FS_AREALLOC_BU tfibsegs B (as_universe B).
Proof.
intros B TB HA HD.
unfold FSR.FS_AREALLOC_BU, FSupoisonReallocG.arealloc_realizesU.
intros ly S Up W regs mem md p n_old n ch PREU R3 HBLK HA0 HA1 HN HL HUP HTR HBOT.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct PREU as ((HAR & Hev & Hra & Hal & Hlo & Hbot & Hhi & HPRES & Hgp & Htp & Hch & HQM) & OKU & POU).
assert (ARU0 : FSPo.ARU tfibsegs B ly S Up W mem md) by exact (conj HAR (conj OKU POU)).
assert (SK : kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd)
  by (eapply FSPo.stk_kHighMemBeg; exact (proj1 HAR)).
destruct SK as (SKL & SKH).
pose proof (lo_top ly (am_layout B ly S _ (proj1 HAR))) as (_ & (_ & TOPHI) & _).
(* at or above kHighMemBeg the unpoisoned reading is the machine's *)
assert (UNP : forall a, kHighMemBeg <= a < 2 ^ 64 -> FSPo.unpoison Up mem (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
{ intros a Ha. apply FSPo.unpoison_out. destruct (FSPo.in_ush Up (bv_unsigned (Z_to_bv 64 a))) eqn:E; [|reflexivity].
  exfalso. pose proof (FSPo.ush_facts tfibsegs B ly S Up W mem md _ ARU0 E) as (_ & _ & L2).
  rewrite FSPo.wz in L2 by (unfold kHighMemBeg in *; lia). lia. }
(* realloc_pre on the machine memory *)
assert (HPRES' : forall a, spZ regs - ASTACK <= a < spZ regs -> apresent (w_H W) mem a).
{ intros a Ha. destruct (HPRES a Ha) as (Hh & b & Hb). split; [exact Hh|]. exists b.
  rewrite <- (UNP a ltac:(unfold ASTACK, kHighMemBeg, kHighMemEnd in *; lia)). exact Hb. }
assert (HCH' : chain_pre ly (aview tfibsegs (w_H W) mem) regs ch).
{ unfold chain_pre in Hch |- *. destruct Hch as (H4096 & Hc). split; [exact H4096|].
  destruct (frame0_ok ly regs); [|exact Hc].
  destruct (bad_next (spZ regs) (ly_top ly) (s0Z regs)) eqn:BN; [exact Hc|].
  destruct Hc as (Hs0 & Hfp). split; [exact Hs0|].
  unfold bad_next in BN. apply Bool.orb_false_elim in BN as [BN1 _]. apply Bool.orb_false_elim in BN1 as [_ BN2].
  apply Z.leb_gt in BN2.
  eapply YF0x.fpchain_ext2; [exact Hfp | lia |].
  intros a v Ha1 Ha2 Hv. eapply YF0x.rdword_ext; [|exact Hv].
  intros i Hi. apply FSPo.aview_at. symmetry. apply UNP. unfold ASTACK, kHighMemBeg, kHighMemEnd in *. lia. }
assert (PRE : realloc_pre tfibsegs B (FS_ARX B Up) FS_RFRAME TFIB_INST ly S W regs mem md ch).
{ unfold realloc_pre. split; [split; [reflexivity | exact ARU0]|].
  split; [exact Hra|]. split; [exact Hal|]. split; [exact Hlo|].
  split; [unfold FS_RFRAME; exact HBOT|]. split; [exact Hhi|].
  split; [exact HPRES'|]. split; [exact Hgp|]. split; [exact Htp|]. exact HCH'. }
assert (RP : FS_rpre B S n) by exact (conj (am_wf B ly S _ (proj1 HAR)) (conj HQM R3)).
pose proof (fs_rU_call B ly FS_AREALLOC_IPC_B regs ch S HTR) as HRU.
set (tr := call_trace ly FS_AREALLOC_IPC_B regs ch) in *.
eapply amreal_mono;
  [|exact (fs_realloc_all B Up TB (HA Up) (HD Up) ly S W regs mem md p n_old n ch PRE RP HBLK HUP HA0 HA1 HN HL HRU)].
intros [q S3] W' c' LEAF.
destruct LEAF as (_ & ly' & regs' & mem' & md' & Ec & CS & LP & HNULL & HBLOCK).
cbn [fst snd] in HNULL, HBLOCK, LP.
unfold FSupoisonReallocG.arealloc_leafU. cbn [fst snd].
exists ly', regs', mem', md'. split; [exact Ec|]. split; [exact CS|].
destruct (rg_null_dec q) as [EQ | HQ].
- (* the NULL-return arm *)
  subst q. destruct (HNULL eq_refl) as (A0 & RS & REF & _ & _ & _).
  split; [rewrite A0; reflexivity|]. split; [exact LP|].
  split; [exact (fs_astageU_of_rstage B Up ly S W regs mem md _ ly' S3 W' mem' md' RS)|].
  destruct REF as (S1 & trc1 & trc2 & HP1 & _ & HP2 & _).
  rewrite fs_free_null in HP1. destruct trc1 as [|e trc1']; cbn [apath] in HP1; [|destruct HP1].
  injection HP1 as E1. subst S1.
  exact (fs_mpost B TB S n tr PNull S3 trc2 RP HN HL HRU HP2).
- (* a block q *)
  destruct (HBLOCK HQ) as (ly2 & S2 & W2 & mem2 & md2 & A0 & RS1 & (trc & HPN & _) & LP2 & CPY & RS2 & (trc3 & HP3 & _)).
  unfold realloc_null_tree_with, YG00.bind in HPN. cbv beta in HPN. rewrite fs_free_null in HPN. cbn [ibind] in HPN.
  destruct (fs_fpost B TB S n tr q S2 trc p n_old trc3 S3 RP HN HL HRU HBLK HPN HQ HP3) as (QIN & FPOST).
  pose proof (fs_mpost B TB S n tr q S2 trc RP HN HL HRU HPN) as MPOST.
  (* p's address under ly2 is its address under ly; q's under ly' is its address under ly2 *)
  assert (EPA : sptr_addr B ly2 p = sptr_addr B ly p).
  { destruct RS1 as (_ & LLE1 & _).
    destruct (al_layout _ _ LAWS ly S W (FSPo.unpoison Up mem) md ly2 HAR LLE1) as (EAB & _).
    unfold ablocks in EAB. exact (f_equal fst (fs_map_eq_In _ _ (blocks S) (p, n_old) EAB HBLK)). }
  assert (EQA : sptr_addr B ly' q = sptr_addr B ly2 q).
  { destruct RS1 as ((_ & ARU2) & _). destruct RS2 as (_ & LLE2 & _).
    destruct (al_layout _ _ LAWS ly2 S2 W2 (FSPo.unpoison Up mem2) md2 ly' (FSPo.ARU_AR _ _ _ _ _ _ _ _ ARU2) LLE2)
      as (EAB & _).
    unfold ablocks in EAB. exact (f_equal fst (fs_map_eq_In _ _ (blocks S2) (q, n) EAB QIN)). }
  rewrite EPA in RS2.
  assert (A0' : getr regs' 10 = w64 (sptr_addr B ly' q)) by (rewrite EQA; exact A0).
  assert (BODY : exists ly2 S2 W2 mem2 md2,
    FSupoisonReallocG.astageU tfibsegs B ASTACK ly S Up W regs mem md
      (fun a => sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n) ly2 S2 W2 mem2 md2 /\
    (exists ns, FSH_ReallocModelG.realloc_mpost (as_universe B) S n ns (q, S2)) /\ qtight S2 /\
    (forall i, 0 <= i < Z.min n_old n ->
       aview tfibsegs (w_H W2) mem2 (sptr_addr B ly2 q + i) = aview tfibsegs (w_H W) mem (sptr_addr B ly p + i)) /\
    FSupoisonReallocG.astageU tfibsegs B ASTACK ly2 S2 Up W2 regs mem2 md2
      (fun a => sptr_addr B ly p <= a < sptr_addr B ly p + req_size n_old) ly' S3 W' mem' md' /\
    (exists ns, FSH_ReallocModelG.realloc_fpost (as_universe B) S2 p n_old ns (tt, S3))).
  { exists ly2, S2, W2, mem2, md2.
    split; [exact (fs_astageU_of_rstage B Up ly S W regs mem md _ ly2 S2 W2 mem2 md2 RS1)|].
    split; [exact MPOST|]. split; [exact LP2|]. split; [exact CPY|].
    split; [exact (fs_astageU_of_rstage B Up ly2 S2 W2 regs mem2 md2 _ ly' S3 W' mem' md' RS2) | exact FPOST]. }
  destruct q as [|o|r o|c o].
  + exfalso; exact (HQ eq_refl).
  + split; [exact A0'|]. split; [exact LP | exact BODY].
  + split; [exact A0'|]. split; [exact LP | exact BODY].
  + split; [exact A0'|]. split; [exact LP | exact BODY].
Qed.

End t.
