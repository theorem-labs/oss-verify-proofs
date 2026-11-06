(* fuzz_state image A: the composed realloc contract (a Theorem Labs lane L14 steps 4 and 5).

   Rule 24 (released-proof lookup): proves function __asan::Allocator::Reallocate chain composition on fs (reuse search:
   proof-index unpiped, 2026-10-29 ~03:55Z, (internal path): `proof-index: end;
   0x53078 / 0x53474 / 0x3287c / 0x32928 (A): 0 named, 0 by address, 0 related, 0 lemma(s), 0 by file name, an earlier delivery 0 named
   and 0 name(s) holding it`; control preset_base64_encode found; cold: cold-search.md (725 refs) + b-check.md (1243
   refs); second-agent checker a Theorem Labs lane: CONFIRM for image A, b-check.md:150-252).

   - [fs_realloc_all] (step 4): a Theorem Labs lane's RGtop.rg_realloc_all at fs's image-A instance (FSRealloc_inst.fs_rg_realloc_all)
     with the five thin segments discharged (FSRealloc_S1.fs_seg_pre, FSRealloc_S2a.fs_seg_mid_a,
     FSRealloc_S2b.fs_seg_mid_b, FSRealloc_S3.fs_seg_ret, FSRealloc_S4.fs_seg_nret).  Its only hypotheses are fs's symbol
     fact [TfibSyms B] and a Theorem Labs lane's two callee contracts at fs's pcA / pcD: AllocG.aalloc_realizes (Allocate, 0x31ef4)
     and DeallocG.adealloc_realizes_raw (Deallocate, 0x31be0).
   - [fs_arealloc_AU] (step 5): FSupoisonRealloc.FS_AREALLOC_AU (lib/A/FSupoisonRealloc.v @ a working branch
     e0461c947a1) at the universe [as_universe B], from [fs_realloc_all] for every user-poison set, modulo the same two
     callee contracts (for every poison set Up, as FS_AREALLOC_AU quantifies Up).  The bridge:
     * acall_preU (AR over the unpoisoned reading) -> c5's realloc_pre (raw memory): the user-poisoned bytes are shadow
       bytes below kHighMemBeg (FSupoison.ush_facts), so the stack window's presence and the frame-pointer chain read the
       same on both memories (YCbq.fpchain_ext); the stack margin `ly_bot ly + 0x8a0 < spZ regs` is FS_AREALLOC_AU's;
     * the trace premise `In .. Un \/ st_nev S + 2 < EV_MAX` -> FS_rU (FSRealloc_rmodel.fs_rU_call);
     * rstage -> astageU (drop the raw frame; ARX's second part is ARU);
     * the granted paths -> realloc_mpost / realloc_fpost (malloc_gen at realloc_s1 S, free_gen at the inner malloc's
       state S2, as FSRealloc_rmodel.fs_rmodel_ok);
     * a0 and the freed block's range under the final layouts (AR_layout_law: a live block keeps its address when the
       layout grows).

   No Axiom, no Admitted. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1w AF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSRealloc_inst.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require
FSRealloc_S1 FSRealloc_S2a FSRealloc_S2b FSRealloc_S3 FSRealloc_S4.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require
FSupoison FSupoisonU FSH_ReallocModelG FSupoisonReallocG FSupoisonRealloc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI16.sink_head := _.
Fail Definition probe_SH : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI14.sink_syms := _.

Module PU := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.
Module PR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonRealloc.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Step 4: the composition with the five segments discharged.                                                       *)

Theorem fs_realloc_all : forall (B : asyms) (Up : list (Z * Z)), TfibSyms B ->
  aalloc_realizes tfibsegs B (FS_U B) YG00.malloc (FS_ARX B Up) (aowned B) FS_rpreA MALLOC_MAX LIVE_MAX qtight
    tfib_A__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb TFIB_OOM 8 1 1 ->
  adealloc_realizes_raw tfibsegs B (FS_U B) YG00.free (FS_ARX B Up) (aowned B) FS_rpreD qtight (FS_fpre B Up)
    tfib_A__ZN6__asan9Allocator10DeallocateEPvmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeE 1 ->
  arealloc_realizes_all tfibsegs B YG00.malloc YG00.free (FS_ARX B Up) (aowned B) (FS_rpre B) MALLOC_MAX LIVE_MAX qtight
    (FS_fpre B Up) (FS_rU B) FS_RFRAME FS_AREALLOC_PC_A FS_AREALLOC_IPC_A TFIB_INST TFIB_OOM.
Proof.
intros B Up TB HA HD.
apply (fs_rg_realloc_all B Up TB HA HD).
- exact (FSRealloc_S1.fs_seg_pre B Up TB).
- eapply FSRealloc_S2a.fs_seg_mid_a; eassumption.
- eapply FSRealloc_S2b.fs_seg_mid_b.
- eapply FSRealloc_S3.fs_seg_ret; eassumption.
- eapply FSRealloc_S4.fs_seg_nret; eassumption.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Step 5: the bridge to FSupoisonRealloc.arealloc_realizesU.                                                       *)

(* The model side, as FSRealloc_rmodel.fs_rmodel_ok: the inner malloc at realloc_s1 S. *)
Lemma fs_malloc_facts : forall B S n tr trc q S2,
  universe_ok (as_universe B) -> FS_rpre B S n -> 1 <= n < MALLOC_MAX -> blocks_bytes S + n <= LIVE_MAX ->
  FS_rU B tr S -> apath (YG00.malloc n tr (realloc_s1 S)) trc (q, S2) ->
  (exists ns, FSH_ReallocModelG.realloc_mpost (as_universe B) S n ns (q, S2)) /\ Wf (as_universe B) S2 /\ aregime S2 /\
  st_nev S2 = st_nev S + 2 /\ (q <> PNull -> blocks S2 = blocks S ++ [(q, n)]).
Proof.
intros B S n tr trc q S2 HU (W0 & QM & R3) Hn Hl Htr Hp.
assert (Hn' : 0 <= n < MALLOC_MAX) by lia.
pose proof (fs_realloc_s1_wf (FS_Un B) S n W0 Hn' R3) as W1. pose proof (fs_aregime3_s1 (FS_Un B) S n W0 Hn' R3) as R1.
pose proof (malloc_gen (FS_Un B) (realloc_s1 S) n tr HU W1 (aregime_ok _ R1) ltac:(lia) Hl (fs_rU_admit B tr S Htr)) as AT.
destruct (atok_apath _ _ _ _ _ AT Hp) as (ns & MP & BG & MG). cbn [snd] in BG, MG.
pose proof MP as (W2 & NE & _ & _ & BL & QTI).
pose proof (apost_apath _ _ _ _ (ik_malloc n tr (realloc_s1 S)) Hp) as INI. unfold IK in INI. cbn [snd] in INI.
pose proof (fs_aregime3_s2 (FS_Un B) S n S2 W0 Hn' R3 (qmeter_tight S QM) W2 NE QTI BG MG) as R2.
split.
{ exists ns. split; [exact MP|]. cbn [snd]. split; [rewrite INI; reflexivity|]. intros BI. split; [exact (BG BI) | exact MG]. }
split; [exact W2|]. split; [exact R2|].
split; [rewrite NE; unfold realloc_s1; cbn [st_nev set_nev set_internal_inited]; lia|].
intros HQ. destruct q as [|o|r o|c o]; [exfalso; exact (HQ eq_refl) | exact (proj1 BL) ..].
Qed.

(* The model side of the free of the old block at the inner malloc's state S2. *)
Lemma fs_free_facts : forall B S tr p n_old S2 trc S3,
  universe_ok (as_universe B) -> Wf (as_universe B) S2 -> aregime S2 -> In (p, n_old) (blocks S2) ->
  FS_rU B tr S -> st_nev S2 = st_nev S + 2 -> apath (YG00.free p tr S2) trc (tt, S3) ->
  exists ns, FSH_ReallocModelG.realloc_fpost (as_universe B) S2 p n_old ns (tt, S3).
Proof.
intros B S tr p n_old S2 trc S3 HU W2 R2 HIN Htr NE Hp.
assert (ADM : tr_admit (FS_Un B) S2 tr) by (destruct Htr as [H|(L & H)]; [left; exact H | right; split; [exact L | lia]]).
pose proof (free_gen (FS_Un B) S2 p n_old tr HU W2 (aregime_ok _ R2) (or_intror HIN) ADM) as AT.
destruct (atok_apath _ _ _ _ _ AT Hp) as (ns & FP & BG & FG). cbn [snd] in BG, FG.
exists ns. split; [exact FP|]. intros BI. split; [exact (BG BI) | exact FG].
Qed.

(* realloc(NULL, n)'s tree after the no-op entry step is the malloc tree at realloc_s1 S. *)
Lemma fs_null_tree_path : forall n tr S trc r,
  apath (realloc_null_tree_with YG00.malloc YG00.free n tr S) trc r -> apath (YG00.malloc n tr (realloc_s1 S)) trc r.
Proof. intros n tr S trc r H. unfold realloc_null_tree_with, YG00.bind in H. rewrite fs_free_null in H. exact H. Qed.

(* A live block keeps its address when the layout grows (AR_layout_law). *)
Lemma fs_addr_keep : forall B ly S W m md ly' p n,
  AR tfibsegs B ly S W m md -> layout_le (length (st_secs S)) ly ly' -> In (p, n) (blocks S) ->
  sptr_addr B ly' p = sptr_addr B ly p.
Proof.
intros B ly S W m md ly' p n HAR LLE HIN.
destruct (al_layout _ _ (AR_laws_ok tfibsegs B) ly S W m md ly' HAR LLE) as (EAB & _).
unfold ablocks in EAB.
pose proof (FSRealloc_S2a.map_eq_In_loc (fun b : sptr * Z => (sptr_addr B ly' (fst b), snd b))
              (fun b : sptr * Z => (sptr_addr B ly (fst b), snd b)) (blocks S) (p, n) EAB HIN) as E.
cbn [fst snd] in E. injection E as E. exact E.
Qed.

Theorem fs_arealloc_AU : forall B : asyms, TfibSyms B ->
  (forall Up, aalloc_realizes tfibsegs B (FS_U B) YG00.malloc (FS_ARX B Up) (aowned B) FS_rpreA MALLOC_MAX LIVE_MAX qtight
     tfib_A__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb TFIB_OOM 8 1 1) ->
  (forall Up, adealloc_realizes_raw tfibsegs B (FS_U B) YG00.free (FS_ARX B Up) (aowned B) FS_rpreD qtight (FS_fpre B Up)
     tfib_A__ZN6__asan9Allocator10DeallocateEPvmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeE 1) ->
  PR.FS_AREALLOC_AU tfibsegs B (as_universe B).
Proof.
intros B TB HA HD.
pose proof (ts_universe B TB) as HU.
unfold PR.FS_AREALLOC_AU, FSupoisonReallocG.arealloc_realizesU.
intros ly S Up W regs mem md p n_old n ch PREU R3 HIN A0 A1 HN HL HUP HTR HBOT.
destruct PREU as (PRE & OKU & POU).
destruct PRE as (HAR & HREG & HRA & HAL & HLO & HBOT0 & HHI & HPRES & HGP & HTP & HCH & HQM).
assert (HARU : PU.ARU tfibsegs B ly S Up W mem md) by exact (conj HAR (conj OKU POU)).
assert (STK : kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd)
  by (eapply PU.stk_kHighMemBeg; eapply PU.ARU_ARm; exact HARU).
destruct STK as (SKL & SKH).
pose proof (lo_top ly (am_layout B ly S _ (proj1 HAR))) as (_ & TOP & _ & _ & _ & _ & _).
(* the user-poisoned bytes are shadow bytes below kHighMemBeg: above it the two readings agree *)
assert (NOUSH : forall a, kHighMemBeg <= a < 2 ^ 64 -> PU.in_ush Up (bv_unsigned (Z_to_bv 64 a)) = false).
{ intros a Ha. destruct (PU.in_ush Up (bv_unsigned (Z_to_bv 64 a))) eqn:E; [|reflexivity]. exfalso.
  destruct (PU.ush_facts tfibsegs B ly S Up W mem md _ HARU E) as (_ & L).
  assert (Ha' : 0 <= a < 2 ^ 64) by (unfold kHighMemBeg in Ha; lia).
  rewrite (PU.wz a Ha') in L. unfold kHighMemBeg in *. lia. }
assert (VIEW : forall a, kHighMemBeg <= a < 2 ^ 64 ->
  aview tfibsegs (w_H W) (PU.unpoison Up mem) a = aview tfibsegs (w_H W) mem a).
{ intros a Ha. apply PU.aview_unpoison_out. exact (NOUSH a Ha). }
(* c5's realloc_pre on the raw memory *)
pose proof (fs_realloc_all B Up TB (HA Up) (HD Up) ly S W regs mem md p n_old n ch) as RA.
lazymatch type of RA with ?P -> _ => assert (RPRE : P) end.
{ unfold realloc_pre.
  split; [split; [reflexivity | exact HARU]|].
  split; [exact HRA|]. split; [exact HAL|]. split; [exact HLO|].
  split; [unfold FS_RFRAME; exact HBOT|]. split; [exact HHI|].
  split.
  { intros a Ha. destruct (HPRES a Ha) as (Hh & b & Hb). split; [exact Hh|]. exists b. rewrite <- Hb. symmetry.
    apply PU.unpoison_out. apply NOUSH. unfold ASTACK in *. unfold kHighMemEnd in SKH. lia. }
  split; [exact HGP|]. split; [exact HTP|].
  unfold chain_pre in HCH |- *. destruct HCH as (R4 & HC). split; [exact R4|].
  destruct (frame0_ok ly regs) eqn:F0; [|exact HC].
  destruct (bad_next (spZ regs) (ly_top ly) (s0Z regs)) eqn:BN; [exact HC|].
  destruct HC as (L16 & FC). split; [exact L16|].
  unfold bad_next in BN. apply Bool.orb_false_elim in BN as [BN _]. apply Bool.orb_false_elim in BN as [_ BN].
  apply Z.leb_gt in BN.
  apply (YCbq.fpchain_ext (rdword (aview tfibsegs (w_H W) (PU.unpoison Up mem)))); [| lia | exact FC].
  intros a Ha1 Ha2. unfold kHighMemEnd in SKH. unfold ASTACK in HLO.
  unfold rdword. rewrite !VIEW by lia. reflexivity. }
specialize (RA RPRE).
assert (RP : FS_rpre B S n) by exact (conj (am_wf B ly S _ (proj1 HAR)) (conj HQM R3)).
specialize (RA RP HIN HUP A0 A1 HN HL (fs_rU_call B ly FS_AREALLOC_IPC_A regs ch S HTR)).
set (tr := call_trace ly FS_AREALLOC_IPC_A regs ch) in *.
unfold FSH_ReallocModelG.realloc_tree. unfold realloc_tree_with, realloc_k in RA.
eapply amreal_mono; [|exact RA].
clear RA.
intros [q S'] W' c' LEAF.
destruct LEAF as (_ & ly' & regs' & mem' & md' & Ec & CS & LP & HNUL & HBLK). cbn [fst snd] in *.
exists ly', regs', mem', md'.
split; [exact Ec|]. split; [exact CS|].
(* the block arm, for any non-NULL result *)
assert (BLKARM : q <> PNull ->
  getr regs' 10 = w64 (sptr_addr B ly' q) /\
  exists ly2 S2 W2 mem2 md2,
  FSupoisonReallocG.astageU tfibsegs B ASTACK ly S Up W regs mem md
    (fun a => sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n) ly2 S2 W2 mem2 md2 /\
  (exists ns, FSH_ReallocModelG.realloc_mpost (as_universe B) S n ns (q, S2)) /\ qtight S2 /\
  (forall i, 0 <= i < Z.min n_old n ->
     aview tfibsegs (w_H W2) mem2 (sptr_addr B ly2 q + i) = aview tfibsegs (w_H W) mem (sptr_addr B ly p + i)) /\
  FSupoisonReallocG.astageU tfibsegs B ASTACK ly2 S2 Up W2 regs mem2 md2
    (fun a => sptr_addr B ly p <= a < sptr_addr B ly p + req_size n_old) ly' S' W' mem' md' /\
  (exists ns, FSH_ReallocModelG.realloc_fpost (as_universe B) S2 p n_old ns (tt, S'))).
{ intros HQ.
  destruct (HBLK HQ) as (ly2 & S2 & W2 & mem2 & md2 & A02 & ST1 & (trcN & HPN & _) & LP2 & CPY & ST2 & (trcF & HPF & _)).
  destruct (fs_malloc_facts B S n tr trcN q S2 HU RP HN HL (fs_rU_call B ly FS_AREALLOC_IPC_A regs ch S HTR)
              (fs_null_tree_path n tr S trcN (q, S2) HPN)) as (MP & W2f & R2 & NE & BL).
  destruct ST1 as ((_ & ARU2) & LLE1 & WLE1 & IO1 & FR1 & _ & PR1).
  destruct ST2 as ((_ & ARU3) & LLE2 & WLE2 & IO2 & FR2 & _ & PR2).
  assert (HINQ : In (q, n) (blocks S2)) by (rewrite (BL HQ); apply in_or_app; right; left; reflexivity).
  assert (HINP : In (p, n_old) (blocks S2)) by (rewrite (BL HQ); apply in_or_app; left; exact HIN).
  assert (EQA : sptr_addr B ly' q = sptr_addr B ly2 q)
    by exact (fs_addr_keep B ly2 S2 W2 _ md2 ly' q n (PU.ARU_AR _ _ _ _ _ _ _ _ ARU2) LLE2 HINQ).
  assert (EPA : sptr_addr B ly2 p = sptr_addr B ly p)
    by exact (fs_addr_keep B ly S W _ md ly2 p n_old HAR LLE1 HIN).
  split; [rewrite EQA; exact A02|].
  exists ly2, S2, W2, mem2, md2.
  split; [exact (conj ARU2 (conj LLE1 (conj WLE1 (conj IO1 (conj FR1 PR1)))))|].
  split; [exact MP|]. split; [exact LP2|]. split; [exact CPY|].
  split.
  { split; [exact ARU3|]. split; [exact LLE2|]. split; [exact WLE2|]. split; [exact IO2|].
    split; [|exact PR2].
    intros a Ha N1 N2 N3 NE'. apply (FR2 a Ha N1 N2 N3). intros X. apply NE'. cbv beta in X |- *. rewrite EPA in X. exact X. }
  exact (fs_free_facts B S tr p n_old S2 trcF S' HU W2f R2 HINP (fs_rU_call B ly FS_AREALLOC_IPC_A regs ch S HTR) NE HPF). }
destruct q as [|o|r o|c o].
- (* the NULL-return arm *)
  destruct (HNUL eq_refl) as (A00 & ST & (S1 & trc1 & trc2 & HP1 & _ & HP2 & _) & _ & _ & _).
  split; [rewrite A00; reflexivity|]. split; [exact LP|].
  rewrite fs_free_null in HP1. destruct trc1 as [|e trc']; cbn [apath] in HP1; [|destruct HP1].
  injection HP1 as E1. subst S1.
  destruct (fs_malloc_facts B S n tr trc2 PNull S' HU RP HN HL (fs_rU_call B ly FS_AREALLOC_IPC_A regs ch S HTR) HP2)
    as (MP & _).
  destruct ST as ((_ & ARU') & LLE & WLE & IO & FRv & _ & PR').
  split; [exact (conj ARU' (conj LLE (conj WLE (conj IO (conj FRv PR')))))|].
  exact MP.
- destruct (BLKARM ltac:(discriminate)) as (A0' & REST). split; [exact A0'|]. split; [exact LP|]. exact REST.
- destruct (BLKARM ltac:(discriminate)) as (A0' & REST). split; [exact A0'|]. split; [exact LP|]. exact REST.
- destruct (BLKARM ltac:(discriminate)) as (A0' & REST). split; [exact A0'|]. split; [exact LP|]. exact REST.
Qed.

End t.
