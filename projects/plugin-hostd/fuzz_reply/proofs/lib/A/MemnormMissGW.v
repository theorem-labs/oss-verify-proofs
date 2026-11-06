(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/MemnormMissGW.v (commit 3295f3a9fd5, CfInstMiss lane M field round 3 (cf-miss 3295f3a9fd5); file sha256 62f56312bd65) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 6 image addresses moved by function pairs the comparison kit cmpkit 4bbd3a74be89 calls the same code except at the by-hand acceptances named below (strictcmp2 16982e3ef42b, by funcpair_reply 053b61532a33 on the cgif twin ce511d541cda; 6 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the pair, each data one a pc-relative target of both paired functions; 0 code pcs the tool read as sizes, by the pair; 1 pair(s) carry a BY-HAND acceptance of the kit's known false-difference class (accept.tsv, re-measured each run: the bytes the code reads equal and read-only on both images): _ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb+0xdc); no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane for a Theorem Labs lane, lane missw): MemnormMissGW, the AIfaceMw variant of MemnormMissG.v (c5
   8d6c9f45705b): the refill's stack window is the Section variable RW (0 <= RW, 176 + RW <= AFSTACK: hypothesis
   RWB) of MnRefillW.v, not RSTACK = 1024.  Same proof script; the changes are AIfaceM -> AIfaceMw (fields if_ ->
   ifw_), the refill leaves -> their _w forms at RW, RSTACK -> RW, the refill-window steps through
   MnRefillW.win_af_w and the other frame lia steps under RWB, RW (and RWB) in the explicit arguments of the W
   twins' lemmas, and the imports of the W twins.  MemnormMissG.v is unchanged.  rule 24: no function proved (kind:
   re-statement of a proved miss walk over a wider refill window). *)
(* Theorem Labs, 2026-10 (task MEMNORM): the memnorm-kept twin of the g-path MISS arm at can_fill = 1.
   [alloc_missg_em] is AGimEW.alloc_missg_e with MemnormT.alloc_leaf_em (ErrnoG.alloc_leaf_e plus
   `memnorm mem -> memnorm mem'`) in place of ErrnoG.alloc_leaf_e.
   rule 24: no function proved (kind: arm twin, frame corollary over the refill's memnorm-kept contract).

   AGimE's Section variables and hypotheses in AGimE's order, with the refill's add-on IFME (ErrnoG.AIfaceME) replaced
   by the refill's memnorm-kept contract [RFm] (MnRefillW.amm_refill_w_t: ErrnoG.ame_refill_t's premises, post
   MnRefillW.rleaf_em_w RW = rleaf_e plus the keep).  No new walking: every step is AGim's lemma, cited as AGimE cites it.
   The keep is the chain of the arm's own raw frames and the refill's keep:
   - MISS1's raw frame MEQW (outside AGiu.WINM: Allocate's stack window and the thread's unwinding byte; [memnorm_winm]:
     the window is in the layout's stack, the byte in the thread object, an owned extent);
   - the refill's keep (rleaf_em);
   - the grant path (a0 = 1): at_RETw's raw frame MEQF at the post-refill layout (MemnormHitG.memnorm_at_RETw);
   - the class-full OOM path (a0 = 0): the OOM tail's raw frame (AGk1W.RETN: outside WN, i.e. the stack window, the
     OOM flag byte and errno, [memnorm_winn]), in [miss_oom_tail_em], the twin of AGk1EW.miss_oom_tail_e.
   Copied (marked): AGimE's section scripts and AGk1EW.miss_oom_tail_e's, each over the _em lemmas.
   AGimE, AGk1E and every existing statement are unchanged. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YG0b.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG02 YG06 YG07 YG0k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0h.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1w AE3d AFhy AFhm AGhy AGhz AGi4.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YFen.
(* AGif0cgif before AGif0n: hview / hit_writes / wframe are AGif0n's short names here (AGif0cgif's header). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGis AFi3 AllocG AGif0reply AGif0n AGif2reply AGiz AGj0 AGj2 AGiw AGiu AGit AGiv AB13.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require MnRefillW.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ErrnoG.
(* The original arm (AGim), the shared OOM tail's twin (AGk1E), the image facts (ErrnoApart) and at_RETw's errno
   lemma (AGikE.errno_kept_at_RETw), used qualified. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ErrnoApart AGimW AGk1EW AGikE.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AGk1W ImgBaseAG AGhy.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require MemnormT MemnormHitG MemnormSafereply MemnormLocG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YAkMemnorm.
(* field round 3: the read-only data predicate at Allocate's entry, used qualified *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfNames YG0dcf.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
(* copy of AGim.v:40 *)
Local Ltac bvne := first [cbn; lia | vm_compute; congruence | intros X; vm_compute in X; discriminate X].
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : YGcfNames.CfImg}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The bridge into alloc_leaf_em, and the two windows.                                                              *)

(* ErrnoG.alloc_leaf_e and memnorm kept in the memory of the returned configuration give alloc_leaf_em. *)
Lemma alloc_leaf_em_of_e : forall (segs : list Segment) B mt ARX AOX lpost oomb inst ly S (W : world segs) regs mem md n tr
(r : sptr * astate) (W' : world segs) c',
alloc_leaf_e segs B mt ARX AOX lpost oomb inst ly S W regs mem md n tr r W' c' ->
(forall regs' mem' md', c' = cfg_at segs (raZ regs) regs' mem' md' -> MemnormT.memnorm_keep segs mem mem') ->
MemnormT.alloc_leaf_em segs B mt ARX AOX lpost oomb inst ly S W regs mem md n tr r W' c'.
Proof.
intros segs B mt ARX AOX lpost oomb inst ly S W regs mem md n tr r W' c' (ly' & regs' & mem' & md' & Hc & HP & HE & HR & HL & HT & HO) HK.
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact HP|]. split; [exact HE|]. split; [exact (HK regs' mem' md' Hc)|].
split; [exact HR|]. split; [exact HL|]. split; [exact HT | exact HO].
Qed.

(* MISS1's window (AGiu.WINM): Allocate's stack window and the thread's unwinding byte. *)
Lemma memnorm_winm : forall ly (regs0 : bvmap 5 word) (mem0 m : word -> option byte), layout_ok ly -> img_cover ly ->
  ly_stk_lo ly + AGhy.AFSTACK <= bv_unsigned (getr regs0 2) -> bv_unsigned (getr regs0 2) <= ly_stk_hi ly ->
  (forall x : word, ~ AGiu.WINM ly regs0 (bv_unsigned x) -> m x = mem0 x) -> MemnormT.memnorm_keep tfibsegs mem0 m.
Proof.
intros ly regs0 mem0 m LY IMG Hlo Hhi F.
pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7).
apply (MemnormLocG.memnorm_keep_window tfibsegs (AGiu.WINM ly regs0) mem0 m); [|exact F].
intros x Hw. unfold AGiu.WINM in Hw. cbv zeta in Hw. destruct Hw as [Hw|Hw].
- apply MemnormHitG.mn_safe_high. unfold AGhy.AFSTACK, kHighMemBeg, kHighMemEnd, kImgEnd, TASK_SIZE in *. lia.
- apply (MemnormHitG.mn_safe_owned ly (ly_T ly, kThreadObjSize) x LY IMG
    ltac:(unfold owned_extents; right; right; left; reflexivity)).
  cbn [fst snd]. unfold t_unwinding, kThreadObjSize in *. lia.
Qed.

(* The OOM tail's window (a window WN inside the stack window, the OOM flag byte and errno: AGiv.WINN). *)
Lemma memnorm_winn : forall ly (sp0 : Z) (WN : Z -> Prop) (m m' : word -> option byte), layout_ok ly ->
  ly_stk_lo ly + AGhy.AFSTACK <= sp0 -> sp0 <= ly_stk_hi ly ->
  (forall a, WN a -> (sp0 - AGhy.AFSTACK <= a < sp0) \/ (TFIB_OOM <= a < TFIB_OOM + 1) \/ (TFIB_ERRNO <= a < TFIB_ERRNO + 4)) ->
  (forall x : word, ~ WN (bv_unsigned x) -> m' x = m x) -> MemnormT.memnorm_keep tfibsegs m m'.
Proof.
intros ly sp0 WN m m' LY Hlo Hhi HWN F.
pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7).
apply (MemnormLocG.memnorm_keep_window tfibsegs WN m m'); [|exact F].
intros x Hw. destruct (HWN _ Hw) as [H|[H|H]].
- apply MemnormHitG.mn_safe_high. unfold AGhy.AFSTACK, kHighMemBeg, kHighMemEnd, kImgEnd, TASK_SIZE in *. lia.
- apply MemnormSafereply.mn_safe_rw. unfold TFIB_OOM, TASK_SIZE in *. lia.
- apply MemnormSafereply.mn_safe_rw. unfold TFIB_ERRNO, TASK_SIZE in *. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The OOM tail with memnorm kept: copy of AGk1E.v:73-155 (AGk1's section b), plus the keep up to the refill's return
   [HKC], and the twin of AGk1EW.miss_oom_tail_e. *)
Section o.
Variable B : asyms.
Variable U : list Z -> astate -> Prop.
Variable mt : Z -> list Z -> M sptr.
Variable ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variables (nmax lmax : Z).
Variable lpost : astate -> Prop.
Variable dpost : Z -> alayout -> astate -> world tfibsegs -> list Z -> Z -> (word -> option byte) -> Prop.
Variables (mtag stag : Z).
Variable rtree : Z -> M unit.
Variable RW : Z.
Hypothesis RWB : 0 <= RW /\ 176 + RW <= AFSTACK.
Hypothesis IFM : MnRefillW.AIfaceMw B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree RW.
Hypothesis TS : TfibSyms B.

(* The caller at Allocate's entry: the virtual register file regs0 of the walk (atom 2 = the entry sp, 13 = the stack
   object) and the entry registers regsU. *)
Variables (inst : Z) (ly : alayout) (S : astate) (W : world tfibsegs).
Variables (regs0 regsU : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (n : Z) (tr : list Z).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let SOv : Z := bv_unsigned (getr regs0 13).
Let cl : Z := chunk_class n.
Hypothesis HARX : ARX inst ly S W mem0 md0.
Hypothesis Hn0 : 0 <= n.
Hypothesis FP : from_primary n = true.
Hypothesis LY : layout_ok ly.
Hypothesis Hsp : ly_stk_lo ly + AFSTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
Hypothesis Hso : sp0 <= SOv /\ SOv + 16 <= ly_stk_hi ly /\ SOv mod 8 = 0.
Hypothesis HUo : forall r : bv 5, bv_unsigned r <> 10 -> bv_unsigned r <> 11 -> bv_unsigned r <> 12 -> getr regsU r = getr regs0 r.

(* The refill call: its registers, memory and model (if_refill's premises at the call). *)
Variables (regsC : bvmap 5 word) (memC : word -> option byte) (mdC : Model).
Hypothesis SPC : spZ regsC = sp0 - 176.
Hypothesis AGC : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - AFSTACK <= a < sp0) -> aview tfibsegs (w_H W) memC a = aview tfibsegs (w_H W) mem0 a.
Hypothesis RAWC : forall x : word, ~ (sp0 - AFSTACK <= bv_unsigned x < sp0) ->
  ~ (ly_T ly + t_unwinding <= bv_unsigned x < ly_T ly + t_unwinding + 1) -> memC x = mem0 x.
Hypothesis PRESC : forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) memC a.
Hypothesis SIOC : same_io md0 mdC.

(* The refill's refusal: rleaf at the post-refill state S' (layout ly' >= ly), with the class cache still empty and
   a0 = 0. *)
Variables (S' : astate) (ly' : alayout) (W' : world tfibsegs) (regsR : bvmap 5 word) (memR : word -> option byte) (mdR : Model).
Hypothesis HARXp : ARX inst ly' S' W' memR mdR.
Hypothesis HLPp : lpost S'.
Hypothesis Hly : layout_le (length (st_secs S)) ly ly'.
Hypothesis HWLE : wle W W'.
Hypothesis HSIO : same_io mdC mdR.
Hypothesis HFRA : forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly S a -> ~ AOX ly' S' a -> ~ (spZ regsC - RW <= a < spZ regsC) ->
  aview tfibsegs (w_H W') memR a = aview tfibsegs (w_H W) memC a.
Hypothesis HFRR : forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ AOX ly' S' (bv_unsigned x) ->
  ~ (spZ regsC - RW <= bv_unsigned x < spZ regsC) -> memR x = memC x.
Hypothesis HPRR : forall a, spZ regsC - RW <= a < spZ regsC -> apresent (w_H W') memR a.
Hypothesis Hc0 : pc_chunks (cache S' cl) = [].
Hypothesis HA0 : getr regsR 10 = w64 0.

(* The symbolic state at the refill's return, and the segment run to the ret. *)
Let ms3 : machine_state := mkst regsR (w64 A_REFILL_RET) (mrestrict (w_H W') memR) (seg_rom tfibsegs).
Variables (E0m E1 : env) (SS3 MSN0 : sstate) (r1 r2 r3 : YP09.region) (WN : Z -> Prop).
Hypothesis HE0_2 : ew E0m 2 = getr regs0 2.
Hypothesis HE0_13 : ew E0m 13 = getr regs0 13.
Hypothesis HE1 : forall k, (k < aHAV)%nat -> ew E1 k = ew E0m k.
Hypothesis HS3 : st_ok tfibsegs E1 SS3 ms3.
Hypothesis Hmem3 : ss_mem SS3 = [r1; trim_lo r2 (-176); r3].
Hypothesis HMS : MSN0 = mkSS (ss_pc SS3) (sr_set (ss_regs SS3) 10%bv (SLit 0)) ([r1; r2; r3] ++ AGi4.NREGS) (ss_resv SS3) (ss_facts SS3).
Hypothesis Hx1 : ext3 r1 = ext3 R_soG.
Hypothesis Hx2 : ext3 r2 = ext3 R_scrG.
Hypothesis Hx3 : ext3 r3 = ext3 R_slotG.
Hypothesis Hwf : regions_wf [r1; r2; r3] = true.
Hypothesis Hc2 : YP09.r_chunks (trim_lo r2 (-176)) = YP09.r_chunks r2.
Hypothesis HWN : forall a, WN a -> (sp0 - AFSTACK <= a < sp0) \/ (TFIB_OOM <= a < TFIB_OOM + 1) \/ (TFIB_ERRNO <= a < TFIB_ERRNO + 4).
Hypothesis SEGN : forall W0 c, AGk1W.STN E0m W' regs0 memR mdR MSN0 W0 c -> SRr tfibsegs W0 c (AGk1W.RETN WN W' regs0 memR mdR).

Let msR : machine_state := mkst regsR (w64 A_REFILL_RET) memR (seg_rom tfibsegs).
Let cR : config := mkCfg msR (with_vm_backing (m_vm_lazy mdR) (m_vm_materialized mdR) mdR).

(* AGk1's section-b lemmas, cited. *)
Local Abbreviation ATN := (AGk1W.ATN B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree RW IFM TS inst ly S W regs0 mem0 md0 n
  HARX Hn0 FP LY Hsp Hso regsC memC SPC PRESC S' ly' W' regsR memR mdR HARXp Hly HFRA HPRR Hc0 HA0 E0m E1 SS3 MSN0 r1 r2 r3
  HE0_2 HE0_13 HE1 HS3 Hmem3 HMS Hx1 Hx2 Hx3 Hwf Hc2).
Local Abbreviation LEAFN := (AGk1W.LEAFN B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree RW RWB IFM TS inst ly S W regs0 regsU mem0 md0 n tr
  HARX LY Hsp HUo regsC memC mdC SPC AGC RAWC PRESC SIOC S' ly' W' memR mdR HARXp HLPp Hly HWLE HSIO HFRA HFRR HPRR Hc0 WN HWN).

(* the keep from Allocate's entry to the refill's return (MISS1's window, then the refill's keep) *)
Hypothesis HKC : MemnormT.memnorm_keep tfibsegs mem0 memR.

(* AGk1EW.miss_oom_tail_e with memnorm kept: the tail's raw frame (RETN, outside WN) after HKC. *)
Theorem miss_oom_tail_em : amreal tfibsegs (AGif0n.malloc_join_t stag n tr cl S') W' (cfg_at tfibsegs A_REFILL_RET regsR memR mdR)
(fun r W'' c'' => (exists trc, apath (mt n tr S) trc r /\ gflag trc = true) ->
  MemnormT.alloc_leaf_em tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regsU mem0 md0 n tr r W'' c'').
Proof.
(* copy of AGk1E.v:163-166 *)
unfold AGif0n.malloc_join_t. rewrite bind_assoc_eq. eapply amreal_pure; [exact (pop_miss S' cl Hc0)|]. eapply amreal_pure; [reflexivity|].
unfold AGif0n.malloc_K_t. cbn [amreal].
replace (cfg_at tfibsegs A_REFILL_RET regsR memR mdR) with cR by (unfold cfg_at, cR, msR; rewrite with_vm_backing_id; reflexivity).
eapply SRr_mono; [exact (SEGN W' cR ATN)|]. intros W6 c6 _ HR.
intros HPATH. apply alloc_leaf_em_of_e.
- exact (AGk1EW.alloc_leaf_e_null tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regsU mem0 md0 n tr (PNull, S') W6 c6 eq_refl
    (LEAFN W6 c6 HR HPATH)).
- intros regs1 mem1 md1 Hc. pose proof HR as (_ & regsx & memx & matx & Hcx & _ & _ & FRN & _ & _).
  assert (EQM : memx = mem1).
  { rewrite Hcx in Hc. unfold cfg_at in Hc. exact (f_equal (fun c => ms_mem (cfg_ms c)) Hc). }
  subst mem1. pose proof Hsp as (Hlo & _ & Hhi & _).
  exact (MemnormLocG.memnorm_keep_trans _ _ _ _ HKC
    (memnorm_winn ly sp0 WN memR memx LY Hlo Hhi HWN FRN)).
Qed.
End o.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* copy of AGimE.v:54-71 (AGim's section b), with the refill's memnorm-kept contract in place of IFME *)
(* ---------------------------------------------------------------------------------------------------------------- *)
(* AGim's section b: the same variables and hypotheses, in AGim's order, then the add-on and the image facts.        *)
Section b.
Variable B : asyms.
(* The trace premise (C5): a predicate on the trace and the state (cgif: In tr (as_universe B)). *)
Variable U : list Z -> astate -> Prop.
Variable mt : Z -> list Z -> M sptr.
Variable ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variables (nmax lmax : Z).
Variable lpost : astate -> Prop.
Variable dpost : Z -> alayout -> astate -> world tfibsegs -> list Z -> Z -> (word -> option byte) -> Prop.
Variables (mtag stag : Z).
Hypothesis IF : AIface B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag.
Hypothesis TS : TfibSyms B.
Variable rtree : Z -> M unit.
Variable RW : Z.
Hypothesis RWB : 0 <= RW /\ 176 + RW <= AFSTACK.
Hypothesis IFM : MnRefillW.AIfaceMw B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree RW.
(* The refill callee with errno and memnorm kept (MnRefillW.amm_refill_w_t), in place of AGimE's IFME. *)
Hypothesis RFm : MnRefillW.amm_refill_w_t B ARX AOX rpre lpost rtree RW.
(* The image facts of the grant leaf (cgif_file: ErrnoApartcgif.v). *)
Hypothesis EII : ErrnoApart.errno_in_img.
Hypothesis ESH : ErrnoApart.errno_apart_shadow_ag.
Hypothesis EDZ : ErrnoApart.errno_apart_dzone_ag.
(* AGim's section-b definitions. *)
Local Abbreviation Finst := (AGimW.Finst B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF).
Local Abbreviation Fmview := (AGimW.Fmview B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree RW IFM).
Local Abbreviation Fshape_miss := (AGimW.Fshape_miss B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree RW IFM).
Local Abbreviation vregs := AGimW.vregs.
Local Abbreviation vregs_other := AGimW.vregs_other.
Local Abbreviation vregs_10 := AGimW.vregs_10.
Local Abbreviation vregs_11 := AGimW.vregs_11.
Local Abbreviation vregs_12 := AGimW.vregs_12.

(* ---------------------------------------------------------------------------------------------------------------- *)
Section c.
Variables (inst : Z) (ly : alayout) (S : astate) (W : world tfibsegs).
Variables (regs0 regsU : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (n : Z) (tr : list Z).
Hypothesis HARX : ARX inst ly S W mem0 md0.
Hypothesis HRP : rpre S n.
Hypothesis Nrange0 : 49 <= n <= 64512.
Hypothesis Hmiss : pc_chunks (cache S (chunk_class n)) = [].
Hypothesis Hnnmax : n < nmax.
Hypothesis HBB : blocks_bytes S + n <= lmax.
Hypothesis Htr : U tr S.
Hypothesis Htrlen : (1 <= length tr <= 30)%nat.
Hypothesis Hn : getr regs0 10 = w64 n.
Hypothesis Hi11 : getr regs0 11 = w64 inst.
Hypothesis Htp : getr regs0 4 = w64 TFIB_TP.
Hypothesis Hgp : getr regs0 3 = w64 (as_gp B).
Hypothesis Hra : YK0s.ret_ok (getr regs0 1).
Hypothesis Hra4096 : 4096 <= bv_unsigned (getr regs0 1).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let SOv : Z := bv_unsigned (getr regs0 13).
Let BPv : Z := bv_unsigned (getr regs0 12).
Let T : Z := ly_T ly.
Let cl : Z := chunk_class n.
Let kz : Z := rz_log n.
Let csz : Z := class_size cl.
Let S1 : astate := set_nev (st_nev S + 1) S.
Let md0' : list word -> Model := fun mat => with_vm_backing (m_vm_lazy md0) mat md0.
Hypothesis Hsp : ly_stk_lo ly + AFSTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
Hypothesis Hso : sp0 <= SOv /\ SOv + 16 <= ly_stk_hi ly /\ SOv mod 8 = 0.
Hypothesis Hbp : sp0 <= BPv /\ BPv + 8 * 30 <= ly_stk_hi ly /\ BPv mod 8 = 0.
Hypothesis Hcf1 : getr regs0 15 = w64 1.
Hypothesis Hpres0 : forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis PSO : val_mem tfibsegs (mrestrict (w_H W) mem0) SOv 8 BPv.
Hypothesis PLEN : val_mem tfibsegs (mrestrict (w_H W) mem0) (SOv + 8) 8 (Z.of_nat (length tr)).
Hypothesis PBUF0 : forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem0) (BPv + 8 * Z.of_nat i) 8 (nth i tr 0).
(* field round 3: the refill's call-state facts at the entry memory (AbudgetRestate's lane text) *)
Hypothesis HRO0 : YG0dcf.arodata_ok_cf tfibsegs B mem0.
Hypothesis HUo : forall r : bv 5, bv_unsigned r <> 10 -> bv_unsigned r <> 11 -> bv_unsigned r <> 12 -> getr regsU r = getr regs0 r.
Hypothesis HU10 : getr regsU 10%bv = getr regs0 11%bv.
Hypothesis HU11 : getr regsU 11%bv = getr regs0 10%bv.
Hypothesis HU12 : getr regsU 12%bv = w64 8.
Hypothesis HU14 : getr regsU 14%bv = w64 1.

(* AGim's section-c facts. *)
Local Abbreviation Hn0 := (@AGimW.Hn0 ly regs0 n tr Nrange0 Htrlen).
Local Abbreviation Hkz1 := (@AGimW.Hkz1 n Nrange0).
Local Abbreviation Nrange := (@AGimW.Nrange n Nrange0).
Local Abbreviation FP := (@AGimW.FP n Nrange0).
Local Abbreviation Hcl := (@AGimW.Hcl ly regs0 n tr Nrange0 Htrlen).
Local Abbreviation Hvd := (@AGimW.Hvd ly regs0 n tr Htrlen).
Local Abbreviation LY := (AGimW.LY B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree RW IFM inst ly S W regs0 mem0 md0 n tr HARX Nrange0 Hmiss Htrlen).
Local Abbreviation IMG := (AGimW.IMG B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree RW IFM inst ly S W regs0 mem0 md0 n tr HARX Nrange0 Hmiss Htrlen).
Lemma Hcl_class : cl = chunk_class n. Proof. reflexivity. Qed.
Let E0m : env := AGis.E0 ly regs0 n tr cl 1 0 csz 0 0 0 0 0 0 kz.
Let DPOSTm : Z -> (word -> option byte) -> Prop := fun z m => dpost inst ly S W tr z m.
Local Abbreviation MISS1 := (AGimW.MISS1 B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF TS rtree RW IFM inst ly S W regs0 regsU mem0 md0 n tr
  HARX Nrange0 Hmiss Htrlen Hn Hi11 Htp Hsp Hso Hbp Hcf1 Hpres0 PSO PLEN PBUF0 HUo HU10 HU11 HU12 HU14).
Local Abbreviation ms1_shape := (AGimW.ms1_shape W).
Local Abbreviation RAZ1 := (AGimW.RAZ1 ly W regs0 n tr Htrlen).

(* copy of AGimE.v:147-150 *)
(* AGimW.PL over alloc_leaf_e: the leaf given its granted path. *)
Definition PL_e (r : sptr * astate) (W' : world tfibsegs) (c' : config) : Prop :=
(exists trc, apath (mt n tr S) trc r /\ gflag trc = true) ->
alloc_leaf_e tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regsU mem0 md0 n tr r W' c'.
(* AGimEW.PL_e over alloc_leaf_em. *)
Definition PL_em (r : sptr * astate) (W' : world tfibsegs) (c' : config) : Prop :=
(exists trc, apath (mt n tr S) trc r /\ gflag trc = true) ->
MemnormT.alloc_leaf_em tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regsU mem0 md0 n tr r W' c'.

(* --- The refill-call machine state (AGim's section f). --- *)
Section f.
Variables (ms1 : machine_state) (mat1 : list word) (Em : env).
Hypothesis HEm : forall k, (k < aHAV)%nat -> ew Em k = ew E0m k.
Hypothesis HSC : st_ok tfibsegs Em AGi4.MS_CALL (restrict (w_H W) ms1).
Hypothesis MEQW : forall x : word, ~ AGiu.WINM ly regs0 (bv_unsigned x) -> (ms_mem ms1) x = mem0 x.
Hypothesis PRESW : forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms1) a.
Hypothesis BUFW : forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms1)) (BPv + 8 * Z.of_nat i) 8 (nth i tr 0).
(* AGim's section-f facts: the call state's registers and frames. *)
Local Abbreviation AG1 := (AGimW.AG1 B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree RW IFM inst ly S W regs0 mem0 md0 n tr
  HARX Nrange0 Hmiss Htrlen ms1 Em HEm HSC MEQW).
Local Abbreviation RAW1 := (@AGimW.RAW1 ly regs0 mem0 ms1 MEQW).
Local Abbreviation SP1 := (AGimW.SP1 B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree RW IFM inst ly S W regs0 mem0 md0 n tr
  HARX Nrange0 Hmiss Htrlen Hsp Hso Hbp ms1 Em HEm HSC).
Local Abbreviation R_ra := (AGimW.R_ra W ms1 Em HSC).
Local Abbreviation R_gp := (AGimW.R_gp ly W regs0 n tr Htrlen ms1 Em HEm HSC).
Local Abbreviation R_tp := (AGimW.R_tp W ms1 Em HSC).
Local Abbreviation R_a0 := (AGimW.R_a0 ly W regs0 n tr Htrlen ms1 Em HEm HSC).
Local Abbreviation R_a1 := (AGimW.R_a1 ly W regs0 n tr Htrlen ms1 Em HEm HSC).
Local Abbreviation R_a2 := (AGimW.R_a2 inst ly W regs0 n tr Htrlen Hi11 ms1 Em HEm HSC).
Local Abbreviation R_a3 := (AGimW.R_a3 ly W regs0 n tr Htrlen ms1 Em HEm HSC).
(* MISS1's raw frame keeps memnorm (memnorm_winm). *)
Lemma MNW : MemnormT.memnorm_keep tfibsegs mem0 (ms_mem ms1).
Proof. pose proof Hsp as (Hlo & _ & Hhi & _). exact (memnorm_winm ly regs0 mem0 (ms_mem ms1) LY IMG Hlo Hhi MEQW). Qed.
(* The refill call: AGimW.REFILL's premises (AGimEW.REFILL_e), over RFm (the post rleaf_em keeps errno and memnorm). *)
Lemma REFILL_em : amreal tfibsegs (rtree cl S1) W (cfg_at tfibsegs A_Refill (ms_regs ms1) (ms_mem ms1) (md0' mat1))
  (MnRefillW.rleaf_em_w RW B ARX AOX lpost inst ly S n cl W (ms_regs ms1) (ms_mem ms1) (md0' mat1)).
Proof.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal).
exact (RFm inst ly S W mem0 md0 n sp0 (ms_regs ms1) (ms_mem ms1) mat1
  HARX HRP HRO0 Hn0 FP Hmiss Hlo Hbot Hhi Hal AG1 RAW1 PRESW SP1 R_ra (eq_trans R_gp Hgp) R_tp R_a0 R_a1 R_a2 R_a3).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* After the refill (AGim's section g0), with errno kept across the refill (rleaf_e).                                *)
Section g0.
Variables (S' : astate) (ly' : alayout) (W' : world tfibsegs) (regsR : bvmap 5 word) (memR : word -> option byte) (mdR : Model).
Hypothesis HARXp : ARX inst ly' S' W' memR mdR.
Hypothesis HLPp : lpost S'.
Hypothesis CIp : st_cache_inited S' = true.
Hypothesis HBBp : blocks_bytes S' = blocks_bytes S.
Hypothesis HDPp : st_depot S' = st_depot S.
Hypothesis Hly : layout_le (length (st_secs S)) ly ly'.
Hypothesis HWLE : wle W W'.
Hypothesis HAREGS : aregs_preserved (ms_regs ms1) regsR.
Hypothesis HSIO : same_io (md0' mat1) mdR.
Hypothesis HFRA : forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly S a -> ~ AOX ly' S' a -> ~ (spZ (ms_regs ms1) - RW <= a < spZ (ms_regs ms1)) ->
  aview tfibsegs (w_H W') memR a = aview tfibsegs (w_H W) (ms_mem ms1) a.
Hypothesis HFRR : forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ AOX ly' S' (bv_unsigned x) ->
  ~ (spZ (ms_regs ms1) - RW <= bv_unsigned x < spZ (ms_regs ms1)) -> memR x = ms_mem ms1 x.
Hypothesis HPRR : forall a, spZ (ms_regs ms1) - RW <= a < spZ (ms_regs ms1) -> apresent (w_H W') memR a.
Hypothesis HERR : errno_kept B (ms_mem ms1) memR.
(* the refill's keep (rleaf_em) *)
Hypothesis HMN : MemnormT.memnorm_keep tfibsegs (ms_mem ms1) memR.
Let E1 : env := havoc Em hRF (map (getr regsR) CLOB).
Local Abbreviation Hsp' := (@AGimW.Hsp' ly S regs0 Hsp ly' Hly).
Local Abbreviation HS3 := (AGimW.HS3 B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree RW RWB IFM inst ly S W regs0 mem0 md0 n tr
  HARX Nrange0 Hmiss Htrlen Hsp Hso Hbp ms1 Em HEm HSC S' ly' W' regsR memR mdR HARXp Hly HAREGS HFRA).

(* errno from the entry memory to the refill's return: MISS1's raw frame MEQW (Allocate's stack window and the
   unwinding byte), then the refill's errno_kept. *)
Lemma ERR1 : errno_kept B mem0 memR.
Proof.
intros i Hi. rewrite (HERR i Hi).
pose proof (ts_errno B TS) as EE. unfold TFIB_ERRNO in EE.
assert (Ra : 0 <= as_errno B + i < 2 ^ 64) by lia.
assert (Hae : as_errno B <= bv_unsigned (w64 (as_errno B + i)) < as_errno B + 4) by (rewrite w64_unsigned by exact Ra; lia).
apply MEQW. unfold AGiu.WINM. intros [Hs|Hu].
- refine (ErrnoApart.errno_apart_stack EII B ly _ _ _ TS LY IMG _ Hs Hae).
  pose proof Hsp as (Hlo & _). unfold sp0 in Hlo. lia.
- exact (ErrnoApart.errno_apart_unw EII B ly _ TS LY IMG Hu Hae).
Qed.

(* memnorm from the entry memory to the refill's return: MISS1's raw frame MEQW, then the refill's keep. *)
Lemma MN1 : MemnormT.memnorm_keep tfibsegs mem0 memR.
Proof. exact (MemnormLocG.memnorm_keep_trans _ _ _ _ MNW HMN). Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The a0 = 1 cache join, at the post-refill layout ly' (AGim's section g).                                         *)
Section g.
Variables (l : list Z) (off : Z).
Hypothesis Hcache' : pc_chunks (cache S' cl) = l ++ [off].
Hypothesis HA1 : getr regsR 10 = w64 1.
Let cnt' : Z := Z.of_nat (length (l ++ [off])).
Let v' : Z := off / 16.
Let DPOST' : Z -> (word -> option byte) -> Prop := fun z m => dpost inst ly' S' W' tr z m.
Local Abbreviation HV' := (AGimW.HV' B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree RW IFM inst ly regs0 n tr Nrange0 Htrlen S' ly' W' memR mdR HARXp CIp l off Hcache').
Local Abbreviation LY' := (AGimW.LY' B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree RW IFM inst ly regs0 n tr Nrange0 Htrlen S' ly' W' memR mdR HARXp CIp l off Hcache').
Local Abbreviation IMG' := (AGimW.IMG' B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree RW IFM inst ly regs0 n tr Nrange0 Htrlen S' ly' W' memR mdR HARXp CIp l off Hcache').
Local Abbreviation Hv' := (AGimW.Hv' B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag TS rtree RW IFM inst ly regs0 n tr Nrange0 Htrlen S' ly' W' memR mdR HARXp CIp l off Hcache').
(* AGimW.TAILJ (the remaining arguments are the join state's junk values). *)
Local Abbreviation TAILJ := (AGimW.TAILJ B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag IF TS rtree RW RWB IFM inst ly S W regs0 mem0 md0 n tr
  HARX Nrange0 Hmiss Htr Htrlen Hn Hi11 Htp Hgp Hra Hsp Hso Hbp Hcf1 PSO PLEN ms1 Em HEm HSC MEQW PRESW BUFW
  S' ly' W' regsR memR mdR HARXp CIp HDPp Hly HAREGS HFRA HPRR l off Hcache' HA1).
(* AGimW.LEAFJ (the remaining arguments are the junk byte of the join state and the result). *)
Local Abbreviation LEAFJ := (AGimW.LEAFJ B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree RW RWB IFM inst ly S W regs0 regsU mem0 md0 n tr
  HARX HRP Nrange0 Hmiss Hnnmax HBB Htr Htrlen Hsp Hso Hbp HUo ms1 mat1 Em HEm HSC MEQW PRESW
  S' ly' W' memR mdR HARXp CIp HBBp Hly HWLE HSIO HFRA HFRR HPRR l off Hcache').

Section gj.
Variables (jb : Z).
Hypothesis Hjb : 0 <= jb <= 255.
Hypothesis Hjb_def : val_mem tfibsegs (mrestrict (w_H W') memR) (AGis.Kv ly' cl v' + AGis.RZ kz - 15) 1 jb.
(* The join leaf with errno kept: AGimW.LEAFJ, and errno from the entry memory to the return memory (ERR1, then
   at_RETw's raw frame MEQF through AGikE.errno_kept_at_RETw). *)
Lemma LEAFJ_e : forall r W'' c'',
(exists odd z, r = (ck_user (new_chunk cl off n), st_final S' cl l off n tr z) /\ (odd = true <-> n mod 8 <> 0) /\
  at_RETw W' ly' regs0 memR mdR n cl cnt' v' jb kz DPOST' odd z W'' c'') -> PL_e r W'' c''.
Proof.
intros r W'' c'' H HPATH.
apply AGk1EW.alloc_leaf_e_of; [exact (LEAFJ jb Hjb Hjb_def r W'' c'' H HPATH)|].
intros _ regs1 mem1 md1 Hc.
destruct H as (odd & z & _ & _ & HR).
destruct HR as (_ & regs' & mem' & mat & Hc' & _ & _ & _ & MEQF & _).
assert (EQM : mem' = mem1).
{ rewrite Hc' in Hc. unfold cfg_at in Hc. exact (f_equal (fun c => ms_mem (cfg_ms c)) Hc). }
subst mem1.
assert (HC : 1 <= cl <= 31) by exact Hcl.
assert (CL : 0 <= cl < kNumClasses) by (unfold kNumClasses; lia).
assert (V0 : 0 <= v') by exact (proj1 Hv').
assert (N0 : 0 <= n) by lia.
assert (SPA : ly_stk_lo ly' + ImgBaseAG.AFSTACK <= bv_unsigned (getr regs0 2)) by exact (proj1 Hsp').
pose proof (AGikE.errno_kept_at_RETw EII ESH EDZ B ly' regs0 n cl v' kz odd memR mem' TS LY' IMG' SPA CL V0 N0 MEQF) as E2.
intros i Hi. rewrite (E2 i Hi). exact (ERR1 i Hi).
Qed.

(* LEAFJ_e with memnorm kept: MN1, then at_RETw's raw frame MEQF at the post-refill layout
   (MemnormHitG.memnorm_at_RETw). *)
Lemma LEAFJ_em : forall r W'' c'',
(exists odd z, r = (ck_user (new_chunk cl off n), st_final S' cl l off n tr z) /\ (odd = true <-> n mod 8 <> 0) /\
  at_RETw W' ly' regs0 memR mdR n cl cnt' v' jb kz DPOST' odd z W'' c'') -> PL_em r W'' c''.
Proof.
intros r W'' c'' H HPATH.
apply alloc_leaf_em_of_e; [exact (LEAFJ_e r W'' c'' H HPATH)|].
intros regs1 mem1 md1 Hc.
destruct H as (odd & z & _ & _ & HR).
destruct HR as (_ & regs' & mem' & mat & Hc' & _ & _ & _ & MEQF & _).
assert (EQM : mem' = mem1).
{ rewrite Hc' in Hc. unfold cfg_at in Hc. exact (f_equal (fun c => ms_mem (cfg_ms c)) Hc). }
subst mem1.
assert (HC : 1 <= cl <= 31) by exact Hcl.
assert (CL : 0 <= cl < kNumClasses) by (unfold kNumClasses; lia).
pose proof Hsp' as (SPA & _ & SPH & _).
refine (MemnormLocG.memnorm_keep_trans _ _ _ _ MN1
  (MemnormHitG.memnorm_at_RETw B ly' regs0 n cl v' kz odd memR mem' TS LY' IMG' SPA SPH CL (proj1 Hv') (proj2 Hv') _ Hkz1 MEQF)).
lia.
Qed.
End gj.

(* AGimEW.JOIN_e over LEAFJ_em. *)
Lemma JOIN_em : amreal tfibsegs (malloc_join_t stag n tr cl S') W' (cfg_at tfibsegs 0x36528 regsR memR mdR) PL_em.
Proof.
(* copy of AGimE.v:272-275 *)
destruct (@AGiz.vw_junk_values _ _ B W' ly' inst memR n cl cnt' v' kz TS HV' Hkz1 Nrange Hcl_class)
  as (j0 & j1 & j2 & j3 & j4 & jb & Hj0 & Hj1 & Hj2 & Hj3 & Hj4 & Hjb & Hjb_def).
eapply amreal_mono; [| eapply TAILJ; eassumption].
intros r W'' c'' H. eapply LEAFJ_em; eassumption.
Qed.
End g.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The a0 = 0 class-full OOM arm (AGimE's section h), over miss_oom_tail_em. *)
Section h.
Hypothesis Hc0 : pc_chunks (cache S' cl) = [].
Hypothesis HA0 : getr regsR 10 = w64 0.
Local Abbreviation HE1 := (@AGimW.HE1 ly regs0 n tr Htrlen Em HEm regsR).
Lemma OOMJ_em : amreal tfibsegs (malloc_join_t stag n tr cl S') W' (cfg_at tfibsegs 0x36528 regsR memR mdR) PL_em.
Proof.
(* copy of AGimE.v:288-297, over miss_oom_tail_em (+ MN1) *)
assert (HWN : forall a, AGiv.WINN regs0 a -> (bv_unsigned (getr regs0 2) - AFSTACK <= a < bv_unsigned (getr regs0 2)) \/
  (TFIB_OOM <= a < TFIB_OOM + 1) \/ (TFIB_ERRNO <= a < TFIB_ERRNO + 4))
by (intros a X; unfold AGiv.WINN in X; cbv zeta in X; lia).
exact (miss_oom_tail_em B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag rtree RW RWB IFM TS inst ly S W regs0 regsU mem0 md0 n tr
  HARX Hn0 FP LY Hsp Hso HUo (ms_regs ms1) (ms_mem ms1) (md0' mat1) SP1 AG1 RAW1 PRESW (AGimW.same_io_wvb md0 mat1)
  S' ly' W' regsR memR mdR HARXp HLPp Hly HWLE HSIO HFRA HFRR HPRR Hc0 HA0
  E0m E1 AGi4.SS3 AGi4.MS_N0 AGi4.R3bst AGi4.R3scr AGi4.R3top (AGiv.WINN regs0)
  ltac:(reflexivity) ltac:(reflexivity) HE1 HS3 ltac:(reflexivity) AGi4.MS_N0_eq eq_refl eq_refl eq_refl
  ltac:(reflexivity) ltac:(reflexivity) HWN
  (fun W0 c H => @AGiv.segN _ _ W' ly regs0 memR mdR n tr cl 1 0 csz 0 0 0 0 0 0 kz Hvd LY IMG Htp Hra Hsp Htrlen DPOSTm [] 0 W0 c H)
  MN1).
Qed.
End h.
End g0.
End f.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* AGimEW.missg_core_e over alloc_leaf_em: the refill through REFILL_em (rleaf_em), the branches through OOMJ_em /
   JOIN_em. *)
Lemma missg_core_em : amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs A_Allocate regsU mem0 md0)
(MemnormT.alloc_leaf_em tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regsU mem0 md0 n tr).
Proof.
(* copy of AGimE.v:309-344, over the _em lemmas *)
assert (CORE : amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs A_Allocate regsU mem0 md0) PL_em).
{
rewrite (Fshape_miss n tr S Hn0 FP Hmiss). fold cl.
eapply amreal_pure; [reflexivity|].
eapply amreal_pure; [unfold mcheck; replace (n <? kMaxAllowedMalloc - kPage) with true by (symmetry; apply Z.ltb_lt; unfold kMaxAllowedMalloc, kPage; lia); reflexivity|].
change (set_nev (st_nev S + 1) S) with S1.
eapply (YG0d.amreal_mbind tfibsegs (rtree cl) (fun _ : unit => malloc_join_t stag n tr cl) S1 W _
(fun r W1 c1 => exists ms1 mat1 Em,
  ((forall k, (k < aHAV)%nat -> ew Em k = ew E0m k) /\ st_ok tfibsegs Em AGi4.MS_CALL (restrict (w_H W) ms1) /\
   (forall x : word, ~ AGiu.WINM ly regs0 (bv_unsigned x) -> ms_mem ms1 x = mem0 x) /\
   (forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms1) a) /\
   (forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms1)) (BPv + 8 * Z.of_nat i) 8 (nth i tr 0))) /\
  MnRefillW.rleaf_em_w RW B ARX AOX lpost inst ly S n cl W (ms_regs ms1) (ms_mem ms1) (md0' mat1) r W1 c1)).
- (* MISS1, then the refill callee *)
  eapply amreal_SRr_pre; [exact MISS1|]. intros W1 c1 _ HC.
  destruct HC as (-> & ms1 & mat1 & Em & -> & HEm & HSC & MEQW & PRESW & BUFW).
  assert (SHAPE : ms1 = mkst (ms_regs ms1) (w64 0x369c8) (ms_mem ms1) (seg_rom tfibsegs)) by (eapply ms1_shape; eassumption).
  assert (RR : amreal tfibsegs (rtree cl S1) W (cfg_at tfibsegs A_Refill (ms_regs ms1) (ms_mem ms1) (md0' mat1))
    (MnRefillW.rleaf_em_w RW B ARX AOX lpost inst ly S n cl W (ms_regs ms1) (ms_mem ms1) (md0' mat1))) by (eapply REFILL_em; eassumption).
  unfold cfg_at, A_Refill in RR. rewrite SHAPE at 1.
  eapply amreal_mono; [| exact RR]. intros r W2 c2 HRL. exists ms1, mat1, Em. split; [|exact HRL]. repeat (split; [assumption|]). exact BUFW.
- (* the post-refill branch on the class cache *)
  intros [] Sp W1 c1 (ms1 & mat1 & Em & (HEm & HSC & MEQW & PRESW & BUFW) & HRL).
  destruct HRL as (ly' & regsR & memR & mdR & -> & HARXp & HLPp & CIp & HBBp & HDPp & Hly & HWLE & HAREGS & HSIO & HFRA & HFRR & HERR & HMN & HPRR & HA0e).
  cbn [snd] in *.
  assert (RA : raZ (ms_regs ms1) = 0x36528) by (eapply RAZ1; eassumption). rewrite RA.
  destruct (pc_chunks (cache Sp cl)) as [|x t] eqn:El.
  + assert (HA0 : getr regsR 10 = w64 0) by (rewrite HA0e; try rewrite El; reflexivity).
    eapply OOMJ_em; eassumption.
  + assert (LX : exists l off, x :: t = l ++ [off]) by (exists (List.removelast (x :: t)), (List.last (x :: t) 0); apply List.app_removelast_last; discriminate).
    destruct LX as (l & off & LX). rewrite LX in El.
    assert (HA1 : getr regsR 10 = w64 1) by (rewrite HA0e; try rewrite El; destruct l; reflexivity).
    eapply JOIN_em; eassumption.
}
eapply amreal_mono; [| exact (amreal_apath_gflag tfibsegs (mt n tr S) W (cfg_at tfibsegs A_Allocate regsU mem0 md0) PL_em CORE)].
intros r W' c' [HL HP]. exact (HL HP).
Qed.
End c.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The theorem: AGimEW.alloc_missg_e concluding alloc_leaf_em. *)
Theorem alloc_missg_em : forall inst so bp ly S W regs mem md n tr,
alloc_pre tfibsegs B U ARX rpre nmax lmax 8 1 1 inst so bp ly S W regs mem md n tr ->
YG0dcf.arodata_ok_cf tfibsegs B mem ->
49 <= n <= 64512 -> pc_chunks (cache S (chunk_class n)) = [] ->
amreal tfibsegs (mt n tr S) W (cfg_at tfibsegs 0x31bd8 regs mem md)
(MemnormT.alloc_leaf_em tfibsegs B mt ARX AOX lpost TFIB_OOM inst ly S W regs mem md n tr).
Proof.
(* copy of AGimE.v:357-401, over missg_core_em *)
intros inst so bp ly S W regs mem md n tr PRE HRO Nrange0 Hmiss.
destruct PRE as (HARX & HRP & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & Hpres0 & Hgp & Htp & Hr10 & Hr11 & Hr12 & Hr13 & Hr14 & Hr15 &
Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htrlen & PSO & PLEN & PBUF & Htr & Hn0 & Hlive).
unfold spZ, raZ, AFSTACK_G in *. rewrite (ts_tp B TS) in Htp.
pose proof (Finst inst ly S W mem md HARX) as HIO. pose proof HIO as (HIO1 & HIO2 & HIO3).
assert (Hnn : n < nmax) by lia.
assert (FP0 : from_primary n = true) by (eapply AGimW.FP; eassumption).
pose proof (Fmview inst ly S W mem md n HARX ltac:(lia) FP0 Hmiss) as HMV0.
pose proof (lo_top ly (AGif0n.mv_ly B W ly inst mem (chunk_class n) HMV0)) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
set (regs0 := vregs regs n inst bp).
assert (Hso64 : 0 <= so < 2 ^ 64) by (unfold kHighMemEnd, kHighMemBeg in T4, T7; lia).
assert (Hbp64 : 0 <= bp < 2 ^ 64) by (unfold kHighMemEnd, kHighMemBeg in T4, T7; lia).
assert (Hinst64 : 0 <= inst < 2 ^ 64) by lia.
assert (HUo : forall r : bv 5, bv_unsigned r <> 10 -> bv_unsigned r <> 11 -> bv_unsigned r <> 12 -> getr regs r = getr regs0 r)
by (intros r H10 H11 H12; unfold regs0; symmetry; exact (vregs_other regs n inst bp r H10 H11 H12)).
assert (HU10 : getr regs 10%bv = getr regs0 11%bv) by (unfold regs0; rewrite Hr10, vregs_11; reflexivity).
assert (HU11 : getr regs 11%bv = getr regs0 10%bv) by (unfold regs0; rewrite Hr11, vregs_10; reflexivity).
assert (HU12 : getr regs 12%bv = w64 8) by exact Hr12.
assert (HU14 : getr regs 14%bv = w64 1) by exact Hr14.
assert (Hn : getr regs0 10 = w64 n) by (unfold regs0; apply vregs_10).
assert (Hi11 : getr regs0 11 = w64 inst) by (unfold regs0; apply vregs_11).
assert (R2 : getr regs0 2 = getr regs 2) by (unfold regs0; apply vregs_other; bvne).
assert (R1 : getr regs0 1 = getr regs 1) by (unfold regs0; apply vregs_other; bvne).
assert (R12 : bv_unsigned (getr regs0 12) = bp) by (unfold regs0; rewrite vregs_12; apply w64_unsigned; exact Hbp64).
assert (R13 : bv_unsigned (getr regs0 13) = so)
by (unfold regs0; rewrite (vregs_other regs n inst bp 13%bv) by bvne; rewrite Hr13; apply w64_unsigned; exact Hso64).
assert (Htp0 : getr regs0 4 = w64 TFIB_TP) by (unfold regs0; rewrite (vregs_other regs n inst bp 4%bv) by bvne; exact Htp).
assert (Hgp0 : getr regs0 3 = w64 (as_gp B)) by (unfold regs0; rewrite (vregs_other regs n inst bp 3%bv) by bvne; exact Hgp).
assert (Hcf1 : getr regs0 15 = w64 1) by (unfold regs0; rewrite (vregs_other regs n inst bp 15%bv) by bvne; exact Hr15).
assert (Hra0 : YK0s.ret_ok (getr regs0 1)) by (rewrite R1; exact Hra).
assert (Hra40 : 4096 <= bv_unsigned (getr regs0 1)) by (rewrite R1; exact Hra4096).
assert (Hsp : ly_stk_lo ly + AFSTACK <= bv_unsigned (getr regs0 2) /\ ly_bot ly < bv_unsigned (getr regs0 2) /\
bv_unsigned (getr regs0 2) <= ly_stk_hi ly /\ bv_unsigned (getr regs0 2) mod 16 = 0) by (rewrite R2; unfold AFSTACK; repeat split; assumption).
assert (Hso : bv_unsigned (getr regs0 2) <= bv_unsigned (getr regs0 13) /\ bv_unsigned (getr regs0 13) + 16 <= ly_stk_hi ly /\
bv_unsigned (getr regs0 13) mod 8 = 0) by (rewrite R2, R13; repeat split; assumption).
assert (Hbp : bv_unsigned (getr regs0 2) <= bv_unsigned (getr regs0 12) /\ bv_unsigned (getr regs0 12) + 8 * 30 <= ly_stk_hi ly /\
bv_unsigned (getr regs0 12) mod 8 = 0) by (rewrite R2, R12; repeat split; assumption).
assert (Hpres00 : forall a, bv_unsigned (getr regs0 2) - AFSTACK <= a < bv_unsigned (getr regs0 2) -> apresent (w_H W) mem a)
by (rewrite R2; unfold AFSTACK; exact Hpres0).
assert (PSO0 : val_mem tfibsegs (mrestrict (w_H W) mem) (bv_unsigned (getr regs0 13)) 8 (bv_unsigned (getr regs0 12))) by (rewrite R13, R12; exact PSO).
assert (PLEN0 : val_mem tfibsegs (mrestrict (w_H W) mem) (bv_unsigned (getr regs0 13) + 8) 8 (Z.of_nat (length tr))) by (rewrite R13; exact PLEN).
assert (PBUF0 : forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem) (bv_unsigned (getr regs0 12) + 8 * Z.of_nat i) 8 (nth i tr 0))
by (rewrite R12; exact PBUF).
change (cfg_at tfibsegs 0x31bd8 regs mem md) with (cfg_at tfibsegs A_Allocate regs mem md).
eapply (missg_core_em inst ly S W regs0 regs mem md n tr); eassumption.
Qed.
End b.
End a.
