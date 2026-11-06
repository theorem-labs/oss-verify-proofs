(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/MemnormDmid.v (a working branch 29b7505aa27, file sha256 8164a0d31ef3) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 f0d2e8d40c7e; pin d83eb25dbf0d); module paths changed; its 3 image addresses moved by code-verified function pairs (3 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 0 code pcs the tool read as sizes, by the internal file funcpair.py); no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from the old pin A (pinned fuzz_preset.asan d83eb25dbf0d, twin f0d2e8d40c7e; this file at 3d44582d342f) to A' (#102 pin 1be0f53d96cb, twin bff8519bbe3e) by the relocation route of record, frozen alreloc ced0368250cb6538 (a working branch b85bfdee67c4), --assume-source, --resolve the internal file resolve-102.txt (0 lines name this file); 3 numerals changed. *)
(* Modified by Theorem Labs, 2026-10-30: a Theorem Labs lane's delta to proofs/cgif/cgif_file_fuzzer/lib/MemnormDmid.v (29b7505aa27 -> a working branch 5ad50e61fc6a, file sha256 cf594a16c154) applied at A' by the 3-way merge of record (the internal file p2merge.sh): the call memory MP and DMiface's 0 <= a < 2^64 guard on the qhdr presence clause. 0 conflicts; the added lines equal the source delta's; no numeral in the delta. *)
(* Theorem Labs, 2026-10 (task MEMNORM): the two Deallocate arms that call QuarantineCache::Enqueue (the mid arm,
   DGg2, and the drain arm, DGfz), with errno and memnorm kept on the raw memory.
   rule 24: no function proved (kind: arm twins, frame corollaries over the callees' memnorm-kept contracts).

   Both walks are generic in the callee's extra conjunct: DGg2.mid_walk over any Enqueue relation XR, DGfz.mid_walk_x /
   TAILD_x over any Enqueue / Drain relations that give the raw one back.  Here XR is MnEnq.acall_raw_em_x (the raw
   frame, errno kept, memnorm kept), so the arms need the callees' memnorm-kept contracts [ENQm]
   (MnEnq.de_enqueue_m_t) and [DRNm] (MnDrain.de_drain_m_t).  No walk is re-run.
   The keep is the chain of the walk's own raw facts and the callees' keeps:
   - Deallocate's entry to Enqueue's call: dmem_m's frame (outside DGif0.dwin_m, the depot zone, the internal
     allocator's zone and the block's shadow), none of whose bytes is read-only or reaches TASK_SIZE
     ([memnorm_dmem_m], from DGgm.free_hyps: the stack window is in the layout's stack, the thread-object cells and
     the chunk header / first word are zone3 extents below ASAN_CEIL (DGgm.LYB, DGgm.derived_ranges, DGgm.fh_Hp), the
     depot and internal-allocator zones are as in MemnormDcommon.memnorm_dmem_c, the shadow lies in
     [SHADOW_OFF + 514, kHighMemBeg));
   - each callee: its contract's keep (MnEnq.acall_raw_em_x's third conjunct);
   - Put's run between and after the callees: the 80-byte frame [sp0 - 80, sp0), in the layout's stack ([mn_keep_stack]).
   errno is as in DGg2.dealloc_mid_e / DGfz.drain_arm_c_e (copied, marked), at the raw form.
   The arms conclude MemnormT.dealloc_leaf_raw_em.  DGg2, DGfz and every existing statement are unchanged. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AE3d AFeq DGbase AFex.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFfj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AFew DGgm DGfw DGgd DGgf AFeu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0k.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB13.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import AllocG DeallocG AGif0n DMspec DGif0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DIfaceR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DGg1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require ErrnoG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DGleafE.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require ErrnoApart.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import DGgi DGfv.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DGg2 DGfz.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require MemnormHitG MemnormSafeA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormLocG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require MemnormLoc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MnEnq MnDrain.
(* As DGfz.v / DGg2.v: ErrnoG / ErrnoApart reach YA09, whose non-local [Ltac ::=] turns zify's euclidean-division
   conversion off; the copied errno scripts were written with it on.  #[local]: the setting stays in this file. *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope Z_scope.
Local Open Scope am_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* A stack window of the layout keeps memnorm: its bytes are at or above kImgEnd and below TASK_SIZE. *)
Lemma mn_keep_stack : forall ly (lo sp : Z) (m m' : word -> option byte), layout_ok ly ->
  ly_stk_lo ly <= lo -> sp <= ly_stk_hi ly ->
  (forall x : word, ~ (lo <= bv_unsigned x < sp) -> m' x = m x) -> MemnormT.memnorm_keep tfibsegs m m'.
Proof.
intros ly lo sp m m' LY Hlo Hhi F.
pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7).
apply (MemnormLocG.memnorm_keep_window tfibsegs (fun a => lo <= a < sp) m m'); [|exact F].
intros x Hx. apply MemnormHitG.mn_safe_high. unfold kHighMemBeg, kHighMemEnd, kImgEnd, TASK_SIZE in *. lia.
Qed.

(* memnorm is kept by a memory that equals [mem0] outside dmem_m's frame zones (DGif0.dmem_m), over the seed's
   DGgm.free_hyps. *)
Lemma memnorm_dmem_m : forall W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU (sp0 : Z) (mem' : word -> option byte),
  DGgm.free_hyps W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU -> sp0 = bv_unsigned (getr regs0 2) ->
  (forall x : word, ~ dwin_m ly sp0 p (bv_unsigned x) -> ~ DGgi.DZONE ly (bv_unsigned x) ->
    ~ DGgi.IZONE (bv_unsigned x) -> ~ dshadow p nn (bv_unsigned x) -> mem' x = mem0 x) ->
  MemnormT.memnorm_keep tfibsegs mem0 mem'.
Proof.
intros W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU sp0 mem' FH E0 MEQ. subst sp0.
pose proof (DGgm.LYB W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH)
  as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & T1 & T2 & T3 & T4 & T5).
pose proof (DGgm.derived_ranges W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & _).
pose proof (DGgm.fh_Hsp W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH) as (S1 & S2 & S3).
pose proof (DGgm.fh_Hp W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH) as HP.
pose proof (ASAN_CEIL_range) as [CR _].
apply (MemnormT.memnorm_frame4 tfibsegs (dwin_m ly (bv_unsigned (getr regs0 2)) p) (DGgi.DZONE ly) DGgi.IZONE
  (dshadow p nn) mem0 mem').
- intros x Hw. unfold dwin_m, DGgmC.WINT, DGgmC.WINB in Hw. cbv beta zeta in Hw.
  destruct Hw as [Hw|[[Hw|Hw]|[Hw|Hw]]].
  + apply MemnormHitG.mn_safe_high.
    unfold DGbaseC.DFSTACK, DGbase.DFSTACK, kHighMemBeg, kHighMemEnd, kImgEnd, TASK_SIZE in *. lia.
  + apply (MemnormLoc.mn_safe_zone3 (ly_T ly) kThreadObjSize x F1); [|exact F2].
    unfold t_unwinding, kThreadObjSize in *. lia.
  + apply (MemnormLoc.mn_safe_zone3 (ly_T ly) kThreadObjSize x F1); [|exact F2].
    unfold t_stats, kThreadObjSize in *. lia.
  + apply (MemnormLoc.mn_safe_zone3 (p - 16) (DGgm.N8v nn + 16) x HP); lia.
  + apply (MemnormLoc.mn_safe_zone3 (p - 16) (DGgm.N8v nn + 16) x HP); lia.
- (* as MemnormDcommon.memnorm_dmem_c *)
  intros x Hd. unfold DGgi.DZONE in Hd. destruct Hd as [Hd|[Hd|Hd]].
  + apply MemnormSafeA.mn_safe_rw. unfold TASK_SIZE. lia.
  + pose proof (zone3_off_img _ _ _ F9 Hd) as O.
    apply MemnormSafeA.mn_safe_offimg; unfold off_img, TFIB_IMG_LO, TFIB_IMG_END, TASK_SIZE in *; lia.
  + pose proof (zone3_off_img _ _ _ F11 Hd) as O.
    apply MemnormSafeA.mn_safe_offimg; unfold off_img, TFIB_IMG_LO, TFIB_IMG_END, TASK_SIZE in *; lia.
- intros x Hz. unfold DGgi.IZONE in Hz. apply MemnormSafeA.mn_safe_rw.
  unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TASK_SIZE in *. lia.
- intros x Hs. unfold dshadow, DGgiC.SPv, DGgiC.CNT8v, DGgiC.N8v in Hs.
  unfold DGgm.SPv, DGgm.CNT8v, DGgm.N8v in D3, D4.
  apply MemnormSafeA.mn_safe_offimg; unfold TFIB_IMG_LO, TFIB_IMG_END, SHADOW_OFF, kHighMemBeg, TASK_SIZE in *; lia.
- exact MEQ.
Qed.

(* MnEnq.acall_raw_em_x gives the raw conjunct back (DGfz.xr_raw at rawb = true). *)
Lemma xr_raw_em : forall B AOX, DGfz.xr_raw B AOX true (MnEnq.acall_raw_em_x B AOX).
Proof. intros B AOX inst stk ly S W regs mem md E ly' S' W' regs' mem' md' H _. exact (proj1 H). Qed.

(* copy of DGfz.v:88-103 / DGg2.v:149-163 (the section header), plus the callees' memnorm-kept contracts and the
   ErrnoApart image facts the copied errno scripts read (DGfz.v:113-116) *)
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
Variable MP : (word -> option byte) -> Prop.
Hypothesis IF : DIface B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP.
Hypothesis ENQm : MnEnq.de_enqueue_m_t B U ARX AOX rpre lpost fpre dpost L24 QB MP.
Hypothesis DRNm : MnDrain.de_drain_m_t B ARX AOX dbody L24 QB.
(* DGfz.MP_keep / DGg2.MP_keep (the walks' keep law of MP) *)
Hypothesis MP_keep : forall W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU (mem' : word -> option byte),
  DGgm.free_hyps W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU ->
  (forall x : word, ~ dwin_m ly (bv_unsigned (getr regs0 2)) p (bv_unsigned x) -> ~ dg_dzone ly (bv_unsigned x) ->
    ~ dg_izone (bv_unsigned x) -> ~ dshadow p nn (bv_unsigned x) -> mem' x = mem0 x) ->
  MP mem0 -> MP mem'.
Hypothesis EAimg : ErrnoApart.errno_in_img.
Hypothesis EAz3 : ErrnoApart.errno_apart_zone3_d.
Hypothesis EAdz : ErrnoApart.errno_apart_dzone_d.
Hypothesis EAiz : ErrnoApart.errno_apart_izone.

(* The mid arm (a new batch, no drain): DGg2.mid_walk at MnEnq.acall_raw_em_x. *)
Theorem dealloc_mid_em : forall inst so bp ly S W regs mem md p n tr,
DeallocG.dealloc_pre tfibsegs B U ARX rpre fpre 1 inst so bp ly S W regs mem md p n tr -> MP mem ->
In (p, n) (blocks S) -> need_new_batch (st_qthread S) = true ->
qc_bytes (st_qthread S) + req_size n + (if need_new_batch (st_qthread S) then kBatchBytes else 0) <= kQuarantineCacheMax ->
amreal tfibsegs (ft p tr S) W (cfg_at tfibsegs 0x322a4 regs mem md)
(MemnormT.dealloc_leaf_raw_em tfibsegs B ft ARX AOX lpost inst ly S W regs mem md p n tr).
Proof.
intros inst so bp ly S W regs mem md p n tr PRE HMP HBLK HNB Hcache.
pose proof (DGg2.mid_walk B TS U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF MP_keep
  (MnEnq.acall_raw_em_x B AOX) ENQm inst so bp ly S W regs mem md p n tr PRE HMP HBLK HNB Hcache) as MAIN.
pose proof PRE as PRE0.
destruct PRE as (HARX & HRP & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & Hpres & Hgp & Htp & Hr10 & Hr11 & Hr12 & Hr13 & Hr14 & Hr15 &
Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htrlen & PSO & PLEN & PBUF & Htr & Hp0 & HFP).
pose proof (di_view B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF inst ly S W mem md p n HARX HRP HFP HBLK) as DV.
pose proof (di_inst B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF inst ly S W mem md HARX) as HIO.
destruct (DGg1.FH_m B TS U ARX rpre fpre inst so bp ly S W regs mem md p n tr PRE0 HBLK HIO DV)
  as (hb1 & j1 & j2 & j3 & Hhb1 & Hhdr & FH).
(* copy of DGg2.v:619-624 *)
destruct DV as [[LY IMG _ _ _ _ _] _ _ _ _ _ _ (HZp & _ & _ & HNN) _ _].
assert (Hpa : 0 <= sptr_addr B ly p) by (destruct HZp as [Z0 _]; lia).
assert (HSP : ly_stk_lo ly + DGbaseC.DFSTACK <= bv_unsigned (getr regs 2))
  by (unfold DGbaseC.DFSTACK, DFSTACK_G, spZ in *; lia).
assert (EB : forall i, 0 <= i < 4 -> bv_unsigned (w64 (as_errno B + i)) = as_errno B + i)
  by (intros i Hi; rewrite (ts_errno B TS); unfold w64; apply unsigned_lit_small; unfold TFIB_ERRNO; lia).
assert (RG2 : getr (dregs regs (sptr_addr B ly p) inst bp so) 2 = getr regs 2) by (apply dregs_other; vm_compute; discriminate).
eapply amreal_mono; [| exact (amreal_apath_gflag tfibsegs _ _ _ _ MAIN)].
intros r Wo co [(regsR & memR & mdR & -> & HPOST & HLP & X & regsC & memC & mdC & regsE & memE & mdE & HX & RAWC & DMC & FRT)
  HPATH].
destruct HX as (HXr & HXe & HXm).
(* copy of DGg2.v:630-639: errno from Deallocate's entry to Enqueue's call, and from Enqueue's return to Put's ret *)
assert (ERRC : ErrnoG.errno_kept B mem memC).
{ intros i Hi. apply DMC; rewrite (EB i Hi); intros Hw.
  - apply (ErrnoApart.errno_apart_dwin_m EAimg EAz3 B ly _ _ _ _ TS LY IMG HSP HZp (proj1 HNN) Hw). lia.
  - apply (EAdz B ly _ TS LY IMG Hw). lia.
  - apply (EAiz B _ TS Hw). lia.
  - apply (ErrnoApart.errno_apart_dshadow EAimg B ly _ _ _ TS LY IMG Hpa Hw). lia. }
assert (ERRT : ErrnoG.errno_kept B memE memR).
{ intros i Hi. apply FRT. rewrite (EB i Hi). intros Hw.
  refine (ErrnoApart.errno_apart_stack EAimg B ly _ _ _ TS LY IMG _ Hw _); unfold DFSTACK_G, spZ in *; lia. }
(* memnorm: dmem_m's frame, Enqueue's keep, Put's 80-byte frame *)
assert (MNC : MemnormT.memnorm_keep tfibsegs mem memC).
{ refine (memnorm_dmem_m W ly _ mem tr _ _ hb1 _ j1 j2 j3 regs (bv_unsigned (getr regs 2)) memC FH _ DMC).
  rewrite RG2. reflexivity. }
assert (MNT : MemnormT.memnorm_keep tfibsegs memE memR).
{ apply (mn_keep_stack ly (bv_unsigned (getr regs 2) - 80) (bv_unsigned (getr regs 2)) memE memR LY);
    [unfold DFSTACK_G, spZ in *; lia | unfold spZ in *; lia | exact FRT]. }
exists ly, regsR, memR, mdR. split; [reflexivity|].
split.
{ destruct HPOST as (H1 & H2 & H3 & H4 & H5 & H6 & H7).
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj (RAWC HXr) H7))))))). }
split; [intros i Hi; rewrite (ERRT i Hi), (HXe i Hi); exact (ERRC i Hi)|].
split; [exact (MemnormLocG.memnorm_keep_trans _ _ _ _ MNC (MemnormLocG.memnorm_keep_trans _ _ _ _ HXm MNT))|].
split; [exact HLP | exact HPATH].
Qed.

(* The drain arm (Enqueue, then Drain): DGfz.mid_walk_x and DGfz.TAILD_x at MnEnq.acall_raw_em_x. *)
Theorem dealloc_drn_em : forall inst so bp ly S W regs mem md p n tr,
DeallocG.dealloc_pre tfibsegs B U ARX rpre fpre 1 inst so bp ly S W regs mem md p n tr -> MP mem ->
In (p, n) (blocks S) ->
kQuarantineCacheMax < qc_bytes (st_qthread S) + req_size n + (if need_new_batch (st_qthread S) then kBatchBytes else 0) ->
amreal tfibsegs (ft p tr S) W (cfg_at tfibsegs 0x322a4 regs mem md)
(MemnormT.dealloc_leaf_raw_em tfibsegs B ft ARX AOX lpost inst ly S W regs mem md p n tr).
Proof.
intros inst so bp ly S W regs mem md p n tr PRE HMP HBLK DRAIN.
pose proof PRE as PRE0.
destruct PRE0 as (HARX & HRP & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & Hpres & Hgp & Htp & Hr10 & Hr11 & Hr12 & Hr13 & Hr14 & Hr15 &
Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htrlen & PSO & PLEN & PBUF & Htr & Hp0 & HFP).
(* copy of DGfz.v:724-728 *)
pose proof (di_view _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md p n HARX HRP HFP HBLK) as DV.
destruct (dv_chunk _ _ _ _ _ _ _ _ DV) as (k & HK & HKS & _ & HKR).
pose proof (dv_nonnull _ _ _ _ _ _ _ _ DV) as PNN.
pose proof (di_inst _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IF inst ly S W mem md HARX) as HIO.
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
assert (MAIN : amreal tfibsegs (ft p tr S) W (cfg_at tfibsegs 0x322a4 regs mem md)
  (fun r W' c' => exists ly' regs' mem' md',
    c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
    dealloc_post tfibsegs B ARX AOX inst ly S W regs mem md
      (fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n) ly' (snd r) W' regs' mem' md' /\
    (true = true -> forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ AOX ly' (snd r) (bv_unsigned x) ->
      ~ ascratch B DFSTACK_G regs (bv_unsigned x) ->
      ~ (p <> PNull /\ sptr_addr B ly p <= bv_unsigned x < sptr_addr B ly p + req_size n) -> mem' x = mem x) /\
    ErrnoG.errno_kept B mem mem' /\ MemnormT.memnorm_keep tfibsegs mem mem' /\ lpost (snd r))).
{ apply (DGfz.mid_walk_x B TS U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP true IF MP_keep
    inst so bp ly S W regs mem md p n tr PRE HMP HBLK (MnEnq.acall_raw_em_x B AOX) ENQm (xr_raw_em B AOX)
    k hb1 j1 j2 j3 HK HKS Hhb1 Hhdr FH).
  intros z msE matE E5 W5 regs' mem' md' X' nb ER XE DMfr.
  eapply amreal_mono; [| exact (DGfz.TAILD_x B TS U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP true IF
    inst so bp ly S W regs mem md p n tr PRE HBLK DRAIN k hb1 j1 j2 j3 HK HKS HKR PNN FH
    (MnEnq.acall_raw_em_x B AOX) DRNm (xr_raw_em B AOX) z msE matE E5 W5 regs' mem' md' X' nb ER)].
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
  { refine (memnorm_dmem_m W ly _ mem tr _ _ hb1 _ j1 j2 j3 regs (bv_unsigned (getr regs 2)) (ms_mem msE) FH _ DMfr).
    rewrite RG2. reflexivity. }
  assert (M3 : MemnormT.memnorm_keep tfibsegs mem' memC).
  { apply (mn_keep_stack ly (bv_unsigned (getr regs 2) - 80) (bv_unsigned (getr regs 2)) mem' memC LY);
      [unfold DFSTACK_G, spZ in *; lia | unfold spZ in *; lia | exact FR1]. }
  assert (M5 : MemnormT.memnorm_keep tfibsegs mem6 memR).
  { apply (mn_keep_stack ly (bv_unsigned (getr regs 2) - 80) (bv_unsigned (getr regs 2)) mem6 memR LY);
      [unfold DFSTACK_G, spZ in *; lia | unfold spZ in *; lia | exact FRT]. }
  exact (MemnormLocG.memnorm_keep_trans _ _ _ _ M1 (MemnormLocG.memnorm_keep_trans _ _ _ _ XEm
    (MemnormLocG.memnorm_keep_trans _ _ _ _ M3 (MemnormLocG.memnorm_keep_trans _ _ _ _ XDm M5)))). }
eapply amreal_mono; [| exact (amreal_apath_gflag tfibsegs _ _ _ _ MAIN)].
intros r W' c' [(ly' & regs' & mem' & md' & Hc & Hpost & Hraw & He & Hm & Hlp) HPATH].
exists ly', regs', mem', md'. split; [exact Hc|].
split.
{ destruct Hpost as (H1 & H2 & H3 & H4 & H5 & H6 & H7).
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj (Hraw eq_refl) H7))))))). }
split; [exact He|]. split; [exact Hm|]. split; [exact Hlp | exact HPATH].
Qed.
End e.
End d.
