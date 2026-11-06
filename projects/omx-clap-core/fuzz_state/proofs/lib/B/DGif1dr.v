(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DGif1dr.v (a working branch ced28ed2383, file sha256 5bbf29a1aa83) onto omx-clap-core/fuzz_state's asan-ubsan image (fuzz_state.asan-ubsan, pinned sha256 5ac5ce0954f8; addresses read from its unstripped build b1566a1ca816); module paths changed; its 2 image addresses moved by code-verified function pairs (2 port_addr_check 16f8a030c869 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 2 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: moved from ced28ed2383 to a Theorem Labs lane's c5 install head a working branch 57e82b93d43 (cgif file sha256 b5ecd9b8a963; the errno-kept twins of ad994c27165, additive). By 3-way merge (base = agreloc of ced28ed2383, theirs = agreloc of 57e82b93d43 with port_addr_check 16f8a030c869 PREDICT rows for it, ours = this file's image-B rows and L edits). *)
(* Modified by Theorem Labs, 2026-10: cgif_file's instance of DGif0.DIface's di_rchunk and di_cdealloc (DMiface.v types),
   restated from the released QuarantineCallback::Recycle and LocalCache::Deallocate walks (YFfs, YFg7, YFg8, YFg9, YFg0)
   at DMspec.acall_post_x's raw frame clause and the stack window DMiface.KSTACK_CF. *)
(* cgif_file's instance of the recycle-side fields of the generic Deallocate interface (DGif0.DIface), at the agreed
   instantiation ARXr := AllocGcgif.ARX_cgif B, AOX := aowned B, DRq := DRq_cgif B (below).

   - [dgif1_rchunk_cgif]: QuarantineCallback::Recycle (0x341bc), the released YFeu.tfib_rchunk_spec (YFeu.v:280), proved
     by YFfs.tfib_rchunk_of_arms (YFfs.v:27): the primary arm YFg7.tfib_rchunk_prim_arm (which tail-calls CacheDealloc)
     and the secondary arm YFg9.tfib_rchunk_sec (YFg8.plumbing over YFg9.WALK);
   - [dgif1_cdealloc_cgif]: SizeClassAllocator64LocalCache::Deallocate (0x345c0), the released YFeu.tfib_cdealloc_spec
     (YFeu.v:257), proved by YFg0.tfib_cdealloc_arm;
   - [dgif1_rchunk_walk] / [dgif1_cdealloc_walk]: the same two posts with the walk's raw frame (below) kept beside
     acall_raw_x, which those two drop (DGif1dIE reads errno from it).

   What is restated, and from where:
   - the raw frame clause.  The released leaves (YFeu.rcc_leaf / cd_leaf over YG0d.acall_post) frame the view only.
     Each arm is re-run here from the same released pieces: the segment lemmas, whose posts carry the raw frame of the
     walk ([YFgk.MEQ] at CacheDealloc's return, [YFgs.MEQ] at RChunk's tail call, [YFg8.LINKD] and [YFgv.MEQP] around
     the munmap), and the released leaf lemmas (YFg0.FINKH, YFg7.CDPRE, YFg8.FIN) for everything else.  The walk's
     window is owned or in the call's stack scratch by the released [YFez.D_owned] / [YFf3.D_owned] / [YFf4.D_owned];
     [cd_leafR] / [rcc_leafR] below are the released leaves with that raw frame added.  No new walk;
   - the stack window.  The released walks use at most 320 bytes below the entry sp (YFgk.WIN: 320, YFgs.WIN: 256,
     YFgv.GDEPTH: 96; CacheDealloc is a tail call at the same sp), inside YFeu.KSTACK = 512, which KSTACK_CF = 2048
     contains.  The 1264 bytes DMiface.v:113-116 counts are the free-array growth arm's (FGt.tfib_efa_spec,
     FGt.v:85-88).  At cgif that arm is not reached: DRq_cgif's free-array room (YG03.RIx's fa_room, with a batch object
     still to free) is cd_pre's room conjunct, from which the released walk's segment facts show that the drained half
     fits the mapped free array (YFfi.FH_ok, YFfi.v:462, by YG0l.return_room), so EnsureFreeArraySpace does not map;
   - the model.  The recycle invariant after each call: YFhh.RIx_rc_step for Recycle, [RIx_cd_step_its] below (YFhh.
     RIx_cd_step with chunks of later batches still pending) for CacheDealloc. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j YP0n YK0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o YG0j YG0k YG08 YG0g.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1w YFeq YFew YFeu.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YFfj YFfk YFfn YFhh.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YFg0 YFez YFfi YFgk YFgy YFgz YFg7 YFf3 YFfr YFgs YFh7.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YFg8 YFg9 YFf4 YFgv.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import AGif2cgif DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DIfaceR.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import AllocGcgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DMspec DMiface.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.

(* The cgif recycle invariant: [DRq_cgif B S its zs] with the chunks [its] and the batch objects [zs] (their offsets in
   the space) still to recycle (DGif0.v:253-255, DMiface.v:21-22).  Same body as DGif1d.DRq_cgif. *)
Definition DRq_cgif (B : asyms) (S : astate) (its : list chunk) (zs : list Z) : Prop :=
RIx (as_universe B) 0 0 0 S its [] zs.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Model: YFhh.RIx_cd_pre / RIx_cd_step with chunks still pending ([its]).                                          *)
Lemma RIx_cd_pre_its : forall U pp cc bb s its P z selfs,
RIx U pp cc bb s its P (z :: selfs) ->
WfP U pp cc bb s /\ 0 <= z - region_off kBatchClass < rg_alloc_user (reg s kBatchClass) /\
(z - region_off kBatchClass) mod class_size kBatchClass = 0 /\ ~ In (z - region_off kBatchClass) (class_elems s kBatchClass) /\
4 * (Z.of_nat (length (class_elems s kBatchClass)) + 1 + (cc + bb + 2 * (EV_MAX - st_nev s))) <= rg_mapped_fa (reg s kBatchClass).
Proof.
intros U pp cc bb s its P z selfs (W & IT & ND & BL & SF & NDS & RM). cbn [app] in SF, RM.
inversion SF as [|z0 l0 (Z1 & Z2 & Z3) SFP]; subst.
split; [exact W|]. split; [exact Z1|]. split; [exact Z2|]. split; [exact Z3|].
destruct RM as [Z0|R]; [lia|]. cbn [length] in R. lia.
Qed.

Lemma RIx_cd_step_its : forall U pp cc bb s its P z selfs ns s2,
RIx U pp cc bb s its P (z :: selfs) -> cache_dealloc_post U pp cc bb s kBatchClass (z - region_off kBatchClass) ns (tt, s2) ->
RIx U pp cc bb s2 its P selfs.
Proof.
intros U pp cc bb s its P z selfs ns s2 RX CP.
destruct RX as (W1 & IT1 & ND1 & BL1 & SF1 & NDS1 & RM1). cbn [app] in SF1, NDS1, RM1.
inversion SF1 as [|z0 l0 (Z1 & Z2 & Z3) SFP]; subst. inversion NDS1 as [|z1 l1 Hnself NDSP]; subst.
destruct CP as (W2 & RO2 & AU2 & CE2 & MF2 & LEN2). cbn [snd] in W2, RO2, AU2, CE2, MF2, LEN2.
destruct RO2 as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10).
unfold RIx. split; [exact W2|]. split; [rewrite R1; exact IT1|]. split.
{ replace (q_items s2) with (q_items s) by (unfold q_items, all_batches; rewrite R5, R6; reflexivity). exact ND1. }
split; [exact BL1|]. split.
{ apply Forall_forall. intros y Hy. pose proof (proj1 (Forall_forall _ _) SFP y Hy) as (Y1 & Y2 & Y3).
rewrite AU2 by (unfold kBatchClass; lia). split; [exact Y1 | split; [exact Y2|]].
intros Hin. destruct (CE2 kBatchClass _ ltac:(unfold kBatchClass; lia) Hin) as [[Ez _]|Hin'].
- apply Hnself. replace z with y by lia. exact Hy.
- exact (Y3 Hin'). }
split; [exact NDSP|].
rewrite AU2, (LEN2 kBatchClass), R10 by (unfold kBatchClass; lia). rewrite Z.eqb_refl.
eapply fa_room_xfer; [exact RM1 | cbn [length]; lia | apply MF2; unfold kBatchClass; lia].
Qed.

(* The config's memory, read off a config equation. *)
Lemma cfg_mem_eqR : forall (c1 c2 : config), c1 = c2 -> ms_mem (cfg_ms c1) = ms_mem (cfg_ms c2).
Proof. intros c1 c2 E. rewrite E. reflexivity. Qed.

Section b.
Variable B : asyms.
Hypothesis TB : TfibSyms B.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The released leaves with the walk's raw frame.                                                                   *)
Definition cd_leafR (ly : alayout) (X : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (r : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
cd_leaf B ly X W regs mem md r W' c' /\
(exists regs' mem' md', c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
 forall x : word, ~ aowned B ly X (bv_unsigned x) -> ~ aowned B ly (snd r) (bv_unsigned x) ->
 ~ (spZ regs - KSTACK <= bv_unsigned x < spZ regs) -> mem' x = mem x).
Definition rcc_leafR (ly : alayout) (X : astate) (k : chunk) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (r : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
rcc_leaf B ly X k W regs mem md r W' c' /\
(exists regs' mem' md', c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
 forall x : word, ~ aowned B ly X (bv_unsigned x) -> ~ aowned B ly (snd r) (bv_unsigned x) ->
 ~ (spZ regs - KSTACK <= bv_unsigned x < spZ regs) -> mem' x = mem x).

(* ---------------------------------------------------------------------------------------------------------------- *)
(* CacheDealloc: YFg0.tfib_cdealloc_arm (YFg0.v:285-297), the leaf with YFgk.MEQ's raw frame.                         *)
Theorem cdealloc_okR : forall ly X c off W regs mem md, cd_pre B ly X c off W regs mem md -> ly_tsd ly = TFIB_TSD ->
amreal tfibsegs (cache_dealloc c off X) W (cfg_at tfibsegs A_CDealloc regs mem md) (cd_leafR ly X W regs mem md).
Proof.
intros ly X c off W regs mem md PRE HTSD.
pose proof (YFg0.PREF B ly X c off W regs mem md PRE) as (Hci & Hcc & Hx & Hxm & Hxni & HROOM).
pose proof (YFfi.M B ly X c off W regs mem md PRE) as M0.
pose proof (YFfi.HSP B ly X c off W regs mem md PRE) as HSP0.
pose proof (YFfi.IMG B ly X c off W regs mem md PRE) as IMG0.
rewrite (YFez.cache_dealloc_S' B ly X _ M0 c off Hci Hcc Hx Hxm HROOM). cbn [amreal].
destruct (YFfi.junk_vals B ly X c off W regs mem md PRE) as (j80 & j88 & jst & HJ80 & HJ88 & HJST).
pose proof (YFfi.FH_ok B TB ly X c off W regs mem md PRE j80 j88 jst HJ80 HJ88 HJST) as FH.
pose proof (YFfi.reg_facts B ly X c off W regs mem md PRE) as RFx.
unfold cfg_at, A_CDealloc. rewrite <- (YFg0.wvb_self md) at 1.
eapply SRr_mono; [| intros W' c' _ HR; split; [exact (YFg0.FINKH B TB ly X c off W regs mem md PRE HTSD W' c' HR) |]].
2:{ destruct HR as (-> & regs' & mem' & mat & -> & CSP & CS & MEQ' & PRESW & VALS).
    exists regs', mem', (with_vm_backing (m_vm_lazy md) mat md). split.
    { unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
    intros x NO NO' NS. apply MEQ'. intros Hw.
    destruct (YFez.D_owned B ly X _ M0 c off Hci Hcc Hx Hxm HROOM _ HSP0 IMG0 _ (proj1 (u64_range x))
      (YFg0.WIN_D ly X c regs _ Hw)) as [O|O]; [exact (NO O) | apply NS; unfold YFez.DS, spZ in *; exact O]. }
destruct (Z_lt_le_dec (YFfi.kcnt X c) (YFgk.MAXv c)) as [LT|GE].
- exact (YFgy.segK1 W ly regs mem md c off (YFfi.kcnt X c) (YFfi.kold X c) (YFfi.kmf X c) j80 j88 jst (m_vm_materialized md) FH LT).
- apply (YFgz.segK2 W ly regs mem md c off (YFfi.kcnt X c) (YFfi.kold X c) (YFfi.kmf X c) j80 j88 jst (m_vm_materialized md) FH).
  clear - RFx GE. unfold YFgk.MAXv in *. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Recycle, primary chunk: YFg7.tfib_rchunk_prim_arm (YFg7.v:291-316), the tail call's raw frame from YFgs.MEQ and    *)
(* CacheDealloc's from [cdealloc_okR].                                                                              *)
Theorem rchunk_primR : forall ly X k cbp W regs mem md off,
rcc_pre B ly X k cbp W regs mem md -> ck_beg k = PPrim off -> ly_tsd ly = TFIB_TSD ->
amreal tfibsegs (recycle_chunk k X) W (cfg_at tfibsegs A_RChunk regs mem md) (rcc_leafR ly X k W regs mem md).
Proof.
intros ly X k cbp W regs mem md off PRE Hb HTSD.
pose proof PRE as (_ & Hci & Hk & Hst & Hni & _).
pose proof (YFfr.M B ly X k cbp W regs mem md PRE) as M0.
pose proof (YFfr.HSP B ly X k cbp W regs mem md PRE) as HSP0.
rewrite (YFg7.recycle_chunk_prim k X off (proj2 (mem_chunk_spec _ _) Hk) Hb).
unfold cfg_at, A_RChunk. rewrite <- (YFg0.wvb_self md) at 1.
eapply (amreal_SRr_pre tfibsegs _ _ _ _ (YFgs.at_CD W ly regs mem md (YFfr.rcl off) (YFfr.rbase B ly k) (YFfr.rrz k) (YFfr.rnn k) (YFfr.hb1 B ly k W mem))).
{ exact (YFh7.segRC W ly regs mem md (YFfr.rcl off) (YFfr.rbase B ly k) (YFfr.rrz k) (YFfr.rnn k) (YFfr.hb1 B ly k W mem) cbp
    (YFfr.rmuc X off) (YFfr.j1 ly W mem) (YFfr.j2 ly W mem) (m_vm_materialized md) (YFfr.FH_ok B TB ly X k cbp W regs mem md off PRE Hb HTSD)). }
intros W' c' _ HCD. pose proof HCD as HCD'.
destruct (YFg7.CDPRE B TB ly X k cbp W regs mem md off PRE Hb HTSD W' c' HCD) as (regs' & mem' & mat & -> & -> & PRE' & R2 & R1 & RS & FR & PUF).
destruct HCD' as (_ & regs2 & mem2 & mat2 & Hc2 & _ & _ & _ & _ & _ & _ & _ & MEQ' & _).
assert (Em : mem2 = mem') by (pose proof (cfg_mem_eqR _ _ Hc2) as E; cbn in E; symmetry; exact E).
subst mem2.
eapply amreal_mono; [| exact (cdealloc_okR ly (YFf3.X1 X k) (YFfr.rcl off) off W regs' mem' _ PRE' HTSD)].
cbv beta. intros [[] S''] W'' c'' [HL (regs3 & mem3 & md3 & Hc3 & RAW3)]. split.
- destruct HL as (regs'' & mem'' & md'' & Hc'' & AP & UF & CI). exists regs'', mem'', md''.
  split; [rewrite Hc''; unfold cfg_at, raZ; rewrite R1; reflexivity|].
  split.
  2:{ split; [|exact CI]. intros a Ha PU NK. rewrite (UF a Ha) by exact PU. exact (PUF a Ha PU NK). }
  destruct AP as (AR'' & LLE & WLE & RP & IO & FRM & PRS). unfold acall_post. unfold spZ in *. rewrite R2 in PRS.
  split; [exact AR''|]. split; [exact LLE|]. split; [exact WLE|]. split.
  { intros rr Hr. rewrite (RP rr Hr). unfold acallee_saved in Hr.
    assert (R : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
    destruct R as [->|R]; [exact R2|]. apply RS. clear - R. unfold YFgs.SREGS.
    repeat match goal with R : _ \/ _ |- _ => destruct R as [R|R] end; subst rr; cbn [In]; repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]). }
  split. { pose proof (YFg0.same_io_wvb md mat) as IO1. clear - IO IO1. unfold same_io in *. destruct IO as (I1 & I2 & I3 & I4). destruct IO1 as (J1 & J2 & J3 & J4). repeat split; congruence. }
  split.
  { intros a Ha NO NO' NS NE. rewrite (FRM a Ha); [apply FR; [exact Ha | exact NO | exact NS] | | exact NO' | unfold ascratch, spZ in *; rewrite R2; exact NS | exact NE].
    intros O1. apply NO. exact (proj1 (YFf3.aowned_X1 B ly X _ M0 k off Hk Hst Hb _ HSP0 a) O1). }
  exact PRS.
- exists regs3, mem3, md3. split; [rewrite Hc3; unfold cfg_at, raZ; rewrite R1; reflexivity|].
  intros x NO NO' NS.
  assert (NO1 : ~ aowned B ly (YFf3.X1 X k) (bv_unsigned x)) by (intros O; apply NO; exact (proj1 (YFf3.aowned_X1 B ly X _ M0 k off Hk Hst Hb _ HSP0 _) O)).
  rewrite (RAW3 x NO1 NO' ltac:(unfold spZ in *; rewrite R2; exact NS)).
  apply MEQ'. intros Hw.
  destruct (YFf3.D_owned B ly X _ M0 k off Hk Hst Hb _ HSP0 _ (proj1 (u64_range x)) (YFg7.WIN_D B ly X k cbp W regs mem md off PRE Hb _ Hw)) as [O|O];
    [exact (NO O) | apply NS; unfold YFf3.DS, spZ in *; exact O].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Recycle, secondary chunk: YFg8.plumbing (YFg8.v:334-368) over YFg9.WALK, the leaf with the raw frame of           *)
(* YFg8.LINKD (to the munmap) and YFgv.MEQP (after it); their windows are inside YFf4.D (YFg8.FIN's [WD],           *)
(* YFg8.v:287-303).                                                                                                 *)
Lemma WD_sec : forall ly X k cbp (W : world tfibsegs) regs mem md r o sm i (regsD : bvmap 5 word),
rcc_pre B ly X k cbp W regs mem md -> ck_beg k = PSec r o -> nth_error (st_secs X) r = Some sm -> nth_error (st_sec_arr X) i = Some r ->
getr regsD 2 = getr regs 2 ->
forall a, 0 <= a < 2 ^ 64 ->
(YFg8.WPRE ly regs a \/ YFgv.WIN3 ly regsD (YFg8.MAP ly r) (YFg8.LEN sm) (YFg8.qi ly i) (YFg8.lst ly X r) a) ->
YFf4.D B ly X k r i (bv_unsigned (getr regs 2)) a.
Proof.
intros ly X k cbp W regs mem md r o sm i regsD PRE Hb Hsm Hi LSP a Ha HW.
pose proof (YFg8.KFACTS B ly X k cbp W regs mem md r o sm PRE Hb Hsm) as (_ & _ & ELEN & _ & _ & _).
pose proof (YFg8.LEN_facts B ly X k cbp W regs mem md r o sm PRE Hb Hsm) as [L1 L2].
assert (EI : A_ALLOCATOR = as_inst B) by (rewrite (ts_inst _ TB); reflexivity).
assert (SPD : bv_unsigned (getr regsD 2) = bv_unsigned (getr regs 2)) by (rewrite LSP; reflexivity).
pose proof (YFf4.ARR B ly X _ (proj1 (proj1 PRE)) r i Hi) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
assert (ELEN' : sec_map_size (ck_req k) = YFg8.LEN sm) by (symmetry; exact ELEN).
unfold YFf4.D, YFf4.DS, YFf4.DI, YFf4.DJ, YFf4.DQ, YFf4.DL, YFf4.DH, YFf4.DM.
unfold YFf4.own, YFf4.qi, YFf4.lst, YFf4.MAP, YFf4.LEN, YFf4.idx, YFf4.nA, YFf4.lastr, YFf4.arr.
rewrite ELEN'. rewrite <- EI. unfold shadow_addr.
unfold YFg8.WPRE, YFgv.WIN3, YFgv.WIN2, YFgv.WIN, YFgv.WINS, YFgv.WINM, YFgv.SHAv, YFgv.CNTv, YFgv.GDEPTH in HW. cbv zeta in HW. rewrite SPD in HW.
unfold YFg8.qi, YFg8.lst, YFg8.idx, YFg8.MAP in HW.
destruct (Z.eqb_spec (Z.of_nat i) (Z.of_nat (length (st_sec_arr X)) - 1)) as [EO|NEO].
- assert (LR : last (st_sec_arr X) r = r) by (apply A8; unfold YFf4.own, YFf4.idx, YFf4.nA, YFf4.arr; apply Z.eqb_eq; exact EO).
  rewrite LR in HW. unfold KSTACK.
  lazymatch goal with |- ?A \/ ?Bq \/ ?C \/ ?Dq \/ (_ /\ _) \/ ?G =>
  enough (G' : A \/ Bq \/ C \/ Dq \/ G) by (destruct G' as [?|[?|[?|[?|?]]]]; [left | right; left | do 2 right; left | do 3 right; left | do 5 right]; assumption) end.
  clear - HW L1 Ha. lia.
- unfold KSTACK.
  lazymatch goal with |- ?A \/ ?Bq \/ ?C \/ ?Dq \/ (_ /\ ?F) \/ ?G =>
  enough (G' : A \/ Bq \/ C \/ Dq \/ F \/ G) by (destruct G' as [?|[?|[?|[?|[?|?]]]]]; [left | right; left | do 2 right; left | do 3 right; left | do 4 right; left; split; [reflexivity | assumption] | do 5 right]; assumption) end.
  clear - HW L1 Ha. lia.
Qed.

Theorem plumbingR : forall ly X k cbp (W : world tfibsegs) regs mem md r o sm i,
rcc_pre B ly X k cbp W regs mem md -> ck_beg k = PSec r o -> nth_error (st_secs X) r = Some sm ->
nth_error (st_sec_arr X) i = Some r -> index_of (st_sec_arr X) r 0%nat = Some i -> needs_remap (sm_len sm) = false ->
ly_tsd ly = TFIB_TSD ->
amreal tfibsegs (recycle_chunk k X) W (cfg_at tfibsegs A_RChunk regs mem md) (rcc_leafR ly X k W regs mem md).
Proof.
intros ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi Hidx SMALL HTSD.
pose proof (YFg9.WALK B TB ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi SMALL HTSD) as WALK.
pose proof (YFg8.MAP_facts B ly X k cbp W regs mem md r o sm PRE Hb Hsm) as (P1 & P2 & P3 & INA & INV & MW).
pose proof (YFg8.LEN_facts B ly X k cbp W regs mem md r o sm PRE Hb Hsm) as [L1 L2].
pose proof PRE as (_ & _ & Hk & Hst & _).
rewrite (YFg8.recycle_chunk_sec k X r o sm i (proj2 (mem_chunk_spec _ _) Hk) Hb Hsm Hidx SMALL). cbn [amreal].
eapply SRr_bind; [exact WALK|]. intros W1 c1 _ (regsD & memD & LNK & HM).
destruct HM as (-> & regs1 & mem1 & mat1 & -> & H17 & H10 & H11 & INNER). cbv zeta in INNER.
apply SRr_use_AI. cbn [cfg_model]. intros HAI. apply SRr_ret.
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md) in *.
set (c2 := mkCfg (mkst (regupd regs1 10 (w64 0)) (w64 0x64c78) (unfill (w64 (YFg8.MAP ly r)) (w64 (YFg8.LEN sm)) mem1) (seg_rom tfibsegs))
  (munmap_model (w64 (YFg8.MAP ly r)) (w64 (YFg8.LEN sm)) md1)).
assert (UM : bv_unsigned (w64 (YFg8.MAP ly r)) = YFg8.MAP ly r) by (unfold w64; apply unsigned_lit_small; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia).
assert (UL : bv_unsigned (w64 (YFg8.LEN sm)) = YFg8.LEN sm) by (unfold w64; apply unsigned_lit_small; lia).
assert (MW1 : amwf md1) by (apply (amwf_same md md1); [subst md1; apply m_vmmaps_wvb | subst md1; apply m_vm_lazy_wvb | exact MW]).
assert (INV1 : In (w64 (YFg8.MAP ly r), w64 (YFg8.LEN sm)) (vm_maps (m_vmmaps md1))) by (subst md1; rewrite m_vmmaps_wvb; exact INV).
destruct (in_split _ _ INV1) as (l1 & l2 & EVM).
exists unit, (fun _ => c2), (fun _ => 1), (fun _ => false), tt.
split.
{ pose proof (munmap_node tfibsegs regs1 (w64 0x64c74) mem1 (seg_rom tfibsegs) md1 (w64 (YFg8.MAP ly r)) (YFg8.LEN sm) (AI_halted _ _ _ _ HAI) H17 H10
    ltac:(rewrite UM; unfold page_size; exact P3) H11 ltac:(lia)
    ltac:(rewrite UM, (YFg8.page_round_up_Z_aligned (YFg8.LEN sm)) by lia; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, two_pow_64, TASK_SIZE, kHighMemBeg, ASAN_CEIL in *; lia)
    ltac:(rewrite (YFg8.page_round_up_Z_aligned (YFg8.LEN sm)) by lia; exact (map_has_In _ _ _ INV1))) as ND.
  cbv zeta in ND. rewrite (YFg8.page_round_up_Z_aligned (YFg8.LEN sm)) in ND by lia. exact ND. }
split. { intros [] _. cbn [cfg_model]. exact (munmap_AI tfibsegs (w_H W) (w_A W) md1 (w64 (YFg8.MAP ly r), w64 (YFg8.LEN sm)) l1 l2 HAI MW1 EVM
    ltac:(cbn [fst]; rewrite UM; unfold page_size; exact P3)
    ltac:(cbn [fst snd]; rewrite UM, UL; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia)). }
split. { intros []. cbn [aok]. reflexivity. }
split; [reflexivity|]. split; [reflexivity|]. split; [intros [] _; reflexivity|]. split; [intros [] XX; discriminate XX|].
intros [] _. cbn [amreal].
eapply SRr_bind; [exact INNER|]. intros W3 c3 _ HR. pose proof HR as (-> & regs' & mem' & mat' & Ec3 & _).
apply SRr_use_AI. intros HAI3. rewrite Ec3 in HAI3 |- *. cbn [cfg_model] in HAI3.
apply (SRr_world_le tfibsegs W (YFg8.W2 ly W r sm)).
{ apply wrefund_wle. }
{ intros _. cbn [cfg_model]. apply AI_refund_gen; [exact HAI3|]. intros p Hp. rewrite m_vm_lazy_wvb in Hp. unfold YFg8.iv. cbn [fst snd].
  pose proof (munmap_lazy_out (w64 (YFg8.MAP ly r)) (w64 (YFg8.LEN sm)) md1 p ltac:(destruct MW1 as [(_ & _ & W3l & _) _]; intros q Hq; exact (W3l q Hq))
    ltac:(rewrite UM, UL; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia) Hp) as NL. rewrite UM, UL in NL. exact NL. }
apply SRr_ret. rewrite <- Ec3. split.
- exact (YFg8.FIN B TB ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi HTSD regsD memD mat1 W c3 LNK HR).
- destruct HR as (_ & regs4 & mem4 & mat4 & Ec4 & _ & _ & _ & _ & _ & MEQ' & _).
  exists regs4, mem4. eexists. split; [rewrite Ec4; unfold cfg_at; reflexivity|].
  intros x NO NO' NS.
  assert (HSP0 : ly_stk_lo ly + KSTACK <= bv_unsigned (getr regs 2) <= ly_stk_hi ly).
  { destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & Hlo & Hcb1 & Hcb2 & _). unfold spZ in *. lia. }
  assert (IMG0 : img_cover ly) by (exact (img_cover_of_ledger ly X md (proj1 (proj2 (proj1 PRE))))).
  assert (ND : ~ YFf4.D B ly X k r i (bv_unsigned (getr regs 2)) (bv_unsigned x)).
  { intros HD. destruct (YFf4.D_owned B TB ly X _ (proj1 (proj1 PRE)) k r o sm i Hk Hst Hb Hsm Hi _ HSP0 IMG0 _ (proj1 (u64_range x)) HD) as [O|O];
      [exact (NO O) | apply NS; unfold YFf4.DS, spZ in *; exact O]. }
  destruct LNK as (LSP & _ & LMEM & _).
  rewrite (MEQ' x) by (intros HW; apply ND; apply (WD_sec ly X k cbp W regs mem md r o sm i regsD PRE Hb Hsm Hi LSP _ (u64_range x)); right; exact HW).
  apply LMEM. intros HW. apply ND. apply (WD_sec ly X k cbp W regs mem md r o sm i regsD PRE Hb Hsm Hi LSP _ (u64_range x)). left. exact HW.
Qed.

(* YFg9.tfib_rchunk_sec + tfib_rchunk_sec_small (YFg9.v:94-120) over [plumbingR]. *)
Theorem rchunk_secR : forall ly X k cbp W regs mem md r o,
rcc_pre B ly X k cbp W regs mem md -> ck_beg k = PSec r o -> ly_tsd ly = TFIB_TSD ->
amreal tfibsegs (recycle_chunk k X) W (cfg_at tfibsegs A_RChunk regs mem md) (rcc_leafR ly X k W regs mem md).
Proof.
intros ly X k cbp W regs mem md r o PRE Hb HTSD. pose proof PRE as ((M & _) & _ & Hk & _).
pose proof (am_wf B ly X _ M) as WF.
assert (SMALL : needs_remap (sec_map_size (ck_req k)) = false).
{ apply needs_remap_false.
  pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ WF) k Hk) as [CKr _].
  pose proof (YG08.sec_map_size_bound (ck_req k) (proj1 CKr)) as SB. unfold req_size, MALLOC_MAX in *.
  destruct (ck_req k =? 0); lia. }
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ WF) k Hk) as [_ CK]. rewrite Hb in CK. destruct CK as (_ & _ & sm & Hsm & Hlive & Hsz & Hlen).
destruct (wf_secondary _ _ _ _ _ WF) as [_ Sac _ _ _].
assert (Hr : In r (st_sec_arr X)).
{ apply (proj2 (Sac r)). exists k. split; [exact Hk|]. rewrite Hb.
  pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ WF) k Hk) as [_ CK']. rewrite Hb in CK'. destruct CK' as (_ & -> & _). reflexivity. }
destruct (index_of_spec (st_sec_arr X) r 0%nat Hr) as (i & Hidx & Hi). rewrite Nat.add_0_l in Hidx.
assert (SM : needs_remap (sm_len sm) = false) by (rewrite Hlen; exact SMALL).
exact (plumbingR ly X k cbp W regs mem md r o sm i PRE Hb Hsm Hi Hidx SM HTSD).
Qed.

(* YFfs.tfib_rchunk_of_arms (YFfs.v:27-35) over the two arms. *)
Theorem rchunkR : forall ly X k cbp W regs mem md, rcc_pre B ly X k cbp W regs mem md ->
amreal tfibsegs (recycle_chunk k X) W (cfg_at tfibsegs A_RChunk regs mem md) (rcc_leafR ly X k W regs mem md).
Proof.
intros ly X k cbp W regs mem md PRE. pose proof PRE as ((M & _) & _ & Hk & _).
assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite (am_tsd B ly X _ M); apply (ts_tsd _ TB)).
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ (am_wf B ly X _ M)) k Hk) as [_ CK].
destruct (ck_beg k) as [|off|r o|c q] eqn:Eb; try solve [destruct CK].
- exact (rchunk_primR ly X k cbp W regs mem md off PRE Eb HTSD).
- exact (rchunk_secR ly X k cbp W regs mem md r o PRE Eb HTSD).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The KSTACK_CF window's presence after the call: below the released 512 bytes the walk wrote nothing (the raw       *)
(* frame; the stack is not owned, YG0s.AR_stack_law_ok), and the world only grows ([wle]).                          *)
Lemma stk_lo_nonneg : forall ly S (W : world tfibsegs) mem md, AR tfibsegs B ly S W mem md -> 0 <= ly_stk_lo ly.
Proof.
intros ly S W mem md HAR.
pose proof (YFf4.HIGH B TB ly S _ (proj1 HAR) (img_cover_of_ledger ly S md (proj1 (proj2 HAR)))) as HI.
destruct HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H15 & _).
unfold YG0f.kHighMemBeg in H15. lia.
Qed.

Lemma pres_lift : forall ly S S' (W W' : world tfibsegs) mem mem' md md' sp,
AR tfibsegs B ly S W mem md -> AR tfibsegs B ly S' W' mem' md' -> wle W W' ->
(forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ aowned B ly S' (bv_unsigned x) -> ~ (sp - KSTACK <= bv_unsigned x < sp) -> mem' x = mem x) ->
ly_stk_lo ly + KSTACK_CF <= sp -> sp <= ly_stk_hi ly -> sp < 2 ^ 64 ->
(forall a, sp - KSTACK_CF <= a < sp -> apresent (w_H W) mem a) ->
(forall a, sp - KSTACK <= a < sp -> apresent (w_H W') mem' a) ->
forall a, sp - KSTACK_CF <= a < sp -> apresent (w_H W') mem' a.
Proof.
intros ly S S' W W' mem mem' md md' sp HAR HAR' WLE RAW Hlo Hhi Hsp P0 P1 a Ha.
destruct (Z_lt_le_dec a (sp - KSTACK)) as [Hl|Hh]; [|apply P1; lia].
pose proof (stk_lo_nonneg ly S W mem md HAR) as L0.
assert (Ua : 0 <= a < 2 ^ 64) by (unfold KSTACK_CF in *; lia).
destruct (P0 a Ha) as [Hn [b Hb]].
assert (E : mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
{ apply RAW; rewrite unsigned_lit_small by exact Ua.
  - apply (AR_stack_law_ok tfibsegs B ly S W mem md a HAR). unfold KSTACK, KSTACK_CF in *. lia.
  - apply (AR_stack_law_ok tfibsegs B ly S' W' mem' md' a HAR'). unfold KSTACK, KSTACK_CF in *. lia.
  - lia. }
split; [|exists b; rewrite E; exact Hb].
destruct (w_H W' (Z_to_bv 64 a)) eqn:E'; [|reflexivity]. rewrite (WLE _ E') in Hn. discriminate.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* di_rchunk.                                                                                                       *)
(* The Recycle post with rcc_leafR's raw frame kept beside acall_raw_x: the walk changes no byte outside the owned
   bytes before and after and the released KSTACK window.  dgif1_rchunk_cgif drops it; DGif1dIE reads errno from it. *)
Lemma dgif1_rchunk_walk : forall inst ly X k ks zs cbp W regs mem md,
rcc_pre_x B (ARX_cgif B) inst ly X k cbp W regs mem md -> DRq_cgif B X (k :: ks) zs ->
amreal tfibsegs (recycle_chunk k X) W (cfg_at tfibsegs A_RChunk regs mem md)
(fun r W' c' => exists regs' mem' md',
  c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
  acall_post_x B (ARX_cgif B) (aowned B) inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  acall_raw_x B (aowned B) inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  (forall x : word, ~ aowned B ly X (bv_unsigned x) -> ~ aowned B ly (snd r) (bv_unsigned x) ->
   ~ (spZ regs - KSTACK <= bv_unsigned x < spZ regs) -> mem' x = mem x) /\
  (forall a, 0 <= a < 2 ^ 64 -> YFeuC.puser ly X a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) ->
   aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) /\
  (forall a, YFeuC.puser ly X a -> YFeuC.puser ly (snd r) a) /\
  DRq_cgif B (snd r) ks zs /\ st_cache_inited (snd r) = true /\ (forall a, aowned B ly (snd r) a -> aowned B ly X a)).
Proof.
intros inst ly X k ks zs cbp W regs mem md PREX RX.
destruct PREX as ([Hinst HAR] & Hci & Hra & Hra4 & Hal & Hlo & Hcb1 & Hcb2 & Hcb3 & HPRES & HPRC & HVC & Hgp & Htp & Ha0 & Ha1).
pose proof (RIx_head _ _ _ _ _ _ _ _ _ RX) as (WF & Hk & Hst & Hni).
assert (PRE : rcc_pre B ly X k cbp W regs mem md).
{ refine (conj HAR (conj Hci (conj Hk (conj Hst (conj Hni (conj Hra (conj Hra4 (conj Hal (conj _ (conj Hcb1 (conj Hcb2 (conj Hcb3
    (conj _ (conj HPRC (conj HVC (conj Hgp (conj Htp (conj Ha0 Ha1)))))))))))))))))).
  - unfold KSTACK, KSTACK_CF in *. lia.
  - intros a Ha. apply HPRES. unfold KSTACK, KSTACK_CF in *. lia. }
pose proof (rchunkR ly X k cbp W regs mem md PRE) as RR.
assert (APOST : apost (recycle_chunk k X) (fun r => exists ns, recycle_postx (as_universe B) 0 0 0 X k ns r)).
{ intros tr r0 Hp. exact (atok_apath _ true _ tr r0 (recycle_chunk_okx (as_universe B) 0 0 0 X k true WF Hk Hst Hni) Hp). }
pose proof (amreal_apost tfibsegs _ _ W _ _ APOST RR) as RR2.
eapply amreal_mono; [|exact RR2]. cbv beta.
intros [[] S'] W' c' [(ns & RPX & _) [LEAF (regs2 & mem2 & md2 & Hc2 & RAW)]]. cbn [snd] in RAW |- *.
destruct LEAF as (regs' & mem' & md' & Hc & POST & PUF & CI).
assert (Em : mem2 = mem') by (pose proof (cfg_mem_eqR _ _ (eq_trans (eq_sym Hc2) Hc)) as E; cbn in E; exact E).
subst mem2.
pose proof (RIx_rc_step _ _ _ _ _ _ _ _ _ _ _ RX RPX) as (RX' & _).
exists regs', mem', md'. split; [exact Hc|].
split.
{ destruct POST as (AR' & LLE & WLE & ARP & SIO & AGV & PRS).
  split; [split; [exact Hinst | exact AR']|].
  split; [exact LLE|]. split; [exact WLE|]. split; [exact ARP|]. split; [exact SIO|].
  split. { intros a Ha NO NO' NS NE. apply AGV; try assumption. intros HS. apply NS. unfold ascratch in *. unfold KSTACK, KSTACK_CF in *. lia. }
  apply (pres_lift ly X S' W W' mem mem' md md' (spZ regs) HAR AR' WLE RAW Hlo ltac:(lia) ltac:(unfold spZ; apply u64_range) HPRES PRS). }
split.
{ intros x NO NO' NS NE. apply RAW; [exact NO | exact NO' |]. intros HS. apply NS. unfold ascratch. left. unfold KSTACK, KSTACK_CF in *. lia. }
split; [exact RAW|].
split; [exact PUF|].
split.
{ intros a (c0 & Hc0 & Hr). exists c0. split; [exact Hc0|].
  pose proof RPX as RPX'. unfold recycle_post in RPX'. cbn [snd] in RPX'. destruct RPX' as (_ & _ & _ & _ & _ & _ & _ & _ & AU & _).
  rewrite (AU c0 ltac:(lia)). exact Hr. }
split; [exact RX'|]. split; [exact CI|].
intros a O. exact (aowned_rc_back B ly _ _ _ _ X k ns S' Hst RPX a O).
Qed.
Lemma dgif1_rchunk_cgif : dr_rchunk_t B (ARX_cgif B) (aowned B) (DRq_cgif B).
Proof.
intros inst ly X k ks zs cbp W regs mem md PREX RX.
eapply amreal_mono; [|exact (dgif1_rchunk_walk inst ly X k ks zs cbp W regs mem md PREX RX)].
intros r W' c' (regs' & mem' & md' & Hc & HP & HR & _ & REST).
exists regs', mem', md'. split; [exact Hc|]. split; [exact HP|]. split; [exact HR | exact REST].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* di_cdealloc.                                                                                                     *)
(* The CacheDealloc post with cd_leafR's raw frame kept beside acall_raw_x (as dgif1_rchunk_walk). *)
Lemma dgif1_cdealloc_walk : forall inst ly X its z zs W regs mem md,
cd_pre_x B (ARX_cgif B) inst ly X z W regs mem md -> DRq_cgif B X its (z :: zs) ->
amreal tfibsegs (cache_dealloc kBatchClass z X) W (cfg_at tfibsegs A_CDealloc regs mem md)
(fun r W' c' => exists regs' mem' md',
  c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
  acall_post_x B (ARX_cgif B) (aowned B) inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  acall_raw_x B (aowned B) inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  (forall x : word, ~ aowned B ly X (bv_unsigned x) -> ~ aowned B ly (snd r) (bv_unsigned x) ->
   ~ (spZ regs - KSTACK <= bv_unsigned x < spZ regs) -> mem' x = mem x) /\
  (forall a, 0 <= a < 2 ^ 64 -> YFeuC.puser ly X a -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) /\
  (forall a, YFeuC.puser ly X a -> YFeuC.puser ly (snd r) a) /\
  DRq_cgif B (snd r) its zs /\ st_cache_inited (snd r) = true /\ (forall a, aowned B ly (snd r) a -> aowned B ly X a)).
Proof.
intros inst ly X its z zs W regs mem md PREX RX.
destruct PREX as ([Hinst HAR] & Hci & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha2 & Ha3).
pose proof (RIx_cd_pre_its _ _ _ _ _ _ _ _ _ RX) as (WF & Z1 & Z2 & Z3 & ROOM).
assert (ROOM0 : 4 * (Z.of_nat (length (class_elems X kBatchClass)) + 1 + (0 + bslack kBatchClass 0 + 2 * (EV_MAX - st_nev X))) <= rg_mapped_fa (reg X kBatchClass)).
{ change (bslack kBatchClass 0) with 0. exact ROOM. }
assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite (am_tsd B ly X _ (proj1 HAR)); apply (ts_tsd _ TB)).
assert (PRE : cd_pre B ly X kBatchClass z W regs mem md).
{ refine (conj HAR (conj Hci (conj _ (conj Z1 (conj Z2 (conj Z3 (conj ROOM0 (conj Hra (conj Hra4 (conj Hal
    (conj _ (conj Hhi (conj _ (conj Hgp (conj Htp (conj Ha0 (conj _ (conj Ha2 Ha3)))))))))))))))))).
  - unfold kBatchClass. lia.
  - unfold KSTACK, KSTACK_CF in *. lia.
  - intros a Ha. apply HPRES. unfold KSTACK, KSTACK_CF in *. lia.
  - rewrite Ha1, Hinst. reflexivity. }
pose proof (cdealloc_okR ly X kBatchClass z W regs mem md PRE HTSD) as RR.
assert (APOST : apost (cache_dealloc kBatchClass z X)
  (fun r => exists ns, cache_dealloc_post (as_universe B) 0 0 0 X kBatchClass (z - region_off kBatchClass) ns r)).
{ intros tr r0 Hp. exact (atok_apath _ true _ tr r0
    (cache_dealloc_ok (as_universe B) 0 0 0 X kBatchClass z true WF ltac:(unfold kBatchClass; lia) Z1 Z2 Z3 ROOM0) Hp). }
pose proof (amreal_apost tfibsegs _ _ W _ _ APOST RR) as RR2.
eapply amreal_mono; [|exact RR2]. cbv beta.
intros [[] S'] W' c' [(ns & CP) [LEAF (regs2 & mem2 & md2 & Hc2 & RAW)]]. cbn [snd] in RAW |- *.
destruct LEAF as (regs' & mem' & md' & Hc & POST & PUF & CI).
assert (Em : mem2 = mem') by (pose proof (cfg_mem_eqR _ _ (eq_trans (eq_sym Hc2) Hc)) as E; cbn in E; exact E).
subst mem2.
exists regs', mem', md'. split; [exact Hc|].
split.
{ destruct POST as (AR' & LLE & WLE & ARP & SIO & AGV & PRS).
  split; [split; [exact Hinst | exact AR']|].
  split; [exact LLE|]. split; [exact WLE|]. split; [exact ARP|]. split; [exact SIO|].
  split. { intros a Ha NO NO' NS NE. apply AGV; try assumption. intros HS. apply NS. unfold ascratch in *. unfold KSTACK, KSTACK_CF in *. lia. }
  apply (pres_lift ly X S' W W' mem mem' md md' (spZ regs) HAR AR' WLE RAW Hlo Hhi ltac:(unfold spZ; apply u64_range) HPRES PRS). }
split.
{ intros x NO NO' NS NE. apply RAW; [exact NO | exact NO' |]. intros HS. apply NS. unfold ascratch. left. unfold KSTACK, KSTACK_CF in *. lia. }
split; [exact RAW|].
split; [exact PUF|].
split.
{ intros a (c0 & Hc0 & Hr). exists c0. split; [exact Hc0|].
  pose proof CP as CP'. destruct CP' as (_ & _ & AU & _). cbn [snd] in AU.
  rewrite (AU c0 ltac:(lia)). exact Hr. }
split; [exact (RIx_cd_step_its _ _ _ _ _ _ _ _ _ _ _ RX CP)|]. split; [exact CI|].
intros a O. exact (proj1 (aowned_cd_same B ly _ _ _ _ X kBatchClass _ ns S' CP a) O).
Qed.
Lemma dgif1_cdealloc_cgif : dr_cdealloc_t B (ARX_cgif B) (aowned B) (DRq_cgif B).
Proof.
intros inst ly X its z zs W regs mem md PREX RX.
eapply amreal_mono; [|exact (dgif1_cdealloc_walk inst ly X its z zs W regs mem md PREX RX)].
intros r W' c' (regs' & mem' & md' & Hc & HP & HR & _ & REST).
exists regs', mem', md'. split; [exact Hc|]. split; [exact HP|]. split; [exact HR | exact REST].
Qed.
End b.
End a.
