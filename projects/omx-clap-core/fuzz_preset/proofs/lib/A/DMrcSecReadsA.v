(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMrcSecReads.v (commit 5ad50e61fc6a, file sha256 cad2bf4780da) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; #102 pin 1be0f53d96cb); module paths changed; its 0 image addresses moved by code-verified function pairs (0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 0 code pcs the tool read as sizes, by the internal file funcpair.py), and 1 pcs named in comments; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (head H4 of the interface DMwalkIF.v at dc3949af11c): the SECONDARY arm of
   __asan::QuarantineCallback::Recycle (0x34810) over the opaque cut relation [ARXr], from the munmap ecall to the return,
   in MnRecycle.de_rchunk_m_t's post.
   rule 24: proves function __asan::QuarantineCallback::Recycle (secondary arm), at omx-clap-core/fuzz_preset's asan
   image A' (relocated from the donor's proof at cgif_file_fuzzer's asan-ubsan image); reuse search at fuzz_preset
   (2026-10-31, by name and by word over the released corpus, both with and without the meaning ranking, and an exact
   theorem-name grep over origin/ossv/recipes; a by-address search cannot see this unit, whose released builds carry no
   symbol table): no released file is named for the function.  PRIOR ART: tfib_rchunk_sec (lib/A/AFg9.v on
   origin/ossv/recipes) proves the secondary arm over the concrete amreal / rcc_pre form; these fields state what the
   same arm reads and writes over the opaque cut relation ARXr of DMwalkIF head H4, and take MAP_facts and the map
   definitions of the released lib/A/AFg8.v, which this tree carries at the released blob.
   FIELDS (CfF2b's obligations at ARXr_cf; at cgif YFfc / YFf4 / AFg8.MAP_facts / AFg8.FIN_core):
   rc_sec_cut_t   the CUT READ: DMrcSecFcA.sec_cut at the call, inst = as_inst B, the TSD and the image's constant cells;
   rc_sec_mapr_t  the MAP READ: the map's index in the array, its interval in the world's account, its vm map, the
                  model's well-formedness and the madvise gate over its shadow;
   rc_sec_step_t  the MAPPING STEP (sibling of DMrcReadsA.rc_prim_step_t, the no-map step): from the walk's own frame at
                  the return (DMrcSecMunA.LINKD + DMrcSecGvA.at_RET: memory off the walk's windows unchanged, the map's
                  shadow zeroed and the map unfilled, the written allocator words, the constant cells still holding) after the munmap of the map, the cut
                  relation at the model's next state with the refunded world, the windows inside the owned set or the
                  stack scratch, and the owned / user steps.  The map's shadow residue is the cf discharge's (the R-form:
                  Rs shrinks at the unmap and keeps the <= 2 edge shadow pages, KMAX a unit parameter; the internal file RECIPE.md
                  :859-881); no size or residue literal is stated here.
   rc_sec_step_g  rc_sec_step_t with the cut relation of its post a parameter [ARXp] indexed by a SLACK (the pre stays
                  [ARXr]): the post is ARXp (YGcfRehidePost.rh_hi MAP LEN - YGcfRehidePost.rh_lo MAP) at the model's
                  next state, the slack the recycled slot's re-hide pays (MAP = AFg8.MAP ly r, LEN = AFg8.LEN sm).
                  rc_sec_step_t is rc_sec_step_g at ARXp := fun _ => ARXr.  At a real recycle the cf relation holds at
                  the post state only loosened by the dead hull the world still counts (YGcfRehideAR.ARcfR_sl at that
                  slack); plain ARXr holds again in the re-hidden world (DMrcRh). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AFeq AFex AFfu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFfj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AFew AFeu AFfm AFf3 AFf4 AFff AFgu AFf5 AFgw AFfb AFg8 AFfc AB13.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG08 YG0g.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMwalkIFA DMrcSecFcA DMrcSecGvA DMrcSecWalkA DMrcSecF6A DMrcSecF7A DMrcSecF9A DMrcSecMunA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require ErrnoG MemnormT MemnormLocG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMrcReadsA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DIfaceR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import DMwalkIFA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0v YFfn YA05 YG0j.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kPtrArrayResv, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, KSTACK, TFIB_IMG_END, kBatchBytes, SHADOW_OFF, TFIB_TP, TFIB_TSD, TFIB_INST, A_ALLOCATOR, o_space, o_rinfo, o_sec, o_sec_chunks, o_sec_reserved, o_sec_n, o_sec_sorted, o_sec_stats, o_sec_mutex, kRegionInfoOff, kLowMemEnd, kChunkHeaderSize, kPage, AFgu.GFRAME, DMrcSecGvA.GDEPTH in *.
Ltac splits := repeat match goal with |- _ /\ _ => split end.
Ltac inS := cbn [In]; repeat (first [left; reflexivity | right]).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.
Section f.
Variable B : asyms.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Definition rc_sec_cut_t : Prop :=
forall inst ly X k cbp W regs mem md r o sm i,
rcc_pre_x B ARXr inst ly X k cbp W regs mem md -> ck_beg k = PSec r o -> nth_error (st_secs X) r = Some sm ->
nth_error (st_sec_arr X) i = Some r -> In k (st_chunks X) -> ck_state k = CQuarantined ->
inst = as_inst B /\ ly_tsd ly = as_tsd B /\ Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (as_const B ly) /\
DMrcSecFcA.sec_cut B ly X k W regs mem r o sm i.
Definition rc_sec_mapr_t : Prop :=
forall inst ly X k cbp W regs mem md r o sm i,
rcc_pre_x B ARXr inst ly X k cbp W regs mem md -> ck_beg k = PSec r o -> nth_error (st_secs X) r = Some sm ->
nth_error (st_sec_arr X) i = Some r ->
index_of (st_sec_arr X) r 0%nat = Some i /\
In (AFg8.MAP ly r, AFg8.MAP ly r + AFg8.LEN sm) (w_A W) /\ In (w64 (AFg8.MAP ly r), w64 (AFg8.LEN sm)) (vm_maps (m_vmmaps md)) /\ amwf md /\
(forall PB kk, 0 < kk -> DMrcSecGvA.SHAv (AFg8.MAP ly r) <= PB -> PB + kk <= DMrcSecGvA.SHEv (AFg8.MAP ly r) (AFg8.LEN sm) ->
 madvise_dontneed_ok (m_vmmaps md) (Z_to_bv 64 PB) (Z_to_bv 64 kk) = true).
End f.
Section g.
Variable B : asyms.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable ARXp : Z -> (Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop).
Variable AOX : alayout -> astate -> Z -> Prop.
Definition rc_sec_step_g : Prop :=
forall inst ly X k cbp W regs mem md r o sm i regsD memD mat1 regs' mem' mat,
rcc_pre_x B ARXr inst ly X k cbp W regs mem md -> ck_beg k = PSec r o -> nth_error (st_secs X) r = Some sm ->
nth_error (st_sec_arr X) i = Some r ->
In k (st_chunks X) -> ck_state k = CQuarantined -> ~ In (ck_beg k) (map ck_beg (q_items X)) ->
DMrcSecMunA.LINKD ly W regs mem regsD memD ->
let MAP := AFg8.MAP ly r in let LEN := AFg8.LEN sm in
let mdM := munmap_model (w64 MAP) (w64 LEN) (with_vm_backing (m_vm_lazy md) mat1 md) in
DMrcSecGvA.at_RET W ly regsD memD MAP LEN (AFg8.idx i) (AFg8.nA X) (AFg8.qi ly i) (AFg8.lst ly X r)
  (DMrcSecF6A.v regs 1%bv) (DMrcSecF6A.v regs 8%bv) (DMrcSecF6A.v regs 9%bv) (DMrcSecF6A.v regs 18%bv) (AFg8.own X i) mdM
  W (mkCfg (mkst regs' (w64 (DMrcSecF6A.v regs 1%bv)) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy mdM) mat mdM)) ->
Forall (cell_holds B ly (aview tfibsegs (w_H W) mem')) (as_const B ly) ->
ARXp (YGcfRehidePost.rh_hi MAP LEN - YGcfRehidePost.rh_lo MAP) inst ly (AFg8.X2v X k r sm i) (AFg8.W2 ly W r sm) mem'
  (with_vm_backing (m_vm_lazy mdM) mat mdM) /\
(forall a, 0 <= a < 2 ^ 64 -> DMrcSecMunA.WPRE ly regs a \/ DMrcSecGvA.WIN3 ly regs MAP LEN (AFg8.qi ly i) (AFg8.lst ly X r) a ->
 AOX ly X a \/ ascratch B KSTACK_CF regs a) /\
(forall a, AOX ly (AFg8.X2v X k r sm i) a -> AOX ly X a) /\
(forall a, YFeuC.puser ly X a -> YFeuC.puser ly (AFg8.X2v X k r sm i) a) /\
(forall a, YFeuC.puser ly X a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) ->
 ~ DMrcSecMunA.WPRE ly regs a /\ ~ DMrcSecGvA.WIN3 ly regs MAP LEN (AFg8.qi ly i) (AFg8.lst ly X r) a) /\
st_cache_inited (AFg8.X2v X k r sm i) = true.
End g.
Section t.
Variable B : asyms.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Definition rc_sec_step_t : Prop := rc_sec_step_g B ARXr (fun _ => ARXr) AOX.
End t.
End d.
