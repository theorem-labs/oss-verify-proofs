(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/AGif1m.v at 95e6f1d72b6 (sha256 a8ba029fc832) into lib/B (libreac/fuzz_decode image B, fuzz_decode.asan-ubsan), with its module paths changed and its image numerals moved to fuzz_decode.asan-ubsan (pin sha256 5d05689fd5b1) by symbol + offset (alreloc 9b786608301; KEEP, regenerated and resolved values per proofs/libreac/fuzz_decode/provenance/alloc-reloc/B/resolve.txt); later the model labels became the model's tags (202260 -> 3, 449860 -> 12). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/B/AGif1m.v, with its module paths, module names and addresses changed; 112 of its 186 lines of code are new or changed and 367 lines of the source are left out. *)
(* fuzz_state image B: the ARU refill lift [fs_refill_U], the premise H_refill_U of lib/B/FSReallocAG.v (:272-273) at
   rtree := refill_tree (the value lib/B/AGif1m.iface_cgif_m fixes, :503-505), at the B relocation's image instances
   AGif2cgif.AImg_cgif / AGif0cgif.AGImg_cgif (a Theorem Labs lane, 2026-10-29).

   rule 24: no function proved (kind: instance lift: the proved ARU refill walk twin composed into the record-field
   shape FSupoisonARXmA.if_refill_t).

   THE PREMISE [tfib_refill_specURaw B].  The ARU refill walk lib/B/FSupoisonAllocRt.tfib_refill_okU proves
   FSupoisonAllocR.tfib_refill_specU B (:385-388), whose leaf refill_leafU (:379-384) carries only the aview frame of
   FSupoisonU.acall_postU, on FSupoison.unpoison U mem.  The record field (AGif0n.rleaf) also asks the frame on the raw
   memory, which aview does not see at hidden in-band bytes.  [refill_leafURaw] is refill_leafU with exactly the
   raw-frame conjunct of a Theorem Labs lane's RAW-TEXT record (refill_leafU section, a Theorem Labs lane
   19:00Z) as its LAST conjunct inside `exists regs' mem' md'`; [tfib_refill_specURaw] is tfib_refill_specU over it.
   When that conjunct is added in place to lib/B/FSupoisonAllocR.v's refill_leafU with the same text, the fixed
   FSupoisonAllocR.tfib_refill_specU B is convertible to tfib_refill_specURaw B (both unfold to the same term), so
   `exact (FSupoisonAllocRt.tfib_refill_okU ..)` discharges this premise.

   THE PROOF mirrors lib/B/AGif1m.refill_cgif (:164): the entry ARU at the post-tick state (FSupoisonAllocR.ARU_tick),
   moved to the call-time memory by FSupoison.ARU_frame (as refill_cgif moves AR by AR_frame_law_ok), the refill
   pre-state refill_preU, the walk from the premise, YFkq.refill_tree_apost for regs_only, and the leaf: ARX_ARU of
   the post state from acall_postU, the aview frame on the raw memory from acall_postU's frame moved off U
   (offU_not_owned / aview_unpoison) and, at errno (which acall_postU's ascratch excludes; never hidden), from the raw
   frame; the raw frame itself; presence on the raw memory by stack_present_real.

   No Axiom, no Admitted. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YG00 YG0a YG01 YG04 YG03 YG06 YG0k YG0f YG0v YG0n YG0d YG0s YG0q YG0t.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG02 YG0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import AllocG AllocGtop DeallocG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
ImgBase ImgBaseAG ImgBaseAGS ImgBaseDG AGif0n AGif2 AGif4 DMspec DMiface DGif0 DIfaceR.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YF0p YFfk.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison FSupoisonU.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoisonARXm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoisonARXmA FSupoisonARXmS FSupoisonARXmD.
(* the image-free glue: the U bridge, the prim + sec split, DIface's callee fields from DIfaceR, img_at *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSReallocAGg.
(* fs's image B: segments, symbols, instance constants; the instance values and the composed realloc contract *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1w YF0m FSRealloc_inst.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YF0x YFl0 YFem FSupoisonARX FSupoisonRealloc FSRealloc_top.
(* the B relocation's image instances (as lib/B/AGif1m.v), the refill callee's names, its ARU walk's statement kit *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import AGif2cgif AGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YB13 YFkq FSupoisonAllocR FSupoisonAllocRt AGif1m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI16.sink_head := _.
Fail Definition probe_SH : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI14.sink_syms := _.

(* lib/B modules named by their full paths: lib/A has modules of the same short names. *)
Module FSU := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonU.
Module FAR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSupoisonAllocR.
Module BX := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.YF0x.
Module BKq := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.YFkq.
Module BM := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.AGif1m.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. The refill contract for any U with the raw frame: lib/B/FSupoisonAllocR.v:379-388 with RAW-TEXT.md's        *)
(*    refill conjunct last inside `exists regs' mem' md'`.                                                           *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Section rf.
Variable B : asyms.
Definition refill_leafURaw (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (c : Z) (r : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
  exists regs' mem' md',
    c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
    FSU.acall_postU tfibsegs B RSTACK ly S U W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
    getr regs' 10 = w64 (match pc_chunks (cache (snd r) c) with [] => 0 | _ => 1 end) /\
    (forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ aowned B ly (snd r) (bv_unsigned x) ->
       ~ (spZ regs - RSTACK <= bv_unsigned x < spZ regs) -> mem' x = mem x).
Definition tfib_refill_specURaw : Prop :=
  forall ly S U W regs mem md c,
    FAR.refill_preU B ly S U W regs mem md c ->
    amreal tfibsegs (refill_tree c S) W (cfg_at tfibsegs A_Refill regs mem md) (refill_leafURaw ly S U W regs mem md c).
End rf.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. The lift's statement: lib/B/FSReallocAG.v's H_refill_U (:272-273) at rtree := refill_tree.                     *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Definition fs_refill_U_stmt : Prop :=
  forall B, TfibSyms B -> tfib_refill_specURaw B -> forall Up,
  FSupoisonARXmA.if_refill_t B (ARX_ARU im_segs B TFIB_INST Up) (aowned B) FS_rpreA qtight refill_tree.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. The lift.  [refill_U_cgif]: if_refill_t's text at the B relocation's instance values (im_segs = tfibsegs,     *)
(*    ag_refill = A_Refill, ag_refill_ret = A_REFILL_RET, im_tp = TFIB_TP), as lib/B/AGif1m.refill_cgif states it;   *)
(*    its proof is refill_cgif's with ARU in place of AR and the premise in place of CLrefillR.tfib_refill_okR.      *)
(*    [fs_refill_U] is it by conversion (as AGif1m.iface_cgif_m takes refill_cgif for the field).                    *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Lemma refill_U_cgif : forall B, TfibSyms B -> tfib_refill_specURaw B -> forall Up inst ly S0 W mem0 md0 n (sp0 : Z)
  (regs : bvmap 5 word) (mem : word -> option byte) (mat : list word),
  ARX_ARU tfibsegs B TFIB_INST Up inst ly S0 W mem0 md0 -> FS_rpreA S0 n -> 0 <= n -> from_primary n = true ->
  pc_chunks (cache S0 (chunk_class n)) = [] ->
  ly_stk_lo ly + ImgBaseAG.AFSTACK <= sp0 -> ly_bot ly < sp0 -> sp0 <= ly_stk_hi ly -> sp0 mod 16 = 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - ImgBaseAG.AFSTACK <= a < sp0) ->
     aview tfibsegs (w_H W) mem a = aview tfibsegs (w_H W) mem0 a) ->
  (forall x : word, ~ (sp0 - ImgBaseAG.AFSTACK <= bv_unsigned x < sp0) ->
     ~ (ly_T ly + t_unwinding <= bv_unsigned x < ly_T ly + t_unwinding + 1) -> mem x = mem0 x) ->
  (forall a, sp0 - ImgBaseAG.AFSTACK <= a < sp0 -> apresent (w_H W) mem a) ->
  spZ regs = sp0 - 176 -> getr regs 1 = w64 A_REFILL_RET -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 TFIB_TP ->
  getr regs 10 = w64 (ly_T ly + t_cache) -> getr regs 11 = w64 (ly_T ly + t_cache + 80 * chunk_class n) ->
  getr regs 12 = w64 inst -> getr regs 13 = w64 (chunk_class n) ->
  amreal tfibsegs (refill_tree (chunk_class n) (set_nev (st_nev S0 + 1) S0)) W
    (cfg_at tfibsegs A_Refill regs mem (with_vm_backing (m_vm_lazy md0) mat md0))
    (rleaf (ARX_ARU tfibsegs B TFIB_INST Up) (aowned B) qtight inst ly S0 n (chunk_class n) W regs mem
       (with_vm_backing (m_vm_lazy md0) mat md0)).
Proof.
intros B TS HSP Up inst ly S0 W mem0 md0 n sp0 regs mem mat [Ei HARU0] [Hev HQ] Hn0 FP Hmiss Hlo Hbot Hhi Hal AG1 RAW1 PRES1
SP R1 R3 R4 R10 R11 R12 R13.
pose proof (FSP.ARU_AR tfibsegs B ly S0 Up W mem0 md0 HARU0) as HAR0.
pose proof (proj1 HAR0) as HARm0. pose proof (am_layout _ _ _ _ HARm0) as LY.
pose proof (BX.img_cover_of_ledger ly S0 md0 (proj1 (proj2 HAR0))) as IMG.
pose proof (lo_top ly LY) as (_ & _ & _ & K2 & _ & _ & K1).
pose proof (BM.T_zone_of ly LY IMG) as ZT.
pose proof (primary_geometry n Hn0 FP) as (Gc & _).
set (cl := chunk_class n) in *. assert (Hcl : 1 <= cl <= 31) by lia.
set (S1 := set_nev (st_nev S0 + 1) S0).
set (md1 := with_vm_backing (m_vm_lazy md0) mat md0).
pose proof (FAR.ARU_tick B ly S0 Up W mem0 md0 HARU0 Hev) as HARU1. fold S1 in HARU1.
pose proof (WfP_tick _ S0 (am_wf _ _ _ _ HARm0) Hev) as WfP1. fold S1 in WfP1.
pose proof (FSP.ARU_AR tfibsegs B ly S1 Up W mem0 md0 HARU1) as HAR1.
(* ARU at the call-time memory (refill_cgif's AR at the call-time memory, by FSupoison.ARU_frame) *)
assert (HARUc : FSP.ARU tfibsegs B ly S1 Up W mem md1).
{ apply (FSP.ARU_frame tfibsegs B (AR_laws_ok tfibsegs B) ly S1 Up W mem0 md0 mem md1 HARU1).
  - intros a Ha Ho. apply AG1; [exact Ha|]. intros Hst.
    apply (AR_stack_law_ok tfibsegs B ly S1 W (FSP.unpoison Up mem0) md0 a HAR1); [lia | exact Ho].
  - intros a Hv. set (x := Z_to_bv 64 a). set (a' := bv_unsigned x).
    assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
    assert (AV : forall m, aview tfibsegs (w_H W) m a = aview tfibsegs (w_H W) m a') by (intros m; unfold aview, mbyte, mrestrict; rewrite Ex; reflexivity).
    rewrite AV in Hv |- *. assert (Ha' : 0 <= a' < 2 ^ 64) by (subst a'; apply u64_range).
    destruct (Z_lt_le_dec a' (sp0 - ImgBaseAG.AFSTACK)) as [H1|H1]; [|destruct (Z_lt_le_dec a' sp0) as [H2|H2]].
    2:{ apply BM.apresent_aview_some. apply PRES1. lia. }
    all: rewrite (AG1 a' Ha' ltac:(lia)); exact Hv.
  - apply m_vmmaps_wvb.
  - apply m_vm_lazy_wvb.
  - apply eager_used_wvb.
  - intros a Ha Hx.
    assert (Ha' : 0 <= a < 2 ^ 64) by (clear - Ha; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; lia).
    assert (HB : kLowShadowBeg <= a < kHighMemBeg) by (clear - Ha; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *; lia).
    pose proof (BX.zone3_apart_hsh _ _ a ZT HB) as TH.
    unfold YG0d.w64, YG0n.w64 in *. apply RAW1; rewrite unsigned_lit_small by exact Ha'.
    + clear - HB K1 Hlo. unfold kHighMemBeg, ImgBaseAG.AFSTACK in *. lia.
    + clear - TH. unfold t_unwinding, kThreadObjSize in *. lia. }
(* the refill callee's pre-state for U (refill_cgif's PRE, on FSupoison.unpoison Up mem) *)
assert (PREU : FAR.refill_preU B ly S1 Up W regs mem md1 cl).
{ pose proof HARUc as (HARc & OK1 & PO1).
  pose proof HAR0 as (_ & _ & [BUD _] & _).
  unfold FAR.refill_preU. split; [|exact (conj OK1 PO1)].
  unfold refill_pre. rewrite SP. unfold raZ. rewrite R1, R3, R4, R10, R11, R12, R13, (ts_tp B TS).
  split; [exact HARc|].
  split; [unfold abudget in *; unfold S1; change (sec_live_bytes (set_nev (st_nev S0 + 1) S0)) with (sec_live_bytes S0);
    change (sec_hulls (set_nev (st_nev S0 + 1) S0)) with (sec_hulls S0); cbn [st_nev set_nev]; unfold EV_A in *; lia|].
  split; [split; [pose proof (wf_prim_ev _ _ _ _ _ WfP1) as PE; lia|];
    split; [exact (aregime_preg_tick S0 cl Hev Hcl) | exact (aregime_mid_tick S0 Hev)]|].
  split; [split; [apply qtight_qloose; exact (qmeter_tight _ HQ) | apply (rroom_tick S0); [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact (qmeter_room _ HQ)]]|].
  split; [apply ret_ok_even; reflexivity|]. split; [unfold w64, YG0d.w64, YG0n.w64, A_REFILL_RET; rewrite unsigned_lit_small by lia; lia|].
  split; [clear - Hal; replace (sp0 - 176) with (sp0 + (-11) * 16) by lia; rewrite Z_mod_plus_full; exact Hal|].
  split; [clear - Hlo; unfold ImgBaseAG.AFSTACK, YFl1.RSTACK in *; lia|]. split; [lia|].
  split; [intros a Ha; apply FAR.apresent_to_unpoison; apply PRES1; clear - Ha; unfold ImgBaseAG.AFSTACK, YFl1.RSTACK in *; lia|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [rewrite Ei; reflexivity|]. split; [reflexivity|]. split; [exact Hcl | exact Hmiss]. }
pose proof (HSP ly S1 Up W regs mem md1 cl PREU) as RR.
pose proof (BKq.refill_tree_apost (as_universe B) 1 1 1 S1 cl WfP1 Hcl ltac:(lia) (aregime_preg_tick S0 cl Hev Hcl)) as APOST.
pose proof (YFfk.amreal_apost tfibsegs _ _ W _ _ APOST RR) as RR2.
eapply amreal_mono; [|exact RR2].
intros r W' c' [(_ & RO & CI) (regs' & mem' & md' & Ec & ((AR' & _ & WLE & RP & IO & FR & PR) & OK' & PO') & A0 & RAWF)].
destruct RO as (Rck & _ & _ & _ & Rqt & Rqg & _).
assert (ENO : forall a, TFIB_ERRNO <= a < TFIB_ERRNO + 4 -> 0x9f000 <= a < 0x5fd000) by (unfold TFIB_ERRNO; lia).
unfold rleaf. exists ly, regs', mem', md'.
split; [exact Ec|].
split; [exact (conj Ei (conj AR' (conj OK' PO')))|].
split; [exact (qtight_ext S0 (snd r) Rck Rqt Rqg (qmeter_tight _ HQ))|].
split; [exact CI|].
split; [unfold blocks_bytes; rewrite Rck; reflexivity|].
split; [apply layout_le_refl|].
split; [exact WLE|].
split; [exact RP|].
split; [exact IO|].
split.
{ (* the aview frame on the raw memory: off U the two readings agree (acall_postU's frame); errno from the raw frame *)
  intros a Ra NO NO' NS. unfold ImgBaseAG.RSTACK in NS.
  change (aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a).
  destruct (Z_le_gt_dec TFIB_ERRNO a) as [E1|E1]; [destruct (Z_lt_ge_dec a (TFIB_ERRNO + 4)) as [E2|E2]|].
  - (* errno: never hidden, so the raw frame gives the view *)
    pose proof (BM.rw_not_hidden W a (ENO a (conj E1 E2))) as Hh.
    assert (Hh' : w_H W' (Z_to_bv 64 a) = false) by (destruct (w_H W' (Z_to_bv 64 a)) eqn:E; [rewrite (WLE _ E) in Hh; discriminate | reflexivity]).
    assert (Ex : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; exact Ra).
    unfold aview, mbyte, mrestrict. rewrite Hh, Hh'.
    rewrite (RAWF (Z_to_bv 64 a)); [reflexivity | rewrite Ex; exact NO | rewrite Ex; exact NO' | rewrite Ex; unfold YFl1.RSTACK; exact NS].
  - pose proof (FAR.offU_not_owned B ly S0 Up W mem0 md0 a HARU0 Ra NO) as O.
    rewrite <- (FAR.aview_unpoison (w_H W') Up mem' a O), <- (FAR.aview_unpoison (w_H W) Up mem a O).
    apply (FR a Ra NO NO'); [|intros []]. unfold ascratch. intros [X|X]; [unfold YFl1.RSTACK in X; exact (NS X)|].
    rewrite (ts_errno B TS) in X. lia.
  - pose proof (FAR.offU_not_owned B ly S0 Up W mem0 md0 a HARU0 Ra NO) as O.
    rewrite <- (FAR.aview_unpoison (w_H W') Up mem' a O), <- (FAR.aview_unpoison (w_H W) Up mem a O).
    apply (FR a Ra NO NO'); [|intros []]. unfold ascratch. intros [X|X]; [unfold YFl1.RSTACK in X; exact (NS X)|].
    rewrite (ts_errno B TS) in X. lia. }
split; [intros x NO NO' NS; exact (RAWF x NO NO' NS)|].
split.
{ (* presence on the raw memory: the callee's window is stack, off U *)
  intros a Ha. unfold ImgBaseAG.RSTACK in Ha.
  apply (FAR.stack_present_real B ly (snd r) Up W' mem' md' (spZ regs - 1024) (spZ regs) (conj AR' (conj OK' PO')));
    [clear - SP Hlo; unfold ImgBaseAG.AFSTACK in *; lia | clear - SP Hhi; lia | | exact Ha].
  intros a' Ha'. apply PR. unfold YFl1.RSTACK. exact Ha'. }
exact A0.
Qed.

Theorem fs_refill_U : forall B, TfibSyms B -> tfib_refill_specURaw B -> forall Up,
  FSupoisonARXmA.if_refill_t B (ARX_ARU im_segs B TFIB_INST Up) (aowned B) FS_rpreA qtight refill_tree.
Proof. intros B TS HSP Up. exact (refill_U_cgif B TS HSP Up). Qed.

Theorem fs_refill_U_ok : fs_refill_U_stmt.
Proof. exact fs_refill_U. Qed.

(* CLOSED (a Theorem Labs lane's in-place refill-leaf fix, a working branch 7a8987cb974, taken by path:
   lib/B FSupoisonAllocR / Rf / Rt / Mm): FSupoisonAllocR.refill_leafU now carries RAW-TEXT.md's raw conjunct last, so
   FSupoisonAllocR.tfib_refill_specU B IS tfib_refill_specURaw B by conversion, and a Theorem Labs lane's re-proved
   FSupoisonAllocRt.tfib_refill_okU discharges the premise. The image-B twin of a Theorem Labs lane's lib/A fs_refill_U_closed. *)
Theorem fs_refill_U_closed : forall B, TfibSyms B -> forall Up,
  FSupoisonARXmA.if_refill_t B (ARX_ARU im_segs B TFIB_INST Up) (aowned B) FS_rpreA qtight refill_tree.
Proof.
intros B TS.
exact (fs_refill_U B TS (OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSupoisonAllocRt.tfib_refill_okU B TS)).
Qed.

End k.
