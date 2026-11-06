(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACf1.v, with its module paths and module names changed; 639 of its 687 lines of code are new or changed and 451 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_fuzz_free.v, with its module paths changed; 469 of its 535 lines of code are new or changed and 621 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/FSW_fuzz_malloc.v, with its numbers changed; 409 of its 516 lines of code are new or changed and 428 lines of the source are left out. *)
(* fs ASan+UBSan (image B: fs.asan-ubsan), group ALLOC, a Theorem Labs lane: fuzz_realloc's SEG-CD (B 0x82bc4, alloc.c:75-94),
   from the realloc call point fsr_at_realloc to arm (c) of fuzz_realloc_spec (lib/B/FSW_realloc_pn.v's interface).
   proves function fuzz_realloc (B 0x82bc4) (reuse search: proof-index on main@f4cc67298b7 / ossv/recipes@5121fb8693b
   / ossv/candidates@ee89628c997 / release/pau-projects-recipes@b6a0088adcb, by address on those four refs, and on named
   lane branches / `proof-index fuzz_realloc`, `git grep -i -e <addr>`, `git grep -E '^(Theorem|Lemma)
   .*fuzz_realloc_spec'`; B 0x82bc4: 0 hits, CONFIRM).

   MEASURED (capstone 5.0.7 on the unstripped twin of the pinned fuzz_state.asan-ubsan): `jal __wrap_realloc` 0x82cec
   (0x530e8, ra 0x82cf0); `beqz a0` 0x82cf0 (NULL: dead, lib/B/FSW_realloc.arealloc_granted: 4096 <= a0); a1 = s0 = n
   0x82cf4; restore ra / s0 / s1 / s2 from [sp0 - 8 .. sp0 - 32], sp += 32; tail `j own` 0x82d0c (0x82acc) with a0 = b,
   a1 = n. B's own() is out of line, so the poison of the new head is own's (own_spec), not this segment's.

   Steps: the realloc call (lib/B/FSW_realloc.fsw_aj_reallocU: three ticks, the old block replaced by the new one at the
   end of the block list, the kept bytes copied); the resume at 0x82cf0 (FSW_rres.fsw_resume_after_rtU_args_chunks: the
   four saved words as chunks read back from the caller's val_mem facts, kept across the call by acall_kept); two runs
   (`beqz`, then the epilogue and `j own`); own's fpreU at the tail state (FSW_ret.fsw_fpreU_atFP, o = 0); own_spec; and
   the composition of own's fpostU into arm (c) (fsrCD_tail_post: ajournal_sub with own's footprint FS_PSTAT_FP ++
   [(b, b + 8)] being the caller's statics and the new block's head, which is either the old block (realloc in place,
   inside fsr_FPc) or a block the caller's realloc made (in_tmp_block)). The kept bytes reach the post through three
   keeps: realloc's copy, the two runs' frame (no write window covers the block), own's journal (block bytes off own's
   footprint).

   ported from: lib/A/FSW_realloc_segC.v (a Theorem Labs lane, image A; fsrC_unpoison_sub, fsrC_val_keep, fsrC_glob_acall copied
   with the prefix fsrCD_, as A's file is image A and may not be Required here), lib/B/FSW_fuzz_malloc.v (a Theorem Labs lane;
   the resume / `beqz` / tail call into own, fmB_tail_post generalised to ajournal_sub's full footprint premise and a
   post conversion that sees own's journal). No rename. Relocated files: none.

   NAMED PREMISES (arguments of fsr_segCD_stmt, listed with owners in the lane report): fs_img_facts (RELOC),
   FsShadowSyms (the B start-up layer), api_env (RELOC), FS_AREALLOC_BU (a Theorem Labs lane via a Theorem Labs lane),
   own_spec (a Theorem Labs lane's lib/B/FSW_own.own_holds discharges it). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG08 YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q YG05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen FSpoisonS.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSH_Fn_alloc FSH_ReallocModel FSupoisonRealloc FSW_K FSW_K3 FSW_ret FSW_rres FSW_rd
FSW_statics FSW_statics_awr FSW_head FSW_poison_conv FSW_fuzz_realloc_tbl FSW_realloc FSW_realloc_pn FSW_fuzz_malloc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The segment statement                                                                                            *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* SEG-CD: from the realloc call point to arm (c), given the entry's premises *)
Definition fsr_segCD_stmt : Prop :=
  fs_img_facts tfibsegs B -> FsShadowSyms B -> api_env tfibsegs B -> FS_AREALLOC_BU tfibsegs B (as_universe B) ->
  @own_spec fx rc SK tfibsegs B ->
  forall ly S U W regs mem md ch p k n old live peak cnt fail U1 U2 W2 c,
  fsr_pre_pn B ly S U W regs mem md ch p k n old live peak cnt fail U1 U2 ->
  fsr_at_realloc B ly S U W regs mem md p k n old live peak cnt fail U1 U2 W2 c ->
  SRr tfibsegs W2 c (fsr_post_c B ly S U W regs mem md p k n old live peak cnt fail U1 U2).
End i.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Helpers (prefix fsrCD_)                                                                                           *)
(* ---------------------------------------------------------------------------------------------------------------- *)

(* unpoisoning a SUBSET of U on top of unpoison U changes nothing (A: FSW_realloc_segC.fsrC_unpoison_sub, verbatim) *)
Lemma fsrCD_unpoison_sub : forall (U U' : list (Z * Z)) (mem : word -> option byte),
  (forall r, In r U' -> In r U) -> unpoison U' (unpoison U mem) = unpoison U mem.
Proof.
intros U U' mem HS. apply functional_extensionality. intros w.
destruct (in_ush U' (bv_unsigned w)) eqn:E1.
- rewrite (unpoison_in U' (unpoison U mem) w E1). symmetry. apply unpoison_in.
  apply in_ush_spec. apply in_ush_spec in E1 as (r & Hr & Hrng). exists r. split; [exact (HS r Hr) | exact Hrng].
- rewrite (unpoison_out U' (unpoison U mem) w E1). reflexivity.
Qed.

(* the write windows of the state resumed after the realloc call: the frame and the statics *)
Lemma fsrCD_nw : forall E rs a r, skeleton rs = skeleton (ss_mem (fss_retT r 32 fsr_cs fs_pstat_regions [])) ->
  a < bv_unsigned (ew E 2) -> ~ inFP FS_PSTAT_FP a -> ~ in_wrange E rs a.
Proof.
intros E rs a r Hsk Hlt Hnf Hw. apply (in_wrange_skeleton E rs _ a Hsk) in Hw. destruct Hw as (rg & Hin & Ha).
assert (NS : forall g, In (g, g + 8) FS_PSTAT_FP -> ~ (g <= a < g + 8))
  by (intros g Hg Ha'; apply Hnf; exists (g, g + 8); split; [exact Hg | cbn [fst snd]; lia]).
vm_compute in Hin.
repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    first [ lia
          | lazymatch type of Ha with _ + ?g <= _ < _ => apply (NS g); [vm_compute; tauto | lia] end ]
  | ]).
destruct Hin.
Qed.

(* the caller's footprint fsr_FPc: the sink stays closed (no byte at address 0) *)
Lemma fsrCD_FPc_sink : forall p k, 4096 <= p - HEAD -> ~ YI16.sink_open_fp (fsr_FPc p k).
Proof.
intros p k Hp (r & Hr & H0). unfold fsr_FPc in Hr. apply in_app_or in Hr as [Hr | Hr].
- apply fmB_pstat_sink. exists r. split; [exact Hr | exact H0].
- unfold ablocks_fp in Hr. cbn [map fst snd] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in H0. lia.
Qed.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd := fs_segs_low.

(* no read-only byte lies in fsr_FPc: the statics are writable, the block is no image byte *)
Lemma fsrCD_FPc_not_ro : forall ly S (W : world tfibsegs) mem md p k,
  AR tfibsegs B ly S W mem md -> In (p - HEAD, k + HEAD) (ablocks B ly S) ->
  forall a, in_roP tfibsegs FS_RLO FS_RHI a -> ~ inFP (fsr_FPc p k) a.
Proof.
intros ly S W mem md p k HAR Hin a Hro (r & Hr & Ha). unfold fsr_FPc in Hr. apply in_app_or in Hr as [Hr | Hr].
- exact (fmB_pstat_not_ro a Hro (ex_intro _ r (conj Hr Ha))).
- unfold ablocks_fp in Hr. cbn [map fst snd] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  exact (blk_img tfibsegs B LAWS ly S W mem md (p - HEAD) (k + HEAD) a HAR Hin ltac:(lia) (fsw_roP_img a Hro)).
Qed.

(* a value held HIGH (the caller's frame) is kept across a call that keeps its aview (A: fsrC_val_keep, verbatim) *)
Lemma fsrCD_val_keep : forall ly S ly' S' U (W W' : world tfibsegs) mem mem' md md' a (j : nat) v,
  ARU tfibsegs B ly S U W mem md -> ARU tfibsegs B ly' S' U W' mem' md' ->
  (forall x, a <= x < a + Z.of_nat j ->
     aview tfibsegs (w_H W') (unpoison U mem') x = aview tfibsegs (w_H W) (unpoison U mem) x) ->
  kHighMemBeg <= a -> a + Z.of_nat j < 2 ^ 64 ->
  val_mem tfibsegs (mrestrict (w_H W) mem) a j v -> val_mem tfibsegs (mrestrict (w_H W') mem') a j v.
Proof.
intros ly S ly' S' U W W' mem mem' md md' a j v H1 H2 HV Hlo Hhi Hv i Hi.
rewrite <- (Hv i Hi). apply fsr_mbyte_of_aview2.
rewrite <- (fsw_aview_unpoison_high B ly' S' U W' mem' md' (a + Z.of_nat i) H2 ltac:(lia)).
rewrite <- (fsw_aview_unpoison_high B ly S U W mem md (a + Z.of_nat i) H1 ltac:(lia)).
exact (HV (a + Z.of_nat i) ltac:(lia)).
Qed.

(* fs_glob is kept by any memory change that keeps the four statics' bytes (A: fsrC_glob_mbyte, verbatim) *)
Lemma fsrCD_glob_mbyte : forall (W W' : world tfibsegs) (m m' : word -> option byte) live peak cnt fail,
  (forall a, inFP FS_PSTAT_FP a ->
     mbyte tfibsegs (mrestrict (w_H W') m') a = mbyte tfibsegs (mrestrict (w_H W) m) a) ->
  fs_glob tfibsegs W m live peak cnt fail -> fs_glob tfibsegs W' m' live peak cnt fail.
Proof.
intros W W' m m' live peak cnt fail KB (G1 & G2 & G3 & G4 & GR).
assert (V : forall g v, In (g, g + 8) FS_PSTAT_FP ->
  val_mem tfibsegs (mrestrict (w_H W) m) g 8 v -> val_mem tfibsegs (mrestrict (w_H W') m') g 8 v).
{ intros g v Hg Hv i Hi. rewrite (KB (g + Z.of_nat i)); [exact (Hv i Hi)|].
  exists (g, g + 8). split; [exact Hg | cbn [fst snd]; lia]. }
split; [apply (V G_LIVE live); [vm_compute; tauto | exact G1]|].
split; [apply (V G_PEAK peak); [vm_compute; tauto | exact G2]|].
split; [apply (V G_COUNT cnt); [vm_compute; tauto | exact G3]|].
split; [apply (V G_FAIL fail); [vm_compute; tauto | exact G4]|].
exact GR.
Qed.

(* fs_glob across an allocator call: the statics are image bytes, no owned static and off errno (A: fsrC_glob_acall) *)
Lemma fsrCD_glob_acall : forall ly S ly' S' U (W W' : world tfibsegs) mem mem' md md' slo shi Ex live peak cnt fail,
  fs_img_facts tfibsegs B ->
  ARU tfibsegs B ly S U W mem md -> ARU tfibsegs B ly' S' U W' mem' md' ->
  acall_kept tfibsegs B ly S W (unpoison U mem) W' (unpoison U mem') slo shi Ex ->
  fs_glob tfibsegs W mem live peak cnt fail -> fs_glob tfibsegs W' mem' live peak cnt fail.
Proof.
intros ly S ly' S' U W W' mem mem' md md' slo shi Ex live peak cnt fail IMG H1 H2 (_ & _ & HKimg & _) G.
apply (fsrCD_glob_mbyte W W' mem mem' live peak cnt fail); [|exact G].
intros a Ha. destruct (proj1 IMG a Ha) as (HnOwn & HnErr).
assert (Hlo : 0 <= a < SHADOW_OFF) by (pose proof (fsr_pstat_low a Ha); unfold SHADOW_OFF; lia).
apply fsr_mbyte_of_aview2.
rewrite (aview_at tfibsegs (w_H W') mem' (unpoison U mem') a
  (eq_sym (fs_head_app_view B ly' S' U W' mem' md' a H2 ltac:(unfold SHADOW_OFF in *; lia) ltac:(left; lia)))).
rewrite (aview_at tfibsegs (w_H W) mem (unpoison U mem) a
  (eq_sym (fs_head_app_view B ly S U W mem md a H1 ltac:(unfold SHADOW_OFF in *; lia) ltac:(left; lia)))).
exact (HKimg a (fs_pstat_img a Ha) HnOwn HnErr).
Qed.

(* ---- a TAIL call's post (lib/B/FSW_fuzz_malloc.fmB_tail_post, generalised): ajournal_sub's full footprint premise,
   and a post conversion that also sees the callee's journal and poison facts ---- *)
Lemma fsrCD_tail_post : forall STK sp0 FP regs ly S U (W : world tfibsegs) mem md k lyc Sc Uc Wc memc mdc regsc STK1 FP1
  k1 k2 U' (Q1 Q : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  ajournal tfibsegs B STK sp0 FP ly S W (unpoison U mem) md [] lyc Sc Wc (unpoison Uc memc) mdc k ->
  spZ regsc = sp0 -> STK1 <= STK -> getr regsc 1 = getr regs 1 -> aregs_preserved regs regsc -> k + k1 = k2 ->
  (forall a, inFP FP1 a ->
     (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
     in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a \/
     (inFP FP a /\ in_img tfibsegs a)) ->
  (forall ly' S' W' regs' mem' md',
     ajournal tfibsegs B STK1 sp0 FP1 lyc Sc Wc (unpoison Uc memc) mdc [] ly' S' W' (unpoison U' mem') md' k1 ->
     upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
     Q1 ly' S' W' regs' mem' md' -> Q ly' S' W' regs' mem' md') ->
  forall W' c', fpostU tfibsegs B STK1 (spZ regsc) FP1 regsc lyc Sc Uc Wc memc mdc k1 U' Q1 W' c' ->
  fpostU tfibsegs B STK sp0 FP regs ly S U W mem md k2 U' Q W' c'.
Proof.
intros STK sp0 FP regs ly S U W mem md k lyc Sc Uc Wc memc mdc regsc STK1 FP1 k1 k2 U' Q1 Q HJ Hsp HSTK Hra HP Hk HF HQ
  W' c' (ly' & S' & regs' & mem' & md' & -> & HJ1 & OK & PO & HP' & HQ1).
rewrite Hsp in HJ1.
exists ly', S', regs', mem', md'.
split; [rewrite Hra; reflexivity|].
split.
{ subst k2.
  exact (ajournal_sub tfibsegs B LAWS segs_low STK sp0 FP ly S W (unpoison U mem) md [] lyc Sc Wc (unpoison Uc memc) mdc k
    STK1 sp0 FP1 [] ly' S' W' (unpoison U' mem') md' k1 HJ HJ1 ltac:(lia) ltac:(lia) HF). }
split; [exact OK|]. split; [exact PO|].
split; [exact (aregs_preserved_trans _ _ _ HP HP')|].
exact (HQ _ _ _ _ _ _ HJ1 OK PO HQ1).
Qed.

(* an application byte reads the same through unpoison *)
Lemma fsrCD_app_view : forall ly S U (W : world tfibsegs) mem md a, ARU tfibsegs B ly S U W mem md ->
  0 <= a < 2 ^ 64 -> a < SHADOW_OFF \/ kHighMemBeg <= a ->
  aview tfibsegs (w_H W) (unpoison U mem) a = aview tfibsegs (w_H W) mem a.
Proof.
intros ly S U W mem md a H Ha Happ. exact (aview_at tfibsegs (w_H W) (unpoison U mem) mem a
  (fs_head_app_view B ly S U W mem md a H Ha Happ)).
Qed.
End k.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* SEG-CD                                                                                                           *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

Lemma fsr_segCD : fsr_segCD_stmt B.
Proof.
intros IMG SHS ENV AREALLOC OWN ly S U W regs mem md ch p k n old live peak cnt fail U1 U2 W2 c HPRE HAT.
pose proof (proj1 SHS) as FS_GOT. pose proof (proj2 SHS) as FS_CELL.
pose proof HPRE as (HPREU & FH & H10 & H11 & Hn1 & HnM & HGL & Hlv & Hcn & Hcf & Hp0 & EU & HRB & Hlen & HZ & Hkl & Hev
  & Hbb).
destruct HAT as (regsT & memT & md2 & Ec & HJ & HARU & T10 & T11 & T1 & Tsp & T8 & T9 & T18 & HKP & HFV & HGL2 & HZT).
pose proof HPREU as (HAP & HRO).
pose proof (fsw_ARU B STK_fuzz_realloc ly S U W regs mem md ch HAP) as HARU0.
pose proof HAP as (HAN & _ & _).
pose proof HAN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (_ & _ & _ & _ & _ & Hshi47 & _ & Hsptop & Htophi).
pose proof (fsw_sp B STK_fuzz_realloc ly S U W regs mem md ch HAP) as (Hal16 & Hceil & H47 & HSTK0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FR : STK_fuzz_realloc = ltac:(let v := eval vm_compute in STK_fuzz_realloc in exact v)) by reflexivity.
assert (FRo : STK_own <= STK_fuzz_realloc) by (apply Z.leb_le; vm_compute; reflexivity).
assert (FRo0 : 0 <= STK_own) by (apply Z.leb_le; vm_compute; reflexivity).
assert (Hceil47 : alloc_ceiling < 2 ^ 47) by exact alloc_ceiling_lt.
assert (HD : HEAD = 16) by reflexivity.
pose proof HGL as (G1 & G2 & G3 & G4 & Hlp & Hp64 & Hc64 & Hf64).
pose proof HARU0 as (HAR0 & (HUF & HUPW) & HUPO).
destruct HFV as (V18 & V9 & V8 & V1).
pose proof HRB as (Hblk & Hp16 & Hk0 & Hhead).
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md (p - HEAD) (k + HEAD) HAR Hblk)
  as (Hob16 & Hob4096 & Hobceil & _).
assert (Hrqk : req_size (k + HEAD) = k + HEAD) by (unfold req_size, HEAD; destruct (Z.eqb_spec (k + 16) 0); lia).
assert (Hn64 : 0 <= n < 2 ^ 64) by (unfold MALLOC_MAX, HEAD in *; lia).
assert (FHU : fs_heads B ly S (U1 ++ (p - HEAD, HEAD) :: U2)) by (rewrite <- EU; exact FH).
assert (PWU : pairwise zdisjoint (U1 ++ (p - HEAD, HEAD) :: U2)) by (rewrite <- EU; exact HUPW).
assert (FH12 : fs_heads B ly S (U1 ++ U2)).
{ intros r Hr. apply FHU. apply in_app_or in Hr as [Hx|Hx]; apply in_or_app; [left; exact Hx | right; right; exact Hx]. }
assert (HNIN : ~ In (p - HEAD, HEAD) (U1 ++ U2)) by (apply (pairwise_head_once U1 U2 (p - HEAD)); exact PWU).
assert (HUout : forall rg, In rg (U1 ++ U2) ->
  fst rg + snd rg <= p - HEAD \/ (p - HEAD) + req_size (k + HEAD) <= fst rg).
{ intros rg Hrg. eapply (ARU_free_outside tfibsegs B).
  all: first [ solve [exact LAWS] | solve [exact HARU] | solve [exact FH12] | solve [exact Hblk]
             | solve [exact HNIN] | solve [exact Hrg] ]. }
assert (EUM : unpoison (U1 ++ U2) (unpoison U mem) = unpoison U mem).
{ apply fsrCD_unpoison_sub. intros r Hr. rewrite EU.
  apply in_app_or in Hr as [Hx|Hx]; apply in_or_app; [left; exact Hx | right; right; exact Hx]. }
assert (HJ0 : ajournal tfibsegs B STK_fuzz_realloc (spZ regs) (fsr_FPc p k) ly S W
  (unpoison (U1 ++ U2) (unpoison U mem)) md [] ly S W2 (unpoison (U1 ++ U2) memT) md2 0)
  by (rewrite EUM; exact HJ).
rewrite Ec.
(* ---- the realloc call (lib/B/FSW_realloc.fsw_aj_reallocU): three ticks, the block swapped, the kept bytes ---- *)
eapply SRr_bind.
{ eapply (fsw_aj_reallocU B ENV AREALLOC W2 regsT memT STK_fuzz_realloc (spZ regs) (fsr_FPc p k) ly S W
    (unpoison U mem) md [] ly S (U1 ++ U2) md2 0 (p - HEAD) (k + HEAD) (n + HEAD) (-32)
    (Z_to_bv 64 A_fuzz_realloc_raB) []).
  all: first
    [ solve [exact HJ0] | solve [exact HARU] | solve [exact Hblk] | solve [exact HUout]
    | solve [exact T10] | solve [exact T11] | solve [exact T1] | solve [exact Hbb]
    | solve [exact (proj1 (proj2 HKP))] | solve [exact (proj2 (proj2 HKP))]
    | solve [lazymatch goal with |- _ <= _ < MALLOC_MAX => unfold MALLOC_MAX, HEAD in *; lia end]
    | solve [lazymatch goal with |- spZ _ = _ => rewrite Tsp; lia end]
    | solve [lazymatch goal with |- _ mod _ = _ => reflexivity end]
    | solve [lazymatch goal with |- _ + 16 < 0 => lia end]
    | solve [lazymatch goal with |- STK_RT_REALLOC - _ <= _ => apply Z.leb_le; vm_compute; reflexivity end]
    | solve [lazymatch goal with |- YK0s.ret_ok _ =>
               apply ret_ok_even; rewrite unsigned_lit_small by (unfold A_fuzz_realloc_raB; lia); reflexivity end]
    | solve [lazymatch goal with |- st_nev _ + 2 < EV_MAX => lia end]
    | solve [lazymatch goal with |- chain_pre _ _ _ _ =>
               unfold chain_pre; split;
               [ unfold raZ; rewrite T1, unsigned_lit_small by (unfold A_fuzz_realloc_raB; lia);
                 unfold A_fuzz_realloc_raB; lia
               | destruct (frame0_ok ly regsT); [|reflexivity];
                 replace (bad_next (spZ regsT) (ly_top ly) (s0Z regsT)) with true; [reflexivity|];
                 symmetry; unfold bad_next; rewrite Tsp; unfold s0Z; rewrite T8; unfold w64;
                 rewrite unsigned_lit_small by (unfold MALLOC_MAX, HEAD in *; lia);
                 apply orb_true_iff; left; apply orb_true_iff; left; apply Z.leb_le;
                 unfold MALLOC_MAX, HEAD in *; lia ] end]
    | solve [lazymatch goal with |- forall i, _ -> inFP _ _ =>
               intros i Hi; exists (p - HEAD, p - HEAD + req_size (k + HEAD)); split;
               [ unfold fsr_FPc, ablocks_fp; apply in_or_app; right; cbn [map fst snd]; left; reflexivity
               | cbn [fst snd]; lia ] end]
    | solve [lia] ]. }
intros W3 c3 _ (ly2 & S2 & regs2 & mem2 & md3 & b & -> & HARU2 & HJc & HP & R10 & Hfr2 & Hnev2 & Hb4096 &
  (b1 & b2 & Eb1 & Eb2) & CPY & HK).
rewrite EUM in HJc. change (0 + 3) with 3 in HJc.
assert (GA : fs_glob tfibsegs W3 mem2 (live - k) peak (cnt + 1) fail)
  by exact (fsrCD_glob_acall B ly S ly2 S2 (U1 ++ U2) W2 W3 memT mem2 md2 md3 _ _ _
       (live - k) peak (cnt + 1) fail IMG HARU HARU2 HK HGL2).
(* ---- the new block ---- *)
assert (Hnew : In (b, n + HEAD) (ablocks B ly2 S2)) by (rewrite Eb2; apply in_or_app; right; left; reflexivity).
assert (Hrq : req_size (n + HEAD) = n + HEAD)
  by (unfold req_size, HEAD; destruct (Z.eqb_spec (n + 16) 0); lia).
destruct (al_blocks _ _ LAWS ly2 S2 W3 (unpoison (U1 ++ U2) mem2) md3 b (n + HEAD) (proj1 HARU2) Hnew)
  as (Hb16 & _ & Hbceil & Happ & _).
rewrite Hrq in Hbceil.
rewrite FR in Hceil.
destruct (fsr_new_heads B ly S ly2 S2 W3 (unpoison (U1 ++ U2) mem2) md3 U1 U2 (p - HEAD) k b n b1 b2
  (proj1 HARU2) FHU PWU Eb1 Eb2 ltac:(lia)) as (FH12b & FHnew & DJ).
assert (HFRESH : ~ In (b, n + HEAD) (b1 ++ b2)).
{ intros Hin. apply in_split in Hin as (x1 & x2 & Ex).
  pose proof (sep_blocks_pos tfibsegs B LAWS ly2 S2 W3 (unpoison (U1 ++ U2) mem2) md3 (b, n + HEAD) (b, n + HEAD)
    x1 x2 [] (proj1 HARU2) ltac:(rewrite Eb2, Ex, <- app_assoc; reflexivity)) as D.
  unfold zdisjoint, block_rng in D. cbn [fst snd] in D. rewrite Hrq in D. unfold HEAD in *. lia. }
assert (Hnin : ~ In (b, HEAD) (U1 ++ U2)).
{ intros Hin. pose proof (proj1 (Forall_forall _ _) DJ _ Hin) as D. unfold zdisjoint in D. cbn [fst snd] in D.
  unfold HEAD in *. lia. }
(* the block's bytes: below the frame, no static, application bytes *)
assert (NIMG : forall a, b <= a < b + n + HEAD -> ~ inFP FS_PSTAT_FP a).
{ intros a Ha Hf. exact (blk_img tfibsegs B LAWS ly2 S2 W3 _ md3 b (n + HEAD) a (proj1 HARU2) Hnew
    ltac:(rewrite Hrq; lia) (fs_pstat_img a Hf)). }
assert (HAPPB : forall a, b <= a < b + n + HEAD -> 0 <= a < 2 ^ 64 /\ (a < SHADOW_OFF \/ kHighMemBeg <= a)).
{ intros a Ha. split; [lia|].
  destruct (in_app_addr _ _ a Happ ltac:(rewrite Hrq; lia)) as [_ [Hx|[Hx _]]].
  - left. unfold kLowShadowBeg, SHADOW_OFF in *. lia.
  - right. exact Hx. }
(* ---- the kept bytes, at the new block's body after the call (realloc's copy) ---- *)
set (l := firstn (Z.to_nat (Z.min k n)) old).
assert (Hll : Z.of_nat (length l) = Z.min k n).
{ unfold l. rewrite firstn_length_le by lia. lia. }
assert (Z1 : zbytes_at tfibsegs W3 mem2 (b + HEAD) l).
{ apply (fsr_zbytes_copy W2 W3 memT mem2 p (b + HEAD) old (Z.min k n) HZT ltac:(lia) ltac:(lia)).
  intros i Hi.
  replace (b + HEAD + i) with (b + (HEAD + i)) by lia. replace (p + i) with (p - HEAD + (HEAD + i)) by lia.
  exact (CPY (HEAD + i) ltac:(unfold HEAD in *; lia)). }
(* ---- the resume at 0x82cf0 (FSW_rres.fsw_resume_after_rtU_args_chunks) ---- *)
assert (P2 : getr regs2 2 = getr regsT 2) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs2 8 = getr regsT 8) by exact (HP 8 ltac:(unfold acallee_saved; lia)).
set (xs := fsr_xsB regs k cnt fail (live - k) peak).
set (E2 := Ereg regs2 (fs_extraT ++ xs)).
assert (E2_2 : bv_unsigned (ew E2 2) = spZ regs - 32)
  by (unfold E2; rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl), P2; unfold spZ in Tsp; exact Tsp).
assert (E2_10 : bv_unsigned (ew E2 10) = b)
  by (unfold E2; rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl), R10; unfold w64; apply unsigned_lit_small;
      unfold HEAD in *; lia).
assert (EX2 : forall j w, nth j (fs_extraT ++ xs) (Z_to_bv 64 0) = w -> ew E2 (32 + j) = w)
  by (intros j w Hw; unfold E2; rewrite ew_Ereg_extra; exact Hw).
assert (KEEPF : forall x, spZ regs - 32 <= x < spZ regs ->
  aview tfibsegs (w_H W3) (unpoison (U1 ++ U2) mem2) x = aview tfibsegs (w_H W2) (unpoison (U1 ++ U2) memT) x).
{ intros x Hx. apply (proj1 HK); lia. }
assert (VK : forall a v, spZ regs - 32 <= a -> a + 8 <= spZ regs ->
  val_mem tfibsegs (mrestrict (w_H W2) memT) a 8 v -> val_mem tfibsegs (mrestrict (w_H W3) mem2) a 8 v).
{ intros a v Ha1 Ha2 Hv.
  apply (fsrCD_val_keep B ly S ly2 S2 (U1 ++ U2) W2 W3 memT mem2 md2 md3 a 8 v HARU HARU2);
    [ intros x Hx; apply KEEPF; cbn [Z.of_nat] in Hx; lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | exact Hv ]. }
assert (CK : forall (j : nat) (r : bv 5) (off a : Z),
  nth j (fs_extraT ++ xs) (Z_to_bv 64 0) = getr regs r -> spZ regs - 32 + off = a ->
  spZ regs - 32 <= a -> a + 8 <= spZ regs ->
  val_mem tfibsegs (mrestrict (w_H W2) memT) a 8 (bv_unsigned (getr regs r)) ->
  YP09.chunk_ok tfibsegs E2 (mrestrict (w_H W3) mem2) (spZ regs - 32)
    (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros j r off a Hnth Hoff Hlo Hhi Hv.
  apply (chunk_ok_val tfibsegs E2 _ (spZ regs - 32) off 8 (SOff (32 + j) 0) (bv_unsigned (getr regs r))).
  - rewrite fsw_SOff0, (EX2 j _ Hnth), Z_to_bv_bv_unsigned. reflexivity.
  - pose proof (u64_range (getr regs r)). cbn [Z.of_N]. lia.
  - cbn [Z.of_N]. lia.
  - cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. rewrite Hoff. apply VK; assumption. }
assert (Hck : Forall (YP09.chunk_ok tfibsegs E2 (mrestrict (w_H W3) mem2) (spZ regs - 32)) fsr_cs).
{ unfold fsr_cs. repeat apply Forall_cons; try apply Forall_nil.
  - apply (CK 8%nat 18%bv 0 (spZ regs - 32)); first [reflexivity | lia | exact V18].
  - apply (CK 7%nat 9%bv 8 (spZ regs - 24)); first [reflexivity | lia | exact V9].
  - apply (CK 6%nat 8%bv 16 (spZ regs - 16)); first [reflexivity | lia | exact V8].
  - apply (CK 5%nat 1%bv 24 (spZ regs - 8)); first [reflexivity | lia | exact V1]. }
assert (Hrs : Forall (region_ok tfibsegs E2 (mrestrict (w_H W3) mem2)) fs_pstat_regions)
  by exact (fsr_pstat_ok W3 regs2 mem2 (live - k) peak (cnt + 1) fail
    ([getr regs 1; getr regs 8; getr regs 9; getr regs 18] ++ [Z_to_bv 64 k]) GA).
assert (Hpdj : pairwise_disjoint E2 (fsT_ret_regions 32 fsr_cs fs_pstat_regions)).
{ apply pairwise_disjoint_of_extents.
  unfold fsT_ret_regions, fs_pstat_regions, fs_got_region, fs_bcell_region, fstk_ret, fs_pstat_region, extent_of_region.
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E2_2.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address,
    G_COUNT, G_FAIL, G_LIVE, G_PEAK in *.
  cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia | lia]. }
assert (HS0 : st_ok tfibsegs E2 (fss_retT A_fuzz_realloc_raB 32 fsr_cs fs_pstat_regions [])
  (restrict (w_H W3) (mkst regs2 (Z_to_bv 64 A_fuzz_realloc_raB) mem2 (seg_rom tfibsegs)))).
{ apply (fsw_resume_after_rtU_args_chunks B STK_fuzz_realloc (spZ regs) (fsr_FPc p k) ly S W (unpoison U mem) md []
    ly2 S2 (U1 ++ U2) W3 mem2 md3 3 regs2 32 xs fsr_cs fs_pstat_regions [] A_fuzz_realloc_raB).
  all: first
    [ solve [exact FS_GOT] | solve [exact FS_CELL] | solve [exact HJc] | solve [exact HARU2]
    | solve [exact Hck] | solve [exact Hrs] | solve [exact Hpdj]
    | solve [lazymatch goal with |- atoms_ok _ _ => first [exact I | constructor] end]
    | solve [lazymatch goal with |- spZ _ = _ => unfold spZ; rewrite P2; unfold spZ in Tsp; rewrite Tsp; reflexivity end]
    | solve [lazymatch goal with |- regions_wf _ = true => vm_compute; reflexivity end]
    | solve [lazymatch goal with |- _ mod _ = _ => reflexivity end]
    | solve [lia] ]. }
(* the write windows of every run of this stretch: the frame (stack arm) and the statics *)
assert (A1 : forall ss, skeleton (ss_mem ss) =
    skeleton (ss_mem (fss_retT A_fuzz_realloc_raB 32 fsr_cs fs_pstat_regions [])) ->
  awr_ok tfibsegs B E2 (ss_mem ss) STK_fuzz_realloc (spZ regs) (fsr_FPc p k) (ablocks B ly S) (ablocks B ly2 S2)
    ly2 [] (frames S))
  by (intros ss Hsk; exact (fsr_awr_skel B E2 _ (ss_mem ss) STK_fuzz_realloc (spZ regs) (fsr_FPc p k)
        (ablocks B ly S) (ablocks B ly2 S2) ly2 [] (frames S)
        (fsw_awr_retTS B IMG E2 A_fuzz_realloc_raB 32 STK_fuzz_realloc (spZ regs) fsr_cs [] (fsr_FPc p k)
           (ablocks B ly S) (ablocks B ly2 S2) ly2 [] (frames S) E2_2 ltac:(rewrite FR; lia) (fsr_pstat_FPc p k)) Hsk)).
(* no run of this stretch writes a byte of the new block *)
assert (NWB : forall rs, skeleton rs = skeleton (ss_mem (fss_retT A_fuzz_realloc_raB 32 fsr_cs fs_pstat_regions [])) ->
  forall a, b + HEAD <= a < b + HEAD + Z.min k n -> ~ in_wrange E2 rs a).
{ intros rs Hsk a Ha. apply (fsrCD_nw E2 rs a A_fuzz_realloc_raB Hsk).
  - rewrite E2_2. lia.
  - exact (NIMG a ltac:(lia)). }
assert (Klo : 0 <= b + HEAD) by lia.
assert (Khi : b + HEAD + Z.min k n <= 2 ^ 64) by lia.
(* ---- 0x82cf0 `beqz a0`: the NULL arm is dead (4096 <= a0 = b) ---- *)
fsw_aj_runU fsr_tbl_ok HS0 HJc HARU2.
{ apply A1. lazymatch goal with |- skeleton _ = skeleton _ => vm_compute; reflexivity end. }
lazymatch type of HF with frame_of _ ?rs _ _ =>
  assert (Hsk1 : skeleton rs = skeleton (ss_mem (fss_retT A_fuzz_realloc_raB 32 fsr_cs fs_pstat_regions [])))
    by (vm_compute; reflexivity) end.
pose proof (fsr_KB_run E2 _ (w_H W3) _ _ (b + HEAD) (b + HEAD + Z.min k n) HF Klo Khi (NWB _ Hsk1)) as KR1.
clear Hsk1.
clear HF HFr HG.
eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 10 0) (b := SLit 0) (1 := HS0).
1: { intros Hb' _. exfalso.
     rewrite branch_eq_U, U_SOff, E2_10, Z.add_0_r, (U_lit E2 0 ltac:(lia)) in Hb'.
     rewrite zcanon_id in Hb' by (unfold M64; lia). apply Z.eqb_eq in Hb'. lia. }
intros _ HS1. clear HS0.
(* ---- a1 = n, the epilogue, `j own`: stops at own's entry 0x82acc ---- *)
fsw_aj_runU fsr_tbl_ok HS1 HJc HARU2.
{ apply A1. lazymatch goal with |- skeleton _ = skeleton _ => vm_compute; reflexivity end. }
lazymatch type of HF with frame_of _ ?rs _ _ =>
  assert (Hsk2 : skeleton rs = skeleton (ss_mem (fss_retT A_fuzz_realloc_raB 32 fsr_cs fs_pstat_regions [])))
    by (vm_compute; reflexivity) end.
pose proof (fsr_KB_run E2 _ (w_H W3) _ _ (b + HEAD) (b + HEAD + Z.min k n) HF Klo Khi (NWB _ Hsk2)) as KR2.
clear Hsk2.
clear HF HFr HG.
rewrite ?wvb_collapse in HJc, HARU2.
assert (Z2 : zbytes_at tfibsegs W3 (ms_mem ms0) (b + HEAD) l).
{ unfold zbytes_at in *.
  exact (fsr_garr8_KB (w_H W3) mem2 (ms_mem ms0) (b + HEAD) l (b + HEAD) (b + HEAD + Z.min k n)
    (fsr_KB_trans _ _ _ _ _ _ KR1 KR2) ltac:(lia) ltac:(rewrite Hll; lia) Z1). }
(* ---- the tail call into own ---- *)
pose proof HS1 as HS1c. destruct HS1c as (_ & _ & _ & _ & _ & _ & _ & HM5 & _).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W3) E2 _ ms0 HS1 eq_refl) as Hshape.
assert (E2_37 : ew E2 37 = getr regs 1) by exact (EX2 5%nat _ eq_refl).
assert (E2_38 : ew E2 38 = getr regs 8) by exact (EX2 6%nat _ eq_refl).
assert (E2_39 : ew E2 39 = getr regs 9) by exact (EX2 7%nat _ eq_refl).
assert (E2_40 : ew E2 40 = getr regs 18) by exact (EX2 8%nat _ eq_refl).
assert (T1' : getr (ms_regs ms0) 1 = getr regs 1).
{ apply bv_eq. rewrite (fsw_reg_off _ E2 _ ms0 1%bv 37 0 (bv_unsigned (getr regs 1)) HS1 ltac:(vm_compute; reflexivity)
    ltac:(rewrite E2_37; reflexivity) ltac:(pose proof (u64_range (getr regs 1)); lia)). lia. }
assert (T8' : getr (ms_regs ms0) 8 = getr regs 8).
{ apply bv_eq. rewrite (fsw_reg_off _ E2 _ ms0 8%bv 38 0 (bv_unsigned (getr regs 8)) HS1 ltac:(vm_compute; reflexivity)
    ltac:(rewrite E2_38; reflexivity) ltac:(pose proof (u64_range (getr regs 8)); lia)). lia. }
assert (T9' : getr (ms_regs ms0) 9 = getr regs 9).
{ apply bv_eq. rewrite (fsw_reg_off _ E2 _ ms0 9%bv 39 0 (bv_unsigned (getr regs 9)) HS1 ltac:(vm_compute; reflexivity)
    ltac:(rewrite E2_39; reflexivity) ltac:(pose proof (u64_range (getr regs 9)); lia)). lia. }
assert (T18' : getr (ms_regs ms0) 18 = getr regs 18).
{ apply bv_eq. rewrite (fsw_reg_off _ E2 _ ms0 18%bv 40 0 (bv_unsigned (getr regs 18)) HS1 ltac:(vm_compute; reflexivity)
    ltac:(rewrite E2_40; reflexivity) ltac:(pose proof (u64_range (getr regs 18)); lia)). lia. }
assert (Tsp' : spZ (ms_regs ms0) = spZ regs).
{ unfold spZ at 1. rewrite (fsw_reg_off _ E2 _ ms0 2%bv 2 32 (spZ regs - 32) HS1 ltac:(vm_compute; reflexivity) E2_2
    ltac:(unfold spZ in *; pose proof (bv_unsigned_in_range _ (getr regs 2)); lia)). lia. }
assert (T10' : getr (ms_regs ms0) 10 = w64 b).
{ rewrite (fsw_reg_atom (w_H W3) regs2 (fs_extraT ++ xs) _ ms0 10%bv 10%bv 10 HS1 ltac:(vm_compute; reflexivity) eq_refl).
  exact R10. }
assert (T11' : getr (ms_regs ms0) 11 = w64 n).
{ rewrite (fsw_reg_atom (w_H W3) regs2 (fs_extraT ++ xs) _ ms0 11%bv 8%bv 8 HS1 ltac:(vm_compute; reflexivity) eq_refl).
  rewrite P8. exact T8. }
assert (TP : aregs_preserved regs (ms_regs ms0)).
{ intros r Hcs.
  assert (Hr : In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]) by (cbn; unfold acallee_saved in Hcs; lia).
  repeat (destruct Hr as [<- | Hr]); [..| destruct Hr].
  all: first
    [ solve [apply bv_eq; change (bv_unsigned (getr (ms_regs ms0) (Z_to_bv 5 2)) = bv_unsigned (getr regs (Z_to_bv 5 2)));
             exact Tsp']
    | solve [exact T8'] | solve [exact T9'] | solve [exact T18']
    | solve [lazymatch goal with |- getr _ (Z_to_bv 5 ?z) = _ =>
        let k := eval vm_compute in (Z.to_nat z) in
        transitivity (getr regs2 (Z_to_bv 5 z));
        [ exact (fsw_reg_atom (w_H W3) regs2 (fs_extraT ++ xs) _ ms0 (Z_to_bv 5 z) (Z_to_bv 5 z) k HS1
                   ltac:(vm_compute; reflexivity) eq_refl)
        | transitivity (getr regsT (Z_to_bv 5 z));
          [ exact (HP z ltac:(unfold acallee_saved; lia))
          | first
              [ solve [exact (proj1 HKP z ltac:(lia))]
              | solve [etransitivity; [exact (proj1 (proj2 HKP)) | symmetry; exact Hgp]]
              | solve [etransitivity; [exact (proj2 (proj2 HKP)) | symmetry; exact Htp]] ] ] ] end] ]. }
assert (Tgp' : getr (ms_regs ms0) 3 = w64 (as_gp B))
  by (transitivity (getr regs 3); [exact (TP 3 ltac:(unfold acallee_saved; lia)) | exact Hgp]).
assert (Ttp' : getr (ms_regs ms0) 4 = w64 (as_tp B))
  by (transitivity (getr regs 4); [exact (TP 4 ltac:(unfold acallee_saved; lia)) | exact Htp]).
(* the statics at own's entry *)
assert (G5 : fs_glob tfibsegs W3 (ms_mem ms0) (live - k) peak (cnt + 1) fail).
{ apply (fs_glob_of_TS E2 W3 _ _ (live - k) peak (cnt + 1) fail (SOff 35 0) (SOff 36 0) (SOff 33 0) (SOff 34 0) HM5).
  all: first
    [ solve [lazymatch goal with |- fs_pstat_find _ _ = Some _ => vm_compute; reflexivity end]
    | solve [rewrite fsw_SOff0; exact (EX2 3%nat _ eq_refl)]
    | solve [rewrite fsw_SOff0; exact (EX2 4%nat _ eq_refl)]
    | solve [rewrite fsw_SOff0; exact (EX2 1%nat _ eq_refl)]
    | solve [rewrite fsw_SOff0; exact (EX2 2%nat _ eq_refl)]
    | solve [lia] ]. }
(* own's fpreU: the caller's journal at o = 0, the read-only view kept, the caller's chain kept (above sp0) *)
pose proof HJc as (_ & HlyJ & _ & _ & _ & _ & _ & _ & HkeepJ & _).
pose proof HlyJ as (_ & _ & _ & _ & _ & _ & _ & _ & Etop2 & _).
assert (HRO5 : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W3) (ms_mem ms0)))
  by exact (arodata_kept B STK_fuzz_realloc (spZ regs) (fsr_FPc p k) ly S U W mem md ly2 S2 (U1 ++ U2) W3 (ms_mem ms0) _ 3
    HJc HARU0 (proj1 (proj2 HARU2)) (proj2 (proj2 HARU2)) (fsrCD_FPc_sink p k ltac:(lia))
    (fsrCD_FPc_not_ro B ly S W (unpoison U mem) md p k HAR Hblk) HRO).
assert (Hch5 : achain ly2 (aview tfibsegs (w_H W3) (unpoison (U1 ++ U2) (ms_mem ms0))) (spZ (ms_regs ms0))
  (s0Z (ms_regs ms0)) ch).
{ rewrite Tsp'. unfold s0Z. rewrite T8'. fold (s0Z regs).
  apply (achain_ly_top ly ly2 _ _ _ _ Etop2).
  apply (achain_kept ly _ _ _ _ _ (spZ regs) Hch ltac:(lia) ltac:(lia)).
  intros a Ha. apply HkeepJ; [lia | lia]. }
assert (HPRE5 : fpreU tfibsegs B STK_own ly2 S2 (U1 ++ U2) W3 (ms_regs ms0) (ms_mem ms0) _ ch)
  by exact (fsw_fpreU_atFP B STK_fuzz_realloc (spZ regs) (fsr_FPc p k) ly S (U1 ++ U2) W (unpoison U mem) md [] ly2 S2 W3
    (ms_mem ms0) _ 3 (ms_regs ms0) STK_own 0 ch HJc HARU2 HRO5 ltac:(lia) eq_refl ltac:(lia) FRo0 ltac:(lia)
    ltac:(rewrite T1'; exact Hra) ltac:(unfold raZ; rewrite T1'; exact Hra4) Tgp' Ttp' Hch5).
rewrite Hshape.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdg) ?Qg =>
  change (SRr tfibsegs W3 (cfg_at tfibsegs A_own (ms_regs ms0) (ms_mem ms0) mdg) Qg) end.
eapply SRr_mono.
{ apply (OWN ly2 S2 (U1 ++ U2) W3 (ms_regs ms0) (ms_mem ms0) _ ch b n (live - k) peak (cnt + 1) fail HPRE5 FH12b).
  all: first
    [ solve [exact T10'] | solve [exact T11'] | solve [exact Hnew] | solve [exact Hnin] | solve [exact Hb16]
    | solve [exact Hb4096] | solve [exact Hn1] | solve [exact HnM] | solve [exact G5]
    | solve [lazymatch goal with |- range_addressable _ _ _ _ =>
               pose proof (fmB_block_addressable B ly2 S2 (U1 ++ U2) W3 (ms_mem ms0) _ b (n + HEAD) HARU2 FH12b Hnew Hnin)
                 as RA;
               rewrite Hrq in RA; exact RA end]
    | solve [lazymatch goal with |- _ < 2 ^ 64 - HEAD => unfold HEAD in *; lia end]
    | solve [lia] ]. }
intros W' c' _ HQ.
unfold fsr_post_c. exists (b + HEAD).
replace (b + HEAD - HEAD) with b by lia.
rewrite (app_assoc U1 U2).
unfold apost_baseU in HQ |- *.
refine (fsrCD_tail_post B STK_fuzz_realloc (spZ regs) (fsr_FPc p k) regs ly S U W mem md 3 ly2 S2 (U1 ++ U2) W3
  (ms_mem ms0) _ (ms_regs ms0) STK_own (FS_PSTAT_FP ++ [(b, b + 8)]) 0 3 _ _ _ HJc Tsp' FRo T1' TP eq_refl _ _ W' c' HQ).
- (* own's footprint: the caller's statics, and the new head (the old block's, or a block the caller's realloc made) *)
  intros a (r & Hr & Ha). apply in_app_or in Hr as [Hr | Hr].
  + right. right. assert (Hp : inFP FS_PSTAT_FP a) by (exists r; split; assumption).
    split; [exact (fsr_pstat_FPc p k a Hp) | exact (fs_pstat_img a Hp)].
  + destruct Hr as [Ep | []]. rewrite <- Ep in Ha. cbn [fst snd] in Ha.
    destruct (Z.eq_dec b (p - HEAD)) as [Eb | Nb].
    * left. split.
      -- exists (p - HEAD, p - HEAD + req_size (k + HEAD)). split;
           [ unfold fsr_FPc, ablocks_fp; apply in_or_app; right; cbn [map fst snd]; left; reflexivity
           | cbn [fst snd]; rewrite Hrqk; unfold HEAD in *; lia ].
      -- exists b, (n + HEAD). split; [exact Hnew | rewrite Hrq; unfold HEAD in *; lia].
    * right. left. exists b, (n + HEAD). split; [exact Hnew|].
      split; [|rewrite Hrq; unfold HEAD in *; lia].
      intros Hin. rewrite Eb1 in Hin. apply in_app_or in Hin as [Hx|[Hx|Hx]].
      -- apply HFRESH. apply in_or_app. left. exact Hx.
      -- injection Hx as Hx1 _. exact (Nb (eq_sym Hx1)).
      -- apply HFRESH. apply in_or_app. right. exact Hx.
- (* own's post into arm (c) at res = b + HEAD *)
  intros ly' S' W'' regs' mem' md' HJ1 OK PO HQ1. cbv beta in HQ1.
  destruct HQ1 as (Q10 & Qbl & Qfh & Qrb & Qra & Qgl).
  split; [exact Q10|].
  split; [unfold HEAD in *; lia|].
  split; [exists b1, b2, (b1 ++ b2), []; split; [exact Eb1|]; split; [rewrite Qbl, Eb2; reflexivity | apply app_nil_r]|].
  split; [exact Qfh|].
  split; [intros _; exact Qrb|].
  split; [|exact Qgl].
  (* the kept bytes across own: off own's footprint, in a block own keeps *)
  pose proof HJ1 as (HAR' & _ & _ & _ & _ & _ & _ & _ & _ & HBK & _).
  assert (HARU' : ARU tfibsegs B ly' S' ((U1 ++ U2) ++ [(b, HEAD)]) W'' mem' md') by (split; [exact HAR' | split; assumption]).
  assert (Hnew' : In (b, n + HEAD) (ablocks B ly' S')) by (rewrite Qbl; exact Hnew).
  pose proof (fsr_zbytes_copy W3 W'' (ms_mem ms0) mem' (b + HEAD) (b + HEAD) l (Z.of_nat (length l)) Z2
    ltac:(lia) ltac:(rewrite Nat2Z.id; lia)) as ZC.
  rewrite Nat2Z.id, firstn_all in ZC. apply ZC.
  intros i Hi. rewrite Hll in Hi.
  destruct (HAPPB (b + HEAD + i) ltac:(unfold HEAD in *; lia)) as [Hx64 Hxa].
  rewrite <- (fsrCD_app_view B ly' S' _ W'' mem' md' (b + HEAD + i) HARU' Hx64 Hxa).
  rewrite <- (fsrCD_app_view B ly2 S2 (U1 ++ U2) W3 (ms_mem ms0) _ (b + HEAD + i) HARU2 Hx64 Hxa).
  replace (b + HEAD + i) with (b + (HEAD + i)) by lia.
  apply (HBK b (n + HEAD) (HEAD + i) Hnew Hnew' ltac:(rewrite Hrq; unfold HEAD in *; lia)).
  intros (r & Hr & Hrr). apply in_app_or in Hr as [Hr | Hr].
  + apply (NIMG (b + (HEAD + i)) ltac:(unfold HEAD in *; lia)). exists r. split; assumption.
  + destruct Hr as [<- | []]. cbn [fst snd] in Hrr. unfold HEAD in *. lia.
Qed.
End s.
