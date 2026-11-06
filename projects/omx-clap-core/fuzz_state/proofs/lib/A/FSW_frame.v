(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img's image range set to libreac/fuzz_boxreg's own (Reusable/YImgTop.v IMG_LO, IMG_TOP). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Reusable/YCbq.v, with its module paths and module names changed; 234 of its 311 lines of code are new or changed and 2885 lines of the source are left out. *)
(* The fake-frame call steps of the walk kit for fs's ASan program part over fs.asan (image tfibsegs), in the U form
   (FSupoison.unpoison: the user-poisoned shadow bytes of U read as 0, FSupoisonU's ARU): the journal transfer across
   the call to __asan_stack_malloc_<cid> that grants a fake frame, and the epilogue flag store that releases it.
   A kit: no function's contract is proved here (rule 24). Owner: lane CRT (a Theorem Labs lane), per the walk-kit layout
   (a Theorem Labs lane 22:01Z): FSW_K.v keeps the entry states, run steps, realign and runtime-call steps; this file holds
   fsw_stack_malloc_atU, fsw_flag_storeU and fsw_flag_addr_ge4096 only; FSW_ret.v holds the return side.

   Port-from: cgif's S-form originals, origin/ossv/recipes proofs/cgif/cgif_file_fuzzer/lib/YCbq.v:1748
   `aj_stack_malloc_at` and :2361 `aj_flag_store` (same lemmas also at YCe5.v:1254 / :1867, YCbo.v, YC85.v, and
   cgif_rgb_fuzzer/lib/YC04.v). Rule 24, both discharges, against proof index v5 built 2026-10-28T21:58:24Z
   (main@e966c513ee6, ossv/recipes@566eb6ffa5d, ossv/candidates@ee89628c997, release/pau-projects-recipes@b6a0088adcb;
   "every branch is where the index read it"), status read from a file, not through a pipe: `proof-index
   __asan_stack_malloc_3` exits 0 and reports 0 file(s) NAMED for it and 382 that use its address; the same report lists
   omx-clap-core/fuzz_state among the units it did NOT address-search. `git grep` over origin/main, origin/ossv/recipes,
   origin/ossv/candidates and origin/release/pau-projects-recipes (2026-10-28 ~22:10Z) returns no line for
   `fsw_stack_malloc_atU`, `fsw_flag_storeU`, `aj_stack_malloc_atU`, `aj_flag_storeU` or `astack_malloc_realizesU`.
   The DONOR is the S-form pair above (cgif YCbq.v:1748 / :2361, on ossv/recipes); these U forms port it, and the released
   plain / UBSan fuzz_state trees on ossv/recipes are the structural template for fs's program part.
   Changed from the donor: the journal and the state invariant run over `unpoison U mem` with `ARU` carried beside them,
   as FSW_K.v's own U twins do (fsw_after_callU, fsw_exec_U); the callee contract is FSupoisonU's `astack_malloc_realizesU`
   (ecall_preU, ARU in its post) instead of YG0d's `astack_malloc_realizes`; the premise order is FSW_K's (the journal,
   then ARU). The statements are FP-generic: FP is a parameter and no clause fixes it. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSW_K.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the engine's laws the donor's steps ask for; proved for fs in FSW_K.v, not assumed here *)
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
(* the unit's own hypotheses: a kit proves no contract (rule 24) *)
Hypothesis errno_low : api_env tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis stack_malloc_progress : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.

(* ---- the call that grants a fake frame: __asan_stack_malloc_<cid> ----
   The U twin of YCbq.v:1748 aj_stack_malloc_at. The caller's journal and the frame's state invariant run over the
   unpoisoned reading of the machine's memory; the engine's configuration is the machine's own memory memT. *)
Lemma fsw_stack_malloc_atU : forall cid, astack_malloc_realizesU tfibsegs B cid -> 0 <= cid <= 10 ->
  forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc U mdc k (o : Z) raw,
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U memT) mdc k ->
  ARU tfibsegs B lyc Sc U W memT mdc ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  count_cid cid (frames Sc) < fs_frames cid ->
  SRr tfibsegs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_stack_malloc (as_code B) cid)) memT (seg_rom tfibsegs)) mdc)
  (fun W2 c2 => W2 = W /\ exists S2 regs2 mem2 md2 pos,
    c2 = mkCfg (mkst regs2 raw mem2 (seg_rom tfibsegs)) md2 /\
    ajournal tfibsegs B STK sp0 FP ly S W0 mem md ((cid, pos) :: own) lyc S2 W (unpoison U mem2) md2 k /\
    ARU tfibsegs B lyc S2 U W mem2 md2 /\
    aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (frame_addr lyc cid pos) /\
    ablocks B lyc S2 = ablocks B lyc Sc /\ frames S2 = (cid, pos) :: frames Sc /\ ~ In (cid, pos) (frames Sc) /\
    st_nev S2 = st_nev Sc /\ blocks_bytes S2 = blocks_bytes Sc /\
    zero_shadow (aview tfibsegs (w_H W) mem2) SHADOW_OFF (frame_addr lyc cid pos) (fs_frame_bytes cid) /\
    rdword (aview tfibsegs (w_H W) mem2) (frame_addr lyc cid pos + fs_frame_bytes cid - 8)
      = Some (flag_addr lyc cid pos) /\
    acall_kept tfibsegs B lyc Sc W (unpoison U memT) W (unpoison U mem2) (sp0 + o - ESTACK) (sp0 + o) (fun _ => False)).
Proof.
intros cid ASM Hcid W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc U mdc k o raw
  HJ HARU Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hcnt.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity. assert (ESTACK = 4096) as Hes by reflexivity.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ESTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
  all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
(* ecall_preU: ecall_pre over the unpoisoned memory (which is exactly the journal's memory) plus U's own invariants *)
assert (HPRE : ecall_preU tfibsegs B lyc Sc U W regsT memT mdc).
{ split.
  - split; [exact HAR|]. split; [rewrite Hra; exact Hraw|]. split; [destruct HstkC as (Q1 & _); exact Q1|].
    split; [rewrite Eslo, Hsp'; zlia|]. split; [rewrite Eshi, Hsp'; zlia|].
    split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|]. split; [exact Hgp | exact Htp].
  - split; [exact (ARU_ok tfibsegs B lyc Sc U W memT mdc HARU)
           | exact (ARU_poisoned tfibsegs B lyc Sc U W memT mdc HARU)]. }
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
destruct (stack_malloc_progress Sc cid HWF Hcid Hcnt) as (pos & S2 & Hpath).
pose proof (ml_stack_malloc _ ML Sc cid HWF Hcid) as HTOK.
destruct (atok_apath _ _ _ [] (PFake cid pos, S2) HTOK Hpath) as (ns' & HQ). unfold stack_malloc_post in HQ.
destruct HQ as (HWF2 & (f & ES2) & _ & Hpos & Hfrs2 & Hfresh).
eapply SRr_mono; [exact (ASM lyc Sc U W regsT memT mdc pos S2 HPRE Hcnt Hpath)|].
cbv beta. intros W2 c2 HwleW (-> & regs2 & mem2 & md2 & -> & HARU2 & Hres & Hsame & Hreg10 & Hz & Hflag & Hfpres & Hfr & Hpres2).
assert (Hblk : blocks S2 = blocks Sc) by (rewrite ES2; reflexivity).
assert (Eab2 : ablocks B lyc S2 = ablocks B lyc Sc) by (unfold ablocks; rewrite Hblk; reflexivity).
assert (Hnev2 : st_nev S2 = st_nev Sc) by (rewrite ES2; reflexivity).
assert (Hbb : blocks_bytes S2 = blocks_bytes Sc) by (rewrite ES2; reflexivity).
assert (Hsecs2 : st_secs S2 = st_secs Sc) by (rewrite ES2; reflexivity).
(* the new state's AR is ARU's, i.e. over the unpoisoned memory *)
pose proof (ARU_AR tfibsegs B lyc S2 U W mem2 md2 HARU2) as HAR2.
(* the callee kept the memory outside the frame and the stack window, as read through U *)
assert (HfrU : forall a, 0 <= a < 2 ^ 64 -> ~ aowned B lyc Sc a -> ~ aowned B lyc S2 a ->
  ~ (spZ regsT - ESTACK <= a < spZ regsT) ->
  aview tfibsegs (w_H W) (unpoison U mem2) a = aview tfibsegs (w_H W) (unpoison U memT) a).
{ intros a Ha H1 H2 H3. destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:E.
  - apply (aview_unpoison_in tfibsegs (w_H W) U mem2 memT a E).
  - rewrite !(aview_unpoison_out tfibsegs (w_H W) U _ a E). exact (Hfr a Ha H1 H2 H3). }
assert (HpresU : forall a, spZ regsT - ESTACK <= a < spZ regsT -> apresent (w_H W) (unpoison U mem2) a).
{ intros a Ha. apply (fsw_apresent_poison B lyc S2 U W mem2 md2 a HARU2).
  - unfold SHADOW_OFF, kHighMemBeg in *. rewrite Hsp' in Ha. zlia.
  - exact (Hpres2 a Ha). }
assert (HJ1 : ajournal tfibsegs B ESTACK (spZ regsT) [] lyc Sc W (unpoison U memT) mdc [(cid, pos)] lyc S2 W
  (unpoison U mem2) md2 0).
{ eapply (call_effect_journal tfibsegs B LAWS fs_segs_low errno_low ESTACK lyc Sc W regsT (unpoison U memT) mdc lyc S2 W
    (unpoison U mem2) md2 (fun _ => False) [] [(cid, pos)] 0);
  [exact HAR2 | apply layout_le_refl | apply wle_refl | apply same_io_materialized; exact Hsame | | exact HpresU | exact HAR | exact HstkC
  | cbn; exact Hfrs2 | zlia | zlia | rewrite Hsecs2; zlia | intros a [] | | ].
  - intros a H0 H1 H2 H3 _. apply (HfrU a H0 H1 H2). intros H. apply H3. left. exact H.
  - intros p n i Hp Hnp. exfalso. apply Hnp. rewrite Eab2. exact Hp.
  - rewrite ES2. apply (qtight_ext Sc); [reflexivity | reflexivity | reflexivity | exact HQT]. }
split; [reflexivity|]. exists S2, regs2, mem2, md2, pos.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. replace k with (k + 0) by zlia. change ((cid, pos) :: own) with ([(cid, pos)] ++ own).
  eapply (ajournal_sub tfibsegs B LAWS fs_segs_low); [exact HJ | exact HJ1 | zlia | zlia | intros a (rg & [] & _)]. }
split; [exact HARU2|].
split; [exact Hres|]. split; [exact Hreg10|]. split; [exact Eab2|]. split; [exact Hfrs2|]. split; [exact Hfresh|].
split; [exact Hnev2|]. split; [exact Hbb|]. split; [exact Hz|]. split; [exact Hflag|].
(* Discharged per goal rather than by a positional list: RELOC's FP-keyed YCbq gives acall_kept_of_journal a sixth
   premise (image bytes are not in FP1, YCbq.v:984-991 on 4aa3d96b823), so a fixed bracket list fits one base and
   breaks the other. Every goal here is one of the two journal facts or is vacuous on FP1 = []. *)
rewrite Hsp' in HJ1. eapply (acall_kept_of_journal tfibsegs B fs_segs_low);
  (* each alternative must CLOSE its goal: an intro pattern can match the wrong goal and leave subgoals behind, so a
     bare `first` would pick it and stop (a Theorem Labs lane's RELOC build, 23:40Z) *)
  first [ solve [exact HJ1]
        | solve [exact HAR]
        | solve [exact sink_closed_nil]
        | solve [intros b m i Hb Hi _; rewrite Eab2; exact Hb]
        | solve [intros a (rg & [] & _)]
        | solve [intros a _ (rg & [] & _)] ].
Qed.

(* ---- re-adding a live fake frame's two regions to a symbolic state that lost them ----
   An after-call state (FSW_K's fss_ret_s0) holds only the s0 region, so a fake-frame caller must put back the frame
   [0, bytes) at the atom holding its address (chunks cs) and its shadow [0, bytes / 8) at the atom holding its shadow
   address. Both are present and not runtime-owned (AR_frames_law, Reusable/YG0d.v:446-454), hence no shadow byte of U
   (FSupoison ush_facts) and writable on the machine's memory; in bounds by YCbq.frames_bounds.
   Ported from: a Theorem Labs lane's starved lane, a working branch 6ff9f5bc4f4,
   lib/A/FSH_check_reject_clean_starved.v:187-249 (crcs_unpoison_notowned, crcs_apresent_notowned,
   crcs_readd_frame_regions), handed over for the kit so the six fake-frame walks share one copy. Changed: crcs_* ->
   fsw_*, the redundant `forall B` dropped (this Section already fixes B), and st_ok_add_region' qualified as
   YI0n.st_ok_add_region'. The proofs are a Theorem Labs lane's text. *)
Lemma fsw_unpoison_notowned : forall ly S U (W : world tfibsegs) mem md a,
  ARU tfibsegs B ly S U W mem md -> 0 <= a < 2 ^ 64 -> ~ aowned B ly S a ->
  unpoison U mem (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof.
intros ly S U W mem md a H Ha Hno. apply unpoison_out. rewrite (wz a Ha).
destruct (in_ush U a) eqn:E; [|reflexivity]. exfalso. exact (Hno (proj1 (ush_facts tfibsegs B ly S U W mem md a H E))).
Qed.
Lemma fsw_apresent_notowned : forall ly S U (W : world tfibsegs) mem md a,
  ARU tfibsegs B ly S U W mem md -> 0 <= a < 2 ^ 64 -> ~ aowned B ly S a ->
  apresent (w_H W) (unpoison U mem) a -> apresent (w_H W) mem a.
Proof.
intros ly S U W mem md a H Ha Hno (Hh & b & Hb). split; [exact Hh|]. exists b.
rewrite <- (fsw_unpoison_notowned ly S U W mem md a H Ha Hno). exact Hb.
Qed.
Lemma fsw_readd_frame_regions : forall ly S U (W : world tfibsegs) md E ss ms cid pos nF nS cs,
  ARU tfibsegs B ly S U W (ms_mem ms) md -> In (cid, pos) (frames S) -> 0 <= cid ->
  st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  bv_unsigned (ew E nF) = frame_addr ly cid pos ->
  bv_unsigned (ew E nS) = shadow_addr (frame_addr ly cid pos) ->
  YP09.region_wf (YP09.mkRegion (Some nF) 0 (fs_frame_bytes cid) 0 (fs_frame_bytes cid) cs) = true ->
  YP09.region_wf (YP09.mkRegion (Some nS) 0 (fs_frame_bytes cid / 8) 0 (fs_frame_bytes cid / 8) []) = true ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms)) (frame_addr ly cid pos)) cs ->
  all_disjoint E (YP09.mkRegion (Some nS) 0 (fs_frame_bytes cid / 8) 0 (fs_frame_bytes cid / 8) []) (ss_mem ss) ->
  all_disjoint E (YP09.mkRegion (Some nF) 0 (fs_frame_bytes cid) 0 (fs_frame_bytes cid) cs)
    (YP09.mkRegion (Some nS) 0 (fs_frame_bytes cid / 8) 0 (fs_frame_bytes cid / 8) [] :: ss_mem ss) ->
  st_ok tfibsegs E
    (mkSS (ss_pc ss) (ss_regs ss)
       (YP09.mkRegion (Some nF) 0 (fs_frame_bytes cid) 0 (fs_frame_bytes cid) cs ::
        YP09.mkRegion (Some nS) 0 (fs_frame_bytes cid / 8) 0 (fs_frame_bytes cid / 8) [] :: ss_mem ss)
       (ss_resv ss) (ss_facts ss))
    (restrict (w_H W) ms).
Proof.
intros ly S U W md E ss ms cid pos nF nS cs H Hin Hc0 HS EF ES WF WS Hcs DS DF.
pose proof (ARU_AR tfibsegs B ly S U W (ms_mem ms) md H) as HAR.
destruct (al_frames _ _ LAWS ly S W (unpoison U (ms_mem ms)) md cid pos HAR Hin) as (_ & _ & Hfp & Hsp).
destruct (frames_bounds tfibsegs B LAWS ly S W (unpoison U (ms_mem ms)) md cid pos HAR Hin) as (H4096 & Hceil & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (fs_frame_bytes_pos cid Hc0) as Hfb.
set (F := frame_addr ly cid pos) in *.
pose proof (shadow_addr_bounds F ltac:(lia)) as (Hs1 & Hs2).
assert (Hs3 : shadow_addr F + fs_frame_bytes cid / 8 <= shadow_addr (F + fs_frame_bytes cid))
  by (apply shadow_range_end; lia).
pose proof (shadow_addr_bounds (F + fs_frame_bytes cid - 1) ltac:(lia)) as (_ & Hs4).
assert (Hs5 : shadow_addr (F + fs_frame_bytes cid) <= shadow_addr (F + fs_frame_bytes cid - 1) + 1)
  by (unfold shadow_addr; Z.div_mod_to_equations; lia).
(* the shadow region *)
assert (RS : region_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms))
  (YP09.mkRegion (Some nS) 0 (fs_frame_bytes cid / 8) 0 (fs_frame_bytes cid / 8) [])).
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite ES.
  split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o Ho. apply (apresent_writable tfibsegs).
  destruct (Hsp o Ho) as (Hp & Hno).
  exact (fsw_apresent_notowned ly S U W (ms_mem ms) md (shadow_addr F + o) H ltac:(lia) Hno Hp). }
pose proof (YI0n.st_ok_add_region' tfibsegs E ss (restrict (w_H W) ms) _ HS WS RS DS) as HS1.
(* the frame region *)
pose proof (YI0n.st_ok_add_region' tfibsegs E _ (restrict (w_H W) ms) _ HS1 WF) as HS2.
cbn [ms_mem restrict ss_mem ss_pc ss_regs ss_resv ss_facts] in HS2.
apply HS2; [|exact DF].
unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite EF.
split; [lia|]. split; [lia|]. split; [|exact Hcs].
intros o Ho. apply (apresent_writable tfibsegs).
destruct (Hfp (F + o) ltac:(lia)) as (Hp & Hno).
exact (fsw_apresent_notowned ly S U W (ms_mem ms) md (F + o) H ltac:(lia) Hno Hp).
Qed.

(* growth of the visible memory survives reading both sides through the same U: unpoison only ever turns a byte into
   Some 0, on both sides at once *)
Lemma fsw_mem_grows_unpoison : forall (H : word -> bool) U m m',
  mem_grows (mrestrict H m) (mrestrict H m') -> mem_grows (mrestrict H (unpoison U m)) (mrestrict H (unpoison U m')).
Proof.
intros H U m m' G x. specialize (G x). unfold mrestrict, unpoison in *.
destruct (H x); [exact G|]. destruct (in_ush U (bv_unsigned x)); [intros _; discriminate | exact G].
Qed.

(* ---- the epilogue store that releases the fake frame ----
   The U twin of YCbq.v:2361 aj_flag_store: the run ends with `sb zero, 0(a0)` on the frame's flag byte, which hands the
   frame back (frames S' = frames S minus this one, stack_free_state). The engine premises are on the machine's own
   memory; the journal runs over `unpoison U`, and ARU is carried to the continuation beside it. A user-poisoned byte of
   U is a live block's shadow byte, so it sits at or above SHADOW_OFF (FSupoison ush_facts), while the frame and its
   flag lie below alloc_ceiling (YCbq.frames_bounds) - the two never meet, which is why the release leaves U intact. *)
Lemma fsw_flag_storeU : forall tbl (tbl_ok : YP02.table_ok tfibsegs tbl) W n E ss ss' st ms STK sp0 FP ly S W0 mem md
  own' lyc Sc U mdc k cid pos Q,
  st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  sym_runN tfibsegs tbl n ss = (ss', st) ->
  match st with RS_ecall => False | _ => True end ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md ((cid, pos) :: own') lyc Sc W (unpoison U (ms_mem ms)) mdc k ->
  ARU tfibsegs B lyc Sc U W (ms_mem ms) mdc ->
  0 <= cid ->
  (forall a, in_wrange E (ss_mem ss) a ->
     awr_byte tfibsegs B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc ((cid, pos) :: own') (frames S) a
     \/ a = flag_addr lyc cid pos) ->
  (forall msr, st_ok tfibsegs E ss' msr -> mbyte tfibsegs (ms_mem msr) (flag_addr lyc cid pos) = Some (Z_to_bv 8 0)) ->
  (forall ms' mat',
     st_ok tfibsegs E ss' (restrict (w_H W) ms') ->
     ajournal tfibsegs B STK sp0 FP ly S W0 mem md own' lyc (stack_free_state cid pos Sc) W
       (unpoison U (ms_mem ms')) (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
     ARU tfibsegs B lyc (stack_free_state cid pos Sc) U W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) ->
     frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
     frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
     mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
     SRr tfibsegs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros tbl tbl_ok W n E ss ss' st ms STK sp0 FP ly S W0 mem md own' lyc Sc U mdc k cid pos Q
  HS Hrun Hst HJ HARU Hcid Hwr Hflag0 Hk.
destruct (msteps_run_gen tfibsegs tbl tbl_ok n E ss ss' st _ HS Hrun) as (msr' & Hms & HS'0 & Hfr).
assert (HS' : st_ok tfibsegs E ss' msr') by (destruct st; [exact HS'0 | destruct Hst | exact HS'0]). clear HS'0.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hkk & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (FFL lyc Sc W (unpoison U (ms_mem ms)) mdc cid pos HAR Hin) as (Hfp & Hfo & Hfr_rng & Hfr_num).
destruct (frames_bounds tfibsegs B LAWS lyc Sc W (unpoison U (ms_mem ms)) mdc cid pos HAR Hin) as (H4096 & Hceil & _).
destruct (al_flag _ _ LAWS lyc Sc W (unpoison U (ms_mem ms)) mdc cid pos HAR Hin) as (_ & _ & Hflapp & Hflc).
(* the flag byte is no user-poisoned byte of U. A byte of U is a live block's shadow byte, so it lies in
   [SHADOW_OFF, kHighMemBeg) (ush_facts); the flag is in application memory (AR_flag_law's in_app), which is either low
   (below kLowShadowBeg < SHADOW_OFF) or high (at or above kHighMemBeg) - on neither side of the shadow band. *)
assert (HflagU : in_ush U (bv_unsigned (Z_to_bv 64 (flag_addr lyc cid pos))) = false).
{ destruct (in_ush U (bv_unsigned (Z_to_bv 64 (flag_addr lyc cid pos)))) eqn:Eu; [|reflexivity]. exfalso.
  pose proof ASAN_CEIL_range as (Hc1 & _).
  unfold in_app in Hflapp.
  destruct Hflapp as (H0 & [Hlo | (Hhi & Hhc)]);
  rewrite (wz (flag_addr lyc cid pos) ltac:(unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia)) in Eu;
  pose proof (ush_facts tfibsegs B lyc Sc U W (ms_mem ms) mdc _ HARU Eu) as (_ & L1 & L2);
  unfold ASAN_CEIL, SHADOW_OFF, kHighMemBeg, kLowShadowBeg in *; lia. }
apply (SRr_msteps tfibsegs fs_wx W ms msr' mdc Q Hms).
intros model' Hsame Hcl.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows tfibsegs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
set (memc' := ms_mem (unrestrict (w_H W) (ms_mem ms) msr')) in *.
assert (Hfr' : forall x : word, ~ in_wrange E (ss_mem ss) (bv_unsigned x) ->
  mrestrict (w_H W) memc' x = mrestrict (w_H W) (ms_mem ms) x).
{ subst memc'. rewrite Hmm. exact Hfr. }
assert (Hgr' : mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) memc'))
  by (subst memc'; rewrite Hmm; exact Hgr).
assert (Heqw : forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange E (ss_mem ss) a ->
  aview tfibsegs (w_H W) memc' a = aview tfibsegs (w_H W) (ms_mem ms) a).
{ intros a Ha HWa. apply aview_eq_of. apply Hfr'. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by lia. exact HWa. }
(* the same equality through U's reading, which is what the journal runs over *)
assert (HeqwU : forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange E (ss_mem ss) a ->
  aview tfibsegs (w_H W) (unpoison U memc') a = aview tfibsegs (w_H W) (unpoison U (ms_mem ms)) a).
{ intros a Ha HWa. destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:Eu.
  - apply (aview_unpoison_in tfibsegs (w_H W) U memc' (ms_mem ms) a Eu).
  - rewrite !(aview_unpoison_out tfibsegs (w_H W) U _ a Eu). exact (Heqw a Ha HWa). }
assert (Hsame' : same_but_materialized mdc (with_vm_backing (m_vm_lazy mdc) (m_vm_materialized model') mdc)).
{ rewrite <- (same_but_materialized_wvb mdc model' Hsame). exact Hsame. }
pose proof (same_but_materialized_wvb mdc _ Hsame') as Emd.
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
destruct (ml_stack_free _ ML Sc cid pos HWF Hin) as (HWF2 & l1 & l2 & E1 & E2).
assert (El1 : l1 = []).
{ destruct l1 as [|f l1']; [reflexivity|]. exfalso.
  rewrite Hfrs in E1. cbn in E1. injection E1 as <- E1'.
  pose proof (sep_frames_pos tfibsegs B LAWS lyc Sc W (unpoison U (ms_mem ms)) mdc (cid, pos) (cid, pos) [] l1' l2 HAR
    ltac:(rewrite Hfrs; cbn; rewrite E1'; reflexivity)) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. pose proof (fs_frame_bytes_pos cid Hcid). zlia. }
subst l1. cbn in E1, E2. rewrite Hfrs in E1. cbn in E1. injection E1 as E1.
(* AR of the freed state, over the unpoisoned memories: the donor's astack_free_law *)
assert (HAR' : AR tfibsegs B lyc (stack_free_state cid pos Sc) W (unpoison U memc')
  (with_vm_backing (m_vm_lazy mdc) (m_vm_materialized model') mdc)).
{ eapply (ASF lyc Sc W (unpoison U (ms_mem ms)) mdc (unpoison U memc') _ cid pos HAR Hin).
  - rewrite (aview_unpoison_out tfibsegs (w_H W) U memc' _ HflagU).
    unfold aview. subst memc'. rewrite Hmm. rewrite (Hflag0 msr' HS'). reflexivity.
  - intros a Ha Ho Hne. apply HeqwU; [exact Ha|]. intros HWa.
    destruct (Hwr a HWa) as [Hw | Hw]; [|exact (Hne Hw)].
    exact (proj1 (awr_byte_cases tfibsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) Ho).
  - intros a Hv. eapply aview_keeps_vis; [apply fsw_mem_grows_unpoison; exact Hgr' | exact Hv].
  - rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
  - rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
  - rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
  - intros a _ Hh. unfold unpoison. destruct (in_ush U (bv_unsigned (w64 a))); [reflexivity|].
    subst memc'. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hh. reflexivity. }
apply (Hk (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model')).
- rewrite Hrr. exact HS'.
- eapply (ajournal_after_write tfibsegs B LAWS fs_segs_low STK sp0 FP ly S W0 mem md ((cid, pos) :: own') lyc Sc W
    (unpoison U (ms_mem ms)) mdc k (unpoison U memc') _ (in_wrange E (ss_mem ss)) (stack_free_state cid pos Sc) own'
    HJ HeqwU
    ltac:(intros a Ha; eapply apresent_grows; [apply fsw_mem_grows_unpoison; exact Hgr' | exact Ha]) Hsame').
  + intros a Ha. destruct (Hwr a Ha) as [Hw | ->]; [left; exact Hw | right; split; [exact Hfo | exact Hfr_rng]].
  + exact HAR'.
  + unfold ablocks. rewrite blocks_stack_free_state. reflexivity.
  + reflexivity.
  + cbn. zlia.
  + etransitivity; [exact E2 | symmetry; exact E1].
  + pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
    apply (qtight_ext Sc); [reflexivity | reflexivity | reflexivity | exact HQT].
- (* ARU for the freed state: AR' above, U's ranges still in live blocks, their bytes untouched *)
  split; [exact HAR'|]. split.
  + pose proof (ARU_ok tfibsegs B lyc Sc U W (ms_mem ms) mdc HARU) as (OKf & OKd).
    split; [|exact OKd]. revert OKf. apply Forall_impl. intros rg (A1 & A2 & A3 & p & nn & Hb & Hp1 & Hp2).
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. exists p, nn.
    split; [|split; [exact Hp1 | exact Hp2]]. unfold ablocks in Hb |- *. rewrite blocks_stack_free_state. exact Hb.
  + intros s Hs. pose proof (ARU_poisoned tfibsegs B lyc Sc U W (ms_mem ms) mdc HARU s Hs) as Hps.
    pose proof (ush_facts tfibsegs B lyc Sc U W (ms_mem ms) mdc s HARU Hs) as (Hown & L1 & L2).
    rewrite <- Hps. apply Heqw; [unfold SHADOW_OFF, kHighMemBeg in *; lia|]. intros HWa.
    destruct (Hwr s HWa) as [Hw | ->].
    * exact (proj1 (awr_byte_cases tfibsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s HJ Hw) Hown).
    * (* s is the flag byte: the same low / high application split as HflagU *)
      pose proof ASAN_CEIL_range as (Hc1 & _). unfold in_app in Hflapp.
      unfold ASAN_CEIL, SHADOW_OFF, kHighMemBeg, kLowShadowBeg in *.
      destruct Hflapp as (H0 & [Hlo | (Hhi & Hhc)]); lia.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- exact Hfr'.
- exact Hgr'.
Qed.
(* the flag byte of a live fake frame lies at or above 4096, at any AR state (ARU gives AR by ARU_AR, an ajournal by
   its first conjunct): AR_flag_law (Reusable/YG0d.v:463-467) puts it in application memory, in_app (flag_addr ly cid
   pos) 1, whose first conjunct is 4096 <= lo (Reusable/YG0f.v:276). A walk's engine run over the release store needs
   it for the flag pointer's atom fact (mkAF 4096 ...); fsw_flag_storeU itself takes no such premise. *)
Lemma fsw_flag_addr_ge4096 : forall ly S (W : world tfibsegs) mem md cid pos,
  AR tfibsegs B ly S W mem md -> In (cid, pos) (frames S) -> 4096 <= flag_addr ly cid pos.
Proof.
intros ly S W mem md cid pos HAR Hin.
destruct (al_flag _ _ LAWS ly S W mem md cid pos HAR Hin) as (_ & _ & (H4096 & _) & _). exact H4096.
Qed.

End f.
