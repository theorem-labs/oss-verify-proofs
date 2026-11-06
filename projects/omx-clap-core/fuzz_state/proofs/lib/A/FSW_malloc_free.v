(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img's image range set to libreac/fuzz_boxreg's own (Reusable/YImgTop.v IMG_LO, IMG_TOP). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Reusable/YCbq.v, with its module paths and module names changed; 442 of its 552 lines of code are new or changed and 2852 lines of the source are left out. *)
(* fs ASan, group ALLOC: the U-form allocator call steps of fuzz_state (image tfibsegs), a kit file other walks import,
   plus the fuzz_free p = 0 arm. The fuzz_malloc_spec / fuzz_free_spec walks themselves (lib/A/FSH_Fn_alloc.v) need
   RELOC's static-store arm and are NOT in this file.

   The allocator call steps the world W -> W2 through amreal and changes ablocks (unlike aj_intrin_at, which keeps
   W2 = W), so these are not FSW_K's runtime-call step. All take a journal over `unpoison U mem`, ARU of the machine
   memory, and give ARU at the resumed state with U UNCHANGED (malloc_leafU / free_leafU keep U).
   - fsw_aj_mallocU    : U form of YCbq.aj_malloc_at (res = 0 allowed: the NULL disjunct is kept).
   - fsw_aj_malloc04U  : U form of YCbq.aj_malloc_at04 (non-NULL: 4096 <= res, the block appended).
   - fsw_aj_malloc04U_sub : the call-relative (callee-only) journal of fsw_aj_malloc04U, after YC85.amalloc04_sub's
                         standalone output, for a walk that resumes after a NON-tail malloc call.
   - fsw_aj_freeU      : U form of YCbq.aj_free_at; afree_realizesU's free-outside premise is the lemma's HUoutside
                         (a caller closes it with FSupoisonU.ARU_free_outside + fs_heads, see the U bookkeeping below).

   port-from: Reusable/YCbq.v aj_malloc_at (1353), aj_malloc_at04 (1550), aj_free_at (991), ajournal_sub_init (1826);
   YC85.amalloc04_sub (RELOC) for the _sub shape. Same proof scripts, U-threaded; no rename beyond the U suffix.

   Per-image cells (lead's cell scan): the allocator steps and the U bookkeeping READ NO per-image cell (no GOT shadow
   0x9f6f0, no uar flag, no A_EMPTY, no rodata shadow cell); fsw_fuzz_free_null reads none either (its path is before
   fuzz_free's GOT load at 0x82d5c). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG08 YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSW_K FSW_ret.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Module FSP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.

(* ---- code tables (MEASURED spans; no RVC, 4 * insns = bytes): fuzz_malloc 0x828ac..0x829e8 = 79 words;
   fuzz_free 0x82d40..0x82e5c = 71 words (a Theorem Labs lane 21:39Z) ---- *)
Definition tbl_fm : ctable := Eval vm_compute in build_table tfibsegs A_fuzz_malloc 79 TEmpty.
Lemma tbl_fm_eq : tbl_fm = build_table tfibsegs A_fuzz_malloc 79 TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_fm). Qed.
Lemma tbl_fm_ok : table_ok tfibsegs tbl_fm.
Proof. rewrite tbl_fm_eq. apply build_table_ok0. unfold A_fuzz_malloc. lia. Qed.
Definition tbl_ff : ctable := Eval vm_compute in build_table tfibsegs A_fuzz_free 71 TEmpty.
Lemma tbl_ff_eq : tbl_ff = build_table tfibsegs A_fuzz_free 71 TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_ff). Qed.
Lemma tbl_ff_ok : table_ok tfibsegs tbl_ff.
Proof. rewrite tbl_ff_eq. apply build_table_ok0. unfold A_fuzz_free. lia. Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis FS_ENV : api_env tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Local Notation code := (as_code B).
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd := fs_segs_low.
(* an arithmetic premise of a core lemma, closed only where its goal is an inequality (inside `first [solve ..]` lists,
   so no other premise kind is ever handed to lia) *)
Local Ltac zle := lazymatch goal with |- (_ <= _)%Z => zlia | |- (_ < _)%Z => zlia end.

(* ---- fsw_aj_mallocU: the U twin of aj_malloc_at (YCbq.v:1353), res = 0 allowed. From a within-walk journal over
   `unpoison U mem` and ARU of the machine memory, consume `jal __wrap_malloc`, giving the composed journal over
   `unpoison U mem2`, ARU at the result (U unchanged), and either the NULL result (blocks unchanged, nothing new kept
   out) or the appended block. ---- *)
Lemma fsw_aj_mallocU : FSupoisonU.amalloc_realizesU tfibsegs B ->
  forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc U mdc k n (o : Z) raw ch,
  ajournal tfibsegs B STK sp0 FP ly S W0 (FSP.unpoison U mem) md own lyc Sc W (FSP.unpoison U memT) mdc k ->
  FSP.ARU tfibsegs B lyc Sc U W memT mdc ->
  getr regsT 10 = w64 n -> 0 <= n < MALLOC_MAX -> blocks_bytes Sc + n <= LIVE_MAX ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  st_nev Sc < EV_MAX ->
  chain_pre lyc (aview tfibsegs (w_H W) (FSP.unpoison U memT)) regsT ch ->
  SRr tfibsegs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_malloc code)) memT (seg_rom tfibsegs)) mdc)
  (fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
    c2 = mkCfg (mkst regs2 raw mem2 (seg_rom tfibsegs)) md2 /\
    FSP.ARU tfibsegs B ly2 S2 U W2 mem2 md2 /\
    ajournal tfibsegs B STK sp0 FP ly S W0 (FSP.unpoison U mem) md own ly2 S2 W2 (FSP.unpoison U mem2) md2 (k + 1) /\
    aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
    ((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
      acall_kept tfibsegs B lyc Sc W (FSP.unpoison U memT) W2 (FSP.unpoison U mem2)
        (sp0 + o - ASTACK) (sp0 + o) (fun _ => False))
     \/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
      acall_kept tfibsegs B lyc Sc W (FSP.unpoison U memT) W2 (FSP.unpoison U mem2)
        (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n)))).
Proof.
intros AMALLOC W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc U mdc k n o raw ch
  HJ HARU Ha0 Hn Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch.
pose proof HARU as (HARU_AR & HARU_OK & HARU_PO).
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 FS_ENV) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ASTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE0 : acall_pre tfibsegs B lyc Sc W regsT (FSP.unpoison U memT) mdc ch).
{ destruct HstkC as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
split; [exact HAR|]. split; [exact (aregime_small _ Hev)|]. split; [rewrite Hra; exact Hraw|].
split; [exact Q1|]. split; [zlia|]. split; [zlia|]. split; [zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|].
split; [exact Hgp|]. split; [exact Htp|]. split; [exact Hch | exact (conj HQT (mroom_of_regime (as_universe B) Sc (am_wf _ _ _ _ (proj1 HAR)) (aregime_to_mid Sc (aregime_small _ Hev)) (qtight_qloose Sc HQT)))]. }
assert (HPRE : FSupoisonU.acall_preU tfibsegs B lyc Sc U W regsT memT mdc ch)
  by (split; [exact HPRE0 | split; [exact HARU_OK | exact HARU_PO]]).
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
pose proof (ml_malloc _ ML Sc n (call_trace lyc (pc_malloc_ra0 code) regsT ch) HWF Hev Hn Hlive
  (call_trace_len lyc _ regsT ch)) as HTOK.
pose proof (AMALLOC lyc Sc U W regsT memT mdc n ch HPRE Ha0 Hn Hlive (or_intror Hev)) as HREAL.
eapply SRr_mono.
{ exact (amreal_SRr tfibsegs _ W _ _ HREAL (atok_asafe _ _ _ HTOK) (atok_agprog _ _ _ HTOK) (atok_nospin _ _ HTOK)). }
intros W2 c2 HwleW (r & tr & Hpath & Hleaf).
destruct (atok_apath _ _ _ tr r HTOK Hpath) as (ns' & HQ). destruct r as [p S2]. unfold malloc_post in HQ.
destruct HQ as (HWF2 & Hnev2 & Hsecs2 & Hfrs2 & Hbl & _). cbn [fst snd] in *.
destruct Hleaf as (ly2 & regs2 & mem2 & md2 & -> & HPOSTU & Hres & HQT2).
pose proof HPOSTU as (HPOST & OK2 & PO2).
pose proof HPOST as (HAR2 & Hly2 & Hwle2' & HP & Hio2 & Hfr2 & Hpres2).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
set (f2 := fun b : sptr * Z => (sptr_addr B ly2 (fst b), snd b)).
set (fc := fun b : sptr * Z => (sptr_addr B lyc (fst b), snd b)).
assert (Efc : forall b, In b (blocks Sc) -> f2 b = fc b).
{ intros b Hb. exact (map_eq_In f2 fc (blocks Sc) b Eab Hb). }
assert (Hsecsle : (length (st_secs Sc) <= length (st_secs S2))%nat) by exact (secs_ext_length _ _ Hsecs2).
destruct (asptr_null_dec p) as [-> | Hnn].
- cbn in Hres.
  assert (Eab2 : ablocks B ly2 S2 = ablocks B lyc Sc).
  { unfold ablocks. change (map f2 (blocks S2) = map fc (blocks Sc)). rewrite Hbl. apply map_ext_in. exact Efc. }
  assert (HJ1 : ajournal tfibsegs B ASTACK (spZ regsT) [] lyc Sc W (FSP.unpoison U memT) mdc [] ly2 S2 W2 (FSP.unpoison U mem2) md2 1).
  { eapply (acall_post_journal tfibsegs B LAWS segs_low FS_ENV).
    all: first [ solve [exact HPOST] | solve [exact HAR] | solve [exact HstkC] | solve [exact Hfrs2] | solve [zle]
               | solve [exact Hsecsle] | solve [exact HQT2]
               | solve [intros a [Hf _]; exfalso; exact (Hf eq_refl)]
               | solve [intros q m i Hq Hnq Hi; exfalso; apply Hnq; rewrite Eab2; exact Hq] ]. }
  exists ly2, S2, regs2, mem2, md2, 0.
  split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
  split; [split; [exact HAR2 | split; [exact OK2 | exact PO2]]|].
  split.
  { rewrite Hsp' in HJ1. change own with ([] ++ own); eapply (ajournal_sub tfibsegs B LAWS segs_low).
    all: first [ solve [exact HJ] | solve [exact HJ1] | solve [zle] | solve [intros a (rg & [] & _)] ]. }
  split; [exact HP|]. split; [exact Hres|]. split; [exact Hfrs2|]. left. split; [reflexivity|]. split; [exact Eab2|].
  rewrite Hsp' in HJ1. eapply (acall_kept_of_journal tfibsegs B segs_low).
  all: first [ solve [exact HJ1] | solve [exact HAR] | solve [exact sink_closed_nil] | solve [intros a (rg & [] & _)]
             | solve [intros a _ (rg & [] & _)] | solve [intros b m i Hb Hi _; rewrite Eab2; exact Hb] ].
- assert (Hbl' : blocks S2 = blocks Sc ++ [(p, n)] /\ ~ In p (map fst (blocks Sc))).
  { destruct p; [exfalso; exact (Hnn eq_refl) | exact Hbl | exact Hbl | exact Hbl]. }
  clear Hbl. destruct Hbl' as [Hbl Hfresh].
  set (res := sptr_addr B ly2 p) in *.
  assert (Eab2 : ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)]).
  { unfold ablocks. change (map f2 (blocks S2) = map fc (blocks Sc) ++ [(res, n)]). rewrite Hbl, map_app. cbn [map].
  f_equal. apply map_ext_in. exact Efc. }
  assert (Hnew : In (res, n) (ablocks B ly2 S2)) by (rewrite Eab2; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS ly2 S2 W2 (FSP.unpoison U mem2) md2 res n HAR2 Hnew) as (_ & Hr4096 & _).
  assert (Hdisj : forall b m a, In (b, m) (ablocks B lyc Sc) -> b <= a < b + req_size m -> ~ (res <= a < res + req_size n)).
  { intros b m a Hb Hr HE. apply in_split in Hb as (b1 & b2 & Ebq).
  pose proof (sep_blocks_pos tfibsegs B LAWS ly2 S2 W2 (FSP.unpoison U mem2) md2 (b, m) (res, n) b1 b2 [] HAR2
  ltac:(rewrite Eab2, Ebq, <- app_assoc; reflexivity)) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. zlia. }
  assert (HJ1 : ajournal tfibsegs B ASTACK (spZ regsT) [] lyc Sc W (FSP.unpoison U memT) mdc [] ly2 S2 W2 (FSP.unpoison U mem2) md2 1).
  { eapply (acall_post_journal tfibsegs B LAWS segs_low FS_ENV).
    all: first [ solve [exact HPOST] | solve [exact HAR] | solve [exact HstkC] | solve [exact Hfrs2] | solve [zle]
               | solve [exact Hsecsle] | solve [exact HQT2]
               | solve [intros a [_ Ha]; exists res, n; split; [right; exact Hnew|]; split; [exact Ha|]; right;
                        intros Hold; exact (Hdisj res n a Hold Ha Ha)]
               | solve [intros q m i Hq Hnq Hi; exfalso; apply Hnq; rewrite Eab2; apply in_or_app; left; exact Hq] ]. }
  exists ly2, S2, regs2, mem2, md2, res.
  split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
  split; [split; [exact HAR2 | split; [exact OK2 | exact PO2]]|].
  split.
  { rewrite Hsp' in HJ1. change own with ([] ++ own); eapply (ajournal_sub tfibsegs B LAWS segs_low).
    all: first [ solve [exact HJ] | solve [exact HJ1] | solve [zle] | solve [intros a (rg & [] & _)] ]. }
  split; [exact HP|]. split; [exact Hres|]. split; [exact Hfrs2|]. right. split; [exact Hr4096|]. split; [exact Eab2|].
  rewrite Hsp' in HJ1. eapply (acall_kept_of_journal tfibsegs B segs_low).
  all: first [ solve [exact HJ1] | solve [exact HAR] | solve [exact sink_closed_nil] | solve [intros a (rg & [] & _)]
             | solve [intros a _ (rg & [] & _)] | solve [intros b m i Hb Hi _; rewrite Eab2; apply in_or_app; left; exact Hb] ].
Qed.

(* ---- fsw_aj_malloc04U: the U twin of aj_malloc_at04 (YCbq.v:1550). From a within-walk journal over `unpoison U mem`
   and ARU of the machine memory, consume `jal __wrap_malloc`, giving the composed journal over `unpoison U mem2`, ARU
   at the result, and the non-NULL block / register facts. ---- *)
Lemma fsw_aj_malloc04U : FSupoisonU.amalloc_realizesU tfibsegs B ->
  forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc U mdc k n (o : Z) raw ch,
  ajournal tfibsegs B STK sp0 FP ly S W0 (FSP.unpoison U mem) md own lyc Sc W (FSP.unpoison U memT) mdc k ->
  FSP.ARU tfibsegs B lyc Sc U W memT mdc ->
  getr regsT 10 = w64 n -> 0 <= n < MALLOC_MAX -> blocks_bytes Sc + n <= LIVE_MAX ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  st_nev Sc < EV_MAX ->
  chain_pre lyc (aview tfibsegs (w_H W) (FSP.unpoison U memT)) regsT ch ->
  SRr tfibsegs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_malloc code)) memT (seg_rom tfibsegs)) mdc)
  (fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
    c2 = mkCfg (mkst regs2 raw mem2 (seg_rom tfibsegs)) md2 /\
    FSP.ARU tfibsegs B ly2 S2 U W2 mem2 md2 /\
    ajournal tfibsegs B STK sp0 FP ly S W0 (FSP.unpoison U mem) md own ly2 S2 W2 (FSP.unpoison U mem2) md2 (k + 1) /\
    aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
    4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
    acall_kept tfibsegs B lyc Sc W (FSP.unpoison U memT) W2 (FSP.unpoison U mem2)
      (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n)).
Proof.
intros AMALLOC W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc U mdc k n o raw ch
  HJ HARU Ha0 Hn Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch.
pose proof HARU as (HARU_AR & HARU_OK & HARU_PO).
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 FS_ENV) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ASTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE0 : acall_pre tfibsegs B lyc Sc W regsT (FSP.unpoison U memT) mdc ch).
{ destruct HstkC as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
split; [exact HAR|]. split; [exact (aregime_small _ Hev)|]. split; [rewrite Hra; exact Hraw|].
split; [exact Q1|]. split; [zlia|]. split; [zlia|]. split; [zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|].
split; [exact Hgp|]. split; [exact Htp|]. split; [exact Hch | exact (conj HQT (mroom_of_regime (as_universe B) Sc (am_wf _ _ _ _ (proj1 HAR)) (aregime_to_mid Sc (aregime_small _ Hev)) (qtight_qloose Sc HQT)))]. }
assert (HPRE : FSupoisonU.acall_preU tfibsegs B lyc Sc U W regsT memT mdc ch)
  by (split; [exact HPRE0 | split; [exact HARU_OK | exact HARU_PO]]).
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
pose proof (ml_malloc_ns _ ML Sc n (call_trace lyc (pc_malloc_ra0 code) regsT ch) HWF (or_introl Hev) Hn Hlive
  (or_intror (conj (call_trace_len lyc _ regsT ch) Hev))) as HTOK.
pose proof (AMALLOC lyc Sc U W regsT memT mdc n ch HPRE Ha0 Hn Hlive (or_intror Hev)) as HREAL.
eapply SRr_mono.
{ exact (amreal_SRr04 tfibsegs _ W _ _ HREAL (atok_asafe _ _ _ HTOK) (atok_agprog _ _ _ HTOK) (atok_nospin _ _ HTOK)). }
intros W2 c2 HwleW (r & tr & Hpath & Hgf & Hleaf).
pose proof (atok_apath_flag _ _ _ tr r HTOK Hpath) as [HQ HNS]. rewrite (last_flag_true tr Hgf) in HNS.
destruct r as [p S2]. unfold malloc_post in HQ.
destruct HQ as (HWF2 & Hnev2 & Hsecs2 & Hfrs2 & Hbl & _). cbn [fst snd] in *.
destruct Hleaf as (ly2 & regs2 & mem2 & md2 & -> & HPOSTU & Hres & HQT2).
pose proof HPOSTU as (HPOST & OK2 & PO2).
pose proof HPOST as (HAR2 & Hly2 & Hwle2' & HP & Hio2 & Hfr2 & Hpres2).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
set (f2 := fun b : sptr * Z => (sptr_addr B ly2 (fst b), snd b)).
set (fc := fun b : sptr * Z => (sptr_addr B lyc (fst b), snd b)).
assert (Efc : forall b, In b (blocks Sc) -> f2 b = fc b).
{ intros b Hb. exact (map_eq_In f2 fc (blocks Sc) b Eab Hb). }
assert (Hsecsle : (length (st_secs Sc) <= length (st_secs S2))%nat) by exact (secs_ext_length _ _ Hsecs2).
destruct (asptr_null_dec p) as [-> | Hnn].
- exfalso. discriminate (HNS eq_refl).
- assert (Hbl' : blocks S2 = blocks Sc ++ [(p, n)] /\ ~ In p (map fst (blocks Sc))).
  { destruct p; [exfalso; exact (Hnn eq_refl) | exact Hbl | exact Hbl | exact Hbl]. }
  clear Hbl. destruct Hbl' as [Hbl Hfresh].
  set (res := sptr_addr B ly2 p) in *.
  assert (Eab2 : ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)]).
  { unfold ablocks. change (map f2 (blocks S2) = map fc (blocks Sc) ++ [(res, n)]). rewrite Hbl, map_app. cbn [map].
  f_equal. apply map_ext_in. exact Efc. }
  assert (Hnew : In (res, n) (ablocks B ly2 S2)) by (rewrite Eab2; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS ly2 S2 W2 (FSP.unpoison U mem2) md2 res n HAR2 Hnew) as (_ & Hr4096 & _).
  assert (Hdisj : forall b m a, In (b, m) (ablocks B lyc Sc) -> b <= a < b + req_size m -> ~ (res <= a < res + req_size n)).
  { intros b m a Hb Hr HE. apply in_split in Hb as (b1 & b2 & Ebq).
  pose proof (sep_blocks_pos tfibsegs B LAWS ly2 S2 W2 (FSP.unpoison U mem2) md2 (b, m) (res, n) b1 b2 [] HAR2
  ltac:(rewrite Eab2, Ebq, <- app_assoc; reflexivity)) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. zlia. }
  assert (HJ1 : ajournal tfibsegs B ASTACK (spZ regsT) [] lyc Sc W (FSP.unpoison U memT) mdc [] ly2 S2 W2 (FSP.unpoison U mem2) md2 1).
  { eapply (acall_post_journal tfibsegs B LAWS segs_low FS_ENV).
    all: first [ solve [exact HPOST] | solve [exact HAR] | solve [exact HstkC] | solve [exact Hfrs2] | solve [zle]
               | solve [exact Hsecsle] | solve [exact HQT2]
               | solve [intros a [_ Ha]; exists res, n; split; [right; exact Hnew|]; split; [exact Ha|]; right;
                        intros Hold; exact (Hdisj res n a Hold Ha Ha)]
               | solve [intros q m i Hq Hnq Hi; exfalso; apply Hnq; rewrite Eab2; apply in_or_app; left; exact Hq] ]. }
  exists ly2, S2, regs2, mem2, md2, res.
  split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
  split; [split; [exact HAR2 | split; [exact OK2 | exact PO2]]|].
  split.
  { rewrite Hsp' in HJ1. change own with ([] ++ own); eapply (ajournal_sub tfibsegs B LAWS segs_low).
    all: first [ solve [exact HJ] | solve [exact HJ1] | solve [zle] | solve [intros a (rg & [] & _)] ]. }
  split; [exact HP|]. split; [exact Hres|]. split; [exact Hfrs2|]. split; [exact Hr4096|]. split; [exact Eab2|].
  rewrite Hsp' in HJ1. eapply (acall_kept_of_journal tfibsegs B segs_low).
  all: first [ solve [exact HJ1] | solve [exact HAR] | solve [exact sink_closed_nil] | solve [intros a (rg & [] & _)]
             | solve [intros a _ (rg & [] & _)] | solve [intros b m i Hb Hi _; rewrite Eab2; apply in_or_app; left; exact Hb] ].
Qed.

(* ---- fsw_aj_freeU_sub: the CALL-RELATIVE journal of a free call (callee only: window [sp - ASTACK, sp), footprint the
   freed block, own = []), the free twin of fsw_aj_malloc04U_sub, for a walk whose own call machinery composes the callee
   half (CRT's crt_seg_call / crt_after_call). No trace premise (C5: afree_realizesU and ml_free admit any trace once
   st_nev < EV_MAX). Its premises are the callee's: acall_preU and astk_ok ASTACK at the call, the event room, the
   block, U outside it, a0 and ra. ported from: CRT's crtD2_free_sub (lib/A/FSH_crt_segD2_s39.v, a working branch
   6cf61486dca), the same statement and script, renamed into this file; fsw_aj_freeU below is now built on it. ---- *)
Lemma fsw_aj_freeU_sub : FSupoisonU.afree_realizesU tfibsegs B ->
  forall lyc Sc U (W : world tfibsegs) regsT memT mdc pa n raw ch,
  FSupoisonU.acall_preU tfibsegs B lyc Sc U W regsT memT mdc ch ->
  astk_ok ASTACK lyc (spZ regsT) ->
  st_nev Sc < EV_MAX ->
  In (pa, n) (ablocks B lyc Sc) ->
  (forall r, In r U -> fst r + snd r <= pa \/ pa + req_size n <= fst r) ->
  getr regsT 10 = w64 pa ->
  getr regsT 1 = raw ->
  SRr tfibsegs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free (as_code B))) memT (seg_rom tfibsegs)) mdc)
  (fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 raw mem2 (seg_rom tfibsegs)) md2 /\
    ajournal tfibsegs B ASTACK (spZ regsT) [(pa, pa + req_size n)] lyc Sc W (unpoison U memT) mdc []
      ly2 S2 W2 (unpoison U mem2) md2 1 /\
    upoison_ok B ly2 S2 U /\ upoisoned tfibsegs W2 mem2 U /\
    aregs_preserved regsT regs2 /\
    (exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2)).
Proof.
intros AFREE lyc Sc U W regsT memT mdc pa n raw ch HPRE HstkC Hev Hin HUoutside Ha0 Hra.
pose proof HPRE as (HPRE0 & HARU_OK & HARU_PO).
pose proof HPRE0 as (HAR & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 FS_ENV) as [He0 He1].
destruct (proj1 (in_ablocks B lyc Sc pa n) Hin) as (q & Hq & Hqin).
destruct (al_blocks _ _ LAWS lyc Sc W (unpoison U memT) mdc pa n HAR Hin)
  as (Hpa16 & Hpa4096 & Hpaceil & [Hpah Hpah2] & Hpab & _).
assert (Hqnn : q <> PNull) by (intros ->; cbn in Hq; zlia).
assert (HUout' : forall r, In r U -> fst r + snd r <= sptr_addr B lyc q \/ sptr_addr B lyc q + req_size n <= fst r)
  by (rewrite Hq; exact HUoutside).
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
pose proof (ml_free _ ML Sc q n (call_trace lyc (pc_free_ra0 (as_code B)) regsT ch) HWF Hev (or_intror Hqin)
  (call_trace_len lyc _ regsT ch)) as HTOK.
pose proof (AFREE lyc Sc U W regsT memT mdc q n ch HPRE (or_intror Hqin) HUout' ltac:(rewrite Hq; exact Ha0)
  (or_intror Hev)) as HREAL.
eapply SRr_mono.
{ exact (amreal_SRr tfibsegs _ W _ _ HREAL (atok_asafe _ _ _ HTOK) (atok_agprog _ _ _ HTOK) (atok_nospin _ _ HTOK)). }
intros W2 c2 HwleW (r & tr & Hpath & Hleaf).
destruct (atok_apath _ _ _ tr r HTOK Hpath) as (ns' & HQ). destruct r as [[] S2]. unfold free_post in HQ.
cbn [fst snd] in HQ.
destruct HQ as (HWF2 & Hnev2 & Hsecs2 & Hfrs2 & (l1 & l2 & Hsplit & Hbl2) & _).
destruct Hsplit as [[Hnull _] | Hsplit]; [exfalso; exact (Hqnn Hnull)|].
cbn [fst snd] in *.
destruct Hleaf as (ly2 & regs2 & mem2 & md2 & -> & HPOSTU & HQT2).
pose proof HPOSTU as (HPOST & OK2 & PO2).
pose proof HPOST as (HAR2 & Hly2 & Hwle2' & HP & Hio2 & Hfr2 & Hpres2).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
set (f2 := fun b : sptr * Z => (sptr_addr B ly2 (fst b), snd b)).
set (fc := fun b : sptr * Z => (sptr_addr B lyc (fst b), snd b)).
assert (Efc : forall b, In b (blocks Sc) -> f2 b = fc b).
{ intros b Hb. exact (map_eq_In f2 fc (blocks Sc) b Eab Hb). }
assert (Eab2 : ablocks B ly2 S2 = map fc l1 ++ map fc l2).
{ unfold ablocks. change (map f2 (blocks S2) = map fc l1 ++ map fc l2). rewrite Hbl2, map_app.
  f_equal; apply map_ext_in; intros b Hb; apply Efc; rewrite Hsplit; apply in_or_app;
    [left; exact Hb | right; right; exact Hb]. }
assert (EabC : ablocks B lyc Sc = map fc l1 ++ (pa, n) :: map fc l2).
{ unfold ablocks. change (map fc (blocks Sc) = map fc l1 ++ (pa, n) :: map fc l2). rewrite Hsplit, map_app.
  cbn [map app].
  replace (fc (q, n)) with (pa, n) by (subst fc; cbn [fst snd]; rewrite Hq; reflexivity). reflexivity. }
assert (Hlive : forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ (pa <= b + i < pa + req_size n) ->
  In (b, m) (ablocks B ly2 S2)).
{ intros b m i Hb Hi HnE. rewrite Eab2. rewrite EabC in Hb. apply in_app_or in Hb as [Hb | [Hb | Hb]].
  - apply in_or_app. left. exact Hb.
  - exfalso. injection Hb as <- <-. apply HnE. zlia.
  - apply in_or_app. right. exact Hb. }
assert (HgoneC : forall p m i, In (p, m) (ablocks B lyc Sc) -> ~ In (p, m) (ablocks B ly2 S2) -> 0 <= i < req_size m ->
  inFP [(pa, pa + req_size n)] (p + i)).
{ intros p m i Hp Hnp Hi. exists (pa, pa + req_size n). split; [left; reflexivity|]. cbn [fst snd].
  destruct (Z_lt_le_dec (p + i) pa) as [H1|H1]; [exfalso; apply Hnp; apply (Hlive p m i Hp Hi); zlia|].
  destruct (Z_lt_le_dec (p + i) (pa + req_size n)) as [H2|H2]; [zlia|].
  exfalso; apply Hnp; apply (Hlive p m i Hp Hi); zlia. }
assert (HJ1 : ajournal tfibsegs B ASTACK (spZ regsT) [(pa, pa + req_size n)] lyc Sc W (unpoison U memT) mdc []
    ly2 S2 W2 (unpoison U mem2) md2 1).
{ eapply (acall_post_journal tfibsegs B LAWS segs_low FS_ENV).
  all: first [ solve [exact HPOST] | solve [exact HAR] | solve [exact HstkC] | solve [exact Hfrs2] | solve [zle]
             | solve [exact (secs_ext_length _ _ Hsecs2)] | solve [exact HgoneC] | solve [exact HQT2]
             | solve [intros a [_ Ha]; rewrite Hq in Ha; exists pa, n; split; [left; exact Hin|]; split; [exact Ha|];
                      left; exists (pa, pa + req_size n); split; [left; reflexivity | cbn; zlia]] ]. }
exists ly2, S2, regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [exact HJ1|]. split; [exact OK2|]. split; [exact PO2|]. split; [exact HP|].
exists (map fc l1), (map fc l2). split; [exact EabC | exact Eab2].
Qed.

(* ---- fsw_aj_freeU: the U twin of aj_free_at (YCbq.v:1004). The freed block holds no U range (HUoutside, discharged at
   fuzz_free's call site from ARU_free_outside + fs_heads after disown unpoisons its own head). ---- *)
Lemma fsw_aj_freeU : FSupoisonU.afree_realizesU tfibsegs B ->
  forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc U mdc k pa n (o : Z) raw ch,
  ajournal tfibsegs B STK sp0 FP ly S W0 (FSP.unpoison U mem) md own lyc Sc W (FSP.unpoison U memT) mdc k ->
  FSP.ARU tfibsegs B lyc Sc U W memT mdc ->
  In (pa, n) (ablocks B lyc Sc) ->
  (forall r, In r U -> fst r + snd r <= pa \/ pa + req_size n <= fst r) ->
  getr regsT 10 = w64 pa ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  st_nev Sc < EV_MAX ->
  chain_pre lyc (aview tfibsegs (w_H W) (FSP.unpoison U memT)) regsT ch ->
  (In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
  SRr tfibsegs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom tfibsegs)) mdc)
  (fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 raw mem2 (seg_rom tfibsegs)) md2 /\
    FSP.ARU tfibsegs B ly2 S2 U W2 mem2 md2 /\
    ajournal tfibsegs B STK sp0 FP ly S W0 (FSP.unpoison U mem) md own ly2 S2 W2 (FSP.unpoison U mem2) md2 (k + 1) /\
    aregs_preserved regsT regs2 /\
    (exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
    frames S2 = frames Sc /\
    acall_kept tfibsegs B lyc Sc W (FSP.unpoison U memT) W2 (FSP.unpoison U mem2)
      (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n)).
Proof.
intros AFREE W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc U mdc k pa n o raw ch
  HJ HARU Hin HUoutside Ha0 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch HFP.
pose proof HARU as (HARU_AR & HARU_OK & HARU_PO).
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (ASTACK = 16384) as Has by reflexivity.
destruct (al_blocks _ _ LAWS lyc Sc W (FSP.unpoison U memT) mdc pa n HAR Hin) as (Hpa16 & Hpa4096 & Hpaceil & [Hpah Hpah2] & Hpab & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ASTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE0 : acall_pre tfibsegs B lyc Sc W regsT (FSP.unpoison U memT) mdc ch).
{ destruct HstkC as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
split; [exact HAR|]. split; [exact (aregime_small _ Hev)|]. split; [rewrite Hra; exact Hraw|].
split; [exact Q1|]. split; [zlia|]. split; [zlia|]. split; [zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|].
split; [exact Hgp|]. split; [exact Htp|]. split; [exact Hch | exact (conj HQT (mroom_of_regime (as_universe B) Sc (am_wf _ _ _ _ (proj1 HAR)) (aregime_to_mid Sc (aregime_small _ Hev)) (qtight_qloose Sc HQT)))]. }
assert (HPRE : FSupoisonU.acall_preU tfibsegs B lyc Sc U W regsT memT mdc ch)
  by (split; [exact HPRE0 | split; [exact HARU_OK | exact HARU_PO]]).
(* the callee half, then its composition with the caller's journal *)
eapply SRr_mono.
{ exact (fsw_aj_freeU_sub AFREE lyc Sc U W regsT memT mdc pa n raw ch HPRE HstkC Hev Hin HUoutside Ha0 Hra). }
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ1 & OK2 & PO2 & HP & (l1 & l2 & EabC & Eab2)).
pose proof HJ1 as (HAR2 & _ & _ & _ & _ & Hfrs2 & _).
assert (Hlive : forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ (pa <= b + i < pa + req_size n) ->
  In (b, m) (ablocks B ly2 S2)).
{ intros b m i Hb Hi HnE. rewrite Eab2. rewrite EabC in Hb. apply in_app_or in Hb as [Hb | [Hb | Hb]].
  - apply in_or_app. left. exact Hb.
  - exfalso. injection Hb as <- <-. apply HnE. zlia.
  - apply in_or_app. right. exact Hb. }
exists ly2, S2, regs2, mem2, md2.
split; [reflexivity|].
split; [split; [exact HAR2 | split; [exact OK2 | exact PO2]]|].
split.
{ rewrite Hsp' in HJ1. change own with ([] ++ own); eapply (ajournal_sub tfibsegs B LAWS segs_low).
  (* the callee footprint byte a is the freed block's: in FP when the block was the caller's at entry, else a block
     the walk's own journal made (in_tmp_block); the base's HF may carry further arms, so the in_tmp_block arm is
     reached by `right` and, if it is not the last arm, `left` *)
  all: first [ solve [exact HJ] | solve [exact HJ1] | solve [zle]
             | solve [intros a (rg & [<-|[]] & Ha); cbn [fst snd] in Ha;
                      destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (pa, n) (ablocks B ly S))
                        as [H0|H0];
                      [ left; split; [| exists pa, n; split; [exact Hin | zlia]];
                        replace a with (pa + (a - pa)) by zlia; apply (HFP H0); zlia
                      | right; first [ solve [exists pa, n; split; [exact Hin|]; split; [exact H0 | zlia]]
                                     | solve [left; exists pa, n; split; [exact Hin|]; split; [exact H0 | zlia]] ] ]] ]. }
split; [exact HP|].
split; [exists l1, l2; split; [exact EabC | exact Eab2]|].
split; [exact Hfrs2|].
rewrite Hsp' in HJ1.
eapply (acall_kept_of_journal tfibsegs B segs_low).
all: first [ solve [exact HJ1] | solve [exact HAR] | solve [exact Hlive]
           | solve [apply sink_closed_pos; constructor; [cbn [fst]; zlia | constructor]]
           | solve [intros a (rg & [<-|[]] & Ha); cbn [fst snd] in Ha; exact Ha]
           | solve [intros a' Hi' (rg & [<-|[]] & Ha'); cbn [fst snd] in Ha';
                    exact (blk_img tfibsegs B LAWS lyc Sc W (FSP.unpoison U memT) mdc pa n a' HAR Hin ltac:(zlia) Hi')] ].
Qed.

(* ---- fsw_aj_malloc04U_sub: the CALL-RELATIVE journal of a malloc call (callee only: window [sp0 + o - ASTACK, sp0 + o),
   FP1 = [], own = []), the U twin of YC85.amalloc04_sub's standalone output: the callee journal a walk takes when it
   resumes inside the caller after a NON-tail malloc call (fuzz_malloc's `jal __wrap_malloc` at 0x82908 resumes at
   0x8290c). Built as amalloc04_sub is: ajournal_sub_init at the call sp, then fsw_aj_malloc04U at o = 0. ---- *)
Lemma fsw_aj_malloc04U_sub : FSupoisonU.amalloc_realizesU tfibsegs B ->
  forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc U mdc k n (o : Z) raw ch,
  ajournal tfibsegs B STK sp0 FP ly S W0 (FSP.unpoison U mem) md own lyc Sc W (FSP.unpoison U memT) mdc k ->
  FSP.ARU tfibsegs B lyc Sc U W memT mdc ->
  getr regsT 10 = w64 n -> 0 <= n < MALLOC_MAX -> blocks_bytes Sc + n <= LIVE_MAX ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  st_nev Sc < EV_MAX ->
  chain_pre lyc (aview tfibsegs (w_H W) (FSP.unpoison U memT)) regsT ch ->
  SRr tfibsegs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_malloc code)) memT (seg_rom tfibsegs)) mdc)
  (fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
    c2 = mkCfg (mkst regs2 raw mem2 (seg_rom tfibsegs)) md2 /\
    FSP.ARU tfibsegs B ly2 S2 U W2 mem2 md2 /\
    ajournal tfibsegs B ASTACK (sp0 + o) [] lyc Sc W (FSP.unpoison U memT) mdc [] ly2 S2 W2 (FSP.unpoison U mem2) md2 1 /\
    aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
    4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
    acall_kept tfibsegs B lyc Sc W (FSP.unpoison U memT) W2 (FSP.unpoison U mem2)
      (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n)).
Proof.
intros AM W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc U mdc k n o raw ch
  HJ HARU Ha0 Hn Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hev Hch.
pose proof (ajournal_sub_init tfibsegs B STK sp0 FP ly S W0 (FSP.unpoison U mem) md own lyc Sc W (FSP.unpoison U memT)
  mdc k ASTACK (sp0 + o) [] o HJ eq_refl Hal Hneg ltac:(unfold ASTACK; lia) Hbud) as HJ1.
eapply SRr_mono.
{ exact (fsw_aj_malloc04U AM W regsT memT ASTACK (sp0 + o) [] lyc Sc W memT mdc [] lyc Sc U mdc 0 n 0 raw ch HJ1 HARU
    Ha0 Hn Hlive ltac:(rewrite Hsp'; lia) eq_refl ltac:(lia) ltac:(lia) Hgp Htp Hra Hraw Hev Hch). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HARU2 & HJ2 & HP & Hres & Hfr & Hr4 & Hbl & HK).
replace (sp0 + o + 0) with (sp0 + o) in HK by lia.
exists ly2, S2, regs2, mem2, md2, res. split; [reflexivity|]. split; [exact HARU2|].
split; [exact HJ2|]. split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr|]. split; [exact Hr4|].
split; [exact Hbl | exact HK].
Qed.

(* ---- U bookkeeping at fs's free / poison sites: the call premises, closed here so each call is one apply ---- *)
(* disown removes the block's own head wherever it sits; the rest of U is still fs_heads *)
Lemma fs_heads_remove : forall ly S U1 U2 h,
  FSupoisonU.fs_heads B ly S (U1 ++ (h, 16) :: U2) -> FSupoisonU.fs_heads B ly S (U1 ++ U2).
Proof.
intros ly S U1 U2 h H r Hr. apply H. apply in_app_or in Hr as [Hr|Hr]; apply in_or_app; [left | right; right]; exact Hr.
Qed.
(* a head occurs once in a pairwise-disjoint U, so once removed it is gone: ARU_free_outside's ~ In premise *)
Lemma head_not_in_rest : forall U1 U2 h,
  pairwise zdisjoint (U1 ++ (h, 16) :: U2) -> ~ In (h, 16) (U1 ++ U2).
Proof.
intros U1 U2 h P Hin. apply in_app_or in Hin as [Hin|Hin]; apply in_split in Hin as (a & c & ->).
- pose proof (YCbq.pairwise_In2 zdisjoint _ (h, 16) (h, 16) a c U2 P ltac:(rewrite <- app_assoc; reflexivity)) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. lia.
- pose proof (YCbq.pairwise_In2 zdisjoint _ (h, 16) (h, 16) U1 a c P eq_refl) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.
(* the block malloc appends is fresh: it was not among the old blocks (AR's blocks are pairwise disjoint) *)
Lemma fresh_of_snoc : forall ly2 S2 W mem md l b m,
  AR tfibsegs B ly2 S2 W mem md -> ablocks B ly2 S2 = l ++ [(b, m)] -> 0 < req_size m -> ~ In (b, m) l.
Proof.
intros ly2 S2 W mem md l b m HAR E Hm Hin.
assert (Hnew : In (b, m) (ablocks B ly2 S2)) by (rewrite E; apply in_or_app; right; left; reflexivity).
pose proof (al_blocks _ _ LAWS ly2 S2 W mem md b m HAR Hnew) as (_ & _ & _ & _ & _ & PW & _).
rewrite E, map_app in PW. cbn [map fst snd] in PW.
apply (in_map (fun x : Z * Z => (fst x, req_size (snd x)))) in Hin. cbn [fst snd] in Hin.
apply in_split in Hin as (a & c & Ea). rewrite Ea in PW.
pose proof (YCbq.pairwise_In2 zdisjoint _ (b, req_size m) (b, req_size m) a c [] PW
  ltac:(rewrite <- app_assoc; reflexivity)) as D.
unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.
(* a fresh block's 16-byte head is disjoint from every head of the old U (U's heads sit in old blocks) *)
Lemma new_head_disjoint : forall ly S ly2 S2 W mem md U b m,
  AR tfibsegs B ly2 S2 W mem md -> FSupoisonU.fs_heads B ly S U ->
  (forall x, In x (ablocks B ly S) -> In x (ablocks B ly2 S2)) ->
  In (b, m) (ablocks B ly2 S2) -> ~ In (b, m) (ablocks B ly S) -> 16 <= req_size m ->
  forall r, In r U -> zdisjoint (b, 16) r.
Proof.
intros ly S ly2 S2 W mem md U b m HAR FH Hsub Hb Hfresh Hm r Hr.
destruct (FH r Hr) as (E16 & m' & Hm' & Hreq). destruct r as [q s]. cbn [fst snd] in *. subst s.
assert (Hne : (b, m) <> (q, m')) by (intros E; rewrite E in Hfresh; exact (Hfresh Hm')).
pose proof (sep_blocks tfibsegs B LAWS ly2 S2 W mem md b m q m' HAR Hb (Hsub _ Hm') Hne) as D.
unfold zdisjoint in *. cbn [fst snd] in *. lia.
Qed.
(* own()'s poison: the contract's premise upoison_ok ((b, 16) :: U) for the fresh block's head *)
Lemma upoison_ok_new_head : forall ly S U b m,
  FSP.upoison_ok B ly S U -> In (b, m) (ablocks B ly S) -> b mod 8 = 0 -> 16 <= 8 * (req_size m / 8) ->
  (forall r, In r U -> zdisjoint (b, 16) r) -> FSP.upoison_ok B ly S ((b, 16) :: U).
Proof.
intros ly S U b m [F PW] Hb B8 H16 DJ. split.
- constructor; [|exact F]. cbn [fst snd]. split; [exact B8|]. split; [lia|]. split; [reflexivity|].
  exists b, m. split; [exact Hb|]. split; lia.
- cbn [pairwise]. split; [apply Forall_forall; exact DJ | exact PW].
Qed.
(* own() adds the head at the END of U (the spec's U ++ [(res - HEAD, HEAD)]); poison conses it at the front, so ARU
   is carried across with FSupoisonU.ARU_perm + Permutation_cons_append *)
Lemma fs_heads_snoc : forall ly S ly2 S2 U b m,
  FSupoisonU.fs_heads B ly S U -> (forall x, In x (ablocks B ly S) -> In x (ablocks B ly2 S2)) ->
  In (b, m) (ablocks B ly2 S2) -> 16 <= req_size m -> FSupoisonU.fs_heads B ly2 S2 (U ++ [(b, 16)]).
Proof.
intros ly S ly2 S2 U b m FH Hsub Hb Hm r Hr. apply in_app_or in Hr as [Hr | [<- | []]].
- destruct (FH r Hr) as (E16 & m' & Hm' & Hreq). split; [exact E16|]. exists m'. split; [apply Hsub; exact Hm' | exact Hreq].
- cbn [fst snd]. split; [reflexivity|]. exists m. split; [exact Hb | exact Hm].
Qed.

(* ---- fuzz_free p = 0 arm (alloc.c:111-112): prologue 0x82d40..0x82d50 (frame, save ra/s0/s1/s2), beqz a0 at 0x82d54
   taken (a0 = p = 0) to the epilogue 0x82e20..0x82e34 (restore, ret). The p = 0 path loads NO static and NO shadow base
   (beqz precedes the GOT load at 0x82d5c), writes only its frame and makes NO call, so FP = [] and U' = U.
   ENTRY: the plain FSW_K.fsw_entry (the frame only), NOT FSW_statics.fsw_entryTS: fss0TS declares the four statics as
   WRITABLE regions, and awr_ok over a writable image region needs awr_byte's static arm AND FS_PSTAT_FP in FP, which
   this arm's FP = [] can never give. The p <> 0 arm (which writes g_live) takes fsw_entryTS. This lemma is the p = 0
   branch of fuzz_free_spec, used directly by that walk. ---- *)
Lemma fsw_fuzz_free_null :
  forall ly S U (W : world tfibsegs) regs mem md ch live peak cnt fail,
  fpreU tfibsegs B STK_fuzz_free ly S U W regs mem md ch ->
  FSupoisonU.fs_heads B ly S U ->
  getr regs 10 = w64 0 ->
  fs_glob tfibsegs W mem live peak cnt fail ->
  SRr tfibsegs W (cfg_at tfibsegs A_fuzz_free regs mem md)
    (apost_baseU tfibsegs B STK_fuzz_free [] regs ly S W mem md 0 U U
       (fun ly' S' W' regs' mem' md' =>
          ablocks B ly' S' = ablocks B ly S /\ FSupoisonU.fs_heads B ly' S' U /\
          fs_glob tfibsegs W' mem' live peak cnt fail)).
Proof.
intros ly S U W regs mem md ch live peak cnt fail HPRE FH H10 HGL.
pose proof HPRE as (HAP & HRO).
pose proof (fsw_ARU B STK_fuzz_free ly S U W regs mem md ch HAP) as HARU.
pose proof HAP as (HAN & _ & _).
pose proof HAN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (fsw_sp B STK_fuzz_free ly S U W regs mem md ch HAP) as (Hal16 & Hceil & H47 & HS0).
assert (FS : STK_fuzz_free = 16416) by reflexivity.
pose proof (fsw_entry B STK_fuzz_free 32 ly S U W regs mem md ch A_fuzz_free HAP
  ltac:(rewrite FS; lia) ltac:(vm_compute; reflexivity)) as HS.
pose proof (ajournal_init tfibsegs B STK_fuzz_free [] ly S W regs (FSP.unpoison U mem) md ch HAN) as HJ.
set (E := Ereg regs []) in HS.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl); reflexivity).
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs [] 1 1%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 0) by (subst E; rewrite (ew_Ereg_nat regs [] 10 10%bv eq_refl); exact H10).
unfold cfg_at. change (w64 A_fuzz_free) with (Z_to_bv 64 A_fuzz_free).
(* 0x82d40..0x82d50: frame, save ra / s0 / s1 / s2; stops at beqz a0 *)
fsw_aj_runU tbl_ff_ok HS HJ HARU.
{ awr_ok_tac. all: exact Usp. }
assert (SB1 : same_below mem (ms_mem ms) alloc_ceiling).
{ change (frame_of E [fstk 32] mem (ms_mem ms)) in HF.
  apply (same_below_frame1 E (fstk 32) mem (ms_mem ms) alloc_ceiling HF).
  all: first [ solve [zle] | solve [cbn [fstk YP09.r_base YP09.r_wlo base_val]; rewrite Usp; lia] ]. }
clear HF HFr HG.
(* 0x82d54 beqz a0: taken, since a0 = p = 0 *)
eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 10 0) (b := SLit 0) (1 := HS).
(* the two branch continuations of SRr_sym_branch: taken (p = 0), then not taken (refuted) *)
- intros Hb HS2. clear HS.
  (* 0x82e20..0x82e30: restore ra / s0 / s1 / s2, sp; stops at ret 0x82e34 *)
  fsw_aj_runU tbl_ff_ok HS2 HJ HARU.
  { awr_ok_tac. all: exact Usp. }
  assert (SB2 : same_below (ms_mem ms) (ms_mem ms0) alloc_ceiling).
  { cbn [add_cond ss_mem] in HF.
    eapply (same_below_frame1 E _ (ms_mem ms) (ms_mem ms0) alloc_ceiling HF).
    all: first [ solve [zle] | solve [cbn [YP09.r_base YP09.r_wlo base_val]; rewrite Usp; lia] ]. }
  rreg HS2 (1%bv : bv 5) R1.
  rewrite ?wvb_collapse in HJ.
  unfold apost_baseU.
  eapply (fsw_retU B tbl_ff tbl_ff_ok).
  all: first [ solve [exact HS2] | solve [exact HJ] | solve [exact HARU]
             | solve [lazymatch goal with |- ss_resv _ = None => reflexivity end]
             | solve [lazymatch goal with |- clookup _ _ = Some _ => vm_compute; reflexivity end]
             | solve [rewrite R1, ?fsw_SOff0, E1; exact Hra]
             | solve [eapply (aregs_preserved_of_st_ok tfibsegs _ E _ _ regs [] HS2);
                      first [ solve [apply env_agree_refl]
                            | solve [lazymatch goal with |- forallb _ _ = true => vm_compute; reflexivity end] ]]
             | solve [intros mat1; cbv beta; split; [reflexivity|]; split; [exact FH|];
                      apply (fs_glob_below W mem);
                      first [ solve [exact (same_below_trans _ _ _ _ SB1 SB2)] | solve [exact HGL] ]] ].
- intros Hb _. exfalso. rewrite branch_eq_U, (U_atom E 10 0 E10 ltac:(lia)), U_lit in Hb by lia. discriminate Hb.
Qed.

End c.
