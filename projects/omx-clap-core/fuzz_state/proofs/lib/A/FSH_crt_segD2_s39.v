(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YCbo.v, with its module paths and module names changed; 248 of its 306 lines of code are new or changed and 2409 lines of the source are left out. *)
(* fs ASan, check_round_trip (fs.asan 0x81a9c), lane D2, SEGMENT 39: the second `__wrap_free` thunk.
   rule 24: proves no function (kind: segment lemma of check_round_trip's walk, PORTED from a working branch
   d25a984c903 proofs/omx-clap-core/fuzz_state/lib/A/Prog/check_round_trip_sd24.v, stage St24 - the same __wrap_free
   thunk at 0x82350, freeing the raw interceptor block `same`).

   The code (MEASURED, crt_tbl): 0x8234c `mv a0, s8` (s8 = atom 24 = same, the second __wrap_malloc block,
   0x81cb8) and 0x82350 `jal __wrap_free` (PC_free 0x53070), returning to 0x82354, the tail's entry (crt_ssT).
   What St24 proves, restated in S0's ajournal / ARU / U form:
   - the block freed is (same, nsame), a RAW malloc block: __wrap_malloc owns no user-poisoned head for it, so U
     (a permutation of the entry's c_U here, crtD2_INV_39) has no range in it (crtD2_no_head + crtD2_free_outside);
   - the free keeps U, the fake frame and the real stack: it is a runtime call with a CALL-RELATIVE journal of its
     own (crtD2_free_sub, the callee half of FSW_malloc_free.fsw_aj_freeU) whose footprint is the freed block only,
     so the base's crt_seg_call / crt_after_call put crt's journal, ARU, the frame and the boundary state back;
   - after it the walk holds the entry's blocks again (up to order), g_live / g_count are untouched (the statics
     are not in the free's footprint: fs_img_facts' first conjunct), and the read-only image is re-derived (IMG).
   The tail's invariant crt_INV_T states U3 = c_U syntactically; the walk has only a permutation. crtD2_tail_perm
   transports crt_tail across that gap; it rewrites `unpoison U3 mem = unpoison (c_U cx) mem`, which
   FSupoisonU.unpoison_perm gives pointwise, with FunctionalExtensionality (already in the development's
   assumptions: crt_seg_call's own Print Assumptions lists functional_extensionality_dep).

   The trace premise `In (call_trace0 (pc_free_ra0 ..) regs ch) (as_universe B)` of fsw_aj_freeU is NOT taken:
   fsw_aj_freeU never uses it (afree_realizesU and ml_free admit any trace once st_nev < EV_MAX), and
   crtD2_free_sub, which is fsw_aj_freeU's proof stopped at its callee journal, does not state it. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP03 YP0l YP0k YP06 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG08 YG0d YG05 YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w SetShadowDefU FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_rres FSW_ret FSW_frame
FSW_frame3 FSW_K3 FSW_crt_tbl FSH_Fn_reader FSH_Fn_writer FSH_Fn_alloc FSH_Fn_crt FSH_crt_base FSH_crt_site
FSH_crt_room FSH_crt_segD FSH_crt_segD2.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec HState PjStruct.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================= the free's callee journal =================
   FSW_malloc_free.fsw_aj_freeU's proof (lines 313-379 at S0), stopped at its call-relative journal HJ1 instead of
   composing it with the caller's: crt_seg_call's crt_hcall asks the callee half (window [sp - ASTACK, sp), footprint
   the freed block, own = []) and composes it itself (crt_after_call). The premises are the callee's: acall_preU at
   the call and astk_ok of ASTACK there (both from the call site's fpreU ASTACK, crtD2_acall_preU below), the event
   room, the block, U outside it, a0 and ra. Same script, no bridge. ================= *)
Section fsub. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Hypothesis FS_ENV : api_env tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd := fs_segs_low.
Local Ltac zle := lazymatch goal with |- (_ <= _)%Z => zlia | |- (_ < _)%Z => zlia end.

Lemma crtD2_free_sub : FSupoisonU.afree_realizesU tfibsegs B ->
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

(* the callee's acall_preU and its ASTACK window, from the call site's fpreU at STK = ASTACK (crt_hcall hands it):
   afn_pre's stack facts give acall_pre's, its achain gives chain_pre (YCbq.achain_chain_pre), and the event room
   gives aregime and, with afn_pre's qtight, the model room (as fsw_aj_freeU builds HPRE0) *)
Lemma crtD2_acall_preU : forall ly S U (W : world tfibsegs) regs mem md ch,
  fpreU tfibsegs B ASTACK ly S U W regs mem md ch -> st_nev S < EV_MAX ->
  FSupoisonU.acall_preU tfibsegs B ly S U W regs mem md ch /\ astk_ok ASTACK ly (spZ regs).
Proof.
intros ly S U W regs mem md ch (((HAR & Hret & Hra & Hgp & Htp & Hstk & Hpres & Hach & Hqt) & OK & PO) & _) Hev.
pose proof Hstk as (H16 & H0 & Hceil & Hlo & Hhi & H47 & Hbot & Htop & Htop2).
split; [|exact Hstk].
split; [|split; [exact OK | exact PO]].
split; [exact HAR|]. split; [exact (aregime_small _ Hev)|]. split; [exact Hret|].
split; [exact H16|]. split; [lia|]. split; [lia|]. split; [exact Hhi|].
split; [exact Hpres|]. split; [exact Hgp|]. split; [exact Htp|].
split; [apply (achain_chain_pre ly _ (spZ regs) (s0Z regs) ch regs Hach); [lia | reflexivity | exact Hra]|].
exact (conj Hqt (mroom_of_regime (as_universe B) S (am_wf _ _ _ _ (proj1 HAR)) (aregime_to_mid S (aregime_small _ Hev))
  (qtight_qloose S Hqt))).
Qed.
End fsub.

(* ================= what a free keeps, and what the next boundary re-derives ================= *)
Section keep. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Hypothesis IMG : fs_img_facts tfibsegs B.

(* fuzz/alloc.c's statics across a callee whose footprint holds no image byte: the boundary memory m3 agrees with
   the call memory below alloc_ceiling (the store-free run, crt_hcall's same_below), and the callee journal's image
   clause keeps every static (they are FS_PSTAT_FP's four cells, neither owned statics nor errno: fs_img_facts' first
   conjunct; outside the footprint; sink-closed footprint), read through the unpoisoned views (statics lie below the
   shadow band, crt_ush_low) *)
Lemma crtD2_glob_call : forall ly3 S3 U3 (W3 : world tfibsegs) (m3 memC : word -> option byte) mdC ly2 S2 U2
    (W2 : world tfibsegs) mem2 md2 STKc sp FPc kc live peak cnt fail,
  ARU tfibsegs B ly3 S3 U3 W3 memC mdC -> ARU tfibsegs B ly2 S2 U2 W2 mem2 md2 ->
  ajournal tfibsegs B STKc sp FPc ly3 S3 W3 (unpoison U3 memC) mdC [] ly2 S2 W2 (unpoison U2 mem2) md2 kc ->
  same_below m3 memC alloc_ceiling ->
  (forall a, in_img tfibsegs a -> ~ inFP FPc a) -> ~ YI16.sink_open_fp FPc ->
  fs_glob tfibsegs W3 m3 live peak cnt fail -> fs_glob tfibsegs W2 mem2 live peak cnt fail.
Proof.
intros ly3 S3 U3 W3 m3 memC mdC ly2 S2 U2 W2 mem2 md2 STKc sp FPc kc live peak cnt fail HARU3 HARU2 HJc HSB HFPI Hcl
  (G1 & G2 & G3 & G4 & R).
pose proof (@alloc_ceiling_value rc) as (HCV & _).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
assert (KS : forall a, (G_FAIL <= a < G_FAIL + 8 \/ G_LIVE <= a < G_LIVE + 8 \/ G_PEAK <= a < G_PEAK + 8 \/
    G_COUNT <= a < G_COUNT + 8) -> aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W3) m3 a).
{ intros a Ha.
  pose proof (crt_glob_img a Ha) as Hi. pose proof (crt_img_range a Hi) as Hr.
  assert (HP : inFP FS_PSTAT_FP a).
  { unfold FS_PSTAT_FP, G_FAIL, G_LIVE, G_PEAK, G_COUNT in *.
    destruct Ha as [H|[H|[H|H]]];
      [exists (0xa3ca0, 0xa3ca8) | exists (0x5da5c0, 0x5da5c8) | exists (0x5da5e0, 0x5da5e8)
      | exists (0x5da600, 0x5da608)];
      (split; [cbn [In]; tauto | cbn [fst snd]; lia]). }
  destruct (proj1 IMG a HP) as (Hno & Herr).
  assert (Hlow : 0 <= a < SHADOW_OFF) by (unfold SHADOW_OFF; lia).
  rewrite <- (aview_unpoison_out tfibsegs (w_H W2) U2 mem2 a (crt_ush_low B _ _ _ _ _ _ a HARU2 Hlow)).
  rewrite (F3 a Hi Hno Herr (HFPI a Hi) (fp_spares_closed FPc a Hcl)).
  rewrite (aview_unpoison_out tfibsegs (w_H W3) U3 memC a (crt_ush_low B _ _ _ _ _ _ a HARU3 Hlow)).
  apply (aview_below (w_H W3) m3 memC alloc_ceiling a HSB). lia. }
assert (VB : forall g v, (G_FAIL <= g /\ g + 8 <= G_FAIL + 8 \/ G_LIVE <= g /\ g + 8 <= G_LIVE + 8 \/
    G_PEAK <= g /\ g + 8 <= G_PEAK + 8 \/ G_COUNT <= g /\ g + 8 <= G_COUNT + 8) ->
  val_mem tfibsegs (mrestrict (w_H W3) m3) g 8 v -> val_mem tfibsegs (mrestrict (w_H W2) mem2) g 8 v).
{ intros g v Hg Hv kk Hkk.
  rewrite (mbyte_of_aview tfibsegs (w_H W3) (w_H W2) m3 mem2 (g + Z.of_nat kk) (KS (g + Z.of_nat kk) ltac:(lia))).
  exact (Hv kk Hkk). }
unfold fs_glob, fs_glob_at in *.
split; [apply VB; [lia | exact G1]|]. split; [apply VB; [lia | exact G2]|].
split; [apply VB; [lia | exact G3]|]. split; [apply VB; [lia | exact G4]|]. exact R.
Qed.

(* the event room of the walk at a boundary whose invariant leaves `t` ticks of room: st_nev stays below EV_MAX *)
Lemma crtD2_nev : forall cx k ly3 S3 (W3 : world tfibsegs) mem3 md3 t,
  crt_base B cx ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 mem3 md3 k ->
  1 <= t -> k + t <= EV_check_round_trip -> st_nev S3 < EV_MAX.
Proof.
intros cx k ly3 S3 W3 mem3 md3 t HB HJ Ht Hk.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HEV & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
lia.
Qed.
End keep.

(* fs_heads after freeing a block that has no head in U: every head still names a live block *)
Lemma crtD2_heads_free : forall B ly S ly2 S2 U l1 l2 p n,
  FSupoisonU.fs_heads B ly S U -> ~ In (p, 16) U ->
  ablocks B ly S = l1 ++ (p, n) :: l2 -> ablocks B ly2 S2 = l1 ++ l2 ->
  FSupoisonU.fs_heads B ly2 S2 U.
Proof.
intros B ly S ly2 S2 U l1 l2 p n FH Hnot E1 E2 r Hr.
destruct (FH r Hr) as (E16 & m & Hm & M16). split; [exact E16|]. exists m. split; [|exact M16].
rewrite E2. rewrite E1 in Hm. apply in_app_or in Hm as [Hm|[Hm|Hm]].
- apply in_or_app. left. exact Hm.
- exfalso. injection Hm as Ep En. apply Hnot. destruct r as [q s]. cbn [fst snd] in *. subst. exact Hr.
- apply in_or_app. right. exact Hm.
Qed.

(* g_count's whole increment over crt's walk to 0x82354, BY TRACE (base v33 states CNT_82268 over pj_write's own
   writer state crt_wst and pj_parse's trace crt_TR): CNT_822ac = CNT_82218 + wcalls (crt_wst cx) + |crt_TR cx| + 1
   = 17 + (at most 3) + 15 + 1 <= 36 of the released 68 (FSH_crt_room.v crtr_K18, crtr_wcalls, crtr_TR15; the frees
   and the two thunks never bump it) *)
Local Strategy expand [CNT_822ac CNT_82268].
Section cnt. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Lemma crtD2_cnt_le : forall cx, crt_base B cx -> CNT_822ac cx <= crt_allocs.
Proof.
intros cx HB.
destruct (crtr_K18 cx) as (_ & EC18).
pose proof (crtr_wcalls B cx HB) as HW.
destruct (crtr_TR15 (crt_es cx)) as (_ & ETR).
unfold CNT_822ac, CNT_82268, crt_TR. rewrite EC18, ETR.
unfold crt_allocs, CRT_ALLOCS. lia.
Qed.
End cnt.

(* ================= segment 39 ================= *)
(* the call-site state of segment 39, MEASURED by the engine from crt_ss2 0x8234c (the saved words and the s1 slots):
   `mv a0, s8` then `jal __wrap_free`, no store; a0 = atom 24 (same), ra = 0x82354 *)
Definition crtD2_ss39c : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL PC_free (crt_ss2 0x8234c)).
Lemma crtD2_seg39c_run : sym_run_toN tfibsegs crt_tbl FUEL PC_free (crt_ss2 0x8234c) = (crtD2_ss39c, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crtD2_ss39c_site : crt_csite crtD2_ss39c PC_free 0x82354.
Proof. unfold crt_csite. repeat split; vm_compute; reflexivity. Qed.
Lemma crtD2_ss39c_regs : sr_get (ss_regs crtD2_ss39c) 10%bv = SOff 24 0 /\ sr_get (ss_regs crtD2_ss39c) 24%bv = SOff 24 0.
Proof. split; vm_compute; reflexivity. Qed.

Section s39. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Hypothesis RT : CrtRt B.
Hypothesis HENV : api_env tfibsegs B.
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* crt_INV_T with its U clause read up to order: what the walk holds at 0x82354 *)
Definition crtD2_INV_Tp : crt_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  Permutation U3 (c_U cx) /\ crt_budget_T k /\ crt_Q B cx ly3 S3 W3 (ms_regs ms3) (ms_mem ms3) md3.

(* the transport: crt_from at crt_INV_T gives crt_from at crt_INV_T up to the order of U. crt_from's premises read
   U3 only through `unpoison U3 mem` (the journal) and ARU; ARU moves by FSupoisonU.ARU_perm, and the journal by
   rewriting the memory function `unpoison U3 mem = unpoison (c_U cx) mem`, equal pointwise by
   FSupoisonU.unpoison_perm, as functions by FunctionalExtensionality.functional_extensionality. *)
Lemma crtD2_tail_perm : forall ss, crt_from SK B ss (crt_INV_T B) -> crt_from SK B ss crtD2_INV_Tp.
Proof.
intros ss H cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU HFR (HP & Hk & HQ) HS.
assert (EU : unpoison U3 (ms_mem ms3) = unpoison (c_U cx) (ms_mem ms3)).
{ apply functional_extensionality. intros w. apply unpoison_perm. exact HP. }
apply (H cx E k ly3 S3 (c_U cx) W3 ms3 md3 HB HE).
- rewrite <- EU. exact HJ.
- exact (ARU_perm tfibsegs B LAWS ly3 S3 U3 (c_U cx) W3 (ms_mem ms3) md3 HP HARU).
- exact HFR.
- split; [reflexivity|]. split; [exact Hk | exact HQ].
- exact HS.
Qed.

(* the free of `same`: from crtD2_INV_39 at the call, the callee half of the free, and crtD2_INV_Tp after it *)
Lemma crtD2_hcall39 : crt_hcall SK B crtD2_ss39c PC_free 0x82354 ASTACK (crtD2_INV_39 B) crtD2_INV_Tp.
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 regsC memC mdC HB HE HINV HJ HARU Hfr HSB RG HPRE HFRL HTOP.
destruct HINV as (same & nsame & peak & cnt & E24 & HBL & HHD & HFH & HGL & HRV & Hcnt & Hk).
unfold crtD2_blocks, crtD2_heads in HBL, HHD. rewrite app_nil_r in HHD.
pose proof (crt_fr_free B RT) as (EPC & AFREE).
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARU) as HAR.
pose proof HB as (_ & HFH0 & _).
destruct crtD2_ss39c_regs as (G10 & G24).
assert (R10 : YK11.getr regsC 10%bv = Z_to_bv 64 same) by (rewrite RG, G10, fsw_SOff0; exact E24).
(* the block, its absence from the entry, and U outside it *)
assert (Hin : In (same, nsame) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HBL)). apply in_or_app. right. left. reflexivity. }
assert (Hnin0 : ~ In (same, nsame) (ablocks B (c_ly cx) (c_S cx))).
{ intros X. apply (crtD2_once B ly3 S3 W3 _ mdC (ablocks B (c_ly cx) (c_S cx)) [] (same, nsame) HAR HBL).
  rewrite app_nil_r. exact X. }
assert (Hnot : ~ In (same, 16) U3).
{ apply (crtD2_no_head B ly3 S3 W3 _ mdC U3 (c_U cx) (ablocks B (c_ly cx) (c_S cx)) [] same nsame HAR HFH HBL HHD).
  intros q Hq. destruct (crtD2_head_of_U B (c_ly cx) (c_S cx) (c_U cx) q HFH0 Hq) as (m & Hm & _).
  exists m. rewrite app_nil_r. exact Hm. }
pose proof (crtD2_free_outside B ly3 S3 U3 W3 memC mdC same nsame HARU HFH Hin Hnot) as Hout.
destruct (al_blocks _ _ LAWS ly3 S3 W3 _ mdC same nsame HAR Hin) as (_ & Hs4096 & _).
(* the callee's precondition *)
assert (Hev : st_nev S3 < EV_MAX)
  by (apply (crtD2_nev SK B cx k ly3 S3 W3 _ mdC CRT_EV_WRAP HB HJ); [unfold CRT_EV_WRAP; lia | exact Hk]).
destruct (crtD2_acall_preU B ly3 S3 U3 W3 regsC memC mdC (crt_ch1 cx) HPRE Hev) as (HPREU & HstkC).
exists [(same, same + req_size nsame)], 1. eexists.
split.
{ change (cfg_at tfibsegs PC_free regsC memC mdC)
    with (mkCfg (mkst regsC (Z_to_bv 64 PC_free) memC (seg_rom tfibsegs)) mdC).
  rewrite <- EPC.
  exact (crtD2_free_sub SK B HENV ML AFREE ly3 S3 U3 W3 regsC memC mdC same nsame (YK11.getr regsC 1%bv) (crt_ch1 cx)
    HPREU HstkC Hev Hin Hout R10 eq_refl). }
split.
{ (* the footprint is a block the walk made: in_tmp_block *)
  intros a (rg & [<-|[]] & Ha). cbn [fst snd] in Ha. right. left.
  exists same, nsame. split; [exact Hin|]. split; [exact Hnin0 | exact Ha]. }
split.
{ (* the flag word is a frame byte, apart from every block *)
  intros a Ha (rg & [<-|[]] & Ha'). cbn [fst snd] in Ha'.
  pose proof HJ as (_ & Hly & _).
  pose proof (crt_F_ly cx _ ly3 Hly) as EF.
  assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfr; left; reflexivity).
  pose proof (sep_block_frame tfibsegs B LAWS ly3 S3 W3 _ mdC same nsame 3 (c_pos cx) HAR Hin Hin3) as D.
  rewrite EF, crt_frame3 in D. rewrite crt_frame3 in Ha. unfold zdisjoint in D. cbn [fst snd] in D. lia. }
intros W' c' (ly2 & S2 & regs2 & mem2 & md2 & -> & HJc & OK2 & PO2 & HP & (l1 & l2 & Esp & E2)).
exists ly2, S2, U3, regs2, mem2, md2.
split; [reflexivity|]. split; [exact HJc|]. split; [exact OK2|]. split; [exact PO2|]. split; [exact HP|].
intros HJ' HARU'.
unfold crtD2_INV_Tp, crt_budget_T, crt_Q. cbn [ms_regs ms_mem mkst].
split; [exact HHD|].
split; [unfold CRT_EV_WRAP in Hk; lia|].
split.
{ rewrite E2. rewrite Esp in HBL. apply Permutation_app_inv in HBL. rewrite app_nil_r in HBL. exact HBL. }
split.
{ exists cnt. split; [pose proof (crtD2_cnt_le B cx HB); lia|]. exists peak.
  apply (crtD2_glob_call SK B IMG ly3 S3 U3 W3 (ms_mem ms3) memC mdC ly2 S2 U3 W' mem2 md2 ASTACK (spZ regsC)
    [(same, same + req_size nsame)] 1 _ _ _ _ HARU HARU' HJc HSB); [| | exact HGL].
  - intros a Hi (rg & [<-|[]] & Ha). cbn [fst snd] in Ha.
    exact (blk_img tfibsegs B LAWS ly3 S3 W3 _ mdC same nsame a HAR Hin Ha Hi).
  - apply sink_closed_pos. constructor; [cbn [fst]; lia | constructor]. }
exact (crt_rom SK B IMG cx (k + 1) ly2 S2 U3 W' mem2 md2 HB HJ' HARU').
Qed.

(* ---- segment 39: crt_from at the tail's entry under crt_INV_T gives crt_from at 0x8234c under crtD2_INV_39 ---- *)
Lemma crtD2_seg39 : crt_from SK B crt_ssT (crt_INV_T B) -> crt_from SK B crt_ss39 (crtD2_INV_39 B).
Proof.
intros NEXT.
exact (crt_seg_call SK B 0x8234c PC_free 0x82354 crtD2_ss39c (crtD2_INV_39 B) crtD2_INV_Tp ASTACK
  crtD2_seg39c_run crtD2_ss39c_site ltac:(lia) ltac:(reflexivity) (proj2 (proj2 crtD2_stk_pos)) crtD2_stk_free
  crtD2_hcall39 (crtD2_tail_perm crt_ssT NEXT)).
Qed.
End s39.
