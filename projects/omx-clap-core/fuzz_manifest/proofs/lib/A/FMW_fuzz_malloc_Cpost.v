(* fuzz_malloc, the close of its granted path: from the final state's facts (the journal read with the user-poisoned
   head as the allocator made it, the head holding n, the statics) to fuzz_malloc_spec's second disjunct (fmm_post2). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0s YG0d YG0p YG0q YCbq YC5d YCbp YC20 YI00 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v AF0m AF0x AE2y ACej.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import ACeg.
From OSSVerify.omx_clap_core.fuzz_manifest.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMpoisonS FMPstat FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_fuzz_alloc_base FMW_fuzz_malloc_lem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis TL : TfibLib B.
#[local] Notation LAWS := (AR_laws_ok tfibsegs B).

(* b = res is the block malloc granted (its first 16 bytes are the head); the function returns res + 16 *)
Lemma fmm_post_close : forall ly S (W : world tfibsegs) regs mem md n live peak cnt fail
  ly2 S2 (W2 : world tfibsegs) regs6 mem6 md6 res,
  cnt <> fail -> 1 <= n -> n + 16 < 2 ^ 28 -> live + n < 2 ^ 33 -> cnt + 1 < 2 ^ 33 ->
  0 <= live <= peak -> peak < 2 ^ 33 -> 0 <= cnt -> 0 <= fail < 2 ^ 64 ->
  ajournal tfibsegs B STK_fuzz_malloc (spZ regs) FM_PSTAT_FP ly S W mem md [] ly2 S2 W2 (unpoison [(res, 16)] mem6) md6 1 ->
  upoison_ok B ly2 S2 [(res, 16)] -> upoisoned tfibsegs W2 mem6 [(res, 16)] ->
  ablocks B ly2 S2 = ablocks B ly S ++ [(res, n + 16)] ->
  aregs_preserved regs regs6 -> getr regs6 10 = w64 (res + 16) ->
  val_mem tfibsegs (mrestrict (w_H W2) mem6) res 8 n ->
  val_mem tfibsegs (mrestrict (w_H W2) mem6) G_LIVE 8 (live + n) ->
  val_mem tfibsegs (mrestrict (w_H W2) mem6) G_PEAK 8 (Z.max peak (live + n)) ->
  val_mem tfibsegs (mrestrict (w_H W2) mem6) G_COUNT 8 (cnt + 1) ->
  val_mem tfibsegs (mrestrict (w_H W2) mem6) G_FAIL 8 fail ->
  fmm_post2 B regs ly S W mem md n live peak cnt fail W2 (mkCfg (mkst regs6 (getr regs 1) mem6 (seg_rom tfibsegs)) md6).
Proof using HB TL.
intros ly S W regs mem md n live peak cnt fail ly2 S2 W2 regs6 mem6 md6 res
  Hcf Hn1 Hn28 Hlive Hcnt Hlp Hpk Hc0 Hfail HJ Hok Hpo Hbl Hpres H10 Vh Vl Vp Vc Vf.
pose proof YM05.alloc_ceiling_lt as Hac.
assert (Erq : req_size (n + 16) = n + 16).
{ unfold req_size. destruct (Z.eqb_spec (n + 16) 0); [lia | reflexivity]. }
pose proof HJ as (HAR & _).
assert (Hin : In (res, n + 16) (ablocks B ly2 S2)).
{ rewrite Hbl. apply in_or_app. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS ly2 S2 W2 (unpoison [(res, 16)] mem6) md6 res (n + 16) HAR Hin)
  as (Hal & H4096 & Hceil & _).
rewrite Erq in Hceil.
assert (E1 : res + 16 - HEAD = res) by (unfold HEAD; lia).
unfold fmm_post2, apost_baseU. cbv beta.
split; [exact Hcf|].
exists (res + 16). rewrite E1.
exists ly2, S2, regs6, mem6, md6.
split; [reflexivity|].
split; [rewrite unpoison_nil; exact HJ|].
split; [exact Hok|]. split; [exact Hpo|]. split; [exact Hpres|].
split; [exact H10|].
split; [unfold HEAD; lia|].
split; [rewrite Hbl; reflexivity|].
split.
{ unfold fm_rblock. rewrite E1. split; [exact Hin|]. split; [lia|]. split; [lia|]. exact Vh. }
split.
{ pose proof (YCbq.range_addressable_of_block tfibsegs B LAWS ly2 S2 W2 (unpoison [(res, 16)] mem6) md6
    res (n + 16) (res + 16) n HAR Hin ltac:(lia) ltac:(rewrite Erq; lia)) as RA.
  intros x Hx. destruct (RA x Hx) as (s & Hs & Hsa). exists s. split; [|exact Hsa].
  rewrite <- Hs. symmetry. apply aview_unpoison_out.
  unfold shadow_of_addr. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
  destruct (in_ush [(res, 16)] (SHADOW_OFF + x / 8)) eqn:Eu; [|reflexivity].
  apply in_ush_one in Eu. unfold shadow_addr, SHADOW_OFF in Eu. lia. }
split.
{ intros _.
  pose proof (YCbq.shadow_hull_vis_of_block tfibsegs B LAWS ly2 S2 W2 (unpoison [(res, 16)] mem6) md6
    res (n + 16) (res + 16) n HAR Hin ltac:(lia) ltac:(rewrite Erq; lia) ltac:(lia)) as SH.
  intros s Hs.
  assert (Hs64 : 0 <= s < 2 ^ 64) by (unfold shadow_addr, SHADOW_OFF in Hs; lia).
  destruct (in_ush [(res, 16)] s) eqn:Eu.
  - rewrite (Hpo s Eu). discriminate.
  - intros Hn. apply (SH s Hs). rewrite aview_unpoison_out; [exact Hn|].
    rewrite unsigned_lit_small by exact Hs64. exact Eu. }
unfold fm_glob. split; [exact Vl|]. split; [exact Vp|]. split; [exact Vc|]. split; [exact Vf|].
pose proof (Z.max_spec peak (live + n)). lia.
Qed.

End c.
