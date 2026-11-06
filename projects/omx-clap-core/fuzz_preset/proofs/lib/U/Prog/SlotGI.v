From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger GIInit LLVMFuzzerTestOneInput_c.
Import ListNotations.
Local Open Scope Z_scope.

(* #102: omx_G has the seven program-written cells of LedgerCells.GL_cells (four ledger words, g_ran_out, g_most,
   g_own_ran_out, each with its alignment padding) and slot_G = GL_runs, their two maximal runs: the .data run
   g_fail_at, g_most and the .bss run g_own_ran_out, g_ran_out, g_live, g_peak, g_count. Every bound is a LedgerCells name. *)
Lemma slot_G_covers : forall a, in_globals omx_G a <-> in_globals slot_G a.
Proof.
  intros a. unfold in_globals, omx_G, slot_G, GL_runs. split.
  - intros (lo & len & Hin & Hr). cbn [In] in Hin.
    destruct Hin as [E|[E|[E|[E|[E|[E|[E|[]]]]]]]]; injection E as E1 E2; subst lo len;
      [exists GL_OWN_RAN_OUT, 40 | exists GL_OWN_RAN_OUT, 40 | exists GL_OWN_RAN_OUT, 40 | exists GL_FAIL, 16
      | exists GL_OWN_RAN_OUT, 40 | exists GL_FAIL, 16 | exists GL_OWN_RAN_OUT, 40];
      (split; [cbn [In]; tauto | unfold G_LIVE, G_PEAK, G_COUNT, G_FAIL, GL_LIVE, GL_PEAK, GL_COUNT, GL_FAIL,
        GL_RAN_OUT, GL_MOST, GL_OWN_RAN_OUT in *; lia]).
  - intros (lo & len & Hin & Hr). cbn [In] in Hin.
    destruct Hin as [E|[E|[]]]; injection E as E1 E2; subst lo len.
    + destruct (Z.lt_ge_cases a GL_MOST) as [H0|H0]; [exists G_FAIL, 8 | exists GL_MOST, 8];
        (split; [cbn [In]; tauto | unfold G_FAIL, GL_FAIL, GL_MOST in *; lia]).
    + destruct (Z.lt_ge_cases a GL_RAN_OUT) as [H0|H0];
        [exists GL_OWN_RAN_OUT, 8 | destruct (Z.lt_ge_cases a G_LIVE) as [H1|H1];
          [exists GL_RAN_OUT, 8 | destruct (Z.lt_ge_cases a G_PEAK) as [H2|H2];
            [exists G_LIVE, 8 | destruct (Z.lt_ge_cases a G_COUNT) as [H3|H3];
              [exists G_PEAK, 8 | exists G_COUNT, 8]]]];
        (split; [cbn [In]; tauto | unfold G_LIVE, G_PEAK, G_COUNT, GL_LIVE, GL_PEAK, GL_COUNT,
          GL_RAN_OUT, GL_OWN_RAN_OUT in *; lia]).
Qed.

Lemma slot_GI_init : forall (B : malloc_syms) mem,
  ms_segs B = rsegs ->
  (forall a, in_globals slot_G a -> mbyte (ms_segs B) mem a = seg_rom (ms_segs B) (Z_to_bv 64 a)) ->
  omx_GI B 0 mem.
Proof.
  intros B mem HS H. apply omx_GI_init; [exact HS|].
  intros a Ha. apply H. apply slot_G_covers. exact Ha.
Qed.

Lemma slot_G_local : forall (B : malloc_syms), G_local_c B slot_G (omx_GI B).
Proof.
  intros B j m m' Hm (peak & cnt & (W1 & W2 & W3 & W4) & R).
  assert (T : forall g v, In (g, 8) omx_G -> word_mem (ms_segs B) m g v -> word_mem (ms_segs B) m' g v).
  { intros g v Hin W k Hk. rewrite Hm; [apply W; exact Hk|].
    apply slot_G_covers. exists g, 8. split; [exact Hin | lia]. }
  exists peak, cnt. split; [|exact R].
  unfold alloc_words. repeat split; apply T; (cbn [omx_G In]; tauto) || assumption.
Qed.
