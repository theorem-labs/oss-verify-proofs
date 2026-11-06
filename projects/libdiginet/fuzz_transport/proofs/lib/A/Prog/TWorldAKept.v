(* Image A (fuzz_transport.asan e89be137db17): the world relation kept at the leaf form's view.
   csw_kept: a run that writes only [lo, hi) (munch [(lo, hi)] m m'), with [lo, hi) outside the hull
   [G_HARNESS_LO, G_HARNESS_HI) of the 18 harness globals (A/TransportG.v), keeps tw_at TMAP_A (csw_view m) Bw with
   the same world Bw. csw_view (A/Prog/check_state_wake_c.v) is the machine's view
   fun a => option_map bv_unsigned (mrd rsegs m (wa a)), so this is TWorldA.v's TMAP_A_kept at segs := rsegs.
   Every image-A form-F leaf walk uses it for the post's world fact: the leaf writes only its frame, and its off_stk
   premise puts the frame outside the hull. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA check_state_wake_c.
Import ListNotations.
Open Scope Z_scope.

Lemma csw_kept : forall (m m' : word -> option byte) lo hi Bw,
  tw_at TMAP_A (csw_view m) Bw -> munch [(lo, hi)] m m' ->
  (hi <= TG.G_HARNESS_LO \/ TG.G_HARNESS_HI <= lo) ->
  tw_at TMAP_A (csw_view m') Bw.
Proof. intros m m' lo hi Bw. unfold csw_view. exact (TMAP_A_kept m m' lo hi Bw). Qed.
