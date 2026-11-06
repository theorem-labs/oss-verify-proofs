(* Satisfiability witness of reply's driver hypothesis NS_START (KF-COUNT #7), ONE copy for both images.
   The hypothesis is the driver's (a Theorem Labs lane for image A: lib/A/AD1pcf.v, AD1qcf.v, AD2dcf.v on
   a working branch 458a2b5da2a; a Theorem Labs lane mirrors it for image B):
     Hypothesis NS_START : NS init_state + 12 + 4 * XNMAX <= NRUN.
   12 is image A's measured prefix count before the loop's first library call (1 input-buffer malloc, at most 10
   grows, 1 payload malloc) and 4 * XNMAX pays the loop's at most 4 calls; image B takes its own prefix count.
   So the count PRE is an argument here: image A cites it at PRE := 12, image B at its own constant.
   The instance takes NS := nsec_cf, the run's count of granted secondary entries (lib/Reusable/YGcfNames.v).
   Why the start, and not a state fact: nsec_cf counts st_secs, which only grows (secs_ext), so no fact about a
   later state bounds it; at init_state the history is EMPTY.  init_state (lib/Reusable/YG00.v) builds its st_secs
   field, mkA's fifth argument, as [], so nsec_cf init_state = 0: the cf layer's nsec_cf_init (lib/Reusable/YGcfNsec.v).
   It names only nsec_cf, init_state and Z, so it is image-free; it is reply's own (the prefix count is the driver's,
   not a cf model fact), so it is not in the cf layer (a Theorem Labs lane 13:57Z). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YGcfNames YGcfNsec.
Open Scope Z_scope.

(* NS_START at NS := nsec_cf, for every prefix count PRE, per-call bound XNMAX and run bound NRUN with
   PRE + 4 * XNMAX <= NRUN; at PRE := 12 its conclusion is image A's NS_START text token for token *)
Lemma ns_start_wit : forall (PRE XNMAX NRUN : Z),
  PRE + 4 * XNMAX <= NRUN -> nsec_cf init_state + PRE + 4 * XNMAX <= NRUN.
Proof. intros PRE XNMAX NRUN H. rewrite nsec_cf_init. lia. Qed.

Print Assumptions nsec_cf_init.
Print Assumptions ns_start_wit.
