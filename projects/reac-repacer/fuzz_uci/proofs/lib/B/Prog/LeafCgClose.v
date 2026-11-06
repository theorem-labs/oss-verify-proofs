(* Modified by Theorem Labs: made from proofs/libreac/fuzz_decode/lib/B/Prog/LeafCgClose.v at recipes commit 88154566652a (a recipes commit newer than the unit's base 25e3d17bdb50) for reac-repacer/fuzz_uci's image B: the three kit rows of lib/B/UciBClose.v's block at their agreed names and statements (H_KIT_AVIEW_EXT, H_KIT_AVIEW_SOME at the image's segments ucisegsB0; H_LEAF_GLUE at the record UciB, lib/B/YD2l.v:17, read at lib/B/Prog/UciCg.v's uci_leaf_wr_at); fuzz_uci has no float-state leaf, so decode's H_LEAF_GLUE_FX row is not copied; module paths changed. *)
(* LeafCgClose: the three kit / glue rows of lib/B/UciBClose.v, each at its exact type, image B. The two aview facts
   are LeafCgFacts.v's aview_ext_stmt_YG0n / aview_some_stmt_YG0n (any segs); the glue row is LeafCgGlue.v's
   leaf_cg_of_evtF read at UciCg.v's uci_leaf_wr_at instance, with the kit facts of LeafCgFacts.v as its premises. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK11 YK0s YM05 YK04 YA0n YG0f YG00 YG0d YG0n.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import UciBTFIB YD2l.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog Require LeafCgKit LeafCgFacts LeafCgGlue UciCg.

Module LK := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog.LeafCgKit.
Module LF := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog.LeafCgFacts.
Module LG := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog.LeafCgGlue.
Module PCs := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog.UciCg.

Lemma H_KIT_AVIEW_EXT : @LK.aview_ext_stmt (aview ucisegsB0).
Proof. exact (LF.aview_ext_stmt_YG0n ucisegsB0). Qed.

Lemma H_KIT_AVIEW_SOME : @LK.aview_some_stmt (aview ucisegsB0).
Proof. exact (LF.aview_some_stmt_YG0n ucisegsB0). Qed.

Lemma H_LEAF_GLUE : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @LK.aview_ext_stmt (aview ucisegsB0) -> @LK.aview_some_stmt (aview ucisegsB0) ->
  @PCs.uci_leaf_wr_at rc UciB (@LK.leaf_cg_of_evtF_stmt) fx.
Proof.
  intros rc fx AE AS. unfold PCs.uci_leaf_wr_at.
  eapply (@LG.leaf_cg_of_evtF fx).
  - apply LF.bridge_evtF_stmt_YA0n.
  - apply LF.SRr_ret_stmt_YA0n.
  - apply LF.AR_frame_stmt_YG0q.
  - apply LF.AR_stack_stmt_YG0s.
  - apply LF.AR_sbm_stmt_YG0q.
  - exact AE.
  - exact AS.
  - apply LF.ret_ok_stmt_YK0s.
Qed.
