(* Modified by Theorem Labs: made from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/A/Prog/LeafCgClose.v at 88154566652a310ff96f54a5442e5c73fdaad090 for reac-repacer/fuzz_uci's image A: the rows are read at fuzz_uci's leaf instance lib/A/Prog/UciCg.v uci_leaf_wr_at (in place of check_round_trip_cg.v dec_leaf_wr_at) and image A's segments ucisegs0 (lib/A/UciTFIB.v, in place of decodesegs0); the float-state glue row (decode's H_LEAF_GLUE_FX) is dropped, because no function fuzz_uci's walks reach writes a float register; names dec_a_ -> uci_a_; module paths changed. *)
(* LeafCgClose: the three leaf-kit facts lib/A/UciClose.v takes (H_KIT_AVIEW_EXT, H_KIT_AVIEW_SOME, H_LEAF_GLUE), each at
   its exact type, image A. The two aview facts are LeafCgFacts.v's aview_ext_stmt_YG0n / aview_some_stmt_YG0n (any
   segs); the glue fact is LeafCgGlue.v's leaf_cg_of_evtF read at UciCg.v's uci_leaf_wr_at instance, with the kit facts
   of LeafCgFacts.v as its premises. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK11 YK0s YM05 YK04 YA0n YG0f YG00 YG0d YG0n.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import UciTFIB.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require LeafCgKit LeafCgFacts LeafCgGlue UciCg.

Module LK := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.LeafCgKit.
Module LF := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.LeafCgFacts.
Module LG := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.LeafCgGlue.
Module PCs := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.UciCg.

Lemma uci_a_kit_aview_ext : @LK.aview_ext_stmt (aview ucisegs0).
Proof. exact (LF.aview_ext_stmt_YG0n ucisegs0). Qed.

Lemma uci_a_kit_aview_some : @LK.aview_some_stmt (aview ucisegs0).
Proof. exact (LF.aview_some_stmt_YG0n ucisegs0). Qed.

Section rows.
Variable B : asyms.

Lemma uci_a_leaf_glue : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @LK.aview_ext_stmt (aview ucisegs0) -> @LK.aview_some_stmt (aview ucisegs0) ->
  @PCs.uci_leaf_wr_at rc B (@LK.leaf_cg_of_evtF_stmt) fx.
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

End rows.
