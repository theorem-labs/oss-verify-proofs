(* LeafCgClose: the three leaf-kit facts lib/A/WireClose.v takes (H_KIT_AVIEW_EXT, H_KIT_AVIEW_SOME, H_LEAF_GLUE), each
   at its exact type, image A. The two aview facts are LeafCgFacts.v's aview_ext_stmt_YG0n / aview_some_stmt_YG0n
   (any segs); the glue fact is LeafCgGlue.v's leaf_cg_of_evtF read at WireCg.v's wire_leaf_wr_at instance, with the
   kit facts of LeafCgFacts.v as its premises. The float-state glue row is not stated: no function fuzz_wire's walks
   reach writes a float register. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0s YM05 YK04 YA0n YG0f YG00 YG0d YG0n.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import WireTFIB.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require LeafCgKit LeafCgFacts LeafCgGlue WireCg.

Module LK := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.LeafCgKit.
Module LF := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.LeafCgFacts.
Module LG := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.LeafCgGlue.
Module PCs := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.WireCg.

Lemma wire_a_kit_aview_ext : @LK.aview_ext_stmt (aview wiresegs0).
Proof. exact (LF.aview_ext_stmt_YG0n wiresegs0). Qed.

Lemma wire_a_kit_aview_some : @LK.aview_some_stmt (aview wiresegs0).
Proof. exact (LF.aview_some_stmt_YG0n wiresegs0). Qed.

Section rows.
Variable B : asyms.

Lemma wire_a_leaf_glue : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @LK.aview_ext_stmt (aview wiresegs0) -> @LK.aview_some_stmt (aview wiresegs0) ->
  @PCs.wire_leaf_wr_at rc B (@LK.leaf_cg_of_evtF_stmt) fx.
Proof.
  intros rc fx AE AS. unfold PCs.wire_leaf_wr_at.
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
