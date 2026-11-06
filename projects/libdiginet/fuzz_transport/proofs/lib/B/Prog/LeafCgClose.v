(* LeafCgClose: the three kit / glue rows of the image-B composition (H_KIT_AVIEW_EXT, H_KIT_AVIEW_SOME, H_LEAF_GLUE),
   each at its exact type, image B. The two aview facts are LeafCgFacts.v's aview_ext_stmt_YG0n /
   aview_some_stmt_YG0n (any segs); the glue row is LeafCgGlue.v's leaf_cg_of_evtF read at DgnDecodeBCg.v's
   decode_leaf_wr_at instance, with the kit facts of LeafCgFacts.v as its Section hypotheses. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YM05 YK04 YA0n YG0f YG00 YG0d YG0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require LeafCgKit LeafCgFacts LeafCgGlue DgnTransportBCg.

Module LK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.LeafCgKit.
Module LF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.LeafCgFacts.
Module LG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.LeafCgGlue.
Module PC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.DgnTransportBCg.

Lemma dec_b_kit_aview_ext : @LK.aview_ext_stmt (aview tfibsegs).
Proof. exact (LF.aview_ext_stmt_YG0n tfibsegs). Qed.

Lemma dec_b_kit_aview_some : @LK.aview_some_stmt (aview tfibsegs).
Proof. exact (LF.aview_some_stmt_YG0n tfibsegs). Qed.

Section rows.
Variable B : asyms.

Lemma dec_b_leaf_glue : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @LK.aview_ext_stmt (aview tfibsegs) -> @LK.aview_some_stmt (aview tfibsegs) ->
  @PC.transport_leaf_wr_at rc B (@LK.leaf_cg_of_evtF_stmt) fx.
Proof.
  intros rc fx AE AS. unfold PC.transport_leaf_wr_at.
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
