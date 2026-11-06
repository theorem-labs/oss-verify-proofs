(* LeafCgClose: the four kit / glue rows of lib/B/DecodeBClose.v (H_KIT_AVIEW_EXT, H_KIT_AVIEW_SOME,
   H_LEAF_GLUE, H_LEAF_GLUE_FX), each at its exact type, image B. The two aview facts are LeafCgFacts.v's
   aview_ext_stmt_YG0n / aview_some_stmt_YG0n (any segs); the two glue rows are LeafCgGlue.v's leaf_cg_of_evtF /
   leaf_cg_of_evtF_fx read at check_round_trip_cg.v's dec_leaf_wr_at instance, with the eight kit facts of
   LeafCgFacts.v (a working branch 585df3525ed) as their Section hypotheses. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0s YM05 YK04 YA0n YG0f YG00 YG0d YG0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require LeafCgKit LeafCgFacts LeafCgGlue check_round_trip_cg.

Module LK := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.LeafCgKit.
Module LF := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.LeafCgFacts.
Module LG := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.LeafCgGlue.
Module PC := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.check_round_trip_cg.

Lemma dec_b_kit_aview_ext : @LK.aview_ext_stmt (aview decodesegsB0).
Proof. exact (LF.aview_ext_stmt_YG0n decodesegsB0). Qed.

Lemma dec_b_kit_aview_some : @LK.aview_some_stmt (aview decodesegsB0).
Proof. exact (LF.aview_some_stmt_YG0n decodesegsB0). Qed.

Section rows.
Variable B : asyms.

Lemma dec_b_leaf_glue : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @LK.aview_ext_stmt (aview decodesegsB0) -> @LK.aview_some_stmt (aview decodesegsB0) ->
  @PC.dec_leaf_wr_at rc B (@LK.leaf_cg_of_evtF_stmt) fx.
Proof.
  intros rc fx AE AS. unfold PC.dec_leaf_wr_at.
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

Lemma dec_b_leaf_glue_fx : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @LK.aview_ext_stmt (aview decodesegsB0) -> @LK.aview_some_stmt (aview decodesegsB0) ->
  @PC.dec_leaf_wr_at rc B (@LK.leaf_cg_of_evtF_fx_stmt) fx.
Proof.
  intros rc fx AE AS. unfold PC.dec_leaf_wr_at.
  eapply (@LG.leaf_cg_of_evtF_fx fx).
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
