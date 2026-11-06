(* diginet_cursor_init_cgW (image B): Theorem decode_diginet_cursor_init_cg_holds, the leaf statement
   lib/B/Prog/diginet_cursor_init_cg.v decode_diginet_cursor_init_cg read at this unit's model (DgnDecodeBCg.v
   decode_leaf_wr_at), for every record B: the premise diginet_body_check's statement takes for its call of
   diginet_cursor_init. It composes three closed pieces:
   - decode_diginet_cursor_init_cg_of_F (lib/B/Prog/diginet_cursor_init_cg.v): the footprint contract gives the leaf
     statement, given the kit's translation (its Section hypothesis HGLUE);
   - LeafCgClose.v dec_b_leaf_glue with dec_b_kit_aview_ext and dec_b_kit_aview_some: that translation at this
     unit's decode_leaf_wr_at instance;
   - diginet_cursor_init_F.v diginet_cursor_init_holds_F: the footprint walk of diginet_cursor_init. *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YM05 YG0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_cursor_init_F_c diginet_cursor_init_F.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require DgnTransportBCg LeafCgClose diginet_cursor_init_cg.
Module PC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.DgnTransportBCg.
Module LCC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.LeafCgClose.
Module LCI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_cursor_init_cg.

Theorem transport_diginet_cursor_init_cg_holds : forall (rc : YM05.RunCeil) (B : asyms) (fx : YK11.FPState),
  @PC.transport_leaf_wr_at rc B (@LCI.transport_diginet_cursor_init_cg) fx.
Proof.
  intros rc B fx.
  pose proof (LCC.dec_b_leaf_glue B rc fx LCC.dec_b_kit_aview_ext LCC.dec_b_kit_aview_some) as G.
  unfold PC.transport_leaf_wr_at in G |- *.
  exact (@LCI.transport_diginet_cursor_init_cg_of_F fx _ _ _ _ _ _ _ _ _ _ _ _ _ _ G diginet_cursor_init_holds_F).
Qed.
