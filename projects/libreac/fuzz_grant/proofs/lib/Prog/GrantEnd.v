From OSSVerify.libreac.fuzz_grant Require Statements.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require FrameProof.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require PlainHalts SlotTop LayLink ctrl_lay_block
  reac_box_model_block_c memset memcpy.

(* fuzz_grant plain: the frame (FrameProof), the slot (SlotTop) and every function the slot reaches, except
   reac_box_model_block, whose contract is the one premise left. *)
Theorem plain_halts_of_box : reac_box_model_block_c.reac_box_model_block_contract -> Statements.plain_halts.
Proof.
  intros BOX.
  exact (PlainHalts.plain_halts_of_frame FrameProof.frame_plain_holds
           (SlotTop.grant_slot_sb
              (LayLink.ctrl_lay_block_link
                 (ctrl_lay_block.ctrl_lay_block_holds memset.memset_holds memcpy.memcpy_holds BOX)))).
Qed.

From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require reac_box_model_block build_dt1_single.

Theorem plain_halts_holds : Statements.plain_halts.
Proof.
  exact (plain_halts_of_box
           (reac_box_model_block.reac_box_model_block_holds memset.memset_holds memcpy.memcpy_holds
              (build_dt1_single.build_dt1_single_holds memcpy.memcpy_holds))).
Qed.
