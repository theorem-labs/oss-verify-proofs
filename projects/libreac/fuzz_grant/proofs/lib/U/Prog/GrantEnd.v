From OSSVerify.libreac.fuzz_grant Require Statements.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require FrameProof.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require UbsanHalts SlotTop LayLink ctrl_lay_block
  reac_box_model_block_c memset memcpy.

(* fuzz_grant ubsan: the frame (U FrameProof), the slot (U SlotTop) and every function the slot reaches, except
   reac_box_model_block, whose contract is the one premise left. *)
Theorem ubsan_halts_of_box : reac_box_model_block_c.reac_box_model_block_contract -> Statements.ubsan_halts.
Proof.
  intros BOX.
  exact (UbsanHalts.ubsan_halts_of_frame FrameProof.frame_ubsan_holds
           (SlotTop.grant_slot_sb
              (LayLink.ctrl_lay_block_link
                 (ctrl_lay_block.ctrl_lay_block_holds memset.memset_holds memcpy.memcpy_holds BOX)))).
Qed.

From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require reac_box_model_block dt1_head name_field
  build_dt1_single.

Theorem ubsan_halts_holds : Statements.ubsan_halts.
Proof.
  exact (ubsan_halts_of_box
           (reac_box_model_block.reac_box_model_block_holds memset.memset_holds memcpy.memcpy_holds
              dt1_head.dt1_head_holds (name_field.name_field_holds memset.memset_holds)
              (build_dt1_single.build_dt1_single_holds dt1_head.dt1_head_holds memcpy.memcpy_holds))).
Qed.
