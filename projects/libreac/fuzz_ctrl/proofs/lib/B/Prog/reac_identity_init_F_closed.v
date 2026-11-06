(* The closed corollary of reac_identity_init, moved here out of reac_identity_initF.v (a Theorem Labs lane, 07:03Z) so
   that the proof file's Require closure stays free of lib/B/Bz: that chain entered reac_identity_initF.v ONLY
   through this corollary's Require of asan_memsetF (-> lib/B/BzBridge, lib/B/BzCallBridge -> lib/B/Bz/Lib). The
   corollary keeps its exact name and statement; only its module changed.

   With no hypothesis left: the footprint statement of reac_identity_init at the callee contract its owner proves
   for this image -- a Theorem Labs lane's asan_memset_holds_F (lib/B/Prog/asan_memsetF.v), at this image's plain memset
   proof memset_holds (lib/B/Prog/memset.v). *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_identity_initF.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_memsetF.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.memset.

Corollary reac_identity_init_F_holds_closed :
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_identity_init_c.reac_identity_init_contract_F.
Proof.
  exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_identity_initF.reac_identity_init_F_holds
           (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_memsetF.asan_memset_holds_F
              OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.memset.memset_holds)).
Qed.
