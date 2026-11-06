(* The closed corollary of declaration_of, moved here out of declaration_ofF.v (a Theorem Labs lane, 07:03Z) so that the
   proof file's Require closure stays free of lib/B/Bz: that chain entered declaration_ofF.v ONLY through this
   corollary's Require of asan_memcpyF (-> lib/B/BzBridge -> lib/B/Bz/Lib), and the auditor's ctrlgate flags the
   proof file's bare lib.Lib names as DUP once a lib/B/Bz twin is in the closure. The corollary keeps its exact
   name and statement; only its module changed.

   With no hypothesis left: the footprint statement of declaration_of at the callee contract its owner proves for
   this image -- a Theorem Labs lane's asan_memcpy_holds_F (lib/B/Prog/asan_memcpyF.v), which is closed. *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.declaration_ofF.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_memcpyF.

Corollary declaration_of_F_holds_closed :
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.declaration_of_c.declaration_of_contract_F.
Proof.
  exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.declaration_ofF.declaration_of_F_holds
           OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_memcpyF.asan_memcpy_holds_F).
Qed.

(* The narrowed corollary (route (C)): declaration_of_contract_F_on at a Theorem Labs lane's asan_memcpy_holds_F_on
   (lib/B/Prog/asan_memcpyF_on.v), the memcpy _F_on run merged in via the rton bundle. *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_memcpyF_on.

Corollary declaration_of_F_holds_closed_on :
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.declaration_of_c.declaration_of_contract_F_on.
Proof.
  exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.declaration_ofF.declaration_of_F_holds_on
           OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_memcpyF_on.asan_memcpy_holds_F_on).
Qed.
