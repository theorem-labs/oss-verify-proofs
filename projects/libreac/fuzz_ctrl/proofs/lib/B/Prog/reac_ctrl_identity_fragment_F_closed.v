(* The closed corollary of reac_ctrl_identity_fragment, moved here out of reac_ctrl_identity_fragment_F.v
   (a Theorem Labs lane, 07:03Z) so that the proof file's Require closure stays free of lib/B/Bz: that chain entered
   reac_ctrl_identity_fragment_F.v ONLY through this corollary's Require of asan_memcpyF and bcmp_wrap_F
   (-> lib/B/Bz/A, lib/B/Bz/Lib). The corollary keeps its exact name and statement; only its module changed.

   With no hypothesis left: the footprint statement of reac_ctrl_identity_fragment at the contracts its three
   callees' owners prove for this image -- a Theorem Labs lane's asan_memcpy_holds_F (lib/B/Prog/asan_memcpyF.v),
   a Theorem Labs lane's bcmp_wrap_holds_F (lib/B/Prog/bcmp_wrap_F.v, re-fitted to this branch's published
   bcmp_wrap_contract_F) and reac_ctrl_record_cksum_verify_holds_F
   (lib/B/Prog/reac_ctrl_record_cksum_verify_F.v), all three closed. *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_identity_fragment_F.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_memcpyF.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.bcmp_wrap_F.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_record_cksum_verify_F.

Corollary reac_ctrl_identity_fragment_holds_F_closed :
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_identity_fragment_c.reac_ctrl_identity_fragment_contract_F.
Proof.
  exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_identity_fragment_F.reac_ctrl_identity_fragment_holds_F
           OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_memcpyF.asan_memcpy_holds_F
           OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.bcmp_wrap_F.bcmp_wrap_holds_F
           OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_record_cksum_verify_F.reac_ctrl_record_cksum_verify_holds_F).
Qed.

(* Route (C), the callee case (a Theorem Labs lane): the closed form of reac_ctrl_identity_fragment_holds_F_on.
   The narrowed statement reac_ctrl_identity_fragment_contract_F_on, at the _F_on runs its three callees' owners prove
   for this image: asan_memcpy_holds_F_on (lib/B/Prog/asan_memcpyF_on.v), bcmp_wrap_holds_F_on (lib/B/Prog/bcmp_wrap_on.v,
   taken by path from a working branch 05b456d375e) and reac_ctrl_record_cksum_verify_holds_F_on
   (lib/B/Prog/reac_ctrl_record_cksum_verify_F.v), all three closed. *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_memcpyF_on.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.bcmp_wrap_on.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_identity_fragment_c.

Corollary reac_ctrl_identity_fragment_holds_F_closed_on : reac_ctrl_identity_fragment_contract_F_on.
Proof.
  exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_identity_fragment_F.reac_ctrl_identity_fragment_holds_F_on
           OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_memcpyF_on.asan_memcpy_holds_F_on
           OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.bcmp_wrap_on.bcmp_wrap_holds_F_on
           OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_record_cksum_verify_F.reac_ctrl_record_cksum_verify_holds_F_on).
Qed.
