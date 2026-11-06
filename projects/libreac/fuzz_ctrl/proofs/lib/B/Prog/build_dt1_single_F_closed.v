(* The closed corollary of build_dt1_single, moved here out of build_dt1_singleF.v (a Theorem Labs lane, 07:03Z) so that
   the proof file's Require closure stays free of lib/B/Bz: that chain entered build_dt1_singleF.v ONLY through
   this corollary's Require of asan_memcpyF (-> lib/B/BzBridge -> lib/B/Bz/Lib) and dt1_head_F. The corollary
   keeps its exact name and statement; only its module changed.

   With no hypothesis left: the footprint statement of build_dt1_single at the contracts its two callees' owners
   prove for this image -- dt1_head_holds_F (lib/B/Prog/dt1_head_F.v) and a Theorem Labs lane's asan_memcpy_holds_F
   (lib/B/Prog/asan_memcpyF.v), both closed. *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.build_dt1_singleF.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.dt1_head_F.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_memcpyF.

Corollary build_dt1_single_F_holds_closed :
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.build_dt1_single_c.build_dt1_single_contract_F.
Proof.
  exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.build_dt1_singleF.build_dt1_single_F_holds
           OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.dt1_head_F.dt1_head_holds_F
           OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_memcpyF.asan_memcpy_holds_F).
Qed.

(* Route (C) (a Theorem Labs lane's brief dt1-on-B): the _on twin of the corollary above. With no hypothesis left: the
   footprint _on statement of build_dt1_single at the _on contracts its two callees' owners prove for this image --
   dt1_head_F_holds_on (lib/B/Prog/dt1_head_F.v, premise-free) and asan_memcpy_holds_F_on
   (lib/B/Prog/asan_memcpyF_on.v, a Theorem Labs lane at a working branch ec8fc6d9297), both closed. *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_memcpyF_on.

Corollary build_dt1_single_F_holds_on_closed :
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.build_dt1_single_c.build_dt1_single_contract_F_on.
Proof.
  exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.build_dt1_singleF.build_dt1_single_F_holds_on
           OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.dt1_head_F.dt1_head_F_holds_on
           OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_memcpyF_on.asan_memcpy_holds_F_on).
Qed.
