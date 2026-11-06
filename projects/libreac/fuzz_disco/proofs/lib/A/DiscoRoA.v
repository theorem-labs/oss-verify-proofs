(* fuzz_disco A (asan): the read-only facts of the part's walks, lib/A/DiscoAsanT.v:54 H_RO_stmt, PROVED at every rc
   (rule 24: no function proved; this file is assembly). It is the satisfiability witness, at the real instance
   (B := AD2l.TfibB, the asan image's loaded segments, DiscoRoList.disco_globs), of the shared hypothesis
   lib/A/AD2p.v:49 H_RO and of the premise `DiscoAsanT.H_RO_stmt rc` of a Theorem Labs lane's DiscoLibX.disco_lib_x_all_acfn.
   The three conjuncts are a Theorem Labs lane's lib/A/Prog/DiscoRoClose.v lemmas (disco_ro_unowned_tfib, disco_globs_marked,
   disco_img_shadow_vis), each closed by computation. DiscoRoClose states them at DiscoImg.disco_segs, which is
   `Asan.M.loaded_segments` by definition (lib/A/Prog/DiscoImg.v:15), the `segs` of DiscoAsanT.v:41; its disco_globs is
   DiscoRoList.disco_globs (DiscoRo.v:15 re-exports DiscoRoList). The Y twin is lib/Reusable/DiscoAsanUbsanT.v:43 H_RO. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require DiscoAsanT.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require DiscoRoClose.

Lemma disco_H_RO : forall rc : YM05.RunCeil, DiscoAsanT.H_RO_stmt rc.
Proof.
  intros rc. unfold DiscoAsanT.H_RO_stmt.
  split; [exact DiscoRoClose.disco_ro_unowned_tfib|].
  split; [exact DiscoRoClose.disco_globs_marked | exact DiscoRoClose.disco_img_shadow_vis].
Qed.
