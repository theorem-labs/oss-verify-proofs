(* fuzz_state image A: the route-1 realloc contract FSupoisonRealloc.FS_AREALLOC_AU with no hypothesis left
   (a Theorem Labs lane, 2026-10-29).

   rule 24: no function proved (kind: merge - lib/A/FSReallocAGc.v's generic theorem at the two ARU callee lifts).

   [fs_arealloc_AU_closed_final] is FSReallocAGc.fs_arealloc_AU_at_cgif (FSReallocAG.v's Section g closed at the relocated
   chain, under its two Section hypotheses) with
     H_refill_U := FSupoisonARXmRf.fs_refill_U_closed (if_refill at ARX_ARU, from FSupoisonAllocRt.tfib_refill_okU)
     H_difR_U   := FSupoisonARXmDRc.fs_difR_U_closed at L24 := 16385 (DIfaceR at ARX_ARU, from the FSupoisonAllocF* walks)
   each of which meets its hypothesis by conversion.  [fs_arealloc_AU_TfibB_final] is its corollary at fs's symbol table
   AD2l.TfibB (AD2l.TfibB_syms, the depot hash by eq_refl): the H_arealloc premise of lib/A/FSClose.v.

   No Axiom, no Admitted. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YM05 YG00 YG01 YG0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YF0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require
AD2l FSupoisonRealloc FSupoisonARXmRf FSupoisonARXmDRc FSReallocAGc.
Open Scope Z_scope.

Module PR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonRealloc.

Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Theorem fs_arealloc_AU_closed_final : forall B : asyms, TfibSyms B -> (forall t, as_dhash B t = YF0p.tfib_dhash t) ->
  PR.FS_AREALLOC_AU tfibsegs B (as_universe B).
Proof.
exact (@FSReallocAGc.fs_arealloc_AU_at_cgif fx rc
  (fun B TS Up => FSupoisonARXmRf.fs_refill_U_closed B TS Up)
  (fun B TS Up => FSupoisonARXmDRc.fs_difR_U_closed B TS 16385 (Z.le_refl 16385) Up)).
Qed.

Corollary fs_arealloc_AU_TfibB_final : PR.FS_AREALLOC_AU tfibsegs AD2l.TfibB (as_universe AD2l.TfibB).
Proof. exact (fs_arealloc_AU_closed_final AD2l.TfibB AD2l.TfibB_syms (fun t => eq_refl)). Qed.

End f.
