(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Export MemoFast.

Ltac conj_leaf_unfold :=
  lazymatch goal with
  | |- ?G =>
      let h := lazymatch G with
               | ?f _ _ _ _ _ _ _ _ => f | ?f _ _ _ _ _ _ _ => f | ?f _ _ _ _ _ _ => f | ?f _ _ _ _ _ => f
               | ?f _ _ _ _ => f | ?f _ _ _ => f | ?f _ _ => f | ?f _ => f | ?f => f end in
      lazymatch h with
      | @eq => fail "conj_leaf_unfold: equation"
      | and => fail "conj_leaf_unfold: conjunction"
      | _ => is_const h; unfold h
      end
  end.
Ltac conj_vmc2 :=
  repeat (lazymatch goal with |- _ /\ _ => split end);
  first [ vmc1
        | exact I
        | (conj_leaf_unfold; lazymatch goal with |- _ /\ _ => idtac | |- @eq _ _ _ => idtac end; conj_vmc2)
        | (vm_compute; repeat split; reflexivity) ].
