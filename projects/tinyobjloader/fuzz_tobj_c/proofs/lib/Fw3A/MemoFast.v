(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)

Ltac memo_rw H :=
  lazymatch type of H with
  | @eq ?A ?a ?b =>
      lazymatch goal with
      | |- ?G =>
          lazymatch (eval pattern a in G) with
          | ?P _ => lazymatch P with
                    | (fun _ => ?B) => idtac
                    | _ => refine (@eq_ind_r A b P _ a H); cbv beta
                    end
          end
      end
  end.

Ltac vmc1 :=
  lazymatch goal with
  | |- @eq ?T ?t ?v =>
      tryif first [ has_evar t | has_evar v ] then fail "vmc1: the goal has evars"
      else vm_cast_no_check (@eq_refl T v)
  end.

Ltac memo_rwn nf H :=
  lazymatch type of H with
  | @eq ?A ?a ?b =>
      let a' := nf a in
      lazymatch goal with
      | |- ?G =>
          lazymatch (eval pattern a' in G) with
          | ?P _ => lazymatch P with
                    | (fun _ => ?B) => idtac
                    | _ => refine (@eq_ind_r A b P _ a' H); cbv beta
                    end
          end
      end
  end.

Ltac conj_vmc := repeat (lazymatch goal with |- _ /\ _ => split end); first [ vmc1 | exact I ].

Ltac vmc := first [ vmc1 | (vm_compute; reflexivity) ].
