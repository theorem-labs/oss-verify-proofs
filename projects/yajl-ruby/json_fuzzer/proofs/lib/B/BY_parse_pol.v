(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BYajl_iface BY_parse_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition ppol_marker {Y : ay_params} (E : apE Y) (mh : mhand) : Prop := True.
Lemma ppol_mark : forall {Y : ay_params} (E : apE Y) (mh : mhand), ppol_marker E mh.
Proof. aceil. intros. exact I. Qed.

End RC__1.
Ltac ppolby pat :=
  match goal with
  | H : forall a k, pat <= a -> _ |- _ => eapply H; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; solve [lia | zsimp; lia]
  end.

Ltac parsepolicy E mh :=
  lazymatch goal with
  | |- _ (Z_to_bv 64 ?A, _) =>
      match A with
      | context [p_SQ E] => ppolby (p_lo E)
      | context [bv_unsigned (p_sp E)] => ppolby (p_lo E)
      | context [2147450880] =>
          match A with
          | context [mh_addr (p_mh E)] => ppolby (2147450880 + mh_addr (p_mh E) / 8)
          | context [mh_stack mh] => ppolby (2147450880 + mh_stack mh / 8)
          | context [mh_lexer mh] => ppolby (2147450880 + mh_lexer mh / 8)
          | context [mb_addr (mh_decbuf mh)] => ppolby (2147450880 + mb_addr (mh_decbuf mh) / 8)
          | context [mh_ctx (p_mh E)] => ppolby (2147450880 + mh_ctx (p_mh E) / 8)
          | context [p_ff E] => ppolby (2147450880 + p_ff E / 8)
          | context [p_OT E] => ppolby (2147450880 + p_OT E / 8)
          | _ => ppolby 2147454976
          end
      | context [mh_addr (p_mh E)] => ppolby (mh_addr (p_mh E))
      | context [mh_stack mh] => ppolby (mh_stack mh)
      | context [mh_lexer mh] => ppolby (mh_lexer mh)
      | context [mb_addr (mh_decbuf mh)] => ppolby (mb_addr (mh_decbuf mh))
      | context [mh_ctx (p_mh E)] => ppolby (mh_ctx (p_mh E))
      | context [p_ff E] => ppolby (p_ff E)
      | context [p_T E] => ppolby (p_T E)
      | _ => first [ppolby 65536 | ppolby 2147459072]
      end
  end.

Ltac policy1 ::=
  lazymatch goal with
  | |- ?P (?a, ?n) =>
      (lazymatch a with
       | Z_to_bv 64 _ => idtac
       | wa _ => apply policy_wa
       | wz ?X => change (wz X) with (Z_to_bv 64 X)
       | _ => apply policy_var
       end);
      first [ assumption
            | match goal with M : ppol_marker ?E ?mh |- _ => parsepolicy E mh end
            | match goal with
              | H : _ |- _ =>
                  lazymatch type of H with
                  | context [P (_, _)] => eapply H; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; solve [ eauto | lia | zsimp; lia ]
                  end
              end ]
  end.
