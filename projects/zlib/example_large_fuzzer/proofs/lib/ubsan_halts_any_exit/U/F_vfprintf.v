(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Bytes PropExec.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim Monad PrintfModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Printf_lib F_memset F_memcpy F_fwritex F_pop_arg Printf_mlib F_printf_iface F_printf_core.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import F_printf_snsink F_sn_write F_towrite.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import PrintfModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Definition zpk__ (P : Prop) : Prop := P.
Local Ltac zpk1__ H := let T := type of H in change (zpk__ T) in H.
Local Ltac zpk_nf__ H A q := lazymatch A with context [q] => fail | _ => zpk1__ H end.
Local Ltac zidleF__ q n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(q, q + n)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zpk_nf__ H A q
    | H : ro_cells segs m ?A _ |- _ => zpk_nf__ H A q
    | H : u8arr segs m ?A _ |- _ => zpk_nf__ H A q
    | H : bytes_at segs m ?A _ |- _ => zpk_nf__ H A q
    end
  end.
Module DJ.
  Import Ltac2.
  Ltac2 prune_reld () : unit :=
    let bad := SF2.bad_heads () in
    let gv := SF2.vars_of [] (Control.goal ()) in
    SF2.prune_with (fun ty => if SF2.plain_arith false ty then SF2.clean bad ty else SF2.meets (SF2.vars_of [] ty) gv).
  Ltac2 prune_reld1 () : unit := Control.enter prune_reld.
End DJ.
Local Ltac dj_prune := ltac2:(DJ.prune_reld1 ()).
Module DJR.
  Import Ltac2.
  Ltac2 is_hidden (t : constr) : constr option := lazy_match! t with sf_hide ?p => Some p | _ => None end.
  Ltac2 unhide_rel () : unit :=
    let gv := SF2.vars_of [] (Control.goal ()) in
    let rm := List.map_filter (fun h => let (id, body, ty) := h in
      match body with
      | Some _ => None
      | None =>
          match is_hidden ty with
          | Some p => if SF2.meets (SF2.vars_of [] p) gv
                      then (let c := Control.hyp id in ltac1:(c |- unfold sf_hide in c) (Ltac1.of_constr c); None)
                      else Some id
          | None => None
          end
      end) (Control.hyps ()) in
    match rm with [] => () | _ :: _ => Std.clear rm end.
  Ltac2 unhide_rel1 () : unit := Control.enter unhide_rel.
End DJR.
Local Ltac dj_unhide_rel := ltac2:(DJR.unhide_rel1 ()).
Local Ltac dj_one := first [ Zify.zify; xlia zchecker | dj_unhide_rel; Zify.zify; xlia zchecker | sf_unhide; dj_prune; Zify.zify; xlia zchecker | tlia ].
Local Ltac tslia ::= first [ exact I | repeat lazymatch goal with |- _ /\ _ => split end; first [ exact I | dj_one ] ].
Local Ltac lia ::= lia3.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

Lemma arg_ok_vf : forall Fp B BS m m' lo sp sp' ap w a,
  arg_ok Fp B BS m lo sp ap w a -> sp' <= sp -> munch [(lo, sp); (Fp, Fp + 232)] m m' -> arg_ok Fp B BS m' lo sp' ap w a.
Proof.
  intros Fp B BS m m' lo sp sp' ap w a H Hsp MU. destruct a as [s| |i|u|u|d]; cbn in H |- *; try exact H.
  destruct H as (slack & BY & HF & PAD & NZ & D1 & D2 & D3 & D4). exists slack.
  split; [|repeat (split; [first [assumption | lia]|]); exact D4].
  eapply bytes_at_transport; [exact BY | exact MU |].
  cbn [disjoint_from]. rewrite length_app, zb_length. cbn [length]. unfold zlength in *. lia.
Qed.
Lemma args_ok_vf : forall Fp B BS m m' lo sp sp' ap ws args,
  args_ok Fp B BS m lo sp ap ws args -> sp' <= sp -> munch [(lo, sp); (Fp, Fp + 232)] m m' -> args_ok Fp B BS m' lo sp' ap ws args.
Proof.
  intros Fp B BS m m' lo sp sp' ap ws args. revert ws. induction args as [|a args IH]; intros ws H Hsp MU; [destruct ws; exact I|].
  cbn [args_ok] in H |- *. destruct ws as [|w ws]; [exact H|]. destruct H as [H1 H2].
  split; [eapply arg_ok_vf; eassumption | apply IH; assumption].
Qed.

Lemma rwc_eq : forall m A A' cs, rw_cells usegs m A cs -> A = A' -> rw_cells usegs m A' cs.
Proof. intros m A A' cs H <-. exact H. Qed.
Ltac piece H := eapply rwc_eq; [exact H | cbn [cells_size csize Nat.add app]; lia].

Definition VF_FRAME : Z := 368.

