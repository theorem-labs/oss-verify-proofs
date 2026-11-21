(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit Require Import PropExec CatExec CatSim StoreOk ExitSim MmapSim StreamSim WallSim DrainSim StepTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.

Fixpoint l10_wchain (m : word -> option byte) (ws : list (word * list byte)) : word -> option byte :=
  match ws with
  | nil => m
  | cons (a, bs) ws' => wbytes (l10_wchain m ws') a bs
  end.

Lemma l10_wchain_grows : forall ws m, mem_grows m (l10_wchain m ws).
Proof.
  induction ws as [|[a bs] ws IH]; intro m; cbn [l10_wchain];
    [ apply mem_grows_refl | eapply mem_grows_trans; [ apply IH | apply wbytes_grows ] ].
Qed.

Lemma l10_store_ok_wchain : forall segs n ws m a,
  store_ok segs m a n = true -> store_ok segs (l10_wchain m ws) a n = true.
Proof. intros segs n ws m a H. eapply store_ok_mono; [ apply l10_wchain_grows | exact H ]. Qed.

Ltac l10_reify M :=
  lazymatch M with
  | wbytes ?M' ?a ?bs =>
      let r := l10_reify M' in
      lazymatch r with (?b, ?ws) => constr:((b, @cons (word * list byte) (a, bs) ws)) end
  | _ => constr:((M, @nil (word * list byte)))
  end.

Ltac l10_peel :=
  lazymatch goal with
  | |- store_ok ?segs (wbytes ?M' ?a0 ?bs0) ?a ?n = true =>
      let r := l10_reify (wbytes M' a0 bs0) in
      lazymatch r with
      | (?b, ?ws) => change_no_check (store_ok segs (l10_wchain b ws) a n = true); apply l10_store_ok_wchain
      end
  | |- _ => idtac
  end.

Ltac l10_bind_final :=
  lazymatch goal with
  | |- msteps ?segs ?s ?fin =>
      tryif is_var fin then idtac
      else tryif has_evar fin then
        (let F := fresh "L10FIN" in pose (F := fin); change_no_check (msteps segs s F))
      else idtac
  | |- _ => idtac
  end.

Ltac l10_unbind_final :=
  lazymatch goal with
  | |- msteps ?segs ?s ?F =>
      tryif is_var F then
        (let b := eval cbv delta [F] in F in change_no_check (msteps segs s b); clear F)
      else idtac
  | |- _ => idtac
  end.

Ltac l10_mst_refl := l10_unbind_final; apply mst_refl.

Ltac l10_chain_step_kit :=
  first [ eapply mst_step
        | eapply tw_step
        | eapply twm_step
        | eapply MmapSim.twmt_step
        | eapply tmw_step
        | eapply StreamSim.twr_step
        | eapply StreamSim.trd_step
        | eapply WallSim.twt_step
        | eapply WallSim.twe_step
        | eapply DrainSim.tout_step
        | eapply DrainSim.trd_step
        | eapply te_step ].

Ltac l10_chain_step := l10_bind_final; l10_chain_step_kit.
