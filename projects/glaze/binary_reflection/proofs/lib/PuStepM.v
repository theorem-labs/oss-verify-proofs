(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.PuPeel OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac pu_mK := constr:(2%nat).
Ltac pu_msub X K := lazymatch K with O => X | S ?k => lazymatch X with wbytes ?m _ _ => pu_msub m k end end.
Ltac pu_mcut X K x :=
  lazymatch K with
  | O => x
  | S ?k => lazymatch X with wbytes ?m ?a ?bs => let m' := pu_mcut m k x in constr:(wbytes m' a bs) end
  end.
Ltac pu_setMJ :=
  lazymatch goal with
  | |- msteps ?s (mkst ?X ?pc (cmem ?sp ?W ?J ?D) ?rom) ?F =>
      let K := pu_mK in
      let R := match goal with _ => pu_msub J K | _ => constr:(tt) end in
      lazymatch R with
      | wbytes _ _ _ =>
          let x := fresh "pJ" in
          refine (let x : pu_mf := R in _);
          let J' := pu_mcut J K x in
          change (msteps s (mkst X pc (cmem sp W J' D) rom) F)
      | _ => idtac
      end
  | |- _ => idtac
  end.
Ltac pu_setMD :=
  lazymatch goal with
  | |- msteps ?s (mkst ?X ?pc (cmem ?sp ?W ?J ?D) ?rom) ?F =>
      let K := pu_mK in
      let R := match goal with _ => pu_msub D K | _ => constr:(tt) end in
      lazymatch R with
      | wbytes _ _ _ =>
          let x := fresh "pD" in
          refine (let x : pu_mf := R in _);
          let D' := pu_mcut D K x in
          change (msteps s (mkst X pc (cmem sp W J D') rom) F)
      | _ => idtac
      end
  | |- _ => idtac
  end.
Ltac pu_setM := pu_setMJ; pu_setMD.
Ltac pu_vnorm3 := pu_vnorm; pu_setM.
Ltac pu_push_store := blit; first [ rewrite wbytes_cmem_win by region_side | rewrite wbytes_cmem_data by region_side | idtac ]; pu_setM.
Ltac pu_rdn_unlet :=
  match goal with
  | |- context [rdn ?segs ?x ?a ?n] => pu_isletM x; let b := eval unfold x in x in change (rdn segs x a n) with (rdn segs b a n)
  end.
Ltac pu_peel := repeat (tryif pp_stop then fail else first [ pp_peel1 | rewrite rdn_wbytes_out by region_side | pu_rdn_unlet ]).

(* [comment removed for export] *)
Ltac pu_setMP :=
  lazymatch goal with
  | |- msteps ?s (mkst ?X ?pc ?M ?rom) ?F =>
      lazymatch M with
      | wbytes _ _ _ =>
          let K := pu_mK in
          let R := match goal with _ => pu_msub M K | _ => constr:(tt) end in
          lazymatch R with
          | wbytes _ _ _ =>
              let x := fresh "pM" in
              refine (let x : pu_mf := R in _);
              let M' := pu_mcut M K x in
              change (msteps s (mkst X pc M' rom) F)
          | _ => idtac
          end
      | _ => idtac
      end
  | |- _ => idtac
  end.
Ltac pu_push_storeP := blit; first [ rewrite wbytes_cmem_win by region_side | rewrite wbytes_cmem_data by region_side | idtac ]; pu_setM; pu_setMP.
