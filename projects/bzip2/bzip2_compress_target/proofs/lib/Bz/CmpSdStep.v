(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 CmpSdKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Ltac pstep_with_fast SC p q n k :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pce ?fc ?rv ?m ?ro) =>
    let kn := eval vm_compute in (Z.to_nat (k / 4)) in
    let qa := eval vm_compute in (q + k)%Z in
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 qa)) in
    lazymatch fw with
    | Some ?w =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (?i, ?sz) =>
        let Hs := fresh "Hs" in
        pose proof (same_code_nth segs n p q kn SC ltac:(lia)) as Hs;
        replace (p + 4 * Z.of_nat kn)%Z with (p + k)%Z in Hs by lia;
        replace (q + 4 * Z.of_nat kn)%Z with qa in Hs by lia;
        let wv := fresh "wv" in let H1 := fresh "Hf1" in let H2 := fresh "Hf2" in
        cps_destruct Hs as (wv & H1 & H2);
        assert (wv = w) by (apply (f_equal (fun o => match o with Some x => x | None => w end)) in H2;
                            rewrite <- H2; vm_compute; reflexivity);
        subst wv; clear H2;
        first [ StepFast.sf_step_fetch H1
              | eapply evt_step;
                [ split; [reflexivity|];
                  rewrite (step_gen segs R F pce fc rv m ro w i sz H1 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity));
                  exec_pre i;
                  exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
                  try solve_load; try solve_store;
                  reflexivity
                | simp_regs; vnorm_for i; mem_after_store_opt; post_step i ] ];
        clear H1
      | None => fail "undecodable instruction at" qa
      end
    | None => fail "no instruction at" qa
    end
  end.
