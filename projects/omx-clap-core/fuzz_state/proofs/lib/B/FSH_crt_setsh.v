(* lib/B/FSH_crt_setsh.v: check_round_trip's runtime premise SETSH (lib/B/FSH_crt_segD.v crt_set_shadow_fixed, the
   contract of __asan_set_shadow_f5 at PC_set_shadow_f5 0x550a0 (fs.asan-ubsan, lib/B/FSH_Base.v; A: 0x82378) that the
   B tail crt_tail takes) from S0's set_shadow contract (lib/B/FSH_crt_base.v CrtRt's crt_fr_set_shadow_f5, lib/B/FSH_Rt.v
   FsRt's fr_set_shadow_f5).
   rule 24: proves no function (kind: runtime-law lemma of check_round_trip's walk, PORTED from 1bec65b39d3 lib/A/FSH_crt_setsh.v)
   rule 24: proves no function (kind: segment lemmas of check_round_trip's walk, PORTED from 1ab57ca7ad7) - the
   premise is the one set_shadow contract, not FsRt (A 19fe26faf75, merged at 1ab57ca7ad7).
   PORT SOURCE: a working branch 1bec65b39d3 proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_setsh.v (blob
   49de96cf382), with a working branch 1ab57ca7ad7's change. Same Lemma name and statement shape as the A
   file, over image B. B twin written by a Theorem Labs lane. No program code is walked, so no pc of
   check_round_trip is used; the one image constant is B's PC_set_shadow_f5 (0x550a0, `sym __asan_set_shadow_f5`,
   lib/B/FSH_Base.v), which both the contract and the premise name. Non-mechanical changes: none.
   That contract is lib/A SetShadowDefU.aset_shadow_realizesU at PC_set_shadow_f5 0xf5 (the image-generic contract
   file; lib/B/FSH_Rt.v:120 FsRt's field), which states the presence clause
   `forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a` (its last conjunct, SetShadowDefU.v:48).
   crt_set_shadow_fixed is that contract less one conjunct (the callee's stack window is present after the call,
   SetShadowDefU.v:47), so SETSH is a weakening of its post; no other premise is needed. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0s YA0i YA0n YG0f YG0d YI16 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v FSH_Base FSH_crt_segD.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require SetShadowDefU.
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(* SETSH from the set_shadow contract: its post with the stack-window presence conjunct dropped *)
Lemma crt_setsh_of_rt :
  SetShadowDefU.aset_shadow_realizesU tfibsegs B PC_set_shadow_f5 0xf5 -> crt_set_shadow_fixed B PC_set_shadow_f5 0xf5.
Proof.
intros SSH ly S U W regs mem md cid pos q n HPRE HIN G10 G11 Hn Hq1 Hq2.
eapply SRr_mono.
{ exact (SSH ly S U W regs mem md cid pos q n HPRE HIN G10 G11 Hn Hq1 Hq2). }
cbv beta. intros W' c' _ (EW & regs' & mem' & md' & Ec & HARU & HP & Hsame & Hset & Hfr & _ & Hpr).
split; [exact EW|]. exists regs', mem', md'.
exact (conj Ec (conj HARU (conj HP (conj Hsame (conj Hset (conj Hfr Hpr)))))).
Qed.

End s.
Print Assumptions crt_setsh_of_rt.
