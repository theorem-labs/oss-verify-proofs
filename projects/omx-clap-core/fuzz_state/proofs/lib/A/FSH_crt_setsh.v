(* lib/A/FSH_crt_setsh.v: check_round_trip's runtime premise SETSH (lib/A/FSH_crt_segD.v crt_set_shadow_fixed, the
   contract of __asan_set_shadow_f5 at PC_set_shadow_f5 0x82378 that crt_tail_sm and Section tail take) from S0's
   set_shadow contract (FSH_crt_base.v CrtRt's crt_fr_set_shadow_f5, FSH_Rt.v FsRt's fr_set_shadow_f5).
   rule 24: no function proved (kind: helper / kit / model lemmas; no walk of program code).
   That contract is SetShadowDefU.aset_shadow_realizesU at PC_set_shadow_f5 0xf5, and S0 states it WITH the presence
   clause `forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a` (its last conjunct, SetShadowDefU.v:48, S0
   5dbb8ce6286 "set_shadow contracts keep presence"). crt_set_shadow_fixed is that contract less one conjunct (the
   callee's stack window is present after the call, SetShadowDefU.v:47), so SETSH is a weakening of its post; no other
   premise is needed. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0s YA0i YA0n YG0f YG0d YI16 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v FSH_Base FSH_crt_segD.
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
