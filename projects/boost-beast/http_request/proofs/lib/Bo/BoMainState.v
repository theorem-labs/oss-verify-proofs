(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.boost_beast.http_request.images Require AsanUbsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import PropExec Scfg AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit AsanInitL BothImages BothPlanImages AsHSTab BoStartupHSF.
Import ListNotations. Import AX2. Import AP. Import APS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition A_MAIN : Z := 0xa3f9c.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition N_HOLES : nat := 6.

(* The state at main.  #38: the start-up invariant is [AsanInitL.SINV0L], [AsanInit.SINV0] with
   the run's mmap base bound inside by its defining facts, so no consumer of [P_main] holds or
   chooses a base.  [apc] is the Both image's own entry, [AsanUbsan.M.init_pc]. *)
Definition P_main (sp0 brk0 mbase : word) (rdraw : EntryDraw) (inp : ProcInput) (c : config) : Prop :=
  (valid_sp sp0 /\ valid_brk BSEGS2 brk0 /\ valid_mmap_base mbase /\ valid_argv (in_argv inp) /\ valid_envp (in_envp inp)
   /\ entry_stack_fits sp0 (in_argv inp) (in_envp inp) /\ valid_id (in_uid inp) /\ valid_hwcap (in_hwcap inp))
  /\ exists (h : nat) (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model),
    HSF_both h = Some ch /\ pc ch = A_MAIN /\
    c = cfg_of BSEGS2 R A_MAIN FULL model /\
    cs_ok BSEGS2 BOTH_H AsanInit.LIMIT
          (SINV0L BPH2 OSSVerify.boost_beast.http_request.images.AsanUbsan.M.init_pc sp0 rdraw brk0 inp)
          (argH0 sp0 rdraw inp)
          (in_fs inp) E ch R FULL model.
