(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: statements written out as text, the launch input as a ProcInput. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec Scfg AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit AsanInitP BothImages BothPlanImages AsHSTab BsStartupHSF.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z04Npos35stdpp9bitvectorbdefinitionsi22bv3h5LinuxProcessSemanticsfLinuxProcessSem3Runk46config3h5LinuxProcessSemanticsfLinuxProcessSembStackLayoutn99EntryDraw3h5LinuxProcessSemanticsfLinuxProcessSem5Stater99ProcInput37Corelib4Init5Logicv33andv32exr97in_argvr97in_envp79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanPlan2AP~~~~~~hi63acs37Corelib4Init9Datatypeshmb6optionv32eqr98in_hwcapr96in_uid69OSSVerify6Proofsaboost_jsonafuzz_parse3libeBothPlanImages~~~~~~hq65ASEGShmb3natr95Model3h5LinuxProcessSemantics5Riscv7Preludehvf5bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3libaAxSymExec33AX2~~~~~~iie3envhq63APH69OSSVerify6Proofsaboost_jsonafuzz_parse3libbBsMainState~~~~~~ind6A_MAINhmb4Somek4h0entry_stack_fitsk4avalid_argvk49valid_brkk4avalid_envpk4bvalid_hwcapk48valid_idk4fvalid_mmap_basek48valid_spr95in_fs69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanInit~~~~~~jk55LIMITjk55SINV0jk55argH0hi62pc79OSSVerify6Proofsaboost_jsonafuzz_parse3libdAsanPlanSound3APS~~~~~~jq16cfg_ofjq15cs_ok69OSSVerify6Proofsaboost_jsonafuzz_parse3libaBothImages~~~~~~jv86BOTH_H69OSSVerify6Proofsaboost_jsonafuzz_parse3libcBsStartupHSF~~~~~~kjf8HSF_asan69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~koa3fx0" s.
Import ListNotations. Import AX2. Import AP. Import APS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Existing Instance fx0.

(* [comment removed for export] *)
Definition A_MAIN : Z := 0xbe8bc.   (* [comment removed for export] *)

(* [comment removed for export] *)
  (* [comment removed for export] *)

(* [comment removed for export] *)
(* RULE 11g, twin of AsMainState.v -- see the note there.  Written out as explicit text
   because [AsanInit.SINV0] is now twenty-six arguments and [AsanInit.argH0] lost
   ph/uid/hw and gained kern/execfn; both are reached through AsanInitP.v's packed
   [SINVp]/[argHp], which are the same terms at this [inp]'s projections.
   LPS 727298f3: the invariant is [AsanInitP.SINVm], the run's mmap base bound inside it
   (as AsMainState.v). *)
Definition P_main (sp0 brk0 mbase : word) (rdraw : EntryDraw) (inp : ProcInput) (c : config) : Prop :=
  (valid_sp sp0 /\ valid_brk ASEGS brk0 /\ valid_mmap_base mbase
   /\ valid_argv (in_argv inp) /\ valid_envp (in_envp inp)
   /\ entry_stack_fits sp0 (in_argv inp) (in_envp inp)
   /\ valid_id (in_uid inp) /\ valid_hwcap (in_hwcap inp))
  /\ exists (h : nat) (ch : acs) (E : env) (R : bvmap 5 word)
            (FULL : word -> option byte) (model : Model),
       HSF_asan h = Some ch /\ pc ch = A_MAIN
       /\ c = cfg_of ASEGS R A_MAIN FULL model
       /\ cs_ok ASEGS BOTH_H AsanInit.LIMIT
            (SINVm APH A_PC sp0 rdraw brk0 inp)
            (argHp sp0 rdraw inp)
            (in_fs inp) E ch R FULL model.
(* [comment removed for export] *)
