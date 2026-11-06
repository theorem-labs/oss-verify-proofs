(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmParse Require Import ParseSomeKn.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallKn.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module SPKX.
Definition S2V : expr := EVar 52.
Definition ENC_SIZE : Z := 408.
(* [comment removed for export] *)
Definition xtra (C : PSK.consts) (P Vv E sp : expr) (X : PSK.pexprs) : list kentry :=
  let p := PSK.x_p X in let pk := APC.escale 2 (PSK.x_k X) in let sb := PSK.x_sb X in let scap := PSK.x_scap X in
  [KRange S2V 1099511627776 140737488355328; KAlign S2V 8;
   PSK.kdisj Vv 0 (ELit ENC_SIZE) p 0 pk; PSK.kdisj Vv 0 (ELit ENC_SIZE) sb 0 scap; PSK.kdisj S2V 0 (ELit 24) p 0 pk; PSK.kdisj S2V 0 (ELit 24) sb 0 scap;
   PSK.kdisj sp (- PSK.c_scr C) (ELit (PSK.c_scr C)) Vv 0 (ELit ENC_SIZE); PSK.kdisj sp (- PSK.c_scr C) (ELit (PSK.c_scr C)) S2V 0 (ELit 24);
   PSK.kdisj P 0 (ELit 272) Vv 0 (ELit ENC_SIZE); PSK.kdisj E 0 (ELit 16) Vv 0 (ELit ENC_SIZE);
   PSK.kdisj P 0 (ELit 272) S2V 0 (ELit 24); PSK.kdisj E 0 (ELit 16) S2V 0 (ELit 24); PSK.kdisj Vv 0 (ELit ENC_SIZE) S2V 0 (ELit 24)].
Definition knx (C : PSK.consts) (fr : bool) (P Vv E sp wend : expr) (X : PSK.pexprs) : list kentry :=
  SPK.kn C fr P Vv E sp wend X ++ xtra C P Vv E sp X.
(* [comment removed for export] *)
Definition wxtra (Vv seg wlen : expr) : list kentry := [PSK.kdisj Vv 0 (ELit ENC_SIZE) seg 0 wlen; PSK.kdisj S2V 0 (ELit 24) seg 0 wlen].
Definition win_fx (C : PSK.consts) (P Vv E sp seg wlen : expr) (X : PSK.pexprs) : list kentry :=
  SPK.win_f C P Vv E sp seg wlen X ++ wxtra Vv seg wlen.
End SPKX.
