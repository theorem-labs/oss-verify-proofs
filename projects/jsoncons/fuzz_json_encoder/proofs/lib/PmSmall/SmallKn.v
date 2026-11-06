(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmParse Require Import ParseSomeKn.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module SPK.
Definition objs_f (C : PSK.consts) (P Vv E : expr) : list kentry :=
  [KWr (SA P 0) (ELit 272); KRange P 1099511627776 140737488355328; KAlign P 8;
   KWr (SA E 0) (ELit 16); KRange E 1099511627776 140737488355328;
   PSK.kw Vv 0 8 (ELit (PSK.c_vt_visitor C)); KRange Vv 1099511627776 140737488355328].
(* [comment removed for export] *)
Definition objs_h (E : expr) (X : PSK.pexprs) : list kentry :=
  [PSK.kw E 0 4 (PSK.x_ec X);
   KUnk (SA (PSK.x_sb X) 0) (PSK.x_scap X); KWr (SA (PSK.x_sb X) 0) (PSK.x_scap X); KRange (PSK.x_sb X) 4096 140737488355328; KRange (PSK.x_slen X) 1 1027; KRange (PSK.x_scap X) 66 1056;
   KRange (APC.esub (PSK.x_scap X) (PSK.x_slen X)) 0 1056;
   KRange (PSK.x_size X) 0 67108863; KRange (PSK.x_level X) 0 1025; KRange (PSK.x_st X) 0 255; KRange (PSK.x_sst X) 0 255; KRange (PSK.x_nst X) 0 255; KRange (PSK.x_more X) 0 1; KRange (PSK.x_done X) 0 1].
Definition disj_h (C : PSK.consts) (P Vv E sp : expr) (X : PSK.pexprs) : list kentry :=
  let p := PSK.x_p X in let pk := APC.escale 2 (PSK.x_k X) in let sb := PSK.x_sb X in let scap := PSK.x_scap X in
  flat_map (fun o : expr * Z * expr => let '(b, lo, n) := o in [PSK.kdisj b lo n p 0 pk; PSK.kdisj b lo n sb 0 scap])
           [(sp, - PSK.c_scr C, ELit (PSK.c_scr C)); (P, 0, ELit 272); (E, 0, ELit 16); (Vv, 0, ELit 8)]
  ++ [PSK.kdisj p 0 pk sb 0 scap; PSK.hull C p pk; PSK.hull C sb scap].
Definition disj_f (C : PSK.consts) (P Vv E sp : expr) : list kentry :=
  [PSK.kdisj sp (- PSK.c_scr C) (ELit (PSK.c_scr C)) P 0 (ELit 272); PSK.kdisj sp (- PSK.c_scr C) (ELit (PSK.c_scr C)) E 0 (ELit 16);
   PSK.kdisj sp (- PSK.c_scr C) (ELit (PSK.c_scr C)) Vv 0 (ELit 8);
   PSK.kdisj P 0 (ELit 272) E 0 (ELit 16); PSK.kdisj P 0 (ELit 272) Vv 0 (ELit 8); PSK.kdisj E 0 (ELit 16) Vv 0 (ELit 8)].
(* [comment removed for export] *)
Definition kn_sem (C : PSK.consts) (P Vv E sp wend : expr) (X : PSK.pexprs) : list kentry :=
  PSK.pconst C P ++ PSK.pstate_cells P wend X ++ PSK.strblk X ++ objs_h E X ++ disj_h C P Vv E sp X.
Definition kn_frz (C : PSK.consts) (fr : bool) (P Vv E sp : expr) : list kentry :=
  objs_f C P Vv E ++ PSK.frame C sp fr ++ disj_f C P Vv E sp.
Definition kn (C : PSK.consts) (fr : bool) (P Vv E sp wend : expr) (X : PSK.pexprs) : list kentry :=
  kn_sem C P Vv E sp wend X ++ kn_frz C fr P Vv E sp.
(* [comment removed for export] *)
Definition win_f (C : PSK.consts) (P Vv E sp seg wlen : expr) (X : PSK.pexprs) : list kentry :=
  [KBlob (SA seg 0) wlen 1; KUnk (SA seg 0) wlen; KRange wlen 0 16384; KRange seg 4096 140737488355328;
   PSK.kdisj sp (- PSK.c_scr C) (ELit (PSK.c_scr C)) seg 0 wlen; PSK.kdisj P 0 (ELit 272) seg 0 wlen; PSK.kdisj E 0 (ELit 16) seg 0 wlen; PSK.kdisj Vv 0 (ELit 8) seg 0 wlen;
   PSK.kdisj seg 0 wlen (PSK.x_p X) 0 (APC.escale 2 (PSK.x_k X)); PSK.kdisj seg 0 wlen (PSK.x_sb X) 0 (PSK.x_scap X); PSK.hull C seg wlen].
End SPK.
