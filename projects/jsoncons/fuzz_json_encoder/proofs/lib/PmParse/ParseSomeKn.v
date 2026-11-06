(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PSK.
Definition kw (b : expr) (o : Z) (w : nat) (v : expr) : kentry := KWord (SA b o) w v.
Definition kdisj (b1 : expr) (o1 : Z) (n1 : expr) (b2 : expr) (o2 : Z) (n2 : expr) : kentry := KDisj (SA b1 o1) n1 (SA b2 o2) n2.

(* [comment removed for export] *)
Record consts : Type := CONSTS { c_vt_parser : Z; c_vt_func : Z; c_vt_visitor : Z; c_hull_lo : Z; c_hull_hi : Z; c_img_lo : Z; c_img_hi : Z;
                                 c_scr : Z;                       (* [comment removed for export] *)
                                 c_saved : list (Z * nat);        (* [comment removed for export] *)
                                 c_fsz : Z }.                     (* [comment removed for export] *)

(* [comment removed for export] *)
Record pexprs : Type := PX { x_level : expr; x_wptr : expr; x_st : expr; x_sst : expr; x_nst : expr; x_more : expr; x_done : expr;
                             x_k : expr; x_size : expr; x_p : expr; x_sb : expr; x_slen : expr; x_scap : expr; x_line : expr; x_pos : expr; x_ec : expr }.

Definition pconst (C : consts) (P : expr) : list kentry :=
  [kw P 0 8 (ELit (c_vt_parser C)); kw P 8 4 (ELit 1024); kw P 12 1 (ELit 0); kw P 13 1 (ELit 1); kw P 14 1 (ELit 0); kw P 15 1 (ELit 1); kw P 16 1 (ELit 0); kw P 17 1 (ELit 0); kw P 18 1 (ELit 0);
   kw P 24 1 (ELit 0); kw P 25 1 (ELit 0); kw P 48 1 (ELit 0); kw P 49 1 (ELit 0); kw P 72 1 (ELit 0); kw P 73 1 (ELit 0);
   kw P 96 8 (ELit (c_vt_func C)); kw P 128 8 (APC.eaddz P 96); kw P 213 1 (ELit 0); kw P 216 4 (ELit 0)].
Definition pstate_cells (P wend : expr) (X : pexprs) : list kentry :=
  [kw P 144 4 (x_level X); kw P 192 8 wend; kw P 200 8 (x_wptr X); kw P 208 1 (x_st X); kw P 209 1 (x_sst X); kw P 210 1 (x_nst X); kw P 211 1 (x_more X); kw P 212 1 (x_done X);
   kw P 224 8 (APC.eaddz (APC.escale 2 (x_k X)) 1); kw P 232 8 (x_size X); kw P 240 8 (x_p X);
   kw P 248 8 (x_sb X); kw P 256 8 (APC.eadd (x_sb X) (x_slen X)); kw P 264 8 (APC.eadd (x_sb X) (x_scap X));
   kw P 160 8 (x_line X); kw P 168 8 (x_pos X)].
Definition strblk (X : pexprs) : list kentry :=
  let k := x_k X in let size := x_size X in let p := x_p X in
  [kw (APC.eadd size p) 0 1 (ELit 0); KRange k 132 67108864; KRange (APC.esub (APC.eaddz (APC.escale 2 k) (-1)) size) 0 140737488355328; KAlign (APC.escale 2 k) 8;
   KUnk (SA p 0) (APC.escale 2 k); KWr (SA p 0) (APC.escale 2 k); KRange p 4096 140737488355328; KAlign p 16].
(* [comment removed for export] *)
Definition objs_h (E : expr) (X : pexprs) : list kentry :=
  [kw E 0 4 (x_ec X);
   KUnk (SA (x_sb X) 0) (x_scap X); KWr (SA (x_sb X) 0) (x_scap X); KRange (x_sb X) 4096 140737488355328; KRange (x_slen X) 1 1027; KRange (x_scap X) 66 1056;
   KRange (APC.esub (x_scap X) (x_slen X)) 0 1056;
   KRange (x_size X) 0 67108863; KRange (x_level X) 0 1025; KRange (x_st X) 0 255; KRange (x_sst X) 0 255; KRange (x_nst X) 0 255; KRange (x_more X) 0 1; KRange (x_done X) 0 1].
(* [comment removed for export] *)
Definition objs_f (C : consts) (P Vv E seg wlen : expr) : list kentry :=
  [KWr (SA P 0) (ELit 272); KRange P 1099511627776 140737488355328; KAlign P 8;
   KWr (SA E 0) (ELit 16); KRange E 1099511627776 140737488355328;
   kw Vv 0 8 (ELit (c_vt_visitor C)); KRange Vv 1099511627776 140737488355328;
   KBlob (SA seg 0) wlen 1; KUnk (SA seg 0) wlen; KRange wlen 0 16384; KRange seg 0 140737488355328].
Definition frame (C : consts) (sp : expr) (fr : bool) : list kentry :=
  (if fr then map (fun s : Z * nat => kw sp (fst s) 8 (EVar (snd s))) (c_saved C) ++ [KUnk (SA sp (- c_scr C)) (ELit (c_scr C - c_fsz C))] else [KUnk (SA sp (- c_scr C)) (ELit (c_scr C))])
  ++ [KWr (SA sp (- c_scr C)) (ELit (c_scr C)); KRange sp 1099511627776 140737488355328; KAlign sp 16; KImg (c_img_lo C) (c_img_hi C)].
(* [comment removed for export] *)
Definition hull (C : consts) (b n : expr) : kentry := kdisj b 0 n (ELit 0) (c_hull_lo C) (ELit (c_hull_hi C - c_hull_lo C)).
Definition disj_h (C : consts) (P Vv E sp seg wlen : expr) (X : pexprs) : list kentry :=
  let p := x_p X in let pk := APC.escale 2 (x_k X) in let sb := x_sb X in let scap := x_scap X in
  flat_map (fun o : expr * Z * expr => let '(b, lo, n) := o in [kdisj b lo n p 0 pk; kdisj b lo n sb 0 scap])
           [(sp, - c_scr C, ELit (c_scr C)); (P, 0, ELit 272); (E, 0, ELit 16); (Vv, 0, ELit 8); (seg, 0, wlen)]
  ++ [kdisj p 0 pk sb 0 scap; hull C p pk; hull C sb scap].
Definition disj_f (C : consts) (P Vv E sp seg wlen : expr) : list kentry :=
  [kdisj sp (- c_scr C) (ELit (c_scr C)) P 0 (ELit 272); kdisj sp (- c_scr C) (ELit (c_scr C)) E 0 (ELit 16); kdisj sp (- c_scr C) (ELit (c_scr C)) Vv 0 (ELit 8);
   kdisj sp (- c_scr C) (ELit (c_scr C)) seg 0 wlen;
   kdisj P 0 (ELit 272) E 0 (ELit 16); kdisj P 0 (ELit 272) Vv 0 (ELit 8); kdisj P 0 (ELit 272) seg 0 wlen;
   kdisj E 0 (ELit 16) Vv 0 (ELit 8); kdisj E 0 (ELit 16) seg 0 wlen; kdisj Vv 0 (ELit 8) seg 0 wlen; hull C seg wlen].

(* [comment removed for export] *)
Definition pkn_sem (C : consts) (P Vv E sp seg wlen : expr) (X : pexprs) : list kentry :=
  pconst C P ++ pstate_cells P (APC.eadd seg wlen) X ++ strblk X ++ objs_h E X ++ disj_h C P Vv E sp seg wlen X.
Definition pkn_frz (C : consts) (fr : bool) (P Vv E sp seg wlen : expr) : list kentry :=
  objs_f C P Vv E seg wlen ++ frame C sp fr ++ disj_f C P Vv E sp seg wlen.
Definition pkn (C : consts) (fr : bool) (P Vv E sp seg wlen : expr) (X : pexprs) : list kentry :=
  pkn_sem C P Vv E sp seg wlen X ++ pkn_frz C fr P Vv E sp seg wlen.
End PSK.
