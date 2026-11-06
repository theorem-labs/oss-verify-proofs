(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Wellfounded.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec SymStepR.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 MemSplit AsanPlanCore.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosFxStep PIosFxSound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require PIosRegs PIosKit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegLearn SegFPSteps SegFP SegExplore SegLin SegTmpl SegGhost SegCall.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Import AX2. Import AX2B. Import AX2S. Import AX2F. Import SX. Import ST.

Module SP.

(* [comment removed for export] *)
Definition win : Type := (expr * Z * expr)%type.

(* [comment removed for export] *)
Record summ : Type := SUMY { sm_G : nat; sm_pre : tmpl; sm_post : list tmpl; sm_W : list win;
                            sm_A : option (list win);  (* [comment removed for export] *)
                            sm_PS : option expr         (* [comment removed for export] *);
                            sm_PR : bool;               (* [comment removed for export] *)
                            sm_CR : list win            (* [comment removed for export] *) }.
(* [comment removed for export] *)
Definition SUMX (G : nat) (pre : tmpl) (post : list tmpl) (W : list win) (A : option (list win)) (PS : option expr) (PR : bool) : summ :=
  SUMY G pre post W A PS PR [].
Definition SUMA (G : nat) (pre : tmpl) (post : list tmpl) (W : list win) (A : option (list win)) : summ := SUMY G pre post W A None false [].
Definition SUMR (G : nat) (pre : tmpl) (post : list tmpl) (W : list win) (A : option (list win)) (PS : option expr) : summ :=
  SUMY G pre post W A PS true [].
Definition SUM (G : nat) (pre : tmpl) (post : list tmpl) (W : list win) : summ := SUMA G pre post W None.

Record prog : Type := PGY {
  p_G : nat;
  p_tm : list tmpl;
  p_ex : list tmpl;
  p_W : list win;
  p_sp : list split;         (* [comment removed for export] *)
  p_xt : list tmpl;          (* [comment removed for export] *)
  p_cs : list summ;          (* [comment removed for export] *)
  p_A : option (list win);   (* [comment removed for export] *)
  p_PS : option expr;        (* [comment removed for export] *)
  p_CR : list win;           (* [comment removed for export] *)
  p_IK : list kentry         (* [comment removed for export] *)
}.
Definition PGX (G : nat) (tm ex : list tmpl) (W : list win) (sp : list split) (xt : list tmpl) (cs : list summ) (A : option (list win)) : prog :=
  PGY G tm ex W sp xt cs A None [] [].
Definition PGH (G : nat) (tm ex : list tmpl) (W : list win) (sp : list split) (cs : list summ) (A : option (list win))
    (PS : option expr) (CR : list win) (IK : list kentry) : prog := PGY G tm ex W sp [] cs A PS CR IK.
Definition PGS (G : nat) (tm ex : list tmpl) (W : list win) (sp : list split) : prog := PGX G tm ex W sp [] [] None.
Definition PG (G : nat) (tm ex : list tmpl) (W : list win) : prog := PGX G tm ex W [] [] [] None.
Definition PGC (G : nat) (tm ex : list tmpl) (W : list win) (sp : list split) (cs : list summ) : prog := PGX G tm ex W sp [] cs None.
Definition PGCA (G : nat) (tm ex : list tmpl) (W : list win) (sp : list split) (cs : list summ) (A : list win) : prog :=
  PGX G tm ex W sp [] cs (Some A).

Fixpoint find_cs (pc : Z) (l : list summ) : option summ :=
  match l with [] => None | Sm :: r => if Z.eqb (t_pc (sm_pre Sm)) pc then Some Sm else find_cs pc r end.

(* [comment removed for export] *)
Definition pr_match (Sm : summ) (ra : expr) : bool :=
  if sm_PR Sm then match ra with ELit z => forallb (fun X => Z.eqb (t_pc X) z) (sm_post Sm) | _ => false end else true.

Fixpoint find_csr (pc : Z) (ra : expr) (l : list summ) : option summ :=
  match l with
  | [] => None
  | Sm :: r => if Z.eqb (t_pc (sm_pre Sm)) pc then (if pr_match Sm ra then Some Sm else find_csr pc ra r) else find_csr pc ra r
  end.

(* [comment removed for export] *)
Definition ret_ok (IT : itab) (X : tmpl) : bool :=
  match itab_lookup IT (t_pc X) with
  | Some (Jalr rd rs imm) => (Z.eqb (bv_unsigned rd) 0 && Z.eqb (bv_unsigned rs) 1 && Z.eqb (bv_signed imm) 0)%bool
  | _ => false
  end.

(* [comment removed for export] *)
Definition ret_ok' (S : summ) (IT : itab) (X : tmpl) : bool := if sm_PR S then true else ret_ok IT X.
Definition pr_pc_ok (S : summ) (X : tmpl) (rpc : Z) : bool := if sm_PR S then Z.eqb (t_pc X) rpc else true.

(* [comment removed for export] *)
Definition ret_pc (S : summ) (sg : list expr) (X : tmpl) : option Z :=
  match nth 1 (t_regs X) (ELit 0) with
  | EVar j =>
      if Nat.ltb j (sm_G S) then
        match nth j sg (ELit 0) with
        | ELit rpc => if (Z.leb 0 rpc && Z.ltb rpc (2^64) && Z.eqb (Z.land rpc (-2)) rpc)%bool then Some rpc else None
        | _ => None
        end
      else None
  | _ => None
  end.

Fixpoint find_tm (pc : Z) (l : list tmpl) : option tmpl :=
  match l with [] => None | T :: r => if Z.eqb (t_pc T) pc then Some T else find_tm pc r end.

Definition win_closed (G : nat) (w : win) : bool := match w with (b, _, n) => (expr_vars_lt G b && expr_vars_lt G n)%bool end.

(* [comment removed for export] *)
Definition wins_ok (W : list win) (kn : list kentry) (lg : list sentry) : bool :=
  forallb (fun s => SLin.ex2 (fun w => match w with (b, off, n) => xinside kn (a_base (e_addr s)) (a_off (e_addr s)) (elen (e_width s)) b off n end)
                             (fun w => match w with (b, off, n) => SLin.xinside2 kn (a_base (e_addr s)) (a_off (e_addr s)) (elen (e_width s)) b off n end) W) lg.

Definition globals_id (G : nat) (sg : list expr) : bool :=
  forallb (fun j => expr_eqb (nth j sg (ELit 0)) (EVar j)) (seq 0 G).

(* [comment removed for export] *)
Definition zval (kn : list kentry) (e : expr) (hl hu : list SLin.fterm) : bool :=
  let L := lin_of e in
  (SLin.fcheck kn L hl && SLin.fcheck kn ((2^64 - 1 - fst L)%Z, SLin.zscale_ts (-1) (snd L)) hu)%bool.

(* [comment removed for export] *)
Definition zdiff (kn : list kentry) (a b : expr) (d : Z) (h : list SLin.fterm) : bool :=
  let La := lin_of a in let Lb := lin_of b in
  SLin.fcheck kn ((fst La - fst Lb - d)%Z, SLin.zadd_ts (snd La) (SLin.zscale_ts (-1) (snd Lb))) h.

(* [comment removed for export] *)
Definition zval_auto (kn : list kentry) (e : expr) : bool :=
  let L := lin_of e in (SLin.fauto kn L && SLin.fauto kn ((2^64 - 1 - fst L)%Z, SLin.zscale_ts (-1) (snd L)))%bool.
Definition zdiff_auto (kn : list kentry) (a b : expr) (d : Z) : bool :=
  let La := lin_of a in let Lb := lin_of b in
  SLin.fauto kn ((fst La - fst Lb - d)%Z, SLin.zadd_ts (snd La) (SLin.zscale_ts (-1) (snd Lb))).
Definition udiff (kn : list kentry) (a b : expr) (d : Z) (hs : list (list SLin.fterm)) : bool :=
  match hs with
  | [hal; hau; hbl; hbu; hd] => (zval kn a hal hau && zval kn b hbl hbu && zdiff kn a b d hd)%bool
  | _ => (zval_auto kn a && zval_auto kn b && zdiff_auto kn a b d)%bool
  end.

(* [comment removed for export] *)
Definition decreases (kn : list kentry) (T T' : tmpl) (sg : list expr) (hs : list (list SLin.fterm)) : bool :=
  match decide_branch kn BC_LTU (esub sg (t_meas T')) (t_meas T) with
  | Some true => true
  | _ => udiff kn (t_meas T) (esub sg (t_meas T')) 1 hs ||
         (Nat.ltb (t_rank T') (t_rank T) &&
          (match decide_branch kn BC_GEU (t_meas T) (esub sg (t_meas T')) with Some true => true | _ => false end
           || udiff kn (t_meas T) (esub sg (t_meas T')) 0 hs))
  end%bool.

Section Check.
Variable segs : list Segment.
Variable gfp : nat -> list expr -> list SG.gwin.     (* [comment removed for export] *)
Variable gvc : SG.vc -> bool.                       (* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint bad_of (kn : list kentry) (fh : list (nat * (list SLin.fterm * list SLin.fterm))) (i : nat) (l : list kentry) : list kentry :=
  match l with
  | [] => []
  | K :: r => (if kimplied_h segs kn (hfind i fh) K then [] else [K]) ++ bad_of kn fh (S i) r
  end.

(* [comment removed for export] *)
Definition tgt_rest (knp : list kentry) (lg : list sentry) (src tgt : list gatom) : list gatom :=
  List.filter (fun g => negb (SG.keep_ok gfp knp lg src g)) tgt.

(* [comment removed for export] *)
Definition edge_vc (T T' : tmpl) (x : sexit) (kn' : list kentry) (sg : list expr) (fh : list (nat * (list SLin.fterm * list SLin.fterm))) : option SG.vc :=
  let ss := x_ss x in
  let bad := bad_of kn' fh 0 (map (ksub sg) (t_know T')) in
  let rest := tgt_rest (s_know ss) (s_log ss) (t_ghost T) (map (gsub sg) (t_ghost T')) in
  match bad, rest with
  | [], [] => None
  | _, _ => Some (SG.VC (s_know ss) (x_path x) (s_log ss) (t_ghost T) rest bad)
  end.

Definition gedge (T T' : tmpl) (x : sexit) (kn' : list kentry) (sg : list expr) (fh : list (nat * (list SLin.fterm * list SLin.fterm))) : bool :=
  match edge_vc T T' x kn' sg fh with None => true | Some c => gvc c end.

(* [comment removed for export] *)
Definition entailsG (T T' : tmpl) (x : sexit) (kn' : list kentry) (sg : list expr) (fh : list (nat * (list SLin.fterm * list SLin.fterm))) : bool :=
  let ss := x_ss x in
  (Z.eqb (s_pc ss) (t_pc T') && regs_match kn' (s_regs ss) (map (esub sg) (t_regs T')) && gedge T T' x kn' sg fh)%bool.

(* [comment removed for export] *)
Definition stack_win (spc : expr) : SC.wn := (spc, 0, EAlu ALU_SUB (ELit (2^47)) spc).

(* [comment removed for export] *)
Definition sh_of (a : Z) : Z := 0x7fff8000 + Z.shiftr a 3.
Definition sh_above (sp x : Z) : Prop := exists a, sp <= a < 2^47 /\ x = sh_of a.

(* [comment removed for export] *)
Definition stack_shwin (spc : expr) : SC.wn :=
  let b := EAlu ALU_ADD (EAlu ALU_SRL spc (ELit 3)) (ELit 0x7fff8000) in (b, 0, EAlu ALU_SUB (ELit (2^44 + 0x7fff8000)) b).

(* [comment removed for export] *)
Definition pres_rs (P : prog) (S : summ) (sg : list expr) : option (list SC.wn) :=
  match sm_PS S with None => None | Some spc => Some (stack_win (esub sg spc) :: stack_shwin (esub sg spc) :: p_CR P) end.

(* [comment removed for export] *)
Definition ik_of (P : prog) (S : summ) : list kentry := match sm_PS S with None => [] | Some _ => p_IK P end.

(* [comment removed for export] *)
Definition ps_ok (P : prog) (S : summ) (sg : list expr) (kn : list kentry) : bool :=
  match sm_PS S with
  | None => true
  | Some spc =>
      match p_PS P with
      | None => false
      | Some spe =>
          if SL.dtrue (decide_branch kn BC_GEU spe (esub sg spc))
          then SL.dtrue (decide_branch kn BC_LTU (esub sg spc) (ELit (2^47 + 1)))
          else false
      end
  end.

(* [comment removed for export] *)
Definition call_exit (P : prog) (T : tmpl) (x : sexit) (kn' : list kentry) (S : summ) (sg : list expr) (X : tmpl) (rpc : Z) : sexit * list gatom :=
  let ss := x_ss x in let n0 := s_next ss in
  let sg' := SC.post_sg (sm_G S) sg n0 (t_ns X) in
  let Wc := map (SC.sub_win sg) (sm_W S) in
  let PR := pres_rs P S sg in
  let knC := map (ksub sg') (t_know X) ++ List.filter (SC.survivesP kn' Wc PR) kn' ++ ik_of P S in
  let keptC := List.filter (fun g => SG.keep_ok gfp (s_know ss) (s_log ss) (t_ghost T) g && SC.apart_allP kn' (gfp (g_id g) (g_args g)) Wc PR)%bool
                 (t_ghost T) in
  (SXT (SS rpc (map (esub sg') (t_regs X)) [] knC (n0 + t_ns X)) (List.filter SC.is_brb (x_path x)),
   keptC ++ map (gsub sg') (t_ghost X)).

(* [comment removed for export] *)
Definition ret_edge_ok (P : prog) (T : tmpl) (xC : sexit) (src : list gatom) (xh : xhint) : bool :=
  let ssC := x_ss xC in let knC := s_know ssC in
  let T0 := TMG (t_pc T) (t_regs T) (t_know T) (t_ns T) (t_meas T) (t_rank T) src in
  match find_tm (s_pc ssC) (p_tm P ++ p_xt P) with
  | Some T' => let sg := mk_sg (p_G P) T' (s_regs ssC) knC (xh_sg xh) in
               (Nat.leb (p_G P) (t_ns T') && globals_id (p_G P) sg && Nat.eqb (length sg) (t_ns T')
                && entailsG T0 T' xC knC sg (xh_fk xh) && decreases (map (ksub sg) (t_know T') ++ knC) T T' sg (xh_dec xh))%bool
  | None =>
    match find_tm (s_pc ssC) (p_ex P) with
    | Some X => let sg := mk_sg (p_G P) X (s_regs ssC) knC (xh_sg xh) in
                (Nat.leb (p_G P) (t_ns X) && globals_id (p_G P) sg && Nat.eqb (length sg) (t_ns X)
                 && entailsG T0 X xC knC sg (xh_fk xh))%bool
    | None => false
    end
  end.

(* [comment removed for export] *)
Definition acc_cont (A : option (list win)) (Ac : option (list win)) (sg : list expr) (kn : list kentry) : bool :=
  match A, Ac with
  | None, None => true
  | Some WA, Some WcA =>
      forallb (fun wc => let '(b, off, n) := SC.sub_win sg wc in
                         existsb (fun w' => let '(b', off', n') := w' in SLin.xinside2 kn b off n b' off' n') WA) WcA
  | _, _ => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint dstk_l (spe : expr) (W : list win) : option Z :=
  match W with
  | [] => None
  | (b, off, ELit n) :: r => if (expr_eqb b spe && Z.eqb off (- n) && Z.leb 0 n && Z.ltb n (2^47))%bool then Some n else dstk_l spe r
  | _ :: r => dstk_l spe r
  end.
Definition dstk (PS : option expr) (W : list win) : option (expr * Z) :=
  match PS with None => None | Some spe => match dstk_l spe W with Some n => Some (spe, n) | None => None end end.
Definition stk_ok (P : prog) (S : summ) (sg : list expr) (kn : list kentry) : bool :=
  match dstk (sm_PS S) (sm_W S) with
  | None => true
  | Some (spc, n') => match dstk (p_PS P) (p_W P) with
                      | None => false
                      | Some (spe, n) =>
                          (* [comment removed for export] *)
                          if SLin.xinside2 kn (esub sg spc) (- n') (ELit n') spe (- n) (ELit n) then true
                          else if shares_var (esub sg spc) spe then false
                          else SLin.xinside_f kn (esub sg spc) (- n') (ELit n') spe (- n) (ELit n)
                      end
  end.

(* [comment removed for export] *)
Definition crw_in (kn : list kentry) (b : expr) (k : Z) (n : expr) (w : win) : bool :=
  let '(b', k', n') := w in
  if SLin.xinside2 kn b k n b' k' n' then true else if shares_var b b' then false else SLin.xinside_f kn b k n b' k' n'.
Definition crs_ok (P : prog) (S : summ) (sg : list expr) (kn : list kentry) : bool :=
  forallb (fun wc => let '(b, k, n) := SC.sub_win sg wc in SLin.lex (crw_in kn b k n) (p_CR P)) (sm_CR S).

Definition call_edge_ok (P : prog) (IT : itab) (T : tmpl) (x : sexit) (xh : xhint) (S : summ) : bool :=
  let ss := x_ss x in
  match exit_kn ss with
  | None => false
  | Some kn' =>
    let sg := mk_sg 0 (sm_pre S) (s_regs ss) kn' (xh_sg xh) in
    let Wc := map (SC.sub_win sg) (sm_W S) in
    (wins_ok (p_W P) (s_know ss) (s_log ss)
     && Nat.eqb (length sg) (t_ns (sm_pre S)) && forallb (expr_vars_lt (s_next ss)) sg
     && Nat.leb (t_ns T) (s_next ss)
     && entailsG T (sm_pre S) x kn' sg (xh_fk xh)
     && forallb (fun wc => let '(b, off, n) := wc in
                           existsb (fun w' => let '(b', off', n') := w' in SLin.xinside2 kn' b off n b' off' n') (p_W P)) Wc
     && acc_cont (p_A P) (sm_A S) sg kn' && ps_ok P S sg kn' && stk_ok P S sg kn' && crs_ok P S sg kn'
     && forallb (fun X => (ret_ok' S IT X && Nat.leb (sm_G S) (t_ns X) &&
                           match ret_pc S sg X with
                           | Some rpc => if pr_pc_ok S X rpc then (let '(xC, src) := call_exit P T x kn' S sg X rpc in ret_edge_ok P T xC src xh0)
                                         else false
                           | None => false
                           end)%bool) (sm_post S))%bool
  end.

Definition edge_ok (P : prog) (IT : itab) (T : tmpl) (x : sexit) (xh : xhint) : bool :=
  let ss := x_ss x in
  match exit_kn ss with
  | None => false
  | Some kn' =>
    match find_tm (s_pc ss) (p_tm P ++ p_xt P) with
    | Some T' => let sg := mk_sg (p_G P) T' (s_regs ss) kn' (xh_sg xh) in
                 (wins_ok (p_W P) (s_know ss) (s_log ss) &&
                  Nat.leb (p_G P) (t_ns T') && globals_id (p_G P) sg && Nat.eqb (length sg) (t_ns T')
                  && entailsG T T' x kn' sg (xh_fk xh) && decreases (map (ksub sg) (t_know T') ++ kn') T T' sg (xh_dec xh))%bool
    | None =>
      match find_csr (s_pc ss) (nth 1 (s_regs ss) (ELit 0)) (p_cs P) with
      | Some Sm => call_edge_ok P IT T x xh Sm
      | None =>
        match find_tm (s_pc ss) (p_ex P) with
        | Some X => let sg := mk_sg (p_G P) X (s_regs ss) kn' (xh_sg xh) in
                    (wins_ok (p_W P) (s_know ss) (s_log ss) &&
                     Nat.leb (p_G P) (t_ns X) && globals_id (p_G P) sg && Nat.eqb (length sg) (t_ns X)
                     && entailsG T X x kn' sg (xh_fk xh))%bool
        | None => false
        end
      end
    end
  end%bool.

Fixpoint edges_ok (P : prog) (IT : itab) (T : tmpl) (xs : list sexit) (hss : list xhint) : bool :=
  match xs with
  | [] => true
  | x :: xr => (edge_ok P IT T x (hd xh0 hss) && edges_ok P IT T xr (tl hss))%bool
  end.

Definition p_stops (P : prog) : list Z :=
  map t_pc (p_tm P) ++ map t_pc (p_xt P) ++ map (fun S => t_pc (sm_pre S)) (p_cs P) ++ map t_pc (p_ex P).

Definition tm_check (P : prog) (IT : itab) (fuel : nat) (rr : bool) (T : tmpl) (hss : list xhint) : bool :=
  let ss := tstate T in
  match explore segs IT (p_stops P) rr (p_sp P) (p_A P) fuel true false (mkbc (facts_of (s_know ss))) (mk_kix (s_know ss)) ss [] with
  | Some xs => (Nat.leb (p_G P) (t_ns T) && edges_ok P IT T xs hss)%bool
  | None => false
  end.

Fixpoint tms_check (P : prog) (IT : itab) (fuel : nat) (rr : bool) (l : list tmpl) (hints : list (list xhint)) : bool :=
  match l with
  | [] => true
  | T :: r => (tm_check P IT fuel rr T (hd [] hints) && tms_check P IT fuel rr r (tl hints))%bool
  end.

Definition ps_closed (G : nat) (PS : option expr) : bool := match PS with None => true | Some e => expr_vars_lt G e end.

(* [comment removed for export] *)
Definition pcheckH (P : prog) (IT : itab) (fuel : nat) (rr : bool) (hints : list (list xhint)) : bool :=
  (forallb tm_closed (p_tm P) && forallb tm_closed (p_ex P) && forallb tm_closed (p_xt P) && forallb (win_closed (p_G P)) (p_W P)
   && forallb (fun T => Nat.leb (p_G P) (t_ns T)) (p_xt P)
   && forallb (fun S => tm_closed (sm_pre S) && forallb tm_closed (sm_post S) && Nat.leb (sm_G S) (t_ns (sm_pre S))
                        && aw_closed (sm_G S) (sm_A S) && ps_closed (sm_G S) (sm_PS S))%bool (p_cs P)
   && aw_closed (p_G P) (p_A P)
   && ps_closed (p_G P) (p_PS P) && forallb (win_closed (p_G P)) (p_CR P) && kn_vars_lt (p_G P) (p_IK P)
   && tms_check P IT fuel rr (p_tm P) hints)%bool.

(* [comment removed for export] *)
Definition pcheck (P : prog) (IT : itab) (fuel : nat) (rr : bool) (hints : list (list xhint)) : bool :=
  (pcheckH P IT fuel rr hints && match p_IK P with [] => true | _ => false end)%bool.

Lemma pcheck_pcheckH : forall P IT fuel rr hints, pcheck P IT fuel rr hints = true -> pcheckH P IT fuel rr hints = true.
Proof. intros P IT fuel rr hints H. unfold pcheck in H. apply andb_prop in H as [H _]. exact H. Qed.

End Check.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition win_den (E : env) (w : win) : Z * Z :=
  match w with (b, off, n) => (bv_unsigned (edenot E b) + off, bv_unsigned (edenot E b) + off + bv_unsigned (edenot E n))%Z end.

Definition outside_wins (E : env) (W : list win) (x : Z) : Prop :=
  Forall (fun w => let '(lo, hi) := win_den E w in ~ (lo <= x < hi)%Z) W.

Definition gagree (G : nat) (E E' : env) : Prop := forall j, (j < G)%nat -> ev E j = ev E' j.

Lemma gagree_refl : forall G E, gagree G E E. Proof. intros G E j _. reflexivity. Qed.
Lemma gagree_trans : forall G E1 E2 E3, gagree G E1 E2 -> gagree G E2 E3 -> gagree G E1 E3.
Proof. intros G E1 E2 E3 H1 H2 j Hj. rewrite H1 by exact Hj. apply H2. exact Hj. Qed.

Lemma edenot_gagree : forall G E E' e, gagree G E E' -> eb E = eb E' -> expr_vars_lt G e = true -> edenot E e = edenot E' e.
Proof.
  intros G E E' e Hg Hb He. apply (edenot_agree G E E' e); [|exact He]. split; [exact Hg | exact Hb].
Qed.

Lemma win_den_gagree : forall G E E' w, gagree G E E' -> eb E = eb E' -> win_closed G w = true -> win_den E w = win_den E' w.
Proof.
  intros G E E' [[b off] n] Hg Hb Hc. cbn [win_closed] in Hc. apply andb_prop in Hc as [Hcb Hcn].
  cbn [win_den]. rewrite (edenot_gagree G E E' b Hg Hb Hcb), (edenot_gagree G E E' n Hg Hb Hcn). reflexivity.
Qed.

Lemma outside_wins_gagree : forall G E E' W x, gagree G E E' -> eb E = eb E' -> forallb (win_closed G) W = true ->
  outside_wins E W x -> outside_wins E' W x.
Proof.
  intros G E E' W x Hg Hb Hc H. unfold outside_wins in *. apply Forall_forall. intros w Hw.
  rewrite <- (win_den_gagree G E E' w Hg Hb (proj1 (forallb_forall _ _) Hc w Hw)).
  exact (proj1 (Forall_forall _ _) H w Hw).
Qed.

Section Sound.
Variable segs : list Segment.
Variable GP : nat -> list word -> (word -> option byte) -> Prop.    (* [comment removed for export] *)
Variable gfp : nat -> list expr -> list SG.gwin.
Variable gvc : SG.vc -> bool.
Hypothesis HGF : SG.gp_frameP GP gfp.
Hypothesis HGV : forall c, gvc c = true -> SG.vc_holds segs GP c.

Lemma elenZ_elen8 : forall E w, (w <= 8)%nat -> elenZ E (elen w) = Z.of_nat w.
Proof. exact elenZ_elen'. Qed.

(* [comment removed for export] *)
Lemma mem_denot_outside_wins : forall E W kn base lg x,
  know_ok segs E base kn -> log_flat E lg -> wins_ok W kn lg = true ->
  outside_wins E W (bv_unsigned x) -> mem_denot E base lg x = base x.
Proof.
  intros E W kn base lg x HK. induction lg as [|[a w v] rest IH]; intros Hlf Hw Hout; [reflexivity|].
  cbn [log_flat] in Hlf. destruct Hlf as (Hw8 & Hfa & Hlf'). cbn [wins_ok forallb] in Hw. apply andb_prop in Hw as [Hw1 Hw2].
  cbn [mem_denot]. rewrite <- (IH Hlf' Hw2 Hout).
  rewrite SLin.ex2_eq in Hw1 by (intros [[b0 o0] l0] Hx0; apply SLin.xinside_2; exact Hx0).
  apply existsb_exists in Hw1 as ([[b off] n] & Hin & Hx). cbn [e_addr e_width] in Hx.
  destruct (SLin.xinside2_sound segs E base kn (a_base a) (a_off a) (elen w) b off n HK Hx) as [A B].
  rewrite elenZ_elen8 in B by exact Hw8.
  pose proof (proj1 (Forall_forall _ _) Hout _ Hin) as Ho. cbn [win_den] in Ho.
  unfold estart in A, B. cbn [a_base a_off] in A, B. unfold elenZ in B.
  destruct a as [ab ak]. cbn [a_base a_off] in *.
  pose proof (flat_u E _ _ Hfa) as Hu. unfold estart in Hu. cbn [a_base a_off] in Hu.
  apply wbytes_outside.
  - rewrite length_N_to_le_bytes, Hu. destruct Hfa as (?&?&?&?). unfold estart in *. cbn [a_base a_off] in *. lia.
  - rewrite length_N_to_le_bytes, Hu. lia.
Qed.

Lemma globals_id_ok : forall G sg j, globals_id G sg = true -> (j < G)%nat -> nth j sg (ELit 0) = EVar j.
Proof.
  intros G sg j H Hj. unfold globals_id in H. pose proof (proj1 (forallb_forall _ _) H j ltac:(apply in_seq; lia)) as X.
  exact (expr_eqb_eq _ _ X).
Qed.

Lemma senv_gagree : forall G E sg, globals_id G sg = true -> gagree G E (senv E sg).
Proof.
  intros G E sg H j Hj. cbn [senv ev]. unfold vals_ev.
  assert (Hl : (j < length sg)%nat \/ (length sg <= j)%nat) by lia.
  destruct Hl as [Hl|Hl].
  - rewrite (nth_indep _ (Z_to_bv 64 0) (edenot E (ELit 0))) by (rewrite length_map; exact Hl).
    rewrite map_nth, (globals_id_ok G sg j H Hj). reflexivity.
  - exfalso. unfold globals_id in H. pose proof (proj1 (forallb_forall _ _) H j ltac:(apply in_seq; lia)) as X.
    cbv beta in X. rewrite nth_overflow in X by exact Hl. discriminate.
Qed.

Lemma eagree_gagree : forall G n E E', (G <= n)%nat -> eagree n E E' -> gagree G E E'.
Proof. intros G n E E' Hle [Ha _] j Hj. apply Ha. lia. Qed.

Lemma find_tm_in : forall pc l T, find_tm pc l = Some T -> In T l /\ t_pc T = pc.
Proof.
  intros pc l. induction l as [|T0 r IH]; intros T H; [discriminate|]. cbn [find_tm] in H.
  destruct (Z.eqb (t_pc T0) pc) eqn:E; [injection H as <-; split; [left; reflexivity | apply Z.eqb_eq; exact E]|].
  destruct (IH T H) as [A B]. split; [right; exact A | exact B].
Qed.

Lemma edges_ok_in : forall P IT T xs hss x, edges_ok segs gfp gvc P IT T xs hss = true -> In x xs -> exists hs, edge_ok segs gfp gvc P IT T x hs = true.
Proof.
  intros P IT T xs. induction xs as [|x0 xr IH]; intros hss x H Hin; [destruct Hin|].
  cbn [edges_ok] in H. apply andb_prop in H as [H1 H2]. destruct Hin as [<-|Hin]; [eexists; exact H1|].
  exact (IH _ x H2 Hin).
Qed.

Lemma tms_check_in : forall P IT fuel rr l hints T, tms_check segs gfp gvc P IT fuel rr l hints = true -> In T l ->
  exists hss, tm_check segs gfp gvc P IT fuel rr T hss = true.
Proof.
  intros P IT fuel rr l. induction l as [|T0 r IH]; intros hints T H Hin; [destruct Hin|].
  cbn [tms_check] in H. apply andb_prop in H as [H1 H2]. destruct Hin as [<-|Hin]; [eexists; exact H1|].
  exact (IH _ T H2 Hin).
Qed.

Lemma zval_ok : forall E M kn e hl hu, know_ok segs E M kn -> zval kn e hl hu = true ->
  bv_unsigned (edenot E e) = (fst (lin_of e) + tden E (snd (lin_of e)))%Z.
Proof.
  intros E M kn e hl hu HK H. unfold zval in H. apply andb_prop in H as [H1 H2].
  pose proof (SLin.fcheck_sound segs E M kn _ hl HK H1) as A. pose proof (SLin.fcheck_sound segs E M kn _ hu HK H2) as B.
  unfold SLin.zden in A, B. cbn [fst snd] in A, B. rewrite SLin.zscale_den in B.
  pose proof (lin_of_sound E e) as [q Hq]. unfold lden, uE in Hq.
  pose proof (bv_unsigned_in_range 64 (edenot E e)) as R. unfold bv_modulus in R. cbn in R.
  assert (q = 0) by nia. subst q. lia.
Qed.

Lemma zval_auto_ok : forall E M kn e, know_ok segs E M kn -> zval_auto kn e = true ->
  bv_unsigned (edenot E e) = (fst (lin_of e) + tden E (snd (lin_of e)))%Z.
Proof.
  intros E M kn e HK H. unfold zval_auto in H. apply andb_prop in H as [H1 H2].
  pose proof (SLin.fauto_sound segs E M kn _ HK H1) as A. pose proof (SLin.fauto_sound segs E M kn _ HK H2) as B.
  unfold SLin.zden in A, B. cbn [fst snd] in A, B. rewrite SLin.zscale_den in B.
  pose proof (lin_of_sound E e) as [q Hq]. unfold lden, uE in Hq.
  pose proof (bv_unsigned_in_range 64 (edenot E e)) as R. unfold bv_modulus in R. cbn in R.
  assert (q = 0) by nia. subst q. lia.
Qed.

Lemma udiff_ok : forall E M kn a b d hs, know_ok segs E M kn -> udiff kn a b d hs = true ->
  (bv_unsigned (edenot E b) + d <= bv_unsigned (edenot E a))%Z.
Proof.
  intros E M kn a b d hs HK H. unfold udiff in H.
  assert (AUTO : (zval_auto kn a && zval_auto kn b && zdiff_auto kn a b d)%bool = true ->
                 (bv_unsigned (edenot E b) + d <= bv_unsigned (edenot E a))%Z).
  { intros H0. apply andb_prop in H0 as [H0 H3]. apply andb_prop in H0 as [H1 H2].
    rewrite (zval_auto_ok E M kn a HK H1), (zval_auto_ok E M kn b HK H2).
    pose proof (SLin.fauto_sound segs E M kn _ HK H3) as D. unfold SLin.zden in D. cbn [fst snd] in D.
    rewrite SLin.zadd_den, SLin.zscale_den in D. lia. }
  destruct hs as [|hal [|hau [|hbl [|hbu [|hd [|]]]]]]; try (exact (AUTO H)).
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  rewrite (zval_ok E M kn a _ _ HK H1), (zval_ok E M kn b _ _ HK H2).
  pose proof (SLin.fcheck_sound segs E M kn _ hd HK H3) as D. unfold SLin.zden in D. cbn [fst snd] in D.
  rewrite SLin.zadd_den, SLin.zscale_den in D. lia.
Qed.

Lemma bad_of_sound : forall E M kn fh l i, know_ok segs E M kn -> know_ok segs E M (bad_of segs kn fh i l) -> know_ok segs E M l.
Proof.
  intros E M kn fh l. induction l as [|K r IH]; intros i HK HB; [constructor|].
  cbn [bad_of] in HB. apply Forall_app in HB as [H1 H2]. constructor; [|exact (IH (S i) HK H2)].
  destruct (kimplied_h segs kn (hfind i fh) K) eqn:E1.
  - exact (kimplied_h_ok segs E M kn _ K HK E1).
  - inversion H1; assumption.
Qed.

Lemma tgt_rest_sound : forall E m kn lg src tgt, know_ok segs E m kn -> log_flat E lg -> SG.gholds GP E m src ->
  SG.gholds GP E (mem_denot E m lg) (tgt_rest gfp kn lg src tgt) -> SG.gholds GP E (mem_denot E m lg) tgt.
Proof.
  intros E m kn lg src tgt HK HL HS HR. unfold SG.gholds in *. apply Forall_forall. intros g Hg.
  destruct (SG.keep_ok gfp kn lg src g) eqn:Hk.
  - exact (SG.keep_ok_sound segs GP gfp E m kn lg src g HGF HK HL HS Hk).
  - apply (proj1 (Forall_forall _ _) HR g). unfold tgt_rest. apply filter_In. split; [exact Hg|]. rewrite Hk. reflexivity.
Qed.

Lemma gedge_sound : forall T T' x kn' sg fh E m,
  gedge segs gfp gvc T T' x kn' sg fh = true ->
  know_ok segs E m (s_know (x_ss x)) -> scs_denot segs m E (x_path x) -> log_flat E (s_log (x_ss x)) ->
  SG.gholds GP E m (t_ghost T) -> know_ok segs E (mem_denot E m (s_log (x_ss x))) kn' ->
  know_ok segs E (mem_denot E m (s_log (x_ss x))) (map (ksub sg) (t_know T'))
  /\ SG.gholds GP E (mem_denot E m (s_log (x_ss x))) (map (gsub sg) (t_ghost T')).
Proof.
  intros T T' x kn' sg fh E m H HK HP HL HS HK'. unfold gedge, edge_vc in H.
  set (bad := bad_of segs kn' fh 0 (map (ksub sg) (t_know T'))) in *.
  set (rest := tgt_rest gfp (s_know (x_ss x)) (s_log (x_ss x)) (t_ghost T) (map (gsub sg) (t_ghost T'))) in *.
  assert (VC : SG.gholds GP E (mem_denot E m (s_log (x_ss x))) rest /\ know_ok segs E (mem_denot E m (s_log (x_ss x))) bad).
  { destruct bad as [|b0 bad'] eqn:Hb; destruct rest as [|r0 rest'] eqn:Hr;
      [ split; [unfold SG.gholds; apply Forall_nil | apply Forall_nil] | exact (HGV _ H E m HK HP HL HS) ..]. }
  destruct VC as [VR VB]. split.
  - exact (bad_of_sound E _ kn' fh _ 0 HK' VB).
  - exact (tgt_rest_sound E m _ _ _ _ HK HL HS VR).
Qed.

Section FX.
Context {fx : FPState}.
Lemma entailsG_sound : forall T T' x kn' sg fh E m rom R,
  entailsG segs gfp gvc T T' x kn' sg fh = true ->
  know_ok segs E m (s_know (x_ss x)) -> scs_denot segs m E (x_path x) -> log_flat E (s_log (x_ss x)) ->
  SG.gholds GP E m (t_ghost T) -> know_ok segs E (mem_denot E m (s_log (x_ss x))) kn' -> regs_ok E (s_regs (x_ss x)) R ->
  tm_ok segs T' (senv E sg) (mem_denot E m (s_log (x_ss x))) rom (mkst R (Z_to_bv 64 (s_pc (x_ss x))) (mem_denot E m (s_log (x_ss x))) rom)
  /\ SG.gholds GP (senv E sg) (mem_denot E m (s_log (x_ss x))) (t_ghost T').
Proof.
  intros T T' x kn' sg fh E m rom R H HK HP HL HS HK' HR. unfold entailsG in H.
  apply andb_prop in H as [H Hg]. apply andb_prop in H as [Hpc Hsr]. apply Z.eqb_eq in Hpc.
  destruct (gedge_sound T T' x kn' sg fh E m Hg HK HP HL HS HK') as [HF HA].
  pose proof (regs_match_ok segs E _ kn' _ _ HK' Hsr) as RM.
  split; [|exact (SG.gholds_sub GP E _ sg _ HA)].
  exists R. cbn [tstate s_pc s_regs s_log s_know mem_denot]. rewrite Hpc.
  split; [reflexivity|]. split.
  { intros r. rewrite (HR r), (RM r), sr_get_map. symmetry. apply esub_den. }
  split; [exact I|]. apply know_ok_ksub. exact HF.
Qed.
End FX.


(* [comment removed for export] *)
Lemma lex_ind : forall (Q : nat -> nat -> Prop),
  (forall n r, (forall n' r', (n' < n \/ (n' = n /\ r' < r))%nat -> Q n' r') -> Q n r) -> forall n r, Q n r.
Proof.
  intros Q H n. induction n as [n IHn] using (well_founded_induction lt_wf).
  intros r. induction r as [r IHr] using (well_founded_induction lt_wf).
  apply H. intros n' r' [Hn|[-> Hr]]; [apply IHn; exact Hn | apply IHr; exact Hr].
Qed.

Definition mval (T : tmpl) (E : env) : nat := Z.to_nat (bv_unsigned (edenot E (t_meas T))).

(* [comment removed for export] *)
Definition prun_post (P : prog) (E : env) (M rom : word -> option byte) (ms' : machine_state) : Prop :=
  exists X E' M', In X (p_ex P) /\ tm_okF segs X E' M' rom ms' /\ SG.gholds GP E' M' (t_ghost X)
    /\ gagree (p_G P) E E' /\ eb E' = eb E
    /\ (forall x : word, outside_wins E (p_W P) (bv_unsigned x) -> M' x = M x).

(* [comment removed for export] *)
Definition ext_ok (P : prog) (TA : tmpl) : Prop :=
  forall E M rom ms, aw_genuine E (p_A P) -> tm_okF segs TA E M rom ms -> SG.gholds GP E M (t_ghost TA) ->
  exists ms', ExecF.mstepsF segs (fp_of (p_A P) E) ms ms' /\
    ((exists TB E' M', In TB (p_tm P ++ p_xt P) /\ tm_okF segs TB E' M' rom ms' /\ SG.gholds GP E' M' (t_ghost TB)
        /\ gagree (p_G P) E E' /\ eb E' = eb E /\ (forall x : word, outside_wins E (p_W P) (bv_unsigned x) -> M' x = M x)
        /\ (mval TB E' < mval TA E \/ (mval TB E' = mval TA E /\ t_rank TB < t_rank TA))%nat)
     \/ prun_post P E M rom ms').

(* [comment removed for export] *)
Definition summ_ok (S : summ) : Prop :=
  forall E M rom ms, aw_genuine E (sm_A S) -> tm_okF segs (sm_pre S) E M rom ms -> SG.gholds GP E M (t_ghost (sm_pre S)) ->
  exists ms' X E' M', ExecF.mstepsF segs (fp_of (sm_A S) E) ms ms' /\ In X (sm_post S) /\ tm_okF segs X E' M' rom ms' /\ SG.gholds GP E' M' (t_ghost X)
    /\ gagree (sm_G S) E E' /\ eb E' = eb E /\ (forall x : word, outside_wins E (sm_W S) (bv_unsigned x) -> M' x = M x).

(* [comment removed for export] *)
(* [comment removed for export] *)
Variable hmH : (word -> option byte) -> Prop.
Variable hmA : Z -> Prop.
Variable hmC : Z -> Z -> Prop.
Variable hmR : (word -> option byte) -> Prop.    (* [comment removed for export] *)

Definition wins_client (E : env) (W : list win) : Prop := Forall (fun w => hmC (fst (win_den E w)) (snd (win_den E w))) W.

Hypothesis HMC_sub : forall lo hi lo' hi', hmC lo hi -> lo <= lo' -> hi' <= hi -> hmC lo' hi'.
Hypothesis HMF : forall E W M M', wins_client E W -> hmH M -> PIosRegs.wrel segs M M' ->
  (forall x : word, outside_wins E W (bv_unsigned x) -> M' x = M x) -> hmH M'.

(* [comment removed for export] *)
Definition frame_ok (E : env) (W : list win) (PS : option expr) (M M' : word -> option byte) : Prop :=
  match PS with
  | None => forall x : word, outside_wins E W (bv_unsigned x) -> M' x = M x
  | Some spe => forall x : word, outside_wins E W (bv_unsigned x) ->
                  (bv_unsigned (edenot E spe) <= bv_unsigned x < 2^47 \/ sh_above (bv_unsigned (edenot E spe)) (bv_unsigned x)
                   \/ hmA (bv_unsigned x)) -> M' x = M x
  end.

Lemma frame_ok_full : forall E W PS M M', (forall x : word, outside_wins E W (bv_unsigned x) -> M' x = M x) -> frame_ok E W PS M M'.
Proof. intros E W [spe|] M M' H; cbn [frame_ok]; [intros x Hx _; exact (H x Hx) | exact H]. Qed.

(* [comment removed for export] *)
Lemma sh_above_mono : forall s s' x, s' <= s -> sh_above s x -> sh_above s' x.
Proof. intros s s' x Hs (a & Ha & ->). exists a. split; [lia | reflexivity]. Qed.

(* [comment removed for export] *)
Lemma shwin_sh_above : forall E spc z, bv_unsigned (edenot E spc) <= 2^47 ->
  SC.in_win E (stack_shwin spc) z -> sh_above (bv_unsigned (edenot E spc)) z.
Proof.
  intros E spc z Hs Hin. unfold SC.in_win, stack_shwin, SG.win_den in Hin. cbn [edenot] in Hin.
  set (s := bv_unsigned (edenot E spc)) in *.
  assert (Hs0 : 0 <= s) by (pose proof (bv_unsigned_in_range 64 (edenot E spc)) as R; unfold s; lia).
  assert (Hq : bv_unsigned (alu64 ALU_SRL (edenot E spc) (Z_to_bv 64 3)) = s / 8).
  { rewrite u_srl64, u_lit64a. rewrite (Z.mod_small 3 (2^64)) by lia. rewrite (Z.mod_small 3 64) by lia. reflexivity. }
  assert (Hb : bv_unsigned (alu64 ALU_ADD (alu64 ALU_SRL (edenot E spc) (Z_to_bv 64 3)) (Z_to_bv 64 0x7fff8000)) = s / 8 + 0x7fff8000).
  { rewrite u_add64, Hq, u_lit64a. rewrite (Z.mod_small 0x7fff8000 (2^64)) by lia.
    apply Z.mod_small. split; [apply Z.add_nonneg_nonneg; [apply Z.div_pos|]; lia|].
    assert (s / 8 <= 2^44) by (apply Z.div_le_upper_bound; lia). lia. }
  rewrite u_sub64, Hb, u_lit64a in Hin. rewrite (Z.mod_small (2^44 + 0x7fff8000) (2^64)) in Hin by lia.
  assert (Hd : s / 8 <= 2^44) by (apply Z.div_le_upper_bound; lia).
  rewrite (Z.mod_small (2^44 + 0x7fff8000 - (s / 8 + 0x7fff8000)) (2^64)) in Hin by lia.
  assert (Hz : s / 8 <= z - 0x7fff8000 < 2^44) by lia.
  unfold sh_above, sh_of. exists (Z.max s (8 * (z - 0x7fff8000))).
  rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  destruct (Z.le_gt_cases s (8 * (z - 0x7fff8000))) as [Hle|Hgt].
  - rewrite Z.max_r by exact Hle. split; [lia|]. rewrite Z.mul_comm, Z.div_mul by lia. lia.
  - rewrite Z.max_l by lia. assert (E8 : s / 8 = z - 0x7fff8000) by (clear - Hz Hgt Hs0; Z.div_mod_to_equations; lia).
    split; [split; [lia|]|lia]. clear - E8 Hz Hs Hs0. Z.div_mod_to_equations; lia.
Qed.

Lemma frame_ok_refl : forall E W PS M, frame_ok E W PS M M.
Proof. intros E W PS M. apply frame_ok_full. intros x _. reflexivity. Qed.

Lemma frame_ok_trans_g : forall G E E' W PS M1 M2 M3, gagree G E E' -> eb E = eb E' -> forallb (win_closed G) W = true ->
  ps_closed G PS = true -> frame_ok E W PS M1 M2 -> frame_ok E' W PS M2 M3 -> frame_ok E W PS M1 M3.
Proof.
  intros G E E' W [spe|] M1 M2 M3 Hg Hb HW HPS F1 F2; cbn [frame_ok ps_closed] in *.
  - intros x Hx Hc. rewrite (F2 x (outside_wins_gagree G E E' W _ Hg Hb HW Hx)); [exact (F1 x Hx Hc)|].
    rewrite <- (edenot_gagree G E E' spe Hg Hb HPS). exact Hc.
  - intros x Hx. rewrite (F2 x (outside_wins_gagree G E E' W _ Hg Hb HW Hx)). exact (F1 x Hx).
Qed.

(* [comment removed for export] *)
Definition prun_postH (P : prog) (E : env) (M rom : word -> option byte) (ms' : machine_state) : Prop :=
  exists X E' M', In X (p_ex P) /\ tm_okF segs X E' M' rom ms' /\ SG.gholds GP E' M' (t_ghost X)
    /\ gagree (p_G P) E E' /\ eb E' = eb E /\ hmH M' /\ frame_ok E (p_W P) (p_PS P) M M'.

(* [comment removed for export] *)
Definition ext_okH (P : prog) (Cnd : env -> Prop) (TA : tmpl) : Prop :=
  forall E M rom ms, hmR rom -> aw_genuine E (p_A P) -> Cnd E -> hmH M -> tm_okF segs TA E M rom ms -> SG.gholds GP E M (t_ghost TA) ->
  exists ms', ExecF.mstepsF segs (fp_of (p_A P) E) ms ms' /\
    ((exists TB E' M', In TB (p_tm P ++ p_xt P) /\ tm_okF segs TB E' M' rom ms' /\ SG.gholds GP E' M' (t_ghost TB)
        /\ gagree (p_G P) E E' /\ eb E' = eb E /\ hmH M' /\ frame_ok E (p_W P) (p_PS P) M M'
        /\ (mval TB E' < mval TA E \/ (mval TB E' = mval TA E /\ t_rank TB < t_rank TA))%nat)
     \/ prun_postH P E M rom ms').

(* [comment removed for export] *)
Definition summ_okH (S : summ) : Prop :=
  forall E M rom ms, hmR rom -> aw_genuine E (sm_A S) -> wins_client E (sm_W S) -> hmH M -> tm_okF segs (sm_pre S) E M rom ms ->
    SG.gholds GP E M (t_ghost (sm_pre S)) ->
  exists ms' X E' M', ExecF.mstepsF segs (fp_of (sm_A S) E) ms ms' /\ In X (sm_post S) /\ tm_okF segs X E' M' rom ms' /\ SG.gholds GP E' M' (t_ghost X)
    /\ gagree (sm_G S) E E' /\ eb E' = eb E /\ hmH M' /\ frame_ok E (sm_W S) (sm_PS S) M M'.

(* [comment removed for export] *)
Lemma senv_nth : forall E sg j, ev (senv E sg) j = edenot E (nth j sg (ELit 0)).
Proof.
  intros E sg j. cbn [senv ev]. unfold vals_ev.
  change (Z_to_bv 64 0) with (edenot E (ELit 0)). apply map_nth.
Qed.

Lemma ksub_ok_inv : forall E m sg K, kentry_ok segs (senv E sg) m K -> kentry_ok segs E m (ksub sg K).
Proof.
  intros E m sg K H.
  destruct K as [a w v|a n|a n k|lo hi|e md|e lo hi|a n|a1 n1 a2 n2|a n c|a n]; cbn [ksub kentry_ok] in H |- *;
    rewrite ?asub_estart, ?asub_adenot, ?asub_elenZ, ?esub_den, ?asub_flat in H; exact H.
Qed.

Lemma know_ok_ksub_inv : forall E m sg kn, know_ok segs (senv E sg) m kn -> know_ok segs E m (map (ksub sg) kn).
Proof.
  intros E m sg kn H. unfold know_ok in *. apply Forall_forall. intros K HK. apply in_map_iff in HK as (K0 & <- & HK0).
  apply ksub_ok_inv. exact (proj1 (Forall_forall _ _) H K0 HK0).
Qed.

Lemma gholds_sub_inv : forall E m sg l, SG.gholds GP (senv E sg) m l -> SG.gholds GP E m (map (gsub sg) l).
Proof.
  intros E m sg l H. unfold SG.gholds in *. apply Forall_forall. intros g Hg. apply in_map_iff in Hg as (g0 & <- & Hg0).
  pose proof (proj1 (Forall_forall _ _) H g0 Hg0) as X. cbn [gsub g_id g_args].
  rewrite map_map. erewrite map_ext; [exact X|]. intros e. symmetry. apply esub_den.
Qed.

Lemma esub_closed : forall n sg e, forallb (expr_vars_lt n) sg = true -> expr_vars_lt n (esub sg e) = true.
Proof.
  intros n sg e Hc. induction e; cbn [esub expr_vars_lt]; try reflexivity;
    try (rewrite IHe1, IHe2; reflexivity); try exact IHe.
  destruct (Nat.lt_ge_cases n0 (length sg)) as [Hl|Hl].
  - exact (proj1 (forallb_forall _ _) Hc _ (nth_In _ _ Hl)).
  - rewrite nth_overflow by exact Hl. reflexivity.
Qed.

Lemma find_csr_in : forall pc ra l S, find_csr pc ra l = Some S -> In S l /\ t_pc (sm_pre S) = pc.
Proof.
  intros pc ra l. induction l as [|S0 r IH]; intros S H; [discriminate|]. cbn [find_csr] in H.
  destruct (Z.eqb (t_pc (sm_pre S0)) pc) eqn:E.
  - destruct (pr_match S0 ra); [injection H as <-; split; [left; reflexivity | apply Z.eqb_eq; exact E]|].
    destruct (IH S H) as [A B]. split; [right; exact A | exact B].
  - destruct (IH S H) as [A B]. split; [right; exact A | exact B].
Qed.

Lemma find_cs_in : forall pc l S, find_cs pc l = Some S -> In S l /\ t_pc (sm_pre S) = pc.
Proof.
  intros pc l. induction l as [|S0 r IH]; intros S H; [discriminate|]. cbn [find_cs] in H.
  destruct (Z.eqb (t_pc (sm_pre S0)) pc) eqn:E; [injection H as <-; split; [left; reflexivity | apply Z.eqb_eq; exact E]|].
  destruct (IH S H) as [A B]. split; [right; exact A | exact B].
Qed.

(* [comment removed for export] *)
Lemma decreases_sound : forall E M kn T T' sg hs,
  know_ok segs E M kn -> decreases kn T T' sg hs = true ->
  (Z.to_nat (bv_unsigned (edenot E (esub sg (t_meas T')))) < Z.to_nat (bv_unsigned (edenot E (t_meas T)))
   \/ (Z.to_nat (bv_unsigned (edenot E (esub sg (t_meas T')))) = Z.to_nat (bv_unsigned (edenot E (t_meas T)))
       /\ t_rank T' < t_rank T))%nat.
Proof.
  intros E M1 kn T T' sg hs HK' Hdec.
  pose proof (bv_unsigned_in_range 64 (edenot E (esub sg (t_meas T')))) as RR.
  pose proof (bv_unsigned_in_range 64 (edenot E (t_meas T))) as RR'.
  assert (STRICT : (bv_unsigned (edenot E (esub sg (t_meas T'))) < bv_unsigned (edenot E (t_meas T)))%Z ->
            (Z.to_nat (bv_unsigned (edenot E (esub sg (t_meas T')))) < Z.to_nat (bv_unsigned (edenot E (t_meas T))))%nat)
    by (intros; apply Z2Nat.inj_lt; lia).
  assert (WEAK : (bv_unsigned (edenot E (esub sg (t_meas T'))) <= bv_unsigned (edenot E (t_meas T)))%Z -> (t_rank T' < t_rank T)%nat ->
            ((Z.to_nat (bv_unsigned (edenot E (esub sg (t_meas T')))) < Z.to_nat (bv_unsigned (edenot E (t_meas T))))%nat
             \/ (Z.to_nat (bv_unsigned (edenot E (esub sg (t_meas T')))) = Z.to_nat (bv_unsigned (edenot E (t_meas T)))
                 /\ (t_rank T' < t_rank T)%nat))).
  { intros W Hrk. destruct (Z.eq_dec (bv_unsigned (edenot E (esub sg (t_meas T')))) (bv_unsigned (edenot E (t_meas T)))) as [Heq|Hne].
    - right. split; [rewrite Heq; reflexivity | exact Hrk].
    - left. apply Z2Nat.inj_lt; lia. }
  unfold decreases in Hdec.
  destruct (decide_branch kn BC_LTU (esub sg (t_meas T')) (t_meas T)) as [[|]|] eqn:D1;
    [ pose proof (decide_branch_sound segs E M1 kn BC_LTU _ _ true HK' D1) as B; cbn [branch_taken] in B;
      unfold bv_ltu in B; apply Z.ltb_lt in B; left; exact (STRICT B) | | ];
    (apply orb_prop in Hdec as [Hdec|Hdec];
     [ left; apply STRICT; pose proof (udiff_ok E M1 kn _ _ 1 _ HK' Hdec); lia
     | apply andb_prop in Hdec as [Hrk Hge]; apply Nat.ltb_lt in Hrk; refine (WEAK _ Hrk);
       destruct (decide_branch kn BC_GEU (t_meas T) (esub sg (t_meas T'))) as [[|]|] eqn:D2;
       [ pose proof (decide_branch_sound segs E M1 kn BC_GEU _ _ true HK' D2) as B; cbn [branch_taken] in B;
         unfold bv_ltu in B; apply negb_true_iff, Z.ltb_ge in B; exact B
       | cbn in Hge; pose proof (udiff_ok E M1 kn _ _ 0 _ HK' Hge); lia
       | cbn in Hge; pose proof (udiff_ok E M1 kn _ _ 0 _ HK' Hge); lia ] ]).
Qed.

Lemma win_sub_den : forall E sg w, SG.win_den E (SC.sub_win sg w) = win_den (senv E sg) w.
Proof. intros E sg [[b off] n]. cbn [SC.sub_win SG.win_den win_den]. rewrite !esub_den. reflexivity. Qed.

(* [comment removed for export] *)
Lemma awin_den_sub : forall E sg w, awin_den (senv E sg) w = awin_den E (SC.sub_win sg w).
Proof. intros E sg [[b off] n]. cbn [awin_den SC.sub_win]. rewrite !esub_den. reflexivity. Qed.

Lemma awin_den_gagree : forall G E E' w, gagree G E E' -> eb E = eb E' -> win_closed G w = true -> awin_den E w = awin_den E' w.
Proof.
  intros G E E' [[b off] n] Hg Hb Hc. cbn [win_closed] in Hc. apply andb_prop in Hc as [Hcb Hcn].
  cbn [awin_den]. rewrite (edenot_gagree G E E' b Hg Hb Hcb), (edenot_gagree G E E' n Hg Hb Hcn). reflexivity.
Qed.

Lemma aw_closed_win : forall G W w, aw_closed G (Some W) = true -> In w W -> win_closed G w = true.
Proof. intros G W [[b off] n] H Hw. exact (proj1 (forallb_forall _ _) H _ Hw). Qed.

Lemma fp_of_gagree : forall G E E' A, gagree G E E' -> eb E = eb E' -> aw_closed G A = true ->
  forall b j, fp_of A E' b j -> fp_of A E b j.
Proof.
  intros G E E' [W|] Hg Hb Hc b j H; [|exact I]. destruct H as (w & Hw & H). exists w. split; [exact Hw|].
  rewrite (awin_den_gagree G E E' w Hg Hb (aw_closed_win G W w Hc Hw)). exact H.
Qed.

Lemma aw_genuine_gagree : forall G E E' A, gagree G E E' -> eb E = eb E' -> aw_closed G A = true ->
  aw_genuine E A -> aw_genuine E' A.
Proof.
  intros G E E' [W|] Hg Hb Hc H; [|exact I]. intros w Hw. rewrite <- (awin_den_gagree G E E' w Hg Hb (aw_closed_win G W w Hc Hw)).
  exact (H w Hw).
Qed.

(* [comment removed for export] *)
Lemma acc_cont_ok : forall A Ac sg kn E M, acc_cont A Ac sg kn = true -> know_ok segs E M kn -> aw_genuine E A ->
  aw_genuine (senv E sg) Ac /\ (forall b j, fp_of Ac (senv E sg) b j -> fp_of A E b j).
Proof.
  intros [WA|] [WcA|] sg kn E M H HK HG; try discriminate H.
  - cbn [acc_cont] in H.
    assert (IN : forall wc, In wc WcA -> exists w', In w' WA /\ (fst (awin_den E w') <= fst (awin_den (senv E sg) wc)
                   /\ snd (awin_den (senv E sg) wc) <= snd (awin_den E w'))%Z).
    { intros wc Hwc. pose proof (proj1 (forallb_forall _ _) H wc Hwc) as X. rewrite awin_den_sub.
      cbv beta in X. destruct (SC.sub_win sg wc) as [[b off] n]. cbv beta iota in X.
      apply existsb_exists in X as ([[b' off'] n'] & Hw' & Hx). cbv beta iota in Hx.
      destruct (SLin.xinside2_sound segs E M kn b off n b' off' n' HK Hx) as [P1 P2].
      exists (b', off', n'). split; [exact Hw'|]. cbn [awin_den fst snd]. unfold estart, elenZ in P1, P2. cbn [a_base a_off] in P1, P2. lia. }
    split.
    + intros wc Hwc. destruct (IN wc Hwc) as (w' & Hw' & L & U). pose proof (HG w' Hw') as G'.
      pose proof (bv_unsigned_in_range 64 (edenot (senv E sg) (match wc with (b, _, _) => b end))) as R1.
      destruct wc as [[b off] n]. cbn [awin_den fst snd] in L, U |- *.
      pose proof (bv_unsigned_in_range 64 (edenot (senv E sg) n)) as R2. unfold bv_modulus in R2. cbn in R2. lia.
    + intros b j (wc & Hwc & L). destruct (IN wc Hwc) as (w' & Hw' & L' & U'). exists w'. split; [exact Hw'|]. lia.
  - split; [exact I | intros; exact I].
Qed.

(* [comment removed for export] *)
Definition win_inside_b (w w' : win) : bool :=
  match w, w' with
  | (b, off, n), (b', off', n') =>
      if expr_eqb b b' then
        match n, n' with
        | ELit nz, ELit nz' => if Z.leb off' off then if Z.leb 0 nz then if Z.ltb nz' (2 ^ 64) then Z.leb (off + nz) (off' + nz')
                               else false else false else false
        | _, _ => if Z.eqb off off' then expr_eqb n n' else false
        end
      else false
  end.
Definition cr_inside_b (P : prog) : bool :=
  forallb (fun w => existsb (fun w' => win_inside_b w w') (p_W P)) (p_CR P).

Lemma win_inside_b_ok : forall E w w' z, win_inside_b w w' = true ->
  fst (win_den E w) <= z < snd (win_den E w) -> fst (win_den E w') <= z < snd (win_den E w').
Proof.
  intros E [[b off] n] [[b' off'] n'] z H Hz. cbn [win_inside_b] in H.
  destruct (expr_eqb b b') eqn:Hb; [|discriminate]. apply expr_eqb_eq in Hb. subst b'. cbn [win_den fst snd] in *.
  assert (GEN : (if Z.eqb off off' then expr_eqb n n' else false) = true -> off + bv_unsigned (edenot E n) = off' + bv_unsigned (edenot E n')
                 /\ off = off').
  { intros H1. destruct (Z.eqb off off') eqn:Ho; [|discriminate]. apply Z.eqb_eq in Ho. apply expr_eqb_eq in H1. subst. split; reflexivity. }
  destruct n as [nz| | | | | | |]; destruct n' as [nz'| | | | | | |];
    try (destruct (GEN H) as [G1 G2]; lia).
  destruct (Z.leb off' off) eqn:H1; [|discriminate]. destruct (Z.leb 0 nz) eqn:H2; [|discriminate].
  destruct (Z.ltb nz' (2 ^ 64)) eqn:H3; [|discriminate]. apply Z.leb_le in H1, H2, H. apply Z.ltb_lt in H3.
  rewrite !edenot_lit, !Z_to_bv_unsigned in *. unfold bv_wrap, bv_modulus in *. change (2 ^ Z.of_N 64) with (2 ^ 64) in *.
  pose proof (Z.mod_le nz (2 ^ 64) H2 ltac:(lia)).
  assert (0 <= nz') by lia. rewrite (Z.mod_small nz') by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Variable hmF : ExecF.footprint.
Definition fpu (A : option (list awin)) (E : env) : ExecF.footprint := ExecF.fp_union (fp_of A E) hmF.

Lemma fpu_of : forall A E ms ms', ExecF.mstepsF segs (fp_of A E) ms ms' -> ExecF.mstepsF segs (fpu A E) ms ms'.
Proof. intros A E ms ms' H. exact (ExecF.mstepsF_weaken segs _ _ _ _ (fun b j Hb => or_introl Hb) H). Qed.
Lemma fpu_mono : forall A E A' E', (forall b j, fp_of A' E' b j -> fp_of A E b j) -> forall b j, fpu A' E' b j -> fpu A E b j.
Proof. intros A E A' E' H b j [Hb|Hb]; [left; exact (H b j Hb) | right; exact Hb]. Qed.
Lemma fpu_gagree : forall G E E' A, gagree G E E' -> eb E = eb E' -> aw_closed G A = true ->
  forall b j, fpu A E' b j -> fpu A E b j.
Proof. intros G E E' A Hg Hb Hc. apply fpu_mono. exact (fp_of_gagree G E E' A Hg Hb Hc). Qed.

(* [comment removed for export] *)
Definition ext_okHF (P : prog) (Cnd : env -> Prop) (TA : tmpl) : Prop :=
  forall E M rom ms, hmR rom -> aw_genuine E (p_A P) -> Cnd E -> hmH M -> tm_okF segs TA E M rom ms -> SG.gholds GP E M (t_ghost TA) ->
  exists ms', ExecF.mstepsF segs (fpu (p_A P) E) ms ms' /\
    ((exists TB E' M', In TB (p_tm P ++ p_xt P) /\ tm_okF segs TB E' M' rom ms' /\ SG.gholds GP E' M' (t_ghost TB)
        /\ gagree (p_G P) E E' /\ eb E' = eb E /\ hmH M' /\ frame_ok E (p_W P) (p_PS P) M M'
        /\ (mval TB E' < mval TA E \/ (mval TB E' = mval TA E /\ t_rank TB < t_rank TA))%nat)
     \/ prun_postH P E M rom ms').

(* [comment removed for export] *)
Definition summ_okHF (S : summ) : Prop :=
  forall E M rom ms, hmR rom -> aw_genuine E (sm_A S) -> wins_client E (sm_W S) -> hmH M -> tm_okF segs (sm_pre S) E M rom ms ->
    SG.gholds GP E M (t_ghost (sm_pre S)) ->
  exists ms' X E' M', ExecF.mstepsF segs (fpu (sm_A S) E) ms ms' /\ In X (sm_post S) /\ tm_okF segs X E' M' rom ms' /\ SG.gholds GP E' M' (t_ghost X)
    /\ gagree (sm_G S) E E' /\ eb E' = eb E /\ hmH M' /\ frame_ok E (sm_W S) (sm_PS S) M M'.

(* [comment removed for export] *)
Variable hmS : Z -> Z -> Prop.
Hypothesis HMS_mono : forall s n s' n', hmS s n -> s - n <= s' - n' -> s' <= s -> hmS s' n'.
Definition hs_ok (E : env) (PS : option expr) (W : list win) : Prop :=
  match dstk PS W with None => True | Some (spe, n) => hmS (bv_unsigned (edenot E spe)) n end.

(* [comment removed for export] *)
Definition summ_okHS (S : summ) : Prop :=
  forall E M rom ms, hmR rom -> aw_genuine E (sm_A S) -> wins_client E (sm_W S) -> hs_ok E (sm_PS S) (sm_W S) -> hmH M ->
    tm_okF segs (sm_pre S) E M rom ms -> SG.gholds GP E M (t_ghost (sm_pre S)) ->
  exists ms' X E' M', ExecF.mstepsF segs (fpu (sm_A S) E) ms ms' /\ In X (sm_post S) /\ tm_okF segs X E' M' rom ms' /\ SG.gholds GP E' M' (t_ghost X)
    /\ gagree (sm_G S) E E' /\ eb E' = eb E /\ hmH M' /\ frame_ok E (sm_W S) (sm_PS S) M M'.

(* [comment removed for export] *)
Definition crs_law (E : env) (CR : list win) : Prop :=
  forall w, In w CR -> forall z, fst (win_den E w) <= z < snd (win_den E w) -> hmA z.
Definition summ_okHSC (S : summ) : Prop :=
  forall E M rom ms, hmR rom -> aw_genuine E (sm_A S) -> wins_client E (sm_W S) -> hs_ok E (sm_PS S) (sm_W S) ->
    crs_law E (sm_CR S) -> hmH M -> tm_okF segs (sm_pre S) E M rom ms -> SG.gholds GP E M (t_ghost (sm_pre S)) ->
  exists ms' X E' M', ExecF.mstepsF segs (fpu (sm_A S) E) ms ms' /\ In X (sm_post S) /\ tm_okF segs X E' M' rom ms' /\ SG.gholds GP E' M' (t_ghost X)
    /\ gagree (sm_G S) E E' /\ eb E' = eb E /\ hmH M' /\ frame_ok E (sm_W S) (sm_PS S) M M'.
Lemma summ_okHS_C : forall S, summ_okHS S -> summ_okHSC S.
Proof. intros S H E M rom ms H1 H2 H3 H4 _ H6 H7 H8. exact (H E M rom ms H1 H2 H3 H4 H6 H7 H8). Qed.

Lemma dstk_l_bound : forall spe W n, dstk_l spe W = Some n -> 0 <= n < 2^47.
Proof.
  intros spe W. induction W as [|[[b off] e] r IH]; intros n H; [discriminate|]. cbn [dstk_l] in H.
  destruct e; try exact (IH n H).
  destruct (expr_eqb b spe && Z.eqb off (- z) && Z.leb 0 z && Z.ltb z (2^47))%bool eqn:C; [|exact (IH n H)].
  injection H as <-. apply andb_prop in C as [C C4]. apply andb_prop in C as [_ C3]. apply Z.leb_le in C3. apply Z.ltb_lt in C4. lia.
Qed.
Lemma dstk_bound : forall PS W spe n, dstk PS W = Some (spe, n) -> 0 <= n < 2^47 /\ PS = Some spe.
Proof.
  intros [e|] W spe n H; [|discriminate]. cbn [dstk] in H. destruct (dstk_l e W) as [n0|] eqn:D; [|discriminate].
  injection H as <- <-. split; [exact (dstk_l_bound _ _ _ D) | reflexivity].
Qed.
Lemma hs_ok_gagree : forall G E E2 PS W, gagree G E E2 -> eb E = eb E2 -> ps_closed G PS = true -> hs_ok E PS W -> hs_ok E2 PS W.
Proof.
  intros G E E2 PS W Hg Hb Hc H. unfold hs_ok in *. destruct (dstk PS W) as [[spe n]|] eqn:D; [|exact I].
  destruct (dstk_bound PS W spe n D) as [_ ->]. cbn [ps_closed] in Hc.
  rewrite <- (edenot_gagree G E E2 spe Hg Hb Hc). exact H.
Qed.

(* [comment removed for export] *)
Lemma call_edge_soundHSC : forall P IT T x xh S E' M rom ms' (Cnd : env -> Prop),
  itab_sound segs IT -> summ_okHSC S ->
  call_edge_ok segs gfp gvc P IT T x xh S = true ->
  forallb tm_closed (sm_post S) = true ->
  (p_G P <= t_ns T)%nat -> tm_closed T = true ->
  SG.gholds GP E' M (t_ghost T) ->
  SFP.st_okXF segs E' M rom (x_ss x) ms' -> PIosRegs.rfull (ms_regs ms') -> aw_genuine E' (p_A P) ->
  path_okX segs M E' (s_next (x_ss x)) (x_path x) -> s_resv (x_ss x) = None ->
  forallb (win_closed (p_G P)) (p_CR P) = true ->
  Cnd E' -> (forall E E2, gagree (p_G P) E E2 -> eb E = eb E2 -> Cnd E -> Cnd E2) ->
  (forall E, Cnd E -> wins_client E (p_W P)) ->
  (forall E, Cnd E -> forall w, In w (p_CR P) -> forall z, fst (win_den E w) <= z < snd (win_den E w) -> hmA z) ->
  (forall E M0, Cnd E -> hmH M0 -> know_ok segs E M0 (p_IK P)) ->
  (forall E, Cnd E -> hs_ok E (p_PS P) (p_W P)) ->
  hmH (ms_mem ms') -> hmR rom ->
  exists ms3 T' E3 M3, ExecF.mstepsF segs (fpu (p_A P) E') ms' ms3 /\ tm_okF segs T' E3 M3 rom ms3 /\ SG.gholds GP E3 M3 (t_ghost T')
    /\ gagree (p_G P) E' E3 /\ eb E3 = eb E'
    /\ hmH M3 /\ frame_ok E' (p_W P) (p_PS P) M M3
    /\ ((In T' (p_tm P ++ p_xt P) /\ (mval T' E3 < mval T E' \/ (mval T' E3 = mval T E' /\ t_rank T' < t_rank T))%nat)
        \/ In T' (p_ex P)).
Proof.
  intros P IT T x xh S E' M rom ms' Cnd HIT HS Hce Hpc HGT Hc HGE HXF HRF HAG HP Hres HCRc HCnd HCG HCW HCR HIK HSTK HH1 HRom.
  unfold call_edge_ok in Hce. set (ss := x_ss x) in *.
  destruct (exit_kn ss) as [kn'|] eqn:Hkn; [|discriminate].
  set (sg := mk_sg 0 (sm_pre S) (s_regs ss) kn' (xh_sg xh)) in *.
  set (Wc := map (SC.sub_win sg) (sm_W S)) in *.
  apply andb_prop in Hce as [Hce Hposts]. apply andb_prop in Hce as [Hce Hcrs]. apply andb_prop in Hce as [Hce Hstk].
  apply andb_prop in Hce as [Hce Hps]. apply andb_prop in Hce as [Hce Hacc].
  apply andb_prop in Hce as [Hce HWin].
  apply andb_prop in Hce as [Hce Hent].
  apply andb_prop in Hce as [Hce Hns]. apply andb_prop in Hce as [Hce Hcl]. apply andb_prop in Hce as [Hwin Hlen].
  apply Nat.eqb_eq in Hlen. apply Nat.leb_le in Hns.
  set (n0 := s_next ss) in *.
  destruct HXF as [HZ HX'].
  pose proof (st_okR_ok segs E' M rom ss ms' (st_okX_R segs E' M rom ss ms' HX') Hres) as (R & Hms' & HR & Hlf & HK).
  pose proof (exit_kn_ok segs E' M ss kn' Hkn Hlf HK) as HK'.
  set (M1 := mem_denot E' M (s_log ss)) in *.
  pose proof (HP E' (eagree_refl _ _)) as HPE.
  unfold tm_closed in Hc.
  apply andb_prop in Hc as [Hc HgvT]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _].
  apply andb_prop in Hc as [Hc HmT]. apply andb_prop in Hc as [_ _].
  (* [comment removed for export] *)
  destruct (@entailsG_sound (SFP.fx_of ms') T (sm_pre S) x kn' sg _ E' M rom R Hent HK HPE Hlf HGE HK' HR) as [HTf HGf].
  fold ss M1 in HTf, HGf. rewrite <- Hms' in HTf.
  assert (HTfF : tm_okF segs (sm_pre S) (senv E' sg) M1 rom ms') by (split; [exact HZ | split; [exact HRF | exact HTf]]).
  (* [comment removed for export] *)
  destruct (acc_cont_ok (p_A P) (sm_A S) sg kn' E' M1 Hacc HK' HAG) as [HAGc FPc0].
  pose proof (fpu_mono (p_A P) E' (sm_A S) (senv E' sg) FPc0) as FPc.
  assert (HH1' : hmH M1) by (rewrite Hms' in HH1; exact HH1).
  (* [comment removed for export] *)
  assert (WINc : forall wc, In wc Wc -> exists w', In w' (p_W P) /\ fst (win_den E' w') <= fst (SG.win_den E' wc)
                                                   /\ snd (SG.win_den E' wc) <= snd (win_den E' w')).
  { intros wc Hwc. pose proof (proj1 (forallb_forall _ _) HWin wc Hwc) as HW1. destruct wc as [[b off] n]. cbv beta iota in HW1.
    apply existsb_exists in HW1 as ([[b' off'] n'] & Hw' & Hx). cbv beta iota in Hx.
    destruct (SLin.xinside2_sound segs E' M1 kn' b off n b' off' n' HK' Hx) as [A B].
    exists (b', off', n'). split; [exact Hw'|]. cbn [win_den SG.win_den fst snd]. unfold estart, elenZ in A, B. cbn [a_base a_off] in A, B. lia. }
  assert (HWCc : wins_client (senv E' sg) (sm_W S)).
  { unfold wins_client. apply Forall_forall. intros w0 Hw0.
    destruct (WINc (SC.sub_win sg w0) (in_map _ _ _ Hw0)) as (w' & Hw' & L & U). rewrite win_sub_den in L, U.
    pose proof (proj1 (Forall_forall _ _) (HCW E' HCnd) w' Hw') as C'. eapply HMC_sub; [exact C' | exact L | exact U]. }
  (* [comment removed for export] *)
  assert (HSc : hs_ok (senv E' sg) (sm_PS S) (sm_W S)).
  { unfold hs_ok. unfold stk_ok in Hstk. destruct (dstk (sm_PS S) (sm_W S)) as [[spc n']|] eqn:Dc; [|exact I].
    pose proof (HSTK E' HCnd) as HS0. unfold hs_ok in HS0.
    destruct (dstk (p_PS P) (p_W P)) as [[spe n]|] eqn:Dp; [|discriminate].
    destruct (dstk_bound _ _ _ _ Dc) as [Bc _]. destruct (dstk_bound _ _ _ _ Dp) as [Bp _].
    assert (Hin2 : estart E' (SA spe (- n)) <= estart E' (SA (esub sg spc) (- n')) /\
                   estart E' (SA (esub sg spc) (- n')) + elenZ E' (ELit n') <= estart E' (SA spe (- n)) + elenZ E' (ELit n)).
    { destruct (SLin.xinside2 kn' (esub sg spc) (- n') (ELit n') spe (- n) (ELit n)) eqn:X2.
      - exact (SLin.xinside2_sound segs E' M1 kn' (esub sg spc) (- n') (ELit n') spe (- n) (ELit n) HK' X2).
      - destruct (shares_var (esub sg spc) spe); [discriminate|].
        exact (SLin.xinside_f_sound segs E' M1 kn' (esub sg spc) (- n') (ELit n') spe (- n) (ELit n) HK' Hstk). }
    destruct Hin2 as [A B].
    unfold estart, elenZ in A, B. cbn [a_base a_off] in A, B.
    rewrite !edenot_lit, !Z_to_bv_unsigned, !bv_wrap_small in B by (unfold bv_modulus; cbn; lia).
    rewrite esub_den. apply (HMS_mono _ _ _ _ HS0); lia. }
  (* [comment removed for export] *)
  assert (HCRs : crs_law (senv E' sg) (sm_CR S)).
  { intros w Hw z Hz. unfold crs_ok in Hcrs. pose proof (proj1 (forallb_forall _ _) Hcrs w Hw) as Hx. cbv beta in Hx.
    rewrite <- win_sub_den in Hz. destruct (SC.sub_win sg w) as [[b k] n] eqn:Esw. cbv iota in Hx.
    apply SLin.lex_exists in Hx as ([[b' k'] n'] & Hw' & Hi). unfold crw_in in Hi.
    assert (Hin2 : estart E' (SA b' k') <= estart E' (SA b k) /\ estart E' (SA b k) + elenZ E' n <= estart E' (SA b' k') + elenZ E' n').
    { destruct (SLin.xinside2 kn' b k n b' k' n') eqn:X2.
      - exact (SLin.xinside2_sound segs E' M1 kn' b k n b' k' n' HK' X2).
      - destruct (shares_var b b'); [discriminate|]. exact (SLin.xinside_f_sound segs E' M1 kn' b k n b' k' n' HK' Hi). }
    apply (HCR E' HCnd (b', k', n') Hw' z). cbn [SG.win_den win_den fst snd] in Hz |- *.
    unfold estart, elenZ in Hin2. cbn [a_base a_off] in Hin2. lia. }
  destruct (HS _ _ _ _ HRom HAGc HWCc HSc HCRs HH1' HTfF HGf) as (ms2 & X & E2 & M2 & Hms2F & HinX & HTX & HGX & Hga & Hb2 & HH2 & FR2).
  pose proof (ExecF.mstepsF_msteps segs _ _ _ Hms2F) as Hms2.
  pose proof (proj1 (forallb_forall _ _) Hpc X HinX) as HcX.
  (* [comment removed for export] *)
  pose proof (proj1 (forallb_forall _ _) Hposts X HinX) as HpX. cbv beta in HpX.
  apply andb_prop in HpX as [HpX Hrt]. apply andb_prop in HpX as [Hret HGX'].
  apply Nat.leb_le in HGX'.
  destruct (ret_pc S sg X) as [rpc|] eqn:Hrpc; [|discriminate].
  destruct (pr_pc_ok S X rpc) eqn:Hprpc; [|discriminate].
  destruct (call_exit gfp P T x kn' S sg X rpc) as [xC src] eqn:HxC.
  (* [comment removed for export] *)
  destruct HTX as (HZ2 & HRF2 & HTX).
  destruct HTX as (R2 & Hms2' & HR2 & _ & HK2).
  cbn [tstate s_pc s_regs s_log s_know mem_denot] in Hms2', HR2, HK2.
  assert (Hrpc0 := Hrpc).
  unfold ret_pc in Hrpc.
  destruct (nth 1 (t_regs X) (ELit 0)) as [|jra| | | | | |] eqn:Hra; try discriminate Hrpc.
  destruct (Nat.ltb jra (sm_G S)) eqn:Hjra; [|discriminate]. apply Nat.ltb_lt in Hjra.
  destruct (nth jra sg (ELit 0)) as [rpc0| | | | | | |] eqn:Hsgj; try discriminate Hrpc.
  destruct (Z.leb 0 rpc0 && Z.ltb rpc0 (2^64) && Z.eqb (Z.land rpc0 (-2)) rpc0)%bool eqn:Hrv; [|discriminate].
  injection Hrpc as <-.
  apply andb_prop in Hrv as [Hrv Hev]. apply andb_prop in Hrv as [Hr0 Hr1].
  apply Z.leb_le in Hr0. apply Z.ltb_lt in Hr1. apply Z.eqb_eq in Hev.
  assert (HRA : getr R2 (Z_to_bv 5 1) = Z_to_bv 64 rpc0).
  { rewrite (HR2 (Z_to_bv 5 1)). change (sr_get (t_regs X) (Z_to_bv 5 1)) with (nth 1 (t_regs X) (ELit 0)). rewrite Hra.
    cbn [edenot]. rewrite <- (Hga jra Hjra), senv_nth, Hsgj. reflexivity. }
  set (ms3 := @mkst (SFP.fx_of ms2) R2 (Z_to_bv 64 rpc0) M2 rom).
  assert (Hm3 : ExecF.mstepsF segs (fpu (p_A P) E') ms' ms3).
  { unfold pr_pc_ok in Hprpc. unfold ret_ok' in Hret. destruct (sm_PR S) eqn:HPR.
    - (* [comment removed for export] *)
      apply Z.eqb_eq in Hprpc. assert (Hms23 : ms2 = ms3) by (unfold ms3; rewrite Hms2', Hprpc; reflexivity).
      rewrite <- Hms23. exact (ExecF.mstepsF_weaken segs _ _ _ _ FPc Hms2F).
    - unfold ret_ok in Hret. destruct (itab_lookup IT (t_pc X)) as [i|] eqn:Hl; [|discriminate].
      destruct i; try discriminate Hret.
      apply andb_prop in Hret as [Hret Himm]. apply andb_prop in Hret as [Hrd Hrs].
      apply Z.eqb_eq in Hrd, Hrs, Himm.
      assert (Erd : rd = Z_to_bv 5 0) by (apply bv_eq; rewrite Hrd; reflexivity).
      assert (Ers : rs1 = Z_to_bv 5 1) by (apply bv_eq; rewrite Hrs; reflexivity).
      subst rd rs1.
      destruct (itab_facts segs IT (t_pc X) _ HIT Hl) as (w1 & Hf & He & Hd).
      assert (STEP : RiscvSemantics.step segs ms2 = MachineOk ms3).
      { rewrite Hms2'. rewrite <- mkstR_None.
        rewrite (stepR_jalr segs R2 (Z_to_bv 64 (t_pc X)) M2 rom None w1 (Z_to_bv 5 0) (Z_to_bv 5 1) imm Hf He Hd).
        rewrite mkstR_None. unfold ms3. f_equal. f_equal. rewrite HRA, Himm. unfold v_jalr, jalr_tgtZ.
        rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia). rewrite Z.add_0_r, Hev. reflexivity. }
      eapply ExecF.mstepsF_trans; [exact (ExecF.mstepsF_weaken segs _ _ _ _ FPc Hms2F)|]. apply ExecF.mstepsF_one.
      apply (stepF_nonmem0 segs _ ms2 ms3 (Jalr (Z_to_bv 5 0) (Z_to_bv 5 1) imm) w1); [rewrite Hms2'; exact Hf | exact He | exact Hd | reflexivity | reflexivity | rewrite Hms2'; reflexivity | exact STEP]. }
  (* [comment removed for export] *)
  unfold call_exit in HxC. fold ss n0 in HxC. injection HxC as HxC Hsrc.
  set (sg' := SC.post_sg (sm_G S) sg n0 (t_ns X)) in *.
  set (EC := SC.ecomb E' E2 n0).
  pose proof (SC.ecomb_agree E' E2 n0) as AGE. fold EC in AGE.
  assert (HGsg : forall j, (j < sm_G S)%nat -> ev E2 j = edenot E' (nth j sg (ELit 0))).
  { intros j Hj. rewrite <- (Hga j Hj). apply senv_nth. }
  assert (Hb2' : eb E2 = eb E') by exact Hb2.
  pose proof (SC.post_sg_agree E' E2 (sm_G S) sg n0 (t_ns X) HGsg Hb2' Hcl) as AG. fold sg' EC in AG.
  assert (AGX : env_agree (t_ns X) E2 (senv EC sg')).
  { split; [intros j Hj; symmetry; exact (AG j Hj) | cbn [senv eb EC SC.ecomb]; exact Hb2']. }
  unfold tm_closed in HcX.
  apply andb_prop in HcX as [HcX HgvX]. apply andb_prop in HcX as [HcX _]. apply andb_prop in HcX as [HcX _].
  apply andb_prop in HcX as [HcX _]. apply andb_prop in HcX as [HsrX HknX].
  (* [comment removed for export] *)
  assert (HRC : regs_ok EC (map (esub sg') (t_regs X)) R2).
  { pose proof (regs_ok_agree (t_ns X) E2 (senv EC sg') (t_regs X) R2 AGX HsrX HR2) as HR2'.
    intros r. rewrite (HR2' r), sr_get_map. apply esub_den. }
  (* [comment removed for export] *)
  assert (HW12 : mem_grows M1 M2).
  { pose proof (PIosRegs.msteps_wrel segs _ _ Hms2) as W.
    assert (E1m : ms_mem ms' = M1) by (rewrite Hms'; reflexivity).
    assert (E2m : ms_mem ms2 = M2) by (rewrite Hms2'; reflexivity).
    rewrite E1m, E2m in W. exact (SC.wrel_grows segs _ _ W). }
  (* [comment removed for export] *)
  assert (OUTW : forall y : word, (forall wc, In wc Wc -> ~ SC.in_win E' wc (bv_unsigned y)) -> outside_wins (senv E' sg) (sm_W S) (bv_unsigned y)).
  { intros y Hy. unfold outside_wins. apply Forall_forall. intros w0 Hw0.
    pose proof (Hy (SC.sub_win sg w0) (in_map _ _ _ Hw0)) as Hyw. unfold SC.in_win in Hyw. rewrite win_sub_den in Hyw.
    destruct (win_den (senv E' sg) w0). exact Hyw. }
  assert (OUTP : forall y : word, (forall wc, In wc Wc -> ~ SC.in_win E' wc (bv_unsigned y)) -> SC.in_PR E' (pres_rs P S sg) (bv_unsigned y) -> M2 y = M1 y).
  { intros y Hy HyP. unfold pres_rs in HyP. unfold frame_ok in FR2. unfold ps_ok in Hps.
    destruct (sm_PS S) as [spc|]; [|exact (FR2 y (OUTW y Hy))].
    apply (FR2 y (OUTW y Hy)). destruct HyP as (w1 & Hw1 & Hin). destruct Hw1 as [<-|[<-|Hw1]].
    - left. unfold SC.in_win, stack_win, SG.win_den in Hin. rewrite <- esub_den in Hin.
      destruct (p_PS P) as [spe|]; [|discriminate].
      destruct (SL.dtrue (decide_branch kn' BC_GEU spe (esub sg spc))) eqn:D1; [|discriminate].
      pose proof (SL.dtrue_sound segs E' M1 kn' _ _ _ HK' Hps) as B. cbn [branch_taken] in B. unfold bv_ltu in B. apply Z.ltb_lt in B.
      rewrite edenot_lit, Z_to_bv_unsigned, bv_wrap_small in B by (unfold bv_modulus; cbn; lia). rewrite <- esub_den in B.
      cbn [edenot] in Hin. rewrite alu_sub in Hin. unfold v_sub in Hin. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod in Hin.
      rewrite (Z.mod_small (2^47) (2^64)) in Hin by lia. repeat rewrite <- esub_den in Hin.
      rewrite Z.mod_small in Hin by (pose proof (bv_unsigned_in_range 64 (edenot (senv E' sg) spc)) as Rg; unfold bv_modulus in Rg; cbn in Rg; lia).
      lia.
    - (* [comment removed for export] *)
      right; left. destruct (p_PS P) as [spe|]; [|discriminate].
      destruct (SL.dtrue (decide_branch kn' BC_GEU spe (esub sg spc))) eqn:D1; [|discriminate].
      pose proof (SL.dtrue_sound segs E' M1 kn' _ _ _ HK' Hps) as B. cbn [branch_taken] in B. unfold bv_ltu in B. apply Z.ltb_lt in B.
      rewrite edenot_lit, Z_to_bv_unsigned, bv_wrap_small in B by (unfold bv_modulus; cbn; lia).
      rewrite esub_den. apply shwin_sh_above; [lia | exact Hin].
    - right; right. apply (HCR E' HCnd w1 Hw1). unfold SC.in_win in Hin. destruct w1 as [[b k] n]. cbn [SG.win_den win_den fst snd] in Hin |- *. exact Hin. }

  assert (WIN_EC : forall wc, In wc Wc -> forall z, SC.in_win EC wc z <-> SC.in_win E' wc z).
  { intros wc Hwc z. apply in_map_iff in Hwc as (w0 & <- & Hw0). destruct w0 as [[b off] n].
    unfold SC.in_win. cbn [SC.sub_win SG.win_den].
    assert (Eb : edenot EC (esub sg b) = edenot E' (esub sg b))
      by (symmetry; apply (edenot_agree n0 E' EC); [apply eagree_env_agree; exact AGE | apply esub_closed; exact Hcl]).
    assert (En : edenot EC (esub sg n) = edenot E' (esub sg n))
      by (symmetry; apply (edenot_agree n0 E' EC); [apply eagree_env_agree; exact AGE | apply esub_closed; exact Hcl]).
    rewrite Eb, En. tauto. }
  assert (PR_EC : forall z, SC.in_PR EC (pres_rs P S sg) z <-> SC.in_PR E' (pres_rs P S sg) z).
  { assert (Hwin_cl : forall w, (match pres_rs P S sg with None => False | Some l => In w l end) -> forall z, SC.in_win EC w z <-> SC.in_win E' w z).
    { intros [[b k] n] Hw z. unfold pres_rs in Hw. destruct (sm_PS S) as [spc|]; [|contradiction].
      assert (Hcb : expr_vars_lt n0 b = true /\ expr_vars_lt n0 n = true).
      { destruct Hw as [Hw|[Hw|Hw]].
        - unfold stack_win in Hw. injection Hw as <- <- <-. split; [apply esub_closed; exact Hcl|].
          cbn [expr_vars_lt]. rewrite esub_closed by exact Hcl. reflexivity.
        - unfold stack_shwin in Hw. injection Hw as <- <- <-. cbn [expr_vars_lt]. rewrite esub_closed by exact Hcl. split; reflexivity.
        - pose proof (proj1 (forallb_forall _ _) HCRc _ Hw) as Hc'. cbn [win_closed] in Hc'. apply andb_prop in Hc' as [Hc1 Hc2].
          split; (apply (SC.expr_vars_lt_mono (p_G P)); [assumption | lia]). }
      destruct Hcb as [Hcb Hcn]. unfold SC.in_win. cbn [SG.win_den].
      assert (Eb : edenot EC b = edenot E' b) by (symmetry; apply (edenot_agree n0 E' EC); [apply eagree_env_agree; exact AGE | exact Hcb]).
      assert (En : edenot EC n = edenot E' n) by (symmetry; apply (edenot_agree n0 E' EC); [apply eagree_env_agree; exact AGE | exact Hcn]).
      rewrite Eb, En. tauto. }
    intros z. unfold SC.in_PR. destruct (pres_rs P S sg) as [l|] eqn:HPR; [|tauto].
    split; intros (w1 & Hw1 & Hin); exists w1; (split; [exact Hw1|]); apply (Hwin_cl w1 Hw1 z); exact Hin. }
  (* [comment removed for export] *)
  assert (HK'C : know_ok segs EC M1 kn').
  { destruct (st_okR_parts segs EC M rom ss ms' (HX' EC AGE)) as (_ & HmC & HlfC & HKC & _).
    pose proof (exit_kn_ok segs EC M ss kn' Hkn HlfC HKC) as X1.
    assert (HmE : ms_mem ms' = M1) by (rewrite Hms'; reflexivity).
    rewrite <- HmC, HmE in X1. exact X1. }
  assert (HgEC0 : gagree (p_G P) E' EC) by (eapply eagree_gagree; [|exact AGE]; lia).
  assert (HKC : know_ok segs EC M2 (map (ksub sg') (t_know X) ++ List.filter (SC.survivesP kn' Wc (pres_rs P S sg)) kn' ++ ik_of P S)).
  { apply Forall_app. split.
    - apply know_ok_ksub_inv. exact (know_ok_agree segs (t_ns X) E2 (senv EC sg') M2 (t_know X) AGX HknX HK2).
    - apply Forall_app. split.
      + apply (SC.survivesP_all_ok segs EC M1 M2 kn' Wc (pres_rs P S sg) HK'C HW12).
        intros y Hy HyP. apply OUTP; [intros wc Hwc; rewrite <- (WIN_EC wc Hwc); exact (Hy wc Hwc) | apply PR_EC; exact HyP].
      + unfold ik_of. destruct (sm_PS S); [|constructor].
        apply HIK; [|exact HH2]. apply (HCG E' EC HgEC0 eq_refl HCnd). }
  (* [comment removed for export] *)
  assert (HPC : scs_denot segs M2 EC (List.filter SC.is_brb (x_path x))).
  { apply (SC.br_filter_ok segs M M2 EC). exact (HP EC AGE). }
  (* [comment removed for export] *)
  assert (HGC : SG.gholds GP EC M2 src).
  { rewrite <- Hsrc. apply SG.gholds_app.
    - unfold SG.gholds. apply Forall_forall. intros g Hg. apply filter_In in Hg as [HgT Hg]. apply andb_prop in Hg as [Hkeep Hap].
      pose proof (SG.keep_ok_sound segs GP gfp E' M (s_know ss) (s_log ss) (t_ghost T) g HGF HK Hlf HGE Hkeep) as G1. fold M1 in G1.
      assert (G2 : GP (g_id g) (map (edenot E') (g_args g)) M2).
      { apply (HGF (g_id g) (g_args g) E' M1 M2); [|exact G1].
        intros y Hy. destruct (SC.apart_allP_ok segs E' M1 kn' _ Wc (pres_rs P S sg) HK' Hap (bv_unsigned y) Hy) as [Ha1 Ha2]. exact (OUTP y Ha1 Ha2). }
      assert (Eargs : map (edenot E') (g_args g) = map (edenot EC) (g_args g)).
      { apply map_ext_in. intros e0 He0. apply (edenot_agree n0 E' EC); [apply eagree_env_agree; exact AGE|].
        unfold gvars_lt in HgvT. pose proof (proj1 (forallb_forall _ _) HgvT g HgT) as Hg1.
        pose proof (proj1 (forallb_forall _ _) Hg1 e0 He0) as He1. apply (SC.expr_vars_lt_mono (t_ns T)); [exact He1 | lia]. }
      rewrite <- Eargs. exact G2.
    - apply gholds_sub_inv. exact (SG.gholds_agree GP (t_ns X) E2 (senv EC sg') M2 (t_ghost X) AGX HgvX HGX). }
  (* [comment removed for export] *)
  unfold ret_edge_ok in Hrt. rewrite <- HxC in Hrt. cbn [x_ss s_pc s_regs s_know s_log] in Hrt.
  set (regsC := map (esub sg') (t_regs X)) in *.
  set (knC := map (ksub sg') (t_know X) ++ List.filter (SC.survivesP kn' Wc (pres_rs P S sg)) kn' ++ ik_of P S) in *.
  set (T0 := TMG (t_pc T) (t_regs T) (t_know T) (t_ns T) (t_meas T) (t_rank T) src) in *.
  assert (HGC0 : SG.gholds GP EC M2 (t_ghost T0)) by exact HGC.
  assert (HmT' : bv_unsigned (edenot EC (t_meas T)) = bv_unsigned (edenot E' (t_meas T))).
  { f_equal. symmetry. apply (edenot_agree n0 E' EC); [apply eagree_env_agree; exact AGE | apply (SC.expr_vars_lt_mono (t_ns T)); [exact HmT | lia]]. }
  assert (HgEC : gagree (p_G P) E' EC) by exact HgEC0.
  assert (OUTc : forall y : word, outside_wins E' (p_W P) (bv_unsigned y) -> forall wc, In wc Wc -> ~ SC.in_win E' wc (bv_unsigned y)).
  { intros y Hy wc Hwc Hin. destruct (WINc wc Hwc) as (w' & Hw' & L & U).
    unfold outside_wins in Hy. pose proof (proj1 (Forall_forall _ _) Hy _ Hw') as Hy'.
    destruct w' as [[b' k'] n']. destruct wc as [[b k] n]. unfold SC.in_win in Hin. cbn [win_den SG.win_den fst snd] in L, U, Hy', Hin. lia. }
  assert (FRM : frame_ok E' (p_W P) (p_PS P) M M2).
  { assert (M1M : forall y : word, outside_wins E' (p_W P) (bv_unsigned y) -> M1 y = M y)
      by (intros y Hy; exact (mem_denot_outside_wins E' (p_W P) (s_know ss) M (s_log ss) y HK Hlf Hwin Hy)).
    unfold frame_ok in FR2 |- *. unfold ps_ok in Hps.
    destruct (sm_PS S) as [spc|] eqn:HPS.
    - destruct (p_PS P) as [spe|] eqn:HPP; [|discriminate].
      destruct (SL.dtrue (decide_branch kn' BC_GEU spe (esub sg spc))) eqn:D1; [|discriminate].
      pose proof (SL.geu_true _ _ (SL.dtrue_sound segs E' M1 kn' _ _ _ HK' D1)) as G. rewrite <- esub_den in G.
      intros y Hy Hc'. rewrite <- (M1M y Hy). apply (FR2 y (OUTW y (OUTc y Hy))).
      destruct Hc' as [Hc'|[Hc'|Hc']]; [left; lia | right; left; eapply sh_above_mono; [|exact Hc']; lia | right; right; exact Hc'].
    - assert (F0 : forall y : word, outside_wins E' (p_W P) (bv_unsigned y) -> M2 y = M y)
        by (intros y Hy; rewrite <- (M1M y Hy); exact (FR2 y (OUTW y (OUTc y Hy)))).
      destruct (p_PS P); [intros y Hy _; exact (F0 y Hy) | exact F0]. }
  assert (CMP : forall sgR T', know_ok segs EC M2 (map (ksub sgR) (t_know T') ++ knC) ->
             mval T' (senv EC sgR) = Z.to_nat (bv_unsigned (edenot EC (esub sgR (t_meas T'))))).
  { intros sgR T' _. unfold mval. rewrite esub_den. reflexivity. }
  destruct (find_tm rpc0 (p_tm P ++ p_xt P)) as [T'|] eqn:Hf'.
  - (* [comment removed for export] *)
    destruct (find_tm_in _ _ _ Hf') as [HinT' Hpc'].
    set (sgR := mk_sg (p_G P) T' regsC knC (xh_sg xh0)) in *.
    apply andb_prop in Hrt as [Hrt Hdec]. apply andb_prop in Hrt as [Hrt Hent'].
    apply andb_prop in Hrt as [Hrt Hlen']. apply andb_prop in Hrt as [HG' Hgid].
    destruct (@entailsG_sound (SFP.fx_of ms2) T0 T' (SXT (SS rpc0 regsC [] knC (n0 + t_ns X)) (List.filter SC.is_brb (x_path x)))
                knC sgR _ EC M2 rom R2 Hent' HKC HPC I HGC0 HKC HRC) as [HT' HGT'].
    cbn [x_ss s_pc s_log mem_denot] in HT', HGT'.
    assert (HKT : know_ok segs EC M2 (map (ksub sgR) (t_know T') ++ knC)).
    { apply Forall_app. split; [|exact HKC].
      unfold entailsG in Hent'. apply andb_prop in Hent' as [_ Hg].
      exact (proj1 (gedge_sound T0 T' _ knC sgR _ EC M2 Hg HKC HPC I HGC0 HKC)). }
    pose proof (decreases_sound EC M2 _ T T' sgR _ HKT Hdec) as DEC.
    exists ms3, T', (senv EC sgR), M2. split; [exact Hm3|].
    split; [split; [exact HZ2 | split; [rewrite Hms2' in HRF2; exact HRF2 | exact HT']] |]. split; [exact HGT'|].
    split; [eapply gagree_trans; [exact HgEC | exact (senv_gagree _ EC sgR Hgid)]|].
    split; [reflexivity|]. split; [exact HH2|]. split; [exact FRM|].
    left. split; [exact HinT'|]. unfold mval. rewrite !esub_den. rewrite <- !HmT'. exact DEC.
  - destruct (find_tm rpc0 (p_ex P)) as [X'|] eqn:Hfx; [|discriminate].
    destruct (find_tm_in _ _ _ Hfx) as [HinX' Hpcx].
    set (sgR := mk_sg (p_G P) X' regsC knC (xh_sg xh0)) in *.
    apply andb_prop in Hrt as [Hrt Hent']. apply andb_prop in Hrt as [Hrt Hlen']. apply andb_prop in Hrt as [HG' Hgid].
    destruct (@entailsG_sound (SFP.fx_of ms2) T0 X' (SXT (SS rpc0 regsC [] knC (n0 + t_ns X)) (List.filter SC.is_brb (x_path x)))
                knC sgR _ EC M2 rom R2 Hent' HKC HPC I HGC0 HKC HRC) as [HT' HGT'].
    cbn [x_ss s_pc s_log mem_denot] in HT', HGT'.
    exists ms3, X', (senv EC sgR), M2. split; [exact Hm3|].
    split; [split; [exact HZ2 | split; [rewrite Hms2' in HRF2; exact HRF2 | exact HT']] |]. split; [exact HGT'|].
    split; [eapply gagree_trans; [exact HgEC | exact (senv_gagree _ EC sgR Hgid)]|].
    split; [reflexivity|]. split; [exact HH2|]. split; [exact FRM|]. right. exact HinX'.
Qed.


(* [comment removed for export] *)
Theorem pcheck_soundHSC : forall P IT fuel rr hints (Cnd : env -> Prop),
  pcheckH segs gfp gvc P IT fuel rr hints = true -> itab_sound segs IT ->
  (forall TA, In TA (p_xt P) -> ext_okHF P Cnd TA) ->
  (forall S, In S (p_cs P) -> summ_okHSC S) ->
  (forall E E2, gagree (p_G P) E E2 -> eb E = eb E2 -> Cnd E -> Cnd E2) ->
  (forall E, Cnd E -> wins_client E (p_W P)) ->
  (forall E, Cnd E -> forall w, In w (p_CR P) -> forall z, fst (win_den E w) <= z < snd (win_den E w) -> hmA z) ->
  (forall E M0, Cnd E -> hmH M0 -> know_ok segs E M0 (p_IK P)) ->
  (forall E, Cnd E -> hs_ok E (p_PS P) (p_W P)) ->
  forall T E M rom ms, In T (p_tm P ++ p_xt P) -> hmR rom -> aw_genuine E (p_A P) -> Cnd E -> hmH M ->
    tm_okF segs T E M rom ms -> SG.gholds GP E M (t_ghost T) ->
  exists ms', ExecF.mstepsF segs (fpu (p_A P) E) ms ms' /\ prun_postH P E M rom ms'.
Proof.
  intros P IT fuel rr hints Cnd Hchk HIT HEXT HCS HCG HCW HCR HIK HSTK.
  unfold pcheckH in Hchk. apply andb_prop in Hchk as [Hchk Htms]. apply andb_prop in Hchk as [Hchk HIKc].
  apply andb_prop in Hchk as [Hchk HCRc]. apply andb_prop in Hchk as [Hchk HPSc].
  apply andb_prop in Hchk as [Hchk HAc]. apply andb_prop in Hchk as [Hchk Hcsc].
  apply andb_prop in Hchk as [Hchk HGx].
  apply andb_prop in Hchk as [Hchk HWc].
  apply andb_prop in Hchk as [Hchk Hxtc]. apply andb_prop in Hchk as [Htc Hxc].
  assert (MAIN : forall n r T E M rom ms, In T (p_tm P ++ p_xt P) -> hmR rom -> aw_genuine E (p_A P) -> Cnd E -> hmH M -> tm_okF segs T E M rom ms ->
                   SG.gholds GP E M (t_ghost T) -> mval T E = n -> t_rank T = r ->
                   exists ms', ExecF.mstepsF segs (fpu (p_A P) E) ms ms' /\ prun_postH P E M rom ms').
  { intros n r. pattern n, r. apply lex_ind. clear n r. intros n r IH T E M rom ms HinTT HRom HAG HCnd HHM HT HGT Hn Hr.
    apply in_app_or in HinTT as [HinT|HinX].
    2: { (* [comment removed for export] *)
      destruct (HEXT T HinX E M rom ms HRom HAG HCnd HHM HT HGT) as (ms' & Hms & [(TB & E' & M' & HinB & HTB & HGB & Hg & Hb & HH' & FR & Hdec)|Hpost]).
      - subst n r.
        destruct (IH _ _ Hdec TB E' M' rom ms' HinB HRom (aw_genuine_gagree _ E E' _ Hg (eq_sym Hb) HAc HAG) (HCG E E' Hg (eq_sym Hb) HCnd) HH' HTB HGB eq_refl eq_refl)
          as (ms'' & Hms'' & Hpost).
        exists ms''. split; [eapply ExecF.mstepsF_trans; [exact Hms | exact (ExecF.mstepsF_weaken segs _ _ _ _ (fpu_gagree _ E E' _ Hg (eq_sym Hb) HAc) Hms'')]|].
        destruct Hpost as (X & E'' & M'' & HinX' & HX'' & HGX & Hg'' & Hb'' & HH'' & FR'').
        exists X, E'', M''. split; [exact HinX'|]. split; [exact HX''|]. split; [exact HGX|].
        split; [eapply gagree_trans; [exact Hg | exact Hg'']|]. split; [rewrite Hb''; exact Hb|]. split; [exact HH''|].
        exact (frame_ok_trans_g (p_G P) E E' (p_W P) (p_PS P) M M' M'' Hg (eq_sym Hb) HWc HPSc FR FR'').
      - exists ms'. split; [exact Hms | exact Hpost]. }
    destruct (tms_check_in P IT fuel rr _ hints T Htms HinT) as (hss & Hck). unfold tm_check in Hck.
    destruct (explore segs IT (p_stops P) rr (p_sp P) (p_A P) fuel true false
                (mkbc (facts_of (s_know (tstate T)))) (mk_kix (s_know (tstate T))) (tstate T) []) as [xs|] eqn:Hex;
      [|discriminate].
    apply andb_prop in Hck as [HG Hedges]. apply Nat.leb_le in HG.
    pose proof (proj1 (forallb_forall _ _) Htc T HinT) as HcT.
    pose proof (tm_okXF segs T E M rom ms HcT HT) as HX.
    destruct (explore_sound segs IT _ rr (p_sp P) (p_A P) fuel true false _ _ (tstate T) [] xs HIT eq_refl eq_refl Hex E M rom ms
                (aw_closed_mono _ _ _ HAc HG) HAG HX ltac:(intros E' _; constructor))
      as (x & E' & ms' & Hin & Ha & Hle & Hms0F & HX' & HPx & Hres).
    pose proof (fpu_of _ _ _ _ Hms0F) as Hms.
    pose proof (HPx E' (eagree_refl _ _)) as HPE.
    assert (HRF' : PIosRegs.rfull (ms_regs ms')) by exact (PIosRegs.msteps_rfull segs _ _ (ExecF.mstepsF_msteps segs _ _ _ Hms) (proj1 (proj2 HT))).
    assert (HGE : SG.gholds GP E' M (t_ghost T)).
    { unfold tm_closed in HcT. apply andb_prop in HcT as [_ Hgv].
      apply (SG.gholds_agree GP (t_ns T) E E' M _); [apply eagree_env_agree; exact Ha | exact Hgv | exact HGT]. }
    destruct (edges_ok_in P IT T xs hss x Hedges Hin) as (hs & Hedge).
    pose proof (st_okR_ok segs E' M rom (x_ss x) ms' (st_okX_R segs E' M rom (x_ss x) ms' (proj2 HX')) Hres) as (R & Hms' & HR & Hlf & HK).
    set (ss := x_ss x) in *. cbn [tstate s_next] in Ha, Hle.
    assert (HgE : gagree (p_G P) E E') by (eapply eagree_gagree; [exact HG | exact Ha]).
    assert (HbE : eb E' = eb E) by (destruct Ha as [_ Hb]; symmetry; exact Hb).
    assert (Hmi : edenot E' (t_meas T) = edenot E (t_meas T)).
    { pose proof HcT as HcT'. unfold tm_closed in HcT'. apply andb_prop in HcT' as [HcT' _]. apply andb_prop in HcT' as [HcT' _].
      apply andb_prop in HcT' as [HcT' _]. apply andb_prop in HcT' as [_ Hmc]. symmetry.
      apply (edenot_agree (t_ns T) E E'); [apply eagree_env_agree; exact Ha | exact Hmc]. }
    (* [comment removed for export] *)
    assert (HCnd' : Cnd E') by exact (HCG E E' HgE (eq_sym HbE) HCnd).
    assert (CONT : forall ms3 T' E3 M3, ExecF.mstepsF segs (fpu (p_A P) E) ms ms3 -> tm_okF segs T' E3 M3 rom ms3 -> SG.gholds GP E3 M3 (t_ghost T') ->
                gagree (p_G P) E' E3 -> eb E3 = eb E' -> hmH M3 -> frame_ok E' (p_W P) (p_PS P) M M3 ->
                ((In T' (p_tm P ++ p_xt P) /\ (mval T' E3 < mval T E' \/ (mval T' E3 = mval T E' /\ t_rank T' < t_rank T))%nat)
                 \/ In T' (p_ex P)) ->
                exists ms', ExecF.mstepsF segs (fpu (p_A P) E) ms ms' /\ prun_postH P E M rom ms').
    { intros ms3 T' E3 M3 Hm3 HT3 HG3 Hg3 Hb3 HH3 FR3 Hcase.
      assert (Hg13 : gagree (p_G P) E E3) by (eapply gagree_trans; [exact HgE | exact Hg3]).
      assert (Hb13 : eb E3 = eb E) by (rewrite Hb3; exact HbE).
      assert (FR13 : frame_ok E (p_W P) (p_PS P) M M3).
      { apply (frame_ok_trans_g (p_G P) E E' (p_W P) (p_PS P) M M M3 HgE (eq_sym HbE) HWc HPSc); [apply frame_ok_refl | exact FR3]. }
      destruct Hcase as [[HinT' Hd]|HinX].
      - assert (Hmv : mval T E' = n) by (subst n; unfold mval; rewrite Hmi; reflexivity).
        rewrite Hmv in Hd. rewrite Hr in Hd.
        destruct (IH _ _ Hd T' E3 M3 rom ms3 HinT' HRom (aw_genuine_gagree _ E E3 _ Hg13 (eq_sym Hb13) HAc HAG)
                    (HCG E E3 Hg13 (eq_sym Hb13) HCnd) HH3 HT3 HG3 eq_refl eq_refl)
          as (ms'' & Hms'' & Hpost).
        exists ms''. split; [eapply ExecF.mstepsF_trans; [exact Hm3 | exact (ExecF.mstepsF_weaken segs _ _ _ _ (fpu_gagree _ E E3 _ Hg13 (eq_sym Hb13) HAc) Hms'')]|].
        destruct Hpost as (X & E'' & M'' & HinX & HX'' & HGX & Hg'' & Hb'' & HH'' & FR'').
        exists X, E'', M''. split; [exact HinX|]. split; [exact HX''|]. split; [exact HGX|].
        split; [eapply gagree_trans; [exact Hg13 | exact Hg'']|]. split; [rewrite Hb''; exact Hb13|]. split; [exact HH''|].
        exact (frame_ok_trans_g (p_G P) E E3 (p_W P) (p_PS P) M M3 M'' Hg13 (eq_sym Hb13) HWc HPSc FR13 FR'').
      - exists ms3. split; [exact Hm3|]. exists T', E3, M3. split; [exact HinX|]. split; [exact HT3|]. split; [exact HG3|].
        split; [exact Hg13|]. split; [exact Hb13|]. split; [exact HH3 | exact FR13]. }
    unfold edge_ok in Hedge. fold ss in Hedge.
    destruct (exit_kn ss) as [kn'|] eqn:Hkn; [|discriminate].
    pose proof (exit_kn_ok segs E' M ss kn' Hkn Hlf HK) as HK'.
    set (M1 := mem_denot E' M (s_log ss)) in *.
    assert (FRAME1 : forall (Hwin : wins_ok (p_W P) (s_know ss) (s_log ss) = true) (y : word),
                       outside_wins E' (p_W P) (bv_unsigned y) -> M1 y = M y).
    { intros Hwin y Hy. exact (mem_denot_outside_wins E' (p_W P) (s_know ss) M (s_log ss) y HK Hlf Hwin Hy). }
    (* [comment removed for export] *)
    assert (HWR : PIosRegs.wrel segs M M1).
    { pose proof (PIosRegs.msteps_wrel segs _ _ (ExecF.mstepsF_msteps segs _ _ _ Hms)) as W.
      destruct HT as (_ & _ & (R0 & Hms0 & _)). rewrite Hms0, Hms' in W. cbn [tstate s_log mem_denot] in W. exact W. }
    assert (HH1 : forall (Hwin : wins_ok (p_W P) (s_know ss) (s_log ss) = true), hmH M1).
    { intros Hwin. exact (HMF E' (p_W P) M M1 (HCW E' HCnd') HHM HWR (FRAME1 Hwin)). }
    destruct (find_tm (s_pc ss) (p_tm P ++ p_xt P)) as [T'|] eqn:Hf.
    + (* [comment removed for export] *)
      destruct (find_tm_in _ _ _ Hf) as [HinT' Hpc'].
      set (sg := mk_sg (p_G P) T' (s_regs ss) kn' (xh_sg hs)) in *.
      apply andb_prop in Hedge as [Hedge Hdec]. apply andb_prop in Hedge as [Hedge Hent].
      apply andb_prop in Hedge as [Hedge Hlen]. apply andb_prop in Hedge as [Hedge Hgid]. apply andb_prop in Hedge as [Hwin HG'].
      destruct (@entailsG_sound (SFP.fx_of ms') T T' x kn' sg _ E' M rom R Hent HK HPE Hlf HGE HK' HR) as [HT' HGT'].
      fold ss M1 in HT', HGT'.
      assert (HKT : know_ok segs E' M1 (map (ksub sg) (t_know T') ++ kn')).
      { apply Forall_app. split; [|exact HK'].
        unfold entailsG in Hent. apply andb_prop in Hent as [_ Hg].
        exact (proj1 (gedge_sound T T' x kn' sg _ E' M Hg HK HPE Hlf HGE HK')). }
      rewrite <- Hms' in HT'.
      pose proof (decreases_sound E' M1 _ T T' sg _ HKT Hdec) as DEC.
      apply (CONT ms' T' (senv E' sg) M1 Hms (conj (proj1 HX') (conj HRF' HT')) HGT').
      * exact (senv_gagree _ E' sg Hgid).
      * reflexivity.
      * exact (HH1 Hwin).
      * apply frame_ok_full. exact (FRAME1 Hwin).
      * left. split; [exact HinT'|]. unfold mval. rewrite !esub_den. exact DEC.
    + destruct (find_csr (s_pc ss) (nth 1 (s_regs ss) (ELit 0)) (p_cs P)) as [S|] eqn:Hfc.
      * (* [comment removed for export] *)
        destruct (find_csr_in _ _ _ _ Hfc) as [HinS _].
        pose proof (proj1 (forallb_forall _ _) Hcsc S HinS) as HcS. cbv beta in HcS.
        apply andb_prop in HcS as [HcS _]. apply andb_prop in HcS as [HcS _]. apply andb_prop in HcS as [HcS _]. apply andb_prop in HcS as [_ Hpcl].
        assert (Hwin : wins_ok (p_W P) (s_know ss) (s_log ss) = true).
        { unfold call_edge_ok in Hedge. cbv zeta in Hedge.
          destruct (exit_kn (x_ss x)) as [l|]; [|discriminate].
          repeat (apply andb_prop in Hedge as [Hedge _]). exact Hedge. }
        assert (HH1' : hmH (ms_mem ms')) by (rewrite Hms'; exact (HH1 Hwin)).
        destruct (call_edge_soundHSC P IT T x hs S E' M rom ms' Cnd HIT (HCS S HinS) Hedge Hpcl HG HcT HGE HX' HRF'
                    (aw_genuine_gagree _ E E' _ HgE (eq_sym HbE) HAc HAG) HPx Hres HCRc HCnd' HCG HCW HCR HIK HSTK HH1' HRom)
          as (ms3 & T' & E3 & M3 & Hm & HT3 & HG3 & Hg3 & Hb3 & HH3 & FR3 & Hcase).
        exact (CONT ms3 T' E3 M3 (ExecF.mstepsF_trans segs _ _ _ _ Hms (ExecF.mstepsF_weaken segs _ _ _ _ (fpu_gagree _ E E' _ HgE (eq_sym HbE) HAc) Hm))
                 HT3 HG3 Hg3 Hb3 HH3 FR3 Hcase).
      * (* [comment removed for export] *)
        destruct (find_tm (s_pc ss) (p_ex P)) as [X|] eqn:Hfx; [|discriminate].
        destruct (find_tm_in _ _ _ Hfx) as [HinX Hpcx].
        set (sg := mk_sg (p_G P) X (s_regs ss) kn' (xh_sg hs)) in *.
        apply andb_prop in Hedge as [Hedge Hent]. apply andb_prop in Hedge as [Hedge Hlen].
        apply andb_prop in Hedge as [Hedge Hgid]. apply andb_prop in Hedge as [Hwin HG'].
        destruct (@entailsG_sound (SFP.fx_of ms') T X x kn' sg _ E' M rom R Hent HK HPE Hlf HGE HK' HR) as [HXX HGX].
        fold ss M1 in HXX, HGX. rewrite <- Hms' in HXX.
        apply (CONT ms' X (senv E' sg) M1 Hms (conj (proj1 HX') (conj HRF' HXX)) HGX).
        -- exact (senv_gagree _ E' sg Hgid).
        -- reflexivity.
        -- exact (HH1 Hwin).
        -- apply frame_ok_full. exact (FRAME1 Hwin).
        -- right. exact HinX. }
  intros T E M rom ms HinT HRom HAG HCnd HHM HT HGT. exact (MAIN _ _ T E M rom ms HinT HRom HAG HCnd HHM HT HGT eq_refl eq_refl).
Qed.

(* [comment removed for export] *)
Theorem pcheck_soundHS : forall P IT fuel rr hints (Cnd : env -> Prop),
  pcheckH segs gfp gvc P IT fuel rr hints = true -> itab_sound segs IT ->
  (forall TA, In TA (p_xt P) -> ext_okHF P Cnd TA) ->
  (forall S, In S (p_cs P) -> summ_okHS S) ->
  (forall E E2, gagree (p_G P) E E2 -> eb E = eb E2 -> Cnd E -> Cnd E2) ->
  (forall E, Cnd E -> wins_client E (p_W P)) ->
  (forall E, Cnd E -> forall w, In w (p_CR P) -> forall z, fst (win_den E w) <= z < snd (win_den E w) -> hmA z) ->
  (forall E M0, Cnd E -> hmH M0 -> know_ok segs E M0 (p_IK P)) ->
  (forall E, Cnd E -> hs_ok E (p_PS P) (p_W P)) ->
  forall T E M rom ms, In T (p_tm P ++ p_xt P) -> hmR rom -> aw_genuine E (p_A P) -> Cnd E -> hmH M ->
    tm_okF segs T E M rom ms -> SG.gholds GP E M (t_ghost T) ->
  exists ms', ExecF.mstepsF segs (fpu (p_A P) E) ms ms' /\ prun_postH P E M rom ms'.
Proof.
  intros P IT fuel rr hints Cnd Hc HIT HEXT HCS.
  exact (pcheck_soundHSC P IT fuel rr hints Cnd Hc HIT HEXT (fun S H => summ_okHS_C S (HCS S H))).
Qed.



(* [comment removed for export] *)
Lemma ext_okHF_mono : forall P (C C' : env -> Prop) TA, ext_okHF P C TA -> (forall E, C' E -> C E) -> ext_okHF P C' TA.
Proof. intros P C C' TA H Hm E M rom ms H1 H2 H3. exact (H E M rom ms H1 H2 (Hm E H3)). Qed.

Lemma pcheckH_closed : forall P IT fuel rr hints, pcheckH segs gfp gvc P IT fuel rr hints = true ->
  forallb (win_closed (p_G P)) (p_W P) = true /\ ps_closed (p_G P) (p_PS P) = true /\ forallb (win_closed (p_G P)) (p_CR P) = true.
Proof.
  intros P IT fuel rr hints Hc. unfold pcheckH in Hc. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _].
  apply andb_prop in Hc as [Hc HCRc]. apply andb_prop in Hc as [Hc HPSc].
  split; [|split; [exact HPSc | exact HCRc]]. repeat (apply andb_prop in Hc as [Hc ?]). assumption.
Qed.

(* [comment removed for export] *)
Lemma cnd_hs_gagree : forall P E1 E2, forallb (win_closed (p_G P)) (p_W P) = true -> ps_closed (p_G P) (p_PS P) = true ->
  gagree (p_G P) E1 E2 -> eb E1 = eb E2 ->
  wins_client E1 (p_W P) /\ hs_ok E1 (p_PS P) (p_W P) -> wins_client E2 (p_W P) /\ hs_ok E2 (p_PS P) (p_W P).
Proof.
  intros P E1 E2 HWc HPSc Hg Hb [H1 H2]. split; [|exact (hs_ok_gagree (p_G P) E1 E2 _ _ Hg Hb HPSc H2)].
  unfold wins_client in *. apply Forall_forall. intros w Hw.
  rewrite <- (win_den_gagree (p_G P) E1 E2 w Hg Hb (proj1 (forallb_forall _ _) HWc w Hw)).
  exact (proj1 (Forall_forall _ _) H1 w Hw).
Qed.

(* [comment removed for export] *)
Theorem summ_of_pcheckHS : forall P IT fuel rr hints T0,
  pcheckH segs gfp gvc P IT fuel rr hints = true -> itab_sound segs IT -> p_CR P = [] -> p_IK P = [] ->
  (forall TA, In TA (p_xt P) -> ext_okHF P (fun E => wins_client E (p_W P)) TA) -> (forall S, In S (p_cs P) -> summ_okHS S) ->
  In T0 (p_tm P) -> summ_okHS (SUMX (p_G P) T0 (p_ex P) (p_W P) (p_A P) (p_PS P) false).
Proof.
  intros P IT fuel rr hints T0 Hc HIT HCR0 HIK0 HEXT HCS Hin E M rom ms HRom HAG HWC HSK HHM HT HG.
  cbn [SUMX sm_pre sm_post sm_G sm_W sm_A sm_PS sm_PR sm_CR] in *.
  destruct (pcheckH_closed P IT fuel rr hints Hc) as (HWc & HPSc & _).
  destruct (pcheck_soundHS P IT fuel rr hints (fun E => wins_client E (p_W P) /\ hs_ok E (p_PS P) (p_W P)) Hc HIT
              (fun TA H => ext_okHF_mono P _ _ TA (HEXT TA H) (fun E1 H1 => proj1 H1)) HCS
              (fun E1 E2 Hg Hb H1 => cnd_hs_gagree P E1 E2 HWc HPSc Hg Hb H1)
              ltac:(intros E1 H1; exact (proj1 H1))
              ltac:(intros E1 _ w Hw; rewrite HCR0 in Hw; destruct Hw)
              ltac:(intros E1 M1 _ _; rewrite HIK0; constructor)
              ltac:(intros E1 H1; exact (proj2 H1))
              T0 E M rom ms ltac:(apply in_or_app; left; exact Hin) HRom HAG (conj HWC HSK) HHM HT HG)
    as (ms' & Hms & X & E' & M' & HinX & HX & HGX & Hg & Hb & HH & FR).
  exists ms', X, E', M'. auto 10.
Qed.

Theorem summ_of_pcheckHS_CR : forall P IT fuel rr hints T0,
  (forall lo hi z, hmC lo hi -> lo <= z < hi -> hmA z) ->
  pcheckH segs gfp gvc P IT fuel rr hints = true -> itab_sound segs IT -> cr_inside_b P = true -> p_IK P = [] ->
  (forall TA, In TA (p_xt P) -> ext_okHF P (fun E => wins_client E (p_W P)) TA) -> (forall S, In S (p_cs P) -> summ_okHS S) ->
  In T0 (p_tm P) -> summ_okHS (SUMX (p_G P) T0 (p_ex P) (p_W P) (p_A P) (p_PS P) false).
Proof.
  intros P IT fuel rr hints T0 HMCA Hc HIT HCRin HIK0 HEXT HCS Hin E M rom ms HRom HAG HWC HSK HHM HT HG.
  cbn [SUMX sm_pre sm_post sm_G sm_W sm_A sm_PS sm_PR sm_CR] in *.
  destruct (pcheckH_closed P IT fuel rr hints Hc) as (HWc & HPSc & _).
  destruct (pcheck_soundHS P IT fuel rr hints (fun E => wins_client E (p_W P) /\ hs_ok E (p_PS P) (p_W P)) Hc HIT
              (fun TA H => ext_okHF_mono P _ _ TA (HEXT TA H) (fun E1 H1 => proj1 H1)) HCS
              (fun E1 E2 Hg Hb H1 => cnd_hs_gagree P E1 E2 HWc HPSc Hg Hb H1)
              ltac:(intros E1 H1; exact (proj1 H1))
              ltac:(intros E1 H1 w Hw z Hz;
                    pose proof (proj1 (forallb_forall _ _) HCRin w Hw) as Hx; apply existsb_exists in Hx as (w' & Hw' & Hi);
                    pose proof (win_inside_b_ok E1 w w' z Hi Hz) as Hz';
                    exact (HMCA _ _ z (proj1 (Forall_forall _ _) (proj1 H1) w' Hw') Hz'))
              ltac:(intros E1 M1 _ _; rewrite HIK0; constructor)
              ltac:(intros E1 H1; exact (proj2 H1))
              T0 E M rom ms ltac:(apply in_or_app; left; exact Hin) HRom HAG (conj HWC HSK) HHM HT HG)
    as (ms' & Hms & X & E' & M' & HinX & HX & HGX & Hg & Hb & HH & FR).
  exists ms', X, E', M'. auto 10.
Qed.

Theorem summ_of_pcheckHS_CRL : forall P IT fuel rr hints T0,
  pcheckH segs gfp gvc P IT fuel rr hints = true -> itab_sound segs IT -> p_IK P = [] ->
  (forall TA, In TA (p_xt P) -> ext_okHF P (fun E => wins_client E (p_W P)) TA) -> (forall S, In S (p_cs P) -> summ_okHS S) ->
  In T0 (p_tm P) ->
  (forall E M rom ms, hmH M -> tm_okF segs T0 E M rom ms ->
     forall w, In w (p_CR P) -> forall z, fst (win_den E w) <= z < snd (win_den E w) -> hmA z) ->
  summ_okHS (SUMX (p_G P) T0 (p_ex P) (p_W P) (p_A P) (p_PS P) false).
Proof.
  intros P IT fuel rr hints T0 Hc HIT HIK0 HEXT HCS Hin HL E M rom ms HRom HAG HWC HSK HHM HT HG.
  cbn [SUMX sm_pre sm_post sm_G sm_W sm_A sm_PS sm_PR sm_CR] in *.
  destruct (pcheckH_closed P IT fuel rr hints Hc) as (HWc & HPSc & HCRc).
  set (CRok := fun E1 => forall w, In w (p_CR P) -> forall z, fst (win_den E1 w) <= z < snd (win_den E1 w) -> hmA z).
  destruct (pcheck_soundHS P IT fuel rr hints (fun E1 => (wins_client E1 (p_W P) /\ hs_ok E1 (p_PS P) (p_W P)) /\ CRok E1) Hc HIT
              (fun TA H => ext_okHF_mono P _ _ TA (HEXT TA H) (fun E1 H1 => proj1 (proj1 H1))) HCS
              ltac:(intros E1 E2 Hg Hb [H1 H2]; split;
                    [ exact (cnd_hs_gagree P E1 E2 HWc HPSc Hg Hb H1)
                    | intros w Hw z Hz; apply (H2 w Hw z);
                      rewrite (win_den_gagree (p_G P) E1 E2 w Hg Hb (proj1 (forallb_forall _ _) HCRc w Hw)); exact Hz ])
              ltac:(intros E1 H1; exact (proj1 (proj1 H1)))
              ltac:(intros E1 H1; exact (proj2 H1))
              ltac:(intros E1 M1 _ _; rewrite HIK0; constructor)
              ltac:(intros E1 H1; exact (proj2 (proj1 H1)))
              T0 E M rom ms ltac:(apply in_or_app; left; exact Hin) HRom HAG (conj (conj HWC HSK) (HL E M rom ms HHM HT)) HHM HT HG)
    as (ms' & Hms & X & E' & M' & HinX & HX & HGX & Hg & Hb & HH & FR).
  exists ms', X, E', M'. auto 10.
Qed.

(* [comment removed for export] *)
Theorem summ_of_pcheckHSC : forall P IT fuel rr hints T0,
  pcheckH segs gfp gvc P IT fuel rr hints = true -> itab_sound segs IT -> p_IK P = [] ->
  (forall TA, In TA (p_xt P) -> ext_okHF P (fun E => wins_client E (p_W P)) TA) -> (forall S, In S (p_cs P) -> summ_okHSC S) ->
  In T0 (p_tm P) -> summ_okHSC (SUMY (p_G P) T0 (p_ex P) (p_W P) (p_A P) (p_PS P) false (p_CR P)).
Proof.
  intros P IT fuel rr hints T0 Hc HIT HIK0 HEXT HCS Hin E M rom ms HRom HAG HWC HSK HCRL HHM HT HG.
  cbn [sm_pre sm_post sm_G sm_W sm_A sm_PS sm_PR sm_CR] in *.
  destruct (pcheckH_closed P IT fuel rr hints Hc) as (HWc & HPSc & HCRc).
  destruct (pcheck_soundHSC P IT fuel rr hints (fun E1 => (wins_client E1 (p_W P) /\ hs_ok E1 (p_PS P) (p_W P)) /\ crs_law E1 (p_CR P)) Hc HIT
              (fun TA H => ext_okHF_mono P _ _ TA (HEXT TA H) (fun E1 H1 => proj1 (proj1 H1))) HCS
              ltac:(intros E1 E2 Hg Hb [H1 H2]; split;
                    [ exact (cnd_hs_gagree P E1 E2 HWc HPSc Hg Hb H1)
                    | intros w Hw z Hz; apply (H2 w Hw z);
                      rewrite (win_den_gagree (p_G P) E1 E2 w Hg Hb (proj1 (forallb_forall _ _) HCRc w Hw)); exact Hz ])
              ltac:(intros E1 H1; exact (proj1 (proj1 H1)))
              ltac:(intros E1 H1; exact (proj2 H1))
              ltac:(intros E1 M1 _ _; rewrite HIK0; constructor)
              ltac:(intros E1 H1; exact (proj2 (proj1 H1)))
              T0 E M rom ms ltac:(apply in_or_app; left; exact Hin) HRom HAG (conj (conj HWC HSK) HCRL) HHM HT HG)
    as (ms' & Hms & X & E' & M' & HinX & HX & HGX & Hg & Hb & HH & FR).
  exists ms', X, E', M'. auto 10.
Qed.

End Sound.

(* [comment removed for export] *)
Section SoundF.
Variable segs : list Segment.
Variable GP : nat -> list word -> (word -> option byte) -> Prop.
Variable gfp : nat -> list expr -> list SG.gwin.
Variable gvc : SG.vc -> bool.
Hypothesis HGF : SG.gp_frameP GP gfp.
Hypothesis HGV : forall c, gvc c = true -> SG.vc_holds segs GP c.
Variable hmH : (word -> option byte) -> Prop.
Variable hmA : Z -> Prop.
Variable hmC : Z -> Z -> Prop.
Variable hmR : (word -> option byte) -> Prop.
Hypothesis HMC_sub : forall lo hi lo' hi', hmC lo hi -> lo <= lo' -> hi' <= hi -> hmC lo' hi'.
Hypothesis HMF : forall E W M M', wins_client hmC E W -> hmH M -> PIosRegs.wrel segs M M' ->
  (forall x : word, outside_wins E W (bv_unsigned x) -> M' x = M x) -> hmH M'.
Variable hmF : ExecF.footprint.

Definition hmS0 (s n : Z) : Prop := True.
Lemma HMS0_mono : forall s n s' n', hmS0 s n -> s - n <= s' - n' -> s' <= s -> hmS0 s' n'.
Proof. intros. exact I. Qed.
Lemma hs_ok0 : forall E PS W, hs_ok hmS0 E PS W.
Proof. intros E PS W. unfold hs_ok. destruct (dstk PS W) as [[? ?]|]; exact I. Qed.
Lemma summ_okHF_S0 : forall S, summ_okHF segs GP hmH hmA hmC hmR hmF S -> summ_okHS segs GP hmH hmA hmC hmR hmF hmS0 S.
Proof. intros S H E M rom ms H1 H2 H3 _ H5 H6 H7. exact (H E M rom ms H1 H2 H3 H5 H6 H7). Qed.
Lemma summ_okHS0_F : forall S, summ_okHS segs GP hmH hmA hmC hmR hmF hmS0 S -> summ_okHF segs GP hmH hmA hmC hmR hmF S.
Proof. intros S H E M rom ms H1 H2 H3 H5 H6 H7. exact (H E M rom ms H1 H2 H3 (hs_ok0 _ _ _) H5 H6 H7). Qed.

Theorem pcheck_soundHF : forall P IT fuel rr hints (Cnd : env -> Prop),
  pcheckH segs gfp gvc P IT fuel rr hints = true -> itab_sound segs IT ->
  (forall TA, In TA (p_xt P) -> ext_okHF segs GP hmH hmA hmR hmF P Cnd TA) ->
  (forall S, In S (p_cs P) -> summ_okHF segs GP hmH hmA hmC hmR hmF S) ->
  (forall E E2, gagree (p_G P) E E2 -> eb E = eb E2 -> Cnd E -> Cnd E2) ->
  (forall E, Cnd E -> wins_client hmC E (p_W P)) ->
  (forall E, Cnd E -> forall w, In w (p_CR P) -> forall z, fst (win_den E w) <= z < snd (win_den E w) -> hmA z) ->
  (forall E M0, Cnd E -> hmH M0 -> know_ok segs E M0 (p_IK P)) ->
  forall T E M rom ms, In T (p_tm P ++ p_xt P) -> hmR rom -> aw_genuine E (p_A P) -> Cnd E -> hmH M ->
    tm_okF segs T E M rom ms -> SG.gholds GP E M (t_ghost T) ->
  exists ms', ExecF.mstepsF segs (fpu hmF (p_A P) E) ms ms' /\ prun_postH segs GP hmH hmA P E M rom ms'.
Proof.
  intros P IT fuel rr hints Cnd Hc HIT HEXT HCS HCG HCW HCR HIK.
  exact (pcheck_soundHS segs GP gfp gvc HGF HGV hmH hmA hmC hmR HMC_sub HMF hmF hmS0 HMS0_mono P IT fuel rr hints Cnd Hc HIT HEXT
           (fun S H => summ_okHF_S0 S (HCS S H)) HCG HCW HCR HIK (fun E _ => hs_ok0 E _ _)).
Qed.

Theorem summ_of_pcheckHF : forall P IT fuel rr hints T0,
  pcheckH segs gfp gvc P IT fuel rr hints = true -> itab_sound segs IT -> p_CR P = [] -> p_IK P = [] ->
  (forall TA, In TA (p_xt P) -> ext_okHF segs GP hmH hmA hmR hmF P (fun E => wins_client hmC E (p_W P)) TA) ->
  (forall S, In S (p_cs P) -> summ_okHF segs GP hmH hmA hmC hmR hmF S) ->
  In T0 (p_tm P) -> summ_okHF segs GP hmH hmA hmC hmR hmF (SUMX (p_G P) T0 (p_ex P) (p_W P) (p_A P) (p_PS P) false).
Proof.
  intros P IT fuel rr hints T0 Hc HIT HCR0 HIK0 HEXT HCS Hin. apply summ_okHS0_F.
  exact (summ_of_pcheckHS segs GP gfp gvc HGF HGV hmH hmA hmC hmR HMC_sub HMF hmF hmS0 HMS0_mono P IT fuel rr hints T0 Hc HIT HCR0 HIK0
           HEXT (fun S H => summ_okHF_S0 S (HCS S H)) Hin).
Qed.

Theorem summ_of_pcheckHF_CR : forall P IT fuel rr hints T0,
  (forall lo hi z, hmC lo hi -> lo <= z < hi -> hmA z) ->
  pcheckH segs gfp gvc P IT fuel rr hints = true -> itab_sound segs IT -> cr_inside_b P = true -> p_IK P = [] ->
  (forall TA, In TA (p_xt P) -> ext_okHF segs GP hmH hmA hmR hmF P (fun E => wins_client hmC E (p_W P)) TA) ->
  (forall S, In S (p_cs P) -> summ_okHF segs GP hmH hmA hmC hmR hmF S) ->
  In T0 (p_tm P) -> summ_okHF segs GP hmH hmA hmC hmR hmF (SUMX (p_G P) T0 (p_ex P) (p_W P) (p_A P) (p_PS P) false).
Proof.
  intros P IT fuel rr hints T0 HMCA Hc HIT HCRin HIK0 HEXT HCS Hin. apply summ_okHS0_F.
  exact (summ_of_pcheckHS_CR segs GP gfp gvc HGF HGV hmH hmA hmC hmR HMC_sub HMF hmF hmS0 HMS0_mono P IT fuel rr hints T0 HMCA Hc HIT
           HCRin HIK0 HEXT (fun S H => summ_okHF_S0 S (HCS S H)) Hin).
Qed.

Theorem summ_of_pcheckHF_CRL : forall P IT fuel rr hints T0,
  pcheckH segs gfp gvc P IT fuel rr hints = true -> itab_sound segs IT -> p_IK P = [] ->
  (forall TA, In TA (p_xt P) -> ext_okHF segs GP hmH hmA hmR hmF P (fun E => wins_client hmC E (p_W P)) TA) ->
  (forall S, In S (p_cs P) -> summ_okHF segs GP hmH hmA hmC hmR hmF S) ->
  In T0 (p_tm P) ->
  (forall E M rom ms, hmH M -> tm_okF segs T0 E M rom ms ->
     forall w, In w (p_CR P) -> forall z, fst (win_den E w) <= z < snd (win_den E w) -> hmA z) ->
  summ_okHF segs GP hmH hmA hmC hmR hmF (SUMX (p_G P) T0 (p_ex P) (p_W P) (p_A P) (p_PS P) false).
Proof.
  intros P IT fuel rr hints T0 Hc HIT HIK0 HEXT HCS Hin HL. apply summ_okHS0_F.
  exact (summ_of_pcheckHS_CRL segs GP gfp gvc HGF HGV hmH hmA hmC hmR HMC_sub HMF hmF hmS0 HMS0_mono P IT fuel rr hints T0 Hc HIT HIK0
           HEXT (fun S H => summ_okHF_S0 S (HCS S H)) Hin HL).
Qed.
End SoundF.

(* [comment removed for export] *)
Section SoundC.
Variable segs : list Segment.
Variable GP : nat -> list word -> (word -> option byte) -> Prop.
Variable gfp : nat -> list expr -> list SG.gwin.
Variable gvc : SG.vc -> bool.
Hypothesis HGF : SG.gp_frameP GP gfp.
Hypothesis HGV : forall c, gvc c = true -> SG.vc_holds segs GP c.
Variable hmH : (word -> option byte) -> Prop.
Variable hmA : Z -> Prop.
Variable hmC : Z -> Z -> Prop.
Variable hmR : (word -> option byte) -> Prop.
Hypothesis HMC_sub : forall lo hi lo' hi', hmC lo hi -> lo <= lo' -> hi' <= hi -> hmC lo' hi'.
Hypothesis HMF : forall E W M M', wins_client hmC E W -> hmH M -> PIosRegs.wrel segs M M' ->
  (forall x : word, outside_wins E W (bv_unsigned x) -> M' x = M x) -> hmH M'.

Definition fp0 : ExecF.footprint := fun _ _ => False.
Lemma fpu0 : forall A E ms ms', ExecF.mstepsF segs (fpu fp0 A E) ms ms' -> ExecF.mstepsF segs (fp_of A E) ms ms'.
Proof. intros A E ms ms' H. exact (ExecF.mstepsF_weaken segs _ _ _ _ (fun b j Hb => match Hb with or_introl h => h | or_intror f => False_ind _ f end) H). Qed.
Lemma summ_okH_F0 : forall S, summ_okH segs GP hmH hmA hmC hmR S -> summ_okHF segs GP hmH hmA hmC hmR fp0 S.
Proof.
  intros S H E M rom ms H1 H2 H3 H4 H5 H6. destruct (H E M rom ms H1 H2 H3 H4 H5 H6) as (ms' & X & E' & M' & Hm & R).
  exists ms', X, E', M'. split; [exact (fpu_of segs fp0 _ _ _ _ Hm) | exact R].
Qed.
Lemma summ_okH_of_F0 : forall S, summ_okHF segs GP hmH hmA hmC hmR fp0 S -> summ_okH segs GP hmH hmA hmC hmR S.
Proof.
  intros S H E M rom ms H1 H2 H3 H4 H5 H6. destruct (H E M rom ms H1 H2 H3 H4 H5 H6) as (ms' & X & E' & M' & Hm & R).
  exists ms', X, E', M'. split; [exact (fpu0 _ _ _ _ Hm) | exact R].
Qed.
Lemma ext_okH_F0 : forall P Cnd TA, ext_okH segs GP hmH hmA hmR P Cnd TA -> ext_okHF segs GP hmH hmA hmR fp0 P Cnd TA.
Proof.
  intros P Cnd TA H E M rom ms H1 H2 H3 H4 H5 H6. destruct (H E M rom ms H1 H2 H3 H4 H5 H6) as (ms' & Hm & R).
  exists ms'. split; [exact (fpu_of segs fp0 _ _ _ _ Hm) | exact R].
Qed.

Theorem pcheck_soundH : forall P IT fuel rr hints (Cnd : env -> Prop),
  pcheckH segs gfp gvc P IT fuel rr hints = true -> itab_sound segs IT ->
  (forall TA, In TA (p_xt P) -> ext_okH segs GP hmH hmA hmR P Cnd TA) ->
  (forall S, In S (p_cs P) -> summ_okH segs GP hmH hmA hmC hmR S) ->
  (forall E E2, gagree (p_G P) E E2 -> eb E = eb E2 -> Cnd E -> Cnd E2) ->
  (forall E, Cnd E -> wins_client hmC E (p_W P)) ->
  (forall E, Cnd E -> forall w, In w (p_CR P) -> forall z, fst (win_den E w) <= z < snd (win_den E w) -> hmA z) ->
  (forall E M0, Cnd E -> hmH M0 -> know_ok segs E M0 (p_IK P)) ->
  forall T E M rom ms, In T (p_tm P ++ p_xt P) -> hmR rom -> aw_genuine E (p_A P) -> Cnd E -> hmH M ->
    tm_okF segs T E M rom ms -> SG.gholds GP E M (t_ghost T) ->
  exists ms', ExecF.mstepsF segs (fp_of (p_A P) E) ms ms' /\ prun_postH segs GP hmH hmA P E M rom ms'.
Proof.
  intros P IT fuel rr hints Cnd Hc HIT HEXT HCS HCG HCW HCR HIK T E M rom ms HinT HRom HAG HCnd HHM HT HGT.
  destruct (pcheck_soundHF segs GP gfp gvc HGF HGV hmH hmA hmC hmR HMC_sub HMF fp0 P IT fuel rr hints Cnd Hc HIT
              (fun TA H => ext_okH_F0 P Cnd TA (HEXT TA H)) (fun S H => summ_okH_F0 S (HCS S H)) HCG HCW HCR HIK
              T E M rom ms HinT HRom HAG HCnd HHM HT HGT) as (ms' & Hm & R).
  exists ms'. split; [exact (fpu0 _ _ _ _ Hm) | exact R].
Qed.

Theorem summ_of_pcheckH : forall P IT fuel rr hints T0,
  pcheckH segs gfp gvc P IT fuel rr hints = true -> itab_sound segs IT -> p_CR P = [] -> p_IK P = [] ->
  (forall TA, In TA (p_xt P) -> ext_okH segs GP hmH hmA hmR P (fun E => wins_client hmC E (p_W P)) TA) ->
  (forall S, In S (p_cs P) -> summ_okH segs GP hmH hmA hmC hmR S) ->
  In T0 (p_tm P) -> summ_okH segs GP hmH hmA hmC hmR (SUMX (p_G P) T0 (p_ex P) (p_W P) (p_A P) (p_PS P) false).
Proof.
  intros P IT fuel rr hints T0 Hc HIT HCR0 HIK0 HEXT HCS Hin.
  apply summ_okH_of_F0.
  exact (summ_of_pcheckHF segs GP gfp gvc HGF HGV hmH hmA hmC hmR HMC_sub HMF fp0 P IT fuel rr hints T0 Hc HIT HCR0 HIK0
           (fun TA H => ext_okH_F0 P _ TA (HEXT TA H)) (fun S H => summ_okH_F0 S (HCS S H)) Hin).
Qed.

Theorem summ_of_pcheckH_CR : forall P IT fuel rr hints T0,
  (forall lo hi z, hmC lo hi -> lo <= z < hi -> hmA z) ->
  pcheckH segs gfp gvc P IT fuel rr hints = true -> itab_sound segs IT -> cr_inside_b P = true -> p_IK P = [] ->
  (forall TA, In TA (p_xt P) -> ext_okH segs GP hmH hmA hmR P (fun E => wins_client hmC E (p_W P)) TA) ->
  (forall S, In S (p_cs P) -> summ_okH segs GP hmH hmA hmC hmR S) ->
  In T0 (p_tm P) -> summ_okH segs GP hmH hmA hmC hmR (SUMX (p_G P) T0 (p_ex P) (p_W P) (p_A P) (p_PS P) false).
Proof.
  intros P IT fuel rr hints T0 HMCA Hc HIT HCRin HIK0 HEXT HCS Hin.
  apply summ_okH_of_F0.
  exact (summ_of_pcheckHF_CR segs GP gfp gvc HGF HGV hmH hmA hmC hmR HMC_sub HMF fp0 P IT fuel rr hints T0 HMCA Hc HIT HCRin HIK0
           (fun TA H => ext_okH_F0 P _ TA (HEXT TA H)) (fun S H => summ_okH_F0 S (HCS S H)) Hin).
Qed.

Theorem summ_of_pcheckH_CRL : forall P IT fuel rr hints T0,
  pcheckH segs gfp gvc P IT fuel rr hints = true -> itab_sound segs IT -> p_IK P = [] ->
  (forall TA, In TA (p_xt P) -> ext_okH segs GP hmH hmA hmR P (fun E => wins_client hmC E (p_W P)) TA) ->
  (forall S, In S (p_cs P) -> summ_okH segs GP hmH hmA hmC hmR S) ->
  In T0 (p_tm P) ->
  (forall E M rom ms, hmH M -> tm_okF segs T0 E M rom ms ->
     forall w, In w (p_CR P) -> forall z, fst (win_den E w) <= z < snd (win_den E w) -> hmA z) ->
  summ_okH segs GP hmH hmA hmC hmR (SUMX (p_G P) T0 (p_ex P) (p_W P) (p_A P) (p_PS P) false).
Proof.
  intros P IT fuel rr hints T0 Hc HIT HIK0 HEXT HCS Hin HL.
  apply summ_okH_of_F0.
  exact (summ_of_pcheckHF_CRL segs GP gfp gvc HGF HGV hmH hmA hmC hmR HMC_sub HMF fp0 P IT fuel rr hints T0 Hc HIT HIK0
           (fun TA H => ext_okH_F0 P _ TA (HEXT TA H)) (fun S H => summ_okH_F0 S (HCS S H)) Hin HL).
Qed.

End SoundC.

Lemma frame_ok_True : forall E W PS (M M' : word -> option byte), frame_ok (fun _ => True) E W PS M M' ->
  forall x : word, outside_wins E W (bv_unsigned x) -> M' x = M x.
Proof. intros E W [spe|] M M' F x Hx; cbn [frame_ok] in F; [exact (F x Hx (or_intror (or_intror I))) | exact (F x Hx)]. Qed.

(* [comment removed for export] *)
Section Classic.
Variable segs : list Segment.
Variable GP : nat -> list word -> (word -> option byte) -> Prop.
Variable gfp : nat -> list expr -> list SG.gwin.
Variable gvc : SG.vc -> bool.
Hypothesis HGF : SG.gp_frameP GP gfp.
Hypothesis HGV : forall c, gvc c = true -> SG.vc_holds segs GP c.

Theorem pcheck_sound : forall P IT fuel rr hints,
  pcheck segs gfp gvc P IT fuel rr hints = true -> itab_sound segs IT ->
  (forall TA, In TA (p_xt P) -> ext_ok segs GP P TA) ->
  (forall S, In S (p_cs P) -> summ_ok segs GP S) ->
  forall T E M rom ms, In T (p_tm P ++ p_xt P) -> aw_genuine E (p_A P) -> tm_okF segs T E M rom ms -> SG.gholds GP E M (t_ghost T) ->
  exists ms', ExecF.mstepsF segs (fp_of (p_A P) E) ms ms' /\ prun_post segs GP P E M rom ms'.
Proof.
  intros P IT fuel rr hints Hc HIT HEXT HCS T E M rom ms HinT HAG HT HG.
  unfold pcheck in Hc. apply andb_prop in Hc as [Hc HIK0].
  assert (HIK : p_IK P = []) by (destruct (p_IK P); [reflexivity | discriminate]).
  destruct (pcheck_soundH segs GP gfp gvc HGF HGV (fun _ => True) (fun _ => True) (fun _ _ => True) (fun _ => True)
              (fun _ _ _ _ _ _ _ => I) (fun _ _ _ _ _ _ _ _ => I) P IT fuel rr hints (fun _ => True) Hc HIT)
    with (T := T) (E := E) (M := M) (rom := rom) (ms := ms) as (ms' & Hms & X & E' & M' & HinX & HX & HGX & Hg & Hb & _ & FR).
  - intros TA HTA E0 M0 rom0 ms0 _ HAG0 _ _ HT0 HG0.
    destruct (HEXT TA HTA E0 M0 rom0 ms0 HAG0 HT0 HG0) as (ms1 & Hms1 & [(TB & E1 & M1 & HinB & HTB & HGB & Hg1 & Hb1 & FR1 & Hdec)|Hpost]).
    + exists ms1. split; [exact Hms1|]. left. exists TB, E1, M1. repeat (split; [assumption|]). split; [exact I|].
      split; [apply frame_ok_full; exact FR1 | exact Hdec].
    + exists ms1. split; [exact Hms1|]. right. destruct Hpost as (X & E1 & M1 & HinX & HX & HGX & Hg1 & Hb1 & FR1).
      exists X, E1, M1. repeat (split; [assumption|]). split; [exact I|]. apply frame_ok_full; exact FR1.
  - intros S HS E0 M0 rom0 ms0 _ HAG0 _ _ HT0 HG0.
    destruct (HCS S HS E0 M0 rom0 ms0 HAG0 HT0 HG0) as (ms1 & X & E1 & M1 & Hms1 & HinX & HX & HGX & Hg1 & Hb1 & FR1).
    exists ms1, X, E1, M1. repeat (split; [assumption|]). split; [exact I|]. apply frame_ok_full; exact FR1.
  - intros E1 E2 _ _ _. exact I.
  - intros E1 _. unfold wins_client. apply Forall_forall. intros w _. exact I.
  - intros E1 _ w _ z _. exact I.
  - intros E1 M1 _ _. rewrite HIK. constructor.
  - exact HinT.
  - exact I.
  - exact HAG.
  - exact I.
  - exact I.
  - exact HT.
  - exact HG.
  - exists ms'. split; [exact Hms|]. exists X, E', M'. repeat (split; [assumption|]). exact (frame_ok_True E (p_W P) (p_PS P) M M' FR).
Qed.

(* [comment removed for export] *)
Theorem summ_of_pcheck : forall P IT fuel rr hints T0,
  pcheck segs gfp gvc P IT fuel rr hints = true -> itab_sound segs IT ->
  (forall TA, In TA (p_xt P) -> ext_ok segs GP P TA) -> (forall S, In S (p_cs P) -> summ_ok segs GP S) ->
  In T0 (p_tm P) -> summ_ok segs GP (SUMA (p_G P) T0 (p_ex P) (p_W P) (p_A P)).
Proof.
  intros P IT fuel rr hints T0 Hc HIT HEXT HCS Hin E M rom ms HAG HT HG. cbn [sm_pre sm_post sm_G sm_W sm_A] in *.
  destruct (pcheck_sound P IT fuel rr hints Hc HIT HEXT HCS T0 E M rom ms ltac:(apply in_or_app; left; exact Hin) HAG HT HG)
    as (ms' & Hms & X & E' & M' & HinX & HX & HGX & Hg & Hb & FR).
  exists ms', X, E', M'. auto 8.
Qed.
End Classic.


(* [comment removed for export] *)
Lemma itab_ranges_sound : forall segs rs, itab_sound segs (APC.mk_itab_ranges segs rs).
Proof.
  intros segs rs. unfold APC.mk_itab_ranges.
  assert (H : forall rs0 t, itab_sound segs t -> itab_sound segs (APC.mk_itab_ranges_acc segs rs0 t)).
  { induction rs0 as [|[lo n] rs0 IH]; intros t Ht; cbn [APC.mk_itab_ranges_acc]; [exact Ht|]. apply IH. apply mk_itab_fuel_sound. exact Ht. }
  apply H. intros pc i. unfold itab_lookup. destruct pc; try discriminate. rewrite pt_get_leaf. discriminate.
Qed.
End SP.
