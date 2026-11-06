(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan Pm4PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmEncSpecs PmLibSpecsW PmRef RelLeaf.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib CutHeap2 CutAutoX Pm4CutKit CutCertA CutHeapA CutAutoXA CutRtA CutShC.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Cut_ps_xasanw_T Cut_ps_xasanw_D Cut_ps_xasanw.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmParseSW Require Import UvZ.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGenW Require Import PswRefKitXA PswConvKitXA ParseStringChkXAW.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PSW.
Import PML PMR PSKW.
Module G := PSA.G.
Module GT := PSA.GT.
Definition cutn (i : nat) : CC.cutpoint := nth i G.CPS CA.dummy_cp.
Definition RETPC : Z := PSA.RETPC.
Definition PUSHB : Z := PSA.PC_PUSHB. Definition APPEND : Z := PSA.PC_APPEND. Definition SETEC : Z := PSA.PC_SETEC. Definition ESV : Z := PSA.PC_ESV.
Definition ATC : Z := PSA.PC_ATC. Definition CONVERT : Z := PSA.PC_CONVERT. Definition ERRH : Z := PSA.PC_ERRH. Definition SM : Z := PSA.PC_SM.

(* [comment removed for export] *)
(* [comment removed for export] *)
Import PCVK.
Definition NEG (a : expr) : expr := EMd M_MUL (ELit (-1)) a.
Definition BV : nat := 79.
Definition CUR0 : expr := ADD (V 11) (ADD (V 32) (NEG (V 51))).
Definition curform (c : Z) : expr := if c =? 0 then CUR0 else ADD CUR0 (ELit c).
Definition ENDE : expr := ADD (V 11) (V 32).
Definition RUNS : expr := ADD (V 11) (V 61).
Definition RUNL : expr := ADD (V 32) (ADD (NEG (V 51)) (NEG (V 61))).
Definition RUNL1 : expr := ADD RUNL (ELit 1).
Definition JM1 : expr := ADD (V 51) (ELit (-1)).
(* [comment removed for export] *)
Definition sboform (c : Z) : expr := if c =? 0 then ADD (V 32) (NEG (V 51)) else ADD (ADD (V 32) (NEG (V 51))) (ELit c).
(* [comment removed for export] *)
Definition PAIRX : expr := ADD (ORE (SRLE (MULE (ELit 18014398509481984) (EXT4 (V 57))) (ELit 44)) (ANDE (V 66) (ELit 1023))) (ELit 65536).
(* [comment removed for export] *)
Fixpoint cellb (cells : list kentry) (base : nat) (off : Z) (w : nat) : option expr :=
  match cells with
  | [] => None
  | KWord (SA (EVar b) o) w' v :: r => if (Nat.eqb b base && (o =? off) && Nat.eqb w' w)%bool then Some v else cellb r base off w
  | _ :: r => cellb r base off w
  end.
Definition cellv (cells : list kentry) (off : Z) (w : nat) : option expr := cellb cells 10 off w.
Definition CPX (i : nat) := cellv (CC.cp_know (cutn i)) 148 4.
Definition CP2X (i : nat) := cellv (CC.cp_know (cutn i)) 152 4.
Definition TAGX (i : nat) := cellv (CC.cp_know (cutn i)) 220 1.
Definition SIZX (i : nat) := cellv (CC.cp_know (cutn i)) 232 8.
Definition PTRX (i : nat) := cellv (CC.cp_know (cutn i)) 240 8.
(* [comment removed for export] *)
Definition A0X (i : nat) : expr := nth 10 (CC.cp_regs (cutn i)) (ELit 0).
Definition ECVX (i : nat) : expr := EVar (PSA.ecv i).
Definition oeqb (a : option expr) (e : expr) : bool := match a with Some x => expr_eqb x e | None => false end.
Definition sub (s : CC.subst) (n : nat) : expr := CC.slook s n.
(* [comment removed for export] *)
Definition parent (j : nat) : option (nat * nat) :=
  match find (fun r : nat * nat * nat * Z => let '(j', _, _, _) := r in Nat.eqb j j') G.RETS with Some (_, i, k, _) => Some (i, k) | None => None end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive ckind :=
  KEntry                       (* [comment removed for export] *)
| KStep (sst c : Z)            (* [comment removed for export] *)
| KText                        (* [comment removed for export] *)
| KAtc (sst : Z)               (* [comment removed for export] *)
| KConv (u8 : bool)            (* [comment removed for export] *)
| KRet4                        (* [comment removed for export] *)
| KSetEc (code : Z)            (* [comment removed for export] *)
| KEsv                         (* [comment removed for export] *)
| KRetx                        (* [comment removed for export] *)
| KBad.
Definition ckind_eqb (a b : ckind) : bool :=
  match a, b with
  | KEntry, KEntry | KText, KText | KRet4, KRet4 | KEsv, KEsv | KRetx, KRetx | KBad, KBad => true
  | KStep s1 c1, KStep s2 c2 => (s1 =? s2) && (c1 =? c2)
  | KAtc s1, KAtc s2 => s1 =? s2
  | KConv u1, KConv u2 => Bool.eqb u1 u2
  | KSetEc x, KSetEc y => x =? y
  | _, _ => false
  end%bool.
Lemma ckind_eqb_eq : forall a b, ckind_eqb a b = true -> a = b.
Proof.
  intros [] [] H; cbn in H; try discriminate H; try reflexivity.
  - apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1, H2. subst. reflexivity.
  - apply Z.eqb_eq in H. subst. reflexivity.
  - apply Bool.eqb_prop in H. subst. reflexivity.
  - apply Z.eqb_eq in H. subst. reflexivity.
Qed.
(* [comment removed for export] *)
Definition DSST (j : nat) : Z :=
  nth j [-1; 1; 1; 2; 2; 3; 3; 4; 4; 5; 5; 6; 6; 7; 7; 8; 8; 9; 9; 10; 10; 11; 11; 0; -1; -1; 0; 0; -1] (-1).
Definition decl_kind (j : nat) : ckind :=
  if Nat.eqb j 0 then KEntry
  else if Nat.leb j 23 then KStep (DSST j) 0
  else if Nat.eqb j 24 then KConv false else if Nat.eqb j 25 then KConv true
  else if (Nat.eqb j 26 || Nat.eqb j 27)%bool then KText
  else if Nat.eqb j 28 then KRetx else KBad.
Definition ck_c (k : ckind) : option Z := match k with KStep _ c => Some c | KText => Some 0 | _ => None end.
Definition ck_sst (k : ckind) : option Z := match k with KStep s _ => Some s | KText => Some 0 | _ => None end.
Inductive lres := LBad (why : nat) | LOk | LPost (k : ckind).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bytes256 : list Z := map Z.of_nat (seq 0 256).
Definition admlist (cells : list kentry) (bv : nat) : list Z := List.filter (fun b => RLF.byte_adm bv cells b) bytes256.
Definition allb (adm : list Z) (f : Z -> bool) : bool := forallb f adm.
Definition someb (adm : list Z) : bool := match adm with [] => false | _ => true end.
(* [comment removed for export] *)
Definition exh_fact (cells : list kentry) (c : Z) : bool :=
  hasr cells (V 51) c c || hasr cells (SLTUE (curform c) ENDE) 0 0.
Definition lt_fact (cells : list kentry) (c : Z) : bool := hasr cells (SLTUE (curform c) ENDE) 1 1.
(* [comment removed for export] *)
Definition jlt_fact (cells : list kentry) (c : Z) : bool :=
  lt_fact cells c || existsb (fun k => match k with KRange (EVar 51) lo _ => c + 1 <=? lo | _ => false end) cells.
(* [comment removed for export] *)
Definition hasb (cells : list kentry) (c : Z) : bool :=
  has cells (KWord (SA (curform c) 0) 1 (V BV)) && hasr cells (V BV) 0 255 && jlt_fact cells c.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition needs (var : nat) (s : Z) : bool := if Nat.eqb var 57 then (3 <=? s) && (s <=? 11) else (9 <=? s) && (s <=? 11).
Definition keep_ok (cur : option expr) (var : nat) (e : expr) (sstj : Z) : bool := (oeqb cur e || negb (needs var sstj))%bool.
(* [comment removed for export] *)
Definition upd_ok (cur : option expr) (var : nat) (u : cpu) (e : expr) (sstj : Z) : bool :=
  match u with
  | UKeep => keep_ok cur var e sstj
  | USet v => expr_eqb e (ELit v) || negb (needs var sstj)
  | UHex _ => false                                   (* [comment removed for export] *)
  end%bool.
Definition tag_ok (i : nat) (e : expr) : bool := (oeqb (TAGX i) e || expr_eqb e (ELit 0) || expr_eqb e (ELit 1))%bool.
Definition tagc_ok (i : nat) (cells : list kentry) : bool := match cellv cells 220 1 with Some e => tag_ok i e | None => false end.
Definition buf_ok (i : nat) (esz eptr : expr) : bool := (oeqb (SIZX i) esz && oeqb (PTRX i) eptr)%bool.
(* [comment removed for export] *)
Definition cparg (i : nat) (sst : Z) : option expr :=
  if (sst =? SS_U1) || (sst =? SS_U5) then Some (ELit 0)
  else if (SS_U2 <=? sst) && (sst <=? SS_U4) then option_map EXT4 (CPX i)            (* [comment removed for export] *)
  else if (SS_U6 <=? sst) && (sst <=? SS_U8) then option_map EXT4 (CP2X i) else None.
(* [comment removed for export] *)
Definition hexst (sst : Z) : bool := ((SS_U1 <=? sst) && (sst <=? SS_U4)) || ((SS_U5 <=? sst) && (sst <=? SS_U8)).

(* [comment removed for export] *)
Definition oeq (a b : option expr) : bool := match a, b with Some x, Some y => expr_eqb x y | None, None => true | _, _ => false end.
Definition same_cells (i j : nat) : bool := (oeq (CPX i) (CPX j) && oeq (CP2X i) (CP2X j) && oeq (SIZX i) (SIZX j) && oeq (PTRX i) (PTRX j) && oeq (TAGX i) (TAGX j))%bool.
(* [comment removed for export] *)
Definition vlt (n : nat) (o : option expr) : bool := match o with Some e => APC.expr_vars_lt n e | None => true end.
Definition lowcells (i : nat) : bool := (vlt 62 (CPX i) && vlt 62 (CP2X i) && vlt 62 (SIZX i) && vlt 62 (PTRX i) && vlt 62 (TAGX i))%bool.
Section Leaf.
Variable K : nat -> ckind.
(* [comment removed for export] *)
Definition goto_step_chk (i : nat) (sst c : Z) (istext : bool) (cells : list kentry) (adm : list Z) (j : nat) (s : CC.subst) : lres :=
  let dj := if expr_eqb (sub s 51) JM1 then Some 1 else if expr_eqb (sub s 51) (V 51) then Some 0 else None in
  match K j with
  | KRetx =>
      (* [comment removed for export] *)
      if negb istext && exh_fact cells c && oeqb (cellv cells 209 1) (ELit sst) && expr_eqb (sub s 78) (curform c) &&
         keep_ok (CPX i) 57 (sub s 86) sst && keep_ok (CP2X i) 58 (sub s 87) sst &&
         match cellv cells 220 1 with Some e => tag_ok i e | None => false end &&
         (oeq (cellv cells 148 4) (CPX i) || negb (needs 57 sst)) && (oeq (cellv cells 152 4) (CP2X i) || negb (needs 58 sst))      (* [comment removed for export] *)
      then LOk else LBad 6
  | _ =>
  match dj, ck_c (K j), ck_sst (K j) with
  | Some dj, Some cj, Some sstj =>
      let delta := cj + dj - c in
      let frame := tag_ok i (sub s 59) && buf_ok i (sub s 53) (sub s 54) &&
                   match K j with
                   | KText => if istext then expr_eqb (sub s 61) (V 61) else expr_eqb (sub s 61) (sboform c)
                   | KStep _ _ => true | _ => false end in
      if negb frame then LBad 1
      else if delta =? 0 then
        (if (sstj =? sst) && keep_ok (CPX i) 57 (sub s 57) sstj && keep_ok (CP2X i) 58 (sub s 58) sstj && negb istext then LOk else LBad 2)
      else if delta =? 1 then
        let tk := match K j with KText => true | _ => false end in      (* [comment removed for export] *)
        if Bool.eqb istext tk && someb adm && hasb cells c &&
           allb adm (fun b =>
             match sdesc sst b with
             | SGo s' u1 u2 out => (s' =? sstj) && Nat.eqb (length out) (if istext then 1%nat else 0%nat) &&
                                   upd_ok (CPX i) 57 u1 (sub s 57) sstj && upd_ok (CP2X i) 58 u2 (sub s 58) sstj
             | _ => false
             end)
        then LOk else LBad 3
      else LBad 4
  | _, _, _ => LBad 5
  end end%bool.
(* [comment removed for export] *)
Definition goto_atc_chk (i : nat) (sst : Z) (cells : list kentry) (adm : list Z) (j : nat) (s : CC.subst) : lres :=
  let a0 := A0X i in
  let frame := (tag_ok i (sub s 59) && buf_ok i (sub s 53) (sub s 54))%bool in
  match K j with
  | KRetx =>      (* [comment removed for export] *)
      if hasr cells (ECVX i) 1 31 && oeqb (cellv cells 209 1) (ELit sst) && expr_eqb (sub s 78) (curform 0) && hasb cells 0 then LOk else LBad 10
  | KStep sstj 0 =>      (* [comment removed for export] *)
      if frame && hasr cells (ECVX i) 0 0 && expr_eqb (sub s 51) JM1 && hasb cells 0 &&
         allb adm (fun b => match hexval b with None => true | Some _ =>      (* [comment removed for export] *)
                           match sdesc sst b with
                           | SGo s' u1 u2 [] =>
                               (s' =? sstj) &&
                               match u1 with UKeep => keep_ok (CPX i) 57 (sub s 57) sstj | _ => expr_eqb (sub s 57) a0 end &&
                               match u2 with UKeep => keep_ok (CP2X i) 58 (sub s 58) sstj | _ => expr_eqb (sub s 58) a0 end
                           | SU4 _ => (* [comment removed for export] *)
                               (sstj =? SS_SP1) && match lit cells (fe_hs a0) with Some true => true | _ => false end &&
                               expr_eqb (sub s 57) a0 && keep_ok (CP2X i) 58 (sub s 58) sstj
                           | _ => false end end)
      then LOk else LBad 11
  | KConv false =>       (* [comment removed for export] *)
      if frame && (sst =? SS_U4) && hasr cells (ECVX i) 0 0 && expr_eqb (sub s 51) (V 51) && hasb cells 0 &&
         match lit cells (fe_hs a0) with Some false => true | _ => false end &&
         expr_eqb (sub s 57) a0 && oeqb (CPX j) (V 57)
      then LOk else LBad 12
  | KConv true =>        (* [comment removed for export] *)
      if frame && (sst =? SS_U8) && hasr cells (ECVX i) 0 0 && expr_eqb (sub s 51) (V 51) && hasb cells 0 &&
         oeqb (CPX i) (sub s 57) && expr_eqb (sub s 58) a0 && expr_eqb (sub s 66) a0 && oeqb (CPX j) (V 57) && oeqb (CP2X j) (V 58)
      then LOk else LBad 13
  | _ => LBad 14
  end%bool.
(* [comment removed for export] *)
Definition goto_other_chk (i : nat) (ki : ckind) (cells : list kentry) (adm : list Z) (j : nat) (s : CC.subst) : lres :=
  match ki with
  | KEntry =>      (* [comment removed for export] *)
      match K j with
      | KStep sstj 0 =>
          if hasr cells (V 41) sstj sstj && expr_eqb (sub s 51) (V 32) && expr_eqb (sub s 57) (V 44) && expr_eqb (sub s 58) (V 45) &&
             expr_eqb (sub s 59) (V 48) && expr_eqb (sub s 53) (V 35) && expr_eqb (sub s 54) (V 36) && Nat.leb 1 j && Nat.leb j 23 then LOk else LBad 20
      | KRetx =>      (* [comment removed for export] *)
          if hasr cells (V 41) 1 1 && oeqb (cellv cells 209 1) (ELit 1) && hasr cells (SLTUE (V 11) ENDE) 0 0 && expr_eqb (sub s 78) (V 11) &&
             match cellv cells 220 1 with Some e => expr_eqb e (V 48) | None => false end then LOk else LBad 21
      | _ => LBad 22
      end
  | KRet4 => match K j with KRetx => if expr_eqb (sub s 78) (curform 1) && oeqb (cellv cells 209 1) (ELit 0) && tagc_ok i cells then LOk else LBad 23 | _ => LBad 24 end      (* [comment removed for export] *)
  | KSetEc code => match K j with KRetx => LOk | _ => LBad 25 end
  | KEsv => match K j with KRetx => if (hasr cells (ECVX i) 0 0 && expr_eqb (sub s 78) (curform 1)) || hasr cells (ECVX i) 1 31 then LOk else LBad 26 | _ => LBad 28 end      (* [comment removed for export] *)
  | _ => LBad 27
  end%bool.
(* [comment removed for export] *)
Definition atc_chk (i : nat) (ki : ckind) (cells : list kentry) (a1 a2 : expr) : lres :=
  match ki with
  | KStep sst 0 => if hexst sst && hasb cells 0 && expr_eqb a2 (V BV) && oeqb (cparg i sst) a1 then LPost (KAtc sst) else LBad 30
  | _ => LBad 31
  end%bool.
(* [comment removed for export] *)
Definition push_chk (i : nat) (ki : ckind) (cells : list kentry) (adm : list Z) (a1 : expr) : lres :=
  match ki with
  | KStep sst c =>
      if (sst =? SS_ESC) && someb adm && hasb cells c && tagc_ok i cells &&
         allb adm (fun b => match sdesc sst b with SGo s' UKeep UKeep [o] => (s' =? SS_TEXT) && expr_eqb a1 (ELit o) | _ => false end)
      then LPost (KStep SS_TEXT (c + 1)) else LBad 32
  | _ => LBad 33
  end%bool.
(* [comment removed for export] *)
Definition app_chk (i : nat) (ki : ckind) (cells : list kentry) (adm : list Z) (a1 a2 : expr) : lres :=
  match ki with
  | KText =>
      if negb (expr_eqb a1 RUNS && tagc_ok i cells) then LBad 40 else
      if expr_eqb a2 RUNL then
        (if someb adm && hasb cells 0 && allb adm (fun b => b =? 92) then LPost (KStep SS_ESC 1)
         else if someb adm && hasb cells 0 && allb adm (fun b => b =? 34) then LPost (KStep SS_TEXT 0)
         else LBad 41)
      else if expr_eqb a2 RUNL1 then
        (if someb adm && hasb cells 0 && allb adm (fun b => match sdesc SS_TEXT b with SGo s' UKeep UKeep [o] => (s' =? SS_TEXT) && (o =? b) | _ => false end) && exh_fact cells 1
         then LPost (KStep SS_TEXT 1) else LBad 42)
      else LBad 43
  | KStep sst c => if (sst =? SS_TEXT) && expr_eqb a2 (ELit 0) && exh_fact cells c && expr_eqb a1 (curform c) && tagc_ok i cells then LPost (KStep SS_TEXT c) else LBad 44
  | _ => LBad 45
  end%bool.
(* [comment removed for export] *)
Definition setec_chk (i : nat) (ki : ckind) (cells : list kentry) (adm : list Z) (a1 : expr) : lres :=
  match ki, a1 with
  | KStep sst c, ELit code =>
      if negb (code =? 0) && someb adm && hasb cells c && allb adm (fun b => match sdesc sst b with SErr e => e =? code | _ => false end) then LPost (KSetEc code) else LBad 50
  | KText, ELit code =>
      if negb (code =? 0) && someb adm && hasb cells 0 && allb adm (fun b => match sdesc SS_TEXT b with SErr e => e =? code | _ => false end) then LPost (KSetEc code) else LBad 51
  | _, _ => LBad 52
  end%bool.
(* [comment removed for export] *)
Definition errh_chk (i : nat) (ki : ckind) : lres :=
  match ki with KStep _ _ | KText => if lowcells i then LPost ki else LBad 56 | _ => LBad 55 end.
(* [comment removed for export] *)
Definition esv_chk (i : nat) (ki : ckind) (cells : list kentry) (adm : list Z) (a1 a2 : expr) : lres :=
  match ki with
  | KText => if someb adm && hasb cells 0 && allb adm (fun b => b =? 34) && expr_eqb a1 RUNS && expr_eqb a2 RUNL && hasr cells (V 53) 0 0 && tagc_ok i cells && oeqb (SIZX i) (V 53) then LPost KEsv else LBad 60
  | KStep sst c => if (sst =? SS_TEXT) && (c =? 0) && someb adm && hasb cells c && allb adm (fun b => b =? 34) && oeqb (PTRX i) a1 && oeqb (SIZX i) a2 && tagc_ok i cells then LPost KEsv else LBad 61
  | _ => LBad 62
  end%bool.
(* [comment removed for export] *)
Definition conv_chk (i : nat) (ki : ckind) (cells : list kentry) (a0 a1 a2 : expr) : lres :=
  match ki with
  | KConv u8 =>
      if expr_eqb a0 (if u8 then ADD (V 55) (ELit 112) else ADD (V 10) (ELit 148)) && expr_eqb a1 (ELit 1) && expr_eqb a2 (ADD (V 10) (ELit 224)) && tagc_ok i cells &&
         (if u8 then oeqb (cellb cells 55 112 4) PAIRX && oeqb (CPX i) (V 57) else oeqb (cellv cells 148 4) (V 57) && oeqb (CPX i) (V 57))      (* [comment removed for export] *)
      then LPost (if u8 then KStep SS_TEXT 1 else KRet4) else LBad 65
  | _ => LBad 66
  end.
Definition leaf_eval (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : lres :=
  let cells := SR.ps_cells ps in let ki := K i in let adm := admlist cells BV in
  match t with
  | CC.TGoto j s =>
      match ki with
      | KStep sst c => goto_step_chk i sst c false cells adm j s
      | KText => goto_step_chk i 0 0 true cells adm j s
      | KAtc sst => goto_atc_chk i sst cells adm j s
      | _ => goto_other_chk i ki cells adm j s
      end
  | CC.TOther pc =>
      if pc =? RETPC then match ki with KRetx => LOk | _ => LBad 70 end
      else if pc =? SM then match ki with KEntry => LPost KEntry | _ => LBad 71 end
      else if pc =? ATC then atc_chk i ki cells (PSA.reg_of ps 11) (PSA.reg_of ps 12)
      else if pc =? PUSHB then push_chk i ki cells adm (PSA.reg_of ps 11)
      else if pc =? APPEND then app_chk i ki cells adm (PSA.reg_of ps 11) (PSA.reg_of ps 12)
      else if pc =? SETEC then setec_chk i ki cells adm (PSA.reg_of ps 11)
      else if pc =? ERRH then errh_chk i ki
      else if pc =? ESV then esv_chk i ki cells adm (PSA.reg_of ps 11) (PSA.reg_of ps 12)
      else if pc =? CONVERT then conv_chk i ki cells (PSA.reg_of ps 10) (PSA.reg_of ps 11) (PSA.reg_of ps 12)
      else (* [comment removed for export] *)
        match CSLR.find_row PSA.ROWS i (SR.ps_pc ps) with Some r => if ckind_eqb (K (CSLR.r_j r)) ki && same_cells i (CSLR.r_j r) && lowcells i then LOk else LBad 72 | None => LBad 73 end
  end.
End Leaf.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition post_of (K : nat -> ckind) (i k : nat) : ckind :=
  let c := cutn i in
  match nth_error (CC.cp_PSS c) k, nth_error (nth i G.TAGS []) k with
  | Some ps, Some t => match leaf_eval K i c k ps t with LPost kd => kd | _ => KBad end
  | _, _ => KBad
  end.
Fixpoint build (n : nat) (acc : list ckind) : list ckind :=
  match n with
  | O => acc
  | S n' => let j := length acc in
            let kd := if Nat.leb j 28 then decl_kind j else match parent j with Some (i, k) => post_of (fun x => nth x acc KBad) i k | None => KBad end in
            build n' (acc ++ [kd])
  end.
(* [comment removed for export] *)
Definition KTAB : list ckind := Eval vm_compute in build 79 [].
Definition KD (i : nat) : ckind := nth i KTAB KBad.
Definition wl_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match leaf_eval KD i c k ps t with
  | LBad _ => false
  | LOk => true
  | LPost kd => match t with CC.TOther _ => match CH2.ret_of G.RETS i k with Some j => ckind_eqb (KD j) kd | None => false end | _ => false end
  end.
(* [comment removed for export] *)
Definition fails (lo n : nat) : list (nat * nat * lres) :=
  flat_map (fun i => let c := cutn i in let tg := nth i G.TAGS [] in
     flat_map (fun k => let ps := nth k (CC.cp_PSS c) (SR.PS 0 [] [] []) in let t := nth k tg (CC.TOther 0) in
                        if wl_chk i c k ps t then [] else [(i, k, leaf_eval KD i c k ps t)]) (seq 0 (length tg))) (seq lo n).
Lemma KTAB_ok : build (length G.CPS) [] = KTAB.
Proof. vm_compute. reflexivity. Qed.
Lemma KTAB_nobad : forallb (fun k => negb (ckind_eqb k KBad)) KTAB = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wl_ok : CH2.leaves_all G.CPS G.TAGS wl_chk = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition size_of (cells : list kentry) : expr := match cellv cells 232 8 with Some e => e | None => ELit 0 end.
Definition retw_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => true
  | CC.TOther pc =>
      match CH2.ret_of G.RETS i k, (CH2.ret_of G.RETS i k) with
      | None, _ => (pc =? RETPC) || negb ((pc =? PUSHB) || (pc =? APPEND) || (pc =? CONVERT) || (pc =? ATC) || (pc =? ERRH) || (pc =? SETEC) || (pc =? ESV) || (pc =? SM))
      | Some j, _ =>
          let cells := SR.ps_cells ps in let cj := cutn j in
          let kept := (oeq (CPX j) (cellv cells 148 4) && oeq (CP2X j) (cellv cells 152 4) && oeq (TAGX j) (cellv cells 220 1) && oeqb (cellv cells 232 8) (size_of (CC.cp_know c)))%bool in
          if pc =? PUSHB then let g := PSA.gof ps i c cj 4368 2 in kept && oeqb (SIZX j) (APC.eaddz (size_of cells) 1) && oeqb (PTRX j) (EVar g)
          else if pc =? APPEND then let g := PSA.gof ps i c cj 4368 2 in kept && oeqb (SIZX j) (APC.eadd (size_of cells) (PSA.reg_of ps 12)) && oeqb (PTRX j) (EVar g)
          else if pc =? CONVERT then let g := PSA.gof ps i c cj 4496 3 in oeqb (SIZX j) (EVar (g + 2)%nat) && oeqb (PTRX j) (EVar g) && oeqb (cellv cells 232 8) (size_of (CC.cp_know c)) && oeq (TAGX j) (cellv cells 220 1) && oeq (CPX j) (cellv cells 148 4)
          else if pc =? ATC then let g := PSA.gof ps i c cj 1120 1 in same_cells i j && expr_eqb (ECVX j) (EVar g) && expr_eqb (A0X j) (EVar (g + 5)%nat) && Nat.ltb BV g
          else if (pc =? ERRH) || (pc =? SETEC) then same_cells i j && kept && oeq (PTRX j) (cellv cells 240 8)
          else if pc =? ESV then Nat.eqb (PSA.ecv j) (PSA.gof ps i c cj 16544 7)
          else if pc =? SM then Nat.eqb j 29
          else false
      end
  end%bool.
Lemma retw_ok : CH2.leaves_all G.CPS G.TAGS retw_chk = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bufkind (k : ckind) : bool := match k with KEntry | KStep _ _ | KText | KAtc _ | KConv _ | KRet4 => true | _ => false end.
Definition cut_chk (i : nat) : bool :=
  let n := CC.cp_nx (cutn i) in
  (vlt n (CPX i) && vlt n (CP2X i) && vlt n (SIZX i) && vlt n (PTRX i) && vlt n (TAGX i) && (Nat.ltb 27 i || lowcells i) &&
   match KD i with KEntry => true | KAtc _ => Nat.leb 80 n && APC.expr_vars_lt n (A0X i) && APC.expr_vars_lt n (ECVX i) | KConv _ => Nat.leb 79 n | _ => Nat.leb 62 n end &&
   (negb (bufkind (KD i)) || (oeqb (PTRX i) (fst (PSA.blk0 i)) && oeqb (SIZX i) (PSA.szc (cutn i)) && PSA.szok (cutn i) &&
                             match TAGX i with Some _ => true | None => false end && match CPX i with Some _ => true | None => false end && match CP2X i with Some _ => true | None => false end)))%bool.
Lemma cut_ok : forallb cut_chk (seq 0 79) = true.
Proof. vm_compute. reflexivity. Qed.
End PSW.
