(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseSums_u5 ParseSums2_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmParse Require Import ParseSomeKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseSpecs_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5 ParseBridges3_u5 ParseBridges4_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParseW Require Import ParseSomeChk_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Import PSMC.
Module PSM2.
Definition cutn (i : nat) : CC.cutpoint := nth i G.CPS CA.dummy_cp.
(* [comment removed for export] *)
Fixpoint root (fuel : nat) (i : nat) : nat := match fuel with O => i | S f => match ret_src i with Some (i0, _, _) => root f i0 | None => i end end.
Definition in_loop (i : nat) : bool := let r := root 6 i in ((Nat.leb 2 r && Nat.leb r 6) || Nat.eqb r 8)%bool.      (* [comment removed for export] *)
Definition under0 (i : nat) : bool := Nat.eqb (root 6 i) 0.
(* [comment removed for export] *)
Definition reent_pc (i : nat) : Z :=
  match find (fun t => match t with CC.TOther pc => (Z.eqb pc L0PC || Z.eqb pc LPC || Z.eqb pc L2PC)%bool | _ => false end) (nth i G.TAGS []) with Some (CC.TOther pc) => pc | _ => 0 end.
(* [comment removed for export] *)
Definition pushed_of (j : nat) : expr :=
  match ret_src j with Some (i, k, _) => nth 11 (CA.ps_reglist (nth k (CC.cp_PSS (cutn i)) (SR.PS 0 [] [] []))) (ELit 0) | None => ELit 0 end.

(* [comment removed for export] *)
Definition c16 (o : Z) (cells : list kentry) : list kentry :=
  match CAX.cell_at cells Pb o 1, know_byte_lit PML.RSEGS cells Pb o, know_byte_lit PML.RSEGS cells Pb (o + 1) with
  | None, Some b0, Some b1 => KWord (SA Pb o) 1 (ELit b0) :: KWord (SA Pb (o + 1)) 1 (ELit b1) :: cells
  | _, _, _ => cells
  end.
Definition lcells (ps : SR.post_spec) : list kentry := c16 208 (c16 210 (SR.ps_cells ps)).
(* [comment removed for export] *)
Definition pview2x (cells : list kentry) (pe ce : expr) : option PB4.pvals2 :=
  match CAX.cell_at cells Pb 144 4, CAX.cell_at cells Pb 192 8, CAX.cell_at cells Pb 200 8, CAX.cell_at cells Pb 208 1, CAX.cell_at cells Pb 209 1,
        CAX.cell_at cells Pb 210 1, CAX.cell_at cells Pb 211 1, CAX.cell_at cells Pb 212 1, CAX.cell_at cells Pb 232 8,
        CAX.cell_at cells Pb 248 8, CAX.cell_at cells Pb 256 8, CAX.cell_at cells Pb 264 8 with
  | Some lvl, Some wend, Some wptr, Some st, Some sst, Some nst, Some more, Some done, Some se, Some csb, Some csend, Some cscend =>
      if (PB2.pconst_chk cells Pb && PB4.str_patx cells Pb 224 pe ce se 264 67108864)%bool
      then Some (PB4.PV2 lvl wend wptr st sst nst more done se csb csend cscend) else None
  | _, _, _, _, _, _, _, _, _, _, _, _ => None
  end.
(* [comment removed for export] *)
Definition vw (i : nat) : option (PB4.pvals2 * expr * expr) :=
  match nth i G.BLS [] with
  | (pe, ce) :: _ => match PB4.pview2 (CC.cp_know (cutn i)) Pb pe ce with Some pv => Some (pv, pe, ce) | None => None end
  | [] => None
  end.
(* [comment removed for export] *)
Definition blk_chk (i : nat) (pv : PB4.pvals2) : bool :=
  match nth i G.BLS [] with
  | [(pe, ce); (sbe, sce)] => (expr_eqb (PB4.pv_sb pv) sbe && expr_eqb (PB4.pv_scend pv) (PSU.eadd sbe sce))%bool
  | _ => false
  end.
Definition lview (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) : option (PB4.pvals2 * PB4.pvals2 * expr * expr) :=
  match vw i with
  | Some (pv, pe, ce) =>
      match pview2x (lcells ps) pe ce with
      | Some lv =>
          if (expr_eqb (PB4.pv_level pv) (PB4.pv_level lv) && expr_eqb (PB4.pv_wend pv) (PB4.pv_wend lv) && expr_eqb (PB4.pv_wend pv) WEND
              && expr_eqb (PB4.pv_sb pv) (PB4.pv_sb lv) && expr_eqb (PB4.pv_send pv) (PB4.pv_send lv) && expr_eqb (PB4.pv_scend pv) (PB4.pv_scend lv)
              && blk_chk i pv
              && forallb (APC.expr_vars_lt (CC.cp_nx c)) [PB4.pv_level pv; PB4.pv_wptr pv; PB4.pv_st pv; PB4.pv_sst pv; PB4.pv_nst pv; PB4.pv_more pv; PB4.pv_done pv; PB4.pv_size pv; PB4.pv_sb pv; PB4.pv_send pv; PB4.pv_scend pv; pe; ce]
              && PB.prove (lcells ps) (KRange (APC.esub WEND (PB4.pv_wptr lv)) 0 16384)
              && PB.has (CC.cp_know c) (KWr (SA Pb 0) (ELit 272)) && PB.has (CC.cp_know c) (KUnk (SA pe 0) ce))%bool
          then Some (pv, lv, pe, ce) else None
      | None => None
      end
  | None => None
  end.
Definition is_view_kind (i : nat) : bool := match kind_of i with KPt => false | _ => true end.
Definition lview_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool := if is_view_kind i then isSome (lview i c ps) else true.

(* [comment removed for export] *)
Definition flds (pv : PB4.pvals2) : list expr :=
  [PB4.pv_level pv; PB4.pv_wend pv; PB4.pv_wptr pv; PB4.pv_st pv; PB4.pv_sst pv; PB4.pv_nst pv; PB4.pv_more pv; PB4.pv_done pv; PB4.pv_size pv; PB4.pv_sb pv; PB4.pv_send pv; PB4.pv_scend pv].
Definition gview (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) (j : nat) (s : CC.subst) : option (PB4.pvals2 * PB4.pvals2 * expr * expr * PB4.pvals2) :=
  match lview i c ps, vw j with
  | Some (pv, lv, pe, ce), Some (pvj, pej, cej) =>
      if (forallb (fun ab : expr * expr => expr_eqb (CC.esubstL GT.NF s (fst ab)) (snd ab)) (combine (flds pvj) (flds lv))
          && expr_eqb (CC.esubstL GT.NF s pej) pe && expr_eqb (CC.esubstL GT.NF s cej) ce)%bool
      then Some (pv, lv, pe, ce, pvj) else None
  | _, _ => None
  end.
Definition gview_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with CC.TGoto j s => isSome (gview i c ps j s) | _ => true end.

(* [comment removed for export] *)
Definition rng_of (cells : list kentry) (e : expr) : Z * Z := match CX.range3 cells e with Some r => r | None => (0, 18446744073709551615) end.
Definition rng_is (cells : list kentry) (e : expr) (v : Z) : bool := match CX.range3 cells e with Some (lo, hi) => (Z.eqb lo v && Z.eqb hi v)%bool | None => false end.
Definition rng_in (cells : list kentry) (e : expr) (a b : Z) : bool := match CX.range3 cells e with Some (lo, hi) => (Z.leb a lo && Z.leb hi b)%bool | None => false end.
Definition lo_ge (cells : list kentry) (e : expr) (v : Z) : bool := match CX.range3 cells e with Some (lo, _) => Z.leb v lo | None => false end.
Definition ne_chk (cells : list kentry) (x : expr) (c : Z) : bool := PB.has cells (KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB x (ELit c)) (ELit 1)) 0 0).
(* [comment removed for export] *)
Definition fdelta (a b : expr) : option (option Z) := if expr_eqb a b then Some None else match b with ELit z => if ((0 <=? z) && (z <=? 255))%bool then Some (Some z) else None | _ => None end.
Record delta : Type := DL { d_st : option expr; d_sst : option Z; d_nst : option Z; d_more : option Z; d_done : option Z; d_clr : bool; d_adv : Z }.
Definition mkdelta (cells : list kentry) (pv lv : PB4.pvals2) : option delta :=
  match Some (if expr_eqb (PB4.pv_st pv) (PB4.pv_st lv) then None else Some (PB4.pv_st lv)), fdelta (PB4.pv_sst pv) (PB4.pv_sst lv), fdelta (PB4.pv_nst pv) (PB4.pv_nst lv), fdelta (PB4.pv_more pv) (PB4.pv_more lv),
        fdelta (PB4.pv_done pv) (PB4.pv_done lv), fdelta (PB4.pv_size pv) (PB4.pv_size lv) with
  | Some a, Some b, Some c, Some d, Some e, Some f =>
      let adv := if expr_eqb (PB4.pv_wptr pv) (PB4.pv_wptr lv) then Some 0 else if rng_is cells (APC.esub (PB4.pv_wptr lv) (PB4.pv_wptr pv)) 1 then Some 1 else None in
      match adv, f with
      | Some n, None => Some (DL a b c d e false n)
      | Some n, Some 0 => Some (DL a b c d e true n)
      | _, _ => None
      end
  | _, _, _, _, _, _ => None
  end.
(* [comment removed for export] *)
Definition handledb (x : Z) : bool := ((1 <=? x) && (x <=? 7) || (9 <=? x) && (x <=? 13) || (x =? 15) || (17 <=? x) && (x <=? 28))%bool.
Definition commentb (x : Z) : bool := ((3 <=? x) && (x <=? 6))%bool.
Definition ccrb (x : Z) : bool := (commentb x || (x =? 28))%bool.
Definition zseq (lo hi : Z) : list Z := map (fun n => lo + Z.of_nat n) (seq 0 (Z.to_nat (hi - lo + 1))).
(* [comment removed for export] *)
Definition step1 (lvl1 : bool) (s s' : Z) : bool :=
  ((commentb s && commentb s') || (negb (ccrb s) && negb (s =? 15) && handledb s' && negb (ccrb s') && negb (s' =? 15) && negb (s' =? 17) && (negb (s' =? 7) || lvl1) && negb ((9 <=? s') && (s' <=? 11))))%bool.      (* [comment removed for export] *)
Definition foot2 (c : CC.cutpoint) : bool := (Nat.leb (length (CC.cp_F c)) 2).     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition cur_cut (i : nat) : bool := match CC.cp_F (cutn i) with [_; _] => true | _ => false end.

Definition goto_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto j s =>
      match gview i c ps j s with
      | Some (pv, lv, pe, ce, pvj) =>
          let cells := SR.ps_cells ps in
          (implb (in_loop j) (in_loop i) && (if Nat.eqb i 0 then ne_chk cells (EVar 42) 2 else true) &&
           match (match kind_of i with KVis => KInv | ki => ki end), kind_of j with      (* [comment removed for export] *)
           | KInv, KInv =>
               (* [comment removed for export] *)
               (Nat.eqb i 0 && (rng_is cells (EVar 45) 0 || lo_ge cells (EVar 42) 29))
               || match mkdelta cells pv lv with
                  | Some d =>
                      let '(lo, hi) := rng_of cells (PB4.pv_st pv) in
                      ((match d_st d, d_more d with None, None => true | _, _ => false end || Nat.eqb i 0 || rng_is cells (PB4.pv_more pv) 1) && match d_more d with None | Some 1 => true | _ => false end
                       && (Nat.eqb j I_L0 || Nat.eqb j I_L || Nat.eqb j I_L2) && (if Nat.eqb i 0 then expr_eqb (PB4.pv_more pv) (EVar 45) else true) && match d_done d with None => true | _ => false end
                       && match d_sst d, d_nst d with None, None => true | _, _ => false end && negb (d_clr d)
                       && match d_st d with None => (foot2 c || negb ((lo <=? 17) && (17 <=? hi))) | Some (ELit s') => forallb (fun s => step1 (lo_ge cells (PB4.pv_level lv) 1) s s') (zseq lo hi) | _ => false end
                       && (if Nat.eqb j I_L then expr_eqb (CC.esubstL GT.NF s (EVar 54)) (ELit 3) else true)
                       && (if Nat.eqb j I_L0 then lo_ge cells (EVar 33) 1 else true))
                  | None => false
                  end
           | KSetEc, KErr =>
               match mkdelta cells pv lv with
               | Some d => (match d_st d, d_sst d, d_nst d, d_done d with None, None, None, None => true | _, _, _, _ => false end && negb (d_clr d) && Z.eqb (d_adv d) 0
                            && match d_more d with Some 0 => true | _ => false end && foot2 c)
               | None => false
               end
           | _, _ => false
           end)%bool
      | None => false
      end
  | _ => true
  end.

(* [comment removed for export] *)
Definition reg_eqb (r q : SGP.region) : bool := let '(b, lo, len) := r in let '(b', lo', len') := q in (expr_eqb b b' && Z.eqb lo lo' && expr_eqb len len')%bool.
Definition STKREG : SGP.region := (EVar 2, -12800, ELit 12800).      (* [comment removed for export] *)
Definition foot_chk (i : nat) (c : CC.cutpoint) : bool :=
  match CC.cp_F c with
  | [r0] => reg_eqb r0 STKREG
  | [r0; (b1, o1, n1)] => (reg_eqb r0 STKREG && expr_eqb b1 Pb && (((o1 =? 200) && expr_eqb n1 (ELit 8)) || ((o1 =? 156) && expr_eqb n1 (ELit 116))))%bool      (* [comment removed for export] *)
  | [r0; r1; (pb, po, pn)] =>      (* [comment removed for export] *)
      (reg_eqb r0 STKREG && reg_eqb r1 (Pb, 156, ELit 116) && (po =? 0) &&      (* [comment removed for export] *)
       match nth i G.BLS [] with (pe, ce) :: _ => (expr_eqb pb pe && expr_eqb pn ce)%bool | [] => false end)%bool
  | _ => false
  end.
(* [comment removed for export] *)
Definition blk2_chk (i : nat) (c : CC.cutpoint) : bool :=
  match nth i G.BLS [] with [(pe, ce); (sbe, sce)] => forallb (APC.expr_vars_lt (CC.cp_nx c)) [pe; ce; sbe; sce] | _ => false end.
Definition foot_all (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool := (foot_chk i c && blk2_chk i c)%bool.
(* [comment removed for export] *)
Definition ldelta (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) : option (PB4.pvals2 * PB4.pvals2 * expr * expr * delta) :=
  match lview i c ps with Some (pv, lv, pe, ce) => match mkdelta (SR.ps_cells ps) pv lv with Some d => Some (pv, lv, pe, ce, d) | None => None end | None => None end.
Definition delta_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool := if is_view_kind i then isSome (ldelta i c ps) else true.
End PSM2.
Lemma delta_ok : CH2.leaves_all PSMC.G.CPS PSMC.G.TAGS PSM2.delta_chk = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lview_ok : CH2.leaves_all PSMC.G.CPS PSMC.G.TAGS PSM2.lview_chk = true.
Proof. vm_compute. reflexivity. Qed.
Lemma goto_ok : CH2.leaves_all PSMC.G.CPS PSMC.G.TAGS PSM2.goto_chk = true.
Proof. vm_compute. reflexivity. Qed.
Lemma foot_ok : CH2.leaves_all PSMC.G.CPS PSMC.G.TAGS PSM2.foot_all = true.
Proof. vm_compute. reflexivity. Qed.
