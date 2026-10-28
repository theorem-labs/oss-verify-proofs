From Stdlib Require Import ZArith NArith List Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocLayout Contract.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame SymEntail SymCFG SymSummary.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv TobjJV TobjJVA ObjXform ObjUnbase TobjJVAx TobjJVAy TobjJVAz DrvGlue2.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1 Require Import S_lo S_u14e64 lo_defs lo_view.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require S_bli.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L4 Require Import ZeroKeep.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition cps_e : list Z :=
  [ec_malloc EC_U; BinitAddr.bi_entry; S_bli.bli_entry; LoU.pc_loop; LoU.pc_tail; LoU.pc_bd].
Definition run_e (n : nat) (S : sstate) : list leaf :=
  match sym_run segsU n cps_e S true with Some ls => ls | None => [] end.
Definition leaf_e (n : nat) (S : sstate) (k : nat) : sstate := nth k (map lf_state (run_e n S)) S.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition optSd (d : sstate) (x : option sstate) : sstate := match x with Some St => St | None => d end.

Definition E_m : sstate := Eval vm_compute in leaf_e 3000 Pre_lo_U 0.
Definition s_m : wsub := (15%positive, LD.vDp) :: infer_sub 10 E_m (Pre_malloc EC_U).
Definition R_m : list sobj := Eval vm_compute in optR (entails_fr E_m (Pre_malloc EC_U) s_m).
Definition T_mnull : sstate := Eval vm_compute in T_after E_m s_m R_m (L_malloc_null EC_U).
Definition T_mok0 : sstate := Eval vm_compute in T_after E_m s_m R_m (L_malloc_ok EC_U).
Definition vN : positive := 110.
Definition blkN : sv * sv := (SVar vN, SLit 64).
Definition tv_m : list (sv * sv) := [blkN].
Definition T_mok : sstate := add_facts (tv_facts blkN) T_mok0.

Definition X_bi_raw : sstate := leaf_e 8000 T_mok 0.

Definition bF : Z := -1752.
Definition bi_ns : list nstep :=
  [NX [XSplit 2 (SLit bF); XSplit 3 (SLit (bF + 1304))]; NU 3 bF;
   NX [XSplit 3 (SLit 120); XSplit 4 (SLit 312); XSplit 5 (SLit 320); XSplit 6 (SLit 480); XSplit 7 (SLit 496);
       XSplit 8 (SLit 880); XSplit 9 (SLit 900); XSplit 10 (SLit 908); XSplit 11 (SLit 936); XSplit 12 (SLit 1256)]].
Fixpoint zk_all (St : sstate) (l : list nat) : option sstate :=
  match l with
  | [] => Some St
  | i :: r => match zero_keep_at St i with Some St' => zk_all St' r | None => None end
  end.
Definition zk_idx : list nat := [3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 15]%nat.
Definition bi_prep (St : sstate) : option sstate :=
  match run_nsteps St bi_ns with Some S1 => zk_all S1 zk_idx | None => None end.

Definition E_bi : sstate := Eval vm_compute in optSd Pre_lo_U (bi_prep X_bi_raw).
Definition s_bi : wsub := infer_sub 10 E_bi Pre_bi.
Definition R_bi : list sobj := Eval vm_compute in optR (entails_fr E_bi Pre_bi s_bi).
Definition T_bi : sstate := Eval vm_compute in
  add_facts (ss_facts E_bi) (import_post s_bi (ss_next Pre_bi) P_bi (ss_next E_bi) R_bi).
Definition E_bli0 : sstate := Eval vm_compute in leaf_e 3000 T_bi 0.

Definition bl_ns : list nstep :=
  [NX [XSplit 5 (SLit (-96))]; NU 5 (-96); NX [XSplit 8 (SLit LoU.lno)]; NX [XSplit 16 (SLit (LoU.alo + 48))];
   NU 9 LoU.lno; NU 16 LoU.alo].
Definition E_bl1 : sstate := Eval vm_compute in optSd Pre_lo_U (run_nsteps E_bli0 bl_ns).
Definition dat0 : sobj := mkObj (SLit 0) (SLit 0) (S_bli.kb16 (SLit 0)) [] DUnknown.
Definition E_bl : sstate := set_objs E_bl1 (ss_objs E_bl1 ++ [dat0]).
Definition s_bl : wsub :=
  [(19%positive, SAlu ALU_ADD LD.vDp (SLit 96)); (15%positive, SLit 0); (16%positive, SLit 0); (17%positive, SLit 0)]
  ++ infer_sub 10 E_bl S_bli.Pre_bli0.
Definition R_bl : list sobj := Eval vm_compute in optR (entails_fr E_bl S_bli.Pre_bli0 s_bl).
Definition Tpost : sstate := Eval vm_compute in T_afterN NF E_bl s_bl R_bl S_bli.P_ret_darr.
Definition tvT : list (sv * sv) := Eval vm_compute in
  tv_m ++ import_tv (import_sub s_bl NF S_bli.P_ret_darr (ss_next E_bl)) S_bli.tvP.
Definition T_N : sstate := Eval vm_compute in LoV.renorm Tpost.
Definition conts_bl : list (list nstep * aedesc) :=
  [(LoV.renorm_prog Tpost, ((T_N, (tvT, ANone)), (60, SLit 0)))].

Definition T_Za : sstate := Eval vm_compute in optSd Pre_lo_U (zcells_at T_N 22 [(16, 8); (96, 4); (104, 8)]).
Definition T_Zb : sstate := Eval vm_compute in optSd Pre_lo_U (zcells_at T_Za 24 [(480, 8); (488, 1)]).
Definition T_Zc : sstate := Eval vm_compute in optSd Pre_lo_U (zcells_at T_Zb 25 [(885, 1)]).
Definition T_Z0 : sstate := Eval vm_compute in optSd Pre_lo_U (zcells_at T_Zc 27 [(1264, 1)]).
Definition fg_idx : list nat := [22; 23; 24; 25; 26; 27; 28]%nat.
Definition T_Z : sstate := Eval vm_compute in fold_left obj_forget fg_idx T_Z0.
Definition land_ns : list nstep :=
  [NX [XSelect [1;3;22;7;23;8;24;9;25;10;26;11;12;13;14;15;16;17;18;19;20;27;4;2;0;28;5;29;21;6]%nat;
       XSplit 23 (SLit (-256)); XSplit 24 (SLit (-240)); XSplit 25 (SLit (-120))];
   NU 24 LoU.cxo;
   NX [XSplit 24 (SLit 8); XMerge 9; XMerge 8;
       XSplit 7 (SLit 848); XSplit 7 (SLit 816); XSplit 7 (SLit 784); XSplit 7 (SLit 752); XSplit 7 (SLit 720);
       XSplit 7 (SLit 688); XSplit 7 (SLit 656); XSplit 7 (SLit 624); XSplit 7 (SLit 592); XSplit 7 (SLit 560);
       XSplit 7 (SLit 528);
       XSplit 5 (SLit 448); XSplit 5 (SLit 416); XSplit 5 (SLit 384); XSplit 5 (SLit 352);
       XSplit 3 (SLit 280); XSplit 3 (SLit 248); XSplit 3 (SLit 216); XSplit 3 (SLit 184); XSplit 3 (SLit 152);
       XSplit 2 (SLit 96); XSplit 2 (SLit 32); XSplit 2 (SLit 8)]].
Definition T_L : sstate := Eval vm_compute in optSd Pre_lo_U (run_nsteps T_Z land_ns).
Definition T_L2 : sstate :=
  mkSS (ss_pc T_L) (setregs (ss_regs T_L) [(26%nat, LoU.vOUTn)]) (ss_fregs T_L) (ss_fcsr T_L)
    (ss_resv T_L) (ss_objs T_L) (ss_facts T_L) (ss_next T_L) (ss_lenient T_L).

Definition kA_facts : list sprop :=
  [SPUle LD.pRET (SLit 1); SPUle LD.pCN (SLit 0); SPUle LD.pHP (SLit 0); SPUle LD.pH (SLit 0); SPUle LD.pERR (SLit 0)]
  ++ LD.zfacts LD.vsP ++ LoU.loop_facts LD.vsP LD.pCN LD.pHP LD.pH.
Definition spill_A : list cell := [LoU.c8 (-1800) LD.vCFG; LoU.c8 (-1792) LD.vB].
Definition objs_A : list sobj :=
  [LoU.O_spill spill_A; LoU.O_lnh LD.xLD LD.xLC LD.xLK]
  ++ LoU.builder LD.pERR LD.pLINE LD.pCN LD.pHP LD.vsP
  ++ [LoU.O_alc; LoU.O_dfc; LoU.O_cp []; LoU.O_ce []; LoU.O_loc []; LoU.O_sav; LoU.O_D; LoU.O_out [] DUnknown;
      LoU.O_text; LoU.O_cfg; LoU.O_ar LD.pH; LD.O_lines LD.xLD LD.xLC LD.xLK].
Definition pc_back : Z := 0x13e40.
Definition M_A : sstate :=
  mkSS S_bli.bli_ret (setregs LD.lo_xregs (LoU.fixregs ++ [(1%nat, SLit pc_back); (10%nat, LD.pRET)]))
    LoU.lo_fregs FcsrFrm0 None objs_A kA_facts LD.HNEXT false.
Definition K_A : sstate := set_objs M_A (objs_A ++ LD.datas LD.vsP).
Definition sA : wsub := map (fun n => (Pos.of_nat n, SLit 0)) (seq 110 54).
Definition nulls : list (sv * sv) := repeat (SLit 0, SLit 0) 18.
Definition tvA : list (sv * sv) := [(LD.xAR, SLit 64); (LD.xLD, LD.kb 16 LD.xLK)] ++ LD.tv_vecs LD.vsP.
