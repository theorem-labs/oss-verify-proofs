From Stdlib Require Import ZArith NArith List Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocLayout Contract.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymSummary.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv TobjJV TobjJVA.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1 Require Import S_lo.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module LoU.
Import LoAddrU.

Definition FR : Z := FRU.
Definition spo (k : Z) : sv := LD.spo k.
Definition sp1 : sv := sp1U.
Definition bofs : Z := 104 - FR.
Definition bx : sv := spo bofs.
Definition alo : Z := 1408 - FR.
Definition alx : sv := spo alo.
Definition dfo : Z := 1456 - FR.
Definition cxo : Z := 1600 - FR.
Definition cx : sv := spo cxo.
Definition loco : Z := 1616 - FR.
Definition savo : Z := 1736 - FR.
Definition lno : Z := 72 - FR.
Definition lnx : sv := spo lno.

Definition c8 (o : Z) (v : sv) : cell := LD.c8 o v.
Definition c4 (o : Z) (v : sv) : cell := LD.c4 o v.
Definition c1 (o : Z) (v : sv) : cell := LD.c1 o v.

Definition fp (lo hi : Z) (cells : list cell) : sobj := mkObj (SVar 10) (SLit lo) (SLit hi) cells DUnknown.
Definition O_spill (cells : list cell) : sobj := fp (- FR) lno cells.
Definition O_lnh (d c k : sv) : sobj :=
  mkObj lnx (SLit 0) (SLit 32) [c8 0 d; c8 8 c; c8 16 k; c8 24 (SLit 16)] DUnknown.

Definition piece (lo hi : Z) (cells : list cell) : sobj := mkObj bx (SLit lo) (SLit hi) cells DUnknown.
Definition P_alloc : sobj := piece 0 8 [c8 0 alx].
Definition P_hdr : sobj := piece 8 32 [c8 8 LD.xAR; c8 16 (SLit 0); c8 24 LD.vCFG].
Definition P_caps : sobj :=
  piece 32 96 [c8 32 (SLit LD.BIG); c8 40 (SLit LD.BIG); c8 48 (SLit LD.BIG); c8 56 (SLit (2 ^ 20));
               c8 64 (SLit (2 ^ 24)); c8 72 (SLit (2 ^ 24)); c8 80 (SLit (2 ^ 24)); c8 88 (SLit LD.BIG)].
Definition P_st (err line : sv) : sobj := piece 96 120 [c4 96 err; c8 104 line; c1 112 (SLit 1)].
Definition P_st0 (err : sv) : sobj := piece 96 120 [c4 96 err; c1 112 (SLit 1)].
Definition V (o : Z) (t : LD.T3) (e : Z) : sobj :=
  piece o (o + 32) [c8 o (LD.t_d t); c8 (o + 8) (LD.t_c t); c8 (o + 16) (LD.t_k t); c8 (o + 24) (SLit e)].
Definition Vd (o e : Z) : sobj := V o LD.zt e.
Definition Vz (o : Z) : sobj := piece o (o + 32) [c8 o (SLit 0); c8 (o + 8) (SLit 0); c8 (o + 16) (SLit 0)].
Definition P_cs : sobj := piece 312 320 [].
Definition P_cur (cn hp : sv) : sobj := piece 480 496 [c8 480 cn; c1 488 hp].
Definition P_ff : sobj := piece 880 936 [c1 885 (SLit 0)].
Definition P_mat : sobj := piece 1256 1304 [c1 1264 (SLit 0)].

Definition builder_head (err : sv) (st : sobj) (v : LD.vecs) : list sobj :=
  [P_alloc; P_hdr; P_caps; st;
   V 120 (LD.av3 (LD.v_av v)) 4; V 152 (LD.v_avw v) 4; V 184 (LD.v_avn v) 4; V 216 (LD.v_avt v) 4;
   V 248 (LD.v_avtw v) 4; V 280 (LD.v_acol v) 4; P_cs].
Definition builder_mid (cn hp : sv) (v : LD.vecs) : list sobj :=
  [V 448 (LD.v_sh v) 128; P_cur cn hp;
   V 496 (LD.v_mi v) 12; V 528 (LD.v_fv v) 4; V 560 (LD.v_mm v) 4; V 592 (LD.v_sg v) 4; V 624 (LD.v_li v) 12;
   V 656 (LD.v_lc v) 4; V 688 (LD.v_pi v) 12; V 720 (LD.v_co v) 12; V 752 (LD.v_rp v) 4; V 784 (LD.v_tr v) 4;
   V 816 (LD.v_ts v) 1].
Definition dlo : list Z := [848; 936; 968; 1000; 1032; 1064; 1096; 1128; 1160; 1192; 1224].
Definition dle : list Z := [4; 4; 12; 4; 4; 12; 12; 12; 56; 48; 128].
Definition builder_tail (mk : Z -> Z -> sobj) : list sobj :=
  [mk 848 4; P_ff; mk 936 4; mk 968 12; mk 1000 4; mk 1032 4; mk 1064 12; mk 1096 12; mk 1128 12; mk 1160 56;
   mk 1192 48; mk 1224 128; P_mat].
Definition builder (err line cn hp : sv) (v : LD.vecs) : list sobj :=
  builder_head err (P_st err line) v ++ [Vd 320 1168; Vd 352 8; Vd 384 4; Vd 416 24] ++ builder_mid cn hp v
  ++ builder_tail Vd.
Definition builder0 (err cn hp : sv) (v : LD.vecs) : list sobj :=
  builder_head err (P_st0 err) v ++ [Vd 320 1168; Vd 352 8; Vd 384 4; Vd 416 24] ++ builder_mid cn hp v
  ++ builder_tail Vd.
Definition builderT (err line cn hp : sv) : list sobj :=
  builder_head err (P_st err line) LD.vs0 ++ [Vz 320; Vz 352; Vz 384; Vz 416] ++ builder_mid cn hp LD.vs0
  ++ builder_tail (fun o _ => Vz o).

Definition O_alc : sobj := mkObj alx (SLit 0) (SLit 48) al_cellsU DUnknown.
Definition O_dfc : sobj := fp dfo cxo [].
Definition O_cp (cells : list cell) : sobj := mkObj cx (SLit 0) (SLit 8) cells DUnknown.
Definition O_ce (cells : list cell) : sobj := mkObj cx (SLit 8) (SLit 16) cells DUnknown.
Definition cpC (p : sv) : list cell := [c8 0 (LD.txt p)].
Definition ceC (e : sv) : list cell := [c8 8 (LD.txt e)].
Definition O_loc (cells : list cell) : sobj := fp loco savo cells.
Definition save_cells : list cell :=
  [c8 (-8) (SVar 11); c8 (-16) (SVar 28); c8 (-24) (SVar 29); c8 (-32) (SVar 38); c8 (-40) (SVar 39);
   c8 (-48) (SVar 40); c8 (-56) (SVar 41); c8 (-64) (SVar 42); c8 (-72) (SVar 43); c8 (-80) (SVar 44);
   c8 (-88) (SVar 45); c8 (-96) (SVar 46); c8 (-104) (SVar 47); c8 (-112) (SVar 68); c8 (-120) (SVar 69)].
Definition O_sav : sobj := fp savo 0 save_cells.
Definition O_D : sobj := O_DU.
Definition O_out (cells : list cell) (d : odefault) : sobj := LD.O_out cells d.
Definition O_text : sobj := LD.O_text.
Definition O_cfg : sobj := O_cfgU.
Definition O_ar (hd : sv) : sobj := O_arU hd.

Definition canonLs (spill : list cell) (line : option sv) (cp ce loc : list cell) (v : LD.vecs)
    (err cn hp hd : sv) : list sobj :=
  [O_spill spill; O_lnh LD.xLD LD.xLC LD.xLK]
  ++ (match line with Some ln => builder err ln cn hp v | None => builder0 err cn hp v end)
  ++ [O_alc; O_dfc; O_cp cp; O_ce ce; O_loc loc; O_sav; O_D; O_out [] DUnknown; O_text; O_cfg; O_ar hd]
  ++ LD.datas v ++ [LD.O_lines LD.xLD LD.xLC LD.xLK].

Definition canonT (ltail : list sobj) (hd : sv) (out : list cell) : list sobj :=
  [O_spill []; O_lnh LD.xLD LD.xLC LD.xLK] ++ builderT LD.pERR LD.pLINE LD.pCN LD.pHP
  ++ [O_alc; O_dfc; O_cp []; O_ce []; O_loc []; O_sav; O_D; O_out out DUnknown; O_text; O_cfg; O_ar hd] ++ ltail.

Definition base_facts : list sprop := base_factsU.
Definition loop_facts (v : LD.vecs) (cn hp hd : sv) : list sprop :=
  base_facts ++ LD.ar_facts ++ LD.hd_facts hd ++ LD.lines_facts LD.xLD LD.xLC LD.xLK ++ [SPUle LD.xLC LD.vL]
  ++ LD.misc_facts cn hp ++ LD.vecs_facts v.
Definition tail_facts : list sprop :=
  base_facts ++ LD.ar_facts ++ LD.hd_facts LD.pH ++ LD.lines_facts LD.xLD LD.xLC LD.xLK
  ++ LD.misc_facts LD.pCN LD.pHP.

Definition fkeep (r : nat) : bool := match r with 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 => true | _ => false end%nat.
Definition lo_fregs : list sv :=
  map (fun r => if fkeep r then SVar (Pos.of_nat (60 + r)) else LD.hf r) (seq 0 32).
Definition lfregs (l : list (nat * sv)) : list sv := setregs lo_fregs l.
Definition fs01 : list (nat * sv) := LD.fs01.

Definition vOUTn : sv := SAlu ALU_XOR LD.vOUT (SLit (-1)).
Definition cfg50 : sv := SAlu ALU_ADD LD.vCFG (SLit 50).
Definition fixregs : list (nat * sv) :=
  [(2%nat, sp1); (8%nat, LD.xAR); (21%nat, cfg50); (26%nat, vOUTn); (27%nat, LD.vOUT)].
Definition lregs (l : list (nat * sv)) : list sv :=
  setregs LD.lo_xregs (fixregs ++ [(5%nat, SLit 35); (6%nat, SLit 1); (11%nat, LD.vB); (18%nat, SLit 1);
                                   (19%nat, SLit 32); (20%nat, SLit 9)] ++ l).

Definition ltab_cells : list cell :=
  [c8 (-1824) (SAlu ALU_SUB (SLit 0) (SAlu ALU_ADD (SVar 10) (SLit (-200)))); c8 (-1840) (SLit 0);
   c8 (-1816) (SLit 1431655765); c8 (-1808) (SLit 18446744072277895851); c8 (-1832) (SLit 0);
   c8 (-1800) LD.vCFG; c8 (-1792) LD.vB].
Definition canonL := canonLs ltab_cells.

Definition tvL : list (sv * sv) := LD.tvL.
Definition amL : amode := LD.amL.

Definition LS (pc : Z) (regs : list (nat * sv)) (line : option sv) (cp ce loc : list cell) (facts : list sprop)
    : sstate :=
  mkSS pc (lregs regs) (lfregs fs01) FcsrFrm0 None
    (canonL line cp ce loc LD.vsP LD.pERR LD.pCN LD.pHP LD.pH)
    (facts ++ loop_facts LD.vsP LD.pCN LD.pHP LD.pH) LD.HNEXT false.

Definition cfg_spill : list cell := [c8 (56 - FR) LD.vCFG].

Definition LA (pc : Z) (regs : list (nat * sv)) (v : LD.vecs) (err : sv) (facts : list sprop) : sstate :=
  mkSS pc (setregs LD.lo_xregs (fixregs ++ regs)) lo_fregs FcsrFrm0 None
    (canonLs cfg_spill (Some LD.pLINE) [] [] [] v err LD.pCN LD.pHP LD.pH)
    (facts ++ loop_facts v LD.pCN LD.pHP LD.pH) LD.HNEXT false.

Definition LT (pc : Z) (regs : list (nat * sv)) (ltail : list sobj) (hd : sv) (out : list cell)
    (facts : list sprop) : sstate :=
  mkSS pc (setregs LD.lo_xregs (fixregs ++ regs)) lo_fregs FcsrFrm0 None (canonT ltail hd out)
    (facts ++ tail_facts) LD.HNEXT false.

Definition pc_loop : Z := 0x13ed8.
Definition pc_tail : Z := 0x14a3c.
Definition pc_bd : Z := 0x14cb0.

Definition K_loop : sstate := LS pc_loop [(9%nat, LD.pI)] (Some LD.pLINE) [] [] [] [SPUlt LD.pI LD.xLC].
Definition K_tail : sstate := LA pc_tail [] LD.vsP LD.pERR [].
Definition K_bd : sstate := LA pc_bd [(21%nat, SVar 299)] LD.vsP LD.pERR [].

Definition tv_ar : list (sv * sv) := LD.tv_ar.
Definition errnz : list sprop := LD.errnz.
Definition out_ok (ar : sv) : list cell := out_okU ar.

End LoU.
