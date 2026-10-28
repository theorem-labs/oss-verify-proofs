From Stdlib Require Import ZArith NArith List Bool PArith.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocLayout Contract.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymCFG.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv TobjJV TobjJVA.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1 Require Import S_lo lo_defs lo4_meas lo_front lo_ret_defs.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1 Require lo4_bw lo4_bwda lo4_da0 lo4_da1 lo4_da2 lo4_fs lo4_hf lo4_hl.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1 Require lo4_hp lo4_hvn lo4_ir lo4_mf lo4_ml lo4_nt lo4_op1 lo4_op3.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1 Require lo4_op3b lo4_sdA1 lo4_sdA2 lo4_sdA3 lo4_sdA4 lo4_sdA5 lo4_sdA6 lo4_sdA7.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1 Require lo4_sdA8 lo4_sdB1 lo4_sdB2 lo4_sdB3 lo4_se1 lo4_se2 lo4_se3 lo4_se4.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1 Require lo4_se5 lo4_se6 lo4_se7 lo4_se8 lo4_se9 lo4_si lo4_vrA lo4_vrB.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module LoNodes.
Definition FUEL : nat := 8000%nat.
Definition heads : list Z := [0x13ed8; 0x13f70; 0x13fa8; 0x140f4; 0x146b8; 0x14934; 0x14a0c].
Definition entries : list Z :=
  [0x152cc; 0x167f8; 0x18298; 0x18350; 0x183d0; 0x18c6c; 0x18d80; 0x1914c; 0x19308; 0x19f68; 0x1a298;
   0x1a54c; 0x1a690; 0x1a6b4; 0x1a8fc; 0x1bd78; 0x1bf5c].
Definition cps : list Z := [ec_malloc EC_U; ec_free EC_U; LoU.pc_tail; LoU.pc_bd] ++ entries ++ heads.
Definition z0 : sv := SLit 0.
Definition ret_cuts : list aedesc :=
  [(lo4_bw.T_bw1, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_bw LD.z0)));
   (lo4_bwda.T_bwda1, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_bwda LD.z0)));
   (lo4_da0.T_da01, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_da LD.z0)));
   (lo4_da1.T_da11, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_da LD.z0)));
   (lo4_da2.T_da21, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_da LD.z0)));
   (lo4_fs.T_fs1, (lo4_fs.tvT_fs1, lo4_fs.amT_fs1), (LoMeas.rT, (LD.VLp LoMeas.kT_fs LD.z0)));
   (lo4_fs.T_fs2, (lo4_fs.tvT_fs2, lo4_fs.amT_fs2), (LoMeas.rT, (LD.VLp LoMeas.kT_fs LD.z0)));
   (lo4_fs.T_fs3, (lo4_fs.tvT_fs3, lo4_fs.amT_fs3), (LoMeas.rT, (LD.VLp LoMeas.kT_fs LD.z0)));
   (lo4_fs.T_fs4, (lo4_fs.tvT_fs4, lo4_fs.amT_fs4), (LoMeas.rT, (LD.VLp LoMeas.kT_fs LD.z0)));
   (lo4_hf.T_hf1, (lo4_hf.tvT_hf1, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_hf LD.z0)));
   (lo4_hf.T_hf2, (lo4_hf.tvT_hf2, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_hf LD.z0)));
   (lo4_hl.T_hl1, (lo4_hl.tvT_hl1, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_hl LD.z0)));
   (lo4_hp.T_hp1, (lo4_hp.tvT_hp1, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_hp LD.z0)));
   (lo4_hvn.T_hvn1, (lo4_hvn.tvT_hvn1, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_hvn LD.z0)));
   (lo4_hvn.T_hvn2, (lo4_hvn.tvT_hvn2, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_hvn LD.z0)));
   (lo4_hvn.T_hvn3, (lo4_hvn.tvT_hvn3, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_hvn LD.z0)));
   (lo4_ir.T_ir1, (lo4_ir.tvT_ir1, lo4_ir.amT_ir1), (LoMeas.rT, (LD.VLp LoMeas.kT_ir LD.z0)));
   (lo4_ir.T_ir2, (lo4_ir.tvT_ir2, lo4_ir.amT_ir2), (LoMeas.rT, (LD.VLp LoMeas.kT_ir LD.z0)));
   (lo4_mf.T_mf1, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_mf LD.z0)));
   (lo4_ml.T_ml1, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_ml LD.z0)));
   (lo4_nt.T_nt1, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_nt LD.z0)));
   (lo4_nt.T_nt2, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_nt LD.z0)));
   (lo4_op1.T_op11, (lo4_op1.tvT_op11, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_op1 LD.z0)));
   (lo4_op3.T_op31, (lo4_op3.tvT_op31, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_op3 LD.z0)));
   (lo4_op3b.T_op3b1, (lo4_op3b.tvT_op3b1, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_op3b LD.z0)));
   (lo4_sdA1.T_sdA11, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA1 LD.z0)));
   (lo4_sdA1.T_sdA12, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA1 LD.z0)));
   (lo4_sdA1.T_sdA13, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA1 LD.z0)));
   (lo4_sdA1.T_sdA14, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA1 LD.z0)));
   (lo4_sdA2.T_sdA21, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA2 LD.z0)));
   (lo4_sdA2.T_sdA22, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA2 LD.z0)));
   (lo4_sdA2.T_sdA23, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA2 LD.z0)));
   (lo4_sdA2.T_sdA24, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA2 LD.z0)));
   (lo4_sdA3.T_sdA31, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA3 LD.z0)));
   (lo4_sdA3.T_sdA32, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA3 LD.z0)));
   (lo4_sdA3.T_sdA33, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA3 LD.z0)));
   (lo4_sdA3.T_sdA34, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA3 LD.z0)));
   (lo4_sdA4.T_sdA41, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA4 LD.z0)));
   (lo4_sdA4.T_sdA42, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA4 LD.z0)));
   (lo4_sdA4.T_sdA43, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA4 LD.z0)));
   (lo4_sdA4.T_sdA44, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA4 LD.z0)));
   (lo4_sdA5.T_sdA51, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA5 LD.z0)));
   (lo4_sdA5.T_sdA52, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA5 LD.z0)));
   (lo4_sdA5.T_sdA53, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA5 LD.z0)));
   (lo4_sdA5.T_sdA54, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA5 LD.z0)));
   (lo4_sdA6.T_sdA61, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA6 LD.z0)));
   (lo4_sdA6.T_sdA62, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA6 LD.z0)));
   (lo4_sdA6.T_sdA63, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA6 LD.z0)));
   (lo4_sdA6.T_sdA64, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA6 LD.z0)));
   (lo4_sdA7.T_sdA71, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA7 LD.z0)));
   (lo4_sdA7.T_sdA72, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA7 LD.z0)));
   (lo4_sdA7.T_sdA73, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA7 LD.z0)));
   (lo4_sdA7.T_sdA74, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA7 LD.z0)));
   (lo4_sdA8.T_sdA81, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA8 LD.z0)));
   (lo4_sdA8.T_sdA82, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA8 LD.z0)));
   (lo4_sdA8.T_sdA83, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA8 LD.z0)));
   (lo4_sdA8.T_sdA84, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdA8 LD.z0)));
   (lo4_sdB1.T_sdB11, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdB1 LD.z0)));
   (lo4_sdB1.T_sdB12, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdB1 LD.z0)));
   (lo4_sdB1.T_sdB13, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdB1 LD.z0)));
   (lo4_sdB1.T_sdB14, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdB1 LD.z0)));
   (lo4_sdB2.T_sdB21, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdB2 LD.z0)));
   (lo4_sdB2.T_sdB22, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdB2 LD.z0)));
   (lo4_sdB2.T_sdB23, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdB2 LD.z0)));
   (lo4_sdB2.T_sdB24, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdB2 LD.z0)));
   (lo4_sdB3.T_sdB31, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdB3 LD.z0)));
   (lo4_sdB3.T_sdB32, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdB3 LD.z0)));
   (lo4_sdB3.T_sdB33, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdB3 LD.z0)));
   (lo4_sdB3.T_sdB34, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_sdB3 LD.z0)));
   (lo4_se1.T_se11, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_se1 LD.z0)));
   (lo4_se1.T_se12, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_se1 LD.z0)));
   (lo4_se1.T_se13, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_se1 LD.z0)));
   (lo4_se2.T_se21, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_se2 LD.z0)));
   (lo4_se2.T_se22, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_se2 LD.z0)));
   (lo4_se2.T_se23, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_se2 LD.z0)));
   (lo4_se3.T_se31, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_se3 LD.z0)));
   (lo4_se3.T_se32, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_se3 LD.z0)));
   (lo4_se3.T_se33, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_se3 LD.z0)));
   (lo4_se4.T_se41, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_se4 LD.z0)));
   (lo4_se4.T_se42, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_se4 LD.z0)));
   (lo4_se4.T_se43, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_se4 LD.z0)));
   (lo4_se5.T_se51, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_se5 LD.z0)));
   (lo4_se5.T_se52, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_se5 LD.z0)));
   (lo4_se5.T_se53, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_se5 LD.z0)));
   (lo4_se6.T_se61, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_se6 LD.z0)));
   (lo4_se6.T_se62, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_se6 LD.z0)));
   (lo4_se6.T_se63, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_se6 LD.z0)));
   (lo4_se7.T_se71, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_se7 LD.z0)));
   (lo4_se7.T_se72, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_se7 LD.z0)));
   (lo4_se7.T_se73, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_se7 LD.z0)));
   (lo4_se8.T_se81, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_se8 LD.z0)));
   (lo4_se8.T_se82, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_se8 LD.z0)));
   (lo4_se8.T_se83, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_se8 LD.z0)));
   (lo4_se9.T_se91, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_se9 LD.z0)));
   (lo4_se9.T_se92, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_se9 LD.z0)));
   (lo4_se9.T_se93, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_se9 LD.z0)));
   (lo4_si.T_si1, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_si LD.z0)));
   (lo4_si.T_si2, (LoU.tvL, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_si LD.z0)));
   (lo4_vrA.K_vrA1, (lo4_vrA.tvT_vrA1, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_vrA LD.z0)));
   (lo4_vrA.T_vrA2, (lo4_vrA.tvT_vrA2, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_vrA LD.z0)));
   (lo4_vrA.T_vrA3, (lo4_vrA.tvT_vrA3, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_vrA LD.z0)));
   (lo4_vrB.K_vrB1, (lo4_vrB.tvT_vrB1, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_vrB LD.z0)));
   (lo4_vrB.T_vrB2, (lo4_vrB.tvT_vrB2, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_vrB LD.z0)));
   (lo4_vrB.T_vrB3, (lo4_vrB.tvT_vrB3, LoU.amL), (LoMeas.rT, (LD.VLp LoMeas.kT_vrB LD.z0)))].
Definition cutsE : list aedesc := [LoFront.n_loop1; LoFront.n_skip; LoFront.n_tok] ++ LoRet.ret_nodes ++ ret_cuts.
Definition call_exits : list aedesc :=
  [(lo4_bw.E_bw, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_bw LD.z0)));
   (lo4_bwda.E_bwda, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_bwda LD.z0)));
   (lo4_da0.E_da0, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_da LD.z0)));
   (lo4_da1.E_da1, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_da LD.z0)));
   (lo4_da2.E_da2, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_da LD.z0)));
   (lo4_fs.E_fs, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_fs LD.z0)));
   (lo4_hf.E_hf, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_hf LD.z0)));
   (lo4_hl.E_hl, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_hl LD.z0)));
   (lo4_hp.E_hp, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_hp LD.z0)));
   (lo4_hvn.E_hvn, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_hvn LD.z0)));
   (lo4_ir.E_ir, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_ir LD.z0)));
   (lo4_mf.E_mf, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_mf LD.z0)));
   (lo4_ml.E_ml, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_ml LD.z0)));
   (lo4_nt.E_nt, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_nt LD.z0)));
   (lo4_op1.E_op1, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_op1 LD.z0)));
   (lo4_op3.E_op3, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_op3 LD.z0)));
   (lo4_op3b.E_op3b, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_op3b LD.z0)));
   (lo4_sdA1.E_sdA1, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_sdA1 LD.z0)));
   (lo4_sdA2.E_sdA2, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_sdA2 LD.z0)));
   (lo4_sdA3.E_sdA3, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_sdA3 LD.z0)));
   (lo4_sdA4.E_sdA4, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_sdA4 LD.z0)));
   (lo4_sdA5.E_sdA5, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_sdA5 LD.z0)));
   (lo4_sdA6.E_sdA6, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_sdA6 LD.z0)));
   (lo4_sdA7.E_sdA7, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_sdA7 LD.z0)));
   (lo4_sdA8.E_sdA8, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_sdA8 LD.z0)));
   (lo4_sdB1.E_sdB1, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_sdB1 LD.z0)));
   (lo4_sdB2.E_sdB2, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_sdB2 LD.z0)));
   (lo4_sdB3.E_sdB3, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_sdB3 LD.z0)));
   (lo4_se1.E_se1, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_se1 LD.z0)));
   (lo4_se2.E_se2, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_se2 LD.z0)));
   (lo4_se3.E_se3, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_se3 LD.z0)));
   (lo4_se4.E_se4, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_se4 LD.z0)));
   (lo4_se5.E_se5, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_se5 LD.z0)));
   (lo4_se6.E_se6, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_se6 LD.z0)));
   (lo4_se7.E_se7, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_se7 LD.z0)));
   (lo4_se8.E_se8, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_se8 LD.z0)));
   (lo4_se9.E_se9, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_se9 LD.z0)));
   (lo4_si.E_si, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_si LD.z0)));
   (lo4_vrA.E_vrA, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_vrA LD.z0)));
   (lo4_vrB.E_vrB, (LoU.tvL, LoU.amL), (LoMeas.rE, (LD.VLp LoMeas.kE_vrB LD.z0)))].
Definition exitsE : list aedesc :=
  call_exits ++ [((LoU.K_tail, (LoU.tvL, LoU.amL)), (0, z0)); ((LoU.K_bd, (LoU.tvL, LoU.amL)), (0, z0))].
Definition nodes : list aedesc := cutsE ++ exitsE.
End LoNodes.
