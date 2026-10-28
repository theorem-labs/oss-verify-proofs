From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymCFG.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv RingBuf RingCfg.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L7 Require Import S_r2 r2_cuts r2_ex_base r2_ex_defs.
Import ListNotations.
Open Scope Z_scope.

(* Forced-clip region of r2's complete side (ubsan 0x1f494 .. 0x1f568), P's K_g / K_gb / K_g2 / X_g2.
   The clipped vertex is v192 = NXT cur; v194 = PRV v192 and v198 = NXT v192 are the ring neighbours
   loaded at 0x1f4e0 / 0x1f4e4; v199 is the dead miss counter. *)
Module R2G.
Import R2C R2X R2E.

Definition kg_x : list (nat * sv) :=
  [(10%nat, vPRV); (12%nat, vNXT); (14%nat, V 199); (16%nat, V 192); (17%nat, vP2D); (21%nat, V 192)].
Definition kg_facts : list sprop := km_facts ++ mg_facts ++ [SPUlt (V 192) vN].
Definition K_g : sstate := cut 0x1f494 (km_regs ++ kg_x) [] objsKe kg_facts.
Definition gf_g : list sprop := [SPUlt (NXT (V 192)) vN; SPUlt (PRV (V 192)) vN].

(* after both neighbour loads, before the triangle and ring stores *)
Definition kgb_x : list (nat * sv) :=
  kg_x ++ [(5%nat, SAlu ALU_ADD vOUT (SAlu ALU_SLL (k3 (V 189)) (SLit 2))); (11%nat, SAlu ALU_ADD vPRV (IX4 (V 192)));
           (13%nat, SAlu ALU_XOR vPRV M1); (14%nat, SAlu ALU_XOR vNXT M1); (15%nat, V 198); (16%nat, V 194);
           (17%nat, k3 (V 189))].
Definition kgb_facts : list sprop := kg_facts ++ [SPUlt (V 194) vN; SPUlt (V 198) vN].
Definition K_gb : sstate := cut 0x1f4e8 (km_regs ++ kgb_x) [] objsKe kgb_facts.

(* after the stores: triangle (v194, v192, v198) written, NXT v194 := v198, PRV v198 := v194, cur := v198 *)
Definition L_g2 : Z := 0x1f568.
Definition xg2_x : list (nat * sv) :=
  kgb_x ++ [(5%nat, SLit 0); (6%nat, SLit 0); (10%nat, SAlu ALU_ADD vPRV (IX4 (V 198))); (11%nat, V 194); (12%nat, SLit 0);
            (14%nat, SLit 0); (15%nat, IX4 (V 198)); (16%nat, IX4 (V 194));
            (17%nat, SAlu ALU_ADD vOUT (SAlu ALU_SLL (SAlu ALU_ADD (k3 (V 189)) (SLit 2)) (SLit 2)));
            (20%nat, V 198); (23%nat, SAlu ALU_ADD (V 189) (SLit 1))].
Definition X_g2 : sstate :=
  cut L_g2 (km_regs ++ xg2_x) []
    (eobjs [mkCell (IX4 (V 194)) 4 (V 198)] [mkCell (IX4 (V 198)) 4 (V 194)]
       (out3 (V 189) (V 194) (V 192) (V 198)) (r2_outK (V 189)) stk_cells)
    kgb_facts.
Definition K_g2 : sstate :=
  cut L_g2 (km_regs ++ xg2_x) [] (eobjs [] [] (out3 (V 189) (V 194) (V 192) (V 198)) (r2_outK (V 189)) stk_cells) kgb_facts.
Definition gf_g2 : list sprop :=
  [SPUlt (NXT (V 194)) vN; SPUlt (PRV (V 194)) vN; SPUlt (NXT (V 198)) vN; SPUlt (PRV (V 198)) vN].

Definition N_Kg : rnode :=
  mkRN K_g gf_g true None (RGm R196 (V 188) [V 188; V 192] [(V 192, NXT (V 188))]) 5 lexM 5 None.
Definition N_Kgb : rnode :=
  mkRN K_gb [] true None (RGm R196 (V 192) [V 192; V 194; V 198] [(V 194, PRV (V 192)); (V 198, NXT (V 192))]) 5 lexM 4 None.
Definition N_Kg2 : rnode := mkRN K_g2 gf_g2 true None (RGm R196m1 (V 198) [V 198; V 194] []) 5 lexM 2 None.
Definition N_Xg2 : rnode :=
  mkRN X_g2 [] true None (RGm R196 (V 192) [V 192; V 194; V 198] [(V 194, PRV (V 192)); (V 198, NXT (V 192))]) 5 lexM 3 None.

Definition ecutpcs_g : list Z := [0x1f494; 0x1f4e8; L_g2].
Definition rcuts_g : list rnode := [N_Kg; N_Kgb; N_Kg2].
Definition rexits_g : list rnode := [N_Xg2].
End R2G.
