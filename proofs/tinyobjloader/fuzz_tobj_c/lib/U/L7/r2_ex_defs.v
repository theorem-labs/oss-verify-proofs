From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymCFG.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv RingBuf RingCfg.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L7 Require Import S_r2 r2_cuts r2_ex_base.
Import ListNotations.
Open Scope Z_scope.

(* Complete-side (existence) cut and exit states of r2 on segsU, in the shape of P's Lib_tess_run2d_ex_defs.
   nxt/prv are ghost lists LN/LP (objects 3/4 of eobjs).  Register map against P:
     init loop  i = v123 (P 123; ubsan has no down counter, P's 124), flag v127 (<= 1)
     reflex     i = v183 (P 125)
     main loop  cur = v188 (P 180), triangles k = v189 (P 181), remaining R = v196 (P 182),
                misses = v186 (P 183), pass = v185 (P 184), flag reg19 = v187
     clip       NXT cur = v192 (P 186), PRV cur = v191 (P 187), Kc reg19 = v190
     scan (Ki)  the vertex loaded at the cut pc is NXT v193 (P 188 is the loaded vertex itself);
                dist (NXT v193, v191)
     fan        k = v195 (P 126) *)
Module R2E.
Import R2C R2X.

Definition eobjs (cn cp outc : list cell) (outd : odefault) (stkc : list cell) : list sobj :=
  [r2_O_stk stkc; r2_O_w; r2_O_p2d;
   mkObj vNXT (SLit 0) (SAlu ALU_SLL vN (SLit 2)) cn (DList LN);
   mkObj vPRV (SLit 0) (SAlu ALU_SLL vN (SLit 2)) cp (DList LP);
   r2_O_rfx; r2_O_out outc outd].

Definition k3 (k : sv) : sv := SAlu ALU_ADD (SAlu ALU_SLL k (SLit 1)) k.
Definition out3 (k a b d : sv) : list cell :=
  [mkCell (SAlu ALU_SLL (SAlu ALU_ADD (k3 k) (SLit 2)) (SLit 2)) 4 d;
   mkCell (SAlu ALU_SLL (SAlu ALU_ADD (k3 k) (SLit 1)) (SLit 2)) 4 b;
   mkCell (SAlu ALU_SLL (k3 k) (SLit 2)) 4 a].

(* init loop (ubsan 0x1ee14; exit to 0x1ee84) *)
Definition L_r : Z := 0x1ee14.
Definition L_rf : Z := 0x1ee84.
Definition kr_regs : list (nat * sv) :=
  [(5%nat, SAlu ALU_ADD (V 123) (SLit 1)); (8%nat, vOUT); (9%nat, vN); (10%nat, vN); (11%nat, V 127);
   (12%nat, vNXT); (13%nat, I4); (14%nat, SAlu ALU_XOR vNXT M1);
   (15%nat, SAlu ALU_ADD (SAlu ALU_ADD vN (SLit (-1))) (V 123));
   (16%nat, SAlu ALU_SUB (SLit 0) vN); (17%nat, SLit 1); (18%nat, vW)].
Definition xr_regs : list (nat * sv) :=
  [(5%nat, SAlu ALU_ADD (V 123) (SLit 2)); (6%nat, TESTV); (7%nat, REMP); (8%nat, vOUT); (9%nat, vN);
   (10%nat, vN); (11%nat, V 127); (12%nat, vNXT); (13%nat, SAlu ALU_ADD I4 (SLit 4));
   (14%nat, SAlu ALU_XOR vNXT M1);
   (15%nat, SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD vN (SLit (-1))) (V 123)) (SLit 1));
   (16%nat, SAlu ALU_SUB (SLit 0) vN); (17%nat, SLit 1); (18%nat, vW); (28%nat, SLit 1); (29%nat, SLit 0)].

Definition X_r0 : sstate := cut L_r kr_regs [] objs0 (SPEq (V 123) (SLit 0) :: inv_r).
Definition K_r : sstate := cut L_r kr_regs [] (eobjs [] [] [] DUnknown stk_cells) inv_r.
Definition X_r : sstate := cut L_r xr_regs [] (eobjs [cellN] [cellP] [] DUnknown stk_cells) (TEST_r :: inv_r).
Definition X_rf : sstate :=
  cut L_rf xr_regs [] (eobjs [cellN] [cellP] [] DUnknown stk_cells) (SPNot TEST_r :: inv_r).
Definition K_f0 : sstate := cut L_rf xr_regs [] (eobjs [] [] [] DUnknown stk_cells) (SPNot TEST_r :: inv_r).

(* reflex-flag loop (0x1eeb8) and fan loop (0x1f664) *)
Definition K_f : sstate :=
  cut 0x1eeb8
    [(8%nat, vOUT); (9%nat, vN); (10%nat, vN); (11%nat, V 180); (12%nat, V 182); (13%nat, V 183);
     (14%nat, SLit 9); (15%nat, SLit (-9)); (16%nat, SLit 1); (18%nat, vW); (28%nat, SLit 1)]
    [] (eobjs [] [] [] DUnknown stk_cells)
    [SPUlt (V 183) vN; SPUle (V 182) (V 183); SPUle (V 180) (SLit 1)].
Definition gf_f : list sprop := [SPUlt (NXT (V 183)) vN; SPUlt (PRV (V 183)) vN].

Definition K_fan : sstate :=
  cut 0x1f664
    [(8%nat, vOUT); (9%nat, vN); (10%nat, SAlu ALU_ADD (SLit 2) (V 195));
     (12%nat, SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (V 195) (SLit 1)) (V 195)) (SLit 1));
     (18%nat, vW); (22%nat, SAlu ALU_XOR vOUT M1); (28%nat, SLit 1)]
    [] (eobjs [] [] [] (r2_outK (V 195)) stk_cells)
    [SPUle (SAlu ALU_ADD (V 195) (SLit 3)) vN; hint12 (V 195); SPUle (V 195) (SLit r2_two20)].

(* main loop (0x1f080), clip (0x1f230, exit 0x1f2d0), scan (0x1f36c), last triangle (0x1f30c, 0x1f5a4) *)
Definition mg_facts : list sprop := [SPUle (V 185) (SLit 2)].
Definition objsKe : list sobj := eobjs [] [] [] (r2_outK (V 189)) stk_cells.

Definition K_m : sstate := cut 0x1f080 km_regs [] objsKe (km_facts ++ mg_facts).
Definition gf_m : list sprop :=
  [SPUlt (NXT (V 188)) vN; SPUlt (PRV (V 188)) vN; SPUlt (NXT (NXT (V 188))) vN; SPUlt (PRV (NXT (V 188))) vN].

Definition kc_x : list (nat * sv) :=
  [(5%nat, pt (V 192)); (10%nat, vPRV); (11%nat, V 191); (12%nat, vNXT); (15%nat, V 191);
   (16%nat, V 192); (17%nat, vP2D); (19%nat, V 190); (21%nat, V 192)].
Definition kc_facts : list sprop :=
  km_facts ++ mg_facts ++ [SPUlt (V 190) vN; SPUlt (V 191) vN; SPUlt (V 192) vN].
Definition K_c : sstate := cut 0x1f230 (km_regs ++ kc_x) [] objsKe kc_facts.

Definition L_c2 : Z := 0x1f2d0.
Definition xc2_regs : list (nat * sv) :=
  km_regs ++ kc_x ++
  [(10%nat, SAlu ALU_ADD vPRV (IX4 (V 192))); (12%nat, SLit 0); (13%nat, SAlu ALU_XOR vPRV M1);
   (14%nat, SAlu ALU_XOR vNXT M1); (15%nat, IX4 (V 191)); (16%nat, IX4 (V 192)); (17%nat, SLit 0);
   (23%nat, SAlu ALU_ADD (V 189) (SLit 1))].
Definition X_c2 : sstate :=
  cut L_c2 xc2_regs []
    (eobjs [mkCell (IX4 (V 191)) 4 (V 192)] [mkCell (IX4 (V 192)) 4 (V 191)]
       (out3 (V 189) (V 191) (V 188) (V 192)) (r2_outK (V 189)) stk_cells)
    kc_facts.
Definition K_c2 : sstate :=
  cut L_c2 xc2_regs [] (eobjs [] [] (out3 (V 189) (V 191) (V 188) (V 192)) (r2_outK (V 189)) stk_cells) kc_facts.
Definition gf_c2 : list sprop :=
  [SPUlt (NXT (V 191)) vN; SPUlt (PRV (V 191)) vN; SPUlt (NXT (V 192)) vN; SPUlt (PRV (V 192)) vN].

Definition ki_x : list (nat * sv) :=
  [(5%nat, pt (V 192)); (6%nat, SAlu ALU_XOR vNXT M1); (7%nat, SAlu ALU_XOR vP2D M1);
   (10%nat, vPRV); (11%nat, V 191); (12%nat, vNXT); (15%nat, V 191); (16%nat, V 192); (17%nat, vP2D);
   (21%nat, V 192); (28%nat, SLit 0); (29%nat, SAlu ALU_ADD vNXT (IX4 (V 193))); (30%nat, SLit 0)].
Definition ki_facts : list sprop :=
  km_facts ++ mg_facts ++ [SPUlt (V 191) vN; SPUlt (V 192) vN; SPUlt (V 193) vN].
Definition K_i : sstate := cut 0x1f36c (km_regs ++ ki_x) [] objsKe ki_facts.
Definition gf_i : list sprop := [SPUlt (NXT (V 193)) vN].

Definition K_x : sstate := cut 0x1f30c km_regs [] objsKe kx_facts.
Definition K_x2 : sstate := cut 0x1f5a4 km_regs [] objsKe kx_facts.
Definition gf_x : list sprop := [SPUlt (NXT (V 188)) vN; SPUlt (NXT (NXT (V 188))) vN].

Definition E_ret : sstate :=
  mkSS r2_ret (post_regs NF) r2_post_fregs FcsrFrm0 None
    (eobjs [] [] [] (r2_outK (SAlu ALU_ADD vN (SLit (-2)))) []) r2_base_facts r2_NXC false.

(* ring nodes *)
Definition VN : positive := 13%positive.
Definition noring : option rghost := None.
Definition RGfull (roots : list sv) : option rghost := Some (mkRG vN (SLit 0) roots []).
Definition RGm (R cur : sv) (roots : list sv) (eqs : list (sv * sv)) : option rghost :=
  Some (mkRG R cur roots eqs).
Definition R196 : sv := V 196.
Definition R196m1 : sv := SAlu ALU_ADD (V 196) (SLit (-1)).
Definition lexM : list (vdir * sv) := [(Vdown false, V 196); (Vup false, V 185); (Vup false, V 186)].
Definition eqs_c : list (sv * sv) := [(V 192, NXT (V 188)); (V 191, PRV (V 188))].

Definition N_Pre : rnode := mkRN Pre_r2U [] false None noring 12 [] 0 None.
Definition N_Ks : rnode := mkRN Ks [] false None noring 11 [(Vdown false, V 121)] 0 None.
Definition N_Ka : rnode := mkRN Ka [] false None noring 10 [(Vdown false, V 126)] 0 None.
Definition N_Kr : rnode := mkRN K_r [] false (Some (V 123)) noring 8 [(Vup false, V 123)] 2 None.
Definition N_Kf0 : rnode := mkRN K_f0 [] true None (RGfull []) 7 [] 0 None.
Definition N_Kf : rnode := mkRN K_f gf_f true None (RGfull [V 183]) 6 [(Vup false, V 183)] 0 None.
Definition N_Kfan : rnode := mkRN K_fan [] true None noring 5 [(Vup false, V 195)] 0 None.
Definition N_Km : rnode := mkRN K_m gf_m true None (RGm R196 (V 188) [V 188] []) 5 lexM 8 None.
Definition N_Kc : rnode := mkRN K_c [] true None (RGm R196 (V 188) [V 188; V 192; V 191] eqs_c) 5 lexM 5 None.
Definition N_Kc2 : rnode := mkRN K_c2 gf_c2 true None (RGm R196m1 (V 192) [V 192; V 191] []) 5 lexM 3 None.
Definition N_Ki : rnode :=
  mkRN K_i gf_i true None (RGm R196 (V 188) [V 188; V 192; V 191; V 193] eqs_c) 5 lexM 6
    (Some (NXT (V 193), V 191)).
Definition N_Kx : rnode := mkRN K_x [] true None (RGm R196 (V 188) [V 188] []) 2 [] 1 None.
Definition N_Kx2 : rnode := mkRN K_x2 gf_x true None (RGm R196 (V 188) [V 188] []) 2 [] 0 None.
Definition N_Xr0 : rnode := mkRN X_r0 [] false (Some (V 123)) noring 9 [] 0 None.
Definition N_Xr : rnode := mkRN X_r [] false (Some (V 123)) noring 8 [(Vup false, V 123)] 1 None.
Definition N_Xrf : rnode := mkRN X_rf [] false (Some (V 123)) noring 8 [(Vup false, V 123)] 1 None.
Definition N_Xc2 : rnode := mkRN X_c2 [] true None (RGm R196 (V 188) [V 188; V 192; V 191] eqs_c) 5 lexM 4 None.
Definition N_Eret : rnode := mkRN E_ret [] true None noring 1 [] 0 None.

(* cut pcs and node lists without the forced-clip region (K_g, K_gb, K_g2, X_g2 live in r2_ex_g.v) *)
Definition ecutpcs_base : list Z := cutpcs_r2 ++ [L_rf; L_c2].
Definition rcuts_base : list rnode :=
  [N_Pre; N_Ks; N_Ka; N_Kr; N_Kf0; N_Kf; N_Kfan; N_Km; N_Kc; N_Kc2; N_Ki; N_Kx; N_Kx2].
Definition rexits_base : list rnode := [N_Xr0; N_Xr; N_Xrf; N_Xc2; N_Eret].

End R2E.
