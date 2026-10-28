From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L7 Require Import S_r2.
Import ListNotations.
Open Scope Z_scope.

Module R2C.

Definition vW := r2_W. Definition vN := r2_N. Definition vOUT := r2_OUT. Definition vP2D := r2_P2D.
Definition vNXT := r2_NXT. Definition vPRV := r2_PRV.
Definition M1 : sv := SLit 18446744073709551615.
Definition rsp : sv := SAlu ALU_ADD (SVar 10) (SLit (- r2_frame)).
Definition V (i : positive) : sv := SVar i.

Definition stk_cells : list cell :=
  [mkCell (SLit (-128)) 8 (SVar 78); mkCell (SLit (-120)) 8 (SVar 69); mkCell (SLit (-112)) 8 (SVar 68);
   mkCell (SLit (-104)) 8 (SVar 47); mkCell (SLit (-96)) 8 (SVar 46); mkCell (SLit (-88)) 8 (SVar 45);
   mkCell (SLit (-80)) 8 (SVar 44); mkCell (SLit (-72)) 8 (SVar 43); mkCell (SLit (-64)) 8 (SVar 42);
   mkCell (SLit (-56)) 8 (SVar 41); mkCell (SLit (-48)) 8 (SVar 40); mkCell (SLit (-40)) 8 (SVar 39);
   mkCell (SLit (-32)) 8 (SVar 38); mkCell (SLit (-24)) 8 (SVar 29); mkCell (SLit (-16)) 8 (SVar 28);
   mkCell (SLit (-8)) 8 (SVar 11)].
Definition body_regs (l : list (nat * sv)) : list sv :=
  setregs (cut_regs NF)
    ([(2%nat, rsp); (8%nat, SVar 132); (9%nat, SVar 133); (18%nat, SVar 134); (19%nat, SVar 135);
      (20%nat, SVar 136); (21%nat, SVar 137); (22%nat, SVar 138); (23%nat, SVar 139); (24%nat, SVar 176);
      (25%nat, SVar 177); (26%nat, SVar 178); (27%nat, SVar 179)] ++ l).
Definition body_fregs (l : list (nat * sv)) : list sv :=
  setregs r2_post_fregs ([(8%nat, SVar 172); (9%nat, SVar 173); (18%nat, SVar 174)] ++ l).
Definition NXC : positive := 200%positive.
Definition cut (pc : Z) (regs fregs : list (nat * sv)) (objs : list sobj) (facts : list sprop) : sstate :=
  mkSS pc (body_regs regs) (body_fregs fregs) FcsrFrm0 None objs (facts ++ r2_base_facts) NXC false.
Definition objs0 := r2_objs stk_cells DUnknown DUnknown [] DUnknown.
Definition objsF := r2_objs stk_cells (r2_arrK vN) (r2_arrK vN) [] DUnknown.
Definition hint12 (k : sv) : sprop := SPEq (SMd M_MUL k (SLit 12)) (SMd M_MUL k (SLit 12)).
Definition pt (v : sv) : sv := SAlu ALU_ADD vP2D (SAlu ALU_SLL (SAlu ALU_SLL v (SLit 1)) (SLit 3)).

Definition Ks : sstate :=
  cut 0x1ec6c
    [(8%nat, vOUT); (9%nat, vN); (10%nat, vN); (11%nat, vP2D); (12%nat, SAlu ALU_XOR vP2D M1); (13%nat, V 120);
     (14%nat, V 121); (15%nat, V 122); (16%nat, V 123); (17%nat, SAlu ALU_SLL (V 120) (SLit 3)); (18%nat, vW)]
    [(15%nat, SLit 0)] objs0
    [SPUle (SLit 1) (V 121); SPUle (V 121) vN;
     SPEq (SAlu ALU_ADD (V 120) (SAlu ALU_SLL (V 121) (SLit 1))) (SAlu ALU_ADD (SAlu ALU_SLL vN (SLit 1)) (SLit 1));
     SPUle (V 120) (SLit 4194304); SPUle (V 122) (SLit 1); SPUle (V 123) (SLit 1)].

Definition Ka : sstate :=
  cut 0x1ed34
    [(8%nat, vOUT); (9%nat, vN); (10%nat, vN); (11%nat, vP2D); (12%nat, SAlu ALU_XOR vP2D M1);
     (13%nat, SAlu ALU_ADD (SLit 1) (V 124)); (14%nat, V 126); (18%nat, vW)]
    [(8%nat, V 125)] objs0
    [SPUle (SLit 1) (V 126); SPUle (V 126) vN;
     SPEq (SAlu ALU_ADD (V 124) (SAlu ALU_SLL (V 126) (SLit 1))) (SAlu ALU_SLL vN (SLit 1));
     SPAlign 124 1; SPUle (V 124) (SLit 4194304)].

Definition Kr : sstate :=
  cut 0x1ee14
    [(5%nat, SAlu ALU_ADD (SLit 1) (V 181)); (8%nat, vOUT); (9%nat, vN); (10%nat, vN); (11%nat, V 180);
     (12%nat, vNXT); (13%nat, SAlu ALU_SLL (V 181) (SLit 2)); (14%nat, SAlu ALU_XOR vNXT M1);
     (16%nat, SAlu ALU_SUB (SLit 0) vN); (17%nat, SLit 1); (18%nat, vW)]
    [] (r2_objs stk_cells (r2_arrK (V 181)) (r2_arrK (V 181)) [] DUnknown)
    [SPUlt (V 181) vN; SPUle (V 180) (SLit 1)].

Definition Kf : sstate :=
  cut 0x1eeb8
    [(8%nat, vOUT); (9%nat, vN); (10%nat, vN); (11%nat, V 180); (12%nat, V 182); (13%nat, V 183);
     (14%nat, SLit 9); (15%nat, SLit (-9)); (16%nat, SLit 1); (18%nat, vW); (28%nat, SLit 1)]
    [] objsF
    [SPUlt (V 183) vN; SPUle (V 182) (V 183); SPUle (V 180) (SLit 1)].

Definition km_regs : list (nat * sv) :=
  [(1%nat, V 197); (8%nat, vOUT); (9%nat, V 196); (13%nat, V 185); (14%nat, V 186); (18%nat, vW); (19%nat, V 187);
   (20%nat, V 188); (22%nat, SAlu ALU_XOR vOUT M1); (23%nat, V 189); (24%nat, SLit 9); (25%nat, SLit (-9));
   (26%nat, SLit (-8))].
Definition km_facts : list sprop :=
  [SPUlt (V 185) vN; SPUle (V 186) (V 196); SPUlt (V 187) vN; SPUlt (V 188) vN;
   SPEq (SAlu ALU_ADD (V 196) (V 189)) vN; SPBranch BC_LTU (SLit 3) (V 196); SPUle (V 196) vN;
   SPUle (SAlu ALU_ADD (V 189) (SLit 3)) vN; hint12 (V 189); SPUle (V 189) (SLit r2_two20)].
Definition objsK := r2_objs stk_cells (r2_arrK vN) (r2_arrK vN) [] (r2_outK (V 189)).

Definition Km : sstate := cut 0x1f080 km_regs [] objsK km_facts.

Definition Kc : sstate :=
  cut 0x1f230
    (km_regs ++ [(5%nat, pt (V 192)); (10%nat, vPRV); (11%nat, V 191); (12%nat, vNXT); (15%nat, V 191);
                 (16%nat, V 192); (17%nat, vP2D); (19%nat, V 190); (21%nat, V 192)])
    [] objsK (km_facts ++ [SPUlt (V 190) vN; SPUlt (V 191) vN; SPUlt (V 192) vN]).

Definition Ki : sstate :=
  cut 0x1f36c
    (km_regs ++ [(5%nat, pt (V 192)); (6%nat, SAlu ALU_XOR vNXT M1); (7%nat, SAlu ALU_XOR vP2D M1);
                 (10%nat, vPRV); (11%nat, V 191); (12%nat, vNXT); (15%nat, V 191); (16%nat, V 192); (17%nat, vP2D);
                 (21%nat, V 192); (28%nat, SLit 0); (29%nat, SAlu ALU_ADD vNXT (SAlu ALU_SLL (V 193) (SLit 2)));
                 (30%nat, SLit 0)])
    [] objsK (km_facts ++ [SPUlt (V 191) vN; SPUlt (V 192) vN; SPUlt (V 193) vN]).

Definition Kfan : sstate :=
  cut 0x1f664
    [(8%nat, vOUT); (9%nat, vN); (10%nat, SAlu ALU_ADD (SLit 2) (V 195));
     (12%nat, SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (V 195) (SLit 1)) (V 195)) (SLit 1));
     (18%nat, vW); (22%nat, SAlu ALU_XOR vOUT M1); (28%nat, SLit 1)]
    [] (r2_objs stk_cells (r2_arrK vN) (r2_arrK vN) [] (r2_outK (V 195)))
    [SPUle (SAlu ALU_ADD (V 195) (SLit 3)) vN; hint12 (V 195); SPUle (V 195) (SLit r2_two20)].

Definition kx_facts : list sprop :=
  [SPUlt (V 185) vN; SPUle (V 186) (V 196); SPUlt (V 187) vN; SPUlt (V 188) vN;
   SPEq (SAlu ALU_ADD (V 196) (V 189)) vN; SPUle (V 196) (SLit 3); SPUle (SLit 3) (V 196);
   SPUle (SAlu ALU_ADD (V 189) (SLit 3)) vN; hint12 (V 189); SPUle (V 189) (SLit r2_two20)].
Definition Kx : sstate := cut 0x1f30c km_regs [] objsK kx_facts.
Definition Kx2 : sstate := cut 0x1f5a4 km_regs [] objsK kx_facts.

Definition FUEL_r2 : nat := 1000%nat.
Definition cutpcs_r2 : list Z :=
  [0x1ec6c; 0x1ed34; 0x1ee14; 0x1eeb8; 0x1f080; 0x1f230; 0x1f36c; 0x1f664; 0x1f30c; 0x1f5a4].
Definition cuts_r2 : list sstate := [Pre_r2U; Ks; Ka; Kr; Kf; Km; Kc; Ki; Kfan; Kx; Kx2].
Definition exits_r2 : list sstate := [P_r2U].

End R2C.
