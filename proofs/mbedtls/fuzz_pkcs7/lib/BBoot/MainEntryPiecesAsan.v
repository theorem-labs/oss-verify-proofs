(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AxSymExec3 AsanPlanCore AsanPlan. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanCertDefs. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import PlanCut. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import StartupHSAsan MainEntryPlanAsan MainEntryHSAsan MainEntryHScutAsan.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.


(* [comment removed for export] *)
Definition NX1 : nat := 467.
(* [comment removed for export] *)
Definition IT1_ranges : list (Z * nat) :=
  [(288920, 9%nat); (288964, 7%nat); (289020, 4%nat); (348740, 39%nat); (348944, 13%nat); (349012, 40%nat); (349296, 49%nat); (349636, 34%nat);
   (349792, 12%nat); (349864, 8%nat); (350124, 2%nat); (350424, 9%nat); (350732, 19%nat); (350860, 27%nat); (351216, 31%nat); (351484, 41%nat);
   (351652, 5%nat); (351704, 8%nat); (351748, 1%nat); (351780, 17%nat); (353836, 20%nat); (355712, 37%nat); (355976, 24%nat); (356076, 5%nat);
   (356128, 8%nat); (356172, 2%nat); (356240, 5%nat); (356272, 12%nat); (356336, 16%nat); (356960, 13%nat); (357112, 20%nat); (357208, 4%nat);
   (357256, 4%nat); (357360, 1%nat); (357380, 19%nat); (357528, 4%nat); (357636, 1%nat); (357644, 30%nat); (357776, 24%nat); (357904, 18%nat);
   (358168, 6%nat); (358296, 18%nat); (358496, 19%nat); (358612, 75%nat); (361944, 14%nat); (362008, 35%nat); (435528, 28%nat); (436108, 5%nat);
   (436192, 10%nat); (436420, 2%nat); (436436, 10%nat); (440004, 6%nat); (456376, 6%nat); (461000, 1%nat); (463696, 46%nat); (463992, 14%nat);
   (470472, 8%nat); (470924, 3%nat); (470988, 9%nat); (471076, 6%nat); (479900, 22%nat); (480104, 10%nat); (486052, 12%nat); (487740, 4%nat);
   (487780, 1%nat); (504376, 9%nat); (504416, 1%nat); (510248, 13%nat); (510312, 40%nat); (510488, 7%nat); (510632, 6%nat); (510712, 6%nat);
   (511584, 11%nat); (511640, 40%nat); (511816, 7%nat); (513540, 17%nat); (513876, 10%nat); (537276, 8%nat); (537372, 1%nat); (552868, 13%nat);
   (552928, 6%nat); (552956, 42%nat); (553160, 13%nat); (553232, 12%nat); (553428, 3%nat); (555696, 38%nat); (561848, 18%nat); (562592, 25%nat);
   (562696, 55%nat); (563000, 4%nat); (563056, 27%nat); (563172, 13%nat); (563256, 3%nat); (564532, 12%nat); (564596, 6%nat); (564648, 34%nat);
   (564792, 22%nat); (565028, 25%nat); (565196, 19%nat); (565288, 10%nat); (566664, 17%nat); (566784, 1%nat); (566888, 14%nat); (620380, 11%nat);
   (920032, 9%nat); (920216, 4%nat); (968296, 7%nat)].
Definition IT1 : itab := mk_itab_ranges ASEGS IT1_ranges.
(* [comment removed for export] *)
Definition me_SB : expr := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 16) (EVar 6)).
Definition me_KD : kentry := KDisj (SA me_SB (-8388608)) (ELit 16777216) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 93)) 0) (ELit 65536).

(* [comment removed for export] *)
Definition natpairs (l : list (N * N)) : list (nat * nat) := List.map (fun p => (N.to_nat (fst p), N.to_nat (snd p))) l.
Definition me_M4 : list (nat * nat) := natpairs [(484%N, 467%N); (483%N, 468%N); (482%N, 485%N); (901%N, 12102%N); (965%N, 12182%N); (964%N, 12181%N); (963%N, 12180%N); (962%N, 12179%N); (961%N, 12178%N); (960%N, 12177%N); (959%N, 12176%N); (958%N, 12175%N); (957%N, 12174%N); (956%N, 12173%N); (955%N, 12172%N); (953%N, 12170%N); (952%N, 12169%N); (951%N, 12168%N); (950%N, 12167%N)].
Definition me_M5 : list (nat * nat) := natpairs [(485%N, 467%N); (484%N, 468%N); (483%N, 485%N); (478%N, 12102%N); (864%N, 12545%N); (863%N, 12544%N); (862%N, 12543%N); (861%N, 12542%N); (860%N, 12541%N); (859%N, 12540%N); (858%N, 12539%N); (857%N, 12538%N); (856%N, 12537%N); (855%N, 12536%N); (854%N, 12535%N)].
Definition me_cmp (M : list (nat * nat)) (q : plan) : plan := PCompact (at_handoffs (fun h => PRename M (PHandoff h)) q).

(* [comment removed for export] *)
Definition me_qA : plan := pkid 0 (pskip 1 mainentry_plan).
Definition me_qB : plan := pkid 1 (pskip 1 mainentry_plan).
Definition me_qA2 : plan := subL 592 me_qA.
Definition me_qA3 : plan := subL 480 me_qA2.
Definition me_qA4 : plan := subL 340 me_qA3.
Definition me_qA5 : plan := subL 62 me_qA4.
Definition me_qB2 : plan := subL 592 me_qB.
Definition me_qB3 : plan := subL 480 me_qB2.
Definition me_qB4 : plan := subL 340 me_qB3.
Definition me_qB5 : plan := subL 62 me_qB4.

(* [comment removed for export] *)
Definition me_R0_plan : plan := fst (pcut 2 mainentry_plan 0).
Definition me_R0_tab : nat -> option acs := hs_tab [(1000%nat, HS_s2c_1000); (1001%nat, HS_s2c_1001)].

(* [comment removed for export] *)
Definition me_A1_plan : plan := PFact me_KD (fst (pcut 592 me_qA 10)).   (* [comment removed for export] *)
Definition me_A1_tab : nat -> option acs := hs_tab [(1010%nat, HS_s2c_1010)].

(* [comment removed for export] *)
Definition me_A2_plan : plan := PFact me_KD (fst (pcut 480 me_qA2 11)).   (* [comment removed for export] *)
Definition me_A2_tab : nat -> option acs := hs_tab [(1011%nat, HS_s2c_1011)].

(* [comment removed for export] *)
Definition me_A3_plan : plan := PFact me_KD (fst (pcut 340 me_qA3 12)).   (* [comment removed for export] *)
Definition me_A3_tab : nat -> option acs := hs_tab [(1012%nat, HS_s2c_1012)].

(* [comment removed for export] *)
Definition me_A4_plan : plan := PFact me_KD (me_cmp me_M4 (fst (pcut 62 me_qA4 13))).   (* [comment removed for export] *)
Definition me_A4_tab : nat -> option acs := hs_tab [(1013%nat, HS_s2c_1013)].

(* [comment removed for export] *)
Definition me_A5_plan : plan := PFact me_KD (me_cmp me_M5 (me_qA5)).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition me_B1_plan : plan := PFact me_KD (fst (pcut 592 me_qB 20)).   (* [comment removed for export] *)
Definition me_B1_tab : nat -> option acs := hs_tab [(1020%nat, HS_s2c_1020)].

(* [comment removed for export] *)
Definition me_B2_plan : plan := PFact me_KD (fst (pcut 480 me_qB2 21)).   (* [comment removed for export] *)
Definition me_B2_tab : nat -> option acs := hs_tab [(1021%nat, HS_s2c_1021)].

(* [comment removed for export] *)
Definition me_B3_plan : plan := PFact me_KD (fst (pcut 340 me_qB3 22)).   (* [comment removed for export] *)
Definition me_B3_tab : nat -> option acs := hs_tab [(1022%nat, HS_s2c_1022)].

(* [comment removed for export] *)
Definition me_B4_plan : plan := PFact me_KD (me_cmp me_M4 (fst (pcut 62 me_qB4 23))).   (* [comment removed for export] *)
Definition me_B4_tab : nat -> option acs := hs_tab [(1023%nat, HS_s2c_1023)].

(* [comment removed for export] *)
Definition me_B5_plan : plan := PFact me_KD (me_cmp me_M5 (me_qB5)).   (* [comment removed for export] *)
