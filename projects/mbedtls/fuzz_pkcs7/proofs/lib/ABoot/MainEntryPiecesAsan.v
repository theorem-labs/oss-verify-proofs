(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AxSymExec3 AsanPlanCore AsanPlan AsanCertDefs PlanCut StartupHSAsan MainEntryPlanAsan MainEntryHSAsan MainEntryHScutAsan.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.


(* [comment removed for export] *)
Definition NX1 : nat := 467.
(* [comment removed for export] *)
Definition IT1_ranges : list (Z * nat) :=
  [(287524, 9%nat); (287568, 7%nat); (287624, 4%nat); (347344, 39%nat); (347548, 13%nat); (347616, 40%nat); (347900, 49%nat); (348240, 34%nat);
   (348396, 12%nat); (348468, 8%nat); (348728, 2%nat); (349028, 9%nat); (349336, 19%nat); (349464, 27%nat); (349820, 31%nat); (350088, 41%nat);
   (350256, 5%nat); (350308, 8%nat); (350352, 1%nat); (350384, 17%nat); (352440, 20%nat); (354316, 37%nat); (354580, 24%nat); (354680, 5%nat);
   (354732, 8%nat); (354776, 2%nat); (354844, 5%nat); (354876, 12%nat); (354940, 16%nat); (355564, 13%nat); (355716, 20%nat); (355812, 4%nat);
   (355860, 4%nat); (355964, 1%nat); (355984, 19%nat); (356132, 4%nat); (356240, 1%nat); (356248, 30%nat); (356380, 24%nat); (356508, 18%nat);
   (356772, 6%nat); (356900, 18%nat); (357100, 19%nat); (357216, 75%nat); (360548, 14%nat); (360612, 35%nat); (434132, 28%nat); (434712, 5%nat);
   (434796, 10%nat); (435024, 2%nat); (435040, 10%nat); (438608, 6%nat); (454980, 6%nat); (459604, 1%nat); (462300, 46%nat); (462596, 14%nat);
   (469076, 8%nat); (469528, 3%nat); (469592, 9%nat); (469680, 6%nat); (478504, 22%nat); (478708, 10%nat); (484656, 12%nat); (486344, 4%nat);
   (486384, 1%nat); (502980, 9%nat); (503020, 1%nat); (508852, 13%nat); (508916, 40%nat); (509092, 7%nat); (509236, 6%nat); (509316, 6%nat);
   (510188, 11%nat); (510244, 40%nat); (510420, 7%nat); (512144, 17%nat); (512480, 10%nat); (535880, 8%nat); (535976, 1%nat); (551472, 13%nat);
   (551532, 6%nat); (551560, 42%nat); (551764, 13%nat); (551836, 12%nat); (552032, 3%nat); (554300, 38%nat); (560452, 18%nat); (561196, 25%nat);
   (561300, 55%nat); (561604, 4%nat); (561660, 27%nat); (561776, 13%nat); (561860, 3%nat); (563136, 12%nat); (563200, 6%nat); (563252, 34%nat);
   (563396, 22%nat); (563632, 25%nat); (563800, 19%nat); (563892, 10%nat); (565268, 17%nat); (565388, 1%nat); (565492, 14%nat); (618984, 11%nat);
   (906772, 9%nat); (906956, 4%nat); (955036, 7%nat)].
Definition IT1 : itab := mk_itab_ranges ASEGS IT1_ranges.
(* [comment removed for export] *)
Definition me_SB : expr := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 16) (EVar 6)).
Definition me_KD : kentry := KDisj (SA me_SB (-8388608)) (ELit 16777216) (SA (EMd Instr.M_MUL (ELit 4096) (EVar 93)) 0) (ELit 65536).

(* [comment removed for export] *)
Definition natpairs (l : list (N * N)) : list (nat * nat) := List.map (fun p => (N.to_nat (fst p), N.to_nat (snd p))) l.
Definition me_M4 : list (nat * nat) := natpairs [(484%N, 467%N); (483%N, 468%N); (482%N, 485%N); (885%N, 12102%N); (965%N, 12182%N); (964%N, 12181%N); (963%N, 12180%N); (962%N, 12179%N); (961%N, 12178%N); (960%N, 12177%N); (959%N, 12176%N); (958%N, 12175%N); (957%N, 12174%N); (956%N, 12173%N); (955%N, 12172%N); (953%N, 12170%N); (952%N, 12169%N); (951%N, 12168%N); (950%N, 12167%N)].
Definition me_M5 : list (nat * nat) := natpairs [(485%N, 467%N); (484%N, 468%N); (483%N, 485%N); (478%N, 12102%N); (848%N, 12545%N); (847%N, 12544%N); (846%N, 12543%N); (845%N, 12542%N); (844%N, 12541%N); (843%N, 12540%N); (842%N, 12539%N); (841%N, 12538%N); (840%N, 12537%N); (839%N, 12536%N); (838%N, 12535%N)].
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
