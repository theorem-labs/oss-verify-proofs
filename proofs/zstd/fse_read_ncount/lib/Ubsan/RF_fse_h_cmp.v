(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseHarness.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKit.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImg RF_fse_iface RF_fse_h_model.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section Cmp.
Variables (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : fmem) (SP NC RT : Z) (nc rt : list Z) (msv : Z).
Variable POST : machine_state -> Prop.
Hypothesis MSV : 0 <= msv <= 255.
Hypothesis LNC : length nc = 256%nat.
Hypothesis LRT : length rt = 256%nat.
Hypothesis NCB : bytes_at usegs m NC (u16s (map (Z_to_bv 64) nc)).
Hypothesis RTB : bytes_at usegs m RT (u16s (map (Z_to_bv 64) rt)).
Hypothesis AGREE : forall i, 0 <= i <= msv -> Znth i rt = Znth i nc.
Notation STpc pc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 :=
(MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 pc) fc None m (seg_rom usegs)).
#[using="nc rt MSV LNC LRT NCB RTB AGREE"] Lemma cmp_loop : forall f s A2 A3 (x1 x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word),
0 <= s <= msv -> msv - s < Z.of_nat f -> msv < A2 <= 2^63 -> msv < A3 <= 2^63 ->
(forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
evt usegs POST (STpc 0x13794 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31)) ->
evt usegs POST (STpc 0x13768 x1 x5 x6 x7 (Z_to_bv 64 (NC + 2 * s)) (Z_to_bv 64 (RT + 2 * s))
(Z_to_bv 64 (A2 - s)) (Z_to_bv 64 (A3 - s)) (Z_to_bv 64 (msv + 1 - s))
x15 x16 x17 x28 x29 x30 x31).
Proof.
induction f as [|f IH]; intros s A2 A3 x1 x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 HS HF HA2 HA3 K.
{ exfalso. cbn in HF. lia. }
zstep. if_cases B0; zify_cond B0; [exfalso; lia|]. clear B0.
zstep. if_cases B1; zify_cond B1; [exfalso; lia|]. clear B1.
assert (NTHN : nth_error (map (Z_to_bv 64) nc) (Z.to_nat s) = Some (Z_to_bv 64 (Znth s nc))).
{ rewrite nth_error_map. unfold Znth. rewrite (nth_error_nth' nc 0) by lia. reflexivity. }
assert (NTHR : nth_error (map (Z_to_bv 64) rt) (Z.to_nat s) = Some (Z_to_bv 64 (Znth s nc))).
{ rewrite nth_error_map. rewrite <- (AGREE s HS). unfold Znth. rewrite (nth_error_nth' rt 0) by lia. reflexivity. }
pose proof (u16ro_read usegs m NC _ s _ (wa (NC + 2 * s)) NCB NTHN ltac:(lia) eq_refl) as RD1.
pose proof (u16ro_read usegs m RT _ s _ (wa (RT + 2 * s)) RTB NTHR ltac:(lia) eq_refl) as RD2.
zstep.
zstep.
zstep. if_cases B. { exfalso. revert B. rewrite bv_eqb_refl. discriminate. }
clear B.
zstep. zstep. zstep. zstep. zstep.
zstep. if_cases B2; zify_cond B2.
- replace (NC + 2 * s + 2) with (NC + 2 * (s + 1)) by lia.
replace (RT + 2 * s + 2) with (RT + 2 * (s + 1)) by lia.
replace (A2 - s + -1) with (A2 - (s + 1)) by lia.
replace (A3 - s + -1) with (A3 - (s + 1)) by lia.
replace (msv + 1 - s + -1) with (msv + 1 - (s + 1)) by lia.
eapply (IH (s + 1)); [lia| lia| lia| lia| exact K].
- apply K.
Qed.
End Cmp.
