(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseHarness.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg ABase RtCells AH_fse_kit AH_fse_pure.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Plain Require Import RF_fse_h_model.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKitF.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common.FseWalkKit.simpl_arr_sizes_fwk_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section CANSEC1. Context {rc : runConstT}.
Section Cmp.
Variables (RNG : footprint) (gp tp sp s0 s1 s2 s4 s6 s7 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32).
Variables (m : amem) (NC RT : Z) (nc rt : list Z) (msv A2 A3 : Z).
Variable POST : machine_state -> Prop.
Hypothesis MSV : 0 <= msv <= 255.
Hypothesis LNC : length nc = 256%nat.
Hypothesis LRT : length rt = 256%nat.
Hypothesis NCB : bytes_at bsegs m NC (u16s (map (Z_to_bv 64) nc)).
Hypothesis RTB : bytes_at bsegs m RT (u16s (map (Z_to_bv 64) rt)).
Hypothesis AGREE : forall i, 0 <= i <= msv -> Znth i rt = Znth i nc.
Hypothesis MI : mem_inv bsegs m.
Hypothesis NCR : 0 <= NC /\ NC + 512 + 8 <= KEND /\ NC mod 8 = 0.
Hypothesis RTR : 0 <= RT /\ RT + 512 + 8 <= KEND /\ RT mod 8 = 0.
Hypothesis UNC : unpoisoned m NC (NC + 512).
Hypothesis URT : unpoisoned m RT (RT + 512).
Hypothesis RNC : rng RNG NC 512.
Hypothesis RRT : rng RNG RT 512.
Hypothesis RNCS : rng RNG (shad NC) 64.
Hypothesis RRTS : rng RNG (shad RT) 64.
Hypothesis A2R : msv < A2 < 2^63.
Hypothesis A3R : msv < A3 < 2^63.
Notation STpc pc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 x31 :=
(MS (mkR x1 sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17
s2 (Z_to_bv 64 2147450880) s4 x21 s6 s7 x24 s9 s10 s11 x28 x29 x30 x31)
FR (Z_to_bv 64 pc) fc None m (seg_rom bsegs)).
#[using="nc rt MSV LNC LRT NCB RTB AGREE NCR RTR UNC URT RNC RRT RNCS RRTS A2R A3R"] Lemma cmp_loopB : forall f s (x1 x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word),
0 <= s <= msv -> msv - s < Z.of_nat f ->
(forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y24 y28 y29 y30 y31 : word),
evtF bsegs RNG POST (STpc 0x81240 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y24 y28 y29 y30 y31)) ->
evtF bsegs RNG POST (STpc 0x811c4 x1 x5 x6 x7 (Z_to_bv 64 (NC + 2 * s)) (Z_to_bv 64 (RT + 2 * s)) (Z_to_bv 64 (A2 - s))
(Z_to_bv 64 (A3 - s)) (Z_to_bv 64 (msv + 1 - s)) x15 x16 x17
(Z_to_bv 64 (RT + 2 * s)) (Z_to_bv 64 (NC + 2 * s)) x28 x29 x30 x31).
Proof.
induction f as [|f IH]; intros s x1 x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 HS HF K.
{ exfalso. cbn in HF. Local Ltac2 Set LiaHints.tbl := fun () => "00S0?11447729958.11011447729958.11311866103177.72 11869970069.71 19335898386.85 19567732401.83 23683590488.21 26274314084.21 28022624402.82 29786656982.65 29786659037.68 29788510300.67 29788510301.66 31827797969.78 32843401394.78 36277103323.84 37694598650.82 38898666155.69 42276654520.78 43324722563.85 45427048136.75 52067329428.78 5468053843.78  5490622699.85  59308693840.74 59308693969.75 59314923118.57 59435130665.84 61226506573.74 61336826000.78 65453664584.70 65747618005.21 68112585672.78 9178932959.21  9421519879.78  00000100200I00`01;01Z01n02F02G02[02o03C03W03k04?04Z04[05605J05K05f06A06[06\07:07X07g08F08a09509P09d0:80:L0:`FFS3LNC3LRT2HS2HF3NC03RT0S3LNC3LRT2HS2HF3NC03RT0S3MSV3LNC3LRT2HS2HF3NC03RT0S3MSV3LNC3LRT2HS2HF3NC03RT03RTES3MSV2HS3NC81H2H02H4S3MSV2HS3NC81H2H42H53RT8FS3LNC3LRT2HF3NC03RT0S3LNC3LRT2HF3NC03RT0S3LNC3LRT2HF3NC03RT0S3LNC3LRT2HF3NC03RT0S3LNC3LRT2HF3NC03RT0S3LNC3LRT2HF3NC03RT0S3MSV3LNC3LRT2HS2HF3NC03RT0FS3MSV3LNC3LRT2HS2HF3NC03RT0S3LNC3LRT2HF3NC03RT0FS3LNC3LRT3A3R2HS2HF3NC03RT0S3MSV3LNC3LRT2HS2HF3NC03RT0S3LNC3LRT2HS2HF3NC03RT02B2FS3LNC3LRT3A2R2HS2HF3NC03RT02G1S3LNC3LRT3A3R2HS2HF3NC03RT02G2S3LNC3LRT2HS2HFS3MSV3LNC3LRT2HS2HF3NC03NCE3RT0S3LNC3LRT3A2R2HS2HF3NC03RT0S3LNC3LRT2HF3NC03RT0S3MSV3LNC3LRT2HS2HF3NC03RT0S3MSV2HS3RT81H2H02H4S3LNC3LRT2HF3NC03RT0S2HS3NC81H2H42H53RT8S3LNC3LRT2HF3NC03RT0".
lia. }
destruct NCR as (NC0 & NCE & NC8). destruct RTR as (RT0 & RTE & RT8). unfold KEND in *.
assert (ACC1 : acc_in RNG (Z_to_bv 64 (Z.shiftr (NC + 2 * s) 3 + 2147450880), 1%nat)).
{ apply (rng_acc_litZ' RNG _ _ _ 1 1 RNCS eq_refl eq_refl). rewrite shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF. change (2^3) with 8.
clear - NC8 HS MSV NC0. Z.div_mod_to_equations. lia. }
assert (ACC2 : acc_in RNG (Z_to_bv 64 (Z.shiftr (RT + 2 * s) 3 + 2147450880), 1%nat)).
{ apply (rng_acc_litZ' RNG _ _ _ 1 1 RRTS eq_refl eq_refl). rewrite shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF. change (2^3) with 8.
clear - RT8 HS MSV RT0. Z.div_mod_to_equations. lia. }
assert (RD1 : ov_read_bytes bsegs m (wa (Z.shiftr (NC + 2 * s) 3 + 2147450880)) 1 = Some [Z_to_bv 8 0]).
{ apply (unpoisoned_full_rd bsegs m NC (NC + 512)); [exact UNC| |];
rewrite ?shad_div, ?Z.shiftr_div_pow2 by lia; unfold ASHOFF; change (2^3) with 8; clear - NC8 HS MSV NC0; Z.div_mod_to_equations; lia. }
assert (RD2 : ov_read_bytes bsegs m (wa (Z.shiftr (RT + 2 * s) 3 + 2147450880)) 1 = Some [Z_to_bv 8 0]).
{ apply (unpoisoned_full_rd bsegs m RT (RT + 512)); [exact URT| |];
rewrite ?shad_div, ?Z.shiftr_div_pow2 by lia; unfold ASHOFF; change (2^3) with 8; clear - RT8 HS MSV RT0; Z.div_mod_to_equations; lia. }
assert (NTHN : nth_error (map (Z_to_bv 64) nc) (Z.to_nat s) = Some (Z_to_bv 64 (Znth s nc))).
{ rewrite nth_error_map. unfold Znth. rewrite (nth_error_nth' nc 0) by lia. reflexivity. }
assert (NTHR : nth_error (map (Z_to_bv 64) rt) (Z.to_nat s) = Some (Z_to_bv 64 (Znth s nc))).
{ rewrite nth_error_map. rewrite <- (AGREE s HS). unfold Znth. rewrite (nth_error_nth' rt 0) by lia. reflexivity. }
pose proof (u16ro_read bsegs m NC _ s _ (wa (NC + 2 * s)) NCB NTHN ltac:(lia) eq_refl) as RN.
pose proof (u16ro_read bsegs m RT _ s _ (wa (RT + 2 * s)) RTB NTHR ltac:(lia) eq_refl) as RR.
zstep. if_cases G1; zify_cond G1; [exfalso; rewrite ?unsigned_lit in G1 by lia; lia|].
zstep. if_cases G2; zify_cond G2; [exfalso; rewrite ?unsigned_lit in G2 by lia; lia|].
zstep. zstep. zstep.
zstep. if_cases B0; zify_cond B0; [exfalso; apply B0; reflexivity|].
zstep. zstep. zstep.
zstep.
zstep. if_cases B1; zify_cond B1; [exfalso; apply B1; reflexivity|].
zstep.
zstep. if_cases B. { exfalso. revert B. rewrite bv_eqb_refl. discriminate. }
clear B.
do 7 zstep.
zstep. if_cases B2; zify_cond B2.
- apply K.
- zstep.
replace (A2 - s + -1) with (A2 - (s + 1)) by lia. replace (A3 - s + -1) with (A3 - (s + 1)) by lia.
replace (NC + 2 * s + 2) with (NC + 2 * (s + 1)) by lia. replace (RT + 2 * s + 2) with (RT + 2 * (s + 1)) by lia.
replace (msv + 1 - s + -1) with (msv + 1 - (s + 1)) by lia.
eapply (IH (s + 1)); [lia| lia| exact K].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Cmp.
End CANSEC1.
