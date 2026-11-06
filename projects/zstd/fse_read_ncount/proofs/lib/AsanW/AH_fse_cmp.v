(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseHarness.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg ABase RtCells AH_fse_kit AH_fse_pure.
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
Lemma idx2_valA : forall s, 0 <= s < 2147483648 -> Z.shiftr (Z.shiftl s 32 mod 18446744073709551616) 31 = 2 * s.
Proof.
intros s Hs. Local Ltac2 Set LiaHints.tbl := fun () => "0040=17303709668.941201450270.244015170411.27224926811.2 00000600:00;00<S1H2H0S2HsSS".
rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
change (2^32) with 4294967296. change (2^31) with 2147483648.
rewrite Z.mod_small by lia. Z.div_mod_to_equations. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma idx2_valA' : forall s, 0 <= s < 2147483648 -> Z.shiftr (Z.land (Z.shiftl s 32) 18446744073709551615) 31 = 2 * s.
Proof.
intros s Hs. change 18446744073709551615 with (Z.ones 64). Local Ltac2 Set LiaHints.tbl := fun () => "0010=35497641323.2000001S".
rewrite Z.land_ones by lia.
change (2^64) with 18446744073709551616. apply idx2_valA. exact Hs.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma idx1_valA : forall s, 0 <= s < 2147483648 -> Z.shiftr (Z.shiftl s 32 mod 18446744073709551616) 32 = s.
Proof.
intros s Hs. Local Ltac2 Set LiaHints.tbl := fun () => "0030=41201450270.241316647297.944015170411.200000400:00;S2HsS1H2H0S".
rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
change (2^32) with 4294967296. rewrite Z.mod_small by lia. Z.div_mod_to_equations. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma idx1_valA' : forall s, 0 <= s < 2147483648 -> Z.shiftr (Z.land (Z.shiftl s 32) 18446744073709551615) 32 = s.
Proof.
intros s Hs. change 18446744073709551615 with (Z.ones 64). Local Ltac2 Set LiaHints.tbl := fun () => "0010=35497641323.2000001S".
rewrite Z.land_ones by lia.
change (2^64) with 18446744073709551616. apply idx1_valA. exact Hs.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section CANSEC1. Context {rc : runConstT}.
Section Cmp.
Variables (RNG : footprint) (gp tp sp s0 s1 s2 s4 s7 s8 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32).
Variables (m : amem) (NC RT : Z) (nc rt : list Z) (msv : Z).
Variable POST : machine_state -> Prop.
Hypothesis MSV : 0 <= msv <= 255.
Hypothesis LNC : length nc = 256%nat.
Hypothesis LRT : length rt = 256%nat.
Hypothesis NCB : bytes_at asegs m NC (u16s (map (Z_to_bv 64) nc)).
Hypothesis RTB : bytes_at asegs m RT (u16s (map (Z_to_bv 64) rt)).
Hypothesis AGREE : forall i, 0 <= i <= msv -> Znth i rt = Znth i nc.
Hypothesis MI : mem_inv asegs m.
Hypothesis NCR : 0 <= NC /\ NC + 512 + 8 <= KEND /\ NC mod 8 = 0.
Hypothesis RTR : 0 <= RT /\ RT + 512 + 8 <= KEND /\ RT mod 8 = 0.
Hypothesis UNC : unpoisoned m NC (NC + 512).
Hypothesis URT : unpoisoned m RT (RT + 512).
Hypothesis RNC : rng RNG NC 512.
Hypothesis RRT : rng RNG RT 512.
Hypothesis RNCS : rng RNG (shad NC) 64.
Hypothesis RRTS : rng RNG (shad RT) 64.
Notation STpc pc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 :=
(MS (mkR x1 sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17
s2 (Z_to_bv 64 2147450880) s4 (Z_to_bv 64 NC) (Z_to_bv 64 RT) s7 s8 (Z_to_bv 64 msv) s10 s11 x28 x29 x30 x31)
FR (Z_to_bv 64 pc) fc None m (seg_rom asegs)).
#[using="nc rt MSV LNC LRT NCB RTB AGREE NCR RTR UNC URT RNC RRT RNCS RRTS"] Lemma cmp_loopA : forall f s (x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
0 <= s <= msv -> msv - s < Z.of_nat f ->
(forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
evtF asegs RNG POST (STpc 0x812d4 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31)) ->
evtF asegs RNG POST (STpc 0x81260 x1 x5 x6 x7 x10 x11 (Z_to_bv 64 s) x13 x14 x15 x16 x17 x28 x29 x30 x31).
Proof.
induction f as [|f IH]; intros s x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 HS HF K.
{ exfalso. cbn in HF. Local Ltac2 Set LiaHints.tbl := fun () => "00X0?11447729958.10711447729958.10811866103177.71 11869970069.70 11874844849.81 1304312772.81  1304312779.81  1624184818.74  18606756866.79 18606756866.80 18606756868.76 19335898384.80 19567732400.81 23683590488.21 24606477382.73 25678300509.72 25678574719.73 2597469165.81  26274314084.21 28022624402.79 29786656982.64 29786659037.67 29788510300.66 29788510301.65 31827797969.75 36277103321.79 37694598650.79 38898666155.68 42132665045.74 43324722563.80 5468053843.75  5490622699.80  59314923118.56 59435130664.82 65453664584.69 65747618005.21 67148971104.75 6755820734.73  7604148560.75  9178932959.21  00000100200I00`01701801901T01o02J02e03@03_04304G04b05=05Q05i05j06>06R06f07:07N07i07j08E08Y08Z09409509D09c0:>0:R0:m0;A0;Y0;mFFS3LNC3LRT2HS2HF3NC03RT0S3LNC3LRT2HS2HF3NC03RT0S3LNC3LRT2HS2HF3NC03RT0FFS3MSV3LNC3LRT2HS2HF3NC03RT0S3MSV3LNC3LRT2HS2HF3NC03RT0S3MSV3LNC3LRT2HS2HF3NC03RT0S3MSV3LNC3LRT2HS2HF3NC03RT0S3MSV3LNC3LRT2HS2HF3NC03RT0S3MSV3LNC3LRT2HS2HF3NC03RT03RTES3MSV2HS3NC81H2H02H4S3LNC3LRT2HF3NC03RT0S3MSV3LNC3LRT2HS2HF3NC03RT0S3MSV3LNC3LRT2HS2HF3NC03RT0S3LNC3LRT2HF3NC03RT0S3MSV2HS3NC81H2H42H53RT8FS3LNC3LRT2HF3NC03RT0S3LNC3LRT2HF3NC03RT0S3LNC3LRT2HF3NC03RT0S3LNC3LRT2HF3NC03RT0S3LNC3LRT2HF3NC03RT0S3MSV3LNC3LRT2HS2HF3NC03RT0FS3MSV3LNC3LRT2HS2HF3NC03RT0S3LNC3LRT2HF3NC03RT0FS3LNC3LRT2HS2HF3NC03RT02B2FS3LNC3LRT2HS2HFS3MSV3LNC3LRT2HS2HF3NC03NCE3RT0S3MSV3LNC3LRT2HS2HF3NC03RT0S3MSV2HS3RT81H2H02H4S3MSV3LNC3LRT2HS2HF3NC03RT0S3LNC3LRT2HF3NC03RT0S3MSV3LNC3LRT2HF3NC03RT0S2HS3NC81H2H42H53RT8".
lia. }
destruct NCR as (NC0 & NCE & NC8). destruct RTR as (RT0 & RTE & RT8). unfold KEND in *.
assert (ACC1 : acc_in RNG (Z_to_bv 64 (Z.shiftr (NC + 2 * s) 3 + 2147450880), 1%nat)).
{ apply (rng_acc_litZ' RNG _ _ _ 1 1 RNCS eq_refl eq_refl). rewrite shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF. change (2^3) with 8.
clear - NC8 HS MSV NC0. Z.div_mod_to_equations. lia. }
assert (ACC2 : acc_in RNG (Z_to_bv 64 (Z.shiftr (RT + 2 * s) 3 + 2147450880), 1%nat)).
{ apply (rng_acc_litZ' RNG _ _ _ 1 1 RRTS eq_refl eq_refl). rewrite shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF. change (2^3) with 8.
clear - RT8 HS MSV RT0. Z.div_mod_to_equations. lia. }
assert (RD1 : ov_read_bytes asegs m (wa (Z.shiftr (NC + 2 * s) 3 + 2147450880)) 1 = Some [Z_to_bv 8 0]).
{ apply (unpoisoned_full_rd asegs m NC (NC + 512)); [exact UNC| |];
rewrite ?shad_div, ?Z.shiftr_div_pow2 by lia; unfold ASHOFF; change (2^3) with 8; clear - NC8 HS MSV NC0; Z.div_mod_to_equations; lia. }
assert (RD2 : ov_read_bytes asegs m (wa (Z.shiftr (RT + 2 * s) 3 + 2147450880)) 1 = Some [Z_to_bv 8 0]).
{ apply (unpoisoned_full_rd asegs m RT (RT + 512)); [exact URT| |];
rewrite ?shad_div, ?Z.shiftr_div_pow2 by lia; unfold ASHOFF; change (2^3) with 8; clear - RT8 HS MSV RT0; Z.div_mod_to_equations; lia. }
assert (NTHN : nth_error (map (Z_to_bv 64) nc) (Z.to_nat s) = Some (Z_to_bv 64 (Znth s nc))).
{ rewrite nth_error_map. unfold Znth. rewrite (nth_error_nth' nc 0) by lia. reflexivity. }
assert (NTHR : nth_error (map (Z_to_bv 64) rt) (Z.to_nat s) = Some (Z_to_bv 64 (Znth s nc))).
{ rewrite nth_error_map. rewrite <- (AGREE s HS). unfold Znth. rewrite (nth_error_nth' rt 0) by lia. reflexivity. }
pose proof (u16ro_read asegs m NC _ s _ (wa (NC + 2 * s)) NCB NTHN ltac:(lia) eq_refl) as RN.
pose proof (u16ro_read asegs m RT _ s _ (wa (RT + 2 * s)) RTB NTHR ltac:(lia) eq_refl) as RR.
zstep. zstep. first [rewrite idx2_valA by lia | rewrite idx2_valA' by lia].
zstep. zstep. zstep. zstep.
zstep. if_cases B0; zify_cond B0; [exfalso; apply B0; reflexivity|].
zstep. first [rewrite idx1_valA by lia | rewrite idx1_valA' by lia | rewrite land_ones32A by lia | idtac].
zstep. first [rewrite land_ones32A by lia | idtac]. rewrite (Z.shiftl_mul_pow2 s 1) by lia. change (2^1) with 2. replace (s * 2) with (2 * s) by lia.
zstep. zstep. zstep. zstep. zstep.
zstep. if_cases B1; zify_cond B1; [exfalso; apply B1; reflexivity|].
zstep.
zstep. if_cases B. { exfalso. revert B. rewrite bv_eqb_refl. discriminate. }
clear B.
zstep. sw32 (s + 1).
zstep. if_cases B2; zify_cond B2.
- apply K.
- zstep. eapply (IH (s + 1)); [lia| lia| exact K].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Cmp.
End CANSEC1.
