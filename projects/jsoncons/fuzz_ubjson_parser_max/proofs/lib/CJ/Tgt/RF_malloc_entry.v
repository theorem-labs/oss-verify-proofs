(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp F_malloc_entry.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt Require Import RMallocRep RMallocTree.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Tgt_RF_malloc_entry () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_malloc_enframe."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RF_malloc_entry.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1bool"; "1cons"; "1list"; "1nil"; "1option"; "1true"; "2and"; "2eq"; "3Z"; "0F"; "4ov_read_bytes"; "5bvmap"; "6zseq"; "7b8"]; ["8mem"; "9C1"; "9CB"; "9cell"; ":evt"; ";mkR"; ";stk"; "<MS"; "=mem_inv"; "=wa"; ">ro_cells"; ">rw_cells"; "?MMAP_THRESHOLD"; "@rsegs"; "ArDB32"; "Arclz_fn"]; ["Arclz_pow"; "Arclz_v4"; "Ardbi"; "Ardebruijn_bytes"; "Arentry_big_post"; "Arentry_post"; "BRDEBRUIJN"; "BRNEED_LOCKS"; "Brmalloc_entry"; "Cseg_rom"; "Dforallb"; "Eadd"; "Eeven"; "Ele"; "Elog2"; "Elor"]; ["Elt"; "Elxor"; "Emul"; "Epow"; "Eshiftr"; "Esub"; "0a"; "0a0"; "0a1"; "0a2"; "0a3"; "0a4"; "0a5"; "0a6"; "0a7"; "0fc"]; ["0gp"; "0k"; "0lo"; "0m"; "0n"; "0ra"; "0s0"; "0s1"; "0s10"; "0s11"; "0s2"; "0s3"; "0s4"; "0s5"; "0s6"; "0s7"]; ["0s8"; "0s9"; "0sp"; "FZ_to_bv"; "Fbv"; "Fbv_swrap"; "Fbv_unsigned"; "Fbv_wrap"; "0t0"; "0t1"; "0t2"; "0t3"; "0t4"; "0t5"; "0t6"; "0tp"]; ["0x"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition rDB32 : Z := 125613361.
Definition rdbi (k : Z) : Z := ((2 ^ k * rDB32) mod 2^32) / 2^27.
Lemma rdbi_range : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_malloc_entry "=':'8&Q=z&Q2r1%211%5241&Q@+Q0%2241%:241pT4<1").
Proof. intros k. unfold rdbi. pose proof (Z.mod_pos_bound (2^k * rDB32) (2^32) ltac:(lia)). Z.div_mod_to_equations. nia. Qed.
Definition rdebruijn_bytes : list byte :=
Eval vm_compute in (match image_bytes rsegs RDEBRUIJN 32 with Some bs => bs | None => [] end).
Lemma rdebruijn_ro : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_malloc_entry "K'RDyR0%211'6y8%511%311p051&H&Mr1%3221&Jr2&Q6(3'C(BuQ0&Q3%3221(5%116%83731%<4?;:1p0>1pT8C1").
Proof. intros m MI. apply (ro_cells_image rsegs m); [exact MI | vm_compute; reflexivity | unfold RDEBRUIJN; lia | unfold RDEBRUIJN; cbn; lia]. Qed.
Section SE.
Local Abbreviation SEC_T_rdebruijn_read := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_malloc_entry "QB'RDyR0%211'6y8%511%311p051':&H&Mr2%3221'8&Q=z%2215&Q@+Q0%2281%7241'9'4%11B%E11&<r4&I&Q;&Q6&Q2r3%211%5241%711u1%;4J:21(1(3&?%119(5%11Q5%53Q631%72E1%H3E91p0J1p0Q31pT4Q81pT8Q:1")) (only parsing).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rdebruijn_read) 0%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_rdebruijn_read) 1%nat 0%nat).
Lemma rdebruijn_read : ltac:(sec_stmt2 constr:(SEC_T_rdebruijn_read) 2%nat 0%nat).
Proof.
intros MI Hk.
destruct (rdebruijn_ro m MI) as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
pose proof (rdbi_range k) as R.
rewrite (bytes_at_read rsegs m RDEBRUIJN rdebruijn_bytes (rdbi k) 1 B) by (cbn; lia).
assert (Hn : exists n, k = Z.of_nat n /\ (n < 32)%nat) by (exists (Z.to_nat k); split; [lia|lia]).
destruct Hn as (n & -> & Hn).
Ltac solve_db := vm_compute; reflexivity.
do 32 (destruct n as [|n]; [solve_db |]). lia.
Qed.
End SE.
Lemma mul_srliw27 : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_malloc_entry "Q4':'8&Q=zr1%3221&Q@+Q0%2241%8241'9&REyQ0&QD&RG&RFyR0&RC&QB&QC+2r2%3221&N%6221%8291%;2:1%=2?1+K%@221%C2B1&Q2%11;%G3Q131p0I1pT4Q31").
Proof. intros k.
intros Hk. unfold rdbi.
assert (P : 0 < 2 ^ k <= 2 ^ 31) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_le_mono_r; lia]).
rewrite unsigned_lit by (unfold rDB32; nia).
change (bv_wrap 32 (2 ^ k * rDB32)) with ((2 ^ k * rDB32) mod 2^32).
rewrite Z.shiftr_div_pow2 by lia.
pose proof (Z.mod_pos_bound (2 ^ k * rDB32) (2^32) ltac:(lia)).
apply swrap32_small. Z.div_mod_to_equations. nia.
Qed.
Definition rclz_v4 (x : Z) : Z :=
let v1 := Z.lor (Z.shiftr x 2) x in
let v2 := Z.lor v1 (Z.shiftr x 1) in
let w2 := Z.lor (Z.shiftr v2 2) (Z.shiftr x 1) in
let w3 := Z.lor (Z.shiftr w2 4) w2 in
Z.lor (Z.shiftr w3 8) w3.
Definition rclz_pow (x : Z) : Z := Z.land (rclz_v4 x + 1) (Z.lxor (rclz_v4 x) 18446744073709551615).
Definition rclz_fn (x : Z) : bool := (rclz_pow x =? 2 ^ Z.log2 x) && (rclz_v4 x <? 2 ^ 13).
Lemma rclz_check_true : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_malloc_entry "<'9'2&Q:':&O&>+;+WoE%3221%73651(7%;3:21").
Proof. vm_compute. reflexivity. Qed.
Lemma rclz_pow_eq : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_malloc_entry "O':'8&Q=+;r1%3221&Q@+XP0%2241%8241'9&Q0r2%211&QC+2&Q>%115%4231%93C61z&Q1%11:%E231+=%;2:1%D241%J241%K291p0D1pV2N1").
Proof. intros x.
intros Hx. pose proof (forallb_zseq rclz_fn 11 8181 x rclz_check_true ltac:(lia) ltac:(lia)) as X. unfold rclz_fn in X.
apply andb_prop in X. destruct X as [X1 X2].
apply Z.eqb_eq in X1. apply Z.ltb_lt in X2. split; [exact X1| split; [|exact X2]].
unfold rclz_v4. repeat first [apply Z.lor_nonneg; split | apply Z.shiftr_nonneg]; lia.
Qed.
Lemma lxor_4k_124 : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_malloc_entry "G':'8&Q=+3r1%3221+<%5231%7231'9&QA&QBr2+4%3221+SL%6221&QE%7256%2241%;3D41p0=1pT4F1").
Proof. intros k. intros Hk. assert (H : k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12) by lia.
destruct H as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]]; reflexivity. Qed.
Lemma lor_even_1 : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_malloc_entry "F':&Q=zr1%3221'9'2&Q<r2%211(7%63521&Q?r3+1%3221&Q;%1243%=3B31p081p0@1pS>E1").
Proof. intros a. intros Ha He.
assert (D : Z.land a 1 = 0). { change 1 with (Z.ones 1). rewrite Z.land_ones by lia. change (2^1) with 2. rewrite Zeven_mod in He. apply Z.eqb_eq in He. exact He. }
rewrite <- Z.lxor_lor by exact D. rewrite <- Z.add_nocarry_lxor by exact D. reflexivity. Qed.
Definition rentry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : mem) (n : Z) : machine_state -> Prop :=
fun ms' => exists a0 a1 a2 a3 m',
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 RDEBRUIJN) (Z_to_bv 64 (size_to_class n)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9c984) fc None m' (seg_rom rsegs)
/\ rw_cells rsegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ stk rsegs m' lo (bv_unsigned sp + -48)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.
Section SE.
Local Abbreviation SEC_T_rmalloc_entry_walk := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_malloc_entry "TB'RDyR0%211&=y5%2213yQ0%711&@':'9rK&RCr1%22=1%53=41'8&Q=zr2%3221&Q@&L%2241%8241&F&Mr5r4&RFrQ5%22N1%746541+mXP0%A217r6&QErQ7%92Q51+Q@%4221%H261&Hr8%22B1&Kr9&Q7(3'C(A&?%11Q2%311(5%116%83731%<4O;:1&D&Q5rQ;rQ:rQ9rQ8rQ4rQ3rJrIrHrGrFrErDrCrBrArQ6rNrMrLr@r?r>r=r<r;r:%LQ0KJIHGFEDCBA@?>=<QB;QI:98R<765432Q91Q<&G&ErQ2rQ1rQ0rO%5OQ2Q1Q0OQIBR0NM4321A@?RCLKJIHGFEDC>=<;&Q8%RD2RO1(0%11S0&Q9%11R:%=77A5@3?1%Q<3R<?1p0Q>1p0QL1p0R01p0R81p0R;1p0RD1p0RN1pT:S51pT6S61pT8S81pT0S:1pHS=1pUNSA1pULSB1pUJSC1pUHSD1pTDSE1pTBSF1pU4SG1pU2SH1pU0SI1pTNSJ1pTLSK1pTJSL1pTHSM1pTFSN1pSNSO1pSLT01pSJT11pSHT21pSFT31pSDT41pSBT51pS@T61pT@T71pT>T81pUFT91pUDT:1pUBT;1pV0T<1pT2T=1pU6T>1pT<T?1")) (only parsing).
Variable ra : ltac:(sec_ty2 constr:(SEC_T_rmalloc_entry_walk) 0%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_rmalloc_entry_walk) 1%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_rmalloc_entry_walk) 2%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_rmalloc_entry_walk) 3%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_rmalloc_entry_walk) 4%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_rmalloc_entry_walk) 5%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_rmalloc_entry_walk) 6%nat 0%nat).
Variable s0 : ltac:(sec_ty2 constr:(SEC_T_rmalloc_entry_walk) 7%nat 0%nat).
Variable s1 : ltac:(sec_ty2 constr:(SEC_T_rmalloc_entry_walk) 8%nat 0%nat).
Variable a0 : ltac:(sec_ty2 constr:(SEC_T_rmalloc_entry_walk) 9%nat 0%nat).
Variable a1 : ltac:(sec_ty2 constr:(SEC_T_rmalloc_entry_walk) 10%nat 0%nat).
Variable a2 : ltac:(sec_ty2 constr:(SEC_T_rmalloc_entry_walk) 11%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_rmalloc_entry_walk) 12%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_rmalloc_entry_walk) 13%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_rmalloc_entry_walk) 14%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_rmalloc_entry_walk) 15%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_rmalloc_entry_walk) 16%nat 0%nat).
Variable s2 : ltac:(sec_ty2 constr:(SEC_T_rmalloc_entry_walk) 17%nat 0%nat).
Variable s3 : ltac:(sec_ty2 constr:(SEC_T_rmalloc_entry_walk) 18%nat 0%nat).
Variable s4 : ltac:(sec_ty2 constr:(SEC_T_rmalloc_entry_walk) 19%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_rmalloc_entry_walk) 20%nat 0%nat).
Variable s6 : ltac:(sec_ty2 constr:(SEC_T_rmalloc_entry_walk) 21%nat 0%nat).
Variable s7 : ltac:(sec_ty2 constr:(SEC_T_rmalloc_entry_walk) 22%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_rmalloc_entry_walk) 23%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_rmalloc_entry_walk) 24%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_rmalloc_entry_walk) 25%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_rmalloc_entry_walk) 26%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_rmalloc_entry_walk) 27%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_rmalloc_entry_walk) 28%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_rmalloc_entry_walk) 29%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_rmalloc_entry_walk) 30%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_rmalloc_entry_walk) 31%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_rmalloc_entry_walk) 32%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rmalloc_entry_walk) 33%nat 0%nat).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_rmalloc_entry_walk) 34%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_rmalloc_entry_walk) 35%nat 0%nat).
Lemma rmalloc_entry_walk : ltac:(sec_stmt2 constr:(SEC_T_rmalloc_entry_walk) 36%nat 0%nat).
Proof.
intros HA N ST ILO LO MI NL. subst a0.
pose proof (size_to_class_props n N) as (SCR & SFIT & LG). unfold MMAP_THRESHOLD in N.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold rmalloc_entry, RNEED_LOCKS in *.
step. carve_frame 48%nat ST. step. step. step. step. step. step.
step. step. step.
step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
clear K0.
step. step. step. step. step.
step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
clear K1.
step. step. step. step. step.
rewrite (unsigned_lit (n + 3)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
set (q := (n + 3) / 16) in *. assert (QR : 0 <= q < 8191) by (subst q; Z.div_mod_to_equations; lia).
assert (STC : size_to_class n = stc_q q) by (apply size_to_class_q; lia).
assert (LOCKJ : forall (a0' a1' a2' a3' : word) (sc : Z) (mj : mem),
sc = size_to_class n ->
mem_inv rsegs mj -> rw_cells rsegs mj (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> stk rsegs mj lo (bv_unsigned sp + -48) ->
munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m mj -> wmono rsegs m mj -> rw_cells rsegs mj 954179 [C1 (b8 0)] ->
evt rsegs (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 954552) a0' a1' a2' a3' a4 a5 a6 a7
s2 (Z_to_bv 64 110016) (Z_to_bv 64 sc) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9c96c) fc None mj (seg_rom rsegs))).
{ intros a0' a1' a2' a3' sc mj -> MIj FRj STj MUj WMj NLj.
step. step. rewrite ?zxb_b8 by lia. step. if_cases KL; zify_cond KL. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in KL by lia. lia. }
apply evt_done. unfold rentry_post, RMLOCK, RDEBRUIJN. do 5 eexists. split; [reflexivity|].
split; [exact FRj|]. split; [exact STj|]. split; [exact MUj|]. split; [exact WMj| exact MIj]. }
step. if_cases K2; zify_cond K2; rewrite ?(unsigned_lit n) in K2 by lia.
-
apply LOCKJ; try assumption.
rewrite STC. unfold stc_q. replace (q <? 10) with true by (symmetry; apply Z.ltb_lt; subst q; Z.div_mod_to_equations; lia). reflexivity.
-
assert (Q10 : 10 <= q) by (subst q; Z.div_mod_to_equations; lia).
step. rewrite ?(unsigned_lit q) by lia. set (x := q + 1) in *. assert (XR : 11 <= x < 8192) by lia.
destruct (rclz_pow_eq x XR) as [PW RV4].
step.
step. rewrite (unsigned_lit x), srliw_small by lia.
pose proof (shiftr_small 13 x 1 ltac:(lia) ltac:(lia)) as R1. pose proof (shiftr_small 13 x 2 ltac:(lia) ltac:(lia)) as R2.
step. rewrite (unsigned_lit (Z.shiftr x 2)), (unsigned_lit x) by lia.
set (v1 := Z.lor (Z.shiftr x 2) x). assert (RX : 0 <= x < 2 ^ 13) by lia. pose proof (lor_small 13 _ _ ltac:(lia) R2 RX) as RV1. fold v1 in RV1.
step. rewrite (unsigned_lit x), srliw_small by lia.
step.
step. rewrite (unsigned_lit v1), (unsigned_lit (Z.shiftr x 1)) by lia.
set (v2 := Z.lor v1 (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) RV1 R1) as RV2. fold v2 in RV2.
step. rewrite (unsigned_lit v2), srliw_small by lia. pose proof (shiftr_small 13 v2 2 RV2 ltac:(lia)) as R3.
step. rewrite (unsigned_lit (Z.shiftr v2 2)), (unsigned_lit (Z.shiftr x 1)) by lia.
set (w2 := Z.lor (Z.shiftr v2 2) (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) R3 R1) as RW2. fold w2 in RW2.
step. rewrite (unsigned_lit w2) by lia. pose proof (shiftr_small 13 w2 4 RW2 ltac:(lia)) as R4.
step. rewrite (unsigned_lit (Z.shiftr w2 4)), (unsigned_lit w2) by lia.
set (w3 := Z.lor (Z.shiftr w2 4) w2). pose proof (lor_small 13 _ _ ltac:(lia) R4 RW2) as RW3. fold w3 in RW3.
step. rewrite (unsigned_lit w3) by lia. pose proof (shiftr_small 13 w3 8 RW3 ltac:(lia)) as R5.
step. rewrite (unsigned_lit (Z.shiftr w3 8)), (unsigned_lit w3) by lia.
set (w4 := Z.lor (Z.shiftr w3 8) w3). pose proof (lor_small 13 _ _ ltac:(lia) R5 RW3) as RW4. fold w4 in RW4.
assert (EW4 : w4 = rclz_v4 x) by reflexivity.
step. step. step.
rewrite (unsigned_lit w4), Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (w4 * 2 ^ 33)) by lia.
replace ((w4 * 2 ^ 33) ≫ 49) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
rewrite (unsigned_lit 0), Z.lor_0_l by lia.
step. step. rewrite (unsigned_lit w4) by lia.
step. rewrite (unsigned_lit (w4 + 1)) by lia. rewrite (unsigned_lit (Z.lxor w4 18446744073709551615)) by (rewrite zb_lxor_ones by lia; lia).
change (Z.land (w4 + 1) (Z.lxor w4 18446744073709551615)) with (rclz_pow x). rewrite PW.
set (k := Z.log2 x) in *.
assert (P2 : 0 < 2 ^ k < 2 ^ 13) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
assert (EK : k = Z.log2 x) by reflexivity. clearbody k. clear PW RV4 EW4 RW4 R5 RW3 R4 RW2 R3 RV2 RV1 R1 R2. subst w4 w3 w2 v2 v1.
assert (EX : x = q + 1) by reflexivity. clearbody x.
assert (K13 : 3 <= k <= 12) by (apply LG; lia).
step. rewrite (unsigned_lit (2 ^ k)) by lia. change 125613361 with rDB32.
step. rewrite (mul_srliw27 k) by lia.
pose proof (rdbi_range k) as DR.
step. rewrite ?(unsigned_lit (rdbi k)) by lia.
lazymatch goal with HI : mem_inv rsegs ?mc |- _ => pose proof (rdebruijn_read mc k HI ltac:(lia)) as DBR; unfold RDEBRUIJN in DBR end.
step. rewrite ?zxb_b8 by lia. clear DBR.
step. step. step. rewrite (wz_unsigned k), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
step.
rewrite (unsigned_lit (k * 4)), lxor_4k_124 by lia.
set (i := 4 * k - 4). assert (IR : 8 <= i <= 44) by lia.
replace (124 - 4 * k) with (120 - i) by lia.
assert (STQ : stc_q q = (let i1 := if size_class (i + 1) <? x then i + 2 else i in if size_class i1 <? x then i1 + 1 else i1)).
{ unfold stc_q. replace (q <? 10) with false by (symmetry; apply Z.ltb_ge; lia). rewrite <- EX, <- EK. reflexivity. }
assert (IEV : Z.even i = true) by (subst i; rewrite Z.even_sub, Z.even_mul; reflexivity).
clearbody i. clear EK.
pose proof (size_class_range (i + 1) ltac:(lia)) as SR1.
step. rewrite (unsigned_lit (120 - i)) by lia. replace (121 - (120 - i)) with (i + 1) by lia.
step. rewrite (unsigned_lit (i + 1)), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
step. step. replace (110048 + (i + 1) * 2) with (110048 + 2 * (i + 1)) by lia.
lazymatch goal with HI : mem_inv rsegs ?mc |- _ => pose proof (rsize_classes_read mc (i + 1) HI ltac:(lia)) as RS1; unfold RSIZE_CLASSES in RS1 end.
step. rewrite ?zx16_wz by lia. clear RS1.
assert (J1 : forall (i1 c : Z) (mj : mem),
i1 = (if size_class (i + 1) <? x then i + 2 else i) -> c = i1 - i + 120 ->
mem_inv rsegs mj -> rw_cells rsegs mj (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> stk rsegs mj lo (bv_unsigned sp + -48) ->
munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m mj -> wmono rsegs m mj -> rw_cells rsegs mj 954179 [C1 (b8 0)] ->
evt rsegs (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 954552)
(Z_to_bv 64 (120 - i)) (Z_to_bv 64 110048) (Z_to_bv 64 c) (Z_to_bv 64 (110048 + 2 * (i + 1))) a4 a5 a6 a7
s2 (Z_to_bv 64 110016) (Z_to_bv 64 q) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9c950) fc None mj (seg_rom rsegs))).
{ intros i1 c mj Hi1 Hc MIj FRj STj MUj WMj NLj.
assert (I1R : 8 <= i1 <= 46 /\ Z.even i1 = true).
{ subst i1. destruct (size_class (i + 1) <? x); (split; [lia|]); rewrite ?Z.even_add, ?IEV; reflexivity. }
destruct I1R as [I1R I1E].
pose proof (size_class_range i1 ltac:(lia)) as SR2.
step. rewrite (unsigned_lit c), (unsigned_lit (120 - i)) by lia. replace (c - (120 - i)) with i1 by lia.
step. rewrite (unsigned_lit i1), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
step. replace (110048 + i1 * 2) with (110048 + 2 * i1) by lia.
pose proof (rsize_classes_read mj i1 MIj ltac:(lia)) as RS2. unfold RSIZE_CLASSES in RS2.
step. rewrite ?zx16_wz by lia. clear RS2.
step. rewrite v_sltu_b2z, (unsigned_lit q), (wz_unsigned (size_class i1)) by lia.
step. step.
destruct (Z.ltb_spec q (size_class i1)) as [LT|GE]; cbn [Z.b2z].
* rewrite (unsigned_lit 1), (unsigned_lit i1) by lia. change (Z.lxor 1 1) with 0. rewrite (unsigned_lit 0), Z.lor_0_r by lia.
apply LOCKJ; try assumption. rewrite STC, STQ. cbv zeta. rewrite <- Hi1.
replace (size_class i1 <? x) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
* rewrite (unsigned_lit 0), (unsigned_lit i1) by lia. change (Z.lxor 0 1) with 1. rewrite (unsigned_lit 1), (lor_even_1 i1 ltac:(lia) I1E) by lia.
apply LOCKJ; try assumption. rewrite STC, STQ. cbv zeta. rewrite <- Hi1.
replace (size_class i1 <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
step. if_cases K3; zify_cond K3; rewrite ?(unsigned_lit q), ?(wz_unsigned (size_class (i + 1))) in K3 by lia.
+
step. eapply J1; try eassumption; [reflexivity|]. replace (size_class (i + 1) <? x) with false by (symmetry; apply Z.ltb_ge; lia). lia.
+
step. step. eapply J1; try eassumption; [reflexivity|]. replace (size_class (i + 1) <? x) with true by (symmetry; apply Z.ltb_lt; lia). lia.
Qed.
End SE.
Definition rentry_big_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : mem) (n : Z) : machine_state -> Prop :=
fun ms' => exists a1 m',
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 131052) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9c7ec) fc None m' (seg_rom rsegs)
/\ rw_cells rsegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ stk rsegs m' lo (bv_unsigned sp + -48)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.
Section SE.
Local Abbreviation SEC_T_rentry_big_walk := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_malloc_entry "T8'RDyR0%211&=y5%2213yQ0%711&@':'9rK&RCr1%22=1%53=41'8&Q=&Lr2%3221&Q@&QC+2+Q0%3221%5271%;271&F&Mr5r4&RFrQ5%22Q11%746541+mXP0%D217r6&QErQ7%92Q81+Q@%4221%K261&Hr8%22B1&D&Q4rQ:rQ9rQ8rQ3rQ2rIrHrGrFrErDrCrBrAr@rQ6rQ4rOrNrMrLrJr?r>r=r<r;r:r9r7%OQ2NMLQ8KJIHGFEDCBA@?Q?>=<;:R59876543Q221&G&ErQ1rQ0%3OQ3Q2Q1Q=DQDCQ0O21BA@?R:>NMLKJIHGFE=<;:&Q8%R;2RF1(0%11RG&Q9%11QN%;77@5?3>1%Q=3R0=1p0Q?1p0QC1p0QK1p0QN1p0R71p0RD1pT:RK1pT6RL1pT8RN1pT0S01pHS31pUNS71pULS81pUJS91pUHS:1pTDS;1pTBS<1pU4S=1pU2S>1pU0S?1pTNS@1pTLSA1pTJSB1pTHSC1pTFSD1pSNSE1pSLSF1pSJSG1pSHSH1pSFSI1pSDSJ1pSBSK1pS@SL1pT@SM1pT>SN1pUFSO1pUDT01pUBT11pV0T21pT2T31pU6T41pT<T51")) (only parsing).
Variable ra : ltac:(sec_ty2 constr:(SEC_T_rentry_big_walk) 0%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_rentry_big_walk) 1%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_rentry_big_walk) 2%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_rentry_big_walk) 3%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_rentry_big_walk) 4%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_rentry_big_walk) 5%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_rentry_big_walk) 6%nat 0%nat).
Variable s0 : ltac:(sec_ty2 constr:(SEC_T_rentry_big_walk) 7%nat 0%nat).
Variable s1 : ltac:(sec_ty2 constr:(SEC_T_rentry_big_walk) 8%nat 0%nat).
Variable a0 : ltac:(sec_ty2 constr:(SEC_T_rentry_big_walk) 9%nat 0%nat).
Variable a1 : ltac:(sec_ty2 constr:(SEC_T_rentry_big_walk) 10%nat 0%nat).
Variable a2 : ltac:(sec_ty2 constr:(SEC_T_rentry_big_walk) 11%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_rentry_big_walk) 12%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_rentry_big_walk) 13%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_rentry_big_walk) 14%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_rentry_big_walk) 15%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_rentry_big_walk) 16%nat 0%nat).
Variable s2 : ltac:(sec_ty2 constr:(SEC_T_rentry_big_walk) 17%nat 0%nat).
Variable s3 : ltac:(sec_ty2 constr:(SEC_T_rentry_big_walk) 18%nat 0%nat).
Variable s4 : ltac:(sec_ty2 constr:(SEC_T_rentry_big_walk) 19%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_rentry_big_walk) 20%nat 0%nat).
Variable s6 : ltac:(sec_ty2 constr:(SEC_T_rentry_big_walk) 21%nat 0%nat).
Variable s7 : ltac:(sec_ty2 constr:(SEC_T_rentry_big_walk) 22%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_rentry_big_walk) 23%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_rentry_big_walk) 24%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_rentry_big_walk) 25%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_rentry_big_walk) 26%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_rentry_big_walk) 27%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_rentry_big_walk) 28%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_rentry_big_walk) 29%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_rentry_big_walk) 30%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_rentry_big_walk) 31%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_rentry_big_walk) 32%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_rentry_big_walk) 33%nat 0%nat).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_rentry_big_walk) 34%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_rentry_big_walk) 35%nat 0%nat).
Lemma rentry_big_walk : ltac:(sec_stmt2 constr:(SEC_T_rentry_big_walk) 36%nat 0%nat).
Proof.
intros HA N ST ILO LO MI. subst a0. unfold MMAP_THRESHOLD in N.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold rmalloc_entry.
step. carve_frame 48%nat ST. step. step. step. step. step. step.
step. step. step.
step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
clear K0.
step. step. step. step. step.
step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
clear K1.
apply evt_done. unfold rentry_big_post, RMLOCK. do 2 eexists. split; [reflexivity|].
lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -48) _ |- _ => split; [exact H|] end.
repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.
End SE.
End CEIL_WRAP_1.
