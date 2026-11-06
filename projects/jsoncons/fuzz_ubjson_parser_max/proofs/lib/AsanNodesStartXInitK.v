(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib
AsanAcct AsanAcctShape.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AxSymExec3K AxSymExec3SoundK AxSymRun3K AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanNodesAuxK AsanStartLoops AsanNodesStartXK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2K. Import AX2SK. Import APK. Import APSK.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__AsanNodesStartXInitK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanInitK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanK.APK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundK.APSK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3K.AX2K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1length"; "1option"; "2and"; "2eq"; "3Z"; "0E"; "0FS0"; "4total_arg_bytes"; "5sp_window_hi"; "5sp_window_lo"; "0M"; "6LIMIT"; "6argH0"; "7NX0"; "7V_ENVC"]; ["7XEnvScan"; "7XLayout"; "7XPnScan"; "7e_envp"; "7e_sp0"; "7e_str0"; "8uE"; "8x_stmt"; "9env"; "9ev"; ":wrap_mem"; "0SINV"; ";add"; ";le"; ";lt"; ";mul"]; [";of_nat"; "0a"; "0argc"; "0argv"; "0envc"; "0envp"; "0hw"; "0ph"; "0rdraw"; "0s0"; "0scfg"; "0segs"; "0sp"; "<Z_to_bv"; "<bv"; "<bv_unsigned"]; ["0uid"; "0usp"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section GenericInit.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Variable A : atable.
Variable ph : PhdrInfo.
Hypothesis SEGS_wx : wx_segs_nowrap segs.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment segs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_ok A.
Variables we1 we2 we3 wp0 wp1 wp2 wp3 wp4 : bv 32.
Hypothesis Xenv : 0 <= x_envscan A /\ x_envscan A + 12 < 2 ^ 64 /\ x_envscan_k A = x_envscan A + 12.
Hypothesis Fe1 : fetch_word segs (Z_to_bv 64 (x_envscan A)) = Some we1.
Hypothesis Fe2 : fetch_word segs (Z_to_bv 64 (x_envscan A + 4)) = Some we2.
Hypothesis Fe3 : fetch_word segs (Z_to_bv 64 (x_envscan A + 8)) = Some we3.
Hypothesis Ee : is_ecall we1 = false /\ is_ecall we2 = false /\ is_ecall we3 = false.
Hypothesis De1 : decode_any we1 = Some (Load SZ8 true 10 9 0, 4%Z).
Hypothesis De2 : decode_any we2 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Hypothesis De3 : decode_any we3 = Some (Branch BC_NE 10 0 8184, 4%Z).
Hypothesis Xpn : 8 <= x_pnscan A /\ x_pnscan A + 12 < 2 ^ 64 /\ x_pnscan_k A = x_pnscan A + 12.
Hypothesis Fp0 : fetch_word segs (Z_to_bv 64 (x_pnscan A - 8)) = Some wp0.
Hypothesis Fp1 : fetch_word segs (Z_to_bv 64 (x_pnscan A - 4)) = Some wp1.
Hypothesis Fp2 : fetch_word segs (Z_to_bv 64 (x_pnscan A)) = Some wp2.
Hypothesis Fp3 : fetch_word segs (Z_to_bv 64 (x_pnscan A + 4)) = Some wp3.
Hypothesis Fp4 : fetch_word segs (Z_to_bv 64 (x_pnscan A + 8)) = Some wp4.
Hypothesis Ep : is_ecall wp0 = false /\ is_ecall wp1 = false /\ is_ecall wp2 = false /\ is_ecall wp3 = false /\ is_ecall wp4 = false.
Hypothesis Dp0 : decode_any wp0 = Some (Store SZ8 10 11 0, 4%Z).
Hypothesis Dp1 : decode_any wp1 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Hypothesis Dp2 : decode_any wp2 = Some (Load SZ1 false 13 11 4095, 4%Z).
Hypothesis Dp3 : decode_any wp3 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Hypothesis Dp4 : decode_any wp4 = Some (Branch BC_NE 13 0 8180, 4%Z).
Variable sp : word.
Variable rdraw : EntryDraw.
Variable brk0 mbase : word.
Variable argv envp : list (list byte).
Variable fs : Fs.Fs.
Variable stdin : InputStream.
Variable FS0 : Fs.Fs.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Variable uid : word.
Variable hw : word.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Variable SINV : env -> (word -> option byte) -> Prop.
Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 ph sp rdraw brk0 argv envp uid hw E M.
Hypothesis SINV_frame : forall E M M', (forall a, argH0 ph sp rdraw argv envp uid hw E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.
Let usp := bv_unsigned sp.
Let argc := Z.of_nat (length argv).
Let envc := Z.of_nat (length envp).
Let s0 := nth 0 argv [].
Lemma sp_lo : ltac2:(TCodec.tc2 tcn__AsanNodesStartXInitK "7&M&:&Q?yR0vQ<%3221%6251").
Proof. destruct Hsp as [H _]. exact H. Qed.
Lemma sp_hi : ltac2:(TCodec.tc2 tcn__AsanNodesStartXInitK "7&M&Q?yR0vQ<%3221&9%6221").
Proof. destruct Hsp as (_ & H & _). exact H. Qed.
Lemma SINV0_vals : ltac2:(TCodec.tc2 tcn__AsanNodesStartXInitK "QA'H'Q>yR0%211'2y8%511%311p051vKr2r1%3221'3'4'5&Fr3&C%3221&LvQA&O+8vQ2%3221%6251+@%8221%?3>:1&I&?%22?1&Q=vQ4%22Q11%F3Q141&E%F2E1%A2@5%D2>1+UH%F221%M3L51%O281%Q02@1p0Q21pHQ71p>Q@1").
Proof.
intros E M HS. apply SINV_SINV0 in HS. destruct HS as [Hev _].
pose proof (u_e_envp ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as U1.
pose proof (u_e_str0 ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as U3.
pose proof (uE0 ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as (_ & _ & _ & U2 & _).
assert (Hev7 : forall n, (n < NX0)%nat -> ev E n = ev (E0 ph sp rdraw brk0 argv envp uid hw) n) by (intros n Hn; apply Hev; exact Hn).
unfold uE in *.
rewrite (edenot_ev_agree NX0 E (E0 ph sp rdraw brk0 argv envp uid hw) e_envp eq_refl Hev7).
rewrite (edenot_ev_agree NX0 E (E0 ph sp rdraw brk0 argv envp uid hw) e_str0 eq_refl Hev7).
split; [exact U1|]. split; [|exact U3].
change (ev E V_ENVC) with (edenot E (EVar V_ENVC)).
rewrite (edenot_ev_agree NX0 E (E0 ph sp rdraw brk0 argv envp uid hw) (EVar V_ENVC) eq_refl Hev7).
apply bv_eq. rewrite U2. unfold envc. destruct Hve as [H _]. rewrite u64_lit by lia. reflexivity.
Qed.
Lemma SINV0_sp0 : ltac2:(TCodec.tc2 tcn__AsanNodesStartXInitK "H'H'Q>yR0%211'2y8%511%311p051vKr2r1%3221'4'5&Fr3&D%3221vQA%73621p091pH>1p>G1").
Proof.
intros E M HS. apply SINV_SINV0 in HS. destruct HS as [Hev _].
assert (Hev7 : forall n, (n < NX0)%nat -> ev E n = ev (E0 ph sp rdraw brk0 argv envp uid hw) n) by (intros n Hn; apply Hev; exact Hn).
unfold uE. rewrite (edenot_ev_agree NX0 E (E0 ph sp rdraw brk0 argv envp uid hw) e_sp0 eq_refl Hev7).
exact (u_e_sp0 ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit).
Qed.
Lemma SINV0_envp : ltac2:(TCodec.tc2 tcn__AsanNodesStartXInitK "QD'H'Q>yR0%211'2y8%511%311p051vKr3r2%3221'3&M&LvQA&O+8vQ2%3221%6251+@%8221&Q?%12G>%<231&NvQ4%<2;1%?271%@21=%5271%D271'4r4%11J&JvQ7vQ<vQ3vQ5vQ@vQ6vQ8%887654321Q3%<3Q7:1p0>1p0Q41pR4Q>1pHQ:1p>QC1").
Proof.
intros E M a HS Ha. pose proof (SINV0_sp0 E M HS) as US. apply SINV_SINV0 in HS. destruct HS as [_ HM]. apply HM. unfold argH0.
pose proof (proj1 Hva) as AV. fold argc in AV.
apply andb_true_intro. split; [apply Z.leb_le; rewrite US; lia|].
apply orb_true_intro. left. apply orb_true_intro. left.
apply andb_true_intro. unfold usp, argc, envc in Ha. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Lemma s0_fits : ltac2:(TCodec.tc2 tcn__AsanNodesStartXInitK "@&M&L&Q0&1'Q>y8%211vQ9%5221%711+1%:221&8vQ3%211%?241").
Proof.
unfold s0. rewrite total_arg_bytes_Z. destruct argv as [|a r]; [destruct Hva as [H _]; cbn in H; lia|].
cbn [nth]. rewrite total_arg_bytes_cons. lia.
Qed.
Lemma SINV0_str0 : ltac2:(TCodec.tc2 tcn__AsanNodesStartXInitK "QH'H'Q>yR0%211'2y8%511%311p051vKr3r2%3221'3&M&LvQA&O+8vQ2%3221%6251vQ4%6251%9231+UH%;221&Q?%12JA%?231&Q0&1vQ9%22K1%411%D291%F281%H281'4r4%11N&JvQ7vQ<vQ3vQ5vQ@vQ6vQ8%887654321Q7%<3Q;:1p0>1p0Q81pR4QB1pHQ>1p>QG1").
Proof.
intros E M a HS Ha. pose proof (SINV0_sp0 E M HS) as US. apply SINV_SINV0 in HS. destruct HS as [_ HM]. apply HM. unfold argH0.
pose proof (proj1 Hva) as AV. fold argc in AV. pose proof (proj1 Hve) as EV. fold envc in EV.
apply andb_true_intro. split; [apply Z.leb_le; rewrite US; lia|].
apply orb_true_intro. left. apply orb_true_intro. right.
pose proof (W_range ph sp rdraw argv envp uid hw Hva Hve) as (W1 & W2 & W3).
pose proof (length_bsb_eq ph sp rdraw argv envp uid hw) as L. pose proof s0_fits as F.
pose proof (total_arg_bytes_Z envp) as TE.
unfold stack_image_size in L.
assert (Hpd : 0 <= (8 - (8 + (Z.of_nat (length argv) + 1) * 8 + (Z.of_nat (length envp) + 1) * 8 + 160
+ total_arg_bytes argv + total_arg_bytes envp) mod 8) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
apply andb_true_intro. unfold usp, argc, envc in Ha. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Theorem init_x_sound_envscan : ltac2:(TCodec.tc2 tcn__AsanNodesStartXInitK "C&GvQ;vQ:v0&>&<vK&=vQ7vQ<vQ8vQ3vQ5vQ@vQ6%877654321v7(@%B9A@?>=<321").
Proof.
exact (x_sound_envscan segs scfg A NX0 LIMIT SINV (argH0 ph sp rdraw argv envp uid hw) FS0
SEGS_wx SEGS_in_hull HULL_ok SINV_frame
we1 we2 we3 Xenv Fe1 Fe2 Fe3 Ee De1 De2 De3
ph sp rdraw argv envp uid hw Hva Hve sp_lo sp_hi SINV0_vals SINV0_sp0 SINV0_envp).
Qed.
Theorem init_x_sound_pnscan : ltac2:(TCodec.tc2 tcn__AsanNodesStartXInitK "C&GvQ;vQ:v0&>&<vK&=vQ7vQ<vQ8vQ3vQ5vQ@vQ6%877654321v7(B%B9A@?>=<321").
Proof.
exact (x_sound_pnscan segs scfg A NX0 LIMIT SINV (argH0 ph sp rdraw argv envp uid hw) FS0
SEGS_wx SEGS_in_hull HULL_ok
(argH0_high ph sp rdraw argv envp uid hw Hsp Hva) e_sp0_init (argH0_agree ph sp rdraw argv envp uid hw)
SINV_frame SINV_agree
wp0 wp1 wp2 wp3 wp4 Xpn Fp0 Fp1 Fp2 Fp3 Fp4 Ep Dp0 Dp1 Dp2 Dp3 Dp4
ph sp rdraw argv envp uid hw Hva Hve sp_lo sp_hi SINV0_vals SINV0_sp0 SINV0_str0).
Qed.
Theorem init_x_sound_layout : ltac2:(TCodec.tc2 tcn__AsanNodesStartXInitK "C&GvQ;vQ:v0&>&<vK&=vQ7vQ<vQ8vQ3vQ5vQ@vQ6%877654321v7(A%B9A@?>=<321").
Proof. apply x_sound_layout. Qed.
End GenericInit.
