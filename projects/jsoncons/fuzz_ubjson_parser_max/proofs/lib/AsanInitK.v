(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim StepTac ShapeAlg AgentLib StartupAux RefLayout ArgvEnv AsanAcct AsanAcctShape AsanPlacement BackingAlgebra.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AxSymExec3K AxSymExec3SoundK AxSymRun3K AsanPlanK AsanPlanSoundK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanCeil.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import AX2K. Import AX2SK. Import APK. Import APSK.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__AsanInitK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanInitK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanInitK.Init."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanK.APK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundK.APSK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3K.AX2K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3SoundK.AX2SK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymRun3K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefLayout."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1None"; "1O"; "1Some"; "1bool"; "1cons"; "1false"; "1fst"; "1length"; "1list"; "1nat"; "1negb"; "1nil"; "1option"; "1orb"; "1pair"]; ["1prod"; "1snd"; "1true"; "2and"; "2eq"; "2or"; "3lt"; "4nth"; "5N"; "5Z"; "0E"; "0E'"; "0L0"; "0L1"; "6word_le8"; "7config"]; ["7init_config"; "7segments_reserved"; "8at_random_ptr"; "8stack_to_mem"; "9FdEntry"; "9m_fds"; "9m_halted"; "9m_tid"; "9m_vm_lazy"; "9m_vm_materialized"; "9m_vmmaps"; "9sp_window_hi"; "9sp_window_lo"; "9vm_brk"; "9vm_limit"; "9vm_maps"]; ["9vm_mmap_base"; "9vm_noaccess"; "9vm_reserved"; "9vm_start_brk"; "0M"; "0M'"; "0Mr0"; ":A_bytes"; ":eager_used"; "<E0"; "<FULL0"; "<R0"; "<SINV0"; "<argH0"; "<inp"; "<model0"]; [";LIMIT"; ";stack_image_size"; "=BRK_ASLR"; "=CEIL"; "=K_RND"; "=NX0"; "=V_ARGC"; "=V_BRK"; "=V_ENVC"; "=V_HW"; "=V_L0"; "=V_L1"; "=V_S1"; "=V_S2"; "=V_S2A"; "=V_UID"]; ["=V_W"; "=a_entry"; "=auxw"; "=e_argv1w"; "=e_atr8"; "=e_atrandom"; "=e_atrb"; "=e_auxb"; "=e_auxv"; "=e_envp"; "=e_sp0"; "=e_sp8"; "=e_sppg"; "=e_stk_len"; "=e_str0"; "=e_str1"]; ["=e_top"; "=eadd"; "=escale"; "=expr_vars_lt"; "=img_hi"; "=img_lo"; "=init_kn"; "=init_kn_with"; "=init_regs"; "=kw_argv1"; "=rw_len"; "=rw_lo"; "=shadow_off"; "=vis_cost"; ">allowA"; ">cfg_of"]; [">cs_ok"; ">fds_std"; ">in_hull"; ">pagedown"; ">pageup"; ">uE"; ">utop"; "?ELit"; "?EVar"; "?KBlob"; "?KImg"; "?KRange"; "?KWord"; "?KWr"; "?KZero"; "?SA"]; ["?adenot"; "?edenot"; "?env"; "?expr"; "?kentry"; "?split_lit"; "@kentry_ok"; "@know_ok"; "@regs_ok"; "Aenv_agree"; "Brdn"; "Cauxv_words"; "0SIMG"; "Dadd"; "Ddiv"; "Dle"]; ["Dleb"; "Dlt"; "Dmodulo"; "Dmul"; "Dof_N"; "Dof_nat"; "Dpow"; "Dsub"; "Dto_nat"; "0W"; "0a"; "0apc"; "0argc"; "0argv"; "0atr"; "0b"]; ["0brk0"; "0bsb"; "0cs0"; "0e"; "0envc"; "0envp"; "0fs"; "0hi"; "0hid0"; "0hw"; "0i"; "0j"; "0k"; "0lo"; "0mbase"; "0n"]; ["0ph"; "0rdraw"; "0segs"; "0sp"; "EZ_to_bv"; "Ebv"; "Ebv_unsigned"; "0ty"; "0uid"; "0usp"; "0v"; "0w"; "0x"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition LIMIT : Z := target_alloc_limit.
Record img_facts (segs : list Segment) (A : atable) (ph : PhdrInfo) : Prop := IMG_FACTS {
if_ph : ph_addr_z A = Z.of_N (ph_addr ph) /\ ph_ent_z A = Z.of_N (ph_ent ph) /\ ph_num_z A = Z.of_N (ph_num ph);
if_hull : 0 <= img_lo A <= img_hi A /\ img_hi A <= 2 ^ 32 /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0;
if_top : reserved_top (segments_reserved segs) = img_hi A;
if_res : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A)
(segments_reserved segs);
if_sizes : sum_sizes (segments_reserved segs) = img_hi A - img_lo A;
if_rw : (0 <= rw_lo A /\ 0 <= rw_len A /\ rw_lo A + rw_len A < 2 ^ 64)
/\ forall m (x : word), rw_lo A <= bv_unsigned x < rw_lo A + rw_len A -> wview segs m x <> None;
if_shadow : 0 <= shadow_off A <= 2 ^ 47
}.
Definition stack_image_size (argv envp : list (list byte)) : Z :=
let struct_size := (8 + (Z.of_nat (length argv) + 1) * 8
+ (Z.of_nat (length envp) + 1) * 8 + 160)%Z in
let len := (struct_size + total_arg_bytes argv + total_arg_bytes envp)%Z in
(len + ((8 - len mod 8) mod 8) + 16)%Z.
Section Init.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Variable A : atable.
Variable ph : PhdrInfo.
Variable sp : word.
Variable rdraw : EntryDraw.
Variable brk0 mbase : word.
Variable argv envp : list (list byte).
Variable fs : Fs.Fs.
Variable stdin : InputStream.
Variable uid gid : word.
Variable hw : word.
Variable groups : list word.
Variable net : NetQueue.
Variable nofile : word.
Variable sigmask : word.
Variable abrt : bool.
Variable urnd : InputStream.
Hypothesis IMG : img_facts segs A ph.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hbrk : valid_brk segs brk0.
Hypothesis Hmb : valid_mmap_base mbase.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Hypothesis Huid : valid_id uid.
Hypothesis Hhw : valid_hwcap hw.
Definition inp : ProcInput := mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw abrt Sv48 urnd [].
Let bsb := build_stack_bytes ph sp argv envp uid hw rdraw.
Let SIMG := entry_stack_image ph sp argv envp uid hw rdraw.
Let usp := bv_unsigned sp.
Let argc := Z.of_nat (length argv).
Let envc := Z.of_nat (length envp).
Let L0 := Z.of_nat (length (nth 0 argv [])).
Let L1 := Z.of_nat (length (nth 1 argv [])).
Let W := (Z.of_nat (length bsb) - 16 - (8 * argc + 8 * envc + 184)) / 8.
Definition vals0 : list word :=
[Z_to_bv 64 (usp / 32768); Z_to_bv 64 argc; Z_to_bv 64 envc; Z_to_bv 64 L0; Z_to_bv 64 W;
Z_to_bv 64 (bv_unsigned brk0 / 4096); Z_to_bv 64 ((usp mod 4096) / 16); Z_to_bv 64 L1; uid; hw;
Z_to_bv 64 ((usp mod 32768) / 4096)].
Definition E0 : env := Env (fun n => nth n vals0 (Z_to_bv 64 0))
(fun k => if Nat.eqb k K_RND then at_random_bytes (ed_random rdraw) else []).
Definition argH0 (E : env) (a : word) : bool :=
let z := bv_unsigned a in
((uE E e_sp0 <=? z) &&
(((usp + 24 <=? z) && (z <? usp + 8 * argc + 8 * envc + 24))
|| ((usp + 8 * argc + 8 * envc + 184 <=? z) && (z <? usp + 8 * argc + 8 * envc + 184 + 8 * W))
|| ((usp + Z.of_nat (length bsb) <=? z) && (z <? usp + Z.of_nat (length SIMG)))))%bool.
Definition SINV0 (E : env) (M : word -> option byte) : Prop :=
(forall n, (n < NX0)%nat -> ev E n = ev E0 n)
/\ (forall a, argH0 E a = true -> M a = wrap_mem ph sp argv envp uid hw rdraw a).
Lemma argH0_high : ltac2:(TCodec.tc2 tcn__AsanInitK "K'T2'UEyR0%211'D'4&QMr2r1%3221(B%73621'C&T?&R3&UF%12>9%4231&SEr3&RJ%3221%9216%;261p0=1pYFF1pQFJ1").
Proof.
intros E a H. unfold argH0 in H. destruct Hsp as [Hlo _]. unfold sp_window_lo in Hlo. unfold CEIL.
pose proof (valid_argv_len argv Hva).
apply andb_prop in H as [HS H]. apply Z.leb_le in HS.
apply orb_prop in H as [H|H]; [apply orb_prop in H as [H|H]|]; apply andb_prop in H as [H _]; apply Z.leb_le in H; unfold usp, argc, envc in H; lia.
Qed.
Lemma e_sp0_init : ltac2:(TCodec.tc2 tcn__AsanInitK "8'D'4&S3&R5&RJ%3221(B%73621").
Proof. reflexivity. Qed.
Lemma argH0_agree : ltac2:(TCodec.tc2 tcn__AsanInitK "D'T2'UEyR0%211&T9&R5r3r2%43321'D'4&QMr4%2216%3287%63521p081pYF>1pQHB1pQFC1").
Proof.
intros E E' a Hag. unfold argH0, uE. rewrite (APSK.edenot_agree' NX0 E E' e_sp0 Hag e_sp0_init). reflexivity.
Qed.
Lemma SINV0_frame : ltac2:(TCodec.tc2 tcn__AsanInitK "Q1'T2'UEyR0%211'=y8%511%311p[J51'D'4&QMr4r1%3221(B%73621r3r2%211%812%<3>21p061pYFD1&QL%12=8r5%321:p031p061pS<F1pS:G1pQFQ01").
Proof. intros E M M' Hf [H1 H2]. split; [exact H1|]. intros a Ha. rewrite (Hf a Ha). apply H2. exact Ha. Qed.
Lemma SINV0_agree : ltac2:(TCodec.tc2 tcn__AsanInitK "G'T2'UEyR0%211'=y8%511%311p051&T9&R5r3r2%43321&QLr4%2214%3226p021p061pS:<1pQHE1pQFF1").
Proof.
intros E E' M HAG [H1 H2]. pose proof HAG as [Hag _]. split.
- intros n Hn. rewrite <- (Hag n) by (unfold NX0 in *; lia). apply H1. exact Hn.
- intros a Ha. apply H2. rewrite (argH0_agree E E' a HAG). exact Ha.
Qed.
Lemma Hlo' : ltac2:(TCodec.tc2 tcn__AsanInitK "7&T?&Q<&UFyR0vUC%3221%6251"). Proof. destruct Hsp as (?&?&?); assumption. Qed.
Lemma Hhi' : ltac2:(TCodec.tc2 tcn__AsanInitK "7&T?&UFyR0vUC%3221&Q;%6221"). Proof. destruct Hsp as (?&?&?); assumption. Qed.
Lemma Hal' : ltac2:(TCodec.tc2 tcn__AsanInitK ";'D'I&TB&UFyR0vUC%3221+@%6221z%:3921"). Proof. destruct Hsp as (?&?&?); assumption. Qed.
Lemma Hav0 : ltac2:(TCodec.tc2 tcn__AsanInitK ";&F(2&8'9'UEy8%211%411vTM%7221%:291"). Proof. destruct Hva as [[? ?] _]; lia. Qed.
Lemma len_av : ltac2:(TCodec.tc2 tcn__AsanInitK "8'C&T?+1vTL%3221+QP0%5231%7231").
Proof. unfold argc. destruct Hva as [H _]. lia. Qed.
Lemma len_ev : ltac2:(TCodec.tc2 tcn__AsanInitK "8'C&T?zvU4%3221+X0%5231%7231").
Proof. unfold envc. destruct Hve as [H _]. lia. Qed.
Lemma usp_lo : ltac2:(TCodec.tc2 tcn__AsanInitK "4&T?+SoonPPPPP0vUI%3221").
Proof. unfold usp. destruct Hsp as [H _]. exact H. Qed.
Lemma usp_al : ltac2:(TCodec.tc2 tcn__AsanInitK "8'D'I&TBvUI+@%3221z%73621").
Proof. unfold usp. destruct Hsp as (_ & _ & H). exact H. Qed.
Lemma length_bsb_eq : ltac2:(TCodec.tc2 tcn__AsanInitK "?'D'I&TE&8'UEy8%211vU1%5221%711&R1vTMvU5%3221%>3=51").
Proof.
unfold bsb, build_stack_bytes, stack_image_size. cbv zeta.
rewrite (string_addrs_pair argv). cbv beta iota.
rewrite (string_addrs_pair envp). cbv beta iota.
rewrite !length_app, length_at_random_bytes, repeat_length, !length_flat_map_le8,
!length_string_addrs_fst, !length_n_to_le_8, length_auxv_bytes,
!length_flatten_strings.
rewrite !total_arg_bytes_Z. unfold auxv_size.
rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul.
match goal with
| |- context [Z.to_nat ?pd] =>
assert (Hpd : (0 <= pd < 8)%Z) by (apply Z.mod_pos_bound; lia); rewrite (Z2Nat.id pd) by lia
end.
lia.
Qed.
Lemma usp_fit : ltac2:(TCodec.tc2 tcn__AsanInitK "A&T?&T=vUI&TE&8'UEy8%211vU1%5221%711%:291&TF+2+Q?%3221%@251").
Proof.
pose proof (build_stack_bytes_within_span ph sp argv envp uid hw rdraw) as B. fold bsb in B.
unfold entry_stack_fits, sp_window_hi in Hfit. unfold usp. lia.
Qed.
Lemma bsb_ge : ltac2:(TCodec.tc2 tcn__AsanInitK "Q2'C&T?&T=&TC+8vTL%3221vU4%5241%7231+V8%9221&TE&8'UEy8%211vU1%5221%711%C291'D'I&TB&TG+@%2271+UH%J2C1%5231%721Jz%;3:21%Q12=1").
Proof.
rewrite length_bsb_eq. unfold stack_image_size, argc, envc. cbv zeta.
pose proof (total_arg_bytes_Z argv). pose proof (total_arg_bytes_Z envp).
match goal with |- context [((8 - ?l mod 8) mod 8)%Z] => set (len := l) end.
assert (0 <= Z.of_nat (total_arg_bytes_nat argv)) by lia.
split; [lia|].
assert (Hpd : 0 <= (8 - len mod 8) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
assert (Hm : (len + (8 - len mod 8) mod 8) mod 8 = 0).
{ rewrite <- Zplus_mod_idemp_l. rewrite Zplus_mod_idemp_r.
replace (len mod 8 + (8 - len mod 8)) with 8 by lia. reflexivity. }
replace (len + (8 - len mod 8) mod 8 + 16 - 16 - (8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 184))
with (len + (8 - len mod 8) mod 8 - 8 * (Z.of_nat (length argv) + Z.of_nat (length envp) + 23)) by (unfold len; lia).
rewrite Zminus_mod, Hm, Z.mul_comm, Z_mod_mult. reflexivity.
Qed.
Lemma W_range : ltac2:(TCodec.tc2 tcn__AsanInitK "Q3'C&T?zvTI%3221'D'I&TC+8%2216&TG&TE&8'UEy8%211vU1%5221%711+@%:221&T=vTL%@2?1vU4%B2A1%5231+UH%7221%C291%I3HE1+Xa^0%O2M1%Q1231%Q22N1").
Proof.
pose proof bsb_ge as [G M]. pose proof (bsb_bound ph sp argv envp uid hw rdraw Hva Hve) as B. fold bsb in B.
unfold W. pose proof len_av. pose proof len_ev.
lia.
Qed.
Lemma brk_range : ltac2:(TCodec.tc2 tcn__AsanInitK "G'C&T?&S4v0%211&UFyR0vU0%3221%8251&T=&R2%2281%<251%>251'D'I&TB+TP0%22;1z%63521%F281").
Proof.
destruct Hbrk as (H1 & H2 & H3). unfold brk_aslr_max in H2. unfold page_size in H3.
rewrite (if_top _ _ _ IMG) in H1, H2. unfold BRK_ASLR. lia.
Qed.
Lemma usp_hi : ltac2:(TCodec.tc2 tcn__AsanInitK ":&T?&T=vUI+V0%3221&TF+2+Q?%3221%9251").
Proof. pose proof usp_fit. pose proof bsb_ge as [G _]. pose proof len_av. pose proof len_ev. lia. Qed.
Lemma uE0 : ltac2:(TCodec.tc2 tcn__AsanInitK "QJ'C'D'I&SE&QI(SH&R<%211%5241&T>vUI+QPP0%3221%<3;51&R=%:11%=2<1&TB+TP0%2291+@%<221%E3D61&R6%C11%F2E1vTL%J3I21&R8%H11%K2J1vU4%O3N21&R:%M11%Q02O1vL%Q43Q321&R@%Q211%Q52Q41vTI%Q93Q821&R7%Q711%Q:2Q91&UFyR0vU0%3221%Q921Q0%QB3QA61%QD2:1%QE2@1%QF2F1%QG2L1%QH2Q21%QI2Q<1").
Proof.
pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. pose proof W_range as (W1 & W2 & W3).
pose proof (u64_range brk0) as [B1 B2].
assert (HL0 : 0 <= L0 <= 131071).
{ unfold L0. pose proof (valid_argv_str_len argv 0 Hva ltac:(destruct Hva as [Hl _]; lia)). lia. }
unfold uE. cbn [edenot E0 ev nth vals0 V_S1 V_S2 V_ARGC V_ENVC V_L0 V_W V_BRK].
rewrite !u64_lit by lia. repeat split; reflexivity.
Qed.
Lemma uE0_s2a : ltac2:(TCodec.tc2 tcn__AsanInitK "@'D'I&SE&QI(SH&R>%211%5241&T>&TBvUI+QPP0%3221+TP0%6221%?3>81").
Proof.
pose proof usp_lo. pose proof usp_hi. unfold uE. cbn [edenot E0 ev nth vals0 V_S2A].
rewrite u64_lit by lia. reflexivity.
Qed.
Lemma L1_range : ltac2:(TCodec.tc2 tcn__AsanInitK "8'C&T?zvM%3221+SooO%5231%7231").
Proof.
unfold L1. destruct (Nat.lt_ge_cases 1 (length argv)) as [Hl|Hl].
- pose proof (valid_argv_str_len argv 1 Hva Hl). lia.
- rewrite nth_overflow by lia. cbn. lia.
Qed.
Lemma uE0_L1 : ltac2:(TCodec.tc2 tcn__AsanInitK ":'D'I&SE&QI(SH&R;%211%5241vM%93821").
Proof. pose proof L1_range. unfold uE. cbn [edenot E0 ev nth vals0 V_L1]. rewrite u64_lit by lia. reflexivity. Qed.
Lemma edenot_uid : ltac2:(TCodec.tc2 tcn__AsanInitK "<'D'UEyR0%211vUH&T1&QI(SH&R?%211%5241%;3871").
Proof. reflexivity. Qed.
Lemma uE0_uid : ltac2:(TCodec.tc2 tcn__AsanInitK "='D'I&SE&QI(SH&R?%211%5241&UFyR0vUH%3221%<3;51").
Proof. reflexivity. Qed.
Lemma uE0_hw : ltac2:(TCodec.tc2 tcn__AsanInitK "='D'I&SE&QI(SH&R9%211%5241&UFyR0vU9%3221%<3;51").
Proof. reflexivity. Qed.
Lemma hw_range : ltac2:(TCodec.tc2 tcn__AsanInitK "<'E'D'I&UFyR0vU9%3221+TY=%73621+RPTY=%93841%;231").
Proof. destruct Hhw as [-> | ->]; [left|right]; reflexivity. Qed.
Lemma u_e_sppg : ltac2:(TCodec.tc2 tcn__AsanInitK "='D'I&SE&QI&RL%3221&TC&T>vUI+TP0%3221%5212%<3;71").
Proof.
pose proof usp_lo. pose proof usp_hi. pose proof usp_al. destruct uE0 as (U1 & _). pose proof uE0_s2a as U2A.
unfold e_sppg, eadd, escale, uE in *. rewrite mkAlu_denot, !mkMd_denot, !edenot_lit.
rewrite u_add64, !u_mul64, !u64_lit by lia. rewrite U1, U2A.
rewrite !Z.mod_small by lia. lia.
Qed.
Lemma u_e_sp0 : ltac2:(TCodec.tc2 tcn__AsanInitK "8'D'I&SE&QI&RJ%3221vUI%73621").
Proof.
pose proof usp_lo. pose proof usp_hi. pose proof usp_al. destruct uE0 as (U1 & U2 & _). pose proof u_e_sppg as UP.
rewrite e_sp0_unfold. unfold eadd, escale, uE in *. rewrite mkAlu_denot, !mkMd_denot, !edenot_lit.
rewrite u_add64, !u_mul64, !u64_lit by lia. rewrite UP, U2.
rewrite !Z.mod_small by lia. lia.
Qed.
Lemma edenot_e_sp0 : ltac2:(TCodec.tc2 tcn__AsanInitK ":'D'UEyR0%211&T1&QI&RJ%3221vUC%93621").
Proof. apply bv_eq. exact u_e_sp0. Qed.
Lemma u_e_top : ltac2:(TCodec.tc2 tcn__AsanInitK "@'D'I&SE&QI&S0%3221&TG&TC&T>vUI+TP0%3221%5212+XPPP0%8221%?3>:1").
Proof.
pose proof usp_lo. pose proof usp_hi. unfold e_top, eaddz, uE. rewrite mkAlu_denot, edenot_lit.
pose proof u_e_sppg as U. unfold uE in U. rewrite u_add64, U, u_lit64. unfold two64.
replace ((-8388608) mod 2 ^ 64) with (2 ^ 64 - 8388608) by reflexivity.
replace (usp / 4096 * 4096 + (2 ^ 64 - 8388608)) with ((usp / 4096 * 4096 - 8388608) + 1 * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small; lia.
Qed.
Lemma u_e_stk_len : ltac2:(TCodec.tc2 tcn__AsanInitK "F'D'I&SE&QI&RM%3221&TG&T=&TF+2+Q?%3221+XPPP0%6221&TC&T>vUI+TP0%3221%5212%>271%E3D@1").
Proof.
pose proof usp_lo. pose proof usp_hi. unfold e_stk_len, esub, uE. rewrite mkAlu_denot, edenot_lit.
pose proof u_e_sppg as U. unfold uE in U. rewrite u_sub64, U, u_lit64. unfold two64.
rewrite (Z.mod_small (2 ^ 47 + 8388608)) by lia. rewrite Z.mod_small; lia.
Qed.
Lemma u_sp8 : ltac2:(TCodec.tc2 tcn__AsanInitK ";'D'I&SE&QI&RK%3221&T>vUI+8%3221%:3951").
Proof.
pose proof usp_lo. pose proof usp_hi. pose proof usp_al. destruct uE0 as (U1 & U2 & _). pose proof uE0_s2a as U2A.
unfold e_sp8, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite U1, U2, U2A.
rewrite !Z.mod_small by lia. lia.
Qed.
Lemma u_sppg8 : ltac2:(TCodec.tc2 tcn__AsanInitK "G'D'I&SE&QI&S1&S2+TP0(SH&R<%211%5241+`0&R>%611%9231%;251%>2=1&TC&T>vUI%221>%421:%F3E61").
Proof.
pose proof usp_lo. pose proof usp_hi. pose proof usp_al. destruct uE0 as (U1 & _). pose proof uE0_s2a as U2A.
unfold eadd, escale, uE in *. rewrite mkAlu_denot, !mkMd_denot, !edenot_lit.
rewrite u_add64, !u_mul64, !u64_lit by lia. rewrite U1, U2A.
rewrite !Z.mod_small by lia. lia.
Qed.
Lemma u_e_envp : ltac2:(TCodec.tc2 tcn__AsanInitK "@'D'I&SE&QI&RI%3221&T=vUI&TC+8vTL%3221%6251+@%8221%?3>:1").
Proof.
pose proof usp_lo. pose proof usp_hi. pose proof len_av. destruct uE0 as (_ & _ & U3 & _).
pose proof u_e_sp0 as US. unfold e_envp, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite US, U3.
rewrite !Z.mod_small by lia. lia.
Qed.
Lemma u_e_auxv : ltac2:(TCodec.tc2 tcn__AsanInitK "C'D'I&SE&QI&RH%3221&T=vUI&TC+8vTL%3221%6251vU4%6251%9231+H%;221%B3A=1").
Proof.
pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. destruct uE0 as (_ & _ & _ & U4 & _).
pose proof u_e_envp as UE. unfold e_auxv, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite UE, U4.
rewrite !Z.mod_small by lia. lia.
Qed.
Lemma u_e_str0 : ltac2:(TCodec.tc2 tcn__AsanInitK "C'D'I&SE&QI&RN%3221&T=vUI&TC+8vTL%3221%6251vU4%6251%9231+UH%;221%B3A=1").
Proof.
pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev.
pose proof u_e_auxv as UA. unfold e_str0, eaddz, uE in *. rewrite mkAlu_denot, edenot_lit.
rewrite u_add64, u64_lit by lia. rewrite UA. rewrite Z.mod_small by lia. lia.
Qed.
Lemma u_e_str1 : ltac2:(TCodec.tc2 tcn__AsanInitK "G'D'I&SE&QI&RO%3221&T=vUI&TC+8vTL%3221%6251vU4%6251%9231+UH%;221vL%=221+1%?221%F3EA1").
Proof.
pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
destruct uE0 as (_ & _ & _ & _ & U5 & _).
assert (HL0 : 0 <= L0 <= 131071).
{ unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
pose proof u_e_str0 as US. unfold e_str1, eadd, eaddz, uE in *. rewrite !mkAlu_denot, !edenot_lit.
rewrite !u_add64, !u64_lit by lia. rewrite US, U5. rewrite !Z.mod_small by lia. lia.
Qed.
Lemma u_e_atrandom : ltac2:(TCodec.tc2 tcn__AsanInitK "E'D'I&SE&QI&RE%3221&TG&T=vUI&TE&8'UEy8%211vU1%5221%711%:291+@%=221%D3C?1").
Proof.
pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof W_range as (W1 & W2 & W3).
destruct uE0 as (_ & _ & _ & _ & _ & U6 & _).
pose proof u_e_str0 as US. unfold e_atrandom, eadd, escale, uE in *. rewrite mkAlu_denot, mkMd_denot, edenot_lit.
rewrite u_add64, u_mul64, u64_lit by lia. rewrite US, U6. rewrite !Z.mod_small by lia. lia.
Qed.
Lemma u_e_atr8 : ltac2:(TCodec.tc2 tcn__AsanInitK "B'D'I&SE&QI&RD%3221&T=&T>vUI+8%3221vTL%6221vU4%8221vTI%:221%A3@<1").
Proof.
pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. pose proof W_range as (W1 & W2 & W3).
destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7). pose proof u_sp8 as U8.
unfold e_atr8, eadd, escale, uE in *. rewrite !mkAlu_denot.
rewrite !u_add64 by lia. rewrite U8, U3, U4, U6. rewrite !Z.mod_small by lia. lia.
Qed.
Definition R0 : bvmap 5 word := regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp.
Definition FULL0 : word -> option byte := wrap_mem ph sp argv envp uid hw rdraw.
Definition model0 : Model := init_model (segments_reserved segs) brk0 mbase sp LIMIT inp.
Let cs0 := init_acs_of A.
Let hid0 := hid A argH0 E0 cs0 model0.
Let Mr0 := Mr A argH0 E0 cs0 model0 FULL0.
Lemma model0_facts : ltac2:(TCodec.tc2 tcn__AsanInitK "RC'C'D'='UEyR0%211%411&Q6&QO%211(1%116%;3631'9'@'Q4%22;1%411&Q5%11;&SA%D3421&Q7%11?%G3B1=%;2DD%=11&QB&Q:%11E%311&Q1vUB%211%Q13841&Q?%117(<%11=%Q63=31&QA%11<%Q93@14&Q8%11Q4%Q<3C17%Q11Q9&Q9%11Q8%<1Q<%QA3421'I&Q>%11H&R0%QF3421&Q=%11LvU0%QJ3QF21&QC%11Q0%QM3QI14&Q@%11Q3vU>%R13QM21&QH%11QLz%R53C21%R7251%R82:1%R92>1%R:2C1%R;2I1%R<2O1%R=2Q31%R>2Q71%R?2Q=1%R@2QH1%RA2QL1%RB2R61").
Proof. repeat split; reflexivity. Qed.
Lemma utop0 : ltac2:(TCodec.tc2 tcn__AsanInitK "?'D'I&SF&QI%211&TG&TC&T>vUI+TP0%3221%5212+XPPP0%8221%>3=:1").
Proof. unfold APSK.utop, APSK.pagedown. rewrite u_e_sp0. reflexivity. Qed.
Lemma hid0_eq : ltac2:(TCodec.tc2 tcn__AsanInitK "Q2'UEyR0%211'D'4vU8r1%211&>&QM&QI%2215&;&SBv0&UF%12?:%4231&T@&TG&TC&T>vUI+TP0%3221%5212+XPPP0%8221%:21<%E2<1%B11%G2D1%M3LI1pYFO1").
Proof.
intros a. unfold hid0, hid, vis. rewrite utop0. destruct model0_facts as (_&_&_&_&Hm&Hn&Hl&_). rewrite Hm. cbn [in_ivs existsb andb].
rewrite orb_false_r. reflexivity.
Qed.
Lemma Mr0_visible : ltac2:(TCodec.tc2 tcn__AsanInitK "Q1'UEyR0%211&T?&TGvUI+XPPP0%3221&UFr1%2291%8241'D'4&QM&QIr2%3221(6%73621'=y8%F11%311vQFr3%211&QJ%113%A3631p0;1p0D1pYFN1").
Proof.
intros a Hc Ha. unfold Mr0, Mr, mrestrict. fold hid0. rewrite hid0_eq, Ha.
replace (usp / 4096 * 4096 - 8388608 <=? bv_unsigned a) with true by (symmetry; apply Z.leb_le; lia). rewrite orb_true_r. reflexivity.
Qed.
Lemma FULL0_below : ltac2:(TCodec.tc2 tcn__AsanInitK "Q0'UEyR0%211'C&T?&TGvUI+XPPP0%3221&UFr1%22:1%8241&TA%1238%<231'D'=y8%C11%311&QJr2%211(3&UDz%2291%4291%=3961p0?1pYFM1").
Proof.
intros a Ha. unfold FULL0, wrap_mem.
assert (Hs : stack_to_mem sp SIMG a = None).
{ unfold stack_to_mem. replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; unfold usp in Ha; lia). reflexivity. }
fold SIMG. rewrite Hs. unfold stack_max_size, usp in *.
replace (Z.leb (bv_unsigned sp - 8 * 1024 * 1024) (bv_unsigned a)) with true by (symmetry; apply Z.leb_le; lia).
replace (Z.ltb (bv_unsigned a) (bv_unsigned sp)) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
Lemma FULL0_low : ltac2:(TCodec.tc2 tcn__AsanInitK "I'UEyR0%211&TA&UFr1%2251&TGvUI+XPPP0%3221%8251'D'=y8%?11%311&QJr2%211(1%116%:3631p0<1pYFF1").
Proof.
intros a Ha. unfold FULL0, wrap_mem.
assert (Hs : stack_to_mem sp SIMG a = None).
{ unfold stack_to_mem. replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; unfold usp in Ha; lia). reflexivity. }
fold SIMG. rewrite Hs. unfold stack_max_size, usp in *.
replace (Z.leb (bv_unsigned sp - 8 * 1024 * 1024) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
Qed.
Lemma rdn_Mr0_stack : ltac2:(TCodec.tc2 tcn__AsanInitK "QO'UEyR0%211':&T?vUI&UFr2%2271%5241&T=r3%62;1&TE%117%5231&TF+2+R0%3221%@251'Cr5%A2F1r1%C2H1%F231&TAr4%@11%D271%4261%;261'D'4&QM&QI%221N(6%63521p081p[JQ71'='9y8%Q=11%311%511&T:vUBvQF%3421MG&Q3vUCvT<%3221%8471Q2L%H3:61p0A1p0Q71p0QC1p[0QJ1pYFQL1").
Proof.
intros a n Ha Hn Hvis. pose proof usp_lo. unfold SIMG.
rewrite <- (rdn_wrap_stack_above segs ph sp argv envp a n uid hw rdraw) by (unfold usp in *; lia).
apply rdn_ext; [exact Hn|]. intros x Hx. apply Mr0_visible; [unfold usp, CEIL in *; lia | apply Hvis; exact Hx].
Qed.
Lemma split_u : ltac2:(TCodec.tc2 tcn__AsanInitK "Q8'T2'T3'I'D'@%1243&T5r3%211(?r2r1%34;:21%:3851&T?z%2216&SEr6r5%3221%72>1&T=&UFyR0&T1r7%2218%5241r4%8221%>25=%M3N21p0<1p0B1p0F1pZJQ21pZ0Q41pZ8Q51pQFQ71").
Proof.
intros E e b k Hs Hk Hle. unfold uE in *. rewrite (split_lit_denot E e b k Hs) in Hle |- *.
pose proof (u64_range (edenot E b)) as Rb.
rewrite Z_to_bv_unsigned in Hle |- *. unfold bv_wrap, bv_modulus in *. change (2 ^ Z.of_N 64) with (2 ^ 64) in *.
destruct (Z_lt_le_dec (bv_unsigned (edenot E b) + k) (2 ^ 64)).
- rewrite Z.mod_small by lia. reflexivity.
- exfalso.
assert ((bv_unsigned (edenot E b) + k) mod 2 ^ 64 = bv_unsigned (edenot E b) + k - 2 ^ 64).
{ replace (bv_unsigned (edenot E b) + k) with ((bv_unsigned (edenot E b) + k - 2 ^ 64) + 1 * 2 ^ 64) at 1 by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
lia.
Qed.
Lemma adenot_SA : ltac2:(TCodec.tc2 tcn__AsanInitK "J'T2'T3'I'D'UEyR0%211&T0r3(SOr2r1%3221%6251&UD&T=&UF&T1%12:8%32>1%5219%72@1%C3@91pZJE1pZ0G1pQFI1").
Proof. intros. unfold adenot, v_addi. cbn [a_base a_off]. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. Qed.
Lemma argH0_range : ltac2:(TCodec.tc2 tcn__AsanInitK "QM'UEyR0%211'D'4&QM&QIr1%3221(B%73621'E'C&T?&T=vUI+H%3221&UFr2%22C1%8241&TA&TC+8vTL%3221%=2<1vU4%6251%@231%A21?%:2<1%E2<1+UH%E251%G21@&TG&TE&8y8%Q911vU1%4221%611%O2N1+@%:221%J2L1%Q52=1%Q525NvT<%=2;1%?11%Q82Q71%Q12Q31%Q<261%Q>281%Q?2I1p0QA1pYFQJ1").
Proof.
intros a H. unfold argH0 in H. pose proof W_range as (W1 & W2 & W3). apply andb_prop in H as [_ H].
apply orb_prop in H as [H|H]; [apply orb_prop in H as [H|H]|]; apply andb_prop in H as [H1 H2]; apply Z.leb_le in H1; apply Z.ltb_lt in H2;
[left | right; left | right; right]; lia.
Qed.
Lemma not_argH0 : ltac2:(TCodec.tc2 tcn__AsanInitK "QG'UEyR0%211'E&TA&UFr1%2261&T=vUI+H%3221%8251'C&T?&TC+8vTL%3221%;2:1vU4%6251%>231%?21=%:21A+UH%B241%G2D1%?241&TG&TE&8y8%Q111vU1%4221%611%M2L1+@%:221%J21Q1%Q52Q24%M221%Q82?1%Q92Q01'D'4&QM&QIr2%3221(6%73621p091pYFQD1").
Proof.
intros a H. destruct (argH0 E0 a) eqn:Ha; [|reflexivity]. apply argH0_range in Ha.
pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _]. lia.
Qed.
Lemma kword_stack : ltac2:(TCodec.tc2 tcn__AsanInitK "RH'T3'I'UEyR0%211'D&T=&UF&T1&QIr4%3221%5291r3%8221r1%92=1%<3@31&T?vUIr2%>2B1%4231%@2D:+8%C221&TE&8y8%K11vU1%4221%611%K2>1%@291'Cr5%N2Q21%D21F&TA%Q223@%22I1%7241'4&QM%12Q4I(6%Q:3421p061p[JQ=1'='9%11G%311&T:vUB&Q3vUCvT<%3221u8%7462I1(3&Nr6%QI2QH1%311%52?1%QO3?71&T6vQF(SL(SOr9r8%3221r7%632A1%94GR581p0;1p0O1p0Q?1p0QL1p0R21p[HR@1p[FRE1pZJRE1pZ0RG1").
Proof.
intros b k v w Hw Hlo Hhi Hvis Hrd. pose proof usp_fit. pose proof usp_lo. pose proof (u64_range w).
cbn [kentry_ok]. split; [lia|].
assert (Hfl : flat E0 (SA b k) (Z.of_nat 8)) by (unfold flat, estart; cbn [a_base a_off]; change (Z.of_nat 8) with 8; lia).
split; [exact Hfl|].
rewrite adenot_SA. cbn [a_base a_off]. rewrite Hw, Z_to_bv_bv_unsigned.
rewrite rdn_Mr0_stack; [| lia | change (Z.of_nat 8) with 8; lia | exact Hvis].
rewrite Hrd. rewrite n_to_le_8_spec. reflexivity.
Qed.
Lemma spb_eq : ltac2:(TCodec.tc2 tcn__AsanInitK "<'D'@'T3'I%3221&T5&RJ%211(?z%248741%;3741").
Proof. reflexivity. Qed.
Lemma auxv_word_ok : ltac2:(TCodec.tc2 tcn__AsanInitK "QI':'T3&Fr2uD%3221'D'UEyR0%211&Gr3&T;vU@&Q2vUCvTMvU5%43321vUHvU9%948321&UDz%22@1%?4@>41&T1&QI%221I%G3D41&T6vUBvQF(SL(SO&7'I&RG%33Q521&T=&A%13Q854&TC+8&TEr4%211%5241%9271%?2;1u8%B321Q8%F4EID1p0H1p0QA1p[FQF1pZHQH1").
Proof.
intros j v Hj Hv. pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
assert (Hab : split_lit e_auxv = (fst e_auxb, snd e_auxb)) by (unfold e_auxb; destruct (split_lit e_auxv); reflexivity).
set (ab := fst e_auxb) in *. set (ak := snd e_auxb) in *.
pose proof (split_u E0 e_auxv ab ak Hab) as Hs. rewrite u_e_auxv in Hs.
assert (Hak : ak = 24) by (subst ak; vm_compute; reflexivity).
specialize (Hs ltac:(lia) ltac:(lia)).
apply (kword_stack ab (ak + 8 * Z.of_nat j) v (sp + nat_to_word (auxv_off argv envp + 8 * j))%bv).
- rewrite word_add_nat, u64_lit; unfold auxv_off, usp in *; [|lia]. rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
- rewrite word_add_nat, u64_lit; unfold auxv_off, usp in *; lia.
- rewrite word_add_nat, u64_lit; unfold auxv_off, usp in *; [|lia]. rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
- intros x Hx. apply not_argH0. rewrite word_add_nat, u64_lit in Hx; unfold auxv_off, usp in *; [|lia].
rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul in Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. lia.
- rewrite <- Hv.
pose proof (read_auxv_word segs ph sp rdraw argv envp uid hw Hva Hve Hhi' j Hj) as RW.
exact RW.
Qed.
Lemma auxw_ok : ltac2:(TCodec.tc2 tcn__AsanInitK "QL'I'T3'C&T?zr3%3221+9%5231%7231'D'UEyR0%211&G&TH&TC+2r4%3221%511&T;vU@&Q2vUCvTMvU5%43321vUHvU9%948321&UD%12DL%C4D=31%32FM%I3F21&T=r5%F2E1+1%4221%J11%L4M1<:&T1&QI%221Q8%Q43Q141&T7vUBvQF&RBr6%231?Q2%645941p081p0D1p0Q?1p[FQH1p[@QJ1pZFQK1").
Proof.
intros i ty v Hi H1 H2. unfold auxw.
constructor; [|constructor; [|constructor]].
- replace (snd e_auxb + 16 * i) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i))) by lia. apply auxv_word_ok; [lia|]. rewrite H1. reflexivity.
- replace (snd e_auxb + 16 * i + 8) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i + 1))) by lia. apply auxv_word_ok; [lia|]. exact H2.
Qed.
Lemma kr_ok : ltac2:(TCodec.tc2 tcn__AsanInitK "H'T3'I'C&T?r2&SE&QIr3%3221%6251r1%8231%:231&T6vUBvQF(SKr4%231;>%645=41p081pZ@D1pZLE1pZ8G1").
Proof. intros e lo hi H. cbn [kentry_ok]. unfold uE in H. exact H. Qed.
Lemma Mr0_below : ltac2:(TCodec.tc2 tcn__AsanInitK "Q0'UEyR0%211'C&T?&TGvUI+XPPP0%3221&UFr1%22:1%8241&TA%1238%<231'D'=y8%C11%311vQFr2%211(3&UDz%2291%4291%=3961p0?1pYFM1").
Proof.
intros a Ha. pose proof usp_lo. pose proof len_av.
rewrite Mr0_visible; [apply FULL0_below; exact Ha | unfold CEIL; lia | apply not_argH0; lia].
Qed.
Lemma stack_window_ok : ltac2:(TCodec.tc2 tcn__AsanInitK "C'C&T6vUB&QIvQF(SM(SO&RJ-XPPP0%3221(SG+XPPP0%211%8241%=4<;:1(SN%1274%@4?>=1%B241").
Proof.
pose proof usp_lo. pose proof usp_hi.
assert (Hst : estart E0 (SA e_sp0 (-8388608)) = usp - 8388608).
{ unfold estart. cbn [a_base a_off]. pose proof u_e_sp0 as U. unfold uE in U. rewrite U. lia. }
assert (Hl : elenZ E0 (ELit 8388608) = 8388608) by (apply elenZ_lit; lia).
assert (Hfl : flat E0 (SA e_sp0 (-8388608)) (elenZ E0 (ELit 8388608))).
{ unfold flat. rewrite Hst, Hl. lia. }
split; cbn [kentry_ok]; (split; [exact Hfl|]); rewrite Hst, ?Hl.
- intros d m Hd Hdm. apply store_ok_of_all; rewrite u_small by lia; [lia|].
intros x Hx. unfold wview. rewrite (Mr0_below x) by lia. discriminate.
- intros i Hi. apply Mr0_below. rewrite u_small by lia. lia.
Qed.
Lemma argc_word_ok : ltac2:(TCodec.tc2 tcn__AsanInitK "?&T6vUB&QIvQF(SL(SO&RJz%3221u8(SH&R6%211%93541%>4=<;1").
Proof.
pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
apply (kword_stack e_sp0 0 (EVar V_ARGC) sp).
- pose proof u_e_sp0 as U. unfold uE in U. rewrite U. unfold usp. lia.
- unfold usp. lia.
- unfold usp in *. lia.
- intros x Hx. apply not_argH0. unfold usp in *. lia.
- pose proof (read_argc ph segs sp argv envp uid hw rdraw) as RW.
assert (Hv : len_word argv = edenot E0 (EVar V_ARGC)).
{ apply bv_eq. destruct uE0 as (_ & _ & U3 & _). unfold uE in U3. rewrite U3. unfold argc. exact (u_argcN argv Hva). }
rewrite <- Hv. apply RW. fold bsb. pose proof usp_fit. unfold usp in *. lia.
Qed.
Lemma argv0_word_ok : ltac2:(TCodec.tc2 tcn__AsanInitK "=&T6vUB&QIvQF(SL(SO&RJ+8%3221u8&RN%73321%<4;:91").
Proof.
pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
apply (kword_stack e_sp0 8 e_str0 (sp + nat_to_word (8 + 8 * 0))%bv).
- pose proof u_e_sp0 as U. unfold uE in U. rewrite U. rewrite word_add_nat, u64_lit; unfold usp in *; lia.
- rewrite word_add_nat, u64_lit; unfold usp in *; lia.
- rewrite word_add_nat, u64_lit; unfold usp in *; lia.
- intros x Hx. apply not_argH0. rewrite word_add_nat, u64_lit in Hx; unfold usp in *; lia.
- pose proof (read_argv_ptr_k ph segs sp argv envp 0 uid hw rdraw Hav0) as RW.
assert (Hv : cat_argv_ptr sp argv envp 0 = edenot E0 e_str0).
{ apply bv_eq. rewrite (@u_cat_argv_ptr ph sp rdraw argv envp uid hw Hva Hve Hlo' Hhi' 0 Hav0).
pose proof u_e_str0 as U. unfold uE in U. rewrite U. unfold cat_struct_size, auxv_size. replace (total_arg_bytes_nat (firstn 0 argv)) with 0%nat by reflexivity.
unfold usp, argc, envc. lia. }
rewrite <- Hv. apply RW. fold bsb. unfold usp in *. lia.
Qed.
Lemma argv1_word_ok : ltac2:(TCodec.tc2 tcn__AsanInitK "8&T6vUB&QIvQF&S9&RC%211%746541").
Proof.
unfold kw_argv1.
pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
assert (HL0 : 0 <= L0 <= 131071).
{ unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
assert (Hw1 : edenot E0 e_argv1w = if (1 <? argc) then edenot E0 e_str1 else Z_to_bv 64 0).
{ unfold e_argv1w. cbn [edenot]. destruct uE0 as (_ & _ & U3 & _). unfold uE in U3. cbn [edenot] in U3.
apply bv_eq. rewrite u_mul64, u_sltu64, u64_lit, U3 by lia.
pose proof (u64_range (edenot E0 e_str1)).
destruct (1 <? argc); [rewrite Z.mul_1_l, Z.mod_small by lia; reflexivity | rewrite u64_lit by lia; reflexivity]. }
apply (kword_stack e_sp0 16 e_argv1w (sp + nat_to_word (8 + 8 * 1))%bv).
- pose proof u_e_sp0 as U. unfold uE in U. rewrite U. rewrite word_add_nat, u64_lit; unfold usp in *; lia.
- rewrite word_add_nat, u64_lit; unfold usp in *; lia.
- rewrite word_add_nat, u64_lit; unfold usp in *; lia.
- intros x Hx. apply not_argH0. rewrite word_add_nat, u64_lit in Hx; unfold usp in *; lia.
- rewrite Hw1. destruct (1 <? argc) eqn:Hc.
+ apply Z.ltb_lt in Hc. assert (Hav1 : (1 < length argv)%nat) by (unfold argc in Hc; lia).
pose proof (read_argv_ptr_k ph segs sp argv envp 1 uid hw rdraw Hav1) as RW.
assert (Hv : cat_argv_ptr sp argv envp 1 = edenot E0 e_str1).
{ apply bv_eq. rewrite (@u_cat_argv_ptr ph sp rdraw argv envp uid hw Hva Hve Hlo' Hhi' 1 Hav1).
pose proof u_e_str1 as U. unfold uE in U. rewrite U. unfold cat_struct_size, auxv_size.
assert (TF : forall l : list (list byte), (0 < length l)%nat ->
Z.of_nat (total_arg_bytes_nat (firstn 1 l)) = Z.of_nat (length (nth 0 l [])) + 1)
by (intros [|x t] Hl; [cbn in Hl; lia|]; change (firstn 1 (x :: t)) with [x]; cbn -[Z.of_nat Z.add]; lia).
rewrite Nat2Z.inj_add, (TF argv Hav0). unfold L0, usp, argc, envc. lia. }
rewrite <- Hv. apply RW. fold bsb. unfold usp in *. lia.
+ apply Z.ltb_ge in Hc. assert (Hav1 : length argv = 1%nat) by (unfold argc in Hc; pose proof Hav0; lia).
pose proof (read_argv_null segs ph sp rdraw argv envp uid hw Hva Hve Hhi') as RW. rewrite Hav1 in RW.
exact RW.
Qed.
Lemma atrandom_ok : ltac2:(TCodec.tc2 tcn__AsanInitK "D&T6vUB&QIvQF(SI(SO&7'T3'I&RF%43321&A%13543%8231(SG+@%211&R4%>3521%C4BA@1").
Proof.
pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
assert (Hab : split_lit e_atrandom = (fst e_atrb, snd e_atrb)) by (unfold e_atrb; destruct (split_lit e_atrandom); reflexivity).
set (ab := fst e_atrb) in *. set (ak := snd e_atrb) in *.
pose proof (split_u E0 e_atrandom ab ak Hab) as Hs. rewrite u_e_atrandom in Hs.
assert (Hak : ak = 184) by (subst ak; vm_compute; reflexivity).
specialize (Hs ltac:(lia) ltac:(lia)).
assert (Hst : estart E0 (SA ab ak) = usp + Z.of_nat (length bsb) - 16) by (unfold estart; cbn [a_base a_off]; lia).
assert (Hl : elenZ E0 (ELit 16) = 16) by (apply elenZ_lit; lia).
cbn [kentry_ok]. rewrite Hst, Hl.
assert (HE : eb E0 K_RND = at_random_bytes (ed_random rdraw)) by (unfold E0; cbn [eb]; rewrite Nat.eqb_refl; reflexivity).
rewrite HE.
split; [unfold flat; rewrite Hst; unfold usp in *; lia|].
split; [rewrite length_at_random_bytes; reflexivity|].
intros i Hi.
destruct (at_random_off segs ph sp rdraw argv envp uid hw Hva Hve Hhi') as [off (Hp & Hlen & Hmod & Hrd)].
fold bsb in Hlen.
assert (Hu : bv_unsigned (at_random_ptr sp argv envp) = usp + Z.of_nat off).
{ rewrite Hp, word_add_nat. apply u64_lit. unfold usp in *. lia. }
specialize (Hrd (Z.to_nat i) 1%nat ltac:(lia)). fold bsb in Hrd. fold SIMG in Hrd.
rewrite (AsanCeil.firstn1_skipn_nth _ _ (Z_to_bv 8 0)) in Hrd by (rewrite length_at_random_bytes; lia).
assert (Ha : (at_random_ptr sp argv envp + nat_to_word (Z.to_nat i))%bv = Z_to_bv 64 (usp + Z.of_nat (length bsb) - 16 + i)).
{ apply bv_eq. rewrite word_add_nat, Hu, u64_lit, u64_lit; unfold usp in *; lia. }
rewrite Ha in Hrd.
rewrite Mr0_visible; [| rewrite u64_lit; unfold usp, CEIL in *; lia | apply not_argH0; rewrite u64_lit; unfold usp in *; lia].
unfold FULL0. rewrite (wrap_above_sp ph sp argv envp _ uid hw rdraw) by (rewrite u64_lit; unfold usp in *; lia). fold SIMG.
cbn [rdn] in Hrd.
destruct (stack_to_mem sp SIMG (Z_to_bv 64 (usp + Z.of_nat (length bsb) - 16 + i))) as [b|] eqn:Hstk.
- cbn in Hrd. injection Hrd as ->. reflexivity.
- exfalso. unfold stack_to_mem in Hstk. fold usp in Hstk. rewrite u64_lit in Hstk by (unfold usp in *; lia).
replace (usp <=? usp + Z.of_nat (length bsb) - 16 + i) with true in Hstk by (symmetry; apply Z.leb_le; lia).
cbv zeta in Hstk.
assert (HL : (length bsb <= length SIMG)%nat) by (unfold SIMG, entry_stack_image; cbv zeta; rewrite length_app; fold bsb; lia).
replace (usp + Z.of_nat (length bsb) - 16 + i - usp <? Z.of_nat (length SIMG)) with true in Hstk by (symmetry; apply Z.ltb_lt; lia).
apply nth_error_None in Hstk. lia.
Qed.
Lemma kimg_ok : ltac2:(TCodec.tc2 tcn__AsanInitK "<&T6vUB&QIvQF(SJ&S5v0%211&S4%113%6231%;4:981").
Proof.
pose proof usp_lo. pose proof (if_hull _ _ _ IMG) as (H1 & H2 & H3 & H4). cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
unfold Mr0, Mr, mrestrict. destruct (hid A argH0 E0 cs0 model0 (Z_to_bv 64 i)); [reflexivity|].
apply FULL0_low. rewrite u64_lit; lia.
Qed.
Lemma rw_window_ok : ltac2:(TCodec.tc2 tcn__AsanInitK "B&T6vUB&QIvQF(SM(SO(SGz%211&S;v0%211%7241&S:%114%911%<241%A4@?>1").
Proof.
pose proof (if_rw _ _ _ IMG) as ((R1 & R0 & R2) & R3).
assert (Hst : estart E0 (SA (ELit 0) (rw_lo A)) = rw_lo A) by (unfold estart; cbn [a_base a_off]; rewrite edenot_lit, u64_lit; lia).
assert (Hl : elenZ E0 (ELit (rw_len A)) = rw_len A) by (apply elenZ_lit; lia).
cbn [kentry_ok]. rewrite Hst, Hl. split; [unfold flat; rewrite Hst; lia|].
intros d m Hd Hdm. destruct m as [|m']; [reflexivity|].
assert (Hu : bv_unsigned (Z_to_bv 64 (rw_lo A + d)) = rw_lo A + d) by (apply u_small; rewrite Nat2Z.inj_succ in Hdm; lia).
apply store_ok_of_all; rewrite Hu; [lia|].
intros x Hx. apply R3. lia.
Qed.
Lemma atr_ptr_eq : ltac2:(TCodec.tc2 tcn__AsanInitK ">'D'UEyR0%211&Q2vUCvTMvU5%43321&T1&QI&RE%3221%=3:51").
Proof.
pose proof usp_lo. pose proof usp_fit.
destruct (at_random_off segs ph sp rdraw argv envp uid hw Hva Hve Hhi') as [off (Hp & Hlen & Hmod & _)]. fold bsb in Hlen.
apply bv_eq. rewrite Hp, word_add_nat, u64_lit by (unfold usp in *; lia).
pose proof u_e_atrandom as U. unfold uE in U. rewrite U. unfold usp. lia.
Qed.
Lemma init_kn_with_ok : ltac2:(TCodec.tc2 tcn__AsanInitK "?'T4&T6vUB&QIvQFr1%544321&T7&S7r2v0%3221%54:981p071pYN>1").
Proof.
intros atr Hatr.
pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof W_range as (W1 & W2 & W3).
pose proof brk_range as [B1 B2]. pose proof bsb_ge as [G _]. pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4).
pose proof (if_ph _ _ _ IMG) as (P1 & P2 & P3).
destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7).
assert (HL0 : 0 <= L0 <= 131071).
{ unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
unfold init_kn_with.
destruct stack_window_ok as [SW1 SW2].
apply Forall_app; split.
{ apply Forall_cons; [apply kr_ok; rewrite U1; lia|].
apply Forall_cons; [apply kr_ok; rewrite U2; lia|].
apply Forall_cons; [apply kr_ok; rewrite uE0_s2a; lia|].
apply Forall_cons; [apply kr_ok; unfold eaddz, uE; rewrite mkAlu_denot, edenot_lit, u_add64, u64_lit by lia;
pose proof u_e_atrandom as U; unfold uE in U; rewrite U; rewrite Z.mod_small by lia; lia|].
apply Forall_cons; [apply kr_ok; rewrite u_e_atr8; lia|].
apply Forall_cons; [apply kr_ok; rewrite u_e_auxv; lia|].
apply Forall_cons; [apply kr_ok; rewrite u_e_sp0; lia|].
apply Forall_cons; [apply kr_ok; rewrite u_sp8; lia|].
apply Forall_cons; [apply kr_ok; rewrite u_e_sppg; lia|].
apply Forall_cons; [apply kr_ok; rewrite u_sppg8; lia|].
apply Forall_cons; [apply kr_ok; rewrite U3; lia|].
apply Forall_cons; [apply kr_ok; rewrite U4; lia|].
apply Forall_cons; [apply kr_ok; rewrite U5; lia|].
apply Forall_cons; [apply kr_ok; rewrite uE0_L1; pose proof L1_range; lia|].
apply Forall_cons; [apply kr_ok; rewrite uE0_uid; unfold valid_id in Huid; pose proof (u64_range uid); lia|].
apply Forall_cons; [apply kr_ok; rewrite uE0_hw; pose proof hw_range; lia|].
apply Forall_cons; [apply kr_ok; rewrite U6; lia|].
apply Forall_cons; [apply kr_ok; rewrite U7; unfold BRK_ASLR in *; lia|].
apply Forall_cons; [exact SW1|].
apply Forall_cons; [exact SW2|].
apply Forall_cons; [exact argc_word_ok|].
apply Forall_cons; [exact argv0_word_ok|].
apply Forall_cons; [exact argv1_word_ok|].
apply Forall_nil. }
repeat (apply Forall_app; split).
1-10: apply auxw_ok; [lia | rewrite auxv_words_eq; cbn [nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul]; try reflexivity ..].
all: try (rewrite edenot_lit; reflexivity).
1: rewrite edenot_lit, P1; reflexivity.
1: rewrite edenot_lit, P2; reflexivity.
1: rewrite edenot_lit, P3; reflexivity.
1: exact atr_ptr_eq.
apply Forall_cons; [exact Hatr|].
apply Forall_cons; [exact kimg_ok|].
apply Forall_cons; [exact rw_window_ok|].
apply Forall_nil.
Qed.
Lemma init_kn_ok : ltac2:(TCodec.tc2 tcn__AsanInitK "8&T7vUB&QIvQF&S6v0%211%746541").
Proof. exact (init_kn_with_ok _ atrandom_ok). Qed.
Lemma init_regs_nth : forall n, nth n init_regs (ELit 0) = if Nat.eqb n 2 then e_sp0 else ELit 0.
Proof.
intros n. unfold init_regs.
do 32 (destruct n as [|n]; [reflexivity|]). cbn. destruct n; reflexivity.
Qed.
Lemma init_regs_ok : ltac2:(TCodec.tc2 tcn__AsanInitK "5&T8&QI&S8&QK%43321").
Proof.
intros r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
- assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. reflexivity.
- rewrite init_regs_nth. pose proof (ridx_range r) as Hlt.
destruct (Nat.eqb (ridx r) 2) eqn:H2.
+ apply Nat.eqb_eq in H2. rewrite edenot_e_sp0.
assert (r = 2%bv) by (rewrite <- (ridx_roundtrip r); rewrite H2; apply bv_eq; reflexivity). subst r. reflexivity.
+ rewrite edenot_lit. apply Nat.eqb_neq in H2.
rewrite <- (ridx_roundtrip r). rewrite <- (ridx_roundtrip r) in Hr0.
set (n := ridx r) in *. clearbody n.
do 32 (destruct n as [|n]; [first [exfalso; lia | vm_compute in Hr0 |- *; first [discriminate | reflexivity]] |]).
exfalso. lia.
Qed.
Lemma allowA_init : ltac2:(TCodec.tc2 tcn__AsanInitK "R4'D'9'@'I%2211%411&S>v0&QIvU2%43321(5(?&SC&S5%118%311&SD&T=&TG&S4%11>%3217%5281%711%=4FF91&S<%11D&T>+8%22?1%=241%C11%52:4%@271%B11%H4Q1Q141&TCvUI+TP0%<221%4212+XPPP0%H221%O11&TF+2+Q?%3221%O217%O219%Q1281%Q311%Q94QBQB91%J2;I%Q52L1%Q;11%M26L%Q82O1%Q:11%Q@4QIQI41(<%11QJ%QD3QK31%QE3QL;1%QF3QMM1%QG3QNQ91%R33QNQI1").
Proof.
pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4).
unfold allowA, cs0, init_acs_of, init_acs_of_with, init_vis. cbn [a_vis a_ghost app flat_map allow1 fst snd].
unfold sh_lo, sh_hi. cbn [fst snd]. rewrite !u_e_top, !u_e_stk_len.
unfold uE. rewrite !edenot_lit, !u64_lit by (unfold CEIL; lia). reflexivity.
Qed.
Lemma abytes_init : ltac2:(TCodec.tc2 tcn__AsanInitK "N'C&T?&QG&S>v0&QIvU2%43321%611&T=&S=&TG&S4%119&S5%11;%5231%711&TF+2+Q?%3221&R3%<221%>11%@281%I2B1&R0%K231%M231").
Proof.
pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof (if_shadow _ _ _ IMG) as S1.
pose proof usp_lo as UL. pose proof usp_hi as UH.
rewrite allowA_init. cbn [A_bytes fst snd]. unfold vis_cost, CEIL, LIMIT, target_alloc_limit.
replace (img_lo A + (img_hi A - img_lo A)) with (img_hi A) by lia.
set (P := usp / 4096 * 4096). assert (HP : usp - 4095 <= P <= usp) by (unfold P; lia).
replace ((P - 8388608) + (2 ^ 47 + 8388608 - P)) with (2 ^ 47) by lia.
assert (P1 : forall z, z mod 4096 = 0 -> pagedown z = z) by (intros z Hz; unfold pagedown; lia).
assert (P2 : forall z, z mod 4096 = 0 -> pageup z = z) by (intros z Hz; unfold pageup; lia).
rewrite (P1 (img_lo A) I3), (P2 (img_hi A) I4).
rewrite (P2 (2 ^ 47) eq_refl).
assert (PD : forall z, z - 4095 <= pagedown z <= z) by (intros z; unfold pagedown; lia).
pose proof (PD (P - 8388608)).
pose proof (pageup_minus_pagedown (shadow_off A + img_lo A / 8) (shadow_off A + img_hi A / 8) ltac:(lia)).
pose proof (pageup_minus_pagedown (shadow_off A + (P - 8388608) / 8) (shadow_off A + 2 ^ 47 / 8) ltac:(lia)).
clearbody P. split; lia.
Qed.
Theorem init_cs_ok : ltac2:(TCodec.tc2 tcn__AsanInitK "='S@vUBv0&R0&QL&QMvU6&QIvU2&QK&QJ&QO%<;;:987654321").
Proof.
destruct model0_facts as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof brk_range as [B1 B2]. pose proof (u64_range brk0) as [B3 B4].
destruct abytes_init as [AB1 AB2].
constructor; cbn [cs0 init_acs_of init_acs_of_with a_ss s_regs s_log kn s_know a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_hna a_hlz];
rewrite ?M1, ?M2, ?M3, ?M4, ?M5, ?M6, ?M7, ?M8, ?M9, ?M10, ?M11, ?M12, ?M13.
- exact init_regs_ok.
- reflexivity.
- exact init_kn_ok.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- constructor.
- apply seps_nil.
- unfold model_ivs_wf. rewrite M5, M6, M7. repeat split; try (intros q []).
unfold model0. apply init_sp_ok_init_model. exact Hsp.
- constructor.
- constructor.
- intros z Hz. exact Hz.
- constructor.
- constructor.
- rewrite app_nil_r, (if_sizes _ _ _ IMG). lia.
- rewrite u_e_sp0, u_e_sppg. unfold APSK.pagedown, model0, init_model, usp. cbn -[Z.mul Z.div Z.sub Z.add].
destruct Hsp as (S1 & S2 & S3). repeat split; [lia | exact S2].
- unfold escale. rewrite mkMd_denot. cbn [edenot]. apply bv_eq. rewrite u_mul64, u64_lit by lia.
destruct uE0 as (_ & _ & _ & _ & _ & _ & U7). unfold uE in U7. cbn [edenot] in U7. rewrite U7.
rewrite Z.mod_small by lia. lia.
- lia.
- lia.
- exact AB1.
- constructor; rewrite ?M8, ?M9, ?M13; [constructor | intros p [] | intros p [] | intros p [] | lia].
- intros a _ Hm. exact (eq_sym Hm) || discriminate Hm.
- split; [intros; reflexivity | intros; reflexivity].
- reflexivity.
- reflexivity.
- intros HH. discriminate HH.
Qed.
Theorem init_cfg_eq : ltac2:(TCodec.tc2 tcn__AsanInitK "N'H'D'I&TDr1%211&RAv0%211%83741'O&Q0vUBr2vU@vUCvU0vU>vUA&R0&QN%:9987654321&S?&QK&QJ&QO%45>3B21%J3A61p0C1pYHM1").
Proof.
intros apc Hpc. unfold init_config, cfg_of. cbn [in_argv in_envp in_uid in_hwcap inp]. rewrite init_mkst. rewrite Hpc. reflexivity.
Qed.
End Init.
