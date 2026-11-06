(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
SimInv ExitSim CatSim CatExec PropExec SeqExec Hoare ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes FileSim AgentLib AgentNodes.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__LibWritev () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Init.Specif."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs."; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite."; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.LibWritev.FPX_1.WithSegs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1O"; "1Some"; "1app"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2I"; "2and"]; ["2eq"; "3le"; "4proj1_sig"; "5firstn"; "5map"; "5skipn"; "6Z"; "0K"; "7word_to_nat"; "8check_syscall"; "9check_writev"; ":check_result"; ";Segment"; "<fetch_word"; "<is_ecall"; "<machine_state"]; ["<ms_gpr"; "<ms_mem"; "<ms_read_byte"; "<ms_rom"; "<ms_svc_pending"; "<set_gpr0"; "<word_to_le_bytes"; "=SpuriousCfg"; "=advance_past_svc"; "=config"; "=mkCfg"; ">FdChannel"; ">FdEntry"; ">ImpOk"; ">IovEntry"; ">Model"]; [">SyscallEffect"; ">SyscallInput"; ">TASK_SIZE"; ">WriteEv"; ">access_okb"; ">cap_iovecs_aux"; ">copy_iovecs_aux"; ">event"; ">fd_lookup"; ">gather_iovecs"; ">import_iovecs"; ">in_arg"; ">in_sysno"; ">iov_entry"; ">iov_import"; ">iovs_access_okb"]; [">iovs_total"; ">m_fds"; ">m_halted"; ">m_vm_lazy"; ">read_bytes_map"; ">read_iovec_entry"; ">read_u64"; "?fd32"; "@rw_bytes_max"; "Abvmap"; "Biov_array"; "Biov_bufs"; "Biov_bufs_ok"; "Cgetr"; "Cmkst"; "Crdn"]; ["Cregupd"; "Cseg_rom"; "Cv_addi"; "DTSet"; "Dt_alt"; "Dt_emit"; "Dt_eq"; "Dt_write_ch"; "Dwr_index"; "Esrealizes"; "Fconcat"; "Gadd"; "Gle"; "Glt"; "Gmul"; "Gof_nat"]; ["Gpow"; "Gto_nat"; "0T"; "0a"; "0b"; "0b1"; "0b2"; "0bs"; "0bs1"; "0bs2"; "0bss"; "0c"; "0ch"; "0eff"; "0fd"; "0fx"]; ["0i"; "0iov"; "0iovs"; "0k"; "0left"; "0m"; "0mem"; "0model"; "0ms"; "0n"; "0n1"; "0n2"; "0pc"; "0r"; "0regs"; "0scfg"]; ["0segs"; "HBV"; "HZ_to_bv"; "Hbv"; "Hbv_add"; "Hbv_unsigned"; "0tr"; "0v"; "0w"; "0x"; "0x8"; "0z"]]).
Section FPX_1. Context {fx : FPState}.
Lemma bv_add_Zform : ltac2:(TCodec.tc2 tcn__LibWritev "B'T3yR0%211'@&T4r2r1%33621&T2&RK&T5%12:6%22;6%4221%62=1%<3=81pV:>1pV8?1").
Proof.
intros a b. apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned. reflexivity.
Qed.
Lemma word_to_nat_Z : ltac2:(TCodec.tc2 tcn__LibWritev "J'F'?&RLzr1%3221&RM&S0+2+R0%3221%5271%;271'@'8&H&T2yR0r2%3221%511&S1%114%:3931p0<1pXHI1").
Proof.
intros z Hz. unfold word_to_nat. rewrite Z_to_bv_unsigned.
rewrite (bv_wrap_small 64 z) by (change (bv_modulus 64) with (2^64)%Z; lia). reflexivity.
Qed.
Lemma u64_roundtrip' : ltac2:(TCodec.tc2 tcn__LibWritev ";'T3yR0%211'@&T2&T5r1%2261%4271%63713pXD81").
Proof. intros x. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.
Lemma access_okb_of_le : ltac2:(TCodec.tc2 tcn__LibWritev "K'T3yR0%211'F&RLzr1%3221&RK&T5r3%22:1r2%5221&QB%;221'@'4&QDr4%221:(=%63521p081p0A1pWDF1pV:H1").
Proof.
intros b n Hn H. unfold access_okb. pose proof (bv_unsigned_in_range 64 b) as [Hb _].
apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.
Lemma check_syscall_writev : ltac2:(TCodec.tc2 tcn__LibWritev "Q2'QA'Q@'Q?'@'F&T5yR0&QLr3%211%5241+R2%93821'K&Ir4r2%33291&J&R7&QK(1%2271%411u1%52:1u2%72<1%:6=531D<%J3@<1p0B1pW<M1pVLO1pW2Q11").
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.
Lemma t_alt_wall_nat : ltac2:(TCodec.tc2 tcn__LibWritev "QJ'T3yR0%211'7y8%511%311&RCr1(9'QG%211%411'Au1&6r3%22<1%5241&RF&RD'8%C1<'?r2%<2;1r6%<2F1%?241%6241&RE&D(QCr7%211&C%13O<:%64Q0K31&E%13Q2?=%94Q3N61r5%<221%=361Q3%E2?1qX>G1qW8I1%K2J1%@17r4%C4Q=Q821%E21Q3%Q1251p0Q31p0Q:1pQ@Q@1pV@QB1pVJQG1").
Proof.
intros ch bs K HK Hnb tr. rewrite <- (t_alt_wall ch bs K HK Hnb tr). unfold t_alt. split.
- intros [k [Hk Ht]]. exists (exist _ k Hk). exact Ht.
- intros [[k Hk] Ht]. exists k. split; [exact Hk | exact Ht].
Qed.
Lemma rz_wall : ltac2:(TCodec.tc2 tcn__LibWritev "R5'7'L%211'Q7'Q9'T3yR0%211y8%411%:11&RC'Au1&6r2%2271%5241(9'QG%211%611'RIr8r7r6&RD&RHr4%211&RE&D(QC%118&C&B'8'?r1%K2J1%J2O?%M231%5231qWD71%93816r5%<3Q521%@4Q6L>1&E%13Q854%C4Q9OA1%E21G%F251qW2H1%L2I1%Q14Q0ON1r9%J4Q@Q6H<%L21N%Q543Q4Q31p051p0Q81p0Q=1pQ@QD1pV@QF1pVJQJ1pVHQN1pX0R01pX2R21").
Proof.
intros segs scfg c ch bs K Hnb HK H. eapply srz_conseq; [exact H | apply t_alt_wall; assumption].
Qed.
Section WithSegs.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Lemma read_u64_rdn : ltac2:(TCodec.tc2 tcn__LibWritev "Q='O'T3yR0%211'@':y8%611%311p061&Q3r3%211&RAvT0%211%<3741'7%11;%>11&R?&Q1r4%211u8%54;2>1(2&Q6r2%2251%42<1%K3<61%K1M&R6&Q2r5%211%421?%<2Q3K%Q33721p091p0I1pX@Q71pV8Q81pWBQ<1").
Proof.
intros ms a v Hrom H. unfold read_u64.
rewrite read_bytes_map_read_byte, (ms_read_bytes_rdn segs) by exact Hrom.
change (word_to_nat (Z_to_bv 64 8)) with 8%nat. rewrite H.
f_equal. apply le_word_v. apply bytes_le_to_Z_8.
Qed.
Lemma read_bytes_map_rdn : ltac2:(TCodec.tc2 tcn__LibWritev "Q='O'T3yR0%211'7y8%511%311'@':%114p081&Q3r4%211&RAvT0%211%:3741%:1<&R?&Q1r5%211&Hr3%211%74;4>1(2r2%22G1%G3<41&R4&Q2r6%211%431>G%92N<%N3C21p081p0F1pV@Q21pWDQ71pV8Q81pWBQ<1").
Proof.
intros ms a n bs Hrom H.
rewrite read_bytes_map_read_byte, (ms_read_bytes_rdn segs) by exact Hrom. exact H.
Qed.
Fixpoint iov_array (mem : word -> option byte) (iov : word) (iovs : list (word * word)) : Prop :=
match iovs with
| [] => True
| (b, n) :: r =>
rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b)
/\ rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n)
/\ (bv_unsigned n < 2 ^ 63)%Z
/\ iov_array mem (Z_to_bv 64 (bv_unsigned iov + 16)) r
end.
Lemma read_iovec_entry_of_array : ltac2:(TCodec.tc2 tcn__LibWritev "QA'O'T3yR0%211'7'<%1233%311'@':y8%:11%311p0:1&Q3r5%211&RAvT0%211%<3741&R:&Q1r6%211r2(5(;r4%24JJ>1r3%53I21%;3871'QM&R5&Q2r7%211%4218(Q>%12AI%Q13831p0:1p0G1pW4Q91pWLQ61pWDQ;1pV:Q<1pWBQ@1").
Proof.
intros ms b n r iov Hrom (Hb & Hn & Hlt & _). unfold read_iovec_entry.
rewrite (read_u64_rdn ms iov b Hrom Hb).
rewrite bv_add_Zform. change (bv_unsigned (8 : word)) with 8%Z.
rewrite (read_u64_rdn ms _ n Hrom Hn).
rewrite (proj2 (Z.leb_gt _ _) Hlt). reflexivity.
Qed.
Lemma copy_iovecs_of_array : ltac2:(TCodec.tc2 tcn__LibWritev "Q;'O'7'<'T3yR0%211%4211%611'@':y8%811%311p081&Q3r3%211&RAvT0%211%<3741&R:&Q1r4%211r2%5321;'QN&QF&Q2r5%211&6%12K:%633C1(Q=%11=%M3:31p0<1p0C1pW4Q31pW6Q21pWBQ:1").
Proof.
intros ms iovs; induction iovs as [|[b n] r IH]; intros iov Hrom Ha; [reflexivity|].
cbn [length copy_iovecs_aux].
rewrite (read_iovec_entry_of_array ms b n r iov Hrom Ha).
destruct Ha as (_ & _ & _ & Hr).
rewrite bv_add_Zform. change (bv_unsigned (16 : word)) with 16%Z.
rewrite (IH _ Hrom Hr). reflexivity.
Qed.
Fixpoint iov_bufs (mem : word -> option byte) (iovs : list (word * word)) (bss : list (list byte)) : Prop :=
match iovs, bss with
| [], [] => True
| (b, n) :: r, bs :: bss' => rdn segs mem b (word_to_nat n) = Some bs /\ iov_bufs mem r bss'
| _, _ => False
end.
Lemma gather_of_bufs : ltac2:(TCodec.tc2 tcn__LibWritev "Q='O'7'<'T3yR0%211%4211%611y8%611%911%:11'@':%115p0:1&Q3r3%211&RAvT0%211%:3741&R;&Q1r4%211r2%532;1%@1C&QI&Q2r5%211%4219(2&RJ%12LD%32L1%K3:51p0<1p0C1pVFO1pW6Q41pWBQ<1").
Proof.
intros ms iovs; induction iovs as [|[b n] r IH]; intros [|bs bss] Hrom Hb; cbn in Hb; try contradiction.
- reflexivity.
- destruct Hb as [H1 H2]. cbn [gather_iovecs concat].
rewrite (read_bytes_map_rdn ms b n bs Hrom H1), (IH bss Hrom H2). reflexivity.
Qed.
Lemma cap_iovecs_id : ltac2:(TCodec.tc2 tcn__LibWritev "F'7'<'T3yR0%211%4211%611'F&RL&R0r2%211r1%5221'@&QEr3%2217%43<12p061pW:=1pW6?1").
Proof.
induction iovs as [|[b n] r IH]; intros left H; [reflexivity|].
cbn [cap_iovecs_aux]. cbn [iovs_total] in H. pose proof (iovs_total_nonneg r).
rewrite Z.min_r by lia. rewrite u64_roundtrip', IH by lia. reflexivity.
Qed.
Fixpoint iov_bufs_ok (iovs : list (word * word)) : Prop :=
match iovs with
| [] => True
| (b, n) :: r => (bv_unsigned b + bv_unsigned n <= TASK_SIZE)%Z /\ iov_bufs_ok r
end.
Lemma iovs_access_okb_of_ok : ltac2:(TCodec.tc2 tcn__LibWritev "C'7'<'T3yR0%211%4211%611&R<r1%211'@'4&QOr2%211(=%63521p081pW6<1").
Proof.
induction iovs as [|[b n] r IH]; intros H; [reflexivity|].
destruct H as [Hb Hr]. unfold iovs_access_okb. cbn [forallb fst snd].
rewrite (access_okb_intro b n Hb). cbn [andb]. exact (IH Hr).
Qed.
Lemma import_iovecs_of_array : ltac2:(TCodec.tc2 tcn__LibWritev "R:'O'7'<'T3yR0%211%4211%611'@':y8%811%311p081&Q3r3%211&RAvT0%211%<3741'?'Au1&6%12C:%4231uQP0%6231%8231&RL&RK&T5%12MB&RN+@&ROr4%>2Q01%311%6251%:281&QB%=221&R:&Q1r6%211r5%532<1&R<%115'QN&QJ&Q2r8%211&T2r7%Q32QE1%H11%42QI1%936@1(Q=%116%QI3=31p0?1p0B1p0I1p0Q81p0QB1pW4R21pW6R11pWBR91").
Proof.
intros ms iovs iov Hrom Hcnt Hok Harr Hbok. unfold import_iovecs.
destruct iovs as [|[b n] r]; [cbn in Hcnt; lia|].
destruct r as [|[b2 n2] r2].
-
cbn [length] in *. change (Z.of_nat 1) with 1%Z in *.
rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
rewrite (access_okb_of_le iov 16) by lia.
rewrite (read_iovec_entry_of_array ms b n [] iov Hrom Harr).
destruct Hbok as [Hb _]. pose proof (u64_range n).
rewrite (access_okb_of_le b (Z.min (bv_unsigned n) MAX_RW_COUNT))
by (unfold MAX_RW_COUNT in *; lia).
reflexivity.
-
set (cnt := Z.of_nat (length ((b, n) :: (b2, n2) :: r2))) in *.
assert (Hc2 : (2 <= cnt <= 1024)%Z) by (unfold cnt; cbn [length] in *; lia).
assert (E1 : bv_eqb (Z_to_bv 64 cnt) (Z_to_bv 64 1) = false).
{ unfold bv_eqb. apply Z.eqb_neq. rewrite !u64_lit by lia. lia. }
assert (E0 : bv_eqb (Z_to_bv 64 cnt) (Z_to_bv 64 0) = false).
{ unfold bv_eqb. apply Z.eqb_neq. rewrite !u64_lit by lia. lia. }
rewrite E1, E0. rewrite u64_lit by lia.
replace ((IOV_MAX <? cnt)%Z) with false by (symmetry; apply Z.ltb_ge; unfold IOV_MAX; lia).
rewrite (access_okb_of_le iov (16 * cnt)) by lia.
rewrite word_to_nat_Z by lia. unfold cnt. rewrite Nat2Z.id.
rewrite (copy_iovecs_of_array ms _ iov Hrom Harr).
rewrite (iovs_access_okb_of_ok _ Hbok). reflexivity.
Qed.
Lemma writev_check : forall ms x8 model (fd : Z) (iov : word) iovs bss,
ms_rom ms = seg_rom segs ->
fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
(0 < fd < 2^31)%Z ->
bv_unsigned x8 = 66%Z ->
ms_gpr ms 0 = Z_to_bv 64 fd ->
ms_gpr ms 1 = iov ->
ms_gpr ms 2 = Z_to_bv 64 (Z.of_nat (length iovs)) ->
(1 <= length iovs <= 1024)%nat ->
(bv_unsigned iov + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
iov_array (ms_mem ms) iov iovs ->
iov_bufs_ok iovs ->
iov_bufs (ms_mem ms) iovs bss ->
let bs := concat bss in
let tot := iovs_total iovs in
(1 <= tot)%Z -> (tot <= rw_bytes_max)%Z -> (tot <= 2 ^ 30)%Z ->
let CA := import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs))) in
Z.of_nat (length bs) = tot /\
forall eff, check_syscall (sys_input segs ms x8) eff model
= match eff with
| mkEffectU ret [] [] [] [] ci =>
if (1 <=? bv_unsigned ret)%Z && (bv_unsigned ret <=? tot)%Z && negb (addr_is_error_b ret)
then if access_ranges_eqb ci (CA ++ iov_prefix_accesses iovs (Z.to_nat (bv_unsigned ret)))
then CheckOk model (map (WriteEv (Z_to_bv 64 fd)) (firstn (Z.to_nat (bv_unsigned ret)) bs))
else CheckReject
else CheckReject
| _ => CheckReject
end.
Proof.
intros ms x8 model fd iov iovs bss Hrom Hfd Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs bs tot Ht1 Htmax Ht30 CA.
pose proof (gather_of_bufs ms iovs bss Hrom Hbufs) as Hg. fold bs in Hg.
pose proof (gather_iovecs_length _ _ _ Hg) as Hlen. fold tot in Hlen.
split; [exact Hlen|].
intros eff.
rewrite (check_syscall_writev (sys_input segs ms x8) eff model) by (rewrite in_sysno_si; exact Hno).
rewrite in_arg0_si, in_arg1_si, in_arg2_si, H0, H1, H2.
rewrite fd32_id by (rewrite u64_lit; lia).
assert (Hcnt32 : iovcnt32 (Z_to_bv 64 (Z.of_nat (length iovs))) = Z_to_bv 64 (Z.of_nat (length iovs))).
{ unfold iovcnt32, abi_low32. rewrite u64_lit by lia. rewrite Z.mod_small by lia. reflexivity. }
unfold check_writev. rewrite Hfd.
replace (w_is0 (Z_to_bv 64 fd)) with false
by (symmetry; apply w_is0_pos; rewrite u64_lit; lia).
rewrite in_mem_si, Hcnt32.
rewrite (import_iovecs_of_array ms iovs iov Hrom Hcnt Hiok Harr Hbok).
assert (Hcap : cap_iovecs iovs = iovs).
{ unfold cap_iovecs. apply cap_iovecs_id. unfold MAX_RW_COUNT. lia. }
unfold writev_gathered. rewrite Hcap, (gather_prefix_full _ _ _ Hg).
cbv beta iota zeta. fold tot.
replace ((tot =? 0)%Z) with false by (symmetry; apply Z.eqb_neq; lia).
replace ((length bs =? 0)%nat) with false by (symmetry; apply Nat.eqb_neq; lia).
assert (Hlw : bv_unsigned (len_word bs) = tot).
{ unfold len_word. rewrite Hlen. apply u64_lit. lia. }
replace (addr_is_error_b (len_word bs)) with false
by (symmetry; unfold addr_is_error_b, two_pow_64; apply Z.ltb_ge; rewrite Hlw; lia).
cbv beta iota.
destruct eff as [ret ws zs us cs ci]. destruct ws; [|reflexivity]. destruct zs; [|reflexivity].
destruct us; [|reflexivity]. destruct cs; [|reflexivity].
rewrite Hlen. reflexivity.
Qed.
Lemma rz_writev_pending : ltac2:(TCodec.tc2 tcn__LibWritev "VJ'O'T3yR0%211'Q?'F'7'<%1255%311y8%:11%611%711'8&RCp021'@':%118p0A1&Q3r8%211&RAvT0%211%:3741%:1I&R2r7%211(0%11N%A3631&R3%11>(9%11N%F3N31&Q4r;%211(2r:%22Q:1%M3B41'Q<%N11&QH&R1%117&T2r9%22QD1%6241(Q;%113%?2;1%Q:3;41'?&RMz%221C&S0+2+O%3221%72H1%9261&T5r=%22R61+R2%QI3R521&Q0r?(1%3221r<%L2R>1%R03R>31r@u1%9221%R43RB16rAu2%=221&RO&6%12RC<%311%Q92RK1%R=3RK61'A%62RHI%22>1uQP0%4231%Q8231&RL&RK%Q12S5K&RN+@r>%A2S31%C11%5241%8271&QB%;221&R:&Q1rD%211%431Q3Q9&R<%11Q5&R;rF%811%331Q5Q9&RJ%12SBQ7+1&R0rC%211%M241%41@&R8%Q0221rE%811+N%R92R81%Q5231r1%Q=2QI1r2r6%QE2T41%QA231'RIvSO(Q:&Q8&Q5rNr3%QO11%S52TG1%5241%711rL%:221rG%118%?4T7>31p0A1p0F1pW8TE1rJ%B291&RD&RHr5%211&RE&D'QG(QC%SJ2U<:%211&C&B%RH2U7TD%RD2Q81%SH2Q81qWDU71%53U81Q;%73U<1Q9%=4U=<91%R013%@221qW2B1%F2C1%Q<4U4Q;H1p0K1p0QE1p0QK1p0QO1tV@UFR51p0R81p0R=1p0R@1p0RF1p0S31p0S:1p0SD1p0SI1p0T11p0T71p0TB1p0U01p0U81p0U>1p0UF1pV6V21pVFV61pW6V;1pW4VB1pVNVA1pW@VC1pXFVE1pWBVI1").
Proof.
intros ms x8 model fd iov iovs bss T Hrom Hh Hlazy Hsvc Hfd Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs bs
Ht1 Htmax Ht30 Hk.
destruct (writev_check ms x8 model fd iov iovs bss Hrom Hfd Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs
Ht1 Htmax Ht30)
as [Hlen Hchk]. fold bs in Hlen, Hchk.
set (tot := iovs_total iovs) in *.
set (CA := import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs)))) in *.
assert (Hnb : (1 <= length bs)%nat) by lia.
pose (effs := fun i : wr_index bs =>
mkEffectU (Z_to_bv 64 (Z.of_nat (proj1_sig i))) [] [] [] []
(CA ++ iov_prefix_accesses iovs (proj1_sig i))).
assert (Enx : forall i : wr_index bs,
mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat (proj1_sig i))))) model
= mkCfg (advance_past_svc (apply_effect ms (effs i))) model).
{ intros [k Hk']. cbn [proj1_sig]. unfold effs. cbn [proj1_sig].
rewrite <- (apply_effect_copyins_no_write ms (Z_to_bv 64 (Z.of_nat k)) (CA ++ iov_prefix_accesses iovs k)).
reflexivity. }
apply (srz_node segs scfg (mkCfg ms model) (wr_index bs)
(fun i => map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs))
(fun i => mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 (Z.of_nat (proj1_sig i))))) model)
(fun i => T (proj1_sig i)) (wr_full bs Hnb)).
2:{ intros [k [Hk1 Hk2]]. cbn [proj1_sig]. apply Hk; assumption. }
assert (Hku : forall k, (k <= length bs)%nat -> bv_unsigned (Z_to_bv 64 (Z.of_nat k)) = Z.of_nat k).
{ intros k Hk2. apply u64_lit. lia. }
apply (node_ok_of_pnode_sysno segs scfg ms model x8 66%Z); [exact Hsvc | exact Hno | exact injected_arm_66 |].
split.
- intros i. rewrite Enx. apply (sstep_of_check segs ms model x8); [exact Hh | exact Hsvc | | exact Hh | exact Hlazy].
destruct i as [k [Hk1 Hk2]]. unfold effs. cbn [proj1_sig]. rewrite Hchk.
rewrite (Hku k Hk2), Nat2Z.id.
rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia.
replace (addr_is_error_b (Z_to_bv 64 (Z.of_nat k))) with false
by (symmetry; unfold addr_is_error_b, two_pow_64; apply Z.ltb_ge; rewrite (Hku k Hk2); lia).
rewrite (proj2 (access_ranges_eqb_eq _ _) eq_refl). reflexivity.
- assert (Hinv : forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
exists i : wr_index bs, eff = effs i /\ m' = model /\ ev = map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs)).
{ intros [ret ws zs us cs ci] m' ev Hc. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
destruct cs; [|discriminate].
destruct ((1 <=? bv_unsigned ret)%Z && (bv_unsigned ret <=? tot)%Z && negb (addr_is_error_b ret))%bool eqn:Eb;
[|discriminate].
destruct (access_ranges_eqb ci (CA ++ iov_prefix_accesses iovs (Z.to_nat (bv_unsigned ret)))) eqn:Eci;
[|discriminate].
injection Hc as <- <-.
apply andb_true_iff in Eb as [Eb _]. apply andb_true_iff in Eb as [E1 E2].
apply Z.leb_le in E1. apply Z.leb_le in E2. apply access_ranges_eqb_eq in Eci.
assert (Hkr : (1 <= Z.to_nat (bv_unsigned ret))%nat /\ (Z.to_nat (bv_unsigned ret) <= length bs)%nat) by lia.
exists (exist _ (Z.to_nat (bv_unsigned ret)) Hkr). cbn [proj1_sig]. unfold effs. cbn [proj1_sig].
rewrite Z2Nat.id by lia. rewrite u64_roundtrip'. subst ci. repeat split; reflexivity. }
intros e st Hss.
destruct (sstep_svc_inv segs ms model x8 e st Hsvc Hss)
as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hmat & ->) | [(Hh2 & -> & Hmat & ->) | (code & Hh2 & -> & ->)]])
| (eff & Hc & -> & ->)].
+ destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat. injection Hmat as <-.
exists i. rewrite Enx. split; reflexivity.
+ destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat. discriminate.
+ destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). congruence.
+ exfalso. rewrite Hchk in Hc. destruct eff as [ret ws zs us cs ci].
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
destruct cs; [|discriminate]. destruct (_ && _)%bool; [destruct (access_ranges_eqb _ _)|]; discriminate.
Qed.
Lemma rz_writev2 : ltac2:(TCodec.tc2 tcn__LibWritev "XC&R9y5'T3yR0%211%5241':y8%611%311p061'Q?yQ0%;11'F'7%118'8&RCp021'@%?18&MvT0r=%3221(2r:%22?1%93841'4&Nr;%211(=%?3521%N1Q0&R2%11>(0%11Q4%E3531'<%12Q7Q7%M11&R3r>%211(9%116%N3631'Q<%Q>11&QH&R1r?%211&T2%12QGQ2%6231(Q;%113%Q42;1%Q;3;41'?&RMz%221E&S0+2+O%3221%72J1%9261&R=rD(T1+A(>%33R>21%6251+R2%I2R?1%QO3R?31rE+:%:3RE18%=231r@%Q02RF1%R63RF31rF+;%A3RL1?%D231%R;3RK17rG+<%F3S11D%I231%Q;2S1O%RA3S121%S01RF&R?rBu8%34RC?21&Q6rA%2241%RD2RN1%RK3951&RK&T5rC%22S@1+8%5221%QM2SC1%@4S0G1>%S43B1:rH%92SGQ?+@%<221%R42SJ1%G4S751E%S;3I1ArI%@2SNQ=+H%C221%R;2T11%N4S>51L%SB3Q01HrJ&H%11QN%Q34SC3QF1%SA2SKO%SH3Q621rK%61L%Q84SH2R41%SL3Q:15&RL%Q12T?I+Q0%Q4221&QB%5221%Q62TDQG%Q8261%8214%Q92TGQO%Q;241%;217+1%Q=2TKN%Q?218%?231%Q@2TNJ%QB21@&R8%C221%QD2U2H%QF218+N%S42S31%H231'Au1r1%3221r2&6&3%13U9Q4Q:%32U:1%9251'RIvSO(Q:&R>vS?&R@rQ7&ROr3%211%T52UK1%635S91&RBrQ6+4%3221rQ5&RA%11U?%@5?8431rQ4%C221%R31>%G4UDF21p0I1p0Q01pW8UM1rQ3%I5H<81:rQ2%L221&RD&RH%Q53V=R>RE%211&RE&D'QG(QCrQ1%U32VI1%311&C&BrL%QA3VI1RD%QC2VJ1%QI2QG1%U42QG1qWDVD1%73VE1QJ%93VO1QF%@4W0?;1%S913%C221qW2E1%I2F1%QI4VFQHK1p0Q01p0R61p0R<1p0RA1p0RF1p0RJ1p0RN1p0S51p0S:1p0SA1p0SI1p0T11p0T;1p0TF1p0TM1p0U31p0U;1p0UF1p0V11p0V?1p0VI1p0W01p0W71pV6WB1pVDWF1pVBWG1pWHX41pV>X51pWFX61pV<X71pW4X81pVNWO1pXBX11pW@X41pW>X61pWJX=1pWNX=1").
Proof.
intros regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 T HF HE Hh Hlazy Hfd Hfdr H17 H10 H11 H12
Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiok Hb1 Hb2 Ht1 Htmax Ht30 Hk.
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
pose proof (u64_range n1). pose proof (u64_range n2).
replace (bs1 ++ bs2) with (concat [bs1; bs2]) in * by (cbn; rewrite app_nil_r; reflexivity).
eapply (rz_writev_pending (epend regs pc mem (seg_rom segs) (getr regs 17)) (getr regs 17) model fd iov
[(b1, n1); (b2, n2)] [bs1; bs2] T);
[reflexivity | exact Hh | exact Hlazy | reflexivity | exact Hfd | exact Hfdr
| rewrite H17; apply u64_lit; lia
| rewrite ms_gpr_epend0; exact H10 | rewrite ms_gpr_epend1; exact H11 | rewrite ms_gpr_epend2; exact H12
| cbn; lia | change (Z.of_nat (length [(b1, n1); (b2, n2)])) with 2%Z; lia
| | cbn [iov_bufs_ok]; repeat split; assumption | | cbn [iovs_total]; lia | cbn [iovs_total]; lia
| cbn [iovs_total]; lia | ].
- cbn [iov_array ms_mem epend].
replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (Z_to_bv 64 (bv_unsigned iov + 24)).
2:{ change (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (at_ (at_ iov 16) 8).
rewrite at_at. reflexivity. }
repeat split; try assumption; lia.
- cbn [iov_bufs ms_mem epend]. repeat split; assumption.
- intros k Hk1 Hk2. rewrite adv_set_epend. apply Hk; assumption.
Qed.
Lemma rz_writev1 : ltac2:(TCodec.tc2 tcn__LibWritev "W@&R9y5'T3yR0%211%5241':y8%611%311p061'Q?yQ0%;11'F'7%118'8&RCp021'@%?18&MvT0r:%3221(2r7%22?1%93841'4&Nr8%211(=%?3521%N1Q0&R2%11>(0%11Q4%E3531'<%12Q7Q7%M11&R3r;%211(9%116%N3631'Q<%Q>11&QH&R1r<%211&T2%12QGQ2%6231(Q;%113%Q42;1%Q;3;41'?&RMz%221E&S0+2+O%3221%72J1%9261&R=rA(T1+A(>%33R>21%6251+R2%I2R?1%QO3R?31rB+:%:3RE18%=231r=%Q02RF1%R63RF31rC+;%A3RL1?%D231%R;3RK17rD+<%F3S11D%I231+1%Q<2S21%RB3S231%S11RG&R?r?u8%34RD@21&Q6r>%2241%RE2RO1%RL3951&RK&T5r@%22SA1+8%5221%QN2SD1%@4S1H1>%S53B1:rE&H%11C%E4S63:1%S42S>A%S;3H21&RL%?2SNQ=+@%B221&QB%5221%D2T3QK%F261%8214%92Q58%H2T7Q?&R8%<221%K2T:Q=+N%R;2R:1%@231'Au1r1%3221r2&6rF%22T@1%8241'RIvSO(Q:&R>vS?&R@rQ0&ROr3%211%S;2U11%635R?1&RBrO+4%3221rN&RA%11TE%@5?8431rM%C221%I1>%G4TJF21p0I1p0O1pW8U31rL%I5H<81:rK%L221&RD&RH%11R1&RE&D'QG(QCrJ%T82UN1%311&C&BrG%Q@2UN1%QF2QD1%T82QD1qWDUH1%63UI1QG%83V31QD%?4V4>:1%RC13%B221qW2D1%G2E1%QG4UJQFI1p0N1p0R31p0R81p0R<1p0R>1p0RB1p0RI1p0S01p0S:1p0SE1p0SM1p0T31p0T;1p0TF1p0U11p0U?1p0UI1p0V01p0V71pV6VB1pVBVF1pWFW31pV<W41pW4W51pVNVL1pXBVN1pW@W11pW>W31pWJW:1pWNW:1").
Proof.
intros regs pc mem model w fd iov b1 n1 bs1 T HF HE Hh Hlazy Hfd Hfdr H17 H10 H11 H12
Rb1 Rn1 Rs1 Hiok Hb1 Ht1 Htmax Ht30 Hk.
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
pose proof (u64_range n1).
replace bs1 with (concat [bs1]) in Hk by (cbn; rewrite app_nil_r; reflexivity).
replace bs1 with (concat [bs1]) by (cbn; rewrite app_nil_r; reflexivity).
eapply (rz_writev_pending (epend regs pc mem (seg_rom segs) (getr regs 17)) (getr regs 17) model fd iov
[(b1, n1)] [bs1] T);
[reflexivity | exact Hh | exact Hlazy | reflexivity | exact Hfd | exact Hfdr
| rewrite H17; apply u64_lit; lia
| rewrite ms_gpr_epend0; exact H10 | rewrite ms_gpr_epend1; exact H11 | rewrite ms_gpr_epend2; exact H12
| cbn; lia | change (Z.of_nat (length [(b1, n1)])) with 1%Z; lia
| | cbn [iov_bufs_ok]; split; [assumption | exact I] | | cbn [iovs_total]; lia | cbn [iovs_total]; lia
| cbn [iovs_total]; lia | ].
- cbn [iov_array ms_mem epend]. repeat split; try assumption; lia.
- cbn [iov_bufs ms_mem epend]. split; [assumption | exact I].
- intros k Hk1 Hk2. rewrite adv_set_epend. apply Hk; assumption.
Qed.
Lemma rz_writev2_wall : ltac2:(TCodec.tc2 tcn__LibWritev "X=&R9y5'T3yR0%211%5241':y8%611%311p061'Q?yQ0%;11'F'7%118&RC'@%=16&MvT0r=%3221(2r:%22=1%93841'4&Nr;%211(=%?3521%L1N&R2%11>(0%11Q2%E3531'<%12Q5Q5%K11&R3r>%211(9%116%N3631'Q<%Q<11&QH&R1r?%211&T2%12QEQ2%6231(Q;%113%Q42;1%Q;3;41'?&RMz%221E&S0+2+O%3221%72J1%9261&R=rD(T1+A(>%33R<21%6251+R2%I2R=1%QO3R=31rE+:%:3RC18%=231r@%Q02RD1%R63RD31rF+;%A3RJ1?%D231%R;3RI17rG+<%F3RO1D%I231%Q;2ROO%RA3RO21%RN1RD&R?rBu8%34RC?21&Q6rA%2241%RD2RL1%RK3951&RK&T5rC%22S>1+8%5221%QM2SA1%@4S0G1>%S43B1:rH%92SEQ?+@%<221%R42SH1%G4S751E%S;3I1ArI%@2SLQ=+H%C221%R;2SO1%N4S>51L%SB3Q01HrJ&H%11QN%Q34SC3QF1%SA2SIO%SH3Q621rK%61L%Q84SH2R41%SL3Q:15&RL%Q12T=I+Q0%Q4221&QB%5221%Q62TBQG%Q8261%8214%Q92TEQO%Q;241%;217+1%Q=2TIN%Q?218%?231%Q@2TLJ%QB21@&R8%C221%QD2U0H%QF218+N%S42S31%H231'QG%SK11%R<11'8'Au1r1%3221r2&6&3rL%23U<1Q9%42U=1%:261'RIvSO(Q:&R>vS?&R@rQ8&ROr3%211%T:2UN1%635S>1&RBrQ7+4%3221rQ6&RA%11UD%@5?8431rQ5%C221&RE&D(QCrQ3%TJ2V>1%311&ErM%Q33V=1Q2%33V>G1%94V?Q?51%;21R=%Q24V4Q1=1p0Q41p0Q<1pW8QA1rQ4%Q45Q3GC1E%Q621?rQ1%U:2VN1%C11%QA3VKRHRN%F4VLQL21%H21S7%Q?4VAQ>71p0;1p0QN1p0R21p0R81p0R=1p0RB1p0RF1p0RJ1p0S11p0S61p0S=1p0SE1p0SM1p0T71p0TB1p0TI1p0TO1p0U71p0UB1p0UM1p0V;1p0VE1p0VL1p0W31pQ@W>1pVDW@1pVBWA1pWHWN1pV>WO1pWFX01pV<X11pW4X21pVNWI1pXBWK1pW@WN1pW>X01pWJX71pWNX71").
Proof.
intros regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 K HF HE Hh Hlazy Hfd Hfdr H17 H10 H11 H12
Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiok Hb1 Hb2 Ht1 Htmax Ht30 HK Hk.
pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (rdn_length segs mem _ _ _ Rs2) as L2.
pose proof (u64_range n1). pose proof (u64_range n2).
apply rz_wall; [rewrite length_app; unfold word_to_nat in L1, L2; lia | exact HK |].
eapply (rz_writev2 regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2
(fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K)); eassumption.
Qed.
Lemma rz_writev1_wall : ltac2:(TCodec.tc2 tcn__LibWritev "W:&R9y5'T3yR0%211%5241':y8%611%311p061'Q?yQ0%;11'F'7%118&RC'@%=16&MvT0r:%3221(2r7%22=1%93841'4&Nr8%211(=%?3521%L1N&R2%11>(0%11Q2%E3531'<%12Q5Q5%K11&R3r;%211(9%116%N3631'Q<%Q<11&QH&R1r<%211&T2%12QEQ2%6231(Q;%113%Q42;1%Q;3;41'?&RMz%221E&S0+2+O%3221%72J1%9261&R=rA(T1+A(>%33R<21%6251+R2%I2R=1%QO3R=31rB+:%:3RC18%=231r=%Q02RD1%R63RD31rC+;%A3RJ1?%D231%R;3RI17rD+<%F3RO1D%I231+1%Q<2S01%RB3S031%RO1RE&R?r?u8%34RD@21&Q6r>%2241%RE2RM1%RL3951&RK&T5r@%22S?1+8%5221%QN2SB1%@4S1H1>%S53B1:rE&H%11C%E4S63:1%S42S<A%S;3H21&RL%?2SLQ=+@%B221&QB%5221%D2T1QK%F261%8214%92Q58%H2T5Q?&R8%<221%K2T8Q=+N%R;2R:1%@231'QG%S211%QH11'8'Au1r1%3221r2&6rG%22TB1%8241'RIvSO(Q:&R>vS?&R@rQ1&ROr3%211%S?2U31%635RC1&RBrQ0+4%3221rO&RA%11TI%@5?8431rN%C221&RE&D(QCrL%SO2UC1%311&ErH%23UBF1%84UCQ<41%:21Q3%Q14U8Q0<1p0Q31p0Q91pW8Q>1rM%Q35Q2FB1D%Q521>rJ%T>2V21%B11rF%E4V0QI21%G21RA%Q>4UEQ=71p0;1p0QK1p0QO1p0R41p0R81p0R:1p0R>1p0RE1p0RL1p0S61p0SA1p0SI1p0SO1p0T71p0TB1p0TM1p0U;1p0UE1p0UL1p0V31pQ@V>1pVBV@1pWFVM1pV<VN1pW4VO1pVNVF1pXBVH1pW@VK1pW>VM1pWJW41pWNW41").
Proof.
intros regs pc mem model w fd iov b1 n1 bs1 K HF HE Hh Hlazy Hfd Hfdr H17 H10 H11 H12
Rb1 Rn1 Rs1 Hiok Hb1 Ht1 Htmax Ht30 HK Hk.
pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (u64_range n1).
apply rz_wall; [unfold word_to_nat in L1; lia | exact HK |].
eapply (rz_writev1 regs pc mem model w fd iov b1 n1 bs1
(fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)); eassumption.
Qed.
Lemma rz_writev2_ch : ltac2:(TCodec.tc2 tcn__LibWritev "WL&R9y5'T3yR0%211%5241':y8%611%311p061'Q?yQ0%;11'F'7%118&RC'@%=16&MvT0r=%3221(2r:%22=1%93841'4&Nr;%211(=%?3521%L1N&R2%11>(0%11Q2%E3531'<%12Q5Q5%K11&R3r>%211(9%116%N3631'Q<%Q<11&QH&R1r?%211&T2%12QEQ2%6231(Q;%113%Q42;1%Q;3;41'?&RMz%221E&S0+2+O%3221%72J1%9261&R=rD(T1+A(>%33R<21%6251+R2%I2R=1%QO3R=31rE+:%:3RC18%=231r@%Q02RD1%R63RD31rF+;%A3RJ1?%D231%R;3RI17rG+<%F3RO1D%I231%Q;2ROO%RA3RO21%RN1RD&R?rBu8%34RC?21&Q6rA%2241%RD2RL1%RK3951&RK&T5rC%22S>1+8%5221%QM2SA1%@4S0G1>%S43B1:rH%92SEQ?+@%<221%R42SH1%G4S751E%S;3I1ArI%@2SLQ=+H%C221%R;2SO1%N4S>51L%SB3Q01HrJ&H%11QN%Q34SC3QF1%SA2SIO%SH3Q621rK%61L%Q84SH2R41%SL3Q:15&RL%Q12T=I+Q0%Q4221&QB%5221%Q62TBQG%Q8261%8214%Q92TEQO%Q;241%;217+1%Q=2TIN%Q?218%?231%Q@2TLJ%QB21@&R8%C221%QD2U0H%QF218+N%S42S31%H231'8'Au1r1%3221r2&6&3%13U8Q5Q;%32U91%9251'RIvSO(Q:&R>vS?&R@rQ7&ROr3%211%T62UJ1%635S:1&RBrQ6+4%3221rQ5&RA%11U@%@5?8431rQ4%C221%F4UDE1R4p0H1p0O1pW8Q41rQ3%H5G;719rQ2%K221&RGrQ0%TL2V@1%Q53V<R?RF%4321RN%Q34V1Q261p0;1p0QA1p0QG1p0QL1p0R11p0R51p0R91p0R@1p0RE1p0RL1p0S41p0S<1p0SF1p0T11p0T81p0T>1p0TF1p0U11p0U<1p0UJ1p0V41p0V;1p0VB1pQ@VM1pVDVO1pVBW01pWHW=1pV>W>1pWFW?1pV<W@1pW4WA1pVNW81pXBW:1pW@W=1pW>W?1pWJWF1pWNWF1").
Proof.
intros. unfold t_write_ch.
eapply (rz_writev2 regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 (fun _ => K)); eassumption.
Qed.
Lemma rz_writev1_zero : ltac2:(TCodec.tc2 tcn__LibWritev "UD&R9y5'T3yR0%211%5241':y8%611%311p061'Q?yQ0%;11'F&RC'@%;14&MvT0r8%3221(2r5%22;1%93841'4&Nr6%211(=%?3521%J1L&R2%11>(0%11Q0%E3531'7'<%12Q4Q4%311&R3r9%211(9%116%O3631'Q<%Q;11&QH&R1r:%211&T2%12QDQ3%6231(Q;%113%Q52;1%Q<3;41'?&RMz%221E&S0+2+O%3221%72J1%9261&R=r?(T1+A(>%33R;21%6251+R2%I2R<1%R03R<31r@+:%:3RB18%=231r;%Q02RC1%R73RC31rA+;%A3RI1?%D231%R<3RH17rB+<%F3RN1D%I231+1%Q<2RO1%RC3RO31%QN1RL%RO11&R?r=u8%34RFA21&Q6r<%2241%RG291%RN3951&RK&T5r>%22S?1+8%5221%QO2SB1%@4S3I1>%R12SDQH%>2@1%S32E1%S:3E41&RL%<2SIQD+@%?221&QB%5221%6252&R8%82R41'RIvSO(Q:&R>vS?&R@rH%231QHD&RBrG+4%3221rF&RA%11SO%<5;8431rE%?221%B4T3A1R5rI%A5@1>;6%C219%F4T7E1R2p051p0I1p0L1p0N1p0Q51p0QB1p0QN1p0R61p0R<1p0RD1p0RO1p0S:1p0SH1p0T31p0T:1p0TA1pQ@TL1pV<U81pW4U91pVNU01pXBU21pW@U51pW>U71pWJU>1pWNU>1").
Proof.
intros regs pc mem model w fd iov b1 K HF HE Hh Hlazy Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Hiok Hb1 Hmax Hc.
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
assert (Hno : bv_unsigned (getr regs 17) = 66%Z) by (rewrite H17; apply u64_lit; lia).
assert (Harr : iov_array (ms_mem ms) iov [(b1, Z_to_bv 64 0)]).
{ cbn [iov_array ms_mem ms epend]. refine (conj Rb1 (conj Rn1 (conj _ I))). rewrite u64_lit by lia. lia. }
assert (Himp : import_iovecs (ms_read_byte ms) iov (Z_to_bv 64 1) = ImpOk [(b1, Z_to_bv 64 0)]).
{ unfold import_iovecs. rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
rewrite (access_okb_of_le iov 16) by lia.
rewrite (read_iovec_entry_of_array ms b1 (Z_to_bv 64 0) [] iov eq_refl Harr).
rewrite u64_lit by lia. change (Z.min 0 MAX_RW_COUNT) with 0%Z.
rewrite (access_okb_of_le b1 0) by lia. reflexivity. }
assert (Hacc : import_iovecs_accesses (ms_read_byte ms) iov (Z_to_bv 64 1) = [(iov, 16%nat)]).
{ unfold import_iovecs_accesses. rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
rewrite (access_okb_of_le iov 16) by lia. reflexivity. }
eapply (rz_ret_only_copyins_silent segs scfg ms model (getr regs 17) [(iov, 16%nat)] (Z_to_bv 64 0) model);
[exact Hh | reflexivity | | exact Hh | exact Hlazy | unfold ms; rewrite adv_set_epend; exact Hc].
intros eff.
rewrite (check_syscall_writev (sys_input segs ms (getr regs 17)) eff model) by (rewrite in_sysno_si; exact Hno).
rewrite in_arg0_si, in_arg1_si, in_arg2_si.
assert (G0 : ms_gpr ms 0 = Z_to_bv 64 fd) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
assert (G1 : ms_gpr ms 1 = iov) by (unfold ms; rewrite ms_gpr_epend1; exact H11).
assert (G2 : ms_gpr ms 2 = Z_to_bv 64 1) by (unfold ms; rewrite ms_gpr_epend2; exact H12).
rewrite G0, G1, G2.
rewrite fd32_id by (rewrite u64_lit; lia).
unfold check_writev. rewrite Hfd.
replace (w_is0 (Z_to_bv 64 fd)) with false by (symmetry; apply w_is0_pos; rewrite u64_lit; lia).
change (iovcnt32 (Z_to_bv 64 1)) with (Z_to_bv 64 1).
rewrite in_mem_si, Himp, Hacc.
unfold cap_iovecs. cbn [cap_iovecs_aux iovs_total].
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.min_r by (unfold MAX_RW_COUNT; lia).
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. cbv beta iota zeta.
change ((0 + 0 =? 0)%Z) with true. cbv beta iota. reflexivity.
Qed.
End WithSegs.
End FPX_1.
