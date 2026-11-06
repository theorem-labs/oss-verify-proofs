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
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import LibWritev.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__LibWritevX () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Init.Specif."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.LibWritev."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1O"; "1Some"; "1app"; "1bool"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "1true"; "2I"; "2and"; "2eq"; "3le"]; ["4proj1_sig"; "5firstn"; "5map"; "5skipn"; "6Z"; "0K"; "7word_to_nat"; "8fetch_word"; "8is_ecall"; "8machine_state"; "8ms_gpr"; "8ms_mem"; "8ms_rom"; "8ms_svc_pending"; "8set_gpr0"; "8word_to_le_bytes"]; ["9advance_past_svc"; "9mkCfg"; ":FdChannel"; ":FdEntry"; ":Model"; ":TASK_SIZE"; ":WriteEv"; ":event"; ":fd_lookup"; ":iovs_total"; ":m_fds"; ":m_halted"; ":m_vm_lazy"; ";bvmap"; "<iov_array"; "<iov_bufs"]; ["<iov_bufs_ok"; "=getr"; "=mkst"; "=rdn"; "=regupd"; "=seg_rom"; "=v_addi"; ">TSet"; ">t_alt"; ">t_emit"; ">t_write_ch"; ">wr_index"; "?srealizes"; "@concat"; "Aadd"; "Ale"]; ["Alt"; "Amul"; "Aof_nat"; "Apow"; "0T"; "0b1"; "0b2"; "0bs"; "0bs1"; "0bs2"; "0bss"; "0fd"; "0fx"; "0i"; "0iov"; "0iovs"]; ["0k"; "0mem"; "0model"; "0ms"; "0n"; "0n1"; "0n2"; "0pc"; "0regs"; "0scfg"; "0segs"; "BBV"; "BZ_to_bv"; "Bbv"; "Bbv_unsigned"; "0w"]; ["0x8"]]).
Section FPX_1. Context {fx : FPState}.
Section WithSegs.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Lemma writev_checkX : forall ms x8 model (fd : Z) (iov : word) iovs bss,
ms_rom ms = seg_rom segs ->
fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
(0 < fd < 2^31)%Z ->
bv_unsigned x8 = 66%Z ->
ms_gpr ms 0 = Z_to_bv 64 fd ->
ms_gpr ms 1 = iov ->
ms_gpr ms 2 = Z_to_bv 64 (Z.of_nat (length iovs)) ->
(1 <= length iovs <= 1024)%nat ->
(bv_unsigned iov + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
iov_array segs (ms_mem ms) iov iovs ->
iov_bufs_ok iovs ->
iov_bufs segs (ms_mem ms) iovs bss ->
let bs := concat bss in
let tot := iovs_total iovs in
(1 <= tot)%Z -> (tot <= 2 ^ 30)%Z ->
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
intros ms x8 model fd iov iovs bss Hrom Hfd Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs bs tot Ht1 Ht30 CA.
pose proof (gather_of_bufs segs ms iovs bss Hrom Hbufs) as Hg. fold bs in Hg.
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
rewrite (import_iovecs_of_array segs ms iovs iov Hrom Hcnt Hiok Harr Hbok).
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
Lemma rz_writev_pendingX : ltac2:(TCodec.tc2 tcn__LibWritevX "VF'I'RMyR0%211'Q4'D'6':%1255%311y8%:11%611%711'7&QGp021'>'9%118p0A1&Lr8%211&QEvRJ%211%:3741%:1I&Q;r7%211(0%11N%A3631&Q<%11>(8%11N%F3N31&Mr;%211(2r:%22Q:1%M3B41'Q3%N11&Q8&Q:%117&RLr9%22QD1%6241(Q2%113%?2;1%Q:3;41'=&R0z%221C&R3+2+O%3221%72H1%9261&RNr=%22R61+R2%QI3R521&Jr?(1%3221r<%L2R>1%R03R>31r@u1%9221%R43RB16rAu2%=221&R2&5%12RC<%311%Q92RK1%R=3RK61'?%62RHI%22>1uQP0%4231%Q8231&QO&QN%Q12S5K&R1+@r>%A2S31%C11%5241%8271&Q5%;221&Q>&KrD%211%44RL1Q3Q9&Q@%11Q5&Q?rF%811%34S21Q5Q9&QM%12SBQ7+1&Q9rC%211%M241%41@+N%R52R41%Q1231r1%Q92QE1r2r5%QA2T01%Q=231'QLvRI(Q1&Q0&NrMr3%QK11%S12TC1%5241%711rK%:221%Q117%>4T2=21p0@1p0E1pU2T@1rI%A281&QH&QKr4%211&QI&B'Q7(Q6%SE2U7:%211&A&@r6%RD2U31%R@2Q81%SD2Q81qU:U31%63U41Q;%83U81Q9%>4U9=:1rE%114%B231qTLD1%H2E1%Q=4U1Q<J1p0M1p0QF1p0QK1tT@UBR11p0R41p0R91p0R<1p0RB1p0RO1p0S61p0S@1p0SE1p0SM1p0T31p0T>1p0TL1p0U41p0U:1p0UB1pT:UN1pTFV21pU0V71pTNV>1pTHV=1pU6V?1pV2VA1pU8VE1").
Proof.
intros ms x8 model fd iov iovs bss T Hrom Hh Hlazy Hsvc Hfd Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs bs
Ht1 Ht30 Hk.
destruct (writev_checkX ms x8 model fd iov iovs bss Hrom Hfd Hfdr Hno H0 H1 H2 Hcnt Hiok Harr Hbok Hbufs
Ht1 Ht30)
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
Lemma rz_writev2X : ltac2:(TCodec.tc2 tcn__LibWritevX "X=&Q=y5'RMyR0%211%5241'9y8%611%311p061'Q4yQ0%;11'D'6%118'7&QGp021'>%?18&GvRJr=%3221(2r:%22?1%93841'4&Hr;%211(;%?3521%N1Q0&Q;%11>(0%11Q4%E3531':%12Q7Q7%M11&Q<r>%211(8%116%N3631'Q3%Q>11&Q8&Q:r?%211&RL%12QGQ2%6231(Q2%113%Q42;1%Q;3;41'=&R0z%221E&R3+2+O%3221%72J1%9261&QArD(RK+A(<%33R>21%6251+R2%I2R?1%QO3R?31rE+:%:3RE18%=231r@%Q02RF1%R63RF31rF+;%A3RL1?%D231%R;3RK17rG+<%F3S11D%I231%Q;2S1O%RA3S121%S01RF&QCrBu8%34RC?21&OrA%2241%RD2RN1%RK3951&QN&RNrC%22S@1+8%5221%QM2SC1%@4S0G1>%S43B1:rH%92SGQ?+@%<221%R42SJ1%G4S751E%S;3I1ArI%@2SNQ=+H%C221%R;2T11%N4S>51L%SB3Q01HrJ&F%11QN%Q34SC3QF1%SA2SKO%SH3Q621rK%61L%Q84SH2R41%SL3Q:15&QO%Q12T?I+Q0%Q4221&Q5%5221%Q62TDQG%Q8261%8214%Q92TGQO%Q;241%;217+1%Q=2TKN%Q?218%?231%Q@2TNJ%QB21@+N%S02RO1%D231'?u1r1%3221r2&5&3%13U5Q6Q=%32U61%9251'QLvRI(Q1&QBvR<&QDrQ6&R2r3%211%T12UG1%635S51&QFrQ5+4%3221rQ4&QE%11U;%@5?8431rQ3%C221%R61>%G4U@F21p0I1p0Q01pU2UI1rQ2%I5H<81:rQ1%L221&QH&QK%Q53V9RARH%211&QI&B'Q7(Q6rQ0%TO2VE1%311&A&@%Q@3VDR?RE%QB2VE1%QH2QF1%TO2QF1qU:V?1%63V@1QI%83VJ1QE%?4VK>:1%S;13%B221qTLD1%H2E1%QH4VAQGJ1p0O1p0R51p0R;1p0R@1p0RD1p0RH1p0RO1p0S41p0S;1p0SC1p0SK1p0T51p0T@1p0TG1p0TM1p0U51p0U@1p0UK1p0V91p0VC1p0VJ1p0W11pT:W<1pTDW@1pTBWA1pU>WN1pT>WO1pU<X01pT<X11pTNX21pTHWI1pV0WK1pU6WN1pU4X01pU@X71pUBX71").
Proof.
intros regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 T HF HE Hh Hlazy Hfd Hfdr H17 H10 H11 H12
Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiok Hb1 Hb2 Ht1 Ht30 Hk.
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
pose proof (u64_range n1). pose proof (u64_range n2).
replace (bs1 ++ bs2) with (concat [bs1; bs2]) in * by (cbn; rewrite app_nil_r; reflexivity).
eapply (rz_writev_pendingX (epend regs pc mem (seg_rom segs) (getr regs 17)) (getr regs 17) model fd iov
[(b1, n1); (b2, n2)] [bs1; bs2] T);
[reflexivity | exact Hh | exact Hlazy | reflexivity | exact Hfd | exact Hfdr
| rewrite H17; apply u64_lit; lia
| rewrite ms_gpr_epend0; exact H10 | rewrite ms_gpr_epend1; exact H11 | rewrite ms_gpr_epend2; exact H12
| cbn; lia | change (Z.of_nat (length [(b1, n1); (b2, n2)])) with 2%Z; lia
| | cbn [iov_bufs_ok]; repeat split; assumption | | cbn [iovs_total]; lia
| cbn [iovs_total]; lia | ].
- cbn [iov_array ms_mem epend].
replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (Z_to_bv 64 (bv_unsigned iov + 24)).
2:{ change (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned iov + 16)) + 8)) with (at_ (at_ iov 16) 8).
rewrite at_at. reflexivity. }
repeat split; try assumption; lia.
- cbn [iov_bufs ms_mem epend]. repeat split; assumption.
- intros k Hk1 Hk2. rewrite adv_set_epend. apply Hk; assumption.
Qed.
Lemma rz_writev1X : ltac2:(TCodec.tc2 tcn__LibWritevX "W;&Q=y5'RMyR0%211%5241'9y8%611%311p061'Q4yQ0%;11'D'6%118'7&QGp021'>%?18&GvRJr:%3221(2r7%22?1%93841'4&Hr8%211(;%?3521%N1Q0&Q;%11>(0%11Q4%E3531':%12Q7Q7%M11&Q<r;%211(8%116%N3631'Q3%Q>11&Q8&Q:r<%211&RL%12QGQ2%6231(Q2%113%Q42;1%Q;3;41'=&R0z%221E&R3+2+O%3221%72J1%9261&QArA(RK+A(<%33R>21%6251+R2%I2R?1%QO3R?31rB+:%:3RE18%=231r=%Q02RF1%R63RF31rC+;%A3RL1?%D231%R;3RK17rD+<%F3S11D%I231+1%Q<2S21%RB3S231%S11RG&QCr?u8%34RD@21&Or>%2241%RE2RO1%RL3951&QN&RNr@%22SA1+8%5221%QN2SD1%@4S1H1>%S53B1:rE&F%11C%E4S63:1%S42S>A%S;3H21&QO%?2SNQ=+@%B221&Q5%5221%D2T3QK%F261%8214%92Q58%H2T7Q?+N%R82R71%=231'?u1r1%3221r2&5%12T<J%7231'QLvRI(Q1&QBvR<&QDrO&R2r3%211%S72TM1%635R;1&QFrN+4%3221rM&QE%11TA%@5?8431rL%C221%QB1>%G4TFF21p0I1p0N1pU2TO1rK%I5H<81:rJ%L221&QH&QK%11RG&QI&B'Q7(Q6rI%T42UJ1%311&A&@rF%Q?2UJ1%QE2QC1%T42QC1qU:UD1%63UE1QF%83UO1R=%?4V0>:1%S913%B221qTLD1%G2E1%QG4UFQFI1p0N1p0R21p0R71p0R91p0R=1p0RD1p0RK1p0S51p0S@1p0SH1p0SN1p0T61p0TA1p0TL1p0U:1p0UD1p0UK1p0V21pT:V=1pTBVA1pU<VN1pT<VO1pTNW01pTHVG1pV0VI1pU6VL1pU4VN1pU@W51pUBW51").
Proof.
intros regs pc mem model w fd iov b1 n1 bs1 T HF HE Hh Hlazy Hfd Hfdr H17 H10 H11 H12
Rb1 Rn1 Rs1 Hiok Hb1 Ht1 Ht30 Hk.
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
pose proof (u64_range n1).
replace bs1 with (concat [bs1]) in Hk by (cbn; rewrite app_nil_r; reflexivity).
replace bs1 with (concat [bs1]) by (cbn; rewrite app_nil_r; reflexivity).
eapply (rz_writev_pendingX (epend regs pc mem (seg_rom segs) (getr regs 17)) (getr regs 17) model fd iov
[(b1, n1)] [bs1] T);
[reflexivity | exact Hh | exact Hlazy | reflexivity | exact Hfd | exact Hfdr
| rewrite H17; apply u64_lit; lia
| rewrite ms_gpr_epend0; exact H10 | rewrite ms_gpr_epend1; exact H11 | rewrite ms_gpr_epend2; exact H12
| cbn; lia | change (Z.of_nat (length [(b1, n1)])) with 1%Z; lia
| | cbn [iov_bufs_ok]; split; [assumption | exact I] | | cbn [iovs_total]; lia
| cbn [iovs_total]; lia | ].
- cbn [iov_array ms_mem epend]. repeat split; try assumption; lia.
- cbn [iov_bufs ms_mem epend]. split; [assumption | exact I].
- intros k Hk1 Hk2. rewrite adv_set_epend. apply Hk; assumption.
Qed.
Lemma rz_writev2_wallX : ltac2:(TCodec.tc2 tcn__LibWritevX "X7&Q=y5'RMyR0%211%5241'9y8%611%311p061'Q4yQ0%;11'D'6%118&QG'>%=16&GvRJr=%3221(2r:%22=1%93841'4&Hr;%211(;%?3521%L1N&Q;%11>(0%11Q2%E3531':%12Q5Q5%K11&Q<r>%211(8%116%N3631'Q3%Q<11&Q8&Q:r?%211&RL%12QEQ2%6231(Q2%113%Q42;1%Q;3;41'=&R0z%221E&R3+2+O%3221%72J1%9261&QArD(RK+A(<%33R<21%6251+R2%I2R=1%QO3R=31rE+:%:3RC18%=231r@%Q02RD1%R63RD31rF+;%A3RJ1?%D231%R;3RI17rG+<%F3RO1D%I231%Q;2ROO%RA3RO21%RN1RD&QCrBu8%34RC?21&OrA%2241%RD2RL1%RK3951&QN&RNrC%22S>1+8%5221%QM2SA1%@4S0G1>%S43B1:rH%92SEQ?+@%<221%R42SH1%G4S751E%S;3I1ArI%@2SLQ=+H%C221%R;2SO1%N4S>51L%SB3Q01HrJ&F%11QN%Q34SC3QF1%SA2SIO%SH3Q621rK%61L%Q84SH2R41%SL3Q:15&QO%Q12T=I+Q0%Q4221&Q5%5221%Q62TBQG%Q8261%8214%Q92TEQO%Q;241%;217+1%Q=2TIN%Q?218%?231%Q@2TLJ%QB21@+N%S02RO1%D231'Q7%SG11%R=11'7'?u1r1%3221r2&5&3%13U7Q4Q:%32U81%9251'QLvRI(Q1&QBvR<&QDrQ7&R2r3%211%T52UI1%635S91&QFrQ6+4%3221rQ5&QE%11U?%@5?8431rQ4%C221&QI&B(Q6rQ2%TE2V91%311&CrL%Q23V81R5%33V9G1%94V:Q>51%;21R>%Q24UOQ1=1p0Q41p0Q;1pU2Q@1rQ3%Q45Q3GC1E%Q621?rQ0%U52VI1%C11%Q@3VFRIS0%F4VGQK21%H21S9%Q?4V<Q>71p0;1p0QM1p0R11p0R71p0R<1p0R@1p0RD1p0RK1p0S01p0S71p0S?1p0SG1p0T11p0T<1p0TC1p0TI1p0U11p0U<1p0UG1p0V51p0V?1p0VF1p0VM1pQ<W81pTDW:1pTBW;1pU>WH1pT>WI1pU<WJ1pT<WK1pTNWL1pTHWC1pV0WE1pU6WH1pU4WJ1pU@X11pUBX11").
Proof.
intros regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 K HF HE Hh Hlazy Hfd Hfdr H17 H10 H11 H12
Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiok Hb1 Hb2 Ht1 Ht30 HK Hk.
pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (rdn_length segs mem _ _ _ Rs2) as L2.
pose proof (u64_range n1). pose proof (u64_range n2).
apply rz_wall; [rewrite length_app; unfold word_to_nat in L1, L2; lia | exact HK |].
eapply (rz_writev2X regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2
(fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs1 ++ bs2))) K)); eassumption.
Qed.
Lemma rz_writev1_wallX : ltac2:(TCodec.tc2 tcn__LibWritevX "W5&Q=y5'RMyR0%211%5241'9y8%611%311p061'Q4yQ0%;11'D'6%118&QG'>%=16&GvRJr:%3221(2r7%22=1%93841'4&Hr8%211(;%?3521%L1N&Q;%11>(0%11Q2%E3531':%12Q5Q5%K11&Q<r;%211(8%116%N3631'Q3%Q<11&Q8&Q:r<%211&RL%12QEQ2%6231(Q2%113%Q42;1%Q;3;41'=&R0z%221E&R3+2+O%3221%72J1%9261&QArA(RK+A(<%33R<21%6251+R2%I2R=1%QO3R=31rB+:%:3RC18%=231r=%Q02RD1%R63RD31rC+;%A3RJ1?%D231%R;3RI17rD+<%F3RO1D%I231+1%Q<2S01%RB3S031%RO1RE&QCr?u8%34RD@21&Or>%2241%RE2RM1%RL3951&QN&RNr@%22S?1+8%5221%QN2SB1%@4S1H1>%S53B1:rE&F%11C%E4S63:1%S42S<A%S;3H21&QO%?2SLQ=+@%B221&Q5%5221%D2T1QK%F261%8214%92Q58%H2T5Q?+N%R82R71%=231'Q7%RO11%QL11'7'?u1r1%3221r2&5rF%22T?1%8241'QLvRI(Q1&QBvR<&QDrQ0&R2r3%211%S<2U01%635R@1&QFrO+4%3221rN&QE%11TF%@5?8431rM%C221&QI&B(Q6rK%SL2U@1%311&CrG%23U?F1%84U@Q<41%:21Q3%Q14U5Q0<1p0Q31p0Q91pU2Q>1rL%Q35Q2FB1D%Q521>rI%T;2UO1%B11%D4ULQH1R<%F21S7%Q=4UAQ<61p0:1p0QJ1p0QN1p0R31p0R51p0R91p0R@1p0RG1p0S11p0S<1p0SD1p0SJ1p0T21p0T=1p0TH1p0U61p0U@1p0UG1p0UN1pQ<V91pTBV;1pU<VH1pT<VI1pTNVJ1pTHVA1pV0VC1pU6VF1pU4VH1pU@VO1pUBVO1").
Proof.
intros regs pc mem model w fd iov b1 n1 bs1 K HF HE Hh Hlazy Hfd Hfdr H17 H10 H11 H12
Rb1 Rn1 Rs1 Hiok Hb1 Ht1 Ht30 HK Hk.
pose proof (rdn_length segs mem _ _ _ Rs1) as L1. pose proof (u64_range n1).
apply rz_wall; [unfold word_to_nat in L1; lia | exact HK |].
eapply (rz_writev1X regs pc mem model w fd iov b1 n1 bs1
(fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs1)) K)); eassumption.
Qed.
Lemma rz_writev2_chX : ltac2:(TCodec.tc2 tcn__LibWritevX "WG&Q=y5'RMyR0%211%5241'9y8%611%311p061'Q4yQ0%;11'D'6%118&QG'>%=16&GvRJr=%3221(2r:%22=1%93841'4&Hr;%211(;%?3521%L1N&Q;%11>(0%11Q2%E3531':%12Q5Q5%K11&Q<r>%211(8%116%N3631'Q3%Q<11&Q8&Q:r?%211&RL%12QEQ2%6231(Q2%113%Q42;1%Q;3;41'=&R0z%221E&R3+2+O%3221%72J1%9261&QArD(RK+A(<%33R<21%6251+R2%I2R=1%QO3R=31rE+:%:3RC18%=231r@%Q02RD1%R63RD31rF+;%A3RJ1?%D231%R;3RI17rG+<%F3RO1D%I231%Q;2ROO%RA3RO21%RN1RD&QCrBu8%34RC?21&OrA%2241%RD2RL1%RK3951&QN&RNrC%22S>1+8%5221%QM2SA1%@4S0G1>%S43B1:rH%92SEQ?+@%<221%R42SH1%G4S751E%S;3I1ArI%@2SLQ=+H%C221%R;2SO1%N4S>51L%SB3Q01HrJ&F%11QN%Q34SC3QF1%SA2SIO%SH3Q621rK%61L%Q84SH2R41%SL3Q:15&QO%Q12T=I+Q0%Q4221&Q5%5221%Q62TBQG%Q8261%8214%Q92TEQO%Q;241%;217+1%Q=2TIN%Q?218%?231%Q@2TLJ%QB21@+N%S02RO1%D231'7'?u1r1%3221r2&5&3%13U4Q7Q>%32U51%9251'QLvRI(Q1&QBvR<&QDrQ6&R2r3%211%T22UF1%635S61&QFrQ5+4%3221rQ4&QE%11U<%@5?8431rQ3%C221%F4U@E1R7p0H1p0O1pU2Q41rQ2%H5G;719rQ1%K221&QJrO%TH2V<1%Q53V8RBRI%4321SC%Q34UMQ261p0;1p0QA1p0QG1p0QL1p0R01p0R41p0R;1p0R@1p0RG1p0RO1p0S71p0SA1p0SL1p0T31p0T91p0TA1p0TL1p0U71p0UE1p0UO1p0V61p0V=1pQ<VH1pTDVJ1pTBVK1pU>W81pT>W91pU<W:1pT<W;1pTNW<1pTHW31pV0W51pU6W81pU4W:1pU@WA1pUBWA1").
Proof.
intros. unfold t_write_ch.
eapply (rz_writev2X regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 (fun _ => K)); eassumption.
Qed.
Lemma rz_writev1_zeroX : ltac2:(TCodec.tc2 tcn__LibWritevX "UA&Q=y5'RMyR0%211%5241'9y8%611%311p061'Q4yQ0%;11'D&QG'>%;14&GvRJr8%3221(2r5%22;1%93841'4&Hr6%211(;%?3521%J1L&Q;%11>(0%11Q0%E3531'6':%12Q4Q4%311&Q<r9%211(8%116%O3631'Q3%Q;11&Q8&Q:r:%211&RL%12QDQ3%6231(Q2%113%Q52;1%Q<3;41'=&R0z%221E&R3+2+O%3221%72J1%9261&QAr?(RK+A(<%33R;21%6251+R2%I2R<1%R03R<31r@+:%:3RB18%=231r;%Q02RC1%R73RC31rA+;%A3RI1?%D231%R<3RH17rB+<%F3RN1D%I231+1%Q<2RO1%RC3RO31%QN1RL%RO11&QCr=u8%34RFA21&Or<%2241%RG291%RN3951&QN&RNr>%22S?1+8%5221%QO2SB1%@4S3I1>%R12SDQH%>2@1%S32E1%S:3E41&QO%<2SIQD+@%?221&Q5%5221%6252'QLvRI(Q1&QBvR<&QDrG%231QFB&QFrF+4%3221rE&QE%11SM%<5;8431rD%?221%B4T1A1R<rH%A5@1>;6%C219%F4T5E1R7p051p0I1p0K1p0Q21p0Q?1p0QK1p0R31p0R91p0RA1p0RL1p0S71p0SE1p0T01p0T71p0T>1pQ<TI1pT<U51pTNU61pTHTM1pV0TO1pU6U21pU4U41pU@U;1pUBU;1").
Proof.
intros regs pc mem model w fd iov b1 K HF HE Hh Hlazy Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Hiok Hb1 Hc.
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
assert (Hno : bv_unsigned (getr regs 17) = 66%Z) by (rewrite H17; apply u64_lit; lia).
assert (Harr : iov_array segs (ms_mem ms) iov [(b1, Z_to_bv 64 0)]).
{ cbn [iov_array ms_mem ms epend]. refine (conj Rb1 (conj Rn1 (conj _ I))). rewrite u64_lit by lia. lia. }
assert (Himp : import_iovecs (ms_read_byte ms) iov (Z_to_bv 64 1) = ImpOk [(b1, Z_to_bv 64 0)]).
{ unfold import_iovecs. rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
rewrite (access_okb_of_le iov 16) by lia.
rewrite (read_iovec_entry_of_array segs ms b1 (Z_to_bv 64 0) [] iov eq_refl Harr).
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
