(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs Progress.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import PropExec MState Mem Exec ITree.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Export RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Lib_Nodes () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Nodes."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1O"; "1Some"; "1app"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "2I"; "2and"; "2eq"; "2iff"; "2not"]; ["3mul"; "4le"; "4lt"; "5Z"; "6word_to_nat"; "7Segment"; "8machine_state"; "8ms_mem"; "8ms_read_byte"; "8ms_rom"; "8ms_writable_byte"; "8wview"; "9sys_input"; ":CstrOk"; ":CstrTooLong"; ":Model"]; [":ProcInput"; ":cstr_result"; ":gather_iovecs"; ":in_arg"; ":in_mem"; ":in_sysno"; ":in_wmem"; ":init_model"; ":iovs_total"; ":m_vm_lazy"; ":read_bytes_aux"; ":read_bytes_map"; ":read_cstr_aux"; ":read_iovecs_aux"; ":read_u64"; ":readable_bytes"]; [":readable_bytes_aux"; ";bytes_at"; ";le8"; ";mrd"; ";wa"; ";wr_at"; "<areg"; "<bytes_in"; "<iov_ok"; "<iovec_bytes"; "<minv"; "=seg_rom"; ">Forall2"; ">In"; ">concat"; "?add"]; ["?le"; "?lt"; "?of_nat"; "?pow"; "0a"; "0b"; "0brk"; "0bs"; "0bs1"; "0bs2"; "0bufs"; "0fuel"; "0inp"; "0iovs"; "0k"; "0lim"]; ["0m"; "0mbase"; "0mo"; "0mp"; "0ms"; "0n"; "0reserved"; "0segs"; "0sp"; "@BV"; "@Z_to_bv"; "@bv"; "@bv_add"; "@bv_unsigned"; "0str"; "0v"]; ["0w"; "0x8"]]).
Lemma in_sysno_si : ltac2:(TCodec.tc2 tcn__CJ_Lib_Nodes "C'6'E%211'F'RKyR0%211'=&Q5&Lr3r2r1%43321%611%83913pV4:1pU:>1pU@@1").
Proof. reflexivity. Qed.
Definition areg (ms : machine_state) (r : bv 5) : word := reg_get (ms_regs ms) r.
Lemma in_a0_si : ltac2:(TCodec.tc2 tcn__CJ_Lib_Nodes "K'6'E%211'F'RKyR0%211'=&Q3&Lr3r2r1%43321(1%7221&QF(RIy5+:(;%43321%62;1%@3A81pV4B1pU:F1pU@H1").
Proof. reflexivity. Qed.
Lemma in_a1_si : ltac2:(TCodec.tc2 tcn__CJ_Lib_Nodes "K'6'E%211'F'RKyR0%211'=&Q3&Lr3r2r1%43321u1%7221&QF(RIy5+;(;%43321%62;1%@3A81pV4B1pU:F1pU@H1").
Proof. reflexivity. Qed.
Lemma in_a2_si : ltac2:(TCodec.tc2 tcn__CJ_Lib_Nodes "K'6'E%211'F'RKyR0%211'=&Q3&Lr3r2r1%43321u2%7221&QF(RIy5+<(;%43321%62;1%@3A81pV4B1pU:F1pU@H1").
Proof. reflexivity. Qed.
Lemma in_a3_si : ltac2:(TCodec.tc2 tcn__CJ_Lib_Nodes "K'6'E%211'F'RKyR0%211'=&Q3&Lr3r2r1%43321u3%7221&QF(RIy5+=(;%43321%62;1%@3A81pV4B1pU:F1pU@H1").
Proof. reflexivity. Qed.
Lemma in_a4_si : ltac2:(TCodec.tc2 tcn__CJ_Lib_Nodes "K'6'E%211'F'RKyR0%211'=&Q3&Lr3r2r1%43321u4%7221&QF(RIy5+>(;%43321%62;1%@3A81pV4B1pU:F1pU@H1").
Proof. reflexivity. Qed.
Lemma in_a5_si : ltac2:(TCodec.tc2 tcn__CJ_Lib_Nodes "K'6'E%211'F'RKyR0%211'=&Q3&Lr3r2r1%43321u5%7221&QF(RIy5+?(;%43321%62;1%@3A81pV4B1pU:F1pU@H1").
Proof. reflexivity. Qed.
Lemma in_mem_si : ltac2:(TCodec.tc2 tcn__CJ_Lib_Nodes "J'6'E%211'F'RKyR0%211'='9y8%611%311p061&Q4&Lr3r2r1%43321%611&H%115%?3:31pV4A1pU:E1pU@G1").
Proof. reflexivity. Qed.
Lemma in_wmem_si : ltac2:(TCodec.tc2 tcn__CJ_Lib_Nodes "J'6'E%211'F'RKyR0%211'='9y8%611%311p061&Q6&Lr3r2r1%43321%611&J%1265%?3:31pV4A1pU:E1pU@G1").
Proof. reflexivity. Qed.
Definition bytes_in (mp : word -> option byte) (a : Z) (bs : list byte) : Prop :=
0 <= a /\ a + Z.of_nat (length bs) <= 2^64 /\
forall i, (i < length bs)%nat -> mp (wa (a + Z.of_nat i)) = nth_error bs i.
Lemma ms_read_byte_mrd : ltac2:(TCodec.tc2 tcn__CJ_Lib_Nodes "Q0'6'E%211'F'RKyR0%211'='9y8%611%311p061&Ir2%211&QKr3%211%<3741&H%1247&QCr4&G%118%4331<%D3@61p091pT:G1pU:K1pU@M1").
Proof. intros segs ms a H. unfold ms_read_byte, mrd. rewrite H. reflexivity. Qed.
Lemma bytes_at_in : ltac2:(TCodec.tc2 tcn__CJ_Lib_Nodes "Q6'6'E%211'F'C'RKy8%211%811'=yR0%611'9%116p031&Ir3%211&QKr4%211%<3741&QAr5&G%116r2%5442;1&QG&H%117%331<?p051p0<1pT@J1pT:O1pU:Q11pU@Q31").
Proof.
intros segs ms a bs Hrom (Ha & Hl & H). split; [lia|]. split; [lia|].
intros i Hi. rewrite (ms_read_byte_mrd segs) by exact Hrom. apply H. exact Hi.
Qed.
Section SE.
Local Abbreviation SEC_T_bytes_in_app := (ltac2:(TCodec.tc2 tcn__CJ_Lib_Nodes "Q3'RKyR0%211'9y8%511%311p051'C'6%115&>&QGr4r3&3r2r1%33=21%73651'<%93875&QO&R2&5%12D9%311%52=1%@3?1;%9281%C2;1pTDE1pTBF1pT:I1pU8K1")) (only parsing).
Variable mp : ltac:(sec_ty2 constr:(SEC_T_bytes_in_app) 0%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_bytes_in_app) 1%nat 0%nat).
Variable bs1 : ltac:(sec_ty2 constr:(SEC_T_bytes_in_app) 2%nat 0%nat).
Variable bs2 : ltac:(sec_ty2 constr:(SEC_T_bytes_in_app) 3%nat 0%nat).
Lemma bytes_in_app : ltac:(sec_stmt2 constr:(SEC_T_bytes_in_app) 4%nat 0%nat).
Proof.
unfold bytes_in. rewrite length_app. split.
- intros (Ha & Hl & H). repeat split; try lia.
+ intros i Hi. rewrite (H i) by lia. rewrite nth_error_app1 by lia. reflexivity.
+ intros i Hi. replace (a + Z.of_nat (length bs1) + Z.of_nat i) with (a + Z.of_nat (length bs1 + i)) by lia.
rewrite (H (length bs1 + i)%nat) by lia. rewrite nth_error_app2 by lia. f_equal. lia.
- intros ((Ha & Hl1 & H1) & (Ha2 & Hl2 & H2)). repeat split; try lia.
intros i Hi. destruct (Nat.ltb_spec0 i (length bs1)).
+ rewrite nth_error_app1 by lia. apply H1. lia.
+ rewrite nth_error_app2 by lia. rewrite <- (H2 (i - length bs1)%nat) by lia. f_equal. f_equal. lia.
Qed.
End SE.
Lemma bytes_in_cons : ltac2:(TCodec.tc2 tcn__CJ_Lib_Nodes "Q6'RKyR0%211'9y8%511%311p051'C'6%115&QGr4r3(4r2r1%33<21%73651'<'=r5&QD%11;%311(2%12E=%73E31&QO+1%22B1%D3:1@%=251p0?1pT@H1pT<N1pT:L1pU8N1").
Proof.
intros mp a b bs H. change (b :: bs) with ([b] ++ bs) in H. apply bytes_in_app in H as [H1 H2].
split; [|exact H2]. destruct H1 as (_ & _ & H1). specialize (H1 0%nat ltac:(cbn; lia)).
rewrite Z.add_0_r in H1. exact H1.
Qed.
Lemma read_bytes_aux_bytes_in : ltac2:(TCodec.tc2 tcn__CJ_Lib_Nodes "Q0'6'RKy8%211%411yR0%511'9%115p031'C&QGr2r1r3%43321'=%:1=&Q:&QD%118&5r4%22D1%63:41(2%12F4%;3:31p0=1pT:C1pU8E1pT@K1").
Proof.
induction bs as [|b bs IH]; intros mp a H; [reflexivity|].
apply bytes_in_cons in H as [Hb H]. cbn [read_bytes_aux length]. rewrite Hb.
rewrite wa_succ, (IH _ _ H). reflexivity.
Qed.
Lemma readable_bytes_aux_bytes_in : ltac2:(TCodec.tc2 tcn__CJ_Lib_Nodes "M'6'RKy8%211%411yR0%511'9%115p031'C&QGr2r1r3%43321'=&Q@&QD%117&5r4%22C1%63941%83D13p0:1pT:@1pU8B1pT@H1").
Proof.
intros. apply readable_bytes_aux_full, read_bytes_aux_bytes_in. assumption.
Qed.
Lemma word_to_nat_of_nat : ltac2:(TCodec.tc2 tcn__CJ_Lib_Nodes "E'7&R1&R2r1%211&R3+2+R0%3221%8251'=&D&RJyR0r2%=11%4231%611%83B14p0:1pU<D1").
Proof. intros. unfold word_to_nat. rewrite unsigned_lit by lia. lia. Qed.
Lemma read_bytes_map_bytes_in : ltac2:(TCodec.tc2 tcn__CJ_Lib_Nodes "Q>'6'RKy8%211%411yR0%511'9%115p031'C&QGr2r1r3%43321&R1&R2&5r4%22A1%411&R3+2+R0%3221%:251'=%E1H&Q;&QD%11A&RJr5%@2O1%B11%42O1%83B61(2%12Q36%=3<31p0?1p0K1pT:Q11pU8Q31pT@Q91").
Proof.
intros bs mp a H Hl. rewrite read_bytes_map_eq. rewrite word_to_nat_of_nat by exact Hl.
apply read_bytes_aux_bytes_in, H.
Qed.
Lemma readable_bytes_bytes_in : ltac2:(TCodec.tc2 tcn__CJ_Lib_Nodes "Q;'6'RKy8%211%411yR0%511'9%115p031'C&QGr2r1r3%43321&R1&R2&5r4%22A1%411&R3+2+R0%3221%:251'=&Q?&QD%11@&RJr5%?2N1%A11%42N1%83A61%:3Q115p0<1p0H1pT:N1pU8Q01pT@Q61").
Proof.
intros. apply readable_bytes_full, read_bytes_map_bytes_in; assumption.
Qed.
Lemma read_cstr_aux_bytes_in : ltac2:(TCodec.tc2 tcn__CJ_Lib_Nodes "QD'6'RKy8%211%411'7yR0%611'9%116p031'C&B&5r4%22<1r3%5221&?&QM&RJz%22D1r5%53E21%711&QG&3r6(4(8%11L%33M:1%63N51%83DB1'='Q1&Q<&QD%11I%33A1<(Mr7%211%93841p0;1p0E1p0N1pT:Q51pU8Q71pTHQ=1pUNQ?1").
Proof.
induction str as [|b str IH]; intros fuel mp a Hf Hnz H.
- destruct fuel as [|fuel]; [cbn in Hf; lia|]. cbn [app] in H. apply bytes_in_cons in H as [Hb _].
cbn [read_cstr_aux]. rewrite Hb. reflexivity.
- destruct fuel as [|fuel]; [cbn in Hf; lia|]. cbn [app] in H. apply bytes_in_cons in H as [Hb H].
cbn [read_cstr_aux]. rewrite Hb.
assert (Hne : bv_eqb b (Z_to_bv 8 0) = false).
{ destruct (bv_eqb b (Z_to_bv 8 0)) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. exfalso. apply Hnz. left. congruence. }
rewrite Hne, wa_succ. rewrite (IH fuel mp (a + 1)); [reflexivity| cbn in Hf; lia | |exact H].
intro Hin. apply Hnz. right. exact Hin.
Qed.
Lemma read_cstr_aux_toolong_bytes_in : ltac2:(TCodec.tc2 tcn__CJ_Lib_Nodes "Q<'7'6'RKy8%211%411yR0%511'9%115p031'C'Ar4&5r3%22<1%5241&?&QM&RJz%22C1%43C1:%611&QGr5%23><1'='Q1&Q<&QD%11Cr7%43821(N%83721p0:1p0>1p0F1pT:M1pU8O1pUNQ51pTHQ;1").
Proof.
induction fuel as [|fuel IH]; intros str mp a Hf Hnz H; [reflexivity|].
destruct str as [|b str]; [cbn in Hf; lia|]. apply bytes_in_cons in H as [Hb H].
cbn [read_cstr_aux]. rewrite Hb.
assert (Hne : bv_eqb b (Z_to_bv 8 0) = false).
{ destruct (bv_eqb b (Z_to_bv 8 0)) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. exfalso. apply Hnz. left. congruence. }
rewrite Hne, wa_succ. rewrite (IH str mp (a + 1)); [reflexivity| cbn in Hf; lia | |exact H].
intro Hin. apply Hnz. right. exact Hin.
Qed.
Definition iovec_bytes (iovs : list (word * word)) : list byte :=
flat_map (fun p => le8 (fst p) ++ le8 (snd p)) iovs.
Lemma length_iovec_bytes : ltac2:(TCodec.tc2 tcn__CJ_Lib_Nodes "F'6':'RKyR0%211%4211%611'='7&5y8%911&QIr1%211%6241&@u@%92=5%3221%=3<51pTL?1").
Proof.
induction iovs as [|[b l] iovs IH]; [reflexivity|]. cbn [iovec_bytes flat_map fst snd].
rewrite !length_app, !length_le8. unfold iovec_bytes in IH. rewrite IH. cbn [length]. lia.
Qed.
Lemma read_u64_bytes_in : ltac2:(TCodec.tc2 tcn__CJ_Lib_Nodes "N'RKyR0%211'9y8%511%311p051'C&QGr3r2&QBr1%211%63541'=%>1?&Q>r4&QD%11;%4231(2%12F=%93831p0;1pV0I1pT:D1pU8F1").
Proof.
intros mp a v H. unfold read_u64.
pose proof (read_bytes_map_bytes_in _ _ _ H ltac:(rewrite length_le8; cbn; lia)) as R. rewrite length_le8 in R.
change (Z.of_nat 8) with 8 in R. rewrite R. rewrite le_bytes_to_word_le8. reflexivity.
Qed.
Lemma wa_add : ltac2:(TCodec.tc2 tcn__CJ_Lib_Nodes "C'C'RKyR0%211'=&RL&QDr2%211r1%53821&QO&RM%12;4%3271%911%<3=61pTN>1pT:B1").
Proof. intros. rewrite <- (Z_to_bv_bv_unsigned k) at 1. unfold wa. apply lit_add_lit. Qed.
Lemma read_iovecs_aux_bytes_in : ltac2:(TCodec.tc2 tcn__CJ_Lib_Nodes "Q4'6':'RKyR0%211%4211%611'9y8%711%311p071'C&QGr2r1&QIr3%211%63541'=%>1?&Q=&QD%11:&5r4%22F1%63;41(2%12H4%;3:31p0=1pT:E1pU8G1pTLM1").
Proof.
induction iovs as [|[b l] iovs IH]; intros mp a H; [reflexivity|].
cbn [iovec_bytes flat_map fst snd] in H. rewrite <- app_assoc in H.
apply bytes_in_app in H as [H1 H]. apply bytes_in_app in H as [H2 H3].
rewrite !length_le8 in H2. rewrite !length_le8 in H3.
cbn [read_iovecs_aux length]. rewrite (read_u64_bytes_in _ _ _ H1).
rewrite !wa_add. change (bv_unsigned (8%bv : word)) with 8. change (bv_unsigned (16%bv : word)) with 16.
replace (a + Z.of_nat 8) with (a + 8) in H2 by lia. rewrite (read_u64_bytes_in _ _ _ H2).
replace (a + Z.of_nat 8 + Z.of_nat 8) with (a + 16) in H3 by lia.
unfold iovec_bytes in IH. rewrite (IH _ _ H3). reflexivity.
Qed.
Definition iov_ok (mp : word -> option byte) (iov : word * word) (bs : list byte) : Prop :=
snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\ Z.of_nat (length bs) < 2^64 /\ bytes_in mp (bv_unsigned (fst iov)) bs.
Lemma wa_unsigned_id : ltac2:(TCodec.tc2 tcn__CJ_Lib_Nodes ";'RKyR0%211'=&QD&RMr1%2261%411%63713pV281").
Proof. intros. unfold wa. apply Z_to_bv_bv_unsigned. Qed.
Lemma gather_iovecs_ok : ltac2:(TCodec.tc2 tcn__CJ_Lib_Nodes "Q3'RKyR0%211'9y8%511%311p051'6':%1288%311%417%511'QL&QHr3%211r2r1%65:8321'=%C1:&Q2r4%2219(2&QN%12G:%32A1%93851p0;1pTFC1pTLF1pU8K1").
Proof.
intros mp iovs bufs H. induction H as [|[b l] bs iovs bufs (Hl & Hlen & Hb) _ IH]; [reflexivity|].
cbn [gather_iovecs fst snd] in *. subst l.
rewrite <- (wa_unsigned_id b). rewrite (read_bytes_map_bytes_in _ _ _ Hb Hlen). rewrite IH. reflexivity.
Qed.
Lemma iovs_total_ok : ltac2:(TCodec.tc2 tcn__CJ_Lib_Nodes "Q4'RKyR0%211'9y8%511%311p051'6':%1288%311%417%511'QL&QHr3%211r2r1%65:8321'='C&Q8%118&R2&5&QN%12G:%32H1%511%:3971p0<1pTFD1pTLG1pU8L1").
Proof.
intros mp iovs bufs H. induction H as [|[b l] bs iovs bufs (Hl & Hlen & Hb) _ IH]; [reflexivity|].
cbn [iovs_total fst snd concat] in *. subst l. rewrite length_app, IH.
rewrite unsigned_lit by lia. lia.
Qed.
Lemma read_bytes_aux_wr_at : ltac2:(TCodec.tc2 tcn__CJ_Lib_Nodes "Q>'6'E%211'RKyR0%211'9y8%511%311p051'C'7&QEr5r4r3r2%544321&R0&R2%114%3216&?'=%I1A%D11&Q:&Kr7r6%3221&QD%11C%7331B(0%11;%=3;31%?11p0A1p0F1pTNM1pU<O1pT:Q01pU2Q21pU@Q;1").
Proof.
intros segs m a n k W Hk. destruct W as (Ha & Hn & H). revert a n Ha Hn H Hk.
induction k as [|k IH]; intros a n Ha Hn H Hk; cbn [read_bytes_aux]; [discriminate|].
destruct (wview segs m (wa a)) eqn:E.
2:{ exfalso. apply (H 0); [lia|]. rewrite Z.add_0_r. exact E. }
rewrite wa_succ.
assert (IH' : read_bytes_aux (wview segs m) (wa (a + 1)) k <> None).
{ apply (IH (a + 1) (n - 1)); try lia. intros i Hi. replace (a + 1 + i) with (a + (1 + i)) by lia. apply H. lia. }
destruct (read_bytes_aux (wview segs m) (wa (a + 1)) k); [discriminate|]. exfalso; apply IH'; reflexivity.
Qed.
Inductive node : Type :=
| NWrite (fd : Z) (bs : list byte)
| NWritev (fd : Z) (bufs : list (list byte))
| NOpen (path : list byte)
| NRead (fd : Z) (buf : Z) (count : Z)
| NClose (fd : Z)
| NIoctl (fd : Z) (req : Z)
| NSetTid
| NExit (code : Z)
| NBrk (req : Z)
| NMmap (addr len prot flags : Z)
| NMunmap (addr len : Z)
| NMprotect (addr len prot : Z).
Definition pure_input (no : Z) (args : list word) : SyscallInput :=
mkInput (Z_to_bv 64 no) args (fun _ => None) (fun _ => None).
Definition node_input (n : node) : option SyscallInput :=
match n with
| NBrk req => Some (pure_input 214 [Z_to_bv 64 req])
| NMmap addr len prot flags =>
Some (pure_input 222 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 flags; Z_to_bv 64 (-1); Z_to_bv 64 0])
| NMunmap addr len => Some (pure_input 215 [Z_to_bv 64 addr; Z_to_bv 64 len])
| NMprotect addr len prot => Some (pure_input 226 [Z_to_bv 64 addr; Z_to_bv 64 len; Z_to_bv 64 prot])
| _ => None
end.
Section AtNode.
Variable segs : list Segment.
Definition at_node (n : node) (ms : machine_state) : Prop :=
match n with
| NWrite fd bs =>
ms_svc_pending ms = Some (Z_to_bv 64 64) /\
(fd = 1 \/ fd = 2) /\
areg ms 10 = Z_to_bv 64 fd /\
areg ms 12 = Z_to_bv 64 (Z.of_nat (length bs)) /\
Z.of_nat (length bs) < 2^64 /\
ms_rom ms = seg_rom segs /\
bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) bs
| NWritev fd bufs =>
ms_svc_pending ms = Some (Z_to_bv 64 66) /\
(fd = 1 \/ fd = 2) /\
areg ms 10 = Z_to_bv 64 fd /\
areg ms 12 = Z_to_bv 64 (Z.of_nat (length bufs)) /\
(length bufs <= 1024)%nat /\
Z.of_nat (length (concat bufs)) < 2^63 /\
ms_rom ms = seg_rom segs /\
exists iovs : list (word * word),
bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (iovec_bytes iovs) /\
Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
bytes_at segs (ms_mem ms) (bv_unsigned (fst iov)) bs) iovs bufs
| NOpen path =>
ms_svc_pending ms = Some (Z_to_bv 64 56) /\
areg ms 10 = Z_to_bv 64 (-100) /\
Z.ldiff (bv_unsigned (areg ms 12)) (O_CLOEXEC + O_LARGEFILE) = 0 /\
~ In (Z_to_bv 8 0) path /\
ms_rom ms = seg_rom segs /\
bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (path ++ [Z_to_bv 8 0])
| NRead fd buf count =>
ms_svc_pending ms = Some (Z_to_bv 64 63) /\
3 <= fd < 2^32 /\
areg ms 10 = Z_to_bv 64 fd /\
areg ms 11 = Z_to_bv 64 buf /\
areg ms 12 = Z_to_bv 64 count /\
0 <= count /\
wr_at segs (ms_mem ms) buf count
| NClose fd =>
ms_svc_pending ms = Some (Z_to_bv 64 57) /\
3 <= fd < 2^32 /\
areg ms 10 = Z_to_bv 64 fd
| NIoctl fd req =>
ms_svc_pending ms = Some (Z_to_bv 64 29) /\
0 <= fd <= 2 /\ req = 21523 /\
areg ms 10 = Z_to_bv 64 fd /\
areg ms 11 = Z_to_bv 64 req
| NSetTid =>
ms_svc_pending ms = Some (Z_to_bv 64 96)
| NExit code =>
(ms_svc_pending ms = Some (Z_to_bv 64 93) \/ ms_svc_pending ms = Some (Z_to_bv 64 94)) /\
areg ms 10 = Z_to_bv 64 code
| NBrk req =>
ms_svc_pending ms = Some (Z_to_bv 64 214) /\
areg ms 10 = Z_to_bv 64 req
| NMmap addr len prot flags =>
ms_svc_pending ms = Some (Z_to_bv 64 222) /\
areg ms 10 = Z_to_bv 64 addr /\ areg ms 11 = Z_to_bv 64 len /\
areg ms 12 = Z_to_bv 64 prot /\ areg ms 13 = Z_to_bv 64 flags /\
areg ms 14 = Z_to_bv 64 (-1) /\ areg ms 15 = Z_to_bv 64 0
| NMunmap addr len =>
ms_svc_pending ms = Some (Z_to_bv 64 215) /\
areg ms 10 = Z_to_bv 64 addr /\ areg ms 11 = Z_to_bv 64 len
| NMprotect addr len prot =>
ms_svc_pending ms = Some (Z_to_bv 64 226) /\
areg ms 10 = Z_to_bv 64 addr /\ areg ms 11 = Z_to_bv 64 len /\ areg ms 12 = Z_to_bv 64 prot
end.
End AtNode.
Ltac at_node_red :=
cbn [at_node]; unfold areg; cbn [ms_regs ms_svc_pending ms_rom ms_mem MSsvc MS];
repeat match goal with
| |- context [reg_get ?R ?r] =>
let p := eval vm_compute in (bv_key r) in
let R' := eval hnf in R in
change (reg_get R r) with (match tget p R' with Some v => v | None => w0 end);
cbv beta iota delta [tget]
end.
Ltac split_spine :=
lazymatch goal with
| |- _ /\ _ => split; [|split_spine]
| |- _ => idtac
end.
Definition eff0 (r : word) : resp := mkEffect r [] [].
Definition efferr (e : Z) : resp := eff0 (errno_ret e).
Definition open_result (mo : Model) (ent : FdEntry) (eff : resp) (mo' : Model) : Prop :=
(exists e, In e openat_errnos /\ eff = efferr e /\ mo' = mo)
\/ (let fd := alloc_fd (m_fds mo) in
fd_lookup (m_fds mo) fd = None /\ eff = eff0 fd /\
mo' = with_fds (fd_insert (m_fds mo) fd ent) mo).
Definition nstep (n : node) (mo : Model) (eff : resp) (mo' : Model) (evs : list event) : Prop :=
match n with
| NWrite fd bs =>
eff = eff0 (Z_to_bv 64 (Z.of_nat (length bs))) /\ mo' = mo /\
evs = map (WriteEv (Z_to_bv 64 fd)) bs
| NWritev fd bufs =>
eff = eff0 (Z_to_bv 64 (Z.of_nat (length (concat bufs)))) /\ mo' = mo /\
evs = map (WriteEv (Z_to_bv 64 fd)) (concat bufs)
| NOpen path =>
evs = [] /\
if (path_max <=? length path)%nat then eff = efferr ENAMETOOLONG /\ mo' = mo
else match path with
| [] => eff = efferr ENOENT /\ mo' = mo
| _ => if path_eqb path dot_path then open_result mo FdDir eff mo'
else match fs_lookup (m_fs mo) path with
| None => eff = efferr ENOENT /\ mo' = mo
| Some _ => open_result mo (FdFile path (Z_to_bv 64 0)) eff mo'
end
end
| NRead fd buf count =>
evs = [] /\
match fd_lookup (m_fds mo) (Z_to_bv 64 fd) with
| None => eff = efferr EBADF /\ mo' = mo
| Some FdDir => eff = efferr EISDIR /\ mo' = mo
| Some (FdFile p off) =>
match fs_lookup (m_fs mo) p with
| None => False
| Some data =>
let bs := file_read data off (Z_to_bv 64 count) in
eff = mkEffect (len_word bs) (delivered_writes (Z_to_bv 64 buf) bs) [] /\
mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) mo
end
| Some _ => False
end
| NClose fd =>
evs = [] /\ 3 <= fd < 2^32 /\
match fd_lookup (m_fds mo) (Z_to_bv 64 fd) with
| None => eff = efferr EBADF /\ mo' = mo
| Some _ => eff = eff0 (Z_to_bv 64 0) /\ mo' = with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo
end
| NIoctl fd req => evs = [] /\ eff = efferr ENOTTY /\ mo' = mo
| NSetTid =>
evs = [] /\ exists t, eff = eff0 t /\
match m_tid mo with
| Some t0 => t = t0 /\ mo' = mo
| None => 0 < bv_unsigned t < PID_MAX_ENVELOPE /\ mo' = with_tid t mo
end
| NExit _ => False
| NBrk _ | NMmap _ _ _ _ | NMunmap _ _ | NMprotect _ _ _ =>
evs = [] /\
match node_input n with
| Some i => syscall_spec i mo (Ok eff mo' evs)
| None => False
end
end.
Definition nexit (n : node) (mo : Model) (code : word) (mo' : Model) : Prop :=
match n with
| NExit c => code = bv_and (Z_to_bv 64 c) (Z_to_bv 64 255) /\ mo' = with_halted code mo
| _ => False
end.
Definition minv (mo : Model) : Prop :=
fd_lookup (m_fds mo) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) /\
fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) /\
fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) /\
(forall k c, fd_lookup (m_fds mo) k = Some (FdChannel c) -> bv_unsigned k < 3) /\
(forall k p off, fd_lookup (m_fds mo) k = Some (FdFile p off) -> fs_lookup (m_fs mo) p <> None) /\
(forall k p off, fd_lookup (m_fds mo) k <> Some (FdFileW p off)) /\
(forall t, m_tid mo = Some t -> 0 < bv_unsigned t < PID_MAX_ENVELOPE) /\
m_vm_lazy mo = [].
Lemma minv_nolazy : ltac2:(TCodec.tc2 tcn__CJ_Lib_Nodes "D'O&QJr1%211'='6':'RKyR0%211%4211%611&Q9r2%211(8%116%=3631p0?1pU6C1").
Proof. intros mo H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))). Qed.
Lemma minv_init : ltac2:(TCodec.tc2 tcn__CJ_Lib_Nodes "I'6':'RKyR0%211%4211%611'C'Q0&QJ&Q7r6r5r4r3r2r1%76654321%911pTJ;1pU0=1pUBA1pU4B1pT>C1pU>B1").
Proof.
intros. unfold minv. rewrite m_fds_init_model, m_fs_init_model, m_tid_init_model.
repeat split; try reflexivity; try (intros; discriminate).
- intros k c H. cbn [fd_lookup] in H.
destruct (bv_eqb (Z_to_bv 64 0) k) eqn:E0. { apply bv_eqb_eq in E0. subst k. vm_compute. reflexivity. }
destruct (bv_eqb (Z_to_bv 64 1) k) eqn:E1. { apply bv_eqb_eq in E1. subst k. vm_compute. reflexivity. }
destruct (bv_eqb (Z_to_bv 64 2) k) eqn:E2. { apply bv_eqb_eq in E2. subst k. vm_compute. reflexivity. }
discriminate.
- intros k p off H. cbn [fd_lookup] in H.
destruct (bv_eqb (Z_to_bv 64 0) k); [discriminate|].
destruct (bv_eqb (Z_to_bv 64 1) k); [discriminate|].
destruct (bv_eqb (Z_to_bv 64 2) k); discriminate.
- intros k p off H. cbn [fd_lookup] in H.
destruct (bv_eqb (Z_to_bv 64 0) k); [discriminate|].
destruct (bv_eqb (Z_to_bv 64 1) k); [discriminate|].
destruct (bv_eqb (Z_to_bv 64 2) k); discriminate.
Qed.
Definition munmap_safe_b (addr len : word) (h : VmMaps) : bool :=
if negb (Z.eqb (bv_unsigned addr mod page_size) 0) || w_is0 len then true
else
let nZ := page_round_up_Z (bv_unsigned len) in
if (two_pow_64 <=? bv_unsigned addr + nZ) then false
else
let n := Z_to_bv 64 nZ in
map_has (vm_maps h) addr n || region_free (vm_reserved h ++ vm_maps h) addr n.
Definition mprotect_safe_b (addr len prot : word) (h : VmMaps) : bool :=
if mprotect_grows_conflict_b prot then true
else if negb (Z.eqb (bv_unsigned addr mod page_size) 0) then true
else if w_is0 len then true
else if (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len)) then true
else if mprotect_modeled_b prot then
let nZ := page_round_up_Z (bv_unsigned len) in
let n := Z_to_bv 64 nZ in
(map_contains (vm_noaccess h) addr n && map_contains (vm_maps h) addr n)
|| (map_contains (vm_maps h) addr n && region_free (vm_noaccess h) addr n)
else false.
Section CEIL_NODES.
Context {RUNp : RunP}.
Definition mmap_safe_b (addr len prot flags fd off : word) (h : VmMaps) : bool :=
mmap_modeled_b prot flags off
|| mmap_noaccess_b prot flags off
|| (if w_is0 len then mmap_plain_anon_b flags
else if mmap_fixed_noaccess_b prot flags off then
let nZ := page_round_up_Z (bv_unsigned len) in
if (two_pow_64 <=? bv_unsigned addr + nZ) then true
else if negb (bv_unsigned addr + nZ <=? alloc_ceiling) then false
else if negb (Z.eqb (bv_unsigned addr mod page_size) 0) then true
else region_free (vm_reserved h) addr (Z_to_bv 64 nZ) && map_contains (vm_maps h) addr (Z_to_bv 64 nZ)
else false).
Definition nsafe (n : node) (mo : Model) : Prop :=
match n with
| NMmap addr len prot flags =>
mmap_safe_b (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags)
(Z_to_bv 64 (-1)) (Z_to_bv 64 0) (m_vmmaps mo) = true
| NMunmap addr len => munmap_safe_b (Z_to_bv 64 addr) (Z_to_bv 64 len) (m_vmmaps mo) = true
| NMprotect addr len prot =>
mprotect_safe_b (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (m_vmmaps mo) = true
| _ => True
end.
End CEIL_NODES.
Definition vm_only (m m' : Model) : Prop :=
m_fds m' = m_fds m /\ m_fs m' = m_fs m /\ m_halted m' = m_halted m /\
m_tid m' = m_tid m /\ m_stdin m' = m_stdin m.
