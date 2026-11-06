(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ExitSim ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes LibWritev LibWritevX Frame RefMemcpyLib Js0StdioDefs Js0StdioWrite_run1 Js0StdioWrite_run2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Js0StdioWrite () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0StdioDefs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0StdioWrite."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0StdioWrite.FPX_1.Loop."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0StdioWrite_run1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0StdioWrite_run2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1app"; "1bool"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "1true"; "2I"; "2and"; "2eq"; "2or"; "3add"]; ["4le"; "4lt"; "5map"; "5skipn"; "6Z"; "0K"; "7store_ok"; "7word_to_le_bytes"; "8config"; "8mkCfg"; "9FdChannel"; "9FdEntry"; "9Model"; "9WriteEv"; "9event"; "9fd_lookup"]; ["9m_fds"; "9m_halted"; "9m_vm_lazy"; ":bvmap"; ";wbytes"; "<at_"; "<ret_ok"; "=ssp_cells"; "=sw_file"; "=sw_post"; "?LM"; "?RI"; ">LM"; "@mem_sw1"; "Amem_sw2"; "Asw_regs_but"]; ["Bgetr"; "Bmkst"; "Brdn"; "Bseg_rom"; "Bv_addi"; "CTSet"; "Ct_emit"; "Dsrealizes"; "Eloaded_segments"; "Fadd"; "Fle"; "Flt"; "Fof_nat"; "Fpow"; "Fsub"; "0a"]; ["0b"; "0b0"; "0b1"; "0bs"; "0bs0"; "0bs1"; "0bufp"; "0bufsz"; "0c"; "0can"; "0extra"; "0f"; "0fd"; "0fx"; "0k"; "0l"]; ["0m"; "0mem"; "0mem'"; "0mem1"; "0model"; "0n"; "0pending"; "0ra"; "0regs"; "0regs'"; "0ret"; "0s"; "0s0"; "0s1"; "0s2"; "0s3"]; ["0s4"; "0s5"; "0s6"; "0scfg"; "GBV"; "GZ_to_bv"; "Gbv"; "Gbv_unsigned"; "0su"; "0v"; "0wb"; "0wp"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RdnPeelKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Plain.
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac rdn_side_fast := rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length]; lia_fast.
Local Ltac rdn_solve_fast :=
lazymatch goal with
| |- rdn _ (wbytes _ ?a _) ?b _ = _ =>
tryif constr_eq a b then (apply rdn_wbytes_hit8; zsimp; lia)
else (first [ RdnPeelKit.rdn_peel_many ltac:(idtac; rdn_side_fast) | rdn_peel1 ]; rdn_solve_fast)
| |- _ => rdn_hyp
end.
Local Ltac rdn_solve ::= rdn_solve_fast.
Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
#[using="Type"] Lemma rz_emit_nil : ltac2:(TCodec.tc2 tcn__Js0StdioWrite "B'H&QE'QG&QHvS3r2r1%544321r3&QF(7'N%211%4218%<4;:61p081pQ<?1pTBA1").
Proof.
intros c K H. eapply srz_conseq; [exact H|].
apply t_eq_sym. apply t_emit_nil_eq. exact (srealizes_nonempty _ _ _ _ H).
Qed.
#[using="Type"] Lemma skipn_app_le : forall {A} (k : nat) (l1 l2 : list A),
(k <= length l1)%nat -> skipn k (l1 ++ l2) = skipn k l1 ++ l2.
Proof.
intros A k l1 l2 Hk. rewrite skipn_app. replace (k - length l1)%nat with 0%nat by lia. reflexivity.
Qed.
#[using="Type"] Lemma skipn_app_ge : forall {A} (k : nat) (l1 l2 : list A),
(length l1 <= k)%nat -> skipn k (l1 ++ l2) = skipn (k - length l1) l2.
Proof.
intros A k l1 l2 Hk. rewrite skipn_app. rewrite (proj1 (skipn_all_iff k l1) Hk). reflexivity.
Qed.
#[using="Type"] Lemma u_at_le : ltac2:(TCodec.tc2 tcn__Js0StdioWrite "Q5'S6yR0%211'D&QJzr1%3221&QI&S7r3%22:1r2%5221&QM+2+R0%3221%>251'>'=&Q5r4%221=%?2G1%@2H3%B21@%73H31'<%93J5H%:3K4=%3221%=251p0?1p0K1pTNQ01pT2Q21").
Proof.
intros b k Hk Hle. unfold at_. pose proof (u64_range b).
destruct (Z.eq_dec (bv_unsigned b + k) (2 ^ 64)) as [E|NE].
- right. split; [|exact E]. rewrite E. vm_compute. reflexivity.
- left. u_norm. reflexivity.
Qed.
Section Loop.
Variables (su f fd : Z) (l bufp bufsz can ret : word).
Variables (e8 e9 e18 e19 e20 e21 e22 g3 g4 g23 g24 g25 g26 g27 : word).
Variable mem1 : word -> option byte.
Variable model : Model.
Variable K : TSet.
Hypothesis SUlo : (4294967296 + 112 <= su)%Z.
Hypothesis SUhi : (su <= 0x800000000000)%Z.
Hypothesis Flo : (0xb5000 <= f)%Z.
Hypothesis Fhi : (f + 232 <= 0xe7ed0)%Z.
Hypothesis FD : (0 < fd < 2147483648)%Z.
Hypothesis Hfd : fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)).
Hypothesis Hh : m_halted model = None.
Hypothesis Hlazy : m_vm_lazy model = [].
Hypothesis Hret : ret_ok ret.
Hypothesis HKnil : K [].
Hypothesis SOK1 : store_ok RSEGS mem1 (Z_to_bv 64 (su - 112)) 112%nat = true.
Hypothesis M8 : rdn RSEGS mem1 (Z_to_bv 64 (su - 8)) 8%nat = Some (word_to_le_bytes 8 ret).
Hypothesis M16 : rdn RSEGS mem1 (Z_to_bv 64 (su - 16)) 8%nat = Some (word_to_le_bytes 8 e8).
Hypothesis M24 : rdn RSEGS mem1 (Z_to_bv 64 (su - 24)) 8%nat = Some (word_to_le_bytes 8 e9).
Hypothesis M32 : rdn RSEGS mem1 (Z_to_bv 64 (su - 32)) 8%nat = Some (word_to_le_bytes 8 e18).
Hypothesis M40 : rdn RSEGS mem1 (Z_to_bv 64 (su - 40)) 8%nat = Some (word_to_le_bytes 8 e19).
Hypothesis M48 : rdn RSEGS mem1 (Z_to_bv 64 (su - 48)) 8%nat = Some (word_to_le_bytes 8 e20).
Hypothesis M56 : rdn RSEGS mem1 (Z_to_bv 64 (su - 56)) 8%nat = Some (word_to_le_bytes 8 e21).
Hypothesis M64 : rdn RSEGS mem1 (Z_to_bv 64 (su - 64)) 8%nat = Some (word_to_le_bytes 8 e22).
Hypothesis M72 : rdn RSEGS mem1 (Z_to_bv 64 (su - 72)) 8%nat = Some (word_to_le_bytes 8 can).
Hypothesis Mcan : rdn RSEGS mem1 (Z_to_bv 64 0xe7ed0) 8%nat = Some (word_to_le_bytes 8 can).
Hypothesis Mbuf : rdn RSEGS mem1 (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp).
Hypothesis Mbsz : rdn RSEGS mem1 (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz).
Hypothesis Mfd : rdn RSEGS mem1 (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)).
Definition LM (m : word -> option byte) : Prop :=
(forall x : word, ~ (su - 104 <= bv_unsigned x < su - 72)%Z -> m x = mem1 x) /\ mem_grows mem1 m.
Hypothesis HK : forall regs' m,
getr regs' 10 = l -> getr regs' 2 = Z_to_bv 64 su -> getr regs' 1 = ret ->
getr regs' 8 = e8 -> getr regs' 9 = e9 ->
getr regs' 18 = e18 -> getr regs' 19 = e19 -> getr regs' 20 = e20 ->
getr regs' 21 = e21 -> getr regs' 22 = e22 -> getr regs' 23 = g23 ->
getr regs' 24 = g24 -> getr regs' 25 = g25 -> getr regs' 26 = g26 ->
getr regs' 27 = g27 -> getr regs' 3 = g3 -> getr regs' 4 = g4 ->
LM m ->
srealizes RSEGS scfg (mkCfg (mkst regs' ret (mem_sw2 m f bufp bufsz) (seg_rom RSEGS)) model) K.
Definition RI (regs : bvmap 5 word) : Prop :=
getr regs 2 = Z_to_bv 64 (su - 112) /\ getr regs 8 = l /\ getr regs 9 = Z_to_bv 64 f
/\ getr regs 21 = Z_to_bv 64 0xe7ed0 /\ getr regs 3 = g3 /\ getr regs 4 = g4
/\ getr regs 23 = g23 /\ getr regs 24 = g24 /\ getr regs 25 = g25
/\ getr regs 26 = g26 /\ getr regs 27 = g27.
Section SE.
Local Abbreviation SEC_T_RI_but := (ltac2:(TCodec.tc2 tcn__Js0StdioWrite "A&Q3y5'S6yR0%211%5241&Q;r2%211&Q?r3%2214%612p021p061pUD:1pUB;1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_RI_but) 0%nat 0%nat).
Variable regs' : ltac:(sec_ty2 constr:(SEC_T_RI_but) 1%nat 0%nat).
Lemma RI_but : ltac:(sec_stmt2 constr:(SEC_T_RI_but) 2%nat 0%nat).
Proof using Type regs regs'.
intros (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27)
(P2 & P8 & P9 & P21 & P3 & P4 & P23 & P24 & P25 & P26 & P27).
unfold RI. rewrite P2, P8, P9, P21, P3, P4, P23, P24, P25, P26, P27. repeat split; assumption.
Qed.
End SE.
#[using="Type"] Lemma LM_refl : ltac2:(TCodec.tc2 tcn__Js0StdioWrite "3&Q:vRC%211").
Proof. split; [intros; reflexivity | apply mem_grows_refl]. Qed.
#[using="Type"] Lemma LM_rdn : ltac2:(TCodec.tc2 tcn__Js0StdioWrite "R1'S6yR0%211'8y8%511%311p051'6'5%115&Q:r4%211'=%<15&QB&QHvRCr3%443281(1r2%22=1%:3941&QJ&QI&S7r5%22L1&QL%11C%6231&QM+2+R0%3221%<251'>r6%=2Q71%;1=%@221&QNvS8+S8%3221%F251+R8%6251%I21:%=241r8r7%Q64Q521?%Q22Q=K%Q:3Q921p061p0E1p0Q31p0Q?1pT8QC1pU<QF1pT0QM1pU2QI1").
Proof.
intros m a n bs [E G] H Hnw D.
rewrite (rdn_ext RSEGS n m mem1 a Hnw); [exact H|].
intros x Hx. apply E. lia.
Qed.
#[using="Type"] Lemma LM_store_ok : ltac2:(TCodec.tc2 tcn__Js0StdioWrite "N'S6yR0%211'8y8%511%311p051'6&Q:r3%211'='3&F&QHvRCr2%443281(:%83721r5r4%94821=%<3;15p051p0?1pU<C1pT0J1pU2F1").
Proof. intros m a n [E G] H. eapply store_ok_mono; [exact G | exact H]. Qed.
#[using="SUlo SUhi"] Lemma LM_wbytes8 : ltac2:(TCodec.tc2 tcn__Js0StdioWrite "Q9'S6yR0%211'8y8%511%311p051'D&Q:r3%211&QJ&QNvS8+S8%3221%5217&QIr4+8%3221+R8%:291%<231&Q4r6&S5r5%22L1&Gu8%221=%83741%I11p0;1p0C1p0J1pVDQ41pT0O1pU2Q11").
Proof.
intros m a v [E G] Hlo Hhi. split.
- intros x Hx. rewrite wbytes_outside.
+ apply E, Hx.
+ unfold in_rng. rewrite length_N_to_le_bytes. u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
+ rewrite length_N_to_le_bytes. u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
- eapply mem_grows_trans; [exact G | apply wbytes_grows].
Qed.
Section SE.
Local Abbreviation SEC_T_finish := (ltac2:(TCodec.tc2 tcn__Js0StdioWrite "Q8&Q3y5'S6yR0%211%5241'8y8%611%311p061&Q;r2%211&Q:%113'QG&QHvS3(I&QAvR=r4(S4+cgV<(;%33G21/01Gr3&QC%11=%;5:9431vRD%>221vE%C4BA21p0E1p0H1pU2L1pUBQ21")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_finish) 0%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_finish) 1%nat 0%nat).
Lemma finish : ltac:(sec_stmt2 constr:(SEC_T_finish) 2%nat 0%nat).
Proof using bufp bufsz can ret e8 e9 e18 e19 e20 e21 e22 SUlo SUhi Flo Fhi Hh Hlazy Hret M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz HK regs m.
intros RIr LMm.
destruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27).
destruct (sw_done regs m (seg_rom RSEGS) su f l bufp bufsz can ret e8 e9 e18 e19 e20 e21 e22)
as (regs2 & RUN & Q10 & Q2 & Q1 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q3 & Q4 & Q23 & Q24 & Q25 & Q26 & Q27);
try assumption.
all: try (eapply LM_rdn; [exact LMm | eassumption | u_norm; lia | u_norm; lia]).
eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
apply HK; try assumption.
- rewrite Q23; exact R23.
- rewrite Q24; exact R24.
- rewrite Q25; exact R25.
- rewrite Q26; exact R26.
- rewrite Q27; exact R27.
- rewrite Q3; exact R3.
- rewrite Q4; exact R4.
Qed.
End SE.
#[using="bufp bufsz can ret e8 e9 e18 e19 e20 e21 e22 SUlo SUhi Flo Fhi Hh Hlazy Hret M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz HK"] Lemma finish_nil : ltac2:(TCodec.tc2 tcn__Js0StdioWrite "Q=&Q3y5'S6yR0%211%5241'8y8%611%311p061&Q;r2%211&Q:%113'QG&QHvS3(I&QAvR=r4(S4+cgV<(;%33G21/01Gr3&QC%11=%;5:9431vRD%>221&QF(7'N%211vE%5221%H4GF71p0J1p0M1pU2Q11pUBQ71").
Proof. intros. apply rz_emit_nil. apply finish; assumption. Qed.
#[using="Type"] Lemma pc_9dcfc : ltac2:(TCodec.tc2 tcn__Js0StdioWrite "@'='S6yR0%211&QD(S4+cgZ8(;%33621/016+4%7221+cgZ<%83;16/01;%?3<41").
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
#[using="bufp bufsz can ret e8 e9 e18 e19 e20 e21 e22 SUlo SUhi Flo Fhi FD Hfd Hh Hlazy Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK"] Lemma loop1 : ltac2:(TCodec.tc2 tcn__Js0StdioWrite "U?'6&Q3y5'S6yR0%211%5241'8y8%611%311p061'5%114'@&4r1%2281r6%5221&Q;%113&Q:%115'=&Q@r8(S4+:(;%33L21%6251&S5&QL%11@%32O1%<3O51r9+F%<3Q51:%?231r5%K2Q11%:11%<2Q81%E3Q851r:+B%E3Q>1C%H231+1%C2Q?1%L3Q?31r;+C%L3QE1J%O231&QNvS8+RH%3221%M2QI1%Q63QI61'<u1%QC21C&A%QD2QJQ9%22F1%6241%QO1QI&QB&QHr<u8%4432>1(1&G%124Q0%32R21%QH3:51r=+R@%J2I1%QD2R@1%>4=41;%R72R=Q8%QF11%QH2RD1%<2?1%>2R=1%R33E61vRC%R>2RDQ8%G4F2E1%C2RBQ:%R83J21'>&QJ&QI&S7%12S1D%RG2RMM%R611%5231+S@%QA2Q@1%9231%:2QB7%<221r>%;2S;1%S12S7O%R@11%?231&QM+2+Q?%3221%E251%S92S?:%RH11+N%8271%J231'QGvS3(I&QAvR=rC+cgZH%S93T01S7/01T0rB&QC%11R0%9587431vRD%<221&QF&B'N(MvR<%SA2T=1%311&CrAr?%33T=21%:4T>951vE%=221%M4RBL?1p0O1p0Q51p0Q@1p0QN1p0R41p0R@1p0RL1p0S41p0S?1p0SG1p0T11p0T?1p0TB1p0TE1pT8TL1pT2U51pTNU;1pU2U11pUBU71pU<U>1").
Proof.
induction n as [|n IH]; intros regs m k b bs LEN RIr LMm Ha0 Hs6 Hs2 Hs3 Kb Mb Mn Bbs DISJ NW M30.
{ exfalso. lia. }
pose proof RIr as RIr'.
destruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27).
pose proof (u64_range b) as Hb.
destruct (sw_retry_a regs m (seg_rom RSEGS) su f fd (su - 88) 1 (Z.of_nat k)
(Z.of_nat (length bs)) (Z.of_nat (length bs)) b)
as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
{ eapply LM_store_ok; [exact LMm | exact SOK1]. }
{ replace (su - 88 + 8)%Z with (su - 80)%Z by lia. exact Mn. }
{ eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
replace (su - 88 + 8)%Z with (su - 80)%Z by lia.
set (m' := wbytes (wbytes m _ _) _ _).
assert (LMm' : LM m').
{ subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).
eapply (rz_writev1_wallX RSEGS scfg regs1 (0x9dd48 : word) m' model (ltac:(oW' 0x9dd48%Z)) fd
(Z_to_bv 64 (su - 88)) (Z_to_bv 64 (bv_unsigned b + Z.of_nat k))
(Z_to_bv 64 (Z.of_nat (length bs) - Z.of_nat k)) (skipn k bs) K);
[ exact (ltac:(oF' 0x9dd48%Z)) | exact (ltac:(oE' 0x9dd48%Z)) | exact Hh | exact Hlazy | exact Hfd | exact FD
| exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | | | exact HKnil | ].
- subst m'. rdn_solve.
- subst m'. u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rdn_solve.
- rewrite word_to_nat_Z by lia.
replace (Z.to_nat (Z.of_nat (length bs) - Z.of_nat k)) with (length bs - k)%nat by lia.
subst m'. repeat rdn_peel1.
change (Z_to_bv 64 (bv_unsigned b + Z.of_nat k)) with (at_ b (Z.of_nat k)).
apply (rdn_skipn RSEGS m (length bs) b bs k); [|lia].
eapply LM_rdn; [exact LMm | exact Bbs | lia | lia].
- unfold TASK_SIZE. u_norm. lia.
- unfold TASK_SIZE. u_norm. lia.
- u_norm. lia.
- u_norm. lia.
-
intros k' K1 K2. rewrite pc_9dcfc. rewrite length_skipn in K2.
destruct (Nat.eq_dec k' (length bs - k)) as [EQ|NE].
+
destruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. rewrite Q22. f_equal. lia. }
{ lia. }
eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
rewrite (proj1 (skipn_all_iff k' (skipn k bs))) by (rewrite length_skipn; lia).
apply finish_nil; [| exact LMm'].
eapply RI_but; [exact RI1|].
revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
+
destruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
(Z.of_nat (length bs) - Z.of_nat k))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. exact Q22. }
{ lia. }
{ lia. }
{ lia. }
eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
apply (IH regs2 m' k' (at_ b (Z.of_nat k)) (skipn k bs)).
* rewrite length_skipn. lia.
* eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
* exact LMm'.
* exact P10.
* rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
* rewrite P18. gres. exact Q18.
* rewrite P19. gres. exact Q20.
* rewrite length_skipn. lia.
* subst m'. unfold at_. rdn_solve.
* subst m'. rewrite length_skipn.
replace (Z.of_nat (length bs - k)) with (Z.of_nat (length bs) - Z.of_nat k)%Z by lia. rdn_solve.
* rewrite length_skipn. apply (rdn_skipn RSEGS mem1 (length bs) b bs k); [exact Bbs|lia].
* unfold at_. rewrite length_skipn. u_norm. lia.
* unfold at_. rewrite length_skipn. u_norm. lia.
* rewrite length_skipn. lia.
Qed.
#[using="bufp bufsz can ret e8 e9 e18 e19 e20 e21 e22 SUlo SUhi Flo Fhi FD Hfd Hh Hlazy Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK"] Lemma loop2 : ltac2:(TCodec.tc2 tcn__Js0StdioWrite "VG'6&Q3y5'S6yR0%211%5241'8y8%611%311p061'5%114'@&?&4r3%2291r1%42;1%6231r8%9221&Q;%113&Q:%115'=&Q@r:(S4+:(;%33Q021%6251&S5&QL%11@%32Q31%<3Q351r;+F%<3Q91:%?231&QIr7%O2Q61%;11r5%Q22Q91%>11%7241%A2QA1%J3QA:1r<+B%J3QG1H%M231+2%H2QH1%Q13QH31r=+C%Q13QN1O%Q4231&QNvS8+S8%3221%Q22R21%Q;3R261'<u1%QL21C&A%QL2R3Q>%QM2R4QG%QO221%42H1%8261%R:1R4&QB&QHr>u8%4432@1(1&G%124Q2%32R=1%QO3:51r?+S0%L2K1%QK2RK1%>4=41;%RA2RHQ:%QM11%QO2RO1%<2?1%>2RH1%R:3E61r@+RH%Q72Q61%R62S61%I4H41F%R@3K1BrA+R@%Q=2Q<1%R<2S<1%O4N41L%RF3Q11=vRC%S42S;H%Q34Q22>1%O2S9J%RK3Q621%S82S?Q4%Q74Q66M1%Q32S=Q6%RO3Q:21'>&QJ&S7rB%22SL1%SA2SHD%RM11%RF231+S@%R32R21%9231%:2R47%<221rC%<2T61%SK2T2<%S711%S0231&QM+Q?%22RE1%D241rE%T32T:1%S?11%T52T<<%SA11%S:231+N%;2RN1%M231'QGvS3(I&QAvR=rJ+cgZH%T33TN1T1/01TNrI&QC%11RC%9587431vRD%<221&QF&B'N(MvR<%T;2U;1%311&CrH&2rFrD%33U=21%63U>51%=4U?<81vE%@221%Q04S8OB1p0Q21p0Q<1p0QF1p0Q>1p0QH1p0R61p0R;1p0RA1p0RH1p0RO1p0S;1p0SG1p0T11p0T<1p0TD1p0U31p0UA1p0UD1p0UG1pT<V21pT6V;1pT:V41pT4V=1pTNVC1pU2V91pUBV?1pU<VF1").
Proof.
induction n as [|n IH]; intros regs m k b0 bs0 b1 bs1 LEN RIr LMm Ha0 Hs6 Hs2 Hs3 Kb
Mb0 Mn0 Mb1 Mn1 Bbs0 Bbs1 DISJ0 NW0 DISJ1 NW1 M30.
{ exfalso. lia. }
pose proof RIr as RIr'.
destruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27).
pose proof (u64_range b0) as Hb0. pose proof (u64_range b1) as Hb1.
destruct (Nat.le_gt_cases k (length bs0)) as [LE|GT].
-
destruct (sw_retry_a regs m (seg_rom RSEGS) su f fd (su - 104) 2 (Z.of_nat k)
(Z.of_nat (length bs0)) (Z.of_nat (length bs0) + Z.of_nat (length bs1)) b0)
as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
{ eapply LM_store_ok; [exact LMm | exact SOK1]. }
{ replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact Mn0. }
{ eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
replace (su - 104 + 8)%Z with (su - 96)%Z by lia.
set (m' := wbytes (wbytes m _ _) _ _).
assert (LMm' : LM m').
{ subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).
rewrite (skipn_app_le k bs0 bs1 LE).
eapply (rz_writev2_wallX RSEGS scfg regs1 (0x9dd48 : word) m' model (ltac:(oW' 0x9dd48%Z)) fd
(Z_to_bv 64 (su - 104)) (Z_to_bv 64 (bv_unsigned b0 + Z.of_nat k))
(Z_to_bv 64 (Z.of_nat (length bs0) - Z.of_nat k))
b1 (Z_to_bv 64 (Z.of_nat (length bs1))) (skipn k bs0) bs1 K);
[ exact (ltac:(oF' 0x9dd48%Z)) | exact (ltac:(oE' 0x9dd48%Z)) | exact Hh | exact Hlazy | exact Hfd | exact FD
| exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | | | | | | | exact HKnil | ].
+ subst m'. rdn_solve.
+ subst m'. u_norm. replace (su - 104 + 8)%Z with (su - 96)%Z by lia. rdn_solve.
+ subst m'. u_norm. replace (su - 104 + 16)%Z with (su - 88)%Z by lia. repeat rdn_peel1. exact Mb1.
+ subst m'. u_norm. replace (su - 104 + 24)%Z with (su - 80)%Z by lia. repeat rdn_peel1. exact Mn1.
+ rewrite word_to_nat_Z by lia.
replace (Z.to_nat (Z.of_nat (length bs0) - Z.of_nat k)) with (length bs0 - k)%nat by lia.
destruct (Nat.eq_dec k (length bs0)) as [EK|NK].
{ replace (length bs0 - k)%nat with 0%nat by lia.
rewrite (proj1 (skipn_all_iff k bs0)) by lia. reflexivity. }
subst m'. repeat rdn_peel1.
change (Z_to_bv 64 (bv_unsigned b0 + Z.of_nat k)) with (at_ b0 (Z.of_nat k)).
apply (rdn_skipn RSEGS m (length bs0) b0 bs0 k); [|lia].
eapply LM_rdn; [exact LMm | exact Bbs0 | lia | lia].
+ rewrite word_to_nat_Z by lia. rewrite Nat2Z.id.
subst m'. repeat rdn_peel1.
eapply LM_rdn; [exact LMm | exact Bbs1 | lia | lia].
+ unfold TASK_SIZE. u_norm. lia.
+ unfold TASK_SIZE. u_norm. lia.
+ unfold TASK_SIZE. u_norm. lia.
+ u_norm. lia.
+ u_norm. lia.
+ intros k' K1 K2. rewrite pc_9dcfc. rewrite length_app, length_skipn in K2.
destruct (Nat.eq_dec k' (length bs0 - k + length bs1)) as [EQ|NE].
* destruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. rewrite Q22. f_equal. lia. }
{ lia. }
eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
rewrite (proj1 (skipn_all_iff k' (skipn k bs0 ++ bs1))) by (rewrite length_app, length_skipn; lia).
apply finish_nil; [| exact LMm'].
eapply RI_but; [exact RI1|].
revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
* destruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
(Z.of_nat (length bs0) + Z.of_nat (length bs1) - Z.of_nat k))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. exact Q22. }
{ lia. }
{ lia. }
{ lia. }
eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
apply (IH regs2 m' k' (at_ b0 (Z.of_nat k)) (skipn k bs0) b1 bs1).
-- rewrite length_skipn. lia.
-- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
-- exact LMm'.
-- exact P10.
-- rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
-- rewrite P18. gres. exact Q18.
-- rewrite P19. gres. exact Q20.
-- rewrite length_skipn. lia.
-- subst m'. unfold at_. rdn_solve.
-- subst m'. rewrite length_skipn.
replace (Z.of_nat (length bs0 - k)) with (Z.of_nat (length bs0) - Z.of_nat k)%Z by lia. rdn_solve.
-- subst m'. repeat rdn_peel1. exact Mb1.
-- subst m'. repeat rdn_peel1. exact Mn1.
-- rewrite length_skipn. apply (rdn_skipn RSEGS mem1 (length bs0) b0 bs0 k); [exact Bbs0|lia].
-- exact Bbs1.
-- pose proof (u_at_le b0 (Z.of_nat k) ltac:(lia) ltac:(lia)). rewrite length_skipn. lia.
-- pose proof (u_at_le b0 (Z.of_nat k) ltac:(lia) ltac:(lia)). rewrite length_skipn. lia.
-- exact DISJ1.
-- exact NW1.
-- rewrite length_skipn. lia.
-
destruct (sw_retry_b regs m (seg_rom RSEGS) su f fd (su - 104) (Z.of_nat k)
(Z.of_nat (length bs0)) (Z.of_nat (length bs1))
(Z.of_nat (length bs0) + Z.of_nat (length bs1)) b1)
as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
{ eapply LM_store_ok; [exact LMm | exact SOK1]. }
{ replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact Mn0. }
{ replace (su - 104 + 16)%Z with (su - 88)%Z by lia. exact Mb1. }
{ replace (su - 104 + 24)%Z with (su - 80)%Z by lia. exact Mn1. }
{ eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
replace (su - 104 + 16)%Z with (su - 88)%Z in * by lia.
replace (su - 104 + 24)%Z with (su - 80)%Z by lia.
replace (Z.of_nat k - Z.of_nat (length bs0))%Z with (Z.of_nat (k - length bs0)) by lia.
set (m' := wbytes (wbytes m _ _) _ _).
assert (LMm' : LM m').
{ subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).
rewrite (skipn_app_ge k bs0 bs1) by lia.
eapply (rz_writev1_wallX RSEGS scfg regs1 (0x9dd48 : word) m' model (ltac:(oW' 0x9dd48%Z)) fd
(Z_to_bv 64 (su - 88)) (Z_to_bv 64 (bv_unsigned b1 + Z.of_nat (k - length bs0)))
(Z_to_bv 64 (Z.of_nat (length bs1) - Z.of_nat (k - length bs0)))
(skipn (k - length bs0) bs1) K);
[ exact (ltac:(oF' 0x9dd48%Z)) | exact (ltac:(oE' 0x9dd48%Z)) | exact Hh | exact Hlazy | exact Hfd | exact FD
| exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | | | exact HKnil | ].
+ subst m'. rdn_solve.
+ subst m'. u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rdn_solve.
+ rewrite word_to_nat_Z by lia.
replace (Z.to_nat (Z.of_nat (length bs1) - Z.of_nat (k - length bs0))) with (length bs1 - (k - length bs0))%nat by lia.
subst m'. repeat rdn_peel1.
change (Z_to_bv 64 (bv_unsigned b1 + Z.of_nat (k - length bs0))) with (at_ b1 (Z.of_nat (k - length bs0))).
apply (rdn_skipn RSEGS m (length bs1) b1 bs1 (k - length bs0)); [|lia].
eapply LM_rdn; [exact LMm | exact Bbs1 | lia | lia].
+ unfold TASK_SIZE. u_norm. lia.
+ unfold TASK_SIZE. u_norm. lia.
+ u_norm. lia.
+ u_norm. lia.
+ intros k' K1 K2. rewrite pc_9dcfc. rewrite length_skipn in K2.
destruct (Nat.eq_dec k' (length bs1 - (k - length bs0))) as [EQ|NE].
* destruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. rewrite Q22. f_equal. lia. }
{ lia. }
eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
rewrite (proj1 (skipn_all_iff k' (skipn (k - length bs0) bs1))) by (rewrite length_skipn; lia).
apply finish_nil; [| exact LMm'].
eapply RI_but; [exact RI1|].
revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
* destruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
(Z.of_nat (length bs0) + Z.of_nat (length bs1) - Z.of_nat k))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. exact Q22. }
{ lia. }
{ lia. }
{ lia. }
eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
apply (loop1 (length bs1) regs2 m' k' (at_ b1 (Z.of_nat (k - length bs0))) (skipn (k - length bs0) bs1)).
-- rewrite length_skipn. lia.
-- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
-- exact LMm'.
-- exact P10.
-- rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
-- rewrite P18. gres. exact Q18.
-- rewrite P19. gres. exact Q20.
-- rewrite length_skipn. lia.
-- subst m'. unfold at_. rdn_solve.
-- subst m'. rewrite length_skipn.
replace (Z.of_nat (length bs1 - (k - length bs0))) with (Z.of_nat (length bs1) - Z.of_nat (k - length bs0))%Z by lia.
rdn_solve.
-- rewrite length_skipn.
apply (rdn_skipn RSEGS mem1 (length bs1) b1 bs1 (k - length bs0)); [exact Bbs1|lia].
-- unfold at_. rewrite length_skipn. u_norm. lia.
-- unfold at_. rewrite length_skipn. u_norm. lia.
-- rewrite length_skipn. lia.
Qed.
End Loop.
End FPX_1.
Ltac wout1 :=
rewrite wbytes_outside;
[ | unfold in_rng; rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; u_norm; lia
| rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; u_norm; lia ].
Section FPX_2. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
#[using="Type"] Lemma sw_post_of_LM : ltac2:(TCodec.tc2 tcn__Js0StdioWrite "R9'S6yR0%211'8y8%511%311p051'D&QJ&QI+TPPPPP0+S@%3221rA%6221rB+TPPPPPPPP0%9221+fdP0%;214rC+W8%=221+lof@%@221&Q<rE&Q=rGr@r?r>r=r<r;r:r9r8r7%<?;=CHJ:987654321rF%@3?21'Q9rHr6&Q>%14BD82%5647E931p071p0I1p0O1p0Q21p0Q61pT@QD1pT>QE1pU0QF1pUHQG1pU<QB1pVFQC1pTDQJ1pV6QK1pV4QL1pV2QM1pV0QN1pUNQO1pULR01pUJR11pU@R21pTHQM1pVBQN1pU2R01pU4R11").
Proof.
intros mem m su f ra s0 s1 s2 s3 s4 s5 s6 can wb n s l bufp bufsz SUlo SUhi Flo Fhi [E G].
constructor.
- intros x Hx1 Hx2 Hx3. pose proof (u64_range x) as Hx.
unfold mem_sw2. do 3 wout1.
rewrite (E x) by lia.
unfold mem_sw1. do 13 wout1. reflexivity.
- unfold mem_sw2. repeat (eapply mem_grows_trans; [|apply wbytes_grows]).
eapply mem_grows_trans; [|exact G].
unfold mem_sw1. repeat (eapply mem_grows_trans; [|apply wbytes_grows]).
apply mem_grows_refl.
- unfold mem_sw2. rdn_solve.
- unfold mem_sw2. rdn_solve.
- unfold mem_sw2. rdn_solve.
Qed.
#[using="Type"] Lemma pc_9dc74 : ltac2:(TCodec.tc2 tcn__Js0StdioWrite "@'='S6yR0%211&QD(S4+cgV0(;%33621/016+4%7221+cgV4%83;16/01;%?3<41").
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_ref_stdio_write := (ltac2:(TCodec.tc2 tcn__Js0StdioWrite "[M&Q3y5'S6yR0%211%5241'8y8%611%311p061'L'D'5%116&QE'=&Q@rA(S4+2(;%33E21%6251&S5r>%22G1%;3G41rB+:%;3M19%>231%@3L16rC+;%@3Q21>%C231r;%F3Q221rD+<%F3Q81D%I231%K3Q716rE+1%K3Q=1I%N231r8%Q13Q=21&QJ&QI+TPPPPP0+S@%3221%521F+TPPPPPPPP0%72B1'3&F&QHrG&QN%12C:%Q82QM1uS@%746521(:%QD3:21+fdP0%D21JrF+W8%F221+lof@%I221'Q8rJr@%372B8Q3Q8QM1&Q7rK%2214'<&QKz%221?+RPPPPP0%42A1%6231'K%RE11&O&Q0rL%211%R82RMQ3%5221(1(J%114%32;1%RF3;51%S11S3&Q1rM%211(0%11S8%RM3631'9%12S;S;%S311&Q2rN%211(7%116%S63631%R52Q2I%R62JQ7%Q6221&QM+Q?%22S81%R;2O1%R02E<&QL&4%12SIRE%311%SC3SG51&S7%12T2QD%SF3SJ14%72SOR:%911%92T1R2%;11%RH231+N%C2SI1%RL231'>rQ0rQ3%RD21RM%S1231rQ1%S3241%7231rO%D2TE1%E2TFQ7%S7221rQ4%RN21S7%S;231%S<236%@221%L2TM@%S>219%S@21Q6%TM1TE&QBrQ8%T>2U3;%Q72TORF%44S<321%R72TKRH%TJ3721rQ9rQ2%94SA216%TN3;15&Q6%11QN'N%QN11%RE11r2%U421TGrQ6%U73UC21r3%U821U3rQ=%U32UH1%U<3UH31r4%U=21T@%U?3UK1Q4r5+8%U?3V11U=%UB231rQB%UD213%UF3V231r6+9%UF3V81UD%UI231rQC%UK213%UM3V931r7+B%UM3V?1UK%V0231rQD%V2213%V43V@31+C%V33VE1V1%V62U71rQE%V8213%V:3VF31r9+D%V:3VL1V8%V=231rQF%V?213%VA3VM31r:+E%VA3W31V?%VD231rQG%VF213%VH3W431+F%VG3W91VE%VJ2V61rQH%VL213%VN3W:31r<+G%VN3W@1VL%W1231rQI%W3213%W53WA31r=+H%W53WG1W3%W8231rQJ%W:213%W<3WH31+I%W;3WM1W9%W>2W61rQK%W@213%WB3WN31r?+J%WB3X41W@%WE231rQL%WG213%WI3X531+K%WH3X:1WF%WK2UN1rQM%WM213%WO3X;31+3%WN3X@1WL%X12X01rQN%X3213%X53XA31+4%X43XF1X2%X72WL1rQO%X9213%X;3XG31'Q9%164@FQNR5X1'QGvS3(I&QAvR=&QC%11W8%453WNRCX41%621=rQA%:4W<921p0<1p0?1p0F1p0M1p0Q41p0Q<1p0QC1p0QK1p0R31p0R:1p0RB1p0RJ1p0S11p0S91p0SA1p0SI1p0SM1p0T31pU6YA1pUDYG1rQ>+cgQH%Y<3YL1Y:/01YL%Q05O41T7MrQ<%Q3221&QF&B(MrQ7%Y@2Z51%311&2%13Z3UKUD%74Z4TK31%921VK%Q@4XBQ?;1p0C1p0TM1p0U11p0U41p0U91p0UB1p0UF1p0V01p0V91p0VB1p0VF1p0VM1p0W21p0W61p0W@1p0WH1p0X61p0X>1p0XB1p0XG1p0XM1p0Y01p0Y<1p0Y?1p0YF1p0YM1p0Z31p0Z:1p0Z@1pQ<ZM1pTFZO1pU>[01pUF[;1pTD[<1pT@[=1pT>[>1pU0[?1pUH[@1pTJ[91pVH[:1pVF[;1pTH[<1pVB[=1pU:[?1pU4[A1pUB[G1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_ref_stdio_write) 0%nat 0%nat).
Variable mem : ltac:(sec_ty2 constr:(SEC_T_ref_stdio_write) 1%nat 0%nat).
Variable model : ltac:(sec_ty2 constr:(SEC_T_ref_stdio_write) 2%nat 0%nat).
Variable su : ltac:(sec_ty2 constr:(SEC_T_ref_stdio_write) 3%nat 0%nat).
Variable f : ltac:(sec_ty2 constr:(SEC_T_ref_stdio_write) 4%nat 0%nat).
Variable wb : ltac:(sec_ty2 constr:(SEC_T_ref_stdio_write) 5%nat 0%nat).
Variable wp : ltac:(sec_ty2 constr:(SEC_T_ref_stdio_write) 6%nat 0%nat).
Variable fd : ltac:(sec_ty2 constr:(SEC_T_ref_stdio_write) 7%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SEC_T_ref_stdio_write) 8%nat 0%nat).
Variable l : ltac:(sec_ty2 constr:(SEC_T_ref_stdio_write) 9%nat 0%nat).
Variable bufp : ltac:(sec_ty2 constr:(SEC_T_ref_stdio_write) 10%nat 0%nat).
Variable bufsz : ltac:(sec_ty2 constr:(SEC_T_ref_stdio_write) 11%nat 0%nat).
Variable can : ltac:(sec_ty2 constr:(SEC_T_ref_stdio_write) 12%nat 0%nat).
Variable ret : ltac:(sec_ty2 constr:(SEC_T_ref_stdio_write) 13%nat 0%nat).
Theorem ref_stdio_write : ltac:(sec_stmt2 constr:(SEC_T_ref_stdio_write) 14%nat 0%nat).
Proof using Type regs mem model su f wb wp fd s l bufp bufsz can ret.
intros pending extra K
Hsp Ha0 Ha1 Ha2 Hra SUlo SUhi SOK Flo Fhi SWF SSP FD Hfd Hh Hlazy WBP WPhi
LENP LENE M30 DISJP DISJE SNW RDP RDE Hret HKnil HK.
pose proof (u64_range s) as Hs. pose proof (u64_range l) as Hl.
pose proof SWF as SWF'. pose proof SSP as SSP'.
destruct SWF as [Fwp Fwb Ffd Fbuf Fbsz]. destruct SSP as [Ggot Gcan].
zaddr Fwp; zaddr Fwb; zaddr Ffd; zaddr Fbuf; zaddr Fbsz.
assert (HlZ : l = Z_to_bv 64 (Z.of_nat (length extra))).
{ rewrite <- LENE. symmetry. apply u64_roundtrip'. }
set (mem1 := mem_sw1 mem su ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
(getr regs 20) (getr regs 21) (getr regs 22) can wb (wp - wb) s l).
assert (SOK1 : store_ok RSEGS mem1 (Z_to_bv 64 (su - 112)) 112%nat = true).
{ subst mem1; unfold mem_sw1. store_ok_peel. exact SOK. }
assert (M8 : rdn RSEGS mem1 (Z_to_bv 64 (su - 8)) 8%nat = Some (word_to_le_bytes 8 ret)) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M16 : rdn RSEGS mem1 (Z_to_bv 64 (su - 16)) 8%nat = Some (word_to_le_bytes 8 (getr regs 8))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M24 : rdn RSEGS mem1 (Z_to_bv 64 (su - 24)) 8%nat = Some (word_to_le_bytes 8 (getr regs 9))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M32 : rdn RSEGS mem1 (Z_to_bv 64 (su - 32)) 8%nat = Some (word_to_le_bytes 8 (getr regs 18))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M40 : rdn RSEGS mem1 (Z_to_bv 64 (su - 40)) 8%nat = Some (word_to_le_bytes 8 (getr regs 19))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M48 : rdn RSEGS mem1 (Z_to_bv 64 (su - 48)) 8%nat = Some (word_to_le_bytes 8 (getr regs 20))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M56 : rdn RSEGS mem1 (Z_to_bv 64 (su - 56)) 8%nat = Some (word_to_le_bytes 8 (getr regs 21))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M64 : rdn RSEGS mem1 (Z_to_bv 64 (su - 64)) 8%nat = Some (word_to_le_bytes 8 (getr regs 22))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M72 : rdn RSEGS mem1 (Z_to_bv 64 (su - 72)) 8%nat = Some (word_to_le_bytes 8 can)) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M104 : rdn RSEGS mem1 (Z_to_bv 64 (su - 104)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M96 : rdn RSEGS mem1 (Z_to_bv 64 (su - 96)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (wp - wb)))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M88 : rdn RSEGS mem1 (Z_to_bv 64 (su - 88)) 8%nat = Some (word_to_le_bytes 8 s)) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M80 : rdn RSEGS mem1 (Z_to_bv 64 (su - 80)) 8%nat = Some (word_to_le_bytes 8 l)) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (Mcan : rdn RSEGS mem1 (Z_to_bv 64 0xe7ed0) 8%nat = Some (word_to_le_bytes 8 can)) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (Mbuf : rdn RSEGS mem1 (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp)) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (Mbsz : rdn RSEGS mem1 (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz)) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (Mfd : rdn RSEGS mem1 (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (Bp : rdn RSEGS mem1 (Z_to_bv 64 wb) (length pending) = Some pending).
{ subst mem1; unfold mem_sw1. repeat rdn_peel1. exact RDP. }
assert (Be : rdn RSEGS mem1 s (length extra) = Some extra).
{ subst mem1; unfold mem_sw1. repeat rdn_peel1. exact RDE. }
assert (HK' : forall regs' m,
getr regs' 10 = l -> getr regs' 2 = Z_to_bv 64 su -> getr regs' 1 = ret ->
getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 ->
getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 ->
getr regs' 27 = getr regs 27 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
LM su mem1 m ->
srealizes RSEGS scfg (mkCfg (mkst regs' ret (mem_sw2 m f bufp bufsz) (seg_rom RSEGS)) model) K).
{ intros. apply HK. all: try assumption.
eapply sw_post_of_LM; [exact SUlo | exact SUhi | exact Flo | exact Fhi | ].
match goal with H : LM _ _ _ |- _ => exact H end. }
pose proof (finish_nil scfg su f l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
(getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
(getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 model K
SUlo SUhi Flo Fhi Hh Hlazy Hret M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz HK') as FIN.
pose proof (loop1 scfg su f fd l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
(getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
(getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 model K
SUlo SUhi Flo Fhi FD Hfd Hh Hlazy Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK') as L1.
pose proof (loop2 scfg su f fd l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
(getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
(getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 model K
SUlo SUhi Flo Fhi FD Hfd Hh Hlazy Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK') as L2.
pose proof (LM_refl su mem1) as LM1.
destruct (Z.eq_dec wb wp) as [EQ|NEQ].
-
destruct pending as [|p0 pending']; [| cbn [length] in LENP; lia]. cbn [app].
subst wb.
destruct (sw_enter_eq regs mem (seg_rom RSEGS) su f wp fd s l bufp bufsz can ret)
as (regs1 & RUN1 & R17 & R10 & R11 & R12 & R2 & R8 & R9 & R18 & R19 & R21 & R22 & R3 & R4 & R23 & R24 & R25 & R26 & R27);
try assumption; try lia.
eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
lazymatch goal with |- srealizes _ _ (mkCfg (mkst _ _ ?M _) _) _ =>
replace M with mem1 by (subst mem1; rewrite Z.sub_diag; reflexivity) end.
rewrite Z.sub_diag in M96.
assert (RI1 : RI su f l (getr regs 3) (getr regs 4) (getr regs 23) (getr regs 24) (getr regs 25)
(getr regs 26) (getr regs 27) regs1).
{ unfold RI. repeat split; assumption. }
destruct extra as [|x0 extra'].
+
cbn [length] in HlZ. change (Z.of_nat 0) with 0%Z in HlZ. cbn [map].
eapply (rz_writev1_zeroX RSEGS scfg regs1 (0x9dcc0 : word) mem1 model (ltac:(oW' 0x9dcc0%Z)) fd (Z_to_bv 64 (su - 88)) s (t_emit [] K));
[ exact (ltac:(oF' 0x9dcc0%Z)) | exact (ltac:(oE' 0x9dcc0%Z)) | exact Hh | exact Hlazy | exact Hfd | exact FD
| exact R17 | exact R10 | exact R11 | exact R12 | exact M88 | | unfold TASK_SIZE; u_norm; lia | unfold TASK_SIZE; u_norm; lia | ].
{ u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rewrite <- HlZ. exact M80. }
rewrite pc_9dc74.
destruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 0)) mem1 (seg_rom RSEGS) 0)
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. rewrite R22. exact HlZ. }
{ lia. }
eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
apply FIN; [|exact LM1].
eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
+
eapply (rz_writev1_wallX RSEGS scfg regs1 (0x9dcc0 : word) mem1 model (ltac:(oW' 0x9dcc0%Z)) fd
(Z_to_bv 64 (su - 88)) s l (x0 :: extra') K);
[ exact (ltac:(oF' 0x9dcc0%Z)) | exact (ltac:(oE' 0x9dcc0%Z)) | exact Hh | exact Hlazy | exact Hfd | exact FD
| exact R17 | exact R10 | exact R11 | exact R12 | exact M88 | | | | | | | exact HKnil | ].
* u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. exact M80.
* unfold word_to_nat. rewrite LENE, Nat2Z.id. exact Be.
* unfold TASK_SIZE. u_norm. lia.
* unfold TASK_SIZE. u_norm. lia.
* cbn [length] in LENE. lia.
* lia.
* intros k K1 K2. rewrite pc_9dc74.
destruct (Nat.eq_dec k (length (x0 :: extra'))) as [EK|NK].
-- destruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. rewrite R22, HlZ. f_equal. lia. }
{ lia. }
eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
rewrite (proj1 (skipn_all_iff k (x0 :: extra'))) by lia. cbn [map].
apply FIN; [|exact LM1].
eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
-- destruct (sw_c1_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k)
(Z.of_nat (length (x0 :: extra'))))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. rewrite R22, HlZ. reflexivity. }
{ lia. }
{ lia. }
{ lia. }
eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
apply (L1 (length (x0 :: extra')) regs2 mem1 k s (x0 :: extra')); try lia.
++ eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
++ exact LM1.
++ exact P10.
++ rewrite P22. gres. rewrite R22, HlZ. reflexivity.
++ rewrite P18. gres. exact R18.
++ rewrite P19. gres. exact R19.
++ exact M88.
++ rewrite <- HlZ. exact M80.
++ exact Be.
-
destruct (sw_enter regs mem (seg_rom RSEGS) su f wb wp fd s l bufp bufsz can ret)
as (regs1 & RUN1 & R17 & R10 & R11 & R12 & R2 & R8 & R9 & R18 & R19 & R21 & R22 & R3 & R4 & R23 & R24 & R25 & R26 & R27);
try assumption; try lia.
eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1. fold mem1.
assert (RI1 : RI su f l (getr regs 3) (getr regs 4) (getr regs 23) (getr regs 24) (getr regs 25)
(getr regs 26) (getr regs 27) regs1).
{ unfold RI. repeat split; assumption. }
eapply (rz_writev2_wallX RSEGS scfg regs1 (0x9dcc0 : word) mem1 model (ltac:(oW' 0x9dcc0%Z)) fd
(Z_to_bv 64 (su - 104)) (Z_to_bv 64 wb) (Z_to_bv 64 (wp - wb)) s l pending extra K);
[ exact (ltac:(oF' 0x9dcc0%Z)) | exact (ltac:(oE' 0x9dcc0%Z)) | exact Hh | exact Hlazy | exact Hfd | exact FD
| exact R17 | exact R10 | exact R11 | exact R12 | exact M104 | | | | | | | | | | | exact HKnil | ].
+ u_norm. replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact M96.
+ u_norm. replace (su - 104 + 16)%Z with (su - 88)%Z by lia. exact M88.
+ u_norm. replace (su - 104 + 24)%Z with (su - 80)%Z by lia. exact M80.
+ rewrite word_to_nat_Z by lia. replace (Z.to_nat (wp - wb)) with (length pending) by lia. exact Bp.
+ unfold word_to_nat. rewrite LENE, Nat2Z.id. exact Be.
+ unfold TASK_SIZE. u_norm. lia.
+ unfold TASK_SIZE. u_norm. lia.
+ unfold TASK_SIZE. u_norm. lia.
+ u_norm. lia.
+ u_norm. lia.
+ intros k K1 K2. rewrite pc_9dc74. rewrite length_app in K2.
destruct (Nat.eq_dec k (length pending + length extra)) as [EK|NK].
* destruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. rewrite R22. f_equal. lia. }
{ lia. }
eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
rewrite (proj1 (skipn_all_iff k (pending ++ extra))) by (rewrite length_app; lia). cbn [map].
apply FIN; [|exact LM1].
eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
* destruct (sw_c1_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k)
(wp - wb + bv_unsigned l))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. exact R22. }
{ lia. }
{ lia. }
{ lia. }
eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
apply (L2 (length pending + length extra)%nat regs2 mem1 k (Z_to_bv 64 wb) pending s extra); try lia.
-- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
-- exact LM1.
-- exact P10.
-- rewrite P22. gres. rewrite R22. f_equal. lia.
-- rewrite P18. gres. exact R18.
-- rewrite P19. gres. exact R19.
-- exact M104.
-- replace (Z.of_nat (length pending)) with (wp - wb)%Z by lia. exact M96.
-- exact M88.
-- rewrite <- HlZ. exact M80.
-- exact Bp.
-- exact Be.
-- u_norm. lia.
-- u_norm. lia.
Qed.
End SE.
End FPX_2.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
