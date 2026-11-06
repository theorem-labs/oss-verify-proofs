(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import StrFun.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TMemcpyU.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Tgt_F_memcpy () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.F_memcpy.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1None"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "2eq"; "2or"; "3Z"; "0F"; "4bvmap"; "5CB"]; ["5cell"; "6evt"; "7mkR"; "7munch"; "8MS"; "9bytes_at"; "9mem_inv"; "9wr_at"; ":rw_cells"; ";memcpy_post"; ";rsegs"; "<seg_rom"; "=add"; "=le"; "=to_nat"; "0a0"]; ["0a1"; "0a2"; "0a3"; "0a4"; "0a5"; "0a6"; "0a7"; "0fc"; "0gp"; "0junk"; "0m"; "0m'"; "0n"; "0ra"; "0s0"; "0s1"]; ["0s10"; "0s11"; "0s2"; "0s3"; "0s4"; "0s5"; "0s6"; "0s7"; "0s8"; "0s9"; "0sp"; "0src"; ">Z_to_bv"; ">bv"; ">bv_unsigned"; "0t0"]; ["0t1"; "0t2"; "0t3"; "0t4"; "0t5"; "0t6"; "0tp"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition rsegs := Ubsan.Ubsan_loaded_segments.
Definition memcpy_entry := 0xaa1b4%Z.
Definition memcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 a2 : word) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
/\ bytes_at rsegs m' (bv_unsigned a1) src.
Lemma mem_inv_munch_wr : ltac2:(TCodec.tc2 tcn__CJ_Tgt_F_memcpy "Q7'QMyR0%211'7y8%511%311p051'<&F&Jr4%3221&C(2'9%1288(8r3&Lr2%2231%54>>41(6%118%;3931r5%>321@&Gr6%24D1C<%F2E2p021p061p0F1pRJK1p2L1pRHN1pRFO1").
Proof.
intros m m' A n MI MU (HA & HB & WR) x b Hx.
destruct (Z_lt_dec (bv_unsigned x) A) as [L|L].
{ rewrite (MU x) in Hx by (cbn; lia). exact (MI _ _ Hx). }
destruct (Z_le_dec (A + n) (bv_unsigned x)) as [G|G].
{ rewrite (MU x) in Hx by (cbn; lia). exact (MI _ _ Hx). }
specialize (WR (bv_unsigned x - A)%Z ltac:(lia)).
replace (wa (A + (bv_unsigned x - A))) with x in WR.
2:{ unfold wa. apply bv_eq. rewrite Z_to_bv_unsigned. replace (A + (bv_unsigned x - A))%Z with (bv_unsigned x) by lia.
rewrite bv_wrap_small; [reflexivity | apply bv_unsigned_in_range]. }
destruct (m x) eqn:E; [exact (MI _ _ E) | exact (wview_not_ro _ _ _ WR E)].
Qed.
Lemma memcpy_spec : ltac2:(TCodec.tc2 tcn__CJ_Tgt_F_memcpy "TA'QMyR0%211&>y5%2213yQ0%711'7y8%:11%311p0:1'4%114&E&Jr3&QNrJ%22C1r2%746521':'5&3%12@9&N%118%63531&Hr5rM%?2Q01(2'@(?rK%D2Q51%<11%421G(6%117%93831%>4L=;1';&M&LrL%O2Q@1%32A1rN%Q22QC1%7231%7225%921F%;231&Fr7%22Q;1&A&IrQ9rQ8rQ7rQ6rQ2rQ1rHrGrFrErDrCrBrAr@r?r:r9rQ0rOr8%FGEDCBA@?>=<;:98765432Q0I1&D&BrQ5rQ4rQ3rIr>r=r<r;%9OQ0ONM876LK>=Q;QNQ>QIR;5JIHGFEDCBA4321&QL+eX]D%22S01(1%11S1&K%11RE%B78H5G3D1%Q;3RGD1p0Q=1p0QA1p0QN1p0R>1p0RF1pRDRO1pSHS01pRFS31pR@S91pLS<1pT<S@1pT:SA1pT8SB1pT6SC1pS4SD1pS2SE1pSDSF1pSBSG1pS@SH1pS>SI1pS<SJ1pS:SK1pS8SL1pS6SM1pR>SN1pR<SO1pR:T01pR8T11pR6T21pR4T31pR2T41pR0T51pS0T61pRNT71pT4T81pT2T91pT0T:1pT>T;1pRBT<1pSFT=1pRLT>1").
Proof.
intros until junk. intros SRC LEN DST SEP MI.
eapply evt_mono.
{ exact (TMemcpyU.memcpy_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m src junk SRC LEN DST SEP). }
intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & RW & BA).
exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
refine (conj E (conj MU (conj WM (conj _ (conj RW BA))))).
eapply mem_inv_munch_wr; [exact MI | exact MU |].
destruct DST as [_ W]. cbn [cells_size csize Nat.add] in W. rewrite Nat.add_0_r in W.
assert (EN : Z.of_nat (Z.to_nat (bv_unsigned a2)) = bv_unsigned a2) by (apply Z2Nat.id; apply bv_unsigned_in_range).
rewrite EN in W. exact W.
Qed.
End CEIL_WRAP_1.
