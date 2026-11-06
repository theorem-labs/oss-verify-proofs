(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import MemsetLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanMemset_codeKB0 AsanMemset1KB0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__AsanMemsetKB0 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanMemsetKB0."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanMemset_codeKB0."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.MemsetLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1option"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "3repeat"; "4Z"; "0Hn"; "0Hnw"; "0Hok"; "0Hret"; "5store_ok"; "6bvmap"; "7asanreflect_fx"]; ["7ms_entry"; "8ms_base"; "9wbytes"; ":msteps"; ";ret_ok"; "<cbyte"; "<ms_agree"; "=getr"; "=mkst"; ">keeps"; "?loaded_segments"; "@add"; "@le"; "@lt"; "@pow"; "@to_nat"]; ["0cv"; "0d"; "0mem0"; "0n"; "0nw"; "0regs"; "0regs'"; "0ret"; "0rom"; "ABV"; "AZ_to_bv"; "Abv"; "Abv_unsigned"]]).
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
#[local] Ltac solve_incl :=
let x := fresh "x" in let H := fresh "H" in
intros x H; cbn [In] in H;
repeat (destruct H as [<-|H]; [cbn [In]; repeat first [left; reflexivity | right] |]);
destruct H.
Section Summary.
Variable mem0 : word -> option byte.
Variables d cv ret : word.
Variable n : Z.
Variable rom : word -> option byte.
Hypothesis Hn : (0 <= n)%Z.
Hypothesis Hnw : (bv_unsigned d + n < 2 ^ 64)%Z.
Hypothesis Hok : store_ok MSEGS mem0 d (Z.to_nat n) = true.
Hypothesis Hret : ret_ok ret.
#[local] Abbreviation CF := (cfill mem0 d n (cbyte cv)).
#[local] Abbreviation PC o := (Z_to_bv 64 (ms_base + o)).
#[local] Ltac cover L' :=
apply (cfill_full_chain mem0 d n (cbyte cv) Hn Hnw _ L');
[ unfold L2, L6, L8, LB, LC, LD; solve_incl
| cbn [ms_chain]; lia ].
Theorem memset_summary : ltac2:(TCodec.tc2 tcn__AsanMemsetKB0 "R7&>y5'Q;yR0%211%5241'5&Gr1(Q9+:(3%33;21%6251vQ1%93;21r2+;%93A17%<231vQ0%?3A21r3+<%?3G1=%B231&Q:vQ3%22I1%G3I41r4+1%G3O1E%J231vQ7%M3O21'6'4'C&J&H&?r6&A%B2Q91vQ2vQ8%7565321&B&7y8%QA11&E%11Q1&O%11L%73531%93<Q;1%B5AQBH1<%E3D<1&F%12CQE%I2Q?1%J241qR>QK1%M2QL1p0O1p0Q61p0Q?1p0QF1pR<R11").
Proof.
intros regs H10 H11 H12 H1.
pose proof (u64_range d) as Hd.
rewrite <- (at_0 d) in H10.
replace (Z_to_bv 64 ms_base) with (PC 0) by (f_equal; lia).
replace (mkst regs (PC 0) mem0 rom) with (mkst regs (PC 0) (CF []) rom) by (rewrite cfill_nil; reflexivity).
assert (FIN : forall regs' (M : word -> option byte),
M = wbytes mem0 d (repeat (cbyte cv) (Z.to_nat n)) ->
msteps MSEGS (mkst regs (PC 0) (CF []) rom) (mkst regs' ret M rom) ->
getr regs' 10 = at_ d 0 -> ms_agree regs regs' ->
exists regs'',
msteps MSEGS (mkst regs (PC 0) (CF []) rom)
(mkst regs'' ret (wbytes mem0 d (repeat (cbyte cv) (Z.to_nat n))) rom)
/\ getr regs'' 10 = d /\ ms_agree regs regs'').
{ intros regs' M -> RUN P10 AG. exists regs'. rewrite at_0 in P10. auto. }
destruct (Z.lt_ge_cases n 9) as [Hsmall|Hn9].
{
destruct (Z.eq_dec n 0) as [Hz|Hnz].
{ destruct (A_exit0 mem0 d cv ret n rom Hn Hret regs H10 H11 H12 H1 Hz) as (r1 & RUN & P10 & AG).
eapply (FIN r1); try eassumption.
rewrite cfill_nil. rewrite Hz. reflexivity. }
destruct (Z.lt_ge_cases n 3) as [H3|H3].
{ destruct (A_exit2 mem0 d cv ret n rom Hn Hnw Hok Hret regs H10 H11 H12 H1 ltac:(lia)) as (r1 & RUN & P10 & AG).
eapply (FIN r1); try eassumption. cover ([(0,1); (n-1,1)]%Z). }
destruct (Z.lt_ge_cases n 7) as [H7|H7].
{ destruct (A_exit6 mem0 d cv ret n rom Hn Hnw Hok Hret regs H10 H11 H12 H1 ltac:(lia)) as (r1 & RUN & P10 & AG).
eapply (FIN r1); try eassumption. cover ([(0,1); (1,1); (2,1); (n-3,1); (n-2,1); (n-1,1)]%Z). }
destruct (A_exit8 mem0 d cv ret n rom Hn Hnw Hok Hret regs H10 H11 H12 H1 ltac:(lia)) as (r1 & RUN & P10 & AG).
eapply (FIN r1); try eassumption.
cover ([(0,1); (1,1); (2,1); (3,1); (n-4,1); (n-3,1); (n-2,1); (n-1,1)]%Z). }
destruct (A_cont mem0 d cv ret n rom Hn Hnw Hok regs H10 H11 H12 H1 Hn9)
as (r1 & RUN1 & Q10 & Q11 & Q12 & Q13 & Q15 & Q1 & AG1).
set (k := ((- bv_unsigned d) mod 4)%Z).
pose proof (neg_mod4_range (bv_unsigned d)) as Hk. fold k in Hk.
pose proof (negw_and3 d) as Hkv. fold k in Hkv.
set (n1 := (n - k - (n - k) mod 4)%Z).
set (m1 := ((n - k) / 4)%Z).
pose proof (Z.div_mod (n - k) 4 ltac:(lia)) as Hdm.
pose proof (Z.mod_pos_bound (n - k) 4 ltac:(lia)) as Hmb.
assert (Hm1 : (4 * m1 = n1)%Z) by (subst n1 m1; lia).
assert (Hn1 : (n - k - 3 <= n1 <= n - k)%Z) by (subst n1; lia).
pose proof (andi_m4 (n - k) ltac:(lia)) as Hn1v. fold n1 in Hn1v.
clearbody n1 m1. clear Hdm Hmb.
destruct (Z.lt_ge_cases n1 9) as [HB|HB].
{
destruct (B_exit mem0 d cv ret n rom Hnw Hok Hret k n1 Hk Hn1 Hkv Hn1v r1 Q10 Q11 Q12 Q13 Q15 Q1 Hn9 HB)
as (r2 & RUN2 & P10 & AG2).
eapply (FIN r2); [| eapply msteps_trans; [exact RUN1 | exact RUN2] | exact P10 | eapply ms_agree_trans; eassumption].
cover ([(0,1); (1,1); (2,1); (3,1); (k,4); (k+n1-4,4); (n-4,1); (n-3,1); (n-2,1); (n-1,1)]%Z). }
destruct (B_cont mem0 d cv ret n rom Hnw Hok k n1 Hk Hn1 Hkv Hn1v r1 Q10 Q11 Q12 Q13 Q15 Q1 Hn9 HB)
as (r2 & RUN2 & S10 & S11 & S12 & S13 & S14 & S1 & AG2).
destruct (Z.lt_ge_cases n1 25) as [HC|HC].
{ destruct (C_exit mem0 d cv ret n rom Hnw Hok Hret k n1 Hk Hn1 r2 S10 S11 S12 S13 S14 S1 Hn9 ltac:(lia) HC)
as (r3 & RUN3 & P10 & AG3).
eapply (FIN r3); [| eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]]
| exact P10 | repeat (eapply ms_agree_trans; [eassumption|]); first [assumption | apply ms_agree_refl]].
cover ([(0,1); (1,1); (2,1); (3,1); (k,4); (k+4,4); (k+8,4); (k+n1-12,4); (k+n1-8,4); (k+n1-4,4);
(n-4,1); (n-3,1); (n-2,1); (n-1,1)]%Z). }
destruct (C_cont mem0 d cv ret n rom Hnw Hok k n1 Hk Hn1 r2 S10 S11 S12 S13 S14 S1 Hn9 HC)
as (r3 & RUN3 & T10 & T11 & T12 & T13 & T14 & T1 & AG3).
destruct (andi_4_cases (at_ d k)) as (s4 & Hs4v & Hs4).
destruct (Z.lt_ge_cases (n1 - s4 - 24) 32) as [HD|HD].
{ destruct (D_exit mem0 d cv ret n rom Hnw Hok Hret k n1 Hk Hn1 s4 Hs4 Hs4v r3 T10 T11 T12 T13 T14 T1 Hn9 ltac:(lia) HD)
as (r4 & RUN4 & P10 & AG4).
eapply (FIN r4); [| eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 |
eapply msteps_trans; [exact RUN3 | exact RUN4]]]
| exact P10 | repeat (eapply ms_agree_trans; [eassumption|]); first [assumption | apply ms_agree_refl]].
cover ([(0,1); (1,1); (2,1); (3,1); (k,4); (k+4,4); (k+8,4); (k+12,4); (k+16,4); (k+20,4); (k+24,4);
(k+n1-28,4); (k+n1-24,4); (k+n1-20,4); (k+n1-16,4); (k+n1-12,4); (k+n1-8,4); (k+n1-4,4);
(n-4,1); (n-3,1); (n-2,1); (n-1,1)]%Z). }
destruct (D_cont mem0 d cv ret n rom Hnw Hok k n1 Hk Hn1 s4 Hs4 Hs4v r3 T10 T11 T12 T13 T14 T1 Hn9 ltac:(lia) HD)
as (r4 & RUN4 & U10 & U11 & U12 & U14 & U15 & U1 & AG4).
destruct (E_run mem0 d cv ret n rom k n1 s4 Hs4 r4 (LD n k n1 s4) U10 U11 U12 U14 U15 U1 Hn9 ltac:(lia))
as (r5 & RUN5 & V10 & V11 & V12 & V13 & V14 & V1 & AG5).
set (r := (n1 - s4 - 24)%Z) in *.
set (q := Z.to_nat (r / 32 - 1)).
assert (Hq : (32 * (Z.of_nat q + 1) <= r < 32 * (Z.of_nat q + 1) + 32)%Z).
{ subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
pose proof (Z.div_mod r 32 ltac:(lia)). pose proof (Z.mod_pos_bound r 32 ltac:(lia)). lia. }
destruct (loop_run mem0 d cv ret n rom Hnw Hok q r5 (LD n k n1 s4) (k + s4 + 24)%Z r
V10 V11 V12 V13 V14 V1 ltac:(lia) ltac:(lia) Hq)
as (r6 & RUN6 & W10 & W1 & AG6).
destruct (ret_run ret rom Hret r6 (CF (((k + s4 + 24)%Z, (32 * (Z.of_nat q + 1))%Z) :: LD n k n1 s4)) W1)
as (r7 & RUN7 & ->).
eapply (FIN r6); [| eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 |
eapply msteps_trans; [exact RUN3 | eapply msteps_trans; [exact RUN4 |
eapply msteps_trans; [exact RUN5 | eapply msteps_trans; [exact RUN6 | exact RUN7]]]]]]
| exact W10 | repeat (eapply ms_agree_trans; [eassumption|]); first [assumption | apply ms_agree_refl]].
cover ([(0,1); (1,1); (2,1); (3,1); (k,4); (k+4,4); (k+8,4); (k+12,4); (k+16,4); (k+20,4); (k+24,4);
(k+s4+24, 32 * (Z.of_nat q + 1));
(k+n1-28,4); (k+n1-24,4); (k+n1-20,4); (k+n1-16,4); (k+n1-12,4); (k+n1-8,4); (k+n1-4,4);
(n-4,1); (n-3,1); (n-2,1); (n-1,1)]%Z).
Qed.
End Summary.
Definition ms_entry : word := ltac:(let l := word_lit (Z_to_bv 64 ms_base) in exact l).
Lemma ms_entry_eq : ltac2:(TCodec.tc2 tcn__AsanMemsetKB0 "9'5'Q;yR0%211&Q:&A%2241&@%83521").
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Corollary memset_summary_lit : ltac2:(TCodec.tc2 tcn__AsanMemsetKB0 "S?'Q;yR0%211'1y8%511%311p051'8&Lzr2%3221&M&K&Q<r6%22@1r3%5221&N+2+R0%3221%;251'5'0&=&Jr8r7&Or4%211%746541(2%;3:21&D%11F&>y5%221Q7&Gr1(Q9+:(3%33721%6251r:%I3Q@21+;%83<16%;2Q:1%M3QD15+<%<3@1:%?2Q71&Q:r9%22QK1%Q43QK41+1%C3G1A%F2Q01r;%Q93R021'6'4'C&H&?+QTjo8%M3R81Kr@%554QK21:r=&Br?&7&Er>%211r<%QE11%63R@31%93<81%A5@Q<;1F%C3QL=1%R03RGQ9;&F%12R;Q@%H231%I251qR>QE1%L2QF1p0N1p0Q41p0Q<1p0QA1pR<QK1pJQO1pHR21pFR?1pDRL1pRBS21pR8S21pR@S91pR2S:1pR4S;1pR6S71").
Proof.
pose proof memset_summary as H. rewrite ms_entry_eq in H. exact H.
Qed.
Corollary memset_summary_w : ltac2:(TCodec.tc2 tcn__AsanMemsetKB0 "S='Q;yR0%211'1y8%511%311p051&>y5%2218&M&K&Q<r6%22>1r3%42@1%6231&N+2+R0%3221%<251'5'0&=&Jr8r7&Or4%C2O1%311%847651(2%<3;21&D%11H&G(Q9+:(3%33Q221%52=1r9%F3Q<21r5+;%93Q817%;231%K3QA16+<%=3Q<1;%?2Q81%O3QE1K+1%A3Q@1?%C2M1r:%Q43QJ21'6'4'C&H&?&@r?%453G219r1r<&Br>&7&Er=%211r;%R12R=1%QA11%73R;41%:3>91%B5A=<1G%D3QH?1%Q=2?Q9%QM3RC1=&F%12Q:B&I%12Q<D%L231%M261%N291qR>RC1%Q12RD1p0Q31p0Q91p0Q>1p0QD1p0QM1p0R01p0R>1pR<RL1pRBS01pR:S61pR@S71pR2S81pR4S91pR6S51").
Proof.
intros mem0 d cv ret nw rom regs Hnw Hok Hret H10 H11 H12 H1.
pose proof (u64_range nw) as Hr.
destruct (memset_summary mem0 d cv ret (bv_unsigned nw) rom ltac:(lia) Hnw Hok Hret regs H10 H11
ltac:(rewrite Z_to_bv_bv_unsigned; exact H12) H1) as (regs' & RUN & P10 & AG).
exists regs'. rewrite <- ms_entry_eq. repeat split; try assumption. apply ms_agree_keeps, AG.
Qed.
