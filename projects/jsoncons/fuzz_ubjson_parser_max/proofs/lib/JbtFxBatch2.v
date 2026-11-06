(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac ArtFxTac JbtLeaf JbtAllocG JbtPoison JbtInitCache JbtPopulate1 ArtRuns ArtRunsMem JbtCls JbtFp JbtClsRep JbtClsGfa2 JbtClsRefill
JbtCellEx JbtCARSpec JbtAlloc3Pure JbtFxBatch1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtFxBatch2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtRuns."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.As0Tables.AsanTab."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtCARSpec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtCls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFxBatch2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtInitCache."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtLeaf."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtPoison."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0B"; "1app"; "1bool"; "1cons"; "1length"; "1list"; "1nil"; "1option"; "1true"; "2I"; "2and"; "2eq"; "2not"; "2or"; "3Z"; "0EVOK"]; ["0FP0"; "0GR"; "0HI"; "0L"; "4machine_state"; "5bvmap"; "0M"; "0M'"; "0MX"; "0Q"; "6apart"; "6cell"; "6wr"; "7aev"; "7aruns"; "8class_size"]; ["9ret_ok"; ":art_ca_cptr"; ":art_ca_events"; ":art_ca_pre"; ":art_cls_pop"; ";art_cls"; ";art_cls_mfa'"; ";art_cls_needs_populate"; ";art_cls_new"; ";art_cls_ok"; ";art_cls_refill"; ";art_cls_rep"; ";art_cptr_ok"; ";art_evok_list"; ";art_geo"; ";art_pc_hdr"]; [";art_prim_consts"; ";art_refill_fp"; ";cl_au"; ";cl_cache"; ";cl_free"; ";cl_mu"; "<art_agree"; "<art_out"; "=art_enq_new_fp"; "=art_enq_tail_W"; ">art_ic_size"; "?art_tsd"; "@art_layout"; "Agetr"; "Amkst"; "Bmem_grows"]; ["Cloaded_segments"; "DIn"; "Dlast"; "Eadd"; "Ele"; "Elt"; "Emul"; "Eof_nat"; "Epow"; "Esub"; "0b"; "0bytes"; "0c"; "0ca"; "0cl"; "0clp"]; ["0cnt"; "0ctx"; "0fx"; "0inited"; "0j"; "0key"; "0km"; "0l"; "0log"; "0logE"; "0m"; "0n"; "0qs"; "0qt"; "0r"; "0rP"]; ["0raw"; "0regs"; "0regs'"; "0ris"; "0rom"; "0sp"; "0spb"; "0st"; "FBV"; "FZ_to_bv"; "Fbv"; "Fbv_unsigned"; "0sv"; "0t"; "0tp"; "0tsd"]; ["0w"; "0wB"; "0x"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Definition art_enq_new_fp (sp t spb ris qs km b L B : Z) (x : Z) : Prop :=
(sp - 64 <= x < sp) \/ art_refill_fp (sp - 64) t spb ris qs 24 km x \/ (t + 208 + 2576 <= x < t + 208 + 2584)
\/ (b <= x < b + 32) \/ (L <> 0 /\ B <= x < B + 8) \/ (t + 80 <= x < t + 112 /\ (L <> 0 -> ~ (t + 88 <= x < t + 96))).
Definition art_enq_tail_W (t b L B : Z) : list (Z * Z) :=
[ (t + 208 + 1920, 4); (t + 208 + 2576, 8); (b, 32); ((if L =? 0 then t + 80 + 8 else B), 8); (t + 80, 8); (t + 96, 16) ].
Lemma art_class_size_24 : ltac2:(TCodec.tc2 tcn__JbtFxBatch2 "7';'>&O+H%211+XP0%63521"). Proof. reflexivity. Qed.
Lemma art_ic_size_24 : ltac2:(TCodec.tc2 tcn__JbtFxBatch2 "7';'>&QJ+H%211+XP0%63521"). Proof. reflexivity. Qed.
Section Spec.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_enq_finish := (ltac2:(TCodec.tc2 tcn__JbtFxBatch2 "`<'5'M%211'D!p021p041&Ey5'S:yR0%211%5241'7y8%611%311p061'>'Q5p02@&R3r?+R@%3221r@+V@%6221&R7&4&QCr4%211%42?1%611&R2r5%711z%43E21rA&R6+H&R8+2+Q0%3221%6251%K281+@r1%:221%O241&Q0rG%211&R4rF&R9+g0%2261%5241&R5rH+Q?%F2E1%4231';rE+RPP0rC%N221%53QF41+`PQoooPP0%B21A+Q5%Q12Q01%QH2G1%;3QLE1+TP0%QK2J1rK%J221%K242rL%R0216rM%O221%Q?294%F3R731&JrN%R72@=%342>91rO+Vb\P0%Q621K%743BL1&<%S31RA%R61N(6%11RD%Q43431%611&Q9rD%22R11':rJ%QF2R81+QO%R52R41%QC241%6241rI%QL2R>1%S028J+XP0%S2221+R0%R>2R=1%QL231%R32REMrQ1%R52RG1%R0225%C221%R82RJQ<%R32Q=8%F221%R03SA7RM%Q211rQ8%SA21RGrQ0%RO2RG1%SD231%R73SH>1&Q<&QB%11QG%33H17%R<3SM8R@%Q>11%Q5231%Q6281p0?1&QOrQ@rQ?%3221&S;%12T?S7%QO11%QI11rQBr2%211rQC%113%RN3TA31p071pW6TH1&Q?(8rQA%33RC21&Q;rQ;rQ:%36RE21T1Q4?&L&R0rQ>%342@1S0&KrQD+R`@%TN2RE1u8rQ3%6595321rQE+QWToH%95<215;rQFrQ2rQ9%=5@3291rQG%U:2:TErQ7%A5D32=1%SO3U@ITL%S111rQIrQ5%UA21TE%G5J31CNp051+8%T@2@1%QC2V1=%L5O82H1rQJ%TD2@TM&QMrQM(S8(9%23V;:1%5241%QM2V;1%Q65Q998Q21rQKrQH%TO21U?rQN+9%;3VD1:%>231%R62VD1%Q?5QB86Q;1rQL%U72MUDrQO+B%C3VL1B%F231%R>2VL1%QG5QJ76QC1+Q8%U?2L1rR0+C%K3W41J%N231%RF2W41%QO5R2O6QK1+Q@%UG2J1rR1+D%Q33W<1Q2%Q6231%RN2W<1%R75R:M6R31+QH%UO2I1rR2+E%Q;3WD1Q:%Q>231%S62WD1%R?5RBM6R;1%Q?3WHVDQ>%QB271&S9%V92QCT;%22WJ1%V23WJ41rR3+:%QG3X01QF%QJ231rQ=%92X11%V93X131rR4+;%QN3X71QM%R1231%V>3X616rR5+=%R33X<1R2%R6231%D2X<QN%VD3X<21rR6+>%R93XB1R8%R<231%VI3XA16rR7+?%R>3XG1R=%RA231%O2XGT;%VO3XG21%XJ1XK&R1(3+3%RF3XO1RE+4%RH3Y11RG+F%RJ3Y31RI+G%RL3Y51RK%RM3Y6X4RL+I%RO3Y81RN+J%S13Y:1S0+K%S33Y<1S2%V@1B%A3C21%B3D51%C3E81%D3F;1%E3G=1%F3H@1%G3IC1%H3JF1%J3KX<1rR:%SA21U3rR;%SC21U5%X03YH31p061pW6Q21%SG2U9R6%R52YMQ?%X53YM21r3+1%SJ3Z31SI%SM231rR8%X;3Z321%Q:3Q<RCD%Q;3Q=RL1%Q<3Q>S51%Q=3Q?S>1%Q>3Q@SG1%Q?3QAT11%Q@3QBQ<1%QA3QCQ?1%QC3QDY51r6%T:21ULrR@%T<21UN%XI3ZA31p061pUNQK1rR=%V<21Z1%T:1V8%X011&QG&QI%14Q6U7S;SC%V>2ZLV9%4221r8%11Q0rRA%11Q2%Y93ZL31p061p0<1pW6[41rR>%VM21I&QFrR?r7%33@21%VB3TOVA>rR9&Q4%11TGr9%VC6TKQL4ZA21r:%V=5V@1U@V9ZGr;%[:2U8UF%[;2S3X:%VA5VD32V=1r<%[>2U3ZB%VD5VG21V@QJr=%[A2UFZL%VG5VJ21VCR8r>%[D2BQO%VJ5VM2T@VF1%[F2T5ZJ%VL5VO[F1VHU:%[H2T0[3rR<%[J21XI%[K2R31%W15W4[H4VM1%Z?3\04[<rB%[O2SLV;%W55W821W1TKp041%ZD3\5QH[A%YF11%W95W<ZCQJW5TCp021rS0rRO&QNvRBrRIrRJ%453YG2ZK1%7261p091p0>1p0D1p0J1p0M1p0Q11p0Q51p0Q91p0Q>1p0QA1p0QG1p0QI1p0QN1p0R11p0RA1p0RD1p0S51p0S<1pQ@]41pV6]:1'Nv?vA+ZiS8%W:3]A1W9/01]A%Q05OSN1S@U0%77XA65Q0ROQ@1p091p0SK1p0TO1p0U61p0U<1p0UC1p0UI1p0V11p0V81p0VA1p0VJ1p0W31p0W<1p0WF1p0X11p0X61p0X>1p0XC1p0XH1p0XL1p0Y41p0Y91p0Y>1p0YC1p0Z01p0Z51p0ZG1p0ZK1p0[01p0[21p0[91p0[<1p0[=1p0[E1p0[I1p0\11p0\61p0\;1p0\>1p0\C1p0\E1p0\J1p0\O1p0]21p0]91p0]?1p0]F1tTF^L]J1tW2^M^81tU2^N^>1tTL^O^F1tTJ_0^J1pQ2^O1pU0_11pVJ_31pTH_41pW4_51p2_61pQ8_71pUH_81pUF_91pU>_:1pUJ_;1pV8_<1pV>_=1pUL_>1pVL_?1pQ6_@1pV<_A1pV2_I1pV:_D1pQB_E1pQ>_F1pV0_L1pV4_M1pUD`81pQD`51")) (only parsing).
Variable Q : ltac:(sec_ty2 constr:(SEC_T_art_enq_finish) 0%nat 0%nat).
Variable logE : ltac:(sec_ty2 constr:(SEC_T_art_enq_finish) 1%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_enq_finish) 2%nat 0%nat).
Variable rP : ltac:(sec_ty2 constr:(SEC_T_art_enq_finish) 3%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_enq_finish) 4%nat 0%nat).
Variable MX : ltac:(sec_ty2 constr:(SEC_T_art_enq_finish) 5%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_enq_finish) 6%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_enq_finish) 7%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_enq_finish) 8%nat 0%nat).
Variable HI : ltac:(sec_ty2 constr:(SEC_T_art_enq_finish) 9%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_enq_finish) 10%nat 0%nat).
Variable qt : ltac:(sec_ty2 constr:(SEC_T_art_enq_finish) 11%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_enq_finish) 12%nat 0%nat).
Variable ris : ltac:(sec_ty2 constr:(SEC_T_art_enq_finish) 13%nat 0%nat).
Variable qs : ltac:(sec_ty2 constr:(SEC_T_art_enq_finish) 14%nat 0%nat).
Variable km : ltac:(sec_ty2 constr:(SEC_T_art_enq_finish) 15%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_art_enq_finish) 16%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_enq_finish) 17%nat 0%nat).
Variable L : ltac:(sec_ty2 constr:(SEC_T_art_enq_finish) 18%nat 0%nat).
Variable B : ltac:(sec_ty2 constr:(SEC_T_art_enq_finish) 19%nat 0%nat).
Variable wB : ltac:(sec_ty2 constr:(SEC_T_art_enq_finish) 20%nat 0%nat).
Variable bytes : ltac:(sec_ty2 constr:(SEC_T_art_enq_finish) 21%nat 0%nat).
Variable sv : ltac:(sec_ty2 constr:(SEC_T_art_enq_finish) 22%nat 0%nat).
Variable clp : ltac:(sec_ty2 constr:(SEC_T_art_enq_finish) 23%nat 0%nat).
Variable FP0 : ltac:(sec_ty2 constr:(SEC_T_art_enq_finish) 24%nat 0%nat).
Lemma art_enq_finish : ltac:(sec_stmt2 constr:(SEC_T_art_enq_finish) 25%nat 0%nat).
Proof using Type Q logE regs rP M MX rom raw sp HI t qt spb ris qs km m n L B wB bytes sv clp FP0.
intros c ca cnt w b
Hret HHI Hsp' Espb Hspb Eris Hris Ht Ht' Et Atk Ati Hne OK HL HB0 Hby Hby' Hn Hm Hsv HB GX AX PH CR Wt Csv Cspb CL Cby CB
F1 F8 F9 F18 F19 F20 F21 P2 P10 P11 P13 P14 P15 KP K.
assert (Ec : c = t + 80) by reflexivity. assert (Eca : ca = t + 208) by reflexivity. assert (Eb : b = spb + 24 * 2 ^ 32 + 16 * w) by reflexivity.
clearbody c ca b.
pose proof Atk as Xk. unfold apart in Xk. pose proof Ati as Xi. unfold apart in Xi.
pose proof OK as (Hl16 & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _ & (Hmfa0 & Hmfa1) & Hnf4 & Hfor & _).
rewrite art_class_size_24 in Hfor.
assert (Hcnt : 1 <= cnt <= 16). { unfold cnt. destruct (cl_cache clp); [contradiction|]. cbn [length] in *. lia. }
assert (Hch : art_cptr_ok 8192 (cl_au clp) w).
{ apply (proj1 (Forall_forall _ _) Hfor). apply in_or_app. left. unfold w. rewrite (app_removelast_last 0 Hne) at 2. apply in_or_app. right. left. reflexivity. }
pose proof Hch as (Hw0 & Hw1 & _).
destruct CR as [[C0 CW] RR]. pose proof RR as (Rmx & Rnf & _ & _ & _ & _ & _ & Rna & _ & _ & _ & _ & Wu).
destruct (PH 24 ltac:(lia)) as [_ Pcsz]. cbn [andb] in Pcsz. rewrite art_ic_size_24 in Pcsz.
assert (HBf : L <> 0 -> 0 <= wB /\ 16 * wB + 8192 <= cl_au clp /\ (16 * wB + 8192 <= 16 * w \/ 16 * w + 8192 <= 16 * wB)).
{ intros NL. destruct (HB NL) as (_ & (Hb0 & Hb1 & (iB & EiB)) & Nw). destruct Hch as (_ & _ & (iw & Eiw)). repeat split; [exact Hb0|exact Hb1|]. clear - EiB Eiw Nw. lia. }
assert (Wc : wrA MX c 32) by (eapply wr_sub; [exact Wt|lia|lia]).
assert (Wb : wrA MX b 32) by (eapply wr_sub; [exact Wu|lia|lia]).
assert (RUN : msteps ASEGS (mkst rP (0x56468 : word) MX rom)
(mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd rP 1 raw) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 (U (getr regs 8)))) 9 (Z_to_bv 64 (U (getr regs 9)))) 11 (Z_to_bv 64 (bytes + (n + 8192)))) 12 (Z_to_bv 64 (L + 1))) 14 (Z_to_bv 64 (n + 8192))) 15 (Z_to_bv 64 L)) 16 (Z_to_bv 64 103079215104)) 18 (Z_to_bv 64 (U (getr regs 18)))) 19 (Z_to_bv 64 (U (getr regs 19)))) 20 (Z_to_bv 64 (U (getr regs 20)))) 21 (Z_to_bv 64 (U (getr regs 21))))
raw (art_enq_new_mem MX c ca L B bytes b m n cnt sv) rom)).
{ rewrite Eb.
apply (art_enq_new_tail_fn rP MX rom raw sp c ca spb L B bytes w m n cnt sv (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21)));
first [ assumption | apply u64_range | idtac ].
all: try (intros NL; destruct (HB NL) as (EB & _ & _); destruct (HBf NL) as (HB1 & HB2 & HB3)).
all: try (unfold apart; lia).
- rewrite Eca, Et. replace (4096 * qt + 208 + 2576) with ((512 * qt + 348) * 8) by lia. apply Z_mod_mult.
- eapply wr_sub; [exact Wt|lia|lia].
- eapply wr_sub; [exact Wt|lia|lia].
- rewrite <- Eb. exact Wb.
- eapply wr_sub; [exact Wu|lia|lia].
- unfold w. rewrite art_last_nth. replace (ca + 1936 + 4 * (cnt - 1)) with (ca + 80 * 24 + 16 + 4 * Z.of_nat (length (cl_cache clp) - 1)) by (unfold cnt; lia). apply CW. lia.
- replace (ca + 1928) with (ca + 80 * 24 + 8) by lia. exact Pcsz. }
eapply ar_steps; [exact RUN|]. apply ar_done. clear RUN.
set (a8 := if L =? 0 then t + 80 + 8 else B).
assert (Fa8 : (a8 = c + 8 /\ L = 0) \/ (a8 = B /\ L <> 0 /\ spb + 24 * 2 ^ 32 <= a8 /\ a8 + 8192 <= spb + 24 * 2 ^ 32 + cl_au clp /\ (a8 + 8192 <= b \/ b + 8192 <= a8))).
{ unfold a8. destruct (Z.eqb_spec L 0) as [EL|NL]; [left; split; [lia|exact EL]|right]. destruct (HB NL) as (EB & _ & _). destruct (HBf NL) as (HB1 & HB2 & HB3). repeat split; lia. }
assert (EM2 : art_enq_new_mem MX c ca L B bytes b m n cnt sv
= Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 4 MX (ca + 1920) (cnt - 1)) (ca + 2576) (sv + 8192)) b 0) (b + 8) (n + 8192)) (b + 16) 1) (b + 24) m) a8 b) c (L + 1)) (c + 16) b) (c + 24) (bytes + (n + 8192))).
{ unfold art_enq_new_mem, a8. rewrite Ec. reflexivity. }
rewrite EM2. clear EM2.
assert (EW : art_enq_tail_W t b L B = [ (t + 208 + 1920, 4); (t + 208 + 2576, 8); (b, 32); (a8, 8); (t + 80, 8); (t + 96, 16) ]) by reflexivity.
rewrite EW in K. clear EW. clearbody a8.
set (M2 := Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 4 MX (ca + 1920) (cnt - 1)) (ca + 2576) (sv + 8192)) b 0) (b + 8) (n + 8192)) (b + 16) 1) (b + 24) m) a8 b) c (L + 1)) (c + 16) b) (c + 24) (bytes + (n + 8192))).
assert (A2 : art_agree [ (t + 208 + 1920, 4); (t + 208 + 2576, 8); (b, 32); (a8, 8); (t + 80, 8); (t + 96, 16) ] MX M2).
{ unfold M2. eapply art_agree_sub; [zagree|]. intros z Hz Hout. cbn [art_out app fst snd] in Hout |- *. clear - Hout Ec Eca. repeat split; lia. }
assert (G2 : mem_grows MX M2) by (unfold M2; zgrows).
apply (K _ M2).
- gres. reflexivity.
- gres. reflexivity.
- intros r Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]; gres; first [apply Z_to_bv_bv_unsigned | apply KP; inl].
- eapply mem_grows_trans; [exact GX|exact G2].
- intros x N Hout. rewrite (A2 x Hout). apply AX. exact N.
- exact G2.
- exact A2.
-
apply (art_pc_hdr_tr _ ca true MX M2 ltac:(lia) ltac:(lia) A2); [|exact PH]. intros c' Hc'. revert Hc'; clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; intros Hc'. zarith_t.
-
split.
+ split.
* cbn [art_cls_pop cl_cache]. rewrite art_removelast_length by exact Hne.
replace (Z.of_nat (length (cl_cache clp) - 1)) with (cnt - 1) by (unfold cnt; lia). replace (ca + 80 * 24) with (ca + 1920) by lia. unfold M2.
do 9 (apply cell_Wn_other; [clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|lia|cbn; lia|unfold apart; clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|]).
apply cell_Wn_hit; [lia|cbn; lia].
* cbn [art_cls_pop cl_cache]. intros j Hj. rewrite art_removelast_length in Hj by exact Hne. rewrite art_removelast_nth by exact Hj.
apply (art_cell_tr1 _ MX M2 _ _ _ A2); [|apply CW; lia]. revert Hj Hl16; clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; intros Hj Hl16. zarith_t.
+ apply (art_region_rep_upd spb ris 24 0 0 clp (art_cls_pop clp) MX M2 [ (t + 208 + 1920, 4); (t + 208 + 2576, 8); (b, 32); (a8, 8); (t + 80, 8); (t + 96, 16) ]); try reflexivity;
first [ lia | exact RR | exact G2 | exact A2 | (intros; reflexivity) | idtac ].
* clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt. zarith_t.
* clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt. zarith_t.
* cbn [art_cls_pop cl_free]. clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt. zarith_t.
* apply (art_cell_tr1 _ MX M2 _ _ _ A2); [|exact Rmx]. clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt. zarith_t.
* apply (art_cell_tr1 _ MX M2 _ _ _ A2); [|exact Rnf]. clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt. zarith_t.
* apply (art_cell_tr1 _ MX M2 _ _ _ A2); [|exact Rna]. clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt. zarith_t.
- unfold M2; repeat first [ apply cell_Wn_hit; [clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia | clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia] | apply cell_Wn_other; [clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|unfold apart; clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|] ].
- unfold M2; repeat first [ apply cell_Wn_hit; [clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia | clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia] | apply cell_Wn_other; [clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|unfold apart; clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|] ].
- unfold M2; repeat first [ apply cell_Wn_hit; [clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia | clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia] | apply cell_Wn_other; [clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|unfold apart; clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|] ].
- unfold M2; repeat first [ apply cell_Wn_hit; [clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia | clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia] | apply cell_Wn_other; [clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|unfold apart; clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|] ].
- unfold M2; repeat first [ apply cell_Wn_hit; [clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia | clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia] | apply cell_Wn_other; [clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|unfold apart; clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|] ].
- unfold M2; repeat first [ apply cell_Wn_hit; [clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia | clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia] | apply cell_Wn_other; [clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|unfold apart; clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|] ].
- unfold M2; repeat first [ apply cell_Wn_hit; [clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia | clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia] | apply cell_Wn_other; [clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|unfold apart; clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|] ].
- intros EL. assert (E8 : a8 = c + 8) by (clear - EL Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia). rewrite <- E8. unfold M2; repeat first [ apply cell_Wn_hit; [clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia | clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia] | apply cell_Wn_other; [clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|unfold apart; clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|] ].
- intros NL. assert (E8 : a8 = B) by (clear - NL Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia). rewrite <- E8. unfold M2; repeat first [ apply cell_Wn_hit; [clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia | clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia] | apply cell_Wn_other; [clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; lia|clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|unfold apart; clear - Ec Eca Et Ht Ht' HHI Hsp' Xk Xi Espb Hspb Eris Hris Fa8 Hw0 Hw1 Haumu Hmu3 Hmfa1 Hnf4 Eb Hby Hby' HL Hn Hm Hsv Hcnt; cbn; lia|] ].
Qed.
End SE.
#[using="Type"] Lemma art_last_in : ltac2:(TCodec.tc2 tcn__JbtFxBatch2 "B'5'>%211&<';r1(6%116%43631%611&R1&R2r2z%33=21%53>13p071pU@?1").
Proof. intros l H. rewrite (app_removelast_last 0 H) at 2. apply in_or_app. right. left. reflexivity. Qed.
#[using="Type"] Lemma art_refill_au_mono : ltac2:(TCodec.tc2 tcn__JbtFxBatch2 "H'>'Q5':&R4+1r2%3221+N%5231%7231&Q9r3%2217&QB%113&Q:r4%2216%511%@251p081p0<1pTNE1pTJG1").
Proof.
intros c cl Hc OK. rewrite art_cls_refill_eq. cbn [art_cls_take cl_au]. unfold art_cls_pre_take. destruct (art_cls_needs_populate c cl); [|lia].
cbn [art_cls_populate cl_au]. destruct OK as (_ & (Hau0 & Haumu) & _). pose proof (art_class_size_facts c Hc) as (Hsz & _).
assert (0 <= art_cls_new c cl) by (unfold art_cls_new; apply Z.div_pos; lia). nia.
Qed.
Section SE.
Local Abbreviation SEC_T_art_refill_fp_out64 := (ltac2:(TCodec.tc2 tcn__JbtFxBatch2 "SE'>&R4r7&R9r8+g0%3221%6251&R5r9&R8+2+Q?%3221%6251';&R6+RPP0r5%3221%53DB1+`PQoooPP0%E21B&R3+Q5%?2>1%32A1%<3KG1+TP0%62D1r<%N221%O242r=%;216r>%Q3221&J%?2=:%244;61r?+QoonlP0%Q72E1%643?21r@+Vb\P0%Q;21M%:43CN1z%Q@21@+XPP0%Q321@+S`PPPP0%QD221'=':rE+R0%QG221%QJ21H%QD2I4%6221rC+V@%Q9221+R`@%Q;221%R221Q0+R`H%Q>251%QN2Q31%@241+R@%QB2;1%R921Q7+S@%QE2>1%R52Q:1%G241%R>2QNQ<%R82Q=Q3%J221%L241%M2<1%N2G1&<&QArF%RE21OrDrBrA+H%7854O321QAQE%911p0;1p0Q;1p0Q@1p0QC1p0QH1p0QM1p0R11p0R61p0R81p0R=1p0RC1p0RF1p0RM1p0S51pW6S=1pU>S>1pUJS?1pV8S@1pV>SA1pVLSB1pQ6SC1pV<SD1")) (only parsing).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_refill_fp_out64) 0%nat 0%nat).
Variable HI : ltac:(sec_ty2 constr:(SEC_T_art_refill_fp_out64) 1%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_refill_fp_out64) 2%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_refill_fp_out64) 3%nat 0%nat).
Variable ris : ltac:(sec_ty2 constr:(SEC_T_art_refill_fp_out64) 4%nat 0%nat).
Variable qs : ltac:(sec_ty2 constr:(SEC_T_art_refill_fp_out64) 5%nat 0%nat).
Variable km : ltac:(sec_ty2 constr:(SEC_T_art_refill_fp_out64) 6%nat 0%nat).
Variable x : ltac:(sec_ty2 constr:(SEC_T_art_refill_fp_out64) 7%nat 0%nat).
Lemma art_refill_fp_out64 : ltac:(sec_stmt2 constr:(SEC_T_art_refill_fp_out64) 8%nat 0%nat).
Proof using Type sp HI t spb ris qs km x.
intros HHI Hsp' Espb Hspb Eris Hris Ht Ht' Atk Ats Ati Hkm Hkm' Hx F.
unfold art_refill_fp in F. unfold apart in Atk, Ats, Ati.
destruct F as [F|[F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]]]; try lia. destruct F as (c' & Hc' & F). lia.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_enq_new_aruns := (ltac2:(TCodec.tc2 tcn__JbtFxBatch2 "_M'5'M%211'D!p021p041&Ey5'S:yR0%211%5241'7y8%611%311p061'>'2'Q5&R3rB+R@%3221rC+V@%6221r?&R6+H&R8+2+Q0%3221%6251%?281+@&Q1r3%22:1%<241%E261';&QMrK(S8+1(9%33Q921%6251rH%93Q921&Q0rI%211rM%;3QAI9%>221&S9%12QB6%B3QB31rN+4%B3QH1@%E231rF%82QI1%I3QI31rO+:%I3QO1G%L231r7%?2R01%Q03R031rQ0+;%Q03R61N%Q3231%Q53R516rQ1+<%Q53R;1Q3%Q8231%J2R;QO%Q;3R;21rQ2+=%Q;3RA1Q9%Q>231%Q@3R@16rQ3+>%Q@3RF1Q>%QC231%QE3RE1;&R4&R9+g0%22H1%42Q01&R5+Q?%R92R81%32H1&Q>rLrJ%38LQ1Q8Q?2R01QG&L&R0rQ6%?2E>%44321?rQ7+TP0%7462N1&Q@rQ8%23QJR01&QLrQ9%211&QKrQ:rQ4rQ5%463Q4Q9Q?21&Q?rQ;%23S:R11&Q;rDrQ<%362Q@QFS9R51&Q9rG%22S<1&<%T<1SJ&QC%11RK(6%11SN%S63531%711(8%S93T1Q81p031&QE%11S1+XPP0%SL21R2%S?3T831%>1Q?%SA3@1<&Q7%12T0SA%SD3T<1<':%;1QF%T=21:+S`PPPP0%R3221&Q6&R7&4&QD%11QN%32TH1%511&Q8%12T?R2%TI231%:2R41+`PPPP0%R@221rQB+QoooPP0+XP0%TH21R5%U1231+M%TI2TH1%TL2TK1%U5241+QPP0%TO21QM%U8231%R@4R?<13+^PPPP0%U;261+RPPPP0%RD4RC@21%Q3251%Q42C1%Q52Q11p0Q71p0Q;1&Q=v?rQC&Q2%13RIU>TO%53431z%S>21SN+QO%UB2UA1%S<2T11%QC241%SC26T8%V02T4RF%V121Q2+R0%UI2UH1%SC231%SI2<S:%SJ2=S4%SF2S54%QM221&KrQHu8%35SB2T@1S>rQI%V>2T<V5%65SE214S5%UJ3VCS;G%RK11rQA%VC21V5%V<2V4SB%VE221%V03VISA1&Q<&QB%11S?%33QK1SH&R1&1%S51SC%R;1SD%33W221%53W3SN1%S;11rQK%W32SJVC%K5T:21ISO%W52T0VE+oM%N5T=52L1%RM241%RN281%RO2@1%S02E1p0K1r2%VG21V:rQJ%V:2WK1%VK3WK31%VK2W0VFrQL%VN3WN21%X11X2r1(3+3%W03X61VN+8%W23X81W0+9%W43X:1W2+B%W63X<1W4+C%W83X>1W6+D%W:3X@1W8+E%W<3XB1W:+F%W>3XD1W<+G%W@3XF1W>%WA3XGX1W?+I%WC3XI1WA+J%WE3XK1WC+K%WG3XM1WE%TG1L%K3M21%L3N51%M3O81%N3Q0;1%O3Q1=1%Q03Q2@1%Q13Q3C1%Q23Q4F1%Q33Q5I1%Q43Q6L1%Q53Q7O1%Q63Q8Q21%Q73Q9WC1%Q83Q:Q61%R53Q;Q:1r6%X;21QErR2%X=21QG%X?3Y?31p061pUNQB1&QOrR0r4%3221&QHrQOrQMrQGrQFrQErQ@&S;%12YOQN%9:87S;654V@S331%V011%X31R:rR3%11R<%Y43YO31p051pW6Z61%VA3VEUOL&Q4&Q3rQ=%22YH1%411%VD6VFSFSIYJ1X?rQ>%62YL1%811%VD2YN1rQ?%:2Z01%SB11%YJ2Z23%SE3U=21%VE1K%YH3VG1VC%V72Z6SM%YJ3ZB1VB%X52THRK%X12RLU<%V8221r>rQN%Z>2UG1%ZG2UI1%ZH21UD%ZA2UCQ;%ZJ221%ZK21S>u1+WJ%TE5X4:321p0<1pU:[31p0A1p0D1r;%TK5X:1Q0TIU;r<%[62NS<%[72TMV8%TO5X>32TM1r=%[:2QHZJ%U25XA21U0ZA%[<2TJ[3%U45XCI1U2T;rQD%[?2T0ZE%U75XF[92U51r@%[B2R1[2%U:5XI21U8UNrA%[E2R5[<%[F2R8VG%[G2U:1%U?5XN43U=1%[33[LR;V0%[J2U@T0%UB5Y1[G1U@R;p031%[73\0Q8V4%X811%UF5Y5X?Q:UDR@p021rRCrRBrR6%V>31[KTE%U93\I31&QNvRBrErR>rR?%55432XK1%;271p0=1p0B1p0G1p0M1p0Q11p0Q51p0Q81p0Q<1p0QA1p0QD1p0R;1p0RA1p0RF1p0RM1p0RO1p0SA1p0SF1p0U:1p0U>1pQ@]41pV6]:1'NvA+ZiQ8%\<3]@1\:/01]@%Q15Q0SI1UDV5%67Z>WD5Q1SKRC1p081p0UN1p0VL1p0W01p0W51p0W91p0W;1p0WA1p0WC1p0WD1p0WK1p0X21p0Y@1p0YF1p0Z21p0Z61p0Z;1p0Z?1p0ZE1p0ZI1p0ZM1p0[11p0[71p0[<1p0[A1p0[G1p0[M1p0\31p0\:1p0\@1p0\H1p0]01p0]71p0];1tTF^>]F1tTL^?^61tTJ^@^:1pTN^?1pU8^A1pTH^C1pW4^D1p2^E1pQ8^F1pUH^G1pUF^H1pV@^I1pU>^J1pUJ^K1pV8^L1pV>^M1pW0^N1pU<^O1pVN_01pU4_11pVL_21pQ6_31pV<_41pV2_<1pV:_71pQ>_81pV4_>1pUB_I1pQD_F1")) (only parsing).
Variable Q : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_aruns) 0%nat 0%nat).
Variable log : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_aruns) 1%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_aruns) 2%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_aruns) 3%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_aruns) 4%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_aruns) 5%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_aruns) 6%nat 0%nat).
Variable HI : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_aruns) 7%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_aruns) 8%nat 0%nat).
Variable ctx : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_aruns) 9%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_aruns) 10%nat 0%nat).
Variable key : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_aruns) 11%nat 0%nat).
Variable tsd : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_aruns) 12%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_aruns) 13%nat 0%nat).
Variable ris : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_aruns) 14%nat 0%nat).
Variable qs : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_aruns) 15%nat 0%nat).
Variable km : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_aruns) 16%nat 0%nat).
Variable st : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_aruns) 17%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_aruns) 18%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_aruns) 19%nat 0%nat).
Variable L : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_aruns) 20%nat 0%nat).
Variable B : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_aruns) 21%nat 0%nat).
Variable wB : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_aruns) 22%nat 0%nat).
Variable bytes : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_aruns) 23%nat 0%nat).
Variable inited : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_aruns) 24%nat 0%nat).
Variable cl : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_aruns) 25%nat 0%nat).
Theorem art_enq_new_aruns : ltac:(sec_stmt2 constr:(SEC_T_art_enq_new_aruns) 26%nat 0%nat).
Proof using Type Q log regs M rom raw sp HI t ctx tp key tsd spb ris qs km st m n L B wB bytes inited cl.
intros c ca b
H1 Hret H2 H4 H10 H11 H12 H13 H14 HHI Hsp' GEO W Wt PC LY T PH RC OK Hin Emu Room EV HL HB0 Hby Hby' Hn Hm CL Cby HB K.
assert (Hc : 1 <= 24 <= 30) by lia.
pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & G11 & (qt & Et) & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22).
assert (At_i : apart t 4096 0x10000 (0x693000 - 0x10000)) by (unfold apart; clear - G9; lia).
assert (At_s : apart t 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; clear - G10; lia).
clear G9 G10 G15 G16.
pose proof OK as (Hl16 & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _ & (Hmfa0 & Hmfa1) & Hnf4 & Hfor & _). rewrite art_class_size_24 in Hfor.
assert (Hkm : 0 <= km) by lia.
assert (Ec : c = t + 80) by reflexivity. assert (Eca : ca = t + 208) by reflexivity. assert (Eb : b = spb + 24 * 2 ^ 32 + 16 * art_ca_cptr 24 cl) by reflexivity.
clearbody c ca b.
pose proof G11 as X11. unfold apart in X11. pose proof At_i as Xi. unfold apart in Xi. pose proof At_s as Xs. unfold apart in Xs.
assert (HBf : L <> 0 -> spb + 24 * 2 ^ 32 <= B /\ B + 8192 <= spb + 24 * 2 ^ 32 + cl_au cl).
{ intros NL. destruct (HB NL) as (EB & (Hb0 & Hb1 & _) & _). lia. }
destruct (art_enq_new_head regs M rom raw sp c L B H1 H2 H10 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HL ltac:(lia) ltac:(lia)
ltac:(unfold apart; lia) ltac:(intros NL; destruct (HBf NL); unfold apart; lia) ltac:(eapply wr_sub; [exact W|lia|lia]) CL
ltac:(intros NL; destruct (HB NL) as (_ & _ & _ & X1 & X2); split; assumption)) as (r1 & RUN1 & R1_2 & K1).
set (M1 := art_enq_frame M sp raw regs) in *.
assert (A1 : art_agree [(sp - 64, 64)] M M1). { unfold M1, art_enq_frame. eapply art_agree_sub; [zagree|]. zsub. }
assert (G1' : mem_grows M M1) by (unfold M1, art_enq_frame; zgrows).
assert (FC : cellA M1 (sp - 8) 8 (U raw) /\ cellA M1 (sp - 16) 8 (U (getr regs 8)) /\ cellA M1 (sp - 24) 8 (U (getr regs 9)) /\ cellA M1 (sp - 32) 8 (U (getr regs 18))
/\ cellA M1 (sp - 40) 8 (U (getr regs 19)) /\ cellA M1 (sp - 48) 8 (U (getr regs 20)) /\ cellA M1 (sp - 56) 8 (U (getr regs 21))).
{ unfold M1, art_enq_frame. repeat split; zcell. }
destruct FC as (FC1 & FC8 & FC9 & FC18 & FC19 & FC20 & FC21).
eapply ar_steps; [exact RUN1|].
destruct RC as [CR RR].
assert (PH1 : art_pc_hdr ca inited M1).
{ apply (art_pc_hdr_tr _ ca inited M M1 ltac:(lia) ltac:(lia) A1); [|exact PH]. intros c' Hc'. clear - Hc' Eca HHI G7 G8. zarith_t. }
assert (CR1 : art_cache_rep ca 24 (cl_cache cl) M1).
{ apply (art_cache_rep_tr _ ca 24 (cl_cache cl) M M1 ltac:(lia) ltac:(lia) ltac:(lia) Hl16 A1); [| |exact CR]; clear - Eca HHI G7 G8; zarith_t. }
assert (RR1 : art_region_rep spb ris 24 0 cl M1).
{ pose proof RR as (Rmx & Rnf & _ & _ & _ & _ & _ & Rna & _).
apply (art_region_rep_upd spb ris 24 0 0 cl cl M M1 [(sp - 64, 64)]); try reflexivity;
first [ lia | exact RR | exact G1' | exact A1 | (intros; reflexivity) | idtac ].
- clear - HHI Hsp' G1 G2 G6 Eris G4 Espb. zarith_t.
- clear - HHI Hsp' G1 G2 G6 Eris G4 Espb. zarith_t.
- clear - HHI Hsp' G1 G2 G6 Eris G4 Espb Hnf4 Hmfa1. zarith_t.
- apply (art_cell_tr1 _ M M1 _ _ _ A1); [|exact Rmx]. clear - HHI Hsp' G1 G2 G6 Eris G4 Espb. zarith_t.
- apply (art_cell_tr1 _ M M1 _ _ _ A1); [|exact Rnf]. clear - HHI Hsp' G1 G2 G6 Eris G4 Espb. zarith_t.
- apply (art_cell_tr1 _ M M1 _ _ _ A1); [|exact Rna]. clear - HHI Hsp' G1 G2 G6 Eris G4 Espb. zarith_t. }
assert (PC1 : art_prim_consts spb ris M1). { eapply art_prim_consts_fp; [exact A1| |exact PC]. intros z Hz. cbn. clear - Hz HHI G1. repeat split; lia. }
assert (Wt1 : wrA M1 t 4096) by (eapply wr_grows; [exact G1'|exact Wt]).
assert (TC1 : forall a v, t + 80 <= a -> a + 8 <= t + 112 -> cellA M a 8 v -> cellA M1 a 8 v).
{ intros a v Ha Ha' C. apply (art_cell_tr1 _ M M1 _ _ _ A1); [|exact C]. clear - Ha Ha' HHI Hsp' G7 G8. zarith_t. }
assert (CL1 : cellA M1 c 8 L) by (apply TC1; [lia|lia|exact CL]).
assert (Cby1 : cellA M1 (c + 24) 8 bytes) by (apply TC1; [lia|lia|exact Cby]).
assert (CB1 : L <> 0 -> cellA M1 (c + 16) 8 B) by (intros NL; destruct (HB NL) as (_ & _ & _ & X1 & _); apply TC1; [lia|lia|exact X1]).
assert (R1K : forall r : reg, In r [1; 3; 4; 8; 9; 10; 11; 12; 13; 14; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r1 r = getr regs r) by exact K1.
assert (Hcase : cl_cache cl = [] \/ cl_cache cl <> []) by (destruct (cl_cache cl); [left; reflexivity|right; discriminate]).
destruct Hcase as [Ecache|Hne].
2:{
assert (Epre : art_ca_pre 24 cl = cl) by (unfold art_ca_pre; destruct (cl_cache cl); [contradiction|reflexivity]).
assert (Eev : art_ca_events spb 24 cl = []) by (unfold art_ca_events; destruct (cl_cache cl); [contradiction|reflexivity]).
rewrite Eev in K. rewrite app_nil_r in K. unfold art_ca_cptr in Eb. rewrite Epre in K, Eb.
pose proof (Hin Hne) as ->.
set (cnt := Z.of_nat (length (cl_cache cl))).
assert (Hcnt : 1 <= cnt <= 16). { unfold cnt. destruct (cl_cache cl); [contradiction|]. cbn [length] in *. lia. }
destruct (art_tcell_exists M1 t 2784 At_i G7 ltac:(lia) ltac:(lia) ltac:(lia) Wt1) as (sv & Hsv & Csv).
pose proof CR1 as [C0 CW]. pose proof PC1 as (Pspb & _).
pose proof (art_enq_new_pop_fn r1 M1 rom ca cnt ltac:(rewrite R1K by inl; exact H11) ltac:(lia) ltac:(lia) Hcnt ltac:(replace (ca + 1920) with (ca + 80 * 24) by lia; exact C0)) as RUN2.
eapply ar_steps; [exact RUN2|]. subst c ca.
apply (art_enq_finish Q log regs (regupd r1 15 (Z_to_bv 64 cnt)) M M1 rom raw sp HI t qt spb ris qs km m n L B wB bytes sv cl (fun x => sp - 64 <= x < sp)
Hret HHI Hsp' Espb G4 Eris G6 G7 G8 Et G11 At_i Hne OK HL HB0 Hby Hby' Hn Hm Hsv).
+ intros NL. destruct (HB NL) as (EB & CPB & NIB & _). split; [exact EB|]. split; [exact CPB|]. intros E. apply NIB. apply in_or_app. left. rewrite E.
rewrite (app_removelast_last 0 Hne) at 2. apply in_or_app. right. left. reflexivity.
+ exact G1'.
+ intros x N. apply A1. cbn. split; [clear - N; lia|exact I].
+ exact PH1.
+ split; [exact CR1|exact RR1].
+ exact Wt1.
+ replace (t + 208 + 2576) with (t + 2784) by lia. exact Csv.
+ exact Pspb.
+ exact CL1.
+ exact Cby1.
+ exact CB1.
+ exact FC1.
+ exact FC8.
+ exact FC9.
+ exact FC18.
+ exact FC19.
+ exact FC20.
+ exact FC21.
+ gres. exact R1_2.
+ gres. rewrite R1K by inl. exact H10.
+ gres. rewrite R1K by inl. exact H11.
+ gres. rewrite R1K by inl. exact H13.
+ gres. rewrite R1K by inl. exact H14.
+ gres. reflexivity.
+ intros x Hx. cbn [In] in Hx. destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; gres; apply R1K; inl.
+ intros regs' M' S2 S1 SK SG SA SGX SAX SPH SCR B1 B2 B3 B4 L1 L2 L3 LE LN. rewrite <- Eb in *.
apply (K regs' M' S2 S1 SK SG); try assumption.
* intros x N. apply SA.
-- intros F. apply N. left. exact F.
-- unfold art_enq_tail_W. cbn [art_out fst snd]. unfold art_enq_new_fp, art_refill_fp in N.
repeat match goal with H : ~ (_ \/ _) |- _ => apply Decidable.not_or in H; destruct H end.
destruct (Z.eqb_spec L 0) as [EL|NL]; repeat split; lia.
* apply art_cls_ok_pop; assumption.
* unfold art_ca_cptr. rewrite ?Epre. apply (proj1 (Forall_forall _ _) Hfor). apply in_or_app. left. apply art_last_in. exact Hne.
* intros E. contradiction. }
assert (Epre : art_ca_pre 24 cl = art_cls_refill 24 cl) by (unfold art_ca_pre; rewrite Ecache; reflexivity).
assert (Eev : art_ca_events spb 24 cl = art_refill_events spb 24 cl) by (unfold art_ca_events; rewrite Ecache; reflexivity).
rewrite Eev in EV, K. unfold art_ca_cptr in Eb.
pose proof (art_ca_cptr_origin 24 cl Hc OK) as ORG. unfold art_ca_cptr in ORG. rewrite Epre in K, Eb, ORG.
pose proof CR1 as [C0 _]. rewrite Ecache in C0. cbn in C0.
pose proof (art_enq_new_ra_fn r1 M1 rom c ca st m n ltac:(rewrite R1K by inl; exact H10) ltac:(rewrite R1K by inl; exact H11) ltac:(rewrite R1K by inl; exact H12)
ltac:(rewrite R1K by inl; exact H13) ltac:(rewrite R1K by inl; exact H14) ltac:(lia) ltac:(lia)
ltac:(replace (ca + 1920) with (ca + 80 * 24) by lia; exact C0)) as RUN3.
match type of RUN3 with msteps _ _ (mkst ?R _ _ _) => set (r3 := R) in RUN3 end.
eapply ar_steps; [exact RUN3|].
assert (L1 : art_layout M1). { eapply art_layout_fp; [exact A1| |exact LY]. intros z Hz. cbn. clear - Hz HHI G1. repeat split; lia. }
assert (T1 : art_tsd M1 tp key tsd ctx t).
{ eapply art_tsd_fp; [exact A1| | |exact G19|exact G20|exact G21|exact G22|exact T].
- intros z Hz. cbn. clear - Hz HHI G1. repeat split; lia.
- intros z Hz. cbn. clear - Hz HHI G1 G13 G14. repeat split; lia. }
destruct (art_tcell_exists M1 t 2872 At_i G7 ltac:(lia) ltac:(lia) ltac:(lia) Wt1) as (m1 & _ & Cm1).
destruct (art_tcell_exists M1 t 2880 At_i G7 ltac:(lia) ltac:(lia) ltac:(lia) Wt1) as (m2 & _ & Cm2).
destruct (art_tcell_exists M1 t 2792 At_i G7 ltac:(lia) ltac:(lia) ltac:(lia) Wt1) as (sv0 & _ & Csv0).
apply (aruns_bind ASEGS EVOK GR (fun lg st => aruns ASEGS EVOK GR Q lg st) Q); [|intros lg st0 H; exact H].
apply (art_refill_rspec_holds EVOK GR (fun lg st => aruns ASEGS EVOK GR Q lg st) log r3 M1 rom (0x5657c : bv 64)%bv (sp - 64) HI t ctx tp key tsd spb ris qs 24 km inited cl
ltac:(unfold r3; gres; bveq) ltac:(unfold ret_ok; bveq) ltac:(unfold r3; gres; exact R1_2) ltac:(unfold r3; gres; rewrite R1K by inl; exact H4)
ltac:(unfold r3; gres; rewrite Eca; reflexivity) ltac:(unfold r3; gres; rewrite Eca; f_equal; lia) ltac:(unfold r3; gres; reflexivity) ltac:(unfold r3; gres; reflexivity)
Hc ltac:(lia) ltac:(lia) GEO ltac:(eapply wr_grows; [exact G1'|]; eapply wr_sub; [exact W|lia|lia]) Wt1 PC1 L1 T1
ltac:(rewrite <- Eca; exact PH1) ltac:(rewrite <- Eca; exact (conj CR1 RR1)) OK Ecache Emu
ltac:(exists m1, m2, sv0; repeat split; [exact Cm1|exact Cm2|replace (t + 208 + 2584) with (t + 2792) by lia; exact Csv0])
ltac:(intros NP; destruct (Room Ecache NP) as (Q1 & Q2 & Q3 & Q4); repeat split; first [assumption | eapply wr_grows; [exact G1'|assumption]]) EV).
intros rR MR R10 R2 R1 RK RG RA RPH RCR ROK RSH.
set (clr := art_cls_refill 24 cl) in *. set (nr := art_refill_n 24).
pose proof (art_pre_take_enough 24 cl Hc OK) as Hen. fold nr in Hen.
destruct (art_refill_need 24 Hc) as (_ & Hnr). fold nr in Hnr.
assert (Lc : length (cl_cache clr) = nr). { unfold clr. rewrite art_cls_refill_eq. fold nr. cbn [art_cls_take cl_cache]. rewrite length_skipn. lia. }
assert (Hne' : cl_cache clr <> []). { intros E. rewrite E in Lc. cbn in Lc. lia. }
pose proof RCR as [[D0 DW] DRR]. rewrite Lc in D0.
assert (WtR : wrA MR t 4096) by (eapply wr_grows; [exact RG|exact Wt1]).
assert (OUT : forall x, (sp - 64 <= x < sp) \/ (t + 208 + 2576 <= x < t + 208 + 2584) \/ (t + 80 <= x < t + 112) \/ (0x10000 <= x < 0x693000) -> ~ art_refill_fp (sp - 64) t spb ris qs 24 km x).
{ intros x Hx. exact (art_refill_fp_out64 sp HI t spb ris qs km x HHI Hsp' Espb G4 Eris G6 G7 G8 G11 At_s At_i Hkm ltac:(lia) Hx). }
assert (TR : forall a (k : nat) v, ((sp - 64 <= a /\ a + Z.of_nat k <= sp) \/ (t + 80 <= a /\ a + Z.of_nat k <= t + 112) \/ (0x10000 <= a /\ a + Z.of_nat k <= 0x693000)) ->
cellA M1 a k v -> cellA MR a k v).
{ intros a k v Ha C. apply (art_cell_agree _ M1 MR); [|clear - Ha HHI G1 G7; lia|clear - Ha Hsp' G7 G8 HHI; lia|exact C]. intros x Hx. apply RA. apply OUT. clear - Ha Hx. lia. }
pose proof (art_enq_new_rb_fn rR MR rom c ca st m n (Z.of_nat nr) R10
ltac:(rewrite RK by inl; unfold r3; gres; reflexivity) ltac:(rewrite RK by inl; unfold r3; gres; reflexivity) ltac:(rewrite RK by inl; unfold r3; gres; reflexivity)
ltac:(rewrite RK by inl; unfold r3; gres; reflexivity) ltac:(rewrite RK by inl; unfold r3; gres; reflexivity) ltac:(rewrite RK by inl; unfold r3; gres; reflexivity)
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(replace (ca + 1920) with (t + 208 + 80 * 24) by lia; exact D0)) as RUN4.
eapply ar_steps; [exact RUN4|].
destruct (art_tcell_exists MR t 2784 At_i G7 ltac:(lia) ltac:(lia) ltac:(lia) WtR) as (sv & Hsv & Csv).
pose proof ROK as (_ & (Hau0r & Haumur) & _ & _ & _ & Hmu3r & _ & (_ & Hmfa1r) & Hnf4r & Hforr & _). rewrite art_class_size_24 in Hforr.
pose proof (art_refill_au_mono 24 cl Hc OK) as Haum. fold clr in Haum.
replace (Z.of_nat nr) with (Z.of_nat (length (cl_cache clr))) by (rewrite Lc; reflexivity).
subst c ca.
apply (art_enq_finish Q (log ++ art_refill_events spb 24 cl) regs _ M MR rom raw sp HI t qt spb ris qs km m n L B wB bytes sv clr
(fun x => (sp - 64 <= x < sp) \/ art_refill_fp (sp - 64) t spb ris qs 24 km x)
Hret HHI Hsp' Espb G4 Eris G6 G7 G8 Et G11 At_i Hne' ROK HL HB0 Hby Hby' Hn Hm Hsv).
+ intros NL. destruct (HB NL) as (EB & CPB & NIB & _). split; [exact EB|]. split; [eapply art_cptr_mono; [exact Haum|exact CPB]|].
intros E. destruct ORG as [ORG|(_ & _ & ORG)]; [apply NIB; rewrite E; exact ORG|]. destruct CPB as (_ & CPB1 & _). rewrite <- E in ORG. clear - ORG CPB1. lia.
+ eapply mem_grows_trans; [exact G1'|exact RG].
+ intros x N. rewrite (RA x) by (intros F; apply N; right; exact F). apply A1. cbn. split; [|exact I]. intros F. apply N. left. clear - F. lia.
+ exact RPH.
+ exact RCR.
+ exact WtR.
+ replace (t + 208 + 2576) with (t + 2784) by lia. exact Csv.
+ pose proof PC1 as (Pspb & _). apply TR; [right; right; cbn; lia|exact Pspb].
+ apply TR; [right; left; cbn; lia|exact CL1].
+ apply TR; [right; left; cbn; lia|exact Cby1].
+ intros NL. apply TR; [right; left; cbn; lia|exact (CB1 NL)].
+ apply TR; [left; cbn; lia|exact FC1].
+ apply TR; [left; cbn; lia|exact FC8].
+ apply TR; [left; cbn; lia|exact FC9].
+ apply TR; [left; cbn; lia|exact FC18].
+ apply TR; [left; cbn; lia|exact FC19].
+ apply TR; [left; cbn; lia|exact FC20].
+ apply TR; [left; cbn; lia|exact FC21].
+ gres. exact R2.
+ gres. reflexivity.
+ gres. reflexivity.
+ gres. reflexivity.
+ gres. reflexivity.
+ gres. reflexivity.
+ intros x Hx. cbn [In] in Hx. destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; gres; rewrite RK by inl; unfold r3; gres; apply R1K; inl.
+ intros regs' M' S2 S1 SK SG SA SGX SAX SPH SCR B1 B2 B3 B4 L1' L2 L3 LE LN. rewrite <- Eb in *.
apply (K regs' M' S2 S1 SK SG); try assumption.
* intros x N. apply SA.
-- intros [F|F]; apply N; [left; exact F|right; left; exact F].
-- unfold art_enq_tail_W. cbn [art_out fst snd]. unfold art_enq_new_fp, art_refill_fp in N.
repeat match goal with H : ~ (_ \/ _) |- _ => apply Decidable.not_or in H; destruct H end.
destruct (Z.eqb_spec L 0) as [EL|NL]; repeat split; lia.
* apply art_cls_ok_pop; assumption.
* unfold art_ca_cptr. rewrite ?Epre. apply (proj1 (Forall_forall _ _) Hforr). apply in_or_app. left. apply art_last_in. exact Hne'.
* intros _ NP j Hj. pose proof (RSH NP j Hj) as C.
apply (art_cell_tr1 _ MR M' _ _ _ SAX); [|exact C].
assert (Fa8 : L = 0 \/ (spb + 24 * 2 ^ 32 <= B /\ B + 8192 <= spb + 24 * 2 ^ 32 + cl_au cl)) by (destruct (Z.eq_dec L 0) as [EL|NL]; [left; exact EL|right; exact (HBf NL)]).
assert (Hw : 0 <= last (cl_cache clr) 0 /\ 16 * last (cl_cache clr) 0 + 8192 <= cl_au clr).
{ pose proof (proj1 (Forall_forall _ _) Hforr (last (cl_cache clr) 0) ltac:(apply in_or_app; left; apply art_last_in; exact Hne')) as (X0 & X1 & _). split; assumption. }
unfold art_enq_tail_W. clear - Hj Xs X11 Fa8 Hw Eb G4 Espb Hkm Emu Hmu3 G6 Eris G2 G7 G8 HHI Hsp' Haumu Haumur Hmu3r Hau0.
destruct (Z.eqb_spec L 0) as [EL|NL]; zarith_t.
Qed.
End SE.
End Spec.
