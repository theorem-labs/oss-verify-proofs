(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac ITree Nodes.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Export Decode.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Lib_SysStep () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess."; "LinuxProcessSemantics.Riscv.Prelude."; "LinuxProcessSemantics.Riscv.Sem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Decode."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.ITree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1None"; "1Some"; "1bool"; "1cons"; "1false"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2I"; "2and"]; ["2eq"; "2not"; "2or"; "3sub"; "4le"; "5repeat"; "5skipn"; "6Z"; "0F"; "7Segment"; "8fetch_word"; "8is_ecall"; "8machine_state"; "8store_ok"; "8write_to_mem"; "8wview"]; ["9apply_unmaps"; "9apply_writes"; "9apply_zeros"; ":MemCopy"; ":errno_ret"; ":mkEffectU"; ";delivered_writes"; "<bvmap"; "<bvmap_set"; "=reg_get"; "0Q"; "0R"; ">CB"; ">cell"; ">cells_bytes"; ">cells_size"]; ["?errno_of"; "@evt"; "Ainside"; "Aivl"; "AmkR"; "Amunch"; "Astk"; "Awmono"; "Bnret"; "CMS"; "CMSsvc"; "Dbytes_at"; "Dmem_inv"; "Dro_addr"; "Dwa"; "Dwr_at"]; ["Ero_cells"; "Erw_cells"; "Fadd"; "Fle"; "Flt"; "Fof_nat"; "Fopp"; "Fpow"; "Fsub"; "Fto_nat"; "0W"; "0a"; "0bs"; "0ci"; "0cs"; "0e"]; ["0fc"; "0hi"; "0junk"; "0k"; "0lo"; "0m"; "0m'"; "0m0"; "0n"; "0pc"; "0r"; "0ro"; "0rv"; "0segs"; "GBV"; "GZ_to_bv"]; ["Gbv"; "Gbv_add"; "Gbv_swrap"; "Gbv_unsigned"; "0u"; "0us"; "0v"; "0w"; "0ws"; "0x"; "0x1"; "0x10"; "0x11"; "0x12"; "0x13"; "0x14"]; ["0x15"; "0x16"; "0x17"; "0x18"; "0x19"; "0x2"; "0x20"; "0x21"; "0x22"; "0x23"; "0x24"; "0x25"; "0x26"; "0x27"; "0x28"; "0x29"]; ["0x3"; "0x30"; "0x31"; "0x4"; "0x5"; "0x6"; "0x7"; "0x8"; "0x9"; "0z"; "0zs"]]).
Lemma evt_ecall : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "R;'7'I%211'L!p021&Q7y5'S0yR0%211%5241'GyQ0%611':%116y8%:11%411p0:1'@%718&Jr:&ROr6%22B1%5241(2r1%22A1%;3:41'3&Kr2%211(=%A3521r;&QJr9r8%B2Q21&Q9(RN+A(>%33Q921%52I1r7r5r4%=8M<:43K21%?11&QAr=r<&QI%Q22QBB%27EQ41B:Q29%63541p081p0I1p0Q01pV@QC1pUHQ>1pU<Q?1pUJQD1pU2QG1pUDQJ1pQBQL1pRHQM1pRFR41pULR81").
Proof.
intros segs Q R F pc fc rv m ro w Hf He HQ.
eapply evt_step; [|apply evt_done; exact HQ].
split; [reflexivity|]. rewrite (step_ecall_gen segs R F (Z_to_bv 64 pc) fc rv m ro w Hf He). reflexivity.
Qed.
Ltac step_ecall :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
lazymatch fw with
| Some ?w =>
apply (evt_ecall segs Q R F pc fc rv m ro w);
[ vm_compute; reflexivity | vm_compute; reflexivity | simp_regs ]
| None => fail "no instruction at" pc
end
end.
Lemma nret_MSsvc : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "RA&Q7y5'S0yR0%211%5241yQ0%511':%115y8%911%411p091'7'<%215%22=1%411%42??%611'8%72B1%911'@'L&QH&QJr=r<r;r:r9r8r7r6%9887654321(Q5r5r4r3r2(9'Q3%211r1%96876521%E2;1&QI&Q8(RN+:(>%33QD21%55QEQB1@J&S1&RO+4%22QG1%43QHM1&Q1&Q2&Q0%12MF%321H%521J%B7<Q57Q2Q11O%Q;3Q:D1pTLQ=1pV<QA1pXFQB1pVBQE1pUFR41pUHQL1pU<QM1pUJR21pU2R51pX@R91pUDR:1pQBR:1pRHR;1").
Proof. reflexivity. Qed.
Lemma mkR_set_a0 : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "RA'S0yR0%211'@&Q7y5%2214&Q8(RN+:(>%33621r1&QDrQ0rOrNrMrLrKrJrIrHrGrFrErDrCrBrAr@r?r>r=r<r;r:r9r8r7r6r5r4r3r2%Q0OONMLKJIHGFEDCBA@?>=<;:987654321%Q75Q9Q<Q3Q21%Q2OQ1Q0ONMLKJIQ3GFEDCBA@?>=<;:9876543%Q=3Q:21pV>Q?1pX6Q@1pX4QA1pX0QB1pWNQC1pWLQD1pWJQE1pWHQF1pWFQG1pWDQH1pWBQI1pW@QJ1pW>QK1pW:QL1pW8QM1pW6QN1pW4QO1pW2R01pW0R11pVNR21pVLR31pVJR41pVHR51pXBR61pX@R71pX>R81pX<R91pX:R:1pX8R;1pX2R<1pW<R=1pVFR>1").
Proof. reflexivity. Qed.
Lemma apply_mem_none : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "J'S0yR0%211':y8%511%311p051'@&Q1&Q2&Q0r1(9'<%12==%311%6251%8212'7%11?%72C1%911%>251%@3A1<pU<B1").
Proof. reflexivity. Qed.
Lemma apply_mem_write : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "Q4'S0yR0%211':y8%511%311p051'7%114'@&Q1&Q2&Q0r3(9'<%12??%311%6251%8212(4%62D=(;r2r1%34HA21%<15%73621%B291&N%13A76%F3I31pTJH1pTHQ01pU<L1").
Proof. reflexivity. Qed.
Lemma apply_mem_delivered : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "Q0'S0yR0%211':y8%511%311p051'7%114'@&Q1&Q2&Q0r3(9'<%12??%311%6251%8212&Q6r2r1%3221%>251&N%13=54%B3E31pTJD1pTHL1pU<H1").
Proof. intros m a [|b bs]; reflexivity. Qed.
Definition in_range (a n : Z) (x : word) : bool :=
(a <=? bv_unsigned x)%Z && (bv_unsigned x <? a + n)%Z.
Lemma apply_zeros_spec : forall m a n x, (0 <= a < 2^64)%Z -> (0 <= n < 2^64)%Z -> (a + n <= 2^64)%Z ->
apply_zeros m [(wa a, Z_to_bv 64 n)] x = if in_range a n x then Some (Z_to_bv 8 0) else m x.
Proof.
intros m a n x Ha Hn Han. cbn [apply_zeros zeros_cover existsb fst snd]. unfold in_range.
rewrite wa_unsigned by lia. rewrite unsigned_lit by lia. rewrite orb_false_r. reflexivity.
Qed.
Lemma apply_unmaps_spec : forall m a n x, (0 <= a < 2^64)%Z -> (0 <= n < 2^64)%Z -> (a + n <= 2^64)%Z ->
apply_unmaps m [(wa a, Z_to_bv 64 n)] x = if in_range a n x then None else m x.
Proof.
intros m a n x Ha Hn Han. cbn [apply_unmaps zeros_cover existsb fst snd]. unfold in_range.
rewrite wa_unsigned by lia. rewrite unsigned_lit by lia. rewrite orb_false_r. reflexivity.
Qed.
Section MemEffects.
Variable segs : list Segment.
Lemma rw_cells_CB_prefix_write : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "QE'S0yR0%211':y8%511%311p051'G'8'7%116&R1vRMr5r4(4'Q=(Q<r3r2%3221(9%116%83731%=4<;:1'D&6%12G8%321>&Nr7&QNr6%211%5341@%92OA%C21B&C%12I3&F%13Q45J%H231%K3J1D%L3K71%Q14Q0:<1p0A1p0F1pTJQ51pU6Q61pUBQ91p2Q;1pU<Q=1").
Proof.
intros m A n junk bs [[Hwf Hb] Hw] Hlen. cbn in Hwf. destruct Hwf as [Hj _].
cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
split; [split|].
- cbn. repeat split; try reflexivity. rewrite skipn_length. lia.
- cbn [cells_bytes cbytes]. rewrite app_nil_r.
pose proof (bytes_at_write_inside segs m A junk 0 bs Hb ltac:(lia) ltac:(cbn; lia)) as W.
rewrite Z.add_0_r in W. unfold upd_bytes in W. cbn [firstn app Nat.add] in W. exact W.
- cbn [cells_size csize]. cbn [cells_size csize] in Hw. replace (length bs + (n - length bs + 0))%nat with (n + 0)%nat by lia.
apply wr_at_write. exact Hw.
Qed.
Lemma rw_cells_CB_store_ok : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "Q='S0yR0%211':y8%511%311p051'G'8'7%116&R1vRMr5r4(4'Q=(Q<r3r2%3221(9%116%83731%=4<;:1'D%127<'@'3&Mr7&QNr6%211%54F41@(=%93821p0;1p0>1pU8O1pU6N1pUBQ11p2Q31pU<Q51").
Proof.
intros m A n junk k [_ Hw] Hk. cbn [cells_size csize] in Hw.
rewrite <- (Z.add_0_r A). apply (wr_at_store_ok segs m A (Z.of_nat (n + 0))); [exact Hw|lia|lia].
Qed.
Lemma mem_inv_syswrite : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "Q?'S0yR0%211':y8%511%311p051'G'8'7%116&QLvRMr5%3221&R1r6(4'Q=(Q<r4r3%3221(9%116%83731%;4>:=1'D&6%12I8%321A&Nr8&QNr7%211%5341@%J2I1p081p0=1p0J1pTJO1pU6Q01pUBQ31p2Q51pU<Q71").
Proof.
intros. apply mem_inv_store; [assumption|]. eapply rw_cells_CB_store_ok; eauto.
Qed.
Section Zeros.
Variables (m : word -> option byte) (a n : Z).
Hypothesis Ha : (0 <= a < 2^64)%Z.
Hypothesis Hn : (0 <= n < 2^64)%Z.
Hypothesis Han : (a + n <= 2^64)%Z.
Let m' := apply_zeros m [(wa a, Z_to_bv 64 n)].
Lemma zeros_outside : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "M'S0yR0%211'B&R4&S3r1%2261vR;%5221&R3&R2vRH%2251%4217%<261'@':y8%C11%311vRFr2%211vRE%113%:3631p0<1pVDJ1").
Proof.
intros x Hx. unfold m'. rewrite apply_zeros_spec by assumption. unfold in_range.
destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + n)); cbn [andb]; try reflexivity. lia.
Qed.
Lemma zeros_inside : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "Q0'S0yR0%211'?&R3vR;&S3r1%2271%5241&R4&R2vRH%2281%4261%<261'@':y8%C11%311vRFr2%211(2&ROz%2291%4291%=3961p0?1pVDM1").
Proof.
intros x Hx. unfold m'. rewrite apply_zeros_spec by assumption. unfold in_range.
destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + n)); cbn [andb]; try reflexivity; lia.
Qed.
Lemma wview_zeros_mono : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "I'S0yR0%211&A'@':y8%711%311&OvRMvREr1%43321(1%118%<3831%>11vRFr2%;3:21%A3=16%C11p061pVDF1").
Proof.
intros x Hx. unfold wview in *. unfold m'. rewrite apply_zeros_spec by assumption.
destruct (in_range a n x); [discriminate| exact Hx].
Qed.
Lemma bytes_at_zeros_other : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "Q2'G'7'S0y8%211%411&QKvRMvREr2r1%544321'B&R3&R2r3&R5&6%12>9%311%6251vR;%9221vRH%:231%<21:%>241vRFr4%G4F21>p041p0D1pTJK1p2Q11").
Proof.
intros A bs (H0 & H1 & H) Hd. split; [lia|]. split; [lia|]. intros i Hi.
unfold mrd. rewrite zeros_outside. { apply H. exact Hi. } rewrite wa_unsigned by lia. lia.
Qed.
Lemma wr_at_zeros : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "='G&QOvRMvREr2r1%544321vRFr3%847215p041pU8;1p2<1").
Proof. intros A k (H0 & H1 & H). split; [lia|]. split; [lia|]. intros i Hi. apply wview_zeros_mono, H, Hi. Qed.
Lemma rw_cells_zeros_other : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "Q0'G'7'Q=%211&R1vRMvREr2r1%544321'B&R3&R2r3&R5&Q?%119%311%6251vR;%9221vRH%:231%<21:%>241vRFr4%G4F21>p041p0D1pTNK1p2O1").
Proof.
intros A cs [[Hwf Hb] Hw] Hd. split; [split; [exact Hwf|]|].
- apply bytes_at_zeros_other; [exact Hb|]. rewrite cells_bytes_length by assumption. exact Hd.
- apply wr_at_zeros. exact Hw.
Qed.
Lemma ro_cells_zeros_other : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "Q0'G'7'Q=%211&R0vRMvREr2r1%544321'B&R3&R2r3&R5&Q?%119%311%6251vR;%9221vRH%:231%<21:%>241vRFr4%G4F21>p041p0D1pTNK1p2O1").
Proof.
intros A cs [Hwf Hb] Hd. split; [exact Hwf|].
apply bytes_at_zeros_other; [exact Hb|]. rewrite cells_bytes_length by assumption. exact Hd.
Qed.
Lemma stk_zeros : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "='G&QFvRMvREr2r1%544321vRFr3%847215p041pU4;1pU:<1").
Proof.
intros lo hi (H0 & H1 & H). split; [lia|]. split; [lia|]. intros x Hx.
destruct (H x Hx) as [Hw (b & Hb)]. split; [apply wview_zeros_mono; exact Hw|].
unfold mrd in *. unfold m'. rewrite apply_zeros_spec by assumption.
destruct (in_range a n (wa x)); [eexists; reflexivity|]. exists b. exact Hb.
Qed.
Lemma munch_zeros : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "L'7&QC%211'S0yR0%211':y8%511%311p051&QEr2r1vRE%43321&QBr3vR;vRH%43321r4vRF%<3261p041p0:1pU@@1pTFI1").
Proof.
intros W m0 H Hin x Hx. pose proof (bv_unsigned_in_range 64 x).
rewrite zeros_outside. { apply H. exact Hx. }
destruct (Z.ltb_spec0 (bv_unsigned x) a); [lia|].
destruct (Z.leb_spec0 (a + n) (bv_unsigned x)); [lia|].
exfalso. eapply (inside_not_outside W a n (bv_unsigned x) Hin); [lia| exact Hx].
Qed.
Lemma wmono_zeros : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "B'S0yR0%211':y8%511%311p051&QGvRMr1vRE%43321r2vRF%73621p041pU@:1").
Proof. intros m0 H x Hx. apply wview_zeros_mono, H, Hx. Qed.
Lemma mem_inv_zeros : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "Q1&QLvRMvRE%3221'S0yR0%211'?&R3vR;&S3r1%2271%5241&R4&R2vRH%2281%4261%<261'@'3&QMr2%22G1(5%63521p081pVDF1vRF%N2M1p031p0M1").
Proof.
intros Hinv Hro x b Hx. unfold m' in Hx. rewrite apply_zeros_spec in Hx by assumption.
unfold in_range in Hx.
destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + n)); cbn [andb] in Hx;
try exact (Hinv _ _ Hx).
apply Hro. lia.
Qed.
Lemma bytes_at_zeros_new : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "@&QKvRMvRFvR;&E'S0y8%211&ROz%2241&R9vRH%211%:3741%?4>=<1").
Proof.
split; [lia|]. rewrite repeat_length. split; [lia|]. intros i Hi.
unfold mrd. rewrite zeros_inside. 2:{ rewrite wa_unsigned by lia. lia. }
symmetry. apply nth_error_repeat. exact Hi.
Qed.
Lemma wr_at_zeros_new : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "6&QOvRMvRFvR;vRH%544321").
Proof.
split; [lia|]. split; [lia|]. intros i Hi. unfold wview. rewrite zeros_inside; [discriminate|].
rewrite wa_unsigned by lia. lia.
Qed.
Lemma rw_cells_zeros_new : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "G&R1vRMvRFvR;(4'Q=(Q<&R9vRH%211&E'S0y8%211&ROz%2241%73418%<291(9%11?%A3@31%F4EDC1").
Proof.
split; [split|].
- cbn. split; [apply repeat_length| exact I].
- cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_zeros_new.
- cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. apply wr_at_zeros_new.
Qed.
End Zeros.
Section Unmaps.
Variables (m : word -> option byte) (a n : Z).
Hypothesis Ha : (0 <= a < 2^64)%Z.
Hypothesis Hn : (0 <= n < 2^64)%Z.
Hypothesis Han : (a + n <= 2^64)%Z.
Let m' := apply_unmaps m [(wa a, Z_to_bv 64 n)].
Lemma unmaps_outside : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "M'S0yR0%211'B&R4&S3r1%2261vR;%5221&R3&R2vRH%2251%4217%<261'@':y8%C11%311vRFr2%211vRE%113%:3631p0<1pVDJ1").
Proof.
intros x Hx. unfold m'. rewrite apply_unmaps_spec by assumption. unfold in_range.
destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + n)); cbn [andb]; try reflexivity. lia.
Qed.
Lemma bytes_at_unmaps_other : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "Q2'G'7'S0y8%211%411&QKvRMvREr2r1%544321'B&R3&R2r3&R5&6%12>9%311%6251vR;%9221vRH%:231%<21:%>241vRFr4%G4F21>p041p0D1pTJK1p2Q11").
Proof.
intros A bs (H0 & H1 & H) Hd. split; [lia|]. split; [lia|]. intros i Hi.
unfold mrd. rewrite unmaps_outside. { apply H. exact Hi. } rewrite wa_unsigned by lia. lia.
Qed.
Lemma wr_at_unmaps_other : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "I'G&QOvRMvREr2r1%544321'B&R3&R2r3%2217vR;%5221vRH%6231%8216%:241vRFr4%C4B21:p041p0@1pU8G1p2H1").
Proof.
intros A k (H0 & H1 & H) Hd. split; [lia|]. split; [lia|]. intros i Hi.
unfold wview. rewrite unmaps_outside. { apply H. exact Hi. } rewrite wa_unsigned by lia. lia.
Qed.
Lemma rw_cells_unmaps_other : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "Q0'G'7'Q=%211&R1vRMvREr2r1%544321'B&R3&R2r3&R5&Q?%119%311%6251vR;%9221vRH%:231%<21:%>241vRFr4%G4F21>p041p0D1pTNK1p2O1").
Proof.
intros A cs [[Hwf Hb] Hw] Hd. split; [split; [exact Hwf|]|].
- apply bytes_at_unmaps_other; [exact Hb|]. rewrite cells_bytes_length by assumption. exact Hd.
- apply wr_at_unmaps_other; [exact Hw| exact Hd].
Qed.
Lemma ro_cells_unmaps_other : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "Q0'G'7'Q=%211&R0vRMvREr2r1%544321'B&R3&R2r3&R5&Q?%119%311%6251vR;%9221vRH%:231%<21:%>241vRFr4%G4F21>p041p0D1pTNK1p2O1").
Proof.
intros A cs [Hwf Hb] Hd. split; [exact Hwf|].
apply bytes_at_unmaps_other; [exact Hb|]. rewrite cells_bytes_length by assumption. exact Hd.
Qed.
Lemma stk_unmaps_other : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "H'G&QFvRMvREr2r1%544321'B&R3vR;%2261&R2vRH%2241r3%7221%9261vRFr4%B4A215p041p0?1pU4F1pU:G1").
Proof.
intros lo hi (H0 & H1 & H) Hd. split; [lia|]. split; [lia|]. intros x Hx.
destruct (H x Hx) as [Hw (b & Hb)].
assert (E : m' (wa x) = m (wa x)). { apply unmaps_outside. rewrite wa_unsigned by lia. lia. }
split. { unfold wview in *. rewrite E. exact Hw. } exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.
Lemma munch_unmaps : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "L'7&QC%211'S0yR0%211':y8%511%311p051&QEr2r1vRE%43321&QBr3vR;vRH%43321r4vRF%<3261p041p0:1pU@@1pTFI1").
Proof.
intros W m0 H Hin x Hx. pose proof (bv_unsigned_in_range 64 x).
rewrite unmaps_outside. { apply H. exact Hx. }
destruct (Z.ltb_spec0 (bv_unsigned x) a); [lia|].
destruct (Z.leb_spec0 (a + n) (bv_unsigned x)); [lia|].
exfalso. eapply (inside_not_outside W a n (bv_unsigned x) Hin); [lia| exact Hx].
Qed.
Lemma mem_inv_unmaps : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "7&QLvRMvRE%3221vRF%5241p031").
Proof.
intros Hinv x b Hx. unfold m' in Hx. rewrite apply_unmaps_spec in Hx by assumption.
destruct (in_range a n x); [discriminate|]. exact (Hinv _ _ Hx).
Qed.
End Unmaps.
End MemEffects.
Lemma rw_cells_wr_at : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "Q5'7'I%211'S0yR0%211':y8%511%311p051'G'Q=%=11&R1r5r4r3r2%544321&R3&R5&Q?%116%311%5271&QOr7r6%3421><p051p0<1pUBE1pTND1p2G1pU<I1pULQ21").
Proof. intros segs m A cs n [_ (H0 & H1 & H)] Hn. split; [lia|]. split; [lia|]. intros i Hi. apply H. lia. Qed.
Lemma rw_cells_bytes_at : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "N'7'I%211'S0yR0%211':y8%511%311p051'G'Q=%=11&R1r4r3r2r1%544321&QKr5&Q>%116%443981p061pTN=1p2@1pU<B1pULK1").
Proof. intros segs m A cs [[_ H] _]. exact H. Qed.
Lemma ro_cells_bytes_at : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "N'7'I%211'S0yR0%211':y8%511%311p051'G'Q=%=11&R0r4r3r2r1%544321&QKr5&Q>%116%443981p061pTN=1p2@1pU<B1pULK1").
Proof. intros segs m A cs [_ H]. exact H. Qed.
Ltac at_node_solve :=
at_node_red; split_spine;
first [ reflexivity | lia | assumption
| symmetry; apply Z_to_bv_bv_unsigned
| lazymatch goal with
| |- wr_at ?segs ?m ?A ?n =>
match goal with H : rw_cells segs m A ?cs |- _ =>
apply (rw_cells_wr_at segs m A cs n H); cbn [cells_size csize]; lia end
| |- bytes_at ?segs ?m ?A ?bs =>
match goal with
| H : rw_cells segs m A ?cs |- _ =>
apply (bytes_at_ext segs m A _ bs (rw_cells_bytes_at segs m A cs H));
cbn [cells_bytes cbytes]; rewrite ?app_nil_r; reflexivity
| H : ro_cells segs m A ?cs |- _ =>
apply (bytes_at_ext segs m A _ bs (ro_cells_bytes_at segs m A cs H));
cbn [cells_bytes cbytes]; rewrite ?app_nil_r; reflexivity
end
end
| idtac ].
Ltac sys_mem_write :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (Z_to_bv 64 ?B) ?bs) ?ro) =>
change (write_to_mem m (Z_to_bv 64 B) bs) with (write_to_mem m (wa B) bs);
lazymatch goal with
| H : rw_cells segs m B [CB ?n ?junk] |- _ =>
let HB := fresh "HB" in
pose proof (rw_cells_bound segs m B _ H) as HB; cbn [cells_size csize Nat.add] in HB;
(try lazymatch goal with
| HI : mem_inv segs m |- _ =>
let HI' := fresh "MI" in
pose proof (mem_inv_syswrite segs m B n junk bs HI H ltac:(lia)) as HI'; clear HI; rename HI' into HI
end);
let H' := fresh "DST" in
pose proof (rw_cells_CB_prefix_write segs m B n junk bs H ltac:(lia)) as H';
clear H;
transport_chunks segs m B bs;
footprint_after_store segs m B bs;
let m' := fresh "m" in
remember (write_to_mem m (wa B) bs) as m' eqn:Heqm;
clear Heqm; clear HB; try clear m; rename H' into H
| _ => fail "sys_mem_write: no hypothesis rw_cells" segs m B "[CB _ _]"
end
end.
Lemma apply_mem_zeros : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "O'S0yR0%211':y8%511%311p051'<%1277'@&Q1&Q2&Q0r2(9%117%4231(4r1%23;14%9241'7%11B%@2F1%:11%?251%?2=7%B3E21pXDD1pU<G1").
Proof. reflexivity. Qed.
Lemma apply_mem_unmaps : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "N'S0yR0%211':y8%511%311p051'<%1277'@&Q1&Q2&Q0r2(4r1(9%119%43:31%7261%9213'7%11B%@2F1%811%?251%A3D17pV:C1pU<F1").
Proof. reflexivity. Qed.
Ltac transport_zeros segs m a n Ha Hn Han :=
repeat match goal with
| H : bytes_at segs m ?A2 ?bs2 |- _ =>
first [ apply (bytes_at_zeros_other segs m a n Ha Hn Han A2 bs2 H) in H; [|simpl_sizes; slia]
| idtac "note: dropping hypothesis (not provably disjoint from zero-fill):" H; clear H ]
| H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_zeros segs m a n Ha Hn Han A2 n2) in H
| H : rw_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (rw_cells_zeros_other segs m a n Ha Hn Han A2 cs2 H) in H; [|simpl_sizes; slia]
| idtac "note: dropping hypothesis (not provably disjoint from zero-fill):" H; clear H ]
| H : ro_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (ro_cells_zeros_other segs m a n Ha Hn Han A2 cs2 H) in H; [|simpl_sizes; slia]
| idtac "note: dropping hypothesis (not provably disjoint from zero-fill):" H; clear H ]
| H : stk segs m ?lo ?hi |- _ => apply (stk_zeros segs m a n Ha Hn Han lo hi) in H
| H : munch ?W ?m0 m |- _ =>
first [ apply (munch_zeros segs m a n Ha Hn Han W m0 H) in H; [|cbn [inside]; slia]
| fail 100 "zero-filled range not inside the declared footprint" ]
| H : wmono segs ?m0 m |- _ => apply (wmono_zeros segs m a n Ha Hn Han m0) in H
| H : mem_inv segs m |- _ =>
let H' := fresh "MI" in
assert (H' : mem_inv segs (apply_zeros m [(wa a, Z_to_bv 64 n)]))
by (apply (mem_inv_zeros segs m a n Ha Hn Han H); first [assumption | intros; shelve]);
clear H
end.
Ltac sys_mem_zeros :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (apply_zeros ?m [(?A, Z_to_bv 64 ?n)]) ?ro) =>
let a := lazymatch A with wa ?a => a | Z_to_bv 64 ?a => a end in
change (apply_zeros m [(A, Z_to_bv 64 n)]) with (apply_zeros m [(wa a, Z_to_bv 64 n)]);
let Ha := fresh "Hza" in let Hn := fresh "Hzn" in let Han := fresh "Hzan" in
assert (Ha : (0 <= a < 2^64)%Z) by lia;
assert (Hn : (0 <= n < 2^64)%Z) by lia;
assert (Han : (a + n <= 2^64)%Z) by lia;
transport_zeros segs m a n Ha Hn Han;
let Z' := fresh "ZNEW" in
pose proof (rw_cells_zeros_new segs m a n Ha Hn Han) as Z';
let m' := fresh "m" in
remember (apply_zeros m [(wa a, Z_to_bv 64 n)]) as m' eqn:Heqm;
clear Heqm Ha Hn Han; try clear m
end.
Ltac transport_unmaps segs m a n Ha Hn Han :=
repeat match goal with
| H : bytes_at segs m ?A2 ?bs2 |- _ =>
first [ apply (bytes_at_unmaps_other segs m a n Ha Hn Han A2 bs2 H) in H; [|simpl_sizes; slia]
| idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
| H : wr_at segs m ?A2 ?n2 |- _ =>
first [ apply (wr_at_unmaps_other segs m a n Ha Hn Han A2 n2 H) in H; [|slia]
| idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
| H : rw_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (rw_cells_unmaps_other segs m a n Ha Hn Han A2 cs2 H) in H; [|simpl_sizes; slia]
| idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
| H : ro_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (ro_cells_unmaps_other segs m a n Ha Hn Han A2 cs2 H) in H; [|simpl_sizes; slia]
| idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
| H : stk segs m ?lo ?hi |- _ =>
first [ apply (stk_unmaps_other segs m a n Ha Hn Han lo hi H) in H; [|slia]
| idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
| H : munch ?W ?m0 m |- _ =>
first [ apply (munch_unmaps m a n Ha Hn Han W m0 H) in H; [|cbn [inside]; slia]
| fail 100 "unmapped range not inside the declared footprint" ]
| H : wmono segs ?m0 m |- _ => idtac "note: dropping wmono (not preserved by an unmap):" H; clear H
| H : mem_inv segs m |- _ => apply (mem_inv_unmaps segs m a n Ha Hn Han) in H
end.
Ltac sys_mem_unmaps :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (apply_unmaps ?m [(?A, Z_to_bv 64 ?n)]) ?ro) =>
let a := lazymatch A with wa ?a => a | Z_to_bv 64 ?a => a end in
change (apply_unmaps m [(A, Z_to_bv 64 n)]) with (apply_unmaps m [(wa a, Z_to_bv 64 n)]);
let Ha := fresh "Hua" in let Hn := fresh "Hun" in let Han := fresh "Huan" in
assert (Ha : (0 <= a < 2^64)%Z) by lia;
assert (Hn : (0 <= n < 2^64)%Z) by lia;
assert (Han : (a + n <= 2^64)%Z) by lia;
transport_unmaps segs m a n Ha Hn Han;
let m' := fresh "m" in
remember (apply_unmaps m [(wa a, Z_to_bv 64 n)]) as m' eqn:Heqm;
clear Heqm Ha Hn Han; try clear m
end.
Ltac sys_nret :=
rewrite nret_MSsvc; rewrite ?mkR_set_a0; simp_regs;
(lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
let p' := eval vm_compute in (p + 4)%Z in
replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity)
| _ => idtac
end);
first [ rewrite apply_mem_none
| rewrite apply_mem_delivered; sys_mem_write
| rewrite apply_mem_write; sys_mem_write
| rewrite apply_mem_zeros; sys_mem_zeros
| rewrite apply_mem_unmaps; sys_mem_unmaps
| idtac ].
Notation errno_addr tp := (bv_unsigned tp + (-164))%Z (only parsing).
Definition sysret_val (r : word) : word :=
match errno_of r with Some _ => Z_to_bv 64 (-1) | None => r end.
Definition sysret_errno (r errv : word) : word :=
match errno_of r with Some e => Z_to_bv 64 e | None => errv end.
Lemma errno_of_big : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "M'S0yR0%211&R4&R8&R7+2+R0%3221+TP0%6221&S3r1%22<1%;241'@':'G%211&Q@r2%211(2%<2F3%D2@1%3281%;3851p0=1pUFJ1").
Proof. intros r H. unfold errno_of. destruct (Z.leb_spec0 (2^64 - 4095) (bv_unsigned r)); [reflexivity|lia]. Qed.
Lemma negw_errno : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "I'G'?&R4&R8&R7+2+R0%3221+TP0%6221r1%9221%:225%<221'@&S2yQ0zr2%@221%5241%B2>3%83F21p0:1pV:H1").
Proof.
intros u Hu. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
replace (0 - u + 2^31)%Z with ((2^64 - u + 2^31) + (- 2^32) * 2^32)%Z by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma swrap32_small : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "F'G'?&R3&R6&R7+2+O%3221%511r1%8221&R4%1235%<231'@&S2yQ0r2%3221%53C12p071pXDE1").
Proof.
intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
rewrite Z.mod_small by lia. lia.
Qed.
Lemma swrap32_high : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "I'G'?&R3&R8&R7+2+R0%3221+O%5241%7231r1%:221&R4%1237%>231'@&S2yQ0r2%3221%B22>%63F21p081pV:H1").
Proof.
intros u Hu. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
replace (u + 2^31)%Z with ((u - 2^64 + 2^31) + 2^32 * 2^32)%Z by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma unsigned_errno_ret : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "I'G'?&R3+1r1%3221+SoO%5231%7231'@&S3yR0&Q4r2%211%5241&R8&R7+2+R0%3221%5218%=3F71p0?1pU0H1").
Proof. intros. rewrite errno_ret_unsigned by lia. reflexivity. Qed.
Lemma Z_to_bv_minus_mod : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "A'G'@'S0yR0%211&RO&R8r1&R7+2+R0%3221%6251%82:1%92;7%>3;21pXD@1").
Proof.
intros. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with (2^64)%Z.
replace (z - 2^64)%Z with (z + (-1) * 2^64)%Z by lia. apply Z.mod_add. lia.
Qed.
Lemma errno_ret_fold : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep ">'G'@'S0yR0%211&RO&R6r1%211%4261&Q4%114%;3831pU0=1").
Proof. reflexivity. Qed.
Lemma sextw_errno : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "Q0'G'?&R3+1r1%3221&R7+2+O%3221%8261%:261'@'S0yR0%211&RO&S2yQ0&R2&S3&Q4r2%211%42:1z%7221%:291%<2>1%A3>16p0C1pU0O1").
Proof.
intros e He. unfold errno_ret. rewrite unsigned_lit_wrap.
replace ((- e) mod 2^64)%Z with (2^64 - e)%Z.
2:{ replace (-e)%Z with ((2^64 - e) + (-1) * 2^64)%Z by lia. rewrite Z.mod_add; [|lia]. rewrite Z.mod_small; [reflexivity|lia]. }
rewrite Z.add_0_r, swrap32_high by lia. f_equal. lia.
Qed.
Lemma sextw_small : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "O'G'?&R3zr1%3221&R4&R7+2+O%3221%5271%;271'@'S0yR0%211&RO&S2yQ0&R2&S3r2%6281%3291%521F%8271%:2<1%?3<15p0A1pXDN1").
Proof. intros z Hz. rewrite unsigned_lit by lia. rewrite Z.add_0_r, swrap32_small by lia. reflexivity. Qed.
Lemma stk_lo_nonneg : ltac2:(TCodec.tc2 tcn__CJ_Lib_SysStep "J'7'I%211'S0yR0%211':y8%511%311p051'G&QFr4r3r2r1%544321&R3z%2216p041pU4;1pU:<1pU<>1pULG1").
Proof. intros segs m lo hi (H & _). exact H. Qed.
Ltac name_sp sp k :=
let sp1 := fresh "sp" in let E := fresh "Esp" in let H := fresh "Hsp" in
remember (Z_to_bv 64 (bv_unsigned sp + k)) as sp1 eqn:E;
assert (H : bv_unsigned sp1 = (bv_unsigned sp + k)%Z)
by (rewrite E; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *;
try match goal with ST : stk _ _ _ _ |- _ => pose proof (stk_lo_nonneg _ _ _ _ ST) end;
apply unsigned_lit; lia).
Ltac unname_sp :=
match goal with
| H : bv_unsigned ?sp1 = (bv_unsigned ?sp + ?k)%Z, E : ?sp1' = Z_to_bv 64 (bv_unsigned ?sp + ?k) |- _ =>
constr_eq sp1 sp1'; rewrite ?H in *; clear H; subst sp1
end.
Tactic Notation "call_sp" uconstr(SPEC) :=
lazymatch goal with
| |- evt _ _ (MS (TNode _ None (TNode _ (Some (Z_to_bv 64 (bv_unsigned ?sp + ?k))) _)) _ _ _ _ _ _) =>
name_sp sp k; call SPEC; unname_sp
| |- evt _ _ (MS (mkR _ (Z_to_bv 64 (bv_unsigned ?sp + ?k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
name_sp sp k; call SPEC; unname_sp
| _ => call SPEC
end.
Ltac sys_finish :=
(lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
lazymatch goal with |- ?P ?ms => try unfold P | _ => idtac end;
hnf;
repeat (lazymatch goal with |- ex _ => eexists end);
lazymatch goal with
| |- _ = _ /\ _ => split; [ cbv delta [mkR]; reflexivity | ]
| |- _ = _ => cbv delta [mkR]; reflexivity
end;
repeat match goal with |- _ /\ _ => split end; try assumption.
Lemma impl_from_evt : forall {node : Type} segs (atn : node -> machine_state -> Prop) {R} (t : itree node R) Q ms,
evt segs (fun ms' => impl segs atn t Q ms') ms -> impl segs atn t Q ms.
Proof. intros node segs atn R t Q ms H. eapply impl_evt; [exact H|]. intros ms' H'; exact H'. Qed.
Ltac iprefix := apply impl_from_evt.
Ltac ihere := apply evt_done.
Tactic Notation "icall" uconstr(SPEC) :=
(lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
first [ eapply SPEC
| eapply impl_epost_mono; [ eapply SPEC | ] ].
Ltac ipost segs :=
let a := fresh "ans" in let ms' := fresh "ms'" in let PO := fresh "POST" in
intros a ms' PO;
destruct_exs PO;
let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
destruct PO as [E [MUc [WMc PO]]];
first [ destruct PO as [MIc PO] | rename PO into MIc ];
subst ms';
lazymatch type of MUc with
| munch _ ?m ?m' =>
transport_after_call segs m m' MUc WMc;
clear MUc WMc;
try match goal with H : mem_inv segs m |- _ => clear H end;
try clear m
end;
try destruct_ands PO;
try (let MIname := fresh "MI" in
lazymatch goal with H : mem_inv segs _ |- _ => rename H into MIname; try rename MIname into MI end);
repeat match goal with
| |- context [ret_pc (Z_to_bv 64 ?n)] => is_Zlit n;
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
end.
