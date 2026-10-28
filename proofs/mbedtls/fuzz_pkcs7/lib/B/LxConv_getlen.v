From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_asn1_get_tag P_asn1_get_len.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg A_asn1_get_len.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface Arr CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxSum LxSoundSum.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc.
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia.
Local Ltac qlia ::= orc_qlia.
Local Ltac pqlia ::= orc_pqlia.
Local Ltac lia1 D ::= orc_lia1 D.
Local Ltac dlia ::= orc_dlia.
Local Ltac plia ::= orc_plia.
Local Ltac clear_disj ::= fc_clear_disj.
Local Ltac prune_disj ::= fc_prune_disj.
Local Ltac clear_mods ::= fc_clear_mods.
Local Ltac keep_disj1 D ::= fc_keep_disj1 D.
Ltac2 gd_tbl_LxConv_getlen () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LX.LxSum.SUM"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Numbers.BinNums.positive"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.mfact"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MRw"; "q"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.cellx"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.XZ"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MAobj"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.ELit"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MRo"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.pfact"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FLe"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EAdd"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FLt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FSep"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FSep0"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FAl"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EZv"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FCr"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EMulC"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.two64"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.expr"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MStk"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FOr2"; "RocqVerifyHarness.AgentSubmission.LX.LxSum.SUMG"; "Corelib.Init.Datatypes.nat"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.LX.LxSum.summary"; "RocqVerifyHarness.AgentSubmission.LX.LxSoundSum.summary_okG"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "SUM_getlenA"; "SUM_gettagA"; "SUM_getboolA"; "SUM_getintA"; "SUM_bitstrnullA"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.XB"; "lxz1"; "RocqVerifyHarness.AgentSubmission.LX.LxSum.SUMX"; "Corelib.Init.Datatypes.None"; "Stdlib.ZArith.BinInt.Z.of_N"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FEq"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.XRep"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FOr3z"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Corelib.Lists.ListDef.nth"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LX.LxSoundSum.summary_okO"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "SUM_amemsetA"; "SUM_amemset0A"; "lxz4"; "lxz8"; "lxbs0"; "SUM_getalgA"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_bcmp"; "SUM_oidlook1A"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FProp"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_memcmp_i"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.True"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Corelib.Init.Datatypes.list"; "bcmp_prop"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Lib.Image.ro_bytes_b"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.LX.LxSoundSum.summary_okP"; "SUM_bcmpA"; "SUM_bcmp0A"].


Definition q (i : positive) : expr := EZv i.
Notation "a .+ b" := (EAdd a b) (at level 50, left associativity).
Notation "a .- b" := (EAdd a (EMulC (-1) b)) (at level 50, left associativity).


Definition SUM_getlenA : summary := ltac2:(CDefT.buildp (gd_tbl_LxConv_getlen ()) "(0.+99724.$1.#:.#11.#1.(2.(3.$4.$5.)(6.$4.$5.+:.^1.)(2.(3.$4.$5.)(6.$4.$5.+;.^2.)(2.(3.$4.$5.)(6.$4.$5.+<.^3.)(2.(3.$4.$5.)(6.$4.$5.+2.^7.)(7.(3.$4.$5.))))))(8.$5.^9.)(2.$9.(:.(;.^1.)(2.$<.(=.&8.(;.^4.))(7.$<.)))(2.$9.(:.(;.^3.)(2.$<.(=.&8.(;.^:.))(7.$<.)))(7.$9.)))(8.(3.$5.$5.)(6.$5.$5.^8.^7.))(2.(3.(3.$5.$5.)$5.)(6.(3.$5.$5.)$5.(6.$5.$5.^5.^6.)^1.)(7.(3.(3.$5.$5.)$5.)))(2.$9.(>.(;.^1.)(?.+8.))(2.$9.(>.(;.^3.)(?.+8.))(2.$9.(>.(;.^5.)(;.^6.))(2.$9.(10.(?.+?5>50.)(2.$<.(=.&8.(?.+1099?8.))(7.$<.)))(2.$9.(10.(?.+1099?8.)(2.$<.(=.&8.(;.^9.))(7.$<.)))(7.$9.))))))(2.$11.(12.(;.^5.)(;.^4.))(2.$11.(12.(;.^4.)(;.^2.))(2.$11.(12.(;.^2.)(13.(;.^5.)(;.^6.)))(2.$11.(14.(13.(;.^5.)(;.^6.))(?.(15.+2.+3?.)))(2.$11.(16.(;.^1.)(?.+8.)(;.^3.)(?.+8.))(2.$11.(17.(;.^6.)(;.^1.)(?.+8.)(;.^5.)(;.^6.))(2.$11.(17.(;.^6.)(;.^3.)(?.+8.)(;.^5.)(;.^6.))(2.$11.(18.(19.^1.)&3.)(2.$11.(18.(19.^3.)&3.)(2.$11.(14.(?.=)(;.^1.))(2.$11.(14.(?.=)(;.^3.))(2.$11.(14.(?.=)(;.^5.))(2.$11.(12.(;.^8.)(13.(;.^7.)(?.-10.)))(2.$11.(18.(19.^7.)&4.)(2.$11.(1:.(;.^8.)(13.(;.^7.)(1;.-1.(;.^8.))))(2.$11.(16.(;.^1.)(?.+8.)(13.(;.^7.)(?.-10.))(?.+10.))(2.$11.(16.(;.^3.)(?.+8.)(13.(;.^7.)(?.-10.))(?.+10.))(2.$11.(17.(;.^6.)(;.^5.)(;.^6.)(13.(;.^7.)(?.-10.))(?.+10.))(2.$11.(12.(?.=)(;.^7.))(2.$11.(12.(;.^7.)(?.(1<.$1=.+1.)))(7.$11.)))))))))))))))))))))(2.(3.$1>.$1>.)(6.$1>.$1>.(;.^1.)(13.(;.^1.)(?.+8.)))(2.(3.$1>.$1>.)(6.$1>.$1>.(;.^3.)(13.(;.^3.)(?.+8.)))(2.(3.$1>.$1>.)(6.$1>.$1>.(13.(;.^7.)(?.-10.))(;.^7.))(7.(3.$1>.$1>.)))))(2.(3.$4.$5.)(6.$4.$5.+:.^;.)(2.(3.$4.$5.)(6.$4.$5.+5.^>.)(2.(3.$4.$5.)(6.$4.$5.+6.^?.)(2.(3.$4.$5.)(6.$4.$5.+7.^10.)(2.(3.$4.$5.)(6.$4.$5.+;.^11.)(2.(3.$4.$5.)(6.$4.$5.+<.^12.)(2.(3.$4.$5.)(6.$4.$5.+=.^13.)(2.(3.$4.$5.)(6.$4.$5.+>.^14.)(2.(3.$4.$5.)(6.$4.$5.+?.^15.)(2.(3.$4.$5.)(6.$4.$5.+10.^16.)(2.(3.$4.$5.)(6.$4.$5.+11.^17.)(2.(3.$4.$5.)(6.$4.$5.+1<.^18.)(2.(3.$4.$5.)(6.$4.$5.+1=.^19.)(2.(3.$4.$5.)(6.$4.$5.+1>.^1:.)(2.(3.$4.$5.)(6.$4.$5.+1?.^1;.)(7.(3.$4.$5.)))))))))))))))))(2.$9.(:.(;.^1.)(2.$<.(=.&8.(;.^<.))(7.$<.)))(2.$9.(:.(;.^3.)(2.$<.(=.&8.(;.^=.))(7.$<.)))(2.$9.(1?.(;.^8.)(;.^7.))(7.$9.))))(2.$11.(14.(?.-7?.)(;.^;.))(2.$11.(12.(;.^;.)(?.=))(2.$11.(12.(;.^4.)(;.^<.))(2.$11.(12.(;.^<.)(;.^2.))(2.$11.(20.(13.(;.^;.)(?.+1.))(?.=)(13.(;.^4.)(?.+1.))(;.^<.))(2.$11.(20.(13.(;.^;.)(?.+1.))(?.=)(;.^=.)(13.(;.^2.)(1;.-1.(;.^<.))))(2.$11.(12.(?.=)(;.^=.))(2.$11.(12.(;.^=.)(?.(1<.$1=.+1.)))(7.$11.))))))))))")
.
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L38557627424.3000009S1z2H12H2".
Lemma uw64 : forall z, 0 <= z -> z <= two64 - 1 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z H1 H2. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus, two64 in *. cbn in *. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "".

Section S.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0@L12066857909.93 L13952666928.120L20572041089.120L20628170175.120L22369800293.120L23290313653.93 L25516740322.120L2951488621.120 L43033456413.93 L43494931656.93 L4890678494.120 L61492213990.12000000J01101g02V03E03_04U05<05Z05[06B06iS2PP4LENP3SPu2bs4PR174PR19S2PP4LENP3SPu2bs3PR83PR94PR144PR191r2HrS2PP3END4LENP1P3SPu2bs3PR83PR94PR144PR191r2p'1L2Hr3HL0S2PP3END4LENP1P3SPu2bs3PR83PR94PR144PR192p'3Hp'S2PP3END4LENP1P3SPu2bs3PR83PR94PR144PR192p'3Hp'S2PP4LENP3SPu2bs4PR164PR19S2PP3END4LENP1P3SPu2bs3PR83PR94PR144PR191r2p'1L2Hr3HL0S2PP4LENP3SPu2bs3PR83PR94PR144PR191L2LRS2PP4LENP3BUF3SPu2bs4PR184PR19FS2PP4LENP3SPu2bs3PR83PR94PR144PR191L2LRS2PP4LENP3SPu2bs3PR83PR94PR144PR191r2Hr".
  Lemma sum_getlenA_valid : summary_valid asegs AL SUM_getlenA.
  Proof.
    unfold SUM_getlenA, q. lx_sum_unfold.
    intros PP END LENP P BUF LEN SPu lo sb LV bs CS F fc m.
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    intros [CSOK ALWF] SB MI R10 R11 R12 R2 ST HPP HLENP [HBUF HLEN] OPP OLEN OBUF G1 G2.
    intros PR1 PR2 PR3 PR4 PR5 PR6 PR7 PR8 PR9 PR10 PR11 PR12 PR13 PR14 PR15 PR16 PR17 PR18 PR19 PR20.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'. destruct IMG' as (IG & ILO & IHI & IGSB). subst LEN.
    assert (U2 : bv_unsigned x2 = SPu) by (rewrite R2; apply uw64; assumption).
    pose proof (A_asn1_get_len_spec AL IMG) as SP. unfold asn1_get_len_stmtA, A_ASN1_GET_LEN in SP.
    eapply evtA_cut.
    { eapply (SP CS x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m PP LENP P END BUF lo bs (Z_to_bv 64 LV));
        rewrite ?U2; first [eassumption | cbn in *; lia | split; [rewrite IG, IGSB; exact G1 | rewrite IGSB, <- SB; exact G2] ]. }
    clear SP. cbv beta. intros ms' POST. unfold asn1_get_len_postA in POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & r & p' & L & -> & MU & WM & MI' & -> & Hr & HPP' & HLENP' & Hp' & HL0 & ST').
    apply evtA_done. pose proof (lx_urange L) as LR. rewrite U2 in MU, ST'.
    lx_sum_post.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "".

  Lemma sums_getlen_ok : Forall (summary_ok asegs AL) [SUM_getlenA].
  Proof. repeat constructor; apply apply_summary_sound; apply sum_getlenA_valid. Qed.
End S.
