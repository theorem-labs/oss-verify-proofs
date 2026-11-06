(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool FunctionalExtensionality.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import AxSymExec3K AxSymExec3BK AsanPlanCoreK AsanPlanK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_AsanPlanFastK () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00K47Corelib4Init5Logic2eq01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3K4AX2K4itabC13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK6atable00C13~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3K4AX2K4expr00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK3acs00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK6spiece00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK7loopctx00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK4plan00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK4cres00C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK5checkC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=AsanPlanFastK4APKF8kgf_fastC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=AsanPlanCoreK4APCK?kn_grant_filterC13~~~I47Corelib4Init5Logic2eq00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<AxSymExec3BK5AX2BK4mkbcC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=AsanPlanCoreK4APCK@kn_grant_filterBC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=AsanPlanCoreK4APCKDkn_grant_filterB_eqfC13~~~C47Corelib4Init5Logic8eq_ind_rC46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityI89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=AsanPlanCoreK4APCK6atable00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3K4AX2K6kentry00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=AsanPlanCoreK4APCK4amap00C13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=AsanPlanFastK4APKF7check_gC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=AsanPlanFastK4APKF;check_g_refC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=AsanPlanFastK4APKF;kgf_fast_eqC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=AsanPlanFastK4APKF:check_fastC13~~~".
Import ListNotations. Import AX2K. Import AX2BK.

Module APKF.

(* [comment removed for export] *)
Definition check_g :=
  ltac:(let t := eval cbv beta delta [APK.check APCK.node_mmap2 APCK.node_brk2 APCK.mmap_null APCK.mmap_fixed_free
                                      APCK.mmap_fixed_free1 APCK.mmap_fixed_grant] in @APK.check in
        let t' := eval pattern (@APCK.kn_grant_filter) in t in
        lazymatch t' with ?F _ => exact F end).

Lemma check_g_ref : check_g (@APCK.kn_grant_filter) = @APK.check.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanFastK ()) [] "h01Ah12HSh22ITh32KCh45LIMITh52XBh62XEh72XNh85bfuelh92csh:4fuelh;2lch<3nx0h=1ph>4segsp;1p;2g0000j11Tg000Pj10Tg0012j22Tg001Rj23Tg001l#1g002kg004;g005LR0g005kR1g006I#1R2g007[R3%03R4[[\0g008i#1,21/23#0\3\2\01233#0\3\2\0P4\0g00::#0g00;Lg00<[]=^93];^:0^80^30]1]5]6]7]4]<]0]2]>g00=j'3o"). Qed.

Definition kgf_fast (A : APCK.atable) (k : list kentry) (ms : list APCK.amap) : list kentry :=
  APCK.kn_grant_filterB A (mkbc k) ms.
Lemma kgf_fast_eq : kgf_fast = @APCK.kn_grant_filter.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanFastK ()) [] "h01kh12msh21Ah31lp;1p;2p;3p;6p;5g0000j14Tg00?8R0j1=j25j39Tg00@NR1j1<j23j32Tg00Akj31Tg001Rj2;Tg00BEj1:Tg00CWj26Tg00E5j27Tg00FWj68Tg00G5j50Tg00H7R2g00IM#4R3g00Ja#4R4P3]1R5]0P0P1P3P5f0R1#=%<1P4P3f1R0/511301P5f2R6/30P1P0O1f3?260513X35A2601R5,;3%:0,661760E8A9601=135eX14D0X03D0X22D0o"). Qed.

Definition check_fast := check_g kgf_fast.
Theorem check_fast_eq : check_fast = @APK.check.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanFastK ()) [] "h01Ah12HSh22ITh32KCh45LIMITh52XBh62XEh72XNh85bfuelh92csh:4fuelh;1kh<1lh=2lch>2msh?3nx0h@1phA4segsp;1p;2p;3p;6g0000j10Tg000Pj11Tg0012j22Tg00L5j14Tg00Akj33Tg00FWj65Tg00H7g00IM#0R0g00Ja#0P0]>];]0R0g00@Ng001l#0g002kg004;g005LR1g005kR2g006I#0R3g007[R4%14R5[[\1g008i#0,22/24#1\4\3\11244#1\4\3\1P5\1g00::#1g00;Lg00<[]@^94]=^:1^81^31]1]5]6]7]4]?]0]2]AR1f0#4g00=jR433X<0g00MJg00?8g00NcE5g00P<=314eo"). Qed.

End APKF.
