(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool FunctionalExtensionality.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec AxSymExec3K AxSymExec3BK AsanPlanCoreK AsanPlanK AsanPlanFastK FxExecK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_AsanPlanFastXK () := "C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3K4AX2K4itabC13~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00K47Corelib4Init5Logic2eq01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK6atable00C13~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3K4AX2K4expr00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK3acs00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK6spiece00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK7loopctx00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK4plan00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK4cres00C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK5checkC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FxExecK4EXFK>run_block_gc_fC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=AsanPlanCoreK4APCK<run_block_gcC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FxExecK4EXFKArun_block_gc_f_eqC13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=AsanPlanCoreK4APCK3acs00C13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>AsanPlanFastXK4APKX8check_g2C13~~~I47Corelib4Init5Logic2eq00I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=AsanPlanCoreK4APCK6atable00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3K4AX2K6kentry00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=AsanPlanCoreK4APCK4amap00C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=AsanPlanCoreK4APCK?kn_grant_filterC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=AsanPlanCoreK4APCK9kn_havocMC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=AsanPlanCoreK4APCK8kn_havocC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>AsanPlanFastXK4APKX<check_g2_refC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=AsanPlanCoreK4APCK<kn_havocM_eqC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>AsanPlanFastXK4APKXBrun_block_gc_f_eqfC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=AsanPlanFastK4APKF8kgf_fastC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=AsanPlanFastK4APKF;kgf_fast_eqC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>AsanPlanFastXK4APKX;check_fastxC13~~~".
Import ListNotations. Import AX2K.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module APKX.
Ltac has_const t c := lazymatch t with context [c] => idtac | _ => fail "abstraction target does not occur:" c end.
Definition check_g2 :=
  ltac:(let t := eval cbv beta delta [APK.check APCK.node_mmap2 APCK.node_brk2 APCK.mmap_null APCK.mmap_fixed_free
                                      APCK.mmap_fixed_free1 APCK.mmap_fixed_grant APCK.node_absword] in @APK.check in
        has_const t (@APCK.kn_grant_filter); has_const t (@APCK.run_block_gc); has_const t (@APCK.kn_havoc);
        let t' := eval pattern (@APCK.kn_grant_filter), (@APCK.run_block_gc), (@APCK.kn_havoc) in t in
        lazymatch t' with ?F _ _ _ => exact F end).
Lemma check_g2_ref : check_g2 (@APCK.kn_grant_filter) (@APCK.run_block_gc) (@APCK.kn_havoc) = @APK.check.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanFastXK ()) [] "h01Ah12HSh22ITh32KCh45LIMITh52XBh62XEh72XNh85bfuelh92csh:4fuelh;2lch<3nx0h=1ph>4segsp;1p;2g0000R0p4p70R1p1001@R2p4p710p8P1P2p4p7210p8P1p1002Bp4p710p8g002`j11Tg003@j10Tg003bj22Tg004Bj23Tg004\#1g005[g006lR1g007KR2g007i#1R3g009;R4%04R5[[\1g00:I#1,22/24#0\4\3\11244#0\4\3\1P5\1g00;Z#0g00<lg00>;]=^94];^:1^81^31]1]5]6]7]4]<]0^20]>g00?J'3o"). Qed.
Lemma run_block_gc_f_eqf : EXFK.run_block_gc_f = @APCK.run_block_gc.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanFastXK ()) [] "h02ITh11Kh22csh34fuelh43nx0h55stopsh61xh72x0h82x1h92x2h:2x3h;2x4h<2x5p;1p;2p;3p;4p;5p;6p;7g002`j11Tg003@j1?Tg00@XR0j13j2>j3:j45j57j69Tg00AnR1j12j2;j34j46j58j6=Tg00CHj7<Tg001@j50Tg004\#1R2g0000R3g006lR4g007K#1R5g00DaR6%?6R7]2R8]5R9^34R:^14R;]4R<]0P0P1P3P<f0R<#3%2<P4P;f1R;/><1;;<P4P:f2R:?:;<A4:;<P4P9f3R9P:P;P<C5P9P:P;P<C6P5P8f4R8P9P:P;P<D7P8P9P:P;P<D8P6P7f5R7P8P9P:P;P<E9P7P8P9P:P;P<E=f6P7P8P9P:P;P<F<X<6D0X;5D0X:4D0X94D0X84D0X73D0X62D0o"). Qed.
Definition check_fastx := check_g2 APKF.kgf_fast EXFK.run_block_gc_f (@APCK.kn_havocM).
Theorem check_fastx_eq : check_fastx = @APK.check.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanFastXK ()) [] "h01Ah12ITh22csh34fuelh41kh51lh63nx0h74segsh82HSh91Kh:2KCh;5LIMITh<2XBh=2XEh>2XNh?5bfuelh@2lchA2mshB1ohC1phD5stopshE2ubhF2ukhG2unp;1p;2p;3p;6g002`j10Tg003@j11Tg003bj24Tg00F4j33Tg00GKj32Tg002Bj65Tg00Geg00I;#0R0g00JO#0P0]A]4]0R1g00KcR2g004\#0R3g0000R4g005[g006lR5g007KR6g007iR7#0R8g009;R9%19R:[[\5g00:I#0,46/49#1\9\8\51499#1\9\8\5P:\5g00;Z#1g00<lg00>;]C^29]@^35^?5^:5]8]<]=]>];]6]0]1]7R9f0R:g00@XR8g00M@R;33g00?JR<32X51%06g00DaR1%11]2]D^35^95^65^14^73R3g00AnR4A32:;=29<XB3P0^G7^F6^E7^40R0g00NWA324:=29<X50g00OmP;g00QHE5P8g00RbE5g00TCg00UYE5g00W2=29<eo"). Qed.
End APKX.
