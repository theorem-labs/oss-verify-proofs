(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import HeapIface.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Bridge Require Import BrRes.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.MB Require Import ModelBounds.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Heap Require Import HeIface HeInst0 HeInst1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_HeClosed () := "C4ELinuxProcessSemantics?LinuxProcessSem3Run8sc_allocI47Corelib4Init5Logic2eq00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ2MB;ModelBoundsBmodel_bounds_proofC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Heap7HeInst06HI0_okC13~~~I47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics?LinuxProcessSem3Run;SpuriousCfg00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP4RunP00C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Heap7HeInst16HI1_okC13~~~".

Section BmKitW. Context {bmK : BMode}.   (* [comment removed for export] *)
Theorem HI0_ok_closed : forall (sptop lim : Z) (scfg : SpuriousCfg),
  sc_alloc scfg = false -> heap_ifaceE_ok (L0 sptop) scfg (HI0 sptop lim) lim.
Proof.
ltac2:(KReplay.run1 (kr_t_HeClosed ()) ["BmKitW"] "h06Halloch11Rh23limh34scfgh45sptopp;1p;3p;6g0000j13Tg000ej32Tg001?j10Tg002^j61Tg003lR0g004Jg005Df0R1#3g005d32p,3bmKf3f2f1P1g006D%01W1E1W0W3X20W4o"). Qed.

Theorem HI1_ok_closed : forall (sptop lim : Z) (scfg : SpuriousCfg),
  sc_alloc scfg = false -> heap_ifaceE_ok (L1 sptop) scfg (HI1 sptop lim) lim.
Proof.
ltac2:(KReplay.run1 (kr_t_HeClosed ()) ["BmKitW"] "h06Halloch11Rh23limh34scfgh45sptopp;1p;3p;6g0000j13Tg000ej32Tg001?j10Tg007Qj61Tg003lR0g004Jg005Df0R1#3g005d32p,3bmKf3f2f1P1g006D%01W1E1W0W3X20W4o"). Qed.
End BmKitW.
