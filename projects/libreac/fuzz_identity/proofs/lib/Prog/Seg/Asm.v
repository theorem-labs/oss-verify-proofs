From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel SlotInv
  reac_identity_init_c reac_identity_ingest_c reac_identity_fw_str_c reac_identity_reac_ver_str_c
  reac_box_catalogue_defect_c reac_box_family_of_c reac_box_family_stem_c check_str_c put_dec_c
  reac_box_catalogue_c bcmp_c memchr_c memcpy_c strlen_c strcmp_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Slot.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require reac_identity_init reac_identity_ingest
  reac_identity_fw_str reac_identity_reac_ver_str write_uint reac_box_catalogue_defect reac_box_family_of
  reac_box_family_stem check_str put_dec reac_box_catalogue bcmp memchr memcpy memset strlen strcmp.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require FrameProof.
From OSSVerify.libreac.fuzz_identity Require Statements.
Import ListNotations.
Open Scope Z_scope.


Section Asm.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.

Hypothesis sA01 :
  Hcut B APIf ra (Inv_K12eec B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13cb0 B APIf ra empty) ->
  Hcut B APIf ra (Inv_ENTRY B APIf ra empty).
Hypothesis sA02 :
  Hcut B APIf ra (Inv_K12ef4 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K12eec B APIf ra empty).
Hypothesis sA03 :
  Hcut B APIf ra (Inv_K12f08 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K12ef4 B APIf ra empty).
Hypothesis sA04 :
  Hcut B APIf ra (Inv_K12f24 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K12f08 B APIf ra empty).
Hypothesis sA05 :
  Hcut B APIf ra (Inv_K12f38 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K12f24 B APIf ra empty).
Hypothesis sA06 :
  Hcut B APIf ra (Inv_K12f54 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K12f38 B APIf ra empty).
Hypothesis sA07 :
  Hcut B APIf ra (Inv_K12f70 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K12f54 B APIf ra empty).
Hypothesis sA08 :
  Hcut B APIf ra (Inv_K12f78 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K12f70 B APIf ra empty).
Hypothesis sC01 :
  Hcut B APIf ra (Inv_K134ec B APIf ra empty) ->
  Hcut B APIf ra (Inv_K134e4 B APIf ra empty).
Hypothesis sC02 :
  Hcut B APIf ra (Inv_K13540 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13508 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K134ec B APIf ra empty).
Hypothesis sC03 :
  Hcut B APIf ra (Inv_K13c68 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K1353c B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13508 B APIf ra empty).
Hypothesis sC04 :
  Hcut B APIf ra (Inv_K1353c B APIf ra empty) ->
  Hcut B APIf ra (Inv_K1352c B APIf ra empty) /\ Hcut B APIf ra (Inv_K13530 B APIf ra empty).
Hypothesis sC05 :
  Hcut B APIf ra (Inv_K13544 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K1353c B APIf ra empty) /\ Hcut B APIf ra (Inv_K13540 B APIf ra empty) /\ Hcut B APIf ra (Inv_K13c68 B APIf ra empty).
Hypothesis sD01 :
  Hcut B APIf ra (Inv_K13594 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13544 B APIf ra empty).
Hypothesis sE01 :
  Hcut B APIf ra (Inv_K135a0 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13594 B APIf ra empty).
Hypothesis sE02 :
  Hcut B APIf ra (Inv_K135c0 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K135a0 B APIf ra empty).
Hypothesis sE03 :
  Hcut B APIf ra (Inv_K135cc B APIf ra empty) ->
  Hcut B APIf ra (Inv_K135c0 B APIf ra empty).
Hypothesis sE04 :
  Hcut B APIf ra (Inv_K135dc B APIf ra empty) ->
  Hcut B APIf ra (Inv_K135cc B APIf ra empty).
Hypothesis sE05 :
  Hcut B APIf ra (Inv_K135e8 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K135dc B APIf ra empty).
Hypothesis sE06 :
  Hcut B APIf ra (Inv_K135f0 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K135e8 B APIf ra empty).
Hypothesis sE07 :
  Hcut B APIf ra (Inv_K135fc B APIf ra empty) ->
  Hcut B APIf ra (Inv_K135f0 B APIf ra empty).
Hypothesis sE08 :
  Hcut B APIf ra (Inv_K1361c B APIf ra empty) ->
  Hcut B APIf ra (Inv_K135fc B APIf ra empty).
Hypothesis sE09 :
  Hcut B APIf ra (Inv_K13628 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K1361c B APIf ra empty).
Hypothesis sE10 :
  Hcut B APIf ra (Inv_K13630 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13628 B APIf ra empty).
Hypothesis sF01 :
  Hcut B APIf ra (Inv_K13664 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13630 B APIf ra empty).
Hypothesis sF02 :
  Hcut B APIf ra (Inv_K136a4 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13664 B APIf ra empty).
Hypothesis sF03 :
  Hcut B APIf ra (Inv_K136c0 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K136a4 B APIf ra empty).
Hypothesis sF04 :
  Hcut B APIf ra (Inv_K136dc B APIf ra empty) ->
  Hcut B APIf ra (Inv_K136c0 B APIf ra empty).
Hypothesis sG01 :
  Hcut B APIf ra (Inv_K136f0 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K136f8 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K136dc B APIf ra empty).
Hypothesis sG02 :
  Hcut B APIf ra (Inv_K13704 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K136f0 B APIf ra empty) /\ Hcut B APIf ra (Inv_K136f8 B APIf ra empty).
Hypothesis sG03 :
  Hcut B APIf ra (Inv_K1371c B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13704 B APIf ra empty).
Hypothesis sG04 :
  Hcut B APIf ra (Inv_K13734 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K1371c B APIf ra empty).
Hypothesis sG05 :
  Hcut B APIf ra (Inv_K13748 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13734 B APIf ra empty).
Hypothesis sG06 :
  Hcut B APIf ra (Inv_K1378c B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13748 B APIf ra empty).
Hypothesis sG07 :
  Hcut B APIf ra (Inv_K137c0 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K1378c B APIf ra empty).
Hypothesis sH01 :
  Hcut B APIf ra (Inv_K138bc B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13b18 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K137c0 B APIf ra empty).
Hypothesis sH02 :
  Hcut B APIf ra (Inv_K138d0 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K138bc B APIf ra empty).
Hypothesis sH03 :
  Hcut B APIf ra (Inv_K138f4 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13968 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K138d0 B APIf ra empty).
Hypothesis sH04 :
  Hcut B APIf ra (Inv_K1390c B APIf ra empty) ->
  Hcut B APIf ra (Inv_K138f4 B APIf ra empty).
Hypothesis sH05 :
  Hcut B APIf ra (Inv_K13968 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K139a4 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K1390c B APIf ra empty).
Hypothesis sH06 :
  Hcut B APIf ra (Inv_K1398c B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13968 B APIf ra empty).
Hypothesis sH07 :
  Hcut B APIf ra (Inv_K139a4 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K1398c B APIf ra empty).
Hypothesis sH08 :
  Hcut B APIf ra (Inv_K139cc B APIf ra empty) ->
  Hcut B APIf ra (Inv_K139a4 B APIf ra empty).
Hypothesis sH09 :
  Hcut B APIf ra (Inv_K139f4 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K139cc B APIf ra empty).
Hypothesis sH10 :
  Hcut B APIf ra (Inv_K13a2c B APIf ra empty) ->
  Hcut B APIf ra (Inv_K139ec B APIf ra empty) /\ Hcut B APIf ra (Inv_K139f4 B APIf ra empty).
Hypothesis sH11 :
  Hcut B APIf ra (Inv_K13a40 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13a2c B APIf ra empty).
Hypothesis sH12 :
  Hcut B APIf ra (Inv_K13a58 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13a40 B APIf ra empty).
Hypothesis sH13 :
  Hcut B APIf ra (Inv_K13a74 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13a58 B APIf ra empty).
Hypothesis sH14 :
  Hcut B APIf ra (Inv_K13a94 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13a74 B APIf ra empty).
Hypothesis sH15 :
  Hcut B APIf ra (Inv_K13aac B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13a94 B APIf ra empty).
Hypothesis sH16 :
  Hcut B APIf ra (Inv_K13ac8 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13af4 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13aac B APIf ra empty).
Hypothesis sH17 :
  Hcut B APIf ra (Inv_K13b18 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13ac8 B APIf ra empty) /\ Hcut B APIf ra (Inv_K13af4 B APIf ra empty).
Hypothesis sI01 :
  Hcut B APIf ra (Inv_K13b24 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13c98 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13b18 B APIf ra empty).
Hypothesis sI02 :
  Hcut B APIf ra (Inv_K13b34 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13b24 B APIf ra empty).
Hypothesis sI03 :
  Hcut B APIf ra (Inv_K13b3c B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13b34 B APIf ra empty).
Hypothesis sI04 :
  Hcut B APIf ra (Inv_K13b4c B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13b3c B APIf ra empty).
Hypothesis sI05 :
  Hcut B APIf ra (Inv_K13b54 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13b4c B APIf ra empty).
Hypothesis sI06 :
  Hcut B APIf ra (Inv_K13b64 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13b54 B APIf ra empty).
Hypothesis sI07 :
  Hcut B APIf ra (Inv_K13b70 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13b64 B APIf ra empty).
Hypothesis sI08 :
  Hcut B APIf ra (Inv_K13b80 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13b70 B APIf ra empty).
Hypothesis sI09 :
  Hcut B APIf ra (Inv_K13b9c B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13be0 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13b80 B APIf ra empty).
Hypothesis sI10 :
  Hcut B APIf ra (Inv_K13be0 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13b9c B APIf ra empty).
Hypothesis sI11 :
  Hcut B APIf ra (Inv_K13bf8 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13be0 B APIf ra empty).
Hypothesis sJ01 :
  Hcut B APIf ra (Inv_K13c28 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13bf8 B APIf ra empty).
Hypothesis sJ02 :
  Hcut B APIf ra (Inv_K13c5c B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13c48 B APIf ra empty).
Hypothesis sJ03 :
  Hcut B APIf ra (Inv_K13c60 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13c94 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13c88 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13c28 B APIf ra empty).
Hypothesis sJ04 :
  Hcut B APIf ra (Inv_K13c94 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13c5c B APIf ra empty) /\ Hcut B APIf ra (Inv_K13c60 B APIf ra empty).
Hypothesis sJ05 :
  Hcut B APIf ra (Inv_K13ca0 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13c88 B APIf ra empty) /\ Hcut B APIf ra (Inv_K13c94 B APIf ra empty) /\ Hcut B APIf ra (Inv_K13c98 B APIf ra empty).
Hypothesis sJ06 :
  Hcut B APIf ra (Inv_K13ca8 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13ca0 B APIf ra empty).
Hypothesis sJ07 :
  Hcut B APIf ra (Inv_K13cb0 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13ca8 B APIf ra empty).
Hypothesis sJ08 :
  Hcut B APIf ra (Inv_K13cb0 B APIf ra empty).
Hypothesis sA09 :
  Hrec B APIf ra (Inv_K12fc4_at B APIf ra empty) 0 ->
  Hcut B APIf ra (Inv_K1352c B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13530 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K12f78 B APIf ra empty).
Hypothesis sB00 :
  Hcut B APIf ra (Inv_K134e4 B APIf ra empty) -> forall i, Hrec B APIf ra (Inv_K12fc4_at B APIf ra empty) i.
Theorem slot_entry : Hcut B APIf ra (Inv_ENTRY B APIf ra empty).
Proof.
  pose proof sJ08 as h13cb0.
  pose proof (sJ07 h13cb0) as h13ca8.
  pose proof (sJ06 h13ca8) as h13ca0.
  destruct (sJ05 h13ca0) as (h13c88 & h13c94 & h13c98).
  destruct (sJ04 h13c94) as (h13c5c & h13c60).
  pose proof (sJ03 h13c60 h13c94 h13c88) as h13c28.
  pose proof (sJ02 h13c5c) as h13c48.
  pose proof (sJ01 h13c28) as h13bf8.
  pose proof (sI11 h13bf8) as h13be0.
  pose proof (sI10 h13be0) as h13b9c.
  pose proof (sI09 h13b9c h13be0) as h13b80.
  pose proof (sI08 h13b80) as h13b70.
  pose proof (sI07 h13b70) as h13b64.
  pose proof (sI06 h13b64) as h13b54.
  pose proof (sI05 h13b54) as h13b4c.
  pose proof (sI04 h13b4c) as h13b3c.
  pose proof (sI03 h13b3c) as h13b34.
  pose proof (sI02 h13b34) as h13b24.
  pose proof (sI01 h13b24 h13c98) as h13b18.
  destruct (sH17 h13b18) as (h13ac8 & h13af4).
  pose proof (sH16 h13ac8 h13af4) as h13aac.
  pose proof (sH15 h13aac) as h13a94.
  pose proof (sH14 h13a94) as h13a74.
  pose proof (sH13 h13a74) as h13a58.
  pose proof (sH12 h13a58) as h13a40.
  pose proof (sH11 h13a40) as h13a2c.
  destruct (sH10 h13a2c) as (h139ec & h139f4).
  pose proof (sH09 h139f4) as h139cc.
  pose proof (sH08 h139cc) as h139a4.
  pose proof (sH07 h139a4) as h1398c.
  pose proof (sH06 h1398c) as h13968.
  pose proof (sH05 h13968 h139a4) as h1390c.
  pose proof (sH04 h1390c) as h138f4.
  pose proof (sH03 h138f4 h13968) as h138d0.
  pose proof (sH02 h138d0) as h138bc.
  pose proof (sH01 h138bc h13b18) as h137c0.
  pose proof (sG07 h137c0) as h1378c.
  pose proof (sG06 h1378c) as h13748.
  pose proof (sG05 h13748) as h13734.
  pose proof (sG04 h13734) as h1371c.
  pose proof (sG03 h1371c) as h13704.
  destruct (sG02 h13704) as (h136f0 & h136f8).
  pose proof (sG01 h136f0 h136f8) as h136dc.
  pose proof (sF04 h136dc) as h136c0.
  pose proof (sF03 h136c0) as h136a4.
  pose proof (sF02 h136a4) as h13664.
  pose proof (sF01 h13664) as h13630.
  pose proof (sE10 h13630) as h13628.
  pose proof (sE09 h13628) as h1361c.
  pose proof (sE08 h1361c) as h135fc.
  pose proof (sE07 h135fc) as h135f0.
  pose proof (sE06 h135f0) as h135e8.
  pose proof (sE05 h135e8) as h135dc.
  pose proof (sE04 h135dc) as h135cc.
  pose proof (sE03 h135cc) as h135c0.
  pose proof (sE02 h135c0) as h135a0.
  pose proof (sE01 h135a0) as h13594.
  pose proof (sD01 h13594) as h13544.
  destruct (sC05 h13544) as (h1353c & h13540 & h13c68).
  destruct (sC04 h1353c) as (h1352c & h13530).
  pose proof (sC03 h13c68 h1353c) as h13508.
  pose proof (sC02 h13540 h13508) as h134ec.
  pose proof (sC01 h134ec) as h134e4.
  pose proof (sB00 h134e4 0%nat) as hrec0.
  pose proof (sA09 hrec0 h1352c h13530) as h12f78.
  pose proof (sA08 h12f78) as h12f70.
  pose proof (sA07 h12f70) as h12f54.
  pose proof (sA06 h12f54) as h12f38.
  pose proof (sA05 h12f38) as h12f24.
  pose proof (sA04 h12f24) as h12f08.
  pose proof (sA03 h12f08) as h12ef4.
  pose proof (sA02 h12ef4) as h12eec.
  exact (sA01 h12eec h13cb0).
Qed.

End Asm.
