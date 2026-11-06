(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac EbtLeaf EbtAllocG EbtPoison ArtRuns ArtRunsMem EbtFp EbtFree1 EbtCellEx EbtRecycle4.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_r3ef18_4052c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_rcy_head_mem (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
  Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18)))
    (sp - 40) (U (getr regs 19))) (sp - 48) (U (getr regs 20))) (sp - 80) 0) (sp - 72) 0) (sp - 64) 0) (sp - 56) 0) (0x142d70 + 152) 257.

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_rcy_head : forall regs (M rom : word -> option byte) (raw : word) (sp mn cnt gbytes gfirst : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 0x142d70 -> getr regs 11 = Z_to_bv 64 mn ->
  0x69c000 + 80 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 80) 80 -> wrA M (0x142d70 + 152) 4 ->
  1 <= cnt -> 16384 * cnt <= gbytes -> gbytes < 2 ^ 57 -> 0 <= mn < gbytes -> 0 <= gfirst < 2 ^ 64 ->
  cellA M (0x142d70 + 152) 4 256 -> cellA M (0x142d70 + 184) 8 gbytes -> cellA M (0x142d70 + 160) 8 cnt -> cellA M (0x142d70 + 168) 8 gfirst ->
  exists regs', msteps ASEGS (mkst regs (0x55464 : word) M rom) (mkst regs' (0x55560 : word) (art_rcy_head_mem M sp raw regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (sp - 80) /\ getr regs' 10 = Z_to_bv 64 0x142d70 /\ getr regs' 11 = Z_to_bv 64 mn /\ getr regs' 14 = Z_to_bv 64 0 /\ getr regs' 15 = Z_to_bv 64 0
    /\ getr regs' 16 = Z_to_bv 64 cnt /\ getr regs' 5 = Z_to_bv 64 gfirst
    /\ (forall r : reg, In r [1; 3; 4; 8; 9; 12; 13; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp mn cnt gbytes gfirst H1 H2 H10 H11 Hsp Hsp' W Wlk Hcnt Hmerge Hgb Hmn Hgf Clk Cgb Ccnt Cgf.
  eexists. split.
  { zstep F_55414 D_55414.
    zsd F_55418 D_55418 (sp - 8) (U raw) ltac:(rewok W). zsd F_5541c D_5541c (sp - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_55420 D_55420 (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_55424 D_55424 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_55428 D_55428 (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_5542c D_5542c (sp - 48) (U (getr regs 20)) ltac:(rewok W).
    zsd F_55430 D_55430 (sp - 80) 0 ltac:(rewok W). zsd F_55434 D_55434 (sp - 72) 0 ltac:(rewok W).
    zsd F_55438 D_55438 (sp - 64) 0 ltac:(rewok W). zsd F_5543c D_5543c (sp - 56) 0 ltac:(rewok W).
    zstep F_55440 D_55440. zstep F_55444 D_55444.
    stepn F_55448 D_55448. rwH. zclosed (0x142d70 + 152).
    zstep F_5544c D_5544c.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Clk' : cellA X (0x142d70 + 152) 4 256) by zcell; assert (Wlk' : wokA X (0x142d70 + 152) 4) by zwok end.
    zcas6 F_55450 D_55450 F_55454 D_55454 F_55458 D_55458 F_5545c D_5545c F_55460 D_55460 F_55464 D_55464 (0x142d70 + 152) 256 257 1 257 Clk' Wlk'.
    zbft F_55468 D_55468.
    stepn F_5546c D_5546c. rwH. zclosed 0.
    zbft F_55470 D_55470.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cgb' : cellA X (0x142d70 + 184) 8 gbytes) by zcell; assert (Ccnt' : cellA X (0x142d70 + 160) 8 cnt) by zcell;
      assert (Cgf' : cellA X (0x142d70 + 168) 8 gfirst) by zcell;
      assert (T0 : cellA X (sp - 80) 8 0) by zcell; assert (T16 : cellA X (sp - 64) 8 0) by zcell end.
    zld F_55474 D_55474 (0x142d70 + 184) Cgb'.
    zld F_55478 D_55478 (0x142d70 + 160) Ccnt'.
    zstep F_5547c D_5547c.
    zbft F_55480 D_55480.
    zbft F_55484 D_55484.
    stepn F_55488 D_55488. zcl4.
    zstep F_5548c D_5548c. zstep F_55490 D_55490. zstep F_55494 D_55494.
    zbtk F_55498 D_55498.
    zld F_554d0 D_554d0 (sp - 80) T0.
    zld F_554d4 D_554d4 (sp - 64) T16.
    zld F_554d8 D_554d8 (0x142d70 + 184) Cgb'.
    zbft F_554dc D_554dc.
    zld F_554e0 D_554e0 (0x142d70 + 168) Cgf'.
    stepn F_554e4 D_554e4.
    unfold art_rcy_head_mem. apply mst_refl. }
  split; [gres; reflexivity|]. split; [gres; exact H10|]. split; [gres; exact H11|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
  split; [gres; reflexivity|]. split; [gres; reflexivity|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

#[using="Type"] Lemma art_rcy_pop : forall regs (M rom : word -> option byte) (tmp k plast gc b next size gbytes glast tbytes tfirst : Z),
  getr regs 10 = Z_to_bv 64 0x142d70 -> getr regs 14 = Z_to_bv 64 k -> getr regs 15 = Z_to_bv 64 plast -> getr regs 16 = Z_to_bv 64 gc -> getr regs 5 = Z_to_bv 64 b ->
  getr regs 2 = Z_to_bv 64 tmp ->
  0x69c000 <= tmp -> tmp + 32 < 2 ^ 64 -> 0x69c000 <= b -> b + 8192 < 2 ^ 64 -> apart tmp 32 b 8192 -> 0 <= k < 2 ^ 63 -> 1 <= gc < 2 ^ 64 ->
  0 <= next < 2 ^ 64 -> 0 <= size < 2 ^ 64 -> 0 <= gbytes < 2 ^ 64 -> 0 <= tbytes < 2 ^ 64 ->
  (k <> 0 -> 0x69c000 <= plast /\ plast + 8 < 2 ^ 64 /\ apart plast 8 b 8192 /\ apart plast 8 tmp 32 /\ wrA M plast 8) ->
  wrA M tmp 32 -> wrA M (0x142d70 + 160) 32 -> wrA M b 8 ->
  cellA M b 8 next -> cellA M (b + 8) 8 size -> cellA M (0x142d70 + 184) 8 gbytes -> cellA M (0x142d70 + 176) 8 glast -> cellA M (tmp + 24) 8 tbytes -> cellA M (tmp + 8) 8 tfirst ->
  exists regs' (M' : word -> option byte), msteps ASEGS (mkst regs (0x55560 : word) M rom) (mkst regs' (0x5555c : word) M' rom)
    /\ getr regs' 14 = Z_to_bv 64 (k + 1) /\ getr regs' 15 = Z_to_bv 64 b /\ getr regs' 5 = Z_to_bv 64 next /\ getr regs' 7 = Z_to_bv 64 (gbytes - size) /\ getr regs' 16 = Z_to_bv 64 (gc - 1) /\ getr regs' 6 = Z_to_bv 64 b
    /\ (forall r : reg, In r [1; 2; 3; 4; 8; 9; 10; 11; 12; 13; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r)
    /\ mem_grows M M' /\ art_agree [(0x142d70 + 160, 32); (b, 8); (tmp, 32); (plast, if k =? 0 then 0 else 8)] M M'
    /\ cellA M' (0x142d70 + 168) 8 next /\ cellA M' (0x142d70 + 160) 8 (gc - 1) /\ cellA M' (0x142d70 + 184) 8 (gbytes - size) /\ cellA M' b 8 0
    /\ (next = 0 -> cellA M' (0x142d70 + 176) 8 0) /\ (next <> 0 -> cellA M' (0x142d70 + 176) 8 glast)
    /\ (k = 0 -> cellA M' (tmp + 8) 8 b) /\ (k <> 0 -> cellA M' (tmp + 8) 8 tfirst /\ cellA M' plast 8 b)
    /\ cellA M' (tmp + 24) 8 (tbytes + size).
Proof.
  intros regs M rom tmp k plast gc b next size gbytes glast tbytes tfirst H10 H14 H15 H16 H5 H2 Htmp Htmp' Hb Hb' Atb Hk Hgc Hnext Hsize Hgb Htb Hpl Wt Wq Wb
    Cnext Csize Cgb Cgl Ctb Ctf.
  unfold apart in Atb.
  destruct (Z.eq_dec next 0) as [N0|N1]; destruct (Z.eq_dec k 0) as [K0|K1].
  - rewrite (proj2 (Z.eqb_eq k 0) K0). eexists. eexists. split.
    { zbft F_55510 D_55510.
      zld F_55514 D_55514 b Cnext.
      zsd F_55518 D_55518 (0x142d70 + 168) next ltac:(rewok Wq).
      zbft F_5551c D_5551c.
      zsd F_55520 D_55520 (0x142d70 + 176) 0 ltac:(rewok Wq).
      zstep F_55524 D_55524.
      zsd F_55528 D_55528 (0x142d70 + 160) (gc + -1) ltac:(rewok Wq).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize' : cellA X (b + 8) 8 size) by zcell; assert (Cgb' : cellA X (0x142d70 + 184) 8 gbytes) by zcell end.
      zld F_5552c D_5552c (b + 8) Csize'.
      zld F_55530 D_55530 (0x142d70 + 184) Cgb'.
      zstep F_55534 D_55534.
      zsd F_55538 D_55538 (0x142d70 + 184) (gbytes - size) ltac:(rewok Wq).
      zstep F_5553c D_5553c.
      zsd F_55540 D_55540 b 0 ltac:(rewok Wb).
      zbft F_55544 D_55544.
      stepn F_55548 D_55548.
      zsd F_5555c D_5555c (tmp + 8) b ltac:(rewok Wt).
      stepn F_55560 D_55560.
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize2 : cellA X (b + 8) 8 size) by zcell; assert (Ctb' : cellA X (tmp + 24) 8 tbytes) by zcell end.
      zld F_554ec D_554ec (b + 8) Csize2.
      zld F_554f0 D_554f0 (tmp + 24) Ctb'.
      zstep F_554f4 D_554f4.
      zsd F_554f8 D_554f8 (tmp + 24) (tbytes + size) ltac:(rewok Wt).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cgb2 : cellA X (0x142d70 + 184) 8 (gbytes - size)) by zcell end.
      zld F_554fc D_554fc (0x142d70 + 184) Cgb2.
      zstep F_55500 D_55500. zstep F_55504 D_55504. zstep F_55508 D_55508.
      apply mst_refl. }
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
    split. { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
    split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|].
    split; [zcell|]. split; [replace (gc - 1) with (gc + -1) by lia; zcell|]. split; [zcell|]. split; [zcell|].
    split; [intros _; zcell|]. split; [intros X; exfalso; lia|].
    split; [intros _; zcell|]. split; [intros X; exfalso; lia|]. zcell.
  - destruct (Hpl K1) as (Hp0 & Hp1 & Apb & Apt & Wpl). unfold apart in Apb, Apt. rewrite (proj2 (Z.eqb_neq k 0) K1). eexists. eexists. split.
    { zbft F_55510 D_55510.
      zld F_55514 D_55514 b Cnext.
      zsd F_55518 D_55518 (0x142d70 + 168) next ltac:(rewok Wq).
      zbft F_5551c D_5551c.
      zsd F_55520 D_55520 (0x142d70 + 176) 0 ltac:(rewok Wq).
      zstep F_55524 D_55524.
      zsd F_55528 D_55528 (0x142d70 + 160) (gc + -1) ltac:(rewok Wq).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize' : cellA X (b + 8) 8 size) by zcell; assert (Cgb' : cellA X (0x142d70 + 184) 8 gbytes) by zcell end.
      zld F_5552c D_5552c (b + 8) Csize'.
      zld F_55530 D_55530 (0x142d70 + 184) Cgb'.
      zstep F_55534 D_55534.
      zsd F_55538 D_55538 (0x142d70 + 184) (gbytes - size) ltac:(rewok Wq).
      zstep F_5553c D_5553c.
      zsd F_55540 D_55540 b 0 ltac:(rewok Wb).
      zbtk F_55544 D_55544.
      zsd F_554e8 D_554e8 plast b ltac:(rewok Wpl).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize2 : cellA X (b + 8) 8 size) by zcell; assert (Ctb' : cellA X (tmp + 24) 8 tbytes) by zcell end.
      zld F_554ec D_554ec (b + 8) Csize2.
      zld F_554f0 D_554f0 (tmp + 24) Ctb'.
      zstep F_554f4 D_554f4.
      zsd F_554f8 D_554f8 (tmp + 24) (tbytes + size) ltac:(rewok Wt).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cgb2 : cellA X (0x142d70 + 184) 8 (gbytes - size)) by zcell end.
      zld F_554fc D_554fc (0x142d70 + 184) Cgb2.
      zstep F_55500 D_55500. zstep F_55504 D_55504. zstep F_55508 D_55508.
      apply mst_refl. }
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
    split. { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
    split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|].
    split; [zcell|]. split; [replace (gc - 1) with (gc + -1) by lia; zcell|]. split; [zcell|]. split; [zcell|].
    split; [intros _; zcell|]. split; [intros X; exfalso; lia|].
    split; [intros X; exfalso; lia|]. split; [intros _; split; zcell|]. zcell.
  - rewrite (proj2 (Z.eqb_eq k 0) K0). eexists. eexists. split.
    { zbft F_55510 D_55510.
      zld F_55514 D_55514 b Cnext.
      zsd F_55518 D_55518 (0x142d70 + 168) next ltac:(rewok Wq).
      zbtk F_5551c D_5551c.
      zstep F_55524 D_55524.
      zsd F_55528 D_55528 (0x142d70 + 160) (gc + -1) ltac:(rewok Wq).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize' : cellA X (b + 8) 8 size) by zcell; assert (Cgb' : cellA X (0x142d70 + 184) 8 gbytes) by zcell end.
      zld F_5552c D_5552c (b + 8) Csize'.
      zld F_55530 D_55530 (0x142d70 + 184) Cgb'.
      zstep F_55534 D_55534.
      zsd F_55538 D_55538 (0x142d70 + 184) (gbytes - size) ltac:(rewok Wq).
      zstep F_5553c D_5553c.
      zsd F_55540 D_55540 b 0 ltac:(rewok Wb).
      zbft F_55544 D_55544.
      stepn F_55548 D_55548.
      zsd F_5555c D_5555c (tmp + 8) b ltac:(rewok Wt).
      stepn F_55560 D_55560.
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize2 : cellA X (b + 8) 8 size) by zcell; assert (Ctb' : cellA X (tmp + 24) 8 tbytes) by zcell end.
      zld F_554ec D_554ec (b + 8) Csize2.
      zld F_554f0 D_554f0 (tmp + 24) Ctb'.
      zstep F_554f4 D_554f4.
      zsd F_554f8 D_554f8 (tmp + 24) (tbytes + size) ltac:(rewok Wt).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cgb2 : cellA X (0x142d70 + 184) 8 (gbytes - size)) by zcell end.
      zld F_554fc D_554fc (0x142d70 + 184) Cgb2.
      zstep F_55500 D_55500. zstep F_55504 D_55504. zstep F_55508 D_55508.
      apply mst_refl. }
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
    split. { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
    split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|].
    split; [zcell|]. split; [replace (gc - 1) with (gc + -1) by lia; zcell|]. split; [zcell|]. split; [zcell|].
    split; [intros X; exfalso; lia|]. split; [intros _; zcell|].
    split; [intros _; zcell|]. split; [intros X; exfalso; lia|]. zcell.
  - destruct (Hpl K1) as (Hp0 & Hp1 & Apb & Apt & Wpl). unfold apart in Apb, Apt. rewrite (proj2 (Z.eqb_neq k 0) K1). eexists. eexists. split.
    { zbft F_55510 D_55510.
      zld F_55514 D_55514 b Cnext.
      zsd F_55518 D_55518 (0x142d70 + 168) next ltac:(rewok Wq).
      zbtk F_5551c D_5551c.
      zstep F_55524 D_55524.
      zsd F_55528 D_55528 (0x142d70 + 160) (gc + -1) ltac:(rewok Wq).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize' : cellA X (b + 8) 8 size) by zcell; assert (Cgb' : cellA X (0x142d70 + 184) 8 gbytes) by zcell end.
      zld F_5552c D_5552c (b + 8) Csize'.
      zld F_55530 D_55530 (0x142d70 + 184) Cgb'.
      zstep F_55534 D_55534.
      zsd F_55538 D_55538 (0x142d70 + 184) (gbytes - size) ltac:(rewok Wq).
      zstep F_5553c D_5553c.
      zsd F_55540 D_55540 b 0 ltac:(rewok Wb).
      zbtk F_55544 D_55544.
      zsd F_554e8 D_554e8 plast b ltac:(rewok Wpl).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize2 : cellA X (b + 8) 8 size) by zcell; assert (Ctb' : cellA X (tmp + 24) 8 tbytes) by zcell end.
      zld F_554ec D_554ec (b + 8) Csize2.
      zld F_554f0 D_554f0 (tmp + 24) Ctb'.
      zstep F_554f4 D_554f4.
      zsd F_554f8 D_554f8 (tmp + 24) (tbytes + size) ltac:(rewok Wt).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cgb2 : cellA X (0x142d70 + 184) 8 (gbytes - size)) by zcell end.
      zld F_554fc D_554fc (0x142d70 + 184) Cgb2.
      zstep F_55500 D_55500. zstep F_55504 D_55504. zstep F_55508 D_55508.
      apply mst_refl. }
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
    split. { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
    split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|].
    split; [zcell|]. split; [replace (gc - 1) with (gc + -1) by lia; zcell|]. split; [zcell|]. split; [zcell|].
    split; [intros X; exfalso; lia|]. split; [intros _; zcell|].
    split; [intros X; exfalso; lia|]. split; [intros _; split; zcell|]. zcell.
Qed.

#[using="Type"] Lemma art_rcy_more : forall regs (M rom : word -> option byte) (mn gb : Z),
  getr regs 11 = Z_to_bv 64 mn -> getr regs 7 = Z_to_bv 64 gb -> 0 <= mn < gb -> gb < 2 ^ 64 ->
  exists regs', msteps ASEGS (mkst regs (0x5555c : word) M rom) (mkst regs' (0x55560 : word) M rom) /\ (forall r : reg, getr regs' r = getr regs r).
Proof.
  intros regs M rom mn gb H11 H7 Hmn Hgb. eexists. split. { zbft F_5550c D_5550c. apply mst_refl. } intros r. reflexivity.
Qed.
#[using="Type"] Lemma art_rcy_exit : forall regs (M rom : word -> option byte) (mn gb : Z),
  getr regs 11 = Z_to_bv 64 mn -> getr regs 7 = Z_to_bv 64 gb -> 0 <= gb <= mn -> mn < 2 ^ 64 ->
  exists regs', msteps ASEGS (mkst regs (0x5555c : word) M rom) (mkst regs' (0x555b4 : word) M rom) /\ (forall r : reg, getr regs' r = getr regs r).
Proof.
  intros regs M rom mn gb H11 H7 Hmn Hgb. eexists. split. { zbtk F_5550c D_5550c. apply mst_refl. } intros r. reflexivity.
Qed.

Definition art_rcy_tail_mem (M : word -> option byte) (tmp k b : Z) : word -> option byte :=
  Wn 1 (Wn 1 (Wn 8 (Wn 8 M tmp k) (tmp + 16) b) (0x142d70 + 152) 0) (0x142d70 + 153) 0.

#[using="Type"] Lemma art_rcy_tail : forall regs (M rom : word -> option byte) (tmp k b : Z),
  getr regs 2 = Z_to_bv 64 tmp -> getr regs 10 = Z_to_bv 64 0x142d70 -> getr regs 14 = Z_to_bv 64 k -> getr regs 6 = Z_to_bv 64 b ->
  0x69c000 <= tmp -> tmp + 32 < 2 ^ 64 -> 0 <= k < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> wrA M tmp 32 -> wrA M (0x142d70 + 152) 4 ->
  exists regs', msteps ASEGS (mkst regs (0x555b4 : word) M rom) (mkst regs' (0x557cc : word) (art_rcy_tail_mem M tmp k b) rom)
    /\ getr regs' 1 = (0x555d4 : bv 64)%bv /\ getr regs' 11 = Z_to_bv 64 tmp
    /\ (forall r : reg, In r [2; 3; 4; 8; 9; 10; 12; 13; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom tmp k b H2 H10 H14 H6 Htmp Htmp' Hk Hb Wt Wq.
  eexists. split.
  { zsd F_55564 D_55564 tmp k ltac:(rewok Wt).
    zsd F_55568 D_55568 (tmp + 16) b ltac:(rewok Wt).
    stepfence F_5556c D_5556c.
    zsb F_55570 D_55570 (0x142d70 + 152) 0 ltac:(zwok').
    stepfence F_55574 D_55574.
    zsb F_55578 D_55578 (0x142d70 + 153) 0 ltac:(zwok').
    zstep F_5557c D_5557c.
    stepn F_55580 D_55580.
    unfold art_rcy_tail_mem. apply mst_refl. }
  split; [gres; bveq|]. split; [gres; f_equal; lia|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

#[using="Type"] Lemma art_rcy_tail_mem_facts : forall (M : word -> option byte) tmp k b, 0x69c000 <= tmp -> tmp + 32 < 2 ^ 64 -> cellA M (0x142d70 + 152) 4 257 ->
  mem_grows M (art_rcy_tail_mem M tmp k b) /\ art_agree [(tmp, 8); (tmp + 16, 8); (0x142d70 + 152, 4)] M (art_rcy_tail_mem M tmp k b)
  /\ cellA (art_rcy_tail_mem M tmp k b) tmp 8 k /\ cellA (art_rcy_tail_mem M tmp k b) (tmp + 16) 8 b /\ cellA (art_rcy_tail_mem M tmp k b) (0x142d70 + 152) 4 0.
Proof.
  intros M tmp k b Htmp Htmp' Clk. unfold art_rcy_tail_mem.
  split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|]. split; [zcell|]. split; [zcell|].
  change (cellA (Wn 1 (Wn 1 (Wn 8 (Wn 8 M tmp k) (tmp + 16) b) (0x142d70 + 152) 0) (0x142d70 + 153) 0) (0x142d70 + 152) 4 (0 + 256 * 0 + 65536 * 0)).
  apply cell4_join; [lia|lia|lia|lia|lia| | | ].
  - zcell.
  - zcell.
  - destruct (cell4_split M (0x142d70 + 152) 257 ltac:(lia) ltac:(lia) ltac:(lia) Clk) as (_ & _ & C2). change (257 / 65536) with 0 in C2. zcell.
Qed.

#[using="Type"] Lemma art_rcy_epi : forall regs (M rom : word -> option byte) (raw : word) (sp g8 g9 g18 g19 g20 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 80) -> ret_ok raw -> 80 <= sp -> sp < 2 ^ 64 ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 g8 -> cellA M (sp - 24) 8 g9 -> cellA M (sp - 32) 8 g18 -> cellA M (sp - 40) 8 g19 -> cellA M (sp - 48) 8 g20 ->
  exists regs', msteps ASEGS (mkst regs (0x555d4 : word) M rom) (mkst regs' raw M rom)
    /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 8 = Z_to_bv 64 g8 /\ getr regs' 9 = Z_to_bv 64 g9 /\ getr regs' 18 = Z_to_bv 64 g18
    /\ getr regs' 19 = Z_to_bv 64 g19 /\ getr regs' 20 = Z_to_bv 64 g20
    /\ (forall r : reg, In r [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp g8 g9 g18 g19 g20 H2 Hret Hsp Hsp' F1 F8 F9 F18 F19 F20.
  eexists. split.
  { zld F_55584 D_55584 (sp - 8) F1. rewrite Z_to_bv_bv_unsigned.
    zld F_55588 D_55588 (sp - 16) F8. zld F_5558c D_5558c (sp - 24) F9. zld F_55590 D_55590 (sp - 32) F18. zld F_55594 D_55594 (sp - 40) F19. zld F_55598 D_55598 (sp - 48) F20.
    zstep F_5559c D_5559c.
    stepret F_555a0 D_555a0 raw ltac:(reflexivity).
    apply mst_refl. }
  split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
  split; [gres; reflexivity|]. split; [gres; reflexivity|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.
End FPX.
