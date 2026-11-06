(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac EatLeaf EatAllocG EatPoison ArtRuns ArtRunsMem EatFp EatFree1 EatCellEx EatRecycle4.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_r3ef18_4052c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_rcy_head_mem (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
  Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18)))
    (sp - 40) (U (getr regs 19))) (sp - 48) (U (getr regs 20))) (sp - 80) 0) (sp - 72) 0) (sp - 64) 0) (sp - 56) 0) (0x13e670 + 152) 257.

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_rcy_head : forall regs (M rom : word -> option byte) (raw : word) (sp mn cnt gbytes gfirst : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 0x13e670 -> getr regs 11 = Z_to_bv 64 mn ->
  0x698000 + 80 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 80) 80 -> wrA M (0x13e670 + 152) 4 ->
  1 <= cnt -> 16384 * cnt <= gbytes -> gbytes < 2 ^ 57 -> 0 <= mn < gbytes -> 0 <= gfirst < 2 ^ 64 ->
  cellA M (0x13e670 + 152) 4 256 -> cellA M (0x13e670 + 184) 8 gbytes -> cellA M (0x13e670 + 160) 8 cnt -> cellA M (0x13e670 + 168) 8 gfirst ->
  exists regs', msteps ASEGS (mkst regs (0x54c3c : word) M rom) (mkst regs' (0x54d38 : word) (art_rcy_head_mem M sp raw regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (sp - 80) /\ getr regs' 10 = Z_to_bv 64 0x13e670 /\ getr regs' 11 = Z_to_bv 64 mn /\ getr regs' 14 = Z_to_bv 64 0 /\ getr regs' 15 = Z_to_bv 64 0
    /\ getr regs' 16 = Z_to_bv 64 cnt /\ getr regs' 5 = Z_to_bv 64 gfirst
    /\ (forall r : reg, In r [1; 3; 4; 8; 9; 12; 13; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp mn cnt gbytes gfirst H1 H2 H10 H11 Hsp Hsp' W Wlk Hcnt Hmerge Hgb Hmn Hgf Clk Cgb Ccnt Cgf.
  eexists. split.
  { zstep F_54bec D_54bec.
    zsd F_54bf0 D_54bf0 (sp - 8) (U raw) ltac:(rewok W). zsd F_54bf4 D_54bf4 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_54bf8 D_54bf8 (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_54bfc D_54bfc (sp - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_54c00 D_54c00 (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_54c04 D_54c04 (sp - 48) (U (getr regs 20)) ltac:(rewok W).
    zsd F_54c08 D_54c08 (sp - 80) 0 ltac:(rewok W). zsd F_54c0c D_54c0c (sp - 72) 0 ltac:(rewok W).
    zsd F_54c10 D_54c10 (sp - 64) 0 ltac:(rewok W). zsd F_54c14 D_54c14 (sp - 56) 0 ltac:(rewok W).
    zstep F_54c18 D_54c18. zstep F_54c1c D_54c1c.
    stepn F_54c20 D_54c20. rwH. zclosed (0x13e670 + 152).
    zstep F_54c24 D_54c24.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Clk' : cellA X (0x13e670 + 152) 4 256) by zcell; assert (Wlk' : wokA X (0x13e670 + 152) 4) by zwok end.
    zcas6 F_54c28 D_54c28 F_54c2c D_54c2c F_54c30 D_54c30 F_54c34 D_54c34 F_54c38 D_54c38 F_54c3c D_54c3c (0x13e670 + 152) 256 257 1 257 Clk' Wlk'.
    zbft F_54c40 D_54c40.
    stepn F_54c44 D_54c44. rwH. zclosed 0.
    zbft F_54c48 D_54c48.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cgb' : cellA X (0x13e670 + 184) 8 gbytes) by zcell; assert (Ccnt' : cellA X (0x13e670 + 160) 8 cnt) by zcell;
      assert (Cgf' : cellA X (0x13e670 + 168) 8 gfirst) by zcell;
      assert (T0 : cellA X (sp - 80) 8 0) by zcell; assert (T16 : cellA X (sp - 64) 8 0) by zcell end.
    zld F_54c4c D_54c4c (0x13e670 + 184) Cgb'.
    zld F_54c50 D_54c50 (0x13e670 + 160) Ccnt'.
    zstep F_54c54 D_54c54.
    zbft F_54c58 D_54c58.
    zbft F_54c5c D_54c5c.
    stepn F_54c60 D_54c60. zcl4.
    zstep F_54c64 D_54c64. zstep F_54c68 D_54c68. zstep F_54c6c D_54c6c.
    zbtk F_54c70 D_54c70.
    zld F_54ca8 D_54ca8 (sp - 80) T0.
    zld F_54cac D_54cac (sp - 64) T16.
    zld F_54cb0 D_54cb0 (0x13e670 + 184) Cgb'.
    zbft F_54cb4 D_54cb4.
    zld F_54cb8 D_54cb8 (0x13e670 + 168) Cgf'.
    stepn F_54cbc D_54cbc.
    unfold art_rcy_head_mem. apply mst_refl. }
  split; [gres; reflexivity|]. split; [gres; exact H10|]. split; [gres; exact H11|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
  split; [gres; reflexivity|]. split; [gres; reflexivity|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

#[using="Type"] Lemma art_rcy_pop : forall regs (M rom : word -> option byte) (tmp k plast gc b next size gbytes glast tbytes tfirst : Z),
  getr regs 10 = Z_to_bv 64 0x13e670 -> getr regs 14 = Z_to_bv 64 k -> getr regs 15 = Z_to_bv 64 plast -> getr regs 16 = Z_to_bv 64 gc -> getr regs 5 = Z_to_bv 64 b ->
  getr regs 2 = Z_to_bv 64 tmp ->
  0x698000 <= tmp -> tmp + 32 < 2 ^ 64 -> 0x698000 <= b -> b + 8192 < 2 ^ 64 -> apart tmp 32 b 8192 -> 0 <= k < 2 ^ 63 -> 1 <= gc < 2 ^ 64 ->
  0 <= next < 2 ^ 64 -> 0 <= size < 2 ^ 64 -> 0 <= gbytes < 2 ^ 64 -> 0 <= tbytes < 2 ^ 64 ->
  (k <> 0 -> 0x698000 <= plast /\ plast + 8 < 2 ^ 64 /\ apart plast 8 b 8192 /\ apart plast 8 tmp 32 /\ wrA M plast 8) ->
  wrA M tmp 32 -> wrA M (0x13e670 + 160) 32 -> wrA M b 8 ->
  cellA M b 8 next -> cellA M (b + 8) 8 size -> cellA M (0x13e670 + 184) 8 gbytes -> cellA M (0x13e670 + 176) 8 glast -> cellA M (tmp + 24) 8 tbytes -> cellA M (tmp + 8) 8 tfirst ->
  exists regs' (M' : word -> option byte), msteps ASEGS (mkst regs (0x54d38 : word) M rom) (mkst regs' (0x54d34 : word) M' rom)
    /\ getr regs' 14 = Z_to_bv 64 (k + 1) /\ getr regs' 15 = Z_to_bv 64 b /\ getr regs' 5 = Z_to_bv 64 next /\ getr regs' 7 = Z_to_bv 64 (gbytes - size) /\ getr regs' 16 = Z_to_bv 64 (gc - 1) /\ getr regs' 6 = Z_to_bv 64 b
    /\ (forall r : reg, In r [1; 2; 3; 4; 8; 9; 10; 11; 12; 13; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r)
    /\ mem_grows M M' /\ art_agree [(0x13e670 + 160, 32); (b, 8); (tmp, 32); (plast, if k =? 0 then 0 else 8)] M M'
    /\ cellA M' (0x13e670 + 168) 8 next /\ cellA M' (0x13e670 + 160) 8 (gc - 1) /\ cellA M' (0x13e670 + 184) 8 (gbytes - size) /\ cellA M' b 8 0
    /\ (next = 0 -> cellA M' (0x13e670 + 176) 8 0) /\ (next <> 0 -> cellA M' (0x13e670 + 176) 8 glast)
    /\ (k = 0 -> cellA M' (tmp + 8) 8 b) /\ (k <> 0 -> cellA M' (tmp + 8) 8 tfirst /\ cellA M' plast 8 b)
    /\ cellA M' (tmp + 24) 8 (tbytes + size).
Proof.
  intros regs M rom tmp k plast gc b next size gbytes glast tbytes tfirst H10 H14 H15 H16 H5 H2 Htmp Htmp' Hb Hb' Atb Hk Hgc Hnext Hsize Hgb Htb Hpl Wt Wq Wb
    Cnext Csize Cgb Cgl Ctb Ctf.
  unfold apart in Atb.
  destruct (Z.eq_dec next 0) as [N0|N1]; destruct (Z.eq_dec k 0) as [K0|K1].
  - rewrite (proj2 (Z.eqb_eq k 0) K0). eexists. eexists. split.
    { zbft F_54ce8 D_54ce8.
      zld F_54cec D_54cec b Cnext.
      zsd F_54cf0 D_54cf0 (0x13e670 + 168) next ltac:(rewok Wq).
      zbft F_54cf4 D_54cf4.
      zsd F_54cf8 D_54cf8 (0x13e670 + 176) 0 ltac:(rewok Wq).
      zstep F_54cfc D_54cfc.
      zsd F_54d00 D_54d00 (0x13e670 + 160) (gc + -1) ltac:(rewok Wq).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize' : cellA X (b + 8) 8 size) by zcell; assert (Cgb' : cellA X (0x13e670 + 184) 8 gbytes) by zcell end.
      zld F_54d04 D_54d04 (b + 8) Csize'.
      zld F_54d08 D_54d08 (0x13e670 + 184) Cgb'.
      zstep F_54d0c D_54d0c.
      zsd F_54d10 D_54d10 (0x13e670 + 184) (gbytes - size) ltac:(rewok Wq).
      zstep F_54d14 D_54d14.
      zsd F_54d18 D_54d18 b 0 ltac:(rewok Wb).
      zbft F_54d1c D_54d1c.
      stepn F_54d20 D_54d20.
      zsd F_54d34 D_54d34 (tmp + 8) b ltac:(rewok Wt).
      stepn F_54d38 D_54d38.
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize2 : cellA X (b + 8) 8 size) by zcell; assert (Ctb' : cellA X (tmp + 24) 8 tbytes) by zcell end.
      zld F_54cc4 D_54cc4 (b + 8) Csize2.
      zld F_54cc8 D_54cc8 (tmp + 24) Ctb'.
      zstep F_54ccc D_54ccc.
      zsd F_54cd0 D_54cd0 (tmp + 24) (tbytes + size) ltac:(rewok Wt).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cgb2 : cellA X (0x13e670 + 184) 8 (gbytes - size)) by zcell end.
      zld F_54cd4 D_54cd4 (0x13e670 + 184) Cgb2.
      zstep F_54cd8 D_54cd8. zstep F_54cdc D_54cdc. zstep F_54ce0 D_54ce0.
      apply mst_refl. }
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
    split. { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
    split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|].
    split; [zcell|]. split; [replace (gc - 1) with (gc + -1) by lia; zcell|]. split; [zcell|]. split; [zcell|].
    split; [intros _; zcell|]. split; [intros X; exfalso; lia|].
    split; [intros _; zcell|]. split; [intros X; exfalso; lia|]. zcell.
  - destruct (Hpl K1) as (Hp0 & Hp1 & Apb & Apt & Wpl). unfold apart in Apb, Apt. rewrite (proj2 (Z.eqb_neq k 0) K1). eexists. eexists. split.
    { zbft F_54ce8 D_54ce8.
      zld F_54cec D_54cec b Cnext.
      zsd F_54cf0 D_54cf0 (0x13e670 + 168) next ltac:(rewok Wq).
      zbft F_54cf4 D_54cf4.
      zsd F_54cf8 D_54cf8 (0x13e670 + 176) 0 ltac:(rewok Wq).
      zstep F_54cfc D_54cfc.
      zsd F_54d00 D_54d00 (0x13e670 + 160) (gc + -1) ltac:(rewok Wq).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize' : cellA X (b + 8) 8 size) by zcell; assert (Cgb' : cellA X (0x13e670 + 184) 8 gbytes) by zcell end.
      zld F_54d04 D_54d04 (b + 8) Csize'.
      zld F_54d08 D_54d08 (0x13e670 + 184) Cgb'.
      zstep F_54d0c D_54d0c.
      zsd F_54d10 D_54d10 (0x13e670 + 184) (gbytes - size) ltac:(rewok Wq).
      zstep F_54d14 D_54d14.
      zsd F_54d18 D_54d18 b 0 ltac:(rewok Wb).
      zbtk F_54d1c D_54d1c.
      zsd F_54cc0 D_54cc0 plast b ltac:(rewok Wpl).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize2 : cellA X (b + 8) 8 size) by zcell; assert (Ctb' : cellA X (tmp + 24) 8 tbytes) by zcell end.
      zld F_54cc4 D_54cc4 (b + 8) Csize2.
      zld F_54cc8 D_54cc8 (tmp + 24) Ctb'.
      zstep F_54ccc D_54ccc.
      zsd F_54cd0 D_54cd0 (tmp + 24) (tbytes + size) ltac:(rewok Wt).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cgb2 : cellA X (0x13e670 + 184) 8 (gbytes - size)) by zcell end.
      zld F_54cd4 D_54cd4 (0x13e670 + 184) Cgb2.
      zstep F_54cd8 D_54cd8. zstep F_54cdc D_54cdc. zstep F_54ce0 D_54ce0.
      apply mst_refl. }
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
    split. { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
    split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|].
    split; [zcell|]. split; [replace (gc - 1) with (gc + -1) by lia; zcell|]. split; [zcell|]. split; [zcell|].
    split; [intros _; zcell|]. split; [intros X; exfalso; lia|].
    split; [intros X; exfalso; lia|]. split; [intros _; split; zcell|]. zcell.
  - rewrite (proj2 (Z.eqb_eq k 0) K0). eexists. eexists. split.
    { zbft F_54ce8 D_54ce8.
      zld F_54cec D_54cec b Cnext.
      zsd F_54cf0 D_54cf0 (0x13e670 + 168) next ltac:(rewok Wq).
      zbtk F_54cf4 D_54cf4.
      zstep F_54cfc D_54cfc.
      zsd F_54d00 D_54d00 (0x13e670 + 160) (gc + -1) ltac:(rewok Wq).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize' : cellA X (b + 8) 8 size) by zcell; assert (Cgb' : cellA X (0x13e670 + 184) 8 gbytes) by zcell end.
      zld F_54d04 D_54d04 (b + 8) Csize'.
      zld F_54d08 D_54d08 (0x13e670 + 184) Cgb'.
      zstep F_54d0c D_54d0c.
      zsd F_54d10 D_54d10 (0x13e670 + 184) (gbytes - size) ltac:(rewok Wq).
      zstep F_54d14 D_54d14.
      zsd F_54d18 D_54d18 b 0 ltac:(rewok Wb).
      zbft F_54d1c D_54d1c.
      stepn F_54d20 D_54d20.
      zsd F_54d34 D_54d34 (tmp + 8) b ltac:(rewok Wt).
      stepn F_54d38 D_54d38.
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize2 : cellA X (b + 8) 8 size) by zcell; assert (Ctb' : cellA X (tmp + 24) 8 tbytes) by zcell end.
      zld F_54cc4 D_54cc4 (b + 8) Csize2.
      zld F_54cc8 D_54cc8 (tmp + 24) Ctb'.
      zstep F_54ccc D_54ccc.
      zsd F_54cd0 D_54cd0 (tmp + 24) (tbytes + size) ltac:(rewok Wt).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cgb2 : cellA X (0x13e670 + 184) 8 (gbytes - size)) by zcell end.
      zld F_54cd4 D_54cd4 (0x13e670 + 184) Cgb2.
      zstep F_54cd8 D_54cd8. zstep F_54cdc D_54cdc. zstep F_54ce0 D_54ce0.
      apply mst_refl. }
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
    split. { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
    split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|].
    split; [zcell|]. split; [replace (gc - 1) with (gc + -1) by lia; zcell|]. split; [zcell|]. split; [zcell|].
    split; [intros X; exfalso; lia|]. split; [intros _; zcell|].
    split; [intros _; zcell|]. split; [intros X; exfalso; lia|]. zcell.
  - destruct (Hpl K1) as (Hp0 & Hp1 & Apb & Apt & Wpl). unfold apart in Apb, Apt. rewrite (proj2 (Z.eqb_neq k 0) K1). eexists. eexists. split.
    { zbft F_54ce8 D_54ce8.
      zld F_54cec D_54cec b Cnext.
      zsd F_54cf0 D_54cf0 (0x13e670 + 168) next ltac:(rewok Wq).
      zbtk F_54cf4 D_54cf4.
      zstep F_54cfc D_54cfc.
      zsd F_54d00 D_54d00 (0x13e670 + 160) (gc + -1) ltac:(rewok Wq).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize' : cellA X (b + 8) 8 size) by zcell; assert (Cgb' : cellA X (0x13e670 + 184) 8 gbytes) by zcell end.
      zld F_54d04 D_54d04 (b + 8) Csize'.
      zld F_54d08 D_54d08 (0x13e670 + 184) Cgb'.
      zstep F_54d0c D_54d0c.
      zsd F_54d10 D_54d10 (0x13e670 + 184) (gbytes - size) ltac:(rewok Wq).
      zstep F_54d14 D_54d14.
      zsd F_54d18 D_54d18 b 0 ltac:(rewok Wb).
      zbtk F_54d1c D_54d1c.
      zsd F_54cc0 D_54cc0 plast b ltac:(rewok Wpl).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize2 : cellA X (b + 8) 8 size) by zcell; assert (Ctb' : cellA X (tmp + 24) 8 tbytes) by zcell end.
      zld F_54cc4 D_54cc4 (b + 8) Csize2.
      zld F_54cc8 D_54cc8 (tmp + 24) Ctb'.
      zstep F_54ccc D_54ccc.
      zsd F_54cd0 D_54cd0 (tmp + 24) (tbytes + size) ltac:(rewok Wt).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cgb2 : cellA X (0x13e670 + 184) 8 (gbytes - size)) by zcell end.
      zld F_54cd4 D_54cd4 (0x13e670 + 184) Cgb2.
      zstep F_54cd8 D_54cd8. zstep F_54cdc D_54cdc. zstep F_54ce0 D_54ce0.
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
  exists regs', msteps ASEGS (mkst regs (0x54d34 : word) M rom) (mkst regs' (0x54d38 : word) M rom) /\ (forall r : reg, getr regs' r = getr regs r).
Proof.
  intros regs M rom mn gb H11 H7 Hmn Hgb. eexists. split. { zbft F_54ce4 D_54ce4. apply mst_refl. } intros r. reflexivity.
Qed.
#[using="Type"] Lemma art_rcy_exit : forall regs (M rom : word -> option byte) (mn gb : Z),
  getr regs 11 = Z_to_bv 64 mn -> getr regs 7 = Z_to_bv 64 gb -> 0 <= gb <= mn -> mn < 2 ^ 64 ->
  exists regs', msteps ASEGS (mkst regs (0x54d34 : word) M rom) (mkst regs' (0x54d8c : word) M rom) /\ (forall r : reg, getr regs' r = getr regs r).
Proof.
  intros regs M rom mn gb H11 H7 Hmn Hgb. eexists. split. { zbtk F_54ce4 D_54ce4. apply mst_refl. } intros r. reflexivity.
Qed.

Definition art_rcy_tail_mem (M : word -> option byte) (tmp k b : Z) : word -> option byte :=
  Wn 1 (Wn 1 (Wn 8 (Wn 8 M tmp k) (tmp + 16) b) (0x13e670 + 152) 0) (0x13e670 + 153) 0.

#[using="Type"] Lemma art_rcy_tail : forall regs (M rom : word -> option byte) (tmp k b : Z),
  getr regs 2 = Z_to_bv 64 tmp -> getr regs 10 = Z_to_bv 64 0x13e670 -> getr regs 14 = Z_to_bv 64 k -> getr regs 6 = Z_to_bv 64 b ->
  0x698000 <= tmp -> tmp + 32 < 2 ^ 64 -> 0 <= k < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> wrA M tmp 32 -> wrA M (0x13e670 + 152) 4 ->
  exists regs', msteps ASEGS (mkst regs (0x54d8c : word) M rom) (mkst regs' (0x54fa4 : word) (art_rcy_tail_mem M tmp k b) rom)
    /\ getr regs' 1 = (0x54dac : bv 64)%bv /\ getr regs' 11 = Z_to_bv 64 tmp
    /\ (forall r : reg, In r [2; 3; 4; 8; 9; 10; 12; 13; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom tmp k b H2 H10 H14 H6 Htmp Htmp' Hk Hb Wt Wq.
  eexists. split.
  { zsd F_54d3c D_54d3c tmp k ltac:(rewok Wt).
    zsd F_54d40 D_54d40 (tmp + 16) b ltac:(rewok Wt).
    stepfence F_54d44 D_54d44.
    zsb F_54d48 D_54d48 (0x13e670 + 152) 0 ltac:(zwok').
    stepfence F_54d4c D_54d4c.
    zsb F_54d50 D_54d50 (0x13e670 + 153) 0 ltac:(zwok').
    zstep F_54d54 D_54d54.
    stepn F_54d58 D_54d58.
    unfold art_rcy_tail_mem. apply mst_refl. }
  split; [gres; bveq|]. split; [gres; f_equal; lia|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

#[using="Type"] Lemma art_rcy_tail_mem_facts : forall (M : word -> option byte) tmp k b, 0x698000 <= tmp -> tmp + 32 < 2 ^ 64 -> cellA M (0x13e670 + 152) 4 257 ->
  mem_grows M (art_rcy_tail_mem M tmp k b) /\ art_agree [(tmp, 8); (tmp + 16, 8); (0x13e670 + 152, 4)] M (art_rcy_tail_mem M tmp k b)
  /\ cellA (art_rcy_tail_mem M tmp k b) tmp 8 k /\ cellA (art_rcy_tail_mem M tmp k b) (tmp + 16) 8 b /\ cellA (art_rcy_tail_mem M tmp k b) (0x13e670 + 152) 4 0.
Proof.
  intros M tmp k b Htmp Htmp' Clk. unfold art_rcy_tail_mem.
  split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|]. split; [zcell|]. split; [zcell|].
  change (cellA (Wn 1 (Wn 1 (Wn 8 (Wn 8 M tmp k) (tmp + 16) b) (0x13e670 + 152) 0) (0x13e670 + 153) 0) (0x13e670 + 152) 4 (0 + 256 * 0 + 65536 * 0)).
  apply cell4_join; [lia|lia|lia|lia|lia| | | ].
  - zcell.
  - zcell.
  - destruct (cell4_split M (0x13e670 + 152) 257 ltac:(lia) ltac:(lia) ltac:(lia) Clk) as (_ & _ & C2). change (257 / 65536) with 0 in C2. zcell.
Qed.

#[using="Type"] Lemma art_rcy_epi : forall regs (M rom : word -> option byte) (raw : word) (sp g8 g9 g18 g19 g20 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 80) -> ret_ok raw -> 80 <= sp -> sp < 2 ^ 64 ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 g8 -> cellA M (sp - 24) 8 g9 -> cellA M (sp - 32) 8 g18 -> cellA M (sp - 40) 8 g19 -> cellA M (sp - 48) 8 g20 ->
  exists regs', msteps ASEGS (mkst regs (0x54dac : word) M rom) (mkst regs' raw M rom)
    /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 8 = Z_to_bv 64 g8 /\ getr regs' 9 = Z_to_bv 64 g9 /\ getr regs' 18 = Z_to_bv 64 g18
    /\ getr regs' 19 = Z_to_bv 64 g19 /\ getr regs' 20 = Z_to_bv 64 g20
    /\ (forall r : reg, In r [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp g8 g9 g18 g19 g20 H2 Hret Hsp Hsp' F1 F8 F9 F18 F19 F20.
  eexists. split.
  { zld F_54d5c D_54d5c (sp - 8) F1. rewrite Z_to_bv_bv_unsigned.
    zld F_54d60 D_54d60 (sp - 16) F8. zld F_54d64 D_54d64 (sp - 24) F9. zld F_54d68 D_54d68 (sp - 32) F18. zld F_54d6c D_54d6c (sp - 40) F19. zld F_54d70 D_54d70 (sp - 48) F20.
    zstep F_54d74 D_54d74.
    stepret F_54d78 D_54d78 raw ltac:(reflexivity).
    apply mst_refl. }
  split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
  split; [gres; reflexivity|]. split; [gres; reflexivity|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.
End FPX.
