(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac Pm8ArtLeaf Pm8ArtAllocG Pm8ArtPoison ArtRuns ArtRunsMem Pm8ArtFp Pm8ArtFree1 Pm8ArtCellEx Pm8ArtRecycle4.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm8_code_5b000_5c000.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_rcy_head_mem (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
  Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18)))
    (sp - 40) (U (getr regs 19))) (sp - 48) (U (getr regs 20))) (sp - 80) 0) (sp - 72) 0) (sp - 64) 0) (sp - 56) 0) (0x159630 + 152) 257.

Section FPX. Context {fx : PropExec.FPState}.

Lemma art_rcy_head : forall regs (M rom : word -> option byte) (raw : word) (sp mn cnt gbytes gfirst : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 0x159630 -> getr regs 11 = Z_to_bv 64 mn ->
  0x6b3000 + 80 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 80) 80 -> wrA M (0x159630 + 152) 4 ->
  1 <= cnt -> 16384 * cnt <= gbytes -> gbytes < 2 ^ 57 -> 0 <= mn < gbytes -> 0 <= gfirst < 2 ^ 64 ->
  cellA M (0x159630 + 152) 4 256 -> cellA M (0x159630 + 184) 8 gbytes -> cellA M (0x159630 + 160) 8 cnt -> cellA M (0x159630 + 168) 8 gfirst ->
  exists regs', msteps ASEGS (mkst regs (0x5b2cc : word) M rom) (mkst regs' (0x5b3c8 : word) (art_rcy_head_mem M sp raw regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (sp - 80) /\ getr regs' 10 = Z_to_bv 64 0x159630 /\ getr regs' 11 = Z_to_bv 64 mn /\ getr regs' 14 = Z_to_bv 64 0 /\ getr regs' 15 = Z_to_bv 64 0
    /\ getr regs' 16 = Z_to_bv 64 cnt /\ getr regs' 5 = Z_to_bv 64 gfirst
    /\ (forall r : reg, In r [1; 3; 4; 8; 9; 12; 13; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp mn cnt gbytes gfirst H1 H2 H10 H11 Hsp Hsp' W Wlk Hcnt Hmerge Hgb Hmn Hgf Clk Cgb Ccnt Cgf.
  eexists. split.
  { zstep F_5b27c D_5b27c.
    zsd F_5b280 D_5b280 (sp - 8) (U raw) ltac:(rewok W). zsd F_5b284 D_5b284 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_5b288 D_5b288 (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_5b28c D_5b28c (sp - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_5b290 D_5b290 (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_5b294 D_5b294 (sp - 48) (U (getr regs 20)) ltac:(rewok W).
    zsd F_5b298 D_5b298 (sp - 80) 0 ltac:(rewok W). zsd F_5b29c D_5b29c (sp - 72) 0 ltac:(rewok W).
    zsd F_5b2a0 D_5b2a0 (sp - 64) 0 ltac:(rewok W). zsd F_5b2a4 D_5b2a4 (sp - 56) 0 ltac:(rewok W).
    zstep F_5b2a8 D_5b2a8. zstep F_5b2ac D_5b2ac.
    stepn F_5b2b0 D_5b2b0. rwH. zclosed (0x159630 + 152).
    zstep F_5b2b4 D_5b2b4.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Clk' : cellA X (0x159630 + 152) 4 256) by zcell; assert (Wlk' : wokA X (0x159630 + 152) 4) by zwok end.
    zcas6 F_5b2b8 D_5b2b8 F_5b2bc D_5b2bc F_5b2c0 D_5b2c0 F_5b2c4 D_5b2c4 F_5b2c8 D_5b2c8 F_5b2cc D_5b2cc (0x159630 + 152) 256 257 1 257 Clk' Wlk'.
    zbft F_5b2d0 D_5b2d0.
    stepn F_5b2d4 D_5b2d4. rwH. zclosed 0.
    zbft F_5b2d8 D_5b2d8.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cgb' : cellA X (0x159630 + 184) 8 gbytes) by zcell; assert (Ccnt' : cellA X (0x159630 + 160) 8 cnt) by zcell;
      assert (Cgf' : cellA X (0x159630 + 168) 8 gfirst) by zcell;
      assert (T0 : cellA X (sp - 80) 8 0) by zcell; assert (T16 : cellA X (sp - 64) 8 0) by zcell end.
    zld F_5b2dc D_5b2dc (0x159630 + 184) Cgb'.
    zld F_5b2e0 D_5b2e0 (0x159630 + 160) Ccnt'.
    zstep F_5b2e4 D_5b2e4.
    zbft F_5b2e8 D_5b2e8.
    zbft F_5b2ec D_5b2ec.
    stepn F_5b2f0 D_5b2f0. zcl4.
    zstep F_5b2f4 D_5b2f4. zstep F_5b2f8 D_5b2f8. zstep F_5b2fc D_5b2fc.
    zbtk F_5b300 D_5b300.
    zld F_5b338 D_5b338 (sp - 80) T0.
    zld F_5b33c D_5b33c (sp - 64) T16.
    zld F_5b340 D_5b340 (0x159630 + 184) Cgb'.
    zbft F_5b344 D_5b344.
    zld F_5b348 D_5b348 (0x159630 + 168) Cgf'.
    stepn F_5b34c D_5b34c.
    unfold art_rcy_head_mem. apply mst_refl. }
  split; [gres; reflexivity|]. split; [gres; exact H10|]. split; [gres; exact H11|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
  split; [gres; reflexivity|]. split; [gres; reflexivity|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

Lemma art_rcy_pop : forall regs (M rom : word -> option byte) (tmp k plast gc b next size gbytes glast tbytes tfirst : Z),
  getr regs 10 = Z_to_bv 64 0x159630 -> getr regs 14 = Z_to_bv 64 k -> getr regs 15 = Z_to_bv 64 plast -> getr regs 16 = Z_to_bv 64 gc -> getr regs 5 = Z_to_bv 64 b ->
  getr regs 2 = Z_to_bv 64 tmp ->
  0x6b3000 <= tmp -> tmp + 32 < 2 ^ 64 -> 0x6b3000 <= b -> b + 8192 < 2 ^ 64 -> apart tmp 32 b 8192 -> 0 <= k < 2 ^ 63 -> 1 <= gc < 2 ^ 64 ->
  0 <= next < 2 ^ 64 -> 0 <= size < 2 ^ 64 -> 0 <= gbytes < 2 ^ 64 -> 0 <= tbytes < 2 ^ 64 ->
  (k <> 0 -> 0x6b3000 <= plast /\ plast + 8 < 2 ^ 64 /\ apart plast 8 b 8192 /\ apart plast 8 tmp 32 /\ wrA M plast 8) ->
  wrA M tmp 32 -> wrA M (0x159630 + 160) 32 -> wrA M b 8 ->
  cellA M b 8 next -> cellA M (b + 8) 8 size -> cellA M (0x159630 + 184) 8 gbytes -> cellA M (0x159630 + 176) 8 glast -> cellA M (tmp + 24) 8 tbytes -> cellA M (tmp + 8) 8 tfirst ->
  exists regs' (M' : word -> option byte), msteps ASEGS (mkst regs (0x5b3c8 : word) M rom) (mkst regs' (0x5b3c4 : word) M' rom)
    /\ getr regs' 14 = Z_to_bv 64 (k + 1) /\ getr regs' 15 = Z_to_bv 64 b /\ getr regs' 5 = Z_to_bv 64 next /\ getr regs' 7 = Z_to_bv 64 (gbytes - size) /\ getr regs' 16 = Z_to_bv 64 (gc - 1) /\ getr regs' 6 = Z_to_bv 64 b
    /\ (forall r : reg, In r [1; 2; 3; 4; 8; 9; 10; 11; 12; 13; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r)
    /\ mem_grows M M' /\ art_agree [(0x159630 + 160, 32); (b, 8); (tmp, 32); (plast, if k =? 0 then 0 else 8)] M M'
    /\ cellA M' (0x159630 + 168) 8 next /\ cellA M' (0x159630 + 160) 8 (gc - 1) /\ cellA M' (0x159630 + 184) 8 (gbytes - size) /\ cellA M' b 8 0
    /\ (next = 0 -> cellA M' (0x159630 + 176) 8 0) /\ (next <> 0 -> cellA M' (0x159630 + 176) 8 glast)
    /\ (k = 0 -> cellA M' (tmp + 8) 8 b) /\ (k <> 0 -> cellA M' (tmp + 8) 8 tfirst /\ cellA M' plast 8 b)
    /\ cellA M' (tmp + 24) 8 (tbytes + size).
Proof.
  intros regs M rom tmp k plast gc b next size gbytes glast tbytes tfirst H10 H14 H15 H16 H5 H2 Htmp Htmp' Hb Hb' Atb Hk Hgc Hnext Hsize Hgb Htb Hpl Wt Wq Wb
    Cnext Csize Cgb Cgl Ctb Ctf.
  unfold apart in Atb.
  destruct (Z.eq_dec next 0) as [N0|N1]; destruct (Z.eq_dec k 0) as [K0|K1].
  - rewrite (proj2 (Z.eqb_eq k 0) K0). eexists. eexists. split.
    { zbft F_5b378 D_5b378.
      zld F_5b37c D_5b37c b Cnext.
      zsd F_5b380 D_5b380 (0x159630 + 168) next ltac:(rewok Wq).
      zbft F_5b384 D_5b384.
      zsd F_5b388 D_5b388 (0x159630 + 176) 0 ltac:(rewok Wq).
      zstep F_5b38c D_5b38c.
      zsd F_5b390 D_5b390 (0x159630 + 160) (gc + -1) ltac:(rewok Wq).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize' : cellA X (b + 8) 8 size) by zcell; assert (Cgb' : cellA X (0x159630 + 184) 8 gbytes) by zcell end.
      zld F_5b394 D_5b394 (b + 8) Csize'.
      zld F_5b398 D_5b398 (0x159630 + 184) Cgb'.
      zstep F_5b39c D_5b39c.
      zsd F_5b3a0 D_5b3a0 (0x159630 + 184) (gbytes - size) ltac:(rewok Wq).
      zstep F_5b3a4 D_5b3a4.
      zsd F_5b3a8 D_5b3a8 b 0 ltac:(rewok Wb).
      zbft F_5b3ac D_5b3ac.
      stepn F_5b3b0 D_5b3b0.
      zsd F_5b3c4 D_5b3c4 (tmp + 8) b ltac:(rewok Wt).
      stepn F_5b3c8 D_5b3c8.
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize2 : cellA X (b + 8) 8 size) by zcell; assert (Ctb' : cellA X (tmp + 24) 8 tbytes) by zcell end.
      zld F_5b354 D_5b354 (b + 8) Csize2.
      zld F_5b358 D_5b358 (tmp + 24) Ctb'.
      zstep F_5b35c D_5b35c.
      zsd F_5b360 D_5b360 (tmp + 24) (tbytes + size) ltac:(rewok Wt).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cgb2 : cellA X (0x159630 + 184) 8 (gbytes - size)) by zcell end.
      zld F_5b364 D_5b364 (0x159630 + 184) Cgb2.
      zstep F_5b368 D_5b368. zstep F_5b36c D_5b36c. zstep F_5b370 D_5b370.
      apply mst_refl. }
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
    split. { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
    split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|].
    split; [zcell|]. split; [replace (gc - 1) with (gc + -1) by lia; zcell|]. split; [zcell|]. split; [zcell|].
    split; [intros _; zcell|]. split; [intros X; exfalso; lia|].
    split; [intros _; zcell|]. split; [intros X; exfalso; lia|]. zcell.
  - destruct (Hpl K1) as (Hp0 & Hp1 & Apb & Apt & Wpl). unfold apart in Apb, Apt. rewrite (proj2 (Z.eqb_neq k 0) K1). eexists. eexists. split.
    { zbft F_5b378 D_5b378.
      zld F_5b37c D_5b37c b Cnext.
      zsd F_5b380 D_5b380 (0x159630 + 168) next ltac:(rewok Wq).
      zbft F_5b384 D_5b384.
      zsd F_5b388 D_5b388 (0x159630 + 176) 0 ltac:(rewok Wq).
      zstep F_5b38c D_5b38c.
      zsd F_5b390 D_5b390 (0x159630 + 160) (gc + -1) ltac:(rewok Wq).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize' : cellA X (b + 8) 8 size) by zcell; assert (Cgb' : cellA X (0x159630 + 184) 8 gbytes) by zcell end.
      zld F_5b394 D_5b394 (b + 8) Csize'.
      zld F_5b398 D_5b398 (0x159630 + 184) Cgb'.
      zstep F_5b39c D_5b39c.
      zsd F_5b3a0 D_5b3a0 (0x159630 + 184) (gbytes - size) ltac:(rewok Wq).
      zstep F_5b3a4 D_5b3a4.
      zsd F_5b3a8 D_5b3a8 b 0 ltac:(rewok Wb).
      zbtk F_5b3ac D_5b3ac.
      zsd F_5b350 D_5b350 plast b ltac:(rewok Wpl).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize2 : cellA X (b + 8) 8 size) by zcell; assert (Ctb' : cellA X (tmp + 24) 8 tbytes) by zcell end.
      zld F_5b354 D_5b354 (b + 8) Csize2.
      zld F_5b358 D_5b358 (tmp + 24) Ctb'.
      zstep F_5b35c D_5b35c.
      zsd F_5b360 D_5b360 (tmp + 24) (tbytes + size) ltac:(rewok Wt).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cgb2 : cellA X (0x159630 + 184) 8 (gbytes - size)) by zcell end.
      zld F_5b364 D_5b364 (0x159630 + 184) Cgb2.
      zstep F_5b368 D_5b368. zstep F_5b36c D_5b36c. zstep F_5b370 D_5b370.
      apply mst_refl. }
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
    split. { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
    split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|].
    split; [zcell|]. split; [replace (gc - 1) with (gc + -1) by lia; zcell|]. split; [zcell|]. split; [zcell|].
    split; [intros _; zcell|]. split; [intros X; exfalso; lia|].
    split; [intros X; exfalso; lia|]. split; [intros _; split; zcell|]. zcell.
  - rewrite (proj2 (Z.eqb_eq k 0) K0). eexists. eexists. split.
    { zbft F_5b378 D_5b378.
      zld F_5b37c D_5b37c b Cnext.
      zsd F_5b380 D_5b380 (0x159630 + 168) next ltac:(rewok Wq).
      zbtk F_5b384 D_5b384.
      zstep F_5b38c D_5b38c.
      zsd F_5b390 D_5b390 (0x159630 + 160) (gc + -1) ltac:(rewok Wq).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize' : cellA X (b + 8) 8 size) by zcell; assert (Cgb' : cellA X (0x159630 + 184) 8 gbytes) by zcell end.
      zld F_5b394 D_5b394 (b + 8) Csize'.
      zld F_5b398 D_5b398 (0x159630 + 184) Cgb'.
      zstep F_5b39c D_5b39c.
      zsd F_5b3a0 D_5b3a0 (0x159630 + 184) (gbytes - size) ltac:(rewok Wq).
      zstep F_5b3a4 D_5b3a4.
      zsd F_5b3a8 D_5b3a8 b 0 ltac:(rewok Wb).
      zbft F_5b3ac D_5b3ac.
      stepn F_5b3b0 D_5b3b0.
      zsd F_5b3c4 D_5b3c4 (tmp + 8) b ltac:(rewok Wt).
      stepn F_5b3c8 D_5b3c8.
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize2 : cellA X (b + 8) 8 size) by zcell; assert (Ctb' : cellA X (tmp + 24) 8 tbytes) by zcell end.
      zld F_5b354 D_5b354 (b + 8) Csize2.
      zld F_5b358 D_5b358 (tmp + 24) Ctb'.
      zstep F_5b35c D_5b35c.
      zsd F_5b360 D_5b360 (tmp + 24) (tbytes + size) ltac:(rewok Wt).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cgb2 : cellA X (0x159630 + 184) 8 (gbytes - size)) by zcell end.
      zld F_5b364 D_5b364 (0x159630 + 184) Cgb2.
      zstep F_5b368 D_5b368. zstep F_5b36c D_5b36c. zstep F_5b370 D_5b370.
      apply mst_refl. }
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
    split. { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
    split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|].
    split; [zcell|]. split; [replace (gc - 1) with (gc + -1) by lia; zcell|]. split; [zcell|]. split; [zcell|].
    split; [intros X; exfalso; lia|]. split; [intros _; zcell|].
    split; [intros _; zcell|]. split; [intros X; exfalso; lia|]. zcell.
  - destruct (Hpl K1) as (Hp0 & Hp1 & Apb & Apt & Wpl). unfold apart in Apb, Apt. rewrite (proj2 (Z.eqb_neq k 0) K1). eexists. eexists. split.
    { zbft F_5b378 D_5b378.
      zld F_5b37c D_5b37c b Cnext.
      zsd F_5b380 D_5b380 (0x159630 + 168) next ltac:(rewok Wq).
      zbtk F_5b384 D_5b384.
      zstep F_5b38c D_5b38c.
      zsd F_5b390 D_5b390 (0x159630 + 160) (gc + -1) ltac:(rewok Wq).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize' : cellA X (b + 8) 8 size) by zcell; assert (Cgb' : cellA X (0x159630 + 184) 8 gbytes) by zcell end.
      zld F_5b394 D_5b394 (b + 8) Csize'.
      zld F_5b398 D_5b398 (0x159630 + 184) Cgb'.
      zstep F_5b39c D_5b39c.
      zsd F_5b3a0 D_5b3a0 (0x159630 + 184) (gbytes - size) ltac:(rewok Wq).
      zstep F_5b3a4 D_5b3a4.
      zsd F_5b3a8 D_5b3a8 b 0 ltac:(rewok Wb).
      zbtk F_5b3ac D_5b3ac.
      zsd F_5b350 D_5b350 plast b ltac:(rewok Wpl).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize2 : cellA X (b + 8) 8 size) by zcell; assert (Ctb' : cellA X (tmp + 24) 8 tbytes) by zcell end.
      zld F_5b354 D_5b354 (b + 8) Csize2.
      zld F_5b358 D_5b358 (tmp + 24) Ctb'.
      zstep F_5b35c D_5b35c.
      zsd F_5b360 D_5b360 (tmp + 24) (tbytes + size) ltac:(rewok Wt).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cgb2 : cellA X (0x159630 + 184) 8 (gbytes - size)) by zcell end.
      zld F_5b364 D_5b364 (0x159630 + 184) Cgb2.
      zstep F_5b368 D_5b368. zstep F_5b36c D_5b36c. zstep F_5b370 D_5b370.
      apply mst_refl. }
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
    split. { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
    split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|].
    split; [zcell|]. split; [replace (gc - 1) with (gc + -1) by lia; zcell|]. split; [zcell|]. split; [zcell|].
    split; [intros X; exfalso; lia|]. split; [intros _; zcell|].
    split; [intros X; exfalso; lia|]. split; [intros _; split; zcell|]. zcell.
Qed.

Lemma art_rcy_more : forall regs (M rom : word -> option byte) (mn gb : Z),
  getr regs 11 = Z_to_bv 64 mn -> getr regs 7 = Z_to_bv 64 gb -> 0 <= mn < gb -> gb < 2 ^ 64 ->
  exists regs', msteps ASEGS (mkst regs (0x5b3c4 : word) M rom) (mkst regs' (0x5b3c8 : word) M rom) /\ (forall r : reg, getr regs' r = getr regs r).
Proof.
  intros regs M rom mn gb H11 H7 Hmn Hgb. eexists. split. { zbft F_5b374 D_5b374. apply mst_refl. } intros r. reflexivity.
Qed.
Lemma art_rcy_exit : forall regs (M rom : word -> option byte) (mn gb : Z),
  getr regs 11 = Z_to_bv 64 mn -> getr regs 7 = Z_to_bv 64 gb -> 0 <= gb <= mn -> mn < 2 ^ 64 ->
  exists regs', msteps ASEGS (mkst regs (0x5b3c4 : word) M rom) (mkst regs' (0x5b41c : word) M rom) /\ (forall r : reg, getr regs' r = getr regs r).
Proof.
  intros regs M rom mn gb H11 H7 Hmn Hgb. eexists. split. { zbtk F_5b374 D_5b374. apply mst_refl. } intros r. reflexivity.
Qed.

Definition art_rcy_tail_mem (M : word -> option byte) (tmp k b : Z) : word -> option byte :=
  Wn 1 (Wn 1 (Wn 8 (Wn 8 M tmp k) (tmp + 16) b) (0x159630 + 152) 0) (0x159630 + 153) 0.

Lemma art_rcy_tail : forall regs (M rom : word -> option byte) (tmp k b : Z),
  getr regs 2 = Z_to_bv 64 tmp -> getr regs 10 = Z_to_bv 64 0x159630 -> getr regs 14 = Z_to_bv 64 k -> getr regs 6 = Z_to_bv 64 b ->
  0x6b3000 <= tmp -> tmp + 32 < 2 ^ 64 -> 0 <= k < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> wrA M tmp 32 -> wrA M (0x159630 + 152) 4 ->
  exists regs', msteps ASEGS (mkst regs (0x5b41c : word) M rom) (mkst regs' (0x5b634 : word) (art_rcy_tail_mem M tmp k b) rom)
    /\ getr regs' 1 = (0x5b43c : bv 64)%bv /\ getr regs' 11 = Z_to_bv 64 tmp
    /\ (forall r : reg, In r [2; 3; 4; 8; 9; 10; 12; 13; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom tmp k b H2 H10 H14 H6 Htmp Htmp' Hk Hb Wt Wq.
  eexists. split.
  { zsd F_5b3cc D_5b3cc tmp k ltac:(rewok Wt).
    zsd F_5b3d0 D_5b3d0 (tmp + 16) b ltac:(rewok Wt).
    stepfence F_5b3d4 D_5b3d4.
    zsb F_5b3d8 D_5b3d8 (0x159630 + 152) 0 ltac:(zwok').
    stepfence F_5b3dc D_5b3dc.
    zsb F_5b3e0 D_5b3e0 (0x159630 + 153) 0 ltac:(zwok').
    zstep F_5b3e4 D_5b3e4.
    stepn F_5b3e8 D_5b3e8.
    unfold art_rcy_tail_mem. apply mst_refl. }
  split; [gres; bveq|]. split; [gres; f_equal; lia|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

Lemma art_rcy_tail_mem_facts : forall (M : word -> option byte) tmp k b, 0x6b3000 <= tmp -> tmp + 32 < 2 ^ 64 -> cellA M (0x159630 + 152) 4 257 ->
  mem_grows M (art_rcy_tail_mem M tmp k b) /\ art_agree [(tmp, 8); (tmp + 16, 8); (0x159630 + 152, 4)] M (art_rcy_tail_mem M tmp k b)
  /\ cellA (art_rcy_tail_mem M tmp k b) tmp 8 k /\ cellA (art_rcy_tail_mem M tmp k b) (tmp + 16) 8 b /\ cellA (art_rcy_tail_mem M tmp k b) (0x159630 + 152) 4 0.
Proof.
  intros M tmp k b Htmp Htmp' Clk. unfold art_rcy_tail_mem.
  split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|]. split; [zcell|]. split; [zcell|].
  change (cellA (Wn 1 (Wn 1 (Wn 8 (Wn 8 M tmp k) (tmp + 16) b) (0x159630 + 152) 0) (0x159630 + 153) 0) (0x159630 + 152) 4 (0 + 256 * 0 + 65536 * 0)).
  apply cell4_join; [lia|lia|lia|lia|lia| | | ].
  - zcell.
  - zcell.
  - destruct (cell4_split M (0x159630 + 152) 257 ltac:(lia) ltac:(lia) ltac:(lia) Clk) as (_ & _ & C2). change (257 / 65536) with 0 in C2. zcell.
Qed.

Lemma art_rcy_epi : forall regs (M rom : word -> option byte) (raw : word) (sp g8 g9 g18 g19 g20 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 80) -> ret_ok raw -> 80 <= sp -> sp < 2 ^ 64 ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 g8 -> cellA M (sp - 24) 8 g9 -> cellA M (sp - 32) 8 g18 -> cellA M (sp - 40) 8 g19 -> cellA M (sp - 48) 8 g20 ->
  exists regs', msteps ASEGS (mkst regs (0x5b43c : word) M rom) (mkst regs' raw M rom)
    /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 8 = Z_to_bv 64 g8 /\ getr regs' 9 = Z_to_bv 64 g9 /\ getr regs' 18 = Z_to_bv 64 g18
    /\ getr regs' 19 = Z_to_bv 64 g19 /\ getr regs' 20 = Z_to_bv 64 g20
    /\ (forall r : reg, In r [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp g8 g9 g18 g19 g20 H2 Hret Hsp Hsp' F1 F8 F9 F18 F19 F20.
  eexists. split.
  { zld F_5b3ec D_5b3ec (sp - 8) F1. rewrite Z_to_bv_bv_unsigned.
    zld F_5b3f0 D_5b3f0 (sp - 16) F8. zld F_5b3f4 D_5b3f4 (sp - 24) F9. zld F_5b3f8 D_5b3f8 (sp - 32) F18. zld F_5b3fc D_5b3fc (sp - 40) F19. zld F_5b400 D_5b400 (sp - 48) F20.
    zstep F_5b404 D_5b404.
    stepret F_5b408 D_5b408 raw ltac:(reflexivity).
    apply mst_refl. }
  split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
  split; [gres; reflexivity|]. split; [gres; reflexivity|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.
End FPX.
