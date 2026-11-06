(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac ArtLeaf ArtAllocG ArtPoison ArtRuns ArtRunsMem ArtFp ArtFree1 ArtCellEx ArtRecycle4.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import As0_code_3f03c_40650.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Definition art_rcy_head_mem (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
  Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18)))
    (sp - 40) (U (getr regs 19))) (sp - 48) (U (getr regs 20))) (sp - 80) 0) (sp - 72) 0) (sp - 64) 0) (sp - 56) 0) (0xda7b0 + 152) 257.

Section FPX. Context {fx : PropExec.FPState}.

Lemma art_rcy_head : forall regs (M rom : word -> option byte) (raw : word) (sp mn cnt gbytes gfirst : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 0xda7b0 -> getr regs 11 = Z_to_bv 64 mn ->
  0x633000 + 80 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 80) 80 -> wrA M (0xda7b0 + 152) 4 ->
  1 <= cnt -> 16384 * cnt <= gbytes -> gbytes < 2 ^ 57 -> 0 <= mn < gbytes -> 0 <= gfirst < 2 ^ 64 ->
  cellA M (0xda7b0 + 152) 4 256 -> cellA M (0xda7b0 + 184) 8 gbytes -> cellA M (0xda7b0 + 160) 8 cnt -> cellA M (0xda7b0 + 168) 8 gfirst ->
  exists regs', msteps ASEGS (mkst regs (0x3f1e0 : word) M rom) (mkst regs' (0x3f2dc : word) (art_rcy_head_mem M sp raw regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (sp - 80) /\ getr regs' 10 = Z_to_bv 64 0xda7b0 /\ getr regs' 11 = Z_to_bv 64 mn /\ getr regs' 14 = Z_to_bv 64 0 /\ getr regs' 15 = Z_to_bv 64 0
    /\ getr regs' 16 = Z_to_bv 64 cnt /\ getr regs' 5 = Z_to_bv 64 gfirst
    /\ (forall r : reg, In r [1; 3; 4; 8; 9; 12; 13; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp mn cnt gbytes gfirst H1 H2 H10 H11 Hsp Hsp' W Wlk Hcnt Hmerge Hgb Hmn Hgf Clk Cgb Ccnt Cgf.
  eexists. split.
  { zstep F_3f1e0 D_3f1e0.
    zsd F_3f1e4 D_3f1e4 (sp - 8) (U raw) ltac:(rewok W). zsd F_3f1e8 D_3f1e8 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_3f1ec D_3f1ec (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_3f1f0 D_3f1f0 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_3f1f4 D_3f1f4 (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_3f1f8 D_3f1f8 (sp - 48) (U (getr regs 20)) ltac:(rewok W).
    zsd F_3f1fc D_3f1fc (sp - 80) 0 ltac:(rewok W). zsd F_3f200 D_3f200 (sp - 72) 0 ltac:(rewok W).
    zsd F_3f204 D_3f204 (sp - 64) 0 ltac:(rewok W). zsd F_3f208 D_3f208 (sp - 56) 0 ltac:(rewok W).
    zstep F_3f20c D_3f20c. zstep F_3f210 D_3f210.
    stepn F_3f214 D_3f214. rwH. zclosed (0xda7b0 + 152).
    zstep F_3f218 D_3f218.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Clk' : cellA X (0xda7b0 + 152) 4 256) by zcell; assert (Wlk' : wokA X (0xda7b0 + 152) 4) by zwok end.
    zcas6 F_3f21c D_3f21c F_3f220 D_3f220 F_3f224 D_3f224 F_3f228 D_3f228 F_3f22c D_3f22c F_3f230 D_3f230 (0xda7b0 + 152) 256 257 1 257 Clk' Wlk'.
    zbft F_3f234 D_3f234.
    stepn F_3f238 D_3f238. rwH. zclosed 0.
    zbft F_3f23c D_3f23c.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cgb' : cellA X (0xda7b0 + 184) 8 gbytes) by zcell; assert (Ccnt' : cellA X (0xda7b0 + 160) 8 cnt) by zcell;
      assert (Cgf' : cellA X (0xda7b0 + 168) 8 gfirst) by zcell;
      assert (T0 : cellA X (sp - 80) 8 0) by zcell; assert (T16 : cellA X (sp - 64) 8 0) by zcell end.
    zld F_3f240 D_3f240 (0xda7b0 + 184) Cgb'.
    zld F_3f244 D_3f244 (0xda7b0 + 160) Ccnt'.
    zstep F_3f248 D_3f248.
    zbft F_3f24c D_3f24c.
    zbft F_3f250 D_3f250.
    stepn F_3f254 D_3f254. zcl4.
    zstep F_3f258 D_3f258. zstep F_3f25c D_3f25c. zstep F_3f260 D_3f260.
    zbtk F_3f264 D_3f264.
    zld F_3f29c D_3f29c (sp - 80) T0.
    zld F_3f2a0 D_3f2a0 (sp - 64) T16.
    zld F_3f2a4 D_3f2a4 (0xda7b0 + 184) Cgb'.
    zbft F_3f2a8 D_3f2a8.
    zld F_3f2ac D_3f2ac (0xda7b0 + 168) Cgf'.
    stepn F_3f2b0 D_3f2b0.
    unfold art_rcy_head_mem. apply mst_refl. }
  split; [gres; reflexivity|]. split; [gres; exact H10|]. split; [gres; exact H11|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
  split; [gres; reflexivity|]. split; [gres; reflexivity|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

(* [comment removed for export] *)
Lemma art_rcy_pop : forall regs (M rom : word -> option byte) (tmp k plast gc b next size gbytes glast tbytes tfirst : Z),
  getr regs 10 = Z_to_bv 64 0xda7b0 -> getr regs 14 = Z_to_bv 64 k -> getr regs 15 = Z_to_bv 64 plast -> getr regs 16 = Z_to_bv 64 gc -> getr regs 5 = Z_to_bv 64 b ->
  getr regs 2 = Z_to_bv 64 tmp ->
  0x633000 <= tmp -> tmp + 32 < 2 ^ 64 -> 0x633000 <= b -> b + 8192 < 2 ^ 64 -> apart tmp 32 b 8192 -> 0 <= k < 2 ^ 63 -> 1 <= gc < 2 ^ 64 ->
  0 <= next < 2 ^ 64 -> 0 <= size < 2 ^ 64 -> 0 <= gbytes < 2 ^ 64 -> 0 <= tbytes < 2 ^ 64 ->
  (k <> 0 -> 0x633000 <= plast /\ plast + 8 < 2 ^ 64 /\ apart plast 8 b 8192 /\ apart plast 8 tmp 32 /\ wrA M plast 8) ->
  wrA M tmp 32 -> wrA M (0xda7b0 + 160) 32 -> wrA M b 8 ->
  cellA M b 8 next -> cellA M (b + 8) 8 size -> cellA M (0xda7b0 + 184) 8 gbytes -> cellA M (0xda7b0 + 176) 8 glast -> cellA M (tmp + 24) 8 tbytes -> cellA M (tmp + 8) 8 tfirst ->
  exists regs' (M' : word -> option byte), msteps ASEGS (mkst regs (0x3f2dc : word) M rom) (mkst regs' (0x3f2d8 : word) M' rom)
    /\ getr regs' 14 = Z_to_bv 64 (k + 1) /\ getr regs' 15 = Z_to_bv 64 b /\ getr regs' 5 = Z_to_bv 64 next /\ getr regs' 7 = Z_to_bv 64 (gbytes - size) /\ getr regs' 16 = Z_to_bv 64 (gc - 1) /\ getr regs' 6 = Z_to_bv 64 b
    /\ (forall r : reg, In r [1; 2; 3; 4; 8; 9; 10; 11; 12; 13; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r)
    /\ mem_grows M M' /\ art_agree [(0xda7b0 + 160, 32); (b, 8); (tmp, 32); (plast, if k =? 0 then 0 else 8)] M M'
    /\ cellA M' (0xda7b0 + 168) 8 next /\ cellA M' (0xda7b0 + 160) 8 (gc - 1) /\ cellA M' (0xda7b0 + 184) 8 (gbytes - size) /\ cellA M' b 8 0
    /\ (next = 0 -> cellA M' (0xda7b0 + 176) 8 0) /\ (next <> 0 -> cellA M' (0xda7b0 + 176) 8 glast)
    /\ (k = 0 -> cellA M' (tmp + 8) 8 b) /\ (k <> 0 -> cellA M' (tmp + 8) 8 tfirst /\ cellA M' plast 8 b)
    /\ cellA M' (tmp + 24) 8 (tbytes + size).
Proof.
  intros regs M rom tmp k plast gc b next size gbytes glast tbytes tfirst H10 H14 H15 H16 H5 H2 Htmp Htmp' Hb Hb' Atb Hk Hgc Hnext Hsize Hgb Htb Hpl Wt Wq Wb
    Cnext Csize Cgb Cgl Ctb Ctf.
  unfold apart in Atb.
  destruct (Z.eq_dec next 0) as [N0|N1]; destruct (Z.eq_dec k 0) as [K0|K1].
  - rewrite (proj2 (Z.eqb_eq k 0) K0). eexists. eexists. split.
    { zbft F_3f2dc D_3f2dc.
      zld F_3f2e0 D_3f2e0 b Cnext.
      zsd F_3f2e4 D_3f2e4 (0xda7b0 + 168) next ltac:(rewok Wq).
      zbft F_3f2e8 D_3f2e8.
      zsd F_3f2ec D_3f2ec (0xda7b0 + 176) 0 ltac:(rewok Wq).
      zstep F_3f2f0 D_3f2f0.
      zsd F_3f2f4 D_3f2f4 (0xda7b0 + 160) (gc + -1) ltac:(rewok Wq).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize' : cellA X (b + 8) 8 size) by zcell; assert (Cgb' : cellA X (0xda7b0 + 184) 8 gbytes) by zcell end.
      zld F_3f2f8 D_3f2f8 (b + 8) Csize'.
      zld F_3f2fc D_3f2fc (0xda7b0 + 184) Cgb'.
      zstep F_3f300 D_3f300.
      zsd F_3f304 D_3f304 (0xda7b0 + 184) (gbytes - size) ltac:(rewok Wq).
      zstep F_3f308 D_3f308.
      zsd F_3f30c D_3f30c b 0 ltac:(rewok Wb).
      zbft F_3f310 D_3f310.
      stepn F_3f314 D_3f314.
      zsd F_3f328 D_3f328 (tmp + 8) b ltac:(rewok Wt).
      stepn F_3f32c D_3f32c.
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize2 : cellA X (b + 8) 8 size) by zcell; assert (Ctb' : cellA X (tmp + 24) 8 tbytes) by zcell end.
      zld F_3f2b8 D_3f2b8 (b + 8) Csize2.
      zld F_3f2bc D_3f2bc (tmp + 24) Ctb'.
      zstep F_3f2c0 D_3f2c0.
      zsd F_3f2c4 D_3f2c4 (tmp + 24) (tbytes + size) ltac:(rewok Wt).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cgb2 : cellA X (0xda7b0 + 184) 8 (gbytes - size)) by zcell end.
      zld F_3f2c8 D_3f2c8 (0xda7b0 + 184) Cgb2.
      zstep F_3f2cc D_3f2cc. zstep F_3f2d0 D_3f2d0. zstep F_3f2d4 D_3f2d4.
      apply mst_refl. }
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
    split. { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
    split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|].
    split; [zcell|]. split; [replace (gc - 1) with (gc + -1) by lia; zcell|]. split; [zcell|]. split; [zcell|].
    split; [intros _; zcell|]. split; [intros X; exfalso; lia|].
    split; [intros _; zcell|]. split; [intros X; exfalso; lia|]. zcell.
  - destruct (Hpl K1) as (Hp0 & Hp1 & Apb & Apt & Wpl). unfold apart in Apb, Apt. rewrite (proj2 (Z.eqb_neq k 0) K1). eexists. eexists. split.
    { zbft F_3f2dc D_3f2dc.
      zld F_3f2e0 D_3f2e0 b Cnext.
      zsd F_3f2e4 D_3f2e4 (0xda7b0 + 168) next ltac:(rewok Wq).
      zbft F_3f2e8 D_3f2e8.
      zsd F_3f2ec D_3f2ec (0xda7b0 + 176) 0 ltac:(rewok Wq).
      zstep F_3f2f0 D_3f2f0.
      zsd F_3f2f4 D_3f2f4 (0xda7b0 + 160) (gc + -1) ltac:(rewok Wq).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize' : cellA X (b + 8) 8 size) by zcell; assert (Cgb' : cellA X (0xda7b0 + 184) 8 gbytes) by zcell end.
      zld F_3f2f8 D_3f2f8 (b + 8) Csize'.
      zld F_3f2fc D_3f2fc (0xda7b0 + 184) Cgb'.
      zstep F_3f300 D_3f300.
      zsd F_3f304 D_3f304 (0xda7b0 + 184) (gbytes - size) ltac:(rewok Wq).
      zstep F_3f308 D_3f308.
      zsd F_3f30c D_3f30c b 0 ltac:(rewok Wb).
      zbtk F_3f310 D_3f310.
      zsd F_3f2b4 D_3f2b4 plast b ltac:(rewok Wpl).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize2 : cellA X (b + 8) 8 size) by zcell; assert (Ctb' : cellA X (tmp + 24) 8 tbytes) by zcell end.
      zld F_3f2b8 D_3f2b8 (b + 8) Csize2.
      zld F_3f2bc D_3f2bc (tmp + 24) Ctb'.
      zstep F_3f2c0 D_3f2c0.
      zsd F_3f2c4 D_3f2c4 (tmp + 24) (tbytes + size) ltac:(rewok Wt).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cgb2 : cellA X (0xda7b0 + 184) 8 (gbytes - size)) by zcell end.
      zld F_3f2c8 D_3f2c8 (0xda7b0 + 184) Cgb2.
      zstep F_3f2cc D_3f2cc. zstep F_3f2d0 D_3f2d0. zstep F_3f2d4 D_3f2d4.
      apply mst_refl. }
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
    split. { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
    split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|].
    split; [zcell|]. split; [replace (gc - 1) with (gc + -1) by lia; zcell|]. split; [zcell|]. split; [zcell|].
    split; [intros _; zcell|]. split; [intros X; exfalso; lia|].
    split; [intros X; exfalso; lia|]. split; [intros _; split; zcell|]. zcell.
  - rewrite (proj2 (Z.eqb_eq k 0) K0). eexists. eexists. split.
    { zbft F_3f2dc D_3f2dc.
      zld F_3f2e0 D_3f2e0 b Cnext.
      zsd F_3f2e4 D_3f2e4 (0xda7b0 + 168) next ltac:(rewok Wq).
      zbtk F_3f2e8 D_3f2e8.
      zstep F_3f2f0 D_3f2f0.
      zsd F_3f2f4 D_3f2f4 (0xda7b0 + 160) (gc + -1) ltac:(rewok Wq).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize' : cellA X (b + 8) 8 size) by zcell; assert (Cgb' : cellA X (0xda7b0 + 184) 8 gbytes) by zcell end.
      zld F_3f2f8 D_3f2f8 (b + 8) Csize'.
      zld F_3f2fc D_3f2fc (0xda7b0 + 184) Cgb'.
      zstep F_3f300 D_3f300.
      zsd F_3f304 D_3f304 (0xda7b0 + 184) (gbytes - size) ltac:(rewok Wq).
      zstep F_3f308 D_3f308.
      zsd F_3f30c D_3f30c b 0 ltac:(rewok Wb).
      zbft F_3f310 D_3f310.
      stepn F_3f314 D_3f314.
      zsd F_3f328 D_3f328 (tmp + 8) b ltac:(rewok Wt).
      stepn F_3f32c D_3f32c.
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize2 : cellA X (b + 8) 8 size) by zcell; assert (Ctb' : cellA X (tmp + 24) 8 tbytes) by zcell end.
      zld F_3f2b8 D_3f2b8 (b + 8) Csize2.
      zld F_3f2bc D_3f2bc (tmp + 24) Ctb'.
      zstep F_3f2c0 D_3f2c0.
      zsd F_3f2c4 D_3f2c4 (tmp + 24) (tbytes + size) ltac:(rewok Wt).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cgb2 : cellA X (0xda7b0 + 184) 8 (gbytes - size)) by zcell end.
      zld F_3f2c8 D_3f2c8 (0xda7b0 + 184) Cgb2.
      zstep F_3f2cc D_3f2cc. zstep F_3f2d0 D_3f2d0. zstep F_3f2d4 D_3f2d4.
      apply mst_refl. }
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
    split. { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
    split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|].
    split; [zcell|]. split; [replace (gc - 1) with (gc + -1) by lia; zcell|]. split; [zcell|]. split; [zcell|].
    split; [intros X; exfalso; lia|]. split; [intros _; zcell|].
    split; [intros _; zcell|]. split; [intros X; exfalso; lia|]. zcell.
  - destruct (Hpl K1) as (Hp0 & Hp1 & Apb & Apt & Wpl). unfold apart in Apb, Apt. rewrite (proj2 (Z.eqb_neq k 0) K1). eexists. eexists. split.
    { zbft F_3f2dc D_3f2dc.
      zld F_3f2e0 D_3f2e0 b Cnext.
      zsd F_3f2e4 D_3f2e4 (0xda7b0 + 168) next ltac:(rewok Wq).
      zbtk F_3f2e8 D_3f2e8.
      zstep F_3f2f0 D_3f2f0.
      zsd F_3f2f4 D_3f2f4 (0xda7b0 + 160) (gc + -1) ltac:(rewok Wq).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize' : cellA X (b + 8) 8 size) by zcell; assert (Cgb' : cellA X (0xda7b0 + 184) 8 gbytes) by zcell end.
      zld F_3f2f8 D_3f2f8 (b + 8) Csize'.
      zld F_3f2fc D_3f2fc (0xda7b0 + 184) Cgb'.
      zstep F_3f300 D_3f300.
      zsd F_3f304 D_3f304 (0xda7b0 + 184) (gbytes - size) ltac:(rewok Wq).
      zstep F_3f308 D_3f308.
      zsd F_3f30c D_3f30c b 0 ltac:(rewok Wb).
      zbtk F_3f310 D_3f310.
      zsd F_3f2b4 D_3f2b4 plast b ltac:(rewok Wpl).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize2 : cellA X (b + 8) 8 size) by zcell; assert (Ctb' : cellA X (tmp + 24) 8 tbytes) by zcell end.
      zld F_3f2b8 D_3f2b8 (b + 8) Csize2.
      zld F_3f2bc D_3f2bc (tmp + 24) Ctb'.
      zstep F_3f2c0 D_3f2c0.
      zsd F_3f2c4 D_3f2c4 (tmp + 24) (tbytes + size) ltac:(rewok Wt).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cgb2 : cellA X (0xda7b0 + 184) 8 (gbytes - size)) by zcell end.
      zld F_3f2c8 D_3f2c8 (0xda7b0 + 184) Cgb2.
      zstep F_3f2cc D_3f2cc. zstep F_3f2d0 D_3f2d0. zstep F_3f2d4 D_3f2d4.
      apply mst_refl. }
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
    split. { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
    split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|].
    split; [zcell|]. split; [replace (gc - 1) with (gc + -1) by lia; zcell|]. split; [zcell|]. split; [zcell|].
    split; [intros X; exfalso; lia|]. split; [intros _; zcell|].
    split; [intros X; exfalso; lia|]. split; [intros _; split; zcell|]. zcell.
Qed.

(* [comment removed for export] *)
Lemma art_rcy_more : forall regs (M rom : word -> option byte) (mn gb : Z),
  getr regs 11 = Z_to_bv 64 mn -> getr regs 7 = Z_to_bv 64 gb -> 0 <= mn < gb -> gb < 2 ^ 64 ->
  exists regs', msteps ASEGS (mkst regs (0x3f2d8 : word) M rom) (mkst regs' (0x3f2dc : word) M rom) /\ (forall r : reg, getr regs' r = getr regs r).
Proof.
  intros regs M rom mn gb H11 H7 Hmn Hgb. eexists. split. { zbft F_3f2d8 D_3f2d8. apply mst_refl. } intros r. reflexivity.
Qed.
Lemma art_rcy_exit : forall regs (M rom : word -> option byte) (mn gb : Z),
  getr regs 11 = Z_to_bv 64 mn -> getr regs 7 = Z_to_bv 64 gb -> 0 <= gb <= mn -> mn < 2 ^ 64 ->
  exists regs', msteps ASEGS (mkst regs (0x3f2d8 : word) M rom) (mkst regs' (0x3f330 : word) M rom) /\ (forall r : reg, getr regs' r = getr regs r).
Proof.
  intros regs M rom mn gb H11 H7 Hmn Hgb. eexists. split. { zbtk F_3f2d8 D_3f2d8. apply mst_refl. } intros r. reflexivity.
Qed.

(* [comment removed for export] *)
Definition art_rcy_tail_mem (M : word -> option byte) (tmp k b : Z) : word -> option byte :=
  Wn 1 (Wn 1 (Wn 8 (Wn 8 M tmp k) (tmp + 16) b) (0xda7b0 + 152) 0) (0xda7b0 + 153) 0.

Lemma art_rcy_tail : forall regs (M rom : word -> option byte) (tmp k b : Z),
  getr regs 2 = Z_to_bv 64 tmp -> getr regs 10 = Z_to_bv 64 0xda7b0 -> getr regs 14 = Z_to_bv 64 k -> getr regs 6 = Z_to_bv 64 b ->
  0x633000 <= tmp -> tmp + 32 < 2 ^ 64 -> 0 <= k < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> wrA M tmp 32 -> wrA M (0xda7b0 + 152) 4 ->
  exists regs', msteps ASEGS (mkst regs (0x3f330 : word) M rom) (mkst regs' (0x3f548 : word) (art_rcy_tail_mem M tmp k b) rom)
    /\ getr regs' 1 = (0x3f350 : bv 64)%bv /\ getr regs' 11 = Z_to_bv 64 tmp
    /\ (forall r : reg, In r [2; 3; 4; 8; 9; 10; 12; 13; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom tmp k b H2 H10 H14 H6 Htmp Htmp' Hk Hb Wt Wq.
  eexists. split.
  { zsd F_3f330 D_3f330 tmp k ltac:(rewok Wt).
    zsd F_3f334 D_3f334 (tmp + 16) b ltac:(rewok Wt).
    stepfence F_3f338 D_3f338.
    zsb F_3f33c D_3f33c (0xda7b0 + 152) 0 ltac:(zwok').
    stepfence F_3f340 D_3f340.
    zsb F_3f344 D_3f344 (0xda7b0 + 153) 0 ltac:(zwok').
    zstep F_3f348 D_3f348.
    stepn F_3f34c D_3f34c.
    unfold art_rcy_tail_mem. apply mst_refl. }
  split; [gres; bveq|]. split; [gres; f_equal; lia|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

Lemma art_rcy_tail_mem_facts : forall (M : word -> option byte) tmp k b, 0x633000 <= tmp -> tmp + 32 < 2 ^ 64 -> cellA M (0xda7b0 + 152) 4 257 ->
  mem_grows M (art_rcy_tail_mem M tmp k b) /\ art_agree [(tmp, 8); (tmp + 16, 8); (0xda7b0 + 152, 4)] M (art_rcy_tail_mem M tmp k b)
  /\ cellA (art_rcy_tail_mem M tmp k b) tmp 8 k /\ cellA (art_rcy_tail_mem M tmp k b) (tmp + 16) 8 b /\ cellA (art_rcy_tail_mem M tmp k b) (0xda7b0 + 152) 4 0.
Proof.
  intros M tmp k b Htmp Htmp' Clk. unfold art_rcy_tail_mem.
  split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|]. split; [zcell|]. split; [zcell|].
  change (cellA (Wn 1 (Wn 1 (Wn 8 (Wn 8 M tmp k) (tmp + 16) b) (0xda7b0 + 152) 0) (0xda7b0 + 153) 0) (0xda7b0 + 152) 4 (0 + 256 * 0 + 65536 * 0)).
  apply cell4_join; [lia|lia|lia|lia|lia| | | ].
  - zcell.
  - zcell.
  - destruct (cell4_split M (0xda7b0 + 152) 257 ltac:(lia) ltac:(lia) ltac:(lia) Clk) as (_ & _ & C2). change (257 / 65536) with 0 in C2. zcell.
Qed.

(* [comment removed for export] *)
Lemma art_rcy_epi : forall regs (M rom : word -> option byte) (raw : word) (sp g8 g9 g18 g19 g20 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 80) -> ret_ok raw -> 80 <= sp -> sp < 2 ^ 64 ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 g8 -> cellA M (sp - 24) 8 g9 -> cellA M (sp - 32) 8 g18 -> cellA M (sp - 40) 8 g19 -> cellA M (sp - 48) 8 g20 ->
  exists regs', msteps ASEGS (mkst regs (0x3f350 : word) M rom) (mkst regs' raw M rom)
    /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 8 = Z_to_bv 64 g8 /\ getr regs' 9 = Z_to_bv 64 g9 /\ getr regs' 18 = Z_to_bv 64 g18
    /\ getr regs' 19 = Z_to_bv 64 g19 /\ getr regs' 20 = Z_to_bv 64 g20
    /\ (forall r : reg, In r [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp g8 g9 g18 g19 g20 H2 Hret Hsp Hsp' F1 F8 F9 F18 F19 F20.
  eexists. split.
  { zld F_3f350 D_3f350 (sp - 8) F1. rewrite Z_to_bv_bv_unsigned.
    zld F_3f354 D_3f354 (sp - 16) F8. zld F_3f358 D_3f358 (sp - 24) F9. zld F_3f35c D_3f35c (sp - 32) F18. zld F_3f360 D_3f360 (sp - 40) F19. zld F_3f364 D_3f364 (sp - 48) F20.
    zstep F_3f368 D_3f368.
    stepret F_3f36c D_3f36c raw ltac:(reflexivity).
    apply mst_refl. }
  split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
  split; [gres; reflexivity|]. split; [gres; reflexivity|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.
End FPX.
