(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatAllocG_b BatPoison_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatFp_b BatFree1_b BatCellEx_b BatRecycle4_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r3ef18_4052c_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Definition art_rcy_head_mem (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
  Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18)))
    (sp - 40) (U (getr regs 19))) (sp - 48) (U (getr regs 20))) (sp - 80) 0) (sp - 72) 0) (sp - 64) 0) (sp - 56) 0) (0x13c8b0 + 152) 257.

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_rcy_head : forall regs (M rom : word -> option byte) (raw : word) (sp mn cnt gbytes gfirst : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 0x13c8b0 -> getr regs 11 = Z_to_bv 64 mn ->
  0x696000 + 80 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 80) 80 -> wrA M (0x13c8b0 + 152) 4 ->
  1 <= cnt -> 16384 * cnt <= gbytes -> gbytes < 2 ^ 57 -> 0 <= mn < gbytes -> 0 <= gfirst < 2 ^ 64 ->
  cellA M (0x13c8b0 + 152) 4 256 -> cellA M (0x13c8b0 + 184) 8 gbytes -> cellA M (0x13c8b0 + 160) 8 cnt -> cellA M (0x13c8b0 + 168) 8 gfirst ->
  exists regs', msteps ASEGS (mkst regs (0x54454 : word) M rom) (mkst regs' (0x54550 : word) (art_rcy_head_mem M sp raw regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (sp - 80) /\ getr regs' 10 = Z_to_bv 64 0x13c8b0 /\ getr regs' 11 = Z_to_bv 64 mn /\ getr regs' 14 = Z_to_bv 64 0 /\ getr regs' 15 = Z_to_bv 64 0
    /\ getr regs' 16 = Z_to_bv 64 cnt /\ getr regs' 5 = Z_to_bv 64 gfirst
    /\ (forall r : reg, In r [1; 3; 4; 8; 9; 12; 13; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp mn cnt gbytes gfirst H1 H2 H10 H11 Hsp Hsp' W Wlk Hcnt Hmerge Hgb Hmn Hgf Clk Cgb Ccnt Cgf.
  eexists. split.
  { zstep F_5403c D_5403c.
    zsd F_54040 D_54040 (sp - 8) (U raw) ltac:(rewok W). zsd F_54044 D_54044 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_54048 D_54048 (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_5404c D_5404c (sp - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_54050 D_54050 (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_54054 D_54054 (sp - 48) (U (getr regs 20)) ltac:(rewok W).
    zsd F_54058 D_54058 (sp - 80) 0 ltac:(rewok W). zsd F_5405c D_5405c (sp - 72) 0 ltac:(rewok W).
    zsd F_54060 D_54060 (sp - 64) 0 ltac:(rewok W). zsd F_54064 D_54064 (sp - 56) 0 ltac:(rewok W).
    zstep F_54068 D_54068. zstep F_5406c D_5406c.
    stepn F_54070 D_54070. rwH. zclosed (0x13c8b0 + 152).
    zstep F_54074 D_54074.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Clk' : cellA X (0x13c8b0 + 152) 4 256) by zcell; assert (Wlk' : wokA X (0x13c8b0 + 152) 4) by zwok end.
    zcas6 F_54078 D_54078 F_5407c D_5407c F_54080 D_54080 F_54084 D_54084 F_54088 D_54088 F_5408c D_5408c (0x13c8b0 + 152) 256 257 1 257 Clk' Wlk'.
    zbft F_54090 D_54090.
    stepn F_54094 D_54094. rwH. zclosed 0.
    zbft F_54098 D_54098.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cgb' : cellA X (0x13c8b0 + 184) 8 gbytes) by zcell; assert (Ccnt' : cellA X (0x13c8b0 + 160) 8 cnt) by zcell;
      assert (Cgf' : cellA X (0x13c8b0 + 168) 8 gfirst) by zcell;
      assert (T0 : cellA X (sp - 80) 8 0) by zcell; assert (T16 : cellA X (sp - 64) 8 0) by zcell end.
    zld F_5409c D_5409c (0x13c8b0 + 184) Cgb'.
    zld F_540a0 D_540a0 (0x13c8b0 + 160) Ccnt'.
    zstep F_540a4 D_540a4.
    zbft F_540a8 D_540a8.
    zbft F_540ac D_540ac.
    stepn F_540b0 D_540b0. zcl4.
    zstep F_540b4 D_540b4. zstep F_540b8 D_540b8. zstep F_540bc D_540bc.
    zbtk F_540c0 D_540c0.
    zld F_540f8 D_540f8 (sp - 80) T0.
    zld F_540fc D_540fc (sp - 64) T16.
    zld F_54100 D_54100 (0x13c8b0 + 184) Cgb'.
    zbft F_54104 D_54104.
    zld F_54108 D_54108 (0x13c8b0 + 168) Cgf'.
    stepn F_5410c D_5410c.
    unfold art_rcy_head_mem. apply mst_refl. }
  split; [gres; reflexivity|]. split; [gres; exact H10|]. split; [gres; exact H11|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
  split; [gres; reflexivity|]. split; [gres; reflexivity|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_rcy_pop : forall regs (M rom : word -> option byte) (tmp k plast gc b next size gbytes glast tbytes tfirst : Z),
  getr regs 10 = Z_to_bv 64 0x13c8b0 -> getr regs 14 = Z_to_bv 64 k -> getr regs 15 = Z_to_bv 64 plast -> getr regs 16 = Z_to_bv 64 gc -> getr regs 5 = Z_to_bv 64 b ->
  getr regs 2 = Z_to_bv 64 tmp ->
  0x696000 <= tmp -> tmp + 32 < 2 ^ 64 -> 0x696000 <= b -> b + 8192 < 2 ^ 64 -> apart tmp 32 b 8192 -> 0 <= k < 2 ^ 63 -> 1 <= gc < 2 ^ 64 ->
  0 <= next < 2 ^ 64 -> 0 <= size < 2 ^ 64 -> 0 <= gbytes < 2 ^ 64 -> 0 <= tbytes < 2 ^ 64 ->
  (k <> 0 -> 0x696000 <= plast /\ plast + 8 < 2 ^ 64 /\ apart plast 8 b 8192 /\ apart plast 8 tmp 32 /\ wrA M plast 8) ->
  wrA M tmp 32 -> wrA M (0x13c8b0 + 160) 32 -> wrA M b 8 ->
  cellA M b 8 next -> cellA M (b + 8) 8 size -> cellA M (0x13c8b0 + 184) 8 gbytes -> cellA M (0x13c8b0 + 176) 8 glast -> cellA M (tmp + 24) 8 tbytes -> cellA M (tmp + 8) 8 tfirst ->
  exists regs' (M' : word -> option byte), msteps ASEGS (mkst regs (0x54550 : word) M rom) (mkst regs' (0x5454c : word) M' rom)
    /\ getr regs' 14 = Z_to_bv 64 (k + 1) /\ getr regs' 15 = Z_to_bv 64 b /\ getr regs' 5 = Z_to_bv 64 next /\ getr regs' 7 = Z_to_bv 64 (gbytes - size) /\ getr regs' 16 = Z_to_bv 64 (gc - 1) /\ getr regs' 6 = Z_to_bv 64 b
    /\ (forall r : reg, In r [1; 2; 3; 4; 8; 9; 10; 11; 12; 13; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r)
    /\ mem_grows M M' /\ art_agree [(0x13c8b0 + 160, 32); (b, 8); (tmp, 32); (plast, if k =? 0 then 0 else 8)] M M'
    /\ cellA M' (0x13c8b0 + 168) 8 next /\ cellA M' (0x13c8b0 + 160) 8 (gc - 1) /\ cellA M' (0x13c8b0 + 184) 8 (gbytes - size) /\ cellA M' b 8 0
    /\ (next = 0 -> cellA M' (0x13c8b0 + 176) 8 0) /\ (next <> 0 -> cellA M' (0x13c8b0 + 176) 8 glast)
    /\ (k = 0 -> cellA M' (tmp + 8) 8 b) /\ (k <> 0 -> cellA M' (tmp + 8) 8 tfirst /\ cellA M' plast 8 b)
    /\ cellA M' (tmp + 24) 8 (tbytes + size).
Proof.
  intros regs M rom tmp k plast gc b next size gbytes glast tbytes tfirst H10 H14 H15 H16 H5 H2 Htmp Htmp' Hb Hb' Atb Hk Hgc Hnext Hsize Hgb Htb Hpl Wt Wq Wb
    Cnext Csize Cgb Cgl Ctb Ctf.
  unfold apart in Atb.
  destruct (Z.eq_dec next 0) as [N0|N1]; destruct (Z.eq_dec k 0) as [K0|K1].
  - rewrite (proj2 (Z.eqb_eq k 0) K0). eexists. eexists. split.
    { zbft F_54138 D_54138.
      zld F_5413c D_5413c b Cnext.
      zsd F_54140 D_54140 (0x13c8b0 + 168) next ltac:(rewok Wq).
      zbft F_54144 D_54144.
      zsd F_54148 D_54148 (0x13c8b0 + 176) 0 ltac:(rewok Wq).
      zstep F_5414c D_5414c.
      zsd F_54150 D_54150 (0x13c8b0 + 160) (gc + -1) ltac:(rewok Wq).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize' : cellA X (b + 8) 8 size) by zcell; assert (Cgb' : cellA X (0x13c8b0 + 184) 8 gbytes) by zcell end.
      zld F_54154 D_54154 (b + 8) Csize'.
      zld F_54158 D_54158 (0x13c8b0 + 184) Cgb'.
      zstep F_5415c D_5415c.
      zsd F_54160 D_54160 (0x13c8b0 + 184) (gbytes - size) ltac:(rewok Wq).
      zstep F_54164 D_54164.
      zsd F_54168 D_54168 b 0 ltac:(rewok Wb).
      zbft F_5416c D_5416c.
      stepn F_54170 D_54170.
      zsd F_54184 D_54184 (tmp + 8) b ltac:(rewok Wt).
      stepn F_54188 D_54188.
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize2 : cellA X (b + 8) 8 size) by zcell; assert (Ctb' : cellA X (tmp + 24) 8 tbytes) by zcell end.
      zld F_54114 D_54114 (b + 8) Csize2.
      zld F_54118 D_54118 (tmp + 24) Ctb'.
      zstep F_5411c D_5411c.
      zsd F_54120 D_54120 (tmp + 24) (tbytes + size) ltac:(rewok Wt).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cgb2 : cellA X (0x13c8b0 + 184) 8 (gbytes - size)) by zcell end.
      zld F_54124 D_54124 (0x13c8b0 + 184) Cgb2.
      zstep F_54128 D_54128. zstep F_5412c D_5412c. zstep F_54130 D_54130.
      apply mst_refl. }
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
    split. { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
    split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|].
    split; [zcell|]. split; [replace (gc - 1) with (gc + -1) by lia; zcell|]. split; [zcell|]. split; [zcell|].
    split; [intros _; zcell|]. split; [intros X; exfalso; lia|].
    split; [intros _; zcell|]. split; [intros X; exfalso; lia|]. zcell.
  - destruct (Hpl K1) as (Hp0 & Hp1 & Apb & Apt & Wpl). unfold apart in Apb, Apt. rewrite (proj2 (Z.eqb_neq k 0) K1). eexists. eexists. split.
    { zbft F_54138 D_54138.
      zld F_5413c D_5413c b Cnext.
      zsd F_54140 D_54140 (0x13c8b0 + 168) next ltac:(rewok Wq).
      zbft F_54144 D_54144.
      zsd F_54148 D_54148 (0x13c8b0 + 176) 0 ltac:(rewok Wq).
      zstep F_5414c D_5414c.
      zsd F_54150 D_54150 (0x13c8b0 + 160) (gc + -1) ltac:(rewok Wq).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize' : cellA X (b + 8) 8 size) by zcell; assert (Cgb' : cellA X (0x13c8b0 + 184) 8 gbytes) by zcell end.
      zld F_54154 D_54154 (b + 8) Csize'.
      zld F_54158 D_54158 (0x13c8b0 + 184) Cgb'.
      zstep F_5415c D_5415c.
      zsd F_54160 D_54160 (0x13c8b0 + 184) (gbytes - size) ltac:(rewok Wq).
      zstep F_54164 D_54164.
      zsd F_54168 D_54168 b 0 ltac:(rewok Wb).
      zbtk F_5416c D_5416c.
      zsd F_54110 D_54110 plast b ltac:(rewok Wpl).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize2 : cellA X (b + 8) 8 size) by zcell; assert (Ctb' : cellA X (tmp + 24) 8 tbytes) by zcell end.
      zld F_54114 D_54114 (b + 8) Csize2.
      zld F_54118 D_54118 (tmp + 24) Ctb'.
      zstep F_5411c D_5411c.
      zsd F_54120 D_54120 (tmp + 24) (tbytes + size) ltac:(rewok Wt).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cgb2 : cellA X (0x13c8b0 + 184) 8 (gbytes - size)) by zcell end.
      zld F_54124 D_54124 (0x13c8b0 + 184) Cgb2.
      zstep F_54128 D_54128. zstep F_5412c D_5412c. zstep F_54130 D_54130.
      apply mst_refl. }
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
    split. { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
    split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|].
    split; [zcell|]. split; [replace (gc - 1) with (gc + -1) by lia; zcell|]. split; [zcell|]. split; [zcell|].
    split; [intros _; zcell|]. split; [intros X; exfalso; lia|].
    split; [intros X; exfalso; lia|]. split; [intros _; split; zcell|]. zcell.
  - rewrite (proj2 (Z.eqb_eq k 0) K0). eexists. eexists. split.
    { zbft F_54138 D_54138.
      zld F_5413c D_5413c b Cnext.
      zsd F_54140 D_54140 (0x13c8b0 + 168) next ltac:(rewok Wq).
      zbtk F_54144 D_54144.
      zstep F_5414c D_5414c.
      zsd F_54150 D_54150 (0x13c8b0 + 160) (gc + -1) ltac:(rewok Wq).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize' : cellA X (b + 8) 8 size) by zcell; assert (Cgb' : cellA X (0x13c8b0 + 184) 8 gbytes) by zcell end.
      zld F_54154 D_54154 (b + 8) Csize'.
      zld F_54158 D_54158 (0x13c8b0 + 184) Cgb'.
      zstep F_5415c D_5415c.
      zsd F_54160 D_54160 (0x13c8b0 + 184) (gbytes - size) ltac:(rewok Wq).
      zstep F_54164 D_54164.
      zsd F_54168 D_54168 b 0 ltac:(rewok Wb).
      zbft F_5416c D_5416c.
      stepn F_54170 D_54170.
      zsd F_54184 D_54184 (tmp + 8) b ltac:(rewok Wt).
      stepn F_54188 D_54188.
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize2 : cellA X (b + 8) 8 size) by zcell; assert (Ctb' : cellA X (tmp + 24) 8 tbytes) by zcell end.
      zld F_54114 D_54114 (b + 8) Csize2.
      zld F_54118 D_54118 (tmp + 24) Ctb'.
      zstep F_5411c D_5411c.
      zsd F_54120 D_54120 (tmp + 24) (tbytes + size) ltac:(rewok Wt).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cgb2 : cellA X (0x13c8b0 + 184) 8 (gbytes - size)) by zcell end.
      zld F_54124 D_54124 (0x13c8b0 + 184) Cgb2.
      zstep F_54128 D_54128. zstep F_5412c D_5412c. zstep F_54130 D_54130.
      apply mst_refl. }
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
    split. { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
    split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|].
    split; [zcell|]. split; [replace (gc - 1) with (gc + -1) by lia; zcell|]. split; [zcell|]. split; [zcell|].
    split; [intros X; exfalso; lia|]. split; [intros _; zcell|].
    split; [intros _; zcell|]. split; [intros X; exfalso; lia|]. zcell.
  - destruct (Hpl K1) as (Hp0 & Hp1 & Apb & Apt & Wpl). unfold apart in Apb, Apt. rewrite (proj2 (Z.eqb_neq k 0) K1). eexists. eexists. split.
    { zbft F_54138 D_54138.
      zld F_5413c D_5413c b Cnext.
      zsd F_54140 D_54140 (0x13c8b0 + 168) next ltac:(rewok Wq).
      zbtk F_54144 D_54144.
      zstep F_5414c D_5414c.
      zsd F_54150 D_54150 (0x13c8b0 + 160) (gc + -1) ltac:(rewok Wq).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize' : cellA X (b + 8) 8 size) by zcell; assert (Cgb' : cellA X (0x13c8b0 + 184) 8 gbytes) by zcell end.
      zld F_54154 D_54154 (b + 8) Csize'.
      zld F_54158 D_54158 (0x13c8b0 + 184) Cgb'.
      zstep F_5415c D_5415c.
      zsd F_54160 D_54160 (0x13c8b0 + 184) (gbytes - size) ltac:(rewok Wq).
      zstep F_54164 D_54164.
      zsd F_54168 D_54168 b 0 ltac:(rewok Wb).
      zbtk F_5416c D_5416c.
      zsd F_54110 D_54110 plast b ltac:(rewok Wpl).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize2 : cellA X (b + 8) 8 size) by zcell; assert (Ctb' : cellA X (tmp + 24) 8 tbytes) by zcell end.
      zld F_54114 D_54114 (b + 8) Csize2.
      zld F_54118 D_54118 (tmp + 24) Ctb'.
      zstep F_5411c D_5411c.
      zsd F_54120 D_54120 (tmp + 24) (tbytes + size) ltac:(rewok Wt).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cgb2 : cellA X (0x13c8b0 + 184) 8 (gbytes - size)) by zcell end.
      zld F_54124 D_54124 (0x13c8b0 + 184) Cgb2.
      zstep F_54128 D_54128. zstep F_5412c D_5412c. zstep F_54130 D_54130.
      apply mst_refl. }
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
    split. { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
    split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|].
    split; [zcell|]. split; [replace (gc - 1) with (gc + -1) by lia; zcell|]. split; [zcell|]. split; [zcell|].
    split; [intros X; exfalso; lia|]. split; [intros _; zcell|].
    split; [intros X; exfalso; lia|]. split; [intros _; split; zcell|]. zcell.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_rcy_more : forall regs (M rom : word -> option byte) (mn gb : Z),
  getr regs 11 = Z_to_bv 64 mn -> getr regs 7 = Z_to_bv 64 gb -> 0 <= mn < gb -> gb < 2 ^ 64 ->
  exists regs', msteps ASEGS (mkst regs (0x5454c : word) M rom) (mkst regs' (0x54550 : word) M rom) /\ (forall r : reg, getr regs' r = getr regs r).
Proof.
  intros regs M rom mn gb H11 H7 Hmn Hgb. eexists. split. { zbft F_54134 D_54134. apply mst_refl. } intros r. reflexivity.
Qed.
#[using="Type"] Lemma art_rcy_exit : forall regs (M rom : word -> option byte) (mn gb : Z),
  getr regs 11 = Z_to_bv 64 mn -> getr regs 7 = Z_to_bv 64 gb -> 0 <= gb <= mn -> mn < 2 ^ 64 ->
  exists regs', msteps ASEGS (mkst regs (0x5454c : word) M rom) (mkst regs' (0x545a4 : word) M rom) /\ (forall r : reg, getr regs' r = getr regs r).
Proof.
  intros regs M rom mn gb H11 H7 Hmn Hgb. eexists. split. { zbtk F_54134 D_54134. apply mst_refl. } intros r. reflexivity.
Qed.

(* [comment removed for export] *)
Definition art_rcy_tail_mem (M : word -> option byte) (tmp k b : Z) : word -> option byte :=
  Wn 1 (Wn 1 (Wn 8 (Wn 8 M tmp k) (tmp + 16) b) (0x13c8b0 + 152) 0) (0x13c8b0 + 153) 0.

#[using="Type"] Lemma art_rcy_tail : forall regs (M rom : word -> option byte) (tmp k b : Z),
  getr regs 2 = Z_to_bv 64 tmp -> getr regs 10 = Z_to_bv 64 0x13c8b0 -> getr regs 14 = Z_to_bv 64 k -> getr regs 6 = Z_to_bv 64 b ->
  0x696000 <= tmp -> tmp + 32 < 2 ^ 64 -> 0 <= k < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> wrA M tmp 32 -> wrA M (0x13c8b0 + 152) 4 ->
  exists regs', msteps ASEGS (mkst regs (0x545a4 : word) M rom) (mkst regs' (0x547bc : word) (art_rcy_tail_mem M tmp k b) rom)
    /\ getr regs' 1 = (0x545c4 : bv 64)%bv /\ getr regs' 11 = Z_to_bv 64 tmp
    /\ (forall r : reg, In r [2; 3; 4; 8; 9; 10; 12; 13; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom tmp k b H2 H10 H14 H6 Htmp Htmp' Hk Hb Wt Wq.
  eexists. split.
  { zsd F_5418c D_5418c tmp k ltac:(rewok Wt).
    zsd F_54190 D_54190 (tmp + 16) b ltac:(rewok Wt).
    stepfence F_54194 D_54194.
    zsb F_54198 D_54198 (0x13c8b0 + 152) 0 ltac:(zwok').
    stepfence F_5419c D_5419c.
    zsb F_541a0 D_541a0 (0x13c8b0 + 153) 0 ltac:(zwok').
    zstep F_541a4 D_541a4.
    stepn F_541a8 D_541a8.
    unfold art_rcy_tail_mem. apply mst_refl. }
  split; [gres; bveq|]. split; [gres; f_equal; lia|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

#[using="Type"] Lemma art_rcy_tail_mem_facts : forall (M : word -> option byte) tmp k b, 0x696000 <= tmp -> tmp + 32 < 2 ^ 64 -> cellA M (0x13c8b0 + 152) 4 257 ->
  mem_grows M (art_rcy_tail_mem M tmp k b) /\ art_agree [(tmp, 8); (tmp + 16, 8); (0x13c8b0 + 152, 4)] M (art_rcy_tail_mem M tmp k b)
  /\ cellA (art_rcy_tail_mem M tmp k b) tmp 8 k /\ cellA (art_rcy_tail_mem M tmp k b) (tmp + 16) 8 b /\ cellA (art_rcy_tail_mem M tmp k b) (0x13c8b0 + 152) 4 0.
Proof.
  intros M tmp k b Htmp Htmp' Clk. unfold art_rcy_tail_mem.
  split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|]. split; [zcell|]. split; [zcell|].
  change (cellA (Wn 1 (Wn 1 (Wn 8 (Wn 8 M tmp k) (tmp + 16) b) (0x13c8b0 + 152) 0) (0x13c8b0 + 153) 0) (0x13c8b0 + 152) 4 (0 + 256 * 0 + 65536 * 0)).
  apply cell4_join; [lia|lia|lia|lia|lia| | | ].
  - zcell.
  - zcell.
  - destruct (cell4_split M (0x13c8b0 + 152) 257 ltac:(lia) ltac:(lia) ltac:(lia) Clk) as (_ & _ & C2). change (257 / 65536) with 0 in C2. zcell.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_rcy_epi : forall regs (M rom : word -> option byte) (raw : word) (sp g8 g9 g18 g19 g20 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 80) -> ret_ok raw -> 80 <= sp -> sp < 2 ^ 64 ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 g8 -> cellA M (sp - 24) 8 g9 -> cellA M (sp - 32) 8 g18 -> cellA M (sp - 40) 8 g19 -> cellA M (sp - 48) 8 g20 ->
  exists regs', msteps ASEGS (mkst regs (0x545c4 : word) M rom) (mkst regs' raw M rom)
    /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 8 = Z_to_bv 64 g8 /\ getr regs' 9 = Z_to_bv 64 g9 /\ getr regs' 18 = Z_to_bv 64 g18
    /\ getr regs' 19 = Z_to_bv 64 g19 /\ getr regs' 20 = Z_to_bv 64 g20
    /\ (forall r : reg, In r [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp g8 g9 g18 g19 g20 H2 Hret Hsp Hsp' F1 F8 F9 F18 F19 F20.
  eexists. split.
  { zld F_541ac D_541ac (sp - 8) F1. rewrite Z_to_bv_bv_unsigned.
    zld F_541b0 D_541b0 (sp - 16) F8. zld F_541b4 D_541b4 (sp - 24) F9. zld F_541b8 D_541b8 (sp - 32) F18. zld F_541bc D_541bc (sp - 40) F19. zld F_541c0 D_541c0 (sp - 48) F20.
    zstep F_541c4 D_541c4.
    stepret F_541c8 D_541c8 raw ltac:(reflexivity).
    apply mst_refl. }
  split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
  split; [gres; reflexivity|]. split; [gres; reflexivity|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.
End FPX.
