(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac Pm9ArtLeaf Pm9ArtAllocG Pm9ArtPoison ArtRuns ArtRunsMem Pm9ArtFp Pm9ArtFree1 Pm9ArtCellEx Pm9ArtRecycle4.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm9_code_5b000_5c000.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_rcy_head_mem (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
  Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18)))
    (sp - 40) (U (getr regs 19))) (sp - 48) (U (getr regs 20))) (sp - 80) 0) (sp - 72) 0) (sp - 64) 0) (sp - 56) 0) (0x15a970 + 152) 257.

Section FPX. Context {fx : PropExec.FPState}.

Lemma art_rcy_head : forall regs (M rom : word -> option byte) (raw : word) (sp mn cnt gbytes gfirst : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 0x15a970 -> getr regs 11 = Z_to_bv 64 mn ->
  0x6b4000 + 80 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 80) 80 -> wrA M (0x15a970 + 152) 4 ->
  1 <= cnt -> 16384 * cnt <= gbytes -> gbytes < 2 ^ 57 -> 0 <= mn < gbytes -> 0 <= gfirst < 2 ^ 64 ->
  cellA M (0x15a970 + 152) 4 256 -> cellA M (0x15a970 + 184) 8 gbytes -> cellA M (0x15a970 + 160) 8 cnt -> cellA M (0x15a970 + 168) 8 gfirst ->
  exists regs', msteps ASEGS (mkst regs (0x5b68c : word) M rom) (mkst regs' (0x5b788 : word) (art_rcy_head_mem M sp raw regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (sp - 80) /\ getr regs' 10 = Z_to_bv 64 0x15a970 /\ getr regs' 11 = Z_to_bv 64 mn /\ getr regs' 14 = Z_to_bv 64 0 /\ getr regs' 15 = Z_to_bv 64 0
    /\ getr regs' 16 = Z_to_bv 64 cnt /\ getr regs' 5 = Z_to_bv 64 gfirst
    /\ (forall r : reg, In r [1; 3; 4; 8; 9; 12; 13; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp mn cnt gbytes gfirst H1 H2 H10 H11 Hsp Hsp' W Wlk Hcnt Hmerge Hgb Hmn Hgf Clk Cgb Ccnt Cgf.
  eexists. split.
  { zstep F_5b644 D_5b644.
    zsd F_5b648 D_5b648 (sp - 8) (U raw) ltac:(rewok W). zsd F_5b64c D_5b64c (sp - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_5b650 D_5b650 (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_5b654 D_5b654 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_5b658 D_5b658 (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_5b65c D_5b65c (sp - 48) (U (getr regs 20)) ltac:(rewok W).
    zsd F_5b660 D_5b660 (sp - 80) 0 ltac:(rewok W). zsd F_5b664 D_5b664 (sp - 72) 0 ltac:(rewok W).
    zsd F_5b668 D_5b668 (sp - 64) 0 ltac:(rewok W). zsd F_5b66c D_5b66c (sp - 56) 0 ltac:(rewok W).
    zstep F_5b670 D_5b670. zstep F_5b674 D_5b674.
    stepn F_5b678 D_5b678. rwH. zclosed (0x15a970 + 152).
    zstep F_5b67c D_5b67c.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Clk' : cellA X (0x15a970 + 152) 4 256) by zcell; assert (Wlk' : wokA X (0x15a970 + 152) 4) by zwok end.
    zcas6 F_5b680 D_5b680 F_5b684 D_5b684 F_5b688 D_5b688 F_5b68c D_5b68c F_5b690 D_5b690 F_5b694 D_5b694 (0x15a970 + 152) 256 257 1 257 Clk' Wlk'.
    zbft F_5b698 D_5b698.
    stepn F_5b69c D_5b69c. rwH. zclosed 0.
    zbft F_5b6a0 D_5b6a0.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cgb' : cellA X (0x15a970 + 184) 8 gbytes) by zcell; assert (Ccnt' : cellA X (0x15a970 + 160) 8 cnt) by zcell;
      assert (Cgf' : cellA X (0x15a970 + 168) 8 gfirst) by zcell;
      assert (T0 : cellA X (sp - 80) 8 0) by zcell; assert (T16 : cellA X (sp - 64) 8 0) by zcell end.
    zld F_5b6a4 D_5b6a4 (0x15a970 + 184) Cgb'.
    zld F_5b6a8 D_5b6a8 (0x15a970 + 160) Ccnt'.
    zstep F_5b6ac D_5b6ac.
    zbft F_5b6b0 D_5b6b0.
    zbft F_5b6b4 D_5b6b4.
    stepn F_5b6b8 D_5b6b8. zcl4.
    zstep F_5b6bc D_5b6bc. zstep F_5b6c0 D_5b6c0. zstep F_5b6c4 D_5b6c4.
    zbtk F_5b6c8 D_5b6c8.
    zld F_5b700 D_5b700 (sp - 80) T0.
    zld F_5b704 D_5b704 (sp - 64) T16.
    zld F_5b708 D_5b708 (0x15a970 + 184) Cgb'.
    zbft F_5b70c D_5b70c.
    zld F_5b710 D_5b710 (0x15a970 + 168) Cgf'.
    stepn F_5b714 D_5b714.
    unfold art_rcy_head_mem. apply mst_refl. }
  split; [gres; reflexivity|]. split; [gres; exact H10|]. split; [gres; exact H11|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
  split; [gres; reflexivity|]. split; [gres; reflexivity|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

Lemma art_rcy_pop : forall regs (M rom : word -> option byte) (tmp k plast gc b next size gbytes glast tbytes tfirst : Z),
  getr regs 10 = Z_to_bv 64 0x15a970 -> getr regs 14 = Z_to_bv 64 k -> getr regs 15 = Z_to_bv 64 plast -> getr regs 16 = Z_to_bv 64 gc -> getr regs 5 = Z_to_bv 64 b ->
  getr regs 2 = Z_to_bv 64 tmp ->
  0x6b4000 <= tmp -> tmp + 32 < 2 ^ 64 -> 0x6b4000 <= b -> b + 8192 < 2 ^ 64 -> apart tmp 32 b 8192 -> 0 <= k < 2 ^ 63 -> 1 <= gc < 2 ^ 64 ->
  0 <= next < 2 ^ 64 -> 0 <= size < 2 ^ 64 -> 0 <= gbytes < 2 ^ 64 -> 0 <= tbytes < 2 ^ 64 ->
  (k <> 0 -> 0x6b4000 <= plast /\ plast + 8 < 2 ^ 64 /\ apart plast 8 b 8192 /\ apart plast 8 tmp 32 /\ wrA M plast 8) ->
  wrA M tmp 32 -> wrA M (0x15a970 + 160) 32 -> wrA M b 8 ->
  cellA M b 8 next -> cellA M (b + 8) 8 size -> cellA M (0x15a970 + 184) 8 gbytes -> cellA M (0x15a970 + 176) 8 glast -> cellA M (tmp + 24) 8 tbytes -> cellA M (tmp + 8) 8 tfirst ->
  exists regs' (M' : word -> option byte), msteps ASEGS (mkst regs (0x5b788 : word) M rom) (mkst regs' (0x5b784 : word) M' rom)
    /\ getr regs' 14 = Z_to_bv 64 (k + 1) /\ getr regs' 15 = Z_to_bv 64 b /\ getr regs' 5 = Z_to_bv 64 next /\ getr regs' 7 = Z_to_bv 64 (gbytes - size) /\ getr regs' 16 = Z_to_bv 64 (gc - 1) /\ getr regs' 6 = Z_to_bv 64 b
    /\ (forall r : reg, In r [1; 2; 3; 4; 8; 9; 10; 11; 12; 13; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r)
    /\ mem_grows M M' /\ art_agree [(0x15a970 + 160, 32); (b, 8); (tmp, 32); (plast, if k =? 0 then 0 else 8)] M M'
    /\ cellA M' (0x15a970 + 168) 8 next /\ cellA M' (0x15a970 + 160) 8 (gc - 1) /\ cellA M' (0x15a970 + 184) 8 (gbytes - size) /\ cellA M' b 8 0
    /\ (next = 0 -> cellA M' (0x15a970 + 176) 8 0) /\ (next <> 0 -> cellA M' (0x15a970 + 176) 8 glast)
    /\ (k = 0 -> cellA M' (tmp + 8) 8 b) /\ (k <> 0 -> cellA M' (tmp + 8) 8 tfirst /\ cellA M' plast 8 b)
    /\ cellA M' (tmp + 24) 8 (tbytes + size).
Proof.
  intros regs M rom tmp k plast gc b next size gbytes glast tbytes tfirst H10 H14 H15 H16 H5 H2 Htmp Htmp' Hb Hb' Atb Hk Hgc Hnext Hsize Hgb Htb Hpl Wt Wq Wb
    Cnext Csize Cgb Cgl Ctb Ctf.
  unfold apart in Atb.
  destruct (Z.eq_dec next 0) as [N0|N1]; destruct (Z.eq_dec k 0) as [K0|K1].
  - rewrite (proj2 (Z.eqb_eq k 0) K0). eexists. eexists. split.
    { zbft F_5b740 D_5b740.
      zld F_5b744 D_5b744 b Cnext.
      zsd F_5b748 D_5b748 (0x15a970 + 168) next ltac:(rewok Wq).
      zbft F_5b74c D_5b74c.
      zsd F_5b750 D_5b750 (0x15a970 + 176) 0 ltac:(rewok Wq).
      zstep F_5b754 D_5b754.
      zsd F_5b758 D_5b758 (0x15a970 + 160) (gc + -1) ltac:(rewok Wq).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize' : cellA X (b + 8) 8 size) by zcell; assert (Cgb' : cellA X (0x15a970 + 184) 8 gbytes) by zcell end.
      zld F_5b75c D_5b75c (b + 8) Csize'.
      zld F_5b760 D_5b760 (0x15a970 + 184) Cgb'.
      zstep F_5b764 D_5b764.
      zsd F_5b768 D_5b768 (0x15a970 + 184) (gbytes - size) ltac:(rewok Wq).
      zstep F_5b76c D_5b76c.
      zsd F_5b770 D_5b770 b 0 ltac:(rewok Wb).
      zbft F_5b774 D_5b774.
      stepn F_5b778 D_5b778.
      zsd F_5b78c D_5b78c (tmp + 8) b ltac:(rewok Wt).
      stepn F_5b790 D_5b790.
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize2 : cellA X (b + 8) 8 size) by zcell; assert (Ctb' : cellA X (tmp + 24) 8 tbytes) by zcell end.
      zld F_5b71c D_5b71c (b + 8) Csize2.
      zld F_5b720 D_5b720 (tmp + 24) Ctb'.
      zstep F_5b724 D_5b724.
      zsd F_5b728 D_5b728 (tmp + 24) (tbytes + size) ltac:(rewok Wt).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cgb2 : cellA X (0x15a970 + 184) 8 (gbytes - size)) by zcell end.
      zld F_5b72c D_5b72c (0x15a970 + 184) Cgb2.
      zstep F_5b730 D_5b730. zstep F_5b734 D_5b734. zstep F_5b738 D_5b738.
      apply mst_refl. }
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
    split. { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
    split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|].
    split; [zcell|]. split; [replace (gc - 1) with (gc + -1) by lia; zcell|]. split; [zcell|]. split; [zcell|].
    split; [intros _; zcell|]. split; [intros X; exfalso; lia|].
    split; [intros _; zcell|]. split; [intros X; exfalso; lia|]. zcell.
  - destruct (Hpl K1) as (Hp0 & Hp1 & Apb & Apt & Wpl). unfold apart in Apb, Apt. rewrite (proj2 (Z.eqb_neq k 0) K1). eexists. eexists. split.
    { zbft F_5b740 D_5b740.
      zld F_5b744 D_5b744 b Cnext.
      zsd F_5b748 D_5b748 (0x15a970 + 168) next ltac:(rewok Wq).
      zbft F_5b74c D_5b74c.
      zsd F_5b750 D_5b750 (0x15a970 + 176) 0 ltac:(rewok Wq).
      zstep F_5b754 D_5b754.
      zsd F_5b758 D_5b758 (0x15a970 + 160) (gc + -1) ltac:(rewok Wq).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize' : cellA X (b + 8) 8 size) by zcell; assert (Cgb' : cellA X (0x15a970 + 184) 8 gbytes) by zcell end.
      zld F_5b75c D_5b75c (b + 8) Csize'.
      zld F_5b760 D_5b760 (0x15a970 + 184) Cgb'.
      zstep F_5b764 D_5b764.
      zsd F_5b768 D_5b768 (0x15a970 + 184) (gbytes - size) ltac:(rewok Wq).
      zstep F_5b76c D_5b76c.
      zsd F_5b770 D_5b770 b 0 ltac:(rewok Wb).
      zbtk F_5b774 D_5b774.
      zsd F_5b718 D_5b718 plast b ltac:(rewok Wpl).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize2 : cellA X (b + 8) 8 size) by zcell; assert (Ctb' : cellA X (tmp + 24) 8 tbytes) by zcell end.
      zld F_5b71c D_5b71c (b + 8) Csize2.
      zld F_5b720 D_5b720 (tmp + 24) Ctb'.
      zstep F_5b724 D_5b724.
      zsd F_5b728 D_5b728 (tmp + 24) (tbytes + size) ltac:(rewok Wt).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cgb2 : cellA X (0x15a970 + 184) 8 (gbytes - size)) by zcell end.
      zld F_5b72c D_5b72c (0x15a970 + 184) Cgb2.
      zstep F_5b730 D_5b730. zstep F_5b734 D_5b734. zstep F_5b738 D_5b738.
      apply mst_refl. }
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
    split. { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
    split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|].
    split; [zcell|]. split; [replace (gc - 1) with (gc + -1) by lia; zcell|]. split; [zcell|]. split; [zcell|].
    split; [intros _; zcell|]. split; [intros X; exfalso; lia|].
    split; [intros X; exfalso; lia|]. split; [intros _; split; zcell|]. zcell.
  - rewrite (proj2 (Z.eqb_eq k 0) K0). eexists. eexists. split.
    { zbft F_5b740 D_5b740.
      zld F_5b744 D_5b744 b Cnext.
      zsd F_5b748 D_5b748 (0x15a970 + 168) next ltac:(rewok Wq).
      zbtk F_5b74c D_5b74c.
      zstep F_5b754 D_5b754.
      zsd F_5b758 D_5b758 (0x15a970 + 160) (gc + -1) ltac:(rewok Wq).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize' : cellA X (b + 8) 8 size) by zcell; assert (Cgb' : cellA X (0x15a970 + 184) 8 gbytes) by zcell end.
      zld F_5b75c D_5b75c (b + 8) Csize'.
      zld F_5b760 D_5b760 (0x15a970 + 184) Cgb'.
      zstep F_5b764 D_5b764.
      zsd F_5b768 D_5b768 (0x15a970 + 184) (gbytes - size) ltac:(rewok Wq).
      zstep F_5b76c D_5b76c.
      zsd F_5b770 D_5b770 b 0 ltac:(rewok Wb).
      zbft F_5b774 D_5b774.
      stepn F_5b778 D_5b778.
      zsd F_5b78c D_5b78c (tmp + 8) b ltac:(rewok Wt).
      stepn F_5b790 D_5b790.
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize2 : cellA X (b + 8) 8 size) by zcell; assert (Ctb' : cellA X (tmp + 24) 8 tbytes) by zcell end.
      zld F_5b71c D_5b71c (b + 8) Csize2.
      zld F_5b720 D_5b720 (tmp + 24) Ctb'.
      zstep F_5b724 D_5b724.
      zsd F_5b728 D_5b728 (tmp + 24) (tbytes + size) ltac:(rewok Wt).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cgb2 : cellA X (0x15a970 + 184) 8 (gbytes - size)) by zcell end.
      zld F_5b72c D_5b72c (0x15a970 + 184) Cgb2.
      zstep F_5b730 D_5b730. zstep F_5b734 D_5b734. zstep F_5b738 D_5b738.
      apply mst_refl. }
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
    split. { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
    split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|].
    split; [zcell|]. split; [replace (gc - 1) with (gc + -1) by lia; zcell|]. split; [zcell|]. split; [zcell|].
    split; [intros X; exfalso; lia|]. split; [intros _; zcell|].
    split; [intros _; zcell|]. split; [intros X; exfalso; lia|]. zcell.
  - destruct (Hpl K1) as (Hp0 & Hp1 & Apb & Apt & Wpl). unfold apart in Apb, Apt. rewrite (proj2 (Z.eqb_neq k 0) K1). eexists. eexists. split.
    { zbft F_5b740 D_5b740.
      zld F_5b744 D_5b744 b Cnext.
      zsd F_5b748 D_5b748 (0x15a970 + 168) next ltac:(rewok Wq).
      zbtk F_5b74c D_5b74c.
      zstep F_5b754 D_5b754.
      zsd F_5b758 D_5b758 (0x15a970 + 160) (gc + -1) ltac:(rewok Wq).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize' : cellA X (b + 8) 8 size) by zcell; assert (Cgb' : cellA X (0x15a970 + 184) 8 gbytes) by zcell end.
      zld F_5b75c D_5b75c (b + 8) Csize'.
      zld F_5b760 D_5b760 (0x15a970 + 184) Cgb'.
      zstep F_5b764 D_5b764.
      zsd F_5b768 D_5b768 (0x15a970 + 184) (gbytes - size) ltac:(rewok Wq).
      zstep F_5b76c D_5b76c.
      zsd F_5b770 D_5b770 b 0 ltac:(rewok Wb).
      zbtk F_5b774 D_5b774.
      zsd F_5b718 D_5b718 plast b ltac:(rewok Wpl).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize2 : cellA X (b + 8) 8 size) by zcell; assert (Ctb' : cellA X (tmp + 24) 8 tbytes) by zcell end.
      zld F_5b71c D_5b71c (b + 8) Csize2.
      zld F_5b720 D_5b720 (tmp + 24) Ctb'.
      zstep F_5b724 D_5b724.
      zsd F_5b728 D_5b728 (tmp + 24) (tbytes + size) ltac:(rewok Wt).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cgb2 : cellA X (0x15a970 + 184) 8 (gbytes - size)) by zcell end.
      zld F_5b72c D_5b72c (0x15a970 + 184) Cgb2.
      zstep F_5b730 D_5b730. zstep F_5b734 D_5b734. zstep F_5b738 D_5b738.
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
  exists regs', msteps ASEGS (mkst regs (0x5b784 : word) M rom) (mkst regs' (0x5b788 : word) M rom) /\ (forall r : reg, getr regs' r = getr regs r).
Proof.
  intros regs M rom mn gb H11 H7 Hmn Hgb. eexists. split. { zbft F_5b73c D_5b73c. apply mst_refl. } intros r. reflexivity.
Qed.
Lemma art_rcy_exit : forall regs (M rom : word -> option byte) (mn gb : Z),
  getr regs 11 = Z_to_bv 64 mn -> getr regs 7 = Z_to_bv 64 gb -> 0 <= gb <= mn -> mn < 2 ^ 64 ->
  exists regs', msteps ASEGS (mkst regs (0x5b784 : word) M rom) (mkst regs' (0x5b7dc : word) M rom) /\ (forall r : reg, getr regs' r = getr regs r).
Proof.
  intros regs M rom mn gb H11 H7 Hmn Hgb. eexists. split. { zbtk F_5b73c D_5b73c. apply mst_refl. } intros r. reflexivity.
Qed.

Definition art_rcy_tail_mem (M : word -> option byte) (tmp k b : Z) : word -> option byte :=
  Wn 1 (Wn 1 (Wn 8 (Wn 8 M tmp k) (tmp + 16) b) (0x15a970 + 152) 0) (0x15a970 + 153) 0.

Lemma art_rcy_tail : forall regs (M rom : word -> option byte) (tmp k b : Z),
  getr regs 2 = Z_to_bv 64 tmp -> getr regs 10 = Z_to_bv 64 0x15a970 -> getr regs 14 = Z_to_bv 64 k -> getr regs 6 = Z_to_bv 64 b ->
  0x6b4000 <= tmp -> tmp + 32 < 2 ^ 64 -> 0 <= k < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> wrA M tmp 32 -> wrA M (0x15a970 + 152) 4 ->
  exists regs', msteps ASEGS (mkst regs (0x5b7dc : word) M rom) (mkst regs' (0x5b9f4 : word) (art_rcy_tail_mem M tmp k b) rom)
    /\ getr regs' 1 = (0x5b7fc : bv 64)%bv /\ getr regs' 11 = Z_to_bv 64 tmp
    /\ (forall r : reg, In r [2; 3; 4; 8; 9; 10; 12; 13; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom tmp k b H2 H10 H14 H6 Htmp Htmp' Hk Hb Wt Wq.
  eexists. split.
  { zsd F_5b794 D_5b794 tmp k ltac:(rewok Wt).
    zsd F_5b798 D_5b798 (tmp + 16) b ltac:(rewok Wt).
    stepfence F_5b79c D_5b79c.
    zsb F_5b7a0 D_5b7a0 (0x15a970 + 152) 0 ltac:(zwok').
    stepfence F_5b7a4 D_5b7a4.
    zsb F_5b7a8 D_5b7a8 (0x15a970 + 153) 0 ltac:(zwok').
    zstep F_5b7ac D_5b7ac.
    stepn F_5b7b0 D_5b7b0.
    unfold art_rcy_tail_mem. apply mst_refl. }
  split; [gres; bveq|]. split; [gres; f_equal; lia|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

Lemma art_rcy_tail_mem_facts : forall (M : word -> option byte) tmp k b, 0x6b4000 <= tmp -> tmp + 32 < 2 ^ 64 -> cellA M (0x15a970 + 152) 4 257 ->
  mem_grows M (art_rcy_tail_mem M tmp k b) /\ art_agree [(tmp, 8); (tmp + 16, 8); (0x15a970 + 152, 4)] M (art_rcy_tail_mem M tmp k b)
  /\ cellA (art_rcy_tail_mem M tmp k b) tmp 8 k /\ cellA (art_rcy_tail_mem M tmp k b) (tmp + 16) 8 b /\ cellA (art_rcy_tail_mem M tmp k b) (0x15a970 + 152) 4 0.
Proof.
  intros M tmp k b Htmp Htmp' Clk. unfold art_rcy_tail_mem.
  split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|]. split; [zcell|]. split; [zcell|].
  change (cellA (Wn 1 (Wn 1 (Wn 8 (Wn 8 M tmp k) (tmp + 16) b) (0x15a970 + 152) 0) (0x15a970 + 153) 0) (0x15a970 + 152) 4 (0 + 256 * 0 + 65536 * 0)).
  apply cell4_join; [lia|lia|lia|lia|lia| | | ].
  - zcell.
  - zcell.
  - destruct (cell4_split M (0x15a970 + 152) 257 ltac:(lia) ltac:(lia) ltac:(lia) Clk) as (_ & _ & C2). change (257 / 65536) with 0 in C2. zcell.
Qed.

Lemma art_rcy_epi : forall regs (M rom : word -> option byte) (raw : word) (sp g8 g9 g18 g19 g20 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 80) -> ret_ok raw -> 80 <= sp -> sp < 2 ^ 64 ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 g8 -> cellA M (sp - 24) 8 g9 -> cellA M (sp - 32) 8 g18 -> cellA M (sp - 40) 8 g19 -> cellA M (sp - 48) 8 g20 ->
  exists regs', msteps ASEGS (mkst regs (0x5b7fc : word) M rom) (mkst regs' raw M rom)
    /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 8 = Z_to_bv 64 g8 /\ getr regs' 9 = Z_to_bv 64 g9 /\ getr regs' 18 = Z_to_bv 64 g18
    /\ getr regs' 19 = Z_to_bv 64 g19 /\ getr regs' 20 = Z_to_bv 64 g20
    /\ (forall r : reg, In r [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp g8 g9 g18 g19 g20 H2 Hret Hsp Hsp' F1 F8 F9 F18 F19 F20.
  eexists. split.
  { zld F_5b7b4 D_5b7b4 (sp - 8) F1. rewrite Z_to_bv_bv_unsigned.
    zld F_5b7b8 D_5b7b8 (sp - 16) F8. zld F_5b7bc D_5b7bc (sp - 24) F9. zld F_5b7c0 D_5b7c0 (sp - 32) F18. zld F_5b7c4 D_5b7c4 (sp - 40) F19. zld F_5b7c8 D_5b7c8 (sp - 48) F20.
    zstep F_5b7cc D_5b7cc.
    stepret F_5b7d0 D_5b7d0 raw ltac:(reflexivity).
    apply mst_refl. }
  split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
  split; [gres; reflexivity|]. split; [gres; reflexivity|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.
End FPX.
