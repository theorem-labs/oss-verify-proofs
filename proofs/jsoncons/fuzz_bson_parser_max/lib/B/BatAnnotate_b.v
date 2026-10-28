(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.GcFlush06.  (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MemsetLib As0StepLib
     ArtMem ArtRegs ArtAtomics ArtTac.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.muslA Require Import Ba0SumsMemset_code_b Ba0SumsMemset_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r7af8c_7b250_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatPoison_b BatPoisonRun_b BatPoison2G_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Definition art_ann_kept (r : reg) : Prop := r = 3%bv \/ r = 4%bv \/ r = 22%bv \/ r = 23%bv \/ r = 24%bv \/ r = 25%bv \/ r = 26%bv \/ r = 27%bv.

(* [comment removed for export] *)
Lemma art_ann_andim8 : forall x, 0 <= x < 2 ^ 64 -> x mod 8 = 0 -> v_andi (Z_to_bv 64 x) (-8) = Z_to_bv 64 x.
Proof.
  intros x Hx H8. unfold v_andi. rewrite art_u_lit by lia. change (bv_wrap 64 (-8)) with 18446744073709551608. rewrite art_land_m8 by lia.
  f_equal. pose proof (Z.div_mod x 8 ltac:(lia)). lia.
Qed.
Lemma art_ann_andim8_up : forall x, 0 <= x -> x + 7 < 2 ^ 64 -> x mod 8 = 0 -> v_andi (Z_to_bv 64 (x + 7)) (-8) = Z_to_bv 64 x.
Proof.
  intros x Hx Hx' H8. unfold v_andi. rewrite art_u_lit by lia. change (bv_wrap 64 (-8)) with 18446744073709551608. rewrite art_land_m8 by lia.
  f_equal. pose proof (Z.div_mod x 8 ltac:(lia)) as D. rewrite H8, Z.add_0_r in D.
  replace (x + 7) with (7 + (x / 8) * 8) by lia. rewrite Z.div_add by lia. change (7 / 8) with 0. lia.
Qed.
Lemma art_ann_and7 : forall x, 0 <= x < 2 ^ 64 -> x mod 8 = 0 -> v_andi (Z_to_bv 64 x) 7 = Z_to_bv 64 0.
Proof.
  intros x Hx H8. rewrite art_zb_andi by lia. f_equal. rewrite Z.land_ones with (n := 3) by lia. change (2 ^ 3) with 8. exact H8.
Qed.

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_ann_pre : forall regs (M rom : word -> option byte) (raw : word) (sp0 b c u u' : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp0 -> getr regs 10 = Z_to_bv 64 b -> getr regs 11 = Z_to_bv 64 (b + c) ->
  getr regs 12 = Z_to_bv 64 (b + u) -> getr regs 13 = Z_to_bv 64 (b + u') ->
  0 <= b -> b + c <= 2 ^ 47 -> 0 <= u <= c -> 0 <= u' <= c -> c < 2 ^ 40 ->
  0x696000 + 2192 <= sp0 -> sp0 < 2 ^ 63 -> wrA M (sp0 - 2192) 2192 ->
  cellA M 0x1374b8 8 0x13d438 -> cellA M (0x13d438 + 96) 1 1 -> cellA M 0x137510 8 0x1cf6d8 -> cellA M 0x1cf6d8 4 0 ->
  exists regs',
    msteps ASEGS (mkst regs (0x7ba7c : word) M rom)
      (mkst regs' (0x7bb94 : word) (art_poison_frame M sp0 (U raw) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21))) rom)
    /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 (sp0 - 2128) /\ getr regs' 8 = Z_to_bv 64 sp0
    /\ getr regs' 9 = Z_to_bv 64 b /\ getr regs' 18 = Z_to_bv 64 (b + u') /\ getr regs' 19 = Z_to_bv 64 (b + u) /\ getr regs' 20 = Z_to_bv 64 (b + c)
    /\ (forall r : reg, art_ann_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp0 b c u u' H1 H2 H10 H11 H12 H13 Hb Hbc Hu Hu' Hc40 Hsp Hsp' W CG CF CV CV0.
  eexists. split.
  { zstep F_7b664 D_7b664.
    zsd F_7b668 D_7b668 (sp0 - 8) (U raw) ltac:(rewok W).
    zsd F_7b66c D_7b66c (sp0 - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_7b670 D_7b670 (sp0 - 24) (U (getr regs 9)) ltac:(rewok W).
    zsd F_7b674 D_7b674 (sp0 - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_7b678 D_7b678 (sp0 - 40) (U (getr regs 19)) ltac:(rewok W).
    zsd F_7b67c D_7b67c (sp0 - 48) (U (getr regs 20)) ltac:(rewok W).
    zsd F_7b680 D_7b680 (sp0 - 56) (U (getr regs 21)) ltac:(rewok W).
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (C1 : cellA X 0x1374b8 8 0x13d438) by zcell; assert (C2 : cellA X (0x13d438 + 96) 1 1) by zcell;
      assert (C3 : cellA X 0x137510 8 0x1cf6d8) by zcell; assert (C4 : cellA X 0x1cf6d8 4 0) by zcell end.
    zstep F_7b684 D_7b684. zstep F_7b688 D_7b688. zstep F_7b68c D_7b68c.
    zstep F_7b690 D_7b690. zld F_7b694 D_7b694 0x1374b8 C1.
    zlbu F_7b698 D_7b698 (0x13d438 + 96) C2.
    zbft F_7b69c D_7b69c.
    zstep F_7b6a0 D_7b6a0. zstep F_7b6a4 D_7b6a4. zstep F_7b6a8 D_7b6a8.
    zstep F_7b6ac D_7b6ac. zld F_7b6b0 D_7b6b0 0x137510 C3. zlw F_7b6b4 D_7b6b4 0x1cf6d8 C4.
    zstep F_7b6b8 D_7b6b8. zbft F_7b6bc D_7b6bc.
    zbtk F_7b6c0 D_7b6c0.
    zbft F_7b75c D_7b75c. zbft F_7b760 D_7b760. zbft F_7b764 D_7b764.
    zstep F_7b768 D_7b768. zstep F_7b76c D_7b76c. zstep F_7b770 D_7b770. zstep F_7b774 D_7b774.
    zbft F_7b778 D_7b778.
    apply mst_refl. }
  zsplit; try kept_solve.
  intros r Hr. unfold art_ann_kept in Hr. destruct Hr as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; kept_solve.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_ann_grow : forall regs (M rom : word -> option byte) (sp0 b c u u' : Z),
  getr regs 2 = Z_to_bv 64 (sp0 - 2128) -> getr regs 9 = Z_to_bv 64 b -> getr regs 18 = Z_to_bv 64 (b + u') -> getr regs 19 = Z_to_bv 64 (b + u) ->
  getr regs 20 = Z_to_bv 64 (b + c) ->
  b mod 8 = 0 -> c mod 8 = 0 -> u mod 8 = 0 -> u' mod 8 = 0 -> 0 <= b -> b + c <= 2 ^ 47 -> 0 <= u -> u < u' -> u' <= c ->
  exists regs', msteps ASEGS (mkst regs (0x7bb94 : word) M rom) (mkst regs' (0x7ab38 : word) M rom)
    /\ getr regs' 1 = Z_to_bv 64 0x7bcc4 /\ getr regs' 2 = Z_to_bv 64 (sp0 - 2128) /\ getr regs' 10 = Z_to_bv 64 (b + u) /\ getr regs' 11 = Z_to_bv 64 (u' - u)
    /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = Z_to_bv 64 (b + u') /\ getr regs' 18 = Z_to_bv 64 (b + u')
    /\ (forall r : reg, art_ann_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp0 b c u u' H2 H9 H18 H19 H20 Hb8 Hc8 Hu8 Hu8' Hb Hbc Hu Huu Hu'.
  assert (Ebc : (b + c) mod 8 = 0) by (rewrite Z.add_mod by lia; rewrite Hb8, Hc8; reflexivity).
  assert (Ebu : (b + u) mod 8 = 0) by (rewrite Z.add_mod by lia; rewrite Hb8, Hu8; reflexivity).
  assert (Ebu' : (b + u') mod 8 = 0) by (rewrite Z.add_mod by lia; rewrite Hb8, Hu8'; reflexivity).
  eexists. split.
  { zbft F_7b77c D_7b77c.
    stepn F_7b780 D_7b780. rwH. rewrite art_ann_and7 by lia.
    zbft F_7b784 D_7b784.
    zstep F_7b788 D_7b788. zstep F_7b78c D_7b78c. zstep F_7b790 D_7b790.
    stepn F_7b794 D_7b794. rwH. rewrite art_ann_and7 by lia.
    zbft F_7b798 D_7b798.
    zstep F_7b79c D_7b79c. zstep F_7b7a0 D_7b7a0.
    zbtk F_7b7a4 D_7b7a4.
    stepn F_7b874 D_7b874. rwH. rewrite art_ann_andim8 by lia.
    zbft F_7b878 D_7b878.
    zstep F_7b87c D_7b87c.
    stepn F_7b880 D_7b880. rwH. rewrite art_ann_andim8 by lia.
    zstep F_7b884 D_7b884.
    stepn F_7b888 D_7b888. rwH. rewrite art_ann_andim8_up by lia.
    zbtk F_7b88c D_7b88c.
    zstep F_7b7c0 D_7b7c0. zstep F_7b7c4 D_7b7c4. zstep F_7b7c8 D_7b7c8. zstep F_7b8a8 D_7b8a8.
    apply mst_refl. }
  zsplit; try kept_solve.
  intros r Hr. unfold art_ann_kept in Hr. destruct Hr as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; kept_solve.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_ann_shrink : forall regs (M rom : word -> option byte) (sp0 b c u u' : Z),
  getr regs 2 = Z_to_bv 64 (sp0 - 2128) -> getr regs 9 = Z_to_bv 64 b -> getr regs 18 = Z_to_bv 64 (b + u') -> getr regs 19 = Z_to_bv 64 (b + u) ->
  getr regs 20 = Z_to_bv 64 (b + c) ->
  b mod 8 = 0 -> c mod 8 = 0 -> u mod 8 = 0 -> u' mod 8 = 0 -> 0 <= b -> b + c <= 2 ^ 47 -> 0 <= u' -> u' < u -> u <= c ->
  exists regs', msteps ASEGS (mkst regs (0x7bb94 : word) M rom) (mkst regs' (0x7ab38 : word) M rom)
    /\ getr regs' 1 = Z_to_bv 64 0x7bcc4 /\ getr regs' 2 = Z_to_bv 64 (sp0 - 2128) /\ getr regs' 10 = Z_to_bv 64 (b + u') /\ getr regs' 11 = Z_to_bv 64 (u - u')
    /\ getr regs' 12 = Z_to_bv 64 252 /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = Z_to_bv 64 (b + u') /\ getr regs' 18 = Z_to_bv 64 (b + u')
    /\ (forall r : reg, art_ann_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp0 b c u u' H2 H9 H18 H19 H20 Hb8 Hc8 Hu8 Hu8' Hb Hbc Hu Huu Hu'.
  assert (Ebc : (b + c) mod 8 = 0) by (rewrite Z.add_mod by lia; rewrite Hb8, Hc8; reflexivity).
  assert (Ebu : (b + u) mod 8 = 0) by (rewrite Z.add_mod by lia; rewrite Hb8, Hu8; reflexivity).
  assert (Ebu' : (b + u') mod 8 = 0) by (rewrite Z.add_mod by lia; rewrite Hb8, Hu8'; reflexivity).
  eexists. split.
  { zbft F_7b77c D_7b77c.
    stepn F_7b780 D_7b780. rwH. rewrite art_ann_and7 by lia.
    zbft F_7b784 D_7b784.
    zstep F_7b788 D_7b788. zstep F_7b78c D_7b78c. zstep F_7b790 D_7b790.
    stepn F_7b794 D_7b794. rwH. rewrite art_ann_and7 by lia.
    zbft F_7b798 D_7b798.
    zstep F_7b79c D_7b79c. zstep F_7b7a0 D_7b7a0.
    zbft F_7b7a4 D_7b7a4.
    stepn F_7b7a8 D_7b7a8. rwH. rewrite art_ann_andim8 by lia.
    zbft F_7b7ac D_7b7ac.
    stepn F_7b7b0 D_7b7b0. rwH. rewrite art_ann_andim8 by lia.
    zstep F_7b7b4 D_7b7b4.
    stepn F_7b7b8 D_7b7b8. rwH. rewrite art_ann_andim8_up by lia.
    zbtk F_7b7bc D_7b7bc.
    zstep F_7b890 D_7b890.
    stepn F_7b894 D_7b894. rwH. rewrite art_ann_andim8_up by lia.
    zbft F_7b898 D_7b898.
    zstep F_7b89c D_7b89c. zstep F_7b8a0 D_7b8a0. zstep F_7b8a4 D_7b8a4. zstep F_7b8a8 D_7b8a8.
    apply mst_refl. }
  zsplit; try kept_solve.
  intros r Hr. unfold art_ann_kept in Hr. destruct Hr as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; kept_solve.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_ann_eq0 : forall regs (M rom : word -> option byte),
  getr regs 19 = getr regs 18 -> msteps ASEGS (mkst regs (0x7bb94 : word) M rom) (mkst regs (0x7bce4 : word) M rom).
Proof. intros regs M rom E. zbtk F_7b77c D_7b77c. apply mst_refl. Qed.
#[using="Type"] Lemma art_ann_tail0 : forall regs (M rom : word -> option byte),
  getr regs 18 = getr regs 9 -> msteps ASEGS (mkst regs (0x7bcc4 : word) M rom) (mkst regs (0x7bce4 : word) M rom).
Proof. intros regs M rom E. zbtk F_7b8ac D_7b8ac. apply mst_refl. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_ann_epi : forall regs (M rom : word -> option byte) (raw : word) (sp0 g16 g24 g32 g40 g48 g56 : Z),
  getr regs 2 = Z_to_bv 64 (sp0 - 2128) -> 2128 <= sp0 -> sp0 < 2 ^ 63 -> ret_ok raw ->
  0 <= g16 < 2 ^ 64 -> 0 <= g24 < 2 ^ 64 -> 0 <= g32 < 2 ^ 64 -> 0 <= g40 < 2 ^ 64 -> 0 <= g48 < 2 ^ 64 -> 0 <= g56 < 2 ^ 64 ->
  cellA M (sp0 - 8) 8 (U raw) -> cellA M (sp0 - 16) 8 g16 -> cellA M (sp0 - 24) 8 g24 -> cellA M (sp0 - 32) 8 g32 -> cellA M (sp0 - 40) 8 g40 ->
  cellA M (sp0 - 48) 8 g48 -> cellA M (sp0 - 56) 8 g56 ->
  exists regs', msteps ASEGS (mkst regs (0x7bce4 : word) M rom) (mkst regs' raw M rom)
    /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp0 /\ getr regs' 8 = Z_to_bv 64 g16 /\ getr regs' 9 = Z_to_bv 64 g24
    /\ getr regs' 18 = Z_to_bv 64 g32 /\ getr regs' 19 = Z_to_bv 64 g40 /\ getr regs' 20 = Z_to_bv 64 g48 /\ getr regs' 21 = Z_to_bv 64 g56
    /\ (forall r : reg, art_ann_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp0 g16 g24 g32 g40 g48 g56 H2 Hsp Hsp' Hret Hg16 Hg24 Hg32 Hg40 Hg48 Hg56 C8 C16 C24 C32 C40 C48 C56.
  eexists. split.
  { zstep F_7b8cc D_7b8cc.
    zld F_7b8d0 D_7b8d0 (sp0 - 8) C8. rewrite Z_to_bv_bv_unsigned.
    zld F_7b8d4 D_7b8d4 (sp0 - 16) C16. zld F_7b8d8 D_7b8d8 (sp0 - 24) C24. zld F_7b8dc D_7b8dc (sp0 - 32) C32.
    zld F_7b8e0 D_7b8e0 (sp0 - 40) C40. zld F_7b8e4 D_7b8e4 (sp0 - 48) C48. zld F_7b8e8 D_7b8e8 (sp0 - 56) C56.
    zstep F_7b8ec D_7b8ec.
    stepret F_7b8f0 D_7b8f0 raw ltac:(rwH; reflexivity).
    apply mst_refl. }
  zsplit; try kept_solve.
  intros r Hr. unfold art_ann_kept in Hr. destruct Hr as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; kept_solve.
Qed.

Lemma art_ann_kept_poison : forall r, art_ann_kept r -> art_poison_kept r.
Proof.
  intros r Hr. unfold art_ann_kept in Hr. unfold art_poison_kept.
  destruct Hr as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; repeat split; intros E; apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate E.
Qed.
Lemma art_pf_grows : forall M sp ra s0 s1 s2 s3 s4 s5, mem_grows M (art_poison_frame M sp ra s0 s1 s2 s3 s4 s5).
Proof. intros. unfold art_poison_frame. repeat (eapply mem_grows_trans; [|apply Wn_grows]). apply mem_grows_refl. Qed.
Lemma art_ann_mod8 : forall x y, x mod 8 = 0 -> y mod 8 = 0 -> (x + y) mod 8 = 0 /\ (x - y) mod 8 = 0.
Proof. intros x y Hx Hy. split; [rewrite Z.add_mod by lia|rewrite Zminus_mod]; rewrite Hx, Hy; reflexivity. Qed.

(* [comment removed for export] *)
Definition art_ann_lo (b u u' : Z) : Z := b + Z.min u u'.
Definition art_ann_n (u u' : Z) : Z := Z.abs (u - u').
Definition art_ann_v (u u' : Z) : Z := if u <? u' then 0 else 252.

Lemma art_ann_ret_7b8ac : ret_ok (Z_to_bv 64 0x7bcc4).
Proof. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.

#[using="Type"] Theorem art_annotate_run : forall regs (M rom : word -> option byte) (raw : word) (sp0 b c u u' : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp0 -> getr regs 10 = Z_to_bv 64 b -> getr regs 11 = Z_to_bv 64 (b + c) ->
  getr regs 12 = Z_to_bv 64 (b + u) -> getr regs 13 = Z_to_bv 64 (b + u') ->
  4096 <= b -> b mod 8 = 0 -> c mod 8 = 0 -> u mod 8 = 0 -> u' mod 8 = 0 -> 0 <= u <= c -> 0 <= u' <= c -> b + c <= 2 ^ 47 -> c < 2 ^ 40 ->
  (b + c <= 0x7fff7000 \/ 0x10007fff8000 <= b) ->
  0x10007fff8000 + 2192 <= sp0 -> sp0 < 2 ^ 63 -> wrA M (sp0 - 2192) 2192 ->
  art_layout M -> cellA M (0x13d438 + 96) 1 1 -> cellA M 0x137510 8 0x1cf6d8 -> cellA M 0x1cf6d8 4 0 ->
  wrA M (SB + art_ann_lo b u u' / 8) (art_ann_n u u' / 8) ->
  exists regs' M',
    msteps ASEGS (mkst regs (0x7ba7c : word) M rom) (mkst regs' raw M' rom)
    /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp0
    /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19
    /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21
    /\ (forall r : reg, art_ann_kept r -> getr regs' r = getr regs r)
    /\ mem_grows M M'
    /\ (forall x : word, ~ (sp0 - 2192 <= U x < sp0) -> ~ (SB + art_ann_lo b u u' / 8 <= U x < SB + art_ann_lo b u u' / 8 + art_ann_n u u' / 8) -> M' x = M x)
    /\ (forall i, 0 <= i < art_ann_n u u' / 8 -> M' (Z_to_bv 64 (SB + art_ann_lo b u u' / 8 + i)) = Some (Z_to_bv 8 (art_ann_v u u'))).
Proof.
  intros regs M rom raw sp0 b c u u' H1 Hret H2 H10 H11 H12 H13 Hb Hb8 Hc8 Hu8 Hu8' Hu Hu' Hbc Hc40 Hplace Hsp Hsp' W L CF CV CV0 Wsh.
  pose proof L as L'. destruct L' as (_ & _ & _ & _ & _ & _ & _ & _ & CG & _).
  destruct (art_ann_pre regs M rom raw sp0 b c u u' H1 H2 H10 H11 H12 H13 ltac:(lia) Hbc Hu Hu' Hc40 ltac:(lia) Hsp' W CG CF CV CV0)
    as (r1 & RUN1 & P1 & P2 & P8 & P9 & P18 & P19 & P20 & PK).
  set (M2 := art_poison_frame M sp0 (U raw) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21))) in *.
  assert (GR2 : mem_grows M M2) by (apply art_pf_grows).
  assert (FR2 : forall x : word, ~ (sp0 - 56 <= U x < sp0) -> M2 x = M x).
  { intros x Hx. unfold M2, art_poison_frame. rewrite !Wn_outside by (cbn; lia). reflexivity. }
  (* [comment removed for export] *)
  assert (C8 : cellA M2 (sp0 - 8) 8 (U raw)) by (unfold M2, art_poison_frame; zcell).
  assert (C16 : cellA M2 (sp0 - 16) 8 (U (getr regs 8))) by (unfold M2, art_poison_frame; zcell).
  assert (C24 : cellA M2 (sp0 - 24) 8 (U (getr regs 9))) by (unfold M2, art_poison_frame; zcell).
  assert (C32 : cellA M2 (sp0 - 32) 8 (U (getr regs 18))) by (unfold M2, art_poison_frame; zcell).
  assert (C40 : cellA M2 (sp0 - 40) 8 (U (getr regs 19))) by (unfold M2, art_poison_frame; zcell).
  assert (C48 : cellA M2 (sp0 - 48) 8 (U (getr regs 20))) by (unfold M2, art_poison_frame; zcell).
  assert (C56 : cellA M2 (sp0 - 56) 8 (U (getr regs 21))) by (unfold M2, art_poison_frame; zcell).
  assert (RG : forall r : reg, 0 <= U (getr regs r) < 2 ^ 64) by (intros r; apply bv_unsigned_in_range).
  destruct (Z.lt_trichotomy u u') as [Lt|[Eq|Gt]].
  - (* [comment removed for export] *)
    destruct (art_ann_grow r1 M2 rom sp0 b c u u' P2 P9 P18 P19 P20 Hb8 Hc8 Hu8 Hu8' ltac:(lia) Hbc ltac:(lia) Lt ltac:(lia))
      as (r1' & RUNG & G1 & G2 & G10 & G11 & G12 & G8 & G9 & G18 & GK).
    assert (ELo : art_ann_lo b u u' = (b + u)) by (unfold art_ann_lo; rewrite Z.min_l by lia; reflexivity).
    assert (En : art_ann_n u u' = (u' - u)) by (unfold art_ann_n; rewrite Z.abs_neq by lia; lia).
    assert (Ev : art_ann_v u u' = 0) by (unfold art_ann_v; rewrite (proj2 (Z.ltb_lt u u') Lt); reflexivity).
    rewrite ELo, En, Ev in *.
    assert (Hp8 : (b + u) mod 8 = 0) by (apply (art_ann_mod8 _ _ Hb8 Hu8)).
    assert (Hn8 : (u' - u) mod 8 = 0) by (apply (art_ann_mod8 _ _ Hu8' Hu8)).
    assert (L2 : art_layout M2) by (unfold M2, art_poison_frame; repeat (apply art_layout_Wn; [lia|lia|unfold apart in *; cbn; lia|unfold apart in *; cbn; lia|]); exact L).
    assert (W2 : wrA M2 (sp0 - 2128 - 64) 64) by (unfold M2, art_poison_frame; repeat apply wr_Wn; eapply wr_sub; [exact W|lia|lia]).
    assert (Wsh2 : wrA M2 (SB + (b + u) / 8) ((u' - u) / 8)) by (unfold M2, art_poison_frame; repeat apply wr_Wn; exact Wsh).
    assert (PLC : art_poison_lo_okG (b + u) (u' - u) \/ art_poison_hi_okG (b + u) (u' - u)).
    { destruct Hplace as [Lo|Hi]; [left; unfold art_poison_lo_okG, SB|right; unfold art_poison_hi_okG, kHighMemBeg, kHighMemEnd]; lia. }
    destruct (art_poison_runG r1' M2 rom (Z_to_bv 64 0x7bcc4) (sp0 - 2128) (b + u) (u' - u) 0 G1 art_ann_ret_7b8ac G2 G10 G11 G12 ltac:(lia) ltac:(lia) W2
               ltac:(unfold apart; lia) ltac:(unfold apart; lia) L2 PLC Hp8 Hn8 ltac:(lia) ltac:(lia)
               ltac:(intros _; apply Z.div_lt_upper_bound; lia) Wsh2)
      as (r2 & RUNP & Q10 & Q1 & Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & QK).
    set (M3 := Wf (art_poison_frame M2 (sp0 - 2128) (U (Z_to_bv 64 0x7bcc4)) (U (getr r1' 8)) (U (getr r1' 9)) (U (getr r1' 18)) (U (getr r1' 19)) (U (getr r1' 20)) (U (getr r1' 21)))
                  (SB + (b + u) / 8) (Z.to_nat ((u' - u) / 8)) 0) in *.
    assert (ET : getr r2 18 = getr r2 9) by (rewrite Q18, Q9, G18, G9; reflexivity).
    assert (NB : 0 <= SB + (b + u) / 8 /\ SB + (b + u) / 8 + Z.of_nat (Z.to_nat ((u' - u) / 8)) < 2 ^ 64).
    { unfold SB. pose proof (Z.div_pos (b + u) 8 ltac:(lia) ltac:(lia)). assert ((b + u) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
      assert ((u' - u) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). rewrite Z2Nat.id by (apply Z.div_pos; lia). lia. }
    assert (APS : forall a k, sp0 - 2192 <= a -> a + k <= sp0 -> 0 <= k -> apart (SB + (b + u) / 8) (Z.of_nat (Z.to_nat ((u' - u) / 8))) a k).
    { intros a k Ha Hk Hk0. unfold apart, SB. rewrite Z2Nat.id by (apply Z.div_pos; lia).
      pose proof (Z.div_mod (b + u) 8 ltac:(lia)) as DP. pose proof (Z.div_mod (u' - u) 8 ltac:(lia)) as DN. rewrite Hp8, Z.add_0_r in DP. rewrite Hn8, Z.add_0_r in DN. lia. }
    assert (D8 : cellA M3 (sp0 - 8) 8 (U raw)).
    { unfold M3. apply cell_Wf_other; [lia|lia|lia|cbn; lia|apply APS; cbn; lia|]. unfold art_poison_frame. zcell. }
    assert (D16 : cellA M3 (sp0 - 16) 8 (U (getr regs 8))).
    { unfold M3. apply cell_Wf_other; [lia|lia|lia|cbn; lia|apply APS; cbn; lia|]. unfold art_poison_frame. zcell. }
    assert (D24 : cellA M3 (sp0 - 24) 8 (U (getr regs 9))).
    { unfold M3. apply cell_Wf_other; [lia|lia|lia|cbn; lia|apply APS; cbn; lia|]. unfold art_poison_frame. zcell. }
    assert (D32 : cellA M3 (sp0 - 32) 8 (U (getr regs 18))).
    { unfold M3. apply cell_Wf_other; [lia|lia|lia|cbn; lia|apply APS; cbn; lia|]. unfold art_poison_frame. zcell. }
    assert (D40 : cellA M3 (sp0 - 40) 8 (U (getr regs 19))).
    { unfold M3. apply cell_Wf_other; [lia|lia|lia|cbn; lia|apply APS; cbn; lia|]. unfold art_poison_frame. zcell. }
    assert (D48 : cellA M3 (sp0 - 48) 8 (U (getr regs 20))).
    { unfold M3. apply cell_Wf_other; [lia|lia|lia|cbn; lia|apply APS; cbn; lia|]. unfold art_poison_frame. zcell. }
    assert (D56 : cellA M3 (sp0 - 56) 8 (U (getr regs 21))).
    { unfold M3. apply cell_Wf_other; [lia|lia|lia|cbn; lia|apply APS; cbn; lia|]. unfold art_poison_frame. zcell. }
    destruct (art_ann_epi r2 M3 rom raw sp0 _ _ _ _ _ _ Q2 ltac:(lia) Hsp' Hret (RG 8%bv) (RG 9%bv) (RG 18%bv) (RG 19%bv) (RG 20%bv) (RG 21%bv) D8 D16 D24 D32 D40 D48 D56)
      as (r3 & RUN3 & E1 & E2 & E8 & E9 & E18 & E19 & E20 & E21 & EK).
    exists r3, M3. split.
    { eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUNG|]. eapply msteps_trans; [exact RUNP|].
      replace (Z_to_bv 64 0x7bcc4) with (0x7bcc4%bv : word) by (apply bv_eq; vm_compute; reflexivity).
      eapply msteps_trans; [exact (art_ann_tail0 r2 M3 rom ET)|exact RUN3]. }
    rewrite !Z_to_bv_bv_unsigned in E8, E9, E18, E19, E20, E21.
    split; [exact E1|]. split; [exact E2|]. split; [exact E8|]. split; [exact E9|]. split; [exact E18|]. split; [exact E19|]. split; [exact E20|]. split; [exact E21|].
    split; [intros r Hr; rewrite (EK r Hr), (QK r (art_ann_kept_poison r Hr)), (GK r Hr); exact (PK r Hr)|].
    split. { eapply mem_grows_trans; [exact GR2|]. unfold M3. eapply mem_grows_trans; [|apply Wf_grows]. apply art_pf_grows. }
    split. { intros x Hx Hy. unfold M3. rewrite Wf_outside by (try rewrite Z2Nat.id by (apply Z.div_pos; lia); lia).
             unfold art_poison_frame. rewrite !Wn_outside by (cbn; lia). apply FR2. lia. }
    intros i Hi. unfold M3. apply Wf_inside; [lia|lia|rewrite Z2Nat.id by (apply Z.div_pos; lia); lia].
  - (* [comment removed for export] *)
    subst u'.
    assert (E19 : getr r1 19 = getr r1 18) by (rewrite P18, P19; reflexivity).
    destruct (art_ann_epi r1 M2 rom raw sp0 _ _ _ _ _ _ P2 ltac:(lia) Hsp' Hret (RG 8%bv) (RG 9%bv) (RG 18%bv) (RG 19%bv) (RG 20%bv) (RG 21%bv) C8 C16 C24 C32 C40 C48 C56)
      as (r3 & RUN3 & Q1 & Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & QK).
    exists r3, M2. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact (art_ann_eq0 r1 M2 rom E19)|exact RUN3]|].
    rewrite !Z_to_bv_bv_unsigned in Q8, Q9, Q18, Q19, Q20, Q21.
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q8|]. split; [exact Q9|]. split; [exact Q18|]. split; [exact Q19|]. split; [exact Q20|]. split; [exact Q21|].
    split; [intros r Hr; rewrite (QK r Hr); exact (PK r Hr)|]. split; [exact GR2|].
    split; [intros x Hx _; apply FR2; lia|]. intros i Hi. unfold art_ann_n in Hi. rewrite Z.sub_diag in Hi. cbn in Hi. lia.
  - (* [comment removed for export] *)
    destruct (art_ann_shrink r1 M2 rom sp0 b c u u' P2 P9 P18 P19 P20 Hb8 Hc8 Hu8 Hu8' ltac:(lia) Hbc ltac:(lia) Gt ltac:(lia))
      as (r1' & RUNG & G1 & G2 & G10 & G11 & G12 & G8 & G9 & G18 & GK).
    assert (ELo : art_ann_lo b u u' = (b + u')) by (unfold art_ann_lo; rewrite Z.min_r by lia; reflexivity).
    assert (En : art_ann_n u u' = (u - u')) by (unfold art_ann_n; rewrite Z.abs_eq by lia; lia).
    assert (Ev : art_ann_v u u' = 252) by (unfold art_ann_v; rewrite (proj2 (Z.ltb_ge u u') ltac:(lia)); reflexivity).
    rewrite ELo, En, Ev in *.
    assert (Hp8 : (b + u') mod 8 = 0) by (apply (art_ann_mod8 _ _ Hb8 Hu8')).
    assert (Hn8 : (u - u') mod 8 = 0) by (apply (art_ann_mod8 _ _ Hu8 Hu8')).
    assert (L2 : art_layout M2) by (unfold M2, art_poison_frame; repeat (apply art_layout_Wn; [lia|lia|unfold apart in *; cbn; lia|unfold apart in *; cbn; lia|]); exact L).
    assert (W2 : wrA M2 (sp0 - 2128 - 64) 64) by (unfold M2, art_poison_frame; repeat apply wr_Wn; eapply wr_sub; [exact W|lia|lia]).
    assert (Wsh2 : wrA M2 (SB + (b + u') / 8) ((u - u') / 8)) by (unfold M2, art_poison_frame; repeat apply wr_Wn; exact Wsh).
    assert (PLC : art_poison_lo_okG (b + u') (u - u') \/ art_poison_hi_okG (b + u') (u - u')).
    { destruct Hplace as [Lo|Hi]; [left; unfold art_poison_lo_okG, SB|right; unfold art_poison_hi_okG, kHighMemBeg, kHighMemEnd]; lia. }
    destruct (art_poison_runG r1' M2 rom (Z_to_bv 64 0x7bcc4) (sp0 - 2128) (b + u') (u - u') 252 G1 art_ann_ret_7b8ac G2 G10 G11 G12 ltac:(lia) ltac:(lia) W2
               ltac:(unfold apart; lia) ltac:(unfold apart; lia) L2 PLC Hp8 Hn8 ltac:(lia) ltac:(lia)
               ltac:(intros _; apply Z.div_lt_upper_bound; lia) Wsh2)
      as (r2 & RUNP & Q10 & Q1 & Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & QK).
    set (M3 := Wf (art_poison_frame M2 (sp0 - 2128) (U (Z_to_bv 64 0x7bcc4)) (U (getr r1' 8)) (U (getr r1' 9)) (U (getr r1' 18)) (U (getr r1' 19)) (U (getr r1' 20)) (U (getr r1' 21)))
                  (SB + (b + u') / 8) (Z.to_nat ((u - u') / 8)) 252) in *.
    assert (ET : getr r2 18 = getr r2 9) by (rewrite Q18, Q9, G18, G9; reflexivity).
    assert (NB : 0 <= SB + (b + u') / 8 /\ SB + (b + u') / 8 + Z.of_nat (Z.to_nat ((u - u') / 8)) < 2 ^ 64).
    { unfold SB. pose proof (Z.div_pos (b + u') 8 ltac:(lia) ltac:(lia)). assert ((b + u') / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
      assert ((u - u') / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). rewrite Z2Nat.id by (apply Z.div_pos; lia). lia. }
    assert (APS : forall a k, sp0 - 2192 <= a -> a + k <= sp0 -> 0 <= k -> apart (SB + (b + u') / 8) (Z.of_nat (Z.to_nat ((u - u') / 8))) a k).
    { intros a k Ha Hk Hk0. unfold apart, SB. rewrite Z2Nat.id by (apply Z.div_pos; lia).
      pose proof (Z.div_mod (b + u') 8 ltac:(lia)) as DP. pose proof (Z.div_mod (u - u') 8 ltac:(lia)) as DN. rewrite Hp8, Z.add_0_r in DP. rewrite Hn8, Z.add_0_r in DN. lia. }
    assert (D8 : cellA M3 (sp0 - 8) 8 (U raw)).
    { unfold M3. apply cell_Wf_other; [lia|lia|lia|cbn; lia|apply APS; cbn; lia|]. unfold art_poison_frame. zcell. }
    assert (D16 : cellA M3 (sp0 - 16) 8 (U (getr regs 8))).
    { unfold M3. apply cell_Wf_other; [lia|lia|lia|cbn; lia|apply APS; cbn; lia|]. unfold art_poison_frame. zcell. }
    assert (D24 : cellA M3 (sp0 - 24) 8 (U (getr regs 9))).
    { unfold M3. apply cell_Wf_other; [lia|lia|lia|cbn; lia|apply APS; cbn; lia|]. unfold art_poison_frame. zcell. }
    assert (D32 : cellA M3 (sp0 - 32) 8 (U (getr regs 18))).
    { unfold M3. apply cell_Wf_other; [lia|lia|lia|cbn; lia|apply APS; cbn; lia|]. unfold art_poison_frame. zcell. }
    assert (D40 : cellA M3 (sp0 - 40) 8 (U (getr regs 19))).
    { unfold M3. apply cell_Wf_other; [lia|lia|lia|cbn; lia|apply APS; cbn; lia|]. unfold art_poison_frame. zcell. }
    assert (D48 : cellA M3 (sp0 - 48) 8 (U (getr regs 20))).
    { unfold M3. apply cell_Wf_other; [lia|lia|lia|cbn; lia|apply APS; cbn; lia|]. unfold art_poison_frame. zcell. }
    assert (D56 : cellA M3 (sp0 - 56) 8 (U (getr regs 21))).
    { unfold M3. apply cell_Wf_other; [lia|lia|lia|cbn; lia|apply APS; cbn; lia|]. unfold art_poison_frame. zcell. }
    destruct (art_ann_epi r2 M3 rom raw sp0 _ _ _ _ _ _ Q2 ltac:(lia) Hsp' Hret (RG 8%bv) (RG 9%bv) (RG 18%bv) (RG 19%bv) (RG 20%bv) (RG 21%bv) D8 D16 D24 D32 D40 D48 D56)
      as (r3 & RUN3 & E1 & E2 & E8 & E9 & E18 & E19 & E20 & E21 & EK).
    exists r3, M3. split.
    { eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUNG|]. eapply msteps_trans; [exact RUNP|].
      replace (Z_to_bv 64 0x7bcc4) with (0x7bcc4%bv : word) by (apply bv_eq; vm_compute; reflexivity).
      eapply msteps_trans; [exact (art_ann_tail0 r2 M3 rom ET)|exact RUN3]. }
    rewrite !Z_to_bv_bv_unsigned in E8, E9, E18, E19, E20, E21.
    split; [exact E1|]. split; [exact E2|]. split; [exact E8|]. split; [exact E9|]. split; [exact E18|]. split; [exact E19|]. split; [exact E20|]. split; [exact E21|].
    split; [intros r Hr; rewrite (EK r Hr), (QK r (art_ann_kept_poison r Hr)), (GK r Hr); exact (PK r Hr)|].
    split. { eapply mem_grows_trans; [exact GR2|]. unfold M3. eapply mem_grows_trans; [|apply Wf_grows]. apply art_pf_grows. }
    split. { intros x Hx Hy. unfold M3. rewrite Wf_outside by (try rewrite Z2Nat.id by (apply Z.div_pos; lia); lia).
             unfold art_poison_frame. rewrite !Wn_outside by (cbn; lia). apply FR2. lia. }
    intros i Hi. unfold M3. apply Wf_inside; [lia|lia|rewrite Z2Nat.id by (apply Z.div_pos; lia); lia].
Qed.
End FPX.
