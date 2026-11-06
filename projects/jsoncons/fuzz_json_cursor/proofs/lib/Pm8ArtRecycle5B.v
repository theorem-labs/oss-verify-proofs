(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac Pm8ArtLeaf Pm8ArtAllocG Pm8ArtPoison ArtRuns ArtRunsMem Pm8ArtFp Pm8ArtFree1 Pm8ArtCellEx Pm8ArtRecycle4.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm8_code_5b000_5c000 .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_f112 (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) (cbc cbs : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18)))
    (sp - 40) (U (getr regs 19))) (sp - 48) (U (getr regs 20))) (sp - 56) (U (getr regs 21))) (sp - 64) (U (getr regs 22))) (sp - 72) (U (getr regs 23))) (sp - 80) (U (getr regs 24)))
    (sp - 88) (U (getr regs 25))) (sp - 104) cbc) (sp - 96) cbs.

Section FPX. Context {fx : PropExec.FPState}.

Lemma art_dr_pro : forall regs (M rom : word -> option byte) (raw : word) (sp tmp cbc cbs k : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 11 = Z_to_bv 64 tmp -> getr regs 12 = Z_to_bv 64 cbc -> getr regs 13 = Z_to_bv 64 cbs ->
  0x6b3000 + 112 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 112) 112 -> sp <= tmp -> tmp + 32 < 2 ^ 64 -> 0 <= cbc < 2 ^ 64 -> 0 <= cbs < 2 ^ 64 -> 1 <= k < 2 ^ 64 ->
  cellA M tmp 8 k ->
  exists regs', msteps ASEGS (mkst regs (0x5b634 : word) M rom) (mkst regs' (0x5b6ac : word) (art_f112 M sp raw regs cbc cbs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (sp - 112) /\ getr regs' 8 = Z_to_bv 64 tmp /\ getr regs' 9 = Z_to_bv 64 1413976 /\ getr regs' 18 = Z_to_bv 64 0x159398
    /\ getr regs' 19 = Z_to_bv 64 0x159608 /\ getr regs' 21 = Z_to_bv 64 (2 ^ 37) /\ getr regs' 10 = Z_to_bv 64 k
    /\ (forall r : reg, In r [3; 4; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp tmp cbc cbs k H1 H2 H11 H12 H13 Hsp Hsp' W Htmp Htmp' Hcbc Hcbs Hk Ck.
  eexists. split.
  { zstep F_5b5e4 D_5b5e4.
    zsd F_5b5e8 D_5b5e8 (sp - 8) (U raw) ltac:(rewok W). zsd F_5b5ec D_5b5ec (sp - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_5b5f0 D_5b5f0 (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_5b5f4 D_5b5f4 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_5b5f8 D_5b5f8 (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_5b5fc D_5b5fc (sp - 48) (U (getr regs 20)) ltac:(rewok W).
    zsd F_5b600 D_5b600 (sp - 56) (U (getr regs 21)) ltac:(rewok W). zsd F_5b604 D_5b604 (sp - 64) (U (getr regs 22)) ltac:(rewok W).
    zsd F_5b608 D_5b608 (sp - 72) (U (getr regs 23)) ltac:(rewok W). zsd F_5b60c D_5b60c (sp - 80) (U (getr regs 24)) ltac:(rewok W).
    zsd F_5b610 D_5b610 (sp - 88) (U (getr regs 25)) ltac:(rewok W).
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Ck' : cellA X tmp 8 k) by zcell end.
    zld F_5b614 D_5b614 tmp Ck'.
    zsd F_5b618 D_5b618 (sp - 104) cbc ltac:(rewok W). zsd F_5b61c D_5b61c (sp - 96) cbs ltac:(rewok W).
    zbft F_5b620 D_5b620.
    zstep F_5b624 D_5b624.
    stepn F_5b628 D_5b628. zstep F_5b62c D_5b62c. stepn F_5b630 D_5b630. zcl4.
    zstep F_5b634 D_5b634. zstep F_5b638 D_5b638. zstep F_5b63c D_5b63c.
    stepn F_5b640 D_5b640.
    unfold art_f112. apply mst_refl. }
  split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; f_equal; lia|].
  split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

Lemma art_dr_pop : forall regs (M rom : word -> option byte) (tmp k b next size bytes ni : Z),
  getr regs 8 = Z_to_bv 64 tmp -> getr regs 10 = Z_to_bv 64 k ->
  0x6b3000 <= tmp -> tmp + 32 < 2 ^ 64 -> 0x6b3000 <= b -> b + 8192 < 2 ^ 64 -> apart tmp 32 b 8192 -> 1 <= k < 2 ^ 64 -> 0 <= next < 2 ^ 64 -> 0 <= size < 2 ^ 64 -> 0 <= bytes < 2 ^ 64 ->
  1 <= ni < 2 ^ 32 -> wrA M tmp 32 ->
  cellA M (tmp + 8) 8 b -> cellA M b 8 next -> cellA M (b + 8) 8 size -> cellA M (tmp + 24) 8 bytes -> cellA M (b + 16) 8 ni ->
  exists regs' (M' : word -> option byte), msteps ASEGS (mkst regs (0x5b6ac : word) M rom) (mkst regs' (0x5b6ec : word) M' rom)
    /\ getr regs' 20 = Z_to_bv 64 b /\ getr regs' 22 = Z_to_bv 64 ni /\ getr regs' 23 = Z_to_bv 64 (b + 152) /\ getr regs' 24 = Z_to_bv 64 (ni + 16) /\ getr regs' 25 = Z_to_bv 64 16
    /\ (forall r : reg, In r [1; 2; 3; 4; 8; 9; 18; 19; 21; 26; 27]%bv -> getr regs' r = getr regs r)
    /\ mem_grows M M' /\ art_agree [(tmp, 32)] M M'
    /\ cellA M' tmp 8 (k - 1) /\ cellA M' (tmp + 8) 8 next /\ cellA M' (tmp + 24) 8 (bytes - size).
Proof.
  intros regs M rom tmp k b next size bytes ni H8 H10 Htmp Htmp' Hb Hb' Ap Hk Hnext Hsize Hbytes Hni W Cb Cnext Csize Cbytes Cni.
  unfold apart in Ap.
  destruct (Z.eq_dec next 0) as [E0|NE0].
  - eexists. eexists. split.
    { zld F_5b65c D_5b65c (tmp + 8) Cb.
      zld F_5b660 D_5b660 b Cnext.
      zsd F_5b664 D_5b664 (tmp + 8) next ltac:(rewok W).
      zbft F_5b668 D_5b668.
      zsd F_5b66c D_5b66c (tmp + 16) 0 ltac:(rewok W).
      zstep F_5b670 D_5b670.
      zsd F_5b674 D_5b674 tmp (k + -1) ltac:(rewok W).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize' : cellA X (b + 8) 8 size) by zcell; assert (Cbytes' : cellA X (tmp + 24) 8 bytes) by zcell;
        assert (Cni' : cellA X (b + 16) 8 ni) by zcell end.
      zld F_5b678 D_5b678 (b + 8) Csize'.
      zld F_5b67c D_5b67c (tmp + 24) Cbytes'.
      zstep F_5b680 D_5b680.
      zsd F_5b684 D_5b684 (tmp + 24) (bytes - size) ltac:(rewok W).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cni'' : cellA X (b + 16) 8 ni) by zcell end.
      zld F_5b688 D_5b688 (b + 16) Cni''.
      zbft F_5b68c D_5b68c.
      zstep F_5b690 D_5b690. zstep F_5b694 D_5b694. zstep F_5b698 D_5b698.
      apply mst_refl. }
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
    split. { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
    split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|].
    split; [replace (k - 1) with (k + -1) by lia; zcell|]. split; [zcell|zcell].
  - eexists. eexists. split.
    { zld F_5b65c D_5b65c (tmp + 8) Cb.
      zld F_5b660 D_5b660 b Cnext.
      zsd F_5b664 D_5b664 (tmp + 8) next ltac:(rewok W).
      zbtk F_5b668 D_5b668.
      zstep F_5b670 D_5b670.
      zsd F_5b674 D_5b674 tmp (k + -1) ltac:(rewok W).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize' : cellA X (b + 8) 8 size) by zcell; assert (Cbytes' : cellA X (tmp + 24) 8 bytes) by zcell;
        assert (Cni' : cellA X (b + 16) 8 ni) by zcell end.
      zld F_5b678 D_5b678 (b + 8) Csize'.
      zld F_5b67c D_5b67c (tmp + 24) Cbytes'.
      zstep F_5b680 D_5b680.
      zsd F_5b684 D_5b684 (tmp + 24) (bytes - size) ltac:(rewok W).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cni'' : cellA X (b + 16) 8 ni) by zcell end.
      zld F_5b688 D_5b688 (b + 16) Cni''.
      zbft F_5b68c D_5b68c.
      zstep F_5b690 D_5b690. zstep F_5b694 D_5b694. zstep F_5b698 D_5b698.
      apply mst_refl. }
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
    split. { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
    split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|].
    split; [replace (k - 1) with (k + -1) by lia; zcell|]. split; [zcell|zcell].
Qed.

Lemma art_dr_item_call : forall regs (M rom : word -> option byte) (sp1 b j m : Z),
  getr regs 2 = Z_to_bv 64 sp1 -> getr regs 23 = Z_to_bv 64 (b + 152 + 8 * j) ->
  0 <= sp1 -> sp1 + 8 < 2 ^ 64 -> 0x6b3000 <= b -> b + 8192 < 2 ^ 64 -> 0 <= j < 1021 -> 0 <= m < 2 ^ 64 ->
  cellA M (b + 24 + 8 * j) 8 m ->
  exists regs', msteps ASEGS (mkst regs (0x5b6ec : word) M rom) (mkst regs' (0x5b76c : word) M rom)
    /\ getr regs' 1 = (0x5b6f8 : bv 64)%bv /\ getr regs' 10 = Z_to_bv 64 (sp1 + 8) /\ getr regs' 11 = Z_to_bv 64 m
    /\ (forall r : reg, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp1 b j m H2 H23 Hsp Hsp' Hb Hb' Hj Hm Cm.
  eexists. split.
  { zld F_5b69c D_5b69c (b + 24 + 8 * j) Cm.
    zstep F_5b6a0 D_5b6a0.
    stepn F_5b6a4 D_5b6a4.
    apply mst_refl. }
  split; [gres; bveq|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

Lemma art_dr_item_more : forall regs (M rom : word -> option byte) (b j ni : Z),
  getr regs 23 = Z_to_bv 64 (b + 152 + 8 * j) -> getr regs 24 = Z_to_bv 64 (ni + 16) -> getr regs 25 = Z_to_bv 64 (16 + j) ->
  0 <= j -> j + 1 < ni -> ni < 2 ^ 32 -> 0 <= b -> b + 8192 < 2 ^ 64 ->
  exists regs', msteps ASEGS (mkst regs (0x5b6f8 : word) M rom) (mkst regs' (0x5b6ec : word) M rom)
    /\ getr regs' 23 = Z_to_bv 64 (b + 152 + 8 * (j + 1)) /\ getr regs' 25 = Z_to_bv 64 (16 + (j + 1))
    /\ (forall r : reg, In r [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom b j ni H23 H24 H25 Hj Hjn Hni Hb Hb'.
  eexists. split.
  { zstep F_5b6a8 D_5b6a8. zstep F_5b6ac D_5b6ac.
    zbtk F_5b6b0 D_5b6b0.
    apply mst_refl. }
  split; [gres; f_equal; lia|]. split; [gres; f_equal; lia|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

Lemma art_dr_item_last : forall regs (M rom : word -> option byte) (b j ni : Z),
  getr regs 23 = Z_to_bv 64 (b + 152 + 8 * j) -> getr regs 24 = Z_to_bv 64 (ni + 16) -> getr regs 25 = Z_to_bv 64 (16 + j) ->
  0 <= j -> j + 1 = ni -> ni < 2 ^ 32 -> 0 <= b -> b + 8192 < 2 ^ 64 ->
  exists regs', msteps ASEGS (mkst regs (0x5b6f8 : word) M rom) (mkst regs' (0x5b704 : word) M rom)
    /\ (forall r : reg, In r [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom b j ni H23 H24 H25 Hj Hjn Hni Hb Hb'.
  eexists. split.
  { zstep F_5b6a8 D_5b6a8. zstep F_5b6ac D_5b6ac.
    zbft F_5b6b0 D_5b6b0.
    apply mst_refl. }
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

Lemma art_dr_bd_call : forall regs (M rom : word -> option byte) (sp1 spb c szi cache : Z),
  let b := spb + c * 2 ^ 32 + szi in
  getr regs 2 = Z_to_bv 64 sp1 -> getr regs 9 = Z_to_bv 64 1413976 -> getr regs 20 = Z_to_bv 64 b -> getr regs 21 = Z_to_bv 64 (2 ^ 37) ->
  0 <= sp1 -> sp1 + 16 < 2 ^ 64 -> 0x6b3000 <= spb -> spb + 2 ^ 37 < 2 ^ 47 -> 1 <= c <= 30 -> 0 <= szi < 2 ^ 32 -> 0 <= cache < 2 ^ 64 ->
  cellA M (1413976 + 32) 8 spb -> cellA M (sp1 + 8) 8 cache ->
  exists regs', msteps ASEGS (mkst regs (0x5b704 : word) M rom) (mkst regs' (0x5bb70 : word) M rom)
    /\ getr regs' 1 = (0x5b730 : bv 64)%bv /\ getr regs' 10 = Z_to_bv 64 cache /\ getr regs' 11 = Z_to_bv 64 1413976 /\ getr regs' 12 = Z_to_bv 64 c /\ getr regs' 13 = Z_to_bv 64 b
    /\ (forall r : reg, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp1 spb c szi cache b H2 H9 H20 H21 Hsp Hsp' Hspb Hspb' Hc Hszi Hcache Cspb Ccache.
  assert (Hb : b = spb + c * 2 ^ 32 + szi) by reflexivity. clearbody b.
  assert (Ec : (b - spb) * 2 ^ 27 / 2 ^ 59 = c).
  { symmetry. apply (Z.div_unique_pos ((b - spb) * 2 ^ 27) (2 ^ 59) c (szi * 2 ^ 27)); lia. }
  eexists. split.
  { zld F_5b6b4 D_5b6b4 (1413976 + 32) Cspb.
    zbft F_5b6b8 D_5b6b8.
    zstep F_5b6bc D_5b6bc.
    zbft F_5b6c0 D_5b6c0.
    zld F_5b6c4 D_5b6c4 (sp1 + 8) Ccache.
    zstep F_5b6c8 D_5b6c8. zstep F_5b6cc D_5b6cc.
    stepn F_5b6d0 D_5b6d0. rwH. rewrite (art_zb_srli ((b - spb) * 2 ^ 27) 59) by lia. rewrite Ec.
    zstep F_5b6d4 D_5b6d4. zstep F_5b6d8 D_5b6d8.
    stepn F_5b6dc D_5b6dc.
    apply mst_refl. }
  split; [gres; bveq|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

Lemma art_dr_next_more : forall regs (M rom : word -> option byte) (tmp k : Z),
  getr regs 8 = Z_to_bv 64 tmp -> 0 <= tmp -> tmp + 8 < 2 ^ 64 -> 1 <= k < 2 ^ 64 -> cellA M tmp 8 k ->
  exists regs', msteps ASEGS (mkst regs (0x5b730 : word) M rom) (mkst regs' (0x5b6ac : word) M rom)
    /\ getr regs' 10 = Z_to_bv 64 k
    /\ (forall r : reg, In r [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom tmp k H8 Htmp Htmp' Hk Ck.
  eexists. split.
  { zld F_5b6e0 D_5b6e0 tmp Ck.
    zbtk F_5b6e4 D_5b6e4.
    apply mst_refl. }
  split; [gres; reflexivity|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

Lemma art_dr_next_done : forall regs (M rom : word -> option byte) (raw : word) (sp tmp g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 112) -> getr regs 8 = Z_to_bv 64 tmp -> ret_ok raw -> 112 <= sp -> sp < 2 ^ 64 -> 0 <= tmp -> tmp + 8 < 2 ^ 64 ->
  cellA M tmp 8 0 ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 g8 -> cellA M (sp - 24) 8 g9 -> cellA M (sp - 32) 8 g18 -> cellA M (sp - 40) 8 g19 -> cellA M (sp - 48) 8 g20 ->
  cellA M (sp - 56) 8 g21 -> cellA M (sp - 64) 8 g22 -> cellA M (sp - 72) 8 g23 -> cellA M (sp - 80) 8 g24 -> cellA M (sp - 88) 8 g25 ->
  exists regs', msteps ASEGS (mkst regs (0x5b730 : word) M rom) (mkst regs' raw M rom)
    /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 8 = Z_to_bv 64 g8 /\ getr regs' 9 = Z_to_bv 64 g9 /\ getr regs' 18 = Z_to_bv 64 g18 /\ getr regs' 19 = Z_to_bv 64 g19
    /\ getr regs' 20 = Z_to_bv 64 g20 /\ getr regs' 21 = Z_to_bv 64 g21 /\ getr regs' 22 = Z_to_bv 64 g22 /\ getr regs' 23 = Z_to_bv 64 g23 /\ getr regs' 24 = Z_to_bv 64 g24
    /\ getr regs' 25 = Z_to_bv 64 g25
    /\ (forall r : reg, In r [3; 4; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp tmp g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 H2 H8 Hret Hsp Hsp' Htmp Htmp' Ck F1 F8 F9 F18 F19 F20 F21 F22 F23 F24 F25.
  eexists. split.
  { zld F_5b6e0 D_5b6e0 tmp Ck.
    zbft F_5b6e4 D_5b6e4.
    zld F_5b6e8 D_5b6e8 (sp - 8) F1. rewrite Z_to_bv_bv_unsigned.
    zld F_5b6ec D_5b6ec (sp - 16) F8. zld F_5b6f0 D_5b6f0 (sp - 24) F9. zld F_5b6f4 D_5b6f4 (sp - 32) F18. zld F_5b6f8 D_5b6f8 (sp - 40) F19. zld F_5b6fc D_5b6fc (sp - 48) F20.
    zld F_5b700 D_5b700 (sp - 56) F21. zld F_5b704 D_5b704 (sp - 64) F22. zld F_5b708 D_5b708 (sp - 72) F23. zld F_5b70c D_5b70c (sp - 80) F24. zld F_5b710 D_5b710 (sp - 88) F25.
    zstep F_5b714 D_5b714.
    stepret F_5b718 D_5b718 raw ltac:(reflexivity).
    apply mst_refl. }
  split; [gres; f_equal; lia|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
  split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.
End FPX.
