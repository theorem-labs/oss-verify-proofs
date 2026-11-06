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

Definition art_f112 (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) (cbc cbs : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18)))
    (sp - 40) (U (getr regs 19))) (sp - 48) (U (getr regs 20))) (sp - 56) (U (getr regs 21))) (sp - 64) (U (getr regs 22))) (sp - 72) (U (getr regs 23))) (sp - 80) (U (getr regs 24)))
    (sp - 88) (U (getr regs 25))) (sp - 104) cbc) (sp - 96) cbs.

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_dr_pro : forall regs (M rom : word -> option byte) (raw : word) (sp tmp cbc cbs k : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 11 = Z_to_bv 64 tmp -> getr regs 12 = Z_to_bv 64 cbc -> getr regs 13 = Z_to_bv 64 cbs ->
  0x698000 + 112 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 112) 112 -> sp <= tmp -> tmp + 32 < 2 ^ 64 -> 0 <= cbc < 2 ^ 64 -> 0 <= cbs < 2 ^ 64 -> 1 <= k < 2 ^ 64 ->
  cellA M tmp 8 k ->
  exists regs', msteps ASEGS (mkst regs (0x54fa4 : word) M rom) (mkst regs' (0x5501c : word) (art_f112 M sp raw regs cbc cbs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (sp - 112) /\ getr regs' 8 = Z_to_bv 64 tmp /\ getr regs' 9 = Z_to_bv 64 1303448 /\ getr regs' 18 = Z_to_bv 64 0x13e3d8
    /\ getr regs' 19 = Z_to_bv 64 0x13e648 /\ getr regs' 21 = Z_to_bv 64 (2 ^ 37) /\ getr regs' 10 = Z_to_bv 64 k
    /\ (forall r : reg, In r [3; 4; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp tmp cbc cbs k H1 H2 H11 H12 H13 Hsp Hsp' W Htmp Htmp' Hcbc Hcbs Hk Ck.
  eexists. split.
  { zstep F_54f54 D_54f54.
    zsd F_54f58 D_54f58 (sp - 8) (U raw) ltac:(rewok W). zsd F_54f5c D_54f5c (sp - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_54f60 D_54f60 (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_54f64 D_54f64 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_54f68 D_54f68 (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_54f6c D_54f6c (sp - 48) (U (getr regs 20)) ltac:(rewok W).
    zsd F_54f70 D_54f70 (sp - 56) (U (getr regs 21)) ltac:(rewok W). zsd F_54f74 D_54f74 (sp - 64) (U (getr regs 22)) ltac:(rewok W).
    zsd F_54f78 D_54f78 (sp - 72) (U (getr regs 23)) ltac:(rewok W). zsd F_54f7c D_54f7c (sp - 80) (U (getr regs 24)) ltac:(rewok W).
    zsd F_54f80 D_54f80 (sp - 88) (U (getr regs 25)) ltac:(rewok W).
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Ck' : cellA X tmp 8 k) by zcell end.
    zld F_54f84 D_54f84 tmp Ck'.
    zsd F_54f88 D_54f88 (sp - 104) cbc ltac:(rewok W). zsd F_54f8c D_54f8c (sp - 96) cbs ltac:(rewok W).
    zbft F_54f90 D_54f90.
    zstep F_54f94 D_54f94.
    stepn F_54f98 D_54f98. zstep F_54f9c D_54f9c. stepn F_54fa0 D_54fa0. zcl4.
    zstep F_54fa4 D_54fa4. zstep F_54fa8 D_54fa8. zstep F_54fac D_54fac.
    stepn F_54fb0 D_54fb0.
    unfold art_f112. apply mst_refl. }
  split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; f_equal; lia|].
  split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

#[using="Type"] Lemma art_dr_pop : forall regs (M rom : word -> option byte) (tmp k b next size bytes ni : Z),
  getr regs 8 = Z_to_bv 64 tmp -> getr regs 10 = Z_to_bv 64 k ->
  0x698000 <= tmp -> tmp + 32 < 2 ^ 64 -> 0x698000 <= b -> b + 8192 < 2 ^ 64 -> apart tmp 32 b 8192 -> 1 <= k < 2 ^ 64 -> 0 <= next < 2 ^ 64 -> 0 <= size < 2 ^ 64 -> 0 <= bytes < 2 ^ 64 ->
  1 <= ni < 2 ^ 32 -> wrA M tmp 32 ->
  cellA M (tmp + 8) 8 b -> cellA M b 8 next -> cellA M (b + 8) 8 size -> cellA M (tmp + 24) 8 bytes -> cellA M (b + 16) 8 ni ->
  exists regs' (M' : word -> option byte), msteps ASEGS (mkst regs (0x5501c : word) M rom) (mkst regs' (0x5505c : word) M' rom)
    /\ getr regs' 20 = Z_to_bv 64 b /\ getr regs' 22 = Z_to_bv 64 ni /\ getr regs' 23 = Z_to_bv 64 (b + 152) /\ getr regs' 24 = Z_to_bv 64 (ni + 16) /\ getr regs' 25 = Z_to_bv 64 16
    /\ (forall r : reg, In r [1; 2; 3; 4; 8; 9; 18; 19; 21; 26; 27]%bv -> getr regs' r = getr regs r)
    /\ mem_grows M M' /\ art_agree [(tmp, 32)] M M'
    /\ cellA M' tmp 8 (k - 1) /\ cellA M' (tmp + 8) 8 next /\ cellA M' (tmp + 24) 8 (bytes - size).
Proof.
  intros regs M rom tmp k b next size bytes ni H8 H10 Htmp Htmp' Hb Hb' Ap Hk Hnext Hsize Hbytes Hni W Cb Cnext Csize Cbytes Cni.
  unfold apart in Ap.
  destruct (Z.eq_dec next 0) as [E0|NE0].
  - eexists. eexists. split.
    { zld F_54fcc D_54fcc (tmp + 8) Cb.
      zld F_54fd0 D_54fd0 b Cnext.
      zsd F_54fd4 D_54fd4 (tmp + 8) next ltac:(rewok W).
      zbft F_54fd8 D_54fd8.
      zsd F_54fdc D_54fdc (tmp + 16) 0 ltac:(rewok W).
      zstep F_54fe0 D_54fe0.
      zsd F_54fe4 D_54fe4 tmp (k + -1) ltac:(rewok W).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize' : cellA X (b + 8) 8 size) by zcell; assert (Cbytes' : cellA X (tmp + 24) 8 bytes) by zcell;
        assert (Cni' : cellA X (b + 16) 8 ni) by zcell end.
      zld F_54fe8 D_54fe8 (b + 8) Csize'.
      zld F_54fec D_54fec (tmp + 24) Cbytes'.
      zstep F_54ff0 D_54ff0.
      zsd F_54ff4 D_54ff4 (tmp + 24) (bytes - size) ltac:(rewok W).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cni'' : cellA X (b + 16) 8 ni) by zcell end.
      zld F_54ff8 D_54ff8 (b + 16) Cni''.
      zbft F_54ffc D_54ffc.
      zstep F_55000 D_55000. zstep F_55004 D_55004. zstep F_55008 D_55008.
      apply mst_refl. }
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
    split. { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
    split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|].
    split; [replace (k - 1) with (k + -1) by lia; zcell|]. split; [zcell|zcell].
  - eexists. eexists. split.
    { zld F_54fcc D_54fcc (tmp + 8) Cb.
      zld F_54fd0 D_54fd0 b Cnext.
      zsd F_54fd4 D_54fd4 (tmp + 8) next ltac:(rewok W).
      zbtk F_54fd8 D_54fd8.
      zstep F_54fe0 D_54fe0.
      zsd F_54fe4 D_54fe4 tmp (k + -1) ltac:(rewok W).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csize' : cellA X (b + 8) 8 size) by zcell; assert (Cbytes' : cellA X (tmp + 24) 8 bytes) by zcell;
        assert (Cni' : cellA X (b + 16) 8 ni) by zcell end.
      zld F_54fe8 D_54fe8 (b + 8) Csize'.
      zld F_54fec D_54fec (tmp + 24) Cbytes'.
      zstep F_54ff0 D_54ff0.
      zsd F_54ff4 D_54ff4 (tmp + 24) (bytes - size) ltac:(rewok W).
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cni'' : cellA X (b + 16) 8 ni) by zcell end.
      zld F_54ff8 D_54ff8 (b + 16) Cni''.
      zbft F_54ffc D_54ffc.
      zstep F_55000 D_55000. zstep F_55004 D_55004. zstep F_55008 D_55008.
      apply mst_refl. }
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
    split. { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
    split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; zsub|].
    split; [replace (k - 1) with (k + -1) by lia; zcell|]. split; [zcell|zcell].
Qed.

#[using="Type"] Lemma art_dr_item_call : forall regs (M rom : word -> option byte) (sp1 b j m : Z),
  getr regs 2 = Z_to_bv 64 sp1 -> getr regs 23 = Z_to_bv 64 (b + 152 + 8 * j) ->
  0 <= sp1 -> sp1 + 8 < 2 ^ 64 -> 0x698000 <= b -> b + 8192 < 2 ^ 64 -> 0 <= j < 1021 -> 0 <= m < 2 ^ 64 ->
  cellA M (b + 24 + 8 * j) 8 m ->
  exists regs', msteps ASEGS (mkst regs (0x5505c : word) M rom) (mkst regs' (0x550dc : word) M rom)
    /\ getr regs' 1 = (0x55068 : bv 64)%bv /\ getr regs' 10 = Z_to_bv 64 (sp1 + 8) /\ getr regs' 11 = Z_to_bv 64 m
    /\ (forall r : reg, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp1 b j m H2 H23 Hsp Hsp' Hb Hb' Hj Hm Cm.
  eexists. split.
  { zld F_5500c D_5500c (b + 24 + 8 * j) Cm.
    zstep F_55010 D_55010.
    stepn F_55014 D_55014.
    apply mst_refl. }
  split; [gres; bveq|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

#[using="Type"] Lemma art_dr_item_more : forall regs (M rom : word -> option byte) (b j ni : Z),
  getr regs 23 = Z_to_bv 64 (b + 152 + 8 * j) -> getr regs 24 = Z_to_bv 64 (ni + 16) -> getr regs 25 = Z_to_bv 64 (16 + j) ->
  0 <= j -> j + 1 < ni -> ni < 2 ^ 32 -> 0 <= b -> b + 8192 < 2 ^ 64 ->
  exists regs', msteps ASEGS (mkst regs (0x55068 : word) M rom) (mkst regs' (0x5505c : word) M rom)
    /\ getr regs' 23 = Z_to_bv 64 (b + 152 + 8 * (j + 1)) /\ getr regs' 25 = Z_to_bv 64 (16 + (j + 1))
    /\ (forall r : reg, In r [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom b j ni H23 H24 H25 Hj Hjn Hni Hb Hb'.
  eexists. split.
  { zstep F_55018 D_55018. zstep F_5501c D_5501c.
    zbtk F_55020 D_55020.
    apply mst_refl. }
  split; [gres; f_equal; lia|]. split; [gres; f_equal; lia|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

#[using="Type"] Lemma art_dr_item_last : forall regs (M rom : word -> option byte) (b j ni : Z),
  getr regs 23 = Z_to_bv 64 (b + 152 + 8 * j) -> getr regs 24 = Z_to_bv 64 (ni + 16) -> getr regs 25 = Z_to_bv 64 (16 + j) ->
  0 <= j -> j + 1 = ni -> ni < 2 ^ 32 -> 0 <= b -> b + 8192 < 2 ^ 64 ->
  exists regs', msteps ASEGS (mkst regs (0x55068 : word) M rom) (mkst regs' (0x55074 : word) M rom)
    /\ (forall r : reg, In r [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom b j ni H23 H24 H25 Hj Hjn Hni Hb Hb'.
  eexists. split.
  { zstep F_55018 D_55018. zstep F_5501c D_5501c.
    zbft F_55020 D_55020.
    apply mst_refl. }
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

#[using="Type"] Lemma art_dr_bd_call : forall regs (M rom : word -> option byte) (sp1 spb c szi cache : Z),
  let b := spb + c * 2 ^ 32 + szi in
  getr regs 2 = Z_to_bv 64 sp1 -> getr regs 9 = Z_to_bv 64 1303448 -> getr regs 20 = Z_to_bv 64 b -> getr regs 21 = Z_to_bv 64 (2 ^ 37) ->
  0 <= sp1 -> sp1 + 16 < 2 ^ 64 -> 0x698000 <= spb -> spb + 2 ^ 37 < 2 ^ 47 -> 1 <= c <= 30 -> 0 <= szi < 2 ^ 32 -> 0 <= cache < 2 ^ 64 ->
  cellA M (1303448 + 32) 8 spb -> cellA M (sp1 + 8) 8 cache ->
  exists regs', msteps ASEGS (mkst regs (0x55074 : word) M rom) (mkst regs' (0x554e0 : word) M rom)
    /\ getr regs' 1 = (0x550a0 : bv 64)%bv /\ getr regs' 10 = Z_to_bv 64 cache /\ getr regs' 11 = Z_to_bv 64 1303448 /\ getr regs' 12 = Z_to_bv 64 c /\ getr regs' 13 = Z_to_bv 64 b
    /\ (forall r : reg, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp1 spb c szi cache b H2 H9 H20 H21 Hsp Hsp' Hspb Hspb' Hc Hszi Hcache Cspb Ccache.
  assert (Hb : b = spb + c * 2 ^ 32 + szi) by reflexivity. clearbody b.
  assert (Ec : (b - spb) * 2 ^ 27 / 2 ^ 59 = c).
  { symmetry. apply (Z.div_unique_pos ((b - spb) * 2 ^ 27) (2 ^ 59) c (szi * 2 ^ 27)); lia. }
  eexists. split.
  { zld F_55024 D_55024 (1303448 + 32) Cspb.
    zbft F_55028 D_55028.
    zstep F_5502c D_5502c.
    zbft F_55030 D_55030.
    zld F_55034 D_55034 (sp1 + 8) Ccache.
    zstep F_55038 D_55038. zstep F_5503c D_5503c.
    stepn F_55040 D_55040. rwH. rewrite (art_zb_srli ((b - spb) * 2 ^ 27) 59) by lia. rewrite Ec.
    zstep F_55044 D_55044. zstep F_55048 D_55048.
    stepn F_5504c D_5504c.
    apply mst_refl. }
  split; [gres; bveq|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

#[using="Type"] Lemma art_dr_next_more : forall regs (M rom : word -> option byte) (tmp k : Z),
  getr regs 8 = Z_to_bv 64 tmp -> 0 <= tmp -> tmp + 8 < 2 ^ 64 -> 1 <= k < 2 ^ 64 -> cellA M tmp 8 k ->
  exists regs', msteps ASEGS (mkst regs (0x550a0 : word) M rom) (mkst regs' (0x5501c : word) M rom)
    /\ getr regs' 10 = Z_to_bv 64 k
    /\ (forall r : reg, In r [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom tmp k H8 Htmp Htmp' Hk Ck.
  eexists. split.
  { zld F_55050 D_55050 tmp Ck.
    zbtk F_55054 D_55054.
    apply mst_refl. }
  split; [gres; reflexivity|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

#[using="Type"] Lemma art_dr_next_done : forall regs (M rom : word -> option byte) (raw : word) (sp tmp g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 112) -> getr regs 8 = Z_to_bv 64 tmp -> ret_ok raw -> 112 <= sp -> sp < 2 ^ 64 -> 0 <= tmp -> tmp + 8 < 2 ^ 64 ->
  cellA M tmp 8 0 ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 g8 -> cellA M (sp - 24) 8 g9 -> cellA M (sp - 32) 8 g18 -> cellA M (sp - 40) 8 g19 -> cellA M (sp - 48) 8 g20 ->
  cellA M (sp - 56) 8 g21 -> cellA M (sp - 64) 8 g22 -> cellA M (sp - 72) 8 g23 -> cellA M (sp - 80) 8 g24 -> cellA M (sp - 88) 8 g25 ->
  exists regs', msteps ASEGS (mkst regs (0x550a0 : word) M rom) (mkst regs' raw M rom)
    /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 8 = Z_to_bv 64 g8 /\ getr regs' 9 = Z_to_bv 64 g9 /\ getr regs' 18 = Z_to_bv 64 g18 /\ getr regs' 19 = Z_to_bv 64 g19
    /\ getr regs' 20 = Z_to_bv 64 g20 /\ getr regs' 21 = Z_to_bv 64 g21 /\ getr regs' 22 = Z_to_bv 64 g22 /\ getr regs' 23 = Z_to_bv 64 g23 /\ getr regs' 24 = Z_to_bv 64 g24
    /\ getr regs' 25 = Z_to_bv 64 g25
    /\ (forall r : reg, In r [3; 4; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp tmp g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 H2 H8 Hret Hsp Hsp' Htmp Htmp' Ck F1 F8 F9 F18 F19 F20 F21 F22 F23 F24 F25.
  eexists. split.
  { zld F_55050 D_55050 tmp Ck.
    zbft F_55054 D_55054.
    zld F_55058 D_55058 (sp - 8) F1. rewrite Z_to_bv_bv_unsigned.
    zld F_5505c D_5505c (sp - 16) F8. zld F_55060 D_55060 (sp - 24) F9. zld F_55064 D_55064 (sp - 32) F18. zld F_55068 D_55068 (sp - 40) F19. zld F_5506c D_5506c (sp - 48) F20.
    zld F_55070 D_55070 (sp - 56) F21. zld F_55074 D_55074 (sp - 64) F22. zld F_55078 D_55078 (sp - 72) F23. zld F_5507c D_5507c (sp - 80) F24. zld F_55080 D_55080 (sp - 88) F25.
    zstep F_55084 D_55084.
    stepret F_55088 D_55088 raw ltac:(reflexivity).
    apply mst_refl. }
  split; [gres; f_equal; lia|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
  split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.
End FPX.
