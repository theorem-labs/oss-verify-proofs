(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib RefMemcpyLib
     MemSplit ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac Pm8ArtDepotA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import muslA.Pm8MemcpyBase Pm8IntMemcpy.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm8_code_9e000_9f000 Pm8_code_a0000_a1000   .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Lemma cell8_lo : forall M a v, cellA M a 8 v -> cellA M a 4 v.
Proof.
  intros M a v C. unfold cell in *. pose proof (SeqExec.rdn_firstn _ _ _ _ _ 4 C ltac:(lia)) as F. rewrite F. reflexivity.
Qed.
Lemma zb_add_lit : forall a (k : nat), 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> bv_add (Z_to_bv 64 a) (nat_to_word k) = Z_to_bv 64 (a + Z.of_nat k).
Proof.
  intros a k Ha Hak. unfold nat_to_word. apply bv_eq.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite <- Zplus_mod. rewrite !Z.mod_small by lia. reflexivity.
Qed.
Lemma cell8_hi : forall M a v, 0 <= a -> a + 8 < 2 ^ 64 -> 0 <= v < 2 ^ 64 -> cellA M a 8 v -> cellA M (a + 4) 4 (v / 2 ^ 32).
Proof.
  intros M a v Ha Ha8 Hv C. unfold cell in *. pose proof (SeqExec.rdn_skipn _ _ _ _ _ 4 C ltac:(lia)) as S.
  rewrite (zb_add_lit a 4%nat) in S by lia. change (8 - 4)%nat with 4%nat in S. change (Z.of_nat 4) with 4 in S. rewrite S. f_equal.
  pose proof (Z.div_pos v (2 ^ 32) ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound v (2 ^ 32) (2 ^ 32) ltac:(lia) ltac:(lia)).
  unfold word_to_le_bytes. rewrite !art_u_lit by lia.
  cbn [Z_to_le_bytes skipn]. rewrite !Z.shiftr_shiftr by lia. rewrite !Z.shiftr_div_pow2 by lia.
  rewrite !Z.div_div by lia. rewrite <- !Z.pow_add_r by lia.
  repeat (f_equal; [f_equal; f_equal; lia|]). reflexivity.
Qed.

Lemma rdn_words : forall (k : nat) M a,
  0 <= a -> a + 8 * Z.of_nat k < 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat k -> rcell M (a + 8 * i)) ->
  exists bs, rdn ASEGS M (Z_to_bv 64 a) (8 * k)%nat = Some bs.
Proof.
  induction k as [|k IH]; intros M a Ha Hak RC; [exists []%list; reflexivity|].
  destruct (RC 0 ltac:(lia)) as (bs0 & R0). replace (a + 8 * 0) with a in R0 by lia.
  destruct (IH M (a + 8) ltac:(lia) ltac:(lia) ltac:(intros i Hi; replace (a + 8 + 8 * i) with (a + 8 * (i + 1)) by lia; apply RC; lia)) as (bs1 & R1).
  exists (bs0 ++ bs1)%list. replace (8 * S k)%nat with (8 + 8 * k)%nat by lia.
  apply SeqExec.rdn_app; [exact R0|]. rewrite (zb_add_lit a 8%nat) by lia. change (Z.of_nat 8) with 8. exact R1.
Qed.

Lemma land_high_mask_0 : forall x, 0 <= x < 16 -> Z.land x 18446744073709551600 = 0.
Proof.
  intros x Hx. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z_lt_le_dec i 4) as [L|G].
  - replace (Z.testbit 18446744073709551600 i) with false; [apply Bool.andb_false_r|].
    assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia. destruct E as [->|[->|[->| ->]]]; reflexivity.
  - rewrite (Z.bits_above_log2 x i); [reflexivity | lia |].
    destruct (Z.eq_dec x 0) as [->|NZ]; [cbn; lia|]. apply Z.log2_lt_pow2; [lia|]. eapply Z.lt_le_trans; [apply (proj2 Hx)|].
    change 16 with (2 ^ 4). apply Z.pow_le_mono_r; lia.
Qed.
Lemma lxor_pow20_nz : forall a, 0 <= a < 2 ^ 20 -> 1 <= Z.lxor a (2 ^ 20) < 2 ^ 64.
Proof.
  intros a Ha. pose proof (lxor_range64 a (2 ^ 20) ltac:(lia) ltac:(lia)).
  destruct (Z.eq_dec (Z.lxor a (2 ^ 20)) 0) as [E|NE]; [|lia].
  apply Z.lxor_eq in E. lia.
Qed.

Lemma cell_wb_other : forall M (a : Z) bs b m u,
  0 <= a -> a + Z.of_nat (length bs) < 2 ^ 64 -> 0 <= b -> b + Z.of_nat m < 2 ^ 64 -> apart a (Z.of_nat (length bs)) b (Z.of_nat m) ->
  cellA M b m u -> cellA (wbytes M (Z_to_bv 64 a) bs) b m u.
Proof.
  intros M a bs b m u Ha Hal Hb Hbm AP C. unfold cell in *. rewrite <- C. apply rdn_wbytes_out; rewrite ?art_u_lit by lia; unfold apart in AP; lia.
Qed.
Lemma wok_wb : forall M (a : word) bs b m, wokA M b m -> wokA (wbytes M a bs) b m.
Proof. intros M a bs b m W. unfold wok in *. eapply store_ok_mono; [apply wbytes_grows | exact W]. Qed.

Section FPX. Context {fx : PropExec.FPState}.
#[local] Ltac wpc := lazymatch goal with |- msteps _ (mkstr _ ?p _ _ _) _ => wlit p | |- msteps _ (mkst _ ?p _ _) _ => wlit p end.

Section STORE.
  Variables (M rom : word -> option byte) (s nd h trp size TF ST blk l2 : Z).
  Hypothesis Hs : 0x6b3000 <= s - 224 /\ s < 2 ^ 64.
  Hypothesis Hl2 : 0x6b3000 <= l2 /\ l2 + 2 ^ 20 < 2 ^ 64.
  Hypothesis Hnd : l2 + 16 <= nd /\ nd + 16 <= l2 + 2 ^ 20 /\ nd mod 16 = 0.
  Hypothesis Hblk : 0x6b3000 <= blk /\ blk + 2 ^ 23 < 2 ^ 64 /\ blk mod 8 = 0.
  Hypothesis HTF : 0 <= TF /\ TF + size + 1 <= 2 ^ 20 - 64.
  Hypothesis HST : 0 <= ST /\ ST + size + 1 < 2 ^ 20.
  Hypothesis Hsz : 1 <= size <= 30.
  Hypothesis Htrp : 4096 <= trp /\ trp + 8 * size < 2 ^ 64 /\ trp mod 8 = 0.
  Hypothesis Hh : 0 <= h < 2 ^ 64.
  Hypothesis A1 : apart (s - 224) 224 l2 (2 ^ 20).
  Hypothesis A2 : apart (s - 224) 224 blk (2 ^ 23).
  Hypothesis A3 : apart l2 (2 ^ 20) blk (2 ^ 23).
  Hypothesis A4 : apart trp (8 * size) blk (2 ^ 23).
  Hypothesis Ctrp : cellA M (s - 104) 8 trp.
  Hypothesis Cszt : cellA M (s - 96) 8 size.
  Hypothesis CTF : cellA M STO 8 TF.
  Hypothesis Cblk : cellA M (STO + 16) 8 blk.
  Hypothesis CST : cellA M (STO + 24) 4 ST.
  Hypothesis RC : forall i, 0 <= i < size -> rcell M (trp + 8 * i).
  Hypothesis Wf : wrA M (s - 224) 112.
  Hypothesis Wnd : wrA M nd 16.
  Hypothesis Wblk : wrA M blk (2 ^ 23).
  Hypothesis Wsto : wrA M STO 32.

  Definition p0 : Z := blk + 8 * TF.

  Definition dp_store_out (x : word) : Prop :=
    ~ (s - 224 <= U x < s - 112) /\ ~ (nd <= U x < nd + 8) /\ ~ (nd + 12 <= U x < nd + 16)
    /\ ~ (STO <= U x < STO + 8) /\ ~ (STO + 24 <= U x < STO + 28) /\ ~ (blk + 8 * TF <= U x < blk + 8 * TF + 8 * (size + 1)).

  Lemma dp_store_run : forall regs,
    getr regs 10 = Z_to_bv 64 nd -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 (s - 104) -> getr regs 13 = Z_to_bv 64 h ->
    getr regs 1 = (0xa13cc : word)%bv -> getr regs 2 = Z_to_bv 64 (s - 112) ->
    exists regs' M',
      msteps ASEGS (mkst regs (0xa0ebc : word) M rom) (mkst regs' (0xa13cc : word)%bv M' rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 112)
      /\ (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r)
      /\ mem_grows M M'
      /\ (forall x : word, dp_store_out x -> M' x = M x)
      /\ cellA M' STO 8 (TF + size + 1) /\ cellA M' (STO + 24) 4 (ST + size + 1) /\ cellA M' (STO + 16) 8 blk
      /\ cellA M' nd 8 h /\ cellA M' (nd + 12) 4 (TF + 1).
  Proof.
    intros regs H10 H11 H12 H13 H1 H2.
    destruct Hs as [S1' S2']. destruct Hl2 as [L1' L2']. destruct Hnd as (N1' & N2' & N3'). destruct Hblk as (B1' & B2' & B3').
    destruct HTF as [T1' T2']. destruct HST as [U1' U2']. destruct Htrp as (P1' & P2' & P3'). unfold STO in *.
    pose proof (cell8_lo _ _ _ Cszt) as Csz4. pose proof (cell8_hi M (s - 96) size ltac:(lia) ltac:(lia) ltac:(lia) Cszt) as Ctg4.
    rewrite (Z.div_small size (2 ^ 32)) in Ctg4 by lia. replace (s - 96 + 4) with (s - 92) in Ctg4 by lia.

    assert (S1 : exists r1 X1,
      msteps ASEGS (mkst regs (0xa0ebc : word) M rom) (mkst r1 (0x9eccc : word) X1 rom)
      /\ X1 = Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M
               (s - 120) (U (0xa13cc : word)%bv)) (s - 128) (U (getr regs 8))) nd h) (s - 136) 0)
               (s - 152) (U (0xa0ee8 : word)%bv)) (s - 160) nd) (s - 168) (U (getr regs 9))) (s - 176) (U (getr regs 18))) (s - 184) (U (getr regs 19)))
               (s - 192) (U (getr regs 20))) (s - 200) (U (getr regs 21))) (s - 208) 0) (s - 136) 0
      /\ getr r1 10 = Z_to_bv 64 2287752 /\ getr r1 11 = Z_to_bv 64 (size + 1) /\ getr r1 12 = Z_to_bv 64 (s - 208) /\ getr r1 13 = Z_to_bv 64 (s - 136)
      /\ getr r1 1 = Z_to_bv 64 0x9ec20 /\ getr r1 2 = Z_to_bv 64 (s - 208)
      /\ getr r1 8 = Z_to_bv 64 (s - 136) /\ getr r1 9 = Z_to_bv 64 2287752 /\ getr r1 18 = Z_to_bv 64 (size + 1) /\ getr r1 19 = Z_to_bv 64 (s - 104)
      /\ getr r1 20 = Z_to_bv 64 size /\ getr r1 21 = Z_to_bv 64 0
      /\ (forall r : reg, In r [3; 4; 22; 23; 24; 25; 26; 27]%bv -> getr r1 r = getr regs r)).
    { eexists _, _. split; [|split; [reflexivity|]].
      - zstep F_a0e6c D_a0e6c.
        zsd F_a0e70 D_a0e70 (s - 120) (U (0xa13cc : word)%bv) ltac:(rewok Wf).
        zsd F_a0e74 D_a0e74 (s - 128) (U (getr regs 8)) ltac:(rewok Wf).
        zstep F_a0e78 D_a0e78.
        zstep F_a0e7c D_a0e7c.
        zsd F_a0e80 D_a0e80 nd h ltac:(rewok Wnd).
        zsd F_a0e84 D_a0e84 (s - 136) 0 ltac:(rewok Wf).
        stepn F_a0e88 D_a0e88.
        stepn F_a0e8c D_a0e8c.
        zstep F_a0e90 D_a0e90.
        stepn F_a0e94 D_a0e94.
        zstep F_9eb58 D_9eb58.
        zsd F_9eb5c D_9eb5c (s - 152) (U (0xa0ee8 : word)%bv) ltac:(rewok Wf).
        zsd F_9eb60 D_9eb60 (s - 160) nd ltac:(rewok Wf).
        zsd F_9eb64 D_9eb64 (s - 168) (U (getr regs 9)) ltac:(rewok Wf).
        zsd F_9eb68 D_9eb68 (s - 176) (U (getr regs 18)) ltac:(rewok Wf).
        zsd F_9eb6c D_9eb6c (s - 184) (U (getr regs 19)) ltac:(rewok Wf).
        zsd F_9eb70 D_9eb70 (s - 192) (U (getr regs 20)) ltac:(rewok Wf).
        zsd F_9eb74 D_9eb74 (s - 200) (U (getr regs 21)) ltac:(rewok Wf).
        zstep F_9eb78 D_9eb78.
        match goal with |- msteps _ (mkst _ _ ?X _) _ =>
          assert (Q1 : cellA X (s - 96) 4 size) by zcell; assert (Q2 : cellA X (s - 92) 4 0) by zcell end.
        zlw F_9eb7c D_9eb7c (s - 96) Q1.
        zlw F_9eb80 D_9eb80 (s - 92) Q2.
        stepn F_9eb84 D_9eb84. rwH. rewrite art_zb_or by lia. rewrite Z.lor_0_r.
        zbtk F_9eb88 D_9eb88.
        zstep F_9eb94 D_9eb94.
        zstep F_9eb98 D_9eb98.
        zbft F_9eb9c D_9eb9c.
        zstep F_9eba0 D_9eba0.
        zstep F_9eba4 D_9eba4.
        zbtk F_9eba8 D_9eba8.
        zsd F_9ebb0 D_9ebb0 (s - 208) 0 ltac:(rewok Wf).
        zsd F_9ebb4 D_9ebb4 (s - 136) 0 ltac:(rewok Wf).
        zstep F_9ebb8 D_9ebb8.
        zstep F_9ebbc D_9ebbc.
        zstep F_9ebc0 D_9ebc0.
        zstep F_9ebc4 D_9ebc4.
        zstep F_9ebc8 D_9ebc8.
        stepn F_9ebcc D_9ebcc.
        replace (s - 112 - 32 - 64) with (s - 208) by lia. replace (s - 112 - 32 + 8) with (s - 136) by lia.
        apply mst_refl.
      - do 12 (split; [kept_solve|]). intros r Hr. cbv in Hr.
        destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; kept_solve. }
    destruct S1 as (r1 & X1 & RUN1 & EX1 & Q10 & Q11 & Q12 & Q13 & Q1 & Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & K1).

    assert (S2 : exists r2 X2,
      msteps ASEGS (mkst r1 (0x9eccc : word) X1 rom) (mkst r2 (0x9ec20 : word) X2 rom)
      /\ X2 = Wn 8 (Wn 8 (Wn 8 (Wn 8 X1 (s - 216) 0x9ec20) (s - 224) (s - 136)) 2287752 (TF + (size + 1))) (s - 208) TF
      /\ getr r2 10 = Z_to_bv 64 (blk + 8 * TF) /\ getr r2 2 = Z_to_bv 64 (s - 208) /\ getr r2 8 = Z_to_bv 64 (s - 136)
      /\ getr r2 9 = Z_to_bv 64 2287752 /\ getr r2 18 = Z_to_bv 64 (size + 1) /\ getr r2 19 = Z_to_bv 64 (s - 104) /\ getr r2 20 = Z_to_bv 64 size /\ getr r2 21 = Z_to_bv 64 0
      /\ (forall r : reg, In r [3; 4; 22; 23; 24; 25; 26; 27]%bv -> getr r2 r = getr regs r)).
    { subst X1.
      match goal with |- exists r2 X2, msteps _ (mkst _ _ ?X _) _ /\ _ =>
        assert (CTF1 : cellA X 2287752 8 TF) by zcell; assert (Cblk1 : cellA X (2287752 + 16) 8 blk) by zcell end.
      pose proof (Z.div_small TF (2 ^ 20) ltac:(lia)) as DT0. pose proof (Z.div_small (size + TF) (2 ^ 20) ltac:(lia)) as DT1.
      pose proof (Z.div_small TF (2 ^ 32) ltac:(lia)) as DT2.
      eexists _, _. split; [|split; [reflexivity|]].
      - zstep F_9ec7c D_9ec7c.
        zsd F_9ec80 D_9ec80 (s - 216) 0x9ec20 ltac:(rewok Wf).
        zsd F_9ec84 D_9ec84 (s - 224) (s - 136) ltac:(rewok Wf).
        zstep F_9ec88 D_9ec88.
        zstep F_9ec8c D_9ec8c.
        match goal with |- msteps _ (mkst _ _ ?X _) _ =>
          assert (CTF2 : cellA X 2287752 8 TF) by zcell; assert (WTF2 : wokA X 2287752 8) by (rewok Wsto) end.
        chain_step; [reflexivity
          | eapply (art_step_amoadd_d_rd _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 2287752) (Z_to_bv 64 (size + 1)) (Z_to_bv 64 TF));
            [ exact F_9ec90 | reflexivity | exact D_9ec90 | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; reflexivity
            | exact CTF2 | apply bytes_le_to_Z_8 | gres; rwH; reflexivity | exact WTF2 ]
          | ]. wpc. rewrite art_zb_add.
        change (wbytes ?M0 (Z_to_bv 64 2287752) (word_to_le_bytes 8 (Z_to_bv 64 (TF + (size + 1))))) with (Wn 8 M0 2287752 (TF + (size + 1))).
        zstep F_9ec94 D_9ec94.
        stepn F_9ec98 D_9ec98. rwH. rewrite art_zb_srli by lia. rewrite DT0.
        zstep F_9ec9c D_9ec9c.
        replace (size + 1 + -1 + TF) with (size + TF) by lia.
        stepn F_9eca0 D_9eca0. rwH. rewrite art_zb_srli by lia. rewrite DT1.
        zbft F_9eca4 D_9eca4.
        stepn F_9eca8 D_9eca8. rwH. rewrite art_zb_srli by lia. rewrite DT2.
        zbtk F_9ecac D_9ecac.
        zsd F_9ecc4 D_9ecc4 (s - 208) TF ltac:(rewok Wf).
        zstep F_9ecc8 D_9ecc8.
        zstep F_9eccc D_9eccc.
        match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cblk3 : cellA X (2287752 + 16) 8 blk) by zcell end.
        zld F_9ecd0 D_9ecd0 (2287752 + 16) Cblk3.
        zbft F_9ecd4 D_9ecd4.
        zstep F_9ecd8 D_9ecd8.
        stepn F_9ecdc D_9ecdc. rwH. rewrite (art_zb_srli_exact (TF * 2 ^ 44) 41 (8 * TF)) by lia.
        zstep F_9ece0 D_9ece0.
        match goal with |- msteps _ (mkst _ _ ?X _) _ =>
          assert (Lra : cellA X (s - 216) 8 0x9ec20) by zcell; assert (Ls0 : cellA X (s - 224) 8 (s - 136)) by zcell end.
        zld F_9ece4 D_9ece4 (s - 216) Lra.
        zld F_9ece8 D_9ece8 (s - 224) Ls0.
        zstep F_9ecec D_9ecec.
        stepret F_9ecf0 D_9ecf0 (Z_to_bv 64 0x9ec20 : word) ltac:(rwH; reflexivity).
        first [apply mst_refl | replace (s - 224 + 16) with (s - 208) by lia; apply mst_refl | replace (s - 208 + -16 + 16) with (s - 208) by lia; apply mst_refl].
      - do 8 (split; [kept_solve|]). intros r Hr. rewrite <- (K1 r Hr). cbv in Hr.
        destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; kept_solve. }
    destruct S2 as (r2 & X2 & RUN2 & EX2 & P10 & P2 & P8 & P9 & P18 & P19 & P20 & P21 & K2).

    assert (S3 : exists r3 X3,
      msteps ASEGS (mkst r2 (0x9ec20 : word) X2 rom) (mkst r3 (0x925c4 : word) X3 rom)
      /\ X3 = Wn 8 X2 (blk + 8 * TF) size
      /\ getr r3 10 = Z_to_bv 64 (blk + 8 * TF + 8) /\ getr r3 11 = Z_to_bv 64 trp /\ getr r3 12 = Z_to_bv 64 (8 * size) /\ getr r3 1 = Z_to_bv 64 0x9ec40
      /\ getr r3 2 = Z_to_bv 64 (s - 208) /\ getr r3 8 = Z_to_bv 64 (s - 136) /\ getr r3 9 = Z_to_bv 64 2287752 /\ getr r3 18 = Z_to_bv 64 (size + 1)
      /\ (forall r : reg, In r [3; 4; 22; 23; 24; 25; 26; 27]%bv -> getr r3 r = getr regs r)).
    { subst X2 X1.
      match goal with |- exists r3 X3, msteps _ (mkst _ _ ?X _) _ /\ _ => assert (Ctrp2 : cellA X (s - 104) 8 trp) by zcell end.
      eexists _, _. split; [|split; [reflexivity|]].
      - zbft F_9ebd0 D_9ebd0.
        stepn F_9ebd4 D_9ebd4. rwH.
        match goal with |- context [v_slliw (Z_to_bv 64 0) ?k] => replace (v_slliw (Z_to_bv 64 0) k) with (Z_to_bv 64 0 : word) by (apply bv_eq; vm_compute; reflexivity) end.
        zld F_9ebd8 D_9ebd8 (s - 104) Ctrp2.
        stepn F_9ebdc D_9ebdc. rwH. rewrite art_zb_or by lia. rewrite Z.lor_0_l.
        zsd F_9ebe0 D_9ebe0 (blk + 8 * TF) size ltac:(rewok Wblk).
        zstep F_9ebe4 D_9ebe4.
        zstep F_9ebe8 D_9ebe8.
        stepn F_9ebec D_9ebec.
        replace (size * 2 ^ 3) with (8 * size) by lia. apply mst_refl.
      - do 8 (split; [kept_solve|]). intros r Hr. rewrite <- (K2 r Hr). cbv in Hr.
        destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; kept_solve. }
    destruct S3 as (r3 & X3 & RUN3 & EX3 & Q10' & Q11' & Q12' & Q1' & Q2' & Q8' & Q9' & Q18' & K3).

    assert (G3 : mem_grows M X3).
    { subst X3 X2 X1. repeat (eapply mem_grows_trans; [|apply Wn_grows]). apply mem_grows_refl. }
    destruct (rdn_words (Z.to_nat size) X3 trp ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)
                ltac:(intros i Hi; apply (rcell_grows M X3 _ G3); apply RC; rewrite Z2Nat.id in Hi by lia; lia)) as (bs & Rbs).
    pose proof (rdn_length _ _ _ _ _ Rbs) as Lbs.
    assert (MCH : mcH X3 (Z_to_bv 64 (blk + 8 * TF + 8)) (Z_to_bv 64 trp) (8 * size) bs).
    { constructor.
      - lia.
      - rewrite Lbs. lia.
      - rewrite Lbs. exact Rbs.
      - rewrite Lbs. subst X3 X2 X1.
        match goal with |- store_ok _ ?X ?a ?n = true => change (wokA X (blk + 8 * TF + 8) n) end. rewok Wblk.
      - rewrite !art_u_lit by lia. unfold apart in A4. lia.
      - rewrite art_u_lit by lia. lia.
      - rewrite art_u_lit by lia. lia. }
    destruct (int_memcpy_run X3 (Z_to_bv 64 (blk + 8 * TF + 8)) (Z_to_bv 64 trp) (8 * size) bs rom MCH r3 (Z_to_bv 64 0x9ec40 : word)
                ltac:(unfold ret_ok; apply bv_eq; vm_compute; reflexivity) Q1' Q10' Q11' Q12') as (r4 & RUN4 & K4).
    set (X4 := wbytes X3 (Z_to_bv 64 (blk + 8 * TF + 8)) bs) in RUN4.
    assert (V2 : getr r4 2 = Z_to_bv 64 (s - 208)) by (rewrite (K4 2%bv) by (cbv; tauto); exact Q2').
    assert (V8 : getr r4 8 = Z_to_bv 64 (s - 136)) by (rewrite (K4 8%bv) by (cbv; tauto); exact Q8').
    assert (V9 : getr r4 9 = Z_to_bv 64 2287752) by (rewrite (K4 9%bv) by (cbv; tauto); exact Q9').
    assert (V18 : getr r4 18 = Z_to_bv 64 (size + 1)) by (rewrite (K4 18%bv) by (cbv; tauto); exact Q18').
    assert (V1 : getr r4 1 = Z_to_bv 64 0x9ec40) by (rewrite (K4 1%bv) by (cbv; tauto); exact Q1').

    subst X3 X2 X1.
    assert (C208 : cellA X4 (s - 208) 8 TF) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    pose proof (cell8_lo _ _ _ C208) as C208w.
    assert (CSTw : cellA X4 (2287752 + 24) 4 ST) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C136 : cellA X4 (s - 136) 8 0) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C152 : cellA X4 (s - 152) 8 0xa0ee8) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C160 : cellA X4 (s - 160) 8 nd) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C168 : cellA X4 (s - 168) 8 (U (getr regs 9))) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C176 : cellA X4 (s - 176) 8 (U (getr regs 18))) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C184 : cellA X4 (s - 184) 8 (U (getr regs 19))) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C192 : cellA X4 (s - 192) 8 (U (getr regs 20))) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C200 : cellA X4 (s - 200) 8 (U (getr regs 21))) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C120 : cellA X4 (s - 120) 8 0xa13cc) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C128 : cellA X4 (s - 128) 8 (U (getr regs 8))) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (WST4 : wokA X4 (2287752 + 24) 4) by (unfold X4; apply wok_wb; rewok Wsto).
    assert (WND4 : wokA X4 (nd + 12) 4) by (unfold X4; apply wok_wb; rewok Wnd).
    assert (W136 : wokA X4 (s - 136) 8) by (unfold X4; apply wok_wb; rewok Wf).
    pose proof (Z.div_pos TF (2 ^ 16) ltac:(lia) ltac:(lia)) as D16. pose proof (Z.div_lt_upper_bound TF (2 ^ 16) 16 ltac:(lia) ltac:(lia)) as D16'.
    pose proof (lxor_pow20_nz (size + 1 + ST) ltac:(lia)) as LX.

    eexists _, (Wn 4 (Wn 8 (Wn 4 X4 (2287752 + 24) (ST + (size + 1))) (s - 136) 0) (nd + 12) (TF + 1)).
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|].
      zld F_9ebf0 D_9ebf0 (s - 208) C208.
      stepn F_9ebf4 D_9ebf4. rwH. rewrite art_zb_srli by lia.
      stepn F_9ebf8 D_9ebf8. rwH. unfold v_andi. rewrite art_u_lit by lia. change (bv_wrap 64 (-16)) with 18446744073709551600.
      rewrite land_high_mask_0 by lia.
      zstep F_9ebfc D_9ebfc.
      zstep F_9ec00 D_9ec00.
      replace (2287752 + 0 + 24) with (2287752 + 24) by lia.
      chain_step; [reflexivity
        | eapply (art_step_amoadd_w_rd _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (2287752 + 24)) (Z_to_bv 64 (size + 1)) (Z_to_bv 64 ST));
          [ exact F_9ec04 | reflexivity | exact D_9ec04 | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; reflexivity
          | exact CSTw | apply art_bytes4; lia | rewrite art_u_lit by lia; lia | gres; rwH; reflexivity | exact WST4 ]
        | ]. wpc. rewrite art_zb_add. rewrite art_v_lw_small by lia.
      change (wbytes ?M0 (Z_to_bv 64 (2287752 + 24)) (word_to_le_bytes 4 (Z_to_bv 64 (ST + (size + 1))))) with (Wn 4 M0 (2287752 + 24) (ST + (size + 1))).
      stepn F_9ec08 D_9ec08.
      zstep F_9ec0c D_9ec0c.
      stepn F_9ec10 D_9ec10. rwH. rewrite (art_zb_srli_exact (ST * 2 ^ 32) 32 ST) by lia.
      zstep F_9ec14 D_9ec14.
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C136a : cellA X (s - 136) 8 0) by zcell end.
      zld F_9ec18 D_9ec18 (s - 136) C136a.
      stepn F_9ec1c D_9ec1c. rwH.
      match goal with |- context [v_xor (Z_to_bv 64 (size + 1 + ST)) ?L] =>
        replace (v_xor (Z_to_bv 64 (size + 1 + ST)) L) with (Z_to_bv 64 (Z.lxor (size + 1 + ST) (2 ^ 20)) : word)
          by (symmetry; replace L with (Z_to_bv 64 (2 ^ 20) : word) by (apply bv_eq; vm_compute; reflexivity); apply art_zb_xor; lia) end.
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C208a : cellA X (s - 208) 4 TF) by zcell end.
      zlw F_9ec20 D_9ec20 (s - 208) C208a.
      stepn F_9ec24 D_9ec24. rwH. rewrite art_zb_sltiu by lia.
      replace (if Z.lxor (size + 1 + ST) (2 ^ 20) <? 1 then 1 else 0) with 0 by (destruct (Z.ltb_spec (Z.lxor (size + 1 + ST) (2 ^ 20)) 1); lia).
      zstep F_9ec28 D_9ec28.
      zsd F_9ec2c D_9ec2c (s - 136) 0 ltac:(apply wok_Wn; exact W136).
      stepn F_9ec30 D_9ec30. rwH. unfold v_addiw. rewrite art_u_lit by lia.
      replace (bv_swrap 32 (TF + 1)) with (TF + 1) by (unfold bv_swrap, bv_wrap; change (bv_half_modulus 32) with (2 ^ 31); change (bv_modulus 32) with (2 ^ 32); rewrite Z.mod_small; lia).
      match goal with |- msteps _ (mkst _ _ ?X _) _ =>
        assert (E152 : cellA X (s - 152) 8 0xa0ee8) by zcell; assert (E160 : cellA X (s - 160) 8 nd) by zcell;
        assert (E168 : cellA X (s - 168) 8 (U (getr regs 9))) by zcell; assert (E176 : cellA X (s - 176) 8 (U (getr regs 18))) by zcell;
        assert (E184 : cellA X (s - 184) 8 (U (getr regs 19))) by zcell; assert (E192 : cellA X (s - 192) 8 (U (getr regs 20))) by zcell;
        assert (E200 : cellA X (s - 200) 8 (U (getr regs 21))) by zcell end.
      zld F_9ec34 D_9ec34 (s - 152) E152.
      zld F_9ec38 D_9ec38 (s - 160) E160.
      zld F_9ec3c D_9ec3c (s - 168) E168. rewrite Z_to_bv_bv_unsigned.
      zld F_9ec40 D_9ec40 (s - 176) E176. rewrite Z_to_bv_bv_unsigned.
      zld F_9ec44 D_9ec44 (s - 184) E184. rewrite Z_to_bv_bv_unsigned.
      zld F_9ec48 D_9ec48 (s - 192) E192. rewrite Z_to_bv_bv_unsigned.
      zld F_9ec4c D_9ec4c (s - 200) E200. rewrite Z_to_bv_bv_unsigned.
      zstep F_9ec50 D_9ec50.
      stepret F_9ec54 D_9ec54 (Z_to_bv 64 0xa0ee8 : word) ltac:(rwH; reflexivity).
      replace (s - 208 + 64) with (s - 144) by lia.
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (E136 : cellA X (s - 136) 8 0) by zcell end.
      zld F_a0e98 D_a0e98 (s - 136) E136.
      zsw F_a0e9c D_a0e9c (nd + 12) (TF + 1) ltac:(apply wok_Wn; apply wok_Wn; exact WND4).
      zbft F_a0ea0 D_a0ea0.
      match goal with |- msteps _ (mkst _ _ ?X _) _ =>
        assert (E120 : cellA X (s - 120) 8 0xa13cc) by zcell; assert (E128 : cellA X (s - 128) 8 (U (getr regs 8))) by zcell end.
      zld F_a0ea4 D_a0ea4 (s - 120) E120.
      zld F_a0ea8 D_a0ea8 (s - 128) E128. rewrite Z_to_bv_bv_unsigned.
      zstep F_a0eac D_a0eac.
      stepret F_a0eb0 D_a0eb0 (Z_to_bv 64 0xa13cc : word) ltac:(rwH; reflexivity).
      replace (s - 144 + 32) with (s - 112) by lia. apply mst_refl.
    - kept_solve.
    - intros r Hr.
      assert (KK : In r [3; 4; 22; 23; 24; 25; 26; 27]%bv -> getr r4 r = getr regs r).
      { intros Hr'. rewrite (K4 r) by (clear -Hr'; cbv in Hr' |- *; intuition). apply K3. exact Hr'. }
      cbv in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
        gres; first [ reflexivity | apply KK; cbv; tauto ].
    - unfold X4. do 3 (eapply mem_grows_trans; [|apply Wn_grows]). eapply mem_grows_trans; [exact G3 | apply wbytes_grows].
    - intros x (O1 & O2 & O3 & O4 & O5 & O6). unfold STO in O4, O5. pose proof (u64_range x). unfold X4.
      rewrite !Wn_outside by (first [lia | cbn; lia]).
      rewrite MemSplit.wbytes_outside by (rewrite ?Lbs, ?art_u_lit by lia; lia).
      rewrite !Wn_outside by (first [lia | cbn; lia]). reflexivity.
    - apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart in A3 |- *; cbn; lia|].
      apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|].
      apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|].
      replace (TF + size + 1) with (TF + (size + 1)) by lia. unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell].
    - apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart in A3 |- *; cbn; lia|].
      apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|].
      replace (ST + size + 1) with (ST + (size + 1)) by lia. apply cell_Wn_hit; cbn; lia.
    - apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart in A3 |- *; cbn; lia|].
      apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|].
      apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]. unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell].
    - apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|].
      apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart in A1 |- *; cbn; lia|].
      apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart in A3 |- *; cbn; lia|].
      unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A3 |- *; cbn; lia | zcell].
    - apply cell_Wn_hit; cbn; lia.
  Qed.
End STORE.
End FPX.
