(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib RefMemcpyLib
     MemSplit ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac Pm9ArtDepotA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import muslA.Pm9MemcpyBase Pm9IntMemcpy.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm9_code_9e000_9f000 Pm9_code_9f000_a0000 Pm9_code_a1000_a2000    .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
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
  Hypothesis Hs : 0x6b4000 <= s - 224 /\ s < 2 ^ 64.
  Hypothesis Hl2 : 0x6b4000 <= l2 /\ l2 + 2 ^ 20 < 2 ^ 64.
  Hypothesis Hnd : l2 + 16 <= nd /\ nd + 16 <= l2 + 2 ^ 20 /\ nd mod 16 = 0.
  Hypothesis Hblk : 0x6b4000 <= blk /\ blk + 2 ^ 23 < 2 ^ 64 /\ blk mod 8 = 0.
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
    getr regs 1 = (0xa178c : word)%bv -> getr regs 2 = Z_to_bv 64 (s - 112) ->
    exists regs' M',
      msteps ASEGS (mkst regs (0xa127c : word) M rom) (mkst regs' (0xa178c : word)%bv M' rom)
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
      msteps ASEGS (mkst regs (0xa127c : word) M rom) (mkst r1 (0x9f08c : word) X1 rom)
      /\ X1 = Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M
               (s - 120) (U (0xa178c : word)%bv)) (s - 128) (U (getr regs 8))) nd h) (s - 136) 0)
               (s - 152) (U (0xa12a8 : word)%bv)) (s - 160) nd) (s - 168) (U (getr regs 9))) (s - 176) (U (getr regs 18))) (s - 184) (U (getr regs 19)))
               (s - 192) (U (getr regs 20))) (s - 200) (U (getr regs 21))) (s - 208) 0) (s - 136) 0
      /\ getr r1 10 = Z_to_bv 64 2292680 /\ getr r1 11 = Z_to_bv 64 (size + 1) /\ getr r1 12 = Z_to_bv 64 (s - 208) /\ getr r1 13 = Z_to_bv 64 (s - 136)
      /\ getr r1 1 = Z_to_bv 64 0x9efe0 /\ getr r1 2 = Z_to_bv 64 (s - 208)
      /\ getr r1 8 = Z_to_bv 64 (s - 136) /\ getr r1 9 = Z_to_bv 64 2292680 /\ getr r1 18 = Z_to_bv 64 (size + 1) /\ getr r1 19 = Z_to_bv 64 (s - 104)
      /\ getr r1 20 = Z_to_bv 64 size /\ getr r1 21 = Z_to_bv 64 0
      /\ (forall r : reg, In r [3; 4; 22; 23; 24; 25; 26; 27]%bv -> getr r1 r = getr regs r)).
    { eexists _, _. split; [|split; [reflexivity|]].
      - zstep F_a1234 D_a1234.
        zsd F_a1238 D_a1238 (s - 120) (U (0xa178c : word)%bv) ltac:(rewok Wf).
        zsd F_a123c D_a123c (s - 128) (U (getr regs 8)) ltac:(rewok Wf).
        zstep F_a1240 D_a1240.
        zstep F_a1244 D_a1244.
        zsd F_a1248 D_a1248 nd h ltac:(rewok Wnd).
        zsd F_a124c D_a124c (s - 136) 0 ltac:(rewok Wf).
        stepn F_a1250 D_a1250.
        stepn F_a1254 D_a1254.
        zstep F_a1258 D_a1258.
        stepn F_a125c D_a125c.
        zstep F_9ef20 D_9ef20.
        zsd F_9ef24 D_9ef24 (s - 152) (U (0xa12a8 : word)%bv) ltac:(rewok Wf).
        zsd F_9ef28 D_9ef28 (s - 160) nd ltac:(rewok Wf).
        zsd F_9ef2c D_9ef2c (s - 168) (U (getr regs 9)) ltac:(rewok Wf).
        zsd F_9ef30 D_9ef30 (s - 176) (U (getr regs 18)) ltac:(rewok Wf).
        zsd F_9ef34 D_9ef34 (s - 184) (U (getr regs 19)) ltac:(rewok Wf).
        zsd F_9ef38 D_9ef38 (s - 192) (U (getr regs 20)) ltac:(rewok Wf).
        zsd F_9ef3c D_9ef3c (s - 200) (U (getr regs 21)) ltac:(rewok Wf).
        zstep F_9ef40 D_9ef40.
        match goal with |- msteps _ (mkst _ _ ?X _) _ =>
          assert (Q1 : cellA X (s - 96) 4 size) by zcell; assert (Q2 : cellA X (s - 92) 4 0) by zcell end.
        zlw F_9ef44 D_9ef44 (s - 96) Q1.
        zlw F_9ef48 D_9ef48 (s - 92) Q2.
        stepn F_9ef4c D_9ef4c. rwH. rewrite art_zb_or by lia. rewrite Z.lor_0_r.
        zbtk F_9ef50 D_9ef50.
        zstep F_9ef5c D_9ef5c.
        zstep F_9ef60 D_9ef60.
        zbft F_9ef64 D_9ef64.
        zstep F_9ef68 D_9ef68.
        zstep F_9ef6c D_9ef6c.
        zbtk F_9ef70 D_9ef70.
        zsd F_9ef78 D_9ef78 (s - 208) 0 ltac:(rewok Wf).
        zsd F_9ef7c D_9ef7c (s - 136) 0 ltac:(rewok Wf).
        zstep F_9ef80 D_9ef80.
        zstep F_9ef84 D_9ef84.
        zstep F_9ef88 D_9ef88.
        zstep F_9ef8c D_9ef8c.
        zstep F_9ef90 D_9ef90.
        stepn F_9ef94 D_9ef94.
        replace (s - 112 - 32 - 64) with (s - 208) by lia. replace (s - 112 - 32 + 8) with (s - 136) by lia.
        apply mst_refl.
      - do 12 (split; [kept_solve|]). intros r Hr. cbv in Hr.
        destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; kept_solve. }
    destruct S1 as (r1 & X1 & RUN1 & EX1 & Q10 & Q11 & Q12 & Q13 & Q1 & Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & K1).

    assert (S2 : exists r2 X2,
      msteps ASEGS (mkst r1 (0x9f08c : word) X1 rom) (mkst r2 (0x9efe0 : word) X2 rom)
      /\ X2 = Wn 8 (Wn 8 (Wn 8 (Wn 8 X1 (s - 216) 0x9efe0) (s - 224) (s - 136)) 2292680 (TF + (size + 1))) (s - 208) TF
      /\ getr r2 10 = Z_to_bv 64 (blk + 8 * TF) /\ getr r2 2 = Z_to_bv 64 (s - 208) /\ getr r2 8 = Z_to_bv 64 (s - 136)
      /\ getr r2 9 = Z_to_bv 64 2292680 /\ getr r2 18 = Z_to_bv 64 (size + 1) /\ getr r2 19 = Z_to_bv 64 (s - 104) /\ getr r2 20 = Z_to_bv 64 size /\ getr r2 21 = Z_to_bv 64 0
      /\ (forall r : reg, In r [3; 4; 22; 23; 24; 25; 26; 27]%bv -> getr r2 r = getr regs r)).
    { subst X1.
      match goal with |- exists r2 X2, msteps _ (mkst _ _ ?X _) _ /\ _ =>
        assert (CTF1 : cellA X 2292680 8 TF) by zcell; assert (Cblk1 : cellA X (2292680 + 16) 8 blk) by zcell end.
      pose proof (Z.div_small TF (2 ^ 20) ltac:(lia)) as DT0. pose proof (Z.div_small (size + TF) (2 ^ 20) ltac:(lia)) as DT1.
      pose proof (Z.div_small TF (2 ^ 32) ltac:(lia)) as DT2.
      eexists _, _. split; [|split; [reflexivity|]].
      - zstep F_9f044 D_9f044.
        zsd F_9f048 D_9f048 (s - 216) 0x9efe0 ltac:(rewok Wf).
        zsd F_9f04c D_9f04c (s - 224) (s - 136) ltac:(rewok Wf).
        zstep F_9f050 D_9f050.
        zstep F_9f054 D_9f054.
        match goal with |- msteps _ (mkst _ _ ?X _) _ =>
          assert (CTF2 : cellA X 2292680 8 TF) by zcell; assert (WTF2 : wokA X 2292680 8) by (rewok Wsto) end.
        chain_step; [reflexivity
          | eapply (art_step_amoadd_d_rd _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 2292680) (Z_to_bv 64 (size + 1)) (Z_to_bv 64 TF));
            [ exact F_9f058 | reflexivity | exact D_9f058 | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; reflexivity
            | exact CTF2 | apply bytes_le_to_Z_8 | gres; rwH; reflexivity | exact WTF2 ]
          | ]. wpc. rewrite art_zb_add.
        change (wbytes ?M0 (Z_to_bv 64 2292680) (word_to_le_bytes 8 (Z_to_bv 64 (TF + (size + 1))))) with (Wn 8 M0 2292680 (TF + (size + 1))).
        zstep F_9f05c D_9f05c.
        stepn F_9f060 D_9f060. rwH. rewrite art_zb_srli by lia. rewrite DT0.
        zstep F_9f064 D_9f064.
        replace (size + 1 + -1 + TF) with (size + TF) by lia.
        stepn F_9f068 D_9f068. rwH. rewrite art_zb_srli by lia. rewrite DT1.
        zbft F_9f06c D_9f06c.
        stepn F_9f070 D_9f070. rwH. rewrite art_zb_srli by lia. rewrite DT2.
        zbtk F_9f074 D_9f074.
        zsd F_9f08c D_9f08c (s - 208) TF ltac:(rewok Wf).
        zstep F_9f090 D_9f090.
        zstep F_9f094 D_9f094.
        match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cblk3 : cellA X (2292680 + 16) 8 blk) by zcell end.
        zld F_9f098 D_9f098 (2292680 + 16) Cblk3.
        zbft F_9f09c D_9f09c.
        zstep F_9f0a0 D_9f0a0.
        stepn F_9f0a4 D_9f0a4. rwH. rewrite (art_zb_srli_exact (TF * 2 ^ 44) 41 (8 * TF)) by lia.
        zstep F_9f0a8 D_9f0a8.
        match goal with |- msteps _ (mkst _ _ ?X _) _ =>
          assert (Lra : cellA X (s - 216) 8 0x9efe0) by zcell; assert (Ls0 : cellA X (s - 224) 8 (s - 136)) by zcell end.
        zld F_9f0ac D_9f0ac (s - 216) Lra.
        zld F_9f0b0 D_9f0b0 (s - 224) Ls0.
        zstep F_9f0b4 D_9f0b4.
        stepret F_9f0b8 D_9f0b8 (Z_to_bv 64 0x9efe0 : word) ltac:(rwH; reflexivity).
        first [apply mst_refl | replace (s - 224 + 16) with (s - 208) by lia; apply mst_refl | replace (s - 208 + -16 + 16) with (s - 208) by lia; apply mst_refl].
      - do 8 (split; [kept_solve|]). intros r Hr. rewrite <- (K1 r Hr). cbv in Hr.
        destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; kept_solve. }
    destruct S2 as (r2 & X2 & RUN2 & EX2 & P10 & P2 & P8 & P9 & P18 & P19 & P20 & P21 & K2).

    assert (S3 : exists r3 X3,
      msteps ASEGS (mkst r2 (0x9efe0 : word) X2 rom) (mkst r3 (0x92984 : word) X3 rom)
      /\ X3 = Wn 8 X2 (blk + 8 * TF) size
      /\ getr r3 10 = Z_to_bv 64 (blk + 8 * TF + 8) /\ getr r3 11 = Z_to_bv 64 trp /\ getr r3 12 = Z_to_bv 64 (8 * size) /\ getr r3 1 = Z_to_bv 64 0x9f000
      /\ getr r3 2 = Z_to_bv 64 (s - 208) /\ getr r3 8 = Z_to_bv 64 (s - 136) /\ getr r3 9 = Z_to_bv 64 2292680 /\ getr r3 18 = Z_to_bv 64 (size + 1)
      /\ (forall r : reg, In r [3; 4; 22; 23; 24; 25; 26; 27]%bv -> getr r3 r = getr regs r)).
    { subst X2 X1.
      match goal with |- exists r3 X3, msteps _ (mkst _ _ ?X _) _ /\ _ => assert (Ctrp2 : cellA X (s - 104) 8 trp) by zcell end.
      eexists _, _. split; [|split; [reflexivity|]].
      - zbft F_9ef98 D_9ef98.
        stepn F_9ef9c D_9ef9c. rwH.
        match goal with |- context [v_slliw (Z_to_bv 64 0) ?k] => replace (v_slliw (Z_to_bv 64 0) k) with (Z_to_bv 64 0 : word) by (apply bv_eq; vm_compute; reflexivity) end.
        zld F_9efa0 D_9efa0 (s - 104) Ctrp2.
        stepn F_9efa4 D_9efa4. rwH. rewrite art_zb_or by lia. rewrite Z.lor_0_l.
        zsd F_9efa8 D_9efa8 (blk + 8 * TF) size ltac:(rewok Wblk).
        zstep F_9efac D_9efac.
        zstep F_9efb0 D_9efb0.
        stepn F_9efb4 D_9efb4.
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
    destruct (int_memcpy_run X3 (Z_to_bv 64 (blk + 8 * TF + 8)) (Z_to_bv 64 trp) (8 * size) bs rom MCH r3 (Z_to_bv 64 0x9f000 : word)
                ltac:(unfold ret_ok; apply bv_eq; vm_compute; reflexivity) Q1' Q10' Q11' Q12') as (r4 & RUN4 & K4).
    set (X4 := wbytes X3 (Z_to_bv 64 (blk + 8 * TF + 8)) bs) in RUN4.
    assert (V2 : getr r4 2 = Z_to_bv 64 (s - 208)) by (rewrite (K4 2%bv) by (cbv; tauto); exact Q2').
    assert (V8 : getr r4 8 = Z_to_bv 64 (s - 136)) by (rewrite (K4 8%bv) by (cbv; tauto); exact Q8').
    assert (V9 : getr r4 9 = Z_to_bv 64 2292680) by (rewrite (K4 9%bv) by (cbv; tauto); exact Q9').
    assert (V18 : getr r4 18 = Z_to_bv 64 (size + 1)) by (rewrite (K4 18%bv) by (cbv; tauto); exact Q18').
    assert (V1 : getr r4 1 = Z_to_bv 64 0x9f000) by (rewrite (K4 1%bv) by (cbv; tauto); exact Q1').

    subst X3 X2 X1.
    assert (C208 : cellA X4 (s - 208) 8 TF) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    pose proof (cell8_lo _ _ _ C208) as C208w.
    assert (CSTw : cellA X4 (2292680 + 24) 4 ST) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C136 : cellA X4 (s - 136) 8 0) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C152 : cellA X4 (s - 152) 8 0xa12a8) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C160 : cellA X4 (s - 160) 8 nd) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C168 : cellA X4 (s - 168) 8 (U (getr regs 9))) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C176 : cellA X4 (s - 176) 8 (U (getr regs 18))) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C184 : cellA X4 (s - 184) 8 (U (getr regs 19))) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C192 : cellA X4 (s - 192) 8 (U (getr regs 20))) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C200 : cellA X4 (s - 200) 8 (U (getr regs 21))) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C120 : cellA X4 (s - 120) 8 0xa178c) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C128 : cellA X4 (s - 128) 8 (U (getr regs 8))) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (WST4 : wokA X4 (2292680 + 24) 4) by (unfold X4; apply wok_wb; rewok Wsto).
    assert (WND4 : wokA X4 (nd + 12) 4) by (unfold X4; apply wok_wb; rewok Wnd).
    assert (W136 : wokA X4 (s - 136) 8) by (unfold X4; apply wok_wb; rewok Wf).
    pose proof (Z.div_pos TF (2 ^ 16) ltac:(lia) ltac:(lia)) as D16. pose proof (Z.div_lt_upper_bound TF (2 ^ 16) 16 ltac:(lia) ltac:(lia)) as D16'.
    pose proof (lxor_pow20_nz (size + 1 + ST) ltac:(lia)) as LX.

    eexists _, (Wn 4 (Wn 8 (Wn 4 X4 (2292680 + 24) (ST + (size + 1))) (s - 136) 0) (nd + 12) (TF + 1)).
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|].
      zld F_9efb8 D_9efb8 (s - 208) C208.
      stepn F_9efbc D_9efbc. rwH. rewrite art_zb_srli by lia.
      stepn F_9efc0 D_9efc0. rwH. unfold v_andi. rewrite art_u_lit by lia. change (bv_wrap 64 (-16)) with 18446744073709551600.
      rewrite land_high_mask_0 by lia.
      zstep F_9efc4 D_9efc4.
      zstep F_9efc8 D_9efc8.
      replace (2292680 + 0 + 24) with (2292680 + 24) by lia.
      chain_step; [reflexivity
        | eapply (art_step_amoadd_w_rd _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (2292680 + 24)) (Z_to_bv 64 (size + 1)) (Z_to_bv 64 ST));
          [ exact F_9efcc | reflexivity | exact D_9efcc | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; reflexivity
          | exact CSTw | apply art_bytes4; lia | rewrite art_u_lit by lia; lia | gres; rwH; reflexivity | exact WST4 ]
        | ]. wpc. rewrite art_zb_add. rewrite art_v_lw_small by lia.
      change (wbytes ?M0 (Z_to_bv 64 (2292680 + 24)) (word_to_le_bytes 4 (Z_to_bv 64 (ST + (size + 1))))) with (Wn 4 M0 (2292680 + 24) (ST + (size + 1))).
      stepn F_9efd0 D_9efd0.
      zstep F_9efd4 D_9efd4.
      stepn F_9efd8 D_9efd8. rwH. rewrite (art_zb_srli_exact (ST * 2 ^ 32) 32 ST) by lia.
      zstep F_9efdc D_9efdc.
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C136a : cellA X (s - 136) 8 0) by zcell end.
      zld F_9efe0 D_9efe0 (s - 136) C136a.
      stepn F_9efe4 D_9efe4. rwH.
      match goal with |- context [v_xor (Z_to_bv 64 (size + 1 + ST)) ?L] =>
        replace (v_xor (Z_to_bv 64 (size + 1 + ST)) L) with (Z_to_bv 64 (Z.lxor (size + 1 + ST) (2 ^ 20)) : word)
          by (symmetry; replace L with (Z_to_bv 64 (2 ^ 20) : word) by (apply bv_eq; vm_compute; reflexivity); apply art_zb_xor; lia) end.
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C208a : cellA X (s - 208) 4 TF) by zcell end.
      zlw F_9efe8 D_9efe8 (s - 208) C208a.
      stepn F_9efec D_9efec. rwH. rewrite art_zb_sltiu by lia.
      replace (if Z.lxor (size + 1 + ST) (2 ^ 20) <? 1 then 1 else 0) with 0 by (destruct (Z.ltb_spec (Z.lxor (size + 1 + ST) (2 ^ 20)) 1); lia).
      zstep F_9eff0 D_9eff0.
      zsd F_9eff4 D_9eff4 (s - 136) 0 ltac:(apply wok_Wn; exact W136).
      stepn F_9eff8 D_9eff8. rwH. unfold v_addiw. rewrite art_u_lit by lia.
      replace (bv_swrap 32 (TF + 1)) with (TF + 1) by (unfold bv_swrap, bv_wrap; change (bv_half_modulus 32) with (2 ^ 31); change (bv_modulus 32) with (2 ^ 32); rewrite Z.mod_small; lia).
      match goal with |- msteps _ (mkst _ _ ?X _) _ =>
        assert (E152 : cellA X (s - 152) 8 0xa12a8) by zcell; assert (E160 : cellA X (s - 160) 8 nd) by zcell;
        assert (E168 : cellA X (s - 168) 8 (U (getr regs 9))) by zcell; assert (E176 : cellA X (s - 176) 8 (U (getr regs 18))) by zcell;
        assert (E184 : cellA X (s - 184) 8 (U (getr regs 19))) by zcell; assert (E192 : cellA X (s - 192) 8 (U (getr regs 20))) by zcell;
        assert (E200 : cellA X (s - 200) 8 (U (getr regs 21))) by zcell end.
      zld F_9effc D_9effc (s - 152) E152.
      zld F_9f000 D_9f000 (s - 160) E160.
      zld F_9f004 D_9f004 (s - 168) E168. rewrite Z_to_bv_bv_unsigned.
      zld F_9f008 D_9f008 (s - 176) E176. rewrite Z_to_bv_bv_unsigned.
      zld F_9f00c D_9f00c (s - 184) E184. rewrite Z_to_bv_bv_unsigned.
      zld F_9f010 D_9f010 (s - 192) E192. rewrite Z_to_bv_bv_unsigned.
      zld F_9f014 D_9f014 (s - 200) E200. rewrite Z_to_bv_bv_unsigned.
      zstep F_9f018 D_9f018.
      stepret F_9f01c D_9f01c (Z_to_bv 64 0xa12a8 : word) ltac:(rwH; reflexivity).
      replace (s - 208 + 64) with (s - 144) by lia.
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (E136 : cellA X (s - 136) 8 0) by zcell end.
      zld F_a1260 D_a1260 (s - 136) E136.
      zsw F_a1264 D_a1264 (nd + 12) (TF + 1) ltac:(apply wok_Wn; apply wok_Wn; exact WND4).
      zbft F_a1268 D_a1268.
      match goal with |- msteps _ (mkst _ _ ?X _) _ =>
        assert (E120 : cellA X (s - 120) 8 0xa178c) by zcell; assert (E128 : cellA X (s - 128) 8 (U (getr regs 8))) by zcell end.
      zld F_a126c D_a126c (s - 120) E120.
      zld F_a1270 D_a1270 (s - 128) E128. rewrite Z_to_bv_bv_unsigned.
      zstep F_a1274 D_a1274.
      stepret F_a1278 D_a1278 (Z_to_bv 64 0xa178c : word) ltac:(rwH; reflexivity).
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
