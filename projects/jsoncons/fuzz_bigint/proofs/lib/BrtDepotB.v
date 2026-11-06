(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib RefMemcpyLib
     MemSplit ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac BrtDepotA.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import muslA.Bo0MemcpyBase Bo0IntMemcpy.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import Bo0_code_7fe40_7fe9c Bo0_code_7db2c_7dd84 Bo0_code_71564_71640.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
(* [comment removed for export] *)
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
(* [comment removed for export] *)
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


(* [comment removed for export] *)
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
  Hypothesis Hs : 0x634000 <= s - 224 /\ s < 2 ^ 64.
  Hypothesis Hl2 : 0x634000 <= l2 /\ l2 + 2 ^ 20 < 2 ^ 64.
  Hypothesis Hnd : l2 + 16 <= nd /\ nd + 16 <= l2 + 2 ^ 20 /\ nd mod 16 = 0.
  Hypothesis Hblk : 0x634000 <= blk /\ blk + 2 ^ 23 < 2 ^ 64 /\ blk mod 8 = 0.
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

  Definition p0 : Z := blk + 8 * TF.     (* [comment removed for export] *)

  Definition dp_store_out (x : word) : Prop :=
    ~ (s - 224 <= U x < s - 112) /\ ~ (nd <= U x < nd + 8) /\ ~ (nd + 12 <= U x < nd + 16)
    /\ ~ (STO <= U x < STO + 8) /\ ~ (STO + 24 <= U x < STO + 28) /\ ~ (blk + 8 * TF <= U x < blk + 8 * TF + 8 * (size + 1)).

  Lemma dp_store_run : forall regs,
    getr regs 10 = Z_to_bv 64 nd -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 (s - 104) -> getr regs 13 = Z_to_bv 64 h ->
    getr regs 1 = (0x80350 : word)%bv -> getr regs 2 = Z_to_bv 64 (s - 112) ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x7fe40 : word) M rom) (mkst regs' (0x80350 : word)%bv M' rom)
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
    (* [comment removed for export] *)
    assert (S1 : exists r1 X1,
      msteps ASEGS (mkst regs (0x7fe40 : word) M rom) (mkst r1 (0x7dc50 : word) X1 rom)
      /\ X1 = Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M
               (s - 120) (U (0x80350 : word)%bv)) (s - 128) (U (getr regs 8))) nd h) (s - 136) 0)
               (s - 152) (U (0x7fe6c : word)%bv)) (s - 160) nd) (s - 168) (U (getr regs 9))) (s - 176) (U (getr regs 18))) (s - 184) (U (getr regs 19)))
               (s - 192) (U (getr regs 20))) (s - 200) (U (getr regs 21))) (s - 208) 0) (s - 136) 0
      /\ getr r1 10 = Z_to_bv 64 1771016 /\ getr r1 11 = Z_to_bv 64 (size + 1) /\ getr r1 12 = Z_to_bv 64 (s - 208) /\ getr r1 13 = Z_to_bv 64 (s - 136)
      /\ getr r1 1 = Z_to_bv 64 0x7dba4 /\ getr r1 2 = Z_to_bv 64 (s - 208)
      /\ getr r1 8 = Z_to_bv 64 (s - 136) /\ getr r1 9 = Z_to_bv 64 1771016 /\ getr r1 18 = Z_to_bv 64 (size + 1) /\ getr r1 19 = Z_to_bv 64 (s - 104)
      /\ getr r1 20 = Z_to_bv 64 size /\ getr r1 21 = Z_to_bv 64 0
      /\ (forall r : reg, In r [3; 4; 22; 23; 24; 25; 26; 27]%bv -> getr r1 r = getr regs r)).
    { eexists _, _. split; [|split; [reflexivity|]].
      - zstep F_7fe40 D_7fe40.                                                   (* [comment removed for export] *)
        zsd F_7fe44 D_7fe44 (s - 120) (U (0x80350 : word)%bv) ltac:(rewok Wf).         (* [comment removed for export] *)
        zsd F_7fe48 D_7fe48 (s - 128) (U (getr regs 8)) ltac:(rewok Wf).            (* [comment removed for export] *)
        zstep F_7fe4c D_7fe4c.                                                   (* [comment removed for export] *)
        zstep F_7fe50 D_7fe50.                                                   (* [comment removed for export] *)
        zsd F_7fe54 D_7fe54 nd h ltac:(rewok Wnd).                                  (* [comment removed for export] *)
        zsd F_7fe58 D_7fe58 (s - 136) 0 ltac:(rewok Wf).                            (* [comment removed for export] *)
        stepn F_7fe5c D_7fe5c.                                                   (* [comment removed for export] *)
        stepn F_7fe60 D_7fe60.                                                   (* [comment removed for export] *)
        zstep F_7fe64 D_7fe64.                                                   (* [comment removed for export] *)
        stepn F_7fe68 D_7fe68.                                                   (* [comment removed for export] *)
        zstep F_7db2c D_7db2c.                                                   (* [comment removed for export] *)
        zsd F_7db30 D_7db30 (s - 152) (U (0x7fe6c : word)%bv) ltac:(rewok Wf).         (* [comment removed for export] *)
        zsd F_7db34 D_7db34 (s - 160) nd ltac:(rewok Wf).                           (* [comment removed for export] *)
        zsd F_7db38 D_7db38 (s - 168) (U (getr regs 9)) ltac:(rewok Wf).            (* [comment removed for export] *)
        zsd F_7db3c D_7db3c (s - 176) (U (getr regs 18)) ltac:(rewok Wf).           (* [comment removed for export] *)
        zsd F_7db40 D_7db40 (s - 184) (U (getr regs 19)) ltac:(rewok Wf).           (* [comment removed for export] *)
        zsd F_7db44 D_7db44 (s - 192) (U (getr regs 20)) ltac:(rewok Wf).           (* [comment removed for export] *)
        zsd F_7db48 D_7db48 (s - 200) (U (getr regs 21)) ltac:(rewok Wf).           (* [comment removed for export] *)
        zstep F_7db4c D_7db4c.                                                   (* [comment removed for export] *)
        match goal with |- msteps _ (mkst _ _ ?X _) _ =>
          assert (Q1 : cellA X (s - 96) 4 size) by zcell; assert (Q2 : cellA X (s - 92) 4 0) by zcell end.
        zlw F_7db50 D_7db50 (s - 96) Q1.                                         (* [comment removed for export] *)
        zlw F_7db54 D_7db54 (s - 92) Q2.                                         (* [comment removed for export] *)
        stepn F_7db58 D_7db58. rwH. rewrite art_zb_or by lia. rewrite Z.lor_0_r.  (* [comment removed for export] *)
        zbtk F_7db5c D_7db5c.                                                    (* [comment removed for export] *)
        zstep F_7db68 D_7db68.                                                   (* [comment removed for export] *)
        zstep F_7db6c D_7db6c.                                                   (* [comment removed for export] *)
        zbft F_7db70 D_7db70.                                                    (* [comment removed for export] *)
        zstep F_7db74 D_7db74.                                                   (* [comment removed for export] *)
        zstep F_7db78 D_7db78.                                                   (* [comment removed for export] *)
        zbtk F_7db7c D_7db7c.                                                    (* [comment removed for export] *)
        zsd F_7db84 D_7db84 (s - 208) 0 ltac:(rewok Wf).                            (* [comment removed for export] *)
        zsd F_7db88 D_7db88 (s - 136) 0 ltac:(rewok Wf).                            (* [comment removed for export] *)
        zstep F_7db8c D_7db8c.                                                   (* [comment removed for export] *)
        zstep F_7db90 D_7db90.                                                   (* [comment removed for export] *)
        zstep F_7db94 D_7db94.                                                   (* [comment removed for export] *)
        zstep F_7db98 D_7db98.                                                   (* [comment removed for export] *)
        zstep F_7db9c D_7db9c.                                                   (* [comment removed for export] *)
        stepn F_7dba0 D_7dba0.                                                   (* [comment removed for export] *)
        replace (s - 112 - 32 - 64) with (s - 208) by lia. replace (s - 112 - 32 + 8) with (s - 136) by lia.
        apply mst_refl.
      - do 12 (split; [kept_solve|]). intros r Hr. cbv in Hr.
        destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; kept_solve. }
    destruct S1 as (r1 & X1 & RUN1 & EX1 & Q10 & Q11 & Q12 & Q13 & Q1 & Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & K1).
    (* [comment removed for export] *)
    assert (S2 : exists r2 X2,
      msteps ASEGS (mkst r1 (0x7dc50 : word) X1 rom) (mkst r2 (0x7dba4 : word) X2 rom)
      /\ X2 = Wn 8 (Wn 8 (Wn 8 (Wn 8 X1 (s - 216) 0x7dba4) (s - 224) (s - 136)) 1771016 (TF + (size + 1))) (s - 208) TF
      /\ getr r2 10 = Z_to_bv 64 (blk + 8 * TF) /\ getr r2 2 = Z_to_bv 64 (s - 208) /\ getr r2 8 = Z_to_bv 64 (s - 136)
      /\ getr r2 9 = Z_to_bv 64 1771016 /\ getr r2 18 = Z_to_bv 64 (size + 1) /\ getr r2 19 = Z_to_bv 64 (s - 104) /\ getr r2 20 = Z_to_bv 64 size /\ getr r2 21 = Z_to_bv 64 0
      /\ (forall r : reg, In r [3; 4; 22; 23; 24; 25; 26; 27]%bv -> getr r2 r = getr regs r)).
    { subst X1.
      match goal with |- exists r2 X2, msteps _ (mkst _ _ ?X _) _ /\ _ =>
        assert (CTF1 : cellA X 1771016 8 TF) by zcell; assert (Cblk1 : cellA X (1771016 + 16) 8 blk) by zcell end.
      pose proof (Z.div_small TF (2 ^ 20) ltac:(lia)) as DT0. pose proof (Z.div_small (size + TF) (2 ^ 20) ltac:(lia)) as DT1.
      pose proof (Z.div_small TF (2 ^ 32) ltac:(lia)) as DT2.
      eexists _, _. split; [|split; [reflexivity|]].
      - zstep F_7dc50 D_7dc50.                                                   (* [comment removed for export] *)
        zsd F_7dc54 D_7dc54 (s - 216) 0x7dba4 ltac:(rewok Wf).                      (* [comment removed for export] *)
        zsd F_7dc58 D_7dc58 (s - 224) (s - 136) ltac:(rewok Wf).                    (* [comment removed for export] *)
        zstep F_7dc5c D_7dc5c.                                                   (* [comment removed for export] *)
        zstep F_7dc60 D_7dc60.                                                   (* [comment removed for export] *)
        match goal with |- msteps _ (mkst _ _ ?X _) _ =>
          assert (CTF2 : cellA X 1771016 8 TF) by zcell; assert (WTF2 : wokA X 1771016 8) by (rewok Wsto) end.
        chain_step; [reflexivity
          | eapply (art_step_amoadd_d_rd _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 1771016) (Z_to_bv 64 (size + 1)) (Z_to_bv 64 TF));
            [ exact F_7dc64 | reflexivity | exact D_7dc64 | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; reflexivity
            | exact CTF2 | apply bytes_le_to_Z_8 | gres; rwH; reflexivity | exact WTF2 ]
          | ]. wpc. rewrite art_zb_add.                                         (* [comment removed for export] *)
        change (wbytes ?M0 (Z_to_bv 64 1771016) (word_to_le_bytes 8 (Z_to_bv 64 (TF + (size + 1))))) with (Wn 8 M0 1771016 (TF + (size + 1))).
        zstep F_7dc68 D_7dc68.                                                   (* [comment removed for export] *)
        stepn F_7dc6c D_7dc6c. rwH. rewrite art_zb_srli by lia. rewrite DT0.     (* [comment removed for export] *)
        zstep F_7dc70 D_7dc70.                                                   (* [comment removed for export] *)
        replace (size + 1 + -1 + TF) with (size + TF) by lia.
        stepn F_7dc74 D_7dc74. rwH. rewrite art_zb_srli by lia. rewrite DT1.     (* [comment removed for export] *)
        zbft F_7dc78 D_7dc78.                                                    (* [comment removed for export] *)
        stepn F_7dc7c D_7dc7c. rwH. rewrite art_zb_srli by lia. rewrite DT2.     (* [comment removed for export] *)
        zbtk F_7dc80 D_7dc80.                                                    (* [comment removed for export] *)
        zsd F_7dc98 D_7dc98 (s - 208) TF ltac:(rewok Wf).                           (* [comment removed for export] *)
        zstep F_7dc9c D_7dc9c.                                                   (* [comment removed for export] *)
        zstep F_7dca0 D_7dca0.                                                   (* [comment removed for export] *)
        match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cblk3 : cellA X (1771016 + 16) 8 blk) by zcell end.
        zld F_7dca4 D_7dca4 (1771016 + 16) Cblk3.                                (* [comment removed for export] *)
        zbft F_7dca8 D_7dca8.                                                    (* [comment removed for export] *)
        zstep F_7dcac D_7dcac.                                                   (* [comment removed for export] *)
        stepn F_7dcb0 D_7dcb0. rwH. rewrite (art_zb_srli_exact (TF * 2 ^ 44) 41 (8 * TF)) by lia.   (* [comment removed for export] *)
        zstep F_7dcb4 D_7dcb4.                                                   (* [comment removed for export] *)
        match goal with |- msteps _ (mkst _ _ ?X _) _ =>
          assert (Lra : cellA X (s - 216) 8 0x7dba4) by zcell; assert (Ls0 : cellA X (s - 224) 8 (s - 136)) by zcell end.
        zld F_7dcb8 D_7dcb8 (s - 216) Lra.                                       (* [comment removed for export] *)
        zld F_7dcbc D_7dcbc (s - 224) Ls0.                                       (* [comment removed for export] *)
        zstep F_7dcc0 D_7dcc0.                                                   (* [comment removed for export] *)
        stepret F_7dcc4 D_7dcc4 (Z_to_bv 64 0x7dba4 : word) ltac:(rwH; reflexivity).
        first [apply mst_refl | replace (s - 224 + 16) with (s - 208) by lia; apply mst_refl | replace (s - 208 + -16 + 16) with (s - 208) by lia; apply mst_refl].
      - do 8 (split; [kept_solve|]). intros r Hr. rewrite <- (K1 r Hr). cbv in Hr.
        destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; kept_solve. }
    destruct S2 as (r2 & X2 & RUN2 & EX2 & P10 & P2 & P8 & P9 & P18 & P19 & P20 & P21 & K2).
    (* [comment removed for export] *)
    assert (S3 : exists r3 X3,
      msteps ASEGS (mkst r2 (0x7dba4 : word) X2 rom) (mkst r3 (0x71564 : word) X3 rom)
      /\ X3 = Wn 8 X2 (blk + 8 * TF) size
      /\ getr r3 10 = Z_to_bv 64 (blk + 8 * TF + 8) /\ getr r3 11 = Z_to_bv 64 trp /\ getr r3 12 = Z_to_bv 64 (8 * size) /\ getr r3 1 = Z_to_bv 64 0x7dbc4
      /\ getr r3 2 = Z_to_bv 64 (s - 208) /\ getr r3 8 = Z_to_bv 64 (s - 136) /\ getr r3 9 = Z_to_bv 64 1771016 /\ getr r3 18 = Z_to_bv 64 (size + 1)
      /\ (forall r : reg, In r [3; 4; 22; 23; 24; 25; 26; 27]%bv -> getr r3 r = getr regs r)).
    { subst X2 X1.
      match goal with |- exists r3 X3, msteps _ (mkst _ _ ?X _) _ /\ _ => assert (Ctrp2 : cellA X (s - 104) 8 trp) by zcell end.
      eexists _, _. split; [|split; [reflexivity|]].
      - zbft F_7dba4 D_7dba4.                                                    (* [comment removed for export] *)
        stepn F_7dba8 D_7dba8. rwH.                                              (* [comment removed for export] *)
        match goal with |- context [v_slliw (Z_to_bv 64 0) ?k] => replace (v_slliw (Z_to_bv 64 0) k) with (Z_to_bv 64 0 : word) by (apply bv_eq; vm_compute; reflexivity) end.
        zld F_7dbac D_7dbac (s - 104) Ctrp2.                                     (* [comment removed for export] *)
        stepn F_7dbb0 D_7dbb0. rwH. rewrite art_zb_or by lia. rewrite Z.lor_0_l. (* [comment removed for export] *)
        zsd F_7dbb4 D_7dbb4 (blk + 8 * TF) size ltac:(rewok Wblk).                  (* [comment removed for export] *)
        zstep F_7dbb8 D_7dbb8.                                                   (* [comment removed for export] *)
        zstep F_7dbbc D_7dbbc.                                                   (* [comment removed for export] *)
        stepn F_7dbc0 D_7dbc0.                                                   (* [comment removed for export] *)
        replace (size * 2 ^ 3) with (8 * size) by lia. apply mst_refl.
      - do 8 (split; [kept_solve|]). intros r Hr. rewrite <- (K2 r Hr). cbv in Hr.
        destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; kept_solve. }
    destruct S3 as (r3 & X3 & RUN3 & EX3 & Q10' & Q11' & Q12' & Q1' & Q2' & Q8' & Q9' & Q18' & K3).
    (* [comment removed for export] *)
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
    destruct (int_memcpy_run X3 (Z_to_bv 64 (blk + 8 * TF + 8)) (Z_to_bv 64 trp) (8 * size) bs rom MCH r3 (Z_to_bv 64 0x7dbc4 : word)
                ltac:(unfold ret_ok; apply bv_eq; vm_compute; reflexivity) Q1' Q10' Q11' Q12') as (r4 & RUN4 & K4).
    set (X4 := wbytes X3 (Z_to_bv 64 (blk + 8 * TF + 8)) bs) in RUN4.
    assert (V2 : getr r4 2 = Z_to_bv 64 (s - 208)) by (rewrite (K4 2%bv) by (cbv; tauto); exact Q2').
    assert (V8 : getr r4 8 = Z_to_bv 64 (s - 136)) by (rewrite (K4 8%bv) by (cbv; tauto); exact Q8').
    assert (V9 : getr r4 9 = Z_to_bv 64 1771016) by (rewrite (K4 9%bv) by (cbv; tauto); exact Q9').
    assert (V18 : getr r4 18 = Z_to_bv 64 (size + 1)) by (rewrite (K4 18%bv) by (cbv; tauto); exact Q18').
    assert (V1 : getr r4 1 = Z_to_bv 64 0x7dbc4) by (rewrite (K4 1%bv) by (cbv; tauto); exact Q1').
    (* [comment removed for export] *)
    subst X3 X2 X1.
    assert (C208 : cellA X4 (s - 208) 8 TF) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    pose proof (cell8_lo _ _ _ C208) as C208w.
    assert (CSTw : cellA X4 (1771016 + 24) 4 ST) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C136 : cellA X4 (s - 136) 8 0) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C152 : cellA X4 (s - 152) 8 0x7fe6c) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C160 : cellA X4 (s - 160) 8 nd) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C168 : cellA X4 (s - 168) 8 (U (getr regs 9))) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C176 : cellA X4 (s - 176) 8 (U (getr regs 18))) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C184 : cellA X4 (s - 184) 8 (U (getr regs 19))) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C192 : cellA X4 (s - 192) 8 (U (getr regs 20))) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C200 : cellA X4 (s - 200) 8 (U (getr regs 21))) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C120 : cellA X4 (s - 120) 8 0x80350) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C128 : cellA X4 (s - 128) 8 (U (getr regs 8))) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (WST4 : wokA X4 (1771016 + 24) 4) by (unfold X4; apply wok_wb; rewok Wsto).
    assert (WND4 : wokA X4 (nd + 12) 4) by (unfold X4; apply wok_wb; rewok Wnd).
    assert (W136 : wokA X4 (s - 136) 8) by (unfold X4; apply wok_wb; rewok Wf).
    pose proof (Z.div_pos TF (2 ^ 16) ltac:(lia) ltac:(lia)) as D16. pose proof (Z.div_lt_upper_bound TF (2 ^ 16) 16 ltac:(lia) ltac:(lia)) as D16'.
    pose proof (lxor_pow20_nz (size + 1 + ST) ltac:(lia)) as LX.
    (* [comment removed for export] *)
    eexists _, (Wn 4 (Wn 8 (Wn 4 X4 (1771016 + 24) (ST + (size + 1))) (s - 136) 0) (nd + 12) (TF + 1)).
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|].
      zld F_7dbc4 D_7dbc4 (s - 208) C208.                                        (* [comment removed for export] *)
      stepn F_7dbc8 D_7dbc8. rwH. rewrite art_zb_srli by lia.                    (* [comment removed for export] *)
      stepn F_7dbcc D_7dbcc. rwH. unfold v_andi. rewrite art_u_lit by lia. change (bv_wrap 64 (-16)) with 18446744073709551600.
      rewrite land_high_mask_0 by lia.                                           (* [comment removed for export] *)
      zstep F_7dbd0 D_7dbd0.                                                     (* [comment removed for export] *)
      zstep F_7dbd4 D_7dbd4.                                                     (* [comment removed for export] *)
      replace (1771016 + 0 + 24) with (1771016 + 24) by lia.
      chain_step; [reflexivity
        | eapply (art_step_amoadd_w_rd _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (1771016 + 24)) (Z_to_bv 64 (size + 1)) (Z_to_bv 64 ST));
          [ exact F_7dbd8 | reflexivity | exact D_7dbd8 | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; reflexivity
          | exact CSTw | apply art_bytes4; lia | rewrite art_u_lit by lia; lia | gres; rwH; reflexivity | exact WST4 ]
        | ]. wpc. rewrite art_zb_add. rewrite art_v_lw_small by lia.              (* [comment removed for export] *)
      change (wbytes ?M0 (Z_to_bv 64 (1771016 + 24)) (word_to_le_bytes 4 (Z_to_bv 64 (ST + (size + 1))))) with (Wn 4 M0 (1771016 + 24) (ST + (size + 1))).
      stepn F_7dbdc D_7dbdc.                                                     (* [comment removed for export] *)
      zstep F_7dbe0 D_7dbe0.                                                     (* [comment removed for export] *)
      stepn F_7dbe4 D_7dbe4. rwH. rewrite (art_zb_srli_exact (ST * 2 ^ 32) 32 ST) by lia.   (* [comment removed for export] *)
      zstep F_7dbe8 D_7dbe8.                                                     (* [comment removed for export] *)
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C136a : cellA X (s - 136) 8 0) by zcell end.
      zld F_7dbec D_7dbec (s - 136) C136a.                                       (* [comment removed for export] *)
      stepn F_7dbf0 D_7dbf0. rwH.                                                (* [comment removed for export] *)
      match goal with |- context [v_xor (Z_to_bv 64 (size + 1 + ST)) ?L] =>
        replace (v_xor (Z_to_bv 64 (size + 1 + ST)) L) with (Z_to_bv 64 (Z.lxor (size + 1 + ST) (2 ^ 20)) : word)
          by (symmetry; replace L with (Z_to_bv 64 (2 ^ 20) : word) by (apply bv_eq; vm_compute; reflexivity); apply art_zb_xor; lia) end.
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C208a : cellA X (s - 208) 4 TF) by zcell end.
      zlw F_7dbf4 D_7dbf4 (s - 208) C208a.                                       (* [comment removed for export] *)
      stepn F_7dbf8 D_7dbf8. rwH. rewrite art_zb_sltiu by lia.
      replace (if Z.lxor (size + 1 + ST) (2 ^ 20) <? 1 then 1 else 0) with 0 by (destruct (Z.ltb_spec (Z.lxor (size + 1 + ST) (2 ^ 20)) 1); lia).   (* [comment removed for export] *)
      zstep F_7dbfc D_7dbfc.                                                     (* [comment removed for export] *)
      zsd F_7dc00 D_7dc00 (s - 136) 0 ltac:(apply wok_Wn; exact W136).            (* [comment removed for export] *)
      stepn F_7dc04 D_7dc04. rwH. unfold v_addiw. rewrite art_u_lit by lia.
      replace (bv_swrap 32 (TF + 1)) with (TF + 1) by (unfold bv_swrap, bv_wrap; change (bv_half_modulus 32) with (2 ^ 31); change (bv_modulus 32) with (2 ^ 32); rewrite Z.mod_small; lia).   (* [comment removed for export] *)
      match goal with |- msteps _ (mkst _ _ ?X _) _ =>
        assert (E152 : cellA X (s - 152) 8 0x7fe6c) by zcell; assert (E160 : cellA X (s - 160) 8 nd) by zcell;
        assert (E168 : cellA X (s - 168) 8 (U (getr regs 9))) by zcell; assert (E176 : cellA X (s - 176) 8 (U (getr regs 18))) by zcell;
        assert (E184 : cellA X (s - 184) 8 (U (getr regs 19))) by zcell; assert (E192 : cellA X (s - 192) 8 (U (getr regs 20))) by zcell;
        assert (E200 : cellA X (s - 200) 8 (U (getr regs 21))) by zcell end.
      zld F_7dc08 D_7dc08 (s - 152) E152.                                        (* [comment removed for export] *)
      zld F_7dc0c D_7dc0c (s - 160) E160.                                        (* [comment removed for export] *)
      zld F_7dc10 D_7dc10 (s - 168) E168. rewrite Z_to_bv_bv_unsigned.           (* [comment removed for export] *)
      zld F_7dc14 D_7dc14 (s - 176) E176. rewrite Z_to_bv_bv_unsigned.           (* [comment removed for export] *)
      zld F_7dc18 D_7dc18 (s - 184) E184. rewrite Z_to_bv_bv_unsigned.           (* [comment removed for export] *)
      zld F_7dc1c D_7dc1c (s - 192) E192. rewrite Z_to_bv_bv_unsigned.           (* [comment removed for export] *)
      zld F_7dc20 D_7dc20 (s - 200) E200. rewrite Z_to_bv_bv_unsigned.           (* [comment removed for export] *)
      zstep F_7dc24 D_7dc24.                                                     (* [comment removed for export] *)
      stepret F_7dc28 D_7dc28 (Z_to_bv 64 0x7fe6c : word) ltac:(rwH; reflexivity).
      replace (s - 208 + 64) with (s - 144) by lia.
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (E136 : cellA X (s - 136) 8 0) by zcell end.
      zld F_7fe6c D_7fe6c (s - 136) E136.                                        (* [comment removed for export] *)
      zsw F_7fe70 D_7fe70 (nd + 12) (TF + 1) ltac:(apply wok_Wn; apply wok_Wn; exact WND4).   (* [comment removed for export] *)
      zbft F_7fe74 D_7fe74.                                                      (* [comment removed for export] *)
      match goal with |- msteps _ (mkst _ _ ?X _) _ =>
        assert (E120 : cellA X (s - 120) 8 0x80350) by zcell; assert (E128 : cellA X (s - 128) 8 (U (getr regs 8))) by zcell end.
      zld F_7fe78 D_7fe78 (s - 120) E120.                                        (* [comment removed for export] *)
      zld F_7fe7c D_7fe7c (s - 128) E128. rewrite Z_to_bv_bv_unsigned.           (* [comment removed for export] *)
      zstep F_7fe80 D_7fe80.                                                     (* [comment removed for export] *)
      stepret F_7fe84 D_7fe84 (Z_to_bv 64 0x80350 : word) ltac:(rwH; reflexivity).
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
