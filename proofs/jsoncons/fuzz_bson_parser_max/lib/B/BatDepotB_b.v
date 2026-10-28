(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib RefMemcpyLib
     MemSplit ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatDepotA_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.muslA Require Import Ba0MemcpyBase_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0IntMemcpy_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r7f8f4_7f950_b Ba0_code_r7d5e0_7d838_b Ba0_code_r71154_71230_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
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
  Hypothesis Hs : 0x696000 <= s - 224 /\ s < 2 ^ 64.
  Hypothesis Hl2 : 0x696000 <= l2 /\ l2 + 2 ^ 20 < 2 ^ 64.
  Hypothesis Hnd : l2 + 16 <= nd /\ nd + 16 <= l2 + 2 ^ 20 /\ nd mod 16 = 0.
  Hypothesis Hblk : 0x696000 <= blk /\ blk + 2 ^ 23 < 2 ^ 64 /\ blk mod 8 = 0.
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

  #[using="trp l2 Hs Hl2 Hnd Hblk HTF HST Hsz Htrp Hh A1 A2 A3 A4 Ctrp Cszt CTF Cblk CST RC Wf Wnd Wblk Wsto"] Lemma dp_store_run : forall regs,
    getr regs 10 = Z_to_bv 64 nd -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 (s - 104) -> getr regs 13 = Z_to_bv 64 h ->
    getr regs 1 = (0x9a1ec : word)%bv -> getr regs 2 = Z_to_bv 64 (s - 112) ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x99cdc : word) M rom) (mkst regs' (0x9a1ec : word)%bv M' rom)
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
      msteps ASEGS (mkst regs (0x99cdc : word) M rom) (mkst r1 (0x97aec : word) X1 rom)
      /\ X1 = Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M
               (s - 120) (U (0x9a1ec : word)%bv)) (s - 128) (U (getr regs 8))) nd h) (s - 136) 0)
               (s - 152) (U (0x99d08 : word)%bv)) (s - 160) nd) (s - 168) (U (getr regs 9))) (s - 176) (U (getr regs 18))) (s - 184) (U (getr regs 19)))
               (s - 192) (U (getr regs 20))) (s - 200) (U (getr regs 21))) (s - 208) 0) (s - 136) 0
      /\ getr r1 10 = Z_to_bv 64 2169608 /\ getr r1 11 = Z_to_bv 64 (size + 1) /\ getr r1 12 = Z_to_bv 64 (s - 208) /\ getr r1 13 = Z_to_bv 64 (s - 136)
      /\ getr r1 1 = Z_to_bv 64 0x97a40 /\ getr r1 2 = Z_to_bv 64 (s - 208)
      /\ getr r1 8 = Z_to_bv 64 (s - 136) /\ getr r1 9 = Z_to_bv 64 2169608 /\ getr r1 18 = Z_to_bv 64 (size + 1) /\ getr r1 19 = Z_to_bv 64 (s - 104)
      /\ getr r1 20 = Z_to_bv 64 size /\ getr r1 21 = Z_to_bv 64 0
      /\ (forall r : reg, In r [3; 4; 22; 23; 24; 25; 26; 27]%bv -> getr r1 r = getr regs r)).
    { eexists _, _. split; [|split; [reflexivity|]].
      - zstep F_998c4 D_998c4.                                                   (* [comment removed for export] *)
        zsd F_998c8 D_998c8 (s - 120) (U (0x9a1ec : word)%bv) ltac:(rewok Wf).         (* [comment removed for export] *)
        zsd F_998cc D_998cc (s - 128) (U (getr regs 8)) ltac:(rewok Wf).            (* [comment removed for export] *)
        zstep F_998d0 D_998d0.                                                   (* [comment removed for export] *)
        zstep F_998d4 D_998d4.                                                   (* [comment removed for export] *)
        zsd F_998d8 D_998d8 nd h ltac:(rewok Wnd).                                  (* [comment removed for export] *)
        zsd F_998dc D_998dc (s - 136) 0 ltac:(rewok Wf).                            (* [comment removed for export] *)
        stepn F_998e0 D_998e0.                                                   (* [comment removed for export] *)
        stepn F_998e4 D_998e4.                                                   (* [comment removed for export] *)
        zstep F_998e8 D_998e8.                                                   (* [comment removed for export] *)
        stepn F_998ec D_998ec.                                                   (* [comment removed for export] *)
        zstep F_975b0 D_975b0.                                                   (* [comment removed for export] *)
        zsd F_975b4 D_975b4 (s - 152) (U (0x99d08 : word)%bv) ltac:(rewok Wf).         (* [comment removed for export] *)
        zsd F_975b8 D_975b8 (s - 160) nd ltac:(rewok Wf).                           (* [comment removed for export] *)
        zsd F_975bc D_975bc (s - 168) (U (getr regs 9)) ltac:(rewok Wf).            (* [comment removed for export] *)
        zsd F_975c0 D_975c0 (s - 176) (U (getr regs 18)) ltac:(rewok Wf).           (* [comment removed for export] *)
        zsd F_975c4 D_975c4 (s - 184) (U (getr regs 19)) ltac:(rewok Wf).           (* [comment removed for export] *)
        zsd F_975c8 D_975c8 (s - 192) (U (getr regs 20)) ltac:(rewok Wf).           (* [comment removed for export] *)
        zsd F_975cc D_975cc (s - 200) (U (getr regs 21)) ltac:(rewok Wf).           (* [comment removed for export] *)
        zstep F_975d0 D_975d0.                                                   (* [comment removed for export] *)
        match goal with |- msteps _ (mkst _ _ ?X _) _ =>
          assert (Q1 : cellA X (s - 96) 4 size) by zcell; assert (Q2 : cellA X (s - 92) 4 0) by zcell end.
        zlw F_975d4 D_975d4 (s - 96) Q1.                                         (* [comment removed for export] *)
        zlw F_975d8 D_975d8 (s - 92) Q2.                                         (* [comment removed for export] *)
        stepn F_975dc D_975dc. rwH. rewrite art_zb_or by lia. rewrite Z.lor_0_r.  (* [comment removed for export] *)
        zbtk F_975e0 D_975e0.                                                    (* [comment removed for export] *)
        zstep F_975ec D_975ec.                                                   (* [comment removed for export] *)
        zstep F_975f0 D_975f0.                                                   (* [comment removed for export] *)
        zbft F_975f4 D_975f4.                                                    (* [comment removed for export] *)
        zstep F_975f8 D_975f8.                                                   (* [comment removed for export] *)
        zstep F_975fc D_975fc.                                                   (* [comment removed for export] *)
        zbtk F_97600 D_97600.                                                    (* [comment removed for export] *)
        zsd F_97608 D_97608 (s - 208) 0 ltac:(rewok Wf).                            (* [comment removed for export] *)
        zsd F_9760c D_9760c (s - 136) 0 ltac:(rewok Wf).                            (* [comment removed for export] *)
        zstep F_97610 D_97610.                                                   (* [comment removed for export] *)
        zstep F_97614 D_97614.                                                   (* [comment removed for export] *)
        zstep F_97618 D_97618.                                                   (* [comment removed for export] *)
        zstep F_9761c D_9761c.                                                   (* [comment removed for export] *)
        zstep F_97620 D_97620.                                                   (* [comment removed for export] *)
        stepn F_97624 D_97624.                                                   (* [comment removed for export] *)
        replace (s - 112 - 32 - 64) with (s - 208) by lia. replace (s - 112 - 32 + 8) with (s - 136) by lia.
        apply mst_refl.
      - do 12 (split; [kept_solve|]). intros r Hr. cbv in Hr.
        destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; kept_solve. }
    destruct S1 as (r1 & X1 & RUN1 & EX1 & Q10 & Q11 & Q12 & Q13 & Q1 & Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & K1).
    (* [comment removed for export] *)
    assert (S2 : exists r2 X2,
      msteps ASEGS (mkst r1 (0x97aec : word) X1 rom) (mkst r2 (0x97a40 : word) X2 rom)
      /\ X2 = Wn 8 (Wn 8 (Wn 8 (Wn 8 X1 (s - 216) 0x97a40) (s - 224) (s - 136)) 2169608 (TF + (size + 1))) (s - 208) TF
      /\ getr r2 10 = Z_to_bv 64 (blk + 8 * TF) /\ getr r2 2 = Z_to_bv 64 (s - 208) /\ getr r2 8 = Z_to_bv 64 (s - 136)
      /\ getr r2 9 = Z_to_bv 64 2169608 /\ getr r2 18 = Z_to_bv 64 (size + 1) /\ getr r2 19 = Z_to_bv 64 (s - 104) /\ getr r2 20 = Z_to_bv 64 size /\ getr r2 21 = Z_to_bv 64 0
      /\ (forall r : reg, In r [3; 4; 22; 23; 24; 25; 26; 27]%bv -> getr r2 r = getr regs r)).
    { subst X1.
      match goal with |- exists r2 X2, msteps _ (mkst _ _ ?X _) _ /\ _ =>
        assert (CTF1 : cellA X 2169608 8 TF) by zcell; assert (Cblk1 : cellA X (2169608 + 16) 8 blk) by zcell end.
      pose proof (Z.div_small TF (2 ^ 20) ltac:(lia)) as DT0. pose proof (Z.div_small (size + TF) (2 ^ 20) ltac:(lia)) as DT1.
      pose proof (Z.div_small TF (2 ^ 32) ltac:(lia)) as DT2.
      eexists _, _. split; [|split; [reflexivity|]].
      - zstep F_976d4 D_976d4.                                                   (* [comment removed for export] *)
        zsd F_976d8 D_976d8 (s - 216) 0x97a40 ltac:(rewok Wf).                      (* [comment removed for export] *)
        zsd F_976dc D_976dc (s - 224) (s - 136) ltac:(rewok Wf).                    (* [comment removed for export] *)
        zstep F_976e0 D_976e0.                                                   (* [comment removed for export] *)
        zstep F_976e4 D_976e4.                                                   (* [comment removed for export] *)
        match goal with |- msteps _ (mkst _ _ ?X _) _ =>
          assert (CTF2 : cellA X 2169608 8 TF) by zcell; assert (WTF2 : wokA X 2169608 8) by (rewok Wsto) end.
        chain_step; [reflexivity
          | eapply (art_step_amoadd_d_rd _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 2169608) (Z_to_bv 64 (size + 1)) (Z_to_bv 64 TF));
            [ exact F_976e8 | reflexivity | exact D_976e8 | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; reflexivity
            | exact CTF2 | apply bytes_le_to_Z_8 | gres; rwH; reflexivity | exact WTF2 ]
          | ]. wpc. rewrite art_zb_add.                                         (* [comment removed for export] *)
        change (wbytes ?M0 (Z_to_bv 64 2169608) (word_to_le_bytes 8 (Z_to_bv 64 (TF + (size + 1))))) with (Wn 8 M0 2169608 (TF + (size + 1))).
        zstep F_976ec D_976ec.                                                   (* [comment removed for export] *)
        stepn F_976f0 D_976f0. rwH. rewrite art_zb_srli by lia. rewrite DT0.     (* [comment removed for export] *)
        zstep F_976f4 D_976f4.                                                   (* [comment removed for export] *)
        replace (size + 1 + -1 + TF) with (size + TF) by lia.
        stepn F_976f8 D_976f8. rwH. rewrite art_zb_srli by lia. rewrite DT1.     (* [comment removed for export] *)
        zbft F_976fc D_976fc.                                                    (* [comment removed for export] *)
        stepn F_97700 D_97700. rwH. rewrite art_zb_srli by lia. rewrite DT2.     (* [comment removed for export] *)
        zbtk F_97704 D_97704.                                                    (* [comment removed for export] *)
        zsd F_9771c D_9771c (s - 208) TF ltac:(rewok Wf).                           (* [comment removed for export] *)
        zstep F_97720 D_97720.                                                   (* [comment removed for export] *)
        zstep F_97724 D_97724.                                                   (* [comment removed for export] *)
        match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cblk3 : cellA X (2169608 + 16) 8 blk) by zcell end.
        zld F_97728 D_97728 (2169608 + 16) Cblk3.                                (* [comment removed for export] *)
        zbft F_9772c D_9772c.                                                    (* [comment removed for export] *)
        zstep F_97730 D_97730.                                                   (* [comment removed for export] *)
        stepn F_97734 D_97734. rwH. rewrite (art_zb_srli_exact (TF * 2 ^ 44) 41 (8 * TF)) by lia.   (* [comment removed for export] *)
        zstep F_97738 D_97738.                                                   (* [comment removed for export] *)
        match goal with |- msteps _ (mkst _ _ ?X _) _ =>
          assert (Lra : cellA X (s - 216) 8 0x97a40) by zcell; assert (Ls0 : cellA X (s - 224) 8 (s - 136)) by zcell end.
        zld F_9773c D_9773c (s - 216) Lra.                                       (* [comment removed for export] *)
        zld F_97740 D_97740 (s - 224) Ls0.                                       (* [comment removed for export] *)
        zstep F_97744 D_97744.                                                   (* [comment removed for export] *)
        stepret F_97748 D_97748 (Z_to_bv 64 0x97a40 : word) ltac:(rwH; reflexivity).
        first [apply mst_refl | replace (s - 224 + 16) with (s - 208) by lia; apply mst_refl | replace (s - 208 + -16 + 16) with (s - 208) by lia; apply mst_refl].
      - do 8 (split; [kept_solve|]). intros r Hr. rewrite <- (K1 r Hr). cbv in Hr.
        destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; kept_solve. }
    destruct S2 as (r2 & X2 & RUN2 & EX2 & P10 & P2 & P8 & P9 & P18 & P19 & P20 & P21 & K2).
    (* [comment removed for export] *)
    assert (S3 : exists r3 X3,
      msteps ASEGS (mkst r2 (0x97a40 : word) X2 rom) (mkst r3 (0x8b3e4 : word) X3 rom)
      /\ X3 = Wn 8 X2 (blk + 8 * TF) size
      /\ getr r3 10 = Z_to_bv 64 (blk + 8 * TF + 8) /\ getr r3 11 = Z_to_bv 64 trp /\ getr r3 12 = Z_to_bv 64 (8 * size) /\ getr r3 1 = Z_to_bv 64 0x97a60
      /\ getr r3 2 = Z_to_bv 64 (s - 208) /\ getr r3 8 = Z_to_bv 64 (s - 136) /\ getr r3 9 = Z_to_bv 64 2169608 /\ getr r3 18 = Z_to_bv 64 (size + 1)
      /\ (forall r : reg, In r [3; 4; 22; 23; 24; 25; 26; 27]%bv -> getr r3 r = getr regs r)).
    { subst X2 X1.
      match goal with |- exists r3 X3, msteps _ (mkst _ _ ?X _) _ /\ _ => assert (Ctrp2 : cellA X (s - 104) 8 trp) by zcell end.
      eexists _, _. split; [|split; [reflexivity|]].
      - zbft F_97628 D_97628.                                                    (* [comment removed for export] *)
        stepn F_9762c D_9762c. rwH.                                              (* [comment removed for export] *)
        match goal with |- context [v_slliw (Z_to_bv 64 0) ?k] => replace (v_slliw (Z_to_bv 64 0) k) with (Z_to_bv 64 0 : word) by (apply bv_eq; vm_compute; reflexivity) end.
        zld F_97630 D_97630 (s - 104) Ctrp2.                                     (* [comment removed for export] *)
        stepn F_97634 D_97634. rwH. rewrite art_zb_or by lia. rewrite Z.lor_0_l. (* [comment removed for export] *)
        zsd F_97638 D_97638 (blk + 8 * TF) size ltac:(rewok Wblk).                  (* [comment removed for export] *)
        zstep F_9763c D_9763c.                                                   (* [comment removed for export] *)
        zstep F_97640 D_97640.                                                   (* [comment removed for export] *)
        stepn F_97644 D_97644.                                                   (* [comment removed for export] *)
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
    destruct (int_memcpy_run X3 (Z_to_bv 64 (blk + 8 * TF + 8)) (Z_to_bv 64 trp) (8 * size) bs rom MCH r3 (Z_to_bv 64 0x97a60 : word)
                ltac:(unfold ret_ok; apply bv_eq; vm_compute; reflexivity) Q1' Q10' Q11' Q12') as (r4 & RUN4 & K4).
    set (X4 := wbytes X3 (Z_to_bv 64 (blk + 8 * TF + 8)) bs) in RUN4.
    assert (V2 : getr r4 2 = Z_to_bv 64 (s - 208)) by (rewrite (K4 2%bv) by (cbv; tauto); exact Q2').
    assert (V8 : getr r4 8 = Z_to_bv 64 (s - 136)) by (rewrite (K4 8%bv) by (cbv; tauto); exact Q8').
    assert (V9 : getr r4 9 = Z_to_bv 64 2169608) by (rewrite (K4 9%bv) by (cbv; tauto); exact Q9').
    assert (V18 : getr r4 18 = Z_to_bv 64 (size + 1)) by (rewrite (K4 18%bv) by (cbv; tauto); exact Q18').
    assert (V1 : getr r4 1 = Z_to_bv 64 0x97a60) by (rewrite (K4 1%bv) by (cbv; tauto); exact Q1').
    (* [comment removed for export] *)
    subst X3 X2 X1.
    assert (C208 : cellA X4 (s - 208) 8 TF) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    pose proof (cell8_lo _ _ _ C208) as C208w.
    assert (CSTw : cellA X4 (2169608 + 24) 4 ST) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C136 : cellA X4 (s - 136) 8 0) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C152 : cellA X4 (s - 152) 8 0x99d08) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C160 : cellA X4 (s - 160) 8 nd) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C168 : cellA X4 (s - 168) 8 (U (getr regs 9))) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C176 : cellA X4 (s - 176) 8 (U (getr regs 18))) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C184 : cellA X4 (s - 184) 8 (U (getr regs 19))) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C192 : cellA X4 (s - 192) 8 (U (getr regs 20))) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C200 : cellA X4 (s - 200) 8 (U (getr regs 21))) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C120 : cellA X4 (s - 120) 8 0x9a1ec) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (C128 : cellA X4 (s - 128) 8 (U (getr regs 8))) by (unfold X4; apply cell_wb_other; [lia | rewrite Lbs; lia | lia | cbn; lia | rewrite Lbs; unfold apart in A2 |- *; cbn; lia | zcell]).
    assert (WST4 : wokA X4 (2169608 + 24) 4) by (unfold X4; apply wok_wb; rewok Wsto).
    assert (WND4 : wokA X4 (nd + 12) 4) by (unfold X4; apply wok_wb; rewok Wnd).
    assert (W136 : wokA X4 (s - 136) 8) by (unfold X4; apply wok_wb; rewok Wf).
    pose proof (Z.div_pos TF (2 ^ 16) ltac:(lia) ltac:(lia)) as D16. pose proof (Z.div_lt_upper_bound TF (2 ^ 16) 16 ltac:(lia) ltac:(lia)) as D16'.
    pose proof (lxor_pow20_nz (size + 1 + ST) ltac:(lia)) as LX.
    (* [comment removed for export] *)
    eexists _, (Wn 4 (Wn 8 (Wn 4 X4 (2169608 + 24) (ST + (size + 1))) (s - 136) 0) (nd + 12) (TF + 1)).
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|].
      zld F_97648 D_97648 (s - 208) C208.                                        (* [comment removed for export] *)
      stepn F_9764c D_9764c. rwH. rewrite art_zb_srli by lia.                    (* [comment removed for export] *)
      stepn F_97650 D_97650. rwH. unfold v_andi. rewrite art_u_lit by lia. change (bv_wrap 64 (-16)) with 18446744073709551600.
      rewrite land_high_mask_0 by lia.                                           (* [comment removed for export] *)
      zstep F_97654 D_97654.                                                     (* [comment removed for export] *)
      zstep F_97658 D_97658.                                                     (* [comment removed for export] *)
      replace (2169608 + 0 + 24) with (2169608 + 24) by lia.
      chain_step; [reflexivity
        | eapply (art_step_amoadd_w_rd _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (2169608 + 24)) (Z_to_bv 64 (size + 1)) (Z_to_bv 64 ST));
          [ exact F_9765c | reflexivity | exact D_9765c | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; reflexivity
          | exact CSTw | apply art_bytes4; lia | rewrite art_u_lit by lia; lia | gres; rwH; reflexivity | exact WST4 ]
        | ]. wpc. rewrite art_zb_add. rewrite art_v_lw_small by lia.              (* [comment removed for export] *)
      change (wbytes ?M0 (Z_to_bv 64 (2169608 + 24)) (word_to_le_bytes 4 (Z_to_bv 64 (ST + (size + 1))))) with (Wn 4 M0 (2169608 + 24) (ST + (size + 1))).
      stepn F_97660 D_97660.                                                     (* [comment removed for export] *)
      zstep F_97664 D_97664.                                                     (* [comment removed for export] *)
      stepn F_97668 D_97668. rwH. rewrite (art_zb_srli_exact (ST * 2 ^ 32) 32 ST) by lia.   (* [comment removed for export] *)
      zstep F_9766c D_9766c.                                                     (* [comment removed for export] *)
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C136a : cellA X (s - 136) 8 0) by zcell end.
      zld F_97670 D_97670 (s - 136) C136a.                                       (* [comment removed for export] *)
      stepn F_97674 D_97674. rwH.                                                (* [comment removed for export] *)
      match goal with |- context [v_xor (Z_to_bv 64 (size + 1 + ST)) ?L] =>
        replace (v_xor (Z_to_bv 64 (size + 1 + ST)) L) with (Z_to_bv 64 (Z.lxor (size + 1 + ST) (2 ^ 20)) : word)
          by (symmetry; replace L with (Z_to_bv 64 (2 ^ 20) : word) by (apply bv_eq; vm_compute; reflexivity); apply art_zb_xor; lia) end.
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C208a : cellA X (s - 208) 4 TF) by zcell end.
      zlw F_97678 D_97678 (s - 208) C208a.                                       (* [comment removed for export] *)
      stepn F_9767c D_9767c. rwH. rewrite art_zb_sltiu by lia.
      replace (if Z.lxor (size + 1 + ST) (2 ^ 20) <? 1 then 1 else 0) with 0 by (destruct (Z.ltb_spec (Z.lxor (size + 1 + ST) (2 ^ 20)) 1); lia).   (* [comment removed for export] *)
      zstep F_97680 D_97680.                                                     (* [comment removed for export] *)
      zsd F_97684 D_97684 (s - 136) 0 ltac:(apply wok_Wn; exact W136).            (* [comment removed for export] *)
      stepn F_97688 D_97688. rwH. unfold v_addiw. rewrite art_u_lit by lia.
      replace (bv_swrap 32 (TF + 1)) with (TF + 1) by (unfold bv_swrap, bv_wrap; change (bv_half_modulus 32) with (2 ^ 31); change (bv_modulus 32) with (2 ^ 32); rewrite Z.mod_small; lia).   (* [comment removed for export] *)
      match goal with |- msteps _ (mkst _ _ ?X _) _ =>
        assert (E152 : cellA X (s - 152) 8 0x99d08) by zcell; assert (E160 : cellA X (s - 160) 8 nd) by zcell;
        assert (E168 : cellA X (s - 168) 8 (U (getr regs 9))) by zcell; assert (E176 : cellA X (s - 176) 8 (U (getr regs 18))) by zcell;
        assert (E184 : cellA X (s - 184) 8 (U (getr regs 19))) by zcell; assert (E192 : cellA X (s - 192) 8 (U (getr regs 20))) by zcell;
        assert (E200 : cellA X (s - 200) 8 (U (getr regs 21))) by zcell end.
      zld F_9768c D_9768c (s - 152) E152.                                        (* [comment removed for export] *)
      zld F_97690 D_97690 (s - 160) E160.                                        (* [comment removed for export] *)
      zld F_97694 D_97694 (s - 168) E168. rewrite Z_to_bv_bv_unsigned.           (* [comment removed for export] *)
      zld F_97698 D_97698 (s - 176) E176. rewrite Z_to_bv_bv_unsigned.           (* [comment removed for export] *)
      zld F_9769c D_9769c (s - 184) E184. rewrite Z_to_bv_bv_unsigned.           (* [comment removed for export] *)
      zld F_976a0 D_976a0 (s - 192) E192. rewrite Z_to_bv_bv_unsigned.           (* [comment removed for export] *)
      zld F_976a4 D_976a4 (s - 200) E200. rewrite Z_to_bv_bv_unsigned.           (* [comment removed for export] *)
      zstep F_976a8 D_976a8.                                                     (* [comment removed for export] *)
      stepret F_976ac D_976ac (Z_to_bv 64 0x99d08 : word) ltac:(rwH; reflexivity).
      replace (s - 208 + 64) with (s - 144) by lia.
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (E136 : cellA X (s - 136) 8 0) by zcell end.
      zld F_998f0 D_998f0 (s - 136) E136.                                        (* [comment removed for export] *)
      zsw F_998f4 D_998f4 (nd + 12) (TF + 1) ltac:(apply wok_Wn; apply wok_Wn; exact WND4).   (* [comment removed for export] *)
      zbft F_998f8 D_998f8.                                                      (* [comment removed for export] *)
      match goal with |- msteps _ (mkst _ _ ?X _) _ =>
        assert (E120 : cellA X (s - 120) 8 0x9a1ec) by zcell; assert (E128 : cellA X (s - 128) 8 (U (getr regs 8))) by zcell end.
      zld F_998fc D_998fc (s - 120) E120.                                        (* [comment removed for export] *)
      zld F_99900 D_99900 (s - 128) E128. rewrite Z_to_bv_bv_unsigned.           (* [comment removed for export] *)
      zstep F_99904 D_99904.                                                     (* [comment removed for export] *)
      stepret F_99908 D_99908 (Z_to_bv 64 0x9a1ec : word) ltac:(rwH; reflexivity).
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
