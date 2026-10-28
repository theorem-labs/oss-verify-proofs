(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.GcFlush06.  (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib
     ArtMem ArtRegs ArtAtomics ArtTac RefMemcpyLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatPoison_b Ba0RegionPoisoned_b Ba0FakeStack1_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_5de44_5def8_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Ltac lit_cell H :=
  unfold cell in H;
  match type of H with rdn _ _ (Z_to_bv 64 ?a) _ = _ =>
    match goal with |- rdn _ _ ?w _ = _ => replace w with (Z_to_bv 64 a : word) by (apply bv_eq; reflexivity); exact H end end.

Definition SF5W : Z := 0xf5f5f5f5f5f5f5f5.
(* [comment removed for export] *)
Definition sf5_frame (M : word -> option byte) (sp ra s0 : Z) : word -> option byte := Wn 8 (Wn 8 M (sp - 8) ra) (sp - 16) s0.
(* [comment removed for export] *)
Fixpoint sf5_fill (M : word -> option byte) (a : Z) (k : nat) : word -> option byte :=
  match k with O => M | S k' => Wn 8 (sf5_fill M a k') (a + 8 * Z.of_nat k') SF5W end.

Lemma sf5_word_bytes : word_to_le_bytes 8 (Z_to_bv 64 SF5W) = repeat (Z_to_bv 8 245) 8.
Proof.
  unfold SF5W. cbn [repeat]. unfold word_to_le_bytes.
  repeat (first [apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|] | reflexivity | progress cbn -[Z_to_bv bv_unsigned]]).
Qed.
Lemma sf5_fill_grows : forall M a k, mem_grows M (sf5_fill M a k).
Proof. intros M a k. induction k as [|k IH]; [apply mem_grows_refl|]. cbn [sf5_fill]. eapply mem_grows_trans; [exact IH|apply Wn_grows]. Qed.
Lemma sf5_fill_outside : forall M a k (x : word), 0 <= a -> a + 8 * Z.of_nat k < 2 ^ 64 -> ~ (a <= U x < a + 8 * Z.of_nat k) -> sf5_fill M a k x = M x.
Proof.
  intros M a k x Ha Hk Hx. induction k as [|k IH]; [reflexivity|]. cbn [sf5_fill].
  rewrite Wn_outside by (cbn; lia). apply IH; lia.
Qed.
Lemma sf5_fill_inside : forall M a k j, 0 <= a -> a + 8 * Z.of_nat k < 2 ^ 64 -> 0 <= j < 8 * Z.of_nat k ->
  sf5_fill M a k (Z_to_bv 64 (a + j)) = Some (Z_to_bv 8 245).
Proof.
  intros M a k j Ha Hk Hj. induction k as [|k IH]; [cbn in Hj; lia|]. cbn [sf5_fill].
  destruct (Z_lt_le_dec j (8 * Z.of_nat k)) as [Lt|Ge].
  - rewrite Wn_outside by (rewrite ?art_u_lit by lia; cbn; lia). apply IH; lia.
  - unfold Wn. rewrite sf5_word_bytes.
    replace (a + j) with ((a + 8 * Z.of_nat k) + (j - 8 * Z.of_nat k)) by lia.
    pose proof (Wf_inside (sf5_fill M a k) (a + 8 * Z.of_nat k) 8 245 (j - 8 * Z.of_nat k) ltac:(lia) ltac:(lia) ltac:(lia)) as W. unfold Wf in W. exact W.
Qed.
Lemma sf5_fill_wr : forall M a k b m, wrA M b m -> wrA (sf5_fill M a k) b m.
Proof. intros M a k b m W. eapply wr_grows; [apply sf5_fill_grows|exact W]. Qed.
Lemma sf5_fill_cell : forall M a k b m v, 0 <= a -> a + 8 * Z.of_nat k < 2 ^ 64 -> 0 <= b -> b + Z.of_nat m < 2 ^ 64 ->
  apart a (8 * Z.of_nat k) b (Z.of_nat m) -> cellA M b m v -> cellA (sf5_fill M a k) b m v.
Proof.
  intros M a k b m v Ha Hk Hb Hm Hap C. induction k as [|k IH]; [exact C|]. cbn [sf5_fill].
  apply cell_Wn_other; [lia|lia|lia|lia| |apply IH; [lia|unfold apart in *; lia]]. unfold apart in *. cbn. lia.
Qed.

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
#[using="Type"] Lemma art_sfree5_pre : forall regs (M rom : word -> option byte) (raw : word) (sp F fl : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 F ->
  16 <= sp -> sp < 2 ^ 63 -> 0 <= F -> F + 2048 < 2 ^ 63 -> 0 <= fl < 2 ^ 63 ->
  wrA M (sp - 16) 16 -> apart (F + 2040) 8 (sp - 16) 16 -> apart fl 1 (sp - 16) 16 ->
  cellA M (F + 2040) 8 fl -> wrA M fl 1 ->
  exists regs', msteps ASEGS (mkst regs (0x5e2e8 : word) M rom) (mkst regs' (0x5e39c : word) (Wn 1 (sf5_frame M sp (U raw) (U (getr regs 8))) fl 0) rom)
    /\ getr regs' 1 = Z_to_bv 64 0x5e304 /\ getr regs' 2 = Z_to_bv 64 (sp - 16) /\ getr regs' 8 = Z_to_bv 64 0 /\ getr regs' 10 = Z_to_bv 64 F
    /\ (forall r : reg, r <> 1%bv -> r <> 2%bv -> r <> 8%bv -> r <> 11%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp F fl H1 H2 H10 Hsp Hsp' HF HF' Hfl W AP1 AP2 CF WF.
  eexists. split.
  { zstep F_5ded0 D_5ded0.
    zsd F_5ded4 D_5ded4 (sp - 8) (U raw) ltac:(rewok W).
    zsd F_5ded8 D_5ded8 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CF' : cellA X (F + 2040) 8 fl) by (unfold apart in *; zcell) end.
    zld F_5dedc D_5dedc (F + 2040) CF'.
    zstep F_5dee0 D_5dee0.
    zsb F_5dee4 D_5dee4 fl 0 ltac:(rewok WF).
    stepn F_5dee8 D_5dee8.
    unfold sf5_frame. apply mst_refl. }
  repeat split; try (gres; reflexivity); try (gres; rwH; first [reflexivity | f_equal; lia]).
  intros r N1 N2 N8 N11. gres. rwH. repeat (rewrite getr_other by (first [exact N1 | exact N2 | exact N8 | exact N11 | symmetry; assumption | reg_neq_tac])). reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_sfree5_post : forall regs (M rom : word -> option byte) (raw : word) (sp SF ra0 s00 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 16) -> getr regs 10 = Z_to_bv 64 SF -> ret_ok raw -> U raw = ra0 ->
  16 <= sp -> sp < 2 ^ 63 -> 0 <= SF -> SF + 256 < 2 ^ 63 -> 0 <= ra0 < 2 ^ 64 -> 0 <= s00 < 2 ^ 64 ->
  cellA M 0x10380 8 SF5W -> wrA M SF 256 -> apart SF 256 (sp - 16) 16 ->
  cellA M (sp - 8) 8 ra0 -> cellA M (sp - 16) 8 s00 ->
  exists regs', msteps ASEGS (mkst regs (0x5e304 : word) M rom) (mkst regs' raw (sf5_fill M SF 32) rom)
    /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 8 = Z_to_bv 64 s00
    /\ (forall r : reg, r <> 1%bv -> r <> 2%bv -> r <> 8%bv -> r <> 11%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp SF ra0 s00 H2 H10 Hret Era Hsp Hsp' HS HS' Hra Hs0 CR WS APS C8 C16.
  eexists. split.
  { zstep F_5deec D_5deec.
    zld F_5def0 D_5def0 0x10380 CR.
    zsd F_5def4 D_5def4 (SF + 0) SF5W ltac:(rewok WS).
    zsd F_5def8 D_5def8 (SF + 8) SF5W ltac:(rewok WS).
    zsd F_5defc D_5defc (SF + 16) SF5W ltac:(rewok WS).
    zsd F_5df00 D_5df00 (SF + 24) SF5W ltac:(rewok WS).
    zsd F_5df04 D_5df04 (SF + 32) SF5W ltac:(rewok WS).
    zsd F_5df08 D_5df08 (SF + 40) SF5W ltac:(rewok WS).
    zsd F_5df0c D_5df0c (SF + 48) SF5W ltac:(rewok WS).
    zsd F_5df10 D_5df10 (SF + 56) SF5W ltac:(rewok WS).
    zsd F_5df14 D_5df14 (SF + 64) SF5W ltac:(rewok WS).
    zsd F_5df18 D_5df18 (SF + 72) SF5W ltac:(rewok WS).
    zsd F_5df1c D_5df1c (SF + 80) SF5W ltac:(rewok WS).
    zsd F_5df20 D_5df20 (SF + 88) SF5W ltac:(rewok WS).
    zsd F_5df24 D_5df24 (SF + 96) SF5W ltac:(rewok WS).
    zsd F_5df28 D_5df28 (SF + 104) SF5W ltac:(rewok WS).
    zsd F_5df2c D_5df2c (SF + 112) SF5W ltac:(rewok WS).
    zsd F_5df30 D_5df30 (SF + 120) SF5W ltac:(rewok WS).
    zsd F_5df34 D_5df34 (SF + 128) SF5W ltac:(rewok WS).
    zsd F_5df38 D_5df38 (SF + 136) SF5W ltac:(rewok WS).
    zsd F_5df3c D_5df3c (SF + 144) SF5W ltac:(rewok WS).
    zsd F_5df40 D_5df40 (SF + 152) SF5W ltac:(rewok WS).
    zsd F_5df44 D_5df44 (SF + 160) SF5W ltac:(rewok WS).
    zsd F_5df48 D_5df48 (SF + 168) SF5W ltac:(rewok WS).
    zsd F_5df4c D_5df4c (SF + 176) SF5W ltac:(rewok WS).
    zsd F_5df50 D_5df50 (SF + 184) SF5W ltac:(rewok WS).
    zsd F_5df54 D_5df54 (SF + 192) SF5W ltac:(rewok WS).
    zsd F_5df58 D_5df58 (SF + 200) SF5W ltac:(rewok WS).
    zsd F_5df5c D_5df5c (SF + 208) SF5W ltac:(rewok WS).
    zsd F_5df60 D_5df60 (SF + 216) SF5W ltac:(rewok WS).
    zsd F_5df64 D_5df64 (SF + 224) SF5W ltac:(rewok WS).
    zsd F_5df68 D_5df68 (SF + 232) SF5W ltac:(rewok WS).
    zsd F_5df6c D_5df6c (SF + 240) SF5W ltac:(rewok WS).
    zsd F_5df70 D_5df70 (SF + 248) SF5W ltac:(rewok WS).
    cbn [sf5_fill Z.of_nat Pos.of_succ_nat].
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (D8 : cellA X (sp - 8) 8 ra0) by (unfold apart in *; zcell); assert (D16 : cellA X (sp - 16) 8 s00) by (unfold apart in *; zcell) end.
    zld F_5df74 D_5df74 (sp - 8) D8. rewrite <- Era, Z_to_bv_bv_unsigned.
    zld F_5df78 D_5df78 (sp - 16) D16.
    zstep F_5df7c D_5df7c.
    stepret F_5df80 D_5df80 raw ltac:(rwH; reflexivity).
    apply mst_refl. }
  repeat split; try (gres; reflexivity); try (gres; rwH; first [reflexivity | f_equal; lia]).
  intros r N1 N2 N8 N11. gres. rwH. repeat (rewrite getr_other by (first [exact N1 | exact N2 | exact N8 | exact N11 | symmetry; assumption | reg_neq_tac])). reflexivity.
Qed.
Lemma art_sf5_ret : ret_ok (Z_to_bv 64 0x5e304).
Proof. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem art_sfree5_run : forall regs (M rom : word -> option byte) (raw : word) (sp F fl : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 F ->
  6905856 + 16 <= sp -> sp < 2 ^ 63 -> in_app F -> 6905856 <= F -> F + 2048 < 2 ^ 63 -> 6905856 <= fl < 2 ^ 63 ->
  wrA M (sp - 16) 16 -> apart (F + 2040) 8 (sp - 16) 16 -> apart fl 1 (sp - 16) 16 ->
  cellA M (F + 2040) 8 fl -> wrA M fl 1 -> art_layout M -> cellA M 0x10380 8 SF5W ->
  wrA M (SB + F / 8) 256 -> apart (SB + F / 8) 256 (sp - 16) 16 -> apart (SB + F / 8) 256 fl 1 ->
  exists regs', msteps ASEGS (mkst regs (0x5e2e8 : word) M rom) (mkst regs' raw (sf5_fill (Wn 1 (sf5_frame M sp (U raw) (U (getr regs 8))) fl 0) (SB + F / 8) 32) rom)
    /\ keeps_cs regs regs'.
Proof.
  intros regs M rom raw sp F fl H1 Hret H2 H10 Hsp Hsp' HA HF HF' Hfl W AP1 AP2 CF WF LAY CR WS APS APF.
  assert (Happ : 0 <= F) by lia.
  destruct (art_sfree5_pre regs M rom raw sp F fl H1 H2 H10 ltac:(lia) Hsp' Happ HF' ltac:(lia) W AP1 AP2 CF WF) as (r1 & RUN1 & P1 & P2 & P8 & P10 & PK).
  set (M1 := Wn 1 (sf5_frame M sp (U raw) (U (getr regs 8))) fl 0) in *.
  assert (C1 : forall a n v, 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> apart a (Z.of_nat n) (sp - 16) 16 -> apart a (Z.of_nat n) fl 1 -> cellA M a n v -> cellA M1 a n v).
  { intros a n v Ha Hn A1 A2 C. unfold M1, sf5_frame.
    apply cell_Wn_other; [lia|lia|lia|lia|unfold apart in *; cbn; lia|].
    apply cell_Wn_other; [lia|lia|lia|lia|unfold apart in *; cbn; lia|].
    apply cell_Wn_other; [lia|lia|lia|lia|unfold apart in *; cbn; lia|]. exact C. }
  assert (LAY1 : art_layout M1).
  { unfold art_layout in *. destruct LAY as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15).
    repeat split; apply C1; first [assumption | cbn; lia | unfold apart; cbn; lia]. }
  assert (GL : rt_layout_globs M1).
  { destruct LAY1 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & _). unfold rt_layout_globs.
    repeat split; [lit_cell A1 | lit_cell A2 | lit_cell A3 | lit_cell A4 | lit_cell A5 | lit_cell A6 | lit_cell A7 | lit_cell A8]. }
  destruct (memtoshadow47_run r1 M1 rom (Z_to_bv 64 0x5e304) F GL HA P10 P1 art_sf5_ret) as (r2 & RUN2 & V10 & K2).
  assert (V2 : getr r2 2 = Z_to_bv 64 (sp - 16)) by (rewrite (K2 2%bv) by (cbv; tauto); exact P2).
  assert (V10' : getr r2 10 = Z_to_bv 64 (SB + F / 8)) by (rewrite V10; f_equal; unfold SB, Ba0RegionPoisoned_b.SB; lia).
  assert (RG : forall r : reg, 0 <= U (getr regs r) < 2 ^ 64) by (intros r; apply bv_unsigned_in_range).
  assert (D8 : cellA M1 (sp - 8) 8 (U raw)).
  { unfold M1, sf5_frame. apply cell_Wn_other; [lia|lia|lia|lia|unfold apart in *; cbn; lia|].
    apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; cbn; lia|]. apply cell_Wn_hit; lia. }
  assert (D16 : cellA M1 (sp - 16) 8 (U (getr regs 8))).
  { unfold M1, sf5_frame. apply cell_Wn_other; [lia|lia|lia|lia|unfold apart in *; cbn; lia|]. apply cell_Wn_hit; lia. }
  assert (CR1 : cellA M1 0x10380 8 SF5W) by (apply C1; [lia|cbn; lia|unfold apart; cbn; lia|unfold apart; cbn; lia|exact CR]).
  assert (WS1 : wrA M1 (SB + F / 8) 256) by (unfold M1, sf5_frame; repeat apply wr_Wn; exact WS).
  assert (Hra : U raw = U raw) by reflexivity.
  destruct (art_sfree5_post r2 M1 rom raw sp (SB + F / 8) (U raw) (U (getr regs 8)) V2 V10' Hret Hra ltac:(lia) Hsp'
              ltac:(unfold SB; pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)); lia)
              ltac:(unfold SB; assert (F / 8 <= 2 ^ 63 / 8) by (apply Z.div_le_mono; lia); change (2 ^ 63 / 8) with (2 ^ 60) in *; lia)
              (bv_unsigned_in_range _ raw) (RG 8%bv) CR1 WS1 APS D8 D16)
    as (r3 & RUN3 & Q1 & Q2 & Q8 & QK).
  exists r3. split.
  { replace (Z_to_bv 64 0x5e304) with (0x5e304%bv : word) in RUN2 by (apply bv_eq; vm_compute; reflexivity).
    eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3. }
  intros r Hr. cbn [callee_saved In] in Hr.
  destruct (decide (r = 1%bv)) as [->|N1]; [rewrite Q1; exact (eq_sym H1)|].
  destruct (decide (r = 2%bv)) as [->|N2]; [rewrite Q2, H2; reflexivity|].
  destruct (decide (r = 8%bv)) as [->|N8]; [rewrite Q8, Z_to_bv_bv_unsigned; reflexivity|].
  assert (N11 : r <> 11%bv) by (intros ->; repeat (destruct Hr as [Hr|Hr]; [apply (f_equal bv_unsigned) in Hr; vm_compute in Hr; discriminate Hr|]); exact Hr).
  rewrite (QK r N1 N2 N8 N11). rewrite (K2 r) by (cbn [callee_saved In]; exact Hr). exact (PK r N1 N2 N8 N11).
Qed.
End FPX.

