(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmLayout_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop Require Import TopKit_u TopKit2_u TopSpecs_u TopSpecs2_u ReadKit_u ChunkKit_u SbufCtorStretch_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module SBC.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Lemma ra_ok_lit : forall z, (0 <=? z) && (z <? 2 ^ 47) && (z mod 2 =? 0) = true -> L5.ra_ok z.
Proof. intros z H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.eqb_eq in H3. split; [lia | exact H3]. Qed.
Lemma al8_add : forall a k, a mod 8 = 0 -> k mod 8 = 0 -> (a + k) mod 8 = 0.
Proof. intros a k H1 H2. apply Z.mod_divide; [lia|]. apply Z.divide_add_r; apply Z.mod_divide; try lia; assumption. Qed.
Lemma land1_odd_low : forall w, Z.testbit w 0 = true -> Z.land (w mod 256) 1 = 1.
Proof.
  intros w H. change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. change (2 ^ 1) with 2. rewrite <- Z.bit0_mod.
  change 256 with (2 ^ 8). rewrite Z.mod_pow2_bits_low by lia. rewrite H. reflexivity.
Qed.
Lemma land1_even : forall k, Z.land (2 * k) 1 = 0.
Proof. intros k. change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. change (2 ^ 1) with 2. rewrite Z.mul_comm. apply Z.mod_mul. lia. Qed.

Lemma bytes_at_of_rdn : forall (M : mem) (s : list Z) p, 0 <= p -> p + Z.of_nat (length s) <= 2 ^ 64 ->
  rdn RSEGS M (Z_to_bv 64 p) (length s) = Some (map (Z_to_bv 8) s) -> L5.bytes_at RSEGS M p s.
Proof.
  intros M s. induction s as [|b s IH]; intros p Hp Hn HR i Hi; [cbn in Hi; lia|].
  cbn [length map] in Hn, HR. cbn [rdn] in HR.
  destruct (match M (Z_to_bv 64 p) with Some b0 => Some b0 | None => seg_rom RSEGS (Z_to_bv 64 p) end) as [b0|] eqn:E0; [|discriminate].
  rewrite (L5C.add1_lit p) in HR.
  destruct (rdn RSEGS M (Z_to_bv 64 (p + 1)) (length s)) as [rest|] eqn:ER; [|discriminate].
  injection HR as E1 E2. subst b0 rest.
  destruct i as [|i].
  - cbn [nth]. unfold L5.u8_at. rewrite Z.add_0_r. cbn [rdn]. rewrite E0. reflexivity.
  - cbn [nth]. replace (p + Z.of_nat (S i)) with (p + 1 + Z.of_nat i) by lia. apply (IH (p + 1)); [lia | lia | exact ER | cbn [length] in Hi; lia].
Qed.

Lemma copied_bytes : forall (M : mem) (s : list Z) dst, 0 <= dst < 2 ^ 64 -> dst + Z.of_nat (length s) <= 2 ^ 64 -> L5.bytes_at RSEGS (wbytes M (Z_to_bv 64 dst) (map (Z_to_bv 8) s)) dst s.
Proof.
  intros M s dst Hd Hn. apply bytes_at_of_rdn; [lia | exact Hn|].
  rewrite <- (length_map (Z_to_bv 8) s) at 1. apply SeqExec.rdn_wbytes_hit. rewrite length_map, u64_of_Z by lia. exact Hn.
Qed.
Lemma u8_inj : forall (M : mem) a x y, L5.u8_at RSEGS M a x -> L5.u8_at RSEGS M a y -> 0 <= x < 256 -> 0 <= y < 256 -> x = y.
Proof.
  intros M a x y Hx Hy Rx Ry. unfold L5.u8_at in *. rewrite Hx in Hy.
  assert (E : Z_to_bv 8 x = Z_to_bv 8 y) by congruence. pose proof (f_equal bv_unsigned E) as E'.
  rewrite !Z_to_bv_unsigned in E'. unfold bv_wrap in E'. change (bv_modulus 8) with 256 in E'. rewrite !Z.mod_small in E' by lia. exact E'.
Qed.

Lemma rp_final4 : forall R0 R' : bvmap 5 word, getr R' 2%bv = getr R0 2%bv -> SBS.same_s04 R0 R' -> TK.keepsR SBS.KO5 R0 R' -> regs_preserved R0 R'.
Proof.
  intros R0 R' H2 (Q8 & Q9 & Q18 & Q19 & Q20) HK. apply CK.rp_of_keeps; [exact H2|]. intros q Hq. unfold CK.CSR in Hq. cbn [In] in Hq.
  assert (QQ : forall m : nat, m = ridx q -> q = Z_to_bv 5 (Z.of_nat m)) by (intros m ->; symmetry; apply ridx_roundtrip).
  assert (HK' : In (ridx q) SBS.KO5 -> getr R' q = getr R0 q) by (apply HK). unfold SBS.KO5 in HK'. cbn [In] in HK'.
  destruct Hq as [Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|Hq]]]]]]]]]];
    [apply HK'; tauto | apply HK'; tauto | rewrite (QQ _ Hq); exact Q8 | rewrite (QQ _ Hq); exact Q9 | rewrite (QQ _ Hq); exact Q18 | rewrite (QQ _ Hq); exact Q19 | rewrite (QQ _ Hq); exact Q20
    | apply HK'; tauto | apply HK'; tauto | apply HK'; tauto | apply HK'; tauto].
Qed.
Lemma rp_final5 : forall R0 R' : bvmap 5 word, getr R' 2%bv = getr R0 2%bv -> SBS.same_s05 R0 R' -> TK.keepsR SBS.KO6 R0 R' -> regs_preserved R0 R'.
Proof.
  intros R0 R' H2 (Q8 & Q9 & Q18 & Q19 & Q20 & Q21) HK. apply CK.rp_of_keeps; [exact H2|]. intros q Hq. unfold CK.CSR in Hq. cbn [In] in Hq.
  assert (QQ : forall m : nat, m = ridx q -> q = Z_to_bv 5 (Z.of_nat m)) by (intros m ->; symmetry; apply ridx_roundtrip).
  assert (HK' : In (ridx q) SBS.KO6 -> getr R' q = getr R0 q) by (apply HK). unfold SBS.KO6 in HK'. cbn [In] in HK'.
  destruct Hq as [Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|Hq]]]]]]]]]];
    [apply HK'; tauto | apply HK'; tauto | rewrite (QQ _ Hq); exact Q8 | rewrite (QQ _ Hq); exact Q9 | rewrite (QQ _ Hq); exact Q18 | rewrite (QQ _ Hq); exact Q19 | rewrite (QQ _ Hq); exact Q20
    | rewrite (QQ _ Hq); exact Q21 | apply HK'; tauto | apply HK'; tauto | apply HK'; tauto].
Qed.
Lemma ko_rp : forall qs R R', regs_preserved R R' -> forallb (fun q => existsb (Nat.eqb q) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat) qs = true -> TK.keepsR qs R R'.
Proof.
  intros qs R R' RP Hqs. apply TK.keepsR_preserved; [exact RP|]. intros q Hq. rewrite forallb_forall in Hqs. specialize (Hqs _ Hq). apply existsb_exists in Hqs as (x & Hx & E).
  apply Nat.eqb_eq in E. subst x. unfold callee_saved_idx. cbn [In] in *. intuition (subst; cbn; tauto).
Qed.
Lemma copy_cap_facts : forall n, 0 <= n -> n < PML.copy_cap n <= Z.max n 44 + 8 /\ PML.copy_cap n mod 8 = 0 /\ Z.testbit (PML.copy_cap n + 1) 0 = true.
Proof.
  intros n Hn. unfold PML.copy_cap. rewrite CL5.lor7 by lia. pose proof (Z.div_mod (Z.max n 44) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (Z.max n 44) 8 ltac:(lia)) as B.
  set (q := Z.max n 44 / 8) in *. split; [lia|]. split.
  - replace (8 * q + 7 + 1) with ((q + 1) * 8) by lia. apply Z.mod_mul. lia.
  - rewrite Z.bit0_odd. replace (8 * q + 7 + 1 + 1) with (1 + 2 * (4 * q + 4)) by lia. rewrite Z.odd_add_mul_2. reflexivity.
Qed.

Lemma u64_of_defined : forall (M : mem) a, L5.defined M a 8 -> exists v, 0 <= v < 2 ^ 64 /\ L5.u64_at RSEGS M a v.
Proof.
  intros M a Hd.
  assert (RD : forall (k : nat) b, (forall i, 0 <= i < Z.of_nat k -> M (Z_to_bv 64 (b + i)) <> None) -> exists bs, rdn RSEGS M (Z_to_bv 64 b) k = Some bs /\ length bs = k).
  { induction k as [|k IH]; intros b H; [exists []; split; reflexivity|].
    destruct (IH (b + 1)) as (bs & Hr & Hl); [intros i Hi; replace (b + 1 + i) with (b + (1 + i)) by lia; apply H; lia|].
    pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. destruct (M (Z_to_bv 64 b)) as [x|] eqn:Hb; [|contradiction].
    exists (x :: bs). cbn [rdn]. rewrite Hb, L5C.add1_lit, Hr. split; [reflexivity | cbn [length]; lia]. }
  destruct (RD 8%nat a Hd) as (bs & Hr & Hl). exists (bytes_le_to_Z bs).
  pose proof (bytes_le_to_Z_nonneg bs) as N0. pose proof (bytes_le_to_Z_bound bs) as N1. rewrite Hl in N1. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in N1.
  split; [lia|]. unfold L5.u64_at. rewrite Hr. f_equal. symmetry. apply APSX.word_to_le_bytes_of_bytes_n; [exact Hl | lia].
Qed.
Lemma u64_copy_u8 : forall (M M' : mem) a b w k v, 0 <= a -> a + 8 <= 2 ^ 64 -> 0 <= b -> b + 8 <= 2 ^ 64 -> L5.u64_at RSEGS M a w -> L5.u64_at RSEGS M' b w -> 0 <= k < 8 ->
  L5.u8_at RSEGS M (a + k) v -> L5.u8_at RSEGS M' (b + k) v.
Proof.
  intros M M' a b w k v Ha Ha8 Hb Hb8 HA HB Hk Hv. unfold L5.u64_at in HA, HB. set (l := word_to_le_bytes 8 (Z_to_bv 64 w)) in *.
  assert (Ll : length l = 8%nat) by (unfold l, word_to_le_bytes; apply length_Z_to_le_bytes).
  pose proof (L5C.rdn_bytes_at RSEGS M l a Ha ltac:(rewrite Ll; lia) ltac:(rewrite Ll; exact HA)) as BA.
  pose proof (L5C.rdn_bytes_at RSEGS M' l b Hb ltac:(rewrite Ll; lia) ltac:(rewrite Ll; exact HB)) as BB.
  specialize (BA (Z.to_nat k) ltac:(rewrite length_map, Ll; lia)). specialize (BB (Z.to_nat k) ltac:(rewrite length_map, Ll; lia)). rewrite Z2Nat.id in BA, BB by lia.
  unfold L5.u8_at in *. rewrite BB, <- BA. exact Hv.
Qed.
Lemma sso_copy : forall (M M' : mem) so d w0 w1 w2 s, 0 <= so -> so + 24 <= 2 ^ 64 -> 0 <= d -> d + 24 <= 2 ^ 64 ->
  L5.u64_at RSEGS M so w0 -> L5.u64_at RSEGS M (so + 8) w1 -> L5.u64_at RSEGS M (so + 16) w2 -> L5.u64_at RSEGS M' d w0 -> L5.u64_at RSEGS M' (d + 8) w1 -> L5.u64_at RSEGS M' (d + 16) w2 ->
  L5.lstr_short RSEGS M so s -> L5.lstr_short RSEGS M' d s.
Proof.
  intros M M' so d w0 w1 w2 s Hso Hso2 Hd Hd2 S0 S1 S2 D0 D1 D2 (Hlen & Hflag & Hbytes & Hnul).
  assert (CP : forall i v, 0 <= i < 24 -> L5.u8_at RSEGS M (so + i) v -> L5.u8_at RSEGS M' (d + i) v).
  { intros i v Hi Hv. destruct (Z_lt_le_dec i 8) as [I8|I8]; [exact (u64_copy_u8 M M' so d w0 i v Hso ltac:(lia) Hd ltac:(lia) S0 D0 ltac:(lia) Hv)|].
    destruct (Z_lt_le_dec i 16) as [I16|I16].
    - replace (d + i) with (d + 8 + (i - 8)) by lia. apply (u64_copy_u8 M M' (so + 8) (d + 8) w1 (i - 8) v); [lia | lia | lia | lia | exact S1 | exact D1 | lia|].
      replace (so + 8 + (i - 8)) with (so + i) by lia. exact Hv.
    - replace (d + i) with (d + 16 + (i - 16)) by lia. apply (u64_copy_u8 M M' (so + 16) (d + 16) w2 (i - 16) v); [lia | lia | lia | lia | exact S2 | exact D2 | lia|].
      replace (so + 16 + (i - 16)) with (so + i) by lia. exact Hv. }
  split; [exact Hlen|]. split; [rewrite <- (Z.add_0_r d); apply CP; [lia | rewrite Z.add_0_r; exact Hflag]|].
  split.
  - intros j Hj. replace (d + 1 + Z.of_nat j) with (d + (1 + Z.of_nat j)) by lia. apply CP; [lia|]. replace (so + (1 + Z.of_nat j)) with (so + 1 + Z.of_nat j) by lia. exact (Hbytes j Hj).
  - replace (d + 1 + Z.of_nat (length s)) with (d + (1 + Z.of_nat (length s))) by lia. apply CP; [lia|]. replace (so + (1 + Z.of_nat (length s))) with (so + 1 + Z.of_nat (length s)) by lia. exact Hnul.
Qed.

Lemma sso_words : forall (M : mem) o s, 0 <= o -> o + 24 <= 2 ^ 64 -> L5.lstr_short RSEGS M o s -> L5.defined M o 24 ->
  exists w0 w1 w2, 0 <= w0 < 2 ^ 64 /\ 0 <= w1 < 2 ^ 64 /\ 0 <= w2 < 2 ^ 64 /\ L5.u64_at RSEGS M o w0 /\ L5.u64_at RSEGS M (o + 8) w1 /\ L5.u64_at RSEGS M (o + 16) w2 /\
    SBS.bit0 w0 = 0 /\ (w0 mod 256) / 2 = Z.of_nat (length s).
Proof.
  intros M o s Ho Ho2 (Hlen & Hflag & _) D.
  destruct (u64_of_defined M o ltac:(eapply L5.defined_sub; [exact D | lia | lia])) as (w0 & Hw0 & C0).
  destruct (u64_of_defined M (o + 8) ltac:(eapply L5.defined_sub; [exact D | lia | lia])) as (w1 & Hw1 & C1).
  destruct (u64_of_defined M (o + 16) ltac:(eapply L5.defined_sub; [exact D | lia | lia])) as (w2 & Hw2 & C2).
  exists w0, w1, w2. repeat (split; [assumption|]).
  pose proof (TK2.u64_u8_low M o w0 Ho ltac:(lia) C0) as B. pose proof (Z.mod_pos_bound w0 256 ltac:(lia)) as Bm.
  assert (E : w0 mod 256 = 2 * Z.of_nat (length s)) by (apply (u8_inj M o _ _ B Hflag); lia).
  unfold SBS.bit0. rewrite E. split; [apply land1_even | rewrite Z.mul_comm; apply Z.div_mul; lia].
Qed.
Definition CS15 : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma ko5_cs : forall q, In q SBS.KO5 -> In q CS15. Proof. intros q Hq. unfold SBS.KO5, CS15 in *. cbn [In] in *. tauto. Qed.
Lemma ko6_cs : forall q, In q SBS.KO6 -> In q CS15. Proof. intros q Hq. unfold SBS.KO6, CS15 in *. cbn [In] in *. tauto. Qed.
Lemma ko5_kn : forall q, In q SBS.KO5 -> In q SBS.KN. Proof. intros q Hq. unfold SBS.KO5, SBS.KN in *. cbn [In] in *. tauto. Qed.
Lemma ko6_ko5 : forall q, In q SBS.KO6 -> In q SBS.KO5. Proof. intros q Hq. unfold SBS.KO5, SBS.KO6 in *. cbn [In] in *. tauto. Qed.

Section H.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis LOCL : PMS.locale_ctor_later_spec L.
Hypothesis OPNEW : PMS.opnew_spec L HI.
Hypothesis MEMMOVE_OK : CH2.copy1_spec L SBT.MEMMOVE.
Hypothesis MEMCPY_OK : CH2.copy1_spec L SBT.MEMCPY.

Lemma heap_client_write : forall LB cr (M M' : mem) VM (K : Z -> Prop), hi_heap HI LB cr M VM -> 0x7fff80000000 <= hl_sptop L -> TK.samem K M M' -> mem_grows M M' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ K a -> in_block LB a \/ hl_ceil L <= a < hl_sptop L) -> hi_heap HI LB cr M' VM.
Proof.
  intros LB cr M M' VM K HH Htop AG MG HK. pose proof (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH) as BOK.
  pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI.
  apply (hio_frame L SCFG HI HIok LB cr M M' VM HH).
  - intros a Ha HP. apply AG; [exact Ha|]. destruct (classic (K a)) as [Y|N]; [exact Y|]. exfalso.
    destruct (HK a Ha N) as [X|X].
    + destruct HP as [(_ & P2 & _)|P]; [exact (P2 X)|]. destruct X as (b & Hb & Hr). destruct (BOK b Hb) as (_ & B1 & _ & _ & B4). unfold hl_ceil in B4.
      destruct (PmLayout.ly_ro L LAY a P) as [Y|Y]; lia.
    + destruct HP as [(P1 & _)|P]; [lia|]. destruct (PmLayout.ly_ro L LAY a P) as [Y|Y]; [rewrite IHI in Y; unfold hl_ceil in X; lia | lia].
  - intros a Hd. apply MG. exact Hd.
Qed.

Lemma FR_fresh_write : forall LB0 sp0 SCR foot (M0 M M' : mem) (K : Z -> Prop) A cap, TK2.FR L LB0 sp0 SCR foot M0 M -> TK.samem K M M' -> mem_grows M M' -> TK2.blocks_ok L LB0 ->
  hl_ceil L + SCR <= sp0 -> 0x7fff80000000 <= hl_sptop L -> block_range L A cap -> blocks_apart A cap LB0 ->
  (forall a, ~ K a -> (sp0 - SCR <= a < sp0) \/ foot a \/ A <= a < A + cap) -> TK2.FR L LB0 sp0 SCR foot M0 M'.
Proof.
  intros LB0 sp0 SCR foot M0 M M' K A cap HF AG MG HB Hc Htop (R0 & R1 & _ & _ & R4) AP HK. apply (TK2.FR_samem L _ _ _ _ _ _ _ K HF AG).
  - intros a Ha HC Hf He. destruct (classic (K a)) as [Y|N]; [exact Y|]. exfalso. destruct (HK a N) as [X|[X|X]]; [exact (TK2.client_not_window L LAY _ _ _ _ HC HB Hc Htop X) | exact (Hf X)|].
    destruct HC as [(b & Hb & Hr)|[(C1 & _)|(C1 & _)]]; [destruct (AP b Hb); lia | lia | lia].
  - intros a Ha Hd. apply MG. exact Hd.
Qed.

Definition EXT_SCR : Z := 48 + PMS.OPNEW_SCR.
Definition ext_spec : Prop :=
  forall (LB : list (Z * Z)) (cr : credit) (this data cap sp r : Z) (s : list Z),
    PML.cps_heap L HI SBT.EXT r sp EXT_SCR LB cr
      (fun R M => PML.entry L R M sp r EXT_SCR /\ PML.a0 R this /\ PML.a1 R data /\ PML.a2 R (Z.of_nat (length s)) /\ Z.of_nat (length s) < 2 ^ 26 /\
                  L5.bytes_at RSEGS M data s /\ In (data, cap) LB /\ Z.of_nat (length s) < cap /\
                  PML.obj_on_stack L sp this 24 /\ L5.defined M this 24 /\ credit_ok L cr (PML.copy_cap (Z.of_nat (length s))))
      (fun R M R' M' LB' cr' LBk W => exists rep, PML.srep_chars rep = s /\ PML.str_at M' this rep /\ LB' = PML.srep_blocks rep ++ LB /\ LBk = LB /\
          (forall b, In b (PML.srep_blocks rep) -> L5C.fresh_block L LB M' (fst b) (snd b) /\ snd b = PML.copy_cap (Z.of_nat (length s)) /\ cr' = debit L cr (snd b)) /\
          (PML.srep_blocks rep = [] -> cr' = cr) /\ W = [(this, 24)]).

Lemma ext_ok : ext_spec.
Proof.
  intros LB cr this data cap sp r s fx R M model K HH (Hh & Hl & Hmat) HK0 Hfp (EN & A0 & A1 & A2 & Hn & BY & INB & Hcap & (O1 & O2 & O3) & DT & CRD) Hcont.
  destruct EN as (Hra & Hrok & Hsp & Htp & STK). pose proof STK as (S1 & S2 & S3 & S4 & S5). unfold PML.a0, PML.a1, PML.a2 in *.
  set (n := Z.of_nat (length s)) in *. assert (Hn0 : 0 <= n) by (unfold n; lia).
  pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_segs L LAY) as Y1.
  set (SCR := EXT_SCR) in *. assert (HSCR : SCR = 8288) by reflexivity.
  assert (SPOK : CK.spok sp) by (split; [unfold hl_ceil in *; lia | exact S1]).
  pose proof (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH) as BOK.
  destruct (BOK _ INB) as (DB0 & DB1 & _ & DB3 & DB4). cbn [fst snd] in DB0, DB1, DB3, DB4.
  unfold hl_ceil in *.
  set (foot := fun a : Z => this <= a < this + 24).
  assert (FR0 : TK2.FR L LB sp SCR foot M M) by (split; [intros a _ _ _ _; reflexivity | intros a Ha; replace a with (sp - SCR + (a - (sp - SCR))) by lia; apply S5; lia]).
  assert (FIN : forall (M' : mem), TK2.FR L LB sp SCR foot M M' -> (forall a, 0 <= a < 2 ^ 64 -> foot a -> M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None) -> L5C.hpres L LB sp SCR [(this, 24)] M M').
  { intros M' [F1 F2] FD. apply L5C.hpres_intro.
    - intros a (Ha & HC & HE & HO). apply F1; [exact Ha | exact HC | | exact HE]. intros X. apply (HO (this, 24) (or_introl eq_refl)). unfold L5.in_rng. cbn [fst snd]. exact X.
    - intros i Hi. apply F2. lia.
    - intros a Ha HC HE Hd. destruct (classic (foot a)) as [Y|N]; [exact (FD a Ha Y Hd) | rewrite (F1 a Ha HC N HE); exact Hd]. }
  apply (SBS.s_ext_entry FPM fx R M model K sp this data n r Hh Hl Hfp Hsp SPOK Hra Hrok A0 A1 A2 ltac:(lia) ltac:(lia) ltac:(lia)
           ltac:(eapply L5.defined_sub; [exact S5 | lia | lia]) ltac:(eapply L5.defined_sub; [exact DT | lia | lia]) O1).
  -
    intros N23 fx1 R1 M1 Hfp1 H2a H1a H10a H8a H9a H19a H20a FRM1 KO1 AG1 MG1.
    destruct (copy_cap_facts n Hn0) as (CC1 & CC2 & CC3). set (capn := PML.copy_cap n) in *.
    assert (AGS1 : TK.samem (fun a => ~ (sp - 48 <= a < hl_sptop L)) M M1) by (apply (TK.samem_weaken _ _ _ _ AG1); intros a Ha; unfold SBS.KE3; lia).
    pose proof (TK2.heap_stack_write L HI HIok LAY _ _ M M1 _ (sp - 48) (hl_sptop L) HH ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) AGS1 MG1) as HH1.
    assert (FR1 : TK2.FR L LB sp SCR foot M M1) by (apply (TK2.FR_grows L LAY LB sp SCR foot M M M1 _ FR0 AG1 MG1 BOK ltac:(unfold hl_ceil; lia) ltac:(lia)); intros a Ha; unfold SBS.KE3, foot in *; lia).
    assert (TP1 : getr R1 4%bv = Z_to_bv 64 PML.TP) by (rewrite (KO1 4%bv ltac:(ck_in)); exact Htp).
    assert (STK1 : L5C.stk (hl_sptop L) M1 (sp - 48) PMS.OPNEW_SCR).
    { apply (CK.sub_stk _ M M1 sp SCR _ _ STK MG1); [apply CK.al16; [exact S1 | reflexivity] | unfold PMS.OPNEW_SCR, PML.HEAP_STACK; lia | lia | unfold PMS.OPNEW_SCR, PML.HEAP_STACK; lia]. }
    apply (OPNEW LB cr capn (sp - 48) SBT.EXT_R_NEW fx1 R1 M1 model K HH1 (conj Hh (conj Hl Hmat)) HK0 Hfp1).
    { split; [exact (CK.mk_entry L R1 M1 (sp - 48) _ _ H1a (ra_ok_lit SBT.EXT_R_NEW eq_refl) H2a TP1 STK1)|]. split; [exact H10a|]. split; [lia | exact CRD]. }
    intros fx2 R2 M2 model2 LB2 cr2 LBk2 W2 Hfp2 (A & A0' & FB & -> & -> & -> & ->) RP2 HP2 BV2 HH2. unfold PML.a0 in A0'.
    destruct FB as (BR & FAP & FDEF). pose proof BR as (FB0 & FB1 & FB2 & FB3 & FB4). unfold hl_ceil in FB4.
    pose proof (FAP _ INB) as AP0. cbn [fst snd] in AP0.
    pose proof (TK2.hpres_samem L LAY _ (sp - 48) _ _ M1 M2 HP2 BOK STK1 ltac:(unfold PMS.OPNEW_SCR, PML.HEAP_STACK; lia)) as AG2.
    assert (FR2 : TK2.FR L LB sp SCR foot M M2).
    { apply (TK2.FR_hpres L LAY LB sp SCR foot M M1 M2 _ (sp - 48) _ _ FR1 HP2 BOK (incl_refl _)); [unfold hl_ceil; lia | lia | lia | unfold PMS.OPNEW_SCR, PML.HEAP_STACK; lia | lia
        | unfold PMS.OPNEW_SCR, PML.HEAP_STACK; lia | intros w a []]. }
    assert (MOK2 : PML.model_ok model2) by (split; [rewrite (L5C.halted_but_vm _ _ BV2); exact Hh | split; [rewrite (L5C.lazy_but_vm _ _ BV2); exact Hl | rewrite (L5C.materialized_but_vm _ _ BV2); exact Hmat]]).
    destruct MOK2 as (Hh2 & Hl2 & Hmat2).
    assert (KH : forall a, sp - 48 <= a -> TK2.keepH L LB [] (sp - 48) PMS.OPNEW_SCR a) by (intros a Ha; split; [intros w [] | left; exact Ha]).
    assert (KB : forall a, data <= a < data + cap -> TK2.keepH L LB [] (sp - 48) PMS.OPNEW_SCR a) by (intros a Ha; split; [intros w [] | right; right; left; exists (data, cap); split; [exact INB | exact Ha]]).
    apply (SBS.s_ext_r_new FPM fx2 R2 M2 model2 K sp A data n Hh2 Hl2 Hfp2 ltac:(rewrite (RP2 2%bv ltac:(ck_in)); exact H2a) SPOK ltac:(rewrite (RP2 8%bv ltac:(ck_in)); exact H8a) A0'
             ltac:(rewrite (RP2 19%bv ltac:(ck_in)); exact H19a) ltac:(lia) ltac:(lia) ltac:(lia)).
    intros fx3 R3 Hfp3 H2c H1c H10c H11c H12c H18c KN3.

    set (bs := map (Z_to_bv 8) s). assert (Lbs : length bs = length s) by apply length_map.
    assert (BY2 : L5.bytes_at RSEGS M2 data s).
    { apply (TK.bytes_samem _ M1 M2 data _ AG2); [lia | fold n; lia | intros i Hi; fold n in Hi; apply KB; lia|].
      apply (TK.bytes_samem _ M M1 data _ AG1); [lia | fold n; lia | intros i Hi; fold n in Hi; unfold SBS.KE3; lia | exact BY]. }
    assert (RD2 : rdn RSEGS M2 (Z_to_bv 64 data) (length bs) = Some bs) by (rewrite Lbs; apply (L5C.bytes_at_rdn RSEGS M2 s data); [lia | fold n; lia | exact BY2]).
    assert (ST2 : store_ok RSEGS M2 (Z_to_bv 64 A) (length bs) = true).
    { pose proof (L5C.writable_of_defined RSEGS M2 A capn FDEF ltac:(lia) ltac:(lia) 0 (length bs) ltac:(lia) ltac:(rewrite Lbs; fold n; lia)) as W. rewrite Z.add_0_r in W. exact W. }
    destruct (MEMCPY_OK fx3 M2 (Z_to_bv 64 A) (Z_to_bv 64 data) n bs R3 (Z_to_bv 64 SBT.EXT_R_CPY)) as (fx4 & R4 & Hms & Hkept & H10d);
      rewrite ?Y1, ?u64_of_Z by lia; try lia; try assumption; try (apply Hoare.ret_ok_even; reflexivity).
    rewrite Y1 in Hms. unfold PML.cfg. eapply L5.cps_of_msteps; [exact Hh2 | exact Hl2 | exact Hms |].
    pose proof (FPM _ _ _ _ _ _ _ _ Hms Hfp3) as Hfp4.
    set (M4 := wbytes M2 (Z_to_bv 64 A) bs) in *.
    assert (AG4 : TK.samem (fun a => ~ (A <= a < A + n)) M2 M4).
    { apply (TK.samem_weaken _ _ _ _ (CK.wbytes_samem M2 A bs ltac:(lia) ltac:(rewrite Lbs; fold n; lia))). intros a Ha. rewrite Lbs. fold n. lia. }
    assert (MG4 : mem_grows M2 M4) by apply CK.wbytes_grows.
    assert (BY4 : L5.bytes_at RSEGS M4 A s) by (apply copied_bytes; [lia | fold n; lia]).
    assert (KR4 : TK.keepsR CS15 R3 R4) by (apply CK.keepsR_kept; [exact Hkept | reflexivity]).
    assert (HH4 : hi_heap HI ((A, capn) :: LB) (debit L cr capn) M4 (m_vmmaps model2)).
    { apply (heap_client_write _ _ M2 M4 _ _ HH2 ltac:(lia) AG4 MG4). intros a Ha NK. left. exists (A, capn). split; [left; reflexivity | cbn [fst snd]; lia]. }
    assert (FR4 : TK2.FR L LB sp SCR foot M M4).
    { apply (FR_fresh_write LB sp SCR foot M M2 M4 _ A capn FR2 AG4 MG4 BOK ltac:(unfold hl_ceil; lia) ltac:(lia) BR FAP). intros a Ha. right. right. lia. }
    apply (SBS.s_ext_r_cpy FPM fx4 R4 M4 model2 K sp this A n (capn - 1) r R Hh2 Hl2 Hfp4 ltac:(rewrite (KR4 2%bv ltac:(ck_in)); exact H2c) SPOK
             ltac:(rewrite (KR4 8%bv ltac:(ck_in)), (KN3 8%bv ltac:(ck_in)), (RP2 8%bv ltac:(ck_in)); exact H8a)
             ltac:(rewrite (KR4 9%bv ltac:(ck_in)), (KN3 9%bv ltac:(ck_in)), (RP2 9%bv ltac:(ck_in)); exact H9a)
             ltac:(rewrite (KR4 18%bv ltac:(ck_in)); exact H18c)
             ltac:(rewrite (KR4 20%bv ltac:(ck_in)), (KN3 20%bv ltac:(ck_in)), (RP2 20%bv ltac:(ck_in)); exact H20a) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    { apply (SBS.ext_frame_x _ M2 M4 sp r R AG4); [lia | intros i Hi; lia|]. apply (SBS.ext_frame_x _ M1 M2 sp r R AG2); [lia | intros i Hi; apply KH; lia | exact FRM1]. }
    { exact Hrok. }
    { apply (L5.defined_grows _ _ _ _ MG4). intros i Hi. apply (L5C.hpres_cdef _ _ _ _ _ _ _ (this + i) HP2 ltac:(lia));
        [right; left; unfold hl_ceil; unfold PMS.OPNEW_SCR, PML.HEAP_STACK; lia | unfold in_errno; rewrite (PmLayout.ly_errno L LAY); lia | apply MG1; apply DT; exact Hi]. }
    { apply (L5.defined_grows _ _ _ _ MG4). eapply L5.defined_sub; [exact FDEF | lia | lia]. }
    { exact O1. }
    { lia. }
    intros fx5 R5 M5 Hfp5 H2e H10e SS5 KO5e W0 W8 W16 NUL5 AG5 MG5.
    apply (Hcont fx5 R5 M5 model2 ((A, capn) :: LB) (debit L cr capn) LB [(this, 24)] Hfp5).
    + exists (PML.SLong capn A s). split; [reflexivity|]. split.
      { cbn [PML.str_at]. fold n. split; [|split; [exact CC2 | lia]]. unfold L5.lstr_long. fold n.
        split; [exact CC3|]. split; [replace (capn + 1) with (capn - 1 + 2) by lia; exact W0|]. split; [exact W8|]. split; [exact W16|].
        split; [|exact NUL5]. apply (TK.bytes_samem _ M4 M5 A _ AG5); [lia | fold n; lia | intros i Hi; fold n in Hi; cbn beta; lia | exact BY4]. }
      split; [reflexivity|]. split; [reflexivity|].
      split; [intros b [<-|[]]; cbn [fst snd]; split; [split; [exact BR | split; [exact FAP | exact (L5.defined_grows _ _ _ _ MG5 (L5.defined_grows _ _ _ _ MG4 FDEF))]] | split; reflexivity]|].
      split; [intros X; discriminate X | reflexivity].
    + apply rp_final4; [rewrite H2e, Hsp; reflexivity | exact SS5 |].
      exact (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ KO1 (ko_rp SBS.KO5 _ _ RP2 eq_refl)) (CK.keepsR_sub _ _ _ _ KN3 ko5_kn))
               (CK.keepsR_sub _ _ _ _ KR4 ko5_cs)) KO5e).
    + apply FIN.
      * apply (FR_fresh_write LB sp SCR foot M M4 M5 _ A capn FR4 AG5 MG5 BOK ltac:(unfold hl_ceil; lia) ltac:(lia) BR FAP). intros a Ha. unfold foot.
        destruct (classic (this <= a < this + 24)) as [Y|N]; [right; left; exact Y | right; right]. destruct (classic (A + n <= a < A + n + 1)) as [Y2|N2]; [lia | exfalso; apply Ha; split; assumption].
      * intros a Ha Hf Hd. apply MG5, MG4. unfold foot in Hf. apply (L5C.hpres_cdef _ _ _ _ _ _ _ a HP2 Ha);
          [right; left; unfold hl_ceil; unfold PMS.OPNEW_SCR, PML.HEAP_STACK; lia | unfold in_errno; rewrite (PmLayout.ly_errno L LAY); lia | apply MG1; exact Hd].
    + exact BV2.
    + apply (heap_client_write _ _ M4 M5 _ _ HH4 ltac:(lia) AG5 MG5). intros a Ha NK.
      destruct (classic (this <= a < this + 24)) as [Y|N]; [right; unfold hl_ceil; lia | left]. exists (A, capn). split; [left; reflexivity | cbn [fst snd]].
      destruct (classic (A + n <= a < A + n + 1)) as [Y2|N2]; [lia | exfalso; apply NK; split; assumption].
  -
    intros N0 fx1 R1 M1 Hfp1 H2a H10a KR1 B0 B1 AG1 MG1.
    assert (Es : s = []) by (unfold n in N0; destruct s; [reflexivity | cbn [length] in N0; lia]). subst s.
    apply (Hcont fx1 R1 M1 model LB cr LB [(this, 24)] Hfp1).
    + exists (PML.SShort []). split; [reflexivity|]. split.
      { cbn [PML.str_at]. unfold L5.lstr_short. cbn [length]. split; [lia|]. split; [exact B0|]. split; [intros i Hi; cbn in Hi; lia|]. replace (this + 1 + Z.of_nat 0) with (this + 1) by lia. exact B1. }
      split; [reflexivity|]. split; [reflexivity|]. split; [intros b []|]. split; reflexivity.
    + apply CK.rp_of_keeps; [rewrite H2a, Hsp; reflexivity | exact KR1].
    + apply FIN; [|intros a Ha _ Hd; apply MG1; exact Hd].
      apply (TK2.FR_grows L LAY LB sp SCR foot M M M1 _ FR0 AG1 MG1 BOK ltac:(unfold hl_ceil; lia) ltac:(lia)). intros a Ha. unfold SBS.KE3, foot in *. lia.
    + apply L5C.model_but_vm_refl.
    + apply (TK2.heap_stack_write L HI HIok LAY _ _ M M1 _ (sp - 48) (hl_sptop L) HH ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia)); [|exact MG1].
      apply (TK.samem_weaken _ _ _ _ AG1). intros a Ha. unfold SBS.KE3. lia.
  -
    intros N fx1 R1 M1 Hfp1 H2a H1a H10a H11a H12a H8a H9a H18a FRM1 KO1 FLAG AG1 MG1.
    set (bs := map (Z_to_bv 8) s). assert (Lbs : length bs = length s) by apply length_map.
    assert (BY1 : L5.bytes_at RSEGS M1 data s).
    { apply (TK.bytes_samem _ M M1 data _ AG1); [lia | fold n; lia | intros i Hi; fold n in Hi; unfold SBS.KE3; lia | exact BY]. }
    assert (RD1 : rdn RSEGS M1 (Z_to_bv 64 data) (length bs) = Some bs) by (rewrite Lbs; apply (L5C.bytes_at_rdn RSEGS M1 s data); [lia | fold n; lia | exact BY1]).
    assert (DT1 : L5.defined M1 this 24) by exact (L5.defined_grows _ _ _ _ MG1 DT).
    assert (ST1 : store_ok RSEGS M1 (Z_to_bv 64 (this + 1)) (length bs) = true).
    { pose proof (L5C.writable_of_defined RSEGS M1 this 24 DT1 ltac:(lia) ltac:(lia) 1 (length bs) ltac:(lia) ltac:(rewrite Lbs; fold n; lia)) as W. exact W. }
    destruct (MEMMOVE_OK fx1 M1 (Z_to_bv 64 (this + 1)) (Z_to_bv 64 data) n bs R1 (Z_to_bv 64 SBT.EXT_R_MOVE)) as (fx2 & R2 & Hms & Hkept & H10b);
      rewrite ?Y1, ?u64_of_Z by lia; try lia; try assumption; try (apply Hoare.ret_ok_even; reflexivity).
    rewrite Y1 in Hms. unfold PML.cfg. eapply L5.cps_of_msteps; [exact Hh | exact Hl | exact Hms |].
    pose proof (FPM _ _ _ _ _ _ _ _ Hms Hfp1) as Hfp2.
    set (M2 := wbytes M1 (Z_to_bv 64 (this + 1)) bs) in *.
    assert (AG2 : TK.samem (fun a => ~ (this + 1 <= a < this + 1 + n)) M1 M2).
    { apply (TK.samem_weaken _ _ _ _ (CK.wbytes_samem M1 (this + 1) bs ltac:(lia) ltac:(rewrite Lbs; fold n; lia))). intros a Ha. rewrite Lbs. fold n. lia. }
    assert (MG2 : mem_grows M1 M2) by apply CK.wbytes_grows.
    assert (BY2 : L5.bytes_at RSEGS M2 (this + 1) s) by (apply copied_bytes; [lia | fold n; lia]).
    assert (KR2 : TK.keepsR CS15 R1 R2) by (apply CK.keepsR_kept; [exact Hkept | reflexivity]).
    apply (SBS.s_ext_r_move FPM fx2 R2 M2 model K sp this (this + 1) n r R Hh Hl Hfp2 ltac:(rewrite (KR2 2%bv ltac:(ck_in)); exact H2a) SPOK ltac:(rewrite (KR2 8%bv ltac:(ck_in)); exact H8a)
             ltac:(rewrite (KR2 9%bv ltac:(ck_in)); exact H9a) ltac:(rewrite (KR2 18%bv ltac:(ck_in)); exact H18a) ltac:(lia) ltac:(lia) ltac:(lia)).
    { apply (SBS.ext_frame_x _ M1 M2 sp r R AG2); [lia | intros i Hi; lia | exact FRM1]. }
    { exact Hrok. }
    { apply (L5.defined_grows _ _ _ _ MG2). eapply L5.defined_sub; [exact DT1 | lia | lia]. }
    { lia. }
    intros fx3 R3 M3 Hfp3 H2c H10c SS3 KO3 NUL3 AG3 MG3.
    set (KA := fun a : Z => ~ (sp - 48 <= a < sp) /\ ~ (this <= a < this + 24)).
    assert (AG03 : TK.samem KA M M3).
    { intros a Ha (Z1 & Z2). rewrite (AG3 a Ha ltac:(cbn beta; lia)), (AG2 a Ha ltac:(cbn beta; lia)). apply (AG1 a Ha). unfold SBS.KE3. lia. }
    assert (MG03 : mem_grows M M3) by (intros z Hz; apply MG3, MG2, MG1; exact Hz).
    apply (Hcont fx3 R3 M3 model LB cr LB [(this, 24)] Hfp3).
    + exists (PML.SShort s). split; [reflexivity|]. split.
      { cbn [PML.str_at]. unfold L5.lstr_short. fold n. split; [lia|].
        split; [apply (TK.u8_samem _ M2 M3 _ _ AG3); [lia | lia|]; apply (TK.u8_samem _ M1 M2 _ _ AG2); [lia | lia | exact FLAG]|].
        split; [apply (TK.bytes_samem _ M2 M3 (this + 1) _ AG3); [lia | fold n; lia | intros i Hi; fold n in Hi; lia | exact BY2]|].
        replace (this + 1 + n) with (this + 1 + n) by lia. exact NUL3. }
      split; [reflexivity|]. split; [reflexivity|]. split; [intros b []|]. split; reflexivity.
    + apply rp_final4; [rewrite H2c, Hsp; reflexivity | exact SS3 |].
      exact (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ KO1 (CK.keepsR_sub _ _ _ _ KR2 ko5_cs)) KO3).
    + apply FIN; [|intros a Ha _ Hd; apply MG03; exact Hd].
      apply (TK2.FR_grows L LAY LB sp SCR foot M M M3 _ FR0 AG03 MG03 BOK ltac:(unfold hl_ceil; lia) ltac:(lia)). intros a Ha. unfold KA, foot in *. lia.
    + apply L5C.model_but_vm_refl.
    + apply (TK2.heap_stack_write L HI HIok LAY _ _ M M3 _ (sp - 48) (hl_sptop L) HH ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia)); [|exact MG03].
      apply (TK.samem_weaken _ _ _ _ AG03). intros a Ha. unfold KA. lia.
Qed.

Theorem sbuf_ctor_ok : TPS2.sbuf_ctor_spec L HI.
Proof.
  intros LB cr SB so sp r srep0 fx R M model K HH (Hh & Hl & Hmat) HK0 Hfp (EN & A0 & A1 & A2 & STR & INB & Hn & (OB1 & OB2 & OB3) & (OS1 & OS2 & OS3) & APT & DSB & DSO & GL & RO & CRD) Hcont.
  destruct EN as (Hra & Hrok & Hsp & Htp & STK). pose proof STK as (S1 & S2 & S3 & S4 & S5). unfold PML.a0, PML.a1, PML.a2, PML.apart in *.
  pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI.
  set (SCR := TPS2.SBUF_SCR) in *. assert (HSCR : SCR = 8352) by reflexivity.
  assert (SPOK : CK.spok sp) by (split; [unfold hl_ceil in *; lia | exact S1]).
  pose proof (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH) as BOK.
  unfold hl_ceil in *.
  set (foot := fun a : Z => SB <= a < SB + 104).
  assert (FR0 : TK2.FR L LB sp SCR foot M M) by (split; [intros a _ _ _ _; reflexivity | intros a Ha; replace a with (sp - SCR + (a - (sp - SCR))) by lia; apply S5; lia]).
  assert (FIN : forall (M' : mem), TK2.FR L LB sp SCR foot M M' -> (forall a, 0 <= a < 2 ^ 64 -> foot a -> M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None) -> L5C.hpres L LB sp SCR [(SB, 104)] M M').
  { intros M' [F1 F2] FD. apply L5C.hpres_intro.
    - intros a (Ha & HC & HE & HO). apply F1; [exact Ha | exact HC | | exact HE]. intros X. apply (HO (SB, 104) (or_introl eq_refl)). unfold L5.in_rng. cbn [fst snd]. exact X.
    - intros i Hi. apply F2. lia.
    - intros a Ha HC HE Hd. destruct (classic (foot a)) as [Y|N]; [exact (FD a Ha Y Hd) | rewrite (F1 a Ha HC N HE); exact Hd]. }

  apply (SBS.s_sb_entry FPM fx R M model K sp SB so r Hh Hl Hfp Hsp SPOK Hra Hrok A0 A1 A2 ltac:(lia) ltac:(lia) RO ltac:(eapply L5.defined_sub; [exact S5 | lia | lia]) DSB OB1).
  intros fx1 R1 M1 Hfp1 H2a H1a H10a LIVE1 FRM1 KO1 AG1 MG1.
  assert (TP1 : getr R1 4%bv = Z_to_bv 64 PML.TP) by (rewrite (KO1 4%bv ltac:(ck_in)); exact Htp).
  assert (STK1 : L5C.stk (hl_sptop L) M1 (sp - 64) 32) by (apply (CK.sub_stk _ M M1 sp SCR _ _ STK MG1); [apply CK.al16; [exact S1 | reflexivity] | lia | lia | lia]).
  assert (RO1 : PML.img_ro M1) by (apply (TK.img_clear_samem _ M M1 _ _ AG1); [lia | unfold PML.IMG_RO_HI; lia | intros i Hi; unfold PML.IMG_RO_HI in Hi; unfold SBS.KE1; lia | exact RO]).
  assert (GL1 : PMS.gloc_done M1).
  { destruct GL as (G1 & G2). split; [apply (TK2.u8_x _ M M1 AG1); [lia | intros i Hi; unfold SBS.KE1; lia | exact G1] | apply (TK2.u64_x _ M M1 AG1); [lia | intros i Hi; unfold SBS.KE1; lia | exact G2]]. }

  apply (LOCL (SB + 8) (sp - 64) SBT.R_LOC fx1 R1 M1 model K Hh Hl HK0 Hfp1).
  { split; [exact (CK.mk_entry L R1 M1 (sp - 64) _ _ H1a (ra_ok_lit SBT.R_LOC eq_refl) H2a TP1 STK1)|]. split; [exact H10a|]. split; [exact GL1|]. split; [exact RO1|].
    split; [split; [lia | split; [lia | apply al8_add; [exact OB3 | reflexivity]]]|]. apply (L5.defined_grows _ _ _ _ MG1). eapply L5.defined_sub; [exact DSB | lia | lia]. }
  intros fx2 R2 M2 Hfp2 LOC2 RP2 FB2 MG2. pose proof (TK2.frame_but_samem _ _ _ FB2) as AG2.
  assert (OUT2 : forall a, ~ (sp - 96 <= a < sp - 64) -> ~ (SB + 8 <= a < SB + 16) -> L5.outside [(sp - 64 - 32, 32); (SB + 8, 8)] a).
  { intros a Z1 Z2 w Hw Hin. destruct Hw as [<-|[<-|[]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; lia. }
  set (KA := fun a : Z => ~ (sp - 96 <= a < sp) /\ ~ (SB <= a < SB + 16)).
  assert (AG02 : TK.samem KA M M2) by (intros a Ha (Z1 & Z2); rewrite (AG2 a Ha (OUT2 a ltac:(lia) ltac:(lia))); apply (AG1 a Ha); unfold SBS.KE1; lia).
  assert (MG02 : mem_grows M M2) by (intros z Hz; apply MG2, MG1; exact Hz).
  assert (STR2 : PML.str_at_w M2 so srep0).
  { apply (TK2.str_at_w_x KA M M2 AG02); [lia | | exact STR]. split; [intros i Hi; unfold KA; lia|]. destruct srep0 as [s0|cap0 p0 s0]; [exact I|].
    destruct (BOK _ (INB (p0, cap0) (or_introl eq_refl))) as (Q0 & _ & _ & Q3 & Q4). cbn [fst snd] in Q0, Q3, Q4. unfold hl_ceil in Q4. split; [lia|]. split; [lia|]. intros i Hi. unfold KA. lia. }
  assert (DSO2 : L5.defined M2 so 24) by exact (L5.defined_grows _ _ _ _ MG02 DSO).
  assert (R2sp : getr R2 2%bv = Z_to_bv 64 (sp - 64)) by (rewrite (RP2 2%bv ltac:(ck_in)); exact H2a).
  assert (LIVE2 : SBS.sb_live R2 SB so).
  { destruct LIVE1 as (L8 & L19 & L20). unfold SBS.sb_live. rewrite (RP2 8%bv ltac:(ck_in)), (RP2 19%bv ltac:(ck_in)), (RP2 20%bv ltac:(ck_in)). repeat split; assumption. }
  assert (FRM2 : SBS.sb_frame M2 sp r R) by (apply (SBS.sb_frame_x _ M1 M2 sp r R AG2); [lia | intros i Hi; apply OUT2; lia | exact FRM1]).
  assert (DF2 : L5.defined M2 (sp - 112) 48) by (apply (L5.defined_grows _ _ _ _ MG02); eapply L5.defined_sub; [exact S5 | lia | lia]).
  assert (RO2 : PML.img_ro M2).
  { apply (TK.img_clear_samem _ M1 M2 _ _ AG2); [lia | unfold PML.IMG_RO_HI; lia | intros i Hi; unfold PML.IMG_RO_HI in Hi; apply OUT2; lia | exact RO1]. }
  assert (DS2 : L5.defined M2 SB 104) by exact (L5.defined_grows _ _ _ _ MG02 DSB).
  unfold PML.u64 in LOC2.
  set (KB := fun a : Z => ~ (sp - 112 <= a < sp) /\ ~ (SB <= a < SB + 104)).
  destruct srep0 as [s0|cap0 p0 s0].
  -
    cbn [PML.str_at_w] in STR2. cbn [PML.srep_chars] in *.
    destruct (sso_words M2 so s0 ltac:(lia) ltac:(lia) STR2 DSO2) as (w0 & w1 & w2 & Hw0 & Hw1 & Hw2 & C0 & C1 & C2 & B0 & HALF).
    apply (SBS.s_sb_r_loc FPM fx2 R2 M2 model K sp SB so r R w0 w1 w2 Hh Hl Hfp2 R2sp SPOK LIVE2 ltac:(lia) ltac:(lia) OB1 OS1 ltac:(lia) FRM2 Hrok DF2 RO2 DS2 Hw0 Hw1 Hw2 C0 C1 C2);
      [|intros B1; exfalso; exact (B1 B0)].
    intros _ fx3 R3 M3 Hfp3 H2c SS3 KO3 CVT (P16 & P24 & P32 & P88) Z3 D0 D1 D2 C96 AG3 MG3.
    assert (AG03 : TK.samem KB M M3) by (intros a Ha (Z1 & Z2); rewrite (AG3 a Ha ltac:(unfold SBS.KE2; lia)); apply (AG02 a Ha); unfold KA; lia).
    assert (MG03 : mem_grows M M3) by (intros z Hz; apply MG3, MG02; exact Hz).
    apply (Hcont fx3 R3 M3 model LB cr LB [(SB, 104)] Hfp3).
    + exists (PML.SShort s0). split; [reflexivity|]. split.
      { unfold TPS2.sbuf_at. cbn [PML.srep_data PML.srep_chars]. cbv zeta. unfold PML.u64, PML.u32. rewrite HALF in P32, P88.
        replace (SB + 64 + 1) with (SB + 65) by lia.
        split; [exact CVT|]. split; [apply (TK.u64_samem _ M2 M3 _ _ AG3); [lia | intros i Hi; unfold SBS.KE2; lia | exact LOC2]|].
        split; [exact P16|]. split; [exact P24|]. split; [exact P32|]. destruct Z3 as (Z40 & Z48 & Z56). split; [exact Z40|]. split; [exact Z48|]. split; [exact Z56|].
        replace (SB + 72) with (SB + 64 + 8) in D1 by lia. replace (SB + 80) with (SB + 64 + 16) in D2 by lia.
        split; [cbn [PML.str_at]; exact (sso_copy M2 M3 so (SB + 64) w0 w1 w2 s0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) C0 C1 C2 D0 D1 D2 STR2)|]. split; [exact P88 | exact C96]. }
      split; [reflexivity|]. split; [reflexivity|]. split; [intros b []|]. split; reflexivity.
    + apply rp_final5; [rewrite H2c, Hsp; reflexivity | exact SS3 |].
      exact (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ KO1 (ko_rp SBS.KO6 _ _ RP2 eq_refl)) KO3).
    + apply FIN; [|intros a Ha _ Hd; apply MG03; exact Hd].
      apply (TK2.FR_grows L LAY LB sp SCR foot M M M3 _ FR0 AG03 MG03 BOK ltac:(unfold hl_ceil; lia) ltac:(lia)). intros a Ha. unfold KB, foot in *. lia.
    + apply L5C.model_but_vm_refl.
    + apply (TK2.heap_stack_write L HI HIok LAY _ _ M M3 _ (sp - 112) (hl_sptop L) HH ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia)); [|exact MG03].
      apply (TK.samem_weaken _ _ _ _ AG03). intros a Ha. unfold KB. lia.
  -
    cbn [PML.str_at_w] in STR2. cbn [PML.srep_chars PML.srep_blocks] in *. destruct STR2 as ((Sbit & Sw0 & Sw8 & Sw16 & SBY & SNUL) & Slt).
    pose proof (INB (p0, cap0) (or_introl eq_refl)) as INB0.
    destruct (BOK _ INB0) as (Q0 & _ & _ & Q3 & Q4). cbn [fst snd] in Q0, Q3, Q4. unfold hl_ceil in Q4.
    set (n := Z.of_nat (length s0)) in *. assert (Hn0 : 0 <= n) by (unfold n; lia).
    apply (SBS.s_sb_r_loc FPM fx2 R2 M2 model K sp SB so r R (cap0 + 1) n p0 Hh Hl Hfp2 R2sp SPOK LIVE2 ltac:(lia) ltac:(lia) OB1 OS1 ltac:(lia) FRM2 Hrok DF2 RO2 DS2 ltac:(lia) ltac:(lia) ltac:(lia) Sw0 Sw8 Sw16);
      [intros B0; exfalso; unfold SBS.bit0 in B0; rewrite (land1_odd_low _ Sbit) in B0; discriminate B0|].
    intros _ fx3 R3 M3 Hfp3 H2c H1c H10c H11c H12c H8c KO3 CVT ZW C96 AG3 MG3.
    assert (AG03 : TK.samem KB M M3) by (intros a Ha (Z1 & Z2); rewrite (AG3 a Ha ltac:(unfold SBS.KE2; lia)); apply (AG02 a Ha); unfold KA; lia).
    assert (MG03 : mem_grows M M3) by (intros z Hz; apply MG3, MG02; exact Hz).
    assert (HH3 : hi_heap HI LB cr M3 (m_vmmaps model)).
    { apply (TK2.heap_stack_write L HI HIok LAY _ _ M M3 _ (sp - 112) (hl_sptop L) HH ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia)); [|exact MG03]. apply (TK.samem_weaken _ _ _ _ AG03). intros a Ha. unfold KB. lia. }
    assert (FR3 : TK2.FR L LB sp SCR foot M M3) by (apply (TK2.FR_grows L LAY LB sp SCR foot M M M3 _ FR0 AG03 MG03 BOK ltac:(unfold hl_ceil; lia) ltac:(lia)); intros a Ha; unfold KB, foot in *; lia).
    assert (TP3 : getr R3 4%bv = Z_to_bv 64 PML.TP) by (rewrite (KO3 4%bv ltac:(ck_in)), (RP2 4%bv ltac:(ck_in)); exact TP1).
    assert (STK3 : L5C.stk (hl_sptop L) M3 (sp - 64) EXT_SCR).
    { apply (CK.sub_stk _ M M3 sp SCR _ _ STK MG03); [apply CK.al16; [exact S1 | reflexivity] | unfold EXT_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK; lia | lia | unfold EXT_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK; lia]. }
    assert (DS3 : L5.defined M3 SB 104) by exact (L5.defined_grows _ _ _ _ MG3 DS2).
    apply (ext_ok LB cr (SB + 64) p0 cap0 (sp - 64) SBT.R_ASSIGN s0 fx3 R3 M3 model K HH3 (conj Hh (conj Hl Hmat)) HK0 Hfp3).
    { split; [exact (CK.mk_entry L R3 M3 (sp - 64) _ _ H1c (ra_ok_lit SBT.R_ASSIGN eq_refl) H2c TP3 STK3)|]. split; [exact H10c|]. split; [exact H11c|]. split; [exact H12c|]. split; [exact Hn|].
      split; [apply (TK.bytes_samem _ M2 M3 p0 _ AG3); [lia | fold n; lia | intros i Hi; fold n in Hi; unfold SBS.KE2; lia | exact SBY]|]. split; [exact INB0|]. split; [exact Slt|].
      split; [split; [lia | split; [lia | apply al8_add; [exact OB3 | reflexivity]]]|]. split; [eapply L5.defined_sub; [exact DS3 | lia | lia] | exact CRD]. }
    intros fx4 R4 M4 model4 LB4 cr4 LBk4 W4 Hfp4 (rep & CHR & SAT & -> & -> & FRESH & NOBLK & ->) RP4 HP4 BV4 HH4.
    pose proof (TK2.hpres_samem L LAY LB (sp - 64) _ _ M3 M4 HP4 BOK STK3 ltac:(unfold EXT_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK; lia)) as AG4.
    assert (KH : forall a, sp - 64 <= a -> ~ (SB + 64 <= a < SB + 88) -> TK2.keepH L LB [(SB + 64, 24)] (sp - 64) EXT_SCR a).
    { intros a Ha Hn4. split; [intros w [<-|[]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; lia | left; exact Ha]. }
    assert (MOK4 : PML.model_ok model4) by (split; [rewrite (L5C.halted_but_vm _ _ BV4); exact Hh | split; [rewrite (L5C.lazy_but_vm _ _ BV4); exact Hl | rewrite (L5C.materialized_but_vm _ _ BV4); exact Hmat]]).
    destruct MOK4 as (Hh4 & Hl4 & _).
    assert (CDEF4 : forall a, sp <= a < hl_sptop L -> M3 (Z_to_bv 64 a) <> None -> M4 (Z_to_bv 64 a) <> None).
    { intros a Ha Hd. apply (L5C.hpres_cdef _ _ _ _ _ _ _ a HP4 ltac:(lia)); [right; left; unfold hl_ceil; unfold EXT_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK; lia | unfold in_errno; rewrite (PmLayout.ly_errno L LAY); lia | exact Hd]. }
    assert (DS4 : L5.defined M4 SB 104) by (intros i Hi; apply CDEF4; [lia | apply DS3; exact Hi]).

    assert (WORDS : exists w0 w1 w2, 0 <= w0 < 2 ^ 64 /\ 0 <= w1 < 2 ^ 64 /\ 0 <= w2 < 2 ^ 64 /\ L5.u64_at RSEGS M4 (SB + 64) w0 /\ L5.u64_at RSEGS M4 (SB + 72) w1 /\ L5.u64_at RSEGS M4 (SB + 80) w2 /\
              (SBS.bit0 w0 <> 0 -> w1 <= 2 ^ 26 /\ 0 < w2 <= 2 ^ 47) /\
              (forall d e, ((SBS.bit0 w0 = 0 /\ d = SB + 65 /\ e = SB + 65 + (w0 mod 256) / 2) \/ (SBS.bit0 w0 <> 0 /\ d = w2 /\ e = w2 + w1)) ->
                           d = PML.srep_data (SB + 64) rep /\ e = PML.srep_data (SB + 64) rep + Z.of_nat (length (PML.srep_chars rep)))).
    { destruct rep as [s1|cap1 p1 s1].
      - cbn [PML.str_at] in SAT.
        destruct (sso_words M4 (SB + 64) s1 ltac:(lia) ltac:(lia) SAT ltac:(eapply L5.defined_sub; [exact DS4 | lia | lia])) as (w0 & w1 & w2 & Hw0 & Hw1 & Hw2 & C0 & C1 & C2 & B0 & HALF).
        exists w0, w1, w2. replace (SB + 64 + 8) with (SB + 72) in C1 by lia. replace (SB + 64 + 16) with (SB + 80) in C2 by lia. repeat (split; [assumption|]).
        split; [intros B1; exfalso; exact (B1 B0)|]. intros d e [(_ & -> & ->)|(B1 & _)]; [|exfalso; exact (B1 B0)]. cbn [PML.srep_data PML.srep_chars]. rewrite HALF. lia.
      - cbn [PML.str_at] in SAT. destruct SAT as ((Tbit & Tw0 & Tw8 & Tw16 & _) & _ & Tlt).
        destruct (FRESH (p1, cap1) (or_introl eq_refl)) as (((F0 & _ & _ & F3 & F4) & _) & _). cbn [fst snd] in F0, F3, F4. unfold hl_ceil in F4. cbn [PML.srep_chars] in CHR. subst s1.
        exists (cap1 + 1), n, p1. replace (SB + 64 + 8) with (SB + 72) in Tw8 by lia. replace (SB + 64 + 16) with (SB + 80) in Tw16 by lia.
        split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Tw0|]. split; [exact Tw8|]. split; [exact Tw16|]. split; [intros _; lia|].
        intros d e [(B0 & _)|(_ & -> & ->)]; [exfalso; unfold SBS.bit0 in B0; rewrite (land1_odd_low _ Tbit) in B0; discriminate B0|]. cbn [PML.srep_data PML.srep_chars]. fold n. lia. }
    destruct WORDS as (w0 & w1 & w2 & Hw0 & Hw1 & Hw2 & D0 & D1 & D2 & LONG & CASE).
    apply (SBS.s_sb_r_assign FPM fx4 R4 M4 model4 K sp SB r R w0 w1 w2 Hh4 Hl4 Hfp4 ltac:(rewrite (RP4 2%bv ltac:(ck_in)); exact H2c) SPOK ltac:(rewrite (RP4 8%bv ltac:(ck_in)); exact H8c) ltac:(lia) OB1).
    { apply (SBS.sb_frame_x _ M3 M4 sp r R AG4); [lia | intros i Hi; apply KH; lia|]. apply (SBS.sb_frame_x _ M2 M3 sp r R AG3); [lia | intros i Hi; unfold SBS.KE2; lia | exact FRM2]. }
    { exact Hrok. }
    { pose proof (L5C.hpres_defined _ _ _ _ _ _ _ HP4) as X. eapply L5.defined_sub; [exact X | unfold EXT_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK; lia | unfold EXT_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK; lia]. }
    { exact DS4. }
    { exact Hw0. } { exact Hw1. } { exact Hw2. } { exact D0. } { exact D1. } { exact D2. }
    { apply (TK.u32_samem _ M3 M4 _ _ AG4); [lia | intros i Hi; apply KH; lia | exact C96]. }
    { exact LONG. }
    intros fx5 R5 M5 d e Hfp5 H2e SS5 KO5 CS (P16 & P24 & P32 & P88) AG5 MG5. destruct (CASE d e CS) as [Ed Ee]. rewrite Ee in P32, P88. rewrite Ed in P16, P24. clear CS CASE.
    assert (X64 : forall off v, 0 <= off -> off + 8 <= 104 -> (off + 8 <= 64 \/ 88 <= off) -> (off + 8 <= 16 \/ 40 <= off) -> (off + 8 <= 88 \/ 96 <= off) -> L5.u64_at RSEGS M3 (SB + off) v -> L5.u64_at RSEGS M5 (SB + off) v).
    { intros off v O1 O2 O3 O4 O5 H. apply (TK.u64_samem _ M4 M5 _ _ AG5); [lia | intros i Hi; unfold SBS.KE4; lia|]. apply (TK.u64_samem _ M3 M4 _ _ AG4); [lia | intros i Hi; apply KH; lia | exact H]. }
    apply (Hcont fx5 R5 M5 model4 (PML.srep_blocks rep ++ LB) cr4 LB [(SB, 104)] Hfp5).
    + exists rep. split; [exact CHR|]. split.
      { unfold TPS2.sbuf_at. cbv zeta. unfold PML.u64, PML.u32.
        split; [rewrite <- (Z.add_0_r SB); apply X64; [lia | lia | lia | lia | lia | rewrite Z.add_0_r; exact CVT]|].
        split; [apply X64; [lia | lia | lia | lia | lia|]; apply (TK.u64_samem _ M2 M3 _ _ AG3); [lia | intros i Hi; unfold SBS.KE2; lia | exact LOC2]|].
        split; [exact P16|]. split; [exact P24|]. split; [exact P32|].
        split; [apply X64; [lia | lia | lia | lia | lia|]; replace (SB + 40) with (SB + 16 + 8 * 3) by lia; apply ZW; lia|].
        split; [apply X64; [lia | lia | lia | lia | lia|]; replace (SB + 48) with (SB + 16 + 8 * 4) by lia; apply ZW; lia|].
        split; [apply X64; [lia | lia | lia | lia | lia|]; replace (SB + 56) with (SB + 16 + 8 * 5) by lia; apply ZW; lia|].
        split.
        { apply (TK2.str_at_x _ M4 M5 AG5); [lia | | exact SAT]. split; [intros i Hi; unfold SBS.KE4; lia|]. destruct rep as [s1|cap1 p1 s1]; [exact I|].
          destruct (FRESH (p1, cap1) (or_introl eq_refl)) as (((F0 & _ & _ & F3 & F4) & _) & _). cbn [fst snd] in F0, F3, F4. unfold hl_ceil in F4.
          split; [lia|]. split; [lia|]. intros i Hi. unfold SBS.KE4. lia. }
        split; [exact P88|]. apply (TK.u32_samem _ M4 M5 _ _ AG5); [lia | intros i Hi; unfold SBS.KE4; lia|]. apply (TK.u32_samem _ M3 M4 _ _ AG4); [lia | intros i Hi; apply KH; lia | exact C96]. }
      split; [reflexivity|]. split; [reflexivity|].
      split; [intros b Hb; destruct (FRESH b Hb) as ((BR & AP & DEF) & E1 & E2); split; [split; [exact BR | split; [exact AP | exact (L5.defined_grows _ _ _ _ MG5 DEF)]] | split; assumption]|].
      split; [exact NOBLK | reflexivity].
    + apply rp_final5; [rewrite H2e, Hsp; reflexivity | exact SS5 |].
      exact (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ (TK.keepsR_trans _ _ _ _ KO1 (ko_rp SBS.KO6 _ _ RP2 eq_refl)) KO3) (ko_rp SBS.KO6 _ _ RP4 eq_refl)) KO5).
    + apply FIN.
      * assert (FR4 : TK2.FR L LB sp SCR foot M M4).
        { apply (TK2.FR_hpres L LAY LB sp SCR foot M M3 M4 LB (sp - 64) _ _ FR3 HP4 BOK (incl_refl _)); [unfold hl_ceil; lia | lia | lia | unfold EXT_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK; lia | lia
            | unfold EXT_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK; lia |]. intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. right. unfold foot. lia. }
        apply (TK2.FR_grows L LAY LB sp SCR foot M M4 M5 _ FR4 AG5 MG5 BOK ltac:(unfold hl_ceil; lia) ltac:(lia)). intros a Ha. unfold SBS.KE4, foot in *. lia.
      * intros a Ha Hf Hd. unfold foot in Hf. apply MG5. apply CDEF4; [lia | apply MG03; exact Hd].
    + exact BV4.
    + apply (TK2.heap_stack_write L HI HIok LAY _ _ M4 M5 _ (sp - 112) (hl_sptop L) HH4 ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia)); [|exact MG5].
      apply (TK.samem_weaken _ _ _ _ AG5). intros a Ha. unfold SBS.KE4. lia.
Qed.
End H.
End SBC.
