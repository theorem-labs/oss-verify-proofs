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
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim RefMemcpyLib As0StepLib
     ArtMem ArtRegs ArtAtomics ArtTac BrtLeaf BrtPoison BrtAllocG.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import Bo0_code_80aac_80c14 Bo0_code_81110_81228 Bo0_code_67fdc_6814c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Definition readable8 (M : word -> option byte) (lo hi : Z) : Prop :=
  forall a, lo <= a -> a + 8 <= hi -> a mod 8 = 0 -> exists w : word, cellA M a 8 (bv_unsigned w).

Lemma readable8_Wn : forall n M a v lo hi, 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> 0 <= lo -> hi < 2 ^ 64 -> (a + Z.of_nat n <= lo \/ hi <= a) ->
  readable8 M lo hi -> readable8 (Wn n M a v) lo hi.
Proof.
  intros n M a v lo hi Ha Hn Hlo Hhi Hap R b Hb1 Hb2 Hb3. destruct (R b Hb1 Hb2 Hb3) as [w C]. exists w.
  apply cell_Wn_other; [lia|lia|lia|cbn; lia|unfold apart; cbn; lia|exact C].
Qed.

(* [comment removed for export] *)
Definition trace_cells (M : word -> option byte) (this sz : Z) : Prop :=
  forall i, 0 <= i < sz -> exists w : word, cellA M (this + 16 + 8 * i) 8 (bv_unsigned w).

Lemma Z_land_upper_7 : forall a, 0 <= a -> Z.land a 7 <= 7.
Proof. intros a Ha. rewrite Z.land_comm. change 7 with (Z.ones 3). rewrite Z.land_ones_low || idtac.
  pose proof (Z.land_ones a 3 ltac:(lia)). rewrite Z.land_comm in H. rewrite H. change (Z.ones 3) with 7. pose proof (Z.mod_pos_bound a 8 ltac:(lia)). change (2^3) with 8. lia. Qed.

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Lemma art_uwf_loop : forall (m : nat) regs (M rom : word -> option byte) (this pc bp top size : Z),
  (Z.to_nat (top - bp) <= m)%nat ->
  getr regs 10 = Z_to_bv 64 this -> getr regs 11 = Z_to_bv 64 pc -> getr regs 12 = Z_to_bv 64 bp -> getr regs 13 = Z_to_bv 64 4096 ->
  getr regs 14 = Z_to_bv 64 (this + 16) -> getr regs 15 = Z_to_bv 64 size -> getr regs 8 = Z_to_bv 64 30 -> getr regs 9 = Z_to_bv 64 (top - 16) ->
  1 <= size <= 30 -> 0 <= pc < 2 ^ 64 -> 0 <= this -> this + 256 <= bp - 16 -> bp < top - 16 -> top < 2 ^ 63 -> bp mod 8 = 0 ->
  wrA M this 256 -> readable8 M (bp - 16) top -> cellA M (this + 8) 4 size -> trace_cells M this size ->
  exists regs' M',
    msteps ASEGS (mkst regs (0x80b74 : word) M rom) (mkst regs' (0x80bb0 : word) M' rom)
    /\ (forall r : reg, r <> 12%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> getr regs' r = getr regs r)
    /\ mem_grows M M'
    /\ (forall x : word, ~ (this + 8 <= U x < this + 12) -> ~ (this + 16 <= U x < this + 256) -> M' x = M x)
    /\ (exists sz, 1 <= sz <= 30 /\ cellA M' (this + 8) 4 sz /\ trace_cells M' this sz).
Proof.
  induction m as [|m IH]; intros regs M rom this pc bp top size Hm H10 H11 H12 H13 H14 H15 H8 H9 Hsz Hpc Hthis Hthis' Hbp Htop Hbp8 W RD CSZ TRC.
  { exfalso. lia. }
  destruct (Z.le_gt_cases 30 size) as [Full|Room].
  { (* [comment removed for export] *)
    eexists _, M. split; [|split; [|split; [apply mem_grows_refl | split; [intros; reflexivity | exists size; split; [lia | split; [exact CSZ | exact TRC]]]]]].
    - zbtk F_80b74 D_80b74. apply mst_refl.
    - intros; reflexivity. }
  pose proof RD as RDu. unfold readable8 in RDu.
  destruct (RDu (bp - 8) ltac:(lia) ltac:(lia) ltac:(lia)) as [w1 C1].
  destruct (RDu (bp - 16) ltac:(lia) ltac:(lia) ltac:(lia)) as [w2 C2].
  pose proof (u64_range w1) as R1. pose proof (u64_range w2) as R2.
  destruct (Z.lt_ge_cases (U w1) 4096) as [Lowpc|Okpc].
  { (* [comment removed for export] *)
    eexists _, M. split; [|split; [|split; [apply mem_grows_refl | split; [intros; reflexivity | exists size; split; [lia | split; [exact CSZ | exact TRC]]]]]].
    - zbft F_80b74 D_80b74. zld F_80b78 D_80b78 (bp - 8) C1. zbtk F_80b7c D_80b7c. apply mst_refl.
    - intros; kept_solve. }
  (* [comment removed for export] *)
  assert (STEP : exists regs1 M1,
      msteps ASEGS (mkst regs (0x80b74 : word) M rom) (mkst regs1 (0x80b98 : word) M1 rom)
      /\ getr regs1 10 = Z_to_bv 64 this /\ getr regs1 11 = Z_to_bv 64 pc /\ getr regs1 12 = Z_to_bv 64 bp /\ getr regs1 13 = Z_to_bv 64 4096
      /\ getr regs1 14 = Z_to_bv 64 (this + 16) /\ (exists size1, getr regs1 15 = Z_to_bv 64 size1 /\ size <= size1 <= size + 1)
      /\ getr regs1 8 = Z_to_bv 64 30 /\ getr regs1 9 = Z_to_bv 64 (top - 16)
      /\ (forall r : reg, r <> 12%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> getr regs1 r = getr regs r)
      /\ mem_grows M M1 /\ (forall x : word, ~ (this + 8 <= U x < this + 12) -> ~ (this + 16 <= U x < this + 256) -> M1 x = M x)
      /\ wrA M1 this 256 /\ readable8 M1 (bp - 16) top /\ (exists size1, size <= size1 <= size + 1 /\ cellA M1 (this + 8) 4 size1 /\ getr regs1 15 = Z_to_bv 64 size1 /\ trace_cells M1 this size1)).
  { destruct (Z.eq_dec (U w1) pc) as [Same|Diff].
    - eexists _, M. split.
      { zbft F_80b74 D_80b74. zld F_80b78 D_80b78 (bp - 8) C1. zbft F_80b7c D_80b7c. zbtk F_80b80 D_80b80. apply mst_refl. }
      repeat (split; [gres; rwH; first [reflexivity | f_equal; lia]|]). split. { exists size. split; [gres; rwH; reflexivity|lia]. }
      repeat (split; [gres; rwH; first [reflexivity | f_equal; lia]|]). split. { intros; kept_solve. }
      split; [apply mem_grows_refl|]. split; [intros; reflexivity|]. split; [assumption|]. split; [assumption|]. exists size. split; [lia|]. split; [exact CSZ | split; [gres; rwH; reflexivity | exact TRC]].
    - eexists _, _. split.
      { zbft F_80b74 D_80b74. zld F_80b78 D_80b78 (bp - 8) C1. zbft F_80b7c D_80b7c. zbft F_80b80 D_80b80.
        zstep F_80b84 D_80b84. zstep F_80b88 D_80b88. zstep F_80b8c D_80b8c.
        zsw F_80b90 D_80b90 (this + 8) (size + 1) ltac:(rewok W).
        zsd F_80b94 D_80b94 (this + 16 + size * 8) (U w1) ltac:(rewok W).
        apply mst_refl. }
      repeat (split; [gres; rwH; first [reflexivity | f_equal; lia]|]). split. { exists (size + 1). split; [gres; rwH; first [reflexivity | f_equal; lia]|lia]. }
      repeat (split; [gres; rwH; first [reflexivity | f_equal; lia]|]). split. { intros; kept_solve. }
      split. { eapply mem_grows_trans; apply Wn_grows. }
      split. { intros x Hx Hx'. rewrite !Wn_outside by (cbn; lia). reflexivity. }
      split. { zwr. }
      split. { apply readable8_Wn; try (cbn; lia). apply readable8_Wn; try (cbn; lia). exact RD. }
      exists (size + 1). split; [lia|]. split; [|split; [gres; rwH; f_equal; lia|]].
      { apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]. apply cell_Wn_hit; cbn; lia. }
      intros i Hi. destruct (Z.eq_dec i size) as [->|Hne].
      + exists w1. replace (this + 16 + 8 * size) with (this + 16 + size * 8) by lia. apply cell_Wn_hit; cbn; lia.
      + destruct (TRC i ltac:(lia)) as [w Cw]. exists w.
        apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]. apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]. exact Cw. }
  destruct STEP as (regs1 & M1 & RUN1 & P10 & P11 & P12 & P13 & P14 & (size1 & P15 & Hs1) & P8 & P9 & K1 & G1 & A1 & W1 & RD1 & (size1' & Hs1' & CS1 & P15' & TRC1)).
  assert (Esz : size1' = size1). { rewrite P15 in P15'. apply (f_equal bv_unsigned) in P15'. rewrite !art_u_lit in P15' by lia. lia. } subst size1'.
  assert (C2' : cellA M1 (bp - 16) 8 (U w2)).
  { apply (cell_agree M M1); [|lia|cbn; lia|exact C2]. intros x Hx. apply A1; cbn in Hx; lia. }
  (* [comment removed for export] *)
  destruct (Z.le_gt_cases (U w2) bp) as [Back|Fwd].
  { eexists _, M1. split; [|split; [|split; [exact G1 | split; [exact A1 | exists size1; split; [lia | split; [exact CS1 | exact TRC1]]]]]].
    - eapply msteps_trans; [exact RUN1|]. zld F_80b98 D_80b98 (bp - 16) C2'. zbtk F_80b9c D_80b9c. apply mst_refl.
    - intros; rewrite <- (K1 r) by assumption; kept_solve. }
  destruct (Z.le_gt_cases (top - 16) (U w2)) as [High|Inr].
  { eexists _, M1. split; [|split; [|split; [exact G1 | split; [exact A1 | exists size1; split; [lia | split; [exact CS1 | exact TRC1]]]]]].
    - eapply msteps_trans; [exact RUN1|]. zld F_80b98 D_80b98 (bp - 16) C2'. zbft F_80b9c D_80b9c. zbtk F_80ba0 D_80ba0. apply mst_refl.
    - intros; rewrite <- (K1 r) by assumption; kept_solve. }
  destruct (Z.eq_dec (U w2 mod 8) 0) as [Al|Nal].
  - (* [comment removed for export] *)
    assert (Hland : Z.land (U w2) 7 = 0). { change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact Al. }
    assert (RUNm : exists regs2, msteps ASEGS (mkst regs1 (0x80b98 : word) M1 rom) (mkst regs2 (0x80b74 : word) M1 rom)
              /\ getr regs2 10 = Z_to_bv 64 this /\ getr regs2 11 = Z_to_bv 64 pc /\ getr regs2 12 = Z_to_bv 64 (U w2) /\ getr regs2 13 = Z_to_bv 64 4096
              /\ getr regs2 14 = Z_to_bv 64 (this + 16) /\ getr regs2 15 = Z_to_bv 64 size1 /\ getr regs2 8 = Z_to_bv 64 30 /\ getr regs2 9 = Z_to_bv 64 (top - 16)
              /\ (forall r : reg, r <> 12%bv -> r <> 16%bv -> r <> 17%bv -> getr regs2 r = getr regs1 r)).
    { eexists. split.
      { zld F_80b98 D_80b98 (bp - 16) C2'. zbft F_80b9c D_80b9c. zbft F_80ba0 D_80ba0.
        stepn F_80ba4 D_80ba4. rwH. rewrite art_zb_andi by lia. rewrite Hland.
        zstep F_80ba8 D_80ba8. zbtk F_80bac D_80bac. apply mst_refl. }
      repeat (split; [gres; rwH; first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity | f_equal; lia]|]). intros; kept_solve. }
    destruct RUNm as (regs2 & RUNm & T10 & T11 & T12 & T13 & T14 & T15 & T8 & T9 & Km).
    destruct (IH regs2 M1 rom this pc (U w2) top size1 ltac:(lia) T10 T11 T12 T13 T14 T15 T8 T9
                ltac:(lia) Hpc Hthis ltac:(lia) ltac:(lia) Htop Al W1
                ltac:(intros b Hb1 Hb2 Hb3; unfold readable8 in RD1; apply RD1; lia) CS1 TRC1) as (regs' & M' & RUN2 & K2 & G2 & A2 & SZ2).
    exists regs', M'. split; [|split; [|split; [|split]]].
    + eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUNm|]. exact RUN2.
    + intros r N12 N15 N16 N17. rewrite K2 by assumption. rewrite Km by assumption. apply K1; assumption.
    + eapply mem_grows_trans; [exact G1 | exact G2].
    + intros x Hx Hx'. rewrite A2 by assumption. apply A1; assumption.
    + exact SZ2.
  - (* [comment removed for export] *)
    assert (Hland : Z.land (U w2) 7 <> 0). { change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact Nal. }
    pose proof (Z_land_upper_7 (U w2) ltac:(lia)) as Lu. pose proof (proj2 (Z.land_nonneg (U w2) 7) ltac:(left; lia)) as Ln.
    eexists _, M1. split; [|split; [|split; [exact G1 | split; [exact A1 | exists size1; split; [lia | split; [exact CS1 | exact TRC1]]]]]].
    + eapply msteps_trans; [exact RUN1|]. zld F_80b98 D_80b98 (bp - 16) C2'. zbft F_80b9c D_80b9c. zbft F_80ba0 D_80ba0.
      stepn F_80ba4 D_80ba4. rwH. rewrite art_zb_andi by lia.
      zstep F_80ba8 D_80ba8.
      stepb_ft F_80bac D_80bac ltac:(rwH; rewrite art_c_eq_zb by lia; apply Z.eqb_neq; exact Hland).
      apply mst_refl.
    + intros; rewrite <- (K1 r) by assumption; kept_solve.
Qed.

End FPX.

Lemma Z_to_le_bytes_add : forall n1 n2 z, Z_to_le_bytes (n1 + n2) z = Z_to_le_bytes n1 z ++ Z_to_le_bytes n2 (Z.shiftr z (8 * Z.of_nat n1)).
Proof.
  induction n1 as [|n1 IH]; intros n2 z.
  - cbn [Nat.add app Z.of_nat Z.mul]. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [Nat.add Z_to_le_bytes app]. f_equal. rewrite IH. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma cell8_of_cells4 : forall M a lo hi, 0 <= a -> a + 8 < 2 ^ 64 -> 0 <= lo < 2 ^ 32 -> 0 <= hi < 2 ^ 32 ->
  cellA M a 4 lo -> cellA M (a + 4) 4 hi -> cellA M a 8 (lo + hi * 2 ^ 32).
Proof.
  intros M a lo hi Ha Ha' Hlo Hhi C1 C2. unfold cell in *.
  change 8%nat with (4 + 4)%nat. erewrite rdn_app; [|exact C1|].
  2: { replace (Z_to_bv 64 a + nat_to_word 4)%bv with (Z_to_bv 64 (a + 4) : word); [exact C2|].
       apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
       rewrite (Z.mod_small 4) by lia. rewrite (Z.mod_small a) by lia. rewrite Z.mod_small by lia. reflexivity. }
  f_equal. unfold word_to_le_bytes. rewrite !art_u_lit by lia. rewrite (Z_to_le_bytes_add 4 4). f_equal.
  - rewrite <- (Z_to_le_bytes_wrap 4 32 (lo + hi * 2 ^ 32)) by (cbn; lia). rewrite <- (Z_to_le_bytes_wrap 4 32 lo) by (cbn; lia). f_equal.
    unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). rewrite Z.mod_add by lia. reflexivity.
  - f_equal. change (8 * Z.of_nat 4) with 32. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

Section FPX2. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Lemma art_unwind_fast_run : forall regs (M rom : word -> option byte) (raw : word) (sp this pc bp top bot : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 this -> getr regs 11 = Z_to_bv 64 pc ->
  getr regs 12 = Z_to_bv 64 bp -> getr regs 13 = Z_to_bv 64 top -> getr regs 14 = Z_to_bv 64 bot -> getr regs 15 = Z_to_bv 64 30 ->
  64 <= sp -> sp + 64 <= this -> this + 2064 <= bp - 16 -> 0 <= bot -> bot < bp -> bp < top - 16 -> top < 2 ^ 63 -> bp mod 8 = 0 -> 0 <= pc < 2 ^ 64 ->
  0x634000 + 64 <= sp ->
  wrA M (sp - 64) 64 -> wrA M this 256 -> readable8 M (bp - 16) top -> cellA M 0xd64a8 8 0x16e1e0 -> cellA M 0x16e1e0 8 4096 ->
  exists regs' M',
    msteps ASEGS (mkst regs (0x80ab4 : word) M rom) (mkst regs' raw M' rom)
    /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 1 = raw
    /\ (forall r : reg, In r [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 3; 4]%bv -> getr regs' r = getr regs r)
    /\ mem_grows M M'
    /\ (forall x : word, ~ (this + 8 <= U x < this + 12) -> ~ (this + 16 <= U x < this + 256) -> ~ (sp - 64 <= U x < sp) -> M' x = M x)
    /\ (exists sz, 1 <= sz <= 30 /\ cellA M' (this + 8) 4 sz /\ trace_cells M' this sz).
Proof.
  intros regs M rom raw sp this pc bp top bot H1 Hret H2 H10 H11 H12 H13 H14 H15 Hsp Hsp' Hthis Hbot Hbot' Hbp Htop Hbp8 Hpc IMG W Wt RD Cg Cps.
  assert (PRE : exists regs1 M1, msteps ASEGS (mkst regs (0x80ab4 : word) M rom) (mkst regs1 (0x80b74 : word) M1 rom)
     /\ getr regs1 10 = Z_to_bv 64 this /\ getr regs1 11 = Z_to_bv 64 pc /\ getr regs1 12 = Z_to_bv 64 bp /\ getr regs1 13 = Z_to_bv 64 4096
     /\ getr regs1 14 = Z_to_bv 64 (this + 16) /\ getr regs1 15 = Z_to_bv 64 1 /\ getr regs1 8 = Z_to_bv 64 30 /\ getr regs1 9 = Z_to_bv 64 (top - 16)
     /\ getr regs1 2 = Z_to_bv 64 (sp - 64)
     /\ (forall r : reg, In r [3; 4; 23; 24; 25; 26; 27]%bv -> getr regs1 r = getr regs r)
     /\ M1 = Wn 8 (Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18)))
               (sp - 40) (U (getr regs 19))) (sp - 48) (U (getr regs 20))) (sp - 56) (U (getr regs 21))) (sp - 64) (U (getr regs 22))) (this + 8) 1) (this + 16) pc).
  { eexists _, _. split.
    - zstep F_80ab4 D_80ab4.
      zsd F_80ab8 D_80ab8 (sp - 8) (U raw) ltac:(rewok W). zsd F_80abc D_80abc (sp - 16) (U (getr regs 8)) ltac:(rewok W).
      zsd F_80ac0 D_80ac0 (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_80ac4 D_80ac4 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
      zsd F_80ac8 D_80ac8 (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_80acc D_80acc (sp - 48) (U (getr regs 20)) ltac:(rewok W).
      zsd F_80ad0 D_80ad0 (sp - 56) (U (getr regs 21)) ltac:(rewok W). zsd F_80ad4 D_80ad4 (sp - 64) (U (getr regs 22)) ltac:(rewok W).
      zstep F_80ad8 D_80ad8. zstep F_80adc D_80adc. zstep F_80ae0 D_80ae0. zstep F_80ae4 D_80ae4.
      zbft F_80ae8 D_80ae8.
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cg' : cellA X 0xd64a8 8 0x16e1e0) by (recell Cg); assert (Cps' : cellA X 0x16e1e0 8 4096) by (recell Cps) end.
      zstep F_80aec D_80aec. zld F_80af0 D_80af0 0xd64a8 Cg'. zld F_80af4 D_80af4 0x16e1e0 Cps'.
      zbft F_80af8 D_80af8.
      zstep F_80afc D_80afc.
      stepn F_80b00 D_80b00. rwH. rewrite art_zb_srli by lia.
      zsw F_80b04 D_80b04 (this + 8) 1 ltac:(rewok Wt).
      zsd F_80b08 D_80b08 (this + 16) pc ltac:(rewok Wt).
      assert (Htop12 : 1 <= top / 2 ^ 12) by (apply Z.div_le_lower_bound; lia). assert (Htop12' : top / 2 ^ 12 < 2 ^ 52) by (apply Z.div_lt_upper_bound; lia). pose proof (art_u_lit top ltac:(lia)).
      zbtk F_80b0c D_80b0c.
      zbft F_80b54 D_80b54. zbft F_80b58 D_80b58.
      zstep F_80b5c D_80b5c.
      zbft F_80b60 D_80b60.
      stepn F_80b64 D_80b64. rwH. rewrite art_zb_andi by lia. replace (Z.land bp 7) with 0 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; lia).
      zbft F_80b68 D_80b68.
      zstep F_80b6c D_80b6c. zstep F_80b70 D_80b70.
      apply mst_refl.
    - repeat (split; [gres; rwH; first [reflexivity | f_equal; lia]|]).
      split. { intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; gres; reflexivity. } reflexivity. }
  destruct PRE as (regs1 & M1 & RUN1 & P10 & P11 & P12 & P13 & P14 & P15 & P8 & P9 & P2 & PK & EM1).
  assert (W1 : wrA M1 this 256) by (rewrite EM1; zwr).
  assert (RD1 : readable8 M1 (bp - 16) top).
  { rewrite EM1. do 10 (apply readable8_Wn; [cbn; lia|cbn; lia|lia|lia|cbn; lia|]). exact RD. }
  destruct (art_uwf_loop (Z.to_nat (top - bp)) regs1 M1 rom this pc bp top 1 ltac:(lia) P10 P11 P12 P13 P14 P15 P8 P9
              ltac:(lia) Hpc ltac:(lia) ltac:(lia) Hbp Htop Hbp8 W1 RD1 ltac:(rewrite EM1; zcell)
              ltac:(intros i Hi; exists (Z_to_bv 64 pc); rewrite art_u_lit by lia; replace (this + 16 + 8 * i) with (this + 16) by lia; rewrite EM1; zcell)) as (regs2 & M2 & RUN2 & K2 & G2 & A2 & SZ2).
  (* [comment removed for export] *)
  assert (FR : forall off v, 0 <= off <= 56 -> cellA M1 (sp - 64 + off) 8 v -> cellA M2 (sp - 64 + off) 8 v).
  { intros off v Hoff C. apply (cell_agree M1 M2); [|lia|cbn; lia|exact C]. intros x Hx. apply A2; cbn in Hx; lia. }
  assert (C56 : cellA M2 (sp - 64 + 56) 8 (U raw)) by (apply FR; [lia|]; rewrite EM1; replace (sp - 64 + 56) with (sp - 8) by lia; zcell).
  assert (C48 : cellA M2 (sp - 64 + 48) 8 (U (getr regs 8))) by (apply FR; [lia|]; rewrite EM1; replace (sp - 64 + 48) with (sp - 16) by lia; zcell).
  assert (C40 : cellA M2 (sp - 64 + 40) 8 (U (getr regs 9))) by (apply FR; [lia|]; rewrite EM1; replace (sp - 64 + 40) with (sp - 24) by lia; zcell).
  assert (C32 : cellA M2 (sp - 64 + 32) 8 (U (getr regs 18))) by (apply FR; [lia|]; rewrite EM1; replace (sp - 64 + 32) with (sp - 32) by lia; zcell).
  assert (C24 : cellA M2 (sp - 64 + 24) 8 (U (getr regs 19))) by (apply FR; [lia|]; rewrite EM1; replace (sp - 64 + 24) with (sp - 40) by lia; zcell).
  assert (C16 : cellA M2 (sp - 64 + 16) 8 (U (getr regs 20))) by (apply FR; [lia|]; rewrite EM1; replace (sp - 64 + 16) with (sp - 48) by lia; zcell).
  assert (C08 : cellA M2 (sp - 64 + 8) 8 (U (getr regs 21))) by (apply FR; [lia|]; rewrite EM1; replace (sp - 64 + 8) with (sp - 56) by lia; zcell).
  assert (C00 : cellA M2 (sp - 64 + 0) 8 (U (getr regs 22))) by (apply FR; [lia|]; rewrite EM1; replace (sp - 64 + 0) with (sp - 64) by lia; zcell).
  assert (Q2 : getr regs2 2 = Z_to_bv 64 (sp - 64)) by (rewrite K2 by discriminate; exact P2).
  eexists _, M2. split.
  { eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
    zld F_80bb0 D_80bb0 (sp - 64 + 56) C56. rewrite Z_to_bv_bv_unsigned.
    zld F_80bb4 D_80bb4 (sp - 64 + 48) C48. rewrite Z_to_bv_bv_unsigned.
    zld F_80bb8 D_80bb8 (sp - 64 + 40) C40. rewrite Z_to_bv_bv_unsigned.
    zld F_80bbc D_80bbc (sp - 64 + 32) C32. rewrite Z_to_bv_bv_unsigned.
    zld F_80bc0 D_80bc0 (sp - 64 + 24) C24. rewrite Z_to_bv_bv_unsigned.
    zld F_80bc4 D_80bc4 (sp - 64 + 16) C16. rewrite Z_to_bv_bv_unsigned.
    zld F_80bc8 D_80bc8 (sp - 64 + 8) C08. rewrite Z_to_bv_bv_unsigned.
    zld F_80bcc D_80bcc (sp - 64 + 0) C00. rewrite Z_to_bv_bv_unsigned.
    zstep F_80bd0 D_80bd0.
    stepret F_80bd4 D_80bd4 raw ltac:(rwH; reflexivity).
    apply mst_refl. }
  split. { gres. f_equal. lia. }
  split. { gres. reflexivity. }
  split. { intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]; gres;
           first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity | rewrite K2 by discriminate; apply PK; cbn; tauto]. }
  split. { eapply mem_grows_trans; [|exact G2]. rewrite EM1. repeat (eapply mem_grows_trans; [|apply Wn_grows]). apply mem_grows_refl. }
  split. { intros x N1 N2 N3. rewrite A2 by assumption. rewrite EM1. rewrite !Wn_outside by (cbn; lia). reflexivity. }
  exact SZ2.
Qed.

(* [comment removed for export] *)
Lemma art_unwind_fn : forall regs (M rom : word -> option byte) (raw : word) (sp this pc bp top bot : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 this -> getr regs 11 = Z_to_bv 64 30 -> getr regs 12 = Z_to_bv 64 pc ->
  getr regs 13 = Z_to_bv 64 bp -> getr regs 14 = Z_to_bv 64 0 -> getr regs 15 = Z_to_bv 64 top -> getr regs 16 = Z_to_bv 64 bot -> getr regs 17 = Z_to_bv 64 1 ->
  64 <= sp -> sp < 2 ^ 64 -> 0 <= this -> this + 2064 < 2 ^ 64 -> 0 <= bp < 2 ^ 64 -> apart (sp - 64) 64 this 2064 ->
  wrA M (sp - 64) 64 -> wrA M this 2064 ->
  msteps ASEGS (mkst regs (0x81110 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 5 (Z_to_bv 64 (this + 2047))) 6 (Z_to_bv 64 bp)) 8 (getr regs 8)) 9 (getr regs 9)) 11 (Z_to_bv 64 pc)) 12 (Z_to_bv 64 bp)) 13 (Z_to_bv 64 top)) 14 (Z_to_bv 64 bot)) 15 (Z_to_bv 64 30)) 18 (getr regs 18)) 19 (getr regs 19)) 20 (getr regs 20)) 21 (getr regs 21)) (0x80ab4 : word) (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18))) (sp - 40) (U (getr regs 19))) (sp - 48) (U (getr regs 20))) (sp - 56) (U (getr regs 21))) (this + 2056) bp) rom).
Proof.
  intros regs M rom raw sp this pc bp top bot H1 H2 H10 H11 H12 H13 H14 H15 H16 H17 Hsp Hsp' Hthis Hthis' Hbp Ap W Wt.
  zstep F_81110 D_81110.
  zsd F_81114 D_81114 (sp - 8) (U raw) ltac:(rewok W). zsd F_81118 D_81118 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_8111c D_8111c (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_81120 D_81120 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_81124 D_81124 (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_81128 D_81128 (sp - 48) (U (getr regs 20)) ltac:(rewok W).
  zsd F_8112c D_8112c (sp - 56) (U (getr regs 21)) ltac:(rewok W).
  zstep F_81130 D_81130. zstep F_81134 D_81134. zstep F_81138 D_81138. zstep F_8113c D_8113c.
  stepn F_81140 D_81140. rwH. rewrite art_zb_and by lia. rewrite art_land_full_l by lia.
  zstep F_81144 D_81144.
  zsd F_81148 D_81148 (this + 2056) bp ltac:(rewok Wt).
  zbft F_8114c D_8114c. zbtk F_81150 D_81150. zbtk F_81188 D_81188.
  zstep F_811f0 D_811f0. zstep F_811f4 D_811f4. zstep F_811f8 D_811f8. zstep F_811fc D_811fc. zstep F_81200 D_81200.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (C56 : cellA X (sp - 8) 8 (U raw)) by zcell; assert (C48 : cellA X (sp - 16) 8 (U (getr regs 8))) by zcell;
    assert (C40 : cellA X (sp - 24) 8 (U (getr regs 9))) by zcell; assert (C32 : cellA X (sp - 32) 8 (U (getr regs 18))) by zcell;
    assert (C24 : cellA X (sp - 40) 8 (U (getr regs 19))) by zcell; assert (C16 : cellA X (sp - 48) 8 (U (getr regs 20))) by zcell;
    assert (C08 : cellA X (sp - 56) 8 (U (getr regs 21))) by zcell end.
  zld F_81204 D_81204 (sp - 8) C56. rewrite Z_to_bv_bv_unsigned.
  zld F_81208 D_81208 (sp - 16) C48. rewrite Z_to_bv_bv_unsigned.
  zld F_8120c D_8120c (sp - 24) C40. rewrite Z_to_bv_bv_unsigned.
  zld F_81210 D_81210 (sp - 32) C32. rewrite Z_to_bv_bv_unsigned.
  zld F_81214 D_81214 (sp - 40) C24. rewrite Z_to_bv_bv_unsigned.
  zld F_81218 D_81218 (sp - 48) C16. rewrite Z_to_bv_bv_unsigned.
  zld F_8121c D_8121c (sp - 56) C08. rewrite Z_to_bv_bv_unsigned.
  zstep F_81220 D_81220.
  stepn F_81224 D_81224.
  zret.
Qed.
End FPX2.

Lemma Wn8_zero_split : forall M a, 0 <= a -> a + 8 < 2 ^ 64 -> Wn 8 M a 0 = Wn 4 (Wn 4 M a 0) (a + 4) 0.
Proof.
  intros M a Ha Ha'. unfold Wn. change (word_to_le_bytes 8 (Z_to_bv 64 0)) with (word_to_le_bytes 4 (Z_to_bv 64 0) ++ word_to_le_bytes 4 (Z_to_bv 64 0)).
  rewrite RefMemcpyLib.wbytes_app. f_equal. rewrite length_N_to_le_bytes. unfold at_. rewrite art_u_lit by lia. reflexivity.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
