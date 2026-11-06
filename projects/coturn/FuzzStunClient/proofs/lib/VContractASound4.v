(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool String Lia.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import Hoare SeqExec RefMemcpyLib ZStores.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VAbs VAbsSound VAbsSound2 VAbsSound3 VStep VStepMem VStepSound VStepMemSound VStepMemSound2 VCert VContract VContractSound VContractSound2 VContractSound4 VState2 VStepMem2 VGamma2 VStepMem2SoundA VStepMem2SoundB VStepMem2SoundC VStepMem2SoundD VContractA VCert2 VContract2 VContract2Iface VContractASound1 VContractASound2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Stdlib.micromega.Lia.lia ::= first [ flia2 | Zify.zify; xlia zchecker ].  (* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition JUNK4 : Z := 2216.

Lemma arith_shd4 (e vf spoff t : Z) :
  e = 8 * (e / 8) -> 17594333495296 <= e - vf -> e + 16 <= 2 ^ 47 -> - vf <= spoff - 2224 -> 0 <= t <= e - 1 ->
  2147450880 + t / 8 + 8 < e + spoff - JUNK4.
Proof.
  intros. unfold JUNK4. pose proof (div8_facts t). pose proof (div8_facts (e - 1)).
  assert (t / 8 <= (e - 1) / 8) by (apply Z.div_le_mono; lia). lia.
Qed.

Lemma arith_shd4_low (e vf spoff t : Z) :
  17594333495296 <= e - vf -> - vf <= spoff - 2224 -> 0 <= t <= 2 ^ 47 - 2 ->
  2147450880 + t / 8 + 8 < e + spoff - JUNK4.
Proof. intros. unfold JUNK4. pose proof (div8_facts t). lia. Qed.

(* [comment removed for export] *)
Lemma word_floor_mono (S a b : Z) : a <= b -> (S + a / 8) / 8 * 8 <= (S + b / 8) / 8 * 8.
Proof.
  intros H. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|]. apply Z.add_le_mono_l. apply Z.div_le_mono; lia.
Qed.
Lemma word_floor_range (S q : Z) : 0 <= S -> 0 <= q < 2 ^ 47 -> S + 2 ^ 44 + 8 <= 2 ^ 64 ->
  0 <= (S + q / 8) / 8 * 8 /\ (S + q / 8) / 8 * 8 + 8 <= 2 ^ 64.
Proof. intros. pose proof (div8_facts q). pose proof (div8_facts (S + q / 8)). lia. Qed.

(* [comment removed for export] *)
Section S.
  Variable SEGS : list Segment.
  Variable P : vparams2.
  Variable E : venv2.
  Variables mem0 rom : word -> option byte.
  Variable CI : cimg.
  Let P1 := p1 P.
  Let E1 := ev1 E.
  Hypothesis PO2 : params_ok2 SEGS P.
  #[warnings="-notation-for-abbreviation"] Notation gamma2P := (gamma2 SEGS P E mem0).
  Hypothesis SHOFF : vp_shoff P = SBz.
  Hypothesis ROM_HI : forall a : word, SBz <= bv_unsigned a -> seg_rom SEGS a = None.
  (* [comment removed for export] *)
  Hypothesis FSLEN : forall len ssl, vp_fs P = Some (len, ssl) -> FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL < len.
  (* [comment removed for export] *)
  Definition acc_facts (mem : word -> option byte) (x n : Z) : Prop :=
       (forall g, x / 8 <= g < (x + n - 1) / 8 -> mem (wordZ (SBz + g)) = Some (Z_to_bv 8 0))
    /\ (exists b1 : byte, mem (wordZ (SBz + (x + n - 1) / 8)) = Some b1
                          /\ (bv_unsigned b1 = 0 \/ (x + n - 1) mod 8 < bv_unsigned b1 < 8))
    /\ (exists w : word, rdn SEGS mem (wordZ ((SBz + x / 8) / 8 * 8)) 8 = Some (word_to_le_bytes 8 w))
    /\ (exists w : word, rdn SEGS mem (wordZ ((SBz + (x + n - 1) / 8) / 8 * 8)) 8 = Some (word_to_le_bytes 8 w)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="SHOFF ROM_HI FSLEN"] Lemma rgn_range_facts A nu regs mem B r lo hi ov n :
    gamma2P A nu regs mem -> rgn_get (vs_rgn A) B = Some r ->
    match vr_kind r with RK_fake _ _ | RK_arg => True | _ => False end ->
    vr_lo r <= lo -> hi <= vr_hi r ->
    rgn_addressable A r lo hi = true -> frames_shadow_zone_ok P = true ->
    lo <= ov -> ov + n <= hi -> 0 <= n ->
    let x := rbase nu r + ov in
    (0 < n -> acc_facts mem x n)
    /\ (exists fa cid, 0 <= cid <= 4 /\ e_fs E + FS_FRAMES <= fa /\ fa + fake_size cid <= e_fs E + FS_FRAMES + 5 * 2 ^ 20
          /\ fa <= rbase nu r + lo /\ rbase nu r + hi <= fa + fake_size cid
          /\ (match vr_kind r with
              | RK_fake c _ => c = cid /\ fa = rbase nu r /\ exists pos, 0 <= pos < fs_nframes cid /\ fa = frame_addr (e_fs E) cid pos /\ ~ In (cid, pos) (e_live E)
              | _ => exists pos, In (cid, pos) (e_live E) /\ 0 <= pos < fs_nframes cid /\ fa = frame_addr (e_fs E) cid pos end))
    /\ vp_fs P <> None
    /\ (0 <= rbase nu r + lo /\ rbase nu r + hi <= 2 ^ 47 - 1 /\ band_ok (rbase nu r + lo) (hi - lo))   (* [comment removed for export] *)
    /\ (forall i, lo <= i < hi -> exists b, rdn SEGS mem (wordZ (rbase nu r + i)) 1 = Some [b]).
  Proof.
    intros HG2 HGr HK RLO RHI HRA HFZ H1 H2 Hn x.
    pose proof HG2 as (HG1 & HE & HM & HF2 & HDD & RGN & LIVE & BEL2 & GL2 & FI2 & MOK).
    pose proof (gamma2_lgamma _ _ _ _ _ _ _ _ HG2) as HL.
    pose proof HE as (HEV1 & _ & HFS & HZO & HKC).
    pose proof (rgn_get_in _ _ _ HGr) as [Hr HBr].
    pose proof (RGN r Hr) as ROK. pose proof ROK as (RB1 & RB2 & RB3 & RDS & CELLS & PERM & NUL & KIND).
    assert (ND : is_data_shadow r = false) by (unfold is_data_shadow; destruct (vr_kind r); auto; contradiction).
    unfold env_fs in HFS.
    assert (FSnz : vp_fs P <> None) by (unfold kind_ok in KIND; destruct (vr_kind r); try contradiction; exact (proj1 KIND)).
    destruct (vp_fs P) as [[flen fssl]|] eqn:EFS; [|exfalso; exact (FSnz eq_refl)].
    destruct HFS as (_ & FS1 & FS2 & FS3 & FS4 & _ & _ & APsf & APdf & APds & HMsp & HMd & _ & SPHI & _).
    pose proof (FSLEN _ _ eq_refl) as FS5. clear APdf APds HMd. unfold HIGH_MEM_BEG, HIGH_MEM_END, FS_NCLASSES, FS_SSL in *.
    assert (FR : exists fa cid, 0 <= cid <= 4 /\ e_fs E + FS_FRAMES <= fa /\ fa + fake_size cid <= e_fs E + FS_FRAMES + 5 * 2 ^ 20
                  /\ fa <= rbase nu r + lo /\ rbase nu r + hi <= fa + fake_size cid
                  /\ (match vr_kind r with
                      | RK_fake c _ => c = cid /\ fa = rbase nu r /\ exists pos, 0 <= pos < fs_nframes cid /\ fa = frame_addr (e_fs E) cid pos /\ ~ In (cid, pos) (e_live E)
                      | _ => exists pos, In (cid, pos) (e_live E) /\ 0 <= pos < fs_nframes cid /\ fa = frame_addr (e_fs E) cid pos end)
                  /\ vr_base r <> SP0 /\ vr_base r <> DATA /\ vr_base r <> FSB).
    { unfold kind_ok in KIND. destruct (vr_kind r) as [cid fl| | | |] eqn:Kr; try contradiction.
      - destruct KIND as (_ & Hcid & VLO & VHI & LF & pos & Hpos & Ebeta & _ & _ & NL & _).
        destruct (frame_in_area (e_fs E) cid pos Hcid Hpos) as [G1 G2].
        exists (frame_addr (e_fs E) cid pos), cid. rewrite <- Ebeta.
        split; [exact Hcid|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [split; [reflexivity|]; split; [reflexivity|]; exists pos; auto|].
        split; [|split]; intros X; rewrite X in LF; cbv in LF; discriminate.
      - destruct KIND as (_ & (cid & pos & Hlive & G3 & G4) & (i & Hi & EB & _)).
        pose proof (live_valid _ _ _ HE ltac:(rewrite EFS; discriminate) Hlive) as [Vc Vp]. cbn in Vc, Vp.
        destruct (frame_in_area (e_fs E) cid pos ltac:(lia) ltac:(lia)) as [G1 G2].
        exists (frame_addr (e_fs E) cid pos), cid. rewrite EB.
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exists pos; repeat split; auto; lia|].
        unfold ASYM2, SP0, DATA, FSB. split; [|split]; intros X; apply (f_equal Z.pos) in X; rewrite Z2Pos.id in X by lia; lia. }
    destruct FR as (fa & cid & Hcid & FA1 & FA2 & FA3 & FA4 & FK & NB1 & NB2 & NB3).
    split; [|split; [exists fa, cid; split; [exact Hcid|]; split; [exact FA1|]; split; [exact FA2|]; split; [exact FA3|]; split; [exact FA4|exact FK]|]].
    2:{ split; [intros X; discriminate X|].
        split; [split; [unfold FS_FRAMES in *; lia|split; [unfold FS_FRAMES in *; lia|]]|].
        { apply (band_ok_sub (e_fs E) flen _ _ (proj2 FS1)); unfold HIGH_MEM_END; unfold FS_FRAMES in *; lia. }
        intros i Hi. destruct (PERM ND) as [RDp _]. exact (proj2 (RDp i ltac:(lia))). }
    intros Hn0.
    assert (DRANGE : fa <= x /\ x + n <= fa + fake_size cid /\ 0 <= x /\ x + n <= 2 ^ 47 - 1).
    { unfold x. unfold FS_FRAMES in *. lia. }
    (* [comment removed for export] *)
    unfold rgn_addressable in HRA.
    destruct (rgn_shadow_of (vs_rgn A) (vr_base r)) as [sh|] eqn:SH; [|discriminate].
    destruct (rgn_shadow_of_in _ _ _ SH) as [Hsh Ksh].
    destruct (rgn_residue A r) as [rB|] eqn:RES; [|discriminate].
    pose proof (RGN sh Hsh) as (_ & _ & _ & _ & _ & _ & _ & KINDsh). unfold kind_ok in KINDsh. rewrite Ksh in KINDsh.
    destruct KINDsh as (_ & DISPsh & _ & _ & _ & KX). destruct (KX NB1 NB2 NB3) as (ro & Gro & B8 & KM).
    rewrite <- HBr in HGr. rewrite HGr in Gro. injection Gro as <-.
    set (Ssh := nu (vr_base sh)) in *.
    assert (RBsh : rbase nu sh = SBz + Ssh) by (unfold rbase; rewrite DISPsh, SHOFF; reflexivity).
    assert (GRID : rbase nu r = 8 * Ssh + rB /\ 0 <= rB < 8).
    { unfold rgn_residue in RES. unfold kind_ok in KIND. destruct (vr_kind r) as [cid' fl| | | |] eqn:Kr; try discriminate.
      - injection RES as <-. lia.
      - destruct (Z.eqb_spec (vr_disp r) 0) as [D0|]; [|discriminate].
        destruct (base_res8_sound A nu _ _ HL RES) as [HrB [k Hk]]. destruct KM as (ES & _).
        unfold rbase in ES |- *. rewrite D0 in *. rewrite Hk in ES |- *.
        replace ((0 + (8 * k + rB)) / 8) with k in ES by (symmetry; replace (0 + (8 * k + rB)) with (rB + k * 8) by lia; rewrite Z.div_add by lia; rewrite Z.div_small by lia; lia).
        lia. }
    destruct GRID as [GRID HrB].
    assert (GR : forall g, (lo + rB) / 8 <= g <= (hi + rB - 1) / 8 ->
      exists k : byte, mem (wordZ (SBz + Ssh + g)) = Some k
                       /\ (bv_unsigned k = 0 \/ Z.min (hi + rB) (8 * g + 8) - 8 * g <= bv_unsigned k < 8)).
    { intros g Hg. destruct (range_granules_ok_sound sh (lo + rB) (hi + rB) g HRA ltac:(lia) Hg) as (b & SB & Hb).
      destruct (sh_byte_mem SEGS P E mem0 A nu regs mem sh g b HG2 Hsh ltac:(unfold is_shadow; rewrite Ksh; reflexivity) SB) as (k & Rk & Vk).
      rewrite RBsh in Rk. exists k. split; [|rewrite Vk; exact Hb].
      apply (rdn1_mem SEGS ROM_HI); [|exact Rk]. unfold SBz, FS_FRAMES in *.
      pose proof (div8_facts (lo + rB)). pose proof (div8_facts (hi + rB - 1)). (ltac2:(LK.k [@H1; @H2; @FS1; @FS2; @HBr; @FS5; @FA1; @FA2; @FA3; @FA4; @NB1; @NB2; @NB3; @Hn0; @DRANGE; @GRID; @Hg; @H; @H0]); lia). }
    assert (SHAD :
      (forall g, x / 8 <= g < (x + n - 1) / 8 -> mem (wordZ (SBz + g)) = Some (Z_to_bv 8 0))
      /\ (exists b1 : byte, mem (wordZ (SBz + (x + n - 1) / 8)) = Some b1
                           /\ (bv_unsigned b1 = 0 \/ (x + n - 1) mod 8 < bv_unsigned b1 < 8))).
    { unfold x. rewrite GRID. replace (8 * Ssh + rB + ov) with (8 * Ssh + (ov + rB)) by lia.
      apply (shadow_access mem Ssh (lo + rB) (hi + rB) (ov + rB) n GR); lia. }
    (* [comment removed for export] *)
    assert (NUE8 : nuE E FS8 = e_fs E / 8).
    { unfold nuE, fix_val2. replace (fix_val (ev1 E) FS8) with (@None Z) by reflexivity. reflexivity. }
    assert (WRD : forall q, fa <= q <= fa + fake_size cid - 1 ->
      exists w : word, rdn SEGS mem (wordZ ((SBz + q / 8) / 8 * 8)) 8 = Some (word_to_le_bytes 8 w)).
    { intros q Hq. unfold FS_FRAMES in *.
      destruct (arith_fs8_word (e_fs E) q FS3 ltac:(lia) ltac:(lia)) as [Wlo Whi]. pose proof (div8_facts (e_fs E)).
      apply (word_readable SEGS P E mem0 A nu regs mem _ HG2); [| unfold SBz in *; (ltac2:(LK.k [@FS1; @HBr; @NB1; @NB2; @NB3; @Wlo; @H; @FS2; @FS5; @FA1; @Hn0; @DRANGE; @Hq; @Whi]); lia) | unfold SBz in *; (ltac2:(LK.k [@FS1; @HBr; @NB1; @NB2; @NB3; @Wlo; @H; @FS2; @FS5; @FA1; @Hn0; @DRANGE; @Hq; @Whi]); lia)].
      intros i Hi. apply (zone_has_sound SEGS P E mem0 A nu regs mem FS8 _ _ _ HG2 HFZ). rewrite SHOFF, NUE8.
      unfold SBz, FS_FRAMES_G, FS_FRAMES_GLEN in *. (ltac2:(LK.k [@FS1; @HBr; @FA1; @NB1; @NB2; @NB3; @Hq; @Wlo; @Whi; @Hi]); lia). }
    split; [exact (proj1 SHAD)|]. split; [exact (proj2 SHAD)|]. split; apply WRD; lia.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="PO2 SHOFF ROM_HI FSLEN"] Lemma stack_range_facts A nu regs mem lo hi ov n :
    gamma2P A nu regs mem ->
    stack_addressable A lo hi = true -> stack_shadow_words_ok P lo hi = true ->
    lo <= ov -> ov + n <= hi -> - vp_frame P1 <= lo -> hi <= 0 -> 0 <= n ->
    let x := e_sp0 E1 + ov in
    (0 < n -> acc_facts mem x n)
    /\ vp_fs P <> None /\ HIGH_MEM_BEG <= e_sp0 E1 - vp_frame P1 /\ e_sp0 E1 + 16 <= HIGH_MEM_END /\ e_sp0 E1 = 8 * (e_sp0 E1 / 8)
    /\ (forall i, lo <= i < hi -> exists b, rdn SEGS mem (wordZ (e_sp0 E1 + i)) 1 = Some [b]).
  Proof.
    intros HG2 Hsa Hsw H1 H2 H3 H4 Hn x.
    pose proof HG2 as (HG1 & HE & HM & HF2 & HDD & RGN & LIVE & BEL2 & GL2 & FI2 & MOK).
    pose proof (gamma2_lgamma _ _ _ _ _ _ _ _ HG2) as HL. pose proof (PO1 _ _ PO2) as PO. pose proof PO as (P0 & Psphi & PS & PF & PW & PR & PP & PB).
    pose proof HE as (HEV1 & _ & HFS & HZO & HKC). pose proof HEV1 as (E1a & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E11 & E12).
    pose proof (proj1 (proj2 HG1)) as (MF & MD & MP & MFM).
    unfold stack_addressable in Hsa.
    destruct (rgn_shadow_of (vs_rgn A) SP0) as [sh|] eqn:SH; [|discriminate].
    destruct (rgn_shadow_of_in _ _ _ SH) as [Hsh Ksh].
    destruct (pm_get SP0 (scong (vs_store (v1 A)))) as [[cm cr]|]; [|discriminate].
    apply andb_prop in Hsa as [_ GRAN].
    pose proof (RGN sh Hsh) as (_ & _ & _ & _ & _ & _ & _ & KIND). unfold kind_ok in KIND. rewrite Ksh in KIND.
    destruct KIND as (FSnz & DISP & KSP & _). destruct (KSP eq_refl) as (BSP8 & SHLO & SHHI).
    assert (SP8v : nu SP8 = e_sp0 E1 / 8) by exact (nu_SP8 SEGS P E mem0 A nu regs mem HG2).
    assert (RB : rbase nu sh = SBz + e_sp0 E1 / 8) by (unfold rbase; rewrite DISP, BSP8, SHOFF, SP8v; reflexivity).
    assert (SP0al : e_sp0 E1 = 8 * (e_sp0 E1 / 8)).
    { pose proof (Z.div_mod (e_sp0 E1) 8 ltac:(lia)) as X. replace (e_sp0 E1 mod 8) with 0 in X; [lia|].
      unfold E1. rewrite <- (Z.mod_mod_divide (e_sp0 (ev1 E)) 16 8) by (exists 2; reflexivity). rewrite E1a. reflexivity. }
    unfold env_fs in HFS. destruct (vp_fs P) as [[flen fssl]|] eqn:EFS; [|exfalso; exact (FSnz eq_refl)].
    destruct HFS as (_ & FS1 & FS2 & FS3 & FS4 & _ & _ & APsf & APdf & APds & HMsp & HMd & _ & SPHI & _).
    clear APsf APdf APds HMd.
    split; [|split; [intros X; discriminate X|]; split; [exact HMsp|]; split; [exact SPHI|]; split; [exact SP0al|]].
    2:{ intros i Hi. exact (proj2 (MF (e_sp0 E1 + i) ltac:(unfold P1, E1 in *; lia))). }
    intros Hn0. unfold HIGH_MEM_BEG, HIGH_MEM_END in *.
    assert (GR : forall g, lo / 8 <= g <= (hi - 1) / 8 ->
      exists k : byte, mem (wordZ (SBz + e_sp0 E1 / 8 + g)) = Some k
                       /\ (bv_unsigned k = 0 \/ Z.min hi (8 * g + 8) - 8 * g <= bv_unsigned k < 8)).
    { intros g Hg. destruct (range_granules_ok_sound sh lo hi g GRAN ltac:(lia) Hg) as (b & SB & Hb).
      destruct (sh_byte_mem SEGS P E mem0 A nu regs mem sh g b HG2 Hsh ltac:(unfold is_shadow; rewrite Ksh; reflexivity) SB) as (k & Rk & Vk).
      rewrite RB in Rk. exists k. split; [|rewrite Vk; exact Hb].
      apply (rdn1_mem SEGS ROM_HI); [|exact Rk]. unfold SBz.
      apply (arith_stack_shadow_addr (e_sp0 E1) (vp_frame P1) lo hi g); unfold P1, E1 in *; lia. }
    assert (SHAD :
      (forall g, x / 8 <= g < (x + n - 1) / 8 -> mem (wordZ (SBz + g)) = Some (Z_to_bv 8 0))
      /\ (exists b1 : byte, mem (wordZ (SBz + (x + n - 1) / 8)) = Some b1
                           /\ (bv_unsigned b1 = 0 \/ (x + n - 1) mod 8 < bv_unsigned b1 < 8))).
    { unfold x. rewrite SP0al. apply (shadow_access mem (e_sp0 E1 / 8) lo hi ov n GR); lia. }
    assert (NUE8 : nuE E SP8 = e_sp0 E1 / 8).
    { unfold nuE, fix_val2. replace (fix_val (ev1 E) SP8) with (@None Z) by reflexivity. reflexivity. }
    assert (WRD : forall q, (q = x \/ q = x + n - 1) ->
      exists w : word, rdn SEGS mem (wordZ ((SBz + q / 8) / 8 * 8)) 8 = Some (word_to_le_bytes 8 w)).
    { intros q Hq.
      pose proof (Z.div_mod (SBz + q / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SBz + q / 8) 8 ltac:(lia)).
      assert (QB : lo / 8 <= q / 8 - e_sp0 E1 / 8 <= (hi - 1) / 8).
      { unfold x in Hq. rewrite SP0al in Hq. exact (arith_qb _ _ _ _ _ _ Hq H1 H2 Hn0). }
      pose proof (div8_facts lo). pose proof (div8_facts (hi - 1)). pose proof (PO1 _ _ PO2) as (Pfr & _).
      apply (word_readable SEGS P E mem0 A nu regs mem _ HG2); [| unfold SBz, P1, E1 in *; (ltac2:(LK.k [@H1; @H3; @FS1; @HMsp; @E4; @E5; @E11; @BSP8; @SP0al; @Hn0; @NUE8; @Hq; @H; @H0; @QB; @H5; @Pfr]); lia) | ].
      - intros i Hi. apply (zone_has_sound SEGS P E mem0 A nu regs mem SP8 _ _ _ HG2 Hsw). rewrite SHOFF, NUE8. unfold SBz in *. (ltac2:(LK.k [@H1; @H2; @FS1; @HMsp; @E4; @E5; @E11; @BSP8; @Hn0; @H; @H0; @QB; @H5; @H6; @Pfr; @Hi]); lia).
      - unfold SBz in *. pose proof (Z.div_mod q 8 ltac:(lia)). pose proof (Z.mod_pos_bound q 8 ltac:(lia)). unfold x, E1, P1 in *. (ltac2:(LK.k [@H2; @H4; @FS1; @SPHI; @E4; @E5; @E11; @BSP8; @Hn0; @Hq; @H; @H0; @Pfr; @H7; @H8]); lia). }
    split; [exact (proj1 SHAD)|]. split; [exact (proj2 SHAD)|]. split; apply WRD; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis DATAL : 8 <= vp_datal P.

  #[using="SHOFF ROM_HI FSLEN DATAL"] Lemma data_range_facts A nu regs mem ov n :
    gamma2P A nu regs mem -> vp_fs P <> None -> 0 <= ov -> ov + n <= e_size E1 -> 0 <= n ->
    let x := e_data E1 + ov in
    (0 < n -> acc_facts mem x n)
    /\ (0 < e_size E1 -> (off_band (e_data E1) (e_size E1) /\ 16 <= e_data E1) /\ e_data E1 + e_size E1 + 64 <= HIGH_MEM_END)   (* [comment removed for export] *)
    /\ e_data E1 mod 8 = 0
    /\ (e_data E1 + e_size E1 + 4096 <= e_sp0 E1 - vp_frame P1 \/ e_sp0 E1 + 4096 <= e_data E1)
    /\ (forall i, 0 <= i < e_size E1 -> exists b, rdn SEGS mem (wordZ (e_data E1 + i)) 1 = Some [b]).
  Proof.
    intros HG2 FSnz Hov Hn1 Hn x.
    pose proof HG2 as (HG1 & HE & HM & HF2 & HDD & RGN & LIVE & BEL2 & GL2 & FI2 & MOK).
    pose proof HE as (HEV1 & HD2 & HFS & HZO & HKC). pose proof HEV1 as (E1a & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E11 & E12).
    pose proof (proj1 (proj2 HG1)) as (MF & MD & MP & MFM).
    pose proof HD2 as (_ & _ & D8 & _). specialize (D8 DATAL).
    pose proof HM as (_ & _ & DS & _). destruct (DS DATAL FSnz) as (DX & DM & DW).
    assert (SHB0 : forall y, shadow_byte P y = SBz + y / 8) by (intros y; unfold shadow_byte; rewrite SHOFF; reflexivity). rewrite !SHB0 in DW.
    unfold env_fs in HFS. destruct (vp_fs P) as [[flen fssl]|] eqn:EFS; [|exfalso; exact (FSnz eq_refl)].
    destruct HFS as (_ & FS1 & FS2 & FS3 & FS4 & _ & _ & APsf & APdf & APds & HMsp & HMd & _ & SPHI & _).
    split; [|split; [exact HMd|]; split; [exact D8|]; split; [exact APds|exact MD]].
    intros Hn0. unfold P1, E1 in *. destruct (HMd ltac:(lia)) as [HD1 HD3].
    (* [comment removed for export] *)
    clear APsf APdf APds HMd. destruct HD1 as [_ HD1]. unfold HIGH_MEM_BEG, HIGH_MEM_END in *.
    pose proof (Z.div_mod (e_data (ev1 E)) 8 ltac:(lia)) as DD. rewrite D8 in DD.
    assert (DIVi : forall i, 0 <= i -> (e_data (ev1 E) + i) / 8 = e_data (ev1 E) / 8 + i / 8).
    { intros i Hi. replace (e_data (ev1 E) + i) with (i + (e_data (ev1 E) / 8) * 8) by lia. rewrite Z.div_add by lia. lia. }
    assert (SHB : shadow_byte P (e_data (ev1 E)) = SBz + e_data (ev1 E) / 8) by (unfold shadow_byte; rewrite SHOFF; reflexivity).
    pose proof (div8_facts ov) as V1. pose proof (div8_facts (ov + n - 1)) as V2.
    assert (V3 : ov / 8 <= (ov + n - 1) / 8) by (apply Z.div_le_mono; lia).
    assert (X1 : x / 8 = e_data (ev1 E) / 8 + ov / 8) by (unfold x; apply DIVi; lia).
    assert (X2 : (x + n - 1) / 8 = e_data (ev1 E) / 8 + (ov + n - 1) / 8).
    { unfold x. replace (e_data (ev1 E) + ov + n - 1) with (e_data (ev1 E) + (ov + n - 1)) by lia. apply DIVi. lia. }
    assert (X3 : (x + n - 1) mod 8 = (ov + n - 1) - 8 * ((ov + n - 1) / 8)).
    { rewrite Z.mod_eq by lia. rewrite X2. unfold x. lia. }
    (* [comment removed for export] *)
    assert (GB : forall g, 0 <= 8 * g < e_size (ev1 E) -> exists k : byte, mem (wordZ (SBz + e_data (ev1 E) / 8 + g)) = Some k
                  /\ (8 * g + 8 <= e_size (ev1 E) -> bv_unsigned k = 0) /\ (e_size (ev1 E) < 8 * g + 8 -> bv_unsigned k = e_size (ev1 E) - 8 * g)).
    { intros g Hg. destruct (DX g Hg) as (k & Rk & K0 & K1). rewrite SHB in Rk. exists k. split; [|auto].
      apply (rdn1_mem SEGS ROM_HI); [|exact Rk]. pose proof (div8_facts (e_data (ev1 E))). unfold SBz in *. (ltac2:(LK.k [@Hov; @FS1; @E4; @E5; @E11; @Hn0; @HD1; @HD3; @DD; @Hg]); lia). }
    split; [|split; [|split]].
    - intros G HG. rewrite X1, X2 in HG. destruct (GB (G - e_data (ev1 E) / 8) ltac:((ltac2:(LK.k [@Hov; @Hn1; @FS1; @E4; @E5; @E11; @Hn0; @HD1; @V1; @X3; @HG]); lia))) as (k & Mk & K0 & _).
      replace (SBz + e_data (ev1 E) / 8 + (G - e_data (ev1 E) / 8)) with (SBz + G) in Mk by lia. rewrite Mk. f_equal.
      apply bv_eq. change (bv_unsigned (Z_to_bv 8 0)) with 0. apply K0. lia.
    - rewrite X2, X3. destruct (GB ((ov + n - 1) / 8) ltac:((ltac2:(LK.k [@Hov; @Hn1; @FS1; @E3; @E4; @E5; @E11; @Hn0; @HD1; @V2; @X1; @X2; @X3]); lia))) as (k & Mk & K0 & K1). rewrite <- Z.add_assoc in Mk.
      exists k. split; [exact Mk|].
      destruct (Z_le_gt_dec (8 * ((ov + n - 1) / 8) + 8) (e_size (ev1 E))) as [LE|GT]; [left; apply K0; lia|right]. rewrite (K1 ltac:(lia)). lia.
    - pose proof (word_floor_mono SBz (e_data (ev1 E)) x ltac:(unfold x; lia)) as M1.
      pose proof (word_floor_mono SBz x (e_data (ev1 E) + e_size (ev1 E) - 1) ltac:(unfold x; lia)) as M2.
      destruct (word_floor_range SBz x ltac:(unfold SBz; lia) ltac:(unfold x; lia) ltac:(unfold SBz; lia)) as [M3 M4].
      apply (word_readable SEGS P E mem0 A nu regs mem _ HG2); [|exact M3|exact M4].
      intros i Hi. apply (DW ltac:(lia)). clear -M1 M2 Hi. lia.
    - pose proof (word_floor_mono SBz (e_data (ev1 E)) (x + n - 1) ltac:(unfold x; lia)) as M1.
      pose proof (word_floor_mono SBz (x + n - 1) (e_data (ev1 E) + e_size (ev1 E) - 1) ltac:(unfold x; lia)) as M2.
      destruct (word_floor_range SBz (x + n - 1) ltac:(unfold SBz; lia) ltac:(unfold x; lia) ltac:(unfold SBz; lia)) as [M3 M4].
      apply (word_readable SEGS P E mem0 A nu regs mem _ HG2); [|exact M3|exact M4].
      intros i Hi. apply (DW ltac:(lia)). clear -M1 M2 Hi. lia.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma range_check_ld_rgn_inv A de ne r lo hi :
    range_check P A de ne false = RA_rgn r lo hi ->
    exists B, base_syms A de = [B] /\ lcoef de B = 1 /\ lcoef de SP0 = 0 /\ lcoef de DATA = 0
      /\ rgn_get (vs_rgn A) B = Some r
      /\ match vr_kind r with RK_fake _ _ | RK_arg => True | _ => False end
      /\ let off := laddc (lsub de (lsym B)) (- vr_disp r) in
         lo_of (v1 A) off = Some lo /\ hi_of (v1 A) (ladd off ne) = Some hi
         /\ vr_lo r <= lo /\ hi <= vr_hi r
         /\ rgn_addressable A r lo hi = true /\ frames_shadow_zone_ok P = true.
  Proof.
    unfold range_check. destruct (base_syms A de) as [|B [|B2 t]]; try discriminate.
    - destruct (readable_range (p1 P) (v1 A) de ne) as [off lo' hi'|doff|ilo ihi| |m]; try discriminate.
      repeat match goal with |- (if ?c then _ else _) = _ -> _ => destruct c; try discriminate end.
    - destruct (Z.eqb_spec (lcoef de B) 1) as [C1|]; cbn [negb orb]; [|discriminate].
      destruct (Z.eqb_spec (lcoef de SP0) 0) as [C2|]; cbn [negb andb orb]; [|discriminate].
      destruct (Z.eqb_spec (lcoef de DATA) 0) as [C3|]; cbn [negb andb orb]; [|discriminate].
      destruct (rgn_get (vs_rgn A) B) as [r0|] eqn:G; [|discriminate].
      cbv zeta. intros H. exists B.
      destruct (vr_kind r0) eqn:K; try discriminate;
        (destruct (dead_lin (v1 A) _ || dead_lin (v1 A) _); [discriminate|]);
        destruct (lo_of (v1 A) _) as [lo1|] eqn:LO; try discriminate; destruct (hi_of (v1 A) _) as [hi1|] eqn:HI; try discriminate;
        (destruct (Z.ltb_spec lo1 (vr_lo r0)); [discriminate|]); (destruct (Z.ltb_spec (vr_hi r0) hi1); cbn [orb] in H; [discriminate|]);
        cbn [andb] in H;
        (destruct (rgn_addressable A r0 lo1 hi1) eqn:RA; cbn [negb] in H; [|discriminate]);
        (destruct (frames_shadow_zone_ok P) eqn:FZ; cbn [negb] in H; [|discriminate]);
        injection H as <- <- <-; rewrite K; repeat split; auto; try lia.
  Qed.

  #[using="Type"] Lemma range_check_ld_v1_inv A de ne rr :
    range_check P A de ne false = RA_v1 rr ->
    (exists so slo shi, rr = RR_stack so slo shi /\ readable_range P1 (v1 A) de ne = RR_stack so slo shi
       /\ above_sp A slo shi = true /\ stack_addressable A slo shi = true /\ stack_shadow_words_ok P slo shi = true)
    \/ (exists doff, rr = RR_data doff /\ readable_range P1 (v1 A) de ne = RR_data doff)
    \/ (exists ilo ihi, rr = RR_img ilo ihi).
  Proof.
    unfold range_check. destruct (base_syms A de) as [|B [|B2 t]]; try discriminate.
    - destruct (readable_range (p1 P) (v1 A) de ne) as [off lo hi|doff|ilo ihi| |m] eqn:RR; try discriminate.
      + destruct (above_sp A lo hi) eqn:AS; cbn [negb]; [|discriminate].
        destruct (stack_addressable A lo hi) eqn:SA; cbn [negb]; [|discriminate].
        destruct (stack_shadow_words_ok P lo hi) eqn:SW; cbn [negb]; [|discriminate].
        intros H. injection H as <-. left. exists off, lo, hi. repeat split; auto.
      + intros H. injection H as <-. right; left. exists doff. auto.
      + intros H. injection H as <-. right; right. exists ilo, ihi. auto.
    - destruct (negb (lcoef de B =? 1) || negb ((lcoef de SP0 =? 0) && (lcoef de DATA =? 0))); [discriminate|].
      destruct (rgn_get (vs_rgn A) B) as [r|]; [|discriminate].
      destruct (vr_kind r); try discriminate;
        (destruct (dead_lin (v1 A) _ || dead_lin (v1 A) _); [discriminate|]);
        destruct (lo_of (v1 A) _); try discriminate; destruct (hi_of (v1 A) _); try discriminate;
        repeat match goal with |- (if ?c then _ else _) = _ -> _ => destruct c; try discriminate end.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma readable_range_data_inv A nu de ne doff :
    lgamma A nu -> gamma_fix E1 nu ->
    readable_range P1 A de ne = RR_data doff ->
    0 <= eval nu de - e_data E1 /\ eval nu de - e_data E1 + eval nu ne <= e_size E1.
  Proof.
    intros HL HF. unfold readable_range.
    destruct (is_sp_rel de); [intros X; exfalso; pose proof (stack_range_shape (p1 P) A de ne false) as SH; unfold P1 in X; rewrite X in SH; exact SH|].
    destruct (is_data_rel de); [|].
    - destruct (dead_lin A (lsub de (lsym DATA))); [discriminate|].
      unfold lo_of, hi_of.
      pose proof (bnd_sound A nu (lsub de (lsym DATA)) HL) as B1.
      destruct (bnd A (lsub de (lsym DATA))) as [[l1|] h1]; [|discriminate]. cbn [fst].
      destruct (Z.ltb_spec l1 0); [discriminate|].
      pose proof (bnd_sound A nu (lsub (ladd (lsub de (lsym DATA)) ne) (lsym SIZE)) HL) as B2.
      destruct (bnd A (lsub (ladd (lsub de (lsym DATA)) ne) (lsym SIZE))) as [l2 [h2|]]; [|discriminate]. cbn [snd].
      destruct (Z.ltb_spec 0 h2); [discriminate|]. intros _.
      destruct B1 as [B1 _]. destruct B2 as [_ B2]. cbn [fst snd lo_le hi_ge] in B1, B2.
      rewrite !eval_lsub, ?eval_ladd, ?eval_lsub, !eval_lsym, (nu_DATA E1 nu HF) in B1.
      rewrite eval_lsub, eval_ladd, eval_lsub, !eval_lsym, (nu_DATA E1 nu HF), (nu_SIZE E1 nu HF) in B2. lia.
    - destruct (negb _); [discriminate|]. destruct (lo_of A de); [|discriminate]. destruct (hi_of A (ladd de ne)); [|discriminate].
      destruct (in_ranges _ _ _); discriminate.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable tgt : Z.
  Variable MCELLS : (word -> option byte) -> Prop.
  Hypothesis MCELLS_OK : forall A nu regs mem, gamma2P A nu regs mem -> MCELLS mem.

  Definition RUN_spec4 : Prop := forall mem (d s n usp : Z) (bs : list byte) regs (ra : word),
    MCELLS mem ->
    0 <= n <= 2 ^ 40 -> 0 <= d -> 0 <= s -> d + n < 2 ^ 64 -> s + n < 2 ^ 64 ->
    (n = 0 \/ s + n <= d \/ d + n <= s) ->
    length bs = Z.to_nat n -> rdn SEGS mem (wordZ s) (length bs) = Some bs ->
    (0 < n -> band_ok d n) ->   (* [comment removed for export] *)
    (0 < n -> band_ok s n) ->
    SBz + 2224 <= usp < 2 ^ 64 ->
    (n = 0 \/ usp <= d \/ d + n <= usp - JUNK4) -> (n = 0 \/ usp <= s \/ s + n <= usp - JUNK4) ->
    (0 < n -> SBz + (d + n - 1) / 8 + 8 < usp - JUNK4) -> (0 < n -> SBz + (s + n - 1) / 8 + 8 < usp - JUNK4) ->
    (0 < n -> acc_facts mem d n) -> (0 < n -> acc_facts mem s n) ->
    (forall j, 0 <= j < n -> store_ok SEGS mem (wordZ (d + j)) 1 = true) ->
    (forall a, usp - JUNK4 <= a < usp -> store_ok SEGS mem (wordZ a) 1 = true) ->
    ret_ok ra -> getr regs 1%bv = ra -> getr regs 2%bv = wordZ usp ->
    getr regs 10%bv = wordZ d -> getr regs 11%bv = wordZ s -> getr regs 12%bv = wordZ n ->
    exists regs' m',
      msteps SEGS (mkst regs (wordZ tgt) mem rom) (mkst regs' ra m' rom)
      /\ getr regs' 10%bv = wordZ d /\ getr regs' 2%bv = wordZ usp /\ getr regs' 1%bv = ra
      /\ (forall r : reg, bv_unsigned r <> 0 -> ~ In (bv_unsigned r) CALLER_SAVED -> getr regs' r = getr regs r)
      /\ (forall x : word, (bv_unsigned x < usp - JUNK4 \/ usp <= bv_unsigned x) -> m' x = wbytes mem (wordZ d) bs x)
      /\ (forall x, mem x <> None -> m' x <> None).
  Hypothesis RUN : RUN_spec4.

  (* [comment removed for export] *)
  Definition src_ok (mem : word -> option byte) (usp s n : Z) : Prop :=
       0 <= s /\ s + n < 2 ^ 64
    /\ (0 < n -> band_ok s n)
    /\ (n = 0 \/ usp <= s \/ s + n <= usp - JUNK4)
    /\ (0 < n -> SBz + (s + n - 1) / 8 + 8 < usp - JUNK4)
    /\ (0 < n -> acc_facts mem s n)
    /\ (forall i, 0 <= i < n -> exists b, rdn SEGS mem (wordZ (s + i)) 1 = Some [b]).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="PO2 SHOFF ROM_HI FSLEN MCELLS MCELLS_OK RUN"] Lemma post_rgn A spoff nu regs mem (ra : word) de ne (n : Z) B r lo hi ov s :
    gamma2P A nu regs mem -> vs_memo A = [] ->
    get_reg (v1 A) 2 = Some (lsymc SP0 spoff) ->
    - vp_frame P1 <= spoff - 2224 -> spoff <= 0 ->
    (exists wr, In wr (vp_wstack P1) /\ fst wr <= spoff - 2224 /\ spoff <= snd wr) ->
    ret_ok ra -> getr regs 1%bv = ra ->
    get_reg (v1 A) A0r = Some de -> lin_below de (vs_next (v1 A)) = true ->
    n = eval nu ne -> 0 <= n <= 2 ^ 40 ->
    getr regs 12%bv = wordZ n -> getr regs 2%bv = wordZ (e_sp0 E1 + spoff) ->
    rgn_get (vs_rgn A) B = Some r -> vr_base r = B ->
    match vr_kind r with RK_fake _ _ | RK_arg => True | _ => False end ->
    vr_lo r <= lo -> hi <= vr_hi r -> (lo < hi -> in_ranges (vr_w r) lo (hi - lo) = true) ->
    rgn_addressable A r lo hi = true -> frames_shadow_zone_ok P = true ->
    eval nu de = rbase nu r + ov -> lo <= ov -> ov + n <= hi -> 0 < n ->
    let d := rbase nu r + ov in let usp := e_sp0 E1 + spoff in
    getr regs 10%bv = wordZ d -> getr regs 11%bv = wordZ s ->
    src_ok mem usp s n -> (n = 0 \/ s + n <= d \/ d + n <= s) ->
    let r2' := rgn_havoc r lo hi false false in
    exists A1 v regs' mem' nu',
         In (A1, v) [(rgn_store_commit A r2', Some de)]
      /\ msteps SEGS (mkst regs (wordZ tgt) mem rom) (mkst regs' ra mem' rom)
      /\ gamma2P (contract_frame2 C_asan_memcpy A1 spoff v) nu' regs' mem'
      /\ getr regs' 1%bv = ra
      /\ ext (vs2_next A) nu nu' /\ (vs2_next A <= vs2_next (contract_frame2 C_asan_memcpy A1 spoff v))%positive
      /\ frame_mod mem mem' (unit_regions2 P E)
      /\ flags_step P E A (contract_frame2 C_asan_memcpy A1 spoff v) nu nu' mem mem'.
  Proof.
    intros HG2 MEMO Hsp K1 K2 KW Hret Hra Ede B10 En Hn R12 R2 HGr HBr HKr RLO RHI HWr HRA HFZ Eoff Bo Bo1 Hn0 d usp R10 R11
           (S1 & S2 & S3 & S4 & S5 & S6 & S7) DISJ r2'.
    pose proof HG2 as (HG1 & HE & HM & HF2 & HDD & RGN & LIVE & BEL2 & GL2 & FI2 & MOK).
    pose proof (gamma2_lgamma _ _ _ _ _ _ _ _ HG2) as HL.
    pose proof (PO1 _ _ PO2) as PO. pose proof PO as (P0 & Psphi & PS & PF & PW & PR & PP & PB).
    pose proof HE as (HEV1 & HD2 & HFS & HZO & HKC). pose proof HEV1 as (E1a & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E11 & E12).
    pose proof (proj1 (proj2 HG1)) as (MF & MD & MP & MFM).
    pose proof (rgn_get_in _ _ _ HGr) as [Hr _].
    pose proof (RGN r Hr) as ROK. pose proof ROK as (RB1 & RB2 & RB3 & RDS & CELLS & PERM & NUL & KIND).
    assert (ND : is_data_shadow r = false) by (unfold is_data_shadow; destruct (vr_kind r); auto; contradiction).
    destruct (rgn_range_facts A nu regs mem B r lo hi ov n HG2 HGr HKr RLO RHI HRA HFZ Bo Bo1 ltac:(lia))
      as (DACC & (fa & cid & Hcid & FA1 & FA2 & FA3 & FA4 & FK) & FSnz & DRNG & _).
    cbv zeta in DACC. fold d in DACC.
    unfold env_fs in HFS. destruct (vp_fs P) as [[flen fssl]|] eqn:EFS; [|exfalso; exact (FSnz eq_refl)].
    destruct HFS as (_ & FS1 & FS2 & FS3 & FS4 & _ & _ & APsf & APdf & APds & HMsp & HMd & _ & SPHI & _).
    pose proof (FSLEN _ _ eq_refl) as FS5. clear APdf APds HMd. unfold HIGH_MEM_BEG, HIGH_MEM_END, FS_NCLASSES, FS_SSL in *.
    assert (DRANGE : fa <= d /\ d + n <= fa + fake_size cid /\ 0 <= d /\ d + n <= 2 ^ 47 - 1) by (unfold d; unfold FS_FRAMES in *; lia).
    assert (USP : 0 <= e_sp0 E1 - vp_frame P1 /\ e_sp0 E1 - vp_frame P1 <= usp - 2224 /\ usp <= e_sp0 E1 /\ e_sp0 E1 < 2 ^ 64)
      by (unfold usp, P1, E1 in *; lia).
    assert (JOK : forall a, usp - JUNK4 <= a < usp -> store_ok SEGS mem (wordZ a) 1 = true).
    { intros a Ha. unfold JUNK4 in Ha. apply (proj1 (MF a ltac:(unfold usp, P1, E1 in *; lia))). }
    (* [comment removed for export] *)
    specialize (HWr ltac:(lia)). apply in_ranges_sound in HWr as (wlo & whi & HWin & W1 & W2).
    destruct (PERM ND) as [RDp WR].
    assert (DOK : forall j, 0 <= j < n -> store_ok SEGS mem (wordZ (d + j)) 1 = true).
    { intros j Hj. destruct (WR wlo whi (ov + j) HWin ltac:(lia)) as (_ & _ & X & _). unfold d. rewrite <- Z.add_assoc. exact X. }
    (* [comment removed for export] *)
    destruct (rdn_bytes SEGS mem s (Z.to_nat n) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)
                ltac:(intros k Hk; rewrite Z2Nat.id in Hk by lia; apply S7; lia)) as (bs & RDs & LENs).
    destruct (RUN mem d s n usp bs regs ra (MCELLS_OK _ _ _ _ HG2) ltac:(lia) ltac:(lia) S1 ltac:(lia) S2 DISJ LENs
                ltac:(rewrite LENs; exact RDs))
      as (regs' & m' & MS & Q10 & Q2 & Q1 & QK & QM & QG).
    { intros _. apply (band_ok_mono _ _ _ _ (proj2 (proj2 DRNG))); unfold d; clear -Bo Bo1; lia. }
    { exact S3. }
    { clear -USP HMsp. unfold SBz, HIGH_MEM_BEG, usp, P1, E1 in *. lia. }
    { right. unfold JUNK4, d, usp. unfold FS_FRAMES in *. destruct APsf as [X|X]; unfold P1, E1 in *; [right|left]; lia. }
    { exact S4. }
    { intros _. unfold SBz, usp. apply (arith_shd4_low (e_sp0 E1) (vp_frame P1) spoff (d + n - 1)); unfold P1, E1 in *; lia. }
    { exact S5. }
    { exact DACC. }
    { exact S6. }
    { exact DOK. }
    { exact JOK. }
    { exact Hret. } { exact Hra. } { exact R2. } { exact R10. } { exact R11. } { exact R12. }
    clear DISJ S3 S4 S5 S6 S7 DACC RDs R11 R12 R2.
    (* [comment removed for export] *)
    assert (LENn : Z.of_nat (length bs) = n) by (rewrite LENs; lia).
    set (m_b := wbytes mem (wordZ d) bs) in *.
    assert (SH2 : rshape r r2') by (unfold r2', rgn_havoc; eapply rshape_trans; [apply rshape_set_cells|apply rshape_set_rnul]).
    pose proof SH2 as (SB2 & _ & SK2 & _).
    assert (INB : In (vr_base r2') (map vr_base (vs_rgn A))) by (rewrite SB2; apply in_map; exact Hr).
    set (l1 := rgn_upd (vs_rgn A) r2').
    set (l2 := match vr_kind r2' with RK_arg => havoc_other_args l1 (vr_base r2') | _ => l1 end).
    assert (SM1 : shape_map (vs_rgn A) l1).
    { unfold l1. apply rgn_upd_shape; [|exact INB]. intros x Hx EB.
      rewrite (live_ok_base_inj nu A x r LIVE Hx Hr ltac:(rewrite EB; exact SB2)). exact SH2. }
    assert (SM2 : shape_map (vs_rgn A) l2).
    { unfold l2. rewrite SK2. destruct (vr_kind r); try exact SM1. eapply shape_map_trans; [exact SM1|apply havoc_shape]. }
    pose proof LIVE as (_ & _ & _ & ND0).
    assert (MEM : forall x, In x l2 ->
              (x = r2') \/ (In x (vs_rgn A) /\ vr_base x <> vr_base r /\ ~ (vr_kind r = RK_arg /\ vr_kind x = RK_arg))
              \/ (exists y, In y (vs_rgn A) /\ vr_base y <> vr_base r /\ vr_kind r = RK_arg /\ vr_kind y = RK_arg
                               /\ x = set_rnul (set_cells y []) [])).
    { intros x Hx. unfold l2 in Hx. rewrite SK2, SB2 in Hx.
      assert (L1C : forall y, In y l1 -> y = r2' \/ (In y (vs_rgn A) /\ vr_base y <> vr_base r)).
      { intros y Hy. destruct (rgn_upd_other _ _ _ ND0 INB Hy) as [->|[Y1 Y2]]; [auto|right]. rewrite SB2 in Y2. auto. }
      destruct (vr_kind r) eqn:K0;
        try (destruct (L1C x Hx) as [->|[X1 X2]]; [left; reflexivity|right; left; repeat split; auto; intros [X _]; discriminate]).
      rewrite havoc_other_args_map in Hx. apply in_map_iff in Hx as (y & <- & Hy).
      destruct (havoc1_spec (vr_base r) y) as [[KB ->]|(KA & NBy & ->)].
      - destruct (L1C y Hy) as [->|[Y1 Y2]]; [left; reflexivity|]. right; left. split; [exact Y1|]. split; [exact Y2|].
        intros [_ X]. destruct KB as [KB|KB]; [exact (KB X)|exact (Y2 KB)].
      - destruct (L1C y Hy) as [->|[Y1 Y2]]; [exfalso; apply NBy; exact SB2|].
        right; right. exists y. repeat split; auto. }
    assert (HWIN : in_ranges (vr_w r) ov (Z.of_nat (length bs)) = true).
    { unfold in_ranges. apply existsb_exists. exists (wlo, whi). split; [exact HWin|]. cbn [fst snd]. rewrite LENn.
      apply andb_true_intro. split; apply Z.leb_le; lia. }
    destruct (rgn_write_sound SEGS P E mem0 PO2 A nu regs mem r ov bs l2 HG2 Hr ND
                ltac:(destruct (vr_kind r); auto; contradiction) ltac:(rewrite LENn; lia) HWIN SM2) as (G2 & FMb2 & FST2 & BND & SOK).
    { (* [comment removed for export] *)
      intros rx Hrx NBx. destruct (MEM rx Hrx) as [->|[(X1 & X2 & X3)|(y & Y1 & Y2 & Y3 & Y4 & ->)]].
      + exfalso. apply NBx. exact SB2.
      + exists rx. split; [exact X1|]. split; [apply rshape_refl|]. left. auto.
      + exists y. split; [exact Y1|]. split; [|right; split; reflexivity].
        eapply rshape_trans; [apply rshape_set_cells|apply rshape_set_rnul]. }
    { (* [comment removed for export] *)
      intros r' Hr' EB.
      assert (ER : r' = r2').
      { destruct (MEM r' Hr') as [->|[(X1 & X2 & X3)|(y & Y1 & Y2 & Y3 & Y4 & ->)]]; [reflexivity|exfalso; exact (X2 EB)|].
        exfalso. apply Y2. exact EB. }
      subst r'. fold d. change (wbytes mem (wordZ d) bs) with m_b.
      assert (NSH : is_shadow r = false) by (unfold is_shadow; destruct (vr_kind r); auto; contradiction).
      assert (CELLS2 : forall x, In x (vr_cells r2') -> In x (vr_cells r) /\ (fst x + fst (snd x) <= lo \/ hi <= fst x)).
      { intros [kk [ww vv]] Hin. unfold r2', rgn_havoc in Hin. cbn [vr_cells set_rnul set_cells] in Hin.
        pose proof (cm_kill_disjoint _ _ _ _ _ _ Hin). split; [eapply cm_kill_sub; exact Hin|cbn [fst snd]; lia]. }
      assert (NUL2 : forall f, In f (vr_nul r2') -> In f (vr_nul r) /\ (snd f < lo \/ hi <= fst f)).
      { intros f Hin. unfold r2', rgn_havoc in Hin. cbn [vr_nul set_rnul set_cells] in Hin.
        apply filter_In in Hin as [Hf C]. split; [exact Hf|]. apply Bool.orb_prop in C as [C|C]; [apply Z.ltb_lt in C|apply Z.leb_le in C]; lia. }
      split.
      2:{ intros kk ww e Hin. destruct BEL2 as (_ & BR & _). pose proof (proj1 (proj2 (BR r Hr))) as CB.
          destruct (CELLS2 _ Hin) as [Hold _]. exact (CB _ _ _ Hold). }
      eapply (region_ok_self SEGS P E A _ nu mem m_b r r2' HE ROK SH2 ND).
      + apply wbytes_grows.
      + unfold kind_ok in KIND. destruct (vr_kind r) as [cidf fl| | | |] eqn:K0; auto.
        destruct KIND as (_ & Hcf & _ & _ & _ & pos & Hpos & _ & Efl & _).
        pose proof (flag_addr_range (e_fs E) cidf pos Hcf Hpos) as FLR. rewrite <- Efl in FLR.
        unfold m_b. apply wblock_rdn1; rewrite ?LENn; unfold FS_FLAGS, FS_FRAMES in *; try lia.
      + intros s0 ro G _ _. cbn [vs_rgn]. exact (shape_map_get _ _ _ _ SM2 G).
      + destruct (vr_kind r) eqn:K0; auto. cbn [vs_live]. apply (proj2 (proj1 LIVE (vr_base r))). exists r. rewrite K0. auto.
      + destruct (vr_kind r); auto; contradiction.
      + intros cc cw cv Hin. destruct (CELLS2 _ Hin) as [Hold DISJc]. cbn [fst snd] in DISJc.
        destruct (CELLS _ _ _ Hold) as (L1 & L2 & L3 & RCH). split; [lia|]. split; [lia|]. split; [lia|].
        unfold m_b. apply kept_cell; rewrite ?LENn; try (ltac2:(LK.k [@HBr; @Bo1; @Hn0; @P0; @SPHI; @E4; @E5; @E11; @FA2; @FA4; @FS5; @DRANGE; @LENs; @SB2; @EB; @RB1; @L1; @Bo; @RB2; @L3; @L2; @DISJc]); lia). exact RCH.
      + intros nlo' nhi' Hin. destruct (NUL2 _ Hin) as [Hold DISJn]. cbn [fst snd] in DISJn.
        destruct (NUL _ _ Hold) as (o0 & b0 & Y1 & Y2 & Y3 & Y4).
        exists o0, b0. split; [exact Y1|]. split; [exact Y2|]. split; [|exact Y4].
        rewrite <- Y3. unfold m_b. apply wblock_rdn1; rewrite ?LENn; unfold d; (ltac2:(LK.k [@HBr; @Bo; @Hn0; @P0; @SPHI; @E4; @E5; @E11; @RB1; @FA2; @DRNG; @FS5; @DRANGE; @LENs; @SB2; @EB; @Y1; @Y2; @Bo1; @RB2; @DISJn]); lia). }
    (* [comment removed for export] *)
    assert (QM0 : forall x : word, bv_unsigned x < usp - JUNK4 \/ usp <= bv_unsigned x -> m' x = m_b x) by exact QM.
    assert (GRW : forall x, m_b x <> None -> m' x <> None).
    { intros x Hx. destruct (Z_lt_le_dec (bv_unsigned x) d) as [X1|X1]; [|destruct (Z_lt_le_dec (bv_unsigned x) (d + n)) as [X2|X2]].
      - apply QG. intros M0. apply Hx. unfold m_b. rewrite wbytes_outside; [exact M0| |]; rewrite ?LENn, ?u_wordZ by lia; unfold in_rng; rewrite ?u_wordZ by lia; lia.
      - rewrite QM0; [exact Hx|]. unfold JUNK4, d, usp in *. unfold FS_FRAMES in *. destruct APsf as [X|X]; unfold P1, E1 in *; [left|right]; lia.
      - apply QG. intros M0. apply Hx. unfold m_b. rewrite wbytes_outside; [exact M0| |]; rewrite ?LENn, ?u_wordZ by lia; unfold in_rng; rewrite ?u_wordZ by lia; lia. }
    set (A' := mkVS2 (v1 A) l2 (vs_live A) (vs_divdef A) []) in *.
    pose proof (proj1 G2) as Gb1. cbn [v1] in Gb1.
    pose proof (gamma_junk SEGS P1 E1 (zpatch P E mem0 m_b) PO (v1 A) nu regs m_b m' spoff 2224 JUNK4 Gb1 QM0 GRW
                  ltac:(unfold JUNK4; lia) K1 K2) as Gk.
    (* [comment removed for export] *)
    set (Bst := contract_frame C_memset (killK 2224 (v1 A) spoff) spoff (Some de)).
    assert (EFR : frame_rule 2224 (v1 A) spoff (Some de) = Bst) by (apply frame_rule_killK; lia).
    destruct (killK_shape 2224 (v1 A) spoff) as (KS1 & KS2 & KS3 & KS4 & KS5 & KS6 & KS7 & KS8 & KS9).
    destruct (contract_frame_shape C_memset (killK 2224 (v1 A) spoff) spoff (Some de)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & FR).
    assert (HLB : lgamma Bst nu).
    { apply lgamma_contract_frame; [apply lgamma_killK; exact HL|]. cbn [vbelow]. rewrite KS4. exact B10. }
    destruct (gamma_call_post SEGS P1 E1 (zpatch P E mem0 m_b) rom PO (killK 2224 (v1 A) spoff) Bst nu nu regs regs' m' m' []
                Gk (ext_refl _ _) ltac:(unfold Bst; rewrite F5; apply Pos.le_refl) HLB) as [GB _].
    { eapply (gamma_regs_contract_frame SEGS P1 E1 (zpatch P E mem0 m_b) C_memset (killK 2224 (v1 A) spoff) (killK 2224 (v1 A) spoff) spoff (Some de) nu nu regs regs');
        [right; pose proof Gk as (_&_&_&_&_&_&_&KRg&_&_&_&KBl); split; [exact KRg|destruct KBl as (_&_&KRB&_); exact KRB]
        |apply ext_refl|reflexivity|exact QK|].
      rewrite Q10, u_wordZ, Eoff by (unfold d in DRANGE; lia). unfold d. symmetry. apply zwrap_id. unfold d in DRANGE. lia. }
    { intros off' w' v' Hin. left. unfold Bst in Hin. rewrite F1 in Hin. cbn in Hin. split; [exact Hin|]. intros x _. exact I. }
    { intros g w' v' Hin. unfold Bst in Hin. rewrite F2 in Hin. split; [exact Hin|]. intros x _. exact I. }
    { intros lo' hi' Hin. left. unfold Bst in Hin. destruct (F3 _ Hin) as [Hin' _]. split; [exact Hin'|]. intros x _. exact I. }
    { apply frame_mod_refl. }
    { intros x Hx. exfalso. apply Hx. exact I. }
    assert (FMU : frame_mod m_b m' (unit_regions P1 E1)).
    { split; [|exact GRW]. intros a Ha.
      assert (NJ : ~ (usp - JUNK4 <= bv_unsigned a < usp)).
      { intros Hin. refine (proj1 (stack_R_ok SEGS P1 E1 (zpatch P E mem0 mem) PO (spoff - JUNK4) (spoff - 2224) spoff JUNK4
                                 K1 K2 ltac:(unfold JUNK4; lia) ltac:(unfold JUNK4; lia) KW HEV1 a _) Ha).
        cbn [outside]. unfold in_rng. rewrite u_wordZ by (unfold usp, JUNK4, P1, E1 in *; lia). unfold usp in Hin. intros [X _]. apply X. unfold JUNK4 in *. lia. }
      apply QM0. pose proof (bv_unsigned_in_range 64 a). lia. }
    destruct (gamma2_lift SEGS P E mem0 PO2 A' Bst nu nu regs regs' m_b m' G2 GB (ext_refl _ _)
                ltac:(unfold A', Bst; cbn [v1]; rewrite F5, KS4; apply Pos.le_refl) FMU
                ltac:(unfold globs_ok2, A', Bst; cbn [v1 with_v1]; rewrite F2, KS2; exact GL2) ltac:(right; reflexivity))
      as (G3 & FM3 & FST3).
    exists (rgn_store_commit A r2'), (Some de), regs', m', nu.
    assert (EST : contract_frame2 C_asan_memcpy (rgn_store_commit A r2') spoff (Some de) = with_v1 A' Bst).
    { unfold contract_frame2, rgn_store_commit, with_v1, A', set_rgn. cbn [v1 vs_rgn vs_live vs_divdef vs_memo contract2_K].
      rewrite <- EFR, MEMO. reflexivity. }
    rewrite EST.
    split; [left; reflexivity|]. split; [exact MS|]. split; [exact G3|]. split; [exact Q1|].
    split; [apply ext_refl|]. split.
    { unfold vs2_next, A', Bst. cbn [v1 with_v1]. rewrite F5, KS4. apply Pos.le_refl. }
    split; [exact (frame_mod_trans_same _ _ _ _ FMb2 FM3)|].
    eapply flags_step_then_same; [exact FST2|]. intros y Hy. split; [unfold A', with_v1; cbn [vs_rgn]; tauto|].
    apply QM0. unfold in_flags_zone in Hy. rewrite EFS in Hy. cbv beta iota in Hy.
    unfold usp, JUNK4, FS_FLAGS, FS_FRAMES in *. rewrite u_wordZ by lia. destruct APsf as [X|X]; unfold P1, E1 in *; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="PO2 SHOFF ROM_HI FSLEN MCELLS MCELLS_OK RUN"] Lemma post_stk A spoff nu regs mem (ra : word) de ne (n : Z) off lo hi s :
    gamma2P A nu regs mem -> vs_memo A = [] ->
    get_reg (v1 A) 2 = Some (lsymc SP0 spoff) ->
    - vp_frame P1 <= spoff - 2224 -> spoff <= 0 ->
    (exists wr, In wr (vp_wstack P1) /\ fst wr <= spoff - 2224 /\ spoff <= snd wr) ->
    ret_ok ra -> getr regs 1%bv = ra ->
    get_reg (v1 A) A0r = Some de -> lin_below de (vs_next (v1 A)) = true ->
    n = eval nu ne -> 0 <= n <= 2 ^ 40 ->
    getr regs 12%bv = wordZ n -> getr regs 2%bv = wordZ (e_sp0 E1 + spoff) ->
    stack_range P1 (v1 A) de ne true = RR_stack off lo hi ->
    above_sp A lo hi = true -> stack_addressable A lo hi = true -> stack_shadow_words_ok P lo hi = true ->
    let d := e_sp0 E1 + eval nu off in let usp := e_sp0 E1 + spoff in
    getr regs 11%bv = wordZ s ->
    src_ok mem usp s n -> (n = 0 \/ s + n <= d \/ d + n <= s) ->
    let A1k := kill_nul (set_slots (v1 A) (cm_kill (vs_slots (v1 A)) lo hi)) lo (hi - 1) None in
    exists A1 v regs' mem' nu',
         In (A1, v) [(with_v1 A A1k, Some de)]
      /\ msteps SEGS (mkst regs (wordZ tgt) mem rom) (mkst regs' ra mem' rom)
      /\ gamma2P (contract_frame2 C_asan_memcpy A1 spoff v) nu' regs' mem'
      /\ getr regs' 1%bv = ra
      /\ ext (vs2_next A) nu nu' /\ (vs2_next A <= vs2_next (contract_frame2 C_asan_memcpy A1 spoff v))%positive
      /\ frame_mod mem mem' (unit_regions2 P E)
      /\ flags_step P E A (contract_frame2 C_asan_memcpy A1 spoff v) nu nu' mem mem'.
  Proof.
    intros HG2 MEMO Hsp K1 K2 KW Hret Hra Ede B10 En Hn R12 R2 Esr Hab Hsa Hsw d usp R11 (S1 & S2 & S3 & S4 & S5 & S6 & S7) DISJ A1k.
    pose proof HG2 as (HG1 & HE & HM & HF2 & HDD & RGN & LIVE & BEL2 & GL2 & FI2 & MOK).
    pose proof (gamma2_lgamma _ _ _ _ _ _ _ _ HG2) as HL.
    pose proof (PO1 _ _ PO2) as PO. pose proof PO as (P0 & Psphi & PS & PF & PW & PR & PP & PB).
    pose proof HE as (HEV1 & HD2 & HFS & HZO & HKC). pose proof HEV1 as (E1a & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E11 & E12).
    pose proof HG1 as (_ & (MF & MD & MP & MFM) & HF1 & HS1 & HC1 & HMo1 & HV1 & HRg & HSl & HGl & HN & HB1).
    destruct (stack_dst SEGS P1 E1 (zpatch P E mem0 mem) PO (v1 A) nu regs mem de ne off lo hi HG1 ltac:(lia) Esr)
      as (Ed & H1 & H2 & H3 & H4 & Hd0 & Hdn & Hok & Hws).
    rewrite <- En in H2, Hdn, Hok. set (ov := eval nu off) in *. fold d in Ed, Hd0, Hdn, Hok.
    assert (R10 : getr regs 10%bv = wordZ d).
    { apply wordZ_eq_u. pose proof (reg_val SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem 10%bv de HG1 ltac:(vm_compute; lia) Ede) as [V10 _].
      rewrite V10, Ed. apply zwrap_id. lia. }
    pose proof (above_sp_sound A spoff lo hi Hsp Hab) as HAB.
    destruct (stack_range_facts A nu regs mem lo hi ov n HG2 Hsa Hsw H1 H2 H3 H4 ltac:(lia)) as (DACC & FSnz & HMsp & SPHI & SP0al & _).
    cbv zeta in DACC. fold d in DACC.
    unfold env_fs in HFS. destruct (vp_fs P) as [[flen fssl]|] eqn:EFS; [|exfalso; exact (FSnz eq_refl)].
    destruct HFS as (_ & FS1 & FS2 & FS3 & FS4 & _ & _ & APsf & APdf & APds & _ & HMd & _ & _ & _).
    clear APsf APdf APds HMd. unfold HIGH_MEM_BEG, HIGH_MEM_END in *.
    assert (USP : 0 <= e_sp0 E1 - vp_frame P1 /\ e_sp0 E1 - vp_frame P1 <= usp - 2224 /\ usp <= e_sp0 E1 /\ e_sp0 E1 < 2 ^ 64)
      by (unfold usp, P1, E1 in *; lia).
    assert (JOK : forall a, usp - JUNK4 <= a < usp -> store_ok SEGS mem (wordZ a) 1 = true).
    { intros a Ha. unfold JUNK4 in Ha. apply (proj1 (MF a ltac:(unfold usp, P1, E1 in *; lia))). }
    assert (DJ : n = 0 \/ usp <= d) by (destruct (Z.eq_dec n 0); [left; assumption|right; unfold d, usp; lia]). clear HAB Hab.
    (* [comment removed for export] *)
    destruct (rdn_bytes SEGS mem s (Z.to_nat n) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)
                ltac:(intros k Hk; rewrite Z2Nat.id in Hk by lia; apply S7; lia)) as (bs & RDs & LENs).
    destruct (RUN mem d s n usp bs regs ra (MCELLS_OK _ _ _ _ HG2) ltac:(lia) ltac:(lia) S1 ltac:(lia) S2 DISJ LENs
                ltac:(rewrite LENs; exact RDs))
      as (regs' & m' & MS & Q10 & Q2 & Q1 & QK & QM & QG).
    { intros _. apply band_ok_high; unfold HIGH_MEM_BEG, HIGH_MEM_END; clear -H1 H2 H3 H4 HMsp SPHI; unfold d, P1, E1 in *; lia. }
    { exact S3. }
    { clear -USP HMsp. unfold SBz, usp, P1, E1 in *. lia. }
    { destruct DJ as [DJ0|DJ1]; [left; exact DJ0|right; left; exact DJ1]. }
    { exact S4. }
    { intros Hn0. unfold SBz, d, usp. apply (arith_shd4 (e_sp0 E1) (vp_frame P1) spoff (e_sp0 E1 + ov + n - 1) SP0al); unfold P1, E1 in *; lia. }
    { exact S5. }
    { exact DACC. }
    { exact S6. }
    { intros j Hj. apply (MF (d + j)). unfold d, P1, E1 in *. (ltac2:(LK.k [@K1; @E4; @E5; @E11; @H1; @H2; @H3; @H4; @DJ; @LENs; @Hj]); lia). }
    { exact JOK. }
    { exact Hret. } { exact Hra. } { exact R2. } { exact R10. } { exact R11. } { exact R12. }
    clear DISJ S3 S4 S5 S6 S7 DACC RDs R11 R12 R2.
    (* [comment removed for export] *)
    assert (LENn : Z.of_nat (length bs) = n) by (rewrite LENs; lia).
    set (m_b := wbytes mem (wordZ d) bs) in *.
    assert (FMb : frame_mod mem m_b [(wordZ d, n)]) by (unfold m_b; rewrite <- LENn; apply frame_mod_wbytes; rewrite u_wordZ; lia).
    destruct (kill_nul_eq (set_slots (v1 A) (cm_kill (vs_slots (v1 A)) lo hi)) lo (hi - 1) None) as [nl [EK Hnl]].
    assert (EA : A1k = set_nul (set_slots (v1 A) (cm_kill (vs_slots (v1 A)) lo hi)) nl) by exact EK.
    clearbody A1k. subst A1k. set (A1k := set_nul (set_slots (v1 A) (cm_kill (vs_slots (v1 A)) lo hi)) nl) in *.
    assert (L1 : lgamma A1k nu).
    { destruct HL as (LS&LC&LM&LV&(Bq0&Bq1&Bq2&Bq3&Bq4&Bq5)). split; [exact LS|]. split; [exact LC|]. split; [exact LM|]. split; [exact LV|].
      split; [exact Bq0|]. split; [exact Bq1|]. split; [exact Bq2|]. split; [intros k w e Hin; apply cm_kill_sub in Hin; exact (Bq3 _ _ _ Hin)|]. split; [exact Bq4|exact Bq5]. }
    destruct (gamma_call_post SEGS P1 E1 (zpatch P E mem0 mem) rom PO (v1 A) A1k nu nu regs regs mem m_b [(wordZ d, n)]
                HG1 (ext_refl _ _) ltac:(apply Pos.le_refl) L1) as [Gb _].
    { unfold gamma_regs. cbn. exact HRg. }
    { intros off' w' v' Hin. cbn in Hin. left. split; [eapply cm_kill_sub; exact Hin|]. pose proof (cm_kill_disjoint _ _ _ _ _ _ Hin) as D.
      destruct (HSl _ _ _ (cm_kill_sub _ _ _ _ Hin)) as [(Ra&Rb&Rc) _].
      intros x Hx. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite !u_wordZ by (unfold d, P1, E1 in *; lia). unfold d, P1, E1 in *. lia. }
    { intros ga gw gv Hin. cbn in Hin. split; [exact Hin|]. destruct (HGl _ _ _ Hin) as [(Ra&Rb&Rc) _].
      intros x Hx. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite !u_wordZ by (unfold d, P1, E1 in *; lia). unfold d, P1, E1 in *. lia. }
    { intros mlo mhi Hin. cbn in Hin. destruct (Hnl _ Hin) as [Hold [X|X]]; [cbn in X; discriminate|]. cbn in Hold, X.
      destruct (HN _ _ Hold) as [z [b (Y1&Y2&Y3&Y4)]]. right. exists z, b.
      split; [exact Y1|]. split; [exact Y2|]. split; [|exact Y4].
      rewrite <- Y3. apply (rdn_unchanged SEGS mem0 rom mem m_b [(wordZ d, n)] (e_sp0 E1 + z) 1 (proj1 FMb)); [unfold P1, E1 in *; lia|unfold P1, E1 in *; lia|].
      intros x Hx. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite !u_wordZ by (unfold d, P1, E1 in *; lia). unfold d, P1, E1 in *. lia. }
    { exact FMb. }
    { apply (stack_R_ok SEGS P1 E1 (zpatch P E mem0 mem) PO ov lo hi n); auto; lia. }
    (* [comment removed for export] *)
    assert (QM0 : forall x : word, bv_unsigned x < usp - JUNK4 \/ usp <= bv_unsigned x -> m' x = m_b x) by exact QM.
    assert (GRW : forall x, m_b x <> None -> m' x <> None).
    { intros x Hx. destruct (Z_lt_le_dec (bv_unsigned x) d) as [X1|X1]; [|destruct (Z_lt_le_dec (bv_unsigned x) (d + n)) as [X2|X2]].
      - apply QG. intros M0. apply Hx. unfold m_b. rewrite wbytes_outside; [exact M0| |]; rewrite ?LENn, ?u_wordZ by lia; unfold in_rng; rewrite ?u_wordZ by lia; lia.
      - rewrite QM0; [exact Hx|]. destruct DJ as [DJ0|DJ1]; [lia|right; lia].
      - apply QG. intros M0. apply Hx. unfold m_b. rewrite wbytes_outside; [exact M0| |]; rewrite ?LENn, ?u_wordZ by lia; unfold in_rng; rewrite ?u_wordZ by lia; lia. }
    pose proof (gamma_junk SEGS P1 E1 (zpatch P E mem0 mem) PO A1k nu regs m_b m' spoff 2224 JUNK4 Gb QM0 GRW
                  ltac:(unfold JUNK4; lia) K1 K2) as Gk.
    (* [comment removed for export] *)
    set (Bst := contract_frame C_memset (killK 2224 A1k spoff) spoff (Some de)).
    assert (EFR : frame_rule 2224 A1k spoff (Some de) = Bst) by (apply frame_rule_killK; lia).
    destruct (killK_shape 2224 A1k spoff) as (KS1 & KS2 & KS3 & KS4 & KS5 & KS6 & KS7 & KS8 & KS9).
    destruct (contract_frame_shape C_memset (killK 2224 A1k spoff) spoff (Some de)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & FR).
    assert (N1 : vs_next A1k = vs_next (v1 A)) by reflexivity.
    assert (HLB : lgamma Bst nu).
    { apply lgamma_contract_frame; [apply lgamma_killK; exact L1|]. cbn [vbelow]. rewrite KS4, N1. exact B10. }
    destruct (gamma_call_post SEGS P1 E1 (zpatch P E mem0 mem) rom PO (killK 2224 A1k spoff) Bst nu nu regs regs' m' m' []
                Gk (ext_refl _ _) ltac:(unfold Bst; rewrite F5; apply Pos.le_refl) HLB) as [GB _].
    { eapply (gamma_regs_contract_frame SEGS P1 E1 (zpatch P E mem0 mem) C_memset (killK 2224 A1k spoff) (killK 2224 A1k spoff) spoff (Some de) nu nu regs regs');
        [right; pose proof Gk as (_&_&_&_&_&_&_&KRg&_&_&_&KBl); split; [exact KRg|destruct KBl as (_&_&KRB&_); exact KRB]
        |apply ext_refl|reflexivity|exact QK|].
      rewrite Q10, u_wordZ, Ed by lia. symmetry. apply zwrap_id. lia. }
    { intros off' w' v' Hin. left. unfold Bst in Hin. rewrite F1 in Hin. cbn in Hin. split; [exact Hin|]. intros x _. exact I. }
    { intros g w' v' Hin. unfold Bst in Hin. rewrite F2 in Hin. split; [exact Hin|]. intros x _. exact I. }
    { intros lo' hi' Hin. left. unfold Bst in Hin. destruct (F3 _ Hin) as [Hin' _]. split; [exact Hin'|]. intros x _. exact I. }
    { apply frame_mod_refl. }
    { intros x Hx. exfalso. apply Hx. exact I. }
    (* [comment removed for export] *)
    assert (FMU : frame_mod mem m' (unit_regions P1 E1)).
    { split; [|intros x Hx; apply GRW; unfold m_b; apply wbytes_grows; exact Hx]. intros a Ha.
      assert (NB : ~ (d <= bv_unsigned a < d + n)).
      { intros Hin. refine (proj1 (stack_R_ok SEGS P1 E1 (zpatch P E mem0 mem) PO ov lo hi n H3 H4 H1 H2 Hws HEV1 a _) Ha).
        cbn [outside]. unfold in_rng. rewrite u_wordZ by lia. unfold d in Hin. intros [X _]. apply X. lia. }
      assert (NJ : ~ (usp - JUNK4 <= bv_unsigned a < usp)).
      { intros Hin. refine (proj1 (stack_R_ok SEGS P1 E1 (zpatch P E mem0 mem) PO (spoff - JUNK4) (spoff - 2224) spoff JUNK4
                                 K1 K2 ltac:(unfold JUNK4; lia) ltac:(unfold JUNK4; lia) KW HEV1 a _) Ha).
        cbn [outside]. unfold in_rng. rewrite u_wordZ by (unfold usp, JUNK4, P1, E1 in *; lia). unfold usp in Hin. intros [X _]. apply X. unfold JUNK4 in *. lia. }
      rewrite QM0 by (pose proof (bv_unsigned_in_range 64 a); lia). unfold m_b. apply wbytes_outside; [|rewrite LENn, u_wordZ by lia; lia].
      unfold in_rng. rewrite u_wordZ, LENn by lia. lia. }
    destruct (gamma2_lift SEGS P E mem0 PO2 A Bst nu nu regs regs' mem m' HG2 GB (ext_refl _ _)
                ltac:(unfold Bst; rewrite F5, KS4, N1; apply Pos.le_refl) FMU
                ltac:(unfold globs_ok2, Bst; cbn [v1 with_v1]; rewrite F2, KS2; exact GL2) ltac:(right; exact MEMO))
      as (G3 & FM3 & FST3).
    exists (with_v1 A A1k), (Some de), regs', m', nu.
    replace (contract_frame2 C_asan_memcpy (with_v1 A A1k) spoff (Some de)) with (with_v1 A Bst)
      by (unfold contract_frame2, with_v1; cbn [v1 vs_rgn vs_live vs_divdef vs_memo contract2_K]; rewrite <- EFR; reflexivity).
    split; [left; reflexivity|]. split; [exact MS|]. split; [exact G3|]. split; [exact Q1|].
    split; [apply ext_refl|]. split.
    { unfold vs2_next, Bst. cbn [v1 with_v1]. rewrite F5, KS4, N1. apply Pos.le_refl. }
    split; [exact FM3|exact FST3].
  Qed.

  #[using="P1 E1 PO2 SHOFF ROM_HI FSLEN DATAL MCELLS MCELLS_OK RUN"] Theorem asan_memcpy_post : contract_post2 SEGS P E mem0 rom CI C_asan_memcpy tgt.
  Proof.
    intros A spoff l nu regs mem ra HC HG2 MEMO Hsp HK Hret Hra.
    pose proof HG2 as (HG1 & HE & HM & HF2 & HDD & RGN & LIVE & BEL2 & GL2 & FI2 & MOK).
    pose proof (gamma2_lgamma _ _ _ _ _ _ _ _ HG2) as HL.
    pose proof (PO1 _ _ PO2) as PO. pose proof PO as (P0 & Psphi & PS & PF & PW & PR & PP & PB).
    pose proof HE as (HEV1 & HD2 & HFS & HZO & HKC). pose proof HEV1 as (E1a & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E11 & E12).
    pose proof (proj1 (proj2 HG1)) as (MF & MD & MP & MFM).
    cbn [contract_apply2] in HC. unfold of_ca, ca_asan_memcpy in HC. cbv zeta in HC.
    destruct (nonneg_len (v1 A) (get_reg2 A A2r) MAXLEN) as [nlo nhi| |msg] eqn:En; try discriminate.
    destruct (nonneg_len_sound (v1 A) nu _ _ _ _ HL En) as [ne (Ene & Hn0 & Hn1 & Hn2)].
    destruct (get_reg2 A A0r) as [de|] eqn:Ede; [|discriminate].
    destruct (get_reg2 A A1r) as [se|] eqn:Ese; [|discriminate].
    rewrite Ene in HC. cbn [lin_of] in HC. unfold MAXLEN in Hn2.
    set (n := eval nu ne) in *.
    unfold get_reg2 in Ede, Ese, Ene, En.
    assert (Hn : 0 <= n <= 2 ^ 40) by (clear -Hn0 Hn1 Hn2; lia). clear Hn0. rename Hn into Hn0.
    (* [comment removed for export] *)
    assert (R12 : getr regs 12%bv = wordZ n).
    { apply (reg_word SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem 12%bv ne n HG1); [vm_compute; lia|exact Ene|reflexivity|lia]. }
    pose proof (reg_val SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem 10%bv de HG1 ltac:(vm_compute; lia) Ede) as [V10 B10].
    pose proof (reg_val SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem 11%bv se HG1 ltac:(vm_compute; lia) Ese) as [V11 B11].
    assert (R2 : getr regs 2%bv = wordZ (e_sp0 E1 + spoff)).
    { apply (reg_word SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem 2%bv (lsymc SP0 spoff) (e_sp0 E1 + spoff) HG1);
        [vm_compute; lia|exact Hsp| |].
      - rewrite eval_lsymc. rewrite (proj1 (proj2 (proj2 HG1)) SP0 (e_sp0 E1)) by reflexivity. reflexivity.
      - destruct HK as [HK'|HK']; [cbn in HK'; discriminate|]. apply in_ranges_sound in HK' as (wlo & whi & Hw & W1 & W2).
        destruct (PR _ Hw). cbn [fst snd contract2_K] in *. unfold K_asan_memcpy, P1, E1 in *. lia. }
    (* [comment removed for export] *)
    assert (HKR : - vp_frame P1 <= spoff - 2224 /\ spoff <= 0 /\ exists wr, In wr (vp_wstack P1) /\ fst wr <= spoff - 2224 /\ spoff <= snd wr).
    { destruct HK as [HK'|HK']; [cbn in HK'; discriminate|]. apply in_ranges_sound in HK' as (wlo & whi & Hw & W1 & W2).
      destruct (PR _ Hw). cbn [fst snd contract2_K] in *. unfold K_asan_memcpy, P1, E1 in *. split; [lia|]. split; [lia|].
      exists (wlo, whi). cbn. split; [exact Hw|lia]. }
    destruct HKR as (K1 & K2 & KW).
    set (usp := e_sp0 E1 + spoff) in *.
    assert (USP : 0 <= e_sp0 E1 - vp_frame P1 /\ e_sp0 E1 - vp_frame P1 <= usp - 2224 /\ usp <= e_sp0 E1 /\ e_sp0 E1 < 2 ^ 64)
      by (unfold usp, P1, E1 in *; lia).
    assert (JOK : forall a, usp - JUNK4 <= a < usp -> store_ok SEGS mem (wordZ a) 1 = true).
    { intros a Ha. unfold JUNK4 in Ha. apply (proj1 (MF a ltac:(unfold usp, P1, E1 in *; lia))). }
    pose proof (proj1 (proj2 (proj2 HG1))) as HF1.
    (* [comment removed for export] *)
    destruct (range_check P A se ne false) as [r2 lo2 hi2|rr2| |m2] eqn:RCs; [| |discriminate HC|discriminate HC].
    - (* [comment removed for export] *)
      destruct (range_check_ld_rgn_inv A se ne r2 lo2 hi2 RCs) as (B2 & HBS2 & C21 & C22 & C23 & HGr2 & HKr2 & LET2).
      cbv zeta in LET2. destruct LET2 as (LO2 & HI2 & RLO2 & RHI2 & HRA2 & HFZ2).
      pose proof (rgn_get_in _ _ _ HGr2) as [Hr2 HBr2].
      set (off2 := laddc (lsub se (lsym B2)) (- vr_disp r2)) in *.
      assert (Eoff2 : eval nu se = rbase nu r2 + eval nu off2) by (unfold off2; rewrite <- HBr2, eval_off; lia).
      pose proof (bnd_sound (v1 A) nu off2 HL) as Bs. pose proof (bnd_sound (v1 A) nu (ladd off2 ne) HL) as Bs1.
      unfold lo_of in LO2. unfold hi_of in HI2.
      destruct (bnd (v1 A) off2) as [slo0 shi0] eqn:Ebs. cbn [fst] in LO2. subst slo0.
      destruct (bnd (v1 A) (ladd off2 ne)) as [slo1 shi1] eqn:Ebs1. cbn [snd] in HI2. subst shi1.
      destruct Bs as [Bs _]. destruct Bs1 as [_ Bs1]. cbn [fst snd lo_le hi_ge] in Bs, Bs1. rewrite eval_ladd in Bs1. fold n in Bs1.
      set (sov := eval nu off2) in *. set (s := rbase nu r2 + sov) in *.
      destruct (rgn_range_facts A nu regs mem B2 r2 lo2 hi2 sov n HG2 HGr2 HKr2 RLO2 RHI2 HRA2 HFZ2 Bs Bs1 ltac:(lia))
        as (SACC & (fa2 & cid2 & Hcid2 & FA21 & FA22 & FA23 & FA24 & FK2) & FSnz0 & SRNG & SRD).
      cbv zeta in SACC. fold s in SACC.
      assert (R11 : getr regs 11%bv = wordZ s).
      { apply wordZ_eq_u. rewrite V11, Eoff2. fold sov. unfold s. apply zwrap_id. unfold HIGH_MEM_BEG in *. clear -SRNG Bs Bs1 Hn0. lia. }

      destruct (range_check P A de ne true) as [r lo hi|rr| |m1] eqn:RCd; [| |discriminate HC|discriminate HC].
      + (* [comment removed for export] *)
        destruct (range_check_rgn_inv P A de ne r lo hi RCd) as (B & HBS & C1 & C2 & C3 & HGr & HKr & LET).
        cbv zeta in LET. destruct LET as (LO & HI & RLO & RHI & HWr & HRA & HFZ).
        pose proof (rgn_get_in _ _ _ HGr) as [Hr HBr].
        set (off := laddc (lsub de (lsym B)) (- vr_disp r)) in *.
        assert (Eoff : eval nu de = rbase nu r + eval nu off) by (unfold off; rewrite <- HBr, eval_off; lia).
        pose proof (bnd_sound (v1 A) nu off HL) as Bo. pose proof (bnd_sound (v1 A) nu (ladd off ne) HL) as Bo1.
        unfold lo_of in LO. unfold hi_of in HI.
        destruct (bnd (v1 A) off) as [olo ohi] eqn:Ebo. cbn [fst] in LO. subst olo.
        destruct (bnd (v1 A) (ladd off ne)) as [olo1 ohi1] eqn:Ebo1. cbn [snd] in HI. subst ohi1.
        destruct Bo as [Bo _]. destruct Bo1 as [_ Bo1]. cbn [fst snd lo_le hi_ge] in Bo, Bo1. rewrite eval_ladd in Bo1. fold n in Bo1.
        set (ov := eval nu off) in *. set (d := rbase nu r + ov) in *.
        (* [comment removed for export] *)
        try match type of HC with context [if ?b then CA_fail _ else (if negb (0 <? nlo) then _ else _)] => destruct b eqn:AL; [discriminate HC|] end.
        destruct (Z.ltb_spec 0 nlo) as [NLO|]; cbn [negb] in HC; [|discriminate]. cbn [ca_ok1] in HC. injection HC as <-.
        destruct (rgn_range_facts A nu regs mem B r lo hi ov n HG2 HGr HKr RLO RHI HRA HFZ Bo Bo1 ltac:(lia))
          as (_ & (fa & cid & Hcid & FA1 & FA2 & FA3 & FA4 & FK) & FSnz & DRNG & _).
        assert (R10 : getr regs 10%bv = wordZ d).
        { apply wordZ_eq_u. rewrite V10, Eoff. fold ov. unfold d. apply zwrap_id. unfold HIGH_MEM_BEG in *. clear -DRNG Bo Bo1 Hn0. lia. }

        assert (EXfs : exists ls, vp_fs P = Some ls) by (destruct (vp_fs P) as [ls|]; [exists ls; reflexivity|exfalso; exact (FSnz eq_refl)]).
        destruct EXfs as [[flen fssl] EFS]. unfold env_fs in HFS. rewrite EFS in HFS.
        destruct HFS as (_ & FS1 & FS2 & FS3 & FS4 & _ & _ & APsf & APdf & APds & HMsp & HMd & _ & SPHI & _).
        pose proof (FSLEN _ _ EFS) as FS5.

        assert (SOK : src_ok mem usp s n).
        { split; [unfold s in *; unfold HIGH_MEM_BEG in *; clear -SRNG Bs; lia|]. split; [unfold s in *; clear -SRNG Bs1 Hn0; lia|].
          split; [intros _; apply (band_ok_mono _ _ _ _ (proj2 (proj2 SRNG))); unfold s; clear -Bs Bs1; lia|].
          split; [right; unfold JUNK4, s, usp, FS_FRAMES, FS_NCLASSES, FS_SSL, P1, E1 in *; clear -FA21 FA22 FA23 FA24 Bs Bs1 APsf FS5 USP; lia|].
          split; [intros Hnp; unfold SBz, usp; apply (arith_shd4_low (e_sp0 E1) (vp_frame P1) spoff (s + n - 1)); unfold s in *; unfold HIGH_MEM_BEG, P1, E1 in *; clear -HMsp K1 SRNG Bs Bs1 Hn0 Hnp; lia|].
          split; [exact SACC|].
          intros i Hi. unfold s. replace (rbase nu r2 + sov + i) with (rbase nu r2 + (sov + i)) by lia. apply SRD. clear -Hi Bs Bs1. lia. }

        assert (DISJ : n = 0 \/ s + n <= d \/ d + n <= s).
        { right. destruct (Pos.eqb_spec (vr_base r2) (vr_base r)) as [EB|NB].
          - apply Bool.negb_false_iff in AL.
            destruct (disjoint_ranges_sound (v1 A) nu de se ne HL AL) as [X|X]; rewrite Eoff, Eoff2 in X; fold ov sov n in X; unfold d, s in *; clear -X; lia.
          - (* [comment removed for export] *)
            assert (NE : exists pos pos2, 0 <= pos < fs_nframes cid /\ fa = frame_addr (e_fs E) cid pos
                           /\ 0 <= pos2 < fs_nframes cid2 /\ fa2 = frame_addr (e_fs E) cid2 pos2 /\ (cid <> cid2 \/ pos <> pos2)).
            { pose proof LIVE as (_ & _ & LV3 & _). specialize (LV3 r r2 Hr Hr2).
              destruct (vr_kind r) as [c fl| |ao|sx|] eqn:Kr; try contradiction;
              destruct (vr_kind r2) as [c2 fl2| |ao2|sx2|] eqn:Kr2; try contradiction; try discriminate AL.
              + destruct FK as (Ec & Efa & pos & Hpos & Efp & NL). destruct FK2 as (Ec2 & Efa2 & pos2 & Hpos2 & Efp2 & NL2).
                exists pos, pos2. split; [exact Hpos|]. split; [exact Efp|]. split; [exact Hpos2|]. split; [exact Efp2|].
                destruct (Z.eq_dec cid cid2) as [EC|NC]; [|left; exact NC]. destruct (Z.eq_dec pos pos2) as [EP|NP]; [|right; exact NP].
                exfalso. apply (LV3 ltac:(intros X; apply NB; symmetry; exact X)). rewrite <- Efa, <- Efa2, Efp, Efp2, EC, EP. reflexivity.
              + destruct FK as (Ec & Efa & pos & Hpos & Efp & NL). destruct FK2 as (pos2 & IL2 & Hpos2 & Efp2).
                exists pos, pos2. split; [exact Hpos|]. split; [exact Efp|]. split; [exact Hpos2|]. split; [exact Efp2|].
                destruct (Z.eq_dec cid cid2) as [EC|NC]; [|left; exact NC]. destruct (Z.eq_dec pos pos2) as [EP|NP]; [|right; exact NP].
                exfalso. apply NL. rewrite EC, EP. exact IL2.
              + destruct FK as (pos & IL & Hpos & Efp). destruct FK2 as (Ec2 & Efa2 & pos2 & Hpos2 & Efp2 & NL2).
                exists pos, pos2. split; [exact Hpos|]. split; [exact Efp|]. split; [exact Hpos2|]. split; [exact Efp2|].
                destruct (Z.eq_dec cid cid2) as [EC|NC]; [|left; exact NC]. destruct (Z.eq_dec pos pos2) as [EP|NP]; [|right; exact NP].
                exfalso. apply NL2. rewrite <- EC, <- EP. exact IL. }
            destruct NE as (pos & pos2 & Hpos & Efp & Hpos2 & Efp2 & NEQ).
            destruct (frames_disjoint (e_fs E) cid pos cid2 pos2 ltac:(clear -Hcid; lia) Hpos ltac:(clear -Hcid2; lia) Hpos2 NEQ) as [X|X];
              rewrite <- Efp, <- Efp2 in X; unfold d, s in *; clear -X FA3 FA4 FA23 FA24 Bo Bo1 Bs Bs1; lia. }
        exact (post_rgn A spoff nu regs mem ra de ne n B r lo hi ov s HG2 MEMO Hsp K1 K2 KW Hret Hra Ede B10 eq_refl Hn0
                 R12 R2 HGr HBr HKr RLO RHI HWr HRA HFZ Eoff Bo Bo1 ltac:(clear -NLO Hn1; lia) R10 R11 SOK DISJ).

      + (* [comment removed for export] *)
        destruct (range_check_v1_inv P A de ne rr RCd) as (off & lo & hi & -> & Esr & Hab & Hsa & Hsw).

        cbn [ca_ok1] in HC. injection HC as <-.
        destruct (stack_range_sound P1 E1 (v1 A) nu de ne true off lo hi HL HF1 Esr) as (_ & Ed & Hd1 & Hd2 & Hd3 & Hd4 & _). fold n in Hd2.
        set (ov := eval nu off) in *. set (d := e_sp0 E1 + ov) in *.
        destruct (stack_range_facts A nu regs mem lo hi ov n HG2 Hsa Hsw Hd1 Hd2 Hd3 Hd4 ltac:(lia)) as (_ & FSnz & DHM & DSPHI & _ & _).

        assert (EXfs : exists ls, vp_fs P = Some ls) by (destruct (vp_fs P) as [ls|]; [exists ls; reflexivity|exfalso; exact (FSnz eq_refl)]).
        destruct EXfs as [[flen fssl] EFS]. unfold env_fs in HFS. rewrite EFS in HFS.
        destruct HFS as (_ & FS1 & FS2 & FS3 & FS4 & _ & _ & APsf & APdf & APds & HMsp & HMd & _ & SPHI & _).
        pose proof (FSLEN _ _ EFS) as FS5.

        assert (SOK : src_ok mem usp s n).
        { split; [unfold s in *; unfold HIGH_MEM_BEG in *; clear -SRNG Bs; lia|]. split; [unfold s in *; clear -SRNG Bs1 Hn0; lia|].
          split; [intros _; apply (band_ok_mono _ _ _ _ (proj2 (proj2 SRNG))); unfold s; clear -Bs Bs1; lia|].
          split; [right; unfold JUNK4, s, usp, FS_FRAMES, FS_NCLASSES, FS_SSL, P1, E1 in *; clear -FA21 FA22 FA23 FA24 Bs Bs1 APsf FS5 USP; lia|].
          split; [intros Hnp; unfold SBz, usp; apply (arith_shd4_low (e_sp0 E1) (vp_frame P1) spoff (s + n - 1)); unfold s in *; unfold HIGH_MEM_BEG, P1, E1 in *; clear -HMsp K1 SRNG Bs Bs1 Hn0 Hnp; lia|].
          split; [exact SACC|].
          intros i Hi. unfold s. replace (rbase nu r2 + sov + i) with (rbase nu r2 + (sov + i)) by lia. apply SRD. clear -Hi Bs Bs1. lia. }

        assert (DISJ : n = 0 \/ s + n <= d \/ d + n <= s).
        { right. unfold d, s in *. unfold FS_FRAMES, FS_NCLASSES, FS_SSL, P1, E1 in *. clear -FA21 FA22 FA23 FA24 Bs Bs1 Hd1 Hd2 Hd3 Hd4 APsf FS5 P0. lia. }
        exact (post_stk A spoff nu regs mem ra de ne n off lo hi s HG2 MEMO Hsp K1 K2 KW Hret Hra Ede B10 eq_refl Hn0
                 R12 R2 Esr Hab Hsa Hsw R11 SOK DISJ).

    - (* [comment removed for export] *)
      destruct (range_check_ld_v1_inv A se ne rr2 RCs) as [(so & slo & shi & -> & RRs & Hab2 & Hsa2 & Hsw2)|[(doff & -> & RRs)|(ilo & ihi & ->)]]; [| |discriminate HC].
      + (* [comment removed for export] *)
        pose proof (readable_range_stack P1 (v1 A) se ne so slo shi RRs) as SRs.
        destruct (stack_range_sound P1 E1 (v1 A) nu se ne false so slo shi HL HF1 SRs) as (_ & Es & Ss1 & Ss2 & Ss3 & Ss4 & _).
        fold n in Ss2. set (sov := eval nu so) in *. set (s := e_sp0 E1 + sov) in *.
        destruct (stack_range_facts A nu regs mem slo shi sov n HG2 Hsa2 Hsw2 Ss1 Ss2 Ss3 Ss4 ltac:(lia)) as (SACC & FSnz0 & SHM & SSPHI & SSP0al & SRD).
        cbv zeta in SACC. fold s in SACC.
        pose proof (above_sp_sound A spoff slo shi Hsp Hab2) as HAB2.
        assert (R11 : getr regs 11%bv = wordZ s).
        { apply wordZ_eq_u. rewrite V11, Es. apply zwrap_id. unfold s, HIGH_MEM_BEG, HIGH_MEM_END, P1, E1 in *. clear -SHM Ss1 Ss2 Ss3 Ss4 SSPHI P0 Hn0. lia. }

        destruct (range_check P A de ne true) as [r lo hi|rr| |m1] eqn:RCd; [| |discriminate HC|discriminate HC].
        * (* [comment removed for export] *)
          destruct (range_check_rgn_inv P A de ne r lo hi RCd) as (B & HBS & C1 & C2 & C3 & HGr & HKr & LET).
          cbv zeta in LET. destruct LET as (LO & HI & RLO & RHI & HWr & HRA & HFZ).
          pose proof (rgn_get_in _ _ _ HGr) as [Hr HBr].
          set (off := laddc (lsub de (lsym B)) (- vr_disp r)) in *.
          assert (Eoff : eval nu de = rbase nu r + eval nu off) by (unfold off; rewrite <- HBr, eval_off; lia).
          pose proof (bnd_sound (v1 A) nu off HL) as Bo. pose proof (bnd_sound (v1 A) nu (ladd off ne) HL) as Bo1.
          unfold lo_of in LO. unfold hi_of in HI.
          destruct (bnd (v1 A) off) as [olo ohi] eqn:Ebo. cbn [fst] in LO. subst olo.
          destruct (bnd (v1 A) (ladd off ne)) as [olo1 ohi1] eqn:Ebo1. cbn [snd] in HI. subst ohi1.
          destruct Bo as [Bo _]. destruct Bo1 as [_ Bo1]. cbn [fst snd lo_le hi_ge] in Bo, Bo1. rewrite eval_ladd in Bo1. fold n in Bo1.
          set (ov := eval nu off) in *. set (d := rbase nu r + ov) in *.
          (* [comment removed for export] *)
          try match type of HC with context [if ?b then CA_fail _ else (if negb (0 <? nlo) then _ else _)] => destruct b eqn:AL; [discriminate HC|] end.
          destruct (Z.ltb_spec 0 nlo) as [NLO|]; cbn [negb] in HC; [|discriminate]. cbn [ca_ok1] in HC. injection HC as <-.
          destruct (rgn_range_facts A nu regs mem B r lo hi ov n HG2 HGr HKr RLO RHI HRA HFZ Bo Bo1 ltac:(lia))
            as (_ & (fa & cid & Hcid & FA1 & FA2 & FA3 & FA4 & FK) & FSnz & DRNG & _).
          assert (R10 : getr regs 10%bv = wordZ d).
          { apply wordZ_eq_u. rewrite V10, Eoff. fold ov. unfold d. apply zwrap_id. unfold HIGH_MEM_BEG in *. clear -DRNG Bo Bo1 Hn0. lia. }

          assert (EXfs : exists ls, vp_fs P = Some ls) by (destruct (vp_fs P) as [ls|]; [exists ls; reflexivity|exfalso; exact (FSnz eq_refl)]).
        destruct EXfs as [[flen fssl] EFS]. unfold env_fs in HFS. rewrite EFS in HFS.
          destruct HFS as (_ & FS1 & FS2 & FS3 & FS4 & _ & _ & APsf & APdf & APds & HMsp & HMd & _ & SPHI & _).
          pose proof (FSLEN _ _ EFS) as FS5.

          assert (SOK : src_ok mem usp s n).
          { split; [unfold s in *; unfold HIGH_MEM_BEG, P1, E1 in *; clear -SHM Ss1 Ss3 P0; lia|]. split; [unfold s in *; unfold HIGH_MEM_END, E1 in *; clear -Ss2 Ss4 SSPHI Hn0; lia|].
            split; [intros _; apply band_ok_high; unfold s in *; unfold HIGH_MEM_BEG, HIGH_MEM_END, P1, E1 in *; clear -SHM Ss1 Ss2 Ss3 Ss4 SSPHI P0; lia|].
            split; [destruct (Z.eq_dec n 0) as [N0|N0]; [left; exact N0|right; left]; unfold s, usp in *; clear -HAB2 Ss1 Ss2 N0 Hn0; lia|].
            split; [intros Hn'; unfold SBz, usp; apply (arith_shd4 (e_sp0 E1) (vp_frame P1) spoff (s + n - 1) SSP0al); unfold s in *; unfold HIGH_MEM_BEG, HIGH_MEM_END, P1, E1 in *; clear -SHM SSPHI K1 Ss1 Ss2 Ss3 Ss4 Hn' P0; lia|].
            split; [exact SACC|].
            intros i Hi. unfold s. replace (e_sp0 E1 + sov + i) with (e_sp0 E1 + (sov + i)) by lia. apply SRD. clear -Hi Ss1 Ss2. lia. }

          assert (DISJ : n = 0 \/ s + n <= d \/ d + n <= s).
          { right. unfold d, s in *. unfold FS_FRAMES, FS_NCLASSES, FS_SSL, P1, E1 in *. clear -FA1 FA2 FA3 FA4 Bo Bo1 Ss1 Ss2 Ss3 Ss4 APsf FS5 P0. lia. }
          exact (post_rgn A spoff nu regs mem ra de ne n B r lo hi ov s HG2 MEMO Hsp K1 K2 KW Hret Hra Ede B10 eq_refl Hn0
                   R12 R2 HGr HBr HKr RLO RHI HWr HRA HFZ Eoff Bo Bo1 ltac:(clear -NLO Hn1; lia) R10 R11 SOK DISJ).

        * (* [comment removed for export] *)
          destruct (range_check_v1_inv P A de ne rr RCd) as (off & lo & hi & -> & Esr & Hab & Hsa & Hsw).

          destruct (disjoint_ranges (v1 A) de se ne) eqn:DR; cbn [negb lift_cresA] in HC; [|discriminate].
          unfold c_memcpy, getA in HC. rewrite En, Ene, Ede, Ese in HC. cbn [lin_of] in HC. unfold P1 in Esr. rewrite Esr in HC.
          unfold P1 in RRs. rewrite RRs in HC. cbv zeta in HC. cbn [ca_ok1] in HC. injection HC as <-. fold P1 in Esr, RRs.
          destruct (stack_range_sound P1 E1 (v1 A) nu de ne true off lo hi HL HF1 Esr) as (_ & Ed & Hd1 & Hd2 & Hd3 & Hd4 & _). fold n in Hd2.
          set (ov := eval nu off) in *. set (d := e_sp0 E1 + ov) in *.
          destruct (stack_range_facts A nu regs mem lo hi ov n HG2 Hsa Hsw Hd1 Hd2 Hd3 Hd4 ltac:(lia)) as (_ & FSnz & DHM & DSPHI & _ & _).

          assert (EXfs : exists ls, vp_fs P = Some ls) by (destruct (vp_fs P) as [ls|]; [exists ls; reflexivity|exfalso; exact (FSnz eq_refl)]).
        destruct EXfs as [[flen fssl] EFS]. unfold env_fs in HFS. rewrite EFS in HFS.
          destruct HFS as (_ & FS1 & FS2 & FS3 & FS4 & _ & _ & APsf & APdf & APds & HMsp & HMd & _ & SPHI & _).
          pose proof (FSLEN _ _ EFS) as FS5.

          assert (SOK : src_ok mem usp s n).
          { split; [unfold s in *; unfold HIGH_MEM_BEG, P1, E1 in *; clear -SHM Ss1 Ss3 P0; lia|]. split; [unfold s in *; unfold HIGH_MEM_END, E1 in *; clear -Ss2 Ss4 SSPHI Hn0; lia|].
            split; [intros _; apply band_ok_high; unfold s in *; unfold HIGH_MEM_BEG, HIGH_MEM_END, P1, E1 in *; clear -SHM Ss1 Ss2 Ss3 Ss4 SSPHI P0; lia|].
            split; [destruct (Z.eq_dec n 0) as [N0|N0]; [left; exact N0|right; left]; unfold s, usp in *; clear -HAB2 Ss1 Ss2 N0 Hn0; lia|].
            split; [intros Hn'; unfold SBz, usp; apply (arith_shd4 (e_sp0 E1) (vp_frame P1) spoff (s + n - 1) SSP0al); unfold s in *; unfold HIGH_MEM_BEG, HIGH_MEM_END, P1, E1 in *; clear -SHM SSPHI K1 Ss1 Ss2 Ss3 Ss4 Hn' P0; lia|].
            split; [exact SACC|].
            intros i Hi. unfold s. replace (e_sp0 E1 + sov + i) with (e_sp0 E1 + (sov + i)) by lia. apply SRD. clear -Hi Ss1 Ss2. lia. }

          assert (DISJ : n = 0 \/ s + n <= d \/ d + n <= s).
          { right. destruct (disjoint_ranges_sound (v1 A) nu de se ne HL DR) as [X|X]; rewrite Ed, Es in X; fold n in X; clear -X; lia. }
          exact (post_stk A spoff nu regs mem ra de ne n off lo hi s HG2 MEMO Hsp K1 K2 KW Hret Hra Ede B10 eq_refl Hn0
                   R12 R2 Esr Hab Hsa Hsw R11 SOK DISJ).

      + (* [comment removed for export] *)
        destruct (range_check P A de ne true) as [r lo hi|rr| |m1] eqn:RCd; [| |discriminate HC|discriminate HC].
        * (* [comment removed for export] *)
          destruct (range_check_rgn_inv P A de ne r lo hi RCd) as (B & HBS & C1 & C2 & C3 & HGr & HKr & LET).
          cbv zeta in LET. destruct LET as (LO & HI & RLO & RHI & HWr & HRA & HFZ).
          pose proof (rgn_get_in _ _ _ HGr) as [Hr HBr].
          set (off := laddc (lsub de (lsym B)) (- vr_disp r)) in *.
          assert (Eoff : eval nu de = rbase nu r + eval nu off) by (unfold off; rewrite <- HBr, eval_off; lia).
          pose proof (bnd_sound (v1 A) nu off HL) as Bo. pose proof (bnd_sound (v1 A) nu (ladd off ne) HL) as Bo1.
          unfold lo_of in LO. unfold hi_of in HI.
          destruct (bnd (v1 A) off) as [olo ohi] eqn:Ebo. cbn [fst] in LO. subst olo.
          destruct (bnd (v1 A) (ladd off ne)) as [olo1 ohi1] eqn:Ebo1. cbn [snd] in HI. subst ohi1.
          destruct Bo as [Bo _]. destruct Bo1 as [_ Bo1]. cbn [fst snd lo_le hi_ge] in Bo, Bo1. rewrite eval_ladd in Bo1. fold n in Bo1.
          set (ov := eval nu off) in *. set (d := rbase nu r + ov) in *.
          (* [comment removed for export] *)
          try match type of HC with context [if ?b then CA_fail _ else (if negb (0 <? nlo) then _ else _)] => destruct b eqn:AL; [discriminate HC|] end.
          destruct (Z.ltb_spec 0 nlo) as [NLO|]; cbn [negb] in HC; [|discriminate]. cbn [ca_ok1] in HC. injection HC as <-.
          destruct (rgn_range_facts A nu regs mem B r lo hi ov n HG2 HGr HKr RLO RHI HRA HFZ Bo Bo1 ltac:(lia))
            as (_ & (fa & cid & Hcid & FA1 & FA2 & FA3 & FA4 & FK) & FSnz & DRNG & _).
          assert (R10 : getr regs 10%bv = wordZ d).
          { apply wordZ_eq_u. rewrite V10, Eoff. fold ov. unfold d. apply zwrap_id. unfold HIGH_MEM_BEG in *. clear -DRNG Bo Bo1 Hn0. lia. }

          assert (EXfs : exists ls, vp_fs P = Some ls) by (destruct (vp_fs P) as [ls|]; [exists ls; reflexivity|exfalso; exact (FSnz eq_refl)]).
        destruct EXfs as [[flen fssl] EFS]. unfold env_fs in HFS. rewrite EFS in HFS.
          destruct HFS as (_ & FS1 & FS2 & FS3 & FS4 & _ & _ & APsf & APdf & APds & HMsp & HMd & _ & SPHI & _).
          pose proof (FSLEN _ _ EFS) as FS5.

          destruct (readable_range_data_inv (v1 A) nu se ne doff HL HF1 RRs) as [SD1 SD2]. fold n in SD2.
          set (s := eval nu se) in *.
          destruct (data_range_facts A nu regs mem (s - e_data E1) n HG2 FSnz ltac:(lia) ltac:(lia) ltac:(lia)) as (SACC & SHM & SD8 & SAP & SRD).
          cbv zeta in SACC. replace (e_data E1 + (s - e_data E1)) with s in SACC by lia.
          assert (R11 : getr regs 11%bv = wordZ s).
          { apply wordZ_eq_u. rewrite V11. fold s. apply zwrap_id. unfold E1 in *. clear -SD1 SD2 E5 E6 Hn0. lia. }

          assert (SOK : src_ok mem usp s n).
          { split; [unfold E1 in *; clear -SD1 E5; lia|]. split; [unfold E1 in *; clear -SD2 E6 Hn0; lia|].
            split; [intros Hn'; destruct (SHM ltac:(clear -Hn' SD1 SD2; lia)) as [M1 M2]; apply (band_ok_in (e_data E1) (e_size E1) _ _ (proj1 M1)); unfold HIGH_MEM_END in *; clear -M1 M2 SD1 SD2; lia|].
            split; [right; unfold JUNK4, usp, P1, E1 in *; clear -SAP SD1 SD2 USP; lia|].
            split; [intros Hn'; destruct (SHM ltac:(clear -Hn' SD1 SD2; lia)) as [M1 M2]; unfold SBz, usp;
                   apply (arith_shd4_low (e_sp0 E1) (vp_frame P1) spoff (s + n - 1)); unfold HIGH_MEM_BEG, HIGH_MEM_END, P1, E1 in *; clear -HMsp K1 M1 M2 SD1 SD2 Hn'; lia|].
            split; [exact SACC|].
            intros i Hi. replace (s + i) with (e_data E1 + (s - e_data E1 + i)) by lia. apply SRD. clear -Hi SD1 SD2. lia. }

          assert (DISJ : n = 0 \/ s + n <= d \/ d + n <= s).
          { right. unfold d, FS_FRAMES, FS_NCLASSES, FS_SSL, E1 in *. clear -FA1 FA2 FA3 FA4 Bo Bo1 SD1 SD2 APdf FS5. lia. }
          exact (post_rgn A spoff nu regs mem ra de ne n B r lo hi ov s HG2 MEMO Hsp K1 K2 KW Hret Hra Ede B10 eq_refl Hn0
                   R12 R2 HGr HBr HKr RLO RHI HWr HRA HFZ Eoff Bo Bo1 ltac:(clear -NLO Hn1; lia) R10 R11 SOK DISJ).

        * (* [comment removed for export] *)
          destruct (range_check_v1_inv P A de ne rr RCd) as (off & lo & hi & -> & Esr & Hab & Hsa & Hsw).

          cbn [lift_cresA] in HC.
          unfold c_memcpy, getA in HC. rewrite En, Ene, Ede, Ese in HC. cbn [lin_of] in HC. unfold P1 in Esr. rewrite Esr in HC.
          unfold P1 in RRs. rewrite RRs in HC. cbv zeta in HC. cbn [ca_ok1] in HC. injection HC as <-. fold P1 in Esr, RRs.
          destruct (stack_range_sound P1 E1 (v1 A) nu de ne true off lo hi HL HF1 Esr) as (_ & Ed & Hd1 & Hd2 & Hd3 & Hd4 & _). fold n in Hd2.
          set (ov := eval nu off) in *. set (d := e_sp0 E1 + ov) in *.
          destruct (stack_range_facts A nu regs mem lo hi ov n HG2 Hsa Hsw Hd1 Hd2 Hd3 Hd4 ltac:(lia)) as (_ & FSnz & DHM & DSPHI & _ & _).

          assert (EXfs : exists ls, vp_fs P = Some ls) by (destruct (vp_fs P) as [ls|]; [exists ls; reflexivity|exfalso; exact (FSnz eq_refl)]).
        destruct EXfs as [[flen fssl] EFS]. unfold env_fs in HFS. rewrite EFS in HFS.
          destruct HFS as (_ & FS1 & FS2 & FS3 & FS4 & _ & _ & APsf & APdf & APds & HMsp & HMd & _ & SPHI & _).
          pose proof (FSLEN _ _ EFS) as FS5.

          destruct (readable_range_data_inv (v1 A) nu se ne doff HL HF1 RRs) as [SD1 SD2]. fold n in SD2.
          set (s := eval nu se) in *.
          destruct (data_range_facts A nu regs mem (s - e_data E1) n HG2 FSnz ltac:(lia) ltac:(lia) ltac:(lia)) as (SACC & SHM & SD8 & SAP & SRD).
          cbv zeta in SACC. replace (e_data E1 + (s - e_data E1)) with s in SACC by lia.
          assert (R11 : getr regs 11%bv = wordZ s).
          { apply wordZ_eq_u. rewrite V11. fold s. apply zwrap_id. unfold E1 in *. clear -SD1 SD2 E5 E6 Hn0. lia. }

          assert (SOK : src_ok mem usp s n).
          { split; [unfold E1 in *; clear -SD1 E5; lia|]. split; [unfold E1 in *; clear -SD2 E6 Hn0; lia|].
            split; [intros Hn'; destruct (SHM ltac:(clear -Hn' SD1 SD2; lia)) as [M1 M2]; apply (band_ok_in (e_data E1) (e_size E1) _ _ (proj1 M1)); unfold HIGH_MEM_END in *; clear -M1 M2 SD1 SD2; lia|].
            split; [right; unfold JUNK4, usp, P1, E1 in *; clear -SAP SD1 SD2 USP; lia|].
            split; [intros Hn'; destruct (SHM ltac:(clear -Hn' SD1 SD2; lia)) as [M1 M2]; unfold SBz, usp;
                   apply (arith_shd4_low (e_sp0 E1) (vp_frame P1) spoff (s + n - 1)); unfold HIGH_MEM_BEG, HIGH_MEM_END, P1, E1 in *; clear -HMsp K1 M1 M2 SD1 SD2 Hn'; lia|].
            split; [exact SACC|].
            intros i Hi. replace (s + i) with (e_data E1 + (s - e_data E1 + i)) by lia. apply SRD. clear -Hi SD1 SD2. lia. }

          assert (DISJ : n = 0 \/ s + n <= d \/ d + n <= s).
          { right. unfold d, P1, E1 in *. clear -Hd1 Hd2 Hd3 Hd4 SD1 SD2 APds P0. lia. }
          exact (post_stk A spoff nu regs mem ra de ne n off lo hi s HG2 MEMO Hsp K1 K2 KW Hret Hra Ede B10 eq_refl Hn0
                   R12 R2 Esr Hab Hsa Hsw R11 SOK DISJ).

  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="P1 E1 PO2"] Lemma range_check_not_dead A nu regs mem de ne st :
    gamma2P A nu regs mem -> 0 <= eval nu ne -> range_check P A de ne st = RA_dead -> False.
  Proof.
    intros HG2 Hn RC. pose proof HG2 as (HG1 & _). pose proof (gamma2_lgamma _ _ _ _ _ _ _ _ HG2) as HL. pose proof (PO1 _ _ PO2) as PO.
    unfold range_check in RC. destruct (base_syms A de) as [|B [|B2 t]]; try discriminate.
    - destruct st.
      + destruct (stack_range (p1 P) (v1 A) de ne true) as [off lo hi| | | |m] eqn:Esr; try discriminate;
          [|exact (stack_range_dead (p1 P) (v1 A) nu _ _ true HL Esr)].
        repeat match type of RC with (if ?c then _ else _) = _ => destruct c; try discriminate end.
      + pose proof (readable_range_sound SEGS P1 E1 (zpatch P E mem0 mem) PO (v1 A) nu regs mem de ne _ HG1 Hn eq_refl) as RS.
        unfold P1 in RS. destruct (readable_range (p1 P) (v1 A) de ne); try discriminate; try exact RS.
        repeat match type of RC with (if ?c then _ else _) = _ => destruct c; try discriminate end.
    - destruct (negb _ || negb _); [discriminate|]. destruct (rgn_get (vs_rgn A) B) as [r|]; [|discriminate].
      destruct (vr_kind r); try discriminate;
        (destruct (dead_lin (v1 A) (laddc (lsub de (lsym B)) (- vr_disp r))) eqn:D1;
           [exact (dead_lin_false (v1 A) nu _ HL D1)|]);
        (destruct (dead_lin (v1 A) (ladd (laddc (lsub de (lsym B)) (- vr_disp r)) ne)) eqn:D2;
           [exact (dead_lin_false (v1 A) nu _ HL D2)|]); cbn [orb] in RC;
        destruct (lo_of (v1 A) _); try discriminate; destruct (hi_of (v1 A) _); try discriminate;
        repeat match type of RC with (if ?c then _ else _) = _ => destruct c; try discriminate end.
  Qed.

  #[using="P1 E1 PO2"] Theorem asan_memcpy_dead : contract_dead2 SEGS P E mem0 CI C_asan_memcpy.
  Proof.
    intros A spoff nu regs mem HC HG2. pose proof (gamma2_lgamma _ _ _ _ _ _ _ _ HG2) as HL.
    pose proof HG2 as (HG1 & _). pose proof (PO1 _ _ PO2) as PO.
    cbn [contract_apply2] in HC. unfold of_ca, ca_asan_memcpy in HC. cbv zeta in HC. unfold get_reg2 in HC.
    destruct (nonneg_len (v1 A) (get_reg (v1 A) A2r) MAXLEN) as [nlo nhi| |msg] eqn:En; try discriminate;
      [|exact (nonneg_len_dead (v1 A) nu _ _ HL En)].
    destruct (nonneg_len_sound (v1 A) nu _ _ _ _ HL En) as [ne (Ene & Hn0 & Hn1 & Hn2)]. rewrite Ene in HC. cbn [lin_of] in HC.
    destruct (get_reg (v1 A) A0r) as [de|] eqn:Ede; [|discriminate]. destruct (get_reg (v1 A) A1r) as [se|] eqn:Ese; [|discriminate].
    destruct (range_check P A se ne false) as [r2 lo2 hi2|rr2| |m2] eqn:RCs;
      [| |exact (range_check_not_dead A nu regs mem se ne false HG2 ltac:(lia) RCs)|discriminate HC].
    - destruct (range_check P A de ne true) as [r lo hi|rr| |m1] eqn:RCd;
        [| |exact (range_check_not_dead A nu regs mem de ne true HG2 ltac:(lia) RCd)|discriminate HC].
      + repeat match type of HC with (match (if ?c then _ else _) with _ => _ end) = _ => destruct c; try discriminate HC end.
      + destruct rr; discriminate HC.
    - destruct (range_check_ld_v1_inv A se ne rr2 RCs) as [(so & slo & shi & -> & RRs & _)|[(doff & -> & RRs)|(ilo & ihi & ->)]]; [| |discriminate HC].
      + destruct (range_check P A de ne true) as [r lo hi|rr| |m1] eqn:RCd;
          [| |exact (range_check_not_dead A nu regs mem de ne true HG2 ltac:(lia) RCd)|discriminate HC].
        * repeat match type of HC with (match (if ?c then _ else _) with _ => _ end) = _ => destruct c; try discriminate HC end.
        * destruct (range_check_v1_inv P A de ne rr RCd) as (off' & lo' & hi' & -> & Esr & _).
          destruct (negb (disjoint_ranges (v1 A) de se ne)); [discriminate HC|]. cbn [lift_cresA] in HC.
          unfold c_memcpy, getA in HC. rewrite En, Ene, Ede, Ese in HC. cbn [lin_of] in HC. unfold P1 in Esr. rewrite Esr in HC.
          destruct (readable_range (p1 P) (v1 A) se ne) eqn:RR; try discriminate HC.
          exact (readable_range_sound SEGS P1 E1 (zpatch P E mem0 mem) PO (v1 A) nu regs mem se ne RR_dead HG1 ltac:(lia) RR).
      + destruct (range_check P A de ne true) as [r lo hi|rr| |m1] eqn:RCd;
          [| |exact (range_check_not_dead A nu regs mem de ne true HG2 ltac:(lia) RCd)|discriminate HC].
        * repeat match type of HC with (match (if ?c then _ else _) with _ => _ end) = _ => destruct c; try discriminate HC end.
        * destruct (range_check_v1_inv P A de ne rr RCd) as (off' & lo' & hi' & -> & Esr & _). cbn [lift_cresA] in HC.
          unfold c_memcpy, getA in HC. rewrite En, Ene, Ede, Ese in HC. cbn [lin_of] in HC. unfold P1 in Esr. rewrite Esr in HC.
          destruct (readable_range (p1 P) (v1 A) se ne) eqn:RR; try discriminate HC.
          exact (readable_range_sound SEGS P1 E1 (zpatch P E mem0 mem) PO (v1 A) nu regs mem se ne RR_dead HG1 ltac:(lia) RR).
  Qed.
End S.
