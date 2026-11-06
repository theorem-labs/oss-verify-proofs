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
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLin VLinalg VWord2 VState VLogic VGamma VAbs VAbsSound VAbsSound2 VAbsSound3 VStep VStepMem VStepSound VStepMemSound VStepMemSound2 VCert VContract VContractSound VContractSound2 VContractSound3 VContractSound4 VState2 VStepMem2 VGamma2 VStepMem2SoundA VStepMem2SoundB VStepMem2SoundC VStepMem2SoundD VContractA VCert2 VContract2 VContract2Iface VContractASound1 VContractASound2 VContractASound4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Stdlib.micromega.Lia.lia ::= first [ flia2 | Zify.zify; xlia zchecker ].  (* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
Unset Lia Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition wend (s K : Z) : Z := (s + K) - (s + K) mod 8 + 8.
Lemma wend_bounds s K : 0 <= s -> 0 <= K -> s + K + 1 <= wend s K <= s + K + 8.
Proof. intros. unfold wend. pose proof (Z.div_mod (s + K) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (s + K) 8 ltac:(lia)). lia. Qed.
Lemma wend_le_aligned s K M : 0 <= s -> 0 <= K -> s + K < M -> M mod 8 = 0 -> wend s K <= M.
Proof.
  intros Hs HK HM H8. unfold wend. pose proof (Z.div_mod (s + K) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (s + K) 8 ltac:(lia)) as B1.
  pose proof (Z.div_mod M 8 ltac:(lia)) as D2. rewrite H8, Z.add_0_r in D2.
  assert (LT : (s + K) / 8 < M / 8) by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma word_between_bounds (S x K a : Z) :
  (S + x / 8) / 8 * 8 <= a -> a <= (S + (x + K) / 8) / 8 * 8 ->
  S + x / 8 - 7 <= a /\ a + 8 <= S + (x + K) / 8 + 8.
Proof. intros. pose proof (div8_facts (S + x / 8)). pose proof (div8_facts (S + (x + K) / 8)). lia. Qed.

(* [comment removed for export] *)
Lemma al64_word (fa : Z) : fa mod 64 = 0 -> (SBz + fa / 8) / 8 * 8 = SBz + fa / 8.
Proof.
  intros H. pose proof (Z.div_mod fa 64 ltac:(lia)) as D. rewrite H in D.
  replace fa with ((fa / 64 * 8) * 8) at 1 2 by lia. rewrite Z.div_mul by lia.
  unfold SBz. replace (2147450880 + fa / 64 * 8) with ((268431360 + fa / 64) * 8) by lia. rewrite Z.div_mul by lia. lia.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma band_ok_str (a n : Z) : band_ok a n -> a + n <= LOW_MEM_END \/ HIGH_MEM_BEG <= a /\ a + n <= HIGH_MEM_END - 1.
Proof. unfold band_ok, LOW_MEM_TOP, LOW_MEM_END. lia. Qed.

Lemma fs8_word_between (fs fa sz x K a : Z) :
  fs mod 4096 = 0 -> 0 <= fs -> fa mod 64 = 0 -> fs + 36864 <= fa -> fa + sz <= fs + 36864 + 5 * 2 ^ 20 ->
  fa <= x -> 0 <= K -> x + K < fa + sz ->
  (SBz + x / 8) / 8 * 8 <= a -> a <= (SBz + (x + K) / 8) / 8 * 8 ->
  SBz + fs / 8 + 4608 <= a /\ a + 8 <= SBz + fs / 8 + 4608 + 655360.
Proof.
  intros. pose proof (word_floor_mono SBz fa x ltac:(lia)). pose proof (al64_word fa ltac:(assumption)).
  destruct (arith_fs8_word fs (x + K) ltac:(assumption) ltac:(lia) ltac:(lia)) as [_ W]. unfold SBz in *.
  pose proof (div8_facts fa). pose proof (div8_facts fs). pose proof (Z.div_mod fs 4096 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma kill_nul_None_nul A lo hi :
  vs_nul (kill_nul A lo hi None) = List.filter (fun r : Z * Z => (snd r <? lo) || (hi <? fst r))%bool (vs_nul A).
Proof. unfold kill_nul. destruct (vs_nul A) eqn:EN; cbn; rewrite ?EN; reflexivity. Qed.
Lemma killK_nul_eq K X Y s : vs_nul X = vs_nul Y -> vs_nul (killK K X s) = vs_nul (killK K Y s).
Proof. intros H. unfold killK. rewrite !kill_nul_None_nul. cbn [vs_nul set_slots]. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma arith_shdK (e vf spoff t Kc J : Z) :
  e = 8 * (e / 8) -> 17594333495296 <= e - vf -> e + 16 <= 2 ^ 47 -> - vf <= spoff - Kc -> J + 8 <= Kc -> 0 <= t <= e - 1 ->
  2147450880 + t / 8 + 8 < e + spoff - J.
Proof.
  intros. pose proof (div8_facts t). pose proof (div8_facts (e - 1)).
  assert (t / 8 <= (e - 1) / 8) by (apply Z.div_le_mono; lia). lia.
Qed.
Lemma arith_shdK_low (e vf spoff t Kc J : Z) :
  17594333495296 <= e - vf -> - vf <= spoff - Kc -> J + 8 <= Kc -> 0 <= t <= 2 ^ 47 - 2 ->
  2147450880 + t / 8 + 8 < e + spoff - J.
Proof. intros. pose proof (div8_facts t). lia. Qed.

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
  Hypothesis FSLEN : forall len ssl, vp_fs P = Some (len, ssl) -> FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL < len.
  (* [comment removed for export] *)
  Hypothesis FS_SOME : vp_fs P <> None.
  Hypothesis FRAME40 : vp_frame (p1 P) < 2 ^ 40.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section KJ.
  Variables Kc J : Z.
  Hypothesis HKJ : 0 <= J /\ J + 8 <= Kc.

  (* [comment removed for export] *)
  Definition str_facts (mem : word -> option byte) (usp s K : Z) (buf : list byte) : Prop :=
       rdn SEGS mem (wordZ s) (length buf) = Some buf
    /\ wend s K - s <= Z.of_nat (length buf)
    /\ s + Z.of_nat (length buf) < 2 ^ 64 /\ 0 <= s /\ 0 <= K /\ K + 1 <= 2 ^ 40
    /\ bv_unsigned (nth (Z.to_nat K) buf B0) = 0
    /\ (s + K + 1 <= LOW_MEM_END \/ HIGH_MEM_BEG <= s /\ s + K + 1 <= HIGH_MEM_END - 1)
    /\ (usp <= s \/ s + Z.of_nat (length buf) <= usp - J)
    /\ SBz + (s + K) / 8 + 8 < usp - J
    /\ (forall g, s / 8 <= g < (s + K) / 8 -> mem (wordZ (SBz + g)) = Some (Z_to_bv 8 0))
    /\ (exists b1 : byte, mem (wordZ (SBz + (s + K) / 8)) = Some b1 /\ (bv_unsigned b1 = 0 \/ (s + K) mod 8 < bv_unsigned b1 < 8))
    /\ (forall a, (SBz + s / 8) / 8 * 8 <= a -> a <= (SBz + (s + K) / 8) / 8 * 8 -> a mod 8 = 0 ->
          exists w : word, rdn SEGS mem (wordZ a) 8 = Some (word_to_le_bytes 8 w)).


  (* [comment removed for export] *)
  #[using="PO2 FSLEN FS_SOME"] Lemma env_facts A nu regs mem :
    gamma2P A nu regs mem ->
    exists flen fssl, vp_fs P = Some (flen, fssl)
      /\ ((0 <= e_fs E /\ off_band (e_fs E) flen) /\ e_fs E + flen <= HIGH_MEM_END) /\ e_fs E mod 4096 = 0 /\ FS_FRAMES + 5 * 2 ^ 20 < flen
      /\ (e_fs E + flen + 4096 <= e_sp0 E1 - vp_frame P1 \/ e_sp0 E1 + 4096 <= e_fs E)
      /\ HIGH_MEM_BEG <= e_sp0 E1 - vp_frame P1 /\ e_sp0 E1 + 16 <= HIGH_MEM_END
      /\ 0 <= vp_frame P1 /\ e_sp0 E1 mod 16 = 0 /\ e_sp0 E1 = 8 * (e_sp0 E1 / 8) /\ vp_splo P1 <= e_sp0 E1.
  Proof.
    intros HG2. pose proof HG2 as (HG1 & HE & _). pose proof HE as (HEV1 & _ & HFS & _).
    pose proof HEV1 as (E1a & E2 & E3 & _). pose proof (PO1 _ _ PO2) as (P0 & _).
    unfold env_fs in HFS. destruct (vp_fs P) as [[flen fssl]|] eqn:EFS; [|exfalso; exact (FS_SOME eq_refl)].
    destruct HFS as (_ & FS1 & FS2 & FS3 & FS4 & _ & _ & APsf & _ & _ & HMsp & _ & _ & SPHI & _).
    pose proof (FSLEN _ _ eq_refl) as FS5. unfold FS_NCLASSES, FS_SSL in FS5.
    assert (SP0al : e_sp0 E1 = 8 * (e_sp0 E1 / 8)).
    { pose proof (Z.div_mod (e_sp0 E1) 8 ltac:(lia)) as X. replace (e_sp0 E1 mod 8) with 0 in X; [lia|].
      unfold E1. rewrite <- (Z.mod_mod_divide (e_sp0 (ev1 E)) 16 8) by (exists 2; reflexivity). rewrite E1a. reflexivity. }
    exists flen, fssl. unfold P1, E1 in *. destruct FS1 as [FS1a FS1b]. repeat split; auto; try lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="PO2 SHOFF ROM_HI FSLEN FS_SOME HKJ"] Lemma img_str_facts A nu regs mem spoff a k :
    gamma2P A nu regs mem -> img_str_ok P a k = true ->
    (forall j, 0 <= j < k -> exists bb, rdn SEGS mem (wordZ (a + j)) 1 = Some [bb] /\ bv_unsigned bb <> 0) ->
    (exists bb, rdn SEGS mem (wordZ (a + k)) 1 = Some [bb] /\ bv_unsigned bb = 0) ->
    in_ranges (vp_segs P1) a (k + 8) = true ->
    - vp_frame P1 <= spoff - Kc ->
    let usp := e_sp0 E1 + spoff in
    exists buf, length buf = Z.to_nat (k + 8) /\ str_facts mem usp a k buf
      /\ (forall j, (j < Z.to_nat k)%nat -> bv_unsigned (nth j buf B0) <> 0).
  Proof.
    intros HG2 HOK NZ ZK Hsg K1 usp.
    pose proof HG2 as (HG1 & HE & HM & _). pose proof (PO1 _ _ PO2) as PO. pose proof PO as (P0 & Psphi & PS & PF & PW & PR & PP & PB).
    destruct (env_facts A nu regs mem HG2) as (flen & fssl & EFS & [FS1 FS2] & FS3 & FS5 & APsf & HMsp & SPHI & Pfr & E1a & SP0al & SPLO).
    unfold img_str_ok, img_addressable in HOK.
    apply andb_prop in HOK as [HOK HW]. apply andb_prop in HOK as [HOK HG]. apply andb_prop in HOK as [HOK H3].
    apply andb_prop in HOK as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3.
    unfold LOW_MEM_END in H3. rewrite SHOFF in HW.
    destruct (in_ranges_sound _ _ _ Hsg) as [slo [shi (Hsin & Q1 & Q2)]]. destruct (PS _ _ Hsin) as (S0 & S1 & SB).
    destruct (rdn_bytes_vals SEGS mem a (Z.to_nat (k + 8)) (fun j b => (j < k -> bv_unsigned b <> 0) /\ (j = k -> bv_unsigned b = 0))
                ltac:(lia) ltac:(lia)) as [buf (Hbuf & Lbuf & Qbuf)].
    { intros j Hj. destruct (Z_lt_le_dec j k) as [Hjk|Hjk].
      - destruct (NZ j ltac:(lia)) as [bb [Rb Ub]]. exists bb. split; [exact Rb|]. split; [auto|intros; lia].
      - destruct (Z.eq_dec j k) as [->|Hne].
        + destruct ZK as [bb [Rb Ub]]. exists bb. split; [exact Rb|]. split; [intros; lia|auto].
        + destruct (rdn1_any SEGS mem (wordZ (a + j)) (SB (a + j) ltac:(lia))) as [bb Rb]. exists bb. split; [exact Rb|]. split; intros; lia. }
    exists buf. split; [exact Lbuf|]. split.
    2:{ intros j Hj. apply (proj1 (Qbuf j ltac:(lia))). lia. }
    (* [comment removed for export] *)
    assert (GR : forall g, a / 8 <= g <= (a + k) / 8 ->
      exists kb : byte, mem (wordZ (SBz + g)) = Some kb /\ (bv_unsigned kb = 0 \/ Z.min (a + k + 1) (8 * g + 8) - 8 * g <= bv_unsigned kb < 8)).
    { intros g Hg. destruct (range_granules_okf_sound (img_sh_byte P) a (a + k + 1) g HG ltac:(lia) ltac:(replace (a + k + 1 - 1) with (a + k) by lia; exact Hg)) as (b & Hb & Bb).
      destruct (img_sh_byte_sound SEGS P E mem0 A nu regs mem g b HG2 Hb) as (kb & Rk & Vk & _). rewrite SHOFF in Rk.
      exists kb. split; [|rewrite Vk; exact Bb]. apply (rdn1_mem SEGS ROM_HI); [|exact Rk]. unfold SBz. pose proof (div8_facts a). pose proof (div8_facts (a + k)). (ltac2:(LK.k [@H1; @H2; @H3; @FS1; @SP0al; @Q1; @S0; @Lbuf; @Hg; @H; @H0]); lia). }
    destruct (shadow_access mem 0 a (a + k + 1) a (k + 1) ltac:(intros g Hg; rewrite Z.add_0_r; apply GR; replace (a + k + 1 - 1) with (a + k) in Hg by lia; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [ZG LG].
    cbv zeta in ZG, LG. rewrite !Z.add_0_l in ZG, LG. replace (a + (k + 1) - 1) with (a + k) in ZG, LG by lia.
    unfold str_facts. rewrite Lbuf, !Z2Nat.id by lia.
    split; [exact Hbuf|]. split; [pose proof (wend_bounds a k); lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [exact (proj2 (Qbuf (Z.to_nat k) ltac:(lia)) ltac:(lia))|].
    split; [left; unfold LOW_MEM_END; lia|].
    split; [right; unfold usp, P1, E1 in *; lia|].
    split; [unfold usp, SBz, HIGH_MEM_BEG in *; pose proof (div8_facts (a + k)); unfold P1, E1 in *; lia|].
    split; [exact ZG|]. split; [exact LG|].
    intros w Hw1 Hw2 Hw8. pose proof (div8_facts a). pose proof (div8_facts (a + k)).
    pose proof (div8_facts (SBz + a / 8)). pose proof (div8_facts (SBz + (a + k) / 8)).
    apply (word_readable SEGS P E mem0 A nu regs mem _ HG2); [|unfold SBz in *; (ltac2:(LK.k [@H1; @H2; @FS1; @Lbuf; @Hw1; @H; @H0; @H4; @H3; @Hw2; @H5]); lia)|unfold SBz in *; (ltac2:(LK.k [@H1; @H2; @FS1; @Lbuf; @Hw1; @H; @H0; @H4; @H3; @Hw2; @H5]); lia)].
    intros i Hi. apply (kruns_cover_sound SEGS P E mem0 A nu regs mem _ _ _ HG2 HW). replace (a + k + 1 - 1) with (a + k) by lia. (ltac2:(LK.k [@H1; @H2; @FS1; @SP0al; @Lbuf; @Hw1; @Hw2; @Hi]); lia).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="PO2 SHOFF ROM_HI FSLEN FS_SOME FRAME40 HKJ"] Lemma stack_str_facts A nu regs mem spoff plo H ov z bz :
    gamma2P A nu regs mem ->
    stack_addressable A plo (H + 1) = true -> stack_shadow_words_ok P plo (H + 1) = true ->
    - vp_frame P1 <= plo -> plo <= ov -> ov <= z -> z <= H -> H + 8 <= 0 ->
    rdn SEGS mem (wordZ (e_sp0 E1 + z)) 1 = Some [bz] -> bv_unsigned bz = 0 ->
    - vp_frame P1 <= spoff - Kc -> spoff <= plo ->
    let usp := e_sp0 E1 + spoff in let p := e_sp0 E1 + ov in let K := z - ov in
    exists buf, length buf = Z.to_nat (K + 8) /\ str_facts mem usp p K buf
      /\ HIGH_MEM_BEG <= p /\ p + K + 1 <= HIGH_MEM_END - 1.
  Proof.
    intros HG2 Hsa Hsw Hplo H1 H2 H3 H8 Rz Uz K1 ASP usp p K.
    pose proof HG2 as (HG1 & HE & HM & HF2 & HDD & RGN & LIVE & BEL2 & GL2 & FI2 & MOK).
    pose proof (PO1 _ _ PO2) as PO. pose proof PO as (P0 & Psphi & PS & PF & PW & PR & PP & PB).
    pose proof (proj1 (proj2 HG1)) as (MF & MD & MP & MFM).
    destruct (env_facts A nu regs mem HG2) as (flen & fssl & EFS & [FS1 FS2] & FS3 & FS5 & APsf & HMsp & SPHI & Pfr & E1a & SP0al & SPLO).
    unfold HIGH_MEM_BEG, HIGH_MEM_END in *.
    (* [comment removed for export] *)
    destruct (rdn_bytes_vals SEGS mem p (Z.to_nat (K + 8)) (fun j b => j = K -> b = bz) ltac:(unfold p, P1, E1 in *; lia) ltac:(unfold p, K, P1, E1 in *; lia)) as [buf (Hbuf & Lbuf & Qbuf)].
    { intros j Hj. destruct (Z.eq_dec j K) as [->|Hne].
      - exists bz. unfold p, K. replace (e_sp0 E1 + ov + (z - ov)) with (e_sp0 E1 + z) by lia. split; [exact Rz|auto].
      - destruct (MF (p + j) ltac:(unfold p, P1, E1 in *; lia)) as [_ [bb Rb]]. exists bb. split; [exact Rb|intros; lia]. }
    exists buf. split; [exact Lbuf|].
    (* [comment removed for export] *)
    unfold stack_addressable in Hsa.
    destruct (rgn_shadow_of (vs_rgn A) SP0) as [sh|] eqn:SH; [|discriminate].
    destruct (rgn_shadow_of_in _ _ _ SH) as [Hsh Ksh].
    destruct (pm_get SP0 (scong (vs_store (v1 A)))) as [[cm cr]|]; [|discriminate].
    apply andb_prop in Hsa as [_ GRAN].
    pose proof (RGN sh Hsh) as (_ & _ & _ & _ & _ & _ & _ & KIND). unfold kind_ok in KIND. rewrite Ksh in KIND.
    destruct KIND as (FSnz & DISP & KSP & _). destruct (KSP eq_refl) as (BSP8 & SHLO & SHHI).
    assert (SP8v : nu SP8 = e_sp0 E1 / 8) by exact (nu_SP8 SEGS P E mem0 A nu regs mem HG2).
    assert (RB : rbase nu sh = SBz + e_sp0 E1 / 8) by (unfold rbase; rewrite DISP, BSP8, SHOFF, SP8v; reflexivity).
    assert (GR : forall g, plo / 8 <= g <= (H + 1 - 1) / 8 ->
      exists k : byte, mem (wordZ (SBz + e_sp0 E1 / 8 + g)) = Some k
                       /\ (bv_unsigned k = 0 \/ Z.min (H + 1) (8 * g + 8) - 8 * g <= bv_unsigned k < 8)).
    { intros g Hg. destruct (range_granules_ok_sound sh plo (H + 1) g GRAN ltac:(lia) Hg) as (b & SB & Hb).
      destruct (sh_byte_mem SEGS P E mem0 A nu regs mem sh g b HG2 Hsh ltac:(unfold is_shadow; rewrite Ksh; reflexivity) SB) as (k & Rk & Vk).
      rewrite RB in Rk. exists k. split; [|rewrite Vk; exact Hb].
      apply (rdn1_mem SEGS ROM_HI); [|exact Rk]. unfold SBz.
      apply (arith_stack_shadow_addr (e_sp0 E1) (vp_frame P1) plo (H + 1) g); unfold P1, E1 in *; lia. }
    destruct (shadow_access mem (e_sp0 E1 / 8) plo (H + 1) ov (K + 1) GR ltac:(lia) ltac:(unfold K; lia) ltac:(unfold K; lia)) as [ZG LG].
    cbv zeta in ZG, LG. rewrite <- SP0al in ZG, LG. fold p in ZG, LG. replace (p + (K + 1) - 1) with (p + K) in ZG, LG by lia.
    assert (NUE8 : nuE E SP8 = e_sp0 E1 / 8).
    { unfold nuE, fix_val2. replace (fix_val (ev1 E) SP8) with (@None Z) by reflexivity. reflexivity. }
    assert (DIVp : p / 8 = e_sp0 E1 / 8 + ov / 8) by (unfold p; rewrite SP0al at 1; rewrite Z.mul_comm, Z.div_add_l by lia; reflexivity).
    assert (DIVpk : (p + K) / 8 = e_sp0 E1 / 8 + z / 8).
    { unfold p, K. replace (e_sp0 E1 + ov + (z - ov)) with (e_sp0 E1 + z) by lia. rewrite SP0al at 1. rewrite Z.mul_comm, Z.div_add_l by lia. reflexivity. }
    pose proof (Z.div_le_mono plo ov 8 ltac:(lia) H1) as Dpo. pose proof (Z.div_le_mono z H 8 ltac:(lia) H3) as Dzh.
    pose proof (wend_bounds p K ltac:(unfold p; lia) ltac:(unfold K; lia)) as WB.
    unfold str_facts. rewrite Lbuf, !Z2Nat.id by (unfold K; lia).
    split.
    2:{ unfold HIGH_MEM_BEG, HIGH_MEM_END, p, K, P1, E1 in *. lia. }
    split; [exact Hbuf|]. split; [lia|]. split; [unfold p, K, P1, E1 in *; lia|]. split; [unfold p, P1, E1 in *; lia|]. split; [unfold K; lia|].
    split; [unfold K, P1 in *; lia|].
    split; [rewrite (Qbuf (Z.to_nat K) ltac:(unfold K; lia) ltac:(unfold K; lia)); exact Uz|].
    split; [right; unfold HIGH_MEM_BEG, HIGH_MEM_END, p, K, P1, E1 in *; lia|].
    split; [left; unfold usp, p; lia|].
    split; [unfold usp, SBz; apply (arith_shdK (e_sp0 E1) (vp_frame P1) spoff (p + K) Kc J); unfold p, K, P1, E1 in *; (ltac2:(LK.k [@HKJ; @Hplo; @H1; @H2; @K1; @ASP; @FS1; @HMsp; @Pfr; @SP0al; @Lbuf; @BSP8; @DIVpk; @SPHI; @H3; @H8]); lia)|].
    split; [exact ZG|]. split; [exact LG|].
    intros a Ha1 Ha2 Ha8. destruct (word_between_bounds SBz p K a Ha1 Ha2) as [W1 W2].
    pose proof (div8_facts plo). pose proof (div8_facts H).
    apply (word_readable SEGS P E mem0 A nu regs mem _ HG2); [| unfold SBz, P1, E1 in *; (ltac2:(LK.k [@HKJ; @Hplo; @H1; @H2; @K1; @ASP; @FS1; @HMsp; @Pfr; @SP0al; @Lbuf; @BSP8; @DIVp; @Dpo; @W1; @H0]); lia) | ].
    - intros i Hi. apply (zone_has_sound SEGS P E mem0 A nu regs mem SP8 _ _ _ HG2 Hsw). rewrite SHOFF, NUE8.
      replace (H + 1 - 1) with H by lia. unfold SBz in *. (ltac2:(LK.k [@HKJ; @H1; @H2; @H3; @H8; @K1; @ASP; @P0; @FS1; @HMsp; @SP0al; @Lbuf; @BSP8; @DIVp; @DIVpk; @Dpo; @Dzh; @W1; @W2; @H0; @H4; @Hi]); lia).
    - unfold SBz in *. unfold p, K, E1, P1 in *. (ltac2:(LK.k [@FRAME40; @HKJ; @Hplo; @H1; @H2; @H8; @K1; @ASP; @FS1; @SPHI; @Pfr; @SP0al; @Lbuf; @BSP8; @DIVpk; @Dzh; @W2; @H4]); lia).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="PO2 SHOFF ROM_HI FSLEN FS_SOME HKJ"] Lemma rgn_str_facts A nu regs mem spoff B r plo H ov z bz :
    gamma2P A nu regs mem -> rgn_get (vs_rgn A) B = Some r ->
    match vr_kind r with RK_fake _ _ | RK_arg => True | _ => False end ->
    vr_lo r <= plo -> H + 1 <= vr_hi r ->
    rgn_addressable A r plo (H + 1) = true -> frames_shadow_zone_ok P = true -> frames_zone_ok P = true ->
    plo <= ov -> ov <= z -> z <= H ->
    rdn SEGS mem (wordZ (rbase nu r + z)) 1 = Some [bz] -> bv_unsigned bz = 0 ->
    - vp_frame P1 <= spoff - Kc -> spoff <= 0 ->
    let usp := e_sp0 E1 + spoff in let x := rbase nu r + ov in let K := z - ov in
    exists buf, str_facts mem usp x K buf /\ band_ok x (K + 1).   (* [comment removed for export] *)
  Proof.
    intros HG2 HGr HK RLO RHI HRA HFZ HFZB H1 H2 H3 Rz Uz K1 K2 usp x K.
    pose proof HG2 as (HG1 & HE & HM & HF2 & HDD & RGN & LIVE & BEL2 & GL2 & FI2 & MOK).
    pose proof (PO1 _ _ PO2) as PO. pose proof PO as (P0 & Psphi & PS & PF & PW & PR & PP & PB).
    destruct (env_facts A nu regs mem HG2) as (flen & fssl & EFS & [FS1 FS2] & FS3 & FS5 & APsf & HMsp & SPHI & Pfr & E1a & SP0al & SPLO).
    destruct (rgn_range_facts SEGS P E mem0 SHOFF ROM_HI FSLEN A nu regs mem B r plo (H + 1) ov (K + 1) HG2 HGr HK RLO RHI HRA HFZ H1
                ltac:(unfold K; lia) ltac:(unfold K; lia))
      as (ACC & (fa & cid & Hcid & FA1 & FA2 & FA3 & FA4 & FK) & FSnz & DRNG & RD).
    cbv zeta in ACC. fold x in ACC. destruct (ACC ltac:(unfold K; lia)) as (ZG & LG & _ & _).
    replace (x + (K + 1) - 1) with (x + K) in ZG, LG by lia.
    unfold HIGH_MEM_BEG, HIGH_MEM_END, FS_FRAMES in *. clear ACC RD.
    pose proof (fake_size_bounds cid Hcid) as SZB. pose proof (fake_size_mod64 cid ltac:(lia)) as SZM.
    assert (FAM : fa mod 64 = 0).
    { destruct (vr_kind r); try contradiction.
      - destruct FK as (_ & _ & pos & _ & -> & _). apply frame_addr_mod64; [exact FS3|lia].
      - destruct FK as (pos & _ & _ & ->). apply frame_addr_mod64; [exact FS3|lia]. }
    assert (XR : fa <= x /\ x + K < fa + fake_size cid) by (unfold x, K; lia).
    pose proof (wend_bounds x K ltac:(lia) ltac:(unfold K; lia)) as WB.
    assert (WE : wend x K <= fa + fake_size cid).
    { apply wend_le_aligned; try (ltac2:(LK.k [@HKJ; @K1; @K2; @FS1; @HMsp; @FA1; @XR; @H2]); lia). pose proof (Z.div_mod fa 64 ltac:(lia)). pose proof (Z.div_mod (fake_size cid) 64 ltac:(lia)).
      rewrite FAM in *. rewrite SZM in *.
      replace (fa + fake_size cid) with (8 * (8 * (fa / 64) + 8 * (fake_size cid / 64))) by lia. rewrite Z.mul_comm. apply Z_mod_mult. }
    (* [comment removed for export] *)
    assert (NUEB : nuE E FSB = e_fs E).
    { unfold nuE, fix_val2. replace (fix_val (ev1 E) FSB) with (@None Z) by reflexivity. reflexivity. }
    destruct (rdn_bytes SEGS mem x (Z.to_nat (wend x K - x)) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (buf & Hbuf & Lbuf).
    { intros i Hi. rewrite Z2Nat.id in Hi by lia.
      apply (zone_hasd_sound SEGS P E mem0 A nu regs mem FSB 0 _ _ _ HG2 HFZB). rewrite NUEB. unfold FS_FRAMES_SZ, FS_FRAMES in *. lia. }
    exists buf.
    assert (LB : Z.of_nat (length buf) = wend x K - x) by (rewrite Lbuf, Z2Nat.id by lia; reflexivity).
    rewrite <- Lbuf in Hbuf. unfold str_facts. rewrite LB.
    assert (XBAND : band_ok x (K + 1)).
    { apply (band_ok_sub (e_fs E) flen _ _ (proj2 FS1)); [unfold HIGH_MEM_END in *; lia|unfold x, K in *; lia|unfold x, K in *; lia]. }
    split.
    2:{ exact XBAND. }
    split; [exact Hbuf|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold K; lia|]. split; [unfold K in *; lia|].
    split.
    { (* [comment removed for export] *)
      pose proof (rdn_nth SEGS mem (length buf) (wordZ x) buf (Z.to_nat K) Hbuf ltac:(unfold K in *; lia)) as X.
      rewrite wordZ_add_nat, Z2Nat.id in X by (unfold K; lia).
      replace (x + K) with (rbase nu r + z) in X by (unfold x, K; lia). rewrite Rz in X. injection X as <-. exact Uz. }
    split; [replace (x + K + 1) with (x + (K + 1)) by lia; exact (band_ok_str x (K + 1) XBAND)|].
    split.
    { unfold usp. unfold FS_FRAMES in *. destruct APsf as [X|X]; unfold P1, E1 in *; [right|left]; lia. }
    split; [unfold usp, SBz; apply (arith_shdK_low (e_sp0 E1) (vp_frame P1) spoff (x + K) Kc J); unfold x, K, P1, E1 in *; lia|].
    split; [exact ZG|]. split; [exact LG|].
    (* [comment removed for export] *)
    assert (NUE8 : nuE E FS8 = e_fs E / 8).
    { unfold nuE, fix_val2. replace (fix_val (ev1 E) FS8) with (@None Z) by reflexivity. reflexivity. }
    intros a Ha1 Ha2 Ha8.
    destruct (fs8_word_between (e_fs E) fa (fake_size cid) x K a FS3 ltac:(clear -FS1; lia) FAM FA1 FA2 (proj1 XR) ltac:(clear -H2; unfold K; lia) (proj2 XR) Ha1 Ha2) as [B1 B2].
    clear - HG2 HFZ B1 B2 FS1 FS2 FS5 SHOFF NUE8.
    apply (word_readable SEGS P E mem0 A nu regs mem _ HG2); [| unfold SBz in *; lia | pose proof (div8_facts (e_fs E)); unfold SBz in *; lia].
    intros i Hi. apply (zone_has_sound SEGS P E mem0 A nu regs mem FS8 _ _ _ HG2 HFZ). rewrite SHOFF, NUE8.
    unfold FS_FRAMES_G, FS_FRAMES_GLEN. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="rom PO2 FSLEN FS_SOME HKJ"] Lemma post_val (c : contract2) A spoff nu nu' regs regs' mem m' (B : vstate) (e : lin) (i : Z) :
    contract2_K c = Kc ->
    gamma2P A nu regs mem -> vs_memo A = [] ->
    - vp_frame P1 <= spoff - Kc -> spoff <= 0 ->
    (exists wr, In wr (vp_wstack P1) /\ fst wr <= spoff - Kc /\ spoff <= snd wr) ->
    let usp := e_sp0 E1 + spoff in
    aext (v1 A) B nu nu' -> lgamma B nu' -> eval nu' e = i -> lin_below e (vs_next B) = true ->
    bv_unsigned (getr regs' 10%bv) = zwrap 64 i ->
    (forall r : reg, bv_unsigned r <> 0 -> ~ In (bv_unsigned r) CALLER_SAVED -> getr regs' r = getr regs r) ->
    (forall x : word, bv_unsigned x < usp - J \/ usp <= bv_unsigned x -> m' x = mem x) ->
    (forall x, mem x <> None -> m' x <> None) ->
    let A2 := contract_frame2 c (with_v1 A B) spoff (Some e) in
       gamma2P A2 nu' regs' m'
    /\ ext (vs2_next A) nu nu' /\ (vs2_next A <= vs2_next A2)%positive
    /\ frame_mod mem m' (unit_regions2 P E)
    /\ flags_step P E A A2 nu nu' mem m'.
  Proof.
    intros HcK HG2 MEMO K1 K2 KW usp XB LB Ve Be R10 QK QM QG A2.
    pose proof HG2 as (HG1 & HE & HM & HF2 & HDD & RGN & LIVE & BEL2 & GL2 & FI2 & MOK).
    pose proof (PO1 _ _ PO2) as PO.
    pose proof HE as (HEV1 & HD2 & HFS & HZO & HKC).
    destruct (env_facts A nu regs mem HG2) as (flen & fssl & EFS & [FS1 FS2] & FS3 & FS5 & APsf & HMsp & SPHI & Pfr & E1a & SP0al & SPLO).
    unfold HIGH_MEM_BEG, HIGH_MEM_END in *.
    destruct XB as (XE & XLE & XS). pose proof XS as (SR & SS & SG & SN & _).
    (* [comment removed for export] *)
    pose proof (gamma_junk SEGS P1 E1 (zpatch P E mem0 mem) PO (v1 A) nu regs mem m' spoff Kc J HG1 QM QG
                  ltac:(lia) K1 K2) as Gk.
    (* [comment removed for export] *)
    set (Bst := contract_frame C_memset (killK Kc B spoff) spoff (Some e)).
    assert (EFR : frame_rule Kc B spoff (Some e) = Bst) by (apply frame_rule_killK; lia).
    destruct (killK_shape Kc (v1 A) spoff) as (KS1 & KS2 & KS3 & KS4 & KS5 & KS6 & KS7 & KS8 & KS9).
    destruct (killK_shape Kc B spoff) as (KT1 & KT2 & KT3 & KT4 & KT5 & KT6 & KT7 & KT8 & KT9).
    destruct (contract_frame_shape C_memset (killK Kc B spoff) spoff (Some e)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & FR).
    assert (HLB : lgamma Bst nu').
    { apply lgamma_contract_frame; [apply lgamma_killK; exact LB|]. cbn [vbelow]. rewrite KT4. exact Be. }
    destruct (gamma_call_post SEGS P1 E1 (zpatch P E mem0 mem) rom PO (killK Kc (v1 A) spoff) Bst nu nu' regs regs' m' m' []
                Gk ltac:(rewrite KS4; exact XE) ltac:(unfold Bst; rewrite F5, KT4, KS4; exact XLE) HLB) as [GB _].
    { eapply (gamma_regs_contract_frame SEGS P1 E1 (zpatch P E mem0 mem) C_memset (killK Kc (v1 A) spoff) (killK Kc B spoff) spoff (Some e) nu nu' regs regs');
        [ right; pose proof Gk as (_&_&_&_&_&_&_&KRg&_&_&_&KBl); split; [exact KRg|destruct KBl as (_&_&KRB&_); exact KRB]
        | rewrite KS4; exact XE | rewrite KT8, KS8; exact SR | exact QK |].
      rewrite R10, Ve. reflexivity. }
    { intros off' w' v' Hin. left. unfold Bst in Hin. rewrite F1 in Hin.
      assert (Hin' : In (off', (w', v')) (vs_slots (killK Kc B spoff))) by exact Hin.
      rewrite KT1, SS, <- KS1 in Hin'. split; [exact Hin'|]. intros x _. exact I. }
    { intros g w' v' Hin. unfold Bst in Hin. rewrite F2 in Hin. rewrite KT2, SG, <- KS2 in Hin. split; [exact Hin|]. intros x _. exact I. }
    { intros lo' hi' Hin. left. unfold Bst in Hin. destruct (F3 _ Hin) as [Hin' _].
      rewrite (killK_nul_eq Kc B (v1 A) spoff SN) in Hin'. split; [exact Hin'|]. intros x _. exact I. }
    { apply frame_mod_refl. }
    { intros x Hx. exfalso. apply Hx. exact I. }
    (* [comment removed for export] *)
    assert (FMU : frame_mod mem m' (unit_regions P1 E1)).
    { split; [|exact QG]. intros a Ha.
      assert (NJ : ~ (usp - J <= bv_unsigned a < usp)).
      { intros Hin. refine (proj1 (stack_R_ok SEGS P1 E1 (zpatch P E mem0 mem) PO (spoff - J) (spoff - Kc) spoff J
                                 K1 K2 ltac:(lia) ltac:(lia) KW HEV1 a _) Ha).
        cbn [outside]. unfold in_rng. rewrite u_wordZ by (unfold usp, P1, E1 in *; lia). unfold usp in Hin. intros [X _]. apply X. lia. }
      apply QM. pose proof (bv_unsigned_in_range 64 a). lia. }
    destruct (gamma2_lift SEGS P E mem0 PO2 A Bst nu nu' regs regs' mem m' HG2 GB XE
                ltac:(unfold Bst; rewrite F5, KT4; exact XLE) FMU
                ltac:(unfold globs_ok2, Bst; cbn [v1 with_v1]; rewrite F2, KT2, SG; exact GL2) ltac:(right; exact MEMO))
      as (G3 & FM3 & FST3).
    assert (EST : A2 = with_v1 A Bst).
    { unfold A2, contract_frame2, with_v1. cbn [v1 vs_rgn vs_live vs_divdef vs_memo]. rewrite HcK, <- EFR. reflexivity. }
    rewrite EST. split; [exact G3|]. split; [exact XE|]. split.
    { unfold vs2_next, Bst. cbn [v1 with_v1]. rewrite F5, KT4. exact XLE. }
    split; [exact FM3|exact FST3].
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="Type"] Lemma rodata_cands_sound extra chk l : forall klo khi a,
    rodata_cands (p1 P) extra chk l = Some (klo, khi) -> In a l ->
    exists k, rodata_cstr_len (p1 P) (Some (lconst a)) = Some k /\ in_ranges (vp_segs (p1 P)) a (k + extra) = true
              /\ chk a k = true /\ klo <= k <= khi.
  Proof.
    induction l as [|a0 t IH]; intros klo khi a H Hin; [destruct Hin|]. cbn [rodata_cands] in H.
    destruct (rodata_cstr_len (p1 P) (Some (lconst a0))) as [k0|] eqn:E0; [|discriminate].
    destruct (in_ranges (vp_segs (p1 P)) a0 (k0 + extra)) eqn:R0; cbn [negb orb] in H; [|discriminate].
    destruct (chk a0 k0) eqn:C0; cbn [negb orb] in H; [|discriminate].
    destruct t as [|a1 t'].
    - injection H as <- <-. destruct Hin as [<-|[]]. exists k0. repeat split; auto; lia.
    - destruct (rodata_cands (p1 P) extra chk (a1 :: t')) as [[lo hi]|] eqn:RT; [|discriminate]. injection H as <- <-.
      destruct Hin as [<-|Hin].
      + exists k0. repeat split; auto; lia.
      + destruct (IH lo hi a eq_refl Hin) as (k & E1' & R1 & C1 & B1). exists k. repeat split; auto; lia.
  Qed.

  #[using="Type"] Lemma ptr_candidates_sound A nu pe l : lgamma (v1 A) nu -> ptr_candidates (v1 A) pe = Some l -> In (eval nu pe) l.
  Proof.
    intros HL H. unfold ptr_candidates in H.
    destruct (lin_is_const pe) eqn:Ec.
    - injection H as <-. left. symmetry. apply eval_is_const. exact Ec.
    - destruct (lin_single pe) as [[s0 k]|] eqn:Es; [|discriminate].
      destruct (Z.eqb_spec k 1) as [->|]; cbn [negb] in H; [|discriminate].
      destruct (pm_get s0 (vs_valset (v1 A))) as [vs|] eqn:Ev; [|discriminate].
      destruct (Nat.leb (length vs) 64); [|discriminate]. injection H as <-.
      pose proof HL as (_ & _ & _ & LV & _). specialize (LV s0 vs Ev).
      rewrite (eval_single nu pe s0 1 Es). apply in_map_iff. exists (nu s0). split; [lia|exact LV].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma rgn_nul_bound_sound A nu regs mem r phi H :
    gamma2P A nu regs mem -> In r (vs_rgn A) -> is_shadow r = false ->
    rgn_nul_bound r phi = Some H ->
    exists z b, phi <= z <= H /\ vr_lo r <= z < vr_hi r /\ rdn SEGS mem (wordZ (rbase nu r + z)) 1 = Some [b] /\ bv_unsigned b = 0.
  Proof.
    intros HG2 Hr NSH Hb. pose proof HG2 as (HG1 & HE & HM & HF2 & HDD & RGN & _).
    pose proof (RGN r Hr) as (RB1 & RB2 & RB3 & RDS & CELLS & PERM & NUL & KIND).
    unfold rgn_nul_bound in Hb. destruct (min_opt_spec _ _ Hb) as [Hin _].
    apply in_app_iff in Hin as [Hin|Hin].
    - apply in_map_iff in Hin as [[lo hi] [Ehi Hin]]. cbn in Ehi. subst hi.
      apply filter_In in Hin as [Hin Hle]. cbn in Hle. apply Z.leb_le in Hle.
      destruct (NUL _ _ Hin) as (off & b & Q1 & Q2 & Q3 & Q4). exists off, b. repeat split; auto; lia.
    - destruct (slot_zero_bytes_spec _ _ _ Hin) as [o [sz [v [i' (Hsl & Hc & Hi & Ez & Hphi & Hbyte)]]]].
      destruct (CELLS _ _ _ Hsl) as (R1 & R2 & R3 & CH). unfold rcell_holds in CH. rewrite NSH in CH. cbn [andb cell_holds] in CH.
      destruct CH as [bs [Hbs Hval]].
      pose proof (rdn_length _ _ _ _ _ Hbs) as Hlen.
      pose proof (rdn_nth SEGS mem (Z.to_nat sz) (wordZ (rbase nu r + o)) bs i' Hbs Hi) as Hb'.
      rewrite wordZ_add_nat in Hb'.
      exists H, (nth i' bs B0). split; [lia|]. split; [lia|]. split.
      + rewrite Ez. replace (rbase nu r + (o + Z.of_nat i')) with (rbase nu r + o + Z.of_nat i') by lia. exact Hb'.
      + rewrite (nth_byte_val bs i') by lia. rewrite Hval, (eval_is_const nu v Hc).
        change 255 with (2 ^ 8 - 1) in Hbyte. rewrite !land_lowmask, Z.shiftr_div_pow2 in Hbyte by lia.
        unfold zwrap. change 256 with (2 ^ 8). exact Hbyte.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition rng_facts (mem : word -> option byte) (usp x K : Z) (buf : list byte) : Prop :=
       rdn SEGS mem (wordZ x) (length buf) = Some buf /\ Z.of_nat (length buf) = K + 1
    /\ x + K + 1 < 2 ^ 64 /\ 0 <= x /\ 0 <= K /\ K + 1 <= 2 ^ 40
    /\ (x + K + 1 <= LOW_MEM_END \/ HIGH_MEM_BEG <= x /\ x + K + 1 <= HIGH_MEM_END - 1)
    /\ (usp <= x \/ x + K + 1 <= usp - J)
    /\ SBz + (x + K) / 8 + 8 < usp - J
    /\ (forall g, x / 8 <= g < (x + K) / 8 -> mem (wordZ (SBz + g)) = Some (Z_to_bv 8 0))
    /\ (exists b1 : byte, mem (wordZ (SBz + (x + K) / 8)) = Some b1 /\ (bv_unsigned b1 = 0 \/ (x + K) mod 8 < bv_unsigned b1 < 8))
    /\ (forall a, (SBz + x / 8) / 8 * 8 <= a -> a <= (SBz + (x + K) / 8) / 8 * 8 -> a mod 8 = 0 ->
          exists w : word, rdn SEGS mem (wordZ a) 8 = Some (word_to_le_bytes 8 w)).

  (* [comment removed for export] *)
  #[using="PO2 SHOFF ROM_HI FSLEN FS_SOME HKJ"] Lemma img_rng_facts A nu regs mem spoff a K m :
    gamma2P A nu regs mem -> img_addressable P a (a + m) = true -> K + 1 <= m -> 0 <= K ->
    in_ranges (vp_segs P1) a (K + 1) = true ->
    - vp_frame P1 <= spoff - Kc ->
    let usp := e_sp0 E1 + spoff in
    exists buf, rng_facts mem usp a K buf.
  Proof.
    intros HG2 HOK HKm HK0 Hsg K1 usp.
    pose proof HG2 as (HG1 & HE & HM & _). pose proof (PO1 _ _ PO2) as PO. pose proof PO as (P0 & Psphi & PS & PF & PW & PR & PP & PB).
    destruct (env_facts A nu regs mem HG2) as (flen & fssl & EFS & [FS1 FS2] & FS3 & FS5 & APsf & HMsp & SPHI & Pfr & E1a & SP0al & SPLO).
    unfold img_addressable in HOK.
    apply andb_prop in HOK as [HOK HW]. apply andb_prop in HOK as [HOK HG]. apply andb_prop in HOK as [HOK H3].
    apply andb_prop in HOK as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3.
    unfold LOW_MEM_END in H3. rewrite SHOFF in HW.
    destruct (in_ranges_sound _ _ _ Hsg) as [slo [shi (Hsin & Q1 & Q2)]]. destruct (PS _ _ Hsin) as (S0 & S1 & SB).
    destruct (rdn_bytes SEGS mem a (Z.to_nat (K + 1)) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (buf & Hbuf & Lbuf).
    { intros i Hi. rewrite Z2Nat.id in Hi by lia. apply rdn1_any. apply SB. lia. }
    assert (GR : forall g, a / 8 <= g <= (a + K) / 8 ->
      exists kb : byte, mem (wordZ (SBz + g)) = Some kb /\ (bv_unsigned kb = 0 \/ Z.min (a + K + 1) (8 * g + 8) - 8 * g <= bv_unsigned kb < 8)).
    { intros g Hg. destruct (range_granules_okf_mono (img_sh_byte P) a (a + m) a (a + K + 1) g HG ltac:(lia) ltac:(lia) ltac:(lia) ltac:(replace (a + K + 1 - 1) with (a + K) by lia; exact Hg)) as (b & Hb & Bb).
      destruct (img_sh_byte_sound SEGS P E mem0 A nu regs mem g b HG2 Hb) as (kb & Rk & Vk & _). rewrite SHOFF in Rk.
      exists kb. split; [|rewrite Vk; exact Bb]. apply (rdn1_mem SEGS ROM_HI); [|exact Rk]. unfold SBz. pose proof (div8_facts a). pose proof (div8_facts (a + K)). (ltac2:(LK.k [@H1; @H2; @H3; @HKm; @HK0; @FS1; @SP0al; @Lbuf; @Hg; @H0]); lia). }
    destruct (shadow_access mem 0 a (a + K + 1) a (K + 1) ltac:(intros g Hg; rewrite Z.add_0_r; apply GR; replace (a + K + 1 - 1) with (a + K) in Hg by lia; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [ZG LG].
    cbv zeta in ZG, LG. rewrite !Z.add_0_l in ZG, LG. replace (a + (K + 1) - 1) with (a + K) in ZG, LG by lia.
    exists buf. unfold rng_facts. rewrite Lbuf, !Z2Nat.id by lia. unfold HIGH_MEM_BEG, HIGH_MEM_END in *.
    split; [exact Hbuf|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [left; unfold LOW_MEM_END; lia|].
    split; [right; unfold usp, P1, E1 in *; lia|].
    split; [unfold usp, SBz in *; pose proof (div8_facts (a + K)); unfold P1, E1 in *; lia|].
    split; [exact ZG|]. split; [exact LG|].
    intros w Hw1 Hw2 Hw8. pose proof (div8_facts a). pose proof (div8_facts (a + K)).
    pose proof (div8_facts (SBz + a / 8)). pose proof (div8_facts (SBz + (a + K) / 8)).
    pose proof (word_floor_mono SBz (a + K) (a + m - 1) ltac:(lia)) as WM.
    apply (word_readable SEGS P E mem0 A nu regs mem _ HG2); [|unfold SBz in *; (ltac2:(LK.k [@H1; @HK0; @FS1; @HMsp; @Pfr; @SP0al; @Lbuf; @Hw1; @H; @H0; @H4; @H3; @HKm; @Hw2; @H5]); lia)|unfold SBz in *; (ltac2:(LK.k [@H1; @HK0; @FS1; @HMsp; @Pfr; @SP0al; @Lbuf; @Hw1; @H; @H0; @H4; @H3; @HKm; @Hw2; @H5]); lia)].
    intros i Hi. apply (kruns_cover_sound SEGS P E mem0 A nu regs mem _ _ _ HG2 HW). (ltac2:(LK.k [@H1; @HK0; @FS1; @HMsp; @Pfr; @SP0al; @Lbuf; @Hw1; @Hw2; @WM; @Hi]); lia).
  Qed.

  (* [comment removed for export] *)
  #[using="PO2 SHOFF ROM_HI FSLEN FS_SOME FRAME40 HKJ"] Lemma stack_rng_facts A nu regs mem spoff lo hi ov K :
    gamma2P A nu regs mem ->
    stack_addressable A lo hi = true -> stack_shadow_words_ok P lo hi = true ->
    - vp_frame P1 <= lo -> lo <= ov -> ov + K + 1 <= hi -> hi <= 0 -> 0 <= K ->
    - vp_frame P1 <= spoff - Kc -> spoff <= lo ->
    let usp := e_sp0 E1 + spoff in let x := e_sp0 E1 + ov in
    exists buf, rng_facts mem usp x K buf /\ HIGH_MEM_BEG <= x /\ x + K + 1 <= HIGH_MEM_END - 1.
  Proof.
    intros HG2 Hsa Hsw Hlo H1 H2 H3 HK K1 ASP usp x.
    pose proof HG2 as (HG1 & HE & HM & HF2 & HDD & RGN & LIVE & BEL2 & GL2 & FI2 & MOK).
    pose proof (PO1 _ _ PO2) as PO. pose proof PO as (P0 & Psphi & PS & PF & PW & PR & PP & PB).
    pose proof (proj1 (proj2 HG1)) as (MF & MD & MP & MFM).
    destruct (env_facts A nu regs mem HG2) as (flen & fssl & EFS & [FS1 FS2] & FS3 & FS5 & APsf & HMsp & SPHI & Pfr & E1a & SP0al & SPLO).
    unfold HIGH_MEM_BEG, HIGH_MEM_END in *.
    destruct (rdn_bytes SEGS mem x (Z.to_nat (K + 1)) ltac:(unfold x, P1, E1 in *; lia) ltac:(rewrite Z2Nat.id by lia; unfold x, P1, E1 in *; lia)) as (buf & Hbuf & Lbuf).
    { intros i Hi. rewrite Z2Nat.id in Hi by lia. exact (proj2 (MF (x + i) ltac:(unfold x, P1, E1 in *; lia))). }
    (* [comment removed for export] *)
    unfold stack_addressable in Hsa.
    destruct (rgn_shadow_of (vs_rgn A) SP0) as [sh|] eqn:SH; [|discriminate].
    destruct (rgn_shadow_of_in _ _ _ SH) as [Hsh Ksh].
    destruct (pm_get SP0 (scong (vs_store (v1 A)))) as [[cm cr]|]; [|discriminate].
    apply andb_prop in Hsa as [_ GRAN].
    pose proof (RGN sh Hsh) as (_ & _ & _ & _ & _ & _ & _ & KIND). unfold kind_ok in KIND. rewrite Ksh in KIND.
    destruct KIND as (FSnz & DISP & KSP & _). destruct (KSP eq_refl) as (BSP8 & SHLO & SHHI).
    assert (SP8v : nu SP8 = e_sp0 E1 / 8) by exact (nu_SP8 SEGS P E mem0 A nu regs mem HG2).
    assert (RB : rbase nu sh = SBz + e_sp0 E1 / 8) by (unfold rbase; rewrite DISP, BSP8, SHOFF, SP8v; reflexivity).
    assert (GR : forall g, lo / 8 <= g <= (hi - 1) / 8 ->
      exists k : byte, mem (wordZ (SBz + e_sp0 E1 / 8 + g)) = Some k
                       /\ (bv_unsigned k = 0 \/ Z.min hi (8 * g + 8) - 8 * g <= bv_unsigned k < 8)).
    { intros g Hg. destruct (range_granules_ok_sound sh lo hi g GRAN ltac:(lia) Hg) as (b & SBb & Hb).
      destruct (sh_byte_mem SEGS P E mem0 A nu regs mem sh g b HG2 Hsh ltac:(unfold is_shadow; rewrite Ksh; reflexivity) SBb) as (k & Rk & Vk).
      rewrite RB in Rk. exists k. split; [|rewrite Vk; exact Hb].
      apply (rdn1_mem SEGS ROM_HI); [|exact Rk]. unfold SBz.
      apply (arith_stack_shadow_addr (e_sp0 E1) (vp_frame P1) lo hi g); unfold P1, E1 in *; lia. }
    destruct (shadow_access mem (e_sp0 E1 / 8) lo hi ov (K + 1) GR ltac:(lia) ltac:(lia) ltac:(lia)) as [ZG LG].
    cbv zeta in ZG, LG. rewrite <- SP0al in ZG, LG. fold x in ZG, LG. replace (x + (K + 1) - 1) with (x + K) in ZG, LG by lia.
    assert (NUE8 : nuE E SP8 = e_sp0 E1 / 8).
    { unfold nuE, fix_val2. replace (fix_val (ev1 E) SP8) with (@None Z) by reflexivity. reflexivity. }
    assert (DIVp : x / 8 = e_sp0 E1 / 8 + ov / 8) by (unfold x; rewrite SP0al at 1; rewrite Z.mul_comm, Z.div_add_l by lia; reflexivity).
    assert (DIVpk : (x + K) / 8 = e_sp0 E1 / 8 + (ov + K) / 8).
    { unfold x. rewrite SP0al at 1. replace (8 * (e_sp0 E1 / 8) + ov + K) with (8 * (e_sp0 E1 / 8) + (ov + K)) by lia.
      rewrite Z.mul_comm, Z.div_add_l by lia. reflexivity. }
    pose proof (Z.div_le_mono lo ov 8 ltac:(lia) H1) as Dpo. pose proof (Z.div_le_mono (ov + K) (hi - 1) 8 ltac:(lia) ltac:(lia)) as Dzh.
    exists buf. unfold rng_facts. rewrite Lbuf, !Z2Nat.id by lia.
    split.
    2:{ unfold HIGH_MEM_BEG, HIGH_MEM_END, x, P1, E1 in *. lia. }
    split; [exact Hbuf|]. split; [lia|]. split; [unfold x, P1, E1 in *; lia|]. split; [unfold x, P1, E1 in *; lia|]. split; [lia|].
    split; [unfold P1 in *; lia|].
    split; [right; unfold HIGH_MEM_BEG, HIGH_MEM_END, x, P1, E1 in *; lia|].
    split; [left; unfold usp, x; lia|].
    split; [unfold usp, SBz; apply (arith_shdK (e_sp0 E1) (vp_frame P1) spoff (x + K) Kc J); unfold x, P1, E1 in *; (ltac2:(LK.k [@HKJ; @Hlo; @H1; @HK; @K1; @ASP; @FS1; @HMsp; @Pfr; @SP0al; @Lbuf; @BSP8; @DIVpk; @SPHI; @H2; @H3]); lia)|].
    split; [exact ZG|]. split; [exact LG|].
    intros a Ha1 Ha2 Ha8. destruct (word_between_bounds SBz x K a Ha1 Ha2) as [W1 W2].
    pose proof (div8_facts lo). pose proof (div8_facts (hi - 1)).
    apply (word_readable SEGS P E mem0 A nu regs mem _ HG2); [| unfold SBz, P1, E1 in *; (ltac2:(LK.k [@HKJ; @Hlo; @H1; @HK; @K1; @ASP; @FS1; @HMsp; @Pfr; @SP0al; @Lbuf; @BSP8; @DIVp; @Dpo; @W1; @H]); lia) | ].
    - intros i Hi. apply (zone_has_sound SEGS P E mem0 A nu regs mem SP8 _ _ _ HG2 Hsw). rewrite SHOFF, NUE8. unfold SBz in *. (ltac2:(LK.k [@HKJ; @H1; @H2; @H3; @HK; @K1; @ASP; @P0; @FS1; @HMsp; @SP0al; @Lbuf; @BSP8; @DIVp; @DIVpk; @Dpo; @Dzh; @W1; @W2; @H; @H0; @Hi]); lia).
    - unfold SBz in *. unfold x, E1, P1 in *. (ltac2:(LK.k [@FRAME40; @HKJ; @Hlo; @H1; @H3; @HK; @K1; @ASP; @FS1; @SPHI; @Pfr; @SP0al; @Lbuf; @BSP8; @DIVpk; @Dzh; @W2; @H0]); lia).
  Qed.

  (* [comment removed for export] *)
  #[using="PO2 SHOFF ROM_HI FSLEN FS_SOME HKJ"] Lemma rgn_rng_facts A nu regs mem spoff B r lo hi ov K :
    gamma2P A nu regs mem -> rgn_get (vs_rgn A) B = Some r ->
    match vr_kind r with RK_fake _ _ | RK_arg => True | _ => False end ->
    vr_lo r <= lo -> hi <= vr_hi r ->
    rgn_addressable A r lo hi = true -> frames_shadow_zone_ok P = true ->
    lo <= ov -> ov + K + 1 <= hi -> 0 <= K ->
    - vp_frame P1 <= spoff - Kc -> spoff <= 0 ->
    let usp := e_sp0 E1 + spoff in let x := rbase nu r + ov in
    exists buf, rng_facts mem usp x K buf /\ band_ok x (K + 1).   (* [comment removed for export] *)
  Proof.
    intros HG2 HGr HK RLO RHI HRA HFZ H1 H2 HK0 K1 K2 usp x.
    pose proof HG2 as (HG1 & HE & HM & HF2 & HDD & RGN & LIVE & BEL2 & GL2 & FI2 & MOK).
    pose proof (PO1 _ _ PO2) as PO. pose proof PO as (P0 & Psphi & PS & PF & PW & PR & PP & PB).
    destruct (env_facts A nu regs mem HG2) as (flen & fssl & EFS & [FS1 FS2] & FS3 & FS5 & APsf & HMsp & SPHI & Pfr & E1a & SP0al & SPLO).
    destruct (rgn_range_facts SEGS P E mem0 SHOFF ROM_HI FSLEN A nu regs mem B r lo hi ov (K + 1) HG2 HGr HK RLO RHI HRA HFZ H1
                ltac:(lia) ltac:(lia))
      as (ACC & (fa & cid & Hcid & FA1 & FA2 & FA3 & FA4 & FK) & FSnz & DRNG & RD).
    cbv zeta in ACC. fold x in ACC. destruct (ACC ltac:(lia)) as (ZG & LG & _ & _).
    replace (x + (K + 1) - 1) with (x + K) in ZG, LG by lia.
    unfold HIGH_MEM_BEG, HIGH_MEM_END, FS_FRAMES in *. clear ACC.
    pose proof (fake_size_bounds cid Hcid) as SZB. pose proof (fake_size_mod64 cid ltac:(lia)) as SZM.
    assert (FAM : fa mod 64 = 0).
    { destruct (vr_kind r); try contradiction.
      - destruct FK as (_ & _ & pos & _ & -> & _). apply frame_addr_mod64; [exact FS3|lia].
      - destruct FK as (pos & _ & _ & ->). apply frame_addr_mod64; [exact FS3|lia]. }
    assert (XR : fa <= x /\ x + K < fa + fake_size cid) by (unfold x; lia).
    destruct (rdn_bytes SEGS mem x (Z.to_nat (K + 1)) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (buf & Hbuf & Lbuf).
    { intros i Hi. rewrite Z2Nat.id in Hi by lia. unfold x. replace (rbase nu r + ov + i) with (rbase nu r + (ov + i)) by lia. apply RD. lia. }
    exists buf. unfold rng_facts. rewrite Lbuf, !Z2Nat.id by lia.
    assert (XBAND : band_ok x (K + 1)) by (apply (band_ok_mono _ _ _ _ (proj2 (proj2 DRNG))); unfold x; lia).
    split.
    2:{ exact XBAND. }
    split; [exact Hbuf|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [replace (x + K + 1) with (x + (K + 1)) by lia; exact (band_ok_str x (K + 1) XBAND)|].
    split.
    { unfold usp. destruct APsf as [X|X]; unfold P1, E1 in *; [right|left]; lia. }
    split; [unfold usp, SBz; apply (arith_shdK_low (e_sp0 E1) (vp_frame P1) spoff (x + K) Kc J); unfold x, P1, E1 in *; lia|].
    split; [exact ZG|]. split; [exact LG|].
    assert (NUE8 : nuE E FS8 = e_fs E / 8).
    { unfold nuE, fix_val2. replace (fix_val (ev1 E) FS8) with (@None Z) by reflexivity. reflexivity. }
    intros a Ha1 Ha2 Ha8.
    destruct (fs8_word_between (e_fs E) fa (fake_size cid) x K a FS3 ltac:(clear -FS1; lia) FAM FA1 FA2 (proj1 XR) HK0 (proj2 XR) Ha1 Ha2) as [B1 B2].
    clear - HG2 HFZ B1 B2 FS1 FS2 FS5 SHOFF NUE8.
    apply (word_readable SEGS P E mem0 A nu regs mem _ HG2); [| unfold SBz in *; lia | pose proof (div8_facts (e_fs E)); unfold SBz in *; lia].
    intros i Hi. apply (zone_has_sound SEGS P E mem0 A nu regs mem FS8 _ _ _ HG2 HFZ). rewrite SHOFF, NUE8.
    unfold FS_FRAMES_G, FS_FRAMES_GLEN. lia.
  Qed.
  End KJ.
End S.
