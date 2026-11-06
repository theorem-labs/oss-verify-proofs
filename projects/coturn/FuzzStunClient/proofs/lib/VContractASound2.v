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
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VAbs VAbsSound VAbsSound2 VAbsSound3 VStep VStepMem VStepSound VStepMemSound VStepMemSound2 VCert VContract VContractSound VContractSound2 VState2 VStepMem2 VGamma2 VStepMem2SoundA VStepMem2SoundB VStepMem2SoundC VStepMem2SoundD VContractA VCert2 VContract2 VContract2Iface VContractASound1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Stdlib.micromega.Lia.lia ::= first [ flia2 | Zify.zify; xlia zchecker ].  (* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
Unset Lia Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bytes_le_to_Z_cons (b : byte) bs :
  bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256.
Proof.
  cbn [bytes_le_to_Z]. pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
  pose proof (bytes_le_to_Z_nonneg bs) as Hr.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  assert (D : Z.land (bv_unsigned b) (bytes_le_to_Z bs * 256) = 0).
  { apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity. }
  rewrite <- Z.lxor_lor by exact D. symmetry. apply Z.add_nocarry_lxor. exact D.
Qed.

Lemma Z_to_le_bytes_to_Z bs : Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes]. rewrite bytes_le_to_Z_cons.
  pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hr.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace ((bv_unsigned b + bytes_le_to_Z bs * 256) / 256) with (bytes_le_to_Z bs) by lia. exact IH.
Qed.

(* [comment removed for export] *)
Lemma rdn8_word segs mem (a : word) bs v :
  rdn segs mem a 8 = Some bs -> bytes_le_to_Z bs = v -> bs = word_to_le_bytes 8 (Z_to_bv 64 v).
Proof.
  intros HR HV. pose proof (rdn_length _ _ _ _ _ HR) as L.
  pose proof (bytes_le_to_Z_bound bs) as B. rewrite L in B. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in B.
  pose proof (bytes_le_to_Z_nonneg bs) as B0.
  unfold word_to_le_bytes. rewrite u_Z_to_bv64, zwrap_id by lia. rewrite <- HV, <- L. symmetry. apply Z_to_le_bytes_to_Z.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition killK (K : Z) (X : vstate) (spoff : Z) : vstate :=
  kill_nul (set_slots X (cm_kill (vs_slots X) (spoff - K) spoff)) (spoff - K) (spoff - 1) None.

Lemma frame_rule_killK K X spoff v :
  K <> 0 -> frame_rule K X spoff v = contract_frame C_memset (killK K X spoff) spoff v.
Proof.
  intros HK. unfold frame_rule, contract_frame, killK. cbn [contract_K].
  destruct (Z.eqb_spec K 0); [lia|]. reflexivity.
Qed.

Lemma killK_shape K X spoff :
  let Y := killK K X spoff in
  vs_slots Y = cm_kill (vs_slots X) (spoff - K) spoff /\ vs_globs Y = vs_globs X /\ vs_store Y = vs_store X /\
  vs_next Y = vs_next X /\ vs_conddef Y = vs_conddef X /\ vs_moddef Y = vs_moddef X /\ vs_valset Y = vs_valset X /\
  vs_regs Y = vs_regs X /\
  (forall f, In f (vs_nul Y) -> In f (vs_nul X) /\ (snd f < spoff - K \/ spoff - 1 < fst f)).
Proof.
  unfold killK.
  destruct (kill_nul_None_shape (set_slots X (cm_kill (vs_slots X) (spoff - K) spoff)) (spoff - K) (spoff - 1))
    as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9).
  cbn zeta. rewrite S1, S2, S3, S4, S5, S6, S7, S8. cbn. repeat split; try reflexivity.
  - apply (proj1 (S9 _ H)).
  - apply (proj2 (S9 _ H)).
Qed.

Lemma lgamma_killK K X spoff nu : lgamma X nu -> lgamma (killK K X spoff) nu.
Proof.
  intros (LS & LC & LM & LV & (B0 & B1 & B2 & B3 & B4 & B5)).
  destruct (killK_shape K X spoff) as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9).
  set (Y := killK K X spoff) in *.
  split; [rewrite S3; exact LS|]. split; [unfold gamma_conddef; rewrite S5; exact LC|].
  split; [unfold gamma_moddef; rewrite S6; exact LM|]. split; [unfold gamma_valset; rewrite S7; exact LV|].
  split; [rewrite S4; exact B0|]. split; [rewrite S3, S4; exact B1|].
  split; [unfold regs_below; rewrite S8, S4; exact B2|].
  split; [rewrite S1, S4; intros k w e Hin; apply cm_kill_sub in Hin; exact (B3 _ _ _ Hin)|].
  split; [rewrite S2, S4; exact B4|].
  unfold side_below. rewrite S5, S6, S7, S4. exact B5.
Qed.

(* [comment removed for export] *)
Lemma rdn1_grows segs m1 m2 (a : word) :
  (m1 a <> None -> m2 a <> None) ->
  (exists b, rdn segs m1 a 1 = Some [b]) -> exists b, rdn segs m2 a 1 = Some [b].
Proof.
  intros G [b Hb]. cbn [rdn] in Hb |- *.
  destruct (m2 a) as [b2|] eqn:E2; [exists b2; reflexivity|].
  destruct (m1 a) as [b1|] eqn:E1; [exfalso; apply G; congruence|].
  destruct (seg_rom segs a) as [b3|]; [exists b3; reflexivity|discriminate].
Qed.

Section Junk.
  Variable SEGS : list Segment.
  Variable P1 : vparams.
  Variable E1 : venv.
  Variable M : word -> option byte.
  Hypothesis PO1 : params_ok SEGS P1.

  (* [comment removed for export] *)
  #[using="PO1"] Lemma gamma_junk B nu regs m1 m2 spoff K J :
    gamma SEGS P1 E1 M B nu regs m1 ->
    let usp := e_sp0 E1 + spoff in
    (forall x : word, (bv_unsigned x < usp - J \/ usp <= bv_unsigned x) -> m2 x = m1 x) ->
    (forall x, m1 x <> None -> m2 x <> None) ->
    0 <= J <= K -> - vp_frame P1 <= spoff - K -> spoff <= 0 ->
    gamma SEGS P1 E1 M (killK K B spoff) nu regs m2.
  Proof.
    intros HG usp AGREE GROWS HJ HK Hsp.
    pose proof HG as (HE & HM & HF & HS & HC & HMo & HV & HR & HSl & HGl & HN & HB).
    pose proof HE as (E1a & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E11 & E12).
    pose proof PO1 as (P0 & Psphi & PS & PF & PW & PR & PP & PB).
    destruct (killK_shape K B spoff) as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9).
    pose proof (lgamma_killK K B spoff nu (gamma_lgamma _ _ _ _ _ _ _ _ HG)) as (LS & LC & LM & LV & LB).
    set (Y := killK K B spoff) in *.
    assert (RDX : forall a (k : nat), 0 <= a < 2 ^ 64 -> a + Z.of_nat k <= 2 ^ 64 ->
              (a + Z.of_nat k <= usp - J \/ usp <= a) -> rdn SEGS m2 (wordZ a) k = rdn SEGS m1 (wordZ a) k).
    { intros a k Ha Hk Hout. apply rdn_ext; [rewrite u_wordZ by lia; lia|]. intros x Hx. rewrite u_wordZ in Hx by lia.
      apply AGREE. lia. }
    split; [exact HE|]. split.
    { (* [comment removed for export] *) destruct HM as (MF & MD & MP & MFM). split; [|split; [|split]].
      - intros a Ha. destruct (MF a Ha) as [W R]. split.
        + eapply store_ok_mono; [|exact W]. intros x Hx. apply GROWS. exact Hx.
        + eapply rdn1_grows; [apply GROWS|exact R].
      - intros i Hi. eapply rdn1_grows; [apply GROWS|exact (MD i Hi)].
      - intros lo hi a Hin Ha. destruct (PP _ _ Hin) as [Q1 Q2]. unfold usp in AGREE.
        rewrite AGREE by (rewrite u_wordZ by lia; lia). exact (MP lo hi a Hin Ha).
      - destruct MFM as [FO FG]. split.
        + intros a Ha. rewrite <- (FO a Ha). apply AGREE.
          unfold footprint in Ha. cbn [outside] in Ha. destruct Ha as [Ha _]. unfold in_rng in Ha. rewrite u_wordZ in Ha by lia.
          unfold usp. pose proof (bv_unsigned_in_range 64 a). lia.
        + intros x Hx. apply GROWS. apply FG. exact Hx. }
    split; [exact HF|]. split; [exact LS|]. split; [exact LC|]. split; [exact LM|]. split; [exact LV|]. split.
    { unfold gamma_regs. rewrite S8. exact HR. }
    split.
    { intros off w v Hin. rewrite S1 in Hin. pose proof (cm_kill_disjoint _ _ _ _ _ _ Hin) as D. apply cm_kill_sub in Hin.
      destruct (HSl _ _ _ Hin) as [R1 R2]. split; [exact R1|].
      destruct v as [e|]; [|exact I]. cbn [cell_holds] in R2 |- *. rewrite RDX; [exact R2|lia|rewrite Z2Nat.id by lia; lia|].
      rewrite Z2Nat.id by lia. unfold usp. lia. }
    split.
    { intros a w v Hin. rewrite S2 in Hin. destruct (HGl _ _ _ Hin) as [R1 R2]. split; [exact R1|].
      destruct v as [e|]; [|exact I]. cbn [cell_holds] in R2 |- *. rewrite RDX; [exact R2|lia|rewrite Z2Nat.id by lia; lia|].
      rewrite Z2Nat.id by lia. unfold usp. lia. }
    split.
    { intros lo hi Hin. destruct (S9 _ Hin) as [Hin' D]. cbn [fst snd] in D. destruct (HN _ _ Hin') as (off & b & Q1 & Q2 & Q3 & Q4).
      exists off, b. split; [exact Q1|]. split; [exact Q2|]. split; [|exact Q4].
      rewrite RDX; [exact Q3|lia|cbn; lia|]. cbn. unfold usp. lia. }
    exact LB.
  Qed.
End Junk.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma div8_facts a : 8 * (a / 8) <= a < 8 * (a / 8) + 8.
Proof. pose proof (Z.div_mod a 8 ltac:(lia)). pose proof (Z.mod_pos_bound a 8 ltac:(lia)). lia. Qed.

Lemma arith_stack_shadow_addr (e vf lo hi g : Z) :
  17594333495296 <= e - vf -> 0 <= vf -> - vf <= lo -> hi <= 0 -> lo / 8 <= g <= (hi - 1) / 8 -> e < 2 ^ 64 ->
  2147450880 <= 2147450880 + e / 8 + g < 2 ^ 64.
Proof.
  intros. pose proof (div8_facts e). pose proof (div8_facts vf). pose proof (div8_facts lo). pose proof (div8_facts (hi - 1)). lia.
Qed.

Lemma arith_qb (e8 ov n lo hi q : Z) :
  (q = 8 * e8 + ov \/ q = 8 * e8 + ov + n - 1) -> lo <= ov -> ov + n <= hi -> 0 < n ->
  lo / 8 <= q / 8 - e8 <= (hi - 1) / 8.
Proof.
  intros Hq H1 H2 Hn.
  assert (M1 : lo / 8 <= ov / 8) by (apply Z.div_le_mono; lia).
  assert (M2 : (ov + n - 1) / 8 <= (hi - 1) / 8) by (apply Z.div_le_mono; lia).
  assert (M3 : ov / 8 <= (ov + n - 1) / 8) by (apply Z.div_le_mono; lia).
  destruct Hq as [-> | ->].
  - replace (8 * e8 + ov) with (ov + e8 * 8) by lia. rewrite Z.div_add by lia. lia.
  - replace (8 * e8 + ov + n - 1) with ((ov + n - 1) + e8 * 8) by lia. rewrite Z.div_add by lia. lia.
Qed.

Lemma arith_shd (e vf spoff t : Z) :
  e = 8 * (e / 8) -> 17594333495296 <= e - vf -> e + 16 <= 2 ^ 47 -> - vf <= spoff - 2208 -> 0 <= t <= e - 1 ->
  2147450880 + t / 8 + 8 < e + spoff - 2200.
Proof.
  intros. pose proof (div8_facts t). pose proof (div8_facts (e - 1)).
  assert (t / 8 <= (e - 1) / 8) by (apply Z.div_le_mono; lia). lia.
Qed.

Lemma arith_shd_rgn (e vf spoff t : Z) :
  17594333495296 <= e - vf -> - vf <= spoff - 2208 -> 0 <= t <= 2 ^ 47 - 2 ->
  2147450880 + t / 8 + 8 < e + spoff - 2200.
Proof. intros. pose proof (div8_facts t). lia. Qed.

(* [comment removed for export] *)
Lemma arith_fs8_word (fs q : Z) :
  fs mod 4096 = 0 -> 0 <= fs -> fs + 36864 <= q <= fs + 36864 + 5 * 2 ^ 20 - 1 ->
  2147450880 + fs / 8 + 4608 <= (2147450880 + q / 8) / 8 * 8
  /\ (2147450880 + q / 8) / 8 * 8 + 8 <= 2147450880 + fs / 8 + 4608 + 655360.
Proof.
  intros Hm Hfs Hq. pose proof (Z.div_mod fs 4096 ltac:(lia)) as D. rewrite Hm in D.
  pose proof (div8_facts fs). pose proof (div8_facts q). pose proof (div8_facts (2147450880 + q / 8)). lia.
Qed.

Lemma frame_in_area fs cid pos :
  0 <= cid <= 4 -> 0 <= pos < fs_nframes cid ->
  fs + FS_FRAMES <= frame_addr fs cid pos /\ frame_addr fs cid pos + fake_size cid <= fs + FS_FRAMES + 5 * 2 ^ 20.
Proof.
  intros Hc Hp. unfold frame_addr. pose proof (class_span cid ltac:(lia)) as CS. pose proof (fake_size_bounds cid Hc) as FB.
  unfold FS_SSL.
  assert (M1 : 0 <= fake_size cid * pos) by nia.
  assert (M2 : fake_size cid * pos + fake_size cid <= 2 ^ 20) by nia.
  assert (M3 : cid * 2 ^ 20 <= 4 * 2 ^ 20) by nia.
  assert (M4 : 0 <= cid * 2 ^ 20) by nia.
  lia.
Qed.

Lemma zero_cells8_in m o k x :
  In x (zero_cells8 m o k) -> In x m \/ exists i, (i < k)%nat /\ x = (o + 8 * Z.of_nat i, (8, Some (lconst 0))).
Proof.
  revert m o. induction k as [|k IH]; intros m o Hin; cbn [zero_cells8] in Hin; [left; exact Hin|].
  destruct (IH _ _ Hin) as [H|[i [Hi ->]]].
  - apply cm_set_in in H as [->|H]; [right; exists 0%nat; split; [lia|f_equal; lia]|left; exact H].
  - right. exists (S i). split; [lia|]. f_equal. lia.
Qed.

Lemma zero_cells1_in m o k x :
  In x (zero_cells1 m o k) -> In x m \/ exists i, (i < k)%nat /\ x = (o + Z.of_nat i, (1, Some (lconst 0))).
Proof.
  revert m o. induction k as [|k IH]; intros m o Hin; cbn [zero_cells1] in Hin; [left; exact Hin|].
  destruct (IH _ _ Hin) as [H|[i [Hi ->]]].
  - apply cm_set_in in H as [->|H]; [right; exists 0%nat; split; [lia|f_equal; lia]|left; exact H].
  - right. exists (S i). split; [lia|]. f_equal. lia.
Qed.

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

  Definition SBz : Z := 0x7fff8000.
  (* [comment removed for export] *)
  Hypothesis SHOFF : vp_shoff P = SBz.
  Hypothesis ROM_HI : forall a : word, SBz <= bv_unsigned a -> seg_rom SEGS a = None.

  #[using="ROM_HI"] Lemma rdn1_mem mem a k : SBz <= a < 2 ^ 64 -> rdn SEGS mem (wordZ a) 1 = Some [k] -> mem (wordZ a) = Some k.
  Proof.
    intros Ha H. unfold SBz in Ha. cbn [rdn] in H. destruct (mem (wordZ a)) as [b|] eqn:M.
    - injection H as ->. reflexivity.
    - rewrite ROM_HI in H by (unfold SBz; rewrite u_wordZ by lia; lia). discriminate.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma zone_coverd_sound A nu regs mem b d fuel : forall lo hi a,
    gamma2P A nu regs mem -> zone_coverd P b d lo hi fuel = true ->
    d + nuE E b + lo <= a < d + nuE E b + hi ->
    exists k, rdn SEGS mem (wordZ a) 1 = Some [k].
  Proof.
    induction fuel as [|f IH]; intros lo hi a HG2 HZ Ha; cbn [zone_coverd] in HZ;
      (destruct (Z.leb_spec hi lo) as [LE|GT]; [lia|]); [discriminate HZ|].
    pose proof HG2 as (_ & _ & (_ & ZOK & _) & _).
    assert (SCAN : forall l, incl l (vp_fzones P) ->
      (fix scan (l : list fzone) : bool :=
         match l with
         | [] => false
         | z :: t => if zone_ok1d P b d z && Z.leb (lc (fz_lo z)) lo && Z.ltb lo (lc (fz_hi z))
                     then (if zone_coverd P b d (lc (fz_hi z)) hi f then true else scan t)
                     else scan t
         end) l = true -> exists k, rdn SEGS mem (wordZ a) 1 = Some [k]).
    { induction l as [|z t IHl]; intros INCL HS; [discriminate HS|].
      assert (Hz : In z (vp_fzones P)) by (apply INCL; left; reflexivity).
      assert (INCLt : incl t (vp_fzones P)) by (intros x Hx; apply INCL; right; exact Hx).
      cbn iota beta in HS. fold (zone_coverd P b d (lc (fz_hi z)) hi f) in HS.
      destruct (zone_ok1d P b d z && Z.leb (lc (fz_lo z)) lo && Z.ltb lo (lc (fz_hi z)))%bool eqn:C; [|exact (IHl INCLt HS)].
      destruct (zone_coverd P b d (lc (fz_hi z)) hi f) eqn:C7; [|exact (IHl INCLt HS)].
      apply andb_prop in C as [C C6]. apply andb_prop in C as [C C5].
      unfold zone_ok1d in C. apply andb_prop in C as [C C4]. apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2].
      apply Pos.eqb_eq in C1. apply Z.eqb_eq in C2. apply Z.leb_le in C5. apply Z.ltb_lt in C6.
      destruct (Z_lt_le_dec a (d + nuE E b + lc (fz_hi z))) as [LT|GE].
      + destruct (ZOK z a Hz) as [R _]; [|exact R].
        unfold in_zone, zone_lo, zone_hi. rewrite C1, C2, (eval_is_const _ _ C3), (eval_is_const _ _ C4). lia.
      + apply (IH (lc (fz_hi z)) hi a HG2 C7). lia. }
    exact (SCAN (vp_fzones P) (incl_refl _) HZ).
  Qed.
  #[using="Type"] Lemma zone_hasd_sound A nu regs mem b d lo hi a :
    gamma2P A nu regs mem -> zone_hasd P b d lo hi = true ->
    d + nuE E b + lo <= a < d + nuE E b + hi ->
    exists k, rdn SEGS mem (wordZ a) 1 = Some [k].
  Proof. intros HG2 HZ Ha. exact (zone_coverd_sound A nu regs mem b d _ lo hi a HG2 HZ Ha). Qed.
  #[using="Type"] Lemma zone_cover_sound A nu regs mem b fuel : forall glo ghi a,
    gamma2P A nu regs mem -> zone_cover P b glo ghi fuel = true ->
    vp_shoff P + nuE E b + glo <= a < vp_shoff P + nuE E b + ghi ->
    exists k, rdn SEGS mem (wordZ a) 1 = Some [k].
  Proof. intros glo ghi a HG2 HZ Ha. exact (zone_coverd_sound A nu regs mem b (vp_shoff P) fuel glo ghi a HG2 HZ Ha). Qed.
  #[using="Type"] Lemma zone_has_sound A nu regs mem b glo ghi a :
    gamma2P A nu regs mem -> zone_has P b glo ghi = true ->
    vp_shoff P + nuE E b + glo <= a < vp_shoff P + nuE E b + ghi ->
    exists k, rdn SEGS mem (wordZ a) 1 = Some [k].
  Proof. intros HG2 HZ Ha. exact (zone_coverd_sound A nu regs mem b (vp_shoff P) _ glo ghi a HG2 HZ Ha). Qed.

  #[using="Type"] Lemma word_readable A nu regs mem a :
    gamma2P A nu regs mem ->
    (forall i, 0 <= i < 8 -> exists k, rdn SEGS mem (wordZ (a + i)) 1 = Some [k]) -> 0 <= a -> a + 8 <= 2 ^ 64 ->
    exists w : word, rdn SEGS mem (wordZ a) 8 = Some (word_to_le_bytes 8 w).
  Proof.
    intros HG2 HB Ha Ha8.
    destruct (rdn_bytes SEGS mem a 8 Ha ltac:(cbn; lia) ltac:(intros k Hk; apply HB; cbn in Hk; lia)) as (bs & R & L).
    exists (Z_to_bv 64 (bytes_le_to_Z bs)). rewrite R. f_equal. eapply rdn8_word; [exact R|reflexivity].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma granules_okf_sound f : forall k g alo ahi g',
    granules_okf f g k alo ahi = true -> g <= g' < g + Z.of_nat k ->
    exists b, f g' = Some b /\ granule_ok b (Z.min ahi (8 * g' + 8) - 8 * g') = true.
  Proof.
    induction k as [|k IH]; intros g alo ahi g' H Hg; [lia|]. cbn [granules_okf] in H.
    destruct (f g) as [b|] eqn:SB; [|discriminate]. apply andb_prop in H as [H1 H2].
    destruct (Z.eq_dec g' g) as [->|NE]; [exists b; auto|].
    apply (IH (g + 1) alo ahi g' H2). lia.
  Qed.
  #[using="Type"] Lemma range_granules_okf_sound f alo ahi g :
    range_granules_okf f alo ahi = true -> alo < ahi -> alo / 8 <= g <= (ahi - 1) / 8 ->
    exists b, f g = Some b /\ (b = 0 \/ Z.min ahi (8 * g + 8) - 8 * g <= b < 8).
  Proof.
    intros H Hlt Hg. unfold range_granules_okf in H. destruct (Z.leb_spec ahi alo); [lia|].
    destruct (granules_okf_sound f _ _ _ _ g H ltac:(rewrite Z2Nat.id by lia; lia)) as (b & SB & OK).
    exists b. split; [exact SB|]. unfold granule_ok in OK. apply Bool.orb_prop in OK as [OK|OK].
    - left. apply Z.eqb_eq in OK. exact OK.
    - right. apply andb_prop in OK as [O1 O2]. apply Z.leb_le in O1. apply Z.ltb_lt in O2. lia.
  Qed.
  #[using="Type"] Lemma granules_ok_sound sh : forall k g alo ahi g',
    granules_ok sh g k alo ahi = true -> g <= g' < g + Z.of_nat k ->
    exists b, sh_byte sh g' = Some b /\ granule_ok b (Z.min ahi (8 * g' + 8) - 8 * g') = true.
  Proof. exact (granules_okf_sound (sh_byte sh)). Qed.
  #[using="Type"] Lemma range_granules_ok_sound sh alo ahi g :
    range_granules_ok sh alo ahi = true -> alo < ahi -> alo / 8 <= g <= (ahi - 1) / 8 ->
    exists b, sh_byte sh g = Some b /\ (b = 0 \/ Z.min ahi (8 * g + 8) - 8 * g <= b < 8).
  Proof. rewrite range_granules_ok_eq. exact (range_granules_okf_sound (sh_byte sh) alo ahi g). Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma range_granules_okf_mono f alo ahi alo' ahi' g :
    range_granules_okf f alo ahi = true -> alo <= alo' -> alo' < ahi' -> ahi' <= ahi -> alo' / 8 <= g <= (ahi' - 1) / 8 ->
    exists b, f g = Some b /\ (b = 0 \/ Z.min ahi' (8 * g + 8) - 8 * g <= b < 8).
  Proof.
    intros H H1 H2 H3 Hg.
    destruct (range_granules_okf_sound f alo ahi g H ltac:(lia)) as (b & Fb & Hb).
    { split; [apply (Z.le_trans _ (alo' / 8)); [apply Z.div_le_mono; lia|lia]|].
      apply (Z.le_trans _ ((ahi' - 1) / 8)); [lia|apply Z.div_le_mono; lia]. }
    exists b. split; [exact Fb|]. destruct Hb as [Hb|Hb]; [left; exact Hb|right]. lia.
  Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma kruns_cover_sound A nu regs mem lo hi a :
    gamma2P A nu regs mem -> kruns_cover P lo hi = true -> lo <= a < hi ->
    exists k, rdn SEGS mem (wordZ a) 1 = Some [k].
  Proof.
    intros HG2 HC Ha. pose proof HG2 as (_ & _ & (_ & _ & _ & _ & _ & KR) & _).
    unfold kruns_cover in HC. rewrite forallb_forall in HC.
    specialize (HC (Z.to_nat (a - lo)) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in HC by lia.
    replace (lo + (a - lo)) with a in HC by lia.
    destruct (krun_get (vp_kruns P) a) as [b|] eqn:K; [|discriminate].
    destruct (krun_get_in _ _ _ K) as (rlo & rhi & Hin & R). destruct (KR rlo rhi b Hin) as (_ & _ & KB).
    destruct (KB a R) as (k & Rk & _). exists k. exact Rk.
  Qed.
  #[using="Type"] Lemma img_sh_byte_sound A nu regs mem g b :
    gamma2P A nu regs mem -> img_sh_byte P g = Some b ->
    exists k : byte, rdn SEGS mem (wordZ (vp_shoff P + g)) 1 = Some [k] /\ bv_unsigned k = b /\ 0 <= b < 256.
  Proof.
    intros HG2 HB. pose proof HG2 as (_ & _ & (_ & _ & _ & _ & _ & KR) & _).
    unfold img_sh_byte in HB. destruct (krun_get (vp_kruns P) (vp_shoff P + g)) as [b0|] eqn:K; [|discriminate].
    injection HB as <-. destruct (krun_get_in _ _ _ K) as (rlo & rhi & Hin & R). destruct (KR rlo rhi b0 Hin) as (_ & _ & KB).
    destruct (KB _ R) as (k & Rk & Vk). exists k. split; [exact Rk|]. split; [exact Vk|].
    rewrite <- Vk. pose proof (bv_unsigned_in_range 8 k) as X. change (bv_modulus 8) with 256 in X. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma sh_byte_mem A nu regs mem sh g b :
    gamma2P A nu regs mem -> In sh (vs_rgn A) -> is_shadow sh = true -> sh_byte sh g = Some b ->
    exists k : byte, rdn SEGS mem (wordZ (rbase nu sh + g)) 1 = Some [k] /\ bv_unsigned k = b.
  Proof.
    intros HG2 Hsh ISH SB. pose proof HG2 as (_ & _ & _ & _ & _ & RGN & _).
    pose proof (RGN sh Hsh) as (_ & _ & _ & _ & CELLS & _).
    unfold sh_byte in SB. destruct (sh_cover (vr_cells sh) g) as [[k0 [w [e|]]]|] eqn:SC; try discriminate.
    destruct (lin_is_const e) eqn:CE; [|discriminate]. injection SB as <-.
    apply sh_cover_in in SC as [Hin Hk].
    destruct (CELLS _ _ _ Hin) as (_ & _ & _ & RC). unfold rcell_holds in RC. rewrite ISH, CE in RC. cbn [andb] in RC.
    destruct (RC (g - k0) ltac:(lia)) as (k & R & V). exists k. replace (rbase nu sh + g) with (rbase nu sh + k0 + (g - k0)) by lia.
    split; [exact R|]. rewrite V. reflexivity.
  Qed.

  #[using="Type"] Lemma rgn_shadow_of_in l s sh : rgn_shadow_of l s = Some sh -> In sh l /\ vr_kind sh = RK_shadow s.
  Proof.
    induction l as [|r t IH]; cbn [rgn_shadow_of]; [discriminate|].
    destruct (vr_kind r) as [cid fl| |ow|s2|] eqn:K.
    4: { destruct (Pos.eqb_spec s2 s) as [->|NE]; [intros H; injection H as ->; split; [left; reflexivity|exact K]|].
         intros H; destruct (IH H); split; [right|]; assumption. }
    all: intros H; destruct (IH H); split; [right|]; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma shadow_access mem (G0 alo ahi x n : Z) :
    (forall g, alo / 8 <= g <= (ahi - 1) / 8 ->
       exists k : byte, mem (wordZ (SBz + G0 + g)) = Some k /\ (bv_unsigned k = 0 \/ Z.min ahi (8 * g + 8) - 8 * g <= bv_unsigned k < 8)) ->
    alo <= x -> x + n <= ahi -> 0 < n ->
    let d := 8 * G0 + x in
    (forall g, d / 8 <= g < (d + n - 1) / 8 -> mem (wordZ (SBz + g)) = Some (Z_to_bv 8 0))
    /\ (exists b1 : byte, mem (wordZ (SBz + (d + n - 1) / 8)) = Some b1
                         /\ (bv_unsigned b1 = 0 \/ (d + n - 1) mod 8 < bv_unsigned b1 < 8)).
  Proof.
    intros GR H1 H2 Hn d.
    assert (DIV : forall y, (8 * G0 + y) / 8 = G0 + y / 8) by (intros y; rewrite Z.mul_comm, Z.div_add_l by lia; reflexivity).
    pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
    pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)).
    pose proof (Z.div_mod (ahi - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (ahi - 1) 8 ltac:(lia)).
    pose proof (Z.div_mod alo 8 ltac:(lia)). pose proof (Z.mod_pos_bound alo 8 ltac:(lia)).
    assert (M1 : alo / 8 <= x / 8) by (apply Z.div_le_mono; lia).
    assert (M2 : (x + n - 1) / 8 <= (ahi - 1) / 8) by (apply Z.div_le_mono; lia).
    split.
    - intros g Hg. unfold d in Hg. rewrite DIV in Hg. replace (8 * G0 + x + n - 1) with (8 * G0 + (x + n - 1)) in Hg by lia. rewrite DIV in Hg.
      destruct (GR (g - G0) ltac:((ltac2:(LK.k [@H1; @H2; @Hn; @H; @H0; @H3; @H4; @H5; @H6; @H7; @H8; @M1; @Hg]); lia))) as (k & Mk & Vk). replace (SBz + G0 + (g - G0)) with (SBz + g) in Mk by lia.
      rewrite Mk. f_equal. apply bv_eq. change (bv_unsigned (Z_to_bv 8 0)) with 0.
      destruct Vk as [V0|Vp]; [rewrite V0; reflexivity|]. exfalso.
      assert (8 * (g - G0) + 8 <= ahi) by (ltac2:(LK.k [@H2; @H3; @H4; @Hg]); lia). rewrite Z.min_l in Vp by lia. lia.
    - unfold d. replace (8 * G0 + x + n - 1) with (8 * G0 + (x + n - 1)) by lia. rewrite DIV.
      destruct (GR ((x + n - 1) / 8) ltac:((ltac2:(LK.k [@H1; @Hn; @H; @H0; @H3; @H4; @H5; @H6; @H7; @H8; @M2]); lia))) as (k & Mk & Vk). rewrite <- Z.add_assoc in Mk. exists k. split; [exact Mk|].
      destruct Vk as [V0|Vp]; [left; exact V0|right].
      replace (8 * G0 + (x + n - 1)) with ((x + n - 1) + G0 * 8) by lia. rewrite Z.mod_add by lia.
      (ltac2:(LK.k [@H2; @H3; @H4; @H7; @H8; @Vp]); lia).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable tgt : Z.
  (* [comment removed for export] *)
  Variable MCELLS : (word -> option byte) -> Prop.
  Hypothesis MCELLS_OK : forall A nu regs mem, gamma2P A nu regs mem -> MCELLS mem.
  Definition JUNK : Z := 2200.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis FSLEN : forall len ssl, vp_fs P = Some (len, ssl) -> FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL < len.

  Hypothesis RUN : forall mem (d c n usp : Z) regs (ra : word),
    MCELLS mem ->
    0 <= n <= 2 ^ 40 -> 0 <= d -> 0 <= c < 2 ^ 64 -> d + n < 2 ^ 64 ->
    (0 < n -> band_ok d n) ->   (* [comment removed for export] *)
    SBz + 2208 <= usp < 2 ^ 64 ->
    (n = 0 \/ usp <= d \/ d + n <= usp - JUNK) ->
    (0 < n -> SBz + (d + n - 1) / 8 + 8 < usp - JUNK) ->
    (forall g, 0 < n -> d / 8 <= g < (d + n - 1) / 8 -> mem (wordZ (SBz + g)) = Some (Z_to_bv 8 0)) ->
    (0 < n -> exists b1 : byte, mem (wordZ (SBz + (d + n - 1) / 8)) = Some b1
                               /\ (bv_unsigned b1 = 0 \/ (d + n - 1) mod 8 < bv_unsigned b1 < 8)) ->
    (0 < n -> exists w : word, rdn SEGS mem (wordZ ((SBz + d / 8) / 8 * 8)) 8 = Some (word_to_le_bytes 8 w)) ->
    (0 < n -> exists w : word, rdn SEGS mem (wordZ ((SBz + (d + n - 1) / 8) / 8 * 8)) 8 = Some (word_to_le_bytes 8 w)) ->
    (forall j, 0 <= j < n -> store_ok SEGS mem (wordZ (d + j)) 1 = true) ->
    (forall a, usp - JUNK <= a < usp -> store_ok SEGS mem (wordZ a) 1 = true) ->
    ret_ok ra -> getr regs 1%bv = ra -> getr regs 2%bv = wordZ usp ->
    getr regs 10%bv = wordZ d -> getr regs 11%bv = wordZ c -> getr regs 12%bv = wordZ n ->
    exists regs' m',
      msteps SEGS (mkst regs (wordZ tgt) mem rom) (mkst regs' ra m' rom)
      /\ getr regs' 10%bv = wordZ d /\ getr regs' 2%bv = wordZ usp /\ getr regs' 1%bv = ra
      /\ (forall r : reg, bv_unsigned r <> 0 -> ~ In (bv_unsigned r) CALLER_SAVED -> getr regs' r = getr regs r)
      /\ (forall x : word, (bv_unsigned x < usp - JUNK \/ usp <= bv_unsigned x) ->
            m' x = wbytes mem (wordZ d) (repeat (Z_to_bv 8 c) (Z.to_nat n)) x)
      /\ (forall x, mem x <> None -> m' x <> None).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma sp_off_spoff A spoff : get_reg (v1 A) 2 = Some (lsymc SP0 spoff) -> sp_off A = Some spoff.
  Proof. intros H. unfold sp_off, get_reg2. rewrite H. reflexivity. Qed.

  #[using="Type"] Lemma above_sp_sound A spoff lo hi :
    get_reg (v1 A) 2 = Some (lsymc SP0 spoff) -> above_sp A lo hi = true -> hi <= lo \/ spoff <= lo.
  Proof.
    intros H HA. unfold above_sp in HA. rewrite (sp_off_spoff A spoff H) in HA.
    apply Bool.orb_prop in HA as [HA|HA]; apply Z.leb_le in HA; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma range_check_v1_inv A de ne rr :
    range_check P A de ne true = RA_v1 rr ->
    exists off lo hi, rr = RR_stack off lo hi /\ stack_range P1 (v1 A) de ne true = RR_stack off lo hi
      /\ above_sp A lo hi = true /\ stack_addressable A lo hi = true /\ stack_shadow_words_ok P lo hi = true.
  Proof.
    unfold range_check. destruct (base_syms A de) as [|B [|B2 t]]; try discriminate.
    - destruct (stack_range (p1 P) (v1 A) de ne true) as [off lo hi| | | |m] eqn:SR; try discriminate.
      destruct (above_sp A lo hi) eqn:AS; cbn [negb]; [|discriminate].
      destruct (stack_addressable A lo hi) eqn:SA; cbn [negb]; [|discriminate].
      destruct (stack_shadow_words_ok P lo hi) eqn:SW; cbn [negb]; [|discriminate].
      intros H. injection H as <-. exists off, lo, hi. repeat split; auto.
    - destruct (negb (lcoef de B =? 1) || negb ((lcoef de SP0 =? 0) && (lcoef de DATA =? 0))); [discriminate|].
      destruct (rgn_get (vs_rgn A) B) as [r|]; [|discriminate].
      destruct (vr_kind r); try discriminate;
        (destruct (dead_lin (v1 A) _ || dead_lin (v1 A) _); [discriminate|]);
        destruct (lo_of (v1 A) _); try discriminate; destruct (hi_of (v1 A) _); try discriminate;
        repeat match goal with |- (if ?c then _ else _) = _ -> _ => destruct c; try discriminate end.
  Qed.

  #[using="Type"] Lemma range_check_rgn_inv A de ne r lo hi :
    range_check P A de ne true = RA_rgn r lo hi ->
    exists B, base_syms A de = [B] /\ lcoef de B = 1 /\ lcoef de SP0 = 0 /\ lcoef de DATA = 0
      /\ rgn_get (vs_rgn A) B = Some r
      /\ match vr_kind r with RK_fake _ _ | RK_arg => True | _ => False end
      /\ let off := laddc (lsub de (lsym B)) (- vr_disp r) in
         lo_of (v1 A) off = Some lo /\ hi_of (v1 A) (ladd off ne) = Some hi
         /\ vr_lo r <= lo /\ hi <= vr_hi r
         /\ (lo < hi -> in_ranges (vr_w r) lo (hi - lo) = true)
         /\ rgn_addressable A r lo hi = true /\ frames_shadow_zone_ok P = true.
  Proof.
    unfold range_check. destruct (base_syms A de) as [|B [|B2 t]]; try discriminate.
    - destruct (stack_range (p1 P) (v1 A) de ne true) as [off lo' hi'| | | |m]; try discriminate.
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
        destruct (Z.leb_spec hi1 lo1) as [LE|GT]; cbn [negb andb] in H;
        (destruct (in_ranges (vr_w r0) lo1 (hi1 - lo1)) eqn:IW; cbn [negb andb] in H);
        try discriminate;
        (destruct (rgn_addressable A r0 lo1 hi1) eqn:RA; cbn [negb] in H; [|discriminate]);
        (destruct (frames_shadow_zone_ok P) eqn:FZ; cbn [negb] in H; [|discriminate]);
        injection H as <- <- <-; rewrite K; repeat split; auto; try lia; intros; try reflexivity; try lia.
  Qed.

  #[using="P1 E1 PO2"] Theorem asan_memset_dead : contract_dead2 SEGS P E mem0 CI C_asan_memset.
  Proof.
    intros A spoff nu regs mem HC HG2. pose proof (gamma2_lgamma _ _ _ _ _ _ _ _ HG2) as HL.
    pose proof HG2 as (HG1 & _). pose proof (PO1 _ _ PO2) as PO.
    cbn [contract_apply2] in HC. unfold of_ca, ca_asan_memset in HC. cbv zeta in HC. unfold get_reg2 in HC.
    destruct (nonneg_len (v1 A) (get_reg (v1 A) A2r) MAXLEN) as [nlo nhi| |msg] eqn:En; try discriminate;
      [|exact (nonneg_len_dead (v1 A) nu _ _ HL En)].
    destruct (get_reg (v1 A) A0r) as [de|]; [|discriminate].
    destruct (range_check P A de (lin_of (get_reg (v1 A) A2r)) true) as [r lo hi|rr| |msg] eqn:RC; try discriminate.
    - destruct (negb (is_zero_byte _ _)); [discriminate|]. destruct (negb (0 <? nlo)); discriminate.
    - unfold lift_cresA in HC. destruct (c_memset (p1 P) (v1 A)) as [A1 v| |m] eqn:CM; try discriminate.
      exact (memset_dead SEGS P1 E1 (zpatch P E mem0 mem) CI (v1 A) spoff nu regs mem CM HG1).
    - (* [comment removed for export] *)
      unfold range_check in RC. destruct (base_syms A de) as [|B [|B2 t]]; try discriminate.
      + destruct (stack_range (p1 P) (v1 A) de _ true) as [off lo hi| | | |m] eqn:Esr; try discriminate;
          [|exact (stack_range_dead (p1 P) (v1 A) nu _ _ true HL Esr)].
        repeat match type of RC with (if ?c then _ else _) = _ => destruct c; try discriminate end.
      + destruct (negb _ || negb _); [discriminate|]. destruct (rgn_get (vs_rgn A) B) as [r|]; [|discriminate].
        destruct (vr_kind r); try discriminate;
          (destruct (dead_lin (v1 A) (laddc (lsub de (lsym B)) (- vr_disp r))) eqn:D1;
             [exact (dead_lin_false (v1 A) nu _ HL D1)|]);
          (destruct (dead_lin (v1 A) (ladd (laddc (lsub de (lsym B)) (- vr_disp r)) (lin_of (get_reg (v1 A) A2r)))) eqn:D2;
             [exact (dead_lin_false (v1 A) nu _ HL D2)|]); cbn [orb] in RC;
          destruct (lo_of (v1 A) _); try discriminate; destruct (hi_of (v1 A) _); try discriminate;
          repeat match type of RC with (if ?c then _ else _) = _ => destruct c; try discriminate end.
  Qed.

  #[using="P1 E1 PO2 SHOFF ROM_HI MCELLS MCELLS_OK FSLEN RUN"] Theorem asan_memset_post : contract_post2 SEGS P E mem0 rom CI C_asan_memset tgt.
  Proof.
    intros A spoff l nu regs mem ra HC HG2 MEMO Hsp HK Hret Hra.
    pose proof HG2 as (HG1 & HE & HM & HF2 & HDD & RGN & LIVE & BEL2 & GL2 & FI2 & MOK).
    pose proof (gamma2_lgamma _ _ _ _ _ _ _ _ HG2) as HL.
    pose proof (PO1 _ _ PO2) as PO. pose proof PO as (P0 & Psphi & PS & PF & PW & PR & PP & PB).
    pose proof HE as (HEV1 & _ & HFS & HZO & HKC). pose proof HEV1 as (E1a & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E11 & E12).
    cbn [contract_apply2] in HC. unfold of_ca, ca_asan_memset in HC. cbv zeta in HC.
    destruct (nonneg_len (v1 A) (get_reg2 A A2r) MAXLEN) as [nlo nhi| |msg] eqn:En; try discriminate.
    destruct (nonneg_len_sound (v1 A) nu _ _ _ _ HL En) as [ne (Ene & Hn0 & Hn1 & Hn2)].
    destruct (get_reg2 A A0r) as [de|] eqn:Ede; [|discriminate].
    rewrite Ene in HC. cbn [lin_of] in HC. unfold MAXLEN in Hn2.
    set (n := eval nu ne) in *.
    (* [comment removed for export] *)
    unfold get_reg2 in Ede, Ene.
    assert (R12 : getr regs 12%bv = wordZ n).
    { apply (reg_word SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem 12%bv ne n HG1); [vm_compute; lia|exact Ene|reflexivity|lia]. }
    pose proof (reg_val SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem 10%bv de HG1 ltac:(vm_compute; lia) Ede) as [V10 B10].
    assert (R2 : getr regs 2%bv = wordZ (e_sp0 E1 + spoff)).
    { apply (reg_word SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem 2%bv (lsymc SP0 spoff) (e_sp0 E1 + spoff) HG1);
        [vm_compute; lia|exact Hsp| |].
      - rewrite eval_lsymc. rewrite (proj1 (proj2 (proj2 HG1)) SP0 (e_sp0 E1)) by reflexivity. reflexivity.
      - destruct HK as [HK|HK]; [cbn in HK; discriminate|]. apply in_ranges_sound in HK as (wlo & whi & Hw & W1 & W2).
        destruct (PR _ Hw). cbn [fst snd contract2_K] in *. unfold K_asan_memset, P1, E1 in *. lia. }
    (* [comment removed for export] *)
    assert (HKR : - vp_frame P1 <= spoff - 2208 /\ spoff <= 0 /\ exists wr, In wr (vp_wstack P1) /\ fst wr <= spoff - 2208 /\ spoff <= snd wr).
    { destruct HK as [HK|HK]; [cbn in HK; discriminate|]. apply in_ranges_sound in HK as (wlo & whi & Hw & W1 & W2).
      destruct (PR _ Hw). cbn [fst snd contract2_K] in *. unfold K_asan_memset, P1, E1 in *. split; [lia|]. split; [lia|]. exists (wlo, whi). cbn. split; [exact Hw|lia]. }
    destruct HKR as (K1 & K2 & KW).
    set (usp := e_sp0 E1 + spoff) in *.
    assert (USP : 0 <= e_sp0 E1 - vp_frame P1 /\ e_sp0 E1 - vp_frame P1 <= usp - 2208 /\ usp <= e_sp0 E1 /\ e_sp0 E1 < 2 ^ 64)
      by (unfold usp, P1, E1 in *; lia).
    pose proof (proj1 (proj2 HG1)) as (MF & MD & MP & MFM).
    assert (JOK : forall a, usp - JUNK <= a < usp -> store_ok SEGS mem (wordZ a) 1 = true).
    { intros a Ha. unfold JUNK in Ha. apply (proj1 (MF a ltac:(unfold usp, P1, E1 in *; lia))). }
    destruct (range_check P A de ne true) as [r lo hi|rr| |msg] eqn:RC; try discriminate.
    - (* [comment removed for export] *)
      destruct (range_check_rgn_inv A de ne r lo hi RC) as (B & HBS & C1 & C2 & C3 & HGr & HKr & LET).
      cbv zeta in LET. destruct LET as (LO & HI & RLO & RHI & HWr & HRA & HFZ).
      unfold get_reg2 in HC.
      destruct (is_zero_byte (v1 A) (get_reg (v1 A) A1r)) eqn:Ezb; cbn [negb] in HC; [|discriminate].
      destruct (Z.ltb_spec 0 nlo) as [NLO|]; cbn [negb] in HC; [|discriminate].
      cbv zeta in HC. cbn [ca_ok1] in HC. injection HC as <-.
      assert (Hn : 0 < n) by lia.
      (* [comment removed for export] *)
      pose proof (rgn_get_in _ _ _ HGr) as [Hr HBr].
      pose proof (RGN r Hr) as ROK. pose proof ROK as (RB1 & RB2 & RB3 & RDS & CELLS & PERM & NUL & KIND).
      assert (ND : is_data_shadow r = false) by (unfold is_data_shadow; destruct (vr_kind r); auto; contradiction).
      set (off := laddc (lsub de (lsym B)) (- vr_disp r)) in *.
      assert (Eoff : eval nu de = rbase nu r + eval nu off) by (unfold off; rewrite <- HBr, eval_off; lia).
      pose proof (bnd_sound (v1 A) nu off HL) as Bo. pose proof (bnd_sound (v1 A) nu (ladd off ne) HL) as Bo2.
      unfold lo_of in LO. unfold hi_of in HI.
      destruct (bnd (v1 A) off) as [olo ohi] eqn:Ebo. cbn [fst] in LO. subst olo.
      destruct (bnd (v1 A) (ladd off ne)) as [olo2 ohi2] eqn:Ebo2. cbn [snd] in HI. subst ohi2.
      destruct Bo as [Bo _]. destruct Bo2 as [_ Bo2]. cbn [fst snd lo_le hi_ge] in Bo, Bo2. rewrite eval_ladd in Bo2. fold n in Bo2.
      set (ov := eval nu off) in *. set (d := rbase nu r + ov) in *.
      (* [comment removed for export] *)
      unfold env_fs in HFS.
      assert (FSnz : vp_fs P <> None) by (unfold kind_ok in KIND; destruct (vr_kind r); try contradiction; exact (proj1 KIND)).
      destruct (vp_fs P) as [[flen fssl]|] eqn:EFS; [|exfalso; exact (FSnz eq_refl)].
      destruct HFS as (_ & FS1 & FS2 & FS3 & FS4 & _ & _ & APsf & APdf & APds & HMsp & HMd & _ & SPHI & _).
      pose proof (FSLEN _ _ eq_refl) as FS5. clear APdf APds HMd. unfold HIGH_MEM_BEG, HIGH_MEM_END, FS_NCLASSES, FS_SSL in *.
      assert (FR : exists fa cid, 0 <= cid <= 4 /\ e_fs E + FS_FRAMES <= fa /\ fa + fake_size cid <= e_fs E + FS_FRAMES + 5 * 2 ^ 20
                    /\ fa <= rbase nu r + lo /\ rbase nu r + hi <= fa + fake_size cid /\ fa mod 64 = 0
                    /\ B <> SP0 /\ B <> DATA /\ B <> FSB).
      { unfold kind_ok in KIND. destruct (vr_kind r) as [cid fl| | | |] eqn:Kr; try contradiction.
        - destruct KIND as (_ & Hcid & VLO & VHI & LF & pos & Hpos & Ebeta & _).
          destruct (frame_in_area (e_fs E) cid pos Hcid Hpos) as [G1 G2].
          exists (frame_addr (e_fs E) cid pos), cid. rewrite <- Ebeta. rewrite <- HBr.
          repeat split; try (ltac2:(LK.k [@E4; @E5; @E11; @HBr; @Hcid; @Ebeta; @G1; @G2; @RLO; @VLO; @RHI; @VHI]); lia).
          + rewrite Ebeta. apply frame_addr_mod64; lia.
          + intros X. rewrite X in LF. cbv in LF. discriminate.
          + intros X. rewrite X in LF. cbv in LF. discriminate.
          + intros X. rewrite X in LF. cbv in LF. discriminate.
        - destruct KIND as (_ & (cid & pos & Hlive & G3 & G4) & (i & Hi & EB & _)).
          pose proof (live_valid _ _ _ HE ltac:(rewrite EFS; discriminate) Hlive) as [Vc Vp]. cbn in Vc, Vp.
          destruct (frame_in_area (e_fs E) cid pos ltac:(lia) ltac:(lia)) as [G1 G2].
          exists (frame_addr (e_fs E) cid pos), cid. rewrite <- HBr, EB.
          repeat split; try (ltac2:(LK.k [@E4; @E5; @E11; @HBr; @EB; @Vc; @G1; @G2; @RLO; @G3; @RHI; @G4]); lia).
          + apply frame_addr_mod64; lia.
          + unfold ASYM2, SP0. intros X. apply (f_equal Z.pos) in X. rewrite Z2Pos.id in X by lia. lia.
          + unfold ASYM2, DATA. intros X. apply (f_equal Z.pos) in X. rewrite Z2Pos.id in X by lia. lia.
          + unfold ASYM2, FSB. intros X. apply (f_equal Z.pos) in X. rewrite Z2Pos.id in X by lia. lia. }
      destruct FR as (fa & cid & Hcid & FA1 & FA2 & FA3 & FA4 & FAm & NB1 & NB2 & NB3).
      assert (DRANGE : fa <= d /\ d + n <= fa + fake_size cid /\ 0 <= d /\ d + n <= 2 ^ 47 - 1).
      { unfold d. unfold FS_FRAMES in *. (ltac2:(LK.k [@P0; @FS1; @FS2; @APsf; @HMsp; @SPHI; @E4; @E5; @E11; @HBr; @Bo; @Bo2; @FS5; @FA1; @FA2; @FA3; @FA4; @NB1; @NB2; @NB3]); lia). }
      assert (DBAND : band_ok d n).   (* [comment removed for export] *)
      { apply (band_ok_sub (e_fs E) flen d n (proj2 FS1)); [unfold HIGH_MEM_END; (ltac2:(LK.k [@FS2; @E11; @HBr; @NB1; @NB2; @NB3; @E4; @E5; @FA1; @DRANGE; @FS5; @FA2]); lia)|unfold d; unfold FS_FRAMES in *; (ltac2:(LK.k [@FS2; @E11; @HBr; @NB1; @NB2; @NB3; @E4; @E5; @FA1; @DRANGE; @FS5; @FA2]); lia)|unfold d; unfold FS_FRAMES in *; (ltac2:(LK.k [@FS2; @E11; @HBr; @NB1; @NB2; @NB3; @E4; @E5; @FA1; @DRANGE; @FS5; @FA2]); lia)]. }
      assert (R10 : getr regs 10%bv = wordZ d).
      { apply wordZ_eq_u. rewrite V10, Eoff. fold ov. unfold d. apply zwrap_id. unfold d in DRANGE. lia. }
      set (c := bv_unsigned (getr regs 11%bv)).
      assert (R11 : getr regs 11%bv = wordZ c) by (symmetry; apply wordZ_u).
      assert (Hcz : c mod 256 = 0).
      { pose proof (gamma_get_reg SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem 11%bv HG1) as [W11 _]. change (rz 11%bv) with A1r in W11.
        destruct (get_reg (v1 A) A1r) as [ce|] eqn:Ec; [|cbn in Ezb; discriminate].
        apply (is_zero_byte_sound mem0 (v1 A) nu (Some ce) (getr regs 11%bv) HL Ezb). exact (proj2 W11). }
      assert (Ec8 : Z_to_bv 8 c = Z_to_bv 8 0).
      { apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap8_mod. change (2 ^ 8) with 256. rewrite Hcz. reflexivity. }
      (* [comment removed for export] *)
      unfold rgn_addressable in HRA.
      destruct (rgn_shadow_of (vs_rgn A) (vr_base r)) as [sh|] eqn:SH; [|discriminate].
      destruct (rgn_shadow_of_in _ _ _ SH) as [Hsh Ksh]. rewrite HBr in Ksh.
      destruct (rgn_residue A r) as [rB|] eqn:RES; [|discriminate].
      pose proof (RGN sh Hsh) as (_ & _ & _ & _ & _ & _ & _ & KINDsh). unfold kind_ok in KINDsh. rewrite Ksh in KINDsh.
      destruct KINDsh as (_ & DISPsh & _ & _ & _ & KX). destruct (KX NB1 NB2 NB3) as (ro & Gro & B8 & KM).
      rewrite HGr in Gro. injection Gro as <-.
      set (S := nu (vr_base sh)) in *.
      assert (RBsh : rbase nu sh = SBz + S) by (unfold rbase; rewrite DISPsh, SHOFF; reflexivity).
      assert (GRID : rbase nu r = 8 * S + rB /\ 0 <= rB < 8).
      { unfold rgn_residue in RES. unfold kind_ok in KIND. destruct (vr_kind r) as [cid' fl| | | |] eqn:Kr; try discriminate.
        - injection RES as <-. lia.
        - destruct (Z.eqb_spec (vr_disp r) 0) as [D0|]; [|discriminate].
          destruct (base_res8_sound A nu _ _ HL RES) as [HrB [k Hk]]. destruct KM as (ES & _).
          unfold rbase in ES |- *. rewrite D0, HBr in *. rewrite Hk in ES |- *.
          replace ((0 + (8 * k + rB)) / 8) with k in ES by (symmetry; replace (0 + (8 * k + rB)) with (rB + k * 8) by lia; rewrite Z.div_add by lia; rewrite Z.div_small by lia; lia).
          (ltac2:(LK.k [@E4; @E5; @E11; @HBr; @NB1; @NB2; @NB3; @ES; @HrB]); lia). }
      destruct GRID as [GRID HrB].
      assert (GR : forall g, (lo + rB) / 8 <= g <= (hi + rB - 1) / 8 ->
        exists k : byte, mem (wordZ (SBz + S + g)) = Some k
                         /\ (bv_unsigned k = 0 \/ Z.min (hi + rB) (8 * g + 8) - 8 * g <= bv_unsigned k < 8)).
      { intros g Hg. destruct (range_granules_ok_sound sh (lo + rB) (hi + rB) g HRA ltac:(lia) Hg) as (b & SB & Hb).
        destruct (sh_byte_mem A nu regs mem sh g b HG2 Hsh ltac:(unfold is_shadow; rewrite Ksh; reflexivity) SB) as (k & Rk & Vk).
        rewrite RBsh in Rk. exists k. split; [|rewrite Vk; exact Hb].
        apply rdn1_mem; [|exact Rk]. unfold SBz, FS_FRAMES in *.
        pose proof (div8_facts (lo + rB)). pose proof (div8_facts (hi + rB - 1)). (ltac2:(LK.k [@P0; @FS1; @APsf; @HMsp; @SPHI; @E4; @E5; @E11; @Hn; @HBr; @Bo; @Bo2; @FS5; @FA1; @FA2; @FA3; @FA4; @NB1; @NB2; @NB3; @DRANGE; @GRID; @Hg; @H; @H0]); lia). }
      assert (SHAD :
        (forall g, d / 8 <= g < (d + n - 1) / 8 -> mem (wordZ (SBz + g)) = Some (Z_to_bv 8 0))
        /\ (exists b1 : byte, mem (wordZ (SBz + (d + n - 1) / 8)) = Some b1
                             /\ (bv_unsigned b1 = 0 \/ (d + n - 1) mod 8 < bv_unsigned b1 < 8))).
      { unfold d. rewrite GRID. replace (8 * S + rB + ov) with (8 * S + (ov + rB)) by lia.
        apply (shadow_access mem S (lo + rB) (hi + rB) (ov + rB) n GR); lia. }
      (* [comment removed for export] *)
      assert (NUE8 : nuE E FS8 = e_fs E / 8).
      { unfold nuE, fix_val2. replace (fix_val (ev1 E) FS8) with (@None Z) by reflexivity. reflexivity. }
      assert (WRD : forall q, fa <= q <= fa + fake_size cid - 1 ->
        exists w : word, rdn SEGS mem (wordZ ((SBz + q / 8) / 8 * 8)) 8 = Some (word_to_le_bytes 8 w)).
      { intros q Hq. unfold FS_FRAMES in *.
        destruct (arith_fs8_word (e_fs E) q FS3 ltac:((ltac2:(LK.k [@FS1; @E11; @HBr; @NB1; @NB2; @NB3; @E4; @E5; @FA1; @FA2; @Hq]); lia)) ltac:((ltac2:(LK.k [@FS1; @E11; @HBr; @NB1; @NB2; @NB3; @E4; @E5; @FA1; @FA2; @Hq]); lia))) as [Wlo Whi]. pose proof (div8_facts (e_fs E)).
        apply (word_readable A nu regs mem _ HG2); [| unfold SBz in *; (ltac2:(LK.k [@P0; @FS1; @HMsp; @E4; @E5; @E11; @HBr; @FA1; @NB1; @NB2; @NB3; @Hq; @Wlo; @H; @SPHI; @Hn; @FS5; @DRANGE; @Whi]); lia) | unfold SBz in *; (ltac2:(LK.k [@P0; @FS1; @HMsp; @E4; @E5; @E11; @HBr; @FA1; @NB1; @NB2; @NB3; @Hq; @Wlo; @H; @SPHI; @Hn; @FS5; @DRANGE; @Whi]); lia)].
        intros i Hi. apply (zone_has_sound A nu regs mem FS8 _ _ _ HG2 HFZ). rewrite SHOFF, NUE8.
        unfold SBz, FS_FRAMES_G, FS_FRAMES_GLEN in *. (ltac2:(LK.k [@P0; @FS1; @HMsp; @E4; @E5; @E11; @HBr; @FA1; @NB1; @NB2; @NB3; @Hq; @Wlo; @Whi; @Hi]); lia). }
      (* [comment removed for export] *)
      apply in_ranges_sound in HWr as (wlo & whi & HWin & W1 & W2); [|lia].
      destruct (PERM ND) as [RDp WR].
      assert (DOK : forall j, 0 <= j < n -> store_ok SEGS mem (wordZ (d + j)) 1 = true).
      { intros j Hj. destruct (WR wlo whi (ov + j) HWin ltac:((ltac2:(LK.k [@E4; @E5; @E11; @W1; @W2; @HBr; @Bo; @Bo2; @NB1; @NB2; @NB3; @Hj]); lia))) as (_ & _ & X & _). unfold d. rewrite <- Z.add_assoc. exact X. }
      (* [comment removed for export] *)
      destruct (RUN mem d c n usp regs ra (MCELLS_OK _ _ _ _ HG2) ltac:((ltac2:(LK.k [@E4; @E5; @E11; @Hn; @HBr; @Bo; @FA1; @FA2; @FA3; @NB1; @NB2; @NB3; @DRANGE; @H]); lia)) ltac:((ltac2:(LK.k [@E4; @E5; @E11; @Hn; @HBr; @Bo; @FA1; @FA2; @FA3; @NB1; @NB2; @NB3; @DRANGE; @H]); lia)) ltac:(unfold c; pose proof (bv_unsigned_in_range 64 (getr regs 11%bv)); change (bv_modulus 64) with (2 ^ 64) in *; (ltac2:(LK.k [@E4; @E5; @E11; @Hn; @HBr; @Bo; @FA1; @FA2; @FA3; @NB1; @NB2; @NB3; @DRANGE; @H]); lia)) ltac:((ltac2:(LK.k [@E4; @E5; @E11; @Hn; @HBr; @Bo; @FA1; @FA2; @FA3; @NB1; @NB2; @NB3; @DRANGE; @H]); lia)))
        as (regs' & m' & MS & Q10 & Q2 & Q1 & QK & QM & QG).
      { intros _. exact DBAND. }
      { unfold SBz, usp, P1, E1 in *. (ltac2:(LK.k [@HMsp; @SPHI; @E4; @E5; @E11; @USP; @HBr; @NB1; @NB2; @NB3]); lia). }
      { right. unfold JUNK, d, usp. unfold FS_FRAMES in *. destruct APsf as [X|X]; unfold P1, E1 in *; [right|left]; lia. }
      { intros _. unfold JUNK, SBz, usp. apply (arith_shd_rgn (e_sp0 E1) (vp_frame P1) spoff (d + n - 1)); unfold P1, E1 in *; (ltac2:(LK.k [@HMsp; @E11; @HBr; @NB1; @NB2; @NB3; @E4; @E5; @K1; @Hn; @DRANGE]); lia). }
      { intros g _ Hg. exact (proj1 SHAD g Hg). }
      { intros _. exact (proj2 SHAD). }
      { intros _. apply (WRD d). lia. }
      { intros _. apply (WRD (d + n - 1)). lia. }
      { exact DOK. }
      { exact JOK. }
      { exact Hret. } { exact Hra. } { exact R2. } { exact R10. } { exact R11. } { exact R12. }
      (* [comment removed for export] *)
      set (bs := zeros (Z.to_nat n)).
      assert (Hlen : length bs = Z.to_nat n) by apply length_zeros.
      assert (LENn : Z.of_nat (length bs) = n) by (rewrite Hlen; lia).
      set (m_b := wbytes mem (wordZ d) bs).
      assert (QM0 : forall x : word, bv_unsigned x < usp - JUNK \/ usp <= bv_unsigned x -> m' x = m_b x).
      { intros x Hx. rewrite (QM x Hx), Ec8. reflexivity. }
      assert (RD : rdn SEGS m_b (wordZ d) (Z.to_nat n) = Some (zeros (Z.to_nat n))).
      { unfold m_b, bs. rewrite <- (length_zeros (Z.to_nat n)) at 2. apply rdn_wbytes_hit. rewrite length_zeros, u_wordZ; (ltac2:(LK.k [@P0; @SPHI; @E4; @E5; @E11; @Hn; @HBr; @Bo2; @FS5; @FA2; @FA4; @NB1; @NB2; @NB3; @DRANGE; @Hlen]); lia). }
      assert (RD1 : forall j, 0 <= j < n -> rdn SEGS m_b (wordZ (d + j)) 1 = Some [Z_to_bv 8 0]).
      { intros j Hj. unfold m_b, bs. replace j with (Z.of_nat (Z.to_nat j)) by (ltac2:(LK.k [@E4; @E5; @E11; @Hn; @HBr; @NB1; @NB2; @NB3; @Hlen; @Hj]); lia).
        rewrite (rdn_wbytes_byte SEGS mem d (zeros (Z.to_nat n)) (Z.to_nat j)); rewrite ?length_zeros; try (ltac2:(LK.k [@E4; @E5; @E11; @HBr; @NB1; @NB2; @NB3; @DRANGE; @Hlen; @P0; @SPHI; @Hn; @Bo2; @FS5; @FA2; @FA4; @Hn1; @NLO; @Hj]); lia).
        rewrite nth_zeros. reflexivity. }
      (* [comment removed for export] *)
      set (ends := lin_is_const ne && (0 <? lc ne) && (lo + lc ne =? hi)) in *.
      set (exact := ends && (lc ne <=? MEMSET_TRACK_MAX)) in *.
      set (r2 := rgn_havoc r lo hi exact ends) in *.
      assert (EXACT : exact = true -> ov = lo /\ lo + n = hi /\ lc ne = n).
      { unfold exact, ends. intros X. apply andb_prop in X as [X _]. apply andb_prop in X as [X X3]. apply andb_prop in X as [X1 X2].
        apply Z.eqb_eq in X3. pose proof (eval_is_const nu ne X1) as EN. unfold n in *. rewrite EN in *. (ltac2:(LK.k [@E4; @E5; @E11; @Hn; @HBr; @Bo; @Bo2; @NB1; @NB2; @NB3; @Hlen; @X3]); lia). }
      assert (ENDS : ends = true -> ov = lo /\ lo + n = hi).
      { unfold ends. intros X. apply andb_prop in X as [X X3]. apply andb_prop in X as [X1 X2].
        apply Z.eqb_eq in X3. pose proof (eval_is_const nu ne X1) as EN. unfold n in *. rewrite EN in *. (ltac2:(LK.k [@E4; @E5; @E11; @Hn; @HBr; @Bo; @Bo2; @NB1; @NB2; @NB3; @Hlen; @X3]); lia). }
      assert (SH2 : rshape r r2) by (unfold r2, rgn_havoc; eapply rshape_trans; [apply rshape_set_cells|apply rshape_set_rnul]).
      pose proof SH2 as (SB2 & _ & SK2 & _).
      assert (INB : In (vr_base r2) (map vr_base (vs_rgn A))) by (rewrite SB2; apply in_map; exact Hr).
      set (l1 := rgn_upd (vs_rgn A) r2).
      set (l2 := match vr_kind r2 with RK_arg => havoc_other_args l1 (vr_base r2) | _ => l1 end).
      assert (SM1 : shape_map (vs_rgn A) l1).
      { unfold l1. apply rgn_upd_shape; [|exact INB]. intros x Hx EB.
        rewrite (live_ok_base_inj nu A x r LIVE Hx Hr ltac:(rewrite EB; exact SB2)). exact SH2. }
      assert (SM2 : shape_map (vs_rgn A) l2).
      { unfold l2. rewrite SK2. destruct (vr_kind r); try exact SM1. eapply shape_map_trans; [exact SM1|apply havoc_shape]. }
      pose proof LIVE as (_ & _ & _ & ND0).
      assert (MEM : forall x, In x l2 ->
                (x = r2) \/ (In x (vs_rgn A) /\ vr_base x <> vr_base r /\ ~ (vr_kind r = RK_arg /\ vr_kind x = RK_arg))
                \/ (exists y, In y (vs_rgn A) /\ vr_base y <> vr_base r /\ vr_kind r = RK_arg /\ vr_kind y = RK_arg
                                 /\ x = set_rnul (set_cells y []) [])).
      { intros x Hx. unfold l2 in Hx. rewrite SK2, SB2 in Hx.
        assert (L1C : forall y, In y l1 -> y = r2 \/ (In y (vs_rgn A) /\ vr_base y <> vr_base r)).
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
        apply andb_true_intro. split; apply Z.leb_le; (ltac2:(LK.k [@E4; @E5; @E11; @W1; @Hn; @HBr; @Bo; @NB1; @NB2; @NB3; @Hlen; @SB2; @W2; @Bo2]); lia). }
      destruct (rgn_write_sound SEGS P E mem0 PO2 A nu regs mem r ov bs l2 HG2 Hr ND
                  ltac:(destruct (vr_kind r); auto; contradiction) ltac:(rewrite LENn; lia) HWIN SM2) as (G2 & FMb2 & FST2 & BND & SOK).
      { (* [comment removed for export] *)
        intros r2' Hr2' NBx. destruct (MEM r2' Hr2') as [->|[(X1 & X2 & X3)|(y & Y1 & Y2 & Y3 & Y4 & ->)]].
        + exfalso. apply NBx. exact SB2.
        + exists r2'. split; [exact X1|]. split; [apply rshape_refl|]. left. auto.
        + exists y. split; [exact Y1|]. split; [|right; split; reflexivity].
          eapply rshape_trans; [apply rshape_set_cells|apply rshape_set_rnul]. }
      { (* [comment removed for export] *)
        intros r' Hr' EB.
        assert (ER : r' = r2).
        { destruct (MEM r' Hr') as [->|[(X1 & X2 & X3)|(y & Y1 & Y2 & Y3 & Y4 & ->)]]; [reflexivity|exfalso; exact (X2 EB)|].
          exfalso. apply Y2. exact EB. }
        subst r'. fold d. change (wbytes mem (wordZ d) bs) with m_b.
        assert (NSH : is_shadow r = false) by (unfold is_shadow; destruct (vr_kind r); auto; contradiction).
        assert (CELLS2 : forall x, In x (vr_cells r2) ->
                  (In x (vr_cells r) /\ (fst x + fst (snd x) <= lo \/ hi <= fst x))
                  \/ (exact = true /\ exists o w, x = (o, (w, Some (lconst 0))) /\ lo <= o /\ o + w <= hi /\ 0 < w)).
        { intros [kk [ww vv]] Hin. unfold r2, rgn_havoc in Hin. cbn [vr_cells set_rnul set_cells] in Hin.
          assert (KILL : In (kk, (ww, vv)) (cm_kill (vr_cells r) lo hi) ->
                    In (kk, (ww, vv)) (vr_cells r) /\ (kk + ww <= lo \/ hi <= kk)).
          { intros Hk. pose proof (cm_kill_disjoint _ _ _ _ _ _ Hk). split; [eapply cm_kill_sub; exact Hk|lia]. }
          destruct exact.
          - destruct (EXACT eq_refl) as (E1x & E2x & E3x).
            pose proof (Z.div_mod n 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Hmb.
            replace (hi - lo) with n in Hin by lia.
            apply zero_cells1_in in Hin as [Hin|[i [Hi Ei]]].
            + apply zero_cells8_in in Hin as [Hin|[i [Hi Ei]]]; [left; cbn [fst snd]; exact (KILL Hin)|].
              right. split; [reflexivity|]. injection Ei as -> -> ->. eexists _, _. split; [reflexivity|].
              assert (Hi' : Z.of_nat i < n / 8) by (apply Nat2Z.inj_lt in Hi; rewrite Z2Nat.id in Hi by (apply Z.div_pos; lia); exact Hi). (ltac2:(LK.k [@P0; @FS1; @HMsp; @E4; @E5; @E11; @Hn; @HBr; @NB1; @NB2; @NB3; @Hlen; @SB2; @EB; @Hi; @E2x; @Hdm]); lia).
            + right. split; [reflexivity|]. injection Ei as -> -> ->. eexists _, _. split; [reflexivity|].
              assert (Hi' : Z.of_nat i < n mod 8) by (apply Nat2Z.inj_lt in Hi; rewrite Z2Nat.id in Hi by lia; exact Hi).
              rewrite Z2Nat.id by (apply Z.div_pos; lia). (ltac2:(LK.k [@P0; @FS1; @HMsp; @E4; @E5; @E11; @Hn1; @NLO; @Hn; @HBr; @NB1; @NB2; @NB3; @Hlen; @SB2; @EB; @Hi; @E2x; @Hdm; @Hmb; @Hi']); lia).
          - left. cbn [fst snd]. exact (KILL Hin). }
        assert (NUL2 : forall f, In f (vr_nul r2) ->
                  (ends = true /\ (f = (lo, lo) \/ f = (hi - 1, hi - 1))) \/ (In f (vr_nul r) /\ (snd f < lo \/ hi <= fst f))).
        { intros f Hin. unfold r2, rgn_havoc in Hin. cbn [vr_nul set_rnul set_cells] in Hin.
          assert (FIL : In f (List.filter (fun f0 : Z * Z => (snd f0 <? lo) || (hi <=? fst f0)) (vr_nul r)) ->
                    In f (vr_nul r) /\ (snd f < lo \/ hi <= fst f)).
          { intros Hf. apply filter_In in Hf as [Hf C]. split; [exact Hf|]. apply Bool.orb_prop in C as [C|C]; [apply Z.ltb_lt in C|apply Z.leb_le in C]; lia. }
          destruct ends; [|right; exact (FIL Hin)].
          destruct Hin as [<-|[<-|Hin]]; [left; auto|left; auto|right; exact (FIL Hin)]. }
        split.
        2:{ intros kk ww e Hin. destruct BEL2 as (_ & BR & _). pose proof (proj1 (proj2 (BR r Hr))) as CB.
            destruct (CELLS2 _ Hin) as [[Hold _]|(_ & o & w & X & _)]; [exact (CB _ _ _ Hold)|].
            injection X as X1 X2 X3. subst. apply lin_below_lconst. }
        eapply (region_ok_self SEGS P E A _ nu mem m_b r r2 HE ROK SH2 ND).
        + apply wbytes_grows.
        + (* [comment removed for export] *)
          unfold kind_ok in KIND. destruct (vr_kind r) as [cidf fl| | | |] eqn:K0; auto.
          destruct KIND as (_ & Hcf & _ & _ & _ & pos & Hpos & _ & Efl & _).
          pose proof (flag_addr_range (e_fs E) cidf pos Hcf Hpos) as FLR. rewrite <- Efl in FLR.
          unfold m_b. apply wblock_rdn1; rewrite ?LENn; unfold FS_FLAGS, FS_FRAMES in *; try (ltac2:(LK.k [@P0; @SPHI; @E4; @E5; @E11; @Hn; @HBr; @Bo2; @FS5; @FA2; @FA4; @NB1; @NB2; @NB3; @DRANGE; @Hlen; @SB2; @EB; @FS1; @APsf; @HMsp; @FA1; @FLR]); lia).
        + intros s0 ro G _ _. cbn [vs_rgn]. exact (shape_map_get _ _ _ _ SM2 G).
        + destruct (vr_kind r) eqn:K0; auto. cbn [vs_live]. apply (proj2 (proj1 LIVE (vr_base r))). exists r. rewrite K0. auto.
        + destruct (vr_kind r); auto; contradiction.
        + (* [comment removed for export] *)
          intros cc cw cv Hin. destruct (CELLS2 _ Hin) as [[Hold DISJ]|(EX & o & w & X & O1 & O2 & O3)].
          * cbn [fst snd] in DISJ. destruct (CELLS _ _ _ Hold) as (L1 & L2 & L3 & RCH). split; [lia|]. split; [lia|]. split; [lia|].
            unfold m_b. apply kept_cell; rewrite ?LENn; try (ltac2:(LK.k [@P0; @SPHI; @E4; @E5; @E11; @Hn; @HBr; @Bo2; @FS5; @FA2; @FA4; @NB1; @NB2; @NB3; @DRANGE; @Hlen; @SB2; @EB; @Hn1; @NLO; @RB1; @L1; @RB2; @Bo; @L3; @L2; @DISJ]); lia). exact RCH.
          * injection X as -> -> ->. destruct (EXACT EX) as (E1x & E2x & E3x).
            split; [lia|]. split; [lia|]. split; [lia|].
            unfold rcell_holds. rewrite NSH. cbn [andb cell_holds]. exists (zeros (Z.to_nat w)). split.
            -- replace (rbase nu r + o) with (d + (o - ov)) by (unfold d; lia).
               pose proof (rdn_sub SEGS m_b (Z.to_nat n) (wordZ d) (zeros (Z.to_nat n)) (Z.to_nat (o - ov)) (Z.to_nat w) RD ltac:((ltac2:(LK.k [@E4; @E5; @E11; @Hn; @HBr; @NB1; @NB2; @NB3; @Hlen; @SB2; @EB; @O1; @O2; @O3; @E1x; @E2x]); lia))) as X.
               rewrite sub_zeros in X by (ltac2:(LK.k [@E4; @E5; @E11; @Hn; @HBr; @NB1; @NB2; @NB3; @Hlen; @SB2; @EB; @O1; @O2; @O3; @E1x; @E2x]); lia). unfold at_ in X. rewrite u_wordZ, Z2Nat.id in X by (ltac2:(LK.k [@P0; @SPHI; @E4; @E5; @E11; @Hn; @HBr; @FS5; @FA2; @NB1; @NB2; @NB3; @DRANGE; @Hlen; @SB2; @EB; @O1; @E1x]); lia). exact X.
            -- rewrite bytes_le_zeros, eval_lconst. reflexivity.
        + (* [comment removed for export] *)
          intros nlo' nhi' Hin. destruct (NUL2 _ Hin) as [(EX & [Ef|Ef])|(Hold & DISJ)].
          * injection Ef as -> ->. destruct (ENDS EX) as [E1x E2x]. exists lo, (Z_to_bv 8 0).
            split; [lia|]. split; [lia|]. split; [|reflexivity]. replace (rbase nu r + lo) with (d + 0) by (unfold d; lia). apply RD1. lia.
          * injection Ef as -> ->. destruct (ENDS EX) as [E1x E2x]. exists (hi - 1), (Z_to_bv 8 0).
            split; [lia|]. split; [lia|]. split; [|reflexivity]. replace (rbase nu r + (hi - 1)) with (d + (n - 1)) by (unfold d; lia). apply RD1. lia.
          * cbn [fst snd] in DISJ. destruct (NUL _ _ Hold) as (o0 & b0 & Y1 & Y2 & Y3 & Y4).
            exists o0, b0. split; [exact Y1|]. split; [exact Y2|]. split; [|exact Y4].
            rewrite <- Y3. unfold m_b. apply wblock_rdn1; rewrite ?LENn; unfold d; (ltac2:(LK.k [@P0; @SPHI; @E4; @E5; @E11; @Hn; @HBr; @RB1; @Bo; @Bo2; @FS5; @FA2; @FA4; @NB1; @NB2; @NB3; @DRANGE; @Hlen; @SB2; @EB; @Y1; @Y2; @RB2; @DISJ]); lia). }
      (* [comment removed for export] *)
      assert (GRW : forall x, m_b x <> None -> m' x <> None).
      { intros x Hx. destruct (Z_lt_le_dec (bv_unsigned x) d) as [B1|B1]; [|destruct (Z_lt_le_dec (bv_unsigned x) (d + n)) as [B2|B2]].
        - apply QG. intros M0. apply Hx. unfold m_b. rewrite wbytes_outside; [exact M0| |]; rewrite ?LENn, ?u_wordZ by (ltac2:(LK.k [@P0; @SPHI; @E4; @E5; @E11; @Hn; @HBr; @Bo2; @FS5; @FA2; @FA4; @NB1; @NB2; @NB3; @DRANGE; @Hlen; @SB2; @B1]); lia); unfold in_rng; rewrite ?u_wordZ by (ltac2:(LK.k [@P0; @SPHI; @E4; @E5; @E11; @Hn; @HBr; @Bo2; @FS5; @FA2; @FA4; @NB1; @NB2; @NB3; @DRANGE; @Hlen; @SB2; @B1]); lia); (ltac2:(LK.k [@P0; @SPHI; @E4; @E5; @E11; @Hn; @HBr; @Bo2; @FS5; @FA2; @FA4; @NB1; @NB2; @NB3; @DRANGE; @Hlen; @SB2; @B1]); lia).
        - rewrite QM0; [exact Hx|]. unfold JUNK, d, usp in *. unfold FS_FRAMES in *. destruct APsf as [X|X]; unfold P1, E1 in *; [left|right]; (ltac2:(LK.k [@X; @E4; @E5; @E11; @USP; @Hn; @HBr; @FS5; @FA2; @NB1; @NB2; @NB3; @DRANGE; @Hlen; @SB2; @B2; @FA1; @B1]); lia).
        - apply QG. intros M0. apply Hx. unfold m_b. rewrite wbytes_outside; [exact M0| |]; rewrite ?LENn, ?u_wordZ by (ltac2:(LK.k [@P0; @SPHI; @E4; @E5; @E11; @Hn; @HBr; @FS5; @FA2; @NB1; @NB2; @NB3; @DRANGE; @Hlen; @SB2; @B2]); lia); unfold in_rng; rewrite ?u_wordZ by (ltac2:(LK.k [@P0; @SPHI; @E4; @E5; @E11; @Hn; @HBr; @FS5; @FA2; @NB1; @NB2; @NB3; @DRANGE; @Hlen; @SB2; @B2]); lia); (ltac2:(LK.k [@P0; @SPHI; @E4; @E5; @E11; @Hn; @HBr; @FS5; @FA2; @NB1; @NB2; @NB3; @DRANGE; @Hlen; @SB2; @B2]); lia). }
      set (A' := mkVS2 (v1 A) l2 (vs_live A) (vs_divdef A) []) in *.
      pose proof (proj1 G2) as Gb1. cbn [v1] in Gb1.
      pose proof (gamma_junk SEGS P1 E1 (zpatch P E mem0 m_b) PO (v1 A) nu regs m_b m' spoff 2208 JUNK Gb1 QM0 GRW
                    ltac:(unfold JUNK; lia) K1 K2) as Gk.
      (* [comment removed for export] *)
      set (Bst := contract_frame C_memset (killK 2208 (v1 A) spoff) spoff (Some de)).
      assert (EFR : frame_rule 2208 (v1 A) spoff (Some de) = Bst) by (apply frame_rule_killK; lia).
      destruct (killK_shape 2208 (v1 A) spoff) as (KS1 & KS2 & KS3 & KS4 & KS5 & KS6 & KS7 & KS8 & KS9).
      destruct (contract_frame_shape C_memset (killK 2208 (v1 A) spoff) spoff (Some de)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & FR).
      assert (HLB : lgamma Bst nu).
      { apply lgamma_contract_frame; [apply lgamma_killK; exact HL|]. cbn [vbelow]. rewrite KS4. exact B10. }
      destruct (gamma_call_post SEGS P1 E1 (zpatch P E mem0 m_b) rom PO (killK 2208 (v1 A) spoff) Bst nu nu regs regs' m' m' []
                  Gk (ext_refl _ _) ltac:(unfold Bst; rewrite F5; apply Pos.le_refl) HLB) as [GB _].
      { eapply (gamma_regs_contract_frame SEGS P1 E1 (zpatch P E mem0 m_b) C_memset (killK 2208 (v1 A) spoff) (killK 2208 (v1 A) spoff) spoff (Some de) nu nu regs regs');
          [right; pose proof Gk as (_&_&_&_&_&_&_&KRg&_&_&_&KBl); split; [exact KRg|destruct KBl as (_&_&KRB&_); exact KRB]
          |apply ext_refl|reflexivity|exact QK|].
        rewrite Q10, u_wordZ, Eoff by (unfold d in DRANGE; (ltac2:(LK.k [@P0; @SPHI; @E4; @E5; @E11; @Hn; @HBr; @Bo2; @FS5; @FA2; @FA4; @NB1; @NB2; @NB3; @DRANGE; @Hlen; @SB2; @BND; @KS4; @F5]); lia)). fold ov. unfold d. symmetry. apply zwrap_id. unfold d in DRANGE. lia. }
      { intros off' w' v' Hin. left. unfold Bst in Hin. rewrite F1 in Hin. cbn in Hin. split; [exact Hin|]. intros x _. exact I. }
      { intros g w' v' Hin. unfold Bst in Hin. rewrite F2 in Hin. split; [exact Hin|]. intros x _. exact I. }
      { intros lo' hi' Hin. left. unfold Bst in Hin. destruct (F3 _ Hin) as [Hin' _]. split; [exact Hin'|]. intros x _. exact I. }
      { apply frame_mod_refl. }
      { intros x Hx. exfalso. apply Hx. exact I. }
      assert (FMU : frame_mod m_b m' (unit_regions P1 E1)).
      { split; [|exact GRW]. intros a Ha.
        assert (NJ : ~ (usp - JUNK <= bv_unsigned a < usp)).
        { intros Hin. refine (proj1 (stack_R_ok SEGS P1 E1 (zpatch P E mem0 mem) PO (spoff - JUNK) (spoff - 2208) spoff JUNK
                                   K1 K2 ltac:(unfold JUNK; lia) ltac:(unfold JUNK; lia) KW HEV1 a _) Ha).
          cbn [outside]. unfold in_rng. rewrite u_wordZ by (unfold usp, JUNK, P1, E1 in *; (ltac2:(LK.k [@HMsp; @SPHI; @E4; @E5; @E11; @USP; @Hn; @HBr; @NB1; @NB2; @NB3; @Hlen; @SB2; @KS4; @F5]); lia)). unfold usp in Hin. intros [X _]. apply X. unfold JUNK in *. lia. }
        apply QM0. pose proof (bv_unsigned_in_range 64 a). lia. }
      destruct (gamma2_lift SEGS P E mem0 PO2 A' Bst nu nu regs regs' m_b m' G2 GB (ext_refl _ _)
                  ltac:(unfold A', Bst; cbn [v1]; rewrite F5, KS4; apply Pos.le_refl) FMU
                  ltac:(unfold globs_ok2, A', Bst; cbn [v1 with_v1]; rewrite F2, KS2; exact GL2) ltac:(right; reflexivity))
        as (G3 & FM3 & FST3).
      exists (rgn_store_commit A r2), (Some de), regs', m', nu.
      assert (EST : contract_frame2 C_asan_memset (rgn_store_commit A r2) spoff (Some de) = with_v1 A' Bst).
      { unfold contract_frame2, rgn_store_commit, with_v1, A', set_rgn. cbn [v1 vs_rgn vs_live vs_divdef vs_memo contract2_K].
        rewrite <- EFR, MEMO. reflexivity. }
      rewrite EST.
      split; [left; reflexivity|]. split; [exact MS|]. split; [exact G3|]. split; [exact Q1|].
      split; [apply ext_refl|]. split.
      { unfold vs2_next, A', Bst. cbn [v1 with_v1]. rewrite F5, KS4. apply Pos.le_refl. }
      split; [exact (frame_mod_trans_same _ _ _ _ FMb2 FM3)|].
      eapply flags_step_then_same; [exact FST2|]. intros y Hy. split; [unfold A', with_v1; cbn [vs_rgn]; tauto|].
      apply QM0. unfold in_flags_zone in Hy. rewrite EFS in Hy. cbv beta iota in Hy.
      unfold usp, JUNK, FS_FLAGS, FS_FRAMES in *. rewrite u_wordZ by (ltac2:(LK.k [@P0; @FS1; @APsf; @HMsp; @SPHI; @E4; @E5; @E11; @Hn; @HBr; @FS5; @FA1; @NB1; @NB2; @NB3; @DRANGE; @Hlen; @SB2; @KS4; @F5; @Hy]); lia). destruct APsf as [X|X]; unfold P1, E1 in *; (ltac2:(LK.k [@X; @E4; @E5; @E11; @USP; @Hn; @HBr; @FS5; @NB1; @NB2; @NB3; @Hlen; @SB2; @KS4; @F5; @Hy]); lia).
    - (* [comment removed for export] *)
      destruct (range_check_v1_inv A de ne rr RC) as (off & lo & hi & -> & Esr & Hab & Hsa & Hsw).
      destruct (c_memset (p1 P) (v1 A)) as [A1' v| |m] eqn:CM; cbn [lift_cresA of_ca ca_ok1] in HC; try discriminate.
      injection HC as <-.
      unfold c_memset, getA in CM. unfold get_reg2 in En. rewrite En, Ene in CM. cbn [lin_of] in CM. rewrite Ede in CM.
      unfold P1 in Esr. rewrite Esr in CM.
      destruct (is_zero_val (v1 A) (get_reg (v1 A) A1r)) eqn:Ez; [|discriminate]. cbn [negb] in CM.
      destruct (stack_dst SEGS P1 E1 (zpatch P E mem0 mem) PO (v1 A) nu regs mem de ne off lo hi HG1 ltac:(lia) Esr)
        as (Ed & H1 & H2 & H3 & H4 & Hd0 & Hdn & Hok & Hws).
      fold n in Ed, H2, Hdn, Hok. set (ov := eval nu off) in *. set (d := e_sp0 E1 + ov) in *.
      assert (R10 : getr regs 10%bv = wordZ d).
      { apply wordZ_eq_u. rewrite V10, Ed. apply zwrap_id. lia. }
      assert (R11 : getr regs 11%bv = wordZ 0).
      { pose proof (gamma_get_reg SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem 11%bv HG1) as [W11 _]. change (rz 11%bv) with A1r in W11.
        destruct (get_reg (v1 A) A1r) as [ce|] eqn:Ec; [|cbn in Ez; discriminate].
        apply wordZ_eq_u. apply (is_zero_val_sound mem0 (v1 A) nu (Some ce) (getr regs 11%bv) HL Ez). exact (proj2 W11). }
      pose proof (above_sp_sound A spoff lo hi Hsp Hab) as HAB.
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
      assert (SP0al : e_sp0 E1 = 8 * (e_sp0 E1 / 8)).
      { pose proof (Z.div_mod (e_sp0 E1) 8 ltac:(lia)). replace (e_sp0 E1 mod 8) with 0 in H; [lia|].
        unfold E1. rewrite <- (Z.mod_mod_divide (e_sp0 (ev1 E)) 16 8) by (exists 2; reflexivity). rewrite E1a. reflexivity. }
      (* [comment removed for export] *)
      unfold env_fs in HFS. destruct (vp_fs P) as [[flen fssl]|] eqn:EFS; [|exfalso; exact (FSnz eq_refl)].
      destruct HFS as (_ & FS1 & FS2 & FS3 & FS4 & _ & _ & APsf & APdf & APds & HMsp & HMd & _ & SPHI & _).
      clear APsf APdf APds HMd. unfold HIGH_MEM_BEG, HIGH_MEM_END in *.
      assert (DJ : n = 0 \/ usp <= d) by (destruct (Z.eq_dec n 0); [left; assumption|right; unfold d, usp; lia]). clear HAB.
      (* [comment removed for export] *)
      assert (GR : 0 < n -> forall g, lo / 8 <= g <= (hi - 1) / 8 ->
        exists k : byte, mem (wordZ (SBz + e_sp0 E1 / 8 + g)) = Some k
                         /\ (bv_unsigned k = 0 \/ Z.min hi (8 * g + 8) - 8 * g <= bv_unsigned k < 8)).
      { intros Hn g Hg. destruct (range_granules_ok_sound sh lo hi g GRAN ltac:(lia) Hg) as (b & SB & Hb).
        destruct (sh_byte_mem A nu regs mem sh g b HG2 Hsh ltac:(unfold is_shadow; rewrite Ksh; reflexivity) SB) as (k & Rk & Vk).
        rewrite RB in Rk. exists k. split; [|rewrite Vk; exact Hb].
        apply rdn1_mem; [|exact Rk]. unfold SBz.
        apply (arith_stack_shadow_addr (e_sp0 E1) (vp_frame P1) lo hi g); unfold P1, E1 in *; (ltac2:(LK.k [@HMsp; @E11; @BSP8; @P0; @E4; @E5; @H3; @H4; @Hn; @Hg; @SPHI]); lia). }
      assert (SHAD : 0 < n ->
        (forall g, d / 8 <= g < (d + n - 1) / 8 -> mem (wordZ (SBz + g)) = Some (Z_to_bv 8 0))
        /\ (exists b1 : byte, mem (wordZ (SBz + (d + n - 1) / 8)) = Some b1
                             /\ (bv_unsigned b1 = 0 \/ (d + n - 1) mod 8 < bv_unsigned b1 < 8))).
      { intros Hn. unfold d. rewrite SP0al. apply (shadow_access mem (e_sp0 E1 / 8) lo hi ov n (GR Hn)); lia. }
      (* [comment removed for export] *)
      assert (NUE8 : nuE E SP8 = e_sp0 E1 / 8).
      { unfold nuE, fix_val2. replace (fix_val (ev1 E) SP8) with (@None Z) by reflexivity. reflexivity. }
      assert (WRD : 0 < n -> forall q, (q = d \/ q = d + n - 1) ->
        exists w : word, rdn SEGS mem (wordZ ((SBz + q / 8) / 8 * 8)) 8 = Some (word_to_le_bytes 8 w)).
      { intros Hn q Hq.
        pose proof (Z.div_mod (SBz + q / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SBz + q / 8) 8 ltac:(lia)).
        assert (QB : lo / 8 <= q / 8 - e_sp0 E1 / 8 <= (hi - 1) / 8).
        { unfold d in Hq. rewrite SP0al in Hq. exact (arith_qb _ _ _ _ _ _ Hq H1 H2 Hn). }
        apply (word_readable A nu regs mem _ HG2); [| unfold SBz in *; (ltac2:(LK.k [@P0; @FS1; @HMsp; @E4; @E5; @E11; @K1; @K2; @USP; @BSP8; @SP0al; @DJ; @Hn; @Hq; @H; @H0; @QB]); lia) | ].
        - intros i Hi. apply (zone_has_sound A nu regs mem SP8 _ _ _ HG2 Hsw). rewrite SHOFF, NUE8. unfold SBz in *. (ltac2:(LK.k [@P0; @FS1; @HMsp; @E4; @E5; @E11; @K1; @K2; @USP; @H2; @H4; @Hd0; @BSP8; @SP0al; @DJ; @NUE8; @Hn; @Hq; @H; @H0; @QB; @Hi]); lia).
        - unfold SBz in *. pose proof (Z.div_mod q 8 ltac:(lia)). pose proof (Z.mod_pos_bound q 8 ltac:(lia)). unfold usp, E1, P1 in *. (ltac2:(LK.k [@P0; @FS1; @SPHI; @E4; @E5; @E11; @H2; @H4; @BSP8; @Hn; @Hq; @H; @H0; @H5; @H6]); lia). }
      (* [comment removed for export] *)
      destruct (RUN mem d 0 n usp regs ra (MCELLS_OK _ _ _ _ HG2) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (regs' & m' & MS & Q10 & Q2 & Q1 & QK & QM & QG).
      { intros Hn. apply band_ok_high; unfold HIGH_MEM_BEG, HIGH_MEM_END, d, usp, P1, E1 in *; lia. }
      { unfold SBz, usp, P1, E1 in *. lia. }
      { destruct DJ as [DJ0|DJ1]; [left; exact DJ0|right; left; exact DJ1]. }
      { intros Hn. unfold JUNK, SBz, d, usp. apply (arith_shd (e_sp0 E1) (vp_frame P1) spoff (e_sp0 E1 + ov + n - 1) SP0al);
          unfold P1, E1 in *; (ltac2:(LK.k [@HMsp; @E11; @BSP8; @SPHI; @E4; @E5; @K1; @H2; @H4; @DJ; @Hn]); lia). }
      { intros g Hn Hg. exact (proj1 (SHAD Hn) g Hg). }
      { intros Hn. exact (proj2 (SHAD Hn)). }
      { intros Hn. apply (WRD Hn d). left; reflexivity. }
      { intros Hn. apply (WRD Hn (d + n - 1)). right; reflexivity. }
      { intros j Hj. apply (MF (d + j)). unfold d, P1, E1 in *. lia. }
      { exact JOK. }
      { exact Hret. } { exact Hra. } { exact R2. } { exact R10. } { exact R11. } { exact R12. }
      (* [comment removed for export] *)
      set (A1b := set_slots (v1 A) (cm_kill (vs_slots (v1 A)) lo hi)) in *.
      assert (CASES : (A1' = A1b /\ v = Some de) \/
                      (lin_is_const off = true /\ lin_is_const ne = true /\ v = Some de /\
                       let o := lc off in let k := lc ne in let q := Z.to_nat (k / 8) in let r := Z.to_nat (k mod 8) in
                       let A2 := set_slots A1b (zero_slots1 (zero_slots8 (vs_slots A1b) o q) (o + 8 * Z.of_nat q) r) in
                       A1' = (if 0 <? k then add_nul (add_nul A2 o o) (o + k - 1) (o + k - 1) else A2))).
      { destruct (lin_is_const off && lin_is_const ne && (lc ne <=? MEMSET_TRACK_MAX)) eqn:Ec.
        - apply andb_prop in Ec as [Ec _]. apply andb_prop in Ec as [Ec1 Ec2]. right. injection CM as <- <-. auto.
        - left. injection CM as <- <-. auto. }
      assert (LG : lgamma A1' nu /\ vs_next A1' = vs_next (v1 A) /\ vs_regs A1' = vs_regs (v1 A) /\ vs_globs A1' = vs_globs (v1 A) /\
                   (forall x, In x (vs_slots A1') -> In x (cm_kill (vs_slots (v1 A)) lo hi) \/
                       exists o w, x = (o, (w, Some (lconst 0))) /\ ov <= o /\ o + w <= ov + n /\ 0 < w) /\
                   (forall f, In f (vs_nul A1') -> In f (vs_nul (v1 A)) \/ (0 < n /\ (f = (ov, ov) \/ f = (ov + n - 1, ov + n - 1))))).
      { destruct HL as (LS&LC&LM&LV&(B0&B1&B2&B3&B4&B5)).
        destruct CASES as [[-> _]|(Co&Cn&_&EA1)].
        - unfold A1b. split; [|cbn; repeat split; auto]. split; [exact LS|]. split; [exact LC|]. split; [exact LM|]. split; [exact LV|].
          split; [exact B0|]. split; [exact B1|]. split; [exact B2|]. split; [intros k w e Hin; apply cm_kill_sub in Hin; exact (B3 _ _ _ Hin)|]. split; [exact B4|exact B5].
        - pose proof (eval_is_const nu off Co) as Eo. pose proof (eval_is_const nu ne Cn) as Ek.
          assert (Eo' : lc off = ov) by (unfold ov; rewrite Eo; reflexivity). assert (Ek' : lc ne = n) by (unfold n; rewrite Ek; reflexivity).
          rewrite Eo', Ek' in EA1. cbn zeta in EA1.
          set (q := Z.to_nat (n / 8)) in EA1. set (r := Z.to_nat (n mod 8)) in EA1.
          set (sl := zero_slots1 (zero_slots8 (vs_slots A1b) ov q) (ov + 8 * Z.of_nat q) r) in EA1.
          set (A2 := set_slots A1b sl) in EA1.
          pose proof (Z.div_mod n 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Hmb.
          assert (Hq : 8 * Z.of_nat q <= n) by (unfold q; rewrite Z2Nat.id by (apply Z.div_pos; (ltac2:(LK.k [@E4; @E5; @E11; @Hn0; @Hn1; @BSP8; @P0; @FS1; @HMsp; @K1; @K2; @USP; @SP0al; @NUE8; @Hdm; @Hmb]); lia)); (ltac2:(LK.k [@E4; @E5; @E11; @Hn0; @Hn1; @BSP8; @P0; @FS1; @HMsp; @K1; @K2; @USP; @SP0al; @NUE8; @Hdm; @Hmb]); lia)).
          assert (Hr : 8 * Z.of_nat q + Z.of_nat r = n) by (unfold q, r; rewrite !Z2Nat.id by (try apply Z.div_pos; (ltac2:(LK.k [@E4; @E5; @E11; @Hn0; @Hn1; @BSP8; @Hq; @P0; @Hmb; @FS1; @HMsp; @K1; @K2; @USP; @SP0al; @NUE8; @Hdm]); lia)); (ltac2:(LK.k [@E4; @E5; @E11; @Hn0; @Hn1; @BSP8; @Hq; @P0; @Hmb; @FS1; @HMsp; @K1; @K2; @USP; @SP0al; @NUE8; @Hdm]); lia)).
          assert (SL : forall x, In x sl -> In x (cm_kill (vs_slots (v1 A)) lo hi) \/ exists o w, x = (o, (w, Some (lconst 0))) /\ ov <= o /\ o + w <= ov + n /\ 0 < w).
          { intros x Hx. unfold sl in Hx. apply zero_slots1_in in Hx as [Hx|[i [Hi ->]]].
            - apply zero_slots8_in in Hx as [Hx|[i [Hi ->]]]; [left; exact Hx|]. right. eexists _, _. split; [reflexivity|]. (ltac2:(LK.k [@E4; @E5; @E11; @BSP8; @Hr; @Hi]); lia).
            - right. eexists _, _. split; [reflexivity|]. (ltac2:(LK.k [@E4; @E5; @E11; @BSP8; @Hr; @Hi]); lia). }
          assert (EA2 : exists l2, A1' = set_nul A2 l2 /\ forall f, In f l2 -> In f (vs_nul (v1 A)) \/ (0 < n /\ (f = (ov, ov) \/ f = (ov + n - 1, ov + n - 1)))).
          { destruct (Z.ltb_spec 0 n).
            - destruct (add_nul_eq A2 ov ov) as [l1 [EN1 Hl1]].
              destruct (add_nul_eq (set_nul A2 l1) (ov + n - 1) (ov + n - 1)) as [l2 [EN2 Hl2]].
              exists l2. rewrite EA1, EN1, EN2. split; [reflexivity|]. intros f Hf.
              destruct (Hl2 f Hf) as [->|Hf1]; [right; auto|]. cbn in Hf1. destruct (Hl1 f Hf1) as [->|Hf0]; [right; auto|left; exact Hf0].
            - exists (vs_nul (v1 A)). rewrite EA1. split; [destruct (v1 A); reflexivity|]. intros f Hf; left; exact Hf. }
          destruct EA2 as [l2 [-> Hl]]. cbn. split; [|repeat split; auto].
          split; [exact LS|]. split; [exact LC|]. split; [exact LM|]. split; [exact LV|].
          split; [exact B0|]. split; [exact B1|]. split; [exact B2|]. split; [|split; [exact B4|exact B5]].
          intros k w e Hin. destruct (SL _ Hin) as [Hin'|[o [w' [X _]]]]; [apply cm_kill_sub in Hin'; exact (B3 _ _ _ Hin')|].
          injection X as X1 X2 X3. subst. apply lin_below_lconst. }
      destruct LG as (L1&N1&RG1&G1&SL1&NL1).
      assert (Hv : v = Some de) by (destruct CASES as [[_ X]|(_&_&X&_)]; exact X).
      clear CASES CM.
      (* [comment removed for export] *)
      set (m_b := wbytes mem (wordZ d) (zeros (Z.to_nat n))).
      assert (FMb : frame_mod mem m_b [(wordZ d, n)]).
      { unfold m_b. replace n with (Z.of_nat (length (zeros (Z.to_nat n)))) at 2 by (rewrite length_zeros; lia).
        apply frame_mod_wbytes. rewrite length_zeros, u_wordZ; lia. }
      assert (RD : rdn SEGS m_b (wordZ d) (Z.to_nat n) = Some (zeros (Z.to_nat n))).
      { unfold m_b. rewrite <- (length_zeros (Z.to_nat n)) at 2. apply rdn_wbytes_hit. rewrite length_zeros, u_wordZ; lia. }
      assert (RD1 : forall j, 0 <= j < n -> rdn SEGS m_b (wordZ (d + j)) 1 = Some [Z_to_bv 8 0]).
      { intros j Hj. unfold m_b. replace j with (Z.of_nat (Z.to_nat j)) by lia.
        rewrite (rdn_wbytes_byte SEGS mem d (zeros (Z.to_nat n)) (Z.to_nat j)); rewrite ?length_zeros; try (ltac2:(LK.k [@E4; @E5; @E11; @Hd0; @BSP8; @N1; @Hdn; @Hj]); lia).
        rewrite nth_zeros. reflexivity. }
      pose proof HG1 as (_&_&_&_&_&_&_&HRg&HSl&HGl&HN&HB1).
      destruct (gamma_call_post SEGS P1 E1 (zpatch P E mem0 mem) rom PO (v1 A) A1' nu nu regs regs mem m_b [(wordZ d, n)]
                  HG1 (ext_refl _ _) ltac:(rewrite N1; apply Pos.le_refl) L1) as [Gb _].
      { unfold gamma_regs. rewrite RG1. exact HRg. }
      { intros off' w' v' Hin. destruct (SL1 _ Hin) as [Hk|[o [w'' [X (Y1&Y2&Y3)]]]].
        + left. split; [eapply cm_kill_sub; exact Hk|]. pose proof (cm_kill_disjoint _ _ _ _ _ _ Hk) as D.
          destruct (HSl _ _ _ (cm_kill_sub _ _ _ _ Hk)) as [(Ra&Rb&Rc) _].
          intros x Hx. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite !u_wordZ by (unfold d, usp, P1, E1 in *; lia). unfold d, usp, P1, E1 in *. lia.
        + injection X as X1 X2 X3. subst off' w' v'. right. split; [unfold ov, n in *; lia|]. cbn [cell_holds].
          exists (zeros (Z.to_nat w'')). split.
          * replace (e_sp0 E1 + o) with (d + (o - ov)) by (unfold d; lia).
            pose proof (rdn_sub SEGS m_b (Z.to_nat n) (wordZ d) (zeros (Z.to_nat n)) (Z.to_nat (o - ov)) (Z.to_nat w'') RD ltac:(lia)) as X.
            rewrite sub_zeros in X by lia. unfold at_ in X. rewrite u_wordZ, Z2Nat.id in X by lia. exact X.
          * rewrite bytes_le_zeros, eval_lconst. reflexivity. }
      { intros a w' v' Hin. rewrite G1 in Hin. split; [exact Hin|]. destruct (HGl _ _ _ Hin) as [(Ra&Rb&Rc) _].
        intros x Hx. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite !u_wordZ by (unfold d, usp, P1, E1 in *; lia). unfold d, usp, P1, E1 in *. lia. }
      { intros mlo mhi Hin. destruct (NL1 _ Hin) as [Hold|[Hnp [Ef|Ef]]]; [|injection Ef as Ef1 Ef2; subst mlo mhi|injection Ef as Ef1 Ef2; subst mlo mhi].
        + destruct (HN _ _ Hold) as [z [b (Y1&Y2&Y3&Y4)]]. right.
          assert (UNCH : z < ov \/ ov + n <= z -> rdn SEGS m_b (wordZ (e_sp0 E1 + z)) 1 = Some [b]).
          { intros Hz. rewrite <- Y3. apply (rdn_unchanged SEGS mem0 rom mem m_b [(wordZ d, n)] (e_sp0 E1 + z) 1 (proj1 FMb)); [unfold P1, E1 in *; lia|unfold P1, E1 in *; lia|].
            intros x Hx. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite !u_wordZ by (unfold d, usp, P1, E1 in *; lia). unfold d, usp, P1, E1 in *. lia. }
          destruct (Z_lt_le_dec z ov) as [Hz|Hz]; [|destruct (Z_lt_le_dec z (ov + n)) as [Hz'|Hz']].
          * exists z, b. split; [exact Y1|]. split; [exact Y2|]. split; [apply UNCH; lia|exact Y4].
          * exists z, (Z_to_bv 8 0). split; [exact Y1|]. split; [exact Y2|]. split; [|reflexivity].
            replace (e_sp0 E1 + z) with (d + (z - ov)) by (unfold d; lia). apply RD1. lia.
          * exists z, b. split; [exact Y1|]. split; [exact Y2|]. split; [apply UNCH; lia|exact Y4].
        + right. exists ov, (Z_to_bv 8 0). split; [lia|]. split; [unfold ov, n in *; lia|]. split; [|reflexivity].
          replace (e_sp0 E1 + ov) with (d + 0) by (unfold d; lia). apply RD1. lia.
        + right. exists (ov + n - 1), (Z_to_bv 8 0). split; [lia|]. split; [unfold ov, n in *; lia|]. split; [|reflexivity].
          replace (e_sp0 E1 + (ov + n - 1)) with (d + (n - 1)) by (unfold d; lia). apply RD1. lia. }
      { exact FMb. }
      { apply (stack_R_ok SEGS P1 E1 (zpatch P E mem0 mem) PO ov lo hi n); auto; lia. }
      (* [comment removed for export] *)
      assert (QM0 : forall x : word, bv_unsigned x < usp - JUNK \/ usp <= bv_unsigned x -> m' x = m_b x).
      { intros x Hx. rewrite (QM x Hx). reflexivity. }
      assert (GRW : forall x, m_b x <> None -> m' x <> None).
      { intros x Hx. destruct (Z_lt_le_dec (bv_unsigned x) d) as [B1|B1]; [|destruct (Z_lt_le_dec (bv_unsigned x) (d + n)) as [B2|B2]].
        - apply QG. intros M0. apply Hx. unfold m_b. rewrite wbytes_outside; [exact M0| |]; rewrite ?length_zeros, ?u_wordZ by lia; unfold in_rng; rewrite ?u_wordZ by lia; lia.
        - rewrite QM0; [exact Hx|]. destruct DJ as [DJ0|DJ1]; [lia|right; lia].
        - apply QG. intros M0. apply Hx. unfold m_b. rewrite wbytes_outside; [exact M0| |]; rewrite ?length_zeros, ?u_wordZ by (ltac2:(LK.k [@E4; @E5; @E11; @Hn0; @Hn1; @USP; @H2; @H4; @Hd0; @Hdn; @BSP8; @N1; @B1; @B2]); lia); unfold in_rng; rewrite ?u_wordZ by (ltac2:(LK.k [@E4; @E5; @E11; @Hn0; @Hn1; @USP; @H2; @H4; @Hd0; @Hdn; @BSP8; @N1; @B1; @B2]); lia); (ltac2:(LK.k [@E4; @E5; @E11; @Hn0; @Hn1; @USP; @H2; @H4; @Hd0; @Hdn; @BSP8; @N1; @B1; @B2]); lia). }
      pose proof (gamma_junk SEGS P1 E1 (zpatch P E mem0 mem) PO A1' nu regs m_b m' spoff 2208 JUNK Gb QM0 GRW
                    ltac:(unfold JUNK; lia) K1 K2) as Gk.
      (* [comment removed for export] *)
      set (Bst := contract_frame C_memset (killK 2208 A1' spoff) spoff v).
      assert (EFR : frame_rule 2208 A1' spoff v = Bst) by (apply frame_rule_killK; lia).
      destruct (killK_shape 2208 A1' spoff) as (KS1 & KS2 & KS3 & KS4 & KS5 & KS6 & KS7 & KS8 & KS9).
      destruct (contract_frame_shape C_memset (killK 2208 A1' spoff) spoff v) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & FR).
      assert (HLB : lgamma Bst nu).
      { apply lgamma_contract_frame; [apply lgamma_killK; exact L1|]. rewrite Hv. cbn [vbelow]. rewrite KS4, N1. exact B10. }
      destruct (gamma_call_post SEGS P1 E1 (zpatch P E mem0 mem) rom PO (killK 2208 A1' spoff) Bst nu nu regs regs' m' m' []
                  Gk (ext_refl _ _) ltac:(unfold Bst; rewrite F5; apply Pos.le_refl) HLB) as [GB _].
      { eapply (gamma_regs_contract_frame SEGS P1 E1 (zpatch P E mem0 mem) C_memset (killK 2208 A1' spoff) (killK 2208 A1' spoff) spoff v nu nu regs regs');
          [right; pose proof Gk as (_&_&_&_&_&_&_&KRg&_&_&_&KBl); split; [exact KRg|destruct KBl as (_&_&KRB&_); exact KRB]
          |apply ext_refl|reflexivity|exact QK|].
        rewrite Hv. rewrite Q10, u_wordZ, Ed by lia. symmetry. apply zwrap_id. lia. }
      { intros off' w' v' Hin. left. unfold Bst in Hin. rewrite F1 in Hin. cbn in Hin. split; [exact Hin|]. intros x _. exact I. }
      { intros g w' v' Hin. unfold Bst in Hin. rewrite F2 in Hin. split; [exact Hin|]. intros x _. exact I. }
      { intros lo' hi' Hin. left. unfold Bst in Hin. destruct (F3 _ Hin) as [Hin' _]. split; [exact Hin'|]. intros x _. exact I. }
      { apply frame_mod_refl. }
      { intros x Hx. exfalso. apply Hx. exact I. }
      (* [comment removed for export] *)
      assert (LENz : Z.of_nat (length (zeros (Z.to_nat n))) = n) by (rewrite length_zeros; lia).
      assert (FMU : frame_mod mem m' (unit_regions P1 E1)).
      { split; [|exact QG]. intros a Ha.
        assert (NB : ~ (d <= bv_unsigned a < d + n)).
        { intros Hin. refine (proj1 (stack_R_ok SEGS P1 E1 (zpatch P E mem0 mem) PO ov lo hi n H3 H4 H1 H2 Hws HEV1 a _) Ha).
          cbn [outside]. unfold in_rng. rewrite u_wordZ by lia. unfold d in Hin. intros [X _]. apply X. lia. }
        assert (NJ : ~ (usp - JUNK <= bv_unsigned a < usp)).
        { intros Hin. refine (proj1 (stack_R_ok SEGS P1 E1 (zpatch P E mem0 mem) PO (spoff - JUNK) (spoff - 2208) spoff JUNK
                                   K1 K2 ltac:(unfold JUNK; lia) ltac:(unfold JUNK; lia) KW HEV1 a _) Ha).
          cbn [outside]. unfold in_rng. rewrite u_wordZ by (unfold usp, JUNK, P1, E1 in *; lia). unfold usp in Hin. intros [X _]. apply X. unfold JUNK in *. lia. }
        rewrite QM0 by (pose proof (bv_unsigned_in_range 64 a); lia). unfold m_b. apply wbytes_outside; [|rewrite length_zeros, u_wordZ by (ltac2:(LK.k [@E4; @E5; @E11; @USP; @H2; @H4; @Hd0; @Hdn; @BSP8; @N1; @KS4; @F5; @LENz]); lia); (ltac2:(LK.k [@E4; @E5; @E11; @USP; @H2; @H4; @Hd0; @Hdn; @BSP8; @N1; @KS4; @F5; @LENz]); lia)].
        unfold in_rng. rewrite u_wordZ, length_zeros, Z2Nat.id by (ltac2:(LK.k [@E4; @E5; @E11; @USP; @H2; @H4; @Hd0; @Hdn; @BSP8; @N1; @KS4; @F5; @LENz; @Hn0; @Hn1]); lia). lia. }
      destruct (gamma2_lift SEGS P E mem0 PO2 A Bst nu nu regs regs' mem m' HG2 GB (ext_refl _ _)
                  ltac:(unfold Bst; rewrite F5, KS4, N1; apply Pos.le_refl) FMU
                  ltac:(unfold globs_ok2, Bst; cbn [v1 with_v1]; rewrite F2, KS2, G1; exact GL2) ltac:(right; exact MEMO))
        as (G3 & FM3 & FST3).
      exists (with_v1 A A1'), v, regs', m', nu.
      replace (contract_frame2 C_asan_memset (with_v1 A A1') spoff v) with (with_v1 A Bst)
        by (unfold contract_frame2, with_v1; cbn [v1 vs_rgn vs_live vs_divdef contract2_K]; rewrite <- EFR; reflexivity).
      split; [left; reflexivity|]. split; [exact MS|]. split; [exact G3|]. split; [exact Q1|].
      split; [apply ext_refl|]. split.
      { unfold vs2_next, Bst. cbn [v1 with_v1]. rewrite F5, KS4, N1. apply Pos.le_refl. }
      split; [exact FM3|exact FST3].
  Qed.
End S.
