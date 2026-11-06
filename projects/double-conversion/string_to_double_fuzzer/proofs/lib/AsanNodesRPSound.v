(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgA.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare AgentLib.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsanNodesRP AsanRPUtil AsanPlanImages.   (* [comment removed for export] *)
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsanSmear.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Import AX2 AX2S AP APS APSX.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPW_1. Context {fx : PropExec.FPState}.


Definition cell8 (SEGS : list Segment) (m : word -> option byte) (a v : Z) : Prop :=
  rdn SEGS m (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 v)).

(* [comment removed for export] *)
Definition img_cell (SEGS : list Segment) (a v : Z) : Prop :=
  forall m, (forall i, a <= i < a + 8 -> m (Z_to_bv 64 i) = None) -> cell8 SEGS m a v.
Record rp_img (SEGS : list Segment) (T : RPN.rptab) : Prop := {
  ri_gsb : img_cell SEGS (RPN.rp_gsb T) (RPN.rp_csb T);
  ri_gm1 : img_cell SEGS (RPN.rp_gm1 T) (RPN.rp_cm1 T);
  ri_gm2 : img_cell SEGS (RPN.rp_gm2 T) (RPN.rp_cm2 T);
  ri_ghi : img_cell SEGS (RPN.rp_ghi T) (RPN.rp_chi T);
  ri_cm1 : img_cell SEGS (RPN.rp_cm1 T) 0;
  ri_cm2 : img_cell SEGS (RPN.rp_cm2 T) 0
}.

(* [comment removed for export] *)
Definition rp_spec (SEGS : list Segment) (T : RPN.rptab) : Prop :=
  forall mem (beg n usp : Z) (regs : bvmap 5 word) (ra : word),
    16 <= n <= 2 ^ 40 -> 0 <= beg ->
    (beg + n <= RPN.kLowEnd \/ (RPN.kHighBeg <= beg /\ beg + n <= RPN.kHighEnd)) ->
    80 <= usp < 2 ^ 64 ->
    RPN.SB + (beg + n - 1) / 8 < usp - 72 ->
    (forall g, beg / 8 <= g < (beg + n - 1) / 8 -> mem (Z_to_bv 64 (RPN.SB + g)) = Some (Z_to_bv 8 0)) ->
    forall b1 : byte, mem (Z_to_bv 64 (RPN.SB + (beg + n - 1) / 8)) = Some b1 ->
    (bv_unsigned b1 = 0 \/ (beg + n - 1) mod 8 < bv_unsigned b1 < 8) ->
    (forall a, usp - 72 <= a < usp -> store_ok SEGS mem (Z_to_bv 64 a) 1 = true) ->
    cell8 SEGS mem (RPN.rp_gsb T) (RPN.rp_csb T) -> cell8 SEGS mem (RPN.rp_csb T) RPN.SB ->
    cell8 SEGS mem (RPN.rp_gm1 T) (RPN.rp_cm1 T) -> cell8 SEGS mem (RPN.rp_cm1 T) 0 ->
    cell8 SEGS mem (RPN.rp_gm2 T) (RPN.rp_cm2 T) -> cell8 SEGS mem (RPN.rp_cm2 T) 0 ->
    cell8 SEGS mem (RPN.rp_ghi T) (RPN.rp_chi T) -> cell8 SEGS mem (RPN.rp_chi T) RPN.kHighEnd ->
    ret_ok ra -> getr regs 1%bv = ra -> getr regs 2%bv = Z_to_bv 64 usp ->
    getr regs 10%bv = Z_to_bv 64 beg -> getr regs 11%bv = Z_to_bv 64 n ->
    exists regs' mem',
      msteps SEGS (mkst regs (Z_to_bv 64 (RPN.rp_entry T)) mem (seg_rom SEGS)) (mkst regs' ra mem' (seg_rom SEGS))
      /\ kept_ok regs regs' /\ getr regs' 10%bv = Z_to_bv 64 0
      /\ (forall x : word, bv_unsigned x < usp - 72 \/ usp <= bv_unsigned x -> mem' x = mem x)
      /\ mem_grows mem mem'.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn_img : forall SEGS n m (a : Z),
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, a <= i < a + Z.of_nat n -> m (Z_to_bv 64 i) = None) ->
  rdn SEGS m (Z_to_bv 64 a) n = rdn SEGS (fun _ => None) (Z_to_bv 64 a) n.
Proof.
  intros SEGS n. induction n as [|n IH]; intros m a Ha Hn Hm; [reflexivity|].
  cbn [rdn]. rewrite (Hm a) by lia.
  rewrite zbv_add1. rewrite (IH m (a + 1)); [reflexivity | lia | lia |].
  intros i Hi. apply Hm. lia.
Qed.

(* [comment removed for export] *)
Lemma map_unsigned_inj : forall (x y : list byte), map bv_unsigned x = map bv_unsigned y -> x = y.
Proof.
  induction x as [|a x IH]; intros [|b y] H; cbn in H; try discriminate; [reflexivity|].
  injection H as Hab Hxy. f_equal; [apply bv_eq; exact Hab | apply IH; exact Hxy].
Qed.
Lemma obytes_eq_of_unsigned : forall (x y : option (list byte)),
  option_map (map bv_unsigned) x = option_map (map bv_unsigned) y -> x = y.
Proof.
  intros [x|] [y|] H; cbn in H; try discriminate; [|reflexivity].
  injection H as H. f_equal. apply map_unsigned_inj. exact H.
Qed.
End FPW_1.

Ltac img_cell_vm :=
  intros m Hm; unfold cell8; rewrite (rdn_img _ 8 m) by (first [lia | intros i Hi; apply Hm; lia]);
  apply obytes_eq_of_unsigned; vm_compute; reflexivity.
Section FPW_2. Context {fx : PropExec.FPState}.





(* [comment removed for export] *)
Definition rc_spec (SEGS : list Segment) (T : RPN.rptab) : Prop :=
  forall mem (rom : word -> option byte) (buf res : Z) (regs : bvmap 5 word),
    1 <= res <= 64 -> 0 <= buf -> buf + 64 < 2 ^ 64 ->
    cell8 SEGS mem (RPN.rp_gsb T) (RPN.rp_csb T) -> cell8 SEGS mem (RPN.rp_csb T) RPN.SB ->
    (forall j, 0 <= j < 16 -> mem (Z_to_bv 64 ((RPN.SB + buf / 8) / 8 * 8 + j)) = Some (Z_to_bv 8 0)) ->
    getr regs 9%bv = Z_to_bv 64 buf -> getr regs 10%bv = Z_to_bv 64 res ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 (RPN.rc_entry T)) mem rom) (mkst regs' (Z_to_bv 64 (RPN.rc_exit T)) mem rom)
      /\ getr regs' 11%bv = Z_to_bv 64 (RPN.SB + buf / 8)
      /\ getr regs' 12%bv = Z_to_bv 64 (RPN.SB + (buf + res - 1) / 8)
      /\ getr regs' 13%bv = Z_to_bv 64 (buf + res - 1)
      /\ getr regs' 14%bv = Z_to_bv 64 0 /\ getr regs' 15%bv = Z_to_bv 64 0
      /\ getr regs' 20%bv = v_addi (v_addi (getr regs 8%bv) (-2048)) (-72)
      /\ (forall r, r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 20%bv -> getr regs' r = getr regs r).


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sound.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Hypothesis SEGS_wx : AsanAcct.wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_okP A.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable LINV : (word -> option byte) -> Prop.   (* [comment removed for export] *)
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis nx0_ge : APS.nx0_ok nx0.   (* [comment removed for export] *)
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis LINV_frame : forall M M' : word -> option byte, (forall a : word, in_lfp A (bv_unsigned a) = true -> M' a = M a) -> LINV M -> LINV M'.
Hypothesis LFP_hull : forall z, in_lfp A z = true -> img_lo A <= z < img_hi A.
Variable FS0 : Fs.Fs.
Variable T : RPN.rptab.
Hypothesis IMG_below_SB : img_hi A <= RPN.SB.   (* [comment removed for export] *)
Hypothesis IMG : rp_img SEGS T.
Hypothesis SPEC : rp_spec SEGS T.
Hypothesis RSPEC : rc_spec SEGS T.

Lemma u_spw_sub72 : forall (spw : word), 72 <= bv_unsigned spw ->
  bv_unsigned (Sem.alu64 ALU_ADD spw (Z_to_bv 64 (-72))) = bv_unsigned spw - 72.
Proof.
  intros spw Hs. pose proof (u64_range spw). rewrite alu_add. unfold v_add.
  rewrite (u_lit64 (-72)). unfold two64.
  change ((-72) mod 2 ^ 64) with (2 ^ 64 - 72).
  replace (bv_unsigned spw + (2 ^ 64 - 72)) with ((bv_unsigned spw - 72) + 1 * 2 ^ 64) by lia.
  rewrite u_lit64. unfold two64. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma srl3_div8 : forall (x y : word), bv_unsigned y mod 64 = 3 ->
  Sem.alu64 ALU_SRL x y = Z_to_bv 64 (bv_unsigned x / 8).
Proof.
  intros x y Hy. rewrite alu_srl. unfold v_srl. rewrite Hy. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

#[local] Notation M_of E cs model FULL := (Mr A argH E cs model FULL).

(* [comment removed for export] *)
Lemma lit_cell_sound : forall E M k cell v,
  know_ok SEGS E M k -> 0 <= cell -> RPN.lit_cell SEGS k cell v = true -> cell8 SEGS M cell v.
Proof.
  intros E M k cell v HK Hc H. unfold RPN.lit_cell in H. apply andb_prop in H as [Hfl H].
  destruct (know_lookup SEGS k (ELit 0) cell 8 false [] []) as [e sc hs|sc hs|] eqn:HL; try discriminate.
  destruct sc; [|discriminate].
  destruct (erange k e) as [[lo hi]|] eqn:Her; [|discriminate].
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst lo hi.
  pose proof (erange_sound SEGS E M k e v v HK Her) as Hv.
  destruct (flat_x_sound SEGS E M k (ELit 0) cell (ELit 8) HK Hfl) as (Clo & Chi & _).
  assert (HCst : estart E (SA (ELit 0) cell) = cell).
  { unfold estart; cbn [a_base a_off edenot]. rewrite u64_lit by lia. lia. }
  destruct (lookup_piece SEGS E M k (ELit 0) cell 8 e hs HK ltac:(lia) HL ltac:(unfold flat; rewrite HCst; rewrite HCst in Chi; cbn [edenot] in Chi; rewrite u64_lit in Chi by lia; lia))
    as (bs & Hrd & Hlen & Hbs).
  rewrite HCst in Hrd. unfold cell8. rewrite Hrd, <- Hbs. do 2 f_equal.
  rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E e)). f_equal. lia.
Qed.

Lemma img8_sound : forall E M k a v,
  know_ok SEGS E M k -> RPN.img8 k a = true -> img_cell SEGS a v -> cell8 SEGS M a v.
Proof.
  intros E M k a v HK H Himg. apply Himg. intros i Hi. exact (img_cov_sound SEGS E M k a (a + 8) HK H i Hi).
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma u_mkSrl3 : forall E M k e, know_ok SEGS E M k ->
  bv_unsigned (edenot E (mkSrl k e 3)) = bv_unsigned (edenot E e) / 8.
Proof.
  intros E M k e HK. pose proof (u64_range (edenot E e)) as Hr.
  rewrite (mkSrl_denot SEGS E M k e 3 (Z_to_bv 64 3) HK ltac:(rewrite u64_lit by lia; reflexivity)).
  rewrite srl3_div8 by (rewrite u64_lit by lia; reflexivity). apply u64_lit. lia.
Qed.

Lemma u_eadd : forall E a b,
  bv_unsigned (edenot E (mkAlu ALU_ADD a b)) = (bv_unsigned (edenot E a) + bv_unsigned (edenot E b)) mod 2 ^ 64.
Proof. intros E a b. rewrite mkAlu_denot, alu_add. unfold v_add. rewrite u_lit64. reflexivity. Qed.

Lemma u_eand7 : forall E e, bv_unsigned (edenot E (mkAlu ALU_AND e (ELit 7))) = bv_unsigned (edenot E e) mod 8.
Proof.
  intros E e. rewrite mkAlu_denot, alu_and. unfold v_and. cbn [edenot]. rewrite (u64_lit 7) by lia.
  change 7 with (Z.ones 3). rewrite Z.land_ones by lia. pose proof (u64_range (edenot E e)).
  apply u64_lit. change (2 ^ 3) with 8. lia.
Qed.

(* [comment removed for export] *)
Lemma split_lit_estart : forall E e b k o m,
  split_lit e = (b, k) -> flat E (SA b o) m -> 0 < m ->
  0 <= bv_unsigned (edenot E e) + (o - k) < 2 ^ 64 ->
  estart E (SA b o) = bv_unsigned (edenot E e) + (o - k).
Proof.
  intros E e b k o m Hs Hfl Hm Hr.
  pose proof (w_split_lit_denot E e b k Hs) as He.
  apply (f_equal bv_unsigned) in He. rewrite u_lit64 in He. unfold two64 in He.
  unfold flat, estart in *. cbn [a_base a_off] in *.
  set (X := bv_unsigned (edenot E b) + k) in *.
  pose proof (Z.div_mod X (2 ^ 64) ltac:(lia)) as Hdm.
  pose proof (u64_range (edenot E e)) as Hue. nia.
Qed.
Lemma split_lit_estart' : forall E e b k o,
  split_lit e = (b, k) -> 0 <= estart E (SA b o) <= 2 ^ 64 ->
  0 < bv_unsigned (edenot E e) + (o - k) < 2 ^ 64 ->
  estart E (SA b o) = bv_unsigned (edenot E e) + (o - k).
Proof.
  intros E e b k o Hs Hfl Hr.
  pose proof (w_split_lit_denot E e b k Hs) as He.
  apply (f_equal bv_unsigned) in He. rewrite u_lit64 in He. unfold two64 in He.
  unfold estart in *. cbn [a_base a_off] in *.
  set (X := bv_unsigned (edenot E b) + k) in *.
  pose proof (Z.div_mod X (2 ^ 64) ltac:(lia)) as Hdm.
  pose proof (u64_range (edenot E e)) as Hue. nia.
Qed.

(* [comment removed for export] *)
Lemma split_beg_sound : forall E M k bege bb bk,
  know_ok SEGS E M k -> split_lit bege = (bb, bk) -> flat_x k bb bk (ELit 1) = true ->
  bv_unsigned (edenot E bege) = bv_unsigned (edenot E bb) + bk.
Proof.
  intros E M k bege bb bk HK Hs Hfl.
  destruct (flat_x_sound SEGS E M k bb bk (ELit 1) HK Hfl) as (B0 & B1 & _).
  change (bv_unsigned (edenot E (ELit 1))) with (bv_unsigned (Z_to_bv 64 1)) in B1. rewrite u64_lit in B1 by lia.
  pose proof (w_split_lit_denot E bege bb bk Hs) as He. rewrite He.
  unfold estart in B0, B1. cbn [a_base a_off] in B0, B1. apply u64_lit. lia.
Qed.

Lemma v_add_zbv_mod' : forall a b, v_add (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b. unfold v_add. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite <- Z.add_mod by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma shsplit_sound : forall E M k bb bk hb hk o len,
  know_ok SEGS E M k -> 3 <= ealign k bb -> RPN.shsplit k bb bk = (hb, hk) ->
  flat_x k hb o (ELit len) = true -> 0 < len < 2 ^ 62 -> o <= hk < o + len ->
  0 <= bv_unsigned (edenot E bb) + bk < 2 ^ 64 ->
  exists q, bv_unsigned (edenot E bb) = 8 * q
    /\ estart E (SA hb hk) = RPN.SB + q + bk / 8
    /\ 0 <= estart E (SA hb o) /\ estart E (SA hb o) + len <= 2 ^ 64.
Proof.
  intros E M k bb bk hb hk o len HK Hal Hsh Hfl Hlen Ho Hbeg. unfold RPN.shsplit in Hsh.
  destruct (ealign_sound SEGS E M k bb HK) as [Hea1 Hea2].
  set (bbu := bv_unsigned (edenot E bb)) in *.
  assert (Hal8 : exists q, bbu = 8 * q).
  { destruct Hea2 as [q Hq8]. exists (q * 2 ^ (ealign k bb - 3)). fold bbu in Hq8. rewrite Hq8.
    replace (ealign k bb) with ((ealign k bb - 3) + 3) at 1 by lia.
    rewrite Z.pow_add_r by lia. change (2 ^ 3) with 8. lia. }
  destruct Hal8 as [q Hq8]. exists q. split; [exact Hq8|].
  pose proof (u64_range (edenot E bb)) as Ubb. fold bbu in Ubb.
  destruct (flat_x_sound SEGS E M k hb o (ELit len) HK Hfl) as (F0 & F1 & _).
  change (bv_unsigned (edenot E (ELit len))) with (bv_unsigned (Z_to_bv 64 len)) in F1. rewrite u64_lit in F1 by lia.
  pose proof (w_split_lit_denot E _ hb hk Hsh) as Hsa.
  unfold eadd in Hsa. rewrite mkAlu_denot in Hsa.
  rewrite (mkSrl_denot SEGS E M k bb 3 (Z_to_bv 64 3) HK ltac:(rewrite u64_lit by lia; reflexivity)) in Hsa.
  rewrite (srl3_div8 (edenot E bb) (Z_to_bv 64 3)) in Hsa by (rewrite u64_lit by lia; reflexivity). fold bbu in Hsa.
  cbn [edenot] in Hsa. rewrite alu_add, v_add_zbv_mod' in Hsa.
  assert (Hdiv4 : bbu / 8 = q) by (rewrite Hq8, Z.mul_comm; apply Z.div_mul; lia).
  rewrite Hdiv4 in Hsa.
  assert (Hdiv1 : (bbu + bk) / 8 = q + bk / 8).
  { rewrite Hq8. rewrite Z.mul_comm, Z.div_add_l by lia. reflexivity. }
  assert (Hr1 : 0 <= (bbu + bk) / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  unfold RPN.SB in *. unfold estart in *. cbn [a_base a_off] in *.
  replace (2147450880 + bk / 8 + q) with (2147450880 + (bbu + bk) / 8) in Hsa by lia.
  pose proof (u64_range (edenot E hb)) as Uhb.
  apply (f_equal bv_unsigned) in Hsa. rewrite (u64_lit (2147450880 + (bbu + bk) / 8)) in Hsa by lia.
  rewrite u64_lit in Hsa by lia. lia.
Qed.


(* [comment removed for export] *)
Lemma lit_shadow_zero_sound : forall E M k bb bk len hb hk,
  know_ok SEGS E M k -> RPN.lit_shadow_zero k bb bk len = true -> RPN.shsplit k bb bk = (hb, hk) -> 0 < len < 2 ^ 61 ->
  let B := bv_unsigned (edenot E bb) + bk in
  0 <= B /\ B + 1 <= 2 ^ 64 /\
  forall g, B / 8 <= g <= (B + len - 1) / 8 -> M (Z_to_bv 64 (RPN.SB + g)) = Some (Z_to_bv 8 0).
Proof.
  intros E M k bb bk len hb hk HK H Hsh Hlen.
  unfold RPN.lit_shadow_zero in H. rewrite Hsh in H.
  apply andb_prop in H as [H Hkz]. apply andb_prop in H as [H Hflh]. apply andb_prop in H as [Hal Hflb]. apply Z.leb_le in Hal.
  destruct (flat_x_sound SEGS E M k bb bk (ELit 1) HK Hflb) as (B0 & B1 & _).
  change (bv_unsigned (edenot E (ELit 1))) with (bv_unsigned (Z_to_bv 64 1)) in B1. rewrite u64_lit in B1 by lia.
  unfold estart in B0, B1. cbn [a_base a_off] in B0, B1.
  cbn zeta. split; [lia|]. split; [lia|].
  set (L := RPN.ngran bk len) in *.
  assert (HL : 1 <= L < 2 ^ 62).
  { unfold L, RPN.ngran. pose proof (Z.div_le_mono bk (bk + len - 1) 8 ltac:(lia) ltac:(lia)). lia. }
  destruct (shsplit_sound E M k bb bk hb hk hk L HK Hal Hsh Hflh ltac:(lia) ltac:(lia) ltac:(lia)) as (q & Hq & HH & H0 & H1).
  destruct (kzero_x_sound SEGS E M k k hb hk (ELit L) HK HK Hkz) as (Zb & _ & _).
  change (elenZ E (ELit L)) with (bv_unsigned (Z_to_bv 64 L)) in Zb. rewrite u64_lit in Zb by lia.
  intros g Hg. rewrite Hq in Hg.
  replace (8 * q + bk) with (q * 8 + bk) in Hg by lia. replace (q * 8 + bk + len - 1) with (q * 8 + (bk + len - 1)) in Hg by lia.
  rewrite !Z.div_add_l in Hg by lia.
  replace (RPN.SB + g) with (estart E (SA hb hk) + (g - q - bk / 8)) by lia.
  apply Zb. unfold L, RPN.ngran. lia.
Qed.

(* [comment removed for export] *)
Lemma off_image_byte : forall M (a : Z) b, 0 <= a < 2 ^ 64 -> RPN.SB <= a ->
  rdn SEGS M (Z_to_bv 64 a) 1 = Some [b] -> M (Z_to_bv 64 a) = Some b.
Proof.
  intros M a b Ha Hsb Hrd. cbn [rdn] in Hrd. destruct (M (Z_to_bv 64 a)) as [b'|] eqn:Hb'.
  - cbn in Hrd. congruence.
  - exfalso. unfold seg_rom, memory_read in Hrd. rewrite u64_lit in Hrd by lia. change (Z.of_N 1) with 1 in Hrd.
    rewrite <- (u64_lit a) in Hrd by lia. rewrite (SEGS_in_hull (Z_to_bv 64 a)) in Hrd; [discriminate|].
    unfold in_hull. rewrite u64_lit by lia. pose proof IMG_below_SB as HO. apply andb_false_intro2. apply Z.ltb_ge. lia.
Qed.

(* [comment removed for export] *)
Lemma and7_of_sound : forall E M k m ne,
  know_ok SEGS E M k -> RPN.and7_of k m ne = true -> bv_unsigned (edenot E m) = bv_unsigned (edenot E ne) mod 8.
Proof.
  intros E M k m ne HK H. unfold RPN.and7_of in H.
  assert (U7 : forall x : word, bv_unsigned (alu64 ALU_AND x (Z_to_bv 64 7)) = bv_unsigned x mod 8).
  { intros x. pose proof (u64_range x) as Hx. rewrite alu_and. unfold v_and. rewrite (u64_lit 7) by lia.
    change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
    pose proof (Z.mod_pos_bound (bv_unsigned x) 8 ltac:(lia)). apply u64_lit. lia. }
  destruct (expr_eqb m (mkAnd k ne (ELit 7))) eqn:E1.
  - apply expr_eqb_eq in E1. subst m. rewrite (mkAnd_denot SEGS E M k _ _ HK). cbn [edenot]. apply U7.
  - destruct m as [ | | op ne' b | | | | | ]; try discriminate H. destruct op; try discriminate H.
    destruct b as [z | | | | | | | ]; try discriminate H.
    destruct (Z.eq_dec z 7) as [-> | Hz]; [| destruct z as [|p|p]; try discriminate H; destruct p as [p|p|]; try discriminate H;
        destruct p as [p|p|]; try discriminate H; destruct p as [p|p|]; try discriminate H; exfalso; apply Hz; reflexivity].
    destruct (lin_ge0 k [(ne', 0)] [(ne, 0)]) eqn:G1; [|discriminate].
    pose proof (lin_ge0_sound SEGS E M k _ _ HK G1) as L1. pose proof (lin_ge0_sound SEGS E M k _ _ HK H) as L2.
    cbn [xt_den] in L1, L2. cbn [edenot]. rewrite U7. f_equal. lia.
Qed.
Definition vval (n : Z) : Z := if Z.eqb (n mod 8) 0 then 250 else n mod 8.
Lemma vval_range : forall n, 0 <= vval n <= 250 /\ vval n <> 0.
Proof. intros n. unfold vval. pose proof (Z.mod_pos_bound n 8 ltac:(lia)). destruct (Z.eqb_spec (n mod 8) 0); lia. Qed.
Lemma vshape0_sound : forall E M k v ne,
  know_ok SEGS E M k -> RPN.vshape0 k v ne = true -> bv_unsigned (edenot E v) = vval (bv_unsigned (edenot E ne)).
Proof.
  intros E M k v ne HK H. unfold RPN.vshape0 in H.
  repeat lazymatch type of H with
    | (if expr_eqb _ _ then _ else _) = true => fail
    | (match ?x with _ => _ end) = true => destruct x; try discriminate H
    end.
  lazymatch type of H with (if expr_eqb ?a ?b then _ else _) = true => destruct (expr_eqb a b) eqn:He; [|discriminate H] end.
  apply expr_eqb_eq in He. subst.
  pose proof (and7_of_sound E M k _ ne HK H) as Hm.
  cbn [edenot]. rewrite u_add64, u_mul64, alu_sltu. unfold v_sltu, c_ltu, bv_ltu. rewrite Hm.
  rewrite (u64_lit 1), (u64_lit 250) by lia. unfold vval.
  pose proof (Z.mod_pos_bound (bv_unsigned (edenot E ne)) 8 ltac:(lia)) as Hr.
  destruct (Z.eqb_spec (bv_unsigned (edenot E ne) mod 8) 0) as [H0 | H0].
  - rewrite H0. cbn [Z.ltb Z.compare]. rewrite ?(u64_lit 1) by lia. reflexivity.
  - destruct (Z.ltb_spec (bv_unsigned (edenot E ne) mod 8) 1); [lia|].
    rewrite ?(u64_lit 0) by lia. rewrite ?Z.mul_0_r. change (0 mod 2 ^ 64) with 0. rewrite ?Z.add_0_r. apply Z.mod_small. lia.
Qed.
Lemma vshape_sound : forall E M k v ne,
  know_ok SEGS E M k -> RPN.vshape k v ne = true -> bv_unsigned (edenot E v) = vval (bv_unsigned (edenot E ne)).
Proof.
  intros E M k v ne HK H. unfold RPN.vshape in H.
  destruct (RPN.vshape0 k v ne) eqn:H0; [exact (vshape0_sound E M k v ne HK H0)|].
  destruct v as [ | | | | | | sx lo n v' | ]; try discriminate H. destruct sx; [discriminate H|].
  destruct lo as [|lo]; [|discriminate H]. destruct n as [|[|n]]; try discriminate H.
  pose proof (vshape0_sound E M k v' ne HK H) as H1. pose proof (vval_range (bv_unsigned (edenot E ne))).
  cbn [edenot]. rewrite u_ext_zx0_small; [exact H1|]. change (2 ^ (8 * Z.of_nat 1)) with 256. lia.
Qed.

(* [comment removed for export] *)
Lemma partial_val_sound : forall E M k v ne,
  know_ok SEGS E M k -> RPN.partial_val_ok k v ne = true ->
  bv_unsigned (edenot E ne) mod 8 <> 0 ->
  bv_unsigned (edenot E v) mod 256 = bv_unsigned (edenot E ne) mod 8.
Proof.
  intros E M k v ne HK H Hn8. pose proof (u64_range (edenot E ne)) as Un. set (n := bv_unsigned (edenot E ne)) in *.
  pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Hm8.
  assert (EXT : forall e, bv_unsigned (edenot E e) mod 256 = n mod 8 ->
                          bv_unsigned (edenot E (mkExt false 0 1 e)) mod 256 = n mod 8).
  { intros e He. rewrite mkExt_denot by lia. unfold ext_val, ext_Z. cbn [Z.of_nat Z.mul].
    rewrite Z.pow_0_r, Z.div_1_r. change (2 ^ 8) with 256. pose proof (u64_range (edenot E e)).
    pose proof (Z.mod_pos_bound (bv_unsigned (edenot E e)) 256 ltac:(lia)).
    rewrite u64_lit by lia. rewrite Z.mod_mod by lia. exact He. }
  assert (AND : bv_unsigned (edenot E (mkAlu ALU_AND ne (ELit 7))) mod 256 = n mod 8).
  { rewrite u_eand7. fold n. apply Z.mod_small. lia. }
  assert (KAND : bv_unsigned (edenot E (mkAnd k ne (ELit 7))) mod 256 = n mod 8).
  { rewrite (mkAnd_denot SEGS E M k ne (ELit 7) HK). rewrite alu_and. unfold v_and. cbn [edenot]. rewrite (u64_lit 7) by lia.
    change 7 with (Z.ones 3). rewrite Z.land_ones by lia. fold n. change (2 ^ 3) with 8.
    rewrite u64_lit by lia. apply Z.mod_small. lia. }
  assert (SELF : match erange k ne with Some (lo, hi) => ((0 <=? lo) && (hi <=? 7))%bool | None => false end = true ->
                 bv_unsigned (edenot E ne) mod 256 = n mod 8).
  { intros Hr. destruct (erange k ne) as [[lo hi]|] eqn:Her; [|discriminate]. apply andb_prop in Hr as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. pose proof (erange_sound SEGS E M k _ _ _ HK Her). fold n.
    rewrite (Z.mod_small n 8) by lia. apply Z.mod_small. lia. }
  unfold RPN.partial_val_ok in H.
  apply orb_prop in H. destruct H as [H|HV].
  2: { rewrite (vshape_sound E M k v ne HK HV). fold n. unfold vval. destruct (Z.eqb_spec (n mod 8) 0); [contradiction|]. apply Z.mod_small. lia. }
  repeat (apply orb_prop in H; destruct H as [H|H]);
    try (apply andb_prop in H as [H Hr]); try (apply expr_eqb_eq in H; subst v); auto.
Qed.

(* [comment removed for export] *)
Lemma sym_shadow_sound : forall E M k bege ne,
  know_ok SEGS E M k -> RPN.sym_shadow_ok SEGS k bege ne = true ->
  let beg := bv_unsigned (edenot E bege) in let n := bv_unsigned (edenot E ne) in
  beg mod 8 = 0
  /\ (forall g, 0 <= g < n / 8 -> M (Z_to_bv 64 (RPN.SB + beg / 8 + g)) = Some (Z_to_bv 8 0))
  /\ (n mod 8 <> 0 -> M (Z_to_bv 64 (RPN.SB + beg / 8 + n / 8)) = Some (Z_to_bv 8 (n mod 8))).
Proof.
  intros E M k bege ne HK G. cbn zeta.
  set (beg := bv_unsigned (edenot E bege)). set (n := bv_unsigned (edenot E ne)).
  pose proof (u64_range (edenot E bege)) as Ub. fold beg in Ub. pose proof (u64_range (edenot E ne)) as Un. fold n in Un.
  unfold RPN.sym_shadow_ok, RPN.SB in G.
  destruct (split_lit (mkAlu ALU_ADD (mkSrl k bege 3) (ELit 2147450880))) as [sb sk] eqn:Hss.
  set (ng := mkSrl k ne 3) in *.
  apply andb_prop in G as [G1 G2]. apply andb_prop in G1 as [Gal G1]. apply Z.leb_le in Gal.
  assert (Usbe : bv_unsigned (edenot E (mkAlu ALU_ADD (mkSrl k bege 3) (ELit 2147450880))) = beg / 8 + 2147450880).
  { pose proof (u_mkSrl3 E M k bege HK) as Hs3. fold beg in Hs3. rewrite u_eadd. rewrite Hs3.
    change (bv_unsigned (edenot E (ELit 2147450880))) with (bv_unsigned (Z_to_bv 64 2147450880)). rewrite u64_lit by lia.
    apply Z.mod_small. lia. }
  assert (Ung : elenZ E ng = n / 8) by (unfold elenZ, ng; rewrite (u_mkSrl3 E M k ne HK); reflexivity).
  (* [comment removed for export] *)
  assert (G0 : RPN.is00 (erange k ng) = true -> n / 8 = 0).
  { intros H0. unfold RPN.is00 in H0. destruct (erange k ng) as [[lo hi]|] eqn:Her; [|discriminate].
    destruct lo; try discriminate. destruct hi; try discriminate.
    pose proof (erange_sound SEGS E M k _ _ _ HK Her) as Hr. unfold elenZ in Ung. rewrite Ung in Hr. lia. }
  (* [comment removed for export] *)
  assert (ES : forall m, 0 <= estart E (SA sb sk) -> estart E (SA sb sk) + m <= 2 ^ 64 -> 0 <= m ->
               estart E (SA sb sk) = 2147450880 + beg / 8).
  { intros m F0 F1 Fm. pose proof (split_lit_estart' E _ sb sk sk Hss ltac:(lia) ltac:(rewrite Usbe; lia)) as X. rewrite Usbe in X. lia. }
  split.
  { destruct (ealign_sound SEGS E M k bege HK) as [He1 [q Hq]]. fold beg in Hq. rewrite Hq.
    replace (ealign k bege) with ((ealign k bege - 3) + 3) by lia.
    rewrite Z.pow_add_r by lia. change (2 ^ 3) with 8. rewrite Z.mul_assoc. apply Z_mod_mult. }
  (* [comment removed for export] *)
  assert (ZG : (RPN.is00 (erange k ng) = true /\ n / 8 = 0)
               \/ (estart E (SA sb sk) = 2147450880 + beg / 8
                   /\ forall i, 0 <= i < n / 8 -> M (Z_to_bv 64 (estart E (SA sb sk) + i)) = Some (Z_to_bv 8 0))).
  { destruct (RPN.is00 (erange k ng)) eqn:H0; [left; auto|]. cbn [orb] in G1.
    destruct (kzero_x_sound SEGS E M k k sb sk ng HK HK G1) as (Z0 & ZS0 & ZS1). rewrite Ung in Z0, ZS1.
    right. split; [apply (ES (n / 8)); lia | exact Z0]. }
  split.
  { intros g Hg. destruct ZG as [[_ Hn0]|[HS Z0]]; [lia|]. unfold RPN.SB. rewrite <- HS. apply Z0. exact Hg. }
  intros Hmod. unfold RPN.SB.
  apply orb_prop in G2 as [G2|G2].
  { exfalso. unfold RPN.is00 in G2. destruct (erange k (mkAlu ALU_AND ne (ELit 7))) as [[lo hi]|] eqn:Her; [|discriminate].
    destruct lo; try discriminate. destruct hi; try discriminate.
    pose proof (erange_sound SEGS E M k _ _ _ HK Her) as Hr. rewrite u_eand7 in Hr. fold n in Hr. lia. }
  apply andb_prop in G2 as [Gfl G2].
  set (pb := if RPN.is00 (erange k ng) then sb else mkAlu ALU_ADD sb ng) in *.
  destruct (know_lookup SEGS k pb sk 1 false [] []) as [v scs hs|scs hs|] eqn:HL; try discriminate.
  destruct scs; [|discriminate].
  destruct (flat_x_sound SEGS E M k pb sk (ELit 1) HK Gfl) as (Q0 & Q1 & _).
  change (bv_unsigned (edenot E (ELit 1))) with (bv_unsigned (Z_to_bv 64 1)) in Q1. rewrite (u64_lit 1) in Q1 by lia.
  set (P := estart E (SA pb sk)) in *.
  (* [comment removed for export] *)
  assert (HP : P = 2147450880 + beg / 8 + n / 8).
  { unfold P, pb in *. destruct (RPN.is00 (erange k ng)) eqn:H0.
    - rewrite (G0 eq_refl). rewrite (ES 1); [lia | exact Q0 | exact Q1 | lia].
    - destruct ZG as [[X _]|[HS _]]; [discriminate|].
      unfold estart. cbn [a_base a_off]. rewrite u_eadd. fold ng in Ung. unfold elenZ in Ung. rewrite Ung.
      unfold estart in HS. cbn [a_base a_off] in HS. pose proof (u64_range (edenot E sb)) as Usb.
      unfold estart in Q0, Q1. cbn [a_base a_off] in Q0, Q1. rewrite u_eadd in Q0, Q1. rewrite Ung in Q0, Q1. lia. }
  destruct (lookup_piece SEGS E M k pb sk 1 v hs HK ltac:(lia) HL ltac:(unfold flat; fold P; lia)) as (bs & Hrd & Hlen & Hbs).
  fold P in Hrd. rewrite HP in Hrd.
  destruct bs as [|b [|]]; try discriminate.
  pose proof (partial_val_sound E M k v ne HK G2 Hmod) as Hv. fold n in Hv.
  apply (off_image_byte M (2147450880 + beg / 8 + n / 8) b ltac:(lia) ltac:(unfold RPN.SB; lia)) in Hrd. rewrite Hrd. f_equal.
  unfold word_to_le_bytes in Hbs. cbn [Z_to_le_bytes] in Hbs. injection Hbs as <-.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Hv. symmetry. apply Z.mod_small.
  pose proof (Z.mod_pos_bound n 8 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma enc_ok_sound : forall E M k bege ne nhi eb ek elen,
  know_ok SEGS E M k -> RPN.enc_ok k bege ne nhi eb ek elen = true ->
  let beg := bv_unsigned (edenot E bege) in let n := bv_unsigned (edenot E ne) in let B0 := bv_unsigned (edenot E eb) + ek in
  1 <= n <= nhi ->
  B0 <= beg /\ beg + n <= B0 + elen /\ 0 <= B0 /\ B0 + elen <= 2 ^ 64 /\ elen <= 2 ^ 40.
Proof.
  intros E M k bege ne nhi eb ek elen HK H. cbn zeta. intros Hn.
  unfold RPN.enc_ok in H.
  destruct (erange k (mkAlu ALU_SUB bege (eaddz eb ek))) as [[dlo dhi]|] eqn:Her; [|discriminate].
  apply andb_prop in H as [H Hj]. apply andb_prop in H as [H Hfl]. apply andb_prop in H as [H He40]. apply andb_prop in H as [Hd0 Hel0].
  apply Z.leb_le in Hd0. apply Z.leb_le in He40. apply Z.leb_le in Hel0.
  destruct (flat_x_sound SEGS E M k eb ek (ELit elen) HK Hfl) as (F0 & F1 & F2).
  change (bv_unsigned (edenot E (ELit elen))) with (bv_unsigned (Z_to_bv 64 elen)) in F1, F2.
  pose proof (erange_sound SEGS E M k _ _ _ HK Her) as Hr.
  assert (Hel : bv_unsigned (Z_to_bv 64 elen) = elen) by (apply u64_lit; lia).
  rewrite Hel in F1, F2. unfold estart in F0, F1. cbn [a_base a_off] in F0, F1.
  rewrite mkAlu_denot, alu_sub in Hr. unfold v_sub in Hr. rewrite u_lit64 in Hr. unfold two64 in Hr.
  unfold eaddz in Hr. rewrite (u_eadd E eb (ELit ek)) in Hr. change (bv_unsigned (edenot E (ELit ek))) with (bv_unsigned (Z_to_bv 64 ek)) in Hr.
  rewrite (u_lit64 ek) in Hr. unfold two64 in Hr.
  pose proof (u64_range (edenot E bege)) as Ub. pose proof (u64_range (edenot E eb)) as Ueb. pose proof (u64_range (edenot E ne)) as Un.
  set (beg := bv_unsigned (edenot E bege)) in *. set (ebu := bv_unsigned (edenot E eb)) in *. set (n := bv_unsigned (edenot E ne)) in *.
  assert (E1 : (ebu + ek mod 2 ^ 64) mod 2 ^ 64 = ebu + ek).
  { rewrite Z.add_mod_idemp_r by lia. apply Z.mod_small. lia. }
  rewrite E1 in Hr.
  pose proof (Z.div_mod (beg - (ebu + ek)) (2 ^ 64) ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (beg - (ebu + ek)) (2 ^ 64) ltac:(lia)) as Hmb.
  (* [comment removed for export] *)
  assert (Hq : (beg - (ebu + ek)) / 2 ^ 64 = 0 \/ (beg - (ebu + ek)) / 2 ^ 64 <= -1) by lia.
  assert (HEND : ebu + ek <= beg /\ beg + n <= ebu + ek + elen).
  { apply orb_prop in Hj. destruct Hj as [Hdn|Hj].
    - apply Z.leb_le in Hdn. destruct Hq; nia.
    - apply andb_prop in Hj as [Hnw Hj]. apply Z.ltb_lt in Hnw. unfold two64 in Hnw.
      destruct (erange k (mkAlu ALU_ADD (mkAlu ALU_SUB bege (eaddz eb ek)) ne)) as [[tlo thi]|] eqn:Het; [|discriminate].
      apply Z.leb_le in Hj.
      pose proof (erange_sound SEGS E M k _ _ _ HK Het) as Ht.
      rewrite mkAlu_denot, alu_add in Ht. unfold v_add in Ht. rewrite u_lit64 in Ht. unfold two64 in Ht.
      rewrite mkAlu_denot, alu_sub in Ht. unfold v_sub in Ht. rewrite u_lit64 in Ht. unfold two64 in Ht.
      unfold eaddz in Ht. rewrite (u_eadd E eb (ELit ek)) in Ht. change (bv_unsigned (edenot E (ELit ek))) with (bv_unsigned (Z_to_bv 64 ek)) in Ht.
      rewrite (u_lit64 ek) in Ht. unfold two64 in Ht. fold beg ebu n in Ht. rewrite E1 in Ht.
      pose proof (Z.div_mod ((beg - (ebu + ek)) mod 2 ^ 64 + n) (2 ^ 64) ltac:(lia)) as Hdm2.
      pose proof (Z.mod_pos_bound ((beg - (ebu + ek)) mod 2 ^ 64 + n) (2 ^ 64) ltac:(lia)) as Hmb2.
      assert (Hq2 : ((beg - (ebu + ek)) mod 2 ^ 64 + n) / 2 ^ 64 = 0 \/ ((beg - (ebu + ek)) mod 2 ^ 64 + n) / 2 ^ 64 >= 1) by lia.
      destruct Hq; destruct Hq2; nia. }
  destruct HEND; repeat split; lia.
Qed.

(* [comment removed for export] *)
Lemma ushadow_val : forall E M k bege sb sk len,
  know_ok SEGS E M k -> RPN.ushadow k bege = (sb, sk) -> flat_x k sb sk (ELit len) = true -> 0 < len < 2 ^ 62 ->
  estart E (SA sb sk) = RPN.SB + bv_unsigned (edenot E bege) / 8
  /\ 0 <= estart E (SA sb sk) /\ estart E (SA sb sk) + len <= 2 ^ 64.
Proof.
  intros E M k bege sb sk len HK Hu Hfl Hlen. unfold RPN.ushadow in Hu.
  destruct (flat_x_sound SEGS E M k sb sk (ELit len) HK Hfl) as (F0 & F1 & _).
  change (bv_unsigned (edenot E (ELit len))) with (bv_unsigned (Z_to_bv 64 len)) in F1. rewrite u64_lit in F1 by lia.
  pose proof (w_split_lit_denot E _ sb sk Hu) as Hsa.
  apply (f_equal bv_unsigned) in Hsa. rewrite u_eadd, (u_mkSrl3 E M k bege HK) in Hsa. cbn [edenot] in Hsa.
  pose proof (u64_range (edenot E bege)) as Ub. pose proof (u64_range (edenot E sb)) as Us.
  unfold RPN.SB in *. rewrite (u64_lit 2147450880) in Hsa by lia.
  rewrite Z.mod_small in Hsa by lia.
  unfold estart in *. cbn [a_base a_off] in *. rewrite u64_lit in Hsa by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma ushadow_zero_sound : forall E M k bege nhi,
  know_ok SEGS E M k -> RPN.ushadow_zero k bege nhi = true -> 1 <= nhi <= 2 ^ 40 ->
  let beg := bv_unsigned (edenot E bege) in
  forall g, beg / 8 <= g <= (beg + nhi - 1) / 8 -> M (Z_to_bv 64 (RPN.SB + g)) = Some (Z_to_bv 8 0).
Proof.
  intros E M k bege nhi HK H Hn. cbn zeta. unfold RPN.ushadow_zero in H.
  destruct (RPN.ushadow k bege) as [sb sk] eqn:Hu. apply andb_prop in H as [Hfl Hkz].
  assert (HG : 1 <= RPN.ugran nhi < 2 ^ 38) by (unfold RPN.ugran; lia).
  destruct (ushadow_val E M k bege sb sk (RPN.ugran nhi) HK Hu Hfl ltac:(lia)) as (S1 & S2 & S3).
  destruct (kzero_x_sound SEGS E M k k sb sk (ELit (RPN.ugran nhi)) HK HK Hkz) as (Zb & _ & _).
  change (elenZ E (ELit (RPN.ugran nhi))) with (bv_unsigned (Z_to_bv 64 (RPN.ugran nhi))) in Zb. rewrite u64_lit in Zb by lia.
  pose proof (u64_range (edenot E bege)) as Ub.
  intros g Hg. replace (RPN.SB + g) with (estart E (SA sb sk) + (g - bv_unsigned (edenot E bege) / 8)) by lia.
  apply Zb. unfold RPN.ugran in *. lia.
Qed.

(* [comment removed for export] *)
Lemma ushadow_val_x : forall E M k bege sb sk len,
  know_ok SEGS E M k -> RPN.ushadow k bege = (sb, sk) -> flat_x k sb sk len = true ->
  estart E (SA sb sk) = RPN.SB + bv_unsigned (edenot E bege) / 8
  /\ 0 <= estart E (SA sb sk) /\ estart E (SA sb sk) + elenZ E len <= 2 ^ 64 /\ 0 < elenZ E len.
Proof.
  intros E M k bege sb sk len HK Hu Hfl. unfold RPN.ushadow in Hu.
  destruct (flat_x_sound SEGS E M k sb sk len HK Hfl) as (F0 & F1 & F2).
  pose proof (w_split_lit_denot E _ sb sk Hu) as Hsa.
  apply (f_equal bv_unsigned) in Hsa. rewrite u_eadd, (u_mkSrl3 E M k bege HK) in Hsa. cbn [edenot] in Hsa.
  pose proof (u64_range (edenot E bege)) as Ub. pose proof (u64_range (edenot E sb)) as Us.
  unfold RPN.SB in *. rewrite (u64_lit 2147450880) in Hsa by lia.
  rewrite Z.mod_small in Hsa by lia.
  unfold estart, elenZ in *. cbn [a_base a_off] in *. rewrite u64_lit in Hsa by lia. lia.
Qed.

Lemma ugran_sym_val : forall E M k bege ne,
  know_ok SEGS E M k ->
  let beg := bv_unsigned (edenot E bege) in let n := bv_unsigned (edenot E ne) in
  1 <= n -> beg + n <= 2 ^ 64 ->
  bv_unsigned (edenot E (RPN.ugran_sym k bege ne)) = (beg + n - 1) / 8 - beg / 8 + 1.
Proof.
  intros E M k bege ne HK. cbn zeta. intros Hn Hb. unfold RPN.ugran_sym.
  pose proof (u64_range (edenot E bege)) as Ub. pose proof (u64_range (edenot E ne)) as Un.
  rewrite u_eadd. rewrite mkAlu_denot, u_sub64. rewrite !(u_mkSrl3 E M k _ HK).
  rewrite u_eadd, u_eadd. cbn [edenot]. rewrite (u_lit64 (-1)), (u64_lit 1) by lia. unfold two64.
  change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
  replace ((bv_unsigned (edenot E ne) + (2 ^ 64 - 1)) mod 2 ^ 64) with (bv_unsigned (edenot E ne) - 1)
    by (replace (bv_unsigned (edenot E ne) + (2 ^ 64 - 1)) with ((bv_unsigned (edenot E ne) - 1) + 1 * 2 ^ 64) by lia; rewrite Z.mod_add by lia; symmetry; apply Z.mod_small; lia).
  rewrite (Z.mod_small (bv_unsigned (edenot E bege) + (bv_unsigned (edenot E ne) - 1))) by lia.
  assert (D1 : bv_unsigned (edenot E bege) / 8 <= (bv_unsigned (edenot E bege) + (bv_unsigned (edenot E ne) - 1)) / 8) by (apply Z.div_le_mono; lia).
  assert (D2 : (bv_unsigned (edenot E bege) + (bv_unsigned (edenot E ne) - 1)) / 8 < 2 ^ 61) by (apply Z.div_lt_upper_bound; lia).
  pose proof (Z.div_pos (bv_unsigned (edenot E bege)) 8 ltac:(lia) ltac:(lia)) as D3.
  rewrite (Z.mod_small (_ - _)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma ushadow_zero_sym_sound : forall E M k bege ne,
  know_ok SEGS E M k -> RPN.ushadow_zero_sym k bege ne = true ->
  let beg := bv_unsigned (edenot E bege) in let n := bv_unsigned (edenot E ne) in
  1 <= n -> beg + n <= 2 ^ 64 ->
  forall g, beg / 8 <= g <= (beg + n - 1) / 8 -> M (Z_to_bv 64 (RPN.SB + g)) = Some (Z_to_bv 8 0).
Proof.
  intros E M k bege ne HK H. cbn zeta. intros Hn Hb. unfold RPN.ushadow_zero_sym in H.
  destruct (RPN.ushadow k bege) as [sb sk] eqn:Hu. apply andb_prop in H as [Hfl Hkz].
  destruct (ushadow_val_x E M k bege sb sk _ HK Hu Hfl) as (S1 & S2 & S3 & S4).
  pose proof (ugran_sym_val E M k bege ne HK Hn Hb) as G1. cbn zeta in G1.
  destruct (kzero_x_sound SEGS E M k k sb sk (RPN.ugran_sym k bege ne) HK HK Hkz) as (Zb & _ & _).
  unfold elenZ in Zb. rewrite G1 in Zb.
  intros g Hg. replace (RPN.SB + g) with (estart E (SA sb sk) + (g - bv_unsigned (edenot E bege) / 8)) by lia.
  apply Zb. lia.
Qed.

(* [comment removed for export] *)
Lemma region_shadow_sound : forall E M k args bege ne nhi,
  know_ok SEGS E M k -> RPN.region_shadow_ok SEGS k args bege ne nhi = true ->
  let beg := bv_unsigned (edenot E bege) in let n := bv_unsigned (edenot E ne) in
  1 <= n <= nhi -> nhi <= 2 ^ 40 -> beg + nhi <= 2 ^ 64 ->
  (forall g, beg / 8 <= g < (beg + n - 1) / 8 -> M (Z_to_bv 64 (RPN.SB + g)) = Some (Z_to_bv 8 0))
  /\ exists b1, M (Z_to_bv 64 (RPN.SB + (beg + n - 1) / 8)) = Some b1
             /\ (bv_unsigned b1 = 0 \/ (beg + n - 1) mod 8 < bv_unsigned b1 < 8).
Proof.
  intros E M k args bege ne nhi HK H. cbn zeta. intros Hn Hnhi Hwrap.
  pose proof (u64_range (edenot E bege)) as Ub. pose proof (u64_range (edenot E ne)) as Un.
  unfold RPN.region_shadow_ok in H.
  destruct (split_lit bege) as [bb bk] eqn:Hsb.
  (* [comment removed for export] *)
  assert (LIT : forall bb' bk' len, RPN.lit_shadow_zero k bb' bk' len = true -> 0 < len < 2 ^ 61 ->
            (let B := bv_unsigned (edenot E bb') + bk' in B <= bv_unsigned (edenot E bege) /\ bv_unsigned (edenot E bege) + bv_unsigned (edenot E ne) <= B + len) ->
            (forall g, bv_unsigned (edenot E bege) / 8 <= g < (bv_unsigned (edenot E bege) + bv_unsigned (edenot E ne) - 1) / 8 ->
               M (Z_to_bv 64 (RPN.SB + g)) = Some (Z_to_bv 8 0))
            /\ exists b1, M (Z_to_bv 64 (RPN.SB + (bv_unsigned (edenot E bege) + bv_unsigned (edenot E ne) - 1) / 8)) = Some b1
                       /\ (bv_unsigned b1 = 0 \/ (bv_unsigned (edenot E bege) + bv_unsigned (edenot E ne) - 1) mod 8 < bv_unsigned b1 < 8)).
  { intros bb' bk' len HL Hlen HB. destruct (RPN.shsplit k bb' bk') as [hb hk] eqn:Hsh.
    destruct (lit_shadow_zero_sound E M k bb' bk' len hb hk HK HL Hsh Hlen) as (B0 & B1 & Z0). cbn zeta in HB.
    assert (G1 : (bv_unsigned (edenot E bb') + bk') / 8 <= bv_unsigned (edenot E bege) / 8) by (apply Z.div_le_mono; lia).
    assert (G2 : (bv_unsigned (edenot E bege) + bv_unsigned (edenot E ne) - 1) / 8 <= (bv_unsigned (edenot E bb') + bk' + len - 1) / 8)
      by (apply Z.div_le_mono; lia).
    split.
    - intros g Hg. apply Z0. lia.
    - exists (Z_to_bv 8 0). split; [apply Z0 | left; reflexivity].
      split; [|exact G2]. apply (Z.le_trans _ (bv_unsigned (edenot E bege) / 8)); [exact G1 | apply Z.div_le_mono; lia]. }
  destruct args as [|ebase [|[elen| | | | | | |] [|]]]; try discriminate.
  - (* [comment removed for export] *)
    apply orb_prop in H as [H|HUS].
    2:{ pose proof (ushadow_zero_sym_sound E M k bege ne HK HUS) as Z0. cbn zeta in Z0. specialize (Z0 ltac:(lia) ltac:(lia)).
        split.
        - intros g Hg. apply Z0. lia.
        - exists (Z_to_bv 8 0). split; [apply Z0; lia | left; reflexivity]. }
    apply orb_prop in H as [H|HU].
    2:{ pose proof (ushadow_zero_sound E M k bege nhi HK HU ltac:(lia)) as Z0. cbn zeta in Z0.
        assert (G2 : (bv_unsigned (edenot E bege) + bv_unsigned (edenot E ne) - 1) / 8 <= (bv_unsigned (edenot E bege) + nhi - 1) / 8)
          by (apply Z.div_le_mono; lia).
        assert (G1 : bv_unsigned (edenot E bege) / 8 <= (bv_unsigned (edenot E bege) + bv_unsigned (edenot E ne) - 1) / 8)
          by (apply Z.div_le_mono; lia).
        split.
        - intros g Hg. apply Z0. lia.
        - exists (Z_to_bv 8 0). split; [apply Z0; lia | left; reflexivity]. }
    apply orb_prop in H as [H|H].
    + pose proof H as H'. unfold RPN.lit_shadow_zero in H'. destruct (RPN.shsplit k bb bk) as [hb hk] eqn:Hsh.
      apply andb_prop in H' as [H' _]. apply andb_prop in H' as [H' _]. apply andb_prop in H' as [_ Hflb].
      pose proof (split_beg_sound E M k bege bb bk HK Hsb Hflb) as HuB.
      apply (LIT bb bk nhi H ltac:(lia)). cbn zeta. lia.
    + destruct (sym_shadow_sound E M k bege ne HK H) as (Hal & Z0 & Zp).
      set (beg := bv_unsigned (edenot E bege)) in *. set (n := bv_unsigned (edenot E ne)) in *.
      pose proof (Z.div_mod beg 8 ltac:(lia)) as Hdb. rewrite Hal, Z.add_0_r in Hdb.
      pose proof (Z.div_mod n 8 ltac:(lia)) as Hdn. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Hmn.
      assert (E1 : (beg + n - 1) / 8 = beg / 8 + (n - 1) / 8).
      { rewrite Hdb at 1. replace (8 * (beg / 8) + n - 1) with (beg / 8 * 8 + (n - 1)) by lia. rewrite Z.div_add_l by lia. reflexivity. }
      assert (E2 : (beg + n - 1) mod 8 = (n - 1) mod 8).
      { rewrite Hdb at 1. replace (8 * (beg / 8) + n - 1) with ((n - 1) + (beg / 8) * 8) by lia. apply Z.mod_add. lia. }
      rewrite E1, E2.
      destruct (Z.eq_dec (n mod 8) 0) as [Hz|Hnz].
      * (* [comment removed for export] *)
        assert (E3 : (n - 1) / 8 = n / 8 - 1).
        { pose proof (Z.div_mod (n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n - 1) 8 ltac:(lia)). lia. }
        split.
        -- intros g Hg. replace (RPN.SB + g) with (RPN.SB + beg / 8 + (g - beg / 8)) by lia. apply Z0. lia.
        -- exists (Z_to_bv 8 0). split; [|left; reflexivity].
           replace (RPN.SB + (beg / 8 + (n - 1) / 8)) with (RPN.SB + beg / 8 + (n / 8 - 1)) by lia. apply Z0. lia.
      * (* [comment removed for export] *)
        assert (E3 : (n - 1) / 8 = n / 8).
        { pose proof (Z.div_mod (n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n - 1) 8 ltac:(lia)). lia. }
        assert (E4 : (n - 1) mod 8 = n mod 8 - 1).
        { pose proof (Z.div_mod (n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n - 1) 8 ltac:(lia)). lia. }
        split.
        -- intros g Hg. replace (RPN.SB + g) with (RPN.SB + beg / 8 + (g - beg / 8)) by lia. apply Z0. lia.
        -- exists (Z_to_bv 8 (n mod 8)). split.
           ++ replace (RPN.SB + (beg / 8 + (n - 1) / 8)) with (RPN.SB + beg / 8 + n / 8) by lia. apply Zp. exact Hnz.
           ++ right. rewrite u8_lit. rewrite (Z.mod_small (n mod 8) 256) by lia. lia.
  - (* [comment removed for export] *)
    destruct (split_lit ebase) as [eb ek] eqn:Hse.
    apply andb_prop in H as [Henc Hlit].
    destruct (enc_ok_sound E M k bege ne nhi eb ek elen HK Henc Hn) as (C0 & C1 & C2 & C3 & C4).
    apply (LIT eb ek elen Hlit ltac:(lia)). cbn zeta. lia.
Qed.


(* [comment removed for export] *)
Definition readable1 (M : word -> option byte) (a : Z) : Prop := exists c, rdn SEGS M (Z_to_bv 64 a) 1 = Some [c].

Lemma rpiece_sound : forall E M K b o l, kentry_ok SEGS E M K -> RPN.rpiece K = Some (b, o, l) ->
  flat E (SA b o) (elenZ E l) /\ forall i, 0 <= i < elenZ E l -> readable1 M (estart E (SA b o) + i).
Proof.
  intros E M K b o l HK HP.
  destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk| | | | | |[kb kk] len fc|[kb kk] len]; cbn [RPN.rpiece] in HP; try discriminate;
    injection HP as <- <- <-; cbn [kentry_ok] in HK.
  - destruct HK as (Hw & Hfl & Hrd). rewrite adenot_SA in Hrd.
    assert (El : elenZ E (ELit (Z.of_nat w)) = Z.of_nat w) by (unfold elenZ; cbn [edenot]; apply u64_lit; lia). rewrite El.
    split; [exact Hfl|]. intros i Hi. destruct Hfl as (F0 & F1 & F2 & F3).
    pose proof (APSX.rdn_nth SEGS M w (Z_to_bv 64 (estart E (SA kb kk))) _ (Z.to_nat i) ltac:(rewrite u64_lit by lia; lia) Hrd ltac:(lia)) as H1.
    rewrite u64_lit in H1 by lia. replace (estart E (SA kb kk) + Z.of_nat (Z.to_nat i)) with (estart E (SA kb kk) + i) in H1 by lia.
    eexists. exact H1.
  - destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. eexists. apply APSX.rdn1_overlay. apply Hz. exact Hi.
  - destruct HK as (Hfl & Hlen & Hz). split; [exact Hfl|]. intros i Hi. eexists. apply APSX.rdn1_overlay. apply Hz. exact Hi.
  - destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. eexists. apply APSX.rdn1_overlay. apply Hz. exact Hi.
  - destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi.
    destruct (M (Z_to_bv 64 (estart E (SA kb kk) + i))) as [c|] eqn:Hc; [|exfalso; exact (Hz i Hi Hc)].
    exists c. apply APSX.rdn1_overlay. exact Hc.
Qed.

Lemma lin_eqb_sound : forall E a b, RPN.lin_eqb a b = true -> bv_unsigned (edenot E a) = bv_unsigned (edenot E b).
Proof.
  intros E a b H. unfold RPN.lin_eqb in H. apply expr_eqb_eq in H.
  pose proof (lin_of_sound E a) as La. pose proof (unlin_sound E (lin_of a)) as Ua.
  pose proof (lin_of_sound E b) as Lb. pose proof (unlin_sound E (lin_of b)) as Ub. rewrite H in Ua.
  assert (X : eqm (AX2S.uE E a) (AX2S.uE E b)).
  { eapply eqm_trans; [apply eqm_sym; exact La|]. eapply eqm_trans; [apply eqm_sym; exact Ua|].
    eapply eqm_trans; [exact Ub | exact Lb]. }
  unfold AX2S.uE in X. destruct X as [q Hq]. pose proof (u64_range (edenot E a)). pose proof (u64_range (edenot E b)). nia.
Qed.

Lemma chain_go_sound : forall E M k ps (W : Z), know_ok SEGS E M k ->
  (forall p, In p ps -> exists K, In K k /\ RPN.rpiece K = Some p) ->
  forall fuel cur e,
    W <= e -> ((e < 2 ^ 64 /\ bv_unsigned (edenot E cur) = e) \/ 2 ^ 64 <= e) ->
    (forall a, W <= a < e -> a < 2 ^ 64 -> readable1 M a) ->
    exists e', W <= e' /\ ((e' < 2 ^ 64 /\ bv_unsigned (edenot E (RPN.chain_go fuel ps cur)) = e') \/ 2 ^ 64 <= e')
               /\ (forall a, W <= a < e' -> a < 2 ^ 64 -> readable1 M a).
Proof.
  intros E M k ps W HK Hps. induction fuel as [|f IH]; intros cur e HWe He Hrd.
  - exists e. cbn [RPN.chain_go]. auto.
  - cbn [RPN.chain_go].
    destruct (find (fun p => RPN.lin_eqb (eaddz (fst (fst p)) (snd (fst p))) cur) ps) as [[[b o] l]|] eqn:Hf; [|exists e; auto].
    apply find_some in Hf as [Hin Heq]. cbn [fst snd] in Heq.
    destruct (Hps _ Hin) as (K & HinK & HP).
    destruct (rpiece_sound E M K b o l (proj1 (Forall_forall _ _) HK _ HinK) HP) as [Hfl Hrp].
    pose proof (lin_eqb_sound E _ _ Heq) as Hcur. unfold eaddz in Hcur. rewrite u_eadd in Hcur.
    change (bv_unsigned (edenot E (ELit o))) with (bv_unsigned (Z_to_bv 64 o)) in Hcur. rewrite u_lit64 in Hcur. unfold two64 in Hcur.
    destruct Hfl as (F0 & F1 & F2 & F3). unfold estart in *. cbn [a_base a_off] in *.
    set (S := bv_unsigned (edenot E b) + o) in *. set (L := elenZ E l) in *.
    assert (HS : (bv_unsigned (edenot E b) + o mod 2 ^ 64) mod 2 ^ 64 = S).
    { rewrite Z.add_mod_idemp_r by lia. apply Z.mod_small. lia. }
    rewrite HS in Hcur.
    destruct He as [[He1 He2]|He].
    + (* [comment removed for export] *)
      rewrite He2 in Hcur. subst e.
      apply (IH (mkAlu ALU_ADD (mkAlu ALU_ADD b (ELit o)) l) (S + L)); [lia | |].
      * rewrite u_eadd. rewrite u_eadd. change (bv_unsigned (edenot E (ELit o))) with (bv_unsigned (Z_to_bv 64 o)).
        rewrite u_lit64. unfold two64. rewrite HS. fold L.
        destruct (Z_lt_ge_dec (S + L) (2 ^ 64)); [left; split; [lia | apply Z.mod_small; lia] | right; lia].
      * intros a Ha Ha64. destruct (Z_lt_ge_dec a S); [apply Hrd; lia|].
        replace a with (S + (a - S)) by lia. apply Hrp. lia.
    + apply (IH _ e); [lia | right; exact He | exact Hrd].
Qed.

Lemma chain_go_s_sound : forall E M k ps (W : Z), know_ok SEGS E M k ->
  (forall p, In p ps -> exists K, In K k /\ RPN.rpiece K = Some p) ->
  forall start minlen fuel cur e,
    W <= e -> ((e < 2 ^ 64 /\ bv_unsigned (edenot E cur) = e) \/ 2 ^ 64 <= e) ->
    (forall a, W <= a < e -> a < 2 ^ 64 -> readable1 M a) ->
    exists e', W <= e' /\ ((e' < 2 ^ 64 /\ bv_unsigned (edenot E (RPN.chain_go_s fuel ps start minlen cur)) = e') \/ 2 ^ 64 <= e')
               /\ (forall a, W <= a < e' -> a < 2 ^ 64 -> readable1 M a).
Proof.
  intros E M k ps W HK Hps start minlen. induction fuel as [|f IH]; intros cur e HWe He Hrd.
  - exists e. cbn [RPN.chain_go_s]. auto.
  - cbn [RPN.chain_go_s]. destruct (RPN.chain_reached start minlen cur); [exists e; auto|].
    destruct (find (fun p => RPN.lin_eqb (eaddz (fst (fst p)) (snd (fst p))) cur) ps) as [[[b o] l]|] eqn:Hf; [|exists e; auto].
    apply find_some in Hf as [Hin Heq]. cbn [fst snd] in Heq.
    destruct (Hps _ Hin) as (K & HinK & HP).
    destruct (rpiece_sound E M K b o l (proj1 (Forall_forall _ _) HK _ HinK) HP) as [Hfl Hrp].
    pose proof (lin_eqb_sound E _ _ Heq) as Hcur. unfold eaddz in Hcur. rewrite u_eadd in Hcur.
    change (bv_unsigned (edenot E (ELit o))) with (bv_unsigned (Z_to_bv 64 o)) in Hcur. rewrite u_lit64 in Hcur. unfold two64 in Hcur.
    destruct Hfl as (F0 & F1 & F2 & F3). unfold estart in *. cbn [a_base a_off] in *.
    set (S := bv_unsigned (edenot E b) + o) in *. set (L := elenZ E l) in *.
    assert (HS : (bv_unsigned (edenot E b) + o mod 2 ^ 64) mod 2 ^ 64 = S).
    { rewrite Z.add_mod_idemp_r by lia. apply Z.mod_small. lia. }
    rewrite HS in Hcur.
    destruct He as [[He1 He2]|He].
    + (* [comment removed for export] *)
      rewrite He2 in Hcur. subst e.
      apply (IH (mkAlu ALU_ADD (mkAlu ALU_ADD b (ELit o)) l) (S + L)); [lia | |].
      * rewrite u_eadd. rewrite u_eadd. change (bv_unsigned (edenot E (ELit o))) with (bv_unsigned (Z_to_bv 64 o)).
        rewrite u_lit64. unfold two64. rewrite HS. fold L.
        destruct (Z_lt_ge_dec (S + L) (2 ^ 64)); [left; split; [lia | apply Z.mod_small; lia] | right; lia].
      * intros a Ha Ha64. destruct (Z_lt_ge_dec a S); [apply Hrd; lia|].
        replace a with (S + (a - S)) by lia. apply Hrp. lia.
    + apply (IH _ e); [lia | right; exact He | exact Hrd].
Qed.

Lemma kchain_sound : forall E M k b off minlen,
  know_ok SEGS E M k -> RPN.kchain k b off minlen = true ->
  let W := bv_unsigned (edenot E b) + off in 0 <= W -> W < 2 ^ 64 ->
  forall a, W <= a < W + minlen -> a < 2 ^ 64 -> readable1 M a.
Proof.
  intros E M k b off minlen HK H. cbn zeta. intros HW0 HW1 a Ha Ha64. unfold RPN.kchain in H.
  set (ps := flat_map _ k) in H.
  set (cur := RPN.chain_go_s (length ps) ps (eaddz b off) minlen (eaddz b off)) in H.
  destruct (lin_of (mkAlu ALU_SUB cur (eaddz b off))) as [d ts] eqn:Hl. destruct ts; [|discriminate].
  apply andb_prop in H as [H Hm0]. apply andb_prop in H as [Hd1 Hd2]. apply Z.leb_le in Hd1. apply Z.ltb_lt in Hd2. apply Z.leb_le in Hm0.
  assert (Hps : forall p, In p ps -> exists K, In K k /\ RPN.rpiece K = Some p).
  { intros p Hp. unfold ps in Hp. apply in_flat_map in Hp as (K & HinK & HP). exists K. split; [exact HinK|].
    destruct (RPN.rpiece K) as [p'|]; [|destruct HP]. destruct HP as [<-|[]]. reflexivity. }
  set (W := bv_unsigned (edenot E b) + off) in *.
  assert (Hcur0 : bv_unsigned (edenot E (eaddz b off)) = W).
  { unfold eaddz. rewrite u_eadd. change (bv_unsigned (edenot E (ELit off))) with (bv_unsigned (Z_to_bv 64 off)).
    rewrite u_lit64. unfold two64. rewrite Z.add_mod_idemp_r by lia. apply Z.mod_small. lia. }
  destruct (chain_go_s_sound E M k ps W HK Hps (eaddz b off) minlen (length ps) (eaddz b off) W ltac:(lia) ltac:(left; split; [lia | exact Hcur0]) ltac:(intros; lia))
    as (e' & HWe & He & Hrd). fold cur in He.
  destruct He as [[He1 He2]|He]; [|apply Hrd; lia].
  (* [comment removed for export] *)
  pose proof (lin_of_sound E (mkAlu ALU_SUB cur (eaddz b off))) as Ld. rewrite Hl in Ld.
  unfold lden in Ld. cbn [fst snd tden] in Ld. rewrite Z.add_0_r in Ld.
  unfold AX2S.uE in Ld. rewrite mkAlu_denot, alu_sub in Ld. unfold v_sub in Ld. rewrite Hcur0, He2, u_lit64 in Ld. unfold two64 in Ld.
  destruct Ld as [q Hq].
  pose proof (Z.div_mod (e' - W) (2 ^ 64) ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound (e' - W) (2 ^ 64) ltac:(lia)) as Hmb.
  apply Hrd; [|exact Ha64]. nia.
Qed.

(* [comment removed for export] *)
Lemma lin_gcd_divides : forall E (c : Z) (ts : list (Z * expr)),
  let g := fold_right (fun t g => Z.gcd (fst t) g) c ts in (g | c) /\ (g | AX2S.tden E ts).
Proof.
  intros E c ts. induction ts as [|[k a] rest IH]; cbn [fold_right AX2S.tden fst].
  - split; [apply Z.divide_refl | apply Z.divide_0_r].
  - destruct IH as [IHc IHt]. set (g' := fold_right _ c rest) in *.
    pose proof (Z.gcd_divide_l k g') as G1. pose proof (Z.gcd_divide_r k g') as G2.
    split; [exact (Z.divide_trans _ _ _ G2 IHc)|].
    apply Z.divide_add_r; [apply Z.divide_mul_l; exact G1 | exact (Z.divide_trans _ _ _ G2 IHt)].
Qed.

Lemma lin_align_sound : forall E e,
  0 <= RPN.lin_align e <= 64 /\ (2 ^ RPN.lin_align e | bv_unsigned (edenot E e)).
Proof.
  intros E e. unfold RPN.lin_align, RPN.lin_gcd.
  destruct (ctz64_sound (fold_right (fun t g => Z.gcd (fst t) g) (fst (lin_of e)) (snd (lin_of e)))) as [Hr Hd].
  split; [exact Hr|].
  set (j := ctz64 _) in *. set (g := fold_right _ _ _) in *.
  destruct (lin_gcd_divides E (fst (lin_of e)) (snd (lin_of e))) as [Gc Gt]. fold g in Gc, Gt.
  pose proof (lin_of_sound E e) as [q Hq]. unfold AX2S.lden, AX2S.uE in Hq.
  assert (G : (2 ^ j | bv_unsigned (edenot E e) + q * 2 ^ 64)).
  { rewrite <- Hq. apply (Z.divide_trans _ g); [exact Hd|]. apply Z.divide_add_r; [exact Gc | exact Gt]. }
  apply (Z.divide_add_cancel_r (2 ^ j) (q * 2 ^ 64)).
  - apply Z.divide_mul_r. apply pow2_divide_le. lia.
  - rewrite Z.add_comm. exact G.
Qed.

Lemma zrd8 : forall z, z - z mod 8 = z / 8 * 8.
Proof. intros z. pose proof (Z.div_mod z 8 ltac:(lia)). lia. Qed.

(* [comment removed for export] *)
Lemma window_cover_sound : forall E M k hb hk ng,
  know_ok SEGS E M k -> RPN.window_cover k hb hk ng = true -> 1 <= ng < 2 ^ 60 ->
  let x := bv_unsigned (edenot E hb) + hk in
  7 <= x /\ x + ng <= 2 ^ 64 /\
  forall a, x - x mod 8 <= a < (x + ng - 1) - (x + ng - 1) mod 8 + 8 -> readable1 M a.
Proof.
  intros E M k hb hk ng HK H Hng. rewrite RPN.window_cover_eq in H. unfold RPN.window_cover_ref in H.
  apply existsb_exists in H as (K & HinK & HKc).
  destruct (RPN.rpiece K) as [[[b o] l]|] eqn:HP; [|discriminate].
  destruct (rpiece_sound E M K b o l (proj1 (Forall_forall _ _) HK _ HinK) HP) as [Hfl Hrd].
  destruct Hfl as (F0 & F1 & F2 & F3).
  set (S := estart E (SA b o)) in *. set (L := elenZ E l) in *.
  cbn zeta.
  pose proof (Z.mod_pos_bound (bv_unsigned (edenot E hb) + hk) 8 ltac:(lia)) as M1.
  pose proof (Z.mod_pos_bound (bv_unsigned (edenot E hb) + hk + ng - 1) 8 ltac:(lia)) as M2.
  pose proof (Z.div_mod (bv_unsigned (edenot E hb) + hk + ng - 1) 8 ltac:(lia)) as D2.
  assert (RD : forall a, S <= a < S + L -> readable1 M a).
  { intros a Ha. replace a with (S + (a - S)) by lia. apply Hrd. lia. }
  destruct (xinsideL k hb (hk - 7) (ELit (ng + 14)) b o l) eqn:X1.
  - pose proof (xinsideL_sound SEGS E M k _ _ _ _ _ _ HK X1) as [I1 I2].
    rewrite (APS.elenZ_lit E (ng + 14)) in I2 by lia. fold L in I2.
    unfold estart in I1, I2. cbn [a_base a_off] in I1, I2.
    change (bv_unsigned (edenot E b) + o) with S in I1, I2.
    split; [lia|]. split; [lia|]. intros a Ha. apply RD. lia.
  - apply andb_prop in HKc as [X2 Hal]. apply Z.leb_le in Hal.
    pose proof (xinsideL_sound SEGS E M k _ _ _ _ _ _ HK X2) as [I1 I2].
    rewrite (APS.elenZ_lit E (ng + 7)) in I2 by lia. fold L in I2.
    unfold estart in I1, I2. cbn [a_base a_off] in I1, I2.
    change (bv_unsigned (edenot E b) + o) with S in I1, I2.
    (* [comment removed for export] *)
    destruct (lin_align_sound E (mkAlu ALU_ADD (eaddz b o) l)) as [Hj Hdv].
    set (j := RPN.lin_align _) in *.
    rewrite u_eadd in Hdv. unfold eaddz in Hdv. rewrite u_eadd in Hdv.
    change (bv_unsigned (edenot E (ELit o))) with (bv_unsigned (Z_to_bv 64 o)) in Hdv. rewrite u_lit64 in Hdv. unfold two64 in Hdv.
    change (bv_unsigned (edenot E l)) with L in Hdv.
    assert (HS : (bv_unsigned (edenot E b) + o mod 2 ^ 64) mod 2 ^ 64 = S).
    { rewrite Z.add_mod_idemp_r by lia. apply Z.mod_small. unfold S, estart in *. cbn [a_base a_off] in *. lia. }
    rewrite HS in Hdv.
    assert (H8 : (8 | S + L)).
    { rewrite (Z.div_mod (S + L) (2 ^ 64)) by lia. apply Z.divide_add_r.
      - apply Z.divide_mul_l. exists (2 ^ 61). reflexivity.
      - apply (Z.divide_trans 8 (2 ^ j)); [|exact Hdv]. change 8 with (2 ^ 3). apply pow2_divide_le. lia. }
    destruct H8 as [t Ht].
    split; [lia|]. split; [lia|]. intros a Ha. apply RD. lia.
Qed.

(* [comment removed for export] *)
Lemma rd8_mono : forall a b, a <= b -> a / 8 * 8 <= b / 8 * 8.
Proof. intros a b H. pose proof (Z.div_le_mono a b 8 ltac:(lia) H). lia. Qed.
Lemma ushadow_window_sound : forall E M k bege nhi,
  know_ok SEGS E M k -> RPN.ushadow_window k bege nhi = true -> 1 <= nhi <= 2 ^ 40 ->
  let beg := bv_unsigned (edenot E bege) in
  forall a, (RPN.SB + beg / 8) / 8 * 8 <= a < (RPN.SB + (beg + nhi - 1) / 8) / 8 * 8 + 8 -> readable1 M a.
Proof.
  intros E M k bege nhi HK H Hn. cbn zeta. unfold RPN.ushadow_window in H.
  destruct (RPN.ushadow k bege) as [sb sk] eqn:Hu. apply andb_prop in H as [Hfl Hwc].
  assert (HG : 1 <= RPN.ugran nhi < 2 ^ 38) by (unfold RPN.ugran; lia).
  destruct (ushadow_val E M k bege sb sk (RPN.ugran nhi) HK Hu Hfl ltac:(lia)) as (S1 & S2 & S3).
  pose proof (window_cover_sound E M k sb sk (RPN.ugran nhi) HK Hwc ltac:(lia)) as W. cbn zeta in W. destruct W as (W1 & W2 & RD).
  unfold estart in S1, S2, S3. cbn [a_base a_off] in S1, S2, S3.
  pose proof (u64_range (edenot E bege)) as Ub.
  intros a Ha. apply RD. rewrite !zrd8. rewrite S1.
  assert (G2 : RPN.SB + (bv_unsigned (edenot E bege) + nhi - 1) / 8 <= RPN.SB + bv_unsigned (edenot E bege) / 8 + RPN.ugran nhi - 1)
    by (unfold RPN.ugran; lia).
  pose proof (rd8_mono _ _ G2). lia.
Qed.

(* [comment removed for export] *)
Lemma elenZ_addlit : forall E n z, 0 <= z -> elenZ E n + z < 2 ^ 64 -> elenZ E (mkAlu ALU_ADD n (ELit z)) = elenZ E n + z.
Proof.
  intros E n z Hz Hb. unfold elenZ in *. rewrite u_eadd. cbn [edenot]. pose proof (u64_range (edenot E n)).
  rewrite (u64_lit z) by lia. apply Z.mod_small. lia.
Qed.
Lemma window_cover_x_sound : forall E M k hb hk nge,
  know_ok SEGS E M k -> RPN.window_cover_x k hb hk nge = true -> 1 <= elenZ E nge < 2 ^ 60 ->
  let ng := elenZ E nge in
  let x := bv_unsigned (edenot E hb) + hk in
  7 <= x /\ x + ng <= 2 ^ 64 /\
  forall a, x - x mod 8 <= a < (x + ng - 1) - (x + ng - 1) mod 8 + 8 -> readable1 M a.
Proof.
  intros E M k hb hk nge HK H Hng. rewrite RPN.window_cover_x_eq in H. unfold RPN.window_cover_x_ref in H.
  apply existsb_exists in H as (K & HinK & HKc).
  destruct (RPN.rpiece K) as [[[b o] l]|] eqn:HP; [|discriminate].
  destruct (rpiece_sound E M K b o l (proj1 (Forall_forall _ _) HK _ HinK) HP) as [Hfl Hrd].
  destruct Hfl as (F0 & F1 & F2 & F3).
  set (S := estart E (SA b o)) in *. set (L := elenZ E l) in *. set (ng := elenZ E nge) in *.
  cbn zeta.
  pose proof (Z.mod_pos_bound (bv_unsigned (edenot E hb) + hk) 8 ltac:(lia)) as M1.
  pose proof (Z.mod_pos_bound (bv_unsigned (edenot E hb) + hk + ng - 1) 8 ltac:(lia)) as M2.
  pose proof (Z.div_mod (bv_unsigned (edenot E hb) + hk + ng - 1) 8 ltac:(lia)) as D2.
  assert (RD : forall a, S <= a < S + L -> readable1 M a).
  { intros a Ha. replace a with (S + (a - S)) by lia. apply Hrd. lia. }
  assert (E14 : elenZ E (mkAlu ALU_ADD nge (ELit 14)) = ng + 14) by (unfold ng; apply elenZ_addlit; lia).
  assert (E7 : elenZ E (mkAlu ALU_ADD nge (ELit 7)) = ng + 7) by (unfold ng; apply elenZ_addlit; lia).
  destruct (xinsideL k hb (hk - 7) (mkAlu ALU_ADD nge (ELit 14)) b o l) eqn:X1.
  - pose proof (xinsideL_sound SEGS E M k _ _ _ _ _ _ HK X1) as [I1 I2].
    rewrite E14 in I2. fold L in I2.
    unfold estart in I1, I2. cbn [a_base a_off] in I1, I2.
    change (bv_unsigned (edenot E b) + o) with S in I1, I2.
    split; [lia|]. split; [lia|]. intros a Ha. apply RD. lia.
  - apply andb_prop in HKc as [X2 Hal]. apply Z.leb_le in Hal.
    pose proof (xinsideL_sound SEGS E M k _ _ _ _ _ _ HK X2) as [I1 I2].
    rewrite E7 in I2. fold L in I2.
    unfold estart in I1, I2. cbn [a_base a_off] in I1, I2.
    change (bv_unsigned (edenot E b) + o) with S in I1, I2.
    (* [comment removed for export] *)
    destruct (lin_align_sound E (mkAlu ALU_ADD (eaddz b o) l)) as [Hj Hdv].
    set (j := RPN.lin_align _) in *.
    rewrite u_eadd in Hdv. unfold eaddz in Hdv. rewrite u_eadd in Hdv.
    change (bv_unsigned (edenot E (ELit o))) with (bv_unsigned (Z_to_bv 64 o)) in Hdv. rewrite u_lit64 in Hdv. unfold two64 in Hdv.
    change (bv_unsigned (edenot E l)) with L in Hdv.
    assert (HS : (bv_unsigned (edenot E b) + o mod 2 ^ 64) mod 2 ^ 64 = S).
    { rewrite Z.add_mod_idemp_r by lia. apply Z.mod_small. unfold S, estart in *. cbn [a_base a_off] in *. lia. }
    rewrite HS in Hdv.
    assert (H8 : (8 | S + L)).
    { rewrite (Z.div_mod (S + L) (2 ^ 64)) by lia. apply Z.divide_add_r.
      - apply Z.divide_mul_l. exists (2 ^ 61). reflexivity.
      - apply (Z.divide_trans 8 (2 ^ j)); [|exact Hdv]. change 8 with (2 ^ 3). apply pow2_divide_le. lia. }
    destruct H8 as [t Ht].
    split; [lia|]. split; [lia|]. intros a Ha. apply RD. lia.
Qed.
Lemma ushadow_window_sym_sound : forall E M k bege ne,
  know_ok SEGS E M k -> RPN.ushadow_window_sym k bege ne = true ->
  let beg := bv_unsigned (edenot E bege) in let n := bv_unsigned (edenot E ne) in
  1 <= n <= 2 ^ 40 -> beg + n <= 2 ^ 64 ->
  forall a, (RPN.SB + beg / 8) / 8 * 8 <= a < (RPN.SB + (beg + n - 1) / 8) / 8 * 8 + 8 -> readable1 M a.
Proof.
  intros E M k bege ne HK H. cbn zeta. intros Hn Hb. unfold RPN.ushadow_window_sym in H.
  destruct (RPN.ushadow k bege) as [sb sk] eqn:Hu. apply andb_prop in H as [Hfl Hwc].
  destruct (ushadow_val_x E M k bege sb sk _ HK Hu Hfl) as (S1 & S2 & S3 & S4).
  pose proof (ugran_sym_val E M k bege ne HK ltac:(lia) Hb) as G1. cbn zeta in G1.
  pose proof (u64_range (edenot E bege)) as Ub. pose proof (u64_range (edenot E ne)) as Un.
  assert (D1 : bv_unsigned (edenot E bege) / 8 <= (bv_unsigned (edenot E bege) + bv_unsigned (edenot E ne) - 1) / 8) by (apply Z.div_le_mono; lia).
  assert (D2 : (bv_unsigned (edenot E bege) + bv_unsigned (edenot E ne) - 1) / 8 <= bv_unsigned (edenot E bege) / 8 + 2 ^ 38).
  { pose proof (Z.div_mod (bv_unsigned (edenot E bege)) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned (edenot E bege)) 8 ltac:(lia)).
    apply Z.div_le_upper_bound; lia. }
  assert (HG : 1 <= elenZ E (RPN.ugran_sym k bege ne) < 2 ^ 60) by (unfold elenZ; rewrite G1; lia).
  pose proof (window_cover_x_sound E M k sb sk (RPN.ugran_sym k bege ne) HK Hwc HG) as W. cbn zeta in W. destruct W as (W1 & W2 & RD).
  unfold elenZ in RD, W2. rewrite G1 in RD, W2.
  unfold estart in S1, S2, S3. cbn [a_base a_off] in S1, S2, S3.
  intros a Ha. apply RD. rewrite !zrd8. rewrite S1.
  replace (RPN.SB + bv_unsigned (edenot E bege) / 8 + ((bv_unsigned (edenot E bege) + bv_unsigned (edenot E ne) - 1) / 8 - bv_unsigned (edenot E bege) / 8 + 1) - 1)
    with (RPN.SB + (bv_unsigned (edenot E bege) + bv_unsigned (edenot E ne) - 1) / 8) by lia.
  exact Ha.
Qed.

(* [comment removed for export] *)
Lemma shsplit_sound0 : forall E M k bb bk hb hk,
  know_ok SEGS E M k -> 3 <= ealign k bb -> RPN.shsplit k bb bk = (hb, hk) ->
  0 <= bv_unsigned (edenot E hb) + hk < 2 ^ 64 ->
  0 <= bv_unsigned (edenot E bb) + bk < 2 ^ 64 ->
  exists q, bv_unsigned (edenot E bb) = 8 * q /\ estart E (SA hb hk) = RPN.SB + q + bk / 8.
Proof.
  intros E M k bb bk hb hk HK Hal Hsh Hhb Hbeg. unfold RPN.shsplit in Hsh.
  destruct (ealign_sound SEGS E M k bb HK) as [Hea1 Hea2].
  set (bbu := bv_unsigned (edenot E bb)) in *.
  assert (Hal8 : exists q, bbu = 8 * q).
  { destruct Hea2 as [q Hq8]. exists (q * 2 ^ (ealign k bb - 3)). fold bbu in Hq8. rewrite Hq8.
    replace (ealign k bb) with ((ealign k bb - 3) + 3) at 1 by lia.
    rewrite Z.pow_add_r by lia. change (2 ^ 3) with 8. lia. }
  destruct Hal8 as [q Hq8]. exists q. split; [exact Hq8|].
  pose proof (u64_range (edenot E bb)) as Ubb. fold bbu in Ubb.
  pose proof (w_split_lit_denot E _ hb hk Hsh) as Hsa.
  unfold eadd in Hsa. rewrite mkAlu_denot in Hsa.
  rewrite (mkSrl_denot SEGS E M k bb 3 (Z_to_bv 64 3) HK ltac:(rewrite u64_lit by lia; reflexivity)) in Hsa.
  rewrite (srl3_div8 (edenot E bb) (Z_to_bv 64 3)) in Hsa by (rewrite u64_lit by lia; reflexivity). fold bbu in Hsa.
  cbn [edenot] in Hsa. rewrite alu_add, v_add_zbv_mod' in Hsa.
  assert (Hdiv4 : bbu / 8 = q) by (rewrite Hq8, Z.mul_comm; apply Z.div_mul; lia).
  rewrite Hdiv4 in Hsa.
  assert (Hdiv1 : (bbu + bk) / 8 = q + bk / 8).
  { rewrite Hq8. rewrite Z.mul_comm, Z.div_add_l by lia. reflexivity. }
  assert (Hr1 : 0 <= (bbu + bk) / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  unfold RPN.SB in *. unfold estart in *. cbn [a_base a_off] in *.
  replace (2147450880 + bk / 8 + q) with (2147450880 + (bbu + bk) / 8) in Hsa by lia.
  pose proof (u64_range (edenot E hb)) as Uhb.
  apply (f_equal bv_unsigned) in Hsa. rewrite (u64_lit (2147450880 + (bbu + bk) / 8)) in Hsa by lia.
  rewrite u64_lit in Hsa by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma shadow_window_sound : forall E M k bb bk len hb hk,
  know_ok SEGS E M k -> RPN.shadow_window_ok k bb bk len = true -> RPN.shsplit k bb bk = (hb, hk) -> 0 < len < 2 ^ 61 ->
  let B := bv_unsigned (edenot E bb) + bk in
  0 <= B /\ B + 1 <= 2 ^ 64 /\
  forall a, (RPN.SB + B / 8) / 8 * 8 <= a < (RPN.SB + (B + len - 1) / 8) / 8 * 8 + 8 -> readable1 M a.
Proof.
  intros E M k bb bk len hb hk HK H Hsh Hlen.
  unfold RPN.shadow_window_ok in H. rewrite Hsh in H.
  set (L := RPN.ngran bk len) in *.
  assert (HL : 1 <= L < 2 ^ 59).
  { unfold L, RPN.ngran. pose proof (Z.div_le_mono bk (bk + len - 1) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_mod bk 8 ltac:(lia)). pose proof (Z.mod_pos_bound bk 8 ltac:(lia)).
    pose proof (Z.div_mod (bk + len - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (bk + len - 1) 8 ltac:(lia)). lia. }
  set (w0 := hk - hk mod 8) in *. set (w1 := hk + L - 1 - (hk + L - 1) mod 8 + 8) in *.
  apply andb_prop in H as [H Hwin]. apply andb_prop in H as [Halb Hflb].
  apply Z.leb_le in Halb.
  destruct (flat_x_sound SEGS E M k bb bk (ELit 1) HK Hflb) as (B0 & B1 & _).
  change (bv_unsigned (edenot E (ELit 1))) with (bv_unsigned (Z_to_bv 64 1)) in B1. rewrite u64_lit in B1 by lia.
  unfold estart in B0, B1. cbn [a_base a_off] in B0, B1.
  cbn zeta. split; [lia|]. split; [lia|].
  pose proof (Z.mod_pos_bound hk 8 ltac:(lia)) as M1. pose proof (Z.mod_pos_bound (hk + L - 1) 8 ltac:(lia)) as M2.
  pose proof (Z.div_mod hk 8 ltac:(lia)) as D1. pose proof (Z.div_mod (hk + L - 1) 8 ltac:(lia)) as D2.
  pose proof (Z.div_le_mono hk (hk + L - 1) 8 ltac:(lia) ltac:(lia)) as D3.
  match type of Hwin with (if ?c then true else _) = true => destruct c eqn:Hal end.   (* [comment removed for export] *)
  - (* [comment removed for export] *)
    clear Hwin. apply andb_prop in Hal as [Hal Hch]. apply andb_prop in Hal as [Halh Hflw]. apply Z.leb_le in Halh.
    destruct (shsplit_sound E M k bb bk hb hk w0 (w1 - w0) HK Halb Hsh Hflw ltac:(lia) ltac:(lia) ltac:(lia)) as (q & Hq & HH & H0 & H1).
    unfold estart in HH, H0, H1. cbn [a_base a_off] in HH, H0, H1.
    (* [comment removed for export] *)
    destruct (ealign_sound SEGS E M k hb HK) as [He1 [qh Hqh]].
    assert (Hh8 : exists t, bv_unsigned (edenot E hb) = 8 * t).
    { exists (qh * 2 ^ (ealign k hb - 3)). rewrite Hqh.
      replace (ealign k hb) with ((ealign k hb - 3) + 3) at 1 by lia. rewrite Z.pow_add_r by lia. change (2 ^ 3) with 8. lia. }
    destruct Hh8 as [t Ht].
    assert (Hdiv1 : (bv_unsigned (edenot E bb) + bk) / 8 = q + bk / 8).
    { rewrite Hq. rewrite Z.mul_comm, Z.div_add_l by lia. reflexivity. }
    assert (Hdiv2 : (bv_unsigned (edenot E bb) + bk + len - 1) / 8 = q + (bk + len - 1) / 8).
    { rewrite Hq. replace (8 * q + bk + len - 1) with (q * 8 + (bk + len - 1)) by lia. rewrite Z.div_add_l by lia. reflexivity. }
    pose proof (kchain_sound E M k hb w0 (w1 - w0) HK Hch) as KC. cbn zeta in KC.
    (* [comment removed for export] *)
    assert (R1 : (RPN.SB + (q + bk / 8)) / 8 * 8 = 8 * t + w0).
    { replace (RPN.SB + (q + bk / 8)) with (t * 8 + hk) by lia. rewrite Z.div_add_l by lia. unfold w0. lia. }
    assert (R2 : (RPN.SB + (q + (bk + len - 1) / 8)) / 8 * 8 + 8 = 8 * t + w1).
    { replace (RPN.SB + (q + (bk + len - 1) / 8)) with (t * 8 + (hk + L - 1)) by (clear - HH Ht; unfold L, RPN.ngran; lia).
      rewrite Z.div_add_l by lia. unfold w1. clear. lia. }
    intros a Ha. rewrite Hdiv1, Hdiv2, R1, R2 in Ha. apply KC; clear - Ha Ht HH H0 H1 M1 M2 HL; lia.   (* [comment removed for export] *)
  - (* [comment removed for export] *)
    change (RPN.window_cover k hb hk L = true) in Hwin.
    destruct (window_cover_sound E M k hb hk L HK Hwin ltac:(lia)) as (X0 & X1 & Xrd).
    destruct (shsplit_sound0 E M k bb bk hb hk HK Halb Hsh ltac:(lia) ltac:(lia)) as (q & Hq & HH).
    unfold estart in HH. cbn [a_base a_off] in HH.
    assert (Hdiv1 : (bv_unsigned (edenot E bb) + bk) / 8 = q + bk / 8).
    { rewrite Hq. rewrite Z.mul_comm, Z.div_add_l by lia. reflexivity. }
    assert (Hdiv2 : (bv_unsigned (edenot E bb) + bk + len - 1) / 8 = q + (bk + len - 1) / 8).
    { rewrite Hq. replace (8 * q + bk + len - 1) with (q * 8 + (bk + len - 1)) by lia. rewrite Z.div_add_l by lia. reflexivity. }
    intros a Ha. rewrite Hdiv1, Hdiv2 in Ha. apply Xrd. rewrite HH.
    rewrite !zrd8.
    replace (RPN.SB + q + bk / 8 + L - 1) with (RPN.SB + (q + (bk + len - 1) / 8)) by (unfold L, RPN.ngran; lia).
    replace (RPN.SB + q + bk / 8) with (RPN.SB + (q + bk / 8)) by lia. exact Ha.
Qed.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Lemma ulit_lo : forall E, bv_unsigned (edenot E (ELit RPN.kLowEnd)) = RPN.kLowEnd.
Proof. intros E. cbn [edenot]. rewrite u_lit64 by (unfold RPN.kLowEnd, two64; lia). apply Z.mod_small. unfold RPN.kLowEnd, two64. lia. Qed.
Lemma ulit_band : forall E, bv_unsigned (edenot E (ELit (RPN.kHighBeg - RPN.kLowEnd))) = RPN.kHighBeg - RPN.kLowEnd.
Proof. intros E. cbn [edenot]. rewrite u_lit64 by (unfold RPN.kLowEnd, RPN.kHighBeg, two64; lia). apply Z.mod_small. unfold RPN.kLowEnd, RPN.kHighBeg, two64. lia. Qed.
Lemma side_ok_cases : forall k beg ne blo bhi nhi, RPN.side_ok k beg ne blo bhi nhi = true ->
  (bhi + nhi <= RPN.kLowEnd \/ (RPN.kHighBeg <= blo /\ bhi + nhi <= RPN.kHighEnd))
  \/ (bhi <= 2^47 /\ nhi <= 2^47 /\ ranges_apart_x k beg 0 ne (ELit RPN.kLowEnd) 0 (ELit (RPN.kHighBeg - RPN.kLowEnd)) = true
      /\ (bhi + nhi <= RPN.kHighEnd \/ exists lo1 hi1 e, base_range k beg = Some (lo1,hi1) /\ end_hi k beg 0 ne lo1 hi1 nhi = Some e /\ e <= RPN.kHighEnd)).
Proof.
  intros k beg ne blo bhi nhi H. unfold RPN.side_ok in H.
  apply orb_prop in H as [Hnum|Hrel].
  - left. apply orb_prop in Hnum as [Hr|Hr]; [apply Z.leb_le in Hr; left; exact Hr|].
    apply andb_prop in Hr as [Hr1 Hr2]. apply Z.leb_le in Hr1. apply Z.leb_le in Hr2. right. split; assumption.
  - right. apply andb_prop in Hrel as [Hrel Hend]. apply andb_prop in Hrel as [Hrel Hap]. apply andb_prop in Hrel as [Hb47 Hn47].
    apply Z.leb_le in Hb47. apply Z.leb_le in Hn47. split; [exact Hb47|]. split; [exact Hn47|]. split; [exact Hap|].
    apply orb_prop in Hend as [He|He]; [apply Z.leb_le in He; left; exact He|].
    destruct (base_range k beg) as [[lo1 hi1]|] eqn:Hbr; [|discriminate He].
    destruct (end_hi k beg 0 ne lo1 hi1 nhi) as [e|] eqn:Hh; [|discriminate He]. apply Z.leb_le in He.
    right. exists lo1, hi1, e. split; [reflexivity|]. split; [exact Hh| exact He].
Qed.
Lemma side_ok_sound : forall E M k beg ne blo bhi nhi,
  know_ok SEGS E M k -> RPN.side_ok k beg ne blo bhi nhi = true ->
  xlo k beg = Some blo -> xhi k beg = Some bhi -> xhi k ne = Some nhi ->
  (bv_unsigned (edenot E beg) + bv_unsigned (edenot E ne) <= RPN.kLowEnd
   \/ (RPN.kHighBeg <= bv_unsigned (edenot E beg) /\ bv_unsigned (edenot E beg) + bv_unsigned (edenot E ne) <= RPN.kHighEnd))
  /\ bv_unsigned (edenot E beg) + nhi <= 2 ^ 64.
Proof.
  intros E M k beg ne blo bhi nhi HK H Hblo Hbhi Hnhi.
  pose proof (xlo_sound SEGS E M k _ _ HK Hblo) as L1. pose proof (xhi_sound SEGS E M k _ _ HK Hbhi) as L2.
  pose proof (xhi_sound SEGS E M k _ _ HK Hnhi) as L3.
  pose proof (u64_range (edenot E beg)) as Rb. pose proof (u64_range (edenot E ne)) as Rn.
  apply side_ok_cases in H. destruct H as [Hnum | (Hb47 & Hn47 & Hap & Hend)].
  - clear HK Hblo Hbhi Hnhi. unfold RPN.kLowEnd, RPN.kHighBeg, RPN.kHighEnd in *. lia.
  - assert (END : bv_unsigned (edenot E beg) + bv_unsigned (edenot E ne) <= RPN.kHighEnd).
    { destruct Hend as [He | (lo1 & hi1 & e & Hbr & Hh & He)]; [lia|].
      pose proof (end_hi_sound SEGS E M k beg 0 ne lo1 hi1 nhi e HK Hbr Hnhi Hh) as EH.
      unfold estart, elenZ in EH. cbn [a_base a_off] in EH. lia. }
    pose proof (ranges_apart_x_sound SEGS E M k beg 0 ne (ELit RPN.kLowEnd) 0 (ELit (RPN.kHighBeg - RPN.kLowEnd)) HK Hap) as AP.
    unfold estart, elenZ in AP. cbn [a_base a_off] in AP. rewrite ulit_lo, ulit_band in AP.
    clear HK Hblo Hbhi Hnhi Hap Hend. unfold RPN.kLowEnd, RPN.kHighBeg, RPN.kHighEnd in *. lia.
Qed.

Theorem node_rpoison_sound :
  forall args, node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (RPN.node_rpoison SEGS A nx0 T args).
Proof.
  intros args cs cs' E R FULL model TT HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := Mr A argH E cs model FULL) in *.
  unfold RPN.node_rpoison in Hn.
  destruct (Z.eqb (pc cs) (RPN.rp_entry T)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (split_lit (eaddz (reg cs 2) (-72))) as [qb qk] eqn:Hsq.
  destruct (xlo (kn cs) (reg cs 11)) as [nlo|] eqn:Hnlo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 11)) as [nhi|] eqn:Hnhi; [|discriminate].
  destruct (xlo (kn cs) (reg cs 10)) as [blo|] eqn:Hblo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [bhi|] eqn:Hbhi; [|discriminate].
  destruct (xlo (kn cs) (reg cs 2)) as [splo|] eqn:Hsplo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 2)) as [sphi|] eqn:Hsphi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond Lhi]. apply andb_prop in Hcond as [Hcond Lsb].
  apply andb_prop in Hcond as [Hcond Icm2]. apply andb_prop in Hcond as [Hcond Icm1].
  apply andb_prop in Hcond as [Hcond Ighi]. apply andb_prop in Hcond as [Hcond Igm2].
  apply andb_prop in Hcond as [Hcond Igm1]. apply andb_prop in Hcond as [Hcond Igsb].
  apply andb_prop in Hcond as [Hcond Hrs].
  apply andb_prop in Hcond as [Hcond Hflq]. apply andb_prop in Hcond as [Hcond Hwr].
  apply andb_prop in Hcond as [Hcond B8]. apply andb_prop in Hcond as [Hcond B7]. apply andb_prop in Hcond as [Hcond B6]. apply andb_prop in Hcond as [Hcond B5].
  apply andb_prop in Hcond as [Hcond B4]. apply andb_prop in Hcond as [Hcond B3]. apply andb_prop in Hcond as [Hcond B2]. apply andb_prop in Hcond as [Hcond B1].
  apply andb_prop in Hcond as [Hcond P8]. apply andb_prop in Hcond as [Hcond P7]. apply andb_prop in Hcond as [Hcond P6]. apply andb_prop in Hcond as [Hcond P5].
  apply andb_prop in Hcond as [Hcond P4]. apply andb_prop in Hcond as [Hcond P3]. apply andb_prop in Hcond as [Hcond P2]. apply andb_prop in Hcond as [Hcond P1].
  apply andb_prop in Hcond as [Hcond Hdisj]. apply andb_prop in Hcond as [Hcond Hsphi']. apply andb_prop in Hcond as [Hcond Hsplo'].
  apply andb_prop in Hcond as [Hcond Hrng].
  apply andb_prop in Hcond as [Hn16 Hn40].
  apply Z.leb_le in Hn16. apply Z.leb_le in Hn40. apply Z.leb_le in Hsplo'. apply Z.ltb_lt in Hsphi'. apply Z.ltb_lt in Hdisj.
  apply Z.leb_le in P1. apply Z.leb_le in P2. apply Z.leb_le in P3. apply Z.leb_le in P4. apply Z.leb_le in P5. apply Z.leb_le in P6. apply Z.leb_le in P7. apply Z.leb_le in P8.
  apply Z.leb_le in B1. apply Z.leb_le in B2. apply Z.leb_le in B3. apply Z.leb_le in B4. apply Z.leb_le in B5. apply Z.leb_le in B6. apply Z.leb_le in B7. apply Z.leb_le in B8.
  unfold two64 in Hsphi'.
  (* [comment removed for export] *)
  destruct (ret_lit_sound SEGS A LIMIT SINV argH LINV FS0 E cs R FULL model ret HC Hret) as (R1 & Hrok & Hretr).
  pose proof (w_reg_sound SEGS A LIMIT SINV argH LINV FS0 E cs R FULL model 2 HC ltac:(lia)) as R2.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH LINV FS0 E cs R FULL model 10 HC ltac:(lia)) as R10.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH LINV FS0 E cs R FULL model 11 HC ltac:(lia)) as R11.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Hnlo2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Hnhi2.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hblo) as Hblo2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hbhi) as Hbhi2.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hsplo) as Hsplo2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hsphi) as Hsphi2.
  set (begw := edenot E (reg cs 10)) in *. set (spw := edenot E (reg cs 2)) in *. set (nw := edenot E (reg cs 11)) in *.
  set (n := bv_unsigned nw) in *. set (usp := bv_unsigned spw) in *. set (beg := bv_unsigned begw) in *.
  pose proof (u64_range nw) as Hnr. fold n in Hnr. pose proof (u64_range begw) as Hbr. fold beg in Hbr.
  pose proof (u64_range spw) as Hsr. fold usp in Hsr.
  assert (HnwN : Z_to_bv 64 n = nw) by (apply Z_to_bv_bv_unsigned).
  assert (HspW : Z_to_bv 64 usp = spw) by (apply Z_to_bv_bv_unsigned).
  assert (HbgW : Z_to_bv 64 beg = begw) by (apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  pose proof (w_split_lit_denot E _ qb qk Hsq) as Hq.
  unfold eaddz in Hq. rewrite mkAlu_denot in Hq. cbn [edenot] in Hq. fold spw in Hq.
  destruct (kwritable_sound SEGS A E M (kn cs) (kn cs) qb qk 72 HKN HKN Hwr ltac:(lia)) as (Qst & Qlo & Qhi).
  set (Q := estart E (SA qb qk)) in *.
  assert (HQ : Q = usp - 72).
  { apply (f_equal bv_unsigned) in Hq. rewrite (u_spw_sub72 spw) in Hq by lia. fold usp in Hq.
    rewrite u_lit64 in Hq. unfold two64 in Hq. rewrite (Z.mod_small Q) in Hq by lia. lia. }
  assert (Hstk : forall a, usp - 72 <= a < usp -> store_ok SEGS M (Z_to_bv 64 a) 1 = true).
  { intros a Ha. apply store_ok_of_all; [cbn; rewrite u64_lit by lia; lia|].
    intros x Hx. eapply (store_ok_all SEGS M 72 (Z_to_bv 64 Q)); [rewrite u64_lit by lia; cbn; lia | exact Qst |].
    rewrite u64_lit in Hx |- * by lia. cbn in Hx |- *. lia. }
  (* [comment removed for export] *)
  destruct (side_ok_sound E M (kn cs) (reg cs 10) (reg cs 11) blo bhi nhi HKN Hrng Hblo Hbhi Hnhi) as [Hrng2 Hbn].
  fold begw nw in Hrng2, Hbn. fold beg n in Hrng2, Hbn. fold begw beg in Hbn.
  (* [comment removed for export] *)
  assert (A1 : 1 <= n <= nhi) by lia. assert (A2 : nhi <= 2 ^ 40) by lia. assert (A3 : beg + nhi <= 2 ^ 64) by lia.
  destruct (region_shadow_sound E M (kn cs) args (reg cs 10) (reg cs 11) nhi HKN Hrs A1 A2 A3) as [Hz Hlast].
  fold begw nw in Hz, Hlast. fold beg n in Hz, Hlast. destruct Hlast as (b1 & Hb1 & Hb1v).
  (* [comment removed for export] *)
  pose proof (img8_sound E M (kn cs) _ _ HKN Igsb (ri_gsb _ _ IMG)) as C1.
  pose proof (lit_cell_sound E M (kn cs) _ _ HKN B5 Lsb) as C2.
  pose proof (img8_sound E M (kn cs) _ _ HKN Igm1 (ri_gm1 _ _ IMG)) as C3.
  pose proof (img8_sound E M (kn cs) _ _ HKN Icm1 (ri_cm1 _ _ IMG)) as C4.
  pose proof (img8_sound E M (kn cs) _ _ HKN Igm2 (ri_gm2 _ _ IMG)) as C5.
  pose proof (img8_sound E M (kn cs) _ _ HKN Icm2 (ri_cm2 _ _ IMG)) as C6.
  pose proof (img8_sound E M (kn cs) _ _ HKN Ighi (ri_ghi _ _ IMG)) as C7.
  pose proof (lit_cell_sound E M (kn cs) _ _ HKN B8 Lhi) as C8.
  (* [comment removed for export] *)
  destruct (SPEC M beg n usp R (Z_to_bv 64 ret) ltac:(lia) ltac:(lia) Hrng2 ltac:(lia) ltac:(lia) Hz b1 Hb1 Hb1v Hstk
              C1 C2 C3 C4 C5 C6 C7 C8 Hrok R1 ltac:(rewrite HspW; exact R2) ltac:(rewrite HbgW; exact R10) ltac:(rewrite HnwN; exact R11))
    as (regs' & M' & Hms & Hkept & Ha0 & Hout & Hgr).
  eapply (call_node_sound SEGS A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SINV argH LINV argH_high argH_agree nx0_ge SINV_frame SINV_agree LINV_frame FS0
            cs cs' E R FULL model TT ret (Some (ELit 0)) _ regs' M' HC Hn).
  - rewrite Hpc. exact Hms.
  - exact Hkept.
  - cbn [edenot]. exact Ha0.
  - eapply w_know_ok_havoc; [exact HKN | | exact Hgr].
    intros x Hx. change (estart E (SA qb qk)) with Q in Hx.
    replace (elenZ E (ELit 72)) with 72 in Hx by (unfold elenZ; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
    apply Hout. lia.
  - (* [comment removed for export] *)
    intros a Ha. apply Hout. pose proof (kwritable_lfp SEGS A E M (kn cs) (kn cs) qb qk 72 HKN Hwr (bv_unsigned a) Ha) as X.
    change (estart E (SA qb qk)) with Q in X. lia.
  - exact Hk.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


(* [comment removed for export] *)
Lemma v_addi_as_add : forall (x : word) i, v_addi x i = Sem.alu64 ALU_ADD x (Z_to_bv 64 i).
Proof.
  intros x i. rewrite alu_add. unfold v_add, v_addi. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

Lemma nth_rc_regs : forall sr e1 e2 e3 e20 i,
  nth i (RPN.rc_regs sr e1 e2 e3 e20) (ELit 0) =
  if Nat.eqb i 20 then e20 else if Nat.eqb i 15 then ELit 0 else if Nat.eqb i 14 then ELit 0
  else if Nat.eqb i 13 then e3 else if Nat.eqb i 12 then e2 else if Nat.eqb i 11 then e1 else nth i sr (ELit 0).
Proof.
  intros. unfold RPN.rc_regs.
  rewrite (nth_sr_upd 20). destruct (Nat.eqb i 20); [reflexivity|].
  rewrite (nth_sr_upd 15). destruct (Nat.eqb i 15); [reflexivity|].
  rewrite (nth_sr_upd 14). destruct (Nat.eqb i 14); [reflexivity|].
  rewrite (nth_sr_upd 13). destruct (Nat.eqb i 13); [reflexivity|].
  rewrite (nth_sr_upd 12). destruct (Nat.eqb i 12); [reflexivity|].
  rewrite (nth_sr_upd 11). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma v_add_zbv_mod : forall a b, v_add (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b. unfold v_add. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite <- Z.add_mod by lia. reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Theorem node_readcheck_sound :
  node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (RPN.node_readcheck SEGS nx0 T).
Proof.
  intros cs cs' E R FULL model TT HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := Mr A argH E cs model FULL) in *.
  unfold RPN.node_readcheck in Hn.
  destruct (Z.eqb (pc cs) (RPN.rc_entry T)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (split_lit (reg cs 9)) as [bb bk] eqn:Hsb.
  destruct (split_lit (eadd (ELit (RPN.SB + bk / 8 - (RPN.SB + bk / 8) mod 8)) (mkSrl (kn cs) bb 3))) as [hb hk] eqn:Hsh.
  destruct (xlo (kn cs) (reg cs 10)) as [rlo|] eqn:Hrlo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [rhi|] eqn:Hrhi; [|discriminate].
  destruct (xhi (kn cs) (reg cs 9)) as [dhi|] eqn:Hdhi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Lsb]. apply andb_prop in Hcond as [Hcond Igsb].
  apply andb_prop in Hcond as [Hcond B2]. apply andb_prop in Hcond as [Hcond B1].
  apply andb_prop in Hcond as [Hcond Hkz]. apply andb_prop in Hcond as [Hcond Hflh].
  apply andb_prop in Hcond as [Hcond Hfresh]. apply andb_prop in Hcond as [Hcond Hflb]. apply andb_prop in Hcond as [Hcond Hal].
  apply andb_prop in Hcond as [Hcond Hd64]. apply andb_prop in Hcond as [Hr1 Hr64].
  apply Z.leb_le in Hr1. apply Z.leb_le in Hr64. apply Z.ltb_lt in Hd64. apply Z.leb_le in Hal. apply Z.leb_le in B1. apply Z.leb_le in B2.
  unfold two64 in Hd64. injection Hn as <-.
  (* [comment removed for export] *)
  pose proof (w_reg_sound SEGS A LIMIT SINV argH LINV FS0 E cs R FULL model 9 HC ltac:(lia)) as R9.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH LINV FS0 E cs R FULL model 10 HC ltac:(lia)) as R10.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH LINV FS0 E cs R FULL model 8 HC ltac:(lia)) as R8.
  replace (Z_to_bv 5 (Z.of_nat 8)) with (8%bv : bv 5) in R8 by (apply bv_eq; reflexivity).
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hrlo) as Hrlo2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hrhi) as Hrhi2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hdhi) as Hdhi2.
  set (dw := edenot E (reg cs 9)) in *. set (rw := edenot E (reg cs 10)) in *.
  set (buf := bv_unsigned dw) in *. set (res := bv_unsigned rw) in *.
  pose proof (u64_range dw) as Hbr. fold buf in Hbr. pose proof (u64_range rw) as Hrr. fold res in Hrr.
  assert (HdwB : Z_to_bv 64 buf = dw) by (apply Z_to_bv_bv_unsigned).
  assert (HrwR : Z_to_bv 64 res = rw) by (apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  pose proof (w_split_lit_denot E (reg cs 9) bb bk Hsb) as Hbeg. fold dw in Hbeg.
  destruct (flat_x_sound SEGS E M (kn cs) bb bk (ELit 1) HKN Hflb) as (Blo & Bhi & _).
  set (bbu := bv_unsigned (edenot E bb)) in *.
  replace (bv_unsigned (edenot E (ELit 1))) with 1 in Bhi by (cbn [edenot]; rewrite u64_lit by lia; reflexivity).
  assert (HuB : buf = bbu + bk).
  { unfold buf. rewrite Hbeg. unfold estart in Blo, Bhi. cbn [a_base a_off] in Blo, Bhi. fold bbu in Blo, Bhi. apply u64_lit. lia. }
  destruct (ealign_sound SEGS E M (kn cs) bb HKN) as [Hea1 Hea2]. fold bbu in Hea2.
  assert (Hal64 : exists q, bbu = 64 * q).
  { destruct Hea2 as [q Hq8]. exists (q * 2 ^ (ealign (kn cs) bb - 6)). rewrite Hq8.
    replace (ealign (kn cs) bb) with ((ealign (kn cs) bb - 6) + 6) at 1 by lia.
    rewrite Z.pow_add_r by lia. change (2 ^ 6) with 64. lia. }
  destruct Hal64 as [q Hq64].
  assert (Hdiv4 : bbu / 8 = 8 * q) by (rewrite Hq64; replace (64 * q) with (8 * q * 8) by lia; apply Z.div_mul; lia).
  assert (Hdiv1 : buf / 8 = 8 * q + bk / 8).
  { rewrite HuB, Hq64. replace (64 * q + bk) with (8 * q * 8 + bk) by lia. rewrite Z.div_add_l by lia. reflexivity. }
  (* [comment removed for export] *)
  pose proof (w_split_lit_denot E _ hb hk Hsh) as Hsa.
  unfold eadd in Hsa. rewrite mkAlu_denot in Hsa.
  rewrite (mkSrl_denot SEGS E M (kn cs) bb 3 (Z_to_bv 64 3) HKN ltac:(rewrite u64_lit by lia; reflexivity)) in Hsa.
  rewrite (srl3_div8 (edenot E bb) (Z_to_bv 64 3)) in Hsa by (rewrite u64_lit by lia; reflexivity). fold bbu in Hsa.
  cbn [edenot] in Hsa. rewrite alu_add in Hsa. unfold v_add in Hsa.
  destruct (kzero_x_sound SEGS E M (kn cs) (kn cs) hb hk (ELit 16) HKN HKN Hkz) as (Zb & Hlo' & Hhi').
  set (H := estart E (SA hb hk)) in *.
  change (bv_unsigned (edenot E hb) + hk) with H in Hsa.
  replace (elenZ E (ELit 16)) with 16 in Zb, Hhi' by (unfold elenZ; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
  pose proof (Z.mod_pos_bound (RPN.SB + bk / 8) 8 ltac:(lia)) as Hm.
  assert (HH : H = (RPN.SB + buf / 8) / 8 * 8).
  { apply (f_equal bv_unsigned) in Hsa. rewrite Hdiv4 in Hsa.
    rewrite !u_lit64 in Hsa. unfold two64 in Hsa. rewrite Hdiv1. unfold RPN.SB in *.
    rewrite <- Z.add_mod in Hsa by lia.
    rewrite (Z.mod_small (2147450880 + bk / 8 - (2147450880 + bk / 8) mod 8 + 8 * q)) in Hsa by lia.
    rewrite (Z.mod_small H) in Hsa by lia. lia. }
  assert (Hz : forall j, 0 <= j < 16 -> M (Z_to_bv 64 ((RPN.SB + buf / 8) / 8 * 8 + j)) = Some (Z_to_bv 8 0)).
  { intros j Hj. rewrite <- HH. apply Zb. lia. }
  (* [comment removed for export] *)
  pose proof (img8_sound E M (kn cs) _ _ HKN Igsb (ri_gsb _ _ IMG)) as C1.
  pose proof (lit_cell_sound E M (kn cs) _ _ HKN B2 Lsb) as C2.
  (* [comment removed for export] *)
  destruct (RSPEC M (seg_rom SEGS) buf res R ltac:(lia) ltac:(lia) ltac:(lia) C1 C2 Hz
              ltac:(rewrite HdwB; exact R9) ltac:(rewrite HrwR; exact R10))
    as (regs' & Hms & P11 & P12 & P13 & P14 & P15 & P20 & Pother).
  lazymatch type of Hk with context [mk_ss _ ?sr _ _] =>
    eapply (call_core SEGS A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SINV argH LINV argH_high argH_agree nx0_ge SINV_frame SINV_agree LINV_frame FS0
              cs E E R FULL model TT (RPN.rc_exit T) sr (kn cs) (nxt cs) regs' M HC Hfresh (env_agree_refl _ E))
  end.
  - rewrite Hpc. exact Hms.
  - (* [comment removed for export] *)
    apply regs_ok_pointwise. intros r Hr0.
    pose proof (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC) as HR.
    assert (HRr : forall r' : bv 5, r' <> 0%bv -> getr R r' = edenot E (nth (ridx r') (s_regs (a_ss cs)) (ELit 0))).
    { intros r' Hr'. rewrite (HR r'). unfold sr_get. destruct (bv_eqb r' 0%bv) eqn:E0; [|reflexivity].
      exfalso. apply Hr'. apply bv_eq. unfold bv_eqb in E0. apply Z.eqb_eq in E0. exact E0. }
    cbn [s_regs mk_ss]. rewrite nth_rc_regs.
    assert (RX : forall n (rb : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned rb -> Nat.eqb (ridx r) n = true -> r = rb).
    { intros n rb Hn Hrb E1. apply Nat.eqb_eq in E1. rewrite (reg_of_ridx r n E1). apply bv_eq.
      rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. exact Hrb. }
    destruct (Nat.eqb (ridx r) 20) eqn:E20; [apply (RX 20%nat 20%bv ltac:(lia) eq_refl) in E20; subst r|].
    { rewrite P20, R8. unfold eaddz. do 2 rewrite mkAlu_denot. cbn [edenot]. do 2 rewrite v_addi_as_add. reflexivity. }
    destruct (Nat.eqb (ridx r) 15) eqn:E15; [apply (RX 15%nat 15%bv ltac:(lia) eq_refl) in E15; subst r; rewrite P15; reflexivity|].
    destruct (Nat.eqb (ridx r) 14) eqn:E14; [apply (RX 14%nat 14%bv ltac:(lia) eq_refl) in E14; subst r; rewrite P14; reflexivity|].
    destruct (Nat.eqb (ridx r) 13) eqn:E13; [apply (RX 13%nat 13%bv ltac:(lia) eq_refl) in E13; subst r|].
    { rewrite P13. unfold eaddz, eadd. do 2 rewrite mkAlu_denot. cbn [edenot]. fold dw rw. rewrite <- HdwB, <- HrwR.
      rewrite <- v_addi_as_add. rewrite alu_add. rewrite v_add_zbv by lia. rewrite v_addi_zbv by lia. first [reflexivity | f_equal; lia]. }
    destruct (Nat.eqb (ridx r) 12) eqn:E12; [apply (RX 12%nat 12%bv ltac:(lia) eq_refl) in E12; subst r|].
    { rewrite P12. unfold eadd, eaddz. rewrite mkAlu_denot.
      rewrite (mkSrl_denot SEGS E M (kn cs) _ 3 (Z_to_bv 64 3) HKN ltac:(rewrite u64_lit by lia; reflexivity)).
      do 2 rewrite mkAlu_denot. cbn [edenot]. fold dw rw. rewrite <- HdwB, <- HrwR.
      rewrite <- (v_addi_as_add (Sem.alu64 ALU_ADD (Z_to_bv 64 buf) (Z_to_bv 64 res))).
      rewrite (alu_add (Z_to_bv 64 buf)). rewrite (v_add_zbv buf res) by lia. rewrite v_addi_zbv by lia.
      replace (buf + res + -1) with (buf + res - 1) by lia.
      rewrite (srl3_div8 _ (Z_to_bv 64 3)) by (rewrite u64_lit by lia; reflexivity). rewrite zbv_u by lia.
      rewrite alu_add. rewrite v_add_zbv_mod. reflexivity. }
    destruct (Nat.eqb (ridx r) 11) eqn:E11; [apply (RX 11%nat 11%bv ltac:(lia) eq_refl) in E11; subst r|].
    { rewrite P11. unfold eadd. rewrite mkAlu_denot.
      rewrite (mkSrl_denot SEGS E M (kn cs) bb 3 (Z_to_bv 64 3) HKN ltac:(rewrite u64_lit by lia; reflexivity)).
      rewrite (srl3_div8 (edenot E bb) (Z_to_bv 64 3)) by (rewrite u64_lit by lia; reflexivity). fold bbu. rewrite Hdiv4.
      cbn [edenot]. rewrite alu_add, v_add_zbv_mod. rewrite Hdiv1. apply (f_equal (Z_to_bv 64)). lia. }
    rewrite Pother; [apply HRr; exact Hr0
                   | intros ->; cbv in E11; discriminate E11 | intros ->; cbv in E12; discriminate E12
                   | intros ->; cbv in E13; discriminate E13 | intros ->; cbv in E14; discriminate E14
                   | intros ->; cbv in E15; discriminate E15 | intros ->; cbv in E20; discriminate E20 ].
  - exact HKN.
  - intros a Ha. reflexivity.
  - intros R' FULL' model' HC' Hfs'. apply (Hk E R' FULL' model' (conj (env_agree_refl _ E) (env_agree_refl _ E)) HC' Hfs').
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition msb_spec (SEGS : list Segment) (T : RPN.rptab) : Prop :=
  forall mem (rom : word -> option byte) (s1 wz : Z) (bs : list byte) (regs : bvmap 5 word),
    0 <= s1 -> s1 + 56 < 2 ^ 64 ->
    rdn SEGS mem (Z_to_bv 64 (s1 + 48)) 8 = Some bs -> bytes_le_to_Z bs = wz -> 0 <= wz < 2 ^ 64 ->
    getr regs (Z_to_bv 5 9) = Z_to_bv 64 s1 ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 (RPN.msb_entry T)) mem rom) (mkst regs' (Z_to_bv 64 (RPN.msb_exit T)) mem rom)
      /\ getr regs' (Z_to_bv 5 19) = snd (RPN.msb_regs (getr regs (Z_to_bv 5 18)) (Z_to_bv 64 wz))
      /\ getr regs' (Z_to_bv 5 14) = Z_to_bv 64 wz
      /\ (forall r : bv 5, r <> (Z_to_bv 5 11) -> r <> (Z_to_bv 5 12) -> r <> (Z_to_bv 5 14) -> r <> (Z_to_bv 5 15) -> r <> (Z_to_bv 5 16) -> r <> (Z_to_bv 5 19) -> getr regs' r = getr regs r).
(* [comment removed for export] *)
Definition ls_spec (SEGS : list Segment) (T : RPN.rptab) : Prop :=
  forall mem (rom : word -> option byte) (s1 idx : Z) (regs : bvmap 5 word),
    0 <= s1 -> s1 + 616 < 2 ^ 64 -> 0 <= idx <= 63 ->
    (forall j, 0 <= j < 520 -> store_ok SEGS mem (Z_to_bv 64 (s1 + 96 + j)) 1 = true) ->
    (forall a, s1 + 96 <= a -> a + 8 <= s1 + 616 -> exists bs, rdn SEGS mem (Z_to_bv 64 a) 8 = Some bs /\ length bs = 8%nat) ->
    getr regs (Z_to_bv 5 9) = Z_to_bv 64 s1 -> getr regs (Z_to_bv 5 11) = Z_to_bv 64 idx ->
    exists regs' mem',
      msteps SEGS (mkst regs (Z_to_bv 64 (RPN.ls_entry T)) mem rom) (mkst regs' (Z_to_bv 64 (RPN.ls_exit T)) mem' rom)
      /\ (forall r : bv 5, r <> (Z_to_bv 5 11) -> r <> (Z_to_bv 5 12) -> r <> (Z_to_bv 5 13) -> getr regs' r = getr regs r)
      /\ (exists v1 v2 : word, mem' = wbytes (wbytes mem (Z_to_bv 64 (s1 + 96)) (word_to_le_bytes 8 v1))
                                              (Z_to_bv 64 (s1 + 104 + 8 * idx)) (word_to_le_bytes 8 v2)).

Definition qc_spec (SEGS : list Segment) (T : RPN.rptab) (qe qx : Z) (rb rs : bv 5) : Prop :=
  forall mem (rom : word -> option byte) (beg n : Z) (b1 : byte) (regs : bvmap 5 word),
    1 <= n <= 64 -> 0 <= beg -> beg + 64 < 2 ^ 64 ->
    cell8 SEGS mem (RPN.rp_gsb T) (RPN.rp_csb T) -> cell8 SEGS mem (RPN.rp_csb T) RPN.SB ->
    (forall a, (RPN.SB + beg / 8) / 8 * 8 <= a < (RPN.SB + (beg + n - 1) / 8) / 8 * 8 + 8 ->
               exists c, rdn SEGS mem (Z_to_bv 64 a) 1 = Some [c]) ->
    (forall g, beg / 8 <= g < (beg + n - 1) / 8 -> mem (Z_to_bv 64 (RPN.SB + g)) = Some (Z_to_bv 8 0)) ->
    mem (Z_to_bv 64 (RPN.SB + (beg + n - 1) / 8)) = Some b1 ->
    (bv_unsigned b1 = 0 \/ (beg + n - 1) mod 8 < bv_unsigned b1 < 128) ->
    getr regs rb = Z_to_bv 64 beg -> getr regs 12%bv = Z_to_bv 64 n -> getr regs rs = Z_to_bv 64 (beg + n) ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 qe) mem rom) (mkst regs' (Z_to_bv 64 qx) mem rom)
      /\ getr regs' rs = Z_to_bv 64 (beg + n - 1)
      /\ (forall r, r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> r <> rs -> getr regs' r = getr regs r).

Lemma nth_map_lt {X Y : Type} (f : X -> Y) (l : list X) (d : Y) (d' : X) (i : nat) :
  (i < length l)%nat -> nth i (map f l) d = f (nth i l d').
Proof. revert i; induction l as [|x l IH]; intros [|i] H; cbn in *; try lia; auto. apply IH. lia. Qed.

Lemma ridx_lit : forall m, (m < 32)%nat -> ridx (Z_to_bv 5 (Z.of_nat m)) = m.
Proof.
  intros m Hm. unfold ridx. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
  rewrite Z.mod_small by lia. apply Nat2Z.id.
Qed.

#[local] Notation QR := ([13; 14; 15; 16; 17]%nat).
Lemma QR_nodup : List.NoDup QR.
Proof. repeat (apply List.NoDup_cons; [cbn; intros H; repeat (destruct H as [H|H]; [lia|]); exact H|]). apply List.NoDup_nil. Qed.

Theorem node_quick_sound : forall (qe qx : Z) (rb rs : nat) args,
  (0 < rb < 32)%nat -> (0 < rs < 32)%nat -> ~ In rb QR -> ~ In rs QR -> rb <> rs -> rb <> 12%nat -> rs <> 12%nat ->
  qc_spec SEGS T qe qx (Z_to_bv 5 (Z.of_nat rb)) (Z_to_bv 5 (Z.of_nat rs)) ->
  node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (RPN.node_quick SEGS nx0 T qe qx rb rs args).
Proof.
  intros qe qx rb rs args Hrb Hrs Nrb Nrs Nbs Nb12 Ns12 QSPEC cs cs' E R FULL model TT HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := Mr A argH E cs model FULL) in *.
  unfold RPN.node_quick in Hn.
  destruct (Z.eqb (pc cs) qe) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (expr_eqb (reg cs rs) (mkAlu ALU_ADD (reg cs rb) (reg cs 12))) eqn:Hsum; [|discriminate]. cbn [negb] in Hn.
  apply expr_eqb_eq in Hsum.
  destruct (xlo (kn cs) (reg cs 12)) as [nlo|] eqn:Hnlo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 12)) as [nhi|] eqn:Hnhi; [|discriminate].
  destruct (xhi (kn cs) (reg cs rb)) as [bhi|] eqn:Hbhi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Hfresh]. apply andb_prop in Hcond as [Hcond Hwin]. apply andb_prop in Hcond as [Hcond Hrs'].
  apply andb_prop in Hcond as [Hcond Lsb]. apply andb_prop in Hcond as [Hcond Igsb]. apply andb_prop in Hcond as [Hcond B2].
  apply andb_prop in Hcond as [Hcond B1]. apply andb_prop in Hcond as [Hcond Hb64]. apply andb_prop in Hcond as [Hn1 Hn64].
  apply Z.leb_le in Hn1. apply Z.leb_le in Hn64. apply Z.ltb_lt in Hb64. apply Z.leb_le in B1. apply Z.leb_le in B2.
  unfold two64 in Hb64.
  destruct (node_havoc nx0 cs QR) as [cs1|] eqn:Hhv; [|discriminate]. injection Hn as <-.
  unfold node_havoc in Hhv.
  destruct (fresh_ok nx0 cs && forallb (fun r => Nat.ltb 0 r && Nat.ltb r 32) QR)%bool eqn:Hc; [|discriminate].
  injection Hhv as <-.
  destruct (w_fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  (* [comment removed for export] *)
  pose proof (w_reg_sound SEGS A LIMIT SINV argH LINV FS0 E cs R FULL model rb HC ltac:(lia)) as Rb.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH LINV FS0 E cs R FULL model 12 HC ltac:(lia)) as R12.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH LINV FS0 E cs R FULL model rs HC ltac:(lia)) as Rs.
  change (Z.of_nat 12) with 12 in R12.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Hnlo2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Hnhi2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hbhi) as Hbhi2.
  set (begw := edenot E (reg cs rb)) in *. set (nw := edenot E (reg cs 12)) in *.
  set (n := bv_unsigned nw) in *. set (beg := bv_unsigned begw) in *.
  pose proof (u64_range nw) as Hnr. fold n in Hnr. pose proof (u64_range begw) as Hbr. fold beg in Hbr.
  assert (HnwN : Z_to_bv 64 n = nw) by (apply Z_to_bv_bv_unsigned).
  assert (HbgW : Z_to_bv 64 beg = begw) by (apply Z_to_bv_bv_unsigned).
  assert (Hsumv : getr R (Z_to_bv 5 (Z.of_nat rs)) = Z_to_bv 64 (beg + n)).
  { rewrite Rs, Hsum, mkAlu_denot, alu_add. unfold v_add. fold begw nw beg n. reflexivity. }
  (* [comment removed for export] *)
  assert (A1 : 1 <= n <= nhi) by lia. assert (A2 : nhi <= 2 ^ 40) by lia. assert (A3 : beg + nhi <= 2 ^ 64) by lia.
  destruct (region_shadow_sound E M (kn cs) args (reg cs rb) (reg cs 12) nhi HKN Hrs' A1 A2 A3) as [Hz Hlast].
  fold begw nw in Hz, Hlast. fold beg n in Hz, Hlast. destruct Hlast as (b1 & Hb1 & Hb1v).
  assert (Hrdw : forall a, (RPN.SB + beg / 8) / 8 * 8 <= a < (RPN.SB + (beg + n - 1) / 8) / 8 * 8 + 8 -> readable1 M a).
  { unfold RPN.region_window_ok in Hwin.
    destruct (split_lit (reg cs rb)) as [bb bk] eqn:Hsb.
    assert (WIN : forall bb' bk' len, RPN.shadow_window_ok (kn cs) bb' bk' len = true -> 0 < len < 2 ^ 61 ->
              (let B := bv_unsigned (edenot E bb') + bk' in B <= beg /\ beg + n <= B + len) ->
              forall a, (RPN.SB + beg / 8) / 8 * 8 <= a < (RPN.SB + (beg + n - 1) / 8) / 8 * 8 + 8 -> readable1 M a).
    { intros bb' bk' len HW Hlen HB a Ha. destruct (RPN.shsplit (kn cs) bb' bk') as [hb hk] eqn:Hsh.
      destruct (shadow_window_sound E M (kn cs) bb' bk' len hb hk HKN HW Hsh Hlen) as (W0 & W1 & Hrd). cbn zeta in HB.
      apply Hrd.
      assert (G1 : (RPN.SB + (bv_unsigned (edenot E bb') + bk') / 8) / 8 <= (RPN.SB + beg / 8) / 8).
      { apply Z.div_le_mono; [lia|]. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
      assert (G2 : (RPN.SB + (beg + n - 1) / 8) / 8 <= (RPN.SB + (bv_unsigned (edenot E bb') + bk' + len - 1) / 8) / 8).
      { apply Z.div_le_mono; [lia|]. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
      lia. }
    destruct args as [|ebase [|[elen| | | | | | |] [|]]]; try discriminate.
    - apply orb_prop in Hwin as [Hwin|HUWS]; [apply orb_prop in Hwin as [Hwin|HUW]|].
      + pose proof Hwin as HW. unfold RPN.shadow_window_ok in HW. destruct (RPN.shsplit (kn cs) bb bk) as [hb hk] eqn:Hsh.
        apply andb_prop in HW as [HW _]. apply andb_prop in HW as [_ Hflb].   (* [comment removed for export] *)
        pose proof (split_beg_sound E M (kn cs) (reg cs rb) bb bk HKN Hsb Hflb) as HuB. fold begw beg in HuB.
        apply (WIN bb bk nhi Hwin ltac:(lia)). cbn zeta. lia.
      + (* [comment removed for export] *)
        intros a Ha. pose proof (ushadow_window_sound E M (kn cs) (reg cs rb) nhi HKN HUW ltac:(lia)) as UW. cbn zeta in UW.
        fold begw in UW. fold beg in UW. apply UW.
        pose proof (rd8_mono (RPN.SB + (beg + n - 1) / 8) (RPN.SB + (beg + nhi - 1) / 8) ltac:(apply Z.add_le_mono_l; apply Z.div_le_mono; lia)). lia.
      + (* [comment removed for export] *)
        intros a Ha. pose proof (ushadow_window_sym_sound E M (kn cs) (reg cs rb) (reg cs 12) HKN HUWS) as UW. cbn zeta in UW.
        fold begw nw in UW. fold beg n in UW. apply (UW ltac:(lia) ltac:(lia) a Ha).
    - destruct (split_lit ebase) as [eb ek] eqn:Hse.
      unfold RPN.region_shadow_ok in Hrs'. rewrite Hsb, Hse in Hrs'. apply andb_prop in Hrs' as [Henc _].
      destruct (enc_ok_sound E M (kn cs) (reg cs rb) (reg cs 12) nhi eb ek elen HKN Henc A1) as (C0 & C1 & C2 & C3 & C4).
      fold begw beg in C0, C1. fold nw in C1. fold n in C1.
      apply (WIN eb ek elen Hwin ltac:(lia)). cbn zeta. lia. }
  (* [comment removed for export] *)
  pose proof (img8_sound E M (kn cs) _ _ HKN Igsb (ri_gsb _ _ IMG)) as C1.
  pose proof (lit_cell_sound E M (kn cs) _ _ HKN B2 Lsb) as C2.
  (* [comment removed for export] *)
  destruct (QSPEC M (seg_rom SEGS) beg n b1 R ltac:(lia) ltac:(lia) ltac:(lia) C1 C2 Hrdw Hz Hb1 ltac:(lia)
              ltac:(rewrite HbgW; exact Rb) ltac:(rewrite HnwN; exact R12) Hsumv)
    as (regs' & Hms & Prs & Pother).
  set (vals := map (fun r => getr regs' (Z_to_bv 5 (Z.of_nat r))) QR).
  set (E' := ext_list E (nxt cs) vals).
  assert (Hag : env_agree (nxt cs) E E') by apply ext_list_agree.
  lazymatch goal with |- SpinAlg.srealizes _ _ _ =>
  eapply (call_core SEGS A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SINV argH LINV argH_high argH_agree nx0_ge SINV_frame SINV_agree LINV_frame FS0
            cs E E' R FULL model TT qx
            (sr_upd (sr_fresh (s_regs (a_ss cs)) QR (nxt cs)) rs (eaddz (mkAlu ALU_ADD (reg cs rb) (reg cs 12)) (-1)))
            (kn cs) (nxt cs + length QR)%nat regs' M HC Hfresh Hag)
  end.
  - rewrite Hpc. exact Hms.
  - (* [comment removed for export] *)
    apply regs_ok_pointwise. intros r Hr0.
    pose proof (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC) as HR.
    assert (HRr : forall r' : bv 5, r' <> 0%bv -> getr R r' = edenot E (nth (ridx r') (s_regs (a_ss cs)) (ELit 0))).
    { intros r' Hr'. rewrite (HR r'). unfold sr_get. destruct (bv_eqb r' 0%bv) eqn:E0; [|reflexivity].
      exfalso. apply Hr'. apply bv_eq. unfold bv_eqb in E0. apply Z.eqb_eq in E0. exact E0. }
    assert (OLD : forall i, (i < 32)%nat -> edenot E' (nth i (s_regs (a_ss cs)) (ELit 0)) = edenot E (nth i (s_regs (a_ss cs)) (ELit 0))).
    { intros i Hi. symmetry. apply (edenot_agree' (nxt cs)); [exact Hag|]. apply nth_sr_vars_lt'; assumption. }
    assert (RX : forall (rb' : bv 5), ridx r = ridx rb' -> r = rb').
    { intros rb' Hx. rewrite (reg_of_ridx r (ridx r) eq_refl), (reg_of_ridx rb' (ridx rb') eq_refl), Hx. reflexivity. }
    pose proof (ridx_range r) as Hrr.
    rewrite nth_sr_upd.
    destruct (Nat.eqb_spec (ridx r) rs) as [Ers|Nrs'].
    + (* [comment removed for export] *)
      assert (r = Z_to_bv 5 (Z.of_nat rs)) as -> by (apply (reg_of_ridx r rs Ers)).
      rewrite Prs. unfold eaddz. rewrite mkAlu_denot.
      rewrite <- (edenot_agree' (nxt cs) E E' (mkAlu ALU_ADD (reg cs rb) (reg cs 12)) Hag)
        by (rewrite <- Hsum; apply nth_sr_vars_lt'; [exact Fsr | lia]).
      rewrite <- Hsum, <- Rs. change (Z.of_nat rs) with (Z.of_nat rs). rewrite Hsumv. cbn [edenot].
      rewrite alu_add, v_add_zbv_mod'. apply (f_equal (Z_to_bv 64)). lia.
    + destruct (in_dec Nat.eq_dec (ridx r) QR) as [Hin|Hout].
      * (* [comment removed for export] *)
        destruct (In_nth _ _ 0%nat Hin) as (j & Hj & Hnth).
        rewrite <- Hnth at 1. rewrite (nth_sr_fresh_in QR (nxt cs) _ j QR_nodup Hj). cbn [edenot].
        unfold E'. rewrite ext_list_at by (unfold vals; rewrite length_map; exact Hj).
        unfold vals. rewrite (nth_map_lt _ _ _ 0%nat) by exact Hj. rewrite Hnth.
        rewrite <- (reg_of_ridx r (ridx r) eq_refl). reflexivity.
      * (* [comment removed for export] *)
        rewrite nth_sr_fresh_out by exact Hout. rewrite OLD by lia. rewrite <- HRr by exact Hr0.
        assert (NE : forall m, (m < 32)%nat -> ridx r <> m -> r <> Z_to_bv 5 (Z.of_nat m)).
        { intros m Hm Hne ->. apply Hne. apply ridx_lit. exact Hm. }
        apply Pother. all: try exact (NE rs ltac:(lia) Nrs').
        all: intros ->; apply Hout; cbn; tauto.
  - (* [comment removed for export] *)
    eapply know_ok_agree'; [exact Hag | exact Fkn | exact HKN].
  - intros a Ha. reflexivity.
  - intros R' FULL' model' HC' Hfs'.
    apply (Hk E' R' FULL' model'); [split; [eapply w_env_agree_le; [exact Hag | exact Fle] | exact Hag] | | exact Hfs'].
    exact HC'.
Qed.


(* [comment removed for export] *)
Definition mv_spec (SEGS' : list Segment) (T' : RPN.rptab) : Prop :=
  forall mem (rom : word -> option byte) (x : word) (regs : bvmap 5 word),
    getr regs (Z_to_bv 5 10) = x ->
    exists regs',
      msteps SEGS' (mkst regs (Z_to_bv 64 (RPN.mv_entry T')) mem rom) (mkst regs' (Z_to_bv 64 (RPN.mv_exit T')) mem rom)
      /\ getr regs' (Z_to_bv 5 10) = fst (mv_smear x) /\ getr regs' (Z_to_bv 5 15) = snd (mv_smear x)
      /\ getr regs' (Z_to_bv 5 11) = Z_to_bv 64 RPN.MV_C55 /\ getr regs' (Z_to_bv 5 12) = Z_to_bv 64 RPN.MV_C33
      /\ getr regs' (Z_to_bv 5 13) = Z_to_bv 64 RPN.MV_C0F /\ getr regs' (Z_to_bv 5 14) = Z_to_bv 64 RPN.MV_C01
      /\ (forall r : bv 5, r <> Z_to_bv 5 10 -> r <> Z_to_bv 5 11 -> r <> Z_to_bv 5 12 -> r <> Z_to_bv 5 13 -> r <> Z_to_bv 5 14 -> r <> Z_to_bv 5 15 ->
            getr regs' r = getr regs r).
Hypothesis QS : qc_spec SEGS T (RPN.qs_entry T) (RPN.qs_exit T) (Z_to_bv 5 11) (Z_to_bv 5 19).
Hypothesis QD : qc_spec SEGS T (RPN.qd_entry T) (RPN.qd_exit T) (Z_to_bv 5 10) (Z_to_bv 5 20).

Hypothesis MSPEC : msb_spec SEGS T.
Hypothesis MVSPEC : mv_spec SEGS T.   (* [comment removed for export] *)
Hypothesis LSPEC : ls_spec SEGS T.
Hypothesis SEGS_wr : segs_wr_ok SEGS.    (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma kreadZ_rdn8 : forall E M k cell z,
  know_ok SEGS E M k -> kreadZ SEGS k (ELit 0) cell 8 = Some z -> flat_x k (ELit 0) cell (ELit 8) = true -> 0 <= cell ->
  exists bs, rdn SEGS M (Z_to_bv 64 cell) 8 = Some bs /\ bytes_le_to_Z bs = z /\ 0 <= z < 2 ^ 64.
Proof.
  intros E M k cell z HK H Hfl Hc. unfold kreadZ in H.
  pose proof (know_lookup_sound SEGS E M k (ELit 0) cell 8 false [] [] HK ltac:(lia) ltac:(lia)) as Hs.
  destruct (know_lookup SEGS k (ELit 0) cell 8 false [] []) as [v scs h|scs h|]; try discriminate.
  destruct v as [z0| | | | | | |]; try discriminate. destruct scs; [|discriminate]. injection H as <-.
  destruct (flat_x_sound SEGS E M k (ELit 0) cell (ELit 8) HK Hfl) as (F0 & F1 & F2).
  assert (HCst : estart E (SA (ELit 0) cell) = cell) by (unfold estart; cbn [a_base a_off edenot]; rewrite u64_lit by lia; lia).
  replace (bv_unsigned (edenot E (ELit 8))) with 8 in F1, F2 by (cbn [edenot]; rewrite u64_lit by lia; reflexivity).
  destruct (Hs ltac:(constructor) ltac:(unfold flat; rewrite HCst; change (Z.of_nat 8) with 8; lia)) as (bs & P1 & P2 & P3).
  unfold extz in P3. cbn [edenot] in P3.
  pose proof (bytes_le_to_Z_bound bs) as Hbnd. rewrite P2 in Hbnd. change (2 ^ (8 * Z.of_nat 8%nat)) with (2 ^ 64) in Hbnd.
  pose proof (bytes_le_to_Z_nonneg bs) as Hb0.
  apply (f_equal bv_unsigned) in P3. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod in P3.
  rewrite (Z.mod_small (bytes_le_to_Z bs)) in P3 by lia.
  exists bs. rewrite adenot_SA, HCst in P1. split; [exact P1|]. split; [|apply Z.mod_pos_bound; unfold two64; lia].
  unfold two64. rewrite P3. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma store_ok_at : forall n M (a j : Z),
  store_ok SEGS M (Z_to_bv 64 a) n = true -> 0 <= a -> 0 <= j < Z.of_nat n -> store_ok SEGS M (Z_to_bv 64 (a + j)) 1 = true.
Proof.
  induction n as [|n IH]; intros M a j H Ha Hj; [cbn in Hj; lia|].
  cbn [store_ok] in H. destruct (wview SEGS M (Z_to_bv 64 a)) as [b|] eqn:Hv; [|discriminate].
  destruct (Z.eq_dec j 0) as [->|Hj0].
  - rewrite Z.add_0_r. cbn [store_ok]. rewrite Hv. reflexivity.
  - rewrite zbv_add1 in H. replace (a + j) with (a + 1 + (j - 1)) by lia. apply (IH M (a + 1) (j - 1) H); [lia | cbn in Hj |- *; lia].
Qed.

Lemma w2l_len : forall n (v : word), length (word_to_le_bytes n v) = n.
Proof. intros. unfold word_to_le_bytes. generalize (bv_unsigned v). induction n as [|n IH]; intros z; cbn; [reflexivity|]. f_equal. apply IH. Qed.

(* [comment removed for export] *)
Lemma lxor63_small : forall x, 0 <= x <= 63 -> 0 <= Z.lxor x 63 <= 63.
Proof.
  intros x Hx.
  assert (TAB : forallb (fun n => let y := Z.lxor (Z.of_nat n) 63 in (Z.leb 0 y && Z.leb y 63)%bool) (seq 0 64) = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) TAB (Z.to_nat x) ltac:(apply in_seq; lia)) as H. cbn beta in H.
  rewrite Z2Nat.id in H by lia. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

#[local] Notation MSBR := ([11; 12; 15; 16; 19]%nat).
#[local] Notation LSR := ([11; 12; 13]%nat).
Lemma MSBR_nodup : List.NoDup MSBR. Proof. repeat constructor; cbn; intuition discriminate. Qed.
Lemma LSR_nodup : List.NoDup LSR. Proof. repeat constructor; cbn; intuition discriminate. Qed.

Theorem node_msb_sound : node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (RPN.node_msb SEGS nx0 T).
Proof.
  intros cs cs' E R FULL model TT HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := Mr A argH E cs model FULL) in *.
  unfold RPN.node_msb, RPN.MSBR in Hn.
  destruct (Z.eqb (pc cs) (RPN.msb_entry T)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (reg cs 9) as [s1| | | | | | |] eqn:Hr9; try discriminate.
  destruct (erange (kn cs) (reg cs 18)) as [[lo hi]|] eqn:Her; [|discriminate].
  destruct (kreadZ SEGS (kn cs) (ELit 0) (s1 mod two64 + 48) 8) as [nres|] eqn:Hkr; [|discriminate].
  destruct (RPN.msb_rangeF lo hi) as [[cmin cmax]|] eqn:Hmr; [|discriminate].   (* [comment removed for export] *)
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Hfresh]. apply andb_prop in Hcond as [Hcond Hfl]. apply andb_prop in Hcond as [Hcond Hs56].
  apply andb_prop in Hcond as [Hal Hs0]. apply Z.leb_le in Hal. apply Z.leb_le in Hs0. apply Z.ltb_lt in Hs56. unfold two64 in Hs56.
  destruct (node_havoc nx0 cs MSBR) as [cs1|] eqn:Hhv; [|discriminate]. injection Hn as <-.
  unfold node_havoc in Hhv.
  destruct (fresh_ok nx0 cs && forallb (fun r => Nat.ltb 0 r && Nat.ltb r 32) MSBR)%bool eqn:Hc; [|discriminate].
  injection Hhv as <-.
  destruct (w_fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (s := s1 mod two64) in *.
  (* [comment removed for export] *)
  pose proof (w_reg_sound SEGS A LIMIT SINV argH LINV FS0 E cs R FULL model 9 HC ltac:(lia)) as R9.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH LINV FS0 E cs R FULL model 18 HC ltac:(lia)) as R18.
  rewrite Hr9 in R9. cbn [edenot] in R9.
  assert (R9' : getr R (Z_to_bv 5 9) = Z_to_bv 64 s).
  { replace (Z_to_bv 5 (Z.of_nat 9)) with (Z_to_bv 5 9) in R9 by reflexivity. rewrite R9. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold s, two64. rewrite Z.mod_mod by lia. reflexivity. }
  destruct (kreadZ_rdn8 E M (kn cs) (s + 48) nres HKN Hkr Hfl ltac:(lia)) as (bs & Hrd & Hbs & Hnres).
  pose proof (erange_sound SEGS E M (kn cs) _ _ _ HKN Her) as Hx.
  destruct (ealign_sound SEGS E M (kn cs) (reg cs 18) HKN) as [_ Hdiv].
  set (x := edenot E (reg cs 18)) in *.
  assert (Hx4096 : bv_unsigned x mod 4096 = 0).
  { destruct Hdiv as [q Hq]. rewrite Hq. replace (ealign (kn cs) (reg cs 18)) with ((ealign (kn cs) (reg cs 18) - 12) + 12) by lia.
    rewrite Z.pow_add_r by lia. change (2 ^ 12) with 4096. rewrite Z.mul_assoc. apply Z.mod_mul. lia. }
  (* [comment removed for export] *)
  destruct (MSPEC M (seg_rom SEGS) s nres bs R Hs0 Hs56 Hrd Hbs Hnres R9') as (regs' & Hms & P19 & P14 & Pother).
  set (vals := map (fun r => getr regs' (Z_to_bv 5 (Z.of_nat r))) MSBR).
  set (E' := ext_list E (nxt cs) vals).
  assert (Hag : env_agree (nxt cs) E E') by apply ext_list_agree.
  lazymatch goal with |- SpinAlg.srealizes _ _ _ =>
  eapply (call_core SEGS A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SINV argH LINV argH_high argH_agree nx0_ge SINV_frame SINV_agree LINV_frame FS0
            cs E E' R FULL model TT (RPN.msb_exit T)
            (sr_upd (sr_fresh (s_regs (a_ss cs)) MSBR (nxt cs)) 14 (ELit nres))
            (KRange (EVar (nxt cs + 4)%nat) cmin cmax :: kn cs) (nxt cs + length MSBR)%nat regs' M HC Hfresh Hag)
  end.
  - rewrite Hpc. exact Hms.
  - (* [comment removed for export] *)
    apply regs_ok_pointwise. intros r Hr0.
    pose proof (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC) as HR.
    assert (HRr : forall r' : bv 5, r' <> 0%bv -> getr R r' = edenot E (nth (ridx r') (s_regs (a_ss cs)) (ELit 0))).
    { intros r' Hr'. rewrite (HR r'). unfold sr_get. destruct (bv_eqb r' 0%bv) eqn:E0; [|reflexivity].
      exfalso. apply Hr'. apply bv_eq. unfold bv_eqb in E0. apply Z.eqb_eq in E0. exact E0. }
    assert (OLD : forall i, (i < 32)%nat -> edenot E' (nth i (s_regs (a_ss cs)) (ELit 0)) = edenot E (nth i (s_regs (a_ss cs)) (ELit 0))).
    { intros i Hi. symmetry. apply (edenot_agree' (nxt cs)); [exact Hag|]. apply nth_sr_vars_lt'; assumption. }
    pose proof (ridx_range r) as Hrr.
    rewrite nth_sr_upd.
    destruct (Nat.eqb_spec (ridx r) 14) as [E14|N14].
    + assert (r = Z_to_bv 5 (Z.of_nat 14)) as -> by (apply (reg_of_ridx r 14%nat E14)). cbn [edenot].
      replace (Z_to_bv 5 (Z.of_nat 14)) with (Z_to_bv 5 14) by reflexivity. rewrite P14. apply bv_eq.
      rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite (Z.mod_small nres) by lia. reflexivity.
    + destruct (in_dec Nat.eq_dec (ridx r) MSBR) as [Hin|Hout].
      * destruct (In_nth _ _ 0%nat Hin) as (j & Hj & Hnth).
        rewrite <- Hnth at 1. rewrite (nth_sr_fresh_in MSBR (nxt cs) _ j MSBR_nodup Hj). cbn [edenot].
        unfold E'. rewrite ext_list_at by (unfold vals; rewrite length_map; exact Hj).
        unfold vals. rewrite (nth_map_lt _ _ _ 0%nat) by exact Hj. rewrite Hnth.
        rewrite <- (reg_of_ridx r (ridx r) eq_refl). reflexivity.
      * rewrite nth_sr_fresh_out by exact Hout. rewrite OLD by lia. rewrite <- HRr by exact Hr0.
        assert (NE : forall m, (m < 32)%nat -> ridx r <> m -> r <> Z_to_bv 5 (Z.of_nat m)).
        { intros m Hm Hne ->. apply Hne. apply ridx_lit. exact Hm. }
        apply Pother.
        all: first [ exact (NE 14%nat ltac:(lia) N14) | apply (NE 11%nat ltac:(lia)) | apply (NE 12%nat ltac:(lia)) | apply (NE 15%nat ltac:(lia)) | apply (NE 16%nat ltac:(lia)) | apply (NE 19%nat ltac:(lia)) | idtac ];
          try (intros X; apply Hout; rewrite X; cbn; tauto).
  - (* [comment removed for export] *)
    constructor.
    + cbn [kentry_ok edenot]. unfold E'.
      replace (nxt cs + 4)%nat with (nxt cs + 4)%nat by reflexivity.
      rewrite (ext_list_at E (nxt cs) vals 4) by (unfold vals; cbn; lia).
      unfold vals. cbn [map nth]. replace (Z_to_bv 5 (Z.of_nat 19)) with (Z_to_bv 5 19) by reflexivity. rewrite P19.
      replace (Z_to_bv 5 (Z.of_nat 18)) with (Z_to_bv 5 18) in R18 by reflexivity. rewrite R18. fold x.
      apply (msb_rangeF_sound lo hi cmin cmax x Hmr Hx Hx4096 (Z_to_bv 64 nres)).
    + eapply know_ok_agree'; [exact Hag | exact Fkn | exact HKN].
  - intros a Ha. reflexivity.
  - intros R' FULL' model' HC' Hfs'.
    apply (Hk E' R' FULL' model'); [split; [eapply w_env_agree_le; [exact Hag | exact Fle] | exact Hag] | | exact Hfs'].
    exact HC'.
Qed.

Lemma in63_sound : forall E M k e, know_ok SEGS E M k -> RPN.in63 k e = true -> 0 <= bv_unsigned (edenot E e) <= 63.
Proof.
  intros E M k e HK H. unfold RPN.in63 in H. destruct (erange k e) as [[lo hi]|] eqn:He; [|discriminate].
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (erange_sound SEGS E M k _ _ _ HK He). lia.
Qed.
Lemma idx_ok_sound : forall E M k e, know_ok SEGS E M k -> RPN.idx_ok k e = true -> 0 <= bv_unsigned (edenot E e) <= 63.
Proof.
  intros E M k e HK H. unfold RPN.idx_ok in H.
  destruct e as [| |op a b| | | | |]; try exact (in63_sound E M k _ HK H).
  destruct op; try exact (in63_sound E M k _ HK H).
  destruct b as [z| | | | | | |]; try exact (in63_sound E M k _ HK H).
  destruct (Z.eqb_spec z 63) as [->|Hne]; [|exact (in63_sound E M k _ HK H)].
  pose proof (in63_sound E M k a HK H) as Ha.
  change (edenot E (EAlu ALU_XOR a (ELit 63))) with (alu64 ALU_XOR (edenot E a) (Z_to_bv 64 63)).
  rewrite u_xor64, (u64_lit 63) by lia. apply lxor63_small. exact Ha.
Qed.

Theorem node_largestats_sound : node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (RPN.node_largestats A nx0 T).
Proof.
  intros cs cs' E R FULL model TT HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := Mr A argH E cs model FULL) in *.
  unfold RPN.node_largestats, RPN.LSR in Hn.
  destruct (Z.eqb (pc cs) (RPN.ls_entry T)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (reg cs 9) as [s1| | | | | | |] eqn:Hr9; try discriminate.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Hfresh]. apply andb_prop in Hcond as [Hcond Hfl]. apply andb_prop in Hcond as [Hcond Hwr].
  apply andb_prop in Hcond as [Hcond Hs616]. apply andb_prop in Hcond as [Hidx Hs0].
  apply Z.leb_le in Hs0. apply Z.ltb_lt in Hs616. unfold two64 in Hs616.
  destruct (node_havoc nx0 cs LSR) as [cs1|] eqn:Hhv; [|discriminate]. injection Hn as <-.
  unfold node_havoc in Hhv.
  destruct (fresh_ok nx0 cs && forallb (fun r => Nat.ltb 0 r && Nat.ltb r 32) LSR)%bool eqn:Hc; [|discriminate].
  injection Hhv as <-.
  destruct (w_fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (s := s1 mod two64) in *.
  (* [comment removed for export] *)
  pose proof (w_reg_sound SEGS A LIMIT SINV argH LINV FS0 E cs R FULL model 9 HC ltac:(lia)) as R9.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH LINV FS0 E cs R FULL model 11 HC ltac:(lia)) as R11.
  rewrite Hr9 in R9. cbn [edenot] in R9.
  assert (R9' : getr R (Z_to_bv 5 9) = Z_to_bv 64 s).
  { replace (Z_to_bv 5 (Z.of_nat 9)) with (Z_to_bv 5 9) in R9 by reflexivity. rewrite R9. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold s, two64. rewrite Z.mod_mod by lia. reflexivity. }
  (* [comment removed for export] *)
  set (iw := edenot E (reg cs 11)) in *.
  assert (Hidx' : 0 <= bv_unsigned iw <= 63) by (unfold iw; exact (idx_ok_sound E M (kn cs) (reg cs 11) HKN Hidx)).
  assert (R11' : getr R (Z_to_bv 5 11) = Z_to_bv 64 (bv_unsigned iw)).
  { replace (Z_to_bv 5 (Z.of_nat 11)) with (Z_to_bv 5 11) in R11 by reflexivity. rewrite R11. fold iw. symmetry. apply Z_to_bv_bv_unsigned. }
  (* [comment removed for export] *)
  destruct (kwritable_sound SEGS A E M (kn cs) (kn cs) (ELit 0) (s + 96) 520 HKN HKN Hwr ltac:(lia)) as (SW & W0 & W1).
  assert (HW : estart E (SA (ELit 0) (s + 96)) = s + 96) by (unfold estart; cbn [a_base a_off edenot]; rewrite u64_lit by lia; lia).
  rewrite HW in SW, W0, W1.
  assert (ST1 : forall j, 0 <= j < 520 -> store_ok SEGS M (Z_to_bv 64 (s + 96 + j)) 1 = true).
  { intros j Hj. apply (store_ok_at (Z.to_nat 520)); [exact SW | lia | lia]. }
  assert (ST8 : forall a, s + 96 <= a -> a + 8 <= s + 616 -> store_ok SEGS M (Z_to_bv 64 a) 8 = true).
  { intros a H1 H2.
    assert (GO : forall n b, 0 <= b -> (forall j, 0 <= j < Z.of_nat n -> store_ok SEGS M (Z_to_bv 64 (b + j)) 1 = true) -> store_ok SEGS M (Z_to_bv 64 b) n = true).
    { induction n as [|n IH]; intros b Hb Hby; [reflexivity|]. cbn [store_ok].
      pose proof (Hby 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. cbn [store_ok] in H0.
      destruct (wview SEGS M (Z_to_bv 64 b)); [|discriminate]. rewrite zbv_add1. apply IH; [lia|].
      intros j Hj. replace (b + 1 + j) with (b + (1 + j)) by lia. apply Hby. lia. }
    apply GO; [lia|]. intros j Hj. replace (a + j) with (s + 96 + (a - s - 96 + j)) by lia. apply ST1. cbn in Hj. lia. }
  assert (RD8 : forall a, s + 96 <= a -> a + 8 <= s + 616 -> exists bs, rdn SEGS M (Z_to_bv 64 a) 8 = Some bs /\ length bs = 8%nat).
  { intros a H1 H2. apply (store_ok_rdn SEGS SEGS_wr 8 M); [rewrite zbv_u by lia; lia | apply ST8; lia]. }
  (* [comment removed for export] *)
  destruct (LSPEC M (seg_rom SEGS) s (bv_unsigned iw) R Hs0 Hs616 Hidx' ST1 RD8 R9' R11') as (regs' & mem' & Hms & Pother & v1 & v2 & Hmem').
  set (vals := map (fun r => getr regs' (Z_to_bv 5 (Z.of_nat r))) LSR).
  set (E' := ext_list E (nxt cs) vals).
  assert (Hag : env_agree (nxt cs) E E') by apply ext_list_agree.
  assert (OUT : forall x : word, bv_unsigned x < s + 96 \/ s + 96 + 520 <= bv_unsigned x -> mem' x = M x).
  { intros x Hx. rewrite Hmem'. pose proof (u64_range x).
    rewrite wbytes_out; [| rewrite w2l_len, zbv_u by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite w2l_len, zbv_u by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
    rewrite wbytes_out; [reflexivity | rewrite w2l_len, zbv_u by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite w2l_len, zbv_u by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]. }
  lazymatch goal with |- SpinAlg.srealizes _ _ _ =>
  eapply (call_core SEGS A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SINV argH LINV argH_high argH_agree nx0_ge SINV_frame SINV_agree LINV_frame FS0
            cs E E' R FULL model TT (RPN.ls_exit T)
            (sr_fresh (s_regs (a_ss cs)) LSR (nxt cs))
            (kn_havoc (kn cs) (ELit 0) (s + 96) (ELit 520)) (nxt cs + length LSR)%nat regs' mem' HC Hfresh Hag)
  end.
  - rewrite Hpc. exact Hms.
  - (* [comment removed for export] *)
    apply regs_ok_pointwise. intros r Hr0.
    pose proof (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC) as HR.
    assert (HRr : forall r' : bv 5, r' <> 0%bv -> getr R r' = edenot E (nth (ridx r') (s_regs (a_ss cs)) (ELit 0))).
    { intros r' Hr'. rewrite (HR r'). unfold sr_get. destruct (bv_eqb r' 0%bv) eqn:E0; [|reflexivity].
      exfalso. apply Hr'. apply bv_eq. unfold bv_eqb in E0. apply Z.eqb_eq in E0. exact E0. }
    assert (OLD : forall i, (i < 32)%nat -> edenot E' (nth i (s_regs (a_ss cs)) (ELit 0)) = edenot E (nth i (s_regs (a_ss cs)) (ELit 0))).
    { intros i Hi. symmetry. apply (edenot_agree' (nxt cs)); [exact Hag|]. apply nth_sr_vars_lt'; assumption. }
    pose proof (ridx_range r) as Hrr.
    destruct (in_dec Nat.eq_dec (ridx r) LSR) as [Hin|Hout].
    + destruct (In_nth _ _ 0%nat Hin) as (j & Hj & Hnth).
      rewrite <- Hnth at 1. rewrite (nth_sr_fresh_in LSR (nxt cs) _ j LSR_nodup Hj). cbn [edenot].
      unfold E'. rewrite ext_list_at by (unfold vals; rewrite length_map; exact Hj).
      unfold vals. rewrite (nth_map_lt _ _ _ 0%nat) by exact Hj. rewrite Hnth.
      rewrite <- (reg_of_ridx r (ridx r) eq_refl). reflexivity.
    + rewrite nth_sr_fresh_out by exact Hout. rewrite OLD by lia. rewrite <- HRr by exact Hr0.
      assert (NE : forall m, (m < 32)%nat -> ridx r <> m -> r <> Z_to_bv 5 (Z.of_nat m)).
      { intros m Hm Hne ->. apply Hne. apply ridx_lit. exact Hm. }
      apply Pother; [apply (NE 11%nat ltac:(lia)) | apply (NE 12%nat ltac:(lia)) | apply (NE 13%nat ltac:(lia))]; intros X; apply Hout; rewrite X; cbn; tauto.
  - (* [comment removed for export] *)
    apply (know_ok_havoc SEGS E' M mem' (kn cs) (ELit 0) (s + 96) (ELit 520)).
    + eapply know_ok_agree'; [exact Hag | exact Fkn | exact HKN].
    + intros x Hx. apply OUT. unfold estart, elenZ in Hx. cbn [a_base a_off edenot] in Hx. rewrite !u64_lit in Hx by lia. lia.
    + rewrite Hmem'. eapply mem_grows_trans; apply wbytes_grows.
  - (* [comment removed for export] *)
    intros a Ha. apply OUT.
    pose proof (kwritable_lfp SEGS A E M (kn cs) (kn cs) (ELit 0) (s + 96) 520 HKN Hwr (bv_unsigned a) Ha) as Hl. rewrite HW in Hl. lia.
  - intros R' FULL' model' HC' Hfs'.
    apply (Hk E' R' FULL' model'); [split; [eapply w_env_agree_le; [exact Hag | exact Fle] | exact Hag] | | exact Hfs'].
    exact HC'.
Qed.

(* [comment removed for export] *)
Theorem node_maxva_sound : node1_stmt SEGS A nx0 LIMIT SINV argH LINV FS0 always (RPN.node_maxva nx0 T).
Proof.
  intros cs cs' E R FULL model TT HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := Mr A argH E cs model FULL) in *.
  unfold RPN.node_maxva in Hn.
  destruct (Z.eqb (pc cs) (RPN.mv_entry T)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (erange (kn cs) (reg cs 10)) as [[lo hi]|] eqn:Her; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end. injection Hn as <-.
  apply andb_prop in Hcond as [Hcond Hfresh]. apply andb_prop in Hcond as [Hlo Hhi]. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
  destruct (w_fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  pose proof (w_reg_sound SEGS A LIMIT SINV argH LINV FS0 E cs R FULL model 10 HC ltac:(lia)) as R10.
  pose proof (erange_sound SEGS E M (kn cs) _ _ _ HKN Her) as Hx.
  set (x := edenot E (reg cs 10)) in *.
  assert (Hxr : 2 ^ 46 <= bv_unsigned x <= 2 ^ 47 - 1) by (unfold RPN.MV_A0 in Hhi; lia).
  destruct (mv_smear_val x Hxr) as [V10 V15].
  (* [comment removed for export] *)
  destruct (MVSPEC M (seg_rom SEGS) x R ltac:(replace (Z_to_bv 5 10) with (Z_to_bv 5 (Z.of_nat 10)) by reflexivity; exact R10))
    as (regs' & Hms & P10 & P15 & P11 & P12 & P13 & P14 & Pother).
  lazymatch goal with |- SpinAlg.srealizes _ _ _ =>
  eapply (call_core SEGS A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SINV argH LINV argH_high argH_agree nx0_ge SINV_frame SINV_agree LINV_frame FS0
            cs E E R FULL model TT (RPN.mv_exit T) (RPN.mv_regs (s_regs (a_ss cs))) (kn cs) (nxt cs) regs' M HC Hfresh (env_agree_refl _ _))
  end.
  - rewrite Hpc. exact Hms.
  - (* [comment removed for export] *)
    apply regs_ok_pointwise. intros r Hr0.
    pose proof (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC) as HR.
    assert (HRr : forall r' : bv 5, r' <> 0%bv -> getr R r' = edenot E (nth (ridx r') (s_regs (a_ss cs)) (ELit 0))).
    { intros r' Hr'. rewrite (HR r'). unfold sr_get. destruct (bv_eqb r' 0%bv) eqn:E0; [|reflexivity].
      exfalso. apply Hr'. apply bv_eq. unfold bv_eqb in E0. apply Z.eqb_eq in E0. exact E0. }
    pose proof (ridx_range r) as Hrr.
    unfold RPN.mv_regs. rewrite !nth_sr_upd.
    assert (LIT : forall (m : nat) (z : Z) (P : getr regs' (Z_to_bv 5 (Z.of_nat m)) = Z_to_bv 64 z),
              Nat.eqb (ridx r) m = true -> getr regs' r = edenot E (ELit z)).
    { intros m z P Hm. apply Nat.eqb_eq in Hm. rewrite (reg_of_ridx r m Hm). cbn [edenot]. exact P. }
    destruct (Nat.eqb (ridx r) 15) eqn:N15; [apply (LIT 15%nat _ ltac:(rewrite <- V15; exact P15) N15)|].
    destruct (Nat.eqb (ridx r) 14) eqn:N14; [apply (LIT 14%nat _ P14 N14)|].
    destruct (Nat.eqb (ridx r) 13) eqn:N13; [apply (LIT 13%nat _ P13 N13)|].
    destruct (Nat.eqb (ridx r) 12) eqn:N12; [apply (LIT 12%nat _ P12 N12)|].
    destruct (Nat.eqb (ridx r) 11) eqn:N11; [apply (LIT 11%nat _ P11 N11)|].
    destruct (Nat.eqb (ridx r) 10) eqn:N10; [apply (LIT 10%nat _ ltac:(rewrite <- V10; exact P10) N10)|].
    rewrite <- HRr by exact Hr0.
    assert (NE : forall m, (m < 32)%nat -> Nat.eqb (ridx r) m = false -> r <> Z_to_bv 5 (Z.of_nat m)).
    { intros m Hm Hne ->. rewrite (ridx_lit m Hm), Nat.eqb_refl in Hne. discriminate. }
    apply Pother; first [ exact (NE 10%nat ltac:(lia) N10) | exact (NE 11%nat ltac:(lia) N11) | exact (NE 12%nat ltac:(lia) N12)
                        | exact (NE 13%nat ltac:(lia) N13) | exact (NE 14%nat ltac:(lia) N14) | exact (NE 15%nat ltac:(lia) N15) ].
  - (* [comment removed for export] *)
    exact HKN.
  - intros a Ha. reflexivity.
  - intros R' FULL' model' HC' Hfs'.
    apply (Hk E R' FULL' model'); [split; apply env_agree_refl | exact HC' | exact Hfs'].
Qed.

Theorem rp_xn_ref_sound : ext_stmt SEGS A nx0 LIMIT (RPN.xn_ref SEGS A nx0 T) SINV argH LINV FS0.
Proof.
  intros id args. unfold RPN.xn_ref.
  destruct (Nat.eqb id 100); [apply node_rpoison_sound|].
  destruct (Nat.eqb id 101); [apply node_readcheck_sound|].
  destruct (Nat.eqb id 102).
  { unfold RPN.node_quick_src. apply (node_quick_sound (RPN.qs_entry T) (RPN.qs_exit T) 11 19 args); first [exact QS | cbn; lia | cbn; tauto]. }
  destruct (Nat.eqb id 103).
  { unfold RPN.node_quick_dst. apply (node_quick_sound (RPN.qd_entry T) (RPN.qd_exit T) 10 20 args); first [exact QD | cbn; lia | cbn; tauto]. }
  destruct (Nat.eqb id 105); [apply node_msb_sound|].
  destruct (Nat.eqb id 106); [apply node_largestats_sound|].
  destruct (Nat.eqb id 107); [apply node_maxva_sound|].   (* [comment removed for export] *)
  intros cs cs' E R FULL model TT _ _ H. discriminate H.
Qed.
(* [comment removed for export] *)
Theorem rp_xn_sound : ext_stmt SEGS A nx0 LIMIT (RPN.xn SEGS A nx0 T) SINV argH LINV FS0.
Proof.
  intros id args cs cs' E R FULL model TT HC Hal Hn Hk. rewrite RPN.xn_eq in Hn.
  exact (rp_xn_ref_sound id args cs cs' E R FULL model TT HC Hal Hn Hk).
Qed.
End Sound.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End FPW_2.
(* [comment removed for export] *)
