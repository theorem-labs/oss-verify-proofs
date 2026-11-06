(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgA.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib Hoare RefMemcpyLib LibIface.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsanAcct AsanAcctShape AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanLibNode AsanPlan AsanPlanSound AsanPlanSoundSums AsanPlanSoundLib AsanPlanImages AsanPlanImagesInit
  AsanInit AsanNodesIface AsanStartup AsanMainClosed AsanNodesRP AsanNodesRPSound LibIfaceA AsanLibTab AsanLibNodeSound.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations.
Import AX2 AX2B AX2S APC AP APS APSX ALN.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition LINV_A (M : word -> option byte) : Prop := lib_statics LIBR_HULL_A LIBR_A SNAP_A M.

(* [comment removed for export] *)
Lemma LIBR_in_hull : forallb (fun r => (fst LIBR_HULL_A <=? fst r) && (snd r <=? snd LIBR_HULL_A))%bool LIBR_A = true.
Proof. vm_compute. reflexivity. Qed.
Lemma SNAP_in_hull : forallb (fun c => (fst LIBR_HULL_A <=? fst c) && (fst c <? snd LIBR_HULL_A))%bool SNAP_A = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lib_fp_ASAN : lib_fp ASAN = [LIBR_HULL_A].
Proof. reflexivity. Qed.

Lemma in_lfp_hull : forall z, in_lfp ASAN z = true <-> fst LIBR_HULL_A <= z < snd LIBR_HULL_A.
Proof.
  intros z. unfold in_lfp. rewrite lib_fp_ASAN. cbn [existsb fst snd].
  rewrite orb_false_r, andb_true_iff, Z.leb_le, Z.ltb_lt. cbn [fst snd LIBR_HULL_A]. tauto.
Qed.

Lemma in_ranges_LIBR_hull : forall a, in_ranges a LIBR_A -> fst LIBR_HULL_A <= a < snd LIBR_HULL_A.
Proof.
  intros a (r & Hin & Hr).
  pose proof (proj1 (forallb_forall _ _) LIBR_in_hull r Hin) as Y.
  apply andb_prop in Y as [Y1 Y2]. apply Z.leb_le in Y1. apply Z.leb_le in Y2. lia.
Qed.

Theorem LINV_A_stmt : LINV_STMT LINV_A.
Proof.
  split.
  - (* [comment removed for export] *)
    intros M HM. unfold LINV_A, lib_statics. split.
    + left. intros a Ha. pose proof (in_ranges_LIBR_hull a Ha) as Hh.
      pose proof (u64_range (Z_to_bv 64 a)) as _.
      apply HM. apply (proj2 (in_lfp_hull _)). rewrite u64_lit by (cbn [fst snd LIBR_HULL_A] in Hh; lia). exact Hh.
    + intros a Hh _. apply HM. apply (proj2 (in_lfp_hull _)). rewrite u64_lit by (cbn [fst snd LIBR_HULL_A] in Hh; lia). exact Hh.
  - (* [comment removed for export] *)
    intros M M' Hag [Hst Hrest]. unfold LINV_A, lib_statics.
    assert (HH : forall a, fst LIBR_HULL_A <= a < snd LIBR_HULL_A -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha. apply Hag. apply (proj2 (in_lfp_hull _)). rewrite u64_lit by (cbn [fst snd LIBR_HULL_A] in Ha; lia). exact Ha. }
    split.
    + destruct Hst as [Hp|Hs].
      * left. intros a Ha. rewrite HH by (apply in_ranges_LIBR_hull; exact Ha). apply Hp. exact Ha.
      * right. intros a b Hin. rewrite HH; [apply Hs; exact Hin|].
        pose proof (proj1 (forallb_forall _ _) SNAP_in_hull (a, b) Hin) as Y. cbn [fst snd LIBR_HULL_A] in Y.
        apply andb_prop in Y as [Y1 Y2]. apply Z.leb_le in Y1. apply Z.ltb_lt in Y2. cbn [fst snd LIBR_HULL_A]. lia.
    + intros a Ha Hn. rewrite HH by exact Ha. apply Hrest; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Notation SEGS := ASEGS.

Lemma SEGS_A_eq : SEGS_A = ASEGS.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma off_image_noseg : forall a, 0 <= a < 2 ^ 64 -> (a < img_lo ASAN \/ img_hi ASAN <= a) -> find_segment SEGS a 1 = None.
Proof.
  intros a Ha Hout. rewrite <- (u64_lit a) by lia. apply asan_in_hull.
  unfold in_hull. rewrite u64_lit by lia.
  destruct Hout as [H|H]; [apply andb_false_intro1; apply Z.leb_gt; lia | apply andb_false_intro2; apply Z.ltb_ge; lia].
Qed.

Lemma seg_rom_off : forall a, 0 <= a < 2 ^ 64 -> (a < img_lo ASAN \/ img_hi ASAN <= a) -> seg_rom SEGS (Z_to_bv 64 a) = None.
Proof.
  intros a Ha Hout. unfold seg_rom, memory_read. rewrite u64_lit by lia. change (Z.of_N 1) with 1.
  rewrite (off_image_noseg a Ha Hout). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rdn1_off : forall M a b, 0 <= a < 2 ^ 64 -> (a < img_lo ASAN \/ img_hi ASAN <= a) ->
  rdn SEGS M (Z_to_bv 64 a) 1 = Some [b] -> M (Z_to_bv 64 a) = Some b.
Proof.
  intros M a b Ha Hout H. cbn [rdn] in H. rewrite (seg_rom_off a Ha Hout) in H.
  destruct (M (Z_to_bv 64 a)) as [b'|]; [|discriminate]. cbn in H. congruence.
Qed.

(* [comment removed for export] *)
Lemma rdn_off_bytes : forall M a n bs, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (a + Z.of_nat n <= img_lo ASAN \/ img_hi ASAN <= a) ->
  rdn SEGS M (Z_to_bv 64 a) n = Some bs ->
  forall j, (j < n)%nat -> M (Z_to_bv 64 (a + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0)).
Proof.
  intros M a n bs Ha Hn Hout H j Hj.
  pose proof (APSX.rdn_nth SEGS M n (Z_to_bv 64 a) bs j ltac:(rewrite u64_lit by lia; lia) H Hj) as H1.
  rewrite u64_lit in H1 by lia. apply rdn1_off in H1; [exact H1 | lia | lia].
Qed.

(* [comment removed for export] *)
Lemma kreadZ_rdn : forall E M k b off n z,
  know_ok SEGS E M k -> kreadZ SEGS k b off n = Some z -> (1 <= n <= 8)%nat ->
  flat E (SA b off) (Z.of_nat n) ->
  rdn SEGS M (Z_to_bv 64 (estart E (SA b off))) n = Some (word_to_le_bytes n (Z_to_bv 64 z)) /\ 0 <= z < 2 ^ (8 * Z.of_nat n) /\ z < two64.
Proof.
  intros E M k b off n z HK H Hn Hfl. unfold kreadZ in H.
  pose proof (know_lookup_sound SEGS E M k b off n false [] [] HK ltac:(lia) ltac:(lia)) as Hs.
  destruct (know_lookup SEGS k b off n false [] []) as [v scs h|scs h|]; try discriminate.
  destruct v as [z0| | | | | | |]; try discriminate. destruct scs; [|discriminate]. injection H as <-.
  destruct (Hs ltac:(constructor) Hfl) as (bs & P1 & P2 & P3). unfold extz in P3. cbn [edenot] in P3.
  pose proof (bytes_le_to_Z_bound bs) as Hbnd. rewrite P2 in Hbnd.
  assert (Hlt : 2 ^ (8 * Z.of_nat n) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  apply (f_equal bv_unsigned) in P3. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod in P3.
  rewrite (Z.mod_small (bytes_le_to_Z bs)) in P3 by lia. unfold two64. rewrite <- P3.
  rewrite adenot_SA in P1.
  split; [|lia]. rewrite P1. f_equal. unfold word_to_le_bytes. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  rewrite Z.mod_small by lia. rewrite <- P2. symmetry. apply Z_to_le_bytes_lez.
Qed.

(* [comment removed for export] *)
Lemma seg_rom_memory_read : forall (a : word) b, seg_rom SEGS a = Some b -> memory_read SEGS a 1%N = Some [b].
Proof.
  intros a b H. unfold seg_rom in H.
  destruct (memory_read SEGS a 1) as [l|] eqn:Hm; [|discriminate].
  unfold memory_read in Hm.
  destruct (find_segment SEGS (bv_unsigned a) (Z.of_N 1)) as [seg|]; [|discriminate].
  destruct (seg_readable seg); [|discriminate].
  change (N.to_nat 1) with 1%nat in Hm. cbn [segment_read_bytes] in Hm.
  destruct (segment_byte_at _ _) as [b'|]; [|discriminate].
  destruct l as [|b1 [|b2 l2]]; try discriminate. congruence.
Qed.

(* [comment removed for export] *)
Lemma rdn_ro_byte : forall M (a : Z) n bs j b,
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  rdn SEGS M (Z_to_bv 64 a) n = Some bs ->
  rdn SEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs ->
  (j < n)%nat ->
  M (Z_to_bv 64 (a + Z.of_nat j)) = Some b -> memory_read SEGS (Z_to_bv 64 (a + Z.of_nat j)) 1%N = Some [b].
Proof.
  intros M a n bs j b Ha Hn HM HI Hj Hb.
  pose proof (APSX.rdn_nth SEGS M n (Z_to_bv 64 a) bs j ltac:(rewrite u64_lit by lia; lia) HM Hj) as B1.
  pose proof (APSX.rdn_nth SEGS (fun _ => None) n (Z_to_bv 64 a) bs j ltac:(rewrite u64_lit by lia; lia) HI Hj) as B2.
  rewrite u64_lit in B1, B2 by lia.
  cbn [rdn] in B1, B2. rewrite Hb in B1.
  destruct (seg_rom SEGS (Z_to_bv 64 (a + Z.of_nat j))) as [c|] eqn:Hc; [|discriminate].
  injection B1 as E1. injection B2 as E2. apply seg_rom_memory_read. rewrite Hc. congruence.
Qed.

(* [comment removed for export] *)
Lemma RO_LIBR_apart :
  forallb (fun q => forallb (fun r => (snd q <=? fst r) || (snd r <=? fst q)) RO_A)%bool LIBR_A = true.
Proof. vm_compute. reflexivity. Qed.
Lemma RO_sane : forallb (fun r => (0 <=? fst r) && (snd r <=? 2 ^ 64))%bool RO_A = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lt_ro_eq : lt_ro LIBTAB_ASAN = RO_A.     Proof. reflexivity. Qed.
Lemma lt_rt_eq : lt_rt LIBTAB_ASAN = RT_A.     Proof. reflexivity. Qed.
Lemma lt_gsh_eq : lt_gsh LIBTAB_ASAN = GSH_A.  Proof. reflexivity. Qed.
Lemma lt_tp_eq : lt_tp LIBTAB_ASAN = TP_A.     Proof. reflexivity. Qed.
Lemma lt_can_eq : lt_can LIBTAB_ASAN = CANARY_A. Proof. reflexivity. Qed.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma kread8e_rdn0 : forall E M k a v, know_ok SEGS E M k -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  kread8e SEGS k (ELit 0) a = Some v -> rdn SEGS M (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (edenot E v)).
Proof.
  intros E M k a v HK Ha0 Ha8 H. unfold kread8e in H.
  pose proof (know_lookup_sound SEGS E M k (ELit 0) a 8 false [] [] HK ltac:(lia) ltac:(lia)) as Hs.
  destruct (know_lookup SEGS k (ELit 0) a 8 false [] []) as [v' scs h|scs h|]; try discriminate.
  destruct scs; [|discriminate]. injection H as ->.
  assert (Hfl : flat E (SA (ELit 0) a) (Z.of_nat 8)) by (unfold flat, estart; cbn [a_base a_off]; rewrite edenot_lit, u_lit0; lia).
  destruct (Hs ltac:(constructor) Hfl) as (bs & P1 & P2 & P3). unfold extz in P3.
  rewrite (flat_u' E (SA (ELit 0) a) (Z.of_nat 8) Hfl) in P1 || (unfold adenot in P1; cbn [a_base a_off] in P1; rewrite edenot_lit in P1;
    unfold v_addi in P1; rewrite u_lit0 in P1 || idtac).
  match type of P1 with rdn _ _ ?x _ = _ => replace (Z_to_bv 64 a) with x by (apply bv_eq; rewrite ?Z_to_bv_unsigned, ?bv_wrap64_mod, ?u_lit0; rewrite ?Z.mod_small by lia; lia) end.
  rewrite P1, <- P3. f_equal. unfold word_to_le_bytes.
  pose proof (bytes_le_to_Z_bound bs) as Hbnd. rewrite P2 in Hbnd. change (8 * Z.of_nat 8) with 64 in Hbnd.
  rewrite Z_to_bv_unsigned, bv_wrap64_mod. rewrite Z.mod_small by lia. rewrite <- P2. symmetry. apply Z_to_le_bytes_lez.
Qed.

(* [comment removed for export] *)
Lemma ro_ok_sound : forall E M k,
  know_ok SEGS E M k -> LINV_A M -> ro_ok_b SEGS LIBTAB_ASAN ASAN k = true -> ro_ok SEGS RO_A M.
Proof.
  intros E M k HK HLINV Hro. unfold ro_ok. intros a b (r & Hin & Hr) Hb.
  unfold ro_ok_b in Hro. rewrite lt_ro_eq in Hro.
  apply (proj1 (forallb_forall _ _)) with (x := r) in Hro; [|exact Hin].
  destruct r as [lo hi]. cbn [fst snd] in Hr. unfold ro_range_ok in Hro. cbn [fst snd] in Hro.
  assert (Hlo0 : 0 <= lo /\ hi <= 2 ^ 64).
  { pose proof (proj1 (forallb_forall _ _) RO_sane (lo, hi) Hin) as Y. cbn [fst snd] in Y.
    apply andb_prop in Y as [Y1 Y2]. apply Z.leb_le in Y1. apply Z.leb_le in Y2. lia. }
  destruct (lfp_inside ASAN lo hi) eqn:Hh.
  - (* [comment removed for export] *)
    exfalso. unfold lfp_inside in Hh. rewrite lib_fp_ASAN in Hh. cbn [existsb fst snd LIBR_HULL_A] in Hh. rewrite orb_false_r in Hh.
    apply andb_prop in Hh as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    destruct HLINV as [_ HP]. cbn [fst snd LIBR_HULL_A] in HP.
    assert (HN : ~ in_ranges a LIBR_A).
    { intros Hl. destruct Hl as ([ql qh] & Hq & Ha'). cbn [fst snd] in Ha'.
      pose proof (proj1 (forallb_forall _ _) RO_LIBR_apart (ql, qh) Hq) as Y.
      apply (proj1 (forallb_forall _ _)) with (x := (lo, hi)) in Y; [|exact Hin]. cbn [fst snd] in Y.
      apply orb_prop in Y as [Y|Y]; apply Z.leb_le in Y; lia. }
    rewrite (HP a ltac:(lia) HN) in Hb. discriminate.
  - cbn [orb] in Hro. destruct (img_cov k lo hi) eqn:Hcov.
    + (* [comment removed for export] *)
      rewrite (img_cov_sound SEGS E M k lo hi HK Hcov a ltac:(lia)) in Hb. discriminate.
    + (* [comment removed for export] *)
      apply andb_prop in Hro as [Hro Heq]. apply andb_prop in Hro as [Hpos Hle8].
      apply Z.ltb_lt in Hpos. apply Z.leb_le in Hle8.
      destruct (kreadZ SEGS k (ELit 0) lo (Z.to_nat (hi - lo))) as [v|] eqn:Hkr; [|discriminate].
      destruct (img_readZ SEGS lo (Z.to_nat (hi - lo))) as [w|] eqn:Hir; [|discriminate]. apply Z.eqb_eq in Heq. subst w.
      unfold img_readZ in Hir. destruct (rdn SEGS (fun _ => None) (Z_to_bv 64 lo) (Z.to_nat (hi - lo))) as [bs|] eqn:Hbs; [|discriminate].
      injection Hir as Hv.
      destruct (kreadZ_rdn E M k (ELit 0) lo (Z.to_nat (hi - lo)) v HK Hkr ltac:(lia)
                  ltac:(unfold flat, estart; cbn [a_base a_off edenot]; rewrite u64_lit, Z2Nat.id by lia; lia)) as (HM & Hvr & _).
      unfold estart in HM. cbn [a_base a_off edenot] in HM. rewrite u64_lit, Z.add_0_l in HM by lia.
      pose proof (rdn_length _ _ _ _ _ Hbs) as Hlen.
      rewrite <- Hv, <- Hlen, (word_to_le_bytes_of_bytes bs ltac:(lia)) in HM. rewrite Hlen in HM.
      replace a with (lo + Z.of_nat (Z.to_nat (a - lo))) in Hb |- * by lia.
      eapply (rdn_ro_byte M lo (Z.to_nat (hi - lo)) bs); [lia | lia | exact HM | exact Hbs | lia | exact Hb].
Qed.

(* [comment removed for export] *)
Lemma cells_rd_sound : forall E M k l,
  know_ok SEGS E M k -> cells_ok_b SEGS k l = true -> (forall c, In c l -> 0 <= fst c < 2 ^ 64) -> rd_cells_ok l M.
Proof.
  intros E M k l HK H Hsane a b Hin.
  unfold cells_ok_b in H. apply (proj1 (forallb_forall _ _)) with (x := (a, b)) in H; [|exact Hin]. cbn [fst snd] in H.
  destruct (kreadZ SEGS k (ELit 0) a 1) as [v|] eqn:Hkr; [|discriminate]. apply Z.eqb_eq in H. subst v.
  pose proof (Hsane _ Hin) as Ha. cbn [fst] in Ha.
  destruct (kreadZ1_byte SEGS E M k (ELit 0) a b HK Hkr
              ltac:(unfold flat, estart; cbn [a_base a_off edenot]; rewrite u64_lit by lia; lia)) as [Hrd Hb].
  unfold estart in Hrd. cbn [a_base a_off edenot] in Hrd. rewrite u64_lit, Z.add_0_l in Hrd by lia.
  exists [Z_to_bv 8 b]. rewrite SEGS_A_eq. split; [exact Hrd|]. rewrite bytes_le_single, u8_lit. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma cells_ov_sound : forall E M k l,
  know_ok SEGS E M k -> cells_ok_b SEGS k l = true -> (forall c, In c l -> img_hi ASAN <= fst c < 2 ^ 64) -> cells_ok l M.
Proof.
  intros E M k l HK H Hsane a b Hin.
  unfold cells_ok_b in H. apply (proj1 (forallb_forall _ _)) with (x := (a, b)) in H; [|exact Hin]. cbn [fst snd] in H.
  destruct (kreadZ SEGS k (ELit 0) a 1) as [v|] eqn:Hkr; [|discriminate]. apply Z.eqb_eq in H. subst v.
  pose proof (Hsane _ Hin) as Ha. cbn [fst img_hi ASAN] in Ha.
  destruct (kreadZ1_byte SEGS E M k (ELit 0) a b HK Hkr
              ltac:(unfold flat, estart; cbn [a_base a_off edenot]; rewrite u64_lit by lia; lia)) as [Hrd Hb].
  unfold estart in Hrd. cbn [a_base a_off edenot] in Hrd. rewrite u64_lit, Z.add_0_l in Hrd by lia.
  unfold w64. apply (rdn1_off M a); [lia | cbn [img_lo img_hi ASAN]; lia | exact Hrd].
Qed.

(* [comment removed for export] *)
Lemma kn_readable_x_sound : forall E M k rb rk ne,
  know_ok SEGS E M k -> kn_readable_x k rb rk ne = true -> 0 < elenZ E ne ->
  flat E (SA rb rk) (elenZ E ne) /\
  forall i, 0 <= i < elenZ E ne -> exists b, rdn SEGS M (Z_to_bv 64 (estart E (SA rb rk) + i)) 1 = Some [b].
Proof.
  intros E M k rb rk ne HK H Hpos. unfold kn_readable_x in H. apply existsb_exists in H as (K & Hin & HK2).
  pose proof (proj1 (Forall_forall _ _) HK _ Hin) as KOK.
  assert (X : exists kb kk len, xinsideL k rb rk ne kb kk len = true /\ flat E (SA kb kk) (elenZ E len) /\
             forall i, 0 <= i < elenZ E len -> M (Z_to_bv 64 (estart E (SA kb kk) + i)) <> None).
  { destruct K as [| [kb kk] len |[kb kk] len bk| | | | | |[kb kk] len fc|[kb kk] len]; try discriminate;
      (exists kb, kk, len; split; [exact HK2| cbn [kentry_ok] in KOK]).
    - destruct KOK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. rewrite (Hz i Hi). discriminate.
    - destruct KOK as (Hfl & Hlen & Hz). split; [exact Hfl|]. intros i Hi. rewrite (Hz i Hi). discriminate.
    - destruct KOK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. rewrite (Hz i Hi). discriminate.
    - destruct KOK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. exact (Hz i Hi). }
  destruct X as (kb & kk & len & Hx & Hfl & Hdef).
  pose proof (xinsideL_sound SEGS E M k rb rk ne kb kk len HK Hx) as [I1 I2].
  destruct Hfl as (F1 & F2 & F3 & F4).
  split; [unfold flat; lia|].
  intros i Hi.
  destruct (M (Z_to_bv 64 (estart E (SA rb rk) + i))) as [b|] eqn:Hb.
  - exists b. apply APSX.rdn1_overlay. exact Hb.
  - exfalso. apply (Hdef (estart E (SA rb rk) + i - estart E (SA kb kk))); [lia|].
    replace (estart E (SA kb kk) + (estart E (SA rb rk) + i - estart E (SA kb kk))) with (estart E (SA rb rk) + i) by lia. exact Hb.
Qed.

(* [comment removed for export] *)
Section Cover.
  Variables (E : env) (M : word -> option byte) (b : expr).
  #[local] Notation B := (bv_unsigned (edenot E b)).
  Definition byte_readable (i : Z) : Prop :=
    0 <= B + i < 2 ^ 64 /\ exists c, rdn SEGS M (Z_to_bv 64 (B + i)) 1 = Some [c].
  Definition pieces_ok (ps : list (Z * Z)) : Prop :=
    forall lo hi, In (lo, hi) ps -> forall i, lo <= i < hi -> byte_readable i.

  #[using="Type"] Lemma piece_of_sound : forall k K lo hi,
    know_ok SEGS E M k -> In K k -> piece_of b K = Some (lo, hi) -> forall i, lo <= i < hi -> byte_readable i.
  Proof.
    intros k K lo hi HK Hin HP i Hi.
    pose proof (proj1 (Forall_forall _ _) HK _ Hin) as KOK.
    assert (OV : forall kb kk l (P : word -> Prop),
              (expr_eqb kb b && (0 <=? l) && (l <? two64))%bool = true -> Some (kk, kk + l) = Some (lo, hi) ->
              flat E (SA kb kk) (elenZ E (ELit l)) ->
              (forall i', 0 <= i' < elenZ E (ELit l) -> M (Z_to_bv 64 (estart E (SA kb kk) + i')) <> None) ->
              byte_readable i).
    { intros kb kk l _ Hc Hkl Hfl Hdef. apply andb_prop in Hc as [Hc Hl2]. apply andb_prop in Hc as [Hc Hl1].
      apply expr_eqb_eq in Hc. subst kb. apply Z.leb_le in Hl1. apply Z.ltb_lt in Hl2. unfold two64 in Hl2.
      injection Hkl as <- <-.
      assert (El : elenZ E (ELit l) = l) by (unfold elenZ; cbn [edenot]; apply u64_lit; lia). rewrite El in Hfl, Hdef.
      unfold flat, estart in Hfl. cbn [a_base a_off] in Hfl. unfold estart in Hdef. cbn [a_base a_off] in Hdef.
      split; [lia|].
      destruct (M (Z_to_bv 64 (B + i))) as [c|] eqn:Hc'.
      - exists c. apply APSX.rdn1_overlay. exact Hc'.
      - exfalso. apply (Hdef (i - kk)); [lia|]. replace (B + kk + (i - kk)) with (B + i) by lia. exact Hc'. }
    destruct K as [[kb kk] w v| [kb kk] [l| | | | | | |] |[kb kk] [l| | | | | | |] bk| | | | | |[kb kk] [l| | | | | | |] fc|[kb kk] [l| | | | | | |]];
      cbn [piece_of] in HP; try discriminate.
    - (* [comment removed for export] *)
      destruct (expr_eqb kb b) eqn:Heq; [|discriminate]. apply expr_eqb_eq in Heq. subst kb. injection HP as <- <-.
      cbn [kentry_ok] in KOK. destruct KOK as (Hw & Hfl & Hrd).
      unfold flat, estart in Hfl. cbn [a_base a_off] in Hfl. rewrite adenot_SA in Hrd. unfold estart in Hrd. cbn [a_base a_off] in Hrd.
      split; [lia|].
      pose proof (APSX.rdn_nth SEGS M w (Z_to_bv 64 (B + kk)) _ (Z.to_nat (i - kk)) ltac:(rewrite u64_lit by lia; lia) Hrd ltac:(lia)) as H1.
      rewrite u64_lit in H1 by lia. replace (B + kk + Z.of_nat (Z.to_nat (i - kk))) with (B + i) in H1 by lia.
      eexists. exact H1.
    - destruct (expr_eqb kb b && (0 <=? l) && (l <? two64))%bool eqn:Hc; [|discriminate].
      cbn [kentry_ok] in KOK. destruct KOK as [Hfl Hz]. eapply (OV kb kk l (fun _ => True) Hc HP Hfl).
      intros i' Hi'. rewrite (Hz i' Hi'). discriminate.
    - destruct (expr_eqb kb b && (0 <=? l) && (l <? two64))%bool eqn:Hc; [|discriminate].
      cbn [kentry_ok] in KOK. destruct KOK as (Hfl & Hlen & Hz). eapply (OV kb kk l (fun _ => True) Hc HP Hfl).
      intros i' Hi'. rewrite (Hz i' Hi'). discriminate.
    - destruct (expr_eqb kb b && (0 <=? l) && (l <? two64))%bool eqn:Hc; [|discriminate].
      cbn [kentry_ok] in KOK. destruct KOK as [Hfl Hz]. eapply (OV kb kk l (fun _ => True) Hc HP Hfl).
      intros i' Hi'. rewrite (Hz i' Hi'). discriminate.
    - destruct (expr_eqb kb b && (0 <=? l) && (l <? two64))%bool eqn:Hc; [|discriminate].
      cbn [kentry_ok] in KOK. destruct KOK as [Hfl Hz]. eapply (OV kb kk l (fun _ => True) Hc HP Hfl).
      intros i' Hi'. exact (Hz i' Hi').
  Qed.

  #[using="Type"] Lemma pieces_of_sound : forall k, know_ok SEGS E M k ->
    pieces_ok (flat_map (fun K => match piece_of b K with Some p => [p] | None => [] end) k).
  Proof.
    intros k HK lo hi Hin. apply in_flat_map in Hin as (K & HinK & HP).
    destruct (piece_of b K) as [p|] eqn:Hp; [|destruct HP]. destruct HP as [Hp'|[]]. subst p.
    intros i Hi. eapply piece_of_sound; eassumption.
  Qed.

  #[using="Type"] Lemma cover_step_sound : forall ps cur, pieces_ok ps ->
    forall i, cur <= i < cover_step ps cur -> byte_readable i.
  Proof.
    induction ps as [|[lo hi] r IH]; intros cur Hps i Hi; cbn [cover_step] in Hi; [lia|].
    assert (Hr : pieces_ok r) by (intros lo' hi' Hin; apply Hps; right; exact Hin).
    destruct ((lo <=? cur) && (cur <? hi))%bool eqn:Hc.
    - apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
      destruct (Z_lt_ge_dec i hi).
      + apply (Hps lo hi (or_introl eq_refl)). lia.
      + apply (IH hi Hr). lia.
    - apply (IH cur Hr). exact Hi.
  Qed.

  #[using="Type"] Lemma cover_go_sound : forall fuel ps cur stop, pieces_ok ps ->
    cover_go fuel ps cur stop = true -> forall i, cur <= i < stop -> byte_readable i.
  Proof.
    induction fuel as [|f IH]; intros ps cur stop Hps H i Hi; cbn [cover_go] in H.
    - destruct (Z.leb_spec stop cur); [lia | discriminate].
    - destruct (Z.leb_spec stop cur); [lia|].
      destruct (Z.leb_spec (cover_step ps cur) cur); [discriminate|].
      destruct (Z_lt_ge_dec i (cover_step ps cur)).
      + apply (cover_step_sound ps cur Hps). lia.
      + apply (IH ps (cover_step ps cur) stop Hps H). lia.
  Qed.

  #[using="Type"] Lemma kcover_sound : forall k off len, know_ok SEGS E M k -> kcover k b off len = true ->
    forall i, off <= i < off + len -> byte_readable i.
  Proof.
    intros k off len HK H. unfold kcover in H. eapply cover_go_sound; [apply pieces_of_sound; exact HK | exact H].
  Qed.
End Cover.

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

Lemma split_lit_0 : forall E e b, split_lit e = (b, 0) -> bv_unsigned (edenot E e) = bv_unsigned (edenot E b).
Proof.
  intros E e b Hs. pose proof (w_split_lit_denot E e b 0 Hs) as He. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in He.
  rewrite He. reflexivity.
Qed.

Lemma u_eaddz_neg : forall E e z, 0 <= z -> z <= bv_unsigned (edenot E e) ->
  bv_unsigned (edenot E (eaddz e (- z))) = bv_unsigned (edenot E e) - z.
Proof.
  intros E e z Hz Hle. unfold eaddz. rewrite mkAlu_denot, alu_add. unfold v_add. cbn [edenot].
  pose proof (u64_range (edenot E e)) as Hr.
  rewrite (u_lit64 (- z)). unfold two64.
  destruct (Z.eq_dec z 0) as [->|Hnz].
  - rewrite Z.mod_0_l by lia. rewrite Z.add_0_r, Z.sub_0_r. apply u64_lit. lia.
  - replace ((- z) mod 2 ^ 64) with (2 ^ 64 - z).
    2: { symmetry. rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia. }
    replace (bv_unsigned (edenot E e) + (2 ^ 64 - z)) with ((bv_unsigned (edenot E e) - z) + 1 * 2 ^ 64) by lia.
    rewrite u_lit64. unfold two64. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma u_eaddz_pos : forall E e z, 0 <= z -> bv_unsigned (edenot E e) + z < 2 ^ 64 ->
  bv_unsigned (edenot E (mkAlu ALU_ADD e (ELit z))) = bv_unsigned (edenot E e) + z.
Proof.
  intros E e z Hz Hlt. rewrite mkAlu_denot, alu_add. unfold v_add. cbn [edenot].
  pose proof (u64_range (edenot E e)) as Hr. rewrite (u64_lit z) by lia. apply u64_lit. lia.
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

Lemma srl3_div8 : forall (x y : word), bv_unsigned y mod 64 = 3 -> alu64 ALU_SRL x y = Z_to_bv 64 (bv_unsigned x / 8).
Proof.
  intros x y Hy. rewrite alu_srl. unfold v_srl. rewrite Hy. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma u_mkSrl3 : forall E M k e, know_ok SEGS E M k ->
  bv_unsigned (edenot E (mkSrl k e 3)) = bv_unsigned (edenot E e) / 8.
Proof.
  intros E M k e HK. pose proof (u64_range (edenot E e)) as Hr.
  rewrite (mkSrl_denot SEGS E M k e 3 (Z_to_bv 64 3) HK ltac:(rewrite u64_lit by lia; reflexivity)).
  rewrite srl3_div8 by (rewrite u64_lit by lia; reflexivity). apply u64_lit. lia.
Qed.

(* [comment removed for export] *)
Lemma nth_Z_to_le_bytes : forall n z j d, (j < n)%nat -> nth j (Z_to_le_bytes n z) d = Z_to_bv 8 (z / 2 ^ (8 * Z.of_nat j)).
Proof.
  induction n as [|n IH]; intros z j d Hj; [lia|].
  cbn [Z_to_le_bytes]. destruct j as [|j'].
  - cbn [nth]. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r. reflexivity.
  - cbn [nth]. rewrite IH by lia. rewrite Z.shiftr_div_pow2 by lia.
    rewrite Z.div_div by lia. f_equal. f_equal. rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma Z_to_bv8_mod : forall x, Z_to_bv 8 (x mod 256) = Z_to_bv 8 x.
Proof.
  intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  apply Z.mod_mod. lia.
Qed.

Lemma nth_map_lt {X Y : Type} (f : X -> Y) (l : list X) (d : Y) (d' : X) (i : nat) :
  (i < length l)%nat -> nth i (map f l) d = f (nth i l d').
Proof. revert i; induction l as [|x l IH]; intros [|i] H; cbn in *; try lia; auto. apply IH. lia. Qed.

(* [comment removed for export] *)
Lemma mem_u64_of_bytes : forall M a (w : word),
  (forall j, (j < 8)%nat -> M (Z_to_bv 64 (a + Z.of_nat j)) = Some (nth j (word_to_le_bytes 8 w) (Z_to_bv 8 0))) ->
  mem_u64 M a (bv_unsigned w).
Proof.
  intros M a w H i Hi. unfold le_bytes in Hi. rewrite length_map, length_seq in Hi.
  unfold mem_byte, w64. rewrite (H i Hi). f_equal. unfold word_to_le_bytes. rewrite nth_Z_to_le_bytes by exact Hi.
  unfold le_bytes. rewrite (nth_map_lt _ _ 0 0%nat) by (rewrite length_seq; exact Hi).
  rewrite seq_nth by exact Hi. cbn [Nat.add]. symmetry. apply Z_to_bv8_mod.
Qed.

(* [comment removed for export] *)
Lemma wview_off : forall M a, 0 <= a < 2 ^ 64 -> (a < img_lo ASAN \/ img_hi ASAN <= a) ->
  wview SEGS M (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Proof.
  intros M a Ha Hout. unfold wview. destruct (M (Z_to_bv 64 a)); [reflexivity|].
  rewrite u64_lit by lia. rewrite (off_image_noseg a Ha Hout). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma store_ok_mem_def : forall M a n,
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (a + Z.of_nat n <= img_lo ASAN \/ img_hi ASAN <= a) ->
  store_ok SEGS M (Z_to_bv 64 a) n = true -> mem_def M a (Z.of_nat n).
Proof.
  intros M a n Ha Hn Hout Hst i Hi.
  pose proof (store_ok_all SEGS M n (Z_to_bv 64 a) ltac:(rewrite u64_lit by lia; lia) Hst (Z_to_bv 64 (a + i))
                ltac:(rewrite !u64_lit by lia; lia)) as W.
  rewrite (wview_off M (a + i)) in W by lia. unfold w64.
  destruct (M (Z_to_bv 64 (a + i))) as [b|]; [exists b; reflexivity | exfalso; exact (W eq_refl)].
Qed.

(* [comment removed for export] *)
Lemma RT_sane : forall c, In c RT_A -> 0 <= fst c < 2 ^ 64.
Proof.
  assert (Y : forallb (fun c => (0 <=? fst c) && (fst c <? 2 ^ 64))%bool RT_A = true) by (vm_compute; reflexivity).
  intros c Hin. pose proof (proj1 (forallb_forall _ _) Y c Hin) as H. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.
Lemma GSH_sane : forall c, In c GSH_A -> img_hi ASAN <= fst c < 2 ^ 64.
Proof.
  assert (Y : forallb (fun c => (img_hi ASAN <=? fst c) && (fst c <? 2 ^ 64))%bool GSH_A = true) by (vm_compute; reflexivity).
  intros c Hin. pose proof (proj1 (forallb_forall _ _) Y c Hin) as H. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

(* [comment removed for export] *)
Definition inr (lo hi : Z) (x : word) : bool := ((lo <=? bv_unsigned x) && (bv_unsigned x <? hi))%bool.
Lemma inr_spec : forall lo hi x, inr lo hi x = true <-> lo <= bv_unsigned x < hi.
Proof. intros lo hi x. unfold inr. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. Qed.
Lemma inr_false : forall lo hi x, inr lo hi x = false <-> ~ (lo <= bv_unsigned x < hi).
Proof. intros lo hi x. rewrite <- inr_spec. destruct (inr lo hi x); split; congruence. Qed.

(* [comment removed for export] *)
Lemma know_ok_havoc4 : forall E M M' k (a1 l1 a2 l2 a3 l3 a4 l4 : Z) b1 o1 n1 b2 o2 n2 b3 o3 n3 b4 o4 n4 (f : list kentry -> list kentry),
  know_ok SEGS E M k ->
  (forall M0, know_ok SEGS E M0 (kn_havoc k b1 o1 n1) -> know_ok SEGS E M0 (f (kn_havoc k b1 o1 n1))) ->
  estart E (SA b1 o1) = a1 -> elenZ E n1 = l1 -> estart E (SA b2 o2) = a2 -> elenZ E n2 = l2 ->
  estart E (SA b3 o3) = a3 -> elenZ E n3 = l3 -> estart E (SA b4 o4) = a4 -> elenZ E n4 = l4 ->
  (forall x : word,
     ~ (a1 <= bv_unsigned x < a1 + l1) -> ~ (a2 <= bv_unsigned x < a2 + l2) ->
     ~ (a3 <= bv_unsigned x < a3 + l3) -> ~ (a4 <= bv_unsigned x < a4 + l4) -> M' x = M x) ->
  mem_grows M M' ->
  know_ok SEGS E M' (kn_havoc (kn_havoc (kn_havoc (f (kn_havoc k b1 o1 n1)) b2 o2 n2) b3 o3 n3) b4 o4 n4).
Proof.
  intros E M M' k a1 l1 a2 l2 a3 l3 a4 l4 b1 o1 n1 b2 o2 n2 b3 o3 n3 b4 o4 n4 f HK Hf E1 L1 E2 L2 E3 L3 E4 L4 Hout Hg.
  set (M1 := fun x : word => if (inr a2 (a2 + l2) x || inr a3 (a3 + l3) x || inr a4 (a4 + l4) x)%bool then M x else M' x).
  set (M2 := fun x : word => if (inr a3 (a3 + l3) x || inr a4 (a4 + l4) x)%bool then M x else M' x).
  set (M3 := fun x : word => if inr a4 (a4 + l4) x then M x else M' x).
  assert (G' : forall (c : bool) x, M x <> None -> (if c then M x else M' x) <> None).
  { intros c x Hx. destruct c; [exact Hx | exact (Hg x Hx)]. }
  assert (O1 : forall x : word, bv_unsigned x < a1 \/ a1 + l1 <= bv_unsigned x -> M1 x = M x).
  { intros x Hx. unfold M1. destruct (inr a2 (a2 + l2) x) eqn:Ea; [reflexivity|]. destruct (inr a3 (a3 + l3) x) eqn:Eb; [reflexivity|].
    destruct (inr a4 (a4 + l4) x) eqn:Ec; [reflexivity|]. cbn [orb].
    apply inr_false in Ea. apply inr_false in Eb. apply inr_false in Ec. apply Hout; [lia | exact Ea | exact Eb | exact Ec]. }
  assert (G1 : mem_grows M M1) by (intros x Hx; unfold M1; apply G'; exact Hx).
  assert (O2 : forall x : word, bv_unsigned x < a2 \/ a2 + l2 <= bv_unsigned x -> M2 x = M1 x).
  { intros x Hx. unfold M1, M2. destruct (inr a2 (a2 + l2) x) eqn:Ea.
    - apply inr_spec in Ea. lia.
    - cbn [orb]. reflexivity. }
  assert (G2 : mem_grows M1 M2).
  { intros x Hx. unfold M1, M2 in *. destruct (inr a2 (a2 + l2) x); cbn [orb] in *; [apply G'; exact Hx | exact Hx]. }
  assert (O3 : forall x : word, bv_unsigned x < a3 \/ a3 + l3 <= bv_unsigned x -> M3 x = M2 x).
  { intros x Hx. unfold M2, M3. destruct (inr a3 (a3 + l3) x) eqn:Ea.
    - apply inr_spec in Ea. lia.
    - cbn [orb]. reflexivity. }
  assert (G3 : mem_grows M2 M3).
  { intros x Hx. unfold M2, M3 in *. destruct (inr a3 (a3 + l3) x); cbn [orb] in *; [apply G'; exact Hx | exact Hx]. }
  assert (O4 : forall x : word, bv_unsigned x < a4 \/ a4 + l4 <= bv_unsigned x -> M' x = M3 x).
  { intros x Hx. unfold M3. destruct (inr a4 (a4 + l4) x) eqn:Ea; [|reflexivity]. apply inr_spec in Ea. lia. }
  assert (G4 : mem_grows M3 M').
  { intros x Hx. unfold M3 in Hx. destruct (inr a4 (a4 + l4) x); [exact (Hg x Hx) | exact Hx]. }
  assert (K1 : know_ok SEGS E M1 (f (kn_havoc k b1 o1 n1))).
  { apply Hf. eapply w_know_ok_havoc; [exact HK | rewrite E1, L1; exact O1 | exact G1]. }
  assert (K2 : know_ok SEGS E M2 (kn_havoc (f (kn_havoc k b1 o1 n1)) b2 o2 n2)).
  { eapply w_know_ok_havoc; [exact K1 | rewrite E2, L2; exact O2 | exact G2]. }
  eapply w_know_ok_havoc; [| rewrite E4, L4; exact O4 | exact G4].
  eapply w_know_ok_havoc; [exact K2 | rewrite E3, L3; exact O3 | exact G3].
Qed.

(* [comment removed for export] *)
Lemma rdn_of_mem_u64 : forall M a v, mem_u64 M a v -> 0 <= a -> a + 8 <= 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  rdn SEGS M (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 v)).
Proof.
  intros M a v H Ha Ha8 Hv. apply rdn_pointwise; [apply length_N_to_le_bytes | rewrite u64_lit by lia; lia |].
  intros j Hj. rewrite u64_lit by lia.
  unfold mem_u64, mem_bytes, mem_byte, w64 in H. specialize (H j). unfold le_bytes in H at 1. rewrite length_map, length_seq in H.
  rewrite (H Hj). f_equal. unfold word_to_le_bytes. rewrite nth_Z_to_le_bytes by exact Hj. rewrite u64_lit by lia.
  unfold le_bytes. rewrite (nth_map_lt _ _ 0 0%nat) by (rewrite length_seq; exact Hj). rewrite seq_nth by exact Hj. cbn [Nat.add].
  apply Z_to_bv8_mod.
Qed.

Lemma LIBR_sub_hull : forall a, in_ranges a LIBR_A -> fst LIBR_HULL_A <= a < snd LIBR_HULL_A.
Proof. exact in_ranges_LIBR_hull. Qed.

(* [comment removed for export] *)
Lemma post_know_sound : forall E M M' K fb fk hb hk qb qk (sp FS : Z),
  know_ok SEGS E M K ->
  mem_frame M M' ((sp - FR_A, sp) :: LIBR_A ++ [(FS, FS + LibIfaceA.FS_LEN); (sh FS + LibIfaceA.FS_SHLO, sh FS + LibIfaceA.FS_SHHI)]) ->
  fs_inv FS M' ->
  estart E (SA qb qk) = sp - FR_A -> estart E (SA fb fk) = FS -> estart E (SA hb (hk + ALN.FS_SHLO)) = sh FS + LibIfaceA.FS_SHLO ->
  know_ok SEGS E M'
    (lib_extra_effect fb fk hb hk
       (kn_havoc (kn_havoc (lib_fp_havoc (lib_fp ASAN) (kn_havoc K qb qk (ELit LIB_FRAME))) fb fk (ELit ALN.FS_LEN))
                 hb (hk + ALN.FS_SHLO) (ELit (ALN.FS_SHHI - ALN.FS_SHLO)))).
Proof.
  intros E M M' K fb fk hb hk qb qk sp FS HK [Hout Hgr] FI EQ EF EH.
  pose proof (fi_lo _ _ FI) as Flo. pose proof (fi_hi _ _ FI) as Fhi. unfold IMGHI_A in Flo. unfold HIEND_A, LibIfaceA.FS_LEN in Fhi.
  unfold LibIfaceA.FS_SHLO, LibIfaceA.FS_SHHI, LibIfaceA.FS_LEN, LibIfaceA.FS_FRAMES, ALN.FS_SHLO, ALN.FS_SHHI, ALN.FS_LEN, ALN.FS_FLAGS, LIB_FRAME, FR_A in *.
  change (36864 / 8) with 4608 in *. change (11571200 / 8) with 1446400 in *.
  assert (Hsh : 0 <= sh FS /\ sh FS + 1446400 <= 2 ^ 64) by (unfold sh, SH_A; lia).
  unfold lib_extra_effect. unfold ALN.FS_LEN, ALN.FS_FLAGS, ALN.FS_SHLO, ALN.FS_SHHI. rewrite lib_fp_ASAN. cbn [lib_fp_havoc]. cbn [fst snd LIBR_HULL_A].
  (* [comment removed for export] *)
  assert (HAV : know_ok SEGS E M'
     (kn_havoc (kn_havoc (kn_havoc (kimg_cut (kn_havoc K qb qk (ELit 4096)) 6703360 (6707736 - 6703360)) (ELit 0) 6703360 (ELit (6707736 - 6703360)))
                         fb fk (ELit 11571200)) hb (hk + 4608) (ELit (1446400 - 4608)))).
  { apply (know_ok_havoc4 E M M' K (sp - 4096) 4096 6703360 4376 FS 11571200 (sh FS + 4608) 1441792
             qb qk (ELit 4096) (ELit 0) 6703360 (ELit (6707736 - 6703360)) fb fk (ELit 11571200) hb (hk + 4608) (ELit (1446400 - 4608))
             (fun k => kimg_cut k 6703360 (6707736 - 6703360)) HK).
    - intros M0 H0. apply kimg_cut_sound. exact H0.
    - exact EQ.
    - unfold elenZ. cbn [edenot]. apply u64_lit. lia.
    - unfold estart. cbn [a_base a_off edenot]. rewrite u64_lit; lia.
    - unfold elenZ. cbn [edenot]. apply u64_lit. lia.
    - exact EF.
    - unfold elenZ. cbn [edenot]. apply u64_lit. lia.
    - exact EH.
    - unfold elenZ. cbn [edenot]. apply u64_lit. lia.
    - intros x N1 N2 N3 N4. apply Hout. intros (r & Hin & Hr).
      destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|].
      apply in_app_or in Hin as [Hin|Hin].
      + pose proof (LIBR_sub_hull (bv_unsigned x) (ex_intro _ r (conj Hin Hr))) as Hh. cbn [fst snd LIBR_HULL_A] in Hh. lia.
      + destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; lia.
    - intros x Hx. destruct (M x) as [b|] eqn:Hb; [|exfalso; exact (Hx eq_refl)]. destruct (Hgr x b Hb) as [b' ->]. discriminate. }
  (* [comment removed for export] *)
  repeat apply Forall_cons; [ | | | | | exact HAV].
  - (* [comment removed for export] *)
    cbn [kentry_ok]. split; [unfold flat, elenZ; rewrite EF; cbn [edenot]; rewrite u64_lit by lia; lia|].
    intros i Hi. unfold elenZ in Hi. cbn [edenot] in Hi. rewrite u64_lit in Hi by lia. rewrite EF.
    destruct (fi_def _ _ FI i ltac:(unfold LibIfaceA.FS_LEN; lia)) as [b Hb]. unfold w64 in Hb. rewrite Hb. discriminate.
  - (* [comment removed for export] *)
    cbn [kentry_ok]. split; [lia|]. split; [unfold flat, estart; cbn [a_base a_off]; unfold estart in EF; cbn [a_base a_off] in EF; lia|].
    rewrite adenot_SA. replace (estart E (SA fb (fk + 88))) with (FS + 88) by (unfold estart in *; cbn [a_base a_off] in *; lia).
    cbn [edenot]. apply rdn_of_mem_u64; [exact (fi_log _ _ FI) | lia | lia | lia].
  - (* [comment removed for export] *)
    cbn [kentry_ok]. split; [unfold flat, estart, elenZ; cbn [a_base a_off edenot]; rewrite u64_lit by lia; unfold estart in EF; cbn [a_base a_off] in EF; lia|].
    intros i Hi. unfold elenZ in Hi. cbn [edenot] in Hi. rewrite u64_lit in Hi by lia.
    replace (estart E (SA fb (fk + 96)) + i) with (FS + 96) by (unfold estart in *; cbn [a_base a_off] in *; lia).
    exact (fi_gc _ _ FI).
  - (* [comment removed for export] *)
    cbn [kentry_ok]. split; [unfold flat, estart, elenZ; cbn [a_base a_off edenot]; rewrite u64_lit by lia; unfold estart in EF; cbn [a_base a_off] in EF; lia|].
    intros i Hi. unfold elenZ in Hi. cbn [edenot] in Hi. rewrite u64_lit in Hi by lia.
    replace (estart E (SA fb (fk + 4096)) + i) with (FS + LibIfaceA.FS_FLAGS + i) by (unfold LibIfaceA.FS_FLAGS, estart in *; cbn [a_base a_off] in *; lia).
    exact (fi_flags _ _ FI i Hi).
  - (* [comment removed for export] *)
    cbn [kentry_ok]. split; [unfold flat, elenZ; rewrite EH; cbn [edenot]; rewrite u64_lit by lia; lia|].
    intros i Hi. unfold elenZ in Hi. cbn [edenot] in Hi. rewrite u64_lit in Hi by lia. rewrite EH.
    destruct (fi_shdef _ _ FI i ltac:(unfold LibIfaceA.FS_SHLO, LibIfaceA.FS_SHHI, LibIfaceA.FS_LEN, LibIfaceA.FS_FRAMES; cbn; lia)) as [b Hb].
    unfold w64, LibIfaceA.FS_SHLO, LibIfaceA.FS_FRAMES in Hb. change (36864 / 8) with 4608 in Hb. rewrite Hb. discriminate.
Qed.

(* [comment removed for export] *)
Lemma keeps_cs_kept : forall R R', keeps_cs R R' -> kept_ok R R'.
Proof.
  intros R R' HK r Hr0 Hnin. pose proof (ridx_range r) as Hrr.
  assert (Hr : ridx r <> 0%nat).
  { intros X. apply Hr0. rewrite (reg_of_ridx r 0 X). apply bv_eq. reflexivity. }
  unfold caller_saved in Hnin. cbn [In] in Hnin.
  rewrite (reg_of_ridx r (ridx r) eq_refl).
  apply HK. unfold cs_regs. cbn [In]. lia.
Qed.

(* [comment removed for export] *)
Lemma stack_shadow_sound : forall E M K splo sphi spe sp,
  know_ok SEGS E M K ->
  (kzero_x K K (ELit 0) (LIB_SH + (splo - LIB_FRAME) / 8) (ELit ((sphi - splo + LIB_FRAME) / 8 + 2)) || sshadow_sym K spe)%bool = true ->
  sp = bv_unsigned (edenot E spe) ->
  splo <= sp <= sphi -> 2 ^ 32 + 4096 <= splo -> sphi <= HIEND_A -> stack_shadow_ok sp M.
Proof.
  intros E M K splo sphi spe sp HK Gssh Hspe Hsp Hsplo Hsphi g Hg. unfold LIB_SH, LIB_FRAME, HIEND_A, FR_A in *.
  apply orb_prop in Gssh as [Gssh|Gsym].
  2: { (* [comment removed for export] *)
       unfold sshadow_sym, LIB_FRAME, LIB_SH in Gsym.
       match type of Gsym with context [split_lit ?e] => destruct (split_lit e) as [hb hk] eqn:Hsh end.
       apply andb_prop in Gsym as [Gfl Gkz]. change (4096 / 8) with 512 in Gfl, Gkz.
       destruct (kzero_x_sound SEGS E M K K _ _ _ HK HK Gkz) as (Z0 & _ & _).
       change (elenZ E (ELit 512)) with (bv_unsigned (Z_to_bv 64 512)) in Z0. rewrite u64_lit in Z0 by lia.
       destruct (flat_x_sound SEGS E M K hb hk (ELit 512) HK Gfl) as (F0 & F1 & _).
       change (bv_unsigned (edenot E (ELit 512))) with (bv_unsigned (Z_to_bv 64 512)) in F1. rewrite u64_lit in F1 by lia.
       pose proof (w_split_lit_denot E _ hb hk Hsh) as Hsa.
       apply (f_equal bv_unsigned) in Hsa. rewrite u_eadd, (u_mkSrl3 E M K _ HK) in Hsa. cbn [edenot] in Hsa.
       rewrite (u_eaddz_neg E spe 4096) in Hsa by lia. rewrite <- Hspe in Hsa.
       rewrite (u64_lit 2147450880) in Hsa by lia. rewrite Z.mod_small in Hsa by lia.
       pose proof (u64_range (edenot E hb)) as Uhb.
       assert (HS : estart E (SA hb hk) = (sp - 4096) / 8 + 2147450880).
       { unfold estart in *. cbn [a_base a_off] in *. rewrite u64_lit in Hsa by lia. lia. }
       unfold mem_byte, w64, SH_A.
       replace (2147450880 + g) with (estart E (SA hb hk) + (g - (sp - 4096) / 8)) by lia.
       apply Z0. lia. }
  destruct (kzero_x_sound SEGS E M K K _ _ _ HK HK Gssh) as (Z0 & _ & _).
  unfold estart in Z0. cbn [a_base a_off edenot] in Z0. rewrite (u64_lit 0) in Z0 by lia. rewrite Z.add_0_l in Z0.
  change (elenZ E (ELit ((sphi - splo + 4096) / 8 + 2))) with (bv_unsigned (Z_to_bv 64 ((sphi - splo + 4096) / 8 + 2))) in Z0.
  rewrite u64_lit in Z0 by lia.
  unfold mem_byte, w64, SH_A.
  replace (2147450880 + g) with (2147450880 + (splo - 4096) / 8 + (g - (splo - 4096) / 8)) by lia.
  apply Z0. lia.
Qed.

(* [comment removed for export] *)
Lemma payload_shadow_sound : forall E M K de ne nhi data n,
  know_ok SEGS E M K -> lib_payload_shadow_ok SEGS K de ne nhi = true ->
  n = bv_unsigned (edenot E ne) -> data = bv_unsigned (edenot E de) -> n <= nhi -> payload_shadow_ok data n M.
Proof.
  intros E M K de ne nhi data n HK G Hn Hdata Hnhi. unfold lib_payload_shadow_ok in G.
  assert (HSB : img_hi ASAN <= AsanNodesRP.RPN.SB) by (vm_compute; discriminate || (cbv; lia)).
  destruct (sym_shadow_sound SEGS ASAN asan_in_hull HSB E M K de ne HK G) as (Hal & Z0 & Zp).
  rewrite <- Hn, <- Hdata in *. unfold AsanNodesRP.RPN.SB in Z0, Zp.
  split.
  - intros g Hg. unfold mem_byte, w64, SH_A. apply Z0. exact Hg.
  - intros Hmod. unfold mem_byte, w64, SH_A. apply Zp. exact Hmod.
Qed.

(* [comment removed for export] *)
Lemma extra_guard_sound : forall E M cs qb qk splo sphi bb bk ne nhi dlo dhi fse fb fk hb hk (sp data n : Z),
  know_ok SEGS E M (kn cs) -> LINV_A M ->
  lib_extra_guard SEGS LIBTAB_ASAN ASAN cs qb qk splo sphi bb bk ne nhi dlo dhi = Some fse ->
  split_lit fse = (fb, fk) ->
  split_lit (mkAlu ALU_ADD (mkSrl (kn cs) fse 3) (ELit LIB_SH)) = (hb, hk) ->
  n = bv_unsigned (edenot E ne) -> data = bv_unsigned (edenot E (reg cs 10)) ->
  splo <= sp <= sphi -> 2 ^ 32 + 4096 <= splo -> sphi <= HIEND_A ->
  n <= nhi -> dlo <= data <= dhi -> estart E (SA bb bk) = data ->
  estart E (SA qb qk) = sp - FR_A ->   (* [comment removed for export] *)
  sp = bv_unsigned (edenot E (reg cs 2)) ->   (* [comment removed for export] *)
  exists FS,
       fs_inv FS M
    /\ malloc_ctx_ok (sp - FR_A) sp FS M
    /\ rt_ok M /\ gsh_ok M /\ ro_ok SEGS RO_A M
    /\ stack_shadow_ok sp M
    /\ payload_shadow_ok data n M
    /\ (sp <= FS \/ FS + LibIfaceA.FS_LEN <= sp - FR_A)
    /\ (n = 0 \/ data + n <= FS \/ FS + LibIfaceA.FS_LEN <= data)
    /\ FS = estart E (SA fb fk)
    /\ sh FS + LibIfaceA.FS_SHLO = estart E (SA hb (hk + FS_SHLO))
    /\ (exists c : word, rdn SEGS M (Z_to_bv 64 CANARY_A) 8%nat = Some (word_to_le_bytes 8 c)).   (* [comment removed for export] *)
Proof.
  intros E M cs qb qk splo sphi bb bk ne nhi dlo dhi fse fb fk hb hk sp data n HK HL Hxg Hsf Hsh Hn Hdata Hsp Hsplo Hsphi Hnhi Hd HB HQW Hspe. unfold FR_A in HQW.
  pose proof (u64_range (edenot E ne)) as Hnr. rewrite <- Hn in Hnr.
  pose proof (u64_range (edenot E (reg cs 10))) as Hdr. rewrite <- Hdata in Hdr.
  unfold lib_extra_guard in Hxg. rewrite lt_tp_eq in Hxg.
  change (lt_ctx LIBTAB_ASAN) with 0x6877e0 in Hxg. change (lt_dt LIBTAB_ASAN) with 0x666330 in Hxg. rewrite lt_can_eq in Hxg.
  destruct (know_lookup SEGS (kn cs) (ELit 0) TP_A 8 false [] []) as [fse' scs hs|scs hs|] eqn:HLfs; try discriminate.
  destruct scs; [|discriminate].
  destruct (split_lit fse') as [fb' fk'] eqn:Hsf'.
  destruct (split_lit (mkAlu ALU_ADD (mkSrl (kn cs) fse' 3) (ELit LIB_SH))) as [hb' hk'] eqn:Hsh'.
  destruct (xlo (kn cs) fse') as [flo|] eqn:Hflo; [|discriminate].
  destruct (xhi (kn cs) fse') as [fhi|] eqn:Hfhi; [|discriminate].
  destruct (know_lookup SEGS (kn cs) (ELit 0) 0x6877e0 8 false [] []) as [ctxe scs2 hs2|scs2 hs2|] eqn:HLctx; try discriminate.
  destruct scs2; [|discriminate].
  destruct (know_lookup SEGS (kn cs) (ELit 0) 0x666330 8 false [] []) as [dte scs3 hs3|scs3 hs3|] eqn:HLdt; try discriminate.
  destruct scs3; [|discriminate].
  destruct (split_lit ctxe) as [cb ck] eqn:Hsc.
  destruct (know_lookup SEGS (kn cs) cb (ck + 0x98) 8 false [] []) as [thre scs4 hs4|scs4 hs4|] eqn:HLthr; try discriminate.
  destruct scs4; [|discriminate].
  destruct (split_lit thre) as [tb tk] eqn:Hst.
  destruct (split_lit dte) as [db dk] eqn:Hsd.
  destruct (xlo (kn cs) (mkAlu ALU_ADD ctxe (ELit 0x98))) as [c98lo|] eqn:Hc98lo; [|discriminate].
  destruct (xhi (kn cs) (mkAlu ALU_ADD ctxe (ELit 0x98))) as [c98hi|] eqn:Hc98hi; [|discriminate].
  destruct (xlo (kn cs) (mkAlu ALU_ADD thre (ELit 0x30))) as [t30lo|] eqn:Ht30lo; [|discriminate].
  destruct (xhi (kn cs) (mkAlu ALU_ADD thre (ELit 0x30))) as [t30hi|] eqn:Ht30hi; [|discriminate].
  destruct (xlo (kn cs) (mkAlu ALU_ADD dte (ELit 0x18))) as [d18lo|] eqn:Hd18lo; [|discriminate].
  destruct (xhi (kn cs) (mkAlu ALU_ADD dte (ELit 0x18))) as [d18hi|] eqn:Hd18hi; [|discriminate].
  destruct (xlo (kn cs) ctxe) as [clo|] eqn:Hclo; [|discriminate].
  destruct (xhi (kn cs) ctxe) as [chi|] eqn:Hchi; [|discriminate].
  match type of Hxg with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  injection Hxg as ->. rewrite Hsf in Hsf'. injection Hsf' as <- <-. rewrite Hsh in Hsh'. injection Hsh' as <- <-.
  (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond Gpsh]. apply andb_prop in Hcond as [Hcond GapFSd]. apply andb_prop in Hcond as [Hcond GapFSsp].
  apply andb_prop in Hcond as [Hcond Gapd18]. apply andb_prop in Hcond as [Hcond Gapt30]. apply andb_prop in Hcond as [Hcond Gapc98].
  apply andb_prop in Hcond as [Hcond Gd18w]. apply andb_prop in Hcond as [Hcond Gt30w]. apply andb_prop in Hcond as [Hcond Gc98w].
  apply andb_prop in Hcond as [Hcond Gdtp]. apply andb_prop in Hcond as [Hcond Gt30wr]. apply andb_prop in Hcond as [Hcond Gt30fl].
  apply andb_prop in Hcond as [Hcond Gd18fl]. apply andb_prop in Hcond as [Hcond Gc98fl].
  apply andb_prop in Hcond as [Hcond Gd18]. apply andb_prop in Hcond as [Hcond Gt30]. apply andb_prop in Hcond as [Hcond Gc98].   (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond Gchi]. apply andb_prop in Hcond as [Hcond Gclo].
  apply andb_prop in Hcond as [Hcond Gssh].
  apply andb_prop in Hcond as [Hcond Gcan].   (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond Ggsh]. apply andb_prop in Hcond as [Hcond Gro]. apply andb_prop in Hcond as [Hcond Grt].
  apply andb_prop in Hcond as [Hcond Ggc]. apply andb_prop in Hcond as [Hcond Glog]. apply andb_prop in Hcond as [Hcond Gflags].
  apply andb_prop in Hcond as [Hcond Gshwr]. apply andb_prop in Hcond as [Hcond Gshfl].
  apply andb_prop in Hcond as [Hcond Gfswr]. apply andb_prop in Hcond as [Hcond Gfsfl].
  apply andb_prop in Hcond as [Hcond Gfhi]. apply andb_prop in Hcond as [Hcond Gfapp]. apply andb_prop in Hcond as [Galign Gflo].   (* [comment removed for export] *)
  apply Z.leb_le in Galign. apply Z.leb_le in Gflo. apply Z.leb_le in Gfhi. apply Z.leb_le in Gclo. apply Z.leb_le in Gchi.
  cbn [img_hi ASAN] in Gflo.
  pose proof (proj1 (ctx_cellb_cases _ _ _ _ _ _ Gc98)) as Gc98lo. pose proof (proj1 (ctx_cellb_cases _ _ _ _ _ _ Gt30)) as Gt30lo.
  pose proof (proj1 (ctx_cellb_cases _ _ _ _ _ _ Gd18)) as Gd18lo.   (* [comment removed for export] *)
  unfold LIB_KHI, LIB_HIEND, LIB_IMGHI, ALN.FS_LEN, ALN.FS_SHLO, ALN.FS_SHHI, ALN.FS_FLAGS, LIB_FRAME, LIB_SH in *.
  unfold HIEND_A in Hsphi.
  set (K := kn cs) in *.
  (* [comment removed for export] *)
  set (FS := estart E (SA fb fk)).
  destruct (flat_x_sound SEGS E M K fb fk (ELit 11571200) HK Gfsfl) as (F0 & F1 & _).
  change (bv_unsigned (edenot E (ELit 11571200))) with (bv_unsigned (Z_to_bv 64 11571200)) in F1. rewrite u64_lit in F1 by lia.
  fold FS in F0, F1.
  pose proof (xlo_sound SEGS E M K fse flo HK Hflo) as Xflo. pose proof (xhi_sound SEGS E M K fse fhi HK Hfhi) as Xfhi.
  pose proof (u64_range (edenot E fse)) as Ufse.
  assert (HFS : bv_unsigned (edenot E fse) = FS).
  { pose proof (split_lit_estart E fse fb fk fk 11571200 Hsf ltac:(unfold flat; fold FS; lia) ltac:(lia) ltac:(lia)) as X. fold FS in X. lia. }
  (* [comment removed for export] *)
  assert (Hal : FS mod 4096 = 0).
  { destruct (ealign_sound SEGS E M K fse HK) as [He1 [q Hq]]. rewrite HFS in Hq. rewrite Hq.
    replace (ealign K fse) with ((ealign K fse - 12) + 12) by lia.
    rewrite Z.pow_add_r by lia. change (2 ^ 12) with 4096. rewrite Z.mul_assoc. apply Z_mod_mult. }
  (* [comment removed for export] *)
  destruct (kreadZ SEGS K fb (fk + 88) 8) as [v88|] eqn:Hk88; [|discriminate].
  destruct v88 as [|p88|]; try discriminate. destruct p88 as [p|p|]; try discriminate. destruct p as [p|p|]; try discriminate.
  destruct p as [p|p|]; try discriminate. destruct p as [p|p|]; try discriminate. destruct p; try discriminate. clear Glog.
  destruct (kreadZ_rdn E M K fb (fk + 88) 8 20 HK Hk88 ltac:(lia) ltac:(unfold flat, estart; cbn [a_base a_off]; unfold FS, estart in F0, F1; cbn [a_base a_off] in F0, F1; lia)) as (R88 & _ & _).
  destruct (kreadZ SEGS K fb (fk + 96) 1) as [v96|] eqn:Hk96; [|discriminate].
  destruct v96; try discriminate. clear Ggc.
  destruct (kreadZ1_byte SEGS E M K fb (fk + 96) 0 HK Hk96 ltac:(unfold flat, estart; cbn [a_base a_off]; unfold FS, estart in F0, F1; cbn [a_base a_off] in F0, F1; lia)) as [R96 _].
  (* [comment removed for export] *)
  set (HS := estart E (SA hb (hk + 4608))).
  destruct (flat_x_sound SEGS E M K hb (hk + 4608) (ELit (1446400 - 4608)) HK Gshfl) as (S0 & S1 & _).
  change (bv_unsigned (edenot E (ELit (1446400 - 4608)))) with (bv_unsigned (Z_to_bv 64 1441792)) in S1. rewrite u64_lit in S1 by lia.
  fold HS in S0, S1.
  assert (HHS : HS = sh FS + 4608).
  { pose proof (split_lit_estart E _ hb hk (hk + 4608) 1441792 Hsh ltac:(unfold flat; fold HS; lia) ltac:(lia)) as X.
    rewrite (u_eaddz_pos E (mkSrl K fse 3) 2147450880) in X by (first [lia | rewrite (u_mkSrl3 E M K fse HK); lia]).
    rewrite (u_mkSrl3 E M K fse HK), HFS in X. unfold sh, SH_A. fold HS in X. lia. }
  assert (E88 : estart E (SA fb (fk + 88)) = FS + 88) by (unfold FS, estart; cbn [a_base a_off]; lia).
  assert (E96 : estart E (SA fb (fk + 96)) = FS + 96) by (unfold FS, estart; cbn [a_base a_off]; lia).
  rewrite E88 in R88. rewrite E96 in R96.
  assert (IMGHI : img_hi ASAN <= FS) by (cbn [img_hi ASAN]; lia).
  (* [comment removed for export] *)
  assert (FAPP : app_mem FS LibIfaceA.FS_LEN).
  { pose proof (app_memb_sound SEGS E M K fb fk (ELit 11571200) flo fhi 11571200 HK Gfapp ltac:(fold FS; lia)
                  ltac:(unfold elenZ; rewrite (ulit_small E 11571200) by (unfold two64; lia); lia)) as FA.
    fold FS in FA. unfold elenZ in FA. rewrite (ulit_small E 11571200) in FA by (unfold two64; lia).
    unfold app_mem, LOSH_A, KHI_A, LibIfaceA.FS_LEN. unfold LIB_LOSH, LIB_KHI in FA. lia. }
  (* [comment removed for export] *)
  assert (FSINV : fs_inv FS M).
  { constructor.
    - (* [comment removed for export] *)
      destruct (lookup_piece SEGS E M K (ELit 0) TP_A 8 fse hs HK ltac:(lia) HLfs
                  ltac:(unfold flat, estart; cbn [a_base a_off edenot]; rewrite u64_lit by lia; unfold TP_A; lia)) as (bs & Hrd & Hlen & Hbs).
      unfold estart in Hrd. cbn [a_base a_off edenot] in Hrd. rewrite u64_lit, Z.add_0_l in Hrd by lia.
      exists bs. rewrite SEGS_A_eq. change FSTLS_A with TP_A. split; [exact Hrd|]. rewrite <- Hbs, bytes_le_to_Z_8. exact HFS.
    - exact Hal.
    - unfold IMGHI_A. lia.
    - exact FAPP.
    - unfold HIEND_A, LibIfaceA.FS_LEN. lia.
    - (* [comment removed for export] *)
      destruct (kwritable_x_sound SEGS ASAN E M K K fb fk (ELit 11571200) HK HK Gfswr) as (W & _ & _).
      specialize (W (Z.to_nat 11571200)). fold FS in W.
      change (elenZ E (ELit 11571200)) with (bv_unsigned (Z_to_bv 64 11571200)) in W. rewrite u64_lit in W by lia.
      unfold LibIfaceA.FS_LEN. rewrite <- (Z2Nat.id 11571200) by lia.
      apply store_ok_mem_def; [lia | lia | lia | apply W; lia].
    - (* [comment removed for export] *)
      destruct (kwritable_x_sound SEGS ASAN E M K K hb (hk + 4608) (ELit (1446400 - 4608)) HK HK Gshwr) as (W & _ & _).
      specialize (W (Z.to_nat 1441792)). fold HS in W.
      change (elenZ E (ELit (1446400 - 4608))) with (bv_unsigned (Z_to_bv 64 1441792)) in W. rewrite u64_lit in W by lia.
      change (mem_def M (sh FS + LibIfaceA.FS_SHLO) (LibIfaceA.FS_SHHI - LibIfaceA.FS_SHLO)) with (mem_def M (sh FS + 4608) 1441792).
      rewrite <- HHS. rewrite <- (Z2Nat.id 1441792) by lia.
      apply store_ok_mem_def; [lia | lia | unfold sh, SH_A in HHS; cbn [img_lo img_hi ASAN]; lia | apply W; lia].
    - (* [comment removed for export] *)
      apply mem_u64_of_bytes with (w := Z_to_bv 64 20). intros j Hj.
      apply (rdn_off_bytes M (FS + 88) 8); [lia | lia | lia | exact R88 | exact Hj].
    - (* [comment removed for export] *)
      unfold mem_byte, w64. apply (rdn1_off M (FS + 96)); [lia | lia | exact R96].
    - (* [comment removed for export] *)
      intros j Hj. destruct (kzero_x_sound SEGS E M K K fb (fk + 4096) (ELit 32768) HK HK Gflags) as (Z0 & _ & _).
      specialize (Z0 j). change (elenZ E (ELit 32768)) with (bv_unsigned (Z_to_bv 64 32768)) in Z0. rewrite u64_lit in Z0 by lia.
      unfold mem_byte, w64, LibIfaceA.FS_FLAGS.
      replace (FS + 4096 + j) with (estart E (SA fb (fk + 4096)) + j) by (unfold FS, estart; cbn [a_base a_off]; lia).
      apply Z0. exact Hj. }
  (* [comment removed for export] *)
  set (CTX := bv_unsigned (edenot E ctxe)). set (THR := bv_unsigned (edenot E thre)). set (DT := bv_unsigned (edenot E dte)).
  pose proof (u64_range (edenot E ctxe)) as Uctx. pose proof (u64_range (edenot E thre)) as Uthr. pose proof (u64_range (edenot E dte)) as Udt.
  fold CTX in Uctx. fold THR in Uthr. fold DT in Udt.
  pose proof (xlo_sound SEGS E M K _ _ HK Hclo) as Xclo. pose proof (xhi_sound SEGS E M K _ _ HK Hchi) as Xchi. fold CTX in Xclo, Xchi.
  pose proof (xlo_sound SEGS E M K _ _ HK Hc98lo) as Xc98lo. pose proof (xhi_sound SEGS E M K _ _ HK Hc98hi) as Xc98hi.
  rewrite (u_eaddz_pos E ctxe 0x98) in Xc98lo, Xc98hi by lia. fold CTX in Xc98lo, Xc98hi.
  pose proof (xlo_sound SEGS E M K _ _ HK Ht30lo) as Xt30lo. pose proof (xhi_sound SEGS E M K _ _ HK Ht30hi) as Xt30hi.
  rewrite u_eadd in Xt30lo, Xt30hi. change (bv_unsigned (edenot E (ELit 48))) with (bv_unsigned (Z_to_bv 64 48)) in Xt30lo, Xt30hi.
  rewrite (u64_lit 48) in Xt30lo, Xt30hi by lia. fold THR in Xt30lo, Xt30hi.
  assert (T30nw : (THR + 48) mod 2 ^ 64 = THR + 48) by (rewrite Z.mod_small; lia).
  rewrite T30nw in Xt30lo, Xt30hi.
  pose proof (xlo_sound SEGS E M K _ _ HK Hd18lo) as Xd18lo. pose proof (xhi_sound SEGS E M K _ _ HK Hd18hi) as Xd18hi.
  rewrite u_eadd in Xd18lo, Xd18hi. change (bv_unsigned (edenot E (ELit 24))) with (bv_unsigned (Z_to_bv 64 24)) in Xd18lo, Xd18hi.
  rewrite (u64_lit 24) in Xd18lo, Xd18hi by lia. fold DT in Xd18lo, Xd18hi.
  assert (D18nw : (DT + 24) mod 2 ^ 64 = DT + 24) by (rewrite Z.mod_small; lia).
  rewrite D18nw in Xd18lo, Xd18hi.
  (* [comment removed for export] *)
  destruct (flat_x_sound SEGS E M K cb (ck + 152) (ELit 8) HK Gc98fl) as (C0 & C1 & _).
  change (bv_unsigned (edenot E (ELit 8))) with (bv_unsigned (Z_to_bv 64 8)) in C1. rewrite (u64_lit 8) in C1 by lia.
  pose proof (split_lit_estart E ctxe cb ck (ck + 152) 8 Hsc ltac:(unfold flat; lia) ltac:(lia) ltac:(fold CTX; lia)) as EC98.
  fold CTX in EC98. replace (ck + 152 - ck) with 152 in EC98 by lia.
  destruct (flat_x_sound SEGS E M K tb (tk + 48) (ELit 16) HK Gt30fl) as (T0 & T1 & _).
  change (bv_unsigned (edenot E (ELit 16))) with (bv_unsigned (Z_to_bv 64 16)) in T1. rewrite (u64_lit 16) in T1 by lia.
  pose proof (split_lit_estart E thre tb tk (tk + 48) 16 Hst ltac:(unfold flat; lia) ltac:(lia) ltac:(fold THR; lia)) as ET30.
  fold THR in ET30. replace (tk + 48 - tk) with 48 in ET30 by lia.
  destruct (flat_x_sound SEGS E M K db (dk + 24) (ELit 8) HK Gd18fl) as (D0 & D1 & _).
  change (bv_unsigned (edenot E (ELit 8))) with (bv_unsigned (Z_to_bv 64 8)) in D1. rewrite (u64_lit 8) in D1 by lia.
  pose proof (split_lit_estart E dte db dk (dk + 24) 8 Hsd ltac:(unfold flat; lia) ltac:(lia) ltac:(fold DT; lia)) as ED18.
  fold DT in ED18. replace (dk + 24 - dk) with 24 in ED18 by lia.
  (* [comment removed for export] *)
  destruct (ctx_cellb_sound SEGS E M K cb (ck + 152) 8 c98lo c98hi HK Gc98 ltac:(unfold two64; lia) ltac:(rewrite EC98; lia)) as (P98a & P98b & P98c & P98d).
  destruct (ctx_cellb_sound SEGS E M K tb (tk + 48) 16 t30lo t30hi HK Gt30 ltac:(unfold two64; lia) ltac:(rewrite ET30; lia)) as (P30a & P30b & P30c & P30d).
  destruct (ctx_cellb_sound SEGS E M K db (dk + 24) 8 d18lo d18hi HK Gd18 ltac:(unfold two64; lia) ltac:(rewrite ED18; lia)) as (P18a & P18b & P18c & P18d).
  rewrite EC98 in P98a, P98b, P98c, P98d. rewrite ET30 in P30a, P30b, P30c, P30d. rewrite ED18 in P18a, P18b, P18c, P18d.
  assert (BHA : band_hi ASAN = img_hi ASAN) by reflexivity. rewrite BHA in P98b, P30b, P18b. cbn [img_hi ASAN] in P98b, P30b, P18b.
  unfold LIB_IMGLO, LIB_IMGHI, LIB_LOSH, LIB_KHI, LIB_HIEND in P98a, P98b, P98c, P98d, P30a, P30b, P30c, P30d, P18a, P18b, P18c, P18d.
  (* [comment removed for export] *)
  pose proof (below_or_apart_sound SEGS E M K qb qk 4096 cb (ck + 152) 8 c98hi (splo - 4096) (sp - 4096) (CTX + 152) HK Gc98w
                ltac:(unfold two64; lia) ltac:(unfold two64; lia) HQW EC98 ltac:(lia) ltac:(lia)) as W98.
  pose proof (below_or_apart_sound SEGS E M K qb qk 4096 tb (tk + 48) 16 t30hi (splo - 4096) (sp - 4096) (THR + 48) HK Gt30w
                ltac:(unfold two64; lia) ltac:(unfold two64; lia) HQW ET30 ltac:(lia) ltac:(lia)) as W30.
  pose proof (below_or_apart_sound SEGS E M K qb qk 4096 db (dk + 24) 8 d18hi (splo - 4096) (sp - 4096) (DT + 24) HK Gd18w
                ltac:(unfold two64; lia) ltac:(unfold two64; lia) HQW ED18 ltac:(lia) ltac:(lia)) as W18.
  pose proof (below_or_apart_sound SEGS E M K qb qk 4096 fb fk 11571200 fhi (splo - 4096) (sp - 4096) FS HK GapFSsp
                ltac:(unfold two64; lia) ltac:(unfold two64; lia) HQW eq_refl ltac:((try clear - E splo sphi fse fb fk hb hk sp data n fhi ctxe dte thre Hsp Hsplo Hnr Hdr FS Xfhi Ufse HFS HS CTX THR DT Uctx Uthr Udt P98c P30c P18c W98 W30 W18; lia)) ltac:(lia)) as WFS.
  assert (MCTX : malloc_ctx_ok (sp - FR_A) sp FS M).
  { exists CTX, THR, DT.
    (* [comment removed for export] *)
    pose proof (ranges_apart_x_sound SEGS E M K cb (ck + 152) (ELit 8) fb fk (ELit 11571200) HK Gapc98) as A1.
    pose proof (ranges_apart_x_sound SEGS E M K tb (tk + 48) (ELit 16) fb fk (ELit 11571200) HK Gapt30) as A2.
    pose proof (ranges_apart_x_sound SEGS E M K db (dk + 24) (ELit 8) fb fk (ELit 11571200) HK Gapd18) as A3.
    rewrite EC98 in A1. rewrite ET30 in A2. rewrite ED18 in A3. fold FS in A1, A2, A3.
    change (elenZ E (ELit 8)) with (bv_unsigned (Z_to_bv 64 8)) in A1, A3.
    change (elenZ E (ELit 16)) with (bv_unsigned (Z_to_bv 64 16)) in A2.
    change (elenZ E (ELit 11571200)) with (bv_unsigned (Z_to_bv 64 11571200)) in A1, A2, A3.
    rewrite !u64_lit in A1, A2, A3 by lia.
    repeat match goal with |- _ /\ _ => split end.
    - (* [comment removed for export] *)
      destruct (lookup_piece SEGS E M K (ELit 0) 0x6877e0 8 ctxe hs2 HK ltac:(lia) HLctx
                  ltac:(unfold flat, estart; cbn [a_base a_off edenot]; rewrite u64_lit by lia; lia)) as (bs & Hrd & Hlen & Hbs).
      unfold estart in Hrd. cbn [a_base a_off edenot] in Hrd. rewrite u64_lit, Z.add_0_l in Hrd by lia.
      exists bs. rewrite SEGS_A_eq. split; [exact Hrd|]. rewrite <- Hbs, bytes_le_to_Z_8. reflexivity.
    - (* [comment removed for export] *)
      destruct (lookup_piece SEGS E M K cb (ck + 152) 8 thre hs4 HK ltac:(lia) HLthr ltac:(unfold flat; lia)) as (bs & Hrd & Hlen & Hbs).
      rewrite EC98 in Hrd. apply mem_u64_of_bytes with (w := edenot E thre). intros j Hj. rewrite <- Hbs in Hrd.
      apply (rdn_off_bytes M (CTX + 152) 8); [lia | lia | cbn [img_lo img_hi ASAN]; lia | exact Hrd | exact Hj].
    - (* [comment removed for export] *)
      destruct (kwritable_x_sound SEGS ASAN E M K K tb (tk + 48) (ELit 16) HK HK Gt30wr) as (W & _ & _).
      specialize (W 16%nat). rewrite ET30 in W. change (elenZ E (ELit 16)) with (bv_unsigned (Z_to_bv 64 16)) in W.
      rewrite (u64_lit 16) in W by lia.
      change 16 with (Z.of_nat 16). apply store_ok_mem_def; [lia | lia | cbn [img_lo img_hi ASAN]; lia | apply W; lia].
    - (* [comment removed for export] *)
      destruct (lookup_piece SEGS E M K (ELit 0) 0x666330 8 dte hs3 HK ltac:(lia) HLdt
                  ltac:(unfold flat, estart; cbn [a_base a_off edenot]; rewrite u64_lit by lia; lia)) as (bs & Hrd & Hlen & Hbs).
      unfold estart in Hrd. cbn [a_base a_off edenot] in Hrd. rewrite u64_lit, Z.add_0_l in Hrd by lia.
      exists bs. rewrite SEGS_A_eq. split; [exact Hrd|]. rewrite <- Hbs, bytes_le_to_Z_8. reflexivity.
    - (* [comment removed for export] *)
      destruct (kreadZ SEGS K db (dk + 24) 8) as [vtp|] eqn:Hktp; [|discriminate]. apply Z.eqb_eq in Gdtp. subst vtp.
      destruct (kreadZ_rdn E M K db (dk + 24) 8 TP_A HK Hktp ltac:(lia) ltac:(unfold flat; lia)) as (Rtp & _ & _).
      rewrite ED18 in Rtp. rewrite <- (u64_lit TP_A) by (unfold TP_A; lia).
      apply mem_u64_of_bytes with (w := Z_to_bv 64 TP_A). intros j Hj.
      apply (rdn_off_bytes M (DT + 24) 8); [lia | lia | cbn [img_lo img_hi ASAN]; lia | exact Rtp | exact Hj].
    - lia.
    - unfold HIEND_A. lia.
    - lia.
    - lia.
    - unfold ctx_cell_ok, app_mem, LOSH_A, KHI_A, IMGHI_A, HIEND_A, FR_A, LibIfaceA.FS_LEN. lia.
    - unfold ctx_cell_ok, app_mem, LOSH_A, KHI_A, IMGHI_A, HIEND_A, FR_A, LibIfaceA.FS_LEN. lia.
    - unfold ctx_cell_ok, app_mem, LOSH_A, KHI_A, IMGHI_A, HIEND_A, FR_A, LibIfaceA.FS_LEN. lia. }
  exists FS. split; [exact FSINV|]. split; [exact MCTX|].
  split; [exact (cells_rd_sound E M K RT_A HK Grt RT_sane)|].
  split; [exact (cells_ov_sound E M K GSH_A HK Ggsh GSH_sane)|].
  split; [exact (ro_ok_sound E M K HK HL Gro)|].
  split; [exact (stack_shadow_sound E M K splo sphi (reg cs 2) sp HK Gssh Hspe Hsp Hsplo Hsphi)|].
  split; [exact (payload_shadow_sound E M K (reg cs 10) ne nhi data n HK Gpsh Hn Hdata Hnhi)|].
  split; [unfold FR_A, LibIfaceA.FS_LEN; lia|].
  split.
  { apply orb_prop in GapFSd as [GapFSd|Gap]; [apply orb_prop in GapFSd as [GapFSd|Gap]; [apply orb_prop in GapFSd as [Gap|Gap]|]|].
    - apply Z.eqb_eq in Gap. (try clear - E splo sphi nhi fse fb fk hb hk sp data n ctxe dte thre Gap Hsp Hsplo Hnhi Hnr Hdr FS Ufse HS CTX THR DT Uctx Uthr Udt P98c P30c P18c W98 W30 W18; lia).
    - apply Z.leb_le in Gap. (try clear - E splo sphi nhi dlo dhi fse fb fk hb hk sp data n flo ctxe dte thre Gap Hsp Hsplo Hnhi Hd Hnr Hdr FS Xflo Ufse HFS HS CTX THR DT Uctx Uthr Udt P98c P30c P18c W98 W30 W18; lia).
    - apply Z.leb_le in Gap. unfold LibIfaceA.FS_LEN. (try clear - E splo sphi dlo dhi fse fb fk hb hk sp data n fhi ctxe dte thre Gap Hsp Hsplo Hd Hnr Hdr FS Xfhi Ufse HFS HS CTX THR DT Uctx Uthr Udt P98c P30c P18c W98 W30 W18; lia).
    - pose proof (ranges_apart_x_sound SEGS E M K bb bk ne fb fk (ELit 11571200) HK Gap) as A. rewrite HB in A. fold FS in A.
      change (elenZ E (ELit 11571200)) with (bv_unsigned (Z_to_bv 64 11571200)) in A. rewrite u64_lit in A by lia.
      unfold elenZ in A. rewrite <- Hn in A. unfold LibIfaceA.FS_LEN. lia. }
  split; [reflexivity|].
  split; [unfold LibIfaceA.FS_SHLO, LibIfaceA.FS_FRAMES; change (36864 / 8) with 4608; symmetry; exact HHS|].
  (* [comment removed for export] *)
  destruct (kread8e SEGS K (ELit 0) CANARY_A) as [cv|] eqn:Hce; [|discriminate Gcan].
  exists (edenot E cv). exact (kread8e_rdn0 E M K CANARY_A cv HK ltac:(unfold CANARY_A; lia) ltac:(unfold CANARY_A; lia) Hce).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Close.
  Hypothesis HLIB : lib_stmt_A.

  (* [comment removed for export] *)
  Variables (sp0 : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (FS0 : Fs.Fs).   (* [comment removed for export] *)
  Hypothesis Hsp : valid_sp sp0.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Variable uid : word.
  Variable hw : word.   (* [comment removed for export] *)
  Hypothesis Hfit : entry_stack_fits sp0 argv envp.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_0 : forall E M, SINV E M -> SINV0 APH sp0 rdraw brk0 argv envp uid hw E M.
  Hypothesis SINV_frame : forall E M M', (forall a, argH0 APH sp0 rdraw argv envp uid hw E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

  #[local] Notation argH := (argH0 APH sp0 rdraw argv envp uid hw).
  #[local] Notation LIM := AsanInit.LIMIT.
  #[local] Notation CSOK := (cs_ok SEGS ASAN LIM SINV argH LINV_A FS0).
  #[local] Notation L := LIBTAB_ASAN.

  Let argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a := argH0_high APH sp0 rdraw argv envp uid hw Hsp Hva.
  Let argH_agree : forall E E' (a : word), env_agree NX0 E E' -> argH E a = argH E' a := argH0_agree APH sp0 rdraw argv envp uid hw.
  Let nx0_ge : APS.nx0_ok NX0 := Nat.le_refl NX0.   (* [comment removed for export] *)
  Let LINV_frame := proj2 LINV_A_stmt.

  #[using="HLIB Hsp Hva SINV_frame SINV_agree argH_high argH_agree nx0_ge LINV_frame"] Theorem summary_lib_sound : OBL_lib SEGS ASAN NX0 LIM SINV argH LINV_A FS0 (ALN.summary_lib SEGS L ASAN NX0).
  Proof.
    unfold OBL_lib, lib_stmt. intros fx FRM cs cs' E R FULL model T HC Hn Hk.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HKN.
    set (M := Mr ASAN argH E cs model FULL) in *.
    rewrite ALN.summary_lib_eq in Hn. unfold ALN.summary_lib_ref in Hn.   (* [comment removed for export] *)
    destruct (Z.eqb (pc cs) (x_lib ASAN)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
    destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
    destruct (reg_lit cs 4) as [tp|] eqn:Htp; [|discriminate].
    destruct (Z.eqb ret (lib_ret ASAN) && Z.eqb (ret mod 4) 0 && Z.eqb tp (lt_tp L))%bool eqn:Hrt; [|discriminate]. cbn [negb] in Hn.
    apply andb_prop in Hrt as [Hrt Htpv]. apply andb_prop in Hrt as [Hretv Hret4].
    apply Z.eqb_eq in Hretv. apply Z.eqb_eq in Hret4. apply Z.eqb_eq in Htpv. subst ret tp.
    destruct (split_lit (reg cs 10)) as [bb bk] eqn:Hsdata.
    destruct (split_lit (eaddz (reg cs 2) (- LIB_FRAME))) as [qb qk] eqn:Hsq.
    destruct (xhi (kn cs) (reg cs 11)) as [nhi|] eqn:Hnhi; [|discriminate].
    destruct (xlo (kn cs) (reg cs 10)) as [dlo|] eqn:Hdlo; [|discriminate].
    destruct (xhi (kn cs) (reg cs 10)) as [dhi|] eqn:Hdhi; [|discriminate].
    destruct (xlo (kn cs) (reg cs 2)) as [splo|] eqn:Hsplo; [|discriminate].
    destruct (xhi (kn cs) (reg cs 2)) as [sphi|] eqn:Hsphi; [|discriminate].
    match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
    destruct (ALN.lib_extra_guard SEGS L ASAN cs qb qk splo sphi bb bk (reg cs 11) nhi dlo dhi) as [fse|] eqn:Hxg; [|discriminate].
    destruct (split_lit fse) as [fb fk] eqn:Hsf.
    destruct (split_lit (mkAlu ALU_ADD (mkSrl (kn cs) fse 3) (ELit LIB_SH))) as [hb hk] eqn:Hsh.
    (* [comment removed for export] *)
    apply andb_prop in Hcond as [Hcond Gfresh]. apply andb_prop in Hcond as [Hcond Gread]. apply andb_prop in Hcond as [Hcond Gkhi].
    apply andb_prop in Hcond as [Hcond Gimg]. apply andb_prop in Hcond as [Hcond Gapw]. apply andb_prop in Hcond as [Hcond Gwr].
    apply andb_prop in Hcond as [Hcond Gflq]. apply andb_prop in Hcond as [Hcond Gsphi]. apply andb_prop in Hcond as [Hcond Gkhisp].
    apply andb_prop in Hcond as [Hcond Gsplo]. apply andb_prop in Hcond as [Hcond Galsp]. apply andb_prop in Hcond as [Hcond Gbflat].
    apply andb_prop in Hcond as [Hcond Galdata]. apply andb_prop in Hcond as [Hcond Gd62]. apply andb_prop in Hcond as [Hcond Gdlo].
    apply andb_prop in Hcond as [Gn0 Gnmax].
    apply Z.ltb_lt in Gnmax. apply Z.leb_le in Gdlo. apply Z.ltb_lt in Gd62. apply Z.leb_le in Galdata. apply Z.leb_le in Galsp.
    apply Z.leb_le in Gsplo. apply Z.leb_le in Gkhisp. apply Z.leb_le in Gsphi.
    unfold LIB_NMAX, LIB_FRAME, LIB_KHI, LIB_HIEND in *.
    set (K := kn cs) in *.
    (* [comment removed for export] *)
    destruct (ret_lit_sound SEGS ASAN LIM SINV argH LINV_A FS0 E cs R FULL model _ HC Hret) as (R1 & Hrok & Hretr).
    destruct (reg_lit_sound SEGS ASAN LIM SINV argH LINV_A FS0 E cs R FULL model 4 _ HC ltac:(lia) Htp) as [R4 _].
    pose proof (w_reg_sound SEGS ASAN LIM SINV argH LINV_A FS0 E cs R FULL model 2 HC ltac:(lia)) as R2.
    pose proof (w_reg_sound SEGS ASAN LIM SINV argH LINV_A FS0 E cs R FULL model 10 HC ltac:(lia)) as R10.
    pose proof (w_reg_sound SEGS ASAN LIM SINV argH LINV_A FS0 E cs R FULL model 11 HC ltac:(lia)) as R11.
    change (Z.of_nat 4) with 4 in R4. change (Z.of_nat 2) with 2 in R2. change (Z.of_nat 10) with 10 in R10. change (Z.of_nat 11) with 11 in R11.
    set (spw := edenot E (reg cs 2)) in *. set (dw := edenot E (reg cs 10)) in *. set (nw := edenot E (reg cs 11)) in *.
    set (sp := bv_unsigned spw). set (data := bv_unsigned dw). set (n := bv_unsigned nw).
    pose proof (u64_range spw) as Usp. pose proof (u64_range dw) as Ud. pose proof (u64_range nw) as Un. fold sp in Usp. fold data in Ud. fold n in Un.
    pose proof (xhi_sound SEGS E M K _ _ HKN Hnhi) as Xnhi. fold nw n in Xnhi.
    pose proof (xlo_sound SEGS E M K _ _ HKN Hdlo) as Xdlo. pose proof (xhi_sound SEGS E M K _ _ HKN Hdhi) as Xdhi. fold dw data in Xdlo, Xdhi.
    pose proof (xlo_sound SEGS E M K _ _ HKN Hsplo) as Xsplo. pose proof (xhi_sound SEGS E M K _ _ HKN Hsphi) as Xsphi. fold spw sp in Xsplo, Xsphi.
    (* [comment removed for export] *)
    assert (AL16 : forall e, 4 <= ealign K e -> bv_unsigned (edenot E e) mod 16 = 0).
    { intros e He. destruct (ealign_sound SEGS E M K e HKN) as [He1 [q Hq]]. rewrite Hq.
      replace (ealign K e) with ((ealign K e - 4) + 4) by lia.
      rewrite Z.pow_add_r by lia. change (2 ^ 4) with 16. rewrite Z.mul_assoc. apply Z_mod_mult. }
    pose proof (AL16 _ Galdata) as ALd. pose proof (AL16 _ Galsp) as ALs. fold dw data in ALd. fold spw sp in ALs. clear AL16.
    (* [comment removed for export] *)
    assert (HB : estart E (SA bb bk) = data).
    { apply orb_prop in Gbflat as [G|G].
      - apply Z.eqb_eq in G. subst bk. unfold estart. cbn [a_base a_off]. rewrite <- (split_lit_0 E _ _ Hsdata). fold dw data. lia.
      - destruct (flat_x_sound SEGS E M K bb bk (ELit 1) HKN G) as (B0 & B1 & _).
        change (bv_unsigned (edenot E (ELit 1))) with (bv_unsigned (Z_to_bv 64 1)) in B1. rewrite u64_lit in B1 by lia.
        pose proof (split_lit_estart E _ bb bk bk 1 Hsdata ltac:(unfold flat; lia) ltac:(lia) ltac:(fold dw data; lia)) as X. fold dw data in X. lia. }
    (* [comment removed for export] *)
    destruct (kwritable_sound SEGS ASAN E M K K qb qk 4096 HKN HKN Gwr ltac:(lia)) as (Qst & Q0 & Q1).
    assert (HQ : estart E (SA qb qk) = sp - 4096).
    { pose proof (u_eaddz_neg E (reg cs 2) 4096 ltac:(lia) ltac:(fold spw sp; lia)) as U. fold spw sp in U.
      pose proof (split_lit_estart E _ qb qk qk 4096 Hsq ltac:(unfold flat; lia) ltac:(lia) ltac:(rewrite U; lia)) as X. rewrite U in X. lia. }
    rewrite HQ in Qst.
    (* [comment removed for export] *)
    pose proof (LINV_Mr ASAN asan_hull_ok argH LINV_A argH_high LINV_frame asan_lfp_hull E cs model FULL (co_linv _ _ _ _ _ _ _ _ _ _ _ _ HC)) as HLM.
    fold M in HLM.
    destruct (extra_guard_sound E M cs qb qk splo sphi bb bk (reg cs 11) nhi dlo dhi fse fb fk hb hk sp data n
                HKN HLM Hxg Hsf Hsh eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(unfold HIEND_A; lia) Xnhi ltac:(lia) HB ltac:(unfold FR_A; exact HQ) eq_refl)
      as (FS & FSINV & MCTX & RT & GSH & RO & SSH & PSH & AP1 & AP2 & EF & EH & CAN).
    (* [comment removed for export] *)
    assert (RD : forall i, 0 <= i < n -> exists b, rdn SEGS M (Z_to_bv 64 (data + i)) 1 = Some [b]).
    { intros i Hi. apply orb_prop in Gread as [G|G]; [apply orb_prop in G as [G|G]|].
      - apply Z.eqb_eq in G. exfalso. lia.
      - destruct (kn_readable_x_sound E M K bb bk (reg cs 11) HKN G ltac:(unfold elenZ; fold nw n; lia)) as [_ RDx].
        rewrite HB in RDx. apply RDx. unfold elenZ. fold nw n. lia.
      - destruct (kcover_sound E M bb K bk nhi HKN G (bk + i) ltac:(lia)) as [_ [c Hc]].
        exists c. replace (data + i) with (bv_unsigned (edenot E bb) + (bk + i)) by (unfold estart in HB; cbn [a_base a_off] in HB; lia). exact Hc. }
    (* [comment removed for export] *)
    assert (WIN : forall a, sp - FR_A <= a < sp -> find_segment SEGS_A a 1 = None).
    { intros a Ha. unfold FR_A in Ha. rewrite SEGS_A_eq. apply off_image_noseg; [lia | cbn [img_lo img_hi ASAN]; lia]. }
    (* [comment removed for export] *)
    assert (HnwN : Z_to_bv 64 n = nw) by (apply Z_to_bv_bv_unsigned).
    destruct (HLIB fx R M (seg_rom SEGS) (Z_to_bv 64 (lib_ret ASAN)) spw dw n FS
                R1 ltac:(rewrite u64_lit by (unfold two64 in Hretr; lia); exact Hret4) R2 R10 ltac:(rewrite HnwN; exact R11)
                ltac:(rewrite R4; reflexivity)
                ltac:(unfold NMAX_A; lia) ltac:(fold data; lia) ltac:(fold data; lia) ALd ALs
                ltac:(unfold FR_A; fold sp; lia) ltac:(fold sp; unfold HIEND_A in *; lia))
      as (fx' & regs' & mem' & Hms & Hkeep & Ha0 & Hfr & Hst' & Hfs' & FRM').
    - (* [comment removed for export] *)
      fold sp data. unfold FR_A.
      apply orb_prop in Gapw as [G|G]; [apply orb_prop in G as [G|G]|].
      + apply Z.leb_le in G. lia.
      + apply Z.leb_le in G. lia.
      + pose proof (ranges_apart_x_sound SEGS E M K qb qk (ELit 4096) bb bk (reg cs 11) HKN G) as A.
        rewrite HQ, HB in A. change (elenZ E (ELit 4096)) with (bv_unsigned (Z_to_bv 64 4096)) in A. rewrite u64_lit in A by lia.
        unfold elenZ in A. fold nw n in A. lia.
    - (* [comment removed for export] *)
      fold data. apply orb_prop in Gimg as [G|G]; [apply orb_prop in G as [G|G]|].
      + apply Z.eqb_eq in G. lia.
      + apply Z.leb_le in G. cbn [img_lo ASAN] in G. lia.
      + apply Z.leb_le in G. cbn [img_hi ASAN] in G. lia.
    - exact WIN.
    - fold data. rewrite SEGS_A_eq. exact RD.
    - rewrite SEGS_A_eq. fold sp. exact Qst.
    - rewrite SEGS_A_eq. exact RO.
    - rewrite SEGS_A_eq. exact CAN.   (* [comment removed for export] *)
    - exact HLM.
    - exact RT.
    - exact GSH.
    - exact SSH.
    - exact PSH.
    - exact FSINV.
    - exact MCTX.
    - (* [comment removed for export] *)
      fold sp data. unfold apart_A, KHI_A, HIEND_A, FR_A. split; [lia|]. split; [lia|]. split; [|split; [exact AP1 | exact AP2]].
      (* [comment removed for export] *)
      apply orb_prop in Gkhi as [G|G]; [apply Z.eqb_eq in G; lia|]. apply andb_prop in G as [G G3]. apply andb_prop in G as [G1 G2].
      apply Z.leb_le in G1. cbn [img_hi ASAN] in G1. rewrite if_orb in G3.
      (* [comment removed for export] *)
      assert (G3' : dhi + nhi <= LIB_HIEND \/ data + n <= LIB_HIEND).
      { apply orb_prop in G3 as [G3|G3]; [left; apply Z.leb_le in G3; exact G3 | right].
        pose proof (lin_ge0_sound SEGS E M K _ _ HKN G3) as LG. cbn [xt_den] in LG.
        rewrite edenot_lit, u64_lit in LG by (unfold LIB_HIEND; lia).
        assert (En : bv_unsigned (edenot E (reg cs 11)) = n) by reflexivity.
        assert (Ed : bv_unsigned (edenot E bb) + bk = data) by (rewrite <- HB; reflexivity).
        unfold LIB_HIEND. rewrite <- Ed, <- En. lia. }
      clear G3.
      pose proof (app_memb_sound SEGS E M K bb bk (reg cs 11) dlo dhi nhi HKN G2 ltac:(rewrite HB; lia) ltac:(unfold elenZ; fold nw n; lia)) as DA.
      rewrite HB in DA. unfold elenZ in DA. fold nw n in DA.
      unfold app_mem, LOSH_A, KHI_A, IMGHI_A. unfold LIB_LOSH, LIB_KHI, LIB_IMGHI, LIB_HIEND in *. lia.
    - exact FRM.
    - (* [comment removed for export] *)
      eapply (call_node_lib_sound SEGS ASAN NX0 LIM asan_wx asan_in_hull asan_hull_ok SINV argH LINV_A argH_high argH_agree nx0_ge
                SINV_frame SINV_agree LINV_frame asan_lfp_hull FS0 fx' cs cs' E R FULL model T (lib_ret ASAN) (Some (ELit 0)) _ regs' mem' HC Hn).
      + rewrite Hpc. change (x_lib ASAN) with ENTRY_A. fold M. exact Hms.
      + exact (keeps_cs_kept R regs' Hkeep).
      + cbn [edenot]. exact Ha0.
      + apply (post_know_sound E M mem' K fb fk hb hk qb qk sp FS HKN Hfr Hfs' ltac:(unfold FR_A; exact HQ) (eq_sym EF) (eq_sym EH)).
      + exact Hst'.
      + intros E' R' FULL' model' Hag HC' Hfs. exact (Hk fx' FRM' E' R' FULL' model' Hag HC' Hfs).
  Qed.
End Close.

Theorem xlib_sound : lib_stmt_A -> XLIB_STMT LINV_A.
Proof.
  intros HLIB sp0 rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit SINV S0 SF SA.
  apply (summary_lib_sound HLIB); assumption.
Qed.
