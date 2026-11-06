(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YChd.v, with its module paths and module names changed; 759 of its 797 lines of code are new or changed and 507 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoYEntExit.v, with its module names changed; 400 of its 457 lines of code are new or changed and 740 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0p YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YC44.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1h YC1i YCjr YCj1 YCja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoArm3TailK DiscoYEntBodyStmt DiscoArm3 DiscoArm3JsonModel
DiscoArm3JsonCut DiscoArm3JsonK DiscoArm3JsonJsStep DiscoArm3JsonC2Defs DiscoArm3JsonC2Mod.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_jscalar_model disco_json_text disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require slot_ser_defs slot_ser_tokb.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma c2cp_nth_le : forall (n i : nat) (z : Z) (d : byte), (i < n)%nat ->
  nth i (Z_to_le_bytes n z) d = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat i)).
Proof.
  induction n as [|n IH]; intros i z d Hi; [lia|].
  destruct i as [|i]; cbn [Z_to_le_bytes nth].
  - change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
  - rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.

Lemma c2cp_nth_map : forall (l : list byte) (j : nat), (j < length l)%nat ->
  nth j (map (fun b : byte => bv_unsigned b) l) 0 = bv_unsigned (nth j l (Z_to_bv 8 0)).
Proof.
  intros l j Hj. rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj).
  apply (map_nth (fun b : byte => bv_unsigned b)).
Qed.

Lemma c2cp_le1 : forall b : byte, Z_to_bv 8 (YO0f.le_byte (bv_unsigned b) 1 0) = b.
Proof.
  intros b. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
  change (2 ^ 8) with 256. repeat rewrite (Z.mod_small (bv_unsigned b) 256) by lia. apply Z_to_bv_bv_unsigned.
Qed.

Lemma c2cp_slot_len : forall (buf : Z) (vpad : list byte) (t : tokv), length vpad = 4%nat ->
  length (slot_ser_defs.slot24 buf vpad t) = 24%nat.
Proof.
  intros buf vpad t L. unfold slot_ser_defs.slot24. destruct (tv_kind t =? 0).
  - apply repeat_length.
  - rewrite !length_app, L. reflexivity.
Qed.

Lemma c2cp_concat_len : forall {A : Type} (f : A -> list byte) (n : nat) (l : list A),
  (forall x, length (f x) = n) -> length (concat (map f l)) = (n * length l)%nat.
Proof.
  intros A f n l H. induction l as [|x l IH]; cbn [map concat length]; [lia|].
  rewrite length_app, H, IH, Nat.mul_succ_r. lia.
Qed.

Lemma c2cp_objs_len : forall (buf : Z) (vpad : list byte) (os : list jobj), length vpad = 4%nat ->
  Forall (fun o => length o = 6%nat) os -> length (slot_ser_defs.objs_bytes buf vpad os) = (144 * length os)%nat.
Proof.
  intros buf vpad os L H. unfold slot_ser_defs.objs_bytes.
  induction H as [|o os Ho _ IH]; cbn [map concat length]; [reflexivity|].
  rewrite length_app, IH. unfold slot_ser_defs.obj_bytes. rewrite (c2cp_concat_len _ 24).
  - rewrite Ho. lia.
  - intros t. apply c2cp_slot_len. exact L.
Qed.

Lemma c2cp_dsh0 : forall kk, 30 <= kk < 192 -> dsh_scr kk = 0.
Proof.
  intros kk Hk.
  assert (Hall : forallb (fun j => Z.eqb (dsh_scr (Z.of_nat j)) 0) (seq 30 162) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall. specialize (Hall (Z.to_nat kk) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in Hall by lia. apply Z.eqb_eq. exact Hall.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma c2cp_present_view : forall (H : word -> bool) (m : word -> option byte) a,
  apresent H m a -> aview SEGS H m a <> None.
Proof. intros H m a (Hh & b & Hb). unfold aview, mbyte, mrestrict. cbv beta. rewrite Hh, Hb. cbn. discriminate. Qed.

Lemma c2cp_mbyte_eq : forall (H H' : word -> bool) (m m' : word -> option byte) a a',
  aview SEGS H' m' a' = aview SEGS H m a -> mbyte SEGS (mrestrict H' m') a' = mbyte SEGS (mrestrict H m) a.
Proof.
  intros H H' m m' a a' E. unfold aview in E.
  destruct (mbyte SEGS (mrestrict H' m') a') as [b1|] eqn:E1; destruct (mbyte SEGS (mrestrict H m) a) as [b2|] eqn:E2;
    cbn [option_map] in E; try discriminate E; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma c2cp_vm1 : forall (m : word -> option byte) a (b : byte), mbyte SEGS m a = Some b -> val_mem SEGS m a 1 (bv_unsigned b).
Proof.
  intros m a b H k Hk. assert (k = 0%nat) by lia. subst k.
  replace (a + Z.of_nat 0) with a by lia. rewrite H, c2cp_le1. reflexivity.
Qed.

Lemma c2cp_vm_pad : forall (m : word -> option byte) a (l : list byte) (i : nat), (i < length l)%nat ->
  garr8 SEGS m a (map (fun b : byte => bv_unsigned b) l) -> mbyte SEGS m (a + Z.of_nat i) = Some (nth i l (Z_to_bv 8 0)).
Proof.
  intros m a l i Hi Hg. destruct (Hg i ltac:(rewrite length_map; exact Hi)) as [Hv _].
  rewrite c2cp_nth_map in Hv by exact Hi. pose proof (Hv 0%nat ltac:(lia)) as E.
  replace (a + Z.of_nat i + Z.of_nat 0) with (a + Z.of_nat i) in E by lia. rewrite c2cp_le1 in E. exact E.
Qed.

Lemma c2cp_vm_le8 : forall (m : word -> option byte) a v (i : nat), (i < 8)%nat -> val_mem SEGS m a 8 v ->
  mbyte SEGS m (a + Z.of_nat i) = Some (nth i (Mem.le8 (Z_to_bv 64 v)) (Z_to_bv 8 0)).
Proof.
  intros m a v i Hi Hv. rewrite (Hv i Hi). f_equal.
  unfold Mem.le8, word_to_le_bytes. rewrite c2cp_nth_le by exact Hi.
  rewrite Z_to_bv_unsigned. apply Z_to_bv_mod8. unfold YO0f.le_byte, bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). change (8 * Z.of_nat 8) with 64. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma c2cp_vm_le4 : forall (m : word -> option byte) a v (i : nat), (i < 4)%nat -> 0 <= v < 2 ^ 32 ->
  val_mem SEGS m a 4 v -> mbyte SEGS m (a + Z.of_nat i) = Some (nth i (Mem.le4 (Z_to_bv 64 v)) (Z_to_bv 8 0)).
Proof.
  intros m a v i Hi Hv0 Hv. rewrite (Hv i Hi). f_equal.
  unfold Mem.le4. rewrite c2cp_nth_le by exact Hi. rewrite unsigned_lit_small by lia.
  apply Z_to_bv_mod8. unfold YO0f.le_byte. change (8 * Z.of_nat 4) with 32.
  rewrite (Z.mod_small v (2 ^ 32)) by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma c2cp_oo : forall (m m' : word -> option byte) (base d x buf : Z) (vpad : list byte)
  (acc : list jobj) (cur : jobj) (ksl : nat) (vk vs vl : Z),
  Forall (fun o => length o = 6%nat) acc -> length cur = 6%nat -> (ksl < 6)%nat -> 1 <= vk <= 3 ->
  length vpad = 4%nat ->
  d = base + 144 * Z.of_nat (length acc) + 24 * Z.of_nat ksl ->
  (forall i, 0 <= i < 24 -> mbyte SEGS m' (d + i) = mbyte SEGS m (x + i)) ->
  (forall a, base <= a < base + 144 * Z.of_nat (length acc) + 144 -> ~ (d <= a < d + 24) ->
     mbyte SEGS m' a = mbyte SEGS m a) ->
  val_mem SEGS m x 8 (buf + vs) -> val_mem SEGS m (x + 8) 8 vl -> val_mem SEGS m (x + 16) 4 vk ->
  garr8 SEGS m (x + 20) (map (fun b : byte => bv_unsigned b) vpad) ->
  garr8 SEGS m base (map (fun b : byte => bv_unsigned b) (slot_ser_defs.objs_bytes buf vpad (acc ++ [cur]))) ->
  garr8 SEGS m' base
    (map (fun b : byte => bv_unsigned b) (slot_ser_defs.objs_bytes buf vpad (acc ++ [set_nth ksl cur (vk, vs, vl)]))).
Proof.
  intros m m' base d x buf vpad acc cur ksl vk vs vl HA HC Hk Hvk HL Hd HCP HKP V0 V8 V16 GV GO.
  assert (Hkind : tv_kind (vk, vs, vl) <> 0) by (unfold tv_kind; cbn [fst]; lia).
  destruct (jc2_obj buf vpad acc cur ksl (vk, vs, vl) HA HC Hk Hkind HL) as (HLEQ & HNTH).
  assert (HL0 : length (slot_ser_defs.objs_bytes buf vpad (acc ++ [cur])) = (144 * length acc + 144)%nat).
  { rewrite c2cp_objs_len; [rewrite length_app; cbn [length]; lia | exact HL |].
    apply Forall_app. split; [exact HA | constructor; [exact HC | constructor]]. }
  intros j Hj. rewrite length_map, HLEQ in Hj.
  assert (HjL : (j < length (slot_ser_defs.objs_bytes buf vpad (acc ++ [set_nth ksl cur (vk, vs, vl)])))%nat)
    by (rewrite HLEQ; exact Hj).
  rewrite (c2cp_nth_map _ j HjL).
  split.
  2:{ pose proof (bv_unsigned_in_range 8
        (nth j (slot_ser_defs.objs_bytes buf vpad (acc ++ [set_nth ksl cur (vk, vs, vl)])) (Z_to_bv 8 0))) as Hr.
      change (bv_modulus 8) with 256 in Hr. exact Hr. }
  apply c2cp_vm1. rewrite (HNTH j Hj).
  match goal with |- context [if ?c then _ else _] => destruct c eqn:Ein end.
  - apply andb_prop in Ein as [E1 E2]. apply Nat.leb_le in E1. apply Nat.ltb_lt in E2.
    remember (j - (144 * length acc + 24 * ksl))%nat as i eqn:Hi.
    replace (base + Z.of_nat j) with (d + Z.of_nat i) by lia.
    rewrite HCP by lia.
    unfold slot_ser_defs.slot24, tv_kind. cbn [fst snd].
    rewrite (proj2 (Z.eqb_neq vk 0)) by lia. cbv iota.
    assert (L8 : forall z, length (Mem.le8 (Z_to_bv 64 z)) = 8%nat) by (intros z; reflexivity).
    assert (L4 : forall z, length (Mem.le4 (Z_to_bv 64 z)) = 4%nat) by (intros z; reflexivity).
    destruct (Nat.lt_ge_cases i 8) as [H8|H8].
    + rewrite app_nth1 by (rewrite L8; exact H8). apply c2cp_vm_le8; [exact H8 | exact V0].
    + rewrite app_nth2 by (rewrite L8; exact H8). rewrite L8.
      destruct (Nat.lt_ge_cases i 16) as [H16|H16].
      * rewrite app_nth1 by (rewrite L8; lia).
        replace (x + Z.of_nat i) with (x + 8 + Z.of_nat (i - 8)) by lia.
        apply c2cp_vm_le8; [lia | exact V8].
      * rewrite app_nth2 by (rewrite L8; lia). rewrite L8.
        destruct (Nat.lt_ge_cases i 20) as [H20|H20].
        -- rewrite app_nth1 by (rewrite L4; lia).
           replace (x + Z.of_nat i) with (x + 16 + Z.of_nat (i - 8 - 8)) by lia.
           apply c2cp_vm_le4; [lia | lia | exact V16].
        -- rewrite app_nth2 by (rewrite L4; lia). rewrite L4.
           replace (x + Z.of_nat i) with (x + 20 + Z.of_nat (i - 8 - 8 - 4)) by lia.
           apply c2cp_vm_pad; [lia | exact GV].
  - assert (Hout : ~ (d <= base + Z.of_nat j < d + 24)).
    { intros Hc. apply andb_false_iff in Ein as [E1 | E2].
      - apply Nat.leb_gt in E1. lia.
      - apply Nat.ltb_ge in E2. lia. }
    rewrite (HKP (base + Z.of_nat j)); [| lia | exact Hout].
    apply c2cp_vm_pad; [lia | exact GO].
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA AS___asan_memcpy).
Hypothesis DBRT : d_body_rt_stmt B.

Theorem jc2_cp : jc2_cp_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
  intros P ksl W c HC.
  unfold jc2_cpy, jc2_at, jcut, d_arm_at_pf, d_at in HC.
  destruct HC as (HFROM & fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm0 & HBASE & HJ & HFR & Hk & Hnev &
    HMO &
    Hacc & Hi & Hn & Hnow & HRL & (R26 & R24 & R25 & (R21 & R22 & R23) & (R1 & R10 & R11 & R12)) &
    (HSP1 & HTAB & HBUF & HX & HSL) & HSP0 & HBODY).
  pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs3 & Rs2 & Rs4 & Rs11).
  pose proof HX as (HFIN & Hip & Hc0 & Hlen & Hkk & Hvk & HUPD & HPC & HLcur & HFcur & HTk & HTv & HJM & HJS &
    V448 & V456 & V464 & V424 & V432 & V440).
  pose proof HJM as (JLv & JGv & JGo & JL6).
  pose proof HJS as (JS408 & JS368 & JS360 & JS328 & JS296 & JS352).
  pose proof (jc2_count P W mem3 HX) as Hcnt.
  pose proof (slot_of_lt _ _ _ HSL) as Hks.
  destruct (jc2_some P W mem3 ksl HX HSL) as (_ & Hc2).
  pose proof (jc2_acc6 P W mem3 HX) as HA6.
  destruct (jc2_c2_ok P W mem3 HX) as (HLc2 & HFc2).
  pose proof (jc2_ws P W mem3 HX) as HWS.
  assert (Hlen' : Z.of_nat (length (p_acc P)) = p_count P) by lia.
  pose proof HBODY as (T & G & Lk & Hh & HFRM & HSHD & HOBJ & HBLK & HINP & HROD & HOFFF & HGEO & HCAN & HSTKF & HAWRF).
  pose proof HBLK as (HPerm0 & _ & _ & HOFFb).
  assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K (p_cx P) ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
  pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS (p_cx P) ly3 S3 W mem3 md3 k HCTX)
    as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GFsh & GSTK & HAR3 & HFin3 & EFA3 & EFL3).
  pose proof alloc_ceiling_value as Hceil0.
  pose proof (d_A_range (p_cx P) ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
  unfold MFRAME in GA1. unfold LLVMF_STK in GSlo, GSTK.
  pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _).
  destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
  destruct Hastk as (_ & _ & Hstk1 & Hstk2 & Hstk3 & _).
  unfold LLVMF_STK in Hstk2.
  pose proof (al_zshadow _ _ LAWS ly3 S3 W mem3 md3 (ly_stk_lo ly3, ly_stk_hi ly3 - ly_stk_lo ly3) HAR3
    ltac:(unfold zero_shadow_ranges; left; reflexivity)) as HZS.
  cbn [fst snd] in HZS. rewrite Elo, Ehi in HZS.
  assert (HOO : d_obj (p_cx P) OO = d_FB (p_cx P) + 240) by reflexivity.
  assert (HD : p_slot P ksl = d_FB (p_cx P) + 240 + 144 * p_count P + 24 * Z.of_nat ksl)
    by (unfold p_slot, jcur; rewrite HOO; lia).
  assert (HFB8 : 0 <= d_FB (p_cx P) / 8 < 2 ^ 44).
  { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  assert (Epc : BASE + (SIGMA AS___asan_memcpy - BASE) = SIGMA AS___asan_memcpy) by lia.
  unfold cfg_at. rewrite Epc.
  eapply SRr_mono.
  { apply (aj_intrin_at SEGS B LAWS pa_segs_low OCpy (SIGMA AS___asan_memcpy) (AMEMCPY fq) W regs mem3
      LLVMF_STK (d_S (p_cx P)) [] (c_ly (p_cx P)) (c_S (p_cx P)) (c_W (p_cx P)) (c_mem (p_cx P)) (c_md (p_cx P))
      [(DFRAME_CLASS, c_fpos (p_cx P))] ly3 S3 md3 k (p_slot P ksl) (d_A (p_cx P) + 424) 24
      (d_A (p_cx P) - d_S (p_cx P)) (w64 (BASE + SLOT_OFF)) HJ R10 R11 R12).
    - lia.
    - lia.
    - lia.
    - rewrite Rsp. lia.
    - pose proof (Z.div_mod (d_A (p_cx P)) 32 ltac:(lia)) as DA.
      pose proof (Z.div_mod (d_S (p_cx P)) 16 ltac:(lia)) as DS.
      rewrite GA32 in DA. rewrite GS16 in DS.
      replace (d_A (p_cx P) - d_S (p_cx P)) with ((2 * (d_A (p_cx P) / 32) - d_S (p_cx P) / 16) * 16) by lia.
      apply Z_mod_mult.
    - lia.
    - unfold ESTACK, LLVMF_STK. lia.
    - exact Rgp.
    - exact Rtp.
    - exact R1.
    - unfold w64. apply ret_ok_codeptr_v; [unfold SLOT_OFF; lia | reflexivity].
    - intros a Ha. split.
      + exact (proj1 (HAWRF a ltac:(unfold DFRAME_SIZE; lia))).
      + unfold ESTACK. lia.
    - apply (amem_range_sub_app (d_FB (p_cx P)) 4096 (p_slot P ksl) 24); [exact GFapp | lia | lia | lia | lia].
    - intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
      replace (SHADOW_OFF + x / 8) with (shadow_addr (d_FB (p_cx P)) + (x / 8 - d_FB (p_cx P) / 8))
        by (unfold shadow_addr; lia).
      rewrite HSHD by (unfold DFRAME_SH; lia). f_equal. apply c2cp_dsh0. lia.
    - intros _ s Hs.
      replace s with (shadow_addr (d_FB (p_cx P)) + (s - shadow_addr (d_FB (p_cx P)))) by lia.
      rewrite HSHD; [discriminate|]. unfold shadow_addr in *. unfold DFRAME_SH. lia.
    - split; [lia|]. split; [lia|]. split.
      { intros a Ha. split; [apply c2cp_present_view; apply GSTK; lia | rewrite Rsp; unfold ESTACK; lia]. }
      split; [left; lia|]. split.
      { pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold amem_range. right. rewrite C3, C4. lia. }
      split.
      { apply (jsc_zs_range _ _ _ _ _ _ HZS); lia. }
      intros _. apply (jsc_zs_hull _ _ _ _ _ HZS); lia. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & Q10 & HCPY & HKP & HPRES).
  assert (HCTX4 : d_ctx B MT XM_LIB RLO RHI tfib_K (p_cx P) ly3 S3 W mem2 md2 k) by exact (conj HBASE (conj HJ2 HFR)).
  pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS (p_cx P) ly3 S3 W mem2 md2 k HCTX4)
    as (_ & _ & _ & _ & _ & _ & _ & _ & GFpres4 & GFsh4 & GSTK4 & _ & _ & _ & _).
  unfold LLVMF_STK in GSTK4.
  set (Pk := fun a => d_A (p_cx P) - 4096 <= a < d_A (p_cx P) \/ p_slot P ksl <= a < p_slot P ksl + 24).
  assert (HK : d_kept Pk W mem3 W mem2).
  { intros a Ha HPa. apply HKP; [exact Ha | intros Hc; apply HPa; right; exact Hc |].
    intros Hc; apply HPa; left; unfold ESTACK in Hc; lia. }
  assert (HPA : forall a, d_A (p_cx P) <= a -> ~ Pk a) by (intros a Ha [Hp|Hp]; lia).
  assert (HPL : forall a, a < p_slot P ksl -> ~ Pk a) by (intros a Ha [Hp|Hp]; lia).
  assert (HPM : forall a, p_slot P ksl + 24 <= a < alloc_ceiling -> ~ Pk a) by (intros a Ha [Hp|Hp]; lia).
  assert (HSHN : forall o, 0 <= o < 512 -> ~ Pk (shadow_addr (d_FB (p_cx P)) + o)).
  { intros o Ho [Hp|Hp]; unfold shadow_addr, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *; lia. }
  pose proof HFRM as (E & HE & HREG & HFLAG & _).
  pose proof (d_hslots_of_frame (p_cx P) (p_h P) dsh_scr W mem3 HFRM) as HSLo.
  pose proof HE as (EE & E32 & HEI & E60 & EF & ESH).
  assert (HSLn : d_hslots (p_cx P) (p_h P) W mem2).
  { apply (d_hslots_kept (p_cx P) (p_h P) W W mem3 mem2); [|exact HSLo].
    intros a Ha. apply HK; [lia | apply HPA; lia]. }
  assert (HFRM4 : d_frame (p_cx P) (p_h P) dsh_scr W mem2).
  { exists E. split; [exact HE|]. split; [|split].
    - unfold d_regions in HREG |- *. rewrite !Forall_cons_iff in HREG |- *.
      destruct HREG as (HRS & HRA & HRF & HRH & _).
      split; [|split; [|split; [|split; [|exact (Forall_nil _)]]]].
      + apply (jsc_region_ok_kept E _ _ _ (-104) 0 HRS); [vm_compute; reflexivity | |].
        * cbn [YP09.r_base base_val]. unfold AT_STK. rewrite (EE 2%nat 2%bv eq_refl).
          change (bv_unsigned (getr (c_regs (p_cx P)) 2)) with (d_S (p_cx P)).
          intros a Ha. apply (mbyte_of_aview SEGS). apply HK; [lia | apply HPA; lia].
        * cbn [YP09.r_wlo YP09.r_whi]. intros o Ho. lia.
      + apply (jsc_region_ok_kept E _ _ _ 0 424 HRA); [vm_compute; reflexivity | |].
        * cbn [YP09.r_base base_val]. rewrite E60. unfold w64. rewrite unsigned_lit_small by lia.
          intros a Ha. apply (mbyte_of_aview SEGS). apply HK; [lia | apply HPA; lia].
        * cbn [YP09.r_base base_val YP09.r_wlo YP09.r_whi]. rewrite E60. unfold w64.
          rewrite unsigned_lit_small by lia. intros o Ho. apply (apresent_writable SEGS). apply GSTK4. lia.
      + apply (jsc_region_ok_kept E _ _ _ 0 24 HRF); [vm_compute; reflexivity | |].
        * cbn [YP09.r_base base_val]. rewrite EF. unfold w64. rewrite unsigned_lit_small by lia.
          intros a Ha. apply (mbyte_of_aview SEGS). apply HK; [lia | apply HPL; lia].
        * cbn [YP09.r_base base_val YP09.r_wlo YP09.r_whi]. rewrite EF. unfold w64.
          rewrite unsigned_lit_small by lia. intros o Ho. apply (apresent_writable SEGS). apply GFpres4.
          unfold DFRAME_SIZE in Ho. lia.
      + apply (jsc_region_ok_kept E _ _ _ 0 384 HRH); [vm_compute; reflexivity | |].
        * unfold fshadow_region. cbn [YP09.r_base base_val]. rewrite ESH. unfold w64.
          rewrite unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF; lia).
          intros a Ha. apply (mbyte_of_aview SEGS).
          replace a with (shadow_addr (d_FB (p_cx P)) + (a - shadow_addr (d_FB (p_cx P)))) by lia.
          apply HK; [unfold shadow_addr, SHADOW_OFF in *; lia | apply HSHN; lia].
        * unfold fshadow_region. cbn [YP09.r_base base_val YP09.r_wlo YP09.r_whi]. rewrite ESH. unfold w64.
          rewrite unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF; lia).
          intros o Ho. apply (apresent_writable SEGS). apply GFsh4. unfold DFRAME_SH in Ho. lia.
    - rewrite <- HFLAG. apply jsc_rdword_kept. intros kk0 Hkk0.
      change (fs_frame_bytes DFRAME_CLASS) with 4096. apply HK; [lia | apply HPM; lia].
    - destruct HSLn as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
      split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|].
      split; [exact Q5|]. split; [exact Q6|]. exact Q7. }
  assert (HSHD4 : d_shadow (p_cx P) dsh_scr W mem2).
  { intros kk0 Hkk0. rewrite <- (HSHD kk0 Hkk0). unfold DFRAME_SH in Hkk0.
    apply HK; [unfold shadow_addr, SHADOW_OFF; lia | apply HSHN; lia]. }
  pose proof HGEO as (_ & _ & _ & _ & _ & _ & Gh & Gp).
  change (fs_frame_bytes DFRAME_CLASS) with 4096 in Gh, Gp.
  assert (HBODY4 : d_body B (p_cx P) (p_h P) (p_n P) (a3_xb (p_buf P) (p_op P)) dsh_scr ly3 S3 W mem2).
  { apply (DBRT (p_cx P) (p_h P) (p_n P) (p_n P) (a3_xb (p_buf P) (p_op P)) dsh_scr dsh_scr ly3 S3 W mem3 mem2
      (d_A (p_cx P) - 4096) (d_A (p_cx P)) Pk HBODY).
    - unfold LLVMF_STK. lia.
    - lia.
    - intros a [Ha|Ha]; [left; exact Ha | right].
      unfold d_rdset. intros [Hr|[Hr|[Hr|[Hr|[Hr|[Hr|[Hr|Hr]]]]]]].
      + unfold d_objr, d_obj in Hr. cbn [dobj_off dobj_size] in Hr. lia.
      + unfold d_objr, d_obj in Hr. cbn [dobj_off dobj_size] in Hr. lia.
      + unfold d_objr, d_obj in Hr. cbn [dobj_off dobj_size] in Hr. lia.
      + unfold d_objr, d_obj in Hr. cbn [dobj_off dobj_size] in Hr. lia.
      + lia.
      + destruct Hr as (Hn0 & Hr). destruct (Gp Hn0) as (_ & _ & Gpf & _). lia.
      + assert (Himg : in_img SEGS a).
        { destruct Hr as ([(s & Hs & _ & Hsa) | Hr] & _ & _);
            [exists s; split; [exact Hs | exact Hsa] | exact (pa_relro_img a Hr)]. }
        pose proof (pa_img_range a Himg) as Hra. unfold off_img in GFoff. lia.
      + pose proof HCAN as (_ & _ & Hcimg).
        pose proof (pa_img_range a (Hcimg a Hr)) as Hra. unfold off_img in GFoff. lia.
    - exact HK.
    - intros a _ Hp. exact (HPRES a Hp).
    - exact HFRM4.
    - exact HSHD4.
    - lia. }
  assert (Hinb : In (p_buf P, Z.max (slot_ser_defs.ser_cap (p_op P)) 1) (ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HPerm0)). unfold a3_xb. cbn [app]. left. reflexivity. }
  pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinb) as (_ & Hb4096 & Hbceil & _).
  pose proof (sep_block_frame SEGS B LAWS ly3 S3 W mem3 md3 _ _ _ _ HAR3 Hinb HFin3) as Hsep.
  rewrite EFA3 in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
  change (fs_frame_bytes DFRAME_CLASS) with 4096 in Hsep.
  assert (Hreq : req_size (Z.max (slot_ser_defs.ser_cap (p_op P)) 1) = Z.max (slot_ser_defs.ser_cap (p_op P)) 1).
  { unfold req_size. destruct (Z.eqb_spec (Z.max (slot_ser_defs.ser_cap (p_op P)) 1) 0); lia. }
  rewrite Hreq in Hbceil, Hsep.
  assert (P2 : getr regs2 2 = getr regs 2) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
  assert (P3 : getr regs2 3 = getr regs 3) by exact (HP 3 ltac:(unfold acallee_saved; lia)).
  assert (P4 : getr regs2 4 = getr regs 4) by exact (HP 4 ltac:(unfold acallee_saved; lia)).
  assert (P8 : getr regs2 8 = getr regs 8) by exact (HP 8 ltac:(unfold acallee_saved; lia)).
  assert (P9 : getr regs2 9 = getr regs 9) by exact (HP 9 ltac:(unfold acallee_saved; lia)).
  assert (P18 : getr regs2 18 = getr regs 18) by exact (HP 18 ltac:(unfold acallee_saved; lia)).
  assert (P19 : getr regs2 19 = getr regs 19) by exact (HP 19 ltac:(unfold acallee_saved; lia)).
  assert (P20 : getr regs2 20 = getr regs 20) by exact (HP 20 ltac:(unfold acallee_saved; lia)).
  assert (P21 : getr regs2 21 = getr regs 21) by exact (HP 21 ltac:(unfold acallee_saved; lia)).
  assert (P22 : getr regs2 22 = getr regs 22) by exact (HP 22 ltac:(unfold acallee_saved; lia)).
  assert (P23 : getr regs2 23 = getr regs 23) by exact (HP 23 ltac:(unfold acallee_saved; lia)).
  assert (P24 : getr regs2 24 = getr regs 24) by exact (HP 24 ltac:(unfold acallee_saved; lia)).
  assert (P25 : getr regs2 25 = getr regs 25) by exact (HP 25 ltac:(unfold acallee_saved; lia)).
  assert (P26 : getr regs2 26 = getr regs 26) by exact (HP 26 ltac:(unfold acallee_saved; lia)).
  assert (P27 : getr regs2 27 = getr regs 27) by exact (HP 27 ltac:(unfold acallee_saved; lia)).
  assert (KV : forall off nb v, 0 <= off -> off + Z.of_nat nb <= 472 ->
    val_mem SEGS (rd W mem3) (d_A (p_cx P) + off) nb v -> val_mem SEGS (rd W mem2) (d_A (p_cx P) + off) nb v).
  { intros off nb v Hoff Hnb Hv. apply (jk_val_mem_kept Pk W mem3 W mem2); [exact HK | lia | lia | | exact Hv].
    intros x Hx. apply HPA. lia. }
  assert (HOO2 : garr8 SEGS (rd W mem2) (d_obj (p_cx P) OO)
    (map (fun b : byte => bv_unsigned b) (slot_ser_defs.objs_bytes (p_buf P) (p_vpad P) (p_acc P ++ [p_c2 P])))).
  { rewrite Hc2. unfold p_vt.
    apply (c2cp_oo (rd W mem3) (rd W mem2) (d_obj (p_cx P) OO) (p_slot P ksl) (d_A (p_cx P) + 424) (p_buf P)
      (p_vpad P) (p_acc P) (p_cur P) ksl (p_vk P) (p_vs P) (p_vl P) HA6 HLcur Hks Hvk JLv).
    - unfold p_slot, jcur. lia.
    - intros i Hi0. apply c2cp_mbyte_eq. apply HCPY. exact Hi0.
    - intros a Ha Hna. apply (mbyte_of_aview SEGS). apply HK; [lia|]. intros [Hp|Hp]; [lia | exact (Hna Hp)].
    - exact V424.
    - replace (d_A (p_cx P) + 424 + 8) with (d_A (p_cx P) + 432) by lia. exact V432.
    - replace (d_A (p_cx P) + 424 + 16) with (d_A (p_cx P) + 440) by lia. exact V440.
    - replace (d_A (p_cx P) + 424 + 20) with (d_A (p_cx P) + 444) by lia. exact JGv.
    - exact JGo. }
  unfold jc2_out, jslot_in, jcut, d_arm_at_pf, d_at.
  split; [exact HFROM|].
  exists fq, ly3, S3, regs2, mem2, md2, k, acc.
  split; [unfold cfg_at; reflexivity|].
  split; [exact Hfrm0|]. split; [exact HBASE|]. split; [exact HJ2|]. split; [exact HFR|]. split; [exact Hk|].
  split; [exact Hnev|].
  split; [exact HMO|]. split; [exact Hacc|]. split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
  split.
  { split; [unfold spZ in *; rewrite P2; exact Rsp|].
    split; [rewrite P3; exact Rgp|]. split; [rewrite P4; exact Rtp|]. split; [rewrite P8; exact Rs0|].
    split; [rewrite P9; exact Rs1|]. split; [rewrite P19; exact Rs3|]. split; [rewrite P18; exact Rs2|].
    split; [rewrite P20; exact Rs4|]. rewrite P27; exact Rs11. }
  split.
  { split; [rewrite P26; exact R26|]. split; [rewrite P24; exact R24|]. split; [rewrite P25; exact R25|].
    split; [rewrite P21; exact R21|]. split; [rewrite P22; exact R22 | rewrite P23; exact R23]. }
  split.
  { pose proof HSP1 as ((H208 & H320) & H192 & H200).
    split; [split; [split|split]|].
    - apply KV; [lia | lia | exact H208].
    - apply KV; [lia | lia | exact H320].
    - apply KV; [lia | lia | exact H192].
    - apply KV; [lia | lia | exact H200].
    - split.
      { pose proof HTAB as (HTex & HgOT). split; [exact HTex|].
        destruct HTex as (rem & _ & HAP). pose proof HAP as (HlenT1 & _).
        apply (jk_garr8_kept Pk W mem3 W mem2); [exact HK | unfold d_obj; cbn [dobj_off]; lia | | | exact HgOT].
        - rewrite length_map, HlenT1. unfold d_obj; cbn [dobj_off]. lia.
        - intros x Hx. rewrite length_map, HlenT1 in Hx. unfold d_obj in Hx; cbn [dobj_off] in Hx. apply HPM. lia. }
      split.
      { pose proof HBUF as ((Hr2 & Hrc) & HgB). split; [split; [exact Hr2 | exact Hrc]|].
        apply (jk_garr8_kept Pk W mem3 W mem2); [exact HK | lia | | | exact HgB].
        - rewrite length_app. cbn [length]. unfold a3_r in *. lia.
        - intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. unfold a3_r in *.
          intros [Hp|Hp]; lia. }
      split; [exact HFIN|]. split; [exact Hip|]. split; [exact Hc0|]. split; [exact Hlen|].
      split; [rewrite HWS in HPC; exact HPC|].
      split; [exact HLc2|]. split; [exact HFc2|].
      split.
      { split; [exact JLv|].
        split.
        { apply (jk_garr8_kept Pk W mem3 W mem2); [exact HK | lia | | | exact JGv].
          - rewrite length_map, JLv. lia.
          - intros x Hx. apply HPA. lia. }
        split; [exact HOO2|].
        apply Forall_app. split; [exact HA6 | constructor; [exact HLc2 | constructor]]. }
      split; [apply KV; [lia | lia | exact JS408]|].
      split; [apply KV; [lia | lia | exact JS368]|].
      split; [apply KV; [lia | lia | exact JS360]|].
      split; [apply KV; [lia | lia | exact JS328]|].
      split; [apply KV; [lia | lia | exact JS296] | apply KV; [lia | lia | exact JS352]]. }
  split.
  { pose proof HSP0 as (Z208 & Z320).
    split; [apply KV; [lia | lia | exact Z208] | apply KV; [lia | lia | exact Z320]]. }
  exact HBODY4.
Qed.

End h.
End f.
End d.
