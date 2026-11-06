(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr ImageA.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords.
From OSSVerify.Proofs.openssl.bndiv.lib.A Require Import Layout Shadow.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnCmp.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require W_cmp_words.
From OSSVerify.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop AW_cmp_words.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition bn_cmp_part_words_aentry := 0x1f632c%Z.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a b : list Z) (cl da db : nat) (lo : Z).
  Notation ap := (bv_unsigned a0).
  Notation bp := (bv_unsigned a1).
  Notation SP := (bv_unsigned sp).
  Hypothesis LA : limbs a.
  Hypothesis LB : limbs b.
  Hypothesis HLA : length a = (cl + da)%nat.
  Hypothesis HLB : length b = (cl + db)%nat.
  Hypothesis DAB : (da = 0 \/ db = 0)%nat.
  Hypothesis NA31 : (Z.of_nat (cl + da + db) < 2147483648)%Z.
  Hypothesis A2 : bv_unsigned a2 = Z.of_nat cl.
  Hypothesis A3 : a3 = Z_to_bv 64 (Z.of_nat da - Z.of_nat db).
  Hypothesis RA : limbs_at asegs m ap a.
  Hypothesis RB : limbs_at asegs m bp b.
  Hypothesis STK : stk asegs m lo SP.
  Hypothesis LO : (lo <= SP - 16)%Z.
  Hypothesis SEPA : (ap + 8 * Z.of_nat (length a) <= SP - 16 \/ SP <= ap)%Z.
  Hypothesis SEPB : (bp + 8 * Z.of_nat (length b) <= SP - 16 \/ SP <= bp)%Z.
  Hypothesis MI0 : mem_inv asegs m.
  (* [comment removed for export] *)
  Hypothesis SHBC : shb_cells asegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m.
  Hypothesis ACA : acc asegs m ap (8 * Z.of_nat (length a)).
  Hypothesis ACB : acc asegs m bp (8 * Z.of_nat (length b)).
  Hypothesis AL8A : (ap mod 8 = 0)%Z.
  Hypothesis AL8B : (bp mod 8 = 0)%Z.
  Hypothesis SHLO_LO : (SHHI <= lo)%Z.

  (* [comment removed for export] *)
  Collection Safe := LA LB HLA HLB DAB NA31 A2 A3 LO SEPA SEPB ACA ACB AL8A AL8B SHLO_LO.

  Notation POST := (ro_post asegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 16%Z (cmp_part_words a b cl) lo m).

  (* [comment removed for export] *)
  Notation ST pc mm x5 x6 x8 x10 x13 x14 x15 x16 x17 :=
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 x6 t2 x8 s1 x10 a1 a2 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
  Notation FW := [(SP + -16, SP)]%Z.

  (* [comment removed for export] *)
  Definition CINV (m1 : word -> option byte) : Prop :=
    limbs_at asegs m1 ap a /\ limbs_at asegs m1 bp b /\
    rw_cells asegs m1 (SP + -16) [C8 s0; C8 ra] /\ stk asegs m1 lo (SP + -16) /\
    mem_inv asegs m1 /\ munch FW m m1 /\ wmono asegs m m1 /\
    shb_cells asegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m1.

  (* [comment removed for export] *)
  Definition cpure : Prop :=
    ((0 < Z.of_nat (length a))%Z -> (0 <= ap /\ ap + 8 * Z.of_nat (length a) <= 140737488355328)%Z) /\
    ((0 < Z.of_nat (length b))%Z -> (0 <= bp /\ bp + 8 * Z.of_nat (length b) <= 140737488355328)%Z) /\ offshW FW
    /\ (lo <= SP - 16)%Z
    /\ (ap + 8 * Z.of_nat (length a) <= SP - 16 \/ SP <= ap)%Z /\ (bp + 8 * Z.of_nat (length b) <= SP - 16 \/ SP <= bp)%Z.

  Lemma cpure_intro : cpure.
  Proof.
    unfold cpure.
    pose proof (limbs_at_bound _ _ _ _ RA) as BA. pose proof (limbs_at_bound _ _ _ _ RB) as BB.
    assert (NE : forall l : list Z, (0 < Z.of_nat (length l))%Z -> lbytes l <> []).
    { intros l Hl E. pose proof (lbytes_lengthZ l) as L. rewrite E in L. cbn [length] in L. lia. }
    split. { intros Hn. pose proof (bytes_at_below asegs m ap _ MI0 RA (NE a Hn)) as TA. rewrite lbytes_lengthZ in TA. unfold UTOP in TA. lia. }
    split. { intros Hn. pose proof (bytes_at_below asegs m bp _ MI0 RB (NE b Hn)) as TB. rewrite lbytes_lengthZ in TB. unfold UTOP in TB. lia. }
    split. { cbn [offshW]. split; [right; unfold SHHI in *; lia | exact I]. }
    split; [exact LO|]. split; [exact SEPA | exact SEPB].
  Qed.

  (* [comment removed for export] *)
  Lemma shA : forall m1 (k : nat) ad, cpure -> CINV m1 -> (k < length a)%nat -> ad = wa (shad (ap + 8 * Z.of_nat k)) ->
    ov_read_bytes asegs m1 ad 1 = Some [z8].
  Proof using Safe.
    intros m1 k ad (BA & _ & OFF & _) (_ & _ & _ & _ & _ & MU & _ & _) Hk ->.
    apply (acc_rd_limb asegs FW m m1 ap (Z.of_nat (length a)) 0 (Z.of_nat k) _ ACA MU OFF AL8A (BA ltac:(lia))); [reflexivity | lia | lia | lia |].
    rewrite Z.add_0_r. reflexivity.
  Qed.
  Lemma shB : forall m1 (k : nat) ad, cpure -> CINV m1 -> (k < length b)%nat -> ad = wa (shad (bp + 8 * Z.of_nat k)) ->
    ov_read_bytes asegs m1 ad 1 = Some [z8].
  Proof using Safe.
    intros m1 k ad (_ & BB & OFF & _) (_ & _ & _ & _ & _ & MU & _ & _) Hk ->.
    apply (acc_rd_limb asegs FW m m1 bp (Z.of_nat (length b)) 0 (Z.of_nat k) _ ACB MU OFF AL8B (BB ltac:(lia))); [reflexivity | lia | lia | lia |].
    rewrite Z.add_0_r. reflexivity.
  Qed.

  Lemma HBsk : length (skipn cl b) = db. Proof using Safe. rewrite length_skipn. lia. Qed.
  Lemma HAsk : length (skipn cl a) = da. Proof using Safe. rewrite length_skipn. lia. Qed.

  (* [comment removed for export] *)
  Lemma cpw_ret : forall m1 res x5 x6 x8 x13 x14 x15 x16 x17, CINV m1 -> res = cmp_part_words a b cl ->
    evt asegs POST (ST 0x1f63f8 m1 x5 x6 x8 (Z_to_bv 64 res) x13 x14 x15 x16 x17).
  Proof using Safe.
    intros m1 res x5 x6 x8 x13 x14 x15 x16 x17 (HA & HB & FR & ST & MI & MU & WM & _) ->.
    do 4 zstep.
    release_frame FR ST (bv_unsigned sp).
    finish.
  Qed.

  (* [comment removed for export] *)
  Lemma cpw_neg : forall m1 x5 x6 x8 x10 x13 x14 x15 x16 x17, CINV m1 -> existsb nonzero (skipn cl b) = true ->
    evt asegs POST (ST 0x1f63f4 m1 x5 x6 x8 x10 x13 x14 x15 x16 x17).
  Proof using Safe.
    intros m1 x5 x6 x8 x10 x13 x14 x15 x16 x17 I E.
    zstep. eapply cpw_ret; [exact I|]. unfold cmp_part_words. rewrite E. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma cpw_pos : forall m1 x5 x6 x8 x10 x13 x14 x15 x16 x17, CINV m1 ->
    existsb nonzero (skipn cl b) = false -> existsb nonzero (skipn cl a) = true ->
    evt asegs POST (ST 0x1f63ec m1 x5 x6 x8 x10 x13 x14 x15 x16 x17).
  Proof using Safe.
    intros m1 x5 x6 x8 x10 x13 x14 x15 x16 x17 I Eb Ea.
    do 2 zstep. eapply cpw_ret; [exact I|]. unfold cmp_part_words. rewrite Eb, Ea. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma acc_pref : forall m1 p (l : list Z) k, acc asegs m p (8 * Z.of_nat (length l)) -> munch FW m m1 -> offshW FW ->
    ((0 < Z.of_nat (length l))%Z -> (0 <= p /\ p + 8 * Z.of_nat (length l) <= 140737488355328)%Z) -> (k <= length l)%nat ->
    acc asegs m1 p (8 * Z.of_nat k).
  Proof using Safe.
    intros m1 p l k AC MU OFF B Hk.
    destruct k as [|k]. { intros i Hi. exfalso. clear - Hi. lia. }
    pose proof (B ltac:(lia)) as B'.
    eapply acc_munch; [ eapply acc_sub; [exact AC | | ] | exact MU | exact OFF | | ]; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma cpw_tail : forall m1 x5 x6 x13 x14 x15 x16 x17, cpure -> CINV m1 ->
    existsb nonzero (skipn cl b) = false -> existsb nonzero (skipn cl a) = false ->
    evt asegs POST (ST 0x1f63dc m1 x5 x6 sp a0 x13 x14 x15 x16 x17).
  Proof using Safe.
    intros m1 x5 x6 x13 x14 x15 x16 x17 (BA & BB & OFF & LO' & SA' & SB') (HA & HB & FR & ST & MI & MU & WM & SHC) Eb Ea.
    do 4 zstep.
    release_frame FR ST (bv_unsigned sp).
    eapply evt_mono.
    - assert (La : length (firstn cl a) = cl) by (rewrite length_firstn; lia).
      assert (Lb : length (firstn cl b) = cl) by (rewrite length_firstn; lia).
      eapply bn_cmp_words_aspec with (a := firstn cl a) (b := firstn cl b) (lo := lo).
      + apply limbs_firstn. exact LA.
      + apply limbs_firstn. exact LB.
      + rewrite La, Lb. reflexivity.
      + rewrite La. clear - NA31. lia.
      + rewrite La. exact A2.
      + rewrite <- (firstn_skipn cl a) in HA. apply limbs_at_app in HA. exact (proj1 HA).
      + rewrite <- (firstn_skipn cl b) in HB. apply limbs_at_app in HB. exact (proj1 HB).
      + exact ST.
      + exact LO.
      + rewrite La. clear - SEPA HLA. lia.
      + rewrite La. clear - SEPB HLB. lia.
      + exact MI.
      + exact SHC.
      + rewrite La. eapply (acc_pref m1 ap a cl ACA MU OFF BA). clear - HLA. lia.
      + rewrite La. eapply (acc_pref m1 bp b cl ACB MU OFF BB). clear - HLB. lia.
      + exact AL8A.
      + exact AL8B.
      + exact SHLO_LO.
    - intros ms' (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & E & MU' & WM' & MI' & ST').
      exists u0, u1, u2, v1, v2, v3, v4, v5, v6, v7, u3, u4, u5, u6, m'.
      split. { rewrite E. unfold cmp_part_words. rewrite Eb, Ea. reflexivity. }
      split. { eapply munch_trans; [ | exact MU']. replace (SP - 16)%Z with (SP + -16)%Z by lia. exact MU. }
      split. { eapply wmono_trans; [exact WM | exact WM']. }
      split; [exact MI' | exact ST'].
  Qed.

  (* [comment removed for export] *)
  Lemma cpw_loopA : forall (j : nat) m1 x5 x6, cpure -> CINV m1 -> db = 0%nat -> (1 <= j <= da)%nat -> zeros_above (skipn cl a) j ->
    evt asegs POST (ST 0x1f63b4 m1 x5 x6 sp a0 (Z_to_bv 64 (ap + 8 * Z.of_nat (cl + j) + -8)) (Z_to_bv 64 (ap + 8 * Z.of_nat (cl + j) + -8))
                       (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.of_nat j + 1)) (Z_to_bv 64 2)).
  Proof using Safe.
    induction j as [|j IH]; intros m1 x5 x6 P I Hdb Hj Z; [exfalso; lia|].
    pose proof I as (HA & _).
    assert (Eb : existsb nonzero (skipn cl b) = false).
    { apply existsb_nonzero_zeros. intros i y _ E. exfalso. assert (nth_error (skipn cl b) i <> None) by congruence.
      apply nth_error_Some in H. rewrite HBsk in H. lia. }
    destruct (nth_error a (cl + j)) as [x|] eqn:Ex; [|apply nth_error_None in Ex; lia].
    pose proof (limbs_nth_error_lit a _ x LA Ex) as Rx.
    assert (Exs : nth_error (skipn cl a) j = Some x) by (rewrite nth_error_skipn; exact Ex).
    assert (Hka : (cl + j < length a)%nat) by (clear - HLA Hj; lia).
    pose proof P as (BA & _). pose proof (BA ltac:(clear - Hka; lia)) as BA'. clear BA.
    do 2 zstep.
    (let ad := cur_mem_addr in pose proof (shA m1 (cl + j) ad P I Hka ltac:(sh_addr)) as RD); zstep; clear RD.
    chk0.
    (let ad := cur_mem_addr in pose proof (limbs_at_read_nth asegs m1 ap a (cl + j) x ad HA Ex ltac:(unfold wa; f_equal; lia)) as RD); zstep; clear RD.
    zstep. if_cases K; zify_cond K.
    - eapply cpw_pos; [exact I | exact Eb | exact (existsb_nonzero_nth _ _ _ Exs K)].
    - subst x. pose proof (zeros_above_step _ _ Z Exs) as Z'.
      do 3 zstep.
      setreg 16%Z (Z_to_bv 64 (Z.of_nat j + 1)) ltac:(f_equal; clear; lia).
      setreg 13%Z (Z_to_bv 64 (ap + 8 * Z.of_nat (cl + j) + -8)) ltac:(f_equal; clear; lia).
      setreg 14%Z (Z_to_bv 64 (ap + 8 * Z.of_nat (cl + j) + -8)) ltac:(f_equal; clear; lia).
      zstep. rewrite lts_signed by (clear - Hj NA31; lia).
      if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        eapply IH; [exact P | exact I | exact Hdb | clear - K2 Hj; lia | exact Z'].
      + (* [comment removed for export] *)
        assert (j = 0%nat) by (clear - K2; lia). subst j.
        eapply cpw_tail; [exact P | exact I | exact Eb | exact (existsb_nonzero_zeros _ Z')].
  Qed.

  (* [comment removed for export] *)
  Lemma cpw_loopB : forall (j : nat) m1 x6, cpure -> CINV m1 -> (1 <= j <= db)%nat -> zeros_above (skipn cl b) j ->
    (forall x5 x6' x14 x17, zeros_above (skipn cl b) 0 ->
       evt asegs POST (ST 0x1f6394 m1 x5 x6' sp a0 (Z_to_bv 64 (- Z.of_nat db)) x14 (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.of_nat cl + -1)) x17)) ->
    evt asegs POST (ST 0x1f636c m1 (Z_to_bv 64 (- Z.of_nat j)) x6 sp a0 (Z_to_bv 64 (- Z.of_nat db)) (Z_to_bv 64 (bp + 8 * Z.of_nat (cl + j) + -8))
                       (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.of_nat cl + -1)) (Z_to_bv 64 (bp + 8 * Z.of_nat (cl + j) + -8))).
  Proof using Safe.
    induction j as [|j IH]; intros m1 x6 P I Hj Z KMID; [exfalso; lia|].
    pose proof I as (_ & HB & _).
    destruct (nth_error b (cl + j)) as [y|] eqn:Ey; [|apply nth_error_None in Ey; lia].
    pose proof (limbs_nth_error_lit b _ y LB Ey) as Ry.
    assert (Eys : nth_error (skipn cl b) j = Some y) by (rewrite nth_error_skipn; exact Ey).
    assert (Hkb : (cl + j < length b)%nat) by (clear - HLB Hj; lia).
    pose proof P as (_ & BB & _). pose proof (BB ltac:(clear - Hkb; lia)) as BB'. clear BB.
    do 2 zstep.
    (let ad := cur_mem_addr in pose proof (shB m1 (cl + j) ad P I Hkb ltac:(sh_addr)) as RD); zstep; clear RD.
    chk0.
    (let ad := cur_mem_addr in pose proof (limbs_at_read_nth asegs m1 bp b (cl + j) y ad HB Ey ltac:(unfold wa; f_equal; lia)) as RD); zstep; clear RD.
    zstep. if_cases K; zify_cond K.
    - eapply cpw_neg; [exact I | exact (existsb_nonzero_nth _ _ _ Eys K)].
    - subst y. pose proof (zeros_above_step _ _ Z Eys) as Z'.
      do 3 zstep.
      setreg 5%Z (Z_to_bv 64 (- Z.of_nat j)) ltac:(f_equal; clear; lia).
      setreg 14%Z (Z_to_bv 64 (bp + 8 * Z.of_nat (cl + j) + -8)) ltac:(f_equal; clear; lia).
      setreg 17%Z (Z_to_bv 64 (bp + 8 * Z.of_nat (cl + j) + -8)) ltac:(f_equal; clear; lia).
      zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        eapply IH; [exact P | exact I | | exact Z' | exact KMID].
        assert (j <> 0%nat) by (intros ->; apply K2; reflexivity). clear - H Hj. lia.
      + (* [comment removed for export] *)
        assert (j = 0%nat).
        { destruct j as [|j']; [reflexivity | exfalso]. clear - K2 Hj NA31.
          rewrite Z.mod_opp_l_nz in K2; rewrite ?Z.mod_small in * by lia; lia. }
        subst j. apply KMID. exact Z'.
  Qed.

  (* [comment removed for export] *)
  Lemma cpw_mid : forall m1 x5 x6 x14 x17, cpure -> CINV m1 -> zeros_above (skipn cl b) 0 ->
    evt asegs POST (ST 0x1f6394 m1 x5 x6 sp a0 (Z_to_bv 64 (Z.of_nat da - Z.of_nat db)) x14 (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.of_nat cl + -1)) x17).
  Proof using Safe.
    intros m1 x5 x6 x14 x17 P I Zb.
    pose proof (existsb_nonzero_zeros _ Zb) as Eb.
    zstep. rewrite lts_signed by (clear - NA31; lia).
    if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      assert (da = 0%nat) by (clear - K DAB; lia).
      eapply cpw_tail; [exact P | exact I | exact Eb |].
      apply existsb_nonzero_zeros. intros i y _ E. exfalso. assert (nth_error (skipn cl a) i <> None) by congruence.
      apply nth_error_Some in H0. rewrite HAsk in H0. lia.
    - assert (Hda : (1 <= da)%nat /\ db = 0%nat) by (clear - K DAB; lia). destruct Hda as (Hda & Hdb).
      do 7 zstep.
      setreg 16%Z (Z_to_bv 64 (Z.of_nat da + 1)) ltac:(f_equal; clear - Hdb; lia).
      setreg 13%Z (Z_to_bv 64 (ap + 8 * Z.of_nat (cl + da) + -8))
        ltac:(apply Z_to_bv_eqm; rewrite !Z.shiftl_mul_pow2 by lia; change (2 ^ 3)%Z with 8%Z; change (2 ^ 64)%Z with 18446744073709551616%Z;
              clear - Hdb; subst db; Z.div_mod_to_equations; lia).
      eapply cpw_loopA; [exact P | exact I | exact Hdb | clear - Hda; lia |].
      pose proof (zeros_above_len (skipn cl a)) as ZL. rewrite HAsk in ZL. exact ZL.
  Qed.
  (* [comment removed for export] *)
  Lemma bn_cmp_part_words_aspec :
    evt asegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1f632c) fc None m (seg_rom asegs)).
  Proof.
    pose proof (munch_refl [(SP - 16, SP)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (LOHI : (17594333495296 <= lo)%Z) by (clear - SHLO_LO; unfold SHHI in SHLO_LO; exact SHLO_LO).
    pose proof cpure_intro as P.
    destruct SHBC as [G1 G2]. unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in G1, G2.
    carve_frame 16%nat STK.
    do 4 zstep.
    assert (I : CINV m1).
    { unfold CINV. split; [|split].
      - eapply limbs_at_transport; [exact RA | exact MU | cbn [disjoint_from]; lia].
      - eapply limbs_at_transport; [exact RB | exact MU | cbn [disjoint_from]; lia].
      - split; [exact FR|]. split; [exact STK|]. split; [exact MI0|]. split; [exact MU |]. split; [exact WM|]. split; [exact G1 | exact G2]. }
    do 3 zstep.
    clear RA RB FR STK MI0 MU WM G1 G2.
    zstep. rewrite A2. rewrite (bn_swrap32_small (Z.of_nat cl + -1)) by (clear - NA31; lia).
    rewrite A3.
    zstep. rewrite lts_signed by (clear - NA31; lia).
    if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      assert (Hdb : db = 0%nat) by (clear - K DAB; lia).
      eapply cpw_mid; [exact P | exact I|].
      intros i y _ E. exfalso. assert (nth_error (skipn cl b) i <> None) by congruence.
      apply nth_error_Some in H. rewrite HBsk in H. lia.
    - assert (Hdb : (1 <= db)%nat /\ da = 0%nat) by (clear - K DAB; lia). destruct Hdb as (Hdb & Hda).
      do 7 zstep.
      setreg 5%Z (Z_to_bv 64 (- Z.of_nat db)) ltac:(f_equal; clear - Hda; lia).
      setreg 14%Z (Z_to_bv 64 (bp + 8 * Z.of_nat (cl + db) + -8))
        ltac:(apply Z_to_bv_eqm; rewrite !Z.shiftl_mul_pow2 by lia; change (2 ^ 3)%Z with 8%Z; change (2 ^ 64)%Z with 18446744073709551616%Z;
              clear - Hda; subst da; Z.div_mod_to_equations; lia).
      eapply cpw_loopB; [exact P | exact I | clear - Hdb; lia | |].
      + pose proof (zeros_above_len (skipn cl b)) as ZL. rewrite HBsk in ZL. exact ZL.
      + intros y5 y6 y14 y17 Zb.
        replace (- Z.of_nat db)%Z with (Z.of_nat da - Z.of_nat db)%Z by (clear - Hda; lia).
        eapply cpw_mid; [exact P | exact I | exact Zb].
  Qed.

End Proofs.
