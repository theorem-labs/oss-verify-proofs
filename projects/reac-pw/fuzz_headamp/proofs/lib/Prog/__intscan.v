From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import CType CTypeFacts.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import __intscan_c __shlim_c __errno_location_c.
Import ListNotations.
Open Scope Z_scope.

Lemma sw32 : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. intros z Hz. apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). lia. Qed.

Lemma sw32_hi : forall z, 2^31 <= z < 2^32 -> bv_swrap 32 z = z - 2^32.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^31) with 2147483648 in Hz. change (2^32) with 4294967296 in Hz |- *.
  replace (z + 2147483648) with ((z - 2147483648) + 1 * 4294967296) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma zx32 : forall z, 0 <= z < 2^32 -> (bv_swrap 32 z mod 18446744073709551616) mod 4294967296 = z.
Proof.
  intros z Hz. destruct (Z.lt_ge_cases z (2^31)).
  - rewrite sw32 by lia. rewrite (Z.mod_small z) by lia. rewrite Z.mod_small by lia. reflexivity.
  - rewrite sw32_hi by lia. Z.div_mod_to_equations. lia.
Qed.

Lemma dval_ge : forall s acc, 0 <= acc -> acc <= dval acc s.
Proof.
  induction s as [|b s IH]; intros acc H; cbn [dval]; [lia|].
  destruct (c_digit b) eqn:E; [|lia].
  unfold c_digit in E. apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
  specialize (IH (10 * acc + (bv_unsigned b - 48)) ltac:(lia)). lia.
Qed.

Lemma digit_rng : forall b : byte, c_digit b = true -> 48 <= bv_unsigned b <= 57.
Proof.
  intros b H. unfold c_digit in H. apply andb_prop in H. destruct H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Lemma dstep : forall (str : list byte) i b acc, nth_error (str ++ [Z_to_bv 8 0]) i = Some b -> (i <= length str)%nat ->
  dval acc (skipn i str) = if c_digit b then dval (10 * acc + (bv_unsigned b - 48)) (skipn (S i) str) else acc.
Proof. intros str i b acc H HI. destruct (txt_cases str i b H HI) as [(L & E) | (L & -> & E)]; rewrite E; reflexivity. Qed.

Lemma nstep : forall (str : list byte) i b, nth_error (str ++ [Z_to_bv 8 0]) i = Some b -> (i <= length str)%nat ->
  ndig (skipn i str) = if c_digit b then S (ndig (skipn (S i) str)) else O.
Proof. intros str i b H HI. destruct (txt_cases str i b H HI) as [(L & E) | (L & -> & E)]; rewrite E; reflexivity. Qed.

Lemma sp_step : forall (str : list byte) i b, nth_error (str ++ [Z_to_bv 8 0]) i = Some b -> (i <= length str)%nat ->
  c_space b = true -> skip_space (skipn i str) = skip_space (skipn (S i) str).
Proof.
  intros str i b H HI SP. destruct (txt_cases str i b H HI) as [(L & E) | (L & -> & E)].
  - rewrite E. cbn [skip_space]. rewrite SP. reflexivity.
  - exfalso. vm_compute in SP. discriminate.
Qed.

Lemma sp_stop : forall (str : list byte) i b, nth_error (str ++ [Z_to_bv 8 0]) i = Some b -> (i <= length str)%nat ->
  c_space b = false -> skip_space (skipn i str) = skipn i str.
Proof.
  intros str i b H HI SP. destruct (txt_cases str i b H HI) as [(L & E) | (L & -> & E)].
  - rewrite E. cbn [skip_space]. rewrite SP. reflexivity.
  - rewrite E. reflexivity.
Qed.

Lemma sg_split : forall (str : list byte) j b, nth_error (str ++ [Z_to_bv 8 0]) j = Some b -> (j <= length str)%nat ->
  sign_split (skipn j str) =
    if bv_unsigned b =? 45 then (true, skipn (S j) str)
    else if bv_unsigned b =? 43 then (false, skipn (S j) str) else (false, skipn j str).
Proof. intros str j b H HJ. destruct (txt_cases str j b H HJ) as [(L & E) | (L & -> & E)]; rewrite E; reflexivity. Qed.

Lemma end_eq : forall (str : list byte) k, s10_rest str = skipn k str -> (k <= length str)%nat ->
  s10_end str = if (s10_nd str =? 0)%nat then 0 else Z.of_nat (k + s10_nd str).
Proof.
  intros str k H HK. unfold s10_end. rewrite H, length_skipn.
  replace (length str - (length str - k))%nat with k by lia. reflexivity.
Qed.

Lemma err_nod : forall s ev, s10_nd s = O -> s10_errno s ev = Z_to_bv 64 22.
Proof. intros s ev H. unfold s10_errno. rewrite H. reflexivity. Qed.

Lemma err_in : forall s ev, s10_nd s <> O -> -9223372036854775808 <= s10_signed s <= 9223372036854775807 ->
  s10_errno s ev = ev.
Proof.
  intros s ev H1 H2. unfold s10_errno, s10_inrange, LMIN. destruct (s10_nd s); [congruence|]. cbn [Nat.eqb].
  rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
Qed.

Lemma err_out : forall s ev, s10_nd s <> O -> (s10_signed s < -9223372036854775808 \/ 9223372036854775807 < s10_signed s) ->
  s10_errno s ev = Z_to_bv 64 34.
Proof.
  intros s ev H1 H2. unfold s10_errno, s10_inrange, LMIN. destruct (s10_nd s); [congruence|]. cbn [Nat.eqb].
  destruct H2 as [H2|H2].
  - rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity.
  - rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity.
Qed.

Definition TBL : list byte := match image_bytes rsegs 70385 256 with Some l => l | None => [] end.
Definition tbl_ok (l : list byte) : bool :=
  forallb (fun i => Bool.eqb (bv_unsigned (nth i l (Z_to_bv 8 0)) <? 10) ((48 <=? Z.of_nat i) && (Z.of_nat i <=? 57)))
    (seq 0 256).
Lemma TBL_len : length TBL = 256%nat. Proof. vm_compute. reflexivity. Qed.
Lemma TBL_ro : ro_bytes_b rsegs 70385 TBL = true. Proof. vm_compute. reflexivity. Qed.
Lemma TBL_ok : tbl_ok TBL = true. Proof. vm_compute. reflexivity. Qed.

Lemma tbl : forall mm (c : byte), mem_inv rsegs mm -> exists t : byte,
  ov_read_bytes rsegs mm (wa (70384 + bv_unsigned c + 1)) 1 = Some [t] /\ (bv_unsigned t < 10 <-> c_digit c = true).
Proof.
  intros mm c MI. pose proof (byte_rng c) as Rc.
  pose proof (ro_cells_image rsegs mm 70385 TBL MI TBL_ro ltac:(lia) ltac:(rewrite TBL_len; lia)) as RO.
  destruct RO as [_ BT]. cbn [cells_bytes cbytes] in BT. rewrite app_nil_r in BT.
  destruct (nth_error TBL (Z.to_nat (bv_unsigned c))) as [t|] eqn:E.
  2:{ apply nth_error_None in E. rewrite TBL_len in E. lia. }
  exists t. split.
  - eapply (u8ro_read rsegs mm 70385 TBL (bv_unsigned c) t); [exact BT | exact E | lia | unfold wa; f_equal; lia].
  - pose proof TBL_ok as OK. unfold tbl_ok in OK. rewrite forallb_forall in OK.
    specialize (OK (Z.to_nat (bv_unsigned c)) ltac:(apply in_seq; lia)).
    replace (nth (Z.to_nat (bv_unsigned c)) TBL (Z_to_bv 8 0)) with t in OK by (symmetry; apply nth_error_nth; exact E).
    rewrite Z2Nat.id in OK by lia. unfold c_digit.
    destruct (Z.ltb_spec (bv_unsigned t) 10), (Z.leb_spec 48 (bv_unsigned c)), (Z.leb_spec (bv_unsigned c) 57);
      cbn in OK |- *; split; intro; first [discriminate | lia | reflexivity].
Qed.

Section IS.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp P : Z) (str : list byte) (ev : word) (lo : Z).
  Hypothesis ERR : __errno_location_contract.
  Hypothesis SHL : __shlim_contract.
  Hypothesis HP : 0 <= P /\ P + Z.of_nat (length str) + 1 < 2^64.
  Hypothesis HF : 0 <= Fp + 8 /\ Fp + 208 <= 2^64.
  Hypothesis HT : 0 <= bv_unsigned tp + -164 /\ bv_unsigned tp + -164 + 4 <= 2^64.
  Hypothesis HS : 0 <= lo /\ lo + 80 <= bv_unsigned sp /\ bv_unsigned sp < 2^64.
  Hypothesis D1 : Fp + 232 <= lo \/ bv_unsigned sp <= Fp.
  Hypothesis D2 : P + Z.of_nat (length str) + 1 <= lo \/ bv_unsigned sp <= P.
  Hypothesis D3 : bv_unsigned tp + -164 + 4 <= lo \/ bv_unsigned sp <= bv_unsigned tp + -164.
  Hypothesis D4 : P + Z.of_nat (length str) + 1 <= Fp \/ Fp + 232 <= P.
  Hypothesis D5 : bv_unsigned tp + -164 + 4 <= Fp \/ Fp + 232 <= bv_unsigned tp + -164.

  Notation WF := [(bv_unsigned sp + -80, bv_unsigned sp); (Fp + 8, Fp + 16); (Fp + 184, Fp + 208);
                  (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)].
  Notation POST := (__intscan_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp P str ev lo m).
  Notation FRc := [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Notation LM := (Z_to_bv 64 9223372036854775808).
  Notation GS pc mm x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp x5 x6 x7 x8 (Z_to_bv 64 Fp) x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).
  Notation LS pc mm x10 x11 x12 x18 x19 x20 x21 x22 x23 x24 :=
    (GS pc mm ra t0 t1 t2 LM x10 x11 x12 LM a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 t3 t4 t5 t6).
  Notation msk neg := (Z_to_bv 64 (if neg then 18446744073709551615 else 0)).

  Definition INV (mm : word -> option byte) (j : nat) : Prop :=
    mem_inv rsegs mm /\ bytes_at rsegs mm P (str ++ [Z_to_bv 8 0]) /\
    rw_cells rsegs mm (Fp + 8) [C8 (Z_to_bv 64 (P + Z.of_nat j)); C8 (Z_to_bv 64 18446744073709551615)] /\
    rw_cells rsegs mm (Fp + 88) [C8 (Z_to_bv 64 P)] /\
    rw_cells rsegs mm (Fp + 184) [C8 (Z_to_bv 64 18446744073709551615); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] /\
    rw_cells rsegs mm (bv_unsigned tp + -164) [C4 ev] /\
    rw_cells rsegs mm (bv_unsigned sp + -80) FRc /\
    stk rsegs mm lo (bv_unsigned sp + -80) /\ munch WF m mm /\ wmono rsegs m mm.

  Lemma rd : forall mm k b, bytes_at rsegs mm P (str ++ [Z_to_bv 8 0]) -> nth_error (str ++ [Z_to_bv 8 0]) k = Some b ->
    ov_read_bytes rsegs mm (wa (P + Z.of_nat k)) 1 = Some [b].
  Proof using HP. intros mm k b H E. eapply (u8ro_read rsegs mm P); [exact H | rewrite Nat2Z.id; exact E | lia | reflexivity]. Qed.

  Ltac dinv H := destruct H as (MI & BY & RP & BF & SH & ER & FR & ST & MU & WM).
  Ltac minv := unfold INV; repeat (split; [assumption|]); assumption.
  Ltac errcall :=
    eapply evt_cut; [apply ERR | ];
    let ms' := fresh "ms'" in let EQ := fresh "EQ" in
    intros ms' EQ; cbv beta in EQ; subst ms'; unfold ERRNO_TP_OFF;
    lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity])
    end.
  Ltac vfin SG :=
    unfold s10_val, LMIN; rewrite SG; apply Z_to_bv_eqm;
    rewrite ?Z.lxor_0_r, ?zb_lxor_ones by lia; Z.div_mod_to_equations; lia.
  Ltac rdr k b Hb :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with HB : bytes_at rsegs mm P _ |- _ =>
        let RD := fresh "RD" in pose proof (rd mm k b HB Hb) as RD end end.
  Ltac tblr c t HR HT :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with HI : mem_inv rsegs mm |- _ => destruct (tbl mm c HI) as (t & HR & HT) end end.
  Ltac cfold :=
    repeat match goal with |- context [Z_to_bv 64 ?e] =>
      tryif is_Zlit e then fail else (let v := eval vm_compute in e in is_Zlit v; change e with v) end.
  Ltac ntk := let K := fresh "K" in if_cases K; [exfalso; zify_cond K; Z.div_mod_to_equations; lia | clear K].
  Ltac tkn := let K := fresh "K" in if_cases K; [clear K | exfalso; zify_cond K; Z.div_mod_to_equations; lia].
  Ltac zxfix z :=
    match goal with |- context [Z_to_bv 64 (?X mod 4294967296)] =>
      replace (X mod 4294967296) with z by (Z.div_mod_to_equations; lia) end.

  Lemma epi : forall mm (w x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word)
      (r : Z),
    mem_inv rsegs mm -> rw_cells rsegs mm (bv_unsigned sp + -80) FRc -> stk rsegs mm lo (bv_unsigned sp + -80) ->
    munch WF m mm -> wmono rsegs m mm ->
    rw_cells rsegs mm (Fp + 8) [C8 (Z_to_bv 64 (P + r)); C8 (Z_to_bv 64 18446744073709551615)] ->
    rw_cells rsegs mm (Fp + 184) [C8 (Z_to_bv 64 18446744073709551615); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (s10_end str - r))] ->
    rw_cells rsegs mm (bv_unsigned tp + -164) [C4 (s10_errno str ev)] ->
    w = Z_to_bv 64 (s10_val str) ->
    evt rsegs POST (GS 0x1d214 mm x1 x5 x6 x7 w x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31).
  Proof using All.
    intros mm w x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 r
      MI FR ST MU WM RP SH ER ->.
    do 12 zstep.
    release_frame FR ST (bv_unsigned sp).
    zstep.
    finish.
    all: eassumption.
  Qed.

  Lemma done : forall i mm y (neg : bool) (x10 x11 x12 x18 x21 x22 x23 x24 : word),
    (i <= length str)%nat -> INV mm (S i) -> 0 <= y < 2^64 -> y = s10_mag str -> Z.of_nat i = s10_end str ->
    s10_neg str = neg -> s10_nd str <> O ->
    evt rsegs POST (LS 0x1d148 mm x10 x11 x12 x18 (Z_to_bv 64 y) (msk neg) x21 x22 x23 x24).
  Proof using All.
    intros i mm y neg x10 x11 x12 x18 x21 x22 x23 x24 HI H Hy HM HE HN HD. dinv H.
    assert (SG : s10_signed str = if neg then - y else y) by (unfold s10_signed; rewrite HN, HM; reflexivity).
    zstep. zstep. if_false.
    zstep. zstep. zstep.
    replace (P + Z.of_nat (S i) + -1) with (P + Z.of_nat i) in RP by lia.
    zstep. if_cases K; zify_cond K.
    - zstep. zstep. if_false.
      destruct neg; cbv beta iota.
      + zstep. if_true. zstep. if_cases K2; zify_cond K2.
        * zstep. zstep. zstep.
          eapply epi with (r := Z.of_nat i); try eassumption.
          -- rewrite <- HE, Z.sub_diag. exact SH.
          -- rewrite err_in; [exact ER | exact HD | lia].
          -- vfin SG.
        * zstep. errcall. zstep. zstep. zstep.
          eapply epi with (r := Z.of_nat i); try eassumption.
          -- rewrite <- HE, Z.sub_diag. exact SH.
          -- rewrite err_out; [exact ER | exact HD | lia].
          -- vfin SG.
      + zstep. if_false. zstep. errcall. zstep. zstep. zstep. zstep.
        eapply epi with (r := Z.of_nat i); try eassumption.
        * rewrite <- HE, Z.sub_diag. exact SH.
        * rewrite err_out; [exact ER | exact HD | lia].
        * vfin SG.
    - destruct neg; cbv beta iota; zstep; zstep; zstep;
        (eapply epi with (r := Z.of_nat i); try eassumption;
         [ rewrite <- HE, Z.sub_diag; exact SH
         | rewrite err_in; [exact ER | exact HD | lia]
         | vfin SG ]).
  Qed.

  Lemma ovf : forall n i mm (neg : bool) (x10 x11 x12 x19 x22 x23 x24 : word),
    (length str - i < n)%nat -> (i <= length str)%nat -> INV mm i -> 18446744073709551615 < s10_mag str ->
    Z.of_nat (i + ndig (skipn i str)) = s10_end str -> s10_neg str = neg -> s10_nd str <> O ->
    evt rsegs POST (LS 0x1d180 mm x10 x11 x12 (Z_to_bv 64 10) x19 (msk neg) (Z_to_bv 64 70384) x22 x23 x24).
  Proof using All.
    induction n as [|n IH]; intros i mm neg x10 x11 x12 x19 x22 x23 x24 HK HI H HM HE HN HD; [lia|].
    destruct (nth_txt str i HI) as [b Hb]. pose proof (byte_rng b) as Rb.
    rewrite (nstep str i b Hb HI) in HE.
    assert (SG : s10_signed str = if neg then - s10_mag str else s10_mag str)
      by (unfold s10_signed; rewrite HN; reflexivity).
    dinv H.
    zstep. zstep. zstep. ntk. zstep. zstep.
    rdr i b Hb. zstep. zstep. tblr b t HR HQ. zstep. zstep. if_cases K; zify_cond K.
    - apply HQ in K. rewrite K in HE. pose proof (digit_rng b K) as DG.
      pose proof (txt_nz_lt str i b Hb HI ltac:(lia)) as LT.
      replace (P + Z.of_nat i + 1) with (P + Z.of_nat (S i)) in RP by lia.
      apply (IH (S i)); [lia | lia | minv | exact HM | rewrite <- HE; f_equal; lia | exact HN | exact HD].
    - assert (CD : c_digit b = false) by (apply not_true_is_false; intro E; apply HQ in E; lia).
      rewrite CD, Nat.add_0_r in HE.
      destruct neg; cbv beta iota.
      + zstep. errcall. do 5 zstep. cfold. zstep. zstep. zstep. if_true. zstep. zstep. zstep.
        replace (P + Z.of_nat i + 1 + -1) with (P + Z.of_nat i) in RP by lia.
        zstep. if_true. zstep. zstep. if_false. zstep. if_true. zstep. if_true. zstep. zstep. zstep.
        eapply epi with (r := Z.of_nat i); try eassumption.
        * replace (s10_end str - Z.of_nat i) with 0 by lia. exact SH.
        * rewrite err_out; [exact ER | exact HD | lia].
        * vfin SG.
      + zstep. errcall. do 5 zstep. cfold. zstep. zstep. zstep. if_true. zstep. zstep. zstep.
        replace (P + Z.of_nat i + 1 + -1) with (P + Z.of_nat i) in RP by lia.
        zstep. if_true. zstep. zstep. if_false. zstep. if_false. zstep. errcall. do 4 zstep.
        eapply epi with (r := Z.of_nat i); try eassumption.
        * replace (s10_end str - Z.of_nat i) with 0 by lia. exact SH.
        * rewrite err_out; [exact ER | exact HD | lia].
        * vfin SG.
  Qed.

  Lemma lp2 : forall n i y d mm (neg : bool) (x10 x11 x12 x18 x19 : word),
    (length str - i < n)%nat -> (1 <= i <= length str)%nat -> INV mm i -> 0 <= y -> 0 <= d <= 9 ->
    y * 10 + d <= 18446744073709551615 ->
    dval (y * 10 + d) (skipn i str) = s10_mag str -> Z.of_nat (i + ndig (skipn i str)) = s10_end str ->
    s10_neg str = neg -> s10_nd str <> O ->
    evt rsegs POST (LS 0x1ce98 mm x10 x11 x12 x18 x19 (msk neg) (Z_to_bv 64 d) (Z_to_bv 64 1844674407370955162)
                       (Z_to_bv 64 9) (Z_to_bv 64 (y * 10))).
  Proof using All.
    induction n as [|n IH]; intros i y d mm neg x10 x11 x12 x18 x19 HK HI H Hy Hd HB HV HE HN HD; [lia|].
    destruct (nth_txt str i ltac:(lia)) as [b Hb]. pose proof (byte_rng b) as Rb.
    rewrite (dstep str i b _ Hb ltac:(lia)) in HV. rewrite (nstep str i b Hb ltac:(lia)) in HE.
    pose proof (dval_ge (skipn (S i) str) (10 * (y * 10 + d) + (bv_unsigned b - 48))) as GE.
    dinv H.
    zstep. zstep. zstep. ntk. zstep. zstep.
    rdr i b Hb. zstep. zstep. zstep. rewrite sw32 by lia.
    zstep. if_cases K; zify_cond K.
    - assert (DG : 48 <= bv_unsigned b <= 57) by (Z.div_mod_to_equations; lia).
      rewrite (digit_t b DG) in HV, HE.
      pose proof (txt_nz_lt str i b Hb ltac:(lia) ltac:(lia)) as LT.
      zstep. if_cases K2; zify_cond K2.
      + zstep. zstep. ntk. do 4 zstep. tblr b t HR HQ.
        assert (T10 : bv_unsigned t < 10) by (apply HQ, digit_t, DG).
        zstep. zstep. tkn.
        replace (P + Z.of_nat i + 1) with (P + Z.of_nat (S i)) in RP by lia.
        eapply ovf with (n := S (length str)) (i := S i); [lia | lia | minv | lia | rewrite <- HE; f_equal; lia | exact HN | exact HD].
      + zstep. zstep. zstep. zstep. if_cases K3; zify_cond K3; rewrite ?zb_lxor_ones in K3 by lia.
        * replace (P + Z.of_nat i + 1) with (P + Z.of_nat (S i)) in RP by lia.
          replace (10 * (y * 10 + d) + (bv_unsigned b - 48)) with ((y * 10 + d) * 10 + (bv_unsigned b + -48)) in HV by lia.
          apply (IH (S i) (y * 10 + d) (bv_unsigned b + -48));
            [lia | lia | minv | lia | lia | lia | exact HV | rewrite <- HE; f_equal; lia | exact HN | exact HD].
        * zstep. do 3 zstep. tblr b t HR HQ.
          assert (T10 : bv_unsigned t < 10) by (apply HQ, digit_t, DG).
          zstep. zstep. tkn.
          replace (P + Z.of_nat i + 1) with (P + Z.of_nat (S i)) in RP by lia.
          eapply ovf with (n := S (length str)) (i := S i); [lia | lia | minv | lia | rewrite <- HE; f_equal; lia | exact HN | exact HD].
    - assert (DG : ~ (48 <= bv_unsigned b <= 57)) by (Z.div_mod_to_equations; lia).
      rewrite (digit_f b DG) in HV, HE. rewrite Nat.add_0_r in HE.
      zstep. zstep. zstep. tkn.
      replace (P + Z.of_nat i + 1) with (P + Z.of_nat (S i)) in RP by lia.
      eapply done with (i := i); [lia | minv | lia | exact HV | exact HE | exact HN | exact HD].
  Qed.

  Lemma lp1 : forall n i x d mm (neg : bool) (x10 x11 x12 : word),
    (length str - i < n)%nat -> (1 <= i <= length str)%nat -> INV mm i -> 0 <= x < 429496729 -> 0 <= d <= 9 ->
    dval (x * 10 + d) (skipn i str) = s10_mag str -> Z.of_nat (i + ndig (skipn i str)) = s10_end str ->
    s10_neg str = neg -> s10_nd str <> O ->
    evt rsegs POST (LS 0x1ce50 mm x10 x11 x12 (Z_to_bv 64 9) (Z_to_bv 64 x) (msk neg) (Z_to_bv 64 d) (Z_to_bv 64 10)
                       (Z_to_bv 64 429496729) s8).
  Proof using All.
    induction n as [|n IH]; intros i x d mm neg x10 x11 x12 HK HI H Hx Hd HV HE HN HD; [lia|].
    destruct (nth_txt str i ltac:(lia)) as [b Hb]. pose proof (byte_rng b) as Rb.
    rewrite (dstep str i b _ Hb ltac:(lia)) in HV. rewrite (nstep str i b Hb ltac:(lia)) in HE.
    dinv H.
    zstep. zstep. zstep. ntk. zstep. zstep.
    rdr i b Hb. zstep. zstep. zstep. zstep.
    rewrite (sw32 (bv_unsigned b + -48)) by lia.
    replace (P + Z.of_nat i + 1) with (P + Z.of_nat (S i)) in RP by lia.
    destruct (Z.lt_ge_cases (x * 10 + d) (2^31)) as [Z1|Z1];
      [rewrite (sw32 (x * 10 + d)) by lia | rewrite (sw32_hi (x * 10 + d)) by lia];
      zstep; if_cases K; zify_cond K.
    - assert (DG : 48 <= bv_unsigned b <= 57) by (Z.div_mod_to_equations; lia).
      rewrite (digit_t b DG) in HV, HE.
      pose proof (txt_nz_lt str i b Hb ltac:(lia) ltac:(lia)) as LT.
      replace (10 * (x * 10 + d) + (bv_unsigned b - 48)) with ((x * 10 + d) * 10 + (bv_unsigned b + -48)) in HV by lia.
      zstep. if_cases K2; zify_cond K2.
      + zstep. zstep. zxfix (x * 10 + d). zstep. ntk. do 5 zstep.
        eapply lp2 with (n := S (length str)) (i := S i);
          [lia | lia | minv | lia | lia | lia | exact HV | rewrite <- HE; f_equal; lia | exact HN | exact HD].
      + apply (IH (S i) (x * 10 + d) (bv_unsigned b + -48));
          [lia | lia | minv | lia | lia | exact HV | rewrite <- HE; f_equal; lia | exact HN | exact HD].
    - assert (DG : ~ (48 <= bv_unsigned b <= 57)) by (Z.div_mod_to_equations; lia).
      rewrite (digit_f b DG) in HV, HE. rewrite Nat.add_0_r in HE.
      zstep. zstep. zxfix (x * 10 + d). zstep. tkn.
      eapply done with (i := i); [lia | minv | lia | exact HV | exact HE | exact HN | exact HD].
    - assert (DG : 48 <= bv_unsigned b <= 57) by (Z.div_mod_to_equations; lia).
      rewrite (digit_t b DG) in HV, HE.
      pose proof (txt_nz_lt str i b Hb ltac:(lia) ltac:(lia)) as LT.
      replace (10 * (x * 10 + d) + (bv_unsigned b - 48)) with ((x * 10 + d) * 10 + (bv_unsigned b + -48)) in HV by lia.
      zstep. tkn. zstep. zstep. zxfix (x * 10 + d). zstep. ntk. do 5 zstep.
      eapply lp2 with (n := S (length str)) (i := S i);
        [lia | lia | minv | lia | lia | lia | exact HV | rewrite <- HE; f_equal; lia | exact HN | exact HD].
    - assert (DG : ~ (48 <= bv_unsigned b <= 57)) by (Z.div_mod_to_equations; lia).
      rewrite (digit_f b DG) in HV, HE. rewrite Nat.add_0_r in HE.
      zstep. zstep. zxfix (x * 10 + d). zstep. tkn.
      eapply done with (i := i); [lia | minv | lia | exact HV | exact HE | exact HN | exact HD].
  Qed.

  Lemma fch : forall k c mm (neg : bool) (x11 x12 : word),
    nth_error (str ++ [Z_to_bv 8 0]) k = Some c -> (k <= length str)%nat -> INV mm (S k) ->
    s10_rest str = skipn k str -> s10_neg str = neg ->
    evt rsegs POST (LS 0x1cda4 mm (Z_to_bv 64 (bv_unsigned c)) x11 x12 (Z_to_bv 64 10) a2 (msk neg) (Z_to_bv 64 32) s6 s7 s8).
  Proof using All.
    intros k c mm neg x11 x12 Hc HK H HR0 HN. pose proof (byte_rng c) as Rc.
    pose proof (end_eq str k HR0 HK) as EE.
    assert (HM0 : s10_mag str = dval 0 (skipn k str)) by (unfold s10_mag; rewrite HR0; reflexivity).
    assert (HD0 : s10_nd str = ndig (skipn k str)) by (unfold s10_nd; rewrite HR0; reflexivity).
    rewrite (dstep str k c 0 Hc HK) in HM0. rewrite (nstep str k c Hc HK) in HD0.
    dinv H.
    zstep. if_true. zstep. zstep. zstep. tblr c t HR HQ. zstep. zstep. if_cases K; zify_cond K.
    - apply HQ in K. rewrite K in HM0, HD0. pose proof (digit_rng c K) as DG.
      pose proof (txt_nz_lt str k c Hc HK ltac:(lia)) as LT.
      zstep. zstep. if_false. zstep. rewrite (sw32 (bv_unsigned c + -48)) by lia.
      zstep. zstep. zstep. ntk. zstep. zstep. zstep. cfold. zstep.
      eapply lp1 with (n := S (length str)) (i := S k); [lia | lia | minv | lia | lia | | | exact HN | rewrite HD0; discriminate].
      + rewrite HM0; f_equal; lia.
      + rewrite EE, HD0; cbn [Nat.eqb]; f_equal; lia.
    - assert (CD : c_digit c = false) by (apply not_true_is_false; intro E; apply HQ in E; lia).
      rewrite CD in HM0, HD0.
      zstep. zstep. if_false. zstep. zstep. zstep.
      replace (P + Z.of_nat (S k) + -1) with (P + Z.of_nat k) in RP by lia.
      zstep. zstep. zstep.
      destruct (rw_cells_forget _ _ _ _ SH) as [jk SHj]. cbn [cells_size csize Nat.add] in SHj.
      call SHL; [exact RP | exact BF | exact SHj | exact MI | ].
      zstep. errcall. zstep. zstep. zstep. zstep.
      eapply epi with (r := Z.of_nat k); try eassumption.
      + rewrite EE, HD0. cbn [Nat.eqb].
        match goal with Hs : rw_cells _ _ (Fp + 184) _ |- _ =>
          rewrite !unsigned_lit in Hs by lia; replace (0 - Z.of_nat k) with (P - (P + Z.of_nat k)) by lia; exact Hs end.
      + rewrite err_nod by (rewrite HD0; reflexivity). eassumption.
      + f_equal. unfold s10_val, s10_signed, LMIN. rewrite HM0. destruct (s10_neg str); lia.
  Qed.

  Lemma sg : forall j b mm (x11 : word), nth_error (str ++ [Z_to_bv 8 0]) j = Some b -> (j <= length str)%nat ->
    (bv_unsigned b = 45 \/ bv_unsigned b = 43) -> INV mm (S j) -> skip_space str = skipn j str ->
    evt rsegs POST (LS 0x1cd0c mm (Z_to_bv 64 (bv_unsigned b)) x11 a2 (Z_to_bv 64 10) a2 (Z_to_bv 64 5) (Z_to_bv 64 32) s6 s7 s8).
  Proof using All.
    intros j b mm x11 Hb HJ HS0 H SK.
    pose proof (txt_nz_lt str j b Hb HJ ltac:(lia)) as LT.
    destruct (nth_txt str (S j) ltac:(lia)) as [b2 Hb2].
    assert (SS : sign_split (skip_space str) = (bv_unsigned b =? 45, skipn (S j) str))
      by (rewrite SK, (sg_split str j b Hb HJ); destruct HS0 as [E|E]; rewrite E; reflexivity).
    assert (HR0 : s10_rest str = skipn (S j) str) by (unfold s10_rest; rewrite SS; reflexivity).
    assert (HN0 : s10_neg str = (bv_unsigned b =? 45)) by (unfold s10_neg; rewrite SS; reflexivity).
    dinv H.
    destruct HS0 as [E|E]; rewrite E in HN0 |- *;
      zstep; zstep; zstep; zstep; zstep; cfold; zstep; ntk; zstep; zstep;
      rdr (S j) b2 Hb2; zstep; zstep; zstep; ntk; zstep;
      replace (P + Z.of_nat (S j) + 1) with (P + Z.of_nat (S (S j))) in RP by lia.
    - try replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by word_eq_tac.
      eapply fch with (k := S j) (neg := true); [exact Hb2 | lia | minv | exact HR0 | exact HN0].
    - eapply fch with (k := S j) (neg := false); [exact Hb2 | lia | minv | exact HR0 | exact HN0].
  Qed.

  Lemma ws : forall n j mm (x10 x11 : word), (length str - j < n)%nat -> (j <= length str)%nat -> INV mm j ->
    skip_space (skipn j str) = skip_space str ->
    evt rsegs POST (LS 0x1ccd8 mm x10 x11 a2 (Z_to_bv 64 10) a2 (Z_to_bv 64 5) (Z_to_bv 64 32) s6 s7 s8).
  Proof using All.
    induction n as [|n IH]; intros j mm x10 x11 HK HJ H SK; [lia|].
    destruct (nth_txt str j HJ) as [b Hb]. pose proof (byte_rng b) as Rb.
    dinv H.
    zstep. zstep. zstep. ntk. zstep. zstep. rdr j b Hb. zstep. zstep. zstep.
    replace (P + Z.of_nat j + 1) with (P + Z.of_nat (S j)) in RP by lia.
    if_cases K; zify_cond K.
    - assert (R9 : 9 <= bv_unsigned b <= 13) by (Z.div_mod_to_equations; lia).
      assert (SP : c_space b = true) by (apply space_t; lia).
      pose proof (txt_nz_lt str j b Hb HJ ltac:(lia)) as LT.
      apply (IH (S j)); [lia | lia | minv | rewrite <- (sp_step str j b Hb HJ SP); exact SK].
    - assert (R9 : ~ (9 <= bv_unsigned b <= 13)) by (Z.div_mod_to_equations; lia).
      zstep. if_cases K2; zify_cond K2.
      + assert (SP : c_space b = true) by (apply space_t; lia).
        pose proof (txt_nz_lt str j b Hb HJ ltac:(lia)) as LT.
        apply (IH (S j)); [lia | lia | minv | rewrite <- (sp_step str j b Hb HJ SP); exact SK].
      + assert (SP : c_space b = false) by (apply space_f; lia).
        assert (SKJ : skip_space str = skipn j str) by (rewrite <- SK; exact (sp_stop str j b Hb HJ SP)).
        zstep. zstep. if_cases K3; zify_cond K3.
        * eapply sg with (j := j); [exact Hb | exact HJ | lia | minv | exact SKJ].
        * zstep. zstep. if_cases K4; zify_cond K4.
          -- assert (SS : sign_split (skip_space str) = (false, skipn j str))
               by (rewrite SKJ, (sg_split str j b Hb HJ); rewrite (proj2 (Z.eqb_neq _ 45)) by lia;
                   rewrite (proj2 (Z.eqb_neq _ 43)) by lia; reflexivity).
             zstep. zstep. zstep. ntk. zstep.
             eapply fch with (k := j) (neg := false);
               [exact Hb | exact HJ | minv | unfold s10_rest; rewrite SS; reflexivity | unfold s10_neg; rewrite SS; reflexivity].
          -- eapply sg with (j := j); [exact Hb | exact HJ | lia | minv | exact SKJ].
  Qed.

  Lemma main :
    rw_cells rsegs m (Fp + 8) [C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 18446744073709551615)] ->
    rw_cells rsegs m (Fp + 88) [C8 (Z_to_bv 64 P)] ->
    rw_cells rsegs m (Fp + 184) [C8 (Z_to_bv 64 18446744073709551615); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
    bytes_at rsegs m P (str ++ [Z_to_bv 8 0]) -> rw_cells rsegs m (bv_unsigned tp + -164) [C4 ev] ->
    stk rsegs m lo (bv_unsigned sp) -> mem_inv rsegs m ->
    evt rsegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 10) a2 LM a4 a5 a6 a7
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x1cc70) fc None m (seg_rom rsegs)).
  Proof using All.
    intros RP BF SH BY ER ST MI.
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (Fp + 8, Fp + 16); (Fp + 184, Fp + 208);
                (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    zstep. carve_frame 80%nat ST. do 10 zstep.
    zstep. zstep. zstep. if_false. zstep. zstep. zstep. if_false. do 5 zstep.
    replace (Z_to_bv 64 P) with (Z_to_bv 64 (P + Z.of_nat 0)) in RP by (f_equal; lia).
    eapply ws with (n := S (length str)) (j := 0%nat); [lia | lia | minv | reflexivity].
  Qed.
End IS.

Theorem __intscan_holds : __errno_location_contract -> __shlim_contract -> __intscan_contract.
Proof.
  intros ERR SHL. unfold __intscan_contract, INTSCAN, LMIN, M64.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Fp P str ev lo
    RP BF SH BY HP ER ST HLO D1 D2 D3 D4 D5 MI.
  pose proof (rw_cells_bound _ _ _ _ RP) as B1. pose proof (rw_cells_bound _ _ _ _ SH) as B2.
  pose proof (rw_cells_bound _ _ _ _ ER) as B3. cbn [cells_size csize Nat.add] in B1, B2, B3.
  pose proof (bytes_at_bound _ _ _ _ BY) as B4. rewrite length_app in B4. cbn [length] in B4.
  pose proof (bv_unsigned_in_range 64 sp) as RS. unfold bv_modulus in RS. cbn in RS.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  eapply main; try eassumption; lia.
Qed.
