(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BakeStackRep BecLazy2.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_Conv LbB_DiagStmt LbB_DStat.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition VT_OS_A : Z := 0x182aa8.
Definition VT_IOS_A : Z := 0x182ad0.
Definition VT_SB_A : Z := 0x182918.
Definition LOC_IMP_A : Z := 0x6c4698.

Lemma u_small : forall z, (0 <= z < 2^64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  change (bv_modulus 64) with (2^64)%Z. lia.
Qed.

Section Rep.
  #[local] Notation fld := (CRep.fld ASEGS).
  #[local] Notation str_repA := (@str_rep AC_A ASEGS LY_A MI_A).

  Record sb_inv (A : list (Z * Z)) (M : mem) (sb : Z) (m : sbuf) (pp hm : Z) : Prop := SB_INV {
    si_vt    : fld M sb 8 VT_SB_A;
    si_loc   : fld M (sb + 8) 8 LOC_IMP_A;
    si_binp  : fld M (sb + 16) 8 0;
    si_ninp  : fld M (sb + 24) 8 0;
    si_einp  : fld M (sb + 32) 8 0;
    si_str   : exists cs, str_repA A M (sb + 64) m cs /\ Zlen cs = str_cap m;
    si_pbase : fld M (sb + 40) 8 (str_data (sb + 64) m);
    si_pptr  : fld M (sb + 48) 8 pp;
    si_epptr : fld M (sb + 56) 8 (str_data (sb + 64) m + str_cap m);
    si_pp    : str_data (sb + 64) m <= pp <= str_data (sb + 64) m + str_cap m;
    si_hm    : fld M (sb + 88) 8 hm;
    si_hmr   : str_data (sb + 64) m <= hm <= str_data (sb + 64) m + str_cap m;
    si_mode  : fld M (sb + 96) 4 16
  }.

  Definition ios_zero (M : mem) (io : Z) : Prop :=
    forall i, 0 <= i < 10 -> fld M (io + 56 + 8 * i) 8 0.

  Record ios_inv (M : mem) (io sb : Z) (fl fill : Z) : Prop := IOS_INV {
    ii_vt    : fld M io 8 VT_IOS_A;
    ii_flags : fld M (io + 8) 4 fl;
    ii_fl    : fl = DS_FL0 \/ fl = DS_FLHEX;
    ii_prec  : fld M (io + 16) 8 6;
    ii_width : fld M (io + 24) 8 0;
    ii_state : fld M (io + 32) 4 0;
    ii_exc   : fld M (io + 36) 4 0;
    ii_rdbuf : fld M (io + 40) 8 sb;
    ii_loc   : fld M (io + 48) 8 LOC_IMP_A;
    ii_zero  : ios_zero M io;
    ii_tie   : fld M (io + 136) 8 0;
    ii_fill  : fld M (io + 144) 4 fill;
    ii_fillr : fill = 2 ^ 32 - 1 \/ fill = 32
  }.

  Record ds_inv (A : list (Z * Z)) (M : mem) (ds err len : Z) (B : list (Z * Z))
                (m : sbuf) (pp hm fl fill : Z) : Prop := DS_INV {
    di_pos   : 0 < ds;
    di_al    : ds mod 8 = 0;
    di_hi    : ds + 392 <= 2 ^ 47;
    di_def   : mdef M ds 392;
    di_vt    : fld M ds 8 VT_OS_A;
    di_sb    : sb_inv A M (ds + 8) m pp hm;
    di_B     : B = str_blocks m;
    di_mx    : forall d asz, m = SLong d asz -> asz <= DS_MAXBLK;
    di_pow   : forall d asz, m = SLong d asz -> exists j, 0 <= j /\ asz = 48 * 2 ^ j;
    di_len0  : 0 <= len;
    di_pl    : pp - str_data (ds + 72) m <= len;
    di_asz   : forall d asz, m = SLong d asz -> asz <= 2 * len + 48;
    di_dj    : forall d asz, m = SLong d asz -> ds + 392 <= d \/ d + asz <= ds;
    di_ios   : ios_inv M (ds + 112) (ds + 8) fl fill;
    di_f320  : fld M (ds + 320) 8 0;
    di_f336  : fld M (ds + 336) 1 0;
    di_f360  : fld M (ds + 360) 4 (err mod 2 ^ 32);
    di_f368  : fld M (ds + 368) 1 0;
    di_err   : - 2 ^ 31 <= err < 0
  }.

  Lemma fld_ag : forall M M' (P : Z -> Prop) a (k : nat) v,
    0 <= a -> a + Z.of_nat k < 2 ^ 64 -> (forall x, a <= x < a + Z.of_nat k -> P x) ->
    agree_on P M M' -> fld M a k v -> fld M' a k v.
  Proof.
    intros M M' P a k v Ha Hk HP HA HF. eapply fld_agree; [lia | lia | exact HF |].
    eapply agree_on_weaken; [exact HA|]. intros x Hx. apply HP. unfold zwin in Hx. lia.
  Qed.

  Definition sb_fp (sb : Z) (m : sbuf) (a : Z) : Prop :=
    zwin sb (sb + 104) a \/ match m with SShort => False | SLong d asz => zwin d (d + asz) a end.

  Lemma sb_inv_frame : forall A A' M M' sb m pp hm,
    sb_inv A M sb m pp hm -> 0 <= sb -> sb + 104 <= 2 ^ 47 ->
    agree_on (sb_fp sb m) M M' ->
    (forall blk, In blk (str_blocks m) -> In blk A') ->
    sb_inv A' M' sb m pp hm.
  Proof.
    intros A A' M M' sb m pp hm SB Hsb0 Hsb1 HA HL. destruct SB.
    assert (FO : forall a (k : nat) v, sb <= a -> a + Z.of_nat k <= sb + 104 -> fld M a k v -> fld M' a k v).
    { intros a k v Ho Hk HF. eapply (fld_ag M M' (sb_fp sb m)); [lia | lia | | exact HA | exact HF].
      intros x Hx. left. unfold zwin. lia. }
    constructor; try assumption.
    - apply FO; [lia | cbn; lia | assumption].
    - apply FO; [lia | cbn; lia | assumption].
    - apply FO; [lia | cbn; lia | assumption].
    - apply FO; [lia | cbn; lia | assumption].
    - apply FO; [lia | cbn; lia | assumption].
    - destruct si_str0 as (cs & SR & HL2). exists cs. split; [|exact HL2].
      eapply str_relive; [eapply str_frame; [exact SR|]|].
      + eapply agree_on_weaken; [exact HA|]. intros a Ha. unfold str_fp in Ha.
        destruct Ha as [Ha|Ha]; [left; unfold zwin in *; lia|].
        destruct m as [|d asz]; [destruct Ha|]. right.
        destruct SR as (_ & _ & _ & Hlen & (Hd & _ & _ & _ & Hsz & _) & _). cbn [str_cap] in Hlen. unfold zwin in *. lia.
      + intros blk Hb _. apply HL. exact Hb.
    - apply FO; [lia | cbn; lia | assumption].
    - apply FO; [lia | cbn; lia | assumption].
    - apply FO; [lia | cbn; lia | assumption].
    - apply FO; [lia | cbn; lia | assumption].
    - apply FO; [lia | cbn; lia | assumption].
  Qed.

  Lemma ios_inv_frame : forall M M' io sb fl fill,
    ios_inv M io sb fl fill -> 0 <= io -> io + 152 <= 2 ^ 47 ->
    agree_on (zwin io (io + 152)) M M' -> ios_inv M' io sb fl fill.
  Proof.
    intros M M' io sb fl fill II Hio0 Hio1 HA. destruct II.
    assert (FO : forall a (k : nat) v, io <= a -> a + Z.of_nat k <= io + 152 -> fld M a k v -> fld M' a k v).
    { intros a k v Ho Hk HF. eapply (fld_ag M M' (zwin io (io + 152))); [lia | lia | | exact HA | exact HF].
      intros x Hx. unfold zwin. lia. }
    constructor; try assumption.
    - apply FO; [lia | cbn; lia | assumption].
    - apply FO; [lia | cbn; lia | assumption].
    - apply FO; [lia | cbn; lia | assumption].
    - apply FO; [lia | cbn; lia | assumption].
    - apply FO; [lia | cbn; lia | assumption].
    - apply FO; [lia | cbn; lia | assumption].
    - apply FO; [lia | cbn; lia | assumption].
    - apply FO; [lia | cbn; lia | assumption].
    - intros i Hi. apply FO; [lia | cbn; lia |]. apply ii_zero0. exact Hi.
    - apply FO; [lia | cbn; lia | assumption].
    - apply FO; [lia | cbn; lia | assumption].
  Qed.

  Definition ds_foot (ds : Z) (B : list (Z * Z)) (a : Z) : Prop :=
    zwin ds (ds + DS_SIZE) a \/ exists q k, In (q, k) B /\ q <= a < q + k.

  Lemma ds_inv_frame : forall A A' M M' ds err len B m pp hm fl fill,
    ds_inv A M ds err len B m pp hm fl fill ->
    agree_on (ds_foot ds B) M M' ->
    (forall blk, In blk B -> In blk A') ->
    ds_inv A' M' ds err len B m pp hm fl fill.
  Proof.
    intros A A' M M' ds err len B m pp hm fl fill DI HA HL. unfold ds_foot, DS_SIZE in HA. destruct DI.
    assert (HAo : agree_on (zwin ds (ds + 392)) M M') by (eapply agree_on_weaken; [exact HA|]; intros a Ha; left; exact Ha).
    assert (FO : forall a (k : nat) v, ds <= a -> a + Z.of_nat k <= ds + 392 -> fld M a k v -> fld M' a k v).
    { intros a k v Ho Hk HF. eapply (fld_ag M M' (zwin ds (ds + 392))); [lia | lia | | exact HAo | exact HF].
      intros x Hx. unfold zwin. lia. }
    constructor; try assumption.
    - eapply mdef_agree; [exact di_def0 | exact HAo].
    - apply FO; [lia | cbn; lia | assumption].
    - eapply sb_inv_frame; [exact di_sb0 | lia | lia | | subst B; exact HL].
      eapply agree_on_weaken; [exact HA|]. intros a [Ha|Ha]; [left; unfold zwin in *; lia|].
      destruct m as [|d asz]; [destruct Ha|]. right. exists d, asz. subst B. split; [left; reflexivity | unfold zwin in Ha; lia].
    - eapply ios_inv_frame; [exact di_ios0 | lia | lia |].
      eapply agree_on_weaken; [exact HAo|]. intros a Ha. unfold zwin in *. lia.
    - apply FO; [lia | cbn; lia | assumption].
    - apply FO; [lia | cbn; lia | assumption].
    - apply FO; [lia | cbn; lia | assumption].
    - apply FO; [lia | cbn; lia | assumption].
  Qed.

  Lemma ds_inv_resb : forall A A' M M' ds err len len' B m pp hm fl fill m' pp' hm' fl' fill',
    ds_inv A M ds err len B m pp hm fl fill ->
    sb_inv A' M' (ds + 8) m' pp' hm' ->
    ios_inv M' (ds + 112) (ds + 8) fl' fill' ->
    mdef M' ds 392 ->
    agree_on (fun a => zwin ds (ds + 8) a \/ zwin (ds + 264) (ds + 392) a) M M' ->
    len <= len' -> pp' - str_data (ds + 72) m' <= len' ->
    (forall d asz, m' = SLong d asz -> asz <= 2 * len' + 48 /\ asz <= DS_MAXBLK /\ (exists j, 0 <= j /\ asz = 48 * 2 ^ j)
                                     /\ (ds + 392 <= d \/ d + asz <= ds)) ->
    ds_inv A' M' ds err len' (str_blocks m') m' pp' hm' fl' fill'.
  Proof.
    intros A A' M M' ds err len len' B m pp hm fl fill m' pp' hm' fl' fill' DI SB' II' HD' HA Hlen Hpl Hm'. destruct DI.
    assert (FO : forall a (k : nat) v, (ds <= a /\ a + Z.of_nat k <= ds + 8) \/ (ds + 264 <= a /\ a + Z.of_nat k <= ds + 392) ->
                 fld M a k v -> fld M' a k v).
    { intros a k v Ho HF. eapply (fld_ag M M' (fun a => zwin ds (ds + 8) a \/ zwin (ds + 264) (ds + 392) a)); [lia | lia | | exact HA | exact HF].
      intros x Hx. unfold zwin. lia. }
    constructor; try assumption; try reflexivity; try lia.
    - apply FO; [cbn; lia | assumption].
    - intros d asz E. exact (proj1 (proj2 (Hm' d asz E))).
    - intros d asz E. exact (proj1 (proj2 (proj2 (Hm' d asz E)))).
    - intros d asz E. exact (proj1 (Hm' d asz E)).
    - intros d asz E. exact (proj2 (proj2 (proj2 (Hm' d asz E)))).
    - apply FO; [cbn; lia | assumption].
    - apply FO; [cbn; lia | assumption].
    - apply FO; [cbn; lia | assumption].
    - apply FO; [cbn; lia | assumption].
  Qed.

  Lemma ds_inv_mono : forall A M ds err len len' B m pp hm fl fill,
    ds_inv A M ds err len B m pp hm fl fill -> len <= len' -> ds_inv A M ds err len' B m pp hm fl fill.
  Proof.
    intros A M ds err len len' B m pp hm fl fill DI Hle. destruct DI.
    constructor; try assumption; try lia. intros d asz Hm. specialize (di_asz0 d asz Hm). lia.
  Qed.

  Lemma ds_inv_setfl : forall A M M' ds err len B m pp hm fl fill fl',
    ds_inv A M ds err len B m pp hm fl fill -> fl' = DS_FL0 \/ fl' = DS_FLHEX ->
    fld M' (ds + 120) 4 fl' -> mdef M' ds 392 ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ (ds + 120 <= a < ds + 124) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
    ds_inv A M' ds err len B m pp hm fl' fill.
  Proof.
    intros A M M' ds err len B m pp hm fl fill fl' DI Hfl' HF' HD' OUT.
    pose proof (di_pos _ _ _ _ _ _ _ _ _ _ _ DI) as G1. pose proof (di_hi _ _ _ _ _ _ _ _ _ _ _ DI) as G3.
    assert (AG : forall P : Z -> Prop, (forall a, P a -> 0 <= a < 2 ^ 64 /\ ~ (ds + 120 <= a < ds + 124)) -> agree_on P M M').
    { intros P HP a Ha. apply OUT; apply (HP a Ha). }
    destruct DI.
    assert (FO : forall a (k : nat) v, ds <= a -> (a + Z.of_nat k <= ds + 120 \/ ds + 124 <= a) -> a + Z.of_nat k <= ds + 392 ->
                 fld M a k v -> fld M' a k v).
    { intros a k v Ho Hd Hk HF. eapply (fld_ag M M' (fun x => a <= x < a + Z.of_nat k)); [lia | lia | intros x Hx; exact Hx | | exact HF].
      apply AG. intros x Hx. lia. }
    constructor; try assumption.
    - apply FO; [lia | cbn; lia | cbn; lia | assumption].
    - assert (SBD : forall d asz, m = SLong d asz -> 0 < d /\ d + asz <= 2 ^ 63).
      { intros d asz E. subst m. destruct (si_str _ _ _ _ _ _ di_sb0) as (cs & SR & _).
        destruct SR as (_ & _ & _ & _ & (Hd & _ & Hde & _) & _). lia. }
      eapply sb_inv_frame; [exact di_sb0 | lia | lia | |
        intros blk Hb; destruct (si_str _ _ _ _ _ _ di_sb0) as (cs & SR & _);
        exact (@str_blocks_live AC_A ASEGS LY_A MI_A _ _ _ _ _ SR blk Hb)].
      apply AG. intros a Ha. unfold sb_fp, zwin in Ha. destruct Ha as [Ha|Ha]; [lia|].
      destruct m as [|d asz]; [destruct Ha|]. specialize (di_dj0 d asz eq_refl). specialize (SBD d asz eq_refl). lia.
    - destruct di_ios0. constructor; try assumption; try (apply FO; [lia | cbn; lia | cbn; lia | assumption]).
      + replace (ds + 112 + 8) with (ds + 120) by lia. exact HF'.
      + intros i Hi. apply FO; [lia | cbn; lia | cbn; lia |]. apply ii_zero0. exact Hi.
    - apply FO; [lia | cbn; lia | cbn; lia | assumption].
    - apply FO; [lia | cbn; lia | cbn; lia | assumption].
    - apply FO; [lia | cbn; lia | cbn; lia | assumption].
    - apply FO; [lia | cbn; lia | cbn; lia | assumption].
  Qed.
End Rep.

Definition ds_blk (LB : list block) (B : list block) (m : sbuf) : Prop :=
  match m with
  | SShort => B = []
  | SLong d asz => exists p, B = [(p, d, asz)] /\ In (p, d, asz) LB
  end.

Definition sb_addr (M : mem) (m : sbuf) : Prop :=
  match m with SShort => True | SLong d asz => addressable M d asz /\ app_obj d asz end.

Definition ds_repA0 (LB : list block) (M : mem) (ds err len : Z) (B : list block) : Prop :=
  exists m pp hm fl fill,
    ds_inv (lbl LB) M ds err len (lbl B) m pp hm fl fill
    /\ ds_blk LB B m
    /\ addressable M ds DS_SIZE /\ wr_at asegs M ds DS_SIZE /\ app_obj ds DS_SIZE
    /\ sb_addr M m.

Lemma app_obj_sh_apart : forall A n a j, app_obj A n -> 0 <= a -> a + j <= AAPP_HI -> 0 <= j ->
  sh a + nsh j <= A \/ A + n <= sh a.
Proof.
  intros A n a j (H1 & H2 & H3) Ha Hj Hj0. unfold nsh, sh, AIMG_TOP, ALOWSH_LO, AHI_LO, AAPP_HI, ASHADOW_BASE in *.
  Z.div_mod_to_equations. lia.
Qed.

Lemma ds_blk_lbl : forall LB B m, ds_blk LB B m -> lbl B = str_blocks m.
Proof. intros LB B [|d asz] H; cbn [ds_blk] in H; [subst B; reflexivity|]. destruct H as (p & -> & _). reflexivity. Qed.

Lemma ds_blk_live : forall LB LB' B m, ds_blk LB B m -> (forall b, In b B -> In b LB') -> ds_blk LB' B m.
Proof.
  intros LB LB' B [|d asz] H HL; cbn [ds_blk] in *; [exact H|]. destruct H as (p & -> & HI).
  exists p. split; [reflexivity|]. apply HL. left. reflexivity.
Qed.

Lemma rw_cells_of_fld4 : forall M a v, CRep.fld ASEGS M a 4 v -> wr_at asegs M a 4 -> rw_cells asegs M a [C4 (Z_to_bv 64 v)].
Proof.
  intros M a v HF HW. pose proof HW as (HW0 & HW1 & _). split; [|exact HW].
  split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
  apply bytes_at_of_rdn; [lia | rewrite length_le4; lia | rewrite length_le4; exact HF].
Qed.

Lemma mdef_of_wr_at_hi : forall M a n, wr_at asegs M a n -> AIMG_TOP <= a -> mdef M a n.
Proof.
  intros M a n (H0 & H1 & H) Ha i Hi E. apply (H i Hi).
  rewrite BakeStackRep.wview_high; [exact E|]. unfold wa. rewrite u_small by (unfold AIMG_TOP in Ha; lia). lia.
Qed.

Lemma bytes_at_pteq : forall m m' a bs, bytes_at asegs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> m' (wa x) = m (wa x)) -> bytes_at asegs m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H) HE. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  rewrite <- (H i Hi). unfold mrd. rewrite (HE (a + Z.of_nat i)) by lia. reflexivity.
Qed.

Lemma wr_at_pteq : forall m m' a n, wr_at asegs m a n ->
  (forall x, a <= x < a + n -> m' (wa x) = m (wa x)) -> wr_at asegs m' a n.
Proof.
  intros m m' a n (H0 & H1 & H) HE. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  rewrite (BecLazy2.wview_pointwise m m' (wa (a + i))) by (apply HE; lia). exact (H i Hi).
Qed.

Lemma u8arr_pteq : forall m m' a bs, u8arr asegs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> m' (wa x) = m (wa x)) -> u8arr asegs m' a bs.
Proof. intros m m' a bs [HB HW] HE. split; [eapply bytes_at_pteq; eassumption | eapply wr_at_pteq; eassumption]. Qed.

Lemma addressable_pteq : forall m m' A n, addressable m A n ->
  (forall x, sh A <= x < sh A + nsh n -> m' (wa x) = m (wa x)) -> addressable m' A n.
Proof.
  intros m m' A n [Hn (HA0 & HA8 & U)] HE. split; [exact Hn|]. split; [exact HA0|]. split; [exact HA8|].
  eapply u8arr_pteq; [exact U|]. rewrite shadow_of_length by lia. exact HE.
Qed.

Lemma wr_at_sub : forall m a n a' n', wr_at asegs m a n -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> wr_at asegs m a' n'.
Proof.
  intros m a n a' n' (H0 & H1 & H) Ha Hb Hn. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply H. lia.
Qed.

Lemma rw_cells_of_fld8 : forall M a v, CRep.fld ASEGS M a 8 v -> wr_at asegs M a 8 -> rw_cells asegs M a [C8 (Z_to_bv 64 v)].
Proof.
  intros M a v HF HW. pose proof HW as (HW0 & HW1 & _). split; [|exact HW].
  split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
  apply bytes_at_of_rdn; [lia | rewrite length_le8; lia | rewrite length_le8; exact HF].
Qed.

Section Laws.
  Context {HCEIL : HeapCeil}.

  Lemma dsa_blocks : forall LB m ds err len B, ds_repA0 LB m ds err len B ->
    (length B <= 1)%nat /\ (forall b, In b B -> In b LB /\ 0 < blk_size b <= DS_MAXBLK).
  Proof.
    intros LB m ds err len B (sm & pp & hm & fl & fill & DI & BL & AD & WR & AO & SA).
    destruct sm as [|d asz]; cbn [ds_blk] in BL.
    - subst B. split; [cbn; lia | intros b []].
    - destruct BL as (p & -> & HIn). split; [cbn; lia|]. intros b [<-|[]].
      split; [exact HIn|]. unfold blk_size; cbn [snd].
      pose proof (di_mx _ _ _ _ _ _ _ _ _ _ _ DI d asz eq_refl) as MX.
      destruct (si_str _ _ _ _ _ _ (di_sb _ _ _ _ _ _ _ _ _ _ _ DI)) as (cs & SR & _).
      destruct SR as (_ & _ & _ & _ & (Hd & _ & _ & _ & Hsz & _) & _). unfold SSO_CAP in Hsz. lia.
  Qed.

  Lemma dsa_err : forall LB m ds err len B, ds_repA0 LB m ds err len B ->
    rw_cells asegs m (ds + DS_ERR_OFF) [C4 (Z_to_bv 64 (err mod 2 ^ 32))].
  Proof.
    intros LB m ds err len B (sm & pp & hm & fl & fill & DI & BL & AD & WR & AO & SA).
    apply rw_cells_of_fld4; [exact (di_f360 _ _ _ _ _ _ _ _ _ _ _ DI)|].
    eapply wr_at_sub; [exact WR | unfold DS_ERR_OFF; lia | unfold DS_ERR_OFF, DS_SIZE; lia | lia].
  Qed.

  Lemma dsa_def : forall LB m ds err len B, ds_repA0 LB m ds err len B ->
    addressable m ds DS_SIZE /\ 0 < ds /\ ds mod 8 = 0 /\ ds + DS_SIZE <= 2 ^ 47 /\ 0 <= len.
  Proof.
    intros LB m ds err len B (sm & pp & hm & fl & fill & DI & BL & AD & WR & AO & SA). destruct DI.
    split; [exact AD|]. unfold DS_SIZE. lia.
  Qed.

  Lemma dsa_mono : forall LB m ds err len len' B, ds_repA0 LB m ds err len B -> len <= len' -> ds_repA0 LB m ds err len' B.
  Proof.
    intros LB m ds err len len' B (sm & pp & hm & fl & fill & DI & BL & AD & WR & AO & SA) Hle.
    exists sm, pp, hm, fl, fill. split; [eapply ds_inv_mono; eassumption|]. tauto.
  Qed.

  Lemma dsa_frame : forall LB LB' m m' ds err len B, ds_repA0 LB m ds err len B ->
    (forall a, 0 <= a < 2 ^ 64 ->
       (ds <= a < ds + DS_SIZE \/ in_block B a \/ in_block_sh B a \/ (sh ds <= a < sh ds + nsh DS_SIZE)) ->
       m' (wa a) = m (wa a)) ->
    (forall b, In b B -> In b LB') -> ds_repA0 LB' m' ds err len B.
  Proof.
    intros LB LB' m m' ds err len B (sm & pp & hm & fl & fill & DI & BL & AD & WR & AO & SA) HE HL.
    pose proof (di_pos _ _ _ _ _ _ _ _ _ _ _ DI) as P0. pose proof (di_hi _ _ _ _ _ _ _ _ _ _ _ DI) as P1.
    assert (SB : forall d asz, sm = SLong d asz -> 0 < d /\ d + asz <= 2 ^ 63 /\ In (d, asz) (lbl B)).
    { intros d asz E. subst sm. destruct (si_str _ _ _ _ _ _ (di_sb _ _ _ _ _ _ _ _ _ _ _ DI)) as (cs & SR & _).
      destruct SR as (_ & _ & _ & _ & (Hd & _ & Hde & _) & _). split; [lia|]. split; [lia|].
      rewrite (ds_blk_lbl _ _ _ BL). left. reflexivity. }
    exists sm, pp, hm, fl, fill. split; [|split; [eapply ds_blk_live; eassumption|]].
    - eapply ds_inv_frame; [exact DI | |].
      + intros a [Ha|(q & k & Hin & Hq)].
        * unfold zwin, DS_SIZE in Ha. apply HE; [lia | left; unfold DS_SIZE; lia].
        * destruct (lbl_in_inv _ _ _ Hin) as (p & HinB). pose proof (di_B _ _ _ _ _ _ _ _ _ _ _ DI) as HB.
          assert (Hk : 0 < q /\ q + k <= 2 ^ 63).
          { destruct sm as [|d asz]; cbn [str_blocks] in HB; rewrite HB in Hin; [destruct Hin|].
            destruct Hin as [E|[]]. injection E as <- <-. destruct (SB d asz eq_refl) as (S0 & S1 & _). lia. }
          apply HE; [lia|]. right. left. exists (p, q, k). split; [exact HinB|]. unfold blk_addr, blk_size; cbn. lia.
      + intros blk Hb. destruct blk as [q k]. destruct (lbl_in_inv _ _ _ Hb) as (p & HinB).
        apply lbl_in with p. apply HL. exact HinB.
    - split; [|split; [|split]].
      + eapply addressable_pteq; [exact AD|]. intros x Hx. apply HE; [|right; right; right; exact Hx].
        pose proof (SHAD_bound _ _ _ (proj2 AD)) as SB'. rewrite shadow_of_length in SB' by (unfold DS_SIZE; lia). lia.
      + eapply wr_at_pteq; [exact WR|]. intros x Hx. apply HE; [unfold DS_SIZE in *; lia | left; exact Hx].
      + exact AO.
      + destruct sm as [|d asz]; cbn [sb_addr] in *; [exact I|].
        destruct BL as (p & -> & HinLB). destruct SA as [SA SAo]. split; [|exact SAo].
        eapply addressable_pteq; [exact SA|]. intros x Hx. apply HE.
        * pose proof (SHAD_bound _ _ _ (proj2 SA)) as SB'. rewrite shadow_of_length in SB' by (destruct SA; lia). lia.
        * right. right. left. exists (p, d, asz). split; [left; reflexivity|]. unfold blk_addr, blk_size; cbn. exact Hx.
  Qed.
End Laws.

Lemma vt_os_acc : forall m, ACONST m -> accessible m (VT_OS_A - 24) 8.
Proof.
  intros m AC. pose proof (ACONST_vt m AC) as [[_ (B0 & B1 & BB)] _].
  split; [unfold VT_OS_A; lia|]. split; [unfold VT_OS_A, AAPP_HI; lia|].
  intros x Hx. exists 0. split; [lia|]. split; [| left; reflexivity].
  assert (Esh : sh x = ASHW_VT + Z.of_nat 122).
  { unfold sh, ASHW_VT, ASHADOW_BASE, VT_OS_A in *. clear - Hx. Z.div_mod_to_equations. lia. }
  rewrite Esh. rewrite (BB 122%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)). vm_compute. reflexivity.
Qed.

Lemma vboff_relro : forall m, relro0 m -> ro_cells asegs m (VT_OS_A - 24) [C8 (Z_to_bv 64 DS_VBOFF)].
Proof.
  intros m HR. split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
  apply bytes_at_relro; [exact HR | unfold VT_OS_A; lia | rewrite length_le8; unfold VT_OS_A; lia |].
  vm_compute. reflexivity.
Qed.

Lemma wr_at_patch : forall m m' a n b k, wr_at asegs m a n -> wr_at asegs m' b k ->
  (forall x, a <= x < a + n -> ~ (b <= x < b + k) -> m' (wa x) = m (wa x)) -> wr_at asegs m' a n.
Proof.
  intros m m' a n b k (H0 & H1 & H) (K0 & K1 & K) HE. split; [lia|]. split; [lia|]. intros i Hi.
  destruct (Z_lt_le_dec (a + i) b) as [C|C]; [| destruct (Z_lt_le_dec (a + i) (b + k)) as [D|D]].
  - rewrite (BecLazy2.wview_pointwise m m' (wa (a + i))) by (apply HE; lia). exact (H i Hi).
  - replace (a + i) with (b + (a + i - b)) by lia. apply K. lia.
  - rewrite (BecLazy2.wview_pointwise m m' (wa (a + i))) by (apply HE; lia). exact (H i Hi).
Qed.

Section Hex.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_P : forall m, LINV m -> LINV_P5 m.

  Lemma dsa_hex : forall LB m ds err len B, LINV m -> ACONST m -> ds_repA0 LB m ds err len B ->
    exists vt fl, rw_cells asegs m ds [C8 (Z_to_bv 64 vt)] /\ ro_cells asegs m (vt - 24) [C8 (Z_to_bv 64 DS_VBOFF)]
                 /\ accessible m (vt - 24) 8
                 /\ (fl = DS_FL0 \/ fl = DS_FLHEX)
                 /\ rw_cells asegs m (ds + DS_VBOFF + 8) [C4 (Z_to_bv 64 fl)] /\
      forall m', (forall a, 0 <= a < 2 ^ 64 -> ~ (ds + DS_VBOFF + 8 <= a < ds + DS_VBOFF + 12) -> m' (wa a) = m (wa a)) ->
                 rw_cells asegs m' (ds + DS_VBOFF + 8) [C4 (Z_to_bv 64 DS_FLHEX)] ->
                 ds_repA0 LB m' ds err len B.
  Proof.
    intros LB m ds err len B HL AC (sm & pp & hm & fl & fill & DI & BL & AD & WR & AO & SA).
    pose proof (di_pos _ _ _ _ _ _ _ _ _ _ _ DI) as P0. pose proof (di_hi _ _ _ _ _ _ _ _ _ _ _ DI) as P1.
    pose proof (di_ios _ _ _ _ _ _ _ _ _ _ _ DI) as II.
    pose proof AO as (AO1 & AO2 & AO3).
    exists VT_OS_A, fl. split; [|split; [|split; [|split; [|split]]]].
    - apply rw_cells_of_fld8; [exact (di_vt _ _ _ _ _ _ _ _ _ _ _ DI)|]. eapply wr_at_sub; [exact WR | lia | unfold DS_SIZE; lia | lia].
    - exact (vboff_relro m (proj1 (LINV_P m HL))).
    - exact (vt_os_acc m AC).
    - exact (ii_fl _ _ _ _ _ II).
    - apply rw_cells_of_fld4; [exact (ii_flags _ _ _ _ _ II)|].
      eapply wr_at_sub; [exact WR | unfold DS_VBOFF; lia | unfold DS_VBOFF, DS_SIZE; lia | lia].
    - intros m' HE HF'. unfold DS_VBOFF in HE, HF'.
      destruct HF' as [HC HW].
      assert (WR' : wr_at asegs m' ds DS_SIZE).
      { eapply wr_at_patch; [exact WR | exact HW |]. intros x Hx Hn. cbn [cells_size csize Z.of_nat] in Hn.
        apply HE; [unfold DS_SIZE in Hx; lia | lia]. }
      exists sm, pp, hm, DS_FLHEX, fill. split; [|split; [exact BL|split; [|split; [exact WR'|split; [exact AO|]]]]].
      + eapply ds_inv_setfl; [exact DI | right; reflexivity | | | ].
        * unfold CRep.fld. rewrite <- rdn_of_ov.
          pose proof (cells_at_read asegs m' _ _ 0 _ HC eq_refl) as R. cbn [csize cbytes] in R.
          replace (Z_to_bv 64 (ds + 120)) with (wa (ds + 112 + 8 + Z.of_nat 0)) by (unfold wa; f_equal; lia). exact R.
        * apply mdef_of_wr_at_hi; [exact WR' | exact AO1].
        * intros a Ha Hn. apply HE; [exact Ha | lia].
      + eapply addressable_pteq; [exact AD|]. intros x Hx.
        pose proof (SHAD_bound _ _ _ (proj2 AD)) as SB'. rewrite shadow_of_length in SB' by (unfold DS_SIZE; lia).
        apply HE; [lia|]. pose proof (app_obj_sh_apart ds DS_SIZE ds DS_SIZE AO ltac:(lia) ltac:(unfold DS_SIZE, AAPP_HI; lia) ltac:(unfold DS_SIZE; lia)) as D.
        unfold DS_SIZE in *. lia.
      + destruct sm as [|d asz]; cbn [sb_addr] in *; [exact I|]. destruct SA as [SA SAo]. split; [|exact SAo].
        pose proof SAo as (S1 & S2 & S3).
        eapply addressable_pteq; [exact SA|]. intros x Hx.
        pose proof (SHAD_bound _ _ _ (proj2 SA)) as SB'. rewrite shadow_of_length in SB' by (destruct SA; lia).
        apply HE; [lia|]. pose proof (app_obj_sh_apart ds DS_SIZE d asz AO ltac:(unfold AIMG_TOP in S1; lia) S3 ltac:(destruct SA; lia)) as D.
        unfold DS_SIZE in *. lia.
  Qed.

  Theorem ds_laws_A : ds_rep_lawsA LINV ds_repA0.
  Proof.
    constructor.
    - exact dsa_blocks.
    - exact dsa_err.
    - exact dsa_def.
    - exact dsa_mono.
    - exact dsa_frame.
    - exact dsa_hex.
  Qed.
End Hex.
