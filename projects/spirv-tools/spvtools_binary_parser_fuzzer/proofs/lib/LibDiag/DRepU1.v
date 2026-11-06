(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec StepTac MmapSim Frame MemSplit CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SRealizes RefMemcpyLib LibIface LibBudget LibEff U1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsNeeds.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag Require Import DiagU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma u_small : forall z, (0 <= z < 2^64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  change (bv_modulus 64) with (2^64)%Z. lia.
Qed.

Definition DS_VBOFF : Z := 112.

Section Rep.
Context {AC : AllocCeiling}.
  Variable MI : MallocIface SEGS L.
  Variable ST : StaticsIface SEGS L.

  #[local] Notation fld := (CRep.fld SEGS).

  Record sb_inv (A : AS MI) (M : mem) (sb : Z) (m : sbuf) (pp hm : Z) : Prop := SB_INV {
    si_vt    : fld M sb 8 VT_SB;
    si_loc   : fld M (sb + 8) 8 LOC_IMP;
    si_binp  : fld M (sb + 16) 8 0;
    si_ninp  : fld M (sb + 24) 8 0;
    si_einp  : fld M (sb + 32) 8 0;
    si_str   : exists cs, str_rep MI A M (sb + 64) m cs /\ Zlen cs = str_cap m;
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
    ii_vt    : fld M io 8 VT_IOS;
    ii_flags : fld M (io + 8) 4 fl;
    ii_fl    : fl = DS_FL0 \/ fl = DS_FLHEX;
    ii_prec  : fld M (io + 16) 8 6;
    ii_width : fld M (io + 24) 8 0;
    ii_state : fld M (io + 32) 4 0;
    ii_exc   : fld M (io + 36) 4 0;
    ii_rdbuf : fld M (io + 40) 8 sb;
    ii_loc   : fld M (io + 48) 8 LOC_IMP;
    ii_zero  : ios_zero M io;
    ii_tie   : fld M (io + 136) 8 0;
    ii_fill  : fld M (io + 144) 4 fill;
    ii_fillr : fill = 2 ^ 32 - 1 \/ fill = 32
  }.

  Record ds_inv (A : AS MI) (M : mem) (ds err len : Z) (B : list (Z * Z))
                (m : sbuf) (pp hm fl fill : Z) : Prop := DS_INV {
    di_pos   : 0 < ds;
    di_al    : ds mod 8 = 0;
    di_hi    : ds + 392 <= 2 ^ 47;
    di_def   : mdef M ds 392;
    di_vt    : fld M ds 8 VT_OS;
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

  Definition ds_rep (A : AS MI) (M : mem) (ds err len : Z) (B : list (Z * Z)) : Prop :=
    exists m pp hm fl fill, ds_inv A M ds err len B m pp hm fl fill.

  Lemma fld_ag : forall M M' (P : Z -> Prop) a (k : nat) v,
    0 <= a -> a + Z.of_nat k < 2 ^ 64 -> (forall x, a <= x < a + Z.of_nat k -> P x) ->
    agree_on P M M' -> fld M a k v -> fld M' a k v.
  Proof using.
    intros M M' P a k v Ha Hk HP HA HF. eapply fld_agree; [lia | lia | exact HF |].
    eapply agree_on_weaken; [exact HA|]. intros x Hx. apply HP. unfold zwin in Hx. lia.
  Qed.

  Definition sb_fp (sb : Z) (m : sbuf) (a : Z) : Prop :=
    zwin sb (sb + 104) a \/ match m with SShort => False | SLong d asz => zwin d (d + asz) a end.

  Lemma sb_inv_frame : forall A A' M M' sb m pp hm,
    sb_inv A M sb m pp hm -> 0 <= sb -> sb + 104 <= 2 ^ 47 ->
    agree_on (sb_fp sb m) M M' ->
    (forall blk, In blk (str_blocks m) -> In blk (live MI A')) ->
    sb_inv A' M' sb m pp hm.
  Proof using AC MI.
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
  Proof using.
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

  Lemma ds_inv_frame : forall A A' M M' ds err len B m pp hm fl fill,
    ds_inv A M ds err len B m pp hm fl fill ->
    agree_on (ds_foot ds B) M M' ->
    (forall blk, In blk B -> In blk (live MI A')) ->
    ds_inv A' M' ds err len B m pp hm fl fill.
  Proof using AC MI.
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
  Proof using AC MI.
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

  Lemma ds_blocks : forall A M ds err len B, ds_rep A M ds err len B ->
    Zlength B <= 1 /\ (forall q k, In (q, k) B -> In (q, k) (live MI A) /\ 0 < k <= DS_MAXBLK).
  Proof using AC MI.
    intros A M ds err len B (m & pp & hm & fl & fill & DI).
    pose proof (di_B _ _ _ _ _ _ _ _ _ _ _ DI) as HB. pose proof (di_mx _ _ _ _ _ _ _ _ _ _ _ DI) as HMX.
    destruct (si_str _ _ _ _ _ _ (di_sb _ _ _ _ _ _ _ _ _ _ _ DI)) as (cs & SR & _).
    subst B. destruct m as [|d asz]; cbn [str_blocks].
    - split; [unfold Zlength; cbn; lia|]. intros q k [].
    - split; [unfold Zlength; cbn; lia|]. intros q k [E|[]]. injection E as <- <-.
      destruct SR as (_ & _ & _ & _ & (Hd & _ & _ & _ & Hsz & HIn & _) & _).
      split; [exact HIn|]. split; [unfold SSO_CAP in Hsz; lia | exact (HMX d asz eq_refl)].
  Qed.

  Lemma ds_err : forall A M ds err len B, ds_rep A M ds err len B -> fld M (ds + 360) 4 (err mod 2 ^ 32).
  Proof using AC MI. intros A M ds err len B (m & pp & hm & fl & fill & DI). exact (di_f360 _ _ _ _ _ _ _ _ _ _ _ DI). Qed.

  Lemma ds_def : forall A M ds err len B, ds_rep A M ds err len B -> mdef M ds DS_SIZE /\ 0 < ds /\ ds + DS_SIZE <= 2 ^ 47 /\ 0 <= len.
  Proof using AC MI.
    intros A M ds err len B (m & pp & hm & fl & fill & DI). unfold DS_SIZE. destruct DI.
    repeat split; assumption.
  Qed.

  Lemma ds_mono : forall A M ds err len len' B, ds_rep A M ds err len B -> len <= len' -> ds_rep A M ds err len' B.
  Proof using AC MI.
    intros A M ds err len len' B (m & pp & hm & fl & fill & DI) Hle. exists m, pp, hm, fl, fill. destruct DI.
    constructor; try assumption; try lia. intros d asz Hm. specialize (di_asz0 d asz Hm). lia.
  Qed.

  Lemma ds_frame : forall A A' M M' ds err len B, ds_rep A M ds err len B ->
    agree_on (fun a => zwin ds (ds + DS_SIZE) a \/ exists q k, In (q, k) B /\ q <= a < q + k) M M' ->
    (forall blk, In blk B -> In blk (live MI A')) -> ds_rep A' M' ds err len B.
  Proof using AC MI.
    intros A A' M M' ds err len B (m & pp & hm & fl & fill & DI) HA HL. exists m, pp, hm, fl, fill.
    eapply ds_inv_frame; [exact DI | exact HA | exact HL].
  Qed.

  Lemma vboff_img : forall M1, img_ro_clear L M1 -> sx_cells_hold SEGS L ST M1 -> fld M1 (VT_OS - 24) 8 DS_VBOFF.
  Proof using ST.
    intros M1 HR [s SX]. unfold CRep.fld, VT_OS, DS_VBOFF.
    rewrite (rdn_ext SEGS 8 M1 (fun _ => None)).
    - vm_compute. reflexivity.
    - rewrite u_small by lia. cbn. lia.
    - intros x Hx. rewrite u_small in Hx by lia. rewrite <- (Z_to_bv_bv_unsigned 64 x).
      apply (sx_relro ST s M1 (bv_unsigned x) SX). exists 0xe8000, 0xef000. split; [left; reflexivity | cbn in Hx; lia].
  Qed.

  Lemma ds_inv_setfl : forall A M ds err len B m pp hm fl fill fl',
    ds_inv A M ds err len B m pp hm fl fill -> fl' = DS_FL0 \/ fl' = DS_FLHEX ->
    ds_inv A (wbytes M (Z_to_bv 64 (ds + 120)) (word_to_le_bytes 4 (Z_to_bv 64 fl'))) ds err len B m pp hm fl' fill.
  Proof using AC MI.
    intros A M ds err len B m pp hm fl fill fl' DI Hfl'.
    set (M' := wbytes M (Z_to_bv 64 (ds + 120)) (word_to_le_bytes 4 (Z_to_bv 64 fl'))).
    pose proof (di_pos _ _ _ _ _ _ _ _ _ _ _ DI) as G1. pose proof (di_hi _ _ _ _ _ _ _ _ _ _ _ DI) as G3.
    assert (OUT : forall x : word, ~ (ds + 120 <= bv_unsigned x < ds + 124) -> M' x = M x).
    { intros x Hx. subst M'. apply wbytes_outside; rewrite ?length_N_to_le_bytes; [|rewrite u_small by lia; cbn; lia].
      unfold in_rng. rewrite u_small by lia. cbn. lia. }
    assert (AG : forall P : Z -> Prop, (forall a, P a -> 0 <= a < 2 ^ 64 /\ ~ (ds + 120 <= a < ds + 124)) -> agree_on P M M').
    { intros P HP a Ha. destruct (HP a Ha) as [Hr Hn]. apply OUT. rewrite u_small by lia. exact Hn. }
    pose proof ac_bounds_lit as Hcv. destruct DI.
    assert (FO : forall a (k : nat) v, ds <= a -> (a + Z.of_nat k <= ds + 120 \/ ds + 124 <= a) -> a + Z.of_nat k <= ds + 392 ->
                 fld M a k v -> fld M' a k v).
    { intros a k v Ho Hd Hk HF. eapply (fld_ag M M' (fun x => a <= x < a + Z.of_nat k)); [lia | lia | intros x Hx; exact Hx | | exact HF].
      apply AG. intros x Hx. lia. }
    constructor; try assumption.
    - intros i Hi. subst M'. apply wbytes_grows. apply di_def0. exact Hi.
    - apply FO; [lia | cbn; lia | cbn; lia | assumption].
    - eapply sb_inv_frame; [exact di_sb0 | lia | lia | | intros blk Hb; destruct (si_str _ _ _ _ _ _ di_sb0) as (cs & SR & _); exact (str_blocks_live MI _ _ _ _ _ SR blk Hb)].
      apply AG. intros a Ha. unfold sb_fp, zwin in Ha. destruct Ha as [Ha|Ha]; [lia|].
      destruct m as [|d asz]; [destruct Ha|]. specialize (di_dj0 d asz eq_refl).
      destruct (si_str _ _ _ _ _ _ di_sb0) as (cs & SR & _). destruct SR as (_ & _ & _ & _ & (Hd & _ & Hde & _) & _). lia.
    - destruct di_ios0. constructor; try assumption; try (apply FO; [lia | cbn; lia | cbn; lia | assumption]).
      + subst M'. unfold CRep.fld. replace (ds + 112 + 8) with (ds + 120) by lia.
        replace 4%nat with (length (word_to_le_bytes 4 (Z_to_bv 64 fl'))) at 1 by (rewrite length_N_to_le_bytes; reflexivity).
        apply rdn_wbytes_hit. rewrite length_N_to_le_bytes, u_small by lia. cbn. lia.
      + intros i Hi. apply FO; [lia | cbn; lia | cbn; lia |]. apply ii_zero0. exact Hi.
    - apply FO; [lia | cbn; lia | cbn; lia | assumption].
    - apply FO; [lia | cbn; lia | cbn; lia | assumption].
    - apply FO; [lia | cbn; lia | cbn; lia | assumption].
    - apply FO; [lia | cbn; lia | cbn; lia | assumption].
  Qed.

  Lemma ds_hex : forall A M ds err len B, ds_rep A M ds err len B ->
    exists vt fl, fld M ds 8 vt /\ (forall M1, img_ro_clear L M1 -> sx_cells_hold SEGS L ST M1 -> fld M1 (vt - 24) 8 DS_VBOFF)
                 /\ 24 <= vt < 2 ^ 47 /\ (fl = DS_FL0 \/ fl = DS_FLHEX)
                 /\ 0 < DS_VBOFF /\ DS_VBOFF + 12 <= 360 /\ fld M (ds + DS_VBOFF + 8) 4 fl /\
      ds_rep A (wbytes M (Z_to_bv 64 (ds + DS_VBOFF + 8)) (word_to_le_bytes 4 (Z_to_bv 64 DS_FLHEX))) ds err len B.
  Proof using AC MI ST.
    intros A M ds err len B (m & pp & hm & fl & fill & DI).
    exists VT_OS, fl. split; [exact (di_vt _ _ _ _ _ _ _ _ _ _ _ DI)|]. split; [exact vboff_img|]. split; [unfold VT_OS; lia|].
    split; [exact (ii_fl _ _ _ _ _ (di_ios _ _ _ _ _ _ _ _ _ _ _ DI))|].
    split; [unfold DS_VBOFF; lia|]. split; [unfold DS_VBOFF; lia|].
    split; [unfold DS_VBOFF; replace (ds + 112 + 8) with (ds + 112 + 8) by lia; exact (ii_flags _ _ _ _ _ (di_ios _ _ _ _ _ _ _ _ _ _ _ DI))|].
    unfold DS_VBOFF. replace (ds + 112 + 8) with (ds + 120) by lia.
    exists m, pp, hm, DS_FLHEX, fill. eapply ds_inv_setfl; [exact DI | right; reflexivity].
  Qed.

  Theorem ds_laws : forall dc, dc_vboff dc = DS_VBOFF -> ds_rep_laws SEGS L MI ST dc ds_rep.
  Proof using AC MI ST.
    intros dc Hvb. constructor; rewrite ?Hvb.
    - exact ds_blocks.
    - exact ds_err.
    - exact ds_def.
    - exact ds_mono.
    - exact ds_frame.
    - intros A M ds err len B DS. exact (ds_hex A M ds err len B DS).
  Qed.
End Rep.

Arguments sb_inv {AC MI} A M sb m pp hm.
Arguments ios_inv M io sb fl fill.
Arguments ds_inv {AC MI} A M ds err len B m pp hm fl fill.
Arguments ds_rep {AC} MI A M ds err len B.
Arguments sb_fp sb m a /.
