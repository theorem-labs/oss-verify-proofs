(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool String Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import Hoare SeqExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VAbs VAbsSound VAbsSound2 VAbsSound3 VStep VStepMem VStepSound VStepMemSound VStepMemSound2 VCert VContract VContractSound VState2 VStepMem2 VGamma2 VStepMem2SoundA VStepMem2SoundB VStepMem2SoundC VContractA VCert2 VContract2 VContract2Iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
Unset Lia Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Lemma nth_repeat_in {X} (c d : X) k j : (j < k)%nat -> nth j (repeat c k) d = c.
Proof. revert j. induction k as [|k IH]; intros [|j] Hj; cbn; try lia; auto. apply IH. lia. Qed.

(* [comment removed for export] *)
Definition band_ok (a n : Z) : Prop := a + n <= LOW_MEM_TOP \/ HIGH_MEM_BEG <= a /\ a + n <= HIGH_MEM_END - 1.

Lemma band_ok_sub (x len a n : Z) : off_band x len -> x + len <= HIGH_MEM_END -> x <= a -> a + n < x + len -> band_ok a n.
Proof. unfold off_band, band_ok, LOW_MEM_TOP, HIGH_MEM_BEG, HIGH_MEM_END. lia. Qed.

Lemma band_ok_high (a n : Z) : HIGH_MEM_BEG <= a -> a + n <= HIGH_MEM_END - 1 -> band_ok a n.
Proof. unfold band_ok. lia. Qed.

Lemma band_ok_mono (a n b m : Z) : band_ok a n -> a <= b -> b + m <= a + n -> band_ok b m.
Proof. unfold band_ok. lia. Qed.

Lemma off_band_mono (x len len' : Z) : off_band x len -> len' <= len -> off_band x len'.
Proof. unfold off_band. lia. Qed.

Lemma band_ok_in (x len a n : Z) : off_band x len -> x + len <= HIGH_MEM_END - 1 -> x <= a -> a + n <= x + len -> band_ok a n.
Proof. unfold off_band, band_ok, LOW_MEM_TOP, HIGH_MEM_BEG, HIGH_MEM_END. lia. Qed.

Section S.
  Variable SEGS : list Segment.
  Variable P : vparams2.
  Variable E : venv2.
  Variables mem0 rom : word -> option byte.
  Variable CI : cimg.
  Let P1 := p1 P.
  Let E1 := ev1 E.
  Hypothesis PO2 : params_ok2 SEGS P.

  Variable tgt : Z.          (* [comment removed for export] *)
  Variable fill : Z.         (* [comment removed for export] *)
  Variables a_got a_cell a_memset : Z.
  Hypothesis Hfill : 0 <= fill < 256.

  (* [comment removed for export] *)
  Hypothesis GOT_PRISTINE : exists plo phi, In (plo, phi) (vp_pristine P1) /\ plo <= a_got /\ a_got + 8 <= phi.
  Hypothesis GOT_BYTES : rdn SEGS (fun _ => None) (wordZ a_got) 8 = Some (word_to_le_bytes 8 (wordZ a_cell)).
  Hypothesis CELL_PRISTINE : exists plo phi, In (plo, phi) (vp_pristine P1) /\ plo <= a_cell /\ a_cell + 8 <= phi.
  Hypothesis CELL_BYTES : rdn SEGS (fun _ => None) (wordZ a_cell) 8 = Some (word_to_le_bytes 8 (wordZ a_memset)).

  (* [comment removed for export] *)
  Hypothesis THUNK : forall regs mem,
    rdn SEGS mem (wordZ a_got) 8 = Some (word_to_le_bytes 8 (wordZ a_cell)) ->
    rdn SEGS mem (wordZ a_cell) 8 = Some (word_to_le_bytes 8 (wordZ a_memset)) ->
    exists regs1,
      msteps SEGS (mkst regs (wordZ tgt) mem rom) (mkst regs1 (wordZ a_memset) mem rom)
      /\ getr regs1 10%bv = getr regs 10%bv /\ getr regs1 11%bv = Z_to_bv 64 fill /\ getr regs1 12%bv = getr regs 11%bv
      /\ getr regs1 1%bv = getr regs 1%bv
      /\ (forall r : reg, bv_unsigned r <> 0 -> ~ In (bv_unsigned r) CALLER_SAVED -> getr regs1 r = getr regs r).

  (* [comment removed for export] *)
  Hypothesis MEMSET : forall mem (d cv ret : word) (n : Z) regs,
    0 <= n -> bv_unsigned d + n < 2 ^ 64 -> store_ok SEGS mem d (Z.to_nat n) = true -> ret_ok ret ->
    getr regs 10%bv = d -> getr regs 11%bv = cv -> getr regs 12%bv = Z_to_bv 64 n -> getr regs 1%bv = ret ->
    exists regs',
      msteps SEGS (mkst regs (wordZ a_memset) mem rom) (mkst regs' ret (wbytes mem d (repeat (Z_to_bv 8 (bv_unsigned cv)) (Z.to_nat n))) rom)
      /\ getr regs' 10%bv = d
      /\ (forall r : reg, ~ In r [11; 12; 13; 14; 15; 16]%bv -> getr regs' r = getr regs r).

  Notation gamma2P := (gamma2 SEGS P E mem0).

  Lemma rdn_pristine2 mem A nu regs a (n : nat) :
    gamma2P A nu regs mem -> (exists plo phi, In (plo, phi) (vp_pristine P1) /\ plo <= a /\ a + Z.of_nat n <= phi) ->
    rdn SEGS mem (wordZ a) n = rdn SEGS (fun _ => None) (wordZ a) n.
  Proof.
    intros HG2 [plo [phi (Hin & Q1 & Q2)]]. pose proof (proj1 HG2) as (HE1 & (MF & MD & MP & MFM) & _).
    pose proof (PO1 _ _ PO2) as (P0 & Psphi & _ & _ & _ & _ & PP & _). destruct (PP _ _ Hin) as [R0 R1].
    pose proof HE1 as (_ & Esp & _ & _ & _ & _ & _ & _ & _ & _ & Efr). unfold P1 in *.
    apply rdn_ext; [rewrite u_wordZ; lia|].
    intros x Hx. rewrite u_wordZ in Hx by lia. rewrite <- (wordZ_u x). apply (MP plo phi); [exact Hin|lia].
  Qed.

  Theorem set_shadow_dead : contract_dead2 SEGS P E mem0 CI (C_set_shadow fill).
  Proof.
    intros A spoff nu regs mem HC HG2. cbn [contract_apply2] in HC. unfold of_ca, ca_set_shadow in HC.
    destruct (get_reg2 A A0r) as [ea|]; [|discriminate]. destruct (get_reg2 A A1r) as [en|]; [|discriminate].
    destruct (negb _); [discriminate|].
    destruct (classify2 A ea (lc en) true) as [[r off lo hi| |m]|] eqn:CL; try discriminate.
    - destruct (vr_kind r); try discriminate. destruct (Pos.eqb _ DATA); [discriminate|]. destruct (negb _); discriminate.
    - exact (classify2_dead A nu ea (lc en) true (gamma2_lgamma _ _ _ _ _ _ _ _ HG2) CL).
  Qed.

  #[using="P1 E1 PO2 a_got a_cell a_memset Hfill GOT_PRISTINE GOT_BYTES CELL_PRISTINE CELL_BYTES THUNK MEMSET"] Theorem set_shadow_post : contract_post2 SEGS P E mem0 rom CI (C_set_shadow fill) tgt.
  Proof.
    intros A spoff l nu regs mem ra HC HG2 MEMO Hsp HK Hret Hra.
    pose proof HG2 as (HG1 & HE & HM & HF2 & HDD & RGN & LIVE & BEL2 & GL2 & FI2 & MOK).
    pose proof (gamma2_lgamma _ _ _ _ _ _ _ _ HG2) as HL.
    cbn [contract_apply2] in HC. unfold of_ca, ca_set_shadow in HC.
    destruct (get_reg2 A A0r) as [ea|] eqn:Hea; [|discriminate]. destruct (get_reg2 A A1r) as [en|] eqn:Hen; [|discriminate].
    destruct (lin_is_const en && (0 <? lc en) && (lc en <=? 2 ^ 18)) eqn:CN; cbn [negb] in HC; [|discriminate].
    apply andb_prop in CN as [CN N2]. apply andb_prop in CN as [CE N1]. apply Z.ltb_lt in N1. apply Z.leb_le in N2.
    set (n := lc en) in *.
    destruct (classify2 A ea n true) as [[r off lo hi| |m]|] eqn:CL; try discriminate.
    destruct (vr_kind r) as [| | |sb|] eqn:KS; try discriminate.
    destruct (Pos.eqb_spec sb DATA) as [|NSD]; [discriminate|].
    destruct (Z.eqb_spec lo hi) as [Elh|]; cbn [negb] in HC; [|discriminate].
    injection HC as <-.
    (* [comment removed for export] *)
    destruct (classify2_rgn A ea n true r off lo hi CL) as (B & r0 & HB & HCo & HR0 & HCL).
    destruct (classify_rgn_sound A nu r0 ea n true r off lo hi HL ltac:(lia) HCL) as (-> & Eoff & Eaddr & NDS & DSH).
    pose proof (rgn_in _ _ _ HR0) as Hr.
    assert (ND : is_data_shadow r0 = false).
    { unfold is_data_shadow. rewrite KS. destruct (Pos.eqb_spec sb DATA); [contradiction|reflexivity]. }
    destruct (NDS ND) as (Hlohi & Hlo & Hhi & HW). specialize (HW eq_refl). rewrite <- Elh, Z.sub_diag, Z.add_0_l in HW.
    assert (EO : eval nu off = lo) by lia.
    pose proof (RGN r0 Hr) as ROK. pose proof ROK as (RB1 & RB2 & RB3 & RDS & CELLS & PERM & NUL & KIND).
    set (a := rbase nu r0 + lo).
    (* [comment removed for export] *)
    unfold get_reg2 in Hea, Hen.
    pose proof (gamma_get_reg SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem 10%bv HG1) as [W10 _]. cbn [rz bv_unsigned] in W10.
    change (rz 10%bv) with A0r in W10. rewrite Hea in W10. apply wval_some in W10.
    pose proof (gamma_get_reg SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem 11%bv HG1) as [W11 _].
    change (rz 11%bv) with A1r in W11. rewrite Hen in W11. apply wval_some in W11. rewrite (eval_is_const nu en CE) in W11. fold n in W11.
    assert (Ea : bv_unsigned (getr regs 10%bv) = a) by (rewrite W10, Eaddr, EO; unfold a; apply zwrap_id; unfold a in *; lia).
    assert (En : getr regs 11%bv = Z_to_bv 64 n).
    { apply bv_eq. rewrite W11, u_Z_to_bv64. reflexivity. }
    assert (Ed : getr regs 10%bv = wordZ a) by (apply bv_eq; rewrite Ea; unfold wordZ; rewrite u_Z_to_bv64, zwrap_id; [reflexivity|unfold a in *; lia]).
    (* [comment removed for export] *)
    set (bs := repeat (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 fill))) (Z.to_nat n)).
    assert (Hlen : length bs = Z.to_nat n) by apply repeat_length.
    set (b0 := Z.land fill 255) in *.
    set (r' := set_rnul (set_cells r0 (sh_write (vr_cells r0) lo n (Some (lconst b0)))) []).
    set (l2 := rgn_upd (vs_rgn A) r').
    assert (SH2 : rshape r0 r') by (eapply rshape_trans; [apply rshape_set_cells|apply rshape_set_rnul]).
    pose proof SH2 as (SB2 & _).
    assert (INB : In (vr_base r') (map vr_base (vs_rgn A))) by (rewrite SB2; apply in_map; exact Hr).
    assert (SM : shape_map (vs_rgn A) l2).
    { unfold l2. apply rgn_upd_shape; [|exact INB]. intros x Hx EB.
      rewrite (live_ok_base_inj nu A x r0 LIVE Hx Hr ltac:(rewrite EB; exact SB2)). exact SH2. }
    pose proof LIVE as (_ & _ & _ & ND0).
    assert (MEM : forall x, In x l2 -> x = r' \/ (In x (vs_rgn A) /\ vr_base x <> vr_base r0)).
    { intros x Hx. destruct (rgn_upd_other _ _ _ ND0 INB Hx) as [->|[Y1 Y2]]; [auto|right]. rewrite SB2 in Y2. auto. }
    assert (Eb0 : bv_unsigned (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 fill))) = b0).
    { rewrite Z_to_bv_unsigned, bv_wrap8_mod, u_Z_to_bv64, (zwrap_id 64 fill) by lia. unfold b0.
      rewrite <- Z.land_ones by lia. reflexivity. }
    destruct (rgn_write_sound SEGS P E mem0 PO2 A nu regs mem r0 lo bs l2 HG2 Hr ND ltac:(rewrite KS; exact I)
                ltac:(rewrite Hlen, Z2Nat.id by (ltac2:(LK.k [@Hfill; @N1; @NSD; @NDS; @ND; @Hlen; @SB2]); lia); (ltac2:(LK.k [@Hfill; @N1; @NSD; @NDS; @ND; @Hlen; @SB2]); lia)) ltac:(rewrite Hlen, Z2Nat.id by (ltac2:(LK.k [@Hfill; @N1; @NSD; @NDS; @ND; @Hlen; @SB2]); lia); exact HW) SM) as (G2 & FM & FS & BND & SOK).
    { (* [comment removed for export] *)
      intros r2' Hr2' NB. destruct (MEM r2' Hr2') as [->|[X1 X2]]; [exfalso; apply NB; exact SB2|].
      exists r2'. split; [exact X1|]. split; [apply rshape_refl|]. left. split; [reflexivity|]. split; [reflexivity|].
      rewrite KS. intros [X _]. discriminate. }
    { (* [comment removed for export] *)
      intros rr Hrr EB.
      assert (ER : rr = r') by (destruct (MEM rr Hrr) as [->|[X1 X2]]; [reflexivity|exfalso; exact (X2 EB)]). subst rr.
      assert (ISH : is_shadow r0 = true) by (unfold is_shadow; rewrite KS; reflexivity).
      set (mem' := wbytes mem (wordZ (rbase nu r0 + lo)) bs).
      assert (BYTE : forall j, (j < Z.to_nat n)%nat ->
                exists kb : byte, rdn SEGS mem' (wordZ (rbase nu r0 + lo + Z.of_nat j)) 1 = Some [kb] /\ bv_unsigned kb = Z.land b0 255).
      { intros j Hj. unfold mem'. eexists. split.
        - rewrite (rdn_wbytes_byte SEGS mem (rbase nu r0 + lo) bs j); rewrite ?Hlen; [|unfold a in *; (ltac2:(LK.k [@Hfill; @N1; @NSD; @NDS; @ND; @Hlo; @EO; @RB1; @Hlen; @SB2; @EB; @Hj; @Hhi; @RB2]); lia)|unfold a in *; (ltac2:(LK.k [@Hfill; @N1; @NSD; @NDS; @ND; @Hlo; @EO; @RB1; @Hlen; @SB2; @EB; @Hj; @Hhi; @RB2]); lia)|exact Hj].
          unfold bs. rewrite nth_repeat_in by exact Hj. reflexivity.
        - rewrite Eb0. unfold b0. rewrite <- Z.land_assoc. reflexivity. }
      assert (CUT : forall c cw cv, In (c, (cw, cv)) (sh_cut (vr_cells r0) lo (lo + n)) ->
                vr_lo r0 <= c /\ 0 < cw /\ c + cw <= vr_hi r0 /\ rcell_holds SEGS (is_shadow r0) nu mem' (rbase nu r0 + c) cw cv).
      { intros c cw cv Hin. apply sh_cut_in in Hin as (k0 & w0 & Hold & K1 & K2 & DISJ & PIECE).
        destruct (CELLS _ _ _ Hold) as (L1 & L2 & L3 & RC).
        destruct PIECE as [EQ|(Hw & e1 & -> & CE1)].
        - injection EQ as -> ->. split; [lia|]. split; [lia|]. split; [lia|]. unfold mem'. apply kept_cell; rewrite ?Hlen; try (unfold a in *; (ltac2:(LK.k [@Hfill; @N1; @NSD; @NDS; @ND; @Hlo; @Hhi; @EO; @RB1; @RB2; @Hlen; @SB2; @EB; @DISJ; @L1; @L2; @L3]); lia)). exact RC.
        - split; [lia|]. split; [lia|]. split; [lia|]. unfold rcell_holds in RC |- *. rewrite ISH, CE1 in RC |- *. cbn [andb] in RC |- *.
          intros i Hi. destruct (RC (c - k0 + i) ltac:(lia)) as (kb & Hkb & Hb). exists kb. split; [|exact Hb].
          replace (rbase nu r0 + c + i) with (rbase nu r0 + k0 + (c - k0 + i)) by lia. rewrite <- Hkb.
          unfold mem'. apply wblock_rdn1; rewrite ?Hlen; unfold a in *; (ltac2:(LK.k [@Hfill; @N1; @NSD; @NDS; @ND; @Hlo; @Hhi; @EO; @RB1; @RB2; @Hlen; @SB2; @EB; @K1; @K2; @DISJ; @Hw; @L1; @L3; @Hi]); lia). }
      (* [comment removed for export] *)
      assert (POS : forall k0 w0 v0, In (k0, (w0, v0)) (sh_cut (vr_cells r0) lo (lo + n)) -> 0 < w0).
      { intros k0 w0 v0 HX. apply sh_cut_in in HX as (k1 & w1 & Hold & K1 & K2 & _ & PIECE).
        destruct (CELLS _ _ _ Hold) as (_ & Pw0 & _). destruct PIECE as [EQ|(Hw & _)]; [injection EQ as -> ->; exact Pw0|exact Hw]. }
      split.
      2:{ cbn [vr_cells r' set_rnul set_cells]. intros kk ww ee Hin. destruct BEL2 as (_ & BR & _). pose proof (proj1 (proj2 (BR r0 Hr))) as CB.
          unfold sh_write in Hin. replace (lin_is_const (lconst b0)) with true in Hin by reflexivity.
          destruct (sh_ins_in (sh_cut (vr_cells r0) lo (lo + n)) lo n (lconst b0) kk ww (Some ee) ltac:(lia) POS Hin) as [Hin'|(Hv & _)]; [|injection Hv as ->; apply lin_below_lconst].
          apply sh_cut_in in Hin' as (k0 & w0 & Hold & _). exact (CB _ _ _ Hold). }
      eapply (region_ok_self SEGS P E A _ nu mem mem' r0 r' HE ROK SH2 ND).
      + apply wbytes_grows.
      + rewrite KS. exact I.
      + intros s0 ro G _ _. cbn [vs_rgn]. exact (shape_map_get _ _ _ _ SM G).
      + rewrite KS. exact I.
      + rewrite KS. exact I.
      + cbn [vr_cells r' set_rnul set_cells]. intros c cw cv Hin. unfold sh_write in Hin.
        replace (lin_is_const (lconst b0)) with true in Hin by reflexivity. rewrite ISH.
        refine (sh_ins_cells SEGS nu mem' r0 lo n b0 _ ltac:((ltac2:(LK.k [@Hfill; @N1; @NSD; @NDS; @ND; @Hlen; @SB2; @EB; @Hlo; @EO; @Hhi]); lia)) ltac:((ltac2:(LK.k [@Hfill; @N1; @NSD; @NDS; @ND; @Hlen; @SB2; @EB; @Hlo; @EO; @Hhi]); lia)) ltac:((ltac2:(LK.k [@Hfill; @N1; @NSD; @NDS; @ND; @Hlen; @SB2; @EB; @Hlo; @EO; @Hhi]); lia)) _ _ c cw cv Hin).
        * intros c' cw' cv' X. pose proof (CUT _ _ _ X) as Y. rewrite ISH in Y. exact Y.
        * intros i Hi. destruct (BYTE (Z.to_nat i) ltac:(lia)) as (kb & R1 & R2). exists kb. split; [|exact R2].
          replace (rbase nu r0 + lo + i) with (rbase nu r0 + lo + Z.of_nat (Z.to_nat i)) by lia. exact R1.
      + cbn. intros ? ? []. }
    (* [comment removed for export] *)
    set (mem' := wbytes mem (wordZ a) bs) in *.
    assert (GOT : rdn SEGS mem (wordZ a_got) 8 = Some (word_to_le_bytes 8 (wordZ a_cell))).
    { rewrite (rdn_pristine2 mem A nu regs a_got 8 HG2); [exact GOT_BYTES|].
      destruct GOT_PRISTINE as [plo [phi X]]. exists plo, phi. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. exact X. }
    assert (CELL : rdn SEGS mem (wordZ a_cell) 8 = Some (word_to_le_bytes 8 (wordZ a_memset))).
    { rewrite (rdn_pristine2 mem A nu regs a_cell 8 HG2); [exact CELL_BYTES|].
      destruct CELL_PRISTINE as [plo [phi X]]. exists plo, phi. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. exact X. }
    destruct (THUNK regs mem GOT CELL) as (regs1 & RUN1 & T10 & T11 & T12 & T1 & TK).
    (* [comment removed for export] *)
    assert (HI : a + n < 2 ^ 64).
    { assert (FSnz : vp_fs P <> None) by (unfold kind_ok in KIND; rewrite KS in KIND; exact (proj1 KIND)).
      pose proof (layout_of_env SEGS P E PO2 HE FSnz) as L.
      destruct (region_desc SEGS P E mem0 PO2 A nu regs mem r0 HG2 Hr ND) as (d1 & V1 & M1 & D1).
      assert (SHD : match d1 with DShStack | DShSlot _ _ => True | _ => False end).
      { unfold desc_matches in M1. rewrite KS in M1. destruct d1; auto; contradiction. }
      pose proof (dbyte_side (e_fs E) (e_sp0 (ev1 E)) (vp_frame (p1 P)) (vp_shoff P) d1 (a + n - 1) L V1
                    ltac:(replace (a + n - 1) with (rbase nu r0 + (lo + n - 1)) by (unfold a; (ltac2:(LK.k [@Hfill; @NSD; @NDS; @ND; @Hlen; @SB2; @N1; @Hlo; @Hhi; @EO]); lia)); apply D1; (ltac2:(LK.k [@Hfill; @NSD; @NDS; @ND; @Hlen; @SB2; @N1; @Hlo; @Hhi; @EO]); lia))) as SD.
      destruct d1; try contradiction; unfold HIGH_MEM_BEG in SD; (ltac2:(LK.k [@Hfill; @NSD; @NDS; @ND; @Hlen; @SB2; @SHD; @SD]); lia). }
    destruct (MEMSET mem (getr regs 10%bv) (Z_to_bv 64 fill) ra n regs1 ltac:((ltac2:(LK.k [@Hfill; @N1; @NSD; @NDS; @ND; @Hlen; @SB2; @HI; @BND; @Hk]); lia)) ltac:(rewrite Ea; (ltac2:(LK.k [@Hfill; @N1; @NSD; @NDS; @ND; @Hlen; @SB2; @HI; @BND; @Hk]); lia))
                ltac:(rewrite Ed; apply store_ok_bytes; rewrite ?Z2Nat.id by (ltac2:(LK.k [@Hfill; @N1; @NSD; @NDS; @ND; @Hlen; @SB2; @HI; @BND; @Hk]); lia); [unfold a in *; (ltac2:(LK.k [@Hfill; @N1; @NSD; @NDS; @ND; @Hlen; @SB2; @HI; @BND; @Hk]); lia)|(ltac2:(LK.k [@Hfill; @N1; @NSD; @NDS; @ND; @Hlen; @SB2; @HI; @BND; @Hk]); lia)|intros k Hk; apply SOK; rewrite Hlen, Z2Nat.id by (ltac2:(LK.k [@Hfill; @N1; @NSD; @NDS; @ND; @Hlen; @SB2; @HI; @BND; @Hk]); lia); exact Hk])
                Hret T10 T11 ltac:(rewrite T12; exact En) ltac:(rewrite T1; exact Hra)) as (regs' & RUN2 & P10 & AG).
    rewrite Ed in RUN2. fold bs in RUN2. fold mem' in RUN2.
    (* [comment removed for export] *)
    set (A2 := mkVS2 (v1 A) l2 (vs_live A) (vs_divdef A) []) in *.
    set (Bst := contract_frame C_memset (v1 A) spoff (Some ea)).
    assert (REGS' : forall r : reg, bv_unsigned r <> 0 -> ~ In (bv_unsigned r) CALLER_SAVED -> getr regs' r = getr regs r).
    { intros x Hx Hcs. rewrite AG; [exact (TK x Hx Hcs)|].
      intros Hin. apply Hcs. unfold CALLER_SAVED.
      destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn; auto 20. }
    destruct (contract_frame_shape C_memset (v1 A) spoff (Some ea)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & FR).
    pose proof (gamma_get_reg SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem 10%bv HG1) as [_ Bea].
    change (rz 10%bv) with A0r in Bea. rewrite Hea in Bea. cbn [vbelow] in Bea.
    assert (HLB : lgamma Bst nu) by (apply lgamma_contract_frame; [exact HL|exact Bea]).
    (* [comment removed for export] *)
    pose proof (proj1 G2) as G1'. cbn [v1] in G1'.
    destruct (gamma_call_post SEGS P1 E1 (zpatch P E mem0 mem') rom (PO1 _ _ PO2) (v1 A) Bst nu nu regs regs' mem' mem' []
                G1' (ext_refl _ _) ltac:(unfold Bst; rewrite F5; apply Pos.le_refl) HLB) as [GB _].
    { eapply (gamma_regs_contract_frame SEGS P1 E1 (zpatch P E mem0 mem') C_memset (v1 A) (v1 A) spoff (Some ea) nu nu regs regs');
        [right; pose proof G1' as (_&_&_&_&_&_&_&HRg&_&_&_&HBl); split; [exact HRg|destruct HBl as (_&_&RB&_); exact RB]
        |apply ext_refl|reflexivity|exact REGS'|].
      rewrite P10, W10. reflexivity. }
    { intros off' w v Hin. left. unfold Bst in Hin. rewrite F1 in Hin. cbn in Hin. split; [exact Hin|]. intros x _. exact I. }
    { intros g w v Hin. unfold Bst in Hin. rewrite F2 in Hin. split; [exact Hin|]. intros x _. exact I. }
    { intros lo' hi' Hin. left. unfold Bst in Hin. destruct (F3 _ Hin) as [Hin' _]. split; [exact Hin'|]. intros x _. exact I. }
    { apply frame_mod_refl. }
    { intros x Hx. exfalso. apply Hx. exact I. }
    (* [comment removed for export] *)
    destruct (gamma2_lift SEGS P E mem0 PO2 A2 Bst nu nu regs regs' mem' mem' G2 GB (ext_refl _ _)
                ltac:(unfold A2, Bst; cbn [v1]; rewrite F5; apply Pos.le_refl) (frame_mod_refl _ _)
                ltac:(unfold globs_ok2, A2, Bst; cbn [v1 with_v1]; rewrite F2; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 G2))))))))))
                ltac:(left; reflexivity))
      as (G3 & _ & FS3).
    (* [comment removed for export] *)
    exists (set_rgn A l2), (Some ea), regs', mem', nu.
    assert (EF : contract_frame2 (C_set_shadow fill) (set_rgn A l2) spoff (Some ea) = with_v1 A2 Bst).
    { unfold contract_frame2, set_rgn, with_v1, A2. cbn [v1 vs_rgn vs_live vs_divdef vs_memo]. rewrite MEMO. reflexivity. }
    rewrite EF.
    split; [left; reflexivity|]. split.
    { eapply msteps_trans; [exact RUN1|exact RUN2]. }
    split; [exact G3|]. split.
    { rewrite AG by (cbn; intros [X|[X|[X|[X|[X|[X|[]]]]]]]; discriminate). rewrite T1. exact Hra. }
    split; [apply ext_refl|]. split.
    { unfold vs2_next, A2, Bst. cbn [v1 with_v1]. rewrite F5. apply Pos.le_refl. }
    split; [exact FM|].
    eapply flags_step_then_same; [exact FS|]. intros y Hy. split; [|reflexivity].
    unfold A2, with_v1. cbn [v1 vs_rgn vs_live vs_divdef vs_memo].
    rewrite (own_flags_shape A (v1 A) l2 nu (vs_live A) (vs_divdef A) [] SM), (own_flags_shape A Bst l2 nu (vs_live A) (vs_divdef A) [] SM). tauto.
  Qed.
End S.
