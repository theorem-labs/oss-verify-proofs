From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require reac_box_catalogue_defect_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import strcmp_c reac_box_catalogue_defect_c.
Import ListNotations.
Open Scope Z_scope.

Lemma sx32_s32 : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616. change (2 ^ Z.of_N 32) with 4294967296.
  change (4294967296 / 2) with 2147483648.
  Z.div_mod_to_equations. lia.
Qed.

Lemma eqb_s32 : forall x y, -2^31 <= x < 2^31 -> -2^31 <= y < 2^31 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof.
  intros x y Hx Hy. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616.
  destruct (Z.eqb_spec x y) as [->|NE]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros H. Z.div_mod_to_equations. lia.
Qed.

Lemma eqb_u64_0 : forall x, 0 <= x < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = (x =? 0).
Proof. intros x Hx. unfold bv_eqb. rewrite (unsigned_lit x) by lia. reflexivity. Qed.

Lemma bd_true : forall sP sd : list byte, sP = sd -> bool_decide (sP = sd) = true.
Proof.
  intros sP sd H. unfold bool_decide.
  match goal with |- (if ?D then _ else _) = _ => destruct D end; [reflexivity | contradiction].
Qed.

Lemma bd_false : forall sP sd : list byte, sP <> sd -> bool_decide (sP = sd) = false.
Proof.
  intros sP sd H. unfold bool_decide.
  match goal with |- (if ?D then _ else _) = _ => destruct D end; [contradiction | reflexivity].
Qed.

Lemma land7_mod8 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Ltac rd H :=
  lazymatch type of H with
  | bytes_at ?segs ?mm ?A ?bs =>
      let RD := fresh "RD" in
      assert (RD : ov_read_bytes segs mm (wa A) (length bs) = Some bs)
        by (replace (wa A) with (wa (A + 0)) by (f_equal; lia);
            rewrite (bytes_at_read segs mm A bs 0 (length bs) H) by lia;
            change (Z.to_nat 0) with 0%nat; rewrite skipn_O, firstn_all; reflexivity);
      rewrite ?length_le8, ?length_le4 in RD
  end.

Ltac brc :=
  repeat match goal with
  | H : -2^31 <= ?z < 2^31 |- context [sx32 (Z_to_bv 64 ?z)] => rewrite (sx32_s32 z H)
  end;
  repeat match goal with
  | Hx : -2^31 <= ?x < 2^31, Hy : -2^31 <= ?y < 2^31 |- context [bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] =>
      rewrite (eqb_s32 x y Hx Hy)
  | Hx : 0 <= ?x < 2^64 |- context [bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 0)] => rewrite (eqb_u64_0 x Hx)
  end;
  first [ if_true | if_false ].

Ltac run :=
  repeat lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => brc
  | |- evt _ _ (MS _ _ (Z_to_bv 64 118508) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 84264) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
  end.

Ltac mask_eval :=
  unfold Prog.reac_box_catalogue_defect_c.CATALOGUE_DEFECT_MASK;
  repeat match goal with
  | |- context [?x =? ?y] =>
      first [ replace (x =? y) with true by (symmetry; apply Z.eqb_eq; lia)
            | replace (x =? y) with false by (symmetry; apply Z.eqb_neq; lia) ]
  end;
  try match goal with H : ?a = ?b |- context [bool_decide (?a = ?b)] => rewrite (bd_true a b H) end;
  try match goal with H : ?a <> ?b |- context [bool_decide (?a = ?b)] => rewrite (bd_false a b H) end;
  cbn [andb orb].

Ltac align_ok HAL :=
  let HAC := fresh "HAC" in
  if_cases HAC; zify_cond HAC;
  [ exfalso;
    first [ solve [ rewrite ?unsigned_lit_wrap, ?land7_mod8 in HAC; Z.div_mod_to_equations; lia ]
          | match type of HAC with ?T => fail 100 "HAC:" T end ]
  | ].

Theorem reac_box_catalogue_defect_holds : strcmp_contract -> reac_box_catalogue_defect_contract.
Proof.
  intros SC. unfold strcmp_contract in SC.
  unfold reac_box_catalogue_defect_contract, REAC_BOX_CATALOGUE_DEFECT, REAC_BOX_CATALOGUE_DEFECT_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo e i o d I O P sP sd -> -> -> -> He Hi Ho Hd HI HO HP HROW HSP HSD HMI ST LO.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (proj1 ST) as LO0.
  destruct (Z.eq_dec e 0) as [E0|E0].
  - subst e. clear HROW HSP HSD. carve_frame 16%nat ST.
    do 4 zstep. if_true. do 5 zstep.
    release_frame FR ST (bv_unsigned sp). zstep. finish.
  - destruct (HROW E0) as (HF8 & HF16 & HF20 & HAL & DJ). clear HROW.
    assert (UE : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    destruct (Z.eq_dec d 0) as [D0|D0]; [clear HSD HSP|destruct (Z.eq_dec P 0) as [P0|P0]];
      [ | clear HSP; destruct (HSD D0) as (HDS & ND & DJD); clear HSD
        | destruct (HSD D0) as (HDS & ND & DJD); destruct (HSP E0 P0) as (HPS & NP & DJP); clear HSD HSP ];
      (destruct (Z.eq_dec I i) as [EI|EI]; [destruct (Z.eq_dec O o) as [EO|EO]|]);
      carve_frame 16%nat ST; run; align_ok HAL; rd HF8; rd HF16; rd HF20; run.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 84264) _ _ _ _) =>
             mask_eval; release_frame FR ST (bv_unsigned sp); zstep; finish
         | |- evt _ _ (MS _ _ (Z_to_bv 64 118508) _ _ _ _) => idtac
         end.
    all: eapply evt_cut;
      [ eapply SC with (sx := sP) (sy := sd); first [ rewrite unsigned_lit by lia; assumption | assumption ] | ];
      intros ms' (r & x11 & x12 & x13 & -> & HR);
      replace (ret_pc (Z_to_bv 64 84228)) with (Z_to_bv 64 84228) by (apply bv_eq; vm_compute; reflexivity);
      zstep;
      destruct (Z.eq_dec (bv_unsigned r) 0) as [R0|R0];
      [ replace (0 <? bv_unsigned r) with false by (symmetry; apply Z.ltb_ge; lia);
        assert (EQS : sP = sd) by (apply HR; apply bv_eq; rewrite R0; reflexivity)
      | replace (0 <? bv_unsigned r) with true
          by (symmetry; apply Z.ltb_lt; pose proof (bv_unsigned_in_range 64 r); lia);
        assert (NES : sP <> sd) by (intros EQS; apply HR in EQS; apply R0; rewrite EQS; reflexivity) ];
      run; mask_eval; release_frame FR ST (bv_unsigned sp); zstep; finish.
Qed.
