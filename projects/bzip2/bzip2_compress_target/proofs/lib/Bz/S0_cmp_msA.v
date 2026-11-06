(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCState BzCSortM BzArrD CmpMem CmpCut CmpCut0 CmpFsKit0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmasMs CmpCutMS CmpMsKit.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Lemma zincr_bound_r : forall ft c j, (forall v, 0 <= v <= 65536 -> 0 <= zget ft v <= c)%Z ->
  forall v, (0 <= v <= 65536)%Z -> (0 <= zget (zincr ft j) v <= c + 1)%Z.
Proof. intros ft c j H v Hv. rewrite zget_zincr. pose proof (H v Hv). destruct (Z.eqb_spec v j) as [->|NE]; [pose proof (H j Hv)|]; lia. Qed.

Section S0MS.
  Variable X : msenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X.
  Notation usp := (bv_unsigned (me_sp X)). Notation p := (bv_unsigned (me_sp X) - 4928)%Z.
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Variables (ra t0 t1 t2 s0 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word).

  (* [comment removed for export] *)
  Ltac rd8_at AR2 AOK idx :=
    lazymatch type of AR2 with u8arr ?segs ?mm ?A (zb8 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zb8_read1 segs mm A a nn idx _ AR2 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; cbv beta;
      let B := fresh "By" in pose proof (AOK idx) as B;
      rewrite (unsigned_lit8 (zget a idx)) by lia
    end.
  (* [comment removed for export] *)
  Ltac rd32_at FTB idx :=
    lazymatch type of FTB with u32arr ?segs ?mm ?A (zw32 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zw32_read segs mm A a nn idx _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; try rewrite (sx32_of_Z (zget a idx)) by lia
    end.
  (* [comment removed for export] *)
  Ltac sh0_at AR2 off :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?ad ?bs) _) =>
      lazymatch type of AR2 with u8arr ?segs m ?A (zb8 ?a ?nn) =>
        let H := fresh "ARw" in
        pose proof (zb8_write2 segs m A a nn off (Z_to_bv 64 0) AR2 ltac:(lia) ltac:(lia)) as H; clear AR2;
        change bs with (le2 (Z_to_bv 64 0)); store_done; rename H into AR2;
        change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in AR2
      end end.

  Lemma S0_radix1x4 : forall (q : nat) (i j : Z) (a2 ft : zarr) (c : Z) (x12 x15 x16 x17 : word) (me m : word -> option byte),
    (1 <= q)%nat -> (Z.of_nat q = (i + 1) / 4)%Z -> (3 <= i < n)%Z -> (0 <= j < 65536)%Z -> zbok a2 ->
    (forall v, 0 <= v <= 65536 -> 0 <= zget ft v <= c)%Z -> (0 <= c)%Z -> (c + i + 1 <= n)%Z ->
    u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) -> u32arr s0segs m FT (zw32 ft 65537) -> mem_inv s0segs m ->
    munch [(A2, A2 + ARR2_SIZE); (FT, FT + 262148)]%Z me m -> wmono s0segs me m ->
    (forall m' (x16' x17' : word), let r := ms_radix1 (4 * q) a2 ft qo i j in
      let a2' := fst (fst r) in let ft' := snd (fst r) in let j' := snd r in
      u8arr s0segs m' A2 (zb8 a2' ARR2_SIZE) -> u32arr s0segs m' FT (zw32 ft' 65537) -> mem_inv s0segs m' ->
      munch [(A2, A2 + ARR2_SIZE); (FT, FT + 262148)]%Z me m' -> wmono s0segs me m' ->
      zbok a2' -> (forall v, 0 <= v <= 65536 -> 0 <= zget ft' v <= c + 4 * Z.of_nat q)%Z -> (0 <= j' < 65536)%Z ->
      (forall k, 0 <= k < qo -> zget a2' k = zget a2 k)%Z ->
      evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp t0 t1 t2 s0 (Z_to_bv 64 FT)
                            (Z_to_bv 64 (qo + 2 * (i - 4 * Z.of_nat q))) (Z_to_bv 64 6) (Z_to_bv 64 j') (Z_to_bv 64 (j' / 256))
                            (Z_to_bv 64 (i - 4 * Z.of_nat q)) (Z_to_bv 64 (i - 4 * Z.of_nat q + 4)) x16' x17'
                            s2 s3 (Z_to_bv 64 A2) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x19744) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp t0 t1 t2 s0 (Z_to_bv 64 FT)
                          (Z_to_bv 64 (qo + 2 * i)) (Z_to_bv 64 6) x12 (Z_to_bv 64 (j / 256)) (Z_to_bv 64 i) x15 x16 x17
                          s2 s3 (Z_to_bv 64 A2) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x1969c) fc None m (seg_rom s0segs)).
  Proof.
    induction q as [|q IH]; [intros; lia|].
    intros i j a2 ft c x12 x15 x16 x17 me m Hq Hq4 Hi Hj BOK FTC Hc Hci AR2 FTB MI MU WM K.
    msenv_open XOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (_ & _ & AP2F & _).
    bz_params.
    pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2. pose proof (zw32_length ft 65537 ltac:(lia)) as LF.
    assert (D0 : (0 <= j / 256 < 256)%Z) by (Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    assert (SO : store_ok s0segs m (wa (A2 + (qo + 2 * i))) 2 = true)
      by (eapply (u8arr_storeN_ok s0segs m A2 _ (qo + 2 * i) 2 _ AR2); [lia| rewrite zb8_length_nat; lia| reflexivity]).
    wstep. sh0_at AR2 (qo + 2 * i)%Z. change (wr16 a2 (qo + 2 * i) 0) with (qwr a2 qo i 0) in AR2.
    set (a2a := qwr a2 qo i 0) in AR2. assert (BOKa : zbok a2a) by (subst a2a; apply zbok_qwr; exact BOK).
    assert (Ea : forall k, (0 <= k < qo)%Z -> zget a2a k = zget a2 k) by (intros; subst a2a; apply zget_qwr_lo; lia).
    (* [comment removed for export] *)
    rd8_at AR2 BOKa i. rewrite (Ea i) by lia. pose proof (BOK i) as B0.
    wstep. wstep. rewrite lor_hb by lia.
    set (j1 := (j / 256 + 256 * zget a2 i)%Z). assert (J1 : (0 <= j1 < 65536)%Z) by (subst j1; lia).
    wstep. wstep.
    pose proof (FTC j1 ltac:(lia)) as Fj1. rd32_at FTB j1.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SO : store_ok s0segs mm (wa (A2 + (qo + 2 * (i - 1)))) 2 = true)
        by (eapply (u8arr_storeN_ok s0segs _ A2 _ (qo + 2 * (i - 1)) 2 _ AR2); [lia| rewrite zb8_length_nat; lia| reflexivity]) end.
    wstep. sh0_at AR2 (qo + 2 * (i - 1))%Z. change (wr16 a2a (qo + 2 * (i - 1)) 0) with (qwr a2a qo (i - 1) 0) in AR2.
    set (a2b := qwr a2a qo (i - 1) 0) in AR2. assert (BOKb : zbok a2b) by (subst a2b; apply zbok_qwr; exact BOKa).
    assert (Eb : forall k, (0 <= k < qo)%Z -> zget a2b k = zget a2 k) by (intros; subst a2b; rewrite zget_qwr_lo by lia; apply Ea; lia).
    wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm FT _ j1 _ FTB ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO end.
    wstep. zw32_store FTB j1 (zget ft j1 + 1)%Z (rewrite unsigned_lit by lia; reflexivity).
    change (zset ft j1 (zget ft j1 + 1)) with (zincr ft j1) in FTB.
    set (ft1 := zincr ft j1) in FTB. pose proof (zincr_bound_r ft c j1 FTC : forall v, (0 <= v <= 65536)%Z -> (0 <= zget ft1 v <= c + 1)%Z) as FTC1.
    (* [comment removed for export] *)
    rd8_at AR2 BOKb (i - 1)%Z. rewrite (Eb (i - 1)%Z) by lia. pose proof (BOK (i - 1)%Z) as B1.
    wstep. wstep. wstep. rewrite lor_hb4 by lia.
    set (j2 := (zget a2 i + 256 * zget a2 (i - 1))%Z). assert (J2 : (0 <= j2 < 65536)%Z) by (subst j2; lia).
    wstep.
    pose proof (FTC1 j2 ltac:(lia)) as Fj2. rd32_at FTB j2.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SO : store_ok s0segs mm (wa (A2 + (qo + 2 * (i - 2)))) 2 = true)
        by (eapply (u8arr_storeN_ok s0segs _ A2 _ (qo + 2 * (i - 2)) 2 _ AR2); [lia| rewrite zb8_length_nat; lia| reflexivity]) end.
    wstep. sh0_at AR2 (qo + 2 * (i - 2))%Z. change (wr16 a2b (qo + 2 * (i - 2)) 0) with (qwr a2b qo (i - 2) 0) in AR2.
    set (a2c := qwr a2b qo (i - 2) 0) in AR2. assert (BOKc : zbok a2c) by (subst a2c; apply zbok_qwr; exact BOKb).
    assert (Ec : forall k, (0 <= k < qo)%Z -> zget a2c k = zget a2 k) by (intros; subst a2c; rewrite zget_qwr_lo by lia; apply Eb; lia).
    wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm FT _ j2 _ FTB ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO end.
    wstep. zw32_store FTB j2 (zget ft1 j2 + 1)%Z (rewrite unsigned_lit by lia; reflexivity).
    change (zset ft1 j2 (zget ft1 j2 + 1)) with (zincr ft1 j2) in FTB.
    set (ft2 := zincr ft1 j2) in FTB. pose proof (zincr_bound_r ft1 (c + 1)%Z j2 FTC1 : forall v, (0 <= v <= 65536)%Z -> (0 <= zget ft2 v <= c + 1 + 1)%Z) as FTC2.
    (* [comment removed for export] *)
    rd8_at AR2 BOKc (i - 2)%Z. rewrite (Ec (i - 2)%Z) by lia. pose proof (BOK (i - 2)%Z) as B2.
    wstep. wstep. wstep. rewrite lor_hb4 by lia.
    set (j3 := (zget a2 (i - 1) + 256 * zget a2 (i - 2))%Z). assert (J3 : (0 <= j3 < 65536)%Z) by (subst j3; lia).
    wstep.
    pose proof (FTC2 j3 ltac:(lia)) as Fj3. rd32_at FTB j3.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SO : store_ok s0segs mm (wa (A2 + (qo + 2 * (i - 3)))) 2 = true)
        by (eapply (u8arr_storeN_ok s0segs _ A2 _ (qo + 2 * (i - 3)) 2 _ AR2); [lia| rewrite zb8_length_nat; lia| reflexivity]) end.
    wstep. sh0_at AR2 (qo + 2 * (i - 3))%Z. change (wr16 a2c (qo + 2 * (i - 3)) 0) with (qwr a2c qo (i - 3) 0) in AR2.
    set (a2d := qwr a2c qo (i - 3) 0) in AR2. assert (BOKd : zbok a2d) by (subst a2d; apply zbok_qwr; exact BOKc).
    assert (Ed : forall k, (0 <= k < qo)%Z -> zget a2d k = zget a2 k) by (intros; subst a2d; rewrite zget_qwr_lo by lia; apply Ec; lia).
    wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm FT _ j3 _ FTB ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO end.
    wstep. zw32_store FTB j3 (zget ft2 j3 + 1)%Z (rewrite unsigned_lit by lia; reflexivity).
    change (zset ft2 j3 (zget ft2 j3 + 1)) with (zincr ft2 j3) in FTB.
    set (ft3 := zincr ft2 j3) in FTB. pose proof (zincr_bound_r ft2 (c + 1 + 1)%Z j3 FTC2 : forall v, (0 <= v <= 65536)%Z -> (0 <= zget ft3 v <= c + 1 + 1 + 1)%Z) as FTC3.
    (* [comment removed for export] *)
    rd8_at AR2 BOKd (i - 3)%Z. rewrite (Ed (i - 3)%Z) by lia. pose proof (BOK (i - 3)%Z) as B3.
    wstep. wstep. rewrite lor_hb by lia.
    set (j4 := (zget a2 (i - 2) + 256 * zget a2 (i - 3))%Z). assert (J4 : (0 <= j4 < 65536)%Z) by (subst j4; lia).
    wstep. wstep.
    pose proof (FTC3 j4 ltac:(lia)) as Fj4. rd32_at FTB j4.
    (* [comment removed for export] *)
    wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm FT _ j4 _ FTB ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO end.
    wstep. zw32_store FTB j4 (zget ft3 j4 + 1)%Z (rewrite unsigned_lit by lia; reflexivity).
    change (zset ft3 j4 (zget ft3 j4 + 1)) with (zincr ft3 j4) in FTB.
    set (ft4 := zincr ft3 j4) in FTB. pose proof (zincr_bound_r ft3 (c + 1 + 1 + 1)%Z j4 FTC3 : forall v, (0 <= v <= 65536)%Z -> (0 <= zget ft4 v <= c + 1 + 1 + 1 + 1)%Z) as FTC4.
    wstep.
    (* [comment removed for export] *)
    replace (4 * S q)%nat with (S (S (S (S (4 * q)))))%nat in K by lia.
    rewrite (ms_radix1_step4 (4 * q) a2 ft qo i j Hj ltac:(lia) BOK) in K. cbv zeta in K.
    fold j1 in K. fold a2a in K. fold ft1 in K. fold j2 in K. fold a2b in K. fold ft2 in K. fold j3 in K. fold a2c in K. fold ft3 in K.
    fold j4 in K. fold a2d in K. fold ft4 in K.
    replace (Z_to_bv 64 (zget a2 (i - 3))) with (Z_to_bv 64 (j4 / 256)) by (subst j4; rewrite key_div256 by lia; reflexivity).
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      enter_with (IH (i - 4)%Z j4 a2d ft4 (c + 4)%Z (Z_to_bv 64 j4) (Z_to_bv 64 i) _ _ me);
        [st_eq| lia| | lia| exact J4| exact BOKd| intros v Hv; pose proof (FTC4 v Hv); lia| lia| lia
        | exact AR2| exact FTB| assumption| assumption| assumption| ].
      { rewrite Nat2Z.inj_succ in Hq4. Z.div_mod_to_equations. lia. }
      intros m' x16' x17'. cbv zeta. intros AR2' FTB' MI' MU' WM' BOK' FTC' J' AG'.
      enter_with (K m' x16' x17'); [st_eq| exact AR2'| exact FTB'| exact MI'| exact MU'| exact WM'| exact BOK'| | exact J'|].
      + intros v Hv. pose proof (FTC' v Hv). lia.
      + intros k Hk. rewrite AG' by lia. apply Ed. lia.
    - (* [comment removed for export] *)
      assert (q = 0)%nat.
      { rewrite Nat2Z.inj_succ in Hq4. assert ((i + 1) / 4 < 2)%Z by (apply Z.div_lt_upper_bound; lia). lia. }
      subst q. change (4 * 0)%nat with 0%nat in K. cbn [ms_radix1 fst snd] in K. change (Z.of_nat 1) with 1%Z in K.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _) end;
        [st_eq| exact AR2| exact FTB| assumption| assumption| assumption| exact BOKd| | exact J4| exact Ed].
      intros v Hv. pose proof (FTC4 v Hv). lia.
  Time Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_radix1x1 : forall (x16 x17 : word) (r : nat) (i j : Z) (a2 ft : zarr) (c : Z) (x14 x15 : word) (me m : word -> option byte),
    (Z.of_nat r = i + 1)%Z -> (0 <= i < n)%Z -> (0 <= j < 65536)%Z -> zbok a2 ->
    (forall v, 0 <= v <= 65536 -> 0 <= zget ft v <= c)%Z -> (0 <= c)%Z -> (c + i + 1 <= n)%Z ->
    u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) -> u32arr s0segs m FT (zw32 ft 65537) -> mem_inv s0segs m ->
    munch [(A2, A2 + ARR2_SIZE); (FT, FT + 262148)]%Z me m -> wmono s0segs me m ->
    (forall m' (x12' x14' x15' : word), let rr := ms_radix1 r a2 ft qo i j in
      let a2' := fst (fst rr) in let ft' := snd (fst rr) in
      u8arr s0segs m' A2 (zb8 a2' ARR2_SIZE) -> u32arr s0segs m' FT (zw32 ft' 65537) -> mem_inv s0segs m' ->
      munch [(A2, A2 + ARR2_SIZE); (FT, FT + 262148)]%Z me m' -> wmono s0segs me m' ->
      zbok a2' -> (forall v, 0 <= v <= 65536 -> 0 <= zget ft' v <= c + Z.of_nat r)%Z ->
      (forall k, 0 <= k < qo -> zget a2' k = zget a2 k)%Z ->
      evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp t0 t1 t2 s0 (Z_to_bv 64 FT)
                            (Z_to_bv 64 (A2 + (qo + 2 * (i - Z.of_nat r)))) (Z_to_bv 64 (A2 + (i - Z.of_nat r))) x12' (Z_to_bv 64 0)
                            x14' x15' x16 x17
                            s2 s3 (Z_to_bv 64 A2) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x19794) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp t0 t1 t2 s0 (Z_to_bv 64 FT)
                          (Z_to_bv 64 (A2 + (qo + 2 * i))) (Z_to_bv 64 (A2 + i)) (Z_to_bv 64 j) (Z_to_bv 64 (i + 1)) x14 x15 x16 x17
                          s2 s3 (Z_to_bv 64 A2) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x1975c) fc None m (seg_rom s0segs)).
  Proof.
    intros x16 x17. induction r as [|r IH]; [intros; lia|].
    intros i j a2 ft c x14 x15 me m Hr Hi Hj BOK FTC Hc Hci AR2 FTB MI MU WM K.
    msenv_open XOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (_ & _ & AP2F & _).
    bz_params.
    pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2. pose proof (zw32_length ft 65537 ltac:(lia)) as LF.
    assert (D0 : (0 <= j / 256 < 256)%Z) by (Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    assert (SO : store_ok s0segs m (wa (A2 + (qo + 2 * i))) 2 = true)
      by (eapply (u8arr_storeN_ok s0segs m A2 _ (qo + 2 * i) 2 _ AR2); [lia| rewrite zb8_length_nat; lia| reflexivity]).
    wstep. sh0_at AR2 (qo + 2 * i)%Z. change (wr16 a2 (qo + 2 * i) 0) with (qwr a2 qo i 0) in AR2.
    set (a2a := qwr a2 qo i 0) in AR2. assert (BOKa : zbok a2a) by (subst a2a; apply zbok_qwr; exact BOK).
    assert (Ea : forall k, (0 <= k < qo)%Z -> zget a2a k = zget a2 k) by (intros; subst a2a; apply zget_qwr_lo; lia).
    (* [comment removed for export] *)
    rd8_at AR2 BOKa i. rewrite (Ea i) by lia. pose proof (BOK i) as B0.
    wstep. wstep. wstep. rewrite lor_hb by lia.
    set (j1 := (j / 256 + 256 * zget a2 i)%Z). assert (J1 : (0 <= j1 < 65536)%Z) by (subst j1; lia).
    wstep. wstep.
    pose proof (FTC j1 ltac:(lia)) as Fj1. rd32_at FTB j1.
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm FT _ j1 _ FTB ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO end.
    wstep. zw32_store FTB j1 (zget ft j1 + 1)%Z (rewrite unsigned_lit by lia; reflexivity).
    change (zset ft j1 (zget ft j1 + 1)) with (zincr ft j1) in FTB.
    set (ft1 := zincr ft j1) in FTB. pose proof (zincr_bound_r ft c j1 FTC : forall v, (0 <= v <= 65536)%Z -> (0 <= zget ft1 v <= c + 1)%Z) as FTC1.
    wstep.
    rewrite (ms_radix1_step r a2 ft qo i j Hj ltac:(lia) BOK) in K. cbv zeta in K. fold j1 in K. fold a2a in K. fold ft1 in K.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - enter_with (IH (i - 1)%Z j1 a2a ft1 (c + 1)%Z _ _ me);
        [st_eq| lia| lia| exact J1| exact BOKa| exact FTC1| lia| lia| exact AR2| exact FTB| assumption| assumption| assumption| ].
      intros m' x12' x14' x15'. cbv zeta. intros AR2' FTB' MI' MU' WM' BOK' FTC' AG'.
      enter_with (K m' x12' x14' x15'); [st_eq| exact AR2'| exact FTB'| exact MI'| exact MU'| exact WM'| exact BOK'| | ].
      + intros v Hv. pose proof (FTC' v Hv). lia.
      + intros k Hk. rewrite AG' by lia. apply Ea. lia.
    - assert (r = 0)%nat by lia. subst r. cbn [ms_radix1 fst snd] in K. change (Z.of_nat 1) with 1%Z in K.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _) end;
        [st_eq| exact AR2| exact FTB| assumption| assumption| assumption| exact BOKa| | exact Ea].
      intros v Hv. pose proof (FTC1 v Hv). lia.
  Time Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_overshoot : forall (x14 x15 x16 x17 : word) (r : nat) (i : Z) (a2 : zarr) (x13 : word) (me m : word -> option byte),
    (Z.of_nat r = 34 - i)%Z -> (0 <= i < 34)%Z -> zbok a2 ->
    u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) -> mem_inv s0segs m ->
    munch [(A2, A2 + ARR2_SIZE)]%Z me m -> wmono s0segs me m ->
    (forall m' (x13' : word), let a2' := ms_overshoot r a2 qo n i in
      u8arr s0segs m' A2 (zb8 a2' ARR2_SIZE) -> mem_inv s0segs m' ->
      munch [(A2, A2 + ARR2_SIZE)]%Z me m' -> wmono s0segs me m' -> zbok a2' ->
      evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp t0 t1 t2 s0 (Z_to_bv 64 FT)
                            (Z_to_bv 64 (A2 + qo + 2 * n + 68)) (Z_to_bv 64 (A2 + qo + 2 * n + 68)) (Z_to_bv 64 (A2 + 34)) x13'
                            x14 x15 x16 x17
                            s2 (Z_to_bv 64 (A2 + n + 34)) (Z_to_bv 64 A2) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x197c8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp t0 t1 t2 s0 (Z_to_bv 64 FT)
                          (Z_to_bv 64 (A2 + qo + 2 * (n + i))) (Z_to_bv 64 (A2 + qo + 2 * n + 68)) (Z_to_bv 64 (A2 + i)) x13
                          x14 x15 x16 x17
                          s2 (Z_to_bv 64 (A2 + n + i)) (Z_to_bv 64 A2) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x197ac) fc None m (seg_rom s0segs)).
  Proof.
    intros x14 x15 x16 x17. induction r as [|r IH]; [intros; lia|].
    intros i a2 x13 me m Hr Hi BOK AR2 MI MU WM K.
    msenv_open XOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (_ & _ & AP2F & _).
    bz_params.
    pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    (* [comment removed for export] *)
    rd8_at AR2 BOK i. pose proof (BOK i) as B0.
    wstep.
    assert (SO : store_ok s0segs m (wa (A2 + (n + i))) 1 = true)
      by (eapply (u8arr_storeN_ok s0segs m A2 _ (n + i) 1 _ AR2); [lia| rewrite zb8_length_nat; lia| reflexivity]).
    wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?ad ?bs) _) =>
      pose proof (zb8_write1 s0segs mm A2 a2 ARR2_SIZE (n + i) (Z_to_bv 64 (zget a2 i)) AR2 ltac:(lia)) as ARw; clear AR2;
      change bs with (le1 (Z_to_bv 64 (zget a2 i))); store_done; rename ARw into AR2 end.
    rewrite (unsigned_lit (zget a2 i)) in AR2 by lia. change (wr8 a2 (n + i) (zget a2 i)) with (wr8 a2 (n + i) (rd8 a2 i)) in AR2.
    set (a2a := wr8 a2 (n + i) (rd8 a2 i)) in AR2. assert (BOKa : zbok a2a) by (subst a2a; apply zbok_wr8; exact BOK).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SO2 : store_ok s0segs mm (wa (A2 + (qo + 2 * (n + i)))) 2 = true)
        by (eapply (u8arr_storeN_ok s0segs _ A2 _ (qo + 2 * (n + i)) 2 _ AR2); [lia| rewrite zb8_length_nat; lia| reflexivity]) end.
    wstep. sh0_at AR2 (qo + 2 * (n + i))%Z. change (wr16 a2a (qo + 2 * (n + i)) 0) with (qwr a2a qo (n + i) 0) in AR2.
    set (a2b := qwr a2a qo (n + i) 0) in AR2. assert (BOKb : zbok a2b) by (subst a2b; apply zbok_qwr; exact BOKa).
    (* [comment removed for export] *)
    wstep. wstep.
    rewrite ms_overshoot_S in K. fold a2a in K. fold a2b in K.
    wstep; if_cases Kc; zify_cond_z Kc.
    - enter_with (IH (i + 1)%Z a2b _ me); [st_eq| lia| lia| exact BOKb| exact AR2| assumption| assumption| assumption| exact K].
    - assert (r = 0)%nat by lia. subst r. cbn [ms_overshoot] in K.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _) end;
        [st_eq| exact AR2| assumption| assumption| assumption| exact BOKb].
  Time Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_accum : forall (x14 x15 x16 x17 x19 : word) (r : nat) (i : Z) (ft : zarr) (x13 : word) (me m : word -> option byte),
    (Z.of_nat r = 65537 - i)%Z -> (1 <= i <= 65536)%Z ->
    (forall v, 0 <= v <= 65536 -> 0 <= zget (ms_accum r ft i) v <= n)%Z -> (forall v, 0 <= zget ft v)%Z ->
    u32arr s0segs m FT (zw32 ft 65537) -> mem_inv s0segs m ->
    munch [(FT, FT + 262148)]%Z me m -> wmono s0segs me m ->
    (forall m' (x10' x13' : word), let ft' := ms_accum r ft i in
      u32arr s0segs m' FT (zw32 ft' 65537) -> mem_inv s0segs m' ->
      munch [(FT, FT + 262148)]%Z me m' -> wmono s0segs me m' -> (forall v, 0 <= zget ft' v)%Z ->
      evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp t0 t1 t2 s0 (Z_to_bv 64 FT)
                            x10' (Z_to_bv 64 (FT + 262148)) (Z_to_bv 64 (FT + 262148)) x13'
                            x14 x15 x16 x17
                            s2 x19 (Z_to_bv 64 A2) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x197f8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp t0 t1 t2 s0 (Z_to_bv 64 FT)
                          (Z_to_bv 64 (zget ft (i - 1))) (Z_to_bv 64 (FT + 4 * i)) (Z_to_bv 64 (FT + 262148)) x13
                          x14 x15 x16 x17
                          s2 x19 (Z_to_bv 64 A2) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x197e4) fc None m (seg_rom s0segs)).
  Proof.
    intros x14 x15 x16 x17 x19. induction r as [|r IH]; [intros; lia|].
    intros i ft x13 me m Hr Hi FIN NNG FTB MI MU WM K.
    msenv_open XOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (_ & _ & AP2F & _).
    pose proof (zw32_length ft 65537 ltac:(lia)) as LF.
    pose proof (FIN i ltac:(lia)) as Fi. rewrite ms_accum_here in Fi. pose proof (NNG i) as N1. pose proof (NNG (i - 1)%Z) as N2.
    (* [comment removed for export] *)
    rd32_at FTB i.
    wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm FT _ i _ FTB ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO end.
    wstep. zw32_store FTB i (zget ft i + zget ft (i - 1))%Z (rewrite unsigned_lit by lia; f_equal; lia).
    set (ft1 := zset ft i (zget ft i + zget ft (i - 1))) in FTB.
    wstep.
    rewrite ms_accum_S in K, FIN. fold ft1 in K. fold ft1 in FIN.
    assert (NNG1 : forall v, (0 <= zget ft1 v)%Z).
    { intros v. subst ft1. rewrite zget_zset. pose proof (NNG v). destruct (v =? i); lia. }
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - enter_with (IH (i + 1)%Z ft1 _ me); [st_eq| lia| lia| exact FIN| exact NNG1| exact FTB| assumption| assumption| assumption| exact K].
      cbv delta [mkR]. replace (i + 1 - 1)%Z with i by lia. subst ft1. rewrite zget_zset_same. reflexivity.
    - assert (r = 0)%nat by lia. subst r. cbn [ms_accum] in K.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _) end;
        [st_eq| exact FTB| assumption| assumption| assumption| exact NNG1].
  Time Qed.
End S0MS.

End ACeilS1.
