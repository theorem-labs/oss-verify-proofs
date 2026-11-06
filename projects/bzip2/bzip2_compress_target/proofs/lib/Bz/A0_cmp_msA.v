(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCState BzCSortM BzArrD CmpMem CmpCut CmpFsKit0 AsanKit AsanCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmasMs CmpCutMS CmpMsKit.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
Local Ltac lia ::= CmpLiaC.lia_c.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_msV.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Lemma zincr_bound_r : forall ft c j, (forall v, 0 <= v <= 65536 -> 0 <= zget ft v <= c)%Z ->
  forall v, (0 <= v <= 65536)%Z -> (0 <= zget (zincr ft j) v <= c + 1)%Z.
Proof. intros ft c j H v Hv. rewrite zget_zincr. pose proof (H v Hv). destruct (Z.eqb_spec v j) as [->|NE]; [pose proof (H j Hv)|]; lia. Qed.

Section A0MS.
  Variable X : msenv. Variable Y : amenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X. Hypothesis YOK : amenv_ok X Y.
  Notation usp := (bv_unsigned (me_sp X)). Notation P := (am_P Y).
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Notation WAF := [(A2, A2 + ARR2_SIZE); (FT, FT + 262148)]%Z.
  Variables (ra t2 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word).

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
  (* [comment removed for export] *)
  Ltac qz_at AR2 k :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let SO := fresh "SO" in
      assert (SO : store_ok a0segs mm (wa (A2 + (qo + 2 * k))) 2 = true)
        by (eapply (u8arr_storeN_ok a0segs _ A2 _ (qo + 2 * k) 2 _ AR2); [lia| rewrite zb8_length_nat; lia| reflexivity]);
      wstep; sh0_at AR2 (qo + 2 * k)%Z; try clear SO end.
  (* [comment removed for export] *)
  Ltac ftinc_at FTB ftv jj :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let SO := fresh "SO" in
      pose proof (u32arr_store_ok a0segs mm FT _ jj _ FTB ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO;
      wstep; zw32_store FTB jj (zget ftv jj + 1)%Z (rewrite unsigned_lit by lia; reflexivity); try clear SO end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_radix1x4 : forall (q : nat) (i j : Z) (a2 ft : zarr) (c : Z) (x6 x10 x11 x13 x17 : word) (me m : word -> option byte),
    (1 <= q)%nat -> (Z.of_nat q = (i + 1) / 4)%Z -> (3 <= i < n)%Z -> (0 <= j < 65536)%Z -> zbok a2 ->
    (forall v, 0 <= v <= 65536 -> 0 <= zget ft v <= c)%Z -> (0 <= c)%Z -> (c + i + 1 <= n)%Z ->
    u8arr a0segs m A2 (zb8 a2 ARR2_SIZE) -> u32arr a0segs m FT (zw32 ft 65537) -> mem_inv a0segs m ->
    munch WAF me m -> wmono a0segs me m ->
    shzW a0segs WAF me A2 (A2 + ARR2_SIZE) -> shzW a0segs WAF me FT (FT + 262144) ->
    (forall m' (x6' x10' x11' : word), let r := ms_radix1 (4 * q) a2 ft qo i j in
      let a2' := fst (fst r) in let ft' := snd (fst r) in let j' := snd r in
      u8arr a0segs m' A2 (zb8 a2' ARR2_SIZE) -> u32arr a0segs m' FT (zw32 ft' 65537) -> mem_inv a0segs m' ->
      munch WAF me m' -> wmono a0segs me m' ->
      zbok a2' -> (forall v, 0 <= v <= 65536 -> 0 <= zget ft' v <= c + 4 * Z.of_nat q)%Z -> (0 <= j' < 65536)%Z ->
      (forall k, 0 <= k < qo -> zget a2' k = zget a2 k)%Z ->
      evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp (Z_to_bv 64 (j' / 256)) x6' t2 (me_sp X) (Z_to_bv 64 P)
                            x10' x11' (Z_to_bv 64 (i - 4 * Z.of_nat q + 4)) x13 (Z_to_bv 64 (A2 + (qo + 2 * (i - 4 * Z.of_nat q))))
                            (Z_to_bv 64 (qo + 2 * (i - 4 * Z.of_nat q))) (Z_to_bv 64 6) (Z_to_bv 64 j')
                            (Z_to_bv 64 A2) cSB s4 s5 s6 (Z_to_bv 64 FT) s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x97f90) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp (Z_to_bv 64 (j / 256)) x6 t2 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 (Z_to_bv 64 (i + 4)) x13 (Z_to_bv 64 (A2 + (qo + 2 * i))) (Z_to_bv 64 (qo + 2 * i)) (Z_to_bv 64 6) x17
                          (Z_to_bv 64 A2) cSB s4 s5 s6 (Z_to_bv 64 FT) s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x97d58) fc None m (seg_rom a0segs)).
  Proof.
    induction q as [|q IH]; [intros; lia|].
    intros i j a2 ft c x6 x10 x11 x13 x17 me m Hq Hq4 Hi Hj BOK FTC Hc Hci AR2 FTB MI MU WM SH2 SHF K.
    msenv_open XOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (_ & _ & AP2F & _).
    bz_params.
    pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2. pose proof (zw32_length ft 65537 ltac:(lia)) as LF.
    assert (D0 : (0 <= j / 256 < 256)%Z) by (Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    arun. qz_at AR2 i. change (wr16 a2 (qo + 2 * i) 0) with (qwr a2 qo i 0) in AR2.
    set (a2a := qwr a2 qo i 0) in AR2. assert (BOKa : zbok a2a) by (subst a2a; apply zbok_qwr; exact BOK).
    assert (Ea : forall k, (0 <= k < qo)%Z -> zget a2a k = zget a2 k) by (intros; subst a2a; apply zget_qwr_lo; lia).
    (* [comment removed for export] *)
    arun. rd8_at AR2 BOKa i. rewrite (Ea i) by lia. pose proof (BOK i) as B0.
    arun_to 0x97d94%Z. rewrite lor_hb by lia.
    set (j1 := (j / 256 + 256 * zget a2 i)%Z). assert (J1 : (0 <= j1 < 65536)%Z) by (subst j1; lia).
    (* [comment removed for export] *)
    pose proof (FTC j1 ltac:(lia)) as Fj1. arun. rd32_at FTB j1.
    arun. ftinc_at FTB ft j1. change (zset ft j1 (zget ft j1 + 1)) with (zincr ft j1) in FTB.
    set (ft1 := zincr ft j1) in FTB. pose proof (zincr_bound_r ft c j1 FTC : forall v, (0 <= v <= 65536)%Z -> (0 <= zget ft1 v <= c + 1)%Z) as FTC1.
    (* [comment removed for export] *)
    arun. qz_at AR2 (i - 1)%Z. change (wr16 a2a (qo + 2 * (i - 1)) 0) with (qwr a2a qo (i - 1) 0) in AR2.
    set (a2b := qwr a2a qo (i - 1) 0) in AR2. assert (BOKb : zbok a2b) by (subst a2b; apply zbok_qwr; exact BOKa).
    assert (Eb : forall k, (0 <= k < qo)%Z -> zget a2b k = zget a2 k) by (intros; subst a2b; rewrite zget_qwr_lo by lia; apply Ea; lia).
    (* [comment removed for export] *)
    arun. rd8_at AR2 BOKb (i - 1)%Z. rewrite (Eb (i - 1)%Z) by lia. pose proof (BOK (i - 1)%Z) as B1.
    arun_to 0x97df4%Z. rewrite lor_hb4 by lia.
    set (j2 := (zget a2 i + 256 * zget a2 (i - 1))%Z). assert (J2 : (0 <= j2 < 65536)%Z) by (subst j2; lia).
    (* [comment removed for export] *)
    pose proof (FTC1 j2 ltac:(lia)) as Fj2. arun. rd32_at FTB j2.
    arun. ftinc_at FTB ft1 j2. change (zset ft1 j2 (zget ft1 j2 + 1)) with (zincr ft1 j2) in FTB.
    set (ft2 := zincr ft1 j2) in FTB. pose proof (zincr_bound_r ft1 (c + 1)%Z j2 FTC1 : forall v, (0 <= v <= 65536)%Z -> (0 <= zget ft2 v <= c + 1 + 1)%Z) as FTC2.
    (* [comment removed for export] *)
    arun. qz_at AR2 (i - 2)%Z. change (wr16 a2b (qo + 2 * (i - 2)) 0) with (qwr a2b qo (i - 2) 0) in AR2.
    set (a2c := qwr a2b qo (i - 2) 0) in AR2. assert (BOKc : zbok a2c) by (subst a2c; apply zbok_qwr; exact BOKb).
    assert (Ec : forall k, (0 <= k < qo)%Z -> zget a2c k = zget a2 k) by (intros; subst a2c; rewrite zget_qwr_lo by lia; apply Eb; lia).
    (* [comment removed for export] *)
    arun. rd8_at AR2 BOKc (i - 2)%Z. rewrite (Ec (i - 2)%Z) by lia. pose proof (BOK (i - 2)%Z) as B2.
    arun_to 0x97e50%Z. rewrite lor_hb4 by lia.
    set (j3 := (zget a2 (i - 1) + 256 * zget a2 (i - 2))%Z). assert (J3 : (0 <= j3 < 65536)%Z) by (subst j3; lia).
    (* [comment removed for export] *)
    pose proof (FTC2 j3 ltac:(lia)) as Fj3. arun. rd32_at FTB j3.
    arun. ftinc_at FTB ft2 j3. change (zset ft2 j3 (zget ft2 j3 + 1)) with (zincr ft2 j3) in FTB.
    set (ft3 := zincr ft2 j3) in FTB. pose proof (zincr_bound_r ft2 (c + 1 + 1)%Z j3 FTC2 : forall v, (0 <= v <= 65536)%Z -> (0 <= zget ft3 v <= c + 1 + 1 + 1)%Z) as FTC3.
    (* [comment removed for export] *)
    arun. qz_at AR2 (i - 3)%Z. change (wr16 a2c (qo + 2 * (i - 3)) 0) with (qwr a2c qo (i - 3) 0) in AR2.
    set (a2d := qwr a2c qo (i - 3) 0) in AR2. assert (BOKd : zbok a2d) by (subst a2d; apply zbok_qwr; exact BOKc).
    assert (Ed : forall k, (0 <= k < qo)%Z -> zget a2d k = zget a2 k) by (intros; subst a2d; rewrite zget_qwr_lo by lia; apply Ec; lia).
    (* [comment removed for export] *)
    arun. rd8_at AR2 BOKd (i - 3)%Z. rewrite (Ed (i - 3)%Z) by lia. pose proof (BOK (i - 3)%Z) as B3.
    arun_to 0x97ea8%Z. rewrite lor_hb by lia.
    set (j4 := (zget a2 (i - 2) + 256 * zget a2 (i - 3))%Z). assert (J4 : (0 <= j4 < 65536)%Z) by (subst j4; lia).
    (* [comment removed for export] *)
    pose proof (FTC3 j4 ltac:(lia)) as Fj4. arun. rd32_at FTB j4.
    arun. ftinc_at FTB ft3 j4. change (zset ft3 j4 (zget ft3 j4 + 1)) with (zincr ft3 j4) in FTB.
    set (ft4 := zincr ft3 j4) in FTB. pose proof (zincr_bound_r ft3 (c + 1 + 1 + 1)%Z j4 FTC3 : forall v, (0 <= v <= 65536)%Z -> (0 <= zget ft4 v <= c + 1 + 1 + 1 + 1)%Z) as FTC4.
    (* [comment removed for export] *)
    replace (4 * S q)%nat with (S (S (S (S (4 * q)))))%nat in K by lia.
    rewrite (ms_radix1_step4 (4 * q) a2 ft qo i j Hj ltac:(lia) BOK) in K. cbv zeta in K.
    fold j1 in K. fold a2a in K. fold ft1 in K. fold j2 in K. fold a2b in K. fold ft2 in K. fold j3 in K. fold a2c in K. fold ft3 in K.
    fold j4 in K. fold a2d in K. fold ft4 in K.
    replace (Z_to_bv 64 (zget a2 (i - 3))) with (Z_to_bv 64 (j4 / 256)) by (subst j4; rewrite key_div256 by lia; reflexivity).
    (* [comment removed for export] *)
    arun. if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      assert (q = 0)%nat.
      { rewrite Nat2Z.inj_succ in Hq4. assert ((i + 1) / 4 < 2)%Z by (apply Z.div_lt_upper_bound; lia). lia. }
      subst q. change (4 * 0)%nat with 0%nat in K. cbn [ms_radix1 fst snd] in K. change (Z.of_nat 1) with 1%Z in K.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _) end;
        [st_eq| exact AR2| exact FTB| assumption| assumption| assumption| exact BOKd| | exact J4| exact Ed].
      intros v Hv. pose proof (FTC4 v Hv). lia.
    - (* [comment removed for export] *)
      wstep.
      enter_with (IH (i - 4)%Z j4 a2d ft4 (c + 4)%Z _ _ _ x13 _ me);
        [st_eq| lia| | lia| exact J4| exact BOKd| intros v Hv; pose proof (FTC4 v Hv); lia| lia| lia
        | exact AR2| exact FTB| assumption| assumption| assumption| exact SH2| exact SHF| ].
      { rewrite Nat2Z.inj_succ in Hq4. Z.div_mod_to_equations. lia. }
      intros m' x6' x10' x11'. cbv zeta. intros AR2' FTB' MI' MU' WM' BOK' FTC' J' AG'.
      enter_with (K m' x6' x10' x11'); [st_eq| exact AR2'| exact FTB'| exact MI'| exact MU'| exact WM'| exact BOK'| | exact J'|].
      + intros v Hv. pose proof (FTC' v Hv). lia.
      + intros k Hk. rewrite AG' by lia. apply Ed. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_radix1x1 : forall (r : nat) (i j : Z) (a2 ft : zarr) (c : Z) (x5 x6 x12 x13 : word) (me m : word -> option byte),
    (Z.of_nat r = i + 1)%Z -> (0 <= i < n)%Z -> (0 <= j < 65536)%Z -> zbok a2 ->
    (forall v, 0 <= v <= 65536 -> 0 <= zget ft v <= c)%Z -> (0 <= c)%Z -> (c + i + 1 <= n)%Z ->
    u8arr a0segs m A2 (zb8 a2 ARR2_SIZE) -> u32arr a0segs m FT (zw32 ft 65537) -> mem_inv a0segs m ->
    munch WAF me m -> wmono a0segs me m ->
    shzW a0segs WAF me A2 (A2 + ARR2_SIZE) -> shzW a0segs WAF me FT (FT + 262144) ->
    (forall m' (x5' x12' x17' : word), let rr := ms_radix1 r a2 ft qo i j in
      let a2' := fst (fst rr) in let ft' := snd (fst rr) in
      u8arr a0segs m' A2 (zb8 a2' ARR2_SIZE) -> u32arr a0segs m' FT (zw32 ft' 65537) -> mem_inv a0segs m' ->
      munch WAF me m' -> wmono a0segs me m' ->
      zbok a2' -> (forall v, 0 <= v <= 65536 -> 0 <= zget ft' v <= c + Z.of_nat r)%Z ->
      (forall k, 0 <= k < qo -> zget a2' k = zget a2 k)%Z ->
      evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp x5' x6 t2 (me_sp X) (Z_to_bv 64 P)
                            (Z_to_bv 64 (A2 + (qo + 2 * (i - Z.of_nat r)))) (Z_to_bv 64 (A2 + (i - Z.of_nat r))) x12' x13
                            (Z_to_bv 64 (A2 + (qo + 2 * (i - Z.of_nat r)))) (Z_to_bv 64 (A2 + (i - Z.of_nat r))) (Z_to_bv 64 0) x17'
                            (Z_to_bv 64 A2) cSB s4 s5 s6 (Z_to_bv 64 FT) s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x98050) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp x5 x6 t2 (me_sp X) (Z_to_bv 64 P)
                          (Z_to_bv 64 (A2 + (qo + 2 * i))) (Z_to_bv 64 (A2 + i)) x12 x13
                          (Z_to_bv 64 (A2 + (qo + 2 * i))) (Z_to_bv 64 (A2 + i)) (Z_to_bv 64 (i + 1)) (Z_to_bv 64 j)
                          (Z_to_bv 64 A2) cSB s4 s5 s6 (Z_to_bv 64 FT) s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x97fac) fc None m (seg_rom a0segs)).
  Proof.
    induction r as [|r IH]; [intros; lia|].
    intros i j a2 ft c x5 x6 x12 x13 me m Hr Hi Hj BOK FTC Hc Hci AR2 FTB MI MU WM SH2 SHF K.
    msenv_open XOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (_ & _ & AP2F & _).
    bz_params.
    pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2. pose proof (zw32_length ft 65537 ltac:(lia)) as LF.
    assert (D0 : (0 <= j / 256 < 256)%Z) by (Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    arun. qz_at AR2 i. change (wr16 a2 (qo + 2 * i) 0) with (qwr a2 qo i 0) in AR2.
    set (a2a := qwr a2 qo i 0) in AR2. assert (BOKa : zbok a2a) by (subst a2a; apply zbok_qwr; exact BOK).
    assert (Ea : forall k, (0 <= k < qo)%Z -> zget a2a k = zget a2 k) by (intros; subst a2a; apply zget_qwr_lo; lia).
    (* [comment removed for export] *)
    arun. rd8_at AR2 BOKa i. rewrite (Ea i) by lia. pose proof (BOK i) as B0.
    arun_to 0x97fe0%Z. rewrite lor_hb by lia.
    set (j1 := (j / 256 + 256 * zget a2 i)%Z). assert (J1 : (0 <= j1 < 65536)%Z) by (subst j1; lia).
    (* [comment removed for export] *)
    pose proof (FTC j1 ltac:(lia)) as Fj1. arun. rd32_at FTB j1.
    arun. ftinc_at FTB ft j1. change (zset ft j1 (zget ft j1 + 1)) with (zincr ft j1) in FTB.
    set (ft1 := zincr ft j1) in FTB. pose proof (zincr_bound_r ft c j1 FTC : forall v, (0 <= v <= 65536)%Z -> (0 <= zget ft1 v <= c + 1)%Z) as FTC1.
    rewrite (ms_radix1_step r a2 ft qo i j Hj ltac:(lia) BOK) in K. cbv zeta in K. fold j1 in K. fold a2a in K. fold ft1 in K.
    (* [comment removed for export] *)
    arun. if_cases Kc; zify_cond_z Kc.
    - enter_with (IH (i - 1)%Z j1 a2a ft1 (c + 1)%Z _ x6 _ x13 me);
        [st_eq| lia| lia| exact J1| exact BOKa| exact FTC1| lia| lia| exact AR2| exact FTB| assumption| assumption| assumption| exact SH2| exact SHF| ].
      intros m' x5' x12' x17'. cbv zeta. intros AR2' FTB' MI' MU' WM' BOK' FTC' AG'.
      enter_with (K m' x5' x12' x17'); [st_eq| exact AR2'| exact FTB'| exact MI'| exact MU'| exact WM'| exact BOK'| | ].
      + intros v Hv. pose proof (FTC' v Hv). lia.
      + intros k Hk. rewrite AG' by lia. apply Ea. lia.
    - assert (r = 0)%nat by lia. subst r. cbn [ms_radix1 fst snd] in K. change (Z.of_nat 1) with 1%Z in K.
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _) end;
        [st_eq| exact AR2| exact FTB| assumption| assumption| assumption| exact BOKa| | exact Ea].
      intros v Hv. pose proof (FTC1 v Hv). lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_overshoot : forall (r : nat) (i : Z) (a2 : zarr) (x5 x6 x11 x12 x16 x17 : word) (me m : word -> option byte),
    (Z.of_nat r = 34 - i)%Z -> (0 <= i < 34)%Z -> zbok a2 ->
    u8arr a0segs m A2 (zb8 a2 ARR2_SIZE) -> mem_inv a0segs m ->
    munch [(A2, A2 + ARR2_SIZE)]%Z me m -> wmono a0segs me m ->
    shzW a0segs [(A2, A2 + ARR2_SIZE)]%Z me A2 (A2 + ARR2_SIZE) ->
    (forall m' (x11' x12' x16' : word), let a2' := ms_overshoot r a2 qo n i in
      u8arr a0segs m' A2 (zb8 a2' ARR2_SIZE) -> mem_inv a0segs m' ->
      munch [(A2, A2 + ARR2_SIZE)]%Z me m' -> wmono a0segs me m' -> zbok a2' ->
      evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp x5 x6 t2 (me_sp X) (Z_to_bv 64 P)
                            (Z_to_bv 64 (A2 + qo + 2 * n + 68)) x11' x12' (Z_to_bv 64 (A2 + qo + 2 * n + 68))
                            (Z_to_bv 64 34) (Z_to_bv 64 34) x16' x17
                            (Z_to_bv 64 A2) cSB (Z_to_bv 64 (A2 + n)) s5 s6 (Z_to_bv 64 FT) s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x980ec) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp x5 x6 t2 (me_sp X) (Z_to_bv 64 P)
                          (Z_to_bv 64 (A2 + qo + 2 * (n + i))) x11 x12 (Z_to_bv 64 (A2 + qo + 2 * (n + i)))
                          (Z_to_bv 64 i) (Z_to_bv 64 34) x16 x17
                          (Z_to_bv 64 A2) cSB (Z_to_bv 64 (A2 + n)) s5 s6 (Z_to_bv 64 FT) s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x9806c) fc None m (seg_rom a0segs)).
  Proof.
    induction r as [|r IH]; [intros; lia|].
    intros i a2 x5 x6 x11 x12 x16 x17 me m Hr Hi BOK AR2 MI MU WM SH2 K.
    msenv_open XOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (_ & _ & AP2F & _).
    bz_params.
    pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    (* [comment removed for export] *)
    arun. rd8_at AR2 BOK i. pose proof (BOK i) as B0.
    arun.
    assert (SO : store_ok a0segs m (wa (A2 + (n + i))) 1 = true)
      by (eapply (u8arr_storeN_ok a0segs m A2 _ (n + i) 1 _ AR2); [lia| rewrite zb8_length_nat; lia| reflexivity]).
    wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?ad ?bs) _) =>
      pose proof (zb8_write1 a0segs mm A2 a2 ARR2_SIZE (n + i) (Z_to_bv 64 (zget a2 i)) AR2 ltac:(lia)) as ARw; clear AR2;
      change bs with (le1 (Z_to_bv 64 (zget a2 i))); store_done; rename ARw into AR2 end.
    rewrite (unsigned_lit (zget a2 i)) in AR2 by lia. change (wr8 a2 (n + i) (zget a2 i)) with (wr8 a2 (n + i) (rd8 a2 i)) in AR2.
    set (a2a := wr8 a2 (n + i) (rd8 a2 i)) in AR2. assert (BOKa : zbok a2a) by (subst a2a; apply zbok_wr8; exact BOK).
    (* [comment removed for export] *)
    arun. qz_at AR2 (n + i)%Z. change (wr16 a2a (qo + 2 * (n + i)) 0) with (qwr a2a qo (n + i) 0) in AR2.
    set (a2b := qwr a2a qo (n + i) 0) in AR2. assert (BOKb : zbok a2b) by (subst a2b; apply zbok_qwr; exact BOKa).
    rewrite ms_overshoot_S in K. fold a2a in K. fold a2b in K.
    (* [comment removed for export] *)
    arun. if_cases Kc; zify_cond_z Kc.
    - enter_with (IH (i + 1)%Z a2b x5 x6 _ _ _ x17 me); [st_eq| lia| lia| exact BOKb| exact AR2| assumption| assumption| assumption| exact SH2| exact K].
    - assert (r = 0)%nat by lia. subst r. cbn [ms_overshoot] in K.
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _) end;
        [st_eq| exact AR2| assumption| assumption| assumption| exact BOKb].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_accum : forall (r : nat) (i : Z) (ft : zarr) (x14 x15 : word) (x5 x6 x16 x17 s7 : word) (me m : word -> option byte),
    (Z.of_nat r = 65537 - i)%Z -> (1 <= i <= 65536)%Z ->
    (forall v, 0 <= v <= 65536 -> 0 <= zget (ms_accum r ft i) v <= n)%Z -> (forall v, 0 <= zget ft v)%Z ->
    u32arr a0segs m FT (zw32 ft 65537) -> mem_inv a0segs m ->
    munch [(FT, FT + 262148)]%Z me m -> wmono a0segs me m ->
    shpW a0segs [(FT, FT + 262148)]%Z me FT (FT + 262148) ->
    (forall m' (x11' x14' x15' : word), let ft' := ms_accum r ft i in
      u32arr a0segs m' FT (zw32 ft' 65537) -> mem_inv a0segs m' ->
      munch [(FT, FT + 262148)]%Z me m' -> wmono a0segs me m' -> (forall v, 0 <= zget ft' v)%Z ->
      evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp x5 x6 t2 (me_sp X) (Z_to_bv 64 P)
                            (Z_to_bv 64 (FT + 262148)) x11' (Z_to_bv 64 (FT + 262148)) (Z_to_bv 64 0) x14' x15' x16 x17
                            (Z_to_bv 64 A2) cSB s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x98160) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp x5 x6 t2 (me_sp X) (Z_to_bv 64 P)
                          (Z_to_bv 64 (FT + 4 * i)) (Z_to_bv 64 (zget ft (i - 1))) (Z_to_bv 64 (FT + 4 * i)) (Z_to_bv 64 (65537 - i)) x14 x15 x16 x17
                          (Z_to_bv 64 A2) cSB s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x98120) fc None m (seg_rom a0segs)).
  Proof.
    induction r as [|r IH]; [intros; lia|].
    intros i ft x14 x15 x5 x6 x16 x17 s7 me m Hr Hi FIN NNG FTB MI MU WM SHP K.
    msenv_open XOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (_ & _ & AP2F & _).
    pose proof (zw32_length ft 65537 ltac:(lia)) as LF.
    pose proof (FIN i ltac:(lia)) as Fi. rewrite ms_accum_here in Fi. pose proof (NNG i) as N1. pose proof (NNG (i - 1)%Z) as N2.
    (* [comment removed for export] *)
    arun_to 0x98128%Z. ack_rd (FT + 4 * i)%Z 4%Z. ack_merge.
    (* [comment removed for export] *)
    rd32_at FTB i.
    arun.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok a0segs mm FT _ i _ FTB ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO end.
    wstep. zw32_store FTB i (zget ft i + zget ft (i - 1))%Z (rewrite unsigned_lit by lia; f_equal; lia).
    set (ft1 := zset ft i (zget ft i + zget ft (i - 1))) in FTB.
    rewrite ms_accum_S in K, FIN. fold ft1 in K. fold ft1 in FIN.
    assert (NNG1 : forall v, (0 <= zget ft1 v)%Z).
    { intros v. subst ft1. rewrite zget_zset. pose proof (NNG v). destruct (v =? i); lia. }
    (* [comment removed for export] *)
    arun. if_cases Kc; zify_cond_z Kc.
    - enter_with (IH (i + 1)%Z ft1 _ _ x5 x6 x16 x17 s7 me); [st_eq| lia| lia| exact FIN| exact NNG1| exact FTB| assumption| assumption| assumption| exact SHP| exact K].
      cbv delta [mkR]. replace (i + 1 - 1)%Z with i by lia. subst ft1. rewrite zget_zset_same. reflexivity.
    - assert (r = 0)%nat by lia. subst r. cbn [ms_accum] in K.
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _) end;
        [st_eq| exact FTB| assumption| assumption| assumption| exact NNG1].
  Qed.
End A0MS.

End ACeilS1.
