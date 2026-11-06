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
Local Ltac AsanKit.a_norm ::= rewrite ?sll48_srl56, ?sll48_srl46.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section A0MS.
  Variable X : msenv. Variable Y : amenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X. Hypothesis YOK : amenv_ok X Y.
  Notation usp := (bv_unsigned (me_sp X)). Notation P := (am_P Y).
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Notation W1F := [(A1, A1 + ARR1_SIZE); (FT, FT + 262148)]%Z.
  Variables (ra t0 t1 t2 a6 a7 s4 s5 s6 s9 s10 s11 t4 t5 t6 : word).

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
  Ltac sw_ptr AR1 j :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?ad (le4 ?w)) _) =>
      lazymatch type of AR1 with u8arr ?segs m ?A (zb8 ?a ?nn) =>
        let H := fresh "ARw" in
        pose proof (zb8_write4 segs m A a nn j w AR1 ltac:(lia) ltac:(lia)) as H; clear AR1; store_done; rename H into AR1
      end end.
  (* [comment removed for export] *)
  Ltac ftdec_at FTB ftv ky :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let SO := fresh "SO" in
      pose proof (u32arr_store_ok a0segs mm FT _ ky _ FTB ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO;
      wstep; zw32_store FTB ky (zget ftv ky - 1)%Z (rewrite unsigned_lit by lia; reflexivity); try clear SO end.
  (* [comment removed for export] *)
  Ltac ptr_at AR1 jj :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let SO := fresh "SO" in
      assert (SO : store_ok a0segs mm (wa (A1 + 4 * jj)) 4 = true)
        by (eapply (u8arr_storeN_ok a0segs _ A1 _ (4 * jj) 4 _ AR1); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]);
      wstep; sw_ptr AR1 jj; try clear SO; rewrite unsigned_lit in AR1 by lia end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_radix2x4 : forall (q : nat) (i s : Z) (a1 ft : zarr) (a2 : zarr) (x10 x13 x15 : word) (me m : word -> option byte),
    (1 <= q)%nat -> (Z.of_nat q = (i + 1) / 4)%Z -> (3 <= i < n)%Z -> (0 <= s < 65536)%Z -> zbok a2 ->
    (forall v, 0 <= v <= 65536 -> 0 <= zget ft v <= n)%Z -> r2ok n (Z.to_nat (i + 1)) a1 a2 ft i s ->
    u8arr a0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr a0segs m A2 (zb8 a2 ARR2_SIZE) -> u32arr a0segs m FT (zw32 ft 65537) -> mem_inv a0segs m ->
    munch W1F me m -> wmono a0segs me m ->
    shzW a0segs W1F me A1 (A1 + ARR1_SIZE) -> shzW a0segs W1F me A2 (A2 + ARR2_SIZE) -> shzW a0segs W1F me FT (FT + 262144) ->
    (forall m' (x10' x13' x15' : word), let rr := ms_radix2 (4 * q) a1 a2 ft i s in
      let a1' := fst (fst rr) in let ft' := snd (fst rr) in let s' := snd rr in
      u8arr a0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr a0segs m' A2 (zb8 a2 ARR2_SIZE) -> u32arr a0segs m' FT (zw32 ft' 65537) -> mem_inv a0segs m' ->
      munch W1F me m' -> wmono a0segs me m' ->
      (forall v, 0 <= v <= 65536 -> 0 <= zget ft' v <= n)%Z -> (0 <= s' < 65536)%Z -> r2ok n (Z.to_nat (i + 1) - 4 * q) a1' a2 ft' (i - 4 * Z.of_nat q) s' ->
      evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (me_sp X) (Z_to_bv 64 P)
                            x10' (Z_to_bv 64 (i - 4 * Z.of_nat q - 1)) (Z_to_bv 64 6) x13' (Z_to_bv 64 s') x15' a6 a7
                            (Z_to_bv 64 A2) cSB s4 s5 s6 (Z_to_bv 64 FT) (Z_to_bv 64 (i - 4 * Z.of_nat q + 4)) s9 s10 s11 (Z_to_bv 64 A1) t4 t5 t6)
                       F (Z_to_bv 64 0x983f8) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (me_sp X) (Z_to_bv 64 P)
                          x10 (Z_to_bv 64 (i - 1)) (Z_to_bv 64 6) x13 (Z_to_bv 64 s) x15 a6 a7
                          (Z_to_bv 64 A2) cSB s4 s5 s6 (Z_to_bv 64 FT) (Z_to_bv 64 (i + 4)) s9 s10 s11 (Z_to_bv 64 A1) t4 t5 t6)
                     F (Z_to_bv 64 0x98184) fc None m (seg_rom a0segs)).
  Proof.
    induction q as [|q IH]; [intros; lia|].
    intros i s a1 ft a2 x10 x13 x15 me m Hq Hq4 Hi Hs BOK FTN RB AR1 AR2 FTB MI MU WM SH1 SH2 SHF K.
    msenv_open XOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    bz_params.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2. pose proof (zw32_length ft 65537 ltac:(lia)) as LF.
    assert (D0 : (0 <= s / 256 < 256)%Z) by (Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    arun. rd8_at AR2 BOK i. pose proof (BOK i) as B0.
    arun_to 0x981b0%Z. rewrite lor_hb by lia.
    set (ky1 := (s / 256 + 256 * zget a2 i)%Z). assert (KY1 : (0 <= ky1 < 65536)%Z) by (subst ky1; lia).
    replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) in RB by lia.
    pose proof (r2ok_here n _ a1 a2 ft i s RB) as R1. fold ky1 in R1. pose proof (FTN ky1 ltac:(lia)) as F1.
    pose proof (r2ok_shift n _ a1 a2 ft i s Hs BOK RB) as RB1. cbv zeta in RB1. fold ky1 in RB1.
    (* [comment removed for export] *)
    arun. rd32_at FTB ky1.
    arun. ftdec_at FTB ft ky1.
    set (j1 := (zget ft ky1 - 1)%Z) in FTB, RB1. set (ft1 := zset ft ky1 j1) in FTB, RB1.
    assert (FTN1 : forall v, (0 <= v <= 65536)%Z -> (0 <= zget ft1 v <= n)%Z) by (intros v Hv; subst ft1 j1; rewrite zget_zset; pose proof (FTN v Hv); destruct (v =? ky1); lia).
    (* [comment removed for export] *)
    arun. ptr_at AR1 j1. replace (i - 1 + 1)%Z with i in AR1 by lia.
    set (a1a := wr32 a1 j1 i) in AR1, RB1.
    (* [comment removed for export] *)
    assert (D1 : (0 <= ky1 / 256 < 256)%Z) by (Z.div_mod_to_equations; lia).
    arun. rd8_at AR2 BOK (i - 1)%Z. pose proof (BOK (i - 1)%Z) as B1.
    arun_to 0x9821c%Z. rewrite lor_hb by lia.
    set (ky2 := (zget a2 i + 256 * zget a2 (i - 1))%Z). assert (KY2 : (0 <= ky2 < 65536)%Z) by (subst ky2; lia).
    assert (Eky2 : (ky1 / 256 + 256 * zget a2 (i - 1))%Z = ky2) by (subst ky1 ky2; rewrite key_div256 by lia; reflexivity).
    rewrite Eky2.
    replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) in RB1 by lia.
    pose proof (r2ok_here n _ a1a a2 ft1 (i - 1) ky1 RB1) as R2. rewrite Eky2 in R2. pose proof (FTN1 ky2 ltac:(lia)) as F2.
    pose proof (r2ok_shift n _ a1a a2 ft1 (i - 1) ky1 KY1 BOK RB1) as RB2. cbv zeta in RB2. rewrite Eky2 in RB2.
    replace (i - 1 - 1)%Z with (i - 2)%Z in RB2 by lia. clear RB1.
    arun. rd32_at FTB ky2.
    arun. ftdec_at FTB ft1 ky2.
    set (j2 := (zget ft1 ky2 - 1)%Z) in FTB, RB2. set (ft2 := zset ft1 ky2 j2) in FTB, RB2.
    assert (FTN2 : forall v, (0 <= v <= 65536)%Z -> (0 <= zget ft2 v <= n)%Z) by (intros v Hv; subst ft2 j2; rewrite zget_zset; pose proof (FTN1 v Hv); destruct (v =? ky2); lia).
    (* [comment removed for export] *)
    arun. ptr_at AR1 j2.
    set (a1b := wr32 a1a j2 (i - 1)) in AR1, RB2.
    (* [comment removed for export] *)
    assert (D2 : (0 <= ky2 / 256 < 256)%Z) by (Z.div_mod_to_equations; lia).
    arun. rd8_at AR2 BOK (i - 2)%Z. pose proof (BOK (i - 2)%Z) as B2.
    arun_to 0x98284%Z. rewrite lor_hb by lia.
    set (ky3 := (zget a2 (i - 1) + 256 * zget a2 (i - 2))%Z). assert (KY3 : (0 <= ky3 < 65536)%Z) by (subst ky3; lia).
    assert (Eky3 : (ky2 / 256 + 256 * zget a2 (i - 2))%Z = ky3) by (subst ky2 ky3; rewrite key_div256 by lia; reflexivity).
    rewrite Eky3.
    replace (Z.to_nat (i - 1)) with (S (Z.to_nat (i - 2))) in RB2 by lia.
    pose proof (r2ok_here n _ a1b a2 ft2 (i - 2) ky2 RB2) as R3. rewrite Eky3 in R3. pose proof (FTN2 ky3 ltac:(lia)) as F3.
    pose proof (r2ok_shift n _ a1b a2 ft2 (i - 2) ky2 KY2 BOK RB2) as RB3. cbv zeta in RB3. rewrite Eky3 in RB3.
    replace (i - 2 - 1)%Z with (i - 3)%Z in RB3 by lia. clear RB2.
    arun. rd32_at FTB ky3.
    arun. ftdec_at FTB ft2 ky3.
    set (j3 := (zget ft2 ky3 - 1)%Z) in FTB, RB3. set (ft3 := zset ft2 ky3 j3) in FTB, RB3.
    assert (FTN3 : forall v, (0 <= v <= 65536)%Z -> (0 <= zget ft3 v <= n)%Z) by (intros v Hv; subst ft3 j3; rewrite zget_zset; pose proof (FTN2 v Hv); destruct (v =? ky3); lia).
    (* [comment removed for export] *)
    arun. ptr_at AR1 j3. replace (i - 1 + -1)%Z with (i - 2)%Z in AR1 by lia.
    set (a1c := wr32 a1b j3 (i - 2)) in AR1, RB3.
    (* [comment removed for export] *)
    assert (D3 : (0 <= ky3 / 256 < 256)%Z) by (Z.div_mod_to_equations; lia).
    arun. rd8_at AR2 BOK (i - 3)%Z. pose proof (BOK (i - 3)%Z) as B3.
    arun_to 0x982f0%Z. rewrite lor_hb by lia.
    set (ky4 := (zget a2 (i - 2) + 256 * zget a2 (i - 3))%Z). assert (KY4 : (0 <= ky4 < 65536)%Z) by (subst ky4; lia).
    assert (Eky4 : (ky3 / 256 + 256 * zget a2 (i - 3))%Z = ky4) by (subst ky3 ky4; rewrite key_div256 by lia; reflexivity).
    rewrite Eky4.
    replace (Z.to_nat (i - 2)) with (S (Z.to_nat (i - 3))) in RB3 by lia.
    pose proof (r2ok_here n _ a1c a2 ft3 (i - 3) ky3 RB3) as R4. rewrite Eky4 in R4. pose proof (FTN3 ky4 ltac:(lia)) as F4.
    pose proof (r2ok_shift n _ a1c a2 ft3 (i - 3) ky3 KY3 BOK RB3) as RB4. cbv zeta in RB4. rewrite Eky4 in RB4.
    replace (i - 3 - 1)%Z with (i - 4)%Z in RB4 by lia. clear RB3.
    (* [comment removed for export] *)
    arun. rd32_at FTB ky4.
    arun. ftdec_at FTB ft3 ky4.
    set (j4 := (zget ft3 ky4 - 1)%Z) in FTB, RB4. set (ft4 := zset ft3 ky4 j4) in FTB, RB4.
    assert (FTN4 : forall v, (0 <= v <= 65536)%Z -> (0 <= zget ft4 v <= n)%Z) by (intros v Hv; subst ft4 j4; rewrite zget_zset; pose proof (FTN3 v Hv); destruct (v =? ky4); lia).
    (* [comment removed for export] *)
    arun. ptr_at AR1 j4. replace (i - 1 + -2)%Z with (i - 3)%Z in AR1 by lia.
    set (a1d := wr32 a1c j4 (i - 3)) in AR1, RB4.
    (* [comment removed for export] *)
    replace (4 * S q)%nat with (S (S (S (S (4 * q)))))%nat in K by lia.
    rewrite (ms_radix2_step _ a1 a2 ft i s Hs BOK) in K. cbv zeta in K. fold ky1 in K. fold j1 in K. fold ft1 in K. fold a1a in K.
    rewrite (ms_radix2_step _ a1a a2 ft1 (i - 1) ky1 KY1 BOK) in K. cbv zeta in K. rewrite Eky2 in K. fold j2 in K. fold ft2 in K. fold a1b in K.
    replace (i - 1 - 1)%Z with (i - 2)%Z in K by lia.
    rewrite (ms_radix2_step _ a1b a2 ft2 (i - 2) ky2 KY2 BOK) in K. cbv zeta in K. rewrite Eky3 in K. fold j3 in K. fold ft3 in K. fold a1c in K.
    replace (i - 2 - 1)%Z with (i - 3)%Z in K by lia.
    rewrite (ms_radix2_step _ a1c a2 ft3 (i - 3) ky3 KY3 BOK) in K. cbv zeta in K. rewrite Eky4 in K. fold j4 in K. fold ft4 in K. fold a1d in K.
    replace (i - 3 - 1)%Z with (i - 4)%Z in K by lia.
    (* [comment removed for export] *)
    arun. if_cases Kc; zify_cond_z Kc.
    - assert (q = 0)%nat.
      { rewrite Nat2Z.inj_succ in Hq4. assert ((i + 1) / 4 < 2)%Z by (apply Z.div_lt_upper_bound; lia). lia. }
      subst q. change (4 * 0)%nat with 0%nat in K. cbn [ms_radix2 fst snd] in K. change (Z.of_nat 1) with 1%Z in K.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _) end;
        [st_eq| exact AR1| exact AR2| exact FTB| assumption| assumption| assumption| exact FTN4| exact KY4|].
      lazymatch goal with |- r2ok n ?a _ _ _ ?b _ => replace a with (Z.to_nat (i - 3)) by lia; replace b with (i - 4)%Z by lia end. exact RB4.
    - wstep.
      enter_with (IH (i - 4)%Z ky4 a1d ft4 a2 _ _ _ me);
        [st_eq| lia| | lia| exact KY4| exact BOK| exact FTN4| | exact AR1| exact AR2| exact FTB| assumption| assumption| assumption| exact SH1| exact SH2| exact SHF| ].
      { rewrite Nat2Z.inj_succ in Hq4. Z.div_mod_to_equations. lia. }
      { replace (Z.to_nat (i - 4 + 1)) with (Z.to_nat (i - 3)) by lia. exact RB4. }
      intros m' x10' x13' x15'. cbv zeta. intros AR1' AR2' FTB' MI' MU' WM' FTN' S' RB'.
      enter_with (K m' x10' x13' x15'); [st_eq| exact AR1'| exact AR2'| exact FTB'| exact MI'| exact MU'| exact WM'| exact FTN'| exact S'|].
      replace (Z.to_nat (i + 1) - S (S (S (S (4 * q)))))%nat with (Z.to_nat (i - 4 + 1) - 4 * q)%nat by lia.
      replace (i - 4 * Z.of_nat (S q))%Z with (i - 4 - 4 * Z.of_nat q)%Z by lia. exact RB'.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_radix2x1 : forall (r : nat) (i s : Z) (a1 ft : zarr) (a2 : zarr) (x11 x15 : word) (me m : word -> option byte),
    (Z.of_nat r = i + 1)%Z -> (0 <= i < n)%Z -> (0 <= s < 65536)%Z -> zbok a2 ->
    (forall v, 0 <= v <= 65536 -> 0 <= zget ft v <= n)%Z -> r2ok n r a1 a2 ft i s ->
    u8arr a0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr a0segs m A2 (zb8 a2 ARR2_SIZE) -> u32arr a0segs m FT (zw32 ft 65537) -> mem_inv a0segs m ->
    munch W1F me m -> wmono a0segs me m ->
    shzW a0segs W1F me A1 (A1 + ARR1_SIZE) -> shzW a0segs W1F me A2 (A2 + ARR2_SIZE) -> shzW a0segs W1F me FT (FT + 262144) ->
    (forall m' (x11' x14' x15' : word), let rr := ms_radix2 r a1 a2 ft i s in
      let a1' := fst (fst rr) in let ft' := snd (fst rr) in
      u8arr a0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr a0segs m' A2 (zb8 a2 ARR2_SIZE) -> u32arr a0segs m' FT (zw32 ft' 65537) -> mem_inv a0segs m' ->
      munch W1F me m' -> wmono a0segs me m' ->
      (forall v, 0 <= v <= 65536 -> 0 <= zget ft' v <= n)%Z ->
      evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (me_sp X) (Z_to_bv 64 P)
                            (Z_to_bv 64 (A2 + (i - Z.of_nat r))) x11' (Z_to_bv 64 (A2 + (i - Z.of_nat r))) (Z_to_bv 64 (i - Z.of_nat r)) x14' x15' a6 a7
                            (Z_to_bv 64 A2) cSB s4 s5 s6 (Z_to_bv 64 FT) (Z_to_bv 64 0) s9 s10 s11 (Z_to_bv 64 A1) t4 t5 t6)
                       F (Z_to_bv 64 0x984c4) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (me_sp X) (Z_to_bv 64 P)
                          (Z_to_bv 64 (A2 + i)) x11 (Z_to_bv 64 (A2 + i)) (Z_to_bv 64 i) (Z_to_bv 64 s) x15 a6 a7
                          (Z_to_bv 64 A2) cSB s4 s5 s6 (Z_to_bv 64 FT) (Z_to_bv 64 (i + 1)) s9 s10 s11 (Z_to_bv 64 A1) t4 t5 t6)
                     F (Z_to_bv 64 0x98414) fc None m (seg_rom a0segs)).
  Proof.
    induction r as [|r IH]; [intros; lia|].
    intros i s a1 ft a2 x11 x15 me m Hr Hi Hs BOK FTN RB AR1 AR2 FTB MI MU WM SH1 SH2 SHF K.
    msenv_open XOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    bz_params.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2. pose proof (zw32_length ft 65537 ltac:(lia)) as LF.
    assert (D0 : (0 <= s / 256 < 256)%Z) by (Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    arun. rd8_at AR2 BOK i. pose proof (BOK i) as B0.
    arun_to 0x98438%Z. rewrite lor_hb by lia.
    set (ky1 := (s / 256 + 256 * zget a2 i)%Z). assert (KY1 : (0 <= ky1 < 65536)%Z) by (subst ky1; lia).
    pose proof (r2ok_here n _ a1 a2 ft i s RB) as R1. fold ky1 in R1. pose proof (FTN ky1 ltac:(lia)) as F1.
    pose proof (r2ok_shift n _ a1 a2 ft i s Hs BOK RB) as RB1. cbv zeta in RB1. fold ky1 in RB1.
    (* [comment removed for export] *)
    arun. rd32_at FTB ky1.
    arun. ftdec_at FTB ft ky1.
    set (j1 := (zget ft ky1 - 1)%Z) in FTB, RB1. set (ft1 := zset ft ky1 j1) in FTB, RB1.
    assert (FTN1 : forall v, (0 <= v <= 65536)%Z -> (0 <= zget ft1 v <= n)%Z) by (intros v Hv; subst ft1 j1; rewrite zget_zset; pose proof (FTN v Hv); destruct (v =? ky1); lia).
    (* [comment removed for export] *)
    arun. ptr_at AR1 j1.
    set (a1a := wr32 a1 j1 i) in AR1, RB1.
    rewrite (ms_radix2_step _ a1 a2 ft i s Hs BOK) in K. cbv zeta in K. fold ky1 in K. fold j1 in K. fold ft1 in K. fold a1a in K.
    (* [comment removed for export] *)
    arun. if_cases Kc; zify_cond_z Kc.
    - enter_with (IH (i - 1)%Z ky1 a1a ft1 a2 _ _ me);
        [st_eq| lia| lia| exact KY1| exact BOK| exact FTN1| exact RB1| exact AR1| exact AR2| exact FTB| assumption| assumption| assumption| exact SH1| exact SH2| exact SHF| ].
      intros m' x11' x14' x15'. cbv zeta. intros AR1' AR2' FTB' MI' MU' WM' FTN'.
      enter_with (K m' x11' x14' x15'); [st_eq| exact AR1'| exact AR2'| exact FTB'| exact MI'| exact MU'| exact WM'| exact FTN'].
    - assert (r = 0)%nat by lia. subst r. cbn [ms_radix2 fst snd] in K. change (Z.of_nat 1) with 1%Z in K.
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _) end;
        [st_eq| exact AR1| exact AR2| exact FTB| assumption| assumption| assumption| exact FTN1].
  Qed.
End A0MS.

End ACeilS1.
