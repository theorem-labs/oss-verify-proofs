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
  (* [comment removed for export] *)


  (* [comment removed for export] *)
  Ltac sw_ptr AR1 j :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?ad (le4 ?w)) _) =>
      lazymatch type of AR1 with u8arr ?segs m ?A (zb8 ?a ?nn) =>
        let H := fresh "ARw" in
        pose proof (zb8_write4 segs m A a nn j w AR1 ltac:(lia) ltac:(lia)) as H; clear AR1; store_done; rename H into AR1
      end end.

  (* [comment removed for export] *)
  Lemma S0_radix2x4 : forall (q : nat) (i s : Z) (a1 ft : zarr) (a2 : zarr) (x17 x5 : word) (me m : word -> option byte),
    (1 <= q)%nat -> (Z.of_nat q = (i + 1) / 4)%Z -> (3 <= i < n)%Z -> (0 <= s < 65536)%Z -> zbok a2 ->
    (forall v, 0 <= v <= 65536 -> 0 <= zget ft v <= n)%Z -> r2ok n (Z.to_nat (i + 1)) a1 a2 ft i s ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) -> u32arr s0segs m FT (zw32 ft 65537) -> mem_inv s0segs m ->
    munch [(A1, A1 + ARR1_SIZE); (FT, FT + 262148)]%Z me m -> wmono s0segs me m ->
    (forall m' (x17' x5' : word), let rr := ms_radix2 (4 * q) a1 a2 ft i s in
      let a1' := fst (fst rr) in let ft' := snd (fst rr) in let s' := snd rr in
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) -> u32arr s0segs m' FT (zw32 ft' 65537) -> mem_inv s0segs m' ->
      munch [(A1, A1 + ARR1_SIZE); (FT, FT + 262148)]%Z me m' -> wmono s0segs me m' ->
      (forall v, 0 <= v <= 65536 -> 0 <= zget ft' v <= n)%Z -> (0 <= s' < 65536)%Z -> r2ok n (Z.to_nat (i + 1) - 4 * q) a1' a2 ft' (i - 4 * Z.of_nat q) s' ->
      evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp x5' t1 t2 (Z_to_bv 64 (i - 4 * Z.of_nat q + 4)) (Z_to_bv 64 FT)
                            (Z_to_bv 64 (A2 + (i - 4 * Z.of_nat q))) (Z_to_bv 64 (i - 4 * Z.of_nat q - n))
                            (Z_to_bv 64 (i - 4 * Z.of_nat q - n - 3)) (Z_to_bv 64 (i - 4 * Z.of_nat q - n - 2)) (Z_to_bv 64 (i - 4 * Z.of_nat q - n - 1))
                            (Z_to_bv 64 6) (Z_to_bv 64 s') x17'
                            s2 s3 (Z_to_bv 64 A2) s5 (Z_to_bv 64 n) s7 s8 s9 s10 (Z_to_bv 64 A1) t3 t4 t5 t6)
                       F (Z_to_bv 64 0x19900) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp x5 t1 t2 (Z_to_bv 64 (i + 4)) (Z_to_bv 64 FT)
                          (Z_to_bv 64 (A2 + i)) (Z_to_bv 64 (i - n))
                          (Z_to_bv 64 (i - n - 3)) (Z_to_bv 64 (i - n - 2)) (Z_to_bv 64 (i - n - 1))
                          (Z_to_bv 64 6) (Z_to_bv 64 s) x17
                          s2 s3 (Z_to_bv 64 A2) s5 (Z_to_bv 64 n) s7 s8 s9 s10 (Z_to_bv 64 A1) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x1981c) fc None m (seg_rom s0segs)).
  Proof.
    induction q as [|q IH]; [intros; lia|].
    intros i s a1 ft a2 x17 x5 me m Hq Hq4 Hi Hs BOK FTN RB AR1 AR2 FTB MI MU WM K.
    msenv_open XOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    bz_params.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2. pose proof (zw32_length ft 65537 ltac:(lia)) as LF.
    assert (D0 : (0 <= s / 256 < 256)%Z) by (Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    rd8_at AR2 BOK i. pose proof (BOK i) as B0.
    wstep. wstep. rewrite srl6_and1020 by lia. wstep. wstep. rewrite lor_hb4 by lia.
    set (ky1 := (s / 256 + 256 * zget a2 i)%Z). assert (KY1 : (0 <= ky1 < 65536)%Z) by (subst ky1; lia).
    replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) in RB by lia.
    pose proof (r2ok_here n _ a1 a2 ft i s RB) as R1. fold ky1 in R1. pose proof (FTN ky1 ltac:(lia)) as F1.
    pose proof (r2ok_shift n _ a1 a2 ft i s Hs BOK RB) as RB1. cbv zeta in RB1. fold ky1 in RB1.
    wstep. rd32_at FTB ky1.
    (* [comment removed for export] *)
    wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm FT _ ky1 _ FTB ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO end.
    wstep. zw32_store FTB ky1 (zget ft ky1 - 1)%Z (rewrite unsigned_lit by lia; reflexivity).
    set (j1 := (zget ft ky1 - 1)%Z) in FTB, RB1. set (ft1 := zset ft ky1 j1) in FTB, RB1.
    assert (FTN1 : forall v, (0 <= v <= 65536)%Z -> (0 <= zget ft1 v <= n)%Z) by (intros v Hv; subst ft1 j1; rewrite zget_zset; pose proof (FTN v Hv); destruct (v =? ky1); lia).
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SO : store_ok s0segs mm (wa (A1 + 4 * j1)) 4 = true)
        by (eapply (u8arr_storeN_ok s0segs _ A1 _ (4 * j1) 4 _ AR1); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]) end.
    wstep. sw_ptr AR1 j1. rewrite unsigned_lit in AR1 by lia. replace (n + (i - n))%Z with i in AR1 by lia.
    set (a1a := wr32 a1 j1 i) in AR1, RB1.
    (* [comment removed for export] *)
    rd8_at AR2 BOK (i - 1)%Z. pose proof (BOK (i - 1)%Z) as B1.
    wstep. wstep. wstep. rewrite lor_hb4 by lia.
    set (ky2 := (zget a2 i + 256 * zget a2 (i - 1))%Z). assert (KY2 : (0 <= ky2 < 65536)%Z) by (subst ky2; lia).
    assert (Eky2 : (ky1 / 256 + 256 * zget a2 (i - 1))%Z = ky2) by (subst ky1 ky2; rewrite key_div256 by lia; reflexivity).
    replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) in RB1 by lia.
    pose proof (r2ok_here n _ a1a a2 ft1 (i - 1) ky1 RB1) as R2. rewrite Eky2 in R2. pose proof (FTN1 ky2 ltac:(lia)) as F2.
    pose proof (r2ok_shift n _ a1a a2 ft1 (i - 1) ky1 KY1 BOK RB1) as RB2. cbv zeta in RB2. rewrite Eky2 in RB2.
    replace (i - 1 - 1)%Z with (i - 2)%Z in RB2 by lia. clear RB1.
    wstep. rd32_at FTB ky2.
    wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm FT _ ky2 _ FTB ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO end.
    wstep. zw32_store FTB ky2 (zget ft1 ky2 - 1)%Z (rewrite unsigned_lit by lia; reflexivity).
    set (j2 := (zget ft1 ky2 - 1)%Z) in FTB, RB2. set (ft2 := zset ft1 ky2 j2) in FTB, RB2.
    assert (FTN2 : forall v, (0 <= v <= 65536)%Z -> (0 <= zget ft2 v <= n)%Z) by (intros v Hv; subst ft2 j2; rewrite zget_zset; pose proof (FTN1 v Hv); destruct (v =? ky2); lia).
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SO : store_ok s0segs mm (wa (A1 + 4 * j2)) 4 = true)
        by (eapply (u8arr_storeN_ok s0segs _ A1 _ (4 * j2) 4 _ AR1); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]) end.
    wstep. sw_ptr AR1 j2. rewrite unsigned_lit in AR1 by lia. replace (n + (i - n - 1))%Z with (i - 1)%Z in AR1 by lia.
    set (a1b := wr32 a1a j2 (i - 1)) in AR1, RB2.
    (* [comment removed for export] *)
    rd8_at AR2 BOK (i - 2)%Z. pose proof (BOK (i - 2)%Z) as B2.
    wstep. wstep. wstep. rewrite lor_hb4 by lia.
    set (ky3 := (zget a2 (i - 1) + 256 * zget a2 (i - 2))%Z). assert (KY3 : (0 <= ky3 < 65536)%Z) by (subst ky3; lia).
    assert (Eky3 : (ky2 / 256 + 256 * zget a2 (i - 2))%Z = ky3) by (subst ky2 ky3; rewrite key_div256 by lia; reflexivity).
    replace (Z.to_nat (i - 1)) with (S (Z.to_nat (i - 2))) in RB2 by lia.
    pose proof (r2ok_here n _ a1b a2 ft2 (i - 2) ky2 RB2) as R3. rewrite Eky3 in R3. pose proof (FTN2 ky3 ltac:(lia)) as F3.
    pose proof (r2ok_shift n _ a1b a2 ft2 (i - 2) ky2 KY2 BOK RB2) as RB3. cbv zeta in RB3. rewrite Eky3 in RB3.
    replace (i - 2 - 1)%Z with (i - 3)%Z in RB3 by lia. clear RB2.
    wstep. rd32_at FTB ky3.
    wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm FT _ ky3 _ FTB ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO end.
    wstep. zw32_store FTB ky3 (zget ft2 ky3 - 1)%Z (rewrite unsigned_lit by lia; reflexivity).
    set (j3 := (zget ft2 ky3 - 1)%Z) in FTB, RB3. set (ft3 := zset ft2 ky3 j3) in FTB, RB3.
    assert (FTN3 : forall v, (0 <= v <= 65536)%Z -> (0 <= zget ft3 v <= n)%Z) by (intros v Hv; subst ft3 j3; rewrite zget_zset; pose proof (FTN2 v Hv); destruct (v =? ky3); lia).
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SO : store_ok s0segs mm (wa (A1 + 4 * j3)) 4 = true)
        by (eapply (u8arr_storeN_ok s0segs _ A1 _ (4 * j3) 4 _ AR1); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]) end.
    wstep. sw_ptr AR1 j3. rewrite unsigned_lit in AR1 by lia. replace (n + (i - n - 2))%Z with (i - 2)%Z in AR1 by lia.
    set (a1c := wr32 a1b j3 (i - 2)) in AR1, RB3.
    (* [comment removed for export] *)
    rd8_at AR2 BOK (i - 3)%Z. pose proof (BOK (i - 3)%Z) as B3.
    wstep. wstep. rewrite lor_hb by lia.
    set (ky4 := (zget a2 (i - 2) + 256 * zget a2 (i - 3))%Z). assert (KY4 : (0 <= ky4 < 65536)%Z) by (subst ky4; lia).
    assert (Eky4 : (ky3 / 256 + 256 * zget a2 (i - 3))%Z = ky4) by (subst ky3 ky4; rewrite key_div256 by lia; reflexivity).
    replace (Z.to_nat (i - 2)) with (S (Z.to_nat (i - 3))) in RB3 by lia.
    pose proof (r2ok_here n _ a1c a2 ft3 (i - 3) ky3 RB3) as R4. rewrite Eky4 in R4. pose proof (FTN3 ky4 ltac:(lia)) as F4.
    pose proof (r2ok_shift n _ a1c a2 ft3 (i - 3) ky3 KY3 BOK RB3) as RB4. cbv zeta in RB4. rewrite Eky4 in RB4.
    replace (i - 3 - 1)%Z with (i - 4)%Z in RB4 by lia. clear RB3.
    wstep. wstep. rewrite sll48_srl46.
    wstep. rd32_at FTB ky4.
    wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm FT _ ky4 _ FTB ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO end.
    wstep. zw32_store FTB ky4 (zget ft3 ky4 - 1)%Z (rewrite unsigned_lit by lia; reflexivity).
    set (j4 := (zget ft3 ky4 - 1)%Z) in FTB, RB4. set (ft4 := zset ft3 ky4 j4) in FTB, RB4.
    assert (FTN4 : forall v, (0 <= v <= 65536)%Z -> (0 <= zget ft4 v <= n)%Z) by (intros v Hv; subst ft4 j4; rewrite zget_zset; pose proof (FTN3 v Hv); destruct (v =? ky4); lia).
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SO : store_ok s0segs mm (wa (A1 + 4 * j4)) 4 = true)
        by (eapply (u8arr_storeN_ok s0segs _ A1 _ (4 * j4) 4 _ AR1); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]) end.
    wstep. sw_ptr AR1 j4. rewrite unsigned_lit in AR1 by lia. replace (n + (i - n - 3))%Z with (i - 3)%Z in AR1 by lia.
    set (a1d := wr32 a1c j4 (i - 3)) in AR1, RB4.
    wstep.
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
    wstep; if_cases Kc; zify_cond_z Kc.
    - enter_with (IH (i - 4)%Z ky4 a1d ft4 a2 _ _ me);
        [st_eq| lia| | lia| exact KY4| exact BOK| exact FTN4| | exact AR1| exact AR2| exact FTB| assumption| assumption| assumption| ].
      { rewrite Nat2Z.inj_succ in Hq4. Z.div_mod_to_equations. lia. }
      { replace (Z.to_nat (i - 4 + 1)) with (Z.to_nat (i - 3)) by lia. exact RB4. }
      intros m' x17' x5'. cbv zeta. intros AR1' AR2' FTB' MI' MU' WM' FTN' S' RB'.
      enter_with (K m' x17' x5'); [st_eq| exact AR1'| exact AR2'| exact FTB'| exact MI'| exact MU'| exact WM'| exact FTN'| exact S'|].
      replace (Z.to_nat (i + 1) - S (S (S (S (4 * q)))))%nat with (Z.to_nat (i - 4 + 1) - 4 * q)%nat by lia.
      replace (i - 4 * Z.of_nat (S q))%Z with (i - 4 - 4 * Z.of_nat q)%Z by lia. exact RB'.
    - assert (q = 0)%nat.
      { rewrite Nat2Z.inj_succ in Hq4. assert ((i + 1) / 4 < 2)%Z by (apply Z.div_lt_upper_bound; lia). lia. }
      subst q. change (4 * 0)%nat with 0%nat in K. cbn [ms_radix2 fst snd] in K. change (Z.of_nat 1) with 1%Z in K.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _) end;
        [st_eq| exact AR1| exact AR2| exact FTB| assumption| assumption| assumption| exact FTN4| exact KY4|].
      lazymatch goal with |- r2ok n ?a _ _ _ ?b _ => replace a with (Z.to_nat (i - 3)) by lia; replace b with (i - 4)%Z by lia end. exact RB4.
  Time Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_radix2x1 : forall (x14 x15 x17 x5 : word) (r : nat) (i s : Z) (a1 ft : zarr) (a2 : zarr) (x12 x13 : word) (me m : word -> option byte),
    (Z.of_nat r = i + 1)%Z -> (0 <= i < n)%Z -> (0 <= s < 65536)%Z -> zbok a2 ->
    (forall v, 0 <= v <= 65536 -> 0 <= zget ft v <= n)%Z -> r2ok n r a1 a2 ft i s ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) -> u32arr s0segs m FT (zw32 ft 65537) -> mem_inv s0segs m ->
    munch [(A1, A1 + ARR1_SIZE); (FT, FT + 262148)]%Z me m -> wmono s0segs me m ->
    (forall m' (x12' x13' x16' : word), let rr := ms_radix2 r a1 a2 ft i s in
      let a1' := fst (fst rr) in let ft' := snd (fst rr) in
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) -> u32arr s0segs m' FT (zw32 ft' 65537) -> mem_inv s0segs m' ->
      munch [(A1, A1 + ARR1_SIZE); (FT, FT + 262148)]%Z me m' -> wmono s0segs me m' ->
      (forall v, 0 <= v <= 65536 -> 0 <= zget ft' v <= n)%Z ->
      evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp x5 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 FT)
                            (Z_to_bv 64 (A2 + (i - Z.of_nat r))) (Z_to_bv 64 (i - Z.of_nat r)) x12' x13' x14 x15 x16' x17
                            s2 s3 (Z_to_bv 64 A2) s5 (Z_to_bv 64 n) s7 s8 s9 s10 (Z_to_bv 64 A1) t3 t4 t5 t6)
                       F (Z_to_bv 64 0x19958) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp x5 t1 t2 (Z_to_bv 64 (i + 1)) (Z_to_bv 64 FT)
                          (Z_to_bv 64 (A2 + i)) (Z_to_bv 64 i) x12 x13 x14 x15 (Z_to_bv 64 s) x17
                          s2 s3 (Z_to_bv 64 A2) s5 (Z_to_bv 64 n) s7 s8 s9 s10 (Z_to_bv 64 A1) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x19910) fc None m (seg_rom s0segs)).
  Proof.
    intros x14 x15 x17 x5. induction r as [|r IH]; [intros; lia|].
    intros i s a1 ft a2 x12 x13 me m Hr Hi Hs BOK FTN RB AR1 AR2 FTB MI MU WM K.
    msenv_open XOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    bz_params.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2. pose proof (zw32_length ft 65537 ltac:(lia)) as LF.
    assert (D0 : (0 <= s / 256 < 256)%Z) by (Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    rd8_at AR2 BOK i. pose proof (BOK i) as B0.
    wstep. wstep. rewrite sll48_srl56. wstep. wstep. rewrite lor_hb by lia.
    set (ky1 := (s / 256 + 256 * zget a2 i)%Z). assert (KY1 : (0 <= ky1 < 65536)%Z) by (subst ky1; lia).
    pose proof (r2ok_here n _ a1 a2 ft i s RB) as R1. fold ky1 in R1. pose proof (FTN ky1 ltac:(lia)) as F1.
    pose proof (r2ok_shift n _ a1 a2 ft i s Hs BOK RB) as RB1. cbv zeta in RB1. fold ky1 in RB1.
    wstep. wstep. rewrite sll48_srl46. wstep. rd32_at FTB ky1.
    (* [comment removed for export] *)
    wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm FT _ ky1 _ FTB ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO end.
    wstep. zw32_store FTB ky1 (zget ft ky1 - 1)%Z (rewrite unsigned_lit by lia; reflexivity).
    set (j1 := (zget ft ky1 - 1)%Z) in FTB, RB1. set (ft1 := zset ft ky1 j1) in FTB, RB1.
    assert (FTN1 : forall v, (0 <= v <= 65536)%Z -> (0 <= zget ft1 v <= n)%Z) by (intros v Hv; subst ft1 j1; rewrite zget_zset; pose proof (FTN v Hv); destruct (v =? ky1); lia).
    (* [comment removed for export] *)
    wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SO : store_ok s0segs mm (wa (A1 + 4 * j1)) 4 = true)
        by (eapply (u8arr_storeN_ok s0segs _ A1 _ (4 * j1) 4 _ AR1); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]) end.
    wstep. sw_ptr AR1 j1. rewrite unsigned_lit in AR1 by lia.
    set (a1a := wr32 a1 j1 i) in AR1, RB1.
    (* [comment removed for export] *)
    wstep. wstep.
    rewrite (ms_radix2_step _ a1 a2 ft i s Hs BOK) in K. cbv zeta in K. fold ky1 in K. fold j1 in K. fold ft1 in K. fold a1a in K.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - enter_with (IH (i - 1)%Z ky1 a1a ft1 a2 _ _ me);
        [st_eq| lia| lia| exact KY1| exact BOK| exact FTN1| exact RB1| exact AR1| exact AR2| exact FTB| assumption| assumption| assumption| ].
      intros m' x12' x13' x16'. cbv zeta. intros AR1' AR2' FTB' MI' MU' WM' FTN'.
      enter_with (K m' x12' x13' x16'); [st_eq| exact AR1'| exact AR2'| exact FTB'| exact MI'| exact MU'| exact WM'| exact FTN'].
    - assert (r = 0)%nat by lia. subst r. cbn [ms_radix2 fst snd] in K. change (Z.of_nat 1) with 1%Z in K.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _) end;
        [st_eq| exact AR1| exact AR2| exact FTB| assumption| assumption| assumption| exact FTN1].
  Time Qed.
End S0MS.

End ACeilS1.
