(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzTac BzTac2 BzArr BzCMem BzCHuff BzCHuffF1 BzArrD CmpMem CmpCut CmpCut0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF1.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFsKit0 CmpHmKit S0_cmp_hmA.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.BzCFactsHm OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpFsKit0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_hmA.
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
Local Ltac simpl_arr_sizes ::= CmpFast.sas7_all.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section S0HM.
  Variable X : hmenv. Variable Q : machine_state -> Prop.
  Variables Jh Jw Jp : list byte.
  Hypothesis XOK : hmenv_ok X.
  Notation usp := (bv_unsigned (he_sp X)). Notation p := (bv_unsigned (he_sp X) - 5296)%Z.
  Notation A := (he_A X). Notation El := (he_El X). Notation Ef := (he_Ef X). Notation lb := (he_lb X). Notation fb := (he_fb X).
  Notation gp := (he_gp X). Notation tp := (he_tp X). Notation F := (he_F X). Notation fc := (he_fc X).
  Notation Jf := (he_Jf X). Notation freq := (he_freq X). Notation NF := (he_NF X).
  Notation Jl := (he_Jl X). Notation NL := (he_NL X).
  (* [comment removed for export] *)
  Notation RR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 p) gp tp t0 t1 t2 (Z_to_bv 64 17) (Z_to_bv 64 (A + 1)) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 (-1)) (Z_to_bv 64 (p + 2088 + 4 * (A + 1))) (Z_to_bv 64 (p + 4152)) (Z_to_bv 64 4) (Z_to_bv 64 A)
         (Z_to_bv 64 (p + 24)) (Z_to_bv 64 2) (Z_to_bv 64 (El + lb - 1)) (Z_to_bv 64 (p + 2088)) (Z_to_bv 64 (p + 4152)) t3 t4 t5 t6).
  Notation RA := (Z_to_bv 64 0x1b710).
  (* [comment removed for export] *)
  Notation RW ra t0 t1 t2 a1 a2 a4 a5 a6 a7 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 p) gp tp t0 t1 t2 (Z_to_bv 64 17) (he_s1 X) (Z_to_bv 64 (El + lb)) a1 a2 (Z_to_bv 64 (Ef + 4 * (fb + A))) a4 a5 a6 a7
         (he_s2 X) (he_s3 X) (Z_to_bv 64 (p + 4152)) (he_s5 X) (Z_to_bv 64 A) (he_s7 X) (he_s8 X) (he_s9 X) (he_s10 X) (he_s11 X) t3 t4 t5 t6).

  Lemma lor_even1 : forall z, (0 <= z)%Z -> Z.lor (z * 2) 1 = (z * 2 + 1)%Z.
  Proof.
    intros z Hz. pose proof (Z.add_lor_land (z * 2) 1) as E.
    assert (L : Z.land (z * 2) 1 = 0%Z); [|lia].
    rewrite land1_mod2. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_hm_down1 : forall (f : nat) (zz nHq nN n1 tmp : Z) (h w : zarr) (me m : word -> option byte)
      (t2 a0 a4 a7 t3 t4 t5 : word),
    (1 <= zz)%Z -> (zz * 2 <= nHq)%Z -> (nHq <= 258)%Z -> (nHq < zz * 2 ^ Z.of_nat f)%Z -> (0 <= nN <= 515)%Z ->
    (0 <= tmp <= nN)%Z -> hw h w nHq nN ->
    u32arr s0segs m (p + 4152) (ovw h Jh 260) -> u32arr s0segs m (p + 2088) (ovw w Jw 516) -> mem_inv s0segs m ->
    munch [(p + 4152, p + 5192)]%Z me m -> wmono s0segs me m ->
    (forall h' zz' m' (t0 t1 t2 t3 : word),
      downheap_loop f h w nHq zz tmp = (h', zz') -> (1 <= zz' <= nHq)%Z -> hw h' w nHq nN ->
      u32arr s0segs m' (p + 4152) (ovw h' Jh 260) -> u32arr s0segs m' (p + 2088) (ovw w Jw 516) -> mem_inv s0segs m' ->
      munch [(p + 4152, p + 5192)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RR RA t0 t1 t2 a0 (Z_to_bv 64 (nHq + 1)) (Z_to_bv 64 nHq) (Z_to_bv 64 n1) a4 (Z_to_bv 64 tmp) (Z_to_bv 64 (zget w tmp)) (Z_to_bv 64 zz') t3 t4 t5 (Z_to_bv 64 3))
                       F (Z_to_bv 64 0x1b894) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RR RA (Z_to_bv 64 zz) (Z_to_bv 64 (zz * 2)) t2 a0 (Z_to_bv 64 (nHq + 1)) (Z_to_bv 64 nHq) (Z_to_bv 64 n1) a4 (Z_to_bv 64 tmp) (Z_to_bv 64 (zget w tmp)) a7 t3 t4 t5 (Z_to_bv 64 3))
                     F (Z_to_bv 64 0x1b80c) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH]. { intros. cbn in H2. lia. }
    intros zz nHq nN n1 tmp h w me m t2 a0 a4 a7 t3 t4 t5 Hzz Hyy HnH Hf HnN Htmp HW HEAP WGT MI MU WM K.
    hmenv_open XOK. cps_destruct HW as (S1 & S2 & HH & WW).
    pose proof (ovw_length h Jh 260 ltac:(lia)) as LH. pose proof (ovw_length w Jw 516 ltac:(lia)) as LW.
    pose proof (WW tmp ltac:(lia)) as [Dwt Rwt].
    (* [comment removed for export] *)
    assert (TAIL : forall yy' (x7 x28 : word), yy' = dh_child h w nHq (zz * 2) -> (zz * 2 <= yy' <= nHq)%Z -> (yy' <= zz * 2 + 1)%Z ->
      evt s0segs Q (MS (RR RA (Z_to_bv 64 zz) (Z_to_bv 64 yy') x7 a0 (Z_to_bv 64 (nHq + 1)) (Z_to_bv 64 nHq) (Z_to_bv 64 n1) a4 (Z_to_bv 64 tmp) (Z_to_bv 64 (zget w tmp)) (Z_to_bv 64 yy') x28 t4 t5 (Z_to_bv 64 3))
                       F (Z_to_bv 64 0x1b858) fc None m (seg_rom s0segs))).
    { intros yy' x7 x28 Eyy Hyy' Hyy2.
      pose proof (HH yy' ltac:(lia)) as [Dy Ry]. pose proof (WW (zget h yy') ltac:(lia)) as [Dwy Rwy].
      (* [comment removed for export] *)
      wstep. wstep.
      pose proof (ovw_read s0segs _ (p + 4152) h Jh 260 yy' _ HEAP ltac:(lia) Dy ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget h yy')) by lia.
      (* [comment removed for export] *)
      wstep. wstep.
      pose proof (ovw_read s0segs _ (p + 2088) w Jw 516 (zget h yy') _ WGT ltac:(lia) Dwy ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget w (zget h yy'))) by lia.
      (* [comment removed for export] *)
      wstep; if_cases Kb; zify_cond_z Kb.
      - (* [comment removed for export] *)
        wstep.
        enter_with (K h zz m _ _ _ _); [st_eq| | lia| exact (conj S1 (conj S2 (conj HH WW)))| exact HEAP| exact WGT| exact MI| exact MU| exact WM].
        apply downheap_loop_stop2; [apply Z.ltb_ge; rewrite shiftl1_mul2; lia|]. rewrite shiftl1_mul2, <- Eyy. apply Z.ltb_lt. exact Kb.
      - (* [comment removed for export] *)
        wstep. wstep. wstep.
        pose proof (u32arr_store_ok s0segs m (p + 4152) _ zz _ HEAP ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
        wstep. store_addr (p + 4152 + 4 * zz)%Z. ovw_store HEAP zz (zget h yy') wval_lit.
        wstep.
        assert (HW1 : hw (zset h zz (zget h yy')) w nHq nN) by (apply hw_hset; [exact (conj S1 (conj S2 (conj HH WW)))| lia| lia]).
        (* [comment removed for export] *)
        wstep; if_cases Kl; zify_cond_z Kl.
        + enter_with (IH yy' nHq nN n1 tmp (zset h zz (zget h yy')) w me); [st_eq| lia| lia| lia| | lia| lia| exact HW1| exact HEAP| exact WGT| exact MI| exact MU| exact WM|].
          * rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hf by lia.
            (* [comment removed for export] *)
            eapply Z.lt_le_trans; [exact Hf|]. rewrite Z.mul_assoc.
            apply Z.mul_le_mono_nonneg_r; [apply Z.pow_nonneg; discriminate | exact (proj1 Hyy')].
          * intros h' zz' m' y5 y6 y7 y28 E Hzz' HW'. eapply K; [| lia| exact HW'].
            rewrite downheap_loop_S. replace (nHq <? Z.shiftl zz 1)%Z with false by (symmetry; apply Z.ltb_ge; rewrite shiftl1_mul2; lia).
            cbn zeta. rewrite shiftl1_mul2, <- Eyy. replace (zget w tmp <? zget w (zget h yy'))%Z with false by (symmetry; apply Z.ltb_ge; lia). exact E.
        + (* [comment removed for export] *)
          wstep.
          enter_with (K (zset h zz (zget h yy')) yy' _ _ _ _ _); [st_eq| | lia| exact HW1| exact HEAP| exact WGT| exact MI| exact MU| exact WM].
          rewrite downheap_loop_S. replace (nHq <? Z.shiftl zz 1)%Z with false by (symmetry; apply Z.ltb_ge; rewrite shiftl1_mul2; lia).
          cbn zeta. rewrite shiftl1_mul2, <- Eyy. replace (zget w tmp <? zget w (zget h yy'))%Z with false by (symmetry; apply Z.ltb_ge; lia).
          apply downheap_loop_stop1. apply Z.ltb_lt. rewrite shiftl1_mul2. lia. }
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      wstep. enter_with (TAIL (zz * 2)%Z t2 t3); [st_eq| | lia| lia].
      unfold dh_child. replace (zz * 2 <? nHq)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
    - (* [comment removed for export] *)
      pose proof (HH (zz * 2)%Z ltac:(lia)) as [D0 R0]. pose proof (HH (zz * 2 + 1)%Z ltac:(lia)) as [D1 R1].
      pose proof (WW (zget h (zz * 2)) ltac:(lia)) as [Dw0 Rw0]. pose proof (WW (zget h (zz * 2 + 1)) ltac:(lia)) as [Dw1 Rw1].
      wstep. rewrite lor_even1 by lia.
      wstep. wstep. wstep. wstep.
      pose proof (ovw_read s0segs _ (p + 4152) h Jh 260 (zz * 2 + 1) _ HEAP ltac:(lia) D1 ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget h (zz * 2 + 1))) by lia.
      pose proof (ovw_read s0segs _ (p + 4152) h Jh 260 (zz * 2) _ HEAP ltac:(lia) D0 ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget h (zz * 2))) by lia.
      wstep. wstep. wstep. wstep.
      pose proof (ovw_read s0segs _ (p + 2088) w Jw 516 (zget h (zz * 2 + 1)) _ WGT ltac:(lia) Dw1 ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget w (zget h (zz * 2 + 1)))) by lia.
      pose proof (ovw_read s0segs _ (p + 2088) w Jw 516 (zget h (zz * 2)) _ WGT ltac:(lia) Dw0 ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget w (zget h (zz * 2)))) by lia.
      (* [comment removed for export] *)
      wstep; if_cases Kw; zify_cond_z Kw.
      + (* [comment removed for export] *)
        wstep. wstep. enter_with (TAIL (zz * 2 + 1)%Z _ _); [st_eq| | lia| lia].
        unfold dh_child. replace (zz * 2 <? nHq)%Z with true by (symmetry; apply Z.ltb_lt; lia).
        replace (zget w (zget h (zz * 2 + 1)) <? zget w (zget h (zz * 2)))%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
      + (* [comment removed for export] *)
        wstep. wstep. wstep. enter_with (TAIL (zz * 2)%Z _ _); [st_eq| | lia| lia].
        unfold dh_child. replace (zz * 2 <? nHq)%Z with true by (symmetry; apply Z.ltb_lt; lia).
        replace (zget w (zget h (zz * 2 + 1)) <? zget w (zget h (zz * 2)))%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_hm_down2 : forall (f : nat) (zz nHq nN n1 n2 tmp : Z) (h w : zarr) (me m : word -> option byte)
      (a0 a4 t4 t5 : word),
    (1 <= zz)%Z -> (zz * 2 <= nHq)%Z -> (nHq <= 258)%Z -> (nHq < zz * 2 ^ Z.of_nat f)%Z -> (0 <= nN <= 515)%Z ->
    (0 <= tmp <= nN)%Z -> hw h w nHq nN ->
    u32arr s0segs m (p + 4152) (ovw h Jh 260) -> u32arr s0segs m (p + 2088) (ovw w Jw 516) -> mem_inv s0segs m ->
    munch [(p + 4152, p + 5192)]%Z me m -> wmono s0segs me m ->
    (forall h' zz' m' (t2 t3 t4 t5 : word),
      downheap_loop f h w nHq zz tmp = (h', zz') -> (1 <= zz' <= nHq)%Z -> hw h' w nHq nN ->
      u32arr s0segs m' (p + 4152) (ovw h' Jh 260) -> u32arr s0segs m' (p + 2088) (ovw w Jw 516) -> mem_inv s0segs m' ->
      munch [(p + 4152, p + 5192)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RR RA (Z_to_bv 64 (zget w tmp)) (Z_to_bv 64 nHq) t2 a0 (Z_to_bv 64 (nHq + 2)) (Z_to_bv 64 (nHq + 1)) (Z_to_bv 64 n1) (Z_to_bv 64 zz') (Z_to_bv 64 (p + 4152 + 4 * (nHq + 1))) (Z_to_bv 64 tmp) (Z_to_bv 64 n2) t3 t4 t5 (Z_to_bv 64 3))
                       F (Z_to_bv 64 0x1b958) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RR RA (Z_to_bv 64 (zget w tmp)) (Z_to_bv 64 nHq) (Z_to_bv 64 zz) a0 (Z_to_bv 64 (nHq + 2)) (Z_to_bv 64 (nHq + 1)) (Z_to_bv 64 n1) a4 (Z_to_bv 64 (p + 4152 + 4 * (nHq + 1))) (Z_to_bv 64 tmp) (Z_to_bv 64 n2) (Z_to_bv 64 (zz * 2)) t4 t5 (Z_to_bv 64 3))
                     F (Z_to_bv 64 0x1b8d0) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH]. { intros. cbn in H2. lia. }
    intros zz nHq nN n1 n2 tmp h w me m a0 a4 t4 t5 Hzz Hyy HnH Hf HnN Htmp HW HEAP WGT MI MU WM K.
    hmenv_open XOK. cps_destruct HW as (S1 & S2 & HH & WW).
    pose proof (ovw_length h Jh 260 ltac:(lia)) as LH. pose proof (ovw_length w Jw 516 ltac:(lia)) as LW.
    pose proof (WW tmp ltac:(lia)) as [Dwt Rwt].
    (* [comment removed for export] *)
    assert (TAIL : forall yy' (x29 x30 : word), yy' = dh_child h w nHq (zz * 2) -> (zz * 2 <= yy' <= nHq)%Z -> (yy' <= zz * 2 + 1)%Z ->
      evt s0segs Q (MS (RR RA (Z_to_bv 64 (zget w tmp)) (Z_to_bv 64 nHq) (Z_to_bv 64 zz) a0 (Z_to_bv 64 (nHq + 2)) (Z_to_bv 64 (nHq + 1)) (Z_to_bv 64 n1) (Z_to_bv 64 yy') (Z_to_bv 64 (p + 4152 + 4 * (nHq + 1))) (Z_to_bv 64 tmp) (Z_to_bv 64 n2) (Z_to_bv 64 yy') x29 x30 (Z_to_bv 64 3))
                       F (Z_to_bv 64 0x1b91c) fc None m (seg_rom s0segs))).
    { intros yy' x29 x30 Eyy Hyy' Hyy2.
      pose proof (HH yy' ltac:(lia)) as [Dy Ry]. pose proof (WW (zget h yy') ltac:(lia)) as [Dwy Rwy].
      (* [comment removed for export] *)
      wstep. wstep.
      pose proof (ovw_read s0segs _ (p + 4152) h Jh 260 yy' _ HEAP ltac:(lia) Dy ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget h yy')) by lia.
      (* [comment removed for export] *)
      wstep. wstep.
      pose proof (ovw_read s0segs _ (p + 2088) w Jw 516 (zget h yy') _ WGT ltac:(lia) Dwy ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget w (zget h yy'))) by lia.
      (* [comment removed for export] *)
      wstep; if_cases Kb; zify_cond_z Kb.
      - (* [comment removed for export] *)
        wstep.
        enter_with (K h zz m _ _ _ _); [st_eq| | lia| exact (conj S1 (conj S2 (conj HH WW)))| exact HEAP| exact WGT| exact MI| exact MU| exact WM].
        apply downheap_loop_stop2; [apply Z.ltb_ge; rewrite shiftl1_mul2; lia|]. rewrite shiftl1_mul2, <- Eyy. apply Z.ltb_lt. exact Kb.
      - (* [comment removed for export] *)
        wstep. wstep. wstep.
        pose proof (u32arr_store_ok s0segs m (p + 4152) _ zz _ HEAP ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
        wstep. store_addr (p + 4152 + 4 * zz)%Z. ovw_store HEAP zz (zget h yy') wval_lit.
        wstep.
        assert (HW1 : hw (zset h zz (zget h yy')) w nHq nN) by (apply hw_hset; [exact (conj S1 (conj S2 (conj HH WW)))| lia| lia]).
        (* [comment removed for export] *)
        wstep; if_cases Kl; zify_cond_z Kl.
        + enter_with (IH yy' nHq nN n1 n2 tmp (zset h zz (zget h yy')) w me); [st_eq| lia| lia| lia| | lia| lia| exact HW1| exact HEAP| exact WGT| exact MI| exact MU| exact WM|].
          * rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hf by lia.
            (* [comment removed for export] *)
            eapply Z.lt_le_trans; [exact Hf|]. rewrite Z.mul_assoc.
            apply Z.mul_le_mono_nonneg_r; [apply Z.pow_nonneg; discriminate | exact (proj1 Hyy')].
          * intros h' zz' m' y5 y6 y7 y28 E Hzz' HW'. eapply K; [| lia| exact HW'].
            rewrite downheap_loop_S. replace (nHq <? Z.shiftl zz 1)%Z with false by (symmetry; apply Z.ltb_ge; rewrite shiftl1_mul2; lia).
            cbn zeta. rewrite shiftl1_mul2, <- Eyy. replace (zget w tmp <? zget w (zget h yy'))%Z with false by (symmetry; apply Z.ltb_ge; lia). exact E.
        + (* [comment removed for export] *)
          wstep.
          enter_with (K (zset h zz (zget h yy')) yy' _ _ _ _ _); [st_eq| | lia| exact HW1| exact HEAP| exact WGT| exact MI| exact MU| exact WM].
          rewrite downheap_loop_S. replace (nHq <? Z.shiftl zz 1)%Z with false by (symmetry; apply Z.ltb_ge; rewrite shiftl1_mul2; lia).
          cbn zeta. rewrite shiftl1_mul2, <- Eyy. replace (zget w tmp <? zget w (zget h yy'))%Z with false by (symmetry; apply Z.ltb_ge; lia).
          apply downheap_loop_stop1. apply Z.ltb_lt. rewrite shiftl1_mul2. lia. }
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      wstep. enter_with (TAIL (zz * 2)%Z t4 t5); [st_eq| | lia| lia].
      unfold dh_child. replace (zz * 2 <? nHq)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
    - (* [comment removed for export] *)
      pose proof (HH (zz * 2)%Z ltac:(lia)) as [D0 R0]. pose proof (HH (zz * 2 + 1)%Z ltac:(lia)) as [D1 R1].
      pose proof (WW (zget h (zz * 2)) ltac:(lia)) as [Dw0 Rw0]. pose proof (WW (zget h (zz * 2 + 1)) ltac:(lia)) as [Dw1 Rw1].
      wstep. rewrite lor_even1 by lia.
      wstep. wstep. wstep. wstep.
      pose proof (ovw_read s0segs _ (p + 4152) h Jh 260 (zz * 2 + 1) _ HEAP ltac:(lia) D1 ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget h (zz * 2 + 1))) by lia.
      pose proof (ovw_read s0segs _ (p + 4152) h Jh 260 (zz * 2) _ HEAP ltac:(lia) D0 ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget h (zz * 2))) by lia.
      wstep. wstep. wstep. wstep.
      pose proof (ovw_read s0segs _ (p + 2088) w Jw 516 (zget h (zz * 2 + 1)) _ WGT ltac:(lia) Dw1 ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget w (zget h (zz * 2 + 1)))) by lia.
      pose proof (ovw_read s0segs _ (p + 2088) w Jw 516 (zget h (zz * 2)) _ WGT ltac:(lia) Dw0 ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget w (zget h (zz * 2)))) by lia.
      (* [comment removed for export] *)
      wstep; if_cases Kw; zify_cond_z Kw.
      + (* [comment removed for export] *)
        wstep. wstep. enter_with (TAIL (zz * 2 + 1)%Z _ _); [st_eq| | lia| lia].
        unfold dh_child. replace (zz * 2 <? nHq)%Z with true by (symmetry; apply Z.ltb_lt; lia).
        replace (zget w (zget h (zz * 2 + 1)) <? zget w (zget h (zz * 2)))%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
      + (* [comment removed for export] *)
        wstep. wstep. wstep. enter_with (TAIL (zz * 2)%Z _ _); [st_eq| | lia| lia].
        unfold dh_child. replace (zz * 2 <? nHq)%Z with true by (symmetry; apply Z.ltb_lt; lia).
        replace (zget w (zget h (zz * 2 + 1)) <? zget w (zget h (zz * 2)))%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_hm_up2 : forall (f : nat) (zz nHm nNq : Z) (h w : zarr) (me m : word -> option byte)
      (t1 t2 a7 t3 t4 t5 : word),
    (1 <= zz <= nHm)%Z -> (nHm <= 258)%Z -> (zz < 2 ^ Z.of_nat f)%Z -> (1 <= nNq <= 515)%Z ->
    (zget w nNq <? zget w (zget h (Z.shiftr zz 1)))%Z = true ->
    hw h w nHm nNq ->
    u32arr s0segs m (p + 4152) (ovw h Jh 260) -> u32arr s0segs m (p + 2088) (ovw w Jw 516) -> mem_inv s0segs m ->
    munch [(p + 4152, p + 5192)]%Z me m -> wmono s0segs me m ->
    (forall h' zz' m' (a5 a6 t1 : word),
      upheap_loop f h w zz nNq = (h', zz') -> (1 <= zz' <= zz)%Z -> hw h' w nHm nNq ->
      u32arr s0segs m' (p + 4152) (ovw h' Jh 260) -> u32arr s0segs m' (p + 2088) (ovw w Jw 516) -> mem_inv s0segs m' ->
      munch [(p + 4152, p + 5192)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RR RA (Z_to_bv 64 zz') t1 t2 (Z_to_bv 64 (nNq - 1)) (Z_to_bv 64 (nHm + 1)) (Z_to_bv 64 nHm) (Z_to_bv 64 (zget w nNq)) (Z_to_bv 64 nNq) a5 a6 (Z_to_bv 64 zz') t3 t4 t5 (Z_to_bv 64 3))
                       F (Z_to_bv 64 0x1ba2c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RR RA (Z_to_bv 64 zz) t1 t2 (Z_to_bv 64 (nNq - 1)) (Z_to_bv 64 (nHm + 1)) (Z_to_bv 64 nHm) (Z_to_bv 64 (zget w nNq)) (Z_to_bv 64 nNq)
                          (Z_to_bv 64 (zz / 2)) (Z_to_bv 64 (zget h (zz / 2))) a7 t3 t4 t5 (Z_to_bv 64 3))
                     F (Z_to_bv 64 0x1b9f0) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH].
    { intros. cbn in H1. lia. }
    intros zz nHm nNq h w me m t1 t2 a7 t3 t4 t5 Hzz HnH Hf HnN CT HW HEAP WGT MI MU WM K.
    hmenv_open XOK. cps_destruct HW as (S1 & S2 & HH & WW).
    rewrite shiftr1_div2 in *.
    assert (Hzz2 : (2 <= zz)%Z).
    { destruct (Z_lt_le_dec zz 2); [|assumption]. exfalso. replace (zz / 2)%Z with 0%Z in CT by (Z.div_mod_to_equations; lia).
      rewrite S1, S2 in CT. apply Z.ltb_lt in CT. pose proof (WW nNq ltac:(lia)). lia. }
    assert (Hz2 : (1 <= zz / 2 < zz)%Z) by (Z.div_mod_to_equations; lia).
    pose proof (HH (zz / 2)%Z ltac:(lia)) as [Dp Rp]. pose proof (WW nNq ltac:(lia)) as [Dwi Rwi].
    pose proof (ovw_length h Jh 260 ltac:(lia)) as LH. pose proof (ovw_length w Jw 516 ltac:(lia)) as LW.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep.
    (* [comment removed for export] *)
    pose proof (u32arr_store_ok s0segs m (p + 4152) _ zz _ HEAP ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO.
    wstep. ovw_store HEAP zz (zget h (zz / 2))%Z wval_lit.
    (* [comment removed for export] *)
    wstep.
    assert (Hz4 : (0 <= zz / 2 / 2 <= zz / 2)%Z) by (Z.div_mod_to_equations; lia).
    set (h1 := zset h zz (zget h (zz / 2))) in *.
    assert (HW1 : hw h1 w nHm nNq) by (subst h1; apply hw_hset; [exact (conj S1 (conj S2 (conj HH WW)))| lia| lia]).
    cps_destruct HW1 as (S1' & _ & HH1 & _).
    pose proof (HH1 (zz / 2 / 2)%Z ltac:(lia)) as [Dq Rq].
    pose proof (ovw_read s0segs _ (p + 4152) h1 Jh 260 (zz / 2 / 2) _ HEAP ltac:(lia) Dq ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. try rewrite (sx32_of_Z (zget h1 (zz / 2 / 2))) by lia.
    (* [comment removed for export] *)
    wstep. wstep.
    pose proof (WW (zget h1 (zz / 2 / 2)) ltac:(lia)) as [Dw2 Rw2].
    pose proof (ovw_read s0segs _ (p + 2088) w Jw 516 (zget h1 (zz / 2 / 2)) _ WGT ltac:(lia) Dw2 ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. try rewrite (sx32_of_Z (zget w (zget h1 (zz / 2 / 2)))) by lia.
    (* [comment removed for export] *)
    wstep.
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      enter_with (IH (zz / 2)%Z nHm nNq h1 w me); [st_eq| lia| lia| | lia| | | exact HEAP| exact WGT| exact MI| exact MU| exact WM| ].
      + rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hf by lia. apply Z.div_lt_upper_bound; lia.
      + rewrite shiftr1_div2. apply Z.ltb_lt. exact Kc.
      + split; [exact S1'| split; [exact S2| split; [exact HH1| exact WW]]].
      + intros h' zz' m' a5' a6' t1' E Hzz' HW'. eapply K; [| lia| exact HW'].
        rewrite upheap_loop_S, shiftr1_div2, CT. subst h1. exact E.
    - (* [comment removed for export] *)
      wstep.
      enter_with (K h1 (zz / 2)%Z _ _ _ _); [st_eq| | lia| | exact HEAP| exact WGT| exact MI| exact MU| exact WM].
      + rewrite upheap_loop_S, shiftr1_div2, CT. apply upheap_loop_stop. rewrite shiftr1_div2. apply Z.ltb_ge. subst h1. lia.
      + split; [exact S1'| split; [exact S2| split; [exact HH1| exact WW]]].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_hm_cpop1 : forall (h w : zarr) (nH nN : Z) (me m : word -> option byte)
      (t0 t1 t2 a0 a1 a3 a5 a6 a7 t3 t4 t5 : word),
    (2 <= nH <= 258)%Z -> (0 <= nN <= 515)%Z -> hw h w nH nN ->
    u32arr s0segs m (p + 4152) (ovw h Jh 260) -> u32arr s0segs m (p + 2088) (ovw w Jw 516) -> mem_inv s0segs m ->
    munch [(p + 4152, p + 5192)]%Z me m -> wmono s0segs me m ->
    (forall hA zzA m' (t0 t1 t2 a6 t3 : word),
      downheap_loop 20 (zset h 1 (zget h nH)) w (nH - 1) 1 (zget h nH) = (hA, zzA) -> (1 <= zzA <= nH - 1)%Z -> hw hA w (nH - 1) nN ->
      u32arr s0segs m' (p + 4152) (ovw hA Jh 260) -> u32arr s0segs m' (p + 2088) (ovw w Jw 516) -> mem_inv s0segs m' ->
      munch [(p + 4152, p + 5192)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RR RA t0 t1 t2 (Z_to_bv 64 nN) (Z_to_bv 64 nH) (Z_to_bv 64 (nH - 1)) (Z_to_bv 64 (zget h 1)) (Z_to_bv 64 1) (Z_to_bv 64 (zget h nH)) a6 (Z_to_bv 64 zzA) t3 t4 t5 (Z_to_bv 64 3))
                       F (Z_to_bv 64 0x1b894) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RR RA t0 t1 t2 a0 a1 (Z_to_bv 64 nH) a3 (Z_to_bv 64 nN) a5 a6 a7 t3 t4 t5 (Z_to_bv 64 3))
                     F (Z_to_bv 64 0x1b7cc) fc None m (seg_rom s0segs)).
  Proof.
    intros h w nH nN me m t0 t1 t2 a0 a1 a3 a5 a6 a7 t3 t4 t5 HnH HnN HW HEAP WGT MI MU WM K.
    hmenv_open XOK. pose proof HW as HW0. cps_destruct HW0 as (S1 & S2 & HH & WW).
    pose proof (ovw_length h Jh 260 ltac:(lia)) as LH. pose proof (ovw_length w Jw 516 ltac:(lia)) as LW.
    pose proof (HH nH ltac:(lia)) as [Dn Rn]. pose proof (HH 1%Z ltac:(lia)) as [D1 R1].
    set (tmp1 := zget h nH) in *. set (n1 := zget h 1) in *.
    pose proof (WW tmp1 ltac:(lia)) as [Dwt Rwt].
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep.
    pose proof (ovw_read s0segs _ (p + 4152) h Jh 260 nH _ HEAP ltac:(lia) Dn ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. fold tmp1. try rewrite (sx32_of_Z tmp1) by lia.
    (* [comment removed for export] *)
    wstep.
    pose proof (ovw_read s0segs _ (p + 4152) h Jh 260 1 _ HEAP ltac:(lia) D1 ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. fold n1. try rewrite (sx32_of_Z n1) by lia.
    (* [comment removed for export] *)
    wstep.
    pose proof (u32arr_store_ok s0segs m (p + 4152) _ 1 _ HEAP ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    wstep. store_addr (p + 4152 + 4 * 1)%Z. ovw_store HEAP 1%Z tmp1 wval_lit.
    assert (HW1 : hw (zset h 1 tmp1) w (nH - 1) nN).
    { apply (hw_nH_le _ _ nH); [|lia]. apply hw_hset; [exact HW| lia| lia]. }
    (* [comment removed for export] *)
    wstep.
    wstep; if_cases Ks; zify_cond_z Ks.
    - (* [comment removed for export] *)
      enter_with (K (zset h 1 tmp1) 1%Z _ _ _ _ _ _); [st_eq| | lia| exact HW1| exact HEAP| exact WGT| exact MI| exact MU| exact WM].
      apply downheap_loop_stop1. apply Z.ltb_lt. rewrite shiftl1_mul2. lia.
    - (* [comment removed for export] *)
      wstep. wstep.
      pose proof (ovw_read s0segs _ (p + 2088) w Jw 516 tmp1 _ WGT ltac:(lia) Dwt ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget w tmp1)) by lia.
      wstep. wstep.
      enter_with (S0_hm_down1 20%nat 1 (nH - 1) nN n1 tmp1 (zset h 1 tmp1) w me); [st_eq| lia| lia| lia| cbn; lia| lia| lia| exact HW1| exact HEAP| exact WGT| exact MI| exact MU| exact WM|].
      intros hA zzA m' x5 x6 x7 x28 E HzzA HWA HEAP' WGT' MI' MU' WM'.
      enter_with (K hA zzA m' x5 x6 x7 _ x28); [st_eq| exact E| lia| exact HWA| exact HEAP'| exact WGT'| exact MI'| exact MU'| exact WM'].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_hm_cpop2 : forall (hA w : zarr) (zzA tmp1 n1 nH nN : Z) (me m : word -> option byte)
      (t0 t1 t2 a6 t3 t4 t5 : word),
    (2 <= nH <= 258)%Z -> (0 <= nN <= 515)%Z -> (1 <= zzA <= nH - 1)%Z -> (0 <= tmp1 <= nN)%Z -> hw hA w (nH - 1) nN ->
    u32arr s0segs m (p + 4152) (ovw hA Jh 260) -> u32arr s0segs m (p + 2088) (ovw w Jw 516) -> mem_inv s0segs m ->
    munch [(p + 4152, p + 5192)]%Z me m -> wmono s0segs me m ->
    (forall hB zzB m' (t0 t1 t2 t3 t4 t5 : word),
      let hp1 := zset hA zzA tmp1 in
      downheap_loop 20 (zset hp1 1 (zget hp1 (nH - 1))) w (nH - 2) 1 (zget hp1 (nH - 1)) = (hB, zzB) -> (1 <= zzB <= nH - 1)%Z ->
      hw hB w (nH - 2) nN ->
      u32arr s0segs m' (p + 4152) (ovw hB Jh 260) -> u32arr s0segs m' (p + 2088) (ovw w Jw 516) -> mem_inv s0segs m' ->
      munch [(p + 4152, p + 5192)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RR RA t0 t1 t2 (Z_to_bv 64 nN) (Z_to_bv 64 nH) (Z_to_bv 64 (nH - 1)) (Z_to_bv 64 n1) (Z_to_bv 64 zzB)
                            (Z_to_bv 64 (p + 4152 + 4 * (nH - 1))) (Z_to_bv 64 (zget hp1 (nH - 1))) (Z_to_bv 64 (zget hp1 1)) t3 t4 t5 (Z_to_bv 64 3))
                       F (Z_to_bv 64 0x1b958) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RR RA t0 t1 t2 (Z_to_bv 64 nN) (Z_to_bv 64 nH) (Z_to_bv 64 (nH - 1)) (Z_to_bv 64 n1) (Z_to_bv 64 1) (Z_to_bv 64 tmp1) a6 (Z_to_bv 64 zzA) t3 t4 t5 (Z_to_bv 64 3))
                     F (Z_to_bv 64 0x1b894) fc None m (seg_rom s0segs)).
  Proof.
    intros hA w zzA tmp1 n1 nH nN me m t0 t1 t2 a6 t3 t4 t5 HnH HnN HzzA Htmp HW HEAP WGT MI MU WM K.
    hmenv_open XOK.
    pose proof (ovw_length hA Jh 260 ltac:(lia)) as LH. pose proof (ovw_length w Jw 516 ltac:(lia)) as LW.
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    pose proof (u32arr_store_ok s0segs m (p + 4152) _ zzA _ HEAP ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    wstep. store_addr (p + 4152 + 4 * zzA)%Z. ovw_store HEAP zzA tmp1 wval_lit.
    set (hp1 := zset hA zzA tmp1) in *.
    assert (HW1 : hw hp1 w (nH - 1) nN) by (subst hp1; apply hw_hset; [exact HW| lia| lia]).
    pose proof HW1 as HW0. cps_destruct HW0 as (S1 & S2 & HH & WW).
    pose proof (HH (nH - 1)%Z ltac:(lia)) as [Dn Rn]. pose proof (HH 1%Z ltac:(lia)) as [D1 R1].
    set (tmp2 := zget hp1 (nH - 1)) in *. set (n2 := zget hp1 1) in *.
    pose proof (WW tmp2 ltac:(lia)) as [Dwt Rwt].
    (* [comment removed for export] *)
    wstep.
    pose proof (ovw_read s0segs _ (p + 4152) hp1 Jh 260 (nH - 1) _ HEAP ltac:(lia) Dn ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. fold tmp2. try rewrite (sx32_of_Z tmp2) by lia.
    pose proof (ovw_read s0segs _ (p + 4152) hp1 Jh 260 1 _ HEAP ltac:(lia) D1 ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. fold n2. try rewrite (sx32_of_Z n2) by lia.
    pose proof (u32arr_store_ok s0segs _ (p + 4152) _ 1 _ HEAP ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO2.
    wstep. store_addr (p + 4152 + 4 * 1)%Z. ovw_store HEAP 1%Z tmp2 wval_lit.
    assert (HW2 : hw (zset hp1 1 tmp2) w (nH - 1) nN) by (apply hw_hset; [exact HW1| lia| lia]).
    (* [comment removed for export] *)
    wstep; if_cases Ks; zify_cond_z Ks.
    - (* [comment removed for export] *)
      enter_with (K (zset hp1 1 tmp2) 1%Z _ _ _ _ _ _ _); [st_eq| | lia| apply (hw_nH_le _ _ (nH - 1)); [exact HW2| lia]| exact HEAP| exact WGT| exact MI| exact MU| exact WM].
      apply downheap_loop_stop1. apply Z.ltb_lt. rewrite shiftl1_mul2. lia.
    - (* [comment removed for export] *)
      wstep. wstep.
      pose proof (ovw_read s0segs _ (p + 2088) w Jw 516 tmp2 _ WGT ltac:(lia) Dwt ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget w tmp2)) by lia.
      wstep. wstep. wstep.
      enter_with (S0_hm_down2 20%nat 1 (nH - 2) nN n1 n2 tmp2 (zset hp1 1 tmp2) w me); [st_eq| lia| lia| lia| cbn; lia| lia| lia| | exact HEAP| exact WGT| exact MI| exact MU| exact WM|].
      + apply (hw_nH_le _ _ (nH - 1)); [exact HW2| lia].
      + intros hB zzB m' x7 x28 x29 x30 E HzzB HWB HEAP' WGT' MI' MU' WM'.
        enter_with (K hB zzB m' _ _ x7 x28 x29 x30); [st_eq| exact E| lia| exact HWB| exact HEAP'| exact WGT'| exact MI'| exact MU'| exact WM'].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_hm_cnode : forall (hB w par : zarr) (zzB tmp2 n1 n2 nH nN : Z) (me m : word -> option byte)
      (t0 t1 t2 t3 t4 t5 : word),
    (2 <= nH <= 258)%Z -> (0 <= nN)%Z -> (nN + 1 <= 515)%Z -> (1 <= zzB <= nH - 1)%Z -> (0 <= tmp2 <= nN)%Z -> (0 <= n1 <= nN)%Z -> (0 <= n2 <= nN)%Z ->
    hw hB w (nH - 2) nN -> hpar par nN -> (weightof (zget w n1) + weightof (zget w n2) <= 2147483136)%Z ->
    u32arr s0segs m (p + 4152) (ovw hB Jh 260) -> u32arr s0segs m (p + 2088) (ovw w Jw 516) -> u32arr s0segs m (p + 24) (ovw par Jp 516) ->
    mem_inv s0segs m -> munch [(p + 24, p + 5192)]%Z me m -> wmono s0segs me m ->
    (forall hC zzC m' (t0 t1 t2 a3 a5 a6 a7 t3 : word),
      let aw := addweights (zget w n1) (zget w n2) in
      let w' := zset w (nN + 1) aw in
      let par' := zset (zset (zset par n2 (nN + 1)) n1 (nN + 1)) (nN + 1) (-1) in
      let h3 := zset (zset hB zzB tmp2) (nH - 1) (nN + 1) in
      upheap_loop 20 h3 w' (nH - 1) (nN + 1) = (hC, zzC) ->
      hw (zset hC zzC (nN + 1)) w' (nH - 1) (nN + 1) -> hpar par' (nN + 1) ->
      u32arr s0segs m' (p + 4152) (ovw (zset hC zzC (nN + 1)) Jh 260) -> u32arr s0segs m' (p + 2088) (ovw w' Jw 516) -> u32arr s0segs m' (p + 24) (ovw par' Jp 516) ->
      mem_inv s0segs m' -> munch [(p + 24, p + 5192)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RR RA t0 t1 t2 (Z_to_bv 64 nN) (Z_to_bv 64 nH) (Z_to_bv 64 (nH - 1)) a3 (Z_to_bv 64 (nN + 1)) a5 a6 a7 t3 t4 t5 (Z_to_bv 64 3))
                       F (Z_to_bv 64 0x1ba38) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RR RA t0 t1 t2 (Z_to_bv 64 nN) (Z_to_bv 64 nH) (Z_to_bv 64 (nH - 1)) (Z_to_bv 64 n1) (Z_to_bv 64 zzB)
                          (Z_to_bv 64 (p + 4152 + 4 * (nH - 1))) (Z_to_bv 64 tmp2) (Z_to_bv 64 n2) t3 t4 t5 (Z_to_bv 64 3))
                     F (Z_to_bv 64 0x1b958) fc None m (seg_rom s0segs)).
  Proof.
    intros hB w par zzB tmp2 n1 n2 nH nN me m t0 t1 t2 t3 t4 t5 HnH HnN HnN' HzzB Htmp Hn1 Hn2 HW HP RF HEAP WGT PAR MI MU WM K.
    hmenv_open XOK. pose proof HW as HW0. cps_destruct HW0 as (S1 & S2 & HH & WW).
    pose proof (ovw_length hB Jh 260 ltac:(lia)) as LH. pose proof (ovw_length w Jw 516 ltac:(lia)) as LW. pose proof (ovw_length par Jp 516 ltac:(lia)) as LP.
    pose proof (WW n1 ltac:(lia)) as [Dw1 Rw1]. pose proof (WW n2 ltac:(lia)) as [Dw2 Rw2].
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep.
    (* [comment removed for export] *)
    pose proof (u32arr_store_ok s0segs m (p + 4152) _ zzB _ HEAP ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    wstep. store_addr (p + 4152 + 4 * zzB)%Z. ovw_store HEAP zzB tmp2 wval_lit.
    set (hp2 := zset hB zzB tmp2) in *.
    (* [comment removed for export] *)
    wstep. wstep.
    pose proof (ovw_read s0segs _ (p + 2088) w Jw 516 n1 _ WGT ltac:(lia) Dw1 ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. try rewrite (sx32_of_Z (zget w n1)) by lia.
    pose proof (ovw_read s0segs _ (p + 2088) w Jw 516 n2 _ WGT ltac:(lia) Dw2 ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. try rewrite (sx32_of_Z (zget w n2)) by lia.
    (* [comment removed for export] *)
    wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm (p + 24) _ n2 _ PAR ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO2 end.
    wstep. store_addr (p + 24 + 4 * n2)%Z. ovw_store PAR n2 (nN + 1)%Z wval_lit.
    (* [comment removed for export] *)
    wstep. wstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm (p + 24) _ n1 _ PAR ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO3 end.
    wstep. store_addr (p + 24 + 4 * n1)%Z. ovw_store PAR n1 (nN + 1)%Z wval_lit.
    pose proof (depthof_range (zget w n1)) as Dr1. pose proof (depthof_range (zget w n2)) as Dr2.
    change (Z.land (zget w n1) 255) with (depthof (zget w n1)). change (Z.land (zget w n2) 255) with (depthof (zget w n2)).
    (* [comment removed for export] *)
    assert (TAIL : forall dm, dm = Z.max (depthof (zget w n1)) (depthof (zget w n2)) ->
      evt s0segs Q (MS (RR RA (Z_to_bv 64 (depthof (zget w n2))) (Z_to_bv 64 (p + 24 + n1 * 4)) (Z_to_bv 64 (p + 24 + n2 * 4))
                            (Z_to_bv 64 nN) (Z_to_bv 64 nH) (Z_to_bv 64 (nH - 1)) (Z_to_bv 64 (zget w n1)) (Z_to_bv 64 (nN + 1))
                            (Z_to_bv 64 (p + 4152 + 4 * (nH - 1))) (Z_to_bv 64 (zget w n2)) (Z_to_bv 64 dm) t3 t4 t5 (Z_to_bv 64 3))
                       F (Z_to_bv 64 0x1b9a0) fc None m0 (seg_rom s0segs))).
    { intros dm Edm.
      (* [comment removed for export] *)
      wstep. wstep. wstep.
      (* [comment removed for export] *)
      pose proof (u32arr_store_ok s0segs m0 (p + 4152) _ (nH - 1) _ HEAP ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO4.
      wstep. store_addr (p + 4152 + 4 * (nH - 1))%Z. ovw_store HEAP (nH - 1)%Z (nN + 1)%Z wval_lit.
      (* [comment removed for export] *)
      wstep. wstep. wstep. wstep.
      rewrite (addweights_compiled (zget w n1) (zget w n2) dm) by lia.
      set (aw := addweights (zget w n1) (zget w n2)) in *.
      assert (AWR : (0 <= aw < 2147483648)%Z) by (subst aw; apply addweights_range; lia).
      set (h3 := zset hp2 (nH - 1) (nN + 1)) in *.
      set (w' := zset w (nN + 1) aw) in *.
      assert (HW3 : hw h3 w' (nH - 1) (nN + 1)).
      { subst h3 w'. replace (nH - 1)%Z with (nH - 2 + 1)%Z by lia. apply hw_push; [|lia| lia]. apply hw_node; [|lia| exact AWR].
        subst hp2. apply hw_hset; [|lia| lia]. cps_destruct HW as (T1 & T2 & HHB & WWB). split; [exact T1|]. split; [exact T2|]. split; [exact HHB|].
        intros x Hx. destruct (WWB x ltac:(lia)). split; [assumption| lia]. }
      pose proof HW3 as HW3'. cps_destruct HW3' as (_ & _ & HH3 & WW3).
      assert (Hq : (0 <= (nH - 1) / 2 < nH - 1)%Z) by (Z.div_mod_to_equations; lia).
      pose proof (HH3 ((nH - 1) / 2)%Z ltac:(lia)) as [Dq Rq].
      (* [comment removed for export] *)
      wstep.
      pose proof (ovw_read s0segs _ (p + 4152) h3 Jh 260 ((nH - 1) / 2) _ HEAP ltac:(lia) Dq ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget h3 ((nH - 1) / 2))) by lia.
      (* [comment removed for export] *)
      wstep. wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u32arr_store_ok s0segs mm (p + 2088) _ (nN + 1) _ WGT ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO5 end.
      wstep. store_addr (p + 2088 + 4 * (nN + 1))%Z. ovw_store WGT (nN + 1)%Z aw wval_lit. fold w' in WGT.
      (* [comment removed for export] *)
      pose proof (WW3 (zget h3 ((nH - 1) / 2)) ltac:(lia)) as [Dw3 Rw3].
      wstep. wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (ovw_read s0segs mm (p + 2088) w' Jw 516 (zget h3 ((nH - 1) / 2)) _ WGT ltac:(lia) Dw3 ltac:(unfold wa; f_equal; lia)) as RD end.
      wstep. clear RD. try rewrite (sx32_of_Z (zget w' (zget h3 ((nH - 1) / 2)))) by lia.
      (* [comment removed for export] *)
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u32arr_store_ok s0segs mm (p + 24) _ (nN + 1) _ PAR ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO6 end.
      wstep. store_addr (p + 24 + 4 * (nN + 1))%Z. ovw_store PAR (nN + 1)%Z (-1)%Z (rewrite unsigned_lit_mod32; reflexivity).
      assert (HP' : hpar (zset (zset (zset par n2 (nN + 1)) n1 (nN + 1)) (nN + 1) (-1)) (nN + 1)).
      { apply hpar_node; [exact HP| lia| lia]. }
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mq end.
      assert (FIN : forall hC zzC m' (x15 x16 x5 x6 : word),
        upheap_loop 20 h3 w' (nH - 1) (nN + 1) = (hC, zzC) -> (1 <= zzC <= nH - 1)%Z -> hw hC w' (nH - 1) (nN + 1) ->
        u32arr s0segs m' (p + 4152) (ovw hC Jh 260) -> u32arr s0segs m' (p + 2088) (ovw w' Jw 516) -> mem_inv s0segs m' ->
        munch [(p + 4152, p + 5192)]%Z mq m' -> wmono s0segs mq m' ->
        evt s0segs Q (MS (RR RA x5 x6 (Z_to_bv 64 (p + 24 + n2 * 4)) (Z_to_bv 64 nN) (Z_to_bv 64 nH) (Z_to_bv 64 (nH - 1)) (Z_to_bv 64 aw) (Z_to_bv 64 (nN + 1))
                              x15 x16 (Z_to_bv 64 zzC) t3 t4 t5 (Z_to_bv 64 3))
                         F (Z_to_bv 64 0x1ba2c) fc None m' (seg_rom s0segs))).
      { intros hC zzC m' x15 x16 x5 x6 E HzzC HWC HEAP' WGT' MI' MU' WM'.
        clear HEAP WGT. transport_after_call s0segs mq m' MU' WM'.
        pose proof (ovw_length hC Jh 260 ltac:(lia)) as LHC.
        wstep. wstep.
        pose proof (u32arr_store_ok s0segs m' (p + 4152) _ zzC _ HEAP' ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO7.
        wstep. store_addr (p + 4152 + 4 * zzC)%Z. ovw_store HEAP' zzC (nN + 1)%Z wval_lit.
        enter_with (K hC zzC _ _ _ _ _ _ _ _ _); [st_eq| exact E| apply hw_hset; [exact HWC| lia| lia]| exact HP'| exact HEAP'| exact WGT'| exact PAR| exact MI'| exact MU| exact WM]. }
      (* [comment removed for export] *)
      wstep; if_cases Kc; zify_cond_z Kc.
      - (* [comment removed for export] *)
        wstep. enter_with (FIN h3 (nH - 1)%Z _ _ _ _ _); [st_eq| | lia| exact HW3| exact HEAP| exact WGT| exact MI| apply munch_refl| apply wmono_refl].
        apply upheap_loop_stop. rewrite shiftr1_div2. apply Z.ltb_ge. subst w'. rewrite zget_zset_same. lia.
      - (* [comment removed for export] *)
        wstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (S0_hm_up2 20%nat (nH - 1) (nH - 1) (nN + 1) h3 w' mm mm) end;
          [st_eq| lia| lia| cbn; lia| lia| | exact HW3| exact HEAP| exact WGT| exact MI| apply munch_refl| apply wmono_refl|].
        + subst w'. cbv delta [mkR]. rewrite zget_zset_same. reflexivity.
        + rewrite shiftr1_div2. subst w'. rewrite zget_zset_same. apply Z.ltb_lt. lia.
        + intros hC zzC m' x15 x16 x6 E HzzC HWC HEAP' WGT' MI' MU' WM'. subst w'. rewrite zget_zset_same.
          enter_with (FIN hC zzC m' x15 x16 (Z_to_bv 64 zzC) x6); [st_eq| exact E| exact HzzC| exact HWC| exact HEAP'| exact WGT'| exact MI'| exact MU'| exact WM']. }
    (* [comment removed for export] *)
    wstep; if_cases Kd; zify_cond_z Kd.
    - enter_with (TAIL (depthof (zget w n1))); [st_eq| symmetry; apply Z.max_l; lia].
    - wstep. enter_with (TAIL (depthof (zget w n2))); [st_eq| symmetry; apply Z.max_r; lia].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_hm_combine : forall (n : nat) (h w par : zarr) (nH nN : Z) (me m : word -> option byte)
      (t0 t1 t2 a0 a1 a3 a5 a6 a7 t3 t4 t5 : word),
    let s := HMS h w par nH nN in
    (nH = Z.of_nat n + 1)%Z -> (1 <= n)%nat -> (nH <= A)%Z -> (A <= nN)%Z -> (nN + Z.of_nat n <= 515)%Z ->
    hw h w nH nN -> hpar par nN ->
    (forall j, (j < n)%nat -> rf_cb (Nat.iter j hm_combine_iter s)) ->
    u32arr s0segs m (p + 4152) (ovw h Jh 260) -> u32arr s0segs m (p + 2088) (ovw w Jw 516) -> u32arr s0segs m (p + 24) (ovw par Jp 516) ->
    mem_inv s0segs m -> munch [(p + 24, p + 5192)]%Z me m -> wmono s0segs me m ->
    (forall h' w' par' nN' m' (t0 t1 t2 a3 a5 a6 a7 t3 t4 t5 : word),
      Nat.iter n hm_combine_iter s = HMS h' w' par' 1 nN' -> (nN' = nN + Z.of_nat n)%Z ->
      hw h' w' 1 nN' -> hpar par' nN' ->
      u32arr s0segs m' (p + 4152) (ovw h' Jh 260) -> u32arr s0segs m' (p + 2088) (ovw w' Jw 516) -> u32arr s0segs m' (p + 24) (ovw par' Jp 516) ->
      mem_inv s0segs m' -> munch [(p + 24, p + 5192)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RR RA t0 t1 t2 (Z_to_bv 64 (nN' - 1)) (Z_to_bv 64 2) (Z_to_bv 64 1) a3 (Z_to_bv 64 nN') a5 a6 a7 t3 t4 t5 (Z_to_bv 64 3))
                       F (Z_to_bv 64 0x1ba3c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RR RA t0 t1 t2 a0 a1 (Z_to_bv 64 nH) a3 (Z_to_bv 64 nN) a5 a6 a7 t3 t4 t5 (Z_to_bv 64 3))
                     F (Z_to_bv 64 0x1b7cc) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros h w par nH nN me m t0 t1 t2 a0 a1 a3 a5 a6 a7 t3 t4 t5 s HnH Hn HA HAN HN HW HP FACTS HEAP WGT PAR MI MU WM K. subst s.
    hmenv_open XOK.
    pose proof HW as HW0. cps_destruct HW0 as (S1 & S2 & HH & WW).
    pose proof (HH nH ltac:(lia)) as [_ Rt1]. pose proof (HH 1%Z ltac:(lia)) as [_ Rn1].
    eapply (S0_hm_cpop1 h w nH nN m m); [lia| lia| exact HW| exact HEAP| exact WGT| exact MI| apply munch_refl| apply wmono_refl|].
    intros hA zzA m1 x5 x6 x7 x16 x28 E1 HzzA HWA HEAP1 WGT1 MI1 MU1 WM1.
    clear HEAP WGT MI. transport_after_call s0segs m m1 MU1 WM1.
    pose proof HWA as HW0. cps_destruct HW0 as (_ & _ & HHA & _).
    eapply (S0_hm_cpop2 hA w zzA (zget h nH) (zget h 1) nH nN m1 m1); [lia| lia| lia| lia| exact HWA| exact HEAP1| exact WGT1| exact MI1| apply munch_refl| apply wmono_refl|].
    intros hB zzB m2 y5 y6 y7 y28 y29 y30. cbv zeta. intros E2 HzzB HWB HEAP2 WGT2 MI2 MU2 WM2.
    clear HEAP1 WGT1 MI1 MU1 WM1. transport_after_call s0segs m1 m2 MU2 WM2.
    set (hp1 := zset hA zzA (zget h nH)) in *.
    assert (HW1 : hw hp1 w (nH - 1) nN) by (subst hp1; apply hw_hset; [exact HWA| lia| lia]).
    cps_destruct HW1 as (_ & _ & HH1 & _). pose proof (HH1 (nH - 1)%Z ltac:(lia)) as [_ Rt2]. pose proof (HH1 1%Z ltac:(lia)) as [_ Rn2].
    cps_destruct (combine_iter_link1 h w par nH nN hA zzA E1) as (_ & N1 & N2 & EW & EP). cbv zeta in N1, N2, EW, EP. fold hp1 in N2, EW, EP.
    pose proof (FACTS 0%nat ltac:(lia)) as RF0. cbn [Nat.iter nat_rect] in RF0. unfold rf_cb in RF0. rewrite N1, N2 in RF0. cbn [hm_weight] in RF0.
    eapply (S0_hm_cnode hB w par zzB (zget hp1 (nH - 1)) (zget h 1) (zget hp1 1) nH nN me m2);
      [lia| lia| lia| lia| lia| lia| lia| exact HWB| exact HP| exact RF0| exact HEAP2| exact WGT2| exact PAR| exact MI2| exact MU| exact WM|].
    intros hC zzC m3 z5 z6 z7 z13 z15 z16 z17 z28. cbv zeta. intros E3 HWC HPC HEAP3 WGT3 PAR3 MI3 MU3 WM3.
    clear HEAP2 WGT2 PAR MI2 MU2 WM2 MU WM.
    pose proof (combine_iter_link h w par nH nN hA zzA hB zzB hC zzC E1 E2 E3) as IT. cbv zeta in IT.
    rewrite <- EW in HWC, WGT3. rewrite <- EP in HPC, PAR3.
    (* [comment removed for export] *)
    wstep; if_cases Kl; zify_cond_z Kl.
    - enter_with (IH (zset hC zzC (nN + 1)) (cb_w' (HMS h w par nH nN)) (cb_p' (HMS h w par nH nN)) (nH - 1)%Z (nN + 1)%Z me m3);
        [st_eq| lia| lia| lia| lia| lia| exact HWC| exact HPC| | exact HEAP3| exact WGT3| exact PAR3| exact MI3| exact MU3| exact WM3|].
      + intros j Hj. rewrite <- IT, <- iter_S_r. apply FACTS. lia.
      + intros h' w' par' nN' m' q5 q6 q7 q13 q15 q16 q17 q28 q29 q30 ITn HnN' HW' HP' HE' WG' PA' MI' MU' WM'.
        apply (K h' w' par' nN' m' q5 q6 q7 q13 q15 q16 q17 q28 q29 q30); [rewrite iter_S_r, IT; exact ITn| lia| exact HW'| exact HP'| exact HE'| exact WG'| exact PA'| exact MI'| exact MU'| exact WM'].
    - assert (n = 0)%nat by lia. subst n.
      enter_with (K (zset hC zzC (nN + 1)) (cb_w' (HMS h w par nH nN)) (cb_p' (HMS h w par nH nN)) (nN + 1)%Z m3 _ _ _ _ _ _ _ _ _ _);
        [st_eq| | lia| exact (eq_rect _ (fun k => hw (zset hC zzC (nN + 1)) (cb_w' (HMS h w par nH nN)) k (nN + 1)) HWC 1%Z ltac:(lia))| exact HPC| exact HEAP3| exact WGT3| exact PAR3| exact MI3| exact MU3| exact WM3].
      cbn [Nat.iter nat_rect]. rewrite IT. f_equal. lia.
  Qed.
End S0HM.

End ACeilS1.
