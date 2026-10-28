(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzCHuff BzCHuffF1 BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCut CmpCut0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF1.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpFsKit0 CmpHmKit.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.BzCFactsHm OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpFsKit0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpHmKit.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7_all.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
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
  Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).
  Notation RR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 (p - 32)) gp tp t0 t1 t2 (NOT (p + 24)) (NOT (p + 2088)) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 (El + lb)) (Z_to_bv 64 (p + 4152)) (Z_to_bv 64 515) (Z_to_bv 64 (p + 2088)) (Z_to_bv 64 (p + 24))
         (Z_to_bv 64 (A + 1)) (Z_to_bv 64 516) (Z_to_bv 64 259) (NOT (p + 4152)) (Z_to_bv 64 129) t3 t4 t5 t6).
  Notation RA := (Z_to_bv 64 17).

  Lemma lor_even1 : forall z, (0 <= z)%Z -> Z.lor (z * 2) 1 = (z * 2 + 1)%Z.
  Proof.
    intros z Hz. pose proof (Z.add_lor_land (z * 2) 1) as E.
    assert (L : Z.land (z * 2) 1 = 0%Z); [|lia].
    rewrite land1_mod2. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_hm_down1 : forall (f : nat) (zz nHq nN tmp : Z) (h w : zarr) (me m : word -> option byte)
      (t0 a2 a3 a5 t3 t4 t5 t6 : word),
    (1 <= zz)%Z -> (zz * 2 <= nHq)%Z -> (nHq <= 258)%Z -> (nHq < zz * 2 ^ Z.of_nat f)%Z -> (0 <= nN <= 515)%Z ->
    (0 <= tmp <= nN)%Z -> hw h w nHq nN ->
    u32arr s0segs m (p + 4152) (ovw h Jh 260) -> u32arr s0segs m (p + 2088) (ovw w Jw 516) -> mem_inv s0segs m ->
    munch [(p + 4152, p + 5192)]%Z me m -> wmono s0segs me m ->
    (forall h' zz' m' (t1 t2 t3 t4 : word),
      downheap_loop f h w nHq zz tmp = (h', zz') -> (1 <= zz' <= nHq)%Z -> hw h' w nHq nN ->
      u32arr s0segs m' (p + 4152) (ovw h' Jh 260) -> u32arr s0segs m' (p + 2088) (ovw w Jw 516) -> mem_inv s0segs m' ->
      munch [(p + 4152, p + 5192)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RR RA (Z_to_bv 64 zz') t1 t2 (Z_to_bv 64 (nHq + 1)) (Z_to_bv 64 nHq) a2 a3 (Z_to_bv 64 tmp) a5 (Z_to_bv 64 (tmp * 4)) (Z_to_bv 64 (p + 2088 + tmp * 4)) t3 t4 t5 t6)
                       F (Z_to_bv 64 0x23ec8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RR RA t0 (Z_to_bv 64 zz) (Z_to_bv 64 (zz * 2)) (Z_to_bv 64 (nHq + 1)) (Z_to_bv 64 nHq) a2 a3 (Z_to_bv 64 tmp) a5 (Z_to_bv 64 (tmp * 4)) (Z_to_bv 64 (p + 2088 + tmp * 4)) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x23e18) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH]. { intros. cbn in H2. lia. }
    intros zz nHq nN tmp h w me m t0 a2 a3 a5 t3 t4 t5 t6 Hzz Hyy HnH Hf HnN Htmp HW HEAP WGT MI MU WM K.
    hmenv_open XOK. cps_destruct HW as (S1 & S2 & HH & WW).
    pose proof (ovw_length h Jh 260 ltac:(lia)) as LH. pose proof (ovw_length w Jw 516 ltac:(lia)) as LW.
    pose proof (WW tmp ltac:(lia)) as [Dwt Rwt].
    (* [comment removed for export] *)
    assert (TAIL : forall yy' (x3 x4 : word), yy' = dh_child h w nHq (zz * 2) -> (zz * 2 <= yy' <= nHq)%Z -> (yy' <= zz * 2 + 1)%Z ->
      evt s0segs Q (MS (RR RA (Z_to_bv 64 yy') (Z_to_bv 64 zz) (Z_to_bv 64 (zz * 2)) (Z_to_bv 64 (nHq + 1)) (Z_to_bv 64 nHq) a2 a3 (Z_to_bv 64 tmp) a5 (Z_to_bv 64 (tmp * 4)) (Z_to_bv 64 (p + 2088 + tmp * 4)) x3 x4 t5 t6)
                       F (Z_to_bv 64 0x23e68) fc None m (seg_rom s0segs))).
    { intros yy' x3 x4 Eyy Hyy' Hyy2.
      pose proof (HH yy' ltac:(lia)) as [Dy Ry]. pose proof (WW (zget h yy') ltac:(lia)) as [Dwy Rwy].
      (* [comment removed for export] *)
      wstep; notrap. wstep; notrap. wstep; notrap. wstep. wstep; notrap. wstep.
      pose proof (ovw_read s0segs _ (p + 4152) h Jh 260 yy' _ HEAP ltac:(lia) Dy ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget h yy')) by lia.
      (* [comment removed for export] *)
      wstep; notrap. wstep. wstep; notrap. wstep.
      pose proof (ovw_read s0segs _ (p + 2088) w Jw 516 tmp _ WGT ltac:(lia) Dwt ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget w tmp)) by lia.
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
        assert (HW1 : hw (zset h zz (zget h yy')) w nHq nN) by (apply hw_hset; [exact (conj S1 (conj S2 (conj HH WW)))| lia| lia]).
        (* [comment removed for export] *)
        wstep. wstep; if_cases Kl; zify_cond_z Kl.
        + enter_with (IH yy' nHq nN tmp (zset h zz (zget h yy')) w me); [st_eq| lia| lia| lia| | lia| lia| exact HW1| exact HEAP| exact WGT| exact MI| exact MU| exact WM|].
          * rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hf by lia.
            (* [comment removed for export] *)
            eapply Z.lt_le_trans; [exact Hf|]. rewrite Z.mul_assoc.
            apply Z.mul_le_mono_nonneg_r; [apply Z.pow_nonneg; discriminate | exact (proj1 Hyy')].
          * intros h' zz' m' y1 y2 y3 y4 E Hzz' HW'. eapply K; [| lia| exact HW'].
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
      wstep. enter_with (TAIL (zz * 2)%Z t3 t4); [st_eq| | lia| lia].
      unfold dh_child. replace (zz * 2 <? nHq)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
    - (* [comment removed for export] *)
      pose proof (HH (zz * 2)%Z ltac:(lia)) as [D0 R0]. pose proof (HH (zz * 2 + 1)%Z ltac:(lia)) as [D1 R1].
      pose proof (WW (zget h (zz * 2)) ltac:(lia)) as [Dw0 Rw0]. pose proof (WW (zget h (zz * 2 + 1)) ltac:(lia)) as [Dw1 Rw1].
      wstep. rewrite lor_even1 by lia. wstep. wstep.
      pose proof (ovw_read s0segs _ (p + 4152) h Jh 260 (zz * 2 + 1) _ HEAP ltac:(lia) D1 ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget h (zz * 2 + 1))) by lia.
      wstep; notrap. wstep. wstep; notrap. wstep. wstep.
      pose proof (ovw_read s0segs _ (p + 4152) h Jh 260 (zz * 2) _ HEAP ltac:(lia) D0 ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget h (zz * 2))) by lia.
      wstep; notrap. wstep. wstep; notrap. wstep. wstep.
      pose proof (ovw_read s0segs _ (p + 2088) w Jw 516 (zget h (zz * 2 + 1)) _ WGT ltac:(lia) Dw1 ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget w (zget h (zz * 2 + 1)))) by lia.
      pose proof (ovw_read s0segs _ (p + 2088) w Jw 516 (zget h (zz * 2)) _ WGT ltac:(lia) Dw0 ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget w (zget h (zz * 2)))) by lia.
      (* [comment removed for export] *)
      wstep; if_cases Kw; zify_cond_z Kw.
      + (* [comment removed for export] *)
        enter_with (TAIL (zz * 2 + 1)%Z _ _); [st_eq| | lia| lia].
        unfold dh_child. replace (zz * 2 <? nHq)%Z with true by (symmetry; apply Z.ltb_lt; lia).
        replace (zget w (zget h (zz * 2 + 1)) <? zget w (zget h (zz * 2)))%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
      + (* [comment removed for export] *)
        wstep. enter_with (TAIL (zz * 2)%Z _ _); [st_eq| | lia| lia].
        unfold dh_child. replace (zz * 2 <? nHq)%Z with true by (symmetry; apply Z.ltb_lt; lia).
        replace (zget w (zget h (zz * 2 + 1)) <? zget w (zget h (zz * 2)))%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_hm_down2 : forall (f : nat) (zz nHq nN tmp : Z) (h w : zarr) (me m : word -> option byte)
      (t2 a0 a1 a2 a3 a4 a6 t5 t6 : word),
    (1 <= zz)%Z -> (zz * 2 <= nHq)%Z -> (nHq <= 258)%Z -> (nHq < zz * 2 ^ Z.of_nat f)%Z -> (0 <= nN <= 515)%Z ->
    (0 <= tmp <= nN)%Z -> hw h w nHq nN ->
    u32arr s0segs m (p + 4152) (ovw h Jh 260) -> u32arr s0segs m (p + 2088) (ovw w Jw 516) -> mem_inv s0segs m ->
    munch [(p + 4152, p + 5192)]%Z me m -> wmono s0segs me m ->
    (forall h' zz' m' (t3 t4 t5 t6 : word),
      downheap_loop f h w nHq zz tmp = (h', zz') -> (1 <= zz' <= nHq)%Z -> hw h' w nHq nN ->
      u32arr s0segs m' (p + 4152) (ovw h' Jh 260) -> u32arr s0segs m' (p + 2088) (ovw w Jw 516) -> mem_inv s0segs m' ->
      munch [(p + 4152, p + 5192)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RR RA (Z_to_bv 64 (tmp * 4)) (Z_to_bv 64 (p + 2088 + tmp * 4)) (Z_to_bv 64 zz') a0 a1 a2 a3 a4 (Z_to_bv 64 nHq) a6 (Z_to_bv 64 tmp) t3 t4 t5 t6)
                       F (Z_to_bv 64 0x23fc8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RR RA (Z_to_bv 64 (tmp * 4)) (Z_to_bv 64 (p + 2088 + tmp * 4)) t2 a0 a1 a2 a3 a4 (Z_to_bv 64 nHq) a6 (Z_to_bv 64 tmp) (Z_to_bv 64 zz) (Z_to_bv 64 (zz * 2)) t5 t6)
                     F (Z_to_bv 64 0x23f14) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH]. { intros. cbn in H2. lia. }
    intros zz nHq nN tmp h w me m t2 a0 a1 a2 a3 a4 a6 t5 t6 Hzz Hyy HnH Hf HnN Htmp HW HEAP WGT MI MU WM K.
    hmenv_open XOK. cps_destruct HW as (S1 & S2 & HH & WW).
    pose proof (ovw_length h Jh 260 ltac:(lia)) as LH. pose proof (ovw_length w Jw 516 ltac:(lia)) as LW.
    pose proof (WW tmp ltac:(lia)) as [Dwt Rwt].
    (* [comment removed for export] *)
    assert (TAIL : forall yy' (x5 x6 : word), yy' = dh_child h w nHq (zz * 2) -> (zz * 2 <= yy' <= nHq)%Z -> (yy' <= zz * 2 + 1)%Z ->
      evt s0segs Q (MS (RR RA (Z_to_bv 64 (tmp * 4)) (Z_to_bv 64 (p + 2088 + tmp * 4)) (Z_to_bv 64 yy') a0 a1 a2 a3 a4 (Z_to_bv 64 nHq) a6 (Z_to_bv 64 tmp) (Z_to_bv 64 zz) (Z_to_bv 64 (zz * 2)) x5 x6)
                       F (Z_to_bv 64 0x23f6c) fc None m (seg_rom s0segs))).
    { intros yy' x5 x6 Eyy Hyy' Hyy2.
      pose proof (HH yy' ltac:(lia)) as [Dy Ry]. pose proof (WW (zget h yy') ltac:(lia)) as [Dwy Rwy].
      (* [comment removed for export] *)
      wstep; notrap. wstep; notrap. wstep; notrap. wstep. wstep; notrap. wstep.
      pose proof (ovw_read s0segs _ (p + 4152) h Jh 260 yy' _ HEAP ltac:(lia) Dy ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget h yy')) by lia.
      (* [comment removed for export] *)
      wstep; notrap. wstep. wstep; notrap. wstep.
      pose proof (ovw_read s0segs _ (p + 2088) w Jw 516 tmp _ WGT ltac:(lia) Dwt ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget w tmp)) by lia.
      pose proof (ovw_read s0segs _ (p + 2088) w Jw 516 (zget h yy') _ WGT ltac:(lia) Dwy ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget w (zget h yy'))) by lia.
      (* [comment removed for export] *)
      wstep; if_cases Kb; zify_cond_z Kb.
      - (* [comment removed for export] *)
        wstep.
        enter_with (K h zz m _ _ _ _); [st_eq| | lia| exact (conj S1 (conj S2 (conj HH WW)))| exact HEAP| exact WGT| exact MI| exact MU| exact WM].
        apply downheap_loop_stop2; [apply Z.ltb_ge; rewrite shiftl1_mul2; lia|]. rewrite shiftl1_mul2, <- Eyy. apply Z.ltb_lt. exact Kb.
      - (* [comment removed for export] *)
        wstep. wstep; notrap. wstep. wstep.
        pose proof (u32arr_store_ok s0segs m (p + 4152) _ zz _ HEAP ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
        wstep. store_addr (p + 4152 + 4 * zz)%Z. ovw_store HEAP zz (zget h yy') wval_lit.
        assert (HW1 : hw (zset h zz (zget h yy')) w nHq nN) by (apply hw_hset; [exact (conj S1 (conj S2 (conj HH WW)))| lia| lia]).
        (* [comment removed for export] *)
        wstep. wstep; if_cases Kl; zify_cond_z Kl.
        + enter_with (IH yy' nHq nN tmp (zset h zz (zget h yy')) w me); [st_eq| lia| lia| lia| | lia| lia| exact HW1| exact HEAP| exact WGT| exact MI| exact MU| exact WM|].
          * rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hf by lia.
            eapply Z.lt_le_trans; [exact Hf|]. rewrite Z.mul_assoc.
            apply Z.mul_le_mono_nonneg_r; [apply Z.pow_nonneg; discriminate | exact (proj1 Hyy')].
          * intros h' zz' m' y3 y4 y5 y6 E Hzz' HW'. eapply K; [| lia| exact HW'].
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
      wstep. enter_with (TAIL (zz * 2)%Z t5 t6); [st_eq| | lia| lia].
      unfold dh_child. replace (zz * 2 <? nHq)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
    - (* [comment removed for export] *)
      pose proof (HH (zz * 2)%Z ltac:(lia)) as [D0 R0]. pose proof (HH (zz * 2 + 1)%Z ltac:(lia)) as [D1 R1].
      pose proof (WW (zget h (zz * 2)) ltac:(lia)) as [Dw0 Rw0]. pose proof (WW (zget h (zz * 2 + 1)) ltac:(lia)) as [Dw1 Rw1].
      wstep; notrap.
      wstep. rewrite lor_even1 by lia. wstep. wstep; notrap. wstep.
      pose proof (ovw_read s0segs _ (p + 4152) h Jh 260 (zz * 2 + 1) _ HEAP ltac:(lia) D1 ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget h (zz * 2 + 1))) by lia.
      wstep; notrap. wstep. wstep; notrap. wstep. wstep.
      pose proof (ovw_read s0segs _ (p + 4152) h Jh 260 (zz * 2) _ HEAP ltac:(lia) D0 ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget h (zz * 2))) by lia.
      wstep; notrap. wstep. wstep; notrap. wstep. wstep.
      pose proof (ovw_read s0segs _ (p + 2088) w Jw 516 (zget h (zz * 2 + 1)) _ WGT ltac:(lia) Dw1 ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget w (zget h (zz * 2 + 1)))) by lia.
      pose proof (ovw_read s0segs _ (p + 2088) w Jw 516 (zget h (zz * 2)) _ WGT ltac:(lia) Dw0 ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget w (zget h (zz * 2)))) by lia.
      (* [comment removed for export] *)
      wstep; if_cases Kw; zify_cond_z Kw.
      + (* [comment removed for export] *)
        enter_with (TAIL (zz * 2 + 1)%Z _ _); [st_eq| | lia| lia].
        unfold dh_child. replace (zz * 2 <? nHq)%Z with true by (symmetry; apply Z.ltb_lt; lia).
        replace (zget w (zget h (zz * 2 + 1)) <? zget w (zget h (zz * 2)))%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
      + (* [comment removed for export] *)
        wstep. enter_with (TAIL (zz * 2)%Z _ _); [st_eq| | lia| lia].
        unfold dh_child. replace (zz * 2 <? nHq)%Z with true by (symmetry; apply Z.ltb_lt; lia).
        replace (zget w (zget h (zz * 2 + 1)) <? zget w (zget h (zz * 2)))%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_hm_up2 : forall (f : nat) (zz nHm nNq : Z) (h w : zarr) (me m : word -> option byte)
      (t0 t1 t2 a0 a1 a4 a7 t3 t4 t5 t6 : word),
    (1 <= zz <= nHm)%Z -> (nHm <= 258)%Z -> (zz < 2 ^ Z.of_nat f)%Z -> (1 <= nNq <= 515)%Z ->
    hw h w nHm nNq ->
    u32arr s0segs m (p + 4152) (ovw h Jh 260) -> u32arr s0segs m (p + 2088) (ovw w Jw 516) -> mem_inv s0segs m ->
    munch [(p + 4152, p + 5192)]%Z me m -> wmono s0segs me m ->
    (forall h' zz' m' (t0 a4 a6 a7 : word),
      upheap_loop f h w zz nNq = (h', zz') -> (1 <= zz' <= zz)%Z -> hw h' w nHm nNq ->
      u32arr s0segs m' (p + 4152) (ovw h' Jh 260) -> u32arr s0segs m' (p + 2088) (ovw w Jw 516) -> mem_inv s0segs m' ->
      munch [(p + 4152, p + 5192)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RR RA t0 t1 t2 a0 a1 (Z_to_bv 64 (zget w nNq)) (Z_to_bv 64 zz') a4 (Z_to_bv 64 nNq) a6 a7 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x240cc) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RR RA t0 t1 t2 a0 a1 (Z_to_bv 64 (zget w nNq)) (Z_to_bv 64 zz) a4 (Z_to_bv 64 nNq) (Z_to_bv 64 (zz / 2)) a7 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x2407c) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH].
    { intros. cbn in H1. lia. }
    intros zz nHm nNq h w me m t0 t1 t2 a0 a1 a4 a7 t3 t4 t5 t6 Hzz HnH Hf HnN HW HEAP WGT MI MU WM K.
    hmenv_open XOK. pose proof HW as HW0. cps_destruct HW0 as (S1 & S2 & HH & WW).
    assert (Hz2 : (0 <= zz / 2 < zz)%Z) by (Z.div_mod_to_equations; lia).
    pose proof (HH (zz / 2)%Z ltac:(lia)) as [Dp Rp]. pose proof (WW nNq ltac:(lia)) as [Dwi Rwi]. pose proof (WW (zget h (zz / 2)) ltac:(lia)) as [Dwp Rwp].
    pose proof (ovw_length h Jh 260 ltac:(lia)) as LH. pose proof (ovw_length w Jw 516 ltac:(lia)) as LW.
    (* [comment removed for export] *)
    wstep. wstep.
    pose proof (ovw_read s0segs _ (p + 4152) h Jh 260 (zz / 2) _ HEAP ltac:(lia) Dp ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. try rewrite (sx32_of_Z (zget h (zz / 2))) by lia.
    (* [comment removed for export] *)
    wstep; notrap. wstep. wstep. wstep; notrap. wstep.
    pose proof (ovw_read s0segs _ (p + 2088) w Jw 516 (zget h (zz / 2)) _ WGT ltac:(lia) Dwp ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. try rewrite (sx32_of_Z (zget w (zget h (zz / 2)))) by lia.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      enter_with (K h zz m _ _ _ _); [st_eq| | lia| exact HW| exact HEAP| exact WGT| exact MI| exact MU| exact WM].
      apply upheap_loop_stop. rewrite shiftr1_div2. apply Z.ltb_ge. lia.
    - (* [comment removed for export] *)
      assert (Hzz2 : (2 <= zz)%Z).
      { destruct (Z_lt_le_dec zz 2); [|assumption]. exfalso. replace (zz / 2)%Z with 0%Z in Kc by (Z.div_mod_to_equations; lia).
        rewrite S1, S2 in Kc. lia. }
      wstep; notrap. wstep. wstep; notrap. wstep. wstep. wstep.
      pose proof (u32arr_store_ok s0segs m (p + 4152) _ zz _ HEAP ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
      wstep. store_addr (p + 4152 + 4 * zz)%Z. ovw_store HEAP zz (zget h (zz / 2))%Z wval_lit.
      assert (HW1 : hw (zset h zz (zget h (zz / 2))) w nHm nNq) by (apply hw_hset; [exact HW| lia| lia]).
      assert (B : (zz / 2 / 2 * 4 <= zz)%Z) by (Z.div_mod_to_equations; lia).
      (* [comment removed for export] *)
      wstep. wstep; notrap.
      try rewrite !shiftr1_div2.
      enter_with (IH (zz / 2)%Z nHm nNq (zset h zz (zget h (zz / 2))) w me); [st_eq| lia| lia| | lia| exact HW1| exact HEAP| exact WGT| exact MI| exact MU| exact WM|].
      + rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hf by lia. apply Z.div_lt_upper_bound; lia.
      + intros h' zz' m' y0 y4 y6 y7 E Hzz' HW'. eapply K; [| lia| exact HW'].
        rewrite upheap_loop_S, shiftr1_div2. replace (zget w nNq <? zget w (zget h (zz / 2)))%Z with true by (symmetry; apply Z.ltb_lt; lia). exact E.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_hm_cpop1 : forall (h w : zarr) (nH nN : Z) (me m : word -> option byte)
      (t0 t1 t2 a0 a1 a2 a4 a6 a7 t3 t4 t5 t6 : word),
    (2 <= nH <= 258)%Z -> (0 <= nN <= 515)%Z -> hw h w nH nN ->
    u32arr s0segs m (p + 4152) (ovw h Jh 260) -> u32arr s0segs m (p + 2088) (ovw w Jw 516) -> mem_inv s0segs m ->
    munch [(p + 4152, p + 5192)]%Z me m -> wmono s0segs me m ->
    (forall hA zzA m' (t1 t2 a6 a7 t3 t4 : word),
      downheap_loop 20 (zset h 1 (zget h nH)) w (nH - 1) 1 (zget h nH) = (hA, zzA) -> (1 <= zzA <= nH - 1)%Z -> hw hA w (nH - 1) nN ->
      u32arr s0segs m' (p + 4152) (ovw hA Jh 260) -> u32arr s0segs m' (p + 2088) (ovw w Jw 516) -> mem_inv s0segs m' ->
      munch [(p + 4152, p + 5192)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RR RA (Z_to_bv 64 zzA) t1 t2 (Z_to_bv 64 nH) (Z_to_bv 64 (nH - 1)) (Z_to_bv 64 (zget h 1)) (Z_to_bv 64 nN) (Z_to_bv 64 (zget h nH)) (Z_to_bv 64 nH) a6 a7 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x23ec8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RR RA t0 t1 t2 a0 a1 a2 (Z_to_bv 64 nN) a4 (Z_to_bv 64 nH) a6 a7 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x23de4) fc None m (seg_rom s0segs)).
  Proof.
    intros h w nH nN me m t0 t1 t2 a0 a1 a2 a4 a6 a7 t3 t4 t5 t6 HnH HnN HW HEAP WGT MI MU WM K.
    hmenv_open XOK. pose proof HW as HW0. cps_destruct HW0 as (S1 & S2 & HH & WW).
    pose proof (ovw_length h Jh 260 ltac:(lia)) as LH. pose proof (ovw_length w Jw 516 ltac:(lia)) as LW.
    pose proof (HH nH ltac:(lia)) as [Dn Rn]. pose proof (HH 1%Z ltac:(lia)) as [D1 R1].
    set (tmp1 := zget h nH) in *. set (n1 := zget h 1) in *.
    pose proof (WW tmp1 ltac:(lia)) as [Dwt Rwt].
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    pose proof (ovw_read s0segs _ (p + 4152) h Jh 260 nH _ HEAP ltac:(lia) Dn ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. fold tmp1. try rewrite (sx32_of_Z tmp1) by lia.
    (* [comment removed for export] *)
    pose proof (ovw_read s0segs _ (p + 4152) h Jh 260 1 _ HEAP ltac:(lia) D1 ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. fold n1. try rewrite (sx32_of_Z n1) by lia.
    (* [comment removed for export] *)
    pose proof (u32arr_store_ok s0segs m (p + 4152) _ 1 _ HEAP ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    wstep. store_addr (p + 4152 + 4 * 1)%Z. ovw_store HEAP 1%Z tmp1 wval_lit.
    assert (HW1 : hw (zset h 1 tmp1) w (nH - 1) nN).
    { apply (hw_nH_le _ _ nH); [|lia]. apply hw_hset; [exact HW| lia| lia]. }
    (* [comment removed for export] *)
    wstep. wstep. wstep; if_cases Ks; zify_cond_z Ks.
    - (* [comment removed for export] *)
      wstep. wstep.
      enter_with (K (zset h 1 tmp1) 1%Z _ _ _ _ _ _ _); [st_eq| | lia| exact HW1| exact HEAP| exact WGT| exact MI| exact MU| exact WM].
      apply downheap_loop_stop1. apply Z.ltb_lt. rewrite shiftl1_mul2. lia.
    - (* [comment removed for export] *)
      wstep. wstep. wstep. wstep.
      enter_with (S0_hm_down1 20%nat 1 (nH - 1) nN tmp1 (zset h 1 tmp1) w me); [st_eq| lia| lia| lia| cbn; lia| lia| lia| exact HW1| exact HEAP| exact WGT| exact MI| exact MU| exact WM|].
      intros hA zzA m' x1 x2 x3 x4 E HzzA HWA HEAP' WGT' MI' MU' WM'.
      enter_with (K hA zzA m' _ _ _ _ _ _); [st_eq| exact E| lia| exact HWA| exact HEAP'| exact WGT'| exact MI'| exact MU'| exact WM'].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_hm_cpop2 : forall (hA w : zarr) (zzA tmp1 n1 nH nN : Z) (me m : word -> option byte)
      (t1 t2 a6 a7 t3 t4 t5 t6 : word),
    (2 <= nH <= 258)%Z -> (0 <= nN <= 515)%Z -> (1 <= zzA <= nH - 1)%Z -> (0 <= tmp1 <= nN)%Z -> hw hA w (nH - 1) nN ->
    u32arr s0segs m (p + 4152) (ovw hA Jh 260) -> u32arr s0segs m (p + 2088) (ovw w Jw 516) -> mem_inv s0segs m ->
    munch [(p + 4152, p + 5192)]%Z me m -> wmono s0segs me m ->
    (forall hB zzB m' (t0 t1 a5 t3 t4 t5 t6 : word),
      let hp1 := zset hA zzA tmp1 in
      downheap_loop 20 (zset hp1 1 (zget hp1 (nH - 1))) w (nH - 2) 1 (zget hp1 (nH - 1)) = (hB, zzB) -> (1 <= zzB <= nH - 1)%Z ->
      hw hB w (nH - 2) nN ->
      u32arr s0segs m' (p + 4152) (ovw hB Jh 260) -> u32arr s0segs m' (p + 2088) (ovw w Jw 516) -> mem_inv s0segs m' ->
      munch [(p + 4152, p + 5192)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RR RA t0 t1 (Z_to_bv 64 zzB) (Z_to_bv 64 nH) (Z_to_bv 64 (nH - 1)) (Z_to_bv 64 n1) (Z_to_bv 64 nN)
                            (Z_to_bv 64 (p + 4152 + 4 * (nH - 1))) a5 (Z_to_bv 64 (zget hp1 1)) (Z_to_bv 64 (zget hp1 (nH - 1))) t3 t4 t5 t6)
                       F (Z_to_bv 64 0x23fc8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RR RA (Z_to_bv 64 zzA) t1 t2 (Z_to_bv 64 nH) (Z_to_bv 64 (nH - 1)) (Z_to_bv 64 n1) (Z_to_bv 64 nN) (Z_to_bv 64 tmp1) (Z_to_bv 64 nH) a6 a7 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x23ec8) fc None m (seg_rom s0segs)).
  Proof.
    intros hA w zzA tmp1 n1 nH nN me m t1 t2 a6 a7 t3 t4 t5 t6 HnH HnN HzzA Htmp HW HEAP WGT MI MU WM K.
    hmenv_open XOK.
    pose proof (ovw_length hA Jh 260 ltac:(lia)) as LH. pose proof (ovw_length w Jw 516 ltac:(lia)) as LW.
    (* [comment removed for export] *)
    wstep. wstep; notrap. wstep. wstep.
    pose proof (u32arr_store_ok s0segs m (p + 4152) _ zzA _ HEAP ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    wstep. store_addr (p + 4152 + 4 * zzA)%Z. ovw_store HEAP zzA tmp1 wval_lit.
    set (hp1 := zset hA zzA tmp1) in *.
    assert (HW1 : hw hp1 w (nH - 1) nN) by (subst hp1; apply hw_hset; [exact HW| lia| lia]).
    pose proof HW1 as HW0. cps_destruct HW0 as (S1 & S2 & HH & WW).
    pose proof (HH (nH - 1)%Z ltac:(lia)) as [Dn Rn]. pose proof (HH 1%Z ltac:(lia)) as [D1 R1].
    set (tmp2 := zget hp1 (nH - 1)) in *. set (n2 := zget hp1 1) in *.
    pose proof (WW tmp2 ltac:(lia)) as [Dwt Rwt].
    (* [comment removed for export] *)
    wstep; notrap. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (ovw_read s0segs mm (p + 4152) hp1 Jh 260 (nH - 1) _ HEAP ltac:(lia) Dn ltac:(unfold wa; f_equal; lia)) as RD end.
    wstep. clear RD. fold tmp2. try rewrite (sx32_of_Z tmp2) by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (ovw_read s0segs mm (p + 4152) hp1 Jh 260 1 _ HEAP ltac:(lia) D1 ltac:(unfold wa; f_equal; lia)) as RD end.
    wstep. clear RD. fold n2. try rewrite (sx32_of_Z n2) by lia.
    pose proof (u32arr_store_ok s0segs _ (p + 4152) _ 1 _ HEAP ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO2.
    wstep. store_addr (p + 4152 + 4 * 1)%Z. ovw_store HEAP 1%Z tmp2 wval_lit.
    assert (HW2 : hw (zset hp1 1 tmp2) w (nH - 1) nN) by (apply hw_hset; [exact HW1| lia| lia]).
    (* [comment removed for export] *)
    wstep. wstep; if_cases Ks; zify_cond_z Ks.
    - (* [comment removed for export] *)
      wstep. wstep. wstep. wstep. wstep.
      enter_with (S0_hm_down2 20%nat 1 (nH - 2) nN tmp2 (zset hp1 1 tmp2) w me); [st_eq| lia| lia| lia| cbn; lia| lia| lia| | exact HEAP| exact WGT| exact MI| exact MU| exact WM|].
      + apply (hw_nH_le _ _ (nH - 1)); [exact HW2| lia].
      + intros hB zzB m' x3 x4 x5 x6 E HzzB HWB HEAP' WGT' MI' MU' WM'.
        enter_with (K hB zzB m' _ _ _ _ _ _ _); [st_eq| exact E| lia| exact HWB| exact HEAP'| exact WGT'| exact MI'| exact MU'| exact WM'].
    - (* [comment removed for export] *)
      wstep. wstep.
      enter_with (K (zset hp1 1 tmp2) 1%Z _ _ _ _ _ _ _ _); [st_eq| | lia| apply (hw_nH_le _ _ (nH - 1)); [exact HW2| lia]| exact HEAP| exact WGT| exact MI| exact MU| exact WM].
      apply downheap_loop_stop1. apply Z.ltb_lt. rewrite shiftl1_mul2. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_hm_cnode : forall (hB w par : zarr) (zzB tmp2 n1 n2 nH nN : Z) (me m : word -> option byte)
      (t0 t1 a5 t3 t4 t5 t6 : word),
    (2 <= nH <= 258)%Z -> (0 <= nN)%Z -> (nN + 1 <= 515)%Z -> (1 <= zzB <= nH - 1)%Z -> (0 <= tmp2 <= nN)%Z -> (0 <= n1 <= nN)%Z -> (0 <= n2 <= nN)%Z ->
    hw hB w (nH - 2) nN -> hpar par nN -> (weightof (zget w n1) + weightof (zget w n2) <= 2147483136)%Z ->
    u32arr s0segs m (p + 4152) (ovw hB Jh 260) -> u32arr s0segs m (p + 2088) (ovw w Jw 516) -> u32arr s0segs m (p + 24) (ovw par Jp 516) ->
    mem_inv s0segs m -> munch [(p + 24, p + 5192)]%Z me m -> wmono s0segs me m ->
    (forall hC zzC m' (t0 t2 a2 a4 a6 a7 : word),
      let aw := addweights (zget w n1) (zget w n2) in
      let w' := zset w (nN + 1) aw in
      let par' := zset (zset (zset par n2 (nN + 1)) n1 (nN + 1)) (nN + 1) (-1) in
      let h3 := zset (zset hB zzB tmp2) (nH - 1) (nN + 1) in
      upheap_loop 20 h3 w' (nH - 1) (nN + 1) = (hC, zzC) ->
      hw (zset hC zzC (nN + 1)) w' (nH - 1) (nN + 1) -> hpar par' (nN + 1) ->
      u32arr s0segs m' (p + 4152) (ovw (zset hC zzC (nN + 1)) Jh 260) -> u32arr s0segs m' (p + 2088) (ovw w' Jw 516) -> u32arr s0segs m' (p + 24) (ovw par' Jp 516) ->
      mem_inv s0segs m' -> munch [(p + 24, p + 5192)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RR RA t0 t1 t2 (Z_to_bv 64 nH) (Z_to_bv 64 2) a2 (Z_to_bv 64 (nN + 1)) a4 (Z_to_bv 64 (nH - 1)) a6 a7 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x240ec) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RR RA t0 t1 (Z_to_bv 64 zzB) (Z_to_bv 64 nH) (Z_to_bv 64 (nH - 1)) (Z_to_bv 64 n1) (Z_to_bv 64 nN)
                          (Z_to_bv 64 (p + 4152 + 4 * (nH - 1))) a5 (Z_to_bv 64 n2) (Z_to_bv 64 tmp2) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x23fc8) fc None m (seg_rom s0segs)).
  Proof.
    intros hB w par zzB tmp2 n1 n2 nH nN me m t0 t1 a5 t3 t4 t5 t6 HnH HnN HnN' HzzB Htmp Hn1 Hn2 HW HP RF HEAP WGT PAR MI MU WM K.
    hmenv_open XOK. pose proof HW as HW0. cps_destruct HW0 as (S1 & S2 & HH & WW).
    pose proof (ovw_length hB Jh 260 ltac:(lia)) as LH. pose proof (ovw_length w Jw 516 ltac:(lia)) as LW. pose proof (ovw_length par Jp 516 ltac:(lia)) as LP.
    pose proof (WW n1 ltac:(lia)) as [Dw1 Rw1]. pose proof (WW n2 ltac:(lia)) as [Dw2 Rw2].
    (* [comment removed for export] *)
    wstep. wstep; notrap. wstep. wstep.
    (* [comment removed for export] *)
    pose proof (u32arr_store_ok s0segs m (p + 4152) _ zzB _ HEAP ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    wstep. store_addr (p + 4152 + 4 * zzB)%Z. ovw_store HEAP zzB tmp2 wval_lit.
    set (hp2 := zset hB zzB tmp2) in *.
    (* [comment removed for export] *)
    wstep; notrap. wstep; notrap. wstep. wstep; notrap. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm (p + 24) _ n2 _ PAR ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO2 end.
    wstep. store_addr (p + 24 + 4 * n2)%Z. ovw_store PAR n2 (nN + 1)%Z wval_lit.
    (* [comment removed for export] *)
    wstep; notrap. wstep. wstep; notrap. wstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm (p + 24) _ n1 _ PAR ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO3 end.
    wstep. store_addr (p + 24 + 4 * n1)%Z. ovw_store PAR n1 (nN + 1)%Z wval_lit.
    (* [comment removed for export] *)
    wstep; notrap. wstep; notrap. wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (ovw_read s0segs mm (p + 2088) w Jw 516 n1 _ WGT ltac:(lia) Dw1 ltac:(unfold wa; f_equal; lia)) as RD end.
    wstep. clear RD. try rewrite (sx32_of_Z (zget w n1)) by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (ovw_read s0segs mm (p + 2088) w Jw 516 n2 _ WGT ltac:(lia) Dw2 ltac:(unfold wa; f_equal; lia)) as RD end.
    wstep. clear RD. try rewrite (sx32_of_Z (zget w n2)) by lia.
    (* [comment removed for export] *)
    wstep. wstep.
    pose proof (depthof_range (zget w n1)) as Dr1. pose proof (depthof_range (zget w n2)) as Dr2.
    change (Z.land (zget w n1) 255) with (depthof (zget w n1)). change (Z.land (zget w n2) 255) with (depthof (zget w n2)).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mq end.
    (* [comment removed for export] *)
    assert (TAIL : forall dm (x2 : word), dm = Z.max (depthof (zget w n1)) (depthof (zget w n2)) ->
      evt s0segs Q (MS (RR RA t0 t1 x2 (Z_to_bv 64 nH) (Z_to_bv 64 (nH - 1)) (Z_to_bv 64 (zget w n1)) (Z_to_bv 64 (zget w n2))
                            (Z_to_bv 64 (p + 4152 + 4 * (nH - 1))) (Z_to_bv 64 (nN + 1)) (Z_to_bv 64 dm) (Z_to_bv 64 (depthof (zget w n2))) t3 t4 t5 t6)
                       F (Z_to_bv 64 0x24030) fc None mq (seg_rom s0segs))).
    { intros dm x2 Edm.
      (* [comment removed for export] *)
      wstep; notrap. wstep. wstep; notrap. wstep. wstep. wstep. wstep. wstep. wstep.
      rewrite (addweights_compiled (zget w n1) (zget w n2) dm) by lia.
      set (aw := addweights (zget w n1) (zget w n2)) in *.
      assert (AWR : (0 <= aw < 2147483648)%Z) by (subst aw; apply addweights_range; lia).
      (* [comment removed for export] *)
      pose proof (u32arr_store_ok s0segs mq (p + 2088) _ (nN + 1) _ WGT ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO5.
      wstep. store_addr (p + 2088 + 4 * (nN + 1))%Z. ovw_store WGT (nN + 1)%Z aw wval_lit.
      set (w' := zset w (nN + 1) aw) in *.
      (* [comment removed for export] *)
      wstep; notrap. wstep. wstep. wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u32arr_store_ok s0segs mm (p + 24) _ (nN + 1) _ PAR ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO6 end.
      wstep. store_addr (p + 24 + 4 * (nN + 1))%Z. ovw_store PAR (nN + 1)%Z (-1)%Z (rewrite unsigned_lit_mod32; reflexivity).
      assert (HP' : hpar (zset (zset (zset par n2 (nN + 1)) n1 (nN + 1)) (nN + 1) (-1)) (nN + 1)).
      { apply hpar_node; [exact HP| lia| lia]. }
      (* [comment removed for export] *)
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u32arr_store_ok s0segs mm (p + 4152) _ (nH - 1) _ HEAP ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO4 end.
      wstep. store_addr (p + 4152 + 4 * (nH - 1))%Z. ovw_store HEAP (nH - 1)%Z (nN + 1)%Z wval_lit.
      set (h3 := zset hp2 (nH - 1) (nN + 1)) in *.
      assert (HW3 : hw h3 w' (nH - 1) (nN + 1)).
      { subst h3 w'. replace (nH - 1)%Z with (nH - 2 + 1)%Z by lia. apply hw_push; [|lia| lia]. apply hw_node; [|lia| exact AWR].
        subst hp2. apply hw_hset; [|lia| lia]. cps_destruct HW as (T1 & T2 & HHB & WWB). split; [exact T1|]. split; [exact T2|]. split; [exact HHB|].
        intros x Hx. destruct (WWB x ltac:(lia)). split; [assumption| lia]. }
      assert (Hq : (0 <= (nH - 1) / 2 < nH - 1)%Z) by (Z.div_mod_to_equations; lia).
      (* [comment removed for export] *)
      wstep; notrap. wstep.
      try rewrite !shiftr1_div2.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mr end.
      enter_with (S0_hm_up2 20%nat (nH - 1) (nH - 1) (nN + 1) h3 w' mr mr);
        [st_eq| lia| lia| cbn; lia| lia| exact HW3| exact HEAP| exact WGT| exact MI| apply munch_refl| apply wmono_refl|].
      { subst w'. cbv delta [mkR]. rewrite zget_zset_same. st_eq. }
      intros hC zzC m' y0 y4 y6 y7 E HzzC HWC HEAP' WGT' MI' MU' WM'.
      clear HEAP WGT MI. transport_after_call s0segs mr m' MU' WM'.
      pose proof (ovw_length hC Jh 260 ltac:(lia)) as LHC.
      (* [comment removed for export] *)
      wstep; notrap. wstep. wstep; notrap. wstep.
      pose proof (u32arr_store_ok s0segs m' (p + 4152) _ zzC _ HEAP' ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO8.
      wstep. store_addr (p + 4152 + 4 * zzC)%Z. ovw_store HEAP' zzC (nN + 1)%Z wval_lit.
      (* [comment removed for export] *)
      wstep. wstep. wstep.
      enter_with (K hC zzC _ _ _ _ _ _ _); [st_eq| exact E| apply hw_hset; [exact HWC| lia| lia]| exact HP'| exact HEAP'| exact WGT'| exact PAR| assumption| exact MU| exact WM]. }
    (* [comment removed for export] *)
    wstep; if_cases Kd; zify_cond_z Kd.
    - (* [comment removed for export] *)
      enter_with (TAIL (depthof (zget w n1)) _); [st_eq| symmetry; apply Z.max_l; lia].
    - (* [comment removed for export] *)
      wstep. enter_with (TAIL (depthof (zget w n2)) _); [st_eq| symmetry; apply Z.max_r; lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_hm_combine : forall (n : nat) (h w par : zarr) (nH nN : Z) (me m : word -> option byte)
      (t0 t1 t2 a0 a1 a2 a4 a6 a7 t3 t4 t5 t6 : word),
    let s := HMS h w par nH nN in
    (nH = Z.of_nat n + 1)%Z -> (1 <= n)%nat -> (nH <= A)%Z -> (A <= nN)%Z -> (nN + Z.of_nat n <= 515)%Z ->
    hw h w nH nN -> hpar par nN ->
    (forall j, (j < n)%nat -> rf_cb (Nat.iter j hm_combine_iter s)) ->
    u32arr s0segs m (p + 4152) (ovw h Jh 260) -> u32arr s0segs m (p + 2088) (ovw w Jw 516) -> u32arr s0segs m (p + 24) (ovw par Jp 516) ->
    mem_inv s0segs m -> munch [(p + 24, p + 5192)]%Z me m -> wmono s0segs me m ->
    (forall h' w' par' nN' m' (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      Nat.iter n hm_combine_iter s = HMS h' w' par' 1 nN' -> (nN' = nN + Z.of_nat n)%Z ->
      hw h' w' 1 nN' -> hpar par' nN' ->
      u32arr s0segs m' (p + 4152) (ovw h' Jh 260) -> u32arr s0segs m' (p + 2088) (ovw w' Jw 516) -> u32arr s0segs m' (p + 24) (ovw par' Jp 516) ->
      mem_inv s0segs m' -> munch [(p + 24, p + 5192)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RR RA t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0x240f0) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RR RA t0 t1 t2 a0 a1 a2 (Z_to_bv 64 nN) a4 (Z_to_bv 64 nH) a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0x23de4) fc None m (seg_rom s0segs)).
  Proof using XOK.
    induction n as [|n IH]. { intros; lia. }
    intros h w par nH nN me m t0 t1 t2 a0 a1 a2 a4 a6 a7 t3 t4 t5 t6 s HnH Hn HA HAN HN HW HP FACTS HEAP WGT PAR MI MU WM K. subst s.
    hmenv_open XOK.
    pose proof HW as HW0. cps_destruct HW0 as (S1 & S2 & HH & WW).
    pose proof (HH nH ltac:(lia)) as [_ Rt1]. pose proof (HH 1%Z ltac:(lia)) as [_ Rn1].
    eapply (S0_hm_cpop1 h w nH nN m m); [lia| lia| exact HW| exact HEAP| exact WGT| exact MI| apply munch_refl| apply wmono_refl|].
    intros hA zzA m1 x1 x2 x6 x7 x3 x4 E1 HzzA HWA HEAP1 WGT1 MI1 MU1 WM1.
    clear HEAP WGT MI. transport_after_call s0segs m m1 MU1 WM1.
    pose proof HWA as HW0. cps_destruct HW0 as (_ & _ & HHA & _).
    eapply (S0_hm_cpop2 hA w zzA (zget h nH) (zget h 1) nH nN m1 m1); [lia| lia| lia| lia| exact HWA| exact HEAP1| exact WGT1| exact MI1| apply munch_refl| apply wmono_refl|].
    intros hB zzB m2 y0 y1 y15 y28 y29 y30 y31. cbv zeta. intros E2 HzzB HWB HEAP2 WGT2 MI2 MU2 WM2.
    clear HEAP1 WGT1 MI1 MU1 WM1. transport_after_call s0segs m1 m2 MU2 WM2.
    set (hp1 := zset hA zzA (zget h nH)) in *.
    assert (HW1 : hw hp1 w (nH - 1) nN) by (subst hp1; apply hw_hset; [exact HWA| lia| lia]).
    cps_destruct HW1 as (_ & _ & HH1 & _). pose proof (HH1 (nH - 1)%Z ltac:(lia)) as [_ Rt2]. pose proof (HH1 1%Z ltac:(lia)) as [_ Rn2].
    cps_destruct (combine_iter_link1 h w par nH nN hA zzA E1) as (_ & N1 & N2 & EW & EP). cbv zeta in N1, N2, EW, EP. fold hp1 in N2, EW, EP.
    pose proof (FACTS 0%nat ltac:(lia)) as RF0. cbn [Nat.iter nat_rect] in RF0. unfold rf_cb in RF0. rewrite N1, N2 in RF0. cbn [hm_weight] in RF0.
    eapply (S0_hm_cnode hB w par zzB (zget hp1 (nH - 1)) (zget h 1) (zget hp1 1) nH nN me m2);
      [lia| lia| lia| lia| lia| lia| lia| exact HWB| exact HP| exact RF0| exact HEAP2| exact WGT2| exact PAR| exact MI2| exact MU| exact WM|].
    intros hC zzC m3 z0 z2 z10 z12 z14 z15. cbv zeta. intros E3 HWC HPC HEAP3 WGT3 PAR3 MI3 MU3 WM3.
    clear HEAP2 WGT2 PAR MI2 MU2 WM2 MU WM.
    pose proof (combine_iter_link h w par nH nN hA zzA hB zzB hC zzC E1 E2 E3) as IT. cbv zeta in IT.
    rewrite <- EW in HWC, WGT3. rewrite <- EP in HPC, PAR3.
    (* [comment removed for export] *)
    wstep; if_cases Kl; zify_cond_z Kl.
    - enter_with (IH (zset hC zzC (nN + 1)) (cb_w' (HMS h w par nH nN)) (cb_p' (HMS h w par nH nN)) (nH - 1)%Z (nN + 1)%Z me m3);
        [st_eq| lia| lia| lia| lia| lia| exact HWC| exact HPC| | exact HEAP3| exact WGT3| exact PAR3| exact MI3| exact MU3| exact WM3|].
      + intros j Hj. rewrite <- IT, <- iter_S_r. apply FACTS. lia.
      + intros h' w' par' nN' m' q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 ITn HnN' HW' HP' HE' WG' PA' MI' MU' WM'.
        apply (K h' w' par' nN' m' q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31); [rewrite iter_S_r, IT; exact ITn| lia| exact HW'| exact HP'| exact HE'| exact WG'| exact PA'| exact MI'| exact MU'| exact WM'].
    - assert (n = 0)%nat by lia. subst n.
      enter_with (K (zset hC zzC (nN + 1)) (cb_w' (HMS h w par nH nN)) (cb_p' (HMS h w par nH nN)) (nN + 1)%Z m3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
        [st_eq| | lia| exact (eq_rect _ (fun k => hw (zset hC zzC (nN + 1)) (cb_w' (HMS h w par nH nN)) k (nN + 1)) HWC 1%Z ltac:(lia))| exact HPC| exact HEAP3| exact WGT3| exact PAR3| exact MI3| exact MU3| exact WM3].
      cbn [Nat.iter nat_rect]. rewrite IT. f_equal. lia.
  Qed.
End S0HM.

End ACeilS1.
