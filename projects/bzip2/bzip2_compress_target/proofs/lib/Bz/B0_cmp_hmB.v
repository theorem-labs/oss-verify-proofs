(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzTac BzTac2 BzArr BzCMem BzCHuff BzArrD CmpMem CmpCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF1.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFsKit0 CmpHmKit.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.BzCFactsHm OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpFsKit0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanCut AsanCutB0 AsanKitB0 B0_cmp_hmV.
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
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section B0HM.
  Variable X : hmenv. Variable Y : ahenv. Variable Q : machine_state -> Prop.
  Variables Jh Jw Jp : list byte.
  Hypothesis XOK : hmenv_ok X. Hypothesis YOK : ahenv_ok X Y. Hypothesis YSX : ahenv_sepx X Y.
  Notation usp := (bv_unsigned (he_sp X)). Notation P := (ah_P Y).
  Notation HP := (ah_HP Y). Notation WT := (ah_WT Y). Notation PR := (ah_PR Y).
  Notation A := (he_A X). Notation El := (he_El X). Notation Ef := (he_Ef X). Notation lb := (he_lb X). Notation fb := (he_fb X).
  Notation gp := (he_gp X). Notation tp := (he_tp X). Notation F := (he_F X). Notation fc := (he_fc X).
  Notation Jf := (he_Jf X). Notation freq := (he_freq X). Notation NF := (he_NF X).
  Notation Jl := (he_Jl X). Notation NL := (he_NL X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).
  (* [comment removed for export] *)
  Notation RB ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (he_sp X) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 PR) (Z_to_bv 64 516) (Z_to_bv 64 515) (NOT PR) (Z_to_bv 64 259) (NOT WT) (Z_to_bv 64 WT) (NOT HP) (Z_to_bv 64 HP) cSB t3 t4 t5 t6).
  Notation Wh := [(HP, HP + 1040)]%Z.
  (* [comment removed for export] *)

  Lemma lor_even1b : forall z, (0 <= z)%Z -> Z.lor (z * 2) 1 = (z * 2 + 1)%Z.
  Proof.
    intros z Hz. pose proof (Z.add_lor_land (z * 2) 1) as E.
    assert (L : Z.land (z * 2) 1 = 0%Z); [|lia].
    rewrite land1_mod2. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_hm_down1 : forall (f : nat) (zz nHq nN tmp : Z) (h w : zarr) (me m : word -> option byte)
      (ra t2 a1 a2 a6 t5 t6 : word),
    (1 <= zz)%Z -> (zz * 2 <= nHq)%Z -> (nHq <= 258)%Z -> (nHq < zz * 2 ^ Z.of_nat f)%Z -> (0 <= nN <= 515)%Z ->
    (0 <= tmp <= nN)%Z -> hw h w nHq nN ->
    u32arr b0segs m HP (ovw h Jh 260) -> u32arr b0segs m WT (ovw w Jw 516) -> mem_inv b0segs m ->
    munch Wh me m -> wmono b0segs me m ->
    shzW b0segs Wh me HP (HP + 1040) -> shzW b0segs Wh me WT (WT + 2064) ->
    (forall h' zz' m' (a1 a2 a6 t3 t4 t5 : word),
      downheap_loop f h w nHq zz tmp = (h', zz') -> (1 <= zz' <= nHq)%Z -> hw h' w nHq nN ->
      u32arr b0segs m' HP (ovw h' Jh 260) -> u32arr b0segs m' WT (ovw w Jw 516) -> mem_inv b0segs m' ->
      munch Wh me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (RB ra (Z_to_bv 64 tmp) (Z_to_bv 64 (tmp * 4)) (Z_to_bv 64 zz') (Z_to_bv 64 (WT + tmp * 4)) a1 a2 (Z_to_bv 64 (nHq + 1)) (Z_to_bv 64 (nHq + 1)) (Z_to_bv 64 nHq)
                           a6 (Z_to_bv 64 nN) t3 t4 t5 t6)
                       F (Z_to_bv 64 0xa86d0) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RB ra (Z_to_bv 64 tmp) (Z_to_bv 64 (tmp * 4)) t2 (Z_to_bv 64 (WT + tmp * 4)) a1 a2 (Z_to_bv 64 (nHq + 1)) (Z_to_bv 64 (nHq + 1)) (Z_to_bv 64 nHq)
                         a6 (Z_to_bv 64 nN) (Z_to_bv 64 zz) (Z_to_bv 64 (zz * 2)) t5 t6)
                     F (Z_to_bv 64 0xa8520) fc None m (seg_rom b0segs)).
  Proof.
    induction f as [|f IH]. { intros. cbn in H2. lia. }
    intros zz nHq nN tmp h w me m ra t2 a1 a2 a6 t5 t6 Hzz Hyy HnH Hf HnN Htmp HW HEAP WGT MI MU WM SHh SHw K.
    hmenv_open XOK. ahenv_open YOK. ahenv_sepx_open YSX. cps_destruct HW as (S1 & S2 & HH & WW).
    pose proof (ovw_length h Jh 260 ltac:(lia)) as LH. pose proof (ovw_length w Jw 516 ltac:(lia)) as LW.
    pose proof (WW tmp ltac:(lia)) as [Dwt Rwt].
    (* [comment removed for export] *)
    assert (TAIL : forall yy' (x11 x12 x16 x30 : word), yy' = dh_child h w nHq (zz * 2) -> (zz * 2 <= yy' <= nHq)%Z -> (yy' <= zz * 2 + 1)%Z ->
      evt b0segs Q (MS (RB ra (Z_to_bv 64 tmp) (Z_to_bv 64 (tmp * 4)) (Z_to_bv 64 yy') (Z_to_bv 64 (WT + tmp * 4)) x11 x12 (Z_to_bv 64 (nHq + 1)) (Z_to_bv 64 (nHq + 1)) (Z_to_bv 64 nHq)
                           x16 (Z_to_bv 64 nN) (Z_to_bv 64 zz) (Z_to_bv 64 (zz * 2)) x30 t6)
                       F (Z_to_bv 64 0xa85b0) fc None m (seg_rom b0segs))).
    { intros yy' x11 x12 x16 x30 Eyy Hyy' Hyy2.
      pose proof (HH yy' ltac:(lia)) as [Dy Ry]. pose proof (WW (zget h yy') ltac:(lia)) as [Dwy Rwy].
      (* [comment removed for export] *)
      brun.
      pose proof (ovw_read b0segs _ WT w Jw 516 tmp _ WGT ltac:(lia) Dwt ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget w tmp)) by lia.
      (* [comment removed for export] *)
      brun.
      pose proof (ovw_read b0segs _ HP h Jh 260 yy' _ HEAP ltac:(lia) Dy ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget h yy')) by lia.
      (* [comment removed for export] *)
      brun.
      pose proof (ovw_read b0segs _ WT w Jw 516 (zget h yy') _ WGT ltac:(lia) Dwy ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget w (zget h yy'))) by lia.
      (* [comment removed for export] *)
      wstep; if_cases Kb; zify_cond_z Kb.
      - (* [comment removed for export] *)
        wstep.
        enter_with (K h zz m _ _ _ _ _ _); [st_eq| | lia| exact (conj S1 (conj S2 (conj HH WW)))| exact HEAP| exact WGT| exact MI| exact MU| exact WM].
        apply downheap_loop_stop2; [apply Z.ltb_ge; rewrite shiftl1_mul2; lia|]. rewrite shiftl1_mul2, <- Eyy. apply Z.ltb_lt. exact Kb.
      - (* [comment removed for export] *)
        brun.
        pose proof (u32arr_store_ok b0segs m HP _ zz _ HEAP ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
        wstep. store_addr (HP + 4 * zz)%Z. ovw_store HEAP zz (zget h yy') wval_lit.
        (* [comment removed for export] *)
        wstep.
        assert (HW1 : hw (zset h zz (zget h yy')) w nHq nN) by (apply hw_hset; [exact (conj S1 (conj S2 (conj HH WW)))| lia| lia]).
        (* [comment removed for export] *)
        wstep; if_cases Kl; zify_cond_z Kl.
        + enter_with (IH yy' nHq nN tmp (zset h zz (zget h yy')) w me); [st_eq| lia| lia| lia| | lia| lia| exact HW1| exact HEAP| exact WGT| exact MI| exact MU| exact WM| exact SHh| exact SHw|].
          * rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hf by lia.
            eapply Z.lt_le_trans; [exact Hf|]. rewrite Z.mul_assoc.
            apply Z.mul_le_mono_nonneg_r; [apply Z.pow_nonneg; discriminate | exact (proj1 Hyy')].
          * intros h' zz' m' y11 y12 y16 y28 y29 y30 E Hzz' HW'. eapply K; [| lia| exact HW'].
            rewrite downheap_loop_S. replace (nHq <? Z.shiftl zz 1)%Z with false by (symmetry; apply Z.ltb_ge; rewrite shiftl1_mul2; lia).
            cbn zeta. rewrite shiftl1_mul2, <- Eyy. replace (zget w tmp <? zget w (zget h yy'))%Z with false by (symmetry; apply Z.ltb_ge; lia). exact E.
        + (* [comment removed for export] *)
          wstep.
          enter_with (K (zset h zz (zget h yy')) yy' _ _ _ _ _ _ _); [st_eq| | lia| exact HW1| exact HEAP| exact WGT| exact MI| exact MU| exact WM].
          rewrite downheap_loop_S. replace (nHq <? Z.shiftl zz 1)%Z with false by (symmetry; apply Z.ltb_ge; rewrite shiftl1_mul2; lia).
          cbn zeta. rewrite shiftl1_mul2, <- Eyy. replace (zget w tmp <? zget w (zget h yy'))%Z with false by (symmetry; apply Z.ltb_ge; lia).
          apply downheap_loop_stop1. apply Z.ltb_lt. rewrite shiftl1_mul2. lia. }
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      wstep. enter_with (TAIL (zz * 2)%Z _ _ _ _); [st_eq| | lia| lia].
      unfold dh_child. replace (zz * 2 <? nHq)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
    - (* [comment removed for export] *)
      pose proof (HH (zz * 2)%Z ltac:(lia)) as [D0 R0]. pose proof (HH (zz * 2 + 1)%Z ltac:(lia)) as [D1 R1].
      pose proof (WW (zget h (zz * 2)) ltac:(lia)) as [Dw0 Rw0]. pose proof (WW (zget h (zz * 2 + 1)) ltac:(lia)) as [Dw1 Rw1].
      (* [comment removed for export] *)
      wstep. rewrite lor_even1b by lia. brun.
      pose proof (ovw_read b0segs _ HP h Jh 260 (zz * 2 + 1) _ HEAP ltac:(lia) D1 ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget h (zz * 2 + 1))) by lia.
      (* [comment removed for export] *)
      brun.
      pose proof (ovw_read b0segs _ WT w Jw 516 (zget h (zz * 2 + 1)) _ WGT ltac:(lia) Dw1 ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget w (zget h (zz * 2 + 1)))) by lia.
      (* [comment removed for export] *)
      brun.
      pose proof (ovw_read b0segs _ HP h Jh 260 (zz * 2) _ HEAP ltac:(lia) D0 ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget h (zz * 2))) by lia.
      (* [comment removed for export] *)
      brun.
      pose proof (ovw_read b0segs _ WT w Jw 516 (zget h (zz * 2)) _ WGT ltac:(lia) Dw0 ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget w (zget h (zz * 2)))) by lia.
      (* [comment removed for export] *)
      wstep; if_cases Kw; zify_cond_z Kw.
      + enter_with (TAIL (zz * 2 + 1)%Z _ _ _ _); [st_eq| | lia| lia].
        unfold dh_child. replace (zz * 2 <? nHq)%Z with true by (symmetry; apply Z.ltb_lt; lia).
        replace (zget w (zget h (zz * 2 + 1)) <? zget w (zget h (zz * 2)))%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
      + (* [comment removed for export] *)
        wstep. enter_with (TAIL (zz * 2)%Z _ _ _ _); [st_eq| | lia| lia].
        unfold dh_child. replace (zz * 2 <? nHq)%Z with true by (symmetry; apply Z.ltb_lt; lia).
        replace (zget w (zget h (zz * 2 + 1)) <? zget w (zget h (zz * 2)))%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_hm_down2 : forall (f : nat) (zz nHq nN tmp : Z) (h w : zarr) (me m : word -> option byte)
      (t0 t1 a0 a2 a3 a4 a5 a6 a7 t5 : word),
    (1 <= zz)%Z -> (zz * 2 <= nHq)%Z -> (nHq <= 258)%Z -> (nHq < zz * 2 ^ Z.of_nat f)%Z -> (0 <= nN <= 515)%Z ->
    (0 <= tmp <= nN)%Z -> hw h w nHq nN ->
    u32arr b0segs m HP (ovw h Jh 260) -> u32arr b0segs m WT (ovw w Jw 516) -> mem_inv b0segs m ->
    munch Wh me m -> wmono b0segs me m ->
    shzW b0segs Wh me HP (HP + 1040) -> shzW b0segs Wh me WT (WT + 2064) ->
    (forall h' zz' m' (ra t0 a2 a3 a6 t6 : word),
      downheap_loop f h w nHq zz tmp = (h', zz') -> (1 <= zz' <= nHq)%Z -> hw h' w nHq nN ->
      u32arr b0segs m' HP (ovw h' Jh 260) -> u32arr b0segs m' WT (ovw w Jw 516) -> mem_inv b0segs m' ->
      munch Wh me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (RB ra t0 t1 (Z_to_bv 64 tmp) a0 (Z_to_bv 64 (WT + tmp * 4)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 nHq) (Z_to_bv 64 (tmp * 4)) (Z_to_bv 64 zz') t6)
                       F (Z_to_bv 64 0xa88f8) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RB (Z_to_bv 64 (zz * 2)) t0 t1 (Z_to_bv 64 tmp) a0 (Z_to_bv 64 (WT + tmp * 4)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 nHq) (Z_to_bv 64 (tmp * 4)) t5 (Z_to_bv 64 zz))
                     F (Z_to_bv 64 0xa8740) fc None m (seg_rom b0segs)).
  Proof.
    induction f as [|f IH]. { intros. cbn in H2. lia. }
    intros zz nHq nN tmp h w me m t0 t1 a0 a2 a3 a4 a5 a6 a7 t5 Hzz Hyy HnH Hf HnN Htmp HW HEAP WGT MI MU WM SHh SHw K.
    hmenv_open XOK. ahenv_open YOK. ahenv_sepx_open YSX. cps_destruct HW as (S1 & S2 & HH & WW).
    pose proof (ovw_length h Jh 260 ltac:(lia)) as LH. pose proof (ovw_length w Jw 516 ltac:(lia)) as LW.
    pose proof (WW tmp ltac:(lia)) as [Dwt Rwt].
    (* [comment removed for export] *)
    assert (TAIL : forall yy' (x5 x12 x13 x16 : word), yy' = dh_child h w nHq (zz * 2) -> (zz * 2 <= yy' <= nHq)%Z -> (yy' <= zz * 2 + 1)%Z ->
      evt b0segs Q (MS (RB (Z_to_bv 64 (zz * 2)) x5 t1 (Z_to_bv 64 tmp) a0 (Z_to_bv 64 (WT + tmp * 4)) x12 x13 a4 a5 x16 a7 (Z_to_bv 64 nHq) (Z_to_bv 64 (tmp * 4)) (Z_to_bv 64 yy') (Z_to_bv 64 zz))
                       F (Z_to_bv 64 0xa87dc) fc None m (seg_rom b0segs))).
    { intros yy' x5 x12 x13 x16 Eyy Hyy' Hyy2.
      pose proof (HH yy' ltac:(lia)) as [Dy Ry]. pose proof (WW (zget h yy') ltac:(lia)) as [Dwy Rwy].
      (* [comment removed for export] *)
      brun.
      pose proof (ovw_read b0segs _ WT w Jw 516 tmp _ WGT ltac:(lia) Dwt ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget w tmp)) by lia.
      (* [comment removed for export] *)
      brun.
      pose proof (ovw_read b0segs _ HP h Jh 260 yy' _ HEAP ltac:(lia) Dy ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget h yy')) by lia.
      (* [comment removed for export] *)
      brun.
      pose proof (ovw_read b0segs _ WT w Jw 516 (zget h yy') _ WGT ltac:(lia) Dwy ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget w (zget h yy'))) by lia.
      (* [comment removed for export] *)
      wstep; if_cases Kb; zify_cond_z Kb.
      - (* [comment removed for export] *)
        wstep.
        enter_with (K h zz m _ _ _ _ _ _); [st_eq| | lia| exact (conj S1 (conj S2 (conj HH WW)))| exact HEAP| exact WGT| exact MI| exact MU| exact WM].
        apply downheap_loop_stop2; [apply Z.ltb_ge; rewrite shiftl1_mul2; lia|]. rewrite shiftl1_mul2, <- Eyy. apply Z.ltb_lt. exact Kb.
      - (* [comment removed for export] *)
        brun.
        pose proof (u32arr_store_ok b0segs m HP _ zz _ HEAP ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
        wstep. store_addr (HP + 4 * zz)%Z. ovw_store HEAP zz (zget h yy') wval_lit.
        (* [comment removed for export] *)
        wstep.
        assert (HW1 : hw (zset h zz (zget h yy')) w nHq nN) by (apply hw_hset; [exact (conj S1 (conj S2 (conj HH WW)))| lia| lia]).
        (* [comment removed for export] *)
        wstep; if_cases Kl; zify_cond_z Kl.
        + enter_with (IH yy' nHq nN tmp (zset h zz (zget h yy')) w me); [st_eq| lia| lia| lia| | lia| lia| exact HW1| exact HEAP| exact WGT| exact MI| exact MU| exact WM| exact SHh| exact SHw|].
          * rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hf by lia.
            eapply Z.lt_le_trans; [exact Hf|]. rewrite Z.mul_assoc.
            apply Z.mul_le_mono_nonneg_r; [apply Z.pow_nonneg; discriminate | exact (proj1 Hyy')].
          * intros h' zz' m' y1 y5 y12 y13 y16 y31 E Hzz' HW'. eapply K; [| lia| exact HW'].
            rewrite downheap_loop_S. replace (nHq <? Z.shiftl zz 1)%Z with false by (symmetry; apply Z.ltb_ge; rewrite shiftl1_mul2; lia).
            cbn zeta. rewrite shiftl1_mul2, <- Eyy. replace (zget w tmp <? zget w (zget h yy'))%Z with false by (symmetry; apply Z.ltb_ge; lia). exact E.
        + (* [comment removed for export] *)
          wstep.
          enter_with (K (zset h zz (zget h yy')) yy' _ _ _ _ _ _ _); [st_eq| | lia| exact HW1| exact HEAP| exact WGT| exact MI| exact MU| exact WM].
          rewrite downheap_loop_S. replace (nHq <? Z.shiftl zz 1)%Z with false by (symmetry; apply Z.ltb_ge; rewrite shiftl1_mul2; lia).
          cbn zeta. rewrite shiftl1_mul2, <- Eyy. replace (zget w tmp <? zget w (zget h yy'))%Z with false by (symmetry; apply Z.ltb_ge; lia).
          apply downheap_loop_stop1. apply Z.ltb_lt. rewrite shiftl1_mul2. lia. }
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      wstep. enter_with (TAIL (zz * 2)%Z _ _ _ _); [st_eq| | lia| lia].
      unfold dh_child. replace (zz * 2 <? nHq)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
    - pose proof (HH (zz * 2)%Z ltac:(lia)) as [D0 R0]. pose proof (HH (zz * 2 + 1)%Z ltac:(lia)) as [D1 R1].
      pose proof (WW (zget h (zz * 2)) ltac:(lia)) as [Dw0 Rw0]. pose proof (WW (zget h (zz * 2 + 1)) ltac:(lia)) as [Dw1 Rw1].
      (* [comment removed for export] *)
      brun_to 0xa8750%Z. rewrite lor_even1b by lia.
      (* [comment removed for export] *)
      brun.
      pose proof (ovw_read b0segs _ HP h Jh 260 (zz * 2 + 1) _ HEAP ltac:(lia) D1 ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget h (zz * 2 + 1))) by lia.
      (* [comment removed for export] *)
      brun.
      pose proof (ovw_read b0segs _ WT w Jw 516 (zget h (zz * 2 + 1)) _ WGT ltac:(lia) Dw1 ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget w (zget h (zz * 2 + 1)))) by lia.
      (* [comment removed for export] *)
      brun.
      pose proof (ovw_read b0segs _ HP h Jh 260 (zz * 2) _ HEAP ltac:(lia) D0 ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget h (zz * 2))) by lia.
      (* [comment removed for export] *)
      brun.
      pose proof (ovw_read b0segs _ WT w Jw 516 (zget h (zz * 2)) _ WGT ltac:(lia) Dw0 ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget w (zget h (zz * 2)))) by lia.
      (* [comment removed for export] *)
      wstep; if_cases Kw; zify_cond_z Kw.
      + enter_with (TAIL (zz * 2 + 1)%Z _ _ _ _); [st_eq| | lia| lia].
        unfold dh_child. replace (zz * 2 <? nHq)%Z with true by (symmetry; apply Z.ltb_lt; lia).
        replace (zget w (zget h (zz * 2 + 1)) <? zget w (zget h (zz * 2)))%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
      + (* [comment removed for export] *)
        wstep. enter_with (TAIL (zz * 2)%Z _ _ _ _); [st_eq| | lia| lia].
        unfold dh_child. replace (zz * 2 <? nHq)%Z with true by (symmetry; apply Z.ltb_lt; lia).
        replace (zget w (zget h (zz * 2 + 1)) <? zget w (zget h (zz * 2)))%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_hm_up2 : forall (f : nat) (zz nHm nNq : Z) (h w : zarr) (me m : word -> option byte)
      (ra t1 t2 a0 a1 a4 a5 a7 t3 t4 t5 t6 : word),
    (1 <= zz <= nHm)%Z -> (nHm <= 258)%Z -> (zz < 2 ^ Z.of_nat f)%Z -> (1 <= nNq <= 515)%Z ->
    hw h w nHm nNq ->
    u32arr b0segs m HP (ovw h Jh 260) -> u32arr b0segs m WT (ovw w Jw 516) -> mem_inv b0segs m ->
    munch Wh me m -> wmono b0segs me m ->
    shzW b0segs Wh me HP (HP + 1040) -> shzW b0segs Wh me WT (WT + 2064) ->
    (forall h' zz' m' (t0 t1 a0 a1 a7 : word),
      upheap_loop f h w zz nNq = (h', zz') -> (1 <= zz' <= zz)%Z -> hw h' w nHm nNq ->
      u32arr b0segs m' HP (ovw h' Jh 260) -> u32arr b0segs m' WT (ovw w Jw 516) -> mem_inv b0segs m' ->
      munch Wh me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (RB ra t0 t1 t2 a0 a1 (Z_to_bv 64 (zget w nNq)) (Z_to_bv 64 nNq) a4 a5 (Z_to_bv 64 zz') a7 t3 t4 t5 t6)
                       F (Z_to_bv 64 0xa8ae0) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RB ra (Z_to_bv 64 (zz / 2)) t1 t2 a0 a1 (Z_to_bv 64 (zget w nNq)) (Z_to_bv 64 nNq) a4 a5 (Z_to_bv 64 zz) a7 t3 t4 t5 t6)
                     F (Z_to_bv 64 0xa8a30) fc None m (seg_rom b0segs)).
  Proof.
    induction f as [|f IH].
    { intros. cbn in H1. lia. }
    intros zz nHm nNq h w me m ra t1 t2 a0 a1 a4 a5 a7 t3 t4 t5 t6 Hzz HnH Hf HnN HW HEAP WGT MI MU WM SHh SHw K.
    hmenv_open XOK. ahenv_open YOK. ahenv_sepx_open YSX. pose proof HW as HW0. cps_destruct HW0 as (S1 & S2 & HH & WW).
    assert (Hz2 : (0 <= zz / 2 < zz)%Z) by (Z.div_mod_to_equations; lia).
    pose proof (HH (zz / 2)%Z ltac:(lia)) as [Dp Rp]. pose proof (WW nNq ltac:(lia)) as [Dwi Rwi]. pose proof (WW (zget h (zz / 2)) ltac:(lia)) as [Dwp Rwp].
    pose proof (ovw_length h Jh 260 ltac:(lia)) as LH. pose proof (ovw_length w Jw 516 ltac:(lia)) as LW.
    (* [comment removed for export] *)
    brun.
    pose proof (ovw_read b0segs _ HP h Jh 260 (zz / 2) _ HEAP ltac:(lia) Dp ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. try rewrite (sx32_of_Z (zget h (zz / 2))) by lia.
    (* [comment removed for export] *)
    brun.
    pose proof (ovw_read b0segs _ WT w Jw 516 (zget h (zz / 2)) _ WGT ltac:(lia) Dwp ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. try rewrite (sx32_of_Z (zget w (zget h (zz / 2)))) by lia.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - enter_with (K h zz m _ _ _ _ _); [st_eq| | lia| exact HW| exact HEAP| exact WGT| exact MI| exact MU| exact WM].
      apply upheap_loop_stop. rewrite shiftr1_div2. apply Z.ltb_ge. lia.
    - assert (Hzz2 : (2 <= zz)%Z).
      { destruct (Z_lt_le_dec zz 2); [|assumption]. exfalso. replace (zz / 2)%Z with 0%Z in Kc by (Z.div_mod_to_equations; lia).
        rewrite S1, S2 in Kc. lia. }
      (* [comment removed for export] *)
      brun.
      pose proof (u32arr_store_ok b0segs m HP _ zz _ HEAP ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
      wstep. store_addr (HP + 4 * zz)%Z. ovw_store HEAP zz (zget h (zz / 2))%Z wval_lit.
      assert (HW1 : hw (zset h zz (zget h (zz / 2))) w nHm nNq) by (apply hw_hset; [exact HW| lia| lia]).
      assert (B : (zz / 2 / 2 * 4 <= zz)%Z) by (Z.div_mod_to_equations; lia).
      (* [comment removed for export] *)
      brun_to 0xa8a30%Z.
      enter_with (IH (zz / 2)%Z nHm nNq (zset h zz (zget h (zz / 2))) w me); [st_eq| lia| lia| | lia| exact HW1| exact HEAP| exact WGT| exact MI| exact MU| exact WM| exact SHh| exact SHw|].
      + rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hf by lia. apply Z.div_lt_upper_bound; lia.
      + intros h' zz' m' y5 y6 y10 y11 y17 E Hzz' HW'. eapply K; [| lia| exact HW'].
        rewrite upheap_loop_S, shiftr1_div2. replace (zget w nNq <? zget w (zget h (zz / 2)))%Z with true by (symmetry; apply Z.ltb_lt; lia). exact E.
  Qed.
End B0HM.

End ACeilS1.
