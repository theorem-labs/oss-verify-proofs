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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzTac BzTac2 BzArr BzCMem BzCHuff BzArrD CmpMem CmpCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF1.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFsKit0 CmpHmKit.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.BzCFactsHm OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpFsKit0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanCut A0_cmp_hmV.
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

Section A0HM.
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
  (* [comment removed for export] *)
  Notation RR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (he_sp X) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 2) (Z_to_bv 64 17) (Z_to_bv 64 (A + 1)) s5 (Z_to_bv 64 HP) (Z_to_bv 64 WT) (Z_to_bv 64 (El + lb - 1)) (Z_to_bv 64 PR)
         (Z_to_bv 64 A) cSB t3 t4 t5 t6).
  Notation Wh := [(HP, HP + 1040)]%Z.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma lor_even1 : forall z, (0 <= z)%Z -> Z.lor (z * 2) 1 = (z * 2 + 1)%Z.
  Proof.
    intros z Hz. pose proof (Z.add_lor_land (z * 2) 1) as E.
    assert (L : Z.land (z * 2) 1 = 0%Z); [|lia].
    rewrite land1_mod2. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_hm_down1 : forall (f : nat) (zz nHq nN n1 tmp : Z) (h w : zarr) (me m : word -> option byte)
      (ra t0 a0 a1 s5 t3 t4 t5 t6 : word),
    (1 <= zz)%Z -> (zz * 2 <= nHq)%Z -> (nHq <= 258)%Z -> (nHq < zz * 2 ^ Z.of_nat f)%Z -> (0 <= nN <= 515)%Z ->
    (0 <= tmp <= nN)%Z -> hw h w nHq nN ->
    u32arr a0segs m HP (ovw h Jh 260) -> u32arr a0segs m WT (ovw w Jw 516) -> mem_inv a0segs m ->
    munch Wh me m -> wmono a0segs me m ->
    shzW a0segs Wh me HP (HP + 1040) -> shzW a0segs Wh me WT (WT + 2064) ->
    (forall h' zz' m' (t1 t2 a0 a1 t3 t4 : word),
      downheap_loop f h w nHq zz tmp = (h', zz') -> (1 <= zz' <= nHq)%Z -> hw h' w nHq nN ->
      u32arr a0segs m' HP (ovw h' Jh 260) -> u32arr a0segs m' WT (ovw w Jw 516) -> mem_inv a0segs m' ->
      munch Wh me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (RR ra (Z_to_bv 64 zz') t1 t2 a0 a1 (Z_to_bv 64 tmp) (Z_to_bv 64 (nHq + 1)) (Z_to_bv 64 nN) (Z_to_bv 64 nHq) (Z_to_bv 64 n1) (Z_to_bv 64 (zget w tmp)) s5 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x9d78c) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RR ra t0 (Z_to_bv 64 zz) (Z_to_bv 64 (zz * 2)) a0 a1 (Z_to_bv 64 tmp) (Z_to_bv 64 (nHq + 1)) (Z_to_bv 64 nN) (Z_to_bv 64 nHq) (Z_to_bv 64 n1) (Z_to_bv 64 (zget w tmp)) s5 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x9d61c) fc None m (seg_rom a0segs)).
  Proof.
    induction f as [|f IH]. { intros. cbn in H2. lia. }
    intros zz nHq nN n1 tmp h w me m ra t0 a0 a1 s5 t3 t4 t5 t6 Hzz Hyy HnH Hf HnN Htmp HW HEAP WGT MI MU WM SHh SHw K.
    hmenv_open XOK. ahenv_open YOK. ahenv_sepx_open YSX. cps_destruct HW as (S1 & S2 & HH & WW).
    pose proof (ovw_length h Jh 260 ltac:(lia)) as LH. pose proof (ovw_length w Jw 516 ltac:(lia)) as LW.
    pose proof (WW tmp ltac:(lia)) as [Dwt Rwt].
    (* [comment removed for export] *)
    assert (TAIL : forall yy' (x10 x11 x28 x29 : word), yy' = dh_child h w nHq (zz * 2) -> (zz * 2 <= yy' <= nHq)%Z -> (yy' <= zz * 2 + 1)%Z ->
      evt a0segs Q (MS (RR ra (Z_to_bv 64 yy') (Z_to_bv 64 zz) (Z_to_bv 64 yy') x10 x11 (Z_to_bv 64 tmp) (Z_to_bv 64 (nHq + 1)) (Z_to_bv 64 nN) (Z_to_bv 64 nHq) (Z_to_bv 64 n1) (Z_to_bv 64 (zget w tmp)) s5 x28 x29 t5 t6)
                       F (Z_to_bv 64 0x9d6a8) fc None m (seg_rom a0segs))).
    { intros yy' x10 x11 x28 x29 Eyy Hyy' Hyy2.
      pose proof (HH yy' ltac:(lia)) as [Dy Ry]. pose proof (WW (zget h yy') ltac:(lia)) as [Dwy Rwy].
      (* [comment removed for export] *)
      arun.
      pose proof (ovw_read a0segs _ HP h Jh 260 yy' _ HEAP ltac:(lia) Dy ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget h yy')) by lia.
      (* [comment removed for export] *)
      arun.
      pose proof (ovw_read a0segs _ WT w Jw 516 (zget h yy') _ WGT ltac:(lia) Dwy ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget w (zget h yy'))) by lia.
      (* [comment removed for export] *)
      wstep; if_cases Kb; zify_cond_z Kb.
      - (* [comment removed for export] *)
        wstep.
        enter_with (K h zz m _ _ _ _ _ _); [st_eq| | lia| exact (conj S1 (conj S2 (conj HH WW)))| exact HEAP| exact WGT| exact MI| exact MU| exact WM].
        apply downheap_loop_stop2; [apply Z.ltb_ge; rewrite shiftl1_mul2; lia|]. rewrite shiftl1_mul2, <- Eyy. apply Z.ltb_lt. exact Kb.
      - (* [comment removed for export] *)
        arun.
        pose proof (u32arr_store_ok a0segs m HP _ zz _ HEAP ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
        wstep. store_addr (HP + 4 * zz)%Z. ovw_store HEAP zz (zget h yy') wval_lit.
        assert (HW1 : hw (zset h zz (zget h yy')) w nHq nN) by (apply hw_hset; [exact (conj S1 (conj S2 (conj HH WW)))| lia| lia]).
        (* [comment removed for export] *)
        arun; if_cases Kl; zify_cond_z Kl.
        + enter_with (IH yy' nHq nN n1 tmp (zset h zz (zget h yy')) w me); [st_eq| lia| lia| lia| | lia| lia| exact HW1| exact HEAP| exact WGT| exact MI| exact MU| exact WM| exact SHh| exact SHw|].
          * rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hf by lia.
            eapply Z.lt_le_trans; [exact Hf|]. rewrite Z.mul_assoc.
            apply Z.mul_le_mono_nonneg_r; [apply Z.pow_nonneg; discriminate | exact (proj1 Hyy')].
          * intros h' zz' m' y6 y7 y10 y11 y28 y29 E Hzz' HW'. eapply K; [| lia| exact HW'].
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
      wstep. enter_with (TAIL (zz * 2)%Z a0 a1 t3 t4); [st_eq| | lia| lia].
      unfold dh_child. replace (zz * 2 <? nHq)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
    - (* [comment removed for export] *)
      pose proof (HH (zz * 2)%Z ltac:(lia)) as [D0 R0]. pose proof (HH (zz * 2 + 1)%Z ltac:(lia)) as [D1 R1].
      pose proof (WW (zget h (zz * 2)) ltac:(lia)) as [Dw0 Rw0]. pose proof (WW (zget h (zz * 2 + 1)) ltac:(lia)) as [Dw1 Rw1].
      wstep. rewrite lor_even1 by lia.
      (* [comment removed for export] *)
      arun.
      pose proof (ovw_read a0segs _ HP h Jh 260 (zz * 2 + 1) _ HEAP ltac:(lia) D1 ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget h (zz * 2 + 1))) by lia.
      (* [comment removed for export] *)
      arun.
      pose proof (ovw_read a0segs _ WT w Jw 516 (zget h (zz * 2 + 1)) _ WGT ltac:(lia) Dw1 ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget w (zget h (zz * 2 + 1)))) by lia.
      (* [comment removed for export] *)
      arun.
      pose proof (ovw_read a0segs _ HP h Jh 260 (zz * 2) _ HEAP ltac:(lia) D0 ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget h (zz * 2))) by lia.
      (* [comment removed for export] *)
      arun.
      pose proof (ovw_read a0segs _ WT w Jw 516 (zget h (zz * 2)) _ WGT ltac:(lia) Dw0 ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget w (zget h (zz * 2)))) by lia.
      (* [comment removed for export] *)
      wstep; if_cases Kw; zify_cond_z Kw.
      + (* [comment removed for export] *)
        wstep. wstep. enter_with (TAIL (zz * 2 + 1)%Z _ _ _ _); [st_eq| | lia| lia].
        unfold dh_child. replace (zz * 2 <? nHq)%Z with true by (symmetry; apply Z.ltb_lt; lia).
        replace (zget w (zget h (zz * 2 + 1)) <? zget w (zget h (zz * 2)))%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
      + (* [comment removed for export] *)
        wstep. wstep. wstep. enter_with (TAIL (zz * 2)%Z _ _ _ _); [st_eq| | lia| lia].
        unfold dh_child. replace (zz * 2 <? nHq)%Z with true by (symmetry; apply Z.ltb_lt; lia).
        replace (zget w (zget h (zz * 2 + 1)) <? zget w (zget h (zz * 2)))%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_hm_down2 : forall (f : nat) (zz nHq nN n1 n2 tmp : Z) (h w : zarr) (me m : word -> option byte)
      (ra a0 a1 a2 a7 s5 t4 : word),
    (1 <= zz)%Z -> (zz * 2 <= nHq)%Z -> (nHq <= 258)%Z -> (nHq < zz * 2 ^ Z.of_nat f)%Z -> (0 <= nN <= 515)%Z ->
    (0 <= tmp <= nN)%Z -> hw h w nHq nN ->
    u32arr a0segs m HP (ovw h Jh 260) -> u32arr a0segs m WT (ovw w Jw 516) -> mem_inv a0segs m ->
    munch Wh me m -> wmono a0segs me m ->
    shzW a0segs Wh me HP (HP + 1040) -> shzW a0segs Wh me WT (WT + 2064) ->
    (forall h' zz' m' (ra a1 a2 s5 t5 t6 : word),
      downheap_loop f h w nHq zz tmp = (h', zz') -> (1 <= zz' <= nHq)%Z -> hw h' w nHq nN ->
      u32arr a0segs m' HP (ovw h' Jh 260) -> u32arr a0segs m' WT (ovw w Jw 516) -> mem_inv a0segs m' ->
      munch Wh me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (RR ra (Z_to_bv 64 n2) (Z_to_bv 64 tmp) (Z_to_bv 64 (zget w tmp)) a0 a1 a2 (Z_to_bv 64 (nHq + 2)) (Z_to_bv 64 nN) (Z_to_bv 64 (nHq + 1)) (Z_to_bv 64 n1) a7 s5
                           (Z_to_bv 64 nHq) (Z_to_bv 64 zz') t5 t6)
                       F (Z_to_bv 64 0x9d96c) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RR ra (Z_to_bv 64 n2) (Z_to_bv 64 tmp) (Z_to_bv 64 (zget w tmp)) a0 a1 a2 (Z_to_bv 64 (nHq + 2)) (Z_to_bv 64 nN) (Z_to_bv 64 (nHq + 1)) (Z_to_bv 64 n1) a7 s5
                         (Z_to_bv 64 nHq) t4 (Z_to_bv 64 zz) (Z_to_bv 64 (zz * 2)))
                     F (Z_to_bv 64 0x9d804) fc None m (seg_rom a0segs)).
  Proof.
    induction f as [|f IH]. { intros. cbn in H2. lia. }
    intros zz nHq nN n1 n2 tmp h w me m ra a0 a1 a2 a7 s5 t4 Hzz Hyy HnH Hf HnN Htmp HW HEAP WGT MI MU WM SHh SHw K.
    hmenv_open XOK. ahenv_open YOK. ahenv_sepx_open YSX. cps_destruct HW as (S1 & S2 & HH & WW).
    pose proof (ovw_length h Jh 260 ltac:(lia)) as LH. pose proof (ovw_length w Jw 516 ltac:(lia)) as LW.
    pose proof (WW tmp ltac:(lia)) as [Dwt Rwt].
    (* [comment removed for export] *)
    assert (TAIL : forall yy' (x1 x11 x12 x21 : word), yy' = dh_child h w nHq (zz * 2) -> (zz * 2 <= yy' <= nHq)%Z -> (yy' <= zz * 2 + 1)%Z ->
      evt a0segs Q (MS (RR x1 (Z_to_bv 64 n2) (Z_to_bv 64 tmp) (Z_to_bv 64 (zget w tmp)) a0 x11 x12 (Z_to_bv 64 (nHq + 2)) (Z_to_bv 64 nN) (Z_to_bv 64 (nHq + 1)) (Z_to_bv 64 n1) a7 x21
                           (Z_to_bv 64 nHq) (Z_to_bv 64 yy') (Z_to_bv 64 zz) (Z_to_bv 64 yy'))
                       F (Z_to_bv 64 0x9d890) fc None m (seg_rom a0segs))).
    { intros yy' x1 x11 x12 x21 Eyy Hyy' Hyy2.
      pose proof (HH yy' ltac:(lia)) as [Dy Ry]. pose proof (WW (zget h yy') ltac:(lia)) as [Dwy Rwy].
      (* [comment removed for export] *)
      arun.
      pose proof (ovw_read a0segs _ HP h Jh 260 yy' _ HEAP ltac:(lia) Dy ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget h yy')) by lia.
      (* [comment removed for export] *)
      arun.
      pose proof (ovw_read a0segs _ WT w Jw 516 (zget h yy') _ WGT ltac:(lia) Dwy ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget w (zget h yy'))) by lia.
      (* [comment removed for export] *)
      wstep; if_cases Kb; zify_cond_z Kb.
      - (* [comment removed for export] *)
        wstep.
        enter_with (K h zz m _ _ _ _ _ _); [st_eq| | lia| exact (conj S1 (conj S2 (conj HH WW)))| exact HEAP| exact WGT| exact MI| exact MU| exact WM].
        apply downheap_loop_stop2; [apply Z.ltb_ge; rewrite shiftl1_mul2; lia|]. rewrite shiftl1_mul2, <- Eyy. apply Z.ltb_lt. exact Kb.
      - (* [comment removed for export] *)
        arun.
        pose proof (u32arr_store_ok a0segs m HP _ zz _ HEAP ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
        wstep. store_addr (HP + 4 * zz)%Z. ovw_store HEAP zz (zget h yy') wval_lit.
        assert (HW1 : hw (zset h zz (zget h yy')) w nHq nN) by (apply hw_hset; [exact (conj S1 (conj S2 (conj HH WW)))| lia| lia]).
        (* [comment removed for export] *)
        arun; if_cases Kl; zify_cond_z Kl.
        + enter_with (IH yy' nHq nN n1 n2 tmp (zset h zz (zget h yy')) w me); [st_eq| lia| lia| lia| | lia| lia| exact HW1| exact HEAP| exact WGT| exact MI| exact MU| exact WM| exact SHh| exact SHw|].
          * rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hf by lia.
            eapply Z.lt_le_trans; [exact Hf|]. rewrite Z.mul_assoc.
            apply Z.mul_le_mono_nonneg_r; [apply Z.pow_nonneg; discriminate | exact (proj1 Hyy')].
          * intros h' zz' m' y1 y11 y12 y21 y30 y31 E Hzz' HW'. eapply K; [| lia| exact HW'].
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
      wstep. enter_with (TAIL (zz * 2)%Z ra a1 a2 s5); [st_eq| | lia| lia].
      unfold dh_child. replace (zz * 2 <? nHq)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
    - (* [comment removed for export] *)
      pose proof (HH (zz * 2)%Z ltac:(lia)) as [D0 R0]. pose proof (HH (zz * 2 + 1)%Z ltac:(lia)) as [D1 R1].
      pose proof (WW (zget h (zz * 2)) ltac:(lia)) as [Dw0 Rw0]. pose proof (WW (zget h (zz * 2 + 1)) ltac:(lia)) as [Dw1 Rw1].
      wstep. rewrite lor_even1 by lia.
      (* [comment removed for export] *)
      arun.
      pose proof (ovw_read a0segs _ HP h Jh 260 (zz * 2 + 1) _ HEAP ltac:(lia) D1 ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget h (zz * 2 + 1))) by lia.
      (* [comment removed for export] *)
      arun.
      pose proof (ovw_read a0segs _ WT w Jw 516 (zget h (zz * 2 + 1)) _ WGT ltac:(lia) Dw1 ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget w (zget h (zz * 2 + 1)))) by lia.
      (* [comment removed for export] *)
      arun.
      pose proof (ovw_read a0segs _ HP h Jh 260 (zz * 2) _ HEAP ltac:(lia) D0 ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget h (zz * 2))) by lia.
      (* [comment removed for export] *)
      arun.
      pose proof (ovw_read a0segs _ WT w Jw 516 (zget h (zz * 2)) _ WGT ltac:(lia) Dw0 ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget w (zget h (zz * 2)))) by lia.
      (* [comment removed for export] *)
      wstep; if_cases Kw; zify_cond_z Kw.
      + (* [comment removed for export] *)
        wstep. wstep. enter_with (TAIL (zz * 2 + 1)%Z _ _ _ _); [st_eq| | lia| lia].
        unfold dh_child. replace (zz * 2 <? nHq)%Z with true by (symmetry; apply Z.ltb_lt; lia).
        replace (zget w (zget h (zz * 2 + 1)) <? zget w (zget h (zz * 2)))%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
      + (* [comment removed for export] *)
        wstep. wstep. wstep. enter_with (TAIL (zz * 2)%Z _ _ _ _); [st_eq| | lia| lia].
        unfold dh_child. replace (zz * 2 <? nHq)%Z with true by (symmetry; apply Z.ltb_lt; lia).
        replace (zget w (zget h (zz * 2 + 1)) <? zget w (zget h (zz * 2)))%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_hm_up2 : forall (f : nat) (zz nHm nNq : Z) (h w : zarr) (me m : word -> option byte)
      (ra t1 t2 a0 s5 t3 t4 t5 t6 : word),
    (1 <= zz <= nHm)%Z -> (nHm <= 258)%Z -> (zz < 2 ^ Z.of_nat f)%Z -> (1 <= nNq <= 515)%Z ->
    (zget w nNq <? zget w (zget h (Z.shiftr zz 1)))%Z = true ->
    hw h w nHm nNq ->
    u32arr a0segs m HP (ovw h Jh 260) -> u32arr a0segs m WT (ovw w Jw 516) -> mem_inv a0segs m ->
    munch Wh me m -> wmono a0segs me m ->
    shzW a0segs Wh me HP (HP + 1040) -> shzW a0segs Wh me WT (WT + 2064) ->
    (forall h' zz' m' (t1 a0 a1 a2 : word),
      upheap_loop f h w zz nNq = (h', zz') -> (1 <= zz' <= zz)%Z -> hw h' w nHm nNq ->
      u32arr a0segs m' HP (ovw h' Jh 260) -> u32arr a0segs m' WT (ovw w Jw 516) -> mem_inv a0segs m' ->
      munch Wh me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (RR ra (Z_to_bv 64 nNq) t1 t2 a0 a1 a2 (Z_to_bv 64 (nHm + 1)) (Z_to_bv 64 (nNq - 1)) (Z_to_bv 64 nHm) (Z_to_bv 64 (zget w nNq)) (Z_to_bv 64 zz') s5 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x9db38) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RR ra (Z_to_bv 64 nNq) t1 t2 a0 (Z_to_bv 64 (zz / 2)) (Z_to_bv 64 (zget h (zz / 2))) (Z_to_bv 64 (nHm + 1)) (Z_to_bv 64 (nNq - 1)) (Z_to_bv 64 nHm)
                         (Z_to_bv 64 (zget w nNq)) (Z_to_bv 64 zz) s5 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x9daa0) fc None m (seg_rom a0segs)).
  Proof.
    induction f as [|f IH].
    { intros. cbn in H1. lia. }
    intros zz nHm nNq h w me m ra t1 t2 a0 s5 t3 t4 t5 t6 Hzz HnH Hf HnN CT HW HEAP WGT MI MU WM SHh SHw K.
    hmenv_open XOK. ahenv_open YOK. ahenv_sepx_open YSX. cps_destruct HW as (S1 & S2 & HH & WW).
    rewrite shiftr1_div2 in *.
    assert (Hzz2 : (2 <= zz)%Z).
    { destruct (Z_lt_le_dec zz 2); [|assumption]. exfalso. replace (zz / 2)%Z with 0%Z in CT by (Z.div_mod_to_equations; lia).
      rewrite S1, S2 in CT. apply Z.ltb_lt in CT. pose proof (WW nNq ltac:(lia)). lia. }
    assert (Hz2 : (1 <= zz / 2 < zz)%Z) by (Z.div_mod_to_equations; lia).
    pose proof (HH (zz / 2)%Z ltac:(lia)) as [Dp Rp]. pose proof (WW nNq ltac:(lia)) as [Dwi Rwi].
    pose proof (ovw_length h Jh 260 ltac:(lia)) as LH. pose proof (ovw_length w Jw 516 ltac:(lia)) as LW.
    (* [comment removed for export] *)
    arun.
    pose proof (u32arr_store_ok a0segs m HP _ zz _ HEAP ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    wstep. store_addr (HP + 4 * zz)%Z. ovw_store HEAP zz (zget h (zz / 2))%Z wval_lit.
    assert (Hz4 : (0 <= zz / 2 / 2 <= zz / 2)%Z) by (Z.div_mod_to_equations; lia).
    set (h1 := zset h zz (zget h (zz / 2))) in *.
    assert (HW1 : hw h1 w nHm nNq) by (subst h1; apply hw_hset; [exact (conj S1 (conj S2 (conj HH WW)))| lia| lia]).
    cps_destruct HW1 as (S1' & _ & HH1 & _).
    pose proof (HH1 (zz / 2 / 2)%Z ltac:(lia)) as [Dq Rq].
    (* [comment removed for export] *)
    arun.
    pose proof (ovw_read a0segs _ HP h1 Jh 260 (zz / 2 / 2) _ HEAP ltac:(lia) Dq ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. try rewrite (sx32_of_Z (zget h1 (zz / 2 / 2))) by lia.
    (* [comment removed for export] *)
    pose proof (WW (zget h1 (zz / 2 / 2)) ltac:(lia)) as [Dw2 Rw2].
    arun.
    pose proof (ovw_read a0segs _ WT w Jw 516 (zget h1 (zz / 2 / 2)) _ WGT ltac:(lia) Dw2 ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. try rewrite (sx32_of_Z (zget w (zget h1 (zz / 2 / 2)))) by lia.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      enter_with (IH (zz / 2)%Z nHm nNq h1 w me); [st_eq| lia| lia| | lia| | | exact HEAP| exact WGT| exact MI| exact MU| exact WM| exact SHh| exact SHw| ].
      + rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hf by lia. apply Z.div_lt_upper_bound; lia.
      + rewrite shiftr1_div2. apply Z.ltb_lt. exact Kc.
      + split; [exact S1'| split; [exact S2| split; [exact HH1| exact WW]]].
      + intros h' zz' m' t1' a0' a1' a2' E Hzz' HW'. eapply K; [| lia| exact HW'].
        rewrite upheap_loop_S, shiftr1_div2, CT. subst h1. exact E.
    - (* [comment removed for export] *)
      wstep.
      enter_with (K h1 (zz / 2)%Z _ _ _ _ _); [st_eq| | lia| | exact HEAP| exact WGT| exact MI| exact MU| exact WM].
      + rewrite upheap_loop_S, shiftr1_div2, CT. apply upheap_loop_stop. rewrite shiftr1_div2. apply Z.ltb_ge. subst h1. lia.
      + split; [exact S1'| split; [exact S2| split; [exact HH1| exact WW]]].
  Qed.
End A0HM.

End ACeilS1.
