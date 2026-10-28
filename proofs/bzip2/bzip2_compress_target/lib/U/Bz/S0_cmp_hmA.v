(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzCHuff BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCut CmpCut0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF1.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpFsKit0 CmpHmKit.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.BzCFactsHm OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpFsKit0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpHmKit.
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
  Notation SC := ([C8 (Z_to_bv 64 17); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 2060); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (El + lb - 1))]).
  (* [comment removed for export] *)
  Notation RW ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 (p - 32)) gp tp t0 t1 t2 (he_s0 X) (he_s1 X) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 (El + lb)) (he_s3 X) (he_s4 X) (he_s5 X) (he_s6 X) (he_s7 X) (he_s8 X) (he_s9 X) (he_s10 X) (he_s11 X) t3 t4 t5 t6).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_hm_winit : forall (n : nat) (i : Z) (w : zarr) (me m : word -> option byte)
      (ra t0 t1 t2 t3 t4 t5 t6 : word),
    (i + Z.of_nat n = A)%Z -> (0 <= i)%Z -> (1 <= n)%nat ->
    u32arr s0segs m (p + 2088) (ovw w Jw 516) -> u32arr s0segs m Ef (ovw freq Jf NF) -> mem_inv s0segs m ->
    munch [(p + 2088, p + 4152)]%Z me m -> wmono s0segs me m ->
    (forall m' (t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 : word),
      u32arr s0segs m' (p + 2088) (ovw (hm_winit n w freq fb i) Jw 516) -> u32arr s0segs m' Ef (ovw freq Jf NF) -> mem_inv s0segs m' ->
      munch [(p + 2088, p + 4152)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RW ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0x23c70) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RW ra t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 (Ef + 4 * fb)) (Z_to_bv 64 (p + 2092 + 4 * i)) (Z_to_bv 64 1)
                         (Z_to_bv 64 (2060 - 4 * i)) (Z_to_bv 64 (A - i)) (Z_to_bv 64 (Ef + 4 * (fb + i))) (Z_to_bv 64 (Ef + 4 * (fb + i))) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x23c24) fc None m (seg_rom s0segs)).
  Proof using XOK.
    induction n as [|n IH]. { intros; lia. }
    intros i w me m ra t0 t1 t2 t3 t4 t5 t6 Hi Hi0 Hn WGT FREQ MI MU WM K.
    hmenv_open XOK. pose proof (FRQ i ltac:(lia)) as [Df Rf].
    pose proof (ovw_length w Jw 516 ltac:(lia)) as LW. pose proof (ovw_length freq Jf NF ltac:(lia)) as LF.
    (* [comment removed for export] *)
    wstep; notrap. wstep; flags. wstep. wstep; notrap. wstep; notrap.
    pose proof (ovw_read s0segs _ Ef freq Jf NF (fb + i) _ FREQ ltac:(lia) Df ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. try rewrite (zx32_of_Z (zget freq (fb + i))) by lia.
    (* [comment removed for export] *)
    wstep. wstep; notrap. wstep; notrap. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    (* [comment removed for export] *)
    pose proof (u32arr_store_ok s0segs m (p + 2088) _ (i + 1) _ WGT ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    wstep. store_addr (p + 2088 + 4 * (i + 1))%Z.
    ovw_store WGT (i + 1)%Z (Z.shiftl (fmax1 (zget freq (fb + i))) 8)
      (unfold fmax1; rewrite shiftl8_mul, unsigned_lit_mod32; destruct (Z.ltb_spec (zget freq (fb + i)) 1); destruct (Z.eqb_spec (zget freq (fb + i)) 0); try lia; cbn [Z.b2z]; rewrite Z.mod_small by lia; f_equal; lia).
    (* [comment removed for export] *)
    wstep. wstep; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (i + 1)%Z (zset w (i + 1) (Z.shiftl (fmax1 (zget freq (fb + i))) 8)) me); [st_eq| lia| lia| lia| exact WGT| exact FREQ| exact MI| exact MU| exact WM|].
      intros m' x5 x6 y0 y1 y2 y3 y4 y5 y6 y7. unfold fmax1. rewrite <- hm_winit_S. exact (K m' x5 x6 y0 y1 y2 y3 y4 y5 y6 y7).
    - assert (n = 0)%nat by lia. subst n.
      enter_with (K _ _ _ _ _ _ _ _ _ _ _); [st_eq| | exact FREQ| exact MI| exact MU| exact WM]. rewrite hm_winit_S. cbn [hm_winit]. unfold fmax1 in WGT. exact WGT.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_hm_fup : forall (f : nat) (zz i : Z) (h w : zarr) (me m : word -> option byte)
      (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    (1 <= zz <= i)%Z -> (i <= A)%Z -> (zz < 2 ^ Z.of_nat f)%Z ->
    hw h w i A ->
    u32arr s0segs m (p + 4152) (ovw h Jh 260) -> u32arr s0segs m (p + 2088) (ovw w Jw 516) -> mem_inv s0segs m ->
    munch [(p + 4152, p + 5192)]%Z me m -> wmono s0segs me m ->
    (forall h' zz' m' (a4 a5 a6 : word),
      upheap_loop f h w zz i = (h', zz') -> (1 <= zz' <= zz)%Z -> hw h' w i A ->
      u32arr s0segs m' (p + 4152) (ovw h' Jh 260) -> u32arr s0segs m' (p + 2088) (ovw w Jw 516) -> mem_inv s0segs m' ->
      munch [(p + 4152, p + 5192)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RR RA t0 t1 t2 (Z_to_bv 64 i) (Z_to_bv 64 i) (Z_to_bv 64 (zget w i)) (Z_to_bv 64 zz') a4 a5 a6 a7 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x23d8c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RR RA t0 t1 t2 (Z_to_bv 64 i) (Z_to_bv 64 i) (Z_to_bv 64 (zget w i)) (Z_to_bv 64 zz) a4 a5 a6 a7 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x23d44) fc None m (seg_rom s0segs)).
  Proof using XOK.
    induction f as [|f IH].
    { intros. cbn in H1. lia. }
    intros zz i h w me m t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 Hzz Hi Hf HW HEAP WGT MI MU WM K.
    hmenv_open XOK. pose proof HW as HW0. cps_destruct HW0 as (S1 & S2 & HH & WW).
    assert (Hz2 : (0 <= zz / 2 < zz)%Z) by (Z.div_mod_to_equations; lia).
    pose proof (HH (zz / 2)%Z ltac:(lia)) as [Dp Rp]. pose proof (WW i ltac:(lia)) as [Dwi Rwi]. pose proof (WW (zget h (zz / 2)) ltac:(lia)) as [Dwp Rwp].
    pose proof (ovw_length h Jh 260 ltac:(lia)) as LH. pose proof (ovw_length w Jw 516 ltac:(lia)) as LW.
    (* [comment removed for export] *)
    wstep. wstep. wstep; notrap. wstep.
    pose proof (ovw_read s0segs _ (p + 4152) h Jh 260 (zz / 2) _ HEAP ltac:(lia) Dp ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. try rewrite (sx32_of_Z (zget h (zz / 2))) by lia.
    (* [comment removed for export] *)
    wstep; notrap. wstep. wstep; notrap. wstep.
    pose proof (ovw_read s0segs _ (p + 2088) w Jw 516 (zget h (zz / 2)) _ WGT ltac:(lia) Dwp ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. try rewrite (sx32_of_Z (zget w (zget h (zz / 2)))) by lia.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      enter_with (K h zz m _ _ _); [st_eq| | lia| exact HW| exact HEAP| exact WGT| exact MI| exact MU| exact WM].
      apply upheap_loop_stop. rewrite shiftr1_div2. apply Z.ltb_ge. lia.
    - (* [comment removed for export] *)
      assert (Hzz2 : (2 <= zz)%Z).
      { destruct (Z_lt_le_dec zz 2); [|assumption]. exfalso. replace (zz / 2)%Z with 0%Z in Kc by (Z.div_mod_to_equations; lia).
        rewrite S1, S2 in Kc. lia. }
      wstep; notrap. wstep. wstep; notrap. wstep.
      pose proof (u32arr_store_ok s0segs m (p + 4152) _ zz _ HEAP ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
      wstep. store_addr (p + 4152 + 4 * zz)%Z. ovw_store HEAP zz (zget h (zz / 2))%Z wval_lit.
      assert (HW1 : hw (zset h zz (zget h (zz / 2))) w i A) by (apply hw_hset; [exact HW| lia| lia]).
      wstep. wstep.
      enter_with (IH (zz / 2)%Z i (zset h zz (zget h (zz / 2))) w me); [st_eq| lia| lia| | exact HW1| exact HEAP| exact WGT| exact MI| exact MU| exact WM|].
      + rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hf by lia. apply Z.div_lt_upper_bound; lia.
      + intros h' zz' m' a4' a5' a6' E Hzz' HW'. eapply K; [| lia| exact HW'].
        rewrite upheap_loop_S, shiftr1_div2. replace (zget w i <? zget w (zget h (zz / 2)))%Z with true by (symmetry; apply Z.ltb_lt; lia). exact E.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_hm_fill : forall (n : nat) (i : Z) (h w par : zarr) (me m : word -> option byte)
      (t0 t1 t2 a1 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    (i + Z.of_nat n = A + 1)%Z -> (1 <= i)%Z -> (1 <= n)%nat ->
    hw h w (i - 1) A ->
    u32arr s0segs m (p + 4152) (ovw h Jh 260) -> u32arr s0segs m (p + 2088) (ovw w Jw 516) -> u32arr s0segs m (p + 24) (ovw par Jp 516) ->
    rw_cells s0segs m (p - 32 + 8) SC -> mem_inv s0segs m ->
    munch [(p + 24, p + 5192)]%Z me m -> wmono s0segs me m ->
    (forall h' m' (a0 a1 a2 a3 a4 a5 a6 a7 : word),
      h' = fill_h n h w (i - 1) i -> hw h' w A A ->
      u32arr s0segs m' (p + 4152) (ovw h' Jh 260) -> u32arr s0segs m' (p + 2088) (ovw w Jw 516) -> u32arr s0segs m' (p + 24) (ovw (pneg par i n) Jp 516) ->
      rw_cells s0segs m' (p - 32 + 8) SC -> mem_inv s0segs m' ->
      munch [(p + 24, p + 5192)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RR RA t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0x23db0) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RR RA t0 t1 t2 (Z_to_bv 64 i) a1 (Z_to_bv 64 (i - 1)) a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0x23d0c) fc None m (seg_rom s0segs)).
  Proof using XOK.
    induction n as [|n IH]. { intros; lia. }
    intros i h w par me m t0 t1 t2 a1 a3 a4 a5 a6 a7 t3 t4 t5 t6 Hi Hi1 Hn HW HEAP WGT PAR SCm MI MU WM K.
    hmenv_open XOK.
    pose proof (ovw_length h Jh 260 ltac:(lia)) as LH. pose proof (ovw_length w Jw 516 ltac:(lia)) as LW. pose proof (ovw_length par Jp 516 ltac:(lia)) as LP.
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    pose proof (u32arr_store_ok s0segs m (p + 24) _ i _ PAR ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    wstep. store_addr (p + 24 + 4 * i)%Z. ovw_store PAR i (-1)%Z (rewrite unsigned_lit_mod32; reflexivity).
    (* [comment removed for export] *)
    wstep; notrap. wstep. wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm (p + 4152) _ i _ HEAP ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO2 end.
    wstep. store_addr (p + 4152 + 4 * i)%Z. ovw_store HEAP i i wval_lit.
    set (h0 := zset h i i) in *.
    assert (HW0 : hw h0 w i A). { subst h0. pose proof (hw_push h w (i - 1) A i HW ltac:(lia) ltac:(lia)) as PU. replace (i - 1 + 1)%Z with i in PU by lia. exact PU. }
    pose proof HW0 as HW0'. cps_destruct HW0' as (S1 & S2 & HH & WW). pose proof (WW i ltac:(lia)) as [Dwi Rwi].
    (* [comment removed for export] *)
    wstep. wstep; notrap. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (ovw_read s0segs mm (p + 2088) w Jw 516 i _ WGT ltac:(lia) Dwi ltac:(unfold wa; f_equal; lia)) as RD end.
    wstep. clear RD. try rewrite (sx32_of_Z (zget w i)) by lia.
    (* [comment removed for export] *)
    wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mq end.
    enter_with (S0_hm_fup 20%nat i i h0 w mq mq);
      [st_eq| lia| lia| cbn; lia| exact HW0| exact HEAP| exact WGT| exact MI| apply munch_refl| apply wmono_refl|].
    intros h' zz' m' y4 y5 y6 E Hzz' HW' HEAP' WGT' MI' MU' WM'.
    clear HEAP WGT MI. transport_after_call s0segs mq m' MU' WM'.
    pose proof (ovw_length h' Jh 260 ltac:(lia)) as LH'.
    (* [comment removed for export] *)
    wstep; notrap. wstep. wstep; notrap. wstep.
    pose proof (u32arr_store_ok s0segs m' (p + 4152) _ zz' _ HEAP' ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO3.
    wstep. store_addr (p + 4152 + 4 * zz')%Z. ovw_store HEAP' zz' i wval_lit.
    assert (UP : upheap h0 w i = zset h' zz' i).
    { pose proof (upheap_eq h0 w i h' zz') as U. replace (zget h0 i) with i in U by (subst h0; rewrite zget_zset_same; reflexivity). exact (U E). }
    assert (HW'' : hw (zset h' zz' i) w i A) by (apply hw_hset; [exact HW'| lia| lia]).
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep; if_cases Ke; zify_cond_z Ke.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH (i + 1)%Z (zset h' zz' i) w (zset par i (-1)) me mm) end;
        [st_eq| lia| lia| lia| | exact HEAP'| exact WGT'| exact PAR| exact SCm| exact MI'| exact MU| exact WM|].
      + replace (i + 1 - 1)%Z with i by lia. exact HW''.
      + intros h'' m'' z0 z1 z2 z3 z4 z5 z6 z7 Eh HWf. rewrite <- pneg_S. eapply K; [|exact HWf].
        rewrite fill_h_S. replace (i - 1 + 1)%Z with i by lia. fold h0. rewrite UP. replace (i + 1 - 1)%Z with i in Eh by lia. exact Eh.
    - assert (n = 0)%nat by lia. subst n.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (K (zset h' zz' i) mm _ _ _ _ _ _ _ _) end; [st_eq| | | exact HEAP'| exact WGT'| | exact SCm| exact MI'| exact MU| exact WM].
      + rewrite fill_h_S. cbn [fill_h]. replace (i - 1 + 1)%Z with i by lia. fold h0. rewrite UP. reflexivity.
      + replace (hw (zset h' zz' i) w A A) with (hw (zset h' zz' i) w i A) by (f_equal; lia). exact HW''.
      + rewrite pneg_S. cbn [pneg]. exact PAR.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_hm_depth : forall (f : nat) (k j : Z) (par : zarr) (nN : Z) (m : word -> option byte)
      (t0 t1 t2 a0 a1 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    (1 <= k <= nN)%Z -> (nN <= 515)%Z -> (nN - k < Z.of_nat f)%Z -> (0 <= j <= k)%Z ->
    hpar par nN -> (forall x, 1 <= x <= nN -> zget par x = -1 \/ x < zget par x <= nN)%Z ->
    u32arr s0segs m (p + 24) (ovw par Jp 516) ->
    (forall j' (a3 a4 : word), j' = hm_depth f par k j -> (j <= j' <= nN)%Z ->
      evt s0segs Q (MS (RR RA t0 t1 t2 a0 a1 (Z_to_bv 64 j') a3 a4 a5 a6 a7 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x2413c) fc None m (seg_rom s0segs))) ->
    evt s0segs Q (MS (RR RA t0 t1 t2 a0 a1 (Z_to_bv 64 j) (Z_to_bv 64 k) a4 a5 a6 a7 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x2410c) fc None m (seg_rom s0segs)).
  Proof using XOK.
    induction f as [|f IH]. { intros. cbn in H1. lia. }
    intros k j par nN m t0 t1 t2 a0 a1 a4 a5 a6 a7 t3 t4 t5 t6 Hk HN Hf Hj HP PC PAR K.
    hmenv_open XOK. pose proof (HP k ltac:(lia)) as [Dk Rk].
    pose proof (ovw_length par Jp 516 ltac:(lia)) as LP.
    (* [comment removed for export] *)
    wstep. wstep; notrap. wstep.
    pose proof (ovw_read s0segs _ (p + 24) par Jp 516 k _ PAR ltac:(lia) Dk ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. try rewrite (sx32_of_Z_signed (zget par k)) by lia.
    (* [comment removed for export] *)
    wstep; if_cases Kc.
    - assert (G : (zget par k < 0)%Z).
      { apply hm_bvlts0_true; [lia|]. destruct (bv_lts (Z_to_bv 64 (zget par k)) (Z_to_bv 64 0)); [reflexivity| discriminate]. }
      enter_with (K j _ _); [st_eq| | lia]. symmetry. apply hm_depth_stop. apply Z.leb_gt. exact G.
    - (* [comment removed for export] *)
      assert (G : (0 <= zget par k)%Z).
      { apply hm_bvlts0_false; [lia|]. destruct (bv_lts (Z_to_bv 64 (zget par k)) (Z_to_bv 64 0)); [discriminate| reflexivity]. }
      destruct (PC k ltac:(lia)) as [E|R]; [exfalso; lia|].
      wstep. wstep; notrap. wstep. wstep. wstep. wstep; notrap. wstep.
      enter_with (IH (zget par k) (j + 1)%Z par nN m); [st_eq| lia| lia| lia| lia| exact HP| exact PC| exact PAR|].
      intros j' x3 x4 Ej Hj'. eapply K; [|lia]. rewrite hm_depth_S. replace (0 <=? zget par k)%Z with true by (symmetry; apply Z.leb_le; lia). exact Ej.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_hm_lens : forall (n : nat) (i : Z) (len par : zarr) (tl : bool) (nN : Z) (me m : word -> option byte)
      (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    (i + Z.of_nat n = A + 1)%Z -> (1 <= i)%Z -> (1 <= n)%nat -> (A <= nN <= 515)%Z ->
    hpar par nN -> (forall x, 1 <= x <= nN -> zget par x = -1 \/ x < zget par x <= nN)%Z ->
    u8arr s0segs m El (ovb len Jl NL) -> u32arr s0segs m (p + 24) (ovw par Jp 516) -> rw_cells s0segs m (p - 32 + 8) SC -> mem_inv s0segs m ->
    munch [(El + lb, El + lb + A)]%Z me m -> wmono s0segs me m ->
    (forall len' tl' m' (a2 a3 a4 a5 : word),
      (len', tl') = hm_lens n len par lb 17 i tl ->
      u8arr s0segs m' El (ovb len' Jl NL) -> u32arr s0segs m' (p + 24) (ovw par Jp 516) -> rw_cells s0segs m' (p - 32 + 8) SC -> mem_inv s0segs m' ->
      munch [(El + lb, El + lb + A)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RR RA t0 t1 t2 (Z_to_bv 64 (Z.b2z tl')) (Z_to_bv 64 (A + 1)) a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0x2416c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RR RA t0 t1 t2 (Z_to_bv 64 (Z.b2z tl)) (Z_to_bv 64 i) a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0x24100) fc None m (seg_rom s0segs)).
  Proof using XOK.
    induction n as [|n IH]. { intros; lia. }
    intros i len par tl nN me m t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Hi Hi1 Hn HN HP PC LEN PAR SCm MI MU WM K.
    hmenv_open XOK.
    pose proof (ovb_length len Jl NL ltac:(lia)) as LL. pose proof (ovw_length par Jp 516 ltac:(lia)) as LP.
    (* [comment removed for export] *)
    wstep; notrap. wstep. wstep.
    enter_with (S0_hm_depth 600%nat i 0 par nN m); [st_eq| lia| lia| cbn; lia| lia| exact HP| exact PC| exact PAR|].
    intros j x3 x4 Ej Hj.
    (* [comment removed for export] *)
    wstep; flags. wstep. wstep. wstep; flags. wstep; notrap. wstep; notrap. wstep; notrap.
    pose proof (u8arr_store_ok s0segs m El _ (lb + i - 1) _ LEN ltac:(rewrite ovb_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    wstep. store_addr (El + (lb + i - 1))%Z. ovb_store1 LEN (lb + i - 1)%Z.
    replace (wr8 len (lb + i - 1) (bv_unsigned (Z_to_bv 64 j))) with (zset len (lb + i - 1) (j mod 256)) in LEN by (unfold wr8; rewrite unsigned_lit by lia; reflexivity).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    (* [comment removed for export] *)
    assert (TAIL : forall (tl2 : bool) (q2 q3 q4 q5 : word), tl2 = (tl || (17 <? j))%bool ->
      evt s0segs Q (MS (RR RA t0 t1 t2 (Z_to_bv 64 (Z.b2z tl2)) (Z_to_bv 64 i) q2 q3 q4 q5 a6 a7 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x24164) fc None m1 (seg_rom s0segs))).
    { intros tl2 q2 q3 q4 q5 Etl.
      wstep. wstep; if_cases Ke; zify_cond_z Ke.
      - enter_with (IH (i + 1)%Z (zset len (lb + i - 1) (j mod 256)) par tl2 nN me m1); [st_eq| lia| lia| lia| lia| exact HP| exact PC| exact LEN| exact PAR| exact SCm| exact MI| exact MU| exact WM|].
        intros len' tl' m' y2 y3 y4 y5 E. eapply K. rewrite hm_lens_S, <- Ej, <- Etl. exact E.
      - assert (n = 0)%nat by lia. subst n.
        enter_with (K (zset len (lb + i - 1) (j mod 256)) tl2 m1 _ _ _ _); [st_eq| | exact LEN| exact PAR| exact SCm| exact MI| exact MU| exact WM].
        rewrite hm_lens_S. cbn [hm_lens]. rewrite <- Ej, <- Etl. reflexivity. }
    wstep; if_cases Kt; zify_cond_z Kt.
    - enter_with (TAIL tl _ _ _ _); [st_eq|]. replace (17 <? j)%Z with false by (symmetry; apply Z.ltb_ge; lia). rewrite Bool.orb_false_r. reflexivity.
    - wstep. enter_with (TAIL true _ _ _ _); [st_eq|]. replace (17 <? j)%Z with true by (symmetry; apply Z.ltb_lt; lia). rewrite Bool.orb_true_r. reflexivity.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_hm_rescale : forall (n : nat) (i : Z) (w : zarr) (me m : word -> option byte)
      (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    (i + Z.of_nat n = A + 1)%Z -> (1 <= i)%Z -> (1 <= n)%nat ->
    (forall x, i <= x <= A -> zdef w x = true /\ 0 <= zget w x < 2147483648)%Z ->
    u32arr s0segs m (p + 2088) (ovw w Jw 516) -> mem_inv s0segs m ->
    munch [(p + 2088, p + 4152)]%Z me m -> wmono s0segs me m ->
    (forall m' (a0 a1 a2 a3 a4 : word),
      u32arr s0segs m' (p + 2088) (ovw (hm_rescale n w i) Jw 516) -> mem_inv s0segs m' ->
      munch [(p + 2088, p + 4152)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RR RA t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0x23ce4) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RR RA t0 t1 t2 (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 (p + 2088 + 4 * i)) (Z_to_bv 64 (2064 - 4 * i)) a3 a4 a5 a6 a7 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x24184) fc None m (seg_rom s0segs)).
  Proof using XOK.
    induction n as [|n IH]. { intros; lia. }
    intros i w me m t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Hi Hi1 Hn WR WGT MI MU WM K.
    hmenv_open XOK. pose proof (WR i ltac:(lia)) as [Dw Rw].
    pose proof (ovw_length w Jw 516 ltac:(lia)) as LW.
    (* [comment removed for export] *)
    wstep; notrap.
    pose proof (ovw_read s0segs _ (p + 2088) w Jw 516 i _ WGT ltac:(lia) Dw ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. try rewrite (sx32_of_Z (zget w i)) by lia.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep; notrap. wstep. wstep. wstep.
    (* [comment removed for export] *)
    pose proof (u32arr_store_ok s0segs m (p + 2088) _ i _ WGT ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    wstep. store_addr (p + 2088 + 4 * i)%Z.
    ovw_store WGT i (resc (zget w i)) (unfold resc; rewrite shiftl8_mul, shiftr8_div; rewrite unsigned_lit_mod32; f_equal; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    wstep. wstep; if_cases Ke; zify_cond_z Ke.
    - assert (n = 0)%nat by lia. subst n.
      enter_with (K _ _ _ _ _ _); [st_eq| | exact MI| exact MU| exact WM]. rewrite hm_rescale_S. cbn [hm_rescale]. unfold resc in WGT. exact WGT.
    - wstep.
      enter_with (IH (i + 1)%Z (zset w i (resc (zget w i))) me); [st_eq| lia| lia| lia| | exact WGT| exact MI| exact MU| exact WM|].
      + intros x Hx. rewrite zdef_zset, zget_zset. destruct (Z.eqb_spec x i); cbn [orb]; [lia|]. apply WR. lia.
      + intros m' x0 x1 x2 x3 x4. unfold resc. rewrite <- hm_rescale_S. exact (K m' x0 x1 x2 x3 x4).
  Qed.
End S0HM.

End ACeilS1.
