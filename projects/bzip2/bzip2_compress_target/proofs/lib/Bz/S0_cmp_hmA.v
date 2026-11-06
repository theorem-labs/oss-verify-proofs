(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzTac BzTac2 BzArr BzCMem BzCHuff BzArrD CmpMem CmpCut CmpCut0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF1.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFsKit0 CmpHmKit.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.BzCFactsHm OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpFsKit0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit.
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

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_hm_winit : forall (n : nat) (i : Z) (w : zarr) (me m : word -> option byte)
      (ra t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    (i + Z.of_nat n = A)%Z -> (0 <= i)%Z -> (1 <= n)%nat ->
    u32arr s0segs m (p + 2088) (ovw w Jw 516) -> u32arr s0segs m Ef (ovw freq Jf NF) -> mem_inv s0segs m ->
    munch [(p + 2088, p + 4152)]%Z me m -> wmono s0segs me m ->
    (forall m' (a4 : word),
      u32arr s0segs m' (p + 2088) (ovw (hm_winit n w freq fb i) Jw 516) -> u32arr s0segs m' Ef (ovw freq Jf NF) -> mem_inv s0segs m' ->
      munch [(p + 2088, p + 4152)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RW ra t0 t1 t2 (Z_to_bv 64 (Ef + 4 * (fb + A))) (Z_to_bv 64 (p + 2092 + 4 * A)) a4 a5 a6 a7 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x1b6a0) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RW ra t0 t1 t2 (Z_to_bv 64 (Ef + 4 * (fb + i))) (Z_to_bv 64 (p + 2092 + 4 * i)) a4 a5 a6 a7 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x1b67c) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros i w me m ra t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 Hi Hi0 Hn WGT FREQ MI MU WM K.
    hmenv_open XOK. pose proof (FRQ i ltac:(lia)) as [Df Rf].
    pose proof (ovw_length w Jw 516 ltac:(lia)) as LW. pose proof (ovw_length freq Jf NF ltac:(lia)) as LF.
    (* [comment removed for export] *)
    pose proof (ovw_read s0segs _ Ef freq Jf NF (fb + i) _ FREQ ltac:(lia) Df ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. try rewrite (sx32_of_Z (zget freq (fb + i))) by lia.
    (* [comment removed for export] *)
    wstep; if_cases Kz; zify_cond_z Kz.
    - (* [comment removed for export] *)
      wstep.
      (* [comment removed for export] *)
      pose proof (u32arr_store_ok s0segs m (p + 2088) _ (i + 1) _ WGT ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
      wstep. store_addr (p + 2088 + 4 * (i + 1))%Z.
      ovw_store WGT (i + 1)%Z (Z.shiftl (fmax1 (zget freq (fb + i))) 8) (unfold fmax1; replace (zget freq (fb + i) =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia); rewrite shiftl8_mul; wval_lit).
      (* [comment removed for export] *)
      wstep. wstep.
      wstep; if_cases Ke; zify_cond_z Ke.
      + enter_with (IH (i + 1)%Z (zset w (i + 1) (Z.shiftl (fmax1 (zget freq (fb + i))) 8)) me); [st_eq| lia| lia| lia| exact WGT| exact FREQ| exact MI| exact MU| exact WM|].
        intros m' x14. unfold fmax1. rewrite <- hm_winit_S. exact (K m' x14).
      + assert (n = 0)%nat by lia. subst n.
        enter_with (K _ _); [st_eq| | exact FREQ| exact MI| exact MU| exact WM]. rewrite hm_winit_S. cbn [hm_winit]. unfold fmax1 in WGT. exact WGT.
    - (* [comment removed for export] *)
      wstep. wstep.
      pose proof (u32arr_store_ok s0segs m (p + 2088) _ (i + 1) _ WGT ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
      wstep. store_addr (p + 2088 + 4 * (i + 1))%Z.
      ovw_store WGT (i + 1)%Z (Z.shiftl (fmax1 (zget freq (fb + i))) 8) (unfold fmax1; replace (zget freq (fb + i) =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia); wval_lit).
      wstep. wstep.
      wstep; if_cases Ke; zify_cond_z Ke.
      + enter_with (IH (i + 1)%Z (zset w (i + 1) (Z.shiftl (fmax1 (zget freq (fb + i))) 8)) me); [st_eq| lia| lia| lia| exact WGT| exact FREQ| exact MI| exact MU| exact WM|].
        intros m' x14. unfold fmax1. rewrite <- hm_winit_S. exact (K m' x14).
      + assert (n = 0)%nat by lia. subst n.
        enter_with (K _ _); [st_eq| | exact FREQ| exact MI| exact MU| exact WM]. rewrite hm_winit_S. cbn [hm_winit]. unfold fmax1 in WGT. exact WGT.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_hm_fup : forall (f : nat) (zz i : Z) (h w : zarr) (me m : word -> option byte)
      (t0 t1 t2 a5 a7 t3 t4 t5 t6 : word),
    (1 <= zz <= i)%Z -> (i <= A)%Z -> (zz < 2 ^ Z.of_nat f)%Z ->
    (zget w i <? zget w (zget h (Z.shiftr zz 1)))%Z = true ->
    hw h w i A ->
    u32arr s0segs m (p + 4152) (ovw h Jh 260) -> u32arr s0segs m (p + 2088) (ovw w Jw 516) -> mem_inv s0segs m ->
    munch [(p + 4152, p + 5192)]%Z me m -> wmono s0segs me m ->
    (forall h' zz' m' (a2 a3 a6 a7 : word),
      upheap_loop f h w zz i = (h', zz') -> (1 <= zz' <= zz)%Z -> hw h' w i A ->
      u32arr s0segs m' (p + 4152) (ovw h' Jh 260) -> u32arr s0segs m' (p + 2088) (ovw w Jw 516) -> mem_inv s0segs m' ->
      munch [(p + 4152, p + 5192)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RR RA t0 t1 t2 (Z_to_bv 64 i) (Z_to_bv 64 i) a2 a3 (Z_to_bv 64 (zget w i)) (Z_to_bv 64 zz') a6 a7 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x1b790) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RR RA t0 t1 t2 (Z_to_bv 64 i) (Z_to_bv 64 i) (Z_to_bv 64 (zz / 2)) (Z_to_bv 64 (zget h (zz / 2)))
                          (Z_to_bv 64 (zget w i)) a5 (Z_to_bv 64 zz) a7 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x1b75c) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH].
    { intros. cbn in H1. lia. }
    intros zz i h w me m t0 t1 t2 a5 a7 t3 t4 t5 t6 Hzz Hi Hf CT HW HEAP WGT MI MU WM K.
    hmenv_open XOK. cps_destruct HW as (S1 & S2 & HH & WW).
    rewrite shiftr1_div2 in *.
    assert (Hzz2 : (2 <= zz)%Z).
    { destruct (Z_lt_le_dec zz 2); [|assumption]. exfalso. replace (zz / 2)%Z with 0%Z in CT by (Z.div_mod_to_equations; lia).
      rewrite S1, S2 in CT. apply Z.ltb_lt in CT. pose proof (WW i ltac:(lia)). lia. }
    assert (Hz2 : (1 <= zz / 2 < zz)%Z) by (Z.div_mod_to_equations; lia).
    pose proof (HH (zz / 2)%Z ltac:(lia)) as [Dp Rp]. pose proof (WW i ltac:(lia)) as [Dwi Rwi].
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
    assert (HW1 : hw h1 w i A) by (subst h1; apply hw_hset; [exact (conj S1 (conj S2 (conj HH WW)))| lia| lia]).
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
      enter_with (IH (zz / 2)%Z i h1 w me); [st_eq| lia| lia| | | | exact HEAP| exact WGT| exact MI| exact MU| exact WM| ].
      + rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hf by lia. apply Z.div_lt_upper_bound; lia.
      + rewrite shiftr1_div2. apply Z.ltb_lt. exact Kc.
      + split; [exact S1'| split; [exact S2| split; [exact HH1| exact WW]]].
      + intros h' zz' m' a2' a3' a6' a7' E Hzz' HW'. eapply K; [| lia| exact HW'].
        rewrite upheap_loop_S, shiftr1_div2, CT. subst h1. exact E.
    - (* [comment removed for export] *)
      eapply K; [| lia| | exact HEAP| exact WGT| exact MI| exact MU| exact WM].
      + rewrite upheap_loop_S, shiftr1_div2, CT. apply upheap_loop_stop. rewrite shiftr1_div2. apply Z.ltb_ge. subst h1. lia.
      + split; [exact S1'| split; [exact S2| split; [exact HH1| exact WW]]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_hm_fill : forall (n : nat) (i : Z) (h w : zarr) (me m : word -> option byte)
      (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    (i + Z.of_nat n = A + 1)%Z -> (1 <= i)%Z -> (1 <= n)%nat ->
    hw h w (i - 1) A ->
    u32arr s0segs m (p + 4152) (ovw h Jh 260) -> u32arr s0segs m (p + 2088) (ovw w Jw 516) -> mem_inv s0segs m ->
    munch [(p + 4152, p + 5192)]%Z me m -> wmono s0segs me m ->
    (forall h' m' (a2 a3 a4 a5 a6 a7 : word),
      h' = fill_h n h w (i - 1) i -> hw h' w A A ->
      u32arr s0segs m' (p + 4152) (ovw h' Jh 260) -> u32arr s0segs m' (p + 2088) (ovw w Jw 516) -> mem_inv s0segs m' ->
      munch [(p + 4152, p + 5192)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RR RA t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 (A + 1)) a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x1b7a4) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RR RA t0 t1 t2 (Z_to_bv 64 (i - 1)) (Z_to_bv 64 i) a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x1b718) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros i h w me m t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Hi Hi1 Hn HW HEAP WGT MI MU WM K.
    hmenv_open XOK.
    pose proof (ovw_length h Jh 260 ltac:(lia)) as LH. pose proof (ovw_length w Jw 516 ltac:(lia)) as LW.
    assert (Hi2 : (0 <= i / 2 < i)%Z) by (Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep.
    (* [comment removed for export] *)
    pose proof (u32arr_store_ok s0segs m (p + 4152) _ i _ HEAP ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO.
    wstep. ovw_store HEAP i i wval_lit.
    set (h0 := zset h i i) in *.
    assert (HW0 : hw h0 w i A). { subst h0. pose proof (hw_push h w (i - 1) A i HW ltac:(lia) ltac:(lia)) as P. replace (i - 1 + 1)%Z with i in P by lia. exact P. }
    cps_destruct HW0 as (S1 & S2 & HH & WW).
    pose proof (HH (i / 2)%Z ltac:(lia)) as [Dp Rp]. pose proof (WW i ltac:(lia)) as [Dwi Rwi]. pose proof (WW (zget h0 (i / 2)) ltac:(lia)) as [Dwp Rwp].
    (* [comment removed for export] *)
    wstep.
    pose proof (ovw_read s0segs _ (p + 4152) h0 Jh 260 (i / 2) _ HEAP ltac:(lia) Dp ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. try rewrite (sx32_of_Z (zget h0 (i / 2))) by lia.
    (* [comment removed for export] *)
    wstep. wstep.
    pose proof (ovw_read s0segs _ (p + 2088) w Jw 516 i _ WGT ltac:(lia) Dwi ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. try rewrite (sx32_of_Z (zget w i)) by lia.
    (* [comment removed for export] *)
    wstep. wstep.
    pose proof (ovw_read s0segs _ (p + 2088) w Jw 516 (zget h0 (i / 2)) _ WGT ltac:(lia) Dwp ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. try rewrite (sx32_of_Z (zget w (zget h0 (i / 2)))) by lia.
    (* [comment removed for export] *)
    wstep.
    (* [comment removed for export] *)
    assert (TAIL : forall h' zz' m' (x12 x13 x16 x17 : word),
      upheap_loop 20 h0 w i i = (h', zz') -> (1 <= zz' <= i)%Z -> hw h' w i A ->
      u32arr s0segs m' (p + 4152) (ovw h' Jh 260) -> u32arr s0segs m' (p + 2088) (ovw w Jw 516) -> mem_inv s0segs m' ->
      munch [(p + 4152, p + 5192)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RR RA t0 t1 t2 (Z_to_bv 64 i) (Z_to_bv 64 i) x12 x13 (Z_to_bv 64 (zget w i)) (Z_to_bv 64 zz') x16 x17 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x1b790) fc None m' (seg_rom s0segs))).
    { intros h' zz' m' x12 x13 x16 x17 E Hzz' HW' HEAP' WGT' MI' MU' WM'.
      clear HEAP WGT MI MU WM.
      pose proof (ovw_length h' Jh 260 ltac:(lia)) as LH'.
      (* [comment removed for export] *)
      wstep. wstep.
      pose proof (u32arr_store_ok s0segs m' (p + 4152) _ zz' _ HEAP' ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO.
      wstep. ovw_store HEAP' zz' i wval_lit.
      assert (UP : upheap h0 w i = zset h' zz' i).
      { pose proof (upheap_eq h0 w i h' zz') as U. replace (zget h0 i) with i in U by (subst h0; rewrite zget_zset_same; reflexivity). exact (U E). }
      assert (HW'' : hw (zset h' zz' i) w i A) by (apply hw_hset; [exact HW'| lia| lia]).
      (* [comment removed for export] *)
      wstep.
      wstep; if_cases Ke; zify_cond_z Ke.
      - enter_with (IH (i + 1)%Z (zset h' zz' i) w me); [st_eq| lia| lia| lia| | exact HEAP'| exact WGT'| exact MI'| exact MU'| exact WM'|].
        + replace (i + 1 - 1)%Z with i by lia. exact HW''.
        + intros h'' m'' y12 y13 y14 y15 y16 y17 Eh HWf. eapply K; [|exact HWf].
          rewrite fill_h_S. replace (i - 1 + 1)%Z with i by lia. fold h0. rewrite UP. replace (i + 1 - 1)%Z with i in Eh by lia. exact Eh.
      - assert (n = 0)%nat by lia. subst n.
        enter_with (K (zset h' zz' i) _ _ _ _ _ _ _); [st_eq| | | exact HEAP'| exact WGT'| exact MI'| exact MU'| exact WM'].
        + rewrite fill_h_S. cbn [fill_h]. replace (i - 1 + 1)%Z with i by lia. fold h0. rewrite UP. reflexivity.
        + exact (eq_rect _ (fun a => hw (zset h' zz' i) w a A) HW'' _ Ke). }
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      enter_with (TAIL h0 i m0); [st_eq| | lia| | exact HEAP| exact WGT| exact MI| exact MU| exact WM].
      + apply upheap_loop_stop. rewrite shiftr1_div2. apply Z.ltb_ge. lia.
      + exact (conj S1 (conj S2 (conj HH WW))).
    - (* [comment removed for export] *)
      wstep.
      enter_with (S0_hm_fup 20%nat i i h0 w me m0); [st_eq| lia| lia| cbn; lia| | | exact HEAP| exact WGT| exact MI| exact MU| exact WM| exact TAIL].
      + rewrite shiftr1_div2. apply Z.ltb_lt. exact Kc.
      + exact (conj S1 (conj S2 (conj HH WW))).
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
                       F (Z_to_bv 64 0x1ba78) fc None m (seg_rom s0segs))) ->
    evt s0segs Q (MS (RR RA t0 t1 t2 a0 a1 (Z_to_bv 64 (j - 1)) (Z_to_bv 64 k) a4 a5 a6 a7 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x1ba5c) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH]. { intros. cbn in H1. lia. }
    intros k j par nN m t0 t1 t2 a0 a1 a4 a5 a6 a7 t3 t4 t5 t6 Hk HN Hf Hj HP PC PAR K.
    hmenv_open XOK. pose proof (HP k ltac:(lia)) as [Dk Rk].
    pose proof (ovw_length par Jp 516 ltac:(lia)) as LP.
    (* [comment removed for export] *)
    wstep. wstep.
    pose proof (ovw_read s0segs _ (p + 24) par Jp 516 k _ PAR ltac:(lia) Dk ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. try rewrite (sx32_of_Z_signed (zget par k)) by lia.
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    (* [comment removed for export] *)
    wstep; if_cases Kc.
    - (* [comment removed for export] *)
      assert (G : (0 <= zget par k)%Z).
      { apply hm_bvlts0_false; [lia|]. destruct (bv_lts (Z_to_bv 64 (zget par k)) (Z_to_bv 64 0)); [discriminate| reflexivity]. }
      destruct (PC k ltac:(lia)) as [E|R]; [exfalso; lia|].
      enter_with (IH (zget par k) (j + 1)%Z par nN m); [st_eq| lia| lia| lia| lia| exact HP| exact PC| exact PAR|].
      intros j' x13 x14 Ej Hj'. eapply K; [|lia]. rewrite hm_depth_S. replace (0 <=? zget par k)%Z with true by (symmetry; apply Z.leb_le; lia). exact Ej.
    - assert (G : (zget par k < 0)%Z).
      { apply hm_bvlts0_true; [lia|]. destruct (bv_lts (Z_to_bv 64 (zget par k)) (Z_to_bv 64 0)); [reflexivity| discriminate]. }
      enter_with (K j _ _); [st_eq| | lia]. symmetry. apply hm_depth_stop. apply Z.leb_gt. exact G.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_hm_lens : forall (n : nat) (i : Z) (len par : zarr) (tl : bool) (nN : Z) (me m : word -> option byte)
      (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    (i + Z.of_nat n = A + 1)%Z -> (1 <= i)%Z -> (1 <= n)%nat -> (A <= nN <= 515)%Z ->
    hpar par nN -> (forall x, 1 <= x <= nN -> zget par x = -1 \/ x < zget par x <= nN)%Z ->
    u8arr s0segs m El (ovb len Jl NL) -> u32arr s0segs m (p + 24) (ovw par Jp 516) -> mem_inv s0segs m ->
    munch [(El + lb, El + lb + A)]%Z me m -> wmono s0segs me m ->
    (forall len' tl' m' (a2 a3 a4 : word),
      (len', tl') = hm_lens n len par lb 17 i tl ->
      u8arr s0segs m' El (ovb len' Jl NL) -> u32arr s0segs m' (p + 24) (ovw par Jp 516) -> mem_inv s0segs m' ->
      munch [(El + lb, El + lb + A)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RR RA t0 t1 t2 (Z_to_bv 64 (Z.b2z tl')) (Z_to_bv 64 (A + 1)) a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x1ba90) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RR RA t0 t1 t2 (Z_to_bv 64 (Z.b2z tl)) (Z_to_bv 64 i) a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x1ba54) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros i len par tl nN me m t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Hi Hi1 Hn HN HP PC LEN PAR MI MU WM K.
    hmenv_open XOK.
    pose proof (ovb_length len Jl NL ltac:(lia)) as LL. pose proof (ovw_length par Jp 516 ltac:(lia)) as LP.
    (* [comment removed for export] *)
    wstep. wstep.
    enter_with (S0_hm_depth 600%nat i 0 par nN m); [st_eq| lia| lia| cbn; lia| lia| exact HP| exact PC| exact PAR|].
    intros j x13 x14 Ej Hj.
    (* [comment removed for export] *)
    wstep.
    pose proof (u8arr_store_ok s0segs m El _ (lb + i - 1) _ LEN ltac:(rewrite ovb_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    wstep. store_addr (El + (lb + i - 1))%Z. ovb_store1 LEN (lb + i - 1)%Z.
    replace (wr8 len (lb + i - 1) (bv_unsigned (Z_to_bv 64 j))) with (zset len (lb + i - 1) (j mod 256)) in LEN by (unfold wr8; rewrite unsigned_lit by lia; reflexivity).
    (* [comment removed for export] *)
    assert (TAIL : forall tl2 : bool, tl2 = (tl || (17 <? j))%bool ->
      evt s0segs Q (MS (RR RA t0 t1 t2 (Z_to_bv 64 (Z.b2z tl2)) (Z_to_bv 64 i) (Z_to_bv 64 j) (Z_to_bv 64 (El + lb - 1 + i)) x14 a5 a6 a7 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x1ba88) fc None m0 (seg_rom s0segs))).
    { intros tl2 Etl.
      wstep. wstep; if_cases Ke; zify_cond_z Ke.
      - enter_with (IH (i + 1)%Z (zset len (lb + i - 1) (j mod 256)) par tl2 nN me m0); [st_eq| lia| lia| lia| lia| exact HP| exact PC| exact LEN| exact PAR| exact MI| exact MU| exact WM|].
        intros len' tl' m' y12 y13 y14 E. eapply K. rewrite hm_lens_S, <- Ej, <- Etl. exact E.
      - assert (n = 0)%nat by lia. subst n.
        enter_with (K (zset len (lb + i - 1) (j mod 256)) tl2 m0 _ _ _); [st_eq| | exact LEN| exact PAR| exact MI| exact MU| exact WM].
        rewrite hm_lens_S. cbn [hm_lens]. rewrite <- Ej, <- Etl. reflexivity. }
    wstep; if_cases Kt; zify_cond_z Kt.
    - enter_with (TAIL tl); [st_eq|]. replace (17 <? j)%Z with false by (symmetry; apply Z.ltb_ge; lia). rewrite Bool.orb_false_r. reflexivity.
    - wstep. enter_with (TAIL true); [st_eq|]. replace (17 <? j)%Z with true by (symmetry; apply Z.ltb_lt; lia). rewrite Bool.orb_true_r. reflexivity.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_hm_rescale : forall (n : nat) (i : Z) (w : zarr) (me m : word -> option byte)
      (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    (i + Z.of_nat n = A + 1)%Z -> (1 <= i)%Z -> (1 <= n)%nat ->
    (forall x, i <= x <= A -> zdef w x = true /\ 0 <= zget w x < 2147483648)%Z ->
    u32arr s0segs m (p + 2088) (ovw w Jw 516) -> mem_inv s0segs m ->
    munch [(p + 2088, p + 4152)]%Z me m -> wmono s0segs me m ->
    (forall m' (a1 a2 : word),
      u32arr s0segs m' (p + 2088) (ovw (hm_rescale n w i) Jw 516) -> mem_inv s0segs m' ->
      munch [(p + 2088, p + 4152)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RR RA t0 t1 t2 (Z_to_bv 64 (p + 2092 + 4 * A)) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x1bac8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RR RA t0 t1 t2 (Z_to_bv 64 (p + 2092 + 4 * (i - 1))) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x1baa0) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros i w me m t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Hi Hi1 Hn WR WGT MI MU WM K.
    hmenv_open XOK. pose proof (WR i ltac:(lia)) as [Dw Rw].
    pose proof (ovw_length w Jw 516 ltac:(lia)) as LW.
    (* [comment removed for export] *)
    pose proof (ovw_read s0segs _ (p + 2088) w Jw 516 i _ WGT ltac:(lia) Dw ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. try rewrite (sx32_of_Z (zget w i)) by lia.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep.
    (* [comment removed for export] *)
    pose proof (u32arr_store_ok s0segs m (p + 2088) _ i _ WGT ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    wstep. store_addr (p + 2088 + 4 * i)%Z.
    ovw_store WGT i (resc (zget w i)) (unfold resc; rewrite shiftl8_mul, shiftr8_div; rewrite unsigned_lit_mod32; f_equal; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    wstep.
    wstep; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (i + 1)%Z (zset w i (resc (zget w i))) me); [st_eq| lia| lia| lia| | exact WGT| exact MI| exact MU| exact WM|].
      + intros x Hx. rewrite zdef_zset, zget_zset. destruct (Z.eqb_spec x i); cbn [orb]; [lia|]. apply WR. lia.
      + intros m' x11 x12. unfold resc. rewrite <- hm_rescale_S. exact (K m' x11 x12).
    - assert (n = 0)%nat by lia. subst n.
      enter_with (K _ _ _); [st_eq| | exact MI| exact MU| exact WM]. rewrite hm_rescale_S. cbn [hm_rescale]. unfold resc in WGT. exact WGT.
  Qed.
End S0HM.

End ACeilS1.
