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
  (* [comment removed for export] *)
  Notation RWB ra t0 t1 t2 a0 a1 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (he_sp X) (Z_to_bv 64 P) a0 a1 (Z_to_bv 64 1) a3 (Z_to_bv 64 1) a5 a6 a7
         s2 s3 s4 s5 s6 s7 (Z_to_bv 64 WT) s9 (Z_to_bv 64 (Ef + 4 * fb)) cSB t3 t4 t5 t6).
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_hm_winit : forall (n : nat) (i : Z) (w : zarr) (me m : word -> option byte)
      (ra t0 t1 t2 s2 s3 s4 s5 s6 s7 s9 t3 t4 t5 t6 : word),
    (i + Z.of_nat n = A)%Z -> (0 <= i)%Z -> (1 <= n)%nat ->
    u32arr b0segs m WT (ovw w Jw 516) -> u32arr b0segs m Ef (ovw freq Jf NF) -> mem_inv b0segs m ->
    munch [(WT, WT + 2064)]%Z me m -> wmono b0segs me m ->
    shzW b0segs [(WT, WT + 2064)]%Z me WT (WT + 2064) -> shzW b0segs [(WT, WT + 2064)]%Z me Ef (Ef + 4 * NF) ->
    (forall m' (t0 t1 : word),
      u32arr b0segs m' WT (ovw (hm_winit n w freq fb i) Jw 516) -> u32arr b0segs m' Ef (ovw freq Jf NF) -> mem_inv b0segs m' ->
      munch [(WT, WT + 2064)]%Z me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (RWB ra t0 t1 t2 (Z_to_bv 64 (WT + 4 + 4 * A)) (Z_to_bv 64 (Ef + 4 * (fb + A))) (Z_to_bv 64 (WT + 4 + 4 * A)) (Z_to_bv 64 (2060 - 4 * A))
                            (Z_to_bv 64 0) (Z_to_bv 64 (Ef + 4 * (fb + A))) s2 s3 s4 s5 s6 s7 s9 t3 t4 t5 t6)
                       F (Z_to_bv 64 0xa816c) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RWB ra t0 t1 t2 (Z_to_bv 64 (WT + 4 + 4 * i)) (Z_to_bv 64 (Ef + 4 * (fb + i))) (Z_to_bv 64 (WT + 4 + 4 * i)) (Z_to_bv 64 (2060 - 4 * i))
                          (Z_to_bv 64 (A - i)) (Z_to_bv 64 (Ef + 4 * (fb + i))) s2 s3 s4 s5 s6 s7 s9 t3 t4 t5 t6)
                     F (Z_to_bv 64 0xa80d8) fc None m (seg_rom b0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros i w me m ra t0 t1 t2 s2 s3 s4 s5 s6 s7 s9 t3 t4 t5 t6 Hi Hi0 Hn WGT FREQ MI MU WM SHw SHf K.
    hmenv_open XOK. ahenv_open YOK. ahenv_sepx_open YSX. pose proof (FRQ i ltac:(lia)) as [Df Rf].
    pose proof (ovw_length w Jw 516 ltac:(lia)) as LW. pose proof (ovw_length freq Jf NF ltac:(lia)) as LF.
    (* [comment removed for export] *)
    brun.
    pose proof (ovw_read b0segs _ Ef freq Jf NF (fb + i) _ FREQ ltac:(lia) Df ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. try rewrite (zx32_of_Z (zget freq (fb + i))) by lia.
    (* [comment removed for export] *)
    brun.
    pose proof (u32arr_store_ok b0segs m WT _ (i + 1) _ WGT ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    wstep. store_addr (WT + 4 * (i + 1))%Z.
    ovw_store WGT (i + 1)%Z (Z.shiftl (fmax1 (zget freq (fb + i))) 8)
      (unfold fmax1; rewrite shiftl8_mul, unsigned_lit_mod32; destruct (Z.ltb_spec (zget freq (fb + i)) 1); destruct (Z.eqb_spec (zget freq (fb + i)) 0); try lia; cbn [Z.b2z]; rewrite Z.mod_small by lia; f_equal; lia).
    (* [comment removed for export] *)
    brun; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (i + 1)%Z (zset w (i + 1) (Z.shiftl (fmax1 (zget freq (fb + i))) 8)) me); [st_eq| lia| lia| lia| exact WGT| exact FREQ| exact MI| exact MU| exact WM| exact SHw| exact SHf|].
      intros m' x5 x6. unfold fmax1. rewrite <- hm_winit_S. exact (K m' x5 x6).
    - assert (n = 0)%nat by lia. subst n.
      wstep. enter_with (K _ _ _); [st_eq| | exact FREQ| exact MI| exact MU| exact WM]. rewrite hm_winit_S. cbn [hm_winit]. unfold fmax1 in WGT. exact WGT.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_hm_fup : forall (f : nat) (zz i : Z) (h w : zarr) (me m : word -> option byte)
      (ra t0 t1 t2 a0 a4 a6 a7 t3 t4 t5 t6 : word),
    (1 <= zz <= i)%Z -> (i <= A)%Z -> (zz < 2 ^ Z.of_nat f)%Z ->
    hw h w i A ->
    u32arr b0segs m HP (ovw h Jh 260) -> u32arr b0segs m WT (ovw w Jw 516) -> mem_inv b0segs m ->
    munch [(HP, HP + 1040)]%Z me m -> wmono b0segs me m ->
    shzW b0segs [(HP, HP + 1040)]%Z me HP (HP + 1040) -> shzW b0segs [(HP, HP + 1040)]%Z me WT (WT + 2064) ->
    (forall h' zz' m' (a0 a4 a6 a7 : word),
      upheap_loop f h w zz i = (h', zz') -> (1 <= zz' <= zz)%Z -> hw h' w i A ->
      u32arr b0segs m' HP (ovw h' Jh 260) -> u32arr b0segs m' WT (ovw w Jw 516) -> mem_inv b0segs m' ->
      munch [(HP, HP + 1040)]%Z me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (RB ra t0 t1 t2 a0 (Z_to_bv 64 i) (Z_to_bv 64 i) (Z_to_bv 64 (zget w i)) a4 (Z_to_bv 64 zz') a6 a7 t3 t4 t5 t6)
                       F (Z_to_bv 64 0xa82f0) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RB ra t0 t1 t2 a0 (Z_to_bv 64 i) (Z_to_bv 64 i) (Z_to_bv 64 (zget w i)) a4 (Z_to_bv 64 zz) a6 a7 t3 t4 t5 t6)
                     F (Z_to_bv 64 0xa8248) fc None m (seg_rom b0segs)).
  Proof.
    induction f as [|f IH].
    { intros. cbn in H1. lia. }
    intros zz i h w me m ra t0 t1 t2 a0 a4 a6 a7 t3 t4 t5 t6 Hzz Hi Hf HW HEAP WGT MI MU WM SHh SHw K.
    hmenv_open XOK. ahenv_open YOK. ahenv_sepx_open YSX. pose proof HW as HW0. cps_destruct HW0 as (S1 & S2 & HH & WW).
    assert (Hz2 : (0 <= zz / 2 < zz)%Z) by (Z.div_mod_to_equations; lia).
    pose proof (HH (zz / 2)%Z ltac:(lia)) as [Dp Rp]. pose proof (WW i ltac:(lia)) as [Dwi Rwi]. pose proof (WW (zget h (zz / 2)) ltac:(lia)) as [Dwp Rwp].
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
    brun; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      enter_with (K h zz m _ _ _ _); [st_eq| | lia| exact HW| exact HEAP| exact WGT| exact MI| exact MU| exact WM].
      apply upheap_loop_stop. rewrite shiftr1_div2. apply Z.ltb_ge. lia.
    - assert (Hzz2 : (2 <= zz)%Z).
      { destruct (Z_lt_le_dec zz 2); [|assumption]. exfalso. replace (zz / 2)%Z with 0%Z in Kc by (Z.div_mod_to_equations; lia).
        rewrite S1, S2 in Kc. lia. }
      (* [comment removed for export] *)
      brun.
      pose proof (u32arr_store_ok b0segs m HP _ zz _ HEAP ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
      wstep. store_addr (HP + 4 * zz)%Z. ovw_store HEAP zz (zget h (zz / 2))%Z wval_lit.
      assert (HW1 : hw (zset h zz (zget h (zz / 2))) w i A) by (apply hw_hset; [exact HW| lia| lia]).
      (* [comment removed for export] *)
      wstep. wstep.
      enter_with (IH (zz / 2)%Z i (zset h zz (zget h (zz / 2))) w me); [st_eq| lia| lia| | exact HW1| exact HEAP| exact WGT| exact MI| exact MU| exact WM| exact SHh| exact SHw|].
      + rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hf by lia. apply Z.div_lt_upper_bound; lia.
      + intros h' zz' m' a0' a4' a6' a7' E Hzz' HW'. eapply K; [| lia| exact HW'].
        rewrite upheap_loop_S, shiftr1_div2. replace (zget w i <? zget w (zget h (zz / 2)))%Z with true by (symmetry; apply Z.ltb_lt; lia). exact E.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation Wfill := [(PR, PR + 2064); (HP, HP + 1040)]%Z.
  Lemma B0_hm_fill : forall (n : nat) (i : Z) (h w par : zarr) (me m : word -> option byte)
      (ra t0 t1 t2 a0 a2 a4 a5 a6 a7 t3 t4 t5 t6 v136 v144 v160 v168 : word),
    (i + Z.of_nat n = A + 1)%Z -> (1 <= i)%Z -> (1 <= n)%nat ->
    hw h w (i - 1) A ->
    u32arr b0segs m HP (ovw h Jh 260) -> u32arr b0segs m WT (ovw w Jw 516) -> u32arr b0segs m PR (ovw par Jp 516) ->
    rw_cells b0segs m (P + 24) (SLb X Y v136 v144 v160 v168) -> mem_inv b0segs m ->
    munch Wfill me m -> wmono b0segs me m ->
    shzW b0segs Wfill me HP (HP + 1040) -> shzW b0segs Wfill me WT (WT + 2064) ->
    (forall h' m' (a0 a2 a3 a4 a5 a6 a7 : word),
      h' = fill_h n h w (i - 1) i -> hw h' w A A ->
      u32arr b0segs m' HP (ovw h' Jh 260) -> u32arr b0segs m' WT (ovw w Jw 516) -> u32arr b0segs m' PR (ovw (pneg par i n) Jp 516) ->
      rw_cells b0segs m' (P + 24) (SLb X Y v136 v144 v160 v168) -> mem_inv b0segs m' ->
      munch Wfill me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (RB ra t0 t1 t2 a0 (Z_to_bv 64 (A + 1)) a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
                       F (Z_to_bv 64 0xa8348) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RB ra t0 t1 t2 a0 (Z_to_bv 64 i) a2 (Z_to_bv 64 (i - 1)) a4 a5 a6 a7 t3 t4 t5 t6)
                     F (Z_to_bv 64 0xa8200) fc None m (seg_rom b0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros i h w par me m ra t0 t1 t2 a0 a2 a4 a5 a6 a7 t3 t4 t5 t6 v136 v144 v160 v168 Hi Hi1 Hn HW HEAP WGT PAR SLB MI MU WM SHh SHw K.
    hmenv_open XOK. ahenv_open YOK. ahenv_sepx_open YSX. unfold SLb in SLB.
    pose proof (ovw_length h Jh 260 ltac:(lia)) as LH. pose proof (ovw_length w Jw 516 ltac:(lia)) as LW. pose proof (ovw_length par Jp 516 ltac:(lia)) as LP.
    (* [comment removed for export] *)
    brun.
    pose proof (u32arr_store_ok b0segs m PR _ i _ PAR ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    wstep. store_addr (PR + 4 * i)%Z. ovw_store PAR i (-1)%Z (rewrite unsigned_lit_mod32; reflexivity).
    (* [comment removed for export] *)
    brun.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok b0segs mm HP _ i _ HEAP ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO2 end.
    wstep. store_addr (HP + 4 * i)%Z. ovw_store HEAP i i wval_lit.
    set (h0 := zset h i i) in *.
    assert (HW0 : hw h0 w i A). { subst h0. pose proof (hw_push h w (i - 1) A i HW ltac:(lia) ltac:(lia)) as PU. replace (i - 1 + 1)%Z with i in PU by lia. exact PU. }
    pose proof HW0 as HW0'. cps_destruct HW0' as (S1 & S2 & HH & WW). pose proof (WW i ltac:(lia)) as [Dwi Rwi].
    (* [comment removed for export] *)
    brun.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (ovw_read b0segs mm WT w Jw 516 i _ WGT ltac:(lia) Dwi ltac:(unfold wa; f_equal; lia)) as RD end.
    wstep. clear RD. try rewrite (sx32_of_Z (zget w i)) by lia.
    (* [comment removed for export] *)
    wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mq end.
    enter_with (B0_hm_fup 20%nat i i h0 w mq mq);
      [st_eq| lia| lia| cbn; lia| exact HW0| exact HEAP| exact WGT| exact MI| apply munch_refl| apply wmono_refl
      | eapply (shzW_sub b0segs Wfill _ me mq); [exact SHh| exact MU| a_sub_fp| lia| lia]
      | eapply (shzW_sub b0segs Wfill _ me mq); [exact SHw| exact MU| a_sub_fp| lia| lia] |].
    intros h' zz' m' y10 y14 y16 y17 E Hzz' HW' HEAP' WGT' MI' MU' WM'.
    clear HEAP WGT MI. transport_after_call b0segs mq m' MU' WM'.
    pose proof (ovw_length h' Jh 260 ltac:(lia)) as LH'.
    (* [comment removed for export] *)
    brun.
    pose proof (u32arr_store_ok b0segs m' HP _ zz' _ HEAP' ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO3.
    wstep. store_addr (HP + 4 * zz')%Z. ovw_store HEAP' zz' i wval_lit.
    assert (UP : upheap h0 w i = zset h' zz' i).
    { pose proof (upheap_eq h0 w i h' zz') as U. replace (zget h0 i) with i in U by (subst h0; rewrite zget_zset_same; reflexivity). exact (U E). }
    assert (HW'' : hw (zset h' zz' i) w i A) by (apply hw_hset; [exact HW'| lia| lia]).
    (* [comment removed for export] *)
    brun; if_cases Ke; zify_cond_z Ke.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH (i + 1)%Z (zset h' zz' i) w (zset par i (-1)) me mm) end;
        [st_eq| lia| lia| lia| | exact HEAP'| exact WGT'| exact PAR| exact SLB| exact MI'| exact MU| exact WM| exact SHh| exact SHw|].
      + replace (i + 1 - 1)%Z with i by lia. exact HW''.
      + intros h'' m'' z10 z12 z13 z14 z15 z16 z17 Eh HWf. rewrite <- pneg_S. eapply K; [|exact HWf].
        rewrite fill_h_S. replace (i - 1 + 1)%Z with i by lia. fold h0. rewrite UP. replace (i + 1 - 1)%Z with i in Eh by lia. exact Eh.
    - assert (n = 0)%nat by lia. subst n.
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (K (zset h' zz' i) mm _ _ _ _ _ _ _) end; [st_eq| | | exact HEAP'| exact WGT'| | exact SLB| exact MI'| exact MU| exact WM].
      + rewrite fill_h_S. cbn [fill_h]. replace (i - 1 + 1)%Z with i by lia. fold h0. rewrite UP. reflexivity.
      + exact (eq_rect _ (fun a => hw (zset h' zz' i) w a A) HW'' _ Ke).
      + rewrite pneg_S. cbn [pneg]. exact PAR.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_hm_depth : forall (f : nat) (k j : Z) (par : zarr) (nN : Z) (Wl : list (Z * Z)) (me m : word -> option byte)
      (ra t0 t1 t2 a1 a2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    (1 <= k <= nN)%Z -> (nN <= 515)%Z -> (nN - k < Z.of_nat f)%Z -> (0 <= j <= k)%Z ->
    hpar par nN -> (forall x, 1 <= x <= nN -> zget par x = -1 \/ x < zget par x <= nN)%Z ->
    u32arr b0segs m PR (ovw par Jp 516) ->
    munch Wl me m -> shzW b0segs Wl me PR (PR + 2064) ->
    (forall j' (a0 a4 : word), j' = hm_depth f par k j -> (j <= j' <= nN)%Z ->
      evt b0segs Q (MS (RB ra t0 t1 t2 a0 a1 a2 (Z_to_bv 64 j') a4 a5 a6 a7 t3 t4 t5 t6)
                       F (Z_to_bv 64 0xa83c8) fc None m (seg_rom b0segs))) ->
    evt b0segs Q (MS (RB ra t0 t1 t2 (Z_to_bv 64 k) a1 a2 (Z_to_bv 64 j) a4 a5 a6 a7 t3 t4 t5 t6)
                     F (Z_to_bv 64 0xa8378) fc None m (seg_rom b0segs)).
  Proof.
    induction f as [|f IH]. { intros. cbn in H1. lia. }
    intros k j par nN Wl me m ra t0 t1 t2 a1 a2 a4 a5 a6 a7 t3 t4 t5 t6 Hk HN Hf Hj HPp PC PAR MU SHp K.
    hmenv_open XOK. ahenv_open YOK. ahenv_sepx_open YSX. pose proof (HPp k ltac:(lia)) as [Dk Rk].
    pose proof (ovw_length par Jp 516 ltac:(lia)) as LP.
    (* [comment removed for export] *)
    brun.
    pose proof (ovw_read b0segs _ PR par Jp 516 k _ PAR ltac:(lia) Dk ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. try rewrite (sx32_of_Z_signed (zget par k)) by lia.
    (* [comment removed for export] *)
    wstep; if_cases Kc.
    - assert (G : (zget par k < 0)%Z).
      { apply hm_bvlts0_true; [lia|]. destruct (bv_lts (Z_to_bv 64 (zget par k)) (Z_to_bv 64 0)); [reflexivity| discriminate]. }
      enter_with (K j _ _); [st_eq| | lia]. symmetry. apply hm_depth_stop. apply Z.leb_gt. exact G.
    - assert (G : (0 <= zget par k)%Z).
      { apply hm_bvlts0_false; [lia|]. destruct (bv_lts (Z_to_bv 64 (zget par k)) (Z_to_bv 64 0)); [discriminate| reflexivity]. }
      destruct (PC k ltac:(lia)) as [E|R]; [exfalso; lia|].
      (* [comment removed for export] *)
      brun_to 0xa8378%Z.
      enter_with (IH (zget par k) (j + 1)%Z par nN Wl me m); [st_eq| lia| lia| lia| lia| exact HPp| exact PC| exact PAR| exact MU| exact SHp|].
      intros j' x10 x14 Ej Hj'. eapply K; [|lia]. rewrite hm_depth_S. replace (0 <=? zget par k)%Z with true by (symmetry; apply Z.leb_le; lia). exact Ej.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation Wlens := [(El + lb, El + lb + A)]%Z.
  Lemma B0_hm_lens : forall (n : nat) (i : Z) (len par : zarr) (tl : bool) (nN : Z) (me m : word -> option byte)
      (ra t0 t1 t2 a0 a3 a4 a5 a6 a7 t3 t4 t5 t6 v136 v144 v160 v168 : word),
    (i + Z.of_nat n = A + 1)%Z -> (1 <= i)%Z -> (1 <= n)%nat -> (A <= nN <= 515)%Z ->
    hpar par nN -> (forall x, 1 <= x <= nN -> zget par x = -1 \/ x < zget par x <= nN)%Z ->
    u8arr b0segs m El (ovb len Jl NL) -> u32arr b0segs m PR (ovw par Jp 516) -> rw_cells b0segs m (P + 24) (SLb X Y v136 v144 v160 v168) -> mem_inv b0segs m ->
    munch Wlens me m -> wmono b0segs me m ->
    shzW b0segs Wlens me El (El + NL) -> shzW b0segs Wlens me PR (PR + 2064) ->
    (forall len' tl' m' (a0 a3 a4 a5 : word),
      (len', tl') = hm_lens n len par lb 17 i tl ->
      u8arr b0segs m' El (ovb len' Jl NL) -> u32arr b0segs m' PR (ovw par Jp 516) -> rw_cells b0segs m' (P + 24) (SLb X Y v136 v144 v160 v168) -> mem_inv b0segs m' ->
      munch Wlens me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (RB ra t0 t1 t2 a0 (Z_to_bv 64 (Z.b2z tl')) (Z_to_bv 64 (A + 1)) a3 a4 a5 a6 a7 t3 t4 t5 t6)
                       F (Z_to_bv 64 0xa842c) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RB ra t0 t1 t2 a0 (Z_to_bv 64 (Z.b2z tl)) (Z_to_bv 64 i) a3 a4 a5 a6 a7 t3 t4 t5 t6)
                     F (Z_to_bv 64 0xa836c) fc None m (seg_rom b0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros i len par tl nN me m ra t0 t1 t2 a0 a3 a4 a5 a6 a7 t3 t4 t5 t6 v136 v144 v160 v168 Hi Hi1 Hn HN HPp PC LEN PAR SLB MI MU WM SHl SHp K.
    hmenv_open XOK. ahenv_open YOK. ahenv_sepx_open YSX. unfold SLb in SLB.
    pose proof (ovb_length len Jl NL ltac:(lia)) as LL. pose proof (ovw_length par Jp 516 ltac:(lia)) as LP.
    (* [comment removed for export] *)
    brun_to 0xa8378%Z.
    enter_with (B0_hm_depth 600%nat i 0 par nN Wlens me m); [st_eq| lia| lia| cbn; lia| lia| exact HPp| exact PC| exact PAR| exact MU| exact SHp|].
    intros j x10 x14 Ej Hj.
    (* [comment removed for export] *)
    brun.
    pose proof (u8arr_store_ok b0segs m El _ (lb + i - 1) _ LEN ltac:(rewrite ovb_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    wstep. store_addr (El + (lb + i - 1))%Z. ovb_store1 LEN (lb + i - 1)%Z.
    replace (wr8 len (lb + i - 1) (bv_unsigned (Z_to_bv 64 j))) with (zset len (lb + i - 1) (j mod 256)) in LEN by (unfold wr8; rewrite unsigned_lit by lia; reflexivity).
    assert (TAIL : forall (tl2 : bool) (x10 x14 x15 : word), tl2 = (tl || (17 <? j))%bool ->
      evt b0segs Q (MS (RB ra t0 t1 t2 x10 (Z_to_bv 64 (Z.b2z tl2)) (Z_to_bv 64 i) (Z_to_bv 64 j) x14 x15 a6 a7 t3 t4 t5 t6)
                       F (Z_to_bv 64 0xa8410) fc None m0 (seg_rom b0segs))).
    { intros tl2 x10' x14' x15' Etl.
      (* [comment removed for export] *)
      brun; if_cases Ke; zify_cond_z Ke.
      - enter_with (IH (i + 1)%Z (zset len (lb + i - 1) (j mod 256)) par tl2 nN me m0); [st_eq| lia| lia| lia| lia| exact HPp| exact PC| exact LEN| exact PAR| exact SLB| exact MI| exact MU| exact WM| exact SHl| exact SHp|].
        intros len' tl' m' y10 y13 y14 y15 E. eapply K. rewrite hm_lens_S, <- Ej, <- Etl. exact E.
      - assert (n = 0)%nat by lia. subst n.
        wstep.
        enter_with (K (zset len (lb + i - 1) (j mod 256)) tl2 m0 _ _ _ _); [st_eq| | exact LEN| exact PAR| exact SLB| exact MI| exact MU| exact WM].
        rewrite hm_lens_S. cbn [hm_lens]. rewrite <- Ej, <- Etl. reflexivity. }
    (* [comment removed for export] *)
    brun; if_cases Kt; zify_cond_z Kt.
    - enter_with (TAIL tl _ _ _); [st_eq|]. replace (17 <? j)%Z with false by (symmetry; apply Z.ltb_ge; lia). rewrite Bool.orb_false_r. reflexivity.
    - wstep. enter_with (TAIL true _ _ _); [st_eq|]. replace (17 <? j)%Z with true by (symmetry; apply Z.ltb_lt; lia). rewrite Bool.orb_true_r. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_hm_rescale : forall (n : nat) (i : Z) (w : zarr) (me m : word -> option byte)
      (ra t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    (i + Z.of_nat n = A + 1)%Z -> (1 <= i)%Z -> (1 <= n)%nat ->
    (forall x, i <= x <= A -> zdef w x = true /\ 0 <= zget w x < 2147483648)%Z ->
    u32arr b0segs m WT (ovw w Jw 516) -> mem_inv b0segs m ->
    munch [(WT, WT + 2064)]%Z me m -> wmono b0segs me m ->
    shzW b0segs [(WT, WT + 2064)]%Z me WT (WT + 2064) ->
    (forall m' (a4 a5 a6 : word),
      u32arr b0segs m' WT (ovw (hm_rescale n w i) Jw 516) -> mem_inv b0segs m' ->
      munch [(WT, WT + 2064)]%Z me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (RB ra t0 t1 t2 (Z_to_bv 64 (WT + 4 + 4 * A)) (Z_to_bv 64 0) (Z_to_bv 64 (WT + 4 + 4 * A)) (Z_to_bv 64 (2060 - 4 * A)) a4 a5 a6 a7 t3 t4 t5 t6)
                       F (Z_to_bv 64 0xa81e0) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RB ra t0 t1 t2 (Z_to_bv 64 (WT + 4 + 4 * (i - 1))) (Z_to_bv 64 (A - i + 1)) (Z_to_bv 64 (WT + 4 + 4 * (i - 1))) (Z_to_bv 64 (2060 - 4 * (i - 1))) a4 a5 a6 a7 t3 t4 t5 t6)
                     F (Z_to_bv 64 0xa8444) fc None m (seg_rom b0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros i w me m ra t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 Hi Hi1 Hn WR WGT MI MU WM SHw K.
    hmenv_open XOK. ahenv_open YOK. ahenv_sepx_open YSX. pose proof (WR i ltac:(lia)) as [Dw Rw].
    pose proof (ovw_length w Jw 516 ltac:(lia)) as LW.
    (* [comment removed for export] *)
    brun.
    pose proof (ovw_read b0segs _ WT w Jw 516 i _ WGT ltac:(lia) Dw ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. try rewrite (sx32_of_Z (zget w i)) by lia.
    (* [comment removed for export] *)
    brun.
    pose proof (u32arr_store_ok b0segs m WT _ i _ WGT ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    wstep. store_addr (WT + 4 * i)%Z.
    ovw_store WGT i (resc (zget w i)) (unfold resc; rewrite shiftl8_mul, shiftr8_div; rewrite unsigned_lit_mod32; f_equal; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    brun; if_cases Ke; zify_cond_z Ke.
    - assert (n = 0)%nat by lia. subst n.
      enter_with (K _ _ _ _); [st_eq| | exact MI| exact MU| exact WM]. rewrite hm_rescale_S. cbn [hm_rescale]. unfold resc in WGT. exact WGT.
    - wstep.
      enter_with (IH (i + 1)%Z (zset w i (resc (zget w i))) me); [st_eq| lia| lia| lia| | exact WGT| exact MI| exact MU| exact WM| exact SHw|].
      + intros x Hx. rewrite zdef_zset, zget_zset. destruct (Z.eqb_spec x i); cbn [orb]; [lia|]. apply WR. lia.
      + intros m' x14 x15 x16. unfold resc. rewrite <- hm_rescale_S. exact (K m' x14 x15 x16).
  Qed.
End B0HM.

End ACeilS1.
