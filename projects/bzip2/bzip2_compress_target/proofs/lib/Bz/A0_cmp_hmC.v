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
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.BzCFactsHm OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpFsKit0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanCut A0_cmp_hmV A0_cmp_hmB.
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


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_hm_cpop1 : forall (h w : zarr) (nH nN : Z) (me m : word -> option byte)
      (ra t1 t2 a0 a1 a2 a3 a4 a6 a7 s5 t3 t4 t5 t6 : word),
    (2 <= nH <= 258)%Z -> (0 <= nN <= 515)%Z -> hw h w nH nN ->
    u32arr a0segs m HP (ovw h Jh 260) -> u32arr a0segs m WT (ovw w Jw 516) -> mem_inv a0segs m ->
    munch Wh me m -> wmono a0segs me m ->
    shzW a0segs Wh me HP (HP + 1040) -> shzW a0segs Wh me WT (WT + 2064) ->
    (forall hA zzA m' (t1 t2 a0 a1 a7 t3 t4 : word),
      downheap_loop 20 (zset h 1 (zget h nH)) w (nH - 1) 1 (zget h nH) = (hA, zzA) -> (1 <= zzA <= nH - 1)%Z -> hw hA w (nH - 1) nN ->
      u32arr a0segs m' HP (ovw hA Jh 260) -> u32arr a0segs m' WT (ovw w Jw 516) -> mem_inv a0segs m' ->
      munch Wh me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (RR ra (Z_to_bv 64 zzA) t1 t2 a0 a1 (Z_to_bv 64 (zget h nH)) (Z_to_bv 64 nH) (Z_to_bv 64 nN) (Z_to_bv 64 (nH - 1)) (Z_to_bv 64 (zget h 1)) a7 s5 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x9d78c) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RR ra (Z_to_bv 64 nN) t1 t2 a0 a1 a2 a3 a4 (Z_to_bv 64 nH) a6 a7 s5 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x9d5c0) fc None m (seg_rom a0segs)).
  Proof.
    intros h w nH nN me m ra t1 t2 a0 a1 a2 a3 a4 a6 a7 s5 t3 t4 t5 t6 HnH HnN HW HEAP WGT MI MU WM SHh SHw K.
    hmenv_open XOK. ahenv_open YOK. ahenv_sepx_open YSX. pose proof HW as HW0. cps_destruct HW0 as (S1 & S2 & HH & WW).
    pose proof (ovw_length h Jh 260 ltac:(lia)) as LH. pose proof (ovw_length w Jw 516 ltac:(lia)) as LW.
    pose proof (HH nH ltac:(lia)) as [Dn Rn]. pose proof (HH 1%Z ltac:(lia)) as [D1 R1].
    set (tmp1 := zget h nH) in *. set (n1 := zget h 1) in *.
    pose proof (WW tmp1 ltac:(lia)) as [Dwt Rwt].
    (* [comment removed for export] *)
    arun.
    pose proof (ovw_read a0segs _ HP h Jh 260 1 _ HEAP ltac:(lia) D1 ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. fold n1. try rewrite (sx32_of_Z n1) by lia.
    (* [comment removed for export] *)
    arun.
    pose proof (ovw_read a0segs _ HP h Jh 260 nH _ HEAP ltac:(lia) Dn ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. fold tmp1. try rewrite (sx32_of_Z tmp1) by lia.
    (* [comment removed for export] *)
    pose proof (u32arr_store_ok a0segs m HP _ 1 _ HEAP ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    wstep. store_addr (HP + 4 * 1)%Z. ovw_store HEAP 1%Z tmp1 wval_lit.
    assert (HW1 : hw (zset h 1 tmp1) w (nH - 1) nN).
    { apply (hw_nH_le _ _ nH); [|lia]. apply hw_hset; [exact HW| lia| lia]. }
    (* [comment removed for export] *)
    arun; if_cases Ks; zify_cond_z Ks.
    - (* [comment removed for export] *)
      wstep. wstep.
      enter_with (K (zset h 1 tmp1) 1%Z _ _ _ _ _ _ _ _); [st_eq| | lia| exact HW1| exact HEAP| exact WGT| exact MI| exact MU| exact WM].
      apply downheap_loop_stop1. apply Z.ltb_lt. rewrite shiftl1_mul2. lia.
    - (* [comment removed for export] *)
      arun.
      pose proof (ovw_read a0segs _ WT w Jw 516 tmp1 _ WGT ltac:(lia) Dwt ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget w tmp1)) by lia.
      wstep. wstep.
      enter_with (A0_hm_down1 X Y Q Jh Jw XOK YOK YSX 20%nat 1 (nH - 1) nN n1 tmp1 (zset h 1 tmp1) w me); [st_eq| lia| lia| lia| cbn; lia| lia| lia| exact HW1| exact HEAP| exact WGT| exact MI| exact MU| exact WM| exact SHh| exact SHw|].
      intros hA zzA m' x6 x7 x10 x11 x28 x29 E HzzA HWA HEAP' WGT' MI' MU' WM'.
      enter_with (K hA zzA m' x6 x7 x10 x11 _ x28 x29); [st_eq| exact E| lia| exact HWA| exact HEAP'| exact WGT'| exact MI'| exact MU'| exact WM'].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_hm_cpop2 : forall (hA w : zarr) (zzA tmp1 n1 nH nN : Z) (me m : word -> option byte)
      (ra t1 t2 a0 a1 a7 s5 t3 t4 t5 t6 : word),
    (2 <= nH <= 258)%Z -> (0 <= nN <= 515)%Z -> (1 <= zzA <= nH - 1)%Z -> (0 <= tmp1 <= nN)%Z -> hw hA w (nH - 1) nN ->
    u32arr a0segs m HP (ovw hA Jh 260) -> u32arr a0segs m WT (ovw w Jw 516) -> mem_inv a0segs m ->
    munch Wh me m -> wmono a0segs me m ->
    shzW a0segs Wh me HP (HP + 1040) -> shzW a0segs Wh me WT (WT + 2064) ->
    (forall hB zzB m' (SH7 : Z) (ra t2 a1 a2 s5 t3 t5 t6 : word),
      let hp1 := zset hA zzA tmp1 in
      downheap_loop 20 (zset hp1 1 (zget hp1 (nH - 1))) w (nH - 2) 1 (zget hp1 (nH - 1)) = (hB, zzB) -> (1 <= zzB <= nH - 1)%Z ->
      hw hB w (nH - 2) nN -> saddr (HP + (nH - 1) * 4) SH7 ->
      u32arr a0segs m' HP (ovw hB Jh 260) -> u32arr a0segs m' WT (ovw w Jw 516) -> mem_inv a0segs m' ->
      munch Wh me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (RR ra (Z_to_bv 64 (zget hp1 1)) (Z_to_bv 64 (zget hp1 (nH - 1))) t2 (Z_to_bv 64 (HP + (nH - 1) * 4)) a1 a2 (Z_to_bv 64 nH) (Z_to_bv 64 nN) (Z_to_bv 64 (nH - 1))
                           (Z_to_bv 64 n1) (Z_to_bv 64 SH7) s5 t3 (Z_to_bv 64 zzB) t5 t6)
                       F (Z_to_bv 64 0x9d96c) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RR ra (Z_to_bv 64 zzA) t1 t2 a0 a1 (Z_to_bv 64 tmp1) (Z_to_bv 64 nH) (Z_to_bv 64 nN) (Z_to_bv 64 (nH - 1)) (Z_to_bv 64 n1) a7 s5 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x9d78c) fc None m (seg_rom a0segs)).
  Proof.
    intros hA w zzA tmp1 n1 nH nN me m ra t1 t2 a0 a1 a7 s5 t3 t4 t5 t6 HnH HnN HzzA Htmp HW HEAP WGT MI MU WM SHh SHw K.
    hmenv_open XOK. ahenv_open YOK. ahenv_sepx_open YSX.
    pose proof (ovw_length hA Jh 260 ltac:(lia)) as LH. pose proof (ovw_length w Jw 516 ltac:(lia)) as LW.
    (* [comment removed for export] *)
    arun.
    pose proof (u32arr_store_ok a0segs m HP _ zzA _ HEAP ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    wstep. store_addr (HP + 4 * zzA)%Z. ovw_store HEAP zzA tmp1 wval_lit.
    set (hp1 := zset hA zzA tmp1) in *.
    assert (HW1 : hw hp1 w (nH - 1) nN) by (subst hp1; apply hw_hset; [exact HW| lia| lia]).
    pose proof HW1 as HW0. cps_destruct HW0 as (S1 & S2 & HH & WW).
    pose proof (HH (nH - 1)%Z ltac:(lia)) as [Dn Rn]. pose proof (HH 1%Z ltac:(lia)) as [D1 R1].
    set (tmp2 := zget hp1 (nH - 1)) in *. set (n2 := zget hp1 1) in *.
    pose proof (WW tmp2 ltac:(lia)) as [Dwt Rwt].
    (* [comment removed for export] *)
    arun.
    pose proof (ovw_read a0segs _ HP hp1 Jh 260 1 _ HEAP ltac:(lia) D1 ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. fold n2. try rewrite (sx32_of_Z n2) by lia.
    (* [comment removed for export] *)
    arun.
    pose proof (ovw_read a0segs _ HP hp1 Jh 260 (nH - 1) _ HEAP ltac:(lia) Dn ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. fold tmp2. try rewrite (sx32_of_Z tmp2) by lia.
    (* [comment removed for export] *)
    pose proof (u32arr_store_ok a0segs _ HP _ 1 _ HEAP ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO2.
    wstep. store_addr (HP + 4 * 1)%Z. ovw_store HEAP 1%Z tmp2 wval_lit.
    assert (HW2 : hw (zset hp1 1 tmp2) w (nH - 1) nN) by (apply hw_hset; [exact HW1| lia| lia]).
    (* [comment removed for export] *)
    arun; if_cases Ks; zify_cond_z Ks.
    - (* [comment removed for export] *)
      arun.
      pose proof (ovw_read a0segs _ WT w Jw 516 tmp2 _ WGT ltac:(lia) Dwt ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget w tmp2)) by lia.
      wstep. wstep. wstep.
      enter_with (A0_hm_down2 X Y Q Jh Jw XOK YOK YSX 20%nat 1 (nH - 2) nN n1 n2 tmp2 (zset hp1 1 tmp2) w me); [st_eq| lia| lia| lia| cbn; lia| lia| lia| | exact HEAP| exact WGT| exact MI| exact MU| exact WM| exact SHh| exact SHw|].
      + apply (hw_nH_le _ _ (nH - 1)); [exact HW2| lia].
      + intros hB zzB m' x1 x11 x12 x21 x30 x31 E HzzB HWB HEAP' WGT' MI' MU' WM'.
        enter_with (K hB zzB m' _ x1 _ x11 x12 x21 _ x30 x31); [st_eq| exact E| lia| exact HWB| apply saddr_intro| exact HEAP'| exact WGT'| exact MI'| exact MU'| exact WM'].
    - (* [comment removed for export] *)
      wstep. wstep.
      enter_with (K (zset hp1 1 tmp2) 1%Z _ _ _ _ _ _ _ _ _ _); [st_eq| | lia| apply (hw_nH_le _ _ (nH - 1)); [exact HW2| lia]| apply saddr_intro| exact HEAP| exact WGT| exact MI| exact MU| exact WM].
      apply downheap_loop_stop1. apply Z.ltb_lt. rewrite shiftl1_mul2. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_hm_cnode : forall (hB w par : zarr) (zzB tmp2 n1 n2 nH nN SH7 : Z) (me m : word -> option byte)
      (ra t2 a1 a2 s5 t3 t5 t6 : word),
    (2 <= nH <= 258)%Z -> (0 <= nN)%Z -> (nN + 1 <= 515)%Z -> (1 <= zzB <= nH - 1)%Z -> (0 <= tmp2 <= nN)%Z -> (0 <= n1 <= nN)%Z -> (0 <= n2 <= nN)%Z ->
    hw hB w (nH - 2) nN -> hpar par nN -> (weightof (zget w n1) + weightof (zget w n2) <= 2147483136)%Z ->
    saddr (HP + (nH - 1) * 4) SH7 ->
    u32arr a0segs m HP (ovw hB Jh 260) -> u32arr a0segs m WT (ovw w Jw 516) -> u32arr a0segs m PR (ovw par Jp 516) ->
    mem_inv a0segs m -> munch [(HP, HP + 1040); (WT, WT + 2064); (PR, PR + 2064)]%Z me m -> wmono a0segs me m ->
    shzW a0segs [(HP, HP + 1040); (WT, WT + 2064); (PR, PR + 2064)]%Z me HP (HP + 1040) ->
    shzW a0segs [(HP, HP + 1040); (WT, WT + 2064); (PR, PR + 2064)]%Z me WT (WT + 2064) ->
    shzW a0segs [(HP, HP + 1040); (WT, WT + 2064); (PR, PR + 2064)]%Z me PR (PR + 2064) ->
    (forall hC zzC m' (ra t1 t2 a0 a1 a2 a6 a7 s5 t3 : word),
      let aw := addweights (zget w n1) (zget w n2) in
      let w' := zset w (nN + 1) aw in
      let par' := zset (zset (zset par n2 (nN + 1)) n1 (nN + 1)) (nN + 1) (-1) in
      let h3 := zset (zset hB zzB tmp2) (nH - 1) (nN + 1) in
      upheap_loop 20 h3 w' (nH - 1) (nN + 1) = (hC, zzC) ->
      hw (zset hC zzC (nN + 1)) w' (nH - 1) (nN + 1) -> hpar par' (nN + 1) ->
      u32arr a0segs m' HP (ovw (zset hC zzC (nN + 1)) Jh 260) -> u32arr a0segs m' WT (ovw w' Jw 516) -> u32arr a0segs m' PR (ovw par' Jp 516) ->
      mem_inv a0segs m' -> munch [(HP, HP + 1040); (WT, WT + 2064); (PR, PR + 2064)]%Z me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (RR ra (Z_to_bv 64 (nN + 1)) t1 t2 a0 a1 a2 (Z_to_bv 64 nH) (Z_to_bv 64 nN) (Z_to_bv 64 (nH - 1)) a6 a7 s5 t3 (Z_to_bv 64 zzB) t5 t6)
                       F (Z_to_bv 64 0x9db54) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RR ra (Z_to_bv 64 n2) (Z_to_bv 64 tmp2) t2 (Z_to_bv 64 (HP + (nH - 1) * 4)) a1 a2 (Z_to_bv 64 nH) (Z_to_bv 64 nN) (Z_to_bv 64 (nH - 1))
                         (Z_to_bv 64 n1) (Z_to_bv 64 SH7) s5 t3 (Z_to_bv 64 zzB) t5 t6)
                     F (Z_to_bv 64 0x9d96c) fc None m (seg_rom a0segs)).
  Proof.
    intros hB w par zzB tmp2 n1 n2 nH nN SH7 me m ra t2 a1 a2 s5 t3 t5 t6 HnH HnN HnN' HzzB Htmp Hn1 Hn2 HW HPa RF SA7 HEAP WGT PAR MI MU WM SHh SHw SHp K.
    hmenv_open XOK. ahenv_open YOK. ahenv_sepx_open YSX. pose proof HW as HW0. cps_destruct HW0 as (S1 & S2 & HH & WW).
    pose proof (ovw_length hB Jh 260 ltac:(lia)) as LH. pose proof (ovw_length w Jw 516 ltac:(lia)) as LW. pose proof (ovw_length par Jp 516 ltac:(lia)) as LP.
    pose proof (WW n1 ltac:(lia)) as [Dw1 Rw1]. pose proof (WW n2 ltac:(lia)) as [Dw2 Rw2].
    (* [comment removed for export] *)
    arun.
    pose proof (u32arr_store_ok a0segs m HP _ zzB _ HEAP ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    wstep. store_addr (HP + 4 * zzB)%Z. ovw_store HEAP zzB tmp2 wval_lit.
    set (hp2 := zset hB zzB tmp2) in *.
    (* [comment removed for export] *)
    arun.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok a0segs mm PR _ n2 _ PAR ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO2 end.
    wstep. store_addr (PR + 4 * n2)%Z. ovw_store PAR n2 (nN + 1)%Z wval_lit.
    (* [comment removed for export] *)
    arun.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok a0segs mm PR _ n1 _ PAR ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO3 end.
    wstep. store_addr (PR + 4 * n1)%Z. ovw_store PAR n1 (nN + 1)%Z wval_lit.
    (* [comment removed for export] *)
    arun.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (ovw_read a0segs mm WT w Jw 516 n1 _ WGT ltac:(lia) Dw1 ltac:(unfold wa; f_equal; lia)) as RD end.
    wstep. clear RD. try rewrite (sx32_of_Z (zget w n1)) by lia.
    (* [comment removed for export] *)
    arun.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (ovw_read a0segs mm WT w Jw 516 n2 _ WGT ltac:(lia) Dw2 ltac:(unfold wa; f_equal; lia)) as RD end.
    wstep. clear RD. try rewrite (sx32_of_Z (zget w n2)) by lia.
    (* [comment removed for export] *)
    wstep. wstep.
    pose proof (depthof_range (zget w n1)) as Dr1. pose proof (depthof_range (zget w n2)) as Dr2.
    change (Z.land (zget w n1) 255) with (depthof (zget w n1)). change (Z.land (zget w n2) 255) with (depthof (zget w n2)).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mt end.
    (* [comment removed for export] *)
    assert (TAIL : forall dm, dm = Z.max (depthof (zget w n1)) (depthof (zget w n2)) ->
      evt a0segs Q (MS (RR ra (Z_to_bv 64 (nN + 1)) (Z_to_bv 64 dm) t2 (Z_to_bv 64 (HP + (nH - 1) * 4)) (Z_to_bv 64 (depthof (zget w n2))) (Z_to_bv 64 (zget w n2))
                           (Z_to_bv 64 nH) (Z_to_bv 64 nN) (Z_to_bv 64 (nH - 1)) (Z_to_bv 64 (zget w n1)) (Z_to_bv 64 SH7) s5 t3 (Z_to_bv 64 zzB) t5 t6)
                       F (Z_to_bv 64 0x9da04) fc None mt (seg_rom a0segs))).
    { intros dm Edm.
      (* [comment removed for export] *)
      arun.
      rewrite (addweights_compiled (zget w n1) (zget w n2) dm) by lia.
      set (aw := addweights (zget w n1) (zget w n2)) in *.
      assert (AWR : (0 <= aw < 2147483648)%Z) by (subst aw; apply addweights_range; lia).
      (* [comment removed for export] *)
      pose proof (u32arr_store_ok a0segs mt WT _ (nN + 1) _ WGT ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO5.
      wstep. store_addr (WT + 4 * (nN + 1))%Z. ovw_store WGT (nN + 1)%Z aw wval_lit.
      set (w' := zset w (nN + 1) aw) in *.
      (* [comment removed for export] *)
      arun.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u32arr_store_ok a0segs mm PR _ (nN + 1) _ PAR ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO6 end.
      wstep. store_addr (PR + 4 * (nN + 1))%Z. ovw_store PAR (nN + 1)%Z (-1)%Z (rewrite unsigned_lit_mod32; reflexivity).
      assert (HP' : hpar (zset (zset (zset par n2 (nN + 1)) n1 (nN + 1)) (nN + 1) (-1)) (nN + 1)).
      { apply hpar_node; [exact HPa| lia| lia]. }
      (* [comment removed for export] *)
      arun.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u32arr_store_ok a0segs mm HP _ (nH - 1) _ HEAP ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO4 end.
      wstep. store_addr (HP + 4 * (nH - 1))%Z. ovw_store HEAP (nH - 1)%Z (nN + 1)%Z wval_lit.
      set (h3 := zset hp2 (nH - 1) (nN + 1)) in *.
      assert (HW3 : hw h3 w' (nH - 1) (nN + 1)).
      { subst h3 w'. replace (nH - 1)%Z with (nH - 2 + 1)%Z by lia. apply hw_push; [|lia| lia]. apply hw_node; [|lia| exact AWR].
        subst hp2. apply hw_hset; [|lia| lia]. cps_destruct HW as (T1 & T2 & HHB & WWB). split; [exact T1|]. split; [exact T2|]. split; [exact HHB|].
        intros x Hx. destruct (WWB x ltac:(lia)). split; [assumption| lia]. }
      pose proof HW3 as HW3'. cps_destruct HW3' as (_ & _ & HH3 & WW3).
      assert (Hq : (0 <= (nH - 1) / 2 < nH - 1)%Z) by (Z.div_mod_to_equations; lia).
      pose proof (HH3 ((nH - 1) / 2)%Z ltac:(lia)) as [Dq Rq].
      pose proof (WW3 (zget h3 ((nH - 1) / 2)) ltac:(lia)) as [Dw3 Rw3].
      (* [comment removed for export] *)
      arun.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (ovw_read a0segs mm HP h3 Jh 260 ((nH - 1) / 2) _ HEAP ltac:(lia) Dq ltac:(unfold wa; f_equal; lia)) as RD end.
      wstep. clear RD. try rewrite (sx32_of_Z (zget h3 ((nH - 1) / 2))) by lia.
      (* [comment removed for export] *)
      arun.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (ovw_read a0segs mm WT w' Jw 516 (zget h3 ((nH - 1) / 2)) _ WGT ltac:(lia) Dw3 ltac:(unfold wa; f_equal; lia)) as RD end.
      wstep. clear RD. try rewrite (sx32_of_Z (zget w' (zget h3 ((nH - 1) / 2)))) by lia.
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mq end.
      assert (FIN : forall hC zzC m' (x6 x7 x10 x11 x12 x28 : word),
        upheap_loop 20 h3 w' (nH - 1) (nN + 1) = (hC, zzC) -> (1 <= zzC <= nH - 1)%Z -> hw hC w' (nH - 1) (nN + 1) ->
        u32arr a0segs m' HP (ovw hC Jh 260) -> u32arr a0segs m' WT (ovw w' Jw 516) -> mem_inv a0segs m' ->
        munch Wh mq m' -> wmono a0segs mq m' ->
        evt a0segs Q (MS (RR ra (Z_to_bv 64 (nN + 1)) x6 x7 x10 x11 x12 (Z_to_bv 64 nH) (Z_to_bv 64 nN) (Z_to_bv 64 (nH - 1)) (Z_to_bv 64 aw) (Z_to_bv 64 zzC) s5 x28 (Z_to_bv 64 zzB) t5 t6)
                         F (Z_to_bv 64 0x9db38) fc None m' (seg_rom a0segs))).
      { intros hC zzC m' x6 x7 x10 x11 x12 x28 E HzzC HWC HEAP' WGT' MI' MU' WM'.
        clear HEAP WGT. transport_after_call a0segs mq m' MU' WM'.
        pose proof (ovw_length hC Jh 260 ltac:(lia)) as LHC.
        (* [comment removed for export] *)
        arun.
        pose proof (u32arr_store_ok a0segs m' HP _ zzC _ HEAP' ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO7.
        wstep. store_addr (HP + 4 * zzC)%Z. ovw_store HEAP' zzC (nN + 1)%Z wval_lit.
        enter_with (K hC zzC _ _ _ _ _ _ _ _ _ _ _); [st_eq| exact E| apply hw_hset; [exact HWC| lia| lia]| exact HP'| exact HEAP'| exact WGT'| exact PAR| exact MI'| exact MU| exact WM]. }
      (* [comment removed for export] *)
      wstep; if_cases Kc; zify_cond_z Kc.
      - (* [comment removed for export] *)
        wstep. enter_with (FIN h3 (nH - 1)%Z _ _ _ _ _ _ _); [st_eq| | lia| exact HW3| exact HEAP| exact WGT| exact MI| apply munch_refl| apply wmono_refl].
        apply upheap_loop_stop. rewrite shiftr1_div2. apply Z.ltb_ge. subst w'. rewrite zget_zset_same. lia.
      - (* [comment removed for export] *)
        wstep.
        enter_with (A0_hm_up2 X Y Q Jh Jw XOK YOK YSX 20%nat (nH - 1) (nH - 1) (nN + 1) h3 w' mq mq);
          [st_eq| lia| lia| cbn; lia| lia| | exact HW3| exact HEAP| exact WGT| exact MI| apply munch_refl| apply wmono_refl| | |].
        + subst w'. cbv delta [mkR]. rewrite zget_zset_same. reflexivity.
        + rewrite shiftr1_div2. subst w'. rewrite zget_zset_same. apply Z.ltb_lt. lia.
        + eapply (shzW_sub a0segs _ Wh me mq); [exact SHh| exact MU| a_sub_fp| lia| lia].
        + eapply (shzW_sub a0segs _ Wh me mq); [exact SHw| exact MU| a_sub_fp| lia| lia].
        + intros hC zzC m' x6 x10 x11 x12 E HzzC HWC HEAP' WGT' MI' MU' WM'. subst w'. rewrite zget_zset_same.
          enter_with (FIN hC zzC m' x6 _ x10 x11 x12 _); [st_eq| exact E| exact HzzC| exact HWC| exact HEAP'| exact WGT'| exact MI'| exact MU'| exact WM']. }
    (* [comment removed for export] *)
    wstep; if_cases Kd; zify_cond_z Kd.
    - enter_with (TAIL (depthof (zget w n1))); [st_eq| symmetry; apply Z.max_l; lia].
    - wstep. enter_with (TAIL (depthof (zget w n2))); [st_eq| symmetry; apply Z.max_r; lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation W3 := [(HP, HP + 1040); (WT, WT + 2064); (PR, PR + 2064)]%Z.
  Lemma A0_hm_combine : forall (n : nat) (h w par : zarr) (nH nN : Z) (me m : word -> option byte)
      (ra t1 t2 a0 a1 a2 a3 a4 a6 a7 s5 t3 t4 t5 t6 : word),
    let s := HMS h w par nH nN in
    (nH = Z.of_nat n + 1)%Z -> (1 <= n)%nat -> (nH <= A)%Z -> (A <= nN)%Z -> (nN + Z.of_nat n <= 515)%Z ->
    hw h w nH nN -> hpar par nN ->
    (forall j, (j < n)%nat -> rf_cb (Nat.iter j hm_combine_iter s)) ->
    u32arr a0segs m HP (ovw h Jh 260) -> u32arr a0segs m WT (ovw w Jw 516) -> u32arr a0segs m PR (ovw par Jp 516) ->
    mem_inv a0segs m -> munch W3 me m -> wmono a0segs me m ->
    shzW a0segs W3 me HP (HP + 1040) -> shzW a0segs W3 me WT (WT + 2064) -> shzW a0segs W3 me PR (PR + 2064) ->
    (forall h' w' par' nN' m' (ra t1 t2 a0 a1 a2 a6 a7 s5 t3 t4 t5 t6 : word),
      Nat.iter n hm_combine_iter s = HMS h' w' par' 1 nN' -> (nN' = nN + Z.of_nat n)%Z ->
      hw h' w' 1 nN' -> hpar par' nN' ->
      u32arr a0segs m' HP (ovw h' Jh 260) -> u32arr a0segs m' WT (ovw w' Jw 516) -> u32arr a0segs m' PR (ovw par' Jp 516) ->
      mem_inv a0segs m' -> munch W3 me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (RR ra (Z_to_bv 64 nN') t1 t2 a0 a1 a2 (Z_to_bv 64 2) (Z_to_bv 64 (nN' - 1)) (Z_to_bv 64 1) a6 a7 s5 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x9dc5c) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RR ra (Z_to_bv 64 nN) t1 t2 a0 a1 a2 a3 a4 (Z_to_bv 64 nH) a6 a7 s5 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x9d5c0) fc None m (seg_rom a0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros h w par nH nN me m ra t1 t2 a0 a1 a2 a3 a4 a6 a7 s5 t3 t4 t5 t6 s HnH Hn HA HAN HN HW HPa FACTS HEAP WGT PAR MI MU WM SHh SHw SHp K. subst s.
    hmenv_open XOK. ahenv_open YOK. ahenv_sepx_open YSX.
    pose proof HW as HW0. cps_destruct HW0 as (S1 & S2 & HH & WW).
    pose proof (HH nH ltac:(lia)) as [_ Rt1]. pose proof (HH 1%Z ltac:(lia)) as [_ Rn1].
    eapply (A0_hm_cpop1 h w nH nN m m); [lia| lia| exact HW| exact HEAP| exact WGT| exact MI| apply munch_refl| apply wmono_refl| | |].
    { eapply (shzW_sub a0segs _ Wh me m); [exact SHh| exact MU| a_sub_fp| lia| lia]. }
    { eapply (shzW_sub a0segs _ Wh me m); [exact SHw| exact MU| a_sub_fp| lia| lia]. }
    intros hA zzA m1 x6 x7 x10 x11 x17 x28 x29 E1 HzzA HWA HEAP1 WGT1 MI1 MU1 WM1.
    clear HEAP WGT MI. transport_after_call a0segs m m1 MU1 WM1.
    pose proof HWA as HW0. cps_destruct HW0 as (_ & _ & HHA & _).
    eapply (A0_hm_cpop2 hA w zzA (zget h nH) (zget h 1) nH nN m1 m1); [lia| lia| lia| lia| exact HWA| exact HEAP1| exact WGT1| exact MI1| apply munch_refl| apply wmono_refl| | |].
    { eapply (shzW_sub a0segs _ Wh me m1); [exact SHh| exact MU| a_sub_fp| lia| lia]. }
    { eapply (shzW_sub a0segs _ Wh me m1); [exact SHw| exact MU| a_sub_fp| lia| lia]. }
    intros hB zzB m2 SH7 y1 y7 y11 y12 y21 y28 y30 y31. cbv zeta. intros E2 HzzB HWB SA7 HEAP2 WGT2 MI2 MU2 WM2.
    clear HEAP1 WGT1 MI1 MU1 WM1. transport_after_call a0segs m1 m2 MU2 WM2.
    set (hp1 := zset hA zzA (zget h nH)) in *.
    assert (HW1 : hw hp1 w (nH - 1) nN) by (subst hp1; apply hw_hset; [exact HWA| lia| lia]).
    cps_destruct HW1 as (_ & _ & HH1 & _). pose proof (HH1 (nH - 1)%Z ltac:(lia)) as [_ Rt2]. pose proof (HH1 1%Z ltac:(lia)) as [_ Rn2].
    cps_destruct (combine_iter_link1 h w par nH nN hA zzA E1) as (_ & N1 & N2 & EW & EP). cbv zeta in N1, N2, EW, EP. fold hp1 in N2, EW, EP.
    pose proof (FACTS 0%nat ltac:(lia)) as RF0. cbn [Nat.iter nat_rect] in RF0. unfold rf_cb in RF0. rewrite N1, N2 in RF0. cbn [hm_weight] in RF0.
    eapply (A0_hm_cnode hB w par zzB (zget hp1 (nH - 1)) (zget h 1) (zget hp1 1) nH nN SH7 me m2);
      [lia| lia| lia| lia| lia| lia| lia| exact HWB| exact HPa| exact RF0| exact SA7| exact HEAP2| exact WGT2| exact PAR| exact MI2| exact MU| exact WM| exact SHh| exact SHw| exact SHp|].
    intros hC zzC m3 z1 z6 z7 z10 z11 z12 z16 z17 z21 z28. cbv zeta. intros E3 HWC HPC HEAP3 WGT3 PAR3 MI3 MU3 WM3.
    clear HEAP2 WGT2 PAR MI2 MU2 WM2 MU WM.
    pose proof (combine_iter_link h w par nH nN hA zzA hB zzB hC zzC E1 E2 E3) as IT. cbv zeta in IT.
    rewrite <- EW in HWC, WGT3. rewrite <- EP in HPC, PAR3.
    (* [comment removed for export] *)
    wstep; if_cases Kl; zify_cond_z Kl.
    - enter_with (IH (zset hC zzC (nN + 1)) (cb_w' (HMS h w par nH nN)) (cb_p' (HMS h w par nH nN)) (nH - 1)%Z (nN + 1)%Z me m3);
        [st_eq| lia| lia| lia| lia| lia| exact HWC| exact HPC| | exact HEAP3| exact WGT3| exact PAR3| exact MI3| exact MU3| exact WM3| exact SHh| exact SHw| exact SHp|].
      + intros j Hj. rewrite <- IT, <- iter_S_r. apply FACTS. lia.
      + intros h' w' par' nN' m' q1 q6 q7 q10 q11 q12 q16 q17 q21 q28 q29 q30 q31 ITn HnN' HW' HP' HE' WG' PA' MI' MU' WM'.
        apply (K h' w' par' nN' m' q1 q6 q7 q10 q11 q12 q16 q17 q21 q28 q29 q30 q31); [rewrite iter_S_r, IT; exact ITn| lia| exact HW'| exact HP'| exact HE'| exact WG'| exact PA'| exact MI'| exact MU'| exact WM'].
    - assert (n = 0)%nat by lia. subst n.
      (* [comment removed for export] *)
      wstep.
      enter_with (K (zset hC zzC (nN + 1)) (cb_w' (HMS h w par nH nN)) (cb_p' (HMS h w par nH nN)) (nN + 1)%Z m3 _ _ _ _ _ _ _ _ _ _ _ _ _);
        [st_eq| | lia| exact (eq_rect _ (fun k => hw (zset hC zzC (nN + 1)) (cb_w' (HMS h w par nH nN)) k (nN + 1)) HWC 1%Z ltac:(lia))| exact HPC| exact HEAP3| exact WGT3| exact PAR3| exact MI3| exact MU3| exact WM3].
      cbn [Nat.iter nat_rect]. rewrite IT. f_equal. lia.
  Qed.
End A0HM.

End ACeilS1.
