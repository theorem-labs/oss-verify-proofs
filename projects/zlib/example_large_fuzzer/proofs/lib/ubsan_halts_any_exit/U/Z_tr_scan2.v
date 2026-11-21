(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_ukit Z_tr_fbpure Z_tr_scan1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees TreeModel FillWinModel ScanModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).


Definition scan_tree_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : dlay) (s : deflate_state) (t : tree_id) (mc lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(lo, bv_unsigned sp); (dl_As L + 212, dl_As L + 2904)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ DST m' L (scan_tree s t mc).

Lemma scan_tree_unfold : forall s t mc f, Z.to_nat (mc + 1) = S f -> (t = TL \/ t = TD) ->
  scan_tree s t mc = scan_tree_loop (S f) (set_bl_tree_fc (set_Len s t (mc + 1) 65535) (ds_bl_tree_fc s)) t mc 0 (-1) (Len s t 0) 0
                       (if Len s t 0 =? 0 then 138 else 7) (if Len s t 0 =? 0 then 3 else 4).
Proof.
  intros s t mc f Ef Ht. unfold scan_tree. rewrite Ef.
  destruct Ht as [-> | ->];
    (change (ds_bl_tree_fc s) with (ds_bl_tree_fc (set_Len s _ (mc + 1) 65535)) at 1 || idtac);
    [ change (ds_bl_tree_fc s) with (ds_bl_tree_fc (set_Len s TL (mc + 1) 65535))
    | change (ds_bl_tree_fc s) with (ds_bl_tree_fc (set_Len s TD (mc + 1) 65535)) ];
    rewrite sbf_self; destruct (_ =? 0); reflexivity.
Qed.

Lemma scan_tree_spec : forall (L : dlay) (s : deflate_state) (t : tree_id) (mc lo : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L s -> mem_inv usegs m ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_SC_STACK -> dlay_below L lo (bv_unsigned sp) ->
  (t = TL \/ t = TD) -> 0 <= mc -> mc + 1 < tsize t ->
  (forall i, 0 <= i < tsize t -> 0 <= arr_get (tree_dl s t) i < 65536) -> (forall i, 0 <= i <= mc -> 0 <= arr_get (tree_dl s t) i <= 15) ->
  a0 = wz (dl_As L) -> a1 = wz (dl_As L + toff t) -> a2 = wz mc ->
  evt usegs (scan_tree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L s t mc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_SCAN_TREE) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ST MI STK LO BEL Ht Rmc RmcN HDL HLEN Ea0 Ea1 Ea2.
  open_DST ST. pose proof LAY as LAY0. lay_open LAY0. pose proof BEL as BEL0. below_open BEL0. pose proof (lo_s _ LAY) as BK. unfold blk_ok in BK.
  destruct (Z.to_nat (mc + 1)) as [|f] eqn:Ef; [lia|].
  destruct Ht as [-> | ->]; cbn [toff tsize tree_dl tree_fc] in *.
  -
    unfold dlt, u16arr in Glt. unfold dbt, u16arr in Gbt.
    eapply evt_mono.
    { eapply (scan_tree_body L (dl_As L + 212) 573 mc (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_bl_tree_dl s) (set_Len s TL (mc + 1) 65535) TL (ds_bl_tree_fc s) lo
                ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
      1:{ exact Glt. } 1:{ exact (ln_ltd _ LENS). } 1:{ exact Gbt. } 1:{ exact (ln_btf _ LENS). } 1:{ exact MI. } 1:{ exact LAY. }
      1:{ exact STK. } 1:{ exact LO. } 1:{ exact BEL. } 1:{ Z.div_mod_to_equations. lia. } 1:{ lia. } 1:{ lia. } 1:{ exact Rmc. } 1:{ exact RmcN. }
      1:{ intros i. reflexivity. } 1:{ exact HDL. } 1:{ exact HLEN. } 1:{ exact Ea0. } 1:{ exact Ea1. } 1:{ exact Ea2. } }
    intros ms' P. unfold scan_tree_body_post in P.
    destruct P as (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & b' & m' & -> & MU & WM & MI' & STK' & ART & ARB & LNB' & ER).
    tr_groups MU WM.
    unfold scan_tree_post. do 16 eexists. split; [reflexivity|].
    split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia|].
    split; [exact WM|]. split; [exact MI'|]. split; [exact STK'|].
    rewrite (scan_tree_unfold s TL mc f Ef ltac:(left; reflexivity)). change (Len s TL 0) with (arr_get (ds_dyn_ltree_dl s) 0). rewrite Ef in ER. rewrite ER.
    constructor; [exact GA| exact GB| exact GC| exact GD| unfold dlt, u16arr; exact ART| exact Gdt| unfold dbt, u16arr; exact ARB| exact Gblc
      | exact Gheap| exact Gdep| exact Gwin| exact Gprev| exact Ghead| exact Gpend| | exact LAY].
    destruct LENS; constructor; cbn -[arr_len Z.add]; rewrite ?arr_len_set; first [assumption| lia].
  -
    unfold ddt, u16arr in Gdt. unfold dbt, u16arr in Gbt.
    eapply evt_mono.
    { eapply (scan_tree_body L (dl_As L + 2504) 61 mc (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_dl s) (set_Len s TD (mc + 1) 65535) TD (ds_bl_tree_fc s) lo
                ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
      1:{ exact Gdt. } 1:{ exact (ln_dtd _ LENS). } 1:{ exact Gbt. } 1:{ exact (ln_btf _ LENS). } 1:{ exact MI. } 1:{ exact LAY. }
      1:{ exact STK. } 1:{ exact LO. } 1:{ exact BEL. } 1:{ Z.div_mod_to_equations. lia. } 1:{ lia. } 1:{ lia. } 1:{ exact Rmc. } 1:{ exact RmcN. }
      1:{ intros i. reflexivity. } 1:{ exact HDL. } 1:{ exact HLEN. } 1:{ exact Ea0. } 1:{ exact Ea1. } 1:{ exact Ea2. } }
    intros ms' P. unfold scan_tree_body_post in P.
    destruct P as (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & b' & m' & -> & MU & WM & MI' & STK' & ART & ARB & LNB' & ER).
    tr_groups MU WM.
    unfold scan_tree_post. do 16 eexists. split; [reflexivity|].
    split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia|].
    split; [exact WM|]. split; [exact MI'|]. split; [exact STK'|].
    rewrite (scan_tree_unfold s TD mc f Ef ltac:(right; reflexivity)). change (Len s TD 0) with (arr_get (ds_dyn_dtree_dl s) 0). rewrite Ef in ER. rewrite ER.
    constructor; [exact GA| exact GB| exact GC| exact GD| exact Glt| unfold ddt, u16arr; exact ART| unfold dbt, u16arr; exact ARB| exact Gblc
      | exact Gheap| exact Gdep| exact Gwin| exact Gprev| exact Ghead| exact Gpend| | exact LAY].
    destruct LENS; constructor; cbn -[arr_len Z.add]; rewrite ?arr_len_set; first [assumption| lia].
Qed.
