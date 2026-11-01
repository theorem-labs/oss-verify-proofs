(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Mem Frame Cells Step Exec ImageA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Common Require Import FastWord FastWordSem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Common.Ax Require Import ExTrie.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound HxRunSound HxHook HxHookSound HxToolkit HxGlue HxImg HxQuery HxLearn.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HXS Require Import HxsKit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HXB Require Import HxaImage HxaExitInit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Definition MODULE_DTOR : Z := 0x1ee8d4.
(* [comment removed for export] *)
Definition XD_STACK : Z := 1024.
(* [comment removed for export] *)
Definition XSH_LO : Z := 0x7fffa000.
Definition XSH_HI : Z := 0x80177a00.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition stopX (pc : w64) : bool := w_eqb pc PC_X_RET.
Definition exit_result : icache * rres := hx_run bsegs stopX 21 IEmpty S0X.
Definition exit_end (r : icache * rres) : sstate := res_state (snd r).

Definition final_regsX : list (rix * hval) :=
  [(X1, VP TX_RA w_zero); (X2, VP 1%uint63 (W false XSTK)); (X3, VP TX_GP w_zero); (X4, VC TPVX);
   (X8, VP TX_S0 w_zero); (X9, VP (TX_S0 + 1)%uint63 w_zero); (X18, VP (TX_S0 + 2)%uint63 w_zero); (X19, VP (TX_S0 + 3)%uint63 w_zero);
   (X20, VP (TX_S0 + 4)%uint63 w_zero); (X21, VP (TX_S0 + 5)%uint63 w_zero); (X22, VP (TX_S0 + 6)%uint63 w_zero); (X23, VP (TX_S0 + 7)%uint63 w_zero);
   (X24, VP (TX_S0 + 8)%uint63 w_zero); (X25, VP (TX_S0 + 9)%uint63 w_zero); (X26, VP (TX_S0 + 10)%uint63 w_zero); (X27, VP (TX_S0 + 11)%uint63 w_zero)].

Definition final_regs_okX (S : sstate) : bool := forallb (fun rv => hval_eqb (rget S (fst rv)) (snd rv)) final_regsX.

Definition exit_ok (r : icache * rres) : bool :=
  match snd r with
  | RStop X => w_eqb (s_pc X) PC_X_RET && (match s_resv X with RNone => true | _ => false end) && final_regs_okX X
  | _ => false
  end.

Lemma exit_ok_inv (r : icache * rres) : exit_ok r = true ->
  exists ic S, r = (ic, RStop S) /\ s_pc S = PC_X_RET /\ s_resv S = RNone /\ final_regs_okX S = true.
Proof.
  destruct r as [ic [S|S|c S]]; cbn [exit_ok snd]; try discriminate. intros H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  exists ic, S. split; [reflexivity|]. split; [apply w_eqb_true_iff; exact H1|].
  split; [destruct (s_resv S); [reflexivity | discriminate | discriminate] | exact H3].
Qed.

Lemma exit_result_unfold : exit_result = hx_run bsegs stopX 21 IEmpty S0X.
Proof. exact eq_refl. Qed.

(* [comment removed for export] *)
Lemma exit_checked : exit_ok exit_result = true.
Proof. vm_compute. reflexivity. Qed.

Lemma fetch_finalX : exists ic', hx_fetch bsegs IEmpty PC_X_RET = Some (DJalr X0 X1 w_zero, ic').
Proof.
  assert (Hdecoded : option_map fst (hx_fetch bsegs IEmpty PC_X_RET) = Some (DJalr X0 X1 w_zero))
    by (vm_compute; reflexivity).
  revert Hdecoded.
  destruct (hx_fetch bsegs IEmpty PC_X_RET) as [[dec ic_after]|]; cbn [option_map fst]; intros Hdecoded.
  - injection Hdecoded as Hdec_eq. exists ic_after. rewrite Hdec_eq. exact eq_refl.
  - discriminate Hdecoded.
Qed.

(* [comment removed for export] *)
Definition wr_bX (k : Z) (rg : region) : bool :=
  (k <? 39) &&
  (negb (rg_wr rg)
   || match rg_abs rg with
      | Some a => existsb (fun iv => (fst iv =? to_Z a) && (snd iv =? to_Z a + to_Z (rg_size rg))) WX
      | None => (k =? 1) && (to_Z (rg_size rg) =? 1024)
      end).

Lemma MX_checked : mem_check wr_bX MX = true.
Proof. vm_compute. reflexivity. Qed.

Lemma MX_get1 : mget MX 1%uint63 = Some xg_1.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac closed_side := first [ vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity | vm_compute; discriminate ].

(* [comment removed for export] *)
Local Ltac img_region slot seg Hchunk Hreadable Hfind Hview :=
  lazymatch goal with
  | |- region_ok bsegs _ _ ?reg _ => let layout := eval hnf in reg in change reg with layout
  end;
  apply (img_region_ok_view bsegs _ _ _ _ _ _ slot _ _ seg (chunk_of seg));
  [ exact eq_refl | exact Hchunk | exact Hreadable | closed_side | closed_side
  | let a := fresh "a" in let Hspan := fresh "Hspan" in
    intros a Hspan; cbv -[Z.le Z.lt] in Hspan; apply Hfind; lia
  | closed_side | closed_side | closed_side
  | let a := fresh "a" in let Hspan := fresh "Hspan" in
    intros a Hspan; cbv -[Z.le Z.lt] in Hspan; apply Hview; lia
  | closed_side .. ].

Section Handoff.
Variables (rho : valuation) (m : word -> option byte).
Hypothesis MI : mem_inv bsegs m.
(* [comment removed for export] *)
Hypothesis V_relro : forall a, 5681152 <= a < 6172672 -> mrd bsegs m (wa a) = seg_rom bsegs (wa a).
Hypothesis V_gdesc : forall a, 6190176 <= a < 6947616 -> mrd bsegs m (wa a) = seg_rom bsegs (wa a).
(* [comment removed for export] *)
Hypothesis C_memset : ro_cells bsegs m 6176536 [C8 (Z_to_bv 64 0x5634a4)].
Hypothesis C_flag : rw_cells bsegs m 6947648 [C8 (Z_to_bv 64 1)].
Hypothesis C_f1 : ro_cells bsegs m 6951440 [C4 (Z_to_bv 64 1)].
Hypothesis C_mu : rw_cells bsegs m 6951600 [C8 (Z_to_bv 64 0)].
Hypothesis C_f2 : ro_cells bsegs m 6959708 [C1 (Z_to_bv 8 1)].
Hypothesis C_shb : ro_cells bsegs m 6961656 [C8 (Z_to_bv 64 0x7fff8000)].
Hypothesis C_f3 : ro_cells bsegs m 6964952 [C1 (Z_to_bv 8 1)].
Hypothesis C_w : ro_cells bsegs m 7558560 [C8 (Z_to_bv 64 0xffffffffffffffff)].
Hypothesis W_odr0 : stk bsegs m 12413536 12413544.
Hypothesis W_odr1 : stk bsegs m 12413920 12413928.
Hypothesis W_odr2 : stk bsegs m 12420128 12420184.
Hypothesis W_odr3 : stk bsegs m 12420224 12420304.
Hypothesis W_odr4 : stk bsegs m 12420384 12420424.
Hypothesis W_odr5 : stk bsegs m 12420480 12420528.
Hypothesis W_odr6 : stk bsegs m 12420864 12420904.
Hypothesis W_odr7 : stk bsegs m 12420992 12421000.
Hypothesis W_odr8 : stk bsegs m 12427808 12427840.
Hypothesis W_odr9 : stk bsegs m 12427872 12427896.
Hypothesis W_odr10 : stk bsegs m 12428000 12428504.
Hypothesis W_img_shadow : stk bsegs m 2147459072 2149022208.

(* [comment removed for export] *)
Local Ltac lit_cells tag reg lo cs Hcells :=
  let Hkb_self := fresh "Hkb_self" in
  assert (Hkb_self : forall bs : list byte, Forall2 (kb_ok rho) (map (fun b => KB (bv_unsigned b)) bs) bs)
    by (intros bs; induction bs as [|b_hd b_tl IH_tl]; [constructor | constructor; [exact eq_refl | exact IH_tl]]);
  apply (literal_region_ok bsegs rho tag reg m lo (map (fun b => KB (bv_unsigned b)) (cells_bytes cs)) (cells_bytes cs));
  [ closed_side | closed_side | apply Hkb_self
  | lazymatch type of Hcells with
    | ro_cells _ _ _ _ => exact (proj2 Hcells)
    | rw_cells _ _ _ _ => exact (proj2 (proj1 Hcells))
    end
  | closed_side
  | lazymatch type of Hcells with
    | ro_cells _ _ _ _ => let Hwr := fresh "Hwr" in intros Hwr; vm_compute in Hwr; discriminate Hwr
    | rw_cells _ _ _ _ => intros _; exact (proj2 Hcells)
    end
  | closed_side ].

Lemma xg2_ok : region_ok bsegs rho 2%uint63 xg_2 m.
Proof.
  assert (Hro_view : forall a, 65536 <= a < 1654784 -> mrd bsegs m (wa a) = seg_rom bsegs (wa a)).
  { intros addr Hro_span. unfold mrd. rewrite (ro_none m addr MI Hro_span). exact eq_refl. }
  img_region 0%nat seg0 seg0_chunk seg0_rd find_seg0_in Hro_view.
Qed.

Lemma xg3_ok : region_ok bsegs rho 3%uint63 xg_3 m.
Proof. img_region 2%nat seg2 seg2_chunk seg2_rd find_seg2_in V_relro. Qed.

Lemma xg4_ok : region_ok bsegs rho 4%uint63 xg_4 m.
Proof. lit_cells 4%uint63 xg_4 6176536%uint63 ([C8 (Z_to_bv 64 0x5634a4)]) C_memset. Qed.

Lemma xg5_ok : region_ok bsegs rho 5%uint63 xg_5 m.
Proof. img_region 3%nat seg3 seg3_chunk seg3_rd find_seg3_in V_gdesc. Qed.

Lemma xg6_ok : region_ok bsegs rho 6%uint63 xg_6 m.
Proof. lit_cells 6%uint63 xg_6 6947648%uint63 ([C8 (Z_to_bv 64 1)]) C_flag. Qed.

Lemma xg7_ok : region_ok bsegs rho 7%uint63 xg_7 m.
Proof. lit_cells 7%uint63 xg_7 6951440%uint63 ([C4 (Z_to_bv 64 1)]) C_f1. Qed.

Lemma xg8_ok : region_ok bsegs rho 8%uint63 xg_8 m.
Proof. lit_cells 8%uint63 xg_8 6951600%uint63 ([C8 (Z_to_bv 64 0)]) C_mu. Qed.

Lemma xg9_ok : region_ok bsegs rho 9%uint63 xg_9 m.
Proof. lit_cells 9%uint63 xg_9 6959708%uint63 ([C1 (Z_to_bv 8 1)]) C_f2. Qed.

Lemma xg10_ok : region_ok bsegs rho 10%uint63 xg_10 m.
Proof. lit_cells 10%uint63 xg_10 6961656%uint63 ([C8 (Z_to_bv 64 0x7fff8000)]) C_shb. Qed.

Lemma xg11_ok : region_ok bsegs rho 11%uint63 xg_11 m.
Proof. lit_cells 11%uint63 xg_11 6964952%uint63 ([C1 (Z_to_bv 8 1)]) C_f3. Qed.

Lemma xg12_ok : region_ok bsegs rho 12%uint63 xg_12 m.
Proof. lit_cells 12%uint63 xg_12 7558560%uint63 ([C8 (Z_to_bv 64 0xffffffffffffffff)]) C_w. Qed.

Lemma xg13_ok : region_ok bsegs rho 13%uint63 xg_13 m.
Proof. refine (unknown_region_ok bsegs rho 13%uint63 _ _ _ _ m _ _); [closed_side | exact W_odr0]. Qed.

Lemma xg14_ok : region_ok bsegs rho 14%uint63 xg_14 m.
Proof. refine (unknown_region_ok bsegs rho 14%uint63 _ _ _ _ m _ _); [closed_side | exact W_odr1]. Qed.

Lemma xg15_ok : region_ok bsegs rho 15%uint63 xg_15 m.
Proof. refine (unknown_region_ok bsegs rho 15%uint63 _ _ _ _ m _ _); [closed_side | exact W_odr2]. Qed.

Lemma xg16_ok : region_ok bsegs rho 16%uint63 xg_16 m.
Proof. refine (unknown_region_ok bsegs rho 16%uint63 _ _ _ _ m _ _); [closed_side | exact W_odr3]. Qed.

Lemma xg17_ok : region_ok bsegs rho 17%uint63 xg_17 m.
Proof. refine (unknown_region_ok bsegs rho 17%uint63 _ _ _ _ m _ _); [closed_side | exact W_odr4]. Qed.

Lemma xg18_ok : region_ok bsegs rho 18%uint63 xg_18 m.
Proof. refine (unknown_region_ok bsegs rho 18%uint63 _ _ _ _ m _ _); [closed_side | exact W_odr5]. Qed.

Lemma xg19_ok : region_ok bsegs rho 19%uint63 xg_19 m.
Proof. refine (unknown_region_ok bsegs rho 19%uint63 _ _ _ _ m _ _); [closed_side | exact W_odr6]. Qed.

Lemma xg20_ok : region_ok bsegs rho 20%uint63 xg_20 m.
Proof. refine (unknown_region_ok bsegs rho 20%uint63 _ _ _ _ m _ _); [closed_side | exact W_odr7]. Qed.

Lemma xg21_ok : region_ok bsegs rho 21%uint63 xg_21 m.
Proof. refine (unknown_region_ok bsegs rho 21%uint63 _ _ _ _ m _ _); [closed_side | exact W_odr8]. Qed.

Lemma xg22_ok : region_ok bsegs rho 22%uint63 xg_22 m.
Proof. refine (unknown_region_ok bsegs rho 22%uint63 _ _ _ _ m _ _); [closed_side | exact W_odr9]. Qed.

Lemma xg23_ok : region_ok bsegs rho 23%uint63 xg_23 m.
Proof. refine (unknown_region_ok bsegs rho 23%uint63 _ _ _ _ m _ _); [closed_side | exact W_odr10]. Qed.

Lemma xg24_ok : region_ok bsegs rho 24%uint63 xg_24 m.
Proof. refine (unknown_region_ok bsegs rho 24%uint63 _ _ _ _ m _ _); [closed_side | exact W_img_shadow]. Qed.


Variables (lo sp0 : Z).
Hypothesis STKH : stk bsegs m lo sp0.
Hypothesis Hrho1 : rho 1%uint63 = sp0 - XD_STACK.
Hypothesis Hlo : lo <= sp0 - XD_STACK.
Hypothesis Hlo0 : XSH_HI <= lo.
Hypothesis Hsp63 : sp0 < 2 ^ 63.
Hypothesis Hsp16 : sp0 mod 16 = 0.

Lemma xg1_ok : region_ok bsegs rho 1%uint63 xg_1 m.
Proof.
  assert (Hxd : XD_STACK = 1024) by exact eq_refl.
  assert (Hpow63 : 2 ^ 63 = 9223372036854775808) by exact eq_refl.
  pose proof Hlo0 as Hfloor. unfold XSH_HI in Hfloor.
  pose proof STKH as Hstk_frame. destruct Hstk_frame as (Hlo_nonneg & _ & Hstk_cells).
  pose proof (region_ok_fresh bsegs rho 1%uint63 None XSTK 4%uint63 true 7%nat m) as Hfresh.
  cbv zeta in Hfresh. unfold rbase in Hfresh. cbn [rg_abs] in Hfresh.
  rewrite Hrho1 in Hfresh.
  change (to_Z XSTK) with 1024 in Hfresh.
  change (2 ^ to_Z 4%uint63) with 16 in Hfresh.
  assert (Hbase_pos : 0 < sp0 - XD_STACK) by lia.
  assert (Hbase_top : sp0 - XD_STACK + 1024 < two63) by (unfold two63; lia).
  assert (Hbase_align : (sp0 - XD_STACK) mod 16 = 0).
  { rewrite Hxd, Zminus_mod, Hsp16. exact eq_refl. }
  assert (Hframe_bytes : forall i, 0 <= i < 1024 ->
            (exists b, mrd bsegs m (wa (sp0 - XD_STACK + i)) = Some b)
            /\ (true = true -> wview bsegs m (wa (sp0 - XD_STACK + i)) <> None)).
  { intros i Hi_range. destruct (Hstk_cells (sp0 - XD_STACK + i)) as [Hview Hread]; [lia|].
    split; [exact Hread | intros _; exact Hview]. }
  refine (Hfresh Hbase_pos Hbase_top _ _ _ _ Hbase_align Hframe_bytes); closed_side.
Qed.

Definition ivr (t : int) (rg : region) : Z * Z := (rbase rho t rg, rbase rho t rg + to_Z (rg_size rg)).

Local Ltac sep :=
  unfold ivr, rbase; cbn [rg_abs rg_size xg_1 xg_2 xg_3 xg_4 xg_5 xg_6 xg_7 xg_8 xg_9 xg_10 xg_11 xg_12 xg_13 xg_14 xg_15 xg_16 xg_17 xg_18 xg_19 xg_20 xg_21 xg_22 xg_23 xg_24];
  rewrite ?Hrho1;
  repeat match goal with |- context [to_Z ?x] => is_ground x; let v := eval vm_compute in (to_Z x) in change (to_Z x) with v end;
  repeat (constructor; [cbn [fst snd]; lia|]); constructor.

Lemma rmemX : Rmem bsegs rho MX m.
Proof.
  pose proof Hlo0 as Hfloor. unfold XSH_HI in Hfloor.
  assert (Hacc : Rmem bsegs rho IEmpty m /\ dir_in rho IEmpty []).
  { split; [exact (Rmem_empty bsegs rho m) | exact (dir_in_empty rho)]. }
  let grow tag reg reg_ok :=
    let Hrm := fresh "Hrm" in let Hdi := fresh "Hdi" in
    destruct Hacc as [Hrm Hdi];
    assert (Hacc := Rmem_add_sep bsegs rho _ tag reg m _ Hrm Hdi);
    specialize (Hacc ltac:(closed_side) ltac:(closed_side) reg_ok ltac:(sep));
    clear Hrm Hdi in
  grow 2%uint63 xg_2 xg2_ok; grow 3%uint63 xg_3 xg3_ok; grow 4%uint63 xg_4 xg4_ok;
  grow 5%uint63 xg_5 xg5_ok; grow 6%uint63 xg_6 xg6_ok; grow 7%uint63 xg_7 xg7_ok;
  grow 8%uint63 xg_8 xg8_ok; grow 9%uint63 xg_9 xg9_ok; grow 10%uint63 xg_10 xg10_ok;
  grow 11%uint63 xg_11 xg11_ok; grow 12%uint63 xg_12 xg12_ok; grow 13%uint63 xg_13 xg13_ok;
  grow 14%uint63 xg_14 xg14_ok; grow 15%uint63 xg_15 xg15_ok; grow 16%uint63 xg_16 xg16_ok;
  grow 17%uint63 xg_17 xg17_ok; grow 18%uint63 xg_18 xg18_ok; grow 19%uint63 xg_19 xg19_ok;
  grow 20%uint63 xg_20 xg20_ok; grow 21%uint63 xg_21 xg21_ok; grow 22%uint63 xg_22 xg22_ok;
  grow 23%uint63 xg_23 xg23_ok; grow 24%uint63 xg_24 xg24_ok; grow 1%uint63 xg_1 xg1_ok.
  exact (proj1 Hacc).
Qed.

End Handoff.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rho_x (sp0 : Z) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : valuation := fun t =>
  if (t =? 1)%uint63 then sp0 - XD_STACK
  else if (t =? TX_RA)%uint63 then bv_unsigned ra else if (t =? TX_GP)%uint63 then bv_unsigned gp
  else if (t =? TX_S0)%uint63 then bv_unsigned s0 else if (t =? TX_S0 + 1)%uint63 then bv_unsigned s1
  else if (t =? TX_S0 + 2)%uint63 then bv_unsigned s2 else if (t =? TX_S0 + 3)%uint63 then bv_unsigned s3
  else if (t =? TX_S0 + 4)%uint63 then bv_unsigned s4 else if (t =? TX_S0 + 5)%uint63 then bv_unsigned s5
  else if (t =? TX_S0 + 6)%uint63 then bv_unsigned s6 else if (t =? TX_S0 + 7)%uint63 then bv_unsigned s7
  else if (t =? TX_S0 + 8)%uint63 then bv_unsigned s8 else if (t =? TX_S0 + 9)%uint63 then bv_unsigned s9
  else if (t =? TX_S0 + 10)%uint63 then bv_unsigned s10 else if (t =? TX_S0 + 11)%uint63 then bv_unsigned s11
  else 0.

Lemma Rregs_initX (rho : valuation)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word) :
  (forall t, to_Z t < to_Z NEXTX -> rho t = rho_x (bv_unsigned sp) ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t) ->
  tp = wbv TPVX ->
  Rregs rho regsX (Core (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F pc fc rv).
Proof.
  intros Hrho -> r.
  assert (Esp : pword rho 1%uint63 (W false XSTK) = sp).
  { unfold pword. rewrite (Hrho 1%uint63) by (vm_compute; reflexivity).
    change (rho_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1%uint63) with (bv_unsigned sp - XD_STACK).
    change (wZ (W false XSTK)) with XD_STACK. replace (bv_unsigned sp - XD_STACK + XD_STACK) with (bv_unsigned sp) by lia. apply Z_to_bv_bv_unsigned. }
  destruct (reg_cases r) as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
    subst r; try exact I; try reflexivity; try exact (eq_sym Esp);
    cbn [den]; symmetry; apply pword_scalar; rewrite Hrho by (vm_compute; reflexivity); reflexivity.
Qed.

Lemma final_regs_denX (rho : valuation) (S : sstate) (F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) :
  final_regs_okX S = true ->
  Rregs rho (s_regs S) (Core (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv) ->
  x1 = pword rho TX_RA w_zero /\ x2 = pword rho 1%uint63 (W false XSTK) /\ x3 = pword rho TX_GP w_zero /\ x4 = wbv TPVX
  /\ x8 = pword rho TX_S0 w_zero /\ x9 = pword rho (TX_S0 + 1)%uint63 w_zero /\ x18 = pword rho (TX_S0 + 2)%uint63 w_zero
  /\ x19 = pword rho (TX_S0 + 3)%uint63 w_zero /\ x20 = pword rho (TX_S0 + 4)%uint63 w_zero /\ x21 = pword rho (TX_S0 + 5)%uint63 w_zero
  /\ x22 = pword rho (TX_S0 + 6)%uint63 w_zero /\ x23 = pword rho (TX_S0 + 7)%uint63 w_zero /\ x24 = pword rho (TX_S0 + 8)%uint63 w_zero
  /\ x25 = pword rho (TX_S0 + 9)%uint63 w_zero /\ x26 = pword rho (TX_S0 + 10)%uint63 w_zero /\ x27 = pword rho (TX_S0 + 11)%uint63 w_zero.
Proof.
  intros Hok HR. unfold final_regs_okX, final_regsX in Hok. cbn [forallb fst snd] in Hok.
  repeat (apply andb_prop in Hok as [?E Hok]). clear Hok.
  repeat match goal with E : hval_eqb (rget S ?X) ?v = true |- _ => apply hval_eqb_eq in E end.
  pose proof (HR (Z_to_bv 5 1)) as D1. pose proof (HR (Z_to_bv 5 2)) as D2. pose proof (HR (Z_to_bv 5 3)) as D3. pose proof (HR (Z_to_bv 5 4)) as D4.
  pose proof (HR (Z_to_bv 5 8)) as D8. pose proof (HR (Z_to_bv 5 9)) as D9. pose proof (HR (Z_to_bv 5 18)) as D18. pose proof (HR (Z_to_bv 5 19)) as D19.
  pose proof (HR (Z_to_bv 5 20)) as D20. pose proof (HR (Z_to_bv 5 21)) as D21. pose proof (HR (Z_to_bv 5 22)) as D22. pose proof (HR (Z_to_bv 5 23)) as D23.
  pose proof (HR (Z_to_bv 5 24)) as D24. pose proof (HR (Z_to_bv 5 25)) as D25. pose proof (HR (Z_to_bv 5 26)) as D26. pose proof (HR (Z_to_bv 5 27)) as D27.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 1))) with (rget S X1) in D1. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 2))) with (rget S X2) in D2.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 3))) with (rget S X3) in D3. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 4))) with (rget S X4) in D4.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 8))) with (rget S X8) in D8. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 9))) with (rget S X9) in D9.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 18))) with (rget S X18) in D18. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 19))) with (rget S X19) in D19.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 20))) with (rget S X20) in D20. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 21))) with (rget S X21) in D21.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 22))) with (rget S X22) in D22. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 23))) with (rget S X23) in D23.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 24))) with (rget S X24) in D24. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 25))) with (rget S X25) in D25.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 26))) with (rget S X26) in D26. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 27))) with (rget S X27) in D27.
  repeat match goal with E : rget S ?X = _, D : den rho (rget S ?X) _ |- _ => rewrite E in D; clear E end.
  cbn [den] in *. repeat split; assumption.
Qed.

Lemma stk_top_below (m : word -> option byte) (lo hi : Z) : mem_inv bsegs m -> stk bsegs m lo hi -> lo < hi -> hi <= UTOP.
Proof.
  intros Hinv Hstk Hgap.
  destruct Hstk as (Hlo_nonneg & Hhi_cap & Hstk_cells).
  destruct (Hstk_cells (hi - 1)) as [Hlast_view _]; [lia|].
  pose proof (wview_below bsegs m (wa (hi - 1)) Hinv Hlast_view) as Hbelow.
  rewrite wa_unsigned in Hbelow by lia.
  lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition dtor_pre (m : word -> option byte) : Prop :=
  (forall a, 5681152 <= a < 6172672 -> mrd bsegs m (wa a) = seg_rom bsegs (wa a)) /\
  (forall a, 6190176 <= a < 6947616 -> mrd bsegs m (wa a) = seg_rom bsegs (wa a)) /\
  ro_cells bsegs m 6176536 [C8 (Z_to_bv 64 0x5634a4)] /\
  rw_cells bsegs m 6947648 [C8 (Z_to_bv 64 1)] /\
  ro_cells bsegs m 6951440 [C4 (Z_to_bv 64 1)] /\
  rw_cells bsegs m 6951600 [C8 (Z_to_bv 64 0)] /\
  ro_cells bsegs m 6959708 [C1 (Z_to_bv 8 1)] /\
  ro_cells bsegs m 6961656 [C8 (Z_to_bv 64 0x7fff8000)] /\
  ro_cells bsegs m 6964952 [C1 (Z_to_bv 8 1)] /\
  ro_cells bsegs m 7558560 [C8 (Z_to_bv 64 0xffffffffffffffff)] /\
  Forall (fun iv : Z * Z => stk bsegs m (fst iv) (snd iv))
    [(12413536, 12413544); (12413920, 12413928); (12420128, 12420184); (12420224, 12420304);
     (12420384, 12420424); (12420480, 12420528); (12420864, 12420904); (12420992, 12421000);
     (12427808, 12427840); (12427872, 12427896); (12428000, 12428504); (2147459072, 2149022208)].

Theorem module_dtor_spec : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> XSH_HI <= lo -> lo <= bv_unsigned sp - XD_STACK ->
  bv_unsigned sp mod 16 = 0 -> mem_inv bsegs m -> tp = Z_to_bv 64 0xbdae50 -> dtor_pre m ->
  evt bsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom bsegs)
               /\ munch ((bv_unsigned sp - XD_STACK, bv_unsigned sp) :: WX) m m'
               /\ wmono bsegs m m' /\ mem_inv bsegs m'
               /\ stk bsegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 MODULE_DTOR) fc None m (seg_rom bsegs)).
Proof.
  assert (Hivl_inside : forall (L : list ivl) (l_iv h_iv a n : Z),
            In (l_iv, h_iv) L -> l_iv <= a -> a + n <= h_iv -> inside L a n).
  { intros L. induction L as [|[l_hd h_hd] L_tl IH_tl]; intros l_iv h_iv a n Hmem Hstart_le Hend_le.
    - cbn [In] in Hmem. contradiction.
    - cbn [In] in Hmem. cbn [inside]. destruct Hmem as [Hhead|Htail].
      + injection Hhead as Hl_eq Hh_eq. left. lia.
      + right. exact (IH_tl l_iv h_iv a n Htail Hstart_le Hend_le). }
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
         Hstk Hfloor Hframe Hsp_align Hinv Htp Hpre.
  destruct Hpre as (Hrelro & Hgdesc & Hmemset & Hflag & Hf1 & Hmu & Hf2 & Hshb & Hf3 & Hcw & Hstk_all).
  pose proof (proj1 (Forall_forall _ _) Hstk_all) as Hstk_at.
  assert (Hxd : XD_STACK = 1024) by exact eq_refl.
  pose (rho0 := rho_x (bv_unsigned sp) ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  pose (Wfp := (bv_unsigned sp - XD_STACK, bv_unsigned sp) :: WX).
  lazymatch goal with |- evt _ _ ?start => set (ms0 := start) end.
  assert (Hsp_top : bv_unsigned sp < 2 ^ 63).
  { pose proof (stk_top_below m lo (bv_unsigned sp) Hinv Hstk ltac:(lia)) as Hceiling.
    eapply Z.le_lt_trans; [exact Hceiling | vm_compute; exact eq_refl]. }
  assert (Hstart : Rn bsegs rho0 S0X ms0).
  { intros rho' Hagree.
    assert (Hrho'_x : forall t, to_Z t < to_Z NEXTX ->
              rho' t = rho_x (bv_unsigned sp) ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t) by exact Hagree.
    assert (Hrho'_1 : rho' 1%uint63 = bv_unsigned sp - XD_STACK).
    { rewrite (Hrho'_x 1%uint63) by (vm_compute; exact eq_refl). exact eq_refl. }
    assert (Htp_word : tp = wbv TPVX) by (rewrite Htp; exact eq_refl).
    split; [exact eq_refl|]. split; [exact eq_refl|]. split.
    { exact (Rregs_initX rho' ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               F (Z_to_bv 64 MODULE_DTOR) fc None Hrho'_x Htp_word). }
    split; [exact eq_refl|].
    refine (rmemX rho' m Hinv Hrelro Hgdesc Hmemset Hflag Hf1 Hmu Hf2 Hshb Hf3 Hcw
              _ _ _ _ _ _ _ _ _ _ _ _ lo (bv_unsigned sp) Hstk Hrho'_1 Hframe Hfloor Hsp_top Hsp_align);
      lazymatch goal with
      | |- stk bsegs m ?lo_w ?hi_w =>
          apply (Hstk_at (lo_w, hi_w)); cbn [In]; repeat (first [left; exact eq_refl | right])
      end. }
  assert (Hwrite_ok : forall t rg, mget MX t = Some rg -> rg_wr rg = true ->
            inside Wfp (rbase rho0 t rg) (to_Z (rg_size rg))).
  { intros t rg Hget Hwr.
    pose proof (mem_check_ok wr_bX MX MX_checked t rg Hget) as Hplace.
    unfold wr_bX in Hplace. rewrite Hwr in Hplace. cbn [negb orb] in Hplace.
    apply andb_prop in Hplace as [_ Hplace].
    unfold rbase. revert Hplace. destruct (rg_abs rg) as [base|]; intros Hplace.
    - apply existsb_exists in Hplace as ([l_iv h_iv] & Hiv_mem & Hiv_match).
      cbn [fst snd] in Hiv_match.
      apply andb_prop in Hiv_match as [Hl_match Hh_match]. apply Z.eqb_eq in Hl_match, Hh_match.
      unfold Wfp. cbn [inside]. right.
      apply (Hivl_inside WX l_iv h_iv); [exact Hiv_mem | lia | lia].
    - apply andb_prop in Hplace as [Htag_one Hsize_k]. apply Z.eqb_eq in Htag_one, Hsize_k.
      assert (Ht_one : t = 1%uint63) by (apply to_Z_inj; exact Htag_one).
      subst t. unfold Wfp. cbn [inside]. left.
      change (rho0 1%uint63) with (bv_unsigned sp - XD_STACK). lia. }
  assert (Hinv0 : CInv bsegs MX Wfp m F fc S0X ms0).
  { refine (conj (same_dirs_refl MX) (conj (munch_refl Wfp m) (conj (wmono_refl bsegs m)
             (conj Hinv (conj eq_refl (conj eq_refl (conj eq_refl _))))))).
    exists ra, sp, gp, tp, t0, t1, t2, s0, s1, a0, a1, a2, a3, a4, a5, a6, a7,
      s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, t3, t4, t5, t6.
    exact eq_refl. }
  pose proof exit_checked as Hexit.
  apply exit_ok_inv in Hexit as (ic_end & S_end & Hres & Hpc_end & Hresv_end & Hregs_end).
  rewrite exit_result_unfold in Hres.
  destruct (hx_run_Rn_inv bsegs stopX rho0 (CInv bsegs MX Wfp m F fc)
              (CInv_step bsegs rho0 MX Wfp m F fc Hwrite_ok) 21 IEmpty ic_end S0X (RStop S_end) ms0
              (ic_ok_empty bsegs) Hstart Hinv0 Hres) as (_ & ms1 & Hsteps01 & HRn1 & Hinv1).
  cbn [res_state] in HRn1, Hinv1.
  destruct fetch_finalX as [ic_ret Hfetch_ret].
  rewrite <- Hpc_end in Hfetch_ret.
  pose proof (Rn_R bsegs rho0 S_end ms1 HRn1) as HR1.
  destruct (hx_ret_step bsegs rho0 IEmpty ic_ret S_end ms1 (ic_ok_empty bsegs) HR1 Hfetch_ret) as (ms2 & Hstep12 & Hms2).
  destruct Hinv1 as (_ & Hmunch1 & Hwmono1 & Hinv_m1 & Hfregs1 & Hfcsr1 & Hrom1 & Hnf1).
  destruct Hnf1 as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16
                    & x17 & x18 & x19 & x20 & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & Hregs1).
  destruct HR1 as (_ & _ & Hden1 & Hresv1 & _).
  rewrite Hresv_end in Hresv1. cbn [Rresv] in Hresv1.
  unfold core_of in Hden1. rewrite Hregs1 in Hden1.
  destruct (final_regs_denX rho0 S_end _ _ _ _ x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
              x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Hregs_end Hden1)
    as (Hx1 & Hx2 & Hx3 & Hx4 & Hx8 & Hx9 & Hx18 & Hx19 & Hx20 & Hx21 & Hx22 & Hx23 & Hx24 & Hx25 & Hx26 & Hx27).
  repeat match goal with
         | Hreg : _ = pword rho0 ?tag w_zero |- _ => rewrite (pword_scalar rho0 tag _ eq_refl) in Hreg
         end.
  assert (Hsp_word : pword rho0 1%uint63 (W false XSTK) = sp).
  { unfold pword. change (rho0 1%uint63) with (bv_unsigned sp - XD_STACK). change (wZ (W false XSTK)) with 1024.
    replace (bv_unsigned sp - XD_STACK + 1024) with (bv_unsigned sp) by lia. apply Z_to_bv_bv_unsigned. }
  rewrite Hsp_word in Hx2.
  assert (Hx4_tp : x4 = tp) by (rewrite Hx4, Htp; exact eq_refl).
  clear Hx4.
  subst x1 x2 x3 x4 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27.
  exists ms2. split.
  - exact (msteps_trans bsegs ms0 ms1 ms2 Hsteps01 (msteps_one bsegs ms1 ms2 Hstep12)).
  - exists x5, x6, x7, x10, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, (ms_mem ms1).
    split.
    + rewrite Hms2. unfold core_of. rewrite Hregs1, Hfregs1, Hfcsr1, Hrom1, Hresv1. exact eq_refl.
    + split; [exact Hmunch1|]. split; [exact Hwmono1|]. split; [exact Hinv_m1|].
      destruct Hstk as (Hlo_nn & Hsp_cap & Hstk_bytes).
      split; [exact Hlo_nn|]. split; [exact Hsp_cap|].
      intros addr Haddr. destruct (Hstk_bytes addr Haddr) as [Hview0 _].
      pose proof (Hwmono1 (wa addr) Hview0) as Hview1.
      split; [exact Hview1|]. exact (wview_mrd bsegs (ms_mem ms1) (wa addr) asegs_wr_rd Hview1).
Qed.

(* [comment removed for export] *)
