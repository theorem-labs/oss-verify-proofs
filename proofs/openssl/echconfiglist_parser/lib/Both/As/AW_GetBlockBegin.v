(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics AllocWalkKit.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_Leaves AW_LargeAlloc2 AW_LargeAlloc3 AllocTacX.
Import ListNotations.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocStoreDj.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_rx8 segs m a bs.   (* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

(* [comment removed for export] *)
Definition gbb_step (p : Z) (best c : Z) : Z := if (best <? c) && (c <=? p) then c else best.
Definition gbb_scan (p : Z) (best : Z) (l : list Z) : Z := fold_left (gbb_step p) l best.

Lemma gbb_scan_bound : forall p l best, 0 <= best <= p -> Forall (fun c => 0 <= c) l -> 0 <= gbb_scan p best l <= p.
Proof.
  intros p l. induction l as [|c l IH]; intros best HB HL; cbn [gbb_scan fold_left]; [exact HB|].
  apply Forall_cons_iff in HL. destruct HL as [Hc HL]. apply IH; [| exact HL].
  unfold gbb_step. destruct (Z.ltb_spec best c); destruct (Z.leb_spec c p); cbn [andb]; lia.
Qed.

(* [comment removed for export] *)
Lemma gbb_scan_hit : forall p l best a,
  0 <= best <= a -> a <= p -> Forall (fun c => 0 <= c /\ (c <= p -> c <= a)) l -> (In a l \/ best = a) ->
  gbb_scan p best l = a.
Proof.
  intros p l. induction l as [|c l IH]; intros best a HB HA HL HIN; cbn [gbb_scan fold_left].
  - destruct HIN as [[]| ->]. reflexivity.
  - apply Forall_cons_iff in HL. destruct HL as [[Hc0 Hc] HL].
    change (fold_left (gbb_step p) l (gbb_step p best c)) with (gbb_scan p (gbb_step p best c) l).
    apply IH; [| exact HA | exact HL |].
    + unfold gbb_step. destruct (Z.ltb_spec best c); destruct (Z.leb_spec c p); cbn [andb]; lia.
    + unfold gbb_step. destruct HIN as [[->|HIN]|HB'].
      * right. destruct (Z.ltb_spec best a); destruct (Z.leb_spec a p); cbn [andb]; lia.
      * left. exact HIN.
      * right. subst best. destruct (Z.ltb_spec a c); destruct (Z.leb_spec c p); cbn [andb]; lia.
Qed.

Lemma u64arr_cons : forall m A w ws,
  u64arr asegs m A (w :: ws) <-> rw_cells asegs m A [C8 w] /\ u64arr asegs m (A + 8) ws.
Proof.
  intros m A w ws. unfold u64arr, rw_cells, cells_at. change (u64s (w :: ws)) with (le8 w ++ u64s ws).
  cbn [map concat cells_bytes cbytes cells_wf cell_wf cells_size csize app].
  rewrite app_nil_r. rewrite bytes_at_app, length_le8. cbn [length].
  replace (8 * Z.of_nat (S (length ws))) with (8 + 8 * Z.of_nat (length ws)) by lia.
  rewrite wr_at_app by lia. change (Z.of_nat (8 + 0)) with 8. change (Z.of_nat 8) with 8. tauto.
Qed.
End HCW.

Section Loop.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.
  Variables (x1 x2 x3 x4 x6 x7 x8 x9 x10 x11 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (p pe : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis PR : 0 <= p < 2^47.

  (* [comment removed for export] *)
  Lemma gbb_iter : forall (c cur best : Z) (x15 x16 x17 x5 : word),
    rw_cells asegs m cur [C8 (wz c)] -> 0 <= cur -> cur + 8 <= aceil -> 0 <= c < 2^47 -> 0 <= best <= p ->   (* [comment removed for export] *)
    evt asegs (fun ms' => exists (y5 y15 y16 y17 : word),
        ms' = MS (mkR x1 x2 x3 x4 y5 x6 x7 x8 x9 x10 (wz p) (wz (cur + 8)) (wz (gbb_step p best c)) (wz pe) y15 y16 y17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                 F (Z_to_bv 64 0x199500) fc None m (seg_rom asegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (wz p) (wz cur) (wz best) (wz pe) x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x199504) fc None m (seg_rom asegs)).
  Proof.
    intros c cur best x15 x16 x17 x5 HD CLO CHI RC BEST.
    unfold AHI_LO in CLO. acb. unfold wz in *.
    (* [comment removed for export] *)
    step. step. step. step.
    rewrite ?(unsigned_lit p), ?(unsigned_lit c), ?(unsigned_lit best) by lia.
    unfold gbb_step. destruct (Z.leb_spec c p) as [CP|CP].
    - (* [comment removed for export] *)
      step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
      + (* [comment removed for export] *)
        step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia. { exfalso. lia. }
        step. step. step. replace (best <? c) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
        apply evt_done. do 4 eexists. reflexivity.
      + (* [comment removed for export] *)
        step. step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia. { exfalso. lia. }
        step. step. step. step. replace (best <? c) with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb].
        apply evt_done. do 4 eexists. reflexivity.
    - (* [comment removed for export] *)
      rewrite andb_false_r.
      step. if_cases K.
      + (* [comment removed for export] *)
        step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia. 2:{ exfalso. lia. }
        step. apply evt_done. do 4 eexists. reflexivity.
      + (* [comment removed for export] *)
        step. step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia. 2:{ exfalso. lia. }
        step. apply evt_done. do 4 eexists. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma gbb_loop : forall (l : list Z) (c : Z) (cur best : Z) (x15 x16 x17 x5 : word),
    u64arr asegs m cur (wlist (c :: l)) -> cur + 8 * (1 + zlen l) = pe -> 0 <= cur -> pe <= aceil ->   (* [comment removed for export] *)
    Forall (fun c => 0 <= c < 2^47) (c :: l) -> 0 <= best <= p ->
    evt asegs (fun ms' => exists (y5 y15 y16 y17 : word),
        ms' = MS (mkR x1 x2 x3 x4 y5 x6 x7 x8 x9 x10 (wz p) (wz pe) (wz (gbb_scan p best (c :: l))) (wz pe) y15 y16 y17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                 F (Z_to_bv 64 0x199530) fc None m (seg_rom asegs))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (wz p) (wz cur) (wz best) (wz pe) x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x199504) fc None m (seg_rom asegs)).
  Proof.
    induction l as [|c2 l IH]; intros c cur best x15 x16 x17 x5 ARR CUR CLO CHI RNG BEST.
    - (* [comment removed for export] *)
      apply Forall_cons_iff in RNG. destruct RNG as [RC _]. unfold zlen in CUR. cbn [length Z.of_nat] in CUR.
      change (wlist [c]) with ([Z_to_bv 64 c]) in ARR. apply u64arr_cons in ARR. destruct ARR as [HD _].
      eapply evt_cut. { eapply (gbb_iter c cur best); try eassumption; unfold AHI_LO in *; acb; lia. }
      cbv beta. intros ms' (y5 & y15 & y16 & y17 & ->).
      unfold AHI_LO in CLO. acb. unfold wz.
      (* [comment removed for export] *)
      step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. 2:{ exfalso. lia. }
      replace (cur + 8) with pe by lia. change (gbb_scan p best [c]) with (gbb_step p best c).
      apply evt_done. do 4 eexists. reflexivity.
    - (* [comment removed for export] *)
      pose proof RNG as RNG0. apply Forall_cons_iff in RNG. destruct RNG as [RC RNG'].
      assert (LL : cur + 8 + 8 * (1 + zlen l) = pe) by (unfold zlen in *; cbn [length] in CUR; lia).
      assert (ZL : 0 <= zlen l) by (unfold zlen; lia).
      change (wlist (c :: c2 :: l)) with (Z_to_bv 64 c :: wlist (c2 :: l)) in ARR. apply u64arr_cons in ARR. destruct ARR as [HD ARR].
      eapply evt_cut. { eapply (gbb_iter c cur best); try eassumption; unfold AHI_LO in *; acb; lia. }
      cbv beta. intros ms' (y5 & y15 & y16 & y17 & ->).
      pose proof CLO as CLO'. unfold AHI_LO in CLO'. pose proof CHI as CHI'. acb. unfold wz.
      (* [comment removed for export] *)
      step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.
      change (gbb_scan p best (c :: c2 :: l)) with (gbb_scan p (gbb_step p best c) (c2 :: l)).
      eapply (IH c2 (cur + 8) (gbb_step p best c)); try eassumption; try lia.
      all: try (unfold AHI_LO in *; lia).
      unfold gbb_step. destruct (Z.ltb_spec best c); destruct (Z.leb_spec c p); cbn [andb]; lia.
  Qed.
End Loop.
Section HCW.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.

(* [comment removed for export] *)
Definition gbb_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo a : Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (a + 4096)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (6976832, 6976836)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' 6976832 [C8 (wz 0)].
End HCW.     (* [comment removed for export] *)

Section Spec.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo p a msz sz idx pa nres nch srt : Z) (chunks : list Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 32 <= bv_unsigned sp.
  Hypothesis Ha0 : a0 = wz (AINST + 64). Hypothesis Ha1 : a1 = wz p.
  Hypothesis AR : aapp a msz /\ a + msz <= aceil /\ a mod 4096 = 0 /\ a <= p < a + msz /\ 0x2000 <= msz.
  Hypothesis PAR : aapp pa (8 * nch) /\ pa + 8 * nch <= aceil.
  Hypothesis NCH : zlen chunks = nch /\ 1 <= nch.
  Hypothesis INA : In a chunks.
  (* [comment removed for export] *)
  Hypothesis DISJ : Forall (fun c => 0 <= c < 2^47 /\ (c <= p -> c <= a)) chunks.
  Hypothesis INST64 : rw_cells asegs m (AINST + 64) [C8 (wz 4096); C8 (wz pa); C8 (wz pa)].
  Hypothesis NRES : rw_cells asegs m (AINST + 112) [C8 (wz nres); C8 (wz nch); C8 (wz srt)].
  Hypothesis MTX : rw_cells asegs m (AINST + 680) [C8 (wz 0)].
  Hypothesis PA : u64arr asegs m pa (wlist chunks).
  Hypothesis HDR : rw_cells asegs m a [C8 (wz a); C8 (wz msz); C8 (wz sz); C8 (wz idx)].

  Let ARE : 12599296 <= a /\ a + msz <= aceil. Proof. exact (aapp_env _ _ (proj1 AR) ltac:(lia)). Qed.   (* [comment removed for export] *)
  Let PAE : 12599296 <= pa /\ pa + 8 * nch <= aceil. Proof. exact (aapp_env _ _ (proj1 PAR) ltac:(lia)). Qed.   (* [comment removed for export] *)
  Theorem get_block_begin_spec :
    evt asegs (gbb_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo a)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x199498) fc None m (seg_rom asegs)).
  Proof.
    subst a0 a1. unfold AHI_LO, AINST in *. acb.
    change (6976152 + 64) with 6976216 in *. change (6976152 + 112) with 6976264 in *. change (6976152 + 680) with 6976832 in *. change (6976152 + 684) with 6976836.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    destruct NCH as [LEN NCH1]. destruct AR as (AHI & CE & AL & AP & MSZ). destruct PAR as [PLO PHI].
    assert (LENW : Z.of_nat (length (wlist chunks)) = nch) by (unfold wlist; rewrite length_map; unfold zlen in LEN; lia).
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (6976832, 6976836)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold wz in *. region_table.
    (* [comment removed for export] *)
    step. carve_frame 32%nat ST. step. step. step. step. step. step. step.
    try match goal with |- context [Z_to_bv 64 (Z.land ?x ?y)] => let v := eval vm_compute in (Z.land x y) in change (Z.land x y) with v end.
    step.
    (* [comment removed for export] *)
    apply rw_cells_C8_zero_split' in MTX.
    assert (MA : 6976832 mod 4 = 0) by reflexivity. assert (MR : 0 <= 6976832 < 2^64) by lia.
    astep. step. step. step. step.
    repeat match goal with |- context [Z_to_bv 64 (Z.lxor ?x ?y)] => let v := eval vm_compute in (Z.lxor x y) in change (Z.lxor x y) with v
                         | |- context [Z_to_bv 64 (Z.land ?x ?y)] => let v := eval vm_compute in (Z.land x y) in change (Z.land x y) with v end.
    astep.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.
    step.
    try match goal with |- context [Z_to_bv 64 (Z.land ?x ?y)] => let v := eval vm_compute in (Z.land x y) in change (Z.land x y) with v end.
    step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.
    (* [comment removed for export] *)
    step. step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    step. step. step. rewrite (unsigned_lit nch), Z.shiftl_mul_pow2 by lia. change (2^3) with 8. step. step.
    replace (pa + nch * 8) with (pa + 8 * nch) by lia.
    destruct chunks as [|c l]; [unfold zlen in LEN; cbn in LEN; lia|].
    assert (PR : 0 <= p < 2^47) by lia.
    eapply evt_cut.
    { eapply (gbb_loop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ p (pa + 8 * nch) PR l c pa 0); try eassumption; try lia.
      - unfold zlen in *. cbn [length] in LEN. lia.
      - eapply Forall_impl; [| exact DISJ]. intros x Hx. cbn beta in Hx. lia. }
    cbv beta. intros ms' (y5 & y15 & y16 & y17 & ->).
    rewrite (gbb_scan_hit p (c :: l) 0 a); [ | lia | lia | eapply Forall_impl; [|exact DISJ]; intros x Hx; cbn beta in Hx; lia | left; exact INA ].
    unfold wz.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    step. step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    step. step. step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    (* [comment removed for export] *)
    step. step. step. rewrite (unsigned_lit a) by lia.
    replace (Z.land 4095 a) with 0 by (rewrite Z.land_comm; change 4095 with (Z.ones 12); rewrite Z.land_ones by lia; clear - AL AHI; try acb; Z.div_mod_to_equations; lia).
    step. if_cases K. { exfalso. revert K. vm_compute. discriminate. } clear K.
    step. step.
    (* [comment removed for export] *)
    step. apply rw_cells_C4_1_bytes in MTX. st1. apply rw_cells_bytes_C4_0 in MTX. apply rw_cells_C4C4_C8_zero in MTX.
    step. step. step. step. step. step.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold gbb_post. do 15 eexists. split; [rewrite (Z.add_comm a 4096); reflexivity|].
    repeat match goal with |- _ /\ _ => split end; try assumption.
  Qed.
End Spec.

