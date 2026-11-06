From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcRec RcLib RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT dt1_head_c.
Import ListNotations.
Open Scope Z_scope.

Definition dt1_head_inv (m0 m : word -> option byte) (o : Z) (P : list byte) : Prop :=
  wr_at rsegs m o 20 /\ munch [(o, o + 20)] m0 m /\ wmono rsegs m0 m /\ (mem_inv rsegs m0 -> mem_inv rsegs m)
  /\ (forall lo hi, stk rsegs m0 lo hi -> stk rsegs m lo hi) /\ bytes_at rsegs m o P.

Lemma dt1_head_init : forall m o, wr_at rsegs m o 20 -> dt1_head_inv m m o [].
Proof.
  intros m o W. pose proof W as (Ho & Hl & _).
  split; [exact W|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [tauto|].
  split; [tauto|].
  apply bytes_at_nil. lia.
Qed.

Lemma dt1_head_ok : forall m0 m o P k, dt1_head_inv m0 m o P -> k = Z.of_nat (length P) -> (length P < 20)%nat ->
  store_ok rsegs m (wa (o + k)) 1 = true.
Proof.
  intros m0 m o P k (W & _) Hk Hl. apply (wr_at_store_ok rsegs m o 20 k 1 W); lia.
Qed.

Lemma dt1_head_ok0 : forall m0 m (x : word), dt1_head_inv m0 m (bv_unsigned x) [] -> store_ok rsegs m x 1 = true.
Proof.
  intros m0 m x D. pose proof (dt1_head_ok m0 m (bv_unsigned x) [] 0 D eq_refl ltac:(cbn; lia)) as H.
  rewrite Z.add_0_r in H. rewrite (wa_of_var x (bv_unsigned x) eq_refl) in H. exact H.
Qed.

Lemma dt1_head_wa0 : forall x : word, x = wa (bv_unsigned x + Z.of_nat 0).
Proof. intros x. unfold wa. cbn [Z.of_nat]. rewrite Z.add_0_r. symmetry. apply Z_to_bv_lit_self. Qed.

Lemma dt1_head_store : forall m0 m o P (A v : word), dt1_head_inv m0 m o P -> (length P < 20)%nat ->
  A = wa (o + Z.of_nat (length P)) ->
  dt1_head_inv m0 (write_to_mem m A (le1 v)) o (P ++ [Z_to_bv 8 (bv_unsigned v)]).
Proof.
  intros m0 m o P A v (W & MU & WM & MI & SK & BA) Hl ->.
  pose proof W as (Ho & Hol & _).
  pose proof (wr_at_store_ok rsegs m o 20 (Z.of_nat (length P)) 1 W ltac:(lia) ltac:(lia)) as HS.
  change (le1 v) with [Z_to_bv 8 (bv_unsigned v)].
  split; [apply wr_at_write; exact W|].
  split; [apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside]; left; cbn [length]; lia]|].
  split; [apply wmono_write; exact WM|].
  split; [intros HI; apply mem_inv_store; [apply MI; exact HI | exact HS]|].
  split; [intros lo hi Hs; apply stk_write; [apply SK; exact Hs | lia | cbn [length]; lia]|].
  apply bytes_at_app. split.
  - apply bytes_at_write_other; [exact BA | lia | cbn [length]; lia | left; lia].
  - apply bytes_at_write_same; cbn [length]; lia.
Qed.

Lemma dt1_head_shadow : forall m0 m o P W off j,
  dt1_head_inv m0 m o P -> sub_fp [(o, o + 20)] W ->
  asan_shadow_rd rsegs m0 off o 20 W -> asan_addressable rsegs m0 off o 20 -> 0 <= j < 20 ->
  exists k : byte, ov_read_bytes rsegs m (wa ((o + j) / 8 + off)) 1 = Some [k] /\ asan_ok k (o + j).
Proof.
  intros m0 m o P W off j (_ & MU & _) Hs HR HA Hj.
  pose proof (asan_shadow_rd_munch rsegs m0 m off o 20 W _ HR MU Hs) as HR'.
  pose proof (asan_addressable_munch rsegs m0 m off o 20 W _ HA HR MU Hs) as HA'.
  destruct (asan_shadow_read rsegs m off o 20 W j HR' Hj) as (k & RK & BK).
  exists k. split; [exact RK | exact (HA' j k Hj BK)].
Qed.

Lemma dt1_head_sub1 : forall a b c d, sub_fp [(a, b)] [(a, b); (c, d)].
Proof. intros a b c d x Hx. cbn in *. tauto. Qed.

Lemma dt1_head_sub2 : forall a b c d, sub_fp [(c, d)] [(a, b); (c, d)].
Proof. intros a b c d x Hx. cbn in *. tauto. Qed.

Lemma dt1_head_cons : forall (x y : byte) xs ys, x = y -> xs = ys -> x :: xs = y :: ys.
Proof. intros; subst; reflexivity. Qed.

Ltac dt1_head_join G r :=
  lazymatch goal with
  | |- evt _ _ (MS ?R _ _ _ _ _ _) => exact (G (reg_get R r))
  end.

Ltac dt1_head_chk j r :=
  lazymatch goal with
  | D : dt1_head_inv ?m0 ?mc ?o ?P, HS : sub_fp [(?o, ?o + 20)] ?W,
    HR : asan_shadow_rd _ ?m0 ?off _ _ _, HA : asan_addressable _ ?m0 _ _ _ |- _ =>
      let k := fresh "k" in let RK := fresh "RK" in let OK := fresh "OK" in let KR := fresh "KR" in
      let X := lazymatch j with Z0 => o | _ => constr:(o + j) end in
      destruct (dt1_head_shadow m0 mc o P W off j D HS HR HA ltac:(lia)) as (k & RK & OK);
      pose proof (rc_byte_signed k) as KR;
      rewrite ?Z.add_0_r in RK, OK;
      lazymatch j with Z0 => idtac | _ => step end;
      step;
      rewrite ?(unsigned_lit X) by lia;
      rewrite rc_shr3;
      step;
      step;
      clear RK;
      step;
      unfold sxb; rewrite (rc_eqb0_signed (bv_signed k)) by lia;
      lazymatch goal with
      | |- evt ?segs ?Q (MS ?R ?F (if _ then _ else ?B) ?fc ?rv ?m ?ro) =>
          let G := fresh "G" in
          enough (G : forall rr : word, evt segs Q (MS (bvmap_set r rr R) F B fc rv m ro));
          [ let K0 := fresh "K0" in
            destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
            [ dt1_head_join G r
            | step;
              rewrite ?(unsigned_lit X) by lia; rewrite rc_land7;
              step;
              rewrite (rc_lts_signed (X mod 8) (bv_signed k))
                by (pose proof (Z.mod_pos_bound X 8 ltac:(lia)); lia);
              replace (X mod 8 <? bv_signed k) with true
                by (symmetry; apply Z.ltb_lt; destruct OK; lia);
              dt1_head_join G r ]
          | intros ?; simp_regs; clear OK KR ]
      end
  end.

Ltac dt1_head_to_store mc :=
  step;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem mc _ _) _) => idtac
  | _ => dt1_head_to_store mc
  end.

Ltac dt1_head_st j :=
  lazymatch goal with
  | D : dt1_head_inv ?m0 ?mc ?o ?P |- _ =>
      let HS := fresh "HS" in
      first [ pose proof (dt1_head_ok0 m0 mc _ D) as HS
            | pose proof (dt1_head_ok m0 mc o P j D eq_refl ltac:(apply Nat.ltb_lt; reflexivity)) as HS ];
      dt1_head_to_store mc;
      clear HS;
      lazymatch goal with
      | |- evt _ _ (MS _ _ _ _ _ (write_to_mem mc ?A (le1 ?v)) _) =>
          let D' := fresh "D" in
          pose proof (dt1_head_store m0 mc o P A v D ltac:(apply Nat.ltb_lt; reflexivity)
                        ltac:(first [reflexivity | apply dt1_head_wa0])) as D';
          clear D;
          let mc' := fresh "mc" in
          set (mc' := write_to_mem mc A (le1 v)) in *; clearbody mc'
      end
  end.

Ltac dt1_head_bstep := step; if_false.

(* Route (C): the run proves the premise-free _on statement (dt1_head_c.v); the script is the old one with the
   unused shadow hypothesis no longer introduced. dt1_head_holds below is the old statement, one line from it. *)
Theorem dt1_head_holds_on : dt1_head_contract_on.
Proof.
  unfold dt1_head_contract_on, DT1_HEAD, DT1_HEAD_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo Ho W ST HLO HD HCE HADR HW.
  pose proof (rt_asan_rt m _ HCE HW) as HRT.
  pose proof (rt_shadow_rd m (bv_unsigned a0) 20 _ HADR (fun x Hx => HW x (or_intror (or_intror Hx)))) as HSR.
  pose proof (rt_addressable m (bv_unsigned a0) 20 HADR) as HAD.
  set (off := ASAN_K) in HRT, HSR, HAD. clearbody off.
  clear HCE HADR HW.
  pose proof (bv_unsigned_in_range 64 a0) as Ra. change (bv_modulus 64) with (2^64) in Ra.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & _ & _).
  assert (WV : forall x, bv_unsigned sp - 16 <= x < bv_unsigned sp -> wview rsegs m (wa x) <> None)
    by (intros x Hx; destruct ST as (_ & _ & H); exact (proj1 (H x ltac:(lia)))).
  carve_frame 16%nat ST.
  step. step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  pose proof (asan_rt_munch rsegs m m1 _ _ off _ _ HRT MU (dt1_head_sub1 _ _ _ _)) as HRT1.
  pose proof (asan_shadow_rd_munch rsegs m m1 off _ 20 _ _ HSR MU (dt1_head_sub1 _ _ _ _)) as HSR1.
  pose proof (asan_addressable_munch rsegs m m1 off _ 20 _ _ HAD HSR MU (dt1_head_sub1 _ _ _ _)) as HAD1.
  pose proof (dt1_head_sub2 (bv_unsigned sp + -16) (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a0 + 20)) as HSUB.
  clear HRT HSR HAD.
  pose proof (asan_rt_got_read rsegs m1 _ _ off _ HRT1) as RG.
  pose proof (asan_rt_cell_read rsegs m1 _ _ off _ HRT1) as RC.
  unfold GOT_CELL_K, CELL_K in RG, RC.
  pose proof (dt1_head_init m1 (bv_unsigned a0) W) as D.
  step. step. step.
  clear RG RC.
  dt1_head_chk 0 (Z_to_bv 5 16). dt1_head_st 0. dt1_head_bstep.
  dt1_head_chk 1 (Z_to_bv 5 17). dt1_head_st 1. dt1_head_bstep.
  dt1_head_chk 2 (Z_to_bv 5 16). dt1_head_st 2. dt1_head_bstep.
  dt1_head_chk 3 (Z_to_bv 5 16). dt1_head_st 3. dt1_head_bstep.
  dt1_head_chk 4 (Z_to_bv 5 16). dt1_head_st 4. dt1_head_bstep.
  dt1_head_chk 5 (Z_to_bv 5 16). dt1_head_st 5. dt1_head_bstep.
  dt1_head_chk 6 (Z_to_bv 5 16). dt1_head_st 6. dt1_head_bstep.
  dt1_head_chk 7 (Z_to_bv 5 16). dt1_head_st 7. dt1_head_bstep.
  dt1_head_chk 8 (Z_to_bv 5 16). dt1_head_st 8. dt1_head_bstep.
  dt1_head_chk 9 (Z_to_bv 5 14). dt1_head_st 9. dt1_head_bstep.
  dt1_head_chk 10 (Z_to_bv 5 14). dt1_head_st 10. dt1_head_bstep.
  dt1_head_chk 11 (Z_to_bv 5 14). dt1_head_st 11. dt1_head_bstep.
  dt1_head_chk 12 (Z_to_bv 5 14). dt1_head_st 12. dt1_head_bstep.
  dt1_head_chk 13 (Z_to_bv 5 14). dt1_head_st 13. dt1_head_bstep.
  dt1_head_chk 14 (Z_to_bv 5 14). dt1_head_st 14. dt1_head_bstep.
  dt1_head_chk 15 (Z_to_bv 5 14). dt1_head_st 15. dt1_head_bstep.
  dt1_head_chk 16 (Z_to_bv 5 14). dt1_head_st 16. dt1_head_bstep.
  dt1_head_chk 17 (Z_to_bv 5 14). dt1_head_st 17. dt1_head_bstep.
  dt1_head_chk 18 (Z_to_bv 5 14). dt1_head_st 18. dt1_head_bstep.
  dt1_head_chk 19 (Z_to_bv 5 12). dt1_head_st 19.
  match goal with D : dt1_head_inv _ ?mf _ _ |- _ =>
    destruct D as (W2 & MU2 & WM2 & MI2 & SK2 & BA); rename mf into m2 end.
  pose proof (rw_cells_transport rsegs _ m1 m2 _ _ FR MU2 WM2) as FR2.
  specialize (FR2 ltac:(simpl_sizes; cbn [disjoint_from]; split; [lia | exact I])).
  pose proof (SK2 _ _ ST) as ST2.
  clear FR ST. rename FR2 into FR. rename ST2 into ST.
  step. step. step.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. cbv beta. do 8 eexists. split; [reflexivity|].
  split.
  { eapply bytes_at_ext; [exact BA|].
    unfold dt1_bytes. cbn [map app].
    repeat apply dt1_head_cons;
      first [ reflexivity
            | apply Z_to_bv8_mod; rewrite unsigned_lit_wrap; rewrite mod_mod8_of_modw by lia; reflexivity ]. }
  split; [exact (munch_trans _ m m1 m2 (munch_weaken _ _ m m1 (dt1_head_sub1 _ _ _ _) MU)
                   (munch_weaken _ _ m1 m2 HSUB MU2))|].
  split; [exact (wmono_trans rsegs _ _ _ WM WM2)|].
  split; [intros HI; exact (MI2 (rc_mem_inv_frame rsegs m m1 _ _ HI MU WV)) | exact ST].
Qed.

(* The old statement, unchanged, in one line from the _on one (route (C), premise dropped): its premise shadow_rw m
   is simply forgotten, since this run never reads or stores shadow through it. *)
Theorem dt1_head_holds : dt1_head_contract.
Proof. exact (dt1_head_contract_of_on dt1_head_holds_on). Qed.
