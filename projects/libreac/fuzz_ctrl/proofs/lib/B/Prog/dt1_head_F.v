From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcRec RcLib RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT dt1_head_c dt1_head.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Local Ltac dt1_head_accF :=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
      lazymatch E with
      | context [Z.div _ _] =>
          let nz := eval cbv in (Z.of_nat n) in
          match goal with
          | H : rng RNG ?lo ?len |- _ =>
              lazymatch lo with
              | context [Z.div _ _] =>
                  apply (rng_acc_litZ' RNG lo len E n nz H (@eq_refl Z nz) (@eq_refl bool true));
                  unfold shadow_addr, ASAN_K in *;
                  try (match goal with HK : _ = 2147450880 |- _ => rewrite HK end);
                  Z.div_mod_to_equations; lia
              end
          end
      end
  end.

Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.acc_hint ::= dt1_head_accF.

Local Ltac dt1_head_storeF :=
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => norm_lit_store_bytes; mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end.

Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.mem_after_store_opt ::= dt1_head_storeF.

Ltac dt1_head_joinF G r :=
  lazymatch goal with
  | |- evtF _ _ _ (MS ?R _ _ _ _ _ _) => exact (G (reg_get R r))
  end.

Ltac dt1_head_chkF j r :=
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
      | |- evtF ?segs ?RNG ?Q (MS ?R ?F (if _ then _ else ?B) ?fc ?rv ?m ?ro) =>
          let G := fresh "G" in
          enough (G : forall rr : word, evtF segs RNG Q (MS (bvmap_set r rr R) F B fc rv m ro));
          [ let K0 := fresh "K0" in
            destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
            [ dt1_head_joinF G r
            | step;
              rewrite ?(unsigned_lit X) by lia; rewrite rc_land7;
              step;
              rewrite (rc_lts_signed (X mod 8) (bv_signed k))
                by (pose proof (Z.mod_pos_bound X 8 ltac:(lia)); lia);
              replace (X mod 8 <? bv_signed k) with true
                by (symmetry; apply Z.ltb_lt; destruct OK; lia);
              dt1_head_joinF G r ]
          | intros ?; simp_regs; clear OK KR ]
      end
  end.

Ltac dt1_head_to_storeF mc :=
  step;
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem mc _ _) _) => idtac
  | _ => dt1_head_to_storeF mc
  end.

Ltac dt1_head_stF j :=
  lazymatch goal with
  | D : dt1_head_inv ?m0 ?mc ?o ?P |- _ =>
      let HS := fresh "HS" in
      first [ pose proof (dt1_head_ok0 m0 mc _ D) as HS
            | pose proof (dt1_head_ok m0 mc o P j D eq_refl ltac:(apply Nat.ltb_lt; reflexivity)) as HS ];
      dt1_head_to_storeF mc;
      clear HS;
      lazymatch goal with
      | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem mc ?A (le1 ?v)) _) =>
          let D' := fresh "D" in
          pose proof (dt1_head_store m0 mc o P A v D ltac:(apply Nat.ltb_lt; reflexivity)
                        ltac:(first [reflexivity | apply dt1_head_wa0])) as D';
          clear D;
          let mc' := fresh "mc" in
          set (mc' := write_to_mem mc A (le1 v)) in *; clearbody mc'
      end
  end.

Ltac dt1_head_bstepF := step; if_false.

(* Route (C): the run proves the premise-free _on statement (dt1_head_c.v); the script is the old one with the
   unused shadow hypothesis no longer introduced. dt1_head_holds_F below is the old statement, one line from it. *)
Theorem dt1_head_F_holds_on : dt1_head_contract_F_on.
Proof.
  unfold dt1_head_contract_F_on, DT1_HEAD, DT1_HEAD_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo Ho W ST HLO HD HCE HADR HW RSTK RRT RA0 RSH.
  (* the runtime words as literal bounds, the form StepF's access solver matches for the GOT-cell and cell loads *)
  unfold RT_LO, RT_HI in RRT.
  pose proof (rt_asan_rt m _ HCE HW) as HRT.
  pose proof (rt_shadow_rd m (bv_unsigned a0) 20 _ HADR (fun x Hx => HW x (or_intror (or_intror Hx)))) as HSR.
  pose proof (rt_addressable m (bv_unsigned a0) 20 HADR) as HAD.
  set (off := ASAN_K) in HRT, HSR, HAD.
  assert (Hoff : off = 2147450880) by reflexivity.
  clearbody off.
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
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
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
  dt1_head_chkF 0 (Z_to_bv 5 16). dt1_head_stF 0. dt1_head_bstepF.
  dt1_head_chkF 1 (Z_to_bv 5 17). dt1_head_stF 1. dt1_head_bstepF.
  dt1_head_chkF 2 (Z_to_bv 5 16). dt1_head_stF 2. dt1_head_bstepF.
  dt1_head_chkF 3 (Z_to_bv 5 16). dt1_head_stF 3. dt1_head_bstepF.
  dt1_head_chkF 4 (Z_to_bv 5 16). dt1_head_stF 4. dt1_head_bstepF.
  dt1_head_chkF 5 (Z_to_bv 5 16). dt1_head_stF 5. dt1_head_bstepF.
  dt1_head_chkF 6 (Z_to_bv 5 16). dt1_head_stF 6. dt1_head_bstepF.
  dt1_head_chkF 7 (Z_to_bv 5 16). dt1_head_stF 7. dt1_head_bstepF.
  dt1_head_chkF 8 (Z_to_bv 5 16). dt1_head_stF 8. dt1_head_bstepF.
  dt1_head_chkF 9 (Z_to_bv 5 14). dt1_head_stF 9. dt1_head_bstepF.
  dt1_head_chkF 10 (Z_to_bv 5 14). dt1_head_stF 10. dt1_head_bstepF.
  dt1_head_chkF 11 (Z_to_bv 5 14). dt1_head_stF 11. dt1_head_bstepF.
  dt1_head_chkF 12 (Z_to_bv 5 14). dt1_head_stF 12. dt1_head_bstepF.
  dt1_head_chkF 13 (Z_to_bv 5 14). dt1_head_stF 13. dt1_head_bstepF.
  dt1_head_chkF 14 (Z_to_bv 5 14). dt1_head_stF 14. dt1_head_bstepF.
  dt1_head_chkF 15 (Z_to_bv 5 14). dt1_head_stF 15. dt1_head_bstepF.
  dt1_head_chkF 16 (Z_to_bv 5 14). dt1_head_stF 16. dt1_head_bstepF.
  dt1_head_chkF 17 (Z_to_bv 5 14). dt1_head_stF 17. dt1_head_bstepF.
  dt1_head_chkF 18 (Z_to_bv 5 14). dt1_head_stF 18. dt1_head_bstepF.
  dt1_head_chkF 19 (Z_to_bv 5 12). dt1_head_stF 19.
  match goal with D : dt1_head_inv _ ?mf _ _ |- _ =>
    destruct D as (W2 & MU2 & WM2 & MI2 & SK2 & BA); rename mf into m2 end.
  pose proof (rw_cells_transport rsegs _ m1 m2 _ _ FR MU2 WM2) as FR2.
  specialize (FR2 ltac:(simpl_sizes; cbn [disjoint_from]; split; [lia | exact I])).
  pose proof (SK2 _ _ ST) as ST2.
  clear FR ST. rename FR2 into FR. rename ST2 into ST.
  step. step. step.
  release_frame FR ST (bv_unsigned sp).
  apply evtF_done. cbv beta. do 8 eexists. split; [reflexivity|].
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

(* The old footprint statement, unchanged, in one line from the _on one (route (C), premise dropped): its premise
   shadow_rw m is simply forgotten, since this run never reads or stores shadow through it. *)
Theorem dt1_head_holds_F : dt1_head_contract_F.
Proof. exact (dt1_head_contract_F_of_on dt1_head_F_holds_on). Qed.
