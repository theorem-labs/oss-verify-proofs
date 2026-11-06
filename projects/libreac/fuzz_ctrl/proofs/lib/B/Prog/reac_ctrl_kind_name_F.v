From Stdlib Require Import String ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes Image ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcKind RcKindLib RcLeafLib RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT reac_ctrl_kind_name_c reac_ctrl_kind_name.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* route (C): the proof below, formerly reac_ctrl_kind_name_holds_F's, proves the region form
   reac_ctrl_kind_name_contract_F_on (reac_ctrl_kind_name_c.v); reac_ctrl_kind_name_holds_F follows from it. *)
Theorem reac_ctrl_kind_name_holds_F_on : reac_ctrl_kind_name_contract_F_on.
Proof.
  unfold reac_ctrl_kind_name_contract_F_on, REAC_CTRL_KIND_NAME, REAC_CTRL_KIND_NAME_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    HT HS ST HLO HKT HCE HADR HW RIMG RSTK RSH.
  change (shadow_addr KIND_NAME) with 2147532464 in RSH.
  pose proof (rt_asan_rt m _ HCE HW) as HRT.
  pose proof (rt_shadow_rd m KIND_NAME 112 _ HADR (fun x Hx => HW x (or_intror (or_intror Hx)))) as HSR.
  pose proof (rt_addressable m KIND_NAME 112 HADR) as HAD.
  pose proof (rt_rt3 m KIND_NAME 112 HADR) as H3.
  set (off := ASAN_K) in HRT, HSR, HAD, H3.
  assert (Hoff : off = 2147450880) by reflexivity.
  clearbody off.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & _ & _).
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (WVS : forall x, bv_unsigned sp - 16 <= x < bv_unsigned sp -> wview rsegs m (wa x) <> None)
    by (intros x Hx; apply (rc_wv_stk rsegs m lo (bv_unsigned sp)); [exact ST | lia]).
  assert (HSa : bytes_at rsegs m (kind_name_addr (bv_unsigned a0)) (cstr_bytes (kind_name (bv_unsigned a0))))
    by exact (HS (bv_unsigned a0) (proj1 (bv_unsigned_in_range 64 a0))).
  pose proof (kn_str_below (bv_unsigned a0) (proj1 (bv_unsigned_in_range 64 a0))) as HBL.
  pose proof kn_bytes_length as HTL.
  carve_frame 16%nat ST.
  step. step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  pose proof (asan_rt_munch rsegs m m1 _ _ off _ _ HRT MU (fun x Hx => Hx)) as HRT1.
  pose proof (asan_shadow_rd_munch rsegs m m1 off KIND_NAME 112 _ _ HSR MU (fun x Hx => Hx)) as HSR1.
  pose proof (asan_addressable_munch rsegs m m1 off KIND_NAME 112 _ _ HAD HSR MU (fun x Hx => Hx)) as HAD1.
  pose proof (asan_rt3_munch rsegs m m1 off KIND_NAME 112 _ _ H3 HSR MU (fun x Hx => Hx)) as H31.
  pose proof (asan_rt_got_read rsegs m1 _ _ off _ HRT1) as RG.
  pose proof (asan_rt_cell_read rsegs m1 _ _ off _ HRT1) as RC.
  unfold GOT_CELL_K, CELL_K in RG, RC.
  tab_entry m1 HT 0. tab_entry m1 HT 1. tab_entry m1 HT 2. tab_entry m1 HT 3. tab_entry m1 HT 4.
  tab_entry m1 HT 5. tab_entry m1 HT 6. tab_entry m1 HT 7. tab_entry m1 HT 8. tab_entry m1 HT 9.
  tab_entry m1 HT 10. tab_entry m1 HT 11. tab_entry m1 HT 12. tab_entry m1 HT 13.
  sh_entry m1 off HSR1 HAD1 H31 0. sh_entry m1 off HSR1 HAD1 H31 1. sh_entry m1 off HSR1 HAD1 H31 2.
  sh_entry m1 off HSR1 HAD1 H31 3. sh_entry m1 off HSR1 HAD1 H31 4. sh_entry m1 off HSR1 HAD1 H31 5.
  sh_entry m1 off HSR1 HAD1 H31 6. sh_entry m1 off HSR1 HAD1 H31 7. sh_entry m1 off HSR1 HAD1 H31 8.
  sh_entry m1 off HSR1 HAD1 H31 9. sh_entry m1 off HSR1 HAD1 H31 10. sh_entry m1 off HSR1 HAD1 H31 11.
  sh_entry m1 off HSR1 HAD1 H31 12. sh_entry m1 off HSR1 HAD1 H31 13.
  step. step.
  if_cases E; zify_cond E.
  - destruct (rc_word_le13 a0 ltac:(lia)) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| -> ]]]]]]]]]]]]].
    all: do 5 step; if_false; do 9 step; if_false; do 4 step.
    all: release_frame FR ST (bv_unsigned sp).
    all: apply evtF_done; cbv beta; do 4 eexists; split; [reflexivity|].
    all: split; [exact MU|]; split; [exact WM|].
    all: split; [intros HI; exact (rc_mem_inv_frame rsegs m m1 _ _ HI MU WVS)|].
    all: split; [exact ST | exact HSa].
  - do 6 step.
    release_frame FR ST (bv_unsigned sp).
    apply evtF_done. cbv beta. do 4 eexists. split.
    { rewrite (kn_addr_big (bv_unsigned a0)) by lia. reflexivity. }
    split; [exact MU|]. split; [exact WM|].
    split; [intros HI; exact (rc_mem_inv_frame rsegs m m1 _ _ HI MU WVS)|].
    split; [exact ST | exact HSa].
Qed.

Theorem reac_ctrl_kind_name_holds_F : reac_ctrl_kind_name_contract_F.
Proof. exact (reac_ctrl_kind_name_contract_F_of_on reac_ctrl_kind_name_holds_F_on). Qed.
