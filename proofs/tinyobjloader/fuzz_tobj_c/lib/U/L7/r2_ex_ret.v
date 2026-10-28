From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR SymCFG SymCall.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue RingBuf RingCfg ListCommit.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L7 Require Import S_r2 r2_cuts r2_ex_base r2_ex_vals r2_ex_defs r2_ex.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import R2C R2X R2E.

(* Exit E_ret (r2_ret): the ghost lists LN/LP hold indices < n (rn_alln), so the nxt/prv objects re-read as the arrays of
   P_r2U; the ghost lists are reset to rho0's, and the leaf is P_r2U itself. *)
Definition arrN : sobj := r2_O_nxt (r2_arrK r2_N).
Definition arrP : sobj := r2_O_prv (r2_arrK r2_N).

Lemma ex_Eret : forall cuts, ex_ok cuts N_Eret.
Proof.
  intros cuts K rho0 rho HG. apply etriple_now. intros [tr [ms md]] [Hsm HK]. right.
  pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI.smatch_facts segsU _ _ _ Hsm) as HF.
  pose proof (base_n rho [] HF) as FN.
  destruct HG as (Hbase & Halln & _ & _). specialize (Halln eq_refl). destruct Halln as [AN AP].
  destruct Hbase as (B1 & B2 & B3 & Bn). unfold nval in AN, AP.
  assert (Hsm1 : smatch segsU rho (obj_upd E_ret 3 arrN) (tr, mkCfg ms md)).
  { eapply smatch_obj_upd; [reflexivity | exact Hsm | reflexivity | reflexivity |].
    intros Hrom Hwf Ho. unfold arrN, r2_O_nxt, r2_arrK.
    eapply (obj_holds_list_arr segsU rho ms r2_NXT _ LN r2_N _ _ Hrom Hwf Ho).
    - refine (soff_IX4 rho r2_N _). cbn [eval r2_N]. lia.
    - reflexivity.
    - exact AN. }
  assert (Hsm2 : smatch segsU rho (obj_upd (obj_upd E_ret 3 arrN) 4 arrP) (tr, mkCfg ms md)).
  { eapply smatch_obj_upd; [reflexivity | exact Hsm1 | reflexivity | reflexivity |].
    intros Hrom Hwf Ho. unfold arrP, r2_O_prv, r2_arrK.
    eapply (obj_holds_list_arr segsU rho ms r2_PRV _ LP r2_N _ _ Hrom Hwf Ho).
    - refine (soff_IX4 rho r2_N _). cbn [eval r2_N]. lia.
    - reflexivity.
    - exact AP. }
  change (smatch segsU rho P_r2U (tr, mkCfg ms md)) in Hsm2.
  pose proof (smatch_set_rl segsU rho LN (rl rho0 LN) P_r2U _ ltac:(vm_compute; reflexivity) Hsm2) as Hsm3.
  pose proof (smatch_set_rl segsU _ LP (rl rho0 LP) P_r2U _ ltac:(vm_compute; reflexivity) Hsm3) as Hsm4.
  set (rhof := rho_set_rl (rho_set_rl rho LN (rl rho0 LN)) LP (rl rho0 LP)) in *.
  exists (mkLeaf P_r2U RsSymJump), rhof. split; [left; reflexivity|]. split; [|split; [exact Hsm4 | exact HK]].
  split; [|split].
  - intros i Hi. rewrite B1 by exact Hi. reflexivity.
  - intros l. subst rhof. destruct (Pos.eq_dec l LP) as [->|HlP]; [rewrite rho_set_rl_at; reflexivity|].
    rewrite rho_set_rl_other by exact HlP.
    destruct (Pos.eq_dec l LN) as [->|HlN]; [rewrite rho_set_rl_at; reflexivity|].
    rewrite rho_set_rl_other by exact HlN. apply B3; assumption.
  - intros a. rewrite B2. reflexivity.
Qed.
