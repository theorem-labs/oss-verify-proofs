(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the state invariants take the launch record [LaunchX], and the argument area is read from it). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.openssl.hashtable.images Require Import AsanUbsan.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanInit.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxOfAps HBPlanImage HBAtable HBCheck0 BC1 BC1HS BC1Cert.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

Lemma ha_img_facts : img_facts HASEGS HAT HAPH.
Proof.
  constructor.
  - exact hat_if_ph.
  - exact hat_if_hull.
  - exact hat_if_top.
  - exact hat_res_hull.
  - exact hat_if_sizes.
  - exact hat_if_rw.
  - exact hat_shadow_ok.
  - split; apply Nat.leb_le; vm_compute; reflexivity.
Qed.

Section C1.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variable lim : Z.   (* [comment removed for export] *)
  Variables argv envp : list (list byte).
  Variables uid hw : word.
  Variable L : LaunchX.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk HASEGS brk0.
  Hypothesis Hlim : (AsanInit.LIMIT <= lim)%Z.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis HLX : launchL HAT sp rdraw brk0 argv envp uid hw L.
  Let fs := lx_fs L.
  #[local] Notation SINV := (SINVL HAPH sp rdraw brk0 argv envp uid hw L).
  #[local] Notation argH := (argH0 sp rdraw argv envp (lx_kb L) (lx_execfn L)).
  #[local] Notation LIM := AsanInit.LIMIT.
  Variable HOLES : nat -> env -> Fs.Fs -> TSet.
  Hypothesis HOLES_agree : forall h E E' fs0, env_agree NX0 E E' -> HOLES h E fs0 = HOLES h E' fs0.
  Hypothesis HOLES_nil : forall h E fs0, HOLES h E fs0 [].
  Hypothesis HOLES_mod : forall h E fs0, HOLES h E fs0 = HOLES (CAP.hole_cls h) E fs0.
  Hypothesis REST : holes_stmt HASEGS HAT LIM C1_HS SINV argH (bv_unsigned sp) HOLES fs.

  Theorem c1_sound :
    crz HASEGS (INITL HASEGS HAPH sp rdraw brk0 lim argv envp uid hw L)
        (sd HOLES t_nil (E0L sp rdraw brk0 argv envp uid hw L) fs c1_shape).
  Proof.
    rewrite (init_cfg_eqL HASEGS HAT HAPH sp rdraw brk0 lim argv envp uid hw L (proj1 HLX)).
    pose proof (init_cs_okL HASEGS HAT HAPH sp rdraw brk0 lim argv envp uid hw L ha_img_facts Hsp Hbrk Hlim Hva Hve Hfit Huid HLX) as HC.
    apply cxs_cs_ok_of_aps in HC.
    exact (ha0_check_sound sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit C1_HS HOLES HOLES_agree HOLES_nil HOLES_mod REST
             C1_IT C1_IT_ok 0%nat true 3000%nat 400000%nat c1_plan_r (init_acs_r (rseq_z (kb_rseq (lx_kb L))) HAT) c1_shape (c1_cert _ (rseq_z_range _)) _ _ _ _ HC).
  Qed.
End C1.
