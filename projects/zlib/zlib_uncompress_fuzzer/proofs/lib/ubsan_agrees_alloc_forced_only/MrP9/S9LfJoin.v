(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require PropExec StdModel ShapeAlg Spec S9TargetPre S9World S9StdioDefs S9ExitBase S9Exit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Walk Arr SysStep ITree Nodes.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KInv. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KLink. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KEv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.ProgDeps. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM13. Import MM13. Import MM13.MallocBlocks.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.PlainS9 Require Import PImg RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Mr Require Import MrRulesS9.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.MrP9 Require Import S9HeapPre S9HBase S9HConv S9TrTail.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition exit_ivs2 : list (Z * Z) :=
  [(0x21000, 0x21be8); (0x21bf0, 0x22c28); (0x22d10, 0x22d18); (0x22e00, 0x22e10); (0x22e11, 0x22e59); (0x92fa0, 0x931c8);
   (0x93608, 0x93628)].

Ltac pristine_rdn2 PR :=
  lazymatch goal with
  | |- OP.rdn _ ?M (Z_to_bv 64 ?a) ?n = _ =>
      first [ rewrite (rdn_pristine _ M 0x21000 0x21be8 a n PR) by (first [lia | clear; cbn; tauto])
            | rewrite (rdn_pristine _ M 0x21bf0 0x22c28 a n PR) by (first [lia | clear; cbn; tauto])
            | rewrite (rdn_pristine _ M 0x22d10 0x22d18 a n PR) by (first [lia | clear; cbn; tauto])
            | rewrite (rdn_pristine _ M 0x22e00 0x22e10 a n PR) by (first [lia | clear; cbn; tauto])
            | rewrite (rdn_pristine _ M 0x22e11 0x22e59 a n PR) by (first [lia | clear; cbn; tauto])
            | rewrite (rdn_pristine _ M 0x92fa0 0x931c8 a n PR) by (first [lia | clear; cbn; tauto])
            | rewrite (rdn_pristine _ M 0x93608 0x93628 a n PR) by (first [lia | clear; cbn; tauto]) ];
      apply some_bytes_eq; vm_compute; reflexivity
  end.


Section JOIN.
Context {RCa1 : RunCtx}.
Context {rc : runConstT}.
Variable sp0 : Z.
Hypothesis SP0 : 0x7fff80000000 <= sp0 <= 0x800000000000.
Hypothesis SP16 : sp0 mod 16 = 0.
Hypothesis ATOPE : ATOP = sp0 - 8388608.

Variable so_ok : (word -> option byte) -> nat -> Prop.
Hypothesis so_exit : forall M k can, so_ok M k -> OSD.ssp_cells M can ->
   (k = 0%nat /\ exists wp1 rp1, OEB.file_clean M 0x22d18 wp1 rp1)
   \/ (exists (wb wp : Z) (bufp bufsz rp1 : word), OSD.stdout_pending M wb wp bufp bufsz rp1 can (OSp.zero_lines k)).
Hypothesis so_frame : forall M M' k, so_ok M k ->
  (forall a, 0x22d18 <= a < 0x22e00 \/ 0x93628 <= a < 0x93a30 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> so_ok M' k.

Lemma exit_rz_g : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (M : word -> option byte) (mo : Model) (s : PState) (LB : list block) (k : nat) (code tid lo : Z) (wp2 rp2 : word),
  x2 = wz (sp0 - 48) -> x4 = wz RATP -> x10 = wz code ->
  RHEAP s LB M -> m_halted mo = None -> m_vm_lazy mo = [] ->
  fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  m_channel_reader mo = true ->   (* as S0TrTail.exit_rz *)
  stk (run_segments psegs rc_inp rc_sp rc_mb) M lo (sp0 - 48) -> lo <= sp0 - 48 - 144 ->
  pristine_in exit_ivs2 M -> OEB.file_clean M 0x22c28 wp2 rp2 ->
  1 <= tid <= 4194303 -> rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 0x72eb8) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  so_ok M k ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                            bvmap_empty (Z_to_bv 64 0x18c08) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo)
           (OSA.t_emit (OSp.W 1 (OSp.zero_lines k)) (OSA.t_exit (bv_and (Z_to_bv 64 code) (Z_to_bv 64 255)) (m_fs mo))).
Proof.
  intros until rp2. intros -> -> -> HH Hh Hl FD RD ST LO PR ERRF TID TIDC SO.
  apply rz_evt; [exact Hh | exact Hl |].
  step. apply evt_done.
  pose proof (ssp_of_RHEAP _ _ _ HH) as SSP.
  lazymatch goal with |- realizes _ (mkCfg (MS ?RR _ _ _ _ _ _) _) _ =>
    refine (S9Exit.ref_exit_Z RR M mo (Z_to_bv 64 code) (OSp.zero_lines k) _) end.
  exists (Z_to_bv 64 (sp0 - 48)), (Z_to_bv 64 RATP), tid, wp2, rp2.
  assert (USP : bv_unsigned (Z_to_bv 64 (sp0 - 48)) = sp0 - 48) by (apply wa_unsigned; lia).
  split; [|split; [exact Hh|split; [exact Hl|]]].
  - constructor; try reflexivity.
    + rewrite USP. lia.
    + rewrite USP. lia.
    + rewrite USP. apply (store_ok_of_stk M lo (sp0 - 48)); [exact ST | lia | lia].
    + unfold RATP. rewrite wa_unsigned by lia. lia.
    + unfold RATP. rewrite wa_unsigned by lia. lia.
    + lia.
    + unfold RATP. rewrite wa_unsigned by lia. exact TIDC.
    + pristine_rdn2 PR.
    + pristine_rdn2 PR.
    + pristine_rdn2 PR.
    + pristine_rdn2 PR.
    + pristine_rdn2 PR.
    + pristine_rdn2 PR.
    + pristine_rdn2 PR.
    + exists (Z_to_bv 64 0x22c00). pristine_rdn2 PR.
    + left. split; pristine_rdn2 PR.
    +
      split; [|split; [|split; [|split]]]; try pristine_rdn2 PR.
      destruct HH as (st & LB0 & _ & _ & (_ & _ & (_ & G & _) & _) & _). unfold RNEED_LOCKS in G.
      destruct G as [[_ B] _]. cbn [cells_bytes cbytes] in B.
      pose proof (bytes_at_rdn (run_segments psegs rc_inp rc_sp rc_mb) M _ _ 0%nat 1%nat B ltac:(cbn; lia)) as X. rewrite Z.add_0_r in X. exact X.
    +
      exact ERRF.
  - destruct (so_exit M k CAN SO SSP) as [(-> & wp1 & rp1 & FC) | (wb & wp & bufp & bufsz & rp1 & PEND)].
    + left. split; [reflexivity|]. exists wp1, rp1. exact FC.
    + right. exists wb, wp, bufp, bufsz, rp1, CAN. split; [exact PEND | exact (conj FD RD)].
Qed.

Lemma file_clean_stderr_heap : forall LB SP M M' (wp rp : word),
  OEB.file_clean M 0x22c28 wp rp -> rheap_pres LB SP M M' -> OEB.file_clean M' 0x22c28 wp rp.
Proof.
  intros LB SP M M' wp rp (F1 & F2 & F3 & F4 & F5) HP.
  assert (T : forall a n, 0x22c28 <= a -> a + Z.of_nat n <= 0x22d10 ->
            OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M' (Z_to_bv 64 a) n = OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 a) n).
  { intros a n A1 A2. apply (rdn_same_on (rclient_addr LB SP)); [apply same_on_rheap_pres; exact HP | | lia | lia].
    intros x Hx. unfold rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. right; left. lia. }
  unfold OEB.file_clean. repeat split.
  - rewrite <- F1. apply T; cbn; lia.
  - rewrite <- F2. apply T; cbn; lia.
  - rewrite <- F3. apply T; cbn; lia.
  - rewrite <- F4. apply T; cbn; lia.
  - rewrite <- F5. apply T; cbn; lia.
Qed.

Lemma main_join_rz_g : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (M : word -> option byte) (mo : Model) (s : PState) (pb : bptr) (buf cap : Z) (fs : Fs.Fs) (k : nat) (code tid lo : Z)
    (junk : list byte) (m7 m6 m5 m4 m3 m2 m1 m0 : word) (errv : word) (wp2 rp2 : word),
  x2 = Z_to_bv 64 (sp0 - 128) -> x4 = Z_to_bv 64 RATP -> x9 = Z_to_bv 64 buf -> x8 = Z_to_bv 64 code -> code = 0 \/ code = 2 ->
  RHEAP s [(pb, buf, cap)] M -> OWN [pb] (G_std fs) s mo ->
  rauxv_ok M sp0 -> stk (run_segments psegs rc_inp rc_sp rc_mb) M lo (sp0 - 128) -> ATOP <= lo -> lo <= sp0 - 128 - 8192 ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M RERRNO [C4 errv] -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M (sp0 - 128) [CB 8 junk; C8 m7; C8 m6; C8 m5; C8 m4; C8 m3; C8 m2; C8 m1; C8 m0; C8 (Z_to_bv 64 0x18c08)] ->
  pristine_in exit_ivs2 M -> OEB.file_clean M 0x22c28 wp2 rp2 ->
  1 <= tid <= 4194303 -> rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 0x72eb8) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  so_ok M k ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                            bvmap_empty (Z_to_bv 64 0x14ac0) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo)
           (OSA.t_emit (OSp.W 1 (OSp.zero_lines k)) (OSA.t_exit (OSp.exit_code code) fs)).
Proof.
  intros until rp2. intros -> -> -> -> CODE HH HOWN AUX ST ALO LO ERR MI FR PR ERRF TID TIDC SO.
  pose proof HOWN as [(L & _ & HKL & _) [_ HG]].
  pose proof (kl_halt _ _ _ HKL) as Hh.
  pose proof (ns_nolazy _ _ _ _ _ _ _ (nodes_sound (run_segments psegs rc_inp rc_sp rc_mb)) mo (kl_minv _ _ _ HKL)) as Hl.
  apply rz_evt; [exact Hh | exact Hl |].
  do 2 step. apply evt_done.
  lazymatch goal with |- realizes _ (mkCfg (MS ?RR _ _ _ _ _ _) _) _ =>
    eapply (free_rz_any RR M mo s [(pb, buf, cap)] [] (G_std fs) pb buf cap lo sp0 errv) end.
  1: exact HH. 1: left; reflexivity. 1: exact HOWN. 1: apply frame_ok_G_std. 1: exact AUX.
  1: simp_regs; rewrite unsigned_lit by lia; lia.
  1: simp_regs; rewrite unsigned_lit by lia; exact ST.
  1: exact ALO.
  1: simp_regs; rewrite unsigned_lit by lia; unfold RFREE_STACK; lia.
  1: simp_regs; rewrite rerrno_lit'; exact ERR.
  1: exact MI. 1: simp_regs; reflexivity. 1: simp_regs; reflexivity.
  intros R' M' mo' s' KEPT MI' ST' ERR' AUX' HP _ _ HH' HOWN'.
  use_kept KEPT. forget_regs R'. clear KEPT.
  revert HP ST'. simp_regs. rewrite !unsigned_lit by lia. intros HP ST'.
  rewrite ret_pc_even by (first [lia | reflexivity]).
  assert (HP0 : rheap_pres [] (sp0 - 128) M M') by (eapply rheap_pres_weaken; [exact HP | lia | intros b []]).
  pose proof (rheap_pres_rw_cells _ _ _ _ _ _ HP0 FR ltac:(left; lia)) as FR'.
  pose proof HOWN' as [(L' & _ & HKL' & _) [_ HG']].
  pose proof (kl_halt _ _ _ HKL') as Hh'.
  pose proof (ns_nolazy _ _ _ _ _ _ _ (nodes_sound (run_segments psegs rc_inp rc_sp rc_mb)) mo' (kl_minv _ _ _ HKL')) as Hl'.
  assert (PR' : pristine_in exit_ivs2 M').
  { eapply pristine_in_same_on; [exact PR | apply same_on_rheap_pres; exact HP0 |].
    intros lo' hi' a IN Ha. unfold exit_ivs2 in IN. cbn [In] in IN.
    unfold rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP.
    repeat (destruct IN as [IN|IN]; [injection IN as <- <-; split; [lia | right; left; lia]|]). destruct IN. }
  pose proof (file_clean_stderr_heap _ _ _ _ _ _ ERRF HP0) as ERRF'.
  assert (TIDC' : rdn (run_segments psegs rc_inp rc_sp rc_mb) M' (Z_to_bv 64 0x72eb8) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid))).
  { rewrite <- TIDC. apply (rdn_same_on (rclient_addr [] (sp0 - 128))); [apply same_on_rheap_pres; exact HP0 | | lia | lia].
    intros x Hx. unfold rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. right; left. lia. }
  assert (SO' : so_ok M' k).
  { apply (so_frame M M' k SO). intros a Ha.
    destruct (HP0 a ltac:(lia)) as [E _]; [| exact E].
    unfold rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. right; left. lia. }
  clear HP HP0 FR PR TIDC SO ST MI ERR AUX HH HOWN HKL Hh Hl HG ERRF.
  apply rz_evt; [exact Hh' | exact Hl' |].
  do 12 step. apply evt_done.
  release_frame FR' ST' (sp0 - 48).
  replace (OSp.exit_code code) with (bv_and (Z_to_bv 64 code) (Z_to_bv 64 255))
    by (destruct CODE as [-> | ->]; apply bv_eq; reflexivity).
  rewrite <- (proj2 HG').
  eapply (exit_rz_g _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M' mo' s' _ k code tid lo wp2 rp2);
    [ f_equal; lia | reflexivity | reflexivity | exact HH' | exact Hh' | exact Hl' | exact (fd1_of_G_std _ _ _ HG')
    | exact (minv_reader _ (kl_minv _ _ _ HKL'))
    | exact ST' | lia | exact PR' | exact ERRF' | exact TID | exact TIDC' | exact SO' ].
Qed.

End JOIN.
