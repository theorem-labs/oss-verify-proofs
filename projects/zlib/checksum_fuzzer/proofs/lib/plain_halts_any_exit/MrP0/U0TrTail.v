(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require PropExec StdModel ShapeAlg Spec U0TargetPre U0World U0StdioDefs U0ExitBase U0Exit.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Walk Arr SysStep ITree Nodes.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import KInv. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import KLink. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import KEv.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require MM15. Import MM15. Import MM15.ProgDeps. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require MM13. Import MM13. Import MM13.MallocBlocks.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.PlainU0 Require Import PImg RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Mr Require Import MrRulesU0.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.MrP0 Require Import U0HeapPre U0HBase U0HConv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Module OSD := OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.U0StdioDefs.
Module OEB := OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.U0ExitBase.
Module OSA := OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Module OSp := OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec.

Definition exit_ivs : list (Z * Z) :=
  [(0x1e000, 0x1ea08); (0x1ea10, 0x1fb38); (0x1fc20, 0x1fc30); (0x1fc31, 0x1fc79); (0x4fdc0, 0x4fdc8); (0x4ffe8, 0x4fff0); (0x50430, 0x50450)].


Lemma rdn_pristine {RCa1 : RunCtx}  : forall ivs (M : word -> option byte) lo hi a n,
  pristine_in ivs M -> In (lo, hi) ivs -> lo <= a -> a + Z.of_nat n <= hi -> 0 <= a < 2^64 -> hi <= 2^64 ->
  OP.rdn (run_segments Tgt_checksum_fuzzer_ubsan.M.loaded_segments rc_inp rc_sp rc_mb) M (Z_to_bv 64 a) n
  = OP.rdn (run_segments Tgt_checksum_fuzzer_ubsan.M.loaded_segments rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 a) n.
Proof.
  intros ivs M lo hi a n PR IN H1 H2 H3 H4. apply OP.rdn_ext.
  - rewrite wa_unsigned by lia. lia.
  - intros x Hx. rewrite wa_unsigned in Hx by lia. apply (pristine_word M lo hi); [intros; eapply PR; eauto | lia].
Qed.

Lemma bytes_eq_unsigned : forall l1 l2 : list byte, map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|a l1 IH]; intros [|b l2] H; try discriminate; [reflexivity|].
  cbn in H. injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

Lemma some_bytes_eq : forall (o : option (list byte)) (l : list byte),
  match o with Some l' => map bv_unsigned l' = map bv_unsigned l | None => False end -> o = Some l.
Proof. intros [l'|] l H; [f_equal; apply bytes_eq_unsigned; exact H | contradiction]. Qed.

Ltac pristine_rdn PR :=
  lazymatch goal with
  | |- OP.rdn _ ?M (Z_to_bv 64 ?a) ?n = _ =>
      first [ rewrite (rdn_pristine _ M 0x1e000 0x1ea08 a n PR) by (first [lia | cbn; tauto])
            | rewrite (rdn_pristine _ M 0x1ea10 0x1fb38 a n PR) by (first [lia | cbn; tauto])
            | rewrite (rdn_pristine _ M 0x1fc20 0x1fc30 a n PR) by (first [lia | cbn; tauto])
            | rewrite (rdn_pristine _ M 0x1fc31 0x1fc79 a n PR) by (first [lia | cbn; tauto])
            | rewrite (rdn_pristine _ M 0x4fdc0 0x4fdc8 a n PR) by (first [lia | cbn; tauto])
            | rewrite (rdn_pristine _ M 0x4ffe8 0x4fff0 a n PR) by (first [lia | cbn; tauto])
            | rewrite (rdn_pristine _ M 0x50430 0x50450 a n PR) by (first [lia | cbn; tauto]) ];
      apply some_bytes_eq; vm_compute; reflexivity
  end.

Ltac use_kept KEPT :=
  eapply (rz_kept _ _ _ _ _ _ KEPT); cbv beta zeta; simp_regs.

Ltac forget_regs R :=
  repeat match goal with |- context [reg_get R ?k] => let x := fresh "y" in set (x := reg_get R k); clearbody x end.

Section TAIL.
Context {RCa1 : RunCtx}.
Context {rc : runConstT}.
Variable sp0 : Z.
Hypothesis SP0 : 0x7fff80000000 <= sp0 <= 0x800000000000.
Hypothesis SP16 : sp0 mod 16 = 0.
Hypothesis ATOPE : ATOP = sp0 - 8388608.

Variable so_ok : (word -> option byte) -> nat -> Prop.
Hypothesis so_exit : forall M k can, so_ok M k -> OSD.ssp_cells M can ->
   (k = 0%nat /\ exists wp1 rp1, OEB.file_clean M 0x1fb38 wp1 rp1)
   \/ (exists (wb wp : Z) (bufp bufsz rp1 : word), OSD.stdout_pending M wb wp bufp bufsz rp1 can (OSp.zero_lines k)).

Lemma rerrno_lit' : errno_addr (Z_to_bv 64 RATP) = RERRNO.
Proof. unfold RATP, RERRNO. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma ssp_of_RHEAP : forall s LB M, RHEAP s LB M -> OSD.ssp_cells M CAN.
Proof.
  intros s LB M (st & LB0 & _ & _ & (_ & _ & (_ & _ & _ & G1 & G2) & _) & _).
  unfold RGOT_SSP, RSSP_GUARD in *. split.
  - destruct G1 as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
    pose proof (bytes_at_rdn (run_segments psegs rc_inp rc_sp rc_mb) M _ _ 0%nat 8%nat B ltac:(rewrite length_le8; lia)) as X.
    rewrite Z.add_0_r in X. exact X.
  - destruct G2 as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
    pose proof (bytes_at_rdn (run_segments psegs rc_inp rc_sp rc_mb) M _ _ 0%nat 8%nat B ltac:(rewrite length_le8; lia)) as X.
    rewrite Z.add_0_r in X. exact X.
Qed.

Lemma exit_rz : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (M : word -> option byte) (mo : Model) (s : PState) (LB : list block) (k : nat) (code tid lo : Z),
  x2 = wz (sp0 - 48) -> x4 = wz RATP -> x10 = wz code ->
  RHEAP s LB M -> m_halted mo = None -> m_vm_lazy mo = [] ->
  fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  (* port727 (): U0Exit's pending-stdout arm also needs the far-end reader (a write to a closed
     channel raises SIGPIPE); the callers have it from minv (Lib/Nodes minv_reader). *)
  m_channel_reader mo = true ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) M lo (sp0 - 48) -> lo <= sp0 - 48 - 144 ->
  pristine_in exit_ivs M ->
  1 <= tid <= 4194303 -> rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 0x2fcd8) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  so_ok M k ->
  OSD.atx_R M ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                            bvmap_empty (Z_to_bv 64 0x15890) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo)
           (OSA.t_emit (OSp.W 1 (OSp.zero_lines k)) (OSA.t_exit (bv_and (Z_to_bv 64 code) (Z_to_bv 64 255)) (m_fs mo))).
Proof.
  intros until lo. intros -> -> -> HH Hh Hl FD RD ST LO PR TID TIDC SO ATXR.
  apply rz_evt; [exact Hh | exact Hl |].
  step. apply evt_done.
  pose proof (ssp_of_RHEAP _ _ _ HH) as SSP.
  lazymatch goal with |- realizes _ (mkCfg (MS ?RR _ _ _ _ _ _) _) _ =>
    refine (U0Exit.ref_exit_Z RR M mo (Z_to_bv 64 code) (OSp.zero_lines k) _) end.
  exists (Z_to_bv 64 (sp0 - 48)), (Z_to_bv 64 RATP), tid, (Z_to_bv 64 0), (Z_to_bv 64 0).
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
    + pristine_rdn PR.
    + pristine_rdn PR.
    + pristine_rdn PR.
    + pristine_rdn PR.
    + pristine_rdn PR.
    + pristine_rdn PR.
    + pristine_rdn PR.
    + exists (Z_to_bv 64 0x1fa20). pristine_rdn PR.
    + right. exact ATXR.
    +
      split; [|split; [|split; [|split]]]; try pristine_rdn PR.
      destruct HH as (st & LB0 & _ & _ & (_ & _ & (_ & G & _) & _) & _). unfold RNEED_LOCKS in G.
      destruct G as [[_ B] _]. cbn [cells_bytes cbytes] in B.
      pose proof (bytes_at_rdn (run_segments psegs rc_inp rc_sp rc_mb) M _ _ 0%nat 1%nat B ltac:(cbn; lia)) as X. rewrite Z.add_0_r in X. exact X.
    +
      unfold OEB.file_clean. repeat split; pristine_rdn PR.
  - destruct (so_exit M k CAN SO SSP) as [(-> & wp1 & rp1 & FC) | (wb & wp & bufp & bufsz & rp1 & PEND)].
    + left. split; [reflexivity|]. exists wp1, rp1. exact FC.
    + right. exists wb, wp, bufp, bufsz, rp1, CAN. split; [exact PEND | exact (conj FD RD)].
Qed.

Lemma frame_ok_G_std : forall fs, frame_ok (G_std fs).
Proof.
  intros fs s s' mo mo' _ _ (E1 & _ & E3 & _) [G1 G2]. unfold G_std, m_fds, m_fs in *. rewrite E1, E3. split; assumption.
Qed.

Lemma fd1_of_G_std : forall fs s mo, G_std fs s mo -> fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
Proof. intros fs s mo [E _]. rewrite E. reflexivity. Qed.

Hypothesis so_frame : forall M M' k, so_ok M k ->
  (forall a, 0x1fb38 <= a < 0x1fc20 \/ 0x50450 <= a < 0x50858 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> so_ok M' k.

Lemma atx_R_rheap : forall LB M M', rheap_pres LB (sp0 - 128) M M' -> OSD.atx_R M -> OSD.atx_R M'.
Proof.
  intros LB M M' HP (A1 & A2 & A3 & A4 & A5 & A6 & A7).
  assert (HP0 : rheap_pres [] (sp0 - 128) M M') by (eapply rheap_pres_weaken; [exact HP | lia | intros b []]).
  assert (T : forall a n (bs : list byte), (0x4fdc8 <= a /\ a + Z.of_nat n <= 0x4ffe8) \/ (0x2fc80 <= a /\ a + Z.of_nat n <= 0x2fc88) ->
              rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 a) n = Some bs -> rdn (run_segments psegs rc_inp rc_sp rc_mb) M' (Z_to_bv 64 a) n = Some bs).
  { intros a n bs Ha H. rewrite <- H. apply (rdn_same_on (rclient_addr [] (sp0 - 128))); [apply same_on_rheap_pres; exact HP0 | | lia | lia].
    intros x Hx. unfold rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RATP, RSSP_GUARD, RGOT_SSP. right; left. lia. }
  repeat split; (apply T; [cbn; lia | assumption]).
Qed.

Lemma main_join_rz : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (M : word -> option byte) (mo : Model) (s : PState) (pb : bptr) (buf cap : Z) (fs : Fs.Fs) (k : nat) (code tid lo : Z)
    (junk : list byte) (m7 m6 m5 m4 m3 m2 m1 m0 : word) (errv : word),
  x2 = Z_to_bv 64 (sp0 - 128) -> x4 = Z_to_bv 64 RATP -> x9 = Z_to_bv 64 buf -> x8 = Z_to_bv 64 code -> code = 0 \/ code = 2 ->
  RHEAP s [(pb, buf, cap)] M -> OWN [pb] (G_std fs) s mo ->
  rauxv_ok M sp0 -> stk (run_segments psegs rc_inp rc_sp rc_mb) M lo (sp0 - 128) -> ATOP <= lo -> lo <= sp0 - 128 - 8192 ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M RERRNO [C4 errv] -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M (sp0 - 128) [CB 8 junk; C8 m7; C8 m6; C8 m5; C8 m4; C8 m3; C8 m2; C8 m1; C8 m0; C8 (Z_to_bv 64 0x15890)] ->
  pristine_in exit_ivs M ->
  1 <= tid <= 4194303 -> rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 0x2fcd8) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  so_ok M k ->
  OSD.atx_R M ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                            bvmap_empty (Z_to_bv 64 0x13f64) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo)
           (OSA.t_emit (OSp.W 1 (OSp.zero_lines k)) (OSA.t_exit (OSp.exit_code code) fs)).
Proof.
  intros until errv. intros -> -> -> -> CODE HH HOWN AUX ST ALO LO ERR MI FR PR TID TIDC SO ATXR.
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
  assert (PR' : pristine_in exit_ivs M').
  { eapply pristine_in_same_on; [exact PR | apply same_on_rheap_pres; exact HP0 |].
    intros lo' hi' a IN Ha. unfold exit_ivs in IN. cbn [In] in IN.
    unfold rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP.
    repeat (destruct IN as [IN|IN]; [injection IN as <- <-; split; [lia | right; left; lia]|]). destruct IN. }
  assert (TIDC' : rdn (run_segments psegs rc_inp rc_sp rc_mb) M' (Z_to_bv 64 0x2fcd8) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid))).
  { rewrite <- TIDC. apply (rdn_same_on (rclient_addr [] (sp0 - 128))); [apply same_on_rheap_pres; exact HP0 | | lia | lia].
    intros x Hx. unfold rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. right; left. lia. }
  assert (SO' : so_ok M' k).
  { apply (so_frame M M' k SO). intros a Ha.
    destruct (HP0 a ltac:(lia)) as [E _]; [| exact E].
    unfold rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. right; left. lia. }
  assert (ATXR' : OSD.atx_R M') by (eapply atx_R_rheap; [exact HP | exact ATXR]).
  clear HP HP0 FR PR TIDC SO ST MI ERR AUX HH HOWN HKL Hh Hl HG ATXR.
  apply rz_evt; [exact Hh' | exact Hl' |].
  do 12 step. apply evt_done.
  release_frame FR' ST' (sp0 - 48).
  replace (OSp.exit_code code) with (bv_and (Z_to_bv 64 code) (Z_to_bv 64 255))
    by (destruct CODE as [-> | ->]; apply bv_eq; reflexivity).
  rewrite <- (proj2 HG').
  eapply (exit_rz _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M' mo' s' _ k code tid lo);
    [ f_equal; lia | reflexivity | reflexivity | exact HH' | exact Hh' | exact Hl' | exact (fd1_of_G_std _ _ _ HG')
    | exact (minv_reader _ (kl_minv _ _ _ HKL'))
    | exact ST' | lia | exact PR' | exact TID | exact TIDC' | exact SO' | exact ATXR' ].
Qed.

Lemma main_tail_rz : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (M : word -> option byte) (mo : Model) (s : PState) (pb : bptr) (buf cap : Z) (fs : Fs.Fs) (k : nat) (rcv b1 tid lo : Z)
    (junk : list byte) (m7 m6 m5 m4 m3 m2 m1 m0 : word) (errv : word),
  x2 = Z_to_bv 64 (sp0 - 128) -> x4 = Z_to_bv 64 RATP -> x9 = Z_to_bv 64 buf -> x10 = Z_to_bv 64 rcv ->
  x21 = Z_to_bv 64 (if b1 <? 128 then b1 else b1 - 256 + 2 ^ 64) -> 0 <= b1 < 256 -> rcv = 0 \/ rcv = 2 ->
  RHEAP s [(pb, buf, cap)] M -> OWN [pb] (G_std fs) s mo ->
  rauxv_ok M sp0 -> stk (run_segments psegs rc_inp rc_sp rc_mb) M lo (sp0 - 128) -> ATOP <= lo -> lo <= sp0 - 128 - 8192 ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M RERRNO [C4 errv] -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M (sp0 - 128) [CB 8 junk; C8 m7; C8 m6; C8 m5; C8 m4; C8 m3; C8 m2; C8 m1; C8 m0; C8 (Z_to_bv 64 0x15890)] ->
  pristine_in exit_ivs M ->
  1 <= tid <= 4194303 -> rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 0x2fcd8) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  so_ok M k ->
  OSD.atx_R M ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                            bvmap_empty (Z_to_bv 64 0x13ee4) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo)
           (OSA.t_emit (OSp.W 1 (OSp.zero_lines k)) (OSA.t_exit (OSp.exit_code (if b1 <? 128 then rcv else 0)) fs)).
Proof.
  intros until errv. intros -> -> -> -> -> B1 RCV HH HOWN AUX ST ALO LO ERR MI FR PR TID TIDC SO ATXR.
  pose proof HOWN as [(L & _ & HKL & _) [_ HG]].
  pose proof (kl_halt _ _ _ HKL) as Hh.
  pose proof (ns_nolazy _ _ _ _ _ _ _ (nodes_sound (run_segments psegs rc_inp rc_sp rc_mb)) mo (kl_minv _ _ _ HKL)) as Hl.
  apply rz_evt; [exact Hh | exact Hl |].
  step.
  destruct (Z.ltb_spec b1 128) as [CNT|CNT].
  -
    assert (C : bv_lts (Z_to_bv 64 b1) (Z_to_bv 64 0) = false)
      by (rewrite bv_lts_zero_r, unsigned_lit by lia; apply Z.leb_gt; lia).
    rewrite C; cbv iota.
    do 2 step. apply evt_done.
    eapply (main_join_rz _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M mo s pb buf cap fs k rcv tid lo);
      try eassumption; reflexivity.
  -
    assert (C : bv_lts (Z_to_bv 64 (b1 - 256 + 2 ^ 64)) (Z_to_bv 64 0) = true)
      by (rewrite bv_lts_zero_r, unsigned_lit by lia; apply Z.leb_le; lia).
    rewrite C; cbv iota.
    do 6 step. if_true. apply evt_done.
    eapply (main_join_rz _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M mo s pb buf cap fs k 0 tid lo);
      try eassumption; try reflexivity. left; reflexivity.
Qed.

End TAIL.
