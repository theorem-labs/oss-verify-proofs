(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import PropExec Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface Malloc_ifaceP ClientOwn LhRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP
     RF_malloc_spec RF_free_spec RF_impl_spec RF_aligned_spec RF_realloc_spec.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun KStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import InitMem. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Startup Fz_iface Driver_iface Drv_kit Fz_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_mutex. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit
     Fz_M_malloc Fz_M_zalloc Fz_M_calloc Fz_M_free Fz_M_secure Fz_M_clear_free Fz_M_clear_realloc Fz_M_realloc Fz_M_aligned
     Fz_T_sa Fz_T_lock_new Fz_T_sk Fz_T_slx Fz_T_its Fz_I1_defs Fz_I1_new Fz_I1_double Fz_I1_insert1 Fz_I1_load Fz_I1_errload Fz_I1_first Fz_I1_efirst Fz_I1_crypto
     Fz_I3_base Fz_I3_ibase Fz_I3_shelve Fz_I3_loadstr Fz_I3_full Fz_I3_fxi Fz_G_OSSL_ERR_STATE_new Fz_I3_egsi Fz_I3_eciter Fz_I3_eclear Fz_I3_glue Fz_I3_top
     Fz_I2_ppi Fz_K_skstmt Fz_K_sk Fz_I2_ppi2 Fz_I2_pstring2 Fz_G_ctxinit_abs
     Fz_W1_defs Fz_W1_writec Fz_W3_iface Fz_W2_rep Fz_W2_exd Fz_W2_gets Fz_W2_puts Fz_W2_read Fz_W2_write Fz_W2_writeg Fz_W2_ctrl Fz_W2_bnew Fz_W2_bfree
     Fz_W3_pmem Fz_W3_sanitize Fz_W3_evp Fz_W3_defs Fz_W3_end Fz_W3_top
     Fz_W5_defs Fz_W5_env Fz_W5_newc Fz_W5_debugc Fz_W5_error Fz_W5_clearc.
     From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_W7_perm. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_W7_defs Fz_W7_top.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pem_cli0 (m : mem) : Prop :=
     (forall a : word, 0x2c0000 <= bv_unsigned a < 0x353000 -> rin_ivs LXW_CLIENT (bv_unsigned a) -> ~ (0x3308d0 <= bv_unsigned a < 0x330918) -> m a = None)
  /\ rw_cells usegs m (RATP + -150) [C1 (Z_to_bv 8 0)] /\ rw_cells usegs m (RATP + -96) [C8 z64; C8 z64].

(* [comment removed for export] *)
Definition pem_cli (m : mem) (CLB : list block) : Prop :=
  exists (pe : bptr) (E : Z) (LBL : list block),
       In (pe, E, 904) CLB /\ ~ In pe (map blk_id LBL) /\ incl_blocks LBL CLB
    /\ libenv m LBL E /\ errst_at_rest E [] m /\ rw_cells usegs m LX_BASE_INITED [C1 (Z_to_bv 8 1)].

(* [comment removed for export] *)
Lemma libenv_static_client : forall a, libenv_static a -> rin_ivs LXW_CLIENT a.
Proof.
  intros a H. unfold libenv_static, IC_S, TH_ONCE, TH_KEY, RMallocRep.RATP, TSD_MAIN, DC_S, DC_GLOBAL_LOCK, DC_IP12 in H.
  unfold LXW_CLIENT, LXW_BASEINIT, LXW_LIBCRYPTO, LXW_PSELF, LXW_PKEYS, LXW_MREPL, LXW_DKEY. cbn [rin_ivs fst snd]. lia.
Qed.

Lemma pem_cli0_stable : forall m m', pem_cli0 m ->
  (forall a, 0 <= a < 2 ^ 64 -> rin_ivs LXW_CLIENT a -> m' (wa a) = m (wa a) /\ (wview usegs m (wa a) <> None -> wview usegs m' (wa a) <> None)) ->
  pem_cli0 m'.
Proof.
  intros m m' (NONE & U & PCB) AG. split; [| split].
  - intros a Ha Hw Hp. pose proof (bv_unsigned_in_range _ a) as AR. change (bv_modulus 64) with (2 ^ 64) in AR.
    destruct (AG (bv_unsigned a) AR Hw) as [E _]. rewrite wa_unsigned_id in E. rewrite E. exact (NONE a Ha Hw Hp).
  - eapply rw_cells_agree; [exact AG| exact U|]. intros a Ha. unfold RMallocRep.RATP in Ha. cbn [cells_size csize Nat.add] in Ha.
    unfold LXW_CLIENT, LXW_BASEINIT, LXW_LIBCRYPTO, LXW_PSELF, LXW_PKEYS, LXW_MREPL, LXW_DKEY. cbn [rin_ivs fst snd]. lia.
  - eapply rw_cells_agree; [exact AG| exact PCB|]. intros a Ha. unfold RMallocRep.RATP in Ha. cbn [cells_size csize Nat.add] in Ha.
    unfold LXW_CLIENT, LXW_BASEINIT, LXW_LIBCRYPTO, LXW_PSELF, LXW_PKEYS, LXW_MREPL, LXW_DKEY. cbn [rin_ivs fst snd]. lia.
Qed.

Lemma pem_cli_stable : forall m m' CLB, pem_cli m CLB ->
  (forall a, 0 <= a < 2 ^ 64 -> cli_fp CLB a -> m' (wa a) = m (wa a) /\ (wview usegs m (wa a) <> None -> wview usegs m' (wa a) <> None)) ->
  pem_cli m' CLB.
Proof.
  intros m m' CLB (pe & E & LBL & INE & NPE & INCL & LE & ER & BI) AG. exists pe, E, LBL.
  split; [exact INE|]. split; [exact NPE|]. split; [exact INCL|].
  split. { eapply libenv_agree; [exact LE|]. eapply agree_on_mono; [exact AG|]. intros a [Ha|(b & Hb & Rb)].
           - right. exact (libenv_static_client a Ha).
           - left. exists b. split; [exact (INCL b Hb)| exact Rb]. }
  split. { eapply errst_rest_agree; [exact ER|]. eapply agree_on_mono; [exact AG|]. intros a Ha. destruct (errst_fp_where _ _ _ Ha) as [Ra|(b & [] & _)].
           left. exists (pe, E, 904). split; [exact INE| unfold blk_addr, blk_size; cbn [fst snd]; exact Ra]. }
  eapply rw_cells_agree; [exact AG| exact BI|]. intros a Ha. unfold LX_BASE_INITED in Ha. cbn [cells_size csize Nat.add] in Ha.
  right. unfold LXW_CLIENT, LXW_BASEINIT. cbn [rin_ivs fst snd]. lia.
Qed.

(* [comment removed for export] *)
Ltac pem_img NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  let nbs := eval vm_compute in (Z.of_nat (length bs)) in
  assert (H : rw_cells usegs m A cs);
  [ apply (rw_cells_recast usegs m A [CB (length bs) bs] cs);
    [ apply (rw_cells_image0 usegs m A bs);
      [ intros a Ha; apply NONE; change (Z.of_nat (length bs)) with nbs in Ha; unfold IC_S, DC_S, DC_CTX, ERR_ONCE_CELL in Ha;
        [ clear - Ha; lia
        | unfold LXW_CLIENT, LXW_BASEINIT, LXW_LIBCRYPTO, LXW_PSELF, LXW_PKEYS, LXW_MREPL, LXW_DKEY; cbn [rin_ivs fst snd]; clear - Ha; lia
        | clear - Ha; lia ]
      | vm_compute; reflexivity | unfold IC_S, DC_S, DC_CTX, ERR_ONCE_CELL; clear; lia | change (Z.of_nat (length bs)) with nbs; unfold IC_S, DC_S, DC_CTX, ERR_ONCE_CELL; clear; lia ]
    | cbn; repeat first [exact I | split] | vm_compute; reflexivity | reflexivity ]
  | ].

Lemma pem_cli0_exit : forall m, pem_cli0 m -> exists v : byte, rw_cells usegs m LX_BASE_INITED [C1 v].
Proof.
  intros m (NONE & _). unfold LX_BASE_INITED.
  pem_img NONE m 0x32de20 [C1 (Z_to_bv 8 0)] H. exists (Z_to_bv 8 0). exact H.
Qed.

Lemma pem_cli_exit : forall m CLB, pem_cli m CLB -> exists v : byte, rw_cells usegs m LX_BASE_INITED [C1 v].
Proof. intros m CLB (pe & E & LBL & _ & _ & _ & _ & _ & BI). exists (Z_to_bv 8 1). exact BI. Qed.

Definition pemC : cli_sig := mkCli pem_cli0 pem_cli pem_cli0_stable pem_cli_stable pem_cli0_exit pem_cli_exit.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem pem_cli0_at_main : cli0_at_main pemC.
Proof.
  unfold cli0_at_main. intros sp0 argv envp uid R F pc fc rv m ro AM. cbn [CLI0 pemC].
  destruct AM as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & t & P0 & pg & m' & EMS & AM).
  injection EMS as _ _ _ _ _ Em _. subst m'.
  destruct AM as (MI & ST & PTH & ERRNO & PTH2 & REST).
  assert (NONE : forall a : word, 0x2c0000 <= bv_unsigned a < 0x353000 -> outside crt_written (bv_unsigned a) -> m a = None).
  { repeat lazymatch type of REST with _ /\ _ => first [exact (proj1 REST) | apply proj2 in REST] end. }
  split.
  - intros a Ha Hw Hp. apply NONE; [exact Ha|]. unfold crt_written. cbn [outside fst snd].
    unfold LXW_CLIENT, LXW_BASEINIT, LXW_LIBCRYPTO, LXW_PSELF, LXW_PKEYS, LXW_MREPL, LXW_DKEY in Hw. cbn [rin_ivs fst snd] in Hw. clear - Ha Hw Hp. lia.
  - (* [comment removed for export] *)
    pose proof (rw_cells_split_CB usegs m 0x3308c8 [C4 (Z_to_bv 64 2)] 76 (repeat (Z_to_bv 8 0) 76) _ [6; 1; 53; 8; 8]%nat PTH2 eq_refl) as X.
    cbn [mk_CB_cells app firstn skipn repeat] in X.
    apply (proj1 (rw_cells_app usegs m _ [_; _] _)) in X. destruct X as [_ X]. cbn [cells_size csize Nat.add] in X.
    apply (proj1 (rw_cells_app usegs m _ [_] _)) in X. destruct X as [U X]. cbn [cells_size csize Nat.add] in X.
    apply (proj1 (rw_cells_app usegs m _ [_] _)) in X. destruct X as [_ X]. cbn [cells_size csize Nat.add] in X.
    apply (proj1 (rw_cells_app usegs m _ [_; _] _)) in X. destruct X as [CB2 _].
    unfold RMallocRep.RATP. split.
    + lazymatch type of U with rw_cells _ _ ?A _ => replace (3344744 + -150) with A by (clear; lia) end.
      eapply rw_cells_recast; [exact U| cbn; repeat first [exact I | split]| vm_compute; reflexivity| reflexivity].
    + lazymatch type of CB2 with rw_cells _ _ ?A _ => replace (3344744 + -96) with A by (clear; lia) end.
      eapply rw_cells_recast; [exact CB2| cbn; repeat first [exact I | split]| vm_compute; reflexivity| reflexivity].
Qed.

(* [comment removed for export] *)
Theorem pem_cli0_pre : forall m, CLI0 pemC m -> finit_pre m.
Proof.
  intros m (NONE & U & PCB). unfold finit_pre.
  exists (Z_to_bv 8 0), (Z_to_bv 8 0), (Z_to_bv 8 0).
  exists (Z_to_bv 64 0xffffffff), z64, z64, z64, z64, z64, z64, z64, z64, z64, z64, z64, z64, z64, z64, z64, z64, z64.
  pem_img NONE m IC_S [C1 (Z_to_bv 8 0)] H1. pem_img NONE m (IC_S + 8) [C1 (Z_to_bv 8 0)] H2. pem_img NONE m (IC_S + 28) [C4 z64] H3.
  pem_img NONE m (IC_S + 32) [C4 z64] H4. pem_img NONE m (IC_S + 36) [C4 z64] H5. pem_img NONE m (IC_S + 40) [C4 z64] H6. pem_img NONE m (IC_S + 44) [C4 z64] H7.
  pem_img NONE m (IC_S + 80) [C8 z64; C8 z64] H8. pem_img NONE m (IC_S + 96) [C8 z64] H9.
  pem_img NONE m ERR_ONCE_CELL [C4 z64; C4 z64; C8 z64; C8 z64] H10.
  pem_img NONE m 0x31d4d0 [C4 (Z_to_bv 64 0xffffffff)] H11. pem_img NONE m (0x31d4d0 + 4) [C4 (Z_to_bv 64 0xffffffff)] H12.
  pem_img NONE m 0x32de90 [C4 z64; C4 z64; C8 z64] H13.
  pem_img NONE m 0x32dea0 [C1 (Z_to_bv 8 0)] H14. pem_img NONE m 0x32dea4 [C4 z64] H15. pem_img NONE m 0x32dea8 [C4 z64] H16.
  pem_img NONE m DC_S [C1 (Z_to_bv 8 0)] H17. pem_img NONE m (DC_S + 4) [C4 z64] H18. pem_img NONE m (DC_S + 8) [C4 z64] H19.
  pem_img NONE m (DC_S + 12) [C4 z64] H20. pem_img NONE m (DC_S + 16) [C4 z64] H21. pem_img NONE m (DC_S + 20) [C4 z64] H22.
  pem_img NONE m DC_CTX [CB CTX_SIZE (repeat (Z_to_bv 8 0) 328)] H23.
  pem_img NONE m 0x351c90 [C4 z64] H24. pem_img NONE m 0x351c98 [C4 z64; C4 z64; C4 z64] H25.
  pem_img NONE m 0x351890 [C8 z64] H26. pem_img NONE m (0x351890 + 8 * 1) [C8 z64] H27. pem_img NONE m (0x351890 + 8 * 2) [C8 z64] H28. pem_img NONE m (0x351890 + 8 * 3) [C8 z64] H29.
  pem_img NONE m 0x351cd0 [C8 z64] H30. pem_img NONE m (0x351cd0 + 8 * 2) [C8 z64] H31. pem_img NONE m (0x351cd0 + 8 * 3) [C8 z64] H32.
  pem_img NONE m 0x351010 [C4 z64] H33. pem_img NONE m 0x32df38 [C8 z64] H34.
  pose proof PCB as CB'. change [C8 z64; C8 z64] with ([C8 z64] ++ [C8 z64]) in CB'. apply (proj1 (rw_cells_app usegs m _ _ _)) in CB'. destruct CB' as [OCB TSD].
  cbn [cells_size csize Nat.add] in TSD. replace (RATP + -96 + Z.of_nat 8) with (RATP + -88) in TSD by (clear; lia).
  repeat match goal with |- _ /\ _ => split end; try assumption.
  - exists (repeat (Z_to_bv 8 0) 328). exact H23.
  - left. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u32arr_of_cells : forall (m : mem) A cs ws, rw_cells usegs m A cs -> cells_bytes cs = u32s ws -> Z.of_nat (cells_size cs) = 4 * Z.of_nat (length ws) -> u32arr usegs m A ws.
Proof. intros m A cs ws [[_ HB] HW] EB ES. split; [rewrite <- EB; exact HB| rewrite <- ES; exact HW]. Qed.
Lemma u64arr_of_cells : forall (m : mem) A cs ws, rw_cells usegs m A cs -> cells_bytes cs = u64s ws -> Z.of_nat (cells_size cs) = 8 * Z.of_nat (length ws) -> u64arr usegs m A ws.
Proof. intros m A cs ws [[_ HB] HW] EB ES. split; [rewrite <- EB; exact HB| rewrite <- ES; exact HW]. Qed.
Lemma u8arr_of_cells : forall (m : mem) A cs bs, rw_cells usegs m A cs -> cells_bytes cs = bs -> cells_size cs = length bs -> u8arr usegs m A bs.
Proof. intros m A cs bs [[_ HB] HW] EB ES. split; [rewrite <- EB; exact HB| rewrite <- ES; exact HW]. Qed.

(* [comment removed for export] *)
Lemma es_clean_at_rest : forall (m : mem) E, rw_cells usegs m E es_clean -> errst_at_rest E [] m.
Proof.
  intros m E ESC. unfold es_clean in ESC.
  Ltac esplit H H1 := apply (proj1 (rw_cells_app usegs _ _ _ _)) in H; destruct H as [H1 H];
    lazymatch type of H with rw_cells _ _ (?a + Z.of_nat ?n) _ => let v := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with v in H end;
    lazymatch type of H with rw_cells _ _ (?e + ?a + ?b) _ => let v := eval vm_compute in (a + b) in replace (e + a + b) with (e + v) in H by (clear; lia) | _ => idtac end.
  esplit ESC X0. esplit ESC X1. esplit ESC X2. esplit ESC X3. esplit ESC X4. esplit ESC X5. esplit ESC X6. esplit ESC X7. esplit ESC X8. rename ESC into X9.
  split; [reflexivity|].
  exists (repeat z64 16), (repeat z64 16), (repeat z64 16), (repeat ECL_LNW 16). unfold es_rep.
  split; [eapply (u32arr_of_cells _ _ _ _ X0); [vm_compute; reflexivity| reflexivity]|]. split; [reflexivity|].
  split; [eapply (u32arr_of_cells _ _ _ _ X1); [vm_compute; reflexivity| reflexivity]|]. split; [reflexivity|].
  split; [eapply (u64arr_of_cells _ _ _ _ X2); [vm_compute; reflexivity| reflexivity]|]. split; [reflexivity|].
  split; [eapply (u8arr_of_cells _ _ _ _ X3); [vm_compute; reflexivity| reflexivity]|].
  split; [eapply (u8arr_of_cells _ _ _ _ X4); [vm_compute; reflexivity| reflexivity]|].
  split; [eapply (u8arr_of_cells _ _ _ _ X5); [vm_compute; reflexivity| reflexivity]|].
  split; [eapply (u64arr_of_cells _ _ _ _ X6); [vm_compute; reflexivity| reflexivity]|]. split; [reflexivity|].
  split; [eapply (u32arr_of_cells _ _ _ _ X7); [vm_compute; reflexivity| reflexivity]|]. split; [reflexivity|].
  split; [eapply (u64arr_of_cells _ _ _ _ X8); [vm_compute; reflexivity| reflexivity]|]. split; [reflexivity|].
  split; [| clear; lia]. eapply rw_cells_recast; [exact X9| cbn; repeat first [exact I | split]| vm_compute; reflexivity| reflexivity].
Qed.

(* [comment removed for export] *)
Theorem pem_cli_post : forall (oldcb sh : word) (LB LBall' : list block) (L' : @clist bptr) (CLB : list block) (m' : mem) (s' : PState) (sp tp : word) (lo B : Z),
  cstate s' LBall' LB L' m' sp tp lo B -> Permutation LBall' (CLB ++ LB) -> cl_rel CLB L' ->
  finit_res CI_RES_B oldcb sh LB [] (Z_to_bv 64 1) LBall' L' m' -> rw_cells usegs m' 0x32df38 [C8 z64] -> CLI pemC m' CLB.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros oldcb sh LB LBall' L' CLB m' s' sp tp lo B CST PERM REL RES IP12. cbn [CLI pemC]. unfold pem_cli.
  destruct RES as (_ & pe & pm & psa & pn & ph & ptn & pg & psk & plk & pd & pk1 & pk2 & pkx & E & MK & SA & P & H & N & G & SK & LK & D & LK1 & LK2 & LKX & LKe & lh & u' & pad & top & ne
                  & INE & INM & INS & INP & INH & INTN & ING & INSK & INLK & IND & INK1 & INK2 & INKX & FRESH & ESC & MKC & HDR & PBLK & HN & NC & GC & SKC & LKM & DC & MC1 & MC2 & MCX
                  & BI & STOP & K1C & C32 & C40 & LKC & OD & EG & IB & OC & KC & DCI & DK & DC8 & DR12 & DC16 & DR20 & GLK & HCE & DK0 & DK4 & CBC & TSD & USED & NK & KL
                  & KY0 & KY1 & KY2 & KY3 & SL0 & SL2 & SL3 & RPL & NE0 & CRES).
  pose proof (cstate_nodup _ _ _ _ _ _ _ _ _ CST) as [NDB _].
  (* [comment removed for export] *)
  assert (TOC : forall (q : bptr) A n, In (q, A, n) LBall' -> In q [pe; pm; psa; pn; ph; ptn; pg; psk; plk; pd; pk1; pk2; pkx] -> In (q, A, n) CLB).
  { intros q A n Hq Hf. pose proof (Permutation_in _ PERM Hq) as X. apply in_app_iff in X. destruct X as [X|X]; [exact X|]. exfalso.
    apply (FRESH q); [left; apply in_map_iff; exists (q, A, n); split; [reflexivity| exact X]| exact Hf]. }
  exists pe, E, [(pm, MK, 72); (psa, SA, 32); (pn, P, 128); (pkx, LKX, 40)].
  split; [apply (TOC _ _ _ INE); left; reflexivity|].
  split. { cbn [map blk_id fst]. intros [X|[X|[X|[X|[]]]]].
    - exact (blk_ids_ne _ _ _ _ _ _ _ NDB INM INE ltac:(clear; lia) X).
    - exact (blk_ids_ne _ _ _ _ _ _ _ NDB INS INE ltac:(clear; lia) X).
    - exact (blk_ids_ne _ _ _ _ _ _ _ NDB INP INE ltac:(clear; lia) X).
    - exact (blk_ids_ne _ _ _ _ _ _ _ NDB INKX INE ltac:(clear; lia) X). }
  split. { intros b [<-|[<-|[<-|[<-|[]]]]]; (apply TOC; [assumption| cbn [In]; tauto]). }
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INM) as (MK0 & _ & _ & MKC' & _).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INS) as (SA0 & _ & _ & SAC & _).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INP) as (P0 & _ & _ & PC & _).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INKX) as (X0 & X16 & _ & XC & _).
  unfold ceil_window in CEIL_RANGE__.
  split.
  { unfold libenv. exists (Z_to_bv 64 2), pad, top, ne, 2, MK, SA, P, pm, psa, pn, pkx, 3, LKX.
    pose proof MKC as MK24. change [CB 24 (zeros 24); C8 (Z_to_bv 64 SA); CB 40 (zeros 40)] with ([CB 24 (zeros 24)] ++ [C8 (Z_to_bv 64 SA)] ++ [CB 40 (zeros 40)]) in MK24.
    apply (proj1 (rw_cells_app usegs m' _ _ _)) in MK24. destruct MK24 as [_ MK24]. apply (proj1 (rw_cells_app usegs m' _ _ _)) in MK24. destruct MK24 as [MK24 _].
    cbn [cells_size csize Nat.add length repeat] in MK24. change (Z.of_nat 24) with 24 in MK24.
    pose proof PBLK as PE. change [C8 (Z_to_bv 64 E); CB 120 (zeros 120)] with ([C8 (Z_to_bv 64 E)] ++ [CB 120 (zeros 120)]) in PE.
    apply (proj1 (rw_cells_app usegs m' _ _ _)) in PE. destruct PE as [PE _].
    unfold TH_ONCE, TH_KEY, TSD_MAIN, DC_IP12.
    split; [reflexivity|]. split; [exact STOP|]. split; [exact C32|]. split; [exact OD|]. split; [exact OC|]. split; [exact KC|]. split; [clear; lia|].
    split; [exact TSD|]. split; [exact SL2|]. split; [clear - MK0 MKC' CEIL_RANGE__; lia|].
    split; [replace (MK + 8 * 3) with (MK + 24) by (clear; lia); exact MK24|]. split; [clear - SA0 SAC CEIL_RANGE__; lia|].
    split; [exact HDR|]. split; [clear - P0 PC CEIL_RANGE__; lia|]. split; [exact NE0|]. split; [exact PE|].
    split; [exact DCI|]. split; [exact DK|]. split; [clear; lia|]. split; [exact DC8|]. split; [exact DR12|]. split; [exact DC16|]. split; [exact DR20|].
    split; [exact SL3|]. split; [exact GLK|]. split; [clear - X0; lia|]. split; [clear - X16; Z.div_mod_to_equations; lia|]. split; [exact MCX| exact IP12]. }
  split; [exact (es_clean_at_rest _ _ ESC)|].
  unfold LX_BASE_INITED. exact BI.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pem_rest (m : mem) : Prop := rw_cells usegs m LX_BASE_INITED [C1 (Z_to_bv 8 1)].
Definition pem_rest_fp (a : Z) : Prop := LX_BASE_INITED <= a < LX_BASE_INITED + 1.

Lemma pem_cli_open7 : forall m CLB, CLI pemC m CLB -> exists (pe : bptr) (E : Z) (LBL : list block),
  In (pe, E, 904) CLB /\ ~ In pe (map blk_id LBL) /\ incl_blocks LBL CLB /\ libenv m LBL E /\ errst_at_rest E [] m /\ pem_rest m.
Proof. intros m CLB (pe & E & LBL & H). exists pe, E, LBL. exact H. Qed.
Lemma pem_cli_close7 : forall m CLB (pe : bptr) (E : Z) (LBL : list block),
  In (pe, E, 904) CLB -> ~ In pe (map blk_id LBL) -> incl_blocks LBL CLB -> libenv m LBL E -> errst_at_rest E [] m -> pem_rest m -> CLI pemC m CLB.
Proof. intros m CLB pe E LBL H1 H2 H3 H4 H5 H6. cbn [CLI pemC]. exists pe, E, LBL. repeat (split; [assumption|]). exact H6. Qed.
Lemma pem_rest_agree : forall m m', pem_rest m -> agree_on pem_rest_fp m m' -> pem_rest m'.
Proof. intros m m' H AG. eapply rw_cells_agree; [exact AG| exact H| intros a Ha; exact Ha]. Qed.
Lemma pem_rest_fp_where : forall a, pem_rest_fp a -> 0x2c0000 <= a < 0x353000 /\ ~ ralloc_static a /\ a <> LX_FLAGS.
Proof.
  intros a Ha. unfold pem_rest_fp, LX_BASE_INITED in Ha.
  unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, LX_FLAGS. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma CM : crypto_malloc_stmt. Proof. exact (crypto_malloc_spec rmalloc_spec). Qed.
Lemma CZ : crypto_zalloc_stmt. Proof. exact (crypto_zalloc_spec CM). Qed.
Lemma CC : crypto_calloc_stmt. Proof. exact (crypto_calloc_spec CZ). Qed.
Lemma CF : crypto_free_stmt. Proof. exact (crypto_free_spec rfree_spec_proof). Qed.
Lemma CCF : crypto_clear_free_stmt. Proof. exact (crypto_clear_free_spec rfree_spec_proof). Qed.
Lemma CSM : crypto_secure_malloc_stmt. Proof. exact (crypto_secure_malloc_spec CM). Qed.
Lemma CSF : crypto_secure_free_stmt. Proof. exact (crypto_secure_free_spec CF). Qed.
Lemma CSCF : crypto_secure_clear_free_stmt. Proof. exact (crypto_secure_clear_free_spec CF). Qed.
Lemma CCRG : crypto_clear_realloc_grow_stmt. Proof. exact (crypto_clear_realloc_grow CM CCF). Qed.
Lemma CCRN : crypto_clear_realloc_null_stmt. Proof. exact (crypto_clear_realloc_null CM). Qed.
Lemma CR : crypto_realloc_stmt. Proof. exact (crypto_realloc_spec rrealloc_prefix_spec rmalloc_impl_spec rfree_impl_spec). Qed.
Lemma CAA : crypto_aligned_alloc_stmt. Proof. exact (crypto_aligned_alloc_spec rmemalign_prefix_spec rmalloc_impl_spec2 rmemalign_tail_spec). Qed.
Lemma LKN : T_lock_new_stmt. Proof. exact (T_lock_new_spec CZ). Qed.
Lemma LHN : lh_new_stmt. Proof. exact (lh_new_spec CZ CC). Qed.
Lemma SKN : T_sk_new_null_stmt. Proof. exact (T_sk_new_null_spec CZ). Qed.
Lemma ELS : err_load_strings_stmt. Proof. exact (err_load_strings_spec (lh_insert_of (lhi_double_spec (crypto_realloc_array_spec CR)) CM)). Qed.
Lemma ICF : init_crypto_full_stmt.
Proof.
  exact (init_crypto_full_spec (init_base_spec LKN)
           (init_load_strings_spec (err_shelve_first_spec (T_set_local_ex_first_spec CC CZ))
              (err_load_crypto_spec (err_load_ERR_first_spec (do_esi_spec LKN LHN) ELS) (err_load_const_spec (err_load_ERR_spec ELS) ELS)))).
Qed.
Lemma ECLF : eclear_first_stmt. Proof. exact (eclear_first_spec (egsi_first_spec (OSSL_ERR_STATE_new_spec CZ) (T_its_first_spec CZ CC CM))). Qed.
Lemma CTXI : context_init_abs_stmt CI_EV_B CI_A_B CI_B_B CI_BIG_B CI_STK_B CI_W_B CI_PRE_B CI_RES_B.
Proof.
  exact (context_init_abs_B CZ CM LKN LHN (ossl_property_string_data_new_rep_proof CZ LKN LHN SKN) CAA
           (ossl_property_parse_init_fp_proof CM CC T_sk_push_room_proof (T_sk_push_grow_proof CR))).
Qed.
Lemma ci_w_ip12_B : forall a, rin_ivs CI_W_B a -> ~ (0x32df38 <= a < 0x32df40).
Proof. intros a H. unfold CI_W_B in H. cbn [rin_ivs fst snd] in H. lia. Qed.
Lemma ci_budget_B13 : (CI_EV_B <= 3415)%nat /\ CI_A_B <= 3700 /\ CI_B_B <= 30 /\ CI_BIG_B <= 800000 /\ CI_STK_B <= 65264.
Proof. unfold CI_EV_B, CI_A_B, CI_B_B, CI_BIG_B, CI_STK_B. lia. Qed.

(* [comment removed for export] *)
Lemma PEMR : pem_read_bio_stmt libenv errst_at_rest errst_live.
Proof.
  exact (pem_read_bio_proof libenv libenv_fp libenv_agree libenv_fp_where errst_at_rest errst_live errst_fp errst_rest_agree errst_live_agree errst_fp_where errst_rest_live
           bio_free_null_proof
           (pem_malloc_spec CM CSM) pem_malloc0_spec (pem_free_spec CF CSCF) pem_free_null_spec sanitize_line_proof
           err_new_rest_proof (err_set_debug_proof CM) err_set_error_proof
           (bio_new_mem_proof CM) (bio_free_mem_proof CF CCF CSCF) bio_gets_proof (bio_puts_specM CCRN CCRG CSM CSCF) bio_ctrl_ptr_proof bio_ctrl_info_proof bio_read_proof
           (evp_ctx_new_spec CZ) (evp_ctx_free_spec CF) evp_ctx_free_null_spec).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem pem_rfuzz_one : rfuzz_one_stmt pemC.
Proof.
  exact (rfuzz_one_proof libenv libenv_fp libenv_agree libenv_fp_where errst_at_rest errst_live errst_fp errst_rest_agree errst_live_agree errst_fp_where
           pemC pem_rest pem_rest_fp pem_cli_open7 pem_cli_close7 pem_rest_agree pem_rest_fp_where
           (bio_new_mem_proof CM) (bio_write_spec CCRN CCRG CSM CSCF) bio_write0_proof (bio_writeg_spec CCRN CCRG CSM CSCF) PEMR
           (bio_free_mem_proof CF CCF CSCF) (err_clear_steady_proof CF) CF CSF).
Qed.

Theorem pem_rfuzz_init : rfuzz_init_stmt pemC.
Proof.
  exact (rfuzz_init_proof CI_EV_B CI_A_B CI_B_B CI_BIG_B CI_STK_B CI_W_B CI_PRE_B CI_FP_B CI_RES_B CTXI ci_w_range_B ci_w_ip12_B ci_stk_pos_B ci_nums_B
           ci_pre_agree_B ci_fp_ok_B ci_res_cfr_B ci_pre_intro_B pemC pem_cli0_pre pem_cli_post ci_budget_B13 ICF ECLF).
Qed.
End WithCeiling0.

(* [comment removed for export] *)
Theorem pem_client : forall (CE__ : Ceiling) (RN__ : RunRnd), exists C : cli_sig, cli0_at_main C /\ rfuzz_init_stmt C /\ rfuzz_one_stmt C.
Proof. intros CE__ RN__. exists pemC. split; [apply pem_cli0_at_main| split; [apply pem_rfuzz_init| apply pem_rfuzz_one]]. Qed.
