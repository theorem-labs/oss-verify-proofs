(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude DecodeC Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface Malloc_ifaceP ClientOwn LhRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun KStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Cs_pad
     Fz_M_malloc Fz_M_free Fz_M_secure Fz_M_clear_free Fz_M_clear_realloc Fz_W1_defs Fz_W1_growc Fz_W1_writec Fz_W1_read Fz_W1_misc Fz_W3_iface Fz_W2_rep Fz_W2_puts
     Fz_W3_defs Fz_W3_lems Fz_W3_j0lem. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_W7_perm. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_W7_defs Fz_W7_f Fz_W7_w Fz_W7_p Fz_W7_q.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.Step.addr_eq_tac ::=
  first [ symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ]
        | apply wa_of_var; lia ].

Notation wz := (Z_to_bv 64) (only parsing).
Ltac hide H := lazymatch type of H with ?X => change X with (hideP X) in H end.

Section W7. Context {CE__ : Ceiling} {RN__ : RunRnd}.
  Variable libenv : mem -> list block -> Z -> Prop.
  Variable libenv_fp : list block -> Z -> Prop.
  Hypothesis libenv_agree : forall m m' LBL E, libenv m LBL E -> agree_on (libenv_fp LBL) m m' -> libenv m' LBL E.
  Hypothesis libenv_fp_where : forall LBL a, libenv_fp LBL a ->
    (0x2c0000 <= a < 0x353000 /\ ~ ralloc_static a /\ a <> LX_FLAGS) \/ (exists b, In b LBL /\ blk_addr b <= a < blk_addr b + blk_size b).
  Variable errst_at_rest : Z -> list block -> mem -> Prop.
  Variable errst_live : Z -> Z -> Z -> list block -> mem -> Prop.
  Variable errst_fp : Z -> list block -> Z -> Prop.
  Hypothesis errst_rest_agree : forall m m' E strs, errst_at_rest E strs m -> agree_on (errst_fp E strs) m m' -> errst_at_rest E strs m'.
  Hypothesis errst_live_agree : forall m m' E top bot strs, errst_live E top bot strs m -> agree_on (errst_fp E strs) m m' -> errst_live E top bot strs m'.
  Hypothesis errst_fp_where : forall E strs a, errst_fp E strs a -> (E <= a < E + 904) \/ (exists b, In b strs /\ blk_addr b <= a < blk_addr b + blk_size b).
  Hypothesis errst_rest_live : forall m E, errst_at_rest E [] m -> errst_live E 0 0 [] m.
  Local Notation w7_comI := (w7_com libenv).
  Local Notation f7_invI := (f7_inv libenv errst_live).
  Local Notation pw_invI := (pw_inv libenv errst_live).
  Local Notation libenv_munchI := (libenv_munch libenv libenv_fp libenv_agree libenv_fp_where).

  (* [comment removed for export] *)
  Lemma er0_munch : forall (W : list (Z * Z)) E pe m m' s LBc LB0 L sp tp lo hi B (EX : bptr -> Prop),
    errst_at_rest E [] m -> munch W m m' -> wmono usegs m m' -> cstate s LBc LB0 L m sp tp lo B ->
    In (pe, E, 904) LBc -> Forall (wfree LBc lo hi EX) W -> EX pe -> errst_at_rest E [] m'.
  Proof.
    intros W E pe m m' s LBc LB0 L sp tp lo hi B EX ER MU WM CST INE HW HXE.
    eapply errst_rest_agree; [exact ER|]. eapply agree_on_mono; [exact (agree_on_of_munch _ _ _ MU WM)|]. cbv beta. intros a Ha.
    eapply wfree_outside; [exact CST| exact HW|]. right. destruct (errst_fp_where _ _ _ Ha) as [R|(b & [] & _)].
    exists (pe, E, 904). split; [exact INE|]. split; [exact HXE|]. unfold blk_addr, blk_size; cbn [fst snd]. exact R.
  Qed.
  Lemma er0_cfr : forall E pe (m m1 : mem) T1 SP s LBc Lc s1 LB1 L1,
    errst_at_rest E [] m -> cframe T1 [] SP s LBc Lc m s1 LB1 L1 m1 -> In (pe, E, 904) LBc -> ~ T1 pe -> errst_at_rest E [] m1.
  Proof.
    intros E pe m m1 T1 SP s LBc Lc s1 LB1 L1 ER (CFR & _) INE NT. eapply errst_rest_agree; [exact ER|]. eapply agree_on_mono; [exact CFR|]. cbv beta.
    intros a Ha. destruct (errst_fp_where _ _ _ Ha) as [R|(b & [] & _)]. right; left. exists (pe, E, 904). split; [exact INE|]. split; [exact NT|]. unfold blk_addr, blk_size; cbn [fst snd]. exact R.
  Qed.

  (* [comment removed for export] *)
  Definition w7_pre (en : w7e) (flags : word) : Prop :=
       RHEAP (w_s en) (w_LBall en) (w_m en) /\ cl_rel (w_CLB en) (w_L en) /\ lx_statics (w_m en) /\ lx_flags (w_m en) flags /\ rauxv_ok (w_m en) (w_B en)
    /\ w_SP en <= w_B en /\ w_B en < 2 ^ 63 /\ stk usegs (w_m en) (w_lo en) (w_SP en) /\ alloc_ceiling <= w_lo en /\ GLOBALS_TOP <= w_lo en
    /\ w_lo en <= w_SP en - LX_FUZZ_STACK
    /\ (exists errv, rw_cells usegs (w_m en) (errno_addr (w_tp en)) [C4 errv]) /\ w_tp en = wz RATP /\ mem_inv usegs (w_m en) /\ w_SP en mod 16 = 0
    /\ payload_ok (w_m en) (w_LB en) (w_D en) (w_d en)
    /\ In (w_pe en, w_E en, 904) (w_CLB en) /\ ~ In (w_pe en) (map blk_id (w_LBL en)) /\ incl_blocks (w_LBL en) (w_CLB en)
    /\ libenv (w_m en) (w_LBL en) (w_E en) /\ errst_at_rest (w_E en) [] (w_m en) /\ In (w_pe en, w_enm en) (w_L en).

  Definition E7_stmt : Prop :=
    forall (en : w7e) (flags t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    w7_pre en flags ->
    climpl (CALL_FUEL (zlength (w_d en))) (w_L en) (w_s en)
           (MS (mkR (w_ra en) (w_sp en) (w_gp en) (w_tp en) t0 t1 t2 (w_s0 en) (w_s1 en) (wz (w_D en)) (wz (zlength (w_d en))) a2 a3 a4 a5 a6 a7
                    (w_s2 en) (w_s3 en) (w_s4 en) (w_s5 en) (w_s6 en) (w_s7 en) (w_s8 en) (w_s9 en) (w_s10 en) (w_s11 en) t3 t4 t5 t6)
               (w_F en) (wz FZ_FUZZ_ONE) (w_fc en) None (w_m en) (seg_rom usegs))
      (w7_post libenv errst_at_rest en).

  (* [comment removed for export] *)
  Lemma land64_neg : forall x, - 2 ^ 64 <= x < 0 -> Z.land x 18446744073709551615 = x + 2 ^ 64.
  Proof.
    intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
    rewrite <- (Z.mod_add x 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
  Qed.

  Theorem E7_proof : bio_new_mem_stmt libenv -> bio_write_stmt -> pem_read_bio_stmt libenv errst_at_rest errst_live ->
    PW2_stmt libenv errst_at_rest errst_live -> PZ7_stmt libenv errst_at_rest errst_live -> E7_stmt.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros BNEW BW PEM PW2P PZ7P en flags t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 PRE.
    unfold bio_new_mem_stmt in BNEW. unfold bio_write_stmt in BW. unfold pem_read_bio_stmt in PEM. unfold PW2_stmt, J_P7 in PW2P. unfold PZ7_stmt, J_P7 in PZ7P. unfold FZ_FUZZ_ONE.
    pose proof PRE as (HP & CREL & LXS & FL & AV & SPB & B63 & ST & LO & GLO & SLO & [errv ERR] & TP & MI & AL16 & PAY & INEC & NPEL & INCLC & LE & ER0 & INL).
    unfold LX_FUZZ_STACK, GLOBALS_TOP in *.
    pose proof (bv_unsigned_in_range _ (w_sp en)) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold w_SP in *.
    pose proof (cstate_call _ _ _ _ _ _ _ _ _ flags errv HP CREL LXS FL AV SPB ST LO GLO ERR TP MI) as CST. fold (w_LBall en) in CST.
    pose proof CREL as [REL ROOM].
    assert (INE : In (w_pe en, w_E en, 904) (w_LBall en)) by (unfold w_LBall; apply in_or_app; left; exact INEC).
    assert (INCL : incl_blocks (w_LBL en) (w_LBall en)) by (intros b Hb; unfold w_LBall; apply in_or_app; left; exact (INCLC b Hb)).
    assert (NPL : forall b, In b (w_LBL en) -> blk_id b <> w_pe en) by (intros b Hb E; apply NPEL; rewrite <- E; apply in_map; exact Hb).
    assert (EPE : In (w_pe en) (map blk_id (w_CLB en))) by (apply in_map_iff; exists (w_pe en, w_E en, 904); split; [reflexivity| exact INEC]).
    pose proof (cstate_nodup _ _ _ _ _ _ _ _ _ CST) as [NDE NDL].
    destruct PAY as (PB & PR & D0 & D63 & D26 & PBLK).
    assert (DLEN0 : 0 <= zlength (w_d en)) by (unfold zlength; clear; lia).
    pose proof (munch_refl [(bv_unsigned (w_sp en) + -80, bv_unsigned (w_sp en))] (w_m en)) as MU. pose proof (wmono_refl usegs (w_m en)) as WM.
    assert (HWo : Forall (wfree (w_LBall en) (w_lo en) (bv_unsigned (w_sp en)) (fun _ => True)) [(bv_unsigned (w_sp en) + -80, bv_unsigned (w_sp en))])
      by (apply Forall_cons; [left; cbn [fst snd]; clear - SLO; lia| apply Forall_nil]).
    (* [comment removed for export] *)
    assert (ENTRY : forall mX, munch [(bv_unsigned (w_sp en) + -80, bv_unsigned (w_sp en))] (w_m en) mX -> wmono usegs (w_m en) mX -> mem_inv usegs mX ->
              stk usegs mX (w_lo en) (bv_unsigned (w_sp en) + -64) -> rw_cells usegs mX (bv_unsigned (w_sp en) + -32) (w7_saved en) -> 2 <= zlength (w_d en) ->
              cstate (w_s en) (w_LBall en) (w_LB en) (w_L en) mX (wz (bv_unsigned (w_sp en) + -64)) (w_tp en) (w_lo en) (w_B en)
              /\ w7_comI en (w_s en) (w_LBall en) (w_L en) mX [] /\ errst_at_rest (w_E en) [] mX).
    { intros mX MUX WMX MIX STX SAVEDX DL2.
      assert (CSTX : cstate (w_s en) (w_LBall en) (w_LB en) (w_L en) mX (wz (bv_unsigned (w_sp en) + -64)) (w_tp en) (w_lo en) (w_B en)).
      { eapply (cstate_seg _ _ _ _ _ (w_m en) mX (w_sp en) _ (w_tp en) (w_lo en) (w_B en) (bv_unsigned (w_sp en))); [exact CST| exact MUX| exact WMX| exact MIX| | clear - SLO; lia| exact SPB| | rewrite unsigned_lit by lia; exact STX| rewrite unsigned_lit by lia; clear - SPB; lia].
        - apply Forall_cons; [apply cwin_stack; clear - SLO; lia| apply Forall_nil].
        - cbn [disjoint_from]. unfold LX_FLAGS. clear - SLO LO GLO; lia. }
      split; [exact CSTX|]. split.
      - unfold w7_com, w_SP. split; [exact CSTX|].
        split. { eapply cframe_seg; [apply cframe_refl| exact MUX| exact WMX| exact HP| clear - SLO LO; lia|]. apply Forall_cons; [apply cseg_ok_stack; clear - SLO LO; lia| apply Forall_nil]. }
        split; [eapply libenv_munchI; [exact LE| exact MUX| exact WMX| exact CST| exact INCL| exact HWo| intros b _; exact I]|].
        split; [exact INCL|]. split; [exact INCL|]. split; [exact NPL|]. split; [exact INE|]. split; [exact INL|]. split; [apply Permutation_refl|].
        split; [exact SAVEDX|]. split; [unfold LX_FUZZ_STACK; clear - SLO; lia|]. split; [exact SPB|]. split; [exact B63|]. split; [exact AL16|]. split; [exact EPE|]. split; [exact ROOM|].
        split; [split; [exact PB| split; [exact PR| split; [exact D0| split; [exact D63| split; [exact D26| exact PBLK]]]]]|]. split; [exact DL2|]. split; [exact NDE| exact REL].
      - eapply (er0_munch _ (w_E en) (w_pe en)); [exact ER0| exact MUX| exact WMX| exact CST| exact INE| exact HWo| exact I]. }
    (* [comment removed for export] *)
    assert (PAYAT : forall T st' LB' L' m', cframe T [] (bv_unsigned (w_sp en)) (w_s en) (w_LBall en) (w_L en) (w_m en) st' LB' L' m' ->
              (forall q, T q -> ~ In q (map blk_id (w_LB en))) -> bytes_at usegs m' (w_D en) (to_bytes (w_d en))).
    { intros T st' LB' L' m' (CFR & _) NT. destruct PBLK as [ED|(pb & INpb & PB1 & PB2)].
      { eapply bytes_at_agree; [exact CFR| exact PB|]. intros a Ha. exfalso. rewrite ED in Ha. cbn in Ha. clear - Ha. lia. }
      eapply bytes_at_agree; [exact CFR| exact PB|]. intros a Ha. right; left. exists pb.
      split; [unfold w_LBall; apply in_or_app; right; exact INpb|]. split; [intros X; exact (NT _ X ltac:(apply in_map; exact INpb))|].
      unfold to_bytes in Ha. rewrite length_map in Ha. unfold zlength in PB2. clear - Ha PB1 PB2. lia. }
    cprefix. step. th_frame 64%nat [8; 8; 8; 8; 8; 8; 8; 8]%nat ST. ths. ths. ths. ths.
    ths. ths. ths. ths. ths. ths. ths. ths.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m0 end.
    lazymatch goal with H : stk usegs m0 _ _ |- _ => rename H into ST0 end. lazymatch goal with H : mem_inv usegs m0 |- _ => rename H into MI0 end.
    lazymatch goal with H : munch _ (w_m en) m0 |- _ => rename H into MU0 end. lazymatch goal with H : wmono usegs (w_m en) m0 |- _ => rename H into WM0 end.
    lazymatch goal with H : rw_cells usegs m0 (bv_unsigned (w_sp en) + -64) (CB 8 ?jk :: _) |- _ => rename H into FR0; set (junk8 := jk) in FR0 end.
    (* [comment removed for export] *)
    pose proof FR0 as FR0'.
    change (rw_cells usegs m0 (bv_unsigned (w_sp en) + -64) (([CB 8 junk8] ++ [C8 (wz 0); C8 (wz 0); C8 (wz 0)]) ++ w7_saved en)) in FR0'.
    apply (proj1 (rw_cells_app usegs m0 _ _ _)) in FR0'. destruct FR0' as [LOC0 SAVED0]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ app] in SAVED0.
    replace (bv_unsigned (w_sp en) + -64 + 32) with (bv_unsigned (w_sp en) + -32) in SAVED0 by (clear; lia).
    pose proof LOC0 as LOC0'. apply (proj1 (rw_cells_app usegs m0 _ _ _)) in LOC0'. destruct LOC0' as [JK0 Z30]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ app] in Z30.
    pose proof (rw_cells_junk_wcells m0 _ 8 _ [8]%nat JK0 ltac:(apply Forall_cons; [left; reflexivity| apply Forall_nil]) eq_refl) as OL0. cbn [wcells Nat.eqb] in OL0.
    lazymatch type of OL0 with rw_cells _ _ _ [C8 ?w] => set (ol := w) in OL0 end.
    assert (LOCw : rw_cells usegs m0 (bv_unsigned (w_sp en) + -64) [C8 ol; C8 (wz 0); C8 (wz 0); C8 (wz 0)]).
    { apply (proj2 (rw_cells_app usegs m0 _ [C8 ol] _)). split; [exact OL0| exact Z30]. }
    clear JK0 Z30 OL0.
    (* [comment removed for export] *)
    ths. if_cases K0; zify_cond K0; rewrite land64_neg in K0 by (clear - D26 DLEN0; lia).
    { (* [comment removed for export] *)
      ths. ths. ths. ths. ths.
      lazymatch goal with H : stk usegs _ (w_lo en) _ |- _ => rename H into STe end.
      pose proof FR0 as FRj. eapply stk_release in FRj; [| exact STe| clear - SLO LO GLO; lia]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ app length] in FRj.
      replace (bv_unsigned (w_sp en) + -64 + 64) with (bv_unsigned (w_sp en)) in FRj by (clear; lia). clear STe.
      ths. ths. chere. apply climpl_done.
      try replace (bv_unsigned (w_sp en) + 0) with (bv_unsigned (w_sp en)) by (clear; lia). try rewrite Z_to_bv_bv_unsigned.
      lazymatch goal with |- w7_post _ _ _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mz end.
      lazymatch goal with H : stk usegs mz (w_lo en) _ |- _ => rename H into STf end. lazymatch goal with H : mem_inv usegs mz |- _ => rename H into MIf end.
      lazymatch goal with H : munch _ (w_m en) mz |- _ => rename H into MUf end. lazymatch goal with H : wmono usegs (w_m en) mz |- _ => rename H into WMf end.
      unfold w7_post, w_SP. do 14 eexists. exists mz, (w_LBall en). split; [reflexivity|].
      split. { eapply (cstate_seg _ _ _ _ _ (w_m en) mz (w_sp en) (w_sp en) (w_tp en) (w_lo en) (w_B en) (bv_unsigned (w_sp en))); [exact CST| exact MUf| exact WMf| exact MIf| | clear - SLO; lia| exact SPB| | exact STf| exact SPB].
        - apply Forall_cons; [apply cwin_stack; clear - SLO; lia| apply Forall_nil].
        - cbn [disjoint_from]. unfold LX_FLAGS. clear - SLO LO GLO; lia. }
      split. { eapply cframe_seg; [apply cframe_refl| exact MUf| exact WMf| exact HP| clear - SLO LO; lia|]. apply Forall_cons; [apply cseg_ok_stack; clear - SLO LO; lia| apply Forall_nil]. }
      split; [apply Permutation_refl|]. split; [eapply libenv_munchI; [exact LE| exact MUf| exact WMf| exact CST| exact INCL| exact HWo| intros b _; exact I]|].
      split; [eapply (er0_munch _ (w_E en) (w_pe en)); [exact ER0| exact MUf| exact WMf| exact CST| exact INE| exact HWo| exact I]| exact INE]. }
    (* [comment removed for export] *)
    ths. tcall (W1_BIO_s_mem_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (w_lo en)).
    all: try first [eassumption | clear - LO SLO SPR GLO; lia].
    cbv beta delta [mkR]. ths. chere.
    lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mx _) _ => rename mx into m1 end.
    lazymatch goal with H : stk usegs m1 _ _ |- _ => rename H into ST1 end. lazymatch goal with H : mem_inv usegs m1 |- _ => rename H into MI1 end.
    lazymatch goal with H : munch _ (w_m en) m1 |- _ => rename H into MU1 end. lazymatch goal with H : wmono usegs (w_m en) m1 |- _ => rename H into WM1 end.
    destruct (ENTRY m1 MU1 WM1 MI1 ST1 SAVED0 ltac:(clear - K0; lia)) as (CST1 & COM1 & ER1).
    clear FR0 LOC0 MU1 WM1. try clear MU0; try clear WM0; try clear MI0; try clear ST0.
    (* [comment removed for export] *)
    eapply climpl_seq.
    { eapply BNEW with (meth := M_MEM) (E := w_E en) (LBL := w_LBL en) (lo := w_lo en) (B := w_B en);
        [unfold CALL_FUEL; clear - DLEN0; lia
        | unfold croom; unfold CL_ROOM_A, CL_ROOM_B, CL_ROOM_BIG in ROOM; clear - ROOM; lia
        | exact CST1
        | rewrite unsigned_lit by lia; unfold BNEW_STACK; clear - SLO; lia
        | exact (proj1 (proj2 (proj2 COM1)))
        | exact INCL| reflexivity| left; reflexivity]. }
    cbv beta. intros f2 L2 st2 ms2 (v2 & m2 & LB2 & RET & FU2 & GR2 & CST2 & FRM2 & LE2 & (K & BI & BB & BM & RP & -> & KD & -> & -> & MB2)).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM2 by lia.
    set (LB2 := (k_rp K, RP, 32) :: (k_bm K, BM, 32) :: (k_bb K, BB, 16) :: (k_bi K, BI, 128) :: w_LBall en) in *.
    set (L2 := (k_rp K, 32) :: (k_bm K, 32) :: (k_bb K, 16) :: (k_bi K, 128) :: w_L en) in *.
    pose proof (cstate_nodup _ _ _ _ _ _ _ _ _ CST2) as [NDB2 NDL2].
    assert (IDSL : forall q, In q (map fst (w_L en)) -> In q (map blk_id (w_LBall en))).
    { intros q Hq. pose proof REL as REL'. change (map blk_ptr (w_CLB en)) with (map blk_id (w_CLB en)) in REL'. apply w_pe_in_gen. rewrite REL'. exact Hq. }
    assert (KFR2 : forall q, In q (map blk_id (w_LBall en)) \/ In q (map fst (w_L en)) -> ~ mbio_T K q).
    { intros q Hq Tq. assert (Hq' : In q (map blk_id (w_LBall en))) by (destruct Hq as [Hq|Hq]; [exact Hq| exact (IDSL _ Hq)]).
      pose proof (nodup_app_disj [k_rp K; k_bm K; k_bb K; k_bi K] (map blk_id (w_LBall en)) q ltac:(cbn [app]; exact NDB2) Hq') as NI.
      apply NI. unfold mbio_T in Tq. rewrite KD in Tq. cbn [In]. clear - Tq. intuition congruence. }
    assert (KL2 : forall b, In b (w_LBL en) -> ~ mbio_T K (blk_id b)) by (intros b Hb; apply KFR2; left; apply in_map; exact (INCL b Hb)).
    assert (NKE : ~ mbio_T K (w_pe en)) by (apply KFR2; left; exact (w_pe_in _ EPE)).
    assert (COM2 : w7_comI en st2 LB2 L2 m2 (mbk_ents K 0)).
    { eapply (com7_call libenv); [exact COM1| exact CST2| exact FRM2| intros q _ _ []| intros b _ []| exact LE2
        | do 4 right; exact INE| do 4 right; exact INL| intros b Hb; do 4 right; exact (INCL b Hb)|].
      unfold mbk_ents. rewrite KD. cbn [app]. apply Permutation_refl. }
    assert (ER2 : errst_at_rest (w_E en) [] m2) by (eapply (er0_cfr (w_E en) (w_pe en)); [exact ER1| exact FRM2| exact INE| intros []]).
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST2 ltac:(do 3 right; left; reflexivity)) as (RBI1 & _ & _ & RBI2 & _).
    pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _). rewrite unsigned_lit in ST2 by lia.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ (proj1 FRM2) LOCw ltac:(clear; lia)) as LOC2.
    clear CST1 COM1 ER1 ST1 MI1 LOCw SAVED0.
    pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    (* [comment removed for export] *)
    cprefix. ths. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by (clear - RBI1 RBI2 LO SLO SPR; lia); clear - K1 RBI1; lia|]. clear K1.
    ths. ths. ths. ths. if_cases KD1; zify_cond KD1.
    { exfalso. clear - KD1 D0; lia. }
    clear KD1. ths. ths. ths. ths. chere.
    (* [comment removed for export] *)
    assert (PB2 : bytes_at usegs m2 (w_D en) (to_bytes (w_d en))).
    { eapply (PAYAT _ _ _ _ _ (proj1 (proj2 COM2))). intros q <- X. unfold w_LBall in NDE. rewrite map_app in NDE. exact (nodup_app_disj _ _ _ NDE X EPE). }
    destruct (w_d en) as [|c0 d'] eqn:ED; [unfold zlength in K0; cbn [length] in K0; exfalso; clear - K0; lia|].
    assert (EN : zlength (c0 :: d') + -1 = zlength d') by (unfold zlength; cbn [length]; clear; lia).
    assert (NLT : 1 <= zlength d' < 2 ^ 26 - 1) by (unfold zlength in D26, K0, EN |- *; cbn [length] in D26, K0, EN; clear - D26 K0 EN; lia).
    pose proof PB2 as PBt. change (to_bytes (c0 :: d')) with ([Z_to_bv 8 c0] ++ to_bytes d') in PBt. apply (proj1 (bytes_at_app _ _ _ _ _)) in PBt. destruct PBt as [PB0 PBt].
    cbn [length Z.of_nat Pos.of_succ_nat] in PBt.
    destruct PBLK as [X|(pb & INpb & PBA & PBS)]; [discriminate|]. destruct pb as [[ps AS] ns]. unfold blk_addr, blk_size in PBA, PBS; cbn [fst snd] in PBA, PBS.
    pose proof (grow_n_le43 (0 + zlength d') ltac:(unfold zlength; clear; lia)) as [G0 G43].
    pose proof (w_bounds (grow_n (0 + zlength d')) G0) as (WA & WB & _ & WBIG).
    eapply climpl_seq.
    { eapply BW with (K := K) (BI := BI) (meth := M_MEM) (len := 0) (max := 0) (IN := w_D en + 1) (n := zlength d') (lo := w_lo en) (B := w_B en) (src := to_bytes d');
        [clear - FU2 DLEN0; unfold CALL_FUEL in *; lia
        | unfold croom; subst L2; rewrite !cntA_cons, !cntB_cons, !bigsum_cons; unfold TIER_A_MAX; cbn [snd Z.leb Z.ltb Z.compare Pos.compare Pos.compare_cont];
          unfold CL_ROOM_A, CL_ROOM_B, CL_ROOM_BIG, CAP_A, CAP_B, BIG_ROOM in ROOM |- *; clear - ROOM WA WB WBIG G43 NLT; lia
        | exact CST2
        | rewrite unsigned_lit by lia; unfold BWRITE_STACK, WRITE_STACK, GROW_STACK, CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK; clear - SLO; lia
        | exact MB2
        | clear - NLT; lia
        | clear - NLT; lia
        | exact PBt
        | unfold to_bytes, zlength; rewrite length_map, Nat2Z.id; reflexivity
        | right; exists ps, AS, ns; split; [subst LB2; do 4 right; unfold w_LBall; apply in_or_app; right; exact INpb| split; [apply KFR2; left; unfold w_LBall; rewrite map_app; apply in_or_app; right; apply in_map_iff; exists (ps, AS, ns); split; [reflexivity| exact INpb]| rewrite <- EN; clear - PBA PBS; lia]]
        | rewrite unsigned_lit by lia; clear - AL16; Z.div_mod_to_equations; lia
        | reflexivity| reflexivity| rewrite EN; reflexivity]. }
    cbv beta. intros f3 L3 st3 ms3 (v3 & m3 & LB3 & RET & FU3 & GR3 & CST3 & FRM3 & R3).
    destruct R3 as (pd' & max' & -> & HMAX & HFIT & MB3 & KB & KL & NB & NL & PLS).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM3 by lia.
    rewrite EN. set (n := zlength d') in *.
    (* [comment removed for export] *)
    destruct PLS as [(P1 & -> & _ & _)|[(q & Dq & -> & _ & ELB3 & EL3)|(q & Dq & dd & i & nm & _ & P2 & _)]];
      [exfalso; clear - HFIT NLT; lia| | exfalso; rewrite KD in P2; discriminate].
    pose proof (cstate_nodup _ _ _ _ _ _ _ _ _ CST3) as [NDB3 NDL3].
    assert (QFR : forall b, In b LB2 -> blk_id b <> q).
    { intros b Hb. destruct b as [[qb Ab] nb]. cbn [blk_id fst]. rewrite ELB3 in CST3. exact (cstate_head_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST3 Hb). }
    assert (KFR3 : forall q0, In q0 (map blk_id (w_LBall en)) \/ In q0 (map fst (w_L en)) -> ~ mbio_T (mbk_data K (Some q)) q0).
    { intros q0 Hq0 X. assert (Hq' : In q0 (map blk_id (w_LBall en))) by (destruct Hq0 as [H|H]; [exact H| exact (IDSL _ H)]).
      unfold mbio_T in X. cbn [k_bi k_bb k_bm k_rp k_d mbk_data] in X.
      destruct X as [X|[X|[X|[X|X]]]]; [apply (KFR2 q0 Hq0); unfold mbio_T; tauto| apply (KFR2 q0 Hq0); unfold mbio_T; tauto| apply (KFR2 q0 Hq0); unfold mbio_T; tauto| apply (KFR2 q0 Hq0); unfold mbio_T; tauto|].
      injection X as <-. apply in_map_iff in Hq'. destruct Hq' as (b & Eb & Hb). apply (QFR b); [subst LB2; do 4 right; exact Hb| exact Eb]. }
    assert (KL3 : forall b, In b (w_LBL en) -> ~ mbio_T (mbk_data K (Some q)) (blk_id b)) by (intros b Hb; apply KFR3; left; apply in_map; exact (INCL b Hb)).
    assert (NKE3 : ~ mbio_T (mbk_data K (Some q)) (w_pe en)) by (apply KFR3; left; exact (w_pe_in _ EPE)).
    assert (INE2 : In (w_pe en, w_E en, 904) LB2) by (subst LB2; do 4 right; exact INE).
    assert (COM3 : w7_comI en st3 LB3 L3 m3 (mbk_ents (mbk_data K (Some q)) max')).
    { eapply (com7_call libenv); [exact COM2| exact CST3| exact FRM3| intros q0 Hq0 _; exact (KFR2 q0 Hq0)| exact KL2
        | eapply (libenv_cfr libenv libenv_fp libenv_agree libenv_fp_where); [exact LE2| exact (proj1 FRM3)| intros b Hb; subst LB2; do 4 right; exact (INCL b Hb)| exact KL2]
        | rewrite ELB3; right; exact INE2| rewrite EL3; right; subst L2; do 4 right; exact INL| intros b Hb; rewrite ELB3; right; subst LB2; do 4 right; exact (INCL b Hb)|].
      rewrite EL3. unfold mbk_ents. cbn [k_bi k_bb k_bm k_rp k_d mbk_data]. subst L2.
      lazymatch goal with |- Permutation ((q, max') :: ?a :: ?b :: ?c :: ?e :: ?r) _ =>
        change (Permutation ((q, max') :: ([a; b; c; e] ++ r)) (([a; b; c; e] ++ [(q, max')]) ++ r)) end.
      rewrite <- app_assoc. apply Permutation_middle. }
    assert (ER3 : errst_at_rest (w_E en) [] m3) by (eapply (er0_cfr (w_E en) (w_pe en)); [exact ER2| exact FRM3| exact INE2| exact NKE]).
    replace (0 + n) with n in MB3 by (clear; lia).
    pose proof CST3 as (HP3 & _ & (errv3 & _ & _ & ST3 & _ & _ & MI3 & _) & _). rewrite unsigned_lit in ST3 by lia.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ (proj1 FRM3) LOC2 ltac:(clear; lia)) as LOC3.
    assert (PB3 : bytes_at usegs m3 (w_D en) (to_bytes (c0 :: d'))).
    { eapply (PAYAT _ _ _ _ _ (proj1 (proj2 COM3))). intros q0 <- X. unfold w_LBall in NDE. rewrite map_app in NDE. exact (nodup_app_disj _ _ _ NDE X EPE). }
    pose proof (bytes_at_read usegs m3 (w_D en) (to_bytes (c0 :: d')) 0 1 PB3 ltac:(clear; lia) ltac:(cbn; clear; lia)) as RD. cbn [firstn skipn to_bytes map Z.to_nat] in RD.
    pose proof RD as RD'. replace (wa (w_D en + 0)) with (Z_to_bv 64 (w_D en)) in RD' by (unfold wa; f_equal; clear; lia).
    clear CST2 COM2 ER2 HP2 ST2 MI2 LOC2 MU WM PB2 PB0 PBt MB2 FRM2 LE2.
    pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    (* [comment removed for export] *)
    cprefix. ths. if_cases K2; zify_cond K2; [exfalso; clear - K2; lia|]. clear K2.
    ths. ubs_if.
    zstep. clear RD RD'. ths. ths. ths. ths. ths. ths. chere.
    pose proof (bv_unsigned_in_range 8 (Z_to_bv 8 c0)) as FLR. change (bv_modulus 8) with 256 in FLR.
    (* [comment removed for export] *)
    pose proof (cnt_of_perm _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 COM3)))))))))) as (CA & CB & CBIG).
    pose proof (cnt_mbk_ents (mbk_data K (Some q)) max' ltac:(clear - HFIT NLT; lia)) as (MA & MBB & MBIG & MA0 & MB0' & MBIG0).
    eapply climpl_seq.
    { eapply PEM with (K := mbk_data K (Some q)) (pe := w_pe en) (BI := BI) (meth := M_MEM) (blen := n) (bmax := max') (boff := 0) (PL := bv_unsigned (w_sp en) + -64)
                      (flags := bv_unsigned (Z_to_bv 8 c0)) (E := w_E en) (enm := w_enm en) (LBL := w_LBL en) (lo := w_lo en) (B := w_B en)
                      (ol := ol) (od := wz 0) (oh := wz 0) (on := wz 0);
        [clear - FU2 FU3 NLT DLEN0 EN; unfold CALL_FUEL in *; subst n; lia
        | unfold croom; unfold CL_ROOM_A, CL_ROOM_B, CL_ROOM_BIG, CAP_A, CAP_B, BIG_ROOM in ROOM |- *; destruct HMAX as [->| ->]; clear - ROOM CA CB CBIG MA MBB MBIG MA0 MB0' MBIG0 NLT G43 HFIT; lia
        | exact CST3
        | rewrite unsigned_lit by lia; unfold PEMR_STACK, BPUTS_STACK, WRITE_STACK, GROW_STACK, CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK; clear - SLO; lia
        | exact (proj1 (proj2 (proj2 COM3)))
        | intros b Hb; rewrite ELB3; right; subst LB2; do 4 right; exact (INCL b Hb)
        | intros b Hb [X|X]; [exact (KL3 b Hb X)| exact (NPL b Hb X)]
        | split; [rewrite ELB3; right; exact INE2| rewrite EL3; right; subst L2; do 4 right; exact INL]
        | intros X; exact (NKE3 (proj2 (mbio_T_blocks _ _) X))
        | exact ER3| exact MB3
        | clear - NLT; lia
        | rewrite unsigned_lit by lia; reflexivity
        | clear - SPB; lia
        | clear - AL16; Z.div_mod_to_equations; lia
        | exact LOC3
        | reflexivity| f_equal; clear; lia| f_equal; clear; lia| f_equal; clear; lia| reflexivity| reflexivity
        | clear - FLR; lia]. }
    cbv beta. intros f4 L4 st4 ms4 (v4 & m4 & LB4 & RET & FU4 & GR4 & CST4 & FRM4 & R4).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit.
    assert (EBL : n = zlength (w_d en) - 1) by (rewrite ED; clear - EN; lia).
    destruct (w7_pem_step libenv errst_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ COM3 MB3 KFR3 KL3 EBL CST4 FRM4 R4)
      as (ret & boff' & top & bot & strs & -> & BOFF & LEN2 & [(-> & INV4 & (lw & LOC4))|(-> & qd & qh & qn & DT & dlen & HD & nh & NM & nn & bd & bh & bn & PW4)]).
    - (* [comment removed for export] *)
      eapply (PZ7P en st4 LB4 L4 f4 m4 (mbk_data K (Some q)) BI n max' boff' top bot strs); [exact INV4| clear - FU2 FU3 FU4 NLT DLEN0 EN LEN2; unfold CALL_FUEL in *; subst n; lia| exact LOC4].
    - (* [comment removed for export] *)
      eapply (PW2P en st4 LB4 L4 f4 m4 (mbk_data K (Some q)) BI n max' boff' top bot n boff' strs qd qh qn DT dlen HD nh NM nn bd bh bn);
        [exact PW4| clear - FU2 FU3 FU4 NLT DLEN0 EN LEN2; unfold CALL_FUEL in *; subst n; lia| clear; lia|].
      destruct HMAX as [->| ->]; clear - G43 BOFF HFIT NLT; lia.
  Qed.
End W7.
