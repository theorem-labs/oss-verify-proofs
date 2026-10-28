(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude DecodeC Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP. From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Bytes.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn LhRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_M_malloc Fz_M_zalloc Fz_M_free Fz_M_secure
     Fz_M_clear_free Fz_M_clear_realloc Fz_W1_defs Fz_W1_sync Fz_W1_growc Fz_W1_writec Fz_W1_read Fz_W3_iface Fz_W2_rep Fz_W3_defs Fz_W3_end Fz_W3_tail Fz_W3_dec
     Cs_pad F_strlen F_strncmp.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation wz := (Z_to_bv 64) (only parsing).
Ltac hide H := lazymatch type of H with ?X => change X with (hideP X) in H end.

(* [comment removed for export] *)
Definition pem_tail_str : list byte := Eval vm_compute in (match image_bytes Image.usegs 0x341ae 7 with Some bs => bs | None => [] end).
Lemma pem_tail_ro : ro_bytes Image.usegs 0x341ae pem_tail_str.
Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma pem_tail_len : length pem_tail_str = 7%nat. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma strncmp_walk_total : forall k l r, (k < length l)%nat -> (k < length r)%nat -> exists v, strncmp_walk l r k = Some v.
Proof.
  induction k as [|k IH]; intros [|a l] [|b r] Hl Hr; cbn in Hl, Hr; try lia; cbn [strncmp_walk].
  - destruct (_ || _)%bool; eexists; reflexivity.
  - destruct (_ || _)%bool; [eexists; reflexivity| apply IH; lia].
Qed.
Lemma strncmp_model_total : forall l r n, 0 <= n -> n <= Z.of_nat (length l) -> n <= Z.of_nat (length r) -> exists v, strncmp_model l r n = Some v.
Proof.
  intros l r n H0 Hl Hr. unfold strncmp_model. destruct (Z.eqb_spec n 0); [eexists; reflexivity|].
  apply strncmp_walk_total; lia.
Qed.

Section W3. Context {CE__ : Ceiling} {RN__ : RunRnd}.
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
  Local Notation com_callI := (com_call libenv libenv_fp libenv_agree libenv_fp_where).
  Local Notation com_segI := (com_seg libenv libenv_fp libenv_agree libenv_fp_where).
  Local Notation er0_callI := (er0_call errst_at_rest errst_fp errst_rest_agree errst_fp_where).
  Local Notation er0_segI := (er0_seg errst_at_rest errst_fp errst_rest_agree errst_fp_where).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem LFREE_proof : pem_free_stmt -> TAIL_stmt libenv errst_at_rest errst_live -> LFREE_stmt libenv errst_at_rest errst_live.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros PF TAILP en s LBc Lc f m off rem rA rB rBig xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s9 s11 t3 t4 t5 t6 l0 l1 l3 l4 l8 l9 l11 ta tb
           qn ql namev nn LB2 hBv dBv bn bs KX KY methX methY lenX maxX lenY maxY.
    cbv zeta. intros COM ER0 REM RA3 RB2 RBIG LSUM2 LOC OWNN NN LBN NMC NUL OWNL LBS LBC MBX MBY ELB CFRESH EL NDT OUT. unfold TAIL_stmt, J_TAIL in TAILP.
    pose proof COM as (CST & FR0 & LE & INCL0 & INCL & NTL & OWNE & MB & OFF & EVF & FU & ROOM & CG & RA0 & RB0 & RBIG0 & PLB & PLC & SAVED & SLO & PLBB & FLR & AL16 & EPE & EK).
    pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
    unfold BPUTS_STACK, WRITE_STACK, GROW_STACK, J_LFREE, GLOBALS_TOP in *.
    assert (WSP : 48 + 32 + (64 + (96 + CCR_STACK + CSM_STACK + CSF_STACK)) = 25200) by (unfold CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK; clear; lia).
    rewrite WSP in SLO. clear WSP.
    pose proof (bv_unsigned_in_range _ (e_sp en)) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold e_PL in *.
    rewrite unsigned_lit in ST by (clear - SPR SLO LO GLO; lia). rewrite unsigned_lit in SPB by (clear - SPR SLO LO GLO; lia).
    assert (INE : In (e_pe en, e_E en, 904) LBc) by exact (proj1 OWNE).
    pose proof (nd_split _ _ NDT) as (NDC & NDR & DJC). pose proof (nd_split _ _ NDC) as (_ & NDC2 & DJX). pose proof (nd_split _ _ NDC2) as (_ & NDC3 & DJY).
    inversion NDC3 as [|z1 k1 NQ1 ND4]; subst. cbn [In] in NQ1.
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNN)) as (RN1 & _ & _ & RN2 & _).
    (* [comment removed for export] *)
    assert (NQL : ~ In ql (mbio_blocks KX ++ mbio_blocks KY ++ [qn] ++ e_pe en :: mbio_blocks (e_K en))).
    { intros X. apply in_app_iff in X. destruct X as [X|X]; [apply (DJX _ X); apply in_or_app; right; right; left; reflexivity|].
      apply in_app_iff in X. destruct X as [X|X]; [apply (DJY _ X); right; left; reflexivity|].
      apply in_app_iff in X. destruct X as [X|X]; [cbn in X; clear - X NQ1; intuition|].
      apply (DJC ql); [do 2 (apply in_or_app; right); right; left; reflexivity| exact X]. }
    assert (HT1 : forall q, In q (map blk_id (e_LBall en)) \/ In q (map fst (e_L en)) -> ~ pem_T en q -> ~ ql = q).
    { intros q [Hq|Hq] _ <-; apply in_map_iff in Hq.
      - destruct Hq as (b & E & Hb). apply (CFRESH _ Hb). rewrite E. do 2 (apply in_or_app; right). right; left; reflexivity.
      - destruct Hq as ([q' nm] & E & Hq). cbn in E. subst q'. apply (EL _ _ Hq). do 2 (apply in_or_app; right). right; left; reflexivity. }
    assert (HK1 : forall q, mbio_T (e_K en) q -> ~ ql = q) by (intros q Hq <-; apply NQL; apply mbio_T_blocks in Hq; do 3 (apply in_or_app; right); right; exact Hq).
    assert (HE1 : ~ ql = e_pe en) by (intros X; apply NQL; do 3 (apply in_or_app; right); left; exact (eq_sym X)).
    assert (HX1 : forall q, mbio_T KX q -> ~ ql = q) by (intros q Hq <-; apply NQL; apply mbio_T_blocks in Hq; apply in_or_app; left; exact Hq).
    assert (HY1 : forall q, mbio_T KY q -> ~ ql = q) by (intros q Hq <-; apply NQL; apply mbio_T_blocks in Hq; apply in_or_app; right; apply in_or_app; left; exact Hq).
    assert (HN1 : ~ ql = qn) by (clear - NQ1; intuition).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold pem_loc in LOC.
    (* [comment removed for export] *)
    cprefix. ths. ths. ths. ths. ths. chere.
    eapply climpl_seq.
    { eapply PF with (p := ql) (A := LB2) (n := 256) (nm := 256) (num := 256) (flags := e_flags en) (junk := bs) (lo := e_lo en) (B := e_B en);
        [clear - FU REM; lia| exact OWNL| clear; lia| exact LBC| clear - FLR; lia| exact CST| rewrite unsigned_lit by lia; unfold PFREE_STACK, CSF_STACK, CF_STACK, RFREE_STACK; clear - SLO; lia
        | reflexivity| reflexivity| reflexivity]. }
    cbv beta. intros f1 L1 st1 ms1 (v1 & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & (-> & i & HI & ->)).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM1 by lia.
    pose proof (w_bounds 256 ltac:(clear; lia)) as (WA & WB' & WAB & WBIG).
    assert (COM1 : pem_com libenv en st1 (lb_remove ql LBc) (cremove i Lc) f1 m1 off (rem - 1) rA rB rBig).
    { eapply (com_callI en) with (T1 := eq ql); [exact COM| exact CST1| exact FRM1| unfold e_PL; clear; lia| exact FU1| clear - REM; lia| exact GR1| | | | | | | exact HT1| exact HK1| exact HE1]; clear - WA WB' WBIG RA0 RB0 RBIG0; lia. }
    pose proof FRM1 as (CFR1 & KP1 & _).
    pose proof (mb_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBX FRM1 HX1) as MBX1. pose proof (mb_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBY FRM1 HY1) as MBY1.
    pose proof (own_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ OWNN FRM1 HN1) as OWNN1.
    pose proof (er0_callI en _ _ _ _ _ _ _ _ _ _ ER0 FRM1 INE HE1) as ER1.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 LOC ltac:(clear; lia)) as LOC1. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 OUT ltac:(clear; lia)) as OUT1.
    pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (qn, namev, nn) CFR1 NMC (proj1 OWNN) HN1 ltac:(cbn; clear; lia) ltac:(cbn; clear - NN; lia)) as NMC1.
    (* [comment removed for export] *)
    eapply (TAILP en st1 (lb_remove ql LBc) (cremove i Lc) f1 m1 off (rem - 1)%nat rA rB rBig _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ l0 l1 l3 l4 (wz LB2) l8 l9 l11 ta tb
              qn namev nn hBv dBv bn KX KY methX methY lenX maxX lenY maxY);
      [exact COM1| exact ER1| clear - REM; lia| exact RA3| exact RB2| exact RBIG| exact LSUM2| unfold pem_loc; exact LOC1
      | exact OWNN1| exact NN| exact LBN| exact NMC1| exact NUL| exact MBX1| exact MBY1| | | | | exact OUT1].
    - intros b Hb. apply lb_remove_In in Hb. destruct Hb as [Hb NE]. destruct (ELB _ Hb) as [X|X]; [left; exact X| right].
      apply in_app_iff in X. apply in_or_app. destruct X as [X|X]; [left; exact X| right]. apply in_app_iff in X. apply in_or_app. destruct X as [X|X]; [left; exact X| right].
      cbn in X |- *. clear - X NE. intuition congruence.
    - intros b Hb X. apply (CFRESH _ Hb). apply in_app_iff in X. apply in_or_app. destruct X as [X|X]; [left; exact X| right].
      apply in_app_iff in X. apply in_or_app. destruct X as [X|X]; [left; exact X| right]. cbn in X |- *. clear - X. tauto.
    - intros q nm Hq X. apply (EL _ _ Hq). apply in_app_iff in X. apply in_or_app. destruct X as [X|X]; [left; exact X| right].
      apply in_app_iff in X. apply in_or_app. destruct X as [X|X]; [left; exact X| right]. cbn in X |- *. clear - X. tauto.
    - apply (nd_drop (mbio_blocks KX ++ mbio_blocks KY ++ [qn]) _ ql).
      lazymatch goal with |- List.NoDup ?l => replace l with ((mbio_blocks KX ++ mbio_blocks KY ++ [qn; ql]) ++ e_pe en :: mbio_blocks (e_K en)); [exact NDT| rewrite <- ?app_assoc; reflexivity] end.
  Qed.

  (* [comment removed for export] *)
  Ltac pure_sync m2 :=
    lazymatch goal with
    | COM : pem_com _ ?en ?s ?LBc ?Lc ?f ?m ?off ?rem ?rA ?rB ?rBig, MU : munch [] ?m0 m2, WM : wmono usegs ?m1 m2, MI2 : mem_inv usegs m2, ST2 : stk usegs m2 _ _,
      CST : cstate ?s ?LBc _ ?Lc ?m _ _ _ _, ER0 : _ (e_E ?en) [] ?m, INE : In (e_pe ?en, e_E ?en, 904) ?LBc |- _ =>
        let COM2 := fresh "COM2" in let ER2 := fresh "ER2" in
        assert (COM2 : pem_com libenv en s LBc Lc f m2 off rem rA rB rBig)
          by (eapply (com_segI en s LBc Lc f m off rem rA rB rBig [] m2 (fun _ => True));
              [exact COM| exact MU| exact WM| exact MI2| exact ST2| apply Forall_nil| intros; exact I| exact I]);
        assert (ER2 : errst_at_rest (e_E en) [] m2)
          by (eapply (er0_segI [] en m m2) with (EX := fun _ => True) (hi := 0); [exact ER0| exact MU| exact WM| exact CST| exact INE| apply Forall_nil| exact I]);
        repeat match goal with
        | MB : mbio_rep m LBc Lc ?K ?BI ?meth ?len ?max ?o |- _ =>
            let MB2 := fresh "MB2" in
            assert (MB2 : mbio_rep m2 LBc Lc K BI meth len max o)
              by (eapply (mb_seg [] m m2) with (EX := fun _ => True) (hi := 0); [exact MB| exact CST| exact MU| exact WM| apply Forall_nil| intros; exact I]);
            clear MB
        end
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem ENDLINE_proof :
    RAISE2_stmt libenv errst_at_rest errst_live -> LFREE_stmt libenv errst_at_rest errst_live -> ENDLINE_stmt libenv errst_at_rest errst_live.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros RAISEP LFREEP en s LBc Lc f m off rem rA rB rBig xra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s11 t3 t4 t5 t6 l0 l1 l3 l4 l8 l11 ta tb
           qn ql namev nn LB2 hBv dBv got str bn2 bs KX KY methX methY lenX maxX lenY maxY.
    cbv zeta. intros COM ER0 REM RA3 RB2 RBIG LSUM2 LOC GOT TMP OWNN NN LBN NMC NONUL OWNL LBS LBC MBX MBY ELB CFRESH EL NDT OUT.
    unfold RAISE2_stmt, J_RAISE2 in RAISEP. unfold LFREE_stmt, J_LFREE in LFREEP.
    pose proof COM as (CST & FR0 & LE & INCL0 & INCL & NTL & OWNE & MB & OFF & EVF & FU & ROOM & CG & RA0 & RB0 & RBIG0 & PLB & PLC & SAVED & SLO & PLBB & FLR & AL16 & EPE & EK).
    pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
    unfold BPUTS_STACK, WRITE_STACK, GROW_STACK, J_ENDLINE, GLOBALS_TOP in *.
    assert (WSP : 48 + 32 + (64 + (96 + CCR_STACK + CSM_STACK + CSF_STACK)) = 25200) by (unfold CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK; clear; lia).
    rewrite WSP in SLO. clear WSP.
    pose proof (bv_unsigned_in_range _ (e_sp en)) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold e_PL in *.
    rewrite unsigned_lit in ST by (clear - SPR SLO LO GLO; lia). rewrite unsigned_lit in SPB by (clear - SPR SLO LO GLO; lia).
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNN)) as (RN1 & _ & _ & RN2 & _).
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNL)) as (RL1 & _ & _ & RL2 & _).
    unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in RN2, RL2.
    (* [comment removed for export] *)
    set (len := Z.of_nat (length str)) in *.
    assert (LSTR : len + 1 + Z.of_nat (length bn2) = nn) by (subst len; rewrite length_app in LBN; cbn [length] in LBN; clear - LBN NN; lia).
    destruct (cstate_blk_pad _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNN)) as (pad & PADB & PADL).
    assert (NMB : bytes_at usegs m namev (str ++ Z_to_bv 8 0 :: (bn2 ++ pad))).
    { pose proof (rw_cells_bytes_at _ _ _ _ NMC) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X.
      rewrite app_comm_cons, app_assoc. apply (proj2 (bytes_at_app _ _ _ _ _)). split; [exact X|]. rewrite LBN, Z2Nat.id by (clear - NN; lia). exact PADB. }
    assert (PAD8 : (- (namev + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length (bn2 ++ pad))).
    { rewrite length_app, Nat2Z.inj_add, PADL. subst len. clear - LSTR NN. Z.div_mod_to_equations. lia. }
    (* [comment removed for export] *)
    pose proof (rw_cells_bytes_at _ _ _ _ LBC) as LBB. cbn [cells_bytes cbytes] in LBB. rewrite app_nil_r in LBB.
    assert (LB9 : bytes_at usegs m (LB2 + 9) (skipn 9 bs)).
    { rewrite <- (firstn_skipn 9 bs) in LBB. apply (proj1 (bytes_at_app _ _ _ _ _)) in LBB. destruct LBB as [_ X]. rewrite firstn_length_le in X by (rewrite LBS; clear; lia). exact X. }
    assert (LB9S : bytes_at usegs m (LB2 + 9 + len) (skipn (Z.to_nat len) (skipn 9 bs))).
    { pose proof LB9 as X. rewrite <- (firstn_skipn (Z.to_nat len) (skipn 9 bs)) in X. apply (proj1 (bytes_at_app _ _ _ _ _)) in X. destruct X as [_ X].
      rewrite firstn_length_le in X by (rewrite skipn_length, LBS; clear - LSTR NN; lia). rewrite Z2Nat.id in X by (clear; subst len; lia). exact X. }
    assert (TLB : bytes_at usegs m 0x341ae pem_tail_str) by (apply ro_bytes_at; [exact MI| clear; lia| rewrite pem_tail_len; clear; lia| exact pem_tail_ro]).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold pem_loc in LOC.
    (* [comment removed for export] *)
    cprefix. ths. ths. ths. if_cases K0; zify_cond K0. { exfalso. clear - K0 RL1 RL2 CEIL_RANGE__. unfold ceil_window in *. lia. } clear K0.
    ths. ths. ths. ths.
    tcall (strlen_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ str (bn2 ++ pad)).
    all: try first [eassumption | clear - RN1 RN2 LO SLO SPR; lia].
    cbv beta delta [mkR]. fold len.
    (* [comment removed for export] *)
    destruct (strncmp_model_total (skipn 9 bs) (str ++ Z_to_bv 8 0 :: bn2 ++ pad) len) as (v1 & V1);
      [clear; subst len; lia| rewrite skipn_length, LBS; clear - LSTR NN; lia| rewrite length_app; cbn [length]; clear; subst len; lia|].
    ths. ths. ths. ths. ths.
    tcall (strncmp_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (skipn 9 bs) (str ++ Z_to_bv 8 0 :: bn2 ++ pad) v1).
    all: try first [eassumption | clear - RN1 RN2 RL1 RL2 LO SLO SPR; lia].
    cbv beta delta [mkR].
    (* [comment removed for export] *)
    assert (INE : In (e_pe en, e_E en, 904) LBc) by exact (proj1 OWNE).
    assert (NUL : In (Z_to_bv 8 0) (str ++ Z_to_bv 8 0 :: bn2)) by (apply in_or_app; right; left; reflexivity).
    assert (LXY : 0 <= lenX /\ 0 <= lenY).
    { destruct MBX as (BMX0 & BBx & RPx & flx & rrwx & padwx & nrx & nwx & _ & _ & _ & _ & _ & _ & _ & (rmaxwx & _ & _ & _ & _ & X1 & X2 & X3 & _)).
      destruct MBY as (BMY0 & BBy & RPy & fly & rrwy & padwy & nry & nwy & _ & _ & _ & _ & _ & _ & _ & (rmaxwy & _ & _ & _ & _ & Y1 & Y2 & Y3 & _)). clear - X1 X2 X3 Y1 Y2 Y3. lia. }
    Ltac raise2 RAISEP m2 en s LBc Lc f off rem rA rB rBig l0 l1 l3 l4 l8 l11 ta tb qn ql namev nn LB2 hBv dBv str bn2 bs KX KY methX methY lenX maxX lenY maxY :=
      chere; pure_sync m2;
      lazymatch goal with
      | COM2 : pem_com _ en s LBc Lc f m2 off rem rA rB rBig, ER2 : _ (e_E en) [] m2, MBX2 : mbio_rep m2 LBc Lc KX _ _ _ _ _, MBY2 : mbio_rep m2 LBc Lc KY _ _ _ _ _,
        LOC2 : rw_cells usegs m2 (bv_unsigned (e_sp en) + -208) _, OUT2 : rw_cells usegs m2 (bv_unsigned (e_sp en)) _, NMC2 : rw_cells usegs m2 namev _, LBC2 : rw_cells usegs m2 LB2 _ |- _ =>
        eapply (RAISEP en s LBc Lc f m2 off rem rA rB rBig _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  l0 l1 l3 l4 (Z_to_bv 64 (bv_unsigned (e_sp en) + 8)) (Z_to_bv 64 (bv_unsigned (e_sp en) + 16)) l8 (Z_to_bv 64 (e_flags en)) l11 ta tb
                  qn ql namev nn LB2 hBv dBv 897 (str ++ Z_to_bv 8 0 :: bn2) bs KX KY methX methY lenX maxX lenY maxY);
          [exact COM2| exact ER2| | | clear; lia| unfold pem_loc; exact LOC2| | | | exact NMC2| | | | exact LBC2| exact MBX2| exact MBY2| | | | | exact OUT2]
      end.
    ths. ths. if_cases K1; zify_cond K1.
    { ths. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        raise2 RAISEP mx en s LBc Lc f off rem rA rB rBig l0 l1 l3 l4 l8 l11 ta tb qn ql namev nn LB2 hBv dBv str bn2 bs KX KY methX methY lenX maxX lenY maxY end;
        [clear - REM; lia| clear - RA3; lia| exact OWNN| clear - NN; lia| exact LBN| exact NUL| exact OWNL| exact LBS| exact ELB| exact CFRESH| exact EL| exact NDT]. }
    clear K1 V1.
    (* [comment removed for export] *)
    destruct (strncmp_model_total (skipn (Z.to_nat len) (skipn 9 bs)) pem_tail_str 6) as (v2 & V2);
      [clear; lia| rewrite !skipn_length, LBS; clear - LSTR NN; lia| rewrite pem_tail_len; clear; lia|].
    ths. ths. if_cases K4; zify_cond K4.
    { exfalso. rewrite Bytes.lnot_mod64 in K4 by (clear - RL1 RL2 CEIL_RANGE__; unfold ceil_window in *; lia). unfold Z.lnot in K4.
      clear - K4 RL1 RL2 CEIL_RANGE__ LSTR NN. unfold ceil_window in *. subst len. Z.div_mod_to_equations. lia. }
    clear K4.
    ths. ths. ths. ths. ths.
    tcall (strncmp_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (skipn (Z.to_nat len) (skipn 9 bs)) pem_tail_str v2).
    all: try first [eassumption | clear - RN1 RN2 RL1 RL2 LO SLO SPR LSTR NN; subst len; lia].
    cbv beta delta [mkR].
    ths. ths. ths. if_cases K2; zify_cond K2.
    { lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        raise2 RAISEP mx en s LBc Lc f off rem rA rB rBig l0 l1 l3 l4 l8 l11 ta tb qn ql namev nn LB2 hBv dBv str bn2 bs KX KY methX methY lenX maxX lenY maxY end;
        [clear - REM; lia| clear - RA3; lia| exact OWNN| clear - NN; lia| exact LBN| exact NUL| exact OWNL| exact LBS| exact ELB| exact CFRESH| exact EL| exact NDT]. }
    clear K2 V2.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    pure_sync m3.
    lazymatch goal with H1 : mbio_rep m3 LBc Lc KX _ _ _ _ _, H2 : mbio_rep m3 LBc Lc KY _ _ _ _ _ |- _ => rename H1 into MBX3; rename H2 into MBY3 end.
    lazymatch goal with H1 : rw_cells usegs m3 (bv_unsigned (e_sp en) + -208) _, H2 : rw_cells usegs m3 (bv_unsigned (e_sp en)) _, H3 : rw_cells usegs m3 namev _, H4 : rw_cells usegs m3 LB2 _ |- _ =>
      rename H1 into LOC3; rename H2 into OUT3; rename H3 into NMC3; rename H4 into LBC3 end.
    ths. if_cases K3; zify_cond K3. all: swap 1 2.
    - (* [comment removed for export] *)
      assert (G0 : got = 0) by (rewrite ?unsigned_lit in K3 by (clear - GOT; lia); clear - K3 GOT; lia). specialize (TMP G0). subst l1. clear K3.
      ths. ths. chere.
      eapply (LFREEP en s LBc Lc f m3 off rem rA rB rBig _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                l0 (Z_to_bv 64 hBv) l3 l4 l8 (Z_to_bv 64 dBv) l11 ta tb qn ql namev nn LB2 dBv hBv (str ++ Z_to_bv 8 0 :: bn2) bs KY KX methY methX lenY maxY lenX maxX);
        [| | clear - REM; lia| exact RA3| exact RB2| pose proof (wBig_mono lenX (lenX + 1) ltac:(clear - LXY; lia)); clear - RBIG H LXY; lia| clear - LSUM2; lia| unfold pem_loc; exact LOC3
        | exact OWNN| clear - NN; lia| exact LBN| exact NMC3| exact NUL| exact OWNL| exact LBS| exact LBC3| exact MBY3| exact MBX3| | | | | exact OUT3].
      + lazymatch goal with H : pem_com _ en s LBc Lc f m3 _ _ _ _ _ |- _ => exact H end.
      + lazymatch goal with H : _ (e_E en) [] m3 |- _ => exact H end.
      + intros b Hb. destruct (ELB _ Hb) as [X|X]; [left; exact X| right]. rewrite !in_app_iff in X |- *. clear - X. tauto.
      + intros b Hb X. apply (CFRESH _ Hb). rewrite !in_app_iff in X |- *. clear - X. tauto.
      + intros q nm Hq X. apply (EL _ _ Hq). rewrite !in_app_iff in X |- *. clear - X. tauto.
      + eapply Permutation_NoDup; [| exact NDT]. apply Permutation_app_tail. rewrite (app_assoc (mbio_blocks KX)), (app_assoc (mbio_blocks KY)).
        apply Permutation_app; [apply Permutation_app_comm| apply Permutation_refl].
    - (* [comment removed for export] *)
      clear K3. chere.
      eapply (LFREEP en s LBc Lc f m3 off rem rA rB rBig _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                l0 l1 l3 l4 l8 (Z_to_bv 64 dBv) l11 ta tb qn ql namev nn LB2 hBv dBv (str ++ Z_to_bv 8 0 :: bn2) bs KX KY methX methY lenX maxX lenY maxY);
        [| | clear - REM; lia| exact RA3| exact RB2| pose proof (wBig_mono lenY (lenY + 1) ltac:(clear - LXY; lia)); clear - RBIG H LXY; lia| exact LSUM2| unfold pem_loc; exact LOC3
        | exact OWNN| clear - NN; lia| exact LBN| exact NMC3| exact NUL| exact OWNL| exact LBS| exact LBC3| exact MBX3| exact MBY3| exact ELB| exact CFRESH| exact EL| exact NDT| exact OUT3].
      + lazymatch goal with H : pem_com _ en s LBc Lc f m3 _ _ _ _ _ |- _ => exact H end.
      + lazymatch goal with H : _ (e_E en) [] m3 |- _ => exact H end.
  Qed.
End W3.
