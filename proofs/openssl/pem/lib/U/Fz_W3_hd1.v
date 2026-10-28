(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude DecodeC Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn LhRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_M_malloc Fz_M_zalloc Fz_M_free Fz_M_secure
     Fz_M_clear_free Fz_M_clear_realloc Fz_W1_defs Fz_W1_sync Fz_W1_growc Fz_W1_writec Fz_W1_read Fz_W3_iface Fz_W2_rep Fz_W3_defs Fz_W3_end Fz_W3_tail Fz_W3_dec
     Fz_W3_endl Cs_pad F_memchr F_strncmp.
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
Definition pem_end_str : list byte := Eval vm_compute in (match image_bytes Image.usegs 0x255f0 9 with Some bs => bs | None => [] end).
Lemma pem_end_ro : ro_bytes Image.usegs 0x255f0 pem_end_str.
Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma pem_end_len : length pem_end_str = 9%nat. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Ltac hd_core_by ER BLEN SA SB SBIG MAXT MAXO DNT DNO GOT ROLE OWNN NN LBN NMC NONUL OWNL LBS LBC MBT MBO ELB CFRESH EL NDT OUT :=
  unfold hd_core; cbv zeta;
  split; [exact ER|]; split; [exact BLEN|]; split; [exact SA|]; split; [exact SB|]; split; [exact SBIG|];
  split; [exact MAXT|]; split; [exact MAXO|]; split; [exact DNT|]; split; [exact DNO|]; split; [exact GOT|]; split; [exact ROLE|];
  split; [exact OWNN|]; split; [exact NN|]; split; [exact LBN|]; split; [exact NMC|]; split; [exact NONUL|]; split; [exact OWNL|]; split; [exact LBS|];
  split; [exact LBC|]; split; [exact MBT|]; split; [exact MBO|]; split; [exact ELB|]; split; [exact CFRESH|]; split; [exact EL|];
  split; [exact NDT| exact OUT].
Ltac hd_inv_by ER REM BLEN SA SB SBIG LSUM MAXT MAXO DNT DNO GOT ROLE LEN OWNN NN LBN NMC NONUL OWNL LBS LBC NULk MBT MBO ELB CFRESH EL NDT OUT :=
  unfold hd_inv; split; [hd_core_by ER BLEN SA SB SBIG MAXT MAXO DNT DNO GOT ROLE OWNN NN LBN NMC NONUL OWNL LBS LBC MBT MBO ELB CFRESH EL NDT OUT|];
  split; [exact REM|]; split; [exact LSUM|]; split; [exact LEN| exact NULk].

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
  Local Notation com_segI := (com_seg libenv libenv_fp libenv_agree libenv_fp_where).
  Local Notation er0_segI := (er0_seg errst_at_rest errst_fp errst_rest_agree errst_fp_where).

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
  Theorem HD1_proof : forall N, HD2_at libenv errst_at_rest errst_live N -> HD_at libenv errst_at_rest errst_live N.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros N HD2P en s LBc Lc f m off rem rA rB rBig xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 l1 l2 l7 l9 ta tb
           qn ql namev nn LB2 hBv dBv tmpv ov got prev endv len str bn2 bs KT KO methT methO lenT maxT lenO maxO.
    intros MEAS COM INV LOC ENDV PREV. unfold HD2_at, J_HD2 in HD2P.
    pose proof INV as ((ER0 & BLEN & SA & SB & SBIG & MAXT & MAXO & DNT & DNO & GOT & ROLE & OWNN & NN & LBN & NMC & NONUL & OWNL & LBS & LBC
                      & MBT & MBO & ELB & CFRESH & EL & NDT & OUT) & REM & LSUM & LEN & NULk).
    pose proof COM as (CST & FR0 & LE & INCL0 & INCL & NTL & OWNE & MB & OFF & EVF & FU & ROOM & CG & RA0 & RB0 & RBIG0 & PLB & PLC & SAVED & SLO & PLBB & FLR & AL16 & EPE & EK).
    pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
    unfold BPUTS_STACK, WRITE_STACK, GROW_STACK, J_HD, GLOBALS_TOP in *.
    assert (WSP : 48 + 32 + (64 + (96 + CCR_STACK + CSM_STACK + CSF_STACK)) = 25200) by (unfold CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK; clear; lia).
    rewrite WSP in SLO. clear WSP.
    pose proof (bv_unsigned_in_range _ (e_sp en)) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold e_PL in *.
    rewrite unsigned_lit in ST by (clear - SPR SLO LO GLO; lia). rewrite unsigned_lit in SPB by (clear - SPR SLO LO GLO; lia).
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNL)) as (RL1 & _ & _ & RL2 & _).
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNN)) as (RN1 & _ & _ & RN2 & _).
    unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in RL2, RN2.
    assert (INE : In (e_pe en, e_E en, 904) LBc) by exact (proj1 OWNE).
    pose proof (rw_cells_bytes_at _ _ _ _ LBC) as LBB. cbn [cells_bytes cbytes] in LBB. rewrite app_nil_r in LBB.
    hide ROLE. hide ELB. hide ROOM. hide CG.
    pose proof (munch_refl [(bv_unsigned (e_sp en) + -176, bv_unsigned (e_sp en) + -168)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold pem_loc in LOC.
    (* [comment removed for export] *)
    cprefix.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m0 _) => lazymatch type of LOC with rw_cells _ _ _ ?LC =>
    eapply (evt_cut usegs (fun ms' => exists (y10 : word) (pv : Z) (m1 : mem),
      ms' = MS (mkR xra (wz (bv_unsigned (e_sp en) + -208)) (e_gp en) (e_tp en) t0 t1 t2 (e_sp en) (wz prev) y10 a1 a2 a3 a4 a5 a6 a7
                    (wz PEM_ENDSTR) (wz got) (wz pv) (wz (e_flags en)) (wz hBv) (e_sp en) (wz (bv_unsigned (e_sp en) + 24)) (wz (e_BI en)) (wz LB2) (wz len) t3 t4 t5 t6)
               (e_F en) (wz 0x18832c) (e_fc en) None m1 (seg_rom usegs)
      /\ munch [(bv_unsigned (e_sp en) + -176, bv_unsigned (e_sp en) + -168)]%Z m0 m1 /\ wmono usegs m0 m1 /\ mem_inv usegs m1
      /\ (pv = 0 \/ pv = 1) /\ stk usegs m1 (e_lo en) (bv_unsigned (e_sp en) + -208)
      /\ rw_cells usegs m1 (bv_unsigned (e_sp en) + -208) LC))
    end end.
    { ths. ths. if_cases K0; zify_cond K0.
      - (* [comment removed for export] *) ths. apply evt_done. eexists _, 0, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
        split; [left; reflexivity|]. split; [assumption| exact LOC].
      - (* [comment removed for export] *)
        ths. ths. if_cases KC; zify_cond KC. { exfalso. pose proof alloc_ceiling_lt_2p47 as ACL. clear - KC RL1 RL2 ACL; lia. } clear KC.
        destruct (nth_error bs 253%nat) as [b253|] eqn:Hb; [| exfalso; apply nth_error_None in Hb; rewrite LBS in Hb; clear - Hb; lia].
        pose proof (u8arr_read usegs m LB2 bs 253 b253 (Z_to_bv 64 (LB2 + 253)) (u8arr_of_rw_cells _ _ _ _ _ LBC) Hb ltac:(clear; lia) ltac:(unfold wa; f_equal; clear; lia)) as RD.
        zstep. clear RD. zstep. zstep. ths. apply evt_done. eexists _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
        split; [| split; [assumption| exact LOC]].
        clear. match goal with |- ?x = 0 \/ ?x = 1 => first [destruct (_ <? _); cbn; [right| left]; reflexivity| idtac] end. }
    cbv beta. intros ms1 (y10 & pv & m1 & -> & MU1 & WM1 & MI1 & PV & ST1 & LOC1).
    clear MU WM. transport_after_call usegs m m1 MU1 WM1.
    assert (HW1 : Forall (wfree LBc (e_lo en) (bv_unsigned (e_sp en) + 32) (fun _ : bptr => True)) [(bv_unsigned (e_sp en) + -176, bv_unsigned (e_sp en) + -168)]%Z).
    { apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. clear - SLO; lia. }
    assert (COM1 : pem_com libenv en s LBc Lc f m1 off rem rA rB rBig).
    { eapply (com_segI en s LBc Lc f m off rem rA rB rBig _ m1 (fun _ => True));
        [exact COM| exact MU1| exact WM1| exact MI1| exact ST1| exact HW1| intros; exact I| unfold e_PL; cbn [disjoint_from fst snd]; clear; lia]. }
    assert (ER1 : errst_at_rest (e_E en) [] m1).
    { eapply (er0_segI _ en m m1) with (EX := fun _ => True) (hi := bv_unsigned (e_sp en) + 32); [exact ER0| exact MU1| exact WM1| exact CST| exact INE| apply Forall_cons; [left; cbn [fst snd]; clear - SLO; lia| apply Forall_nil]| exact I]. }
    assert (MBT1 : mbio_rep m1 LBc Lc KT tmpv methT lenT maxT 0).
    { eapply (mb_seg _ m m1) with (EX := fun _ => True) (hi := bv_unsigned (e_sp en) + 32); [exact MBT| exact CST| exact MU1| exact WM1| apply Forall_cons; [left; cbn [fst snd]; clear - SLO; lia| apply Forall_nil]| intros; exact I]. }
    assert (MBO1 : mbio_rep m1 LBc Lc KO ov methO lenO maxO 0).
    { eapply (mb_seg _ m m1) with (EX := fun _ => True) (hi := bv_unsigned (e_sp en) + 32); [exact MBO| exact CST| exact MU1| exact WM1| apply Forall_cons; [left; cbn [fst snd]; clear - SLO; lia| apply Forall_nil]| intros; exact I]. }
    pose proof COM1 as (CST1 & _). clear COM CST ER0 MBT MBO HP MI ST.
    (* [comment removed for export] *)
    pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    eapply (evt_cut usegs (fun ms' => exists (yra z5 z6 z7 y10 y11 y12 y13 y14 y15 y16 y17 z28 z29 z30 z31 : word) (got1 : Z) (m2 : mem),
      ms' = MS (mkR yra (wz (bv_unsigned (e_sp en) + -208)) (e_gp en) (e_tp en) z5 z6 z7 (e_sp en) (wz prev) y10 y11 y12 y13 y14 y15 y16 y17
                    (wz PEM_ENDSTR) (wz got1) (wz pv) (wz (e_flags en)) (wz hBv) (e_sp en) (wz (bv_unsigned (e_sp en) + 24)) (wz (e_BI en)) (wz LB2) (wz len) z28 z29 z30 z31)
               (e_F en) (wz 0x188348) (e_fc en) None m2 (seg_rom usegs)
      /\ munch [] m1 m2 /\ wmono usegs m1 m2 /\ mem_inv usegs m2 /\ 0 <= got1 <= 2 /\ (got1 = 2 <-> got = 2) /\ stk usegs m2 (e_lo en) (bv_unsigned (e_sp en) + -208))).
    { ths. if_cases K1; zify_cond K1.
      - (* [comment removed for export] *) apply evt_done. do 16 eexists _. exists got, m1. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI1|].
        split; [clear - GOT; lia|]. split; [clear; tauto| exact ST1].
      - (* [comment removed for export] *)
        assert (MOK : memchr_ok LB2 (58 mod 256) len bs).
        { unfold memchr_ok. destruct (find_byte _ _); [left|]; rewrite LBS; clear - LEN; lia. }
        ths. ths. ths. ths.
        tcall (memchr_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bs).
        all: try first [eassumption | clear - RL1 RL2 LO SLO SPR; lia].
        cbv beta delta [mkR]. zstep. apply evt_done. do 16 eexists _. eexists _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
        split; [| split; [| assumption]]; clear - K1; destruct (_ <? _); cbn; lia. }
    cbv beta. intros ms2 (yra & z5 & z6 & z7 & y10' & y11 & y12 & y13 & y14 & y15 & y16 & y17 & z28 & z29 & z30 & z31 & got1 & m2 & -> & MU2 & WM2 & MI2 & GOT1 & GOT12 & ST2).
    clear MU WM. transport_after_call usegs m1 m2 MU2 WM2. pure_sync m2.
    lazymatch goal with H1 : mbio_rep m2 LBc Lc KT _ _ _ _ _, H2 : mbio_rep m2 LBc Lc KO _ _ _ _ _ |- _ => rename H1 into MBT2; rename H2 into MBO2 end.
    lazymatch goal with H : pem_com _ en s LBc Lc f m2 _ _ _ _ _ |- _ => rename H into COM2 end. lazymatch goal with H : _ (e_E en) [] m2 |- _ => rename H into ER2 end.
    try clear COM1; try clear CST1; try clear ER1; try clear MI1; try clear ST1.
    (* [comment removed for export] *)
    pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    assert (ENB : bytes_at usegs m2 0x255f0 pem_end_str) by (apply ro_bytes_at; [exact MI2| clear; lia| rewrite pem_end_len; clear; lia| exact pem_end_ro]).
    destruct (strncmp_model_total bs pem_end_str 9) as (v3 & V3); [clear; lia| rewrite LBS; clear; lia| rewrite pem_end_len; clear; lia|].
    ths. ths. ths. ths.
    tcall (strncmp_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bs pem_end_str v3).
    all: try first [eassumption | unfold PEM_ENDSTR; eassumption | clear - RL1 RL2 LO SLO SPR; unfold PEM_ENDSTR; lia].
    cbv beta delta [mkR].
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    pose proof COM2 as (CST2 & _). pure_sync m3.
    lazymatch goal with H1 : mbio_rep m3 LBc Lc KT _ _ _ _ _, H2 : mbio_rep m3 LBc Lc KO _ _ _ _ _ |- _ => rename H1 into MBT3; rename H2 into MBO3 end.
    lazymatch goal with H : pem_com _ en s LBc Lc f m3 _ _ _ _ _ |- _ => rename H into COM3 end. lazymatch goal with H : _ (e_E en) [] m3 |- _ => rename H into ER3 end.
    lazymatch goal with H1 : rw_cells usegs m3 (bv_unsigned (e_sp en)) _, H2 : rw_cells usegs m3 namev _, H3 : rw_cells usegs m3 LB2 _ |- _ =>
      rename H1 into OUT3; rename H2 into NMC3; rename H3 into LBC3 end.
    chere. unfold hideP in ROLE, ELB.
    assert (ROLE1 : (got1 <> 2 /\ tmpv = hBv /\ ov = dBv) \/ (got1 = 2 /\ tmpv = dBv /\ ov = hBv)).
    { clear - ROLE GOT12. destruct ROLE as [(R1 & R2 & R3)|(R1 & R2 & R3)]; [left| right]; (split; [tauto| split; assumption]). }
    eapply HD2P with (partv := pv).
    1: exact MEAS. 1: exact COM3.
    1: (hd_inv_by ER3 REM BLEN SA SB SBIG LSUM MAXT MAXO DNT DNO GOT1 ROLE1 LEN OWNN NN LBN NMC3 NONUL OWNL LBS LBC3 NULk MBT3 MBO3 ELB CFRESH EL NDT OUT3).
    1: { unfold pem_loc, e_PL. exact LOC1. }
    1: exact ENDV. 1: exact PREV. 1: exact PV.
    clear - FLR. lazymatch goal with |- 0 <= Z.land ?a ?b < _ =>
      rewrite (Z.land_comm a b); enough (BNN : 0 <= a) by (pose proof (OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.Bytes.land_lt_pow2 b a 8 ltac:(lia) BNN); lia) end.
    apply (proj2 (Z.lor_nonneg _ _)). split; [| lia]. change 18446744073709551615 with (2 ^ 64 - 1). rewrite zb_land_mask by lia. apply Z.mod_pos_bound. lia.
  Qed.
End W3.
