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
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy.
     From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_W1_defs Fz_W3_iface Fz_W2_rep Fz_W3_defs Fz_W3_lems. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_W7_perm. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_W7_defs.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation wz := (Z_to_bv 64) (only parsing).

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

  Theorem X7_proof : bio_free_mem_stmt libenv -> err_clear_steady_stmt libenv errst_at_rest errst_live -> X7_stmt libenv errst_at_rest errst_live.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros BF ECL en st LBc Lc f mc K BI len max off top bot strs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1v s2v t3 t4 t5 t6 ol o8 o16 o24.
    intros COM FU MB KFR KL KS LIVE LEN2 SIN SL NDS SFR SLBL LOC. unfold bio_free_mem_stmt in BF. unfold err_clear_steady_stmt in ECL.
    pose proof COM as (CST & FR0 & LE & INCL0 & INCL & NPL & INE & INL & PERM & SAVED & SLO & SPB & B63 & AL16 & EPE & ROOM & PAY & DLEN & NDE & REL).
    pose proof CST as (HP & CO & (errv & AV & SPB' & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
    unfold LX_FUZZ_STACK, J_X7, GLOBALS_TOP in *.
    pose proof (bv_unsigned_in_range _ (w_sp en)) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold w_SP in *.
    rewrite unsigned_lit in ST by (clear - SPR SLO LO GLO; lia). rewrite unsigned_lit in SPB' by (clear - SPR SLO LO GLO; lia).
    pose proof (cstate_nodup _ _ _ _ _ _ _ _ _ CST) as [NDB NDL].
    assert (NKE : ~ mbio_T K (w_pe en)) by (apply KFR; left; exact (w_pe_in _ EPE)).
    pose proof (munch_refl ([] : list (Z * Z)) mc) as MU. pose proof (wmono_refl usegs mc) as WM.
    (* [comment removed for export] *)
    cprefix. ths. ths. chere.
    eapply climpl_seq.
    { destruct MB as [BM MBX]. eapply BF with (LBL := w_LBL en) (E := w_E en) (lo := w_lo en) (B := w_B en);
        [pose proof (mbio_blocks_len K); clear - FU H; lia| exact CST| rewrite unsigned_lit by lia; unfold BFREE_STACK; clear - SLO; lia| rewrite unsigned_lit by lia; clear - AL16; Z.div_mod_to_equations; lia| exact LE| exact INCL| exact KL| exact MBX| reflexivity]. }
    cbv beta. intros f1 L1 st1 ms1 (v1 & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & (-> & LE1 & KB1 & KL1)).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM1 by lia.
    pose proof FRM1 as (CFR1 & KP1 & _).
    pose proof (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [NDB1 NDL1].
    assert (PERM1 : Permutation L1 (bents strs ++ w_L en)).
    { eapply (perm_remove_ids Lc L1 (mbk_ents K max) (bents strs ++ w_L en) (mbio_blocks K)); [rewrite app_assoc; exact PERM| exact NDL| exact NDL1| | intros [q nm]; exact (KL1 q nm)].
      intros q. unfold mbio_blocks, mbk_ents. rewrite map_app, !in_app_iff. destruct (k_d K); cbn [map fst In]; tauto. }
    assert (INE1 : In (w_pe en, w_E en, 904) LB1) by (apply KB1; split; [exact INE| unfold blk_id; cbn [fst]; intros X; exact (NKE (proj2 (mbio_T_blocks _ _) X))]).
    assert (INL1 : In (w_pe en, w_enm en) L1) by (apply KL1; split; [exact INL| intros X; exact (NKE (proj2 (mbio_T_blocks _ _) X))]).
    assert (INCL1 : incl_blocks (w_LBL en) LB1) by (intros b Hb; apply KB1; split; [exact (INCL _ Hb)| intros X; exact (KL _ Hb (proj2 (mbio_T_blocks _ _) X))]).
    assert (SIN1 : Forall (fun b => In b LB1) strs).
    { apply Forall_forall. intros b Hb. apply KB1. split; [exact (proj1 (Forall_forall _ _) SIN b Hb)| intros X; exact (KS _ Hb (proj2 (mbio_T_blocks _ _) X))]. }
    assert (SL1 : strs_inL L1 strs).
    { eapply strs_inL_keep; [exact SL| intros q nm Hq NX; apply KL1; split; [exact Hq| exact NX]| intros b Hb X; exact (KS _ Hb (proj2 (mbio_T_blocks _ _) X))]. }
    assert (LIVE1 : errst_live (w_E en) top bot strs m1).
    { eapply errst_live_agree; [exact LIVE|]. eapply agree_on_mono; [exact CFR1|]. cbv beta. intros a Ha. right; left.
      destruct (errst_fp_where _ _ _ Ha) as [R|(b & Hb & Rb)].
      - exists (w_pe en, w_E en, 904). split; [exact INE|]. split; [exact NKE| unfold blk_addr, blk_size; cbn [fst snd]; exact R].
      - exists b. split; [exact (proj1 (Forall_forall _ _) SIN b Hb)|]. split; [exact (KS _ Hb)| exact Rb]. }
    pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR0 FRM1 ltac:(clear; lia) ltac:(intros a X; exact X) ltac:(intros q Hq _; exact (KFR q Hq))) as FRa.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 SAVED ltac:(clear; lia)) as SAVED1. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 LOC ltac:(clear; lia)) as LOC1.
    pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _). rewrite unsigned_lit in ST1 by lia.
    clear MU WM CST HP MI ST ERR LATCH LXS CIMG FRM1 CFR1.
    pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    (* [comment removed for export] *)
    cprefix. ths. chere.
    eapply climpl_seq.
    { eapply ECL with (LBL := w_LBL en) (E := w_E en) (enm := w_enm en) (top := top) (bot := bot) (lo := w_lo en) (B := w_B en) (strs := strs);
        [pose proof (mbio_blocks_len K); clear - FU FU1 LEN2 H; lia| exact CST1| rewrite unsigned_lit by lia; unfold ERRN_STACK; clear - SLO; lia| exact LE1| exact INCL1| exact SLBL
        | split; [exact INE1| exact INL1]| exact LIVE1|].
      apply Forall_forall. intros b Hb. destruct b as [[p A] n]. unfold blk_id, blk_addr, blk_size; cbn [fst snd]. split.
      - split; [exact (proj1 (Forall_forall _ _) SIN1 _ Hb)| exact (proj1 (proj1 (Forall_forall _ _) SL1 _ Hb))].
      - intros E. apply (SFR _ Hb). left. unfold blk_id; cbn [fst]. rewrite E. exact (w_pe_in _ EPE). }
    cbv beta. intros f2 L2 st2 ms2 (v2 & m2 & LB2 & RET & FU2 & GR2 & CST2 & FRM2 & (KB2 & KL2 & LE2 & REST2)).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM2 by lia.
    pose proof FRM2 as (CFR2 & KP2 & _).
    pose proof (cstate_nodup _ _ _ _ _ _ _ _ _ CST2) as [NDB2 NDL2].
    assert (PERM2 : Permutation L2 (w_L en)).
    { eapply (perm_remove_ids L1 L2 (bents strs) (w_L en) (map blk_id strs)); [exact PERM1| exact NDL1| exact NDL2| intros q; rewrite map_fst_bents; tauto| intros [q nm]; exact (KL2 q nm)]. }
    assert (INE2 : In (w_pe en, w_E en, 904) LB2).
    { apply KB2. split; [exact INE1|]. intros Hb. apply (SFR _ Hb). left. unfold blk_id; cbn [fst]. exact (w_pe_in _ EPE). }
    pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FRa FRM2 ltac:(clear; lia) ltac:(intros a X; exact X)
                  ltac:(intros q Hq NT [X|X]; [exact (NT (eq_sym X))| apply in_map_iff in X; destruct X as (b & <- & Hb); exact (SFR _ Hb Hq)])) as FRb.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 SAVED1 ltac:(clear; lia)) as SAVED2. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 LOC1 ltac:(clear; lia)) as LOC2.
    pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _). rewrite unsigned_lit in ST2 by lia.
    clear MU WM CST1 HP1 MI1 ST1 FRM2 CFR2 SAVED1 LOC1 FRa LIVE1.
    pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    (* [comment removed for export] *)
    unfold w7_saved in SAVED2.
    cprefix. ths. ths. ths. ths. ths.
    assert (FRj : rw_cells usegs m2 (bv_unsigned (w_sp en) + -64) ([C8 ol; C8 o8; C8 o16; C8 o24] ++ w7_saved en)).
    { apply (proj2 (rw_cells_app usegs m2 _ _ _)). split; [exact LOC2|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
      replace (bv_unsigned (w_sp en) + -64 + 32) with (bv_unsigned (w_sp en) + -32) by (clear; lia). exact SAVED2. }
    clear LOC2 SAVED2.
    lazymatch goal with H : stk usegs _ (w_lo en) _ |- _ => rename H into STe end.
    eapply stk_release in FRj; [| exact STe| clear - SLO LO GLO; lia]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ app length] in FRj.
    replace (bv_unsigned (w_sp en) + -64 + 64) with (bv_unsigned (w_sp en)) in FRj by (clear; lia). clear STe.
    ths. ths. chere. apply climpl_done.
    try replace (bv_unsigned (w_sp en) + 0) with (bv_unsigned (w_sp en)) by (clear; lia). try rewrite Z_to_bv_bv_unsigned.
    lazymatch goal with H : stk usegs m2 (w_lo en) _ |- _ => rename H into STf end. lazymatch goal with H : mem_inv usegs m2 |- _ => rename H into MIf end.
    unfold w7_post. do 14 eexists. exists m2, LB2. split; [reflexivity|].
    split. { eapply (cstate_seg [] _ _ _ _ m2 m2 _ (w_sp en) _ (w_lo en) (w_B en) (bv_unsigned (w_sp en))); [exact CST2| apply munch_refl| apply wmono_refl| exact MIf| apply Forall_nil| clear - SLO; lia| exact SPB| cbn; exact I| exact STf| exact SPB]. }
    split; [exact FRb|]. split; [exact PERM2|]. split; [exact LE2|]. split; [exact REST2| exact INE2].
  Qed.
End W7.
