(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Mem Frame Cells Step Arr Exec RzCPS MState. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_defs R_cache_defs R_prim_defs R_glue_defs R_thread R_m2s R_sec_defs R_mmapordie R_secalloc R_comballoc2 R_asan_defs R_allocate1 RT_state RT_rep RT_frame RT_trans RT_maltail RT_reatail RT_malcore_stmt RT_reacore_stmt RT_reacore_case RT_malsec_state.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition front_post (B : Z) (gp s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (mX : mem)
    : machine_state -> Prop :=
  fun ms => exists m1 : mem,
    munch [(B + -248, B + -200)] mX m1 /\ wmono ctasegs mX m1
    /\ rw_cells ctasegs m1 (B + -248) [C8 (Z_to_bv 64 (rz_size n)); C8 (Z_to_bv 64 (needed2 n)); C8 (Z_to_bv 64 8);
                                      C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (Z.b2z (from_primary n))); C8 (Z_to_bv 64 0x19bfbc)]
    /\ secalloc_A1_post (Z_to_bv 64 comballoc_retS) (Z_to_bv 64 (B + -248)) gp (Z_to_bv 64 tpA) (Z_to_bv 64 8) (Z_to_bv 64 n)
         (Z_to_bv 64 8) (Z_to_bv 64 (needed2 n)) (Z_to_bv 64 (rz_size n)) s5 s6 s7 s8 s9 s10 s11 F fc (needed2 n) lo m1 ms.

Section Front.
Variables (Σ : rtsA) (mX : mem) (B : Z) (gp t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z).
Hypothesis Hn : 64512 < n <= 0x8000000.
Hypothesis HA : ART_A Σ mX.
Hypothesis MI : mem_inv ctasegs mX.
Hypothesis ST : stk ctasegs mX lo (B + -200).
Hypothesis LOW : l_ACEIL (lay Σ) <= lo.
Hypothesis LOR : lo + 0x1000 <= B + -200.
Hypothesis SPT : B + 16 <= USTACK_TOP.

Lemma msec_size : 65536 < needed2 n /\ needed2 n mod 8 = 0 /\ needed2 n <= n + 4103 /\ from_primary n = false.
Proof using Hn.
  clear - Hn.
  assert (RZ : rz_size n = 2048) by (unfold rz_size, rz_log; rewrite !(proj2 (Z.leb_gt n _)) by lia; reflexivity).
  assert (RD : rounded n = 8 * ((n + 7) / 8)) by (unfold rounded; rewrite !Z.max_l by lia; reflexivity).
  pose proof (Z.div_mod (n + 7) 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)) as MB.
  assert (FP : from_primary n = false) by (unfold from_primary, needed; rewrite RZ, RD; apply Z.leb_gt; lia).
  unfold needed2, needed. rewrite FP, RZ, RD.
  split; [lia|]. split; [|split; [lia | reflexivity]].
  apply Z.mod_divide; [lia|]. exists ((n + 7) / 8 + 512). lia.
Qed.

(* [comment removed for export] *)
Lemma fs_evt : evt ctasegs (front_post B gp (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 B) (Z_to_bv 64 (0 + - (8)))
                            (Z_to_bv 64 7) (Z_to_bv 64 (l_T (lay Σ))) (Z_to_bv 64 1) F fc n lo mX)
                 (rcore_entry Σ B gp t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc n mX).
Proof using Hn HA MI ST LOW LOR SPT.
  pose proof msec_size as (K1 & K2 & K3 & K4).
  pose proof (ART_consts Σ mX HA) as (_ & MM & _).
  pose proof (ART_sec Σ mX HA) as (_ & _ & _ & PG & _ & _ & NM).
  pose proof (ART_wf Σ mX HA) as (HL & _). pose proof HL as HL'. unfold layout_ok in HL'. destruct HL' as ((Hsp1 & Hsp2) & _).
  unfold l_ACEIL, STACK_WIN, sp_window_lo, sp_window_hi in *.
  assert (RS : 0 <= B + -200 < 2 ^ 64) by (unfold USTACK_TOP in SPT; lia).
  unfold rcore_entry. rewrite K4. cbn [Z.b2z].
  eapply evt_cut.
  { apply (comballoc_big_A_spec (Z_to_bv 64 0x19bfbc) (Z_to_bv 64 (B + -200)) gp (Z_to_bv 64 tpA) t0 t1 t2
             (Z_to_bv 64 0) (Z_to_bv 64 n) (Z_to_bv 64 (l_T (lay Σ) + 208)) a4 a5 a6 a7 (Z_to_bv 64 8) (Z_to_bv 64 (needed2 n))
             (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 B) (Z_to_bv 64 (0 + - (8))) (Z_to_bv 64 7)
             (Z_to_bv 64 (l_T (lay Σ))) (Z_to_bv 64 1) t3 t4 t5 t6 F fc mX (l_ACEIL (lay Σ)) (needed2 n) lo).
    all: rewrite ?unsigned_lit by exact RS.
    1: lia. 1: exact ST. 1: unfold l_ACEIL, STACK_WIN; lia. 1: unfold kHighShadowEnd; lia. 1: lia.
    1: unfold USTACK_TOP in SPT; lia. 1: exact MI. }
  intros ms (t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1).
  rewrite unsigned_lit in MU1, FR1, ST1 by exact RS.
  assert (DJ : forall a k, 0 <= a -> a + k <= 0xbcb000 -> disjoint_from [(B + -200 - 48, B + -200)] a k).
  { intros a k H1 H2. cbn [disjoint_from]. split; [left; lia | exact I]. }
  assert (MM1 : mm_gcells m1).
  { destruct MM as (M1 & M2 & M3 & M4 & M5).
    split; [|split; [|split; [|split]]]; eapply (rw_cells_transport ctasegs _ mX m1); try eassumption; cs_size; apply DJ; lia. }
  assert (PG1 : sec_page m1).
  { unfold sec_page in *. eapply (rw_cells_transport ctasegs _ mX m1); [exact PG | exact MU1 | exact WM1 |].
    cs_size. apply DJ; unfold i_sec_page, INST, g_instance; lia. }
  assert (NM1 : name_cells m1).
  { unfold name_cells in *. destruct NM as (N1 & N2).
    split; eapply (rw_cells_transport ctasegs _ mX m1); try eassumption; cs_size; apply DJ; lia. }
  eapply evt_mono.
  { change (Z_to_bv 64 (INST + 64)) with (Z_to_bv 64 SEC). change (Z_to_bv 64 (INST + 688)) with (Z_to_bv 64 GSTAT).
    change (Z_to_bv 64 comballoc_retS) with (Z_to_bv 64 comballoc_retS).
    apply (secalloc_A1_spec (Z_to_bv 64 comballoc_retS) (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (B + -200)) - 48)) gp (Z_to_bv 64 tpA)
             t0' t1' t2' (Z_to_bv 64 8) (Z_to_bv 64 n) a4' a5' a6' a7' (Z_to_bv 64 8) (Z_to_bv 64 (needed2 n))
             (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 B) (Z_to_bv 64 (0 + - (8))) (Z_to_bv 64 7)
             (Z_to_bv 64 (l_T (lay Σ))) (Z_to_bv 64 1) t3' t4' t5' t6' F fc m1 (needed2 n) lo).
    all: rewrite ?unsigned_lit by (rewrite ?unsigned_lit by exact RS; lia).
    1: lia. 1: lia. 1: exact MM1. 1: exact PG1. 1: exact NM1. 1: exact ST1. 1: unfold kHighShadowEnd; lia. 1: lia.
    1: unfold USTACK_TOP in SPT; lia. 1: exact MI1. }
  intros ms HP. rewrite ?unsigned_lit in HP by (rewrite ?unsigned_lit by exact RS; lia).
  replace (B + -200 - 48) with (B + -248) in * by lia.
  exists m1. split; [exact MU1|]. split; [exact WM1|]. split; [rewrite K4; exact FR1|]. exact HP.
Qed.
End Front.
