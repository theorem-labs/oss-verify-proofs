(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore CatSim.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require ExecF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PImg PIosRegs PIosKitA PIosKit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegGhost SegProg SegExplore SegLib SegBridge.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2Entry.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim SjStage1 SjInvPath SjInv SjS1Lem SjS1Bytes SjS1Ghost.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP Require Import S1P_defs S1G_defs S1G_vcs S1G_cert S1G_ok S1G_thm.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import RMallocRep RMallocTree RMalloc_iface ROpNew_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Monad HarnessP ProgP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import RunDraw PU_iface PC_kit PC_s12iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.
Notation mem := (word -> option byte).

Local Notation u := bv_unsigned.

(* [comment removed for export] *)
Lemma wr_at_of_stk : forall m lo hi A n, stk psegs m lo hi -> lo <= A -> A + n <= hi -> 0 <= n -> wr_at psegs m A n.
Proof.
  intros m lo hi A n (H0 & H1 & H) H2 H3 H4. split; [lia|]. split; [lia|]. intros i Hi. apply (H (A + i)). lia.
Qed.

Lemma wr_at_wmono_b : forall m m' A n, wr_at psegs m A n -> wmono psegs m m' -> wr_at psegs m' A n.
Proof. intros m m' A n (H0 & H1 & H) W. split; [exact H0|]. split; [exact H1|]. intros i Hi. apply W. apply H. exact Hi. Qed.
Lemma wr_at_sub_b : forall m A n A' n', wr_at psegs m A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' -> wr_at psegs m A' n'.
Proof. intros m A n A' n' (H0 & H1 & H) Ha Hb Hn. split; [lia|]. split; [lia|]. intros i Hi. replace (A' + i) with (A + (A' - A + i)) by lia. apply H. lia. Qed.
(* [comment removed for export] *)
Lemma bytes_at_of_mbytes : forall m A bs, mbytes m A bs -> 0 <= A -> A + Z.of_nat (length bs) <= 2^64 -> bytes_at psegs m A bs.
Proof.
  intros m A bs H H0 H1. split; [exact H0|]. split; [exact H1|]. intros i Hi. unfold mrd, wa.
  rewrite (H (Z.of_nat i) ltac:(lia)). rewrite Nat2Z.id. symmetry. apply nth_error_nth'. exact Hi.
Qed.
(* [comment removed for export] *)
Lemma rw_cells_of : forall m A cs, cells_wf cs -> bytes_at psegs m A (cells_bytes cs) -> wr_at psegs m A (Z.of_nat (cells_size cs)) ->
  rw_cells psegs m A cs.
Proof. intros m A cs H1 H2 H3. split; [split; assumption| exact H3]. Qed.

(* [comment removed for export] *)
Lemma mbytes_of_bytes_at : forall m A bs, bytes_at psegs m A bs ->
  (A + Z.of_nat (length bs) <= 0x10000 \/ 0xa9000 <= A) -> mbytes m A bs.
Proof.
  intros m A bs (H0 & H1 & HB) HA i Hi. specialize (HB (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in HB by lia.
  rewrite ref_mrd_overlay in HB by (unfold wa; rewrite unsigned_lit by lia; lia).
  unfold wa in HB. rewrite HB. rewrite (nth_error_nth' bs (Z_to_bv 8 0)) by lia. reflexivity.
Qed.

Ltac mods := repeat match goal with |- context [?x mod 18446744073709551616] => rewrite (Z.mod_small x 18446744073709551616) by lia end.

Section CANSEC1. Context {rc : runConstT}.

Theorem s1l_proof : s1l_stmt.
Proof.
  unfold s1l_stmt. intros until lo. intros BB DB DL HB B16 HT HI AT AI DTB DIB DTI WT W16 WI ST LOA LOS SPA SP47 MI FZ A0 A1 A2 A3.
  atop_facts. unfold PS1_STACK in LOS.
  destruct HB as (HB1 & HB2 & HB3 & HB4). destruct HT as (HT1 & HT2 & HT3 & HT4). destruct HI as (HI1 & HI2 & HI3 & HI4).
  assert (ZD0 : 0 <= zlength d) by (unfold zlength; lia).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  set (ZL := [u ra; u sp; u gp; u tp; u s0; u s1; u s2; u s3; u s4; u s5; u s6; u s7; u s8; u s9; u s10; u s11;
              THIS; BUF; zlength d; ASI; 0; u t0; u t1; u t2; u a4; u a5; u a6; u a7; u t3; u t4; u t5; u t6]).
  assert (HR : regs_ok (mkEZ ZL) (ST.t_regs G0)
                 (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)).
  { apply regs_ok_mkR. subst a0 a1 a2 a3.
    rewrite <- (map_map (fun k => sr_get (ST.t_regs G0) (Z_to_bv 5 k)) (edenot (mkEZ ZL))).
    replace (map (fun k => sr_get (ST.t_regs G0) (Z_to_bv 5 k)) rkeys) with (tl T0_regs) by (vm_compute; reflexivity).
    unfold T0_regs, tl, ZL. cbn [map edenot mkEZ ev nth V]. rewrite !Z_to_bv_bv_unsigned. reflexivity. }
  (* [comment removed for export] *)
  assert (WSP : wr_at psegs m (bv_unsigned sp - 416) 416) by (eapply wr_at_of_stk; [exact ST| lia| lia| lia]).
  assert (BUFL : Z.of_nat (length (s1buf d)) = zlength d + 64) by (unfold s1buf, zlength; rewrite length_map, length_app, repeat_length; lia).
  assert (ROM : forall i, 0 <= i < Z.of_nat (length (s1buf d)) -> seg_rom psegs (Z_to_bv 64 (BUF + i)) = None).
  { intros i Hi. apply ref_seg_rom_none. rewrite unsigned_lit by lia. lia. }
  assert (HK : know_ok SG (mkEZ ZL) m (ST.t_know G0)).
  { unfold G0, T0, kn_glob, ST.t_know. unfold ZL.
    repeat apply Forall_cons; try apply Forall_nil.
    all: unfold idxlen, add, mul, vLEN, vSP, vBUF, vTHIS, vA1, V.
    all: first
      [ kz_pure ltac:(mods; lia)
      | (eapply kz_word_cells; [reflexivity | lia | exact W16 | cbn [zden nth]; mods; instantiate (1 := 0%nat); cbn; lia | reflexivity])
      | (eapply kz_wr_sub; [reflexivity | exact WSP | cbn [zden nth]; mods; lia | cbn [zden nth]; mods; lia
                             | cbn [zden nth]; mods; lia])
      | (eapply kz_wr_sub; [reflexivity | exact WT | cbn [zden nth]; mods; lia | cbn [zden nth]; mods; lia
                             | cbn [zden nth]; mods; lia])
      | (eapply kz_wr_sub; [reflexivity | exact WI | cbn [zden nth]; mods; lia | cbn [zden nth]; mods; lia
                             | cbn [zden nth]; mods; lia])
      | (eapply kz_unk_bytes; [reflexivity | exact BB | exact ROM | cbn [zden nth]; mods; lia
                               | cbn [zden nth]; mods; lia | cbn [zden nth]; mods; lia])
      | (apply kz_img; [lia | lia | exact MI | intros x Hx; rewrite p_ro_addr; apply andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia]) ]. }
  assert (HG : SG.gholds (s1_gp d) (mkEZ ZL) m (ST.t_ghost G0)).
  { unfold G0, ST.t_ghost, gBUF, SG.gholds. apply Forall_cons; [| apply Forall_nil].
    cbn [ST.g_id ST.g_args map]. rewrite !zden_ok by reflexivity. unfold ZL, vBUF, vLEN, V. cbn [zden nth].
    cbn [s1_gp]. unfold g_buf. rewrite !unsigned_lit by lia.
    split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact DB|].
    apply mbytes_of_bytes_at; [exact BB| rewrite BUFL; lia]. }
  assert (RF : rfull (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)) by apply rfull_mkR.
  eapply evt_cut.
  { change (Z_to_bv 64 PSTAGE1) with (Z_to_bv 64 (ST.t_pc G0)).
    exact (s1g_evt d (mkEZ ZL) m (seg_rom psegs) _ F fc RF HR HK HG MI FZ). }
  intros ms' XP.
  destruct XP as (X & E' & m' & R' & F' & fc' & HX & -> & FZ' & RF' & HR' & HK' & HG' & GA & EB & FRM & WM' & MI' & STK').
  destruct HX as [<-|[]].
  (* [comment removed for export] *)
  assert (RR : R' = mkR (ev E' 0) (ev E' 1) (ev E' 2) (ev E' 3) (ev E' 22) (ev E' 23) (ev E' 24) (ev E' 4) (ev E' 5) (ev E' 21)
                        (ev E' 25) (ev E' 26) (ev E' 27) (ev E' 28) (ev E' 29) (ev E' 30) (ev E' 31) (ev E' 6) (ev E' 7) (ev E' 8) (ev E' 9)
                        (ev E' 10) (ev E' 11) (ev E' 12) (ev E' 13) (ev E' 14) (ev E' 15) (ev E' 32) (ev E' 33) (ev E' 34) (ev E' 35)).
  { rewrite (regs_ok_canon _ _ _ RF' HR'). reflexivity. }
  assert (GL : forall j, (j < 21)%nat -> ev E' j = Z_to_bv 64 (nth j ZL 0)) by (intros j Hj; rewrite <- (GA j Hj); reflexivity).
  rewrite (GL 0%nat ltac:(lia)), (GL 1%nat ltac:(lia)), (GL 2%nat ltac:(lia)), (GL 3%nat ltac:(lia)), (GL 4%nat ltac:(lia)), (GL 5%nat ltac:(lia)),
    (GL 6%nat ltac:(lia)), (GL 7%nat ltac:(lia)), (GL 8%nat ltac:(lia)), (GL 9%nat ltac:(lia)), (GL 10%nat ltac:(lia)), (GL 11%nat ltac:(lia)),
    (GL 12%nat ltac:(lia)), (GL 13%nat ltac:(lia)), (GL 14%nat ltac:(lia)), (GL 15%nat ltac:(lia)) in RR.
  unfold ZL in RR. cbn [nth] in RR. rewrite !Z_to_bv_bv_unsigned in RR. subst R'.
  assert (ETHIS : ev E' 16 = Z_to_bv 64 THIS) by (rewrite (GL 16%nat ltac:(lia)); reflexivity).
  assert (EASI : ev E' 19 = Z_to_bv 64 ASI) by (rewrite (GL 19%nat ltac:(lia)); reflexivity).
  change (ST.t_pc GX_) with 0x28f30.
  zstep.
  apply evt_done. unfold s1l_post.
  exists (ev E' 22), (ev E' 23), (ev E' 24), (ev E' 25), (ev E' 26), (ev E' 27), (ev E' 28), (ev E' 29), (ev E' 30), (ev E' 31),
         (ev E' 32), (ev E' 33), (ev E' 34), (ev E' 35), F', fc', m', (u (ev E' 21)).
  split; [rewrite Z_to_bv_bv_unsigned; reflexivity|].
  split; [exact FZ'|]. split; [pose proof (bv_unsigned_in_range 64 (ev E' 21)) as Rr; unfold bv_modulus in Rr; exact Rr|].
  split; [exact MI'|]. split; [exact (STK' _ _ ST)|]. split; [exact WM'|].
  (* [comment removed for export] *)
  split.
  { intros x Hx. apply FRM. unfold SP.outside_wins, S1G, SP.p_W.
    pose proof (bv_unsigned_in_range 64 x) as Rx. unfold bv_modulus in Rx. cbn in Rx.
    unfold s1_win, PS1_STACK in Hx. cbn [outside] in Hx.
    repeat apply Forall_cons; try apply Forall_nil; cbn [SP.win_den]; rewrite !u_zden by reflexivity;
      unfold ZL, idxlen, add, mul, vSP, vTHIS, vA1, vLEN, V; cbn [zden nth]; mods; lia. }
  (* [comment removed for export] *)
  inversion HG' as [|? ? G1 HG'']. inversion HG'' as [|? ? G2 _]. clear HG' HG'' G1.
  cbn [ST.g_id ST.g_args map gX] in G2. cbn [s1_gp] in G2. unfold vA1, vTHIS, V in G2. cbn [edenot] in G2.
  rewrite ?ETHIS, ?EASI in G2. rewrite ?unsigned_lit in G2 by lia.
  destruct G2 as [GC GS].
  split; [exact GC|].
  pose proof (know_nth _ _ _ _ 1%nat _ HK' eq_refl) as K72. pose proof (know_nth _ _ _ _ 2%nat _ HK' eq_refl) as K80.
  pose proof (kx_word_g SG 21 ZL E' m' vTHIS 72 8 vBUF GA (eq_sym EB) eq_refl eq_refl eq_refl K72) as B72.
  pose proof (kx_word_g SG 21 ZL E' m' vTHIS 80 8 vLEN GA (eq_sym EB) eq_refl eq_refl eq_refl K80) as B80.
  unfold ZL, vTHIS, vBUF, vLEN, V in B72, B80. cbn [zden nth] in B72, B80. rewrite (Z.mod_small THIS) in B72, B80 by lia.
  split.
  { apply rw_cells_of; [cbn; repeat split; exact I| |].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. unfold le8. apply bytes_at_app_join; [exact B72|].
      rewrite length_word_to_le_bytes. replace (THIS + 72 + Z.of_nat 8) with (THIS + 80) by lia. exact B80.
    - eapply wr_at_sub_b; [eapply wr_at_wmono_b; [exact WT| exact WM']| lia| cbn; lia| cbn; lia]. }
  intros R0. destruct (GS R0) as (GN & GA1 & GM & GT & G24).
  rewrite unsigned_lit in G24 by lia. rewrite unsigned_lit in GM by lia. rewrite unsigned_lit in GA1 by lia.
  pose proof (know_nth _ _ _ _ 0%nat _ HK' eq_refl) as K8.
  pose proof (SB.kx_word SG E' m' vTHIS 8 4 (V 36) K8) as B8. unfold vTHIS, V in B8. cbn [edenot] in B8. rewrite ETHIS, unsigned_lit in B8 by lia.
  pose proof (bv_unsigned_in_range 64 (ev E' 36)) as R36. unfold bv_modulus in R36. cbn in R36.
  assert (E36 : ev E' 36 = Z_to_bv 64 (zlength (snd (scan d)))) by (apply bv_eq; rewrite GN; rewrite unsigned_lit; [reflexivity| lia]).
  rewrite E36 in B8.
  destruct (scan d) as [ok idx] eqn:ES. cbn [fst snd] in *.
  assert (OK : ok = true) by (apply GC; exact R0). subst ok.
  pose proof (scan_S1OUT d idx ES) as S1O. destruct S1O as [NIX _ _ _ _ _].
  split; [|split].
  - apply rw_cells_of; [cbn; repeat split; exact I| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact B8|].
    eapply wr_at_sub_b; [eapply wr_at_wmono_b; [exact WT| exact WM']| lia| cbn; lia| cbn; lia].
  - apply rw_cells_of; [cbn; repeat split; exact I| cbn [cells_bytes cbytes]; rewrite app_nil_r; apply bytes_at_of_mbytes; [exact G24| lia| cbn; lia]|].
    eapply wr_at_sub_b; [eapply wr_at_wmono_b; [exact WT| exact WM']| lia| cbn; lia| cbn; lia].
  - assert (UL : length (u32bytes (idx ++ [zlength d; zlength d; 0])) = (4 * (length idx + 3))%nat)
      by (rewrite u32bytes_length, length_app; cbn [length]; lia).
    apply rw_cells_of; [cbn; split; [exact UL| exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r; apply bytes_at_of_mbytes; [exact GM| lia| rewrite UL; unfold zlength in GN, NIX; lia]|].
    eapply wr_at_sub_b; [eapply wr_at_wmono_b; [exact WI| exact WM']| lia| cbn; unfold zlength in *; lia| cbn; lia].
Qed.
End CANSEC1.
