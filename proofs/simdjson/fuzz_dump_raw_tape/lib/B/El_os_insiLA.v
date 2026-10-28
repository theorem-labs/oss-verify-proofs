(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image RzCPS FP ZBridge.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import Prelim Monad PrintfModel PrintfFormats.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Export FX_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac Startup_glue Pj_steps Pj_loc_kit Pj_os_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Printf_mlib El_fmt_facts.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout R_m2s I_consts I_qck D_kit D_clx RT_iface RT_iface2 RT_iface3 F_achk Fe_icalls I_pchead I_vprintfw I_vfsn6 I_vsn6 Sj_akit Sj_acps Sj_hkit Sj_num_akit Pj_defsA Pj_os_defsA Pj_loc_getA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import El_os_xsputnA El_np_wgiA El_np_intA El_ins_ifaceA El_os_insA El_os_insiA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Export El_os_defsA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.

Section Lift.
Local Open Scope Z_scope.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis RC2 : rt_contracts2 RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis RIP : rip_stmt.
Hypothesis AF_IC : forall Σ m, ART RT Σ m -> ictx m.
Hypothesis AF_SHW : forall Σ m p n, ART RT Σ m -> (0 < n)%Z -> rng_class RT Σ p n -> qc_words m p n /\ region_in_mem p n.
Hypothesis DCC : forall Σ m, ART RT Σ m -> el_dccA m.
Hypothesis AF_NP : forall Σ m, ART RT Σ m -> rod_chk m /\ rod_chk_fp m /\ ifx_real m /\ pctx m /\ pfcells6 m.

Local Ltac ul := unfold EL_INS_STACK_A, EL_NP_STACK_A, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, kHighShadowEnd, SHADOW_LO, SHADOW_HI in *; lia.

Theorem ins_i_okA : ins_i_cpsA RT PMc.
Proof using AF RC RC2 FDO MST RIP AF_IC AF_SHW DCC AF_NP.
  unfold ins_i_cpsA, ins_cpsA. intros until m. intros FDO' MST' INF FLO FHI AL16 OSW FOK HULL LB TPC SSP RV FRM ART0 MI ST LOW LOR SPT Q32 FRB CRB HK.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_frames_range RT AF Σ m fO kO ART0 INF) as (F0 & FTOP & _ & FLIVE).
  pose proof (af_frames_align RT AF Σ m fO kO ART0 INF) as (_ & FSEG).
  pose proof (af_frames_hi RT AF Σ m fO kO ART0 INF) as FHI2.
  remember (fs_size kO) as FSZ eqn:EFSZ.
  assert (LO0 : 0 <= lo) by (destruct ST as (? & ? & _); lia).
  assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; ul).
  assert (OSLO : OS + 288 <= lo) by (clear - FHI FTOP LOW; ul).
  destruct OSW as (pb & pp & ep & dum & j148 & j284 & OSF & PI).
  destruct SSP as (canary & SSP1 & SSP2). destruct HULL as [_ SHZ].

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut.
  { eapply (ins_i_seg1 ra (Z_to_bv 64 q) gp (Z_to_bv 64 TPV_A) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo OS fill v pp ep pb dum j148 j284 canary);
      rewrite ?EQ; first [exact ST| exact OSF| exact PI| exact FOK| exact RV| exact TPC| split; [exact SSP1| exact SSP2]| exact FRM| exact LB| exact (DCC Σ m ART0)| exact MI| reflexivity| ul]. }
  cbv beta. intros ms1 PO. unfold insi1_post in PO. rewrite !EQ in PO.
  destruct PO as (x5 & x6 & x7 & x16 & x17 & x28 & x29 & x30 & x31 & j8 & j7 & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & SB1 & V1 & IOS1 & TPC1 & SSP' & LB1).
  apply evt_done.
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 lo ART0 LOW); [| exact WM1]. intros a Ha. apply MU1. cbn [outside].
    split; [intros Hr; apply Ha; left; ul|]. split; [intros Hr; apply Ha; right; right; right; left; exists fO, kO; rewrite <- EFSZ; split; [exact INF| lia]|].
    split; [| exact I]. intros Hr. apply Ha. right; left. apply client_static_intro. lia. }
  assert (AG1 : forall P : Z -> Prop, (forall x, P x -> (x < lo \/ q <= x) /\ ~ (OS <= x < OS + 288) /\ ~ (0x6abdb8 <= x < 0x6abdc0)) -> agree_on P m m1).
  { intros P HP a Ha. apply MU1. destruct (HP _ Ha) as (H1 & H2 & H3). cbn [outside]. split; [lia| split; [lia| split; [lia| exact I]]]. }
  assert (SHZ1 : bytes_at bsegs m1 (shad OS) (repeat z8 36)).
  { eapply bytes_at_agree; [exact SHZ|]. apply AG1. intros x Hx. rewrite repeat_length in Hx. unfold shad, SHB in Hx. unfold SEGTOP_A in FSEG.
    clear - Hx FLO FHI FTOP LOW SP0W F0 FSEG OSLO FHI2. unfold STACK_WIN in *. split; [| split]; Z.div_mod_to_equations; lia. }

  eapply (np_lx_okA RT AF RC RC2 PMc FDO MST RIP AF_IC AF_SHW DCC AF_NP Σ K OS (q + -96) lo fO 0x30 v kO pb pp ep dum j148 j284);
    [exact FDO| exact MST| exact INF| exact FLO| rewrite <- EFSZ; exact FHI| exact AL16| exact SB1| exact PI| exact V1| exact IOS1| exact SHZ1| lia| exact RV
    | exact TPC1| exists canary; exact SSP'| exact FRM| exact LB1| exact ART1| exact MI1| exact ST1| exact LOW| ul| ul| clear - Q32; Z.div_mod_to_equations; lia
    | exact FRB| exact CRB|].
  intros Σ2 y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 F2 fc2 m2 pb' pp' ep' dum' ART2 MI2 ST2 SB2 PI2 V2 IOS2 SHZ2 TPC2 LB2 FRM2 LV2 FRS2 SP2 CR2 PRES2.
  rewrite (ret_pc_even 0x111f14) by lia.

  assert (AG2 : forall P : Z -> Prop, (forall x, P x -> (q + -96 <= x < q) \/ (PJ_LOC_LO_A <= x < PJ_LOC_HI_A) \/ (0x6cbe28 <= x < 0x6cbe30)) -> agree_on P m1 m2).
  { intros P HP a Ha. apply PRES2.
    - destruct (HP _ Ha) as [H|[H|H]].
      + left. ul.
      + right; left. apply client_static_intro. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in H. lia.
      + right; left. apply client_static_intro. lia.
    - pose proof (HP _ Ha) as H. clear - H OSLO LOR FSEG FLO. cbn [outside]. unfold PJ_LOC_LO_A, PJ_LOC_HI_A, EL_INS_STACK_A, RT_STACK, SEGTOP_A in *. split; [lia| split; [lia| split; [lia| exact I]]]. }
  assert (FR2 : rw_cells bsegs m2 (q + -96) [CB 8 j8; C1 (Z_to_bv 8 1); CB 7 j7; C8 (Z_to_bv 64 (OS + 128)); C8 (Z_to_bv 64 EL_IMP); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    by (eapply rw_cells_agree_nw; [exact FR1|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia).
  assert (SSPm2 : ssp_cells m2 canary).
  { split; [exact (proj1 (af_got_lib RT AF Σ2 m2 ART2))|]. apply (ro_cells_agree bsegs m1 m2 _ _ (proj2 SSP')). apply AG2. intros x Hx. cbn [cells_size csize Nat.add] in Hx.
    unfold ssp_guard in Hx. lia. }

  apply (aevt_evt RT AF PMc MST).
  replace (q + -96)%Z with (bv_unsigned (Z_to_bv 64 q) + -96)%Z by (rewrite EQ; reflexivity).
  eapply evt_cut.
  { eapply (ins_i_seg2 ra (Z_to_bv 64 q) gp (Z_to_bv 64 TPV_A) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F2 fc2 lo OS v j148 j284 canary m2
              ltac:(rewrite EQ; ul) ltac:(ul) ltac:(rewrite EQ; ul) ltac:(reflexivity) ltac:(ul) OSLO RV FRM2 pb' pp' ep' dum' j8 j7 m2 y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 F2 fc2);
      rewrite ?EQ; first [exact PI2| apply munch_refl| apply wmono_refl| exact MI2| exact ST2| exact FR2| exact SB2| exact V2| exact IOS2| exact LB2
                          | exact TPC2| exact SSPm2| exact FRM2| intros k Hk; reflexivity| exact (DCC Σ2 m2 ART2)| exact RV| reflexivity| ul| idtac].
    all: ul. }
  cbv beta. intros ms3 PO3. unfold ins_postA in PO3. rewrite !EQ in PO3.
  destruct PO3 as (z0 & z1 & z2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & z3 & z4 & z5 & z6 & F3 & fc3 & pb3 & pp3 & ep3 & dum3 & m3 & -> & MU3 & WM3 & MI3 & FRM3 & FOK3 & ST3 & SSP3 & OSF3 & PI3 & TPC3 & LB3).
  apply evt_done.
  assert (ART3 : ART RT Σ2 m3).
  { apply (art_client_write RT AF Σ2 m2 m3 lo ART2 ltac:(rewrite SP2; exact LOW)); [| exact WM3]. intros a Ha. apply MU3. rewrite LV2, FRS2 in Ha. cbn [outside].
    split; [intros Hr; apply Ha; left; ul|]. split; [intros Hr; apply Ha; right; right; right; left; exists fO, kO; rewrite <- EFSZ; split; [exact INF| lia]|].
    split; [| exact I]. intros Hr. apply Ha. right; left. apply client_static_intro. lia. }
  assert (OSW3 : OSXW m3 OS 0x1008 0 (fill_after fill)) by (rewrite FOK; exists pb3, pp3, ep3, dum3, j148, j284; split; [exact OSF3| exact PI3]).
  assert (HULL3 : os_hullA m3 OS).
  { split; [pose proof OSF3 as H3; apply rw_cells_forget in H3; rewrite os_cellsX_size in H3; exact H3|].
    eapply bytes_at_agree; [exact SHZ2|]. apply (agree_of_munch _ _ _ _ MU3). intros x Hx. rewrite repeat_length in Hx. unfold shad, SHB in Hx. cbn [outside].
    unfold SEGTOP_A in FSEG. clear - Hx FLO FHI FTOP LOW SP0W F0 FSEG OSLO FHI2. unfold STACK_WIN in *. split; [| split; [| split; [| exact I]]]; Z.div_mod_to_equations; lia. }
  eapply (HK Σ2 z0 z1 z2 c1 c2 c3 c4 c5 c6 c7 z3 z4 z5 z6 F3 fc3 m3 ART3 MI3 ST3 OSW3 HULL3 LB3 TPC3 FRM3 LV2 FRS2 SP2); [clear - CR2; lia|].

  intros a Ha Ho. cbn [outside] in Ho. destruct Ho as (Ho1 & Ho2 & _).
  assert (OW : outside [(lo, q); (OS, OS + 288); (0x6abdb8, 0x6abdb8 + 8)] (bv_unsigned a)).
  { cbn [outside]. split; [| split; [exact Ho1| split; [exact Ho2| exact I]]]. intros Hr. destruct (aclient_split_c RT AF Σ m q _ ART0 Ha); ul. }
  rewrite (MU3 a OW). rewrite (PRES2 a); [exact (MU1 a OW)| apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia]|].
  cbn [outside]. split; [lia|]. split; [lia|]. split; [exact Ho2| exact I].
Qed.
End Lift.
