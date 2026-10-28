(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image RzCPS FP ZBridge.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim Monad PrintfModel PrintfFormats.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Export FX_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Startup_glue Pj_steps Pj_loc_kit Pj_os_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout D_kit D_clx RT_iface RT_iface2 RT_iface3 Sj_acps Sj_num_akit Pj_defsA El_ins_ifaceA El_np_intA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Export El_os_defsA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.

Notation EL_NP_BOOL_A := 0x11c784%Z (only parsing).

Lemma np_b_prefixA : forall ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q lo OS fill u : Z) (j148 j284 : list byte)
    (l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 : list byte),
  stk bsegs m lo q -> (lo <= q - 96)%Z -> (SEGTOP_A <= lo)%Z -> (q < 2^62)%Z -> (0 <= fill < 256)%Z -> (u = 0 \/ u = 1)%Z ->
  rw_cells bsegs m (OS + 136) (ios_cellsX OS 0x1688b8 0x1002 0 fill j148 j284) -> (q <= OS \/ OS + 288 <= lo)%Z -> (0 <= OS)%Z -> (OS + 288 < 2^62)%Z ->
  rw_cells bsegs m PJ_LOC_LO_A (locb_cellsA l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15) -> el_dccA m -> mem_inv bsegs m ->
  evt bsegs (fun ms' => exists t1' a1' m',
      ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 (Z_to_bv 64 t1') t2 s0 s1 (Z_to_bv 64 EL_NPUT_F) (Z_to_bv 64 OS) (Z_to_bv 64 (OS + 136)) (Z_to_bv 64 fill) (Z_to_bv 64 u) a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 EL_NP_UL) fc None m' (seg_rom bsegs)
      /\ a1' = Z_to_bv 64 OS /\ munch [(q - 96, q)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo q)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 EL_NPUT_F) (Z_to_bv 64 OS) (Z_to_bv 64 (OS + 136)) (Z_to_bv 64 fill) (Z_to_bv 64 u) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 EL_NP_BOOL_A) fc None m (seg_rom bsegs)).
Proof.
  intros until l15. intros ST LO LOLO QH RF RU IOS OSQ OS0 OSH LBC DCC MI.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold SEGTOP_A in LOLO.
  assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(q - 96, q)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  destruct DCC as (VT & WS & WS2 & NPT & NPV & GNP & GCT).
  unfold locb_cellsA, PJ_LOC_LO_A in LBC. unfold ios_cellsX in IOS.
  retype_at IOS 1%nat 1%nat [CB 4 [Z_to_bv 8 2; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 0]].
  lstep.
  rewrite ?EQ. carve_frame 96%nat ST.
  do 5 lstep.
  do 2 lstep.
  lstep.
  lit_words.
  lstep.
  lstep.
  if_false.
  do 2 lstep.
  do 2 lstep.
  do 6 lstep.
  release_frame FR ST q.
  lstep.
  apply evt_done. eexists _, _, _. split; [cbv delta [mkR]; reflexivity|].
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact ST].
Qed.

Section Lift.
Local Open Scope Z_scope.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis DCC : forall Σ m, ART RT Σ m -> el_dccA m.

Definition np_b_cpsA : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (OS q lo fO fill v : Z) (kO : nat) (pb : word) (pp ep : Z) (dum j148 j284 : list byte)
         (ra gp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  fdfs_only PMc -> mat_stable PMc ->
  In (fO, kO) (rt_frames RT Σ) -> (fO <= OS)%Z -> (OS + 288 <= fO + fs_size kO - 8)%Z -> (OS mod 16 = 0)%Z ->
  rw_cells bsegs m OS (sb_cellsX pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) dum) -> PUTINV OS pp ep ->
  rw_cells bsegs m (OS + 128) [C8 (Z_to_bv 64 0x168890)] -> rw_cells bsegs m (OS + 136) (ios_cellsX OS 0x1688b8 0x1002 0 fill j148 j284) ->
  bytes_at bsegs m (shad OS) (repeat z8 36) -> (0 <= fill < 256)%Z -> (v = 0 \/ v = 1)%Z ->
  el_tploc m -> io_ssp m -> frm0 fc -> LOCBA m ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo q -> (rt_sp0 RT Σ - STACK_WIN <= lo)%Z -> (lo + EL_NP_STACK_A <= q)%Z ->
  (q + 16 <= USTACK_TOP)%Z -> (q mod 16 = 0)%Z ->
  (Z.of_nat (length (rt_frames RT Σ)) + 1 <= FRAMES_TOT)%Z -> (1 <= rt_credit RT Σ)%Z ->
  (forall (Σ' : rts RT) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (F' : bvmap 5 word) (fc' : bv 32) m' (pb' : word) (pp' ep' : Z) (dum' : list byte),
     ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' lo q ->
     rw_cells bsegs m' OS (sb_cellsX pb' (Z_to_bv 64 pp') (Z_to_bv 64 ep') dum') -> PUTINV OS pp' ep' ->
     rw_cells bsegs m' (OS + 128) [C8 (Z_to_bv 64 0x168890)] -> rw_cells bsegs m' (OS + 136) (ios_cellsX OS 0x1688b8 0x1002 0 fill j148 j284) ->
     bytes_at bsegs m' (shad OS) (repeat z8 36) -> el_tploc m' -> LOCBA m' -> frm0 fc' ->
     rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ -> (rt_credit RT Σ - 1 <= rt_credit RT Σ')%Z ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(OS + 40, OS + 128); (OS + 160, OS + 168); (0x6ab338, 0x6ab338 + 8)]%Z m m' ->
     aevt RT PMc Σ' K (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 TPV_A) t0' t1' t2' s0 s1 (Z_to_bv 64 OS) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F' (ret_pc ra) fc' None m' (seg_rom bsegs))) ->
  aevt RT PMc Σ K (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 TPV_A) t0 t1 t2 s0 s1 (Z_to_bv 64 EL_NPUT_F) (Z_to_bv 64 OS) (Z_to_bv 64 (OS + 136)) (Z_to_bv 64 fill) (Z_to_bv 64 v) a5 a6 a7
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 EL_NP_BOOL_A) fc None m (seg_rom bsegs)).

Local Ltac ul := unfold EL_NP_STACK_A, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.

Theorem np_b_okA : np_ul_cpsA RT PMc -> np_b_cpsA.
Proof using AF FDO MST DCC.
  intros NPUL. unfold np_b_cpsA. intros until m. intros FDO' MST' INF FLO FHI AL16 SB PI V128 IOS SHZ RF RV TPC SSP FRM LB ART0 MI ST LOW LOR SPT Q32 FRB CRB HK.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_frames_range RT AF Σ m fO kO ART0 INF) as (F0 & FTOP & FSEG' & FLIVE).
  assert (LO0 : 0 <= lo) by (destruct ST as (? & ? & _); lia).
  assert (OSLO : OS + 288 <= lo) by (clear - FHI FTOP LOW; ul).
  assert (QLO : lo + 96 < q) by (clear - LOR; ul).
  pose proof LB as (l1 & l2 & l3 & l4 & l5 & l6 & l7 & l8 & l9 & l10 & l11 & l12 & l13 & l14 & l15 & LBC).

  assert (NFR : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) q a -> ~ (q - 96 <= a < q)).
  { intros a Ha Hr. destruct Ha as [H|[H|[(p & n & Hin & Hp)|[(f & k & Hin & Hf)|(f & k & Hin & Hf)]]]].
    - lia.
    - pose proof (client_static_range _ H). clear - H0 Hr LOR LOW SP0R. ul.
    - pose proof (af_live_range RT AF Σ m p n ART0 Hin) as (_ & Y & _). clear - Y Hp Hr LOW LOR. ul.
    - pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & Y & _). clear - Y Hf Hr LOW LOR. ul.
    - pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (Y0 & Y & _). unfold shad in Hf. clear - Y0 Y Hf Hr LOW LOR SP0W.
      unfold EL_NP_STACK_A, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *. Z.div_mod_to_equations. lia. }

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut.
  { eapply (np_b_prefixA ra gp (Z_to_bv 64 TPV_A) t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q lo OS fill v j148 j284
              l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15);
      [exact ST| clear - LOR; ul| clear - LOW SP0R; ul| clear - SPT; ul| exact RF| exact RV| exact IOS| right; exact OSLO| clear - FLO F0; lia| clear - OSLO LOR SPT; ul
      | exact LBC| exact (DCC Σ m ART0)| exact MI]. }
  cbv beta. intros ms1 (t1' & a1' & m1 & -> & _ & MU1 & WM1 & MI1 & ST1). apply evt_done.

  assert (AG1 : forall P : Z -> Prop, (forall x, P x -> ~ (q - 96 <= x < q)) -> agree_on P m m1).
  { intros P HP a Ha. apply MU1. cbn [outside]. split; [exact (HP _ Ha)| exact I]. }
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 lo ART0 LOW); [| exact WM1]. intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. intros Hr. apply Ha. left. clear - Hr LOR SPT; ul. }
  assert (SB1 : rw_cells bsegs m1 OS (sb_cellsX pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) dum))
    by (eapply rw_cells_agree_nw; [exact SB|]; apply AG1; intros x Hx; cbn [sb_cellsX cells_size csize Nat.add] in Hx; lia).
  assert (V1 : rw_cells bsegs m1 (OS + 128) [C8 (Z_to_bv 64 0x168890)])
    by (eapply rw_cells_agree_nw; [exact V128|]; apply AG1; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia).
  assert (IOS1 : rw_cells bsegs m1 (OS + 136) (ios_cellsX OS 0x1688b8 0x1002 0 fill j148 j284))
    by (eapply rw_cells_agree_nw; [exact IOS|]; apply AG1; intros x Hx; cbn [ios_cellsX cells_size csize Nat.add] in Hx; lia).
  assert (SHZ1 : bytes_at bsegs m1 (shad OS) (repeat z8 36)).
  { eapply bytes_at_agree; [exact SHZ|]. apply AG1. intros x Hx. rewrite repeat_length in Hx. unfold shad, SHB in Hx. clear - Hx OSLO QLO LOW SP0W. unfold STACK_WIN in *. Z.div_mod_to_equations. lia. }
  assert (TPC1 : el_tploc m1) by (eapply rw_cells_agree_nw; [exact TPC|]; apply AG1; intros x Hx; cbn [cells_size csize Nat.add] in Hx; clear - Hx LOR LOW SP0R; ul).
  assert (SSP1 : io_ssp m1).
  { destruct SSP as (g & G1 & G2). exists g. split; [eapply ro_cells_agree; [exact G1|]| eapply ro_cells_agree; [exact G2|]]; apply AG1; intros x Hx; cbn [cells_size csize Nat.add] in Hx; clear - Hx LOR LOW SP0R; ul. }
  assert (LB1 : LOCBA m1) by (apply (LOCBA_agree m m1 LB); apply AG1; intros x Hx; unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx; clear - Hx LOR LOW SP0R; ul).

  eapply (NPUL Σ K OS q lo fO fill v kO pb pp ep dum j148 j284 ra gp t0 (Z_to_bv 64 t1') t2 s0 s1 (Z_to_bv 64 EL_NPUT_F) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1
            FDO' MST' INF FLO FHI AL16 SB1 PI V1 IOS1 SHZ1 RF ltac:(cbv beta; clear - RV; lia) TPC1 SSP1 FRM LB1 ART1 MI1 ST1 LOW LOR SPT Q32 FRB CRB).
  intros Σ' y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 F' fc' m' pb' pp' ep' dum' ART' MI' ST' SB' PI' V' IOS' SHZ' TPC' LB' FRM' LV' FRS' SP' CR' PRES'.
  apply (HK Σ' y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 F' fc' m' pb' pp' ep' dum' ART' MI' ST' SB' PI' V' IOS' SHZ' TPC' LB' FRM' LV' FRS' SP' CR').
  intros a Ha Ho. rewrite (PRES' a Ha Ho). apply MU1. cbn [outside]. split; [exact (NFR _ Ha)| exact I].
Qed.
End Lift.
