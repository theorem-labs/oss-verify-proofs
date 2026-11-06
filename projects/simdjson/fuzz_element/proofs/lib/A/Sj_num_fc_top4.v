(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx I_lkit Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_adefs Sj_num_abig Sj_num_acall Sj_num_acall2 Sj_num_aframe Sj_num_lm_pro
  Sj_num_lm_kit Sj_num_nd_defs Sj_num_lits Sj_num_fc_stmt Sj_num_fc_kit Sj_num_fc_kit2 Sj_num_fc_defs Sj_num_fc_defs2 Sj_num_fc_defs3 Sj_num_fc_kit3 Sj_num_fc_kit4
  Sj_num_fc_pro Sj_num_fc_rel Sj_num_fc_q1 Sj_num_fc_q2a Sj_num_fc_q2b Sj_num_fc_q2c Sj_num_fc_q7 Sj_num_fc_ev Sj_num_fc_tkit Sj_num_fc_top1 Sj_num_fc_top2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | asan_zc_hook | asan_zcp_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section FCTOP.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RTF : rt_contracts_f RT.
  Variable PMc : Model -> Prop.
  Hypothesis FDO : fdfs_only PMc.
  Hypothesis MST : mat_stable PMc.
  Hypothesis HPDC : pdca_stmt RT PMc.
  Hypothesis HNDC : ndca_stmt RT PMc.

  Variables (Σ0 : rts RT) (K : config -> Prop).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (OUT lo d spq f p n A FIRST LAST : Z) (txt : list byte) (me : mem).
  Notation SP := (bv_unsigned sp).
  Notation S := (f / 8 + 2147450880)%Z.
  Notation TL := (Z.of_nat (length txt)).
  Hypothesis ETP : tp = Z_to_bv 64 0x6a7e68.
  Hypothesis ROOM : (lo + SPA_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis SP16 : (SP mod 16 = 0)%Z.
  Hypothesis LOR : (rt_sp0 RT Σ0 - STACK_WIN <= lo)%Z.
  Hypothesis FRL : (length (rt_frames RT Σ0) + FFA_FRAMES <= FRAMES_MAX)%nat.
  Hypothesis CRD : (FFA_CREDIT <= rt_credit RT Σ0)%Z.
  Hypothesis SPQ : ((d = 0 \/ d = 16) /\ spq = SP - 192 - d)%Z.
  Hypothesis NF : (f mod 64 = 0 /\ 0x6ca000 <= f /\ f + 1016 <= lo /\ (f + 1016 <= S \/ S + 127 <= f) /\ 0 <= S /\ S + 127 <= lo)%Z.
  Hypothesis OUTR : (OUT mod 8 = 0 /\ SP <= OUT /\ OUT + 8 <= USTACK_TOP)%Z.

  Hypothesis PIN : In (p, n) (rt_live RT Σ0).
  Hypothesis PCH : (p mod 8 = 0 /\ p <= A /\ LAST + 8 <= p + n /\ A + TL <= p + n)%Z.
  Hypothesis TXR : (0 < A /\ A + TL <= lo /\ TL < 2147483648)%Z.
  Hypothesis FLR : (A <= FIRST /\ FIRST < LAST /\ LAST <= A + TL)%Z.
  Hypothesis TSEP : ((A + TL <= f \/ f + 1024 <= A) /\ (A + TL <= S \/ S + 128 <= A))%Z.

  Hypothesis HK : forall (Σ' : rts RT) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' (v : word), frm0 fc' ->
     rt_after RT Σ' SP lo me m' -> rt_pres_ex (rt_live RT Σ0) (rt_frames RT Σ0) SP OUT 8 me m' ->
     rw_cells asegs m' OUT [C8 v] ->
     rt_frames RT Σ' = rt_frames RT Σ0 -> rt_live RT Σ' = rt_live RT Σ0 -> rt_sp0 RT Σ' = rt_sp0 RT Σ0 ->
     (rt_credit RT Σ0 - FFA_CREDIT <= rt_credit RT Σ')%Z ->
     aevt RT PMc Σ' K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F' (ret_pc ra) fc' None m' (seg_rom asegs)).
  Collection TOPH := AF RTF FDO MST HPDC HNDC ETP ROOM TOP SP16 LOR FRL CRD SPQ NF OUTR PIN PCH TXR FLR TSEP HK.

  Notation MREL := (fc_mrel RT Σ0 sp OUT me).
  Notation PARK := (fc_park ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 d spq f).
  Notation W := (fc_W lo spq f OUT).
  Notation QΣ Σ := (fun ms' => aevt RT PMc Σ K ms').

  Notation T1 L := (L RT AF RTF PMc FDO MST HPDC HNDC Σ0 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 OUT lo d spq f p n A FIRST LAST txt me
                      ETP ROOM TOP SP16 LOR FRL CRD SPQ NF OUTR PIN PCH TXR FLR TSEP HK) (only parsing).
  Notation fc_srel := (Sj_num_fc_top1.fc_srel RT Σ0 f).
  Notation fc_ctx := (Sj_num_fc_top1.fc_ctx RT Σ0 ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 OUT d spq f me).
  Notation TK L Σ SR := (L RT AF Σ0 Σ sp OUT lo d spq f ROOM TOP LOR (proj1 SR) (proj1 (proj2 SR)) (proj1 (proj2 (proj2 SR))) SPQ NF OUTR) (only parsing).
  Notation TKm L Σ SR := (L RT AF Σ0 Σ sp OUT lo d spq f me ROOM TOP LOR (proj1 SR) (proj1 (proj2 SR)) (proj1 (proj2 (proj2 SR))) SPQ NF OUTR) (only parsing).

  Notation EVP L F fc mb Σ used SR HA :=
    (L sp gp tp F fc lo d spq f A FIRST LAST OUT txt mb (T1 top_spq) ROOM TOP (T1 top_F64) (T1 top_FLO) (T1 top_FSH) (T1 top_FS0) TXR FLR TSEP OUTR
       (T1 top_shpt Σ used mb SR HA) (T1 top_shpo Σ used mb SR HA) (QΣ Σ)) (only parsing).
  Notation EVQ L mb Σ used SR HA :=
    (L sp gp tp lo d spq f A FIRST LAST OUT txt mb (T1 top_spq) ROOM TOP (T1 top_F64) (T1 top_FLO) (T1 top_FSH) (T1 top_FS0) TXR FLR TSEP OUTR
       (T1 top_shpt Σ used mb SR HA) (T1 top_shpo Σ used mb SR HA) (QΣ Σ)
       (T1 top_shpl Σ used mb 0x2a2e0%Z 10416%Z SR HA ltac:(left; reflexivity) eq_refl) (T1 top_shpl Σ used mb 0x2cc60%Z 640%Z SR HA ltac:(right; left; reflexivity) eq_refl)) (only parsing).

  Notation FCS' F fc pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR xra (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 spq) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs3 (Z_to_bv 64 S) xs5 xs6 xs7 xs8 xs9
             xs10 xs11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
  Notation FCP' F fc pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs6 xs8 xs10 xs11 xt3 xt4 xt5 xt6 mm :=
    (FCS' F fc pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 (Z_to_bv 64 (f + 608)) xs6 (Z_to_bv 64 LAST) xs8 (Z_to_bv 64 2147450880) xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Notation Z32 := (repeat (Z_to_bv 8 0) 32).
  Notation Z27 := (repeat (Z_to_bv 8 0) 27).

  Notation EVQF L F fc FRM mb Σ used SR HA :=
    (L sp gp tp F fc lo d spq f A FIRST LAST OUT txt mb (T1 top_spq) ROOM TOP (T1 top_F64) (T1 top_FLO) (T1 top_FSH) (T1 top_FS0) TXR FLR TSEP OUTR
       (T1 top_shpt Σ used mb SR HA) (T1 top_shpo Σ used mb SR HA) (QΣ Σ) FRM
       (T1 top_shpl Σ used mb 0x2a2e0%Z 10416%Z SR HA ltac:(left; reflexivity) eq_refl) (T1 top_shpl Σ used mb 0x2cc60%Z 640%Z SR HA ltac:(right; left; reflexivity) eq_refl)) (only parsing).

  Ltac top_env Σ SR :=
    let SPR := fresh "SPR" in pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    pose proof NF as (N1 & N2 & N3 & N4 & N5 & N6); pose proof OUTR as (O1 & O2 & O3);
    pose proof (T1 top_spq) as [Hd Hs]; pose proof ROOM as ROOM'; pose proof TOP as TOP'; unfold SPA_STACK, NDCA_STACK, P5A_STACK, LMA_STACK, RT_STACK, USTACK_TOP in ROOM', TOP';
    pose proof (T1 top_inF Σ _ SR) as HinF; pose proof (f64_8 f (proj1 NF)) as F8; pose proof (eq_refl : fs_size 4 = 1024%Z) as FS4;
    pose proof (T1 top_inP Σ _ SR) as HinP; pose proof PCH as (PC1 & PC2 & PC3 & PC4); pose proof TXR as (TX1 & TX2 & TX3).

  Lemma fc_pns_memset : forall Σ used fc (mm : mem) (jp : list byte) (dz nz : Z) (xra xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word) F,
    fc_ctx Σ used fc mm -> rw_cells asegs mm (f + 608) [CB 72 jp] -> forall a : Z, (a = f + 608 + dz)%Z ->
    rw_cells asegs mm (f / 8 + 2147450956) [CB 9 (repeat (Z_to_bv 8 0) 9)] -> mem_inv asegs mm -> stk asegs mm lo spq ->
    (0 <= dz)%Z -> (0 <= nz)%Z -> (dz + nz <= 72)%Z ->
    (forall t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m', fc_ctx Σ used fc' m' ->
       rt_after RT Σ spq lo mm m' -> rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) spq a nz mm m' ->
       rw_cells asegs m' a [CB (Z.to_nat nz) (repeat (Z_to_bv 8 0) (Z.to_nat nz))] ->
       aevt RT PMc Σ K (MS (mkR xra (Z_to_bv 64 spq) gp tp t0' t1' t2' sp (Z_to_bv 64 spq) (Z_to_bv 64 a) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 f) xs3 (Z_to_bv 64 S) xs5 xs6 xs7 xs8 xs9
                               xs10 xs11 t3' t4' t5' t6') F' (ret_pc xra) fc' None m' (seg_rom asegs))) ->
    aevt RT PMc Σ K (FCS' F fc 0x81794 xra xt0 xt1 xt2 (Z_to_bv 64 a) (Z_to_bv 64 0) (Z_to_bv 64 nz) xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using TOPH.
    intros Σ used fc mm jp dz nz. intros until F. intros CTXm PNS a -> PSH MI ST D0 N0 DN HKc.
    pose proof CTXm as (SR & HU & FRM & ARTm & MRm & PKm). top_env Σ SR.
    assert (JL : length jp = 72%nat) by exact (proj1 (proj1 (proj1 PNS))).
    pose proof (u8arr_of_rw_cells asegs mm _ _ _ PNS) as UA.
    assert (ZR : bytes_at asegs mm ((f + 608) / 8 + 2147450880) (repeat (Z_to_bv 8 0) 9))
      by (replace ((f + 608) / 8 + 2147450880)%Z with (f / 8 + 2147450956)%Z by (Z.div_mod_to_equations; lia); exact (zero_run_of_CB mm _ 9 PSH)).
    assert (UFR : exists f0 c, In (f0, c) (rt_frames RT Σ) /\ (f0 <= f + 608)%Z /\ (f + 608 + Z.of_nat (length jp) <= f0 + fs_size c - 8)%Z)
      by (exists f, 4%nat; split; [exact HinF| rewrite JL; lia]).
    destruct (obj_chk RT Σ mm (f + 608)%Z jp 9%nat lo (Z_to_bv 64 spq) UA ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(rewrite JL; lia) ltac:(rewrite JL; lia) ZR UFR
                (f + 608 + dz)%Z nz N0 ltac:(lia) ltac:(rewrite JL; lia)) as [_ CD].
    eapply (aevt_memset RT RTF PMc FDO MST Σ K) with (d := (f + 608 + dz)%Z) (n := nz) (cb := Z_to_bv 8 0) (lo := lo);
      [reflexivity | reflexivity | reflexivity | lia | lia | exact CD | exact ARTm | exact MI | exact (T1 top_cok Σ used mm SR ST) | exact FRM |].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' FRM' RA PR BY.
    rewrite ?unsigned_lit in RA, PR by lia.
    pose proof (T1 fc_ctx_call Σ used fc fc' mm m' _ _ CTXm FRM' RA PR ltac:(lia)) as CTX'.
    pose proof RA as (_ & _ & WM' & _).
    assert (MID : rw_cells asegs m' (f + 608 + dz) [CB (Z.to_nat nz) (repeat (Z_to_bv 8 0) (Z.to_nat nz))]).
    { pose proof (rw_cells_CB_intro m' (f + 608 + dz) (repeat (Z_to_bv 8 0) (Z.to_nat nz)) BY) as H. rewrite repeat_length in H. apply H.
      rewrite Z2Nat.id by lia. exact (wr_at_transport asegs mm m' _ _ (proj2 (proj2 CD)) WM'). }
    exact (HKc t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' CTX' RA PR MID).
  Qed.

  Ltac err_after_call mm m' AG WM' :=
    rt_transport_with mm m' AG WM' ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?repeat_length in Hx; cbv beta; split; [aclient_tac | lia]).

  Lemma fc_kerr_site2 : forall Σ used F fc mb ra2, fc_ctx Σ used fc mb ->
    forall xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs3 xs6 xs8 xs10 xs11 xt3 xt4 xt5 xt6 c0 c8 c16 c24 c32 c40 c48 c56 c64 c80 jp je (mm : mem),
      fc_einv spq f A OUT lo txt mb c0 c8 c16 c24 c32 c40 c48 c56 c64 c80 [CB 32 jp; CB 32 Z32; CB 8 je] mm ->
      ((In ra2 [0xe3cb4; 0xe4220]%Z /\ xs3 = Z_to_bv 64 f /\ xs8 = Z_to_bv 64 OUT) \/ (In ra2 [0xe3e98; 0xe4794; 0xe4990]%Z /\ c48 = Z_to_bv 64 f /\ c56 = Z_to_bv 64 OUT)) ->
      evt asegs (QΣ Σ) (FCP' F fc 0x81794 (Z_to_bv 64 ra2) xt0 xt1 xt2 (Z_to_bv 64 (f + 608)) (Z_to_bv 64 0) (Z_to_bv 64 27) xa3 xa4 xa5 xa6 xa7 xs3 xs6 xs8
                             xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using TOPH.
    intros Σ used F fc mb ra2 CTX. intros until mm. intros INV KIND.
    fc_eopen INV.
    pose proof (T1 top_ctx_step Σ used fc mb mm CTX MU WM) as CTXm. clear CTX MU WM.
    pose proof CTXm as (SR & HU & FRM & ARTm & MRm & PKm). top_env Σ SR. pose proof TSEP as (TS1 & TS2).
    assert (LJ : length jp = 32%nat) by (destruct PNS as ((W & _) & _); cbn [cells_wf cell_wf] in W; tauto).

    destruct (rw_cells_forget asegs mm _ _ PNS) as (jp1 & PNSF). cbn [cells_size csize Nat.add] in PNSF.
    change [CB 32 jp; CB 32 Z32; CB 8 je] with ([CB 32 jp] ++ [CB 32 Z32] ++ [CB 8 je]) in PNS.
    apply num_rw_cells_app in PNS. destruct PNS as [Q12 PNS]. apply num_rw_cells_app in PNS. destruct PNS as [Q3 Q4].
    cbn [cells_size csize Nat.add] in Q3, Q4.
    replace (f + 608 + Z.of_nat 32)%Z with (f + 640)%Z in * by lia. replace (f + 640 + Z.of_nat 32)%Z with (f + 672)%Z in * by lia.
    apply (rw_cells_split_CB asegs mm _ [] 32 jp [] [27; 5]%nat) in Q12; [| reflexivity]. cbn [mk_CB_cells app] in Q12.
    repeat match type of Q12 with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in Q12; clearbody j end.
    lazymatch type of Q12 with rw_cells _ _ _ [?c1; ?c2] => change [c1; c2] with ([c1] ++ [c2]) in Q12 end.
    apply num_rw_cells_app in Q12. destruct Q12 as [Q1 Q2]. cbn [cells_size csize Nat.add] in Q2. replace (f + 608 + Z.of_nat 27)%Z with (f + 635)%Z in * by lia.
    apply evt_done.
    eapply (fc_pns_memset Σ used fc mm jp1 0 27); [exact CTXm | exact PNSF | lia | exact PSH | exact MI | exact ST | lia | lia | lia |].
    intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F'' fc'' m'' CTX'' RA2 PR2 MID2.
    destruct RA2 as (ART'' & MI'' & WM'' & ST'').
    pose proof (agree_of_pres_ex _ _ _ _ _ mm m'' (fun x => aclient (rt_live RT Σ) (rt_frames RT Σ) spq x /\ ~ (f + 608 <= x < f + 608 + 27)%Z) PR2 (fun x H => H)) as AG2.
    clear Q1 PNSF ST MI. err_after_call mm m'' AG2 WM''.
    change (Z.to_nat 27) with 27%nat in MID2.
    assert (PNS2 : rw_cells asegs m'' (f + 608) [CB 27 Z27; CB 5 j0; CB 32 Z32; CB 8 je])
      by (change [CB 27 Z27; CB 5 j0; CB 32 Z32; CB 8 je] with ([CB 27 Z27] ++ [CB 5 j0] ++ [CB 32 Z32] ++ [CB 8 je]);
          apply num_rw_cells_app; split; [exact MID2|]; cbn [cells_size csize Nat.add]; replace (f + 608 + Z.of_nat 27)%Z with (f + 635)%Z by lia;
          apply num_rw_cells_app; split; [exact Q2|]; cbn [cells_size csize Nat.add]; replace (f + 635 + Z.of_nat 5)%Z with (f + 640)%Z by lia;
          apply num_rw_cells_app; split; [exact Q3|]; cbn [cells_size csize Nat.add]; replace (f + 640 + Z.of_nat 32)%Z with (f + 672)%Z by lia; exact Q4).
    assert (L5 : length j0 = 5%nat) by exact (proj1 (proj1 (proj1 Q2))).
    assert (L8 : length je = 8%nat) by exact (proj1 (proj1 (proj1 Q4))).
    pose proof (munch_refl (fc_W lo spq f OUT) m'') as MU2. pose proof (wmono_refl asegs m'') as WM2.
    pose proof CTX'' as (SR'' & _ & FRM'' & HA'' & _).
    apply (aevt_evt RT AF PMc MST).
    destruct KIND as [(HA & -> & ->) | (HB & -> & ->)]; [ cbn [In] in HA | cbn [In] in HB ].
    - destruct HA as [<- | [<- | []]]; num_ret_pc;
        (eapply evt_eq; [| eapply (EVQF fc_err_tailA F'' fc'' FRM'' m'' Σ used SR'' HA'' (T1 fc_k7f4 Σ used fc'' m'' CTX''))];
           [num_st_eq | cbn [In]; repeat (first [left; reflexivity | right]) | fc_eclose | exact L5 | exact L8]).
    - destruct HB as [<- | [<- | [<- | []]]]; num_ret_pc;
        (eapply evt_eq; [| eapply (EVQF fc_err_tailB F'' fc'' FRM'' m'' Σ used SR'' HA'' (T1 fc_k7f4 Σ used fc'' m'' CTX''))];
           [num_st_eq | cbn [In]; repeat (first [left; reflexivity | right]) | fc_eclose | exact L5 | exact L8]).
  Qed.

  Lemma fc_kerr_site : forall Σ used F fc mb ra1, fc_ctx Σ used fc mb -> In ra1 (FC_ERRA ++ FC_ERRB) ->
    forall xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs3 xs6 xs8 xs10 xs11 xt3 xt4 xt5 xt6 c0 c8 c16 c24 c32 c40 c48 c56 c64 c80 (mm : mem),
      fc_pinv spq f A OUT lo txt mb c0 c8 c16 c24 c32 c40 c48 c56 c64 c80 mm ->
      ((In ra1 FC_ERRA /\ xs3 = Z_to_bv 64 f /\ xs8 = Z_to_bv 64 OUT) \/ (In ra1 FC_ERRB /\ c48 = Z_to_bv 64 f /\ c56 = Z_to_bv 64 OUT)) ->
      evt asegs (QΣ Σ) (FCP' F fc 0x81794 (Z_to_bv 64 ra1) xt0 xt1 xt2 (Z_to_bv 64 (f + 640)) (Z_to_bv 64 0) (Z_to_bv 64 32) xa3 xa4 xa5 xa6 xa7 xs3 xs6 xs8
                             xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using TOPH.
    intros Σ used F fc mb ra1 CTX HIN. intros until mm. intros INV KIND.
    fc_popen INV.
    pose proof (T1 top_ctx_step Σ used fc mb mm CTX MU WM) as CTXm. clear CTX MU WM.
    pose proof CTXm as (SR & HU & FRM & ARTm & MRm & PKm). top_env Σ SR. pose proof TSEP as (TS1 & TS2).
    apply evt_done.
    eapply (fc_pns_memset Σ used fc mm jp 32 32); [exact CTXm | exact PNS | lia | exact PSH | exact MI | exact ST | lia | lia | lia |].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' CTX' RA PR MID.

    apply (rw_cells_split_CB asegs mm _ [] 72 jp [] [32; 32; 8]%nat) in PNS; [| reflexivity]. cbn [mk_CB_cells app] in PNS.
    repeat match type of PNS with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in PNS; clearbody j end.
    lazymatch type of PNS with rw_cells _ _ _ [?c1; ?c2; ?c3] => change [c1; c2; c3] with ([c1] ++ [c2] ++ [c3]) in PNS end.
    apply num_rw_cells_app in PNS. destruct PNS as [Q1 PNS]. apply num_rw_cells_app in PNS. destruct PNS as [Q3 Q4].
    cbn [cells_size csize Nat.add] in Q3, Q4.
    replace (f + 608 + Z.of_nat 32)%Z with (f + 640)%Z in * by lia. replace (f + 640 + Z.of_nat 32)%Z with (f + 672)%Z in * by lia.
    destruct RA as (ART' & MI' & WM' & ST').
    pose proof (agree_of_pres_ex _ _ _ _ _ mm m' (fun x => aclient (rt_live RT Σ) (rt_frames RT Σ) spq x /\ ~ (f + 640 <= x < f + 640 + 32)%Z) PR (fun x H => H)) as AG.
    clear Q3 ST MI. err_after_call mm m' AG WM'.
    change (Z.to_nat 32) with 32%nat in MID.
    assert (PNS1 : rw_cells asegs m' (f + 608) [CB 32 j; CB 32 Z32; CB 8 j1])
      by (change [CB 32 j; CB 32 Z32; CB 8 j1] with ([CB 32 j] ++ [CB 32 Z32] ++ [CB 8 j1]);
          apply num_rw_cells_app; split; [exact Q1|]; cbn [cells_size csize Nat.add]; replace (f + 608 + Z.of_nat 32)%Z with (f + 640)%Z by lia;
          apply num_rw_cells_app; split; [exact MID|]; cbn [cells_size csize Nat.add]; replace (f + 640 + Z.of_nat 32)%Z with (f + 672)%Z by lia; exact Q4).
    pose proof (munch_refl (fc_W lo spq f OUT) m') as MU1. pose proof (wmono_refl asegs m') as WM1.
    assert (INV1 : fc_einv spq f A OUT lo txt m' c0 c8 c16 c24 c32 c40 c48 c56 c64 c80 [CB 32 j; CB 32 Z32; CB 8 j1] m') by fc_eclose.
    apply (aevt_evt RT AF PMc MST).
    unfold FC_ERRA, FC_ERRB in HIN, KIND. cbn [app In] in HIN.
    destruct HIN as [<- | [<- | [<- | [<- | [<- | []]]]]]; num_ret_pc; zstep; zstep; zstep; zstep;
      (eapply evt_eq; [| eapply (fc_kerr_site2 Σ used F' fc' m' _ CTX')]; [num_st_eq | exact INV1 |]);
      (destruct KIND as [(HK1 & HK2) | (HK1 & HK2)]; cbn [In] in HK1; [left | right]; (split; [| exact HK2]); cbn [In]; lia).
  Qed.

  Lemma fc_kerra : forall Σ used F fc mb, fc_ctx Σ used fc mb -> forall ra1, In ra1 FC_ERRA ->
    forall xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs6 xs10 xs11 xt3 xt4 xt5 xt6 c0 c8 c16 c24 c32 c40 c48 c56 c64 c80 (mm : mem),
      fc_pinv spq f A OUT lo txt mb c0 c8 c16 c24 c32 c40 c48 c56 c64 c80 mm ->
      evt asegs (QΣ Σ) (FCP' F fc 0x81794 (Z_to_bv 64 ra1) xt0 xt1 xt2 (Z_to_bv 64 (f + 640)) (Z_to_bv 64 0) (Z_to_bv 64 32) xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs6 (Z_to_bv 64 OUT)
                             xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using TOPH.
    intros Σ used F fc mb CTX ra1 HIN. intros until mm. intros INV.
    eapply (fc_kerr_site Σ used F fc mb ra1 CTX); [apply in_or_app; left; exact HIN | exact INV | left; split; [exact HIN | split; reflexivity]].
  Qed.
  Lemma fc_kerrb : forall Σ used F fc mb, fc_ctx Σ used fc mb -> forall ra1, In ra1 FC_ERRB ->
    forall xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs3 xs6 xs8 xs10 xs11 xt3 xt4 xt5 xt6 c0 c8 c16 c24 c32 c40 c64 c80 (mm : mem),
      fc_pinv spq f A OUT lo txt mb c0 c8 c16 c24 c32 c40 (Z_to_bv 64 f) (Z_to_bv 64 OUT) c64 c80 mm ->
      evt asegs (QΣ Σ) (FCP' F fc 0x81794 (Z_to_bv 64 ra1) xt0 xt1 xt2 (Z_to_bv 64 (f + 640)) (Z_to_bv 64 0) (Z_to_bv 64 32) xa3 xa4 xa5 xa6 xa7 xs3 xs6 xs8
                             xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using TOPH.
    intros Σ used F fc mb CTX ra1 HIN. intros until mm. intros INV.
    eapply (fc_kerr_site Σ used F fc mb ra1 CTX); [apply in_or_app; right; exact HIN | exact INV | right; split; [exact HIN | split; reflexivity]].
  Qed.
End FCTOP.
