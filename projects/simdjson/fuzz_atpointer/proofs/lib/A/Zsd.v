(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z119 FP Z10q.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpe.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Rnd Zso Zvm.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Layout Shadow Zks D_defs D_kit D_clx I_lkit Zpm Zpl Zq2 Sj_rtf
  Zqc Zqd Zsl Zqa Zq7 Zq8 Zq9 Zqb Zt9
  Zt5 Ztr Zsv Zs4 Zr5 Zr6 Zr0 Zr1 Zr2 Zr7 Zr8
  Zrq Zs2 Zrt Zru Zrv Zrw Zs1 Zr3 Zs6 Zs7 Zs9 Zsa Zsb Zsc.
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
  Hypothesis ETP : tp = Z_to_bv 64 0x646eb0.
  Hypothesis ROOM : (lo + SPA_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis SP16 : (SP mod 16 = 0)%Z.
  Hypothesis LOR : (rt_sp0 RT Σ0 - STACK_WIN <= lo)%Z.
  Hypothesis FRL : (length (rt_frames RT Σ0) + FFA_FRAMES <= FRAMES_MAX)%nat.
  Hypothesis CRD : (FFA_CREDIT <= rt_credit RT Σ0)%Z.
  Hypothesis SPQ : ((d = 0 \/ d = 16) /\ spq = SP - 192 - d)%Z.
  Hypothesis NF : (f mod 64 = 0 /\ 0x669000 <= f /\ f + 1016 <= lo /\ (f + 1016 <= S \/ S + 127 <= f) /\ 0 <= S /\ S + 127 <= lo)%Z.
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
  Notation fc_srel := (Zs7.fc_srel RT Σ0 f).
  Notation fc_ctx := (Zs7.fc_ctx RT Σ0 ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 OUT d spq f me).
  Notation TK L Σ SR := (L RT AF Σ0 Σ sp OUT lo d spq f ROOM TOP LOR (proj1 SR) (proj1 (proj2 SR)) (proj1 (proj2 (proj2 SR))) SPQ NF OUTR) (only parsing).
  Notation TKm L Σ SR := (L RT AF Σ0 Σ sp OUT lo d spq f me ROOM TOP LOR (proj1 SR) (proj1 (proj2 SR)) (proj1 (proj2 (proj2 SR))) SPQ NF OUTR) (only parsing).

  Notation EVP L F fc mb Σ used SR HA :=
    (L sp gp tp F fc lo d spq f A FIRST LAST OUT txt mb (T1 top_spq) ROOM TOP (T1 top_F64) (T1 top_FLO) (T1 top_FSH) (T1 top_FS0) TXR FLR TSEP OUTR
       (T1 top_shpt Σ used mb SR HA) (T1 top_shpo Σ used mb SR HA) (QΣ Σ)) (only parsing).
  Notation EVQ L mb Σ used SR HA :=
    (L sp gp tp lo d spq f A FIRST LAST OUT txt mb (T1 top_spq) ROOM TOP (T1 top_F64) (T1 top_FLO) (T1 top_FSH) (T1 top_FS0) TXR FLR TSEP OUTR
       (T1 top_shpt Σ used mb SR HA) (T1 top_shpo Σ used mb SR HA) (QΣ Σ)
       (T1 top_shpl Σ used mb 0x285a0%Z 10416%Z SR HA ltac:(left; reflexivity) eq_refl) (T1 top_shpl Σ used mb 0x2af20%Z 640%Z SR HA ltac:(right; left; reflexivity) eq_refl)) (only parsing).

  Notation FCS' F fc pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR xra (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 spq) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs3 (Z_to_bv 64 S) xs5 xs6 xs7 xs8 xs9
             xs10 xs11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Lemma fc_bodyc : forall Σ F fc mb, fc_ctx Σ 0 fc mb ->
    forall xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs11 xt4 xt6 c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 (mm : mem),
    rw_cells asegs mm spq [C8 c0; C8 c8; C8 c16; C8 c24; C8 c32; C8 c40; C8 c48; C8 c56; C8 c64; C8 c72; C8 c80] ->
    (exists jp, rw_cells asegs mm (f + 608) [CB 72 jp]) ->
    (exists jz, rw_cells asegs mm (f / 8 + 2147450884) [CB 63 jz]) ->
    rw_cells asegs mm (f / 8 + 2147450956) [CB 9 (repeat (Z_to_bv 8 0) 9)] ->
    (exists v, rw_cells asegs mm OUT [C8 v]) ->
    bytes_at asegs mm A txt -> mem_inv asegs mm -> munch W mb mm -> wmono asegs mb mm -> stk asegs mm lo spq ->
    evt asegs (QΣ Σ) (FCS' F fc 0xc4868 xra xt0 xt1 xt2 (Z_to_bv 64 (FIRST / 8)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs5 (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) (Z_to_bv 64 OUT)
                          (Z_to_bv 64 2147450880) (Z_to_bv 64 1) xs11 (Z_to_bv 64 0xA0000002E) xt4 (Z_to_bv 64 53) xt6 mm).
  Proof using TOPH.
    intros Σ F fc mb CTX. pose proof CTX as (SR & HU & FRM & HA & MRb & PKb).
    eapply (EVP fc_body F fc mb Σ 0%Z SR HA).
    - exact (T1 fc_kerra Σ 0%Z F fc mb CTX).
    - exact (T1 fc_kerrb Σ 0%Z F fc mb CTX).
    - exact FRM.
    - exact (T1 top_shpl Σ 0%Z mb 0x285a0%Z 10416%Z SR HA ltac:(left; reflexivity) eq_refl).
    - exact (T1 top_shpl Σ 0%Z mb 0x2af20%Z 640%Z SR HA ltac:(right; left; reflexivity) eq_refl).
    - exact (T1 fc_k7f4 Σ 0%Z fc mb CTX).
    - exact (T1 fc_kmset (T1 fc_kpdc) (T1 fc_kndc) Σ fc mb CTX).
  Qed.
End FCTOP.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Z87 Zti Zu3 Zu0.

Lemma fc_cb8s_c8s : forall segs (m : mem) A (bss : list (list byte)) pre,
  rw_cells segs m A (pre ++ map (CB 8) bss) -> rw_cells segs m A (pre ++ map (fun b => C8 (le_bytes_to_word b)) bss).
Proof.
  intros segs m A bss. induction bss as [| b bss IH]; intros pre H; [exact H|].
  cbn [map] in *. apply num_cb8_c8 in H.
  replace (pre ++ C8 (le_bytes_to_word b) :: map (CB 8) bss) with ((pre ++ [C8 (le_bytes_to_word b)]) ++ map (CB 8) bss) in H by (rewrite <- app_assoc; reflexivity).
  apply IH in H. rewrite <- app_assoc in H. exact H.
Qed.

Theorem fca_ok : forall RT, art_facts RT -> rt_contracts_f RT ->
  forall PMc, fdfs_only PMc -> mat_stable PMc -> pdca_stmt RT PMc -> ndca_stmt RT PMc -> fca_stmt RT PMc.
Proof.
  intros RT AF RTF PMc FDO MST HPDC HNDC. unfold fca_stmt.
  intros Σ K ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A FIRST LAST OUT lo p n txt v0
    ETP FRM FRL CRD ART0 MI ST LOR ROOM TOP SP16 PIN P8 PA PL PT TXT TLR FL1 FL2 FL3 OUTC O8 OSP OTOP HK.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof ROOM as ROOM'. pose proof TOP as TOP'. unfold SPA_STACK, NDCA_STACK, P5A_STACK, LMA_STACK, RT_STACK, USTACK_TOP in ROOM', TOP'.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. unfold SEGTOP_A, STACK_WIN, USTACK_TOP in SP0R. pose proof LOR as LOR'. unfold STACK_WIN in LOR'.
  pose proof (af_live_range RT AF Σ m p n ART0 PIN) as (LR1 & LR2 & _). unfold STACK_WIN in LR2.
  unfold USTACK_TOP in OTOP. unfold FFA_FRAMES in FRL. unfold FFA_CREDIT in CRD.
  apply (aevt_evt RT AF PMc MST).
  eapply (fc_pro1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m ROOM TOP SP16 ltac:(lia) _
            (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) (Z_to_bv 64 OUT) (Z_to_bv 64 53) (Z_to_bv 64 0xA0000002E) (Z_to_bv 64 1));
    [| exact MI | exact ST | exact (af_client_consts RT AF Σ m ART0)].

  intros d spq xt0 xt1 xt2 ya1 ya2 xa6 xa7 xt4 xt6 mm REAL MI1 MU1 WM1 ST1.
  destruct REAL as (Hd & Hspq & (jsp & SPILLc) & (jh & HIGHc) & SAVED).
  apply evt_done.
  apply (bytes_at_transport asegs [((bv_unsigned sp - 208)%Z, bv_unsigned sp)] m mm) in TXT; [| exact MU1 | cbn [disjoint_from]; split; [lia| exact I]].
  apply (rw_cells_transport asegs [((bv_unsigned sp - 208)%Z, bv_unsigned sp)] m mm) in OUTC; [| exact MU1 | exact WM1 | cbn [disjoint_from cells_size csize Nat.add]; split; [lia| exact I]].
  assert (FP1 : fp_ok RT Σ lo [((bv_unsigned sp - 208)%Z, bv_unsigned sp)]) by (constructor; [left; cbn [fst snd]; unfold USTACK_TOP; lia| constructor]).
  pose proof (art_of_munch RT AF Σ m mm lo _ ART0 LOR FP1 MU1 WM1) as ART1.
  assert (COK : call_ok RT Σ mm (Z_to_bv 64 spq) lo).
  { unfold call_ok. rewrite unsigned_lit by lia. split; [exact ST1|]. split; [exact LOR|]. unfold RT_STACK, USTACK_TOP.
    split; [lia|]. split; [lia| Z.div_mod_to_equations; lia]. }
  eapply (aevt_stack_malloc RT RTF PMc FDO MST Σ K 4%nat); [right; left; reflexivity | exact ETP | unfold FRAMES_MAX in *; lia | lia | exact ART1 | exact MI1 | exact COK | exact FRM |].
  intros Σ' f q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' m' FRM' RA PR W1 W2 EF EL ES EC F0 F64 FTOP.
  rewrite ?unsigned_lit in RA, PR by lia. destruct RA as (ART' & MI' & WM' & ST').

  pose proof (agree_pres _ _ _ mm m' (fun x => aclient (rt_live RT Σ) (rt_frames RT Σ) spq x) PR (fun x H => H)) as AG.
  unfold LM_SAVED in SAVED.
  rt_transport_with mm m' AG WM' ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; cbv beta; aclient_tac).

  assert (MREL : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(OUT, (OUT + 8)%Z)] m m').
  { eapply pres_fp_trans.
    - apply (pres_fp_of_munch _ _ _ _ _ _ _ MU1). intros a Ha _. pose proof (aclient_split_c RT AF Σ m _ a ART0 Ha) as SPL.
      cbn [outside]. split; [lia| exact I].
    - intros a Ha _. apply PR. eapply aclient_mono; [exact Ha| auto| auto| lia]. }
  assert (MRb : fc_mrel RT Σ sp OUT m m') by (split; [exact (wmono_trans asegs _ _ _ WM1 WM')| exact MREL]).

  assert (HinF : In (f, 4%nat) (rt_frames RT Σ')) by (rewrite EF; left; reflexivity).
  pose proof (new_frame_facts RT AF Σ' m' f 4 1016 lo ART' ltac:(rewrite ES; exact LOR) HinF eq_refl eq_refl ltac:(lia)) as NF.
  change (1016 / 8)%Z with 127%Z in NF.
  pose proof (af_frames_range RT AF Σ' m' f 4%nat ART' HinF) as (_ & _ & _ & FR4). specialize (FR4 p n ltac:(rewrite EL; exact PIN)).
  pose proof (proj1 (af_fshadow_apart RT AF Σ' m' f 4%nat ART' HinF) p n ltac:(rewrite EL; exact PIN)) as FS4.
  change (fs_size 4) with 1024%Z in FR4, FS4. unfold shad, SHB in FS4.
  replace ((f + 1024) / 8)%Z with (f / 8 + 128)%Z in FS4 by (clear - F64; Z.div_mod_to_equations; lia).
  change (fs_size 4 - 8)%Z with 1016%Z in W1. change (fs_size 4 / 8)%Z with 128%Z in W2. unfold shad, SHB in W2.
  pose proof (wr_at_sub m' f 1016 (f + 32) 504 W1 ltac:(lia) ltac:(lia) ltac:(lia)) as WBIG.
  destruct (wr_at_rw_CB m' f 1016 W1 ltac:(lia)) as [jf FRD]. destruct (wr_at_rw_CB m' _ 128 W2 ltac:(lia)) as [js FRS].
  change (Z.to_nat 1016) with 1016%nat in FRD. change (Z.to_nat 128) with 128%nat in FRS.
  apply (rw_cells_split_CB asegs m' f [] 1016 jf [] [32; 504; 72; 72; 336]%nat) in FRD; [| reflexivity]. cbn [mk_CB_cells app] in FRD.
  destruct (proj1 (num_rw_cells_app asegs _ _ [CB 32 _] _) FRD) as [HDR0 FD1]. clear FRD.
  cbn [cells_size csize Nat.add] in FD1. change (Z.of_nat 32) with 32%Z in FD1.
  destruct (proj1 (num_rw_cells_app asegs _ _ [CB 504 _; CB 72 _] _) FD1) as [_ FD2]. clear FD1.
  cbn [cells_size csize Nat.add] in FD2. change (Z.of_nat 576) with 576%Z in FD2.
  destruct (proj1 (num_rw_cells_app asegs _ _ [CB 72 _] _) FD2) as [PNS0 _]. clear FD2.
  replace (f + 32 + 576)%Z with (f + 608)%Z in PNS0 by lia.
  apply (rw_cells_split_CB asegs m' f [] 32 _ [] [8;8;8;8]%nat) in HDR0; [| reflexivity]. cbn [app] in HDR0. rewrite app_nil_r in HDR0.
  apply (rw_cells_split_CB asegs m' _ [] 128 js [] [4; 63; 9; 9; 7; 36]%nat) in FRS; [| reflexivity]. cbn [mk_CB_cells app] in FRS.
  destruct (proj1 (num_rw_cells_app asegs _ _ [CB 4 _] _) FRS) as [S0 FRS1]. clear FRS. cbn [cells_size csize Nat.add] in FRS1. change (Z.of_nat 4) with 4%Z in FRS1.
  destruct (proj1 (num_rw_cells_app asegs _ _ [CB 63 _] _) FRS1) as [SZ FRS2]. clear FRS1. cbn [cells_size csize Nat.add] in FRS2. change (Z.of_nat 63) with 63%Z in FRS2.
  destruct (proj1 (num_rw_cells_app asegs _ _ [CB 9 _] _) FRS2) as [S1 FRS3]. clear FRS2. cbn [cells_size csize Nat.add] in FRS3. change (Z.of_nat 9) with 9%Z in FRS3.
  destruct (proj1 (num_rw_cells_app asegs _ _ [CB 9 _] _) FRS3) as [SP9 FRS4]. clear FRS3. cbn [cells_size csize Nat.add] in FRS4. change (Z.of_nat 9) with 9%Z in FRS4.
  destruct (proj1 (num_rw_cells_app asegs _ _ [CB 7 _] _) FRS4) as [S3 _]. clear FRS4.
  replace (f / 8 + 2147450880 + 4)%Z with (f / 8 + 2147450884)%Z in SZ, S1, SP9, S3 by lia.
  replace (f / 8 + 2147450884 + 63)%Z with (f / 8 + 2147450947)%Z in S1, SP9, S3 by lia.
  replace (f / 8 + 2147450947 + 9)%Z with (f / 8 + 2147450956)%Z in SP9, S3 by lia.
  replace (f / 8 + 2147450956 + 9)%Z with (f / 8 + 2147450965)%Z in S3 by lia.
  destruct NF as (NF1 & NF2 & NF3 & NF4 & NF5 & NF6).

  apply (aevt_evt RT AF PMc MST).
  replace (ret_pc (Z_to_bv 64 804440)) with (Z_to_bv 64 804440) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  eapply (fc_poison f FIRST m' NF1 ltac:(lia) NF4 ltac:(lia) ltac:(lia) _); [| exact HDR0 | exact S0 | exact SZ | exact S1 | exact SP9 | exact S3 | exact MI' | apply munch_refl | apply wmono_refl].
  intros a1' a2' a3' h' jz' mm2 HDR2 SHZ2 SHP2 MI2 MU2 WM2.
  apply evt_done.
  clear HDR0 S0 SZ S1 SP9 S3 MI' AG.
  transport_after_call asegs m' mm2 MU2 WM2.

  assert (SR : Zs7.fc_srel RT Σ f Σ' 0) by (unfold Zs7.fc_srel; repeat split; try assumption; lia).
  assert (SPQ : ((d = 0 \/ d = 16) /\ spq = bv_unsigned sp - 192 - d)%Z) by (split; [exact Hd| lia]).
  assert (NF : (f mod 64 = 0 /\ 0x669000 <= f /\ f + 1016 <= lo /\ (f + 1016 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 127 <= f) /\ 0 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 127 <= lo)%Z)
    by (repeat split; assumption).
  assert (OUTR : (OUT mod 8 = 0 /\ bv_unsigned sp <= OUT /\ OUT + 8 <= USTACK_TOP)%Z) by (unfold USTACK_TOP; repeat split; assumption).
  assert (PCH : (p mod 8 = 0 /\ p <= A /\ LAST + 8 <= p + n /\ A + Z.of_nat (length txt) <= p + n)%Z) by (repeat split; assumption).
  assert (TXR : (0 < A /\ A + Z.of_nat (length txt) <= lo /\ Z.of_nat (length txt) < 2147483648)%Z) by (repeat split; lia).
  assert (FLR : (A <= FIRST /\ FIRST < LAST /\ LAST <= A + Z.of_nat (length txt))%Z) by (repeat split; assumption).
  assert (TSEP : ((A + Z.of_nat (length txt) <= f \/ f + 1024 <= A) /\ (A + Z.of_nat (length txt) <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 128 <= A))%Z) by (split; lia).
  assert (HW2 : tk_wf sp OUT lo f [(f, (f + 32)%Z); ((f / 8 + 2147450880)%Z, (f / 8 + 2147450880 + 92)%Z)])
    by exact (tk_wf_W2 RT AF Σ Σ' sp OUT lo d spq f ROOM TOP LOR EF EL ES SPQ NF OUTR).
  assert (CTX : Zs7.fc_ctx RT Σ ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 OUT d spq f m Σ' 0 fc' mm2).
  { split; [exact SR|]. split; [lia|]. split; [exact FRM'|].
    split; [exact (art_of_munch RT AF Σ' m' mm2 lo _ ART' ltac:(rewrite ES; exact LOR)
                     (tk_fpok RT AF Σ Σ' sp OUT lo d spq f ROOM TOP LOR EF EL ES SPQ NF OUTR _ HW2) MU2 WM2)|].
    split; [exact (fc_mrel_munch RT AF Σ Σ' sp OUT lo d spq f m ROOM TOP LOR EF EL ES SPQ NF OUTR _ m' mm2 HW2 ART' MRb MU2 WM2)|].
    split; [exists jh; exact HIGHc|]. split; [exact SAVED|]. split; [exists h'; exact HDR2|].
    split; [exact W2| exact WBIG]. }
  apply (rw_cells_split_CB asegs mm2 _ [] 88 jsp [] [8;8;8;8;8;8;8;8;8;8;8]%nat) in SPILLc; [| reflexivity]. cbn [mk_CB_cells app] in SPILLc.
  repeat match type of SPILLc with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in SPILLc; clearbody j end.
  lazymatch type of SPILLc with rw_cells _ _ _ [CB 8 ?b0; CB 8 ?b1; CB 8 ?b2; CB 8 ?b3; CB 8 ?b4; CB 8 ?b5; CB 8 ?b6; CB 8 ?b7; CB 8 ?b8; CB 8 ?b9; CB 8 ?b10] =>
    change [CB 8 b0; CB 8 b1; CB 8 b2; CB 8 b3; CB 8 b4; CB 8 b5; CB 8 b6; CB 8 b7; CB 8 b8; CB 8 b9; CB 8 b10]
      with ([] ++ map (CB 8) [b0; b1; b2; b3; b4; b5; b6; b7; b8; b9; b10]) in SPILLc end.
  apply fc_cb8s_c8s in SPILLc. cbn [map app] in SPILLc.
  apply (aevt_evt RT AF PMc MST).
  eapply evt_eq; [| eapply (fc_bodyc RT AF RTF PMc FDO MST HPDC HNDC Σ K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 OUT lo d spq f p n A FIRST LAST txt m
              ETP ROOM TOP SP16 LOR FRL CRD SPQ NF OUTR PIN PCH TXR FLR TSEP HK Σ' F' fc' mm2 CTX);
      [exact SPILLc | eexists; exact PNS0 | exists jz'; exact SHZ2 | exact SHP2 | exists v0; exact OUTC | exact TXT | exact MI2 | apply munch_refl | apply wmono_refl | exact ST']].
  num_st_eq.
Qed.

Theorem fca_closed : forall RT, art_facts RT -> rt_contracts_f RT -> forall PMc, fdfs_only PMc -> mat_stable PMc -> fca_stmt RT PMc.
Proof.
  intros RT AF RTF PMc FDO MST.
  pose proof (p5a_closed RT AF RTF (num_lits_of_af RT AF) PMc FDO MST) as HP5.
  exact (fca_ok RT AF RTF PMc FDO MST (pdca_ok RT AF RTF PMc FDO MST HP5) (ndca_ok RT AF RTF PMc FDO MST HP5)).
Qed.
