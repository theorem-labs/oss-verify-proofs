(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjNumber SjNumU.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_bkit Sj_num_bdefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Definition FROMCHB_ENTRY : Z := 0x9e77c.

Section Stmt.
Variable RT : rt_sig.
Variable PMc : Model -> Prop.
Definition fromchb_stmt : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (A off stop lo p n : Z) (txt : list byte) (b : byte),
  tp = Z_to_bv 64 B_TP -> frm0 fc ->
  (length (rt_frames RT Σ) + FFB_FRAMES <= FRAMES_MAX)%nat -> (FFB_CREDIT <= rt_credit RT Σ)%Z ->
  ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> (rt_sp0 RT Σ - STACK_WIN <= lo)%Z -> (lo + FFB_STACK <= bv_unsigned sp)%Z ->
  (bv_unsigned sp + 16 <= USTACK_TOP)%Z -> (bv_unsigned sp mod 16 = 0)%Z ->
  In (p, n) (rt_live RT Σ) -> (p mod 8 = 0)%Z -> (p <= A)%Z -> (A + stop + 8 <= p + n)%Z -> (A + Z.of_nat (length txt) <= p + n)%Z ->
  bytes_at bsegs m A txt -> (Z.of_nat (length txt) < 2147483648)%Z ->
  (0 <= off <= stop)%Z -> nth_error txt (Z.to_nat stop) = Some b -> numchar (bv_unsigned b) = false ->
  (forall (Σ' : rts RT) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m', frm0 fc' ->
     rt_after RT Σ' (bv_unsigned sp) lo m m' -> rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m' ->
     rt_frames RT Σ' = rt_frames RT Σ -> rt_live RT Σ' = rt_live RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     (rt_credit RT Σ - FFB_CREDIT <= rt_credit RT Σ')%Z ->
     aevt RT PMc Σ' K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F' (ret_pc ra) fc' None m' (seg_rom bsegs))) ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (A + off)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 FROMCHB_ENTRY) fc None m (seg_rom bsegs)).
End Stmt.

Record fcenv : Type := mkFcEnv {
  c_ra : word; c_sp : word; c_gp : word; c_tp : word;
  c_s0 : word; c_s1 : word; c_s2 : word; c_s3 : word; c_s4 : word; c_s5 : word;
  c_s6 : word; c_s7 : word; c_s8 : word; c_s9 : word; c_s10 : word; c_s11 : word;
  c_A : Z; c_off : Z; c_stop : Z; c_lo : Z; c_p : Z; c_n : Z; c_txt : list byte; c_b : byte }.
Notation c_SP E := (bv_unsigned (c_sp E)).
Notation c_TL E := (Z.of_nat (length (c_txt E))).

Record fc_ok (E : fcenv) : Prop := mkFcOk {
  co_room : (c_lo E + FFB_STACK <= c_SP E)%Z;
  co_top : (c_SP E + 16 <= USTACK_TOP)%Z;
  co_tmax : (c_TL E < 2147483648)%Z;
  co_off : (0 <= c_off E <= c_stop E)%Z;
  co_stop : nth_error (c_txt E) (Z.to_nat (c_stop E)) = Some (c_b E);
  co_nc : numchar (bv_unsigned (c_b E)) = false;
  co_chunk : (0 < c_p E /\ c_p E <= c_A E /\ c_A E + c_stop E + 8 <= c_p E + c_n E /\ c_A E + c_TL E <= c_p E + c_n E /\ c_p E + c_n E <= c_lo E)%Z }.

Notation FC_W E := [(c_SP E - 16, c_SP E)]%Z.

Definition FCINV (E : fcenv) (m0 mm : mem) : Prop :=
  (exists j0, rw_cells bsegs mm (c_SP E + -16) [CB 8 j0; C8 (c_ra E)]) /\
  bytes_at bsegs mm (c_A E) (c_txt E) /\
  mem_inv bsegs mm /\ munch (FC_W E) m0 mm /\ wmono bsegs m0 mm /\
  stk bsegs mm (c_lo E) (c_SP E + -16).

Notation FCS E pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm :=
  (MS (mkR xra (Z_to_bv 64 (c_SP E + -16)) (c_gp E) (c_tp E) xt0 xt1 xt2 (c_s0 E) (c_s1 E) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           (c_s2 E) (c_s3 E) (c_s4 E) (c_s5 E) (c_s6 E) (c_s7 E) (c_s8 E) (c_s9 E) (c_s10 E) (c_s11 E) xt3 xt4 xt5 xt6) xF (Z_to_bv 64 pc) xfc None mm (seg_rom bsegs)).

Section SCAN.
  Variable E : fcenv.
  Hypothesis OK : fc_ok E.
  Variable m0 : mem.

  Hypothesis SHPT : forall m', munch (FC_W E) m0 m' -> wmono bsegs m0 m' -> shz m' (c_p E) (8 * (c_n E / 8)).
  Variable Q : machine_state -> Prop.
  Notation A := (c_A E).

  Definition fc_end_k : Prop :=
    forall (e : Z) xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm,
      FCINV E m0 mm -> frm0 xfc -> (c_off E <= e <= c_stop E)%Z ->
      evt bsegs Q (FCS E 0x9e818 xra xt0 xt1 xt2 (Z_to_bv 64 (A + c_off E)) (Z_to_bv 64 (A + e)) xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm).

  Lemma fcb_scan : fc_end_k -> forall (f : nat) (cur : Z) xra xt0 xt1 xt2 xt3 xt4 xt5 xt6 xF xfc mm,
    FCINV E m0 mm -> frm0 xfc -> (c_off E <= cur <= c_stop E)%Z -> (c_stop E - cur <= Z.of_nat f)%Z ->
    evt bsegs Q (FCS E 0x9e7cc xra xt0 xt1 xt2 (Z_to_bv 64 (A + c_off E)) (Z_to_bv 64 (A + cur)) (Z_to_bv 64 (A + cur))
                     (Z_to_bv 64 10) (Z_to_bv 64 (-1)) (Z_to_bv 64 58) (Z_to_bv 64 2147450880) (Z_to_bv 64 NUMMASK) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK SHPT.
    intros KEND f. induction f as [|f IH]; intros until mm; intros INV FRM Hc Hf.
    all: pose proof INV as INV0; destruct INV0 as ((j0 & FR) & TXT & MI & MU & WM & ST);
      pose proof (bytes_at_bound _ _ _ _ TXT) as TXB;
      destruct OK as [ROOM TOP TMAX HOFF HSTOP HNC (P0 & PA & PS & PT & PLO)]; unfold USTACK_TOP in *;
      pose proof (bv_unsigned_in_range 64 (c_sp E)) as SPR; unfold bv_modulus in SPR; cbn in SPR;
      assert (SL : (c_stop E < c_TL E)%Z)
        by (assert (X : nth_error (c_txt E) (Z.to_nat (c_stop E)) <> None) by (rewrite HSTOP; discriminate); apply nth_error_Some in X; lia);
      assert (N8 : (c_n E - 7 <= 8 * (c_n E / 8))%Z) by (Z.div_mod_to_equations; lia);
      unfold NUMMASK in *.
    all: zastep; replace (A + cur - A)%Z with cur by lia;
      set (c := nth (Z.to_nat cur) (c_txt E) (Z_to_bv 8 0));
      assert (CR : (0 <= bv_unsigned c < 256)%Z) by (pose proof (bv_unsigned_in_range 8 c) as R; unfold bv_modulus in R; cbn in R; lia);
      assert (CS : cur = c_stop E -> numchar (bv_unsigned c) = false)
        by (intros ->; unfold c; rewrite (nth_error_nth _ _ _ HSTOP); exact HNC);
      clearbody c.
    all: zstep; zstep; if_cases K0; zify_cond K0.
    all: try (assert (NC : numchar (bv_unsigned c) = true)
                by (unfold numchar; rewrite (proj2 (Z.leb_le 48 (bv_unsigned c))), (proj2 (Z.leb_le (bv_unsigned c) 57)) by lia; reflexivity);
              assert (cur <> c_stop E) by (intros X; specialize (CS X); congruence)).
    - exfalso; lia.
    - zstep. zstep. if_cases K1; zify_cond K1.
      { eapply evt_eq; [| eapply (KEND cur)]; [num_st_eq | exact INV | exact FRM | lia]. }
      zstep. zstep. zstep.
      assert (K43 : (43 <= bv_unsigned c <= 101)%Z) by lia.
      replace ((bv_unsigned c + -43) mod 64)%Z with (bv_unsigned c - 43)%Z by (rewrite Z.mod_small; lia).
      assert (ND : ~ (48 <= bv_unsigned c <= 57)%Z) by lia.
      pose proof (numchar_mask (bv_unsigned c) CR ND K43) as NM. unfold NUMMASK in NM. rewrite NM. clear NM.
      destruct (numchar (bv_unsigned c)) eqn:NC.
      + exfalso. assert (cur = c_stop E) by lia. specialize (CS H). congruence.
      + change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true. cbv iota.
        eapply evt_eq; [| eapply (KEND cur)]; [num_st_eq | exact INV | exact FRM | lia].
    - zstep. if_cases KT; zify_cond KT; [exfalso; lia|].
      zstep. zstep. zastep. zastep. zastep. zastep. if_true.
      eapply evt_eq; [| eapply (IH (cur + 1)%Z)]; [num_st_eq | exact INV | exact FRM | lia | lia].
    - zstep. zstep. if_cases K1; zify_cond K1.
      { eapply evt_eq; [| eapply (KEND cur)]; [num_st_eq | exact INV | exact FRM | lia]. }
      zstep. zstep. zstep.
      assert (K43 : (43 <= bv_unsigned c <= 101)%Z) by lia.
      replace ((bv_unsigned c + -43) mod 64)%Z with (bv_unsigned c - 43)%Z by (rewrite Z.mod_small; lia).
      assert (ND : ~ (48 <= bv_unsigned c <= 57)%Z) by lia.
      pose proof (numchar_mask (bv_unsigned c) CR ND K43) as NM. unfold NUMMASK in NM. rewrite NM. clear NM.
      destruct (numchar (bv_unsigned c)) eqn:NC.
      + assert (cur <> c_stop E) by (intros X; specialize (CS X); congruence).
        change (bv_eqb (Z_to_bv 64 1) (Z_to_bv 64 0)) with false. cbv iota.
        zstep. if_cases KT; zify_cond KT; [exfalso; lia|].
        zstep. zstep. zastep. zastep. zastep. zastep. if_true.
        eapply evt_eq; [| eapply (IH (cur + 1)%Z)]; [num_st_eq | exact INV | exact FRM | lia | lia].
      + change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true. cbv iota.
        eapply evt_eq; [| eapply (KEND cur)]; [num_st_eq | exact INV | exact FRM | lia].
  Qed.
End SCAN.

Section TOP.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Variable PMc : Model -> Prop.
  Hypothesis MST : mat_stable PMc.
  Hypothesis HFF : ffb_stmt RT PMc.

  Theorem fromchb_walk : fromchb_stmt RT PMc.
  Proof using AF MST HFF.
    unfold fromchb_stmt. intros until b. intros ETP FRM FRL CRD ART0 MI ST LOR ROOM TOP SP16 HIN P8 PA PS PT TXT TMAX HOFF HSTOP HNC HK.
    set (E := mkFcEnv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 A off stop lo p n txt b).
    pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
    pose proof (af_live_range RT AF Σ m p n ART0 HIN) as (P0 & PHI & _).
    assert (OK : fc_ok E).
    { unfold E. constructor; cbn [c_lo c_sp c_txt c_off c_stop c_b c_p c_A c_n]; try assumption; try lia. }
    assert (FPOK : forall Σ0, fp_ok RT Σ0 lo (FC_W E)).
    { intros Σ0. unfold E. cbn [c_sp]. assert (FS16 : (16 <= FFB_STACK)%Z) by (vm_compute; discriminate).
      constructor; [left; cbn [fst snd]; lia| constructor]. }
    pose proof (shzp_live RT AF Σ m lo (FC_W E) p n ART0 LOR (FPOK Σ) HIN P8) as SHPT.
    destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _). unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SHB in G1, G2.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (ROOM0 := ROOM).
    assert (FS16 : (16 <= FFB_STACK)%Z) by (vm_compute; discriminate).
    unfold USTACK_TOP in TOP. unfold SEGTOP_A, STACK_WIN, USTACK_TOP in SP0R, LOR, PHI.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    apply (aevt_evt RT AF PMc MST).
    pose proof (munch_refl (FC_W E) m) as MU. pose proof (wmono_refl bsegs m) as WM.
    set (mb := m) in MU at 1, WM at 1, SHPT.
    unfold E in MU; cbn [c_sp] in MU.
    unfold FROMCHB_ENTRY.
    step.
    carve_frame 16%nat ST.
    apply (rw_cells_split_CB bsegs m _ [] 16 junk [] [8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    step. zstep. if_cases KT; zify_cond KT; [exfalso; lia|]. clear KT.
    do 13 zstep.
    clear G1 G2.
    zastep. zastep. zastep. zastep. if_false.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) => assert (INV : FCINV E mb m1) by
      (unfold FCINV, E; cbn [c_sp c_A c_txt c_ra c_lo];
       split; [eexists; eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption) end.
    lazymatch goal with |- evt _ ?Q _ => assert (KEND : fc_end_k E mb Q) end.
    2: { eapply evt_eq; [| eapply (fcb_scan E OK mb SHPT _ KEND (Z.to_nat stop) off); [exact INV | exact FRM | unfold E; cbn [c_off c_stop]; lia | unfold E; cbn [c_off c_stop]; lia]].
         unfold NUMMASK, E; cbn [c_sp c_A c_off c_gp c_tp c_s0 c_s1 c_s2 c_s3 c_s4 c_s5 c_s6 c_s7 c_s8 c_s9 c_s10 c_s11]; num_st_eq. }

    clear INV. clear dependent junk. clear dependent j.
    unfold fc_end_k.
    intros e xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm INV FRMx He.
    unfold E in He; cbn [c_off c_stop] in He.
    destruct INV as ((jx & FRx) & TXTx & MIx & MUx & WMx & STx).
    unfold E in FRx, TXTx, MUx, STx |- *; cbn [c_sp c_A c_txt c_s0 c_s1 c_ra c_lo c_off c_gp c_tp c_s2 c_s3 c_s4 c_s5 c_s6 c_s7 c_s8 c_s9 c_s10 c_s11] in FRx, TXTx, MUx, STx |- *.
    assert (SL : (stop < Z.of_nat (length txt))%Z)
      by (assert (X : nth_error txt (Z.to_nat stop) <> None) by (rewrite HSTOP; discriminate); apply nth_error_Some in X; lia).
    zstep. zstep.
    release_frame FRx STx (bv_unsigned sp).
    zstep. apply evt_done.
    assert (ARTx : ART RT Σ mm) by (exact (art_of_munch RT AF Σ mb mm lo _ ART0 LOR (FPOK Σ) MUx WMx)).
    eapply (HFF Σ) with (A := A) (FIRST := (A + off)%Z) (LAST := (A + e)%Z) (lo := lo) (p := p) (n := n) (txt := txt);
      [ exact ETP | exact FRMx | exact FRL | exact CRD | exact ARTx | exact MIx | exact STx | unfold STACK_WIN; lia | exact ROOM0 | unfold USTACK_TOP; lia
      | exact SP16 | exact HIN | exact P8 | lia | lia | lia | exact TXTx | lia | lia | lia | ].

    intros Σ' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' FRM' RA PR EF EL ES EC.
    destruct RA as (ART' & MI' & WM' & ST').
    apply HK; [exact FRM' | | | exact EF | exact EL | exact ES | exact EC].
    - split; [exact ART'|]. split; [exact MI'|]. split; [exact (wmono_trans bsegs _ _ _ WMx WM')| exact ST'].
    - intros a Ha. rewrite (PR a Ha). apply MUx.
      pose proof (aclient_split_c RT AF Σ m _ _ ART0 Ha) as SPL. unfold STACK_WIN in SPL.
      cbn [outside]. split; [lia| exact I].
  Qed.
End TOP.

Theorem fromchb_ok : forall RT, art_facts RT ->
  (forall PMc, fdfs_only PMc -> mat_stable PMc -> ffb_stmt RT PMc) ->
  forall PMc, fdfs_only PMc -> mat_stable PMc -> fromchb_stmt RT PMc.
Proof. intros RT AF HFF PMc FDO MST. exact (fromchb_walk RT AF PMc MST (HFF PMc FDO MST)). Qed.
