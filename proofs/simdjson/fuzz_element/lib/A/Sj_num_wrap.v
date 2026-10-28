(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjNumber.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_adefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Record nwenv : Type := mkNwEnv {
  w_ra : word; w_sp : word; w_gp : word; w_tp : word;
  w_s0 : word; w_s1 : word; w_s2 : word; w_s3 : word; w_s4 : word; w_s5 : word;
  w_s6 : word; w_s7 : word; w_s8 : word; w_s9 : word; w_s10 : word; w_s11 : word;
  w_A : Z; w_off : Z; w_stop : Z; w_OUT : Z; w_lo : Z; w_p : Z; w_n : Z; w_txt : list byte; w_b : byte }.
Notation w_SP E := (bv_unsigned (w_sp E)).
Notation w_TL E := (Z.of_nat (length (w_txt E))).

Record nw_ok (E : nwenv) : Prop := mkNwOk {
  wo_room : (w_lo E + NUMA_STACK <= w_SP E)%Z;
  wo_top : (w_SP E + 16 <= USTACK_TOP)%Z;
  wo_tmax : (w_TL E < 2147483648)%Z;
  wo_off : (0 <= w_off E <= w_stop E)%Z;
  wo_stop : nth_error (w_txt E) (Z.to_nat (w_stop E)) = Some (w_b E);
  wo_nc : numchar (bv_unsigned (w_b E)) = false;
  wo_chunk : (0 < w_p E /\ w_p E <= w_A E /\ w_A E + w_stop E + 8 <= w_p E + w_n E /\ w_A E + w_TL E <= w_p E + w_n E /\ w_p E + w_n E <= w_lo E)%Z;
  wo_out : (w_SP E <= w_OUT E /\ w_OUT E + 8 <= USTACK_TOP)%Z }.

Notation NW_W E := [(w_SP E - 32, w_SP E); (w_OUT E, w_OUT E + 8)]%Z.

Definition NWINV (E : nwenv) (m0 mm : mem) : Prop :=
  (exists j0, rw_cells asegs mm (w_SP E + -32) [CB 8 j0; C8 (w_s1 E); C8 (w_s0 E); C8 (w_ra E)]) /\
  (exists junk, rw_cells asegs mm (w_OUT E) [CB 8 junk]) /\
  bytes_at asegs mm (w_A E) (w_txt E) /\
  mem_inv asegs mm /\ munch (NW_W E) m0 mm /\ wmono asegs m0 mm /\
  stk asegs mm (w_lo E) (w_SP E + -32).

Notation NWS E pc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm :=
  (MS (mkR xra (Z_to_bv 64 (w_SP E + -32)) (w_gp E) (w_tp E) xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           (w_s2 E) (w_s3 E) (w_s4 E) (w_s5 E) (w_s6 E) (w_s7 E) (w_s8 E) (w_s9 E) (w_s10 E) (w_s11 E) xt3 xt4 xt5 xt6) xF (Z_to_bv 64 pc) xfc None mm (seg_rom asegs)).

Section SCAN.
  Variable E : nwenv.
  Hypothesis OK : nw_ok E.
  Variable m0 : mem.

  Hypothesis SHPT : forall m', munch (NW_W E) m0 m' -> wmono asegs m0 m' -> shz m' (w_p E) (8 * (w_n E / 8)).
  Variable Q : machine_state -> Prop.
  Notation A := (w_A E).
  Notation OUT := (w_OUT E).

  Definition nw_end_k : Prop :=
    forall (e : Z) xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm,
      NWINV E m0 mm -> frm0 xfc -> (w_off E <= e <= w_stop E)%Z ->
      evt asegs Q (NWS E 0xe9a70 xra xt0 xt1 xt2 (Z_to_bv 64 OUT) (Z_to_bv 64 2147450880) (Z_to_bv 64 (A + w_off E)) (Z_to_bv 64 (A + e)) xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm).

  Lemma sfa_scan : nw_end_k -> forall (f : nat) (cur : Z) xra xt0 xt1 xt2 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm,
    NWINV E m0 mm -> frm0 xfc -> (w_off E <= cur <= w_stop E)%Z -> (w_stop E - cur <= Z.of_nat f)%Z ->
    evt asegs Q (NWS E 0xe9a2c xra xt0 xt1 xt2 (Z_to_bv 64 OUT) (Z_to_bv 64 2147450880) (Z_to_bv 64 (A + w_off E)) (Z_to_bv 64 (A + cur)) (Z_to_bv 64 (A + cur))
                     (Z_to_bv 64 10) (Z_to_bv 64 58) (Z_to_bv 64 NUMMASK) xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK SHPT.
    intros KEND f. induction f as [|f IH]; intros until mm; intros INV FRM Hc Hf.
    all: pose proof INV as INV0; destruct INV0 as ((j0 & FR) & (junk & OUTC) & TXT & MI & MU & WM & ST);
      pose proof (bytes_at_bound _ _ _ _ TXT) as TXB;
      destruct OK as [ROOM TOP TMAX HOFF HSTOP HNC (P0 & PA & PS & PT & PLO) (HOUT & HOUT2)]; unfold NUMA_STACK, RT_STACK, USTACK_TOP in *;
      pose proof (bv_unsigned_in_range 64 (w_sp E)) as SPR; unfold bv_modulus in SPR; cbn in SPR;
      assert (SL : (w_stop E < w_TL E)%Z)
        by (assert (X : nth_error (w_txt E) (Z.to_nat (w_stop E)) <> None) by (rewrite HSTOP; discriminate); apply nth_error_Some in X; lia);
      assert (N8 : (w_n E - 7 <= 8 * (w_n E / 8))%Z) by (Z.div_mod_to_equations; lia);
      unfold NUMMASK in *.
    all: zastep; zastep; zastep; zastep; if_false.
    all: zastep; replace (A + cur - A)%Z with cur by lia;
      set (c := nth (Z.to_nat cur) (w_txt E) (Z_to_bv 8 0));
      assert (CR : (0 <= bv_unsigned c < 256)%Z) by (pose proof (bv_unsigned_in_range 8 c) as R; unfold bv_modulus in R; cbn in R; lia);
      assert (CS : cur = w_stop E -> numchar (bv_unsigned c) = false)
        by (intros ->; unfold c; rewrite (nth_error_nth _ _ _ HSTOP); exact HNC);
      clearbody c.
    all: zstep; zstep; if_cases K0; zify_cond K0.
    all: try (assert (NC : numchar (bv_unsigned c) = true)
                by (unfold numchar; rewrite (proj2 (Z.leb_le 48 (bv_unsigned c))), (proj2 (Z.leb_le (bv_unsigned c) 57)) by lia; reflexivity);
              assert (cur <> w_stop E) by (intros X; specialize (CS X); congruence)).
    - exfalso; lia.
    - zstep. zstep. if_cases K1; zify_cond K1.
      { eapply evt_eq; [| eapply (KEND cur)]; [num_st_eq | exact INV | exact FRM | lia]. }
      zstep. zstep. zstep.
      assert (K43 : (43 <= bv_unsigned c <= 101)%Z) by lia.
      replace ((bv_unsigned c + -43) mod 64)%Z with (bv_unsigned c - 43)%Z by (rewrite Z.mod_small; lia).
      assert (ND : ~ (48 <= bv_unsigned c <= 57)%Z) by lia.
      pose proof (numchar_mask (bv_unsigned c) CR ND K43) as NM. unfold NUMMASK in NM. rewrite NM. clear NM.
      destruct (numchar (bv_unsigned c)) eqn:NC.
      + exfalso. assert (cur = w_stop E) by lia. specialize (CS H). congruence.
      + change (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false. cbv iota. zstep.
        eapply evt_eq; [| eapply (KEND cur)]; [num_st_eq | exact INV | exact FRM | lia].
    - zstep. zstep. eapply evt_eq; [| eapply (IH (cur + 1)%Z)]; [num_st_eq | exact INV | exact FRM | lia | lia].
    - zstep. zstep. if_cases K1; zify_cond K1.
      { eapply evt_eq; [| eapply (KEND cur)]; [num_st_eq | exact INV | exact FRM | lia]. }
      zstep. zstep. zstep.
      assert (K43 : (43 <= bv_unsigned c <= 101)%Z) by lia.
      replace ((bv_unsigned c + -43) mod 64)%Z with (bv_unsigned c - 43)%Z by (rewrite Z.mod_small; lia).
      assert (ND : ~ (48 <= bv_unsigned c <= 57)%Z) by lia.
      pose proof (numchar_mask (bv_unsigned c) CR ND K43) as NM. unfold NUMMASK in NM. rewrite NM. clear NM.
      destruct (numchar (bv_unsigned c)) eqn:NC.
      + assert (cur <> w_stop E) by (intros X; specialize (CS X); congruence).
        change (negb (bv_eqb (Z_to_bv 64 1) (Z_to_bv 64 0))) with true. cbv iota.
        zstep. zstep. eapply evt_eq; [| eapply (IH (cur + 1)%Z)]; [num_st_eq | exact INV | exact FRM | lia | lia].
      + change (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false. cbv iota. zstep.
        eapply evt_eq; [| eapply (KEND cur)]; [num_st_eq | exact INV | exact FRM | lia].
  Qed.
End SCAN.

Section TOP.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RTF : rt_contracts_f RT.
  Variable PMc : Model -> Prop.
  Hypothesis FDO : fdfs_only PMc.
  Hypothesis MST : mat_stable PMc.
  Hypothesis HFF : ffa_stmt RT PMc.

  Lemma slowfa_walk : forall (Σ : rts RT) (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (A off stop OUT lo p n : Z) (txt : list byte) (b : byte) (junk : list byte),
    tp = Z_to_bv 64 0x6a7e68 -> frm0 fc ->
    (length (rt_frames RT Σ) + NUMA_FRAMES <= FRAMES_MAX)%nat -> rt_frames RT Σ <> [] -> (NUMA_CREDIT <= rt_credit RT Σ)%Z ->
    ART RT Σ m -> mem_inv asegs m ->
    stk asegs m lo (bv_unsigned sp) -> (rt_sp0 RT Σ - STACK_WIN <= lo)%Z -> (lo + NUMA_STACK <= bv_unsigned sp)%Z ->
    (bv_unsigned sp + 16 <= USTACK_TOP)%Z -> (bv_unsigned sp mod 16 = 0)%Z ->
    In (p, n) (rt_live RT Σ) -> (p mod 8 = 0)%Z -> (p <= A)%Z -> (A + stop + 8 <= p + n)%Z -> (A + Z.of_nat (length txt) <= p + n)%Z ->
    bytes_at asegs m A txt -> (Z.of_nat (length txt) < 2147483648)%Z ->
    (0 <= off <= stop)%Z -> nth_error txt (Z.to_nat stop) = Some b -> numchar (bv_unsigned b) = false ->
    rw_cells asegs m OUT [CB 8 junk] -> (bv_unsigned sp <= OUT)%Z -> (OUT + 8 <= USTACK_TOP)%Z -> (OUT mod 8 = 0)%Z ->
    aevt RT PMc Σ
      (fun c => exists (Σ' : rts RT),
         ASTA RT Σ' PMc (fun ms => exists m' v (flag : bool),
             ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (if flag then 9 else 0)) m' ms
           /\ frm0 (ms_fcsr ms)
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) OUT 8 m m'
           /\ rw_cells asegs m' OUT [C8 v]) c
         /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_live RT Σ' = rt_live RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
         /\ (rt_credit RT Σ - NUMA_CREDIT <= rt_credit RT Σ')%Z)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (A + off)) (Z_to_bv 64 OUT) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xe99dc) fc None m (seg_rom asegs)).
  Proof using AF RTF FDO MST HFF.
    intros until junk. intros ETP FRM FRL FNZ CRD ART0 MI ST LOR ROOM TOP SP16 HIN P8 PA PS PT TXT TMAX HOFF HSTOP HNC OUTC HOUT HOUT2 OUT8.
    set (E := mkNwEnv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 A off stop OUT lo p n txt b).
    pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
    pose proof (af_live_range RT AF Σ m p n ART0 HIN) as (P0 & PHI & _).
    assert (OK : nw_ok E).
    { unfold E. constructor; cbn [w_lo w_sp w_txt w_off w_stop w_b w_p w_A w_n w_OUT]; try assumption; try lia. }
    assert (FPOK : forall Σ0, fp_ok RT Σ0 lo (NW_W E)).
    { intros Σ0. unfold E. cbn [w_sp w_OUT]. unfold NUMA_STACK, RT_STACK in ROOM.
      constructor; [left; cbn [fst snd]; lia|]. constructor; [left; cbn [fst snd]; lia| constructor]. }
    pose proof (shzp_live RT AF Σ m lo (NW_W E) p n ART0 LOR (FPOK Σ) HIN P8) as SHPT.
    destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _). unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SHB in G1, G2.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    unfold NUMA_STACK, RT_STACK, USTACK_TOP in ROOM, TOP. unfold SEGTOP_A, STACK_WIN, USTACK_TOP in SP0R, LOR, PHI.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    apply (aevt_evt RT AF PMc MST).
    pose proof (munch_refl (NW_W E) m) as MU. pose proof (wmono_refl asegs m) as WM.
    set (mb := m) in MU at 1, WM at 1, SHPT.
    unfold E in MU; cbn [w_sp w_OUT] in MU.
    step.
    carve_frame 32%nat ST.
    apply (rw_cells_split_CB asegs m _ [] 32 junk0 [] [8;8;8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    do 3 step. do 14 zstep.
    clear G1 G2.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) => assert (INV : NWINV E mb m1) by
      (unfold NWINV, E; cbn [w_sp w_OUT w_A w_txt w_s0 w_s1 w_ra w_lo];
       split; [eexists; eassumption|]; split; [eexists; eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption) end.
    lazymatch goal with |- evt _ ?Q _ => assert (KEND : nw_end_k E mb Q) end.
    2: { eapply evt_eq; [| eapply (sfa_scan E OK mb SHPT _ KEND (Z.to_nat stop) off); [exact INV | exact FRM | unfold E; cbn [w_off w_stop]; lia | unfold E; cbn [w_off w_stop]; lia]].
         unfold NUMMASK, E; cbn [w_sp w_OUT w_A w_off w_gp w_tp w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11]; num_st_eq. }

    clear INV. clear dependent junk0. clear dependent j.
    unfold nw_end_k.
    intros e xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc mm INV FRMx He.
    unfold E in He; cbn [w_off w_stop] in He.
    destruct INV as ((jx & FRx) & (junkx & OUTx) & TXTx & MIx & MUx & WMx & STx).
    unfold E in FRx, OUTx, TXTx, MUx, STx |- *; cbn [w_sp w_OUT w_A w_txt w_s0 w_s1 w_ra w_lo w_off w_gp w_tp w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11] in FRx, OUTx, TXTx, MUx, STx |- *.
    assert (SL : (stop < Z.of_nat (length txt))%Z)
      by (assert (X : nth_error txt (Z.to_nat stop) <> None) by (rewrite HSTOP; discriminate); apply nth_error_Some in X; lia).
    zstep. apply evt_done.
    assert (ARTx : ART RT Σ mm) by (exact (art_of_munch RT AF Σ mb mm lo _ ART0 LOR (FPOK Σ) MUx WMx)).
    eapply (HFF Σ) with (A := A) (FIRST := (A + off)%Z) (LAST := (A + e)%Z) (lo := lo) (p := p) (n := n) (txt := txt);
      rewrite ?unsigned_lit by lia; unfold FFA_STACK, SPA_STACK, NDCA_STACK, P5A_STACK, LMA_STACK, RT_STACK, FFA_FRAMES, FFA_CREDIT, USTACK_TOP in *;
      [ exact ETP | exact FRMx | unfold NUMA_FRAMES in FRL; lia | exact FNZ | unfold NUMA_CREDIT in CRD; lia | exact ARTx | exact MIx | exact STx | unfold STACK_WIN; lia | lia | lia
      | Z.div_mod_to_equations; lia | exact HIN | exact P8 | lia | lia | lia | exact TXTx | lia | lia | lia | ].

    intros Σ' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' FRM' RA PR EF EL ES EC.
    rewrite ?unsigned_lit in RA, PR by lia.
    destruct RA as (ART' & MI' & WM' & ST').
    pose proof (agree_pres _ _ _ mm m' (fun x => aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp + -32) x) PR (fun x H => H)) as AG.
    rt_transport_with mm m' AG WM' ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; cbv beta; aclient_tac).
    assert (LOR' : (rt_sp0 RT Σ' - 8388608 <= lo)%Z) by (rewrite ES; exact LOR).
    assert (FPOK2 : fp_ok RT Σ' lo [((bv_unsigned sp + -32)%Z, bv_unsigned sp); (OUT, (OUT + 8)%Z)]).
    { constructor; [left; cbn [fst snd]; unfold USTACK_TOP; lia|]. constructor; [left; cbn [fst snd]; unfold USTACK_TOP; lia| constructor]. }
    pose proof (shzp_stack RT AF Σ' m' lo _ OUT 8 ART' LOR' FPOK2 ltac:(unfold STACK_WIN; lia) ltac:(unfold USTACK_TOP; lia) OUT8) as SHPO.
    change (8 * (8 / 8))%Z with 8%Z in SHPO.
    pose proof (munch_refl [((bv_unsigned sp + -32)%Z, bv_unsigned sp); (OUT, (OUT + 8)%Z)] m') as MU2. pose proof (wmono_refl asegs m') as WM2.
    set (mb2 := m') in MU2 at 1, WM2 at 1, SHPO.
    apply (aevt_evt RT AF PMc MST). num_ret_pc.
    zastep. zastep. zastep. zastep. if_false.
    do 4 zstep.
    match goal with |- context [bword ?f] => set (flag := f); clearbody flag end.
    assert (SPLIT : forall Σ0 (m1 : mem) a, ART RT Σ0 m1 -> rt_live RT Σ0 = rt_live RT Σ -> rt_frames RT Σ0 = rt_frames RT Σ -> rt_sp0 RT Σ0 = rt_sp0 RT Σ ->
              aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) a -> ~ (OUT <= a < OUT + 8)%Z ->
              outside [((bv_unsigned sp + -32)%Z, bv_unsigned sp); (OUT, (OUT + 8)%Z)] a).
    { intros Σ0 m1 a HA0 E1 E2 E3 Ha Hd. rewrite <- E1, <- E2 in Ha. pose proof (aclient_split_c RT AF Σ0 m1 _ a HA0 Ha) as SPL. rewrite E3 in SPL.
      unfold STACK_WIN in SPL. cbn [outside]. split; [lia|]. split; [exact Hd| exact I]. }
    destruct flag; unfold bword; zstep; zstep; nstep; do 5 zstep; release_frame FRx ST' (bv_unsigned sp);
      lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ ?m1 _) =>
        let fl := lazymatch R with context [Z_to_bv 64 9] => constr:(true) | _ => constr:(false) end in
        apply evt_done; apply (aevt_done RT PMc); intros c Hc; exists Σ';
        (split; [| split; [exact EF | split; [exact EL | split; [exact ES | unfold NUMA_CREDIT; lia]]]]);
        eapply AST_conseq; [exact Hc | | intros mo H; exact H];
        intros ms <-; exists m1; eexists; exists fl;
        (split; [unfold ret_st; do 16 eexists; cbv delta [mkR]; reflexivity|]);
        (split; [exact FRM|]);
        (split; [split; [exact (art_of_munch RT AF Σ' mb2 m1 lo _ ART' ltac:(unfold STACK_WIN; exact LOR') FPOK2 MU2 WM2)|];
                 split; [exact MI'|]; split; [exact (wmono_trans asegs _ _ _ WMx WM')| exact ST']|]);
        (split; [| exact OUTx]);
        eapply pres_ex_trans; [exact (pres_ex_of_munch _ _ _ _ _ _ _ _ MUx (fun a => SPLIT Σ m a ART0 eq_refl eq_refl eq_refl))|];
        eapply pres_ex_trans; [eapply pres_ex_of_pres; [exact PR| lia]|];
        exact (pres_ex_of_munch _ _ _ _ _ _ _ _ MU2 (fun a => SPLIT Σ' m' a ART' EL EF ES))
      end.
  Qed.
End TOP.

Theorem slowfa_ok : forall RT, art_facts RT -> rt_contracts_f RT ->
  (forall PMc, fdfs_only PMc -> mat_stable PMc -> ffa_stmt RT PMc) -> slowfa_cps RT.
Proof.
  intros RT AF RTF HFF. unfold slowfa_cps, numwa_cps.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A off stop OUT lo p n txt b junk
    FDO MST -> -> ETP FRM FRL FNZ CRD ART0 MI ST LOR ROOM TOP SP16 HIN P8 PA PS PT TXT TMAX HOFF HSTOP HNC OUTC HOUT HOUT2 OUT8.
  exact (slowfa_walk RT AF RTF PMc FDO MST (HFF PMc FDO MST) Σ ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m A off stop OUT lo p n txt b junk ETP FRM FRL FNZ CRD ART0 MI ST LOR ROOM TOP SP16 HIN P8 PA PS PT TXT TMAX HOFF HSTOP HNC OUTC HOUT HOUT2 OUT8).
Qed.

