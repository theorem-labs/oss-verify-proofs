(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate
     InflateInv InflateInvKit InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InflArmLib6 InflArmLib6b InflArmLib6d
     InflNeed6 InflA_Check2 InflA_Dict1.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Transparent ZSWAP32.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


Definition restore_c (c : icall) (r : iregs) : icall :=
  icset_avail_in (icset_next_in (icset_avail_out (icset_next_out c (ir_put r)) (ir_left r)) (ir_next r)) (ir_have r).

(* zlib 1.4 (smodel14-r1's DICT row): total_in += in - avail_in on the restored stream before Z_NEED_DICT *)
Definition dict_c (c : icall) (r : iregs) : icall :=
  icset_total_in (restore_c c r) (wrap64 (ic_total_in c + wrap32 (ir_in r - ir_have r))).

Lemma arm_DICT_run : forall iv flush s c r,
  is_havedict s = 0 ->
  arm_DICT iv flush (mkW s c r) = ARet Z_NEED_DICT (mkW (iset_bits (iset_hold s (ir_hold r)) (ir_bits r)) (dict_c c r) r).
Proof.
  intros iv flush s c r Hhd. unfold arm_DICT. mstep1 (@gs_eq inflate_state). rewrite Hhd. cbn [Z.eqb].
  unfold amodify, abind, areturn, RESTORE, gr, uc, dict_c, restore_c. cbn [w_s w_c w_r]. destruct c; reflexivity.
Qed.

Lemma arm_DICTID_run : forall iv flush s c r c1 r1,
  is_havedict s = 0 ->
  NEEDBITS 32 (mkW s c r) = ARun tt (mkW s c1 r1) ->
  arm_DICTID iv flush (mkW s c r)
  = ARet Z_NEED_DICT (mkW (iset_bits (iset_hold (iset_mode (iset_check s (ZSWAP32 (ir_hold r1))) DICT) 0) 0)
                          (dict_c (icset_adler c1 (ZSWAP32 (ir_hold r1))) (irset_bits (irset_hold r1 0) 0))
                          (irset_bits (irset_hold r1 0) 0)).
Proof.
  intros iv flush s c r c1 r1 Hhd HN. unfold arm_DICTID. rewrite abind_run, HN. mstep1 HOLD_eq.
  mstep1 set_adler_check_eq. mstep1 INITBITS_eq. mstep1 set_mode_eq.
  rewrite arm_DICT_run by (destruct s; exact Hhd). reflexivity.
Qed.


Definition dstops : list Z := [pc6_ret; pc6_leave; pc6_mem; 0x1f188; 0x1f8c0; 0x1a3d4; 0x27800; 0x1ed04] ++ arm6_pcs.
Definition ilR : cfg := CFG [] [] arm_rets dstops [].

Section DictBody.
  Variable v : icv.
  Hypothesis C : ictx v.

  Ltac open_dje HJ :=
    let X := fresh in pose proof HJ as X; unfold DJE, LVR in X;
    destruct X as (HF & (G9 & G18 & G1 & G22 & G23) & G12 & G26); open_fix HF.

  (* zlib 1.4: the need-dict exit writes total_in. A copy of Infl6B's LMEM_store_total_in (Infl6B is not imported
     here) and the exit's store tower in 1.4's order (0x1ec48: avail_out, hold, bits, next_in, avail_in, total_in,
     next_out). *)
  Lemma icset_total_in_facts_d : forall c m,
    ic_next_in (icset_total_in c m) = ic_next_in c /\ ic_avail_in (icset_total_in c m) = ic_avail_in c
    /\ ic_next_out (icset_total_in c m) = ic_next_out c /\ ic_avail_out (icset_total_in c m) = ic_avail_out c
    /\ ic_input (icset_total_in c m) = ic_input c /\ ic_outbuf (icset_total_in c m) = ic_outbuf c
    /\ ic_total_out (icset_total_in c m) = ic_total_out c /\ ic_adler (icset_total_in c m) = ic_adler c
    /\ ic_msg (icset_total_in c m) = ic_msg c /\ ic_data_type (icset_total_in c m) = ic_data_type c
    /\ ic_total_in (icset_total_in c m) = m.
  Proof. intros c m. destruct c. repeat split; reflexivity. Qed.

  Lemma LMEM_store_total_in_d : forall s c r M m,
    LMEM v (mkW s c r) M -> 0 <= ir_put r <= cv_NO v ->
    LMEM v (mkW s (icset_total_in c m) r) (wbytes M (zw (cv_ZP v + 16)) (Z_to_le_bytes 8 m)).
  Proof.
    intros s c r M m HM Hput.
    open_ictx C. open_lmem HM.
    pose proof (icset_total_in_facts_d c m) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
    constructor; cbn [w_s w_c w_r]; rewrite ?F1, ?F2, ?F3, ?F4, ?F5, ?F6.
    - intros x Hx. rewrite wbytes_inside; [exact (Mrod x Hx) | lia | cbn; lia |]. unfold offimg, IMG6_TOP in CoZ. unfold ROD6_LO, ROD6_HI in Hx. clear - Hx CoZ CZP. cbn. lia.
    - unfold is6_scalars in *. apply (fields_write_other s6_segs _ _ is6_layout _ is6_SIZE _ _ Msc is6_layout_within); [lia | unfold is6_SIZE; lia | lia | cbn; lia |].
      unfold sep in CZS. unfold is6_SIZE. clear - CZS CZP CS. cbn. lia.
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mlens); [cbn; lia | lia | lia | lia | cbn; lia | unfold sep in CZS; cbn; lia].
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mwork); [cbn; lia | lia | lia | lia | cbn; lia | unfold sep in CZS; cbn; lia].
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mcodes); [cbn; lia | lia | lia | lia | cbn; lia | unfold sep in CZS; cbn; lia].
    - intros Hwn. apply (cells_write_other _ _ _ _ _ _ _ _ _ (Mwin Hwn)); [cbn; lia | lia | lia | lia | cbn; lia |]. unfold sep in CZW. cbn. lia.
    - destruct (Z.eq_dec (cv_NI v) 0) as [E0|E0]; [rewrite E0; apply cells_nil|].
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Minp); [cbn; lia | lia | lia | lia | cbn; lia |]. unfold sep in CZI. cbn. lia.
    - destruct (Z.eq_dec (ir_put r) 0) as [E0|E0]; [rewrite E0; apply cells_nil|].
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Mout); [cbn; lia | lia | lia | lia | cbn; lia |]. unfold sep in CZO. cbn. lia.
    - unfold izs6 in *. rewrite F7, F8, F9, ?F10, F11.
      destruct Mzs as (Z0 & Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z96).
      repeat match goal with |- _ /\ _ => split end;
        try (eapply cell_write_other; [eassumption | lia | cbn; lia | lia | cbn; lia | cbn; lia]).
      apply cell_write_same; [lia | cbn; lia].
    - apply (iframe6_other v C); [exact Mfr | lia | cbn; lia | unfold iframe6_ok, INF_FRAME; unfold sep in CfZ; cbn; lia].
    - pose proof (ic_sp _ C) as Csp_o; unfold INF_FRAME, INF_SCRATCH, IMG6_TOP in Csp_o, Moutc |- *; apply (cell_write_other _ _ _ _ _ _ _ Moutc); [lia | cbn; lia | lia | cbn; lia | unfold sep in CfZ; cbn; lia].
    - apply mapped_wbytes. exact Mmap_f.
    - apply mapped_wbytes. exact Mmap_Z.
    - apply mapped_wbytes. exact Mmap_S.
    - apply mapped_wbytes. exact Mmap_P.
    - intros Hwn. apply mapped_wbytes. exact (Mmap_W Hwn).
  Qed.

  Lemma LMEM_dictexit14 : forall s c r M tin,
    LMEM v (mkW s c r) M -> 0 <= ir_put r <= cv_NO v ->
    LMEM v (mkW (iset_bits (iset_hold s (ir_hold r)) (ir_bits r)) (icset_total_in (restore_c c r) tin) r)
      (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M
         (zw (cv_ZP v + 32)) (Z_to_le_bytes 4 (ir_left r)))
         (zw (cv_S v + 96)) (Z_to_le_bytes 8 (ir_hold r)))
         (zw (cv_S v + 104)) (Z_to_le_bytes 4 (ir_bits r)))
         (zw (cv_ZP v + 0)) (Z_to_le_bytes 8 (cv_I0 v + ir_next r)))
         (zw (cv_ZP v + 8)) (Z_to_le_bytes 4 (ir_have r)))
         (zw (cv_ZP v + 16)) (Z_to_le_bytes 8 tin))
         (zw (cv_ZP v + 24)) (Z_to_le_bytes 8 (cv_P0 v + ir_put r))).
  Proof.
    intros s c r M tin HM Hput. pose proof (ic_S _ C) as CS.
    pose proof (LMEM_store_avail_out v C s c r M (ir_left r) HM Hput) as H1.
    assert (H2 : LMEM v (mkW (iset_hold s (ir_hold r)) (icset_avail_out c (ir_left r)) r)
                   (wbytes (wbytes M (zw (cv_ZP v + 32)) (Z_to_le_bytes 4 (ir_left r))) (zw (cv_S v + 96)) (Z_to_le_bytes 8 (ir_hold r)))).
    { eapply (LMEM_store_scalar v C s _ r _ _ 96 _ H1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_hold _ (cv_S v) _ s (ir_hold r) (lm_sc _ _ _ H1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (H3 : LMEM v (mkW (iset_bits (iset_hold s (ir_hold r)) (ir_bits r)) (icset_avail_out c (ir_left r)) r)
                   (wbytes (wbytes (wbytes M (zw (cv_ZP v + 32)) (Z_to_le_bytes 4 (ir_left r))) (zw (cv_S v + 96)) (Z_to_le_bytes 8 (ir_hold r)))
                      (zw (cv_S v + 104)) (Z_to_le_bytes 4 (ir_bits r)))).
    { eapply (LMEM_store_scalar v C _ _ r _ _ 104 _ H2); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_bits _ (cv_S v) _ _ (ir_bits r) (lm_sc _ _ _ H2)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    pose proof (LMEM_store_next_in v C _ _ r _ (ir_next r) H3 Hput) as H4.
    pose proof (LMEM_store_avail_in v C _ _ r _ (ir_have r) H4 Hput) as H5.
    pose proof (LMEM_store_total_in_d _ _ r _ tin H5 Hput) as H6.
    pose proof (LMEM_store_next_out v C _ _ r _ (ir_put r) H6 Hput) as H7.
    match type of H7 with LMEM _ (mkW _ ?c7 _) _ =>
      replace (icset_total_in (restore_c c r) tin) with c7 by (unfold restore_c; destruct c; reflexivity) end.
    exact H7.
  Qed.

  Definition DREG (r : iregs) (R : bvmap 5 word) : Prop :=
    getr R 2 = zw (cv_sp v - 224) /\ getr R 8 = zw (cv_S v) /\ getr R 10 = zw (cv_ZP v)
    /\ getr R 18 = zw (ir_have r) /\ getr R 19 = zw (cv_P0 v + ir_put r) /\ getr R 1 = zw (ir_left r)
    /\ getr R 23 = zw (ir_hold r) /\ getr R 24 = zw (ir_bits r) /\ getr R 27 = zw (cv_I0 v + ir_next r)
    /\ getr R 3 = getr (cv_R0 v) 3 /\ getr R 4 = getr (cv_R0 v) 4.
  Definition dpins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (10, EVar 34%nat); (18, EVar 36%nat); (19, EAdd (EVar 37%nat) (EVar 38%nat)); (1, EVar 39%nat);
     (23, EVar 40%nat); (24, EVar 41%nat); (27, EAdd (EVar 43%nat) (EVar 44%nat))].

  Lemma dict_core : forall s c r R M,
    is_havedict s = 0 -> live_mode (is_mode s) -> is_mode s <> HEAD -> is_mode s <> BAD ->
    LMEM v (mkW s c r) M -> LX v (mkW s c r) -> DREG r R ->
    RINV (cv_NI v) (cv_NO v) r -> 0 <= ic_total_in c < 2 ^ 64 ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1d3d0) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ arm_post v (mkW s c r) M (ARet Z_NEED_DICT (mkW (iset_bits (iset_hold s (ir_hold r)) (ir_bits r)) (dict_c c r) r)) R' M' pc'.
  Proof.
    intros s c r R M Hhd Hlive NH NB HM HX HD RI Hti.
    destruct HD as (P2 & P25 & P10 & P9 & P18 & P1 & P22 & P23 & P26 & P3 & P4).
    open_ictx C. open_lmem HM. open_lx HX. open_rinv RI. open_frame Mfr.
    pose proof Mzs as Mzs'. unfold izs6 in Mzs'. destruct Mzs' as (Z0 & Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z96).
    unfold mapped in *.
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    pose proof (is6_havedict _ _ _ _ Msc) as C20. rewrite Hhd in C20.
    (* 1.4: lw / bnez / j, then the need-dict block at 0x1ec48 (13 instructions, with total_in) and j *)
    arm_symexP (@nil (Z * expr)) ilR 24%nat [false] [RVal (ELit 0); RVal (EVar 45%nat); RVal (EVar 46%nat)] dpins
      [(45%nat, 2 ^ 64); (46%nat, 2 ^ 64)] v r [ic_total_in c; cv_NI v] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1d3d0) M s6_rom) R' HR' Hfr Hms.
    all: try arm_side.
    (* the machine's total_in word is t + (NI - have) mod 2^32, stored as 8 bytes: the model's wrap64 value *)
    replace (Z_to_le_bytes 8 (ic_total_in c + (cv_NI v - ir_have r) mod 2 ^ 32))
      with (Z_to_le_bytes 8 (wrap64 (ic_total_in c + wrap32 (ir_in r - ir_have r)))) in Hms
      by (rewrite <- (SymExec.Z_to_le_bytes_mod 8 (ic_total_in c + (cv_NI v - ir_have r) mod 2 ^ 32)),
                  <- (SymExec.Z_to_le_bytes_mod 8 (wrap64 _));
          f_equal; rewrite wrap64_mod, wrap32_mod, Xin; change (8 * Z.of_nat 8) with 64; rewrite Z.mod_mod by lia; reflexivity).
    pose proof (LMEM_dictexit14 s c r M (wrap64 (ic_total_in c + wrap32 (ir_in r - ir_have r))) HM Hput) as HM4.
    fold (dict_c c r) in HM4. rewrite (Z.add_0_r (cv_ZP v)) in HM4.
    match type of HM4 with LMEM _ _ ?Mx => set (M4 := Mx) in * end.
    exists R', M4, pc6_ret. split; [subst M4; by_run Hms|].
    cbn [arm_post]. split; [reflexivity|]. split.
    - split; [exact HM4|]. split.
      { apply (LX_step0 v s c r _ _ r HX NH NB); unfold dict_c, restore_c; try reflexivity; try (destruct s; reflexivity); [destruct s; exact Hlive | exact Xret | destruct c; cbn in *; exact Xmsg]. }
      split; [split; [destruct s; reflexivity | split; destruct s; reflexivity]|].
      split; [| unfold Z_NEED_DICT, Z_OK; lia].
      symex_reg HR' (21%bv : reg) as G20'. unfold LREG_ret, INF_FRAME. regs_via Hfr; exact G20'.
    - subst M4.
      (* 1.4 tower, outermost first: next_out, total_in, avail_in, next_in (strm); bits, hold (state); avail_out (strm) *)
      do 4 (apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia]).
      do 2 (apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]).
      apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia].
      apply MFRAME_refl.
  Qed.

  Lemma dictid_B_sim : forall s c r1 R M,
    is_mode s = DICTID -> is_havedict s = 0 ->
    LMEM v (mkW s c r1) M -> RETC v (mkW s c r1) M -> LX v (mkW s c r1) -> DJE v c r1 R ->
    RINV (cv_NI v) (cv_NO v) r1 -> CINV (cv_NI v) (cv_NO v) c -> 32 <= ir_bits r1 ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1d380) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ arm_post v (mkW s c r1) M
           (ARet Z_NEED_DICT (mkW (iset_bits (iset_hold (iset_mode (iset_check s (ZSWAP32 (ir_hold r1))) DICT) 0) 0)
                                   (dict_c (icset_adler c (ZSWAP32 (ir_hold r1))) (irset_bits (irset_hold r1 0) 0))
                                   (irset_bits (irset_hold r1 0) 0))) R' M' pc'.
  Proof.
    intros s c r1 R M Hmode Hhd HM HRC HX HJ RI CI Hb32. open_dje HJ.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. open_rinv RI. open_cinv CI. unfold mapped in *.
    assert (Hput : 0 <= ir_put r1 <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    rewrite <- (zswap_exec (ir_hold r1)).
    set (V := (Z.lor (Z.lor (ir_hold r1 * 2 ^ 24) (Z.land (ir_hold r1) 65280 * 2 ^ 8)) (Z.lor (Z.land (ir_hold r1 / 2 ^ 8) 65280) (ir_hold r1 mod 2 ^ 32 / 2 ^ 24))) mod 2 ^ 32).
    assert (HV : 0 <= V < 2 ^ 32) by (subst V; apply Z.mod_pos_bound; lia).
    arm_symexP arm_pins ilR 40%nat (@nil bool) (@nil (option expr))
      [(12, EAdd (EVar 43%nat) (EVar 44%nat))] (@nil (nat * Z)) v r1 (@nil Z) NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1d380) M s6_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTD" G end.
    fold V in Hms1.
    set (M1 := wbytes M (zw (cv_S v + 8)) (Z_to_le_bytes 4 16190)) in *.
    set (M2 := wbytes M1 (zw (cv_S v + 40)) (Z_to_le_bytes 8 V)) in *.
    set (M3 := wbytes M2 (zw (cv_ZP v + 96)) (Z_to_le_bytes 8 V)) in *.
    set (sB := iset_check (iset_mode s DICT) V). set (cB := icset_adler c V). set (r2 := irset_bits (irset_hold r1 0) 0).
    assert (HM1 : LMEM v (mkW (iset_mode s DICT) c r1) M1).
    { apply (LMEM_store_scalar v C s c r1 _ M 8 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_mode M (cv_S v) _ s DICT Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HM2 : LMEM v (mkW sB c r1) M2).
    { apply (LMEM_store_scalar v C _ c r1 _ M1 40 _ HM1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_check M1 (cv_S v) _ _ V (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HM3 : LMEM v (mkW sB cB r2) M3).
    { apply (LMEM_regs v sB cB r1 cB r2); [exact (LMEM_store_adler v C sB c r1 M2 V HM2 Hput) | subst r2; reflexivity ..]. }
    pose proof (icset_adler_facts c V) as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8 & U9 & U10 & U11).
    assert (HX3 : LX v (mkW sB cB r2)).
    { apply (LX_step0 v s c r1 _ cB r2 HX NH NB); subst sB cB r2; try reflexivity; [live_mode_tac | exact Xret | rewrite U9; exact Xmsg]. }
    assert (HD3 : DREG r2 R1).
    { symex_reg HR1 (23%bv : reg) as Q23. symex_reg HR1 (24%bv : reg) as Q8. symex_reg HR1 (27%bv : reg) as Q26.
      unfold DREG. subst r2. cbn [ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next irset_bits irset_hold].
      regs_via Hfr1; first [exact Q23 | exact Q8 | exact Q26]. }
    assert (RI2 : RINV (cv_NI v) (cv_NO v) r2) by (subst r2; unfold RINV in *; cbn; clear - RI; change (2 ^ 0) with 1; lia).
    destruct (dict_core sB cB r2 R1 M3 ltac:(subst sB; destruct s; exact Hhd) ltac:(subst sB; live_mode_tac)
                ltac:(subst sB; destruct s; cbv; discriminate) ltac:(subst sB; destruct s; cbv; discriminate) HM3 HX3 HD3 RI2
                ltac:(subst cB; destruct c; cbn in *; exact Cti))
      as (R' & M' & pc' & Hms2 & HPOST).
    exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; subst M3 M2 M1; by_run Hms1|].
    replace (iset_bits (iset_hold (iset_mode (iset_check s V) DICT) 0) 0) with (iset_bits (iset_hold sB (ir_hold r2)) (ir_bits r2)) by (subst sB r2; destruct s; reflexivity).
    apply (arm_post_chain v (mkW s c r1) (mkW sB cB r2) M M3); [subst sB; split; [destruct s; reflexivity | split; destruct s; reflexivity] | | exact HPOST].
    cbn [w_r]. subst r2 M3 M2 M1. cbn [ir_put irset_bits irset_hold].
    apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia].
    do 2 (apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]).
    apply MFRAME_refl.
  Qed.
End DictBody.

Lemma arm_DICTID_leave : forall iv flush s c r w1,
  NEEDBITS 32 (mkW s c r) = ALeave w1 -> arm_DICTID iv flush (mkW s c r) = ALeave w1.
Proof. intros iv flush s c r w1 HN. unfold arm_DICTID. rewrite abind_run, HN. reflexivity. Qed.

Theorem arm_DICT_sim : arm_stmt DICT.
Proof.
  intros v w R M C Hmode HE HP. destruct w as [s c r]. cbn [w_s] in Hmode.
  rewrite dispatch_eq. cbn [w_s]. rewrite Hmode. change (arm_for ivar_ref (cv_flush v) DICT) with (arm_DICT ivar_ref (cv_flush v)).
  destruct HE as (HM & HRC & HX & (HF & HV & G8)).
  pose proof HX as HX'. open_lx HX'. pose proof HP as HP'. open_pinv HP'.
  rewrite (arm_DICT_run ivar_ref (cv_flush v) s c r Xhd).
  assert (HD : DREG v r R).
  { pose proof (pins_of_regs _ _ _ _ _ HF HV) as (P2 & P25 & P10 & P11 & P21 & P31 & P29 & P24 & P19 & P9 & P18 & P1 & P22 & P23 & P26).
    unfold LFIX in HF. destruct HF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G3 & G4).
    unfold DREG. repeat split; assumption. }
  exact (dict_core v C s c r R M Xhd Xlive ltac:(rewrite Hmode; cbv; discriminate) ltac:(rewrite Hmode; cbv; discriminate) HM HX HD RI
           ltac:(open_cinv CI; exact Cti)).
Qed.

Theorem arm_DICTID_sim : arm_stmt DICTID.
Proof.
  intros v w R M C Hmode HE HP. destruct w as [s c r]. cbn [w_s] in Hmode.
  rewrite dispatch_eq. cbn [w_s]. rewrite Hmode. change (arm_for ivar_ref (cv_flush v) DICTID) with (arm_DICTID ivar_ref (cv_flush v)).
  destruct HE as (HM & HRC & HX & (HF & HV & G8)).
  arm_begin C HM HRC HX HF HV HP.
  pose proof (dictid_need v C s c r R M HM HRC HF HV RI CI) as HN.
  destruct (NEEDBITS 32 (mkW s c r)) as [[] w1 | w1 | rc w1] eqn:EN; [| | destruct HN].
  - destruct HN as (r1 & R1 & -> & Hms1 & HJE & RI1 & S5 & Hb32).
    destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
    rewrite (arm_DICTID_run ivar_ref (cv_flush v) s c r c r1 Xhd EN).
    assert (HM1 : LMEM v (mkW s c r1) M) by (apply (LMEM_regs v s c r c r1 M HM); first [exact Q1 | exact Q4 | reflexivity]).
    assert (HRC1 : RETC v (mkW s c r1) M) by (eapply RETC_regs; [exact HRC | exact Q5]).
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (HX1 : LX v (mkW s c r1)).
    { apply (LX_step0 v s c r s c r1 HX NH NB); try reflexivity; [exact Xlive | exact Q3 | rewrite Q5; exact Xret | exact Xmsg]. }
    destruct (dictid_B_sim v C s c r1 R1 M Hmode Xhd HM1 HRC1 HX1 HJE RI1 CI Hb32) as (R' & M' & pc' & Hms2 & HPOST).
    exists R', M', pc'. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
    apply (arm_post_rebase v s c r c r1); [symmetry; exact Q1 | exact HPOST].
  - destruct HN as (r1 & R1 & -> & Hms1 & HL1 & RI1 & S5).
    destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
    rewrite (arm_DICTID_leave ivar_ref (cv_flush v) s c r _ EN).
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    exists R1, M, pc6_leave. split; [exact Hms1|].
    cbn [arm_post w_r]. split; [reflexivity|]. rewrite Q1. split; [| apply MFRAME_refl].
    split; [apply (LMEM_regs v s c r c r1 M HM); first [exact Q1 | exact Q4 | reflexivity]|].
    split; [| split; [apply same_blocks_refl | exact HL1]].
    apply (LX_step0 v s c r s c r1 HX NH NB); try reflexivity; [exact Xlive | exact Q3 | rewrite Q5; exact Xret | exact Xmsg].
Qed.
End FXG.
