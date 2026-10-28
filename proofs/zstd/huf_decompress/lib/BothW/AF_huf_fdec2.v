(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_tbl_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require RF_huf_tbl_kit RF_huf_fdw_kit RF_huf_fdw_sm RF_huf_fdw_pure RF_huf_fdw_st RF_huf_fdw_fm.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_bdt_model.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells Stdio_kit AHarness_iface AF_huf_tbl_iface AF_huf_bdt_kit
  AF_huf_tbl_iface2 AF_huf_fdw_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require AF_fse_rd_base.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_fse_rd_mem AF_huf_fdw_seg AF_huf_fdw_top1 AF_huf_ids AF_huf_bit AF_huf_sdec.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_reloadi.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require ABytes.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require AF_huf_fdec1.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw FseRdKit HufWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require FseWalkKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= bdtA_acc_hint.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.

Section FDEC.
  Variables (RNG : footprint) (Q : machine_state -> Prop) (m0 : amem) (SPV FF DST dcap S0 DT lo RLO RHI : Z) (bs : list Z)
            (d : dtable) (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (j48 jd : list byte).
  Notation SP1 := (SPAf SPV).
  Notation tl := (dt_tableLog d).
  Notation FRC := [C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 2147450880)].
  Hypothesis FC32 : rw_cells bsegs m0 (SP1 + 32) FRC.
  Hypothesis FO : rw_cells bsegs m0 (SP1 + 80) [CB 72 j48].
  Hypothesis STK : stk bsegs m0 lo SP1.
  Hypothesis BOT : ATOP + 4096 <= lo.
  Hypothesis LO : lo <= SP1 - DEC_STACK.
  Hypothesis SP16 : SPV mod 16 = 0.
  Hypothesis SPH : SPV + 16 <= 2^47.
  Hypothesis ZOBJ : zshadow m0 (SP1 + 80) 72.
  Hypothesis SHC : shclean m0 (SP1 + 112) (SP1 + 152) RLO RHI.
  Hypothesis RRH : rng RNG (shad RLO) (shad RHI - shad RLO).
  Hypothesis RO : rng RNG (SP1 + 80) 72.
  Hypothesis ROs : rng RNG (shad (SP1 + 80)) 9.
  Hypothesis RO32 : rng RNG (SP1 + 32) 32.
  Hypothesis HTL : 5 <= tl <= 12.
  Hypothesis HCELLS : zlen (dt_cells d) = 2^tl.
  Hypothesis HCOK : RF_huf_fdw_sm.cells_ok tl (dt_cells d).
  Hypothesis FM : dt_fastMode d = 1.
  Hypothesis DTH : rw_cells bsegs m0 DT [C2 (Z_to_bv 64 tl); C2 (Z_to_bv 64 1)].
  Hypothesis TBB : bytes_at bsegs m0 (DT + 4) (concat (map fse_cell_bytes (dt_cells d))).
  Hypothesis HDT : ablk DT (DT + 4 + 4 * 2^tl).
  Hypothesis DT4 : DT mod 4 = 0.
  Hypothesis ZDT : zshadow m0 DT (4 + 4 * 2^tl).
  Hypothesis RDT : rng RNG DT (4 + 4 * 2^tl).
  Hypothesis RDTs : rng RNG (shad DT) (nshad (4 + 4 * 2^tl + DT mod 8)).
  Hypothesis SRC : bytes_at bsegs m0 S0 (map (Z_to_bv 8) bs).
  Hypothesis BY : Forall (fun c => 0 <= c < 256) bs.
  Hypothesis NS : zlen bs <= 65536.
  Hypothesis HS0 : ablk S0 (S0 + zlen bs).
  Hypothesis S8 : S0 + 8 <= 2^47.
  Hypothesis S16 : 16 <= S0.
  Hypothesis USRC : unpoisoned m0 S0 (S0 + zlen bs).
  Hypothesis RS : rng RNG S0 (zlen bs).
  Hypothesis RSs : rng RNG (shad S0) (nshad (zlen bs + S0 mod 8)).
  Hypothesis RESOK : dres_ok (decompress_usingDTable bs d dcap true).
  Hypothesis OUTA : u8arr bsegs m0 DST jd.
  Hypothesis LJD : zlen jd = dcap.
  Hypothesis DC : 0 <= dcap <= 255.
  Hypothesis HDST : ablk DST (DST + dcap).
  Hypothesis DST3 : 3 <= DST.
  Hypothesis ZDST : zshadow m0 DST dcap.
  Hypothesis RDST : rng RNG DST dcap.
  Hypothesis RDSTs : rng RNG (shad DST) (nshad (dcap + DST mod 8)).
  Hypothesis DJ2 : DST + dcap <= S0 \/ S0 + zlen bs <= DST.
  Hypothesis DJ1 : DST + dcap <= DT \/ DT + 4 + 4 * 2^tl <= DST.
  Hypothesis DJ3 : S0 + zlen bs <= DT \/ DT + 4 + 4 * 2^tl <= S0.
  Hypothesis MI : mem_inv bsegs m0.
  Hypothesis RTC : artcells m0.
  Hypothesis ZMK : zshadow m0 ABIT_MASK 128.
  Hypothesis RSTK : rng RNG lo (SP1 - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.
  Notation W0 := [(lo, SP1); (SP1 + 80, SP1 + 152); (DST, DST + dcap)].
  Hypothesis K : forall m1 rv (j48' : list byte) (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
       munch W0 m0 m1 -> wmono bsegs m0 m1 ->
       mem_inv bsegs m1 -> stk bsegs m1 lo SP1 -> rw_cells bsegs m1 (SP1 + 80) [CB 72 j48'] -> rw_cells bsegs m1 (SP1 + 32) FRC ->
       dresA DST dcap (decompress_usingDTable bs d dcap true) m1 rv -> 0 <= rv < 2^64 ->
       evtF bsegs RNG Q
         (MS (mkR y1 (Z_to_bv 64 SP1) gp tp y5 y6 y7 (Z_to_bv 64 SPV) (Z_to_bv 64 SP1) (Z_to_bv 64 rv)
                  y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) y19
                  y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
             FR (Z_to_bv 64 0x98318) fc None m1 (seg_rom bsegs)).

  Notation SBI pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SP1) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SP1) x10
             x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880))
             (Z_to_bv 64 (DST + dcap - 3)) (Z_to_bv 64 DT) (Z_to_bv 64 (DST + dcap)) x22 x23 x24 x25
             (Z_to_bv 64 S0) (Z_to_bv 64 2147450880) x28 x29 x30 x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Ltac fbr b := lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    replace c with b; [cbv iota | symmetry; rewrite ?bv_ltu_Z, ?bv_eqb_Z, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
      first [apply Z.ltb_ge | apply Z.ltb_lt | apply Z.eqb_eq | apply Z.eqb_neq
            | apply Bool.negb_true_iff, Z.ltb_ge | apply Bool.negb_false_iff, Z.ltb_lt
            | apply Bool.negb_true_iff, Z.eqb_neq | apply Bool.negb_false_iff, Z.eqb_eq]; Z.div_mod_to_equations; lia] end.

  (* [comment removed for export] *)
  Lemma fdA_err : forall m3 e (j : list byte) (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
    munch [(SP1 - DEC_STACK, SP1); (SP1 + 80, SP1 + 152)] m0 m3 -> wmono bsegs m0 m3 -> mem_inv bsegs m3 -> stk bsegs m3 lo SP1 ->
    rw_cells bsegs m3 (SP1 + 80) [CB 72 j] -> decompress_usingDTable bs d dcap true = Err e -> 0 < e < 120 ->
    evtF bsegs RNG Q
      (MS (mkR y1 (Z_to_bv 64 SP1) gp tp y5 y6 y7 (Z_to_bv 64 SPV) (Z_to_bv 64 SP1) (Z_to_bv 64 (- e))
               y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) y19
               y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
          FR (Z_to_bv 64 0x98318) fc None m3 (seg_rom bsegs)).
  Proof.
    intros m3 e j y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 MU WM MI3 STK3 RW DE ER.
    pose proof (spaf_props SPV SP16) as (SPAB & SPA32). unfold DEC_STACK in LO, MU.
    replace (Z_to_bv 64 (- e)) with (Z_to_bv 64 (2^64 - e))
      by (apply Z_to_bv_eqm; replace (2^64 - e) with (- e + 1 * 2^64) by lia; rewrite Z.mod_add by lia; reflexivity).
    eapply (K m3 (2^64 - e) j).
    - eapply munch_weaken; [| exact MU]. intros x HX; cbn [outside] in *; lia.
    - exact WM.
    - exact MI3.
    - exact STK3.
    - exact RW.
    - eapply rw_cells_transport; [exact FC32 | exact MU | exact WM | cbn; lia].
    - unfold dresA. rewrite DE. lia.
    - lia.
  Qed.

  Definition fdA_KOK (x22 x23 x24 x25 : word) : Prop :=
    forall m1 db jp (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      init_dstream bs = Ok db -> bd_zero db = false ->
      munch [(SP1 - ABIT_INIT_STACK, SP1); (SP1 + 112, SP1 + 112 + 40)] m0 m1 -> wmono bsegs m0 m1 -> mem_inv bsegs m1 ->
      stk bsegs m1 lo SP1 -> bytes_at bsegs m1 S0 (map (Z_to_bv 8) bs) -> rw_cells bsegs m1 (SP1 + 112) (bitdz_cellsA S0 db jp) ->
      evtF bsegs RNG Q (SBI 0x984fc m1 (Z_to_bv 64 0x984f4) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x22 x23 x24 x25 t3 t4 t5 t6).

  (* [comment removed for export] *)
  Lemma fdA_bipost : forall (x22 x23 x24 x25 : word), fdA_KOK x22 x23 x24 x25 ->
    forall ms', bit_init_postA (Z_to_bv 64 0x984f4) (Z_to_bv 64 SP1) gp tp (Z_to_bv 64 SPV) (Z_to_bv 64 SP1)
                  (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 (DST + dcap - 3)) (Z_to_bv 64 DT) (Z_to_bv 64 (DST + dcap))
                  x22 x23 x24 x25 (Z_to_bv 64 S0) (Z_to_bv 64 2147450880) FR fc (SP1 + 112) S0 bs lo m0 ms' -> evtF bsegs RNG Q ms'.
  Proof.
    intros x22 x23 x24 x25 KOK ms'
      (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & ret & m1 & -> & MU & WM & MI1 & STK1 & SRC1 & CASE).
    unfold fdA_KOK in KOK.
    pose proof (spaf_props SPV SP16) as (SPAB & SPA32). pose proof atop_range as ATR. unfold DEC_STACK in LO.
    rewrite ?Z_to_bv_unsigned in MU, STK1. unfold bv_wrap, bv_modulus in MU, STK1. cbn [Z.of_N] in MU, STK1.
    rewrite ?(Z.mod_small (SPAf SPV)) in MU, STK1 by lia.
    sd_retlit.
    destruct (init_dstream bs) as [db| e | |] eqn:EI; try contradiction.
    - destruct CASE as (-> & BZ & jp & RW).
      zstep. zstep. fbr false.
      eapply KOK; [reflexivity | exact BZ | exact MU | exact WM | exact MI1 | exact STK1 | exact SRC1 | exact RW ].
    - destruct CASE as (-> & j' & RW).
      pose proof (RF_huf_fdw_pure.init_err bs e EI) as ER.
      zstep. zstep. fbr true.
      replace (Z_to_bv 64 (- e)) with (Z_to_bv 64 (2^64 - e))
        by (apply Z_to_bv_eqm; replace (2^64 - e) with (- e + 1 * 2^64) by lia; rewrite Z.mod_add by lia; reflexivity).
      eapply (K m1 (2^64 - e)).
      + eapply munch_weaken; [| exact MU]. intros x HX; cbn [outside] in *; unfold ABIT_INIT_STACK; lia.
      + exact WM.
      + exact MI1.
      + exact STK1.
      + pose proof (rw_cells_split_CB _ _ _ [] 72 j48 [] [32%nat; 40%nat] FO eq_refl) as FO2; cbn [app mk_CB_cells] in FO2.
        apply (proj1 (ABytes.rw_cells_app _ _ _ [CB 32 (firstn 32 j48)] _)) in FO2 as [FO3 _].
        pose proof (rw_cells_transport bsegs _ _ _ _ _ FO3 MU WM ltac:(cbn; unfold ABIT_INIT_STACK; lia)) as FO4.
        pose proof (rw_cells_cat _ _ _ _ _ _ FO4 RW ltac:(cbn; lia)) as FO5.
        pose proof (rw_cells_merge _ _ _ [] [CB 32 (firstn 32 j48); CB 40 j'] [] FO5) as FO6.
        cbn [app cells_size csize Nat.add] in FO6. exact FO6.
      + eapply rw_cells_transport; [exact FC32 | exact MU | exact WM | cbn; unfold ABIT_INIT_STACK; lia].
      + unfold dresA, decompress_usingDTable. rewrite EI. cbn. lia.
      + lia.
  Qed.

  Lemma fdA_rbok : forall d0 t v d', bitd_ok bs d0 -> 0 <= t <= 12 -> bd_bits d0 < 2^29 -> read_bits d0 t = Ok (v, d') ->
    bitd_ok bs d' /\ bd_bits d' = bd_bits d0 + t.
  Proof.
    intros d0 t v d' OK T B RB. pose proof OK as (Oc & Ob & Op & Op8 & Oz & Ozr).
    rewrite (RF_huf_fdw_pure.rb_facts d0 t v d' T ltac:(lia) RB). unfold bitd_ok. cbn [bd_cont bd_bits bd_ptr bd_zero].
    repeat split; try lia; first [exact Oz | (intros HZ; specialize (Ozr HZ); lia)].
  Qed.

  Ltac fappW := unfold appW; repeat (apply Forall_cons; [cbn [fst snd]; right; unfold KHIGH; lia |]); apply Forall_nil.
  Ltac fsub := let x := fresh "x" in let HX := fresh "HX" in intros x HX; cbn [outside] in *; lia.
  Ltac fnorm H := rewrite ?Z_to_bv_unsigned in H; unfold bv_wrap, bv_modulus, AFSE_INIT_STACK in H; cbn [Z.of_N] in H;
    rewrite ?(Z.mod_small (SPAf SPV)) in H by lia.
  Ltac fids_cl FX MW WM BDH RB RL OKd SRCm STKm MIm :=
    rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus, AFSE_INIT_STACK; cbn [Z.of_N];
    rewrite ?(Z.mod_small (SPAf SPV)) by lia;
    first [ reflexivity | exact BDH | exact RB | exact RL | exact OKd | exact SRCm | exact STKm | exact MIm
          | exact BY | exact HS0 | exact S8 | exact DT4 | exact RS | exact RSs | exact RI | exact RISH
          | lia
          | (eapply rw_cells_transport; [exact FX | exact MW | exact WM | cbn; lia])
          | (eapply rw_cells_transport; [exact DTH | exact MW | exact WM | cbn; lia])
          | (eapply ablk_sub; [exact HDT | lia | lia])
          | (eapply artcells_munchD; [exact RTC | exact MW | exact WM | cbn [aboveD]; repeat split; lia])
          | (eapply zshadow_appW; [eapply zshadow_sub; [exact ZOBJ | lia | lia] | exact MW | fappW | lia | lia])
          | (eapply zshadow_appW; [eapply zshadow_sub; [exact ZDT | lia | lia] | exact MW | fappW | lia | lia])
          | (eapply zshadow_appW; [exact ZMK | exact MW | fappW | unfold ABIT_MASK; lia | unfold ABIT_MASK; lia])
          | (eapply unpoisoned_appW; [exact USRC | exact MW | fappW | lia | lia])
          | (eapply rng_sub; [exact RO | lia | lia])
          | (eapply rng_sub; [exact RDT | lia | lia])
          | (eapply rng_sub; [exact RSTK | lia | lia])
          | (eapply rng_sub; [exact ROs | |]; rewrite !shad_div; Z.div_mod_to_equations; lia)
          | (eapply rng_sub; [exact RDTs | lia | unfold nshad; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8;
                                                 Z.div_mod_to_equations; lia])
          | idtac ].

  Definition fdA_K956 (x22 x23 x24 x25 : word) : Prop :=
    forall m3 db v1 d1 s1 d2 v2 d3 s2 d4 jp (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      init_dstream bs = Ok db -> read_bits db tl = Ok (v1, d1) -> reload_dstream bs d1 = Ok (s1, d2) ->
      read_bits d2 tl = Ok (v2, d3) -> reload_dstream bs d3 = Ok (s2, d4) -> bitd_ok bs d4 ->
      munch [(SP1 - DEC_STACK, SP1); (SP1 + 80, SP1 + 152)] m0 m3 -> wmono bsegs m0 m3 -> mem_inv bsegs m3 ->
      stk bsegs m3 lo SP1 -> bytes_at bsegs m3 S0 (map (Z_to_bv 8) bs) ->
      rw_cells bsegs m3 (SP1 + 80) [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 (DT + 4)); C8 (Z_to_bv 64 v1); C8 (Z_to_bv 64 (DT + 4))] ->
      rw_cells bsegs m3 (SP1 + 112) (bitdz_cellsA S0 d4 jp) ->
      evtF bsegs RNG Q (SBI 0x9851c m3 (Z_to_bv 64 0x9851c) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x22 x23 x24 x25 t3 t4 t5 t6).

  (* [comment removed for export] *)
  Lemma fdA_ids2 : forall (x22 x23 x24 x25 : word), fdA_K956 x22 x23 x24 x25 -> fdA_KOK x22 x23 x24 x25.
  Proof.
    intros x22 x23 x24 x25 K2 m1 db jp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 EI BZ MU1 WM1 MI1 STK1 SRC1 RW1.
    pose proof (spaf_props SPV SP16) as (SPAB & SPA32). pose proof atop_range as ATR. unfold DEC_STACK in LO.
    unfold ABIT_INIT_STACK in MU1.
    assert (TP : 0 < 2^tl) by (apply Z.pow_pos_nonneg; lia).
    pose proof (ablk_lin _ _ HDT) as HDTl. pose proof (ablk_lin _ _ HS0) as HS0l.
    pose proof (RF_huf_fdw_pure.init_facts bs db BY EI) as (OK0 & B0 & _).
    assert (NZ : 1 <= zlen bs).
    { destruct (length bs) eqn:LB0; [| lia]. apply length_zero_iff_nil in LB0. rewrite LB0 in EI. compute in EI. discriminate. }
    pose proof RESOK as RES. unfold dres_ok, decompress_usingDTable in RES. rewrite EI in RES. cbn [bind] in RES.
    destruct (read_bits_okD db tl ltac:(lia)) as (v1 & d1 & RB1). rewrite RB1 in RES. cbn [bind] in RES.
    destruct (reload_dstream bs d1) as [[s1 d2]| e | |] eqn:RL1; cbn [bind] in RES;
      [| destruct (RF_huf_fdw_st.reload_not_err _ _ _ RL1) | contradiction | contradiction].
    pose proof (fdA_rbok db tl v1 d1 OK0 ltac:(lia) ltac:(lia) RB1) as (OK1 & BB1).
    pose proof (RF_huf_fdw_pure.reload_facts2 bs d1 s1 d2 BY OK1 RL1) as (OK2 & BB2 & _).
    destruct (read_bits_okD d2 tl ltac:(lia)) as (v2 & d3 & RB2). rewrite RB2 in RES. cbn [bind] in RES.
    destruct (reload_dstream bs d3) as [[s2 d4]| e | |] eqn:RL2; cbn [bind] in RES;
      [| destruct (RF_huf_fdw_st.reload_not_err _ _ _ RL2) | contradiction | contradiction].
    pose proof (fdA_rbok d2 tl v2 d3 OK2 ltac:(lia) ltac:(pose proof OK2 as (_ & ? & _); lia) RB2) as (OK3 & BB3).
    pose proof (RF_huf_fdw_pure.reload_facts2 bs d3 s2 d4 BY OK3 RL2) as (OK4 & BB4 & _).
    pose proof (rw_cells_split_CB _ _ _ [] 72 j48 [] [16%nat; 16%nat; 40%nat] FO eq_refl) as FS. cbn [app mk_CB_cells] in FS.
    apply (proj1 (ABytes.rw_cells_app _ _ _ [_] _)) in FS as [FA FS].
    apply (proj1 (ABytes.rw_cells_app _ _ _ [_] _)) in FS as [FB _].
    cbn [cells_size csize Nat.add] in FB.
    replace (SP1 + 80 + Z.of_nat 16) with (SP1 + 96) in FB by lia.
    assert (MW1 : munch [(SP1 - 2240, SP1); (SP1 + 112, SP1 + 152)] m0 m1) by (eapply munch_weaken; [| exact MU1]; fsub).
    zstep. zstep. zstep. zstep.
    eapply evtF_cut.
    { eapply (fse_init_dstate_proofA RNG) with (DS := SP1 + 96) (BD := SP1 + 112) (DT := DT) (S := S0) (bs := bs) (d := db)
        (tl := tl) (v := v1) (d1 := d1) (st := s1) (d2 := d2) (lo := lo).
      all: fids_cl FB MW1 WM1 RW1 RB1 RL1 OK0 SRC1 STK1 MI1. }
    intros ms' (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & jp1 & m2 & -> & MU2 & WM2 & MI2 & STK2 & DS1 & BD1).
    fnorm MU2. fnorm STK2. sd_retlit.
    assert (MW2 : munch [(SP1 - 2240, SP1); (SP1 + 96, SP1 + 152)] m0 m2)
      by (eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU2]]; fsub).
    pose proof (wmono_trans bsegs _ _ _ WM1 WM2) as WM02.
    pose proof (bytes_at_transport bsegs _ _ _ _ _ SRC MW2 ltac:(cbn [disjoint_from]; rewrite length_map; lia)) as SRC2.
    zstep. zstep. zstep. zstep.
    eapply evtF_cut.
    { eapply (fse_init_dstate_proofA RNG) with (DS := SP1 + 80) (BD := SP1 + 112) (DT := DT) (S := S0) (bs := bs) (d := d2)
        (tl := tl) (v := v2) (d1 := d3) (st := s2) (d2 := d4) (lo := lo).
      all: fids_cl FA MW2 WM02 BD1 RB2 RL2 OK2 SRC2 STK2 MI2. }
    intros ms' (u0' & u1' & u2' & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3' & u4' & u5' & u6' & jp2 & m3 & -> & MU3 & WM3 & MI3 & STK3 & DS2 & BD2).
    fnorm MU3. fnorm STK3. sd_retlit.
    assert (MW3 : munch [(SP1 - 2240, SP1); (SP1 + 80, SP1 + 152)] m0 m3)
      by (eapply munch_trans; [eapply munch_weaken; [| exact MW2] | eapply munch_weaken; [| exact MU3]]; fsub).
    pose proof (wmono_trans bsegs _ _ _ WM02 WM3) as WM03.
    pose proof (bytes_at_transport bsegs _ _ _ _ _ SRC MW3 ltac:(cbn [disjoint_from]; rewrite length_map; lia)) as SRC3.
    pose proof (rw_cells_transport bsegs _ _ _ _ _ DS1 MU3 WM3 ltac:(cbn; lia)) as DS1'.
    pose proof (rw_cells_cat _ _ _ _ _ _ DS2 DS1' ltac:(cbn; lia)) as DSC. cbn [app] in DSC.
    eapply K2; [exact EI | exact RB1 | exact RL1 | exact RB2 | exact RL2 | exact OK4 | exact MW3 | exact WM03 | exact MI3
               | exact STK3 | exact SRC3 | exact DSC | exact BD2].
  Qed.

  Definition fdA_K972 (x22 x23 x24 x25 : word) : Prop :=
    forall m3 db v1 d1 s1 d2 v2 d3 s2 d4 jp (r1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      init_dstream bs = Ok db -> read_bits db tl = Ok (v1, d1) -> reload_dstream bs d1 = Ok (s1, d2) ->
      read_bits d2 tl = Ok (v2, d3) -> reload_dstream bs d3 = Ok (s2, d4) -> bitd_ok bs d4 -> bd_bits d4 <= 64 ->
      munch [(SP1 - DEC_STACK, SP1); (SP1 + 80, SP1 + 152)] m0 m3 -> wmono bsegs m0 m3 -> mem_inv bsegs m3 ->
      stk bsegs m3 lo SP1 -> bytes_at bsegs m3 S0 (map (Z_to_bv 8) bs) ->
      rw_cells bsegs m3 (SP1 + 80) [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 (DT + 4)); C8 (Z_to_bv 64 v1); C8 (Z_to_bv 64 (DT + 4))] ->
      rw_cells bsegs m3 (SP1 + 112) (bitdz_cellsA S0 d4 jp) ->
      evtF bsegs RNG Q (SBI 0x9852c m3 r1 t0 t1 t2 a0 (Z_to_bv 64 (bd_bits d4)) a2 a3 a4 a5 a6 a7 x22 x23 x24 x25 t3 t4 t5 t6).

  (* [comment removed for export] *)
  Lemma fdA_bits : forall (x22 x23 x24 x25 : word), fdA_K972 x22 x23 x24 x25 -> fdA_K956 x22 x23 x24 x25.
  Proof.
    intros x22 x23 x24 x25 K3 m3 db v1 d1 s1 d2 v2 d3 s2 d4 jp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
      EI RB1 RL1 RB2 RL2 OK4 MW3 WM3 MI3 STK3 SRC3 DSC BD2.
    pose proof (spaf_props SPV SP16) as (SPAB & SPA32). pose proof atop_range as ATR. unfold DEC_STACK in LO, MW3.
    pose proof OK4 as (O4c & O4b & _). unfold bitdz_cellsA in BD2.
    zstep. zstep. rewrite FseRdKit2.sx32_small by lia. zstep.
    destruct (Z.leb_spec (bd_bits d4) 64) as [B64|B64].
    - fbr true. eapply K3; eassumption.
    - fbr false. zstep. zstep. zstep.
      pose proof (rw_cells_cat _ _ _ _ _ _ DSC BD2 ltac:(cbn; lia)) as FO5.
      lazymatch type of FO5 with rw_cells _ _ _ ?l =>
        pose proof (rw_cells_merge _ _ _ [] l [] ltac:(rewrite app_nil_r; exact FO5)) as FO6 end.
      cbn [app cells_size csize Nat.add] in FO6.
      assert (RL3 : reload_dstream bs d4 = Ok (Overflow, mkBD (bd_cont d4) (bd_bits d4) (bd_ptr d4) true)).
      { unfold reload_dstream. replace (64 <? bd_bits d4) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
      apply (fdA_err m3 20 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MW3 WM3 MI3 STK3 FO6); [| lia].
      unfold decompress_usingDTable. rewrite EI. cbn [bind]. rewrite RB1. cbn [bind]. rewrite RL1. cbn [bind].
      rewrite RB2. cbn [bind]. rewrite RL2. cbn [bind]. rewrite RL3. cbn [bind]. reflexivity.
  Qed.

  Notation FDPRE db v1 d1 s1 d2 v2 d3 s2 d4 :=
    (init_dstream bs = Ok db /\ read_bits db tl = Ok (v1, d1) /\ reload_dstream bs d1 = Ok (s1, d2) /\
     read_bits d2 tl = Ok (v2, d3) /\ reload_dstream bs d3 = Ok (s2, d4)).
  Notation FDMEM m3 v1 v2 := (munch [(SP1 - DEC_STACK, SP1); (SP1 + 80, SP1 + 152)] m0 m3 /\ wmono bsegs m0 m3 /\ mem_inv bsegs m3 /\
     stk bsegs m3 lo SP1 /\ bytes_at bsegs m3 S0 (map (Z_to_bv 8) bs) /\
     rw_cells bsegs m3 (SP1 + 80) [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 (DT + 4)); C8 (Z_to_bv 64 v1); C8 (Z_to_bv 64 (DT + 4))]).

  Definition fdA_K1636 (x22 x23 x24 x25 : word) : Prop :=
    forall m3 db v1 d1 s1 d2 v2 d3 s2 d4 st d5 jp (r1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      FDPRE db v1 d1 s1 d2 v2 d3 s2 d4 -> reload_dstream bs d4 = Ok (st, d5) -> dstatus_eqb st Overflow = false ->
      bitd_ok bs d5 -> bd_bits d5 <= 64 -> bd_zero d5 = false -> FDMEM m3 v1 v2 ->
      rw_cells bsegs m3 (SP1 + 112) (bitdz_cellsA S0 d5 jp) ->
      evtF bsegs RNG Q (SBI 0x987c4 m3 r1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x22 x23 x24 x25 t3 t4 t5 t6).

  Definition fdA_K1628 (x22 x23 x24 x25 : word) : Prop :=
    forall m3 db v1 d1 s1 d2 v2 d3 s2 d4 jp (r1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      FDPRE db v1 d1 s1 d2 v2 d3 s2 d4 -> bitd_ok bs d4 -> bd_bits d4 <= 64 -> bd_zero d4 = false -> 8 <= bd_ptr d4 ->
      FDMEM m3 v1 v2 -> rw_cells bsegs m3 (SP1 + 112) (bitdz_cellsA S0 d4 jp) ->
      evtF bsegs RNG Q (SBI 0x987bc m3 r1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x22 x23 x24 x25 t3 t4 t5 t6).

  Definition fdA_K992 (x22 x23 x24 x25 : word) : Prop :=
    forall m3 db v1 d1 s1 d2 v2 d3 s2 d4 jp (r1 t0 t1 t2 a3 a5 a6 a7 t3 t4 t5 t6 : word),
      FDPRE db v1 d1 s1 d2 v2 d3 s2 d4 -> bitd_ok bs d4 -> bd_bits d4 <= 64 -> bd_zero d4 = false -> 0 < bd_ptr d4 < 8 ->
      FDMEM m3 v1 v2 -> rw_cells bsegs m3 (SP1 + 112) (bitdz_cellsA S0 d4 jp) ->
      evtF bsegs RNG Q (SBI 0x98540 m3 r1 t0 t1 t2 (Z_to_bv 64 (S0 + 8)) (Z_to_bv 64 (bd_bits d4)) (Z_to_bv 64 (S0 + bd_ptr d4))
                         a3 (Z_to_bv 64 S0) a5 a6 a7 x22 x23 x24 x25 t3 t4 t5 t6).

  (* [comment removed for export] *)
  Lemma fdA_split : forall (x22 x23 x24 x25 : word),
    fdA_K1628 x22 x23 x24 x25 -> fdA_K992 x22 x23 x24 x25 -> fdA_K1636 x22 x23 x24 x25 -> fdA_K972 x22 x23 x24 x25.
  Proof.
    intros x22 x23 x24 x25 KR KP KE m3 db v1 d1 s1 d2 v2 d3 s2 d4 jp r1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
      EI RB1 RL1 RB2 RL2 OK4 B4 MW3 WM3 MI3 STK3 SRC3 DSC BD2.
    pose proof (spaf_props SPV SP16) as (SPAB & SPA32). pose proof atop_range as ATR. unfold DEC_STACK in LO.
    pose proof (ablk_lin _ _ HS0) as HS0l.
    pose proof (RF_huf_fdw_pure.init_facts bs db BY EI) as (OK0 & B0 & _).
    pose proof (fdA_rbok db tl v1 d1 OK0 ltac:(lia) ltac:(lia) RB1) as (OK1 & BB1).
    pose proof (RF_huf_fdw_pure.reload_facts2 bs d1 s1 d2 BY OK1 RL1) as (OK2 & BB2 & _).
    pose proof (fdA_rbok d2 tl v2 d3 OK2 ltac:(lia) ltac:(lia) RB2) as (OK3 & BB3).
    pose proof (RF_huf_fdw_pure.reload_facts2 bs d3 s2 d4 BY OK3 RL2) as (_ & BB4 & _ & Z4 & O4).
    assert (B3 : bd_bits d3 <= 64).
    { destruct (Z.leb_spec (bd_bits d3) 64) as [|G]; [lia|]. destruct (O4 G) as [_ ->]. cbn [bd_bits] in B4. lia. }
    destruct (Z4 B3) as [BZ4 _].
    pose proof OK4 as (O4c & O4b & O4p & O4p8 & O4z & _).
    pose proof (conj EI (conj RB1 (conj RL1 (conj RB2 RL2)))) as FP.
    pose proof (conj MW3 (conj WM3 (conj MI3 (conj STK3 (conj SRC3 DSC))))) as FM3.
    pose proof BD2 as BD2f. unfold bitdz_cellsA in BD2. rewrite BZ4 in BD2. cbv iota in BD2.
    zstep. zstep. zstep.
    destruct (Z.leb_spec 8 (bd_ptr d4)) as [P8|P8].
    - fbr true. eapply KR; [exact FP | exact OK4 | exact B4 | exact BZ4 | exact P8 | exact FM3 | exact BD2f].
    - fbr false. zstep. zstep.
      destruct (Z.eqb_spec (bd_ptr d4) 0) as [P0|P0].
      + fbr true.
        assert (RL3 : reload_dstream bs d4 = Ok ((if bd_bits d4 <? 64 then EndOfBuffer else Completed), d4)).
        { unfold reload_dstream. replace (64 <? bd_bits d4) with false by (symmetry; apply Z.ltb_ge; lia).
          replace (8 <=? bd_ptr d4) with false by (symmetry; apply Z.leb_gt; lia). rewrite P0. reflexivity. }
        eapply KE; [exact FP | exact RL3 | destruct (bd_bits d4 <? 64); reflexivity | exact OK4 | exact B4 | exact BZ4
                   | exact FM3 | exact BD2f].
      + fbr false. eapply KP; [exact FP | exact OK4 | exact B4 | exact BZ4 | lia | exact FM3 | exact BD2f].
  Qed.

  (* [comment removed for export] *)
  Lemma fdA_reload : forall (x22 x23 x24 x25 : word), fdA_K1636 x22 x23 x24 x25 -> fdA_K1628 x22 x23 x24 x25.
  Proof.
    intros x22 x23 x24 x25 KE m3 db v1 d1 s1 d2 v2 d3 s2 d4 jp r1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
      FP OK4 B4 BZ4 P8 FM3 BD2.
    pose proof (spaf_props SPV SP16) as (SPAB & SPA32). pose proof atop_range as ATR. unfold DEC_STACK in LO.
    pose proof (ablk_lin _ _ HS0) as HS0l.
    pose proof FM3 as (MW3 & WM3 & MI3 & STK3 & SRC3 & DSC). unfold DEC_STACK in MW3.
    pose proof OK4 as (O4c & O4b & O4p & O4p8 & O4z & _).
    assert (Q8 : bd_ptr d4 + 8 <= zlen bs) by lia.
    pose proof BD2 as BD3. unfold bitdz_cellsA in BD3. rewrite BZ4 in BD3. cbv iota in BD3.
    replace (S0 + bd_ptr d4) with (S0 + (bd_ptr d4)) in BD3 by lia.
    assert (UBD : unpoisoned m3 (SP1 + 112) (SP1 + 112 + 40)).
    { eapply unpoisoned_appW; [| exact MW3 | fappW | lia | lia].
      replace (SP1 + 112 + 40) with (SP1 + 152) by lia. exact (shclean_unpoisoned _ _ _ _ _ SHC). }
    zstep. zstep.
    eapply evtF_cut.
    { eapply (fse_reload_int_proofA RNG) with (BD := SP1 + 112) (S := S0) (bc := bd_bits d4) (q := bd_ptr d4) (bs := bs) (lo := lo).
      all: rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus, RELOADI_STACK; cbn [Z.of_N];
           rewrite ?(Z.mod_small (SPAf SPV)) by lia;
           first [ reflexivity | exact BD3 | exact SRC3 | exact BY | exact HS0 | exact MI3 | exact STK3 | exact UBD
                 | exact RS | exact RSs | exact RI | exact RISH | lia
                 | (eapply artcells_munchD; [exact RTC | exact MW3 | exact WM3 | cbn [aboveD]; repeat split; lia])
                 | (eapply unpoisoned_appW; [exact USRC | exact MW3 | fappW | lia | lia])
                 | (eapply rng_sub; [exact RO | lia | lia])
                 | (eapply rng_sub; [exact RSTK | lia | lia])
                 | (eapply rng_sub; [exact ROs | |]; rewrite !shad_div; Z.div_mod_to_equations; lia)
                 | idtac ]. }
    intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & m4 & -> & MU4 & WM4 & MI4 & STK4 & RW4).
    unfold RELOADI_STACK in MU4. sd_retlit.
    set (d5 := mkBD (le64v bs (bd_ptr d4 - bd_bits d4 / 8)) (bd_bits d4 mod 8) (bd_ptr d4 - bd_bits d4 / 8) false).
    assert (RL3 : reload_dstream bs d4 = Ok (Unfinished, d5)).
    { unfold reload_dstream, d5. replace (64 <? bd_bits d4) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (8 <=? bd_ptr d4) with true by (symmetry; apply Z.leb_le; lia).
      rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      rewrite readLE64_ok by (Z.div_mod_to_equations; lia). cbn [bind].
      replace (Z.land (bd_bits d4) 7) with (bd_bits d4 mod 8) by (symmetry; apply (Z.land_ones (bd_bits d4) 3); lia).
      reflexivity. }
    pose proof (RF_huf_fdw_pure.reload_facts2 bs d4 Unfinished d5 BY OK4 RL3) as (OK5 & BB5 & _ & Z5 & _).
    destruct (Z5 B4) as [BZ5 OV5].
    assert (MW4 : munch [(SP1 - 2240, SP1); (SP1 + 80, SP1 + 152)] m0 m4)
      by (eapply munch_trans; [exact MW3 | eapply munch_weaken; [| exact MU4]; fsub]).
    eapply KE; [exact FP | exact RL3 | exact OV5 | exact OK5 | lia | exact BZ5 | | ].
    - split; [exact MW4|]. split; [exact (wmono_trans bsegs _ _ _ WM3 WM4)|]. split; [exact MI4|]. split; [exact STK4|].
      split.
      + eapply bytes_at_transport; [exact SRC3 | exact MU4 | cbn [disjoint_from]; rewrite length_map; lia].
      + eapply rw_cells_transport; [exact DSC | exact MU4 | exact WM4 | cbn; lia].
    - unfold bitdz_cellsA, d5. cbn [bd_cont bd_bits bd_ptr bd_zero]. unfold reload_cellsA in RW4. exact RW4.
  Qed.

  (* [comment removed for export] *)
  Lemma fdA_init : forall (x22 x23 x24 x25 : word), fdA_K992 x22 x23 x24 x25 -> fdA_K1636 x22 x23 x24 x25 ->
    forall (x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    evtF bsegs RNG Q (SBI 0x984e8 m0 x1 x5 x6 x7 x10 x11 (Z_to_bv 64 (zlen bs)) x13 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31).
  Proof.
    intros x22 x23 x24 x25 KP KE x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31.
    pose proof (spaf_props SPV SP16) as (SPAB & SPA32). unfold DEC_STACK in LO.
    zstep. zstep. zstep.
    eapply evtF_cut;
      [eapply bit_init_proofA
      | exact (fdA_bipost x22 x23 x24 x25 (fdA_ids2 _ _ _ _ (fdA_bits _ _ _ _ (fdA_split _ _ _ _ (fdA_reload _ _ _ _ KE) KP KE))))].
    all: rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus, ABIT_INIT_STACK; cbn [Z.of_N];
         rewrite ?(Z.mod_small (SPAf SPV)) by lia;
         first [ reflexivity | lia | exact SRC | exact BY | exact STK | exact MI | exact RTC | exact RI
               | (intros _; split; [exact HS0 | lia]) | (intros _; split; [exact RS | exact RSs])
               | exact RRH | exact USRC
               | (eapply rng_sub'; [exact RSTK| lia])
               | (replace (SPAf SPV + 112 + 40) with (SPAf SPV + 152) by lia; exact SHC)
               | (eapply rng_sub; [exact RO | lia | lia])
               | (eapply rng_sub; [exact ROs | |]; rewrite !shad_div; Z.div_mod_to_equations; lia)
               | (pose proof (rw_cells_split_CB _ _ _ [] 72 j48 [] [32%nat; 40%nat] FO eq_refl) as FO2; cbn [app mk_CB_cells] in FO2;
                  apply (proj1 (ABytes.rw_cells_app _ _ _ [CB 32 (firstn 32 j48)] _)) in FO2 as [_ FO3]; cbn [cells_size csize Nat.add] in FO3;
                  replace (SPAf SPV + 80 + Z.of_nat 32) with (SPAf SPV + 112) in FO3 by lia; exact FO3) ].
  Qed.

  (* [comment removed for export] *)
  Lemma fast_decA_K : forall (x22 x23 x24 x25 : word), fdA_K1636 x22 x23 x24 x25 ->
    forall (x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    evtF bsegs RNG Q (SBI 0x984e8 m0 x1 x5 x6 x7 x10 x11 (Z_to_bv 64 (zlen bs)) x13 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31).
  Proof.
    intros x22 x23 x24 x25 KE. apply (fdA_init x22 x23 x24 x25); [| exact KE].
    eapply AF_huf_fdec1.fdA_partial; first [exact KE | eassumption].
  Qed.

End FDEC.

End CANSEC1.
