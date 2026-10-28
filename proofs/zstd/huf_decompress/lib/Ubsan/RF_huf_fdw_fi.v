(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface RF_huf_tbl_iface RF_huf_tbl_kit RF_huf_bdt_model
  RF_huf_fdw_cut RF_huf_fdw_fil RF_huf_bitinit_f RF_huf_fdw_kit_reload.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section FI.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (x23 x24 x25 x26 x27 : word).          (* [comment removed for export] *)
  Variables (m0 : fmem) (S DT DST dcap lo : Z) (bs : list Z) (dt : dtable) (fmw : word) (jd j1 j2 jb : list byte).
  Variable POST : machine_state -> Prop.
  Notation SP := (bv_unsigned sp).
  Notation tl := (dt_tableLog dt).
  (* [comment removed for export] *)
  Hypothesis FR2 : rw_cells usegs m0 (SP + 16) [CB 16 j2].
  Hypothesis FR1 : rw_cells usegs m0 (SP + 32) [CB 16 j1].
  Hypothesis FRB : rw_cells usegs m0 (SP + 48) [CB 40 jb].
  (* [comment removed for export] *)
  Hypothesis DTH : rw_cells usegs m0 DT [C2 (Z_to_bv 64 tl); C2 fmw].
  Hypothesis TBB : bytes_at usegs m0 (DT + 4) (concat (map fse_cell_bytes (dt_cells dt))).
  Hypothesis HTL : 1 <= tl <= 12.
  Hypothesis HCELLS : zlen (dt_cells dt) = 2^tl.
  Hypothesis HCOK : cells_ok tl (dt_cells dt).
  (* [comment removed for export] *)
  Hypothesis SRC : bytes_at usegs m0 S (map (Z_to_bv 8) bs).
  Hypothesis BY : Forall (fun c => 0 <= c < 256) bs.
  Hypothesis OUTA : u8arr usegs m0 DST jd.
  Hypothesis LJD : zlen jd = dcap.
  Hypothesis STK : stk usegs m0 lo SP.
  Hypothesis MI : mem_inv usegs m0.
  (* [comment removed for export] *)
  Hypothesis LOSP : lo <= SP.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SP47 : SP + 192 <= 2^47.
  Hypothesis HS : 8 <= S /\ S + zlen bs <= lo.
  Hypothesis HDT : 0 < DT /\ DT mod 4 = 0 /\ DT + 4 + 4 * 2^tl <= lo.
  Hypothesis HDST : 4 <= DST /\ DST + dcap <= lo /\ 0 <= dcap <= 255.
  Hypothesis DJ1 : DST + dcap <= DT \/ DT + 4 + 4 * 2^tl <= DST.
  Hypothesis DJ2 : DST + dcap <= S \/ S + zlen bs <= DST.
  Hypothesis DJ3 : DT + 4 + 4 * 2^tl <= S \/ S + zlen bs <= DT.
  Hypothesis INITDS : fse_init_dstate_stmt.
  Hypothesis L3 : fdw_l3_stmt.
  Hypothesis T2 : fdw_t2_stmt.
  Hypothesis NB1 : Forall (fun c => 1 <= dc_nbBits c) (dt_cells dt).

  Notation WF := [(SP + 16, SP + 88); (DST, DST + dcap)].

  Ltac fi_st3 RD ST b := lazymatch type of RD with context [dstatus_eqb ?s ?C] =>
    let E := fresh "EQ" in assert (E : dstatus_eqb s C = b) by (first [reflexivity | destruct s; first [reflexivity | (cbn in ST; contradiction)]]);
    rewrite E in RD; cbv iota in RD end.

  Lemma fi_pre : forall m1 d3 s1 s2 r (jp : list byte) (w7 w12 w17 x1 x5 x6 x9 x10 x13 x14 x15 x16 x19 x21 x22 x28 x29 x30 x31 : word),
    w7 = Z_to_bv 64 (bd_bits d3) -> w12 = Z_to_bv 64 S -> w17 = Z_to_bv 64 (S + bd_ptr d3) ->
    (let! x := main_loop bs dt dcap true (Datatypes.S (Z.to_nat dcap)) (mkDec [] s1 s2 d3) in
     tail_loop bs dt dcap true (Datatypes.S (Z.to_nat dcap)) x) = r -> res_ok r ->
    bitd_ok bs d3 -> bd_bits d3 <= 64 -> bd_zero d3 = false -> 0 <= s1 < 2^tl -> 0 <= s2 < 2^tl ->
    rw_cells usegs m1 (SP + 16) [C8 (Z_to_bv 64 s2); C8 (Z_to_bv 64 (DT + 4))] ->
    rw_cells usegs m1 (SP + 32) [C8 (Z_to_bv 64 s1); C8 (Z_to_bv 64 (DT + 4))] ->
    rw_cells usegs m1 (SP + 48) (bitdz_cells S d3 jp) ->
    bytes_at usegs m1 (DT + 4) (concat (map fse_cell_bytes (dt_cells dt))) ->
    bytes_at usegs m1 S (map (Z_to_bv 8) bs) -> u8arr usegs m1 DST jd ->
    munch WF m0 m1 -> wmono usegs m0 m1 -> mem_inv usegs m1 -> stk usegs m1 lo SP ->
    fdw_K SP gp tp F fc m0 DST dcap lo POST r ->
    evt usegs POST (MS (mkR x1 sp gp tp x5 x6 w7 (Z_to_bv 64 DST) x9 x10 (Z_to_bv 64 (S + 8))
                            w12 x13 x14 x15 x16 w17 (Z_to_bv 64 (DST + dcap)) x19
                            (Z_to_bv 64 (DST + dcap - 3)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x2012c) fc None m1 (seg_rom usegs)).
  Proof using HTL HCELLS HCOK BY LJD LOSP SP16 SP47 HS HDT HDST DJ1 DJ2 DJ3 L3 T2 NB1.
    intros until x31. intros -> -> -> RD ROK BOK BB BZ S1R S2R C2 C1 CB TB SB OU MU WM MI1 STK1 K.
    unfold bitdz_cells in CB. rewrite BZ in CB.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof BOK as (BC & BBR & BP & BPE & BPS & BZI).
    assert (P2 : 2 <= 2^tl <= 4096)
      by (split; [change 2 with (2^1); apply Z.pow_le_mono_r; lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]).
    (fi_walk_until [0x2016c]).
    fi_setreg 15%Z (Z_to_bv 64 (2^61)) ltac:(f_equal; reflexivity).
    fi_setreg 16%Z (Z_to_bv 64 (2^16 - 1)) ltac:(f_equal; reflexivity).
    replace (0 <? DT + 4) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
    assert (PRE : fdw_pre SP S DT DST dcap lo bs dt) by (unfold fdw_pre; repeat split; first [exact HCOK | exact BY | lia]).
    destruct (main_loop bs dt dcap true (Datatypes.S (Z.to_nat dcap)) (mkDec [] s1 s2 d3)) as [x'|e| |] eqn:ML; cbn [bind] in RD;
      [ | exfalso; exact (fi_main_loop_not_err _ _ _ _ _ _ _ ML) | subst r; contradiction | subst r; contradiction ].
    pose proof (T2 SP gp tp F fc m0 S DT DST dcap lo bs dt POST _ x' r PRE RD ROK K) as KT.
    pose proof (L3 SP gp tp F fc m0 S DT DST dcap lo bs dt POST _ (mkDec [] s1 s2 d3) x' PRE NB1 ML KT) as KL.
    unfold fdw_l3_K in KL. rewrite Z_to_bv_bv_unsigned in KL. cbn [de_s1 de_s2 de_bd de_out length Z.of_nat] in KL.
    rewrite Z.add_0_r in KL.
    eapply KL.
    - unfold sm_ok. cbn [de_bd de_out length Z.of_nat]. split; [exact BOK|]. split; [lia|]. split; [lia | constructor].
    - unfold st_ok. cbn [de_s1 de_s2]. split; lia.
    - unfold fdw_mem, sm_inv. cbn [de_s1 de_s2 de_bd de_out].
      split; [exact C2|]. split; [exact C1|]. split; [unfold bitdz_cells; rewrite BZ; exact CB|].
      split; [split; [exists jd; cbn [map app length Z.of_nat]; split; [exact OU | lia] | split; [exact MU | split; [exact WM | exact MI1]]]|].
      split; [exact TB|]. split; [exact SB | exact STK1].
  Qed.

  Lemma fast_run : forall r (x1 x5 x6 x7 x13 x14 x15 x16 x17 x20 x21 x22 x28 x29 x30 x31 : word),
    decompress_usingDTable bs dt dcap true = r -> res_ok r ->
    fdw_K SP gp tp F fc m0 DST dcap lo POST r ->
    evt usegs POST (MS (mkR x1 sp gp tp x5 x6 x7 (Z_to_bv 64 DST) (Z_to_bv 64 DT) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 (zlen bs)) x13 x14
                            x15 x16 x17 (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 S) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x1f7d8) fc None m0 (seg_rom usegs)).
  Proof.
    intros until x31. intros RD ROK K. pose proof K as K0. unfold fdw_K in K. rewrite Z_to_bv_bv_unsigned in K.
    pose proof (munch_refl WF m0) as MU. pose proof (wmono_refl usegs m0) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (bytes_at_bound _ _ _ _ SRC) as BSB. rewrite length_map in BSB.
    assert (P2 : 2 <= 2^tl <= 4096)
      by (split; [change 2 with (2^1); apply Z.pow_le_mono_r; lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]).
    assert (LBS : Z.of_nat (length (map (Z_to_bv 8) bs)) = zlen bs) by (rewrite length_map; reflexivity).
    assert (LTB : Z.of_nat (length (concat (map fse_cell_bytes (dt_cells dt)))) = 4 * 2^tl) by (rewrite fse_cells_length; lia).
    (fi_walk_until [0x1f808]).
    zstep.
    eapply evt_cut.
    { eapply (bit_init_f_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (SP + 48) S bs jb lo).
      all: first [eassumption | lia | reflexivity]. }
    unfold bit_init_post. lazymatch goal with MIx : mem_inv usegs ?mm |- _ => post_call usegs mm end.
   
    match goal with H : context [init_dstream bs] |- _ => revert H end.
    destruct (init_dstream bs) as [d0|e| |] eqn:ID; intros PI; [ | | contradiction | contradiction].
    2:{ destruct PI as (ER & jbe & FBE). match type of ER with ?v = _ => subst v end. pose proof (fi_init_err bs e ID) as EB.
        (fi_walk_until [0x20450]).
        unfold decompress_usingDTable in RD. rewrite ID in RD. cbn [bind] in RD. subst r.
        eapply K; first [eassumption | (cbn [dres]; split; [reflexivity | exact EB])]. }
    destruct PI as (ER & BZ0 & jp0 & BD0). match type of ER with ?v = _ => subst v end.
    pose proof (fi_init_facts bs d0 BY ID) as (BOK0 & BB0 & _).
    rewrite <- (bitdz_bitd S d0 jp0 BZ0) in BD0.
    unfold decompress_usingDTable in RD. rewrite ID in RD. cbn [bind] in RD.
    rewrite (fi_read_bits_ok d0 tl ltac:(lia)) in RD. cbn [bind] in RD.
    destruct (reload_dstream bs (skip_bits d0 tl)) as [[st1 d1r]|e1| |] eqn:RL1; cbn [bind] in RD;
      [ | exfalso; exact (reload_not_err _ _ _ RL1) | subst r; contradiction | subst r; contradiction ].
    (fi_walk_until [0x1f820]).
    zstep.
    eapply evt_cut.
    { eapply (INITDS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (SP + 32) (SP + 48) DT S tl
                bs d0 j1 jp0 fmw _ _ _ _ lo).
      all: first [eassumption | lia | reflexivity | (apply fi_read_bits_ok; lia)]. }
    unfold fse_init_dstate_post. lazymatch goal with MIx : mem_inv usegs ?mm |- _ => post_call usegs mm end.
   
    pose proof (fi_skip_ok bs d0 tl BOK0 ltac:(lia) ltac:(lia)) as (BOKs0 & BBs0).
    pose proof (fi_reload_facts bs (skip_bits d0 tl) st1 d1r BY BOKs0 RL1) as (BOK1 & BB1 & _).
    rewrite (fi_read_bits_ok d1r tl ltac:(lia)) in RD. cbn [bind] in RD.
    destruct (reload_dstream bs (skip_bits d1r tl)) as [[st2 d2r]|e2| |] eqn:RL2; cbn [bind] in RD;
      [ | exfalso; exact (reload_not_err _ _ _ RL2) | subst r; contradiction | subst r; contradiction ].
    (fi_walk_until [0x1f830]).
    zstep.
    eapply evt_cut.
    { eapply (INITDS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (SP + 16) (SP + 48) DT S tl
                bs d1r j2 _ fmw _ _ _ _ lo).
      all: first [eassumption | lia | reflexivity | (apply fi_read_bits_ok; lia)]. }
    unfold fse_init_dstate_post. lazymatch goal with MIx : mem_inv usegs ?mm |- _ => post_call usegs mm end.
   
    pose proof (fi_skip_ok bs d1r tl BOK1 ltac:(lia) ltac:(lia)) as (BOKs1 & BBs1).
    pose proof (fi_reload_facts bs (skip_bits d1r tl) st2 d2r BY BOKs1 RL2) as (BOK2 & BB2 & _).
    destruct (reload_dstream bs d2r) as [[st3 d3]|e3| |] eqn:RL3; cbn [bind] in RD;
      [ | exfalso; exact (reload_not_err _ _ _ RL3) | subst r; contradiction | subst r; contradiction ].
    pose proof (fi_reload_facts bs d2r st3 d3 BY BOK2 RL3) as (BOK3 & BB3 & BZ3 & BOV3).
    pose proof BOK2 as (BC2 & BBR2 & BP2 & BPE2 & BPS2 & BZI2).
    destruct (Z_lt_le_dec 64 (bd_bits d2r)) as [OV|OV].
    { lazymatch goal with H : rw_cells usegs _ (SP + 48) (bitdz_cells S d2r _) |- _ => unfold bitdz_cells in H end.
      destruct (bd_zero d2r) eqn:BZ2.
      all: (fi_walk_until [0x20450; 0x2012c]).
      all: pose proof (proj1 (BOV3 OV)) as STOV; fi_st3 RD STOV true; subst r.
      all: eapply K; first [eassumption | (cbn [dres]; split; [reflexivity | vm_compute; split; reflexivity])]. }
    assert (BZ2 : bd_zero d2r = false) by (destruct (bd_zero d2r); [specialize (BZI2 eq_refl); lia | reflexivity]).
    lazymatch goal with H : rw_cells usegs _ (SP + 48) (bitdz_cells S d2r _) |- _ => unfold bitdz_cells in H; rewrite BZ2 in H end.
    destruct (Z_le_gt_dec 8 (bd_ptr d2r)) as [FP|FP].
    { pose proof BOK3 as (BCd3 & BBd3 & BPd3 & BPEd3 & BPSd3 & BZId3).
      (fi_walk_until [0x20450; 0x2012c]).
      eapply evt_cut.
      { eapply (fse_reload_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (SP + 48) S lo bs d2r _ st3 d3).
        all: first [eassumption | lia | reflexivity | (unfold bitdz_cells; rewrite BZ2; eassumption)]. }
      unfold fse_reload_post. lazymatch goal with MIx : mem_inv usegs ?mm |- _ => post_call usegs mm end.
     
      lazymatch goal with H : rw_cells usegs _ (SP + 48) (bitdz_cells S d3 _) |- _ => unfold bitdz_cells in H; rewrite (proj1 (BZ3 OV)) in H end.
      (fi_walk_until [0x20450; 0x2012c]).
      pose proof (proj2 (BZ3 OV)) as STOK. fi_st3 RD STOK false.
      eapply (fi_pre _ d3 _ _ r); first [eassumption | lia | apply fi_land_rng; lia | reflexivity | (apply sx32_small; lia) | (f_equal; lia) | (f_equal; fi_znG; lia) | exact (proj1 (BZ3 OV)) | (unfold bitdz_cells; rewrite (proj1 (BZ3 OV)); eassumption)]. }
    destruct (Z.eq_dec (bd_ptr d2r) 0) as [P0|P0].
    { (fi_walk_until [0x20450; 0x2012c]).
      pose proof (proj2 (BZ3 OV)) as STOK. fi_st3 RD STOK false.
      assert (D3E : d3 = d2r).
      { unfold reload_dstream in RL3. replace (64 <? bd_bits d2r) with false in RL3 by (symmetry; apply Z.ltb_ge; lia).
        replace (8 <=? bd_ptr d2r) with false in RL3 by (symmetry; apply Z.leb_gt; lia).
        replace (bd_ptr d2r =? 0) with true in RL3 by (symmetry; apply Z.eqb_eq; lia). injection RL3 as _ <-. reflexivity. }
      subst d3.
      eapply (fi_pre _ d2r _ _ r); first [eassumption | lia | apply fi_land_rng; lia | reflexivity | (apply sx32_small; lia) | (f_equal; lia) | (f_equal; fi_znG; lia) | (unfold bitdz_cells; rewrite BZ2; eassumption)]. }
    {
      assert (NB8 : 0 <= bd_bits d2r / 8 <= 8) by (apply fi_div8_le; lia).
      assert (L8 : 8 <= zlen bs) by (destruct (Z_lt_le_dec (zlen bs) 8) as [Hl|Hl]; [specialize (BPS2 Hl); lia | lia]).
      unfold reload_dstream in RL3.
      replace (64 <? bd_bits d2r) with false in RL3 by (symmetry; apply Z.ltb_ge; lia).
      replace (8 <=? bd_ptr d2r) with false in RL3 by (symmetry; apply Z.leb_gt; lia).
      replace (bd_ptr d2r =? 0) with false in RL3 by (symmetry; apply Z.eqb_neq; lia).
      rewrite Z.shiftr_div_pow2 in RL3 by lia. change (2^3) with 8 in RL3.
      destruct (Z_lt_le_dec (bd_ptr d2r - bd_bits d2r / 8) 0) as [EOB|UNF].
      - replace (bd_ptr d2r - bd_bits d2r / 8 <? 0) with true in RL3 by (symmetry; apply Z.ltb_lt; lia).
        cbv beta iota zeta in RL3. rewrite HufWalkKit.readLE64_ok in RL3 by lia. cbn [bind] in RL3. injection RL3 as ST3 D3. subst st3.
        (fi_walk_until [0x20450; 0x2012c; 0x1f8b4]).
        remember (bd_ptr d2r - bd_ptr d2r) as pp eqn:EPP.
        (fi_setreg 17%Z (Z_to_bv 64 (S + pp)) ltac:(f_equal; fi_znG; lia)).
        eapply fi_ld; [exact SRC | exact BY | lia | lia | intros z5 z13 z14 z15 z16].
        (fi_walk_until [0x20450; 0x2012c]).
        all: lazymatch goal with H : rw_cells usegs _ (SP + 48) (C8 (Z_to_bv 64 (le64v bs _)) :: _) |- _ =>
          fi_fixbd H (bd_cont d3) (bd_bits d3) (S + bd_ptr d3)
            ltac:(rewrite <- D3; cbn [bd_cont bd_bits bd_ptr]; first [reflexivity | fi_znG; lia]) end.
        all: pose proof (proj2 (BZ3 OV)) as STOK; fi_st3 RD STOK false.
        all: eapply (fi_pre _ d3 _ _ r); first [eassumption | lia | apply fi_land_rng; lia | reflexivity | (apply sx32_small; lia) | (f_equal; lia) | (f_equal; fi_znG; lia) | exact (proj1 (BZ3 OV)) | (rewrite <- D3; cbn [bd_cont bd_bits bd_ptr bd_zero]; first [reflexivity | f_equal; fi_znG; lia])
          | (unfold bitdz_cells; rewrite (proj1 (BZ3 OV)); eassumption)].
      - replace (bd_ptr d2r - bd_bits d2r / 8 <? 0) with false in RL3 by (symmetry; apply Z.ltb_ge; lia).
        cbv beta iota zeta in RL3. rewrite HufWalkKit.readLE64_ok in RL3 by lia. cbn [bind] in RL3. injection RL3 as ST3 D3. subst st3.
        (fi_walk_until [0x20450; 0x2012c; 0x1f8b4]).
        remember (bd_ptr d2r - bd_bits d2r / 8) as pp eqn:EPP.
        (fi_setreg 17%Z (Z_to_bv 64 (S + pp)) ltac:(f_equal; fi_znG; lia)).
        eapply fi_ld; [exact SRC | exact BY | lia | lia | intros z5 z13 z14 z15 z16].
        (fi_walk_until [0x20450; 0x2012c]).
        all: lazymatch goal with H : rw_cells usegs _ (SP + 48) (C8 (Z_to_bv 64 (le64v bs _)) :: _) |- _ =>
          fi_fixbd H (bd_cont d3) (bd_bits d3) (S + bd_ptr d3)
            ltac:(rewrite <- D3; cbn [bd_cont bd_bits bd_ptr]; first [reflexivity | fi_znG; lia]) end.
        all: pose proof (proj2 (BZ3 OV)) as STOK; fi_st3 RD STOK false.
        all: eapply (fi_pre _ d3 _ _ r); first [eassumption | lia | apply fi_land_rng; lia | reflexivity | (apply sx32_small; lia) | (f_equal; lia) | (f_equal; fi_znG; lia) | exact (proj1 (BZ3 OV)) | (rewrite <- D3; cbn [bd_cont bd_bits bd_ptr bd_zero]; first [reflexivity | f_equal; fi_znG; lia])
          | (unfold bitdz_cells; rewrite (proj1 (BZ3 OV)); eassumption)]. }
  Qed.
End FI.

Theorem fdw_f_entry_proof : fse_init_dstate_stmt -> fdw_l3_stmt -> fdw_t2_stmt -> fdw_f_entry_stmt.
Proof.
  intros INITDS L3 T2. unfold fdw_f_entry_stmt, fdw_entry_at.
  intros SP gp tp F fc m0 S DT DST dcap lo bs dt fmw jd j1 j2 jb POST r x1 x5 x6 x7 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24
    x25 x26 x27 x28 x29 x30 x31 PRE NBF DTH TBB SRC FR2 FR1 FRB OUTA LJD STK MI RD ROK K.
  pose proof PRE as (HTL & HCELLS & HCOK & BY & LOSP & SP16 & SP47 & HS1 & HS2 & HDT1 & HDT2 & HDT3 & HDST1 & HDST2 & HDST3
                     & DJ1 & DJ2 & DJ3).
  assert (ESP : bv_unsigned (Z_to_bv 64 SP) = SP) by (apply unsigned_lit; lia).
  pose proof (NBF eq_refl) as NB1.
  assert (EPC : PFDW_F = 0x1f7d8) by reflexivity. rewrite EPC.
  eapply fast_run; rewrite ?ESP; first [eassumption | lia].
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
