From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface RF_huf_tbl_iface RF_huf_tbl_kit RF_huf_fdw_kit
  RF_huf_fdw_cut RF_huf_fdw_ftl RF_huf_fdw_fil RF_huf_fdw_kit_dsym RF_huf_fdw_tk.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac ftb_fin K := unfold PFSE_DECOMP in K; cbn [Z.add bd_bits bd_ptr bd_cont bd_zero] in K;
  eapply K; unfold fdw_fmem; cbn [de_out de_s1 de_s2 de_bd];
  (split; [eexists; split; eassumption|]);
  (split; [do 2 eexists; eassumption|]);
  split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption.

Lemma ftb_dsym_o : forall dt fast s d o s' d', cells_ok (dt_tableLog dt) (dt_cells dt) ->
  decode_sym dt fast s d = Ok (o, s', d') -> 0 <= o < 256.
Proof.
  intros dt fast s d o s' d' HC H. unfold decode_sym, HufPure_FseDecomp.cell in H.
  match type of H with context [if ?b then _ else _] => destruct b eqn:R end; cbn [bind] in H; [|discriminate].
  apply andb_prop in R. destruct R as [R1 R2]. apply Z.leb_le in R1. apply Z.ltb_lt in R2.
  assert (HCc : 0 <= dc_symbol (nth (Z.to_nat s) (dt_cells dt) (mkDC 0 0 0)) < 256).
  { unfold cells_ok in HC. rewrite Forall_forall in HC. apply HC. apply nth_In. unfold FseNCount.Zlength in R2. lia. }
  destruct fast; cbn [bind] in H.
  - destruct (read_bits_fast d (dc_nbBits (nth (Z.to_nat s) (dt_cells dt) (mkDC 0 0 0)))) as [lb dd].
    injection H as <- _ _. exact HCc.
  - destruct (read_bits d (dc_nbBits (nth (Z.to_nat s) (dt_cells dt) (mkDC 0 0 0)))) as [[lb dd]| | |]; cbn [bind] in H;
      try discriminate. injection H as <- _ _. exact HCc.
Qed.

Ltac ftb_osb OUTA LJ dcap :=
  let SOK := fresh "SOK" in
  lazymatch type of OUTA with u8arr _ ?mm ?D (map (Z_to_bv 8) ?o ++ ?j) =>
  pose proof (u8arr_store_ok usegs mm D _ (zlen o) (wa (D + zlen o)) OUTA
                ltac:(repeat (rewrite length_app || rewrite length_map); cbn [length]; lia) eq_refl) as SOK;
  zstep;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) _) _) =>
      replace E with (D + zlen o) by (rewrite ?length_app; cbn [length]; lia)
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (Z_to_bv 64 ?E) _) _) =>
      replace E with (D + zlen o) by (rewrite ?length_app; cbn [length]; lia)
  end;
  rewrite le1_lit;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ [Z_to_bv 8 ?v]) _) =>
    let OUT2 := fresh "OUTA" in
    let LJ2 := fresh "LJ" in
    pose proof (out_sb usegs mm D o j v OUTA ltac:(lia)) as OUT2;
    let LO2 := fresh "LO" in
    assert (LO2 : zlen (o ++ [v]) = zlen o + 1) by (rewrite length_app; cbn [length]; lia);
    assert (LJ2 : zlen (List.tl j) = dcap - zlen (o ++ [v])) by (rewrite zlen_tl by lia; lia);
    clear OUTA LJ; store_done; rename OUT2 into OUTA; rename LJ2 into LJ
  end end.

Lemma ftb_nbm : forall sy nb, 0 <= sy < 256 -> 0 <= nb < 256 -> Z.shiftr ((sy + 256 * nb) * 65536) 24 = nb.
Proof.
  intros sy nb A B. rewrite Z.shiftr_div_pow2 by lia. change (2^24) with 16777216.
  symmetry. apply (Z.div_unique _ _ nb (sy * 65536)); lia.
Qed.

Lemma ftb_lor : forall sy nb ns, 0 <= sy < 256 -> 0 <= nb < 256 -> 0 <= ns < 65536 ->
  Z.lor ((sy + 256 * nb) * 65536) ns = ns + (sy + 256 * nb) * 65536.
Proof.
  intros sy nb ns A B C. rewrite Z.lor_comm. apply (lor_add_disjoint ns _ 16); [lia | change (2^16) with 65536; lia |].
  change (2^16) with 65536. apply Z_mod_mult.
Qed.

Lemma ftb_land16 : forall sy nb ns, 0 <= sy < 256 -> 0 <= nb < 256 -> 0 <= ns < 65536 ->
  Z.land (ns + (sy + 256 * nb) * 65536) 65535 = ns.
Proof.
  intros sy nb ns A B C. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. change (2^16) with 65536.
  rewrite Z.mod_add by lia. apply Z.mod_small; lia.
Qed.

Lemma ftb_shr16 : forall sy nb ns, 0 <= sy < 256 -> 0 <= nb < 256 -> 0 <= ns < 65536 ->
  Z.shiftr (ns + (sy + 256 * nb) * 65536) 16 = sy + 256 * nb.
Proof.
  intros sy nb ns A B C. rewrite Z.shiftr_div_pow2 by lia. change (2^16) with 65536.
  symmetry. apply (Z.div_unique _ _ (sy + 256 * nb) ns); lia.
Qed.

Lemma ftb_dsym_eq : forall dt s d, 0 <= s < zlen (dt_cells dt) ->
  decode_sym dt true s d = Ok (dc_symbol (nth (Z.to_nat s) (dt_cells dt) (mkDC 0 0 0)),
    dc_newState (nth (Z.to_nat s) (dt_cells dt) (mkDC 0 0 0)) + look_bits_fast d (dc_nbBits (nth (Z.to_nat s) (dt_cells dt) (mkDC 0 0 0))),
    skip_bits d (dc_nbBits (nth (Z.to_nat s) (dt_cells dt) (mkDC 0 0 0)))).
Proof.
  intros dt s d H. unfold decode_sym, HufPure_FseDecomp.cell.
  replace ((0 <=? s) && (s <? FseNCount.Zlength (dt_cells dt))) with true
    by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt; unfold FseNCount.Zlength]; lia).
  reflexivity.
Qed.

Lemma ftb_reload_ok : forall bs d, bitd_ok bs d -> exists st d', reload_dstream bs d = Ok (st, d').
Proof.
  intros bs [c b p z] (B0 & B1 & B2 & B3 & B4 & B5). cbn [bd_cont bd_bits bd_ptr bd_zero] in *.
  unfold reload_dstream. cbn [bd_cont bd_bits bd_ptr bd_zero]. cbv zeta.
  destruct (Z_lt_le_dec 64 b) as [OV|OV].
  { replace (64 <? b) with true by (symmetry; apply Z.ltb_lt; lia). eauto. }
  replace (64 <? b) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  assert (Q : 0 <= b / 8 <= 8) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  destruct (Z_le_gt_dec 8 p) as [FP|FP].
  { replace (8 <=? p) with true by (symmetry; apply Z.leb_le; lia).
    rewrite HufWalkKit.readLE64_ok by lia. cbn [bind]. eauto. }
  replace (8 <=? p) with false by (symmetry; apply Z.leb_gt; lia).
  destruct (Z.eq_dec p 0) as [P0|P0].
  { replace (p =? 0) with true by (symmetry; apply Z.eqb_eq; lia). eauto. }
  replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  assert (N8 : 8 <= zlen bs) by (destruct (Z_lt_le_dec (zlen bs) 8) as [Hl|Hl]; [specialize (B4 Hl); lia | lia]).
  destruct (Z_lt_le_dec (p - b / 8) 0) as [E|E].
  { replace (p - b / 8 <? 0) with true by (symmetry; apply Z.ltb_lt; lia). cbv beta iota zeta.
    rewrite HufWalkKit.readLE64_ok by lia. cbn [bind]. eauto. }
  replace (p - b / 8 <? 0) with false by (symmetry; apply Z.ltb_ge; lia). cbv beta iota zeta.
  rewrite HufWalkKit.readLE64_ok by lia. cbn [bind]. eauto.
Qed.

Ltac ftb_fix r v tac := let w := fi_reg_val r in lazymatch w with Z_to_bv 64 ?E =>
  let H := fresh "FX" in assert (H : E = v) by tac; rewrite H in *; clear H end.

Lemma ftb_byte : forall sy nb, Z_to_bv 8 (sy + 256 * nb) = Z_to_bv 8 sy.
Proof.
  intros sy nb. apply Mem.Z_to_bv8_mod. change (2^8) with 256.
  replace (sy + 256 * nb) with (sy + nb * 256) by ring. apply Z.mod_add; lia.
Qed.

Section FTB.
  Variables (SP : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem) (S DT DST dcap lo : Z) (bs : list Z)
            (dt : dtable) (POST : machine_state -> Prop).
  Hypothesis HPRE : fdw_pre SP S DT DST dcap lo bs dt.

  Notation TS pc mm j0 j s1 s2 b P c x1 x24 x25 x26 x27 :=
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 s1) (Z_to_bv 64 s2) (Z_to_bv 64 b) (Z_to_bv 64 DST) (Z_to_bv 64 (DST + j0))
             (Z_to_bv 64 (-70)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 S) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4))
             (Z_to_bv 64 (2^61)) (Z_to_bv 64 65535) (Z_to_bv 64 P) (Z_to_bv 64 (DST + j + 1)) (Z_to_bv 64 (j0 - j))
             (Z_to_bv 64 64) (Z_to_bv 64 1) (Z_to_bv 64 (-1)) (Z_to_bv 64 (DST + j)) x24 x25 x26 x27 (Z_to_bv 64 c)
             (Z_to_bv 64 (DST + dcap - 2)) (Z_to_bv 64 1) (Z_to_bv 64 2))
        F (Z_to_bv 64 (PFSE_DECOMP + pc)) fc None mm (seg_rom usegs)).

  Lemma ftb_rA : forall (out : list Z) (j0 j s1 s2 : Z) (d d' : bitD) (st : dstatus) (m1 : fmem) (jp : list byte)
                        (x1 x24 x25 x26 x27 : word),
    reload_dstream bs d = Ok (st, d') -> bitd_ok bs d -> bd_bits d <= 64 ->
    0 <= j0 <= j -> zlen out = j + 1 -> zlen out <= dcap ->
    fdw_fmem m0 m1 SP S DT DST dcap lo bs dt (mkDec out s1 s2 d) jp ->
    (forall (m2 : fmem) (jp2 : list byte) (y1 y24 y25 y26 y27 : word),
       fdw_fmem m0 m2 SP S DT DST dcap lo bs dt (mkDec out s1 s2 d') jp2 ->
       evt usegs POST (TS 4064 m2 j0 j s1 s2 (bd_bits d') (S + bd_ptr d') (bd_cont d') y1 y24 y25 y26 y27)) ->
    evt usegs POST (TS 3828 m1 j0 j s1 s2 (bd_bits d) (S + bd_ptr d) (bd_cont d) x1 x24 x25 x26 x27).
  Proof.
    intros until x27. intros RL BOK BB HJ HO HOD FM K.
    pose proof HPRE as (HTL & HCELLS & HCOK & BY & LOSP & SP16 & SP47 & HS1 & HS2 & HDT1 & HDT2 & HDT3 & HDST1 & HDST2 & HDST3
                        & DJ1 & DJ2 & DJ3).
    unfold fdw_fmem in FM. cbn [de_out de_s1 de_s2 de_bd] in FM.
    destruct FM as ((junk & OU & LJ) & (fb & fp & FR) & MU & WM & MI & TB & SB & STK).
    unfold fdw_fmem in K. cbn [de_out de_s1 de_s2 de_bd] in K.
    pose proof (fi_reload_facts bs d st d' BY BOK RL) as (BOK' & BB' & BZ' & _).
    destruct (BZ' BB) as (BZd' & _).
    assert (P2 : 2 <= 2^(dt_tableLog dt) <= 4096)
      by (split; [change 2 with (2^1); apply Z.pow_le_mono_r; lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]).
    pose proof (bytes_at_bound _ _ _ _ SB) as BSB. rewrite length_map in BSB.
    assert (LBS : Z.of_nat (length (map (Z_to_bv 8) bs)) = zlen bs) by (rewrite length_map; reflexivity).
    assert (LTB : Z.of_nat (length (concat (map fse_cell_bytes (dt_cells dt)))) = 4 * 2^(dt_tableLog dt))
      by (rewrite RF_huf_bdt_model.fse_cells_length; lia).
    unfold PFSE_DECOMP. cbn [Z.add].
    destruct d as [c b p z]. pose proof BOK as (BC & BBR & BP & BPE & BPS & BZI). cbn [bd_cont bd_bits bd_ptr bd_zero] in *.
    assert (Z0 : z = false) by (destruct z; [specialize (BZI eq_refl); lia | reflexivity]). subst z.
    unfold reload_dstream in RL. cbn [bd_cont bd_bits bd_ptr bd_zero] in RL. cbv zeta in RL.
    replace (64 <? b) with false in RL by (symmetry; apply Z.ltb_ge; lia).
    rewrite Z.shiftr_div_pow2 in RL by lia. change (2^3) with 8 in RL.
    assert (NB8 : 0 <= b / 8 <= 8) by (apply fi_div8_le; lia).
    destruct (Z_le_gt_dec 8 p) as [FP|FP].
    - replace (8 <=? p) with true in RL by (symmetry; apply Z.leb_le; lia).
      rewrite HufWalkKit.readLE64_ok in RL by lia. cbn [bind] in RL. injection RL as <- <-.
      fi_walk_until [0x205b8; 0x20618].
      fi_setreg 24%Z (Z_to_bv 64 (S + (p - b / 8))) ltac:(f_equal; fi_znG; lia).
      eapply ft_ld1; [exact SB | exact BY | lia | lia | intros z1 z17 z25 z26 z27].
      unfold PFSE_DECOMP; cbn [Z.add].
      fi_walk_until [0x20618]. all: ftb_fin K.
    - replace (8 <=? p) with false in RL by (symmetry; apply Z.leb_gt; lia).
      destruct (Z.eq_dec p 0) as [P0|P0].
      + replace (p =? 0) with true in RL by (symmetry; apply Z.eqb_eq; lia). injection RL as <- <-.
        fi_walk_until [0x205b8; 0x20618]. all: ftb_fin K.
      + replace (p =? 0) with false in RL by (symmetry; apply Z.eqb_neq; lia).
        assert (L8 : 8 <= zlen bs) by (destruct (Z_lt_le_dec (zlen bs) 8) as [Hl|Hl]; [specialize (BPS Hl); lia | lia]).
        destruct (Z_lt_le_dec (p - b / 8) 0) as [EOB|UNF].
        * replace (p - b / 8 <? 0) with true in RL by (symmetry; apply Z.ltb_lt; lia).
          cbv beta iota zeta in RL. rewrite HufWalkKit.readLE64_ok in RL by lia. cbn [bind] in RL. injection RL as <- <-.
          fi_walk_until [0x205b8; 0x20618].
          fi_setreg 24%Z (Z_to_bv 64 (S + (p - p))) ltac:(f_equal; fi_znG; lia).
          eapply ft_ld1; [exact SB | exact BY | lia | lia | intros z1 z17 z25 z26 z27].
          unfold PFSE_DECOMP; cbn [Z.add].
          fi_walk_until [0x20618].
          all: fi_setreg 7%Z (Z_to_bv 64 (b - p * 8)) ltac:(f_equal; fi_znG; lia).
          all: ftb_fin K.
        * replace (p - b / 8 <? 0) with false in RL by (symmetry; apply Z.ltb_ge; lia).
          cbv beta iota zeta in RL. rewrite HufWalkKit.readLE64_ok in RL by lia. cbn [bind] in RL. injection RL as <- <-.
          fi_walk_until [0x205b8; 0x20618].
          fi_setreg 24%Z (Z_to_bv 64 (S + (p - b / 8))) ltac:(f_equal; fi_znG; lia).
          eapply ft_ld1; [exact SB | exact BY | lia | lia | intros z1 z17 z25 z26 z27].
          unfold PFSE_DECOMP; cbn [Z.add].
          fi_walk_until [0x20618].
          all: fi_setreg 7%Z (Z_to_bv 64 (b - b / 8 * 8)) ltac:(f_equal; fi_znG; lia).
          all: ftb_fin K.
  Qed.

  Lemma ftb_rB : forall (out : list Z) (j0 j s1 s2 : Z) (d d' : bitD) (st : dstatus) (m1 : fmem) (jp : list byte)
                        (x1 x24 x25 x26 x27 : word),
    reload_dstream bs d = Ok (st, d') -> bitd_ok bs d -> bd_bits d <= 64 ->
    0 <= j0 <= j -> zlen out = j + 2 -> zlen out <= dcap ->
    fdw_fmem m0 m1 SP S DT DST dcap lo bs dt (mkDec out s1 s2 d) jp ->
    (forall (m2 : fmem) (jp2 : list byte) (y1 y24 y25 y26 y27 : word),
       fdw_fmem m0 m2 SP S DT DST dcap lo bs dt (mkDec out s1 s2 d') jp2 ->
       evt usegs POST (TS 3704 m2 j0 j s1 s2 (bd_bits d') (S + bd_ptr d') (bd_cont d') y1 y24 y25 y26 y27)) ->
    evt usegs POST (TS 4168 m1 j0 j s1 s2 (bd_bits d) (S + bd_ptr d) (bd_cont d) x1 x24 x25 x26 x27).
  Proof.
    intros until x27. intros RL BOK BB HJ HO HOD FM K.
    pose proof HPRE as (HTL & HCELLS & HCOK & BY & LOSP & SP16 & SP47 & HS1 & HS2 & HDT1 & HDT2 & HDT3 & HDST1 & HDST2 & HDST3
                        & DJ1 & DJ2 & DJ3).
    unfold fdw_fmem in FM. cbn [de_out de_s1 de_s2 de_bd] in FM.
    destruct FM as ((junk & OU & LJ) & (fb & fp & FR) & MU & WM & MI & TB & SB & STK).
    unfold fdw_fmem in K. cbn [de_out de_s1 de_s2 de_bd] in K.
    pose proof (fi_reload_facts bs d st d' BY BOK RL) as (BOK' & BB' & BZ' & _).
    destruct (BZ' BB) as (BZd' & _).
    assert (P2 : 2 <= 2^(dt_tableLog dt) <= 4096)
      by (split; [change 2 with (2^1); apply Z.pow_le_mono_r; lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]).
    pose proof (bytes_at_bound _ _ _ _ SB) as BSB. rewrite length_map in BSB.
    assert (LBS : Z.of_nat (length (map (Z_to_bv 8) bs)) = zlen bs) by (rewrite length_map; reflexivity).
    assert (LTB : Z.of_nat (length (concat (map fse_cell_bytes (dt_cells dt)))) = 4 * 2^(dt_tableLog dt))
      by (rewrite RF_huf_bdt_model.fse_cells_length; lia).
    unfold PFSE_DECOMP. cbn [Z.add].
    destruct d as [c b p z]. pose proof BOK as (BC & BBR & BP & BPE & BPS & BZI). cbn [bd_cont bd_bits bd_ptr bd_zero] in *.
    assert (Z0 : z = false) by (destruct z; [specialize (BZI eq_refl); lia | reflexivity]). subst z.
    unfold reload_dstream in RL. cbn [bd_cont bd_bits bd_ptr bd_zero] in RL. cbv zeta in RL.
    replace (64 <? b) with false in RL by (symmetry; apply Z.ltb_ge; lia).
    rewrite Z.shiftr_div_pow2 in RL by lia. change (2^3) with 8 in RL.
    assert (NB8 : 0 <= b / 8 <= 8) by (apply fi_div8_le; lia).
    destruct (Z_le_gt_dec 8 p) as [FP|FP].
    - replace (8 <=? p) with true in RL by (symmetry; apply Z.leb_le; lia).
      rewrite HufWalkKit.readLE64_ok in RL by lia. cbn [bind] in RL. injection RL as <- <-.
      fi_walk_until [0x2070c; 0x204b0].
      fi_setreg 24%Z (Z_to_bv 64 (S + (p - b / 8))) ltac:(f_equal; fi_znG; lia).
      eapply ft_ld2; [exact SB | exact BY | lia | lia | intros z1 z17 z25 z26 z27].
      unfold PFSE_DECOMP; cbn [Z.add].
      fi_walk_until [0x204b0]. all: ftb_fin K.
    - replace (8 <=? p) with false in RL by (symmetry; apply Z.leb_gt; lia).
      destruct (Z.eq_dec p 0) as [P0|P0].
      + replace (p =? 0) with true in RL by (symmetry; apply Z.eqb_eq; lia). injection RL as <- <-.
        fi_walk_until [0x2070c; 0x204b0]. all: ftb_fin K.
      + replace (p =? 0) with false in RL by (symmetry; apply Z.eqb_neq; lia).
        assert (L8 : 8 <= zlen bs) by (destruct (Z_lt_le_dec (zlen bs) 8) as [Hl|Hl]; [specialize (BPS Hl); lia | lia]).
        destruct (Z_lt_le_dec (p - b / 8) 0) as [EOB|UNF].
        * replace (p - b / 8 <? 0) with true in RL by (symmetry; apply Z.ltb_lt; lia).
          cbv beta iota zeta in RL. rewrite HufWalkKit.readLE64_ok in RL by lia. cbn [bind] in RL. injection RL as <- <-.
          fi_walk_until [0x2070c; 0x204b0].
          fi_setreg 24%Z (Z_to_bv 64 (S + (p - p))) ltac:(f_equal; fi_znG; lia).
          eapply ft_ld2; [exact SB | exact BY | lia | lia | intros z1 z17 z25 z26 z27].
          unfold PFSE_DECOMP; cbn [Z.add].
          fi_walk_until [0x204b0].
          all: fi_setreg 7%Z (Z_to_bv 64 (b - p * 8)) ltac:(f_equal; fi_znG; lia).
          all: ftb_fin K.
        * replace (p - b / 8 <? 0) with false in RL by (symmetry; apply Z.ltb_ge; lia).
          cbv beta iota zeta in RL. rewrite HufWalkKit.readLE64_ok in RL by lia. cbn [bind] in RL. injection RL as <- <-.
          fi_walk_until [0x2070c; 0x204b0].
          fi_setreg 24%Z (Z_to_bv 64 (S + (p - b / 8))) ltac:(f_equal; fi_znG; lia).
          eapply ft_ld2; [exact SB | exact BY | lia | lia | intros z1 z17 z25 z26 z27].
          unfold PFSE_DECOMP; cbn [Z.add].
          fi_walk_until [0x204b0].
          all: fi_setreg 7%Z (Z_to_bv 64 (b - b / 8 * 8)) ltac:(f_equal; fi_znG; lia).
          all: ftb_fin K.
  Qed.
  Definition ftb_mem (m1 : fmem) (out : list Z) (s1 s2 : Z) (d : bitD) (jp : list byte) : Prop :=
    (exists junk, u8arr usegs m1 DST (map (Z_to_bv 8) out ++ junk) /\ zlen junk = dcap - zlen out)
    /\ (exists fp : word, rw_cells usegs m1 (SP + 16)
          [C8 (Z_to_bv 64 s2); C8 (Z_to_bv 64 (DT + 4)); C8 (Z_to_bv 64 s1); C8 (Z_to_bv 64 (DT + 4));
           C8 (Z_to_bv 64 (bd_cont d)); C4 (Z_to_bv 64 (bd_bits d)); CB 4 jp; C8 fp; C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))])
    /\ munch [(SP + 16, SP + 88); (DST, DST + dcap)] m0 m1 /\ wmono usegs m0 m1 /\ mem_inv usegs m1
    /\ bytes_at usegs m1 (DT + 4) (concat (map fse_cell_bytes (dt_cells dt)))
    /\ bytes_at usegs m1 S (map (Z_to_bv 8) bs)
    /\ stk usegs m1 lo SP.

  Notation TF pc mm j0 j b x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 (Z_to_bv 64 b) (Z_to_bv 64 DST) (Z_to_bv 64 (DST + j0)) x10 x11 x12 x13 x14
             x15 x16 x17 (Z_to_bv 64 (DST + j + 1)) (Z_to_bv 64 (j0 - j)) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 (PFSE_DECOMP + pc)) fc None mm (seg_rom usegs)).

  Lemma ftb_finA : fse_dsymf_stmt -> fdw_fin1_stmt ->
    forall (out : list Z) (j0 j s1 s2 o s' : Z) (d d' : bitD) (m1 : fmem) (jp : list byte)
           (x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    0 <= bd_bits d <= 2^30 -> 0 <= bd_cont d < 2^64 ->
    decode_sym dt true s2 (mkBD (bd_cont d) (bd_bits d) (bd_ptr d) true) = Ok (o, s', d') ->
    0 <= j0 <= j -> zlen out = j + 1 -> zlen out + 1 <= dcap ->
    ftb_mem m1 out s1 s2 d jp ->
    fdw_K SP gp tp F fc m0 DST dcap lo POST (Ok (out ++ [o])) ->
    evt usegs POST (TF 4408 m1 j0 j (bd_bits d) x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27
                       x28 x29 x30 x31).
  Proof.
    intros DSYMF FIN1. intros until x31. intros BB BC DS HJ HO HOD FM K.
    pose proof HPRE as (HTL & HCELLS & HCOK & BY & LOSP & SP16 & SP47 & HS1 & HS2 & HDT1 & HDT2 & HDT3 & HDST1 & HDST2 & HDST3
                        & DJ1 & DJ2 & DJ3).
    unfold ftb_mem in FM. destruct FM as ((junk & OU & LJ) & (fp & FR) & MU & WM & MI & TB & SB & STK).
    pose proof (ftb_dsym_o dt true s2 _ o s' d' HCOK DS) as ORNG.
    assert (P2 : 2 <= 2^(dt_tableLog dt) <= 4096)
      by (split; [change 2 with (2^1); apply Z.pow_le_mono_r; lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]).
    pose proof (bytes_at_bound _ _ _ _ SB) as BSB. rewrite length_map in BSB.
    assert (LBS : Z.of_nat (length (map (Z_to_bv 8) bs)) = zlen bs) by (rewrite length_map; reflexivity).
    assert (LTB : Z.of_nat (length (concat (map fse_cell_bytes (dt_cells dt)))) = 4 * 2^(dt_tableLog dt))
      by (rewrite RF_huf_bdt_model.fse_cells_length; lia).
    assert (LOU : Z.of_nat (length (map (Z_to_bv 8) out ++ junk)) = dcap) by (rewrite length_app, length_map; lia).
    unfold PFSE_DECOMP. cbn [Z.add].
    fi_walk_until [0x20ca0].
    pose proof (proj1 (rw_cells_app' usegs _ (SP + 16) [C8 (Z_to_bv 64 s2); C8 (Z_to_bv 64 (DT + 4))] _) FR) as (F16 & FR2).
    replace (SP + 16 + Z.of_nat (cells_size [C8 (Z_to_bv 64 s2); C8 (Z_to_bv 64 (DT + 4))])) with (SP + 32) in FR2
      by (cbn [cells_size csize Nat.add]; lia).
    pose proof (proj1 (rw_cells_app' usegs _ (SP + 32) [C8 (Z_to_bv 64 s1); C8 (Z_to_bv 64 (DT + 4))] _) FR2) as (F32 & F48).
    replace (SP + 32 + Z.of_nat (cells_size [C8 (Z_to_bv 64 s1); C8 (Z_to_bv 64 (DT + 4))])) with (SP + 48) in F48
      by (cbn [cells_size csize Nat.add]; lia).
    clear FR FR2.
    assert (ESP : bv_unsigned (Z_to_bv 64 SP) = SP) by (apply unsigned_lit; lia).
    eapply evt_cut.
    { eapply (DSYMF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (SP + 16) (SP + 48) DT S lo dt s2 (mkBD (bd_cont d) (bd_bits d) (bd_ptr d) true) jp o s' d').
      all: rewrite ?ESP.
      all: first [eassumption | lia | exact HCOK | (unfold bitdz_cells; cbn [bd_cont bd_bits bd_ptr bd_zero]; exact F48)]. }
    unfold fse_dsym_post. lazymatch goal with MIx : mem_inv usegs ?mm |- _ => post_call usegs mm end.
    fi_walk_until [0x207dc].
    fi_setreg 11%Z (Z_to_bv 64 (DST + zlen out - 1)) ltac:(apply Z_to_bv_eqm; rewrite HO; Z.div_mod_to_equations; lia).
    fi_setreg 18%Z (Z_to_bv 64 (DST + zlen out - 1 + 1)) ltac:(f_equal; lia).
    pose proof (FIN1 SP gp tp F fc m0 S DT DST dcap lo bs dt POST out o HPRE ORNG ltac:(lia) HOD K) as KF.
    unfold fdw_fin_K in KF. eapply KF.
    - unfold sm_inv. split; [exists junk; split; eassumption|]. split; [eassumption|]. split; eassumption.
    - eassumption.
  Qed.

  Lemma ftb_finB : fse_dsymf_stmt -> fdw_fin2_stmt ->
    forall (out : list Z) (j0 j s1 s2 o s' : Z) (d d' : bitD) (m1 : fmem) (jp : list byte)
           (x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    0 <= bd_bits d <= 2^30 -> 0 <= bd_cont d < 2^64 ->
    decode_sym dt true s1 (mkBD (bd_cont d) (bd_bits d) (bd_ptr d) true) = Ok (o, s', d') ->
    0 <= j0 <= j -> zlen out = j + 2 -> zlen out + 1 <= dcap ->
    ftb_mem m1 out s1 s2 d jp ->
    fdw_K SP gp tp F fc m0 DST dcap lo POST (Ok (out ++ [o])) ->
    evt usegs POST (TF 4448 m1 j0 j (bd_bits d) x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27
                       x28 x29 x30 x31).
  Proof.
    intros DSYMF FIN2. intros until x31. intros BB BC DS HJ HO HOD FM K.
    pose proof HPRE as (HTL & HCELLS & HCOK & BY & LOSP & SP16 & SP47 & HS1 & HS2 & HDT1 & HDT2 & HDT3 & HDST1 & HDST2 & HDST3
                        & DJ1 & DJ2 & DJ3).
    unfold ftb_mem in FM. destruct FM as ((junk & OU & LJ) & (fp & FR) & MU & WM & MI & TB & SB & STK).
    pose proof (ftb_dsym_o dt true s1 _ o s' d' HCOK DS) as ORNG.
    assert (P2 : 2 <= 2^(dt_tableLog dt) <= 4096)
      by (split; [change 2 with (2^1); apply Z.pow_le_mono_r; lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]).
    pose proof (bytes_at_bound _ _ _ _ SB) as BSB. rewrite length_map in BSB.
    assert (LBS : Z.of_nat (length (map (Z_to_bv 8) bs)) = zlen bs) by (rewrite length_map; reflexivity).
    assert (LTB : Z.of_nat (length (concat (map fse_cell_bytes (dt_cells dt)))) = 4 * 2^(dt_tableLog dt))
      by (rewrite RF_huf_bdt_model.fse_cells_length; lia).
    assert (LOU : Z.of_nat (length (map (Z_to_bv 8) out ++ junk)) = dcap) by (rewrite length_app, length_map; lia).
    unfold PFSE_DECOMP. cbn [Z.add].
    fi_walk_until [0x20ca0].
    pose proof (proj1 (rw_cells_app' usegs _ (SP + 16) [C8 (Z_to_bv 64 s2); C8 (Z_to_bv 64 (DT + 4))] _) FR) as (F16 & FR2).
    replace (SP + 16 + Z.of_nat (cells_size [C8 (Z_to_bv 64 s2); C8 (Z_to_bv 64 (DT + 4))])) with (SP + 32) in FR2
      by (cbn [cells_size csize Nat.add]; lia).
    pose proof (proj1 (rw_cells_app' usegs _ (SP + 32) [C8 (Z_to_bv 64 s1); C8 (Z_to_bv 64 (DT + 4))] _) FR2) as (F32 & F48).
    replace (SP + 32 + Z.of_nat (cells_size [C8 (Z_to_bv 64 s1); C8 (Z_to_bv 64 (DT + 4))])) with (SP + 48) in F48
      by (cbn [cells_size csize Nat.add]; lia).
    clear FR FR2.
    assert (ESP : bv_unsigned (Z_to_bv 64 SP) = SP) by (apply unsigned_lit; lia).
    eapply evt_cut.
    { eapply (DSYMF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (SP + 32) (SP + 48) DT S lo dt s1 (mkBD (bd_cont d) (bd_bits d) (bd_ptr d) true) jp o s' d').
      all: rewrite ?ESP.
      all: first [eassumption | lia | exact HCOK | (unfold bitdz_cells; cbn [bd_cont bd_bits bd_ptr bd_zero]; exact F48)]. }
    unfold fse_dsym_post. lazymatch goal with MIx : mem_inv usegs ?mm |- _ => post_call usegs mm end.
    fi_walk_until [0x20808].
    fi_setreg 11%Z (Z_to_bv 64 (DST + zlen out - 2)) ltac:(apply Z_to_bv_eqm; rewrite HO; Z.div_mod_to_equations; lia).
    fi_setreg 18%Z (Z_to_bv 64 (DST + zlen out - 2 + 1)) ltac:(f_equal; lia).
    pose proof (FIN2 SP gp tp F fc m0 S DT DST dcap lo bs dt POST out o HPRE ORNG ltac:(lia) HOD K) as KF.
    unfold fdw_fin_K in KF. eapply KF.
    - unfold sm_inv. split; [exists junk; split; eassumption|]. split; [eassumption|]. split; eassumption.
    - eassumption.
  Qed.

  Lemma ftb_mid : fse_dsymf_stmt -> fdw_fin2_stmt ->
    forall (out : list Z) (j0 j s1 s2 : Z) (d : bitD) (m1 : fmem) (jp : list byte) (x1 x24 x25 x26 x27 : word),
    bitd_ok bs d -> bd_bits d <= 64 -> bd_zero d = false ->
    0 <= j0 <= j -> zlen out = j + 1 -> zlen out <= dcap -> Forall (fun c => 0 <= c < 256) out ->
    (zlen out <= dcap - 2 -> 0 <= s2 < 2^(dt_tableLog dt)) ->
    fdw_fmem m0 m1 SP S DT DST dcap lo bs dt (mkDec out s1 s2 d) jp ->
    (dcap - 2 < zlen out -> fdw_K SP gp tp F fc m0 DST dcap lo POST (Err ZSTD_error_dstSize_tooSmall)) ->
    (forall (o1 s2a : Z) (d2 : bitD) (st2 : dstatus) (d2r : bitD),
       zlen out <= dcap - 2 -> decode_sym dt true s2 d = Ok (o1, s2a, d2) -> reload_dstream bs d2 = Ok (st2, d2r) ->
       (64 < bd_bits d2 -> 0 <= s1 < 2^(dt_tableLog dt)) /\
       (dstatus_eqb st2 Overflow = true -> forall (o2 s' : Z) (d' : bitD), decode_sym dt true s1 d2r = Ok (o2, s', d') ->
          fdw_K SP gp tp F fc m0 DST dcap lo POST (Ok (out ++ [o1; o2])))
       /\ (dstatus_eqb st2 Overflow = false -> forall (m2 : fmem) (jp2 : list byte) (y1 y24 y25 y26 y27 : word),
          fdw_fmem m0 m2 SP S DT DST dcap lo bs dt (mkDec (out ++ [o1]) s1 s2a d2r) jp2 ->
          evt usegs POST (TS 3704 m2 j0 j s1 s2a (bd_bits d2r) (S + bd_ptr d2r) (bd_cont d2r) y1 y24 y25 y26 y27))) ->
    evt usegs POST (TS 4064 m1 j0 j s1 s2 (bd_bits d) (S + bd_ptr d) (bd_cont d) x1 x24 x25 x26 x27).
  Proof.
    intros DSYMF FIN2. intros until x27. intros BOK BB BZ HJ HO HOD HOB HS2R FM KE KC.
    pose proof HPRE as (HTL & HCELLS & HCOK & BY & LOSP & SP16 & SP47 & HS1 & HS2 & HDT1 & HDT2 & HDT3 & HDST1 & HDST2 & HDST3
                        & DJ1 & DJ2 & DJ3).
    unfold fdw_fmem in FM. cbn [de_out de_s1 de_s2 de_bd] in FM.
    destruct FM as ((junk & OU & LJ) & (fb & fp & FR) & MU & WM & MI & TB & SB & STK).
    assert (P2 : 2 <= 2^(dt_tableLog dt) <= 4096)
      by (split; [change 2 with (2^1); apply Z.pow_le_mono_r; lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]).
    pose proof (bytes_at_bound _ _ _ _ SB) as BSB. rewrite length_map in BSB.
    assert (LBS : Z.of_nat (length (map (Z_to_bv 8) bs)) = zlen bs) by (rewrite length_map; reflexivity).
    assert (LTB : Z.of_nat (length (concat (map fse_cell_bytes (dt_cells dt)))) = 4 * 2^(dt_tableLog dt))
      by (rewrite RF_huf_bdt_model.fse_cells_length; lia).
    assert (LOU : Z.of_nat (length (map (Z_to_bv 8) out ++ junk)) = dcap) by (rewrite length_app, length_map; lia).
    pose proof BOK as (BC & BBR & BP & BPE & BPS & BZI).
    unfold PFSE_DECOMP. cbn [Z.add].
    destruct (Z_lt_le_dec (dcap - 2) (zlen out)) as [ERR|SZ].
    { fi_walk_until [0x20450; 0x20798; 0x20680].
      all: pose proof (KE ERR) as K1; unfold fdw_K in K1.
      all: eapply K1; first [eassumption | (cbn [dres]; split; [reflexivity | vm_compute; split; reflexivity])
                           ]. }
    specialize (HS2R SZ).
    assert (NE : nth_error (dt_cells dt) (Z.to_nat s2) = Some (nth (Z.to_nat s2) (dt_cells dt) (mkDC 0 0 0)))
      by (apply nth_error_nth'; lia).
    pose proof (ftb_dsym_eq dt s2 d ltac:(lia)) as DSE.
    set (c := nth (Z.to_nat s2) (dt_cells dt) (mkDC 0 0 0)) in *. clearbody c.
    pose proof (proj1 (Forall_forall _ _) HCOK c (nth_error_In _ _ NE)) as CK. cbv beta in CK.
    destruct CK as (CS & CN & CN0 & CNS).
    pose proof (Z.pow_pos_nonneg 2 (dc_nbBits c) ltac:(lia) ltac:(lia)) as PN.
    pose proof (cell_rd_ns usegs m1 (DT + 4) (dt_cells dt) s2 c (Z_to_bv 64 (s2 * 4 + (DT + 4))) TB NE ltac:(lia)
                  ltac:(unfold wa; f_equal; lia)) as RNS.
    pose proof (cell_rd_off usegs m1 (DT + 4) (dt_cells dt) s2 c 2 2%nat TB NE ltac:(lia) ltac:(lia) ltac:(lia)) as RSN.
    change (Z.to_nat 2) with 2%nat in RSN. unfold fse_cell_bytes, le2 in RSN. cbn [firstn skipn app Z_to_le_bytes] in RSN.
    rewrite <- (le2_two_bytes (dc_symbol c) (dc_nbBits c)) in RSN by lia.
    replace (DT + 4 + (4 * s2 + 2)) with (s2 * 4 + (DT + 4) + 2) in RSN by lia. unfold wa in RSN.
    fi_walk_until [0x20450; 0x20798; 0x20680].
    ftb_osb OU LJ dcap.
    fi_walk_until [0x20450; 0x20798; 0x20680].
    all: rewrite ?(ftb_lor (dc_symbol c) (dc_nbBits c) (dc_newState c)) in * by lia.
    all: rewrite ?(ftb_nbm (dc_symbol c) (dc_nbBits c)) in * by lia.
    all: rewrite ?(ftb_land16 (dc_symbol c) (dc_nbBits c) (dc_newState c)) in * by lia.
    all: rewrite ?(fd_sh (dc_nbBits c)) in * by lia.
    all: rewrite ?(ftb_shr16 (dc_symbol c) (dc_nbBits c) (dc_newState c)) in * by lia.
    all: rewrite ?(fd_land (dc_symbol c) (dc_nbBits c)) in * by lia.
    all: match goal with H : u8arr _ _ _ (map (Z_to_bv 8) (_ ++ [_ + 256 * _]) ++ _) |- _ =>
           rewrite map_app in H; cbn [map] in H; rewrite (ftb_byte (dc_symbol c) (dc_nbBits c)) in H;
           change ([Z_to_bv 8 (dc_symbol c)]) with (map (Z_to_bv 8) [dc_symbol c]) in H; rewrite <- map_app in H end.
    all: ftb_fix 7%Z (bd_bits (skip_bits d (dc_nbBits c)))
           ltac:(unfold skip_bits, u32; cbn [bd_bits]; rewrite FseWalkKit.swrap32_small by lia; rewrite Z.mod_small by lia; lia).
    all: ftb_fix 6%Z (dc_newState c + look_bits_fast d (dc_nbBits c))
           ltac:(unfold look_bits_fast, u64; rewrite Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia);
                 replace (u32 (bd_bits d)) with (bd_bits d) by (unfold u32; rewrite Z.mod_small; lia);
                 change (2 ^ 64) with 18446744073709551616; lia).
    all: pose proof (fi_skip_ok bs d (dc_nbBits c) BOK ltac:(lia) ltac:(lia)) as (BOK2 & BB2).
    all: destruct (ftb_reload_ok bs _ BOK2) as (st2 & d2r & RL2).
    all: destruct (KC _ _ _ _ _ SZ DSE RL2) as (KS1 & KOV & KNO).
    all: lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x20798) _ _ _ _) =>
        assert (BBX : 64 < bd_bits (skip_bits d (dc_nbBits c)))
          by (match goal with U : 64 < _ mod _ |- _ => rewrite BB2 in U |- *; rewrite Z.mod_small in U by lia; lia end);
        pose proof (KS1 BBX) as HS1R;
        pose proof (fi_reload_facts bs _ st2 d2r BY BOK2 RL2) as (BOKr & BBr & BZr & BOVr);
        destruct (BOVr BBX) as (STO & D2R);
        pose proof (ftb_dsym_eq dt s1 d2r ltac:(lia)) as DS1;
        eapply (ftb_finB DSYMF FIN2 (out ++ [dc_symbol c]) j0 j s1 _ _ _ (skip_bits d (dc_nbBits c)) _ _ jp);
        [ lia | cbn [skip_bits bd_cont]; lia | rewrite D2R in DS1; exact DS1 | lia
        | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia
        | unfold ftb_mem; split; [eexists; split; [eassumption | rewrite ?length_app in *; cbn [length] in *; lia]|];
          split; [eexists; eassumption|];
          split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption
        | rewrite <- app_assoc; cbn [app]; eapply KOV;
          [destruct st2; first [reflexivity | (cbn in STO; contradiction)] | exact DS1] ]
    | |- _ =>
        assert (BBX : bd_bits (skip_bits d (dc_nbBits c)) <= 64)
          by (rewrite BB2; first [ (match goal with U : (bd_bits _ + dc_nbBits _) mod _ <= 64 |- _ =>
                                         rewrite Z.mod_small in U by lia; lia end)
                                 | (match goal with U : bd_bits (skip_bits _ _) mod _ <= 64 |- _ =>
                                         rewrite BB2 in U; rewrite Z.mod_small in U by lia; lia end) ]);
        pose proof (fi_reload_facts bs _ st2 d2r BY BOK2 RL2) as (BOKr & BBr & BZr & BOVr);
        destruct (BZr BBX) as (BZd2r & STN);
        change (Z_to_bv 64 (S + bd_ptr d)) with (Z_to_bv 64 (S + bd_ptr (skip_bits d (dc_nbBits c))));
        change (Z_to_bv 64 (bd_cont d)) with (Z_to_bv 64 (bd_cont (skip_bits d (dc_nbBits c))));
        eapply (ftb_rB (out ++ [dc_symbol c]) j0 j s1 _ (skip_bits d (dc_nbBits c)) d2r st2);
        [ exact RL2 | exact BOK2 | exact BBX | lia | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia
        | unfold fdw_fmem; cbn [de_out de_s1 de_s2 de_bd];
          split; [eexists; split; [eassumption | rewrite ?length_app in *; cbn [length] in *; lia]|]; split; [do 2 eexists; eassumption|];
          split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption
        | intros m2 jp2 y1 y24 y25 y26 y27 FM2; eapply KNO; [destruct st2; first [reflexivity | (cbn in STN; contradiction)] | exact FM2] ]
    end.
  Qed.
End FTB.
