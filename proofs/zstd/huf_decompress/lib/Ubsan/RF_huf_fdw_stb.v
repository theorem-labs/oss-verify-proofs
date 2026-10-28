From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit HufWalkKit STRW_tac.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface RF_huf_tbl_iface RF_huf_tbl_kit RF_huf_fdw_kit
  RF_huf_bdt_model RF_huf_fdw_stl RF_huf_fdw_cut.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac slia ::= slia_sep.

Section STB.
  Variables (SP : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem) (S DT DST dcap lo : Z) (bs : list Z)
            (dt : dtable) (POST : machine_state -> Prop).
  Hypothesis PRE : fdw_pre SP S DT DST dcap lo bs dt.

  Notation tl := (dt_tableLog dt).
  Notation STF pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation STH pc mm x1 j0 j x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (STF pc mm x1 (Z_to_bv 64 64) (Z_to_bv 64 (-1)) (Z_to_bv 64 (DST + j)) (Z_to_bv 64 DST)
         (Z_to_bv 64 (2^61)) (Z_to_bv 64 (-70)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 1) (Z_to_bv 64 1)
         (Z_to_bv 64 (DST + dcap + -2)) (Z_to_bv 64 (2^64 - 1 - BIT_MASK_TAB)) (Z_to_bv 64 2) (Z_to_bv 64 (DST + j + 1))
         (Z_to_bv 64 (2^16 - 1)) (Z_to_bv 64 BIT_MASK_TAB) (Z_to_bv 64 (DST + j0)) (Z_to_bv 64 (j0 - j))
         x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Notation TIb m out s1 s2 d := (exists jp, fdw_mem m0 m SP S DT DST dcap lo bs dt (mkDec out s1 s2 d) jp).

  Ltac sw1 stops := lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) =>
        lazymatch eval vm_compute in (existsb (Z.eqb p) stops) with true => fail | false => zstep end
    | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => let K := fresh "K" in if_cases K; zify_cond K; try dead
    end.
  Ltac sw stops := repeat (first [sw1 stops; znorm | ldc; znorm | ldm; znorm | osh; znorm | lds; znorm]).

  Lemma stb_land7 : forall b, 0 <= b -> Z.land b 7 = b mod 8.
  Proof. intros b Hb. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

  Lemma stb_cells_eq : forall (x x' y y' z z' : Z) jp (a a' : word),
    x = x' -> y = y' -> z = z' ->
    [C8 (Z_to_bv 64 x); C4 (Z_to_bv 64 y); CB 4 jp; C8 (Z_to_bv 64 z); C8 a; C8 a'] =
    [C8 (Z_to_bv 64 x'); C4 (Z_to_bv 64 y'); CB 4 jp; C8 (Z_to_bv 64 z'); C8 a; C8 a'].
  Proof. intros; subst; reflexivity. Qed.

  Ltac stb_idx := kn; change (2^3) with 8 in *; lia.
  Ltac stb_byte BY := apply byte_Znth; [exact BY | stb_idx].
  Ltac stb_sum := repeat (lazymatch goal with
    | |- ?a + ?b = ?c + ?d => apply (f_equal2 Z.add)
    | |- ?k * Znth _ _ = ?k * Znth _ _ => apply (f_equal (Z.mul k))
    | |- Znth _ ?l = Znth _ ?l => apply (f_equal (fun i => Znth i l))
    end).
  Ltac stb_val BY := first [ reflexivity | stb_idx
                           | (rewrite le64_lbu_raw by stb_byte BY; stb_sum; stb_idx)
                           | (rewrite stb_land7 by lia; kn; change (2^3) with 8 in *; lia) ].
  Ltac stb_close K BY JP :=
    eapply K; exists JP; unfold fdw_mem; cbn [de_out de_s1 de_s2 de_bd];
    split; [eassumption|]; split; [eassumption|];
    (split; [ unfold bitdz_cells; cbn [bd_cont bd_bits bd_ptr bd_zero];
              lazymatch goal with |- rw_cells _ ?mm ?A _ => lazymatch goal with H : rw_cells _ mm A _ |- _ =>
                refine (eq_ind _ (fun l => rw_cells usegs mm A l) H _ _) end end;
              apply stb_cells_eq; stb_val BY | ]);
    split; [split; [eexists; split; eassumption | split; [eassumption | split; eassumption]] |];
    split; [eassumption|]; split; eassumption.

  (* [comment removed for export] *)
  Lemma stb_rA : forall m1 out s1 s2 d st d' j0 j (x1 x23 x24 x25 x26 x27 x28 x30 x31 : word),
    TIb m1 out s1 s2 d -> bitd_ok bs d -> bd_bits d <= 64 -> reload_dstream bs d = Ok (st, d') ->
    (forall m2 (y23 y24 y25 y29 y30 y31 : word), TIb m2 out s1 s2 d' ->
       evt usegs POST (STH 0x1ffa0 m2 x1 j0 j y23 y24 y25 x26 x27 (Z_to_bv 64 (S + 8)) y29 y30 y31)) ->
    evt usegs POST (STH 0x1feac m1 x1 j0 j x23 x24 x25 x26 x27 x28 (Z_to_bv 64 (bd_bits d)) x30 x31).
  Proof using All.
    intros until x31. intros (jp_ & FM) BOK BB RL K.
    pose proof PRE as (HTL & HCELLS & HCOK & BY & LOSP & SP16 & SP47 & HS1 & HS2 & HDT1 & HDT2 & HDT3 & HDST1 & HDST2 & HDST3
                        & DJ1 & DJ2 & DJ3).
    unfold fdw_mem in FM. cbn [de_out de_s1 de_s2 de_bd] in FM.
    destruct FM as (FS2 & FS1 & FBD & ((junk & OUT & LJ) & MU & WM & MI) & TBB & SRC & STK).
    destruct d as [c b p z]. pose proof BOK as (BC & BBR & BP & BPE & BPS & BZI). cbn [bd_cont bd_bits bd_ptr bd_zero] in *.
    assert (Z0 : z = false) by (destruct z; [specialize (BZI eq_refl); lia | reflexivity]). subst z.
    unfold bitdz_cells in FBD. cbn [bd_cont bd_bits bd_ptr bd_zero] in FBD.
    pose proof (bytes_at_bound _ _ _ _ SRC) as BSB. rewrite length_map in BSB.
    assert (P2 : 2 <= 2^(dt_tableLog dt) <= 4096)
      by (split; [change 2 with (2^1); apply Z.pow_le_mono_r; lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]).
    assert (LBS : Z.of_nat (length (map (Z_to_bv 8) bs)) = zlen bs) by (rewrite length_map; reflexivity).
    assert (LTB : Z.of_nat (length (concat (map fse_cell_bytes (dt_cells dt)))) = 4 * 2^(dt_tableLog dt))
      by (rewrite RF_huf_bdt_model.fse_cells_length; lia).
    assert (NB8 : 0 <= b / 8 <= 8) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
    unfold reload_dstream in RL. cbn [bd_cont bd_bits bd_ptr bd_zero] in RL. cbv zeta in RL.
    replace (64 <? b) with false in RL by (symmetry; apply Z.ltb_ge; lia).
    rewrite Z.shiftr_div_pow2 in RL by lia. change (2^3) with 8 in RL.
    destruct (Z_le_gt_dec 8 p) as [FP|FP].
    - replace (8 <=? p) with true in RL by (symmetry; apply Z.leb_le; lia).
      rewrite HufWalkKit.readLE64_ok in RL by lia. cbn [bind] in RL. injection RL as <- <-.
      sw [130976; 130568]. all: stb_close K BY jp_.
    - replace (8 <=? p) with false in RL by (symmetry; apply Z.leb_gt; lia).
      destruct (Z.eq_dec p 0) as [P0|P0].
      + replace (p =? 0) with true in RL by (symmetry; apply Z.eqb_eq; lia). injection RL as <- <-.
        sw [130976; 130568]. all: stb_close K BY jp_.
      + replace (p =? 0) with false in RL by (symmetry; apply Z.eqb_neq; lia).
        assert (L8 : 8 <= zlen bs) by (destruct (Z_lt_le_dec (zlen bs) 8) as [Hl|Hl]; [specialize (BPS Hl); lia | lia]).
        destruct (Z_lt_le_dec (p - b / 8) 0) as [EOB|UNF].
        * replace (p - b / 8 <? 0) with true in RL by (symmetry; apply Z.ltb_lt; lia).
          cbv beta iota zeta in RL. rewrite HufWalkKit.readLE64_ok in RL by lia. cbn [bind] in RL. injection RL as <- <-.
          sw [130976; 130568]. all: stb_close K BY jp_.
        * replace (p - b / 8 <? 0) with false in RL by (symmetry; apply Z.ltb_ge; lia).
          cbv beta iota zeta in RL. rewrite HufWalkKit.readLE64_ok in RL by lia. cbn [bind] in RL. injection RL as <- <-.
          sw [130976; 130568]. all: stb_close K BY jp_.
  Qed.

  (* [comment removed for export] *)
  Lemma stb_rB : forall m1 out s1 s2 d st d' j0 j (x1 x23 x24 x25 x26 x27 x30 x31 : word),
    TIb m1 out s1 s2 d -> bitd_ok bs d -> bd_bits d <= 64 -> reload_dstream bs d = Ok (st, d') ->
    (forall m2 (y23 y24 y25 y28 y29 y30 y31 : word), TIb m2 out s1 s2 d' ->
       evt usegs POST (STH 0x1fe08 m2 x1 j0 j y23 y24 y25 x26 x27 y28 y29 y30 y31)) ->
    evt usegs POST (STH 0x20030 m1 x1 j0 j x23 x24 x25 x26 x27 (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (bd_bits d)) x30 x31).
  Proof using All.
    intros until x31. intros (jp_ & FM) BOK BB RL K.
    pose proof PRE as (HTL & HCELLS & HCOK & BY & LOSP & SP16 & SP47 & HS1 & HS2 & HDT1 & HDT2 & HDT3 & HDST1 & HDST2 & HDST3
                        & DJ1 & DJ2 & DJ3).
    unfold fdw_mem in FM. cbn [de_out de_s1 de_s2 de_bd] in FM.
    destruct FM as (FS2 & FS1 & FBD & ((junk & OUT & LJ) & MU & WM & MI) & TBB & SRC & STK).
    destruct d as [c b p z]. pose proof BOK as (BC & BBR & BP & BPE & BPS & BZI). cbn [bd_cont bd_bits bd_ptr bd_zero] in *.
    assert (Z0 : z = false) by (destruct z; [specialize (BZI eq_refl); lia | reflexivity]). subst z.
    unfold bitdz_cells in FBD. cbn [bd_cont bd_bits bd_ptr bd_zero] in FBD.
    pose proof (bytes_at_bound _ _ _ _ SRC) as BSB. rewrite length_map in BSB.
    assert (P2 : 2 <= 2^(dt_tableLog dt) <= 4096)
      by (split; [change 2 with (2^1); apply Z.pow_le_mono_r; lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]).
    assert (LBS : Z.of_nat (length (map (Z_to_bv 8) bs)) = zlen bs) by (rewrite length_map; reflexivity).
    assert (LTB : Z.of_nat (length (concat (map fse_cell_bytes (dt_cells dt)))) = 4 * 2^(dt_tableLog dt))
      by (rewrite RF_huf_bdt_model.fse_cells_length; lia).
    assert (NB8 : 0 <= b / 8 <= 8) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
    unfold reload_dstream in RL. cbn [bd_cont bd_bits bd_ptr bd_zero] in RL. cbv zeta in RL.
    replace (64 <? b) with false in RL by (symmetry; apply Z.ltb_ge; lia).
    rewrite Z.shiftr_div_pow2 in RL by lia. change (2^3) with 8 in RL.
    destruct (Z_le_gt_dec 8 p) as [FP|FP].
    - replace (8 <=? p) with true in RL by (symmetry; apply Z.leb_le; lia).
      rewrite HufWalkKit.readLE64_ok in RL by lia. cbn [bind] in RL. injection RL as <- <-.
      sw [130568; 130976]. all: stb_close K BY jp_.
    - replace (8 <=? p) with false in RL by (symmetry; apply Z.leb_gt; lia).
      destruct (Z.eq_dec p 0) as [P0|P0].
      + replace (p =? 0) with true in RL by (symmetry; apply Z.eqb_eq; lia). injection RL as <- <-.
        sw [130568; 130976]. all: stb_close K BY jp_.
      + replace (p =? 0) with false in RL by (symmetry; apply Z.eqb_neq; lia).
        assert (L8 : 8 <= zlen bs) by (destruct (Z_lt_le_dec (zlen bs) 8) as [Hl|Hl]; [specialize (BPS Hl); lia | lia]).
        destruct (Z_lt_le_dec (p - b / 8) 0) as [EOB|UNF].
        * replace (p - b / 8 <? 0) with true in RL by (symmetry; apply Z.ltb_lt; lia).
          cbv beta iota zeta in RL. rewrite HufWalkKit.readLE64_ok in RL by lia. cbn [bind] in RL. injection RL as <- <-.
          sw [130568; 130976]. all: stb_close K BY jp_.
        * replace (p - b / 8 <? 0) with false in RL by (symmetry; apply Z.ltb_ge; lia).
          cbv beta iota zeta in RL. rewrite HufWalkKit.readLE64_ok in RL by lia. cbn [bind] in RL. injection RL as <- <-.
          sw [130568; 130976]. all: stb_close K BY jp_.
  Qed.
End STB.
