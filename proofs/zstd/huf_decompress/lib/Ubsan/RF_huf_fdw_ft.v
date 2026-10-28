(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit STRW_tac.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface RF_huf_tbl_iface RF_huf_tbl_kit RF_huf_fdw_kit
  RF_huf_fdw_cut RF_huf_fdw_ftl RF_huf_fdw_fil RF_huf_fdw_kit_dsym RF_huf_fdw_ftb RF_huf_fdw_stl.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac ldt := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  let a := cur_mem_addr in
  lazymatch goal with N : nth_error _ (Z.to_nat ?s) = Some ?c, B : bytes_at usegs mm ?T (concat (map fse_cell_bytes _)) |- _ =>
  let RD := fresh "RDc" in
  first [ pose proof (cell_rd_hi mm T _ s c a B N ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; kn; lia)) as RD; zstep
        | pose proof (cell_rd_sym usegs mm T _ s c a B N ltac:(lia) ltac:(unfold wa; f_equal; kn; lia)) as RD; zstep
        | pose proof (cell_rd_nb usegs mm T _ s c a B N ltac:(lia) ltac:(unfold wa; f_equal; kn; lia)) as RD; zstep
        | pose proof (cell_rd_ns usegs mm T _ s c a B N ltac:(lia) ltac:(unfold wa; f_equal; kn; lia)) as RD; zstep ];
  clear RD end end.

Local Ltac slia ::= slia_sep.

Lemma ft_lor : forall s n w, 0 <= s < 256 -> 0 <= n < 256 -> 0 <= w < 2^16 ->
  Z.lor ((s + 256 * n) * 65536) w = w + 65536 * s + 16777216 * n.
Proof.
  intros s n w Hs Hn Hw. pose proof (cw_lor s n w (2^64) eq_refl Hs Hn Hw) as E.
  rewrite Z.shiftl_mul_pow2, Z.mod_small in E by lia. exact E.
Qed.

Lemma ft_lo : forall s n w, 0 <= s < 256 -> 0 <= n < 256 -> 0 <= w < 2^16 ->
  Z.land (w + 65536 * s + 16777216 * n) 65535 = w.
Proof. intros s n w Hs Hn Hw. apply w_lo; lia. Qed.

Lemma ft_hi16 : forall s n w, 0 <= s < 256 -> 0 <= n < 256 -> 0 <= w < 2^16 ->
  Z.shiftr (w + 65536 * s + 16777216 * n) 16 = s + 256 * n.
Proof. intros s n w Hs Hn Hw. apply w_hi; lia. Qed.

Lemma ft_hi24 : forall s n, 0 <= s < 256 -> 0 <= n < 256 -> Z.shiftr ((s + 256 * n) * 65536) 24 = n.
Proof.
  intros s n Hs Hn. rewrite Z.shiftr_div_pow2 by lia. change (2^24) with 16777216.
  symmetry. apply Z.div_unique with (s * 65536); lia.
Qed.

Lemma ft_sw : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. intros z H. apply FseWalkKit.swrap32_small. lia. Qed.

Lemma ft_lbf : forall c b p z nb, 0 <= b < 2^30 -> 0 <= nb <= 12 ->
  look_bits_fast (mkBD c b p z) nb = Z.shiftr ((c * 2^(b mod 64)) mod 2^64) ((0 - nb) mod 2^64 mod 64).
Proof.
  intros c b p z nb HB HN. unfold look_bits_fast, u64, u32. cbn [bd_cont bd_bits].
  rewrite (Z.mod_small b (2^32)) by lia.
  rewrite Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia).
  f_equal.
  assert (H : nb = 0 \/ nb = 1 \/ nb = 2 \/ nb = 3 \/ nb = 4 \/ nb = 5 \/ nb = 6 \/ nb = 7 \/ nb = 8 \/ nb = 9
              \/ nb = 10 \/ nb = 11 \/ nb = 12) by lia.
  repeat (destruct H as [-> | H]; [reflexivity|]). subst nb. reflexivity.
Qed.

Lemma ft_b8 : forall s n, Z_to_bv 8 (s + 256 * n) = Z_to_bv 8 s.
Proof.
  intros s n. apply byte8_eq. replace (s + 256 * n) with (s + n * 256) by ring. rewrite Z.mod_add by lia. reflexivity.
Qed.

Ltac ft_hn ce b :=
  rewrite ?zx16_lit in * by lia;
  rewrite ?(ft_lor (dc_symbol ce) (dc_nbBits ce) (dc_newState ce)) in * by lia;
  rewrite ?(ft_lo (dc_symbol ce) (dc_nbBits ce) (dc_newState ce)), ?(ft_hi16 (dc_symbol ce) (dc_nbBits ce) (dc_newState ce)),
    ?(ft_hi24 (dc_symbol ce) (dc_nbBits ce)) in * by lia;
  rewrite ?(ft_sw (dc_nbBits ce + b)), ?(ft_sw (0 - dc_nbBits ce)) in * by lia.

Lemma ft_outa : forall m A out s n junk, u8arr usegs m A (map (Z_to_bv 8) (out ++ [s + 256 * n]) ++ junk) ->
  u8arr usegs m A (map (Z_to_bv 8) (out ++ [s]) ++ junk).
Proof. intros m A out s n junk H. rewrite map_app in *. cbn [map] in *. rewrite ft_b8 in H. exact H. Qed.

Ltac ft_setr r v' tac := let v := fi_reg_val r in lazymatch v with Z_to_bv 64 ?e =>
  let E := fresh "E" in assert (E : e = v') by tac; rewrite E in *; clear E end.

Ltac ft_zl := rewrite ?length_app; cbn [length]; lia.

Section FT.
  Variables (SP : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).               (* [comment removed for export] *)
  Variables (S DT DST dcap lo : Z) (bs : list Z) (dt : dtable) (POST : machine_state -> Prop).  (* [comment removed for export] *)
  Hypothesis HPRE : fdw_pre SP S DT DST dcap lo bs dt.
  Hypothesis DSYMF : fse_dsymf_stmt.
  Hypothesis FIN1 : fdw_fin1_stmt.
  Hypothesis FIN2 : fdw_fin2_stmt.

  Lemma ft_ok_dsym : forall s d (k : Z * Z * bitD -> res (list Z)), res_ok (bind (decode_sym dt true s d) k) ->
    0 <= s < 2^(dt_tableLog dt).
  Proof.
    intros s d k H. pose proof HPRE as (_ & TLN & _).
    destruct (decode_sym dt true s d) as [[[o s'] d']| e | |] eqn:E; cbn [bind] in H; try contradiction.
    - destruct (dsym_inv _ _ _ _ _ _ _ E) as (ce & lb & SR & _). lia.
    - exfalso; eapply fi_dsym_not_err; exact E.
  Qed.

  Lemma ft_step2 : forall d s o s' d2 st d2r, bitd_ok bs d -> bd_bits d <= 64 ->
    decode_sym dt true s d = Ok (o, s', d2) -> reload_dstream bs d2 = Ok (st, d2r) ->
    0 <= o < 256 /\ bitd_ok bs d2r /\ bd_bits d2r <= 76 /\ (64 < bd_bits d2 -> dstatus_eqb st Overflow = true)
    /\ (dstatus_eqb st Overflow = false -> bd_zero d2r = false).
  Proof.
    intros d s o s' d2 st d2r BOK BB DS RL. pose proof HPRE as (TL & TLN & COK & BY & _).
    split; [eapply ftb_dsym_o; eassumption|].
    destruct (dsym_inv _ _ _ _ _ _ _ DS) as (ce & lb & SR & NE & -> & -> & -> & LB).
    pose proof (proj1 (Forall_forall _ _) COK ce (nth_error_In _ _ NE)) as (CS & CN & CN0 & CNS).
    pose proof (fi_skip_ok bs d (dc_nbBits ce) BOK ltac:(lia) ltac:(lia)) as (BOK2 & BB2).
    pose proof (fi_reload_facts bs _ st d2r BY BOK2 RL) as (BOKr & BBr & BZr & BOr).
    rewrite BB2 in BBr, BZr, BOr |- *.
    split; [exact BOKr|]. split; [lia|]. split.
    - intro HB. destruct (BOr HB) as (STO & _). destruct st; first [reflexivity | exact (False_ind _ STO)].
    - intro OV. destruct (Z_lt_le_dec 64 (bd_bits d + dc_nbBits ce)) as [GT|LE].
      + destruct (BOr GT) as (STO & _). destruct st; first [discriminate OV | exact (False_ind _ STO)].
      + exact (proj1 (BZr LE)).
  Qed.

  Notation TS pc mm j0 j s1 s2 b P c x1 x24 x25 x26 x27 :=
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 s1) (Z_to_bv 64 s2) (Z_to_bv 64 b) (Z_to_bv 64 DST) (Z_to_bv 64 (DST + j0))
             (Z_to_bv 64 (-70)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 S) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4))
             (Z_to_bv 64 (2^61)) (Z_to_bv 64 65535) (Z_to_bv 64 P) (Z_to_bv 64 (DST + j + 1)) (Z_to_bv 64 (j0 - j))
             (Z_to_bv 64 64) (Z_to_bv 64 1) (Z_to_bv 64 (-1)) (Z_to_bv 64 (DST + j)) x24 x25 x26 x27 (Z_to_bv 64 c)
             (Z_to_bv 64 (DST + dcap - 2)) (Z_to_bv 64 1) (Z_to_bv 64 2))
        F (Z_to_bv 64 (PFSE_DECOMP + pc)) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition ft_b2 (f : nat) (out1 : list Z) (s1a s2 : Z) (d1r : bitD) : res (list Z) :=
    if dcap - 2 <? FseNCount.Zlength out1 then Err ZSTD_error_dstSize_tooSmall
    else
      let! q2 := decode_sym dt true s2 d1r in let '(o1, s2a, d2) := q2 in
      let! r2 := reload_dstream bs d2 in let '(st2, d2r) := r2 in
      if dstatus_eqb st2 Overflow then
        let! q3 := decode_sym dt true s1a d2r in let '(o2, _, _) := q3 in
        Ok (out1 ++ [o1; o2])
      else tail_loop bs dt dcap true f (mkDec (out1 ++ [o1]) s1a s2a d2r).

  (* [comment removed for export] *)
  Lemma ft_tail_S : forall f x, tail_loop bs dt dcap true (Datatypes.S f) x =
    if dcap - 2 <? FseNCount.Zlength (de_out x) then Err ZSTD_error_dstSize_tooSmall
    else
      let! q1 := decode_sym dt true (de_s1 x) (de_bd x) in let '(o0, s1a, d1) := q1 in
      let! r1 := reload_dstream bs d1 in let '(st1, d1r) := r1 in
      if dstatus_eqb st1 Overflow then
        let! q2 := decode_sym dt true (de_s2 x) d1r in let '(o1, _, _) := q2 in
        Ok (de_out x ++ [o0; o1])
      else ft_b2 f (de_out x ++ [o0]) s1a (de_s2 x) d1r.
  Proof. intros f x. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition ft_mid_stmt (f : nat) : Prop :=
    forall out j0 j s1 s2 d m1 jp (x1 x24 x25 x26 x27 : word),
      res_ok (ft_b2 f out s1 s2 d) -> fdw_K SP gp tp F fc m0 DST dcap lo POST (ft_b2 f out s1 s2 d) ->
      bitd_ok bs d -> bd_bits d <= 64 -> bd_zero d = false -> zlen out <= dcap -> Forall (fun c => 0 <= c < 256) out ->
      0 <= j0 <= j -> zlen out = j + 1 ->
      fdw_fmem m0 m1 SP S DT DST dcap lo bs dt (mkDec out s1 s2 d) jp ->
      evt usegs POST (TS 4064 m1 j0 j s1 s2 (bd_bits d) (S + bd_ptr d) (bd_cont d) x1 x24 x25 x26 x27).

  (* [comment removed for export] *)
  Definition ft_head_stmt (f : nat) : Prop :=
    forall out j0 s1 s2 d m1 jp (x1 x24 x25 x26 x27 : word),
      res_ok (tail_loop bs dt dcap true (Datatypes.S f) (mkDec out s1 s2 d)) ->
      fdw_K SP gp tp F fc m0 DST dcap lo POST (tail_loop bs dt dcap true (Datatypes.S f) (mkDec out s1 s2 d)) ->
      sm_okr dcap bs (mkDec out s1 s2 d) -> 0 <= j0 <= zlen out -> zlen out + 2 <= dcap ->
      fdw_fmem m0 m1 SP S DT DST dcap lo bs dt (mkDec out s1 s2 d) jp ->
      evt usegs POST (TS 3724 m1 j0 (zlen out) s1 s2 (bd_bits d) (bd_reg S d) (bd_cont d) x1 x24 x25 x26 x27).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition ft_j2_stmt (f : nat) : Prop :=
    forall out j0 j s1 s2 d m1 jp (x1 x24 x25 x26 x27 : word),
      res_ok (tail_loop bs dt dcap true f (mkDec out s1 s2 d)) ->
      fdw_K SP gp tp F fc m0 DST dcap lo POST (tail_loop bs dt dcap true f (mkDec out s1 s2 d)) ->
      sm_okr dcap bs (mkDec out s1 s2 d) -> bd_zero d = false -> 0 <= j0 <= j -> zlen out = j + 2 ->
      fdw_fmem m0 m1 SP S DT DST dcap lo bs dt (mkDec out s1 s2 d) jp ->
      evt usegs POST (TS 3704 m1 j0 j s1 s2 (bd_bits d) (S + bd_ptr d) (bd_cont d) x1 x24 x25 x26 x27).

  Lemma ft_head : forall f, ft_j2_stmt f -> ft_head_stmt f.
  Proof.
    intros f J2 out j0 s1 s2 [c b p z] m1 jp x1 x24 x25 x26 x27 ROK K OK HJ HJC FM. unfold ft_j2_stmt in J2.
    pose proof HPRE as (TL & TLN & COK & BY & LOS & SPA & SPH & S8 & SL & DT0 & DTA & DTL & DST4 & DSTL & DCAP & DJ1 & DJ2 & DJ3).
    pose proof (proj1 OK) as BOK. cbn [de_bd] in BOK.
    destruct OK as ((B0 & B1 & B2 & B3 & B4 & B5) & B29 & HO & OBY). cbn [de_bd de_out de_s1 de_s2 bd_cont bd_bits bd_ptr bd_zero] in *.
    destruct FM as ((junk & OUTA & LJ) & (fb & fp & FR) & MU & WM & MI & TBB & SRC & STK). cbn [de_out de_s1 de_s2 de_bd bd_cont] in *.
    rewrite ft_tail_S in ROK, K. cbn [de_out de_s1 de_s2 de_bd] in ROK, K. unfold FseNCount.Zlength in ROK, K.
    destruct (Z.ltb_spec (dcap - 2) (zlen out)) as [SZ|SZ]; [lia|].
    destruct (decode_sym dt true s1 (mkBD c b p z)) as [[[o0 s1a] d1]| e | |] eqn:DSY; cbn [bind] in ROK, K;
      [| exfalso; eapply fi_dsym_not_err; exact DSY | contradiction | contradiction].
    destruct (dsym_inv _ _ _ _ _ _ _ DSY) as (ce & lb & SR & NE & -> & -> & -> & LB). cbv iota in LB. subst lb.
    pose proof (proj1 (Forall_forall _ _) COK ce (nth_error_In _ _ NE)) as CK. cbv beta in CK.
    destruct CK as (CS & CN & CN0 & CNS).
    assert (P2 : 2 <= 2^(dt_tableLog dt) <= 4096)
      by (split; [change 2 with (2^1); apply Z.pow_le_mono_r; lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]).
    assert (NP : 1 <= 2^(dc_nbBits ce)) by (change 1 with (2^0); apply Z.pow_le_mono_r; lia).
    assert (NSB : 0 <= dc_newState ce < 2^16) by lia.
    assert (NBB : 0 <= dc_nbBits ce <= 12) by lia.
    pose proof (fi_skip_ok bs (mkBD c b p z) (dc_nbBits ce) BOK B29 NBB) as (BOK1 & BB1).
    unfold skip_bits in ROK, K, BOK1, BB1. cbn [bd_cont bd_bits bd_ptr bd_zero] in ROK, K, BOK1, BB1. rewrite BB1 in ROK, K, BOK1.
    destruct (reload_dstream bs (mkBD c (b + dc_nbBits ce) p z)) as [[st1 d1r]| e | |] eqn:RL; cbn [bind] in ROK, K;
      [| exfalso; eapply reload_not_err; exact RL | contradiction | contradiction].
    pose proof (fi_reload_facts bs _ _ _ BY BOK1 RL) as (BOKr & BBr & BZr & BOr). cbn [bd_bits bd_cont bd_ptr bd_zero] in BBr, BZr, BOr.
    pose proof (bytes_at_bound _ _ _ _ SRC) as BSB. rewrite length_map in BSB.
    assert (LBS : Z.of_nat (length (map (Z_to_bv 8) bs)) = zlen bs) by (rewrite length_map; reflexivity).
    assert (LTB : Z.of_nat (length (concat (map fse_cell_bytes (dt_cells dt)))) = 4 * 2^(dt_tableLog dt))
      by (rewrite RF_huf_bdt_model.fse_cells_length; lia).
    assert (HJ1 : hsep (DST + dcap <= DT \/ DT + 4 + 4 * 2^(dt_tableLog dt) <= DST)) by exact DJ1.
    assert (HJ2 : hsep (DST + dcap <= S \/ S + zlen bs <= DST)) by exact DJ2.
    repeat (first [fi_chk | fi_uimref | ldt | osh | fi_notin [PFSE_DECOMP + 3608; PFSE_DECOMP + 3828; PFSE_DECOMP + 4408]; fi_notuim; fi_notcallee; zstep; fi_norm]).
    all: ft_hn ce b.
    all: ft_setr 5%Z (dc_newState ce + look_bits_fast (mkBD c b p z) (dc_nbBits ce))
           ltac:(rewrite ft_lbf by lia; rewrite Z.add_comm; reflexivity).
    all: ft_setr 7%Z (b + dc_nbBits ce) ltac:(lia).
    all: fi_setreg 15%Z (Z_to_bv 64 (2^61)) ltac:(f_equal; reflexivity).
    all: rewrite ?(Z.mod_small (b + dc_nbBits ce)) in * by lia.
    all: match goal with H : u8arr _ _ DST _ |- _ => apply ft_outa in H end.
    - match goal with H : 64 < b + dc_nbBits ce |- _ => destruct (BOr H) as (STO & ->) end.
      assert (OV : dstatus_eqb st1 Overflow = true) by (destruct st1; first [reflexivity | exact (False_ind _ STO)]).
      rewrite OV in ROK, K.
      destruct (decode_sym dt true s2 (mkBD c (b + dc_nbBits ce) p true)) as [[[o1 s2x] d2x]| e | |] eqn:DS2;
        cbn [bind] in ROK, K; [| exfalso; eapply fi_dsym_not_err; exact DS2 | contradiction | contradiction].
      replace (out ++ [dc_symbol ce; o1]) with ((out ++ [dc_symbol ce]) ++ [o1]) in K by (rewrite <- app_assoc; reflexivity).
      eapply ftb_finA with (out := out ++ [dc_symbol ce]) (j := zlen out)
        (s1 := dc_newState ce + look_bits_fast (mkBD c b p z) (dc_nbBits ce)) (s2 := s2)
        (d := mkBD c (b + dc_nbBits ce) p z) (o := o1) (s' := s2x) (d' := d2x).
      all: cbn [bd_bits bd_cont bd_ptr bd_zero].
      all: try first [ exact HPRE | exact DSYMF | exact FIN1 | exact DS2 | exact K | ft_zl | lia ].
      all: try (unfold ftb_mem; refine (conj (ex_intro _ (tl junk) (conj _ _)) (conj (ex_intro _ fp _)
                  (conj _ (conj _ (conj _ (conj _ (conj _ _)))))));
                first [ eassumption | (destruct junk as [|jb junk']; cbn [tl length] in *; [lia | ft_zl]) ]).
    - destruct z; [exfalso; specialize (B5 eq_refl); lia |].
      destruct (BZr ltac:(lia)) as (BZ1 & STO).
      assert (OV : dstatus_eqb st1 Overflow = false) by (destruct st1; first [reflexivity | exact (False_ind _ STO)]).
      rewrite OV in ROK, K.
      eapply ftb_rA with (out := out ++ [dc_symbol ce]) (j := zlen out)
        (s1 := dc_newState ce + look_bits_fast (mkBD c b p false) (dc_nbBits ce)) (s2 := s2)
        (d := mkBD c (b + dc_nbBits ce) p false) (d' := d1r) (st := st1) (m0 := m0).
      all: cbn [bd_bits bd_cont bd_ptr bd_zero].
      all: try first [ exact HPRE | exact RL | exact BOK1 | ft_zl | lia ].
      all: try (unfold fdw_fmem; cbn [de_out de_s1 de_s2 de_bd bd_cont];
                refine (conj (ex_intro _ (tl junk) (conj _ _)) (conj (ex_intro _ (Z_to_bv 64 (b + dc_nbBits ce)) (ex_intro _ fp _))
                  (conj _ (conj _ (conj _ (conj _ (conj _ _)))))));
                first [ eassumption | (destruct junk as [|jb junk']; cbn [tl length] in *; [lia | ft_zl]) ]).
      intros m2 jp2 y1 y24 y25 y26 y27 FM2.
      assert (OBY1 : Forall (fun c0 => 0 <= c0 < 256) (out ++ [dc_symbol ce]))
        by (apply Forall_app; split; [exact OBY | constructor; [lia | constructor]]).
      eapply ftb_mid with (out := out ++ [dc_symbol ce]) (j := zlen out)
        (s1 := dc_newState ce + look_bits_fast (mkBD c b p false) (dc_nbBits ce)) (s2 := s2) (d := d1r).
      all: try first [ exact HPRE | exact DSYMF | exact FIN2 | exact BOKr | exact BZ1 | exact FM2 | exact OBY1 | ft_zl | lia ].
      + intro SZ2. unfold ft_b2 in ROK. unfold FseNCount.Zlength in ROK.
        rewrite (proj2 (Z.ltb_ge (dcap - 2) (zlen (out ++ [dc_symbol ce]))) ltac:(lia)) in ROK. exact (ft_ok_dsym _ _ _ ROK).
      + intro SZ2. unfold ft_b2 in K. unfold FseNCount.Zlength in K. rewrite (proj2 (Z.ltb_lt _ _) SZ2) in K. exact K.
      + intros o1 s2a d2 st2 d2r SZ2 DS2 RL2.
        unfold ft_b2 in ROK, K. unfold FseNCount.Zlength in ROK, K. rewrite (proj2 (Z.ltb_ge (dcap - 2) (zlen (out ++ [dc_symbol ce]))) ltac:(lia)) in ROK, K.
        rewrite DS2 in ROK, K. cbn [bind] in ROK, K. rewrite RL2 in ROK, K. cbn [bind] in ROK, K.
        destruct (ft_step2 _ _ _ _ _ _ _ BOKr ltac:(lia) DS2 RL2) as (O1 & BOK2 & BB2 & OVT & ZF).
        split; [|split].
        * intro HB. specialize (OVT HB). rewrite OVT in ROK. exact (ft_ok_dsym _ _ _ ROK).
        * intros OV2 o2 s' d' DS3. rewrite OV2 in K. rewrite DS3 in K. cbn [bind] in K. exact K.
        * intros OV2 m3 jp3 z1 z24 z25 z26 z27 FM3. rewrite OV2 in ROK, K.
          eapply J2; [exact ROK | exact K | | exact (ZF OV2) | lia | ft_zl | exact FM3].
          unfold sm_okr; cbn [de_bd de_out]. split; [exact BOK2|]. split; [lia|]. split; [ft_zl|].
          apply Forall_app; split; [exact OBY1 | constructor; [lia | constructor]].
  Qed.

  Ltac ft_exit K := eapply K; [eassumption | eassumption | eassumption | eassumption |
    cbn [dres]; split; [reflexivity | first [lia | unfold ZSTD_error_dstSize_tooSmall; lia | split; vm_compute; reflexivity]]].

  Lemma ft_j2_0 : ft_j2_stmt O.
  Proof. intros out j0 j s1 s2 d m1 jp x1 x24 x25 x26 x27 ROK. exact (False_ind _ ROK). Qed.

  Lemma ft_j2_S : forall f, ft_head_stmt f -> ft_j2_stmt (Datatypes.S f).
  Proof.
    intros f HD out j0 j s1 s2 [c b p z] m1 jp x1 x24 x25 x26 x27 ROK K OK ZF HJ HJ2 FM. unfold ft_head_stmt in HD.
    cbn [bd_zero bd_bits bd_ptr bd_cont] in ZF. subst z.
    pose proof OK as OK0. pose proof FM as FM0.
    destruct OK as ((B0 & B1 & B2 & B3 & B4 & B5) & B29 & HO & OBY). cbn [de_bd de_out de_s1 de_s2 bd_cont bd_bits bd_ptr bd_zero] in *.
    pose proof HPRE as (TL & TLN & COK & BY & LOS & SPA & SPH & S8 & SL & DT0 & DTA & DTL & DST4 & DSTL & DCAP & DJ1 & DJ2 & DJ3).
    destruct FM as ((junk & OUTA & LJ) & (fb & fp & FR) & MU & WM & MI & TBB & SRC & STK). cbn [de_out de_s1 de_s2 de_bd bd_cont] in *.
    assert (P2 : 2 <= 2^(dt_tableLog dt) <= 4096)
      by (split; [change 2 with (2^1); apply Z.pow_le_mono_r; lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]).
    pose proof (bytes_at_bound _ _ _ _ SRC) as BSB. rewrite length_map in BSB.
    assert (LBS : Z.of_nat (length (map (Z_to_bv 8) bs)) = zlen bs) by (rewrite length_map; reflexivity).
    assert (LTB : Z.of_nat (length (concat (map fse_cell_bytes (dt_cells dt)))) = 4 * 2^(dt_tableLog dt))
      by (rewrite RF_huf_bdt_model.fse_cells_length; lia).
    assert (HJ1 : hsep (DST + dcap <= DT \/ DT + 4 + 4 * 2^(dt_tableLog dt) <= DST)) by exact DJ1.
    assert (HJ2' : hsep (DST + dcap <= S \/ S + zlen bs <= DST)) by exact DJ2.
    assert (EJ : j = zlen out - 2) by lia. subst j.
    repeat (first [fi_chk | fi_uimref | fi_notin [PFSE_DECOMP + 3608; PFSE_DECOMP + 3724]; fi_notuim; fi_notcallee; zstep; fi_norm]).
    - rewrite ft_tail_S in K. cbn [de_out de_s1 de_s2 de_bd] in K. unfold FseNCount.Zlength in K.
      rewrite (proj2 (Z.ltb_lt (dcap - 2) (zlen out)) ltac:(lia)) in K.
      ft_exit K.
    - fi_setreg 15%Z (Z_to_bv 64 (2^61)) ltac:(f_equal; reflexivity).
      ft_setr 18%Z (DST + zlen out + 1) ltac:(lia).
      ft_setr 19%Z (j0 - zlen out) ltac:(lia).
      ft_setr 23%Z (DST + zlen out) ltac:(lia).
      eapply HD with (out := out) (j0 := j0) (s1 := s1) (s2 := s2) (d := mkBD c b p false);
        [exact ROK | exact K | exact OK0 | lia | lia | exact FM0].
  Qed.

  Lemma ft_t2 : (forall f, ft_head_stmt f) -> forall f x r, tail_loop bs dt dcap true f x = r -> res_ok r ->
    fdw_K SP gp tp F fc m0 DST dcap lo POST r -> fdw_t2_K SP gp tp F fc m0 S DT DST dcap lo bs dt POST x.
  Proof.
    intros HALL f [out s1 s2 [c b p z]] r TLr ROK K m1 jp y1 y10 y19 y20 y21 y22 y23 y24 y25 y26 y27 y29 y30 y31 OK STO FM.
    subst r. destruct f as [|f]; [exact (False_ind _ ROK)|].
    pose proof OK as OK0. pose proof FM as FM0.
    cbn [de_bd de_out de_s1 de_s2 bd_cont bd_bits bd_ptr bd_zero] in OK, STO, FM |- *.
    destruct OK as ((B0 & B1 & B2 & B3 & B4 & B5) & B29 & HO & OBY). cbn [de_bd de_out de_s1 de_s2 bd_cont bd_bits bd_ptr bd_zero] in *.
    pose proof HPRE as (TL & TLN & COK & BY & LOS & SPA & SPH & S8 & SL & DT0 & DTA & DTL & DST4 & DSTL & DCAP & DJ1 & DJ2 & DJ3).
    destruct FM as ((junk & OUTA & LJ) & (fb & fp & FR) & MU & WM & MI & TBB & SRC & STK). cbn [de_out de_s1 de_s2 de_bd bd_cont] in *.
    assert (P2 : 2 <= 2^(dt_tableLog dt) <= 4096)
      by (split; [change 2 with (2^1); apply Z.pow_le_mono_r; lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]).
    pose proof (bytes_at_bound _ _ _ _ SRC) as BSB. rewrite length_map in BSB.
    assert (LBS : Z.of_nat (length (map (Z_to_bv 8) bs)) = zlen bs) by (rewrite length_map; reflexivity).
    assert (LTB : Z.of_nat (length (concat (map fse_cell_bytes (dt_cells dt)))) = 4 * 2^(dt_tableLog dt))
      by (rewrite RF_huf_bdt_model.fse_cells_length; lia).
    assert (HJ1 : hsep (DST + dcap <= DT \/ DT + 4 + 4 * 2^(dt_tableLog dt) <= DST)) by exact DJ1.
    assert (HJ2' : hsep (DST + dcap <= S \/ S + zlen bs <= DST)) by exact DJ2.
    unfold PFDW_T2.
    repeat (first [fi_chk | fi_uimref | fi_notin [PFSE_DECOMP + 3608; PFSE_DECOMP + 3724]; fi_notuim; fi_notcallee; zstep; fi_norm]).
    - fi_setreg 15%Z (Z_to_bv 64 (2^61)) ltac:(f_equal; reflexivity).
      fi_setreg 19%Z (Z_to_bv 64 (zlen out - zlen out)) ltac:(f_equal; lia).
      fi_setreg 21%Z (Z_to_bv 64 1) ltac:(f_equal; rewrite (proj2 (Z.ltb_lt 0 (DT + 4)) ltac:(lia)); reflexivity).
      fi_setreg 29%Z (Z_to_bv 64 (DST + dcap - 2)) ltac:(f_equal; lia).
      eapply (HALL f) with (out := out) (j0 := zlen out) (s1 := s1) (s2 := s2) (d := mkBD c b p z);
        [exact ROK | exact K | exact OK0 | lia | lia | exact FM0].
    - rewrite ft_tail_S in K. cbn [de_out de_s1 de_s2 de_bd] in K. unfold FseNCount.Zlength in K.
      rewrite (proj2 (Z.ltb_lt (dcap - 2) (zlen out)) ltac:(lia)) in K.
      ft_exit K.
  Qed.

  Lemma ft_j2_all : forall f, ft_j2_stmt f.
  Proof. induction f as [|f IH]; [exact ft_j2_0 | apply ft_j2_S, ft_head, IH]. Qed.

  Lemma ft_head_all : forall f, ft_head_stmt f.
  Proof. intro f. apply ft_head, ft_j2_all. Qed.
End FT.

Theorem fdw_t2_proof : fdw_fin1_stmt -> fdw_fin2_stmt -> fdw_t2_stmt.
Proof.
  intros FIN1 FIN2 SP gp tp F fc m0 S DT DST dcap lo bs dt POST f x r HPRE TLr ROK K.
  eapply ft_t2.
  all: first [ exact HPRE | exact fse_dsymf_proof | exact FIN1 | exact FIN2 | exact TLr | exact ROK | exact K
             | intro f'; eapply ft_head_all; first [exact HPRE | exact fse_dsymf_proof | exact FIN1 | exact FIN2] ].
Qed.
