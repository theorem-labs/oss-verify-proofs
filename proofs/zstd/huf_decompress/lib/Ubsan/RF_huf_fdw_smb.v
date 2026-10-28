From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Step MState.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem HufWalkKit STRW_tac.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface RF_huf_tbl_iface RF_huf_tbl_kit RF_huf_bdt_model
  RF_huf_fdw_kit RF_huf_y4_kit_reload RF_huf_fdw_kit_dsym RF_huf_fdw_cut.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition PFDW_L1D : Z := 0x1fbd8.

Definition fdw_l1d_stmt : Prop :=
  forall (SP : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 m1 : fmem) (S DT DST dcap lo : Z) (bs : list Z)
         (dt : dtable) (POST : machine_state -> Prop) (jp : list byte)
         (out : list Z) (s1 s2 : Z) (d0 : bitD) (o0 s1a o1 s2a o2 s1b o3 s2b : Z) (d1 d2 d3 d4 : bitD)
         (y1 y24 y25 y26 y27 y28 : word),
  fdw_pre SP S DT DST dcap lo bs dt ->
  decode_sym dt false s1 d0 = Ok (o0, s1a, d1) -> decode_sym dt false s2 d1 = Ok (o1, s2a, d2) ->
  decode_sym dt false s1a d2 = Ok (o2, s1b, d3) -> decode_sym dt false s2a d3 = Ok (o3, s2b, d4) ->
  sm_ok dcap bs (mkDec out s1 s2 d0) -> st_ok (dt_tableLog dt) (mkDec out s1 s2 d0) -> zlen out + 4 <= dcap ->
  fdw_mem m0 m1 SP S DT DST dcap lo bs dt (mkDec out s1 s2 d0) jp ->
  (bd_bits d4 <= 64 ->
     fdw_l1_K SP gp tp F fc m0 S DT DST dcap lo bs dt POST (mkDec (out ++ [o0; o1; o2; o3]) s1b s2b d4)) ->
  (64 < bd_bits d4 ->
     fdw_t1_K SP gp tp F fc m0 S DT DST dcap lo bs dt POST
       (mkDec (out ++ [o0; o1; o2; o3]) s1b s2b (mkBD (bd_cont d4) (bd_bits d4) (bd_ptr d4) true))) ->
  evt usegs POST (MS (mkR y1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 (-4)) (Z_to_bv 64 (-5)) (Z_to_bv 64 64)
                          (Z_to_bv 64 DST) (Z_to_bv 64 (2^61)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (DT + 4))
                          (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 S)
                          (Z_to_bv 64 (S + bd_ptr d0)) (Z_to_bv 64 (-3)) (Z_to_bv 64 (DST + dcap))
                          (Z_to_bv 64 65535) (Z_to_bv 64 BIT_MASK_TAB) (Z_to_bv 64 (DST + zlen out))
                          (Z_to_bv 64 (DST + dcap - 3)) (Z_to_bv 64 (bd_bits d0)) y24 y25 y26 y27 y28
                          (Z_to_bv 64 s2) (Z_to_bv 64 s1) (Z_to_bv 64 (bd_cont d0)))
                      F (Z_to_bv 64 PFDW_L1D) fc None m1 (seg_rom usegs)).

Lemma l1d_byte : forall sy nb ns, 0 <= sy < 256 -> 0 <= nb < 256 -> 0 <= ns < 65536 ->
  Z_to_bv 8 (Z.shiftr (ns + 65536 * sy + 16777216 * nb) 16) = Z_to_bv 8 sy.
Proof.
  intros sy nb ns A B C. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  rewrite Z.shiftr_div_pow2 by lia. change (2^16) with 65536.
  replace ((ns + 65536 * sy + 16777216 * nb) / 65536) with (sy + nb * 256) by (apply Z.div_unique with ns; lia).
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma l1d_munch_sym : forall W (m m' : fmem), munch W m m' -> munch W m' m.
Proof. intros W m m' H x O. symmetry. exact (H x O). Qed.

Lemma l1d_land_lt : forall x n, 0 <= n -> 0 <= x -> 0 <= Z.land x (2^n - 1) < 2^n.
Proof.
  intros x n H Hx. replace (2^n - 1) with (Z.ones n) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.

Section L1D.
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m0 : fmem) (S DT DST dcap lo : Z) (bs : list Z) (dt : dtable).
  Variable POST : machine_state -> Prop.
  Variable SP : Z.
  Notation TB := (DT + 4).
  Notation tl := (dt_tableLog dt).
  Hypothesis HPRE : fdw_pre SP S DT DST dcap lo bs dt.
  Hypothesis HTL : 1 <= tl <= 12.
  Hypothesis HCELLS : zlen (dt_cells dt) = 2^tl.
  Hypothesis HCOK : cells_ok tl (dt_cells dt).
  Hypothesis TBB : bytes_at usegs m0 TB (concat (map fse_cell_bytes (dt_cells dt))).
  Hypothesis SRC : bytes_at usegs m0 S (map (Z_to_bv 8) bs).
  Hypothesis BY : Forall (fun c => 0 <= c < 256) bs.
  Hypothesis HS : 8 <= S /\ S + Z.max 8 (zlen bs) + 8 <= 2^64.
  Hypothesis HTB : 0 < TB /\ TB + 4 * 2^tl <= 2^64.
  Hypothesis HDST : 3 <= DST /\ DST + dcap < 2^64 /\ 0 <= dcap <= 255.
  Hypothesis DJ1 : DST + dcap <= TB \/ TB + 4 * 2^tl <= DST.
  Hypothesis DJ2 : DST + dcap <= S \/ S + zlen bs <= DST.
  Hypothesis HSPV : 8 <= SP /\ SP + 192 <= 2^47.
  Hypothesis DJF : DST + dcap <= SP /\ S + zlen bs <= SP /\ TB + 4 * 2^tl <= SP.
  Definition sm_box (P : Prop) : Prop := P.

  Lemma sm_lo16 : forall sy nb ns, 0 <= sy < 256 -> 0 <= nb < 256 -> 0 <= ns < 65536 ->
    Z.land (ns + 65536 * sy + 16777216 * nb) 65535 = ns.
  Proof.
    intros sy nb ns A B C. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. change (2^16) with 65536.
    symmetry. apply (Z.mod_unique _ _ (sy + 256 * nb)); lia.
  Qed.

  Lemma sm_sw : forall n b, 0 <= n + b < 18446744073709551616 ->
    bv_swrap 32 (0 - (n + b) mod 18446744073709551616) = bv_swrap 32 (0 - (b + n)).
  Proof.
    intros n b H. rewrite Z.mod_small by lia. rewrite (Z.add_comm n b). reflexivity.
  Qed.

  Ltac sm_nrm := fd_zx; rewrite ?fd_nb in * by lia; rewrite ?fd_w in * by lia; rewrite ?sm_lo16 in * by lia;
    rewrite ?sm_sw in * by lia; rewrite ?fd_land in * by lia.
  Ltac sm_fix c B E :=
    sm_nrm;
    try replace (dc_nbBits c + B) with (B + dc_nbBits c) in * by lia;
    lazymatch type of E with ?sn = ?ns + ?L => replace (L + ns) with sn in * by (rewrite E; ring) end;
    clear E.

  Lemma dec_inv : forall s d o s' d', decode_sym dt false s d = Ok (o, s', d') -> 0 <= bd_bits d <= 2^30 ->
    exists c, nth_error (dt_cells dt) (Z.to_nat s) = Some c /\ 0 <= s < 2^tl
      /\ 0 <= dc_symbol c < 256 /\ 0 <= dc_nbBits c <= tl /\ 0 <= dc_newState c /\ dc_newState c + 2^(dc_nbBits c) <= 2^tl
      /\ o = dc_symbol c
      /\ s' = dc_newState c + Z.land (Z.shiftr (bd_cont d) ((bv_swrap 32 (0 - (bd_bits d + dc_nbBits c)) mod 18446744073709551616) mod 64))
                                    (2^(dc_nbBits c) - 1)
      /\ d' = mkBD (bd_cont d) (bd_bits d + dc_nbBits c) (bd_ptr d) (bd_zero d).
  Proof.
    intros s d o s' d' H HB.
    destruct (dsym_inv dt false s d o s' d' H) as (c & lb & HS1 & NE & Eo & Es & Ed & LB).
    pose proof HCOK as HC. unfold cells_ok in HC.
    pose proof (proj1 (Forall_forall _ _) HC c (nth_error_In _ _ NE)) as (C1 & C2 & C3 & C4).
    rewrite lookbits_mach in LB by lia. injection LB as <-.
    exists c. subst o s' d'. unfold skip_bits, u32. rewrite (Z.mod_small (bd_bits d + dc_nbBits c)) by lia.
    repeat split; try lia; assumption.
  Qed.

  Ltac sm_eqz := fd_zx; rewrite ?fd_nb by lia; rewrite ?fd_nbd by lia; rewrite ?Z.shiftl_mul_pow2 by lia; lia.
  Ltac sm_tb := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with
    | T : bytes_at usegs mm TB _ |- _ => idtac
    | MU : munch _ m0 mm, DB : sm_box (DST + dcap <= TB \/ _) |- _ =>
        let T := fresh "TBM" in
        assert (T : bytes_at usegs mm TB (concat (map fse_cell_bytes (dt_cells dt))))
          by (apply (bytes_at_transport usegs _ m0 mm TB _ TBB MU); rewrite fse_cells_length; cbn [disjoint_from];
              unfold sm_box in DB; lia)
    end end.
  Ltac sm_rd := sm_tb; lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let a := cur_mem_addr in
    first [
      match goal with T : bytes_at usegs mm TB _, NE : nth_error (dt_cells dt) (Z.to_nat ?s) = Some ?c |- _ =>
        let R := fresh "RD" in
        pose proof (cell_rd_ns usegs mm TB (dt_cells dt) s c a T NE ltac:(lia) ltac:(unfold wa; f_equal; sm_eqz)) as R
      end
    | match goal with T : bytes_at usegs mm TB _, NE : nth_error (dt_cells dt) (Z.to_nat ?s) = Some ?c |- _ =>
        let R := fresh "RD" in
        pose proof (cell_rd_off usegs mm TB (dt_cells dt) s c 2 2%nat T NE ltac:(lia) ltac:(lia) ltac:(lia)) as R;
        change (Z.to_nat 2) with 2%nat in R; unfold fse_cell_bytes, le2 in R; cbn [firstn skipn app Z_to_le_bytes] in R;
        rewrite <- (le2_two_bytes (dc_symbol c) (dc_nbBits c)) in R by lia;
        replace (wa (TB + (4 * s + 2))) with a in R by (unfold wa; f_equal; sm_eqz)
      end
    | match goal with MI : mem_inv usegs mm, NE : nth_error (dt_cells dt) (Z.to_nat ?s) = Some ?c |- _ =>
        let R := fresh "RD" in
        pose proof (mask_rd mm (dc_nbBits c) MI ltac:(lia)) as R;
        replace (Z_to_bv 64 (BIT_MASK_TAB + 4 * dc_nbBits c)) with a in R by (f_equal; unfold BIT_MASK_TAB; sm_eqz)
      end ] end.
  Ltac sm_step stop := repeat (lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x20828) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1fac8) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1fdd0) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 stop) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => first [zstep | sm_rd; zstep] end).
  Ltac sm_lx := repeat match goal with H : context [Z.lxor ?a ?b] |- _ =>
    let a' := eval vm_compute in a in is_Zlit a'; let b' := eval vm_compute in b in is_Zlit b';
    let v := eval vm_compute in (Z.lxor a' b') in change (Z.lxor a b) with v in H end.
  Ltac sm_ref := try (exfalso; fd_clr; unfold BIT_MASK_TAB in *; sm_lx; fd_zx; rewrite ?fd_nb in * by lia;
    rewrite ?fd_nbd in * by lia; rewrite ?fd_x4 in * by lia; rewrite ?Z.shiftl_mul_pow2 in * by lia; lia).
  Ltac sm_walk stop := sm_step stop; repeat (fd_brk; sm_ref; sm_step stop).

  (* [comment removed for export] *)
  Ltac osb OUTA LJ OL :=
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


  Ltac l1d_ob OUTA c :=
    rewrite map_app in OUTA; cbn [map] in OUTA;
    let LB := fresh "LB" in
    pose proof (l1d_byte (dc_symbol c) (dc_nbBits c) (dc_newState c) ltac:(lia) ltac:(lia) ltac:(lia)) as LB;
    rewrite LB in OUTA; clear LB;
    change ([Z_to_bv 8 (dc_symbol c)]) with (map (Z_to_bv 8) [dc_symbol c]) in OUTA;
    rewrite <- map_app in OUTA.

  Notation W := [(SP + 16, SP + 88); (DST, DST + dcap)].

  Ltac l1d_n27 := match goal with |- context [Z.b2z (?a mod ?M <? 1)] =>
    replace (Z.b2z (a mod M <? 1)) with 0
      by (rewrite ?Z.shiftl_mul_pow2 by lia; change (2^2) with 4; rewrite Z.mod_small by lia;
          rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity) end.
  Ltac l1d_n28 := match goal with |- context [Z.lxor (BIT_MASK_TAB mod ?M) ?N] =>
    replace (Z.lxor (BIT_MASK_TAB mod M) N) with (18446744073709551615 - BIT_MASK_TAB)
      by (unfold BIT_MASK_TAB; vm_compute; reflexivity) end.

  Lemma l1d_d1 : forall (m m1 : fmem) (out : list Z) (junk : list byte) (s1 s2 B C P j0 : Z) (jp : list byte)
      (o s' : Z) (d' : bitD) (x1 x24 x25 x26 x27 x28 : word),
    decode_sym dt false s1 (mkBD C B P false) = Ok (o, s', d') ->
    0 <= s1 < 2^tl -> 0 <= s2 < 2^tl -> 0 <= B <= 100 -> 0 <= C < 2^64 -> 0 <= P -> S + P < 2^64 ->
    zlen out = j0 + 0 -> 0 <= j0 -> j0 + 4 <= dcap ->
    u8arr usegs m DST (map (Z_to_bv 8) out ++ junk) -> zlen junk = dcap - zlen out ->
       rw_cells usegs m (SP + 16) [C8 (Z_to_bv 64 s2); C8 (Z_to_bv 64 TB)] ->
       rw_cells usegs m (SP + 32) [C8 (Z_to_bv 64 s1); C8 (Z_to_bv 64 TB)] ->
       rw_cells usegs m (SP + 48) [C8 (Z_to_bv 64 C); C4 (Z_to_bv 64 B); CB 4 jp; C8 (Z_to_bv 64 (S + P));
                                     C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
       mem_inv usegs m -> munch W m0 m -> wmono usegs m0 m -> munch W m1 m -> wmono usegs m1 m ->
    (forall (m2 : fmem) (junk2 : list byte) (x26 : word),
       u8arr usegs m2 DST (map (Z_to_bv 8) (out ++ [o]) ++ junk2) -> zlen junk2 = dcap - zlen (out ++ [o]) ->
       rw_cells usegs m2 (SP + 16) [C8 (Z_to_bv 64 s2); C8 (Z_to_bv 64 TB)] ->
       rw_cells usegs m2 (SP + 32) [C8 (Z_to_bv 64 s'); C8 (Z_to_bv 64 TB)] ->
       rw_cells usegs m2 (SP + 48) [C8 (Z_to_bv 64 C); C4 (Z_to_bv 64 (bd_bits d')); CB 4 jp; C8 (Z_to_bv 64 (S + P));
                                     C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
       mem_inv usegs m2 -> munch W m0 m2 -> wmono usegs m0 m2 -> munch W m1 m2 -> wmono usegs m1 m2 ->
       evt usegs POST (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 (-4)) (Z_to_bv 64 (-5)) (Z_to_bv 64 64) (Z_to_bv 64 DST) (Z_to_bv 64 (2^61)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 TB) (Z_to_bv 64 TB) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 S) (Z_to_bv 64 (S + P)) (Z_to_bv 64 (-3)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 65535) (Z_to_bv 64 BIT_MASK_TAB) (Z_to_bv 64 (DST + j0)) (Z_to_bv 64 (DST + dcap - 3)) (Z_to_bv 64 (bd_bits d')) (Z_to_bv 64 (Z.shiftl s2 2)) (Z_to_bv 64 (Z.shiftl s2 2 + TB)) x26 (Z_to_bv 64 0) (Z_to_bv 64 (18446744073709551615 - BIT_MASK_TAB)) (Z_to_bv 64 s2) (Z_to_bv 64 s') (Z_to_bv 64 C))
                          F (Z_to_bv 64 (PFDW_L1D + 140)) fc None m2 (seg_rom usegs))) ->
    evt usegs POST (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 (-4)) (Z_to_bv 64 (-5)) (Z_to_bv 64 64) (Z_to_bv 64 DST) (Z_to_bv 64 (2^61)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 TB) (Z_to_bv 64 TB) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 S) (Z_to_bv 64 (S + P)) (Z_to_bv 64 (-3)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 65535) (Z_to_bv 64 BIT_MASK_TAB) (Z_to_bv 64 (DST + j0)) (Z_to_bv 64 (DST + dcap - 3)) (Z_to_bv 64 B) x24 x25 x26 x27 x28 (Z_to_bv 64 s2) (Z_to_bv 64 s1) (Z_to_bv 64 C))
                          F (Z_to_bv 64 (PFDW_L1D + 0)) fc None m (seg_rom usegs)).
  Proof using All.
    intros until x1. intros x24 x25 x26 x27 x28 DK S1R S2R BR CR PR PR2 OL0 J0 J4 OUTA LJ FS2 FS1 FBD MI MU WM MU1 WM1 KN.
    pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)) as PT.
    assert (P12 : 2^tl <= 4096) by (change 4096 with (2^12); apply Z.pow_le_mono_r; lia).
    assert (DB1 : sm_box (DST + dcap <= TB \/ TB + 4 * 2^tl <= DST)) by exact DJ1.
    destruct HS as (HS1 & HS2). destruct HTB as (HTB1 & HTB2). destruct HDST as (HD1 & HD2 & HD3).
    destruct HSPV as (HP1 & HP2). destruct DJF as (DF1 & DF2 & DF3).
    clear DJ1 DJ2 SRC BY HPRE.
    destruct (dec_inv _ _ _ _ _ DK ltac:(cbn [bd_bits]; lia)) as (c & NE & SR & CS & CN & CX & CNS & Eo & Es & Ed).
    subst o d'. cbn [bd_cont bd_bits bd_ptr bd_zero] in *. clear DK.
    assert (PN : 1 <= 2^(dc_nbBits c) <= 2^tl) by (split; [pose proof (Z.pow_pos_nonneg 2 (dc_nbBits c) ltac:(lia) ltac:(lia)); lia | apply Z.pow_le_mono_r; lia]).
    unfold PFDW_L1D.
    sm_walk 130144.
    sm_fix c B Es. osb OUTA LJ LJ. l1d_ob OUTA c.
    l1d_n27. l1d_n28.
    eapply KN; first [ eassumption | (rewrite ?length_app in *; cbn [length] in *; lia) ].
  Qed.

  Lemma l1d_d2 : forall (m m1 : fmem) (out : list Z) (junk : list byte) (s1 s2 B C P j0 : Z) (jp : list byte)
      (o s' : Z) (d' : bitD) (x1 x26 : word),
    decode_sym dt false s2 (mkBD C B P false) = Ok (o, s', d') ->
    0 <= s1 < 2^tl -> 0 <= s2 < 2^tl -> 0 <= B <= 100 -> 0 <= C < 2^64 -> 0 <= P -> S + P < 2^64 ->
    zlen out = j0 + 1 -> 0 <= j0 -> j0 + 4 <= dcap ->
    u8arr usegs m DST (map (Z_to_bv 8) out ++ junk) -> zlen junk = dcap - zlen out ->
       rw_cells usegs m (SP + 16) [C8 (Z_to_bv 64 s2); C8 (Z_to_bv 64 TB)] ->
       rw_cells usegs m (SP + 32) [C8 (Z_to_bv 64 s1); C8 (Z_to_bv 64 TB)] ->
       rw_cells usegs m (SP + 48) [C8 (Z_to_bv 64 C); C4 (Z_to_bv 64 B); CB 4 jp; C8 (Z_to_bv 64 (S + P));
                                     C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
       mem_inv usegs m -> munch W m0 m -> wmono usegs m0 m -> munch W m1 m -> wmono usegs m1 m ->
    (forall (m2 : fmem) (junk2 : list byte) (x25 x26 x27 : word),
       u8arr usegs m2 DST (map (Z_to_bv 8) (out ++ [o]) ++ junk2) -> zlen junk2 = dcap - zlen (out ++ [o]) ->
       rw_cells usegs m2 (SP + 16) [C8 (Z_to_bv 64 s'); C8 (Z_to_bv 64 TB)] ->
       rw_cells usegs m2 (SP + 32) [C8 (Z_to_bv 64 s1); C8 (Z_to_bv 64 TB)] ->
       rw_cells usegs m2 (SP + 48) [C8 (Z_to_bv 64 C); C4 (Z_to_bv 64 (bd_bits d')); CB 4 jp; C8 (Z_to_bv 64 (S + P));
                                     C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
       mem_inv usegs m2 -> munch W m0 m2 -> wmono usegs m0 m2 -> munch W m1 m2 -> wmono usegs m1 m2 ->
       evt usegs POST (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 (-4)) (Z_to_bv 64 (-5)) (Z_to_bv 64 64) (Z_to_bv 64 DST) (Z_to_bv 64 (2^61)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 TB) (Z_to_bv 64 TB) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 S) (Z_to_bv 64 (S + P)) (Z_to_bv 64 (-3)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 65535) (Z_to_bv 64 BIT_MASK_TAB) (Z_to_bv 64 (DST + j0)) (Z_to_bv 64 (DST + dcap - 3)) (Z_to_bv 64 (bd_bits d')) (Z_to_bv 64 (Z.shiftl s1 2 + TB)) x25 x26 x27 (Z_to_bv 64 (18446744073709551615 - BIT_MASK_TAB)) (Z_to_bv 64 s') (Z_to_bv 64 (Z.shiftl s1 2)) (Z_to_bv 64 C))
                          F (Z_to_bv 64 (PFDW_L1D + 256)) fc None m2 (seg_rom usegs))) ->
    evt usegs POST (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 (-4)) (Z_to_bv 64 (-5)) (Z_to_bv 64 64) (Z_to_bv 64 DST) (Z_to_bv 64 (2^61)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 TB) (Z_to_bv 64 TB) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 S) (Z_to_bv 64 (S + P)) (Z_to_bv 64 (-3)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 65535) (Z_to_bv 64 BIT_MASK_TAB) (Z_to_bv 64 (DST + j0)) (Z_to_bv 64 (DST + dcap - 3)) (Z_to_bv 64 B) (Z_to_bv 64 (Z.shiftl s2 2)) (Z_to_bv 64 (Z.shiftl s2 2 + TB)) x26 (Z_to_bv 64 0) (Z_to_bv 64 (18446744073709551615 - BIT_MASK_TAB)) (Z_to_bv 64 s2) (Z_to_bv 64 s1) (Z_to_bv 64 C))
                          F (Z_to_bv 64 (PFDW_L1D + 140)) fc None m (seg_rom usegs)).
  Proof using All.
    intros until x1. intros x26 DK S1R S2R BR CR PR PR2 OL0 J0 J4 OUTA LJ FS2 FS1 FBD MI MU WM MU1 WM1 KN.
    pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)) as PT.
    assert (P12 : 2^tl <= 4096) by (change 4096 with (2^12); apply Z.pow_le_mono_r; lia).
    assert (DB1 : sm_box (DST + dcap <= TB \/ TB + 4 * 2^tl <= DST)) by exact DJ1.
    destruct HS as (HS1 & HS2). destruct HTB as (HTB1 & HTB2). destruct HDST as (HD1 & HD2 & HD3).
    destruct HSPV as (HP1 & HP2). destruct DJF as (DF1 & DF2 & DF3).
    clear DJ1 DJ2 SRC BY HPRE.
    destruct (dec_inv _ _ _ _ _ DK ltac:(cbn [bd_bits]; lia)) as (c & NE & SR & CS & CN & CX & CNS & Eo & Es & Ed).
    subst o d'. cbn [bd_cont bd_bits bd_ptr bd_zero] in *. clear DK.
    assert (PN : 1 <= 2^(dc_nbBits c) <= 2^tl) by (split; [pose proof (Z.pow_pos_nonneg 2 (dc_nbBits c) ltac:(lia) ltac:(lia)); lia | apply Z.pow_le_mono_r; lia]).
    unfold PFDW_L1D.
    sm_walk 130260.
    sm_fix c B Es. osb OUTA LJ LJ. l1d_ob OUTA c.
    eapply KN; first [ eassumption | (rewrite ?length_app in *; cbn [length] in *; lia) ].
  Qed.

  Lemma l1d_d3 : forall (m m1 : fmem) (out : list Z) (junk : list byte) (s1 s2 B C P j0 : Z) (jp : list byte)
      (o s' : Z) (d' : bitD) (x1 x25 x26 x27 : word),
    decode_sym dt false s1 (mkBD C B P false) = Ok (o, s', d') ->
    0 <= s1 < 2^tl -> 0 <= s2 < 2^tl -> 0 <= B <= 100 -> 0 <= C < 2^64 -> 0 <= P -> S + P < 2^64 ->
    zlen out = j0 + 2 -> 0 <= j0 -> j0 + 4 <= dcap ->
    u8arr usegs m DST (map (Z_to_bv 8) out ++ junk) -> zlen junk = dcap - zlen out ->
       rw_cells usegs m (SP + 16) [C8 (Z_to_bv 64 s2); C8 (Z_to_bv 64 TB)] ->
       rw_cells usegs m (SP + 32) [C8 (Z_to_bv 64 s1); C8 (Z_to_bv 64 TB)] ->
       rw_cells usegs m (SP + 48) [C8 (Z_to_bv 64 C); C4 (Z_to_bv 64 B); CB 4 jp; C8 (Z_to_bv 64 (S + P));
                                     C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
       mem_inv usegs m -> munch W m0 m -> wmono usegs m0 m -> munch W m1 m -> wmono usegs m1 m ->
    (forall (m2 : fmem) (junk2 : list byte) (x25 x26 x27 : word),
       u8arr usegs m2 DST (map (Z_to_bv 8) (out ++ [o]) ++ junk2) -> zlen junk2 = dcap - zlen (out ++ [o]) ->
       rw_cells usegs m2 (SP + 16) [C8 (Z_to_bv 64 s2); C8 (Z_to_bv 64 TB)] ->
       rw_cells usegs m2 (SP + 32) [C8 (Z_to_bv 64 s'); C8 (Z_to_bv 64 TB)] ->
       rw_cells usegs m2 (SP + 48) [C8 (Z_to_bv 64 C); C4 (Z_to_bv 64 (bd_bits d')); CB 4 jp; C8 (Z_to_bv 64 (S + P));
                                     C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
       mem_inv usegs m2 -> munch W m0 m2 -> wmono usegs m0 m2 -> munch W m1 m2 -> wmono usegs m1 m2 ->
       evt usegs POST (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 (-4)) (Z_to_bv 64 (-5)) (Z_to_bv 64 64) (Z_to_bv 64 DST) (Z_to_bv 64 (2^61)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 TB) (Z_to_bv 64 TB) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 S) (Z_to_bv 64 (S + P)) (Z_to_bv 64 (-3)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 65535) (Z_to_bv 64 BIT_MASK_TAB) (Z_to_bv 64 (DST + j0)) (Z_to_bv 64 (DST + dcap - 3)) (Z_to_bv 64 (bd_bits d')) (Z_to_bv 64 (Z.shiftl s2 2 + TB)) x25 x26 x27 (Z_to_bv 64 (18446744073709551615 - BIT_MASK_TAB)) (Z_to_bv 64 (Z.shiftl s2 2)) (Z_to_bv 64 s') (Z_to_bv 64 C))
                          F (Z_to_bv 64 (PFDW_L1D + 372)) fc None m2 (seg_rom usegs))) ->
    evt usegs POST (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 (-4)) (Z_to_bv 64 (-5)) (Z_to_bv 64 64) (Z_to_bv 64 DST) (Z_to_bv 64 (2^61)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 TB) (Z_to_bv 64 TB) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 S) (Z_to_bv 64 (S + P)) (Z_to_bv 64 (-3)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 65535) (Z_to_bv 64 BIT_MASK_TAB) (Z_to_bv 64 (DST + j0)) (Z_to_bv 64 (DST + dcap - 3)) (Z_to_bv 64 B) (Z_to_bv 64 (Z.shiftl s1 2 + TB)) x25 x26 x27 (Z_to_bv 64 (18446744073709551615 - BIT_MASK_TAB)) (Z_to_bv 64 s2) (Z_to_bv 64 (Z.shiftl s1 2)) (Z_to_bv 64 C))
                          F (Z_to_bv 64 (PFDW_L1D + 256)) fc None m (seg_rom usegs)).
  Proof using All.
    intros until x1. intros x25 x26 x27 DK S1R S2R BR CR PR PR2 OL0 J0 J4 OUTA LJ FS2 FS1 FBD MI MU WM MU1 WM1 KN.
    pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)) as PT.
    assert (P12 : 2^tl <= 4096) by (change 4096 with (2^12); apply Z.pow_le_mono_r; lia).
    assert (DB1 : sm_box (DST + dcap <= TB \/ TB + 4 * 2^tl <= DST)) by exact DJ1.
    destruct HS as (HS1 & HS2). destruct HTB as (HTB1 & HTB2). destruct HDST as (HD1 & HD2 & HD3).
    destruct HSPV as (HP1 & HP2). destruct DJF as (DF1 & DF2 & DF3).
    clear DJ1 DJ2 SRC BY HPRE.
    destruct (dec_inv _ _ _ _ _ DK ltac:(cbn [bd_bits]; lia)) as (c & NE & SR & CS & CN & CX & CNS & Eo & Es & Ed).
    subst o d'. cbn [bd_cont bd_bits bd_ptr bd_zero] in *. clear DK.
    assert (PN : 1 <= 2^(dc_nbBits c) <= 2^tl) by (split; [pose proof (Z.pow_pos_nonneg 2 (dc_nbBits c) ltac:(lia) ltac:(lia)); lia | apply Z.pow_le_mono_r; lia]).
    unfold PFDW_L1D.
    sm_walk 130376.
    sm_fix c B Es. osb OUTA LJ LJ. l1d_ob OUTA c.
    eapply KN; first [ eassumption | (rewrite ?length_app in *; cbn [length] in *; lia) ].
  Qed.

  Lemma l1d_d4 : forall (m m1 : fmem) (out : list Z) (junk : list byte) (s1 s2 B C P j0 : Z) (jp : list byte)
      (o s' : Z) (d' : bitD) (x1 x25 x26 x27 : word),
    decode_sym dt false s2 (mkBD C B P false) = Ok (o, s', d') ->
    0 <= s1 < 2^tl -> 0 <= s2 < 2^tl -> 0 <= B <= 100 -> 0 <= C < 2^64 -> 0 <= P -> S + P < 2^64 ->
    zlen out = j0 + 3 -> 0 <= j0 -> j0 + 4 <= dcap ->
    u8arr usegs m DST (map (Z_to_bv 8) out ++ junk) -> zlen junk = dcap - zlen out ->
       rw_cells usegs m (SP + 16) [C8 (Z_to_bv 64 s2); C8 (Z_to_bv 64 TB)] ->
       rw_cells usegs m (SP + 32) [C8 (Z_to_bv 64 s1); C8 (Z_to_bv 64 TB)] ->
       rw_cells usegs m (SP + 48) [C8 (Z_to_bv 64 C); C4 (Z_to_bv 64 B); CB 4 jp; C8 (Z_to_bv 64 (S + P));
                                     C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
       mem_inv usegs m -> munch W m0 m -> wmono usegs m0 m -> munch W m1 m -> wmono usegs m1 m ->
    (forall (m2 : fmem) (junk2 : list byte) (x23 x24 x25 x26 x27 x31 : word),
       u8arr usegs m2 DST (map (Z_to_bv 8) (out ++ [o]) ++ junk2) -> zlen junk2 = dcap - zlen (out ++ [o]) ->
       rw_cells usegs m2 (SP + 16) [C8 (Z_to_bv 64 s'); C8 (Z_to_bv 64 TB)] ->
       rw_cells usegs m2 (SP + 32) [C8 (Z_to_bv 64 s1); C8 (Z_to_bv 64 TB)] ->
       rw_cells usegs m2 (SP + 48) [C8 (Z_to_bv 64 C); C4 (Z_to_bv 64 (bd_bits d')); CB 4 jp; C8 (Z_to_bv 64 (S + P));
                                     C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
       mem_inv usegs m2 -> munch W m0 m2 -> wmono usegs m0 m2 -> munch W m1 m2 -> wmono usegs m1 m2 ->
       evt usegs POST (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 (-4)) (Z_to_bv 64 (-5)) (Z_to_bv 64 64) (Z_to_bv 64 DST) (Z_to_bv 64 (2^61)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 TB) (Z_to_bv 64 TB) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 S) (Z_to_bv 64 (S + P)) (Z_to_bv 64 (-3)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 65535) (Z_to_bv 64 BIT_MASK_TAB) (Z_to_bv 64 (DST + j0)) (Z_to_bv 64 (DST + dcap - 3)) x23 x24 x25 x26 x27 (Z_to_bv 64 (bd_bits d')) (Z_to_bv 64 s') (Z_to_bv 64 s1) x31)
                          F (Z_to_bv 64 (PFDW_L1D + 480)) fc None m2 (seg_rom usegs))) ->
    evt usegs POST (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 (-4)) (Z_to_bv 64 (-5)) (Z_to_bv 64 64) (Z_to_bv 64 DST) (Z_to_bv 64 (2^61)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 TB) (Z_to_bv 64 TB) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 S) (Z_to_bv 64 (S + P)) (Z_to_bv 64 (-3)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 65535) (Z_to_bv 64 BIT_MASK_TAB) (Z_to_bv 64 (DST + j0)) (Z_to_bv 64 (DST + dcap - 3)) (Z_to_bv 64 B) (Z_to_bv 64 (Z.shiftl s2 2 + TB)) x25 x26 x27 (Z_to_bv 64 (18446744073709551615 - BIT_MASK_TAB)) (Z_to_bv 64 (Z.shiftl s2 2)) (Z_to_bv 64 s1) (Z_to_bv 64 C))
                          F (Z_to_bv 64 (PFDW_L1D + 372)) fc None m (seg_rom usegs)).
  Proof using All.
    intros until x1. intros x25 x26 x27 DK S1R S2R BR CR PR PR2 OL0 J0 J4 OUTA LJ FS2 FS1 FBD MI MU WM MU1 WM1 KN.
    pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)) as PT.
    assert (P12 : 2^tl <= 4096) by (change 4096 with (2^12); apply Z.pow_le_mono_r; lia).
    assert (DB1 : sm_box (DST + dcap <= TB \/ TB + 4 * 2^tl <= DST)) by exact DJ1.
    destruct HS as (HS1 & HS2). destruct HTB as (HTB1 & HTB2). destruct HDST as (HD1 & HD2 & HD3).
    destruct HSPV as (HP1 & HP2). destruct DJF as (DF1 & DF2 & DF3).
    clear DJ1 DJ2 SRC BY HPRE.
    destruct (dec_inv _ _ _ _ _ DK ltac:(cbn [bd_bits]; lia)) as (c & NE & SR & CS & CN & CX & CNS & Eo & Es & Ed).
    subst o d'. cbn [bd_cont bd_bits bd_ptr bd_zero] in *. clear DK.
    assert (PN : 1 <= 2^(dc_nbBits c) <= 2^tl) by (split; [pose proof (Z.pow_pos_nonneg 2 (dc_nbBits c) ltac:(lia) ltac:(lia)); lia | apply Z.pow_le_mono_r; lia]).
    unfold PFDW_L1D.
    sm_walk 130484.
    sm_nrm; try replace (dc_nbBits c + B) with (B + dc_nbBits c) in * by lia;
    replace (bv_swrap 32 (B + dc_nbBits c)) with (B + dc_nbBits c) in * by (symmetry; apply FseWalkKit.swrap32_small; lia).
    sm_fix c B Es. osb OUTA LJ LJ. l1d_ob OUTA c.
    eapply KN; first [ eassumption | (rewrite ?length_app in *; cbn [length] in *; lia) ].
  Qed.

  Lemma l1d_bt : forall (m m1 : fmem) (out : list Z) (junk : list byte) (s1 s2 B C P j0 : Z) (jp : list byte)
      (x1 x23 x24 x25 x26 x27 x31 : word),
    0 <= s1 < 2^tl -> 0 <= s2 < 2^tl -> 0 <= B <= 1000 -> 0 <= C < 2^64 -> 0 <= P -> S + P < 2^64 ->
    zlen out = j0 + 4 -> 0 <= j0 -> j0 + 4 <= dcap ->
    u8arr usegs m DST (map (Z_to_bv 8) out ++ junk) -> zlen junk = dcap - zlen out ->
       rw_cells usegs m (SP + 16) [C8 (Z_to_bv 64 s2); C8 (Z_to_bv 64 TB)] ->
       rw_cells usegs m (SP + 32) [C8 (Z_to_bv 64 s1); C8 (Z_to_bv 64 TB)] ->
       rw_cells usegs m (SP + 48) [C8 (Z_to_bv 64 C); C4 (Z_to_bv 64 B); CB 4 jp; C8 (Z_to_bv 64 (S + P));
                                     C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
       mem_inv usegs m -> munch W m0 m -> wmono usegs m0 m -> munch W m1 m -> wmono usegs m1 m ->
    (B <= 64 -> forall (x23 x24 x25 x26 x27 x31 : word), evt usegs POST (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 (-4)) (Z_to_bv 64 (-5)) (Z_to_bv 64 64) (Z_to_bv 64 DST) (Z_to_bv 64 (2^61)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 TB) (Z_to_bv 64 TB) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 S) (Z_to_bv 64 (S + P)) (Z_to_bv 64 (-3)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 65535) (Z_to_bv 64 BIT_MASK_TAB) (Z_to_bv 64 (DST + j0 + 4)) (Z_to_bv 64 (DST + dcap - 3)) x23 x24 x25 x26 x27 (Z_to_bv 64 B) (Z_to_bv 64 s2) (Z_to_bv 64 s1) x31)
                          F (Z_to_bv 64 PFDW_L1) fc None m (seg_rom usegs))) ->
    (64 < B -> forall (m2 : fmem) (y5 y6 y7 y10 y15 y16 y17 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
       u8arr usegs m2 DST (map (Z_to_bv 8) out ++ junk) ->
       rw_cells usegs m2 (SP + 16) [C8 (Z_to_bv 64 s2); C8 (Z_to_bv 64 TB)] ->
       rw_cells usegs m2 (SP + 32) [C8 (Z_to_bv 64 s1); C8 (Z_to_bv 64 TB)] ->
       rw_cells usegs m2 (SP + 48) [C8 (Z_to_bv 64 C); C4 (Z_to_bv 64 B); CB 4 jp; C8 (Z_to_bv 64 ZEROFILLED_F);
                                     C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
       mem_inv usegs m2 -> munch W m0 m2 -> wmono usegs m0 m2 -> munch W m1 m2 -> wmono usegs m1 m2 ->
       evt usegs POST (MS (mkR x1 (Z_to_bv 64 SP) gp tp y5 y6 y7 (Z_to_bv 64 DST) (Z_to_bv 64 (2^61)) y10 (Z_to_bv 64 TB) (Z_to_bv 64 TB) (Z_to_bv 64 1) (Z_to_bv 64 1) y15 y16 y17 (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 65535) (Z_to_bv 64 BIT_MASK_TAB) (Z_to_bv 64 (DST + j0 + 4)) y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                          F (Z_to_bv 64 PFDW_T1) fc None m2 (seg_rom usegs))) ->
    evt usegs POST (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 (-4)) (Z_to_bv 64 (-5)) (Z_to_bv 64 64) (Z_to_bv 64 DST) (Z_to_bv 64 (2^61)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 TB) (Z_to_bv 64 TB) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 S) (Z_to_bv 64 (S + P)) (Z_to_bv 64 (-3)) (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 65535) (Z_to_bv 64 BIT_MASK_TAB) (Z_to_bv 64 (DST + j0)) (Z_to_bv 64 (DST + dcap - 3)) x23 x24 x25 x26 x27 (Z_to_bv 64 B) (Z_to_bv 64 s2) (Z_to_bv 64 s1) x31)
                          F (Z_to_bv 64 (PFDW_L1D + 480)) fc None m (seg_rom usegs)).
  Proof using All.
    intros until x1. intros x23 x24 x25 x26 x27 x31 S1R S2R BR CR PR PR2 OL0 J0 J4 OUTA LJ FS2 FS1 FBD MI MU WM MU1 WM1 KL KT.
    destruct HS as (HS1 & HS2). destruct HTB as (HTB1 & HTB2). destruct HDST as (HD1 & HD2 & HD3).
    destruct HSPV as (HP1 & HP2). destruct DJF as (DF1 & DF2 & DF3).
    clear DJ1 DJ2 SRC BY HPRE.
    unfold PFDW_L1D, PFDW_L1, PFDW_T1 in *. unfold ZEROFILLED_F in KT.
    repeat (lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 129736) _ _ _ _) => fail
      | |- evt _ _ (MS _ _ (Z_to_bv 64 130512) _ _ _ _) => fail
      | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => zstep
      | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => fd_brk; sm_ref end).
    all: first [ (eapply KL; lia) | (eapply KT; first [ lia | eassumption ]) ].
  Qed.

  Lemma l1d_sec : forall (m1 : fmem) (jp : list byte) (out : list Z) (s1 s2 : Z) (d0 : bitD)
      (o0 s1a o1 s2a o2 s1b o3 s2b : Z) (d1 d2 d3 d4 : bitD) (y1 y24 y25 y26 y27 y28 : word),
    decode_sym dt false s1 d0 = Ok (o0, s1a, d1) -> decode_sym dt false s2 d1 = Ok (o1, s2a, d2) ->
    decode_sym dt false s1a d2 = Ok (o2, s1b, d3) -> decode_sym dt false s2a d3 = Ok (o3, s2b, d4) ->
    sm_ok dcap bs (mkDec out s1 s2 d0) -> st_ok tl (mkDec out s1 s2 d0) -> zlen out + 4 <= dcap ->
    fdw_mem m0 m1 SP S DT DST dcap lo bs dt (mkDec out s1 s2 d0) jp ->
    (bd_bits d4 <= 64 ->
       fdw_l1_K SP gp tp F fc m0 S DT DST dcap lo bs dt POST (mkDec (out ++ [o0; o1; o2; o3]) s1b s2b d4)) ->
    (64 < bd_bits d4 ->
       fdw_t1_K SP gp tp F fc m0 S DT DST dcap lo bs dt POST
         (mkDec (out ++ [o0; o1; o2; o3]) s1b s2b (mkBD (bd_cont d4) (bd_bits d4) (bd_ptr d4) true))) ->
    evt usegs POST (MS (mkR y1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 (-4)) (Z_to_bv 64 (-5)) (Z_to_bv 64 64)
                            (Z_to_bv 64 DST) (Z_to_bv 64 (2^61)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (DT + 4))
                            (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 S)
                            (Z_to_bv 64 (S + bd_ptr d0)) (Z_to_bv 64 (-3)) (Z_to_bv 64 (DST + dcap))
                            (Z_to_bv 64 65535) (Z_to_bv 64 BIT_MASK_TAB) (Z_to_bv 64 (DST + zlen out))
                            (Z_to_bv 64 (DST + dcap - 3)) (Z_to_bv 64 (bd_bits d0)) y24 y25 y26 y27 y28
                            (Z_to_bv 64 s2) (Z_to_bv 64 s1) (Z_to_bv 64 (bd_cont d0)))
                       F (Z_to_bv 64 PFDW_L1D) fc None m1 (seg_rom usegs)).
  Proof using All.
    intros until y28. intros D1 D2 D3 D4 OK ST OL MEM KL KT.
    destruct OK as ((BC & BB & BP0 & BP1 & BP2 & BZ) & B64 & OLEN & OBY). cbn [de_bd de_out de_s1 de_s2] in *.
    destruct ST as (ST1 & ST2). cbn [de_s1 de_s2] in ST1, ST2.
    destruct MEM as (FS2 & FS1 & FBD & ((junk & OUTA & LJ) & MU & WM & MI) & TB1 & SRC1 & STK).
    cbn [de_s1 de_s2 de_bd de_out] in *.
    destruct d0 as [C B P z]. cbn [bd_cont bd_bits bd_ptr bd_zero] in *.
    destruct z; [specialize (BZ eq_refl); lia|]. clear BZ.
    unfold bitdz_cells in FBD. cbn [bd_cont bd_bits bd_ptr bd_zero] in FBD.
    pose proof (munch_refl W m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
    clear TB1 SRC1.
    destruct (dec_inv _ _ _ _ _ D1 ltac:(cbn [bd_bits]; lia)) as (c1 & _ & _ & CS1 & CN1 & CX1 & CNS1 & E1o & E1s & E1d).
    subst d1. cbn [bd_cont bd_bits bd_ptr bd_zero] in *.
    destruct (dec_inv _ _ _ _ _ D2 ltac:(cbn [bd_bits]; lia)) as (c2 & _ & _ & CS2 & CN2 & CX2 & CNS2 & E2o & E2s & E2d).
    subst d2. cbn [bd_cont bd_bits bd_ptr bd_zero] in *.
    destruct (dec_inv _ _ _ _ _ D3 ltac:(cbn [bd_bits]; lia)) as (c3 & _ & S1aR & CS3 & CN3 & CX3 & CNS3 & E3o & E3s & E3d).
    subst d3. cbn [bd_cont bd_bits bd_ptr bd_zero] in *.
    destruct (dec_inv _ _ _ _ _ D4 ltac:(cbn [bd_bits]; lia)) as (c4 & _ & S2aR & CS4 & CN4 & CX4 & CNS4 & E4o & E4s & E4d).
    subst d4. cbn [bd_cont bd_bits bd_ptr bd_zero] in *.
    subst o0 o1 o2 o3.
    pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)) as PT.
    pose proof HPRE as HP. unfold fdw_pre in HP. decompose [and] HP. clear HP.
    assert (S1bR : 0 <= s1b < 2^tl).
    { rewrite E3s. pose proof (l1d_land_lt (Z.shiftr C ((bv_swrap 32 (0 - (B + dc_nbBits c1 + dc_nbBits c2 + dc_nbBits c3)) mod 18446744073709551616) mod 64)) (dc_nbBits c3) ltac:(lia) ltac:(apply Z.shiftr_nonneg; lia)). lia. }
    assert (S2bR : 0 <= s2b < 2^tl).
    { rewrite E4s. pose proof (l1d_land_lt (Z.shiftr C ((bv_swrap 32 (0 - (B + dc_nbBits c1 + dc_nbBits c2 + dc_nbBits c3 + dc_nbBits c4)) mod 18446744073709551616) mod 64)) (dc_nbBits c4) ltac:(lia) ltac:(apply Z.shiftr_nonneg; lia)). lia. }
    clear E1s E2s E3s E4s.
    set (n1 := dc_nbBits c1) in *. set (n2 := dc_nbBits c2) in *. set (n3 := dc_nbBits c3) in *. set (n4 := dc_nbBits c4) in *.
    assert (LO1 : zlen (out ++ [dc_symbol c1]) = zlen out + 1) by (rewrite length_app; cbn [length]; lia).
    assert (LO2 : zlen ((out ++ [dc_symbol c1]) ++ [dc_symbol c2]) = zlen out + 2) by (rewrite !length_app; cbn [length]; lia).
    assert (LO3 : zlen (((out ++ [dc_symbol c1]) ++ [dc_symbol c2]) ++ [dc_symbol c3]) = zlen out + 3)
      by (rewrite !length_app; cbn [length]; lia).
    assert (LO4 : zlen (out ++ [dc_symbol c1; dc_symbol c2; dc_symbol c3; dc_symbol c4]) = zlen out + 4)
      by (rewrite !length_app; cbn [length]; lia).
    eapply (l1d_d1 m1 m1 out junk s1 s2 B C P (zlen out) jp _ s1a _ y1 y24 y25 y26 y27 y28 D1).
    all: try eassumption. all: try (lazymatch goal with |- evt _ _ _ => fail | |- forall _, _ => fail | |- _ -> _ => fail | |- _ => lia end).
    intros m2 junk2 z26 OUTA2 LJ2 FS22 FS12 FBD2 MI2 MU2 WM2 MU12 WM12.
    eapply (l1d_d2 m2 m1 (out ++ [dc_symbol c1]) junk2 s1a s2 (B + n1) C P (zlen out) jp _ s2a _ y1 z26 D2).
    all: try eassumption. all: try (lazymatch goal with |- evt _ _ _ => fail | |- forall _, _ => fail | |- _ -> _ => fail | |- _ => lia end).
    intros m3 junk3 z25 z26' z27 OUTA3 LJ3 FS23 FS13 FBD3 MI3 MU3 WM3 MU13 WM13.
    eapply (l1d_d3 m3 m1 ((out ++ [dc_symbol c1]) ++ [dc_symbol c2]) junk3 s1a s2a (B + n1 + n2) C P (zlen out) jp _ s1b _ y1
              z25 z26' z27 D3).
    all: try eassumption. all: try (lazymatch goal with |- evt _ _ _ => fail | |- forall _, _ => fail | |- _ -> _ => fail | |- _ => lia end).
    intros m4 junk4 w25 w26 w27 OUTA4 LJ4 FS24 FS14 FBD4 MI4 MU4 WM4 MU14 WM14.
    eapply (l1d_d4 m4 m1 (((out ++ [dc_symbol c1]) ++ [dc_symbol c2]) ++ [dc_symbol c3]) junk4 s1b s2a (B + n1 + n2 + n3) C P
              (zlen out) jp _ s2b _ y1 w25 w26 w27 D4).
    all: try eassumption. all: try (lazymatch goal with |- evt _ _ _ => fail | |- forall _, _ => fail | |- _ -> _ => fail | |- _ => lia end).
    intros m5 junk5 v23 v24 v25 v26 v27 v31 OUTA5 LJ5 FS25 FS15 FBD5 MI5 MU5 WM5 MU15 WM15.
    rewrite <- !app_assoc in OUTA5, LJ5. cbn [app] in OUTA5, LJ5.
    eapply (l1d_bt m5 m1 (out ++ [dc_symbol c1; dc_symbol c2; dc_symbol c3; dc_symbol c4]) junk5 s1b s2b (B + n1 + n2 + n3 + n4)
              C P (zlen out) jp y1 v23 v24 v25 v26 v27 v31).
    all: try eassumption. all: try (lazymatch goal with |- evt _ _ _ => fail | |- forall _, _ => fail | |- _ -> _ => fail | |- _ => lia end).
    - intros HB q23 q24 q25 q26 q27 q31.
      specialize (KL ltac:(cbn [bd_bits]; lia)). unfold fdw_l1_K in KL.
      cbn [de_out de_s1 de_s2 de_bd bd_cont bd_bits bd_ptr bd_zero] in KL.
      rewrite <- Z.add_assoc. rewrite <- LO4.
      eapply (KL m5 jp).
      + unfold sm_ok, bitd_ok. cbn [de_out de_s1 de_s2 de_bd bd_cont bd_bits bd_ptr bd_zero].
        split; [| split; [lia | split; [lia |]]].
        * split; [lia | split; [lia | split; [lia | split; [lia | split; [assumption | intro HF; discriminate]]]]].
        * apply Forall_app. split; [exact OBY | repeat constructor; lia].
      + unfold st_ok. cbn [de_s1 de_s2]. lia.
      + unfold fdw_mem, sm_inv, bitdz_cells. cbn [de_out de_s1 de_s2 de_bd bd_cont bd_bits bd_ptr bd_zero].
        split; [exact FS25 | split; [exact FS15 | split; [exact FBD5 | split; [ | split; [ | split]]]]].
        * split; [exists junk5; split; [exact OUTA5 | exact LJ5] | split; [exact MU5 | split; [exact WM5 | exact MI5]]].
        * apply (bytes_at_transport usegs W m0 m5 (DT + 4) _ TBB MU5). rewrite fse_cells_length. cbn [disjoint_from].
          unfold sm_box in *. lia.
        * apply (bytes_at_transport usegs W m0 m5 S _ SRC MU5). rewrite length_map. cbn [disjoint_from]. lia.
        * apply (stk_transport_disjoint usegs W m1 m5 lo SP STK MU15 WM15). cbn [disjoint_from]. lia.
    - intros HB m6 y5' y6' y7' y10' y15' y16' y17' y22' y23' y24' y25' y26' y27' y28' y29' y30' y31'
        OUTA6 FS26 FS16 FBD6 MI6 MU6 WM6 MU16 WM16.
      specialize (KT ltac:(cbn [bd_bits]; lia)). unfold fdw_t1_K in KT.
      cbn [de_out de_s1 de_s2 de_bd bd_cont bd_bits bd_ptr bd_zero] in KT.
      rewrite <- Z.add_assoc. rewrite <- LO4.
      eapply (KT m6 jp).
      + unfold sm_okr, bitd_ok. cbn [de_out de_s1 de_s2 de_bd bd_cont bd_bits bd_ptr bd_zero].
        split; [| split; [lia | split; [lia |]]].
        * split; [lia | split; [lia | split; [lia | split; [lia | split; [assumption | intro; lia]]]]].
        * apply Forall_app. split; [exact OBY | repeat constructor; lia].
      + unfold st_ok. cbn [de_s1 de_s2]. lia.
      + unfold fdw_mem, sm_inv, bitdz_cells. cbn [de_out de_s1 de_s2 de_bd bd_cont bd_bits bd_ptr bd_zero].
        split; [exact FS26 | split; [exact FS16 | split; [exact FBD6 | split; [ | split; [ | split]]]]].
        * split; [exists junk5; split; [exact OUTA6 | exact LJ5] | split; [exact MU6 | split; [exact WM6 | exact MI6]]].
        * apply (bytes_at_transport usegs W m0 m6 (DT + 4) _ TBB MU6). rewrite fse_cells_length. cbn [disjoint_from].
          unfold sm_box in *. lia.
        * apply (bytes_at_transport usegs W m0 m6 S _ SRC MU6). rewrite length_map. cbn [disjoint_from]. lia.
        * apply (stk_transport_disjoint usegs W m1 m6 lo SP STK MU16 WM16). cbn [disjoint_from]. lia.
  Qed.

End L1D.

Theorem fdw_l1d_proof : fdw_l1d_stmt.
Proof.
  unfold fdw_l1d_stmt. intros SP gp tp F fc m0 m1 S DT DST dcap lo bs dt POST jp out s1 s2 d0 o0 s1a o1 s2a o2 s1b o3 s2b
    d1 d2 d3 d4 y1 y24 y25 y26 y27 y28 HPRE D1 D2 D3 D4 OK ST OL MEM KL KT.
  pose proof HPRE as HP. unfold fdw_pre in HP. decompose [and] HP. clear HP.
  pose proof MEM as (_ & _ & _ & (_ & MU & _ & _) & TB1 & SRC1 & _).
  assert (TBB : bytes_at usegs m0 (DT + 4) (concat (map fse_cell_bytes (dt_cells dt)))).
  { apply (bytes_at_transport usegs _ m1 m0 _ _ TB1 (l1d_munch_sym _ _ _ MU)). rewrite fse_cells_length.
    cbn [disjoint_from]. lia. }
  assert (SRC : bytes_at usegs m0 S (map (Z_to_bv 8) bs)).
  { apply (bytes_at_transport usegs _ m1 m0 _ _ SRC1 (l1d_munch_sym _ _ _ MU)). rewrite length_map.
    cbn [disjoint_from]. lia. }
  eapply (l1d_sec gp tp F fc m0 S DT DST dcap lo bs dt POST SP HPRE).
  all: try eassumption.
  all: try (lazymatch goal with |- evt _ _ _ => fail | |- _ => lia end).
Qed.
