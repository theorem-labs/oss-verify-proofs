(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit STRW_tac.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface RF_huf_tbl_iface RF_huf_tbl_kit RF_huf_fdw_kit
  RF_huf_y4_kit_reload RF_huf_fdw_kit_dsym RF_huf_bdt_model RF_huf_fdw_cut RF_huf_fdw_fmb RF_huf_fdw_fmbp.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma fm_d8 : forall q r, 0 <= r <= 7 -> (8 * q + r) / 8 = q.
Proof. intros q r R. symmetry. apply (Z.div_unique (8 * q + r) 8 q r); lia. Qed.

Ltac fm_q := repeat match goal with H : context [bv_wrap 32 (8 * ?q + ?r)] |- _ =>
                rewrite (wrap32_small (8 * q + r)) in H by lia end;
  repeat match goal with H : context [(8 * ?q + ?r) / 8] |- _ => rewrite (fm_d8 q r) in H by lia end;
  repeat match goal with H : context [bv_swrap 32 ?q] |- _ => rewrite (swrap32_small q) in H by lia end;
  repeat match goal with H : context [?q mod ?M] |- _ => is_var q; rewrite (Z.mod_small q M) in H by lia end.

Ltac fm_ref := try (exfalso; fd_clr; fm_q; lia).

Lemma fm_land7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Ltac fm_zn := rewrite ?fm_land7, ?wrap32_eq, ?swrap32_eq in *;
  rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 in * by lia; try change (2 ^ 3) with 8 in *.

Ltac fm_fix7 q r p := let v := reg_val 7%Z in lazymatch v with Z_to_bv 64 ?e =>
  let E := fresh "E7" in
  first [ assert (E : e = r) by (fd_clr; fm_zn; lia)
        | assert (E : e = 8 * q + r - 8 * p) by (fd_clr; fm_zn; lia) ];
  rewrite E in * end.

Lemma fm_le64_range : forall bs p, Forall (fun c => 0 <= c < 256) bs -> 0 <= p -> p + 8 <= zlen bs ->
  0 <= Znth p bs + 2^8 * Znth (p+1) bs + 2^16 * Znth (p+2) bs + 2^24 * Znth (p+3) bs
       + 2^32 * Znth (p+4) bs + 2^40 * Znth (p+5) bs + 2^48 * Znth (p+6) bs + 2^56 * Znth (p+7) bs < 2^64.
Proof.
  intros bs p BY P0 P8.
  pose proof (byte_Znth bs p BY ltac:(lia)). pose proof (byte_Znth bs (p+1) BY ltac:(lia)).
  pose proof (byte_Znth bs (p+2) BY ltac:(lia)). pose proof (byte_Znth bs (p+3) BY ltac:(lia)).
  pose proof (byte_Znth bs (p+4) BY ltac:(lia)). pose proof (byte_Znth bs (p+5) BY ltac:(lia)).
  pose proof (byte_Znth bs (p+6) BY ltac:(lia)). pose proof (byte_Znth bs (p+7) BY ltac:(lia)).
  lia.
Qed.

Ltac fm_fin := repeat split; try lia; try reflexivity; try (intros; discriminate); try (intros; lia).

Lemma fm_reload_ok : forall bs d st d0, Forall (fun c => 0 <= c < 256) bs -> bitd_ok bs d -> bd_bits d <= 64 ->
  reload_dstream bs d = Ok (st, d0) ->
  bitd_ok bs d0 /\ bd_bits d0 <= 64 /\ bd_zero d0 = false /\ (st = Unfinished -> bd_bits d0 < 8).
Proof.
  intros bs [c bc p z] st d0 BY (BC & BB & BP0 & BPE & BSM & BZ) B64 RL.
  cbn [bd_cont bd_bits bd_ptr bd_zero] in *.
  assert (Z0 : z = false) by (destruct z; [specialize (BZ eq_refl); lia | reflexivity]). subst z.
  unfold reload_dstream in RL. cbn [bd_cont bd_bits bd_ptr bd_zero] in RL.
  replace (64 <? bc) with false in RL by (symmetry; apply Z.ltb_ge; lia).
  assert (NB : Z.shiftr bc 3 = bc / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  rewrite NB in RL.
  destruct (8 <=? p) eqn:P8.
  - apply Z.leb_le in P8.
    rewrite readLE64_ok in RL by lia. cbn [bind] in RL. injection RL as <- <-.
    pose proof (fm_le64_range bs (p - bc / 8) BY ltac:(lia) ltac:(lia)) as R.
    assert (L7 : Z.land bc 7 = bc mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
    unfold bitd_ok; cbn [bd_cont bd_bits bd_ptr bd_zero]. rewrite L7. fm_fin.
  - apply Z.leb_gt in P8. destruct (p =? 0) eqn:P0.
    + apply Z.eqb_eq in P0. subst p.
      destruct (bc <? 64); injection RL as <- <-; unfold bitd_ok; cbn [bd_cont bd_bits bd_ptr bd_zero];
        fm_fin.
    + apply Z.eqb_neq in P0.
      assert (L8 : 8 <= zlen bs) by (destruct (Z_lt_le_dec (zlen bs) 8) as [L|L]; [specialize (BSM L); lia | lia]).
      destruct (p - bc / 8 <? 0) eqn:PN.
      * apply Z.ltb_lt in PN. cbn iota in RL.
        rewrite readLE64_ok in RL by lia. cbn [bind] in RL. injection RL as <- <-.
        pose proof (fm_le64_range bs (p - p) BY ltac:(lia) ltac:(lia)) as R.
        unfold bitd_ok; cbn [bd_cont bd_bits bd_ptr bd_zero]. fm_fin.
      * apply Z.ltb_ge in PN. cbn iota in RL.
        rewrite readLE64_ok in RL by lia. cbn [bind] in RL. injection RL as <- <-.
        pose proof (fm_le64_range bs (p - bc / 8) BY ltac:(lia) ltac:(lia)) as R.
        unfold bitd_ok; cbn [bd_cont bd_bits bd_ptr bd_zero]. fm_fin.
Qed.

Ltac fm_step stop := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x20828) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x20218) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x2027c) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x20438) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 stop) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) =>
      try (match goal with E1 : bv_unsigned (zx32 _) = _, E2 : Z.shiftr _ 3 = _, E3 : _ mod 2 ^ 3 = _ |- _ =>
             rewrite ?E1, ?E2, ?E3 end); zstep end).

Section FM.
  Variables (SP : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem) (S DT DST dcap lo : Z)
            (bs : list Z) (dt : dtable) (POST : machine_state -> Prop).
  Hypothesis PRE : fdw_pre SP S DT DST dcap lo bs dt.
  Hypothesis NB1 : Forall (fun c => 1 <= dc_nbBits c) (dt_cells dt).

  Notation SL3 pc mm x1 s1 s2 bits j ptr x21 x22 x23 x24 x25 x26 x27 cont :=
    (MS (mkR x1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 s1) (Z_to_bv 64 s2) (Z_to_bv 64 bits) (Z_to_bv 64 DST)
             (Z_to_bv 64 (DST + j)) (Z_to_bv 64 64) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 S) (Z_to_bv 64 (DT + 4))
             (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (2^61)) (Z_to_bv 64 (2^16 - 1)) (Z_to_bv 64 ptr)
             (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (-5)) (Z_to_bv 64 (DST + dcap - 3)) x21 x22 x23 x24 x25 x26 x27
             (Z_to_bv 64 cont) (Z_to_bv 64 1) (Z_to_bv 64 (-3)) (Z_to_bv 64 (-4)))
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Ltac fm_fix17 q p := let v := reg_val 17%Z in lazymatch v with Z_to_bv 64 ?e =>
    let E := fresh "E17" in
    first [ assert (E : e = S + (p - q)) by (fd_clr; fm_zn; lia)
          | assert (E : e = S + 0) by (fd_clr; fm_zn; lia) ];
    rewrite E in * end.

  Ltac fm_src := let v := reg_val 17%Z in lazymatch v with Z_to_bv 64 (S + ?pp) =>
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with SB : bytes_at usegs mm S (map (Z_to_bv 8) bs) |- _ =>
      pose proof (src_rd usegs mm S bs (pp + 0) SB ltac:(fd_clr; fm_zn; lia)) as B0;
      pose proof (src_rd usegs mm S bs (pp + 1) SB ltac:(fd_clr; fm_zn; lia)) as B1;
      pose proof (src_rd usegs mm S bs (pp + 2) SB ltac:(fd_clr; fm_zn; lia)) as B2;
      pose proof (src_rd usegs mm S bs (pp + 3) SB ltac:(fd_clr; fm_zn; lia)) as B3;
      pose proof (src_rd usegs mm S bs (pp + 4) SB ltac:(fd_clr; fm_zn; lia)) as B4;
      pose proof (src_rd usegs mm S bs (pp + 5) SB ltac:(fd_clr; fm_zn; lia)) as B5;
      pose proof (src_rd usegs mm S bs (pp + 6) SB ltac:(fd_clr; fm_zn; lia)) as B6;
      pose proof (src_rd usegs mm S bs (pp + 7) SB ltac:(fd_clr; fm_zn; lia)) as B7 end end end.

  Definition fm_box (P : Prop) : Prop := P.

  Ltac fm_tb := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with
    | T : bytes_at usegs mm (DT + 4) _ |- _ => idtac
    | MU : munch [(SP + 16, SP + 88); (DST, DST + dcap)] ?ma mm, T0 : fm_box (bytes_at usegs ?ma (DT + 4) _) |- _ =>
        let T := fresh "TBM" in
        assert (T : bytes_at usegs mm (DT + 4) (concat (map fse_cell_bytes (dt_cells dt))))
          by (apply (bytes_at_transport usegs _ ma mm (DT + 4) _ T0 MU); rewrite fse_cells_length; cbn [disjoint_from];
              lia)
    end end.
  Definition PFM_LD : Z := 0x20218.

  Ltac fm_mc := unfold fdw_mem, sm_inv, bitdz_cells; cbn [de_out de_s1 de_s2 de_bd bd_cont bd_bits bd_ptr bd_zero];
    repeat match goal with |- _ /\ _ => split end;
    try first [ eassumption | (eexists; split; eassumption) | (eapply munch_trans; eassumption)
          | (eapply wmono_trans; eassumption) ].

  Lemma fm_load : forall m1 out s1 s2 c cf b p jp fl (y1 y22 y23 y24 y25 y26 y27 : word),
    0 <= b <= 64 -> 0 <= p -> p + 8 <= zlen bs -> (fl = 0 \/ fl = 1) ->
    zlen out <= dcap -> Forall (fun v => 0 <= v < 256) out ->
    0 <= s1 < 2^(dt_tableLog dt) -> 0 <= s2 < 2^(dt_tableLog dt) ->
    fdw_mem m0 m1 SP S DT DST dcap lo bs dt (mkDec out s1 s2 (mkBD cf b p false)) jp ->
    (fl = 1 -> zlen out < dcap - 3 ->
       forall m2 (z22 z23 z24 z25 z26 z27 : word),
       fdw_mem m0 m2 SP S DT DST dcap lo bs dt (mkDec out s1 s2 (mkBD (le64v bs p) b p false)) jp ->
       evt usegs POST (SL3 PFDW_D m2 y1 s1 s2 b (zlen out) (S + p) (Z_to_bv 64 1) z22 z23 z24 z25 z26 z27 (le64v bs p))) ->
    (fl = 0 \/ dcap - 3 <= zlen out ->
       fdw_t2_K SP gp tp F fc m0 S DT DST dcap lo bs dt POST (mkDec out s1 s2 (mkBD (le64v bs p) b p false))) ->
    evt usegs POST (SL3 PFM_LD m1 y1 s1 s2 b (zlen out) (S + p) (Z_to_bv 64 fl) y22 y23 y24 y25 y26 y27 c).
  Proof.
    intros until y27. intros BR P0 PE FL OL OBY S1 S2 MEM KD KX.
    pose proof PRE as PRE'.
    destruct PRE' as (HTL & HCL & HCOK & HBY & HLO & HSP16 & HSPT & HS8 & HSE & HDT0 & HDT4 & HDTE & HD4 & HDE & HDC
                     & DJ1 & DJ2 & DJ3).
    unfold fdw_mem in MEM. cbn [de_out de_s1 de_s2 de_bd bd_cont bd_bits bd_ptr bd_zero] in MEM.
    destruct MEM as (FS2 & FS1 & FBD & ((junk & OUTA & LJ) & MU & WM & MI) & TBB & SRCB & STK).
    unfold bitdz_cells in FBD. cbn [bd_cont bd_bits bd_ptr bd_zero] in FBD.
    pose proof (munch_refl [(SP + 16, SP + 88); (DST, DST + dcap)] m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
    assert (TB0 : fm_box (bytes_at usegs m1 (DT + 4) (concat (map fse_cell_bytes (dt_cells dt))))) by exact TBB.
    unfold PFM_LD.
    fm_src. zstep.
    destruct FL as [-> | ->].
    all: repeat (fm_step 0; fd_brk; fm_ref).
    all: fm_step 0.
    all: let v := reg_val 28%Z in lazymatch v with Z_to_bv 64 ?e =>
      let E := fresh "EC" in
      assert (E : e = le64v bs p)
        by (unfold le64v; rewrite le64_lbu_raw by (apply byte_Znth; [exact HBY | lia]); rewrite ?Z.add_0_r; reflexivity);
      rewrite E in * end.
    all: unfold fdw_t2_K in KX.
    all: fm_tb.
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x2027c) _ _ _ _) => eapply KD; [reflexivity | fd_clr; lia | ]
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x20438) _ _ _ _) =>
          eapply KX; [first [left; reflexivity | right; fd_clr; lia] | | | ]
      end.
    all: lazymatch goal with
      | |- sm_okr _ _ _ =>
          unfold sm_okr, bitd_ok; cbn [de_out de_s1 de_s2 de_bd bd_cont bd_bits bd_ptr bd_zero];
          pose proof (le64v_range bs p HBY); repeat split; try lia; try exact OBY; intros; discriminate
      | |- st_ok _ _ => unfold st_ok; cbn [de_s1 de_s2]; lia
      | |- fdw_fmem _ _ _ _ _ _ _ _ _ _ _ _ => apply fdw_mem_fmem; fm_mc
      | |- fdw_mem _ _ _ _ _ _ _ _ _ _ _ _ => fm_mc
      end.
  Qed.

  Lemma fm_head : forall m1 out s1 s2 c bc p jp (y1 y21 y22 y23 y24 y25 y26 y27 : word) st d0,
    sm_ok dcap bs (mkDec out s1 s2 (mkBD c bc p false)) -> st_ok (dt_tableLog dt) (mkDec out s1 s2 (mkBD c bc p false)) ->
    fdw_mem m0 m1 SP S DT DST dcap lo bs dt (mkDec out s1 s2 (mkBD c bc p false)) jp ->
    reload_dstream bs (mkBD c bc p false) = Ok (st, d0) ->
    (dstatus_eqb st Unfinished && (zlen out <? dcap - 3) = true ->
       forall m2 (z22 z23 z24 z25 z26 z27 : word), fdw_mem m0 m2 SP S DT DST dcap lo bs dt (mkDec out s1 s2 d0) jp ->
       evt usegs POST (SL3 PFDW_D m2 y1 s1 s2 (bd_bits d0) (zlen out) (S + bd_ptr d0) (Z_to_bv 64 1)
                         z22 z23 z24 z25 z26 z27 (bd_cont d0))) ->
    (dstatus_eqb st Unfinished && (zlen out <? dcap - 3) = false ->
       fdw_t2_K SP gp tp F fc m0 S DT DST dcap lo bs dt POST (mkDec out s1 s2 d0)) ->
    evt usegs POST (SL3 PFDW_L3 m1 y1 s1 s2 bc (zlen out) (S + p) y21 y22 y23 y24 y25 y26 y27 c).
  Proof.
    intros until d0. intros OK ST MEM RL KD KX.
    pose proof PRE as PRE'.
    destruct PRE' as (HTL & HCL & HCOK & HBY & HLO & HSP16 & HSPT & HS8 & HSE & HDT0 & HDT4 & HDTE & HD4 & HDE & HDC
                     & DJ1 & DJ2 & DJ3).
    pose proof (fm_reload_ok bs _ _ _ HBY (proj1 OK) (proj1 (proj2 OK)) RL) as (BD0 & B640 & Z0 & U8).
    unfold sm_ok, bitd_ok, st_ok, fdw_mem in *. cbn [de_out de_s1 de_s2 de_bd bd_cont bd_bits bd_ptr bd_zero] in *.
    destruct OK as ((BC & BB0 & BP0 & BPE & BSM & _) & B64 & OL & OBY).
    destruct MEM as (FS2 & FS1 & FBD & ((junk & OUTA & LJ) & MU & WM & MI) & TBB & SRCB & STK).
    unfold bitdz_cells in FBD. cbn [bd_cont bd_bits bd_ptr bd_zero] in FBD.
    pose proof (munch_refl [(SP + 16, SP + 88); (DST, DST + dcap)] m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
    assert (QR : exists q r, bc = 8 * q + r /\ 0 <= q <= 8 /\ 0 <= r <= 7) by (exists (bc / 8), (bc mod 8); lia).
    destruct QR as (q & r & -> & Q1 & Q2).
    pose proof (y4_zx q r ltac:(lia) ltac:(lia)) as EZX.
    pose proof (y4_sh q r ltac:(lia) ltac:(lia)) as ESH.
    pose proof (y4_md q r ltac:(lia) ltac:(lia)) as EMD.
    unfold reload_dstream in RL. cbn [bd_cont bd_bits bd_ptr bd_zero] in RL.
    replace (64 <? 8 * q + r) with false in RL by (symmetry; apply Z.ltb_ge; lia).
    rewrite ESH in RL.
    assert (L8 : p <> 0 -> 8 <= zlen bs)
      by (intros; destruct (Z_lt_le_dec (zlen bs) 8) as [L|L]; [specialize (BSM L); lia | lia]).
    destruct (8 <=? p) eqn:P8; [apply Z.leb_le in P8 | apply Z.leb_gt in P8;
      destruct (p =? 0) eqn:P0; [apply Z.eqb_eq in P0 | apply Z.eqb_neq in P0;
        destruct (p - q <? 0) eqn:PN; [apply Z.ltb_lt in PN | apply Z.ltb_ge in PN]]].
    all: try (rewrite readLE64_ok in RL by lia; cbn [bind] in RL).
    all: try (lazymatch type of RL with context [if ?a <? 64 then _ else _] => destruct (a <? 64) end).
    all: injection RL as <- <-.
    all: cbn [dstatus_eqb andb bd_cont bd_bits bd_ptr bd_zero] in KD, KX, U8.
    all: try fold (le64v bs (p - q)) in KD, KX.
    all: try fold (le64v bs (p - p)) in KD, KX.
    all: try (replace (p - p) with 0 in KD, KX by lia).
    all: try (replace (8 * q + r - p * 8) with (8 * q + r - 8 * p) in KD, KX by lia).
    all: try (replace (8 * q + r - q * 8) with r in KD, KX by lia).
    all: try (replace (Z.land (8 * q + r) 7) with r in KD, KX by (rewrite fm_land7; lia)).
    all: assert (TB0 : fm_box (bytes_at usegs m1 (DT + 4) (concat (map fse_cell_bytes (dt_cells dt))))) by exact TBB.
    all: unfold PFDW_L3.
    all: repeat (fm_step 0; fd_brk; fm_ref).
    all: fm_step 0.
    all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x20218) _ _ _ _) => fm_fix7 q r p; fm_fix17 q p end).
    all: rewrite ?EMD in *.
    all: try (let v := reg_val 21%Z in lazymatch v with Z_to_bv 64 (Z.lxor (Z.b2z (?a <? ?b)) 1) =>
           let H := fresh "FL" in
           destruct (a <? b) eqn:H; [apply Z.ltb_lt in H | apply Z.ltb_ge in H];
           try change (Z.lxor (Z.b2z true) 1) with 0; try change (Z.lxor (Z.b2z false) 1) with 1;
           try (exfalso; fd_clr; rewrite ?ESH in *; fm_q; lia) end).
    all: fm_tb.
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x20218) _ _ _ _) =>
          eapply fm_load; [ lia | lia | lia | lia | lia | exact OBY | lia | lia | fm_mc
                          | intros FL1 OLT ? ? ? ? ? ? ? MEM2; first [exfalso; lia | apply KD; [apply Z.ltb_lt; lia | exact MEM2]]
                          | intros FLX; first [apply KX; reflexivity | apply KX; apply Z.ltb_ge; lia] ]
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x20438) _ _ _ _) =>
          unfold fdw_t2_K in KX; eapply KX; [reflexivity | | | apply fdw_mem_fmem; fm_mc]
      end.
    all: lazymatch goal with
      | |- sm_okr _ _ _ =>
          unfold sm_okr, bitd_ok; cbn [de_out de_s1 de_s2 de_bd bd_cont bd_bits bd_ptr bd_zero];
          repeat split; try lia; try exact OBY; intros; discriminate
      | |- st_ok _ _ => unfold st_ok; cbn [de_s1 de_s2]; lia
      end.
  Qed.

  Hypothesis FMB : fdw_fmb_stmt.

  Lemma fm_loop : forall f x r, main_loop bs dt dcap true f x = Ok r ->
    fdw_t2_K SP gp tp F fc m0 S DT DST dcap lo bs dt POST r -> fdw_l3_K SP gp tp F fc m0 S DT DST dcap lo bs dt POST x.
  Proof.
    induction f as [|f IH]; intros x r ML KT; [discriminate|].
    destruct x as [out s1 s2 [c bc p z]].
    intros m1 jp y1 y21 y22 y23 y24 y25 y26 y27 OK ST MEM.
    assert (z = false) as ->
      by (destruct z; [destruct OK as ((_ & _ & _ & _ & _ & ZB) & B64 & _); cbn in *; specialize (ZB eq_refl); lia
                      | reflexivity]).
    cbn [main_loop de_bd de_out de_s1 de_s2] in ML.
    destruct (reload_dstream bs (mkBD c bc p false)) as [[st d0]| | |] eqn:RL; cbn [bind] in ML; try discriminate.
    pose proof PRE as (HTL & HCL & HCOK & HBY & _).
    pose proof (fm_reload_ok bs _ _ _ HBY (proj1 OK) (proj1 (proj2 OK)) RL) as (BD0 & B640 & Z0 & U8).
    unfold FseNCount.Zlength in ML.
    apply (fm_head m1 out s1 s2 c bc p jp y1 y21 y22 y23 y24 y25 y26 y27 st d0 OK ST MEM RL).
    - intros CND m2 z22 z23 z24 z25 z26 z27 MEM2. rewrite CND in ML.
      apply andb_true_iff in CND as (CU & CL). apply Z.ltb_lt in CL.
      destruct st; try discriminate CU. specialize (U8 eq_refl).
      destruct d0 as [c0 b0 p0 z0]. cbn [bd_zero bd_bits bd_ptr bd_cont] in *. subst z0.
      destruct (decode_sym dt true s1 (mkBD c0 b0 p0 false)) as [[[o0 s1a] d1]| | |] eqn:D1; cbn [bind] in ML;
        try discriminate.
      destruct (decode_sym dt true s2 d1) as [[[o1 s2a] d2]| | |] eqn:D2; cbn [bind] in ML; try discriminate.
      destruct (decode_sym dt true s1a d2) as [[[o2 s1b] d3]| | |] eqn:D3; cbn [bind] in ML; try discriminate.
      destruct (decode_sym dt true s2a d3) as [[[o3 s2b] d4]| | |] eqn:D4; cbn [bind] in ML; try discriminate.
      unfold bitd_ok in BD0. cbn [bd_cont bd_bits bd_ptr bd_zero] in BD0.
      destruct OK as (_ & _ & OL & OBY). cbn [de_out] in OL, OBY. unfold st_ok in ST. cbn [de_s1 de_s2] in ST.
      refine (FMB SP gp tp F fc m0 S DT DST dcap lo bs dt POST m2 out s1 s2 c0 b0 p0 jp o0 s1a o1 s2a o2 s1b o3 s2b
                d1 d2 d3 d4 y1 z22 z23 z24 z25 z26 z27 PRE NB1 D1 D2 D3 D4 _ _ _ _ _ _ _ _ _ MEM2 (IH _ _ ML KT));
        first [lia | tauto | exact OBY].
    - intros CND. rewrite CND in ML. injection ML as <-. exact KT.
  Qed.
End FM.

Theorem fdw_l3_proof : fdw_l3_stmt.
Proof.
  unfold fdw_l3_stmt. intros SP gp tp F fc m0 S DT DST dcap lo bs dt POST f x r PRE NB ML KT.
  exact (fm_loop SP gp tp F fc m0 S DT DST dcap lo bs dt POST PRE NB fdw_fmb_proof f x r ML KT).
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
