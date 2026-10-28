(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep Frame.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel PjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer SjPjCont.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 RT_iface4 D_defs D_kit D_clx D_libiface I_lkit
     Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_hkit5A Atp_fzwA Pj_rtkA Pj_defsA Pj_cpsA Pj_copyA Pj_ser_defsA Pj_ser_kitA Pj_ser_callsA Pj_ser_trefA Pj_ser_ckitA
     Pj_ser_objkA Pj_ser_skitA Pj_ser_ncallsA Pj_ser_okitA Pj_ser_okey1A_b Pj_ser_okey1A_a Pj_ser_okey1A_e.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_store ::= first [ pj_solve_store0 | pj_store_wr ].
Local Ltac pj_st_eq_leaf ::=
  lazymatch goal with
  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity | f_equal; cbn [length sa_buf sa_size sa_cap]; lia]
  | |- _ => reflexivity
  end.
Notation wz z := (Z_to_bv 64 z) (only parsing).
Notation M64M1 := 18446744073709551615 (only parsing).
Ltac omucx OX := let c := omuc OX in exact c.
Ltac gok := let G := fresh "G" in zstep; if_cases G; zify_cond G; [try clear G| gref G].
Ltac unzx := zstep; zstep; zstep; unz; change (Z.lxor 1 0) with 1; gok.

Lemma lxor_ones64 : forall a, 0 <= a < 2 ^ 64 -> Z.lxor a 18446744073709551615 = 18446744073709551615 - a.
Proof.
  intros a Ha. rewrite (lnot_mod64 a Ha). unfold Z.lnot, Z.pred. change (2 ^ 64) with 18446744073709551616.
  Z.div_mod_to_equations. lia.
Qed.

Section OKey1.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis GROW : grow_cpsA RT PMc.
Notation aevt := (aevt RT PMc).

Section Pieces.
Variable E : pjenvA.
Variable D : nat.
Variable C : conI.
Variable f : Z.
Variable K : config -> Prop.
Variables (x c l x1 cx A X : Z).
Hypothesis OK : pjenvA_ok E.
Hypothesis CX : cctxA E D C.
Hypothesis OX : octxA E C f.
Hypothesis SER : ser_cpsA RT PMc D.
Hypothesis Hx : 2 <= x /\ x + 1 < x1 /\ x1 <= ci_e C.
Hypothesis HSTR : str_at (pa_S E) (pa_sn E) c l.
Hypothesis EL : elemS (pa_T E) (pa_S E) (pa_sn E) ck_any D (x + 1) x1 (c + l + 5) cx.
Hypothesis CXN : cx <= pa_sn E.
Hypothesis BUD : A + (3 + 6 * l) <= PJ_OUTMAX (pa_len E).
Hypothesis BUD2 : A + (3 + 6 * l) <= 41 * x + 6 * (c + l + 5) + 3.
Hypothesis X2 : 2 * (x1 - (x + 1)) <= X.
Hypothesis X0 : 0 <= X.
Hypothesis HK : forall (Σ' : rts RT) (st' : sbA) (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (y24 y32 y40 y72 y104 y112 y120 y136 y224 y232 : word)
            (yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys6 ys7 ys9 yt3 yt4 yt5 yt6 : word),
    CERMA RT E C (obj_frp E C f (owK E C f y24 y32 y40 (wz (x - 1)) (wz (pa_DOC E + 8)) y72 (wz (pa_DOC E)) (wz 72057594037927935) (wz ((pa_DOC E + 8) / 8 + 2147450880)) y104 y112 y120
                                    (wz (f + 64)) y136 (wz PJ_ESC_TAB_A) (wz PJ_RO184_A) (wz PJ_RO176_A) (wz (pa_SB E)) y224 y232) obj_shpatA) Σ' st' m' ->
    frm0 fc' -> sb_accA st' x1 cx -> CCREDA RT E C Σ' (X - 2 * (x1 - (x + 1))) st' ->
    aevt Σ' K (OST E C 0xbc88c yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 (wz (pa_DOC E)) (wz (18446744073709551615 - PJ_NE_TAB_A)) (wz (x + 1)) ys6 ys7 ys9
                   (wz PJ_NE_TAB_A) (wz (pa_SB E)) yt3 yt4 yt5 yt6 F' fc' m').

Notation DATA := (pa_SBUF E + c + 4).
Notation ok1c := (Pj_ser_okey1A_a.ok1c E C f x c).

Definition hx (x24 x32 x40 x72 x104 x120 x128 x136 x144 x152 x160 x176 x224 x232 : word) : owA :=
  owK E C f x24 x32 x40 (wz (x - 1)) (wz (pa_DOC E + 8)) x72 (wz (pa_DOC E)) (wz 72057594037927935) (wz ((pa_DOC E + 8) / 8 + 2147450880)) x104 (wz DATA) x120
      x128 x136 x144 x152 x160 x176 x224 x232.
Notation okc x24 x32 x72 x120 x136 x144 x152 x160 x224 x232 := (hx x24 x32 (wz (x + 1)) x72 (wz (f + 32)) x120 (wz (f + 64)) x136 x144 x152 x160 (wz (pa_SB E)) x224 x232).
Notation CERMP x24 x32 x72 x120 x136 x144 x152 x160 x224 x232 shp Σ st m := (CERMA RT E C (obj_frp E C f (okc x24 x32 x72 x120 x136 x144 x152 x160 x224 x232) shp) Σ st m).

Notation O1P pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs7 xt3 xt4 xt5 F fc m :=
  (OST E C pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (M64M1 - PJ_NE_TAB_A)) xs5 (Z_to_bv 64 l) xs7 (Z_to_bv 64 DATA) (Z_to_bv 64 PJ_NE_TAB_A)
       (Z_to_bv 64 (pa_SB E)) xt3 xt4 xt5 (Z_to_bv 64 (shad (pa_SB E + 72))) F fc m).

Notation KH1 pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xt3 xt4 xt5 F fc m :=
  (OST E C pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (pa_SBUF E)) (Z_to_bv 64 DATA) (Z_to_bv 64 c) (Z_to_bv 64 (pa_S E (c + 1)))
       (Z_to_bv 64 (pa_S E (c + 2))) (Z_to_bv 64 (pa_S E (c + 3))) (Z_to_bv 64 (pa_SB E)) xt3 xt4 xt5 (Z_to_bv 64 (shad (pa_SB E + 72))) F fc m).
Local Ltac slia := repeat match goal with H : _ \/ _ |- _ => clear H end; cbn [sa_size sa_cap sa_buf sa_heap sa_k]; lia.
Local Ltac sb_shz :=
  lazymatch goal with
  | HREF : CREFA _ _ _ _ _ ?mr, MU : munch _ ?mr ?mm, WM : wmono bsegs ?mr ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let SHZ := fresh "SHZ" in let R64 := fresh "RD64" in let R72 := fresh "RD72" in let R80 := fresh "RD80" in
    let MUc := omuc OX in
    pose proof (shz_sb_muC RT AF E D C OK CX _ _ _ mm HREF MUc WM) as SHZ;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 64) ltac:(clear; lia)) as R64;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 72) ltac:(clear; lia)) as R72;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 80) ltac:(clear; lia)) as R80; clear SHZ
  end.
Local Ltac shf_fold := match goal with SHF : rw_cells bsegs ?m (?g / 8 + 2147450880) ?cs, SHL : length ?shp = 16%nat |- _ =>
  change (rw_cells bsegs m (g / 8 + 2147450880) cs) with (rw_cells bsegs m (g / 8 + 2147450880) (sh16 shp)) in SHF | _ => idtac end.
Local Ltac open HSM := unfold Pj_ser_okey1A_a.ok1c, hx in HSM; obj_open HSM OK CX OX.
Local Ltac oclose HSM := shf_fold; match goal with OXh : octxA _ _ _ |- _ => obj_close HSM OXh end.
Notation esc_headA := (Pj_ser_okey1A_e.esc_headA RT AF RC PMc FDO MST GROW E D C f K x c l x1 cx A X OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK).
Notation okey_closeA := (Pj_ser_okey1A_a.okey_closeA RT AF RC PMc FDO MST GROW E D C f K x c l x1 cx A X OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK).
Notation okey1_scan8A := (Pj_ser_okey1A_b.okey1_scan8A E D C f c l OK CX OX HSTR).
Notation okey1_tailA := (Pj_ser_okey1A_b.okey1_tailA E D C f c l OK CX OX HSTR).

Lemma copy_finA : forall (k : Z) x24 x32 x72 x120 x136 x144 x152 x160 x224 x232 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xt3 xt4 xt5 xt6 : word),
  0 <= k <= l ->
  CERMP x24 x32 x72 x120 x136 x144 x152 x160 x224 x232 obj_shpatA Σ st m -> frm0 fc -> sa_size st + k <= sa_cap st -> sa_size st <= A + 1 -> CCREDA RT E C Σ X st ->
  aevt Σ K (OST E C 0xbc1d4 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (sa_size st + k)) (wz (M64M1 - PJ_NE_TAB_A)) xs5 (wz l) (wz k) (wz DATA)
                 (wz PJ_NE_TAB_A) (wz (pa_SB E)) xt3 xt4 xt5 xt6 F fc m).
Proof using AF RC FDO MST GROW OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK.
  intros k x24 x32 x72 x120 x136 x144 x152 x160 x224 x232 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xt3 xt4 xt5 xt6 HKL HSM FRM ROOM ACC CR.
  pose proof HSTR as (C0 & L0 & CL & _).
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ostr_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM.

  step. sb_shz. astep. astep. unbox FSB; unbox SHSB. step. box_disj.

  zstep. zstep. zstep. zstep. change (Z_to_bv 64 145888) with (Z_to_bv 64 PJ_RO176_A). step.
  zstep. change (Z_to_bv 64 145856) with (Z_to_bv 64 PJ_RO184_A). step.
  zstep. change (Z_to_bv 64 146304) with (Z_to_bv 64 PJ_ESC_TAB_A). step.

  step. if_cases Kc; zify_cond Kc; pjnorm_in Kc.
  -
    oclose HSM2. apply evt_done.
    eapply aevt_eq; [| eapply (okey_closeA x24 x32 x72 x120 x136 x224 x232 Σ (mkSbA buf (size + k) cap hp kk))]; try eassumption; try pj_st_eq; slia.
  -
    step. zstep. zstep. step. zstep. step. step. zstep. step. zstep. zstep.
    rewrite (lxor_ones64 (f + 33)) by (change (2 ^ 64) with 18446744073709551616; clear - F0 FLO LB QT OBQ; lia). step.
    oclose HSM2. apply evt_done.
    eapply aevt_eq; [| eapply (esc_headA (Z.to_nat (l - k)) k x24 x32 x224 x232 Σ (mkSbA buf (size + k) cap hp kk))]; try eassumption; try pj_st_eq;
      cbn [sa_size]; clear - HKL Kc ACC; lia.
Qed.

Lemma copy_tailA : forall (k : Z) x24 x32 x72 x120 x136 x144 x152 x160 x224 x232 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xt3 xt4 xt5 : word),
  0 <= k <= l ->
  CERMP x24 x32 x72 x120 x136 x144 x152 x160 x224 x232 obj_shpatA Σ st m -> frm0 fc -> sa_size st + k <= sa_cap st -> sa_size st <= A + 1 -> CCREDA RT E C Σ X st ->
  aevt Σ K (O1P 0xbc180 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (sa_size st + k)) xs5 (wz k) xt3 xt4 xt5 F fc m).
Proof using AF RC FDO MST GROW OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK.
  intros k x24 x32 x72 x120 x136 x144 x152 x160 x224 x232 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xt3 xt4 xt5 HKL HSM FRM ROOM ACC CR.
  pose proof HSTR as (C0 & L0 & CL & _).
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ostr_envA OK CX OX. apply (aevt_evt RT AF PMc MST). pose proof HSM as HSM0. open HSM. sb_shz.

  step. astep. astep. astep. astep.

  step. step. step. zstep. try (replace (size + buf) with (buf + size) by (clear; lia)).

  gok. unzx.

  zstep. zstep. zstep.
  pose proof (cont_sbuf_srcA RT AF E D C Σ _ m (c + 4) k OK CX (proj1 HSM0) ltac:(clear - C0; lia) ltac:(clear - HKL; lia) ltac:(clear - CL HKL; lia))
    as (src & SRC & SRCL & SAC & SRG & S0' & SLO).
  replace (pa_SBUF E + c + 4) with (pa_SBUF E + (c + 4)) by (clear; lia).
  oclose HSM2. apply evt_done.
  eapply aevt_eq; [| eapply (cont_copyhA RT AF RC PMc FDO MST E D C _ Σ (mkSbA buf size cap hp kk) m K (pa_SBUF E + (c + 4)) k 0xbc1d4 src)];
    [pj_st_eq; clear; lia| exact OK| exact CX| apply obj_frp_local; exact OX| exact HSM2| exact SRC| exact SRCL| clear - HKL; lia| cbn [sa_size sa_cap]; exact ROOM
    | intros _; split; [exact SAC| exact SRG]| clear - SR C0; lia| exact SLO| clear; lia| reflexivity|].
  intros m' F' yt0 yt1 yt2 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CPY.
  replace (pa_SBUF E + (c + 4)) with (pa_SBUF E + c + 4) by (clear; lia).
  eapply aevt_eq; [| eapply (copy_finA k x24 x32 x72 x120 x136 x144 x152 x160 x224 x232 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
Qed.

Lemma okey1_copyA : forall (k : Z) x24 x32 x72 x120 x136 x144 x152 x160 x224 x232 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xt3 xt4 xt5 : word),
  0 <= k <= l ->
  CERMP x24 x32 x72 x120 x136 x144 x152 x160 x224 x232 obj_shpatA Σ st m -> frm0 fc -> sa_size st <= A + 1 -> CCREDA RT E C Σ X st ->
  aevt Σ K (O1P 0xbc12c xra xt0 xt1 xt2 xa0 xa1 (wz (M64M1 - DATA)) xa3 xa4 xa5 xa6 xa7 xs2 xs5 (wz k) xt3 xt4 xt5 F fc m).
Proof using AF RC FDO MST GROW OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK.
  intros k x24 x32 x72 x120 x136 x144 x152 x160 x224 x232 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xt3 xt4 xt5 HKL HSM FRM ACC CR.
  pose proof HSTR as (C0 & L0 & CL & _).
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ostr_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM. sb_shz.

  gok. astep. astep. step. astep. step. astep.

  step. step. step. zstep. step.
  if_cases Kc; zify_cond Kc; pjnorm_in Kc.
  -
    oclose HSM2. apply evt_done.
    eapply aevt_eq; [| eapply (copy_tailA k x24 x32 x72 x120 x136 x144 x152 x160 x224 x232 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
  -
    zstep. pjnorm. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 _ ?mm _) =>
    assert (GROWN : forall (z : Z) (ya2 : word), z = Z.max (2 * cap) (size + k) ->
      evt bsegs (fun ms' => aevt Σ K ms')
        (O1P 0xbc178 xra xt0 xt1 xt2 (wz (pa_SB E)) (wz z) ya2 xa3 xa4 xa5 xa6 xa7 (wz (size + k)) xs5 (wz k) xt3 xt4 xt5 F0 fc0 mm)) end.
    { intros z ya2 EZ.

      zstep.
      oclose HSM3. apply evt_done.
      eapply aevt_eq; [| eapply (cont_growA RT AF PMc GROW E D C _ Σ (mkSbA buf size cap hp kk) _ K z X 0xbc17c)];
        [pj_st_eq| exact OK| exact CX| apply obj_frp_local; exact OX| exact HSM3| | exact CR| exact X0| clear; lia| reflexivity|].
      { rewrite EZ. eapply (cont_req_okA RT E D C); [exact OK| exact CX| exact HSM3| cbn [sa_cap]; clear - Kc; lia|].
        cbn [sa_size]. clear - ACC BUD HKL. lia. }
      intros Σ' NEW m' F' yt0 yt1 yt2 za0 za1 za2 za3 za4 za5 za6 za7 yt3 yt4 yt5 yt6 HSM4 CR4.
      apply (aevt_evt RT AF PMc MST). open HSM4.

      step. shfold.
      oclose HSM5. apply evt_done.
      eapply aevt_eq; [| eapply (copy_tailA k x24 x32 x72 x120 x136 x144 x152 x160 x224 x232 Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW z))]; try eassumption; try pj_st_eq;
        unfold sb_grownA; cbn [sa_size sa_cap sa_buf sa_heap sa_k]; rewrite ?EZ; clear - Kc ACC SZ HKL; lia. }
    if_cases K2; zify_cond K2; pjnorm_in K2.
    + eapply evt_eq; [| eapply (GROWN (size + k))]; [pj_st_eq| clear - K2 Kc; lia].
    +   zstep. eapply evt_eq; [| eapply (GROWN (2 * cap))]; [pj_st_eq| clear - K2 Kc; lia].
Qed.

Lemma okey1_hjoinA : forall x24 x32 x40 x72 x104 x120 x128 x136 x144 x152 x160 x224 x232 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 : word),
  CERMA RT E C (obj_frp E C f (hx x24 x32 x40 x72 x104 x120 x128 x136 x144 x152 x160 (wz (pa_SB E)) x224 x232) obj_shpatA) Σ st m ->
  frm0 fc -> 1 <= sa_size st -> sa_size st <= A + 1 -> CCREDA RT E C Σ X st ->
  aevt Σ K (KH1 0xbbd58 xra xt0 xt1 xt2 (wz (sa_buf st + (sa_size st - 1))) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (pa_S E c)) xt3 xt4 xt5 F fc m).
Proof using AF RC FDO MST GROW OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK.
  intros x24 x32 x40 x72 x104 x120 x128 x136 x144 x152 x160 x224 x232 Σ st m F fc xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 HSM FRM SZ1 ACC CR.
  pose proof HSTR as (C0 & L0 & CL & LE & _). unfold le32 in LE.
  pose proof (S_rangeA E c OK) as BR0. pose proof (S_rangeA E (c + 1) OK) as BR1. pose proof (S_rangeA E (c + 2) OK) as BR2. pose proof (S_rangeA E (c + 3) OK) as BR3.
  set (b0 := pa_S E c) in *. set (b1 := pa_S E (c + 1)) in *. set (b2 := pa_S E (c + 2)) in *. set (b3 := pa_S E (c + 3)) in *.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ostr_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM.
  pose proof (obuf_factsA RT AF E D C OK CX f Σ _ _ OX HREF) as (_ & _ & _ & _ & APB). cbn [sa_buf sa_cap] in APB.
  pose proof (APB (buf + (size - 1)) ltac:(clear - SZ1 SZ; lia)) as (A1 & A2 & A3 & A4). clear APB.

  zstep. zstep. zstep. zstep. step. step. pj_store_done.

  step. zstep. step. zstep. step. zstep. step. zstep. replace (x - 1 + 2) with (x + 1) by (clear; lia). step.

  zstep. step. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  assert (M1 : Z.modulo (Z.shiftl b1 8) 18446744073709551616 = Z.shiftl b1 8) by (rewrite Z.shiftl_mul_pow2 by lia; apply Z.mod_small; clear - BR1; lia).
  assert (M2 : Z.modulo (Z.shiftl b2 16) 18446744073709551616 = Z.shiftl b2 16) by (rewrite Z.shiftl_mul_pow2 by lia; apply Z.mod_small; clear - BR2; lia).
  assert (M3 : Z.modulo (Z.shiftl b3 24) 18446744073709551616 = Z.shiftl b3 24) by (rewrite Z.shiftl_mul_pow2 by lia; apply Z.mod_small; clear - BR3; lia).
  rewrite ?M1, ?M2, ?M3. clear M1 M2 M3.
  rewrite ?pj_land64 by (rewrite Z.shiftl_mul_pow2 by lia; clear - BR1 BR2 BR3; lia).
  rewrite lor4_le32 by lia.
  replace (b0 + 2 ^ 8 * b1 + 2 ^ 16 * b2 + 2 ^ 24 * b3) with l by (clear - LE; lia).
  rewrite (lxor_ones64 DATA) by (change (2 ^ 64) with 18446744073709551616; clear - S0 SL C0 CL L0 LB QT OBQ; lia).
  unfold PJ_NE_TAB_A in *. try rewrite (lxor_ones64 146048) by (clear; lia).
  replace (pa_SBUF E + (c + 4)) with (pa_SBUF E + c + 4) by (clear; lia).

  pose proof (shz_sbuf_muC RT AF E D C OK CX Σ _ _ _ HREF ltac:(omucx OX) WM) as SHS.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (shz_tabs_muC RT AF E D C OK CX Σ _ _ mm HREF ltac:(omucx OX) WM) as SHTB end.
  assert (F1 : l - 8 * 0 < Z.of_nat (S (Z.to_nat l))) by (clear - L0; lia).
  assert (F2 : 0 <= 0) by (clear; lia). assert (F3 : 8 * 0 <= l) by (clear - L0; lia).
  eapply evt_eq; [| eapply (okey1_scan8A (S (Z.to_nat l)) 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 F2 F3 SHS SHTB MI
                               (fun o Ho => sbuf_read_muC RT AF E D C OK CX Σ _ _ _ o HREF ltac:(omucx OX) WM Ho))]; [pj_st_eq|]. clear F1 F2 F3.
  intros k8 ya0 ya1 ya3 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 HK8.

  zstep. if_cases Kc; zify_cond Kc; pjnorm_in Kc.
  -
    oclose HSM2. apply evt_done.
    eapply aevt_eq; [| eapply (okey1_copyA k8 x24 x32 x72 x120 x136 x144 x152 x160 x224 x232 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
  -
    assert (F1 : l - k8 <= Z.of_nat (S (Z.to_nat l))) by (clear - HK8 Kc; lia). assert (F2 : 0 <= k8 < l) by (clear - HK8 Kc; lia).
    eapply evt_eq; [| eapply (okey1_tailA (S (Z.to_nat l)) k8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 F2 SHS SHTB MI
                                 (fun o Ho => sbuf_read_muC RT AF E D C OK CX Σ _ _ _ o HREF ltac:(omucx OX) WM Ho))]; [pj_st_eq|]. clear F1 F2.
    intros k' za0 za1 za3 HK'.
    oclose HSM2. apply evt_done.
    eapply aevt_eq; [| eapply (okey1_copyA k' x24 x32 x72 x120 x136 x144 x152 x160 x224 x232 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq;
      clear - HK' HK8 ACC; cbn [sa_size]; lia.
Qed.

Lemma okey1_htailA : forall (x24 x32 x40 x72 x104 x120 x128 x136 x144 x152 x160 x176 x224 x232 : word) (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 : word),
  CERMA RT E C (obj_frp E C f (hx x24 x32 x40 x72 x104 x120 x128 x136 x144 x152 x160 x176 x224 x232) obj_shpatA) Σ st m ->
  frm0 fc -> sa_size st + 1 <= sa_cap st -> sa_size st <= A -> CCREDA RT E C Σ X st ->
  aevt Σ K (KH1 0xbbce8 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (pa_S E c)) xt3 xt4 xt5 F fc m).
Proof using AF RC FDO MST GROW OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK.
  intros x24 x32 x40 x72 x104 x120 x128 x136 x144 x152 x160 x176 x224 x232 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 HSM FRM ROOM ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ostr_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM. sb_shz.

  step. astep. astep. astep. astep.

  step. step. step. zstep. zstep. unbox FSB; unbox SHSB. step. box_disj.

  gok. unzx. gok. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (acc_buf_muC RT AF E D C OK CX Σ _ _ mm HREF ltac:(omucx OX) WM) as ACCB end.
  cbn [sa_buf sa_cap] in ACCB.
  destruct (acc_read1 _ _ _ (buf + size) ACCB ltac:(clear - ROOM SZ; lia)) as (b & RDB & SOK). clear ACCB.
  change (wa ((buf + size) / 8 + 2147450880)) with (wa (shad (buf + size))) in RDB.

  zstep. pjnorm. zstep. shfold. zstep.
  oclose HSM2.
  destruct (pj_sh_ok_cases b (buf + size) SOK) as [-> | (k & -> & K17 & KM)].
  -
    rewrite sxb_z8. zstep. if_true. apply evt_done.
    eapply aevt_eq; [| eapply (okey1_hjoinA x24 x32 x40 x72 x104 x120 x128 x136 x144 x152 x160 x224 x232 Σ (mkSbA buf (size + 1) cap hp kk))]; try eassumption; try pj_st_eq; slia.
  -
    rewrite (pj_sxb_small7 k) by (clear - K17; lia). zstep.
    if_cases Kc; zify_cond Kc; [exfalso; pjnorm_in Kc; clear - Kc K17; lia| clear Kc].
    zstep. zstep. pjnorm. rewrite pj_land7 by (clear - R0 SZ; lia).
    zstep. if_cases Kc; zify_cond Kc;
      [exfalso; rewrite !pj_signed_small in Kc by (clear - K17; Z.div_mod_to_equations; lia); clear - Kc K17 KM; lia| clear Kc].
    zstep. apply evt_done.
    eapply aevt_eq; [| eapply (okey1_hjoinA x24 x32 x40 x72 x104 x120 x128 x136 x144 x152 x160 x224 x232 Σ (mkSbA buf (size + 1) cap hp kk))]; try eassumption; try pj_st_eq; slia.
Qed.

End Pieces.
Local Ltac shf_fold := match goal with SHF : rw_cells bsegs ?m (?g / 8 + 2147450880) ?cs, SHL : length ?shp = 16%nat |- _ =>
  change (rw_cells bsegs m (g / 8 + 2147450880) cs) with (rw_cells bsegs m (g / 8 + 2147450880) (sh16 shp)) in SHF | _ => idtac end.

Local Ltac hbE E D C OK CX OX c k :=
  let G := fresh "G" in let G2 := fresh "G" in let RD := fresh "RD" in
  lazymatch goal with
  | HREF : CREFA _ _ _ _ _ ?mr, WM : wmono bsegs ?mr ?mm, C0 : 0 <= c, CL : c + ?l + 5 <= _, L0 : 0 <= ?l |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (G : 0 <= c + k < pa_sn E) by (clear - C0 CL L0; lia);
    assert (G2 : pa_SBUF E + c + k = pa_SBUF E + (c + k)) by (clear; lia);
    let MUc := omuc OX in
    pose proof (read1_at mm _ _ (sbuf_read_muC RT AF E D C OK CX _ _ _ mm _ HREF MUc WM G) _ G2) as RD; clear G G2; astep; clear RD
  end.
Local Ltac sb_shzE E D C OK CX OX :=
  lazymatch goal with
  | HREF : CREFA _ _ _ _ _ ?mr, MU : munch _ ?mr ?mm, WM : wmono bsegs ?mr ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let SHZ := fresh "SHZ" in let R64 := fresh "RD64" in let R72 := fresh "RD72" in let R80 := fresh "RD80" in
    let MUc := omuc OX in
    pose proof (shz_sb_muC RT AF E D C OK CX _ _ _ mm HREF MUc WM) as SHZ;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 64) ltac:(clear; lia)) as R64;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 72) ltac:(clear; lia)) as R72;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 80) ltac:(clear; lia)) as R80; clear SHZ
  end.

Local Ltac trefE E D C OK CX OX Σ x Hx EN rpc HSMc HSMo :=
  shf_fold; obj_close HSMc OX;
  eapply evt_cut; [eapply (cont_trefA RT AF E D C _ Σ _ _ x); [exact OK| exact CX| apply obj_frp_local; exact OX| exact HSMc| clear - Hx EN; lia]|];
  cbv beta;
  let ms1 := fresh "ms" in let m1 := fresh "m" in let ya4 := fresh "ya4" in
  intros ms1 (m1 & ya4 & -> & HSMo); clear HSMc; rewrite (ret_pc_even rpc) by (clear; lia);
  obj_open HSMo OK CX OX.

Theorem okey1_proofA : okey1_stmtA RT PMc.
Proof using AF RC FDO MST GROW.
  unfold okey1_stmtA.
  intros E D C f K Σ st m F fc x c l x1 cx A X x24 x32 x40 x48 x56 x72 x80 x88 x96 x104 x112 x120 x128 x136 x144 x152 x160 x176 x224 x232
         xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs5 xs6 xs10 xt3 xt4 xt5 xt6 OK CX OX SER HSM FRM Hx2 Hx1 Hxe HT HSTR EL CXN ACC BUD2 BUD CR X2 HK.
  assert (Hx : 2 <= x /\ x + 1 < x1 /\ x1 <= ci_e C) by (clear - Hx2 Hx1 Hxe; lia).
  assert (X0 : 0 <= X) by (clear - X2 Hx1; lia).
  pose proof HSTR as (C0 & L0 & CL & LE & _). pose proof (cc_e E D C CX) as (I1 & IE & EN).
  pose proof (S_rangeA E c OK) as BR0. pose proof (S_rangeA E (c + 1) OK) as BR1. pose proof (S_rangeA E (c + 2) OK) as BR2. pose proof (S_rangeA E (c + 3) OK) as BR3.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ostr_envA OK CX OX. apply (aevt_evt RT AF PMc MST). obj_open HSM OK CX OX.

  zstep. zstep. zstep.
  trefE E D C OK CX OX Σ x Hx EN 0xbbb84 HSM1 HSM2.

  pose proof (shz_tape_muC RT AF E D C OK CX Σ _ _ _ HREF ltac:(omucx OX) WM) as SHTP.
  assert (G : pa_TAPE E <= pa_TAPE E + 8 * x < pa_TAPE E + 8 * pa_n E) by (clear - Hx EN; lia).
  pose proof (shz_rd _ _ _ SHTP _ G) as RD. clear G SHTP.
  astep. astep. astep. astep. clear RD.

  zstep. zstep. pjnorm. astep. step.
  pose proof (shz_doc_muC RT AF E D C OK CX Σ _ _ _ HREF ltac:(omucx OX) WM) as SHD.
  pose proof (shz_rd _ _ _ SHD (pa_DOC E + 8) ltac:(clear; lia)) as RD8. clear SHD.
  astep. astep. clear RD8.

  step.
  pose proof (doc_cells_muC RT AF E D C OK CX Σ _ _ _ HREF ltac:(omucx OX) WM) as DOCC.
  step. gok.

  pose proof (tape_read_muC RT AF E D C OK CX Σ _ _ _ x HREF ltac:(omucx OX) WM ltac:(clear - Hx EN; lia)) as RDT. rewrite HT in RDT.
  assert (C56 : 0 <= c < 2 ^ 56) by (clear - C0 CL SL S0 LB QT BQ L0; lia).
  assert (T8 : 0 <= t_str < 256) by (unfold t_str; clear; lia).
  pose proof (tword_range t_str c T8 C56) as TWR.
  step. clear RDT. zstep. zstep. pjnorm. lstep. zstep.
  rewrite ?(Z.mod_small (tword t_str c) 18446744073709551616) by (clear - TWR; lia).
  rewrite ?pj_land64 by (clear - TWR; lia).
  assert (EA : Z.land (tword t_str c) 72057594037927935 = c).
  { rewrite land_mask56 by (clear - TWR; lia). apply tval_tword. exact C56. }
  rewrite !EA.
  zstep. zstep. replace (pa_SBUF E + (c + 4)) with (pa_SBUF E + c + 4) by (clear; lia). gok. gok.

  step. zstep. zstep. zstep. clear DOCC.
  trefE E D C OK CX OX Σ x Hx EN 0xbbc00 HSM2 HSM3.

  pose proof (shz_tape_muC RT AF E D C OK CX Σ _ _ _ HREF ltac:(omucx OX) WM) as SHTP.
  assert (G : pa_TAPE E <= pa_TAPE E + 8 * x < pa_TAPE E + 8 * pa_n E) by (clear - Hx EN; lia).
  pose proof (shz_rd _ _ _ SHTP _ G) as RD. clear G SHTP.
  astep. astep. astep. astep. clear RD.

  pose proof (shz_doc_muC RT AF E D C OK CX Σ _ _ _ HREF ltac:(omucx OX) WM) as SHD.
  pose proof (shz_rd _ _ _ SHD (pa_DOC E + 8) ltac:(clear; lia)) as RD8. clear SHD.
  step. astep. step. astep. clear RD8.

  pose proof (tape_read_muC RT AF E D C OK CX Σ _ _ _ x HREF ltac:(omucx OX) WM ltac:(clear - Hx EN; lia)) as RDT. rewrite HT in RDT.
  pose proof (doc_cells_muC RT AF E D C OK CX Σ _ _ _ HREF ltac:(omucx OX) WM) as DOCC.
  step. clear RDT. step. step. clear DOCC. step. zstep.
  rewrite ?(Z.mod_small (tword t_str c) 18446744073709551616) by (clear - TWR; lia).
  rewrite ?pj_land64 by (clear - TWR; lia). rewrite !EA. clear EA T8.
  zstep. gok.

  zstep. zstep. zstep. unz. change (Z.lxor 1 0) with 1. gok. gok.

  pose proof (shz_sbuf_muC RT AF E D C OK CX Σ _ _ _ HREF ltac:(omucx OX) WM) as SHS.
  assert (G : pa_SBUF E <= pa_SBUF E + c < pa_SBUF E + pa_sn E) by (clear - C0 CL L0; lia).
  pose proof (shz_rd _ _ _ SHS _ G) as RD. clear G. astep. astep. astep. astep. clear RD.
  assert (G : pa_SBUF E <= pa_SBUF E + c + 3 < pa_SBUF E + pa_sn E) by (clear - C0 CL L0; lia).
  pose proof (shz_rd _ _ _ SHS _ G) as RD. clear G. astep. astep. astep. astep. astep. clear RD. clear SHS.

  step. sb_shzE E D C OK CX OX. astep. astep.

  step. step. clear RD64 RD72 RD80. sb_shzE E D C OK CX OX. astep. astep. clear RD64 RD72 RD80.

  step. step. step.
  hbE E D C OK CX OX c 0. hbE E D C OK CX OX c 1. hbE E D C OK CX OX c 2. hbE E D C OK CX OX c 3.
  replace (pa_S E (c + 0)) with (pa_S E c) by (f_equal; clear; lia). pjnorm.

  zstep. step.
  if_cases Kc; zify_cond Kc; pjnorm_in Kc.
  -
    shf_fold. obj_close HSM4 OX. apply evt_done.
    eapply aevt_eq; [| eapply (okey1_htailA E D C f K x c l x1 cx A X OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK _ _ _ _ _ _ _ _ _ _ _ _ _ _ Σ (mkSbA buf size cap hp kk))];
      try eassumption; try pj_st_eq; cbn [sa_size sa_cap]; clear - Kc ACC; lia.
  -
    zstep. pjnorm. zstep. zstep.
    shf_fold. obj_close HSM4 OX. apply evt_done.
    eapply aevt_eq; [| eapply (cont_growA RT AF PMc GROW E D C _ Σ (mkSbA buf size cap hp kk) _ K (2 * cap) X 0xbbce4)];
      [pj_st_eq| exact OK| exact CX| apply obj_frp_local; exact OX| exact HSM4| | exact CR| exact X0| clear; lia| reflexivity|].
    { eapply (cont_req_ok2A RT E D C); [exact OK| exact CX| exact HSM4|]. cbn [sa_cap sa_size] in *. clear - Kc ACC BUD L0. lia. }
    intros Σ' NEW m' F' zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 HSM5 CR5.
    apply (aevt_evt RT AF PMc MST). obj_open HSM5 OK CX OX.

    step. shfold.
    shf_fold. obj_close HSM6 OX. apply evt_done.
    eapply aevt_eq; [| eapply (okey1_htailA E D C f K x c l x1 cx A X OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK _ _ _ _ _ _ _ _ _ _ _ _ _ _ Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW (2 * cap)))];
      try eassumption; try pj_st_eq; unfold sb_grownA; cbn [sa_size sa_cap sa_buf sa_heap sa_k]; clear - Kc ACC SZ R1; lia.
Qed.

End OKey1.

Theorem okey1_okA : forall (RT : rt_sig), art_facts RT -> rt_contracts RT -> forall PMc : Model -> Prop, fdfs_only PMc -> mat_stable PMc ->
  grow_cpsA RT PMc -> okey1_stmtA RT PMc.
Proof. intros RT AF RC PMc FDO MST GROW. exact (okey1_proofA RT AF RC PMc FDO MST GROW). Qed.
