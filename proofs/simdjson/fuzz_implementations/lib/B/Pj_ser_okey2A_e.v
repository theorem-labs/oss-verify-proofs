(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep Frame.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel PjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjPjCont.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 RT_iface4 D_defs D_kit D_clx D_libiface I_lkit
     Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_hkit5A Atp_fzwA Pj_rtkA Pj_defsA Pj_cpsA Pj_copyA Pj_ser_defsA Pj_ser_kitA Pj_ser_callsA Pj_ser_trefA Pj_ser_ckitA
     Pj_ser_objkA Pj_ser_skitA Pj_ser_ncallsA Pj_ser_okitA Pj_ser_okey2A_a.
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

Definition shpO2 : list byte := map (Z_to_bv 8) [0xf1; 0xf1; 0xf1; 0xf1; 0xf8; 0xf2; 0xf2; 0xf2; 0; 0xf3; 0xf3; 0xf3; 0; 0; 0; 0].
Lemma shpO2_g8 : nth_error shpO2 8 = Some z8.
Proof. reflexivity. Qed.

Lemma zb8_lit_m8 : Z_to_bv 8 (-8) = Z_to_bv 8 248.
Proof. apply bv_eq. reflexivity. Qed.

Lemma land255_small : forall x, 0 <= x < 256 -> Z.land x 255 = x.
Proof. intros x Hx. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma land255_m64 : forall y, Z.land (y mod 18446744073709551616) 255 = Z.land y 255.
Proof.
  intros y. change 255 with (Z.ones 8). rewrite !Z.land_ones by lia.
  symmetry. apply Znumtheory.Zmod_div_mod; [lia| lia|]. exists (2 ^ 56). reflexivity.
Qed.
Lemma land255_shl : forall y k, 8 <= k -> Z.land (Z.shiftl y k) 255 = 0.
Proof.
  intros y k Hk. rewrite Z.shiftl_mul_pow2 by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  replace (2 ^ k) with (2 ^ (k - 8) * 2 ^ 8) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite Z.mul_assoc. apply Z_mod_mult.
Qed.
Lemma land255_mul : forall y k, 8 <= k -> Z.land (y * 2 ^ k) 255 = 0.
Proof. intros y k Hk. rewrite <- Z.shiftl_mul_pow2 by lia. apply land255_shl. exact Hk. Qed.
Lemma land255_uw : forall y, Z.land (bv_unsigned (Z_to_bv 64 y)) 255 = Z.land y 255.
Proof. intros y. rewrite Z_to_bv_unsigned. unfold bv_wrap. apply land255_m64. Qed.
Ltac land255_simpl :=
  repeat first [ rewrite land255_uw | rewrite land255_m64 | rewrite Z.land_lor_distr_l | rewrite land255_shl by lia | rewrite land255_mul by lia
               | rewrite Z.lor_0_l | rewrite Z.lor_0_r ].

Section OKeyE.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis GROW : grow_cpsA RT PMc.
Notation aevt := (aevt RT PMc).

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
Hypothesis HK : forall (Σ' : rts RT) (st' : sbA) (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (y48 y72 y136 y224 y232 : word)
            (yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys5 ys9 yt3 yt4 yt5 yt6 : word),
    CERMA RT E C (obj_frp E C f (owK E C f (wz 4294967295) (wz 4294967297) (wz 67240448) y48 (wz (pa_DOC E + 8)) y72 (wz (pa_DOC E)) (wz 72057594037927935)
                                    (wz ((pa_DOC E + 8) / 8 + 2147450880)) (wz (x + 1)) (wz (f + 65)) (wz (18446744073709551615 - (f + 65))) (wz (f + 64)) y136
                                    (wz PJ_ESC_TAB_A) (wz PJ_RO184_A) (wz PJ_RO176_A) (wz (pa_SB E)) y224 y232) obj_shpatA) Σ' st' m' ->
    frm0 fc' -> sb_accA st' x1 cx -> CCREDA RT E C Σ' (X - 2 * (x1 - (x + 1))) st' ->
    aevt Σ' K (OST E C 0xbd6d4 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 (wz (pa_DOC E)) (wz (18446744073709551615 - PJ_NE_TAB_A)) ys5 (wz (x + 1)) (wz x) ys9
                   (wz PJ_NE_TAB_A) (wz (pa_SB E)) yt3 yt4 yt5 yt6 F' fc' m').

Notation DATA := (pa_SBUF E + c + 4).
Notation ok2w := (Pj_ser_okey2A_a.ok2w E C f x c).
Notation CERML x224 x232 shp Σ st m := (CERMA RT E C (obj_frp E C f (ok2w x224 x232) shp) Σ st m).
Notation O2S pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs6 xs9 xs7 xt3 xt4 xt5 xt6 F fc m :=
  (OST E C pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 (shad (pa_SB E + 72))) xa7 (Z_to_bv 64 DATA) (Z_to_bv 64 (M64M1 - PJ_NE_TAB_A)) (Z_to_bv 64 c) xs6 xs7
       xs9 (Z_to_bv 64 PJ_NE_TAB_A) (Z_to_bv 64 l) xt3 xt4 xt5 xt6 F fc m).
Notation O2N pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs6 xs9 xs7 xt3 xt4 xt5 xt6 F fc m :=
  (OST E C pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 (shad (pa_SB E + 72))) xa7 (Z_to_bv 64 DATA) (Z_to_bv 64 (M64M1 - PJ_NE_TAB_A)) (Z_to_bv 64 c) xs6 xs7
       xs9 (Z_to_bv 64 PJ_NE_TAB_A) (Z_to_bv 64 l) xt3 xt4 xt5 xt6 F fc m) (only parsing).

Notation O2M pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs9 xs7 xt3 xt4 xt5 xt6 F fc m :=
  (OST E C pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 DATA) (Z_to_bv 64 (M64M1 - PJ_NE_TAB_A)) (Z_to_bv 64 c) xs6 xs7
       xs9 (Z_to_bv 64 PJ_NE_TAB_A) (Z_to_bv 64 l) xt3 xt4 xt5 xt6 F fc m).
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
Local Ltac shl_set l := match goal with SHL : length _ = 16%nat |- _ => clear SHL end; let SHL := fresh "SHL" in assert (SHL : length l = 16%nat) by reflexivity.
Local Ltac shf_explicit := match goal with H : rw_cells bsegs _ (_ / 8 + 2147450880) _ |- _ => try (unfold shpO2 in H); try (unfold sh16, obj_shpatA in H); cbn [map] in H; rewrite ?zb8_m8, ?zb8_lit_m8 in H | _ => idtac end.
Local Ltac open HSM := unfold Pj_ser_okey2A_a.ok2w in HSM; obj_open HSM OK CX OX; shf_explicit.
Local Ltac oclose HSM := shf_explicit; shf_fold; obj_close HSM OX.

Local Ltac diamond_blt FIN Σ buf size cap hp kk sz' K17 KM R0 SZ :=
  first
  [ rewrite sxb_z8; zstep; try if_false; apply evt_done;
    eapply aevt_eq; [| eapply (FIN Σ (mkSbA buf sz' cap hp kk))]; try eassumption; try pj_st_eq; slia
  | let Kc := fresh "Kc" in
    zstep; if_cases Kc; zify_cond Kc; [clear Kc| exfalso; pjnorm_in Kc; clear - Kc K17; lia];
    zstep; pjnorm; rewrite pj_land7 by (clear - R0 SZ; lia);
    zstep; if_cases Kc; zify_cond Kc;
      [clear Kc| exfalso; rewrite !pj_signed_small in Kc by (clear - K17; Z.div_mod_to_equations; lia); clear - Kc K17 KM; lia];
    apply evt_done; eapply aevt_eq; [| eapply (FIN Σ (mkSbA buf sz' cap hp kk))]; try eassumption; try pj_st_eq; slia ].

Notation esc_botA_K := (Pj_ser_okey2A_a.esc_botA_K RT PMc E C f K x c l A X).
Notation okey_closeA := (Pj_ser_okey2A_a.okey_closeA RT AF RC PMc FDO MST GROW E D C f K x c l x1 cx A X OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK).

Section Esc.
  Variable t : Z.
  Hypothesis KB : esc_botA_K t.
  Hypothesis HTL : 0 <= t < l.
  Notation q_tailA := (Pj_ser_okey2A_a.q_tailA RT AF RC PMc FDO MST GROW E D C f K x c l x1 cx A X OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK t KB HTL).
  Notation b_tailA := (Pj_ser_okey2A_a.b_tailA RT AF RC PMc FDO MST GROW E D C f K x c l x1 cx A X OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK t KB HTL).

  Local Ltac esc2 RO TL grown_pc ret_pc Σ buf size cap hp kk HSM ACC CR SZ xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa7 xs6 xt3 xt4 xt5 xt6 :=

    step; zstep; unfold RO; gtrap;

    sb_shz; astep; astep; step; astep; astep;

    step; step; step; zstep; step;
    let Kc := fresh "Kc" in
    if_cases Kc; zify_cond Kc; pjnorm_in Kc;
    [
      let HSM2 := fresh "HSM2" in oclose HSM2; apply evt_done;
      eapply aevt_eq; [| eapply (TL Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia
    |
      zstep; pjnorm; zstep; zstep;
      lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 _ ?mm _) =>
      let GROWN := fresh "GROWN" in
      assert (GROWN : forall (z : Z) (ya0 : word), z = Z.max (2 * cap) (size + 2) ->
        evt bsegs (fun ms' => aevt Σ K ms')
          (O2S grown_pc xra xt0 xt1 xt2 ya0 (wz z) xa2 xa3 xa4 xa5 xa7 xs6 (wz (size + 2)) (wz t) xt3 xt4 xt5 xt6 F0 fc0 mm));
      [ let z := fresh "z" in let ya0 := fresh "ya0" in let EZ := fresh "EZ" in
        intros z ya0 EZ;

        step; zstep;
        let HSM3 := fresh "HSM3" in oclose HSM3; apply evt_done;
        eapply aevt_eq; [| eapply (cont_growA RT AF PMc GROW E D C _ Σ (mkSbA buf size cap hp kk) _ K z X ret_pc)];
          [pj_st_eq| exact OK| exact CX| apply obj_frp_local; exact OX| exact HSM3| | exact CR| exact X0| clear; lia| reflexivity|];
        [ rewrite EZ; eapply (cont_req_okA RT E D C); [exact OK| exact CX| exact HSM3| cbn [sa_cap]; clear - Kc; lia|];
          cbn [sa_size]; clear - ACC BUD HTL; lia
        | let HSM4 := fresh "HSM4" in let CR4 := fresh "CR4" in let HSM5 := fresh "HSM5" in
          intros ?Σ' ?NEW ?m' ?F' ?yt0 ?yt1 ?yt2 ?za0 ?za1 ?za2 ?za3 ?za4 ?za5 ?za6 ?za7 ?yt3 ?yt4 ?yt5 ?yt6 HSM4 CR4;
          apply (aevt_evt RT AF PMc MST); open HSM4;

          step;
          oclose HSM5; apply evt_done;
          eapply aevt_eq; [| eapply (TL _ (sb_grownA (mkSbA buf size cap hp kk) _ z))]; try eassumption; try pj_st_eq;
          unfold sb_grownA; cbn [sa_size sa_cap sa_buf sa_heap sa_k]; rewrite ?EZ; clear - Kc ACC SZ; lia ]
      | let K2 := fresh "K2" in
        if_cases K2; zify_cond K2; pjnorm_in K2;
        [ eapply evt_eq; [| eapply (GROWN (size + 2))]; [pj_st_eq| clear - K2 Kc; lia]
        | zstep; eapply evt_eq; [| eapply (GROWN (2 * cap))]; [pj_st_eq| clear - K2 Kc; lia] ] ]
      end ].

  Lemma esc_quoteA : forall x224 x232 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs6 xs3 xt3 xt4 xt5 xt6 : word),
    CERML x224 x232 obj_shpatA Σ st m -> frm0 fc -> sa_size st <= A + 1 + 6 * t -> CCREDA RT E C Σ X st ->
    aevt Σ K (O2S 0xbd16c xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs6 xs3 (wz t) xt3 xt4 xt5 xt6 F fc m).
  Proof using AF RC FDO MST GROW OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK KB HTL.
    intros x224 x232 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs6 xs3 xt3 xt4 xt5 xt6 HSM FRM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    obj_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM.
    esc2 PJ_RO184_A (q_tailA x224 x232) 0xbd1b0 0xbd1b8 Σ buf size cap hp kk HSM ACC CR SZ xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa7 xs6 xt3 xt4 xt5 xt6.
  Qed.

  Lemma esc_bslashA : forall x224 x232 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs6 xs3 xt3 xt4 xt5 xt6 : word),
    CERML x224 x232 obj_shpatA Σ st m -> frm0 fc -> sa_size st <= A + 1 + 6 * t -> CCREDA RT E C Σ X st ->
    aevt Σ K (O2S 0xbd23c xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs6 xs3 (wz t) xt3 xt4 xt5 xt6 F fc m).
  Proof using AF RC FDO MST GROW OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK KB HTL.
    intros x224 x232 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs6 xs3 xt3 xt4 xt5 xt6 HSM FRM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    obj_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM.
    esc2 PJ_RO176_A (b_tailA x224 x232) 0xbd280 0xbd288 Σ buf size cap hp kk HSM ACC CR SZ xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa7 xs6 xt3 xt4 xt5 xt6.
  Qed.

  Lemma p_finA : forall x224 x232 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa7 xs6 xs3 xt3 xt4 xt5 xt6 : word),
    CERML x224 x232 obj_shpatA Σ st m -> frm0 fc -> 1 <= sa_size st -> sa_size st <= A + 1 + 6 * (t + 1) -> CCREDA RT E C Σ X st ->
    aevt Σ K (O2S 0xbd518 xra xt0 xt1 xt2 (wz (sa_buf st + (sa_size st - 1))) xa1 xa2 xa3 xa4 xa5 xa7 xs6 xs3 (wz t) xt3 xt4 xt5 xt6 F fc m).
  Proof using AF RC FDO MST GROW OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK KB HTL.
    intros x224 x232 Σ st m F fc xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa7 xs6 xs3 xt3 xt4 xt5 xt6 HSM FRM SZ1 ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf] in *.
    obj_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM.
    pose proof (obuf_factsA RT AF E D C OK CX f Σ _ _ OX HREF) as (_ & _ & _ & _ & APB). cbn [sa_buf sa_cap] in APB.
    pose proof (APB (buf + (size - 1)) ltac:(clear - SZ1 SZ; lia)) as (A1 & A2 & A3 & A4). clear APB.

    step. pj_store_done. step.
    oclose HSM2. apply evt_done.
    eapply aevt_eq; [| eapply (KB x224 x232 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
  Qed.

  Lemma p_tailA : forall x224 x232 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs6 xs3 xt3 xt4 xt5 xt6 : word),
    CERML x224 x232 obj_shpatA Σ st m -> frm0 fc -> sa_size st + 1 <= sa_cap st -> sa_size st <= A + 1 + 6 * t -> CCREDA RT E C Σ X st ->
    aevt Σ K (O2S 0xbd4c4 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs6 xs3 (wz t) xt3 xt4 xt5 xt6 F fc m).
  Proof using AF RC FDO MST GROW OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK KB HTL.
    intros x224 x232 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs6 xs3 xt3 xt4 xt5 xt6 HSM FRM ROOM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    obj_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM. sb_shz.

    step. astep. astep. astep. astep.

    step. step. step. zstep. zstep. unbox FSB; unbox SHSB. step. box_disj.

    gtrap. unzt. gtrap.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let MUc := omuc OX in pose proof (acc_buf_muC RT AF E D C OK CX Σ _ _ mm HREF MUc WM) as ACCB end.
    cbn [sa_buf sa_cap] in ACCB.
    destruct (acc_read1 _ _ _ (buf + size) ACCB ltac:(clear - ROOM SZ; lia)) as (b & RDB & SOK). clear ACCB.
    change (wa ((buf + size) / 8 + 2147450880)) with (wa (shad (buf + size))) in RDB.

    zstep. pjnorm. zstep. shfold. zstep.
    oclose HSM2.
    destruct (pj_sh_ok_cases b (buf + size) SOK) as [-> | (k & -> & K17 & KM)]; [| rewrite (pj_sxb_small7 k) by (clear - K17; lia)];
      diamond_blt (p_finA x224 x232) Σ buf size cap hp kk (size + 1) K17 KM R0 SZ.
  Qed.

  Lemma esc_plainA : forall x224 x232 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs6 xs3 xt3 xt4 xt5 xt6 : word),
    CERML x224 x232 obj_shpatA Σ st m -> frm0 fc -> sa_size st <= A + 1 + 6 * t -> CCREDA RT E C Σ X st ->
    aevt Σ K (O2S 0xbd48c xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs6 xs3 (wz t) xt3 xt4 xt5 xt6 F fc m).
  Proof using AF RC FDO MST GROW OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK KB HTL.
    intros x224 x232 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs6 xs3 xt3 xt4 xt5 xt6 HSM FRM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    obj_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM. sb_shz.

    step. astep. astep. astep. astep.

    step. step. step. zstep. step.
    if_cases Kc; zify_cond Kc; pjnorm_in Kc.
    -
      oclose HSM2. apply evt_done.
      eapply aevt_eq; [| eapply (p_tailA x224 x232 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
    -
      zstep. pjnorm. step. zstep.
      oclose HSM3. apply evt_done.
      eapply aevt_eq; [| eapply (cont_growA RT AF PMc GROW E D C _ Σ (mkSbA buf size cap hp kk) _ K (2 * cap) X 0xbd4c0)];
        [pj_st_eq| exact OK| exact CX| apply obj_frp_local; exact OX| exact HSM3| | exact CR| exact X0| clear; lia| reflexivity|].
      { eapply (cont_req_ok2A RT E D C); [exact OK| exact CX| exact HSM3|]. cbn [sa_cap sa_size] in *. clear - Kc ACC BUD HTL. lia. }
      intros Σ' NEW m' F' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CR4.
      apply (aevt_evt RT AF PMc MST). open HSM4.

      step.
      oclose HSM5. apply evt_done.
      eapply aevt_eq; [| eapply (p_tailA x224 x232 Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW (2 * cap)))]; try eassumption; try pj_st_eq;
        unfold sb_grownA; slia.
  Qed.

  Lemma ctl_finA : forall (n : Z) x224 x232 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xt3 xt4 xt5 xt6 : word),
    CERML x224 x232 shpO2 Σ st m -> frm0 fc -> sa_size st + n <= sa_cap st -> 0 <= n -> sa_size st + n <= A + 1 + 6 * (t + 1) -> CCREDA RT E C Σ X st ->
    aevt Σ K (O2M 0xbd46c xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz n) (wz (sa_size st + n)) (wz t) xt3 xt4 xt5 xt6 F fc m).
  Proof using AF RC FDO MST GROW OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK KB HTL.
    intros n x224 x232 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xt3 xt4 xt5 xt6 HSM FRM ROOM N0 ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    obj_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM.

    step. sb_shz. astep. astep. unbox FSB; unbox SHSB. step. box_disj.

    step. zstep. unbox FSB; unbox SHf; unbox SHSB. ls. box_disj. shl_set obj_shpatA.

    step.
    oclose HSM2. apply evt_done.
    eapply aevt_eq; [| eapply (KB x224 x232 Σ (mkSbA buf (size + n) cap hp kk))]; try eassumption; try pj_st_eq; slia.
  Qed.

  Lemma ctl_tailA : forall (n : Z) x224 x232 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs6 xt3 xt4 xt5 xt6 : word),
    CERML x224 x232 shpO2 Σ st m -> frm0 fc -> sa_size st + n <= sa_cap st -> 1 <= n <= 7 -> sa_size st + n <= A + 1 + 6 * (t + 1) -> CCREDA RT E C Σ X st ->
    aevt Σ K (O2N 0xbd428 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 (wz n) (wz (sa_size st + n)) (wz t) xt3 xt4 xt5 xt6 F fc m).
  Proof using AF RC FDO MST GROW OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK KB HTL.
    intros n x224 x232 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs6 xt3 xt4 xt5 xt6 HSM FRM ROOM N17 ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    obj_envA OK CX OX. apply (aevt_evt RT AF PMc MST). pose proof HSM as HSM0. open HSM. sb_shz.

    step. astep. astep. astep. astep.

    step. step. step. zstep. try (replace (size + buf) with (buf + size) by (clear; lia)).

    gtrap. unzt.

    step. zstep. zstep.

    pose proof (f1_rngA RT E D C f _ Σ _ m (f + 65) n _ _ OK CX OX HSM0 eq_refl ltac:(clear; lia) ltac:(clear - N17; lia) ltac:(clear - N17; lia))
      as (RC3 & F3a & F3b & (src & SRC & SRCL)).
    shf_fold. pose proof (f1tmp_accB m f 64 8 shpO2 SHF shpO2_g8 Ef ltac:(clear - F0; lia) eq_refl) as AC8. shf_explicit.
    oclose HSM2. apply evt_done.
    eapply aevt_eq; [| eapply (cont_copyhA RT AF RC PMc FDO MST E D C _ Σ (mkSbA buf size cap hp kk) m K (f + 65) n 0xbd46c src)];
      [pj_st_eq; clear - N17; lia| exact OK| exact CX| apply obj_frp_local; exact OX| exact HSM2| exact SRC| exact SRCL| clear - N17; lia| cbn [sa_size sa_cap]; exact ROOM
      | intros _; split; [eapply acc_sub; [exact AC8| clear; lia| clear - N17; lia]| exact RC3]| clear - F0; lia| exact F3b
      | clear; lia| reflexivity|].
    intros m' F' yt0 yt1 yt2 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CPY.
    eapply aevt_eq; [| eapply (ctl_finA n x224 x232 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; clear - N17 ROOM ACC; cbn [sa_size sa_cap]; lia.
  Qed.

  Local Ltac escb m b MI BR HB k :=
    let G := fresh "G" in let G2 := fresh "G" in let ER := fresh "ER" in let RD := fresh "RD" in
    pose proof (esc_byte_range (8 * b + k)) as ER;
    assert (G : 0 <= 8 * b + k < 256) by (clear - BR HB; lia);
    assert (G2 : 146304 + 8 * b + k = 146304 + (8 * b + k)) by (clear; lia);
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (read1_at mm _ _ (esc_readA mm _ MI G) _ G2) as RD end; clear G G2; unfold PJ_ESC_TAB_A in RD; astep; clear RD.

  Lemma esc_ctlA : forall x224 x232 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa7 xs6 xt3 xt4 xt5 xt6 : word),
    pa_S E (c + 4 + t) <= 31 ->
    CERML x224 x232 obj_shpatA Σ st m -> frm0 fc -> sa_size st <= A + 1 + 6 * t -> CCREDA RT E C Σ X st ->
    aevt Σ K (O2S 0xbd320 xra xt0 xt1 xt2 (wz (DATA + t)) (wz (shad (DATA + t))) xa2 xa3 xa4 xa5 xa7 xs6 (wz (pa_S E (c + 4 + t))) (wz t) xt3 xt4 xt5 xt6 F fc m).
  Proof using AF RC FDO MST GROW OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK KB HTL.
    intros x224 x232 Σ st m F fc xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa7 xs6 xt3 xt4 xt5 xt6 HB HSM FRM ACC CR.
    pose proof HSTR as (C0 & L0 & CL & _).
    pose proof (S_rangeA E (c + 4 + t) OK) as BR. set (b := pa_S E (c + 4 + t)) in *.
    pose proof (esc_len_range b ltac:(clear - BR HB; lia)) as NR. rewrite <- esc_len_byte in NR. set (n := esc_byte (8 * b)) in *.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    obj_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM. unfold PJ_ESC_TAB_A in *.

    step. unbox FSB; unbox SHf; unbox SHSB. ls. box_disj. shl_set shpO2.

    let SHS := fresh "SHS" in
    pose proof (shz_sbuf_muC RT AF E D C OK CX Σ _ _ _ HREF ltac:(omucx OX) WM) as SHS;
    assert (G : pa_SBUF E <= pa_SBUF E + c + 4 + t < pa_SBUF E + pa_sn E) by (clear - C0 CL HTL; lia);
    pose proof (shz_rd _ _ _ SHS _ G) as RD; clear G SHS. astep. astep. clear RD.
    assert (G : 0 <= c + 4 + t < pa_sn E) by (clear - C0 CL HTL; lia).
    assert (G2 : pa_SBUF E + c + 4 + t = pa_SBUF E + (c + 4 + t)) by (clear; lia).
    pose proof (read1_at _ _ _ (sbuf_read_muC RT AF E D C OK CX Σ _ _ _ _ HREF ltac:(omucx OX) WM G) _ G2) as RD. clear G G2. fold b in RD.
    astep. clear RD.

    zstep. gtrap. zstep. pjnorm. step. zstep. gtrap. step. zstep.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (shz_tabs_muC RT AF E D C OK CX Σ _ _ mm HREF ltac:(omucx OX) WM) as SHTB end.
    assert (G : PJ_TABS_A <= 146304 + 8 * b < PJ_TABS_A + PJ_TABS_LEN) by (unfold PJ_TABS_A, PJ_TABS_LEN; clear - BR HB; lia).
    pose proof (shz_rd _ _ _ SHTB _ G) as RD. clear G. do 4 astep. clear RD.
    assert (G : PJ_TABS_A <= 146304 + 8 * b + 7 < PJ_TABS_A + PJ_TABS_LEN) by (unfold PJ_TABS_A, PJ_TABS_LEN; clear - BR HB; lia).
    pose proof (shz_rd _ _ _ SHTB _ G) as RD. clear G. do 5 astep. clear RD. clear SHTB.

    escb m b MI BR HB 1. escb m b MI BR HB 2. escb m b MI BR HB 3. escb m b MI BR HB 0.
    zstep. zstep. zstep. zstep.
    escb m b MI BR HB 4. escb m b MI BR HB 5. zstep. escb m b MI BR HB 6. escb m b MI BR HB 7.
    do 9 zstep. zstep.
    pose proof (esc_byte_range (8 * b)) as ERn. fold n in ERn. rewrite ?Z.add_0_r. fold n.
    lazymatch goal with |- context [Z_to_bv 64 (Z.land ?W 255)] =>
      replace (Z.land W 255) with n by (symmetry; land255_simpl; rewrite ?land255_small by (clear - ERn; lia); reflexivity) end.
    repeat match goal with |- context [Z_to_bv 64 (Z.lor ?x ?y)] => let j := fresh "recw" in set (j := Z_to_bv 64 (Z.lor x y)) in *; clearbody j end.

    step. unbox FSB; unbox FDOC; unbox SHf. step. pj_store_done. box_disj. step. gtrap.
    sb_shz.

    astep. astep. step. astep. astep.

    step. step. step. zstep. step.
    if_cases Kc; zify_cond Kc; pjnorm_in Kc.
    -
      oclose HSM2. apply evt_done.
      eapply aevt_eq; [| eapply (ctl_tailA n x224 x232 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
    -
      zstep. pjnorm. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 _ ?mm _) =>
      assert (GROWN : forall (z : Z) (ya0 ya2 ya3 ya4 ya5 : word), z = Z.max (2 * cap) (size + n) ->
        evt bsegs (fun ms' => aevt Σ K ms')
          (O2N 0xbd41c xra xt0 xt1 xt2 ya0 (wz z) ya2 ya3 ya4 ya5 xa7 (wz n) (wz (size + n)) (wz t) xt3 xt4 xt5 xt6 F0 fc0 mm)) end.
      { intros z ya0 ya2 ya3 ya4 ya5 EZ.

        step. zstep.
        oclose HSM3. apply evt_done.
        eapply aevt_eq; [| eapply (cont_growA RT AF PMc GROW E D C _ Σ (mkSbA buf size cap hp kk) _ K z X 0xbd424)];
          [pj_st_eq| exact OK| exact CX| apply obj_frp_local; exact OX| exact HSM3| | exact CR| exact X0| clear; lia| reflexivity|].
        { rewrite EZ. eapply (cont_req_okA RT E D C); [exact OK| exact CX| exact HSM3| cbn [sa_cap]; clear - Kc; lia|].
          cbn [sa_size]. clear - ACC BUD HTL NR. lia. }
        intros Σ' NEW m' F' yt0 yt1 yt2 za0 za1 za2 za3 za4 za5 za6 za7 yt3 yt4 yt5 yt6 HSM4 CR4.
        apply (aevt_evt RT AF PMc MST). open HSM4.

        step.
        oclose HSM5. apply evt_done.
        eapply aevt_eq; [| eapply (ctl_tailA n x224 x232 Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW z))]; try eassumption; try pj_st_eq;
          unfold sb_grownA; cbn [sa_size sa_cap sa_buf sa_heap sa_k]; rewrite ?EZ; clear - Kc ACC SZ NR; lia. }
      if_cases K2; zify_cond K2; pjnorm_in K2.
      + eapply evt_eq; [| eapply (GROWN (size + n))]; [pj_st_eq| clear - K2 Kc; lia].
      +   zstep. eapply evt_eq; [| eapply (GROWN (2 * cap))]; [pj_st_eq| clear - K2 Kc; lia].
  Qed.
End Esc.

Definition esc_head_stmtA (fu : nat) : Prop :=
  forall (t : Z) x224 x232 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
         (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs6 xs2 xt3 xt4 xt5 xt6 : word),
    l - t <= Z.of_nat fu -> 0 <= t < l ->
    CERML x224 x232 obj_shpatA Σ st m -> frm0 fc -> sa_size st <= A + 1 + 6 * t -> CCREDA RT E C Σ X st ->
    aevt Σ K (O2S 0xbd140 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs6 xs2 (wz t) xt3 xt4 xt5 xt6 F fc m).

Lemma esc_botA : forall fu, esc_head_stmtA fu -> forall t, 0 <= t < l -> l - t <= Z.of_nat (S fu) -> esc_botA_K t.
Proof using AF RC FDO MST GROW OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK.
  intros fu IH t HTL HF0. unfold Pj_ser_okey2A_a.esc_botA_K.
  intros x224 x232 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs6 xs2 xt3 xt4 xt5 xt6 HSM FRM ACC CR.
  pose proof HSTR as (C0 & L0 & CL & _).
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  obj_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM.

  zstep. zstep.
  oclose HSM2.
  if_cases Kc; zify_cond Kc; pjnorm_in Kc.
  -
    apply evt_done.
    eapply aevt_eq; [| eapply (IH (t + 1) x224 x232 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq;
      cbn [sa_size]; clear - HF0 HTL Kc ACC; lia.
  -
    zstep. apply evt_done.
    eapply aevt_eq; [| eapply (okey_closeA x224 x232 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq;
      cbn [sa_size]; clear - ACC HTL Kc; lia.
Qed.

Lemma esc_headA : forall fu, esc_head_stmtA fu.
Proof using AF RC FDO MST GROW OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK.
  induction fu as [|fu IH]; unfold esc_head_stmtA;
    intros t x224 x232 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa7 xs6 xs2 xt3 xt4 xt5 xt6 HF0 HTL HSM FRM ACC CR; [lia|].
  pose proof (esc_botA fu IH t HTL HF0) as KB.
  pose proof HSTR as (C0 & L0 & CL & _).
  pose proof (S_rangeA E (c + 4 + t) OK) as BR. set (b := pa_S E (c + 4 + t)) in *.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  obj_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM.

  zstep. gtrap.
  pose proof (shz_sbuf_muC RT AF E D C OK CX Σ _ _ _ HREF ltac:(omucx OX) WM) as SHS.
  assert (G : pa_SBUF E <= pa_SBUF E + c + 4 + t < pa_SBUF E + pa_sn E) by (clear - C0 CL HTL; lia).
  pose proof (shz_rd m _ _ SHS _ G) as RD. clear G SHS.
  astep. astep. astep. astep.

  assert (G : 0 <= c + 4 + t < pa_sn E) by (clear - C0 CL HTL; lia).
  assert (G2 : pa_SBUF E + c + 4 + t = pa_SBUF E + (c + 4 + t)) by (clear; lia).
  pose proof (read1_at m _ _ (sbuf_read_muC RT AF E D C OK CX Σ _ _ m _ HREF ltac:(omucx OX) WM G) _ G2) as RD1. clear G G2. fold b in RD1.
  astep. clear RD1.

  zstep. zstep. if_cases K1; zify_cond K1; pjnorm_in K1.
  - clear RD. oclose HSM2. apply evt_done.
    eapply aevt_eq; [| eapply (esc_bslashA t KB HTL x224 x232 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
  -
    zstep. zstep. if_cases K2; zify_cond K2; pjnorm_in K2.
    +
      gtrap. zstep. zstep. if_cases K3; zify_cond K3; pjnorm_in K3.
      * clear RD. oclose HSM2. apply evt_done.
        eapply aevt_eq; [| eapply (esc_plainA t KB HTL x224 x232 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
      *
        clear RD. oclose HSM2. apply evt_done.
        eapply aevt_eq; [| eapply (esc_ctlA t KB HTL x224 x232 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq;
          subst b; clear - K3 ACC; lia.
    + clear RD. oclose HSM2. apply evt_done.
      eapply aevt_eq; [| eapply (esc_quoteA t KB HTL x224 x232 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
Qed.
End OKeyE.
