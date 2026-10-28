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
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_libiface
     Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_hkit3A Atp_hkit4A Pj_rtkA Pj_defsA Pj_cpsA Pj_copyA Pj_ser_trefA Pj_ser_defsA Pj_ser_kitA Pj_ser_callsA Pj_ser_skitA
     Pj_ser_ncallsA Pj_ser_keyA_a.
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

Definition shpK1Z : list Z :=
  [241; 241; 241; 241; 248; 248; 248; 248; 248; 242; 242; 242; 242; 242; 248; 248; 248; 242; 242; 242; 242; 242;
   248; 248; 248; 242; 242; 242; 242; 242; 248; 242; 242; 242; 0; 242; 242; 242; 0; 0; 243; 243; 243; 243].
Definition shpK1 : list byte := map (Z_to_bv 8) shpK1Z.
Lemma shpK1_eq : upd ser_shpatA 34 z8 = shpK1.
Proof. reflexivity. Qed.
Lemma shpK0_eq : upd shpK1 34 (Z_to_bv 8 248) = ser_shpatA.
Proof. reflexivity. Qed.
Lemma shpK1_g34 : nth_error shpK1 34 = Some z8.
Proof. reflexivity. Qed.

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

Section KeyE.
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
Variable I : serI.
Variable K : config -> Prop.
Variable isobj : list byte.
Variables (i dp c l A X : Z).
Hypothesis OK : pjenvA_ok E.
Hypothesis CX : sctxA E D I.
Hypothesis Hi : 1 <= i < pa_n E.
Hypothesis HT : pa_T E i = tword t_str c.
Hypothesis HSTR : str_at (pa_S E) (pa_sn E) c l.
Hypothesis Hdp : 0 <= dp <= 15.
Hypothesis BUD : A + (3 + 6 * l) <= PJ_OUTMAX (pa_len E).
Hypothesis X0 : 0 <= X.
Hypothesis HK : disp_KA RT PMc E I K isobj (i + 1) dp X (A + (3 + 6 * l)).

Notation DATA := (pa_SBUF E + c + 4).
Notation kx := (Pj_ser_keyA_a.kx E c).
Notation SERML x0 x8 x16 x288 x296 shp Σ st m := (SERMA RT E I (wkI E (wz (shad (pa_SB E + 80)))) (kx x0 x8 x16 x288 x296) shp isobj Σ st m).
Notation KSS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs3 xs4 xt3 xt4 xt5 xt6 F fc m :=
  (SSTA I pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 (Z_to_bv 64 DATA) xa5 xa6 xa7 (Z_to_bv 64 (pa_SB E + 72)) xs3 xs4 (Z_to_bv 64 l) (Z_to_bv 64 i)
        (Z_to_bv 64 PJ_NE_TAB_A) (Z_to_bv 64 (pa_SB E)) (Z_to_bv 64 2147450880) (Z_to_bv 64 dp) (Z_to_bv 64 (shad (pa_SB E + 72))) xt3 xt4 xt5 xt6 F fc m).
Notation KSN pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs8 xs4 xt3 xt4 xt5 xt6 F fc m :=
  (SSTA I pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (pa_SB E + 72)) xs3 xs4 (Z_to_bv 64 l) (Z_to_bv 64 i)
        (Z_to_bv 64 PJ_NE_TAB_A) xs8 (Z_to_bv 64 2147450880) (Z_to_bv 64 dp) (Z_to_bv 64 (shad (pa_SB E + 72))) xt3 xt4 xt5 xt6 F fc m).
Local Ltac slia := repeat match goal with H : _ \/ _ |- _ => clear H end; cbn [sa_size sa_cap sa_buf sa_heap sa_k]; lia.
Local Ltac cbnx := cbn [Pj_ser_keyA_a.kx Pj_ser_defsA.xj0 Pj_ser_defsA.xj8 Pj_ser_defsA.xj16 Pj_ser_defsA.xj24 Pj_ser_defsA.xj80 Pj_ser_defsA.xj208 Pj_ser_defsA.xj216
                         Pj_ser_defsA.xj288 Pj_ser_defsA.xj296] in *.
Local Ltac sb_shz :=
  lazymatch goal with
  | HREF : SREFA _ _ _ _ _ ?mr, MU : munch _ ?mr ?mm, WM : wmono bsegs ?mr ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let SHZ := fresh "SHZ" in let R64 := fresh "RD64" in let R72 := fresh "RD72" in let R80 := fresh "RD80" in
    pose proof (shz_sb_mu RT AF E D I OK CX _ _ _ mm HREF MU WM) as SHZ;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 64) ltac:(clear; lia)) as R64;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 72) ltac:(clear; lia)) as R72;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 80) ltac:(clear; lia)) as R80; clear SHZ
  end.
Local Ltac open HSM := unfold Pj_ser_keyA_a.kx in HSM; ser_open HSM OK; cbnx.
Local Ltac shp_norm SHF l :=
  rewrite ?zb8_m8 in SHF;
  lazymatch type of SHF with u8arr _ _ _ ?cur => lazymatch cur with l => idtac | _ => replace cur with l in SHF by reflexivity end end;
  try match goal with L : length _ = 44%nat |- _ => clear L end;
  let SHL := fresh "SHL" in assert (SHL : length l = 44%nat) by reflexivity.
Local Ltac shst SHF k :=
  lazymatch type of SHF with u8arr _ ?m ?A ?l =>
    let SOK := fresh "SOK" in
    pose proof (u8arr_store_ok bsegs m A l k (wa (A + k)) SHF ltac:(change (Z.of_nat (length l)) with 44; lia) eq_refl) as SOK;
    step;
    let SHF1 := fresh "SHF" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ ?a (le1 ?v)) _) =>
      pose proof (u8arr_write_le1 m A l k v a SHF ltac:(change (Z.of_nat (length l)) with 44; lia) ltac:(unfold wa; f_equal; lia)) as SHF1 end;
    store_done; try clear SHF; rename SHF1 into SHF
  end.

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

Notation esc_botA_K := (Pj_ser_keyA_a.esc_botA_K RT PMc E I K isobj i dp c l A X).
Notation key_closeA := (Pj_ser_keyA_a.key_closeA RT AF RC PMc FDO MST GROW E D I K isobj i dp c l A X OK CX Hi HT HSTR Hdp BUD X0 HK).

Section Esc.
  Variable t : Z.
  Hypothesis KB : esc_botA_K t.
  Hypothesis HTL : 0 <= t < l.
  Notation q_tailA := (Pj_ser_keyA_a.q_tailA RT AF RC PMc FDO MST GROW E D I K isobj i dp c l A X OK CX Hi HT HSTR Hdp BUD X0 HK t KB HTL).
  Notation b_tailA := (Pj_ser_keyA_a.b_tailA RT AF RC PMc FDO MST GROW E D I K isobj i dp c l A X OK CX Hi HT HSTR Hdp BUD X0 HK t KB HTL).

  Local Ltac esc2 RO TL grown_pc ret_pc Σ buf size cap hp kk HSM ACC CR SZ xra xt0 xt1 xt2 xa2 xa3 xa5 xa6 xa7 xt3 xt4 xt5 xt6 :=

    step; zstep; unfold RO; gok;

    sb_shz; astep; astep; step; astep; astep;

    step; step; step; zstep; step;
    let Kc := fresh "Kc" in
    if_cases Kc; zify_cond Kc; pjnorm_in Kc;
    [
      let HSM2 := fresh "HSM2" in ser_close HSM2 OK CX; apply evt_done;
      eapply aevt_eq; [| eapply (TL Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia
    |
      zstep; pjnorm; zstep; zstep;
      lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 _ ?mm _) =>
      let GROWN := fresh "GROWN" in
      assert (GROWN : forall (z : Z) (ya0 : word), z = Z.max (2 * cap) (size + 2) ->
        evt bsegs (fun ms' => aevt Σ K ms')
          (KSS grown_pc xra xt0 xt1 xt2 ya0 (wz z) xa2 xa3 xa5 xa6 xa7 (wz (size + 2)) (wz t) xt3 xt4 xt5 xt6 F0 fc0 mm));
      [ let z := fresh "z" in let ya0 := fresh "ya0" in let EZ := fresh "EZ" in
        intros z ya0 EZ;

        zstep; zstep;
        let HSM3 := fresh "HSM3" in ser_close HSM3 OK CX; apply evt_done;
        eapply aevt_eq; [| eapply (ser_growA RT AF PMc GROW E D I _ _ _ isobj Σ (mkSbA buf size cap hp kk) _ K z X ret_pc)];
          [pj_st_eq| exact OK| exact CX| exact HSM3| | exact CR| exact X0| clear; lia| reflexivity|];
        [ rewrite EZ; eapply (ser_req_okA RT E D I); [exact OK| exact CX| exact HSM3| cbn [sa_cap]; clear - Kc; lia|];
          cbn [sa_size]; clear - ACC BUD HTL; lia
        | let HSM4 := fresh "HSM4" in let CR4 := fresh "CR4" in let HSM5 := fresh "HSM5" in
          intros ?Σ' ?NEW ?m' ?F' ?yt0 ?yt1 ?yt2 ?za0 ?za1 ?za2 ?za3 ?za4 ?za5 ?za6 ?za7 ?yt3 ?yt4 ?yt5 ?yt6 HSM4 CR4;
          apply (aevt_evt RT AF PMc MST); open HSM4;

          step;
          ser_close HSM5 OK CX; apply evt_done;
          eapply aevt_eq; [| eapply (TL _ (sb_grownA (mkSbA buf size cap hp kk) _ z))]; try eassumption; try pj_st_eq;
          unfold sb_grownA; cbn [sa_size sa_cap sa_buf sa_heap sa_k]; rewrite ?EZ; clear - Kc ACC SZ; lia ]
      | let K2 := fresh "K2" in
        if_cases K2; zify_cond K2; pjnorm_in K2;
        [ eapply evt_eq; [| eapply (GROWN (size + 2))]; [pj_st_eq| clear - K2 Kc; lia]
        | zstep; eapply evt_eq; [| eapply (GROWN (2 * cap))]; [pj_st_eq| clear - K2 Kc; lia] ] ]
      end ].

  Lemma esc_quoteA : forall x0 x8 x16 x288 x296 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 : word),
    SERML x0 x8 x16 x288 x296 ser_shpatA Σ st m -> frm0 fc -> sa_size st <= A + 1 + 6 * t -> CREDA RT E I Σ X st ->
    aevt Σ K (KSS 0xb88ec xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs3 (wz t) xt3 xt4 xt5 xt6 F fc m).
  Proof using AF RC FDO MST GROW OK CX Hi HT HSTR Hdp BUD X0 HK KB HTL.
    intros x0 x8 x16 x288 x296 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 HSM FRM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM.
    esc2 PJ_RO184_A (q_tailA x0 x8 x16 x288 x296) 0xb893c 0xb8944 Σ buf size cap hp kk HSM ACC CR SZ xra xt0 xt1 xt2 xa2 xa3 xa5 xa6 xa7 xt3 xt4 xt5 xt6.
  Qed.

  Lemma esc_bslashA : forall x0 x8 x16 x288 x296 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 : word),
    SERML x0 x8 x16 x288 x296 ser_shpatA Σ st m -> frm0 fc -> sa_size st <= A + 1 + 6 * t -> CREDA RT E I Σ X st ->
    aevt Σ K (KSS 0xb89dc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs3 (wz t) xt3 xt4 xt5 xt6 F fc m).
  Proof using AF RC FDO MST GROW OK CX Hi HT HSTR Hdp BUD X0 HK KB HTL.
    intros x0 x8 x16 x288 x296 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 HSM FRM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM.
    esc2 PJ_RO176_A (b_tailA x0 x8 x16 x288 x296) 0xb8a2c 0xb8a34 Σ buf size cap hp kk HSM ACC CR SZ xra xt0 xt1 xt2 xa2 xa3 xa5 xa6 xa7 xt3 xt4 xt5 xt6.
  Qed.

  Lemma p_finA : forall x0 x8 x16 x288 x296 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa1 xa2 xa3 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 : word),
    SERML x0 x8 x16 x288 x296 ser_shpatA Σ st m -> frm0 fc -> 1 <= sa_size st -> sa_size st <= A + 1 + 6 * (t + 1) -> CREDA RT E I Σ X st ->
    aevt Σ K (KSS 0xb8d24 xra xt0 xt1 xt2 (wz (sa_buf st + (sa_size st - 1))) xa1 xa2 xa3 xa5 xa6 xa7 xs3 (wz t) xt3 xt4 xt5 xt6 F fc m).
  Proof using AF RC FDO MST GROW OK CX Hi HT HSTR Hdp BUD X0 HK KB HTL.
    intros x0 x8 x16 x288 x296 Σ st m F fc xra xt0 xt1 xt2 xa1 xa2 xa3 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 HSM FRM SZ1 ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf] in *.
    ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM.
    pose proof (buf_factsA RT AF E D I Σ _ _ (si_b I) OK CX HREF) as (_ & _ & _ & _ & APB). cbn [sa_buf sa_cap] in APB.
    pose proof (APB (buf + (size - 1)) ltac:(clear - SZ1 SZ; lia)) as (A1 & A2 & A3 & A4). clear APB.

    step. pj_store_done. step.
    ser_close HSM2 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (KB x0 x8 x16 x288 x296 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
  Qed.

  Lemma p_tailA : forall x0 x8 x16 x288 x296 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 : word),
    SERML x0 x8 x16 x288 x296 ser_shpatA Σ st m -> frm0 fc -> sa_size st + 1 <= sa_cap st -> sa_size st <= A + 1 + 6 * t -> CREDA RT E I Σ X st ->
    aevt Σ K (KSS 0xb8cbc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs3 (wz t) xt3 xt4 xt5 xt6 F fc m).
  Proof using AF RC FDO MST GROW OK CX Hi HT HSTR Hdp BUD X0 HK KB HTL.
    intros x0 x8 x16 x288 x296 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 HSM FRM ROOM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM. sb_shz.

    step. astep. astep. astep. astep.

    step. step. step. zstep. zstep. unbox FSB; unbox SHSB. step. box_disj.

    gok. unzx. gok.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (acc_buf_mu RT AF E D I OK CX Σ _ _ mm HREF MU WM) as ACCB end.
    cbn [sa_buf sa_cap] in ACCB.
    destruct (acc_read1 _ _ _ (buf + size) ACCB ltac:(clear - ROOM SZ; lia)) as (b & RDB & SOK). clear ACCB.
    change (wa ((buf + size) / 8 + 2147450880)) with (wa (shad (buf + size))) in RDB.

    zstep. pjnorm. zstep. shfold. zstep.
    ser_close HSM2 OK CX.
    destruct (pj_sh_ok_cases b (buf + size) SOK) as [-> | (k & -> & K17 & KM)]; [| rewrite (pj_sxb_small7 k) by (clear - K17; lia)];
      diamond_blt (p_finA x0 x8 x16 x288 x296) Σ buf size cap hp kk (size + 1) K17 KM R0 SZ.
  Qed.

  Lemma esc_plainA : forall x0 x8 x16 x288 x296 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 : word),
    SERML x0 x8 x16 x288 x296 ser_shpatA Σ st m -> frm0 fc -> sa_size st <= A + 1 + 6 * t -> CREDA RT E I Σ X st ->
    aevt Σ K (KSS 0xb8c7c xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs3 (wz t) xt3 xt4 xt5 xt6 F fc m).
  Proof using AF RC FDO MST GROW OK CX Hi HT HSTR Hdp BUD X0 HK KB HTL.
    intros x0 x8 x16 x288 x296 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 HSM FRM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM. sb_shz.

    step. astep. astep. astep. astep.

    step. step. step. zstep. step.
    if_cases Kc; zify_cond Kc; pjnorm_in Kc.
    -
      ser_close HSM2 OK CX. apply evt_done.
      eapply aevt_eq; [| eapply (p_tailA x0 x8 x16 x288 x296 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
    -
      zstep. pjnorm. zstep. zstep.
      ser_close HSM3 OK CX. apply evt_done.
      eapply aevt_eq; [| eapply (ser_growA RT AF PMc GROW E D I _ _ _ isobj Σ (mkSbA buf size cap hp kk) _ K (2 * cap) X 0xb8cb8)];
        [pj_st_eq| exact OK| exact CX| exact HSM3| | exact CR| exact X0| clear; lia| reflexivity|].
      { eapply (ser_req_ok2A RT E D I); [exact OK| exact CX| exact HSM3|]. cbn [sa_cap sa_size] in *. clear - Kc ACC BUD HTL. lia. }
      intros Σ' NEW m' F' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CR4.
      apply (aevt_evt RT AF PMc MST). open HSM4.

      step.
      ser_close HSM5 OK CX. apply evt_done.
      eapply aevt_eq; [| eapply (p_tailA x0 x8 x16 x288 x296 Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW (2 * cap)))]; try eassumption; try pj_st_eq;
        unfold sb_grownA; slia.
  Qed.

  Lemma ctl_finA : forall (n : Z) x0 x8 x16 x288 x296 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    SERML x0 x8 x16 x288 x296 shpK1 Σ st m -> frm0 fc -> sa_size st + n <= sa_cap st -> 0 <= n -> sa_size st + n <= A + 1 + 6 * (t + 1) -> CREDA RT E I Σ X st ->
    aevt Σ K (KSN 0xb8c54 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz n) (wz (sa_size st + n)) (wz t) xt3 xt4 xt5 xt6 F fc m).
  Proof using AF RC FDO MST GROW OK CX Hi HT HSTR Hdp BUD X0 HK KB HTL.
    intros n x0 x8 x16 x288 x296 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HSM FRM ROOM N0 ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM. sb_shz.

    astep. astep. unbox FSB; unbox SHSB. step. box_disj.

    step. zstep. unbox SHSB; unbox SHf; unbox SHDC. shst SHF 34. box_disj. shp_norm SHF ser_shpatA.

    step. step. step.
    ser_close HSM2 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (KB x0 x8 x16 x288 x296 Σ (mkSbA buf (size + n) cap hp kk))]; try eassumption; try pj_st_eq; slia.
  Qed.

  Lemma ctl_tailA : forall (n : Z) x0 x8 x16 x288 x296 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    SERML x0 x8 x16 x288 x296 shpK1 Σ st m -> frm0 fc -> sa_size st + n <= sa_cap st -> 1 <= n <= 7 -> sa_size st + n <= A + 1 + 6 * (t + 1) -> CREDA RT E I Σ X st ->
    aevt Σ K (KSN 0xb8c00 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz n) (wz (sa_size st + n)) (wz t) xt3 xt4 xt5 xt6 F fc m).
  Proof using AF RC FDO MST GROW OK CX Hi HT HSTR Hdp BUD X0 HK KB HTL.
    intros n x0 x8 x16 x288 x296 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HSM FRM ROOM N17 ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ser_envA OK CX. apply (aevt_evt RT AF PMc MST). pose proof HSM as HSM0. open HSM. sb_shz.

    step. astep. astep. astep. astep.

    step. step. step. zstep. try (replace (size + buf) with (buf + size) by (clear; lia)).

    gok. unzx.

    step. zstep. zstep.

    pose proof (f3_rngA RT E D I _ _ _ isobj Σ _ m (si_f I + 273) n OK CX HSM0 ltac:(clear; lia) ltac:(clear - N17; lia) ltac:(clear - N17; lia))
      as (RC3 & F3a & F3b & (src & SRC & SRCL)).
    pose proof (f3tmp_accA m (si_f I) 272 34 shpK1 SHF shpK1_g34 Ef ltac:(clear - F0; lia) eq_refl) as AC8.
    ser_close HSM2 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (ser_copyA RT AF RC PMc FDO MST E D I _ _ _ isobj Σ (mkSbA buf size cap hp kk) m K (si_f I + 273) n 0xb8c54 src)];
      [pj_st_eq; clear - N17; lia| exact OK| exact CX| exact HSM2| exact SRC| exact SRCL| clear - N17; lia| cbn [sa_size sa_cap]; exact ROOM
      | intros _; split; [eapply acc_sub; [exact AC8| clear; lia| clear - N17; lia]| exact RC3]| clear - F0; lia| exact F3b
      | clear; lia| reflexivity|].
    intros m' F' yt0 yt1 yt2 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CPY.
    eapply aevt_eq; [| eapply (ctl_finA n x0 x8 x16 x288 x296 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; clear - N17 ROOM ACC; cbn [sa_size sa_cap]; lia.
  Qed.

  Local Ltac escb m b MI BR HB k :=
    let G := fresh "G" in let G2 := fresh "G" in let ER := fresh "ER" in let RD := fresh "RD" in
    pose proof (esc_byte_range (8 * b + k)) as ER;
    assert (G : 0 <= 8 * b + k < 256) by (clear - BR HB; lia);
    assert (G2 : 146304 + 8 * b + k = 146304 + (8 * b + k)) by (clear; lia);
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (read1_at mm _ _ (esc_readA mm _ MI G) _ G2) as RD end; clear G G2; unfold PJ_ESC_TAB_A in RD; astep; clear RD.

  Lemma esc_ctlA : forall x0 x8 x16 x288 x296 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    pa_S E (c + 4 + t) <= 31 ->
    SERML x0 x8 x16 x288 x296 ser_shpatA Σ st m -> frm0 fc -> sa_size st <= A + 1 + 6 * t -> CREDA RT E I Σ X st ->
    aevt Σ K (KSS 0xb8ae8 xra xt0 xt1 xt2 (wz (DATA + t)) (wz (shad (DATA + t))) xa2 xa3 xa5 xa6 xa7 (wz (pa_S E (c + 4 + t))) (wz t) xt3 xt4 xt5 xt6 F fc m).
  Proof using AF RC FDO MST GROW OK CX Hi HT HSTR Hdp BUD X0 HK KB HTL.
    intros x0 x8 x16 x288 x296 Σ st m F fc xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HB HSM FRM ACC CR.
    pose proof HSTR as (C0 & L0 & CL & _).
    pose proof (S_rangeA E (c + 4 + t) OK) as BR. set (b := pa_S E (c + 4 + t)) in *.
    pose proof (esc_len_range b ltac:(clear - BR HB; lia)) as NR. rewrite <- esc_len_byte in NR. set (n := esc_byte (8 * b)) in *.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM. unfold PJ_ESC_TAB_A in *.

    step. unbox SHSB; unbox SHf; unbox SHDC. shst SHF 34. box_disj. shp_norm SHF shpK1.

    let SHS := fresh "SHS" in
    pose proof (shz_sbufA RT AF E D I Σ _ _ _ OK CX HREF MU WM) as SHS;
    assert (G : pa_SBUF E <= pa_SBUF E + c + 4 + t < pa_SBUF E + pa_sn E) by (clear - C0 CL HTL; lia);
    pose proof (shz_rd _ _ _ SHS _ G) as RD; clear G SHS. astep. astep. clear RD.
    assert (G : 0 <= c + 4 + t < pa_sn E) by (clear - C0 CL HTL; lia).
    assert (G2 : pa_SBUF E + c + 4 + t = pa_SBUF E + (c + 4 + t)) by (clear; lia).
    pose proof (read1_at _ _ _ (sbuf_read_mu RT AF E D I OK CX Σ _ _ _ _ HREF MU WM G) _ G2) as RD. clear G G2. fold b in RD.
    astep. clear RD.

    zstep. gok. zstep. pjnorm. step. zstep. gok. step. zstep.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (shz_tabs mm (tabs_accA RT AF Σ mm (ART_mu RT AF E D I Σ _ _ mm OK CX HREF MU WM))) as SHTB end.
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

    step. unbox FSB; unbox FDOC; unbox SHf. step. pj_store_done. box_disj. step.

    replace (lnotw (si_f I + 273)) with (Z_to_bv 64 (18446744073709551615 - (si_f I + 273)))
      by (unfold lnotw; f_equal; unfold Z.lnot, Z.pred; change (2 ^ 64) with 18446744073709551616; clear - F0 FLO LQ QT; Z.div_mod_to_equations; lia).
    gok.
    sb_shz.

    astep. astep. step. astep. astep.

    step. step. step. zstep. step.
    if_cases Kc; zify_cond Kc; pjnorm_in Kc.
    -
      ser_close HSM2 OK CX. apply evt_done.
      eapply aevt_eq; [| eapply (ctl_tailA n x0 x8 x16 x288 x296 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
    -
      zstep. pjnorm. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 _ ?mm _) =>
      assert (GROWN : forall (z : Z) (ya0 ya2 ya3 ya4 ya5 : word), z = Z.max (2 * cap) (size + n) ->
        evt bsegs (fun ms' => aevt Σ K ms')
          (KSN 0xb8bf8 xra xt0 xt1 xt2 ya0 (wz z) ya2 ya3 ya4 ya5 xa6 xa7 (wz n) (wz (size + n)) (wz t) xt3 xt4 xt5 xt6 F0 fc0 mm)) end.
      { intros z ya0 ya2 ya3 ya4 ya5 EZ.

        step. zstep.
        ser_close HSM3 OK CX. apply evt_done.
        eapply aevt_eq; [| eapply (ser_growA RT AF PMc GROW E D I _ _ _ isobj Σ (mkSbA buf size cap hp kk) _ K z X 0xb8c00)];
          [pj_st_eq| exact OK| exact CX| exact HSM3| | exact CR| exact X0| clear; lia| reflexivity|].
        { rewrite EZ. eapply (ser_req_okA RT E D I); [exact OK| exact CX| exact HSM3| cbn [sa_cap]; clear - Kc; lia|].
          cbn [sa_size]. clear - ACC BUD HTL NR. lia. }
        intros Σ' NEW m' F' yt0 yt1 yt2 za0 za1 za2 za3 za4 za5 za6 za7 yt3 yt4 yt5 yt6 HSM4 CR4.
        eapply aevt_eq; [| eapply (ctl_tailA n x0 x8 x16 x288 x296 Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW z))]; try eassumption; try pj_st_eq;
          unfold sb_grownA; cbn [sa_size sa_cap sa_buf sa_heap sa_k]; rewrite ?EZ; clear - Kc ACC SZ NR; lia. }
      if_cases K2; zify_cond K2; pjnorm_in K2.
      + eapply evt_eq; [| eapply (GROWN (size + n))]; [pj_st_eq| clear - K2 Kc; lia].
      +   zstep. eapply evt_eq; [| eapply (GROWN (2 * cap))]; [pj_st_eq| clear - K2 Kc; lia].
  Qed.
End Esc.

Definition esc_head_stmtA (fu : nat) : Prop :=
  forall (t : Z) x0 x8 x16 x288 x296 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
         (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 : word),
    l - t <= Z.of_nat fu -> 0 <= t < l ->
    SERML x0 x8 x16 x288 x296 ser_shpatA Σ st m -> frm0 fc -> sa_size st <= A + 1 + 6 * t -> CREDA RT E I Σ X st ->
    aevt Σ K (KSS 0xb88bc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs3 (wz t) xt3 xt4 xt5 xt6 F fc m).

Lemma esc_botA : forall fu, esc_head_stmtA fu -> forall t, 0 <= t < l -> l - t <= Z.of_nat (S fu) -> esc_botA_K t.
Proof using AF RC FDO MST GROW OK CX Hi HT HSTR Hdp BUD X0 HK.
  intros fu IH t HTL HF0. unfold Pj_ser_keyA_a.esc_botA_K.
  intros x0 x8 x16 x288 x296 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 HSM FRM ACC CR.
  pose proof HSTR as (C0 & L0 & CL & _).
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM.

  zstep. zstep.
  ser_close HSM2 OK CX.
  if_cases Kc; zify_cond Kc; pjnorm_in Kc.
  -
    apply evt_done.
    eapply aevt_eq; [| eapply (IH (t + 1) x0 x8 x16 x288 x296 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq;
      cbn [sa_size]; clear - HF0 HTL Kc ACC; lia.
  -
    zstep. apply evt_done.
    eapply aevt_eq; [| eapply (key_closeA x0 x8 x16 x288 x296 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq;
      cbn [sa_size]; clear - ACC HTL Kc; lia.
Qed.

Lemma esc_headA : forall fu, esc_head_stmtA fu.
Proof using AF RC FDO MST GROW OK CX Hi HT HSTR Hdp BUD X0 HK.
  induction fu as [|fu IH]; unfold esc_head_stmtA;
    intros t x0 x8 x16 x288 x296 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 HF0 HTL HSM FRM ACC CR; [lia|].
  pose proof (esc_botA fu IH t HTL HF0) as KB.
  pose proof HSTR as (C0 & L0 & CL & _).
  pose proof (S_rangeA E (c + 4 + t) OK) as BR. set (b := pa_S E (c + 4 + t)) in *.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). open HSM.

  zstep. gok.
  pose proof (shz_sbufA RT AF E D I Σ _ _ _ OK CX HREF MU WM) as SHS.
  assert (G : pa_SBUF E <= pa_SBUF E + c + 4 + t < pa_SBUF E + pa_sn E) by (clear - C0 CL HTL; lia).
  pose proof (shz_rd m _ _ SHS _ G) as RD. clear G SHS.
  astep. astep. astep. astep.

  assert (G : 0 <= c + 4 + t < pa_sn E) by (clear - C0 CL HTL; lia).
  assert (G2 : pa_SBUF E + c + 4 + t = pa_SBUF E + (c + 4 + t)) by (clear; lia).
  pose proof (read1_at m _ _ (sbuf_read_mu RT AF E D I OK CX Σ _ _ m _ HREF MU WM G) _ G2) as RD1. clear G G2. fold b in RD1.
  astep. clear RD1.

  zstep. zstep. if_cases K1; zify_cond K1; pjnorm_in K1.
  - clear RD. ser_close HSM2 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (esc_bslashA t KB HTL x0 x8 x16 x288 x296 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
  -
    zstep. zstep. if_cases K2; zify_cond K2; pjnorm_in K2.
    +
      gok. zstep. zstep. if_cases K3; zify_cond K3; pjnorm_in K3.
      * clear RD. ser_close HSM2 OK CX. apply evt_done.
        eapply aevt_eq; [| eapply (esc_plainA t KB HTL x0 x8 x16 x288 x296 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
      *
        clear RD. ser_close HSM2 OK CX. apply evt_done.
        eapply aevt_eq; [| eapply (esc_ctlA t KB HTL x0 x8 x16 x288 x296 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq;
          subst b; clear - K3 ACC; lia.
    + clear RD. ser_close HSM2 OK CX. apply evt_done.
      eapply aevt_eq; [| eapply (esc_quoteA t KB HTL x0 x8 x16 x288 x296 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
Qed.
End KeyE.
