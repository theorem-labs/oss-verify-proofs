(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep Frame.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim SjModel PjModel.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer SjPjCont.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.A Require Import Layout Shadow RT_iface RT_iface2 RT_iface3 RT_iface4 D_defs D_kit D_clx D_libiface I_lkit
     Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_hkit5A Atp_fzwA Pj_rtkA Pj_defsA Pj_cpsA Pj_ser_defsA Pj_ser_kitA Pj_ser_callsA Pj_ser_proA Pj_ser_topA Pj_ser_ckitA
     Pj_ser_objkA Pj_ser_skitA Pj_ser_okitA Pj_ser_okey2A_a.
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

Ltac omucx OX := let c := omuc OX in exact c.

Section OKeyE.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis GROW : grow_cpsA RT PMc.
Hypothesis TABS : forall Σ m, ART RT Σ m -> acc asegs m PJ_TABS_A PJ_TABS_LEN.
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
Hypothesis HK : forall (Σ' : rts RT) (st' : sbA) (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (y224 y232 y240 : word)
            (yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys11 yt3 yt4 yt5 yt6 : word),
    CERMA RT E C (obj_frp E C f (owK E C f (wz M32M1) (wz M32P1) (wz MNUMK) (wz M56M1) (wz ((pa_DOC E + 8) / 8 + 2147450880)) (wz (pa_DOC E + 8)) (wz (pa_DOC E)) (wz M32M8)
                                    (wz c) (wz (pa_SBUF E)) (wz (x + 1)) (wz (pa_SB E)) (wz PJ_ESC_TAB_A) (wz x) (wz (f + 64)) y224 y232 y240) obj_shpatA) Σ' st' m' ->
    frm0 fc' -> sb_accA st' x1 cx -> CCREDA RT E C Σ' (X - 2 * (x1 - (x + 1))) st' ->
    aevt Σ' K (OST E C 0xb7aa8 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 (wz (pa_DOC E)) (wz (pa_SB E + 80)) (wz x) (wz PJ_NE_TAB_A) (wz (x + 1)) (wz 92) (wz (pa_SB E)) ys11
                   yt3 yt4 yt5 yt6 F' fc' m').

Notation DATA := (pa_SBUF E + c + 4).

Notation ok2w := (Pj_ser_okey2A_a.ok2w E C f x c).
Notation CERML x224 x232 x240 Σ st m := (CERMA RT E C (obj_frp E C f (ok2w x224 x232 x240) obj_shpatA) Σ st m).

Notation OK2S pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs6 xs8 xs11 xt3 xt4 xt6 F fc m :=
  (OST E C pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (pa_SB E + 80)) xs6 (Z_to_bv 64 PJ_NE_TAB_A) xs8 (Z_to_bv 64 92) (Z_to_bv 64 (pa_SB E)) xs11
       xt3 xt4 (Z_to_bv 64 (shad (pa_SB E + 72))) xt6 F fc m).

Local Ltac slia := repeat match goal with H : _ \/ _ |- _ => clear H end; cbn [sa_size sa_cap sa_buf sa_heap sa_k]; lia.

Local Ltac sb_shz :=
  lazymatch goal with
  | HREF : CREFA _ _ _ _ _ ?mr, MU : munch _ ?mr ?mm, WM : wmono asegs ?mr ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let SHZ := fresh "SHZ" in let R64 := fresh "RD64" in let R72 := fresh "RD72" in let R80 := fresh "RD80" in
    let MUc := omuc OX in
    pose proof (shz_sb_muC RT AF E D C OK CX _ _ _ mm HREF MUc WM) as SHZ;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 64) ltac:(clear; lia)) as R64;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 72) ltac:(clear; lia)) as R72;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 80) ltac:(clear; lia)) as R80; clear SHZ
  end.

Local Ltac shf_open := match goal with SHF : rw_cells _ _ _ (sh16 _) |- _ => unfold sh16, obj_shpatA in SHF; cbn [map] in SHF | _ => idtac end.
Local Ltac shf_fold := match goal with SHF : rw_cells asegs ?m (?g / 8 + 2147450880) ?cs |- _ =>
  change (rw_cells asegs m (g / 8 + 2147450880) cs) with (rw_cells asegs m (g / 8 + 2147450880) (sh16 obj_shpatA)) in SHF | _ => idtac end.
Local Ltac open HSM := unfold Pj_ser_okey2A_a.ok2w in HSM; obj_open HSM OK CX OX; shf_open.
Local Ltac oclose HSM := shf_fold; obj_close HSM OX.

Local Ltac buf_sh a ROOM SZ b RDB SOK :=
  lazymatch goal with HREF : CREFA _ _ _ ?Σc _ ?mr, WM : wmono asegs ?mr ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let ACCB := fresh "ACCB" in let MUc := omuc OX in
    pose proof (acc_buf_muC RT AF E D C OK CX Σc _ _ mm HREF MUc WM) as ACCB; cbn [sa_buf sa_cap] in ACCB;
    destruct (acc_read1 _ _ _ a ACCB ltac:(clear - ROOM SZ; lia)) as (b & RDB & SOK); clear ACCB;
    change (wa (a / 8 + 2147450880)) with (wa (shad a)) in RDB
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

Notation kesc_botA_K := (Pj_ser_okey2A_a.kesc_botA_K RT PMc E C f K x c l A X).

Notation OK2N n pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs6 xs8 xs11 xt3 xt4 xt6 F fc m :=
  (OST E C pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 n) xs6 (Z_to_bv 64 PJ_NE_TAB_A) xs8 (Z_to_bv 64 92) (Z_to_bv 64 (pa_SB E)) xs11
       xt3 xt4 (Z_to_bv 64 (shad (pa_SB E + 72))) xt6 F fc m).

Section Esc.
  Variable t : Z.
  Hypothesis KB : kesc_botA_K t.
  Hypothesis HT : 0 <= t < l.
  Notation q_tailA := (Pj_ser_okey2A_a.q_tailA RT AF RC PMc FDO MST GROW TABS E D C f K x c l x1 cx A X OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK t KB HT).
  Notation b_tailA := (Pj_ser_okey2A_a.b_tailA RT AF RC PMc FDO MST GROW TABS E D C f K x c l x1 cx A X OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK t KB HT).

  Local Ltac entry2 TL buf size cap hp kk HSM ACC CR Kc :=

    step; step; zstep; step;
    if_cases Kc; zify_cond Kc; pjnorm_in Kc;
    [
      let HSM2 := fresh "HSM2" in oclose HSM2; apply evt_done;
      eapply aevt_eq; [| TL (mkSbA buf size cap hp kk)]; try eassumption; try pj_st_eq; slia
    |
      zstep; pjnorm; zstep; zstep ].

  Lemma esc_quoteA : forall x224 x232 x240 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 xt6 : word),
    CERML x224 x232 x240 Σ st m -> frm0 fc -> sa_size st <= A + 1 + 6 * t -> CCREDA RT E C Σ X st ->
    aevt Σ K (OK2S 0xb7630 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (DATA + t)) (wz (l - t)) xs9 (wz (DATA + t)) xt3 xt4 xt6 F fc m).
  Proof using AF RC FDO MST GROW TABS OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK KB HT.
    intros x224 x232 x240 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 xt6 HSM FRM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ostr_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM. sb_shz.

    astep. astep. step. astep. astep.
    entry2 ltac:(fun st => eapply (q_tailA x224 x232 x240 Σ st)) buf size cap hp kk HSM ACC CR Kc.
    lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 _ ?mm _) =>
    assert (GROWN : forall (z : Z) (ya0 : word), z = Z.max (2 * cap) (size + 2) ->
      evt asegs (fun ms' => aevt Σ K ms')
        (OK2S 0xb7664 xra xt0 xt1 xt2 ya0 (wz z) xa2 xa3 xa4 xa5 xa6 xa7 (wz (DATA + t)) (wz (l - t)) (wz (size + 2)) (wz (DATA + t)) xt3 xt4 xt6 F0 fc0 mm)) end.
    { intros z ya0 EZ.

      zstep. zstep.
      oclose HSM3. apply evt_done.
      eapply aevt_eq; [| eapply (cont_growA RT AF PMc GROW E D C _ Σ (mkSbA buf size cap hp kk) _ K z X 0xb766c)];
        [pj_st_eq| exact OK| exact CX| apply obj_frp_local; exact OX| exact HSM3| | exact CR| exact X0| clear; lia| reflexivity|].
      { rewrite EZ. eapply (cont_req_okA RT E D C); [exact OK| exact CX| exact HSM3| cbn [sa_cap]; clear - Kc; lia|].
        cbn [sa_size]. clear - ACC BUD HT. lia. }
      intros Σ' NEW m' F' yt0 yt1 yt2 ya0' ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CR4.
      apply (aevt_evt RT AF PMc MST). open HSM4.

      step.
      oclose HSM5. apply evt_done.
      eapply aevt_eq; [| eapply (q_tailA x224 x232 x240 Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW z))]; try eassumption; try pj_st_eq;
        unfold sb_grownA; cbn [sa_size sa_cap sa_buf sa_heap sa_k]; rewrite ?EZ; clear - Kc ACC SZ; lia. }
    if_cases K2; zify_cond K2; pjnorm_in K2.
    - eapply (GROWN (size + 2)). clear - K2 Kc; lia.
    -   zstep. eapply (GROWN (2 * cap)). clear - K2 Kc; lia.
  Qed.

  Lemma esc_bslashA : forall x224 x232 x240 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 xt6 : word),
    CERML x224 x232 x240 Σ st m -> frm0 fc -> sa_size st <= A + 1 + 6 * t -> CCREDA RT E C Σ X st ->
    aevt Σ K (OK2S 0xb76c4 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (DATA + t)) (wz (l - t)) xs9 (wz (DATA + t)) xt3 xt4 xt6 F fc m).
  Proof using AF RC FDO MST GROW TABS OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK KB HT.
    intros x224 x232 x240 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 xt6 HSM FRM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ostr_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM. sb_shz.

    astep. astep. step. astep. astep.
    entry2 ltac:(fun st => eapply (b_tailA x224 x232 x240 Σ st)) buf size cap hp kk HSM ACC CR Kc.
    lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 _ ?mm _) =>
    assert (GROWN : forall (z : Z) (ya0 : word), z = Z.max (2 * cap) (size + 2) ->
      evt asegs (fun ms' => aevt Σ K ms')
        (OK2S 0xb76f8 xra xt0 xt1 xt2 ya0 (wz z) xa2 xa3 xa4 xa5 xa6 xa7 (wz (DATA + t)) (wz (l - t)) (wz (size + 2)) (wz (DATA + t)) xt3 xt4 xt6 F0 fc0 mm)) end.
    { intros z ya0 EZ.

      zstep. zstep.
      oclose HSM3. apply evt_done.
      eapply aevt_eq; [| eapply (cont_growA RT AF PMc GROW E D C _ Σ (mkSbA buf size cap hp kk) _ K z X 0xb7700)];
        [pj_st_eq| exact OK| exact CX| apply obj_frp_local; exact OX| exact HSM3| | exact CR| exact X0| clear; lia| reflexivity|].
      { rewrite EZ. eapply (cont_req_okA RT E D C); [exact OK| exact CX| exact HSM3| cbn [sa_cap]; clear - Kc; lia|].
        cbn [sa_size]. clear - ACC BUD HT. lia. }
      intros Σ' NEW m' F' yt0 yt1 yt2 ya0' ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CR4.
      apply (aevt_evt RT AF PMc MST). open HSM4.

      step.
      oclose HSM5. apply evt_done.
      eapply aevt_eq; [| eapply (b_tailA x224 x232 x240 Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW z))]; try eassumption; try pj_st_eq;
        unfold sb_grownA; cbn [sa_size sa_cap sa_buf sa_heap sa_k]; rewrite ?EZ; clear - Kc ACC SZ; lia. }
    if_cases K2; zify_cond K2; pjnorm_in K2.
    - eapply (GROWN (size + 2)). clear - K2 Kc; lia.
    -   zstep. eapply (GROWN (2 * cap)). clear - K2 Kc; lia.
  Qed.

  Lemma p_finA : forall x224 x232 x240 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 xt6 : word),
    CERML x224 x232 x240 Σ st m -> frm0 fc -> 1 <= sa_size st -> sa_size st <= A + 1 + 6 * (t + 1) -> CCREDA RT E C Σ X st ->
    aevt Σ K (OK2S 0xb7924 xra xt0 xt1 xt2 (wz (sa_buf st + (sa_size st - 1))) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (DATA + t)) (wz (l - t)) xs9 (wz (DATA + t)) xt3 xt4 xt6 F fc m).
  Proof using AF RC FDO MST GROW TABS OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK KB HT.
    intros x224 x232 x240 Σ st m F fc xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 xt6 HSM FRM SZ1 ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf] in *.
    ostr_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM.
    pose proof (obuf_factsA RT AF E D C OK CX f Σ _ _ OX HREF) as (_ & _ & _ & _ & APB). cbn [sa_buf sa_cap] in APB.
    pose proof (APB (buf + (size - 1)) ltac:(clear - SZ1 SZ; lia)) as (A1 & A2 & A3 & A4). clear APB.

    step. pj_store_done. step.
    oclose HSM2. apply evt_done.
    eapply aevt_eq; [| eapply (KB x224 x232 x240 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
  Qed.

  Lemma p_tailA : forall x224 x232 x240 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 xt6 : word),
    CERML x224 x232 x240 Σ st m -> frm0 fc -> sa_size st + 1 <= sa_cap st -> sa_size st <= A + 1 + 6 * t -> CCREDA RT E C Σ X st ->
    aevt Σ K (OK2S 0xb78e8 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (DATA + t)) (wz (l - t)) xs9 (wz (DATA + t)) xt3 xt4 xt6 F fc m).
  Proof using AF RC FDO MST GROW TABS OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK KB HT.
    intros x224 x232 x240 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 xt6 HSM FRM ROOM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ostr_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM. sb_shz.

    step. astep. astep. astep. astep.

    step. step. step. zstep. zstep. unbox FSB; unbox SHSB. step. box_disj.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let MUc := omuc OX in pose proof (acc_buf_muC RT AF E D C OK CX Σ _ _ mm HREF MUc WM) as ACCB end.
    cbn [sa_buf sa_cap] in ACCB.
    destruct (acc_read1 _ _ _ (buf + size) ACCB ltac:(clear - ROOM SZ; lia)) as (b & RDB & SOK). clear ACCB.
    change (wa ((buf + size) / 8 + 2147450880)) with (wa (shad (buf + size))) in RDB.

    zstep. pjnorm. zstep. shfold. zstep.
    oclose HSM2.
    destruct (pj_sh_ok_cases b (buf + size) SOK) as [-> | (k & -> & K17 & KM)].
    -
      rewrite sxb_z8. zstep. if_false. apply evt_done.
      eapply aevt_eq; [| eapply (p_finA x224 x232 x240 Σ (mkSbA buf (size + 1) cap hp kk))]; try eassumption; try pj_st_eq; slia.
    -
      rewrite (pj_sxb_small7 k) by (clear - K17; lia). zstep.
      if_cases Kc; zify_cond Kc; [clear Kc| exfalso; pjnorm_in Kc; clear - Kc K17; lia].
      zstep. pjnorm. rewrite pj_land7 by (clear - R0 SZ; lia).
      zstep. if_cases Kc; zify_cond Kc;
        [clear Kc| exfalso; rewrite !pj_signed_small in Kc by (clear - K17; Z.div_mod_to_equations; lia); clear - Kc K17 KM; lia].
      apply evt_done.
      eapply aevt_eq; [| eapply (p_finA x224 x232 x240 Σ (mkSbA buf (size + 1) cap hp kk))]; try eassumption; try pj_st_eq; slia.
  Qed.

  Lemma esc_plainA : forall x224 x232 x240 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 xt6 : word),
    CERML x224 x232 x240 Σ st m -> frm0 fc -> sa_size st <= A + 1 + 6 * t -> CCREDA RT E C Σ X st ->
    aevt Σ K (OK2S 0xb78b4 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (DATA + t)) (wz (l - t)) xs9 (wz (DATA + t)) xt3 xt4 xt6 F fc m).
  Proof using AF RC FDO MST GROW TABS OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK KB HT.
    intros x224 x232 x240 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 xt6 HSM FRM ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ostr_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM. sb_shz.

    step. astep. astep. astep. astep.

    step. step. zstep. step.
    if_cases Kc; zify_cond Kc; pjnorm_in Kc.
    -
      oclose HSM2. apply evt_done.
      eapply aevt_eq; [| eapply (p_tailA x224 x232 x240 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
    -
      zstep. pjnorm. zstep. zstep.
      oclose HSM3. apply evt_done.
      eapply aevt_eq; [| eapply (cont_growA RT AF PMc GROW E D C _ Σ (mkSbA buf size cap hp kk) _ K (2 * cap) X 0xb78e4)];
        [pj_st_eq| exact OK| exact CX| apply obj_frp_local; exact OX| exact HSM3| | exact CR| exact X0| clear; lia| reflexivity|].
      { eapply (cont_req_ok2A RT E D C); [exact OK| exact CX| exact HSM3|]. cbn [sa_cap sa_size] in *. clear - Kc ACC BUD HT. lia. }
      intros Σ' NEW m' F' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CR4.
      apply (aevt_evt RT AF PMc MST). open HSM4.

      step.
      oclose HSM5. apply evt_done.
      eapply aevt_eq; [| eapply (p_tailA x224 x232 x240 Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW (2 * cap)))]; try eassumption; try pj_st_eq;
        unfold sb_grownA; slia.
  Qed.

  Lemma ctl_finA : forall (n : Z) x224 x232 x240 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 xt6 : word),
    CERML x224 x232 x240 Σ st m -> frm0 fc -> sa_size st + n <= sa_cap st -> 0 <= n -> sa_size st + n <= A + 1 + 6 * (t + 1) -> CCREDA RT E C Σ X st ->
    aevt Σ K (OK2N n 0xb78a0 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (DATA + t)) (wz (l - t)) (wz (sa_size st + n)) (wz (DATA + t)) xt3 xt4 xt6 F fc m).
  Proof using AF RC FDO MST GROW TABS OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK KB HT.
    intros n x224 x232 x240 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 xt6 HSM FRM ROOM N0 ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ostr_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM. sb_shz.

    astep. astep. unbox FSB; unbox SHSB. step. box_disj. step. step.
    oclose HSM2. apply evt_done.
    eapply aevt_eq; [| eapply (KB x224 x232 x240 Σ (mkSbA buf (size + n) cap hp kk))]; try eassumption; try pj_st_eq; slia.
  Qed.

  Lemma ctl_tailA : forall (n : Z) x224 x232 x240 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
    CERML x224 x232 x240 Σ st m -> frm0 fc -> sa_size st + n <= sa_cap st -> 1 <= n <= 7 -> sa_size st + n <= A + 1 + 6 * (t + 1) -> CCREDA RT E C Σ X st ->
    aevt Σ K (OK2N n 0xb7868 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (DATA + t)) (wz (l - t)) (wz (sa_size st + n)) (wz (DATA + t)) xt3 xt4 xt6 F fc m).
  Proof using AF RC FDO MST GROW TABS OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK KB HT.
    intros n x224 x232 x240 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 HSM FRM ROOM N17 ACC CR.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ostr_envA OK CX OX. apply (aevt_evt RT AF PMc MST). pose proof HSM as HSM0. open HSM. sb_shz.

    zstep. if_cases Kz; zify_cond Kz; pjnorm_in Kz; [exfalso; clear - Kz N17; lia|].

    step. astep. astep. astep. astep.

    step. step. step. zstep. step. zstep. zstep.

    pose proof (f1_rngA RT E D C f _ Σ _ m (f + 64) n _ _ OK CX OX HSM0 eq_refl ltac:(clear; lia) ltac:(clear -N17; lia) ltac:(clear -N17; lia))
      as (RC3 & F3a & F3b & (src & SRC & SRCL)).
    shf_fold. pose proof (f1loc_accA m f 64 SHF Ef ltac:(clear - F0; lia) ltac:(right; reflexivity)) as AC8. shf_open.
    pose proof (obuf_factsA RT AF E D C OK CX f Σ _ _ OX HREF) as (_ & _ & _ & _ & APB). cbn [sa_buf sa_cap] in APB.
    assert (APT : buf + size + n <= f + 64 \/ f + 64 + n <= buf + size).
    { apply (apart_of_pointwise (buf + size) n (f + 64) n); [| clear - N17; lia| clear - N17; lia].
      intros y Hy. pose proof (APB y ltac:(clear - Hy ROOM SZ N17; lia)) as (A1 & _). clear - A1 N17. lia. }
    clear APB.
    oclose HSM2. apply evt_done.
    eapply aevt_eq; [| eapply (cont_copyA RT AF RC PMc FDO MST e_asan_memcpy E D C _ Σ (mkSbA buf size cap hp kk) m K (f + 64) n 0xb789c src)];
      [pj_st_eq| left; reflexivity| exact OK| exact CX| apply obj_frp_local; exact OX| exact HSM2| exact SRC| exact SRCL| clear - N17; lia| cbn [sa_size sa_cap]; exact ROOM
      | eapply acc_sub; [exact AC8| clear; lia| clear - N17; lia]| exact RC3| exact F3a| exact F3b| intros _; cbn [sa_buf sa_size]; exact APT
      | clear; lia| reflexivity|].
    intros m' F' yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CPY.
    apply (aevt_evt RT AF PMc MST). open HSM4.

    step.
    oclose HSM5. apply evt_done.
    eapply aevt_eq; [| eapply (ctl_finA n x224 x232 x240 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
  Qed.

  Local Ltac escb m b MI BR HB k :=
    let G := fresh "G" in let G2 := fresh "G" in let ER := fresh "ER" in let RD := fresh "RD" in
    pose proof (esc_byte_range (8 * b + k)) as ER;
    assert (G : 0 <= 8 * b + k < 256) by (clear - BR HB; lia);
    assert (G2 : 144988 + 8 * b + k = 144988 + (8 * b + k)) by (clear; lia);
    pose proof (read1_at m _ _ (esc_readA m _ MI G) _ G2) as RD; clear G G2; unfold PJ_ESC_TAB_A in RD; astep; clear RD.

  Lemma esc_ctlA : forall x224 x232 x240 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 xt6 : word),
    pa_S E (c + 4 + t) <= 31 ->
    CERML x224 x232 x240 Σ st m -> frm0 fc -> sa_size st <= A + 1 + 6 * t -> CCREDA RT E C Σ X st ->
    aevt Σ K (OK2S 0xb7784 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (DATA + t)) (wz (l - t)) xs9 (wz (DATA + t)) xt3 xt4 xt6 F fc m).
  Proof using AF RC FDO MST GROW TABS OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK KB HT.
    intros x224 x232 x240 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 xt6 HB HSM FRM ACC CR.
    pose proof HSTR as (C0 & L0 & CL & _).
    pose proof (S_rangeA E (c + 4 + t) OK) as BR. set (b := pa_S E (c + 4 + t)) in *.
    pose proof (esc_len_range b ltac:(clear - BR HB; lia)) as NR. rewrite <- esc_len_byte in NR. set (n := esc_byte (8 * b)) in *.
    destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
    ostr_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM. unfold PJ_ESC_TAB_A in *.

    assert (G : 0 <= c + 4 + t < pa_sn E) by (clear - C0 CL HT; lia).
    assert (G2 : pa_SBUF E + c + 4 + t = pa_SBUF E + (c + 4 + t)) by (clear; lia).
    let MUc := omuc OX in pose proof (read1_at m _ _ (sbuf_read_muC RT AF E D C OK CX Σ _ _ m _ HREF MUc WM G) _ G2) as RD. clear G G2. fold b in RD.
    astep. clear RD.

    zstep. pjnorm. step. zstep.

    let MUc := omuc OX in pose proof (shz_tabs_muC RT AF E D C OK CX Σ _ _ m HREF MUc WM) as SHTB.
    assert (G : PJ_TABS_A <= 144988 + 8 * b < PJ_TABS_A + PJ_TABS_LEN) by (unfold PJ_TABS_A, PJ_TABS_LEN; clear - BR HB; lia).
    pose proof (shz_rd m _ _ SHTB _ G) as RD. clear G. do 4 astep. clear RD.
    assert (G : PJ_TABS_A <= 144988 + 8 * b + 1 < PJ_TABS_A + PJ_TABS_LEN) by (unfold PJ_TABS_A, PJ_TABS_LEN; clear - BR HB; lia).
    pose proof (shz_rd m _ _ SHTB _ G) as RD. clear G. do 4 astep. clear RD.
    pose proof (esc_byte_range (8 * b)) as ER0. fold n in ER0.
    assert (G : 0 <= 8 * b < 256) by (clear - BR HB; lia).
    pose proof (esc_readA m _ MI G) as RD. clear G. unfold PJ_ESC_TAB_A in RD. fold n in RD. astep. clear RD.
    astep.
    assert (G : PJ_TABS_A <= 144988 + 8 * b + 7 < PJ_TABS_A + PJ_TABS_LEN) by (unfold PJ_TABS_A, PJ_TABS_LEN; clear - BR HB; lia).
    pose proof (shz_rd m _ _ SHTB _ G) as RD. clear G. do 5 astep. clear RD. clear SHTB.

    escb m b MI BR HB 2. escb m b MI BR HB 3. escb m b MI BR HB 4. escb m b MI BR HB 1.
    astep. astep. astep. astep.
    escb m b MI BR HB 5. escb m b MI BR HB 6. astep. escb m b MI BR HB 7.
    do 5 astep.
    repeat match goal with |- context [Z_to_bv 64 (Z.lor ?x ?y)] => let j := fresh "jw" in set (j := Z_to_bv 64 (Z.lor x y)) in *; clearbody j end.
    repeat match goal with |- context [Z_to_bv 64 (Z.shiftr ?x ?y)] => let j := fresh "jw" in set (j := Z_to_bv 64 (Z.shiftr x y)) in *; clearbody j end.

    step. unbox FSB; unbox SHf. step. pj_store_done. step. pj_store_done. step. pj_store_done. box_disj.
    sb_shz.

    astep. astep. step. astep. astep.

    step. step. step. zstep. step.
    if_cases Kc; zify_cond Kc; pjnorm_in Kc.
    -
      oclose HSM2. apply evt_done.
      eapply aevt_eq; [| eapply (ctl_tailA n x224 x232 x240 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
    -
      zstep. pjnorm. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 _ ?mm _) =>
      assert (GROWN : forall (z : Z) (ya0 ya2 ya3 ya4 ya5 ya6 ya7 : word), z = Z.max (2 * cap) (size + n) ->
        evt asegs (fun ms' => aevt Σ K ms')
          (OK2N n 0xb785c xra xt0 xt1 xt2 ya0 (wz z) ya2 ya3 ya4 ya5 ya6 ya7 (wz (DATA + t)) (wz (l - t)) (wz (size + n)) (wz (DATA + t)) xt3 xt4 xt6 F0 fc0 mm)) end.
      { intros z ya0 ya2 ya3 ya4 ya5 ya6 ya7 EZ.

        zstep. zstep.
        oclose HSM3. apply evt_done.
        eapply aevt_eq; [| eapply (cont_growA RT AF PMc GROW E D C _ Σ (mkSbA buf size cap hp kk) _ K z X 0xb7864)];
          [pj_st_eq| exact OK| exact CX| apply obj_frp_local; exact OX| exact HSM3| | exact CR| exact X0| clear; lia| reflexivity|].
        { rewrite EZ. eapply (cont_req_okA RT E D C); [exact OK| exact CX| exact HSM3| cbn [sa_cap]; clear - Kc; lia|].
          cbn [sa_size]. clear - ACC BUD HT NR. lia. }
        intros Σ' NEW m' F' yt0 yt1 yt2 za0 za1 za2 za3 za4 za5 za6 za7 yt3 yt4 yt5 yt6 HSM4 CR4.
        apply (aevt_evt RT AF PMc MST). open HSM4.

        step.
        oclose HSM5. apply evt_done.
        eapply aevt_eq; [| eapply (ctl_tailA n x224 x232 x240 Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW z))]; try eassumption; try pj_st_eq;
          unfold sb_grownA; cbn [sa_size sa_cap sa_buf sa_heap sa_k]; rewrite ?EZ; clear - Kc ACC SZ NR; lia. }
      if_cases K2; zify_cond K2; pjnorm_in K2.
      + eapply (GROWN (size + n)). clear - K2 Kc; lia.
      +   zstep. eapply (GROWN (2 * cap)). clear - K2 Kc; lia.
  Qed.

End Esc.

Definition kesc_head_stmtA (fu : nat) : Prop :=
  forall (t : Z) x224 x232 x240 (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
         (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 xt6 : word),
    l - t <= Z.of_nat fu -> 0 <= t < l ->
    CERML x224 x232 x240 Σ st m -> frm0 fc -> sa_size st <= A + 1 + 6 * t -> CCREDA RT E C Σ X st ->
    aevt Σ K (OK2S 0xb7610 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (DATA + t)) (wz (l - t)) xs9 (wz (DATA + t)) xt3 xt4 xt6 F fc m).

Notation key_closeA := (Pj_ser_okey2A_a.okey_closeA RT AF RC PMc FDO MST GROW TABS E D C f K x c l x1 cx A X OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK).

Lemma esc_botA : forall fu, kesc_head_stmtA fu -> forall t, 0 <= t < l -> l - t <= Z.of_nat (S fu) -> kesc_botA_K t.
Proof using AF RC FDO MST GROW TABS OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK.
  intros fu IH t HT HF0. unfold Pj_ser_okey2A_a.kesc_botA_K.
  intros x224 x232 x240 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 xt6 HSM FRM ACC CR.
  pose proof HSTR as (C0 & L0 & CL & _).
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ostr_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM.

  zstep. zstep. zstep. zstep.
  oclose HSM2.
  if_cases Kc; zify_cond Kc; pjnorm_in Kc.
  -
    apply evt_done.
    eapply aevt_eq; [| eapply (IH (t + 1) x224 x232 x240 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq;
      cbn [sa_size]; clear - HF0 HT Kc ACC; lia.
  -
    zstep. apply evt_done.
    eapply aevt_eq; [| eapply (key_closeA x224 x232 x240 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq;
      cbn [sa_size]; clear - ACC HT Kc; lia.
Qed.

Lemma esc_headA : forall fu, kesc_head_stmtA fu.
Proof using AF RC FDO MST GROW TABS OK CX OX SER Hx HSTR EL CXN BUD BUD2 X2 X0 HK.
  induction fu as [|fu IH]; unfold kesc_head_stmtA;
    intros t x224 x232 x240 Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 xt6 HF0 HT HSM FRM ACC CR; [lia|].
  pose proof (esc_botA fu IH t HT HF0) as KB.
  pose proof HSTR as (C0 & L0 & CL & _).
  pose proof (S_rangeA E (c + 4 + t) OK) as BR. set (b := pa_S E (c + 4 + t)) in *.
  pose proof HSM as HSM0.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ostr_envA OK CX OX. apply (aevt_evt RT AF PMc MST). open HSM.

  let MUc := omuc OX in pose proof (shz_sbuf_muC RT AF E D C OK CX Σ _ _ m HREF MUc WM) as SHS.
  assert (G : pa_SBUF E <= pa_SBUF E + c + 4 + t < pa_SBUF E + pa_sn E) by (clear - C0 CL HT; lia).
  pose proof (shz_rd m _ _ SHS _ G) as RD. clear G.
  astep. astep. astep. astep.

  assert (G : 0 <= c + 4 + t < pa_sn E) by (clear - C0 CL HT; lia).
  assert (G2 : pa_SBUF E + c + 4 + t = pa_SBUF E + (c + 4 + t)) by (clear; lia).
  let MUc := omuc OX in pose proof (read1_at m _ _ (sbuf_read_muC RT AF E D C OK CX Σ _ _ m _ HREF MUc WM G) _ G2) as RD1. clear G G2. fold b in RD1.
  astep. clear RD1.

  zstep. if_cases K1; zify_cond K1; pjnorm_in K1.
  - clear RD. oclose HSM2. apply evt_done.
    eapply aevt_eq; [| eapply (esc_bslashA t KB HT x224 x232 x240 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
  -
    zstep. zstep. if_cases K2; zify_cond K2; pjnorm_in K2.
    +
      zstep. zstep. if_cases K3; zify_cond K3; pjnorm_in K3.
      * clear RD. oclose HSM2. apply evt_done.
        eapply aevt_eq; [| eapply (esc_plainA t KB HT x224 x232 x240 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
      *
        astep. astep. clear RD. oclose HSM2. apply evt_done.
        eapply aevt_eq; [| eapply (esc_ctlA t KB HT x224 x232 x240 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq;
          subst b; clear - K3 ACC; lia.
    + clear RD. oclose HSM2. apply evt_done.
      eapply aevt_eq; [| eapply (esc_quoteA t KB HT x224 x232 x240 Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
Qed.

End OKeyE.
