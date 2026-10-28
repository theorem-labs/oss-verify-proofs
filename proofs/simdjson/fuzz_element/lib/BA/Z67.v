(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun AtpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout Shadow RT_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import IcptSpec D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_hkit2 Sj_num_akit Sj_num_amem Sj_num_aframe I_lkit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA Atp_kitA Atp_objdA Atp_objpA Atp_objkA Z6j Atp_objxA Atp_objcA Atp_objnA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma pres_ex_00 : forall live frames sp d n (m m' : mem), rt_pres_ex live frames sp 0 0 m m' -> rt_pres_ex live frames sp d n m m'.
Proof. intros live frames sp d n m m' H a Ha _. apply H; [exact Ha| lia]. Qed.

Section ObjL.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RC2 : rt_contracts2 RT.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.
  Variable d : nat.
  Hypothesis HELEM : atp_elem_cpsA RT E d.
  Variable PMc : Model -> Prop.
  Hypothesis FDO : fdfs_only PMc.
  Hypothesis MST : mat_stable PMc.
  Variables (Σ Σ1 : rts RT) (I : objI).
  Hypothesis CTX : octx RT E d Σ Σ1 I.

  Local Ltac ul := lia_prep; unfold obj_needA, arr_needA, elem_needA, ATP_LEAFB, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.
  Local Ltac oname :=
    unfold oi_b, oi_L in *;
    set (q := oi_q I) in *; set (dd := oi_dd I) in *; set (out := oi_out I) in *; set (node := oi_node I) in *; set (P := oi_P I) in *;
    set (f := oi_f I) in *; set (ptr := oi_ptr I) in *; set (i := oi_i I) in *; set (e := oi_e I) in *; set (c := oi_c I) in *;
    set (ra := oi_ra I) in *; set (gp := oi_gp I) in *; set (s0 := oi_s0 I) in *; set (s1 := oi_s1 I) in *; set (s2 := oi_s2 I) in *;
    set (s3 := oi_s3 I) in *; set (s4 := oi_s4 I) in *; set (s5 := oi_s5 I) in *; set (s6 := oi_s6 I) in *; set (s7 := oi_s7 I) in *;
    set (s8 := oi_s8 I) in *; set (s9 := oi_s9 I) in *; set (s10 := oi_s10 I) in *; set (s11 := oi_s11 I) in *; set (m0 := oi_m0 I) in *;
    set (jH := oi_jH I) in *; set (b := q + -288 - dd) in *.
  Local Ltac olia := repeat match goal with x := _ |- _ => cbv delta [x] in *; clear x end; unfold oi_b, oi_L in *; flia.

  Lemma obj_split : forall (Σc : rts RT) (m : mem) (a : Z),
    ART RT Σc m -> rt_frames RT Σc = (oi_f I, 1%nat) :: rt_frames RT Σ -> (forall x, In x (rt_live RT Σ) -> In x (rt_live RT Σc)) -> rt_sp0 RT Σc = rt_sp0 RT Σ ->
    aclient (rt_live RT Σ) (rt_frames RT Σ) (oi_q I) a -> oi_q I <= a \/ a < ae_lo E.
  Proof using AF CTX.
    intros Σc m a ART0 EF EL ES Ha. pose proof CTX as CTX'. destruct CTX' as [_ _ _ _ _ _ _ LV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
    pose proof LV as (_ & _ & _ & _ & LWIN).
    assert (Hac : aclient (rt_live RT Σc) (rt_frames RT Σc) (oi_q I) a).
    { rewrite EF. apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact EL| intros x Hx; right; exact Hx| lia]. }
    destruct (aclient_split_c RT AF Σc m (oi_q I) a ART0 Hac); [left; lia| right]. rewrite ES in *. lia.
  Qed.

  Lemma obj_mono : forall (Σc : rts RT) (sp a : Z),
    rt_frames RT Σc = (oi_f I, 1%nat) :: rt_frames RT Σ -> (forall x, In x (rt_live RT Σ) -> In x (rt_live RT Σc)) -> sp <= oi_q I ->
    aclient (rt_live RT Σ) (rt_frames RT Σ) (oi_q I) a -> aclient (rt_live RT Σc) (rt_frames RT Σc) sp a.
  Proof.
    intros Σc sp a EF EL SP Ha. rewrite EF. apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact EL| intros x Hx; right; exact Hx| exact SP].
  Qed.

  Definition ownW (r : Z * Z) : Prop :=
    (oi_b I <= fst r /\ snd r <= oi_b I + 184) \/ (oi_f I + 24 <= fst r /\ snd r <= oi_f I + 120)
    \/ (shad (oi_f I) <= fst r /\ snd r <= shad (oi_f I) + 16) \/ (oi_out I <= fst r /\ snd r <= oi_out I + 24).

  Lemma obase_munch : forall (Σc : rts RT) (W : list (Z * Z)) (m m' : mem),
    obase RT E Σ I Σc m -> rt_frames RT Σc = (oi_f I, 1%nat) :: rt_frames RT Σ -> (forall x, In x (rt_live RT Σ) -> In x (rt_live RT Σc)) -> rt_sp0 RT Σc = rt_sp0 RT Σ ->
    munch W m m' -> wmono asegs m m' -> mem_inv asegs m' -> Forall ownW W ->
    obase RT E Σ I Σc m'.
  Proof using AF CTX OK.
    intros Σc W m m' OB EF EL ES MU WM MI' HW.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    destruct OB as (MI & ART0 & ST & AI & SAVED & HIGH & HDR & PRES).
    pose proof (fun a => obj_split Σc m a ART0 EF EL ES) as SPLIT.
    pose proof LV as (_ & _ & _ & _ & LWIN).
    assert (NEWF : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) (oi_q I) a -> ~ (oi_f I <= a < oi_f I + 128) /\ ~ (shad (oi_f I) <= a < shad (oi_f I) + 16)).
    { intros a Ha. rewrite <- fs1, <- (fs1s (oi_f I)). rewrite fs1 at 2.
      apply (newframe_apartI RT AF Σ Σc m (oi_f I) 1%nat (oi_q I) a ART0 EF EL ES); [| exact Ha].
      unfold oi_b in *. pose proof (ok_lo E OK). unfold obj_needA, elem_needA, ATP_LEAFB, RT_STACK in LOR. lia. }
    assert (HinF : In (oi_f I, 1%nat) (rt_frames RT Σc)) by (rewrite EF; left; reflexivity).
    pose proof (af_sp0_range RT AF Σc m ART0) as SP0R. rewrite ES in SP0R.
    oname. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia).
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]].
    assert (LO : ae_lo E + 304 <= q) by ul.
    unfold ownW, oi_b in HW. cbn [oi_q oi_dd oi_f oi_out] in HW. fold q dd f out in HW. fold b in HW.

    assert (OW : forall a, ~ (b <= a < b + 184) -> ~ (f + 24 <= a < f + 120) -> ~ (shad f <= a < shad f + 16) -> ~ (out <= a < out + 24) -> outside W a).
    { intros a N1 N2 N3 N4. clear MU. induction W as [|[l h] W IH]; [exact Logic.I|]. inversion HW as [|x l' H1 H3]; subst. cbn [fst snd] in H1.
      cbn [outside]. split; [clear - H1 N1 N2 N3 N4; lia| exact (IH H3)]. }
    assert (AG : agree_on (fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) q a /\ ~ (out <= a < out + 24)) m m').
    { apply (agree_of_munch _ _ _ _ MU). intros x [Hx Ho]. destruct (NEWF x Hx) as [N1 N2]. destruct (SPLIT x Hx); (apply OW; flia). }
    split; [exact MI'|]. split.
    { apply (art_of_munch RT AF Σc m m' (ae_lo E) W ART0 ltac:(rewrite ES; exact LWIN)); [| exact MU| exact WM].
      clear MU OW AG. induction W as [|[l h] W IH]; [constructor|]. inversion HW as [|x l' H1 H3]; subst. cbn [fst snd] in H1.
      constructor; [| exact (IH H3)]. cbn [fst snd].
      destruct H1 as [H1|[H1|[H1|H1]]].
      - left. ul.
      - right; right; left. exists f, 1%nat. split; [exact HinF| rewrite fs1; lia].
      - right; right; right. exists f, 1%nat. split; [exact HinF| rewrite fs1s; lia].
      - left. ul. }
    split. { apply (stk_transport _ W m m' (ae_lo E) b ST MU WM). intros x Hx. left. apply OW; flia. }
    split. { apply (AINV_A_agree E m m' AI). intros x Hx. pose proof (ainv_rng_aclient RT Σ E q (bv_unsigned x) LV OK Hx) as CX.
             pose proof (ainv_rng_lo E (bv_unsigned x) OK Hx). apply AG. split; [exact CX| flia]. }
    split. { apply (rw_cells_agree asegs m m' _ _ SAVED); [| exact WM]. apply (agree_of_munch _ _ _ _ MU). intros x Hx. cbn in Hx. apply OW; flia. }
    split. { apply (rw_cells_agree asegs m m' _ _ HIGH); [| exact WM]. apply (agree_of_munch _ _ _ _ MU). intros x Hx. cbn in Hx. apply OW; flia. }
    split. { apply (rw_cells_agree asegs m m' _ _ HDR); [| exact WM]. apply (agree_of_munch _ _ _ _ MU). intros x Hx. cbn in Hx. apply OW; [flia| flia| clear - Hx FSH; lia| flia]. }
    eapply rt_pres_fp_trans; [exact PRES|]. intros a Ha Ho. apply AG. cbn [outside] in Ho. split; [exact Ha| flia].
  Qed.

  Lemma obase_call : forall (Σc : rts RT) (dst n : Z) (m m' : mem),
    obase RT E Σ I Σc m -> rt_frames RT Σc = (oi_f I, 1%nat) :: rt_frames RT Σ -> (forall x, In x (rt_live RT Σ) -> In x (rt_live RT Σc)) -> rt_sp0 RT Σc = rt_sp0 RT Σ ->
    ART RT Σc m' -> mem_inv asegs m' -> stk asegs m' (ae_lo E) (oi_b I) ->
    rt_pres_ex (rt_live RT Σc) (rt_frames RT Σc) (oi_b I) dst n m m' ->
    (forall a, dst <= a < dst + n -> aclient (rt_live RT Σ) (rt_frames RT Σ) (oi_q I) a -> oi_out I <= a < oi_out I + 24) ->
    (dst + n <= oi_b I + 184 \/ oi_q I <= dst \/ dst + n <= ae_lo E) -> (dst + n <= oi_f I \/ oi_f I + 24 <= dst \/ n <= 0) ->
    obase RT E Σ I Σc m'.
  Proof using AF CTX OK.
    intros Σc dst n m m' OB EF EL ES ART' MI' ST' PR NCL SEP1 SEP2.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    destruct OB as (MI & ART0 & ST & AI & SAVED & HIGH & HDR & PRES).
    pose proof (fun a => obj_split Σc m a ART0 EF EL ES) as SPLIT.
    pose proof (fun sp a => obj_mono Σc sp a EF EL) as MONO.
    pose proof LV as (_ & _ & _ & _ & LWIN).
    assert (HinF : In (oi_f I, 1%nat) (rt_frames RT Σc)) by (rewrite EF; left; reflexivity).
    pose proof (af_sp0_range RT AF Σc m ART0) as SP0R. rewrite ES in SP0R.
    oname. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia).
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]].
    assert (LO : ae_lo E + 304 <= q) by ul.
    assert (AGc : agree_on (fun a => aclient (rt_live RT Σc) (rt_frames RT Σc) b a /\ ~ (dst <= a < dst + n)) m m').
    { apply (agree_of_pres_ex _ _ _ _ _ m m' _ PR). intros x Hx. exact Hx. }
    assert (AG : agree_on (fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) q a /\ ~ (out <= a < out + 24)) m m').
    { intros a [Ha Ho]. apply PR; [exact (MONO b _ ltac:(lia) Ha)|]. intros Hd. exact (Ho (NCL _ Hd Ha)). }
    split; [exact MI'|]. split; [exact ART'|]. split; [exact ST'|].
    split. { apply (AINV_A_agree E m m' AI). intros x Hx. pose proof (ainv_rng_aclient RT Σ E q (bv_unsigned x) LV OK Hx) as CX.
             pose proof (ainv_rng_lo E (bv_unsigned x) OK Hx). apply AG. split; [exact CX| flia]. }
    split. { xport_core SAVED AGc ltac:(fun Hx => split; [left; unfold USTACK_TOP in *; flia| clear - Hx SEP1 DDR LO; lia]). exact SAVED. }
    split. { xport_core HIGH AGc ltac:(fun Hx => split; [left; unfold USTACK_TOP in *; flia| clear - Hx SEP1 DDR LO; lia]). exact HIGH. }
    split. { xport_core HDR AGc ltac:(fun Hx => split; [right; right; right; left; exists f, 1%nat; split; [exact HinF| rewrite fs1; flia]| clear - Hx SEP2; lia]). exact HDR. }
    eapply rt_pres_fp_trans; [exact PRES|]. intros a Ha Ho. apply AG. cbn [outside] in Ho. split; [exact Ha| flia].
  Qed.

  Lemma obj_rec : forall (m : mem) (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x24 x25 x26 x28 x29 x30 x31 : word)
      (w24 w32 w40 w48 w56 w64 w72 w88 w96 w104 w120 w128 w0 w1 we : word) (F : bvmap 5 word) (fc : bv 32)
      (rd ri err sl L0 : Z) (rest : list Z) (v4 v5 v6 : Z) (js4 jo j0 jco jt : list byte),
    obase RT E Σ I Σ1 m -> frm0 fc ->
    oi_ptr I = 47 :: rest -> zlength rest = L0 -> (sl = 18446744073709551615 \/ 0 <= sl < L0) ->
    (err = 20 \/ (err = 0 /\ rd = ae_DOC E /\ exists j', elem (ae_T E) (ae_S E) (ae_sn E) ck_any d ri j' /\ 0 <= ri /\ j' <= ae_n E - 1)) ->
    0 <= rd < 2^64 -> 0 <= ri < 2^64 ->
    rw_cells asegs m (oi_b I) (obj_locA j0 w24 w32 w40 w48 w56 w64 w72 (Z_to_bv 64 sl) w88 w96 w104 (Z_to_bv 64 (oi_out I)) w120 w128) ->
    rw_cells asegs m (oi_b I + 136) [CB 24 jco] -> rw_cells asegs m (oi_b I + 160) [C8 w0; C8 w1; C4 we; CB 4 jt] ->
    rw_cells asegs m (shad (oi_f I)) (obj_sh v4 v5 v6 js4) -> rw_cells asegs m (oi_out I) [CB 24 jo] ->
    aevt RT PMc Σ1 (Kpost RT E d Σ I PMc)
      (MS (mkR x1 (wz (oi_b I)) (oi_gp I) (wz TPV) x5 x6 x7 (wz (oi_q I)) (wz (oi_b I)) (wz rd) (wz err) x12 x13 x14 x15 x16 x17
               (wz (oi_f I)) (wz (shad (oi_f I))) (wz ri) (wz (oi_P I + 1)) (wz (oi_f I)) (wz L0) x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
          F (wz 0xb6348) fc None m (seg_rom asegs)).
  Proof using AF CTX FDO MST OK RC2 HELEM.
    intros until jt. intros OB FRM EPTR ZL0 SL HERR RD RI LOC COUT REC SH OUT.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    pose proof OB as OB0. destruct OB as (MI & ART0 & ST & AI & SAVED & HIGH & HDR & PRES).
    oname. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia).
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]].
    assert (LO : ae_lo E + 304 <= q) by ul.
    pose proof (zlength_nonneg rest) as ZLN.
    assert (ZL : zlength ptr = L0 + 1) by (rewrite EPTR, zlength_cons; lia).
    assert (CST : 0 <= rt_credit RT Σ - obj_costA d (zlength ptr)) by (unfold obj_costA, LVL_C1, DCOST in *; lia).
    apply (aevt_evt RT AF PMc MST).
    eapply (obj_w1c0 E OK _ q b rd ri err w0 w1 we); [exact MI| exact LO| lia| lia| lia| exact RD| exact RI| destruct HERR as [X|[X _]]; [right; exact X| left; exact X]| exact REC| |].
    -
      intros m1 E0 MU1 WM1 MI1 REC1. destruct HERR as [X|(_ & -> & j' & ELV & VJ0 & JN)]; [exfalso; lia|].
      pose proof (obase_munch Σ1 _ m m1 OB0 EF1 ltac:(rewrite EL1; auto) ES1 MU1 WM1 MI1 ltac:(constructor; [left; unfold oi_b; cbn; lia| constructor])) as OB1.
      mport LOC MU1 WM1. mport COUT MU1 WM1. mport SH MU1 WM1. mport OUT MU1 WM1.
      eapply (obj_tails RT AF RC2 E OK d HELEM PMc FDO MST Σ Σ1 I CTX Σ1 m1); [exact OB1| exact FRM| exact EF1| exact EL1| exact ES1| exact EPTR| exact ZL0| | exact ELV| exact VJ0| exact JN
        | exact LOC| exact COUT| exact REC1| exact SH| exact OUT].
      destruct SL as [X|X]; [left| right]; split; [exact X| rewrite EC1; unfold elem_costA, obj_costA, LVL_C1, DCOST in *; olia| exact X| rewrite EC1; unfold elem_costA, obj_costA, LVL_C1, DCOST in *; olia].
    -
      intros m1 E20 MU1 WM1 MI1 REC1.
      pose proof (obase_munch Σ1 _ m m1 OB0 EF1 ltac:(rewrite EL1; auto) ES1 MU1 WM1 MI1 ltac:(constructor; [left; unfold oi_b; cbn; lia| constructor])) as OB1.
      mport LOC MU1 WM1. mport COUT MU1 WM1. mport SH MU1 WM1. mport OUT MU1 WM1.
      eapply (obj_copyout RT AF RC2 E OK d PMc FDO MST Σ Σ1 I CTX Σ1 m1); [exact OB1| exact FRM| exact EF1| exact EL1| exact ES1| rewrite EC1; unfold elem_costA, obj_costA, LVL_C1, DCOST in *; olia
        | exact LOC| exact COUT| reflexivity| exact REC1| reflexivity| exact SH| exact OUT].
  Qed.

  Lemma obj_loop1 : forall (n : nat) (it c' : Z) (m : mem) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x17 x18 x25 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
      (sl L0 Lk : Z) (rest : list Z) (v4 v5 v6 : Z) (js4 jo j0 jco jt : list byte) (w24 w32 w40 w128 : word),
    obase RT E Σ I Σ1 m -> frm0 fc ->
    oi_ptr I = 47 :: rest -> zlength rest = L0 -> (sl = 18446744073709551615 \/ 0 <= sl < L0) -> 0 <= Lk <= L0 ->
    tiles (field (ae_T E) (ae_S E) (ae_sn E) (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d)) it (oi_e I) c' -> it <> oi_e I -> 0 <= it -> oi_e I - it <= Z.of_nat n ->
    rw_cells asegs m (oi_b I) (obj_locA j0 w24 w32 w40 (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 L0) (Z_to_bv 64 (oi_f I)) (Z_to_bv 64 (oi_f I)) (Z_to_bv 64 sl)
                                 (Z_to_bv 64 4294967295) (Z_to_bv 64 4294967297) (Z_to_bv 64 (oi_P I + 1)) (Z_to_bv 64 (oi_out I)) (Z_to_bv 64 67240448) w128) ->
    rw_cells asegs m (oi_b I + 136) [CB 24 jco] -> rw_cells asegs m (oi_b I + 160) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 12); CB 4 jt] ->
    rw_cells asegs m (shad (oi_f I)) (obj_sh v4 v5 v6 js4) -> rw_cells asegs m (oi_out I) [CB 24 jo] ->
    aevt RT PMc Σ1 (Kpost RT E d Σ I PMc)
      (MS (mkR x1 (wz (oi_b I)) (oi_gp I) (wz TPV) x5 x6 x7 (wz (oi_q I)) (wz (oi_b I)) x10 x11 x12 x13 x14 (wz (ae_TAPE E)) (wz 32) x17
               x18 (wz (shad (oi_f I))) (wz it) (wz (ae_TAPE E + 8)) (wz 72057594037927935) (wz (ae_SBUF E)) (wz Lk) x25 (wz (oi_e I)) (wz 2147450880) x28 x29 x30 x31)
          F (wz 0xb61e4) fc None m (seg_rom asegs)).
  Proof using AF CTX FDO MST OK RC2 HELEM.
    induction n as [|n IH]; intros until w128; intros OB FRM EPTR ZL0 SL LK TI NE IT0 FUEL LOC COUT REC SH OUT.
    { pose proof (tiles_le _ (field_lt _ _ _ _ (elem_lt _ _ _ _ d)) _ _ _ TI). lia. }
    pose proof (rc2_rt RT RC2) as RC.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    pose proof OB as OB0. destruct OB as (MI & ART0 & ST & AI & SAVED & HIGH & HDR & PRES).
    oname. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia).
    pose proof OK as OK'. destruct OK' as [WF SBS P1F P1L (T16 & NT8 & TN & TS & TL) (S16 & NS8 & SN & SS & SL') PTRR P0' (D8 & DF & DL & DS & DT) LOW [HL HT]].
    pose proof LV as (LVT & LVS & _ & _ & LWIN).
    pose proof (af_sp0_range RT AF Σ1 m ART0) as SP0R. rewrite ES1 in SP0R.
    assert (LO : ae_lo E + 304 <= q) by ul.
    assert (EU : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit; ul).
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (zlength_nonneg rest) as ZLN.
    pose proof (lvl_ptr_range E OK P ptr PAT ltac:(rewrite EPTR; discriminate)) as (PB0 & PB1 & PB2 & PB3).
    rewrite EPTR, zlength_cons, ZL0 in PB2.
    pose proof (a_live_mono RT Σ Σ1 E LV ltac:(rewrite EL1; auto) ltac:(rewrite EF1; intros x Hx; right; exact Hx) ES1) as LV1.
    pose proof (lvl_live_ptr RT E Σ1 P ptr LV1 PAT ltac:(rewrite EPTR; discriminate)) as INPB.
    assert (INS : In (ae_SBUF E, ae_NS E) (rt_live RT Σ1)) by (rewrite EL1; exact LVS).
    destruct (object_iter _ _ _ _ (fun c cv H => H) HSN d it e c' TI NE IT0 ltac:(lia)) as (j' & STR & EL & IJ & AFT & TI').

    assert (ADV : forall (m2 : mem) (FF : bvmap 5 word) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y17 y18 y28 y29 y30 y31 : word),
      obase RT E Σ I Σ1 m2 ->
      rw_cells asegs m2 b (obj_locA j0 w24 w32 w40 (wz (ae_DOC E)) (wz L0) (wz f) (wz f) (wz sl) (wz 4294967295) (wz 4294967297) (wz (P + 1)) (wz out) (wz 67240448) w128) ->
      rw_cells asegs m2 (b + 136) [CB 24 jco] -> rw_cells asegs m2 (b + 160) [C8 (wz 0); C8 (wz 0); C4 (wz 12); CB 4 jt] ->
      rw_cells asegs m2 (shad f) (obj_sh v4 v5 v6 js4) -> rw_cells asegs m2 out [CB 24 jo] ->
      aevt RT PMc Σ1 (Kpost RT E d Σ I PMc)
        (MS (mkR y1 (wz b) gp (wz TPV) y5 y6 y7 (wz q) (wz b) y10 y11 y12 y13 y14 (wz (ae_TAPE E)) (wz 32) y17
                 y18 (wz (shad f)) (wz it) (wz (ae_TAPE E + 8)) (wz 72057594037927935) (wz (ae_SBUF E)) (wz Lk) (wz (8 * it)) (wz e) (wz 2147450880) y28 y29 y30 y31)
            FF (wz 0xb6280) fc None m2 (seg_rom asegs))).
    { intros m2 FF y1 y5 y6 y7 y10 y11 y12 y13 y14 y17 y18 y28 y29 y30 y31 OB2 LOC2 COUT2 REC2 SH2 OUT2.
      pose proof OB2 as (MI2 & ART2 & ST2 & AI2 & _).
      apply (aevt_evt RT AF PMc MST).
      eapply (obj_l1adv E OK d _ q b P L0 Lk f e it j'); [exact MI2| exact LO| lia| lia| lia| exact AI2| exact (lvl_shz_tape RT AF E OK Σ1 m2 ART2 LV1)| exact EL| flia| flia| flia| exact EN| exact LOC2| |].
      - intros xa0 xa1 xa2 NE'.
        eapply (IH j' (c' - 1) m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FF); [exact OB2| exact FRM| exact EPTR| exact ZL0| exact SL| exact LK| exact TI'| exact NE'| flia| flia| exact LOC2| exact COUT2| exact REC2| exact SH2| exact OUT2].
      - intros xa2 ->.
        eapply (obj_rec m2); [exact OB2| exact FRM| exact EPTR| exact ZL0| exact SL| left; reflexivity| flia| flia| exact LOC2| exact COUT2| exact REC2| exact SH2| exact OUT2]. }

    assert (RET : forall (m2 : mem) (FF : bvmap 5 word) (r y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
      obase RT E Σ I Σ1 m2 ->
      rw_cells asegs m2 b (obj_locA j0 w24 w32 w40 (wz (ae_DOC E)) (wz L0) (wz f) (wz f) (wz sl) (wz 4294967295) (wz 4294967297) (wz (P + 1)) (wz out) (wz 67240448) w128) ->
      rw_cells asegs m2 (b + 136) [CB 24 jco] -> rw_cells asegs m2 (b + 160) [C8 (wz 0); C8 (wz 0); C4 (wz 12); CB 4 jt] ->
      rw_cells asegs m2 (shad f) (obj_sh v4 v5 v6 js4) -> rw_cells asegs m2 out [CB 24 jo] ->
      aevt RT PMc Σ1 (Kpost RT E d Σ I PMc)
        (MS (mkR (wz 0xb6270) (wz b) gp (wz TPV) y5 y6 y7 (wz q) (wz b) r y11 y12 y13 y14 y15 y16 y17
                 (wz Lk) (wz (shad f)) (wz it) (wz (ae_TAPE E + 8)) (wz 72057594037927935) (wz (ae_SBUF E)) (wz (ae_TAPE E)) (wz (8 * it)) (wz e) (wz 2147450880) y28 y29 y30 y31)
            FF (wz 0xb6270) fc None m2 (seg_rom asegs))).
    { intros m2 FF r y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 OB2 LOC2 COUT2 REC2 SH2 OUT2.
      pose proof OB2 as (MI2 & _).
      apply (aevt_evt RT AF PMc MST).
      eapply (obj_l1ret E OK _ q b P L0 Lk f e it r); [exact MI2| exact LO| flia| flia| flia| ul| exact LOC2| |].
      - intros _. eapply (obj_rec m2); [exact OB2| exact FRM| exact EPTR| exact ZL0| exact SL| | ul| flia| exact LOC2| exact COUT2| exact REC2| exact SH2| exact OUT2].
        right. split; [reflexivity|]. split; [reflexivity|]. exists j'. split; [exact EL|]. split; [flia| flia].
      - intros _. apply ADV; assumption. }

    apply (aevt_evt RT AF PMc MST).
    eapply (obj_l1body E OK _ q b P L0 Lk f e it); [exact MI| exact LO| flia| flia| flia| ul| exact AI| exact (lvl_shz_tape RT AF E OK Σ1 m ART0 LV1)| | exact STR| flia| flia| exact EN| exact LOC| |].
    { pose proof (shz_live RT AF Σ1 m _ _ ART0 INS ltac:(clear - S16; Z.div_mod_to_equations; lia)) as X.
      replace (8 * (ae_NS E / 8)) with (ae_NS E) in X by (clear - NS8; Z.div_mod_to_equations; lia). exact X. }
    2:{ intros l xa1 xa2 xa3 xa4 SA NEQ. apply ADV; assumption. }
    intros l xa3 xa4 SA ELK.
    pose proof (str_at_bounds _ _ HSN _ _ SA) as (O0 & L0b & OL & LE & O56).
    set (o := tval (ae_T E it)) in *.
    pose proof (obj_cok RT E OK d Σ Σ1 I CTX Σ1 m ES1 ST) as COK. fold b in COK.
    destruct (Z.eq_dec Lk 0) as [LK0|LKP].
    -
      rewrite LK0.
      eapply (aevt_memcmp0 RT PMc FDO MST RC2 Σ1); [reflexivity| exact ART0| exact MI| exact COK|].
      intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m' (ART' & MI' & WM' & ST') PR'.
      rewrite EU in ST', PR'. rewrite (ret_pc_even 0xb6270) by lia.
      pose proof (obase_call Σ1 0 0 m m' OB0 EF1 ltac:(rewrite EL1; auto) ES1 ART' MI' ST' PR' ltac:(intros a Ha; lia) ltac:(left; unfold oi_b; flia) ltac:(right; right; lia)) as OBm.
      pose proof (agree_of_pres_ex _ _ _ _ _ m m' (fun x => aclient (rt_live RT Σ1) (rt_frames RT Σ1) b x /\ ~ (0 <= x < 0 + 0)) PR' (fun x H => H)) as AG.
      assert (HinF : In (f, 1%nat) (rt_frames RT Σ1)) by (rewrite EF1; left; reflexivity).
      xport_stack LOC AG. xport_stack COUT AG. xport_stack REC AG. xport_shadow SH AG HinF. xport_stack OUT AG.
      rewrite <- LK0. apply RET; assumption.
    -
      pose proof (ptr_atA_facts E P ptr m OK PAT (proj1 (proj2 (proj2 AI)))) as (PTRB & _ & _ & _ & PL).
      rewrite EPTR in PTRB. rewrite EPTR, zlength_cons, ZL0 in PL. pose proof (bytes_at_skipn _ _ _ 1 PTRB ltac:(cbn; lia)) as KEYB.
      change (skipn 1 (map (Z_to_bv 8) (47 :: rest))) with (map (Z_to_bv 8) rest) in KEYB. replace (P + Z.of_nat 1) with (P + 1) in KEYB by lia.
      pose proof (bytes_at_firstn _ _ _ (Z.to_nat Lk) KEYB) as KEYL. rewrite firstn_map in KEYL.
      assert (LKB : length (map (Z_to_bv 8) (firstn (Z.to_nat Lk) rest)) = Z.to_nat Lk) by (rewrite length_map, firstn_length_le; [reflexivity| unfold zlength in ZL0; lia]).
      destruct (sbuf_bytesA_at E m o Lk (proj1 (proj2 AI)) ltac:(flia) ltac:(flia) ltac:(flia)) as [QB QL].
      eapply (aevt_memcmpW RT PMc FDO MST RC2 Σ1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (P + 1) (ae_SBUF E + o + 4) (map (Z_to_bv 8) (firstn (Z.to_nat Lk) rest)) (sbuf_bytesA E o Lk) (ae_lo E));
        [reflexivity| reflexivity| rewrite LKB; f_equal; flia| rewrite QL, LKB; reflexivity| ul| ul| rewrite LKB; flia| rewrite LKB; ul| exact KEYL| exact QB| | | exact ART0| exact MI| exact COK|].
      { rewrite LKB. apply (checked_src_live RT AF Σ1 m _ (ae_lo E) (ae_PB E) (ae_NPB E) (P + 1) _ ART0 INPB); [flia| flia| rewrite ES1; exact LWIN]. }
      { rewrite LKB. apply (checked_src_live RT AF Σ1 m _ (ae_lo E) (ae_SBUF E) (ae_NS E) _ _ ART0 INS); [flia| flia| rewrite ES1; exact LWIN]. }
      intros r t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m' HR (ART' & MI' & WM' & ST') PR'.
      rewrite EU in ST', PR'. rewrite (ret_pc_even 0xb6270) by lia.
      pose proof (obase_call Σ1 0 0 m m' OB0 EF1 ltac:(rewrite EL1; auto) ES1 ART' MI' ST' PR' ltac:(intros a Ha; lia) ltac:(left; unfold oi_b; flia) ltac:(right; right; lia)) as OBm.
      pose proof (agree_of_pres_ex _ _ _ _ _ m m' (fun x => aclient (rt_live RT Σ1) (rt_frames RT Σ1) b x /\ ~ (0 <= x < 0 + 0)) PR' (fun x H => H)) as AG.
      assert (HinF : In (f, 1%nat) (rt_frames RT Σ1)) by (rewrite EF1; left; reflexivity).
      clear KEYB KEYL PTRB QB. xport_stack LOC AG. xport_stack COUT AG. xport_stack REC AG. xport_shadow SH AG HinF. xport_stack OUT AG.
      apply RET; assumption.
  Qed.

  Lemma obj_noesc : forall (m : mem) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x26 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
      (sl L0 Lk : Z) (rest : list Z) (v4 v5 v6 : Z) (js4 jo j0 jco jt : list byte) (w24 w32 w40 w48 w56 w64 w72 w88 w96 w104 w128 : word),
    obase RT E Σ I Σ1 m -> frm0 fc ->
    oi_ptr I = 47 :: rest -> zlength rest = L0 -> (sl = 18446744073709551615 \/ 0 <= sl < L0) -> 0 <= Lk <= L0 ->
    rw_cells asegs m (oi_node I) [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 (oi_i I))] ->
    rw_cells asegs m (oi_b I) (obj_locA j0 w24 w32 w40 w48 w56 w64 w72 (Z_to_bv 64 sl) w88 w96 w104 (Z_to_bv 64 (oi_out I)) (Z_to_bv 64 (oi_node I)) w128) ->
    rw_cells asegs m (oi_b I + 136) [CB 24 jco] -> rw_cells asegs m (oi_b I + 160) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 12); CB 4 jt] ->
    rw_cells asegs m (shad (oi_f I)) (obj_sh v4 v5 v6 js4) -> rw_cells asegs m (oi_out I) [CB 24 jo] ->
    aevt RT PMc Σ1 (Kpost RT E d Σ I PMc)
      (MS (mkR x1 (wz (oi_b I)) (oi_gp I) (wz TPV) x5 x6 x7 (wz (oi_q I)) (wz (oi_b I)) x10 x11 x12 x13 x14 x15 x16 x17
               (wz (oi_f I)) (wz (shad (oi_f I))) (wz (oi_L I)) (wz (oi_P I + 1)) (wz (oi_f I)) (wz L0) (wz Lk) x25 x26 (wz 2147450880) x28 x29 x30 x31)
          F (wz 0xb60a0) fc None m (seg_rom asegs)).
  Proof using AF CTX FDO MST OK RC2 HELEM.
    intros until w128. intros OB FRM EPTR ZL0 SL LK NODE LOC COUT REC SH OUT.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    pose proof OB as OB0. destruct OB as (MI & ART0 & ST & AI & SAVED & HIGH & HDR & PRES).
    oname. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia).
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]].
    assert (LO : ae_lo E + 304 <= q) by ul.
    pose proof (a_live_mono RT Σ Σ1 E LV ltac:(rewrite EL1; auto) ltac:(rewrite EF1; intros x Hx; right; exact Hx) ES1) as LV1.
    pose proof (tiles_le _ (field_lt _ _ _ _ (elem_lt _ _ _ _ d)) _ _ _ TILES) as [IE CC].
    assert (OWL : Forall (ownW) [(b, b + 136)]) by (constructor; [left; unfold oi_b; cbn; lia| constructor]).
    unfold oi_L.
    pose proof LV as (_ & _ & _ & _ & LWIN).
    assert (FPb : fp_ok RT Σ1 (ae_lo E) [(b, b + 136)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).
    assert (ARTm : forall m', munch [(b, b + 136)] m m' -> wmono asegs m m' -> ART RT Σ1 m').
    { intros m' MU WM. exact (art_of_munch RT AF Σ1 m m' (ae_lo E) _ ART0 ltac:(rewrite ES1; exact LWIN) FPb MU WM). }
    apply (aevt_evt RT AF PMc MST).
    eapply (obj_n1 E OK _ q b P (zlength ptr) L0 Lk f i e c node); [exact MI| exact LO| lia| lia| lia| exact AI| exact NODE| exact QN| exact NB| exact TY| exact NXT| exact I0| exact EN| exact IE| exact LOC| | | | |].
    - intros m' MU WM. apply (lvl_shz_rec RT AF E OK Σ1 m' node 16 (ARTm m' MU WM) LV1); [lia| lia| exact N8| reflexivity| lia].
    - intros m' MU WM. apply (lvl_shz_doc E OK). apply (AINV_A_munch E _ m m' OK AI MU). constructor; [cbn; lia| constructor].
    - intros m' MU WM. exact (lvl_shz_tape RT AF E OK Σ1 m' (ARTm m' MU WM) LV1).
    -
      intros m1 xa2 xa3 Ee MU1 WM1 MI1 LOC1.
      pose proof (obase_munch Σ1 _ m m1 OB0 EF1 ltac:(rewrite EL1; auto) ES1 MU1 WM1 MI1 OWL) as OB1.
      mport COUT MU1 WM1. mport REC MU1 WM1. mport SH MU1 WM1. mport OUT MU1 WM1.
      eapply (obj_rec m1); [exact OB1| exact FRM| exact EPTR| exact ZL0| exact SL| left; reflexivity| flia| flia| exact LOC1| exact COUT| exact REC| exact SH| exact OUT].
    -
      intros m1 xa0 xa1 xa2 xa3 NE1 MU1 WM1 MI1 LOC1.
      pose proof (obase_munch Σ1 _ m m1 OB0 EF1 ltac:(rewrite EL1; auto) ES1 MU1 WM1 MI1 OWL) as OB1.
      mport COUT MU1 WM1. mport REC MU1 WM1. mport SH MU1 WM1. mport OUT MU1 WM1.
      eapply (obj_loop1 (S (Z.to_nat (e - (i + 1)))) (i + 1) c m1); [exact OB1| exact FRM| exact EPTR| exact ZL0| exact SL| exact LK| exact TILES| exact NE1| lia| lia
        | exact LOC1| exact COUT| exact REC| exact SH| exact OUT].
  Qed.
End ObjL.
