(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit Lept_leaf Lept_objkit.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma spix_hdr_cells : forall (m : mem) A bs, rw_cells asegs m A [CB 24 bs] ->
  exists (b0 b1 b2 b3 : byte) (w1 w2 w3 w4 w5 : word),
    rw_cells asegs m A [C1 b0; C1 b1; C1 b2; C1 b3; C4 w1; C4 w2; C4 w3; C4 w4; C4 w5].
Proof.
  intros m A bs H. pose proof H as [[W _] _]. cbn in W. destruct W as [L _].
  destruct bs as [|b0 [|b1 [|b2 [|b3 rest]]]]; cbn [length] in L; try lia.
  destruct (u32s_exists 5 rest ltac:(lia)) as (ws & E & LW).
  destruct ws as [|w1 [|w2 [|w3 [|w4 [|w5 [|w6 ws]]]]]]; cbn [length] in LW; try lia.
  exists b0, b1, b2, b3, w1, w2, w3, w4, w5.
  apply (rw_cells_recell m A _ _ H); [cbn; tauto| | reflexivity].
  cbn [cells_bytes cbytes u32s app] in *. rewrite <- E. rewrite !app_nil_r. reflexivity.
Qed.

Lemma cb4_c4' : forall (m : mem) A bs, rw_cells asegs m A [CB 4 bs] -> exists x : word, rw_cells asegs m A [C4 x].
Proof.
  intros m A bs H. pose proof H as [[W _] _]. cbn in W. destruct W as [L _].
  destruct (u32s_exists 1 bs L) as (ws & E & LW). destruct ws as [|x [|y ws]]; try discriminate. exists x.
  apply (rw_cells_recell m A _ [C4 x] H); [cbn; tauto | cbn [cells_bytes cbytes u32s] in *; rewrite <- E; reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma bytes_le_to_Z_range' : forall bs : list byte, (0 <= bytes_le_to_Z bs < 2^(8 * Z.of_nat (length bs)))%Z.
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z length]; [cbn; lia|].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2^Z.of_N 8)%Z with (2^8)%Z in Hb.
  assert (Hs : (0 <= Z.shiftl (bytes_le_to_Z bs) 8)%Z) by (apply Z.shiftl_nonneg; lia).
  split. { apply Z.lor_nonneg. lia. }
  pose proof (Z.add_lor_land (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as E.
  pose proof (Z.land_nonneg (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as L.
  rewrite Z.shiftl_mul_pow2 in * by lia.
  replace (2 ^ (8 * Z.of_nat (S (length bs))))%Z with (2^8 * 2 ^ (8 * Z.of_nat (length bs)))%Z.
  2:{ rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  nia.
Qed.
Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (bytes_le_to_Z_range' bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply le_bytes_roundtrip.
Qed.
Lemma cb8_c8_in : forall (m : mem) A pre post bs, rw_cells asegs m A (pre ++ CB 8 bs :: post) ->
  rw_cells asegs m A (pre ++ C8 (le_bytes_to_word bs) :: post).
Proof.
  intros m A pre post bs [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]]. cbn in H2.
  split; [split|].
  - apply cells_wf_app. split; [exact H1|]. split; [exact I | exact H3].
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb |- *. rewrite le8_of_bytes by exact H2. exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size csize] in Hw |- *. exact Hw.
Qed.
Lemma cb4_c4_in : forall (m : mem) A pre post bs, rw_cells asegs m A (pre ++ CB 4 bs :: post) ->
  exists x : word, rw_cells asegs m A (pre ++ C4 x :: post).
Proof.
  intros m A pre post bs [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]]. cbn in H2.
  destruct (u32s_exists 1 bs H2) as (ws & E & LW). destruct ws as [|x [|y ws]]; try discriminate. exists x.
  cbn [u32s] in E. rewrite app_nil_r in E.
  split; [split|].
  - apply cells_wf_app. split; [exact H1|]. split; [exact I | exact H3].
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb |- *. rewrite E. exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size csize] in Hw |- *. exact Hw.
Qed.

(* [comment removed for export] *)
Ltac merge_low H nrest :=
  lazymatch type of H with rw_cells asegs ?mm ?A ?cs =>
    let n := eval lazy in (length cs - nrest)%nat in
    let low := list_firstn n cs in
    let rest := list_skipn n cs in
    let sz := eval lazy in (cells_size low) in
    let H2 := fresh in
    pose proof (rw_cells_merge_prefix mm A low rest H) as H2;
    change (cells_size low) with sz in H2; clear H; rename H2 into H
  end.
(* [comment removed for export] *)
Ltac ds_stops := constr:([0x515d0; 0x966a0; 0x968d0; 0x9964c; 0x99cc8; 0x99174; 0xa3aec; 0x9b020; 0x66378; 0xa1660; 0xbef8c]).
Ltac ds_ivt :=
  cbn [ivls_client];
  let zz := fresh "zz" in let Hzz := fresh "Hzz" in
  split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]].
Ltac ds_pft PFS NFA Hx :=
  let N1 := fresh "N1" in let N2 := fresh "N2" in
  cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia].
Ltac ds_refresh RT AF GP :=
  refresh RT AF; lib_refresh RT GP; unfold shad, SHB in *; unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *; park_disj.
Ltac ds_walk AF MST W := let st := ds_stops in walk_to AF MST W st.
Ltac ds_awalk := let st := ds_stops in awalk st.
(* [comment removed for export] *)
Ltac ds_to_epi RT AF AGF PFS NFA A :=
  cps_stop; art_now RT AF ltac:(ds_ivt);
  lazymatch goal with MUx : munch _ ?mm ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    agf_munch AGF MUx ltac:(fun Hx => ds_pft PFS NFA Hx) end;
  lazymatch goal with FRx : rw_cells asegs _ A _ |- _ => merge_low FRx 13%nat end;
  to_entry.
(* [comment removed for export] *)
Ltac ds_epi_null EPI FRM FSH AGF LVP :=
  eapply EPI with (pixr := 0) (v := mkPixv 0 0 0 0 0 0 0 0 0 0 0) (cv := mkCmapv 0 0 0 0);
  lazymatch goal with
  | |- ART _ _ _ => eassumption
  | |- mem_inv _ _ => assumption
  | |- stk _ _ _ _ => eassumption
  | |- rw_cells _ _ _ _ => eassumption
  | |- wr_at asegs _ _ 120 => exact (proj2 FRM)
  | |- wr_at asegs _ _ 16 => exact (proj2 FSH)
  | |- LIBH _ => assumption
  | |- io_ssp _ => assumption
  | |- agree_on _ _ _ => exact AGF
  | |- rt_frames _ _ = _ => repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity
  | |- rt_sp0 _ _ = _ => repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity
  | |- _ <= rt_credit _ _ => repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end; lia
  | |- forall e, In e _ -> In e _ => solve [live_sub_tac]
  | |- _ \/ _ => left; reflexivity
  | |- 0 = 0 -> _ => intros _; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity
  | |- 0 <> 0 -> _ => let HH := fresh "HH" in intros HH; contradiction
  | |- forall p k, In (p, k) _ -> 0 < k => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact LVP
  | |- Z.of_nat _ <= _ => repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; lia
  end.
(* [comment removed for export] *)
Ltac ds_rerr_leaf RT AF GP MST RERR EPI AGF PFS NFA FRM FSH LVP usp lo A W :=
  at_call RT AF ltac:(ds_ivt) ltac:(fun Hx => ds_pft PFS NFA Hx);
  (let RE := fresh "RE" in pose proof RERR as RE; unfold returnError_cps in RE;
   eapply cps_seq; [eapply RE with (lo := lo); rt_side idtac; [lit_in | lit_in | lenv_tac | lres_tac..] |]);
  after_call RT AF;
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]);
  ds_refresh RT AF GP;
  ds_walk AF MST W;
  ds_to_epi RT AF AGF PFS NFA A;
  ds_epi_null EPI FRM FSH AGF LVP.
(* [comment removed for export] *)
Ltac ds_msg_call RT AF GP LSE AGF PFS NFA usp lo K :=
  at_call RT AF ltac:(ds_ivt) ltac:(fun Hx => ds_pft PFS NFA Hx);
  (let SE := fresh "SE" in pose proof LSE as SE; unfold lept_stderr_cps in SE;
   eapply cps_seq; [eapply SE with (lo := lo) (kinds := K); rt_side idtac; [args_lit_tac | lres_tac..] |]);
  after_call RT AF;
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]);
  ds_refresh RT AF GP.
