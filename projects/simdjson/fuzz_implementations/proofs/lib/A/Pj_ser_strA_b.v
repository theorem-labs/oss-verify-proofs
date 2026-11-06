(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep Frame.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel PjModel.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.A Require Import Layout Shadow RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_libiface
     Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_hkit3A Atp_hkit4A Pj_rtkA Pj_defsA Pj_cpsA Pj_ser_defsA Pj_ser_kitA Pj_ser_callsA Pj_ser_skitA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Section StrB.
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
Variable I : serI.
Variable K : config -> Prop.
Variable isobj : list byte.
Variables (i c l dp A X : Z).
Hypothesis OK : pjenvA_ok E.
Hypothesis CX : sctxA E D I.
Hypothesis Hi : 1 <= i < pa_n E.
Hypothesis HT : pa_T E i = tword t_str c.
Hypothesis HSTR : str_at (pa_S E) (pa_sn E) c l.
Hypothesis Hdp : 0 <= dp <= 15.
Hypothesis BUD : A + (2 + 6 * l) <= PJ_OUTMAX (pa_len E).
Hypothesis X0 : 0 <= X.
Hypothesis HK : av_KA RT PMc E I K isobj i dp X (A + (2 + 6 * l)).

Notation DATA := (pa_SBUF E + c + 4).

Notation XST pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m :=
  (SSTA I pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
        (Z_to_bv 64 dp) (Z_to_bv 64 (pa_SB E + 72)) (Z_to_bv 64 (SHDOCA E)) xs5 (Z_to_bv 64 i) (Z_to_bv 64 2147450880) (Z_to_bv 64 PJ_NE_TAB_A) xs9 xs10 xs11
        xt3 xt4 xt5 xt6 F fc m).

Ltac sf_rng r j :=
  let SR := fresh "SR" in let NR := fresh "NR" in
  pose proof (S_rangeA E (c + 4 + 8 * r + j) OK) as SR; pose proof (ne_val_range (pa_S E (c + 4 + 8 * r + j))) as NR.
Ltac sfD m SHS BR r j RD :=
  let k12 := eval vm_compute in (12 + j) in let G := fresh "G" in
  assert (G : pa_SBUF E <= pa_SBUF E + c + (8 * r - 8) + k12 < pa_SBUF E + pa_sn E) by (clear - BR; lia);
  pose proof (shz_rd m _ _ SHS _ G) as RD; clear G.
Ltac sfL m SB BR r j RD :=
  let k7 := eval vm_compute in (7 + j) in let G := fresh "G" in let G2 := fresh "G" in
  assert (G : 0 <= c + 4 + 8 * r + j < pa_sn E) by (clear - BR; lia);
  assert (G2 : pa_SBUF E + c + 5 + (8 * r - 8) + k7 = pa_SBUF E + (c + 4 + 8 * r + j)) by (clear; lia);
  pose proof (read1_at m _ _ (SB _ G) _ G2) as RD; clear G G2.
Ltac sfT m SHT r j RD :=
  let G := fresh "G" in
  assert (G : 0 <= pa_S E (c + 4 + 8 * r + j) < 256) by (apply S_rangeA; exact OK);
  pose proof (shz_ne m _ SHT G) as RD; clear G; unfold PJ_NE_TAB_A in RD.
Ltac sfV m MI r j RD :=
  let G := fresh "G" in
  assert (G : 0 <= pa_S E (c + 4 + 8 * r + j) < 256) by (apply S_rangeA; exact OK);
  pose proof (ne_readA m _ MI G) as RD; clear G; unfold PJ_NE_TAB_A in RD.

Ltac str_scan_round m SHS SHT SB MI BR r j :=
  let jp := eval vm_compute in (j - 1) in let RD := fresh "RD" in
  sf_rng r j;
  sfD m SHS BR r j RD; do 4 astep; clear RD;
  sfV m MI r jp RD; astep; clear RD;
  astep;
  sfL m SB BR r j RD; astep; clear RD;
  astep;
  sfT m SHT r j RD; do 4 astep; clear RD.
Ltac str_scan_round0 m SHS SHT SB MI BR r :=
  let RD := fresh "RD" in
  astep;
  sf_rng r 0;
  sfD m SHS BR r 0 RD; do 5 astep; clear RD;
  astep;
  sfL m SB BR r 0 RD; astep; clear RD;
  astep;
  sfT m SHT r 0 RD; do 4 astep; clear RD.
Ltac str_scan_tail m MI r :=
  let RD := fresh "RD" in
  astep; astep;
  sfV m MI r 7 RD; astep; clear RD;
  do 6 astep.
Ltac str_scan_block m SHS SHT SB MI BR r :=
  str_scan_round0 m SHS SHT SB MI BR r;
  str_scan_round m SHS SHT SB MI BR r 1; str_scan_round m SHS SHT SB MI BR r 2; str_scan_round m SHS SHT SB MI BR r 3;
  str_scan_round m SHS SHT SB MI BR r 4; str_scan_round m SHS SHT SB MI BR r 5; str_scan_round m SHS SHT SB MI BR r 6;
  str_scan_round m SHS SHT SB MI BR r 7;
  str_scan_tail m MI r.

Lemma str_scan8A : forall (f : nat) (r : Z) (Q : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xt0 xt1 xt2 xa0 xa3 xa4 xa5 xa6 xa7 xs10 xt3 xt4 xt5 xt6 : word),
  l - 8 * r < Z.of_nat f -> 0 <= r -> 8 * r <= l ->
  shz m (pa_SBUF E) (pa_sn E) -> shz m PJ_TABS_A PJ_TABS_LEN -> mem_inv asegs m ->
  (forall o, 0 <= o < pa_sn E -> ov_read_bytes asegs m (wa (pa_SBUF E + o)) 1 = Some [Z_to_bv 8 (pa_S E o)]) ->
  (forall (k8 : Z) (ya0 ya3 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 : word), 0 <= k8 <= l ->
     evt asegs Q (XST 0xb9074 (wz DATA) yt0 yt1 yt2 ya0 (wz (pa_SBUF E + c + 5)) (wz (Z.land l 18446744073709551608)) ya3 ya4 ya5 ya6 ya7
                    (wz l) (wz (pa_SBUF E + c)) xs10 (wz k8) yt3 yt4 xt5 xt6 F fc m)) ->
  evt asegs Q (XST 0xb8834 (wz DATA) xt0 xt1 xt2 xa0 (wz (pa_SBUF E + c + 5)) (wz (Z.land l 18446744073709551608)) xa3 xa4 xa5 xa6 xa7
                 (wz l) (wz (pa_SBUF E + c)) xs10 (wz (8 * r - 8)) xt3 xt4 xt5 xt6 F fc m).
Proof using OK CX HSTR.
  induction f as [|f IH]; intros r Q m F fc xt0 xt1 xt2 xa0 xa3 xa4 xa5 xa6 xa7 xs10 xt3 xt4 xt5 xt6 HF HR0 HRL SHS SHT MI SB EXIT; [lia|].
  pose proof HSTR as (C0 & L0 & CL & LE & _).
  str_envA OK CX.

  zstep. zstep.
  if_cases KX; zify_cond KX.
  - pjnorm_in KX.   zstep.
    pose proof (land_m8_range l ltac:(lia)) as K8R.
    eapply EXIT. lia.
  - pjnorm_in KX.

    assert (BR : 0 <= c /\ 0 <= r /\ c + 8 * r + 12 <= pa_sn E) by (clear - C0 CL KX HR0; lia).
    unfold PJ_NE_TAB_A in *.
    str_scan_block m SHS SHT SB MI BR r.

    zstep. if_cases KZ.
    + replace (Z_to_bv 64 (8 * r - 8 + 8)) with (Z_to_bv 64 (8 * (r + 1) - 8)) by (f_equal; lia).
      eapply (IH (r + 1)); [lia| lia| lia| exact SHS| exact SHT| exact MI| exact SB| exact EXIT].
    +   zstep. eapply EXIT. lia.
Qed.

Lemma str_tailA : forall (f : nat) (k : Z) (Q : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs10 xt3 xt4 xt5 xt6 : word),
  l - k <= Z.of_nat f -> 0 <= k < l ->
  shz m (pa_SBUF E) (pa_sn E) -> shz m PJ_TABS_A PJ_TABS_LEN -> mem_inv asegs m ->
  (forall o, 0 <= o < pa_sn E -> ov_read_bytes asegs m (wa (pa_SBUF E + o)) 1 = Some [Z_to_bv 8 (pa_S E o)]) ->
  (forall (k' : Z) (ya0 ya1 : word), k <= k' <= l ->
     evt asegs Q (XST 0xb9260 (wz DATA) xt0 xt1 xt2 ya0 ya1 xa2 xa3 xa4 xa5 xa6 xa7
                    (wz l) (wz (pa_SB E + 80)) xs10 (wz k') xt3 xt4 xt5 xt6 F fc m)) ->
  evt asegs Q (XST 0xb907c (wz DATA) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                 (wz l) (wz (pa_SB E + 80)) xs10 (wz k) xt3 xt4 xt5 xt6 F fc m).
Proof using OK CX HSTR.
  induction f as [|f IH]; intros k Q m F fc xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs10 xt3 xt4 xt5 xt6 HF HKL SHS SHT MI SB EXIT; [lia|].
  pose proof HSTR as (C0 & L0 & CL & LE & _).
  str_envA OK CX. unfold PJ_NE_TAB_A in *.
  pose proof (S_rangeA E (c + 4 + k) OK) as SR. pose proof (ne_val_range (pa_S E (c + 4 + k))) as NR.

  assert (G : pa_SBUF E <= pa_SBUF E + c + 4 + k < pa_SBUF E + pa_sn E) by (clear - C0 CL HKL; lia).
  pose proof (shz_rd m _ _ SHS _ G) as RD. clear G.
  do 5 astep. clear RD.

  assert (G : 0 <= c + 4 + k < pa_sn E) by (clear - C0 CL HKL; lia).
  assert (G2 : pa_SBUF E + c + 4 + k = pa_SBUF E + (c + 4 + k)) by (clear; lia).
  pose proof (read1_at m _ _ (SB _ G) _ G2) as RD. clear G G2.
  astep. clear RD.

  pose proof (shz_ne m _ SHT SR) as RD. unfold PJ_NE_TAB_A in RD.
  do 5 astep. clear RD.

  pose proof (ne_readA m _ MI SR) as RD. unfold PJ_NE_TAB_A in RD.
  astep. clear RD.
  zstep. if_cases K1.
  - eapply EXIT. clear - HKL; lia.
  -
    zstep. zstep. if_cases K2; zify_cond K2.
    + pjnorm_in K2. eapply (IH (k + 1)); [clear - HF HKL K2; lia| clear - HKL K2; lia| exact SHS| exact SHT| exact MI| exact SB|].
      intros k' ya0 ya1 Hk'. eapply EXIT. clear - Hk' HKL; lia.
    + pjnorm_in K2.   zstep. zstep.
      eapply EXIT. clear - HKL; lia.
Qed.
End StrB.
