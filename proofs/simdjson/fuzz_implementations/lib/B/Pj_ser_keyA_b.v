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
     Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_hkit3A Atp_hkit4A Pj_rtkA Pj_defsA Pj_cpsA Pj_copyA Pj_ser_trefA Pj_ser_defsA Pj_ser_kitA Pj_ser_callsA Pj_ser_skitA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).
Notation M64M1 := 18446744073709551615 (only parsing).

Ltac gok := let G := fresh "G" in zstep; if_cases G; zify_cond G; [try clear G| gref G].

Section KeyB.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable E : pjenvA.
Variable D : nat.
Variable I : serI.
Variables (i dp c l : Z).
Hypothesis OK : pjenvA_ok E.
Hypothesis CX : sctxA E D I.
Hypothesis HSTR : str_at (pa_S E) (pa_sn E) c l.

Notation DATA := (pa_SBUF E + c + 4).

Notation KSX pc xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs11 xt3 xt4 xt5 xt6 F fc m :=
  (SSTA I pc (Z_to_bv 64 DATA) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (pa_SB E + 72)) xs3 xs4 (Z_to_bv 64 l) (Z_to_bv 64 i) (Z_to_bv 64 PJ_NE_TAB_A)
        (Z_to_bv 64 (pa_SB E)) (Z_to_bv 64 2147450880) (Z_to_bv 64 dp) xs11 xt3 xt4 xt5 xt6 F fc m).

Ltac sf_rng r j :=
  let SR := fresh "SR" in let NR := fresh "NR" in
  pose proof (S_rangeA E (c + 4 + 8 * r + j) OK) as SR; pose proof (ne_val_range (pa_S E (c + 4 + 8 * r + j))) as NR.
Ltac sfD m SHS BR r j RD :=
  let k4 := eval vm_compute in (4 + j) in let G := fresh "G" in
  assert (G : pa_SBUF E <= pa_SBUF E + c + 8 * r + k4 < pa_SBUF E + pa_sn E) by (clear - BR; lia);
  pose proof (shz_rd m _ _ SHS _ G) as RD; clear G.
Ltac sfL m SB BR r j RD :=
  let k4 := eval vm_compute in (4 + j) in let G := fresh "G" in let G2 := fresh "G" in
  assert (G : 0 <= c + 4 + 8 * r + j < pa_sn E) by (clear - BR; lia);
  assert (G2 : pa_SBUF E + c + 8 * r + k4 = pa_SBUF E + (c + 4 + 8 * r + j)) by (clear; lia);
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
  zstep; gok;
  sfD m SHS BR r j RD; do 4 astep; clear RD;
  sfV m MI r jp RD; astep; clear RD;
  astep;
  sfL m SB BR r j RD; astep; clear RD;
  gok;
  astep;
  sfT m SHT r j RD; do 4 astep; clear RD.

Ltac str_scan_round1 m SHS SHT SB MI BR r :=
  let RD := fresh "RD" in
  sf_rng r 1;
  gok;
  sfD m SHS BR r 1 RD; do 4 astep; clear RD;
  sfV m MI r 0 RD; astep; clear RD;
  astep;
  sfL m SB BR r 1 RD; astep; clear RD;
  gok;
  astep;
  sfT m SHT r 1 RD; do 4 astep; clear RD.

Ltac str_scan_round0 m SHS SHT SB MI BR r :=
  let RD := fresh "RD" in
  sf_rng r 0;
  gok;
  astep;
  sfD m SHS BR r 0 RD; do 5 astep; clear RD;
  sfL m SB BR r 0 RD; astep; clear RD;
  zstep; pjnorm; gok;
  astep;
  sfT m SHT r 0 RD; do 4 astep; clear RD.
Ltac str_scan_tail m MI r :=
  let RD := fresh "RD" in
  astep; astep;
  sfV m MI r 7 RD; astep; clear RD;
  do 5 astep.
Ltac str_scan_block m SHS SHT SB MI BR r :=
  str_scan_round0 m SHS SHT SB MI BR r;
  str_scan_round1 m SHS SHT SB MI BR r;
  str_scan_round m SHS SHT SB MI BR r 2; str_scan_round m SHS SHT SB MI BR r 3;
  str_scan_round m SHS SHT SB MI BR r 4; str_scan_round m SHS SHT SB MI BR r 5; str_scan_round m SHS SHT SB MI BR r 6;
  str_scan_round m SHS SHT SB MI BR r 7;
  str_scan_tail m MI r.

Lemma key_scan8A : forall (fu : nat) (r : Z) (Q : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xt0 xt1 xt2 xa0 xa4 xa5 xa6 xa7 xs3 xs4 xs11 xt3 xt4 xt5 xt6 : word),
  l - 8 * r < Z.of_nat fu -> 0 <= r -> 8 * r <= l ->
  shz m (pa_SBUF E) (pa_sn E) -> shz m PJ_TABS_A PJ_TABS_LEN -> mem_inv bsegs m ->
  (forall o, 0 <= o < pa_sn E -> ov_read_bytes bsegs m (wa (pa_SBUF E + o)) 1 = Some [Z_to_bv 8 (pa_S E o)]) ->
  (forall (k8 : Z) (ya0 ya2 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 : word), 0 <= k8 <= l ->
     evt bsegs Q (KSX 0xb8794 yt0 yt1 yt2 ya0 (wz (M64M1 - DATA)) ya2 (wz (pa_SBUF E + c)) ya4 ya5 ya6 ya7 xs3 (wz k8) xs4 yt3 yt4 yt5 yt6 F fc m)) ->
  evt bsegs Q (KSX 0xb847c xt0 xt1 xt2 xa0 (wz (M64M1 - DATA)) (wz (8 * r)) (wz (pa_SBUF E + c)) xa4 xa5 xa6 xa7 xs3 xs11 xs4 xt3 xt4 xt5 xt6 F fc m).
Proof using OK CX HSTR.
  induction fu as [|fu IH]; intros r Q m F fc xt0 xt1 xt2 xa0 xa4 xa5 xa6 xa7 xs3 xs4 xs11 xt3 xt4 xt5 xt6 HF HR0 HRL SHS SHT MI SB EXIT; [lia|].
  pose proof HSTR as (C0 & L0 & CL & LE & _).
  str_envA OK CX.

  zstep. zstep. zstep.
  if_cases KX; zify_cond KX.
  - pjnorm_in KX. eapply EXIT. lia.
  - pjnorm_in KX.
    assert (BR : 0 <= c /\ 0 <= r /\ c + 8 * r + 12 <= pa_sn E) by (clear - C0 CL KX HR0; lia).
    unfold PJ_NE_TAB_A in *.
    str_scan_block m SHS SHT SB MI BR r.

    zstep. if_cases KZ.
    + replace (Z_to_bv 64 (8 * r + 8)) with (Z_to_bv 64 (8 * (r + 1))) by (f_equal; lia).
      eapply (IH (r + 1)); [lia| lia| lia| exact SHS| exact SHT| exact MI| exact SB| exact EXIT].
    +   zstep. eapply EXIT. lia.
Qed.

Lemma key_tailA : forall (fu : nat) (k : Z) (Q : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xt3 xt4 xt5 xt6 : word),
  l - k <= Z.of_nat fu -> 0 <= k < l ->
  shz m (pa_SBUF E) (pa_sn E) -> shz m PJ_TABS_A PJ_TABS_LEN -> mem_inv bsegs m ->
  (forall o, 0 <= o < pa_sn E -> ov_read_bytes bsegs m (wa (pa_SBUF E + o)) 1 = Some [Z_to_bv 8 (pa_S E o)]) ->
  (forall (k' : Z) (ya0 ya2 ya3 : word), k <= k' <= l ->
     evt bsegs Q (KSX 0xb87fc xt0 xt1 xt2 ya0 (wz (M64M1 - DATA)) ya2 ya3 xa4 xa5 xa6 xa7 xs3 (wz k') xs4 xt3 xt4 xt5 xt6 F fc m)) ->
  evt bsegs Q (KSX 0xb8798 xt0 xt1 xt2 xa0 (wz (M64M1 - DATA)) xa2 xa3 xa4 xa5 xa6 xa7 xs3 (wz k) xs4 xt3 xt4 xt5 xt6 F fc m).
Proof using OK CX HSTR.
  induction fu as [|fu IH]; intros k Q m F fc xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xt3 xt4 xt5 xt6 HF HKL SHS SHT MI SB EXIT; [lia|].
  pose proof HSTR as (C0 & L0 & CL & LE & _).
  str_envA OK CX. unfold PJ_NE_TAB_A in *.
  pose proof (S_rangeA E (c + 4 + k) OK) as SRk. pose proof (ne_val_range (pa_S E (c + 4 + k))) as NR.

  gok.
  assert (G : pa_SBUF E <= pa_SBUF E + c + 4 + k < pa_SBUF E + pa_sn E) by (clear - C0 CL HKL; lia).
  pose proof (shz_rd m _ _ SHS _ G) as RD. clear G.
  do 5 astep. clear RD.

  assert (G : 0 <= c + 4 + k < pa_sn E) by (clear - C0 CL HKL; lia).
  assert (G2 : pa_SBUF E + c + 4 + k = pa_SBUF E + (c + 4 + k)) by (clear; lia).
  pose proof (read1_at m _ _ (SB _ G) _ G2) as RD. clear G G2.
  astep. clear RD.

  pose proof (shz_ne m _ SHT SRk) as RD. unfold PJ_NE_TAB_A in RD.
  do 5 astep. clear RD.

  pose proof (ne_readA m _ MI SRk) as RD. unfold PJ_NE_TAB_A in RD.
  astep. clear RD.
  zstep. if_cases K1.
  - eapply EXIT. clear - HKL; lia.
  -
    zstep. zstep. if_cases K2; zify_cond K2.
    + pjnorm_in K2. eapply (IH (k + 1)); [clear - HF HKL K2; lia| clear - HKL K2; lia| exact SHS| exact SHT| exact MI| exact SB|].
      intros k' ya0 ya2 ya3 Hk'. eapply EXIT. clear - Hk' HKL; lia.
    + pjnorm_in K2.   zstep. zstep.
      eapply EXIT. clear - HKL; lia.
Qed.
End KeyB.
