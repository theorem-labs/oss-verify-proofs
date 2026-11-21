(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Fs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only Require Import PropExec CatExec CatSim StoreOk Frame Hoare RefMemcpyLib AgentLib FuzzMem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.IK Require Import TSet MstepsGrows ZStep ZMem ZPrune ZTac ZArr ZCall ZCallL ZRegKeys IGlue.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.cks Require Import CkModel CkMathCrc CkMathAdler.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.

Definition msteps_adler32A (segs : list Segment) (pc FR : Z) (ROM : mem -> Prop) : Prop :=
  forall regs m rom (retw : word) (usp a adr v len : Z),
    getr regs 1 = retw -> ret_ok retw -> getr regs 2 = Z_to_bv 64 usp ->
    getr regs 10 = Z_to_bv 64 a -> getr regs 11 = Z_to_bv 64 adr -> getr regs 12 = Z_to_bv 64 v ->
    0 <= v < 2 ^ 64 -> v mod 2 ^ 32 = len ->
    0 <= a < 2 ^ 64 -> 1 <= adr -> adr + len < 2 ^ 64 -> FR <= usp < 2 ^ 64 ->
    store_ok segs m (Z_to_bv 64 (usp - FR)) (Z.to_nat FR) = true ->
    (1 <= len -> adr + len <= usp - FR \/ usp <= adr) ->
    ROM m ->
    (forall i, 0 <= i < len -> exists b : byte, rdn segs m (Z_to_bv 64 (adr + i)) 1 = Some [b]) ->
    exists r m',
      msteps segs (mkst regs (w64 pc) m rom) (mkst r retw m' rom)
      /\ getr r 10 = Z_to_bv 64 (adler32_z_model a (bytes_at segs m adr (Z.to_nat len)))
      /\ keeps_cs regs r
      /\ frame_mod m m' [(Z_to_bv 64 (usp - FR), FR)].

Definition adler32A_spec_at (segs : list Segment) (pc FR : Z) (ROM : mem -> Prop) : Prop :=
  forall Rb l M MD T a adr v len usp ret f,
  m_halted MD = None ->
  zget_l Rb l 11%positive = a -> zget_l Rb l 12%positive = adr -> zget_l Rb l 13%positive = v ->
  zget_l Rb l 3%positive = usp -> zget_l Rb l 2%positive = ret -> Z.land ret (-2) = ret ->
  0 <= a < two64 -> 0 <= v < two64 -> v mod 4294967296 = len ->
  1 <= adr -> adr + len < two64 -> FR <= usp -> usp < two64 ->
  mem_wr segs M (usp - FR) FR -> (1 <= len -> adr + len <= usp - FR \/ usp <= adr) ->
  ROM M ->
  mem_arr 1 segs M adr len f -> (forall i, 0 <= i < len -> 0 <= f i < 256) ->
  (forall M' R',
     mpost segs M M' (usp - FR) usp 0 0 ->
     zget R' 11%positive = adler32_z_model a (flist f len) ->
     zget R' 3%positive = usp -> zget R' 4%positive = zget_l Rb l 4%positive ->
     zget R' 5%positive = zget_l Rb l 5%positive ->
     zget R' 9%positive = zget_l Rb l 9%positive -> zget R' 10%positive = zget_l Rb l 10%positive ->
     zget R' 19%positive = zget_l Rb l 19%positive -> zget R' 20%positive = zget_l Rb l 20%positive ->
     zget R' 21%positive = zget_l Rb l 21%positive -> zget R' 22%positive = zget_l Rb l 22%positive ->
     zget R' 23%positive = zget_l Rb l 23%positive -> zget R' 24%positive = zget_l Rb l 24%positive ->
     zget R' 25%positive = zget_l Rb l 25%positive -> zget R' 26%positive = zget_l Rb l 26%positive ->
     zget R' 27%positive = zget_l Rb l 27%positive -> zget R' 28%positive = zget_l Rb l 28%positive ->
     realizes segs (zcfg segs ret (zupd R' []) M' MD) T) ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.

Theorem adler32A_glue : forall segs pc FR ROM, 0 <= FR ->
  msteps_adler32A segs pc FR ROM -> adler32A_spec_at segs pc FR ROM.
Proof.
  intros segs pc FR ROM HFR AD Rb l M MD T a adr v len usp ret f
         Hh La Ladr Lv Lsp Lr Hret Ha Hv Hlen Hadr Hnw Hfr Husp HW Hapart HROM HARR Hf K.
  set (R := zupd Rb l). set (regs := zden R).
  assert (G1 : getr regs 1 = w64 ret) by (subst regs R; rewrite (getr_zupd Rb l 1) by reflexivity; key_norm; rewrite Lr; reflexivity).
  assert (G2 : getr regs 2 = w64 usp) by (subst regs R; rewrite (getr_zupd Rb l 2) by reflexivity; key_norm; rewrite Lsp; reflexivity).
  assert (G10 : getr regs 10 = w64 a) by (subst regs R; rewrite (getr_zupd Rb l 10) by reflexivity; key_norm; rewrite La; reflexivity).
  assert (G11 : getr regs 11 = w64 adr) by (subst regs R; rewrite (getr_zupd Rb l 11) by reflexivity; key_norm; rewrite Ladr; reflexivity).
  assert (G12 : getr regs 12 = w64 v) by (subst regs R; rewrite (getr_zupd Rb l 12) by reflexivity; key_norm; rewrite Lv; reflexivity).
  pose proof (mem_arr_bounds segs 1 M adr len f HARR) as (_ & Hlen0 & _ & _).
  assert (ST : store_ok segs M (Z_to_bv 64 (usp - FR)) (Z.to_nat FR) = true).
  { apply (store_ok_of_mem_wr segs M (usp - FR) FR (usp - FR) (Z.to_nat FR) HW); [lia|]. rewrite Z2Nat.id by exact HFR. lia. }
  destruct (AD regs M (seg_rom segs) (w64 ret) usp a adr v len G1 (ret_ok_of_land ret Hret) G2 G10 G11 G12
              ltac:(rewrite <- two64_eq; exact Hv) ltac:(change (2 ^ 32) with 4294967296; exact Hlen)
              ltac:(rewrite <- two64_eq; exact Ha) Hadr ltac:(rewrite <- two64_eq; exact Hnw)
              ltac:(rewrite <- two64_eq; lia) ST Hapart HROM (readable_of_mem_arr segs M adr len f HARR))
    as (regs' & M' & RUN & RES & KC & FM).
  pose proof (msteps_regs_keys segs _ _ RUN) as RK. cbn [ms_regs] in RK.
  rewrite (bytes_at_of_mem_arr segs M adr len f HARR Hf) in RES.
  set (res := adler32_z_model a (flist f len)) in RES.
  assert (Hres : 0 <= res < two64).
  { subst res. pose proof (adler32_z_model_range a (flist f len) (flist_bytes f len Hf)) as X. cbn in X |- *. lia_std. }
  set (R' := zback (gres R res) regs').
  specialize (K M' R').
  unfold realizes, zcfg, zst. cbn [cfg_ms cfg_model].
  unfold realizes, zcfg, zst in K. cbn [cfg_ms cfg_model zupd] in K.
  assert (ED : zden R' = regs') by (subst R'; apply zden_zback).
  rewrite ED in K.
  destruct K as (ms'' & RUN2 & HQ).
  - replace usp with (usp - FR + FR) at 2 by lia. apply mpost_of_frame_mod; [lia | lia | exact FM].
  - subst R'. change 11%positive with (bv_key (10%bv : reg)).
    apply (zback_val regs' (gres R res) 10 res); [reflexivity | exact RES | exact Hres | reflexivity].
  - rewrite <- Lsp. subst R' R. kept_cs (2%bv : reg).
  - subst R' R. kept_cs (3%bv : reg).
  - subst R' R. kept_cs (4%bv : reg).
  - subst R' R. kept_cs (8%bv : reg).
  - subst R' R. kept_cs (9%bv : reg).
  - subst R' R. kept_cs (18%bv : reg).
  - subst R' R. kept_cs (19%bv : reg).
  - subst R' R. kept_cs (20%bv : reg).
  - subst R' R. kept_cs (21%bv : reg).
  - subst R' R. kept_cs (22%bv : reg).
  - subst R' R. kept_cs (23%bv : reg).
  - subst R' R. kept_cs (24%bv : reg).
  - subst R' R. kept_cs (25%bv : reg).
  - subst R' R. kept_cs (26%bv : reg).
  - subst R' R. kept_cs (27%bv : reg).
  - exists ms''. split; [| exact HQ]. eapply msteps_trans; [exact RUN | exact RUN2].
Qed.

Theorem adler32_spec_at_of_A : forall segs pc FR ROM,
  adler32A_spec_at segs pc FR ROM -> adler32_spec_at segs pc FR ROM.
Proof.
  intros segs pc FR ROM A Rb l M MD T a adr v len usp ret f
         Hh La Ladr Lv Lsp Lr Hret Ha Hv Hlen Hadr Hnw Hfr Husp HW Hapart HROM HARR Hf K.
  eapply (A Rb l M MD T a adr v len usp ret f); try eassumption.
  intros Hl. left. exact (Hapart Hl).
Qed.

Theorem msteps_adler32_of_A : forall segs pc FR ROM,
  msteps_adler32A segs pc FR ROM -> msteps_adler32 segs pc FR ROM.
Proof.
  intros segs pc FR ROM A regs m rom retw usp a adr v len H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16.
  apply (A regs m rom retw usp a adr v len); try assumption. intros Hl. left. exact (H14 Hl).
Qed.
End FXG.
