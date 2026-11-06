(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AxSymExec3Sound AsanPlanCore AsanNodesRP AsanLibNode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2 AX2S ALN.
Open Scope Z_scope.

Section S. Context {fx : PropExec.FPState}.
Variable SEGS : list Segment.
Context {A : APC.atable}.

Lemma ulit_losh : forall E, bv_unsigned (edenot E (ELit LIB_LOSH)) = LIB_LOSH.
Proof. intros E. cbn [edenot]. rewrite u_lit64 by (unfold LIB_LOSH, two64; lia). apply Z.mod_small. unfold LIB_LOSH, two64. lia. Qed.
Lemma ulit_band : forall E, bv_unsigned (edenot E (ELit (LIB_KHI - LIB_LOSH))) = LIB_KHI - LIB_LOSH.
Proof. intros E. cbn [edenot]. rewrite u_lit64 by (unfold LIB_LOSH, LIB_KHI, two64; lia). apply Z.mod_small. unfold LIB_LOSH, LIB_KHI, two64. lia. Qed.
Lemma ulit_imglo : forall E, bv_unsigned (edenot E (ELit LIB_IMGLO)) = LIB_IMGLO.
Proof. intros E. cbn [edenot]. rewrite u_lit64 by (unfold LIB_IMGLO, two64; lia). apply Z.mod_small. unfold LIB_IMGLO, two64. lia. Qed.
Lemma ulit_iband : forall E, bv_unsigned (edenot E (ELit (band_hi A - LIB_IMGLO))) = band_hi A - LIB_IMGLO.
Proof. intros E. cbn [edenot]. rewrite u_lit64 by (unfold band_hi, LIB_IMGLO, LIB_IMGHI, two64; lia). apply Z.mod_small. unfold band_hi, LIB_IMGLO, LIB_IMGHI, two64. lia. Qed.
Lemma ulit_small : forall E n, 0 <= n < two64 -> bv_unsigned (edenot E (ELit n)) = n.
Proof. intros E n Hn. cbn [edenot]. rewrite u_lit64 by lia. apply Z.mod_small. lia. Qed.

Lemma app_memb_cases : forall k b bk ne lo hi nhi, app_memb k b bk ne lo hi nhi = true ->
  hi + nhi <= LIB_LOSH \/ LIB_KHI <= lo \/ ranges_apart_x k b bk ne (ELit LIB_LOSH) 0 (ELit (LIB_KHI - LIB_LOSH)) = true.
Proof.
  intros k b bk ne lo hi nhi H. unfold app_memb in H.
  apply orb_prop in H as [H|H]; [|right; right; exact H].
  apply orb_prop in H as [H|H]; apply Z.leb_le in H; [left; exact H | right; left; exact H].
Qed.
Lemma img_apartb_cases : forall k b bk n lo hi, img_apartb A k b bk n lo hi = true ->
  hi + n <= LIB_IMGLO \/ band_hi A <= lo \/ ranges_apart_x k b bk (ELit n) (ELit LIB_IMGLO) 0 (ELit (band_hi A - LIB_IMGLO)) = true.
Proof.
  intros k b bk n lo hi H. unfold img_apartb in H.
  apply orb_prop in H as [H|H]; [|right; right; exact H].
  apply orb_prop in H as [H|H]; apply Z.leb_le in H; [left; exact H | right; left; exact H].
Qed.
Lemma ctx_cellb_cases : forall k b bk n lo hi, ctx_cellb A k b bk n lo hi = true ->
  4096 <= lo /\ img_apartb A k b bk n lo hi = true /\ app_memb k b bk (ELit n) lo hi n = true /\ hi + n <= LIB_HIEND.
Proof.
  intros k b bk n lo hi H. unfold ctx_cellb in H.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H4. repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma app_memb_sound : forall E M k b bk ne lo hi nhi,
  know_ok SEGS E M k -> app_memb k b bk ne lo hi nhi = true ->
  lo <= estart E (SA b bk) <= hi -> elenZ E ne <= nhi ->
  estart E (SA b bk) + elenZ E ne <= LIB_LOSH \/ LIB_KHI <= estart E (SA b bk).
Proof.
  intros E M k b bk ne lo hi nhi HK H Hx Hn. pose proof (u64_range (edenot E ne)) as Rn. unfold elenZ in *.
  apply app_memb_cases in H. destruct H as [H|[H|H]]; [lia|lia|].
  pose proof (ranges_apart_x_sound SEGS E M k b bk ne (ELit LIB_LOSH) 0 (ELit (LIB_KHI - LIB_LOSH)) HK H) as AP.
  unfold elenZ in AP. rewrite ulit_band in AP. unfold estart in AP at 2 3. cbn [a_base a_off] in AP. rewrite ulit_losh in AP. lia.
Qed.

(* [comment removed for export] *)
Lemma img_apartb_sound : forall E M k b bk n lo hi,
  know_ok SEGS E M k -> img_apartb A k b bk n lo hi = true -> 0 <= n < two64 ->
  lo <= estart E (SA b bk) <= hi ->
  estart E (SA b bk) + n <= LIB_IMGLO \/ band_hi A <= estart E (SA b bk).
Proof.
  intros E M k b bk n lo hi HK H Hn Hx.
  apply img_apartb_cases in H. destruct H as [H|[H|H]]; [lia|lia|].
  pose proof (ranges_apart_x_sound SEGS E M k b bk (ELit n) (ELit LIB_IMGLO) 0 (ELit (band_hi A - LIB_IMGLO)) HK H) as AP.
  unfold elenZ in AP. rewrite ulit_iband, (ulit_small E n Hn) in AP. unfold estart in AP at 2 3. cbn [a_base a_off] in AP. rewrite ulit_imglo in AP. lia.
Qed.

(* [comment removed for export] *)
Lemma ctx_cellb_sound : forall E M k b bk n lo hi,
  know_ok SEGS E M k -> ctx_cellb A k b bk n lo hi = true -> 0 <= n < two64 ->
  lo <= estart E (SA b bk) <= hi ->
  4096 <= estart E (SA b bk)
  /\ (estart E (SA b bk) + n <= LIB_IMGLO \/ band_hi A <= estart E (SA b bk))
  /\ (estart E (SA b bk) + n <= LIB_LOSH \/ LIB_KHI <= estart E (SA b bk))
  /\ estart E (SA b bk) + n <= LIB_HIEND.
Proof.
  intros E M k b bk n lo hi HK H Hn Hx. apply ctx_cellb_cases in H. destruct H as (H1 & H2 & H3 & H4).
  split; [lia|]. split; [exact (img_apartb_sound E M k b bk n lo hi HK H2 Hn Hx)|].
  split; [|lia].
  pose proof (app_memb_sound E M k b bk (ELit n) lo hi n HK H3 Hx) as AP. unfold elenZ in AP. rewrite (ulit_small E n Hn) in AP. exact (AP ltac:(lia)).
Qed.

(* [comment removed for export] *)
Lemma below_or_apart_sound : forall E M k qb qk L b bk n hi lo_w (w a : Z),
  know_ok SEGS E M k -> ((hi + n <=? lo_w) || ranges_apart_x k qb qk (ELit L) b bk (ELit n))%bool = true ->
  0 <= L < two64 -> 0 <= n < two64 -> estart E (SA qb qk) = w -> estart E (SA b bk) = a -> a <= hi -> lo_w <= w ->
  a + n <= w \/ w + L <= a.
Proof.
  intros E M k qb qk L b bk n hi lo_w w a HK H HL Hn Hw Ha Hhi Hlo.
  apply orb_prop in H as [H|H]; [apply Z.leb_le in H; left; lia|].
  pose proof (ranges_apart_x_sound SEGS E M k qb qk (ELit L) b bk (ELit n) HK H) as AP.
  unfold elenZ in AP. rewrite (ulit_small E L HL), (ulit_small E n Hn), Hw, Ha in AP. lia.
Qed.
End S.
