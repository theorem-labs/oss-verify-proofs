(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only Require PropExec.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Plain Require Import PImg RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.MrP0 Require Import S0HBase S0HConv S0TrTail.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section INV.
Context {RCa1 : RunCtx}.
Context {rc : runConstT}.
Variable sp0 : Z.
Hypothesis SP0 : 0x7fff80000000 <= sp0 <= 0x800000000000.
Hypothesis ATOPE : ATOP = sp0 - 8388608.

Definition fp_cli (iv : Z * Z) : Prop :=
     (ATOP <= fst iv /\ snd iv <= sp0 - 128)
  \/ (snd iv <= ATOP /\ (snd iv <= 0x10000 \/ 0x51000 <= fst iv))
  \/ (0x2fa00 <= fst iv /\ snd iv <= 0x2fa05)
  \/ (0x4fb48 <= fst iv /\ snd iv <= 0x4fd68).
Definition fp_so (iv : Z * Z) : Prop :=
  (0x1f8b0 <= fst iv /\ snd iv <= 0x1f998) \/ (0x501d0 <= fst iv /\ snd iv <= 0x505d8).
Definition fp_ok (iv : Z * Z) : Prop := fp_cli iv \/ fp_so iv.

Definition zone_iv (A n : Z) : Prop :=
  sp0 - 128 <= A
  \/ (0x10000 <= A /\ A + n <= 0x51000 /\ (A + n <= 0x2fa00 \/ 0x2fa05 <= A) /\ (A + n <= 0x4fb48 \/ 0x4fd68 <= A)
      /\ (A + n <= 0x1f8b0 \/ 0x1f998 <= A) /\ (A + n <= 0x501d0 \/ 0x505d8 <= A)).

Lemma fp_disjoint : forall W A n, Forall fp_ok W -> zone_iv A n -> 0 <= n -> disjoint_from W A n.
Proof.
  induction W as [|[lo hi] W IH]; intros A n HW HZ Hn; cbn; [exact I|].
  inversion HW as [|? ? H1 H2]; subst. split; [|apply IH; assumption].
  unfold fp_ok, fp_cli, fp_so, zone_iv in *. cbn [fst snd] in *. lia.
Qed.

Lemma fp_cli_so_outside : forall W a, Forall fp_cli W -> 0x1f8b0 <= a < 0x1f998 \/ 0x501d0 <= a < 0x505d8 -> outside W a.
Proof.
  induction W as [|[lo hi] W IH]; intros a HW Ha; cbn; [exact I|].
  inversion HW as [|? ? H1 H2]; subst. split; [|apply IH; assumption].
  unfold fp_cli in *. cbn [fst snd] in *. lia.
Qed.

Record cli_inv (M : word -> option byte) (tid : Z) : Prop := CLI_INV {
  ci_aux : rauxv_ok M sp0;
  ci_pr  : pristine_in exit_ivs M;
  ci_tid : rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 0x2fa58) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid));
  ci_frm : exists (junk : list byte) (m7 m6 m5 m4 m3 m2 m1 m0 : word),
           rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M (sp0 - 128) [CB 8 junk; C8 m7; C8 m6; C8 m5; C8 m4; C8 m3; C8 m2; C8 m1; C8 m0; C8 (Z_to_bv 64 0x1560c)]
}.

Lemma rauxv_ok_munch : forall W M M', rauxv_ok M sp0 -> munch W M M' -> wmono (run_segments psegs rc_inp rc_sp rc_mb) M M' -> Forall fp_ok W -> rauxv_ok M' sp0.
Proof.
  intros W M M' (av & auxvs & auxr & rnd & C1 & A1 & A2 & H) MU WM FW.
  exists av, auxvs, auxr, rnd. split; [|split; [|split; [|exact H]]].
  - eapply rw_cells_transport; [exact C1 | exact MU | exact WM |]. apply fp_disjoint; [exact FW | | cbn; lia].
    right. unfold RAUXV_CELL. cbn. lia.
  - eapply bytes_at_transport; [exact A1 | exact MU |]. apply fp_disjoint; [exact FW | left; lia | lia].
  - eapply bytes_at_transport; [exact A2 | exact MU |]. apply fp_disjoint; [exact FW | left; lia | lia].
Qed.

Lemma cli_inv_munch : forall W M M' tid,
  cli_inv M tid -> munch W M M' -> wmono (run_segments psegs rc_inp rc_sp rc_mb) M M' -> Forall fp_ok W -> cli_inv M' tid.
Proof.
  intros W M M' tid [AUX PR TIDC (junk & m7 & m6 & m5 & m4 & m3 & m2 & m1 & m0 & FR)] MU WM FW.
  pose proof (same_on_munch _ _ _ MU WM) as SO. constructor.
  - eapply rauxv_ok_munch; eassumption.
  - eapply pristine_in_same_on; [exact PR | exact SO |]. intros lo hi a IN Ha. split.
    + unfold exit_ivs in IN. cbn [In] in IN. repeat (destruct IN as [IN|IN]; [injection IN as <- <-; lia|]). destruct IN.
    + apply (disjoint_outside W a 1); [|lia]. apply fp_disjoint; [exact FW | | lia].
      unfold exit_ivs in IN. cbn [In] in IN. right.
      repeat (destruct IN as [IN|IN]; [injection IN as <- <-; lia|]). destruct IN.
  - rewrite <- TIDC. apply (rdn_same_on (outside W)); [exact SO | | lia | lia].
    intros x Hx. apply (disjoint_outside W x 1); [|lia]. apply fp_disjoint; [exact FW | right; lia | lia].
  - exists junk, m7, m6, m5, m4, m3, m2, m1, m0.
    eapply rw_cells_transport; [exact FR | exact MU | exact WM |]. apply fp_disjoint; [exact FW | left; lia | cbn; lia].
Qed.

Lemma cli_inv_heap : forall LB SP M M' tid,
  cli_inv M tid -> rheap_pres LB SP M M' -> SP <= sp0 - 128 -> rauxv_ok M' sp0 -> cli_inv M' tid.
Proof.
  intros LB SP M M' tid [AUX PR TIDC (junk & m7 & m6 & m5 & m4 & m3 & m2 & m1 & m0 & FR)] HP HS AUX'.
  assert (HP0 : rheap_pres [] (sp0 - 128) M M') by (eapply rheap_pres_weaken; [exact HP | lia | intros b []]).
  constructor.
  - exact AUX'.
  - eapply pristine_in_same_on; [exact PR | apply same_on_rheap_pres; exact HP0 |].
    intros lo' hi' a IN Ha. unfold exit_ivs in IN. cbn [In] in IN.
    unfold rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP.
    repeat (destruct IN as [IN|IN]; [injection IN as <- <-; split; [lia | right; left; lia]|]). destruct IN.
  - rewrite <- TIDC. apply (rdn_same_on (rclient_addr [] (sp0 - 128))); [apply same_on_rheap_pres; exact HP0 | | lia | lia].
    intros x Hx. unfold rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. right; left. lia.
  - exists junk, m7, m6, m5, m4, m3, m2, m1, m0. exact (rheap_pres_rw_cells _ _ _ _ _ _ HP0 FR ltac:(left; lia)).
Qed.

Variable so_ok : (word -> option byte) -> nat -> Prop.
Hypothesis so_frame : forall M M' k, so_ok M k ->
  (forall a, 0x1f8b0 <= a < 0x1f998 \/ 0x501d0 <= a < 0x505d8 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> so_ok M' k.

Lemma so_ok_munch : forall W M M' k, so_ok M k -> munch W M M' -> Forall fp_cli W -> so_ok M' k.
Proof.
  intros W M M' k SO MU FW. apply (so_frame M M' k SO). intros a Ha.
  apply MU. rewrite wa_unsigned by lia. apply fp_cli_so_outside; assumption.
Qed.

Lemma so_ok_heap : forall LB SP M M' k, so_ok M k -> rheap_pres LB SP M M' -> so_ok M' k.
Proof.
  intros LB SP M M' k SO HP. apply (so_frame M M' k SO). intros a Ha.
  destruct (HP a ltac:(lia)) as [E _]; [| exact E].
  unfold rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. right; left. lia.
Qed.

End INV.
