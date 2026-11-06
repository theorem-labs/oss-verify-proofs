(* Modified by Theorem Labs, 2026-10: relocated from omx-clap-core/fuzz_manifest lib/A/Bz/A/F_achk.v (a working branch 7e395de08f5) to libreac/fuzz_boxreg.asan: module paths changed; 0 address numerals relocated (port_addr_check 5033540ba83b predict mode, symbol + offset). *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: relocated onto omx-clap-core/fuzz_manifest.asan from a working branch 840c4afa7e2 proofs/omx-clap-core/fuzz_state/lib/A/Bz/A/F_achk.v: module paths and 0 address numerals by alreloc 7a60a01f65f446d8, each paired by object; the decided numerals are listed in the commit body. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Bz Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Bz.Lib Require Import Tac ImageA.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Bz.A Require Import Shadow.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Bz.A Require Import R_m2s I_consts I_qck D_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition chkr (m : mem) (p n : Z) : Prop :=
  acc asegs m p n
  /\ (forall i, 0 <= i < n -> exists w : word, ro_cells asegs m (al8 (shad (p + i))) [C8 w])
  /\ (region_in_mem p n /\ n <= 2^40).

Lemma chkr_chk_ok : forall m p n, chkr m p n -> chk_ok m p n.
Proof.
  intros m p n (AC & QW & RO). split; [exact AC|]. split; [| intros _; exact RO].
  intros Hn. destruct (QW 0 ltac:(lia)) as (w1 & W1). destruct (QW (n - 1) ltac:(lia)) as (w2 & W2).
  exists w1, w2. rewrite Z.add_0_r in W1. replace (p + (n - 1)) with (p + n - 1) in W2 by lia. split; assumption.
Qed.

(* Prefixes only (p' = p; ct: p <= p'): this tree's region_in_mem (I_consts.v:20-21) also bounds b + 7, which a
   later start p' does not keep. The one use (I_pcxchk2.v, the strnlen prefix of a %.Ns string) has p' = p. *)
Lemma chkr_sub : forall m p n p' n', chkr m p n -> p' = p -> p' + n' <= p + n -> 0 <= n' -> chkr m p' n'.
Proof.
  intros m p n p' n' (AC & QW & RO) H1 H2 H3. split; [| split].
  - intros i Hi. replace (p' + i) with (p + (p' - p + i)) by lia. apply AC. lia.
  - intros i Hi. replace (p' + i) with (p + (p' - p + i)) by lia. apply QW. lia.
  - destruct RO as (RIM & Hb). split; [| lia].
    unfold region_in_mem in *. lia.
Qed.

(* ct: p + n + 8 <= kHighMemEnd; this tree's region_in_mem bounds b + n and b + 7 only. *)
Lemma chkr_bound : forall m p n, chkr m p n -> 0 <= p /\ p + n <= kHighMemEnd.
Proof. intros m p n (_ & _ & (RIM & _)). unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in *. lia. Qed.

(* [comment removed for export] *)
Definition SHADOW_LO : Z := 0x7fff8000.
(* ct: 0x10007fff8007 (= kHighShadowEnd + 8, the donor's lowest lo). The Shadow bytes and words of addresses below
   kHighMemEnd end at kHighShadowEnd + 1, so the stack (lo > kHighShadowEnd, R2) stays outside. *)
Definition SHADOW_HI : Z := 0x10007fff8000.

Lemma chkr_agree : forall m m' p n, chkr m p n ->
  agree_on (fun x => SHADOW_LO <= x < SHADOW_HI) m m' -> chkr m' p n.
Proof.
  intros m m' p n C AG. pose proof (chkr_bound m p n C) as (H0 & H1). unfold kHighMemEnd in H1.
  destruct C as (AC & QW & RO). split; [| split; [| exact RO]].
  - intros i Hi. destruct (AC i Hi) as (b & Hb & Ok). exists b. split; [| exact Ok].
    apply (bytes_at_agree asegs m m' _ _ Hb). apply (agree_sub _ _ _ _ AG). intros x Hx. cbn [length] in Hx.
    unfold SHADOW_LO, SHADOW_HI, shad, SHB in *. Z.div_mod_to_equations. lia.
  - intros i Hi. destruct (QW i Hi) as (w & Hw). exists w.
    apply (ro_cells_agree asegs m m' _ _ Hw). apply (agree_sub _ _ _ _ AG). intros x Hx. cbn [cells_size csize] in Hx.
    unfold SHADOW_LO, SHADOW_HI, al8, shad, SHB in *. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma chkr_munch : forall W m m' p n, chkr m p n -> munch W m m' ->
  (forall x, SHADOW_LO <= x < SHADOW_HI -> outside W x) -> chkr m' p n.
Proof.
  intros W m m' p n C MU HW. apply (chkr_agree m m' p n C). apply (agree_of_munch W m m' _ MU). exact HW.
Qed.
