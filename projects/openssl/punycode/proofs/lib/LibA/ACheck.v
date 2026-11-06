(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit WpTac.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import AShadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Check.
Variable SEGS : list Segment.

Lemma sh_load_k : forall M x k, addr_ok M x k -> 1 <= k <= 8 -> 0 <= x -> x + k <= HIMEM_END ->
  exists u, load_ok SEGS M (W (sha x)) 1 (W u) /\ (u = 0 \/ x mod 8 + k - 1 < u <= 7).
Proof.
  intros M x k Hok Hk Hx Hhi.
  pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hm. pose proof (Z.div_mod x 8 ltac:(lia)) as Hd.
  assert (Hhi' : x + k <= 0x800000000000) by exact Hhi.
  destruct (Z_le_gt_dec (x mod 8 + k - 1) 7) as [Hle|Hgt].
  - destruct (sh_load SEGS M (x + k - 1) (Hok (x + k - 1) ltac:(lia)) ltac:(unfold HIMEM_END; lia)) as (u & Hu & Hc).
    assert (E : sha (x + k - 1) = sha x).
    { unfold sha. f_equal. replace (x + k - 1) with ((x mod 8 + k - 1) + x / 8 * 8) by lia.
      rewrite Z.div_add by lia. rewrite (Z.div_small (x mod 8 + k - 1)) by lia. lia. }
    assert (Em : (x + k - 1) mod 8 = x mod 8 + k - 1).
    { replace (x + k - 1) with ((x mod 8 + k - 1) + x / 8 * 8) by lia. rewrite Z.mod_add by lia.
      apply Z.mod_small. lia. }
    rewrite E in Hu. rewrite Em in Hc. exists u. split; [exact Hu | exact Hc].
  - destruct (sh_load SEGS M (x / 8 * 8 + 7) (Hok (x / 8 * 8 + 7) ltac:(lia)) ltac:(unfold HIMEM_END; lia)) as (u & Hu & Hc).
    assert (E : sha (x / 8 * 8 + 7) = sha x).
    { unfold sha. f_equal. replace (x / 8 * 8 + 7) with (7 + x / 8 * 8) by lia.
      rewrite Z.div_add by lia. rewrite (Z.div_small 7) by lia. lia. }
    assert (Em : (x / 8 * 8 + 7) mod 8 = 7).
    { replace (x / 8 * 8 + 7) with (7 + x / 8 * 8) by lia. rewrite Z.mod_add by lia. reflexivity. }
    rewrite E in Hu. rewrite Em in Hc. exists u. split; [exact Hu | left; lia].
Qed.

End Check.
