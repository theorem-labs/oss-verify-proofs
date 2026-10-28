(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseRdKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells FsKit AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition small_res (hb n : Z) : Z := if (n <? 2^64 - 119) && (hb <? n) then -20 else n.

Section S.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (SP lo : Z).
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SPT : SP + 16 < KEND.
  Hypothesis LOS : lo <= SP - 208 - 4096.
  Hypothesis LOC : ATOP <= lo.
  Variable RNG : footprint.
  Hypothesis RSTK : rng RNG lo (SP - lo).
  Hypothesis RI : rng_aimg RNG.

#[using="lo LOS LOC"] Lemma rd_small2G : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x27 x28 x29 x30 x31 : word) m (FF n hb : Z) (Q : machine_state -> Prop),
rw_cells bsegs m (Z.shiftr FF 3 + 2147450880) RFFSH0 -> mem_inv bsegs m ->
ablk FF (FF + 64) -> FF mod 64 = 0 -> rng RNG (shad FF) 8 ->
0 <= n < 2^64 -> 0 <= hb < 8 ->
(forall m' (y10 y11 : word),
munch [(Z.shiftr FF 3 + 2147450880 + 4, Z.shiftr FF 3 + 2147450880 + 5)] m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
rw_cells bsegs m' (Z.shiftr FF 3 + 2147450880) RFFSH ->
evtF bsegs RNG Q
(MS (mkR x1 (Z_to_bv 64 (SPAz SP)) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 (SPAz SP))
y10 y11 (Z_to_bv 64 (small_res hb n)) x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 (Z_to_bv 64 hb) x24 (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x27 x28 x29 x30 x31)
F (Z_to_bv 64 0x971f0) fc None m' (seg_rom bsegs))) ->
evtF bsegs RNG Q
(MS (mkR x1 (Z_to_bv 64 (SPAz SP)) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 (SPAz SP))
(Z_to_bv 64 n) x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 (Z_to_bv 64 hb) x24 (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x27 x28 x29 x30 x31)
F (Z_to_bv 64 0x96b90) fc None m (seg_rom bsegs)).
Proof.
intros until Q. intros SHF MI FH F64 RSF Hn Hhb K.
pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in *.
pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu. pose proof atop_range as ATR. unfold KEND in SPT.
replace (shad FF) with (Z.shiftr FF 3 + 2147450880) in RSF by (unfold shad, ASHOFF; lia).
assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
unfold RFFSH0 in SHF.
pose proof (munch_refl [(Z.shiftr FF 3 + 2147450880 + 4, Z.shiftr FF 3 + 2147450880 + 5)] m) as MU.
pose proof (wmono_refl bsegs m) as WM.
zstep. zstep. zstep. zstep.
zstep. bcase B.
2: {
assert (SR : small_res hb n = -20).
{ unfold small_res. change (2^64 - 119) with 18446744073709551497.
destruct (n <? 18446744073709551497), (hb <? n); cbn in B |- *; try reflexivity; exfalso; apply B; reflexivity. }
rewrite SR in K. clear SR.
do 4 (zstep; try (replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity))).
eapply K; try eassumption. }
assert (SR : small_res hb n = n).
{ unfold small_res. change (2^64 - 119) with 18446744073709551497.
destruct (n <? 18446744073709551497), (hb <? n); cbn in B |- *; try reflexivity; discriminate B. }
rewrite SR in K. clear SR.
zstep. replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).
zstep.
zstep.
eapply K; try eassumption.
Qed.
End S.
End CANSEC1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
