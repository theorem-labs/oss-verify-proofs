(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_decode/lib/A/DecodeARowsFill.v (donor image sha256 5973b76807d8), with its module paths changed, names decodesegs0 -> tfibsegs. *)
(* libreac/fuzz_decode image A (fuzz_decode.asan): the zero-fill row H_CALLOC_FILL of lib/A/DecodeClose.v:254,
   [decode_zero_fill_spec_A B] (lib/A/DecodeCallocRt.v:331, [zero_fill_specP] :250-266 at DEC_A_memset).

   The entry.  DEC_A_memset (DecodeCallocRt.v:124) = 0x92474 = tfib_A_musl_memset (lib/A/AB1w.v:551), the entry
   the machine run lib/A/AE3d.v:1050 [tfib_memset] starts at.  Measured in image A:
     fuzz_decode.objdump.txt:102972 `0000000000092474 <memset>:`
     (first instruction :102973 `92474: 0e060a63 beqz a2,92568`, last :103034 `92568: 00008067 ret`);
     fuzz_decode.nm.txt:1585 `0000000000092474 00000000000000f8 W memset` (248 bytes, 62 instructions).
   The image.  decodesegs0 (lib/A/DecodeTFIB.v:19) and tfibsegs (lib/A/AB1v.v:13) are both
   OSSVerify.libreac.fuzz_decode.images.Asan.M.loaded_segments, so the two are the same term, and
   [dec_a_fill] states the row exactly as DecodeCallocRt.v does and closes it by conversion from [musl_memset_srr].

   The proof composes two proved pieces:
   - the machine run [tfib_memset] (AE3d.v:1050): from the entry with a0 = d, a1 = x, a2 = n and every byte of
     [d, d + n) storable in the restricted memory, msteps reach the caller's ra with [d, d + n) := x mod 256, a0 = d
     and every register but a1 .. a6 kept;
   - the AR-frame post of lib/A/AE6t.v:348 [ms_tail], the musl-memset leg of lib/A/AE2r.v's path2L / path2H (the
     legs of [asan_memset_realizes], AE2r.v:568): [dest_ok] gives each byte of [d, d + n) writable (so not hidden)
     and not owned, and [AR_frame_law] (YG0d.v:439) keeps AR because no owned byte changes, no visible byte
     disappears, the model changes only in its materialized pages and no hidden byte changes.
   musl memset is a leaf: it calls nothing, never names sp and returns with `ret`, so no stack window is written
   and the frame here is [d, d + n) alone (the post's ESTACK exclusion is not used).  [asan_memset_realizes] is not
   reused: its entry is __asan_memset and it takes the three shadow premises.  AR_laws is YG0q.v:804
   [AR_laws_ok] (no premise); the row needs no symbol record, so this file takes no premise. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AB1w AE3d AE20 AE2y.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require DecodeCallocRt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require DecodeCallocKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* [zero_fill_specP]'s statement over tfibsegs at tfib_A_musl_memset. *)
Lemma musl_memset_srr : forall (B : asyms) ly S (W : world tfibsegs) regs mem md d x n,
ecall_pre tfibsegs B ly S W regs mem md ->
getr regs 10 = w64 d -> getr regs 11 = w64 x -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d ->
d + n <= 2 ^ 63 ->
dest_ok tfibsegs B ly S W regs mem d n ->
SRr tfibsegs W (cfg_at tfibsegs tfib_A_musl_memset regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
AR tfibsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 d /\
(forall i, 0 <= i < n -> aview tfibsegs (w_H W) mem' (d + i) = Some (x mod 256)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regs - ESTACK <= a < spZ regs) ->
aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
intros B ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST.
pose proof (YG0q.AR_laws_ok tfibsegs B) as LAWS.
pose proof HPRE as (HAR & Hra & _).
pose proof AF0x.Hwx_tfa as Hwx.
assert (Hjr : v_jalr (getr regs 1) 0 = w64 (raZ regs)) by (unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; exact Hra).
(* [dest_ok]: each byte of [d, d + n) is writable in the restricted memory, hence not hidden. *)
assert (DW : forall a, d <= a < d + n -> writable_at tfibsegs (mrestrict (w_H W) mem) a /\ w_H W (Z_to_bv 64 a) = false).
{ intros a Ha. destruct (HDST a Ha) as (Hw & _ & _).
split; [exact Hw|]. destruct (w_H W (Z_to_bv 64 a)) eqn:Hh; [|reflexivity].
exfalso. exact (AE2y.hidden_not_writable W mem a ltac:(lia) Hh Hw). }
set (nn := Z.to_nat n). assert (Hnn : Z.of_nat nn = n) by (subst nn; lia).
assert (SOK : store_ok tfibsegs (mrestrict (w_H W) mem) (w64 d) nn = true).
{ apply store_ok_of_all; unfold w64; rewrite unsigned_lit_small by lia; [lia|].
intros z Hz. pose proof (proj1 (DW (bv_unsigned z) ltac:(lia))) as Wz. unfold writable_at in Wz.
rewrite Z_to_bv_bv_unsigned in Wz. exact Wz. }
(* The machine run of musl memset (AE3d.v:1050). *)
destruct (tfib_memset (w64 d) (w64 x) (w64 n) nn (mrestrict (w_H W) mem) (seg_rom tfibsegs) regs G10 G11 G12
ltac:(unfold w64; rewrite unsigned_lit_small by lia; lia) SOK ltac:(unfold w64; rewrite unsigned_lit_small by lia; lia))
as (regs2 & Hms & A10 & Hkeep).
rewrite Hjr in Hms.
set (cb := Z_to_bv 8 (bv_unsigned (w64 x) mod 256)) in Hms.
set (m1r := mrestrict (w_H W) mem) in *. set (m2r := wbytes m1r (w64 d) (repeat cb nn)) in Hms.
set (mem2 := munrestrict (w_H W) mem m2r).
assert (LEN : Z.of_nat (length (repeat cb nn)) = n) by (rewrite repeat_length; exact Hnn).
(* The memory after the run: [d, d + n) holds cb, every other byte is the entry's. *)
assert (M2out : forall z : word, ~ (d <= bv_unsigned z < d + n) -> mem2 z = mem z).
{ intros z Hz. subst mem2 m2r. unfold munrestrict. destruct (w_H W z) eqn:Hh; [reflexivity|].
assert (Ew : wbytes m1r (w64 d) (repeat cb nn) z = m1r z).
{ destruct (Z_lt_le_dec (bv_unsigned z) d) as [L|L].
- apply wbytes_below; unfold w64; rewrite ?LEN, unsigned_lit_small by lia; lia.
- apply wbytes_above. unfold w64. rewrite LEN, unsigned_lit_small by lia. lia. }
rewrite Ew. subst m1r. unfold mrestrict. rewrite Hh. reflexivity. }
assert (M2in : forall i, 0 <= i < n -> mem2 (Z_to_bv 64 (d + i)) = Some cb).
{ intros i Hi. subst mem2. unfold munrestrict. rewrite (proj2 (DW (d + i) ltac:(lia))).
subst m2r. rewrite (wbytes_inside (repeat cb nn) m1r (w64 d) (Z_to_bv 64 (d + i)));
unfold w64; rewrite ?LEN, ?unsigned_lit_small by lia; [|lia|lia].
replace (Z.to_nat (d + i - d)) with (Z.to_nat i) by lia. apply nth_error_repeat. lia. }
assert (MPT : forall z : word, mem2 z = mem z \/ (w_H W z = false /\ mem2 z = Some cb)).
{ intros z. destruct (Z_lt_le_dec (bv_unsigned z) d) as [L|L]; [left; apply M2out; lia|].
destruct (Z_lt_le_dec (bv_unsigned z) (d + n)) as [L2|L2]; [|left; apply M2out; lia].
right. pose proof (M2in (bv_unsigned z - d) ltac:(lia)) as E.
replace (d + (bv_unsigned z - d)) with (bv_unsigned z) in E by lia. rewrite Z_to_bv_bv_unsigned in E.
split; [|exact E].
pose proof (proj2 (DW (bv_unsigned z) ltac:(lia))) as E2. rewrite Z_to_bv_bv_unsigned in E2. exact E2. }
change (cfg_at tfibsegs tfib_A_musl_memset regs mem md)
with (mkCfg (mkst regs (Z_to_bv 64 tfib_A_musl_memset) mem (seg_rom tfibsegs)) md).
eapply (SRr_msteps tfibsegs Hwx W); [rewrite restrict_mkst_fx; exact Hms|].
intros model' Hsbm _.
pose proof (same_but_materialized_frame md model' Hsbm) as MF.
apply SRr_ret. cbv beta. split; [reflexivity|].
exists regs2, mem2, model'.
split; [reflexivity|].
split; [|split; [|split; [|split; [|split; [|split]]]]].
- (* AR: no owned byte changes ([dest_ok]), no visible byte disappears, no hidden byte changes. *)
apply (al_frame _ _ LAWS ly S W mem md mem2 model' HAR).
+ intros a Hr Hown. apply AF0x.aview_same. apply M2out. rewrite unsigned_lit_small by lia.
intros Hd'. exact (proj1 (proj2 (HDST a Hd')) Hown).
+ intros a Hv. unfold aview, mbyte, mrestrict in Hv |- *.
destruct (MPT (Z_to_bv 64 a)) as [E|[Eh E]]; rewrite E; [exact Hv|].
rewrite Eh. cbn. discriminate.
+ apply MF. + apply MF. + apply MF.
+ intros a Hb Hh. exact (AE2y.hs_kept_unrestrict (w_H W) mem m2r a Hb Hh).
- (* callee-saved registers: tfib_memset keeps every register but a1 .. a6. *)
intros r Hr. unfold acallee_saved in Hr.
assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
apply Hkeep; intros E; apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate E.
- exact Hsbm.
- exact A10.
- intros i Hi. unfold aview, mbyte, mrestrict. rewrite (proj2 (DW (d + i) ltac:(lia))), (M2in i Hi). cbn [option_map].
f_equal. subst cb. unfold w64. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (256 * 2 ^ 56).
change (bv_modulus 8) with 256.
rewrite Z.mod_mod by lia. apply Z.mod_mod_divide. exists (2 ^ 56). reflexivity.
- intros a Hr Hd' _. apply AF0x.aview_same. apply M2out. rewrite unsigned_lit_small by lia. exact Hd'.
- intros a [Hh [b Hb]]. destruct (MPT (Z_to_bv 64 a)) as [E|[Eh E]].
+ split; [exact Hh|]. exists b. rewrite E. exact Hb.
+ split; [exact Eh|]. exists cb. exact E.
Qed.
End c.

(* H_CALLOC_FILL (DecodeClose.v:254), for every symbol record B. *)
Theorem dec_a_fill : forall (fx : YK11.FPState) (rc : YM05.RunCeil) (B : asyms),
DecodeCallocRt.decode_zero_fill_spec_A B.
Proof.
intros fx rc B. unfold DecodeCallocRt.decode_zero_fill_spec_A, DecodeCallocKit.zero_fill_specP.
intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST.
exact (musl_memset_srr B ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST).
Qed.
