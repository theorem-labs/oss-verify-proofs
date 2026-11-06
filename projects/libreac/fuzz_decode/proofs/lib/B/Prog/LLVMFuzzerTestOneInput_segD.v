(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* LLVMFuzzerTestOneInput_segD: the INSPECT segment of the image-B (asan-ubsan) walk of libreac/fuzz_decode's
   LLVMFuzzerTestOneInput, i.e. llvm_b_inspect_stmt of lib/B/Prog/LLVMFuzzerTestOneInput_segs.v: offsets
   +0x418 .. +0x5c8 of the listing lib/B/Prog/DecodeBList.v, from the return of malloc #2 (llvm_b_st_418) to
   the return of reac_decode (llvm_b_st_5cc).

   The code (DecodeBList.v slots 262..370, decoded from the audited listing):
     +0x418 sd a0,88(s1)      the decode buffer is spilled
     +0x41c beqz a0,+0xb88    refuted by 4096 <= out
     +0x420..+0x42c           reac_frame_inspect (copy, length, mode)
     +0x430..+0x43c           a1 = 1492, 24(s1) = length, 40(s1) = copy, the `bne s4,a1` of the length test
     +0x440..+0x508           on the 1492 path: the four header / trailer bytes of the copy (+12, +13, +1490,
                              +1491), each behind a UBSan pointer-overflow guard and an ASan shadow check, and
                              s3 := the last byte's test; the other paths set s3 := 0 (+0x50c, +0x514)
     +0x518..+0x524           s4 reloaded, the inspect result's high half against s3, and the `beqz` that skips
                              the counter check when the frame is not well formed
     +0x528..+0x590           on the well-formed path: the two counter bytes (+14, +15) behind the same guards,
                              and their 16-bit value against the inspect result's low half
     +0x594..+0x59c           reac_frame_counter and its result against the same 16-bit value
     +0x5a0..+0x5b4           s2 := the `prod < 481` flag, s6 := the buffer, and __asan_memset(buffer, 0xa5, olen)
     +0x5b8..+0x5c8           reac_decode (copy, length, mode, buffer)
   Refuted inside, never stepped: the ASan report guards +0x468, +0x498, +0x4c8, +0x4f8, +0x55c, +0x578 (their
   slow paths return into the fast path, which is what the token engine's shadow check models); the abort edges
   +0x41c, +0x520, +0x590, +0x59c into +0xb88; and the eight UBSan guards into +0xb84 (+0x440, +0x528 copy null;
   +0x44c, +0x47c, +0x4ac, +0x4dc, +0x534, +0x540 the pointer-overflow tests of copy + 12 / 13 / 0x5d2 / 0x5d3 /
   14 / 15).

   The leaf calls are the shared bridge lib/B/Prog/LLVMFuzzerTestOneInput_leafb.v (dec_leafb_inspect,
   dec_leafb_counter, dec_leafb_decode), the memset is the kit's aj_intrin_atS, and the Pa run is
   lib/B/Prog/DecodeBPaLib.v's paj_run_tok / paj_run_to_tok / psrr_branch_tok, as lib/B/Prog/LLVMFuzzerTestOneInput_segA.v
   and boxreg's lib/A/Prog/ReadName.v (a working branch) use them. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0j YK0o.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0p YG0s YCbq YC5d YI00 YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaRun PaShadow PaJournal PaStep.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import YC1g YC1h YC81 YC4b YC85.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import
DecodeBSyms DecodeBList DecodeBAddr DecodeBPa DecodeBImg DecodeBPaLib.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import
check_round_trip_cg LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_leafb.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YM03.v:182-189 (through PaTable.v) redefines lia / nia globally; this file uses YM03.v:179-180's originals. *)
Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
Local Ltac Lia.nia ::= Zify.zify; xnia zchecker.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Module DCells := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.AsanCells.

(* ------------------------------------------------------------------ *)
(* 1. The symbolic state at +0x418                                      *)
(* ------------------------------------------------------------------ *)

(* The realigned spill area at s1 (atom 9) the segment reads and writes: it writes 88 (+0x418), 24 (+0x434) and
   40 (+0x438); it reads 32 (the shadow base) at every shadow check, 40 (the copy) and 24 (the length). The
   slots 0 / 8 / 16 (the fake frame's three spills), 56 / 64 / 72 (the geometry) and 112 (the frame) are carried
   so that the segment's post can state them again; no store of this segment touches them. *)
Definition dsd_spill : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 120 24 96
    [YP09.mkChunk 0 (CVal 8 (SOff 40 0)); YP09.mkChunk 8 (CVal 8 (SOff 41 0));
     YP09.mkChunk 16 (CVal 8 (SOff 40 0)); YP09.mkChunk 32 (CVal 8 (SOff 32 0));
     YP09.mkChunk 56 (CVal 8 (SOff 42 0)); YP09.mkChunk 64 (CVal 8 (SOff 43 0));
     YP09.mkChunk 72 (CVal 8 (SOff 44 0)); YP09.mkChunk 112 (CVal 8 (SOff 40 0))].
(* The atoms above the registers: 32 the shadow base (the engine's Bx), 40 the fake frame, 41 its shadow
   address, 42 / 43 / 44 the three geometry words of the spill area. *)
Definition dsd_extra (F SH ns32 nch32 ns64 : Z) : list word :=
  [Z_to_bv 64 SB; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
   Z_to_bv 64 0; Z_to_bv 64 F; Z_to_bv 64 SH; Z_to_bv 64 ns32; Z_to_bv 64 nch32; Z_to_bv 64 ns64].
Definition dsd_facts : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF SB SB 0);
           (27%nat, mkAF 4096 (2 ^ 47) 4); (10%nat, mkAF 4096 (2 ^ 47) 4)] [] [].
Definition dsd_ss : sstate := mkSS 0x418 sr_atoms [dsd_spill] None dsd_facts.

(* The same spill area, with 88 now holding the decode buffer (atom 45) and 24 / 40 about to be written. *)
Definition dsd_spill2 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 120 24 96
    [YP09.mkChunk 0 (CVal 8 (SOff 40 0)); YP09.mkChunk 8 (CVal 8 (SOff 41 0));
     YP09.mkChunk 16 (CVal 8 (SOff 40 0)); YP09.mkChunk 32 (CVal 8 (SOff 32 0));
     YP09.mkChunk 56 (CVal 8 (SOff 42 0)); YP09.mkChunk 64 (CVal 8 (SOff 43 0));
     YP09.mkChunk 72 (CVal 8 (SOff 44 0)); YP09.mkChunk 88 (CVal 8 (SOff 45 0));
     YP09.mkChunk 112 (CVal 8 (SOff 40 0))].
Definition dsd_extra2 (F SH ns32 nch32 ns64 out : Z) : list word :=
  [Z_to_bv 64 SB; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
   Z_to_bv 64 0; Z_to_bv 64 F; Z_to_bv 64 SH; Z_to_bv 64 ns32; Z_to_bv 64 nch32; Z_to_bv 64 ns64;
   Z_to_bv 64 out].
(* The copy (atom 27) is bounded by the allocator's ceiling CEIL_MAX (lib/Reusable/YM05.v:12), not 2 ^ 47: the
   shadow checks of its bytes need copy + 1492 to have its shadow byte in the shadow band Bspan. *)
Definition dsd_facts2 : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF SB SB 0);
           (27%nat, mkAF 4096 CEIL_MAX 4); (45%nat, mkAF 4096 (2 ^ 47) 4)] [] [].
Definition dsd_ss430 : sstate := mkSS 0x430 sr_atoms [dsd_spill2] None dsd_facts2.

(* The callee's frame offset is 16-aligned: the segment's frame is 32-aligned and the caller's stack pointer
   is 16-aligned (lia here does not see mod, by the euclidean-equation setting above). *)
Lemma dsd_mod16_sub : forall a b, a mod 32 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof.
  intros a b Ha Hb. apply Z.mod_divide; [lia|]. apply Z.divide_sub_r.
  - apply Z.mod_divide in Ha; [|lia]. destruct Ha as [k ->]. exists (2 * k). lia.
  - apply Z.mod_divide in Hb; [|lia]. exact Hb.
Qed.

(* ---- carrying the walk's memory facts across a step that did not touch their bytes ---- *)

Lemma dsd_mbyte_keep : forall (H : word -> bool) (m1 m2 : word -> option byte) a,
  aview decodesegsB0 H m2 a = aview decodesegsB0 H m1 a ->
  mbyte decodesegsB0 (mrestrict H m2) a = mbyte decodesegsB0 (mrestrict H m1) a.
Proof.
  intros H m1 m2 a Hv. unfold aview in Hv.
  destruct (mbyte decodesegsB0 (mrestrict H m2) a) as [b2|] eqn:E2;
  destruct (mbyte decodesegsB0 (mrestrict H m1) a) as [b1|] eqn:E1; cbn in Hv; try discriminate; [|reflexivity].
  injection Hv as Hv. f_equal. apply bv_eq. exact Hv.
Qed.

Lemma dsd_rdword_keep : forall (H : word -> bool) (m1 m2 : word -> option byte) a v,
  (forall i, 0 <= i < 8 -> aview decodesegsB0 H m2 (a + i) = aview decodesegsB0 H m1 (a + i)) ->
  rdword (aview decodesegsB0 H m1) a = Some v ->
  rdword (aview decodesegsB0 H m2) a = Some v.
Proof.
  intros H m1 m2 a v HK HR. unfold rdword in *.
  pose proof (HK 0 ltac:(lia)) as K0. rewrite Z.add_0_r in K0.
  rewrite K0, (HK 1 ltac:(lia)), (HK 2 ltac:(lia)), (HK 3 ltac:(lia)),
          (HK 4 ltac:(lia)), (HK 5 ltac:(lia)), (HK 6 ltac:(lia)), (HK 7 ltac:(lia)).
  exact HR.
Qed.

Lemma dsd_valmem_keep : forall (H : word -> bool) (m1 m2 : word -> option byte) a (w : nat) v,
  (forall i, 0 <= i < Z.of_nat w -> aview decodesegsB0 H m2 (a + i) = aview decodesegsB0 H m1 (a + i)) ->
  val_mem decodesegsB0 (mrestrict H m1) a w v ->
  val_mem decodesegsB0 (mrestrict H m2) a w v.
Proof.
  intros H m1 m2 a w v HK HV k Hk.
  rewrite (dsd_mbyte_keep H m1 m2 (a + Z.of_nat k) (HK (Z.of_nat k) ltac:(lia))).
  exact (HV k Hk).
Qed.

Lemma dsd_garr8_keep : forall (H : word -> bool) (m1 m2 : word -> option byte) a (l : list Z),
  (forall i, 0 <= i < Z.of_nat (length l) -> aview decodesegsB0 H m2 (a + i) = aview decodesegsB0 H m1 (a + i)) ->
  garr8 decodesegsB0 (mrestrict H m1) a l ->
  garr8 decodesegsB0 (mrestrict H m2) a l.
Proof.
  intros H m1 m2 a l HK HG j Hj. destruct (HG j Hj) as [HV HR]. split; [|exact HR].
  apply (dsd_valmem_keep H m1 m2 (a + Z.of_nat j) 1 (nth j l 0)); [|exact HV].
  intros i Hi. replace (a + Z.of_nat j + i) with (a + (Z.of_nat j + i)) by lia. apply HK. lia.
Qed.

(* An eight-byte field of the view, from the region's val_mem (lib/B/Prog/LLVMFuzzerTestOneInput_segA.v's
   dec_rdword_of_val_mem, copied: that file is a segment, not a library). *)
Lemma dsd_rdword_of_val_mem : forall segs H mem a v,
  val_mem segs (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview segs H mem) a = Some v.
Proof.
intros segs H mem a v Hv Hr.
assert (BY : forall k, (k < 8)%nat -> aview segs H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (BY 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (BY 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (BY 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (BY 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (BY 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (BY 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (BY 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (BY 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.

(* The value of register r in the machine state of a symbolic state HS (lib/B/Prog/LLVMFuzzerTestOneInput_segA.v:368;
   the st_ok_pi case as lib/B/Prog/LLVMFuzzerTestOneInput_segC.v's cp_reg). *)
Ltac reg_at HS r v H tac :=
  lazymatch type of HS with
  | st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
    let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
    assert (H : YK11.getr (ms_regs msx) r = v) by
      (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | st_ok_pi ?segsx ?valx ?Ex ?ssx (restrict ?Hh ?msx) =>
    let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
    assert (H : YK11.getr (ms_regs msx) r = v) by
      (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.

(* ------------------------------------------------------------------ *)
(* 2. The entry state of the segment, from llvm_b_st_418's facts        *)
(* ------------------------------------------------------------------ *)

Section insp. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation PIB := (@PI_decodeb rc).
#[local] Notation SEGS := (@pa_segs rc decodeb_listing PIB).
#[local] Notation VAL := (@pa_val rc decodeb_listing PIB).
#[local] Notation BASE := (@pa_val rc decodeb_listing PIB A_TEXT).
Variable B : asyms.
Hypothesis LAWS : AR_laws decodesegsB0 B.

Definition DEND (regs : bvmap 5 word) (F SH ns32 nch32 ns64 : Z) : env :=
  Eimg (PI := PIB) (Ereg regs (dsd_extra F SH ns32 nch32 ns64)).

(* The spill area and the two heap pointers, as the Pa engine reads them. *)
Lemma dsd_entry_st : forall (W : world decodesegsB0) regs mem sp1 out res F SH ns32 nch32 ns64,
  YK11.getr regs 9 = w64 sp1 -> 2 ^ 46 <= sp1 -> sp1 + 120 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  YK11.getr regs 10 = w64 out -> 4096 <= out -> out < 2 ^ 47 -> out mod 16 = 0 ->
  YK11.getr regs 27 = w64 res -> 4096 <= res -> res < 2 ^ 47 -> res mod 16 = 0 ->
  0 <= F < 2 ^ 64 -> 0 <= SH < 2 ^ 64 -> 0 <= ns32 < 2 ^ 64 -> 0 <= nch32 < 2 ^ 64 -> 0 <= ns64 < 2 ^ 64 ->
  rdword (aview decodesegsB0 (w_H W) mem) (sp1 + 0) = Some F ->
  rdword (aview decodesegsB0 (w_H W) mem) (sp1 + 8) = Some SH ->
  rdword (aview decodesegsB0 (w_H W) mem) (sp1 + 16) = Some F ->
  rdword (aview decodesegsB0 (w_H W) mem) (sp1 + 32) = Some SHADOW_OFF ->
  rdword (aview decodesegsB0 (w_H W) mem) (sp1 + 56) = Some ns32 ->
  rdword (aview decodesegsB0 (w_H W) mem) (sp1 + 64) = Some nch32 ->
  rdword (aview decodesegsB0 (w_H W) mem) (sp1 + 72) = Some ns64 ->
  rdword (aview decodesegsB0 (w_H W) mem) (sp1 + 112) = Some F ->
  (forall o, 24 <= o < 96 -> apresent (w_H W) mem (sp1 + o)) ->
  st_ok_pi SEGS VAL (DEND regs F SH ns32 nch32 ns64) dsd_ss
    (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 (BASE + 0x418)) mem (YK11.seg_rom SEGS))).
Proof.
intros W regs mem sp1 out res F SH ns32 nch32 ns64 H9 Hsp1a Hsp1b Hsp1m H10 Ho1 Ho2 Ho3 H27 Hr1 Hr2 Hr3
  HF HSH Hns32 Hnch32 Hns64 R0 R8 R16 R32 R56 R64 R72 R112 HP.
rewrite restrict_mkst_fx.
set (E := DEND regs F SH ns32 nch32 ns64).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (dsd_extra F SH ns32 nch32 ns64)) k)
  by (intros k Hk; unfold E, DEND; apply Eimg_low; exact Hk).
assert (EREG : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = YK11.getr regs r).
{ intros kk r Hk. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
  rewrite EL by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ kk r Hk). }
assert (EX : forall (j : nat) v, (j < 13)%nat ->
    nth j (dsd_extra F SH ns32 nch32 ns64) (Z_to_bv 64 0) = Z_to_bv 64 v -> ew E (32 + j) = Z_to_bv 64 v)
  by (intros j v Hj Hnth; rewrite EL by (unfold A_TEXT; lia); rewrite ew_Ereg_extra; exact Hnth).
assert (E9 : bv_unsigned (ew E 9) = sp1)
  by (rewrite (EREG 9%nat 9%bv eq_refl), H9; unfold w64; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
      change (2 ^ Z.of_N 64) with (2 ^ 64); apply Z.mod_small; lia).
assert (E10 : bv_unsigned (ew E 10) = out)
  by (rewrite (EREG 10%nat 10%bv eq_refl), H10; unfold w64; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
      change (2 ^ Z.of_N 64) with (2 ^ 64); apply Z.mod_small; lia).
assert (E27 : bv_unsigned (ew E 27) = res)
  by (rewrite (EREG 27%nat 27%bv eq_refl), H27; unfold w64; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
      change (2 ^ Z.of_N 64) with (2 ^ 64); apply Z.mod_small; lia).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by exact (EX 0%nat SB ltac:(lia) eq_refl).
assert (E40 : ew E 40 = Z_to_bv 64 F) by exact (EX 8%nat F ltac:(lia) eq_refl).
assert (E41 : ew E 41 = Z_to_bv 64 SH) by exact (EX 9%nat SH ltac:(lia) eq_refl).
assert (E42 : ew E 42 = Z_to_bv 64 ns32) by exact (EX 10%nat ns32 ltac:(lia) eq_refl).
assert (E43 : ew E 43 = Z_to_bv 64 nch32) by exact (EX 11%nat nch32 ltac:(lia) eq_refl).
assert (E44 : ew E 44 = Z_to_bv 64 ns64) by exact (EX 12%nat ns64 ltac:(lia) eq_refl).
assert (USB : bv_unsigned (ew E 32) = SB)
  by (rewrite E32, Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
      change (2 ^ Z.of_N 64) with (2 ^ 64); apply Z.mod_small; unfold SB; lia).
unfold dsd_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  unfold dsd_spill, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9. split; [lia|]. split; [lia|].
  split; [intros o Ho; apply (apresent_writable decodesegsB0); apply HP; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  + apply (chunk_ok_val decodesegsB0 E _ sp1 0 8 (SOff 40 0) F);
      [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact (val_mem_of_rdword decodesegsB0 _ _ _ _ R0).
  + apply (chunk_ok_val decodesegsB0 E _ sp1 8 8 (SOff 41 0) SH);
      [cbn [sv_denot]; rewrite E41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact (val_mem_of_rdword decodesegsB0 _ _ _ _ R8).
  + apply (chunk_ok_val decodesegsB0 E _ sp1 16 8 (SOff 40 0) F);
      [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact (val_mem_of_rdword decodesegsB0 _ _ _ _ R16).
  + apply (chunk_ok_val decodesegsB0 E _ sp1 32 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; zside | zside |].
    exact (val_mem_of_rdword decodesegsB0 _ _ _ _ R32).
  + apply (chunk_ok_val decodesegsB0 E _ sp1 56 8 (SOff 42 0) ns32);
      [cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact (val_mem_of_rdword decodesegsB0 _ _ _ _ R56).
  + apply (chunk_ok_val decodesegsB0 E _ sp1 64 8 (SOff 43 0) nch32);
      [cbn [sv_denot]; rewrite E43, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact (val_mem_of_rdword decodesegsB0 _ _ _ _ R64).
  + apply (chunk_ok_val decodesegsB0 E _ sp1 72 8 (SOff 44 0) ns64);
      [cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact (val_mem_of_rdword decodesegsB0 _ _ _ _ R72).
  + apply (chunk_ok_val decodesegsB0 E _ sp1 112 8 (SOff 40 0) F);
      [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact (val_mem_of_rdword decodesegsB0 _ _ _ _ R112).
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- split; [|split; [exact I | exact I]].
  cbn [dsd_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E9, E10, E27, USB.
  change (2 ^ 5) with 32. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold SB; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. +0x418 .. +0x42c: the spill, the NULL test and reac_frame_inspect *)
(* ------------------------------------------------------------------ *)

(* What the walk knows at +0x430, the return of reac_frame_inspect: the caller's journal at the new memory,
   the registers the rest of the segment reads, the spill slots (88 now holding the buffer), the memory
   facts of llvm_b_st_418 that the call kept, and, against the memory memS of +0x418, every byte outside the
   callee's stack window and the spill area kept and every present byte still present (what the segment's post
   re-reads its other facts through). *)
Definition dsd_at430 (W : world decodesegsB0) (regsT : bvmap 5 word)
    (STK sp0 : Z) (FP : list (Z * Z)) ly S (W0 : world decodesegsB0) mem0 md0 own lyc Sc (k : Z)
    (memS : word -> option byte) (sp1 F SH res out len mode nch ns olen prod fits0 : Z) (bs : list byte)
    : world decodesegsB0 -> config -> Prop :=
  fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
    c2 = mkCfg (YK11.mkst regs2 (w64 (decodeb_text + 0x430)) mem2 (YK11.seg_rom decodesegsB0)) md2 /\
    @ajournal rc dec_B_sink_head decodesegsB0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
    YK11.getr regs2 3 = w64 (as_gp B) /\ YK11.getr regs2 4 = w64 (as_tp B) /\
    YK11.getr regs2 8 = w64 sp0 /\ YK11.getr regs2 9 = w64 sp1 /\ spZ regs2 = sp1 /\
    YK11.getr regs2 10 = w64 (CInsp.inspect_result len bs) /\
    YK11.getr regs2 18 = w64 SHADOW_OFF /\ YK11.getr regs2 20 = w64 len /\
    YK11.getr regs2 21 = w64 mode /\ YK11.getr regs2 22 = w64 prod /\
    YK11.getr regs2 23 = w64 nch /\ YK11.getr regs2 24 = w64 fits0 /\
    YK11.getr regs2 26 = w64 olen /\ YK11.getr regs2 27 = w64 res /\
    rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 0) = Some F /\
    rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 8) = Some SH /\
    rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 16) = Some F /\
    rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 32) = Some SHADOW_OFF /\
    rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 56) = Some (ns mod 2 ^ 32) /\
    rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 64) = Some (nch mod 2 ^ 32) /\
    rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 72) = Some (ns mod 2 ^ 64) /\
    rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 88) = Some out /\
    rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 112) = Some F /\
    (forall i, 0 <= i < 4 -> aview decodesegsB0 (w_H W) mem2 (SH + i) = Some DEC_SH_LEFT) /\
    aview decodesegsB0 (w_H W) mem2 (SH + 4) = Some 0 /\
    aview decodesegsB0 (w_H W) mem2 (SH + 5) = Some 4 /\
    (forall i, 6 <= i < 8 -> aview decodesegsB0 (w_H W) mem2 (SH + i) = Some DEC_SH_RIGHT) /\
    garr8 decodesegsB0 (mrestrict (w_H W) mem2) res (map (fun b : byte => bv_unsigned b) bs) /\
    val_mem decodesegsB0 (mrestrict (w_H W) mem2) (mode + 4) 4%nat (nch mod 2 ^ 32) /\
    val_mem decodesegsB0 (mrestrict (w_H W) mem2) (mode + 8) 4%nat (ns mod 2 ^ 32) /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - ESTACK <= a < sp1 + 120) ->
       aview decodesegsB0 (w_H W) mem2 a = aview decodesegsB0 (w_H W) memS a) /\
    (forall a, apresent (w_H W) memS a -> apresent (w_H W) mem2 a).

(* The join of the paths, at +0x5a0: the facts of +0x430 but a0 and s2 (the counter path overwrites both, and
   neither is read again before it is set: +0x5a0 sets s2, +0x5ac a0), the two slots +0x434 / +0x438 wrote (24 the
   length, 40 the copy), and s3 holding the frame's well-formedness flag. *)
Definition dsd_at5a0 (W : world decodesegsB0) (regsT : bvmap 5 word)
    (STK sp0 : Z) (FP : list (Z * Z)) ly S (W0 : world decodesegsB0) mem0 md0 own lyc Sc (k : Z)
    (memS : word -> option byte) (sp1 F SH res out len mode nch ns olen prod fits0 : Z) (bs : list byte)
    : world decodesegsB0 -> config -> Prop :=
  fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
    c2 = mkCfg (YK11.mkst regs2 (w64 (decodeb_text + 0x5a0)) mem2 (YK11.seg_rom decodesegsB0)) md2 /\
    @ajournal rc dec_B_sink_head decodesegsB0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
    YK11.getr regs2 3 = w64 (as_gp B) /\ YK11.getr regs2 4 = w64 (as_tp B) /\
    YK11.getr regs2 8 = w64 sp0 /\ YK11.getr regs2 9 = w64 sp1 /\ spZ regs2 = sp1 /\
    YK11.getr regs2 19 = w64 (if CInsp.inspect_wf len bs then 1 else 0) /\
    YK11.getr regs2 20 = w64 len /\
    YK11.getr regs2 21 = w64 mode /\ YK11.getr regs2 22 = w64 prod /\
    YK11.getr regs2 23 = w64 nch /\ YK11.getr regs2 24 = w64 fits0 /\
    YK11.getr regs2 26 = w64 olen /\ YK11.getr regs2 27 = w64 res /\
    rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 0) = Some F /\
    rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 8) = Some SH /\
    rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 16) = Some F /\
    rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 24) = Some len /\
    rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 32) = Some SHADOW_OFF /\
    rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 40) = Some res /\
    rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 56) = Some (ns mod 2 ^ 32) /\
    rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 64) = Some (nch mod 2 ^ 32) /\
    rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 72) = Some (ns mod 2 ^ 64) /\
    rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 88) = Some out /\
    rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 112) = Some F /\
    (forall i, 0 <= i < 4 -> aview decodesegsB0 (w_H W) mem2 (SH + i) = Some DEC_SH_LEFT) /\
    aview decodesegsB0 (w_H W) mem2 (SH + 4) = Some 0 /\
    aview decodesegsB0 (w_H W) mem2 (SH + 5) = Some 4 /\
    (forall i, 6 <= i < 8 -> aview decodesegsB0 (w_H W) mem2 (SH + i) = Some DEC_SH_RIGHT) /\
    garr8 decodesegsB0 (mrestrict (w_H W) mem2) res (map (fun b : byte => bv_unsigned b) bs) /\
    val_mem decodesegsB0 (mrestrict (w_H W) mem2) (mode + 4) 4%nat (nch mod 2 ^ 32) /\
    val_mem decodesegsB0 (mrestrict (w_H W) mem2) (mode + 8) 4%nat (ns mod 2 ^ 32) /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - ESTACK <= a < sp1 + 120) ->
       aview decodesegsB0 (w_H W) mem2 a = aview decodesegsB0 (w_H W) memS a) /\
    (forall a, apresent (w_H W) memS a -> apresent (w_H W) mem2 a).

(* +0x418 .. +0x42c, with the call of reac_frame_inspect: the buffer is spilled to 88(s1), the NULL test of
   +0x41c decides itself (the engine's 16-aligned, 4096 <= out fact), and the leaf bridge takes the call. *)
Lemma dsd_stage1 :
  dec_crt_cells B ->
  (forall fx' : YK11.FPState, @dec_leaf_at rc B (@LInspect.dec_reac_frame_inspect_cg) fx') ->
  forall (W : world decodesegsB0) regs mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc k
         (sp1 F SH res out len mode nch ns olen prod fits0 : Z) (bs : list byte),
  @ajournal rc dec_B_sink_head decodesegsB0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
  spZ regs = sp1 -> sp0 - 240 <= sp1 -> sp1 <= sp0 - 224 -> sp1 mod 32 = 0 -> 4336 <= STK ->
  YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
  YK11.getr regs 8 = w64 sp0 -> YK11.getr regs 9 = w64 sp1 ->
  YK11.getr regs 10 = w64 out -> YK11.getr regs 18 = w64 SHADOW_OFF -> YK11.getr regs 20 = w64 len ->
  YK11.getr regs 21 = w64 mode -> YK11.getr regs 22 = w64 prod -> YK11.getr regs 23 = w64 nch ->
  YK11.getr regs 24 = w64 fits0 -> YK11.getr regs 26 = w64 olen -> YK11.getr regs 27 = w64 res ->
  In (res, len) (ablocks B lyc Sc) -> In (out, olen) (ablocks B lyc Sc) ->
  0 <= len < 2 ^ 64 -> length bs = Z.to_nat len ->
  garr8 decodesegsB0 (mrestrict (w_H W) mem) res (map (fun b : byte => bv_unsigned b) bs) ->
  0 <= F < 2 ^ 64 -> 0 <= SH < 2 ^ 64 ->
  rdword (aview decodesegsB0 (w_H W) mem) (sp1 + 0) = Some F ->
  rdword (aview decodesegsB0 (w_H W) mem) (sp1 + 8) = Some SH ->
  rdword (aview decodesegsB0 (w_H W) mem) (sp1 + 16) = Some F ->
  rdword (aview decodesegsB0 (w_H W) mem) (sp1 + 32) = Some SHADOW_OFF ->
  rdword (aview decodesegsB0 (w_H W) mem) (sp1 + 56) = Some (ns mod 2 ^ 32) ->
  rdword (aview decodesegsB0 (w_H W) mem) (sp1 + 64) = Some (nch mod 2 ^ 32) ->
  rdword (aview decodesegsB0 (w_H W) mem) (sp1 + 72) = Some (ns mod 2 ^ 64) ->
  rdword (aview decodesegsB0 (w_H W) mem) (sp1 + 112) = Some F ->
  (forall i, 0 <= i < 4 -> aview decodesegsB0 (w_H W) mem (SH + i) = Some DEC_SH_LEFT) ->
  aview decodesegsB0 (w_H W) mem (SH + 4) = Some 0 ->
  aview decodesegsB0 (w_H W) mem (SH + 5) = Some 4 ->
  (forall i, 6 <= i < 8 -> aview decodesegsB0 (w_H W) mem (SH + i) = Some DEC_SH_RIGHT) ->
  val_mem decodesegsB0 (mrestrict (w_H W) mem) (mode + 4) 4%nat (nch mod 2 ^ 32) ->
  val_mem decodesegsB0 (mrestrict (w_H W) mem) (mode + 8) 4%nat (ns mod 2 ^ 32) ->
  SH + 8 <= alloc_ceiling -> 4096 <= SH -> 4096 <= F -> F + 64 <= alloc_ceiling ->
  4096 <= mode -> mode + 12 <= alloc_ceiling ->
  SRr decodesegsB0 W
    (mkCfg (YK11.mkst regs (Z_to_bv 64 (decodeb_text + 0x418)) mem (YK11.seg_rom decodesegsB0)) md)
    (dsd_at430 W regs STK sp0 FP ly S W0 mem0 md0 own lyc Sc k mem
       sp1 F SH res out len mode nch ns olen prod fits0 bs).
Proof.
intros HC HLEAF W regs mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc k
  sp1 F SH res out len mode nch ns olen prod fits0 bs
  HJ Hsp Hsp1a Hsp1b Hsp1m HSTK Hgp Htp H8 H9 H10 H18 H20 H21 H22 H23 H24 H26 H27
  Hinr Hino Hlen Hbs HG HFrng HSHrng R0 R8 R16 R32 R56 R64 R72 R112 Fsh0 Fsh4 Fsh5 Fsh6 Hmv1 Hmv2
  HSHhi HSHlo HFlo HFhi Hmlo Hmhi.
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof alloc_ceiling_val as HCEIL.
destruct (al_blocks _ _ LAWS _ _ _ _ _ res len HAR Hinr) as (Hral & Hr4096 & Hrceil & _ & Hrpres & _ & Hrmr).
destruct (al_blocks _ _ LAWS _ _ _ _ _ out olen HAR Hino) as (Hoal & Ho4096 & Hoceil & _ & Hopres & _ & Homr).
pose proof (req_size_pos len ltac:(lia)) as [Hqr1 Hqr2].
pose proof (req_size_pos olen ltac:(lia)) as [Hqo1 Hqo2].
(* the entry state *)
pose proof (dsd_entry_st W regs mem sp1 out res F SH (ns mod 2 ^ 32) (nch mod 2 ^ 32) (ns mod 2 ^ 64)
  H9 ltac:(lia) ltac:(lia) Hsp1m H10 ltac:(lia) ltac:(lia) Hoal H27 ltac:(lia) ltac:(lia) Hral
  ltac:(lia) ltac:(lia) ltac:(pose proof (Z.mod_pos_bound ns (2 ^ 32) ltac:(lia)); lia)
  ltac:(pose proof (Z.mod_pos_bound nch (2 ^ 32) ltac:(lia)); lia)
  ltac:(pose proof (Z.mod_pos_bound ns (2 ^ 64) ltac:(lia)); lia)
  R0 R8 R16 R32 R56 R64 R72 R112 ltac:(intros o Ho; apply Hpres; lia)) as HS.
set (E := DEND regs F SH (ns mod 2 ^ 32) (nch mod 2 ^ 32) (ns mod 2 ^ 64)) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, DEND; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H W) mem)) by constructor.
assert (EREG : forall kk (r : bv 5), Z.of_nat kk = bv_unsigned r -> ew E kk = YK11.getr regs r).
{ intros kk r Hk. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
  unfold E, DEND. rewrite (Eimg_low (PI := PIB) _ kk ltac:(unfold A_TEXT; lia)).
  exact (ew_Ereg_nat regs _ kk r Hk). }
assert (E9 : bv_unsigned (ew E 9) = sp1)
  by (rewrite (EREG 9%nat 9%bv eq_refl), H9; unfold w64; rewrite Z_to_bv_unsigned;
      unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); apply Z.mod_small; lia).
change (Z_to_bv 64 (decodeb_text + 0x418)) with (Z_to_bv 64 (BASE + 0x418)).
pose proof (paj_run (SK := dec_B_sink_head) (PI := PIB) B LAWS) as RUN.
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
  let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (sp1 - sp0));
  [reflexivity | rewrite E9; lia | cbn; lia | cbn; lia | apply awr_ok_nil]. }
(* at the call: the registers reac_frame_inspect reads, and the spill slot the segment wrote *)
assert (AG : forall n, (n < 512)%nat -> ew E n = ew E n) by reflexivity.
lazymatch goal with HS : st_ok _ ?Ex _ (restrict _ ?msx) |- _ =>
  assert (EA : forall n, (n < 512)%nat -> ew Ex n = ew E n)
    by (intros nn Hnn; repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; reflexivity)
end.
lazymatch goal with HS : st_ok _ ?Ex ?ssx (restrict _ ?msx) |- _ =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  assert (HR0 : region_ok SEGS Ex (ms_mem (restrict (w_H W) msx)) r0)
    by (apply (st_ok_region_nth Ex ssx (restrict (w_H W) msx) 0 r0 HS); vm_compute; reflexivity)
end.
cbn [ms_mem restrict] in HR0.
lazymatch goal with HS : st_ok _ ?Ex _ _ |- _ =>
  assert (E9' : bv_unsigned (ew Ex 9) = sp1) by (rewrite ?(EA 9%nat ltac:(lia)); exact E9) end.
reg_at HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 0x430)) RA1 ltac:(apply codeptr_val; exact HEI).
reg_at HS (2%bv : bv 5) (w64 sp1) RSP
  ltac:(cbn [sv_denot]; rewrite ?(EA 2%nat ltac:(lia)), (EREG 2%nat 2%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; unfold w64; unfold spZ in Hsp; rewrite <- Hsp; symmetry;
        apply Z_to_bv_bv_unsigned).
reg_at HS (3%bv : bv 5) (w64 (as_gp B)) RGP
  ltac:(cbn [sv_denot]; rewrite ?(EA 3%nat ltac:(lia)), (EREG 3%nat 3%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact Hgp).
reg_at HS (4%bv : bv 5) (w64 (as_tp B)) RTP
  ltac:(cbn [sv_denot]; rewrite ?(EA 4%nat ltac:(lia)), (EREG 4%nat 4%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact Htp).
reg_at HS (10%bv : bv 5) (w64 res) RA0
  ltac:(cbn [sv_denot]; rewrite ?(EA 27%nat ltac:(lia)), (EREG 27%nat 27%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact H27).
reg_at HS (11%bv : bv 5) (w64 len) RA1L
  ltac:(cbn [sv_denot]; rewrite ?(EA 20%nat ltac:(lia)), (EREG 20%nat 20%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact H20).
(* The bytes the run did not write: everything outside the spill window [sp1 + 24, sp1 + 96). *)
lazymatch goal with HFr2 : frame_of ?Ex ?rsx (mrestrict _ ?m0) (mrestrict _ ?m1) |- _ =>
  assert (KEEPRUN : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 24 <= a < sp1 + 96) ->
      aview decodesegsB0 (w_H W) m1 a = aview decodesegsB0 (w_H W) m0 a);
  [ intros a Ha Hn;
    refine (kept_of_frame Ex rsx (w_H W) m0 m1 (fun x => sp1 + 24 <= x < sp1 + 96) HFr2 _ a Ha Hn);
    intros bb wlo whi x Hin Hr;
    let wsv := eval vm_compute in (windows rsx) in change (In (bb, wlo, whi) wsv) in Hin;
    cbn [In] in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr|]); try contradiction;
    rewrite E9' in Hr; lia
  | ] end.
(* The spill slots at the call, read off the symbolic region (the run wrote 88 only). *)
assert (E32E : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (unfold E, DEND; rewrite Eimg_low by (unfold A_TEXT; lia);
  exact (ew_Ereg_extra regs _ 0)).
assert (E40E : ew E 40 = Z_to_bv 64 F) by (unfold E, DEND; rewrite Eimg_low by (unfold A_TEXT; lia);
  exact (ew_Ereg_extra regs _ 8)).
assert (E41E : ew E 41 = Z_to_bv 64 SH) by (unfold E, DEND; rewrite Eimg_low by (unfold A_TEXT; lia);
  exact (ew_Ereg_extra regs _ 9)).
assert (E42E : ew E 42 = Z_to_bv 64 (ns mod 2 ^ 32)) by (unfold E, DEND; rewrite Eimg_low by (unfold A_TEXT; lia);
  exact (ew_Ereg_extra regs _ 10)).
assert (E43E : ew E 43 = Z_to_bv 64 (nch mod 2 ^ 32)) by (unfold E, DEND; rewrite Eimg_low by (unfold A_TEXT; lia);
  exact (ew_Ereg_extra regs _ 11)).
assert (E44E : ew E 44 = Z_to_bv 64 (ns mod 2 ^ 64)) by (unfold E, DEND; rewrite Eimg_low by (unfold A_TEXT; lia);
  exact (ew_Ereg_extra regs _ 12)).
pose proof (Z.mod_pos_bound ns (2 ^ 32) ltac:(lia)) as Mns32.
pose proof (Z.mod_pos_bound nch (2 ^ 32) ltac:(lia)) as Mnch32.
pose proof (Z.mod_pos_bound ns (2 ^ 64) ltac:(lia)) as Mns64.
lazymatch goal with HS : st_ok _ ?Ex _ (restrict _ ?msx) |- _ =>
  assert (SL0 : rdword (aview decodesegsB0 (w_H W) (ms_mem msx)) (sp1 + 0) = Some F) by
    (apply dsd_rdword_of_val_mem; [|lia];
     refine (field_of_region Ex _ 9%nat sp1 _ _ _ _ _ 0 8%N (SOff 40 0) F HR0 E9'
       ltac:(cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]))
       ltac:(cbn [sv_denot]; rewrite ?(EA 40%nat ltac:(lia)), E40E, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
       ltac:(cbn; lia) ltac:(cbn; lia)));
  assert (SL8 : rdword (aview decodesegsB0 (w_H W) (ms_mem msx)) (sp1 + 8) = Some SH) by
    (apply dsd_rdword_of_val_mem; [|lia];
     refine (field_of_region Ex _ 9%nat sp1 _ _ _ _ _ 8 8%N (SOff 41 0) SH HR0 E9'
       ltac:(cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]))
       ltac:(cbn [sv_denot]; rewrite ?(EA 41%nat ltac:(lia)), E41E, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
       ltac:(cbn; lia) ltac:(cbn; lia)));
  assert (SL16 : rdword (aview decodesegsB0 (w_H W) (ms_mem msx)) (sp1 + 16) = Some F) by
    (apply dsd_rdword_of_val_mem; [|lia];
     refine (field_of_region Ex _ 9%nat sp1 _ _ _ _ _ 16 8%N (SOff 40 0) F HR0 E9'
       ltac:(cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]))
       ltac:(cbn [sv_denot]; rewrite ?(EA 40%nat ltac:(lia)), E40E, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
       ltac:(cbn; lia) ltac:(cbn; lia)));
  assert (SL32 : rdword (aview decodesegsB0 (w_H W) (ms_mem msx)) (sp1 + 32) = Some SHADOW_OFF) by
    (apply dsd_rdword_of_val_mem; [|unfold SHADOW_OFF; lia];
     refine (field_of_region Ex _ 9%nat sp1 _ _ _ _ _ 32 8%N (SOff 32 0) SHADOW_OFF HR0 E9'
       ltac:(cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]))
       ltac:(cbn [sv_denot]; rewrite ?(EA 32%nat ltac:(lia)), E32E, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
       ltac:(unfold SHADOW_OFF; cbn; lia) ltac:(cbn; lia)));
  assert (SL56 : rdword (aview decodesegsB0 (w_H W) (ms_mem msx)) (sp1 + 56) = Some (ns mod 2 ^ 32)) by
    (apply dsd_rdword_of_val_mem; [|lia];
     refine (field_of_region Ex _ 9%nat sp1 _ _ _ _ _ 56 8%N (SOff 42 0) (ns mod 2 ^ 32) HR0 E9'
       ltac:(cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]))
       ltac:(cbn [sv_denot]; rewrite ?(EA 42%nat ltac:(lia)), E42E, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
       ltac:(cbn; lia) ltac:(cbn; lia)));
  assert (SL64 : rdword (aview decodesegsB0 (w_H W) (ms_mem msx)) (sp1 + 64) = Some (nch mod 2 ^ 32)) by
    (apply dsd_rdword_of_val_mem; [|lia];
     refine (field_of_region Ex _ 9%nat sp1 _ _ _ _ _ 64 8%N (SOff 43 0) (nch mod 2 ^ 32) HR0 E9'
       ltac:(cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]))
       ltac:(cbn [sv_denot]; rewrite ?(EA 43%nat ltac:(lia)), E43E, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
       ltac:(cbn; lia) ltac:(cbn; lia)));
  assert (SL72 : rdword (aview decodesegsB0 (w_H W) (ms_mem msx)) (sp1 + 72) = Some (ns mod 2 ^ 64)) by
    (apply dsd_rdword_of_val_mem; [|lia];
     refine (field_of_region Ex _ 9%nat sp1 _ _ _ _ _ 72 8%N (SOff 44 0) (ns mod 2 ^ 64) HR0 E9'
       ltac:(cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]))
       ltac:(cbn [sv_denot]; rewrite ?(EA 44%nat ltac:(lia)), E44E, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
       ltac:(cbn; lia) ltac:(cbn; lia)));
  assert (SL88 : rdword (aview decodesegsB0 (w_H W) (ms_mem msx)) (sp1 + 88) = Some out) by
    (apply dsd_rdword_of_val_mem; [|lia];
     refine (field_of_region Ex _ 9%nat sp1 _ _ _ _ _ 88 8%N (SOff 10 0) out HR0 E9'
       ltac:(cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]))
       ltac:(cbn [sv_denot]; rewrite ?(EA 10%nat ltac:(lia)), (EREG 10%nat 10%bv eq_refl), H10, Z.add_0_r;
             unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity)
       ltac:(cbn; lia) ltac:(cbn; lia)));
  assert (SL112 : rdword (aview decodesegsB0 (w_H W) (ms_mem msx)) (sp1 + 112) = Some F) by
    (apply dsd_rdword_of_val_mem; [|lia];
     refine (field_of_region Ex _ 9%nat sp1 _ _ _ _ _ 112 8%N (SOff 40 0) F HR0 E9'
       ltac:(cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]))
       ltac:(cbn [sv_denot]; rewrite ?(EA 40%nat ltac:(lia)), E40E, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
       ltac:(cbn; lia) ltac:(cbn; lia)))
end.
reg_at HS (8%bv : bv 5) (w64 sp0) RS0
  ltac:(cbn [sv_denot]; rewrite ?(EA 8%nat ltac:(lia)), (EREG 8%nat 8%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact H8).
reg_at HS (9%bv : bv 5) (w64 sp1) RS1
  ltac:(cbn [sv_denot]; rewrite ?(EA 9%nat ltac:(lia)), (EREG 9%nat 9%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact H9).
reg_at HS (18%bv : bv 5) (w64 SHADOW_OFF) RS2
  ltac:(cbn [sv_denot]; rewrite ?(EA 18%nat ltac:(lia)), (EREG 18%nat 18%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact H18).
reg_at HS (20%bv : bv 5) (w64 len) RS4
  ltac:(cbn [sv_denot]; rewrite ?(EA 20%nat ltac:(lia)), (EREG 20%nat 20%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact H20).
reg_at HS (21%bv : bv 5) (w64 mode) RS5
  ltac:(cbn [sv_denot]; rewrite ?(EA 21%nat ltac:(lia)), (EREG 21%nat 21%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact H21).
reg_at HS (22%bv : bv 5) (w64 prod) RS6
  ltac:(cbn [sv_denot]; rewrite ?(EA 22%nat ltac:(lia)), (EREG 22%nat 22%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact H22).
reg_at HS (23%bv : bv 5) (w64 nch) RS7
  ltac:(cbn [sv_denot]; rewrite ?(EA 23%nat ltac:(lia)), (EREG 23%nat 23%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact H23).
reg_at HS (24%bv : bv 5) (w64 fits0) RS8
  ltac:(cbn [sv_denot]; rewrite ?(EA 24%nat ltac:(lia)), (EREG 24%nat 24%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact H24).
reg_at HS (26%bv : bv 5) (w64 olen) RS10
  ltac:(cbn [sv_denot]; rewrite ?(EA 26%nat ltac:(lia)), (EREG 26%nat 26%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact H26).
reg_at HS (27%bv : bv 5) (w64 res) RS11
  ltac:(cbn [sv_denot]; rewrite ?(EA 27%nat ltac:(lia)), (EREG 27%nat 27%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact H27).
assert (HspT : spZ (ms_regs ms) = sp1)
  by (unfold spZ; rewrite RSP; unfold w64; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
      change (2 ^ Z.of_N 64) with (2 ^ 64); apply Z.mod_small; lia).
pmkst HS.
eapply SRr_mono.
- eapply (dec_leafb_inspect B LAWS HC HLEAF W (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 own
            lyc Sc _ k (sp1 - sp0) res len bs HJ);
  [ rewrite HspT; lia | exact (dsd_mod16_sub sp1 sp0 Hsp1m Hsp0al) | lia | unfold ESTACK; lia
  | rewrite RA1; apply (ret_ok_codeptr_v (PI := PIB)); [lia | reflexivity]
  | exact RGP | exact RTP | exact RA0 | exact RA1L | lia | ].
  intros Hl. split; [exact Hinr|]. split; [rewrite Hbs, Hl; reflexivity|].
  apply (dsd_garr8_keep (w_H W) mem (ms_mem ms) res _); [|exact HG].
  intros i Hi. rewrite length_map, Hbs, Hl in Hi. apply KEEPRUN; lia.
- cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & Hc2 & HJ2 & Hpres2 & Hres2 & Heff2 & Hgr2 & _).
  assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 4096 <= a < sp1) ->
      aview decodesegsB0 (w_H W) mem2 a = aview decodesegsB0 (w_H W) (ms_mem ms) a)
    by (intros a Ha Hn; apply Heff2; [lia | rewrite HspT; unfold ESTACK; lia | intros HW; inversion HW]).
  assert (KEEPLOW : forall a, 0 <= a < alloc_ceiling ->
      aview decodesegsB0 (w_H W) mem2 a = aview decodesegsB0 (w_H W) mem a)
    by (intros a Ha; rewrite (KEEP2 a ltac:(lia) ltac:(lia)); apply KEEPRUN; lia).
  assert (KSLOT : forall off v, 0 <= off -> off + 8 <= 120 ->
      rdword (aview decodesegsB0 (w_H W) (ms_mem ms)) (sp1 + off) = Some v ->
      rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + off) = Some v)
    by (intros off v Hl1 Hl2 HR; apply (dsd_rdword_keep (w_H W) (ms_mem ms) mem2 _ v);
        [intros i Hi; apply KEEP2; lia | exact HR]).
  split; [reflexivity|]. exists regs2, mem2, md2.
  rewrite RA1 in Hc2.
  split; [exact Hc2|]. split; [exact HJ2|].
  split; [exact (eq_trans (Hpres2 3 ltac:(unfold acallee_saved; lia)) RGP)|].
  split; [exact (eq_trans (Hpres2 4 ltac:(unfold acallee_saved; lia)) RTP)|].
  split; [exact (eq_trans (Hpres2 8 ltac:(unfold acallee_saved; lia)) RS0)|].
  split; [exact (eq_trans (Hpres2 9 ltac:(unfold acallee_saved; lia)) RS1)|].
  assert (RSP2 : YK11.getr regs2 2 = w64 sp1)
    by exact (eq_trans (Hpres2 2 ltac:(unfold acallee_saved; lia)) RSP).
  split; [unfold spZ; rewrite RSP2; unfold w64; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
          change (2 ^ Z.of_N 64) with (2 ^ 64); apply Z.mod_small; lia|].
  split; [exact Hres2|].
  split; [exact (eq_trans (Hpres2 18 ltac:(unfold acallee_saved; lia)) RS2)|].
  split; [exact (eq_trans (Hpres2 20 ltac:(unfold acallee_saved; lia)) RS4)|].
  split; [exact (eq_trans (Hpres2 21 ltac:(unfold acallee_saved; lia)) RS5)|].
  split; [exact (eq_trans (Hpres2 22 ltac:(unfold acallee_saved; lia)) RS6)|].
  split; [exact (eq_trans (Hpres2 23 ltac:(unfold acallee_saved; lia)) RS7)|].
  split; [exact (eq_trans (Hpres2 24 ltac:(unfold acallee_saved; lia)) RS8)|].
  split; [exact (eq_trans (Hpres2 26 ltac:(unfold acallee_saved; lia)) RS10)|].
  split; [exact (eq_trans (Hpres2 27 ltac:(unfold acallee_saved; lia)) RS11)|].
  split; [exact (KSLOT 0 F ltac:(lia) ltac:(lia) SL0)|].
  split; [exact (KSLOT 8 SH ltac:(lia) ltac:(lia) SL8)|].
  split; [exact (KSLOT 16 F ltac:(lia) ltac:(lia) SL16)|].
  split; [exact (KSLOT 32 SHADOW_OFF ltac:(lia) ltac:(lia) SL32)|].
  split; [exact (KSLOT 56 (ns mod 2 ^ 32) ltac:(lia) ltac:(lia) SL56)|].
  split; [exact (KSLOT 64 (nch mod 2 ^ 32) ltac:(lia) ltac:(lia) SL64)|].
  split; [exact (KSLOT 72 (ns mod 2 ^ 64) ltac:(lia) ltac:(lia) SL72)|].
  split; [exact (KSLOT 88 out ltac:(lia) ltac:(lia) SL88)|].
  split; [exact (KSLOT 112 F ltac:(lia) ltac:(lia) SL112)|].
  split; [intros i Hi; rewrite (KEEPLOW (SH + i) ltac:(lia)); exact (Fsh0 i Hi)|].
  split; [rewrite (KEEPLOW (SH + 4) ltac:(lia)); exact Fsh4|].
  split; [rewrite (KEEPLOW (SH + 5) ltac:(lia)); exact Fsh5|].
  split; [intros i Hi; rewrite (KEEPLOW (SH + i) ltac:(lia)); exact (Fsh6 i Hi)|].
  split; [apply (dsd_garr8_keep (w_H W) mem mem2 res _); [|exact HG];
          intros i Hi; rewrite length_map, Hbs in Hi; apply KEEPLOW; lia|].
  split; [apply (dsd_valmem_keep (w_H W) mem mem2 (mode + 4) 4 _); [|exact Hmv1];
          intros i Hi; apply KEEPLOW; lia|].
  split; [apply (dsd_valmem_keep (w_H W) mem mem2 (mode + 8) 4 _); [|exact Hmv2];
          intros i Hi; apply KEEPLOW; lia|].
  split.
  + intros a Ha Hn. unfold ESTACK in Hn. rewrite (KEEP2 a Ha ltac:(lia)). apply KEEPRUN; [exact Ha | lia].
  + intros a Hp. apply Hgr2.
    lazymatch goal with HGx : YK1b.mem_grows (mrestrict _ mem) (mrestrict _ _) |- _ =>
      exact (apresent_grows _ _ _ a HGx Hp) end.
Qed.


(* The environment from +0x430 on: atoms 32 .. 45 as dsd_extra2 says, and the atoms of tl from 46 on (the copy's
   bytes, on the paths that read them). *)
Definition DEND2 (regs : bvmap 5 word) (F SH ns32 nch32 ns64 out : Z) (tl : list word) : env :=
  Eimg (PI := PIB) (Ereg regs (dsd_extra2 F SH ns32 nch32 ns64 out ++ tl)).

(* The same, from the return of reac_frame_inspect on (pc +0x430 and +0x5a0): the buffer is now the spill slot 88
   (atom 45). *)
Lemma dsd_st_at : forall pc (W : world decodesegsB0) regs mem sp1 out res F SH ns32 nch32 ns64 tl,
  YK11.getr regs 9 = w64 sp1 -> 2 ^ 46 <= sp1 -> sp1 + 120 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  4096 <= out -> out < 2 ^ 47 -> out mod 16 = 0 ->
  YK11.getr regs 27 = w64 res -> 4096 <= res -> res <= CEIL_MAX -> res mod 16 = 0 ->
  0 <= F < 2 ^ 64 -> 0 <= SH < 2 ^ 64 -> 0 <= ns32 < 2 ^ 64 -> 0 <= nch32 < 2 ^ 64 -> 0 <= ns64 < 2 ^ 64 ->
  rdword (aview decodesegsB0 (w_H W) mem) (sp1 + 0) = Some F ->
  rdword (aview decodesegsB0 (w_H W) mem) (sp1 + 8) = Some SH ->
  rdword (aview decodesegsB0 (w_H W) mem) (sp1 + 16) = Some F ->
  rdword (aview decodesegsB0 (w_H W) mem) (sp1 + 32) = Some SHADOW_OFF ->
  rdword (aview decodesegsB0 (w_H W) mem) (sp1 + 56) = Some ns32 ->
  rdword (aview decodesegsB0 (w_H W) mem) (sp1 + 64) = Some nch32 ->
  rdword (aview decodesegsB0 (w_H W) mem) (sp1 + 72) = Some ns64 ->
  rdword (aview decodesegsB0 (w_H W) mem) (sp1 + 88) = Some out ->
  rdword (aview decodesegsB0 (w_H W) mem) (sp1 + 112) = Some F ->
  (forall o, 24 <= o < 96 -> apresent (w_H W) mem (sp1 + o)) ->
  st_ok_pi SEGS VAL (DEND2 regs F SH ns32 nch32 ns64 out tl) (mkSS pc sr_atoms [dsd_spill2] None dsd_facts2)
    (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom SEGS))).
Proof.
intros pc W regs mem sp1 out res F SH ns32 nch32 ns64 tl H9 Hsp1a Hsp1b Hsp1m Ho1 Ho2 Ho3 H27 Hr1 Hr2 Hr3
  HF HSH Hns32 Hnch32 Hns64 R0 R8 R16 R32 R56 R64 R72 R88 R112 HP.
rewrite restrict_mkst_fx.
set (E := DEND2 regs F SH ns32 nch32 ns64 out tl).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (dsd_extra2 F SH ns32 nch32 ns64 out ++ tl)) k)
  by (intros k Hk; unfold E, DEND2; apply Eimg_low; exact Hk).
assert (EREG : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = YK11.getr regs r).
{ intros kk r Hk. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
  rewrite EL by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ kk r Hk). }
assert (EX : forall (j : nat) v, (j < 14)%nat ->
    nth j (dsd_extra2 F SH ns32 nch32 ns64 out ++ tl) (Z_to_bv 64 0) = Z_to_bv 64 v -> ew E (32 + j) = Z_to_bv 64 v)
  by (intros j v Hj Hnth; rewrite EL by (unfold A_TEXT; lia); rewrite ew_Ereg_extra; exact Hnth).
assert (E9 : bv_unsigned (ew E 9) = sp1)
  by (rewrite (EREG 9%nat 9%bv eq_refl), H9; unfold w64; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
      change (2 ^ Z.of_N 64) with (2 ^ 64); apply Z.mod_small; lia).

assert (E27 : bv_unsigned (ew E 27) = res)
  by (rewrite (EREG 27%nat 27%bv eq_refl), H27; unfold w64; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
      change (2 ^ Z.of_N 64) with (2 ^ 64); apply Z.mod_small; lia).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by exact (EX 0%nat SB ltac:(lia) eq_refl).
assert (E40 : ew E 40 = Z_to_bv 64 F) by exact (EX 8%nat F ltac:(lia) eq_refl).
assert (E41 : ew E 41 = Z_to_bv 64 SH) by exact (EX 9%nat SH ltac:(lia) eq_refl).
assert (E42 : ew E 42 = Z_to_bv 64 ns32) by exact (EX 10%nat ns32 ltac:(lia) eq_refl).
assert (E43 : ew E 43 = Z_to_bv 64 nch32) by exact (EX 11%nat nch32 ltac:(lia) eq_refl).
assert (E44 : ew E 44 = Z_to_bv 64 ns64) by exact (EX 12%nat ns64 ltac:(lia) eq_refl).
assert (E45 : ew E 45 = Z_to_bv 64 out) by exact (EX 13%nat out ltac:(lia) eq_refl).
assert (U45 : bv_unsigned (ew E 45) = out)
  by (rewrite E45, Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
      change (2 ^ Z.of_N 64) with (2 ^ 64); apply Z.mod_small; lia).
assert (USB : bv_unsigned (ew E 32) = SB)
  by (rewrite E32, Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
      change (2 ^ Z.of_N 64) with (2 ^ 64); apply Z.mod_small; unfold SB; lia).
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  unfold dsd_spill2, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9. split; [lia|]. split; [lia|].
  split; [intros o Ho; apply (apresent_writable decodesegsB0); apply HP; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  + apply (chunk_ok_val decodesegsB0 E _ sp1 0 8 (SOff 40 0) F);
      [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact (val_mem_of_rdword decodesegsB0 _ _ _ _ R0).
  + apply (chunk_ok_val decodesegsB0 E _ sp1 8 8 (SOff 41 0) SH);
      [cbn [sv_denot]; rewrite E41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact (val_mem_of_rdword decodesegsB0 _ _ _ _ R8).
  + apply (chunk_ok_val decodesegsB0 E _ sp1 16 8 (SOff 40 0) F);
      [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact (val_mem_of_rdword decodesegsB0 _ _ _ _ R16).
  + apply (chunk_ok_val decodesegsB0 E _ sp1 32 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; zside | zside |].
    exact (val_mem_of_rdword decodesegsB0 _ _ _ _ R32).
  + apply (chunk_ok_val decodesegsB0 E _ sp1 56 8 (SOff 42 0) ns32);
      [cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact (val_mem_of_rdword decodesegsB0 _ _ _ _ R56).
  + apply (chunk_ok_val decodesegsB0 E _ sp1 64 8 (SOff 43 0) nch32);
      [cbn [sv_denot]; rewrite E43, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact (val_mem_of_rdword decodesegsB0 _ _ _ _ R64).
  + apply (chunk_ok_val decodesegsB0 E _ sp1 72 8 (SOff 44 0) ns64);
      [cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact (val_mem_of_rdword decodesegsB0 _ _ _ _ R72).
  + apply (chunk_ok_val decodesegsB0 E _ sp1 88 8 (SOff 45 0) out);
      [cbn [sv_denot]; rewrite E45, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact (val_mem_of_rdword decodesegsB0 _ _ _ _ R88).
  + apply (chunk_ok_val decodesegsB0 E _ sp1 112 8 (SOff 40 0) F);
      [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact (val_mem_of_rdword decodesegsB0 _ _ _ _ R112).
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- split; [|split; [exact I | exact I]].
  cbn [dsd_facts2 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E9, U45, E27, USB.
  change (2 ^ 5) with 32. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold SB; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. +0x430 .. +0x59c: the frame-field checks, to the join at +0x5a0  *)
(* ------------------------------------------------------------------ *)


(* The post at +0x5a0 from what each path shows there: the registers and the spill slots read off its symbolic
   state, and every other fact carried from +0x430 through KR / PR (no store of the stage leaves the window
   [sp1 - ESTACK, sp1 + 120)). *)
Lemma dsd_mk5a0 : forall (W : world decodesegsB0) regsT STK sp0 FP ly S W0 mem0 md0 own lyc Sc k memS
    (sp1 F SH res out len mode nch ns olen prod fits0 : Z) (bs : list byte) mem regs2 mem2 md2,
  @ajournal rc dec_B_sink_head decodesegsB0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k ->
  YK11.getr regs2 3 = w64 (as_gp B) -> YK11.getr regs2 4 = w64 (as_tp B) ->
  YK11.getr regs2 8 = w64 sp0 -> YK11.getr regs2 9 = w64 sp1 -> YK11.getr regs2 2 = w64 sp1 ->
  YK11.getr regs2 19 = w64 (if CInsp.inspect_wf len bs then 1 else 0) ->
  YK11.getr regs2 20 = w64 len -> YK11.getr regs2 21 = w64 mode -> YK11.getr regs2 22 = w64 prod ->
  YK11.getr regs2 23 = w64 nch -> YK11.getr regs2 24 = w64 fits0 ->
  YK11.getr regs2 26 = w64 olen -> YK11.getr regs2 27 = w64 res ->
  0 <= sp1 < 2 ^ 64 ->
  rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 0) = Some F ->
  rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 8) = Some SH ->
  rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 16) = Some F ->
  rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 24) = Some len ->
  rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 32) = Some SHADOW_OFF ->
  rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 40) = Some res ->
  rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 56) = Some (ns mod 2 ^ 32) ->
  rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 64) = Some (nch mod 2 ^ 32) ->
  rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 72) = Some (ns mod 2 ^ 64) ->
  rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 88) = Some out ->
  rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 112) = Some F ->
  (forall i, 0 <= i < 4 -> aview decodesegsB0 (w_H W) mem (SH + i) = Some DEC_SH_LEFT) ->
  aview decodesegsB0 (w_H W) mem (SH + 4) = Some 0 ->
  aview decodesegsB0 (w_H W) mem (SH + 5) = Some 4 ->
  (forall i, 6 <= i < 8 -> aview decodesegsB0 (w_H W) mem (SH + i) = Some DEC_SH_RIGHT) ->
  garr8 decodesegsB0 (mrestrict (w_H W) mem) res (map (fun b : byte => bv_unsigned b) bs) ->
  val_mem decodesegsB0 (mrestrict (w_H W) mem) (mode + 4) 4%nat (nch mod 2 ^ 32) ->
  val_mem decodesegsB0 (mrestrict (w_H W) mem) (mode + 8) 4%nat (ns mod 2 ^ 32) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - ESTACK <= a < sp1 + 120) ->
     aview decodesegsB0 (w_H W) mem a = aview decodesegsB0 (w_H W) memS a) ->
  (forall a, apresent (w_H W) memS a -> apresent (w_H W) mem a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - ESTACK <= a < sp1 + 120) ->
     aview decodesegsB0 (w_H W) mem2 a = aview decodesegsB0 (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) ->
  0 <= SH -> SH + 8 <= sp1 - ESTACK -> 0 <= res -> res + Z.of_nat (length bs) <= sp1 - ESTACK ->
  0 <= mode -> mode + 12 <= sp1 - ESTACK ->
  dsd_at5a0 W regsT STK sp0 FP ly S W0 mem0 md0 own lyc Sc k memS
    sp1 F SH res out len mode nch ns olen prod fits0 bs W
    (mkCfg (YK11.mkst regs2 (w64 (decodeb_text + 0x5a0)) mem2 (YK11.seg_rom decodesegsB0)) md2).
Proof.
intros W regsT STK sp0 FP ly S W0 mem0 md0 own lyc Sc k memS sp1 F SH res out len mode nch ns olen prod fits0 bs
  mem regs2 mem2 md2 HJ R3 R4 R8 R9 R2 R19 R20 R21 R22 R23 R24 R26 R27 Hsp1 S0 S8 S16 S24 S32 S40 S56 S64 S72 S88 S112
  Fsh0 Fsh4 Fsh5 Fsh6 HG Hmv1 Hmv2 KS PS KR PR HSH0 HSH1 Hr0 Hr1 Hm0 Hm1.
assert (KL : forall a, 0 <= a < sp1 - ESTACK -> aview decodesegsB0 (w_H W) mem2 a = aview decodesegsB0 (w_H W) mem a)
  by (intros a Ha; apply KR; unfold ESTACK in *; lia).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [reflexivity|]. split; [exact HJ|].
split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
split; [unfold spZ; rewrite R2; unfold w64; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
        change (2 ^ Z.of_N 64) with (2 ^ 64); apply Z.mod_small; lia|].
split; [exact R19|]. split; [exact R20|]. split; [exact R21|]. split; [exact R22|].
split; [exact R23|]. split; [exact R24|]. split; [exact R26|]. split; [exact R27|].
split; [exact S0|]. split; [exact S8|]. split; [exact S16|]. split; [exact S24|]. split; [exact S32|].
split; [exact S40|]. split; [exact S56|]. split; [exact S64|]. split; [exact S72|]. split; [exact S88|].
split; [exact S112|].
split; [intros i Hi; rewrite (KL (SH + i) ltac:(lia)); exact (Fsh0 i Hi)|].
split; [rewrite (KL (SH + 4) ltac:(lia)); exact Fsh4|].
split; [rewrite (KL (SH + 5) ltac:(lia)); exact Fsh5|].
split; [intros i Hi; rewrite (KL (SH + i) ltac:(lia)); exact (Fsh6 i Hi)|].
split; [apply (dsd_garr8_keep (w_H W) mem mem2 res _); [|exact HG];
        intros i Hi; rewrite length_map in Hi; apply KL; lia|].
split; [apply (dsd_valmem_keep (w_H W) mem mem2 (mode + 4) 4 _); [|exact Hmv1]; intros i Hi; apply KL; lia|].
split; [apply (dsd_valmem_keep (w_H W) mem mem2 (mode + 8) 4 _); [|exact Hmv2]; intros i Hi; apply KL; lia|].
split.
- intros a Ha Hn. rewrite (KR a Ha Hn). exact (KS a Ha Hn).
- intros a Hp. exact (PR a (PS a Hp)).
Qed.

(* ---- the stage-2 kit: write rights, the frame fold, atoms, slots, the close at +0x5a0 ---- *)

(* The write right of a run of this segment: the spill area [sp1 + 24, sp1 + 96) in the caller's stack window, the
   read-only regions (the copy's bytes) none. *)
Ltac dsd_awr sp1 sp0 E9 :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]);
  first
  [ apply awr_ok_nil
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (sp1 - sp0));
    [ reflexivity
    | repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; rewrite E9; lia
    | cbn; lia | cbn; lia | apply awr_ok_nil ] ].

(* After a run: the bytes outside [sp1 - ESTACK, sp1 + 120) are still those of the stage's first memory (KR), and
   what was present is present (PR); the run's frame and growth hypotheses are folded into the two. *)
Ltac dsd_fold W sp1 E9 KR PR :=
  lazymatch type of KR with forall a, _ -> _ -> aview _ _ ?mc a = aview _ _ ?mb a =>
  lazymatch goal with
  | HFr : frame_of ?Ex ?rsx (mrestrict _ mc) (mrestrict _ ?m1), HGx : YK1b.mem_grows (mrestrict _ mc) (mrestrict _ ?m1) |- _ =>
    let K2 := fresh "KR" in let P2 := fresh "PR" in
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - ESTACK <= a < sp1 + 120) ->
                   aview decodesegsB0 (w_H W) m1 a = aview decodesegsB0 (w_H W) mb a);
    [ let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
      intros a Ha Hn; refine (eq_trans _ (KR a Ha Hn));
      refine (kept_of_frame Ex rsx (w_H W) mc m1 (fun x => sp1 - ESTACK <= x < sp1 + 120) HFr _ a Ha Hn);
      let bb := fresh "bb" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
      let Hin := fresh "Hin" in let Hr := fresh "Hr" in let Hq := fresh "Hq" in
      intros bb wlo whi x Hin Hr;
      let wsv := eval vm_compute in (windows rsx) in change (In (bb, wlo, whi) wsv) in Hin;
      cbn [In] in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr|]); try contradiction;
      repeat first [rewrite ew_ewset_other in Hr by lia | rewrite ew_havoc_old in Hr by lia];
      try rewrite E9 in Hr; unfold ESTACK; lia
    | ];
    assert (P2 : forall a, apresent (w_H W) mb a -> apresent (w_H W) m1 a)
      by (let a := fresh "a" in let Hq := fresh "Hq" in
          intros a Hq; apply (apresent_grows _ _ _ a HGx); apply PR; exact Hq);
    clear KR PR HGx; rename K2 into KR; rename P2 into PR
  end end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.

Lemma dsd_den_atom : forall E n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma dsd_spZ_reg : forall (regs : bvmap 5 word) sp1, spZ regs = sp1 -> YK11.getr regs 2 = w64 sp1.
Proof. intros regs sp1 H. unfold spZ in H. rewrite <- H. unfold w64. symmetry. apply Z_to_bv_bv_unsigned. Qed.

(* An atom of the stage's first environment E (AT, the table of its values), read at a later environment Ex of the
   same stage (EA: Ex and E agree below 200). *)
Ltac dsd_atom EA AT :=
  apply dsd_den_atom; rewrite ?EA by lia; apply AT; cbn [In]; repeat (first [left; reflexivity | right]).
(* The slot sp1 + off of the spill region HR0 holds v. *)
Ltac dsd_slot W sp1 HR0 E9' EA AT msx off v Hs :=
  lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
  assert (Hs : rdword (aview decodesegsB0 (w_H W) (ms_mem msx)) (sp1 + off) = Some v) by
    (apply dsd_rdword_of_val_mem; [|unfold SHADOW_OFF; lia];
     refine (field_of_region Ex _ 9%nat sp1 _ _ _ _ _ off 8%N _ v HR0 E9'
       ltac:(cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right])) ltac:(dsd_atom EA AT)
       ltac:(cbn; unfold SHADOW_OFF; lia) ltac:(cbn; lia)))
  end.

(* The close at +0x5a0 of every path of stage 2: the spill slots off the spill region (index ri of HS's regions),
   the registers off HS (s3 by tac19), and dsd_mk5a0 with the facts of +0x430 (named as dsd_stage2_* names them). *)
Ltac dsd_close5a0 HS HJ KR PR ri EA AT E9 tac19 :=
  lazymatch goal with |- SRr _ ?W _ (dsd_at5a0 ?W ?regsT ?STK ?sp0 ?FP ?ly ?S ?W0 ?mem0 ?md0 ?own ?lyc ?Sc ?k ?memS
                                       ?sp1 ?F ?SH ?res ?out ?len ?mode ?nch ?ns ?olen ?prod ?fits0 ?bs) =>
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
  let r0 := eval vm_compute in (nth ri (ss_mem ssx) got_regionP) in
  let HR0 := fresh "HR0" in
  assert (HR0 : region_ok SEGS Ex (ms_mem (restrict (w_H W) msx)) r0)
    by (apply (st_ok_region_nth Ex (abs_ss VAL ssx) (restrict (w_H W) msx) ri r0 HS); vm_compute; reflexivity);
  cbn [ms_mem restrict] in HR0;
  let E9' := fresh "E9'" in
  assert (E9' : bv_unsigned (ew Ex 9) = sp1) by (rewrite ?EA by lia; exact E9);
  let S0 := fresh "S" in let S8 := fresh "S" in let S16 := fresh "S" in let S24 := fresh "S" in
  let S32 := fresh "S" in let S40 := fresh "S" in let S56 := fresh "S" in let S64 := fresh "S" in
  let S72 := fresh "S" in let S88 := fresh "S" in let S112 := fresh "S" in
  dsd_slot W sp1 HR0 E9' EA AT msx 0 F S0;
  dsd_slot W sp1 HR0 E9' EA AT msx 8 SH S8;
  dsd_slot W sp1 HR0 E9' EA AT msx 16 F S16;
  dsd_slot W sp1 HR0 E9' EA AT msx 24 len S24;
  dsd_slot W sp1 HR0 E9' EA AT msx 32 SHADOW_OFF S32;
  dsd_slot W sp1 HR0 E9' EA AT msx 40 res S40;
  dsd_slot W sp1 HR0 E9' EA AT msx 56 (ns mod 2 ^ 32) S56;
  dsd_slot W sp1 HR0 E9' EA AT msx 64 (nch mod 2 ^ 32) S64;
  dsd_slot W sp1 HR0 E9' EA AT msx 72 (ns mod 2 ^ 64) S72;
  dsd_slot W sp1 HR0 E9' EA AT msx 88 out S88;
  dsd_slot W sp1 HR0 E9' EA AT msx 112 F S112;
  let G2 := fresh "G" in let G3 := fresh "G" in let G4 := fresh "G" in let G8 := fresh "G" in
  let G9 := fresh "G" in let G19 := fresh "G" in let G20 := fresh "G" in let G21 := fresh "G" in
  let G22 := fresh "G" in let G23 := fresh "G" in let G24 := fresh "G" in let G26 := fresh "G" in
  let G27 := fresh "G" in
  reg_at HS (2%bv : bv 5) (w64 sp1) G2 ltac:(dsd_atom EA AT);
  reg_at HS (3%bv : bv 5) (w64 (as_gp B)) G3 ltac:(dsd_atom EA AT);
  reg_at HS (4%bv : bv 5) (w64 (as_tp B)) G4 ltac:(dsd_atom EA AT);
  reg_at HS (8%bv : bv 5) (w64 sp0) G8 ltac:(dsd_atom EA AT);
  reg_at HS (9%bv : bv 5) (w64 sp1) G9 ltac:(dsd_atom EA AT);
  reg_at HS (19%bv : bv 5) (w64 (if CInsp.inspect_wf len bs then 1 else 0)) G19 tac19;
  reg_at HS (20%bv : bv 5) (w64 len) G20 ltac:(dsd_atom EA AT);
  reg_at HS (21%bv : bv 5) (w64 mode) G21 ltac:(dsd_atom EA AT);
  reg_at HS (22%bv : bv 5) (w64 prod) G22 ltac:(dsd_atom EA AT);
  reg_at HS (23%bv : bv 5) (w64 nch) G23 ltac:(dsd_atom EA AT);
  reg_at HS (24%bv : bv 5) (w64 fits0) G24 ltac:(dsd_atom EA AT);
  reg_at HS (26%bv : bv 5) (w64 olen) G26 ltac:(dsd_atom EA AT);
  reg_at HS (27%bv : bv 5) (w64 res) G27 ltac:(dsd_atom EA AT);
  repeat rewrite wvb_collapse in HJ;
  pmkst HS;
  apply SRr_ret;
  lazymatch type of KR with forall a, _ -> _ -> aview _ _ _ a = aview _ _ ?mb a =>
  refine (dsd_mk5a0 W regsT STK sp0 FP ly S W0 mem0 md0 own lyc Sc k memS sp1 F SH res out len mode nch ns olen prod
    fits0 bs mb (ms_regs msx) (ms_mem msx) _ HJ G3 G4 G8 G9 G2 G19 G20 G21 G22 G23 G24 G26 G27 ltac:(lia)
    S0 S8 S16 S24 S32 S40 S56 S64 S72 S88 S112 _ _ _ _ _ _ _ _ _ KR PR _ _ _ _ _ _) end;
  first [ assumption
        | lazymatch goal with Hb : length bs = Z.to_nat _ |- _ => rewrite Hb, Z2Nat.id by lia end; unfold ESTACK; lia
        | unfold ESTACK; lia ]
  end end.

(* After a run the environment grows above slot 511, after a call it is havocked from slot 200 on
   (lib/B/Prog/LLVMFuzzerTestOneInput_segC.v's cp_env): EA says the slots below 200 are the stage's first environment
   E's. *)
Ltac dsd_env E EA :=
  let Ex := lazymatch goal with HS : st_ok_pi _ _ ?Ex _ _ |- _ => Ex | HS : st_ok _ ?Ex _ _ |- _ => Ex end in
  lazymatch type of EA with forall n, _ -> ew Ex n = _ => idtac | _ =>
    let EA2 := fresh "EA" in
    assert (EA2 : forall n, (n < 200)%nat -> ew Ex n = ew E n)
      by (let nn := fresh "nn" in let Hnn := fresh "Hnn" in
          intros nn Hnn; repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia];
          first [reflexivity | apply EA; exact Hnn]);
    clear EA; rename EA2 into EA
  end.
Ltac dsd_U EA AT :=
  first [ rewrite ?EA by lia; apply AT; cbn [In]; repeat (first [left; reflexivity | right]) | lia ].
(* A shadow-check obligation of a run on the copy's bytes: the copy is a live block of the journal's state. *)
Ltac dsd_obl W HJ Hinr EA AT :=
  lazymatch goal with |- range_addressable (rd_of _ (mrestrict _ ?m)) (U ?Ex (SOff 32 0)) (U ?Ex (SOff 27 ?c)) ?n =>
    rewrite (U_atom Ex 32 SHADOW_OFF) by (first [rewrite ?EA by lia; apply AT; cbn [In]; repeat (first [left; reflexivity | right])
                                                 | unfold SHADOW_OFF; lia]);
    lazymatch goal with |- range_addressable _ _ (U _ (SOff 27 c)) _ =>
    lazymatch type of Hinr with In (?res, ?len) _ =>
      rewrite (U_atom_off Ex 27 res c) by (first [rewrite ?EA by lia; apply AT; cbn [In]; repeat (first [left; reflexivity | right])
                                                 | lia]);
      change (rd_of SEGS (mrestrict (w_H W) m)) with (aview decodesegsB0 (w_H W) m);
      eapply (range_addressable_of_block decodesegsB0 B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hinr); lia
    end end
  end.
(* One run of the stage: its shadow-check obligations (on the copy's bytes) and its write right discharged, the frame
   folded into KR / PR and the environment's agreement EA renewed. *)
Ltac dsd_run RUN HS HJ SHOK W sp1 sp0 E E9 EA AT KR PR Hinr :=
  paj_run_tok RUN HS HJ SHOK Bspan; try first [dsd_obl W HJ Hinr EA AT | dsd_awr sp1 sp0 E9];
  dsd_fold W sp1 E9 KR PR; dsd_env E EA.
Ltac dsd_run_to RUNTO HS HJ SHOK W sp1 sp0 E E9 EA AT KR PR Hinr pc :=
  paj_run_to_tok RUNTO HS HJ SHOK Bspan pc; try first [dsd_obl W HJ Hinr EA AT | dsd_awr sp1 sp0 E9];
  dsd_fold W sp1 E9 KR PR; dsd_env E EA.
(* The tail of a path that has found the frame not well formed (HWF), from a state whose run stops at the `bne` of
   +0x520 with s3 = 0: the abort edge refuted (the inspect result is 0), then to +0x5a0 and the close. *)
Ltac dsd_nwf_tail RUN RUNTO BR HS HJ SHOK KR PR W sp1 sp0 E E9 EA AT HWF :=
  let IR0 := fresh "IR0" in
  assert (IR0 : CInsp.inspect_result _ _ = 0) by (unfold CInsp.inspect_result; rewrite HWF; reflexivity);
  paj_run_tok RUN HS HJ SHOK Bspan; [ dsd_awr sp1 sp0 E9 | ];
  dsd_fold W sp1 E9 KR PR; dsd_env E EA;
  psrr_branch_tok RUN BR HS SHOK Bspan;
  [ exfalso;
    lazymatch goal with Hc : branch_taken _ (sv_denot ?Ex _) _ = true |- _ =>
      rewrite branch_ne_U, U_SAlu, (U_atom Ex 10 0), !U_lit in Hc
        by (first [rewrite <- IR0; rewrite ?EA by lia; apply AT; cbn [In]; repeat (first [left; reflexivity | right]) | lia]);
      cbn in Hc; discriminate Hc end
  | ];
  lazymatch goal with Hc : branch_taken _ _ _ = false |- _ => clear Hc end;
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x5a0; [ dsd_awr sp1 sp0 E9 | ];
  dsd_fold W sp1 E9 KR PR; dsd_env E EA;
  dsd_close5a0 HS HJ KR PR 1%nat EA AT E9 ltac:(rewrite HWF; reflexivity).

(* The copy's six bytes the stage reads, as atoms 46 .. 51 (header 12 / 13, counter 14 / 15, trailer 1490 / 1491), and
   the read-only region of the copy that holds them. *)
Definition dsd_bytes (bs : list byte) : list word :=
  [Z_to_bv 64 (CInsp.inspect_byte bs 12); Z_to_bv 64 (CInsp.inspect_byte bs 13);
   Z_to_bv 64 (CInsp.inspect_byte bs 14); Z_to_bv 64 (CInsp.inspect_byte bs 15);
   Z_to_bv 64 (CInsp.inspect_byte bs 1490); Z_to_bv 64 (CInsp.inspect_byte bs 1491)].
Definition dsd_copy : YP09.region :=
  YP09.mkRegion (Some 27%nat) 0 1492 0 0
    [YP09.mkChunk 12 (CVal 1 (SOff 46 0)); YP09.mkChunk 13 (CVal 1 (SOff 47 0));
     YP09.mkChunk 14 (CVal 1 (SOff 48 0)); YP09.mkChunk 15 (CVal 1 (SOff 49 0));
     YP09.mkChunk 1490 (CVal 1 (SOff 50 0)); YP09.mkChunk 1491 (CVal 1 (SOff 51 0))].

Lemma dsd_byte_mem : forall (H : word -> bool) m res (bs : list byte) (i : nat),
  garr8 decodesegsB0 (mrestrict H m) res (map (fun b : byte => bv_unsigned b) bs) -> (i < length bs)%nat ->
  val_mem decodesegsB0 (mrestrict H m) (res + Z.of_nat i) 1 (CInsp.inspect_byte bs i) /\
  0 <= CInsp.inspect_byte bs i < 256.
Proof.
intros H m res bs i HG Hi.
assert (Hn : nth i (map (fun b : byte => bv_unsigned b) bs) 0 = CInsp.inspect_byte bs i).
{ unfold CInsp.inspect_byte. rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hi).
  apply map_nth. }
split.
- rewrite <- Hn. exact (proj1 (HG i ltac:(rewrite length_map; exact Hi))).
- unfold CInsp.inspect_byte. pose proof (bv_unsigned_in_range 8 (nth i bs (Z_to_bv 8 0))) as Q.
  change (bv_modulus 8) with 256 in Q. exact Q.
Qed.

Lemma dsd_U_byte : forall Ex n v, ew Ex n = Z_to_bv 64 v -> 0 <= v < 256 -> U Ex (SExt false 8 (SOff n 0)) = v.
Proof.
intros Ex n v H Hv. rewrite U_zext, (U_atom Ex n v H ltac:(lia)). change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. lia.
Qed.
(* `addi a1, a1, -c; seqz s3, a1` on a byte (+0x500 / +0x504). *)
Lemma dsd_seqz : forall Ex x b c, U Ex x = b -> 0 <= b < 256 -> 0 < c < 256 ->
  U Ex (SAlu ALU_SLTU (SAlu ALU_ADD x (SLit (- c))) (SLit 1)) = if b =? c then 1 else 0.
Proof.
intros Ex x b c Hx Hb Hc. rewrite !U_SAlu, !U_SLit, Hx. cbn [zalu_raw]. unfold zcanon, M64.
assert (Hm : (- c) mod 2 ^ 64 = 2 ^ 64 - c).
{ replace ((- c) mod 2 ^ 64) with ((- c + 1 * 2 ^ 64) mod 2 ^ 64) by (apply Z.mod_add; lia).
  rewrite Z.mod_small by lia. lia. }
rewrite Hm. change (1 mod 2 ^ 64) with 1.
destruct (Z.eqb_spec b c) as [-> | Hne].
- replace (c + (2 ^ 64 - c)) with (0 + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. reflexivity.
- replace ((b + (2 ^ 64 - c)) mod 2 ^ 64 <? 1) with false; [reflexivity|].
  symmetry. apply Z.ltb_ge. destruct (Z.lt_ge_cases b c).
  + rewrite Z.mod_small; lia.
  + replace (b + (2 ^ 64 - c)) with ((b - c) + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small; lia.
Qed.
Lemma dsd_wf_false : forall len bs,
  (len <> 1492 \/ CInsp.inspect_byte bs 12 <> 136 \/ CInsp.inspect_byte bs 13 <> 25 \/
   CInsp.inspect_byte bs 1490 <> 194 \/ CInsp.inspect_byte bs 1491 <> 234) -> CInsp.inspect_wf len bs = false.
Proof.
intros len bs H. unfold CInsp.inspect_wf.
destruct H as [H | [H | [H | [H | H]]]]; apply Z.eqb_neq in H; rewrite H; rewrite ?andb_false_r; reflexivity.
Qed.
Lemma dsd_wf_true : forall len bs, len = 1492 -> CInsp.inspect_byte bs 12 = 136 -> CInsp.inspect_byte bs 13 = 25 ->
  CInsp.inspect_byte bs 1490 = 194 -> CInsp.inspect_byte bs 1491 = 234 -> CInsp.inspect_wf len bs = true.
Proof. intros len bs -> H12 H13 H90 H91. unfold CInsp.inspect_wf. rewrite H12, H13, H90, H91. reflexivity. Qed.

Lemma dsd_counter_bounds : forall bs, 0 <= CInsp.inspect_counter bs < 65536.
Proof.
intros bs. unfold CInsp.inspect_counter, CInsp.inspect_byte.
pose proof (bv_unsigned_in_range 8 (nth 14 bs (Z_to_bv 8 0))) as Q1.
pose proof (bv_unsigned_in_range 8 (nth 15 bs (Z_to_bv 8 0))) as Q2.
change (bv_modulus 8) with 256 in Q1, Q2. lia.
Qed.
(* The high half of the inspect result (`srli a1, a0, 32` at +0x51c) is the well-formedness flag. *)
Lemma dsd_U_hi : forall Ex len bs, U Ex (SOff 10 0) = CInsp.inspect_result len bs ->
  U Ex (SAlu ALU_SRL (SOff 10 0) (SLit 32)) = if CInsp.inspect_wf len bs then 1 else 0.
Proof.
intros Ex len bs H. rewrite U_SAlu, H, U_lit by lia. cbn [zalu_raw]. change (Z.land 32 63) with 32.
pose proof (dsd_counter_bounds bs) as C.
unfold CInsp.inspect_result. destruct (CInsp.inspect_wf len bs); [|reflexivity].
rewrite Z.shiftr_div_pow2 by lia.
replace ((2 ^ 32 + CInsp.inspect_counter bs) / 2 ^ 32) with 1; [reflexivity|].
apply (Z.div_unique _ _ 1 (CInsp.inspect_counter bs)); lia.
Qed.
Lemma dsd_denot_U : forall Ex e v, U Ex e = v -> sv_denot Ex e = Z_to_bv 64 v.
Proof. intros Ex e v H. rewrite <- H. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma dsd_wf_last : forall len bs, len = 1492 -> CInsp.inspect_byte bs 12 = 136 -> CInsp.inspect_byte bs 13 = 25 ->
  CInsp.inspect_byte bs 1490 = 194 -> CInsp.inspect_wf len bs = (CInsp.inspect_byte bs 1491 =? 234).
Proof. intros len bs -> H12 H13 H90. unfold CInsp.inspect_wf. rewrite H12, H13, H90. reflexivity. Qed.
Lemma dsd_lor8 : forall a h, 0 <= a < 2 ^ 8 -> 0 <= h -> Z.lor (h * 2 ^ 8) a = h * 2 ^ 8 + a.
Proof.
intros a h Ha Hh. rewrite Z.lor_comm. rewrite <- (Z.shiftl_mul_pow2 h 8) by lia.
assert (Hd : Z.land a (Z.shiftl h 8) = 0).
{ apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases n 8) as [Hl | Hg].
  - rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
  - rewrite <- (Z.mod_small a (2 ^ 8)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
rewrite <- Z.lxor_lor by exact Hd. rewrite <- Z.add_nocarry_lxor by exact Hd. lia.
Qed.
(* `slli a2, a2, 8; or s2, a2, a1` (+0x584 / +0x588) on the two counter bytes. *)
Lemma dsd_U_pair : forall Ex x y lo hi, U Ex x = lo -> U Ex y = hi -> 0 <= lo < 256 -> 0 <= hi < 256 ->
  U Ex (SAlu ALU_OR (SAlu ALU_SLL y (SLit 8)) x) = lo + 256 * hi.
Proof.
intros Ex x y lo hi Hx Hy Hl Hh. rewrite !U_SAlu, U_lit, Hx, Hy by lia. cbn [zalu_raw]. change (Z.land 8 63) with 8.
rewrite Z.shiftl_mul_pow2 by lia. unfold zcanon, M64.
rewrite (Z.mod_small (hi * 2 ^ 8)) by lia. rewrite dsd_lor8 by lia. rewrite Z.mod_small by lia. lia.
Qed.
(* `slli a0, a0, 48; srli a0, a0, 48` (+0x580 / +0x58c): the low 16 bits. *)
Lemma dsd_U_lo16 : forall Ex x r, U Ex x = r -> 0 <= r < 2 ^ 64 ->
  U Ex (SAlu ALU_SRL (SAlu ALU_SLL x (SLit 48)) (SLit 48)) = r mod 2 ^ 16.
Proof.
intros Ex x r Hx Hr. rewrite !U_SAlu, !U_lit, Hx by lia. cbn [zalu_raw]. change (Z.land 48 63) with 48.
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. unfold zcanon, M64.
replace (2 ^ 64) with (2 ^ 16 * 2 ^ 48) at 1 by reflexivity.
rewrite Z.mul_mod_distr_r by lia. rewrite Z.div_mul by lia.
apply Z.mod_small. pose proof (Z.mod_pos_bound r (2 ^ 16) ltac:(lia)). lia.
Qed.

Lemma dsd_olen_bounds : forall nch ns, -128 <= nch <= 127 -> -128 <= ns <= 127 -> 1 <= dec_b_olen nch ns <= 48387.
Proof.
intros nch ns Hc Hs. unfold dec_b_olen. destruct ((0 <? nch) && (0 <? ns)) eqn:Eq; [|lia].
apply andb_true_iff in Eq as [E1 E2]. apply Z.ltb_lt in E1, E2.
assert (P : 1 <= nch * ns <= 127 * 127) by (split; [nia | apply Z.mul_le_mono_nonneg; lia]).
rewrite <- Z.mul_assoc. lia.
Qed.

Lemma dsd_vis_of_valmem : forall (W : world decodesegsB0) m a (n : nat) v,
  val_mem decodesegsB0 (mrestrict (w_H W) m) a n v -> forall x, a <= x < a + Z.of_nat n -> w_H W (Z_to_bv 64 x) = false.
Proof.
intros W m a n v Hv x Hx. pose proof (Hv (Z.to_nat (x - a)) ltac:(lia)) as H.
rewrite Z2Nat.id in H by lia. replace (a + (x - a)) with x in H by lia.
exact (dec_leafb_mbyte_vis W m x _ H).
Qed.
Lemma dsd_decode_olen : forall len bs nch ns, CDec.decode_ok len bs nch ns = true -> dec_b_olen nch ns = 3 * nch * ns.
Proof.
intros len bs nch ns H. unfold CDec.decode_ok in H. apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [H H4].
apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [_ H1].
unfold dec_b_olen. rewrite H1, H4. reflexivity.
Qed.

(* +0x430 .. +0x5a0 when the length is not 1492: the length test (+0x43c) taken, s3 := 0 (+0x50c), the inspect
   result's high half against s3 (+0x520) refuted (the result is 0), and the `beqz` of +0x524 taken. *)
Lemma dsd_stage2_ne :
  forall (W : world decodesegsB0) regsT STK sp0 FP ly S W0 mem0 md0 own lyc Sc k memS
         (sp1 F SH res out len mode nch ns olen prod fits0 : Z) (bs : list byte) c,
  sp0 - 240 <= sp1 -> sp1 <= sp0 - 224 -> sp1 mod 32 = 0 -> 4336 <= STK ->
  In (res, len) (ablocks B lyc Sc) -> In (out, olen) (ablocks B lyc Sc) ->
  0 <= len < 2 ^ 64 -> length bs = Z.to_nat len -> len <> 1492 ->
  0 <= F < 2 ^ 64 -> 0 <= SH < 2 ^ 64 ->
  4096 <= SH -> SH + 8 <= alloc_ceiling -> 4096 <= mode -> mode + 12 <= alloc_ceiling ->
  dsd_at430 W regsT STK sp0 FP ly S W0 mem0 md0 own lyc Sc k memS
    sp1 F SH res out len mode nch ns olen prod fits0 bs W c ->
  SRr decodesegsB0 W c
    (dsd_at5a0 W regsT STK sp0 FP ly S W0 mem0 md0 own lyc Sc k memS
       sp1 F SH res out len mode nch ns olen prod fits0 bs).
Proof.
intros W regsT STK sp0 FP ly S W0 mem0 md0 own lyc Sc k memS sp1 F SH res out len mode nch ns olen prod fits0 bs c
  Hsp1a Hsp1b Hsp1m HSTK Hinr Hino Hlen Hbs Hne HFrng HSHrng HSHlo HSHhi Hmlo Hmhi
  (_ & regs & mem & md & -> & HJ & Hgp & Htp & H8 & H9 & Hsp & H10 & H18 & H20 & H21 & H22 & H23 & H24 & H26 & H27
   & R0 & R8 & R16 & R32 & R56 & R64 & R72 & R88 & R112 & Fsh0 & Fsh4 & Fsh5 & Fsh6 & HG & Hmv1 & Hmv2 & KS & PS).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof alloc_ceiling_val as HCEIL.
destruct (al_blocks _ _ LAWS _ _ _ _ _ res len HAR Hinr) as (Hral & Hr4096 & Hrceil & _ & Hrpres & _ & Hrmr).
destruct (al_blocks _ _ LAWS _ _ _ _ _ out olen HAR Hino) as (Hoal & Ho4096 & Hoceil & _ & Hopres & _ & Homr).
pose proof (req_size_pos len ltac:(lia)) as [Hqr1 Hqr2].
pose proof (req_size_pos olen ltac:(lia)) as [Hqo1 Hqo2].

pose proof (Z.mod_pos_bound ns (2 ^ 32) ltac:(lia)) as Mns32.
pose proof (Z.mod_pos_bound nch (2 ^ 32) ltac:(lia)) as Mnch32.
pose proof (Z.mod_pos_bound ns (2 ^ 64) ltac:(lia)) as Mns64.
pose proof (dsd_st_at 0x430 W regs mem sp1 out res F SH (ns mod 2 ^ 32) (nch mod 2 ^ 32) (ns mod 2 ^ 64) []
  H9 ltac:(lia) ltac:(lia) Hsp1m ltac:(lia) ltac:(lia) Hoal H27 ltac:(lia) ltac:(lia) Hral
  HFrng HSHrng ltac:(lia) ltac:(lia) ltac:(lia)
  R0 R8 R16 R32 R56 R64 R72 R88 R112 ltac:(intros o Ho; apply Hpres; lia)) as HS.
set (E := DEND2 regs F SH (ns mod 2 ^ 32) (nch mod 2 ^ 32) (ns mod 2 ^ 64) out []) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, DEND2; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H W) mem)) by constructor.
assert (EREG : forall kk (r : bv 5), Z.of_nat kk = bv_unsigned r -> ew E kk = YK11.getr regs r).
{ intros kk r Hk. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
  unfold E, DEND2. rewrite (Eimg_low (PI := PIB) _ kk ltac:(unfold A_TEXT; lia)).
  exact (ew_Ereg_nat regs _ kk r Hk). }
assert (E9 : bv_unsigned (ew E 9) = sp1)
  by (rewrite (EREG 9%nat 9%bv eq_refl), H9; unfold w64; rewrite Z_to_bv_unsigned;
      unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); apply Z.mod_small; lia).
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - ESTACK <= a < sp1 + 120) ->
               aview decodesegsB0 (w_H W) mem a = aview decodesegsB0 (w_H W) mem a) by reflexivity.
assert (PR : forall a, apresent (w_H W) mem a -> apresent (w_H W) mem a) by (intros a Hq; exact Hq).
change (w64 (decodeb_text + 1072)) with (Z_to_bv 64 (BASE + 0x430)).
pose proof (paj_run (SK := dec_B_sink_head) (PI := PIB) B LAWS) as RUN.
pose proof (paj_run_to (SK := dec_B_sink_head) (PI := PIB) B LAWS) as RUNTO.
paj_run_tok RUN HS HJ SHOK Bspan.
{ dsd_awr sp1 sp0 E9. }
dsd_fold W sp1 E9 KR PR.
assert (U20 : U E (SOff 20 0) = len) by (apply U_atom; [rewrite (EREG 20%nat 20%bv eq_refl); exact H20 | lia]).
psrr_branch_tok RUN paj_branch HS SHOK Bspan.
2: { exfalso. lazymatch goal with Hc : branch_taken _ _ _ = false |- _ =>
       rewrite branch_ne_U, U20, U_lit in Hc by lia; apply negb_false_iff, Z.eqb_eq in Hc; lia end. }
lazymatch goal with Hc : branch_taken _ _ _ = true |- _ => clear Hc end.
paj_run_tok RUN HS HJ SHOK Bspan.
{ dsd_awr sp1 sp0 E9. }
dsd_fold W sp1 E9 KR PR.
assert (IR0 : CInsp.inspect_result len bs = 0).
{ unfold CInsp.inspect_result, CInsp.inspect_wf. replace (len =? 1492) with false by (symmetry; apply Z.eqb_neq; exact Hne). reflexivity. }
assert (U10 : U E (SOff 10 0) = 0) by (apply U_atom; [rewrite (EREG 10%nat 10%bv eq_refl), H10, IR0; reflexivity | lia]).
psrr_branch_tok RUN paj_branch HS SHOK Bspan.
1: { exfalso. lazymatch goal with Hc : branch_taken _ _ _ = true |- _ =>
       rewrite branch_ne_U, U_SAlu, U10, !U_lit in Hc by lia; cbn in Hc; discriminate Hc end. }
lazymatch goal with Hc : branch_taken _ _ _ = false |- _ => clear Hc end.
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x5a0.
{ dsd_awr sp1 sp0 E9. }
dsd_fold W sp1 E9 KR PR.
repeat rewrite wvb_collapse in HJ.

assert (AT : forall n v, In (n, v) [(3%nat, as_gp B); (4%nat, as_tp B); (8%nat, sp0); (9%nat, sp1); (2%nat, sp1);
    (20%nat, len); (21%nat, mode); (22%nat, prod); (23%nat, nch); (24%nat, fits0); (26%nat, olen); (27%nat, res);
    (32%nat, SHADOW_OFF); (40%nat, F); (41%nat, SH); (42%nat, ns mod 2 ^ 32); (43%nat, nch mod 2 ^ 32);
    (44%nat, ns mod 2 ^ 64); (45%nat, out)] -> ew E n = Z_to_bv 64 v).
{ intros n v Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <-|]); try contradiction;
  lazymatch goal with |- ew E ?n = _ =>
    first [ assert (Hn : (n < 32)%nat) by lia;
            let r := eval vm_compute in (Z_to_bv 5 (Z.of_nat n)) in rewrite (EREG n r eq_refl);
            first [eassumption | exact (dsd_spZ_reg regs sp1 Hsp)]
          | unfold E, DEND2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ _) ] end. }

assert (EA : forall n, (n < 200)%nat -> ew E n = ew E n) by reflexivity.
assert (HWF : CInsp.inspect_wf len bs = false)
  by (unfold CInsp.inspect_wf; replace (len =? 1492) with false by (symmetry; apply Z.eqb_neq; exact Hne); reflexivity).
dsd_close5a0 HS HJ KR PR 0%nat EA AT E9 ltac:(rewrite HWF; reflexivity).
Qed.


(* +0x430 .. +0x5a0 when the length is 1492: the four header / trailer bytes (each behind its shadow check, the
   UBSan guards of +0x440 .. +0x4dc decided by the copy's bounds), the abort edge of +0x520 refuted (the inspect
   result's high half is the well-formedness flag, which is s3), and on the well-formed path the two counter bytes,
   reac_frame_counter (+0x598) and the two counter checks of +0x590 / +0x59c refuted (both sides are the counter). *)
Lemma dsd_stage2_eq :
  dec_crt_cells B ->
  (forall fx' : YK11.FPState, @dec_leaf_at rc B (@LCounter.dec_reac_frame_counter_cg) fx') ->
  forall (W : world decodesegsB0) regsT STK sp0 FP ly S W0 mem0 md0 own lyc Sc k memS
         (sp1 F SH res out len mode nch ns olen prod fits0 : Z) (bs : list byte) c,
  sp0 - 240 <= sp1 -> sp1 <= sp0 - 224 -> sp1 mod 32 = 0 -> 4336 <= STK ->
  In (res, len) (ablocks B lyc Sc) -> In (out, olen) (ablocks B lyc Sc) ->
  0 <= len < 2 ^ 64 -> length bs = Z.to_nat len -> len = 1492 ->
  0 <= F < 2 ^ 64 -> 0 <= SH < 2 ^ 64 ->
  4096 <= SH -> SH + 8 <= alloc_ceiling -> 4096 <= mode -> mode + 12 <= alloc_ceiling ->
  dsd_at430 W regsT STK sp0 FP ly S W0 mem0 md0 own lyc Sc k memS
    sp1 F SH res out len mode nch ns olen prod fits0 bs W c ->
  SRr decodesegsB0 W c
    (dsd_at5a0 W regsT STK sp0 FP ly S W0 mem0 md0 own lyc Sc k memS
       sp1 F SH res out len mode nch ns olen prod fits0 bs).
Proof.
intros HC HLEAF W regsT STK sp0 FP ly S W0 mem0 md0 own lyc Sc k memS sp1 F SH res out len mode nch ns olen prod fits0 bs c
  Hsp1a Hsp1b Hsp1m HSTK Hinr Hino Hlen Hbs Heq HFrng HSHrng HSHlo HSHhi Hmlo Hmhi
  (_ & regs & mem & md & -> & HJ & Hgp & Htp & H8 & H9 & Hsp & H10 & H18 & H20 & H21 & H22 & H23 & H24 & H26 & H27
   & R0 & R8 & R16 & R32 & R56 & R64 & R72 & R88 & R112 & Fsh0 & Fsh4 & Fsh5 & Fsh6 & HG & Hmv1 & Hmv2 & KS & PS).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof alloc_ceiling_val as HCEIL.
destruct (al_blocks _ _ LAWS _ _ _ _ _ res len HAR Hinr) as (Hral & Hr4096 & Hrceil & _ & Hrpres & _ & Hrmr).
destruct (al_blocks _ _ LAWS _ _ _ _ _ out olen HAR Hino) as (Hoal & Ho4096 & Hoceil & _ & Hopres & _ & Homr).
pose proof (req_size_pos len ltac:(lia)) as [Hqr1 Hqr2].
pose proof (req_size_pos olen ltac:(lia)) as [Hqo1 Hqo2].
pose proof (Z.mod_pos_bound ns (2 ^ 32) ltac:(lia)) as Mns32.
pose proof (Z.mod_pos_bound nch (2 ^ 32) ltac:(lia)) as Mnch32.
pose proof (Z.mod_pos_bound ns (2 ^ 64) ltac:(lia)) as Mns64.
pose proof (dsd_st_at 0x430 W regs mem sp1 out res F SH (ns mod 2 ^ 32) (nch mod 2 ^ 32) (ns mod 2 ^ 64) (dsd_bytes bs)
  H9 ltac:(lia) ltac:(lia) Hsp1m ltac:(lia) ltac:(lia) Hoal H27 ltac:(lia) ltac:(lia) Hral
  HFrng HSHrng ltac:(lia) ltac:(lia) ltac:(lia)
  R0 R8 R16 R32 R56 R64 R72 R88 R112 ltac:(intros o Ho; apply Hpres; lia)) as HS.
set (E := DEND2 regs F SH (ns mod 2 ^ 32) (nch mod 2 ^ 32) (ns mod 2 ^ 64) out (dsd_bytes bs)) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, DEND2; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H W) mem)) by constructor.
assert (EREG : forall kk (r : bv 5), Z.of_nat kk = bv_unsigned r -> ew E kk = YK11.getr regs r).
{ intros kk r Hk. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
  unfold E, DEND2. rewrite (Eimg_low (PI := PIB) _ kk ltac:(unfold A_TEXT; lia)).
  exact (ew_Ereg_nat regs _ kk r Hk). }
assert (E9 : bv_unsigned (ew E 9) = sp1)
  by (rewrite (EREG 9%nat 9%bv eq_refl), H9; unfold w64; rewrite Z_to_bv_unsigned;
      unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); apply Z.mod_small; lia).

assert (AT : forall n v, In (n, v) [(10%nat, CInsp.inspect_result len bs); (3%nat, as_gp B); (4%nat, as_tp B); (8%nat, sp0); (9%nat, sp1); (2%nat, sp1);
    (20%nat, len); (21%nat, mode); (22%nat, prod); (23%nat, nch); (24%nat, fits0); (26%nat, olen); (27%nat, res);
    (32%nat, SHADOW_OFF); (40%nat, F); (41%nat, SH); (42%nat, ns mod 2 ^ 32); (43%nat, nch mod 2 ^ 32);
    (44%nat, ns mod 2 ^ 64); (45%nat, out);
    (46%nat, CInsp.inspect_byte bs 12); (47%nat, CInsp.inspect_byte bs 13); (48%nat, CInsp.inspect_byte bs 14);
    (49%nat, CInsp.inspect_byte bs 15); (50%nat, CInsp.inspect_byte bs 1490); (51%nat, CInsp.inspect_byte bs 1491)] -> ew E n = Z_to_bv 64 v).
{ intros n v Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <-|]); try contradiction;
  lazymatch goal with |- ew E ?n = _ =>
    first [ assert (Hn : (n < 32)%nat) by lia;
            let r := eval vm_compute in (Z_to_bv 5 (Z.of_nat n)) in rewrite (EREG n r eq_refl);
            first [eassumption | exact (dsd_spZ_reg regs sp1 Hsp)]
          | unfold E, DEND2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ _) ] end. }

assert (HLB : length bs = 1492%nat) by (rewrite Hbs, Heq; reflexivity).
assert (HRC : region_ok SEGS E (ms_mem (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 (BASE + 0x430)) mem (YK11.seg_rom SEGS)))) dsd_copy).
{ unfold dsd_copy, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val restrict ms_mem YK11.mkst].
  assert (U27 : bv_unsigned (ew E 27) = res)
    by (rewrite (EREG 27%nat 27%bv eq_refl), H27; unfold w64; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
        change (2 ^ Z.of_N 64) with (2 ^ 64); apply Z.mod_small; lia).
  rewrite U27. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil;
  lazymatch goal with |- YP09.chunk_ok _ _ _ _ {| c_off := ?o; YP09.c_val := CVal 1 (SOff ?n 0) |} =>
    let i := eval vm_compute in (Z.to_nat o) in
    destruct (dsd_byte_mem (w_H W) mem res bs i HG ltac:(rewrite HLB; lia)) as [HV HB];
    apply (chunk_ok_val decodesegsB0 E _ res o 1 (SOff n 0) (CInsp.inspect_byte bs i));
    [ apply dsd_den_atom; apply AT; cbn [In]; repeat (first [left; reflexivity | right])
    | cbn; lia | cbn; lia | exact HV ] end. }


assert (U27 : bv_unsigned (ew E 27) = res)
  by (rewrite (EREG 27%nat 27%bv eq_refl), H27; unfold w64; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
      change (2 ^ Z.of_N 64) with (2 ^ 64); apply Z.mod_small; lia).
assert (HD : all_disjoint E dsd_copy (ss_mem dsd_ss430)).
{ cbn [dsd_ss430 ss_mem all_disjoint]. split; [|exact I]. unfold extent_disjoint, dsd_copy, dsd_spill2.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. left. rewrite U27, E9. lia. }
pose proof (st_ok_pi_add_region (PI := PIB) E dsd_ss430 _ dsd_copy HS eq_refl HRC HD) as HS1.
clear HS HRC HD. rename HS1 into HS.
assert (EA : forall n, (n < 200)%nat -> ew E n = ew E n) by reflexivity.
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - ESTACK <= a < sp1 + 120) ->
               aview decodesegsB0 (w_H W) mem a = aview decodesegsB0 (w_H W) mem a) by reflexivity.
assert (PR : forall a, apresent (w_H W) mem a -> apresent (w_H W) mem a) by (intros a Hq; exact Hq).
change (w64 (decodeb_text + 1072)) with (Z_to_bv 64 (BASE + 0x430)).
pose proof (paj_run (SK := dec_B_sink_head) (PI := PIB) B LAWS) as RUN.
pose proof (paj_run_to (SK := dec_B_sink_head) (PI := PIB) B LAWS) as RUNTO.
pose proof (@paj_branch fx rc decodeb_listing PIB) as BR.
dsd_run RUN HS HJ SHOK W sp1 sp0 E E9 EA AT KR PR Hinr.
assert (U20 : U E (SOff 20 0) = len) by (apply U_atom; [rewrite (EREG 20%nat 20%bv eq_refl); exact H20 | lia]).
psrr_branch_tok RUN BR HS SHOK Bspan.
1: { exfalso. lazymatch goal with Hc : branch_taken _ _ _ = true |- _ =>
       rewrite branch_ne_U, U20, U_lit in Hc by lia; apply negb_true_iff, Z.eqb_neq in Hc; lia end. }
lazymatch goal with Hc : branch_taken _ _ _ = false |- _ => clear Hc end.

pose proof (dsd_byte_mem (w_H W) mem res bs 12 HG ltac:(rewrite HLB; lia)) as [_ B12].
pose proof (dsd_byte_mem (w_H W) mem res bs 13 HG ltac:(rewrite HLB; lia)) as [_ B13].
pose proof (dsd_byte_mem (w_H W) mem res bs 14 HG ltac:(rewrite HLB; lia)) as [_ B14].
pose proof (dsd_byte_mem (w_H W) mem res bs 15 HG ltac:(rewrite HLB; lia)) as [_ B15].
pose proof (dsd_byte_mem (w_H W) mem res bs 1490 HG ltac:(rewrite HLB; lia)) as [_ B1490].
pose proof (dsd_byte_mem (w_H W) mem res bs 1491 HG ltac:(rewrite HLB; lia)) as [_ B1491].
(* the header byte 12 (+0x474) *)
dsd_run RUN HS HJ SHOK W sp1 sp0 E E9 EA AT KR PR Hinr.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ lazymatch goal with Hc : branch_taken _ (sv_denot ?Ex _) _ = true |- _ =>
    rewrite branch_ne_U, (dsd_U_byte Ex 46 (CInsp.inspect_byte bs 12)), U_lit in Hc by dsd_U EA AT;
    apply negb_true_iff, Z.eqb_neq in Hc;
    pose proof (dsd_wf_false len bs ltac:(right; left; exact Hc)) as HWF end.
  dsd_nwf_tail RUN RUNTO BR HS HJ SHOK KR PR W sp1 sp0 E E9 EA AT HWF. }
lazymatch goal with Hc : branch_taken _ (sv_denot ?Ex _) _ = false |- _ =>
  rewrite branch_ne_U, (dsd_U_byte Ex 46 (CInsp.inspect_byte bs 12)), U_lit in Hc by dsd_U EA AT;
  apply negb_false_iff, Z.eqb_eq in Hc; rename Hc into Hb12 end.
(* the header byte 13 (+0x4a4) *)
dsd_run RUN HS HJ SHOK W sp1 sp0 E E9 EA AT KR PR Hinr.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ lazymatch goal with Hc : branch_taken _ (sv_denot ?Ex _) _ = true |- _ =>
    rewrite branch_ne_U, (dsd_U_byte Ex 47 (CInsp.inspect_byte bs 13)), U_lit in Hc by dsd_U EA AT;
    apply negb_true_iff, Z.eqb_neq in Hc;
    pose proof (dsd_wf_false len bs ltac:(right; right; left; exact Hc)) as HWF end.
  dsd_nwf_tail RUN RUNTO BR HS HJ SHOK KR PR W sp1 sp0 E E9 EA AT HWF. }
lazymatch goal with Hc : branch_taken _ (sv_denot ?Ex _) _ = false |- _ =>
  rewrite branch_ne_U, (dsd_U_byte Ex 47 (CInsp.inspect_byte bs 13)), U_lit in Hc by dsd_U EA AT;
  apply negb_false_iff, Z.eqb_eq in Hc; rename Hc into Hb13 end.
(* the trailer byte 1490 (+0x4d4) *)
dsd_run RUN HS HJ SHOK W sp1 sp0 E E9 EA AT KR PR Hinr.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ lazymatch goal with Hc : branch_taken _ (sv_denot ?Ex _) _ = true |- _ =>
    rewrite branch_ne_U, (dsd_U_byte Ex 50 (CInsp.inspect_byte bs 1490)), U_lit in Hc by dsd_U EA AT;
    apply negb_true_iff, Z.eqb_neq in Hc;
    pose proof (dsd_wf_false len bs ltac:(right; right; right; left; exact Hc)) as HWF end.
  dsd_nwf_tail RUN RUNTO BR HS HJ SHOK KR PR W sp1 sp0 E E9 EA AT HWF. }
lazymatch goal with Hc : branch_taken _ (sv_denot ?Ex _) _ = false |- _ =>
  rewrite branch_ne_U, (dsd_U_byte Ex 50 (CInsp.inspect_byte bs 1490)), U_lit in Hc by dsd_U EA AT;
  apply negb_false_iff, Z.eqb_eq in Hc; rename Hc into Hb1490 end.
(* the trailer byte 1491 (+0x4fc .. +0x504) and the inspect result's high half against s3 (+0x520) *)
dsd_run RUN HS HJ SHOK W sp1 sp0 E E9 EA AT KR PR Hinr.
pose proof (dsd_wf_last len bs Heq Hb12 Hb13 Hb1490) as HWL.
assert (US3 : forall Ex, (forall n, (n < 200)%nat -> ew Ex n = ew E n) ->
  U Ex (SAlu ALU_SLTU (SAlu ALU_ADD (SExt false 8 (SOff 51 0)) (SLit (-234))) (SLit 1)) =
  if CInsp.inspect_wf len bs then 1 else 0).
{ intros Ex EAx. rewrite HWL. apply (dsd_seqz Ex _ (CInsp.inspect_byte bs 1491) 234); [|lia|lia].
  apply dsd_U_byte; [dsd_U EAx AT | lia]. }
assert (UHI : forall Ex, (forall n, (n < 200)%nat -> ew Ex n = ew E n) ->
  U Ex (SAlu ALU_SRL (SOff 10 0) (SLit 32)) = if CInsp.inspect_wf len bs then 1 else 0).
{ intros Ex EAx. apply dsd_U_hi. apply U_atom; [dsd_U EAx AT|].
  unfold CInsp.inspect_result. pose proof (dsd_counter_bounds bs). destruct (CInsp.inspect_wf len bs); lia. }
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. lazymatch goal with Hc : branch_taken _ (sv_denot ?Ex _) _ = true |- _ =>
    rewrite branch_ne_U, (UHI Ex EA), (US3 Ex EA), Z.eqb_refl in Hc; discriminate Hc end. }
lazymatch goal with Hc : branch_taken _ _ _ = false |- _ => clear Hc end.
(* the `beqz` of +0x524 *)
dsd_run RUN HS HJ SHOK W sp1 sp0 E E9 EA AT KR PR Hinr.

psrr_branch_tok RUN BR HS SHOK Bspan.
{ lazymatch goal with Hc : branch_taken _ (sv_denot ?Ex _) _ = true |- _ =>
    rewrite branch_eq_U, (UHI Ex EA), U_lit in Hc by lia end.
  lazymatch goal with Hc : ((if CInsp.inspect_wf len bs then 1 else 0) =? 0) = true |- _ =>
    assert (HWF : CInsp.inspect_wf len bs = false) by (destruct (CInsp.inspect_wf len bs); [discriminate Hc | reflexivity]) end.
  dsd_run_to RUNTO HS HJ SHOK W sp1 sp0 E E9 EA AT KR PR Hinr 0x5a0.
  dsd_close5a0 HS HJ KR PR 1%nat EA AT E9 ltac:(apply dsd_denot_U; apply (US3 _ EA)). }
lazymatch goal with Hc : branch_taken _ (sv_denot ?Ex _) _ = false |- _ =>
  rewrite branch_eq_U, (UHI Ex EA), U_lit in Hc by lia end.
lazymatch goal with Hc : ((if CInsp.inspect_wf len bs then 1 else 0) =? 0) = false |- _ =>
  assert (HWT : CInsp.inspect_wf len bs = true) by (destruct (CInsp.inspect_wf len bs); [reflexivity | discriminate Hc]) end.

(* the well-formed path: the counter bytes 14 / 15 against the inspect result's low half (+0x590) *)
dsd_run RUN HS HJ SHOK W sp1 sp0 E E9 EA AT KR PR Hinr.
assert (UCNT : forall Ex, (forall n, (n < 200)%nat -> ew Ex n = ew E n) ->
  U Ex (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SOff 49 0)) (SLit 8)) (SExt false 8 (SOff 48 0))) = CInsp.inspect_counter bs).
{ intros Ex EAx. unfold CInsp.inspect_counter.
  apply dsd_U_pair; [apply dsd_U_byte; [dsd_U EAx AT | lia] | apply dsd_U_byte; [dsd_U EAx AT | lia] | lia | lia]. }
assert (ULO : forall Ex, (forall n, (n < 200)%nat -> ew Ex n = ew E n) ->
  U Ex (SAlu ALU_SRL (SAlu ALU_SLL (SOff 10 0) (SLit 48)) (SLit 48)) = CInsp.inspect_counter bs).
{ intros Ex EAx. pose proof (dsd_counter_bounds bs) as C.
  rewrite (dsd_U_lo16 Ex _ (CInsp.inspect_result len bs)).
  - unfold CInsp.inspect_result. rewrite HWT.
    replace (2 ^ 32 + CInsp.inspect_counter bs) with (CInsp.inspect_counter bs + 65536 * 2 ^ 16) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - apply U_atom; [dsd_U EAx AT|]. unfold CInsp.inspect_result. rewrite HWT. lia.
  - unfold CInsp.inspect_result. rewrite HWT. lia. }
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. lazymatch goal with Hc : branch_taken _ (sv_denot ?Ex _) _ = true |- _ =>
    rewrite branch_ne_U, (UCNT Ex EA), (ULO Ex EA), Z.eqb_refl in Hc; discriminate Hc end. }
lazymatch goal with Hc : branch_taken _ _ _ = false |- _ => clear Hc end.
(* to the call of reac_frame_counter (+0x598) *)
paj_run_tok RUN HS HJ SHOK Bspan; try first [dsd_obl W HJ Hinr EA AT | dsd_awr sp1 sp0 E9].
dsd_fold W sp1 E9 KR PR.
repeat rewrite wvb_collapse in HJ.
lazymatch goal with HEIx : img_env _ _ ?Ex, HS : st_ok _ ?Ex _ _ |- _ => rename HEIx into HEIc end.
dsd_env E EA.
reg_at HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 0x59c)) CRA ltac:(apply codeptr_val; exact HEIc).
reg_at HS (2%bv : bv 5) (w64 sp1) CSP ltac:(dsd_atom EA AT).
reg_at HS (3%bv : bv 5) (w64 (as_gp B)) CGP ltac:(dsd_atom EA AT).
reg_at HS (4%bv : bv 5) (w64 (as_tp B)) CTP ltac:(dsd_atom EA AT).
reg_at HS (10%bv : bv 5) (w64 res) CA0 ltac:(dsd_atom EA AT).
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msx) |- _ =>
  assert (CspZ : spZ (ms_regs msx) = sp1)
    by (unfold spZ; rewrite CSP; unfold w64; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
        change (2 ^ Z.of_N 64) with (2 ^ 64); apply Z.mod_small; lia);
  pmkst HS;
  eapply SRr_bind;
  [ eapply (dec_leafb_counter B LAWS HC HLEAF W (ms_regs msx) (ms_mem msx) STK sp0 FP ly S W0 mem0 md0 own
            lyc Sc _ k (sp1 - sp0) res len bs HJ);
    [ rewrite CspZ; lia | exact (dsd_mod16_sub sp1 sp0 Hsp1m Hsp0al) | lia | unfold ESTACK; lia
    | rewrite CRA; apply (ret_ok_codeptr_v (PI := PIB)); [lia | reflexivity]
    | exact CGP | exact CTP | exact CA0 | exact Hinr | lia | exact Hbs | ];
    apply (dsd_garr8_keep (w_H W) mem (ms_mem msx) res _); [|exact HG];
    intros i Hi; rewrite length_map, Hbs, Heq in Hi; apply KR; [lia | unfold ESTACK; lia]
  | ];
  cbv beta; intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HR2 & HK2 & HPr2 & _);
  rewrite CRA;
  assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - ESTACK <= a < sp1) ->
      aview decodesegsB0 (w_H W) mem2 a = aview decodesegsB0 (w_H W) (ms_mem msx) a)
    by (intros a Ha Hn; apply HK2; [exact Ha | rewrite CspZ; exact Hn | intros HW; inversion HW])
end.
assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - ESTACK <= a < sp1 + 120) ->
    aview decodesegsB0 (w_H W) mem2 a = aview decodesegsB0 (w_H W) mem a)
  by (intros a Ha Hn; rewrite (KC a Ha ltac:(lia)); exact (KR a Ha Hn)).
assert (PR2 : forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) by (intros a Hq; apply HPr2; apply PR; exact Hq).
clear KR PR. rename KR2 into KR. rename PR2 into PR.
(* back at +0x59c: the copy and the spill area kept by the call *)
jafter_call_keep_pi HS 200%nat regs2 (mrestrict (w_H W) mem2) HP2 [0%nat; 1%nat] HS2.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
lazymatch type of HS2 with Forall (region_kept _ ?Ex (ms_mem (restrict _ ?msx)) _) ?rs -> _ =>
  assert (RK : Forall (region_kept SEGS Ex (ms_mem (restrict (w_H W) msx)) (mrestrict (w_H W) mem2)) rs);
  [ cbn [ms_mem restrict];
    repeat apply Forall_cons; try apply Forall_nil; split;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?EA by lia; rewrite ?U27, ?E9;
    [ intros a Ha; apply dsd_mbyte_keep; apply KC; [lia | unfold ESTACK; lia]
    | intros a Ha; lia
    | intros a Ha; apply dsd_mbyte_keep; apply KC; [lia | unfold ESTACK; lia]
    | intros a Ha _; apply (apresent_writable decodesegsB0); apply Hpres2; lia ]
  | ] end.
specialize (HS2 RK). clear RK. rewrite <- restrict_mkst_fx in HS2.
clear HS HJ SHOK. rename HS2 into HS. rename HJ2 into HJ.
lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
  assert (HEIc2 : img_env VAL A_LIM Ec) by (apply (img_env_havoc (PI := PIB)); [exact HEIc | cbv; lia]);
  assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) Ec (mrestrict (w_H W) mem2)) by constructor;
  assert (EA2 : forall n, (n < 200)%nat -> ew Ec n = ew E n) by (intros nn Hnn; rewrite ew_havoc_old by lia; apply EA; lia);
  assert (A204 : ew Ec 204 = Z_to_bv 64 (CInsp.inspect_counter bs))
    by (change 204%nat with (200 + 4)%nat; rewrite (ew_havoc_new _ _ _ 4 (Z_to_bv 64 0)) by (cbn; lia);
        cbn [map CLOB nth]; rewrite HR2; reflexivity)
end.
clear EA. rename EA2 into EA.
(* reac_frame_counter's answer against the same 16-bit value (+0x59c) *)
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. lazymatch goal with Hc : branch_taken _ (sv_denot ?Ex _) _ = true |- _ =>
    rewrite branch_ne_U, (UCNT Ex EA),
      (U_atom Ex 204 (CInsp.inspect_counter bs) A204 ltac:(pose proof (dsd_counter_bounds bs); lia)), Z.eqb_refl in Hc;
    discriminate Hc end. }
lazymatch goal with Hc : branch_taken _ _ _ = false |- _ => clear Hc end.
dsd_run_to RUNTO HS HJ SHOK W sp1 sp0 E E9 EA AT KR PR Hinr 0x5a0.
dsd_close5a0 HS HJ KR PR 1%nat EA AT E9 ltac:(apply dsd_denot_U; apply (US3 _ EA)).
Qed.


(* ------------------------------------------------------------------ *)
(* 5. +0x5a0 .. +0x5c8: the fits flag, the fill and reac_decode        *)
(* ------------------------------------------------------------------ *)

(* What the walk knows at +0x5cc, the return of reac_decode: the registers llvm_b_st_5cc names, the spill slots,
   the facts of +0x430 the stage kept, the buffer (the decoder's output when the decode succeeds, the 0xa5 fill
   when it does not), and against memS every byte outside the stack windows, the spill area and the buffer
   kept, every present byte still present. *)
Definition dsd_at5cc (W : world decodesegsB0)
    (STK sp0 : Z) (FP : list (Z * Z)) ly S (W0 : world decodesegsB0) mem0 md0 own lyc Sc (k : Z)
    (memS : word -> option byte) (sp1 F SH res out len mode nch ns olen prod fits0 : Z) (bs : list byte)
    : world decodesegsB0 -> config -> Prop :=
  fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
    c2 = mkCfg (YK11.mkst regs2 (w64 (decodeb_text + 0x5cc)) mem2 (YK11.seg_rom decodesegsB0)) md2 /\
    @ajournal rc dec_B_sink_head decodesegsB0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
    YK11.getr regs2 3 = w64 (as_gp B) /\ YK11.getr regs2 4 = w64 (as_tp B) /\
    YK11.getr regs2 8 = w64 sp0 /\ YK11.getr regs2 9 = w64 sp1 /\ spZ regs2 = sp1 /\
    YK11.getr regs2 10 = w64 (if CDec.decode_ok len bs nch ns then ns else -1) /\
    YK11.getr regs2 18 = w64 (if prod <? 481 then 1 else 0) /\
    YK11.getr regs2 19 = w64 (if CInsp.inspect_wf len bs then 1 else 0) /\
    YK11.getr regs2 20 = w64 len /\ YK11.getr regs2 21 = w64 mode /\ YK11.getr regs2 22 = w64 out /\
    YK11.getr regs2 23 = w64 nch /\ YK11.getr regs2 24 = w64 fits0 /\
    YK11.getr regs2 26 = w64 olen /\ YK11.getr regs2 27 = w64 res /\
    rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 0) = Some F /\
    rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 8) = Some SH /\
    rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 16) = Some F /\
    rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 24) = Some len /\
    rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 32) = Some SHADOW_OFF /\
    rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 40) = Some res /\
    rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 56) = Some (ns mod 2 ^ 32) /\
    rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 64) = Some (nch mod 2 ^ 32) /\
    rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 72) = Some (ns mod 2 ^ 64) /\
    rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 88) = Some out /\
    rdword (aview decodesegsB0 (w_H W) mem2) (sp1 + 112) = Some F /\
    (forall i, 0 <= i < 4 -> aview decodesegsB0 (w_H W) mem2 (SH + i) = Some DEC_SH_LEFT) /\
    aview decodesegsB0 (w_H W) mem2 (SH + 4) = Some 0 /\
    aview decodesegsB0 (w_H W) mem2 (SH + 5) = Some 4 /\
    (forall i, 6 <= i < 8 -> aview decodesegsB0 (w_H W) mem2 (SH + i) = Some DEC_SH_RIGHT) /\
    garr8 decodesegsB0 (mrestrict (w_H W) mem2) res (map (fun b : byte => bv_unsigned b) bs) /\
    val_mem decodesegsB0 (mrestrict (w_H W) mem2) (mode + 4) 4%nat (nch mod 2 ^ 32) /\
    val_mem decodesegsB0 (mrestrict (w_H W) mem2) (mode + 8) 4%nat (ns mod 2 ^ 32) /\
    (CDec.decode_ok len bs nch ns = true ->
       garr8 decodesegsB0 (mrestrict (w_H W) mem2) out
         (map (fun b : byte => bv_unsigned b) (CDec.braid_out bs nch ns))) /\
    (CDec.decode_ok len bs nch ns = false ->
       forall i, 0 <= i < olen -> aview decodesegsB0 (w_H W) mem2 (out + i) = Some DEC_FILL) /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - ESTACK <= a < sp1 + 120) -> ~ (out <= a < out + olen) ->
       aview decodesegsB0 (w_H W) mem2 a = aview decodesegsB0 (w_H W) memS a) /\
    (forall a, apresent (w_H W) memS a -> apresent (w_H W) mem2 a).

(* The spill area from +0x5a0 on: no store of stage 3 touches it, so it is a read-only region, and it now holds the
   length (24) and the copy (40) as well. *)
Definition dsd_spill3 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 120 0 0
    [YP09.mkChunk 0 (CVal 8 (SOff 40 0)); YP09.mkChunk 8 (CVal 8 (SOff 41 0));
     YP09.mkChunk 16 (CVal 8 (SOff 40 0)); YP09.mkChunk 24 (CVal 8 (SOff 20 0));
     YP09.mkChunk 32 (CVal 8 (SOff 32 0)); YP09.mkChunk 40 (CVal 8 (SOff 27 0));
     YP09.mkChunk 56 (CVal 8 (SOff 42 0)); YP09.mkChunk 64 (CVal 8 (SOff 43 0));
     YP09.mkChunk 72 (CVal 8 (SOff 44 0)); YP09.mkChunk 88 (CVal 8 (SOff 45 0));
     YP09.mkChunk 112 (CVal 8 (SOff 40 0))].

(* lib/B/Prog/LLVMFuzzerTestOneInput_segC.v's st_ok_pi_submemB, at this image's listing: drop regions of a state. *)
Lemma dsd_submem : forall E ss ms rs, st_ok_pi SEGS VAL E ss ms -> submem rs (ss_mem ss) -> regions_wf rs = true ->
  st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (ss_regs ss) rs (ss_resv ss) (ss_facts ss)) ms.
Proof. intros E ss ms rs HS Hs Hwf. destruct ss as [pc0 sr0 fr0 sm0 rv0 fs0]. exact (st_ok_submem SEGS E _ ms rs HS Hs Hwf). Qed.

(* +0x5a0 .. +0x5c8: s2 := (prod <u 481), s6 := the buffer, __asan_memset(buffer, 0xa5, olen) through the kit's
   aj_intrin_atS, and reac_decode(copy, length, mode, buffer) through the leaf bridge; the buffer is a block of the
   segment's own (malloc #2), so both callees may write it, and nothing else of the walk's state is in it. *)
Lemma dsd_stage3 :
  dec_crt_cells B ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc decodesegsB0 B OSet (decodeb_sigma DB___asan_memset)) ->
  (forall fx' : YK11.FPState, @dec_leaf_wr_at rc B (@LDecode.dec_reac_decode_cg) fx') ->
  forall (W : world decodesegsB0) regsT STK sp0 FP ly S W0 mem0 md0 own lyc Sc k memS
         (sp1 F SH res out len mode nch ns olen prod fits0 : Z) (bs : list byte) c,
  sp0 - 240 <= sp1 -> sp1 <= sp0 - 224 -> sp1 mod 32 = 0 -> 4336 <= STK ->
  ablocks B lyc Sc = ablocks B ly S ++ [(res, len)] ++ [(out, olen)] ->
  0 <= len < 2 ^ 64 -> length bs = Z.to_nat len ->
  -128 <= nch <= 127 -> -128 <= ns <= 127 -> olen = dec_b_olen nch ns -> 0 <= prod < 2 ^ 64 ->
  0 <= F < 2 ^ 64 -> 0 <= SH < 2 ^ 64 ->
  4096 <= SH -> SH + 8 <= alloc_ceiling -> 4096 <= mode -> mode + 12 <= alloc_ceiling ->
  in_app mode 12 -> mode mod 4 = 0 -> (SH + 8 <= out \/ out + olen <= SH) -> (mode + 12 <= out \/ out + olen <= mode) ->
  (forall memx mdx, AR decodesegsB0 B lyc Sc W memx mdx ->
     aview decodesegsB0 (w_H W) memx (SH + 4) = Some 0 -> aview decodesegsB0 (w_H W) memx (SH + 5) = Some 4 ->
     range_addressable (aview decodesegsB0 (w_H W) memx) SHADOW_OFF (mode + 4) 8) ->
  dsd_at5a0 W regsT STK sp0 FP ly S W0 mem0 md0 own lyc Sc k memS
    sp1 F SH res out len mode nch ns olen prod fits0 bs W c ->
  SRr decodesegsB0 W c
    (dsd_at5cc W STK sp0 FP ly S W0 mem0 md0 own lyc Sc k memS
       sp1 F SH res out len mode nch ns olen prod fits0 bs).

Proof.
intros HC AMEMSET ADEC W regsT STK sp0 FP ly S W0 mem0 md0 own lyc Sc k memS sp1 F SH res out len mode nch ns olen prod fits0 bs c
  Hsp1a Hsp1b Hsp1m HSTK Hbl Hlen Hbs Hnch Hns Holen Hprod HFrng HSHrng HSHlo HSHhi Hmlo Hmhi Happ Hm4 HSHo HMO MADDR
  (_ & regs & mem & md & -> & HJ & Hgp & Htp & H8 & H9 & Hsp & H19 & H20 & H21 & H22 & H23 & H24 & H26 & H27
   & R0 & R8 & R16 & R24 & R32 & R40 & R56 & R64 & R72 & R88 & R112 & Fsh0 & Fsh4 & Fsh5 & Fsh6 & HG & Hmv1 & Hmv2 & KS & PS).
assert (Hinr : In (res, len) (ablocks B lyc Sc)) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
assert (Hino : In (out, olen) (ablocks B lyc Sc)) by (rewrite Hbl; apply in_or_app; right; right; left; reflexivity).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof alloc_ceiling_val as HCEIL.
destruct (al_blocks _ _ LAWS _ _ _ _ _ res len HAR Hinr) as (Hral & Hr4096 & Hrceil & Hrapp & Hrpres & _ & Hrmr).
destruct (al_blocks _ _ LAWS _ _ _ _ _ out olen HAR Hino) as (Hoal & Ho4096 & Hoceil & Hoapp & Hopres & _ & Homr).
pose proof (req_size_pos len ltac:(lia)) as [Hqr1 Hqr2].
pose proof (req_size_pos olen ltac:(lia)) as [Hqo1 Hqo2].
pose proof (Z.mod_pos_bound ns (2 ^ 32) ltac:(lia)) as Mns32.
pose proof (Z.mod_pos_bound nch (2 ^ 32) ltac:(lia)) as Mnch32.
pose proof (Z.mod_pos_bound ns (2 ^ 64) ltac:(lia)) as Mns64.
pose proof (dsd_st_at 0x5a0 W regs mem sp1 out res F SH (ns mod 2 ^ 32) (nch mod 2 ^ 32) (ns mod 2 ^ 64) []
  H9 ltac:(lia) ltac:(lia) Hsp1m ltac:(lia) ltac:(lia) Hoal H27 ltac:(lia) ltac:(lia) Hral
  HFrng HSHrng ltac:(lia) ltac:(lia) ltac:(lia)
  R0 R8 R16 R32 R56 R64 R72 R88 R112 ltac:(intros o Ho; apply Hpres; lia)) as HS.
set (E := DEND2 regs F SH (ns mod 2 ^ 32) (nch mod 2 ^ 32) (ns mod 2 ^ 64) out []) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, DEND2; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H W) mem)) by constructor.
assert (EREG : forall kk (r : bv 5), Z.of_nat kk = bv_unsigned r -> ew E kk = YK11.getr regs r).
{ intros kk r Hk. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
  unfold E, DEND2. rewrite (Eimg_low (PI := PIB) _ kk ltac:(unfold A_TEXT; lia)).
  exact (ew_Ereg_nat regs _ kk r Hk). }
assert (E9 : bv_unsigned (ew E 9) = sp1)
  by (rewrite (EREG 9%nat 9%bv eq_refl), H9; unfold w64; rewrite Z_to_bv_unsigned;
      unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); apply Z.mod_small; lia).
assert (AT : forall n v, In (n, v) [(3%nat, as_gp B); (4%nat, as_tp B); (8%nat, sp0); (9%nat, sp1); (2%nat, sp1);
    (19%nat, if CInsp.inspect_wf len bs then 1 else 0);
    (20%nat, len); (21%nat, mode); (22%nat, prod); (23%nat, nch); (24%nat, fits0); (26%nat, olen); (27%nat, res);
    (32%nat, SHADOW_OFF); (40%nat, F); (41%nat, SH); (42%nat, ns mod 2 ^ 32); (43%nat, nch mod 2 ^ 32);
    (44%nat, ns mod 2 ^ 64); (45%nat, out)] -> ew E n = Z_to_bv 64 v).
{ intros n v Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <-|]); try contradiction;
  lazymatch goal with |- ew E ?n = _ =>
    first [ assert (Hn : (n < 32)%nat) by lia;
            let r := eval vm_compute in (Z_to_bv 5 (Z.of_nat n)) in rewrite (EREG n r eq_refl);
            first [eassumption | exact (dsd_spZ_reg regs sp1 Hsp)]
          | unfold E, DEND2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ _) ] end. }
assert (U27 : bv_unsigned (ew E 27) = res)
  by (rewrite (EREG 27%nat 27%bv eq_refl), H27; unfold w64; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
      change (2 ^ Z.of_N 64) with (2 ^ 64); apply Z.mod_small; lia).
pose proof (dsd_submem E _ _ [] HS ltac:(constructor) eq_refl) as HS1. clear HS.
assert (HR3 : region_ok SEGS E (mrestrict (w_H W) mem) dsd_spill3).
{ unfold dsd_spill3, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil;
  lazymatch goal with |- YP09.chunk_ok _ _ _ _ {| c_off := ?o; YP09.c_val := CVal 8 (SOff ?n 0) |} =>
  lazymatch goal with Rh : rdword _ (sp1 + o) = Some ?v |- _ =>
    apply (chunk_ok_val decodesegsB0 E _ sp1 o 8 (SOff n 0) v);
    [ apply dsd_den_atom; apply AT; cbn [In]; repeat (first [left; reflexivity | right])
    | cbn; unfold SHADOW_OFF; lia | cbn; lia | exact (val_mem_of_rdword decodesegsB0 _ _ _ _ Rh) ] end end. }
pose proof (st_ok_pi_add_region (PI := PIB) E _ _ dsd_spill3 HS1 eq_refl HR3 I) as HS. clear HS1 HR3.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
assert (EA : forall n, (n < 200)%nat -> ew E n = ew E n) by reflexivity.
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - ESTACK <= a < sp1 + 120) ->
               aview decodesegsB0 (w_H W) mem a = aview decodesegsB0 (w_H W) mem a) by reflexivity.
assert (PR : forall a, apresent (w_H W) mem a -> apresent (w_H W) mem a) by (intros a Hq; exact Hq).
change (w64 (decodeb_text + 1440)) with (Z_to_bv 64 (BASE + 0x5a0)).
pose proof (paj_run (SK := dec_B_sink_head) (PI := PIB) B LAWS) as RUN.
(* +0x5a0 .. +0x5b0 and the call of __asan_memset (+0x5b4) *)
paj_run_tok RUN HS HJ SHOK Bspan; try first [dsd_obl W HJ Hinr EA AT | dsd_awr sp1 sp0 E9].
dsd_fold W sp1 E9 KR PR. dsd_env E EA.
repeat rewrite wvb_collapse in HJ.

lazymatch goal with HEIx : img_env _ _ ?Ex, HS : st_ok _ ?Ex _ _ |- _ => rename HEIx into HEIc end.
reg_at HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 0x5b8)) MRA ltac:(apply codeptr_val; exact HEIc).
reg_at HS (2%bv : bv 5) (w64 sp1) MSP ltac:(dsd_atom EA AT).
reg_at HS (3%bv : bv 5) (w64 (as_gp B)) MGP ltac:(dsd_atom EA AT).
reg_at HS (4%bv : bv 5) (w64 (as_tp B)) MTP ltac:(dsd_atom EA AT).
reg_at HS (10%bv : bv 5) (w64 out) MA0 ltac:(dsd_atom EA AT).
reg_at HS (11%bv : bv 5) (w64 165) MA1 ltac:(reflexivity).
reg_at HS (12%bv : bv 5) (w64 olen) MA2 ltac:(dsd_atom EA AT).
pose proof (dsd_olen_bounds nch ns Hnch Hns) as Holb. rewrite <- Holen in Holb.
assert (MspZ : spZ (ms_regs ms) = sp1)
  by (unfold spZ; rewrite MSP; unfold w64; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
      change (2 ^ Z.of_N 64) with (2 ^ 64); apply Z.mod_small; lia).
pmkst HS.
eapply SRr_bind.
{ eapply (aj_intrin_atS decodesegsB0 B LAWS decodeb_segs_low OSet (decodeb_sigma DB___asan_memset) (AMEMSET fx)
    W (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k out 165 olen (sp1 - sp0)
    (Z_to_bv 64 (BASE + 0x5b8)) HJ MA0 MA1 MA2).

  - lia.
  - lia.
  - lia.
  - rewrite MspZ. lia.
  - exact (dsd_mod16_sub sp1 sp0 Hsp1m Hsp0al).
  - lia.
  - unfold ESTACK. lia.
  - exact MGP.
  - exact MTP.
  - exact MRA.
  - apply (ret_ok_codeptr_v (PI := PIB)); [lia | reflexivity].
  - intros a Ha. split.
    + apply (dec_leafb_awr_new B LAWS STK sp0 FP ly S lyc Sc W _ _ own [(res, len); (out, olen)] out olen a (proj1 HJ) Hbl);
        [right; left; reflexivity | lia].
    + unfold ESTACK. lia.
  - eapply (amem_range_of_block decodesegsB0 B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hino); lia.
  - eapply (range_addressable_of_block decodesegsB0 B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hino); lia.
  - intros Hl0. eapply (shadow_hull_vis_of_block decodesegsB0 B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hino); lia.
  - exact I. }

cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HR2 & HFILL & HKM & HPM & _).
assert (KR3 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - ESTACK <= a < sp1 + 120) -> ~ (out <= a < out + olen) ->
    aview decodesegsB0 (w_H W) mem2 a = aview decodesegsB0 (w_H W) mem a)
  by (intros a Ha Hn Ho; rewrite (HKM a Ha Ho ltac:(unfold ESTACK in *; lia)); exact (KR a Ha Hn)).
assert (PR3 : forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) by (intros a Hq; apply HPM; apply PR; exact Hq).
assert (FILL : forall i, 0 <= i < olen -> aview decodesegsB0 (w_H W) mem2 (out + i) = Some DEC_FILL)
  by (intros i Hi; rewrite (HFILL i Hi); reflexivity).
clear HFILL.
jafter_call_keep_pi HS 200%nat regs2 (mrestrict (w_H W) mem2) HP2 [0%nat] HS2.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
lazymatch type of HS2 with Forall (region_kept _ ?Ex (ms_mem (restrict _ ?msx)) _) ?rs -> _ =>
  assert (RK : Forall (region_kept SEGS Ex (ms_mem (restrict (w_H W) msx)) (mrestrict (w_H W) mem2)) rs);
  [ cbn [ms_mem restrict];
    repeat apply Forall_cons; try apply Forall_nil; split;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?EA by lia; rewrite ?E9;
    [ intros a Ha; apply dsd_mbyte_keep; apply HKM; [lia | lia | unfold ESTACK; lia]
    | intros a Ha _; lia ]
  | ] end.
specialize (HS2 RK). clear RK. rewrite <- restrict_mkst_fx in HS2.
clear HS HJ SHOK. rename HS2 into HS. rename HJ2 into HJ.
lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
  assert (HEIc2 : img_env VAL A_LIM Ec) by (apply (img_env_havoc (PI := PIB)); [exact HEIc | cbv; lia]);
  assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) Ec (mrestrict (w_H W) mem2)) by constructor end.
dsd_env E EA.

clear KR PR.
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - ESTACK <= a < sp1 + 120) ->
               aview decodesegsB0 (w_H W) mem2 a = aview decodesegsB0 (w_H W) mem2 a) by reflexivity.
assert (PR : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) mem2 a) by (intros a Hq; exact Hq).
(* +0x5b8 .. +0x5c4 and the call of reac_decode (+0x5c8) *)
paj_run_tok RUN HS HJ SHOK Bspan; try first [dsd_obl W HJ Hinr EA AT | dsd_awr sp1 sp0 E9].
dsd_fold W sp1 E9 KR PR. dsd_env E EA.
repeat rewrite wvb_collapse in HJ.

lazymatch goal with HEIx : img_env _ _ ?Ex, HS : st_ok _ ?Ex _ _ |- _ => rename HEIx into HEId end.
lazymatch goal with HS : st_ok _ ?Ex ?ssx (restrict _ ?msx) |- _ =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  assert (HR0 : region_ok SEGS Ex (ms_mem (restrict (w_H W) msx)) r0)
    by (apply (st_ok_region_nth Ex ssx (restrict (w_H W) msx) 0 r0 HS); vm_compute; reflexivity);
  assert (E9' : bv_unsigned (ew Ex 9) = sp1) by (rewrite ?EA by lia; exact E9) end.
cbn [ms_mem restrict] in HR0.
dsd_slot W sp1 HR0 E9' EA AT ms0 0 F T0.
dsd_slot W sp1 HR0 E9' EA AT ms0 8 SH T8.
dsd_slot W sp1 HR0 E9' EA AT ms0 16 F T16.
dsd_slot W sp1 HR0 E9' EA AT ms0 24 len T24.
dsd_slot W sp1 HR0 E9' EA AT ms0 32 SHADOW_OFF T32.
dsd_slot W sp1 HR0 E9' EA AT ms0 40 res T40.
dsd_slot W sp1 HR0 E9' EA AT ms0 56 (ns mod 2 ^ 32) T56.
dsd_slot W sp1 HR0 E9' EA AT ms0 64 (nch mod 2 ^ 32) T64.
dsd_slot W sp1 HR0 E9' EA AT ms0 72 (ns mod 2 ^ 64) T72.
dsd_slot W sp1 HR0 E9' EA AT ms0 88 out T88.
dsd_slot W sp1 HR0 E9' EA AT ms0 112 F T112.
clear HR0.
reg_at HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 0x5cc)) DRA ltac:(apply codeptr_val; exact HEId).
reg_at HS (2%bv : bv 5) (w64 sp1) DSP ltac:(dsd_atom EA AT).
reg_at HS (3%bv : bv 5) (w64 (as_gp B)) DGP ltac:(dsd_atom EA AT).
reg_at HS (4%bv : bv 5) (w64 (as_tp B)) DTP ltac:(dsd_atom EA AT).
reg_at HS (8%bv : bv 5) (w64 sp0) D8 ltac:(dsd_atom EA AT).
reg_at HS (9%bv : bv 5) (w64 sp1) D9 ltac:(dsd_atom EA AT).
reg_at HS (10%bv : bv 5) (w64 res) DA0 ltac:(dsd_atom EA AT).
reg_at HS (11%bv : bv 5) (w64 len) DA1 ltac:(dsd_atom EA AT).
reg_at HS (12%bv : bv 5) (w64 mode) DA2 ltac:(dsd_atom EA AT).
reg_at HS (13%bv : bv 5) (w64 out) DA3 ltac:(dsd_atom EA AT).
reg_at HS (18%bv : bv 5) (w64 (if prod <? 481 then 1 else 0)) D18
  ltac:(apply dsd_denot_U; rewrite U_SAlu, (U_atom _ 22 prod), U_lit by (first [dsd_U EA AT | lia]);
        cbn [zalu_raw]; destruct (prod <? 481); reflexivity).
reg_at HS (19%bv : bv 5) (w64 (if CInsp.inspect_wf len bs then 1 else 0)) D19 ltac:(dsd_atom EA AT).
reg_at HS (20%bv : bv 5) (w64 len) D20 ltac:(dsd_atom EA AT).
reg_at HS (21%bv : bv 5) (w64 mode) D21 ltac:(dsd_atom EA AT).
reg_at HS (22%bv : bv 5) (w64 out) D22 ltac:(dsd_atom EA AT).
reg_at HS (23%bv : bv 5) (w64 nch) D23 ltac:(dsd_atom EA AT).
reg_at HS (24%bv : bv 5) (w64 fits0) D24 ltac:(dsd_atom EA AT).
reg_at HS (26%bv : bv 5) (w64 olen) D26 ltac:(dsd_atom EA AT).
reg_at HS (27%bv : bv 5) (w64 res) D27 ltac:(dsd_atom EA AT).
assert (DspZ : spZ (ms_regs ms0) = sp1)
  by (unfold spZ; rewrite DSP; unfold w64; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
      change (2 ^ Z.of_N 64) with (2 ^ 64); apply Z.mod_small; lia).

assert (KD : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - ESTACK <= a < sp1 + 120) -> ~ (out <= a < out + olen) ->
    aview decodesegsB0 (w_H W) (ms_mem ms0) a = aview decodesegsB0 (w_H W) mem a)
  by (intros a Ha Hn Ho; rewrite (KR a Ha Hn); exact (KR3 a Ha Hn Ho)).
assert (PD : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms0) a) by (intros a Hq; apply PR; apply PR3; exact Hq).
assert (KDL : forall a, 0 <= a < sp1 - 4096 -> ~ (out <= a < out + olen) ->
    aview decodesegsB0 (w_H W) (ms_mem ms0) a = aview decodesegsB0 (w_H W) mem a)
  by (intros a Ha Ho; apply KD; [unfold ESTACK in *; lia | unfold ESTACK in *; lia | exact Ho]).
pose proof (sep_blocks_pos decodesegsB0 B LAWS _ _ _ _ _ (res, len) (out, olen) (ablocks B ly S) [] [] HAR Hbl) as Hro.
unfold zdisjoint, block_rng in Hro. cbn [fst snd] in Hro.
assert (Hnw : forall a, res <= a < res + len -> ~ (out <= a < out + olen)) by (intros a Ha Hb; lia).
pmkst HS.
eapply SRr_bind.
{ eapply (dec_leafb_decode B LAWS HC ADEC W (ms_regs ms0) (ms_mem ms0) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k
          (sp1 - sp0) res len mode out nch ns olen bs HJ).
  all: cycle 16.
  - apply (dsd_garr8_keep (w_H W) mem (ms_mem ms0) res _); [|exact HG].
    intros i Hi. rewrite length_map, Hbs in Hi. rewrite Z2Nat.id in Hi by lia. apply KDL; [lia | apply Hnw; lia].
  - exact Hino.
  - intros Hq. subst out. lia.
  - intros Hok. rewrite Holen, (dsd_decode_olen len bs nch ns Hok). lia.
  - intros Hok a Ha. assert (Hol : olen = 3 * nch * ns) by (rewrite Holen; exact (dsd_decode_olen len bs nch ns Hok)).
    apply (dec_leafb_awr_new B LAWS STK sp0 FP ly S lyc Sc W _ _ own [(res, len); (out, olen)] out olen a (proj1 HJ) Hbl);
      [right; left; reflexivity | lia].
  - exact Happ.
  - exact Hm4.
  - intros a Ha. destruct (Z.lt_ge_cases a (mode + 8)).
    + apply (dsd_vis_of_valmem W mem (mode + 4) 4 (nch mod 2 ^ 32) Hmv1). cbn. lia.
    + apply (dsd_vis_of_valmem W mem (mode + 8) 4 (ns mod 2 ^ 32) Hmv2). cbn. lia.
  - apply (MADDR _ _ (proj1 HJ)).
    + rewrite (KDL (SH + 4) ltac:(lia) ltac:(lia)). exact Fsh4.
    + rewrite (KDL (SH + 5) ltac:(lia) ltac:(lia)). exact Fsh5.
  - apply (dsd_valmem_keep (w_H W) mem (ms_mem ms0) (mode + 4) 4 _); [|exact Hmv1].
    intros i Hi. apply KDL; [cbn in Hi; lia | cbn in Hi; lia].
  - apply (dsd_valmem_keep (w_H W) mem (ms_mem ms0) (mode + 8) 4 _); [|exact Hmv2].
    intros i Hi. apply KDL; [cbn in Hi; lia | cbn in Hi; lia].
  - rewrite DspZ. lia.
  - exact (dsd_mod16_sub sp1 sp0 Hsp1m Hsp0al).
  - lia.
  - unfold ESTACK. lia.
  - rewrite DRA. apply (ret_ok_codeptr_v (PI := PIB)); [lia | reflexivity].
  - exact DGP.
  - exact DTP.
  - exact DA0.
  - exact DA1.
  - exact DA2.
  - exact DA3.
  - exact Hlen.
  - exact Hnch.
  - exact Hns.
  - exact Hinr.
  - intros Hl. rewrite Hbs, Hl. reflexivity.
}

cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HR3 & HK3 & HPr3 & HX).
rewrite DRA.
assert (KF0 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - ESTACK <= a < sp1) ->
    ~ LCK.in_wr (if CDec.decode_ok len bs nch ns then [(out, out + 3 * nch * ns)] else []) a ->
    aview decodesegsB0 (w_H W) mem3 a = aview decodesegsB0 (w_H W) (ms_mem ms0) a)
  by (intros a Ha Hs Hw; apply HK3; [exact Ha | rewrite DspZ; exact Hs | exact Hw]).
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - ESTACK <= a < sp1) -> ~ (out <= a < out + olen) ->
    aview decodesegsB0 (w_H W) mem3 a = aview decodesegsB0 (w_H W) (ms_mem ms0) a).
{ intros a Ha Hs Ho. apply KF0; [exact Ha | exact Hs |].
  destruct (CDec.decode_ok len bs nch ns) eqn:Hok; intros Hin.
  - apply Exists_cons in Hin as [Hp | Hin]; [| apply Exists_nil in Hin; exact Hin].
    cbn [fst snd] in Hp. apply Ho. rewrite Holen, (dsd_decode_olen len bs nch ns Hok). lia.
  - apply Exists_nil in Hin. exact Hin. }
assert (KFA : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - ESTACK <= a < sp1 + 120) -> ~ (out <= a < out + olen) ->
    aview decodesegsB0 (w_H W) mem3 a = aview decodesegsB0 (w_H W) mem a)
  by (intros a Ha Hn Ho; rewrite (KF a Ha ltac:(lia) Ho); exact (KD a Ha Hn Ho)).
assert (KFL : forall a, 0 <= a < sp1 - 4096 -> ~ (out <= a < out + olen) ->
    aview decodesegsB0 (w_H W) mem3 a = aview decodesegsB0 (w_H W) mem a)
  by (intros a Ha Ho; apply KFA; [unfold ESTACK in *; lia | unfold ESTACK in *; lia | exact Ho]).
assert (KSL : forall off v, 0 <= off -> off + 8 <= 120 ->
    rdword (aview decodesegsB0 (w_H W) (ms_mem ms0)) (sp1 + off) = Some v ->
    rdword (aview decodesegsB0 (w_H W) mem3) (sp1 + off) = Some v)
  by (intros off v Hl1 Hl2 HRd; apply (dsd_rdword_keep (w_H W) (ms_mem ms0) mem3 _ v);
      [intros i Hi; apply KF; [lia | unfold ESTACK; lia | lia] | exact HRd]).
apply SRr_ret. split; [reflexivity|]. exists regs3, mem3, md3.
split; [reflexivity|]. split; [exact HJ3|].
split; [exact (eq_trans (HP3 3 ltac:(unfold acallee_saved; lia)) DGP)|].
split; [exact (eq_trans (HP3 4 ltac:(unfold acallee_saved; lia)) DTP)|].
split; [exact (eq_trans (HP3 8 ltac:(unfold acallee_saved; lia)) D8)|].
split; [exact (eq_trans (HP3 9 ltac:(unfold acallee_saved; lia)) D9)|].
assert (RSP3 : YK11.getr regs3 2 = w64 sp1) by exact (eq_trans (HP3 2 ltac:(unfold acallee_saved; lia)) DSP).
split; [unfold spZ; rewrite RSP3; unfold w64; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
        change (2 ^ Z.of_N 64) with (2 ^ 64); apply Z.mod_small; lia|].
split; [exact HR3|].
split; [exact (eq_trans (HP3 18 ltac:(unfold acallee_saved; lia)) D18)|].
split; [exact (eq_trans (HP3 19 ltac:(unfold acallee_saved; lia)) D19)|].
split; [exact (eq_trans (HP3 20 ltac:(unfold acallee_saved; lia)) D20)|].
split; [exact (eq_trans (HP3 21 ltac:(unfold acallee_saved; lia)) D21)|].
split; [exact (eq_trans (HP3 22 ltac:(unfold acallee_saved; lia)) D22)|].
split; [exact (eq_trans (HP3 23 ltac:(unfold acallee_saved; lia)) D23)|].
split; [exact (eq_trans (HP3 24 ltac:(unfold acallee_saved; lia)) D24)|].
split; [exact (eq_trans (HP3 26 ltac:(unfold acallee_saved; lia)) D26)|].
split; [exact (eq_trans (HP3 27 ltac:(unfold acallee_saved; lia)) D27)|].
split; [exact (KSL 0 F ltac:(lia) ltac:(lia) T0)|].
split; [exact (KSL 8 SH ltac:(lia) ltac:(lia) T8)|].
split; [exact (KSL 16 F ltac:(lia) ltac:(lia) T16)|].
split; [exact (KSL 24 len ltac:(lia) ltac:(lia) T24)|].
split; [exact (KSL 32 SHADOW_OFF ltac:(lia) ltac:(lia) T32)|].
split; [exact (KSL 40 res ltac:(lia) ltac:(lia) T40)|].
split; [exact (KSL 56 (ns mod 2 ^ 32) ltac:(lia) ltac:(lia) T56)|].
split; [exact (KSL 64 (nch mod 2 ^ 32) ltac:(lia) ltac:(lia) T64)|].
split; [exact (KSL 72 (ns mod 2 ^ 64) ltac:(lia) ltac:(lia) T72)|].
split; [exact (KSL 88 out ltac:(lia) ltac:(lia) T88)|].
split; [exact (KSL 112 F ltac:(lia) ltac:(lia) T112)|].
split; [intros i Hi; rewrite (KFL (SH + i) ltac:(lia) ltac:(lia)); exact (Fsh0 i Hi)|].
split; [rewrite (KFL (SH + 4) ltac:(lia) ltac:(lia)); exact Fsh4|].
split; [rewrite (KFL (SH + 5) ltac:(lia) ltac:(lia)); exact Fsh5|].
split; [intros i Hi; rewrite (KFL (SH + i) ltac:(lia) ltac:(lia)); exact (Fsh6 i Hi)|].
split; [apply (dsd_garr8_keep (w_H W) mem mem3 res _); [|exact HG];
        intros i Hi; rewrite length_map, Hbs, Z2Nat.id in Hi by lia; apply KFL; [lia | apply Hnw; lia]|].
split; [apply (dsd_valmem_keep (w_H W) mem mem3 (mode + 4) 4 _); [|exact Hmv1];
        intros i Hi; apply KFL; [cbn in Hi; lia | cbn in Hi; lia]|].
split; [apply (dsd_valmem_keep (w_H W) mem mem3 (mode + 8) 4 _); [|exact Hmv2];
        intros i Hi; apply KFL; [cbn in Hi; lia | cbn in Hi; lia]|].
split; [exact HX|].
split.
{ intros Hnok i Hi. rewrite (KF0 (out + i) ltac:(lia) ltac:(unfold ESTACK; lia) ltac:(rewrite Hnok; intros Hin; inversion Hin)).
  rewrite (KR (out + i) ltac:(lia) ltac:(unfold ESTACK; lia)). exact (FILL i Hi). }
split.
- intros a Ha Hn Ho. rewrite (KFA a Ha Hn Ho). exact (KS a Ha Hn).
- intros a Hq. apply HPr3. apply PD. apply PS. exact Hq.
Qed.

End insp.

(* ------------------------------------------------------------------ *)
(* 6. The segment theorem: llvm_b_st_418 -> llvm_b_st_5cc               *)
(* ------------------------------------------------------------------ *)

(* Arithmetic the stage premises need (lia here does not see div or mod). *)
Lemma dsd_div8 : forall a, 0 <= a -> 8 * (a / 8) <= a < 8 * (a / 8) + 8.
Proof.
intros a Ha. pose proof (Z.div_mod a 8 ltac:(lia)). pose proof (Z.mod_pos_bound a 8 ltac:(lia)). lia.
Qed.

Lemma dsd_mod32_add : forall F, F mod 32 = 0 -> (F + 32) mod 4 = 0 /\ (F + 32) mod 8 = 0.
Proof.
intros F HF. apply (Z.mod_divide F 32 ltac:(lia)) in HF. destruct HF as [q ->].
split; [apply (proj2 (Z.mod_divide _ 4 ltac:(lia))); exists (8 * q + 8)
       | apply (proj2 (Z.mod_divide _ 8 ltac:(lia))); exists (4 * q + 4)]; lia.
Qed.

(* The 12 bytes from t + 4 are addressable when the granule at t has shadow 0 and the next one shadow 4 (the
   granules of [t + 4, t + 12) are t and t + 8); after lib/B/Prog/LLVMFuzzerTestOneInput_segC.v's cp_tbl_addr. *)
Lemma dsd_addr12 : forall t (r : reader), t mod 8 = 0 ->
  r (DCells.shadow_addr t) = Some 0 -> r (DCells.shadow_addr (t + 8)) = Some 4 ->
  range_addressable r SHADOW_OFF (t + 4) 8.
Proof.
intros t r Ht R0 R4 x Hx. unfold shadow_of_addr.
pose proof (Z.div_mod t 8 ltac:(lia)) as Dt. rewrite Ht, Z.add_0_r in Dt.
assert (E8 : (t + 8) / 8 = t / 8 + 1) by (replace (t + 8) with (t + 1 * 8) by ring; apply Z.div_add; lia).
assert (E0 : SHADOW_OFF + t / 8 = DCells.shadow_addr t)
  by (unfold DCells.shadow_addr, DCells.ASAN_K, SHADOW_OFF; lia).
assert (E1 : SHADOW_OFF + (t / 8 + 1) = DCells.shadow_addr (t + 8))
  by (unfold DCells.shadow_addr, DCells.ASAN_K, SHADOW_OFF; rewrite E8; lia).
destruct (Z.lt_ge_cases x (t + 8)) as [Hl | Hg].
- assert (Ex : x / 8 = t / 8) by (symmetry; apply (Z.div_unique x 8 (t / 8) (x - 8 * (t / 8))); lia).
  exists 0. split; [rewrite Ex, E0; exact R0 | left; reflexivity].
- assert (Ex : x / 8 = t / 8 + 1)
    by (symmetry; apply (Z.div_unique x 8 (t / 8 + 1) (x - 8 * (t / 8) - 8)); lia).
  assert (Mx : x mod 8 = x - 8 * (t / 8) - 8)
    by (symmetry; apply (Z.mod_unique x 8 (t / 8 + 1)); lia).
  exists 4. split; [rewrite Ex, E1; exact R4 | right; lia].
Qed.

(* The frame's local at F + 32: its two shadow bytes are the bytes 4 and 5 of the frame's shadow (dec_b_fsh). *)
Lemma dsd_local_addr : forall F (r : reader), F mod 32 = 0 ->
  r (shadow_addr F + 4) = Some 0 -> r (shadow_addr F + 5) = Some 4 ->
  range_addressable r SHADOW_OFF (F + 32 + 4) 8.
Proof.
intros F r HF R4 R5.
assert (E32 : (F + 32) / 8 = F / 8 + 4) by (replace (F + 32) with (F + 4 * 8) by ring; apply Z.div_add; lia).
assert (E40 : (F + 32 + 8) / 8 = F / 8 + 5)
  by (replace (F + 32 + 8) with (F + 5 * 8) by ring; apply Z.div_add; lia).
apply dsd_addr12.
- exact (proj2 (dsd_mod32_add F HF)).
- replace (DCells.shadow_addr (F + 32)) with (shadow_addr F + 4)
    by (unfold DCells.shadow_addr, DCells.ASAN_K, shadow_addr, SHADOW_OFF; rewrite E32; lia).
  exact R4.
- replace (DCells.shadow_addr (F + 32 + 8)) with (shadow_addr F + 5)
    by (unfold DCells.shadow_addr, DCells.ASAN_K, shadow_addr, SHADOW_OFF; rewrite E40; lia).
  exact R5.
Qed.

(* The copy's length: the body is the last len input bytes (segC's cp_len_facts). *)
Lemma dsd_len : forall cx, 0 <= d_n cx -> d_n cx = Z.of_nat (length (d_pl cx)) ->
  length (d_body cx) = Z.to_nat (dec_b_len (d_n cx)).
Proof. intros cx Hn Hl. unfold d_body, dec_b_len, dec_b_u. rewrite length_skipn. lia. Qed.

Section dsdk. Context {rc : YM05.RunCeil}.
Variable B : asyms.

(* The fake frame's shadow lies in the shadow memory, below the high application memory. *)
Lemma dsd_sh_bounds : forall cx, 4096 <= d_F cx -> d_F cx + 64 <= alloc_ceiling ->
  SHADOW_OFF <= d_SH cx /\ d_SH cx + 8 <= kHighMemBeg.
Proof.
intros cx H1 H2. pose proof (dsd_div8 (d_F cx) ltac:(lia)) as D. pose proof asan_consts as (C1 & _).
unfold d_SH, shadow_addr, kHighMemBeg, SHADOW_OFF. lia.
Qed.

(* What the frame invariant gives about the walk's addresses (segC's cp_core_facts): the entry sp is a stack
   address above the allocator ceiling, and the fake frame is the one frame of the state, in application memory
   below the ceiling. *)
Lemma dsd_core_facts : forall cx ly S W regs mem md k,
  AR_laws decodesegsB0 B -> dec_b_core B cx ly S W regs mem md k ->
  alloc_ceiling + 32768 <= d_sp0 cx <= 2 ^ 47 /\
  frame_addr ly DEC_FCLASS (d_fpos cx) = d_F cx /\ In (DEC_FCLASS, d_fpos cx) (frames S) /\
  d_F cx + 64 <= alloc_ceiling /\ in_app (d_F cx) 64.
Proof.
intros cx ly S W regs mem md k LAWS Hc.
destruct Hc as (HJ & Hfrms & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hlo & Hhi & H47 & _).
assert (EF : frame_addr ly DEC_FCLASS (d_fpos cx) = d_F cx).
{ unfold d_F, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
assert (Hin : In (DEC_FCLASS, d_fpos cx) (frames S)) by (rewrite Hfrms; left; reflexivity).
destruct (frames_bounds decodesegsB0 B LAWS ly S W mem md DEC_FCLASS (d_fpos cx) HAR Hin) as (_ & Hfc & Hfa).
rewrite EF in Hfc, Hfa. change (fs_frame_bytes DEC_FCLASS) with 64 in Hfc, Hfa.
unfold DEC_LLVMF_STK in *.
split; [lia|]. split; [exact EF|]. split; [exact Hin|]. split; [exact Hfc | exact Hfa].
Qed.

(* A constant cell of B (as_const, re-read at every AR state through ARm's am_const). *)
Lemma dsd_const_word : forall ly S W mem md a v,
  AR decodesegsB0 B ly S W mem md -> In (z8 (ANum a) v) (as_const B ly) -> 0 <= v < 2 ^ 64 ->
  rdword (aview decodesegsB0 (w_H W) mem) a = Some v.
Proof.
intros ly S W mem md a v HAR Hin Hv. destruct HAR as (Mx & _).
apply (rdword_cell B ly _ a v Hv). exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mx) _ Hin).
Qed.

Lemma dsd_const_byte : forall ly S W mem md a v,
  AR decodesegsB0 B ly S W mem md -> In (z1 (ANum a) v) (as_const B ly) ->
  aview decodesegsB0 (w_H W) mem a = Some (le_byte v 1 0).
Proof.
intros ly S W mem md a v HAR Hin. destruct HAR as (Mx & _).
pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mx) _ Hin) as H1.
unfold cell_holds in H1. cbn [c_at c_val c_w z1 c1 aeval] in H1.
pose proof (H1 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r in H0. exact H0.
Qed.

(* A table mode: one of the three 12-byte tables, low in application memory and inside the image, 4-aligned, its
   fields addressable at every AR state (granule 0's shadow from dec_tab_zshadow_at through dec_tab_zshadow_rd,
   granule 1's from its constant shadow row) and its pointer word re-read at every AR state (the pointer rows). *)
Definition dsd_tbl (mode : Z) : Prop :=
  4096 <= mode /\ mode + 12 <= kLowShadowBeg /\ mode mod 4 = 0 /\ IMG_LO <= mode /\ mode + 12 <= IMG_TOP /\
  forall ly S W mem md, AR decodesegsB0 B ly S W mem md ->
    range_addressable (aview decodesegsB0 (w_H W) mem) SHADOW_OFF (mode + 4) 8 /\
    (rdword (aview decodesegsB0 (w_H W) mem) (decodeb_obj 4) = Some mode \/
     rdword (aview decodesegsB0 (w_H W) mem) (decodeb_obj 5) = Some mode \/
     rdword (aview decodesegsB0 (w_H W) mem) (decodeb_obj 6) = Some mode).

(* The mode dec_b_mode_ok selects is the frame's local or a table (segC's cp_where_of; the table addresses come
   from dec_crt_cells' rows by unification). *)
Lemma dsd_where : forall cx ly S W mem md mode nch ns,
  dec_crt_cells B -> AR decodesegsB0 B ly S W mem md -> dec_b_mode_ok cx W mem mode nch ns ->
  mode = d_F cx + 32 \/ dsd_tbl mode.
Proof.
intros cx ly S W mem md mode nch ns HC HAR Hmode.
destruct Hmode as (Hsel & _).
(* dec_crt_cells' rows are picked by their type, never by their position: each row becomes its own hypothesis,
   and every use below names the row it needs in full (so a reordered or extended statement cannot break it). *)
pose proof (HC ly) as HR. repeat match type of HR with _ /\ _ => destruct HR as [? HR] end.
destruct Hsel as [Rm | [Rm | [Rm | Rm]]]; [ | | | left; exact Rm].
- rewrite (dsd_const_word ly S W mem md (decodeb_obj 4) 0x20d60 HAR ltac:(assumption) ltac:(lia)) in Rm.
  injection Rm as Rm. subst mode. right.
  split; [lia|]. split; [unfold kLowShadowBeg; lia|]. split; [reflexivity|].
  split; [rewrite IMG_LO_val; lia|]. split; [rewrite IMG_TOP_val; lia|].
  intros ly2 S2 W2 mem2 md2 HAR2.
  pose proof (HC ly2) as HR2. repeat match type of HR2 with _ /\ _ => destruct HR2 as [? HR2] end.
  split; [apply dsd_addr12;
          [ reflexivity
          | exact (dec_tab_zshadow_rd B ly2 S2 W2 mem2 md2 0x20d60 HAR2 eq_refl ltac:(assumption))
          | exact (dsd_const_byte ly2 S2 W2 mem2 md2 (DCells.shadow_addr 0x20d68) 4 HAR2 ltac:(assumption)) ]|].
  left. exact (dsd_const_word ly2 S2 W2 mem2 md2 (decodeb_obj 4) 0x20d60 HAR2 ltac:(assumption) ltac:(lia)).
- rewrite (dsd_const_word ly S W mem md (decodeb_obj 5) 0x20da0 HAR ltac:(assumption) ltac:(lia)) in Rm.
  injection Rm as Rm. subst mode. right.
  split; [lia|]. split; [unfold kLowShadowBeg; lia|]. split; [reflexivity|].
  split; [rewrite IMG_LO_val; lia|]. split; [rewrite IMG_TOP_val; lia|].
  intros ly2 S2 W2 mem2 md2 HAR2.
  pose proof (HC ly2) as HR2. repeat match type of HR2 with _ /\ _ => destruct HR2 as [? HR2] end.
  split; [apply dsd_addr12;
          [ reflexivity
          | exact (dec_tab_zshadow_rd B ly2 S2 W2 mem2 md2 0x20da0 HAR2 eq_refl ltac:(assumption))
          | exact (dsd_const_byte ly2 S2 W2 mem2 md2 (DCells.shadow_addr 0x20da8) 4 HAR2 ltac:(assumption)) ]|].
  right; left. exact (dsd_const_word ly2 S2 W2 mem2 md2 (decodeb_obj 5) 0x20da0 HAR2 ltac:(assumption) ltac:(lia)).
- rewrite (dsd_const_word ly S W mem md (decodeb_obj 6) 0x20d80 HAR ltac:(assumption) ltac:(lia)) in Rm.
  injection Rm as Rm. subst mode. right.
  split; [lia|]. split; [unfold kLowShadowBeg; lia|]. split; [reflexivity|].
  split; [rewrite IMG_LO_val; lia|]. split; [rewrite IMG_TOP_val; lia|].
  intros ly2 S2 W2 mem2 md2 HAR2.
  pose proof (HC ly2) as HR2. repeat match type of HR2 with _ /\ _ => destruct HR2 as [? HR2] end.
  split; [apply dsd_addr12;
          [ reflexivity
          | exact (dec_tab_zshadow_rd B ly2 S2 W2 mem2 md2 0x20d80 HAR2 eq_refl ltac:(assumption))
          | exact (dsd_const_byte ly2 S2 W2 mem2 md2 (DCells.shadow_addr 0x20d88) 4 HAR2 ltac:(assumption)) ]|].
  right; right. exact (dsd_const_word ly2 S2 W2 mem2 md2 (decodeb_obj 6) 0x20d80 HAR2 ltac:(assumption) ltac:(lia)).
Qed.

(* dec_b_core at a later state of the same journal: the registers it names as the state shows them, and every byte
   it reads (the saved words, the fake frame's flag word, the payload) outside the segment's stack window and the
   decode buffer, hence kept (segC's cp_base0_kept with cp_kz_apart's separation). *)
Lemma dsd_core_kept : forall cx ly S W regs mem md k regs2 mem2 md2 res len out olen,
  AR_laws decodesegsB0 B ->
  d_n cx = Z.of_nat (length (d_pl cx)) ->
  (0 < d_n cx -> In (d_p cx, d_n cx) (ablocks B (d_ly cx) (d_S cx))) ->
  dec_b_core B cx ly S W regs mem md k ->
  ablocks B ly S = ablocks B (d_ly cx) (d_S cx) ++ [(res, len)] ++ [(out, olen)] ->
  @ajournal rc dec_B_sink_head decodesegsB0 B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx)
    (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly S W mem2 md2 k ->
  YK11.getr regs2 8 = w64 (d_sp0 cx) -> YK11.getr regs2 9 = w64 (d_sp1 cx) -> spZ regs2 = d_sp1 cx ->
  YK11.getr regs2 3 = w64 (as_gp B) -> YK11.getr regs2 4 = w64 (as_tp B) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp1 cx - ESTACK <= a < d_sp1 cx + 120) -> ~ (out <= a < out + olen) ->
     aview decodesegsB0 (w_H W) mem2 a = aview decodesegsB0 (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) ->
  dec_b_core B cx ly S W regs2 mem2 md2 k.
Proof.
intros cx ly S W regs mem md k regs2 mem2 md2 res len out olen LAWS Hnl Hpb Hc Hbl HJ2 G8 G9 Gsp G3 G4 KEEP PRES.
pose proof (dsd_core_facts cx ly S W regs mem md k LAWS Hc) as (Hsp0 & EF & Hin & HFc & _).
destruct Hc as (HJ & Hfrms & _ & _ & _ & Hsp1 & Hsp32 & _ & _ & Hsaved & HF4096 & HF32 & HFpres & HFL & Hpay & Hgarr).
pose proof (proj1 HJ) as HAR.
pose proof asan_consts as (C1 & _).
assert (Hino : In (out, olen) (ablocks B ly S))
  by (rewrite Hbl; apply in_or_app; right; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ out olen HAR Hino) as (_ & _ & Hoc & _ & _ & _ & Hor).
pose proof (req_size_pos olen ltac:(lia)) as Hrq.
refine (conj HJ2 (conj Hfrms (conj G8 (conj G9 (conj Gsp (conj Hsp1 (conj Hsp32 (conj G3 (conj G4 (conj _
  (conj HF4096 (conj HF32 (conj _ (conj _ (conj Hpay _))))))))))))))).
- unfold dec_b_saved in *. rewrite Forall_forall in *. intros o Ho.
  assert (Hfo : 8 <= fst o <= 104).
  { unfold dec_b_saved_at in Ho. cbn in Ho. repeat (destruct Ho as [<- | Ho]; [cbn; lia|]). contradiction. }
  apply (dsd_rdword_keep (w_H W) mem mem2 _ _); [|exact (Hsaved o Ho)].
  intros i Hi. apply KEEP; unfold ESTACK; lia.
- intros a Ha. apply PRES. exact (HFpres a Ha).
- pose proof (sep_block_frame decodesegsB0 B LAWS ly S W mem md out olen DEC_FCLASS (d_fpos cx) HAR Hino Hin) as Hsf.
  rewrite EF in Hsf. change (fs_frame_bytes DEC_FCLASS) with 64 in Hsf. unfold zdisjoint in Hsf. cbn [fst snd] in Hsf.
  apply (dsd_rdword_keep (w_H W) mem mem2 _ _); [|exact HFL].
  intros i Hi. apply KEEP; unfold ESTACK; lia.
- apply (dsd_garr8_keep (w_H W) mem mem2 (d_p cx) _); [|exact Hgarr].
  intros i Hi. rewrite length_map, <- Hnl in Hi.
  pose proof (Hpay ltac:(lia)) as Hinp.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hinp) as (_ & Hp4096 & Hpc & _).
  pose proof (req_size_pos (d_n cx) ltac:(lia)) as Hrqp.
  destruct (in_split _ _ (Hpb ltac:(lia))) as (l1 & l2 & El).
  assert (Hpos : ablocks B ly S = l1 ++ (d_p cx, d_n cx) :: (l2 ++ [(res, len)]) ++ (out, olen) :: [])
    by (rewrite Hbl, El, <- !app_assoc; reflexivity).
  pose proof (sep_blocks_pos decodesegsB0 B LAWS ly S W mem md _ _ l1 (l2 ++ [(res, len)]) [] HAR Hpos) as Hsb.
  unfold zdisjoint, block_rng in Hsb. cbn [fst snd] in Hsb.
  apply KEEP; unfold ESTACK; lia.
Qed.

End dsdk.

Section sg. Context {rc : YM05.RunCeil}.
(* lib/B/Prog/LLVMFuzzerTestOneInput_segs.v Section seg, variable for variable; the theorem uses none of
   its Hypotheses. *)
Variable asink_syms : Type.
Variable tfib_K : asink_syms.
Variable asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variable asink_img_laws : list Segment -> asyms -> asink_syms -> Prop.
Variable ro_below_ofl : list Segment -> Z -> Z -> Prop.
Variables RA_LLVMF A_EMPTY : Z.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.

(* +0x418 -> +0x430 (dsd_stage1) -> +0x5a0 (dsd_stage2_eq / dsd_stage2_ne, on the length) -> +0x5cc (dsd_stage3),
   at the journal of dec_b_core and the values llvm_b_st_418 names; llvm_b_st_5cc from dsd_at5cc. *)
Theorem llvm_b_inspect_ok :
  llvm_b_inspect_stmt asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI.
Proof.
unfold llvm_b_inspect_stmt.
intros HC HO HE LAWS ML MTL AMEMSET ACNT AINSP ADEC cx W' c' HBASE HROM H418.
destruct H418 as (fx' & ly' & S' & regs' & mem' & md' & res & out & mode & nch & ns & -> & Hfrm & Hcore & Hbl
  & Hr4096 & Ho4096 & Hmle & Hmok & Hfrs & R10 & R18 & R27 & R20 & R21 & R22 & R23 & R24 & R26 & Hmode & Hfsh
  & Hgarr & S32 & S56 & S64 & S72 & S112).
pose proof HBASE as (_ & _ & _ & _ & Hpn & Hnl & _).
assert (Hn0 : 0 <= d_n cx < 2 ^ 26) by (destruct Hpn as [[-> _] | [Hq _]]; lia).
assert (Hpb : 0 < d_n cx -> In (d_p cx, d_n cx) (ablocks B (d_ly cx) (d_S cx)))
  by (intros Hq; destruct Hpn as [[Hq' _] | [_ Hq']]; [lia | exact Hq']).
pose proof (dsd_core_facts B cx ly' S' W' regs' mem' md' _ LAWS Hcore) as (_ & EF & Hfin & HFc & HFa).
pose proof Hcore as (HJ & _ & R8 & R9 & Rsp & (Hsp1a & Hsp1b) & Hsp32 & R3 & R4 & _ & HF4096 & HF32 & _).
pose proof (proj1 HJ) as HAR.
pose proof asan_consts as (C1 & _).
destruct Hfrs as (S0 & S8 & S16).
destruct Hfsh as (L0 & L4 & L5 & L6).
pose proof Hmode as (_ & Hnch & Hns & V4 & V8).
assert (HSTK : 4336 <= DEC_LLVMF_STK) by (unfold DEC_LLVMF_STK; lia).
(* the two new blocks, the length and the body *)
assert (Hinr : In (res, dec_b_len (d_n cx)) (ablocks B ly' S'))
  by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
assert (Hino : In (out, dec_b_olen nch ns) (ablocks B ly' S'))
  by (rewrite Hbl; apply in_or_app; right; apply in_or_app; right; left; reflexivity).
assert (Hlen0 : 0 <= dec_b_len (d_n cx) < 2 ^ 64) by (unfold dec_b_len; lia).
pose proof (dsd_len cx ltac:(lia) Hnl) as Hbs.
(* the fake frame and its shadow *)
assert (HFr : 0 <= d_F cx < 2 ^ 64) by lia.
pose proof (dsd_sh_bounds cx HF4096 HFc) as (HSHlo & HSHhi).
assert (HSHr : 0 <= d_SH cx < 2 ^ 64) by (unfold SHADOW_OFF, kHighMemBeg in *; lia).
assert (HSH4096 : 4096 <= d_SH cx) by (unfold SHADOW_OFF in *; lia).
assert (HSHc : d_SH cx + 8 <= alloc_ceiling) by (unfold kHighMemBeg in *; lia).
(* the mode: the frame's local or a table *)
pose proof (dsd_where B cx ly' S' W' mem' md' mode nch ns HC HAR Hmode) as Hwhere.
assert (HM : 4096 <= mode /\ mode + 12 <= alloc_ceiling /\ in_app mode 12 /\ mode mod 4 = 0 /\
  (forall memx mdx, AR decodesegsB0 B ly' S' W' memx mdx ->
     aview decodesegsB0 (w_H W') memx (d_SH cx + 4) = Some 0 ->
     aview decodesegsB0 (w_H W') memx (d_SH cx + 5) = Some 4 ->
     range_addressable (aview decodesegsB0 (w_H W') memx) SHADOW_OFF (mode + 4) 8)).
{ destruct Hwhere as [-> | (T1 & T2 & T3 & _ & _ & T4)].
  - split; [lia|]. split; [lia|]. split; [apply (in_app_sub _ _ _ _ HFa); lia|].
    split; [exact (proj1 (dsd_mod32_add _ HF32))|].
    intros memx mdx _ A4 A5. exact (dsd_local_addr _ _ HF32 A4 A5).
  - split; [lia|]. split; [unfold kLowShadowBeg in *; lia|].
    split; [unfold in_app; split; [lia | left; exact T2]|]. split; [exact T3|].
    intros memx mdx HARx _ _. exact (proj1 (T4 _ _ _ _ _ HARx)). }
destruct HM as (HM1 & HM2 & HM3 & HM4 & HM5).
(* the decode buffer is apart from the frame's shadow: a heap block in application memory *)
assert (Hapart : d_SH cx + 8 <= out \/ out + dec_b_olen nch ns <= d_SH cx).
{ destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hino) as (_ & _ & _ & Hoapp & _ & _ & Hor).
  pose proof (req_size_pos (dec_b_olen nch ns) ltac:(lia)) as Hrq.
  unfold in_app in Hoapp. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }

(* the decode buffer is apart from the mode's fields: a heap block is off the image (a table) and apart from the
   fake frame (the local) *)
assert (HMO : mode + 12 <= out \/ out + dec_b_olen nch ns <= mode).
{ pose proof (dsd_olen_bounds nch ns Hnch Hns) as Hob.
  pose proof (req_size_pos (dec_b_olen nch ns) ltac:(lia)) as Hrq.
  destruct Hwhere as [-> | (_ & _ & _ & TL & TH & _)].
  - pose proof (sep_block_frame decodesegsB0 B LAWS ly' S' W' mem' md' out (dec_b_olen nch ns) DEC_FCLASS (d_fpos cx)
      HAR Hino Hfin) as Hsf.
    rewrite EF in Hsf. change (fs_frame_bytes DEC_FCLASS) with 64 in Hsf. unfold zdisjoint in Hsf. cbn [fst snd] in Hsf.
    lia.
  - pose proof (blk_off_imgP (PI := @PI_decodeb rc) B ly' S' W' mem' md' out (dec_b_olen nch ns) HAR Hino) as Hoff.
    unfold off_img in Hoff. pose proof IMG_LO_val. pose proof IMG_TOP_val. lia. }
assert (HPROD : 0 <= dec_b_prod nch ns < 2 ^ 64) by (unfold dec_b_prod; apply Z.mod_pos_bound; lia).
(* +0x418 .. +0x42c *)
replace (w64 (DEC_A_LLVMF + 0x418)) with (Z_to_bv 64 (decodeb_text + 0x418)) by reflexivity.
eapply SRr_bind.
{ exact (dsd_stage1 (fx := fx') B LAWS HC AINSP W' regs' mem' md' DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx)
    (d_W cx) (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly' S' dec_ev_418 (d_sp1 cx) (d_F cx) (d_SH cx)
    res out (dec_b_len (d_n cx)) mode nch ns (dec_b_olen nch ns) (dec_b_prod nch ns) (dec_b_fits0 nch ns)
    (d_body cx) HJ Rsp Hsp1a Hsp1b Hsp32 HSTK R3 R4 R8 R9 R10 R18 R20 R21 R22 R23 R24 R26 R27 Hinr Hino Hlen0 Hbs
    Hgarr HFr HSHr S0 S8 S16 S32 S56 S64 S72 S112 L0 L4 L5 L6 V4 V8 HSHc HSH4096 HF4096 HFc HM1 HM2). }
intros W2 c2 _ H430. pose proof (proj1 H430) as EW2. subst W2.
(* +0x430 .. +0x59c, on the length *)
eapply SRr_bind.
{ destruct (Z.eq_dec (dec_b_len (d_n cx)) 1492) as [Heq | Hne].
  - exact (dsd_stage2_eq (fx := fx') B LAWS HC ACNT W' regs' DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx)
      (d_W cx) (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly' S' dec_ev_418 mem' (d_sp1 cx) (d_F cx) (d_SH cx)
      res out (dec_b_len (d_n cx)) mode nch ns (dec_b_olen nch ns) (dec_b_prod nch ns) (dec_b_fits0 nch ns)
      (d_body cx) c2 Hsp1a Hsp1b Hsp32 HSTK Hinr Hino Hlen0 Hbs Heq HFr HSHr HSH4096 HSHc HM1 HM2 H430).
  - exact (dsd_stage2_ne (fx := fx') B LAWS W' regs' DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx)
      (d_W cx) (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly' S' dec_ev_418 mem' (d_sp1 cx) (d_F cx) (d_SH cx)
      res out (dec_b_len (d_n cx)) mode nch ns (dec_b_olen nch ns) (dec_b_prod nch ns) (dec_b_fits0 nch ns)
      (d_body cx) c2 Hsp1a Hsp1b Hsp32 HSTK Hinr Hino Hlen0 Hbs Hne HFr HSHr HSH4096 HSHc HM1 HM2 H430). }
intros W3 c3 _ H5a0. pose proof (proj1 H5a0) as EW3. subst W3.
(* +0x5a0 .. +0x5c8 *)
eapply SRr_mono.
{ exact (dsd_stage3 (fx := fx') B LAWS HC AMEMSET ADEC W' regs' DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx)
    (d_W cx) (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly' S' dec_ev_418 mem' (d_sp1 cx) (d_F cx) (d_SH cx)
    res out (dec_b_len (d_n cx)) mode nch ns (dec_b_olen nch ns) (dec_b_prod nch ns) (dec_b_fits0 nch ns)
    (d_body cx) c3 Hsp1a Hsp1b Hsp32 HSTK Hbl Hlen0 Hbs Hnch Hns eq_refl HPROD HFr HSHr HSH4096 HSHc HM1 HM2 HM3 HM4
    Hapart HMO HM5 H5a0). }
(* llvm_b_st_5cc from dsd_at5cc *)
intros W4 c4 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & G3 & G4 & G8 & G9 & Gsp & G10 & G18 & G19 & G20 & G21 & G22
  & G23 & G24 & G26 & G27 & T0 & T8 & T16 & T24 & T32 & T40 & T56 & T64 & T72 & T88 & T112 & K0 & K4 & K5 & K6
  & KG & KV4 & KV8 & KOK & KFAIL & KEEP & PRES).
pose proof (proj1 HJ2) as HAR2.
unfold llvm_b_st_5cc.
exists fx', ly', S', regs2, mem2, md2, res, out, mode, nch, ns.
split; [reflexivity|]. split; [exact Hfrm|].
split; [exact (dsd_core_kept B cx ly' S' W' regs' mem' md' _ regs2 mem2 md2 res (dec_b_len (d_n cx)) out
                 (dec_b_olen nch ns) LAWS Hnl Hpb Hcore Hbl HJ2 G8 G9 Gsp G3 G4 KEEP PRES)|].
split; [exact Hbl|]. split; [exact Hr4096|]. split; [exact Ho4096|].
split; [exact Hmle|]. split; [exact Hmok|].
split; [exact (conj T0 (conj T8 T16))|].
split; [exact G10|]. split; [exact G18|]. split; [exact G19|]. split; [exact G20|]. split; [exact G21|].
split; [exact G22|]. split; [exact G23|]. split; [exact G24|]. split; [exact G26|]. split; [exact G27|].
split.
{ refine (conj _ (conj Hnch (conj Hns (conj KV4 KV8)))).
  destruct Hwhere as [Hloc | (_ & _ & _ & _ & _ & T4)].
  - right; right; right. exact Hloc.
  - destruct (proj2 (T4 _ _ _ _ _ HAR2)) as [Q | [Q | Q]]; [left | right; left | right; right; left]; exact Q. }
split; [exact (conj K0 (conj K4 (conj K5 K6)))|].
split; [exact KG|]. split; [exact KOK|]. split; [exact KFAIL|].
split; [exact T24|]. split; [exact T32|]. split; [exact T40|]. split; [exact T56|].
split; [exact T64|]. split; [exact T72|]. split; [exact T88|]. exact T112.
Qed.

End sg.
