(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/B/Prog/LLVMFuzzerTestOneInput_segD.v, with its module paths, module names and numbers changed; 581 of its 652 lines of code are new or changed and 1961 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_exit: u_exit_ok : u_exit_stmt (lib/A/Prog/LLVMFuzzerTestOneInput_segs.v), the exit
   segment of the image-A walk of fuzz_uci.asan's LLVMFuzzerTestOneInput, from u_st_exit (+0x180) to the slot post
   u_post. The form follows fuzz_decode's lib/A/Prog/LLVMFuzzerTestOneInput_seg_exit_tail.v (a seat built by
   pa_entry_st_ok_full, the epilogue run, paj_ret_at at the ret, the slot post read off the journal) and its
   seg_crt1.v c1_Bcrt (a caller-journal callee contract composed at its call).

   +0x180 .. +0x1ac: the five ints at sp1 + 0x1c .. sp1 + 0x2c are loaded (sign-extended) and stored at sp1 + 8 ..
   sp1 + 0x18, a0 = sp1 + 8 and a1 = s2 = margin_max; +0x1b0 jal check_clamp (ra = +0x1b4). The struct's 20 bytes are
   the five results as little-endian int32: the premise garr8 of check_clamp_cg.uci_hot_bytes of RpHot v0 .. v4.
   +0x1b4 .. +0x1ec: a0 = 0, the twelve reloads of the words the prologue saved below the entry sp, sp back to sp0,
   ret to the caller's ra, which the slot pre fixes at RA_LLVMF; s11 is never written (u_core carries it).

   Two runs of the token engine, one seat each (no shadow entry: the frame's bytes are not ASan-checked here, so the
   shadow list is empty and neither run raises an obligation); the call in between is discharged by the u_prem field
   up_cc, whose premises on the struct (addressable, shadow visible) come from the zero-shadow row of the main stack
   range that every AR state carries, and whose post (acall_kept above the callee's stack window) keeps the saved
   words for the second seat. *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0s YC5d.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YM05 YE00 YE01 YO09 YImgTop.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YI16.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import AB1v ACfn.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require AE2k.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal
  UciPSyms UciPList UciPAddr UciPPa UciPPaLib UciPImg UciCg.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import check_clamp_cg.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import LLVMFuzzerTestOneInput_cg
  LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_seg_lib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YK11.
Module XLM := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib.Mem.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ------------------------------------------------------------------ *)
(* 1. The bytes of a 4-byte chunk                                       *)
(* ------------------------------------------------------------------ *)

(* A byte of a value does not see a wider truncation. *)
Lemma x_byte_mod : forall v n s, 0 <= s -> s + 8 <= n ->
  Z.shiftr (v mod 2 ^ n) s mod 256 = Z.shiftr v s mod 256.
Proof.
intros v n s Hs Hn. change 256 with (2 ^ 8). apply Z.bits_inj'. intros j Hj.
destruct (Z.lt_ge_cases j 8) as [H8 | H8].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
  apply Z.mod_pow2_bits_low. lia.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma x_bv8_mod : forall x y, x mod 256 = y mod 256 -> Z_to_bv 8 x = Z_to_bv 8 y.
Proof.
intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. exact H.
Qed.
Lemma x_u8 : forall z, bv_unsigned (Z_to_bv 8 z) = z mod 256.
Proof.
intros z. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. reflexivity.
Qed.
Lemma x_u64 : forall z, bv_unsigned (Z_to_bv 64 z) = z mod 2 ^ 64.
Proof.
intros z. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). reflexivity.
Qed.
(* The engine's byte of a 64-bit word is the little-endian byte of an int32, whatever its sign. *)
Lemma x_byte4 : forall v i, 0 <= i < 4 ->
  YP09.byte_of_word (Z_to_bv 64 v) i = Z_to_bv 8 (le_byte v 4 (Z.to_nat i)).
Proof.
intros v i Hi. unfold YP09.byte_of_word, le_byte. rewrite x_u64.
apply x_bv8_mod. replace (8 * Z.of_nat (Z.to_nat i)) with (8 * i) by lia.
change (8 * Z.of_nat 4) with 32. rewrite (Z.mod_mod _ 256) by lia.
rewrite (x_byte_mod v 64 (8 * i)) by lia. rewrite (x_byte_mod v 32 (8 * i)) by lia. reflexivity.
Qed.
(* The four bytes of le4, in the shape the engine's chunk list has them. *)
Lemma x_b0 : forall v, bv_unsigned (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 v))) = le_byte v 4 0.
Proof.
intros v. rewrite x_u8, x_u64. unfold le_byte.
change (8 * Z.of_nat 4) with 32. change (8 * Z.of_nat 0) with 0.
change ((v mod 2 ^ 64) mod 256) with (Z.shiftr (v mod 2 ^ 64) 0 mod 256).
rewrite (x_byte_mod v 64 0) by lia. rewrite (x_byte_mod v 32 0) by lia. reflexivity.
Qed.
Lemma x_b1 : forall v, bv_unsigned (Z_to_bv 8 (Z.shiftr (bv_unsigned (Z_to_bv 64 v)) 8)) = le_byte v 4 1.
Proof.
intros v. rewrite x_u8, x_u64. unfold le_byte.
change (8 * Z.of_nat 4) with 32. change (8 * Z.of_nat 1) with 8.

rewrite (x_byte_mod v 64 8) by lia. rewrite (x_byte_mod v 32 8) by lia. reflexivity.
Qed.
Lemma x_b2 : forall v,
  bv_unsigned (Z_to_bv 8 (Z.shiftr (Z.shiftr (bv_unsigned (Z_to_bv 64 v)) 8) 8)) = le_byte v 4 2.
Proof.
intros v. rewrite Z.shiftr_shiftr by lia. change (8 + 8) with 16.
rewrite x_u8, x_u64. unfold le_byte.
change (8 * Z.of_nat 4) with 32. change (8 * Z.of_nat 2) with 16.

rewrite (x_byte_mod v 64 16) by lia. rewrite (x_byte_mod v 32 16) by lia. reflexivity.
Qed.
Lemma x_b3 : forall v,
  bv_unsigned (Z_to_bv 8 (Z.shiftr (Z.shiftr (Z.shiftr (bv_unsigned (Z_to_bv 64 v)) 8) 8) 8)) = le_byte v 4 3.
Proof.
intros v. rewrite !Z.shiftr_shiftr by lia.
match goal with |- context [Z.shiftr ?x ?s] => replace s with 24 by lia end.
rewrite x_u8, x_u64. unfold le_byte.
change (8 * Z.of_nat 4) with 32. change (8 * Z.of_nat 3) with 24.

rewrite (x_byte_mod v 64 24) by lia. rewrite (x_byte_mod v 32 24) by lia. reflexivity.
Qed.
Lemma x_byte1v : forall x, 0 <= x < 256 -> le_byte x 1 0 = x.
Proof.
intros x Hx. unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small x 256) by lia. apply Z.mod_small. lia.
Qed.

Section xd. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma x_chunk4 : forall segs E m base off e v,
  sv_denot E e = Z_to_bv 64 v -> val_mem segs m (base + off) 4 v ->
  YP09.chunk_ok segs E m base (YP09.mkChunk off (CVal 4 e)).
Proof.
intros segs E m base off e v He Hv i Hi.
cbn [YP09.c_len YP09.cv_len YP09.c_off YP09.c_val] in *.
exists (Z_to_bv 8 (le_byte v 4 (Z.to_nat i))). split.
- cbn [YP09.cbyte]. rewrite He. f_equal. apply x_byte4. lia.
- replace (base + off + i) with (base + off + Z.of_nat (Z.to_nat i)) by lia. apply Hv. lia.
Qed.
Lemma x_val4 : forall segs E m base off e v,
  sv_denot E e = Z_to_bv 64 v ->
  YP09.chunk_ok segs E m base (YP09.mkChunk off (CVal 4 e)) ->
  val_mem segs m (base + off) 4 v.
Proof.
intros segs E m base off e v He HC k Hk.
assert (Hi : 0 <= Z.of_nat k < YP09.c_len (YP09.mkChunk off (CVal 4 e)))
  by (unfold YP09.c_len, YP09.cv_len; cbn [YP09.c_val]; change (Z.of_N 4) with 4; lia).
destruct (HC (Z.of_nat k) Hi) as (b & Hb & Hm).
cbn [YP09.cbyte YP09.c_off YP09.c_val] in Hb, Hm. rewrite He in Hb.
rewrite (x_byte4 v (Z.of_nat k) ltac:(lia)), Nat2Z.id in Hb. injection Hb as <-. exact Hm.
Qed.
Lemma x_garr_app : forall segs m a l1 l2,
  garr8 segs m a l1 -> garr8 segs m (a + Z.of_nat (length l1)) l2 -> garr8 segs m a (l1 ++ l2).
Proof.
intros segs m a l1 l2 H1 H2 j Hj. rewrite length_app in Hj.
destruct (Nat.lt_ge_cases j (length l1)) as [Hlt | Hge].
- rewrite app_nth1 by exact Hlt. exact (H1 j Hlt).
- rewrite app_nth2 by exact Hge. specialize (H2 (j - length l1)%nat ltac:(lia)).
  replace (a + Z.of_nat (length l1) + Z.of_nat (j - length l1)) with (a + Z.of_nat j) in H2 by lia.
  exact H2.
Qed.
Lemma x_garr4 : forall segs m a v, val_mem segs m a 4 v ->
  garr8 segs m a (map (fun b : byte => bv_unsigned b) (XLM.le4 (Z_to_bv 64 v))).
Proof.
intros segs m a v Hv j Hj. rewrite length_map, XLM.length_le4 in Hj.
assert (EB : nth j (map (fun b : byte => bv_unsigned b) (XLM.le4 (Z_to_bv 64 v))) 0 = le_byte v 4 j).
{ unfold XLM.le4. destruct j as [|[|[|[|j]]]]; [| | | | lia]; cbn [Z_to_le_bytes map nth].
  - apply x_b0. - apply x_b1. - apply x_b2. - apply x_b3. }
assert (HR : 0 <= le_byte v 4 j < 256) by (unfold le_byte; apply Z.mod_pos_bound; lia).
rewrite EB. split; [|exact HR].
intros k Hk. assert (k = 0%nat) as -> by lia.
change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
exact (eq_trans (Hv j ltac:(lia))
  (f_equal (fun z : Z => Some (Z_to_bv 8 z)) (eq_sym (x_byte1v (le_byte v 4 j) HR)))).
Qed.
(* The struct check_clamp reads: the five results as little-endian int32. *)
Lemma x_hot : forall segs m pin v0 v1 v2 v3 v4,
  val_mem segs m pin 4 v0 -> val_mem segs m (pin + 4) 4 v1 -> val_mem segs m (pin + 8) 4 v2 ->
  val_mem segs m (pin + 12) 4 v3 -> val_mem segs m (pin + 16) 4 v4 ->
  garr8 segs m pin (uci_hot_bytes (RpHot v0 v1 v2 v3 v4)).
Proof.
intros segs m pin v0 v1 v2 v3 v4 H0 H1 H2 H3 H4.
assert (L4 : forall v, length (map (fun b : byte => bv_unsigned b) (XLM.le4 (Z_to_bv 64 v))) = 4%nat)
  by (intros v; rewrite length_map; apply XLM.length_le4).
unfold uci_hot_bytes.
cbn [PHC.hot_cells PHC.c4z LC.cells_bytes LC.cbytes
     prefill_ms adapt_min_ms adapt_max_ms adapt_margin servo_clamp_ppm].
rewrite !map_app. cbn [map].
apply x_garr_app; [apply x_garr4; exact H0|]. rewrite L4. change (Z.of_nat 4) with 4.
apply x_garr_app; [apply x_garr4; exact H1|]. rewrite L4. change (Z.of_nat 4) with 4.
replace (pin + 4 + 4) with (pin + 8) by lia.
apply x_garr_app; [apply x_garr4; exact H2|]. rewrite L4. change (Z.of_nat 4) with 4.
replace (pin + 8 + 4) with (pin + 12) by lia.
apply x_garr_app; [apply x_garr4; exact H3|]. rewrite L4. change (Z.of_nat 4) with 4.
replace (pin + 12 + 4) with (pin + 16) by lia.
apply x_garr_app; [apply x_garr4; exact H4|]. rewrite L4. change (Z.of_nat 4) with 4.
apply garr8_nil.
Qed.
End xd.

(* ------------------------------------------------------------------ *)
(* 2. The two seats                                                     *)
(* ------------------------------------------------------------------ *)

(* +0x180: the frame's words between sp1 + 8 and sp1 + 0x30; the write window is the struct [8, 0x1c), the five
   results are the chunks at 0x1c + 4 j (atoms 32 + j). *)
Definition x_rg : YP09.region :=
  YP09.mkRegion (Some 2%nat) 8 48 8 28
    [YP09.mkChunk 28 (CVal 4 (SOff 32 0)); YP09.mkChunk 32 (CVal 4 (SOff 33 0));
     YP09.mkChunk 36 (CVal 4 (SOff 34 0)); YP09.mkChunk 40 (CVal 4 (SOff 35 0));
     YP09.mkChunk 44 (CVal 4 (SOff 36 0))].
Definition x_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition ss180 : sstate := mkSS 384 sr_atoms [x_rg] None x_facts.
(* +0x1b4: the twelve saved words below the entry sp, read only (atoms 32 .. 43, in uci_saved_at's order). *)
Definition x_rg2 : YP09.region :=
  YP09.mkRegion (Some 2%nat) 48 144 0 0
    [YP09.mkChunk 136 (CVal 8 (SOff 32 0)); YP09.mkChunk 128 (CVal 8 (SOff 33 0));
     YP09.mkChunk 120 (CVal 8 (SOff 34 0)); YP09.mkChunk 112 (CVal 8 (SOff 35 0));
     YP09.mkChunk 104 (CVal 8 (SOff 36 0)); YP09.mkChunk 96 (CVal 8 (SOff 37 0));
     YP09.mkChunk 88 (CVal 8 (SOff 38 0)); YP09.mkChunk 80 (CVal 8 (SOff 39 0));
     YP09.mkChunk 72 (CVal 8 (SOff 40 0)); YP09.mkChunk 64 (CVal 8 (SOff 41 0));
     YP09.mkChunk 56 (CVal 8 (SOff 42 0)); YP09.mkChunk 48 (CVal 8 (SOff 43 0))].
Definition ss1b4 : sstate := mkSS 436 sr_atoms [x_rg2] None x_facts.
(* The token engine's shadow base: no shadow entry is needed (this segment checks none). *)
Definition XB : sv := SLit SBv.

Section xe. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation SEGS := (@pa_segs _ uci_listing PI_uci).
Local Abbreviation VAL := (@pa_val _ uci_listing PI_uci).
Local Abbreviation BASE := (@pa_val _ uci_listing PI_uci A_TEXT).

Definition XE (regs : bvmap 5 word) (v0 v1 v2 v3 v4 : Z) : env :=
  Eimg (PI := PI_uci) (Ereg regs [Z_to_bv 64 v0; Z_to_bv 64 v1; Z_to_bv 64 v2; Z_to_bv 64 v3; Z_to_bv 64 v4]).
Definition x_sv (regs0 : bvmap 5 word) : list word :=
  map (fun o : Z * Z => YK11.getr regs0 (Z_to_bv 5 (snd o))) uci_saved_at.
Definition XY (regs regs0 : bvmap 5 word) : env := Eimg (PI := PI_uci) (Ereg regs (x_sv regs0)).

Lemma x_entry : forall (W : world SEGS) (regs : bvmap 5 word) mem (sp1 v0 v1 v2 v3 v4 : Z),
  YK11.getr regs 2 = w64 sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 16 = 0 ->
  (forall a, sp1 + 8 <= a < sp1 + 28 -> apresent (w_H W) mem a) ->
  rd32 (aview SEGS (w_H W) mem) (sp1 + 28) v0 ->
  rd32 (aview SEGS (w_H W) mem) (sp1 + 32) v1 ->
  rd32 (aview SEGS (w_H W) mem) (sp1 + 36) v2 ->
  rd32 (aview SEGS (w_H W) mem) (sp1 + 40) v3 ->
  rd32 (aview SEGS (w_H W) mem) (sp1 + 44) v4 ->
  st_ok_pi SEGS VAL (XE regs v0 v1 v2 v3 v4) ss180
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 384)) mem (seg_rom SEGS))).
Proof.
intros W regs mem sp1 v0 v1 v2 v3 v4 R2 Hsp Hsp16 Hpres Rd0 Rd1 Rd2 Rd3 Rd4.
rewrite restrict_mkst_fx. unfold ss180.
set (E := XE regs v0 v1 v2 v3 v4).
assert (E2 : ew E 2 = YK11.getr regs 2)
  by (unfold E, XE; apply (ew_Eimg_Ereg_nat (L := uci_listing) regs _ 2 2%bv); reflexivity).
assert (Usp : bv_unsigned (ew E 2) = sp1)
  by (rewrite E2, R2; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 v0)
  by (unfold E, XE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 v1)
  by (unfold E, XE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 v2)
  by (unfold E, XE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 v3)
  by (unfold E, XE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 v4)
  by (unfold E, XE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold x_rg. repeat apply Forall_cons; try apply Forall_nil. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Usp. split; [lia|]. split; [lia|].
  split; [intros o Ho; apply (apresent_writable SEGS); apply Hpres; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  + apply (x_chunk4 SEGS E _ sp1 28 (SOff 32 0) v0);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | apply val_mem_of_rd32; exact Rd0].
  + apply (x_chunk4 SEGS E _ sp1 32 (SOff 33 0) v1);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | apply val_mem_of_rd32; exact Rd1].
  + apply (x_chunk4 SEGS E _ sp1 36 (SOff 34 0) v2);
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | apply val_mem_of_rd32; exact Rd2].
  + apply (x_chunk4 SEGS E _ sp1 40 (SOff 35 0) v3);
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | apply val_mem_of_rd32; exact Rd3].
  + apply (x_chunk4 SEGS E _ sp1 44 (SOff 36 0) v4);
      [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | apply val_mem_of_rd32; exact Rd4].
- cbn [pairwise_disjoint all_disjoint]. tauto.
- split; [|split; [exact I | exact I]].
  cbn [x_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp. change (2 ^ 4) with 16.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma x_slot : forall (W : world SEGS) E mem (base off o sp0 : Z) (nn : nat) (r : bv 5) (regs0 : bvmap 5 word),
  ew E nn = YK11.getr regs0 r -> base + off = sp0 - o ->
  rdword (aview SEGS (w_H W) mem) (sp0 - o) = Some (bv_unsigned (YK11.getr regs0 r)) ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 8 (SOff nn 0))).
Proof.
intros W E mem base off o sp0 nn r regs0 He Hoff Hr.
apply (chunk_ok_val SEGS E _ base off 8 (SOff nn 0) (bv_unsigned (YK11.getr regs0 r))).
- cbn [sv_denot]. rewrite He, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- pose proof (bv_unsigned_in_range 64 (YK11.getr regs0 r)) as Hw.
  change (bv_modulus 64) with (2 ^ 64) in Hw. change (8 * Z.of_N 8) with 64. exact Hw.
- zside.
- rewrite Hoff. apply val_mem_of_rdword. exact Hr.
Qed.

Lemma x_entry2 : forall (W : world SEGS) (regs regs0 : bvmap 5 word) mem (sp0 : Z),
  YK11.getr regs 2 = w64 (sp0 - 144) -> 2 ^ 46 + 144 <= sp0 <= 2 ^ 47 -> sp0 mod 16 = 0 ->
  Forall (fun o : Z * Z => rdword (aview SEGS (w_H W) mem) (sp0 - fst o)
            = Some (bv_unsigned (YK11.getr regs0 (Z_to_bv 5 (snd o))))) uci_saved_at ->
  st_ok_pi SEGS VAL (XY regs regs0) ss1b4
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 436)) mem (seg_rom SEGS))).
Proof.
intros W regs regs0 mem sp0 R2 Hsp Hsp16 Hsv.
unfold uci_saved_at in Hsv.
repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H as [?Sv H] end.
cbn [fst snd] in *.
rewrite restrict_mkst_fx. unfold ss1b4.
set (E := XY regs regs0).
assert (E2 : ew E 2 = YK11.getr regs 2)
  by (unfold E, XY; apply (ew_Eimg_Ereg_nat (L := uci_listing) regs _ 2 2%bv); reflexivity).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 144)
  by (rewrite E2, R2; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (EX : forall j, (j < 12)%nat -> ew E (32 + j)%nat = nth j (x_sv regs0) (Z_to_bv 64 0))
  by (intros j Hj; unfold E, XY; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as X0. pose proof (EX 1%nat ltac:(lia)) as X1.
pose proof (EX 2%nat ltac:(lia)) as X2. pose proof (EX 3%nat ltac:(lia)) as X3.
pose proof (EX 4%nat ltac:(lia)) as X4. pose proof (EX 5%nat ltac:(lia)) as X5.
pose proof (EX 6%nat ltac:(lia)) as X6. pose proof (EX 7%nat ltac:(lia)) as X7.
assert (Hsp16' : (sp0 - 144) mod 16 = 0)
  by (replace (sp0 - 144) with (sp0 + (-9) * 16) by lia; rewrite Z.mod_add by lia; exact Hsp16).
pose proof (EX 8%nat ltac:(lia)) as X8. pose proof (EX 9%nat ltac:(lia)) as X9.
pose proof (EX 10%nat ltac:(lia)) as X10. pose proof (EX 11%nat ltac:(lia)) as X11.
cbn [x_sv uci_saved_at map nth snd] in X0, X1, X2, X3, X4, X5, X6, X7, X8, X9, X10, X11.
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold x_rg2. repeat apply Forall_cons; try apply Forall_nil. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  + apply (x_slot W E mem _ _ 8 sp0 32%nat (Z_to_bv 5 1) regs0); [exact X0 | lia | exact Sv].
  + apply (x_slot W E mem _ _ 16 sp0 33%nat (Z_to_bv 5 8) regs0); [exact X1 | lia | exact Sv0].
  + apply (x_slot W E mem _ _ 24 sp0 34%nat (Z_to_bv 5 9) regs0); [exact X2 | lia | exact Sv1].
  + apply (x_slot W E mem _ _ 32 sp0 35%nat (Z_to_bv 5 18) regs0); [exact X3 | lia | exact Sv2].
  + apply (x_slot W E mem _ _ 40 sp0 36%nat (Z_to_bv 5 19) regs0); [exact X4 | lia | exact Sv3].
  + apply (x_slot W E mem _ _ 48 sp0 37%nat (Z_to_bv 5 20) regs0); [exact X5 | lia | exact Sv4].
  + apply (x_slot W E mem _ _ 56 sp0 38%nat (Z_to_bv 5 21) regs0); [exact X6 | lia | exact Sv5].
  + apply (x_slot W E mem _ _ 64 sp0 39%nat (Z_to_bv 5 22) regs0); [exact X7 | lia | exact Sv6].
  + apply (x_slot W E mem _ _ 72 sp0 40%nat (Z_to_bv 5 23) regs0); [exact X8 | lia | exact Sv7].
  + apply (x_slot W E mem _ _ 80 sp0 41%nat (Z_to_bv 5 24) regs0); [exact X9 | lia | exact Sv8].
  + apply (x_slot W E mem _ _ 88 sp0 42%nat (Z_to_bv 5 25) regs0); [exact X10 | lia | exact Sv9].
  + apply (x_slot W E mem _ _ 96 sp0 43%nat (Z_to_bv 5 26) regs0); [exact X11 | lia | exact Sv10].
- cbn [pairwise_disjoint all_disjoint]. tauto.
- split; [|split; [exact I | exact I]].
  cbn [x_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp. change (2 ^ 4) with 16.
  repeat match goal with |- _ /\ _ => split end; try exact I; try exact Hsp16'; lia.
Qed.
End xe.

(* ------------------------------------------------------------------ *)
(* 3. The segment                                                       *)
(* ------------------------------------------------------------------ *)

(* The write rights of the first run: the struct's window, inside the entry's stack window. *)
Ltac x_awr Usp :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (-144));
    [reflexivity | rewrite ?ew_ewset_other by lia; rewrite Usp; lia | cbn; lia | cbn; lia |] ].
Ltac x_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?sg ?vl ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  | st_ok ?sg ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg sg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.

Section sg. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation SEGS := (@pa_segs _ uci_listing PI_uci).
Local Abbreviation VAL := (@pa_val _ uci_listing PI_uci).
Local Abbreviation BASE := (@pa_val _ uci_listing PI_uci A_TEXT).

(* A field of the frame region, whose value may be a negative int. *)
Lemma x_field : forall E m (r : YP09.region) base off e v,
  region_ok segs E m r -> YP09.r_base r = Some 2%nat -> bv_unsigned (ew E 2) = base ->
  In (YP09.mkChunk off (CVal 4 e)) (YP09.r_chunks r) -> sv_denot E e = Z_to_bv 64 v ->
  val_mem segs m (base + off) 4 v.
Proof.
intros E m r base off e v HR Hb Hbv Hin He.
destruct HR as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck.
rewrite Hb in Hck. cbn [base_val] in Hck. rewrite Hbv in Hck.
exact (x_val4 segs E m base off e v He Hck).
Qed.

(* The shadow of the struct: the main stack range has shadow 0 in every AR state. *)
Lemma x_shadow : forall (rd : reader) lo hi pin,
  zero_shadow rd SHADOW_OFF lo (hi - lo) -> lo + 1000 <= pin -> pin + 136 <= hi ->
  range_addressable rd SHADOW_OFF pin 20 /\ shadow_hull_vis rd pin 20.
Proof.
intros rd lo hi pin HZ Hlo Hhi.
assert (HS0 : forall t, pin / 8 - 12 <= t <= pin / 8 + 12 -> rd (SHADOW_OFF + t) = Some 0).
{ intros t Ht.
  replace (SHADOW_OFF + t) with (shadow_of_addr SHADOW_OFF lo + (t - lo / 8))
    by (unfold shadow_of_addr; lia).
  apply HZ. Z.div_mod_to_equations; lia. }
split.
- intros x Hx. exists 0. split; [|left; reflexivity].
  unfold shadow_of_addr. apply HS0. Z.div_mod_to_equations; lia.
- intros s Hs. unfold shadow_addr, SHADOW_OFF in *.
  replace s with (2147450880 + (s - 2147450880)) by lia.
  rewrite HS0; [discriminate | Z.div_mod_to_equations; lia].
Qed.

Theorem u_exit_ok : u_exit_stmt B MT XL RLO RHI.
Proof.
intros HP cx Wc cc HB HEX.
pose proof (up_laws _ _ _ _ _ HP) as LAWS.
pose proof (up_meter_laws _ _ _ _ _ HP) as MTL.
pose proof (up_sink_kept _ _ _ _ _ HP) as HSINK.
pose proof (up_meta_kept _ _ _ _ _ HP) as HMETA.
pose proof (up_cc _ _ _ _ _ HP) as CC.
pose proof (up_cost _ _ _ _ _ HP) as HXL.
destruct cx as [fx ly S W regs mem md p n pl M].
unfold u_base, tfib_lib_pre_x in HB.
unfold u_st_exit, u_core, u_meter, u_res, u_cfg, u_sp1, u_sp0, u_saved in HEX.
cbn [u_fx u_ly u_S u_W u_regs u_mem u_md u_p u_n u_pl u_M] in HB, HEX |- *.
destruct HB as (HAFN & Hra & H10 & H11 & Hpn & Hlen & Hgarr & Hfrs0 & Hnev0 & Hbb & Haro & Hsink0 & Hfd0 & Hfs0
  & Hmeta0 & Hmo0).
pose proof HAFN as (HAR0 & Hret & Hra4 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
destruct HEX as (ly1 & S1 & regs1 & mem1 & md1 & mm & vs & Hcc
  & (HJ & HfrS & Hsp1 & Hgp1 & Htp1 & H27 & Hsaved & Hperm1) & (Hmle & Hmok) & R18 & Hmm & (Hvlen & Hvint & Hvrd)).
subst cc.
destruct vs as [|v0 [|v1 [|v2 [|v3 [|v4 [|v5 vs]]]]]]; cbn [length] in Hvlen; try (exfalso; lia).
repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H as [?Hv H] end.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hstk0 as (Hsp16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
unfold LLVMF_STK, U_FRAME in *.
assert (Hsp : 2 ^ 46 + 144 <= spZ regs <= 2 ^ 47) by lia.
pose proof HJ as (HARJ & HlyJ & HsecsJ & HwleJ & HioJ & HfrsJ & HnevJ & HkJ & F1 & F2 & F3 & F4 & Hgone & HpresJ
  & HstkJ & F5 & HQTJ).
pose proof HlyJ as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
(* the seat at +0x180 *)
assert (R2 : YK11.getr regs1 2 = w64 (spZ regs - 144))
  by (unfold w64; rewrite <- Hsp1; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (Hsp16a : (spZ regs - 144) mod 16 = 0)
  by (replace (spZ regs - 144) with (spZ regs + (-9) * 16) by lia; rewrite Z.mod_add by lia; exact Hsp16).
assert (Rd0 : rd32 (aview segs (w_H Wc) mem1) (spZ regs - 144 + 28) v0)
  by (replace (spZ regs - 144 + 28) with (spZ regs - 144 + 28 + 4 * 0) by lia; exact (Hvrd 0 ltac:(lia))).
assert (Rd1 : rd32 (aview segs (w_H Wc) mem1) (spZ regs - 144 + 32) v1)
  by (replace (spZ regs - 144 + 32) with (spZ regs - 144 + 28 + 4 * 1) by lia; exact (Hvrd 1 ltac:(lia))).
assert (Rd2 : rd32 (aview segs (w_H Wc) mem1) (spZ regs - 144 + 36) v2)
  by (replace (spZ regs - 144 + 36) with (spZ regs - 144 + 28 + 4 * 2) by lia; exact (Hvrd 2 ltac:(lia))).
assert (Rd3 : rd32 (aview segs (w_H Wc) mem1) (spZ regs - 144 + 40) v3)
  by (replace (spZ regs - 144 + 40) with (spZ regs - 144 + 28 + 4 * 3) by lia; exact (Hvrd 3 ltac:(lia))).
assert (Rd4 : rd32 (aview segs (w_H Wc) mem1) (spZ regs - 144 + 44) v4)
  by (replace (spZ regs - 144 + 44) with (spZ regs - 144 + 28 + 4 * 4) by lia; exact (Hvrd 4 ltac:(lia))).
pose proof (x_entry (fx := fx) Wc regs1 mem1 (spZ regs - 144) v0 v1 v2 v3 v4 R2 ltac:(lia) Hsp16a
  ltac:(intros a Ha; apply HpresJ; lia) Rd0 Rd1 Rd2 Rd3 Rd4) as HS.
set (E0 := XE regs1 v0 v1 v2 v3 v4) in HS.
assert (HEI : img_env (@pa_val _ uci_listing PI_uci) A_LIM E0) by (unfold E0, XE; apply Eimg_env).
assert (SHOK : sh_ok SEGS XB (@nil shent) E0 (mrestrict (w_H Wc) mem1)) by apply Forall_nil.
assert (Usp : bv_unsigned (ew E0 2) = spZ regs - 144).
{ unfold E0, XE. rewrite (ew_Eimg_Ereg_nat (L := uci_listing) regs1 _ 2 2%bv eq_refl), R2.
  unfold w64. apply unsigned_lit_small. lia. }
pose proof (paj_run (fx := fx) (SK := AE2k.tfib_sink_head) (PI := PI_uci) B LAWS) as RUN.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr SEGS Wx (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + 384)) mem1 (seg_rom SEGS)) md1) Q) end.
paj_run_tok RUN HS HJ SHOK Bspan; [x_awr Usp|].
assert (EE : forall (nn : nat) (r : bv 5), Z.of_nat nn = bv_unsigned r ->
  sv_denot E0 (SOff nn 0) = YK11.getr regs1 r).
{ intros nn r Hnn. cbn [sv_denot]. unfold E0, XE.
  rewrite (ew_Eimg_Ereg_nat (L := uci_listing) regs1 _ nn r Hnn), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (EX32 : ew E0 32 = Z_to_bv 64 v0)
  by (unfold E0, XE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (EX33 : ew E0 33 = Z_to_bv 64 v1)
  by (unfold E0, XE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (EX34 : ew E0 34 = Z_to_bv 64 v2)
  by (unfold E0, XE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (EX35 : ew E0 35 = Z_to_bv 64 v3)
  by (unfold E0, XE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (EX36 : ew E0 36 = Z_to_bv 64 v4)
  by (unfold E0, XE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 4)).
x_reg HS (1%bv : bv 5) Ra1. x_reg HS (2%bv : bv 5) Rsp. x_reg HS (10%bv : bv 5) Ra0.
x_reg HS (11%bv : bv 5) Ra11. x_reg HS (3%bv : bv 5) Rgp. x_reg HS (4%bv : bv 5) Rtp.
x_reg HS (27%bv : bv 5) R27x.
cbn [sv_denot] in Ra1. rewrite (img_env_codeptr E0 HEI) in Ra1.
cbn [sv_denot] in Rsp, Ra0. rewrite Usp in Rsp, Ra0. rewrite Z.add_0_r in Rsp.
rewrite (EE 18%nat 18%bv eq_refl), R18 in Ra11.
rewrite (EE 3%nat 3%bv eq_refl), Hgp1 in Rgp.
rewrite (EE 4%nat 4%bv eq_refl), Htp1 in Rtp.
rewrite (EE 27%nat 27%bv eq_refl), H27 in R27x.
assert (Hspm : spZ (ms_regs ms) = spZ regs - 144).
{ unfold spZ at 1. rewrite Rsp. apply unsigned_lit_small. lia. }
assert (HAR2 : AR segs B ly1 S1 Wc (ms_mem ms) (with_vm_backing (m_vm_lazy md1) mat md1)) by exact (proj1 HJ).
lazymatch type of HS with st_ok ?sg ?Ex ?ssx (restrict ?H ?msx) =>
  let rr := eval vm_compute in (nth_error (ss_mem ssx) 0) in
  lazymatch rr with Some ?r0 =>
    pose proof (st_ok_region_nth Ex ssx (restrict H msx) 0%nat r0 HS eq_refl) as HR0 end end.
cbn [ms_mem restrict] in HR0.
assert (D0 : sv_denot E0 (SExt true 32 (SOff 32 0)) = Z_to_bv 64 v0).
{ cbn [sv_denot]. rewrite EX32, Z.add_0_r, Z_to_bv_bv_unsigned. apply sext32_small.
  unfold INT_MIN, INT_MAX in *. lia. }
assert (D1 : sv_denot E0 (SExt true 32 (SOff 33 0)) = Z_to_bv 64 v1).
{ cbn [sv_denot]. rewrite EX33, Z.add_0_r, Z_to_bv_bv_unsigned. apply sext32_small.
  unfold INT_MIN, INT_MAX in *. lia. }
assert (D2 : sv_denot E0 (SExt true 32 (SOff 34 0)) = Z_to_bv 64 v2).
{ cbn [sv_denot]. rewrite EX34, Z.add_0_r, Z_to_bv_bv_unsigned. apply sext32_small.
  unfold INT_MIN, INT_MAX in *. lia. }
assert (D3 : sv_denot E0 (SExt true 32 (SOff 35 0)) = Z_to_bv 64 v3).
{ cbn [sv_denot]. rewrite EX35, Z.add_0_r, Z_to_bv_bv_unsigned. apply sext32_small.
  unfold INT_MIN, INT_MAX in *. lia. }
assert (D4 : sv_denot E0 (SExt true 32 (SOff 36 0)) = Z_to_bv 64 v4).
{ cbn [sv_denot]. rewrite EX36, Z.add_0_r, Z_to_bv_bv_unsigned. apply sext32_small.
  unfold INT_MIN, INT_MAX in *. lia. }
assert (V0 : val_mem segs (mrestrict (w_H Wc) (ms_mem ms)) (spZ regs - 144 + 8) 4 v0)
  by (apply (x_field E0 _ _ (spZ regs - 144) 8 (SExt true 32 (SOff 32 0)) v0 HR0 eq_refl Usp
        ltac:(cbn [YP09.r_chunks In]; tauto) D0)).
assert (V1 : val_mem segs (mrestrict (w_H Wc) (ms_mem ms)) (spZ regs - 144 + 12) 4 v1)
  by (apply (x_field E0 _ _ (spZ regs - 144) 12 (SExt true 32 (SOff 33 0)) v1 HR0 eq_refl Usp
        ltac:(cbn [YP09.r_chunks In]; tauto) D1)).
assert (V2 : val_mem segs (mrestrict (w_H Wc) (ms_mem ms)) (spZ regs - 144 + 16) 4 v2)
  by (apply (x_field E0 _ _ (spZ regs - 144) 16 (SExt true 32 (SOff 34 0)) v2 HR0 eq_refl Usp
        ltac:(cbn [YP09.r_chunks In]; tauto) D2)).
assert (V3 : val_mem segs (mrestrict (w_H Wc) (ms_mem ms)) (spZ regs - 144 + 20) 4 v3)
  by (apply (x_field E0 _ _ (spZ regs - 144) 20 (SExt true 32 (SOff 35 0)) v3 HR0 eq_refl Usp
        ltac:(cbn [YP09.r_chunks In]; tauto) D3)).
assert (V4 : val_mem segs (mrestrict (w_H Wc) (ms_mem ms)) (spZ regs - 144 + 24) 4 v4)
  by (apply (x_field E0 _ _ (spZ regs - 144) 24 (SExt true 32 (SOff 36 0)) v4 HR0 eq_refl Usp
        ltac:(cbn [YP09.r_chunks In]; tauto) D4)).
assert (HGARR : garr8 segs (mrestrict (w_H Wc) (ms_mem ms)) (spZ regs - 136)
                  (uci_hot_bytes (RpHot v0 v1 v2 v3 v4))).
{ apply x_hot;
  [ replace (spZ regs - 136) with (spZ regs - 144 + 8) by lia; exact V0
  | replace (spZ regs - 136 + 4) with (spZ regs - 144 + 12) by lia; exact V1
  | replace (spZ regs - 136 + 8) with (spZ regs - 144 + 16) by lia; exact V2
  | replace (spZ regs - 136 + 12) with (spZ regs - 144 + 20) by lia; exact V3
  | replace (spZ regs - 136 + 16) with (spZ regs - 144 + 24) by lia; exact V4 ]. }
assert (HZS : zero_shadow (aview segs (w_H Wc) (ms_mem ms)) SHADOW_OFF (ly_stk_lo ly1)
                (ly_stk_hi ly1 - ly_stk_lo ly1))
  by exact (al_zshadow _ _ LAWS ly1 S1 Wc (ms_mem ms) _ (ly_stk_lo ly1, ly_stk_hi ly1 - ly_stk_lo ly1)
              HAR2 ltac:(left; reflexivity)).
destruct (x_shadow (aview segs (w_H Wc) (ms_mem ms)) (ly_stk_lo ly1) (ly_stk_hi ly1) (spZ regs - 136)
  HZS ltac:(lia) ltac:(lia)) as (HRA & HHULL).
pmkst HS.
eapply SRr_bind.
{ refine (CC fx 32768 (spZ regs) [] ly S W mem md [] ly1 S1 Wc (ms_mem ms) _ (5 * U_EV_TURN)
    (ms_regs ms) (spZ regs - 136) mm (RpHot v0 v1 v2 v3 v4) HJ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  - rewrite Ra1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Ra1. vm_compute. discriminate.
  - exact Rgp.
  - exact Rtp.
  - rewrite Ra0. unfold w64. f_equal. lia.
  - exact Ra11.
  - rewrite Hspm. exact Hsp16a.
  - rewrite Hspm. unfold CC_STK, CC_FRAME, CC_ALIGN, ESTACK. lia.
  - rewrite Hspm. lia.
  - unfold PHC.hot_int. cbn [prefill_ms adapt_min_ms adapt_max_ms adapt_margin servo_clamp_ppm].
    repeat split; lia.
  - destruct Hmm as [-> | ->]; unfold U_MM0, U_MM1, INT_MAX; lia.
  - rewrite Hspm. lia.
  - unfold PHC.RP_HOT_SIZE. lia.
  - exact HGARR.
  - exact HRA.
  - exact HHULL.
  - rewrite HfrS. unfold CC_CID. vm_compute. reflexivity.
  - unfold CC_EV, U_EV_TURN, PN.CNO_EV, PV.CV_EV, EV_LIB in *. lia. }
intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md3 & Hc2 & HJ2 & HPres & HfrS2 & HPerm2 & HKept & Hmle2).
(* the saved words are kept: outside the run's window, and above this call's stack window *)
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 136 <= a < spZ regs - 116) ->
  aview segs (w_H Wc) (ms_mem ms) a = aview segs (w_H Wc) mem1 a).
{ apply (kept_of_frame E0 (ss_mem ss180) (w_H Wc) mem1 (ms_mem ms)
    (fun a => spZ regs - 136 <= a < spZ regs - 116) HFr).
  intros b wlo whi a Hin Hr. vm_compute in Hin. destruct Hin as [Heq | []].
  injection Heq as <- <- <-. cbn [base_val] in Hr. rewrite Usp in Hr. lia. }
assert (KEEPA : forall a, spZ regs - 100 <= a < spZ regs ->
  aview segs (w_H W2) mem2 a = aview segs (w_H Wc) mem1 a).
{ intros a Ha.
  assert (H1 : alloc_ceiling <= a < 2 ^ 64) by lia.
  assert (H2 : ~ spZ (ms_regs ms) - CC_STK <= a < spZ (ms_regs ms))
    by (rewrite Hspm; unfold CC_STK, CC_FRAME, CC_ALIGN, ESTACK; lia).
  apply (eq_trans (y := aview segs (w_H Wc) (ms_mem ms) a));
    [exact (proj1 HKept a H1 H2) | apply KEEP1; lia]. }
assert (KEEPW : forall a, spZ regs - 100 <= a -> a + 8 <= spZ regs ->
  rdword (aview segs (w_H W2) mem2) a = rdword (aview segs (w_H Wc) mem1) a)
  by (intros a H1 H2; apply rdword_kept; intros i Hi; apply KEEPA; lia).
cbn [u_sp0 u_regs] in Hsaved.
assert (Hsaved2 : Forall (fun o : Z * Z => rdword (aview segs (w_H W2) mem2) (spZ regs - fst o)
          = Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) uci_saved_at).
{ unfold uci_saved_at in *.
  repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H as [?Sv H] end.
  cbn [fst snd] in *.
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  rewrite KEEPW by lia; assumption. }
assert (R2' : YK11.getr regs2 (Z_to_bv 5 2) = w64 (spZ regs - 144))
  by (rewrite (HPres 2 ltac:(unfold acallee_saved; lia)); exact Rsp).
pose proof (x_entry2 (fx := fx) W2 regs2 regs mem2 (spZ regs) R2' ltac:(lia) Hsp16 Hsaved2) as HS2.
set (E2 := XY regs2 regs) in HS2.
assert (HEI2 : img_env VAL A_LIM E2) by (unfold E2, XY; apply Eimg_env).
assert (SHOK2 : sh_ok SEGS XB (@nil shent) E2 (mrestrict (w_H W2) mem2)) by apply Forall_nil.
subst c2. rewrite Ra1.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr SEGS Wx (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 436)) mem2 (seg_rom SEGS)) md3) Q) end.
clear HEI HEI0 HS SHOK HF HFr HG.
paj_run_tok RUN HS2 HJ2 SHOK2 Bspan;
  [repeat first [apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]]|].
(* the twelve atoms of the second seat, in uci_saved_at's order *)
assert (EY : forall j, (j < 12)%nat -> ew E2 (32 + j)%nat = nth j (x_sv regs) (Z_to_bv 64 0))
  by (intros j Hj; unfold E2, XY; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EY 0%nat ltac:(lia)) as EY0. pose proof (EY 1%nat ltac:(lia)) as EY1.
pose proof (EY 2%nat ltac:(lia)) as EY2. pose proof (EY 3%nat ltac:(lia)) as EY3.
pose proof (EY 4%nat ltac:(lia)) as EY4. pose proof (EY 5%nat ltac:(lia)) as EY5.
pose proof (EY 6%nat ltac:(lia)) as EY6. pose proof (EY 7%nat ltac:(lia)) as EY7.
pose proof (EY 8%nat ltac:(lia)) as EY8. pose proof (EY 9%nat ltac:(lia)) as EY9.
pose proof (EY 10%nat ltac:(lia)) as EY10. pose proof (EY 11%nat ltac:(lia)) as EY11.
cbn [x_sv uci_saved_at map nth snd Nat.add] in EY0, EY1, EY2, EY3, EY4, EY5, EY6, EY7, EY8, EY9, EY10, EY11.
assert (EYA : forall (nn : nat) (rr : bv 5), ew E2 nn = YK11.getr regs rr ->
  sv_denot E2 (SOff nn 0) = YK11.getr regs rr)
  by (intros nn rr Hnn; cbn [sv_denot]; rewrite Hnn, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (EYB : forall (nn : nat) (rr : bv 5), Z.of_nat nn = bv_unsigned rr ->
  sv_denot E2 (SOff nn 0) = YK11.getr regs2 rr).
{ intros nn rr Hnn. cbn [sv_denot]. unfold E2, XY.
  rewrite (ew_Eimg_Ereg_nat (L := uci_listing) regs2 _ nn rr Hnn), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
lazymatch type of HS2 with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
  eapply (paj_ret_at (L := uci_listing) (PL := PL_uci) (PI := PI_uci) W2 E2 ssx msx _ _ HS2 eq_refl
    ltac:(clear; vm_compute; reflexivity)) end.
intros mat2.
assert (B1 : (1%bv : bv 5) = Z_to_bv 5 1) by (apply bv_eq; reflexivity).
assert (B2 : (2%bv : bv 5) = Z_to_bv 5 2) by (apply bv_eq; reflexivity).
assert (B3 : (3%bv : bv 5) = Z_to_bv 5 3) by (apply bv_eq; reflexivity).
assert (B4 : (4%bv : bv 5) = Z_to_bv 5 4) by (apply bv_eq; reflexivity).
assert (B27 : (27%bv : bv 5) = Z_to_bv 5 27) by (apply bv_eq; reflexivity).
x_reg HS2 (1%bv : bv 5) Q1. x_reg HS2 (10%bv : bv 5) Q10.
assert (Hra1 : YK11.getr (ms_regs ms0) 1 = YK11.getr regs 1).
{ rewrite Q1, (EYA 32%nat (Z_to_bv 5 1) EY0), <- B1. reflexivity. }
assert (Hpc : v_jalr (YK11.getr (ms_regs ms0) 1) 0 = w64 RA_LLVMF).
{ rewrite Hra1. unfold YK0s.ret_ok in Hret. rewrite Hret. rewrite <- Hra. unfold w64, raZ.
  symmetry. apply Z_to_bv_bv_unsigned. }
assert (HPf : aregs_preserved regs (ms_regs ms0)).
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  clear Hr.
  destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
  lazymatch goal with |- YK11.getr (ms_regs ms0) ?rr = _ => let Hq := fresh "Hq" in x_reg HS2 rr Hq; rewrite Hq end.
  - cbn [sv_denot]. unfold E2, XY.
    rewrite (ew_Eimg_Ereg_nat (L := uci_listing) regs2 _ 2 (Z_to_bv 5 2) eq_refl), R2'.
    unfold w64. rewrite unsigned_lit_small by lia. replace (spZ regs - 144 + 144) with (spZ regs) by lia.
    unfold spZ. rewrite B2. apply Z_to_bv_bv_unsigned.
  - rewrite (EYB 3%nat (Z_to_bv 5 3) eq_refl), (HPres 3 ltac:(unfold acallee_saved; lia)).
    rewrite <- B3, Rgp, Hgp0. reflexivity.
  - rewrite (EYB 4%nat (Z_to_bv 5 4) eq_refl), (HPres 4 ltac:(unfold acallee_saved; lia)).
    rewrite <- B4, Rtp, Htp0. reflexivity.
  - apply EYA; assumption.
  - apply EYA; assumption.
  - apply EYA; assumption.
  - apply EYA; assumption.
  - apply EYA; assumption.
  - apply EYA; assumption.
  - apply EYA; assumption.
  - apply EYA; assumption.
  - apply EYA; assumption.
  - apply EYA; assumption.
  - apply EYA; assumption.
  - rewrite (EYB 27%nat (Z_to_bv 5 27) eq_refl), (HPres 27 ltac:(unfold acallee_saved; lia)).
    rewrite <- B27. exact R27x. }
pose proof (ajournal_materialize segs B LAWS (@pa_segs_low _ uci_listing PI_uci)
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat2 HJ2) as HJ3.
destruct (t_journal_io _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as (Efd & Efs).
assert (Hn0 : 0 <= n) by lia.
unfold u_post. cbn [u_fx u_ly u_S u_W u_regs u_mem u_md u_p u_n u_pl u_M].
exists ly2, S2. eexists. eexists. eexists. exists (5 * U_EV_TURN + CC_EV).
split; [unfold cfg_at; rewrite Hpc; reflexivity|].
unfold tfib_lib_post_x.
split; [exact (t_fp_token _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3)|].
split; [unfold U_EV_TURN, CC_EV, PN.CNO_EV, PV.CV_EV, EV_LIB; lia|].
split; [exact HPf|].
split; [rewrite Q10; reflexivity|].
split; [exact (Permutation_trans HPerm2 Hperm1)|].
split; [intros fd; rewrite Efd; reflexivity|].
split; [exact Efs|].
split; [reflexivity|]. split; [reflexivity|].
split; [exact Hfs0|].
split; [exact (HSINK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 sink_closed_nil Hsink0)|].
split; [exact (HMETA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 Hmeta0)|].
split.
{ apply (mo_le_mono MT MTL _ _ _ _ (mo_le_trans MT MTL _ _ _ _ _ Hmle Hmle2)).
  pose proof (HXL n Hn0) as HX. unfold uci_llvmf_cost, U_TURN_COST in *. lia. }
intros i Hi. destruct Hpn as [[Hz _] | [_ Hin]]; [lia|].
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2' & _).
pose proof (req_size_pos n Hn0) as Hrq.
apply (F2' p n i Hin); [| lia | intros (rg & [] & _)].
exact (Permutation_in _ (Permutation_sym (Permutation_trans HPerm2 Hperm1)) Hin).
Qed.
End sg.
