(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, a working branch), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, with its module paths changed; 672 of its 728 lines of code are new or changed and 525 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/check_text_scribble_A.v; 418 of its 533 lines of code are new or changed and 613 lines of the source are left out. *)
(* The inlined owed_scribble_text loop of check_text_scribble at image A (0x838d0-0x83958): the vocabulary its
   segment files share.
   - Boundaries: the loop head 0x838d0 (lib/A/Prog/check_text_scribble_A.v's cts_ss_lp), the state at 0x83908 where
     the plain-byte path and the dot path that found no digit meet (ctl_ss_alt), and the state at 0x83918 where the
     byte to store and the step 1 or 2 are settled (ctl_ss_join, atoms 460 and 461).
   - Atoms: 417 the output slots done, 418 the text bytes used, 419 the text byte at that index, 460 the byte to
     store, 461 the step; the dead registers of a boundary take the windows 440 (the head), 470 (0x83908) and 490
     (0x83918); the walk pins an address or a byte it reads into 600 and up.
   - The loop writes one byte a turn, at the frame's want array (frame + 32 + the slots done). Its three
     instrumented checks are the text byte at the index, the digit after a dot, and that store. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_text.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85 YCeo.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require AE36 AF0x.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import
CodecCJ CPgBase CPgChkC CPgWalk CPgWalkKept CPgWalkFrame CPgWalkCall CPgWalkIntr check_text_scribble_A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================= the Z level ======================= *)
(* the text bytes a run of k output slots uses: at most two a slot *)
Lemma ctl_owe_used : forall k t, 0 <= snd (scr_owe t k) <= 2 * Z.of_nat k.
Proof.
induction k as [|k IH]; intros t; [rewrite cts_owe_0; cbn [snd]; lia|].
destruct t as [|x t']; cbn [scr_owe]; [cbn [snd]; lia|].
destruct (x =? 0); [cbn [snd]; lia|].
cbv iota.
match goal with |- context [if ?c then _ else _] => destruct c end.
- destruct (scr_owe (tl t') k) as [oo u] eqn:Eo. cbn [snd].
  specialize (IH (tl t')). rewrite Eo in IH. cbn [snd] in IH. lia.
- destruct (scr_owe t' k) as [oo u] eqn:Eo. cbn [snd].
  specialize (IH t'). rewrite Eo in IH. cbn [snd] in IH. lia.
Qed.
(* so the text index of a turn is small: at most two a slot of the whole run *)
Lemma ctl_i_small : forall tb nn o i pre, cts_MODEL tb nn o i pre -> 0 <= i -> i <= 2 * Z.of_nat nn.
Proof.
intros tb nn o i pre [H1 H2] Hi.
pose proof (ctl_owe_used nn tb). pose proof (ctl_owe_used (nn - Z.to_nat o) (skipn (Z.to_nat i) tb)). lia.
Qed.
(* `zext.b` of a byte-valued atom *)
Lemma ctl_and255 : forall E m v, ew E m = Z_to_bv 64 v -> 0 <= v < 256 ->
U E (SAlu ALU_AND (SOff m 0) (SLit 255)) = v.
Proof.
intros E m v Hm Hv. rewrite U_and_lit by lia. rewrite (U_atom E m v Hm) by lia.
change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256. apply Z.mod_small. lia.
Qed.
(* `slli x,c,56` of a byte-valued atom *)
Lemma ctl_sll56 : forall E m v, ew E m = Z_to_bv 64 v -> 0 <= v < 256 ->
U E (SAlu ALU_SLL (SOff m 0) (SLit 56)) = v * 2 ^ 56.
Proof.
intros E m v Hm Hv. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (zcanon_id 56) by (unfold M64; lia).
rewrite (U_atom E m v Hm) by lia. change (Z.land 56 63) with 56.
rewrite Z.shiftl_mul_pow2 by lia. apply zcanon_id. unfold M64.
assert (v * 2 ^ 56 <= 255 * 2 ^ 56) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
Qed.
(* the engine's `addi x,c,-49` then `zext.b` of a byte-valued atom *)
Lemma ctl_sub49 : forall x, 0 <= x < 256 -> (x + (2 ^ 64 - 49)) mod 2 ^ 64 mod 256 = (x - 49) mod 256.
Proof.
intros x Hx. destruct (Z_lt_le_dec x 49) as [Hl | Hl].
- rewrite (Z.mod_small _ (2 ^ 64)) by lia.
  replace (x + (2 ^ 64 - 49)) with ((x - 49) + 2 ^ 56 * 256) by lia.
  apply Z.mod_add. lia.
- replace (x + (2 ^ 64 - 49)) with ((x - 49) + 1 * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. rewrite (Z.mod_small (x - 49) (2 ^ 64)) by lia. reflexivity.
Qed.
Lemma ctl_digit_sub : forall E m v, ew E m = Z_to_bv 64 v -> 0 <= v < 256 ->
U E (SAlu ALU_AND (SAlu ALU_ADD (SExt false 8 (SOff m 0)) (SLit (-49))) (SLit 255)) = (v - 49) mod 256.
Proof.
intros E m v Hm Hv. rewrite U_and_lit by lia. rewrite U_SAlu. cbn [zalu_raw].
rewrite U_SLit, U_zext. change (2 ^ Z.of_N 8) with 256.
rewrite (U_atom E m v Hm) by lia. rewrite (Z.mod_small v 256) by lia.
replace 255 with (Z.ones 8) by reflexivity. rewrite Z.land_ones by lia. change (2 ^ 8) with 256.
unfold zcanon, M64. replace ((-49) mod 2 ^ 64) with (2 ^ 64 - 49) by (vm_compute; reflexivity).
apply ctl_sub49. lia.
Qed.
Lemma ctl_digit_iff : forall v, 0 <= v < 256 -> ((v - 49) mod 256 <= 8 <-> 49 <= v <= 57).
Proof.
intros v Hv. split; intros H.
- destruct (Z_lt_le_dec v 49) as [Hl|Hl].
  + rewrite <- (Z.mod_add (v - 49) 1 256) in H by lia.
    rewrite (Z.mod_small (v - 49 + 1 * 256) 256) in H by lia. lia.
  + rewrite (Z.mod_small (v - 49) 256) in H by lia. lia.
- rewrite (Z.mod_small (v - 49) 256) by lia. lia.
Qed.
(* the engine's `addi x,c,-26` of a digit byte *)
Lemma ctl_sub26 : forall E m v, ew E m = Z_to_bv 64 v -> 26 <= v < 256 ->
U E (SAlu ALU_ADD (SExt false 8 (SOff m 0)) (SLit (-26))) = v - 26.
Proof.
intros E m v Hm Hv. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, U_zext.
change (2 ^ Z.of_N 8) with 256. rewrite (U_atom E m v Hm) by lia. rewrite (Z.mod_small v 256) by lia.
unfold zcanon, M64. replace ((-26) mod 2 ^ 64) with (2 ^ 64 - 26) by (vm_compute; reflexivity).
replace (v + (2 ^ 64 - 26)) with ((v - 26) + 1 * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

(* one byte a region's chunk holds, as the engine writes it *)
Lemma ctl_byte_of : forall E m v, ew E m = Z_to_bv 64 v -> 0 <= v < 256 ->
YP09.byte_of_word (sv_denot E (SOff m 0)) 0 = Z_to_bv 8 (YO0f.le_byte v 1 0).
Proof.
intros E m v Hm Hv. rewrite sv_denot_SOff0, Hm.
unfold YP09.byte_of_word, YO0f.le_byte. rewrite unsigned_lit_small by lia.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite !Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite !(Z.mod_small v 256) by lia. reflexivity.
Qed.

(* `addi x,y,1` and `lbu` of a byte-valued atom *)
Lemma ctl_addi1 : forall E m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + 1 < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff m 0) (SLit 1)) = v + 1.
Proof.
intros E m v Hm H1 H2. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (zcanon_id 1) by (unfold M64; lia).
rewrite (U_atom E m v Hm) by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma ctl_zext8 : forall E m v, ew E m = Z_to_bv 64 v -> 0 <= v < 256 ->
U E (SExt false 8 (SOff m 0)) = v.
Proof.
intros E m v Hm Hv. rewrite U_zext. change (2 ^ Z.of_N 8) with 256.
rewrite (U_atom E m v Hm) by lia. apply Z.mod_small. lia.
Qed.

(* `bgez x` on a value held in the engine's unsigned form *)
Lemma ctl_bgez : forall E a v, U E a = v -> 0 <= v < 2 ^ 64 ->
branch_taken BC_GE (sv_denot E a) (sv_denot E (SLit 0)) = (v <? 2 ^ 63).
Proof.
intros E a v Ha Hv. rewrite YO0c.branch_ge. unfold U in Ha. rewrite Ha.
cbn [sv_denot]. rewrite (unsigned_lit_small 0) by lia.
unfold YO0b.s64. change (0 <? 2 ^ 63) with true.
destruct (v <? 2 ^ 63) eqn:Ev.
- apply Z.ltb_lt in Ev. rewrite (proj2 (Z.ltb_ge v 0)) by lia. reflexivity.
- apply Z.ltb_ge in Ev. rewrite (proj2 (Z.ltb_lt (v - 2 ^ 64) 0)) by lia. reflexivity.
Qed.
(* the byte a turn appends when the text byte is not a dot followed by a digit *)
Lemma ctl_plain_byte : forall c, 0 <= c < 256 -> (if c <? 128 then c else 63) = (if c <? 2 ^ 63 * 0 + 128 then c else 63).
Proof. intros c Hc. reflexivity. Qed.

(* the first atom of a havoc window *)
Lemma ctl_ew_h0 : forall E k w ws, ew (havoc E k (w :: ws)) k = w.
Proof. intros E k w ws. unfold havoc. cbn [ew]. rewrite Nat.ltb_irrefl, Nat.sub_diag. reflexivity. Qed.
(* `add x,y,z` of two atoms, one at an offset *)
Lemma ctl_add_off : forall E m1 c1 m2 v1 v2, ew E m1 = Z_to_bv 64 v1 -> ew E m2 = Z_to_bv 64 v2 ->
0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 -> 0 <= v1 + c1 < 2 ^ 64 -> 0 <= v1 + c1 + v2 < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff m1 c1) (SOff m2 0)) = v1 + c1 + v2.
Proof.
intros E m1 c1 m2 v1 v2 H1 H2 R1 R2 R3 R4. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E m1 v1 c1 H1) by lia. rewrite (U_atom E m2 v2 H2) by lia.
apply zcanon_id. unfold M64. lia.
Qed.
(* the value a register holds, as the engine's word *)
Lemma ctl_denot_of_U : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. rewrite denot_lit_U, H. reflexivity. Qed.

(* ======================= the boundary states ======================= *)
(* the four regions the loop carries: the frame's eight shadow bytes, the frame with its flag pointer, the spill
   of the frame address and the twelve saved words (the flag byte's region is dropped while the loop puts a
   region on a text byte, and the exits put it back) *)
Definition ctl_regions : smem := Eval vm_compute in tl cts_rec_regions.
(* the frame's eight shadow bytes, the first region the loop carries *)
Definition ctl_fsh_region : YP09.region :=
Eval vm_compute in nth 0 ctl_regions (YP09.mkRegion None 0 0 0 0 []).
(* where the frame's flag byte lies with respect to the four regions the loop carries: the state at the loop
   head holds its region beside them, so its own state says they do not meet *)
Definition ctl_FLu (lyc : alayout) (fpos : Z) : Z := bv_unsigned (Z_to_bv 64 (flag_addr lyc 0 fpos)).
Definition ctl_fldisjZ (F FL SP1 sp : Z) : Prop :=
(FL + 1 <= shadow_addr F \/ shadow_addr F + 8 <= FL) /\
(FL + 1 <= F + 40 \/ F + 64 <= FL) /\
(FL + 1 <= SP1 + 24 \/ SP1 + 32 <= FL) /\
(FL + 1 <= sp - 96 \/ sp <= FL).

(* the registers of the loop head 0x838d0 *)
Definition ctl_lregs : list sv :=
[SLit 0; SOff 1 0; SOff 33 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0;
 SOff 2 0; SOff 33 0; SOff 10 0; SOff 417 0; SOff 10 1; SLit 46; SLit 8; SOff 419 0;
 SOff 16 0; SOff 17 0; SOff 38 0; SOff 12 0; SOff 11 0; SOff 10 0; SOff 38 32; SOff 32 0;
 SOff 61 0; SOff 38 0; SOff 418 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
(* 0x83908: the plain-byte path and the dot path that found no digit; a0 and a6 are about to be written *)
Definition ctl_ss_alt : sstate :=
Eval vm_compute in
ss_havoc_regs (mkSS 0x83908 ctl_lregs ctl_regions None (mkFacts cts_lp_atoms [] [])) 470%nat cts_deadL.
(* 0x83918: the byte to store in a5 (atom 460) and the step in a6 (atom 461) *)
Definition ctl_jregs : list sv :=
[SLit 0; SOff 1 0; SOff 33 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0;
 SOff 2 0; SOff 33 0; SOff 10 0; SOff 417 0; SOff 10 1; SLit 46; SLit 8; SOff 460 0;
 SOff 461 0; SOff 17 0; SOff 38 0; SOff 12 0; SOff 11 0; SOff 10 0; SOff 38 32; SOff 32 0;
 SOff 61 0; SOff 38 0; SOff 418 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
Definition ctl_deadJ : list nat := [1;5;6;7;10;17;28;29;30;31]%nat.
Definition ctl_deadJ_bv : list (bv 5) := [1;5;6;7;10;17;28;29;30;31]%bv.
Definition ctl_ss_join : sstate :=
Eval vm_compute in
ss_havoc_regs (mkSS 0x83918 ctl_jregs ctl_regions None (mkFacts cts_lp_atoms [] [])) 490%nat ctl_deadJ.

(* ======================= reads of a boundary state ======================= *)
Section r. Context {fx : YK11.FPState}.
Lemma ctl_fldisj_of : forall (H : word -> bool) E ss ms F FL SP1 sp,
st_ok tfibsegs E ss (restrict H ms) -> ss_mem ss = cts_rec_regions ->
bv_unsigned (ew E 60) = FL -> bv_unsigned (ew E 61) = shadow_addr F ->
bv_unsigned (ew E 38) = F -> bv_unsigned (ew E 33) = SP1 -> bv_unsigned (ew E 2) = sp ->
ctl_fldisjZ F FL SP1 sp.
Proof.
intros H E ss ms F FL SP1 sp HS Hm U60 U61 U38 U33 U2.
destruct (st_ok_mem_ok tfibsegs E ss _ HS) as (_ & _ & Hpd).
rewrite Hm in Hpd. unfold cts_rec_regions in Hpd. cbn [pairwise_disjoint all_disjoint] in Hpd.
destruct Hpd as ((D1 & D2 & D3 & D4 & _) & _).
unfold extent_disjoint in D1, D2, D3, D4.
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in D1, D2, D3, D4.
rewrite U60 in D1, D2, D3, D4. rewrite U61 in D1. rewrite U38 in D2. rewrite U33 in D3. rewrite U2 in D4.
unfold ctl_fldisjZ. split; [lia|]. split; [lia|]. split; lia.
Qed.
(* the zero shadow byte of the frame's want array, read off the frame-shadow region *)
Lemma ctl_sh4_of : forall (H : word -> bool) E ss ms Fa,
st_ok tfibsegs E ss (restrict H ms) -> nth_error (ss_mem ss) 0%nat = Some ctl_fsh_region ->
bv_unsigned (ew E 61) = shadow_addr Fa ->
aview tfibsegs H (ms_mem ms) (shadow_addr Fa + 4) = Some 0.
Proof.
intros H E ss ms Fa HS Hr H61.
pose proof (cts_chunk1 H E ss ms 0%nat ctl_fsh_region 7%nat 4 (SLit 0) 0 HS Hr
  ltac:(vm_compute; reflexivity) ltac:(cbn [sv_denot]; apply bv_eq; vm_compute; reflexivity)) as V.
cbn [base_val YP09.r_base ctl_fsh_region] in V. rewrite H61 in V.
exact (aview_of_val_mem1 tfibsegs H (ms_mem ms) _ 0 V ltac:(lia)).
Qed.
(* a register put in a literal of its value, which frees the atoms it used *)
Lemma ctl_reg_lit : forall E ss ms (r : bv 5), st_ok tfibsegs E ss ms -> r <> 0%bv ->
st_ok tfibsegs E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r (SLit (bv_unsigned (getr (ms_regs ms) r))))
  (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r HS Hr. apply (st_ok_pin_rege E ss ms r _ HS Hr). cbn [sv_denot]. apply Z_to_bv_bv_unsigned.
Qed.
End r.
(* the want array of the frame is marked usable: its eight bytes share the zero shadow byte *)
Lemma ctl_want_ra : forall (H : word -> bool) (mem2 : word -> option byte) Fa m,
aview tfibsegs H mem2 (shadow_addr Fa + 4) = Some 0 ->
Fa mod 64 = 0 -> 0 <= Fa -> 0 <= m <= 8 ->
range_addressable (aview tfibsegs H mem2) SHADOW_OFF (Fa + 32) m.
Proof.
intros H mem2 Fa m Hz H64 H0 Hm.
assert (H8 : Fa mod 8 = 0)
  by (destruct (proj1 (Z.mod_divide Fa 64 ltac:(lia)) H64) as (kk & Hkk);
      replace Fa with (kk * 8 * 8) by lia; apply Z_mod_mult).
assert (HR : range_addressable (aview tfibsegs H mem2) SHADOW_OFF (Fa + 32) 8).
{ apply (zero_shadow_range (aview tfibsegs H mem2) SHADOW_OFF (Fa + 32) 8).
  - replace (Fa + 32) with ((Fa / 8 + 4) * 8) by (pose proof (Z.div_mod Fa 8 ltac:(lia)); lia).
    apply Z_mod_mult.
  - reflexivity.
  - intros ii Hii. change (8 / 8) with 1 in Hii. replace ii with 0 by lia. rewrite Z.add_0_r.
    assert (Heq : shadow_of_addr SHADOW_OFF (Fa + 32) = shadow_addr Fa + 4)
      by (unfold shadow_of_addr, shadow_addr;
          replace ((Fa + 32) / 8) with (Fa / 8 + 4)
            by (rewrite <- (Z.div_add Fa 4 8 ltac:(lia)); f_equal; lia); lia).
    rewrite Heq. exact Hz. }
intros x Hx. apply HR. lia.
Qed.

(* a byte of application memory is never a shadow byte of the frame *)
Section rr. Context {rc : YM05.RunCeil}.
Lemma ctl_text_off_fsh : forall x Fa, 0 <= Fa -> Fa mod 8 = 0 -> amem_range Fa 64 -> amem_range x 1 -> 0 <= x ->
~ (shadow_addr Fa <= x < shadow_addr Fa + 8).
Proof.
intros x Fa H0 H8 HamF Hamx Hx Hin.
assert (Heq : x = shadow_of_addr SHADOW_OFF (Fa + 8 * (x - shadow_addr Fa))).
{ unfold shadow_of_addr, shadow_addr in *.
  replace (Fa + 8 * (x - (SHADOW_OFF + Fa / 8))) with (Fa + (x - (SHADOW_OFF + Fa / 8)) * 8) by lia.
  rewrite (Z.div_add Fa (x - (SHADOW_OFF + Fa / 8)) 8 ltac:(lia)). lia. }
exact (cts_shadow_apart (Fa + 8 * (x - shadow_addr Fa)) x 1 ltac:(lia)
         ltac:(unfold amem_range in *; lia) Hamx ltac:(lia) ltac:(lia)).
Qed.
End rr.

(* 0x83950: the turn is done, the next text byte is in atom 419 and the slot count in atom 417 *)
Definition ctl_ss_fin : sstate :=
Eval vm_compute in
ss_havoc_regs (mkSS 0x83950 ctl_lregs cts_rec_regions None (mkFacts cts_lp_atoms [] [])) 520%nat cts_deadL.

(* ======================= the walk's tactics ======================= *)
(* the write windows of a boundary state: the spill slot of atom 33 and the save area of atom 2 lie in the walk's
   window, every other region is read-only *)
Ltac ctl_awr :=
idtac; lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0' fp b0 bc ly own) end;
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
| lazymatch goal with
  | HU : bv_unsigned (ew _ 33) = ?v |- awr_ok _ (YP09.mkRegion (Some 33%nat) _ _ _ _ _ :: _) _ ?s0 _ _ _ _ _ =>
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 33%nat (v - s0));
    [reflexivity | rewrite HU; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |] end
| lazymatch goal with
  | HU : bv_unsigned (ew _ 2) = ?v |- awr_ok _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ ?s0 _ _ _ _ _ =>
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (v - s0));
    [reflexivity | rewrite HU; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |] end ];
lazymatch goal with |- ?g => idtac "CTL-AWR-FAIL" g; fail 1 end.
(* the same for the one run that stores into the want array: the first region is the byte at the frame's
   want slot, which the walk's own frame lets it write *)
Ltac ctl_awr_store :=
idtac; lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0' fp b0 bc ly own) end;
lazymatch goal with
| HU : bv_unsigned (ew _ 462) = ?v, HOWN : In (0, ?ps) ?ow |- _ =>
  let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  let Hrest := fresh "Hrest" in
  assert (Hrest : True) by exact I;
  intros a Hwr; lazymatch type of Hwr with in_wrange _ _ _ => idtac end;
  destruct Hwr as (r & Hr & Hb); cbn [In] in Hr;
  destruct Hr as [<- | Hr];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite HU in Hb;
    right; right; right; exists 0, ps; split; [exact HOWN|];
    left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 0) with 64; lia
  | revert a Hr Hb;
    let a2 := fresh "a" in let r2 := fresh "r" in let Hr2 := fresh "Hr" in let Hb2 := fresh "Hb" in
    intros a2 Hr2 Hb2;
    lazymatch goal with |- awr_byte ?stk2 ?sp2 ?fp2 ?b02 ?bc2 ?ly2 ?own2 _ =>
      refine ((_ : awr_ok _ _ stk2 sp2 fp2 b02 bc2 ly2 own2) a2 (ex_intro _ r2 (conj Hr2 Hb2))) end;
    ctl_awr ]
end.
(* the zone of a state's write windows: the walk's stack window or the walk's own frame *)
Ltac ctl_kwr :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr];
  [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
   repeat match goal with H : bv_unsigned (ew _ ?m) = _ |- _ =>
     lazymatch type of Hb with context [bv_unsigned (ew _ m)] => rewrite H in Hb end end;
   lia |]); destruct Hr.
(* carry the want bytes of the frame across a run: no run of the loop but the one store writes them, and the
   stack windows of a run lie above the allocator ceiling, which the frame is below *)
Ltac ctl_wkeep Fv :=
lazymatch goal with
| HFr1 : frame_of ?Ev ?rs (mrestrict ?Hh ?m1) (mrestrict ?Hh ?m2),
  HW : forall a, _ -> aview tfibsegs ?Hh ?m1 a = aview tfibsegs ?Hh ?m0 a |- _ =>
  let HW2 := fresh "HWK2" in
  assert (HW2 : forall a, Fv + 32 <= a < Fv + 40 -> aview tfibsegs Hh m2 a = aview tfibsegs Hh m0 a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in
    intros a Ha; transitivity (aview tfibsegs Hh m1 a); [| exact (HW a Ha)]; unfold aview, mbyte;
    rewrite (HFr1 (Z_to_bv 64 a)); [reflexivity|];
    rewrite unsigned_lit_small by lia;
    let rr := fresh "rr" in let Hin := fresh "Hin" in let Hb := fresh "Hb" in
    intros (rr & Hin & Hb); cbv beta in Hb;
    lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rr rs1) in Hin end;
    repeat (destruct Hin as [<- | Hin];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
       repeat match goal with H : bv_unsigned (ew _ ?m) = _ |- _ =>
         lazymatch type of Hb with context [bv_unsigned (ew _ m)] => rewrite H in Hb end end;
       lia |]); destruct Hin
  | clear HW; rename HW2 into HWK ]
end.

(* fold a run into the kept fact KT: its writes are in the walk's window or in the walk's own frame, and a byte
   of that frame is fresh for the call state *)
Ltac ctl_keep Fv HZh :=
lazymatch goal with
| HFr1 : frame_of ?Ev ?rs (mrestrict _ ?m1) (mrestrict _ ?m2), HG1 : mem_grows _ _,
  KTh : tcj_kept tfibsegs ?Bv ?T ?lycv ?Scv ?Wc ?memcv _ _ ?sp ?Ew,
  LAWSx : AR_laws tfibsegs ?Bv, HARh : AR tfibsegs ?Bv ?lycv ?Scv ?Wc ?memcv ?mdcv |- _ =>
    let KR := fresh "KR" in let KT2 := fresh "KT2" in
    pose proof (cw_kept_run (fun a => (sp - T <= a < sp) \/ (Fv <= a < Fv + 64))
      Ev rs (w_H Wc) m1 m1 m2 (fun _ _ _ => eq_refl) HFr1 ltac:(ctl_kwr)) as KR;
    pose proof (cw_kept_step Bv LAWSx T lycv Scv Wc memcv mdcv Wc m1 m2 sp Ew
      (fun a => (sp - T <= a < sp) \/ (Fv <= a < Fv + 64))
      ltac:(lia) HARh KTh KR
      ltac:(intros a [Ha | Ha]; [left; exact Ha | right; right; exact (HZh a Ha)])
      ltac:(intros a Hp; exact (apresent_grows _ _ _ a HG1 Hp))) as KT2;
    clear KTh KR; rename KT2 into KT
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
cw_norm_model.
(* the unsigned values of the two stack atoms in the state's current environment *)
Ltac ctl_ufacts SP1v spv E33h AGh B2h :=
repeat match goal with
| H : bv_unsigned (ew _ 33) = _ |- _ => clear H
| H : bv_unsigned (ew _ 2) = _ |- _ => clear H
end;
lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
let n33 := fresh "U33" in let n2 := fresh "U2" in
assert (n33 : bv_unsigned (ew Ev 33) = SP1v)
  by (repeat first [ solve [rewrite E33h; apply unsigned_lit_small; lia]
                   | rewrite ew_ewset_other by lia | rewrite ew_havoc_old by (cbn; lia) ];
      rewrite E33h; apply unsigned_lit_small; lia);
assert (n2 : bv_unsigned (ew Ev 2) = spv)
  by (repeat first [ solve [rewrite (AGh 2%nat) by lia; symmetry; exact B2h]
                   | rewrite ew_ewset_other by lia | rewrite ew_havoc_old by (cbn; lia) ];
      rewrite (AGh 2%nat) by lia; symmetry; exact B2h)
end.
(* carry the walk's agreement and its atom facts to the state's current environment *)
Ltac ctl_rebase :=
try lazymatch goal with
| AG : forall nn, (nn < 33)%nat -> ew _ nn = ew ?Eb nn, HS : st_ok _ ?Ev _ _ |- _ =>
  let AG2 := fresh "AG2" in
  assert (AG2 : forall nn, (nn < 33)%nat -> ew Ev nn = ew Eb nn)
    by (intros nn Hnn;
        repeat first [ solve [apply AG; lia]
                     | rewrite ew_ewset_other by lia | rewrite ew_havoc_old by (cbn; lia) ];
        apply AG; lia);
  clear AG; rename AG2 into AG
end;
repeat match goal with
| H : ew ?Eold ?nn = ?v, HS : st_ok _ ?Ev _ _ |- _ =>
  lazymatch Eold with
  | Ev => fail
  | _ => let H2 := fresh "Eh" in
         assert (H2 : ew Ev nn = v)
           by (repeat first [ solve [exact H]
                            | rewrite ew_ewset_other by lia | rewrite ew_havoc_old by (cbn; lia) ]; exact H);
         clear H; rename H2 into H
  end
end.
(* the branch on the text byte (atom 419) as a test on its value *)
Ltac ctl_c419 H :=
rewrite ?branch_eq_U, ?branch_ne_U in H;
lazymatch type of H with context [U ?Ecur (SAlu ALU_AND (SOff 419 0) (SLit 255))] =>
  lazymatch goal with E419x : ew _ 419 = Z_to_bv 64 ?cv, Hcr : 0 <= ?cv < 256 |- _ =>
  let Hx := fresh "Hx" in
  assert (Hx : ew Ecur 419 = Z_to_bv 64 cv)
    by (repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by (cbn; lia)]; exact E419x);
  rewrite (ctl_and255 Ecur 419 cv Hx Hcr) in H; clear Hx end end;
rewrite ?U_lit in H by lia.

(* the branch the engine cannot decide, taking the state and the shadow table by name *)
Ltac ctl_branch HSn SHn Hc :=
srr_branch_tok tfibtbl_lib_ok HSn SHn CW_Bspan;
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
(* the engine's shadow table at the state's env and memory, with no entry of the walk's own *)
Ltac ctl_shok0 :=
repeat match goal with Hsh : sh_ok _ _ _ _ _ |- _ => clear Hsh end;
lazymatch goal with HS : st_ok _ ?Ev _ (restrict (w_H ?Wc) ?msx) |- _ =>
  assert (SHOK : sh_ok tfibsegs CW_Bx [] Ev (mrestrict (w_H Wc) (ms_mem msx))) by constructor end.
(* a register put in a literal of its value *)
Ltac ctl_lit r :=
lazymatch goal with HS : st_ok _ ?Ev ?ssx ?msx |- _ =>
  let HS3 := fresh "HS3" in
  pose proof (ctl_reg_lit Ev ssx msx r HS ltac:(discriminate)) as HS3;
  clear HS; rename HS3 into HS; norm_ss HS end.
(* a register pinned to a fresh atom holding its value *)
Ltac ctl_pin r a :=
lazymatch goal with HS : st_ok _ ?Ev ?ssx ?msx |- _ =>
  let vals := constr:(map (fun rr : bv 5 => getr (ms_regs msx) rr) [r]) in
  let vals' := eval cbn [map ms_regs restrict] in vals in
  let HS3 := fresh "HS3" in
  pose proof (st_ok_havoc_win tfibsegs a Ev ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
  clear HS; rename HS3 into HS;
  set_regs_rec HS a vals' 0%nat [r]; norm_ss HS end.

(* the two atoms of a two-value havoc window at 460 *)
Lemma ctl_ew460 : forall E w0 ws, ew (havoc E 460 (w0 :: ws)) 460 = w0.
Proof. intros E w0 ws. unfold havoc. cbn [ew]. rewrite Nat.ltb_irrefl, Nat.sub_diag. reflexivity. Qed.
Lemma ctl_ew461 : forall E w0 w1 ws, ew (havoc E 460 (w0 :: w1 :: ws)) 461 = w1.
Proof.
intros E w0 w1 ws. unfold havoc. cbn [ew].
rewrite (proj2 (Nat.ltb_ge 461 460) ltac:(lia)). replace (461 - 460)%nat with 1%nat by lia. reflexivity.
Qed.

(* the two live registers of 0x83918 pinned to the atoms 460 (the byte to store) and 461 (the step) *)
Ltac ctl_join_hook :=
lazymatch goal with HS : st_ok _ ?Ex ?ssx ?msx |- _ =>
  let dl := constr:([(15%bv : bv 5); (16%bv : bv 5)]) in
  let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl) in
  let vals' := eval cbn [map ms_regs restrict] in vals in
  let HS3 := fresh "HS3" in
  pose proof (st_ok_havoc_win tfibsegs 460%nat Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
  clear HS; rename HS3 into HS;
  set_regs_rec HS 460%nat vals' 0%nat dl; norm_ss HS end.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.

(* the text byte at an index, and the text's usable marks, at a state the walk has kept *)
Lemma ctl_text_at : forall lyc Sc (W : world tfibsegs) memc mdc ly4 S4 mem4 md4 sp q ch tb j,
AR tfibsegs B lyc Sc W memc mdc -> AR tfibsegs B ly4 S4 W mem4 md4 ->
(forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly4 S4)) ->
(forall cid pos, frame_addr ly4 cid pos = frame_addr lyc cid pos) ->
cstr_rd tfibsegs W memc sp T_check_text_scribble q tb ->
cobj_ok B lyc Sc q (Z.of_nat (length tb)) ->
amem_range ch 24 -> 0 < ch ->
(q + Z.of_nat (length tb) <= ch \/ ch + 24 <= q) ->
tcj_kept tfibsegs B T_check_text_scribble lyc Sc W memc W mem4 sp (fun x => ch <= x < ch + 24) ->
(j < length tb)%nat ->
range_addressable (aview tfibsegs (w_H W) mem4) SHADOW_OFF q (Z.of_nat (length tb)) /\
aview tfibsegs (w_H W) mem4 (q + Z.of_nat j) = Some (nth j tb 0) /\ 0 <= nth j tb 0 < 256.
Proof.
intros lyc Sc W memc mdc ly4 S4 mem4 md4 sp q ch tb j HAR HAR4 Hbl Hfa Hstr Hoq Hcham Hch0 Hdisj KT Hj.
pose proof Hstr as (Hq0 & Hgtb & Hin0 & Hcrd).
pose proof Hcrd as (Hcq0 & Hcqhi & Hcrdb & Hcra & Hchull & Hcam & Hcwin).
destruct (Hgtb j Hj) as (Hv & Hr).
split; [|split; [|exact Hr]].
- apply (cts_obj_ra B LAWS lyc Sc W memc mdc ly4 S4 W mem4 md4 T_check_text_scribble sp
    (fun x => ch <= x < ch + 24) q (Z.of_nat (length tb)) HAR HAR4 Hbl Hfa Hoq ltac:(lia) ltac:(lia) Hcra KT).
  intros x Hx Hw. cbn beta in Hw.
  exact (cts_shadow_apart x ch 24 ltac:(lia) ltac:(unfold amem_range in *; lia) Hcham ltac:(lia) Hw).
- apply (aview_of_val_mem1 tfibsegs (w_H W) mem4 (q + Z.of_nat j) (nth j tb 0)); [|exact Hr].
  apply (cts_obj_val B lyc Sc W memc W mem4 T_check_text_scribble sp (fun x => ch <= x < ch + 24)
    q (Z.of_nat (length tb)) (q + Z.of_nat j) 1%nat (nth j tb 0) Hoq ltac:(lia) ltac:(lia)
    ltac:(intros y Hy Hw; cbn beta in Hw; lia) KT Hv).
Qed.

(* ======================= the loop's boundaries ======================= *)
(* what the walk has proved before the loop and keeps unchanged through it *)
Definition ctl_pre
(STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world tfibsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
(W : world tfibsegs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
(q ch n : Z) (tb : list Z) (S2 : astate) (fpos SP1 : Z) (E0 : env) : Prop :=
cdc_entry tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_check_text_scribble /\
getr regs 10 = w64 q /\ getr regs 11 = w64 ch /\ getr regs 12 = w64 n /\ 0 <= n <= 8 /\
cstr_rd tfibsegs W memc (spZ regs) T_check_text_scribble q tb /\
cobj_ok B lyc Sc q (Z.of_nat (length tb)) /\ cobj_ok B lyc Sc ch 24 /\
cdst_ok tfibsegs B STK sp0 FP ly S lyc Sc own W memc (spZ regs) T_check_text_scribble ch 24 /\
(q + Z.of_nat (length tb) <= ch \/ ch + 24 <= q) /\
(forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E0 nn = getr regs r) /\
ew E0 32 = Z_to_bv 64 SB /\
In (0, fpos) (frames S2) /\ frames S2 = (0, fpos) :: frames Sc /\
ablocks B lyc S2 = ablocks B lyc Sc /\
spZ regs - 144 <= SP1 <= spZ regs - 128 /\ SP1 mod 32 = 0.
(* what a state of the loop carries: the walk's atoms, the journal, what the walk has kept and the input *)
Definition ctl_at
(STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world tfibsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
(W : world tfibsegs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
(ch : Z) (S2 : astate) (fpos SP1 : Z) (E0 : env)
(EZ : env) (msZ : machine_state) (mdZ : Model) : Prop :=
(forall nn, (nn < 33)%nat -> ew EZ nn = ew E0 nn) /\
ew EZ 33 = Z_to_bv 64 SP1 /\ ew EZ 38 = Z_to_bv 64 (frame_addr lyc 0 fpos) /\
ew EZ 60 = Z_to_bv 64 (flag_addr lyc 0 fpos) /\
ew EZ 61 = Z_to_bv 64 (shadow_addr (frame_addr lyc 0 fpos)) /\
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 ((0, fpos) :: own) lyc S2 W (ms_mem msZ) mdZ k /\
tcj_kept tfibsegs B T_check_text_scribble lyc Sc W memc W (ms_mem msZ) (spZ regs)
  (fun x => ch <= x < ch + 24) /\
same_io mdc mdZ.

(* the loop head 0x838d0: o slots done, i text bytes used, pre the bytes want already holds *)
Definition ctl_head
(STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world tfibsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
(W : world tfibsegs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
(q ch n : Z) (tb : list Z) (S2 : astate) (fpos SP1 : Z) (E0 : env) (fuel : nat)
(Q : world tfibsegs -> config -> Prop) : Prop :=
forall (EZ : env) (msZ : machine_state) (mdZ : Model) (o i : Z) (pre : list Z),
st_ok tfibsegs EZ cts_ss_lp (restrict (w_H W) msZ) ->
ctl_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch S2 fpos SP1 E0 EZ msZ mdZ ->
ew EZ 417 = Z_to_bv 64 o -> ew EZ 418 = Z_to_bv 64 i ->
ew EZ 419 = Z_to_bv 64 (nth (Z.to_nat i) tb 0) ->
0 <= o < n -> (Z.to_nat (n - o) <= fuel)%nat -> 0 <= i < Z.of_nat (length (cts_cstr tb)) ->
length pre = Z.to_nat o -> cts_MODEL tb (Z.to_nat n) o i pre ->
YI00.garr8 tfibsegs (mrestrict (w_H W) (ms_mem msZ)) (frame_addr lyc 0 fpos + 32) pre ->
SRr tfibsegs W (mkCfg msZ mdZ) Q.
(* 0x83908: the same, with the text byte settled as not a dot that a digit follows *)
Definition ctl_alt
(STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world tfibsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
(W : world tfibsegs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
(q ch n : Z) (tb : list Z) (S2 : astate) (fpos SP1 : Z) (E0 : env) (fuel : nat)
(Q : world tfibsegs -> config -> Prop) : Prop :=
forall (EZ : env) (msZ : machine_state) (mdZ : Model) (o i : Z) (pre : list Z),
st_ok tfibsegs EZ ctl_ss_alt (restrict (w_H W) msZ) ->
ctl_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch S2 fpos SP1 E0 EZ msZ mdZ ->
ew EZ 417 = Z_to_bv 64 o -> ew EZ 418 = Z_to_bv 64 i ->
ew EZ 419 = Z_to_bv 64 (nth (Z.to_nat i) tb 0) ->
0 <= o < n -> (Z.to_nat (n - o) <= fuel)%nat -> 0 <= i < Z.of_nat (length (cts_cstr tb)) ->
ctl_fldisjZ (frame_addr lyc 0 fpos) (ctl_FLu lyc fpos) SP1 (spZ regs) ->
length pre = Z.to_nat o -> cts_MODEL tb (Z.to_nat n) o i pre ->
~ (nth (Z.to_nat i) tb 0 = 46 /\ 49 <= nth (Z.to_nat (i + 1)) tb 0 <= 57) ->
YI00.garr8 tfibsegs (mrestrict (w_H W) (ms_mem msZ)) (frame_addr lyc 0 fpos + 32) pre ->
SRr tfibsegs W (mkCfg msZ mdZ) Q.
(* 0x83918: the byte cv to store and the step st are settled, and the model has taken its step *)
(* 0x83950: the two tests that end the turn, with o slots and i text bytes now done *)
Definition ctl_fin
(STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world tfibsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
(W : world tfibsegs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
(q ch n : Z) (tb : list Z) (S2 : astate) (fpos SP1 : Z) (E0 : env) (fuel : nat)
(Q : world tfibsegs -> config -> Prop) : Prop :=
forall (EZ : env) (msZ : machine_state) (mdZ : Model) (o i : Z) (pre : list Z),
st_ok tfibsegs EZ ctl_ss_fin (restrict (w_H W) msZ) ->
ctl_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch S2 fpos SP1 E0 EZ msZ mdZ ->
ew EZ 417 = Z_to_bv 64 o -> ew EZ 418 = Z_to_bv 64 i ->
ew EZ 419 = Z_to_bv 64 (nth (Z.to_nat i) tb 0) ->
0 < o <= n -> (Z.to_nat (n - o) <= fuel)%nat ->
0 <= i <= Z.of_nat (length (cts_cstr tb)) -> i <= 16 ->
length pre = Z.to_nat o -> cts_MODEL tb (Z.to_nat n) o i pre ->
ctl_fldisjZ (frame_addr lyc 0 fpos) (ctl_FLu lyc fpos) SP1 (spZ regs) ->
YI00.garr8 tfibsegs (mrestrict (w_H W) (ms_mem msZ)) (frame_addr lyc 0 fpos + 32) pre ->
SRr tfibsegs W (mkCfg msZ mdZ) Q.
Definition ctl_join
(STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world tfibsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
(W : world tfibsegs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
(q ch n : Z) (tb : list Z) (S2 : astate) (fpos SP1 : Z) (E0 : env) (fuel : nat)
(Q : world tfibsegs -> config -> Prop) : Prop :=
forall (EZ : env) (msZ : machine_state) (mdZ : Model) (o i : Z) (pre : list Z) (cv st : Z),
st_ok tfibsegs EZ ctl_ss_join (restrict (w_H W) msZ) ->
ctl_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch S2 fpos SP1 E0 EZ msZ mdZ ->
ew EZ 417 = Z_to_bv 64 o -> ew EZ 418 = Z_to_bv 64 i ->
ew EZ 460 = Z_to_bv 64 cv -> ew EZ 461 = Z_to_bv 64 st ->
0 <= o < n -> (Z.to_nat (n - o) <= fuel)%nat -> 0 <= i -> 0 <= cv < 256 -> (st = 1 \/ st = 2) ->
i + st <= Z.of_nat (length (cts_cstr tb)) ->
ctl_fldisjZ (frame_addr lyc 0 fpos) (ctl_FLu lyc fpos) SP1 (spZ regs) ->
length pre = Z.to_nat o ->
cts_MODEL tb (Z.to_nat n) (o + 1) (i + st) (pre ++ [cv]) ->
YI00.garr8 tfibsegs (mrestrict (w_H W) (ms_mem msZ)) (frame_addr lyc 0 fpos + 32) pre ->
SRr tfibsegs W (mkCfg msZ mdZ) Q.
End d.
End b.
