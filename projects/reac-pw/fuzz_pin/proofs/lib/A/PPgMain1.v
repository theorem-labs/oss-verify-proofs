(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made for libreac/fuzz_knock's ASan harness walk (LLVMFuzzerTestOneInput 0x7eed0 in
   fuzz_knock.asan, sha256 61768cf4739b7641c99c825dde45eddafc55b601d41109555be0272fc7ca4118): segment S2 PARSED, from
   proofs/cgif/cgif_file_fuzzer/lib/A/ACfe.v (the journal-threaded callee call, lines 159-330) and A/ACf0.v (the
   addressable range of a frame object from its zero shadow bytes, lines 56-78) at c8557374ad2e, with their module paths
   changed and the names of a Theorem Labs lane's framework (a working branch). The S2 -> S7 boundary ss_X / INV_X is
   a Theorem Labs lane's lib/A/APgMain7.v (a working branch); the S2 -> S3 boundary ss_L / INV_L and the loop
   rt_L are a Theorem Labs lane's lib/A/APgLoop0.v / APgMainL.v (a working branch).
   rule 24: no function proved (a port of the released cgif_file_fuzzer harness walk structure). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_knock/lib/A/APgMain2.v, with its module paths and module names changed; 491 of its 566 lines of code are new or changed and 308 lines of the source are left out. *)
(* reac-pw/fuzz_pin's ASan harness walk (LLVMFuzzerTestOneInput 0x806b4, fuzz_pin.asan sha256
   3e4859aed23f78a6eb028120d664abda29bcb8a3bfdea5d6ee5b32b646de9d16), segment S1: 0x807d0 .. 0x80828, from the cut
   ss_H to the cut ss_Q (lib/A/PPgMainSt.v). rule 24 (reuse): no function is proved here; this is a segment lemma of
   the walk, with the call-site lemmas of its two calls.

   The code (neutral disassembly; s3 = n, s4 = p at ss_H):
     0x807d0 beqz s3 -> 0x8080c (n = 0: s9 = s5 = a0 = 0, -> 0x80820)
     0x807d4-0x807e0 the instrumented check of data[0] (slow path 0x80a80, error path 0x80a8c, shown not reached:
       (p, n) is a heap block with req_size n = n); 0x807e4 s9 = data[0]; s5 = n - 1; s4 = p + 1
     0x807f0 beqz s5 -> 0x80814 (n = 1: a0 = 0, -> 0x80820)
     0x807f4-0x80800 memchr(p + 1, 0, n - 1) through the wrapper's 4-byte jump 0x41928; 0x80804 bnez a0 -> 0x8081c
       (found: s5 = a0 - s4) else -> 0x80820
     0x80820 a0 = s5 + 1; 0x80824 malloc through 0x52b54; 0x80828 beqz a0 -> 0x80a6c (the abort, not reached:
       the allocator rule gives 4096 <= the result).
   The segment is cut once more, at 0x80820 (ss_M below, local to this file, with s4 = r, s5 = k and s9 = the flags
   byte pinned to slots 430, 431, 432): pm_S1_head runs ss_H -> ss_M over the four paths (n = 0, n = 1, memchr
   found, memchr not found), pm_S1_tail runs ss_M -> ss_Q (the malloc call and the abort test), pm_S1 composes them.
   memchr's result is pin_k (the first NUL of the bytes after the flags byte): pm_pin_k_of, from first_byte and the
   input bytes rt_base's garr8 gives (pm_in_byte, through the journal with FP = []).
   Call sites: pin_memchr_site with aj_memchr_atS (amemchr_realizes made journal-threaded, the shape of
   PPgMainCall.aj_intrin_atS); pin_malloc_site with PPgMainCall.amalloc04_sub.
   Patterns: proofs/libreac/fuzz_knock/lib/A/APgMain1.v (the checked input read, the branch splits, the joins) and
   APgMain2.v (the frame chain of a call), proofs/cgif/cgif_file_fuzzer/lib/A/ACf2.v (the malloc call, its post and
   the meter), lib/A/PPgMain0.v (a call and the reseat at pin).
   Atoms: 430 .. 433, the after-call windows 434 .. 449 (memchr) and 470 .. 485 (malloc), and ss_M's dead-register
   window 450 .. 469. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import AWalkFw1 AWalkFw2 ACfm PPgBase.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.Rt Require Import WrapRo MemchrDef.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import PPgWrap PPgMainCall PPgMainRt PPgMainSt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ------------------------------ the cut at 0x80820, inside S1 (local) ------------------------------
   ss_H's frame part and memory; s4 = r (slot 430), s5 = k (431), s9 = the flags byte (432); the other registers
   dead (slots 450 ..). INV_M: the journal and the meter as at ss_H, and the three values as the input bytes give
   them. *)
Definition pm_M_deads : list nat := [1; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 19; 26; 27; 28; 29; 30; 31]%nat.
Definition pm_M_deads_bv : list (bv 5) := [1; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 19; 26; 27; 28; 29; 30; 31]%bv.
Definition pm_M_regs : list sv :=
[SLit 0; SOff 1 0; SOff 70 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0;
 SOff 2 0; SOff 9 0; SOff 10 0; SOff 11 0; SOff 12 0; SOff 13 0; SOff 14 0; SOff 15 0;
 SOff 16 0; SOff 17 0; SOff 75 0; SOff 19 0; SOff 430 0; SOff 431 0; SOff 32 0; SOff 88 0;
 SOff 75 0; SOff 432 0; SOff 26 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
Definition ss_M : sstate := Eval vm_compute in
ss_havoc_regs (mkSS 0x80820 pm_M_regs pm_mem None (mkFacts pm_atoms [] pm_alias)) 450 pm_M_deads.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.
Definition INV_M (B : asyms) (MT : ameter_ops) : rtcx -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx E k acc ly3 S3 W3 ms3 md3 => k <= 0 /\ acc <= ACC0 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) /\
exists r kk fl,
ew E 430 = Z_to_bv 64 r /\ ew E 431 = Z_to_bv 64 kk /\ ew E 432 = Z_to_bv 64 fl /\
kk = Z.of_nat (pin_k (c_pl cx)) /\ fl = pin_flags (c_pl cx) /\
r = (if c_n cx =? 0 then c_p cx else c_p cx + 1).

(* ------------------------------ the input bytes and pin_k ------------------------------ *)
Lemma pm_nul_idx_char : forall (l : list byte) (kk : nat),
(kk <= length l)%nat ->
(forall i, (i < kk)%nat -> bv_unsigned (nth i l (Z_to_bv 8 0)) <> 0) ->
((kk < length l)%nat -> bv_unsigned (nth kk l (Z_to_bv 8 0)) = 0) ->
nul_idx l = kk.
Proof.
induction l as [|x l IH]; intros kk Hle Hbef Hat; cbn [length nul_idx] in *.
- lia.
- destruct kk as [|kk].
  + specialize (Hat ltac:(lia)). cbn [nth] in Hat. rewrite Hat. reflexivity.
  + assert (Hx : bv_unsigned x <> 0) by (exact (Hbef 0%nat ltac:(lia))).
    destruct (Z.eqb_spec (bv_unsigned x) 0) as [Ex|_]; [exfalso; exact (Hx Ex)|].
    f_equal. apply IH; [lia | intros i Hi; exact (Hbef (S i) ltac:(lia)) | intros Hk; exact (Hat ltac:(lia))].
Qed.
Lemma pm_pin_k_of : forall (pl : list byte) (rd : reader) p kk,
1 <= Z.of_nat (length pl) ->
(forall i, 0 <= i < Z.of_nat (length pl) -> rd (p + i) = Some (bv_unsigned (nth (Z.to_nat i) pl (Z_to_bv 8 0)))) ->
0 <= kk <= Z.of_nat (length pl) - 1 ->
(forall i, 0 <= i < kk -> exists b, rd (p + 1 + i) = Some b /\ b <> 0) ->
(kk < Z.of_nat (length pl) - 1 -> rd (p + 1 + kk) = Some 0) ->
Z.of_nat (pin_k pl) = kk.
Proof.
intros pl rd p kk Hlen Hrd Hkk Hbef Hat.
destruct pl as [|x l]; cbn [length] in Hlen, Hrd, Hkk, Hat; [lia|].
unfold pin_k, pin_rest. cbn [tl].
assert (HN : nul_idx l = Z.to_nat kk); [|rewrite HN; lia].
apply pm_nul_idx_char; [lia| |].
- intros i Hi. destruct (Hbef (Z.of_nat i) ltac:(lia)) as (b & Hb & Hb0).
  pose proof (Hrd (1 + Z.of_nat i) ltac:(lia)) as R. replace (p + (1 + Z.of_nat i)) with (p + 1 + Z.of_nat i) in R by lia.
  rewrite Hb in R. injection R as R. replace (Z.to_nat (1 + Z.of_nat i)) with (S i) in R by lia. cbn [nth] in R.
  intros Ez. apply Hb0. rewrite R. exact Ez.
- intros Hk. pose proof (Hat ltac:(lia)) as A. pose proof (Hrd (1 + kk) ltac:(lia)) as R.
  replace (p + (1 + kk)) with (p + 1 + kk) in R by lia. rewrite A in R. injection R as R.
  replace (Z.to_nat (1 + kk)) with (S (Z.to_nat kk)) in R by lia. cbn [nth] in R. symmetry. exact R.
Qed.

(* `sub s5,a0,s4` at 0x8081c with s4 = p + 1, as the executor writes it: (p * -1 + -1) + a0 *)
Lemma U_neg_add : forall E a k0 p v,
ew E a = Z_to_bv 64 p -> ew E k0 = Z_to_bv 64 v -> 0 <= p < 2 ^ 64 -> 0 <= v < 2 ^ 64 -> 0 <= v - (p + 1) < 2 ^ 64 ->
U E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff a 0) (SLit (-1))) (SLit (-1))) (SOff k0 0)) = v - (p + 1).
Proof.
intros E a k0 p v Ha Hk Hp Hv Hr.
rewrite !U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite !U_SOff, !U_SLit, Ha, Hk, !unsigned_lit_small by lia.
rewrite !Z.add_0_r. unfold zcanon, M64.
rewrite (Z.mod_small p), (Z.mod_small v) by lia. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
rewrite Zplus_mod_idemp_l, <- Z.add_assoc, Zplus_mod_idemp_l.
replace (p * (2 ^ 64 - 1) + (2 ^ 64 - 1 + v)) with ((v - (p + 1)) + (p + 1) * 2 ^ 64) by ring.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

(* ------------------------------ memchr, journal-threaded (the shape of PPgMainCall.aj_intrin_atS) ------------------------------ *)
Section mc.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Lemma aj_memchr_atS : forall pc, amemchr_realizes segs B pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x c n (o : Z) raw,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 c -> getr regsT 12 = w64 n ->
0 <= c < 256 -> 0 <= n < 2 ^ 32 -> 0 < x -> x + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
src_ok segs W regsT memT x n -> amem_range x n ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x n ->
(0 < n -> shadow_hull_vis (aview segs (w_H W) memT) x n) ->
aro_unowned segs B (aview segs (w_H W) memT) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\
(exists kk, first_byte segs W memT x n c kk /\ getr regs2 10 = (if kk <? n then w64 (x + kk) else w64 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
same_but_materialized mdc md2).
Proof.
intros pc AM W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x c n o raw
HJ Ha0 Ha1 Ha2 Hc Hn Hx0 Hxn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hsrc Hamr Hra_x Hhull Hro.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
assert (ESTACK = 4096) as Hes by reflexivity.
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption. rewrite Hra. exact Hraw. }
eapply SRr_mono.
{ exact (AM lyc Sc W regsT memT mdc x c n HPRE Ha0 Ha1 Ha2 Hc Hn Hx0 Hxn Hsrc Hamr Hra_x Hhull Hro). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write segs B LAWS segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
(fun a => sp0 + o - ESTACK <= a < sp0 + o) Sc own HJ).
- exact Hfr.
- exact Hpres2.
- exact Hsame.
- intros a Ha. left. left. lia.
- exact HAR2.
- reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr|]. split; [exact Hpres2 | exact Hsame].
Qed.
End mc.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Variable FP : list (Z * Z).
Variable POST : rtcx -> world tfibsegs -> config -> Prop.
Hypothesis FP0 : FP = [].
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis AMALLOC4 : amalloc04_rule tfibsegs B MT.
Hypothesis AMEMCHR : amemchr_realizes tfibsegs B 0x41928.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.
(* the input byte i, read at a state the journal reaches: byte i of c_pl *)
Lemma pm_in_byte : forall cx own ly3 S3 W3 mem3 md3 k i,
rt_base B MT cx ->
ajournal tfibsegs B LLVMF_STK (spZ (c_regs cx)) FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 W3 mem3 md3 k ->
0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3) -> 0 <= i < c_n cx ->
aview tfibsegs (w_H W3) mem3 (c_p cx + i) = Some (bv_unsigned (nth (Z.to_nat i) (c_pl cx) (Z_to_bv 8 0))).
Proof.
intros cx own ly3 S3 W3 mem3 md3 k i HB HJ Hn Hin3 Hi.
destruct HB as (HPRE & _ & _ & _ & Hpn & Hnpl & HPL & _).
assert (Hin : In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx))) by (destruct Hpn as [[H0 _] | [_ H]]; [lia | exact H]).
assert (Hrq : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
rewrite (F2 (c_p cx) (c_n cx) i Hin Hin3); [| rewrite Hrq; exact Hi | rewrite FP0; apply inFP_nil].
destruct (HPL (Z.to_nat i) ltac:(rewrite length_map; lia)) as [Hv Hr].
assert (Hn' : nth (Z.to_nat i) (map (fun b : byte => bv_unsigned b) (c_pl cx)) 0 = bv_unsigned (nth (Z.to_nat i) (c_pl cx) (Z_to_bv 8 0))).
{ rewrite <- (map_nth (fun b : byte => bv_unsigned b) (c_pl cx) (Z_to_bv 8 0)). apply nth_indep. rewrite length_map. lia. }
rewrite Hn' in Hv, Hr. rewrite Z2Nat.id in Hv by lia.
apply (aview_of_val_mem1 tfibsegs); assumption.
Qed.
(* ------------------------------ the call at 0x80800: memchr(p + 1, 0, n - 1) through 0x41928 ------------------------------
   The state at the call gives every premise of amemchr_realizes at a0 = p + 1, a1 = 0, a2 = n - 1. *)
Lemma pin_memchr_site : forall (cx : rtcx) own ly3 S3 W3 mem3 md3 k (regsT : bvmap 5 word),
rt_base B MT cx ->
ajournal tfibsegs B LLVMF_STK (spZ (c_regs cx)) FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 W3 mem3 md3 k ->
In (c_p cx, c_n cx) (ablocks B ly3 S3) -> 1 < c_n cx ->
getr regsT 10 = w64 (c_p cx + 1) -> getr regsT 11 = w64 0 -> getr regsT 12 = w64 (c_n cx - 1) ->
spZ regsT = c_sp1 cx -> getr regsT 1 = Z_to_bv 64 RT_memchr_ra ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
ecall_pre tfibsegs B ly3 S3 W3 regsT mem3 md3 /\
getr regsT 10 = w64 (c_p cx + 1) /\ getr regsT 11 = w64 0 /\ getr regsT 12 = w64 (c_n cx - 1) /\
0 <= 0 < 256 /\ 0 <= c_n cx - 1 < 2 ^ 32 /\ 0 < c_p cx + 1 /\ c_p cx + 1 + (c_n cx - 1) <= 2 ^ 63 /\
src_ok tfibsegs W3 regsT mem3 (c_p cx + 1) (c_n cx - 1) /\ amem_range (c_p cx + 1) (c_n cx - 1) /\
range_addressable (aview tfibsegs (w_H W3) mem3) SHADOW_OFF (c_p cx + 1) (c_n cx - 1) /\
(0 < c_n cx - 1 -> shadow_hull_vis (aview tfibsegs (w_H W3) mem3) (c_p cx + 1) (c_n cx - 1)) /\
aro_unowned tfibsegs B (aview tfibsegs (w_H W3) mem3).
Proof.
intros cx own ly3 S3 W3 mem3 md3 k regsT HB HJ Hin3 Hn1 Ha0 Ha1 Ha2 Hsp Hra Hgp Htp.
pose proof HB as (HPRE & _ & _ & _ & Hpn & _ & _ & _ & _ & _ & HROD & Esp1 & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : LLVMF_STK = 32768) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hrq : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
assert (Hn26 : c_n cx < 2 ^ 26) by (destruct Hpn as [[H0 _] | [Hr _]]; lia).
pose proof (proj1 HJ) as HAR3.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (_ & Hp4096 & Hpceil & _ & Hppres & _).
rewrite Hrq in Hpceil, Hppres.
destruct (sp1_facts (spZ (c_regs cx) + -128) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
rewrite <- Esp1 in Hsp1r, Hsp1al, Hsp1al16.
split.
{ eapply (ecall_pre_at tfibsegs B LLVMF_STK (spZ (c_regs cx)) FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 W3 mem3 md3 k regsT (c_sp1 cx - spZ (c_regs cx)) HJ).
  - lia.
  - rewrite Zminus_mod, Hsp1al16, Hal16. reflexivity.
  - lia.
  - rewrite FFS, Hes. lia.
  - rewrite Hra. apply ret_ok_even. vm_compute. reflexivity.
  - exact Hgp.
  - exact Htp. }
split; [exact Ha0|]. split; [exact Ha1|]. split; [exact Ha2|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split.
{ intros a Ha. split.
  - apply (aview_some_of_apresent tfibsegs). exact (proj1 (Hppres a ltac:(lia))).
  - rewrite Hsp. rewrite FFS in Hslo. lia. }
split; [apply (amem_range_of_block tfibsegs B LAWS ly3 S3 W3 mem3 md3 (c_p cx) (c_n cx)); [exact HAR3 | exact Hin3 | lia | rewrite Hrq; lia]|].
split; [apply (range_addressable_of_block tfibsegs B LAWS ly3 S3 W3 mem3 md3 (c_p cx) (c_n cx)); [exact HAR3 | exact Hin3 | lia | rewrite Hrq; lia]|].
split; [intros Hn0; apply (shadow_hull_vis_of_block tfibsegs B LAWS ly3 S3 W3 mem3 md3 (c_p cx) (c_n cx)); [exact HAR3 | exact Hin3 | lia | rewrite Hrq; lia | exact Hn0]|].
apply (aro_unowned_of_arodataP tfibsegs B PM_RLO PM_RHI). apply pm_arodataP.
exact (arodata_ok_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROD).
Qed.
(* ------------------------------ the call at 0x80824: malloc(k + 1) through 0x52b54 ------------------------------
   The state at the call gives every premise of amalloc04_rule (through PPgMainCall.amalloc04_sub) at a0 = k + 1. *)
Lemma pin_malloc_site : forall (cx : rtcx) ly3 S3 W3 mem3 md3 k acc kk (regsT : bvmap 5 word),
rt_base B MT cx ->
ajournal tfibsegs B LLVMF_STK (spZ (c_regs cx)) FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, c_fpos cx)] ly3 S3 W3 mem3 md3 k ->
k <= 0 -> mo_le MT (c_S cx) S3 acc -> acc <= ACC0 -> ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ->
0 <= kk < 2 ^ 26 ->
getr regsT 10 = w64 (kk + 1) -> spZ regsT = c_sp1 cx -> s0Z regsT = spZ (c_regs cx) ->
getr regsT 1 = Z_to_bv 64 RT_malloc_ra -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
rdword (aview tfibsegs (w_H W3) mem3) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) ->
rdword (aview tfibsegs (w_H W3) mem3) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)) ->
getr regsT 10 = w64 (kk + 1) /\ 0 <= kk + 1 < MALLOC_MAX /\ blocks_bytes S3 + (kk + 1) <= LIVE_MAX /\
spZ regsT = spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx)) /\ (c_sp1 cx - spZ (c_regs cx)) mod 16 = 0 /\
c_sp1 cx - spZ (c_regs cx) <= 0 /\ ASTACK - (c_sp1 cx - spZ (c_regs cx)) <= LLVMF_STK /\
getr regsT 3 = w64 (as_gp B) /\ getr regsT 4 = w64 (as_tp B) /\
getr regsT 1 = Z_to_bv 64 RT_malloc_ra /\ YK0s.ret_ok (Z_to_bv 64 RT_malloc_ra) /\
st_nev S3 < EV_MAX /\
chain_pre ly3 (aview tfibsegs (w_H W3) mem3) regsT (rt_ch cx) /\
In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT (rt_ch cx)) (as_universe B) /\
mo_ok MT S3 (mo_malloc MT (kk + 1)).
Proof.
intros cx ly3 S3 W3 mem3 md3 k acc kk regsT HB HJ Hk0 HMLE Hacc Eab Hkk Ha0 Hsp Hs0 Hra Hgp Htp Vra Vs0.
pose proof HB as (HPRE & Hra0 & _ & _ & _ & _ & _ & _ & Hev & Hlive & _ & Esp1 & _ & _ & _ & HMOK & HT0).
pose proof HPRE as (_ & _ & Hra4 & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : LLVMF_STK = 32768) by reflexivity. assert (Has : ASTACK = 16384) by reflexivity.
pose proof HJ as (_ & HLY3 & _ & _ & _ & _ & Hnev3 & Hk0' & F1 & _).
destruct (sp1_facts (spZ (c_regs cx) + -128) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
rewrite <- Esp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (HUP : forall a, spZ (c_regs cx) <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H (c_W cx)) (c_mem cx) a)
by (intros a Ha; apply F1; rewrite FFS in Hslo; lia).
assert (Qtop64 : ly_top (c_ly cx) <= 2 ^ 64) by lia.
assert (Qal8 : spZ (c_regs cx) mod 8 = 0) by (pose proof (Z.div_mod (spZ (c_regs cx)) 16 ltac:(lia)) as D; rewrite Hal16, Z.add_0_r in D; rewrite D; replace (16 * (spZ (c_regs cx) / 16)) with ((2 * (spZ (c_regs cx) / 16)) * 8) by lia; apply Z_mod_mult).
assert (Hch1 : achain ly3 (aview tfibsegs (w_H W3) mem3) (c_sp1 cx) (spZ (c_regs cx)) (rt_ch cx)).
{ unfold rt_ch. apply (achain_ly_top (c_ly cx)); [destruct HLY3 as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|].
  exact (rt_chain (c_ly cx) _ _ (c_regs cx) (c_sp1 cx) Hch Qtop64 HUP Vra Vs0 Hra4 ltac:(rewrite FFS in Hslo; lia) Qal8 ltac:(lia)). }
assert (Hraw : YK0s.ret_ok (Z_to_bv 64 RT_malloc_ra)) by (apply ret_ok_even; vm_compute; reflexivity).
assert (EraX : raZ regsT = RT_malloc_ra) by (unfold raZ; rewrite Hra; apply unsigned_lit_small; unfold RT_malloc_ra; lia).
split; [exact Ha0|]. split; [unfold MALLOC_MAX; lia|].
split; [rewrite (blocks_bytes_bsum B ly3 S3), Eab, <- (blocks_bytes_bsum B (c_ly cx) (c_S cx)); unfold LIVE_LIB, LIVE_MAX in *; lia|].
split; [lia|]. split; [rewrite Zminus_mod, Hsp1al16, Hal16; reflexivity|]. split; [lia|]. split; [rewrite FFS, Has; lia|].
split; [exact Hgp|]. split; [exact Htp|]. split; [exact Hra|]. split; [exact Hraw|].
split; [unfold RT_EV in Hev; lia|].
split; [apply (achain_chain_pre ly3 _ (c_sp1 cx) (spZ (c_regs cx)) _ _ Hch1); [rewrite Hsp; rewrite FFS in Hslo; lia | exact Hs0 | rewrite EraX; unfold RT_malloc_ra; lia]|].
split.
{ replace (pc_malloc_ra0 (as_code B)) with 0x52df0 by (rewrite HBcode; reflexivity). rewrite (tl_universe B TL).
  apply (rt_trace_in 0x52df0 0x80828 regsT cx); [exact Hra0 | exact EraX | left; split; reflexivity]. }
apply (mok_station MT (c_S cx) S3 (c_T cx) acc (mo_malloc MT (kk + 1)) MTL HMOK HMLE); [apply (mo_malloc_nonneg MT MTL); lia|].
pose proof (mo_malloc_mono MT MTL (kk + 1) (2 ^ 26) ltac:(lia)) as Hmm. pose proof (mo_free_nonneg MT MTL).
unfold ACC0, PIN_NEED in *. lia.
Qed.
Ltac tail_run HS HJ AG fpos F EFA stop :=
  reshok HS;
  lazymatch goal with SH : sh_ok _ _ _ _ _ |- _ =>
  aj_run_to_tok tfibtbl_lib_ok HS HJ SH RTBspan stop;
  try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => awrRT AG fpos F EFA end) end.
Ltac call_run HS HJ AG fpos F EFA :=
  reshok HS;
  lazymatch goal with SH : sh_ok _ _ _ _ _ |- _ =>
  aj_run_tok tfibtbl_lib_ok HS HJ SH RTBspan;
  try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => awrRT AG fpos F EFA end) end.
(* ------------------------------ 0x80820 .. 0x8082c: a0 = k + 1, malloc, the abort test (not taken), the join at ss_Q ------------------------------ *)
Lemma pm_S1_tail : rt_from B MT FP POST ss_Q (INV_Q B MT) -> rt_from B MT FP POST ss_M (INV_M B MT).
Proof.
intros RQ. rt_prelude.
destruct HINV as (Hk0 & Hacc & Eab3 & r & kk & fl & E430 & E431 & E432 & Hkk & Hfl & Hr).
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & Hk0' & _).
relowRT HS AG E10 E11 E32 E10n E11n E32n.
assert (Hkk26 : 0 <= kk < 2 ^ 26).
{ rewrite Hkk. pose proof (nul_idx_le (tl pl)) as L1. unfold pin_k, pin_rest.
  assert (L2 : (length (tl pl) <= length pl)%nat) by (destruct pl; cbn [tl length]; lia). lia. }
assert (Hfl8 : 0 <= fl < 256) by (rewrite Hfl; apply pin_flags_range).
assert (HrR : 4096 <= r <= 140737479966720).
{ rewrite Hr. destruct Hpn as [[Hn0 HpE] | [Hnr Hin]].
  - rewrite Hn0, HpE. cbn. unfold A_EMPTY. lia.
  - assert (Hp3 : In (p, n) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hin).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p n (proj1 HJ3) Hp3) as (_ & Hp4096 & Hpceil & _).
    pose proof (req_size_pos n ltac:(clear - Hnr; lia)) as [_ Hrq].
    replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia). lia. }
(* 0x80820 addi a0,s5,1; 0x80824 jal 0x52b54 *)
call_run HS HJ3 AG fpos F EFA3. clear_frames.
rb HS AG E10 E11 E32 E10n E11n E32n. rebv HS E70 RF B70 B75.
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  assert (D10 : sv_denot Ev (SOff 431 1) = w64 (kk + 1)) by (rewrite denot_lit_U, (U_atom_off _ 431 kk 1); [reflexivity | ewpeel; exact E431 | lia | lia]) end.
rreg_by HS (10%bv : bv 5) (w64 (kk + 1)) D10 Xa0. clear D10.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  assert (Usp3 : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp) end.
lazymatch type of Rsp with getr ?rg 2 = _ =>
  assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp; exact B70);
  assert (Es0X : s0Z rg = spZ regs) by (unfold s0Z; rewrite Rs0; exact Usp3);
  assert (XraX : getr rg 1 = Z_to_bv 64 RT_malloc_ra) by (rewrite Rra; reflexivity);
  assert (XgpX : getr rg 3 = w64 (as_gp B)) by (rewrite Rgp; rewrite (AG 3%nat) by (clear; lia); rewrite (EE 3%nat (@BV 5 3 I) eq_refl); exact Hgp);
  assert (XtpX : getr rg 4 = w64 (as_tp B)) by (rewrite Rtp; rewrite (AG 4%nat) by (clear; lia); rewrite (EE 4%nat (@BV 5 4 I) eq_refl); exact Htp) end.
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 2%nat in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat (@BV 5 1 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat (@BV 5 8 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
pose proof (rdword_of_val_mem tfibsegs _ _ _ _ Vra Qra) as Wra;
pose proof (rdword_of_val_mem tfibsegs _ _ _ _ Vs0 Qs0) as Ws0;
replace (spZ regs + -8) with (spZ regs - 8) in Wra by lia;
replace (spZ regs + -16) with (spZ regs - 16) in Ws0 by lia;
lazymatch goal with HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ ly3 S3 W3 (ms_mem msX) _ _ |- _ =>
destruct (pin_malloc_site (mkRTCX ly S W regs mem md p n pl fpos sp1 E0 T) ly3 S3 W3 (ms_mem msX) _ k acc kk _ HBASE0 HJc Hk0 HMLE Hacc Eab3 Hkk26
  Xa0 EspX Es0X XraX XgpX XtpX Wra Ws0) as (Ma0 & Mn & Mlive & Msp & Mo16 & Mo & Mstk & Mgp & Mtp & Mra & Mraw & Mnev & Mch & MU & Mmok) end end.
clear Vra Vs0.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace 338772 with (pc_wrap_malloc (as_code B)) by (rewrite HBcode; reflexivity).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
  lazymatch goal with HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ ly3 S3 W3 (ms_mem msX) _ _ |- _ =>
  exact (amalloc04_sub tfibsegs B LAWS Hsegs MT AMALLOC4 W3 (ms_regs msX) (ms_mem msX) LLVMF_STK (spZ regs) FP ly S W mem md [(1, fpos)]
    ly3 S3 mdX k (kk + 1) (sp1 - spZ regs) (Z_to_bv 64 RT_malloc_ra) (rt_ch (mkRTCX ly S W regs mem md p n pl fpos sp1 E0 T)) HJc
    Ma0 Mn Mlive Msp Mo16 Mo Mstk Mgp Mtp Mra Mraw Mnev Mch MU Mmok) end end. }
cbv beta. intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & res & -> & HJ4 & HP4 & Ha04 & Hfrs4 & Hres4096 & Eab4 & HK & HMLE4c & _).
pose proof (mle_station MT S S3 S4 acc (mo_malloc MT (kk + 1)) MTL HMLE HMLE4c) as HMLE4.
replace (spZ regs + (sp1 - spZ regs)) with sp1 in HK by lia.
pose proof (proj1 HJ4) as HAR4.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
assert (Hfin4 : In (1, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
assert (Hfrs4' : frames S4 = [(1, fpos)]) by (rewrite Hfrs4; exact Hfrs3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & HFSpres4).
change (fs_frame_bytes 1) with 128 in HFpres4, HFSpres4. change (128 / 8) with 16 in HFSpres4. rewrite !EFA4 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
assert (Hres_in : In (res, kk + 1) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res (kk + 1) HAR4 Hres_in) as (Hp16 & Hp4096 & Hpceil & Hph_ia & _).
pose proof (blk_off_img _ _ _ _ _ _ _ _ HAR4 Hres_in) as Hph_img.
assert (Hrq1 : req_size (kk + 1) = kk + 1) by (unfold req_size; destruct (Z.eqb_spec (kk + 1) 0); lia).
pose proof (sep_block_frame tfibsegs B LAWS ly4 S4 _ _ _ res (kk + 1) 1 fpos HAR4 Hres_in Hfin4) as HdPF.
unfold zdisjoint in HdPF. cbn [fst snd] in HdPF. change (fs_frame_bytes 1) with 128 in HdPF. rewrite EFA4 in HdPF. fold F in HdPF.
rewrite Hrq1 in HdPF, Hpceil, Hph_ia, Hph_img.
reseatL HS HJ4 HP4 [0; 1; 2]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 88%nat) _ _ _ _ _) =>
  eapply (region_kept_ownframe_aj tfibsegs _); [exact HK | evalE AG | exact Hfin3
  | right; unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 1 / 8) with 16; unfold SB; clear; lia
  | intros a Ha Hx; rewrite Hrq1 in Hx; clear - Ha Hx Hp4096 Hpceil Hph_ia Hph_img HF8c HF8lo HF8hi HFceil C1 C3; unfold SB in *; zone_lia
  | intros a Ha; exfalso; clear - Ha; unfold SB in *; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 75%nat) _ _ _ _ _) =>
  eapply (region_kept_ownframe_aj tfibsegs _); [exact HK | evalE AG | exact Hfin3
  | left; rewrite EFA3; fold F; change (fs_frame_bytes 1) with 128; clear; lia
  | intros a Ha Hx; rewrite Hrq1 in Hx; clear - Ha Hx HdPF; lia
  | intros a Ha; first [exfalso; clear - Ha; lia | apply (proj1 (HFpres4 a ltac:(clear - Ha; lia)))] ] end
| keptRT HK HJ4 AG Kgot3 Kgot3 Kcell3 Kcell3 Kguar3 Kguar3 Kuar3 Kuar3 ltac:(idtac; fail) ltac:(idtac; fail)
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS. rebv HS E70 RF B70 B75.
lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict ?Hh ?msx) =>
  let e := eval vm_compute in (sr_get (ss_regs ssx) (10%bv : bv 5)) in
  lazymatch e with SOff ?K 0 =>
    assert (EK : ew Ev K = getr (ms_regs msx) 10) by (rewrite <- sv_denot_SOff0; symmetry; exact (st_ok_restrict_reg tfibsegs Hh Ev ssx msx (10%bv : bv 5) HS));
    cbn [ms_regs mkst] in EK; rewrite Ha04 in EK; unfold w64 in EK;
    pose proof (st_ok_add_fact tfibsegs Ev _ _ K (HPTR 4) HS
      ltac:(clear HS; unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite EK; rewrite unsigned_lit_small by (clear - Hp4096 Hpceil C1 Hkk26; lia);
            change (2 ^ 4) with 16; clear - Hp4096 Hpceil Hp16 C1 Hkk26; lia)) as HS3;
    clear HS; rename HS3 into HS end end.
norm_ss HS.
(* 0x80828 beqz a0 (not taken: 4096 <= res); stop at 0x8082c *)
tail_run HS HJ4 AG fpos F EFA4 0x8082c. clear_frames.
pin_reg HS (10%bv : bv 5) 100%nat q Hq E100.
pin_reg HS (20%bv : bv 5) 101%nat rq Hrq E101.
pin_reg HS (21%bv : bv 5) 102%nat kq Hkq E102.
pin_reg HS (25%bv : bv 5) 103%nat fq Hfq E103.
lazymatch type of EK with ew _ ?K = _ =>
  rewrite (U_atom _ K res) in Hq by first [ewpeel; exact EK | lia] end.
rewrite (U_atom _ 430 r) in Hrq by first [ewpeel; exact E430 | lia].
rewrite (U_atom _ 431 kk) in Hkq by first [ewpeel; exact E431 | lia].
rewrite (U_atom _ 432 fl) in Hfq by first [ewpeel; exact E432 | lia].
subst q rq kq fq.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  pose proof (st_ok_add_fact tfibsegs Ev _ _ 100 (HPTR 4) HS
    ltac:(clear HS; unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; ewpeel; rewrite E100, unsigned_lit_small by (clear - Hp4096 Hpceil C1 Hkk26; lia);
          change (2 ^ 4) with 16; clear - Hp4096 Hpceil Hp16 C1 Hkk26; lia)) as HS3;
  clear HS; rename HS3 into HS;
  pose proof (st_ok_add_fact tfibsegs Ev _ _ 101 (HPTR 0) HS
    ltac:(clear HS; unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; ewpeel; rewrite E101, unsigned_lit_small by (clear - HrR; lia);
          rewrite Z.pow_0_r, Z.mod_1_r; clear - HrR; lia)) as HS3;
  clear HS; rename HS3 into HS;
  pose proof (st_ok_add_fact tfibsegs Ev _ _ 102 (mkAF 0 (2 ^ 26 - 1) 0) HS
    ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; ewpeel; rewrite E102, unsigned_lit_small by (clear - Hkk26; lia);
          rewrite Z.pow_0_r, Z.mod_1_r; clear - Hkk26; lia)) as HS3;
  clear HS; rename HS3 into HS;
  pose proof (st_ok_add_fact tfibsegs Ev _ _ 103 (mkAF 0 255 0) HS
    ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; ewpeel; rewrite E103, unsigned_lit_small by (clear - Hfl8; lia);
          rewrite Z.pow_0_r, Z.mod_1_r; clear - Hfl8; lia)) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS.
ra_join_win HS ss_Q 500%nat pm_Q_deads_bv ltac:(idtac).
let HEv := fresh "HEv" in rebaseE HS AG HEv; clear HEv.
rt_hand RQ HS.
split; [lia|].
split; [pose proof (mo_malloc_mono MT MTL (kk + 1) (2 ^ 26) ltac:(lia)); unfold ACC0 in Hacc; lia|].
exists res, r, kk, fl. split; [exact E100|]. split; [exact E101|]. split; [exact E102|]. split; [exact E103|].
split; [exact Hkk|]. split; [exact Hfl|]. split; [exact Hr|].
rewrite Eab4, Eab3. reflexivity.
Qed.
(* the join at 0x80820: s4 -> 430 (r), s5 -> 431 (k), s9 -> 432 (flags); m_pin pins, m_close joins and hands off *)
Ltac m_pin HS r Hr E430 kk Hkk E431 fl Hfl E432 :=
  pin_reg HS (20%bv : bv 5) 430%nat r Hr E430;
  pin_reg HS (21%bv : bv 5) 431%nat kk Hkk E431;
  pin_reg HS (25%bv : bv 5) 432%nat fl Hfl E432.
Ltac m_close HS AG RM :=
  ra_join_win HS ss_M 450%nat pm_M_deads_bv ltac:(idtac);
  let HEv := fresh "HEv" in rebaseE HS AG HEv; clear HEv; rt_hand RM HS.
Lemma pm_S1_head : rt_from B MT FP POST ss_M (INV_M B MT) -> rt_from B MT FP POST ss_H (INV_0 B MT 0).
Proof.
intros RM. rt_prelude.
pose proof HINV as (Hk0 & Hacc & Eab3).
relowRT HS AG E10 E11 E32 E10n E11n E32n.
assert (HpR : 4096 <= p /\ p + n <= alloc_ceiling).
{ destruct Hpn as [[Hn0 HpE] | [Hnr Hin]].
  - rewrite HpE, Hn0. unfold A_EMPTY. clear - C1. lia.
  - assert (Hp3 : In (p, n) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hin).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p n (proj1 HJ3) Hp3) as (_ & Hp4096 & Hpceil & _).
    pose proof (req_size_pos n ltac:(clear - Hnr; lia)) as [_ Hrq]. clear - Hp4096 Hpceil Hrq. lia. }
add_fact HS 10%nat 4096 140737479966720 E10n ltac:(clear - HpR C1 Hn26; lia).
br_go HS Hc1 E11n.
- (* n = 0 *)
  tail_run HS HJ3 AG fpos F EFA3 0x80820. clear_frames.
  m_pin HS r Hr E430 kk Hkk E431 fl Hfl E432.
  rewrite (U_atom _ 10 p) in Hr by first [ewpeel; exact E10n | lia].
  rewrite U_lit0 in Hkk, Hfl.
  m_close HS AG RM.
  split; [exact Hk0|]. split; [exact Hacc|]. split; [exact Eab3|].
  exists r, kk, fl. split; [exact E430|]. split; [exact E431|]. split; [exact E432|].
  destruct pl as [|x pl']; [|cbn [length] in Hnpl; exfalso; clear - Hnpl Hc1; lia].
  rewrite Hc1. split; [rewrite Hkk; reflexivity|]. split; [rewrite Hfl; reflexivity | rewrite Hr; reflexivity].
- assert (Hpin : In (p, n) (ablocks B ly S)) by (destruct Hpn as [[Hn0 _] | [_ Hin]]; [exfalso; clear - Hn0 Hc1; lia | exact Hin]).
  assert (Hpin3 : In (p, n) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hpin).
  assert (Hrq : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); [exfalso; clear - Hc1 e; lia | reflexivity]).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n (proj1 HJ3) Hpin3) as (_ & _ & _ & HinApp & _). rewrite Hrq in HinApp.
  pose proof (blk_off_img B _ _ _ _ _ p n (proj1 HJ3) Hpin3) as HoffImg. rewrite Hrq in HoffImg.
  pose proof (sep_block_frame tfibsegs B LAWS ly3 S3 _ _ _ p n 1 fpos (proj1 HJ3) Hpin3 Hfin3) as HpF.
  unfold zdisjoint in HpF. cbn [fst snd] in HpF. change (fs_frame_bytes 1) with 128 in HpF. rewrite EFA3 in HpF. fold F in HpF. rewrite Hrq in HpF.
  pose proof (pm_in_byte (mkRTCX ly S W regs mem md p n pl fpos sp1 E0 T) _ _ _ _ _ _ _ 0 HBASE0 HJ3 ltac:(cbn [c_n]; clear - Hc1 Hn26; lia) Hpin3 ltac:(cbn [c_n]; clear - Hc1 Hn26; lia)) as A0.
  cbn [c_p c_pl] in A0. change (Z.to_nat 0) with 0%nat in A0.
  remember (bv_unsigned (nth 0 pl (Z_to_bv 8 0))) as b0 eqn:Hb0.
  assert (R0 : 0 <= b0 < 256) by (rewrite Hb0; pose proof (bv_unsigned_in_range 8 (nth 0 pl (Z_to_bv 8 0))) as X; exact X).
  assert (Hfl0 : b0 = pin_flags pl) by (rewrite Hb0; destruct pl; [cbn [length] in Hnpl; clear - Hnpl Hc1; lia | reflexivity]).
  add_atom_win HS 433%nat (Z_to_bv 64 b0) E433.
  in_region HS (YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 433 0))]) E10n AG.
  rd_run HS HJ3 AG fpos F EFA3 E10n E32n Hpin3 Hrq. clear_frames.
  rb HS AG E10 E11 E32 E10n E11n E32n.
  (* 0x807f0 beqz s5 (s5 = n - 1) *)
  reshok HS. srr_branch_tok tfibtbl_lib_ok HS SHOK RTBspan.
  all: lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc2 end.
  all: hc_bool Hc2 ltac:(fun H => rewrite (U_atom_off _ 11 n (-1)) in H by first [ewpeel; exact E11n | lia]); hc_prop Hc2.
  + (* n = 1: 0x80814 a0 = 0, -> 0x80820 *)
    tail_run HS HJ3 AG fpos F EFA3 0x80820. clear_frames.
    m_pin HS r Hr E430 kk Hkk E431 fl Hfl E432.
    rewrite (U_atom_off _ 10 p 1) in Hr by first [ewpeel; exact E10n | lia].
    rewrite (U_atom_off _ 11 n (-1)) in Hkk by first [ewpeel; exact E11n | lia].
    rewrite U_zext, (U_atom _ 433 b0) in Hfl by first [ewpeel; exact E433 | lia].
    change (2 ^ Z.of_N 8) with 256 in Hfl. rewrite Z.mod_small in Hfl by lia.
    m_close HS AG RM.
    split; [exact Hk0|]. split; [exact Hacc|]. split; [exact Eab3|].
    exists r, kk, fl. split; [exact E430|]. split; [exact E431|]. split; [exact E432|].
    split; [rewrite Hkk; destruct pl as [|x [|y l]]; cbn [length] in Hnpl; [lia | change (Z.of_nat (pin_k [x])) with 0; lia | lia]|].
    split; [rewrite Hfl; exact Hfl0|].
    replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia). exact Hr.
  + (* n > 1: memchr(p + 1, 0, n - 1) at 0x80800 *)
    call_run HS HJ3 AG fpos F EFA3. clear_frames.
    rb HS AG E10 E11 E32 E10n E11n E32n. rebv HS E70 RF B70 B75.
    rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
      assert (D10 : sv_denot Ev (SOff 10 1) = w64 (p + 1)) by (rewrite denot_lit_U, (U_atom_off _ 10 p 1); [reflexivity | ewpeel; exact E10n | lia | lia]);
      assert (D12 : sv_denot Ev (SOff 11 (-1)) = w64 (n - 1)) by (rewrite denot_lit_U, (U_atom_off _ 11 n (-1)); [reflexivity | ewpeel; exact E11n | lia | lia]);
      assert (D11 : sv_denot Ev (SLit 0) = w64 0) by reflexivity end.
    rreg_by HS (10%bv : bv 5) (w64 (p + 1)) D10 Xa0. rreg_by HS (11%bv : bv 5) (w64 0) D11 Xa1.
    rreg_by HS (12%bv : bv 5) (w64 (n - 1)) D12 Xa2. clear D10 D11 D12.
    lazymatch type of Rsp with getr ?rg 2 = _ =>
      assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp; exact B70);
      assert (XraX : getr rg 1 = Z_to_bv 64 RT_memchr_ra) by (rewrite Rra; reflexivity);
      assert (XgpX : getr rg 3 = w64 (as_gp B)) by (rewrite Rgp; rewrite (AG 3%nat) by (clear; lia); rewrite (EE 3%nat (@BV 5 3 I) eq_refl); exact Hgp);
      assert (XtpX : getr rg 4 = w64 (as_tp B)) by (rewrite Rtp; rewrite (AG 4%nat) by (clear; lia); rewrite (EE 4%nat (@BV 5 4 I) eq_refl); exact Htp) end.
    destruct (pin_memchr_site (mkRTCX ly S W regs mem md p n pl fpos sp1 E0 T) _ _ _ _ _ _ _ _ HBASE0 HJ3 Hpin3 ltac:(cbn [c_n]; lia)
      Xa0 Xa1 Xa2 EspX XraX XgpX XtpX) as (_ & _ & _ & _ & Mc & Mn & Mx0 & Mxn & Msrc & Mamr & Mrax & Mhull & Mro).
    rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
    eapply SRr_bind.
    { lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
      exact (aj_memchr_atS tfibsegs B LAWS Hsegs 0x41928 AMEMCHR W3 (ms_regs msX) (ms_mem msX) LLVMF_STK (spZ regs) FP ly S W mem md [(1, fpos)]
        ly3 S3 mdX k (p + 1) 0 (n - 1) (sp1 - spZ regs) (Z_to_bv 64 RT_memchr_ra) HJ3 Xa0 Xa1 Xa2 Mc Mn Mx0 Mxn
        ltac:(rewrite EspX; lia) ltac:(rewrite Zminus_mod, Hsp1al16, Hal16; reflexivity) ltac:(lia) ltac:(rewrite FFS, Hes; lia)
        XgpX XtpX XraX ltac:(apply ret_ok_even; vm_compute; reflexivity) Msrc Mamr Mrax Mhull Mro) end. }
    cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & (kk & Hfb & Ha04) & Hfr4 & Hpres4 & Hio4).
    replace (spZ regs + (sp1 - spZ regs)) with sp1 in Hfr4 by lia.
    destruct Hfb as (Hk01 & Hbef & Hat).
    (* memchr's result is pin_k: the first NUL of the bytes after the flags byte *)
    assert (Hkpin : Z.of_nat (pin_k pl) = kk).
    { rewrite Hnpl in Hat.
      lazymatch type of Hbef with forall i, _ -> exists b, aview _ (w_H ?Wx) ?mx _ = _ /\ _ =>
      apply (pm_pin_k_of pl (aview tfibsegs (w_H Wx) mx) p kk); [lia | | lia | exact Hbef | exact Hat] end.
      intros i Hi. rewrite <- Hnpl in Hi.
      exact (pm_in_byte (mkRTCX ly S W regs mem md p n pl fpos sp1 E0 T) _ _ _ _ _ _ _ i HBASE0 HJ3 ltac:(cbn [c_n]; lia) Hpin3 ltac:(cbn [c_n]; lia)). }
    clear Hbef Hat Msrc Mamr Mrax Mhull Mro.
    reseatL HS HJ4 HP4 [1; 2; 3]%nat AG
      ltac:(idtac; eapply region_kept_aview; [evalE AG
        | intros a Ha; apply Hfr4; clear - Ha Hsp1 Hceil Hslo Hstk0 FFS C1 HFceil HF4096 HF8hi HF8lo Hshi H47; unfold ESTACK, SB in *; lia
        | exact Hpres4]).
    relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS. rebv HS E70 RF B70 B75.
    lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) (10%bv : bv 5)) in
      lazymatch e with SOff ?K 0 =>
        assert (EK : ew Ev K = getr (ms_regs msx) 10) by (rewrite <- sv_denot_SOff0; symmetry; exact (st_ok_restrict_reg tfibsegs Hh Ev ssx msx (10%bv : bv 5) HS)) end end.
    cbn [ms_regs mkst] in EK. rewrite Ha04 in EK. unfold w64 in EK.
    revert EK. destruct (Z.ltb_spec kk (n - 1)) as [Hlt | Hge]; intros EK.
    * (* found: a0 = p + 1 + kk <> 0, 0x8081c s5 = a0 - s4 *)
      reshok HS. srr_branch_tok tfibtbl_lib_ok HS SHOK RTBspan.
      all: lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc3 end.
      all: lazymatch type of EK with ew _ ?K = _ =>
        hc_bool Hc3 ltac:(fun H => rewrite (U_atom _ K (p + 1 + kk)) in H by first [ewpeel; exact EK | lia]) end; hc_prop Hc3.
      -- tail_run HS HJ4 AG fpos F EFA3 0x80820. clear_frames.
         m_pin HS r Hr E430 kq Hkq E431 fl Hfl E432.
         rewrite (U_atom_off _ 10 p 1) in Hr by first [ewpeel; exact E10n | lia].
         lazymatch type of EK with ew _ ?K = _ =>
           rewrite (U_neg_add _ 10 K p (p + 1 + kk)) in Hkq by first [ewpeel; exact E10n | ewpeel; exact EK | lia] end.
         rewrite U_zext, (U_atom _ 433 b0) in Hfl by first [ewpeel; exact E433 | lia].
         change (2 ^ Z.of_N 8) with 256 in Hfl. rewrite Z.mod_small in Hfl by lia.
         m_close HS AG RM.
         split; [exact Hk0|]. split; [exact Hacc|]. split; [exact Eab3|].
         exists r, kq, fl. split; [exact E430|]. split; [exact E431|]. split; [exact E432|].
         split; [rewrite Hkq, Hkpin; lia|]. split; [rewrite Hfl; exact Hfl0|].
         replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia). exact Hr.
      -- exfalso. lia.
    * (* not found: a0 = 0, kk = n - 1 *)
      reshok HS. srr_branch_tok tfibtbl_lib_ok HS SHOK RTBspan.
      all: lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc3 end.
      all: lazymatch type of EK with ew _ ?K = _ =>
        hc_bool Hc3 ltac:(fun H => rewrite (U_atom _ K 0) in H by first [ewpeel; exact EK | lia]) end; hc_prop Hc3.
      -- exfalso. lia.
      -- tail_run HS HJ4 AG fpos F EFA3 0x80820. clear_frames.
         m_pin HS r Hr E430 kq Hkq E431 fl Hfl E432.
         rewrite (U_atom_off _ 10 p 1) in Hr by first [ewpeel; exact E10n | lia].
         rewrite (U_atom_off _ 11 n (-1)) in Hkq by first [ewpeel; exact E11n | lia].
         rewrite U_zext, (U_atom _ 433 b0) in Hfl by first [ewpeel; exact E433 | lia].
         change (2 ^ Z.of_N 8) with 256 in Hfl. rewrite Z.mod_small in Hfl by lia.
         m_close HS AG RM.
         split; [exact Hk0|]. split; [exact Hacc|]. split; [exact Eab3|].
         exists r, kq, fl. split; [exact E430|]. split; [exact E431|]. split; [exact E432|].
         split; [rewrite Hkq, Hkpin; lia|]. split; [rewrite Hfl; exact Hfl0|].
         replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia). exact Hr.
Qed.
(* S1: 0x807d0 .. 0x80828, from ss_H to ss_Q *)
Lemma pm_S1 : rt_from B MT FP POST ss_Q (INV_Q B MT) -> rt_from B MT FP POST ss_H (INV_0 B MT 0).
Proof. intros RQ. exact (pm_S1_head (pm_S1_tail RQ)). Qed.
End d.
End b.
