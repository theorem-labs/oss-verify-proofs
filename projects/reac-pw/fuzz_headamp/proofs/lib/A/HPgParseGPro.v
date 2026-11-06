(* reac-pw/fuzz_headamp: the image-free prologue pieces of the walks of reac_headamp_prop_parse_result in image A
   (fuzz_headamp.asan, lib/A/HPgParseE.v) and image B (fuzz_headamp.asan-ubsan, lib/AU/HPgParseE.v). Statement and
   glue only; proves no function (kind: segment lemma).

   Both images open with `addi sp,sp,-0x100`, thirteen `sd`, one `fsd fs0,0x90(sp)`, `addi s0,sp,0x100` and
   `andi sp,sp,-0x20`. The symbolic engine of lib/Reusable (YP0l.sym_step) has no case for FStore, so the walk is
   cut at the `fsd`: a chunk ends before it, the instruction is stepped here, and a new chunk starts after it.
   hgp_fsd is that step with the caller's journal carried over the eight bytes it writes; the other lemmas are the
   small memory facts the hand-over needs (a value read back from the written word, and a value kept by a later
   chunk whose write windows miss it). Every pc is an argument. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0e YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgParseFP.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis Hwx : wx_segs_nowrap segs.

(* ================= the bytes a store leaves ================= *)
Lemma hgp_u64 : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a.
Proof. intros a Ha. apply unsigned_lit_small. exact Ha. Qed.

(* outside [a, a + |bs|) the memory is the old one *)
Lemma hgp_wbytes_out : forall (m : word -> option byte) (a : Z) (bs : list byte) (x : word),
0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 -> (0 < length bs)%nat ->
(bv_unsigned x < a \/ a + Z.of_nat (length bs) <= bv_unsigned x) ->
wbytes m (Z_to_bv 64 a) bs x = m x.
Proof.
intros m a bs x Ha Hn Hp Hx.
assert (Hu : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; lia).
destruct Hx as [Hlo | Hhi].
- apply wbytes_below; rewrite Hu; lia.
- apply wbytes_above; rewrite Hu; lia.
Qed.

(* the bytes a word is stored as (the induction of proofs/reac-pw/fuzz_role/lib/A/RPgParseBase.v,
   nth_error_le_bytes, restated for nth) *)
Lemma hgp_nth_le : forall n z k, (k < n)%nat ->
nth k (Z_to_le_bytes n z) (Z_to_bv 8 0) = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k Hk; [lia|].
destruct k as [|k]; cbn [Z_to_le_bytes nth].
- change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
- rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.

Lemma hgp_le_byte_eq : forall (v : word) k, (k < 8)%nat ->
Z_to_bv 8 (Z.shiftr (bv_unsigned v) (8 * Z.of_nat k)) = Z_to_bv 8 (YO0f.le_byte (bv_unsigned v) 8 k).
Proof.
intros v k Hk. unfold YO0f.le_byte.
pose proof (bv_unsigned_in_range 64 v) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
rewrite (Z.mod_small (bv_unsigned v) (2 ^ (8 * Z.of_nat 8))) by (change (8 * Z.of_nat 8) with 64; lia).
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite Zmod_mod. reflexivity.
Qed.

(* the 8 bytes of a word the store wrote, read back as a value *)
Lemma hgp_wbytes_val : forall (H : word -> bool) (m : word -> option byte) (a : Z) (v : word),
0 <= a -> a + 8 <= 2 ^ 64 ->
(forall i, 0 <= i < 8 -> H (Z_to_bv 64 (a + i)) = false) ->
val_mem segs (mrestrict H (wbytes m (Z_to_bv 64 a) (word_to_le_bytes 8 v))) a 8 (bv_unsigned v).
Proof.
intros H m a v Ha H8 Hh k Hk.
assert (Hlen : length (word_to_le_bytes 8 v) = 8%nat) by apply length_N_to_le_bytes.
assert (Hu : bv_unsigned (Z_to_bv 64 a) = a) by (apply hgp_u64; lia).
unfold mbyte, mrestrict.
rewrite (Hh (Z.of_nat k) ltac:(lia)).
replace (Z_to_bv 64 (a + Z.of_nat k)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 a) + Z.of_nat k))
  by (rewrite Hu; reflexivity).
rewrite (YK0e.AX2S.wbytes_nth (word_to_le_bytes 8 v) m (Z_to_bv 64 a) k ltac:(rewrite Hu, Hlen; lia)
  ltac:(rewrite Hlen; lia)).
f_equal. unfold word_to_le_bytes. rewrite (hgp_nth_le 8 (bv_unsigned v) k Hk).
apply hgp_le_byte_eq. exact Hk.
Qed.
(* a value kept by a run whose write windows miss its bytes *)
Lemma hgp_val_mem_kept : forall (H : word -> bool) (m m' : word -> option byte) a n v,
val_mem segs (mrestrict H m) a n v ->
(forall i, 0 <= i < Z.of_nat n -> aview segs H m' (a + i) = aview segs H m (a + i)) ->
val_mem segs (mrestrict H m') a n v.
Proof.
intros H m m' a n v Hv Hk k Hk8. rewrite <- (Hv k Hk8).
apply (mbyte_of_aview segs). apply Hk. lia.
Qed.

(* store_ok from presence (the argument of proofs/reac-pw/fuzz_headamp/lib/Reusable/YI04.v
   store_ok_of_present, which is stated over a malloc_syms record this file does not have) *)
Lemma hgp_store_ok : forall (m : word -> option byte) n a,
(forall i, 0 <= i < Z.of_nat n -> exists b, m (Z_to_bv 64 (a + i)) = Some b) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
RiscvSemantics.store_ok segs m (Z_to_bv 64 a) n = true.
Proof.
intros m n a Hp Ha Hnw. destruct n as [|n']; [reflexivity|].
apply store_ok_of_all; [rewrite unsigned_lit_small by lia; lia|].
intros x Hx. rewrite unsigned_lit_small in Hx by lia.
destruct (Hp (bv_unsigned x - a) ltac:(lia)) as [b Hb].
replace (a + (bv_unsigned x - a)) with (bv_unsigned x) in Hb by lia.
rewrite Z_to_bv_bv_unsigned in Hb. unfold wview. rewrite Hb. discriminate.
Qed.

(* a run keeps every byte outside the zone its write windows lie in (the argument of
   proofs/reac-pw/fuzz_role/lib/A/RPgParseE.v, kept_run_pe) *)
Lemma hgp_kept_run : forall (Zn : Z -> Prop) E rs (H : word -> bool) (m0 m1 m2 : word -> option byte),
(forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview segs H m1 a = aview segs H m0 a) ->
frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
(forall a, in_wrange E rs a -> Zn a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview segs H m2 a = aview segs H m0 a.
Proof.
intros Zn E rs H m0 m1 m2 HK HF HW a Ha Hz. rewrite <- (HK a Ha Hz). unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha.
intros X. exact (Hz (HW a X)).
Qed.

(* a byte-level change set, as a view equality *)
Lemma hgp_kept_of_eq : forall (Zn : Z -> Prop) (H : word -> bool) (m0 m1 : word -> option byte),
(forall y : word, ~ Zn (bv_unsigned y) -> m1 y = m0 y) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview segs H m1 a = aview segs H m0 a.
Proof.
intros Zn H m0 m1 Hc a Ha Hz. unfold aview, mbyte, mrestrict.
rewrite (Hc (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. exact Hz.
Qed.

(* ================= the fsd between two chunks ================= *)
(* One `fsd rs2, imm(rs1)` at pc p of a code table: the caller's journal is carried over the eight bytes it writes
   (they are write bytes of the journal), the written word is readable, every other byte is unchanged, and the
   memory only grows. *)
Lemma hgp_fsd : forall (tbl : ctable) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  p q wz (rs1 rs2 : bv 5) (imm : bv 12) base a
  STK sp0 FP ly S W0 mem0 md0 own lyc Sc k (Q : world segs -> config -> Prop),
table_ok segs tbl ->
clookup tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
decode_any (Z_to_bv 32 wz) = Some (FStore FMT_D rs1 rs2 imm, 4%Z) -> q = p + 4 ->
getr regs rs1 = Z_to_bv 64 base -> a = base + bv_signed imm -> 0 <= a -> a + 8 <= 2 ^ 64 ->
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
(forall i, 0 <= i < 8 -> apresent (w_H W) mem (a + i)) ->
(forall i, 0 <= i < 8 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own (a + i)) ->
(forall (mem' : word -> option byte) (md' : Model),
 (forall x : word, bv_unsigned x < a \/ a + 8 <= bv_unsigned x -> mem' x = mem x) ->
 val_mem segs (mrestrict (w_H W) mem') a 8 (bv_unsigned (Sem.reg_get (@fp_regs fx) rs2)) ->
 ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
 same_io md md' ->
 (forall x, apresent (w_H W) mem x -> apresent (w_H W) mem' x) ->
 SRr segs W (mkCfg (@mkst fx regs (Z_to_bv 64 q) mem' (seg_rom segs)) md') Q) ->
SRr segs W (mkCfg (@mkst fx regs (Z_to_bv 64 p) mem (seg_rom segs)) md) Q.
Proof.
intros tbl W regs mem md p q wz rs1 rs2 imm base a STK sp0 FP ly S W0 mem0 md0 own lyc Sc k Q
  Htbl Hc He Hd Hq Hrs Ha Ha0 Ha8 HJ Hpres Hwr Hk.
pose proof (AR_laws_ok segs B) as LAWS.
set (bs := word_to_le_bytes 8 (Sem.reg_get (@fp_regs fx) rs2)).
assert (Hlen : length bs = 8%nat) by apply length_N_to_le_bytes.
assert (Hhid : forall i, 0 <= i < 8 -> w_H W (Z_to_bv 64 (a + i)) = false)
by (intros i Hi; exact (proj1 (Hpres i Hi))).
(* the step on the restricted memory *)
assert (Hok : RiscvSemantics.store_ok segs (mrestrict (w_H W) mem) (Z_to_bv 64 a) 8 = true).
{ apply (hgp_store_ok (mrestrict (w_H W) mem) 8 a); [|lia|cbn [Z.of_nat]; lia].
  intros i Hi. cbn [Z.of_nat] in Hi. destruct (Hpres i ltac:(lia)) as [Hh [b Hb]].
  exists b. unfold mrestrict. rewrite Hh. exact Hb. }
set (ms := @mkst fx regs (Z_to_bv 64 p) mem (seg_rom segs)).
assert (Hr : restrict (w_H W) ms = @mkst fx regs (Z_to_bv 64 p) (mrestrict (w_H W) mem) (seg_rom segs))
by (subst ms; apply restrict_mkst_fx).
eapply (SRr_step segs Hwx W ms _ md Q); [reflexivity | |].
{ rewrite Hr.
  exact (hfp_tw_fsd segs tbl Htbl fx regs (mrestrict (w_H W) mem) (seg_rom segs) p q wz rs1 rs2 imm base a
    Hc He Hd Hq Hrs Ha Hok). }
intros md' Hsame. fold bs.
(* the memory after the step, as a function *)
set (mem' := fun x : word => if w_H W x then mem x else wbytes (mrestrict (w_H W) mem) (Z_to_bv 64 a) bs x).
assert (Hun : unrestrict (w_H W) (ms_mem ms) (@mkst fx regs (Z_to_bv 64 q)
   (wbytes (mrestrict (w_H W) mem) (Z_to_bv 64 a) bs) (seg_rom segs))
 = @mkst fx regs (Z_to_bv 64 q) mem' (seg_rom segs)).
{ unfold unrestrict, munrestrict, mem'. subst ms. cbn [ms_mem ms_regs ms_pc_val ms_fregs ms_fcsr ms_rom ms_svc_pending ms_resv mkst].
  f_equal. }
rewrite Hun.
assert (Hu : bv_unsigned (Z_to_bv 64 a) = a) by (apply hgp_u64; lia).
(* outside the eight bytes, mem' is mem *)
assert (Hout : forall x : word, bv_unsigned x < a \/ a + 8 <= bv_unsigned x -> mem' x = mem x).
{ intros x Hx. unfold mem'. destruct (w_H W x) eqn:Hh; [reflexivity|].
  rewrite (hgp_wbytes_out (mrestrict (w_H W) mem) a bs x ltac:(lia) ltac:(rewrite Hlen; lia)
    ltac:(rewrite Hlen; lia) ltac:(rewrite Hlen; cbn [Z.of_nat]; lia)).
  unfold mrestrict. rewrite Hh. reflexivity. }
(* inside, mem' holds the stored word *)
assert (Hin : forall i, 0 <= i < 8 -> mem' (Z_to_bv 64 (a + i)) =
  wbytes (mrestrict (w_H W) mem) (Z_to_bv 64 a) bs (Z_to_bv 64 (a + i))).
{ intros i Hi. unfold mem'. rewrite (Hhid i Hi). reflexivity. }
assert (Hvm : val_mem segs (mrestrict (w_H W) mem') a 8 (bv_unsigned (Sem.reg_get (@fp_regs fx) rs2))).
{ intros kk Hkk. unfold mbyte, mrestrict.
  rewrite (Hhid (Z.of_nat kk) ltac:(lia)).
  rewrite (Hin (Z.of_nat kk) ltac:(lia)).
  pose proof (hgp_wbytes_val (w_H W) (mrestrict (w_H W) mem) a (Sem.reg_get (@fp_regs fx) rs2)
    ltac:(lia) ltac:(lia) Hhid kk Hkk) as Hv.
  unfold mbyte, mrestrict in Hv. rewrite (Hhid (Z.of_nat kk) ltac:(lia)) in Hv. exact Hv. }
(* memory grows and every byte stays present *)
assert (Hgr : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem')).
{ intros x Hx. unfold mrestrict in Hx |- *. destruct (w_H W x) eqn:Hh; [exact Hx|].
  unfold mem'. rewrite Hh.
  destruct (Z_lt_le_dec (bv_unsigned x) a) as [Hlt|Hge].
  - rewrite (hgp_wbytes_out (mrestrict (w_H W) mem) a bs x ltac:(lia) ltac:(rewrite Hlen; lia)
      ltac:(rewrite Hlen; lia) ltac:(left; lia)).
    unfold mrestrict. rewrite Hh. exact Hx.
  - destruct (Z_lt_le_dec (bv_unsigned x) (a + 8)) as [Hlt2|Hge2].
    + replace x with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 a) + (bv_unsigned x - a)))
      by (rewrite Hu; replace (a + (bv_unsigned x - a)) with (bv_unsigned x) by lia; apply Z_to_bv_bv_unsigned).
      rewrite <- (Z2Nat.id (bv_unsigned x - a)) by lia.
      rewrite (YK0e.AX2S.wbytes_nth bs (mrestrict (w_H W) mem) (Z_to_bv 64 a) (Z.to_nat (bv_unsigned x - a))
        ltac:(rewrite Hu, Hlen; lia) ltac:(rewrite Hlen; lia)).
      discriminate.
    + rewrite (hgp_wbytes_out (mrestrict (w_H W) mem) a bs x ltac:(lia) ltac:(rewrite Hlen; lia)
        ltac:(rewrite Hlen; lia) ltac:(right; rewrite Hlen; cbn [Z.of_nat]; lia)).
      unfold mrestrict. rewrite Hh. exact Hx. }
assert (Hpr' : forall x, apresent (w_H W) mem x -> apresent (w_H W) mem' x)
by (intros x Hx; eapply apresent_grows; [exact Hgr | exact Hx]).
(* the journal over the new memory *)
assert (HJ' : ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k).
{ eapply (ajournal_exec segs B LAWS segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k mem' md'
    (fun z => a <= z < a + 8) HJ).
  - intros x Hx. unfold mrestrict. destruct (w_H W x) eqn:Hh; [reflexivity|].
    rewrite (Hout x ltac:(lia)). reflexivity.
  - exact Hgr.
  - intros x Hh. unfold mem'. rewrite Hh. reflexivity.
  - exact Hsame.
  - intros z Hz. replace z with (a + (z - a)) by lia. apply Hwr. lia. }
apply (Hk mem' md' Hout Hvm HJ' ltac:(apply same_io_materialized; exact Hsame) Hpr').
Qed.

End g.
