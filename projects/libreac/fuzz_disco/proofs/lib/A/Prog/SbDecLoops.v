From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require sb_dec_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition SBD_L1 : Z := 0x110.
Definition SBD_L1X : Z := 0x150.
Definition SBD_L2 : Z := 0x1a8.
Definition SBD_L2X : Z := 0x254.
Definition sbd_keep_regs (regs regs2 : bvmap 5 word) (cl : list Z) : Prop :=
  forall r, 0 <= r < 32 -> ~ In r cl -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Section h.
Variable B : asyms.
Definition sbd_wbytes (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (D n : Z) : Prop :=
  forall a, D <= a < D + n ->
    awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a.
Definition sbd_L1_run (fq : YK11.FPState) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (v D : Z) : Prop :=
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  0 <= v < 2 ^ 31 -> 0 <= D -> D + 3 <= 2 ^ 63 ->
  sbd_wbytes STK sp0 FP ly S own lyc Sc W memc D 3 ->
  getr regs 20 = w64 v -> getr regs 15 = w64 0 -> getr regs 11 = w64 0 -> getr regs 14 = w64 D ->
  getr regs 5 = w64 1717986919 -> getr regs 12 = w64 10 -> getr regs 13 = w64 (-20) -> getr regs 6 = w64 2 ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_sb_dec + SBD_L1) regs memc mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = cfg_at (fx := fq) SEGS (BASE + AF_sb_dec + SBD_L1X) regs2 mem2 md2 /\
       ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
       sbd_keep_regs regs regs2 [7; 11; 15; 20; 28; 29; 30; 31] /\
       getr regs2 11 = w64 (Z.of_nat (length (sb_dec_c.sb_dec_lsd v 3))) /\
       getr regs2 15 = w64 (Z.of_nat (length (sb_dec_c.sb_dec_lsd v 3))) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (D <= a < D + Z.of_nat (length (sb_dec_c.sb_dec_lsd v 3))) ->
          aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a) /\
       (forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a) /\
       garr8 SEGS (mrestrict (w_H W) mem2) D (sb_dec_c.sb_dec_lsd v 3)).
Definition sbd_L1_spec : Prop :=
  forall fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs v D,
  sbd_L1_run fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs v D.
Definition sbd_L2_run (fq : YK11.FPState) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (A p cap n0 ov0 D : Z) (buf : list Z) : Prop :=
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  A mod 8 = 0 -> 4096 <= A -> A + 28 <= 2 ^ 47 -> (A + 28 <= 2147446784 \/ 17594333495296 <= A) ->
  0 <= p < 2 ^ 64 -> 0 <= cap < 2 ^ 64 -> 0 <= n0 -> n0 + 1 < 2 ^ 64 - 3 -> 0 <= ov0 < 2 ^ 32 ->
  val_mem SEGS (mrestrict (w_H W) memc) A 8 p ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 8) 8 cap ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 16) 8 n0 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 24) 4 ov0 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF A 28 ->
  sbd_wbytes STK sp0 FP ly S own lyc Sc W memc (A + 16) 12 ->
  (1 <= length buf <= 3)%nat -> Forall (fun c => 0 <= c < 256) buf ->
  garr8 SEGS (mrestrict (w_H W) memc) D buf -> 4096 <= D -> D + 3 <= 2 ^ 47 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF D (Z.of_nat (length buf)) ->
  (A + 28 <= D \/ D + Z.of_nat (length buf) <= A) ->
  (0 < sb_dec_c.sb_dec_room cap n0 ->
     p + cap <= 2 ^ 64 /\
     in_app (p + n0) (Z.min (Z.of_nat (length buf)) (sb_dec_c.sb_dec_room cap n0)) /\
     range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (p + n0)
       (Z.min (Z.of_nat (length buf)) (sb_dec_c.sb_dec_room cap n0)) /\
     sbd_wbytes STK sp0 FP ly S own lyc Sc W memc (p + n0)
       (Z.min (Z.of_nat (length buf)) (sb_dec_c.sb_dec_room cap n0)) /\
     (p + n0 + Z.min (Z.of_nat (length buf)) (sb_dec_c.sb_dec_room cap n0) <= A \/ A + 28 <= p + n0) /\
     (p + n0 + Z.min (Z.of_nat (length buf)) (sb_dec_c.sb_dec_room cap n0) <= D \/
      D + Z.of_nat (length buf) <= p + n0)) ->
  getr regs 11 = w64 (A + 16) -> getr regs 12 = w64 (A + 8) -> getr regs 13 = w64 (A + 24) ->
  getr regs 5 = w64 (- Z.of_nat (length buf)) ->
  getr regs 14 = w64 (D + Z.of_nat (length buf) - 1) -> getr regs 6 = w64 (D + Z.of_nat (length buf) - 1) ->
  getr regs 7 = w64 (SHADOW_OFF + A / 8) -> getr regs 28 = w64 (SHADOW_OFF + (A + 16) / 8) ->
  getr regs 29 = w64 (SHADOW_OFF + (A + 8) / 8) -> getr regs 30 = w64 (SHADOW_OFF + (A + 24) / 8) ->
  getr regs 31 = w64 3 -> getr regs 19 = w64 1 -> getr regs 18 = w64 A -> getr regs 21 = w64 SHADOW_OFF ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_sb_dec + SBD_L2) regs memc mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = cfg_at (fx := fq) SEGS (BASE + AF_sb_dec + SBD_L2X) regs2 mem2 md2 /\
       ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
       sbd_keep_regs regs regs2 [5; 6; 14; 15; 20; 22; 23] /\
       val_mem SEGS (mrestrict (w_H W) mem2) (A + 16) 8
         (n0 + Z.min (Z.of_nat (length buf)) (sb_dec_c.sb_dec_room cap n0)) /\
       val_mem SEGS (mrestrict (w_H W) mem2) (A + 24) 4
         (if sb_dec_c.sb_dec_room cap n0 <? Z.of_nat (length buf) then 1 else ov0) /\
       (0 < sb_dec_c.sb_dec_room cap n0 ->
          garr8 SEGS (mrestrict (w_H W) mem2) (p + n0)
            (firstn (Z.to_nat (Z.min (Z.of_nat (length buf)) (sb_dec_c.sb_dec_room cap n0))) (rev buf))) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (A + 16 <= a < A + 28) ->
          ~ (0 < sb_dec_c.sb_dec_room cap n0 /\ p + n0 <= a <
               p + n0 + Z.min (Z.of_nat (length buf)) (sb_dec_c.sb_dec_room cap n0)) ->
          aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a) /\
       (forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a)).
Definition sbd_L2_spec : Prop :=
  forall fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A p cap n0 ov0 D buf,
  sbd_L2_run fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A p cap n0 ov0 D buf.
End h.
End f.
End d.
