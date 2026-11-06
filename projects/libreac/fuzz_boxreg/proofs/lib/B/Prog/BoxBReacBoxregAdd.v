(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the head-amp table layout and the contract and walk of reac_headamp_tx_effective on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/HeadampTxEffective.v, with its module paths, module names and numbers changed; 2468 of its 2550 lines of code are new or changed and 480 lines of the source are left out. *)
(* reac_boxreg_add (fuzz_boxreg.asan-ubsan 0x81f68, 205 instructions; C: libreac src/reac_boxreg.c:86-120): the
   contract of the ASan+UBSan build's code. The function takes an 80-byte frame on the machine stack
   (addi sp,sp,-80) and returns -1 when nch is not an even width 2..40 (addiw/bltu 0x81f9c-0x81fa4, andi 0x81fac)
   or wider than r->fabric (lw r + 284, 0x81fe0), or when mac_is_zero (mac) (call 0x81fec) is nonzero; else the
   index reac_boxreg_find (r, mac) gives (call 0x82034) when it is >= 0; else it binds the first row i < n whose
   MAC is zero (inlined test 0x820a0-0x820d8) and whose nch (r + 56i + 12) is nch with
   __asan_memcpy (r + 56i, mac, 6) (0x821f4) and returns i; else -1 when n >= 5 (0x82134) or when
   lowest_free_base (r, nch) (call 0x82140) is -1; else it clears row n with __asan_memset (r + 56n, 0, 56)
   (0x82184), copies the MAC with __asan_memcpy (r + 56n, mac, 6) (0x82194), stores the base at r + 56n + 8 and
   nch at r + 56n + 12, stores n + 1 at r + 280, and returns n (sext.w 0x81ff8).
   It writes nothing outside its own frame and the 288-byte registry block r.
   The memory model is Pau's plain one (lib/Prog/reac_boxreg_add_c.v add_out over lib/Prog/Boxreg.v), used as it
   is. add_out's two writing cases are BoxregUpd.v's bind_bytes bs M z (= upd_bytes bs (Z.to_nat (56 * z)) M)
   and new_row_bytes bs (add_row M b k) (= add_bytes bs M b k), the same terms after unfolding.
   Where the MAC is: mac points to the harness's local uint8_t mac[6] (fuzz/fuzz_boxreg.c:206, declared in the
   loop body), at offset 0x20 of the 0x1a0-byte frame LLVMFuzzerTestOneInput takes from __asan_stack_malloc_3
   (0x8001c; frame + 0x20 is stored at 0x801fc-0x80204 and passed as a1 at the calls 0x809c8 / 0x80a60). So the
   premise names it as an object of a side-stack frame, afobj p 6 (the form of grant's CtrlChecksumVerify.v and
   cgif lib/A/ACei.v), and gives its 6 bytes M.
   Hazards.
   (1) The registry struct is 288 bytes: 5 rows of 56 bytes (mac +0..6, base +8, nch +12, established +16,
       pinned +20, name +24..+56) in 0..280, n at +280, fabric at +284.
   (2) afobj holds only on the fake-stack path: when the runtime's detect_stack_use_after_return flag is 0 the
       harness takes its fallback (0x80028-0x8004c: the frame on the machine stack below its own), and mac is
       then in the caller's stack window, which afobj does not cover. cgif's model (stack_malloc_progressP) always
       gives the fake frame.
   (3) Stack: the callees' STK constants are taken from their files (BoxBReacBoxregFind.v, BoxBLowestFreeBase.v,
       BoxBMacIsZero.v). reac_boxreg_find calls bcmp (BS___interceptor_trampoline_bcmp, abcmp_realizes,
       2 * ESTACK; CONVENTIONS section 4) and mac_is_zero: REAC_BOXREG_FIND_STKB = 80 + Z.max MAC_IS_ZERO_STKB
       (2 * ESTACK) is the largest, above lowest_free_base's 64 + RANGE_TAKEN_STKB, mac_is_zero's 16 + ESTACK and
       the memcpy / memset wrappers' ESTACK; the Z.max below says so without depending on that order.
   (4) The int nch arrives sign-extended (LP64 ABI) and the code compares the whole register (blt 0x81fe4,
       beq 0x820f8), so the premise is -2^31 <= k < 2^31, as in the plain contract.
   (5) UBSan traps: every check branches to `unimp` at 0x821fc (word 0xc0001073, csrrw zero,cycle,zero: an
       illegal-instruction trap that the "no csr" scan by mnemonic does not count). They are: r = NULL (0x81fb4)
       and r mod 4 <> 0 (0x81fbc), refuted by the allocator's block law (a block's address is a multiple of 16
       and at least 4096); the row index i = 5 (0x8207c) and n > 5 (0x82160), refuted by boxreg_inv (n <= 5);
       the pointer overflows r + 56i (0x8208c, 0x8209c, 0x82170), refuted by r + 288 < 2^47; the signed
       overflow of n + 1 (0x821d8), refuted by n <= 4 there.
   (6) Shadow-checked accesses: r + 284, r + 280, r + 56i + 12, the row MAC bytes, the store targets r + 56n + 8,
       r + 56n + 12, r + 280 (block shadow from AR, In (r, 288) (ablocks)); the MAC is read by mac_is_zero,
       reac_boxreg_find and __asan_memcpy (afobj's range_addressable). The __asan_report_* branches are refuted
       from these.
   (7) Apart from the trap word of (5), which is never reached, no f* / csr instruction occurs in the function
       (measured), so the fixed {fx} is sound.
   Image difference: the asan build (lib/A/Prog/ReacBoxregAdd.v) inlines mac_is_zero for the MAC and has no
   UBSan traps; the result and the written bytes are the same. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaJournal BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBReacBoxregInit.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require
BoxBReacBoxregFind BoxBLowestFreeBase BoxBMacIsZero.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg reac_boxreg_add_c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YImgTop YK0j YP00 YL02 YL09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaStep YC81 YC4b.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBPaLib YC1g YC1h BoxBFrame YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require BoxregUpd reac_boxreg_add_inv lowest_free_base_c
reac_boxreg_find_c BoxregStep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).
(* The function's address in the image and the stack it needs: its own 80-byte frame and, below it, the largest
   need of its callees (reac_boxreg_find, lowest_free_base, mac_is_zero, and ESTACK for the memcpy / memset
   wrappers). *)
Definition AB_reac_boxreg_addP : Z := BASE + AF_reac_boxreg_add.
Definition REAC_BOXREG_ADD_STKB : Z :=
  80 + Z.max BoxBReacBoxregFind.REAC_BOXREG_FIND_STKB
         (Z.max BoxBLowestFreeBase.LOWEST_FREE_BASE_STKB (Z.max BoxBMacIsZero.MAC_IS_ZERO_STKB ESTACK)).
Section h.
Variable B : asyms.
Definition tbreac_boxreg_add_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md (r k : Z) (bs M : list byte)
  : world SEGS -> config -> Prop :=
apost_base SEGS B REAC_BOXREG_ADD_STKB [(r, r + REG_SIZEB)] regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' =>
ly' = ly /\ S' = S /\ W' = W /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
exists z bs', getr regs' 10 = w64 z /\ reac_boxreg_add_c.add_out bs M k z bs' /\
(forall i, 0 <= i < REG_SIZEB ->
  aview SEGS (w_H W') mem' (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs' (Z_to_bv 8 0))))).
Definition tbreac_boxreg_add_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (r p k : Z) (bs M : list byte),
afn_pre SEGS B REAC_BOXREG_ADD_STKB ly S W regs mem md ch ->
getr regs 10 = w64 r -> getr regs 11 = w64 p -> getr regs 12 = w64 k -> -2^31 <= k < 2^31 ->
In (r, REG_SIZEB) (ablocks B ly S) ->
(forall i, 0 <= i < REG_SIZEB ->
  aview SEGS (w_H W) mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
Boxreg.boxreg_inv bs ->
afobj SEGS B ly S W mem p 6 -> length M = 6%nat ->
(forall i, 0 <= i < 6 -> aview SEGS (w_H W) mem (p + i) = Some (bv_unsigned (nth (Z.to_nat i) M (Z_to_bv 8 0)))) ->
SRr SEGS W (cfg_at SEGS AB_reac_boxreg_addP regs mem md) (tbreac_boxreg_add_post regs ly S W mem md r k bs M).
(* ===== The walk (pg-prog engine, lib/B/Prog layer). =====
   The symbolic state at the entry slot: registers are their own atoms; atom 32 is the shadow base, 33 / 34 the
   unsigned words n / fabric of the registry, 35 + 6 i + j the MAC byte j of row i, 65 + i the unsigned nch word of
   row i, 70 the complement ~r (the UBSan pointer-overflow checks compare against it). The registry region (base r,
   288 bytes) carries a chunk for every byte or word the function reads; its shadow entry covers all 288 bytes. *)
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (pa_sigma BB___asan_memset).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (pa_sigma BB___asan_memcpy).
Hypothesis MZ : BoxBMacIsZero.tbmac_is_zero_spec B.
Hypothesis FIND : BoxBReacBoxregFind.tbreac_boxreg_find_spec B.
Hypothesis LFB : BoxBLowestFreeBase.tblowest_free_base_spec B.
Definition SBv : Z := 0x7fff8000.
Definition ABx : sv := SOff 32 0.
Definition ABspan : Z * Z := (SBv, SBv + 2 ^ 44 - 1).
Definition SH_add : list shent := [mkSHE 10 0 288].
Definition bxb (bs : list byte) (o : Z) : Z := bv_unsigned (nth (Z.to_nat o) bs (Z_to_bv 8 0)).
Definition bxu4 (bs : list byte) (o : Z) : Z :=
  bxb bs o + 256 * (bxb bs (o + 1) + 256 * (bxb bs (o + 2) + 256 * bxb bs (o + 3))).
Definition mac_offs : list Z :=
  Eval vm_compute in flat_map (fun i => map (fun j => 56 * Z.of_nat i + Z.of_nat j) (seq 0 6)) (seq 0 5).
Definition add_xs (r : Z) (bs : list byte) : list word :=
  map (Z_to_bv 64) ([SBv; bxu4 bs 280; bxu4 bs 284] ++ map (bxb bs) mac_offs ++
                    [bxu4 bs 12; bxu4 bs 68; bxu4 bs 124; bxu4 bs 180; bxu4 bs 236] ++ [2 ^ 64 - 1 - r]).
Definition mac_chunk (i j : nat) : YP09.chunk :=
  YP09.mkChunk (56 * Z.of_nat i + Z.of_nat j) (CVal 1 (SOff (35 + 6 * i + j) 0)).
Definition nch_chunk (i : nat) : YP09.chunk := YP09.mkChunk (56 * Z.of_nat i + 12) (CVal 4 (SOff (65 + i) 0)).
Definition reg_chunks : list YP09.chunk :=
  Eval vm_compute in
  flat_map (fun i => map (mac_chunk i) (seq 0 6) ++ [nch_chunk i]) (seq 0 5) ++
  [YP09.mkChunk 280 (CVal 4 (SOff 33 0)); YP09.mkChunk 284 (CVal 4 (SOff 34 0))].
Definition reg_region : YP09.region := YP09.mkRegion (Some 10%nat) 0 288 0 0 reg_chunks.
Definition add_regions : smem := [stack_region 80; got_regionP; bcell_regionP 32; reg_region].
Definition NOTR : Z := 2 ^ 64 - 1.
Definition add_atoms : list (nat * afact) :=
  Eval vm_compute in
  [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 140737479966720 4);
   (11%nat, mkAF 4096 140737479966720 3); (32%nat, mkAF SBv SBv 0); (33%nat, mkAF 0 5 0);
   (34%nat, mkAF 1 40 0)] ++
  map (fun n => (n, mkAF 0 255 0)) (seq 35 30) ++ map (fun n => (n, mkAF 0 4294967295 0)) (seq 65 5) ++
  [(70%nat, mkAF (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 4097) 0)].
Definition add_alias : list (sv * sv) :=
  Eval vm_compute in
  map (fun i => (SAlu ALU_XOR (SOff 10 (56 * Z.of_nat i)) (SLit (-1)), SOff 70 (- 56 * Z.of_nat i))) (seq 0 5).
Definition add_facts : facts := mkFacts add_atoms [] add_alias.
Definition ss_add : sstate := mkSS AF_reac_boxreg_add sr_atoms add_regions None add_facts.
(* The environment of the walk: the registers at entry and the values add_xs names. *)
Definition EOK (regs : bvmap 5 word) (r : Z) (bs : list byte) (E : env) : Prop :=
  img_env VAL A_LIM E /\ env_agree 71 (Ereg regs (add_xs r bs)) E.
Lemma bxb_range : forall bs o, 0 <= bxb bs o < 256.
Proof.
  intros bs o. unfold bxb. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat o) bs (Z_to_bv 8 0))) as R.
  change (bv_modulus 8) with 256 in R. exact R.
Qed.
Lemma bxu4_range : forall bs o, 0 <= bxu4 bs o < 2 ^ 32.
Proof.
  intros bs o. unfold bxu4. pose proof (bxb_range bs o). pose proof (bxb_range bs (o + 1)).
  pose proof (bxb_range bs (o + 2)). pose proof (bxb_range bs (o + 3)). lia.
Qed.
Lemma le_byte_u4 : forall b0 b1 b2 b3 k, 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  (k < 4)%nat -> YG0f.le_byte (b0 + 256 * (b1 + 256 * (b2 + 256 * b3))) 4 k = nth k [b0; b1; b2; b3] 0.
Proof.
  intros b0 b1 b2 b3 k H0 H1 H2 H3 Hk. unfold YG0f.le_byte.
  change (8 * Z.of_nat 4) with 32. rewrite (Z.mod_small _ (2 ^ 32)) by lia.
  set (z := b0 + 256 * (b1 + 256 * (b2 + 256 * b3))).
  assert (D1 : z / 256 = b1 + 256 * (b2 + 256 * b3)) by (symmetry; apply Z.div_unique with b0; unfold z; lia).
  assert (D2 : z / 65536 = b2 + 256 * b3) by (symmetry; apply Z.div_unique with (b0 + 256 * b1); unfold z; lia).
  assert (D3 : z / 16777216 = b3) by (symmetry; apply Z.div_unique with (b0 + 256 * (b1 + 256 * b2)); unfold z; lia).
  assert (S0 : Z.shiftr z (8 * Z.of_nat 0) = z) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_1_r).
  assert (S1 : Z.shiftr z (8 * Z.of_nat 1) = z / 256) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (S2 : Z.shiftr z (8 * Z.of_nat 2) = z / 65536) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (S3 : Z.shiftr z (8 * Z.of_nat 3) = z / 16777216) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  destruct k as [|[|[|[|k]]]]; [| | | | lia]; cbn [nth].
  - rewrite S0. symmetry. apply (Z.mod_unique _ _ (b1 + 256 * (b2 + 256 * b3))); unfold z; lia.
  - rewrite S1, D1. symmetry. apply (Z.mod_unique _ _ (b2 + 256 * b3)); lia.
  - rewrite S2, D2. symmetry. apply (Z.mod_unique _ _ b3); lia.
  - rewrite S3, D3. apply Z.mod_small; lia.
Qed.
Lemma le_byte1 : forall x, 0 <= x < 256 -> YG0f.le_byte x 1 0 = x /\ YO0f.le_byte x 1 0 = x.
Proof.
  intros x Hx. unfold YG0f.le_byte, YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small x 256) by lia.
  rewrite (Z.mod_small x 256) by lia. split; reflexivity.
Qed.
Lemma val1_of_aview : forall H mem a v, aview SEGS H mem a = Some v -> val_mem SEGS (mrestrict H mem) a 1 v.
Proof.
  intros H mem a v Hv k Hk. assert (k = 0%nat) as -> by lia.
  destruct (aview_byte SEGS H mem a v Hv) as (b & Hb & -> & Hr). cbn [Z.of_nat]. rewrite Z.add_0_r, Hb. f_equal.
  destruct (le_byte1 _ Hr) as [L1 L2]. first [rewrite L1 | rewrite L2]. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma val4_of_aview : forall H mem a bs o,
  (forall j, 0 <= j < 4 -> aview SEGS H mem (a + j) = Some (bxb bs (o + j))) ->
  val_mem SEGS (mrestrict H mem) a 4 (bxu4 bs o).
Proof.
  intros H mem a bs o Hv. apply val_mem_of_rd32. intros k Hk.
  rewrite (Hv (Z.of_nat k) ltac:(lia)). f_equal. unfold bxu4.
  rewrite le_byte_u4 by (first [apply bxb_range | lia]).
  destruct k as [|[|[|[|k]]]]; [| | | | lia]; cbn [nth Z.of_nat]; f_equal; lia.
Qed.
Lemma bsub4_eq : forall bs o, 0 <= o -> o + 4 <= Z.of_nat (length bs) ->
  Boxreg.bsub bs o 4 = [nth (Z.to_nat o) bs (Z_to_bv 8 0); nth (Z.to_nat (o + 1)) bs (Z_to_bv 8 0);
                        nth (Z.to_nat (o + 2)) bs (Z_to_bv 8 0); nth (Z.to_nat (o + 3)) bs (Z_to_bv 8 0)].
Proof.
  intros bs o Ho Hl. apply BoxregUpd.list_ext_nth. intros i. rewrite BoxregUpd.nth_bsub by lia.
  change (Z.to_nat 4) with 4%nat.
  destruct i as [|[|[|[|i]]]]; cbn [Nat.ltb Nat.leb nth_error]; [| | | | destruct i; reflexivity];
    rewrite (nth_error_nth' bs (Z_to_bv 8 0)) by lia; do 2 f_equal; lia.
Qed.
Lemma bxu4_bytes : forall bs o, 0 <= o -> o + 4 <= Z.of_nat (length bs) ->
  BvBase.bytes_le_to_Z (Boxreg.bsub bs o 4) = bxu4 bs o.
Proof.
  intros bs o Ho Hl. rewrite bsub4_eq by lia.
  rewrite OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Bytes.bytes_le_to_Z_le_val.
  cbn [map OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Bytes.le_val]. unfold bxu4, bxb. lia.
Qed.
Lemma bxu4_rd4 : forall bs o, 0 <= o -> o + 4 <= Z.of_nat (length bs) -> 0 <= Boxreg.rd4 bs o ->
  bxu4 bs o = Boxreg.rd4 bs o.
Proof.
  intros bs o Ho Hl Hr. unfold Boxreg.rd4 in *. rewrite bxu4_bytes in * by lia.
  pose proof (bxu4_range bs o) as R. set (z := bxu4 bs o) in *.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *. change (2 ^ Z.of_N 32) with 4294967296 in *.
  change (4294967296 / 2) with 2147483648 in *.
  destruct (Z_lt_le_dec z 2147483648) as [Hs|Hs].
  - rewrite (Z.mod_small (z + 2147483648)) in * by lia. lia.
  - rewrite <- (Z.mod_unique (z + 2147483648) 4294967296 1 (z - 2147483648)) in Hr by lia. lia.
Qed.
Lemma add_lxor_ones : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
Proof.
  intros x Hx. change 18446744073709551615 with (Z.ones 64).
  pose proof (Z.add_lnot_diag x).
  assert (E : Z.lxor x (Z.ones 64) = (Z.lnot x) mod 2 ^ 64).
  { rewrite <- Z.land_ones by lia. apply Z.bits_inj'. intros i Hi.
    rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
    destruct (Z.lt_ge_cases i 64).
    - rewrite Z.ones_spec_low by lia. rewrite xorb_true_r, andb_true_r. reflexivity.
    - rewrite Z.ones_spec_high by lia. rewrite xorb_false_r, andb_false_r.
      destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia|lia]. }
  rewrite E. unfold Z.ones. rewrite Z.shiftl_1_l. change (Z.pred (2 ^ 64)) with (2 ^ 64 - 1).
  replace (Z.lnot x) with (- x - 1) by lia.
  rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Ltac bvm := unfold bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); lia.
Lemma xor_alias : forall (v : word) r c, bv_unsigned v = r -> 0 <= r -> 0 <= c -> r + c < 2 ^ 64 ->
  alu64 ALU_XOR (Z_to_bv 64 (bv_unsigned v + c)) (Z_to_bv 64 (-1)) =
  Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (2 ^ 64 - 1 - r)) + - c).
Proof.
  intros v r c Hv Hr Hc Hrc. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite Hv.
  rewrite !Z_to_bv_unsigned.
  rewrite (bv_wrap_small 64 (r + c)) by bvm.
  change (bv_wrap 64 (-1)) with 18446744073709551615.
  rewrite add_lxor_ones by lia.
  rewrite (bv_wrap_small 64 (2 ^ 64 - 1 - r)) by bvm.
  rewrite !bv_wrap_small by bvm. lia.
Qed.
Lemma add_stk : REAC_BOXREG_ADD_STKB = 8352.
Proof. reflexivity. Qed.
Ltac xs_ew := cbn [ew Eimg Ereg nth map app add_xs mac_offs Nat.ltb Nat.leb andb Nat.sub A_TEXT A_LIM].
Lemma add_entry : forall ly S W (regs : bvmap 5 word) mem md ch (r p : Z) (bs : list byte),
  afn_pre SEGS B REAC_BOXREG_ADD_STKB ly S W regs mem md ch ->
  getr regs 10 = w64 r -> getr regs 11 = w64 p -> In (r, REG_SIZEB) (ablocks B ly S) ->
  (forall i, 0 <= i < REG_SIZEB -> aview SEGS (w_H W) mem (r + i) = Some (bxb bs i)) ->
  Boxreg.boxreg_inv bs -> afobj SEGS B ly S W mem p 6 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (add_xs r bs))) ss_add
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_boxreg_add)) mem (seg_rom SEGS))) /\
  sh_ok SEGS ABx SH_add (Eimg (Ereg regs (add_xs r bs))) (mrestrict (w_H W) mem).
Proof.
  intros ly S W regs mem md ch r p bs HPRE H10 H11 Hin HB HI HFO.
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). pose proof add_stk as WS.
  destruct (al_blocks _ _ LAWS ly S W mem md r REG_SIZEB HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
  change (req_size REG_SIZEB) with 288 in *.
  pose proof (blk_off_imgP B ly S W mem md r REG_SIZEB HAR Hin) as Hrimg. change (req_size REG_SIZEB) with 288 in Hrimg.
  destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
  rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
  pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
  pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
  pose proof HFO as ((cid & pos & Hfin & Hcid & Hfal & Hflo & Hfhi) & Hp8 & HRA).
  destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Happ).
  destruct HI as [[HL [H1 [H2 [H3 _]]]] _]. unfold Boxreg.boxreg_B1, Boxreg.boxreg_B2, Boxreg.bx_n, Boxreg.bx_fabric in *.
  assert (Hn : bxu4 bs 280 = Boxreg.rd4 bs 280) by (apply bxu4_rd4; lia).
  assert (Hf : bxu4 bs 284 = Boxreg.rd4 bs 284) by (apply bxu4_rd4; lia).
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (add_xs r bs))).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (add_xs r bs)) n)
    by (intros n Hn0; subst E; apply Eimg_low; exact Hn0).
  assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E10 : ew E 10 = Z_to_bv 64 r) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
  assert (E11 : ew E 11 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
  assert (E32 : ew E 32 = Z_to_bv 64 SBv) by (subst E; xs_ew; reflexivity).
  assert (Egot : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Ecell : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
  { intros n v Hn0 Hv. cbn [base_val]. rewrite Hn0. apply unsigned_lit_small. exact Hv. }
  split.
  - unfold ss_add. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold add_regions, stack_region, got_regionP, bcell_regionP, reg_region.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite WS. lia.
      * rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
        [cbn [sv_denot]; rewrite Ecell, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
      * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Ecell) by (pose proof (pa_val_range (A_OBJ 12)); lia).
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 ABx SBv);
        [cbn [sv_denot ABx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SBv; zside | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
      * rewrite (VB 10%nat r E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        unfold reg_chunks.
        repeat apply Forall_cons; try apply Forall_nil;
        lazymatch goal with
        | |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 1 (SOff ?a 0))) =>
          apply (chunk_ok_val SEGS E _ r o 1 (SOff a 0) (bxb bs o));
          [ cbn [sv_denot]; rewrite Z.add_0_r; subst E; xs_ew; rewrite Z_to_bv_bv_unsigned; reflexivity
          | pose proof (bxb_range bs o); zside | zside
          | apply val1_of_aview; apply HB; unfold REG_SIZEB; lia ]
        | |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 4 (SOff ?a 0))) =>
          apply (chunk_ok_val SEGS E _ r o 4 (SOff a 0) (bxu4 bs o));
          [ cbn [sv_denot]; rewrite Z.add_0_r; subst E; xs_ew; rewrite Z_to_bv_bv_unsigned; reflexivity
          | pose proof (bxu4_range bs o); zside | zside
          | apply val4_of_aview; intros j Hj; rewrite <- Z.add_assoc; apply HB; unfold REG_SIZEB; lia ]
        end.
    + apply pairwise_disjoint_of_extents.
      unfold add_regions, stack_region, got_regionP, bcell_regionP, reg_region, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
      rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Ecell) by (pose proof (pa_val_range (A_OBJ 12)); lia).
      rewrite (VB 10%nat r E10) by lia.
      cbn [base_val]. rewrite Usp.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR Hr4096 Hrceil Hrimg. clear.
      intros. repeat split; lia.
    + split; [|split; [exact I|]].
      * unfold add_facts, add_atoms. cbn [f_atoms atoms_ok].
        repeat match goal with
        | |- afact_ok _ ?n _ /\ _ => split
        | |- True => exact I
        | |- afact_ok _ ?n _ => unfold afact_ok; cbn [af_lo af_hi af_al2]
        end.
        all: try (rewrite Usp; change (2 ^ 4) with 16; revert Hslo Hshi H47 Hceil C1 WS Hstk0 Hal16; clear; intros; repeat split; lia).
        all: try (rewrite E10, unsigned_lit_small by lia; change (2 ^ 4) with 16;
                  revert Hr16 Hr4096 Hrceil C1; clear; intros; repeat split; lia).
        all: try (rewrite E11, unsigned_lit_small by lia; change (2 ^ 3) with 8;
                  revert Hf4096 Hfceil Hflo Hfhi Hp8 C1; clear; intros; repeat split; lia).
        all: subst E; xs_ew; rewrite ?unsigned_lit_small; rewrite ?Z.pow_0_r, ?Z.mod_1_r;
             try lazymatch goal with |- context [bxb ?b ?o] => pose proof (bxb_range b o) end;
             try lazymatch goal with |- context [bxu4 ?b ?o] => pose proof (bxu4_range b o) end;
             try (unfold SBv; lia); try (rewrite Hn; lia); try (rewrite Hf; lia); try lia.
      * unfold add_facts, add_alias. cbn [f_alias alias_ok].
        assert (H10' : getr regs (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 r) by exact H10.
        repeat match goal with |- _ /\ _ => split | |- True => exact I end;
        cbn [sv_denot]; subst E; xs_ew; rewrite H10';
        (apply xor_alias; [apply unsigned_lit_small; lia | lia | lia | lia]).
  - unfold sh_ok, SH_add. constructor; [|constructor].
    apply (shent_ok_of_range SEGS (w_H W) mem E ABx 10 r 288 r 0 288).
    + exact (range_addressable_of_block SEGS B LAWS ly S W mem md r REG_SIZEB r 288 HAR Hin ltac:(lia) ltac:(change (req_size REG_SIZEB) with 288; lia)).
    + unfold U, ABx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SBv; lia). reflexivity.
    + unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
    + lia.
    + lia.
    + intros x Hx. revert Hria Hx. clear. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg. intros. lia.
Qed.
(* The canonical symbolic states at the merge points of the walk (the loop head 0x8207c, the row end 0x820fc,
   the new-row entry 0x82124 and the bind 0x821ec). Dead registers hold the junk atom 700 + x of register x; the
   saved registers are in the frame chunks; t1, t2, ra and t3..t6 hold the junk atoms of the find call. *)
Definition JK (x : nat) : sv := SOff (700 + x) 0.
Definition frame_region : YP09.region :=
  YP09.mkRegion (Some 2%nat) (-80) 0 (-80) 0
    (map (fun ov => YP09.mkChunk (fst ov) (CVal 8 (SOff (snd ov) 0)))
       [(-80, 24%nat); (-72, 23%nat); (-64, 22%nat); (-56, 21%nat); (-48, 20%nat); (-40, 19%nat); (-32, 18%nat);
        (-24, 9%nat); (-16, 8%nat); (-8, 1%nat)]).
Definition cregions : smem := [frame_region; got_regionP; bcell_regionP 32; reg_region].
Definition S7X : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 280) (SLit 3)) (SOff 32 0).
Definition A2X : sv := SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLT (SLit 0) (SOff 33 0))) (SOff 33 0).
Definition cregs (t0 a0 a1 a2 a3 a4 a5 a6 a7 s4 : sv) : list sv :=
  [SLit 0; SOff 620 0; SOff 2 (-80); SOff 3 0; SOff 4 0; t0; SOff 622 0; SOff 623 0;
   SOff 12 0; SOff 10 280; a0; a1; a2; a3; a4; a5; a6; a7; SOff 11 0; SOff 10 0; s4; SOff 21 0; SOff 32 0; S7X;
   SOff 70 0; SOff 25 0; SOff 26 0; SOff 27 0; SOff 632 0; SOff 633 0; SOff 634 0; SOff 635 0].
Definition ss_row (i : Z) : sstate :=
  mkSS 8400 (cregs (JK 5) (JK 10) (JK 11) A2X (SLit 5) (SOff 10 (56 * i)) (SOff 10 (56 * i)) (JK 16) (JK 17) (SLit i))
    cregions None add_facts.
Definition ss_tail (i : Z) : sstate :=
  mkSS 8528 (cregs (JK 5) (SOff 10 (56 * i)) (JK 11) A2X (SLit 5) (SOff 10 (56 * i)) (SOff 10 (56 * i)) (JK 16) (JK 17)
    (SLit i)) cregions None add_facts.
Definition ss_new : sstate :=
  mkSS 8568 (cregs (JK 5) (JK 10) (JK 11) (JK 12) (JK 13) (JK 14) (JK 15) (JK 16) (JK 17) (JK 20)) cregions None add_facts.
Definition ss_bind (j : Z) : sstate :=
  mkSS 8768 (cregs (JK 5) (SOff 10 (56 * j)) (JK 11) (JK 12) (JK 13) (JK 14) (JK 15) (JK 16) (JK 17) (SLit j))
    cregions None add_facts.
(* The new-row state after `bltz a0` (slot 8604) is not taken: b = atom 644 (lowest_free_base's result) is >= 0 and
   the alias fixes 56 n = 56 c. *)
Definition ss_nr (c : Z) : sstate :=
  mkSS 8604
    [SLit 0; JK 1; SOff 2 (-80); SOff 3 0; SOff 4 0; JK 5; JK 6; JK 7; SOff 12 0; SOff 10 280; SOff 644 0; JK 11; JK 12;
     JK 13; JK 14; JK 15; JK 16; JK 17; SOff 11 0; SOff 10 0; SLit 18446744073709551615; SOff 21 0; SOff 32 0; S7X; SOff 70 0;
     SOff 25 0; SOff 26 0; SOff 27 0; JK 28; JK 29; JK 30; JK 31]
    cregions None
    (mkFacts add_atoms [mkAC BC_GE (SOff 644 0) (SLit 0)]
       ((SAlu ALU_SUB (SAlu ALU_SLL (SOff 33 0) (SLit 6)) (SAlu ALU_SLL (SOff 33 0) (SLit 3)), SLit (56 * c)) :: add_alias)).
(* The theorem's premises, and what holds at every merge point (env, shadow entries, journal from the entry, the
   288 registry bytes unchanged). *)
Definition add_pre ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch (r p k : Z) (bs M : list byte) : Prop :=
  afn_pre SEGS B REAC_BOXREG_ADD_STKB ly S W regs mem md ch /\
  getr regs 10 = w64 r /\ getr regs 11 = w64 p /\ getr regs 12 = w64 k /\ -2^31 <= k < 2^31 /\
  In (r, REG_SIZEB) (ablocks B ly S) /\
  (forall i, 0 <= i < REG_SIZEB -> aview SEGS (w_H W) mem (r + i) = Some (bxb bs i)) /\
  Boxreg.boxreg_inv bs /\ afobj SEGS B ly S W mem p 6 /\ length M = 6%nat /\
  (forall i, 0 <= i < 6 -> aview SEGS (w_H W) mem (p + i) = Some (bxb M i)).
Definition add_cur ly S (W : world SEGS) (regs : bvmap 5 word) mem md (r : Z) (bs : list byte)
    (E : env) (ms : machine_state) (mdc : Model) : Prop :=
  EOK regs r bs E /\ sh_ok SEGS ABx SH_add E (mrestrict (w_H W) (ms_mem ms)) /\
  ajournal SEGS B REAC_BOXREG_ADD_STKB (spZ regs) [(r, r + REG_SIZEB)] ly S W mem md [] ly S W (ms_mem ms) mdc 0 /\
  (forall i, 0 <= i < REG_SIZEB -> aview SEGS (w_H W) (ms_mem ms) (r + i) = Some (bxb bs i)).
(* Keeping the walk's invariants across engine runs, calls and re-abstraction. *)
Definition KEEPR (W : world SEGS) (m : word -> option byte) (r : Z) (bs : list byte) : Prop :=
  forall i, 0 <= i < REG_SIZEB -> aview SEGS (w_H W) m (r + i) = Some (bxb bs i).
Lemma EOK_extK : forall regs r bs E K ws,
  EOK regs r bs E -> img_env VAL A_LIM (extK E K ws) -> (71 <= K)%nat -> EOK regs r bs (extK E K ws).
Proof.
  intros regs r bs E K ws [HI HA] HI' HK. split; [exact HI'|].
  eapply env_agree_trans; [exact HA|]. eapply env_agree_le; [|apply env_agree_extK]. exact HK.
Qed.
Lemma EOK_mono : forall regs r bs E0 E1, EOK regs r bs E0 -> img_env VAL A_LIM E1 ->
  (forall n, (n < 71)%nat -> ew E1 n = ew E0 n) -> ed E1 = ed E0 -> EOK regs r bs E1.
Proof.
  intros regs r bs E0 E1 [HI [HA HD]] HI1 Hn Hd. split; [exact HI1|]. split.
  - intros n Hn0. rewrite Hn by exact Hn0. apply HA. exact Hn0.
  - rewrite Hd. exact HD.
Qed.
Lemma EOK_havoc : forall regs r bs E k ws, EOK regs r bs E -> (A_LIM <= k)%nat -> EOK regs r bs (havoc E k ws).
Proof.
  intros regs r bs E k ws [HI HA] Hk. split; [apply img_env_havoc_hi; assumption|].
  apply env_agree_havoc_ge; [unfold A_LIM in Hk; lia | exact HA].
Qed.
Lemma EOK_reg : forall regs r bs E n, EOK regs r bs E -> (n < 32)%nat -> ew E n = getr regs (Z_to_bv 5 (Z.of_nat n)).
Proof.
  intros regs r bs E n [_ [HA _]] Hn. rewrite (HA n ltac:(lia)). unfold Ereg. cbn [ew].
  replace (n <? 32)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hn). reflexivity.
Qed.
Lemma EOK_xs : forall regs r bs E n, EOK regs r bs E -> (32 <= n < 71)%nat ->
  ew E n = nth (n - 32) (add_xs r bs) (Z_to_bv 64 0).
Proof.
  intros regs r bs E n [_ [HA _]] Hn. rewrite (HA n ltac:(lia)). unfold Ereg. cbn [ew].
  replace (n <? 32)%nat with false by (symmetry; apply Nat.ltb_ge; lia). reflexivity.
Qed.
Ltac eok_ew HE n :=
  first [ rewrite (EOK_xs _ _ _ _ n HE ltac:(lia)); cbn [nth map app add_xs mac_offs Nat.sub]
        | rewrite (EOK_reg _ _ _ _ n HE ltac:(lia)) ].
Lemma sh_ok_of_block : forall ly S (W : world SEGS) mem md regs r bs E,
  AR SEGS B ly S W mem md -> In (r, REG_SIZEB) (ablocks B ly S) -> EOK regs r bs E -> getr regs 10 = w64 r ->
  sh_ok SEGS ABx SH_add E (mrestrict (w_H W) mem).
Proof.
  intros ly S W mem md regs r bs E HAR Hin HE H10.
  destruct (al_blocks _ _ LAWS ly S W mem md r REG_SIZEB HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
  change (req_size REG_SIZEB) with 288 in *.
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  assert (E10 : ew E 10 = Z_to_bv 64 r) by (rewrite (EOK_reg _ _ _ _ 10 HE ltac:(lia)); exact H10).
  assert (E32 : ew E 32 = Z_to_bv 64 SBv) by (rewrite (EOK_xs _ _ _ _ 32 HE ltac:(lia)); reflexivity).
  unfold sh_ok, SH_add. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E ABx 10 r 288 r 0 288).
  - exact (range_addressable_of_block SEGS B LAWS ly S W mem md r REG_SIZEB r 288 HAR Hin ltac:(lia) ltac:(change (req_size REG_SIZEB) with 288; lia)).
  - unfold U, ABx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SBv; lia). reflexivity.
  - unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
  - lia.
  - lia.
  - intros x Hx. revert Hria Hx. clear. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg. intros. lia.
Qed.
Definition add_windows : list (option nat * Z * Z) :=
  [(Some 2%nat, -80, 0); (Some (A_OBJ 1), 0, 0); (Some (A_OBJ 12), 0, 0); (Some 10%nat, 0, 0)].
Lemma keep_run : forall E rs (W : world SEGS) m m' (sp r : Z) bs,
  windows rs = add_windows -> bv_unsigned (ew E 2) = sp -> 0 <= r -> r + REG_SIZEB <= sp - 80 ->
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> KEEPR W m r bs -> KEEPR W m' r bs.
Proof.
  intros E rs W m m' sp r bs Hw Hsp Hr0 Hr HF HK i Hi. rewrite <- (HK i Hi).
  apply (kept_of_frame E rs (w_H W) m m' (fun a => sp - 80 <= a < sp) HF).
  - intros b wlo whi a Hin Ha. rewrite Hw in Hin. unfold add_windows in Hin.
    destruct Hin as [Eq | [Eq | [Eq | [Eq | []]]]]; injection Eq as <- <- <-; [|lia | lia | lia].
    cbn [base_val] in Ha. rewrite Hsp in Ha. lia.
  - unfold REG_SIZEB in *. pose proof (bv_unsigned_in_range 64 (ew E 2)) as Hb. rewrite Hsp in Hb.
    unfold bv_modulus in Hb. change (2 ^ Z.of_N 64) with (2 ^ 64) in Hb. lia.
  - unfold REG_SIZEB in *. lia.
Qed.
(* Re-abstraction to a canonical state: dead registers get the junk atoms 700 + x. *)
Definition PJ (n : nat) : bool := negb ((700 <=? n)%nat && (n <? 732)%nat).
Definition JE (E : env) (rg : bvmap 5 word) : env :=
  mkEnv (fun n => if ((700 <=? n)%nat && (n <? 732)%nat) then getr rg (Z_to_bv 5 (Z.of_nat (n - 700))) else ew E n)
        (ed E).
Lemma JE_agree : forall E rg, env_agree_pd PJ PT E (JE E rg).
Proof.
  intros E rg. split; [|reflexivity]. intros n Hn. unfold PJ in Hn. unfold JE. cbn [ew].
  destruct ((700 <=? n)%nat && (n <? 732)%nat); [discriminate | reflexivity].
Qed.
Lemma JE_low : forall E rg n, (n < 700)%nat -> ew (JE E rg) n = ew E n.
Proof.
  intros E rg n Hn. unfold JE. cbn [ew]. replace (700 <=? n)%nat with false by (symmetry; apply Nat.leb_gt; lia).
  reflexivity.
Qed.
Lemma JE_EOK : forall regs r bs E rg, EOK regs r bs E -> EOK regs r bs (JE E rg).
Proof.
  intros regs r bs E rg [HI [HA HD]]. split; [|split].
  - intros a Ha. rewrite JE_low by (unfold A_LIM in Ha; lia). apply HI. exact Ha.
  - intros n Hn. rewrite JE_low by lia. apply HA. exact Hn.
  - cbn [JE ed]. exact HD.
Qed.
Lemma JE_sh : forall E rg m, sh_ok SEGS ABx SH_add E m -> sh_ok SEGS ABx SH_add (JE E rg) m.
Proof.
  intros E rg m H. unfold sh_ok, SH_add in *. inversion H as [|x l Hx _]; subst. constructor; [|constructor].
  unfold shent_ok, app_apart, U, ABx in *. cbn [she_m she_lo she_hi sv_denot] in *.
  rewrite !JE_low by lia. exact Hx.
Qed.
Lemma add_reabs : forall E ss ms regs',
  st_ok_pi SEGS VAL E ss ms ->
  reabs_check PJ (abs_ss VAL ss) regs' add_facts = true ->
  mem_atoms_pd PJ PT (ss_mem ss) = true ->
  Forall (fun rj : bv 5 * nat => ew (JE E (ms_regs ms)) (snd rj) = getr (ms_regs ms) (fst rj)) (reabs_obl PJ regs') ->
  st_ok_pi SEGS VAL (JE E (ms_regs ms)) (mkSS (ss_pc ss) regs' (ss_mem ss) None add_facts) ms.
Proof.
  intros E ss ms regs' HS Hck Hm Hobl. unfold st_ok_pi in *.
  exact (st_ok_reabs SEGS PJ E (JE E (ms_regs ms)) (abs_ss VAL ss) ms regs' (ss_mem ss) add_facts HS (JE_agree E _) Hck Hobl
           ltac:(vm_compute; constructor)
           (mem_ok_agree_pd SEGS PJ PT E _ (ms_mem ms) (ss_mem ss) (JE_agree E _) Hm (st_ok_mem_ok SEGS E _ ms HS))).
Qed.
Lemma sext_atom : forall E n z, ew E n = Z_to_bv 64 z -> -2^31 <= z < 2^31 ->
  sv_denot E (SAluw ALU_ADD (SOff n 0) (SLit 0)) = w64 z.
Proof.
  intros E n z H Hz. cbn [sv_denot]. rewrite H, Z.add_0_r. rewrite zalu32_sound. unfold zalu32, w64. rewrite lit_canon.
  f_equal. cbn [zalu_raw]. rewrite (swrap32_congr _ z).
  - apply bv_swrap_small. unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32).
    change (2 ^ 32 / 2) with (2 ^ 31). lia.
  - unfold zu32, M32, two32. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    rewrite (Z.mod_eq z (2 ^ 64)) by lia.
    replace (z - 2 ^ 64 * (z / 2 ^ 64)) with (z + (- (z / 2 ^ 64 * 2 ^ 32)) * 2 ^ 32) by ring.
    rewrite Z_mod_plus_full. rewrite Zmod_0_l. rewrite (Z.mod_eq z (2 ^ 32)) by lia.
    replace (z - 2 ^ 32 * (z / 2 ^ 32) + 0 - z) with ((- (z / 2 ^ 32)) * 2 ^ 32) by ring. apply Z_mod_mult.
Qed.
(* The regions a program call keeps: the frame above the callee's stack, the GOT word and the shadow cell (fixed by
   AR), and the registry (the callee's footprint is empty). *)
Lemma kept_call4 : forall ly S (W : world SEGS) (regs : bvmap 5 word) r bs E m md m2 md2 cs STK1 EV1,
  EOK regs r bs E -> getr regs 10 = w64 r -> 0 <= STK1 ->
  AR SEGS B ly S W m md -> AR SEGS B ly S W m2 md2 -> In (r, REG_SIZEB) (ablocks B ly S) ->
  ajournal SEGS B STK1 (spZ regs - 80) [] ly S W m md [] ly S W m2 md2 EV1 ->
  (forall a, spZ regs - 80 <= a < spZ regs -> apresent (w_H W) m2 a) ->
  alloc_ceiling <= spZ regs - 80 ->
  Forall (region_kept SEGS E (mrestrict (w_H W) m) (mrestrict (w_H W) m2))
    [YP09.mkRegion (Some 2%nat) (-80) 0 (-80) 0 cs; got_regionP; bcell_regionP 32; reg_region].
Proof.
  intros ly S W regs r bs E m md m2 md2 cs STK1 EV1 HE H10 HSTK HAR HAR2 Hin HJc Hpres2 Hsp.
  pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & _).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EOK_reg _ _ _ _ 2 HE) by lia; reflexivity).
  assert (E10 : bv_unsigned (ew E 10) = r).
  { rewrite (EOK_reg _ _ _ _ 10 HE) by lia. change (getr regs (Z_to_bv 5 (Z.of_nat 10))) with (getr regs 10).
    rewrite H10. apply unsigned_lit_small.
    destruct (al_blocks _ _ LAWS ly S W m md r REG_SIZEB HAR Hin) as (_ & H4096 & Hce & _).
    pose proof (asan_consts) as (C1 & _). change (req_size REG_SIZEB) with 288 in *. lia. }
  destruct (al_const _ _ LAWS ly S W m md HAR) as (Kcell & _ & Kgot & _).
  destruct (al_const _ _ LAWS ly S W m2 md2 HAR2) as (Kcell2 & _ & Kgot2 & _).
  rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot, Kgot2. rewrite (pal_cell B TL) in Kcell, Kcell2.
  assert (Eo1 : bv_unsigned (ew E (A_OBJ 1)) = VAL (A_OBJ 1)) by (apply (proj1 HE); unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Eo12 : bv_unsigned (ew E (A_OBJ 12)) = VAL (A_OBJ 12)) by (apply (proj1 HE); unfold A_OBJ, A_TEXT, A_LIM; lia).
  pose proof (bv_unsigned_in_range 64 (ew E 2)) as Hsr. rewrite Usp in Hsr. unfold bv_modulus in Hsr.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Hsr.
  repeat apply Forall_cons; try apply Forall_nil.
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha.
    + apply (mbyte_of_aview SEGS). apply F1; lia.
    + intros _. apply (apresent_writable SEGS). apply Hpres2. lia.
  - unfold got_regionP.
    apply (region_kept_val_at E _ _ (A_OBJ 1) (VAL (A_OBJ 1)) 8 (VAL (A_OBJ 12)) 0 0); [exact Eo1 | | | lia].
    + exact (val_mem_of_rdword SEGS (w_H W) m _ _ Kgot).
    + exact (val_mem_of_rdword SEGS (w_H W) m2 _ _ Kgot2).
  - unfold bcell_regionP.
    apply (region_kept_val_at E _ _ (A_OBJ 12) (VAL (A_OBJ 12)) 8 SHADOW_OFF 0 0); [exact Eo12 | | | lia].
    + exact (val_mem_of_rdword SEGS (w_H W) m _ _ Kcell).
    + exact (val_mem_of_rdword SEGS (w_H W) m2 _ _ Kcell2).
  - split; cbn [reg_region YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite E10; intros a Ha; [|lia].
    apply (mbyte_of_aview SEGS). replace a with (r + (a - r)) by lia.
    apply (F2 r REG_SIZEB (a - r) Hin Hin); [change (req_size REG_SIZEB) with 288; lia | intros X; exact (inFP_nil _ X)].
Qed.
(* KEEPR across a program call (the callee's footprint is empty). *)
Lemma keep_call : forall ly S (W : world SEGS) r bs m md m2 md2 STK1 sp1 EV1,
  In (r, REG_SIZEB) (ablocks B ly S) ->
  ajournal SEGS B STK1 sp1 [] ly S W m md [] ly S W m2 md2 EV1 -> KEEPR W m r bs -> KEEPR W m2 r bs.
Proof.
  intros ly S W r bs m md m2 md2 STK1 sp1 EV1 Hin HJc HK i Hi. pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  rewrite (F2 r REG_SIZEB i Hin Hin); [exact (HK i Hi) | change (req_size REG_SIZEB) with 288; unfold REG_SIZEB in Hi; lia
  | intros X; exact (inFP_nil _ X)].
Qed.
(* The branch conditions of the walk, as Z tests. *)
Lemma dec_kw : forall E k, ew E 12 = Z_to_bv 64 k -> -2^31 <= k < 2^31 ->
  branch_taken BC_LTU (sv_denot E (SAluw ALU_ADD (SOff 12 0) (SLit (-41)))) (sv_denot E (SLit 18446744073709551577))
  = negb ((2 <=? k) && (k <=? 40)).
Proof.
  intros E k H Hk. rewrite <- (BoxregStep.bx_wtest k Hk). cbn [branch_taken sv_denot]. rewrite H, Z.add_0_r.
  rewrite zalu32_sound. unfold zalu32. rewrite lit_canon. cbn [zalu_raw]. f_equal.
  - f_equal. apply swrap32_congr. unfold zu32, M32, two32.
    set (x := bv_unsigned (Z_to_bv 64 k)).
    rewrite (Z.mod_eq x (2 ^ 32)) by lia. rewrite (Z.mod_eq (-41) (2 ^ 32)) by lia.
    replace (x - 2 ^ 32 * (x / 2 ^ 32) + (-41 - 2 ^ 32 * (-41 / 2 ^ 32)) - (x + -41))
      with ((- (x / 2 ^ 32) - (-41 / 2 ^ 32)) * 2 ^ 32) by ring.
    apply Z_mod_mult.
  - apply bv_eq. rewrite !Z_to_bv_unsigned. vm_compute. reflexivity.
Qed.
Lemma U_off12 : forall E k, ew E 12 = Z_to_bv 64 k -> U E (SOff 12 0) = k mod 2 ^ 64.
Proof.
  intros E k H. rewrite U_SOff, H, Z.add_0_r, Z_to_bv_unsigned. unfold zcanon, bv_wrap, M64, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.
Lemma dec_odd : forall E k, ew E 12 = Z_to_bv 64 k ->
  branch_taken BC_NE (sv_denot E (SAlu ALU_AND (SOff 12 0) (SLit 1))) (sv_denot E (SLit 0)) = negb (k mod 2 =? 0).
Proof.
  intros E k H. rewrite branch_ne_U, U_and_lit by lia. rewrite (U_off12 E k H), U_lit by lia.
  change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. change (2 ^ 1) with 2.
  rewrite (Z.mod_eq k (2 ^ 64)) by lia.
  replace (k - 2 ^ 64 * (k / 2 ^ 64)) with (k + (- (k / 2 ^ 64 * 2 ^ 63)) * 2) by ring.
  rewrite Z_mod_plus_full. reflexivity.
Qed.
Lemma dec_lts_atoms : forall E n m a b, ew E n = Z_to_bv 64 a -> ew E m = Z_to_bv 64 b ->
  -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 ->
  branch_taken BC_LT (sv_denot E (SOff n 0)) (sv_denot E (SOff m 0)) = (a <? b).
Proof.
  intros E n m a b Ha Hb Ra Rb. cbn [branch_taken sv_denot]. rewrite Ha, Hb, !Z.add_0_r, !Z_to_bv_bv_unsigned.
  apply Boxreg.lts_lit; lia.
Qed.
Lemma dec_lts_lit_atom : forall E m c b, ew E m = Z_to_bv 64 b -> -2^63 <= c < 2^63 -> -2^63 <= b < 2^63 ->
  branch_taken BC_LT (sv_denot E (SLit c)) (sv_denot E (SOff m 0)) = (c <? b).
Proof.
  intros E m c b Hb Rc Rb. cbn [branch_taken sv_denot]. rewrite Hb, !Z.add_0_r, !Z_to_bv_bv_unsigned.
  apply Boxreg.lts_lit; lia.
Qed.
Lemma dec_lts_atom_lit : forall E n a c, ew E n = Z_to_bv 64 a -> -2^63 <= a < 2^63 -> -2^63 <= c < 2^63 ->
  branch_taken BC_LT (sv_denot E (SOff n 0)) (sv_denot E (SLit c)) = (a <? c).
Proof.
  intros E n a c Ha Ra Rc. cbn [branch_taken sv_denot]. rewrite Ha, !Z.add_0_r, !Z_to_bv_bv_unsigned.
  apply Boxreg.lts_lit; lia.
Qed.
Lemma dec_ge_lit_atom : forall E m c b, ew E m = Z_to_bv 64 b -> -2^63 <= c < 2^63 -> -2^63 <= b < 2^63 ->
  branch_taken BC_GE (sv_denot E (SLit c)) (sv_denot E (SOff m 0)) = negb (c <? b).
Proof.
  intros E m c b Hb Rc Rb. cbn [branch_taken sv_denot]. rewrite Hb, !Z.add_0_r, !Z_to_bv_bv_unsigned.
  rewrite Boxreg.lts_lit by lia. reflexivity.
Qed.
Lemma dec_ge_atom_lit : forall E n a c, ew E n = Z_to_bv 64 a -> -2^63 <= a < 2^63 -> -2^63 <= c < 2^63 ->
  branch_taken BC_GE (sv_denot E (SOff n 0)) (sv_denot E (SLit c)) = negb (a <? c).
Proof.
  intros E n a c Ha Ra Rc. cbn [branch_taken sv_denot]. rewrite Ha, !Z.add_0_r, !Z_to_bv_bv_unsigned.
  rewrite Boxreg.lts_lit by lia. reflexivity.
Qed.
Lemma dec_eq_atom_lit : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2^64 -> 0 <= c < 2^64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit c)) = (v =? c).
Proof. intros E n v c H Hv Hc. rewrite branch_eq_U, (U_atom E n v H Hv), U_lit by lia. reflexivity. Qed.
Lemma dec_ne_atom_lit : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2^64 -> 0 <= c < 2^64 ->
  branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit c)) = negb (v =? c).
Proof. intros E n v c H Hv Hc. rewrite branch_ne_U, (U_atom E n v H Hv), U_lit by lia. reflexivity. Qed.
Lemma dec_nch : forall E a u k, ew E a = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 -> ew E 12 = Z_to_bv 64 k ->
  -2^31 <= k < 2^31 ->
  branch_taken BC_EQ (sv_denot E (SExt true 32 (SOff a 0))) (sv_denot E (SOff 12 0)) = (bv_swrap 32 u =? k).
Proof.
  intros E a u k Hu Ru Hk Rk. cbn [branch_taken].
  rewrite (denot_lit_U E (SExt true 32 (SOff a 0))), U_SExt, (U_atom E a u Hu) by lia. rewrite lit_canon.
  change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small u) by lia.
  cbn [sv_denot]. rewrite Hk, Z.add_0_r, Z_to_bv_bv_unsigned.
  apply BoxregStep.bx_eqb.
  - unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32).
    pose proof (Z.mod_pos_bound (u + 2 ^ 32 / 2) (2 ^ 32) ltac:(lia)). change (2 ^ 32 / 2) with (2 ^ 31) in *. lia.
  - lia.
Qed.
Lemma U_A2X : forall E n, ew E 33 = Z_to_bv 64 n -> 1 <= n <= 5 -> U E A2X = n.
Proof.
  intros E n H Hn. unfold A2X. rewrite !U_SAlu, (U_atom E 33 n H), !U_lit by lia. cbn [zalu_raw].
  replace (bv_swrap 64 0 <? bv_swrap 64 n) with true.
  2: { symmetry. apply Z.ltb_lt. rewrite !bv_swrap_small; try lia; unfold bv_half_modulus, bv_modulus;
       change (2 ^ Z.of_N 64) with (2 ^ 64); change (2 ^ 64 / 2) with (2 ^ 63); lia. }
  change (zcanon (0 - 1)) with 18446744073709551615.
  rewrite (Z.land_comm 18446744073709551615). change 18446744073709551615 with (Z.ones 64).
  rewrite Z.land_ones by lia. unfold zcanon, M64. rewrite (Z.mod_small n (2 ^ 64)) by lia.
  rewrite (Z.mod_small n (2 ^ 64)) by lia. reflexivity.
Qed.
Lemma dec_loop : forall E n c, ew E 33 = Z_to_bv 64 n -> 1 <= n <= 5 -> 0 <= c < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SLit c)) (sv_denot E A2X) = negb (c =? n).
Proof. intros E n c H Hn Hc. rewrite branch_ne_U, (U_A2X E n H Hn), U_lit by lia. reflexivity. Qed.
(* Helpers of the six lemmas below (prefix lb_): byte lists read through bxb, and where a frame's shadow lies. *)
Lemma lb_bxb_eq : forall l l' o o', nth_error l (Z.to_nat o) = nth_error l' (Z.to_nat o') -> bxb l o = bxb l' o'.
Proof. intros l l' o o' H. unfold bxb. rewrite <- !nth_default_eq. unfold nth_default. rewrite H. reflexivity. Qed.
Lemma lb_upd_in : forall cs (k : Z) bs i, 0 <= k -> (Z.to_nat k + length bs <= length cs)%nat ->
  k <= i < k + Z.of_nat (length bs) ->
  bxb (OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Mem.upd_bytes cs (Z.to_nat k) bs) i = bxb bs (i - k).
Proof.
  intros cs k bs i Hk Hl Hi. apply lb_bxb_eq.
  rewrite OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Mem.upd_bytes_nth by lia.
  destruct (Nat.leb_spec0 (Z.to_nat k) (Z.to_nat i)); destruct (Nat.ltb_spec0 (Z.to_nat i) (Z.to_nat k + length bs));
    cbn [andb]; try (exfalso; lia).
  f_equal. lia.
Qed.
Lemma lb_upd_out : forall cs (k : Z) bs i, 0 <= k -> (Z.to_nat k + length bs <= length cs)%nat ->
  0 <= i < Z.of_nat (length cs) -> (i < k \/ k + Z.of_nat (length bs) <= i) ->
  bxb (OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Mem.upd_bytes cs (Z.to_nat k) bs) i = bxb cs i.
Proof.
  intros cs k bs i Hk Hl Hi Ho. apply lb_bxb_eq.
  rewrite OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Mem.upd_bytes_nth by lia.
  destruct (Nat.leb_spec0 (Z.to_nat k) (Z.to_nat i)); destruct (Nat.ltb_spec0 (Z.to_nat i) (Z.to_nat k + length bs));
    cbn [andb]; try (exfalso; lia); reflexivity.
Qed.
Lemma lb_bxb_sub : forall (l s : list byte) k n o, 0 <= k -> 0 <= n -> Boxreg.bsub l k n = s -> k <= o < k + n ->
  bxb l o = bxb s (o - k).
Proof.
  intros l s k n o Hk Hn Hs Ho. subst s. apply lb_bxb_eq. rewrite BoxregUpd.nth_bsub by lia.
  destruct (Nat.ltb_spec0 (Z.to_nat (o - k)) (Z.to_nat n)); [|exfalso; lia]. f_equal. lia.
Qed.
Lemma lb_nth_le_bytes : forall n z k, (k < n)%nat ->
  nth k (Z_to_le_bytes n z) (Z_to_bv 8 0) = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|].
  destruct k as [|k]; cbn [Z_to_le_bytes nth].
  - change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
  - rewrite IH by lia. rewrite Z.shiftr_shiftr by lia.
    replace (8 + 8 * Z.of_nat k) with (8 * Z.of_nat (S k)) by lia. reflexivity.
Qed.
Lemma lb_le4_0 : OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Mem.le4 (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) 4.
Proof. reflexivity. Qed.
Lemma lb_frame_shadow : forall F fs p x, F mod 8 = 0 -> p mod 8 = 0 -> fs mod 8 = 0 -> F <= p -> p + 6 <= F + fs ->
  p <= x < p + 6 -> shadow_addr F <= shadow_of_addr SHADOW_OFF x < shadow_addr F + fs / 8.
Proof.
  intros F fs p x HF Hp Hfs H1 H2 Hx. unfold shadow_addr, shadow_of_addr.
  pose proof (Z.div_mod F 8 ltac:(lia)) as DF. pose proof (Z.div_mod p 8 ltac:(lia)) as Dp.
  pose proof (Z.div_mod fs 8 ltac:(lia)) as Dfs. rewrite HF in DF. rewrite Hp in Dp. rewrite Hfs in Dfs.
  assert (Ex : x / 8 = p / 8) by (symmetry; apply Z.div_unique with (x - p); lia).
  rewrite Ex. lia.
Qed.
Lemma lb_shadow_not_block : forall r x, in_app r 288 -> 0 <= x < 2 ^ 47 -> ~ (r <= shadow_of_addr SHADOW_OFF x < r + 288).
Proof.
  intros r x Hr Hx. unfold shadow_of_addr. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)) as D0.
  assert (D1 : x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
  unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.
Lemma lb_fs8 : forall cid, 0 <= cid -> fs_frame_bytes cid mod 8 = 0.
Proof.
  intros cid Hc. unfold fs_frame_bytes. rewrite Z.shiftl_mul_pow2 by lia.
  replace (64 * 2 ^ cid) with ((8 * 2 ^ cid) * 8) by lia. apply Z.mod_mul. lia.
Qed.
(* The MAC object and its bytes at any point the journal reaches. *)
Lemma add_afobj_now : forall ly S W regs mem md ch r p k bs M memc mdc,
  add_pre ly S W regs mem md ch r p k bs M ->
  ajournal SEGS B REAC_BOXREG_ADD_STKB (spZ regs) [(r, r + REG_SIZEB)] ly S W mem md [] ly S W memc mdc 0 ->
  afobj SEGS B ly S W memc p 6.
Proof.
  intros ly S W regs mem md ch r p k bs M memc mdc HPRE HJ.
  pose proof HPRE as (HFN & _ & _ & _ & _ & Hin & _ & _ & HFO & _).
  pose proof HFN as (HAR & _).
  pose proof HFO as ((cid & pos & Hfin & Hcid & Hfal & Hflo & Hfhi) & Hp8 & HRA).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
  destruct (al_blocks _ _ LAWS ly S W mem md r REG_SIZEB HAR Hin) as (_ & _ & _ & Hria & _).
  change (req_size REG_SIZEB) with 288 in Hria.
  destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & _).
  pose proof asan_consts as (C1 & _).
  split; [exact (proj1 HFO)|]. split; [exact Hp8|].
  unfold range_addressable in *. intros x Hx. destruct (HRA x Hx) as (s & Hs & Hok).
  exists s. split; [|exact Hok]. rewrite <- Hs.
  pose proof (lb_frame_shadow (frame_addr ly cid pos) (fs_frame_bytes cid) p x Hfal Hp8 (lb_fs8 cid Hcid) Hflo Hfhi Hx)
    as Hsh.
  apply (F4 cid pos); [exact Hfin | right; unfold in_zr; cbn [fst snd]; exact Hsh |].
  intros (rr & [<- | []] & Hrr). cbn [fst snd] in Hrr. unfold REG_SIZEB in Hrr.
  exact (lb_shadow_not_block r x Hria ltac:(lia) Hrr).
Qed.
Lemma add_mac_now : forall ly S W regs mem md ch r p k bs M memc mdc,
  add_pre ly S W regs mem md ch r p k bs M ->
  ajournal SEGS B REAC_BOXREG_ADD_STKB (spZ regs) [(r, r + REG_SIZEB)] ly S W mem md [] ly S W memc mdc 0 ->
  forall i, 0 <= i < 6 -> aview SEGS (w_H W) memc (p + i) = Some (bxb M i).
Proof.
  intros ly S W regs mem md ch r p k bs M memc mdc HPRE HJ i Hi.
  pose proof HPRE as (HFN & _ & _ & _ & _ & Hin & _ & _ & HFO & _ & HMB).
  pose proof HFN as (HAR & _).
  pose proof HFO as ((cid & pos & Hfin & Hcid & Hfal & Hflo & Hfhi) & Hp8 & HRA).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
  pose proof (sep_block_frame SEGS B LAWS ly S W mem md r REG_SIZEB cid pos HAR Hin Hfin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size REG_SIZEB) with 288 in Hd.
  rewrite <- (HMB i Hi).
  apply (F4 cid pos); [exact Hfin | left; unfold frame_rng, in_zr; cbn [fst snd]; lia |].
  intros (rr & [<- | []] & Hrr). cbn [fst snd] in Hrr. unfold REG_SIZEB in Hrr. lia.
Qed.
(* The registry bytes the two writing exits leave (lib.Lib's upd_bytes / le4, named in full: no lib.Lib import). *)
#[local] Notation UPD := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Mem.upd_bytes.
#[local] Notation LE4 := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Mem.le4.
Lemma bxb_le4 : forall v i, 0 <= v < 2 ^ 32 -> 0 <= i < 4 -> bxb (LE4 (Z_to_bv 64 v)) i = YG0f.le_byte v 4 (Z.to_nat i).
Proof.
  intros v i Hv Hi. unfold bxb, OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Mem.le4.
  rewrite unsigned_lit_small by lia. rewrite lb_nth_le_bytes by lia. rewrite Z_to_bv_unsigned.
  unfold YG0f.le_byte. change (8 * Z.of_nat 4) with 32. rewrite (Z.mod_small v (2 ^ 32)) by lia.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. reflexivity.
Qed.
Lemma bxb_upd_bind : forall bs M j i, length bs = 288%nat -> length M = 6%nat -> 0 <= j < 5 -> 0 <= i < 288 ->
  bxb (UPD bs (Z.to_nat (56 * j)) M) i = if (56 * j <=? i) && (i <? 56 * j + 6) then bxb M (i - 56 * j) else bxb bs i.
Proof.
  intros bs M j i HL HM Hj Hi.
  destruct (Z.leb_spec0 (56 * j) i); destruct (Z.ltb_spec0 i (56 * j + 6)); cbn [andb].
  - apply lb_upd_in; rewrite ?HL, ?HM; lia.
  - apply lb_upd_out; rewrite ?HL, ?HM; lia.
  - apply lb_upd_out; rewrite ?HL, ?HM; lia.
  - apply lb_upd_out; rewrite ?HL, ?HM; lia.
Qed.
Lemma bxb_add_bytes : forall bs M b k i,
  length bs = 288%nat -> length M = 6%nat -> 0 <= Boxreg.bx_n bs < 5 -> 0 <= i < 288 ->
  bxb (reac_boxreg_add_c.add_bytes bs M b k) i =
  (if (56 * Boxreg.bx_n bs <=? i) && (i <? 56 * Boxreg.bx_n bs + 56) then
     (if i - 56 * Boxreg.bx_n bs <? 6 then bxb M (i - 56 * Boxreg.bx_n bs)
      else if i - 56 * Boxreg.bx_n bs <? 8 then 0
      else if i - 56 * Boxreg.bx_n bs <? 12 then bxb (LE4 (Z_to_bv 64 b)) (i - 56 * Boxreg.bx_n bs - 8)
      else if i - 56 * Boxreg.bx_n bs <? 16 then bxb (LE4 (Z_to_bv 64 k)) (i - 56 * Boxreg.bx_n bs - 12)
      else 0)
   else if (280 <=? i) && (i <? 284) then bxb (LE4 (Z_to_bv 64 (Boxreg.bx_n bs + 1))) (i - 280)
   else bxb bs i).
Proof.
  intros bs M b k i HL HM Hn Hi.
  unfold reac_boxreg_add_c.add_bytes. set (n := Boxreg.bx_n bs) in *.
  pose proof (reac_boxreg_add_inv.add_row_length M b k HM) as HRL.
  pose proof (OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Mem.length_le4 (Z_to_bv 64 (n + 1))) as HL4.
  assert (HL1 : length (UPD bs (Z.to_nat (56 * n)) (reac_boxreg_add_c.add_row M b k)) = 288%nat)
    by (rewrite OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Mem.upd_bytes_length; rewrite ?HRL, ?HL; lia).
  change 280%nat with (Z.to_nat 280).
  destruct (Z.leb_spec0 (56 * n) i); destruct (Z.ltb_spec0 i (56 * n + 56)); cbn [andb].
  1: {
    rewrite lb_upd_out by (rewrite ?HL1, ?HL4; lia).
    rewrite lb_upd_in by (rewrite ?HL, ?HRL; lia).
    set (o := i - 56 * n). assert (Ho : 0 <= o < 56) by (unfold o; lia). clearbody o.
    destruct (Z.ltb_spec0 o 6); [|destruct (Z.ltb_spec0 o 8); [|destruct (Z.ltb_spec0 o 12);
      [|destruct (Z.ltb_spec0 o 16)]]].
    - rewrite (lb_bxb_sub _ M 0 6 o ltac:(lia) ltac:(lia) (reac_boxreg_add_inv.add_row_mac M b k HM) ltac:(lia)).
      rewrite Z.sub_0_r. reflexivity.
    - unfold bxb, reac_boxreg_add_c.add_row. rewrite app_nth2 by (rewrite HM; lia). rewrite HM.
      rewrite app_nth1 by (rewrite repeat_length; lia). rewrite nth_repeat. reflexivity.
    - exact (lb_bxb_sub _ _ 8 4 o ltac:(lia) ltac:(lia) (reac_boxreg_add_inv.add_row_base M b k HM) ltac:(lia)).
    - exact (lb_bxb_sub _ _ 12 4 o ltac:(lia) ltac:(lia) (reac_boxreg_add_inv.add_row_nch M b k HM) ltac:(lia)).
    - destruct (Z.ltb_spec0 o 20); [|destruct (Z.ltb_spec0 o 24)].
      + rewrite (lb_bxb_sub _ _ 16 4 o ltac:(lia) ltac:(lia) (reac_boxreg_add_inv.add_row_est M b k HM) ltac:(lia)).
        rewrite lb_le4_0. unfold bxb. rewrite nth_repeat. reflexivity.
      + rewrite (lb_bxb_sub _ _ 20 4 o ltac:(lia) ltac:(lia) (reac_boxreg_add_inv.add_row_pin M b k HM) ltac:(lia)).
        rewrite lb_le4_0. unfold bxb. rewrite nth_repeat. reflexivity.
      + rewrite (lb_bxb_sub _ _ 24 32 o ltac:(lia) ltac:(lia) (reac_boxreg_add_inv.add_row_name M b k HM) ltac:(lia)).
        unfold bxb. rewrite nth_repeat. reflexivity. }
  all: destruct (Z.leb_spec0 280 i); destruct (Z.ltb_spec0 i 284); cbn [andb].
  all: first
    [ rewrite lb_upd_in by (rewrite ?HL1, ?HL4; lia); reflexivity
    | rewrite lb_upd_out by (rewrite ?HL1, ?HL4; lia); rewrite lb_upd_out by (rewrite ?HL, ?HRL; lia); reflexivity ].
Qed.
(* The return: a state at the ret slot with ra and the callee-saved registers restored, a0 = z, and the registry
   holding bs'. *)
Lemma add_ret : forall ly S W regs mem md ch r p k bs M E ms mdc ss z bs',
  add_pre ly S W regs mem md ch r p k bs M -> EOK regs r bs E ->
  ajournal SEGS B REAC_BOXREG_ADD_STKB (spZ regs) [(r, r + REG_SIZEB)] ly S W mem md [] ly S W (ms_mem ms) mdc 0 ->
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  plookup pl_tpi (ss_pc ss) = Some (PW RET_WORD_r) ->
  sr_get (ss_regs ss) 1 = SOff 1 0 ->
  forallb (fun r0 : bv 5 => sv_eqb (sr_get (ss_regs ss) r0) (SOff (Z.to_nat (bv_unsigned r0)) 0)) CALLEE_SAVED = true ->
  sv_denot E (sr_get (ss_regs ss) 10) = w64 z ->
  reac_boxreg_add_c.add_out bs M k z bs' ->
  (forall i, 0 <= i < REG_SIZEB -> aview SEGS (w_H W) (ms_mem ms) (r + i) = Some (bxb bs' i)) ->
  SRr SEGS W (mkCfg ms mdc) (tbreac_boxreg_add_post regs ly S W mem md r k bs M).
Proof.
  intros ly S W regs mem md ch r p k bs M E ms mdc ss z bs' HPRE HEOK HJ HS Hrv Hpl Hr1 Hcs Hz Hout Hbs.
  pose proof HPRE as (HFN & _).
  pose proof HFN as (_ & Hra & _).
  destruct HEOK as (_ & HAE).
  assert (HAE32 : env_agree 32 (Ereg regs (add_xs r bs)) E).
  { destruct HAE as [HA HD]. split; [intros n Hn; apply HA; lia | exact HD]. }
  assert (R1 : getr (ms_regs ms) 1 = getr regs 1).
  { rewrite (st_ok_pi_restrict_reg (w_H W) E ss ms (1%bv : bv 5) HS), Hr1. cbn [sv_denot].
    rewrite (proj1 HAE 1%nat ltac:(lia)), (ew_Ereg_nat regs _ 1 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned.
    reflexivity. }
  pose (RET := paj_ret_at (PL := PL_boxb) (PI := PI)).
  apply (RET W E ss ms mdc _ HS Hrv Hpl). intros mat'.
  unfold tbreac_boxreg_add_post, apost_base.
  exists ly, S, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat' mdc).
  split; [rewrite R1, Hra; reflexivity|].
  split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ|].
  split; [eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs (add_xs r bs) HS); [exact HAE32 | exact Hcs]|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [apply Permutation_refl|].
  exists z, bs'. split; [|split; [exact Hout | exact Hbs]].
  rewrite (st_ok_pi_restrict_reg (w_H W) E ss ms (10%bv : bv 5) HS). exact Hz.
Qed.
(* The two segments after the bind loop. *)
(* Helper of the bind segment (prefix bd_). bd_keep: the bytes an engine run leaves as they were, from the run's
   frame_of, when its only write window is the frame's [sp - 80, sp) (bd_frame_only checks the windows). *)
Definition bd_frame_only (rs : smem) : bool :=
  forallb (fun x => match x with (b, wlo, whi) =>
    (whi <=? wlo) || (obase_eqb b (Some 2%nat) && (wlo =? -80) && (whi =? 0)) end) (windows rs).
Lemma bd_keep : forall E rs H (m m' : word -> option byte) sp,
  frame_of E rs (mrestrict H m) (mrestrict H m') -> bd_frame_only rs = true -> bv_unsigned (ew E 2) = sp ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 80 <= a < sp) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
  intros E rs H m m' sp HF Hok Hsp a Ha Hs.
  apply (kept_of_frame E rs H m m' (fun x => sp - 80 <= x < sp) HF); [| exact Ha | exact Hs].
  intros b wlo whi x Hin Hx. unfold bd_frame_only in Hok. rewrite forallb_forall in Hok.
  specialize (Hok _ Hin). cbn beta iota in Hok. apply orb_prop in Hok as [Hok | Hok].
  - apply Z.leb_le in Hok. lia.
  - apply andb_prop in Hok as [Hok H3]. apply andb_prop in Hok as [H1 H2].
    destruct b as [b|]; [|discriminate]. cbn in H1. apply Nat.eqb_eq in H1. subst b.
    apply Z.eqb_eq in H2. apply Z.eqb_eq in H3. subst wlo whi. cbn [base_val] in Hx. lia.
Qed.
Lemma add_bind_seg : forall ly S W regs mem md ch r p k bs M E ms mdc j,
  add_pre ly S W regs mem md ch r p k bs M -> add_cur ly S W regs mem md r bs E ms mdc ->
  st_ok_pi SEGS VAL E (ss_bind j) (restrict (w_H W) ms) -> 0 <= j < 5 ->
  M <> Boxreg.zero6 -> reac_boxreg_add_c.add_width_ok k (Boxreg.bx_fabric bs) ->
  reac_boxreg_add_c.add_none_held bs M -> reac_boxreg_add_c.add_unbound bs k j ->
  SRr SEGS W (mkCfg ms mdc) (tbreac_boxreg_add_post regs ly S W mem md r k bs M).
Proof.
  intros ly S W regs mem md ch r p k bs M E ms mdc j HPRE HCUR HS Hj HM HWD HNH HUB.
  pose proof HPRE as (HPRE0 & H10 & H11 & H12 & Hk & Hin & HB & HI & HFO & HML & HMB).
  pose proof HPRE0 as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). pose proof add_stk as WS.
  assert (Hes : ESTACK = 4096) by reflexivity. pose proof pa_segs_low as Hsegs.
  destruct (al_blocks _ _ LAWS ly S W mem md r REG_SIZEB HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
  change (req_size REG_SIZEB) with 288 in *.
  pose proof HFO as ((cid & pos & Hfin & Hcid & Hfal & Hflo & Hfhi) & Hp8 & HRA).
  destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Happ).
  pose proof (sep_block_frame SEGS B LAWS ly S W mem md r REG_SIZEB cid pos HAR Hin Hfin) as Hsep.
  unfold zdisjoint in Hsep; cbn [fst snd] in Hsep. change (req_size REG_SIZEB) with 288 in Hsep.
  pose proof (fs_frame_bytes_nonneg cid) as Hfs0.
  destruct HCUR as (HEOK & SHOK & HJ & HBc).
  pose proof (proj1 HEOK) as HEI.
  assert (E2 : ew E 2 = getr regs 2) by (rewrite (EOK_reg _ _ _ _ 2 HEOK ltac:(lia)); reflexivity).
  assert (E3 : ew E 3 = getr regs 3) by (rewrite (EOK_reg _ _ _ _ 3 HEOK ltac:(lia)); reflexivity).
  assert (E4 : ew E 4 = getr regs 4) by (rewrite (EOK_reg _ _ _ _ 4 HEOK ltac:(lia)); reflexivity).
  assert (E10 : ew E 10 = Z_to_bv 64 r) by (rewrite (EOK_reg _ _ _ _ 10 HEOK ltac:(lia)); exact H10).
  assert (E11 : ew E 11 = Z_to_bv 64 p) by (rewrite (EOK_reg _ _ _ _ 11 HEOK ltac:(lia)); exact H11).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (Hlen : length bs = 288%nat) by (destruct HI as [[HL _] _]; exact HL).
  pose (RUN := paj_run (PL := PL_boxb) B LAWS).
  assert (Hjc : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4) by lia.
  (* Each row j0: the run to the call of __asan_memcpy (r + 56 j, p, 6) (0x821f4), the call, the run to the ret
     (0x82028) with a0 = j, and add_ret with add_out's third case. *)
  destruct Hjc as [Hjv|[Hjv|[Hjv|[Hjv|Hjv]]]]; rewrite Hjv in HS;
  (paj_run_tok RUN HS HJ SHOK ABspan; [awr_ok_tac; exact Usp |];
  pmkst HS;
  prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (12%bv : bv 5) Ra2;
  prreg HS (1%bv : bv 5) Rra; prreg HS (2%bv : bv 5) Rsp; prreg HS (3%bv : bv 5) Rgp; prreg HS (4%bv : bv 5) Rtp;
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
  assert (Qsp : spZ rg = spZ regs + -80) by (unfold spZ at 1; rewrite Rsp, Usp, unsigned_lit_small by lia; reflexivity);
  pose proof (add_afobj_now ly S W regs mem md ch r p k bs M _ _ HPRE HJ) as HFO1;
  pose proof (add_mac_now ly S W regs mem md ch r p k bs M _ _ HPRE HJ) as HMB1;
  pose proof (proj1 HJ) as HAR1;
  eapply SRr_bind;
  [ eapply (aj_intrin_at SEGS B LAWS Hsegs OCpy (pa_sigma BB___asan_memcpy) AMEMCPY W rg mm
      REAC_BOXREG_ADD_STKB (spZ regs) [(r, r + REG_SIZEB)] ly S W mem md [] ly S _ 0 (r + 56 * j) p 6 (-80) _ HJ);
    [ rewrite Ra0, E10; rewrite ?unsigned_lit_small by lia; unfold w64; f_equal; lia
    | rewrite Ra1, E11; reflexivity
    | rewrite Ra2; reflexivity
    | lia | lia | lia
    | exact Qsp
    | reflexivity
    | lia
    | rewrite WS, Hes; lia
    | rewrite Rgp, E3; exact Hgp
    | rewrite Rtp, E4; exact Htp
    | exact Rra
    | apply ret_ok_codeptr_v; [lia | reflexivity]
    | intros a Ha; split;
      [ right; left; split;
        [ exists (r, r + REG_SIZEB); split; [left; reflexivity | cbn [fst snd]; unfold REG_SIZEB; lia]
        | exists r, REG_SIZEB; split; [exact Hin | change (req_size REG_SIZEB) with 288; lia] ]
      | rewrite Hes; lia ]
    | exact (amem_range_of_block SEGS B LAWS _ _ _ _ _ r REG_SIZEB (r + 56 * j) 6 HAR1 Hin ltac:(lia)
               ltac:(change (req_size REG_SIZEB) with 288; lia))
    | exact (range_addressable_of_block SEGS B LAWS _ _ _ _ _ r REG_SIZEB (r + 56 * j) 6 HAR1 Hin ltac:(lia)
               ltac:(change (req_size REG_SIZEB) with 288; lia))
    | intros _; exact (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ r REG_SIZEB (r + 56 * j) 6 HAR1 Hin ltac:(lia)
                         ltac:(change (req_size REG_SIZEB) with 288; lia) ltac:(lia))
    | split; [lia|]; split; [lia|]; split;
      [ intros a Ha; split;
        [ replace a with (p + (a - p)) by lia; rewrite (HMB1 (a - p) ltac:(lia)); discriminate
        | rewrite Qsp, Hes; lia ]
      | split; [lia|]; split; [exact (amem_range_sub_app _ _ p 6 Happ Hfceil Hflo Hfhi ltac:(lia))|];
        split; [exact (proj2 (proj2 HFO1))|];
        intros _; exact (shadow_hull_vis_of_frame SEGS B LAWS _ _ _ _ _ cid pos p 6 HAR1 Hfin Hflo Hfhi ltac:(lia)) ] ]
  | ]
  end;
  cbv beta; intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Heff & Hfr & Hpres2);
  jafter_call_keep_hi HS 680%nat regs2 (mrestrict (w_H W) mem2) HP2 [0%nat] HS2;
  match type of HS2 with ?Q -> _ =>
    assert (HQ : Q);
    [ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_nil];
      eapply (region_kept_aview E (w_H W) _ mem2 2%nat (spZ regs)); [exact Usp | | exact Hpres2];
      intros a Ha; apply Hfr; lia
    | specialize (HS2 HQ); clear HQ ]
  end;
  clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS;
  pose proof (img_env_havoc_hi E 680%nat (map (getr regs2) CLOB) HEI ltac:(cbv; lia)) as HEI2;
  assert (HEOK2 : EOK regs r bs (havoc E 680 (map (getr regs2) CLOB))) by (apply EOK_havoc; [exact HEOK | cbv; lia]);
  pose proof (sh_ok_of_block ly S W mem2 md2 regs r bs _ (proj1 HJ2) Hin HEOK2 H10) as SHOK2;
  clear SHOK; rename HF into HF1, HFr into HFr1, HG into HG1;
  paj_run_tok RUN HS HJ2 SHOK2 ABspan; [awr_ok_tac; rewrite ew_havoc_old by lia; exact Usp |];
  assert (Usp2 : bv_unsigned (ew (havoc E 680 (map (getr regs2) CLOB)) 2) = spZ regs)
    by (rewrite ew_havoc_old by lia; exact Usp);
  pose proof (bd_keep _ _ _ _ _ (spZ regs) HFr ltac:(vm_compute; reflexivity) Usp2) as K2;
  pose proof (bd_keep _ _ _ _ _ (spZ regs) HFr1 ltac:(vm_compute; reflexivity) Usp) as K1;
  lazymatch type of HS with st_ok_pi _ _ ?Ef ?ssf (restrict _ ?msf) =>
    apply (add_ret ly S W regs mem md ch r p k bs M Ef msf _ ssf j (UPD bs (Z.to_nat (56 * j)) M) HPRE HEOK2 HJ2 HS
             eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
  end;
  [ lazymatch goal with |- sv_denot _ ?e = _ => let v := eval vm_compute in e in change e with v end;
    cbn [sv_denot]; unfold w64; f_equal; lia
  | right; right; left; split; [exact HWD|]; split; [exact HM|]; split; [exact HNH|]; split; [exact HUB | reflexivity]
  | intros i Hi; unfold REG_SIZEB in Hi;
    rewrite bxb_upd_bind by (first [exact Hlen | exact HML | lia]);
    rewrite (K2 (r + i) ltac:(lia) ltac:(lia));
    destruct ((56 * j <=? i) && (i <? 56 * j + 6)) eqn:Hrow;
    [ apply andb_prop in Hrow as [Q1 Q2]; apply Z.leb_le in Q1; apply Z.ltb_lt in Q2;
      replace (r + i) with (r + 56 * j + (i - 56 * j)) by lia;
      rewrite (Heff (i - 56 * j) ltac:(lia)); exact (HMB1 (i - 56 * j) ltac:(lia))
    | assert (Hnr : ~ (r + 56 * j <= r + i < r + 56 * j + 6))
        by (apply andb_false_iff in Hrow; destruct Hrow as [Q|Q]; [apply Z.leb_gt in Q | apply Z.ltb_ge in Q]; lia);
      rewrite (Hfr (r + i) ltac:(lia) Hnr ltac:(lia));
      rewrite (K1 (r + i) ltac:(lia) ltac:(lia));
      exact (HBc i ltac:(unfold REG_SIZEB; lia)) ] ]).
Qed.
(* After an engine run: the registry bytes are kept (the run writes only the frame window) and EOK moves to the
   run's environment. *)
Lemma mac_byte : forall bs i j, length bs = 288%nat -> 0 <= i < 5 -> 0 <= j < 6 ->
  nth_error (Boxreg.bx_mac bs i) (Z.to_nat j) = Some (nth (Z.to_nat (56 * i + j)) bs (Z_to_bv 8 0)).
Proof.
  intros bs i j HL Hi Hj. unfold Boxreg.bx_mac. rewrite BoxregUpd.nth_bsub by lia. change (Z.to_nat 6) with 6%nat.
  replace (Z.to_nat j <? 6)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  rewrite (nth_error_nth' bs (Z_to_bv 8 0)) by lia. do 2 f_equal. lia.
Qed.
Lemma mac_nz : forall bs i j, length bs = 288%nat -> 0 <= i < 5 -> 0 <= j < 6 -> bxb bs (56 * i + j) <> 0 ->
  Boxreg.bx_mac bs i <> Boxreg.zero6.
Proof.
  intros bs i j HL Hi Hj Hb Hz. pose proof (mac_byte bs i j HL Hi Hj) as H. rewrite Hz in H.
  apply BoxregStep.bx_zero6_nth in H. apply Hb. unfold bxb. rewrite H. reflexivity.
Qed.
Lemma mac_z : forall bs i, length bs = 288%nat -> 0 <= i < 5 -> (forall j, 0 <= j < 6 -> bxb bs (56 * i + j) = 0) ->
  Boxreg.bx_mac bs i = Boxreg.zero6.
Proof.
  intros bs i HL Hi Hz. apply BoxregStep.bx_zero6_of.
  - unfold Boxreg.bx_mac. rewrite Boxreg.bsub_length by lia. reflexivity.
  - intros j Hj. replace j with (Z.to_nat (Z.of_nat j)) by lia. rewrite (mac_byte bs i (Z.of_nat j) HL Hi ltac:(lia)).
    f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. specialize (Hz (Z.of_nat j) ltac:(lia)). unfold bxb in Hz.
    rewrite Hz. reflexivity.
Qed.
Lemma nch_swrap : forall bs i, length bs = 288%nat -> 0 <= i < 5 ->
  Boxreg.bx_nch bs i = bv_swrap 32 (bxu4 bs (56 * i + 12)).
Proof. intros bs i HL Hi. unfold Boxreg.bx_nch, Boxreg.rd4. rewrite bxu4_bytes by lia. reflexivity. Qed.
(* The new-row writes: the alias that fixes 56 n for a concrete n, and the two registry windows the stores use. *)
Definition LHS56 : sv := SAlu ALU_SUB (SAlu ALU_SLL (SOff 33 0) (SLit 6)) (SAlu ALU_SLL (SOff 33 0) (SLit 3)).
Lemma den56 : forall E c, ew E 33 = Z_to_bv 64 c -> 0 <= c <= 5 -> sv_denot E LHS56 = sv_denot E (SLit (56 * c)).
Proof.
  intros E c H Hc. rewrite (denot_lit_U E LHS56), (denot_lit_U E (SLit _)). f_equal. unfold LHS56.
  rewrite !U_SAlu, (U_atom E 33 c H), !U_lit by lia. cbn [zalu_raw]. change (Z.land 6 63) with 6. change (Z.land 3 63) with 3.
  rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 6) with 64. change (2 ^ 3) with 8. unfold zcanon, M64.
  rewrite (Z.mod_small (c * 64) (2 ^ 64)) by lia. rewrite (Z.mod_small (c * 8) (2 ^ 64)) by lia.
  rewrite (Z.mod_small (c * 64 - c * 8) (2 ^ 64)) by lia. lia.
Qed.
Definition R2a (c : Z) : YP09.region := YP09.mkRegion (Some 10%nat) (56 * c + 8) (56 * c + 16) (56 * c + 8) (56 * c + 16) [].
Definition R2b : YP09.region :=
  YP09.mkRegion (Some 10%nat) 280 288 280 284 [YP09.mkChunk 280 (CVal 4 (SOff 33 0)); YP09.mkChunk 284 (CVal 4 (SOff 34 0))].
Lemma aview_of_val4 : forall H m a v, val_mem SEGS (mrestrict H m) a 4 v -> 0 <= v < 2 ^ 32 ->
  forall j, 0 <= j < 4 -> aview SEGS H m (a + j) = Some (YG0f.le_byte v 4 (Z.to_nat j)).
Proof.
  intros H m a v Hv Hr j Hj. unfold aview. replace (a + j) with (a + Z.of_nat (Z.to_nat j)) by lia.
  rewrite (Hv (Z.to_nat j) ltac:(lia)). cbn [option_map]. f_equal. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. unfold YO0f.le_byte, YG0f.le_byte. apply Z.mod_mod. lia.
Qed.
Lemma R2_ok : forall ly S (W : world SEGS) m md (regs : bvmap 5 word) r bs E c,
  EOK regs r bs E -> getr regs 10 = w64 r -> AR SEGS B ly S W m md -> In (r, REG_SIZEB) (ablocks B ly S) -> 0 <= c <= 4 ->
  (forall j, 0 <= j < 8 -> aview SEGS (w_H W) m (r + (280 + j)) = Some (bxb bs (280 + j))) ->
  region_ok SEGS E (mrestrict (w_H W) m) (R2a c) /\ region_ok SEGS E (mrestrict (w_H W) m) R2b.
Proof.
  intros ly S W m md regs r bs E c HE H10 HAR Hin Hc HB.
  destruct (al_blocks _ _ LAWS ly S W m md r REG_SIZEB HAR Hin) as (_ & Hr4096 & Hrceil & _ & Hbp & _).
  change (req_size REG_SIZEB) with 288 in *. pose proof (asan_consts) as (C1 & _).
  assert (E10 : bv_unsigned (ew E 10) = r).
  { rewrite (EOK_reg _ _ _ _ 10 HE) by lia. change (getr regs (Z_to_bv 5 (Z.of_nat 10))) with (getr regs 10).
    rewrite H10. apply unsigned_lit_small. lia. }
  split; unfold region_ok, R2a, R2b; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
    rewrite E10; (split; [lia|]); (split; [lia|]); split.
  - intros o Ho. apply (apresent_writable SEGS). apply (proj1 (Hbp (r + o) ltac:(lia))).
  - constructor.
  - intros o Ho. apply (apresent_writable SEGS). apply (proj1 (Hbp (r + o) ltac:(lia))).
  - repeat apply Forall_cons; try apply Forall_nil.
    + apply (chunk_ok_val SEGS E _ r 280 4 (SOff 33 0) (bxu4 bs 280));
        [cbn [sv_denot]; rewrite Z.add_0_r; eok_ew HE 33%nat; rewrite Z_to_bv_bv_unsigned; reflexivity
        | pose proof (bxu4_range bs 280); zside | zside |].
      apply val4_of_aview. intros j Hj. rewrite <- Z.add_assoc. apply (HB j). lia.
    + apply (chunk_ok_val SEGS E _ r 284 4 (SOff 34 0) (bxu4 bs 284));
        [cbn [sv_denot]; rewrite Z.add_0_r; eok_ew HE 34%nat; rewrite Z_to_bv_bv_unsigned; reflexivity
        | pose proof (bxu4_range bs 284); zside | zside |].
      apply val4_of_aview. intros j Hj. rewrite <- Z.add_assoc. replace (284 + j) with (280 + (4 + j)) by lia. apply (HB (4 + j)). lia.
Qed.
(* The regions an intrinsic call (memset / memcpy into the registry) keeps. *)
Lemma kept_intrin3 : forall ly S (W : world SEGS) (regs : bvmap 5 word) r bs E m md m2 md2 cs d n,
  EOK regs r bs E -> AR SEGS B ly S W m md -> AR SEGS B ly S W m2 md2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regs + -80 - ESTACK <= a < spZ regs + -80) ->
     aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m a) ->
  0 <= d -> 0 <= n -> d + n <= spZ regs - 80 - ESTACK -> spZ regs < 2 ^ 64 ->
  (forall a, spZ regs - 80 <= a < spZ regs -> apresent (w_H W) m2 a) ->
  Forall (region_kept SEGS E (mrestrict (w_H W) m) (mrestrict (w_H W) m2))
    [YP09.mkRegion (Some 2%nat) (-80) 0 (-80) 0 cs; got_regionP; bcell_regionP 32].
Proof.
  intros ly S W regs r bs E m md m2 md2 cs d n HE HAR HAR2 Hfr Hd0 Hn0 Hdn Hsp Hpres2.
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EOK_reg _ _ _ _ 2 HE) by lia; reflexivity).
  destruct (al_const _ _ LAWS ly S W m md HAR) as (Kcell & _ & Kgot & _).
  destruct (al_const _ _ LAWS ly S W m2 md2 HAR2) as (Kcell2 & _ & Kgot2 & _).
  rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot, Kgot2. rewrite (pal_cell B TL) in Kcell, Kcell2.
  assert (Eo1 : bv_unsigned (ew E (A_OBJ 1)) = VAL (A_OBJ 1)) by (apply (proj1 HE); unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Eo12 : bv_unsigned (ew E (A_OBJ 12)) = VAL (A_OBJ 12)) by (apply (proj1 HE); unfold A_OBJ, A_TEXT, A_LIM; lia).
  repeat apply Forall_cons; try apply Forall_nil.
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha.
    + apply (mbyte_of_aview SEGS). apply Hfr; unfold ESTACK in *; lia.
    + intros _. apply (apresent_writable SEGS). apply Hpres2. lia.
  - unfold got_regionP.
    apply (region_kept_val_at E _ _ (A_OBJ 1) (VAL (A_OBJ 1)) 8 (VAL (A_OBJ 12)) 0 0); [exact Eo1 | | | lia].
    + exact (val_mem_of_rdword SEGS (w_H W) m _ _ Kgot).
    + exact (val_mem_of_rdword SEGS (w_H W) m2 _ _ Kgot2).
  - unfold bcell_regionP.
    apply (region_kept_val_at E _ _ (A_OBJ 12) (VAL (A_OBJ 12)) 8 SHADOW_OFF 0 0); [exact Eo12 | | | lia].
    + exact (val_mem_of_rdword SEGS (w_H W) m _ _ Kcell).
    + exact (val_mem_of_rdword SEGS (w_H W) m2 _ _ Kcell2).
Qed.
Lemma kept_R : forall (W : world SEGS) (regs : bvmap 5 word) r bs E m m2 d n lo hi wlo whi cs,
  EOK regs r bs E -> getr regs 10 = w64 r -> 0 <= r < 2 ^ 64 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regs + -80 - ESTACK <= a < spZ regs + -80) ->
     aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m a) ->
  (forall a, apresent (w_H W) m a -> apresent (w_H W) m2 a) ->
  (forall a, r + lo <= a < r + hi -> 0 <= a < 2 ^ 64 /\ ~ (d <= a < d + n) /\ ~ (spZ regs + -80 - ESTACK <= a < spZ regs + -80)) ->
  region_kept SEGS E (mrestrict (w_H W) m) (mrestrict (w_H W) m2) (YP09.mkRegion (Some 10%nat) lo hi wlo whi cs).
Proof.
  intros W regs r bs E m m2 d n lo hi wlo whi cs HE H10 Hr Hfr Hpr Hout.
  apply (region_kept_aview E (w_H W) m m2 10 r lo hi wlo whi cs).
  - rewrite (EOK_reg _ _ _ _ 10 HE) by lia. change (getr regs (Z_to_bv 5 (Z.of_nat 10))) with (getr regs 10).
    rewrite H10. apply unsigned_lit_small. lia.
  - intros a Ha. destruct (Hout a Ha) as (H0 & H1 & H2). apply Hfr; assumption.
  - exact Hpr.
Qed.
(* The bind loop: the row head 0x8207c and the row end 0x820fc for row i. *)
Definition ROWP (i : Z) : Prop := forall ly S W regs mem md ch r p k bs M E ms mdc,
  add_pre ly S W regs mem md ch r p k bs M -> add_cur ly S W regs mem md r bs E ms mdc ->
  st_ok_pi SEGS VAL E (ss_row i) (restrict (w_H W) ms) -> i < Boxreg.bx_n bs ->
  M <> Boxreg.zero6 -> reac_boxreg_add_c.add_width_ok k (Boxreg.bx_fabric bs) -> reac_boxreg_add_c.add_none_held bs M ->
  (forall j, 0 <= j < i -> ~ (Boxreg.bx_mac bs j = Boxreg.zero6 /\ Boxreg.bx_nch bs j = k)) ->
  SRr SEGS W (mkCfg ms mdc) (tbreac_boxreg_add_post regs ly S W mem md r k bs M).
Definition TAILP (i : Z) : Prop := forall ly S W regs mem md ch r p k bs M E ms mdc,
  add_pre ly S W regs mem md ch r p k bs M -> add_cur ly S W regs mem md r bs E ms mdc ->
  st_ok_pi SEGS VAL E (ss_tail i) (restrict (w_H W) ms) -> i < Boxreg.bx_n bs ->
  M <> Boxreg.zero6 -> reac_boxreg_add_c.add_width_ok k (Boxreg.bx_fabric bs) -> reac_boxreg_add_c.add_none_held bs M ->
  (forall j, 0 <= j <= i -> ~ (Boxreg.bx_mac bs j = Boxreg.zero6 /\ Boxreg.bx_nch bs j = k)) ->
  SRr SEGS W (mkCfg ms mdc) (tbreac_boxreg_add_post regs ly S W mem md r k bs M).
Ltac post_run regs :=
  lazymatch goal with
  | HFr : frame_of ?E0 ?rs (mrestrict (w_H ?W) ?m0) (mrestrict (w_H ?W) ?m1), HK : KEEPR ?W ?m0 ?r ?bs,
    HE : EOK regs ?r ?bs ?E0 |- _ =>
    let HK' := fresh "HK" in
    assert (HK' : KEEPR W m1 r bs) by
      (apply (keep_run E0 rs W m0 m1 (spZ regs) r bs);
       [ vm_compute; reflexivity | rewrite (EOK_reg _ _ _ _ 2 HE) by lia; reflexivity | lia | unfold REG_SIZEB; lia
       | exact HFr | exact HK ]);
    clear HK HFr; rename HK' into HK
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  lazymatch goal with
  | HS : context [restrict (w_H _) _], HE : EOK regs ?r ?bs ?E0 |- _ =>
    let E1 := lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ => E1 | st_ok _ ?E1 _ _ => E1 end in
    lazymatch E1 with
    | E0 => idtac
    | _ => let HE' := fresh "HE" in
           assert (HE' : EOK regs r bs E1) by
             (apply (EOK_mono regs r bs E0 E1 HE); [assumption | intros nn Hnn; cbn [extK]; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]);
           clear HE; rename HE' into HE
    end
  end.
Ltac arun RUN regs HS HJ SHOK :=
  paj_run_tok RUN HS HJ SHOK ABspan;
  [ awr_ok_tac; lazymatch goal with HE : EOK _ _ _ _ |- _ => rewrite (EOK_reg _ _ _ _ 2 HE) by lia; reflexivity end
  | post_run regs ].
Ltac show_stop RUN :=
  lazymatch goal with HS : st_ok_pi _ _ _ ?ss _, SHOK : sh_ok _ ?Bx ?SH _ _ |- _ =>
  let pc := eval vm_compute in (ss_pc ss) in
  lazymatch paj_tables RUN with (?tpi, ?tw) =>
  let K := eval vm_compute in (run_K A_LIM Bx SH ss) in
  let why := psym_why_tok tpi tw K Bx ABspan SH (start K Bx ABspan SH ss) in idtac "STOP" pc why end end.
Ltac ret_with RUN regs HP z bs' HS HJ SHOK :=
  arun RUN regs HS HJ SHOK;
  lazymatch goal with
  | HS0 : st_ok_pi _ _ ?Ex ?ssx (restrict (w_H ?Wx) ?msx), HE : EOK _ _ _ ?Ex, HK : KEEPR _ _ _ _ |- _ =>
    eapply (add_ret _ _ _ _ _ _ _ _ _ _ _ _ Ex msx _ ssx z bs' HP HE HJ HS0 eq_refl ltac:(vm_compute; reflexivity)
              eq_refl ltac:(vm_compute; reflexivity)); [ | | exact HK ];
    [ let v := eval vm_compute in (sr_get (ss_regs ssx) 10) in change (sr_get (ss_regs ssx) 10) with v | ]
  end.
Ltac after_prog_call regs kj Rra HS HJ SHOK HK HE HJ2 HJc HP2 :=
  lazymatch type of HJ2 with ajournal _ _ _ _ _ ?ly ?S ?W _ _ _ _ _ _ ?mem2 ?md2 _ =>
  lazymatch type of HP2 with aregs_preserved _ ?regs2 =>
  let HS2 := fresh "HS2" in
  jafter_call_keep_hi HS kj regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3]%nat HS2;
  match type of HS2 with ?Q -> _ =>
    let HQ := fresh "HQ" in
    assert (HQ : Q);
    [ cbn [ms_mem restrict];
      lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?m1 ?md1 _ =>
      lazymatch goal with Hin : In (?r, REG_SIZEB) (ablocks _ _ _), H10 : getr regs 10 = w64 ?r |- _ =>
      eapply (kept_call4 ly S W regs r _ _ m1 md1 mem2 md2 _ _ _ HE H10 _ (proj1 HJ) (proj1 HJ2) Hin HJc);
      [ intros a Ha; pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr & _); apply Hpr;
        lazymatch goal with WS : REAC_BOXREG_ADD_STKB = _ |- _ => rewrite WS end; lia
      | lia ] end end
    | specialize (HS2 HQ); clear HQ ] end;
  lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?m1 ?md1 _ =>
  lazymatch goal with Hin : In (?r, REG_SIZEB) (ablocks _ _ _), H10 : getr regs 10 = w64 ?r |- _ =>
  let HK' := fresh "HK" in
  assert (HK' : KEEPR W mem2 _ _) by (exact (keep_call ly S W r _ m1 md1 mem2 md2 _ _ _ Hin HJc HK));
  clear HK; rename HK' into HK;
  let HE' := fresh "HE" in
  assert (HE' : EOK regs r _ (havoc _ kj (map (getr regs2) CLOB))) by (apply EOK_havoc; [exact HE | unfold A_LIM; lia]);
  clear HE; rename HE' into HE;
  clear SHOK; assert (SHOK : sh_ok SEGS ABx SH_add _ (mrestrict (w_H W) mem2))
    by (exact (sh_ok_of_block ly S W mem2 md2 regs r _ _ (proj1 HJ2) Hin HE H10)) end end;
  clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS;
  let HEI' := fresh "HEI" in pose proof (proj1 HE) as HEI';
  clear HJ HJc; rename HJ2 into HJ; rewrite Rra; clear Rra; try clear HP2
  end end.
Ltac arun_to RUNTO regs HS HJ SHOK stop :=
  paj_run_to_tok RUNTO HS HJ SHOK ABspan stop;
  [ awr_ok_tac; lazymatch goal with HE : EOK _ _ _ _ |- _ => rewrite (EOK_reg _ _ _ _ 2 HE) by lia; reflexivity end
  | post_run regs ].
(* Re-abstract HS to the canonical state tgt (same pc, regions); E becomes JE E regs. *)
Ltac reabs_to HS HE SHOK tgt :=
  lazymatch type of HS with st_ok_pi _ _ ?E ?ss ?msr =>
  let HS' := fresh "HS" in
  pose proof (add_reabs E ss msr (ss_regs tgt) HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
     ltac:(let l := eval vm_compute in (reabs_obl PJ (ss_regs tgt)) in change (reabs_obl PJ (ss_regs tgt)) with l;
           repeat constructor)) as HS';
  change (mkSS (ss_pc ss) (ss_regs tgt) (ss_mem ss) None add_facts) with tgt in HS';
  clear HS; rename HS' into HS;
  let HE' := fresh "HE" in pose proof (JE_EOK _ _ _ E (ms_regs msr) HE) as HE'; clear HE; rename HE' into HE;
  let SH' := fresh "SHOK" in pose proof (JE_sh E (ms_regs msr) _ SHOK) as SH'; clear SHOK; rename SH' into SHOK
  end.
Ltac a0_lit := cbn [sv_denot]; apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity.
Ltac zlit_goal := match goal with |- context [bxb ?b ?x] => let v := eval vm_compute in x in change x with v end.
Lemma nr_reabs : forall E ss ms c,
  st_ok_pi SEGS VAL E ss ms -> ss_pc ss = 8604 -> ss_mem ss = cregions ->
  reabs_check PJ (abs_ss VAL ss) (ss_regs (ss_nr c)) (ss_facts (ss_nr c)) = true ->
  Forall (fun rj : bv 5 * nat => ew (JE E (ms_regs ms)) (snd rj) = getr (ms_regs ms) (fst rj))
    (reabs_obl PJ (ss_regs (ss_nr c))) ->
  st_ok_pi SEGS VAL (JE E (ms_regs ms)) (ss_nr c) ms.
Proof.
  intros E ss ms c HS Hpc Hm Hck Hobl.
  assert (Hma : mem_atoms_pd PJ PT (ss_mem ss) = true) by (rewrite Hm; vm_compute; reflexivity).
  assert (H : st_ok_pi SEGS VAL (JE E (ms_regs ms))
                (mkSS (ss_pc ss) (ss_regs (ss_nr c)) (ss_mem ss) None (ss_facts (ss_nr c))) ms).
  { unfold st_ok_pi in *.
    exact (st_ok_reabs SEGS PJ E (JE E (ms_regs ms)) (abs_ss VAL ss) ms (ss_regs (ss_nr c)) (ss_mem ss)
             (ss_facts (ss_nr c)) HS (JE_agree E _) Hck Hobl ltac:(vm_compute; constructor)
             (mem_ok_agree_pd SEGS PJ PT E _ (ms_mem ms) (ss_mem ss) (JE_agree E _) Hma (st_ok_mem_ok SEGS E _ ms HS))). }
  rewrite Hpc, Hm in H. exact H.
Qed.
(* The new row from slot 8604 on: memset and memcpy of the row, the stores of b, k and n + 1, return n. *)
Definition NRP (c : Z) : Prop := forall ly S W regs mem md ch r p k bs M E ms mdc b,
  add_pre ly S W regs mem md ch r p k bs M -> add_cur ly S W regs mem md r bs E ms mdc ->
  st_ok_pi SEGS VAL E (ss_nr c) (restrict (w_H W) ms) -> Boxreg.bx_n bs = c ->
  ew E 644 = w64 b -> 0 <= b -> lowest_free_base_c.lowest_free bs k b ->
  M <> Boxreg.zero6 -> reac_boxreg_add_c.add_width_ok k (Boxreg.bx_fabric bs) ->
  reac_boxreg_add_c.add_none_held bs M -> reac_boxreg_add_c.add_none_unbound bs k ->
  SRr SEGS W (mkCfg ms mdc) (tbreac_boxreg_add_post regs ly S W mem md r k bs M).
(* Helpers of the new-row segment (prefix nr_). nr_keep: the bytes an engine run leaves as they were, from the
   run's frame_of, when its write windows are the frame's [sp - 80, sp) and windows of base atom 10 inside the
   ranges ws (nr_win_ok checks the windows). nr_env reads the walk's atoms out of an EOK environment. *)
Definition nr_win_ok (ws : list (Z * Z)) (rs : smem) : bool :=
  forallb (fun x => match x with (bb, wlo, whi) =>
    (whi <=? wlo) || (obase_eqb bb (Some 2%nat) && (wlo =? -80) && (whi =? 0)) ||
    (obase_eqb bb (Some 10%nat) && existsb (fun w => (fst w <=? wlo) && (whi <=? snd w)) ws) end) (windows rs).
Lemma nr_keep : forall E rs H (m m' : word -> option byte) sp r ws,
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  nr_win_ok ws rs = true -> bv_unsigned (ew E 2) = sp -> bv_unsigned (ew E 10) = r ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 80 <= a < sp) -> (forall w, In w ws -> ~ (r + fst w <= a < r + snd w)) ->
  aview SEGS H m' a = aview SEGS H m a.
Proof.
  intros E rs H m m' sp r ws HF Hok Hsp Hr a Ha Hs Hw.
  apply (kept_of_frame E rs H m m'
           (fun x => (sp - 80 <= x < sp) \/ exists w, In w ws /\ r + fst w <= x < r + snd w) HF); [| exact Ha |].
  - intros bb wlo whi x Hin Hx. unfold nr_win_ok in Hok. rewrite forallb_forall in Hok.
    specialize (Hok _ Hin). cbn beta iota in Hok.
    apply orb_prop in Hok as [Hok | Hok]; [apply orb_prop in Hok as [Hok | Hok] |].
    + apply Z.leb_le in Hok. lia.
    + apply andb_prop in Hok as [Hok H3]. apply andb_prop in Hok as [H1 H2].
      destruct bb as [bb|]; [|discriminate]. cbn in H1. apply Nat.eqb_eq in H1. subst bb.
      apply Z.eqb_eq in H2. apply Z.eqb_eq in H3. subst wlo whi. cbn [base_val] in Hx. left. lia.
    + apply andb_prop in Hok as [H1 H2]. destruct bb as [bb|]; [|discriminate]. cbn in H1. apply Nat.eqb_eq in H1. subst bb.
      apply existsb_exists in H2 as (w & Hin' & Hw'). apply andb_prop in Hw' as [Hw1 Hw2].
      apply Z.leb_le in Hw1. apply Z.leb_le in Hw2. cbn [base_val] in Hx. right. exists w. split; [exact Hin' | lia].
  - intros [Hx | (w & Hin & Hx)]; [exact (Hs Hx) | exact (Hw w Hin Hx)].
Qed.
Lemma nr_region_nth : forall E ss ms i rg,
  st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some rg -> region_ok SEGS E (ms_mem ms) rg.
Proof.
  intros E ss ms i rg HS Hi. unfold st_ok_pi in HS. destruct ss. exact (st_ok_region_nth E _ ms i rg HS Hi).
Qed.
Lemma nr_env : forall (regs : bvmap 5 word) r p k bs E,
  EOK regs r bs E -> getr regs 10 = w64 r -> getr regs 11 = w64 p -> getr regs 12 = w64 k -> 0 <= r < 2 ^ 64 ->
  ew E 10 = w64 r /\ bv_unsigned (ew E 10) = r /\ bv_unsigned (ew E 2) = spZ regs /\
  ew E 3 = getr regs 3 /\ ew E 4 = getr regs 4 /\ ew E 11 = w64 p /\ ew E 12 = w64 k /\
  ew E 33 = w64 (bxu4 bs 280).
Proof.
  intros regs r p k bs E HE H10 H11 H12 Hr.
  assert (E10 : ew E 10 = w64 r) by (rewrite (EOK_reg _ _ _ _ 10 HE ltac:(lia)); exact H10).
  split; [exact E10|]. split; [rewrite E10; apply unsigned_lit_small; lia|].
  split; [rewrite (EOK_reg _ _ _ _ 2 HE ltac:(lia)); reflexivity|].
  split; [rewrite (EOK_reg _ _ _ _ 3 HE ltac:(lia)); reflexivity|].
  split; [rewrite (EOK_reg _ _ _ _ 4 HE ltac:(lia)); reflexivity|].
  split; [rewrite (EOK_reg _ _ _ _ 11 HE ltac:(lia)); exact H11|].
  split; [rewrite (EOK_reg _ _ _ _ 12 HE ltac:(lia)); exact H12|].
  rewrite (EOK_xs _ _ _ _ 33 HE ltac:(lia)). cbn [nth map app add_xs mac_offs Nat.sub]. reflexivity.
Qed.
Lemma add_nr_seg : forall c, 0 <= c <= 4 -> NRP c.
Proof.
  intros c Hc0.
  assert (Hcv : c = 0 \/ c = 1 \/ c = 2 \/ c = 3 \/ c = 4) by lia.
  unfold NRP. intros ly S W regs mem md ch r p k bs M E ms mdc b HP HCUR HS Hn Eb Hb0 HLF HMnz WOK NH NU.
  destruct HCUR as (HE & SHOK & HJ & HK). change (KEEPR W (ms_mem ms) r bs) in HK.
  pose proof HP as (HPRE & H10 & H11 & H12 & Hk & Hin & HB & HI & HFO & HML & HMB).
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). pose proof add_stk as WS.
  assert (Hes : ESTACK = 4096) by reflexivity. pose proof pa_segs_low as Hsegs.
  destruct (al_blocks _ _ LAWS ly S W mem md r REG_SIZEB HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
  change (req_size REG_SIZEB) with 288 in *.
  pose proof HFO as ((cid & pos & Hfin & Hcid & Hfal & Hflo & Hfhi) & Hp8 & HRA).
  destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Happ).
  pose proof (sep_block_frame SEGS B LAWS ly S W mem md r REG_SIZEB cid pos HAR Hin Hfin) as Hsep.
  unfold zdisjoint in Hsep; cbn [fst snd] in Hsep. change (req_size REG_SIZEB) with 288 in Hsep.
  pose proof (fs_frame_bytes_nonneg cid) as Hfs0.
  pose proof HI as ([HL [HB1 [HB2 [HB3 _]]]] & _).
  unfold Boxreg.boxreg_B1, Boxreg.boxreg_B2 in HB1, HB2.
  pose proof WOK as (Hkev & Hk240 & Hkf).
  assert (Hbf : b + k <= Boxreg.bx_fabric bs) by (destruct HLF as [(He & _) | (_ & Hbf & _)]; lia).
  assert (Hu280 : bxu4 bs 280 = Boxreg.bx_n bs) by (apply bxu4_rd4; unfold Boxreg.bx_n in *; lia).
  pose proof (proj1 HE) as HEI.
  set (RUN := paj_run B LAWS).
  destruct Hcv as [Hcc|[Hcc|[Hcc|[Hcc|Hcc]]]]; rewrite Hcc in HS;
  (
  (* the run to the call of __asan_memset (r + 56 c, 0, 56) at 0x82184 *)
  arun RUN regs HS HJ SHOK;
  lazymatch goal with HE : EOK regs r bs ?Ec |- _ =>
    destruct (nr_env regs r p k bs Ec HE H10 H11 H12 ltac:(lia)) as (A10 & AU10 & AU2 & A3 & A4 & A11 & A12 & A33);
    assert (Ab : ew Ec 644 = w64 b) by (cbn [extK]; rewrite ?ew_ewset_other by lia; exact Eb) end;
  pmkst HS;
  prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (12%bv : bv 5) Ra2;
  prreg HS (1%bv : bv 5) Rra; prreg HS (2%bv : bv 5) Rsp; prreg HS (3%bv : bv 5) Rgp; prreg HS (4%bv : bv 5) Rtp;
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
    assert (Qsp : spZ rg = spZ regs + -80)
      by (unfold spZ at 1; rewrite Rsp, AU2, unsigned_lit_small by lia; reflexivity);
    eapply SRr_bind;
    [ eapply (aj_intrin_at SEGS B LAWS Hsegs OSet (pa_sigma BB___asan_memset) AMEMSET W rg mm
        REAC_BOXREG_ADD_STKB (spZ regs) [(r, r + REG_SIZEB)] ly S W mem md [] ly S _ 0 (r + 56 * c) 0 56 (-80) _ HJ);
      [ first [rewrite Ra0, AU10 | rewrite Ra0, A10]; unfold w64; f_equal; lia
      | rewrite Ra1; reflexivity
      | rewrite Ra2; reflexivity
      | lia | lia | lia
      | exact Qsp | reflexivity | lia | rewrite WS, Hes; lia
      | rewrite Rgp, A3; exact Hgp
      | rewrite Rtp, A4; exact Htp
      | exact Rra
      | apply ret_ok_codeptr_v; [lia | reflexivity]
      | intros a Ha; split;
        [ right; left; split;
          [ exists (r, r + REG_SIZEB); split; [left; reflexivity | cbn [fst snd]; unfold REG_SIZEB; lia]
          | exists r, REG_SIZEB; split; [exact Hin | change (req_size REG_SIZEB) with 288; lia] ]
        | rewrite Hes; lia ]
      | exact (amem_range_of_block SEGS B LAWS _ _ _ _ _ r REG_SIZEB (r + 56 * c) 56 (proj1 HJ) Hin ltac:(lia)
                 ltac:(change (req_size REG_SIZEB) with 288; lia))
      | exact (range_addressable_of_block SEGS B LAWS _ _ _ _ _ r REG_SIZEB (r + 56 * c) 56 (proj1 HJ) Hin ltac:(lia)
                 ltac:(change (req_size REG_SIZEB) with 288; lia))
      | intros _; exact (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ r REG_SIZEB (r + 56 * c) 56 (proj1 HJ) Hin
                 ltac:(lia) ltac:(change (req_size REG_SIZEB) with 288; lia) ltac:(lia))
      | exact I ]
    | ]
  end;
  cbv beta; intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Hzz & Hfr1 & Hpres2);
  assert (HROW : forall i, 0 <= i < 56 -> aview SEGS (w_H W) mem2 (r + 56 * c + i) = Some 0)
    by (intros i Hi; rewrite (Hzz i Hi); reflexivity);
  assert (HOUT : forall i, 0 <= i < 288 -> (i < 56 * c \/ 56 * c + 56 <= i) ->
                 aview SEGS (w_H W) mem2 (r + i) = Some (bxb bs i))
    by (intros i Hi Hout; rewrite (Hfr1 (r + i) ltac:(lia) ltac:(lia) ltac:(lia));
        exact (HK i ltac:(unfold REG_SIZEB; lia)));
  jafter_call_keep_hi HS 660%nat regs2 (mrestrict (w_H W) mem2) HP2 [0%nat] HS2;
  match type of HS2 with ?Q -> _ =>
    assert (HQ : Q);
    [ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_nil];
      eapply (region_kept_aview _ (w_H W) _ mem2 2%nat (spZ regs)); [exact AU2 | | exact Hpres2];
      intros a Ha; apply Hfr1; lia
    | specialize (HS2 HQ); clear HQ ] end;
  clear HS HK Hzz Hfr1; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS;
  lazymatch type of HS with st_ok_pi _ _ ?Ec2 _ _ =>
    assert (HE2 : EOK regs r bs Ec2) by (apply EOK_havoc; [exact HE | cbv; lia]);
    assert (HEI2 : img_env VAL A_LIM Ec2) by (apply img_env_havoc_hi; [exact (proj1 HE) | cbv; lia]);
    assert (Ab2 : ew Ec2 644 = w64 b) by (rewrite ew_havoc_old by lia; exact Ab);
    assert (SHOK2 : sh_ok SEGS ABx SH_add Ec2 (mrestrict (w_H W) mem2))
      by (exact (sh_ok_of_block ly S W mem2 md2 regs r bs Ec2 (proj1 HJ2) Hin HE2 H10));
    destruct (nr_env regs r p k bs Ec2 HE2 H10 H11 H12 ltac:(lia)) as (B10 & BU10 & BU2 & B3 & B4 & B11 & B12 & B33)
  end;
  clear SHOK;
  (* the run to the call of __asan_memcpy (r + 56 c, p, 6) at 0x82194 *)
  paj_run_tok RUN HS HJ2 SHOK2 ABspan; [awr_ok_tac; exact BU2 |];
  lazymatch type of HFr with frame_of _ _ (mrestrict _ ?mA) (mrestrict _ ?mB) =>
    assert (HROW2 : forall i, 0 <= i < 56 -> aview SEGS (w_H W) mB (r + 56 * c + i) = Some 0)
      by (intros i Hi;
          rewrite (bd_keep _ _ (w_H W) mA mB (spZ regs) HFr ltac:(vm_compute; reflexivity) BU2
                     (r + 56 * c + i) ltac:(lia) ltac:(lia)); exact (HROW i Hi));
    assert (HOUT2 : forall i, 0 <= i < 288 -> (i < 56 * c \/ 56 * c + 56 <= i) ->
                    aview SEGS (w_H W) mB (r + i) = Some (bxb bs i))
      by (intros i Hi Hout;
          rewrite (bd_keep _ _ (w_H W) mA mB (spZ regs) HFr ltac:(vm_compute; reflexivity) BU2
                     (r + i) ltac:(lia) ltac:(lia)); exact (HOUT i Hi Hout)) end;
  clear HROW HOUT HF HFr HG;
  lazymatch type of HS with st_ok _ ?Eb _ _ =>
    assert (HE2b : EOK regs r bs Eb)
      by (apply (EOK_mono regs r bs _ Eb HE2);
          [ assumption | intros nn Hnn; cbn [extK]; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity ]);
    assert (Ab2b : ew Eb 644 = w64 b) by (cbn [extK]; rewrite ?ew_ewset_other by lia; exact Ab2);
    destruct (nr_env regs r p k bs Eb HE2b H10 H11 H12 ltac:(lia))
      as (B10' & BU10' & BU2' & B3' & B4' & B11' & B12' & B33') end;
  pose proof (add_afobj_now ly S W regs mem md ch r p k bs M _ _ HP HJ2) as HFO1;
  pose proof (add_mac_now ly S W regs mem md ch r p k bs M _ _ HP HJ2) as HMB1;
  pmkst HS;
  prreg HS (10%bv : bv 5) Ra0'; prreg HS (11%bv : bv 5) Ra1'; prreg HS (12%bv : bv 5) Ra2';
  prreg HS (1%bv : bv 5) Rra'; prreg HS (2%bv : bv 5) Rsp'; prreg HS (3%bv : bv 5) Rgp'; prreg HS (4%bv : bv 5) Rtp';
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
    assert (Qsp2 : spZ rg = spZ regs + -80)
      by (unfold spZ at 1; rewrite Rsp'; first [rewrite BU2' | rewrite AU2];
          rewrite unsigned_lit_small by lia; reflexivity);
    eapply SRr_bind;
    [ eapply (aj_intrin_at SEGS B LAWS Hsegs OCpy (pa_sigma BB___asan_memcpy) AMEMCPY W rg mm
        REAC_BOXREG_ADD_STKB (spZ regs) [(r, r + REG_SIZEB)] ly S W mem md [] ly S _ 0 (r + 56 * c) p 6 (-80) _ HJ2);
      [ first [rewrite Ra0', BU10' | rewrite Ra0', B10' | rewrite Ra0', AU10 | rewrite Ra0', A10];
        unfold w64; f_equal; lia
      | first [rewrite Ra1', B11' | rewrite Ra1', A11]; reflexivity
      | rewrite Ra2'; reflexivity
      | lia | lia | lia
      | exact Qsp2 | reflexivity | lia | rewrite WS, Hes; lia
      | first [rewrite Rgp', B3' | rewrite Rgp', A3]; exact Hgp
      | first [rewrite Rtp', B4' | rewrite Rtp', A4]; exact Htp
      | exact Rra'
      | apply ret_ok_codeptr_v; [lia | reflexivity]
      | intros a Ha; split;
        [ right; left; split;
          [ exists (r, r + REG_SIZEB); split; [left; reflexivity | cbn [fst snd]; unfold REG_SIZEB; lia]
          | exists r, REG_SIZEB; split; [exact Hin | change (req_size REG_SIZEB) with 288; lia] ]
        | rewrite Hes; lia ]
      | exact (amem_range_of_block SEGS B LAWS _ _ _ _ _ r REG_SIZEB (r + 56 * c) 6 (proj1 HJ2) Hin ltac:(lia)
                 ltac:(change (req_size REG_SIZEB) with 288; lia))
      | exact (range_addressable_of_block SEGS B LAWS _ _ _ _ _ r REG_SIZEB (r + 56 * c) 6 (proj1 HJ2) Hin ltac:(lia)
                 ltac:(change (req_size REG_SIZEB) with 288; lia))
      | intros _; exact (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ r REG_SIZEB (r + 56 * c) 6 (proj1 HJ2) Hin
                 ltac:(lia) ltac:(change (req_size REG_SIZEB) with 288; lia) ltac:(lia))
      | split; [lia|]; split; [lia|]; split;
        [ intros a Ha; split;
          [ replace a with (p + (a - p)) by lia; rewrite (HMB1 (a - p) ltac:(lia)); discriminate
          | rewrite Qsp2, Hes; lia ]
        | split; [lia|]; split; [exact (amem_range_sub_app _ _ p 6 Happ Hfceil Hflo Hfhi ltac:(lia))|];
          split; [exact (proj2 (proj2 HFO1))|];
          intros _; exact (shadow_hull_vis_of_frame SEGS B LAWS _ _ _ _ _ cid pos p 6 (proj1 HJ2) Hfin Hflo Hfhi
                             ltac:(lia)) ] ]
    | ]
  end;
  cbv beta; intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Ha03 & Heff2 & Hfr2 & Hpres3);
  assert (HMAC : forall i, 0 <= i < 6 -> aview SEGS (w_H W) mem3 (r + 56 * c + i) = Some (bxb M i))
    by (intros i Hi; rewrite (Heff2 i Hi); exact (HMB1 i Hi));
  assert (HROW3 : forall i, 6 <= i < 56 -> aview SEGS (w_H W) mem3 (r + 56 * c + i) = Some 0)
    by (intros i Hi; rewrite (Hfr2 (r + 56 * c + i) ltac:(lia) ltac:(lia) ltac:(lia)); exact (HROW2 i ltac:(lia)));
  assert (HOUT3 : forall i, 0 <= i < 288 -> (i < 56 * c \/ 56 * c + 56 <= i) ->
                  aview SEGS (w_H W) mem3 (r + i) = Some (bxb bs i))
    by (intros i Hi Hout; rewrite (Hfr2 (r + i) ltac:(lia) ltac:(lia) ltac:(lia)); exact (HOUT2 i Hi Hout));
  jafter_call_keep_hi HS 680%nat regs3 (mrestrict (w_H W) mem3) HP3 [0%nat] HS3;
  match type of HS3 with ?Q -> _ =>
    assert (HQ : Q);
    [ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_nil];
      eapply (region_kept_aview _ (w_H W) _ mem3 2%nat (spZ regs)); [exact BU2' | | exact Hpres3];
      intros a Ha; apply Hfr2; lia
    | specialize (HS3 HQ); clear HQ ] end;
  clear HS HROW2 HOUT2 Heff2 Hfr2 HFO1 HMB1; rewrite <- restrict_mkst_fx in HS3; rename HS3 into HS;
  lazymatch type of HS with st_ok_pi _ _ ?Ec3 _ _ =>
    assert (HE3 : EOK regs r bs Ec3) by (apply EOK_havoc; [exact HE2b | cbv; lia]);
    assert (HEI3 : img_env VAL A_LIM Ec3) by (apply img_env_havoc_hi; [exact (proj1 HE2b) | cbv; lia]);
    assert (Ab3 : ew Ec3 644 = w64 b) by (rewrite ew_havoc_old by lia; exact Ab2b);
    assert (SHOK3 : sh_ok SEGS ABx SH_add Ec3 (mrestrict (w_H W) mem3))
      by (exact (sh_ok_of_block ly S W mem3 md3 regs r bs Ec3 (proj1 HJ3) Hin HE3 H10));
    destruct (nr_env regs r p k bs Ec3 HE3 H10 H11 H12 ltac:(lia)) as (Q10 & QU10 & QU2 & Q3 & Q4 & Q11 & Q12 & Q33);
    destruct (R2_ok ly S W mem3 md3 regs r bs Ec3 c HE3 H10 (proj1 HJ3) Hin ltac:(lia)
                ltac:(intros j Hj; exact (HOUT3 (280 + j) ltac:(lia) ltac:(lia)))) as (HRa & HRb)
  end;
  clear SHOK2;
  (* the two registry windows the stores use *)
  lazymatch type of HS with st_ok_pi _ _ ?Ef ?ssf ?msx =>
    assert (HSb : st_ok_pi SEGS VAL Ef
                    (mkSS (ss_pc ssf) (ss_regs ssf) (R2b :: ss_mem ssf) (ss_resv ssf) (ss_facts ssf)) msx)
      by (apply (st_ok_pi_add_region Ef ssf msx R2b HS); [vm_compute; reflexivity | exact HRb |];
          cbn [ss_mem all_disjoint]; split; [|exact I];
          unfold extent_disjoint, R2b; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          rewrite QU10, QU2; left; lia) end;
  clear HS; rename HSb into HS;
  lazymatch type of HS with st_ok_pi _ _ ?Ef ?ssf ?msx =>
    assert (HSa : st_ok_pi SEGS VAL Ef
                    (mkSS (ss_pc ssf) (ss_regs ssf) (R2a c :: ss_mem ssf) (ss_resv ssf) (ss_facts ssf)) msx)
      by (apply (st_ok_pi_add_region Ef ssf msx (R2a c) HS); [rewrite Hcc; vm_compute; reflexivity | exact HRa |];
          cbn [ss_mem all_disjoint]; split; [|split; [|exact I]];
          unfold extent_disjoint, R2a, R2b; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          rewrite QU10; try rewrite QU2; [left; lia | left; lia]) end;
  clear HS; rename HSa into HS; rewrite Hcc in HS;
  (* the run to the ret at 0x82028: the stores of b, k and n + 1 *)
  paj_run_tok RUN HS HJ3 SHOK3 ABspan;
  [ apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat r); [reflexivity | exact QU10
    | intros a Ha; cbn [R2a R2b YP09.r_wlo YP09.r_whi] in Ha; right; left; split;
      [ exists (r, r + REG_SIZEB); split; [left; reflexivity | cbn [fst snd]; unfold REG_SIZEB; lia]
      | exists r, REG_SIZEB; split; [exact Hin | change (req_size REG_SIZEB) with 288; lia] ] |];
    apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat r); [reflexivity | exact QU10
    | intros a Ha; cbn [R2a R2b YP09.r_wlo YP09.r_whi] in Ha; right; left; split;
      [ exists (r, r + REG_SIZEB); split; [left; reflexivity | cbn [fst snd]; unfold REG_SIZEB; lia]
      | exists r, REG_SIZEB; split; [exact Hin | change (req_size REG_SIZEB) with 288; lia] ] |];
    awr_ok_tac; exact QU2
  | ];
  lazymatch type of HS with st_ok_pi _ _ ?Ef ?ssf (restrict _ ?msf) =>
    assert (HE4 : EOK regs r bs Ef)
      by (apply (EOK_mono regs r bs _ Ef HE3);
          [ assumption | intros nn Hnn; cbn [extK]; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity ]);
    assert (D644 : ew Ef 644 = w64 b) by (cbn [extK]; rewrite ?ew_ewset_other by lia; exact Ab3);
    destruct (nr_env regs r p k bs Ef HE4 H10 H11 H12 ltac:(lia)) as (D10 & DU10 & DU2 & D3 & D4 & D11 & D12 & D33);
    assert (HFB : forall j, 0 <= j < 4 ->
             aview SEGS (w_H W) (ms_mem msf) (r + (56 * c + 8) + j) = Some (YG0f.le_byte b 4 (Z.to_nat j)))
      by (intros j Hj; apply (aview_of_val4 (w_H W) (ms_mem msf) (r + (56 * c + 8)) b); [| lia | lia];
          eapply (field_of_region Ef (mrestrict (w_H W) (ms_mem msf)) 10%nat r _ _ _ _ _ (56 * c + 8) 4%N
                   (SOff 644 0) b);
          [ exact (nr_region_nth Ef ssf _ 0%nat _ HS eq_refl)
          | exact DU10
          | rewrite Hcc; cbn [In]; right; left; reflexivity
          | cbn [sv_denot]; rewrite D644; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia
          | lia | lia ]);
    assert (HFK : forall j, 0 <= j < 4 ->
             aview SEGS (w_H W) (ms_mem msf) (r + (56 * c + 12) + j) = Some (YG0f.le_byte k 4 (Z.to_nat j)))
      by (intros j Hj; apply (aview_of_val4 (w_H W) (ms_mem msf) (r + (56 * c + 12)) k); [| lia | lia];
          eapply (field_of_region Ef (mrestrict (w_H W) (ms_mem msf)) 10%nat r _ _ _ _ _ (56 * c + 12) 4%N
                   (SOff 12 0) k);
          [ exact (nr_region_nth Ef ssf _ 0%nat _ HS eq_refl)
          | exact DU10
          | rewrite Hcc; cbn [In]; left; reflexivity
          | cbn [sv_denot]; rewrite D12; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia
          | lia | lia ]);
    assert (HFN : forall j, 0 <= j < 4 ->
             aview SEGS (w_H W) (ms_mem msf) (r + 280 + j) = Some (YG0f.le_byte (c + 1) 4 (Z.to_nat j)))
      by (intros j Hj; apply (aview_of_val4 (w_H W) (ms_mem msf) (r + 280) (c + 1)); [| lia | lia];
          eapply (field_of_region Ef (mrestrict (w_H W) (ms_mem msf)) 10%nat r _ _ _ _ _ 280 4%N
                   (SOff 33 1) (c + 1));
          [ exact (nr_region_nth Ef ssf _ 1%nat _ HS eq_refl)
          | exact DU10
          | cbn [In]; left; reflexivity
          | cbn [sv_denot]; rewrite D33; unfold w64; rewrite unsigned_lit_small
              by (pose proof (bxu4_range bs 280); lia); f_equal; lia
          | lia | lia ]);
    assert (KFIN : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 80 <= a < spZ regs) ->
             (forall w, In w [(56 * c + 8, 56 * c + 16); (280, 284)] -> ~ (r + fst w <= a < r + snd w)) ->
             aview SEGS (w_H W) (ms_mem msf) a = aview SEGS (w_H W) mem3 a)
      by (exact (nr_keep _ _ (w_H W) mem3 (ms_mem msf) (spZ regs) r [(56 * c + 8, 56 * c + 16); (280, 284)] HFr
                   ltac:(rewrite Hcc; vm_compute; reflexivity) QU2 QU10));
    apply (add_ret ly S W regs mem md ch r p k bs M Ef msf _ ssf (Boxreg.bx_n bs)
             (reac_boxreg_add_c.add_bytes bs M b k) HP HE4 HJ3 HS eq_refl
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
  end;
  [ lazymatch goal with |- sv_denot _ ?e = _ => let v := eval vm_compute in e in change e with v end;
    cbn [sv_denot]; rewrite D33; unfold w64; rewrite unsigned_lit_small by (pose proof (bxu4_range bs 280); lia);
    f_equal; lia
  | right; right; right; right;
    split; [exact WOK|]; split; [exact HMnz|]; split; [exact NH|]; split; [exact NU|];
    split; [lia|]; split; [reflexivity|]; exists b; split; [exact Hb0|]; split; [exact HLF | reflexivity]
  | intros i Hi; unfold REG_SIZEB in Hi;
    rewrite bxb_add_bytes by (first [exact HL | exact HML | lia]); rewrite Hn;
    destruct ((56 * c <=? i) && (i <? 56 * c + 56)) eqn:Hrow;
    [ apply andb_prop in Hrow as [Q1 Q2]; apply Z.leb_le in Q1; apply Z.ltb_lt in Q2;
      destruct (i - 56 * c <? 6) eqn:Hi6;
      [ apply Z.ltb_lt in Hi6;
        rewrite (KFIN (r + i) ltac:(lia) ltac:(lia)
                   ltac:(intros w Hw; cbn [In] in Hw; destruct Hw as [<-|[<-|[]]]; cbn [fst snd]; lia));
        replace (r + i) with (r + 56 * c + (i - 56 * c)) by lia; exact (HMAC (i - 56 * c) ltac:(lia))
      | apply Z.ltb_ge in Hi6; destruct (i - 56 * c <? 8) eqn:Hi8;
        [ apply Z.ltb_lt in Hi8;
          rewrite (KFIN (r + i) ltac:(lia) ltac:(lia)
                     ltac:(intros w Hw; cbn [In] in Hw; destruct Hw as [<-|[<-|[]]]; cbn [fst snd]; lia));
          replace (r + i) with (r + 56 * c + (i - 56 * c)) by lia; exact (HROW3 (i - 56 * c) ltac:(lia))
        | apply Z.ltb_ge in Hi8; destruct (i - 56 * c <? 12) eqn:Hi12;
          [ apply Z.ltb_lt in Hi12;
            replace (r + i) with (r + (56 * c + 8) + (i - 56 * c - 8)) by lia;
            rewrite (HFB (i - 56 * c - 8) ltac:(lia));
            rewrite bxb_le4 by lia; f_equal; f_equal; lia
          | apply Z.ltb_ge in Hi12; destruct (i - 56 * c <? 16) eqn:Hi16;
            [ apply Z.ltb_lt in Hi16;
              replace (r + i) with (r + (56 * c + 12) + (i - 56 * c - 12)) by lia;
              rewrite (HFK (i - 56 * c - 12) ltac:(lia));
              rewrite bxb_le4 by lia; f_equal; f_equal; lia
            | apply Z.ltb_ge in Hi16;
              rewrite (KFIN (r + i) ltac:(lia) ltac:(lia)
                         ltac:(intros w Hw; cbn [In] in Hw; destruct Hw as [<-|[<-|[]]]; cbn [fst snd]; lia));
              replace (r + i) with (r + 56 * c + (i - 56 * c)) by lia; exact (HROW3 (i - 56 * c) ltac:(lia)) ] ] ] ]
    | assert (Hnr : i < 56 * c \/ 56 * c + 56 <= i)
        by (apply andb_false_iff in Hrow; destruct Hrow as [Q|Q];
            [apply Z.leb_gt in Q | apply Z.ltb_ge in Q]; lia);
      destruct ((280 <=? i) && (i <? 284)) eqn:Hn280;
      [ apply andb_prop in Hn280 as [Q1 Q2]; apply Z.leb_le in Q1; apply Z.ltb_lt in Q2;
        replace (r + i) with (r + 280 + (i - 280)) by lia;
        rewrite (HFN (i - 280) ltac:(lia)); rewrite bxb_le4 by lia; f_equal; f_equal; lia
      | assert (Hn284 : i < 280 \/ 284 <= i)
          by (apply andb_false_iff in Hn280; destruct Hn280 as [Q|Q];
              [apply Z.leb_gt in Q | apply Z.ltb_ge in Q]; lia);
        rewrite (KFIN (r + i) ltac:(lia) ltac:(lia)
                   ltac:(intros w Hw; cbn [In] in Hw; destruct Hw as [<-|[<-|[]]]; cbn [fst snd]; lia));
        exact (HOUT3 i ltac:(lia) ltac:(lia)) ] ] ]).
Qed.
Ltac lfs := let v := eval vm_compute in BoxBLowestFreeBase.LOWEST_FREE_BASE_STKB in
  change BoxBLowestFreeBase.LOWEST_FREE_BASE_STKB with v; unfold ESTACK; lia.
Lemma add_new_seg : forall ly S W regs mem md ch r p k bs M E ms mdc,
  add_pre ly S W regs mem md ch r p k bs M -> add_cur ly S W regs mem md r bs E ms mdc ->
  st_ok_pi SEGS VAL E ss_new (restrict (w_H W) ms) ->
  M <> Boxreg.zero6 -> reac_boxreg_add_c.add_width_ok k (Boxreg.bx_fabric bs) ->
  reac_boxreg_add_c.add_none_held bs M -> reac_boxreg_add_c.add_none_unbound bs k ->
  SRr SEGS W (mkCfg ms mdc) (tbreac_boxreg_add_post regs ly S W mem md r k bs M).
Proof.
  intros ly S W regs mem md ch r p k bs M E ms mdc HP (HE & SHOK & HJ & HK) HS HMnz WOK NH NU.
  change (KEEPR W (ms_mem ms) r bs) in HK.
  pose proof HP as (HPRE & H10 & H11 & H12 & Hk & Hin & HB & HI & HFO & HML & HM).
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). pose proof add_stk as WS.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ REG_SIZEB HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
  change (req_size REG_SIZEB) with 288 in *.
  pose proof HI as ([HL [H1 [H2 [H3 _]]]] & _). unfold Boxreg.boxreg_B1, Boxreg.boxreg_B2 in H1, H2.
  assert (Hn : bxu4 bs 280 = Boxreg.bx_n bs) by (apply bxu4_rd4; unfold Boxreg.bx_n in H1; lia).
  set (RUN := paj_run B LAWS). set (BR := paj_branch (PI := PI)). set (RUNTO := paj_run_to B LAWS).
  pose proof (proj1 HE) as HEI.
  destruct (Z_lt_le_dec 4 (Boxreg.bx_n bs)) as [Hn5 | Hn4].
  { (* n = 5: -1 *)
    arun RUN regs HS HJ SHOK.
    lazymatch goal with HE : EOK _ _ _ ?Ec |- _ =>
      assert (EN : ew Ec 33 = Z_to_bv 64 (Boxreg.bx_n bs)) by (rewrite <- Hn; eok_ew HE 33%nat; reflexivity) end.
    psrr_branch_tok RUN BR HS SHOK ABspan;
      rewrite (dec_lts_lit_atom _ 33 4 (Boxreg.bx_n bs) EN) in Hc by (unfold Boxreg.bx_n in *; lia).
    - ret_with RUN regs HP (-1) bs HS HJ SHOK; [a0_lit|].
      right; right; right; left. split; [exact WOK|]. split; [exact HMnz|]. split; [exact NH|]. split; [exact NU|].
      split; [left; lia | split; reflexivity].
    - apply Z.ltb_ge in Hc. lia. }
  assert (E1 : ew E 1 = getr regs 1) by (rewrite (EOK_reg _ _ _ _ 1 HE) by lia; reflexivity).
  assert (E2 : ew E 2 = getr regs 2) by (rewrite (EOK_reg _ _ _ _ 2 HE) by lia; reflexivity).
  assert (E3 : ew E 3 = getr regs 3) by (rewrite (EOK_reg _ _ _ _ 3 HE) by lia; reflexivity).
  assert (E4 : ew E 4 = getr regs 4) by (rewrite (EOK_reg _ _ _ _ 4 HE) by lia; reflexivity).
  assert (E10 : ew E 10 = w64 r) by (rewrite (EOK_reg _ _ _ _ 10 HE) by lia; exact H10).
  assert (E12 : ew E 12 = w64 k) by (rewrite (EOK_reg _ _ _ _ 12 HE) by lia; exact H12).
  assert (Hspr : alloc_ceiling + 8352 <= spZ regs <= 2 ^ 47) by (rewrite WS in Hslo; lia).
  assert (Hach : forall rg (L : alayout) rd sp, getr rg 8 = w64 k -> L = ly -> achain L rd sp (s0Z rg) []).
  { intros rg L rd sp Hs0 ->. left. split; [|reflexivity]. unfold s0Z. rewrite Hs0. unfold w64.
    rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    destruct (Z_lt_le_dec k 0) as [Hneg|Hpos].
    - right; left. rewrite <- (Z.mod_unique k (2 ^ 64) (-1) (k + 2 ^ 64)) by lia. lia.
    - left. rewrite Z.mod_small by lia. lia. }
  arun RUN regs HS HJ SHOK.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ =>
    assert (EN : ew Ec 33 = Z_to_bv 64 (Boxreg.bx_n bs)) by (rewrite <- Hn; eok_ew HE 33%nat; reflexivity) end.
  psrr_branch_tok RUN BR HS SHOK ABspan;
    rewrite (dec_lts_lit_atom _ 33 4 (Boxreg.bx_n bs) EN) in Hc by (unfold Boxreg.bx_n in *; lia);
    [apply Z.ltb_lt in Hc; lia|].
  clear Hc EN.
  arun RUN regs HS HJ SHOK.
  (* the call of lowest_free_base *)
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msc) => rename msc into msF end.
  pmkst HS. rewrite pa_sigma_lowest_free_base.
  prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp.
  prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (8%bv : bv 5) Rs0.
  assert (Ra0' : getr (ms_regs msF) 10 = w64 r) by (rewrite Ra0; exact E10).
  assert (Ra1' : getr (ms_regs msF) 11 = w64 k) by (rewrite Ra1; exact E12).
  assert (Qsp : spZ (ms_regs msF) = spZ regs + -80).
  { unfold spZ at 1. rewrite Rsp, E2. rewrite unsigned_lit_small; [reflexivity|]. unfold spZ in Hspr. lia. }
  pose proof WOK as [Wev [Wk Wf]].
  eapply SRr_bind.
  { eapply (cl_callS B LAWS W (ms_regs msF) (ms_mem msF) _ REAC_BOXREG_ADD_STKB (spZ regs) [(r, r + REG_SIZEB)]
              ly S W mem md [] ly S _ 0 BoxBLowestFreeBase.LOWEST_FREE_BASE_STKB [] 0 (-80) (getr (ms_regs msF) 1) [] _ HJ).
    - exact Qsp.
    - reflexivity.
    - lia.
    - lfs.
    - rewrite WS. lfs.
    - rewrite Rgp, E3. exact Hgp.
    - rewrite Rtp, E4. exact Htp.
    - reflexivity.
    - rewrite Rra. apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite Rra. pose proof pa_base_lo. pose proof pa_B_ok as (HB0 & HB1 & _). rewrite unsigned_lit_small by lia. lia.
    - apply Hach; [rewrite Rs0; exact E12 | reflexivity].
    - intros HPRE'. exact (LFB ly S W (ms_regs msF) (ms_mem msF) _ [] r k bs HPRE' Ra0' Ra1' ltac:(lia) Hin HL HK H1 H2 H3).
    - intros a Ha. destruct (inFP_nil a Ha). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs3 & mem3 & md3 & -> & HJ2 & HJc & HP2 & (-> & -> & -> & z & Hz & Hlf)).
  after_prog_call regs 640%nat Rra HS HJ SHOK HK HE HJ2 HJc HP2.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ => assert (A644 : ew Ec 644 = w64 z) by (rewrite <- Hz; reflexivity) end.
  clear Ra0 Ra1 Ra0' Ra1' Rsp Rgp Rtp Rs0 Qsp.
  assert (Hzr : -1 <= z <= 40).
  { destruct Hlf as [(-> & _) | (Hz0 & Hzk & _)]; [lia | unfold Boxreg.bx_fabric in *; lia]. }
  arun RUN regs HS HJ SHOK.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ => assert (A644' : ew Ec 644 = w64 z) by (rewrite <- A644; reflexivity) end.
  clear A644; rename A644' into A644.
  psrr_branch_tok RUN BR HS SHOK ABspan;
    rewrite (dec_lts_atom_lit _ 644 z 0 A644) in Hc by lia.
  { (* no free base: -1 *)
    apply Z.ltb_lt in Hc. assert (z = -1) as -> by lia.
    ret_with RUN regs HP (-1) bs HS HJ SHOK; [a0_lit|].
    right; right; right; left. split; [exact WOK|]. split; [exact HMnz|]. split; [exact NH|]. split; [exact NU|].
    split; [right; exact Hlf | split; reflexivity]. }
  apply Z.ltb_ge in Hc. rename Hc into Hz0.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ =>
    assert (EN : ew Ec 33 = Z_to_bv 64 (Boxreg.bx_n bs)) by (rewrite <- Hn; eok_ew HE 33%nat; reflexivity) end.
  assert (Hc5 : Boxreg.bx_n bs = 0 \/ Boxreg.bx_n bs = 1 \/ Boxreg.bx_n bs = 2 \/ Boxreg.bx_n bs = 3 \/ Boxreg.bx_n bs = 4)
    by (unfold Boxreg.bx_n in *; lia).
  destruct Hc5 as [Hcn | [Hcn | [Hcn | [Hcn | Hcn]]]];
  lazymatch type of Hcn with Boxreg.bx_n bs = ?c =>
  lazymatch goal with HS : st_ok_pi _ _ ?Ec ?ss ?msr |- _ =>
    let EN' := fresh "EN" in
    assert (EN' : ew Ec 33 = Z_to_bv 64 c) by (rewrite EN, Hcn; reflexivity);
    let HSa := fresh "HSa" in
    pose proof (st_ok_pi_add_alias Ec ss msr LHS56 (SLit (56 * c)) HS (den56 Ec c EN' ltac:(lia))) as HSa;
    let HSn := fresh "HSn" in
    pose proof (nr_reabs Ec _ msr c HSa ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  ltac:(let l := eval vm_compute in (reabs_obl PJ (ss_regs (ss_nr c))) in
                        change (reabs_obl PJ (ss_regs (ss_nr c))) with l; repeat constructor)) as HSn;
    eapply (add_nr_seg c ltac:(lia) ly S W regs mem md ch r p k bs M _ _ _ z HP);
    [ split; [exact (JE_EOK _ _ _ Ec (ms_regs msr) HE) | split; [exact (JE_sh Ec (ms_regs msr) _ SHOK) | split; [exact HJ | exact HK]]]
    | exact HSn | exact Hcn | rewrite JE_low by lia; exact A644 | exact Hz0 | exact Hlf | exact HMnz | exact WOK | exact NH
    | exact NU ]
  end end.
Unshelve. all: lfs.
Qed.
Lemma add_tail4 : TAILP 4.
Proof.
  unfold TAILP; intros ly S W regs mem md ch r p k bs M E ms mdc HP (HE & SHOK & HJ & HK) HS Hin_ HMnz WOK NH Hinv.
  change (KEEPR W (ms_mem ms) r bs) in HK.
  pose proof HP as (HPRE & H10 & H11 & H12 & Hk & Hin & HB & HI & HFO & HML & HM).
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). pose proof add_stk as WS.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ REG_SIZEB HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
  change (req_size REG_SIZEB) with 288 in *.
  pose proof HI as ([HL [H1 [H2 [H3 _]]]] & _). unfold Boxreg.boxreg_B1, Boxreg.boxreg_B2 in H1, H2.
  assert (Hn : bxu4 bs 280 = Boxreg.bx_n bs) by (apply bxu4_rd4; unfold Boxreg.bx_n in H1; lia).
  set (RUN := paj_run B LAWS). set (BR := paj_branch (PI := PI)). set (RUNTO := paj_run_to B LAWS).
  pose proof (proj1 HE) as HEI.
  arun RUN regs HS HJ SHOK.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ =>
    assert (EN : ew Ec 33 = Z_to_bv 64 (Boxreg.bx_n bs)) by (rewrite <- Hn; eok_ew HE 33%nat; reflexivity) end.
  psrr_branch_tok RUN BR HS SHOK ABspan.
  - change (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLT (SLit 0) (SOff 33 0))) (SOff 33 0)) with A2X in Hc.
    rewrite (dec_loop _ (Boxreg.bx_n bs) 5 EN) in Hc by (unfold Boxreg.bx_n in *; lia).
    apply negb_true_iff, Z.eqb_neq in Hc. unfold Boxreg.bx_n in *. lia.
  - change (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLT (SLit 0) (SOff 33 0))) (SOff 33 0)) with A2X in Hc.
    rewrite (dec_loop _ (Boxreg.bx_n bs) 5 EN) in Hc by (unfold Boxreg.bx_n in *; lia).
    apply negb_false_iff, Z.eqb_eq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8568.
    reabs_to HS HE SHOK ss_new.
    eapply (add_new_seg ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | exact HMnz | exact WOK | exact NH | intros j0 Hj0; apply Hinv; lia ].
Qed.
Lemma add_row4 : ROWP 4.
Proof.
  unfold ROWP; intros ly S W regs mem md ch r p k bs M E ms mdc HP (HE & SHOK & HJ & HK) HS Hin_ HMnz WOK NH Hinv.
  change (KEEPR W (ms_mem ms) r bs) in HK.
  pose proof HP as (HPRE & H10 & H11 & H12 & Hk & Hin & HB & HI & HFO & HML & HM).
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). pose proof add_stk as WS.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ REG_SIZEB HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
  change (req_size REG_SIZEB) with 288 in *.
  pose proof HI as ([HL [H1 [H2 [H3 _]]]] & _). unfold Boxreg.boxreg_B1, Boxreg.boxreg_B2 in H1, H2.
  assert (Hn : bxu4 bs 280 = Boxreg.bx_n bs) by (apply bxu4_rd4; unfold Boxreg.bx_n in H1; lia).
  set (RUN := paj_run B LAWS). set (BR := paj_branch (PI := PI)). set (RUNTO := paj_run_to B LAWS).
  pose proof (proj1 HE) as HEI.
  arun RUN regs HS HJ SHOK.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ => assert (Ea : ew Ec 59 = Z_to_bv 64 (bxb bs 224)) by (eok_ew HE 59%nat; reflexivity) end.
  psrr_branch_tok RUN BR HS SHOK ABspan;
    rewrite (dec_ne_atom_lit _ 59 (bxb bs 224) 0 Ea) in Hc by (pose proof (bxb_range bs 224); lia).
  { apply negb_true_iff, Z.eqb_neq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8528.
    reabs_to HS HE SHOK (ss_tail 4).
    eapply (add_tail4 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | assumption | exact HMnz | exact WOK | exact NH
      | intros j0 Hj0 [Hz Hnc]; destruct (Z.eq_dec j0 4) as [->|Hne];
        [ exact (mac_nz bs 4 0 HL ltac:(lia) ltac:(lia) Hc Hz) | exact (Hinv j0 ltac:(lia) (conj Hz Hnc)) ] ]. }
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb0. clear Ea.
  arun RUN regs HS HJ SHOK.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ => assert (Ea : ew Ec 60 = Z_to_bv 64 (bxb bs 225)) by (eok_ew HE 60%nat; reflexivity) end.
  psrr_branch_tok RUN BR HS SHOK ABspan;
    rewrite (dec_ne_atom_lit _ 60 (bxb bs 225) 0 Ea) in Hc by (pose proof (bxb_range bs 225); lia).
  { apply negb_true_iff, Z.eqb_neq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8528.
    reabs_to HS HE SHOK (ss_tail 4).
    eapply (add_tail4 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | assumption | exact HMnz | exact WOK | exact NH
      | intros j0 Hj0 [Hz Hnc]; destruct (Z.eq_dec j0 4) as [->|Hne];
        [ exact (mac_nz bs 4 1 HL ltac:(lia) ltac:(lia) Hc Hz) | exact (Hinv j0 ltac:(lia) (conj Hz Hnc)) ] ]. }
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb1. clear Ea.
  arun RUN regs HS HJ SHOK.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ => assert (Ea : ew Ec 61 = Z_to_bv 64 (bxb bs 226)) by (eok_ew HE 61%nat; reflexivity) end.
  psrr_branch_tok RUN BR HS SHOK ABspan;
    rewrite (dec_ne_atom_lit _ 61 (bxb bs 226) 0 Ea) in Hc by (pose proof (bxb_range bs 226); lia).
  { apply negb_true_iff, Z.eqb_neq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8528.
    reabs_to HS HE SHOK (ss_tail 4).
    eapply (add_tail4 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | assumption | exact HMnz | exact WOK | exact NH
      | intros j0 Hj0 [Hz Hnc]; destruct (Z.eq_dec j0 4) as [->|Hne];
        [ exact (mac_nz bs 4 2 HL ltac:(lia) ltac:(lia) Hc Hz) | exact (Hinv j0 ltac:(lia) (conj Hz Hnc)) ] ]. }
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb2. clear Ea.
  arun RUN regs HS HJ SHOK.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ => assert (Ea : ew Ec 62 = Z_to_bv 64 (bxb bs 227)) by (eok_ew HE 62%nat; reflexivity) end.
  psrr_branch_tok RUN BR HS SHOK ABspan;
    rewrite (dec_ne_atom_lit _ 62 (bxb bs 227) 0 Ea) in Hc by (pose proof (bxb_range bs 227); lia).
  { apply negb_true_iff, Z.eqb_neq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8528.
    reabs_to HS HE SHOK (ss_tail 4).
    eapply (add_tail4 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | assumption | exact HMnz | exact WOK | exact NH
      | intros j0 Hj0 [Hz Hnc]; destruct (Z.eq_dec j0 4) as [->|Hne];
        [ exact (mac_nz bs 4 3 HL ltac:(lia) ltac:(lia) Hc Hz) | exact (Hinv j0 ltac:(lia) (conj Hz Hnc)) ] ]. }
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb3. clear Ea.
  arun RUN regs HS HJ SHOK.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ => assert (Ea : ew Ec 63 = Z_to_bv 64 (bxb bs 228)) by (eok_ew HE 63%nat; reflexivity) end.
  psrr_branch_tok RUN BR HS SHOK ABspan;
    rewrite (dec_ne_atom_lit _ 63 (bxb bs 228) 0 Ea) in Hc by (pose proof (bxb_range bs 228); lia).
  { apply negb_true_iff, Z.eqb_neq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8528.
    reabs_to HS HE SHOK (ss_tail 4).
    eapply (add_tail4 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | assumption | exact HMnz | exact WOK | exact NH
      | intros j0 Hj0 [Hz Hnc]; destruct (Z.eq_dec j0 4) as [->|Hne];
        [ exact (mac_nz bs 4 4 HL ltac:(lia) ltac:(lia) Hc Hz) | exact (Hinv j0 ltac:(lia) (conj Hz Hnc)) ] ]. }
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb4. clear Ea.
  arun RUN regs HS HJ SHOK.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ => assert (Ea : ew Ec 64 = Z_to_bv 64 (bxb bs 229)) by (eok_ew HE 64%nat; reflexivity) end.
  psrr_branch_tok RUN BR HS SHOK ABspan;
    rewrite (dec_ne_atom_lit _ 64 (bxb bs 229) 0 Ea) in Hc by (pose proof (bxb_range bs 229); lia).
  { apply negb_true_iff, Z.eqb_neq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8528.
    reabs_to HS HE SHOK (ss_tail 4).
    eapply (add_tail4 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | assumption | exact HMnz | exact WOK | exact NH
      | intros j0 Hj0 [Hz Hnc]; destruct (Z.eq_dec j0 4) as [->|Hne];
        [ exact (mac_nz bs 4 5 HL ltac:(lia) ltac:(lia) Hc Hz) | exact (Hinv j0 ltac:(lia) (conj Hz Hnc)) ] ]. }
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb5. clear Ea.
  arun RUN regs HS HJ SHOK.
  assert (Hmz : Boxreg.bx_mac bs 4 = Boxreg.zero6).
  { apply mac_z; [exact HL | lia |]. intros j0 Hj0.
    assert (j0 = 0 \/ j0 = 1 \/ j0 = 2 \/ j0 = 3 \/ j0 = 4 \/ j0 = 5) as Hc6 by lia.
    destruct Hc6 as [-> | [-> | [-> | [-> | [-> | ->]]]]]; zlit_goal; assumption. }
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ =>
    assert (Ea : ew Ec 69 = Z_to_bv 64 (bxu4 bs 236)) by (eok_ew HE 69%nat; reflexivity);
    assert (EK : ew Ec 12 = Z_to_bv 64 k) by (rewrite (EOK_reg _ _ _ _ 12 HE) by lia; exact H12) end.
  psrr_branch_tok RUN BR HS SHOK ABspan;
    rewrite (dec_nch _ 69 (bxu4 bs 236) k Ea (bxu4_range bs 236) EK Hk) in Hc.
  - apply Z.eqb_eq in Hc. (assert (Hnch : Boxreg.bx_nch bs 4 = bv_swrap 32 (bxu4 bs 236)) by exact (nch_swrap bs 4 HL ltac:(lia)));
    rewrite <- Hnch in Hc.
    arun_to RUNTO regs HS HJ SHOK 8768.
    reabs_to HS HE SHOK (ss_bind 4).
    eapply (add_bind_seg ly S W regs mem md ch r p k bs M _ _ _ 4 HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | lia | exact HMnz | exact WOK | exact NH
      | split; [lia | split; [exact Hmz | split; [exact Hc | exact Hinv]]] ].
  - apply Z.eqb_neq in Hc. (assert (Hnch : Boxreg.bx_nch bs 4 = bv_swrap 32 (bxu4 bs 236)) by exact (nch_swrap bs 4 HL ltac:(lia)));
    rewrite <- Hnch in Hc.
    arun_to RUNTO regs HS HJ SHOK 8528.
    reabs_to HS HE SHOK (ss_tail 4).
    eapply (add_tail4 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | assumption | exact HMnz | exact WOK | exact NH
      | intros j0 Hj0 [Hz Hnc]; destruct (Z.eq_dec j0 4) as [->|Hne]; [exact (Hc Hnc) | exact (Hinv j0 ltac:(lia) (conj Hz Hnc))] ].
Qed.
Lemma add_tail3 : TAILP 3.
Proof.
  unfold TAILP; intros ly S W regs mem md ch r p k bs M E ms mdc HP (HE & SHOK & HJ & HK) HS Hin_ HMnz WOK NH Hinv.
  change (KEEPR W (ms_mem ms) r bs) in HK.
  pose proof HP as (HPRE & H10 & H11 & H12 & Hk & Hin & HB & HI & HFO & HML & HM).
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). pose proof add_stk as WS.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ REG_SIZEB HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
  change (req_size REG_SIZEB) with 288 in *.
  pose proof HI as ([HL [H1 [H2 [H3 _]]]] & _). unfold Boxreg.boxreg_B1, Boxreg.boxreg_B2 in H1, H2.
  assert (Hn : bxu4 bs 280 = Boxreg.bx_n bs) by (apply bxu4_rd4; unfold Boxreg.bx_n in H1; lia).
  set (RUN := paj_run B LAWS). set (BR := paj_branch (PI := PI)). set (RUNTO := paj_run_to B LAWS).
  pose proof (proj1 HE) as HEI.
  arun RUN regs HS HJ SHOK.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ =>
    assert (EN : ew Ec 33 = Z_to_bv 64 (Boxreg.bx_n bs)) by (rewrite <- Hn; eok_ew HE 33%nat; reflexivity) end.
  psrr_branch_tok RUN BR HS SHOK ABspan.
  - change (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLT (SLit 0) (SOff 33 0))) (SOff 33 0)) with A2X in Hc.
    rewrite (dec_loop _ (Boxreg.bx_n bs) 4 EN) in Hc by (unfold Boxreg.bx_n in *; lia).
    apply negb_true_iff, Z.eqb_neq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8400.
    reabs_to HS HE SHOK (ss_row 4).
    eapply (add_row4 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | unfold Boxreg.bx_n in *; lia | exact HMnz | exact WOK | exact NH | intros j0 Hj0; apply Hinv; lia ].
  - change (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLT (SLit 0) (SOff 33 0))) (SOff 33 0)) with A2X in Hc.
    rewrite (dec_loop _ (Boxreg.bx_n bs) 4 EN) in Hc by (unfold Boxreg.bx_n in *; lia).
    apply negb_false_iff, Z.eqb_eq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8568.
    reabs_to HS HE SHOK ss_new.
    eapply (add_new_seg ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | exact HMnz | exact WOK | exact NH | intros j0 Hj0; apply Hinv; lia ].
Qed.
Lemma add_row3 : ROWP 3.
Proof.
  unfold ROWP; intros ly S W regs mem md ch r p k bs M E ms mdc HP (HE & SHOK & HJ & HK) HS Hin_ HMnz WOK NH Hinv.
  change (KEEPR W (ms_mem ms) r bs) in HK.
  pose proof HP as (HPRE & H10 & H11 & H12 & Hk & Hin & HB & HI & HFO & HML & HM).
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). pose proof add_stk as WS.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ REG_SIZEB HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
  change (req_size REG_SIZEB) with 288 in *.
  pose proof HI as ([HL [H1 [H2 [H3 _]]]] & _). unfold Boxreg.boxreg_B1, Boxreg.boxreg_B2 in H1, H2.
  assert (Hn : bxu4 bs 280 = Boxreg.bx_n bs) by (apply bxu4_rd4; unfold Boxreg.bx_n in H1; lia).
  set (RUN := paj_run B LAWS). set (BR := paj_branch (PI := PI)). set (RUNTO := paj_run_to B LAWS).
  pose proof (proj1 HE) as HEI.
  arun RUN regs HS HJ SHOK.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ => assert (Ea : ew Ec 53 = Z_to_bv 64 (bxb bs 168)) by (eok_ew HE 53%nat; reflexivity) end.
  psrr_branch_tok RUN BR HS SHOK ABspan;
    rewrite (dec_ne_atom_lit _ 53 (bxb bs 168) 0 Ea) in Hc by (pose proof (bxb_range bs 168); lia).
  { apply negb_true_iff, Z.eqb_neq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8528.
    reabs_to HS HE SHOK (ss_tail 3).
    eapply (add_tail3 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | assumption | exact HMnz | exact WOK | exact NH
      | intros j0 Hj0 [Hz Hnc]; destruct (Z.eq_dec j0 3) as [->|Hne];
        [ exact (mac_nz bs 3 0 HL ltac:(lia) ltac:(lia) Hc Hz) | exact (Hinv j0 ltac:(lia) (conj Hz Hnc)) ] ]. }
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb0. clear Ea.
  arun RUN regs HS HJ SHOK.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ => assert (Ea : ew Ec 54 = Z_to_bv 64 (bxb bs 169)) by (eok_ew HE 54%nat; reflexivity) end.
  psrr_branch_tok RUN BR HS SHOK ABspan;
    rewrite (dec_ne_atom_lit _ 54 (bxb bs 169) 0 Ea) in Hc by (pose proof (bxb_range bs 169); lia).
  { apply negb_true_iff, Z.eqb_neq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8528.
    reabs_to HS HE SHOK (ss_tail 3).
    eapply (add_tail3 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | assumption | exact HMnz | exact WOK | exact NH
      | intros j0 Hj0 [Hz Hnc]; destruct (Z.eq_dec j0 3) as [->|Hne];
        [ exact (mac_nz bs 3 1 HL ltac:(lia) ltac:(lia) Hc Hz) | exact (Hinv j0 ltac:(lia) (conj Hz Hnc)) ] ]. }
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb1. clear Ea.
  arun RUN regs HS HJ SHOK.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ => assert (Ea : ew Ec 55 = Z_to_bv 64 (bxb bs 170)) by (eok_ew HE 55%nat; reflexivity) end.
  psrr_branch_tok RUN BR HS SHOK ABspan;
    rewrite (dec_ne_atom_lit _ 55 (bxb bs 170) 0 Ea) in Hc by (pose proof (bxb_range bs 170); lia).
  { apply negb_true_iff, Z.eqb_neq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8528.
    reabs_to HS HE SHOK (ss_tail 3).
    eapply (add_tail3 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | assumption | exact HMnz | exact WOK | exact NH
      | intros j0 Hj0 [Hz Hnc]; destruct (Z.eq_dec j0 3) as [->|Hne];
        [ exact (mac_nz bs 3 2 HL ltac:(lia) ltac:(lia) Hc Hz) | exact (Hinv j0 ltac:(lia) (conj Hz Hnc)) ] ]. }
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb2. clear Ea.
  arun RUN regs HS HJ SHOK.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ => assert (Ea : ew Ec 56 = Z_to_bv 64 (bxb bs 171)) by (eok_ew HE 56%nat; reflexivity) end.
  psrr_branch_tok RUN BR HS SHOK ABspan;
    rewrite (dec_ne_atom_lit _ 56 (bxb bs 171) 0 Ea) in Hc by (pose proof (bxb_range bs 171); lia).
  { apply negb_true_iff, Z.eqb_neq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8528.
    reabs_to HS HE SHOK (ss_tail 3).
    eapply (add_tail3 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | assumption | exact HMnz | exact WOK | exact NH
      | intros j0 Hj0 [Hz Hnc]; destruct (Z.eq_dec j0 3) as [->|Hne];
        [ exact (mac_nz bs 3 3 HL ltac:(lia) ltac:(lia) Hc Hz) | exact (Hinv j0 ltac:(lia) (conj Hz Hnc)) ] ]. }
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb3. clear Ea.
  arun RUN regs HS HJ SHOK.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ => assert (Ea : ew Ec 57 = Z_to_bv 64 (bxb bs 172)) by (eok_ew HE 57%nat; reflexivity) end.
  psrr_branch_tok RUN BR HS SHOK ABspan;
    rewrite (dec_ne_atom_lit _ 57 (bxb bs 172) 0 Ea) in Hc by (pose proof (bxb_range bs 172); lia).
  { apply negb_true_iff, Z.eqb_neq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8528.
    reabs_to HS HE SHOK (ss_tail 3).
    eapply (add_tail3 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | assumption | exact HMnz | exact WOK | exact NH
      | intros j0 Hj0 [Hz Hnc]; destruct (Z.eq_dec j0 3) as [->|Hne];
        [ exact (mac_nz bs 3 4 HL ltac:(lia) ltac:(lia) Hc Hz) | exact (Hinv j0 ltac:(lia) (conj Hz Hnc)) ] ]. }
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb4. clear Ea.
  arun RUN regs HS HJ SHOK.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ => assert (Ea : ew Ec 58 = Z_to_bv 64 (bxb bs 173)) by (eok_ew HE 58%nat; reflexivity) end.
  psrr_branch_tok RUN BR HS SHOK ABspan;
    rewrite (dec_ne_atom_lit _ 58 (bxb bs 173) 0 Ea) in Hc by (pose proof (bxb_range bs 173); lia).
  { apply negb_true_iff, Z.eqb_neq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8528.
    reabs_to HS HE SHOK (ss_tail 3).
    eapply (add_tail3 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | assumption | exact HMnz | exact WOK | exact NH
      | intros j0 Hj0 [Hz Hnc]; destruct (Z.eq_dec j0 3) as [->|Hne];
        [ exact (mac_nz bs 3 5 HL ltac:(lia) ltac:(lia) Hc Hz) | exact (Hinv j0 ltac:(lia) (conj Hz Hnc)) ] ]. }
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb5. clear Ea.
  arun RUN regs HS HJ SHOK.
  assert (Hmz : Boxreg.bx_mac bs 3 = Boxreg.zero6).
  { apply mac_z; [exact HL | lia |]. intros j0 Hj0.
    assert (j0 = 0 \/ j0 = 1 \/ j0 = 2 \/ j0 = 3 \/ j0 = 4 \/ j0 = 5) as Hc6 by lia.
    destruct Hc6 as [-> | [-> | [-> | [-> | [-> | ->]]]]]; zlit_goal; assumption. }
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ =>
    assert (Ea : ew Ec 68 = Z_to_bv 64 (bxu4 bs 180)) by (eok_ew HE 68%nat; reflexivity);
    assert (EK : ew Ec 12 = Z_to_bv 64 k) by (rewrite (EOK_reg _ _ _ _ 12 HE) by lia; exact H12) end.
  psrr_branch_tok RUN BR HS SHOK ABspan;
    rewrite (dec_nch _ 68 (bxu4 bs 180) k Ea (bxu4_range bs 180) EK Hk) in Hc.
  - apply Z.eqb_eq in Hc. (assert (Hnch : Boxreg.bx_nch bs 3 = bv_swrap 32 (bxu4 bs 180)) by exact (nch_swrap bs 3 HL ltac:(lia)));
    rewrite <- Hnch in Hc.
    arun_to RUNTO regs HS HJ SHOK 8768.
    reabs_to HS HE SHOK (ss_bind 3).
    eapply (add_bind_seg ly S W regs mem md ch r p k bs M _ _ _ 3 HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | lia | exact HMnz | exact WOK | exact NH
      | split; [lia | split; [exact Hmz | split; [exact Hc | exact Hinv]]] ].
  - apply Z.eqb_neq in Hc. (assert (Hnch : Boxreg.bx_nch bs 3 = bv_swrap 32 (bxu4 bs 180)) by exact (nch_swrap bs 3 HL ltac:(lia)));
    rewrite <- Hnch in Hc.
    arun_to RUNTO regs HS HJ SHOK 8528.
    reabs_to HS HE SHOK (ss_tail 3).
    eapply (add_tail3 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | assumption | exact HMnz | exact WOK | exact NH
      | intros j0 Hj0 [Hz Hnc]; destruct (Z.eq_dec j0 3) as [->|Hne]; [exact (Hc Hnc) | exact (Hinv j0 ltac:(lia) (conj Hz Hnc))] ].
Qed.
Lemma add_tail2 : TAILP 2.
Proof.
  unfold TAILP; intros ly S W regs mem md ch r p k bs M E ms mdc HP (HE & SHOK & HJ & HK) HS Hin_ HMnz WOK NH Hinv.
  change (KEEPR W (ms_mem ms) r bs) in HK.
  pose proof HP as (HPRE & H10 & H11 & H12 & Hk & Hin & HB & HI & HFO & HML & HM).
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). pose proof add_stk as WS.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ REG_SIZEB HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
  change (req_size REG_SIZEB) with 288 in *.
  pose proof HI as ([HL [H1 [H2 [H3 _]]]] & _). unfold Boxreg.boxreg_B1, Boxreg.boxreg_B2 in H1, H2.
  assert (Hn : bxu4 bs 280 = Boxreg.bx_n bs) by (apply bxu4_rd4; unfold Boxreg.bx_n in H1; lia).
  set (RUN := paj_run B LAWS). set (BR := paj_branch (PI := PI)). set (RUNTO := paj_run_to B LAWS).
  pose proof (proj1 HE) as HEI.
  arun RUN regs HS HJ SHOK.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ =>
    assert (EN : ew Ec 33 = Z_to_bv 64 (Boxreg.bx_n bs)) by (rewrite <- Hn; eok_ew HE 33%nat; reflexivity) end.
  psrr_branch_tok RUN BR HS SHOK ABspan.
  - change (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLT (SLit 0) (SOff 33 0))) (SOff 33 0)) with A2X in Hc.
    rewrite (dec_loop _ (Boxreg.bx_n bs) 3 EN) in Hc by (unfold Boxreg.bx_n in *; lia).
    apply negb_true_iff, Z.eqb_neq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8400.
    reabs_to HS HE SHOK (ss_row 3).
    eapply (add_row3 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | unfold Boxreg.bx_n in *; lia | exact HMnz | exact WOK | exact NH | intros j0 Hj0; apply Hinv; lia ].
  - change (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLT (SLit 0) (SOff 33 0))) (SOff 33 0)) with A2X in Hc.
    rewrite (dec_loop _ (Boxreg.bx_n bs) 3 EN) in Hc by (unfold Boxreg.bx_n in *; lia).
    apply negb_false_iff, Z.eqb_eq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8568.
    reabs_to HS HE SHOK ss_new.
    eapply (add_new_seg ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | exact HMnz | exact WOK | exact NH | intros j0 Hj0; apply Hinv; lia ].
Qed.
Lemma add_row2 : ROWP 2.
Proof.
  unfold ROWP; intros ly S W regs mem md ch r p k bs M E ms mdc HP (HE & SHOK & HJ & HK) HS Hin_ HMnz WOK NH Hinv.
  change (KEEPR W (ms_mem ms) r bs) in HK.
  pose proof HP as (HPRE & H10 & H11 & H12 & Hk & Hin & HB & HI & HFO & HML & HM).
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). pose proof add_stk as WS.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ REG_SIZEB HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
  change (req_size REG_SIZEB) with 288 in *.
  pose proof HI as ([HL [H1 [H2 [H3 _]]]] & _). unfold Boxreg.boxreg_B1, Boxreg.boxreg_B2 in H1, H2.
  assert (Hn : bxu4 bs 280 = Boxreg.bx_n bs) by (apply bxu4_rd4; unfold Boxreg.bx_n in H1; lia).
  set (RUN := paj_run B LAWS). set (BR := paj_branch (PI := PI)). set (RUNTO := paj_run_to B LAWS).
  pose proof (proj1 HE) as HEI.
  arun RUN regs HS HJ SHOK.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ => assert (Ea : ew Ec 47 = Z_to_bv 64 (bxb bs 112)) by (eok_ew HE 47%nat; reflexivity) end.
  psrr_branch_tok RUN BR HS SHOK ABspan;
    rewrite (dec_ne_atom_lit _ 47 (bxb bs 112) 0 Ea) in Hc by (pose proof (bxb_range bs 112); lia).
  { apply negb_true_iff, Z.eqb_neq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8528.
    reabs_to HS HE SHOK (ss_tail 2).
    eapply (add_tail2 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | assumption | exact HMnz | exact WOK | exact NH
      | intros j0 Hj0 [Hz Hnc]; destruct (Z.eq_dec j0 2) as [->|Hne];
        [ exact (mac_nz bs 2 0 HL ltac:(lia) ltac:(lia) Hc Hz) | exact (Hinv j0 ltac:(lia) (conj Hz Hnc)) ] ]. }
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb0. clear Ea.
  arun RUN regs HS HJ SHOK.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ => assert (Ea : ew Ec 48 = Z_to_bv 64 (bxb bs 113)) by (eok_ew HE 48%nat; reflexivity) end.
  psrr_branch_tok RUN BR HS SHOK ABspan;
    rewrite (dec_ne_atom_lit _ 48 (bxb bs 113) 0 Ea) in Hc by (pose proof (bxb_range bs 113); lia).
  { apply negb_true_iff, Z.eqb_neq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8528.
    reabs_to HS HE SHOK (ss_tail 2).
    eapply (add_tail2 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | assumption | exact HMnz | exact WOK | exact NH
      | intros j0 Hj0 [Hz Hnc]; destruct (Z.eq_dec j0 2) as [->|Hne];
        [ exact (mac_nz bs 2 1 HL ltac:(lia) ltac:(lia) Hc Hz) | exact (Hinv j0 ltac:(lia) (conj Hz Hnc)) ] ]. }
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb1. clear Ea.
  arun RUN regs HS HJ SHOK.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ => assert (Ea : ew Ec 49 = Z_to_bv 64 (bxb bs 114)) by (eok_ew HE 49%nat; reflexivity) end.
  psrr_branch_tok RUN BR HS SHOK ABspan;
    rewrite (dec_ne_atom_lit _ 49 (bxb bs 114) 0 Ea) in Hc by (pose proof (bxb_range bs 114); lia).
  { apply negb_true_iff, Z.eqb_neq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8528.
    reabs_to HS HE SHOK (ss_tail 2).
    eapply (add_tail2 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | assumption | exact HMnz | exact WOK | exact NH
      | intros j0 Hj0 [Hz Hnc]; destruct (Z.eq_dec j0 2) as [->|Hne];
        [ exact (mac_nz bs 2 2 HL ltac:(lia) ltac:(lia) Hc Hz) | exact (Hinv j0 ltac:(lia) (conj Hz Hnc)) ] ]. }
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb2. clear Ea.
  arun RUN regs HS HJ SHOK.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ => assert (Ea : ew Ec 50 = Z_to_bv 64 (bxb bs 115)) by (eok_ew HE 50%nat; reflexivity) end.
  psrr_branch_tok RUN BR HS SHOK ABspan;
    rewrite (dec_ne_atom_lit _ 50 (bxb bs 115) 0 Ea) in Hc by (pose proof (bxb_range bs 115); lia).
  { apply negb_true_iff, Z.eqb_neq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8528.
    reabs_to HS HE SHOK (ss_tail 2).
    eapply (add_tail2 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | assumption | exact HMnz | exact WOK | exact NH
      | intros j0 Hj0 [Hz Hnc]; destruct (Z.eq_dec j0 2) as [->|Hne];
        [ exact (mac_nz bs 2 3 HL ltac:(lia) ltac:(lia) Hc Hz) | exact (Hinv j0 ltac:(lia) (conj Hz Hnc)) ] ]. }
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb3. clear Ea.
  arun RUN regs HS HJ SHOK.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ => assert (Ea : ew Ec 51 = Z_to_bv 64 (bxb bs 116)) by (eok_ew HE 51%nat; reflexivity) end.
  psrr_branch_tok RUN BR HS SHOK ABspan;
    rewrite (dec_ne_atom_lit _ 51 (bxb bs 116) 0 Ea) in Hc by (pose proof (bxb_range bs 116); lia).
  { apply negb_true_iff, Z.eqb_neq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8528.
    reabs_to HS HE SHOK (ss_tail 2).
    eapply (add_tail2 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | assumption | exact HMnz | exact WOK | exact NH
      | intros j0 Hj0 [Hz Hnc]; destruct (Z.eq_dec j0 2) as [->|Hne];
        [ exact (mac_nz bs 2 4 HL ltac:(lia) ltac:(lia) Hc Hz) | exact (Hinv j0 ltac:(lia) (conj Hz Hnc)) ] ]. }
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb4. clear Ea.
  arun RUN regs HS HJ SHOK.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ => assert (Ea : ew Ec 52 = Z_to_bv 64 (bxb bs 117)) by (eok_ew HE 52%nat; reflexivity) end.
  psrr_branch_tok RUN BR HS SHOK ABspan;
    rewrite (dec_ne_atom_lit _ 52 (bxb bs 117) 0 Ea) in Hc by (pose proof (bxb_range bs 117); lia).
  { apply negb_true_iff, Z.eqb_neq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8528.
    reabs_to HS HE SHOK (ss_tail 2).
    eapply (add_tail2 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | assumption | exact HMnz | exact WOK | exact NH
      | intros j0 Hj0 [Hz Hnc]; destruct (Z.eq_dec j0 2) as [->|Hne];
        [ exact (mac_nz bs 2 5 HL ltac:(lia) ltac:(lia) Hc Hz) | exact (Hinv j0 ltac:(lia) (conj Hz Hnc)) ] ]. }
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb5. clear Ea.
  arun RUN regs HS HJ SHOK.
  assert (Hmz : Boxreg.bx_mac bs 2 = Boxreg.zero6).
  { apply mac_z; [exact HL | lia |]. intros j0 Hj0.
    assert (j0 = 0 \/ j0 = 1 \/ j0 = 2 \/ j0 = 3 \/ j0 = 4 \/ j0 = 5) as Hc6 by lia.
    destruct Hc6 as [-> | [-> | [-> | [-> | [-> | ->]]]]]; zlit_goal; assumption. }
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ =>
    assert (Ea : ew Ec 67 = Z_to_bv 64 (bxu4 bs 124)) by (eok_ew HE 67%nat; reflexivity);
    assert (EK : ew Ec 12 = Z_to_bv 64 k) by (rewrite (EOK_reg _ _ _ _ 12 HE) by lia; exact H12) end.
  psrr_branch_tok RUN BR HS SHOK ABspan;
    rewrite (dec_nch _ 67 (bxu4 bs 124) k Ea (bxu4_range bs 124) EK Hk) in Hc.
  - apply Z.eqb_eq in Hc. (assert (Hnch : Boxreg.bx_nch bs 2 = bv_swrap 32 (bxu4 bs 124)) by exact (nch_swrap bs 2 HL ltac:(lia)));
    rewrite <- Hnch in Hc.
    arun_to RUNTO regs HS HJ SHOK 8768.
    reabs_to HS HE SHOK (ss_bind 2).
    eapply (add_bind_seg ly S W regs mem md ch r p k bs M _ _ _ 2 HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | lia | exact HMnz | exact WOK | exact NH
      | split; [lia | split; [exact Hmz | split; [exact Hc | exact Hinv]]] ].
  - apply Z.eqb_neq in Hc. (assert (Hnch : Boxreg.bx_nch bs 2 = bv_swrap 32 (bxu4 bs 124)) by exact (nch_swrap bs 2 HL ltac:(lia)));
    rewrite <- Hnch in Hc.
    arun_to RUNTO regs HS HJ SHOK 8528.
    reabs_to HS HE SHOK (ss_tail 2).
    eapply (add_tail2 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | assumption | exact HMnz | exact WOK | exact NH
      | intros j0 Hj0 [Hz Hnc]; destruct (Z.eq_dec j0 2) as [->|Hne]; [exact (Hc Hnc) | exact (Hinv j0 ltac:(lia) (conj Hz Hnc))] ].
Qed.
Lemma add_tail1 : TAILP 1.
Proof.
  unfold TAILP; intros ly S W regs mem md ch r p k bs M E ms mdc HP (HE & SHOK & HJ & HK) HS Hin_ HMnz WOK NH Hinv.
  change (KEEPR W (ms_mem ms) r bs) in HK.
  pose proof HP as (HPRE & H10 & H11 & H12 & Hk & Hin & HB & HI & HFO & HML & HM).
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). pose proof add_stk as WS.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ REG_SIZEB HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
  change (req_size REG_SIZEB) with 288 in *.
  pose proof HI as ([HL [H1 [H2 [H3 _]]]] & _). unfold Boxreg.boxreg_B1, Boxreg.boxreg_B2 in H1, H2.
  assert (Hn : bxu4 bs 280 = Boxreg.bx_n bs) by (apply bxu4_rd4; unfold Boxreg.bx_n in H1; lia).
  set (RUN := paj_run B LAWS). set (BR := paj_branch (PI := PI)). set (RUNTO := paj_run_to B LAWS).
  pose proof (proj1 HE) as HEI.
  arun RUN regs HS HJ SHOK.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ =>
    assert (EN : ew Ec 33 = Z_to_bv 64 (Boxreg.bx_n bs)) by (rewrite <- Hn; eok_ew HE 33%nat; reflexivity) end.
  psrr_branch_tok RUN BR HS SHOK ABspan.
  - change (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLT (SLit 0) (SOff 33 0))) (SOff 33 0)) with A2X in Hc.
    rewrite (dec_loop _ (Boxreg.bx_n bs) 2 EN) in Hc by (unfold Boxreg.bx_n in *; lia).
    apply negb_true_iff, Z.eqb_neq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8400.
    reabs_to HS HE SHOK (ss_row 2).
    eapply (add_row2 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | unfold Boxreg.bx_n in *; lia | exact HMnz | exact WOK | exact NH | intros j0 Hj0; apply Hinv; lia ].
  - change (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLT (SLit 0) (SOff 33 0))) (SOff 33 0)) with A2X in Hc.
    rewrite (dec_loop _ (Boxreg.bx_n bs) 2 EN) in Hc by (unfold Boxreg.bx_n in *; lia).
    apply negb_false_iff, Z.eqb_eq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8568.
    reabs_to HS HE SHOK ss_new.
    eapply (add_new_seg ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | exact HMnz | exact WOK | exact NH | intros j0 Hj0; apply Hinv; lia ].
Qed.
Lemma add_row1 : ROWP 1.
Proof.
  unfold ROWP; intros ly S W regs mem md ch r p k bs M E ms mdc HP (HE & SHOK & HJ & HK) HS Hin_ HMnz WOK NH Hinv.
  change (KEEPR W (ms_mem ms) r bs) in HK.
  pose proof HP as (HPRE & H10 & H11 & H12 & Hk & Hin & HB & HI & HFO & HML & HM).
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). pose proof add_stk as WS.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ REG_SIZEB HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
  change (req_size REG_SIZEB) with 288 in *.
  pose proof HI as ([HL [H1 [H2 [H3 _]]]] & _). unfold Boxreg.boxreg_B1, Boxreg.boxreg_B2 in H1, H2.
  assert (Hn : bxu4 bs 280 = Boxreg.bx_n bs) by (apply bxu4_rd4; unfold Boxreg.bx_n in H1; lia).
  set (RUN := paj_run B LAWS). set (BR := paj_branch (PI := PI)). set (RUNTO := paj_run_to B LAWS).
  pose proof (proj1 HE) as HEI.
  arun RUN regs HS HJ SHOK.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ => assert (Ea : ew Ec 41 = Z_to_bv 64 (bxb bs 56)) by (eok_ew HE 41%nat; reflexivity) end.
  psrr_branch_tok RUN BR HS SHOK ABspan;
    rewrite (dec_ne_atom_lit _ 41 (bxb bs 56) 0 Ea) in Hc by (pose proof (bxb_range bs 56); lia).
  { apply negb_true_iff, Z.eqb_neq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8528.
    reabs_to HS HE SHOK (ss_tail 1).
    eapply (add_tail1 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | assumption | exact HMnz | exact WOK | exact NH
      | intros j0 Hj0 [Hz Hnc]; destruct (Z.eq_dec j0 1) as [->|Hne];
        [ exact (mac_nz bs 1 0 HL ltac:(lia) ltac:(lia) Hc Hz) | exact (Hinv j0 ltac:(lia) (conj Hz Hnc)) ] ]. }
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb0. clear Ea.
  arun RUN regs HS HJ SHOK.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ => assert (Ea : ew Ec 42 = Z_to_bv 64 (bxb bs 57)) by (eok_ew HE 42%nat; reflexivity) end.
  psrr_branch_tok RUN BR HS SHOK ABspan;
    rewrite (dec_ne_atom_lit _ 42 (bxb bs 57) 0 Ea) in Hc by (pose proof (bxb_range bs 57); lia).
  { apply negb_true_iff, Z.eqb_neq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8528.
    reabs_to HS HE SHOK (ss_tail 1).
    eapply (add_tail1 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | assumption | exact HMnz | exact WOK | exact NH
      | intros j0 Hj0 [Hz Hnc]; destruct (Z.eq_dec j0 1) as [->|Hne];
        [ exact (mac_nz bs 1 1 HL ltac:(lia) ltac:(lia) Hc Hz) | exact (Hinv j0 ltac:(lia) (conj Hz Hnc)) ] ]. }
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb1. clear Ea.
  arun RUN regs HS HJ SHOK.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ => assert (Ea : ew Ec 43 = Z_to_bv 64 (bxb bs 58)) by (eok_ew HE 43%nat; reflexivity) end.
  psrr_branch_tok RUN BR HS SHOK ABspan;
    rewrite (dec_ne_atom_lit _ 43 (bxb bs 58) 0 Ea) in Hc by (pose proof (bxb_range bs 58); lia).
  { apply negb_true_iff, Z.eqb_neq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8528.
    reabs_to HS HE SHOK (ss_tail 1).
    eapply (add_tail1 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | assumption | exact HMnz | exact WOK | exact NH
      | intros j0 Hj0 [Hz Hnc]; destruct (Z.eq_dec j0 1) as [->|Hne];
        [ exact (mac_nz bs 1 2 HL ltac:(lia) ltac:(lia) Hc Hz) | exact (Hinv j0 ltac:(lia) (conj Hz Hnc)) ] ]. }
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb2. clear Ea.
  arun RUN regs HS HJ SHOK.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ => assert (Ea : ew Ec 44 = Z_to_bv 64 (bxb bs 59)) by (eok_ew HE 44%nat; reflexivity) end.
  psrr_branch_tok RUN BR HS SHOK ABspan;
    rewrite (dec_ne_atom_lit _ 44 (bxb bs 59) 0 Ea) in Hc by (pose proof (bxb_range bs 59); lia).
  { apply negb_true_iff, Z.eqb_neq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8528.
    reabs_to HS HE SHOK (ss_tail 1).
    eapply (add_tail1 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | assumption | exact HMnz | exact WOK | exact NH
      | intros j0 Hj0 [Hz Hnc]; destruct (Z.eq_dec j0 1) as [->|Hne];
        [ exact (mac_nz bs 1 3 HL ltac:(lia) ltac:(lia) Hc Hz) | exact (Hinv j0 ltac:(lia) (conj Hz Hnc)) ] ]. }
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb3. clear Ea.
  arun RUN regs HS HJ SHOK.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ => assert (Ea : ew Ec 45 = Z_to_bv 64 (bxb bs 60)) by (eok_ew HE 45%nat; reflexivity) end.
  psrr_branch_tok RUN BR HS SHOK ABspan;
    rewrite (dec_ne_atom_lit _ 45 (bxb bs 60) 0 Ea) in Hc by (pose proof (bxb_range bs 60); lia).
  { apply negb_true_iff, Z.eqb_neq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8528.
    reabs_to HS HE SHOK (ss_tail 1).
    eapply (add_tail1 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | assumption | exact HMnz | exact WOK | exact NH
      | intros j0 Hj0 [Hz Hnc]; destruct (Z.eq_dec j0 1) as [->|Hne];
        [ exact (mac_nz bs 1 4 HL ltac:(lia) ltac:(lia) Hc Hz) | exact (Hinv j0 ltac:(lia) (conj Hz Hnc)) ] ]. }
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb4. clear Ea.
  arun RUN regs HS HJ SHOK.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ => assert (Ea : ew Ec 46 = Z_to_bv 64 (bxb bs 61)) by (eok_ew HE 46%nat; reflexivity) end.
  psrr_branch_tok RUN BR HS SHOK ABspan;
    rewrite (dec_ne_atom_lit _ 46 (bxb bs 61) 0 Ea) in Hc by (pose proof (bxb_range bs 61); lia).
  { apply negb_true_iff, Z.eqb_neq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8528.
    reabs_to HS HE SHOK (ss_tail 1).
    eapply (add_tail1 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | assumption | exact HMnz | exact WOK | exact NH
      | intros j0 Hj0 [Hz Hnc]; destruct (Z.eq_dec j0 1) as [->|Hne];
        [ exact (mac_nz bs 1 5 HL ltac:(lia) ltac:(lia) Hc Hz) | exact (Hinv j0 ltac:(lia) (conj Hz Hnc)) ] ]. }
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb5. clear Ea.
  arun RUN regs HS HJ SHOK.
  assert (Hmz : Boxreg.bx_mac bs 1 = Boxreg.zero6).
  { apply mac_z; [exact HL | lia |]. intros j0 Hj0.
    assert (j0 = 0 \/ j0 = 1 \/ j0 = 2 \/ j0 = 3 \/ j0 = 4 \/ j0 = 5) as Hc6 by lia.
    destruct Hc6 as [-> | [-> | [-> | [-> | [-> | ->]]]]]; zlit_goal; assumption. }
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ =>
    assert (Ea : ew Ec 66 = Z_to_bv 64 (bxu4 bs 68)) by (eok_ew HE 66%nat; reflexivity);
    assert (EK : ew Ec 12 = Z_to_bv 64 k) by (rewrite (EOK_reg _ _ _ _ 12 HE) by lia; exact H12) end.
  psrr_branch_tok RUN BR HS SHOK ABspan;
    rewrite (dec_nch _ 66 (bxu4 bs 68) k Ea (bxu4_range bs 68) EK Hk) in Hc.
  - apply Z.eqb_eq in Hc. (assert (Hnch : Boxreg.bx_nch bs 1 = bv_swrap 32 (bxu4 bs 68)) by exact (nch_swrap bs 1 HL ltac:(lia)));
    rewrite <- Hnch in Hc.
    arun_to RUNTO regs HS HJ SHOK 8768.
    reabs_to HS HE SHOK (ss_bind 1).
    eapply (add_bind_seg ly S W regs mem md ch r p k bs M _ _ _ 1 HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | lia | exact HMnz | exact WOK | exact NH
      | split; [lia | split; [exact Hmz | split; [exact Hc | exact Hinv]]] ].
  - apply Z.eqb_neq in Hc. (assert (Hnch : Boxreg.bx_nch bs 1 = bv_swrap 32 (bxu4 bs 68)) by exact (nch_swrap bs 1 HL ltac:(lia)));
    rewrite <- Hnch in Hc.
    arun_to RUNTO regs HS HJ SHOK 8528.
    reabs_to HS HE SHOK (ss_tail 1).
    eapply (add_tail1 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | assumption | exact HMnz | exact WOK | exact NH
      | intros j0 Hj0 [Hz Hnc]; destruct (Z.eq_dec j0 1) as [->|Hne]; [exact (Hc Hnc) | exact (Hinv j0 ltac:(lia) (conj Hz Hnc))] ].
Qed.
Lemma add_tail0 : TAILP 0.
Proof.
  unfold TAILP; intros ly S W regs mem md ch r p k bs M E ms mdc HP (HE & SHOK & HJ & HK) HS Hin_ HMnz WOK NH Hinv.
  change (KEEPR W (ms_mem ms) r bs) in HK.
  pose proof HP as (HPRE & H10 & H11 & H12 & Hk & Hin & HB & HI & HFO & HML & HM).
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). pose proof add_stk as WS.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ REG_SIZEB HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
  change (req_size REG_SIZEB) with 288 in *.
  pose proof HI as ([HL [H1 [H2 [H3 _]]]] & _). unfold Boxreg.boxreg_B1, Boxreg.boxreg_B2 in H1, H2.
  assert (Hn : bxu4 bs 280 = Boxreg.bx_n bs) by (apply bxu4_rd4; unfold Boxreg.bx_n in H1; lia).
  set (RUN := paj_run B LAWS). set (BR := paj_branch (PI := PI)). set (RUNTO := paj_run_to B LAWS).
  pose proof (proj1 HE) as HEI.
  arun RUN regs HS HJ SHOK.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ =>
    assert (EN : ew Ec 33 = Z_to_bv 64 (Boxreg.bx_n bs)) by (rewrite <- Hn; eok_ew HE 33%nat; reflexivity) end.
  psrr_branch_tok RUN BR HS SHOK ABspan.
  - change (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLT (SLit 0) (SOff 33 0))) (SOff 33 0)) with A2X in Hc.
    rewrite (dec_loop _ (Boxreg.bx_n bs) 1 EN) in Hc by (unfold Boxreg.bx_n in *; lia).
    apply negb_true_iff, Z.eqb_neq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8400.
    reabs_to HS HE SHOK (ss_row 1).
    eapply (add_row1 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | unfold Boxreg.bx_n in *; lia | exact HMnz | exact WOK | exact NH | intros j0 Hj0; apply Hinv; lia ].
  - change (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLT (SLit 0) (SOff 33 0))) (SOff 33 0)) with A2X in Hc.
    rewrite (dec_loop _ (Boxreg.bx_n bs) 1 EN) in Hc by (unfold Boxreg.bx_n in *; lia).
    apply negb_false_iff, Z.eqb_eq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8568.
    reabs_to HS HE SHOK ss_new.
    eapply (add_new_seg ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | exact HMnz | exact WOK | exact NH | intros j0 Hj0; apply Hinv; lia ].
Qed.
Lemma add_row0 : ROWP 0.
Proof.
  unfold ROWP; intros ly S W regs mem md ch r p k bs M E ms mdc HP (HE & SHOK & HJ & HK) HS Hin_ HMnz WOK NH Hinv.
  change (KEEPR W (ms_mem ms) r bs) in HK.
  pose proof HP as (HPRE & H10 & H11 & H12 & Hk & Hin & HB & HI & HFO & HML & HM).
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). pose proof add_stk as WS.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ REG_SIZEB HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
  change (req_size REG_SIZEB) with 288 in *.
  pose proof HI as ([HL [H1 [H2 [H3 _]]]] & _). unfold Boxreg.boxreg_B1, Boxreg.boxreg_B2 in H1, H2.
  assert (Hn : bxu4 bs 280 = Boxreg.bx_n bs) by (apply bxu4_rd4; unfold Boxreg.bx_n in H1; lia).
  set (RUN := paj_run B LAWS). set (BR := paj_branch (PI := PI)). set (RUNTO := paj_run_to B LAWS).
  pose proof (proj1 HE) as HEI.
  arun RUN regs HS HJ SHOK.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ => assert (Ea : ew Ec 35 = Z_to_bv 64 (bxb bs 0)) by (eok_ew HE 35%nat; reflexivity) end.
  psrr_branch_tok RUN BR HS SHOK ABspan;
    rewrite (dec_ne_atom_lit _ 35 (bxb bs 0) 0 Ea) in Hc by (pose proof (bxb_range bs 0); lia).
  { apply negb_true_iff, Z.eqb_neq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8528.
    reabs_to HS HE SHOK (ss_tail 0).
    eapply (add_tail0 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | assumption | exact HMnz | exact WOK | exact NH
      | intros j0 Hj0 [Hz Hnc]; destruct (Z.eq_dec j0 0) as [->|Hne];
        [ exact (mac_nz bs 0 0 HL ltac:(lia) ltac:(lia) Hc Hz) | exact (Hinv j0 ltac:(lia) (conj Hz Hnc)) ] ]. }
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb0. clear Ea.
  arun RUN regs HS HJ SHOK.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ => assert (Ea : ew Ec 36 = Z_to_bv 64 (bxb bs 1)) by (eok_ew HE 36%nat; reflexivity) end.
  psrr_branch_tok RUN BR HS SHOK ABspan;
    rewrite (dec_ne_atom_lit _ 36 (bxb bs 1) 0 Ea) in Hc by (pose proof (bxb_range bs 1); lia).
  { apply negb_true_iff, Z.eqb_neq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8528.
    reabs_to HS HE SHOK (ss_tail 0).
    eapply (add_tail0 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | assumption | exact HMnz | exact WOK | exact NH
      | intros j0 Hj0 [Hz Hnc]; destruct (Z.eq_dec j0 0) as [->|Hne];
        [ exact (mac_nz bs 0 1 HL ltac:(lia) ltac:(lia) Hc Hz) | exact (Hinv j0 ltac:(lia) (conj Hz Hnc)) ] ]. }
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb1. clear Ea.
  arun RUN regs HS HJ SHOK.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ => assert (Ea : ew Ec 37 = Z_to_bv 64 (bxb bs 2)) by (eok_ew HE 37%nat; reflexivity) end.
  psrr_branch_tok RUN BR HS SHOK ABspan;
    rewrite (dec_ne_atom_lit _ 37 (bxb bs 2) 0 Ea) in Hc by (pose proof (bxb_range bs 2); lia).
  { apply negb_true_iff, Z.eqb_neq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8528.
    reabs_to HS HE SHOK (ss_tail 0).
    eapply (add_tail0 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | assumption | exact HMnz | exact WOK | exact NH
      | intros j0 Hj0 [Hz Hnc]; destruct (Z.eq_dec j0 0) as [->|Hne];
        [ exact (mac_nz bs 0 2 HL ltac:(lia) ltac:(lia) Hc Hz) | exact (Hinv j0 ltac:(lia) (conj Hz Hnc)) ] ]. }
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb2. clear Ea.
  arun RUN regs HS HJ SHOK.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ => assert (Ea : ew Ec 38 = Z_to_bv 64 (bxb bs 3)) by (eok_ew HE 38%nat; reflexivity) end.
  psrr_branch_tok RUN BR HS SHOK ABspan;
    rewrite (dec_ne_atom_lit _ 38 (bxb bs 3) 0 Ea) in Hc by (pose proof (bxb_range bs 3); lia).
  { apply negb_true_iff, Z.eqb_neq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8528.
    reabs_to HS HE SHOK (ss_tail 0).
    eapply (add_tail0 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | assumption | exact HMnz | exact WOK | exact NH
      | intros j0 Hj0 [Hz Hnc]; destruct (Z.eq_dec j0 0) as [->|Hne];
        [ exact (mac_nz bs 0 3 HL ltac:(lia) ltac:(lia) Hc Hz) | exact (Hinv j0 ltac:(lia) (conj Hz Hnc)) ] ]. }
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb3. clear Ea.
  arun RUN regs HS HJ SHOK.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ => assert (Ea : ew Ec 39 = Z_to_bv 64 (bxb bs 4)) by (eok_ew HE 39%nat; reflexivity) end.
  psrr_branch_tok RUN BR HS SHOK ABspan;
    rewrite (dec_ne_atom_lit _ 39 (bxb bs 4) 0 Ea) in Hc by (pose proof (bxb_range bs 4); lia).
  { apply negb_true_iff, Z.eqb_neq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8528.
    reabs_to HS HE SHOK (ss_tail 0).
    eapply (add_tail0 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | assumption | exact HMnz | exact WOK | exact NH
      | intros j0 Hj0 [Hz Hnc]; destruct (Z.eq_dec j0 0) as [->|Hne];
        [ exact (mac_nz bs 0 4 HL ltac:(lia) ltac:(lia) Hc Hz) | exact (Hinv j0 ltac:(lia) (conj Hz Hnc)) ] ]. }
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb4. clear Ea.
  arun RUN regs HS HJ SHOK.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ => assert (Ea : ew Ec 40 = Z_to_bv 64 (bxb bs 5)) by (eok_ew HE 40%nat; reflexivity) end.
  psrr_branch_tok RUN BR HS SHOK ABspan;
    rewrite (dec_ne_atom_lit _ 40 (bxb bs 5) 0 Ea) in Hc by (pose proof (bxb_range bs 5); lia).
  { apply negb_true_iff, Z.eqb_neq in Hc.
    arun_to RUNTO regs HS HJ SHOK 8528.
    reabs_to HS HE SHOK (ss_tail 0).
    eapply (add_tail0 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | assumption | exact HMnz | exact WOK | exact NH
      | intros j0 Hj0 [Hz Hnc]; destruct (Z.eq_dec j0 0) as [->|Hne];
        [ exact (mac_nz bs 0 5 HL ltac:(lia) ltac:(lia) Hc Hz) | exact (Hinv j0 ltac:(lia) (conj Hz Hnc)) ] ]. }
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb5. clear Ea.
  arun RUN regs HS HJ SHOK.
  assert (Hmz : Boxreg.bx_mac bs 0 = Boxreg.zero6).
  { apply mac_z; [exact HL | lia |]. intros j0 Hj0.
    assert (j0 = 0 \/ j0 = 1 \/ j0 = 2 \/ j0 = 3 \/ j0 = 4 \/ j0 = 5) as Hc6 by lia.
    destruct Hc6 as [-> | [-> | [-> | [-> | [-> | ->]]]]]; zlit_goal; assumption. }
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ =>
    assert (Ea : ew Ec 65 = Z_to_bv 64 (bxu4 bs 12)) by (eok_ew HE 65%nat; reflexivity);
    assert (EK : ew Ec 12 = Z_to_bv 64 k) by (rewrite (EOK_reg _ _ _ _ 12 HE) by lia; exact H12) end.
  psrr_branch_tok RUN BR HS SHOK ABspan;
    rewrite (dec_nch _ 65 (bxu4 bs 12) k Ea (bxu4_range bs 12) EK Hk) in Hc.
  - apply Z.eqb_eq in Hc. (assert (Hnch : Boxreg.bx_nch bs 0 = bv_swrap 32 (bxu4 bs 12)) by exact (nch_swrap bs 0 HL ltac:(lia)));
    rewrite <- Hnch in Hc.
    arun_to RUNTO regs HS HJ SHOK 8768.
    reabs_to HS HE SHOK (ss_bind 0).
    eapply (add_bind_seg ly S W regs mem md ch r p k bs M _ _ _ 0 HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | lia | exact HMnz | exact WOK | exact NH
      | split; [lia | split; [exact Hmz | split; [exact Hc | exact Hinv]]] ].
  - apply Z.eqb_neq in Hc. (assert (Hnch : Boxreg.bx_nch bs 0 = bv_swrap 32 (bxu4 bs 12)) by exact (nch_swrap bs 0 HL ltac:(lia)));
    rewrite <- Hnch in Hc.
    arun_to RUNTO regs HS HJ SHOK 8528.
    reabs_to HS HE SHOK (ss_tail 0).
    eapply (add_tail0 ly S W regs mem md ch r p k bs M _ _ _ HP);
      [ split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | assumption | exact HMnz | exact WOK | exact NH
      | intros j0 Hj0 [Hz Hnc]; destruct (Z.eq_dec j0 0) as [->|Hne]; [exact (Hc Hnc) | exact (Hinv j0 ltac:(lia) (conj Hz Hnc))] ].
Qed.
Theorem pbb_reac_boxreg_add : tbreac_boxreg_add_spec.
Proof.
  unfold tbreac_boxreg_add_spec.
  intros ly S W regs mem md ch r p k bs M HPRE H10 H11 H12 Hk Hin HB HI HFO HML HM.
  assert (HP : add_pre ly S W regs mem md ch r p k bs M) by (unfold add_pre; repeat (split; [assumption|]); assumption).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  destruct (add_entry ly S W regs mem md ch r p bs HPRE H10 H11 Hin HB HI HFO) as [HS SHOK].
  pose proof (ajournal_init SEGS B REAC_BOXREG_ADD_STKB [(r, r + REG_SIZEB)] ly S W regs mem md ch HPRE) as HJ.
  assert (HE : EOK regs r bs (Eimg (Ereg regs (add_xs r bs)))).
  { split; [apply Eimg_env|]. split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. }
  assert (HK : KEEPR W mem r bs) by exact HB.
  remember (Eimg (Ereg regs (add_xs r bs))) as E eqn:HEdef. clear HEdef.
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). pose proof add_stk as WS.
  destruct (al_blocks _ _ LAWS ly S W mem md r REG_SIZEB HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
  change (req_size REG_SIZEB) with 288 in *.
  pose proof (proj1 HE) as HEI.
  assert (E1 : ew E 1 = getr regs 1) by (rewrite (EOK_reg _ _ _ _ 1 HE) by lia; reflexivity).
  assert (E2 : ew E 2 = getr regs 2) by (rewrite (EOK_reg _ _ _ _ 2 HE) by lia; reflexivity).
  assert (E3 : ew E 3 = getr regs 3) by (rewrite (EOK_reg _ _ _ _ 3 HE) by lia; reflexivity).
  assert (E4 : ew E 4 = getr regs 4) by (rewrite (EOK_reg _ _ _ _ 4 HE) by lia; reflexivity).
  assert (E10 : ew E 10 = w64 r) by (rewrite (EOK_reg _ _ _ _ 10 HE) by lia; exact H10).
  assert (E11 : ew E 11 = w64 p) by (rewrite (EOK_reg _ _ _ _ 11 HE) by lia; exact H11).
  assert (E12 : ew E 12 = w64 k) by (rewrite (EOK_reg _ _ _ _ 12 HE) by lia; exact H12).
  assert (Hspr : alloc_ceiling + 8352 <= spZ regs <= 2 ^ 47) by (rewrite WS in Hslo; lia).
  unfold cfg_at, AB_reac_boxreg_addP.
  change (w64 (BASE + AF_reac_boxreg_add)) with (Z_to_bv 64 (BASE + AF_reac_boxreg_add)).
  set (RUN := paj_run B LAWS). set (BR := paj_branch (PI := PI)).
  arun RUN regs HS HJ SHOK.
  pose proof HI as ([HL [H1 [H2 [H3 _]]]] & _). unfold Boxreg.boxreg_B1, Boxreg.boxreg_B2 in H1, H2.
  assert (Hn : bxu4 bs 280 = Boxreg.bx_n bs) by (apply bxu4_rd4; unfold Boxreg.bx_n in H1; lia).
  assert (Hf : bxu4 bs 284 = Boxreg.bx_fabric bs) by (apply bxu4_rd4; unfold Boxreg.bx_fabric in H2; lia).
  assert (EK : forall Ex, EOK regs r bs Ex -> ew Ex 12 = Z_to_bv 64 k)
    by (intros Ex HEx; rewrite (EOK_reg _ _ _ _ 12 HEx) by lia; exact H12).
  assert (EN : forall Ex, EOK regs r bs Ex -> ew Ex 33 = Z_to_bv 64 (Boxreg.bx_n bs))
    by (intros Ex HEx; rewrite <- Hn; eok_ew HEx 33%nat; reflexivity).
  assert (EF : forall Ex, EOK regs r bs Ex -> ew Ex 34 = Z_to_bv 64 (Boxreg.bx_fabric bs))
    by (intros Ex HEx; rewrite <- Hf; eok_ew HEx 34%nat; reflexivity).
  psrr_branch_tok RUN BR HS SHOK ABspan.
  { (* k outside 2..40: -1 *)
    rewrite (dec_kw _ k (EK _ HE) Hk) in Hc.
    ret_with RUN regs HP (-1) bs HS HJ SHOK; [a0_lit|].
    left. split; [left; intros (_ & Hw & _); apply negb_true_iff in Hc; apply andb_false_iff in Hc;
                  destruct Hc as [Hc|Hc]; [apply Z.leb_gt in Hc | apply Z.leb_gt in Hc]; lia | split; reflexivity]. }
  rewrite (dec_kw _ k (EK _ HE) Hk) in Hc. apply negb_false_iff, andb_true_iff in Hc.
  destruct Hc as [Hk2 Hk40]; apply Z.leb_le in Hk2; apply Z.leb_le in Hk40.
  arun RUN regs HS HJ SHOK.
  psrr_branch_tok RUN BR HS SHOK ABspan.
  { (* k odd: -1 *)
    rewrite (dec_odd _ k (EK _ HE)) in Hc.
    ret_with RUN regs HP (-1) bs HS HJ SHOK; [a0_lit|].
    left. split; [left; intros (He & _); apply negb_true_iff in Hc; apply Z.eqb_neq in Hc;
                  apply BoxregStep.bx_even in He; lia | split; reflexivity]. }
  rewrite (dec_odd _ k (EK _ HE)) in Hc. apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hkev.
  arun RUN regs HS HJ SHOK.
  psrr_branch_tok RUN BR HS SHOK ABspan.
  { (* fabric < k: -1 *)
    rewrite (dec_lts_atoms _ 34 12 (Boxreg.bx_fabric bs) k (EF _ HE) (EK _ HE)) in Hc by lia.
    ret_with RUN regs HP (-1) bs HS HJ SHOK; [a0_lit|].
    left. split; [left; intros (_ & _ & Hw); apply Z.ltb_lt in Hc; lia | split; reflexivity]. }
  rewrite (dec_lts_atoms _ 34 12 (Boxreg.bx_fabric bs) k (EF _ HE) (EK _ HE)) in Hc by lia. apply Z.ltb_ge in Hc. rename Hc into Hkf.
  assert (WOK : reac_boxreg_add_c.add_width_ok k (Boxreg.bx_fabric bs)) by (split; [apply BoxregStep.bx_even; exact Hkev | lia]).
  arun RUN regs HS HJ SHOK.
  (* the call of mac_is_zero *)
  pmkst HS. rewrite pa_sigma_mac_is_zero.
  prreg HS (10%bv : bv 5) Ra0. prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp.
  prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (8%bv : bv 5) Rs0.
  assert (Ra0' : getr (ms_regs ms) 10 = w64 p) by (rewrite Ra0; exact E11).
  assert (Qsp : spZ (ms_regs ms) = spZ regs + -80).
  { unfold spZ at 1. rewrite Rsp, E2. rewrite unsigned_lit_small; [reflexivity|]. unfold spZ in Hspr. lia. }
  assert (Hach : forall rg (L : alayout) rd sp, getr rg 8 = w64 k -> L = ly -> achain L rd sp (s0Z rg) []).
  { intros rg L rd sp Hs0 ->. left. split; [|reflexivity]. unfold s0Z. rewrite Hs0. unfold w64.
    rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    destruct (Z_lt_le_dec k 0) as [Hneg|Hpos].
    - right; left. rewrite <- (Z.mod_unique k (2 ^ 64) (-1) (k + 2 ^ 64)) by lia. lia.
    - left. rewrite Z.mod_small by lia. lia. }
  eapply SRr_bind.
  { eapply (cl_callS B LAWS W (ms_regs ms) (ms_mem ms) _ REAC_BOXREG_ADD_STKB (spZ regs) [(r, r + REG_SIZEB)]
              ly S W mem md [] ly S _ 0 BoxBMacIsZero.MAC_IS_ZERO_STKB [] 0 (-80) (getr (ms_regs ms) 1) [] _ HJ).
    - exact Qsp.
    - reflexivity.
    - lia.
    - unfold BoxBMacIsZero.MAC_IS_ZERO_STKB, ESTACK. lia.
    - rewrite WS. unfold BoxBMacIsZero.MAC_IS_ZERO_STKB, ESTACK. lia.
    - rewrite Rgp, E3. exact Hgp.
    - rewrite Rtp, E4. exact Htp.
    - reflexivity.
    - rewrite Rra. apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite Rra. pose proof pa_base_lo. pose proof pa_B_ok as (HB0 & HB1 & _). rewrite unsigned_lit_small by lia. lia.
    - apply Hach; [rewrite Rs0; exact E12 | reflexivity].
    - intros HPRE'. exact (MZ ly S W (ms_regs ms) (ms_mem ms) _ [] p M HPRE' Ra0'
                             (add_afobj_now _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP HJ) HML (add_mac_now _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP HJ)).
    - intros a Ha. destruct (inFP_nil a Ha). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP2 & (-> & -> & -> & Hres)).
  after_prog_call regs 600%nat Rra HS HJ SHOK HK HE HJ2 HJc HP2.
  set (RUNTO := paj_run_to B LAWS).
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ => assert (A604 : ew Ec 604 = getr regs2 10) by reflexivity end.
  clear Ra0 Ra0' Rsp Rgp Rtp Rs0 Qsp.
  destruct Hres as [(HMz & Ha) | (HMnz & Ha)]; rewrite Ha in A604.
  { (* M = zero6: -1 *)
    psrr_branch_tok RUN BR HS SHOK ABspan;
      rewrite (dec_eq_atom_lit _ 604 1 0 A604) in Hc by lia; [discriminate Hc|].
    ret_with RUN regs HP (-1) bs HS HJ SHOK; [a0_lit|].
    left. split; [right; exact HMz | split; reflexivity]. }
  psrr_branch_tok RUN BR HS SHOK ABspan;
    rewrite (dec_eq_atom_lit _ 604 0 0 A604) in Hc by lia; [|discriminate Hc].
  clear Hc A604 Ha.
  arun RUN regs HS HJ SHOK.
  (* the call of reac_boxreg_find *)
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msc) => rename msc into msF end.
  pmkst HS. rewrite pa_sigma_reac_boxreg_find.
  prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp.
  prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (8%bv : bv 5) Rs0.
  assert (Ra0' : getr (ms_regs msF) 10 = w64 r) by (rewrite Ra0; exact E10).
  assert (Ra1' : getr (ms_regs msF) 11 = w64 p) by (rewrite Ra1; exact E11).
  assert (Qsp : spZ (ms_regs msF) = spZ regs + -80).
  { unfold spZ at 1. rewrite Rsp, E2. rewrite unsigned_lit_small; [reflexivity|]. unfold spZ in Hspr. lia. }
  eapply SRr_bind.
  { eapply (cl_callS B LAWS W (ms_regs msF) (ms_mem msF) _ REAC_BOXREG_ADD_STKB (spZ regs) [(r, r + REG_SIZEB)]
              ly S W mem md [] ly S _ 0 BoxBReacBoxregFind.REAC_BOXREG_FIND_STKB [] 0 (-80) (getr (ms_regs msF) 1) [] _ HJ).
    - exact Qsp.
    - reflexivity.
    - lia.
    - unfold BoxBReacBoxregFind.REAC_BOXREG_FIND_STKB, BoxBMacIsZero.MAC_IS_ZERO_STKB, ESTACK. lia.
    - rewrite WS. unfold BoxBReacBoxregFind.REAC_BOXREG_FIND_STKB, BoxBMacIsZero.MAC_IS_ZERO_STKB, ESTACK. lia.
    - rewrite Rgp, E3. exact Hgp.
    - rewrite Rtp, E4. exact Htp.
    - reflexivity.
    - rewrite Rra. apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite Rra. pose proof pa_base_lo. pose proof pa_B_ok as (HB0 & HB1 & _). rewrite unsigned_lit_small by lia. lia.
    - apply Hach; [rewrite Rs0; exact E12 | reflexivity].
    - intros HPRE'. exact (FIND ly S W (ms_regs msF) (ms_mem msF) _ [] r p bs M HPRE' Ra0' Ra1' Hin HL HK H1
                             (add_afobj_now _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP HJ) HML (add_mac_now _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP HJ)).
    - intros a Ha. destruct (inFP_nil a Ha). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs3 & mem3 & md3 & -> & HJ2 & HJc & HP2 & (-> & -> & -> & _ & _ & _ & z & Hz & Hfr)).
  after_prog_call regs 620%nat Rra HS HJ SHOK HK HE HJ2 HJc HP2.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ => assert (A624 : ew Ec 624 = w64 z) by (rewrite <- Hz; reflexivity) end.
  clear Ra0 Ra1 Ra0' Ra1' Rsp Rgp Rtp Rs0 Qsp.
  assert (Hzr : -1 <= z < 5).
  { destruct Hfr as [(_ & ->) | [(_ & Hf1 & _) | (_ & -> & _)]]; [lia | unfold Boxreg.bx_n in *; lia | lia]. }
  arun RUN regs HS HJ SHOK.
  lazymatch goal with HE : EOK _ _ _ ?Ec |- _ => assert (A624' : ew Ec 624 = w64 z) by (rewrite <- A624; reflexivity) end.
  clear A624; rename A624' into A624.
  psrr_branch_tok RUN BR HS SHOK ABspan.
  { (* the MAC is held: z *)
    rewrite (dec_ge_atom_lit _ 624 z 0 A624) in Hc by lia. apply negb_true_iff, Z.ltb_ge in Hc.
    ret_with RUN regs HP z bs HS HJ SHOK.
    + apply sext_atom; [exact A624 | lia].
    + right; left. split; [exact WOK|]. split; [exact HMnz|]. split; [|reflexivity].
      destruct Hfr as [(E0 & _) | [(_ & Hf1) | (_ & E1' & _)]]; [exfalso; exact (HMnz E0) | exact Hf1 | lia]. }
  rewrite (dec_ge_atom_lit _ 624 z 0 A624) in Hc by lia. apply negb_false_iff, Z.ltb_lt in Hc.
  assert (NH : reac_boxreg_add_c.add_none_held bs M).
  { destruct Hfr as [(E0 & _) | [(_ & Hf1 & _) | (_ & _ & Hnh)]]; [exfalso; exact (HMnz E0) | lia | exact Hnh]. }
  clear Hfr Hz A624 Hc.
  arun RUN regs HS HJ SHOK.
  psrr_branch_tok RUN BR HS SHOK ABspan.
  { (* n = 0: the new row *)
    rewrite (dec_ge_lit_atom _ 33 0 (Boxreg.bx_n bs) (EN _ HE)) in Hc by (unfold Boxreg.bx_n in *; lia).
    apply negb_true_iff, Z.ltb_ge in Hc.
    arun_to RUNTO regs HS HJ SHOK 8568.
    reabs_to HS HE SHOK ss_new.
    eapply (add_new_seg ly S W regs mem md ch r p k bs M _ _ _ HP); [split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | exact HMnz | exact WOK | exact NH |].
    intros i Hi. unfold Boxreg.bx_n in *. lia. }
  rewrite (dec_ge_lit_atom _ 33 0 (Boxreg.bx_n bs) (EN _ HE)) in Hc by (unfold Boxreg.bx_n in *; lia).
  apply negb_false_iff, Z.ltb_lt in Hc.
  arun_to RUNTO regs HS HJ SHOK 8400.
  reabs_to HS HE SHOK (ss_row 0).
  eapply (add_row0 ly S W regs mem md ch r p k bs M _ _ _ HP); [split; [exact HE | split; [exact SHOK | split; [exact HJ | exact HK]]] | exact HS | lia | exact HMnz | exact WOK | exact NH |].
  intros j Hj. lia.
Unshelve.
all: unfold BoxBMacIsZero.MAC_IS_ZERO_STKB, BoxBReacBoxregFind.REAC_BOXREG_FIND_STKB, ESTACK; lia.
Qed.
End h.
End f.
End d.
