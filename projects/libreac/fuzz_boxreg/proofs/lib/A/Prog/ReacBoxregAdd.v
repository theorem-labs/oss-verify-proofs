(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8q.v:156-158;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203, 287-290,
   358-363, for libreac/fuzz_identity's asan-ubsan build (lib/B). The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8h.v:75-78, 95-98, 104-107. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_family_of.v, with its module paths and numbers changed; 5823 of its 5912 lines of code are new or changed and 758 lines of the source are left out. *)
(* reac_boxreg_add (fuzz_boxreg.asan 0x81ba8, 191 instructions; C: libreac src/reac_boxreg.c:86-120): the contract
   of the ASan build's code. The function takes an 80-byte frame on the machine stack (addi sp,sp,-80) and returns
   -1 when nch is not an even width 2..40 (addiw/bltu 0x81bdc-0x81be4, andi 0x81bec) or wider than r->fabric
   (lw r + 284, 0x81c14), or when the MAC is zero (mac_is_zero is inlined: 6 shadow-checked byte loads,
   0x81c20-0x81c54); else the index reac_boxreg_find (r, mac) gives (call 0x81c70) when it is >= 0; else it binds
   the first row i < n whose MAC is zero and whose nch (r + 56i + 12) is nch (inlined test 0x81cc0-0x81d28) with
   __asan_memcpy (r + 56i, mac, 6) (0x81e28) and returns i; else -1 when n >= 5 (0x81d50) or when
   lowest_free_base (r, nch) (call 0x81d98) is -1; else it clears row n with __asan_memset (r + 56n, 0, 56)
   (0x81dc4), copies the MAC with __asan_memcpy (r + 56n, mac, 6) (0x81dd4), stores the base at r + 56n + 8 and
   nch at r + 56n + 12, stores n + 1 at r + 280, and returns n (sext.w 0x81d5c).
   It writes nothing outside its own frame and the 288-byte registry block r.
   The memory model is Pau's plain one (lib/Prog/reac_boxreg_add_c.v add_out over lib/Prog/Boxreg.v), used as it
   is. add_out's two writing cases are BoxregUpd.v's bind_bytes bs M z (= upd_bytes bs (Z.to_nat (56 * z)) M)
   and new_row_bytes bs (add_row M b k) (= add_bytes bs M b k), the same terms after unfolding.
   Where the MAC is: mac points to the harness's local uint8_t mac[6] (fuzz/fuzz_boxreg.c:206, declared in the
   loop body), at offset 0x20 of the 0x1a0-byte frame LLVMFuzzerTestOneInput takes from __asan_stack_malloc_3
   (0x7ffbc; frame + 0x20 is stored at 0x80190-0x80198, its shadow byte set to 6 at 0x80220, and it is passed as
   a1 at the calls 0x80808 / 0x8088c). So the premise names it as an object of a side-stack frame, afobj p 6 (the
   form of grant's CtrlChecksumVerify.v and cgif lib/A/ACei.v), and gives its 6 bytes M.
   Hazards.
   (1) The registry struct is 288 bytes: 5 rows of 56 bytes (mac +0..6, base +8, nch +12, established +16,
       pinned +20, name +24..+56) in 0..280, n at +280, fabric at +284.
   (2) afobj holds only on the fake-stack path: when the runtime's detect_stack_use_after_return flag is 0 the
       harness takes its fallback (0x7ffc8-0x7ffec: the frame on the machine stack below its own), and mac is
       then in the caller's stack window, which afobj does not cover. cgif's model (stack_malloc_progressP) always
       gives the fake frame.
   (3) Stack: the callees' STK constants are taken from their files (ReacBoxregFind.v, LowestFreeBase.v).
       reac_boxreg_find calls bcmp (BS___interceptor_trampoline_bcmp, abcmp_realizes, 2 * ESTACK; CONVENTIONS
       section 4): REAC_BOXREG_FIND_STK = 48 + 2 * ESTACK is the largest, above lowest_free_base's 32 + ESTACK and
       the memcpy / memset wrappers' ESTACK; the Z.max below says so without depending on that order.
   (4) The int nch arrives sign-extended (LP64 ABI) and the code compares the whole register (blt 0x81c18,
       beq 0x81d18), so the premise is -2^31 <= k < 2^31, as in the plain contract.
   (5) Shadow-checked accesses: r + 284, r + 280, r + 56i + 12, the row MAC bytes, the store targets r + 56n + 8,
       r + 56n + 12, r + 280 (block shadow from AR, In (r, 288) (ablocks)), and the 6 MAC bytes (afobj's
       range_addressable); the __asan_report_* branches are refuted from these.
   (6) No f* / csr instruction occurs in the function (measured), so the fixed {fx} is sound.
   Image difference: the asan-ubsan build (lib/B/Prog/BoxBReacBoxregAdd.v) calls mac_is_zero for the MAC (0x81fec)
   instead of inlining it and adds UBSan traps (unimp at 0x821fc); the result and the written bytes are the same. *)
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
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow BoxSyms BoxList BoxPa.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaJournal BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import ReacBoxregInit.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require ReacBoxregFind LowestFreeBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg reac_boxreg_add_c BoxregUpd.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YImgTop YP00 YI0n YL02 YL09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaStep BoxPaLib YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require BoxFrame.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg box_listing}.
#[local] Notation SEGS := (@pa_segs _ box_listing PI).
#[local] Notation BASE := (@pa_val _ box_listing PI A_TEXT).
(* The function's address in the image and the stack it needs: its own 80-byte frame and, below it, the largest
   need of its callees (reac_boxreg_find, lowest_free_base, and ESTACK for the memcpy / memset wrappers). *)
Definition A_reac_boxreg_addP : Z := BASE + AF_reac_boxreg_add.
Definition REAC_BOXREG_ADD_STK : Z :=
  80 + Z.max ReacBoxregFind.REAC_BOXREG_FIND_STK (Z.max LowestFreeBase.LOWEST_FREE_BASE_STK ESTACK).
Section h.
Variable B : asyms.
Definition treac_boxreg_add_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md (r k : Z) (bs M : list byte)
  : world SEGS -> config -> Prop :=
apost_base SEGS B REAC_BOXREG_ADD_STK [(r, r + REG_SIZE)] regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' =>
ly' = ly /\ S' = S /\ W' = W /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
exists z bs', getr regs' 10 = w64 z /\ reac_boxreg_add_c.add_out bs M k z bs' /\
(forall i, 0 <= i < REG_SIZE ->
  aview SEGS (w_H W') mem' (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs' (Z_to_bv 8 0))))).
Definition treac_boxreg_add_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (r p k : Z) (bs M : list byte),
afn_pre SEGS B REAC_BOXREG_ADD_STK ly S W regs mem md ch ->
getr regs 10 = w64 r -> getr regs 11 = w64 p -> getr regs 12 = w64 k -> -2^31 <= k < 2^31 ->
In (r, REG_SIZE) (ablocks B ly S) ->
(forall i, 0 <= i < REG_SIZE ->
  aview SEGS (w_H W) mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
Boxreg.boxreg_inv bs ->
afobj SEGS B ly S W mem p 6 -> length M = 6%nat ->
(forall i, 0 <= i < 6 -> aview SEGS (w_H W) mem (p + i) = Some (bv_unsigned (nth (Z.to_nat i) M (Z_to_bv 8 0)))) ->
SRr SEGS W (cfg_at SEGS A_reac_boxreg_addP regs mem md) (treac_boxreg_add_post regs ly S W mem md r k bs M).
(* ---------------------------------------------------------------------- *)
(* The walk. *)
#[local] Notation VAL := (@pa_val _ box_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ box_listing PI).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA BS___asan_memset).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA BS___asan_memcpy).
Hypothesis FINDC : ReacBoxregFind.treac_boxreg_find_spec B.
Hypothesis LFBC : LowestFreeBase.tlowest_free_base_spec B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_box) (PI := PI).
(* The shadow base, the atom that holds it and the band of shadow addresses. *)
Definition ADSB : Z := 0x7fff8000.
Definition ADBx : sv := SOff 32 0.
Definition ADspan : Z * Z := (ADSB, ADSB + 2 ^ 44 - 1).
(* The byte values of the registry block and of the MAC, as the atoms hold them. *)
Definition adtb (bs : list byte) (i : Z) : Z := bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)).
Definition ad4 (bs : list byte) (i : Z) : Z :=
adtb bs i + 256 * adtb bs (i + 1) + 65536 * adtb bs (i + 2) + 16777216 * adtb bs (i + 3).
(* Helpers. *)
Lemma adm_bsub : forall bs k n j, 0 <= k -> 0 <= j < n ->
  adtb (Boxreg.bsub bs k n) j = adtb bs (k + j).
Proof.
  intros bs k n j Hk Hj. unfold adtb. rewrite <- !nth_default_eq. unfold nth_default.
  rewrite BoxregUpd.nth_bsub by lia.
  destruct (Nat.ltb_spec (Z.to_nat j) (Z.to_nat n)); [|lia].
  replace (Z.to_nat k + Z.to_nat j)%nat with (Z.to_nat (k + j)) by lia. reflexivity.
Qed.

Lemma adm_le_val4 : forall l : list byte, length l = 4%nat ->
  bytes_le_to_Z l = adtb l 0 + 256 * adtb l 1 + 65536 * adtb l 2 + 16777216 * adtb l 3.
Proof.
  intros l H. destruct l as [|x0 [|x1 [|x2 [|x3 [|x4 l]]]]]; cbn [length] in H; try lia.
  rewrite fuzz_boxreg.lib.Lib.Bytes.bytes_le_to_Z_le_val. unfold adtb.
  change (Z.to_nat 0) with 0%nat. change (Z.to_nat 1) with 1%nat.
  change (Z.to_nat 2) with 2%nat. change (Z.to_nat 3) with 3%nat.
  cbn [nth map fuzz_boxreg.lib.Lib.Bytes.le_val]. lia.
Qed.

Lemma adm_rd4 : forall bs k, 0 <= k -> k + 4 <= Z.of_nat (length bs) ->
  Boxreg.rd4 bs k = bv_swrap 32 (ad4 bs k).
Proof.
  intros bs k Hk H. unfold Boxreg.rd4. f_equal.
  rewrite adm_le_val4 by (rewrite Boxreg.bsub_length by lia; reflexivity).
  rewrite !adm_bsub by lia. unfold ad4. rewrite Z.add_0_r. reflexivity.
Qed.

Lemma adm_list_eq : forall l l' : list byte, length l = length l' ->
  (l = l' <-> forall j, 0 <= j < Z.of_nat (length l) -> adtb l j = adtb l' j).
Proof.
  intros l l' HL. split.
  - intros <- j _. reflexivity.
  - intros H. apply nth_ext with (d := Z_to_bv 8 0) (d' := Z_to_bv 8 0); [exact HL|].
    intros m Hm. apply bv_eq. specialize (H (Z.of_nat m) ltac:(lia)). unfold adtb in H.
    rewrite Nat2Z.id in H. exact H.
Qed.

Lemma adm_repeat0 : forall m j, adtb (repeat (Z_to_bv 8 0) m) j = 0.
Proof. intros m j. unfold adtb. rewrite nth_repeat, Z_to_bv_unsigned. reflexivity. Qed.

Lemma adm_upd : forall cs k bs i, (k + length bs <= length cs)%nat -> 0 <= i < Z.of_nat (length cs) ->
  adtb (fuzz_boxreg.lib.Lib.Mem.upd_bytes cs k bs) i =
  (if ((Z.of_nat k <=? i) && (i <? Z.of_nat k + Z.of_nat (length bs)))%bool
   then adtb bs (i - Z.of_nat k) else adtb cs i).
Proof.
  intros cs k bs i Hk Hi. unfold adtb. rewrite <- !nth_default_eq. unfold nth_default.
  rewrite fuzz_boxreg.lib.Lib.Mem.upd_bytes_nth by lia.
  destruct (Nat.leb_spec k (Z.to_nat i)); destruct (Nat.ltb_spec (Z.to_nat i) (k + length bs));
  destruct (Z.leb_spec (Z.of_nat k) i); destruct (Z.ltb_spec i (Z.of_nat k + Z.of_nat (length bs)));
  cbn [andb]; try (exfalso; lia); try reflexivity.
  replace (Z.to_nat (i - Z.of_nat k)) with (Z.to_nat i - k)%nat by lia. reflexivity.
Qed.

Lemma adm_app : forall (l1 l2 : list byte) j, 0 <= j ->
  adtb (l1 ++ l2) j =
  (if j <? Z.of_nat (length l1) then adtb l1 j else adtb l2 (j - Z.of_nat (length l1))).
Proof.
  intros l1 l2 j Hj. unfold adtb. destruct (Z.ltb_spec j (Z.of_nat (length l1))).
  - rewrite app_nth1 by lia. reflexivity.
  - rewrite app_nth2 by lia.
    replace (Z.to_nat (j - Z.of_nat (length l1))) with (Z.to_nat j - length l1)%nat by lia. reflexivity.
Qed.

Lemma adm_le4b : forall v j j', j = j' -> 0 <= j < 4 ->
  adtb (fuzz_boxreg.lib.Lib.Mem.le4 (Z_to_bv 64 v)) j = (v / 2 ^ (8 * j')) mod 256.
Proof.
  intros v j j' <- Hj. unfold fuzz_boxreg.lib.Lib.Mem.le4, adtb. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 v) with (v mod 2^64).
  assert (E : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by lia.
  destruct E as [-> | [-> | [-> | ->]]].
  - change (Z.to_nat 0) with 0%nat. cbn [Z_to_le_bytes nth]. rewrite Z_to_bv_unsigned.
    change (bv_wrap 8 ?x) with (x mod 2^8). change (2 ^ (8 * 0)) with 1.
    Z.div_mod_to_equations. lia.
  - change (Z.to_nat 1) with 1%nat. cbn [Z_to_le_bytes nth]. rewrite Z_to_bv_unsigned.
    change (bv_wrap 8 ?x) with (x mod 2^8). change (2 ^ (8 * 1)) with (2^8).
    rewrite !Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. lia.
  - change (Z.to_nat 2) with 2%nat. cbn [Z_to_le_bytes nth]. rewrite Z_to_bv_unsigned.
    change (bv_wrap 8 ?x) with (x mod 2^8). change (2 ^ (8 * 2)) with (2^16).
    rewrite !Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. lia.
  - change (Z.to_nat 3) with 3%nat. cbn [Z_to_le_bytes nth]. rewrite Z_to_bv_unsigned.
    change (bv_wrap 8 ?x) with (x mod 2^8). change (2 ^ (8 * 3)) with (2^24).
    rewrite !Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. lia.
Qed.

Lemma adm_le4_0 : forall j, 0 <= j < 4 -> adtb (fuzz_boxreg.lib.Lib.Mem.le4 (Z_to_bv 64 0)) j = 0.
Proof.
  intros j Hj. rewrite (adm_le4b 0 j j eq_refl Hj).
  assert (E : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by lia.
  destruct E as [-> | [-> | [-> | ->]]]; reflexivity.
Qed.

Local Ltac adm_simp :=
  repeat match goal with
  | |- context [Z.ltb ?a ?b] =>
      first [ rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia ]; cbn [andb]
  | |- context [Z.leb ?a ?b] =>
      first [ rewrite (proj2 (Z.leb_le a b)) by lia | rewrite (proj2 (Z.leb_gt a b)) by lia ]; cbn [andb]
  end.

(* a. *)
Lemma ad_bx_n : forall bs, length bs = 288%nat -> Boxreg.bx_n bs = bv_swrap 32 (ad4 bs 280).
Proof. intros bs HL. unfold Boxreg.bx_n. apply adm_rd4; rewrite ?HL; lia. Qed.

(* b. *)
Lemma ad_bx_fabric : forall bs, length bs = 288%nat -> Boxreg.bx_fabric bs = bv_swrap 32 (ad4 bs 284).
Proof. intros bs HL. unfold Boxreg.bx_fabric. apply adm_rd4; rewrite ?HL; lia. Qed.

(* c. *)
Lemma ad_bx_nch : forall bs i, length bs = 288%nat -> 0 <= i <= 4 ->
  Boxreg.bx_nch bs i = bv_swrap 32 (ad4 bs (56 * i + 12)).
Proof. intros bs i HL Hi. unfold Boxreg.bx_nch. apply adm_rd4; rewrite ?HL; lia. Qed.

(* d. *)
Lemma ad_mac_zero : forall bs i, length bs = 288%nat -> 0 <= i <= 4 ->
  (Boxreg.bx_mac bs i = Boxreg.zero6 <-> forall j, 0 <= j < 6 -> adtb bs (56 * i + j) = 0).
Proof.
  intros bs i HL Hi. unfold Boxreg.bx_mac.
  assert (L : length (Boxreg.bsub bs (56 * i) 6) = 6%nat)
    by (rewrite Boxreg.bsub_length by lia; reflexivity).
  rewrite (adm_list_eq (Boxreg.bsub bs (56 * i) 6) Boxreg.zero6) by (rewrite L; reflexivity).
  rewrite L. unfold Boxreg.zero6. split.
  - intros H j Hj. specialize (H j ltac:(lia)). rewrite adm_bsub, adm_repeat0 in H by lia. exact H.
  - intros H j Hj. rewrite adm_bsub, adm_repeat0 by lia. apply H. lia.
Qed.

(* e. *)
Lemma ad_M_zero : forall M, length M = 6%nat ->
  (M = Boxreg.zero6 <-> forall j, 0 <= j < 6 -> adtb M j = 0).
Proof.
  intros M HM. rewrite (adm_list_eq M Boxreg.zero6) by (rewrite HM; reflexivity).
  rewrite HM. unfold Boxreg.zero6. split.
  - intros H j Hj. specialize (H j ltac:(lia)). rewrite adm_repeat0 in H. exact H.
  - intros H j Hj. rewrite adm_repeat0. apply H. lia.
Qed.

(* f. *)
Lemma ad_mac_eq : forall bs M i, length bs = 288%nat -> length M = 6%nat -> 0 <= i <= 4 ->
  (Boxreg.bx_mac bs i = M <-> forall j, 0 <= j < 6 -> adtb bs (56 * i + j) = adtb M j).
Proof.
  intros bs M i HL HM Hi. unfold Boxreg.bx_mac.
  assert (L : length (Boxreg.bsub bs (56 * i) 6) = 6%nat)
    by (rewrite Boxreg.bsub_length by lia; reflexivity).
  rewrite (adm_list_eq (Boxreg.bsub bs (56 * i) 6) M) by (rewrite L, HM; reflexivity).
  rewrite L. split.
  - intros H j Hj. specialize (H j ltac:(lia)). rewrite adm_bsub in H by lia. exact H.
  - intros H j Hj. rewrite adm_bsub by lia. apply H. lia.
Qed.

(* g. *)
Lemma ad_bind_view : forall bs M z i, length bs = 288%nat -> length M = 6%nat -> 0 <= z <= 4 -> 0 <= i < 288 ->
  adtb (BoxregUpd.bind_bytes bs M z) i =
  (if ((56 * z <=? i) && (i <? 56 * z + 6))%bool then adtb M (i - 56 * z) else adtb bs i).
Proof.
  intros bs M z i HL HM Hz Hi. unfold BoxregUpd.bind_bytes.
  rewrite adm_upd by (rewrite ?HL, ?HM; lia).
  rewrite HM, Z2Nat.id by lia. reflexivity.
Qed.

(* h. *)
Lemma ad_new_view : forall bs M b k i, Boxreg.boxreg_inv bs -> length M = 6%nat ->
  0 <= Boxreg.bx_n bs <= 4 -> -2^31 <= b < 2^31 -> -2^31 <= k < 2^31 -> 0 <= i < 288 ->
  adtb (reac_boxreg_add_c.add_bytes bs M b k) i =
  (let n := Boxreg.bx_n bs in
   if (i <? 56*n)%bool then adtb bs i
   else if (i <? 56*n+6)%bool then adtb M (i - 56*n)
   else if (i <? 56*n+8)%bool then 0
   else if (i <? 56*n+12)%bool then (b / 2^(8*(i-56*n-8))) mod 256
   else if (i <? 56*n+16)%bool then (k / 2^(8*(i-56*n-12))) mod 256
   else if (i <? 56*n+56)%bool then 0
   else if (i <? 280)%bool then adtb bs i
   else if (i <? 284)%bool then ((n+1) / 2^(8*(i-280))) mod 256
   else adtb bs i).
Proof.
  intros bs M b k i HI HM Hn Hb Hk Hi.
  assert (HL : length bs = 288%nat) by (destruct HI as [[HL _] _]; exact HL).
  cbv zeta. unfold reac_boxreg_add_c.add_bytes.
  set (n := Boxreg.bx_n bs) in *.
  assert (HR : length (reac_boxreg_add_c.add_row M b k) = 56%nat).
  { unfold reac_boxreg_add_c.add_row.
    rewrite !length_app, HM, !repeat_length, !fuzz_boxreg.lib.Lib.Mem.length_le4. reflexivity. }
  assert (HL1 : length (fuzz_boxreg.lib.Lib.Mem.upd_bytes bs (Z.to_nat (56 * n))
                          (reac_boxreg_add_c.add_row M b k)) = 288%nat).
  { rewrite fuzz_boxreg.lib.Lib.Mem.upd_bytes_length; rewrite ?HR, ?HL; lia. }
  rewrite adm_upd by (rewrite ?HL1, ?fuzz_boxreg.lib.Lib.Mem.length_le4; lia).
  rewrite adm_upd by (rewrite ?HL, ?HR; lia).
  rewrite fuzz_boxreg.lib.Lib.Mem.length_le4, HR, Z2Nat.id by lia.
  unfold reac_boxreg_add_c.add_row.
  assert (C : i < 56*n \/ 56*n <= i < 56*n+6 \/ 56*n+6 <= i < 56*n+8 \/ 56*n+8 <= i < 56*n+12 \/
              56*n+12 <= i < 56*n+16 \/ 56*n+16 <= i < 56*n+20 \/ 56*n+20 <= i < 56*n+24 \/
              56*n+24 <= i < 56*n+56 \/ 56*n+56 <= i < 280 \/ 280 <= i < 284 \/ 284 <= i) by lia.
  destruct C as [C|[C|[C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]]]; adm_simp;
    repeat (rewrite adm_app by lia;
            rewrite ?HM, ?repeat_length, ?fuzz_boxreg.lib.Lib.Mem.length_le4; adm_simp);
    first [ reflexivity | apply adm_repeat0 | apply adm_le4_0; lia | apply adm_le4b; lia ].
Qed.
Definition adrowv (bs : list byte) (i : Z) : list Z :=
[adtb bs (56 * i); adtb bs (56 * i + 1); adtb bs (56 * i + 2); adtb bs (56 * i + 3);
 adtb bs (56 * i + 4); adtb bs (56 * i + 5); ad4 bs (56 * i + 12)].
Definition adextra (bs M : list byte) : list word :=
map (Z_to_bv 64)
([ADSB; ad4 bs 280; ad4 bs 284]
 ++ adrowv bs 0 ++ adrowv bs 1 ++ adrowv bs 2 ++ adrowv bs 3 ++ adrowv bs 4
 ++ [adtb M 0; adtb M 1; adtb M 2; adtb M 3; adtb M 4; adtb M 5]).
Definition adE (regs : bvmap 5 word) (bs M : list byte) : env := Eimg (Ereg regs (adextra bs M)).
(* The regions of the symbolic state: the registry block (its rows read one byte at a time, its n and
   fabric words), the MAC, the frame, the GOT word of the shadow base and the shadow cell. *)
Definition adrow (i : nat) : list YP09.chunk :=
[ YP09.mkChunk (56 * Z.of_nat i) (CVal 1 (SOff (35 + 7 * i)%nat 0));
  YP09.mkChunk (56 * Z.of_nat i + 1) (CVal 1 (SOff (36 + 7 * i)%nat 0));
  YP09.mkChunk (56 * Z.of_nat i + 2) (CVal 1 (SOff (37 + 7 * i)%nat 0));
  YP09.mkChunk (56 * Z.of_nat i + 3) (CVal 1 (SOff (38 + 7 * i)%nat 0));
  YP09.mkChunk (56 * Z.of_nat i + 4) (CVal 1 (SOff (39 + 7 * i)%nat 0));
  YP09.mkChunk (56 * Z.of_nat i + 5) (CVal 1 (SOff (40 + 7 * i)%nat 0));
  YP09.mkChunk (56 * Z.of_nat i + 12) (CVal 4 (SOff (41 + 7 * i)%nat 0)) ].
Definition adR : YP09.region :=
YP09.mkRegion (Some 10%nat) 0 288 0 0
(adrow 0 ++ adrow 1 ++ adrow 2 ++ adrow 3 ++ adrow 4
 ++ [YP09.mkChunk 280 (CVal 4 (SOff 33 0)); YP09.mkChunk 284 (CVal 4 (SOff 34 0))]).
Definition adP : YP09.region :=
YP09.mkRegion (Some 11%nat) 0 6 0 0
[ YP09.mkChunk 0 (CVal 1 (SOff 70 0)); YP09.mkChunk 1 (CVal 1 (SOff 71 0));
  YP09.mkChunk 2 (CVal 1 (SOff 72 0)); YP09.mkChunk 3 (CVal 1 (SOff 73 0));
  YP09.mkChunk 4 (CVal 1 (SOff 74 0)); YP09.mkChunk 5 (CVal 1 (SOff 75 0)) ].
Definition adregions : smem := [adR; adP; stack_region 80; got_regionP; bcell_regionP 32].
Definition adrowf (i : nat) : list (nat * afact) :=
[ ((35 + 7 * i)%nat, mkAF 0 255 0); ((36 + 7 * i)%nat, mkAF 0 255 0); ((37 + 7 * i)%nat, mkAF 0 255 0);
  ((38 + 7 * i)%nat, mkAF 0 255 0); ((39 + 7 * i)%nat, mkAF 0 255 0); ((40 + 7 * i)%nat, mkAF 0 255 0);
  ((41 + 7 * i)%nat, mkAF 0 (2 ^ 32 - 1) 0) ].
Definition adfacts : facts :=
mkFacts ([(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, PTR 4); (11%nat, PTR 3);
          (32%nat, mkAF ADSB ADSB 0); (33%nat, mkAF 0 (2 ^ 32 - 1) 0); (34%nat, mkAF 0 (2 ^ 32 - 1) 0);
          (70%nat, mkAF 0 255 0); (71%nat, mkAF 0 255 0); (72%nat, mkAF 0 255 0);
          (73%nat, mkAF 0 255 0); (74%nat, mkAF 0 255 0); (75%nat, mkAF 0 255 0)]
         ++ adrowf 0 ++ adrowf 1 ++ adrowf 2 ++ adrowf 3 ++ adrowf 4) [] [].
Definition adSH : list shent := [mkSHE 10 0 288; mkSHE 11 0 6].
Definition adss : sstate := mkSS AF_reac_boxreg_add sr_atoms adregions None adfacts.
(* A byte and a four-byte word of the view, as the chunks of a region ask for them. *)
Lemma ad_val1 : forall (H : word -> bool) (m : word -> option byte) (a v : Z),
aview SEGS H m a = Some v -> val_mem SEGS (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv. unfold aview, option_map in Hv.
destruct (mbyte SEGS (mrestrict H m) a) as [b|] eqn:Hb; [|discriminate].
injection Hv as <-. pose proof (bv_unsigned_in_range 8 b) as Hr.
change (bv_modulus 8) with 256 in Hr.
intros kk Hk. assert (kk = 0%nat) as -> by lia. cbn [Z.of_nat].
rewrite Z.add_0_r, Hb. f_equal.
rewrite (le_byte_small (bv_unsigned b) 1 0) by (cbn; lia).
cbn [Z.of_nat]. change (8 * 0) with 0. rewrite Z.shiftr_0_r. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma ad_val4 : forall (H : word -> bool) (m : word -> option byte) (a v0 v1 v2 v3 : Z),
aview SEGS H m a = Some v0 -> aview SEGS H m (a + 1) = Some v1 ->
aview SEGS H m (a + 2) = Some v2 -> aview SEGS H m (a + 3) = Some v3 ->
val_mem SEGS (mrestrict H m) a 4 (v0 + 256 * v1 + 65536 * v2 + 16777216 * v3).
Proof.
intros H m a v0 v1 v2 v3 H0 H1 H2 H3.
assert (Hb : forall c v, aview SEGS H m c = Some v ->
  exists b : byte, mbyte SEGS (mrestrict H m) c = Some b /\ v = bv_unsigned b /\ 0 <= v < 256).
{ intros c v Hv. unfold aview, option_map in Hv.
  destruct (mbyte SEGS (mrestrict H m) c) as [b|] eqn:Hbb; [|discriminate].
  injection Hv as <-. pose proof (bv_unsigned_in_range 8 b) as Hr.
  change (bv_modulus 8) with 256 in Hr. exists b. auto. }
destruct (Hb a v0 H0) as (b0 & Hm0 & -> & R0). destruct (Hb (a + 1) v1 H1) as (b1 & Hm1 & -> & R1).
destruct (Hb (a + 2) v2 H2) as (b2 & Hm2 & -> & R2). destruct (Hb (a + 3) v3 H3) as (b3 & Hm3 & -> & R3).
set (v := bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3).
assert (Hv : 0 <= v < 2 ^ (8 * Z.of_nat 4))
by (replace (2 ^ (8 * Z.of_nat 4)) with 4294967296 by (vm_compute; reflexivity); unfold v; lia).
assert (Hbyte : forall (bb : byte) (q : Z), 0 <= q -> bv_unsigned bb = (v / 2 ^ q) mod 256 ->
  Some bb = Some (Z_to_bv 8 (Z.shiftr v q))).
{ intros bb q Hq Hq2. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. rewrite Z.shiftr_div_pow2 by lia. rewrite Hq2. reflexivity. }
assert (K0 : (0 < 4)%nat) by lia. assert (K1 : (1 < 4)%nat) by lia.
assert (K2 : (2 < 4)%nat) by lia. assert (K3 : (3 < 4)%nat) by lia.
intros kk Hk. destruct kk as [|[|[|[|kk]]]]; try lia.
- rewrite (le_byte_small v 4 0%nat Hv K0). change (Z.of_nat 0) with 0.
  rewrite Z.add_0_r, Hm0. apply (Hbyte b0 0); [lia|]. change (2 ^ 0) with 1.
  rewrite Z.div_1_r. unfold v. Z.div_mod_to_equations. lia.
- rewrite (le_byte_small v 4 1%nat Hv K1). change (Z.of_nat 1) with 1.
  rewrite Hm1. apply (Hbyte b1 8); [lia|]. change (2 ^ 8) with 256. unfold v.
  Z.div_mod_to_equations. lia.
- rewrite (le_byte_small v 4 2%nat Hv K2). change (Z.of_nat 2) with 2.
  rewrite Hm2. apply (Hbyte b2 16); [lia|]. change (2 ^ 16) with 65536. unfold v.
  Z.div_mod_to_equations. lia.
- rewrite (le_byte_small v 4 3%nat Hv K3). change (Z.of_nat 3) with 3.
  rewrite Hm3. apply (Hbyte b3 24); [lia|]. change (2 ^ 24) with 16777216. unfold v.
  Z.div_mod_to_equations. lia.
Qed.
(* The width test at 0x81be4: bltu (k - 41 as an int), -39. *)
Lemma ad_wtest : forall E n v, ew E n = Z_to_bv 64 v -> - 2 ^ 31 <= v < 2 ^ 31 ->
branch_taken BC_LTU (sv_denot E (SAluw ALU_ADD (SOff n 0) (SLit (-41))))
(sv_denot E (SLit 18446744073709551577)) = negb ((2 <=? v) && (v <=? 40)).
Proof.
intros E n v H Hv.
rewrite branch_ltu_U, (U_of_S E (SAluw ALU_ADD (SOff n 0) (SLit (-41)))), S_SAluw, U_SOff, !U_SLit, H,
Z.add_0_r, Z_to_bv_unsigned.
cbn [zalu_raw].
assert (A1 : zcanon (bv_wrap 64 v) mod 2 ^ 32 = v mod 2 ^ 32).
{ unfold zcanon, bv_wrap, M64. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia.
  Z.div_mod_to_equations; lia. }
replace (zcanon (-41) mod 2 ^ 32) with (2 ^ 32 - 41) by reflexivity.
replace (zcanon 18446744073709551577) with 18446744073709551577 by reflexivity.
rewrite A1. unfold bv_swrap, bv_wrap.
change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 32) with (2 ^ 32).
change (bv_half_modulus 32) with (2 ^ 31).
destruct (Z.leb_spec 2 v); destruct (Z.leb_spec v 40); cbn [andb negb];
first [apply Z.ltb_lt | apply Z.ltb_ge]; Z.div_mod_to_equations; lia.
Qed.
(* The parity test at 0x81bf0: bnez (k & 1). *)
Lemma ad_odd : forall E n v, ew E n = Z_to_bv 64 v ->
branch_taken BC_NE (sv_denot E (SAlu ALU_AND (SOff n 0) (SLit 1))) (sv_denot E (SLit 0))
= negb (Z.even v).
Proof.
intros E n v H. rewrite branch_ne_U, U_SAlu, U_SOff, !U_SLit, H, Z.add_0_r, Z_to_bv_unsigned.
cbn [zalu_raw].
replace (zcanon 1) with 1 by reflexivity. replace (zcanon 0) with 0 by reflexivity.
assert (A : Z.land (zcanon (bv_wrap 64 v)) 1 = v mod 2).
{ change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. change (2 ^ 1) with 2.
  unfold zcanon, bv_wrap, M64. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia.
  Z.div_mod_to_equations; lia. }
rewrite A, zcanon_id by (pose proof (Z.mod_pos_bound v 2 ltac:(lia)); unfold M64; lia).
rewrite Zmod_even. destruct (Z.even v); reflexivity.
Qed.
Lemma adtb_range : forall bs i, 0 <= adtb bs i < 256.
Proof.
intros bs i. unfold adtb. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) bs (Z_to_bv 8 0))) as H.
change (bv_modulus 8) with 256 in H. exact H.
Qed.
Lemma ad4_range : forall bs i, 0 <= ad4 bs i < 2 ^ 32.
Proof.
intros bs i. unfold ad4. pose proof (adtb_range bs i). pose proof (adtb_range bs (i + 1)).
pose proof (adtb_range bs (i + 2)). pose proof (adtb_range bs (i + 3)). lia.
Qed.
(* The signed value of an atom and of a sign-extended 32-bit field. *)
Lemma ad_sg_off : forall E n v, ew E n = Z_to_bv 64 v -> - 2 ^ 63 <= v < 2 ^ 63 -> Sg E (SOff n 0) = v.
Proof.
intros E n v H Hv. rewrite S_of_U, U_SOff, H, Z.add_0_r, Z_to_bv_unsigned.
rewrite zcanon_wrap, !(bv_swrap_wrap 64). apply swrap64_id. unfold half64. lia.
Qed.
Lemma ad_sg_sext : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
Sg E (SExt true 32 (SOff n 0)) = bv_swrap 32 v.
Proof.
intros E n v H Hv.
assert (HU : U E (SOff n 0) = v).
{ rewrite U_SOff, H, Z.add_0_r, Z_to_bv_unsigned, zcanon_wrap. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small v (2 ^ 64)) by lia.
  apply Z.mod_small. lia. }
assert (HX : U E (SExt true 32 (SOff n 0)) = zcanon (bv_swrap 32 v)).
{ rewrite U_SExt, HU. f_equal. cbn [Z.of_N]. rewrite (Z.mod_small v (2 ^ 32)) by lia. reflexivity. }
rewrite S_of_U, HX. apply swrap64_zcanon_swrap32.
Qed.
Lemma ad_bnz : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = negb (v =? 0).
Proof.
intros E n v H Hv. rewrite branch_ne_U, (U_atom E n v H ltac:(lia)), U_SLit.
replace (zcanon 0) with 0 by reflexivity. reflexivity.
Qed.
Lemma ad_beq0 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (v =? 0).
Proof.
intros E n v H Hv. rewrite branch_eq_U, (U_atom E n v H ltac:(lia)), U_SLit.
replace (zcanon 0) with 0 by reflexivity. reflexivity.
Qed.
Lemma ad_blt : forall E n v nk kk,
ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 -> ew E nk = Z_to_bv 64 kk -> - 2 ^ 31 <= kk < 2 ^ 31 ->
branch_taken BC_LT (sv_denot E (SExt true 32 (SOff n 0))) (sv_denot E (SOff nk 0))
= (bv_swrap 32 v <? kk).
Proof.
intros E n v nk kk Hn Hv Hk Hkk. cbn [branch_taken]. unfold bv_lts.
change (bv_signed (sv_denot E (SExt true 32 (SOff n 0)))) with (Sg E (SExt true 32 (SOff n 0))).
change (bv_signed (sv_denot E (SOff nk 0))) with (Sg E (SOff nk 0)).
rewrite (ad_sg_sext E n v Hn Hv), (ad_sg_off E nk kk Hk ltac:(lia)). reflexivity.
Qed.
Lemma ad_ewn : forall regs extra n j, n = (32 + j)%nat -> ew (Ereg regs extra) n = nth j extra (Z_to_bv 64 0).
Proof. intros regs extra n j ->. apply ew_Ereg_extra. Qed.
(* The ranges of the atom values and the afacts they give. *)
Lemma ad_tb_rng : forall (bs : list byte) i, 0 <= adtb bs i < 256.
Proof.
intros bs i. unfold adtb. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) bs (Z_to_bv 8 0))) as H.
change (bv_modulus 8) with 256 in H. exact H.
Qed.
Lemma ad_4_rng : forall bs i, 0 <= ad4 bs i < 4294967296.
Proof.
intros bs i. unfold ad4.
pose proof (ad_tb_rng bs i). pose proof (ad_tb_rng bs (i + 1)).
pose proof (ad_tb_rng bs (i + 2)). pose proof (ad_tb_rng bs (i + 3)). lia.
Qed.
Lemma ad_afb : forall E n bs i, ew E n = Z_to_bv 64 (adtb bs i) -> afact_ok E n (mkAF 0 255 0).
Proof.
intros E n bs i H. pose proof (ad_tb_rng bs i) as R. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite H, unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.
Lemma ad_afw : forall E n bs i, ew E n = Z_to_bv 64 (ad4 bs i) -> afact_ok E n (mkAF 0 (2 ^ 32 - 1) 0).
Proof.
intros E n bs i H. pose proof (ad_4_rng bs i) as R. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite H, unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.
Lemma ad_entry : forall ly S W (regs : bvmap 5 word) mem md ch (r p : Z) (bs M : list byte),
afn_pre SEGS B REAC_BOXREG_ADD_STK ly S W regs mem md ch ->
getr regs 10 = w64 r -> getr regs 11 = w64 p ->
In (r, REG_SIZE) (ablocks B ly S) ->
(forall i, 0 <= i < REG_SIZE -> aview SEGS (w_H W) mem (r + i) = Some (adtb bs i)) ->
afobj SEGS B ly S W mem p 6 ->
(forall i, 0 <= i < 6 -> aview SEGS (w_H W) mem (p + i) = Some (adtb M i)) ->
st_ok_pi SEGS VAL (adE regs bs M) adss
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_reac_boxreg_addP) mem (seg_rom SEGS)))
/\ sh_ok SEGS ADBx adSH (adE regs bs M) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch r p bs M HPRE H10 H11 Hin Hbs HFO HMv.
pose proof HFO as ((cid & pos & Hfin & Hcid & Hfal & Hflo & Hfhi) & Hp8 & HRA).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hchn & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOXREG_ADD_STK = 8320) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md r REG_SIZE HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hrapp & Hrpres & _ & _).
pose proof (blk_off_imgP B ly S W mem md r REG_SIZE HAR Hin) as Hrimg.
change (req_size REG_SIZE) with 288 in Hrceil, Hrapp, Hrpres, Hrimg.
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfapp).
pose proof (frm_off_imgP B ly S W mem md cid pos HAR Hfin) as Hfimg.
pose proof (sep_block_frame SEGS B LAWS ly S W mem md r REG_SIZE cid pos HAR Hin Hfin) as Hrf.
unfold zdisjoint in Hrf. cbn [fst snd] in Hrf. change (req_size REG_SIZE) with 288 in Hrf.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
pose proof (range_addressable_of_block SEGS B LAWS ly S W mem md r REG_SIZE r 288 HAR Hin
  ltac:(lia) ltac:(change (req_size REG_SIZE) with 288; lia)) as HRAr.
assert (V1 : forall o, 0 <= o < 288 -> val_mem SEGS (mrestrict (w_H W) mem) (r + o) 1 (adtb bs o))
by (intros o Ho; apply ad_val1; apply Hbs; unfold REG_SIZE; lia).
assert (V4 : forall o, 0 <= o -> o + 4 <= 288 -> val_mem SEGS (mrestrict (w_H W) mem) (r + o) 4 (ad4 bs o))
by (intros o Ho1 Ho2; unfold ad4; apply ad_val4; rewrite <- ?Z.add_assoc; apply Hbs; unfold REG_SIZE; lia).
assert (VM : forall o, 0 <= o < 6 -> val_mem SEGS (mrestrict (w_H W) mem) (p + o) 1 (adtb M o))
by (intros o Ho; apply ad_val1; apply HMv; lia).
rewrite restrict_mkst_fx.
set (E := adE regs bs M).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (adextra bs M)) n)
by (intros n Hn; subst E; unfold adE; apply Eimg_low; exact Hn).
assert (EW : forall n j, n = (32 + j)%nat -> (j < 44)%nat -> ew E n = nth j (adextra bs M) (Z_to_bv 64 0)).
{ intros n j -> Hj. rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 r)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 p)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 ADSB) by (rewrite (EW 32%nat 0%nat eq_refl ltac:(lia)); reflexivity).
assert (Egot : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
by (subst E; unfold adE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Ecell : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
by (subst E; unfold adE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold adss, A_reac_boxreg_addP. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold adregions. repeat apply Forall_cons; try apply Forall_nil.
    * (* the registry block *)
      unfold adR, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB 10%nat r E10) by lia.
      split; [lia|]. split; [lia|]. split.
      { intros o Ho. apply (apresent_writable SEGS). apply (proj1 (Hrpres (r + o) ltac:(lia))). }
      lazymatch goal with |- Forall _ ?l => let l' := eval vm_compute in l in change l with l' end.
      repeat apply Forall_cons; try apply Forall_nil.
      all: lazymatch goal with
      | |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 1 (SOff ?n 0))) =>
          let j := eval vm_compute in (n - 32)%nat in
          apply (chunk_ok_val SEGS E _ r off 1 (SOff n 0) (adtb bs off));
          [ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EW n j eq_refl ltac:(lia));
            unfold adextra; rewrite map_nth; cbn [adrowv app nth]; reflexivity
          | exact (ad_tb_rng bs off) | zside | exact (V1 off ltac:(lia)) ]
      | |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 4 (SOff ?n 0))) =>
          let j := eval vm_compute in (n - 32)%nat in
          apply (chunk_ok_val SEGS E _ r off 4 (SOff n 0) (ad4 bs off));
          [ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EW n j eq_refl ltac:(lia));
            unfold adextra; rewrite map_nth; cbn [adrowv app nth]; reflexivity
          | exact (ad_4_rng bs off) | zside | exact (V4 off ltac:(lia) ltac:(lia)) ]
      end.
    * (* the MAC *)
      unfold adP, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB 11%nat p E11) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      all: lazymatch goal with
      | |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 1 (SOff ?n 0))) =>
          let j := eval vm_compute in (n - 32)%nat in
          apply (chunk_ok_val SEGS E _ p off 1 (SOff n 0) (adtb M off));
          [ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EW n j eq_refl ltac:(lia));
            unfold adextra; rewrite map_nth; cbn [adrowv app nth]; reflexivity
          | exact (ad_tb_rng M off) | zside | exact (VM off ltac:(lia)) ]
      end.
    * (* the frame *)
      unfold stack_region, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite WS. lia.
    * (* the GOT word of the shadow cell *)
      unfold got_regionP, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite Ecell, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * (* the shadow cell *)
      unfold bcell_regionP, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Ecell) by (pose proof (pa_val_range (A_OBJ 12)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) ADSB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold ADSB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  + apply pairwise_disjoint_of_extents.
    unfold adregions, adR, adP, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 10%nat r E10) by lia. rewrite (VB 11%nat p E11) by lia.
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Ecell) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil C1 WS Hstk0 HcellR HgcD HgotR Hr4096 Hrceil Hrimg
      Hf4096 Hfceil Hflo Hfhi Hfimg Hrf.
    clear. intros. repeat split; lia.
  + unfold adfacts, adrowf, PTR. split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok app].
    split.
    { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp. change (2 ^ 4) with 16.
      revert Hslo Hshi H47 Hceil C1 WS Hstk0 Hal16. clear. intros. repeat split; lia. }
    split.
    { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E10, unsigned_lit_small by lia. change (2 ^ 4) with 16.
      revert Hr16 Hr4096 Hrceil C1. clear. intros. repeat split; lia. }
    split.
    { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E11, unsigned_lit_small by lia. change (2 ^ 3) with 8.
      revert Hf4096 Hfceil Hflo Hfhi Hp8 C1. clear. intros. repeat split; lia. }
    split.
    { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E32, unsigned_lit_small by (unfold ADSB; lia).
      rewrite Z.pow_0_r, Z.mod_1_r. lia. }
    repeat lazymatch goal with
    | |- True => exact I
    | |- afact_ok _ ?n _ /\ _ =>
        let j := eval vm_compute in (n - 32)%nat in
        split;
        [ first [ eapply ad_afb | eapply ad_afw ];
          rewrite (EW n j eq_refl ltac:(lia)); unfold adextra; rewrite map_nth; cbn [adrowv app nth]; reflexivity
        | ]
    end.
- unfold sh_ok, adSH. constructor; [|constructor; [|constructor]].
  + apply (shent_ok_of_range SEGS (w_H W) mem E ADBx 10 r 288 r 0 288 HRAr).
    * unfold ADBx. rewrite (U_atom E 32 ADSB E32) by (unfold ADSB; lia). reflexivity.
    * exact (U_atom E 10 r E10 ltac:(lia)).
    * lia.
    * lia.
    * intros x Hx. revert Hrapp Hx. clear. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg. intros. lia.
  + apply (shent_ok_of_range SEGS (w_H W) mem E ADBx 11 p 6 p 0 6 HRA).
    * unfold ADBx. rewrite (U_atom E 32 ADSB E32) by (unfold ADSB; lia). reflexivity.
    * exact (U_atom E 11 p E11 ltac:(lia)).
    * lia.
    * lia.
    * intros x Hx. revert Hfapp Hflo Hfhi Hx. clear. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg. intros. lia.
Qed.
(* The merge point of the six-byte scan of the MAC (0x81c64): the bytes that the loop left in
   a0 .. a4 become fresh atoms, 76 holding the byte the test looks at. *)
(* The regions once the prologue has saved ra and s0 .. s8 in the frame. *)
Definition adframe : YP09.region :=
YP09.mkRegion (Some 2%nat) (-80) 0 (-80) 0
[ YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0));
  YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0));
  YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
  YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
  YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0)) ].
Definition adregions2 : smem := [adR; adP; adframe; got_regionP; bcell_regionP 32].
Definition admz_P : nat -> bool := fun n => negb ((76 <=? n) && (n <=? 80))%nat.
Definition admz_E (Ex : env) (w76 w77 w78 w79 w80 : word) : env :=
ewset (ewset (ewset (ewset (ewset Ex 76 w76) 77 w77) 78 w78) 79 w79) 80 w80.
Definition admz_regs : list sv :=
[SLit 0; SOff 1 0; SOff 2 (-80); SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0;
 SOff 12 0; SOff 11 0; SOff 77 0; SOff 78 0; SOff 79 0; SOff 76 0; SOff 80 0;
 SOff 15 0; SOff 16 0; SOff 17 0; SOff 10 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 32 0;
 SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
Definition admz_facts : facts := mkFacts ((76%nat, mkAF 0 255 0) :: f_atoms adfacts) [] [].
Definition admz : sstate := mkSS 7448 admz_regs adregions2 None admz_facts.
Lemma admz_agree : forall Ex w76 w77 w78 w79 w80,
env_agree_pd admz_P PT Ex (admz_E Ex w76 w77 w78 w79 w80).
Proof.
intros Ex w76 w77 w78 w79 w80. split; [|reflexivity]. intros n Hn.
unfold admz_P in Hn. apply negb_true_iff, andb_false_iff in Hn.
assert (Hne : (n < 76 \/ 80 < n)%nat)
by (destruct Hn as [H|H]; [apply Nat.leb_gt in H; lia | apply Nat.leb_gt in H; lia]).
unfold admz_E. rewrite !ew_ewset_other by lia. reflexivity.
Qed.
Lemma admz_reabs : forall Ex ss msx w76 w77 w78 w79 w80,
st_ok SEGS Ex ss msx -> reabs_check admz_P ss admz_regs admz_facts = true ->
ss_mem ss = adregions2 ->
w77 = getr (ms_regs msx) 10 -> w78 = getr (ms_regs msx) 11 -> w79 = getr (ms_regs msx) 12 ->
w76 = getr (ms_regs msx) 13 -> w80 = getr (ms_regs msx) 14 ->
0 <= bv_unsigned w76 <= 255 ->
st_ok SEGS (admz_E Ex w76 w77 w78 w79 w80)
(mkSS (ss_pc ss) admz_regs adregions2 None admz_facts) msx.
Proof.
intros Ex ss msx w76 w77 w78 w79 w80 HS Hck Hmem Q77 Q78 Q79 Q76 Q80 Hr.
apply (st_ok_reabs SEGS admz_P Ex _ ss msx admz_regs adregions2 admz_facts HS
  (admz_agree Ex _ _ _ _ _) Hck).
- lazymatch goal with |- Forall ?f ?l => let l' := eval vm_compute in l in change l with l' end.
  subst w76 w77 w78 w79 w80.
  repeat (apply Forall_cons; [cbn [ew ewset Nat.eqb fst snd admz_E]; reflexivity|]). apply Forall_nil.
- lazymatch goal with |- Forall ?f ?l => let l' := eval vm_compute in l in change l with l' end.
  apply Forall_cons; [|apply Forall_nil].
  unfold afact_ok. cbn [af_lo af_hi af_al2 fst snd ew ewset Nat.eqb admz_E].
  rewrite Z.pow_0_r, Z.mod_1_r. lia.
- rewrite <- Hmem.
  apply (mem_ok_agree_pd SEGS admz_P PT Ex (admz_E Ex w76 w77 w78 w79 w80)
           (ms_mem msx) (ss_mem ss) (admz_agree Ex _ _ _ _ _)
           ltac:(rewrite Hmem; vm_compute; reflexivity)).
  exact (st_ok_mem_ok SEGS Ex ss msx HS).
Qed.
Lemma admz_other : forall Ex w76 w77 w78 w79 w80 n, (n < 76)%nat ->
ew (admz_E Ex w76 w77 w78 w79 w80) n = ew Ex n.
Proof. intros Ex w76 w77 w78 w79 w80 n Hn. unfold admz_E. rewrite !ew_ewset_other by lia. reflexivity. Qed.
Lemma admz_img : forall Ex w76 w77 w78 w79 w80,
img_env VAL A_LIM Ex -> img_env VAL A_LIM (admz_E Ex w76 w77 w78 w79 w80).
Proof.
intros Ex w76 w77 w78 w79 w80 HE a Ha. unfold admz_E.
rewrite !ew_ewset_other by (unfold A_TEXT in Ha; lia). apply HE. exact Ha.
Qed.
Lemma admz_shok : forall Ex w76 w77 w78 w79 w80 m,
sh_ok SEGS ADBx adSH Ex m -> sh_ok SEGS ADBx adSH (admz_E Ex w76 w77 w78 w79 w80) m.
Proof.
intros Ex w76 w77 w78 w79 w80 m H.
pose proof (admz_other Ex w76 w77 w78 w79 w80) as A.
unfold sh_ok, adSH in *.
apply Forall_forall. intros e He. rewrite Forall_forall in H. specialize (H e He).
unfold shent_ok, app_apart, U, ADBx in *.
cbn [sv_denot] in *. rewrite (A 32%nat ltac:(lia)) in *.
destruct He as [<- | [<- | []]]; cbn [she_m she_lo she_hi] in *;
[rewrite (A 10%nat ltac:(lia)) in * | rewrite (A 11%nat ltac:(lia)) in *]; exact H.
Qed.
Lemma admz_agree32 : forall Ex w76 w77 w78 w79 w80 (regs0 : bvmap 5 word) extra,
env_agree 32 (Ereg regs0 extra) Ex -> env_agree 32 (Ereg regs0 extra) (admz_E Ex w76 w77 w78 w79 w80).
Proof.
intros Ex w76 w77 w78 w79 w80 regs0 extra [H1 H2]. split; [|exact H2].
intros n Hn. rewrite (admz_other Ex w76 w77 w78 w79 w80 n ltac:(lia)). apply H1. exact Hn.
Qed.
(* The MAC object survives a run that writes only the frame. *)
Lemma ad_afobj_keep : forall (Wx : world SEGS) lyx Sx (m m' : word -> option byte) p0 lo hi,
afobj SEGS B lyx Sx Wx m p0 6 ->
(forall a : Z, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
   aview SEGS (w_H Wx) m' a = aview SEGS (w_H Wx) m a) ->
(forall x : Z, p0 <= x < p0 + 6 ->
   0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 64 /\ ~ (lo <= shadow_of_addr SHADOW_OFF x < hi)) ->
afobj SEGS B lyx Sx Wx m' p0 6.
Proof.
intros Wx lyx Sx m m' p0 lo hi (HF & H8 & HRA) HK HS.
split; [exact HF|]. split; [exact H8|].
intros x Hx. destruct (HRA x Hx) as (sb & Hsb & Hok). exists sb. split; [|exact Hok].
destruct (HS x Hx) as (Hr1 & Hr2). rewrite (HK _ Hr1 Hr2). exact Hsb.
Qed.
(* The two shadow entries the walk carries, at any state that holds the block and the MAC. *)
Lemma ad_shok : forall (Ex : env) (W0 : world SEGS) ly0 S0 m md0 r0 p0,
AR SEGS B ly0 S0 W0 m md0 -> In (r0, REG_SIZE) (ablocks B ly0 S0) ->
afobj SEGS B ly0 S0 W0 m p0 6 ->
ew Ex 32 = Z_to_bv 64 ADSB -> ew Ex 10 = Z_to_bv 64 r0 -> ew Ex 11 = Z_to_bv 64 p0 ->
0 <= r0 -> r0 + 288 <= alloc_ceiling -> in_app r0 288 ->
0 <= p0 -> p0 + 6 <= alloc_ceiling -> in_app p0 6 ->
sh_ok SEGS ADBx adSH Ex (mrestrict (w_H W0) m).
Proof.
intros Ex W0 ly0 S0 m md0 r0 p0 HAR0 Hin0 HFO0 H32 Hr10 Hp11 Hr0 Hrc Hrapp Hp0 Hpc Hpapp.
pose proof asan_consts as (C1 & _).
pose proof (range_addressable_of_block SEGS B LAWS ly0 S0 W0 m md0 r0 REG_SIZE r0 288 HAR0 Hin0
  ltac:(lia) ltac:(change (req_size REG_SIZE) with 288; lia)) as HRAr.
destruct HFO0 as (_ & _ & HRAp).
unfold sh_ok, adSH. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_range SEGS (w_H W0) m Ex ADBx 10 r0 288 r0 0 288 HRAr).
  + unfold ADBx. rewrite (U_atom Ex 32 ADSB H32) by (unfold ADSB; lia). reflexivity.
  + exact (U_atom Ex 10 r0 Hr10 ltac:(lia)).
  + lia.
  + lia.
  + intros x Hx. revert Hrapp Hx. clear. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg.
    intros. lia.
- apply (shent_ok_of_range SEGS (w_H W0) m Ex ADBx 11 p0 6 p0 0 6 HRAp).
  + unfold ADBx. rewrite (U_atom Ex 32 ADSB H32) by (unfold ADSB; lia). reflexivity.
  + exact (U_atom Ex 11 p0 Hp11 ltac:(lia)).
  + lia.
  + lia.
  + intros x Hx. revert Hpapp Hx. clear. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg.
    intros. lia.
Qed.
(* The value a sext.w leaves in a0. *)
Lemma ad_sext_val : forall E n v, ew E n = Z_to_bv 64 v -> - 2 ^ 31 <= v < 2 ^ 31 ->
sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 v.
Proof.
intros E n v H Hv.
assert (HU : U E (SOff n 0) = v mod 2 ^ 64).
{ rewrite U_SOff, H, Z.add_0_r, Z_to_bv_unsigned, zcanon_wrap. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia. }
rewrite denot_lit_U, U_SExt, HU. cbn [Z.of_N].
assert (A : v mod 2 ^ 64 mod 2 ^ 32 = v mod 2 ^ 32) by (Z.div_mod_to_equations; lia).
rewrite A.
assert (A2 : bv_swrap 32 (v mod 2 ^ 32) = v).
{ unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2 ^ 32).
  change (bv_half_modulus 32) with (2 ^ 31). Z.div_mod_to_equations; lia. }
rewrite A2, zcanon_wrap. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
apply Z.mod_mod. lia.
Qed.
(* The value a sext.w of an int leaves in a0. *)
Lemma ad_sextw0 : forall E n v, ew E n = Z_to_bv 64 v -> - 2 ^ 31 <= v < 2 ^ 31 ->
sv_denot E (SAluw ALU_ADD (SOff n 0) (SLit 0)) = Z_to_bv 64 v.
Proof.
intros E n v H Hv.
rewrite denot_lit_U, (U_of_S E (SAluw ALU_ADD (SOff n 0) (SLit 0))), S_SAluw, U_SOff, !U_SLit, H,
  Z_to_bv_unsigned.
cbn [zalu_raw]. rewrite ?Z.add_0_r.
assert (A1 : zcanon (bv_wrap 64 v) mod 2 ^ 32 = v mod 2 ^ 32).
{ unfold zcanon, bv_wrap, M64. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_mod by lia. Z.div_mod_to_equations; lia. }
rewrite A1. rewrite ?Z.add_0_r.
assert (A2 : bv_swrap 32 (v mod 2 ^ 32) = v).
{ unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2 ^ 32).
  change (bv_half_modulus 32) with (2 ^ 31). Z.div_mod_to_equations; lia. }
rewrite A2. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
Qed.
(* blez on a sign-extended 32-bit field. *)
Lemma ad_blez : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E (SExt true 32 (SOff n 0)))
= negb (0 <? bv_swrap 32 v).
Proof.
intros E n v H Hv. cbn [branch_taken]. unfold bv_lts.
change (bv_signed (sv_denot E (SExt true 32 (SOff n 0)))) with (Sg E (SExt true 32 (SOff n 0))).
change (bv_signed (sv_denot E (SLit 0))) with (Sg E (SLit 0)).
rewrite (ad_sg_sext E n v H Hv), S_of_U, U_SLit.
replace (zcanon 0) with 0 by reflexivity.
rewrite (swrap64_id 0) by (unfold half64; lia). reflexivity.
Qed.
(* The branch on a signed register against zero. *)
Lemma ad_bge0 : forall E n v, ew E n = Z_to_bv 64 v -> - 2 ^ 63 <= v < 2 ^ 63 ->
branch_taken BC_GE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = negb (v <? 0).
Proof.
intros E n v H Hv. cbn [branch_taken]. unfold bv_lts.
change (bv_signed (sv_denot E (SOff n 0))) with (Sg E (SOff n 0)).
change (bv_signed (sv_denot E (SLit 0))) with (Sg E (SLit 0)).
rewrite (ad_sg_off E n v H Hv), S_of_U, U_SLit.
replace (zcanon 0) with 0 by reflexivity.
rewrite (swrap64_id 0) by (unfold half64; lia). reflexivity.
Qed.
(* The shadow address of a field, as the code computes it. *)
Lemma ad_shaddr : forall E n m v w,
ew E n = Z_to_bv 64 v -> 0 <= v -> v + 280 < 2 ^ 64 ->
ew E m = Z_to_bv 64 w -> 0 <= w -> w + (v + 280) / 8 < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n 280) (SLit 3)) (SOff m 0))
= Z_to_bv 64 (w + (v + 280) / 8).
Proof.
intros E n m v w Hn Hv0 Hv1 Hm Hw0 Hw1.
assert (HU1 : U E (SOff n 280) = v + 280).
{ rewrite U_SOff, Hn, Z_to_bv_unsigned, zcanon_wrap. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small v (2 ^ 64)) by lia.
  apply Z.mod_small. lia. }
assert (HU3 : U E (SOff m 0) = w).
{ rewrite U_SOff, Hm, Z.add_0_r, Z_to_bv_unsigned, zcanon_wrap. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small w (2 ^ 64)) by lia.
  apply Z.mod_small. lia. }
assert (HU2 : U E (SAlu ALU_SRL (SOff n 280) (SLit 3)) = (v + 280) / 8).
{ rewrite U_SAlu, HU1, U_SLit. cbn [zalu_raw].
  replace (Z.land (zcanon 3) 63) with 3 by reflexivity.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  apply zcanon_id. unfold M64. Z.div_mod_to_equations. lia. }
rewrite denot_lit_U, U_SAlu, HU2, HU3. cbn [zalu_raw].
rewrite zcanon_id by (unfold M64; lia). f_equal. lia.
Qed.
(* A saved register in the frame, read out of the chunk the prologue left. *)
Lemma ad_frame_slot : forall Ex ssx (W0 : world SEGS) msx spv (od : Z) (n : nat),
st_ok_pi SEGS VAL Ex ssx (restrict (w_H W0) msx) ->
In adframe (ss_mem ssx) ->
bv_unsigned (ew Ex 2) = spv ->
In (YP09.mkChunk od (CVal 8 (SOff n 0))) (YP09.r_chunks adframe) ->
val_mem SEGS (mrestrict (w_H W0) (ms_mem msx)) (spv + od) 8 (bv_unsigned (ew Ex n)).
Proof.
intros Ex ssx W0 msx spv od n HS Hmem Hsp Hin.
assert (HR : region_ok SEGS Ex (ms_mem (restrict (w_H W0) msx)) adframe).
{ apply (mem_ok_region SEGS Ex _ (ss_mem (abs_ss VAL ssx)));
  [ exact (st_ok_mem_ok SEGS Ex (abs_ss VAL ssx) _ HS)
  | exact Hmem ]. }
cbn [ms_mem restrict mkst] in HR.
pose proof (field_of_region_any Ex (mrestrict (w_H W0) (ms_mem msx)) 2%nat spv
  (YP09.r_chunks adframe) (-80) 0 (-80) 0 od 8 (SOff n 0) HR Hsp Hin ltac:(cbn; lia)) as HV.
cbn [sv_denot] in HV. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in HV.
rewrite (Z.mod_small (bv_unsigned (ew Ex n)) (2 ^ (8 * Z.of_N 8))) in HV;
[ exact HV | pose proof (u64_range (ew Ex n)); cbn [Z.of_N]; lia ].
Qed.
(* The ten saved registers of the frame, as the two segment lemmas ask for them. *)
Lemma ad_frames : forall Ex ssx (W0 : world SEGS) msx (regs0 : bvmap 5 word),
st_ok_pi SEGS VAL Ex ssx (restrict (w_H W0) msx) ->
In adframe (ss_mem ssx) ->
bv_unsigned (ew Ex 2) = spZ regs0 ->
ew Ex 1 = getr regs0 1 -> ew Ex 8 = getr regs0 8 -> ew Ex 9 = getr regs0 9 ->
ew Ex 18 = getr regs0 18 -> ew Ex 19 = getr regs0 19 -> ew Ex 20 = getr regs0 20 ->
ew Ex 21 = getr regs0 21 -> ew Ex 22 = getr regs0 22 -> ew Ex 23 = getr regs0 23 ->
ew Ex 24 = getr regs0 24 ->
val_mem SEGS (mrestrict (w_H W0) (ms_mem msx)) (spZ regs0 - 8) 8 (bv_unsigned (getr regs0 1)) /\
val_mem SEGS (mrestrict (w_H W0) (ms_mem msx)) (spZ regs0 - 16) 8 (bv_unsigned (getr regs0 8)) /\
val_mem SEGS (mrestrict (w_H W0) (ms_mem msx)) (spZ regs0 - 24) 8 (bv_unsigned (getr regs0 9)) /\
val_mem SEGS (mrestrict (w_H W0) (ms_mem msx)) (spZ regs0 - 32) 8 (bv_unsigned (getr regs0 18)) /\
val_mem SEGS (mrestrict (w_H W0) (ms_mem msx)) (spZ regs0 - 40) 8 (bv_unsigned (getr regs0 19)) /\
val_mem SEGS (mrestrict (w_H W0) (ms_mem msx)) (spZ regs0 - 48) 8 (bv_unsigned (getr regs0 20)) /\
val_mem SEGS (mrestrict (w_H W0) (ms_mem msx)) (spZ regs0 - 56) 8 (bv_unsigned (getr regs0 21)) /\
val_mem SEGS (mrestrict (w_H W0) (ms_mem msx)) (spZ regs0 - 64) 8 (bv_unsigned (getr regs0 22)) /\
val_mem SEGS (mrestrict (w_H W0) (ms_mem msx)) (spZ regs0 - 72) 8 (bv_unsigned (getr regs0 23)) /\
val_mem SEGS (mrestrict (w_H W0) (ms_mem msx)) (spZ regs0 - 80) 8 (bv_unsigned (getr regs0 24)).
Proof.
intros Ex ssx W0 msx regs0 HS Hmem Hsp H1 H8 H9 H18 H19 H20 H21 H22 H23 H24.
repeat split.
- pose proof (ad_frame_slot Ex ssx W0 msx (spZ regs0) (-8) 1%nat HS Hmem Hsp
    ltac:(cbn [adframe YP09.r_chunks In]; auto 20)) as F;
  rewrite H1 in F; replace (spZ regs0 + -8) with (spZ regs0 - 8) in F by lia; exact F.
- pose proof (ad_frame_slot Ex ssx W0 msx (spZ regs0) (-16) 8%nat HS Hmem Hsp
    ltac:(cbn [adframe YP09.r_chunks In]; auto 20)) as F;
  rewrite H8 in F; replace (spZ regs0 + -16) with (spZ regs0 - 16) in F by lia; exact F.
- pose proof (ad_frame_slot Ex ssx W0 msx (spZ regs0) (-24) 9%nat HS Hmem Hsp
    ltac:(cbn [adframe YP09.r_chunks In]; auto 20)) as F;
  rewrite H9 in F; replace (spZ regs0 + -24) with (spZ regs0 - 24) in F by lia; exact F.
- pose proof (ad_frame_slot Ex ssx W0 msx (spZ regs0) (-32) 18%nat HS Hmem Hsp
    ltac:(cbn [adframe YP09.r_chunks In]; auto 20)) as F;
  rewrite H18 in F; replace (spZ regs0 + -32) with (spZ regs0 - 32) in F by lia; exact F.
- pose proof (ad_frame_slot Ex ssx W0 msx (spZ regs0) (-40) 19%nat HS Hmem Hsp
    ltac:(cbn [adframe YP09.r_chunks In]; auto 20)) as F;
  rewrite H19 in F; replace (spZ regs0 + -40) with (spZ regs0 - 40) in F by lia; exact F.
- pose proof (ad_frame_slot Ex ssx W0 msx (spZ regs0) (-48) 20%nat HS Hmem Hsp
    ltac:(cbn [adframe YP09.r_chunks In]; auto 20)) as F;
  rewrite H20 in F; replace (spZ regs0 + -48) with (spZ regs0 - 48) in F by lia; exact F.
- pose proof (ad_frame_slot Ex ssx W0 msx (spZ regs0) (-56) 21%nat HS Hmem Hsp
    ltac:(cbn [adframe YP09.r_chunks In]; auto 20)) as F;
  rewrite H21 in F; replace (spZ regs0 + -56) with (spZ regs0 - 56) in F by lia; exact F.
- pose proof (ad_frame_slot Ex ssx W0 msx (spZ regs0) (-64) 22%nat HS Hmem Hsp
    ltac:(cbn [adframe YP09.r_chunks In]; auto 20)) as F;
  rewrite H22 in F; replace (spZ regs0 + -64) with (spZ regs0 - 64) in F by lia; exact F.
- pose proof (ad_frame_slot Ex ssx W0 msx (spZ regs0) (-72) 23%nat HS Hmem Hsp
    ltac:(cbn [adframe YP09.r_chunks In]; auto 20)) as F;
  rewrite H23 in F; replace (spZ regs0 + -72) with (spZ regs0 - 72) in F by lia; exact F.
- pose proof (ad_frame_slot Ex ssx W0 msx (spZ regs0) (-80) 24%nat HS Hmem Hsp
    ltac:(cbn [adframe YP09.r_chunks In]; auto 20)) as F;
  rewrite H24 in F; replace (spZ regs0 + -80) with (spZ regs0 - 80) in F by lia; exact F.
Qed.
(* The MAC object survives a call whose journal keeps the frames. *)
Lemma ad_afobj_j : forall ly0 S0 (W0 : world SEGS) m md0 m' md' p0 STK1 sp1 k1,
ajournal SEGS B STK1 sp1 (@nil (Z * Z)) ly0 S0 W0 m md0 (@nil (Z * Z)) ly0 S0 W0 m' md' k1 ->
afobj SEGS B ly0 S0 W0 m p0 6 -> afobj SEGS B ly0 S0 W0 m' p0 6.
Proof.
intros ly0 S0 W0 m md0 m' md' p0 STK1 sp1 k1 HJ
  ((cid & pos & Hinf & Hcid & Hfal & Hflo & Hfhi) & H8 & HRA).
split; [exists cid, pos; repeat split; assumption|]. split; [exact H8|].
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K4 & _).
intros x Hx. destruct (HRA x Hx) as (sb & Hsb & Hok). exists sb. split; [|exact Hok].
assert (Hfb : fs_frame_bytes cid = 64 * 2 ^ cid)
by (unfold fs_frame_bytes; rewrite Z.shiftl_mul_pow2 by lia; lia).
assert (Hpos : 0 < 2 ^ cid) by (apply Z.pow_pos_nonneg; lia).
rewrite (K4 cid pos (shadow_of_addr SHADOW_OFF x) Hinf); [exact Hsb | | intros Hfp; exact (inFP_nil _ Hfp)].
right. unfold in_zr, shadow_addr, shadow_of_addr, SHADOW_OFF. cbn [fst snd].
assert (Hd : frame_addr ly0 cid pos / 8 <= x / 8 < frame_addr ly0 cid pos / 8 + 64 * 2 ^ cid / 8).
{ rewrite Hfb in Hfhi. split.
  - apply Z.div_le_mono; lia.
  - replace (64 * 2 ^ cid / 8) with (8 * 2 ^ cid)
      by (replace (64 * 2 ^ cid) with (8 * 2 ^ cid * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
    assert (Hfa : frame_addr ly0 cid pos = 8 * (frame_addr ly0 cid pos / 8))
      by (Z.div_mod_to_equations; lia).
    assert (Hxb : x < frame_addr ly0 cid pos + 64 * 2 ^ cid) by lia.
    Z.div_mod_to_equations; lia. }
rewrite Hfb. lia.
Qed.
(* What a run of plain instructions keeps: every byte outside the frame window. *)
Lemma ad_kept : forall E rs (W : world SEGS) (m m' : word -> option byte) lo hi,
frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
(forall b wlo whi a, In (b, wlo, whi) (windows rs) ->
   base_val E b + wlo <= a < base_val E b + whi -> lo <= a < hi) ->
forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof.
intros E rs W m m' lo hi HF Hw a Ha Hn.
exact (kept_of_frame E rs (w_H W) m m' (fun x => lo <= x < hi) HF Hw a Ha Hn).
Qed.
Ltac ad_win Usp :=
let Hin := fresh "Hwin" in let Hr := fresh "Hrng" in let Eq := fresh "Heq" in
intros bb wlo whi aa Hin Hr; cbn [windows map YP09.r_base YP09.r_wlo YP09.r_whi stack_region
  got_regionP bcell_regionP] in Hin;
repeat (destruct Hin as [Eq | Hin];
  [injection Eq as <- <- <-; cbn [base_val ew ewset Nat.eqb] in Hr;
   rewrite ?ew_havoc_old in Hr by (cbv; lia); rewrite ?Usp in Hr; lia |]);
destruct Hin.
(* An atom value, read in the environment the engine has grown. *)
Ltac ad_at Hx nn Hn :=
lazymatch goal with HS : st_ok_pi _ _ ?Ex _ _ |- _ =>
  assert (Hn : ew Ex nn = _)
  by (cbn [ew ewset Nat.eqb]; rewrite ?ew_havoc_old by (cbv; lia); exact Hx)
end.
(* One run of plain instructions: carry the bytes outside the frame window forward. *)
Ltac ad_upd KEEPo Uspx Wx lo hi :=
lazymatch type of KEEPo with
| forall a : Z, _ -> _ -> aview _ _ ?m1 a = aview _ _ ?m0 a =>
  lazymatch goal with
  | HFx : frame_of ?Ex ?rs (mrestrict _ m1) (mrestrict _ ?m2) |- _ =>
    let KEEPn := fresh "KEEPn" in
    let aa := fresh "a" in let Ha := fresh "Ha" in let Hw := fresh "Hw" in
    assert (KEEPn : forall a : Z, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
      aview SEGS (w_H Wx) m2 a = aview SEGS (w_H Wx) m0 a)
    by (intros aa Ha Hw;
        rewrite (ad_kept Ex rs Wx m1 m2 lo hi HFx ltac:(ad_win Uspx) aa Ha Hw);
        apply KEEPo; assumption);
    clear KEEPo;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end;
    repeat match goal with H : mem_grows _ _ |- _ => clear H end;
    rename KEEPn into KEEPo
  end
end.
(* A register's value as the symbolic state spells it, without the normalisation of prreg. *)
Ltac prreg_raw HSx r Hr :=
lazymatch type of HSx with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HSx) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in
  change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
end.
(* The epilogue with the value of a0 left to the caller of the tactic. *)
Ltac ad_ret_t HSx HJx E1x Hrax HAEx zz bss :=
let R1 := fresh "R1" in let mt := fresh "mat" in
prreg HSx (1%bv : bv 5) R1;
eapply (RET _ _ _ _ _ _ HSx eq_refl ltac:(vm_compute; reflexivity)); intros mt;
unfold treac_boxreg_add_post, apost_base; cbn [ms_regs ms_mem];
do 5 eexists;
split; [rewrite R1, E1x; unfold YK0s.ret_ok in Hrax; rewrite Hrax; reflexivity|];
split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJx|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ _ _ HSx);
        [eapply env_agree_trans;
         [exact HAEx
         | split; [intros nn Hnn; rewrite ?ew_ewset_other by lia;
                   rewrite ?ew_havoc_old by lia; reflexivity | reflexivity]]
        | vm_compute; reflexivity]|];
split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [apply Permutation_refl|];
exists zz, bss.
(* The epilogue: the walk is at the return slot, a0 holds zz and the block holds bss. *)
Ltac ad_ret HSx HJx E1x Hrax HAEx zz bss :=
let R1 := fresh "R1" in let R10 := fresh "R10" in let mt := fresh "mat" in
prreg HSx (1%bv : bv 5) R1; prreg HSx (10%bv : bv 5) R10;
eapply (RET _ _ _ _ _ _ HSx eq_refl ltac:(vm_compute; reflexivity)); intros mt;
unfold treac_boxreg_add_post, apost_base; cbn [ms_regs ms_mem];
do 5 eexists;
split; [rewrite R1, E1x; unfold YK0s.ret_ok in Hrax; rewrite Hrax; reflexivity|];
split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJx|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ _ _ HSx);
        [eapply env_agree_trans;
         [exact HAEx
         | split; [intros nn Hnn; rewrite ?ew_ewset_other by lia;
                   rewrite ?ew_havoc_old by lia; reflexivity | reflexivity]]
        | vm_compute; reflexivity]|];
split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [apply Permutation_refl|];
exists zz, bss;
split; [rewrite R10; unfold w64; first [reflexivity | apply bv_eq; vm_compute; reflexivity]|].
Ltac ad_atom HEx nn jj :=
rewrite HEx; unfold adE; rewrite Eimg_low by (unfold A_TEXT; lia);
rewrite (ad_ewn _ _ nn jj eq_refl); unfold adextra, adrowv; cbn [map app nth]; reflexivity.
Ltac ad_ewat Hx := cbn [ew ewset Nat.eqb]; rewrite ?ew_havoc_old by (cbv; lia); exact Hx.
Ltac ad_ag Eb HN :=
lazymatch goal with HS : st_ok_pi _ _ ?Ex _ _ |- _ =>
  assert (HN : forall n : nat, (n < 76)%nat -> ew Ex n = ew Eb n)
  by (let nn := fresh "nn" in let Hnn := fresh "Hnn" in
      intros nn Hnn; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; reflexivity)
end.
(* A leaf of the six-byte scan: re-abstract a0 .. a4 and hand the rest of the walk to CONT. *)
Ltac ad_mz_leaf Mx EMx jj vvv HS2 E76 :=
let R13 := fresh "R13" in let EMa := fresh "EMa" in let HR := fresh "HR" in
ad_at EMx jj EMa;
lazymatch goal with
| HS : st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?Wx) ?msx) |- _ =>
  prreg HS (13%bv : bv 5) R13;
  assert (HR : getr (ms_regs (restrict (w_H Wx) msx)) 13 = Z_to_bv 64 vvv)
    by (cbn [ms_regs restrict]; rewrite R13; exact EMa);
  pose proof (admz_reabs Ex (abs_ss VAL ss) (restrict (w_H Wx) msx)
     (getr (ms_regs (restrict (w_H Wx) msx)) 13) (getr (ms_regs (restrict (w_H Wx) msx)) 10)
     (getr (ms_regs (restrict (w_H Wx) msx)) 11) (getr (ms_regs (restrict (w_H Wx) msx)) 12)
     (getr (ms_regs (restrict (w_H Wx) msx)) 14) HS
     ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
     eq_refl eq_refl eq_refl eq_refl eq_refl
     ltac:(rewrite HR, unsigned_lit_small by (pose proof (adtb_range Mx 0); pose proof (adtb_range Mx 1);
             pose proof (adtb_range Mx 2); pose proof (adtb_range Mx 3); pose proof (adtb_range Mx 4);
             pose proof (adtb_range Mx 5); lia);
           pose proof (adtb_range Mx 0); pose proof (adtb_range Mx 1); pose proof (adtb_range Mx 2);
           pose proof (adtb_range Mx 3); pose proof (adtb_range Mx 4); pose proof (adtb_range Mx 5); lia)) as HS2;
  change (mkSS (ss_pc (abs_ss VAL ss)) admz_regs adregions2 None admz_facts) with (abs_ss VAL admz) in HS2;
  assert (E76 : ew (admz_E Ex (getr (ms_regs (restrict (w_H Wx) msx)) 13)
                       (getr (ms_regs (restrict (w_H Wx) msx)) 10)
                       (getr (ms_regs (restrict (w_H Wx) msx)) 11)
                       (getr (ms_regs (restrict (w_H Wx) msx)) 12)
                       (getr (ms_regs (restrict (w_H Wx) msx)) 14)) 76 = Z_to_bv 64 vvv)
    by (cbn [ew ewset Nat.eqb admz_E]; exact HR)
end.

(* ====================================================================== *)
(* The new-row tail (0x81d90 .. return).                                  *)
(* The symbolic state at 0x81d90: the atoms 0..31 are the entry registers *)
(* of the function (so the frame reloads give them back), 32 is the       *)
(* shadow base and 33..50 hold the values of the registers the code has   *)
(* already clobbered.                                                     *)
Definition nxextra (regsT : bvmap 5 word) : list word :=
[Z_to_bv 64 ADSB;
 getr regsT 13; getr regsT 14; getr regsT 15; getr regsT 16; getr regsT 17;
 getr regsT 20; getr regsT 21; getr regsT 28; getr regsT 29; getr regsT 30; getr regsT 31;
 getr regsT 5; getr regsT 6; getr regsT 7;
 getr regsT 1; getr regsT 10; getr regsT 11; getr regsT 12].
Definition nxE (regs regsT : bvmap 5 word) : env := Eimg (Ereg regs (nxextra regsT)).
Definition nxregs (nl : Z) : list sv :=
[SLit 0; SOff 47 0; SOff 2 (-80); SOff 3 0; SOff 4 0; SOff 44 0; SOff 45 0; SOff 46 0;
 SOff 12 0; SOff 11 0; SOff 48 0; SOff 49 0; SOff 50 0; SOff 33 0; SOff 34 0; SOff 35 0;
 SOff 36 0; SOff 37 0; SOff 10 0; SOff 10 280; SOff 38 0; SOff 39 0; SOff 32 0;
 SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 280) (SLit 3)) (SOff 32 0);
 SLit nl; SOff 25 0; SOff 26 0; SOff 27 0; SOff 40 0; SOff 41 0; SOff 42 0; SOff 43 0].
Definition nxfr : YP09.region :=
YP09.mkRegion (Some 2%nat) (-80) 0 (-80) 0
[YP09.mkChunk (-8) (CVal 8 (SOff 1 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
 YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
 YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
 YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
 YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0))].
Definition nxfacts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, PTR 4); (32%nat, mkAF ADSB ADSB 0)] [] [].
Definition nxss (nl : Z) : sstate := mkSS 7748 (nxregs nl) [nxfr] None nxfacts.
Definition nxFR (W : world SEGS) (memT : word -> option byte) (sp0 : Z) (regs : bvmap 5 word) : Prop :=
val_mem SEGS (mrestrict (w_H W) memT) (sp0 - 8) 8 (bv_unsigned (getr regs 1)) /\
val_mem SEGS (mrestrict (w_H W) memT) (sp0 - 16) 8 (bv_unsigned (getr regs 8)) /\
val_mem SEGS (mrestrict (w_H W) memT) (sp0 - 24) 8 (bv_unsigned (getr regs 9)) /\
val_mem SEGS (mrestrict (w_H W) memT) (sp0 - 32) 8 (bv_unsigned (getr regs 18)) /\
val_mem SEGS (mrestrict (w_H W) memT) (sp0 - 40) 8 (bv_unsigned (getr regs 19)) /\
val_mem SEGS (mrestrict (w_H W) memT) (sp0 - 48) 8 (bv_unsigned (getr regs 20)) /\
val_mem SEGS (mrestrict (w_H W) memT) (sp0 - 56) 8 (bv_unsigned (getr regs 21)) /\
val_mem SEGS (mrestrict (w_H W) memT) (sp0 - 64) 8 (bv_unsigned (getr regs 22)) /\
val_mem SEGS (mrestrict (w_H W) memT) (sp0 - 72) 8 (bv_unsigned (getr regs 23)) /\
val_mem SEGS (mrestrict (w_H W) memT) (sp0 - 80) 8 (bv_unsigned (getr regs 24)).

Lemma nx_shv : forall E n c v,
ew E n = Z_to_bv 64 v -> 0 <= v -> v + c < 2 ^ 64 -> 0 <= c -> ew E 32 = Z_to_bv 64 ADSB ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff 32 0)) = Z_to_bv 64 (ADSB + (v + c) / 8).
Proof.
intros E n c v Hn H0 H1 Hc H32.
assert (HX : U E (SOff n c) = v + c).
{ rewrite U_SOff, Hn, unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. }
assert (H3 : U E (SLit 3) = 3) by (rewrite U_SLit; reflexivity).
assert (HD : 0 <= (v + c) / 8 < 2 ^ 64) by (split; [apply Z.div_pos; lia | apply Z.le_lt_trans with (v + c); [apply Z.div_le_upper_bound; lia | lia]]).
assert (HS : U E (SAlu ALU_SRL (SOff n c) (SLit 3)) = (v + c) / 8).
{ rewrite U_SAlu, HX, H3. cbn [zalu_raw]. change (Z.land 3 63) with 3.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. apply zcanon_id. unfold M64. lia. }
assert (HB : U E (SOff 32 0) = ADSB).
{ rewrite U_SOff, H32, Z.add_0_r, unsigned_lit_small by (unfold ADSB; lia).
  apply zcanon_id. unfold M64, ADSB. lia. }
change (Z_to_bv 64 (ADSB + (v + c) / 8)) with (sv_denot E (SLit (ADSB + (v + c) / 8))).
apply U_inj. rewrite U_SAlu, HS, HB, U_SLit. cbn [zalu_raw]. f_equal. lia.
Qed.

Lemma nx_off0w : forall E n (w : word), ew E n = w -> sv_denot E (SOff n 0) = w.
Proof. intros E n w H. cbn [sv_denot]. rewrite H, Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma nx_offc : forall E n c v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof. intros E n c v H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by lia. reflexivity. Qed.

Ltac nx_sr := lazymatch goal with |- context [sr_get ?rr ?ii] => let v := eval vm_compute in (sr_get rr ii) in change (sr_get rr ii) with v end.

Lemma nx_bltz : forall E n v, ew E n = Z_to_bv 64 v -> - 2 ^ 63 <= v < 2 ^ 63 ->
branch_taken BC_LT (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (v <? 0).
Proof.
intros E n v H Hv. cbn [branch_taken sv_denot]. unfold bv_lts.
rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite !Boxreg.signed_lit by lia. reflexivity.
Qed.

Lemma nx_aview_present : forall (H : word -> bool) (m : word -> option byte) a,
apresent H m a -> aview SEGS H m a <> None.
Proof. intros H m a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. cbv beta. rewrite Hh, Hb. discriminate. Qed.
Lemma nx_sh8 : forall y, 0 <= y -> (ADSB + y / 8) / 8 * 8 = ADSB + y / 64 * 8.
Proof.
intros y Hy. unfold ADSB. replace 2147450880 with (268431360 * 8) by reflexivity.
rewrite Z.div_add_l by lia. rewrite (Z.div_div y 8 8) by lia. change (8 * 8) with 64. lia.
Qed.
Lemma nx_frame_al64 : forall ly cid pos, layout_ok ly -> 0 <= cid -> frame_addr ly cid pos mod 64 = 0.
Proof.
intros ly cid pos HL Hcid. unfold frame_addr, fs_frame_off, fs_frame_bytes, kFakeFramesOff, kStackSizeLog.
pose proof (lo_F_al ly HL) as HF. unfold page_aligned in HF.
rewrite !Z.shiftl_mul_pow2 by lia.
apply Z.mod_divide; [lia|].
repeat apply Z.divide_add_r.
- apply Z.divide_trans with 4096; [exists 64; reflexivity | apply Z.mod_divide; [lia | exact HF]].
- exists 64. reflexivity.
- exists 512. reflexivity.
- apply Z.divide_mul_r. exists 16384. reflexivity.
- apply Z.divide_mul_r. apply Z.divide_factor_l.
Qed.
Lemma nx_hull_frame : forall ly S (W : world SEGS) mem md cid pos x n,
AR SEGS B ly S W mem md -> In (cid, pos) (frames S) -> 0 <= cid ->
frame_addr ly cid pos <= x -> x + n <= frame_addr ly cid pos + fs_frame_bytes cid -> 0 < n ->
shadow_hull_vis (aview SEGS (w_H W) mem) x n.
Proof.
intros ly S W mem md cid pos x n HAR Hin Hcid Hlo Hhi Hn.
destruct (al_frames _ _ LAWS ly S W mem md cid pos HAR Hin) as (_ & _ & _ & Hsh).
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (Hfa4096 & Hfaceil & _).
pose proof HAR as (HARm & _ & _ & _ & _).
assert (HLo : layout_ok ly) by (destruct HARm; assumption).
pose proof (nx_frame_al64 ly cid pos HLo Hcid) as Hfa64.
assert (HF64 : fs_frame_bytes cid mod 64 = 0).
{ unfold fs_frame_bytes. rewrite Z.shiftl_mul_pow2 by lia.
  pose proof (Z.pow_pos_nonneg 2 cid ltac:(lia) ltac:(lia)).
  rewrite Z.mul_comm. apply Z_mod_mult. }
pose proof (fs_frame_bytes_pos cid Hcid) as HFp.
intros s Hs. unfold shadow_addr, SHADOW_OFF in Hs.
change 2147450880 with ADSB in Hs.
rewrite (nx_sh8 x ltac:(lia)), (nx_sh8 (x + n - 1) ltac:(lia)) in Hs.
specialize (Hsh (s - (ADSB + frame_addr ly cid pos / 8))).
unfold shadow_addr, SHADOW_OFF in Hsh. change 2147450880 with ADSB in Hsh.
replace (ADSB + frame_addr ly cid pos / 8 + (s - (ADSB + frame_addr ly cid pos / 8))) with s in Hsh by lia.
apply nx_aview_present. apply Hsh.
revert Hs Hlo Hhi Hfa64 HF64 HFp Hn Hfa4096 Hfaceil.
generalize (frame_addr ly cid pos) as fa. generalize (fs_frame_bytes cid) as F. intros F fa.
intros. Z.div_mod_to_equations. lia.
Qed.

Lemma nx_ad4_n : forall bs, length bs = 288%nat -> 0 <= Boxreg.bx_n bs <= 4 -> ad4 bs 280 = Boxreg.bx_n bs.
Proof.
intros bs HL Hn. rewrite (ad_bx_n bs HL) in *. pose proof (ad4_range bs 280) as HR.
unfold bv_swrap, bv_wrap in *. change (bv_half_modulus 32) with (2 ^ 31) in *.
change (bv_modulus 32) with (2 ^ 32) in *. Z.div_mod_to_equations. lia.
Qed.

Lemma nx_chunk_view : forall E ss (ms : machine_state) (H : word -> bool) rg (n : nat) o (w : N) e v,
st_ok_pi SEGS VAL E ss (restrict H ms) -> In rg (ss_mem ss) -> YP09.r_base rg = Some n ->
In (YP09.mkChunk o (CVal w e)) (YP09.r_chunks rg) -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
forall j, 0 <= j < Z.of_N w ->
aview SEGS H (ms_mem ms) (bv_unsigned (ew E n) + o + j) = Some ((v / 2 ^ (8 * j)) mod 256).
Proof.
intros E ss ms H rg n o w e v HS Hin Hb Hc He Hv j Hj.
pose proof (st_ok_mem_ok SEGS E (abs_ss VAL ss) (restrict H ms) HS) as (_ & HR & _).
unfold abs_ss, setpc in HR. cbn [ss_mem] in HR.
rewrite Forall_forall in HR. specialize (HR rg Hin). destruct HR as (_ & _ & _ & HC).
rewrite Forall_forall in HC. specialize (HC _ Hc j ltac:(cbn [YP09.c_len YP09.c_val cv_len]; lia)).
destruct HC as (b & Hb1 & Hb2). cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hb1, Hb2.
injection Hb1 as <-. rewrite Hb in Hb2. cbn [base_val] in Hb2.
unfold aview. cbn [ms_mem restrict] in Hb2. rewrite Hb2. cbn [option_map]. f_equal.
unfold YP09.byte_of_word. rewrite He, !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 8) with 256.
rewrite (Z.mod_small v) by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
Lemma nx_entry : forall ly S (W : world SEGS) (regs regsT : bvmap 5 word) mem md memT mdT (r p k nl : Z),
ajournal SEGS B REAC_BOXREG_ADD_STK (spZ regs) [(r, r + REG_SIZE)] ly S W mem md [] ly S W memT mdT 0 ->
In (r, REG_SIZE) (ablocks B ly S) ->
getr regs 10 = w64 r -> getr regs 11 = w64 p -> getr regs 12 = w64 k ->
getr regsT 2 = w64 (spZ regs - 80) ->
getr regsT 3 = getr regs 3 -> getr regsT 4 = getr regs 4 ->
getr regsT 8 = w64 k -> getr regsT 9 = w64 p -> getr regsT 18 = w64 r ->
getr regsT 19 = w64 (r + 280) -> getr regsT 22 = w64 ADSB ->
getr regsT 23 = w64 (ADSB + (r + 280) / 8) -> getr regsT 24 = w64 nl ->
getr regsT 25 = getr regs 25 -> getr regsT 26 = getr regs 26 -> getr regsT 27 = getr regs 27 ->
nxFR W memT (spZ regs) regs ->
st_ok_pi SEGS VAL (nxE regs regsT) (nxss nl)
  (restrict (w_H W) (mkst regsT (Z_to_bv 64 (BASE + 7748)) memT (seg_rom SEGS))).
Proof.
intros ly S W regs regsT mem md memT mdT r p k nl HJ Hin H10 H11 H12
  Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q22 Q23 Q24 Q25 Q26 Q27 HFR.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOXREG_ADD_STK = 8320) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W memT mdT r REG_SIZE HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hrapp & Hrpres & _ & _).
change (req_size REG_SIZE) with 288 in Hrceil, Hrapp, Hrpres.
rewrite restrict_mkst_fx.
set (E := nxE regs regsT).
assert (EL : forall (n : nat) (rr : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn Hrr. subst E. unfold nxE. rewrite Eimg_low by (unfold A_TEXT; lia).
  apply (ew_Ereg_nat regs _ n rr Hrr). }
assert (EW : forall n j, n = (32 + j)%nat -> (j < 19)%nat ->
  ew E n = nth j (nxextra regsT) (Z_to_bv 64 0)).
{ intros n j -> Hj. subst E. unfold nxE. rewrite Eimg_low by (unfold A_TEXT; lia).
  apply ew_Ereg_extra. }
assert (E2 : ew E 2 = getr regs 2) by (apply (EL 2%nat 2%bv); [lia | reflexivity]).
assert (E10 : ew E 10 = Z_to_bv 64 r)
  by (rewrite (EL 10%nat 10%bv ltac:(lia) eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 ADSB) by (rewrite (EW 32%nat 0%nat eq_refl ltac:(lia)); reflexivity).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Hr64 : 0 <= r < 2 ^ 64) by lia.
unfold nxss. apply pa_entry_st_ok_full.
- (* regs_ok *)
  apply regs_ok_by_cases. intros rr Hr. cbv [YP01.all_regs In] in Hr.
  repeat (destruct Hr as [<-|Hr]); [..|destruct Hr].
  all: lazymatch goal with |- getr ?rt ?rg = sv_denot ?EE (sr_get ?sr ?rg) =>
         let v := eval vm_compute in (sr_get sr rg) in change (sr_get sr rg) with v end.
  all: lazymatch goal with
  | |- _ = sv_denot _ (SLit 0) => rewrite getr_zero; reflexivity
  | |- _ = sv_denot _ (SOff ?n 0) =>
      let big := eval vm_compute in (Nat.leb 33 n) in
      lazymatch big with
      | true => let j := eval vm_compute in (n - 32)%nat in
                cbn [sv_denot]; rewrite (EW n j eq_refl ltac:(lia));
                unfold nxextra; cbn [nth]; rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned
      | false => idtac
      end
  | _ => idtac
  end.
  all: first
  [ cbn [sv_denot]; rewrite E2, Q2; unfold w64, spZ; f_equal; lia
  | cbn [sv_denot]; rewrite (EL 3%nat 3%bv ltac:(lia) eq_refl), Q3, Z.add_0_r;
    symmetry; apply Z_to_bv_bv_unsigned
  | cbn [sv_denot]; rewrite (EL 4%nat 4%bv ltac:(lia) eq_refl), Q4, Z.add_0_r;
    symmetry; apply Z_to_bv_bv_unsigned
  | cbn [sv_denot]; rewrite (EL 12%nat 12%bv ltac:(lia) eq_refl), H12, Q8, Z.add_0_r;
    unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
  | cbn [sv_denot]; rewrite (EL 11%nat 11%bv ltac:(lia) eq_refl), H11, Q9, Z.add_0_r;
    unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
  | cbn [sv_denot]; rewrite E10, Q18, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
  | cbn [sv_denot]; rewrite E10, Q19, unsigned_lit_small by lia; reflexivity
  | cbn [sv_denot]; rewrite E32, Q22, Z.add_0_r; unfold w64, ADSB;
    rewrite Z_to_bv_bv_unsigned; reflexivity
  | cbn [sv_denot]; rewrite (EL 25%nat 25%bv ltac:(lia) eq_refl), Q25, Z.add_0_r;
    symmetry; apply Z_to_bv_bv_unsigned
  | cbn [sv_denot]; rewrite (EL 26%nat 26%bv ltac:(lia) eq_refl), Q26, Z.add_0_r;
    symmetry; apply Z_to_bv_bv_unsigned
  | cbn [sv_denot]; rewrite (EL 27%nat 27%bv ltac:(lia) eq_refl), Q27, Z.add_0_r;
    symmetry; apply Z_to_bv_bv_unsigned
  | cbn [sv_denot]; exact Q24
  | rewrite (nx_shv E 10%nat 280 r E10 ltac:(lia) ltac:(lia) ltac:(lia) E32); exact Q23 ].
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
  unfold nxfr, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  cbn [base_val]. rewrite Usp.
  split; [lia|]. split; [lia|]. split.
  { intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite WS. lia. }
  destruct HFR as (F1 & F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23 & F24).
  repeat apply Forall_cons; try apply Forall_nil.
  all: lazymatch goal with
  | |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?n 0))) =>
      let rr := eval vm_compute in (Z_to_bv 5 (Z.of_nat n)) in
      apply (chunk_ok_val SEGS E _ (spZ regs) off 8 (SOff n 0) (bv_unsigned (getr regs rr)));
      [ cbn [sv_denot]; rewrite (EL n rr ltac:(lia) ltac:(vm_compute; reflexivity)), Z.add_0_r; reflexivity
      | pose proof (bv_unsigned_in_range 64 (getr regs rr)) as HR;
        change (bv_modulus 64) with (2 ^ 64) in HR; cbn [Z.of_N]; lia
      | cbn [Z.of_N]; lia
      | cbn [N.to_nat]; replace (spZ regs + off) with (spZ regs - (- off)) by lia;
        cbn [Z.opp]; assumption ]
  end.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- unfold nxfacts, PTR. split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok].
  split.
  { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp. change (2 ^ 4) with 16.
    revert Hslo Hshi H47 Hceil C1 WS Hstk0 Hal16. clear. intros. repeat split; lia. }
  split.
  { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E10, unsigned_lit_small by lia.
    change (2 ^ 4) with 16. revert Hr16 Hr4096 Hrceil C1. clear. intros. repeat split; lia. }
  split; [|exact I].
  { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E32, unsigned_lit_small by (unfold ADSB; lia).
    rewrite Z.pow_0_r, Z.mod_1_r. lia. }
Qed.

Lemma ad_newrow : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md
  (regsT : bvmap 5 word) memT mdT (r p k : Z) (bs M : list byte),
ajournal SEGS B REAC_BOXREG_ADD_STK (spZ regs) [(r, r + REG_SIZE)] ly S W mem md [] ly S W memT mdT 0 ->
In (r, REG_SIZE) (ablocks B ly S) ->
getr regs 10 = w64 r -> getr regs 11 = w64 p -> getr regs 12 = w64 k ->
YK0s.ret_ok (getr regs 1) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regsT 2 = w64 (spZ regs - 80) ->
getr regsT 3 = getr regs 3 -> getr regsT 4 = getr regs 4 ->
getr regsT 8 = w64 k -> getr regsT 9 = w64 p -> getr regsT 18 = w64 r ->
getr regsT 19 = w64 (r + 280) -> getr regsT 22 = w64 ADSB ->
getr regsT 23 = w64 (ADSB + (r + 280) / 8) -> getr regsT 24 = w64 (Boxreg.bx_n bs) ->
getr regsT 25 = getr regs 25 -> getr regsT 26 = getr regs 26 -> getr regsT 27 = getr regs 27 ->
nxFR W memT (spZ regs) regs ->
(forall i, 0 <= i < REG_SIZE -> aview SEGS (w_H W) memT (r + i) = Some (adtb bs i)) ->
(forall i, 0 <= i < 6 -> aview SEGS (w_H W) memT (p + i) = Some (adtb M i)) ->
afobj SEGS B ly S W memT p 6 -> length M = 6%nat ->
Boxreg.boxreg_inv bs -> 0 <= Boxreg.bx_n bs <= 4 -> - 2 ^ 31 <= k < 2 ^ 31 ->
reac_boxreg_add_c.add_width_ok k (Boxreg.bx_fabric bs) -> M <> Boxreg.zero6 ->
reac_boxreg_add_c.add_none_held bs M -> reac_boxreg_add_c.add_none_unbound bs k ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (BASE + 7748)) memT (seg_rom SEGS)) mdT)
  (treac_boxreg_add_post regs ly S W mem md r k bs M).
Proof.
intros ly S W regs mem md regsT memT mdT r p k bs M HJ Hin H10 H11 H12 Hra Hgp Htp
  Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q22 Q23 Q24 Q25 Q26 Q27 HFR Hbs HMv HFO HML Hinv Hn Hk
  HWOK HMnz HNH HNU.
pose proof (pa_segs_low) as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOXREG_ADD_STK = 8320) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W memT mdT r REG_SIZE HAR Hin)
  as (Hr16 & Hr4096 & Hrceil & Hrapp & Hrpres & _ & _).
change (req_size REG_SIZE) with 288 in Hrceil, Hrapp, Hrpres.
set (nrw := Boxreg.bx_n bs) in *.
assert (Hcase : nrw = 0 \/ nrw = 1 \/ nrw = 2 \/ nrw = 3 \/ nrw = 4) by lia.
pose proof Hinv as Hinv0.
destruct Hinv as ((HLbs & HB1 & HB2 & HB3 & HB4 & HB5 & HB6) & HB7).
destruct Hcase as [HN|[HN|[HN|[HN|HN]]]]; rewrite HN in Q24.

all: pose proof (nx_entry ly S W regs regsT mem md memT mdT r p k _ HJ Hin H10 H11 H12
  Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q22 Q23 Q24 Q25 Q26 Q27 HFR) as HS.
all: assert (HAE : env_agree 32 (Ereg regs (nxextra regsT)) (nxE regs regsT))
  by (unfold nxE; split; [intros nq Hnq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
all: assert (HEI : img_env VAL A_LIM (nxE regs regsT)) by (unfold nxE; apply Eimg_env).
all: assert (SHOK : sh_ok SEGS ADBx [] (nxE regs regsT) (mrestrict (w_H W) memT)) by constructor.
all: assert (E2 : ew (nxE regs regsT) 2 = getr regs 2)
  by (unfold nxE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
all: assert (Usp : bv_unsigned (ew (nxE regs regsT) 2) = spZ regs) by (rewrite E2; reflexivity).
all: assert (EL3 : forall (n : nat) (rr : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned rr ->
  ew (nxE regs regsT) n = getr regs rr)
  by (intros nq rr Hnq Hrr; unfold nxE; rewrite Eimg_low by (unfold A_TEXT; lia);
      apply (ew_Ereg_nat regs _ nq rr Hrr)).
all: assert (E10 : ew (nxE regs regsT) 10 = Z_to_bv 64 r)
  by (rewrite (EL3 10%nat 10%bv ltac:(lia) eq_refl); exact H10).
all: assert (E12 : ew (nxE regs regsT) 12 = Z_to_bv 64 k)
  by (rewrite (EL3 12%nat 12%bv ltac:(lia) eq_refl); exact H12).
all: assert (E32x : ew (nxE regs regsT) 32 = Z_to_bv 64 ADSB)
  by (unfold nxE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs (nxextra regsT) 0)).
all: set (Ex := nxE regs regsT) in *.
all: clearbody Ex.
all: assert (KEEP0 : forall a : Z, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 80 <= a < spZ regs) ->
  aview SEGS (w_H W) memT a = aview SEGS (w_H W) memT a) by (intros; reflexivity).
(* 0x81d90 .. the call of lowest_free_base *)
all: paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
all: ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
all: lazymatch goal with |- SRr _ _ (mkCfg ?msx ?mdx) _ =>
  assert (R2 : getr (ms_regs msx) 2 = sv_denot Ex (SOff 2 (-80)))
    by (rewrite (st_ok_restrict_reg SEGS (w_H W) Ex _ msx 2%bv HS); f_equal; vm_compute; reflexivity);
  assert (R1 : getr (ms_regs msx) 1 = Z_to_bv 64 (BASE + 7760))
    by (rewrite (st_ok_restrict_reg SEGS (w_H W) Ex _ msx 1%bv HS); nx_sr;
        apply (codeptr_val _ 7760 HEI));
  assert (R3 : getr (ms_regs msx) 3 = w64 (as_gp B))
    by (rewrite (st_ok_restrict_reg SEGS (w_H W) Ex _ msx 3%bv HS); nx_sr;
        rewrite (nx_off0w Ex 3%nat (getr regs 3%bv) (EL3 3%nat 3%bv ltac:(lia) eq_refl)); exact Hgp);
  assert (R4 : getr (ms_regs msx) 4 = w64 (as_tp B))
    by (rewrite (st_ok_restrict_reg SEGS (w_H W) Ex _ msx 4%bv HS); nx_sr;
        rewrite (nx_off0w Ex 4%nat (getr regs 4%bv) (EL3 4%nat 4%bv ltac:(lia) eq_refl)); exact Htp);
  assert (R10 : getr (ms_regs msx) 10 = w64 r)
    by (rewrite (st_ok_restrict_reg SEGS (w_H W) Ex _ msx 10%bv HS); nx_sr;
        rewrite (nx_off0w Ex 10%nat _ E10); reflexivity);
  assert (R11 : getr (ms_regs msx) 11 = w64 k)
    by (rewrite (st_ok_restrict_reg SEGS (w_H W) Ex _ msx 11%bv HS); nx_sr;
        rewrite (nx_off0w Ex 12%nat _ E12); reflexivity);
  assert (R8 : getr (ms_regs msx) 8 = w64 k)
    by (rewrite (st_ok_restrict_reg SEGS (w_H W) Ex _ msx 8%bv HS); nx_sr;
        rewrite (nx_off0w Ex 12%nat _ E12); reflexivity);
  assert (HBY : forall i, 0 <= i < REG_SIZE ->
    aview SEGS (w_H W) (ms_mem msx) (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0))))
    by (intros i Hi; change REG_SIZE with 288 in Hi; rewrite KEEP0 by lia; exact (Hbs i Hi))
end.
(* lowest_free_base (r, k) *)
all: eapply SRr_bind;
[ lazymatch goal with |- SRr _ _ (mkCfg ?msx ?mdx) _ =>
  eapply (aj_call SEGS B LAWS Hsegs W Ex _ msx REAC_BOXREG_ADD_STK (spZ regs) [(r, r + REG_SIZE)]
    ly S W mem md [] ly S mdx 0 LowestFreeBase.LOWEST_FREE_BASE_STK [] 0 (-80) (ew Ex 2) _ []
    (fun ly2 S2 W2 regs2 mem2 md2 => ly2 = ly /\ S2 = S /\ W2 = W /\
       exists z, getr regs2 10 = w64 z /\ lowest_free_base_c.lowest_free bs k z)
    HS ltac:(vm_compute; reflexivity) HJ R2 eq_refl Usp ltac:(reflexivity) ltac:(lia)
    ltac:(unfold LowestFreeBase.LOWEST_FREE_BASE_STK, ESTACK; lia)
    ltac:(unfold LowestFreeBase.LOWEST_FREE_BASE_STK, ESTACK; rewrite WS; lia)
    R3 R4 eq_refl ltac:(rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity])
    ltac:(rewrite R1; rewrite unsigned_lit_small by (pose proof (pa_B_ok (L := box_listing)) as HB0; lia);
          pose proof (pa_B_ok (L := box_listing)) as HB0; lia));
  [ (* achain *) unfold achain; left; split;
    [ unfold reac_boxreg_add_c.add_width_ok in HWOK;
      left; unfold s0Z; rewrite R8; unfold w64; rewrite unsigned_lit_small by lia; lia
    | reflexivity ]
  | (* the callee *) intros HPRE;
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rgs ?pc ?mm _) ?mdx) _ =>
      change pc with (Z_to_bv 64 (SIGMA BS_lowest_free_base)) end;
    rewrite pa_sigma_lowest_free_base;
    eapply SRr_mono;
    [ exact (LFBC ly S W _ _ _ [] r k bs HPRE R10 R11
        ltac:(unfold reac_boxreg_add_c.add_width_ok in HWOK; lia) Hin HLbs HBY HB1 HB2 HB3) | ];
    cbv beta; intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (-> & -> & -> & z & Hz10 & Hzlf));
    exists ly, S, regs2, mem2, md2;
    split; [reflexivity|]; split; [exact HJ2|]; split; [exact HP2|];
    split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
    exists z; split; [exact Hz10 | exact Hzlf]
  | (* FP1 *) intros a (rg & [] & _) ]
  end
| ].
all: intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJout & HJin & HP1 & (-> & -> & -> & z & Hz10 & Hzlf)).
all: pose proof HJin as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N2 & _ & N4 & _ & _ & _ & _ & _).
all: pose proof HFO as ((cid & pos & Hfin & Hcid & Hfal & Hflo & Hfhi) & Hp8 & HRA).
all: assert (HFS8 : fs_frame_bytes cid mod 8 = 0)
  by (unfold fs_frame_bytes; rewrite Z.shiftl_mul_pow2 by lia;
      pose proof (Z.pow_pos_nonneg 2 cid ltac:(lia) ltac:(lia));
      replace (64 * 2 ^ cid) with (8 * 2 ^ cid * 8) by lia; apply Z_mod_mult).
all: assert (HSHC : forall x, frame_addr ly cid pos <= x < frame_addr ly cid pos + fs_frame_bytes cid ->
  in_zr (SHADOW_OFF + x / 8) (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8))
  by (intros x Hx; unfold in_zr, shadow_addr; cbn [fst snd];
      pose proof (fs_frame_bytes_pos cid ltac:(lia));
      split; [apply Z.add_le_mono_l; apply Z.div_le_mono; lia|];
      assert (HQ : x / 8 < frame_addr ly cid pos / 8 + fs_frame_bytes cid / 8)
        by (revert Hfal HFS8 Hx; generalize (frame_addr ly cid pos) as fa; generalize (fs_frame_bytes cid) as fsz;
            intros fsz fa Hfa Hfs Hx; Z.div_mod_to_equations; lia);
      lia).
all: destruct (frames_bounds SEGS B LAWS ly S W memT mdT cid pos HAR Hfin) as (Hfa4096 & Hfaceil & Hfaapp).
all: assert (HPB : 4096 <= p /\ p + 6 <= alloc_ceiling)
  by (pose proof (fs_frame_bytes_pos cid ltac:(lia)); lia).
all: assert (BY1 : forall i, 0 <= i < 288 -> aview SEGS (w_H W) mem2 (r + i) = Some (adtb bs i))
  by (intros i Hi; rewrite (N2 r REG_SIZE i Hin Hin ltac:(change (req_size REG_SIZE) with 288; lia)
        ltac:(intros (rg & [] & _))); change REG_SIZE with 288 in HBY;
      rewrite (HBY i ltac:(lia)); reflexivity).
all: assert (MB1 : forall i, 0 <= i < 6 -> aview SEGS (w_H W) mem2 (p + i) = Some (adtb M i))
  by (intros i Hi; rewrite (N4 cid pos (p + i) Hfin ltac:(left; unfold in_zr, frame_rng; cbn [fst snd]; lia)
        ltac:(intros (rg & [] & _)));
      rewrite KEEP0 by lia; exact (HMv i Hi)).
all: assert (RA1 : range_addressable (aview SEGS (w_H W) mem2) SHADOW_OFF p 6)
  by (intros x Hx; unfold shadow_of_addr;
      rewrite (N4 cid pos (SHADOW_OFF + x / 8) Hfin ltac:(right; apply HSHC; lia) ltac:(intros (rg & [] & _)));
      assert (Hq : 8 * (x / 8) <= x /\ 0 <= x / 8)
        by (split; [Z.div_mod_to_equations; lia | apply Z.div_pos; lia]);
      rewrite KEEP0 by (unfold SHADOW_OFF; lia); exact (HRA x Hx)).
(* back at 0x81d9c *)
all: jafter_call_keep_pi HS 64%nat regs2 (mrestrict (w_H W) mem2) HP1 [0]%nat HS2.
all: match type of HS2 with ?tq -> _ =>
  assert (HRK : tq);
  [ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_nil];
    eapply (region_kept_stack_sub SEGS B); [exact HJin | exact HJout | exact Usp | lia | lia | lia | lia | lia]
  | specialize (HS2 HRK); clear HRK ] end.
all: clear HS.
all: rewrite <- restrict_mkst_fx in HS2.
all: rename HS2 into HS.
all: rewrite R1.
all: remember (havoc Ex 64 (map (getr regs2) CLOB)) as E1 eqn:HE1 in HS.
all: assert (HEI1 : img_env VAL A_LIM E1) by (rewrite HE1; apply img_env_havoc; [exact HEI | cbv; lia]).
all: assert (OLD1 : forall n, (n < 64)%nat -> ew E1 n = ew Ex n) by (intros nq Hnq; rewrite HE1; apply ew_havoc_old; lia).
all: assert (E68 : ew E1 68 = Z_to_bv 64 z)
  by (rewrite HE1; cbn [havoc ew Nat.ltb Nat.leb Nat.sub CLOB map nth]; exact Hz10).
all: assert (HAE1 : env_agree 32 (Ereg regs (nxextra regsT)) E1)
  by (rewrite HE1; apply env_agree_havoc_ge; [lia | exact HAE]).
all: clear HE1.
all: assert (Usp1 : bv_unsigned (ew E1 2) = spZ regs) by (rewrite OLD1 by lia; exact Usp).
all: assert (SHOK1 : sh_ok SEGS ADBx [] E1 (mrestrict (w_H W) mem2)) by constructor.
all: assert (E1a : ew E1 1 = getr regs 1) by (rewrite OLD1 by lia; exact (EL3 1%nat 1%bv ltac:(lia) eq_refl)).
all: assert (Hzrng : - 2 ^ 63 <= z < 2 ^ 63)
  by (destruct Hzlf as [(-> & _) | (Hz0 & Hzf & _)]; [lia|];
      pose proof (Boxreg.rd4_range bs 284) as HF4; unfold Boxreg.bx_fabric in Hzf; lia).
all: lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
all: paj_run_tok RUN HS HJout SHOK1 ADspan; [awr_ok_tac; exact Usp1 |].
all: assert (KEEP1 : forall a : Z, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 80 <= a < spZ regs) ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem2 a) by (intros; reflexivity).
all: ad_upd KEEP1 Usp1 W (spZ regs - 80) (spZ regs).
(* 0x81da0: bltz a0 *)
all: psrr_branch_tok RUN BR HS SHOK1 ADspan;
[ (* lowest_free_base returned -1: return -1 *)
  rewrite (nx_bltz E1 68 z E68 Hzrng) in Hc; apply Z.ltb_lt in Hc;
  assert (HzM : z = -1) by (destruct Hzlf as [(-> & _) | (Hz0 & _)]; lia);
  paj_run_tok RUN HS HJout SHOK1 ADspan; [awr_ok_tac; exact Usp1 |];
  ad_upd KEEP1 Usp1 W (spZ regs - 80) (spZ regs);
  ad_ret HS HJout E1a Hra HAE1 (-1) bs;
  split;
  [ right; right; right; left;
    split; [exact HWOK|]; split; [exact HMnz|]; split; [exact HNH|]; split; [exact HNU|];
    split; [right; rewrite <- HzM; exact Hzlf|]; split; reflexivity
  | intros i Hi; change REG_SIZE with 288 in Hi; rewrite KEEP1 by lia; exact (BY1 i Hi) ]
| ].
(* lowest_free_base returned a base z >= 0 *)
all: rewrite (nx_bltz E1 68 z E68 Hzrng) in Hc.
all: apply Z.ltb_ge in Hc.
all: assert (Hzf : z + k <= Boxreg.bx_fabric bs /\ 0 <= z)
  by (destruct Hzlf as [(Hm & _) | (Hz0 & Hzf2 & _)]; [lia | lia]).
all: assert (Hzb : 0 <= z <= 38)
  by (unfold Boxreg.boxreg_B2 in HB2; unfold reac_boxreg_add_c.add_width_ok in HWOK; lia).
all: paj_run_tok RUN HS HJout SHOK1 ADspan; [awr_ok_tac; exact Usp1 |].
all: ad_upd KEEP1 Usp1 W (spZ regs - 80) (spZ regs).

(* __asan_memset (r + 56 n, 0, 56) *)
all: lazymatch goal with |- SRr _ _ (mkCfg ?msx ?mdx) _ =>
  assert (M1 : getr (ms_regs msx) 1 = Z_to_bv 64 (BASE + 7804))
    by (rewrite (st_ok_restrict_reg SEGS (w_H W) E1 _ msx 1%bv HS); nx_sr; apply (codeptr_val _ 7804 HEI1));
  assert (M2 : spZ (ms_regs msx) = spZ regs + -80)
    by (unfold spZ at 1; rewrite (st_ok_restrict_reg SEGS (w_H W) E1 _ msx 2%bv HS); nx_sr;
        cbn [sv_denot]; rewrite Usp1, unsigned_lit_small by lia; reflexivity);
  assert (M3 : getr (ms_regs msx) 3 = w64 (as_gp B))
    by (rewrite (st_ok_restrict_reg SEGS (w_H W) E1 _ msx 3%bv HS); nx_sr;
        rewrite (nx_off0w E1 3%nat (getr regs 3%bv) ltac:(rewrite OLD1 by lia; apply (EL3 3%nat 3%bv); [lia|reflexivity])); exact Hgp);
  assert (M4 : getr (ms_regs msx) 4 = w64 (as_tp B))
    by (rewrite (st_ok_restrict_reg SEGS (w_H W) E1 _ msx 4%bv HS); nx_sr;
        rewrite (nx_off0w E1 4%nat (getr regs 4%bv) ltac:(rewrite OLD1 by lia; apply (EL3 4%nat 4%bv); [lia|reflexivity])); exact Htp);
  assert (M10 : getr (ms_regs msx) 10 = w64 (r + 56 * nrw))
    by (rewrite (st_ok_restrict_reg SEGS (w_H W) E1 _ msx 10%bv HS); nx_sr;
        rewrite (nx_offc E1 10%nat _ r ltac:(rewrite OLD1 by lia; exact E10) ltac:(lia));
        unfold w64; f_equal; lia);
  assert (M11 : getr (ms_regs msx) 11 = w64 0)
    by (rewrite (st_ok_restrict_reg SEGS (w_H W) E1 _ msx 11%bv HS); nx_sr; reflexivity);
  assert (M12 : getr (ms_regs msx) 12 = w64 56)
    by (rewrite (st_ok_restrict_reg SEGS (w_H W) E1 _ msx 12%bv HS); nx_sr; reflexivity)
end.
all: pmkst HS.
all: lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply SRr_bind;
[ eapply (aj_intrin_at SEGS B LAWS Hsegs OSet (SIGMA BS___asan_memset) AMEMSET W rg mm
    REAC_BOXREG_ADD_STK (spZ regs) [(r, r + REG_SIZE)] ly S W mem md [] ly S _ 0
    (r + 56 * nrw) 0 56 (-80) _ HJout M10 M11 M12 ltac:(lia) ltac:(lia) ltac:(lia) M2
    ltac:(reflexivity) ltac:(lia) ltac:(unfold ESTACK; rewrite WS; lia) M3 M4 eq_refl
    ltac:(rewrite M1; apply ret_ok_codeptr_v; [lia | reflexivity]));
  [ intros a Ha; split;
    [ right; left; split;
      [ exists (r, r + REG_SIZE); split; [left; reflexivity | cbn [fst snd]; change REG_SIZE with 288; lia]
      | exists r, REG_SIZE; split; [exact Hin | change (req_size REG_SIZE) with 288; lia] ]
    | unfold ESTACK; lia ]
  | eapply (amem_range_of_block SEGS B LAWS ly S W _ _ r REG_SIZE _ _ (proj1 HJout) Hin);
    change (req_size REG_SIZE) with 288; lia
  | eapply (range_addressable_of_block SEGS B LAWS ly S W _ _ r REG_SIZE _ _ (proj1 HJout) Hin);
    change (req_size REG_SIZE) with 288; lia
  | intros _; eapply (shadow_hull_vis_of_block SEGS B LAWS ly S W _ _ r REG_SIZE _ _ (proj1 HJout) Hin);
    change (req_size REG_SIZE) with 288; lia
  | exact I ]
| ] end.
all: cbv beta; intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & _ & Heff3 & Hfr3 & _).
all: pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres3 & _).
all: pose proof (sep_block_frame SEGS B LAWS ly S W memT mdT r REG_SIZE cid pos HAR Hin Hfin) as Hrf.
all: unfold zdisjoint in Hrf; cbn [fst snd] in Hrf; change (req_size REG_SIZE) with 288 in Hrf.
all: assert (BY3 : forall i, 0 <= i < 288 -> ~ (56 * nrw <= i < 56 * nrw + 56) ->
  aview SEGS (w_H W) mem3 (r + i) = Some (adtb bs i))
  by (intros i Hi Hni; rewrite Hfr3 by (unfold ESTACK; lia); rewrite KEEP1 by lia; exact (BY1 i Hi)).
all: assert (Z3 : forall i, 0 <= i < 56 -> aview SEGS (w_H W) mem3 (r + 56 * nrw + i) = Some 0)
  by (intros i Hi; rewrite (Heff3 i Hi); reflexivity).
all: assert (MB3 : forall i, 0 <= i < 6 -> aview SEGS (w_H W) mem3 (p + i) = Some (adtb M i))
  by (intros i Hi; rewrite Hfr3 by (unfold ESTACK; lia); rewrite KEEP1 by lia; exact (MB1 i Hi)).
all: assert (RA3 : range_addressable (aview SEGS (w_H W) mem3) SHADOW_OFF p 6)
  by (intros x Hx; unfold shadow_of_addr;
      assert (Hq : 8 * (x / 8) <= x /\ 0 <= x / 8)
        by (split; [Z.div_mod_to_equations; lia | apply Z.div_pos; lia]);
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hrapp;
      rewrite Hfr3 by (unfold ESTACK, SHADOW_OFF; lia); rewrite KEEP1 by (unfold SHADOW_OFF; lia);
      exact (RA1 x Hx)).
(* back at 0x81dc8 *)
all: jafter_call_keep_pi HS 80%nat regs3 (mrestrict (w_H W) mem3) HP3 [0]%nat HS3.
all: match type of HS3 with ?tq -> _ =>
  assert (HRK : tq);
  [ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_nil];
    split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp1; intros a Ha;
    [ apply (mbyte_of_aview SEGS); apply Hfr3; [lia | lia | unfold ESTACK; lia]
    | intros _; apply (apresent_writable SEGS); apply HJpres3; lia ]
  | specialize (HS3 HRK); clear HRK ] end.
all: clear HS.
all: rewrite <- restrict_mkst_fx in HS3.
all: rename HS3 into HS.
all: rewrite M1.
all: remember (havoc E1 80 (map (getr regs3) CLOB)) as Ev2 eqn:HE2 in HS.
all: assert (HEI2' : img_env VAL A_LIM Ev2) by (rewrite HE2; apply img_env_havoc; [exact HEI1 | cbv; lia]).
all: assert (OLD2 : forall n, (n < 80)%nat -> ew Ev2 n = ew E1 n) by (intros nq Hnq; rewrite HE2; apply ew_havoc_old; lia).
all: assert (HAE2 : env_agree 32 (Ereg regs (nxextra regsT)) Ev2)
  by (rewrite HE2; apply env_agree_havoc_ge; [lia | exact HAE1]).
all: clear HE2.
all: assert (Usp2 : bv_unsigned (ew Ev2 2) = spZ regs) by (rewrite OLD2 by lia; exact Usp1).
all: assert (SHOK2 : sh_ok SEGS ADBx [] Ev2 (mrestrict (w_H W) mem3)) by constructor.
all: lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
all: paj_run_tok RUN HS HJ3 SHOK2 ADspan; [awr_ok_tac; exact Usp2 |].
all: assert (KEEP3 : forall a : Z, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 80 <= a < spZ regs) ->
  aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem3 a) by (intros; reflexivity).
all: ad_upd KEEP3 Usp2 W (spZ regs - 80) (spZ regs).
(* __asan_memcpy (r + 56 n, p, 6) *)
all: lazymatch goal with |- SRr _ _ (mkCfg ?msx ?mdx) _ =>
  assert (C1r : getr (ms_regs msx) 1 = Z_to_bv 64 (BASE + 7820))
    by (rewrite (st_ok_restrict_reg SEGS (w_H W) Ev2 _ msx 1%bv HS); nx_sr; apply (codeptr_val _ 7820 HEI2'));
  assert (C2r : spZ (ms_regs msx) = spZ regs + -80)
    by (unfold spZ at 1; rewrite (st_ok_restrict_reg SEGS (w_H W) Ev2 _ msx 2%bv HS); nx_sr;
        cbn [sv_denot]; rewrite Usp2, unsigned_lit_small by lia; reflexivity);
  assert (C3r : getr (ms_regs msx) 3 = w64 (as_gp B))
    by (rewrite (st_ok_restrict_reg SEGS (w_H W) Ev2 _ msx 3%bv HS); nx_sr;
        rewrite (nx_off0w Ev2 3%nat (getr regs 3%bv) ltac:(rewrite OLD2, OLD1 by lia; apply (EL3 3%nat 3%bv); [lia|reflexivity])); exact Hgp);
  assert (C4r : getr (ms_regs msx) 4 = w64 (as_tp B))
    by (rewrite (st_ok_restrict_reg SEGS (w_H W) Ev2 _ msx 4%bv HS); nx_sr;
        rewrite (nx_off0w Ev2 4%nat (getr regs 4%bv) ltac:(rewrite OLD2, OLD1 by lia; apply (EL3 4%nat 4%bv); [lia|reflexivity])); exact Htp);
  assert (C10r : getr (ms_regs msx) 10 = w64 (r + 56 * nrw))
    by (rewrite (st_ok_restrict_reg SEGS (w_H W) Ev2 _ msx 10%bv HS); nx_sr;
        rewrite (nx_offc Ev2 10%nat _ r ltac:(rewrite OLD2, OLD1 by lia; exact E10) ltac:(lia));
        unfold w64; f_equal; lia);
  assert (C11r : getr (ms_regs msx) 11 = w64 p)
    by (rewrite (st_ok_restrict_reg SEGS (w_H W) Ev2 _ msx 11%bv HS); nx_sr;
        rewrite (nx_off0w Ev2 11%nat (Z_to_bv 64 p)
          ltac:(rewrite OLD2, OLD1 by lia; rewrite (EL3 11%nat 11%bv ltac:(lia) eq_refl); exact H11)); reflexivity);
  assert (C12r : getr (ms_regs msx) 12 = w64 6)
    by (rewrite (st_ok_restrict_reg SEGS (w_H W) Ev2 _ msx 12%bv HS); nx_sr; reflexivity)
end.
all: pose proof (fs_frame_bytes_pos cid ltac:(lia)) as HFpos.
all: pmkst HS.
all: lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply SRr_bind;
[ eapply (aj_intrin_at SEGS B LAWS Hsegs OCpy (SIGMA BS___asan_memcpy) AMEMCPY W rg mm
    REAC_BOXREG_ADD_STK (spZ regs) [(r, r + REG_SIZE)] ly S W mem md [] ly S _ 0
    (r + 56 * nrw) p 6 (-80) _ HJ3 C10r C11r C12r ltac:(lia) ltac:(lia) ltac:(lia) C2r
    ltac:(reflexivity) ltac:(lia) ltac:(unfold ESTACK; rewrite WS; lia) C3r C4r eq_refl
    ltac:(rewrite C1r; apply ret_ok_codeptr_v; [lia | reflexivity]));
  [ intros a Ha; split;
    [ right; left; split;
      [ exists (r, r + REG_SIZE); split; [left; reflexivity | cbn [fst snd]; change REG_SIZE with 288; lia]
      | exists r, REG_SIZE; split; [exact Hin | change (req_size REG_SIZE) with 288; lia] ]
    | unfold ESTACK; lia ]
  | eapply (amem_range_of_block SEGS B LAWS ly S W _ _ r REG_SIZE _ _ (proj1 HJ3) Hin);
    change (req_size REG_SIZE) with 288; lia
  | eapply (range_addressable_of_block SEGS B LAWS ly S W _ _ r REG_SIZE _ _ (proj1 HJ3) Hin);
    change (req_size REG_SIZE) with 288; lia
  | intros _; eapply (shadow_hull_vis_of_block SEGS B LAWS ly S W _ _ r REG_SIZE _ _ (proj1 HJ3) Hin);
    change (req_size REG_SIZE) with 288; lia
  | split; [lia|]; split; [lia|]; split;
    [ intros a Ha; split;
      [ replace a with (p + (a - p)) by lia; rewrite KEEP3 by lia; rewrite MB3 by lia; discriminate
      | rewrite C2r; unfold ESTACK; lia ]
    |]; split; [lia|]; split;
    [ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfaapp; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; lia
    |]; split;
    [ intros x Hx; unfold shadow_of_addr;
      assert (Hq : 8 * (x / 8) <= x /\ 0 <= x / 8)
        by (split; [Z.div_mod_to_equations; lia | apply Z.div_pos; lia]);
      rewrite KEEP3 by (unfold SHADOW_OFF; lia); exact (RA3 x Hx)
    | intros _; exact (nx_hull_frame ly S W _ _ cid pos p 6 (proj1 HJ3) Hfin Hcid Hflo Hfhi ltac:(lia)) ] ]
| ] end.
all: cbv beta; intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & _ & Heff4 & Hfr4 & _).
all: pose proof HJ4 as (HAR4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres4 & _).
all: destruct (al_blocks _ _ LAWS ly S W mem4 _ r REG_SIZE HAR4 Hin) as (_ & _ & _ & _ & Hrpres4 & _ & _).
all: change (req_size REG_SIZE) with 288 in Hrpres4.
all: assert (BY4 : forall i, 0 <= i < 288 -> ~ (56 * nrw <= i < 56 * nrw + 56) ->
  aview SEGS (w_H W) mem4 (r + i) = Some (adtb bs i))
  by (intros i Hi Hni; rewrite Hfr4 by (unfold ESTACK; lia); rewrite KEEP3 by lia; exact (BY3 i Hi Hni)).
all: assert (Z4 : forall i, 6 <= i < 56 -> aview SEGS (w_H W) mem4 (r + 56 * nrw + i) = Some 0)
  by (intros i Hi; rewrite Hfr4 by (unfold ESTACK; lia); rewrite KEEP3 by lia; exact (Z3 i ltac:(lia))).
all: assert (MAC4 : forall i, 0 <= i < 6 -> aview SEGS (w_H W) mem4 (r + 56 * nrw + i) = Some (adtb M i))
  by (intros i Hi; rewrite (Heff4 i Hi); rewrite KEEP3 by lia; exact (MB3 i Hi)).
(* back at 0x81dd8 *)
all: jafter_call_keep_pi HS 96%nat regs4 (mrestrict (w_H W) mem4) HP4 [0]%nat HS4.
all: match type of HS4 with ?tq -> _ =>
  assert (HRK : tq);
  [ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_nil];
    split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp2; intros a Ha;
    [ apply (mbyte_of_aview SEGS); apply Hfr4; [lia | lia | unfold ESTACK; lia]
    | intros _; apply (apresent_writable SEGS); apply HJpres4; lia ]
  | specialize (HS4 HRK); clear HRK ] end.
all: clear HS.
all: rewrite <- restrict_mkst_fx in HS4.
all: rename HS4 into HS.
all: rewrite C1r.
all: remember (havoc Ev2 96 (map (getr regs4) CLOB)) as Ev3 eqn:HE3 in HS.
all: assert (OLD3 : forall n, (n < 64)%nat -> ew Ev3 n = ew Ex n)
  by (intros nq Hnq; rewrite HE3, ew_havoc_old, OLD2, OLD1 by lia; reflexivity).
all: assert (HAE3 : env_agree 32 (Ereg regs (nxextra regsT)) Ev3)
  by (rewrite HE3; apply env_agree_havoc_ge; [lia | exact HAE2]).
all: assert (E68' : ew Ev3 68 = Z_to_bv 64 z) by (rewrite HE3, ew_havoc_old, OLD2 by lia; exact E68).
all: assert (HEI3' : img_env VAL A_LIM Ev3) by (rewrite HE3; apply img_env_havoc; [exact HEI2' | cbv; lia]).
all: clear HE3.
all: assert (Usp3 : bv_unsigned (ew Ev3 2) = spZ regs) by (rewrite OLD3 by lia; exact Usp).
all: assert (E3a : ew Ev3 1 = getr regs 1) by (rewrite OLD3 by lia; exact (EL3 1%nat 1%bv ltac:(lia) eq_refl)).
all: assert (Ur : bv_unsigned (ew Ev3 10) = r) by (rewrite OLD3, E10 by lia; apply unsigned_lit_small; lia).
all: assert (E10' : ew Ev3 10 = Z_to_bv 64 r) by (rewrite OLD3 by lia; exact E10).
all: assert (E12' : ew Ev3 12 = Z_to_bv 64 k) by (rewrite OLD3 by lia; exact E12).
all: assert (E32' : ew Ev3 32 = Z_to_bv 64 ADSB) by (rewrite OLD3 by lia; exact E32x).

(* the two windows of the block the code still writes: n at r + 280 and base/nch at r + 56 n + 8 *)
all: assert (HN4 : ad4 bs 280 = nrw) by (apply nx_ad4_n; [exact HLbs | lia]).
all: assert (V280 : val_mem SEGS (mrestrict (w_H W) mem4) (r + 280) 4 nrw)
  by (rewrite <- HN4; unfold ad4; apply ad_val4; rewrite <- ?Z.add_assoc; apply BY4; lia).
all: lazymatch type of HN with _ = ?nl =>
  pose proof (st_ok_pi_add_region Ev3 _ _
    (YP09.mkRegion (Some 10%nat) 280 284 280 284 [YP09.mkChunk 280 (CVal 4 (SLit nl))]) HS
    ltac:(vm_compute; reflexivity)) as HSa
end.
all: match type of HSa with ?tq -> _ =>
  assert (HRK : tq);
  [ unfold region_ok; cbn [ms_mem restrict mkst YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
    rewrite Ur; split; [lia|]; split; [lia|]; split;
    [ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Hrpres4 (r + o) ltac:(lia)))
    | apply Forall_cons; [|apply Forall_nil];
      apply (chunk_ok_val SEGS Ev3 _ r 280 4 (SLit _) nrw); [cbn [sv_denot]; rewrite HN; reflexivity | cbn; lia | cbn; lia |];
      exact V280 ]
  | specialize (HSa HRK); clear HRK ] end.
all: match type of HSa with ?tq -> _ =>
  assert (HRK : tq);
  [ cbn [ss_mem all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite Ur, Usp3; split; [lia | exact I]
  | specialize (HSa HRK); clear HRK ] end.
all: clear HS.
all: rename HSa into HS.
all: lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
all: lazymatch type of HN with _ = ?nl =>
  let lo := eval vm_compute in (56 * nl + 8) in let hi := eval vm_compute in (56 * nl + 16) in
  pose proof (st_ok_pi_add_region Ev3 _ _ (YP09.mkRegion (Some 10%nat) lo hi lo hi []) HS
    ltac:(vm_compute; reflexivity)) as HSa
end.
all: match type of HSa with ?tq -> _ =>
  assert (HRK : tq);
  [ unfold region_ok; cbn [ms_mem restrict mkst YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
    rewrite Ur; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
    intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Hrpres4 (r + o) ltac:(lia)))
  | specialize (HSa HRK); clear HRK ] end.
all: match type of HSa with ?tq -> _ =>
  assert (HRK : tq);
  [ cbn [ss_mem all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite Ur, Usp3; split; [lia|]; split; [lia | exact I]
  | specialize (HSa HRK); clear HRK ] end.
all: clear HS.
all: rename HSa into HS.
all: lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
(* the block's shadow entry for the three CHK4 *)
all: assert (HRA4 : range_addressable (aview SEGS (w_H W) mem4) SHADOW_OFF r 288)
  by (apply (range_addressable_of_block SEGS B LAWS ly S W mem4 _ r REG_SIZE r 288 HAR4 Hin);
      change (req_size REG_SIZE) with 288; lia).
all: assert (SHOK4 : sh_ok SEGS ADBx [mkSHE 10 0 288] Ev3 (mrestrict (w_H W) mem4))
  by (unfold sh_ok; constructor; [|constructor];
      apply (shent_ok_of_range SEGS (w_H W) mem4 Ev3 ADBx 10 r 288 r 0 288 HRA4);
      [ unfold ADBx; rewrite (U_atom Ev3 32 ADSB E32') by (unfold ADSB; lia); reflexivity
      | exact (U_atom Ev3 10 r E10' ltac:(lia))
      | lia
      | lia
      | intros x Hx; revert Hrapp Hx; clear; unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg; intros; lia ]).
(* 0x81dd8 .. ret: the two CHK4 + stores, the CHK4 of r + 280, n + 1, the epilogue *)
all: paj_run_tok RUN HS HJ4 SHOK4 ADspan;
[ eapply awr_ok_cons_block;
  [ reflexivity | exact Ur | exact Hin | cbn; lia | cbn; first [lia | (unfold req_size, REG_SIZE; cbn; lia)]
  | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; exists (r, r + REG_SIZE); split; [left; reflexivity | cbn [fst snd]; change REG_SIZE with 288; lia] |];
  eapply awr_ok_cons_block;
  [ reflexivity | exact Ur | exact Hin | cbn; lia | cbn; first [lia | (unfold req_size, REG_SIZE; cbn; lia)]
  | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; exists (r, r + REG_SIZE); split; [left; reflexivity | cbn [fst snd]; change REG_SIZE with 288; lia] |];
  awr_ok_tac; exact Usp3
| ].
all: lazymatch goal with HFx : frame_of ?Exx ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
  assert (KEEPF : forall a, 0 <= a < 2 ^ 64 ->
    ~ ((spZ regs - 80 <= a < spZ regs) \/ (r + 56 * nrw + 8 <= a < r + 56 * nrw + 16) \/ (r + 280 <= a < r + 284)) ->
    aview SEGS (w_H W) m2 a = aview SEGS (w_H W) mem4 a)
  by (intros aa Haa Hnaa; apply (kept_of_frame Exx rs (w_H W) m1 m2
        (fun a => (spZ regs - 80 <= a < spZ regs) \/ (r + 56 * nrw + 8 <= a < r + 56 * nrw + 16) \/ (r + 280 <= a < r + 284)) HFx); [ |exact Haa | exact Hnaa];
      intros bb wlo whi ab Hwin Hr; cbn [windows map YP09.r_base YP09.r_wlo YP09.r_whi] in Hwin;
      destruct Hwin as [Eq|[Eq|[Eq|[]]]]; injection Eq as <- <- <-; cbn [base_val] in Hr;
      rewrite ?Ur, ?Usp3 in Hr; lia)
end.
all: rewrite HN in BY4, Z4, MAC4, KEEPF.
(* the final memory holds the chunks the stores left *)
all: lazymatch type of HN with _ = ?nl =>
lazymatch type of HS with st_ok_pi _ _ ?EE (mkSST _ _ _ (?rg1 :: ?rg2 :: _) _ _) (restrict _ ?msc) =>
  assert (VZ : forall j, 0 <= j < 4 ->
    aview SEGS (w_H W) (ms_mem msc) (r + (56 * nl + 8) + j) = Some ((z / 2 ^ (8 * j)) mod 256))
  by (intros j Hj; rewrite <- Ur;
      apply (nx_chunk_view EE _ msc (w_H W) rg1 10%nat (56 * nl + 8) 4 (SOff 68 0) z HS);
      [ apply in_eq | reflexivity | cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right])
      | apply nx_off0w; exact E68' | lia | cbn; lia ]);
  assert (VK : forall j, 0 <= j < 4 ->
    aview SEGS (w_H W) (ms_mem msc) (r + (56 * nl + 12) + j) = Some ((k / 2 ^ (8 * j)) mod 256))
  by (intros j Hj; rewrite <- Ur;
      apply (nx_chunk_view EE _ msc (w_H W) rg1 10%nat (56 * nl + 12) 4 (SOff 12 0) k HS);
      [ apply in_eq | reflexivity | cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right])
      | apply nx_off0w; exact E12' | unfold reac_boxreg_add_c.add_width_ok in HWOK; lia | cbn; lia ]);
  assert (VN : forall j, 0 <= j < 4 ->
    aview SEGS (w_H W) (ms_mem msc) (r + 280 + j) = Some (((nl + 1) / 2 ^ (8 * j)) mod 256))
  by (intros j Hj; rewrite <- Ur;
      apply (nx_chunk_view EE _ msc (w_H W) rg2 10%nat 280 4 (SLit (nl + 1)) (nl + 1) HS);
      [ apply in_cons, in_eq | reflexivity | cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right])
      | reflexivity | lia | cbn; lia ])
end end.
(* the return: a0 = n, the block holds add_bytes bs M z k *)
all: lazymatch type of HN with _ = ?nl =>
  ad_ret HS HJ4 E3a Hra HAE3 nl (reac_boxreg_add_c.add_bytes bs M z k)
end.
all: split;
[ right; right; right; right;
  split; [exact HWOK|]; split; [exact HMnz|]; split; [exact HNH|]; split; [exact HNU|];
  split; [change (Boxreg.bx_n bs) with nrw; lia|]; split; [change (Boxreg.bx_n bs) with nrw; lia|];
  exists z; split; [lia|]; split; [exact Hzlf | reflexivity]
| ].
all: intros i Hi.
all: change REG_SIZE with 288 in Hi.
all: change (bv_unsigned (nth (Z.to_nat i) (reac_boxreg_add_c.add_bytes bs M z k) (Z_to_bv 8 0)))
  with (adtb (reac_boxreg_add_c.add_bytes bs M z k) i).
all: rewrite (ad_new_view bs M z k i Hinv0 HML ltac:(change (Boxreg.bx_n bs) with nrw; lia) ltac:(lia) Hk ltac:(lia)).
all: cbv zeta.
all: change (Boxreg.bx_n bs) with nrw.
all: rewrite HN.
all: lazymatch type of HN with _ = ?nl =>
  assert (C : i < 56 * nl \/ (56 * nl <= i < 56 * nl + 6) \/ (56 * nl + 6 <= i < 56 * nl + 8) \/
              (56 * nl + 8 <= i < 56 * nl + 12) \/ (56 * nl + 12 <= i < 56 * nl + 16) \/
              (56 * nl + 16 <= i < 56 * nl + 56) \/ (56 * nl + 56 <= i < 280) \/ (280 <= i < 284) \/ 284 <= i)
    by lia;
  destruct C as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]; adm_simp;
  [ rewrite KEEPF by lia; apply BY4; lia
  | rewrite KEEPF by lia; replace (r + i) with (r + 56 * nl + (i - 56 * nl)) by lia; apply MAC4; lia
  | rewrite KEEPF by lia; replace (r + i) with (r + 56 * nl + (i - 56 * nl)) by lia; apply Z4; lia
  | replace (r + i) with (r + (56 * nl + 8) + (i - 56 * nl - 8)) by lia; apply VZ; lia
  | replace (r + i) with (r + (56 * nl + 12) + (i - 56 * nl - 12)) by lia; apply VK; lia
  | rewrite KEEPF by lia; replace (r + i) with (r + 56 * nl + (i - 56 * nl)) by lia; apply Z4; lia
  | rewrite KEEPF by lia; apply BY4; lia
  | replace (r + i) with (r + 280 + (i - 280)) by lia; apply VN; lia
  | rewrite KEEPF by lia; apply BY4; lia ]
end.
Qed.
(* S6AddBind: the bind loop of reac_boxreg_add (image A), 0x81ca4 .. the two ways out.
   Paste this block just before `Theorem pb_reac_boxreg_add` (inside Section h), and add
   to the file header (outside the Sections, next to the other Requires):
     From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require BoxFrame.
   (needed for BoxFrame.shadow_hull_vis_of_frame at the __asan_memcpy call). *)
(* ---------------------------------------------------------------------- *)
(* The bind loop (0x81ca4, listing offset 7512) and its two ways out.
   The walk enters in the middle of the function, so the state is built from
   the machine registers of that moment: the atoms 81 .. 112 hold those 32
   registers, and the atoms 0 .. 31 keep the ENTRY registers, which the frame
   chunks and the post still need. *)
Definition adrl (rg : bvmap 5 word) : list word :=
[getr rg 0; getr rg 1; getr rg 2; getr rg 3; getr rg 4; getr rg 5; getr rg 6; getr rg 7;
 getr rg 8; getr rg 9; getr rg 10; getr rg 11; getr rg 12; getr rg 13; getr rg 14; getr rg 15;
 getr rg 16; getr rg 17; getr rg 18; getr rg 19; getr rg 20; getr rg 21; getr rg 22; getr rg 23;
 getr rg 24; getr rg 25; getr rg 26; getr rg 27; getr rg 28; getr rg 29; getr rg 30; getr rg 31].
Definition adEX (bs M : list byte) (rg : bvmap 5 word) : list word :=
adextra bs M ++ [Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0] ++ adrl rg.
Definition adET (regs : bvmap 5 word) (bs M : list byte) (rg : bvmap 5 word) : env :=
Eimg (Ereg regs (adEX bs M rg)).
Lemma adextra_len : forall bs M, length (adextra bs M) = 44%nat.
Proof. intros bs M. reflexivity. Qed.
Lemma ad_ewr : forall regs bs M rg n (x : bv 5), Z.of_nat n = bv_unsigned x -> (n < 32)%nat ->
  ew (adET regs bs M rg) n = getr regs x.
Proof.
intros regs bs M rg n x Hn Hlt. unfold adET. rewrite Eimg_low by (unfold A_TEXT; lia).
apply ew_Ereg_nat. exact Hn.
Qed.
Lemma ad_ewx : forall regs bs M rg n j, n = (32 + j)%nat -> (j < 44)%nat ->
  ew (adET regs bs M rg) n = nth j (adextra bs M) (Z_to_bv 64 0).
Proof.
intros regs bs M rg n j -> Hj. unfold adET. rewrite Eimg_low by (unfold A_TEXT; lia).
rewrite ew_Ereg_extra. unfold adEX. rewrite app_nth1 by (rewrite adextra_len; lia). reflexivity.
Qed.
Lemma ad_ewj : forall regs bs M rg n j, n = (81 + j)%nat -> (j < 32)%nat ->
  ew (adET regs bs M rg) n = nth j (adrl rg) (Z_to_bv 64 0).
Proof.
intros regs bs M rg n j -> Hj. unfold adET. rewrite Eimg_low by (unfold A_TEXT; lia).
replace (81 + j)%nat with (32 + (49 + j))%nat by lia. rewrite ew_Ereg_extra. unfold adEX.
rewrite app_nth2 by (rewrite adextra_len; lia). rewrite adextra_len.
replace (49 + j - 44)%nat with (5 + j)%nat by lia.
rewrite app_nth2 by (cbn [length]; lia). cbn [length].
replace (5 + j - 5)%nat with j by lia. reflexivity.
Qed.
Lemma ad_ewj_den : forall regs bs M rg n j, n = (81 + j)%nat -> (j < 32)%nat ->
  sv_denot (adET regs bs M rg) (SOff n 0) = nth j (adrl rg) (Z_to_bv 64 0).
Proof.
intros regs bs M rg n j Hn Hj. cbn [sv_denot].
rewrite (ad_ewj regs bs M rg n j Hn Hj), Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.
Lemma ad_den_atom : forall regs bs M rg n (x : bv 5) v, Z.of_nat n = bv_unsigned x -> (n < 32)%nat ->
  getr regs x = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> forall z,
  sv_denot (adET regs bs M rg) (SOff n z) = Z_to_bv 64 (v + z).
Proof.
intros regs bs M rg n x v Hn Hlt Hx Hv z. cbn [sv_denot].
rewrite (ad_ewr regs bs M rg n x Hn Hlt), Hx, unsigned_lit_small by lia. reflexivity.
Qed.
Lemma ad_den_keep : forall regs bs M rg n (x : bv 5), Z.of_nat n = bv_unsigned x -> (n < 32)%nat ->
  sv_denot (adET regs bs M rg) (SOff n 0) = getr regs x.
Proof.
intros regs bs M rg n x Hn Hlt. cbn [sv_denot].
rewrite (ad_ewr regs bs M rg n x Hn Hlt), Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.
(* The registers at the head of the loop (0x81ca4): s4 = i, a2 = a3 = r + 56 i, the live
   callee-saved registers; everything the walk does not read is an atom of its own. *)
Definition adJ (n : nat) : sv := SOff (81 + n) 0.
Definition adS7 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 280) (SLit 3)) (SOff 32 0).
Definition adsr (i : Z) : list sv :=
[SLit 0; adJ 1; SOff 2 (-80); SOff 3 0; SOff 4 0; adJ 5; adJ 6; adJ 7;
 SOff 12 0; SOff 11 0; adJ 10; adJ 11; SOff 10 (56 * i); SOff 10 (56 * i); adJ 14; adJ 15; adJ 16; adJ 17;
 SOff 10 0; SOff 10 280; SLit i; adJ 21; SOff 32 0; adS7; adJ 24;
 SOff 25 0; SOff 26 0; SOff 27 0; adJ 28; adJ 29; adJ 30; adJ 31].
(* The registers at 0x81e2c, the slot __asan_memcpy returns to: s4 = z and the frame. *)
Definition adtr (z : Z) : list sv :=
[SLit 0; adJ 1; SOff 2 (-80); SOff 3 0; SOff 4 0; adJ 5; adJ 6; adJ 7;
 adJ 8; adJ 9; adJ 10; adJ 11; adJ 12; adJ 13; adJ 14; adJ 15; adJ 16; adJ 17;
 adJ 18; adJ 19; SLit z; adJ 21; adJ 22; adJ 23; adJ 24;
 SOff 25 0; SOff 26 0; SOff 27 0; adJ 28; adJ 29; adJ 30; adJ 31].
(* The ten frame slots: the prologue put the entry registers there. *)
Definition adfr (regs : bvmap 5 word) (W : world SEGS) (memT : word -> option byte) : Prop :=
val_mem SEGS (mrestrict (w_H W) memT) (spZ regs - 80) 8 (bv_unsigned (getr regs 24)) /\
val_mem SEGS (mrestrict (w_H W) memT) (spZ regs - 72) 8 (bv_unsigned (getr regs 23)) /\
val_mem SEGS (mrestrict (w_H W) memT) (spZ regs - 64) 8 (bv_unsigned (getr regs 22)) /\
val_mem SEGS (mrestrict (w_H W) memT) (spZ regs - 56) 8 (bv_unsigned (getr regs 21)) /\
val_mem SEGS (mrestrict (w_H W) memT) (spZ regs - 48) 8 (bv_unsigned (getr regs 20)) /\
val_mem SEGS (mrestrict (w_H W) memT) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) /\
val_mem SEGS (mrestrict (w_H W) memT) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) /\
val_mem SEGS (mrestrict (w_H W) memT) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) /\
val_mem SEGS (mrestrict (w_H W) memT) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) /\
val_mem SEGS (mrestrict (w_H W) memT) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)).
Lemma ad_w64_rng : forall w : word, 0 <= bv_unsigned w < 2 ^ (8 * Z.of_N 8).
Proof.
intros w. pose proof (bv_unsigned_in_range 64 w) as H. change (bv_modulus 64) with (2 ^ 64) in H.
replace (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) by (vm_compute; reflexivity). exact H.
Qed.
Lemma ad_frame_chunk : forall regs bs M rg (W : world SEGS) memT off n (x : bv 5),
  Z.of_nat n = bv_unsigned x -> (n < 32)%nat ->
  val_mem SEGS (mrestrict (w_H W) memT) (spZ regs + off) 8 (bv_unsigned (getr regs x)) ->
  YP09.chunk_ok SEGS (adET regs bs M rg) (mrestrict (w_H W) memT) (spZ regs)
    (YP09.mkChunk off (CVal 8 (SOff n 0))).
Proof.
intros regs bs M rg W memT off n x Hn Hlt HV.
apply (chunk_ok_val SEGS (adET regs bs M rg) (mrestrict (w_H W) memT) (spZ regs) off 8 (SOff n 0)
  (bv_unsigned (getr regs x))).
- rewrite (ad_den_keep regs bs M rg n x Hn Hlt). symmetry. apply Z_to_bv_bv_unsigned.
- apply ad_w64_rng.
- zside.
- cbn [N.to_nat]. exact HV.
Qed.
(* The reverse: the frame slots of a state the walk has reached. *)
Lemma ad_chunk_val : forall E m base off (x : sv) v,
  YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal 8 x)) ->
  sv_denot E x = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> val_mem SEGS m (base + off) 8 v.
Proof.
intros E m base off x v HC Hd Hv kk Hk.
assert (Hk8 : 0 <= Z.of_nat kk < YP09.c_len (YP09.mkChunk off (CVal 8 x))).
{ cbv [YP09.c_len YP09.c_val YP09.cv_len]. cbn [Z.of_N]. lia. }
destruct (HC (Z.of_nat kk) Hk8) as (b & Hb & Hm).
cbv [YP09.cbyte YP09.c_val YP09.c_off] in Hb, Hm.
injection Hb as <-. rewrite Hm. f_equal.
unfold YP09.byte_of_word. rewrite Hd, unsigned_lit_small by lia.
symmetry. apply (le_byte_small v 8 kk);
  [replace (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) by (vm_compute; reflexivity); lia | lia].
Qed.
Lemma ad_frame_out : forall E (W : world SEGS) msx (regs : bvmap 5 word),
  Forall (YP09.chunk_ok SEGS E (mrestrict (w_H W) (ms_mem msx)) (bv_unsigned (ew E 2)))
    (YP09.r_chunks adframe) ->
  bv_unsigned (ew E 2) = spZ regs ->
  (forall n (x : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned x -> ew E n = getr regs x) ->
  adfr regs W (ms_mem msx).
Proof.
intros E W msx regs HF Hsp HE.
assert (HR : forall x : bv 5, 0 <= bv_unsigned (getr regs x) < 2 ^ 64).
{ intros x. pose proof (bv_unsigned_in_range 64 (getr regs x)) as H.
  change (bv_modulus 64) with (2 ^ 64) in H. exact H. }
assert (HD : forall n (x : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned x ->
  sv_denot E (SOff n 0) = Z_to_bv 64 (bv_unsigned (getr regs x))).
{ intros n x Hn Hx. cbn [sv_denot]. rewrite (HE n x Hn Hx), Z.add_0_r. reflexivity. }
unfold adframe in HF. cbn [YP09.r_chunks] in HF. rewrite Hsp in HF.
pose proof (Forall_inv HF) as A1. pose proof (Forall_inv_tail HF) as G1. clear HF.
pose proof (Forall_inv G1) as A2. pose proof (Forall_inv_tail G1) as G2. clear G1.
pose proof (Forall_inv G2) as A3. pose proof (Forall_inv_tail G2) as G3. clear G2.
pose proof (Forall_inv G3) as A4. pose proof (Forall_inv_tail G3) as G4. clear G3.
pose proof (Forall_inv G4) as A5. pose proof (Forall_inv_tail G4) as G5. clear G4.
pose proof (Forall_inv G5) as A6. pose proof (Forall_inv_tail G5) as G6. clear G5.
pose proof (Forall_inv G6) as A7. pose proof (Forall_inv_tail G6) as G7. clear G6.
pose proof (Forall_inv G7) as A8. pose proof (Forall_inv_tail G7) as G8. clear G7.
pose proof (Forall_inv G8) as A9. pose proof (Forall_inv_tail G8) as G9. clear G8.
pose proof (Forall_inv G9) as A10. clear G9.
unfold adfr. repeat apply conj.
- replace (spZ regs - 80) with (spZ regs + -80) by lia.
  apply (ad_chunk_val E _ (spZ regs) (-80) (SOff 24 0) (bv_unsigned (getr regs (24%bv : bv 5))) A1
    (HD 24%nat (24%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)) (HR (24%bv : bv 5))).
- replace (spZ regs - 72) with (spZ regs + -72) by lia.
  apply (ad_chunk_val E _ (spZ regs) (-72) (SOff 23 0) (bv_unsigned (getr regs (23%bv : bv 5))) A2
    (HD 23%nat (23%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)) (HR (23%bv : bv 5))).
- replace (spZ regs - 64) with (spZ regs + -64) by lia.
  apply (ad_chunk_val E _ (spZ regs) (-64) (SOff 22 0) (bv_unsigned (getr regs (22%bv : bv 5))) A3
    (HD 22%nat (22%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)) (HR (22%bv : bv 5))).
- replace (spZ regs - 56) with (spZ regs + -56) by lia.
  apply (ad_chunk_val E _ (spZ regs) (-56) (SOff 21 0) (bv_unsigned (getr regs (21%bv : bv 5))) A4
    (HD 21%nat (21%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)) (HR (21%bv : bv 5))).
- replace (spZ regs - 48) with (spZ regs + -48) by lia.
  apply (ad_chunk_val E _ (spZ regs) (-48) (SOff 20 0) (bv_unsigned (getr regs (20%bv : bv 5))) A5
    (HD 20%nat (20%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)) (HR (20%bv : bv 5))).
- replace (spZ regs - 40) with (spZ regs + -40) by lia.
  apply (ad_chunk_val E _ (spZ regs) (-40) (SOff 19 0) (bv_unsigned (getr regs (19%bv : bv 5))) A6
    (HD 19%nat (19%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)) (HR (19%bv : bv 5))).
- replace (spZ regs - 32) with (spZ regs + -32) by lia.
  apply (ad_chunk_val E _ (spZ regs) (-32) (SOff 18 0) (bv_unsigned (getr regs (18%bv : bv 5))) A7
    (HD 18%nat (18%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)) (HR (18%bv : bv 5))).
- replace (spZ regs - 24) with (spZ regs + -24) by lia.
  apply (ad_chunk_val E _ (spZ regs) (-24) (SOff 9 0) (bv_unsigned (getr regs (9%bv : bv 5))) A8
    (HD 9%nat (9%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)) (HR (9%bv : bv 5))).
- replace (spZ regs - 16) with (spZ regs + -16) by lia.
  apply (ad_chunk_val E _ (spZ regs) (-16) (SOff 8 0) (bv_unsigned (getr regs (8%bv : bv 5))) A9
    (HD 8%nat (8%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)) (HR (8%bv : bv 5))).
- replace (spZ regs - 8) with (spZ regs + -8) by lia.
  apply (ad_chunk_val E _ (spZ regs) (-8) (SOff 1 0) (bv_unsigned (getr regs (1%bv : bv 5))) A10
    (HD 1%nat (1%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)) (HR (1%bv : bv 5))).
Qed.
Definition adtfacts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition adss_row (i : Z) : sstate := mkSS 7512 (adsr i) adregions2 None adfacts.
Definition adss_tail (z : Z) : sstate := mkSS 7904 (adtr z) [adframe] None adtfacts.
(* The state of the walk at a slot inside the function, from the machine registers there. *)
Lemma ad_state : forall ly S W (regs : bvmap 5 word) mem md ch (r p : Z) (bs M : list byte)
  (rg : bvmap 5 word) (memT : word -> option byte) (mdT : Model) (pc : Z) (sr : list sv),
afn_pre SEGS B REAC_BOXREG_ADD_STK ly S W regs mem md ch ->
ajournal SEGS B REAC_BOXREG_ADD_STK (spZ regs) [(r, r + REG_SIZE)] ly S W mem md [] ly S W memT mdT 0 ->
getr regs 10 = w64 r -> getr regs 11 = w64 p ->
In (r, REG_SIZE) (ablocks B ly S) ->
(forall o, 0 <= o < REG_SIZE -> aview SEGS (w_H W) memT (r + o) = Some (adtb bs o)) ->
afobj SEGS B ly S W memT p 6 ->
(forall o, 0 <= o < 6 -> aview SEGS (w_H W) memT (p + o) = Some (adtb M o)) ->
adfr regs W memT ->
regs_ok (adET regs bs M rg) sr rg ->
st_ok_pi SEGS VAL (adET regs bs M rg) (mkSS pc sr adregions2 None adfacts)
  (restrict (w_H W) (mkst rg (Z_to_bv 64 (BASE + pc)) memT (seg_rom SEGS)))
/\ sh_ok SEGS ADBx adSH (adET regs bs M rg) (mrestrict (w_H W) memT).
Proof.
intros ly S W regs mem md ch r p bs M rg memT mdT pc sr HPRE HJ H10 H11 Hin Hbs HFO HMv HFR HRO.
pose proof HJ as (J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10 & J11 & J12 & J13 & J14 & J15 & J16 & J17).
pose proof HFO as ((cid & pos & Hfin & Hcid & Hfal & Hflo & Hfhi) & Hp8 & HRA).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hchn & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOXREG_ADD_STK = 8320) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W memT mdT r REG_SIZE J1 Hin)
  as (Hr16 & Hr4096 & Hrceil & Hrapp & Hrpres & _ & _).
pose proof (blk_off_imgP B ly S W memT mdT r REG_SIZE J1 Hin) as Hrimg.
change (req_size REG_SIZE) with 288 in Hrceil, Hrapp, Hrpres, Hrimg.
destruct (frames_bounds SEGS B LAWS ly S W memT mdT cid pos J1 Hfin) as (Hf4096 & Hfceil & Hfapp).
pose proof (frm_off_imgP B ly S W memT mdT cid pos J1 Hfin) as Hfimg.
pose proof (sep_block_frame SEGS B LAWS ly S W memT mdT r REG_SIZE cid pos J1 Hin Hfin) as Hrf.
unfold zdisjoint in Hrf. cbn [fst snd] in Hrf. change (req_size REG_SIZE) with 288 in Hrf.
destruct (al_const _ _ LAWS ly S W memT mdT J1) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
pose proof (range_addressable_of_block SEGS B LAWS ly S W memT mdT r REG_SIZE r 288 J1 Hin
  ltac:(lia) ltac:(change (req_size REG_SIZE) with 288; lia)) as HRAr.
assert (V1 : forall o, 0 <= o < 288 -> val_mem SEGS (mrestrict (w_H W) memT) (r + o) 1 (adtb bs o))
by (intros o Ho; apply ad_val1; apply Hbs; unfold REG_SIZE; lia).
assert (V4 : forall o, 0 <= o -> o + 4 <= 288 -> val_mem SEGS (mrestrict (w_H W) memT) (r + o) 4 (ad4 bs o))
by (intros o Ho1 Ho2; unfold ad4; apply ad_val4; rewrite <- ?Z.add_assoc; apply Hbs; unfold REG_SIZE; lia).
assert (VM : forall o, 0 <= o < 6 -> val_mem SEGS (mrestrict (w_H W) memT) (p + o) 1 (adtb M o))
by (intros o Ho; apply ad_val1; apply HMv; lia).
rewrite restrict_mkst_fx.
assert (E2 : ew (adET regs bs M rg) 2 = getr regs 2)
by (apply (ad_ewr regs bs M rg 2%nat 2%bv eq_refl); lia).
assert (E10 : ew (adET regs bs M rg) 10 = Z_to_bv 64 r)
by (rewrite (ad_ewr regs bs M rg 10%nat 10%bv eq_refl ltac:(lia)); exact H10).
assert (E11 : ew (adET regs bs M rg) 11 = Z_to_bv 64 p)
by (rewrite (ad_ewr regs bs M rg 11%nat 11%bv eq_refl ltac:(lia)); exact H11).
assert (E32 : ew (adET regs bs M rg) 32 = Z_to_bv 64 ADSB)
by (rewrite (ad_ewx regs bs M rg 32%nat 0%nat eq_refl ltac:(lia)); reflexivity).
assert (Egot : ew (adET regs bs M rg) (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
by (unfold adET; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Ecell : ew (adET regs bs M rg) (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
by (unfold adET; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew (adET regs bs M rg) 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew (adET regs bs M rg) n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  base_val (adET regs bs M rg) (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
destruct HFR as (F80 & F72 & F64 & F56 & F48 & F40 & F32 & F24 & F16 & F8).
split.
- apply pa_entry_st_ok_full.
  + exact HRO.
  + vm_compute. reflexivity.
  + unfold adregions2. repeat apply Forall_cons; try apply Forall_nil.
    * (* the registry block *)
      unfold adR, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB 10%nat r E10) by lia.
      split; [lia|]. split; [lia|]. split.
      { intros o Ho. apply (apresent_writable SEGS). apply (proj1 (Hrpres (r + o) ltac:(lia))). }
      lazymatch goal with |- Forall _ ?l => let l' := eval vm_compute in l in change l with l' end.
      repeat apply Forall_cons; try apply Forall_nil.
      all: lazymatch goal with
      | |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 1 (SOff ?n 0))) =>
          let j := eval vm_compute in (n - 32)%nat in
          apply (chunk_ok_val SEGS (adET regs bs M rg) _ r off 1 (SOff n 0) (adtb bs off));
          [ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned,
              (ad_ewx regs bs M rg n j eq_refl ltac:(lia));
            unfold adextra; rewrite map_nth; cbn [adrowv app nth]; reflexivity
          | exact (ad_tb_rng bs off) | zside | exact (V1 off ltac:(lia)) ]
      | |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 4 (SOff ?n 0))) =>
          let j := eval vm_compute in (n - 32)%nat in
          apply (chunk_ok_val SEGS (adET regs bs M rg) _ r off 4 (SOff n 0) (ad4 bs off));
          [ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned,
              (ad_ewx regs bs M rg n j eq_refl ltac:(lia));
            unfold adextra; rewrite map_nth; cbn [adrowv app nth]; reflexivity
          | exact (ad_4_rng bs off) | zside | exact (V4 off ltac:(lia) ltac:(lia)) ]
      end.
    * (* the MAC *)
      unfold adP, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB 11%nat p E11) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      all: lazymatch goal with
      | |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 1 (SOff ?n 0))) =>
          let j := eval vm_compute in (n - 32)%nat in
          apply (chunk_ok_val SEGS (adET regs bs M rg) _ p off 1 (SOff n 0) (adtb M off));
          [ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned,
              (ad_ewx regs bs M rg n j eq_refl ltac:(lia));
            unfold adextra; rewrite map_nth; cbn [adrowv app nth]; reflexivity
          | exact (ad_tb_rng M off) | zside | exact (VM off ltac:(lia)) ]
      end.
    * (* the frame *)
      unfold adframe, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split.
      { intros o Ho. apply (apresent_writable SEGS). apply J14. rewrite WS. lia. }
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (ad_frame_chunk regs bs M rg W memT (-80) 24%nat 24%bv eq_refl ltac:(lia)).
         replace (spZ regs + -80) with (spZ regs - 80) by lia. exact F80.
      -- apply (ad_frame_chunk regs bs M rg W memT (-72) 23%nat 23%bv eq_refl ltac:(lia)).
         replace (spZ regs + -72) with (spZ regs - 72) by lia. exact F72.
      -- apply (ad_frame_chunk regs bs M rg W memT (-64) 22%nat 22%bv eq_refl ltac:(lia)).
         replace (spZ regs + -64) with (spZ regs - 64) by lia. exact F64.
      -- apply (ad_frame_chunk regs bs M rg W memT (-56) 21%nat 21%bv eq_refl ltac:(lia)).
         replace (spZ regs + -56) with (spZ regs - 56) by lia. exact F56.
      -- apply (ad_frame_chunk regs bs M rg W memT (-48) 20%nat 20%bv eq_refl ltac:(lia)).
         replace (spZ regs + -48) with (spZ regs - 48) by lia. exact F48.
      -- apply (ad_frame_chunk regs bs M rg W memT (-40) 19%nat 19%bv eq_refl ltac:(lia)).
         replace (spZ regs + -40) with (spZ regs - 40) by lia. exact F40.
      -- apply (ad_frame_chunk regs bs M rg W memT (-32) 18%nat 18%bv eq_refl ltac:(lia)).
         replace (spZ regs + -32) with (spZ regs - 32) by lia. exact F32.
      -- apply (ad_frame_chunk regs bs M rg W memT (-24) 9%nat 9%bv eq_refl ltac:(lia)).
         replace (spZ regs + -24) with (spZ regs - 24) by lia. exact F24.
      -- apply (ad_frame_chunk regs bs M rg W memT (-16) 8%nat 8%bv eq_refl ltac:(lia)).
         replace (spZ regs + -16) with (spZ regs - 16) by lia. exact F16.
      -- apply (ad_frame_chunk regs bs M rg W memT (-8) 1%nat 1%bv eq_refl ltac:(lia)).
         replace (spZ regs + -8) with (spZ regs - 8) by lia. exact F8.
    * (* the GOT word of the shadow cell *)
      unfold got_regionP, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS (adET regs bs M rg) _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite Ecell, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memT _ _ Kgot).
    * (* the shadow cell *)
      unfold bcell_regionP, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Ecell) by (pose proof (pa_val_range (A_OBJ 12)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS (adET regs bs M rg) _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) ADSB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold ADSB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memT _ _ Kcell).
  + apply pairwise_disjoint_of_extents.
    unfold adregions2, adR, adP, adframe, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 10%nat r E10) by lia. rewrite (VB 11%nat p E11) by lia.
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Ecell) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil C1 WS Hstk0 HcellR HgcD HgotR Hr4096 Hrceil Hrimg
      Hf4096 Hfceil Hflo Hfhi Hfimg Hrf.
    clear. intros. repeat split; lia.
  + unfold adfacts, adrowf, PTR. split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok app].
    split.
    { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp. change (2 ^ 4) with 16.
      revert Hslo Hshi H47 Hceil C1 WS Hstk0 Hal16. clear. intros. repeat split; lia. }
    split.
    { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E10, unsigned_lit_small by lia.
      change (2 ^ 4) with 16.
      revert Hr16 Hr4096 Hrceil C1. clear. intros. repeat split; lia. }
    split.
    { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E11, unsigned_lit_small by lia.
      change (2 ^ 3) with 8.
      revert Hf4096 Hfceil Hflo Hfhi Hp8 C1. clear. intros. repeat split; lia. }
    split.
    { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E32, unsigned_lit_small by (unfold ADSB; lia).
      rewrite Z.pow_0_r, Z.mod_1_r. lia. }
    repeat lazymatch goal with
    | |- True => exact I
    | |- afact_ok _ ?n _ /\ _ =>
        let j := eval vm_compute in (n - 32)%nat in
        split;
        [ first [ eapply ad_afb | eapply ad_afw ];
          rewrite (ad_ewx regs bs M rg n j eq_refl ltac:(lia));
          unfold adextra; rewrite map_nth; cbn [adrowv app nth]; reflexivity
        | ]
    end.
- unfold sh_ok, adSH. constructor; [|constructor; [|constructor]].
  + apply (shent_ok_of_range SEGS (w_H W) memT (adET regs bs M rg) ADBx 10 r 288 r 0 288 HRAr).
    * unfold ADBx. rewrite (U_atom (adET regs bs M rg) 32 ADSB E32) by (unfold ADSB; lia). reflexivity.
    * exact (U_atom (adET regs bs M rg) 10 r E10 ltac:(lia)).
    * lia.
    * lia.
    * intros x Hx. revert Hrapp Hx. clear. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg. intros. lia.
  + apply (shent_ok_of_range SEGS (w_H W) memT (adET regs bs M rg) ADBx 11 p 6 p 0 6 HRA).
    * unfold ADBx. rewrite (U_atom (adET regs bs M rg) 32 ADSB E32) by (unfold ADSB; lia). reflexivity.
    * exact (U_atom (adET regs bs M rg) 11 p E11 ltac:(lia)).
    * lia.
    * lia.
    * intros x Hx. revert Hfapp Hflo Hfhi Hx. clear.
      unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg. intros. lia.
Qed.
(* The same at the epilogue, where only the frame is read. *)
Lemma ad_state_tail : forall ly S W (regs : bvmap 5 word) mem md ch (r : Z) (bs M : list byte)
  (rg : bvmap 5 word) (memT : word -> option byte) (mdT : Model) (pc : Z) (sr : list sv),
afn_pre SEGS B REAC_BOXREG_ADD_STK ly S W regs mem md ch ->
ajournal SEGS B REAC_BOXREG_ADD_STK (spZ regs) [(r, r + REG_SIZE)] ly S W mem md [] ly S W memT mdT 0 ->
adfr regs W memT ->
regs_ok (adET regs bs M rg) sr rg ->
st_ok_pi SEGS VAL (adET regs bs M rg) (mkSS pc sr [adframe] None adtfacts)
  (restrict (w_H W) (mkst rg (Z_to_bv 64 (BASE + pc)) memT (seg_rom SEGS))).
Proof.
intros ly S W regs mem md ch r bs M rg memT mdT pc sr HPRE HJ HFR HRO.
pose proof HJ as (J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10 & J11 & J12 & J13 & J14 & J15 & J16 & J17).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hchn & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOXREG_ADD_STK = 8320) by reflexivity.
assert (E2 : ew (adET regs bs M rg) 2 = getr regs 2)
by (apply (ad_ewr regs bs M rg 2%nat 2%bv eq_refl); lia).
assert (Usp : bv_unsigned (ew (adET regs bs M rg) 2) = spZ regs) by (rewrite E2; reflexivity).
destruct HFR as (F80 & F72 & F64 & F56 & F48 & F40 & F32 & F24 & F16 & F8).
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- exact HRO.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
  unfold adframe, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split.
  { intros o Ho. apply (apresent_writable SEGS). apply J14. rewrite WS. lia. }
  repeat apply Forall_cons; try apply Forall_nil.
  + apply (ad_frame_chunk regs bs M rg W memT (-80) 24%nat 24%bv eq_refl ltac:(lia)).
    replace (spZ regs + -80) with (spZ regs - 80) by lia. exact F80.
  + apply (ad_frame_chunk regs bs M rg W memT (-72) 23%nat 23%bv eq_refl ltac:(lia)).
    replace (spZ regs + -72) with (spZ regs - 72) by lia. exact F72.
  + apply (ad_frame_chunk regs bs M rg W memT (-64) 22%nat 22%bv eq_refl ltac:(lia)).
    replace (spZ regs + -64) with (spZ regs - 64) by lia. exact F64.
  + apply (ad_frame_chunk regs bs M rg W memT (-56) 21%nat 21%bv eq_refl ltac:(lia)).
    replace (spZ regs + -56) with (spZ regs - 56) by lia. exact F56.
  + apply (ad_frame_chunk regs bs M rg W memT (-48) 20%nat 20%bv eq_refl ltac:(lia)).
    replace (spZ regs + -48) with (spZ regs - 48) by lia. exact F48.
  + apply (ad_frame_chunk regs bs M rg W memT (-40) 19%nat 19%bv eq_refl ltac:(lia)).
    replace (spZ regs + -40) with (spZ regs - 40) by lia. exact F40.
  + apply (ad_frame_chunk regs bs M rg W memT (-32) 18%nat 18%bv eq_refl ltac:(lia)).
    replace (spZ regs + -32) with (spZ regs - 32) by lia. exact F32.
  + apply (ad_frame_chunk regs bs M rg W memT (-24) 9%nat 9%bv eq_refl ltac:(lia)).
    replace (spZ regs + -24) with (spZ regs - 24) by lia. exact F24.
  + apply (ad_frame_chunk regs bs M rg W memT (-16) 8%nat 8%bv eq_refl ltac:(lia)).
    replace (spZ regs + -16) with (spZ regs - 16) by lia. exact F16.
  + apply (ad_frame_chunk regs bs M rg W memT (-8) 1%nat 1%bv eq_refl ltac:(lia)).
    replace (spZ regs + -8) with (spZ regs - 8) by lia. exact F8.
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- unfold adtfacts. split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. split; [|exact I].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp. change (2 ^ 4) with 16.
  revert Hslo Hshi H47 Hceil C1 WS Hstk0 Hal16. clear. intros. repeat split; lia.
Qed.
(* The branch tests of the loop. *)
Lemma ad_swrap32_rng : forall v, - 2 ^ 31 <= bv_swrap 32 v < 2 ^ 31.
Proof.
intros v. unfold bv_swrap, bv_wrap.
change (bv_modulus 32) with (2 ^ 32). change (bv_half_modulus 32) with (2 ^ 31).
Z.div_mod_to_equations. lia.
Qed.
Lemma ad_sext_den : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 (bv_swrap 32 v).
Proof.
intros E n v Hn Hv.
assert (HS : Sg E (SExt true 32 (SOff n 0)) = bv_swrap 32 v) by (apply ad_sg_sext; assumption).
rewrite (denot_lit_U E (SExt true 32 (SOff n 0))), (U_of_S E (SExt true 32 (SOff n 0))), HS.
pose proof (ad_swrap32_rng v) as Hr.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma ad_bnz_b : forall E n bss o, ew E n = Z_to_bv 64 (adtb bss o) ->
  branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = negb (adtb bss o =? 0).
Proof. intros E n bss o H. apply (ad_bnz E n (adtb bss o) H). pose proof (ad_tb_rng bss o). lia. Qed.
Lemma ad_bne_lit : forall E a n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= a < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SLit a)) (sv_denot E (SOff n 0)) = negb (a =? v).
Proof.
intros E a n v Hn Hv Ha. rewrite branch_ne_U, U_SLit, (U_atom E n v Hn Hv).
unfold zcanon, M64. rewrite (Z.mod_small a (2 ^ 64)) by lia. reflexivity.
Qed.
Lemma ad_bge4 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
  branch_taken BC_GE (sv_denot E (SLit 4)) (sv_denot E (SExt true 32 (SOff n 0)))
  = negb (4 <? bv_swrap 32 v).
Proof.
intros E n v Hn Hv. cbn [branch_taken]. unfold bv_lts.
change (bv_signed (sv_denot E (SLit 4))) with (Sg E (SLit 4)).
change (bv_signed (sv_denot E (SExt true 32 (SOff n 0)))) with (Sg E (SExt true 32 (SOff n 0))).
rewrite (ad_sg_sext E n v Hn Hv), S_SLit.
replace (bv_swrap 64 4) with 4 by (vm_compute; reflexivity). reflexivity.
Qed.
Lemma ad_beq_sext : forall E n v nk kk, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
  ew E nk = Z_to_bv 64 kk -> - 2 ^ 31 <= kk < 2 ^ 31 ->
  branch_taken BC_EQ (sv_denot E (SExt true 32 (SOff n 0))) (sv_denot E (SOff nk 0))
  = (bv_swrap 32 v =? kk).
Proof.
intros E n v nk kk Hn Hv Hk Hkk.
rewrite branch_eq_U, (U_of_S E (SExt true 32 (SOff n 0))), (U_of_S E (SOff nk 0)),
  (ad_sg_sext E n v Hn Hv), (ad_sg_off E nk kk Hk ltac:(lia)).
pose proof (ad_swrap32_rng v) as Hr.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
destruct (Z.eqb_spec (bv_swrap 32 v) kk) as [He|Hne].
- rewrite He. apply Z.eqb_refl.
- apply Z.eqb_neq. intros HH. apply Hne. revert HH. Z.div_mod_to_equations. lia.
Qed.
(* Memory facts carried along the walk. *)
Lemma ad_mbyte_of_aview : forall (W : world SEGS) m m' a b,
  aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a ->
  mbyte SEGS (mrestrict (w_H W) m) a = Some b -> mbyte SEGS (mrestrict (w_H W) m') a = Some b.
Proof.
intros W m m' a b Heq Hm. unfold aview, option_map in Heq. rewrite Hm in Heq.
destruct (mbyte SEGS (mrestrict (w_H W) m') a) as [b'|] eqn:Hb'; [|discriminate].
injection Heq as Heq. f_equal. apply bv_eq. exact Heq.
Qed.
Lemma ad_fr_of_aview : forall (W : world SEGS) (regs : bvmap 5 word) m m',
  (forall a, spZ regs - 80 <= a < spZ regs -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  adfr regs W m -> adfr regs W m'.
Proof.
intros W regs m m' HK HF.
destruct HF as (F80 & F72 & F64 & F56 & F48 & F40 & F32 & F24 & F16 & F8).
unfold adfr. repeat apply conj;
  (intros kk Hk;
   lazymatch goal with
   | |- mbyte _ _ (?a + _) = _ =>
       lazymatch goal with
       | Fx : val_mem _ _ a 8 _ |- _ =>
           apply (ad_mbyte_of_aview W m m'); [apply HK; lia | apply Fx; lia]
       end
   end).
Qed.
(* The shadow bytes of the MAC lie far below the frame, so a run that writes only the frame
   keeps the MAC object (ad_afobj_keep of the main walk). *)
Lemma adb_shadow_out : forall (regs : bvmap 5 word) ly p0,
  0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000 ->
  ly_stk_lo ly + REAC_BOXREG_ADD_STK <= spZ regs -> alloc_ceiling <= ly_stk_lo ly ->
  4096 <= p0 -> p0 + 6 <= alloc_ceiling ->
  forall x : Z, p0 <= x < p0 + 6 ->
    0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 64 /\
    ~ (spZ regs - 80 <= shadow_of_addr SHADOW_OFF x < spZ regs).
Proof.
intros regs ly p0 Hac Hsp Hc Hp1 Hp2 x Hx.
assert (WSa : REAC_BOXREG_ADD_STK = 8320) by reflexivity.
unfold shadow_of_addr, SHADOW_OFF. Z.div_mod_to_equations. lia.
Qed.
Lemma ad_frame_of_st : forall E ss (W : world SEGS) msx (regs : bvmap 5 word),
  st_ok SEGS E ss (restrict (w_H W) msx) -> ss_mem ss = adregions2 ->
  bv_unsigned (ew E 2) = spZ regs ->
  (forall n (x : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned x -> ew E n = getr regs x) ->
  adfr regs W (ms_mem msx).
Proof.
intros E ss W msx regs HS Hmem Hsp HE.
apply (ad_frame_out E W msx regs); [| exact Hsp | exact HE].
pose proof (st_ok_mem_ok SEGS E ss (restrict (w_H W) msx) HS) as HM.
destruct HM as (_ & HFa & _).
rewrite Hmem in HFa. unfold adregions2 in HFa.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HFa))) as HR3.
destruct HR3 as (_ & _ & _ & HC). cbn [ms_mem restrict] in *. exact HC.
Qed.
(* The merge of the seven paths of the row scan, at 0x81d1c (listing offset 7632):
   a1, a4, a5, a6, a7 become the fresh atoms 113 .. 117. *)
Definition adbz_P : nat -> bool := fun n => negb ((113 <=? n) && (n <=? 117))%nat.
Definition adbz_E (Ex : env) (w11 w14 w15 w16 w17 : word) : env :=
ewset (ewset (ewset (ewset (ewset Ex 113 w11) 114 w14) 115 w15) 116 w16) 117 w17.
Definition adbz_regs (i : Z) : list sv :=
[SLit 0; adJ 1; SOff 2 (-80); SOff 3 0; SOff 4 0; adJ 5; adJ 6; adJ 7;
 SOff 12 0; SOff 11 0; SOff 10 (56 * i); SOff 113 0; SOff 10 (56 * i); SOff 10 (56 * i);
 SOff 114 0; SOff 115 0; SOff 116 0; SOff 117 0;
 SOff 10 0; SOff 10 280; SLit i; adJ 21; SOff 32 0; adS7; adJ 24;
 SOff 25 0; SOff 26 0; SOff 27 0; adJ 28; adJ 29; adJ 30; adJ 31].
Definition adbz (i : Z) : sstate := mkSS 7632 (adbz_regs i) adregions2 None adfacts.
Lemma adbz_agree : forall Ex w11 w14 w15 w16 w17,
env_agree_pd adbz_P PT Ex (adbz_E Ex w11 w14 w15 w16 w17).
Proof.
intros Ex w11 w14 w15 w16 w17. split; [|reflexivity]. intros n Hn.
unfold adbz_P in Hn. apply negb_true_iff, andb_false_iff in Hn.
assert (Hne : (n < 113 \/ 117 < n)%nat)
by (destruct Hn as [H|H]; [apply Nat.leb_gt in H; lia | apply Nat.leb_gt in H; lia]).
unfold adbz_E. rewrite !ew_ewset_other by lia. reflexivity.
Qed.
Lemma adbz_other : forall Ex w11 w14 w15 w16 w17 n, (n < 113)%nat ->
ew (adbz_E Ex w11 w14 w15 w16 w17) n = ew Ex n.
Proof.
intros Ex w11 w14 w15 w16 w17 n Hn. unfold adbz_E. rewrite !ew_ewset_other by lia. reflexivity.
Qed.
Lemma adbz_img : forall Ex w11 w14 w15 w16 w17,
img_env VAL A_LIM Ex -> img_env VAL A_LIM (adbz_E Ex w11 w14 w15 w16 w17).
Proof.
intros Ex w11 w14 w15 w16 w17 HE a Ha. unfold adbz_E.
rewrite !ew_ewset_other by (unfold A_TEXT in Ha; lia). apply HE. exact Ha.
Qed.
Lemma adbz_shok : forall Ex w11 w14 w15 w16 w17 m,
sh_ok SEGS ADBx adSH Ex m -> sh_ok SEGS ADBx adSH (adbz_E Ex w11 w14 w15 w16 w17) m.
Proof.
intros Ex w11 w14 w15 w16 w17 m H.
pose proof (adbz_other Ex w11 w14 w15 w16 w17) as A.
unfold sh_ok, adSH in *.
apply Forall_forall. intros e He. rewrite Forall_forall in H. specialize (H e He).
unfold shent_ok, app_apart, U, ADBx in *.
cbn [sv_denot] in *. rewrite (A 32%nat ltac:(lia)) in *.
destruct He as [<- | [<- | []]]; cbn [she_m she_lo she_hi] in *;
[rewrite (A 10%nat ltac:(lia)) in * | rewrite (A 11%nat ltac:(lia)) in *]; exact H.
Qed.
Lemma adbz_reabs : forall (i : Z) Ex ss msx w11 w14 w15 w16 w17,
0 <= i <= 4 ->
st_ok SEGS Ex ss msx -> reabs_check adbz_P ss (adbz_regs i) adfacts = true ->
ss_mem ss = adregions2 ->
w11 = getr (ms_regs msx) 11 -> w14 = getr (ms_regs msx) 14 -> w15 = getr (ms_regs msx) 15 ->
w16 = getr (ms_regs msx) 16 -> w17 = getr (ms_regs msx) 17 ->
st_ok SEGS (adbz_E Ex w11 w14 w15 w16 w17)
(mkSS (ss_pc ss) (adbz_regs i) adregions2 None adfacts) msx.
Proof.
intros i Ex ss msx w11 w14 w15 w16 w17 Hi HS Hck Hmem Q11 Q14 Q15 Q16 Q17.
assert (Hi5 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
destruct Hi5 as [-> | [-> | [-> | [-> | ->]]]];
(apply (st_ok_reabs SEGS adbz_P Ex _ ss msx _ adregions2 adfacts HS
   (adbz_agree Ex _ _ _ _ _) Hck);
 [ lazymatch goal with |- Forall ?f ?l => let l' := eval vm_compute in l in change l with l' end;
   subst w11 w14 w15 w16 w17;
   repeat (apply Forall_cons; [cbn [ew ewset Nat.eqb fst snd adbz_E]; reflexivity|]); apply Forall_nil
 | lazymatch goal with |- Forall ?f ?l => let l' := eval vm_compute in l in change l with l' end;
   apply Forall_nil
 | rewrite <- Hmem;
   apply (mem_ok_agree_pd SEGS adbz_P PT Ex (adbz_E Ex w11 w14 w15 w16 w17)
            (ms_mem msx) (ss_mem ss) (adbz_agree Ex _ _ _ _ _)
            ltac:(rewrite Hmem; vm_compute; reflexivity));
   exact (st_ok_mem_ok SEGS Ex ss msx HS) ]).
Qed.
(* Reading a register of a state the walk reached, in the atoms of the entry environment. *)
Ltac ad_atg AGx Hx nn Hn :=
lazymatch goal with HS : st_ok_pi _ _ ?Ex _ _ |- _ =>
  assert (Hn : ew Ex nn = _)
  by (cbn [ew ewset Nat.eqb]; rewrite ?ew_havoc_old by (cbv; lia);
      rewrite (AGx nn ltac:(lia)); exact Hx)
end.
Ltac ad_ag113 Eb HN :=
lazymatch goal with
| HS : st_ok_pi _ _ ?Ex _ _ |- _ =>
  assert (HN : forall n : nat, (n < 113)%nat -> ew Ex n = ew Eb n)
  by (let nn := fresh "nn" in let Hnn := fresh "Hnn" in
      intros nn Hnn; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; reflexivity)
| HS : st_ok _ ?Ex _ _ |- _ =>
  assert (HN : forall n : nat, (n < 113)%nat -> ew Ex n = ew Eb n)
  by (let nn := fresh "nn" in let Hnn := fresh "Hnn" in
      intros nn Hnn; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; reflexivity)
end.
Ltac ad_ag113x Eb AGx HN :=
lazymatch goal with
| HS : st_ok_pi _ _ ?Ex _ _ |- _ =>
  assert (HN : env_agree 113 Eb Ex)
  by (split;
      [ let nn := fresh "nn" in let Hnn := fresh "Hnn" in
        intros nn Hnn; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia;
        apply (proj1 AGx); lia
      | cbn [ed ewset]; exact (proj2 AGx) ])
| HS : st_ok _ ?Ex _ _ |- _ =>
  assert (HN : env_agree 113 Eb Ex)
  by (split;
      [ let nn := fresh "nn" in let Hnn := fresh "Hnn" in
        intros nn Hnn; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia;
        apply (proj1 AGx); lia
      | cbn [ed ewset]; exact (proj2 AGx) ])
end.
(* Reading a register of a state the walk reached, in the atoms of the entry environment. *)
Ltac ad_qreg Eb AGx rr :=
  lazymatch goal with
  | HSx : st_ok_pi _ _ ?Ex ?ss (restrict (w_H _) ?msx) |- _ =>
      let Rq := fresh "Rq" in
      pose proof (st_ok_pi_restrict_reg (w_H _) Ex ss msx rr HSx) as Rq;
      let v := eval vm_compute in (sr_get (ss_regs ss) rr) in
      change (sr_get (ss_regs ss) rr) with v in Rq;
      rewrite (sv_denot_agree 113 Eb Ex v AGx
                 ltac:(vm_compute; reflexivity)) in Rq;
      rewrite Rq; clear Rq
  end.
Lemma ad_pres_get : forall (rg rg2 : bvmap 5 word) (x : bv 5) (z : Z),
  aregs_preserved rg rg2 -> bv_unsigned x = z -> acallee_saved z -> getr rg2 x = getr rg x.
Proof.
intros rg rg2 x z HP Hz Hc. rewrite <- Hz in Hc. pose proof (HP (bv_unsigned x) Hc) as H.
rewrite (Z_to_bv_bv_unsigned 5 x) in H. exact H.
Qed.
(* The epilogue, entered at 0x81e2c (listing offset 7904), the slot __asan_memcpy returns to. *)
Lemma ad_tailret : forall ly S W (regs : bvmap 5 word) mem md ch (r k z : Z) (bs M bs' : list byte)
  (rg : bvmap 5 word) (memT : word -> option byte) (mdT : Model),
afn_pre SEGS B REAC_BOXREG_ADD_STK ly S W regs mem md ch ->
ajournal SEGS B REAC_BOXREG_ADD_STK (spZ regs) [(r, r + REG_SIZE)] ly S W mem md [] ly S W memT mdT 0 ->
In (r, REG_SIZE) (ablocks B ly S) ->
adfr regs W memT ->
getr rg 2 = w64 (spZ regs - 80) -> getr rg 20 = w64 z ->
getr rg 3 = getr regs 3 -> getr rg 4 = getr regs 4 ->
getr rg 25 = getr regs 25 -> getr rg 26 = getr regs 26 -> getr rg 27 = getr regs 27 ->
0 <= z <= 4 ->
reac_boxreg_add_c.add_out bs M k z bs' ->
(forall o, 0 <= o < REG_SIZE -> aview SEGS (w_H W) memT (r + o) = Some (adtb bs' o)) ->
SRr SEGS W (mkCfg (mkst rg (Z_to_bv 64 (BASE + 7904)) memT (seg_rom SEGS)) mdT)
  (treac_boxreg_add_post regs ly S W mem md r k bs M).
Proof.
intros ly S W regs mem md ch r k z bs M bs' rg memT mdT HPRE HJ Hin HFR
  Q2 Q20 Q3 Q4 Q25 Q26 Q27 Hz HOUT HBS.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hchn & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOXREG_ADD_STK = 8320) by reflexivity. rewrite WS in Hslo.
pose proof HJ as (J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10 & J11 & J12 & J13 & J14 & J15 & J16 & J17).
destruct (al_blocks _ _ LAWS ly S W memT mdT r REG_SIZE J1 Hin)
  as (Hr16 & Hr4096 & Hrceil & Hrapp & Hrpres & _ & _).
change (req_size REG_SIZE) with 288 in Hrceil.
assert (HRHI : r + 288 <= spZ regs - 8320) by lia.
assert (E1 : ew (adET regs bs M rg) 1 = getr regs 1)
  by (apply (ad_ewr regs bs M rg 1%nat 1%bv eq_refl); lia).
assert (Usp : bv_unsigned (ew (adET regs bs M rg) 2) = spZ regs)
  by (rewrite (ad_ewr regs bs M rg 2%nat 2%bv eq_refl ltac:(lia)); reflexivity).
assert (HEI : img_env VAL A_LIM (adET regs bs M rg)) by (unfold adET; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (adextra bs M)) (adET regs bs M rg)).
{ unfold adET. split; [|reflexivity]. intros n Hn. rewrite Eimg_low by (unfold A_TEXT; lia).
  unfold Ereg. cbn [ew]. replace (n <? 32)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  reflexivity. }
assert (Dsp : sv_denot (adET regs bs M rg) (SOff 2 (-80)) = w64 (spZ regs - 80)).
{ cbn [sv_denot]. rewrite (ad_ewr regs bs M rg 2%nat 2%bv eq_refl ltac:(lia)).
  unfold spZ, w64. f_equal; try lia. }
assert (D3 : sv_denot (adET regs bs M rg) (SOff 3 0) = getr regs 3)
  by (apply (ad_den_keep regs bs M rg 3%nat 3%bv eq_refl); lia).
assert (D4 : sv_denot (adET regs bs M rg) (SOff 4 0) = getr regs 4)
  by (apply (ad_den_keep regs bs M rg 4%nat 4%bv eq_refl); lia).
assert (D25 : sv_denot (adET regs bs M rg) (SOff 25 0) = getr regs 25)
  by (apply (ad_den_keep regs bs M rg 25%nat 25%bv eq_refl); lia).
assert (D26 : sv_denot (adET regs bs M rg) (SOff 26 0) = getr regs 26)
  by (apply (ad_den_keep regs bs M rg 26%nat 26%bv eq_refl); lia).
assert (D27 : sv_denot (adET regs bs M rg) (SOff 27 0) = getr regs 27)
  by (apply (ad_den_keep regs bs M rg 27%nat 27%bv eq_refl); lia).
assert (HRO : regs_ok (adET regs bs M rg) (adtr z) rg).
{ regs_ok_cases_pre ltac:(
    first
    [ rewrite getr_zero; reflexivity
    | lazymatch goal with
      | |- _ = sv_denot _ (SOff ?n 0) =>
          let j := eval vm_compute in (n - 81)%nat in
          rewrite (ad_ewj_den _ _ _ _ n j eq_refl ltac:(lia)); cbn [adrl nth]; reflexivity
      end
    | rewrite Dsp; assumption
    | rewrite D3; assumption | rewrite D4; assumption
    | rewrite D25; assumption | rewrite D26; assumption | rewrite D27; assumption
    | cbn [sv_denot]; assumption ]). }
pose proof (ad_state_tail ly S W regs mem md ch r bs M rg memT mdT 7904 (adtr z)
  HPRE HJ HFR HRO) as HS.
assert (SHOK : sh_ok SEGS ADBx (@nil shent) (adET regs bs M rg) (mrestrict (w_H W) memT))
  by constructor.
assert (KEEP0 : forall a : Z, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 80 <= a < spZ regs) ->
  aview SEGS (w_H W) memT a = aview SEGS (w_H W) memT a) by (intros; reflexivity).
assert (Hz5 : z = 0 \/ z = 1 \/ z = 2 \/ z = 3 \/ z = 4) by lia.
destruct Hz5 as [-> | [-> | [-> | [-> | ->]]]].
- paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
  ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
  ad_ret HS HJ E1 Hra HAE 0 bs'.
  split; [exact HOUT|].
  intros o Ho. change REG_SIZE with 288 in Ho. rewrite KEEP0 by lia. exact (HBS o Ho).
- paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
  ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
  ad_ret HS HJ E1 Hra HAE 1 bs'.
  split; [exact HOUT|].
  intros o Ho. change REG_SIZE with 288 in Ho. rewrite KEEP0 by lia. exact (HBS o Ho).
- paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
  ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
  ad_ret HS HJ E1 Hra HAE 2 bs'.
  split; [exact HOUT|].
  intros o Ho. change REG_SIZE with 288 in Ho. rewrite KEEP0 by lia. exact (HBS o Ho).
- paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
  ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
  ad_ret HS HJ E1 Hra HAE 3 bs'.
  split; [exact HOUT|].
  intros o Ho. change REG_SIZE with 288 in Ho. rewrite KEEP0 by lia. exact (HBS o Ho).
- paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
  ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
  ad_ret HS HJ E1 Hra HAE 4 bs'.
  split; [exact HOUT|].
  intros o Ho. change REG_SIZE with 288 in Ho. rewrite KEEP0 by lia. exact (HBS o Ho).
Qed.
Lemma ad_bindloop : forall (dd : nat) ly S W (regs : bvmap 5 word) mem md ch (r p k : Z) (bs M : list byte)
  (regsT : bvmap 5 word) (memT : word -> option byte) (mdT : Model) (i : Z),
afn_pre SEGS B REAC_BOXREG_ADD_STK ly S W regs mem md ch ->
getr regs 10 = w64 r -> getr regs 11 = w64 p -> getr regs 12 = w64 k -> - 2 ^ 31 <= k < 2 ^ 31 ->
In (r, REG_SIZE) (ablocks B ly S) ->
Boxreg.boxreg_inv bs -> length M = 6%nat -> M <> Boxreg.zero6 ->
reac_boxreg_add_c.add_width_ok k (Boxreg.bx_fabric bs) ->
reac_boxreg_add_c.add_none_held bs M ->
(Z.to_nat (Boxreg.bx_n bs - i) <= dd)%nat ->
0 <= i < Boxreg.bx_n bs ->
(forall j, 0 <= j < i -> ~ (Boxreg.bx_mac bs j = Boxreg.zero6 /\ Boxreg.bx_nch bs j = k)) ->
getr regsT 2 = w64 (spZ regs - 80) -> getr regsT 3 = getr regs 3 -> getr regsT 4 = getr regs 4 ->
getr regsT 8 = w64 k -> getr regsT 9 = w64 p ->
getr regsT 12 = w64 (r + 56 * i) -> getr regsT 13 = w64 (r + 56 * i) ->
getr regsT 18 = w64 r -> getr regsT 19 = w64 (r + 280) -> getr regsT 20 = w64 i ->
getr regsT 22 = w64 ADSB -> getr regsT 23 = w64 (ADSB + (r + 280) / 8) ->
getr regsT 24 = w64 (Boxreg.bx_n bs) ->
getr regsT 25 = getr regs 25 -> getr regsT 26 = getr regs 26 -> getr regsT 27 = getr regs 27 ->
adfr regs W memT ->
(forall o, 0 <= o < REG_SIZE -> aview SEGS (w_H W) memT (r + o) = Some (adtb bs o)) ->
afobj SEGS B ly S W memT p 6 ->
(forall o, 0 <= o < 6 -> aview SEGS (w_H W) memT (p + o) = Some (adtb M o)) ->
ajournal SEGS B REAC_BOXREG_ADD_STK (spZ regs) [(r, r + REG_SIZE)] ly S W mem md [] ly S W memT mdT 0 ->
(forall (regsT' : bvmap 5 word) (memT' : word -> option byte) (mdT' : Model),
   getr regsT' 2 = w64 (spZ regs - 80) -> getr regsT' 3 = getr regs 3 -> getr regsT' 4 = getr regs 4 ->
   getr regsT' 8 = w64 k -> getr regsT' 9 = w64 p ->
   getr regsT' 18 = w64 r -> getr regsT' 19 = w64 (r + 280) ->
   getr regsT' 22 = w64 ADSB -> getr regsT' 23 = w64 (ADSB + (r + 280) / 8) ->
   getr regsT' 24 = w64 (Boxreg.bx_n bs) ->
   getr regsT' 25 = getr regs 25 -> getr regsT' 26 = getr regs 26 -> getr regsT' 27 = getr regs 27 ->
   adfr regs W memT' ->
   (forall o, 0 <= o < REG_SIZE -> aview SEGS (w_H W) memT' (r + o) = Some (adtb bs o)) ->
   afobj SEGS B ly S W memT' p 6 ->
   (forall o, 0 <= o < 6 -> aview SEGS (w_H W) memT' (p + o) = Some (adtb M o)) ->
   ajournal SEGS B REAC_BOXREG_ADD_STK (spZ regs) [(r, r + REG_SIZE)] ly S W mem md []
     ly S W memT' mdT' 0 ->
   reac_boxreg_add_c.add_none_unbound bs k -> 0 <= Boxreg.bx_n bs <= 4 ->
   SRr SEGS W (mkCfg (mkst regsT' (Z_to_bv 64 (BASE + 7748)) memT' (seg_rom SEGS)) mdT')
     (treac_boxreg_add_post regs ly S W mem md r k bs M)) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (BASE + 7512)) memT (seg_rom SEGS)) mdT)
  (treac_boxreg_add_post regs ly S W mem md r k bs M).
Proof.
induction dd as [|dd IH]; intros ly S W regs mem md ch r p k bs M regsT memT mdT i
  HPRE H10 H11 H12 Hk Hin Hinv HML HMnz HWO HNH Hdd Hi HINV
  R2 R3 R4 R8 R9 R12 R13 R18 R19 R20 R22 R23 R24 R25 R26 R27 HFR Hbs HFO HMv HJ CONT.
- exfalso. lia.
- pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
  pose proof Hinv as Hinv2.
  destruct Hinv2 as ((HLbs & HB1 & HB2 & HB3 & HB4 & HB5 & HB6) & HB7).
  unfold Boxreg.boxreg_B1 in HB1.
  pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hchn & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  assert (WS : REAC_BOXREG_ADD_STK = 8320) by reflexivity. rewrite WS in Hslo.
  pose proof HJ as (J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10 & J11 & J12 & J13 & J14 & J15 & J16 & J17).
  destruct (al_blocks _ _ LAWS ly S W memT mdT r REG_SIZE J1 Hin)
    as (Hr16 & Hr4096 & Hrceil & Hrapp & Hrpres & _ & _).
  change (req_size REG_SIZE) with 288 in Hrceil, Hrapp, Hrpres.
  assert (HRHI : r + 288 <= spZ regs - 8320) by lia.
  pose proof HFO as ((cid & pos & Hfin & Hcid & Hfal & Hflo & Hfhi) & Hp8 & HRA).
  destruct (frames_bounds SEGS B LAWS ly S W memT mdT cid pos J1 Hfin) as (Hf4096 & Hfceil & Hfapp).
  pose proof (sep_block_frame SEGS B LAWS ly S W memT mdT r REG_SIZE cid pos J1 Hin Hfin) as Hrf.
  unfold zdisjoint in Hrf. cbn [fst snd] in Hrf. change (req_size REG_SIZE) with 288 in Hrf.
  assert (E1 : ew (adET regs bs M regsT) 1 = getr regs 1)
    by (apply (ad_ewr regs bs M regsT 1%nat 1%bv eq_refl); lia).
  assert (Usp : bv_unsigned (ew (adET regs bs M regsT) 2) = spZ regs)
    by (rewrite (ad_ewr regs bs M regsT 2%nat 2%bv eq_refl ltac:(lia)); reflexivity).
  assert (HEI : img_env VAL A_LIM (adET regs bs M regsT)) by (unfold adET; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (adextra bs M)) (adET regs bs M regsT)).
  { unfold adET. split; [|reflexivity]. intros n Hn. rewrite Eimg_low by (unfold A_TEXT; lia).
    unfold Ereg. cbn [ew]. replace (n <? 32)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    reflexivity. }
  assert (Dsp : sv_denot (adET regs bs M regsT) (SOff 2 (-80)) = w64 (spZ regs - 80)).
  { cbn [sv_denot]. rewrite (ad_ewr regs bs M regsT 2%nat 2%bv eq_refl ltac:(lia)).
    unfold spZ, w64. f_equal; try lia. }
  assert (D3 : sv_denot (adET regs bs M regsT) (SOff 3 0) = getr regs 3)
    by (apply (ad_den_keep regs bs M regsT 3%nat 3%bv eq_refl); lia).
  assert (D4 : sv_denot (adET regs bs M regsT) (SOff 4 0) = getr regs 4)
    by (apply (ad_den_keep regs bs M regsT 4%nat 4%bv eq_refl); lia).
  assert (D25 : sv_denot (adET regs bs M regsT) (SOff 25 0) = getr regs 25)
    by (apply (ad_den_keep regs bs M regsT 25%nat 25%bv eq_refl); lia).
  assert (D26 : sv_denot (adET regs bs M regsT) (SOff 26 0) = getr regs 26)
    by (apply (ad_den_keep regs bs M regsT 26%nat 26%bv eq_refl); lia).
  assert (D27 : sv_denot (adET regs bs M regsT) (SOff 27 0) = getr regs 27)
    by (apply (ad_den_keep regs bs M regsT 27%nat 27%bv eq_refl); lia).
  assert (Dk : sv_denot (adET regs bs M regsT) (SOff 12 0) = w64 k)
    by (rewrite (ad_den_keep regs bs M regsT 12%nat 12%bv eq_refl ltac:(lia)); exact H12).
  assert (Dp : sv_denot (adET regs bs M regsT) (SOff 11 0) = w64 p)
    by (rewrite (ad_den_keep regs bs M regsT 11%nat 11%bv eq_refl ltac:(lia)); exact H11).
  assert (Dr : forall z, sv_denot (adET regs bs M regsT) (SOff 10 z) = w64 (r + z))
    by (intros z; apply (ad_den_atom regs bs M regsT 10%nat 10%bv r eq_refl ltac:(lia) H10 ltac:(lia))).
  assert (D32 : sv_denot (adET regs bs M regsT) (SOff 32 0) = w64 ADSB).
  { cbn [sv_denot]. rewrite (ad_ewx regs bs M regsT 32%nat 0%nat eq_refl ltac:(lia)).
    unfold adextra. cbn [map nth app adrowv]. rewrite unsigned_lit_small by (unfold ADSB; lia).
    unfold w64. f_equal; try lia. }
  assert (D7 : sv_denot (adET regs bs M regsT)
      (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 280) (SLit 3)) (SOff 32 0)) = w64 (ADSB + (r + 280) / 8)).
  { rewrite (denot_lit_U (adET regs bs M regsT)), U_SAlu. cbn [zalu_raw].
    rewrite U_SAlu. cbn [zalu_raw].
    rewrite (U_atom (adET regs bs M regsT) 32 ADSB
      ltac:(rewrite (ad_ewx regs bs M regsT 32%nat 0%nat eq_refl ltac:(lia));
            unfold adextra; cbn [map nth app adrowv]; reflexivity) ltac:(unfold ADSB; lia)).
    rewrite U_SOff, U_SLit,
      (ad_ewr regs bs M regsT 10%nat 10%bv eq_refl ltac:(lia)), H10.
    unfold w64 at 1. rewrite unsigned_lit_small by lia.
    replace (zcanon 3) with 3 by reflexivity. change (Z.land 3 63) with 3.
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    unfold zcanon, M64, w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64).
    rewrite !Z.mod_mod by lia.
    assert (Hq : (r + 280) mod 2 ^ 64 = r + 280) by (apply Z.mod_small; lia).
    rewrite Hq. f_equal; try lia. }
  assert (E12a : ew (adET regs bs M regsT) 12 = Z_to_bv 64 k)
    by (rewrite (ad_ewr regs bs M regsT 12%nat 12%bv eq_refl ltac:(lia)); exact H12).
  assert (E105 : ew (adET regs bs M regsT) 105 = Z_to_bv 64 (Boxreg.bx_n bs))
    by (rewrite (ad_ewj regs bs M regsT 105%nat 24%nat eq_refl ltac:(lia));
        cbn [adrl nth]; exact R24).
  assert (E33 : ew (adET regs bs M regsT) 33 = Z_to_bv 64 (ad4 bs 280))
    by (rewrite (ad_ewx regs bs M regsT 33%nat 1%nat eq_refl ltac:(lia));
        unfold adextra, adrowv; cbn [map app nth]; reflexivity).
  assert (HRO : regs_ok (adET regs bs M regsT) (adsr i) regsT).
  { regs_ok_cases_pre ltac:(
      first
      [ rewrite getr_zero; reflexivity
      | lazymatch goal with
        | |- _ = sv_denot _ (SOff ?n 0) =>
            let j := eval vm_compute in (n - 81)%nat in
            rewrite (ad_ewj_den _ _ _ _ n j eq_refl ltac:(lia)); cbn [adrl nth]; reflexivity
        end
      | rewrite Dsp; assumption
      | rewrite D3; assumption | rewrite D4; assumption
      | rewrite D25; assumption | rewrite D26; assumption | rewrite D27; assumption
      | rewrite Dk; assumption | rewrite Dp; assumption
      | rewrite D32; assumption | rewrite D7; assumption
      | rewrite Dr; rewrite ?Z.add_0_r; assumption
      | cbn [sv_denot]; assumption ]). }
  destruct (ad_state ly S W regs mem md ch r p bs M regsT memT mdT 7512 (adsr i)
    HPRE HJ H10 H11 Hin Hbs HFO HMv HFR HRO) as [HS SHOK].
  assert (KEEP0 : forall a : Z, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 80 <= a < spZ regs) ->
    aview SEGS (w_H W) memT a = aview SEGS (w_H W) memT a) by (intros; reflexivity).
  assert (Hi5 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
  destruct Hi5 as [-> | [-> | [-> | [-> | ->]]]].
  + (* ---------------- row 0 ---------------- *)
    assert (EB0 : ew (adET regs bs M regsT) 35%nat = Z_to_bv 64 (adtb bs (56 * 0 + 0)))
      by (rewrite (ad_ewx regs bs M regsT 35%nat 3%nat eq_refl ltac:(lia));
          unfold adextra, adrowv; cbn [map app nth]; reflexivity).
    assert (EB1 : ew (adET regs bs M regsT) 36%nat = Z_to_bv 64 (adtb bs (56 * 0 + 1)))
      by (rewrite (ad_ewx regs bs M regsT 36%nat 4%nat eq_refl ltac:(lia));
          unfold adextra, adrowv; cbn [map app nth]; reflexivity).
    assert (EB2 : ew (adET regs bs M regsT) 37%nat = Z_to_bv 64 (adtb bs (56 * 0 + 2)))
      by (rewrite (ad_ewx regs bs M regsT 37%nat 5%nat eq_refl ltac:(lia));
          unfold adextra, adrowv; cbn [map app nth]; reflexivity).
    assert (EB3 : ew (adET regs bs M regsT) 38%nat = Z_to_bv 64 (adtb bs (56 * 0 + 3)))
      by (rewrite (ad_ewx regs bs M regsT 38%nat 6%nat eq_refl ltac:(lia));
          unfold adextra, adrowv; cbn [map app nth]; reflexivity).
    assert (EB4 : ew (adET regs bs M regsT) 39%nat = Z_to_bv 64 (adtb bs (56 * 0 + 4)))
      by (rewrite (ad_ewx regs bs M regsT 39%nat 7%nat eq_refl ltac:(lia));
          unfold adextra, adrowv; cbn [map app nth]; reflexivity).
    assert (EB5 : ew (adET regs bs M regsT) 40%nat = Z_to_bv 64 (adtb bs (56 * 0 + 5)))
      by (rewrite (ad_ewx regs bs M regsT 40%nat 8%nat eq_refl ltac:(lia));
          unfold adextra, adrowv; cbn [map app nth]; reflexivity).
    assert (ENC : ew (adET regs bs M regsT) 41%nat = Z_to_bv 64 (ad4 bs (56 * 0 + 12)))
      by (rewrite (ad_ewx regs bs M regsT 41%nat 9%nat eq_refl ltac:(lia));
          unfold adextra, adrowv; cbn [map app nth]; reflexivity).
    assert (NEXT : forall (E' : env) (ms' : machine_state) (md' : Model),
      st_ok_pi SEGS VAL E' (adbz 0) (restrict (w_H W) ms') ->
      sh_ok SEGS ADBx adSH E' (mrestrict (w_H W) (ms_mem ms')) ->
      img_env VAL A_LIM E' ->
      ajournal SEGS B REAC_BOXREG_ADD_STK (spZ regs) [(r, r + REG_SIZE)] ly S W mem md []
        ly S W (ms_mem ms') md' 0 ->
      (forall a : Z, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 80 <= a < spZ regs) ->
         aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) memT a) ->
      env_agree 113 (adET regs bs M regsT) E' ->
      ~ (Boxreg.bx_mac bs 0 = Boxreg.zero6 /\ Boxreg.bx_nch bs 0 = k) ->
      SRr SEGS W (mkCfg ms' md') (treac_boxreg_add_post regs ly S W mem md r k bs M)).
    { clear HS SHOK KEEP0.
      intros E' ms' md' HSn SHOKn HEIn HJn KEEPn AGe FACT.
      pose proof (proj1 AGe) as AG.
      assert (Usp' : bv_unsigned (ew E' 2) = spZ regs) by (rewrite (AG 2%nat ltac:(lia)); exact Usp).
      assert (E1' : ew E' 1 = getr regs 1) by (rewrite (AG 1%nat ltac:(lia)); exact E1).
      assert (HAE' : env_agree 32 (Ereg regs (adextra bs M)) E')
        by (eapply env_agree_trans;
            [exact HAE | split; [intros nn Hnn; apply AG; lia | exact (proj2 AGe)]]).
      paj_run_tok RUN HSn HJn SHOKn ADspan; [awr_ok_tac; exact Usp' |].
      ad_upd KEEPn Usp' W (spZ regs - 80) (spZ regs).
      psrr_branch_tok RUN BR HSn SHOKn ADspan.
      { (* i + 1 <> n: the next row *)
        ad_atg AG E105 105%nat E105a.
        rewrite (ad_bne_lit _ 1 105%nat (Boxreg.bx_n bs) E105a ltac:(lia) ltac:(lia)) in Hc.
        apply negb_true_iff, Z.eqb_neq in Hc.
        paj_run_to_tok RUNTO HSn HJn SHOKn ADspan 7512; [awr_ok_tac; exact Usp' |].
        ad_upd KEEPn Usp' W (spZ regs - 80) (spZ regs).
        ad_ag113x (adET regs bs M regsT) AGe AGn.
        pmkst HSn.
        refine (IH ly S W regs mem md ch r p k bs M _ _ _ 1
          HPRE H10 H11 H12 Hk Hin Hinv HML HMnz HWO HNH _ _ _
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CONT).
        - lia.
        - lia.
        - intros j Hj. destruct (Z.eq_dec j 0) as [->|Hne]; [exact FACT | apply HINV; lia].
        - ad_qreg (adET regs bs M regsT) AGn (2%bv : bv 5). exact Dsp.
        - ad_qreg (adET regs bs M regsT) AGn (3%bv : bv 5). exact D3.
        - ad_qreg (adET regs bs M regsT) AGn (4%bv : bv 5). exact D4.
        - ad_qreg (adET regs bs M regsT) AGn (8%bv : bv 5). exact Dk.
        - ad_qreg (adET regs bs M regsT) AGn (9%bv : bv 5). exact Dp.
        - ad_qreg (adET regs bs M regsT) AGn (12%bv : bv 5). rewrite Dr. unfold w64. f_equal; try lia.
        - ad_qreg (adET regs bs M regsT) AGn (13%bv : bv 5). rewrite Dr. unfold w64. f_equal; try lia.
        - ad_qreg (adET regs bs M regsT) AGn (18%bv : bv 5). rewrite Dr. unfold w64. f_equal; try lia.
        - ad_qreg (adET regs bs M regsT) AGn (19%bv : bv 5). rewrite Dr. unfold w64. f_equal; try lia.
        - ad_qreg (adET regs bs M regsT) AGn (20%bv : bv 5). cbn [sv_denot]. unfold w64. f_equal; try lia.
        - ad_qreg (adET regs bs M regsT) AGn (22%bv : bv 5). exact D32.
        - ad_qreg (adET regs bs M regsT) AGn (23%bv : bv 5). exact D7.
        - ad_qreg (adET regs bs M regsT) AGn (24%bv : bv 5).
          rewrite (ad_ewj_den regs bs M regsT 105%nat 24%nat eq_refl ltac:(lia)).
          cbn [adrl nth]. exact R24.
        - ad_qreg (adET regs bs M regsT) AGn (25%bv : bv 5). exact D25.
        - ad_qreg (adET regs bs M regsT) AGn (26%bv : bv 5). exact D26.
        - ad_qreg (adET regs bs M regsT) AGn (27%bv : bv 5). exact D27.
        - eapply ad_frame_of_st;
            [ exact HSn | reflexivity | rewrite ((proj1 AGn) 2%nat ltac:(lia)); exact Usp
            | intros nn x Hnn Hx; rewrite ((proj1 AGn) nn ltac:(lia));
              apply (ad_ewr regs bs M regsT nn x Hx Hnn) ].
        - intros o Ho. change REG_SIZE with 288 in Ho. rewrite KEEPn by lia. exact (Hbs o Ho).
        - lazymatch goal with |- afobj _ _ _ _ _ ?mx _ _ =>
            apply (ad_afobj_keep W ly S memT mx p (spZ regs - 80) (spZ regs) HFO KEEPn) end.
          intros x Hx. apply (adb_shadow_out regs ly p C1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) x Hx).
        - intros o Ho. rewrite KEEPn by lia. exact (HMv o Ho).
        - exact HJn. }
      { (* i + 1 = n: the loop is over *)
        ad_atg AG E105 105%nat E105a.
        rewrite (ad_bne_lit _ 1 105%nat (Boxreg.bx_n bs) E105a ltac:(lia) ltac:(lia)) in Hc.
        apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HEQn.
        paj_run_tok RUN HSn HJn SHOKn ADspan; [awr_ok_tac; exact Usp' |].
        ad_upd KEEPn Usp' W (spZ regs - 80) (spZ regs).
        psrr_branch_tok RUN BR HSn SHOKn ADspan.
        { (* n <= 4: the new-row tail at 0x81d90 *)
          ad_atg AG E33 33%nat E33a.
          rewrite (ad_bge4 _ 33%nat (ad4 bs 280) E33a (ad_4_rng bs 280)) in Hc.
          apply negb_true_iff, Z.ltb_ge in Hc. rewrite <- (ad_bx_n bs HLbs) in Hc.
          paj_run_to_tok RUNTO HSn HJn SHOKn ADspan 7748; [awr_ok_tac; exact Usp' |].
          ad_upd KEEPn Usp' W (spZ regs - 80) (spZ regs).
          ad_ag113x (adET regs bs M regsT) AGe AGn.
          pmkst HSn.
          refine (CONT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
          - ad_qreg (adET regs bs M regsT) AGn (2%bv : bv 5). exact Dsp.
          - ad_qreg (adET regs bs M regsT) AGn (3%bv : bv 5). exact D3.
          - ad_qreg (adET regs bs M regsT) AGn (4%bv : bv 5). exact D4.
          - ad_qreg (adET regs bs M regsT) AGn (8%bv : bv 5). exact Dk.
          - ad_qreg (adET regs bs M regsT) AGn (9%bv : bv 5). exact Dp.
          - ad_qreg (adET regs bs M regsT) AGn (18%bv : bv 5). rewrite Dr. unfold w64. f_equal; try lia.
          - ad_qreg (adET regs bs M regsT) AGn (19%bv : bv 5). rewrite Dr. unfold w64. f_equal; try lia.
          - ad_qreg (adET regs bs M regsT) AGn (22%bv : bv 5). exact D32.
          - ad_qreg (adET regs bs M regsT) AGn (23%bv : bv 5). exact D7.
          - ad_qreg (adET regs bs M regsT) AGn (24%bv : bv 5).
            rewrite (ad_sext_den (adET regs bs M regsT) 33%nat (ad4 bs 280) E33 (ad_4_rng bs 280)).
            rewrite <- (ad_bx_n bs HLbs). reflexivity.
          - ad_qreg (adET regs bs M regsT) AGn (25%bv : bv 5). exact D25.
          - ad_qreg (adET regs bs M regsT) AGn (26%bv : bv 5). exact D26.
          - ad_qreg (adET regs bs M regsT) AGn (27%bv : bv 5). exact D27.
          - eapply ad_frame_of_st;
              [ exact HSn | reflexivity | rewrite ((proj1 AGn) 2%nat ltac:(lia)); exact Usp
              | intros nn x Hnn Hx; rewrite ((proj1 AGn) nn ltac:(lia));
                apply (ad_ewr regs bs M regsT nn x Hx Hnn) ].
          - intros o Ho. change REG_SIZE with 288 in Ho. rewrite KEEPn by lia. exact (Hbs o Ho).
          - lazymatch goal with |- afobj _ _ _ _ _ ?mx _ _ =>
              apply (ad_afobj_keep W ly S memT mx p (spZ regs - 80) (spZ regs) HFO KEEPn) end.
            intros x Hx. apply (adb_shadow_out regs ly p C1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) x Hx).
          - intros o Ho. rewrite KEEPn by lia. exact (HMv o Ho).
          - exact HJn.
          - intros j Hj. destruct (Z.eq_dec j 0) as [->|Hne]; [exact FACT | apply HINV; lia].
          - lia. }
        { (* 5 <= n: the function returns -1 *)
          ad_atg AG E33 33%nat E33a.
          rewrite (ad_bge4 _ 33%nat (ad4 bs 280) E33a (ad_4_rng bs 280)) in Hc.
          apply negb_false_iff, Z.ltb_lt in Hc. rewrite <- (ad_bx_n bs HLbs) in Hc.
          paj_run_tok RUN HSn HJn SHOKn ADspan; [awr_ok_tac; exact Usp' |].
          ad_upd KEEPn Usp' W (spZ regs - 80) (spZ regs).
          ad_ret HSn HJn E1' Hra HAE' (-1) bs.
          split.
          - right. right. right. left.
            split; [exact HWO|]. split; [exact HMnz|]. split; [exact HNH|].
            split; [intros j Hj; destruct (Z.eq_dec j 0) as [->|Hne];
                    [exact FACT | apply HINV; lia]|].
            split; [left; lia|]. split; reflexivity.
          - intros o Ho. change REG_SIZE with 288 in Ho. rewrite KEEPn by lia. exact (Hbs o Ho). } } }
    paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
    ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
    psrr_branch_tok RUN BR HS SHOK ADspan.
    { (* the MAC byte 0 of the row is not zero *)
      ad_at EB0 35%nat EBa0.
      rewrite (ad_bnz_b _ 35%nat bs (56 * 0 + 0) EBa0) in Hc.
      apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into HNZ.
      paj_run_to_tok RUNTO HS HJ SHOK ADspan 7632; [awr_ok_tac; exact Usp |].
      ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
      ad_ag113 (adET regs bs M regsT) AGx;
                lazymatch goal with
                | HSx : st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?Wx) ?msx) |- _ =>
                  pose proof (adbz_reabs 0 Ex (abs_ss VAL ss) (restrict (w_H Wx) msx)
                    (getr (ms_regs (restrict (w_H Wx) msx)) 11) (getr (ms_regs (restrict (w_H Wx) msx)) 14)
                    (getr (ms_regs (restrict (w_H Wx) msx)) 15) (getr (ms_regs (restrict (w_H Wx) msx)) 16)
                    (getr (ms_regs (restrict (w_H Wx) msx)) 17)
                    ltac:(lia) HSx ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                    eq_refl eq_refl eq_refl eq_refl eq_refl) as HSm
                end;
                apply (NEXT _ _ _ HSm
                  ltac:(apply adbz_shok; exact SHOK) ltac:(apply adbz_img; assumption)
                  HJ KEEP0
                  ltac:(split;
                        [ intros nn Hnn; rewrite (adbz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn
                        | reflexivity ])
                  ltac:(intros Hzz; apply HNZ;
                  exact (proj1 (ad_mac_zero bs 0 HLbs ltac:(lia)) (proj1 Hzz) 0 ltac:(lia)))). }
    { (* the MAC byte 0 of the row is zero *)
      ad_at EB0 35%nat EBz0.
      rewrite (ad_bnz_b _ 35%nat bs (56 * 0 + 0) EBz0) in Hc.
      apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HZ0.
      paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
      ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
      psrr_branch_tok RUN BR HS SHOK ADspan.
      { (* the MAC byte 1 of the row is not zero *)
        ad_at EB1 36%nat EBa1.
        rewrite (ad_bnz_b _ 36%nat bs (56 * 0 + 1) EBa1) in Hc.
        apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into HNZ.
        paj_run_to_tok RUNTO HS HJ SHOK ADspan 7632; [awr_ok_tac; exact Usp |].
        ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
        ad_ag113 (adET regs bs M regsT) AGx;
                  lazymatch goal with
                  | HSx : st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?Wx) ?msx) |- _ =>
                    pose proof (adbz_reabs 0 Ex (abs_ss VAL ss) (restrict (w_H Wx) msx)
                      (getr (ms_regs (restrict (w_H Wx) msx)) 11) (getr (ms_regs (restrict (w_H Wx) msx)) 14)
                      (getr (ms_regs (restrict (w_H Wx) msx)) 15) (getr (ms_regs (restrict (w_H Wx) msx)) 16)
                      (getr (ms_regs (restrict (w_H Wx) msx)) 17)
                      ltac:(lia) HSx ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                      eq_refl eq_refl eq_refl eq_refl eq_refl) as HSm
                  end;
                  apply (NEXT _ _ _ HSm
                    ltac:(apply adbz_shok; exact SHOK) ltac:(apply adbz_img; assumption)
                    HJ KEEP0
                    ltac:(split;
                          [ intros nn Hnn; rewrite (adbz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn
                          | reflexivity ])
                    ltac:(intros Hzz; apply HNZ;
                    exact (proj1 (ad_mac_zero bs 0 HLbs ltac:(lia)) (proj1 Hzz) 1 ltac:(lia)))). }
      { (* the MAC byte 1 of the row is zero *)
        ad_at EB1 36%nat EBz1.
        rewrite (ad_bnz_b _ 36%nat bs (56 * 0 + 1) EBz1) in Hc.
        apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HZ1.
        paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
        ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
        psrr_branch_tok RUN BR HS SHOK ADspan.
        { (* the MAC byte 2 of the row is not zero *)
          ad_at EB2 37%nat EBa2.
          rewrite (ad_bnz_b _ 37%nat bs (56 * 0 + 2) EBa2) in Hc.
          apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into HNZ.
          paj_run_to_tok RUNTO HS HJ SHOK ADspan 7632; [awr_ok_tac; exact Usp |].
          ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
          ad_ag113 (adET regs bs M regsT) AGx;
                    lazymatch goal with
                    | HSx : st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?Wx) ?msx) |- _ =>
                      pose proof (adbz_reabs 0 Ex (abs_ss VAL ss) (restrict (w_H Wx) msx)
                        (getr (ms_regs (restrict (w_H Wx) msx)) 11) (getr (ms_regs (restrict (w_H Wx) msx)) 14)
                        (getr (ms_regs (restrict (w_H Wx) msx)) 15) (getr (ms_regs (restrict (w_H Wx) msx)) 16)
                        (getr (ms_regs (restrict (w_H Wx) msx)) 17)
                        ltac:(lia) HSx ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                        eq_refl eq_refl eq_refl eq_refl eq_refl) as HSm
                    end;
                    apply (NEXT _ _ _ HSm
                      ltac:(apply adbz_shok; exact SHOK) ltac:(apply adbz_img; assumption)
                      HJ KEEP0
                      ltac:(split;
                            [ intros nn Hnn; rewrite (adbz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn
                            | reflexivity ])
                      ltac:(intros Hzz; apply HNZ;
                      exact (proj1 (ad_mac_zero bs 0 HLbs ltac:(lia)) (proj1 Hzz) 2 ltac:(lia)))). }
        { (* the MAC byte 2 of the row is zero *)
          ad_at EB2 37%nat EBz2.
          rewrite (ad_bnz_b _ 37%nat bs (56 * 0 + 2) EBz2) in Hc.
          apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HZ2.
          paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
          ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
          psrr_branch_tok RUN BR HS SHOK ADspan.
          { (* the MAC byte 3 of the row is not zero *)
            ad_at EB3 38%nat EBa3.
            rewrite (ad_bnz_b _ 38%nat bs (56 * 0 + 3) EBa3) in Hc.
            apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into HNZ.
            paj_run_to_tok RUNTO HS HJ SHOK ADspan 7632; [awr_ok_tac; exact Usp |].
            ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
            ad_ag113 (adET regs bs M regsT) AGx;
                      lazymatch goal with
                      | HSx : st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?Wx) ?msx) |- _ =>
                        pose proof (adbz_reabs 0 Ex (abs_ss VAL ss) (restrict (w_H Wx) msx)
                          (getr (ms_regs (restrict (w_H Wx) msx)) 11) (getr (ms_regs (restrict (w_H Wx) msx)) 14)
                          (getr (ms_regs (restrict (w_H Wx) msx)) 15) (getr (ms_regs (restrict (w_H Wx) msx)) 16)
                          (getr (ms_regs (restrict (w_H Wx) msx)) 17)
                          ltac:(lia) HSx ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                          eq_refl eq_refl eq_refl eq_refl eq_refl) as HSm
                      end;
                      apply (NEXT _ _ _ HSm
                        ltac:(apply adbz_shok; exact SHOK) ltac:(apply adbz_img; assumption)
                        HJ KEEP0
                        ltac:(split;
                              [ intros nn Hnn; rewrite (adbz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn
                              | reflexivity ])
                        ltac:(intros Hzz; apply HNZ;
                        exact (proj1 (ad_mac_zero bs 0 HLbs ltac:(lia)) (proj1 Hzz) 3 ltac:(lia)))). }
          { (* the MAC byte 3 of the row is zero *)
            ad_at EB3 38%nat EBz3.
            rewrite (ad_bnz_b _ 38%nat bs (56 * 0 + 3) EBz3) in Hc.
            apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HZ3.
            paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
            ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
            psrr_branch_tok RUN BR HS SHOK ADspan.
            { (* the MAC byte 4 of the row is not zero *)
              ad_at EB4 39%nat EBa4.
              rewrite (ad_bnz_b _ 39%nat bs (56 * 0 + 4) EBa4) in Hc.
              apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into HNZ.
              paj_run_to_tok RUNTO HS HJ SHOK ADspan 7632; [awr_ok_tac; exact Usp |].
              ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
              ad_ag113 (adET regs bs M regsT) AGx;
                        lazymatch goal with
                        | HSx : st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?Wx) ?msx) |- _ =>
                          pose proof (adbz_reabs 0 Ex (abs_ss VAL ss) (restrict (w_H Wx) msx)
                            (getr (ms_regs (restrict (w_H Wx) msx)) 11) (getr (ms_regs (restrict (w_H Wx) msx)) 14)
                            (getr (ms_regs (restrict (w_H Wx) msx)) 15) (getr (ms_regs (restrict (w_H Wx) msx)) 16)
                            (getr (ms_regs (restrict (w_H Wx) msx)) 17)
                            ltac:(lia) HSx ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                            eq_refl eq_refl eq_refl eq_refl eq_refl) as HSm
                        end;
                        apply (NEXT _ _ _ HSm
                          ltac:(apply adbz_shok; exact SHOK) ltac:(apply adbz_img; assumption)
                          HJ KEEP0
                          ltac:(split;
                                [ intros nn Hnn; rewrite (adbz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn
                                | reflexivity ])
                          ltac:(intros Hzz; apply HNZ;
                          exact (proj1 (ad_mac_zero bs 0 HLbs ltac:(lia)) (proj1 Hzz) 4 ltac:(lia)))). }
            { (* the MAC byte 4 of the row is zero *)
              ad_at EB4 39%nat EBz4.
              rewrite (ad_bnz_b _ 39%nat bs (56 * 0 + 4) EBz4) in Hc.
              apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HZ4.
              paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
              ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
              psrr_branch_tok RUN BR HS SHOK ADspan.
              { (* the MAC byte 5 of the row is not zero *)
                ad_at EB5 40%nat EBa5.
                rewrite (ad_bnz_b _ 40%nat bs (56 * 0 + 5) EBa5) in Hc.
                apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into HNZ.
                paj_run_to_tok RUNTO HS HJ SHOK ADspan 7632; [awr_ok_tac; exact Usp |].
                ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
                ad_ag113 (adET regs bs M regsT) AGx;
                          lazymatch goal with
                          | HSx : st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?Wx) ?msx) |- _ =>
                            pose proof (adbz_reabs 0 Ex (abs_ss VAL ss) (restrict (w_H Wx) msx)
                              (getr (ms_regs (restrict (w_H Wx) msx)) 11) (getr (ms_regs (restrict (w_H Wx) msx)) 14)
                              (getr (ms_regs (restrict (w_H Wx) msx)) 15) (getr (ms_regs (restrict (w_H Wx) msx)) 16)
                              (getr (ms_regs (restrict (w_H Wx) msx)) 17)
                              ltac:(lia) HSx ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                              eq_refl eq_refl eq_refl eq_refl eq_refl) as HSm
                          end;
                          apply (NEXT _ _ _ HSm
                            ltac:(apply adbz_shok; exact SHOK) ltac:(apply adbz_img; assumption)
                            HJ KEEP0
                            ltac:(split;
                                  [ intros nn Hnn; rewrite (adbz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn
                                  | reflexivity ])
                            ltac:(intros Hzz; apply HNZ;
                            exact (proj1 (ad_mac_zero bs 0 HLbs ltac:(lia)) (proj1 Hzz) 5 ltac:(lia)))). }
              { (* the MAC byte 5 of the row is zero *)
                ad_at EB5 40%nat EBz5.
                rewrite (ad_bnz_b _ 40%nat bs (56 * 0 + 5) EBz5) in Hc.
                apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HZ5.
                paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
                ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
                assert (HMZ : Boxreg.bx_mac bs 0 = Boxreg.zero6).
                { apply (proj2 (ad_mac_zero bs 0 HLbs ltac:(lia))). intros jj Hjj.
                  assert (Hj6 : jj = 0 \/ jj = 1 \/ jj = 2 \/ jj = 3 \/ jj = 4 \/ jj = 5) by lia.
                  destruct Hj6 as [-> | [-> | [-> | [-> | [-> | ->]]]]];
                    [exact HZ0 | exact HZ1 | exact HZ2 | exact HZ3 | exact HZ4 | exact HZ5]. }
                ad_at ENC 41%nat ENCa. ad_at E12a 12%nat E12b.
                psrr_branch_tok RUN BR HS SHOK ADspan.
                { rewrite (ad_beq_sext _ 41%nat (ad4 bs (56 * 0 + 12)) 12%nat k ENCa (ad_4_rng bs (56 * 0 + 12)) E12b Hk) in Hc.
                  apply Z.eqb_eq in Hc. rewrite <- (ad_bx_nch bs 0 HLbs ltac:(lia)) in Hc.
                  paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
                            ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
                            ad_ag113 (adET regs bs M regsT) AGb.
                            assert (HspR : 0 <= spZ regs - 80 < 2 ^ 64) by lia.
                            lazymatch goal with
                            | HSx : st_ok _ ?Ex ?ss (restrict (w_H W) ?msx) |- _ =>
                              assert (HFRm : adfr regs W (ms_mem msx))
                                by (eapply ad_frame_of_st;
                                    [ exact HSx | reflexivity | rewrite ?(AGb 2%nat ltac:(lia)); exact Usp
                                    | intros nn x Hnn Hx; rewrite ?(AGb nn ltac:(lia));
                                      apply (ad_ewr regs bs M regsT nn x Hx Hnn) ]);
                              assert (HFOm : afobj SEGS B ly S W (ms_mem msx) p 6)
                                by (apply (ad_afobj_keep W ly S memT (ms_mem msx) p (spZ regs - 80) (spZ regs) HFO KEEP0);
                                    intros x Hx;
                                    apply (adb_shadow_out regs ly p C1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) x Hx));
                              assert (HMvm : forall o, 0 <= o < 6 ->
                                        aview SEGS (w_H W) (ms_mem msx) (p + o) = Some (adtb M o))
                                by (intros o Ho; rewrite KEEP0 by lia; exact (HMv o Ho));
                              assert (Hbsm : forall o, 0 <= o < 288 ->
                                        aview SEGS (w_H W) (ms_mem msx) (r + o) = Some (adtb bs o))
                                by (intros o Ho; rewrite KEEP0 by lia; apply Hbs; unfold REG_SIZE; lia)
                            end.
                            pmkst HS.
                            prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
                            prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp.
                            prreg HS (4%bv : bv 5) Rtp. prreg HS (20%bv : bv 5) Rs4.
                            prreg HS (25%bv : bv 5) Rs9. prreg HS (26%bv : bv 5) Rs10. prreg HS (27%bv : bv 5) Rs11.
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qa0 : getr rg2 (10%bv : bv 5) = w64 (r + 56 * 0)) end.
                            { rewrite Ra0. rewrite ?(AGb 10%nat ltac:(lia)).
                              rewrite (ad_ewr regs bs M regsT 10%nat 10%bv eq_refl ltac:(lia)), H10.
                              unfold w64. rewrite ?unsigned_lit_small by lia. f_equal; try lia. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qa1 : getr rg2 (11%bv : bv 5) = w64 p) end.
                            { rewrite Ra1. rewrite ?(AGb 11%nat ltac:(lia)).
                              rewrite (ad_ewr regs bs M regsT 11%nat 11%bv eq_refl ltac:(lia)), H11.
                              unfold w64. rewrite ?unsigned_lit_small by lia. f_equal; try lia. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qa2 : getr rg2 (12%bv : bv 5) = w64 6) end.
                            { rewrite Ra2. reflexivity. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qsp2 : getr rg2 (2%bv : bv 5) = w64 (spZ regs - 80)) end.
                            { rewrite Rsp. rewrite ?(AGb 2%nat ltac:(lia)).
                              rewrite (ad_ewr regs bs M regsT 2%nat 2%bv eq_refl ltac:(lia)).
                              unfold spZ, w64. f_equal; try lia. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qsp : spZ rg2 = spZ regs + -80) end.
                            { unfold spZ at 1. rewrite Qsp2. unfold w64.
                              rewrite unsigned_lit_small by lia. lia. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qgp : getr rg2 (3%bv : bv 5) = w64 (as_gp B)) end.
                            { rewrite Rgp. rewrite ?(AGb 3%nat ltac:(lia)).
                              rewrite (ad_ewr regs bs M regsT 3%nat 3%bv eq_refl ltac:(lia)). exact Hgp. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qtp : getr rg2 (4%bv : bv 5) = w64 (as_tp B)) end.
                            { rewrite Rtp. rewrite ?(AGb 4%nat ltac:(lia)).
                              rewrite (ad_ewr regs bs M regsT 4%nat 4%bv eq_refl ltac:(lia)). exact Htp. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qs4 : getr rg2 (20%bv : bv 5) = w64 0) end.
                            { rewrite Rs4. reflexivity. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qs9 : getr rg2 (25%bv : bv 5) = getr regs 25) end.
                            { rewrite Rs9. rewrite ?(AGb 25%nat ltac:(lia)).
                              apply (ad_ewr regs bs M regsT 25%nat 25%bv eq_refl ltac:(lia)). }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qs10 : getr rg2 (26%bv : bv 5) = getr regs 26) end.
                            { rewrite Rs10. rewrite ?(AGb 26%nat ltac:(lia)).
                              apply (ad_ewr regs bs M regsT 26%nat 26%bv eq_refl ltac:(lia)). }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qs11 : getr rg2 (27%bv : bv 5) = getr regs 27) end.
                            { rewrite Rs11. rewrite ?(AGb 27%nat ltac:(lia)).
                              apply (ad_ewr regs bs M regsT 27%nat 27%bv eq_refl ltac:(lia)). }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ ?mm _) _) _ =>
                              eapply SRr_bind;
                              [ eapply (aj_intrin_at SEGS B LAWS Hsegs OCpy (SIGMA BS___asan_memcpy) AMEMCPY W rg2 mm
                                  REAC_BOXREG_ADD_STK (spZ regs) [(r, r + REG_SIZE)] ly S W mem md (@nil (Z * Z)) ly S _ 0
                                  (r + 56 * 0) p 6 (-80) _ HJ) | ] end.
                            { exact Qa0. }
                            { exact Qa1. }
                            { exact Qa2. }
                            { lia. }
                            { lia. }
                            { lia. }
                            { exact Qsp. }
                            { reflexivity. }
                            { lia. }
                            { rewrite WS. unfold ESTACK. lia. }
                            { exact Qgp. }
                            { exact Qtp. }
                            { exact Rra. }
                            { apply ret_ok_codeptr_v; [lia | reflexivity]. }
                            { intros a Ha. split.
                              - right. left. split.
                                + exists (r, r + REG_SIZE). split; [left; reflexivity | cbn [fst snd]; unfold REG_SIZE; lia].
                                + exists r, REG_SIZE. split; [exact Hin | change (req_size REG_SIZE) with 288; lia].
                              - unfold ESTACK. lia. }
                            { eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hin);
                                change (req_size REG_SIZE) with 288; lia. }
                            { eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hin);
                                change (req_size REG_SIZE) with 288; lia. }
                            { intros _.
                              eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hin);
                                change (req_size REG_SIZE) with 288; lia. }
                            { split; [lia|]. split; [lia|]. split.
                              - intros a Ha. split.
                                + replace a with (p + (a - p)) by lia.
                                  rewrite (HMvm (a - p) ltac:(lia)). discriminate.
                                + rewrite Qsp. unfold ESTACK. lia.
                              - split; [destruct Hrf as [Hd1|Hd2]; [left; lia | right; lia]|].
                                split.
                                + apply (amem_range_sub_app (frame_addr ly cid pos) (fs_frame_bytes cid) p 6
                                           Hfapp Hfceil ltac:(lia) ltac:(lia) ltac:(lia)).
                                + split; [exact (proj2 (proj2 HFOm))|].
                                  intros _.
                                  lazymatch goal with |- shadow_hull_vis (aview _ _ ?mm) _ _ =>
                                    apply (BoxFrame.shadow_hull_vis_of_frame SEGS B LAWS ly S W mm _ cid pos p 6
                                             (proj1 HJ) Hfin ltac:(lia) ltac:(lia) ltac:(lia)) end. }
                            cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0 & Heff & Hfr2 & Hpres2).
                            lazymatch goal with
                            | HFRx : adfr regs W ?mm |- _ =>
                              apply (ad_tailret ly S W regs mem md ch r k 0 bs M
                                       (BoxregUpd.bind_bytes bs M 0) regs2 mem2 md2 HPRE HJ2 Hin);
                              [ apply (ad_fr_of_aview W regs mm mem2);
                                [ intros a Ha; apply Hfr2; [lia | lia | unfold ESTACK; lia] | exact HFRx ] | .. ]
                            end.
                            { rewrite (ad_pres_get _ regs2 (2%bv : bv 5) 2 HP2 eq_refl
                                 ltac:(unfold acallee_saved; lia)). exact Qsp2. }
                            { rewrite (ad_pres_get _ regs2 (20%bv : bv 5) 20 HP2 eq_refl
                                 ltac:(unfold acallee_saved; lia)). exact Qs4. }
                            { rewrite (ad_pres_get _ regs2 (3%bv : bv 5) 3 HP2 eq_refl
                                 ltac:(unfold acallee_saved; lia)). rewrite Qgp. symmetry. exact Hgp. }
                            { rewrite (ad_pres_get _ regs2 (4%bv : bv 5) 4 HP2 eq_refl
                                 ltac:(unfold acallee_saved; lia)). rewrite Qtp. symmetry. exact Htp. }
                            { rewrite (ad_pres_get _ regs2 (25%bv : bv 5) 25 HP2 eq_refl
                                 ltac:(unfold acallee_saved; lia)). exact Qs9. }
                            { rewrite (ad_pres_get _ regs2 (26%bv : bv 5) 26 HP2 eq_refl
                                 ltac:(unfold acallee_saved; lia)). exact Qs10. }
                            { rewrite (ad_pres_get _ regs2 (27%bv : bv 5) 27 HP2 eq_refl
                                 ltac:(unfold acallee_saved; lia)). exact Qs11. }
                            { lia. }
                            { right. right. left.
                              split; [exact HWO|]. split; [exact HMnz|]. split; [exact HNH|].
                              split.
                              - split; [lia|]. split; [exact HMZ|]. split; [exact Hc|].
                                intros j Hj. apply HINV. lia.
                              - reflexivity. }
                            { intros o Ho. change REG_SIZE with 288 in Ho.
                              rewrite (ad_bind_view bs M 0 o HLbs HML ltac:(lia) ltac:(lia)).
                              destruct (Z.leb_spec (56 * 0) o) as [HA|HA];
                              destruct (Z.ltb_spec o (56 * 0 + 6)) as [HBb|HBb]; cbn [andb];
                              first
                              [ replace (r + o) with ((r + 56 * 0) + (o - 56 * 0)) by lia;
                                rewrite (Heff (o - 56 * 0) ltac:(lia));
                                rewrite (HMvm (o - 56 * 0) ltac:(lia)); reflexivity
                              | rewrite (Hfr2 (r + o) ltac:(lia) ltac:(lia) ltac:(unfold ESTACK; lia));
                                exact (Hbsm o ltac:(lia)) ]. }
                }
                { rewrite (ad_beq_sext _ 41%nat (ad4 bs (56 * 0 + 12)) 12%nat k ENCa (ad_4_rng bs (56 * 0 + 12)) E12b Hk) in Hc.
                  apply Z.eqb_neq in Hc. rewrite <- (ad_bx_nch bs 0 HLbs ltac:(lia)) in Hc.
                  paj_run_to_tok RUNTO HS HJ SHOK ADspan 7632; [awr_ok_tac; exact Usp |].
                  ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
                  ad_ag113 (adET regs bs M regsT) AGx;
                            lazymatch goal with
                            | HSx : st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?Wx) ?msx) |- _ =>
                              pose proof (adbz_reabs 0 Ex (abs_ss VAL ss) (restrict (w_H Wx) msx)
                                (getr (ms_regs (restrict (w_H Wx) msx)) 11) (getr (ms_regs (restrict (w_H Wx) msx)) 14)
                                (getr (ms_regs (restrict (w_H Wx) msx)) 15) (getr (ms_regs (restrict (w_H Wx) msx)) 16)
                                (getr (ms_regs (restrict (w_H Wx) msx)) 17)
                                ltac:(lia) HSx ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                                eq_refl eq_refl eq_refl eq_refl eq_refl) as HSm
                            end;
                            apply (NEXT _ _ _ HSm
                              ltac:(apply adbz_shok; exact SHOK) ltac:(apply adbz_img; assumption)
                              HJ KEEP0
                              ltac:(split;
                                    [ intros nn Hnn; rewrite (adbz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn
                                    | reflexivity ])
                              ltac:(intros Hzz; exact (Hc (proj2 Hzz)))). }
}}}}}}
  + (* ---------------- row 1 ---------------- *)
    assert (EB0 : ew (adET regs bs M regsT) 42%nat = Z_to_bv 64 (adtb bs (56 * 1 + 0)))
      by (rewrite (ad_ewx regs bs M regsT 42%nat 10%nat eq_refl ltac:(lia));
          unfold adextra, adrowv; cbn [map app nth]; reflexivity).
    assert (EB1 : ew (adET regs bs M regsT) 43%nat = Z_to_bv 64 (adtb bs (56 * 1 + 1)))
      by (rewrite (ad_ewx regs bs M regsT 43%nat 11%nat eq_refl ltac:(lia));
          unfold adextra, adrowv; cbn [map app nth]; reflexivity).
    assert (EB2 : ew (adET regs bs M regsT) 44%nat = Z_to_bv 64 (adtb bs (56 * 1 + 2)))
      by (rewrite (ad_ewx regs bs M regsT 44%nat 12%nat eq_refl ltac:(lia));
          unfold adextra, adrowv; cbn [map app nth]; reflexivity).
    assert (EB3 : ew (adET regs bs M regsT) 45%nat = Z_to_bv 64 (adtb bs (56 * 1 + 3)))
      by (rewrite (ad_ewx regs bs M regsT 45%nat 13%nat eq_refl ltac:(lia));
          unfold adextra, adrowv; cbn [map app nth]; reflexivity).
    assert (EB4 : ew (adET regs bs M regsT) 46%nat = Z_to_bv 64 (adtb bs (56 * 1 + 4)))
      by (rewrite (ad_ewx regs bs M regsT 46%nat 14%nat eq_refl ltac:(lia));
          unfold adextra, adrowv; cbn [map app nth]; reflexivity).
    assert (EB5 : ew (adET regs bs M regsT) 47%nat = Z_to_bv 64 (adtb bs (56 * 1 + 5)))
      by (rewrite (ad_ewx regs bs M regsT 47%nat 15%nat eq_refl ltac:(lia));
          unfold adextra, adrowv; cbn [map app nth]; reflexivity).
    assert (ENC : ew (adET regs bs M regsT) 48%nat = Z_to_bv 64 (ad4 bs (56 * 1 + 12)))
      by (rewrite (ad_ewx regs bs M regsT 48%nat 16%nat eq_refl ltac:(lia));
          unfold adextra, adrowv; cbn [map app nth]; reflexivity).
    assert (NEXT : forall (E' : env) (ms' : machine_state) (md' : Model),
      st_ok_pi SEGS VAL E' (adbz 1) (restrict (w_H W) ms') ->
      sh_ok SEGS ADBx adSH E' (mrestrict (w_H W) (ms_mem ms')) ->
      img_env VAL A_LIM E' ->
      ajournal SEGS B REAC_BOXREG_ADD_STK (spZ regs) [(r, r + REG_SIZE)] ly S W mem md []
        ly S W (ms_mem ms') md' 0 ->
      (forall a : Z, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 80 <= a < spZ regs) ->
         aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) memT a) ->
      env_agree 113 (adET regs bs M regsT) E' ->
      ~ (Boxreg.bx_mac bs 1 = Boxreg.zero6 /\ Boxreg.bx_nch bs 1 = k) ->
      SRr SEGS W (mkCfg ms' md') (treac_boxreg_add_post regs ly S W mem md r k bs M)).
    { clear HS SHOK KEEP0.
      intros E' ms' md' HSn SHOKn HEIn HJn KEEPn AGe FACT.
      pose proof (proj1 AGe) as AG.
      assert (Usp' : bv_unsigned (ew E' 2) = spZ regs) by (rewrite (AG 2%nat ltac:(lia)); exact Usp).
      assert (E1' : ew E' 1 = getr regs 1) by (rewrite (AG 1%nat ltac:(lia)); exact E1).
      assert (HAE' : env_agree 32 (Ereg regs (adextra bs M)) E')
        by (eapply env_agree_trans;
            [exact HAE | split; [intros nn Hnn; apply AG; lia | exact (proj2 AGe)]]).
      paj_run_tok RUN HSn HJn SHOKn ADspan; [awr_ok_tac; exact Usp' |].
      ad_upd KEEPn Usp' W (spZ regs - 80) (spZ regs).
      psrr_branch_tok RUN BR HSn SHOKn ADspan.
      { (* i + 1 <> n: the next row *)
        ad_atg AG E105 105%nat E105a.
        rewrite (ad_bne_lit _ 2 105%nat (Boxreg.bx_n bs) E105a ltac:(lia) ltac:(lia)) in Hc.
        apply negb_true_iff, Z.eqb_neq in Hc.
        paj_run_to_tok RUNTO HSn HJn SHOKn ADspan 7512; [awr_ok_tac; exact Usp' |].
        ad_upd KEEPn Usp' W (spZ regs - 80) (spZ regs).
        ad_ag113x (adET regs bs M regsT) AGe AGn.
        pmkst HSn.
        refine (IH ly S W regs mem md ch r p k bs M _ _ _ 2
          HPRE H10 H11 H12 Hk Hin Hinv HML HMnz HWO HNH _ _ _
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CONT).
        - lia.
        - lia.
        - intros j Hj. destruct (Z.eq_dec j 1) as [->|Hne]; [exact FACT | apply HINV; lia].
        - ad_qreg (adET regs bs M regsT) AGn (2%bv : bv 5). exact Dsp.
        - ad_qreg (adET regs bs M regsT) AGn (3%bv : bv 5). exact D3.
        - ad_qreg (adET regs bs M regsT) AGn (4%bv : bv 5). exact D4.
        - ad_qreg (adET regs bs M regsT) AGn (8%bv : bv 5). exact Dk.
        - ad_qreg (adET regs bs M regsT) AGn (9%bv : bv 5). exact Dp.
        - ad_qreg (adET regs bs M regsT) AGn (12%bv : bv 5). rewrite Dr. unfold w64. f_equal; try lia.
        - ad_qreg (adET regs bs M regsT) AGn (13%bv : bv 5). rewrite Dr. unfold w64. f_equal; try lia.
        - ad_qreg (adET regs bs M regsT) AGn (18%bv : bv 5). rewrite Dr. unfold w64. f_equal; try lia.
        - ad_qreg (adET regs bs M regsT) AGn (19%bv : bv 5). rewrite Dr. unfold w64. f_equal; try lia.
        - ad_qreg (adET regs bs M regsT) AGn (20%bv : bv 5). cbn [sv_denot]. unfold w64. f_equal; try lia.
        - ad_qreg (adET regs bs M regsT) AGn (22%bv : bv 5). exact D32.
        - ad_qreg (adET regs bs M regsT) AGn (23%bv : bv 5). exact D7.
        - ad_qreg (adET regs bs M regsT) AGn (24%bv : bv 5).
          rewrite (ad_ewj_den regs bs M regsT 105%nat 24%nat eq_refl ltac:(lia)).
          cbn [adrl nth]. exact R24.
        - ad_qreg (adET regs bs M regsT) AGn (25%bv : bv 5). exact D25.
        - ad_qreg (adET regs bs M regsT) AGn (26%bv : bv 5). exact D26.
        - ad_qreg (adET regs bs M regsT) AGn (27%bv : bv 5). exact D27.
        - eapply ad_frame_of_st;
            [ exact HSn | reflexivity | rewrite ((proj1 AGn) 2%nat ltac:(lia)); exact Usp
            | intros nn x Hnn Hx; rewrite ((proj1 AGn) nn ltac:(lia));
              apply (ad_ewr regs bs M regsT nn x Hx Hnn) ].
        - intros o Ho. change REG_SIZE with 288 in Ho. rewrite KEEPn by lia. exact (Hbs o Ho).
        - lazymatch goal with |- afobj _ _ _ _ _ ?mx _ _ =>
            apply (ad_afobj_keep W ly S memT mx p (spZ regs - 80) (spZ regs) HFO KEEPn) end.
          intros x Hx. apply (adb_shadow_out regs ly p C1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) x Hx).
        - intros o Ho. rewrite KEEPn by lia. exact (HMv o Ho).
        - exact HJn. }
      { (* i + 1 = n: the loop is over *)
        ad_atg AG E105 105%nat E105a.
        rewrite (ad_bne_lit _ 2 105%nat (Boxreg.bx_n bs) E105a ltac:(lia) ltac:(lia)) in Hc.
        apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HEQn.
        paj_run_tok RUN HSn HJn SHOKn ADspan; [awr_ok_tac; exact Usp' |].
        ad_upd KEEPn Usp' W (spZ regs - 80) (spZ regs).
        psrr_branch_tok RUN BR HSn SHOKn ADspan.
        { (* n <= 4: the new-row tail at 0x81d90 *)
          ad_atg AG E33 33%nat E33a.
          rewrite (ad_bge4 _ 33%nat (ad4 bs 280) E33a (ad_4_rng bs 280)) in Hc.
          apply negb_true_iff, Z.ltb_ge in Hc. rewrite <- (ad_bx_n bs HLbs) in Hc.
          paj_run_to_tok RUNTO HSn HJn SHOKn ADspan 7748; [awr_ok_tac; exact Usp' |].
          ad_upd KEEPn Usp' W (spZ regs - 80) (spZ regs).
          ad_ag113x (adET regs bs M regsT) AGe AGn.
          pmkst HSn.
          refine (CONT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
          - ad_qreg (adET regs bs M regsT) AGn (2%bv : bv 5). exact Dsp.
          - ad_qreg (adET regs bs M regsT) AGn (3%bv : bv 5). exact D3.
          - ad_qreg (adET regs bs M regsT) AGn (4%bv : bv 5). exact D4.
          - ad_qreg (adET regs bs M regsT) AGn (8%bv : bv 5). exact Dk.
          - ad_qreg (adET regs bs M regsT) AGn (9%bv : bv 5). exact Dp.
          - ad_qreg (adET regs bs M regsT) AGn (18%bv : bv 5). rewrite Dr. unfold w64. f_equal; try lia.
          - ad_qreg (adET regs bs M regsT) AGn (19%bv : bv 5). rewrite Dr. unfold w64. f_equal; try lia.
          - ad_qreg (adET regs bs M regsT) AGn (22%bv : bv 5). exact D32.
          - ad_qreg (adET regs bs M regsT) AGn (23%bv : bv 5). exact D7.
          - ad_qreg (adET regs bs M regsT) AGn (24%bv : bv 5).
            rewrite (ad_sext_den (adET regs bs M regsT) 33%nat (ad4 bs 280) E33 (ad_4_rng bs 280)).
            rewrite <- (ad_bx_n bs HLbs). reflexivity.
          - ad_qreg (adET regs bs M regsT) AGn (25%bv : bv 5). exact D25.
          - ad_qreg (adET regs bs M regsT) AGn (26%bv : bv 5). exact D26.
          - ad_qreg (adET regs bs M regsT) AGn (27%bv : bv 5). exact D27.
          - eapply ad_frame_of_st;
              [ exact HSn | reflexivity | rewrite ((proj1 AGn) 2%nat ltac:(lia)); exact Usp
              | intros nn x Hnn Hx; rewrite ((proj1 AGn) nn ltac:(lia));
                apply (ad_ewr regs bs M regsT nn x Hx Hnn) ].
          - intros o Ho. change REG_SIZE with 288 in Ho. rewrite KEEPn by lia. exact (Hbs o Ho).
          - lazymatch goal with |- afobj _ _ _ _ _ ?mx _ _ =>
              apply (ad_afobj_keep W ly S memT mx p (spZ regs - 80) (spZ regs) HFO KEEPn) end.
            intros x Hx. apply (adb_shadow_out regs ly p C1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) x Hx).
          - intros o Ho. rewrite KEEPn by lia. exact (HMv o Ho).
          - exact HJn.
          - intros j Hj. destruct (Z.eq_dec j 1) as [->|Hne]; [exact FACT | apply HINV; lia].
          - lia. }
        { (* 5 <= n: the function returns -1 *)
          ad_atg AG E33 33%nat E33a.
          rewrite (ad_bge4 _ 33%nat (ad4 bs 280) E33a (ad_4_rng bs 280)) in Hc.
          apply negb_false_iff, Z.ltb_lt in Hc. rewrite <- (ad_bx_n bs HLbs) in Hc.
          paj_run_tok RUN HSn HJn SHOKn ADspan; [awr_ok_tac; exact Usp' |].
          ad_upd KEEPn Usp' W (spZ regs - 80) (spZ regs).
          ad_ret HSn HJn E1' Hra HAE' (-1) bs.
          split.
          - right. right. right. left.
            split; [exact HWO|]. split; [exact HMnz|]. split; [exact HNH|].
            split; [intros j Hj; destruct (Z.eq_dec j 1) as [->|Hne];
                    [exact FACT | apply HINV; lia]|].
            split; [left; lia|]. split; reflexivity.
          - intros o Ho. change REG_SIZE with 288 in Ho. rewrite KEEPn by lia. exact (Hbs o Ho). } } }
    paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
    ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
    psrr_branch_tok RUN BR HS SHOK ADspan.
    { (* the MAC byte 0 of the row is not zero *)
      ad_at EB0 42%nat EBa0.
      rewrite (ad_bnz_b _ 42%nat bs (56 * 1 + 0) EBa0) in Hc.
      apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into HNZ.
      paj_run_to_tok RUNTO HS HJ SHOK ADspan 7632; [awr_ok_tac; exact Usp |].
      ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
      ad_ag113 (adET regs bs M regsT) AGx;
                lazymatch goal with
                | HSx : st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?Wx) ?msx) |- _ =>
                  pose proof (adbz_reabs 1 Ex (abs_ss VAL ss) (restrict (w_H Wx) msx)
                    (getr (ms_regs (restrict (w_H Wx) msx)) 11) (getr (ms_regs (restrict (w_H Wx) msx)) 14)
                    (getr (ms_regs (restrict (w_H Wx) msx)) 15) (getr (ms_regs (restrict (w_H Wx) msx)) 16)
                    (getr (ms_regs (restrict (w_H Wx) msx)) 17)
                    ltac:(lia) HSx ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                    eq_refl eq_refl eq_refl eq_refl eq_refl) as HSm
                end;
                apply (NEXT _ _ _ HSm
                  ltac:(apply adbz_shok; exact SHOK) ltac:(apply adbz_img; assumption)
                  HJ KEEP0
                  ltac:(split;
                        [ intros nn Hnn; rewrite (adbz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn
                        | reflexivity ])
                  ltac:(intros Hzz; apply HNZ;
                  exact (proj1 (ad_mac_zero bs 1 HLbs ltac:(lia)) (proj1 Hzz) 0 ltac:(lia)))). }
    { (* the MAC byte 0 of the row is zero *)
      ad_at EB0 42%nat EBz0.
      rewrite (ad_bnz_b _ 42%nat bs (56 * 1 + 0) EBz0) in Hc.
      apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HZ0.
      paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
      ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
      psrr_branch_tok RUN BR HS SHOK ADspan.
      { (* the MAC byte 1 of the row is not zero *)
        ad_at EB1 43%nat EBa1.
        rewrite (ad_bnz_b _ 43%nat bs (56 * 1 + 1) EBa1) in Hc.
        apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into HNZ.
        paj_run_to_tok RUNTO HS HJ SHOK ADspan 7632; [awr_ok_tac; exact Usp |].
        ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
        ad_ag113 (adET regs bs M regsT) AGx;
                  lazymatch goal with
                  | HSx : st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?Wx) ?msx) |- _ =>
                    pose proof (adbz_reabs 1 Ex (abs_ss VAL ss) (restrict (w_H Wx) msx)
                      (getr (ms_regs (restrict (w_H Wx) msx)) 11) (getr (ms_regs (restrict (w_H Wx) msx)) 14)
                      (getr (ms_regs (restrict (w_H Wx) msx)) 15) (getr (ms_regs (restrict (w_H Wx) msx)) 16)
                      (getr (ms_regs (restrict (w_H Wx) msx)) 17)
                      ltac:(lia) HSx ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                      eq_refl eq_refl eq_refl eq_refl eq_refl) as HSm
                  end;
                  apply (NEXT _ _ _ HSm
                    ltac:(apply adbz_shok; exact SHOK) ltac:(apply adbz_img; assumption)
                    HJ KEEP0
                    ltac:(split;
                          [ intros nn Hnn; rewrite (adbz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn
                          | reflexivity ])
                    ltac:(intros Hzz; apply HNZ;
                    exact (proj1 (ad_mac_zero bs 1 HLbs ltac:(lia)) (proj1 Hzz) 1 ltac:(lia)))). }
      { (* the MAC byte 1 of the row is zero *)
        ad_at EB1 43%nat EBz1.
        rewrite (ad_bnz_b _ 43%nat bs (56 * 1 + 1) EBz1) in Hc.
        apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HZ1.
        paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
        ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
        psrr_branch_tok RUN BR HS SHOK ADspan.
        { (* the MAC byte 2 of the row is not zero *)
          ad_at EB2 44%nat EBa2.
          rewrite (ad_bnz_b _ 44%nat bs (56 * 1 + 2) EBa2) in Hc.
          apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into HNZ.
          paj_run_to_tok RUNTO HS HJ SHOK ADspan 7632; [awr_ok_tac; exact Usp |].
          ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
          ad_ag113 (adET regs bs M regsT) AGx;
                    lazymatch goal with
                    | HSx : st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?Wx) ?msx) |- _ =>
                      pose proof (adbz_reabs 1 Ex (abs_ss VAL ss) (restrict (w_H Wx) msx)
                        (getr (ms_regs (restrict (w_H Wx) msx)) 11) (getr (ms_regs (restrict (w_H Wx) msx)) 14)
                        (getr (ms_regs (restrict (w_H Wx) msx)) 15) (getr (ms_regs (restrict (w_H Wx) msx)) 16)
                        (getr (ms_regs (restrict (w_H Wx) msx)) 17)
                        ltac:(lia) HSx ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                        eq_refl eq_refl eq_refl eq_refl eq_refl) as HSm
                    end;
                    apply (NEXT _ _ _ HSm
                      ltac:(apply adbz_shok; exact SHOK) ltac:(apply adbz_img; assumption)
                      HJ KEEP0
                      ltac:(split;
                            [ intros nn Hnn; rewrite (adbz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn
                            | reflexivity ])
                      ltac:(intros Hzz; apply HNZ;
                      exact (proj1 (ad_mac_zero bs 1 HLbs ltac:(lia)) (proj1 Hzz) 2 ltac:(lia)))). }
        { (* the MAC byte 2 of the row is zero *)
          ad_at EB2 44%nat EBz2.
          rewrite (ad_bnz_b _ 44%nat bs (56 * 1 + 2) EBz2) in Hc.
          apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HZ2.
          paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
          ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
          psrr_branch_tok RUN BR HS SHOK ADspan.
          { (* the MAC byte 3 of the row is not zero *)
            ad_at EB3 45%nat EBa3.
            rewrite (ad_bnz_b _ 45%nat bs (56 * 1 + 3) EBa3) in Hc.
            apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into HNZ.
            paj_run_to_tok RUNTO HS HJ SHOK ADspan 7632; [awr_ok_tac; exact Usp |].
            ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
            ad_ag113 (adET regs bs M regsT) AGx;
                      lazymatch goal with
                      | HSx : st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?Wx) ?msx) |- _ =>
                        pose proof (adbz_reabs 1 Ex (abs_ss VAL ss) (restrict (w_H Wx) msx)
                          (getr (ms_regs (restrict (w_H Wx) msx)) 11) (getr (ms_regs (restrict (w_H Wx) msx)) 14)
                          (getr (ms_regs (restrict (w_H Wx) msx)) 15) (getr (ms_regs (restrict (w_H Wx) msx)) 16)
                          (getr (ms_regs (restrict (w_H Wx) msx)) 17)
                          ltac:(lia) HSx ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                          eq_refl eq_refl eq_refl eq_refl eq_refl) as HSm
                      end;
                      apply (NEXT _ _ _ HSm
                        ltac:(apply adbz_shok; exact SHOK) ltac:(apply adbz_img; assumption)
                        HJ KEEP0
                        ltac:(split;
                              [ intros nn Hnn; rewrite (adbz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn
                              | reflexivity ])
                        ltac:(intros Hzz; apply HNZ;
                        exact (proj1 (ad_mac_zero bs 1 HLbs ltac:(lia)) (proj1 Hzz) 3 ltac:(lia)))). }
          { (* the MAC byte 3 of the row is zero *)
            ad_at EB3 45%nat EBz3.
            rewrite (ad_bnz_b _ 45%nat bs (56 * 1 + 3) EBz3) in Hc.
            apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HZ3.
            paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
            ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
            psrr_branch_tok RUN BR HS SHOK ADspan.
            { (* the MAC byte 4 of the row is not zero *)
              ad_at EB4 46%nat EBa4.
              rewrite (ad_bnz_b _ 46%nat bs (56 * 1 + 4) EBa4) in Hc.
              apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into HNZ.
              paj_run_to_tok RUNTO HS HJ SHOK ADspan 7632; [awr_ok_tac; exact Usp |].
              ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
              ad_ag113 (adET regs bs M regsT) AGx;
                        lazymatch goal with
                        | HSx : st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?Wx) ?msx) |- _ =>
                          pose proof (adbz_reabs 1 Ex (abs_ss VAL ss) (restrict (w_H Wx) msx)
                            (getr (ms_regs (restrict (w_H Wx) msx)) 11) (getr (ms_regs (restrict (w_H Wx) msx)) 14)
                            (getr (ms_regs (restrict (w_H Wx) msx)) 15) (getr (ms_regs (restrict (w_H Wx) msx)) 16)
                            (getr (ms_regs (restrict (w_H Wx) msx)) 17)
                            ltac:(lia) HSx ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                            eq_refl eq_refl eq_refl eq_refl eq_refl) as HSm
                        end;
                        apply (NEXT _ _ _ HSm
                          ltac:(apply adbz_shok; exact SHOK) ltac:(apply adbz_img; assumption)
                          HJ KEEP0
                          ltac:(split;
                                [ intros nn Hnn; rewrite (adbz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn
                                | reflexivity ])
                          ltac:(intros Hzz; apply HNZ;
                          exact (proj1 (ad_mac_zero bs 1 HLbs ltac:(lia)) (proj1 Hzz) 4 ltac:(lia)))). }
            { (* the MAC byte 4 of the row is zero *)
              ad_at EB4 46%nat EBz4.
              rewrite (ad_bnz_b _ 46%nat bs (56 * 1 + 4) EBz4) in Hc.
              apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HZ4.
              paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
              ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
              psrr_branch_tok RUN BR HS SHOK ADspan.
              { (* the MAC byte 5 of the row is not zero *)
                ad_at EB5 47%nat EBa5.
                rewrite (ad_bnz_b _ 47%nat bs (56 * 1 + 5) EBa5) in Hc.
                apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into HNZ.
                paj_run_to_tok RUNTO HS HJ SHOK ADspan 7632; [awr_ok_tac; exact Usp |].
                ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
                ad_ag113 (adET regs bs M regsT) AGx;
                          lazymatch goal with
                          | HSx : st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?Wx) ?msx) |- _ =>
                            pose proof (adbz_reabs 1 Ex (abs_ss VAL ss) (restrict (w_H Wx) msx)
                              (getr (ms_regs (restrict (w_H Wx) msx)) 11) (getr (ms_regs (restrict (w_H Wx) msx)) 14)
                              (getr (ms_regs (restrict (w_H Wx) msx)) 15) (getr (ms_regs (restrict (w_H Wx) msx)) 16)
                              (getr (ms_regs (restrict (w_H Wx) msx)) 17)
                              ltac:(lia) HSx ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                              eq_refl eq_refl eq_refl eq_refl eq_refl) as HSm
                          end;
                          apply (NEXT _ _ _ HSm
                            ltac:(apply adbz_shok; exact SHOK) ltac:(apply adbz_img; assumption)
                            HJ KEEP0
                            ltac:(split;
                                  [ intros nn Hnn; rewrite (adbz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn
                                  | reflexivity ])
                            ltac:(intros Hzz; apply HNZ;
                            exact (proj1 (ad_mac_zero bs 1 HLbs ltac:(lia)) (proj1 Hzz) 5 ltac:(lia)))). }
              { (* the MAC byte 5 of the row is zero *)
                ad_at EB5 47%nat EBz5.
                rewrite (ad_bnz_b _ 47%nat bs (56 * 1 + 5) EBz5) in Hc.
                apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HZ5.
                paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
                ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
                assert (HMZ : Boxreg.bx_mac bs 1 = Boxreg.zero6).
                { apply (proj2 (ad_mac_zero bs 1 HLbs ltac:(lia))). intros jj Hjj.
                  assert (Hj6 : jj = 0 \/ jj = 1 \/ jj = 2 \/ jj = 3 \/ jj = 4 \/ jj = 5) by lia.
                  destruct Hj6 as [-> | [-> | [-> | [-> | [-> | ->]]]]];
                    [exact HZ0 | exact HZ1 | exact HZ2 | exact HZ3 | exact HZ4 | exact HZ5]. }
                ad_at ENC 48%nat ENCa. ad_at E12a 12%nat E12b.
                psrr_branch_tok RUN BR HS SHOK ADspan.
                { rewrite (ad_beq_sext _ 48%nat (ad4 bs (56 * 1 + 12)) 12%nat k ENCa (ad_4_rng bs (56 * 1 + 12)) E12b Hk) in Hc.
                  apply Z.eqb_eq in Hc. rewrite <- (ad_bx_nch bs 1 HLbs ltac:(lia)) in Hc.
                  paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
                            ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
                            ad_ag113 (adET regs bs M regsT) AGb.
                            assert (HspR : 0 <= spZ regs - 80 < 2 ^ 64) by lia.
                            lazymatch goal with
                            | HSx : st_ok _ ?Ex ?ss (restrict (w_H W) ?msx) |- _ =>
                              assert (HFRm : adfr regs W (ms_mem msx))
                                by (eapply ad_frame_of_st;
                                    [ exact HSx | reflexivity | rewrite ?(AGb 2%nat ltac:(lia)); exact Usp
                                    | intros nn x Hnn Hx; rewrite ?(AGb nn ltac:(lia));
                                      apply (ad_ewr regs bs M regsT nn x Hx Hnn) ]);
                              assert (HFOm : afobj SEGS B ly S W (ms_mem msx) p 6)
                                by (apply (ad_afobj_keep W ly S memT (ms_mem msx) p (spZ regs - 80) (spZ regs) HFO KEEP0);
                                    intros x Hx;
                                    apply (adb_shadow_out regs ly p C1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) x Hx));
                              assert (HMvm : forall o, 0 <= o < 6 ->
                                        aview SEGS (w_H W) (ms_mem msx) (p + o) = Some (adtb M o))
                                by (intros o Ho; rewrite KEEP0 by lia; exact (HMv o Ho));
                              assert (Hbsm : forall o, 0 <= o < 288 ->
                                        aview SEGS (w_H W) (ms_mem msx) (r + o) = Some (adtb bs o))
                                by (intros o Ho; rewrite KEEP0 by lia; apply Hbs; unfold REG_SIZE; lia)
                            end.
                            pmkst HS.
                            prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
                            prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp.
                            prreg HS (4%bv : bv 5) Rtp. prreg HS (20%bv : bv 5) Rs4.
                            prreg HS (25%bv : bv 5) Rs9. prreg HS (26%bv : bv 5) Rs10. prreg HS (27%bv : bv 5) Rs11.
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qa0 : getr rg2 (10%bv : bv 5) = w64 (r + 56 * 1)) end.
                            { rewrite Ra0. rewrite ?(AGb 10%nat ltac:(lia)).
                              rewrite (ad_ewr regs bs M regsT 10%nat 10%bv eq_refl ltac:(lia)), H10.
                              unfold w64. rewrite ?unsigned_lit_small by lia. f_equal; try lia. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qa1 : getr rg2 (11%bv : bv 5) = w64 p) end.
                            { rewrite Ra1. rewrite ?(AGb 11%nat ltac:(lia)).
                              rewrite (ad_ewr regs bs M regsT 11%nat 11%bv eq_refl ltac:(lia)), H11.
                              unfold w64. rewrite ?unsigned_lit_small by lia. f_equal; try lia. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qa2 : getr rg2 (12%bv : bv 5) = w64 6) end.
                            { rewrite Ra2. reflexivity. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qsp2 : getr rg2 (2%bv : bv 5) = w64 (spZ regs - 80)) end.
                            { rewrite Rsp. rewrite ?(AGb 2%nat ltac:(lia)).
                              rewrite (ad_ewr regs bs M regsT 2%nat 2%bv eq_refl ltac:(lia)).
                              unfold spZ, w64. f_equal; try lia. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qsp : spZ rg2 = spZ regs + -80) end.
                            { unfold spZ at 1. rewrite Qsp2. unfold w64.
                              rewrite unsigned_lit_small by lia. lia. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qgp : getr rg2 (3%bv : bv 5) = w64 (as_gp B)) end.
                            { rewrite Rgp. rewrite ?(AGb 3%nat ltac:(lia)).
                              rewrite (ad_ewr regs bs M regsT 3%nat 3%bv eq_refl ltac:(lia)). exact Hgp. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qtp : getr rg2 (4%bv : bv 5) = w64 (as_tp B)) end.
                            { rewrite Rtp. rewrite ?(AGb 4%nat ltac:(lia)).
                              rewrite (ad_ewr regs bs M regsT 4%nat 4%bv eq_refl ltac:(lia)). exact Htp. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qs4 : getr rg2 (20%bv : bv 5) = w64 1) end.
                            { rewrite Rs4. reflexivity. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qs9 : getr rg2 (25%bv : bv 5) = getr regs 25) end.
                            { rewrite Rs9. rewrite ?(AGb 25%nat ltac:(lia)).
                              apply (ad_ewr regs bs M regsT 25%nat 25%bv eq_refl ltac:(lia)). }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qs10 : getr rg2 (26%bv : bv 5) = getr regs 26) end.
                            { rewrite Rs10. rewrite ?(AGb 26%nat ltac:(lia)).
                              apply (ad_ewr regs bs M regsT 26%nat 26%bv eq_refl ltac:(lia)). }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qs11 : getr rg2 (27%bv : bv 5) = getr regs 27) end.
                            { rewrite Rs11. rewrite ?(AGb 27%nat ltac:(lia)).
                              apply (ad_ewr regs bs M regsT 27%nat 27%bv eq_refl ltac:(lia)). }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ ?mm _) _) _ =>
                              eapply SRr_bind;
                              [ eapply (aj_intrin_at SEGS B LAWS Hsegs OCpy (SIGMA BS___asan_memcpy) AMEMCPY W rg2 mm
                                  REAC_BOXREG_ADD_STK (spZ regs) [(r, r + REG_SIZE)] ly S W mem md (@nil (Z * Z)) ly S _ 0
                                  (r + 56 * 1) p 6 (-80) _ HJ) | ] end.
                            { exact Qa0. }
                            { exact Qa1. }
                            { exact Qa2. }
                            { lia. }
                            { lia. }
                            { lia. }
                            { exact Qsp. }
                            { reflexivity. }
                            { lia. }
                            { rewrite WS. unfold ESTACK. lia. }
                            { exact Qgp. }
                            { exact Qtp. }
                            { exact Rra. }
                            { apply ret_ok_codeptr_v; [lia | reflexivity]. }
                            { intros a Ha. split.
                              - right. left. split.
                                + exists (r, r + REG_SIZE). split; [left; reflexivity | cbn [fst snd]; unfold REG_SIZE; lia].
                                + exists r, REG_SIZE. split; [exact Hin | change (req_size REG_SIZE) with 288; lia].
                              - unfold ESTACK. lia. }
                            { eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hin);
                                change (req_size REG_SIZE) with 288; lia. }
                            { eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hin);
                                change (req_size REG_SIZE) with 288; lia. }
                            { intros _.
                              eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hin);
                                change (req_size REG_SIZE) with 288; lia. }
                            { split; [lia|]. split; [lia|]. split.
                              - intros a Ha. split.
                                + replace a with (p + (a - p)) by lia.
                                  rewrite (HMvm (a - p) ltac:(lia)). discriminate.
                                + rewrite Qsp. unfold ESTACK. lia.
                              - split; [destruct Hrf as [Hd1|Hd2]; [left; lia | right; lia]|].
                                split.
                                + apply (amem_range_sub_app (frame_addr ly cid pos) (fs_frame_bytes cid) p 6
                                           Hfapp Hfceil ltac:(lia) ltac:(lia) ltac:(lia)).
                                + split; [exact (proj2 (proj2 HFOm))|].
                                  intros _.
                                  lazymatch goal with |- shadow_hull_vis (aview _ _ ?mm) _ _ =>
                                    apply (BoxFrame.shadow_hull_vis_of_frame SEGS B LAWS ly S W mm _ cid pos p 6
                                             (proj1 HJ) Hfin ltac:(lia) ltac:(lia) ltac:(lia)) end. }
                            cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0 & Heff & Hfr2 & Hpres2).
                            lazymatch goal with
                            | HFRx : adfr regs W ?mm |- _ =>
                              apply (ad_tailret ly S W regs mem md ch r k 1 bs M
                                       (BoxregUpd.bind_bytes bs M 1) regs2 mem2 md2 HPRE HJ2 Hin);
                              [ apply (ad_fr_of_aview W regs mm mem2);
                                [ intros a Ha; apply Hfr2; [lia | lia | unfold ESTACK; lia] | exact HFRx ] | .. ]
                            end.
                            { rewrite (ad_pres_get _ regs2 (2%bv : bv 5) 2 HP2 eq_refl
                                 ltac:(unfold acallee_saved; lia)). exact Qsp2. }
                            { rewrite (ad_pres_get _ regs2 (20%bv : bv 5) 20 HP2 eq_refl
                                 ltac:(unfold acallee_saved; lia)). exact Qs4. }
                            { rewrite (ad_pres_get _ regs2 (3%bv : bv 5) 3 HP2 eq_refl
                                 ltac:(unfold acallee_saved; lia)). rewrite Qgp. symmetry. exact Hgp. }
                            { rewrite (ad_pres_get _ regs2 (4%bv : bv 5) 4 HP2 eq_refl
                                 ltac:(unfold acallee_saved; lia)). rewrite Qtp. symmetry. exact Htp. }
                            { rewrite (ad_pres_get _ regs2 (25%bv : bv 5) 25 HP2 eq_refl
                                 ltac:(unfold acallee_saved; lia)). exact Qs9. }
                            { rewrite (ad_pres_get _ regs2 (26%bv : bv 5) 26 HP2 eq_refl
                                 ltac:(unfold acallee_saved; lia)). exact Qs10. }
                            { rewrite (ad_pres_get _ regs2 (27%bv : bv 5) 27 HP2 eq_refl
                                 ltac:(unfold acallee_saved; lia)). exact Qs11. }
                            { lia. }
                            { right. right. left.
                              split; [exact HWO|]. split; [exact HMnz|]. split; [exact HNH|].
                              split.
                              - split; [lia|]. split; [exact HMZ|]. split; [exact Hc|].
                                intros j Hj. apply HINV. lia.
                              - reflexivity. }
                            { intros o Ho. change REG_SIZE with 288 in Ho.
                              rewrite (ad_bind_view bs M 1 o HLbs HML ltac:(lia) ltac:(lia)).
                              destruct (Z.leb_spec (56 * 1) o) as [HA|HA];
                              destruct (Z.ltb_spec o (56 * 1 + 6)) as [HBb|HBb]; cbn [andb];
                              first
                              [ replace (r + o) with ((r + 56 * 1) + (o - 56 * 1)) by lia;
                                rewrite (Heff (o - 56 * 1) ltac:(lia));
                                rewrite (HMvm (o - 56 * 1) ltac:(lia)); reflexivity
                              | rewrite (Hfr2 (r + o) ltac:(lia) ltac:(lia) ltac:(unfold ESTACK; lia));
                                exact (Hbsm o ltac:(lia)) ]. }
                }
                { rewrite (ad_beq_sext _ 48%nat (ad4 bs (56 * 1 + 12)) 12%nat k ENCa (ad_4_rng bs (56 * 1 + 12)) E12b Hk) in Hc.
                  apply Z.eqb_neq in Hc. rewrite <- (ad_bx_nch bs 1 HLbs ltac:(lia)) in Hc.
                  paj_run_to_tok RUNTO HS HJ SHOK ADspan 7632; [awr_ok_tac; exact Usp |].
                  ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
                  ad_ag113 (adET regs bs M regsT) AGx;
                            lazymatch goal with
                            | HSx : st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?Wx) ?msx) |- _ =>
                              pose proof (adbz_reabs 1 Ex (abs_ss VAL ss) (restrict (w_H Wx) msx)
                                (getr (ms_regs (restrict (w_H Wx) msx)) 11) (getr (ms_regs (restrict (w_H Wx) msx)) 14)
                                (getr (ms_regs (restrict (w_H Wx) msx)) 15) (getr (ms_regs (restrict (w_H Wx) msx)) 16)
                                (getr (ms_regs (restrict (w_H Wx) msx)) 17)
                                ltac:(lia) HSx ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                                eq_refl eq_refl eq_refl eq_refl eq_refl) as HSm
                            end;
                            apply (NEXT _ _ _ HSm
                              ltac:(apply adbz_shok; exact SHOK) ltac:(apply adbz_img; assumption)
                              HJ KEEP0
                              ltac:(split;
                                    [ intros nn Hnn; rewrite (adbz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn
                                    | reflexivity ])
                              ltac:(intros Hzz; exact (Hc (proj2 Hzz)))). }
}}}}}}
  + (* ---------------- row 2 ---------------- *)
    assert (EB0 : ew (adET regs bs M regsT) 49%nat = Z_to_bv 64 (adtb bs (56 * 2 + 0)))
      by (rewrite (ad_ewx regs bs M regsT 49%nat 17%nat eq_refl ltac:(lia));
          unfold adextra, adrowv; cbn [map app nth]; reflexivity).
    assert (EB1 : ew (adET regs bs M regsT) 50%nat = Z_to_bv 64 (adtb bs (56 * 2 + 1)))
      by (rewrite (ad_ewx regs bs M regsT 50%nat 18%nat eq_refl ltac:(lia));
          unfold adextra, adrowv; cbn [map app nth]; reflexivity).
    assert (EB2 : ew (adET regs bs M regsT) 51%nat = Z_to_bv 64 (adtb bs (56 * 2 + 2)))
      by (rewrite (ad_ewx regs bs M regsT 51%nat 19%nat eq_refl ltac:(lia));
          unfold adextra, adrowv; cbn [map app nth]; reflexivity).
    assert (EB3 : ew (adET regs bs M regsT) 52%nat = Z_to_bv 64 (adtb bs (56 * 2 + 3)))
      by (rewrite (ad_ewx regs bs M regsT 52%nat 20%nat eq_refl ltac:(lia));
          unfold adextra, adrowv; cbn [map app nth]; reflexivity).
    assert (EB4 : ew (adET regs bs M regsT) 53%nat = Z_to_bv 64 (adtb bs (56 * 2 + 4)))
      by (rewrite (ad_ewx regs bs M regsT 53%nat 21%nat eq_refl ltac:(lia));
          unfold adextra, adrowv; cbn [map app nth]; reflexivity).
    assert (EB5 : ew (adET regs bs M regsT) 54%nat = Z_to_bv 64 (adtb bs (56 * 2 + 5)))
      by (rewrite (ad_ewx regs bs M regsT 54%nat 22%nat eq_refl ltac:(lia));
          unfold adextra, adrowv; cbn [map app nth]; reflexivity).
    assert (ENC : ew (adET regs bs M regsT) 55%nat = Z_to_bv 64 (ad4 bs (56 * 2 + 12)))
      by (rewrite (ad_ewx regs bs M regsT 55%nat 23%nat eq_refl ltac:(lia));
          unfold adextra, adrowv; cbn [map app nth]; reflexivity).
    assert (NEXT : forall (E' : env) (ms' : machine_state) (md' : Model),
      st_ok_pi SEGS VAL E' (adbz 2) (restrict (w_H W) ms') ->
      sh_ok SEGS ADBx adSH E' (mrestrict (w_H W) (ms_mem ms')) ->
      img_env VAL A_LIM E' ->
      ajournal SEGS B REAC_BOXREG_ADD_STK (spZ regs) [(r, r + REG_SIZE)] ly S W mem md []
        ly S W (ms_mem ms') md' 0 ->
      (forall a : Z, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 80 <= a < spZ regs) ->
         aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) memT a) ->
      env_agree 113 (adET regs bs M regsT) E' ->
      ~ (Boxreg.bx_mac bs 2 = Boxreg.zero6 /\ Boxreg.bx_nch bs 2 = k) ->
      SRr SEGS W (mkCfg ms' md') (treac_boxreg_add_post regs ly S W mem md r k bs M)).
    { clear HS SHOK KEEP0.
      intros E' ms' md' HSn SHOKn HEIn HJn KEEPn AGe FACT.
      pose proof (proj1 AGe) as AG.
      assert (Usp' : bv_unsigned (ew E' 2) = spZ regs) by (rewrite (AG 2%nat ltac:(lia)); exact Usp).
      assert (E1' : ew E' 1 = getr regs 1) by (rewrite (AG 1%nat ltac:(lia)); exact E1).
      assert (HAE' : env_agree 32 (Ereg regs (adextra bs M)) E')
        by (eapply env_agree_trans;
            [exact HAE | split; [intros nn Hnn; apply AG; lia | exact (proj2 AGe)]]).
      paj_run_tok RUN HSn HJn SHOKn ADspan; [awr_ok_tac; exact Usp' |].
      ad_upd KEEPn Usp' W (spZ regs - 80) (spZ regs).
      psrr_branch_tok RUN BR HSn SHOKn ADspan.
      { (* i + 1 <> n: the next row *)
        ad_atg AG E105 105%nat E105a.
        rewrite (ad_bne_lit _ 3 105%nat (Boxreg.bx_n bs) E105a ltac:(lia) ltac:(lia)) in Hc.
        apply negb_true_iff, Z.eqb_neq in Hc.
        paj_run_to_tok RUNTO HSn HJn SHOKn ADspan 7512; [awr_ok_tac; exact Usp' |].
        ad_upd KEEPn Usp' W (spZ regs - 80) (spZ regs).
        ad_ag113x (adET regs bs M regsT) AGe AGn.
        pmkst HSn.
        refine (IH ly S W regs mem md ch r p k bs M _ _ _ 3
          HPRE H10 H11 H12 Hk Hin Hinv HML HMnz HWO HNH _ _ _
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CONT).
        - lia.
        - lia.
        - intros j Hj. destruct (Z.eq_dec j 2) as [->|Hne]; [exact FACT | apply HINV; lia].
        - ad_qreg (adET regs bs M regsT) AGn (2%bv : bv 5). exact Dsp.
        - ad_qreg (adET regs bs M regsT) AGn (3%bv : bv 5). exact D3.
        - ad_qreg (adET regs bs M regsT) AGn (4%bv : bv 5). exact D4.
        - ad_qreg (adET regs bs M regsT) AGn (8%bv : bv 5). exact Dk.
        - ad_qreg (adET regs bs M regsT) AGn (9%bv : bv 5). exact Dp.
        - ad_qreg (adET regs bs M regsT) AGn (12%bv : bv 5). rewrite Dr. unfold w64. f_equal; try lia.
        - ad_qreg (adET regs bs M regsT) AGn (13%bv : bv 5). rewrite Dr. unfold w64. f_equal; try lia.
        - ad_qreg (adET regs bs M regsT) AGn (18%bv : bv 5). rewrite Dr. unfold w64. f_equal; try lia.
        - ad_qreg (adET regs bs M regsT) AGn (19%bv : bv 5). rewrite Dr. unfold w64. f_equal; try lia.
        - ad_qreg (adET regs bs M regsT) AGn (20%bv : bv 5). cbn [sv_denot]. unfold w64. f_equal; try lia.
        - ad_qreg (adET regs bs M regsT) AGn (22%bv : bv 5). exact D32.
        - ad_qreg (adET regs bs M regsT) AGn (23%bv : bv 5). exact D7.
        - ad_qreg (adET regs bs M regsT) AGn (24%bv : bv 5).
          rewrite (ad_ewj_den regs bs M regsT 105%nat 24%nat eq_refl ltac:(lia)).
          cbn [adrl nth]. exact R24.
        - ad_qreg (adET regs bs M regsT) AGn (25%bv : bv 5). exact D25.
        - ad_qreg (adET regs bs M regsT) AGn (26%bv : bv 5). exact D26.
        - ad_qreg (adET regs bs M regsT) AGn (27%bv : bv 5). exact D27.
        - eapply ad_frame_of_st;
            [ exact HSn | reflexivity | rewrite ((proj1 AGn) 2%nat ltac:(lia)); exact Usp
            | intros nn x Hnn Hx; rewrite ((proj1 AGn) nn ltac:(lia));
              apply (ad_ewr regs bs M regsT nn x Hx Hnn) ].
        - intros o Ho. change REG_SIZE with 288 in Ho. rewrite KEEPn by lia. exact (Hbs o Ho).
        - lazymatch goal with |- afobj _ _ _ _ _ ?mx _ _ =>
            apply (ad_afobj_keep W ly S memT mx p (spZ regs - 80) (spZ regs) HFO KEEPn) end.
          intros x Hx. apply (adb_shadow_out regs ly p C1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) x Hx).
        - intros o Ho. rewrite KEEPn by lia. exact (HMv o Ho).
        - exact HJn. }
      { (* i + 1 = n: the loop is over *)
        ad_atg AG E105 105%nat E105a.
        rewrite (ad_bne_lit _ 3 105%nat (Boxreg.bx_n bs) E105a ltac:(lia) ltac:(lia)) in Hc.
        apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HEQn.
        paj_run_tok RUN HSn HJn SHOKn ADspan; [awr_ok_tac; exact Usp' |].
        ad_upd KEEPn Usp' W (spZ regs - 80) (spZ regs).
        psrr_branch_tok RUN BR HSn SHOKn ADspan.
        { (* n <= 4: the new-row tail at 0x81d90 *)
          ad_atg AG E33 33%nat E33a.
          rewrite (ad_bge4 _ 33%nat (ad4 bs 280) E33a (ad_4_rng bs 280)) in Hc.
          apply negb_true_iff, Z.ltb_ge in Hc. rewrite <- (ad_bx_n bs HLbs) in Hc.
          paj_run_to_tok RUNTO HSn HJn SHOKn ADspan 7748; [awr_ok_tac; exact Usp' |].
          ad_upd KEEPn Usp' W (spZ regs - 80) (spZ regs).
          ad_ag113x (adET regs bs M regsT) AGe AGn.
          pmkst HSn.
          refine (CONT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
          - ad_qreg (adET regs bs M regsT) AGn (2%bv : bv 5). exact Dsp.
          - ad_qreg (adET regs bs M regsT) AGn (3%bv : bv 5). exact D3.
          - ad_qreg (adET regs bs M regsT) AGn (4%bv : bv 5). exact D4.
          - ad_qreg (adET regs bs M regsT) AGn (8%bv : bv 5). exact Dk.
          - ad_qreg (adET regs bs M regsT) AGn (9%bv : bv 5). exact Dp.
          - ad_qreg (adET regs bs M regsT) AGn (18%bv : bv 5). rewrite Dr. unfold w64. f_equal; try lia.
          - ad_qreg (adET regs bs M regsT) AGn (19%bv : bv 5). rewrite Dr. unfold w64. f_equal; try lia.
          - ad_qreg (adET regs bs M regsT) AGn (22%bv : bv 5). exact D32.
          - ad_qreg (adET regs bs M regsT) AGn (23%bv : bv 5). exact D7.
          - ad_qreg (adET regs bs M regsT) AGn (24%bv : bv 5).
            rewrite (ad_sext_den (adET regs bs M regsT) 33%nat (ad4 bs 280) E33 (ad_4_rng bs 280)).
            rewrite <- (ad_bx_n bs HLbs). reflexivity.
          - ad_qreg (adET regs bs M regsT) AGn (25%bv : bv 5). exact D25.
          - ad_qreg (adET regs bs M regsT) AGn (26%bv : bv 5). exact D26.
          - ad_qreg (adET regs bs M regsT) AGn (27%bv : bv 5). exact D27.
          - eapply ad_frame_of_st;
              [ exact HSn | reflexivity | rewrite ((proj1 AGn) 2%nat ltac:(lia)); exact Usp
              | intros nn x Hnn Hx; rewrite ((proj1 AGn) nn ltac:(lia));
                apply (ad_ewr regs bs M regsT nn x Hx Hnn) ].
          - intros o Ho. change REG_SIZE with 288 in Ho. rewrite KEEPn by lia. exact (Hbs o Ho).
          - lazymatch goal with |- afobj _ _ _ _ _ ?mx _ _ =>
              apply (ad_afobj_keep W ly S memT mx p (spZ regs - 80) (spZ regs) HFO KEEPn) end.
            intros x Hx. apply (adb_shadow_out regs ly p C1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) x Hx).
          - intros o Ho. rewrite KEEPn by lia. exact (HMv o Ho).
          - exact HJn.
          - intros j Hj. destruct (Z.eq_dec j 2) as [->|Hne]; [exact FACT | apply HINV; lia].
          - lia. }
        { (* 5 <= n: the function returns -1 *)
          ad_atg AG E33 33%nat E33a.
          rewrite (ad_bge4 _ 33%nat (ad4 bs 280) E33a (ad_4_rng bs 280)) in Hc.
          apply negb_false_iff, Z.ltb_lt in Hc. rewrite <- (ad_bx_n bs HLbs) in Hc.
          paj_run_tok RUN HSn HJn SHOKn ADspan; [awr_ok_tac; exact Usp' |].
          ad_upd KEEPn Usp' W (spZ regs - 80) (spZ regs).
          ad_ret HSn HJn E1' Hra HAE' (-1) bs.
          split.
          - right. right. right. left.
            split; [exact HWO|]. split; [exact HMnz|]. split; [exact HNH|].
            split; [intros j Hj; destruct (Z.eq_dec j 2) as [->|Hne];
                    [exact FACT | apply HINV; lia]|].
            split; [left; lia|]. split; reflexivity.
          - intros o Ho. change REG_SIZE with 288 in Ho. rewrite KEEPn by lia. exact (Hbs o Ho). } } }
    paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
    ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
    psrr_branch_tok RUN BR HS SHOK ADspan.
    { (* the MAC byte 0 of the row is not zero *)
      ad_at EB0 49%nat EBa0.
      rewrite (ad_bnz_b _ 49%nat bs (56 * 2 + 0) EBa0) in Hc.
      apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into HNZ.
      paj_run_to_tok RUNTO HS HJ SHOK ADspan 7632; [awr_ok_tac; exact Usp |].
      ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
      ad_ag113 (adET regs bs M regsT) AGx;
                lazymatch goal with
                | HSx : st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?Wx) ?msx) |- _ =>
                  pose proof (adbz_reabs 2 Ex (abs_ss VAL ss) (restrict (w_H Wx) msx)
                    (getr (ms_regs (restrict (w_H Wx) msx)) 11) (getr (ms_regs (restrict (w_H Wx) msx)) 14)
                    (getr (ms_regs (restrict (w_H Wx) msx)) 15) (getr (ms_regs (restrict (w_H Wx) msx)) 16)
                    (getr (ms_regs (restrict (w_H Wx) msx)) 17)
                    ltac:(lia) HSx ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                    eq_refl eq_refl eq_refl eq_refl eq_refl) as HSm
                end;
                apply (NEXT _ _ _ HSm
                  ltac:(apply adbz_shok; exact SHOK) ltac:(apply adbz_img; assumption)
                  HJ KEEP0
                  ltac:(split;
                        [ intros nn Hnn; rewrite (adbz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn
                        | reflexivity ])
                  ltac:(intros Hzz; apply HNZ;
                  exact (proj1 (ad_mac_zero bs 2 HLbs ltac:(lia)) (proj1 Hzz) 0 ltac:(lia)))). }
    { (* the MAC byte 0 of the row is zero *)
      ad_at EB0 49%nat EBz0.
      rewrite (ad_bnz_b _ 49%nat bs (56 * 2 + 0) EBz0) in Hc.
      apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HZ0.
      paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
      ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
      psrr_branch_tok RUN BR HS SHOK ADspan.
      { (* the MAC byte 1 of the row is not zero *)
        ad_at EB1 50%nat EBa1.
        rewrite (ad_bnz_b _ 50%nat bs (56 * 2 + 1) EBa1) in Hc.
        apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into HNZ.
        paj_run_to_tok RUNTO HS HJ SHOK ADspan 7632; [awr_ok_tac; exact Usp |].
        ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
        ad_ag113 (adET regs bs M regsT) AGx;
                  lazymatch goal with
                  | HSx : st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?Wx) ?msx) |- _ =>
                    pose proof (adbz_reabs 2 Ex (abs_ss VAL ss) (restrict (w_H Wx) msx)
                      (getr (ms_regs (restrict (w_H Wx) msx)) 11) (getr (ms_regs (restrict (w_H Wx) msx)) 14)
                      (getr (ms_regs (restrict (w_H Wx) msx)) 15) (getr (ms_regs (restrict (w_H Wx) msx)) 16)
                      (getr (ms_regs (restrict (w_H Wx) msx)) 17)
                      ltac:(lia) HSx ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                      eq_refl eq_refl eq_refl eq_refl eq_refl) as HSm
                  end;
                  apply (NEXT _ _ _ HSm
                    ltac:(apply adbz_shok; exact SHOK) ltac:(apply adbz_img; assumption)
                    HJ KEEP0
                    ltac:(split;
                          [ intros nn Hnn; rewrite (adbz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn
                          | reflexivity ])
                    ltac:(intros Hzz; apply HNZ;
                    exact (proj1 (ad_mac_zero bs 2 HLbs ltac:(lia)) (proj1 Hzz) 1 ltac:(lia)))). }
      { (* the MAC byte 1 of the row is zero *)
        ad_at EB1 50%nat EBz1.
        rewrite (ad_bnz_b _ 50%nat bs (56 * 2 + 1) EBz1) in Hc.
        apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HZ1.
        paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
        ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
        psrr_branch_tok RUN BR HS SHOK ADspan.
        { (* the MAC byte 2 of the row is not zero *)
          ad_at EB2 51%nat EBa2.
          rewrite (ad_bnz_b _ 51%nat bs (56 * 2 + 2) EBa2) in Hc.
          apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into HNZ.
          paj_run_to_tok RUNTO HS HJ SHOK ADspan 7632; [awr_ok_tac; exact Usp |].
          ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
          ad_ag113 (adET regs bs M regsT) AGx;
                    lazymatch goal with
                    | HSx : st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?Wx) ?msx) |- _ =>
                      pose proof (adbz_reabs 2 Ex (abs_ss VAL ss) (restrict (w_H Wx) msx)
                        (getr (ms_regs (restrict (w_H Wx) msx)) 11) (getr (ms_regs (restrict (w_H Wx) msx)) 14)
                        (getr (ms_regs (restrict (w_H Wx) msx)) 15) (getr (ms_regs (restrict (w_H Wx) msx)) 16)
                        (getr (ms_regs (restrict (w_H Wx) msx)) 17)
                        ltac:(lia) HSx ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                        eq_refl eq_refl eq_refl eq_refl eq_refl) as HSm
                    end;
                    apply (NEXT _ _ _ HSm
                      ltac:(apply adbz_shok; exact SHOK) ltac:(apply adbz_img; assumption)
                      HJ KEEP0
                      ltac:(split;
                            [ intros nn Hnn; rewrite (adbz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn
                            | reflexivity ])
                      ltac:(intros Hzz; apply HNZ;
                      exact (proj1 (ad_mac_zero bs 2 HLbs ltac:(lia)) (proj1 Hzz) 2 ltac:(lia)))). }
        { (* the MAC byte 2 of the row is zero *)
          ad_at EB2 51%nat EBz2.
          rewrite (ad_bnz_b _ 51%nat bs (56 * 2 + 2) EBz2) in Hc.
          apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HZ2.
          paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
          ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
          psrr_branch_tok RUN BR HS SHOK ADspan.
          { (* the MAC byte 3 of the row is not zero *)
            ad_at EB3 52%nat EBa3.
            rewrite (ad_bnz_b _ 52%nat bs (56 * 2 + 3) EBa3) in Hc.
            apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into HNZ.
            paj_run_to_tok RUNTO HS HJ SHOK ADspan 7632; [awr_ok_tac; exact Usp |].
            ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
            ad_ag113 (adET regs bs M regsT) AGx;
                      lazymatch goal with
                      | HSx : st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?Wx) ?msx) |- _ =>
                        pose proof (adbz_reabs 2 Ex (abs_ss VAL ss) (restrict (w_H Wx) msx)
                          (getr (ms_regs (restrict (w_H Wx) msx)) 11) (getr (ms_regs (restrict (w_H Wx) msx)) 14)
                          (getr (ms_regs (restrict (w_H Wx) msx)) 15) (getr (ms_regs (restrict (w_H Wx) msx)) 16)
                          (getr (ms_regs (restrict (w_H Wx) msx)) 17)
                          ltac:(lia) HSx ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                          eq_refl eq_refl eq_refl eq_refl eq_refl) as HSm
                      end;
                      apply (NEXT _ _ _ HSm
                        ltac:(apply adbz_shok; exact SHOK) ltac:(apply adbz_img; assumption)
                        HJ KEEP0
                        ltac:(split;
                              [ intros nn Hnn; rewrite (adbz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn
                              | reflexivity ])
                        ltac:(intros Hzz; apply HNZ;
                        exact (proj1 (ad_mac_zero bs 2 HLbs ltac:(lia)) (proj1 Hzz) 3 ltac:(lia)))). }
          { (* the MAC byte 3 of the row is zero *)
            ad_at EB3 52%nat EBz3.
            rewrite (ad_bnz_b _ 52%nat bs (56 * 2 + 3) EBz3) in Hc.
            apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HZ3.
            paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
            ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
            psrr_branch_tok RUN BR HS SHOK ADspan.
            { (* the MAC byte 4 of the row is not zero *)
              ad_at EB4 53%nat EBa4.
              rewrite (ad_bnz_b _ 53%nat bs (56 * 2 + 4) EBa4) in Hc.
              apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into HNZ.
              paj_run_to_tok RUNTO HS HJ SHOK ADspan 7632; [awr_ok_tac; exact Usp |].
              ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
              ad_ag113 (adET regs bs M regsT) AGx;
                        lazymatch goal with
                        | HSx : st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?Wx) ?msx) |- _ =>
                          pose proof (adbz_reabs 2 Ex (abs_ss VAL ss) (restrict (w_H Wx) msx)
                            (getr (ms_regs (restrict (w_H Wx) msx)) 11) (getr (ms_regs (restrict (w_H Wx) msx)) 14)
                            (getr (ms_regs (restrict (w_H Wx) msx)) 15) (getr (ms_regs (restrict (w_H Wx) msx)) 16)
                            (getr (ms_regs (restrict (w_H Wx) msx)) 17)
                            ltac:(lia) HSx ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                            eq_refl eq_refl eq_refl eq_refl eq_refl) as HSm
                        end;
                        apply (NEXT _ _ _ HSm
                          ltac:(apply adbz_shok; exact SHOK) ltac:(apply adbz_img; assumption)
                          HJ KEEP0
                          ltac:(split;
                                [ intros nn Hnn; rewrite (adbz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn
                                | reflexivity ])
                          ltac:(intros Hzz; apply HNZ;
                          exact (proj1 (ad_mac_zero bs 2 HLbs ltac:(lia)) (proj1 Hzz) 4 ltac:(lia)))). }
            { (* the MAC byte 4 of the row is zero *)
              ad_at EB4 53%nat EBz4.
              rewrite (ad_bnz_b _ 53%nat bs (56 * 2 + 4) EBz4) in Hc.
              apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HZ4.
              paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
              ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
              psrr_branch_tok RUN BR HS SHOK ADspan.
              { (* the MAC byte 5 of the row is not zero *)
                ad_at EB5 54%nat EBa5.
                rewrite (ad_bnz_b _ 54%nat bs (56 * 2 + 5) EBa5) in Hc.
                apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into HNZ.
                paj_run_to_tok RUNTO HS HJ SHOK ADspan 7632; [awr_ok_tac; exact Usp |].
                ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
                ad_ag113 (adET regs bs M regsT) AGx;
                          lazymatch goal with
                          | HSx : st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?Wx) ?msx) |- _ =>
                            pose proof (adbz_reabs 2 Ex (abs_ss VAL ss) (restrict (w_H Wx) msx)
                              (getr (ms_regs (restrict (w_H Wx) msx)) 11) (getr (ms_regs (restrict (w_H Wx) msx)) 14)
                              (getr (ms_regs (restrict (w_H Wx) msx)) 15) (getr (ms_regs (restrict (w_H Wx) msx)) 16)
                              (getr (ms_regs (restrict (w_H Wx) msx)) 17)
                              ltac:(lia) HSx ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                              eq_refl eq_refl eq_refl eq_refl eq_refl) as HSm
                          end;
                          apply (NEXT _ _ _ HSm
                            ltac:(apply adbz_shok; exact SHOK) ltac:(apply adbz_img; assumption)
                            HJ KEEP0
                            ltac:(split;
                                  [ intros nn Hnn; rewrite (adbz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn
                                  | reflexivity ])
                            ltac:(intros Hzz; apply HNZ;
                            exact (proj1 (ad_mac_zero bs 2 HLbs ltac:(lia)) (proj1 Hzz) 5 ltac:(lia)))). }
              { (* the MAC byte 5 of the row is zero *)
                ad_at EB5 54%nat EBz5.
                rewrite (ad_bnz_b _ 54%nat bs (56 * 2 + 5) EBz5) in Hc.
                apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HZ5.
                paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
                ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
                assert (HMZ : Boxreg.bx_mac bs 2 = Boxreg.zero6).
                { apply (proj2 (ad_mac_zero bs 2 HLbs ltac:(lia))). intros jj Hjj.
                  assert (Hj6 : jj = 0 \/ jj = 1 \/ jj = 2 \/ jj = 3 \/ jj = 4 \/ jj = 5) by lia.
                  destruct Hj6 as [-> | [-> | [-> | [-> | [-> | ->]]]]];
                    [exact HZ0 | exact HZ1 | exact HZ2 | exact HZ3 | exact HZ4 | exact HZ5]. }
                ad_at ENC 55%nat ENCa. ad_at E12a 12%nat E12b.
                psrr_branch_tok RUN BR HS SHOK ADspan.
                { rewrite (ad_beq_sext _ 55%nat (ad4 bs (56 * 2 + 12)) 12%nat k ENCa (ad_4_rng bs (56 * 2 + 12)) E12b Hk) in Hc.
                  apply Z.eqb_eq in Hc. rewrite <- (ad_bx_nch bs 2 HLbs ltac:(lia)) in Hc.
                  paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
                            ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
                            ad_ag113 (adET regs bs M regsT) AGb.
                            assert (HspR : 0 <= spZ regs - 80 < 2 ^ 64) by lia.
                            lazymatch goal with
                            | HSx : st_ok _ ?Ex ?ss (restrict (w_H W) ?msx) |- _ =>
                              assert (HFRm : adfr regs W (ms_mem msx))
                                by (eapply ad_frame_of_st;
                                    [ exact HSx | reflexivity | rewrite ?(AGb 2%nat ltac:(lia)); exact Usp
                                    | intros nn x Hnn Hx; rewrite ?(AGb nn ltac:(lia));
                                      apply (ad_ewr regs bs M regsT nn x Hx Hnn) ]);
                              assert (HFOm : afobj SEGS B ly S W (ms_mem msx) p 6)
                                by (apply (ad_afobj_keep W ly S memT (ms_mem msx) p (spZ regs - 80) (spZ regs) HFO KEEP0);
                                    intros x Hx;
                                    apply (adb_shadow_out regs ly p C1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) x Hx));
                              assert (HMvm : forall o, 0 <= o < 6 ->
                                        aview SEGS (w_H W) (ms_mem msx) (p + o) = Some (adtb M o))
                                by (intros o Ho; rewrite KEEP0 by lia; exact (HMv o Ho));
                              assert (Hbsm : forall o, 0 <= o < 288 ->
                                        aview SEGS (w_H W) (ms_mem msx) (r + o) = Some (adtb bs o))
                                by (intros o Ho; rewrite KEEP0 by lia; apply Hbs; unfold REG_SIZE; lia)
                            end.
                            pmkst HS.
                            prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
                            prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp.
                            prreg HS (4%bv : bv 5) Rtp. prreg HS (20%bv : bv 5) Rs4.
                            prreg HS (25%bv : bv 5) Rs9. prreg HS (26%bv : bv 5) Rs10. prreg HS (27%bv : bv 5) Rs11.
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qa0 : getr rg2 (10%bv : bv 5) = w64 (r + 56 * 2)) end.
                            { rewrite Ra0. rewrite ?(AGb 10%nat ltac:(lia)).
                              rewrite (ad_ewr regs bs M regsT 10%nat 10%bv eq_refl ltac:(lia)), H10.
                              unfold w64. rewrite ?unsigned_lit_small by lia. f_equal; try lia. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qa1 : getr rg2 (11%bv : bv 5) = w64 p) end.
                            { rewrite Ra1. rewrite ?(AGb 11%nat ltac:(lia)).
                              rewrite (ad_ewr regs bs M regsT 11%nat 11%bv eq_refl ltac:(lia)), H11.
                              unfold w64. rewrite ?unsigned_lit_small by lia. f_equal; try lia. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qa2 : getr rg2 (12%bv : bv 5) = w64 6) end.
                            { rewrite Ra2. reflexivity. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qsp2 : getr rg2 (2%bv : bv 5) = w64 (spZ regs - 80)) end.
                            { rewrite Rsp. rewrite ?(AGb 2%nat ltac:(lia)).
                              rewrite (ad_ewr regs bs M regsT 2%nat 2%bv eq_refl ltac:(lia)).
                              unfold spZ, w64. f_equal; try lia. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qsp : spZ rg2 = spZ regs + -80) end.
                            { unfold spZ at 1. rewrite Qsp2. unfold w64.
                              rewrite unsigned_lit_small by lia. lia. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qgp : getr rg2 (3%bv : bv 5) = w64 (as_gp B)) end.
                            { rewrite Rgp. rewrite ?(AGb 3%nat ltac:(lia)).
                              rewrite (ad_ewr regs bs M regsT 3%nat 3%bv eq_refl ltac:(lia)). exact Hgp. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qtp : getr rg2 (4%bv : bv 5) = w64 (as_tp B)) end.
                            { rewrite Rtp. rewrite ?(AGb 4%nat ltac:(lia)).
                              rewrite (ad_ewr regs bs M regsT 4%nat 4%bv eq_refl ltac:(lia)). exact Htp. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qs4 : getr rg2 (20%bv : bv 5) = w64 2) end.
                            { rewrite Rs4. reflexivity. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qs9 : getr rg2 (25%bv : bv 5) = getr regs 25) end.
                            { rewrite Rs9. rewrite ?(AGb 25%nat ltac:(lia)).
                              apply (ad_ewr regs bs M regsT 25%nat 25%bv eq_refl ltac:(lia)). }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qs10 : getr rg2 (26%bv : bv 5) = getr regs 26) end.
                            { rewrite Rs10. rewrite ?(AGb 26%nat ltac:(lia)).
                              apply (ad_ewr regs bs M regsT 26%nat 26%bv eq_refl ltac:(lia)). }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qs11 : getr rg2 (27%bv : bv 5) = getr regs 27) end.
                            { rewrite Rs11. rewrite ?(AGb 27%nat ltac:(lia)).
                              apply (ad_ewr regs bs M regsT 27%nat 27%bv eq_refl ltac:(lia)). }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ ?mm _) _) _ =>
                              eapply SRr_bind;
                              [ eapply (aj_intrin_at SEGS B LAWS Hsegs OCpy (SIGMA BS___asan_memcpy) AMEMCPY W rg2 mm
                                  REAC_BOXREG_ADD_STK (spZ regs) [(r, r + REG_SIZE)] ly S W mem md (@nil (Z * Z)) ly S _ 0
                                  (r + 56 * 2) p 6 (-80) _ HJ) | ] end.
                            { exact Qa0. }
                            { exact Qa1. }
                            { exact Qa2. }
                            { lia. }
                            { lia. }
                            { lia. }
                            { exact Qsp. }
                            { reflexivity. }
                            { lia. }
                            { rewrite WS. unfold ESTACK. lia. }
                            { exact Qgp. }
                            { exact Qtp. }
                            { exact Rra. }
                            { apply ret_ok_codeptr_v; [lia | reflexivity]. }
                            { intros a Ha. split.
                              - right. left. split.
                                + exists (r, r + REG_SIZE). split; [left; reflexivity | cbn [fst snd]; unfold REG_SIZE; lia].
                                + exists r, REG_SIZE. split; [exact Hin | change (req_size REG_SIZE) with 288; lia].
                              - unfold ESTACK. lia. }
                            { eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hin);
                                change (req_size REG_SIZE) with 288; lia. }
                            { eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hin);
                                change (req_size REG_SIZE) with 288; lia. }
                            { intros _.
                              eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hin);
                                change (req_size REG_SIZE) with 288; lia. }
                            { split; [lia|]. split; [lia|]. split.
                              - intros a Ha. split.
                                + replace a with (p + (a - p)) by lia.
                                  rewrite (HMvm (a - p) ltac:(lia)). discriminate.
                                + rewrite Qsp. unfold ESTACK. lia.
                              - split; [destruct Hrf as [Hd1|Hd2]; [left; lia | right; lia]|].
                                split.
                                + apply (amem_range_sub_app (frame_addr ly cid pos) (fs_frame_bytes cid) p 6
                                           Hfapp Hfceil ltac:(lia) ltac:(lia) ltac:(lia)).
                                + split; [exact (proj2 (proj2 HFOm))|].
                                  intros _.
                                  lazymatch goal with |- shadow_hull_vis (aview _ _ ?mm) _ _ =>
                                    apply (BoxFrame.shadow_hull_vis_of_frame SEGS B LAWS ly S W mm _ cid pos p 6
                                             (proj1 HJ) Hfin ltac:(lia) ltac:(lia) ltac:(lia)) end. }
                            cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0 & Heff & Hfr2 & Hpres2).
                            lazymatch goal with
                            | HFRx : adfr regs W ?mm |- _ =>
                              apply (ad_tailret ly S W regs mem md ch r k 2 bs M
                                       (BoxregUpd.bind_bytes bs M 2) regs2 mem2 md2 HPRE HJ2 Hin);
                              [ apply (ad_fr_of_aview W regs mm mem2);
                                [ intros a Ha; apply Hfr2; [lia | lia | unfold ESTACK; lia] | exact HFRx ] | .. ]
                            end.
                            { rewrite (ad_pres_get _ regs2 (2%bv : bv 5) 2 HP2 eq_refl
                                 ltac:(unfold acallee_saved; lia)). exact Qsp2. }
                            { rewrite (ad_pres_get _ regs2 (20%bv : bv 5) 20 HP2 eq_refl
                                 ltac:(unfold acallee_saved; lia)). exact Qs4. }
                            { rewrite (ad_pres_get _ regs2 (3%bv : bv 5) 3 HP2 eq_refl
                                 ltac:(unfold acallee_saved; lia)). rewrite Qgp. symmetry. exact Hgp. }
                            { rewrite (ad_pres_get _ regs2 (4%bv : bv 5) 4 HP2 eq_refl
                                 ltac:(unfold acallee_saved; lia)). rewrite Qtp. symmetry. exact Htp. }
                            { rewrite (ad_pres_get _ regs2 (25%bv : bv 5) 25 HP2 eq_refl
                                 ltac:(unfold acallee_saved; lia)). exact Qs9. }
                            { rewrite (ad_pres_get _ regs2 (26%bv : bv 5) 26 HP2 eq_refl
                                 ltac:(unfold acallee_saved; lia)). exact Qs10. }
                            { rewrite (ad_pres_get _ regs2 (27%bv : bv 5) 27 HP2 eq_refl
                                 ltac:(unfold acallee_saved; lia)). exact Qs11. }
                            { lia. }
                            { right. right. left.
                              split; [exact HWO|]. split; [exact HMnz|]. split; [exact HNH|].
                              split.
                              - split; [lia|]. split; [exact HMZ|]. split; [exact Hc|].
                                intros j Hj. apply HINV. lia.
                              - reflexivity. }
                            { intros o Ho. change REG_SIZE with 288 in Ho.
                              rewrite (ad_bind_view bs M 2 o HLbs HML ltac:(lia) ltac:(lia)).
                              destruct (Z.leb_spec (56 * 2) o) as [HA|HA];
                              destruct (Z.ltb_spec o (56 * 2 + 6)) as [HBb|HBb]; cbn [andb];
                              first
                              [ replace (r + o) with ((r + 56 * 2) + (o - 56 * 2)) by lia;
                                rewrite (Heff (o - 56 * 2) ltac:(lia));
                                rewrite (HMvm (o - 56 * 2) ltac:(lia)); reflexivity
                              | rewrite (Hfr2 (r + o) ltac:(lia) ltac:(lia) ltac:(unfold ESTACK; lia));
                                exact (Hbsm o ltac:(lia)) ]. }
                }
                { rewrite (ad_beq_sext _ 55%nat (ad4 bs (56 * 2 + 12)) 12%nat k ENCa (ad_4_rng bs (56 * 2 + 12)) E12b Hk) in Hc.
                  apply Z.eqb_neq in Hc. rewrite <- (ad_bx_nch bs 2 HLbs ltac:(lia)) in Hc.
                  paj_run_to_tok RUNTO HS HJ SHOK ADspan 7632; [awr_ok_tac; exact Usp |].
                  ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
                  ad_ag113 (adET regs bs M regsT) AGx;
                            lazymatch goal with
                            | HSx : st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?Wx) ?msx) |- _ =>
                              pose proof (adbz_reabs 2 Ex (abs_ss VAL ss) (restrict (w_H Wx) msx)
                                (getr (ms_regs (restrict (w_H Wx) msx)) 11) (getr (ms_regs (restrict (w_H Wx) msx)) 14)
                                (getr (ms_regs (restrict (w_H Wx) msx)) 15) (getr (ms_regs (restrict (w_H Wx) msx)) 16)
                                (getr (ms_regs (restrict (w_H Wx) msx)) 17)
                                ltac:(lia) HSx ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                                eq_refl eq_refl eq_refl eq_refl eq_refl) as HSm
                            end;
                            apply (NEXT _ _ _ HSm
                              ltac:(apply adbz_shok; exact SHOK) ltac:(apply adbz_img; assumption)
                              HJ KEEP0
                              ltac:(split;
                                    [ intros nn Hnn; rewrite (adbz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn
                                    | reflexivity ])
                              ltac:(intros Hzz; exact (Hc (proj2 Hzz)))). }
}}}}}}
  + (* ---------------- row 3 ---------------- *)
    assert (EB0 : ew (adET regs bs M regsT) 56%nat = Z_to_bv 64 (adtb bs (56 * 3 + 0)))
      by (rewrite (ad_ewx regs bs M regsT 56%nat 24%nat eq_refl ltac:(lia));
          unfold adextra, adrowv; cbn [map app nth]; reflexivity).
    assert (EB1 : ew (adET regs bs M regsT) 57%nat = Z_to_bv 64 (adtb bs (56 * 3 + 1)))
      by (rewrite (ad_ewx regs bs M regsT 57%nat 25%nat eq_refl ltac:(lia));
          unfold adextra, adrowv; cbn [map app nth]; reflexivity).
    assert (EB2 : ew (adET regs bs M regsT) 58%nat = Z_to_bv 64 (adtb bs (56 * 3 + 2)))
      by (rewrite (ad_ewx regs bs M regsT 58%nat 26%nat eq_refl ltac:(lia));
          unfold adextra, adrowv; cbn [map app nth]; reflexivity).
    assert (EB3 : ew (adET regs bs M regsT) 59%nat = Z_to_bv 64 (adtb bs (56 * 3 + 3)))
      by (rewrite (ad_ewx regs bs M regsT 59%nat 27%nat eq_refl ltac:(lia));
          unfold adextra, adrowv; cbn [map app nth]; reflexivity).
    assert (EB4 : ew (adET regs bs M regsT) 60%nat = Z_to_bv 64 (adtb bs (56 * 3 + 4)))
      by (rewrite (ad_ewx regs bs M regsT 60%nat 28%nat eq_refl ltac:(lia));
          unfold adextra, adrowv; cbn [map app nth]; reflexivity).
    assert (EB5 : ew (adET regs bs M regsT) 61%nat = Z_to_bv 64 (adtb bs (56 * 3 + 5)))
      by (rewrite (ad_ewx regs bs M regsT 61%nat 29%nat eq_refl ltac:(lia));
          unfold adextra, adrowv; cbn [map app nth]; reflexivity).
    assert (ENC : ew (adET regs bs M regsT) 62%nat = Z_to_bv 64 (ad4 bs (56 * 3 + 12)))
      by (rewrite (ad_ewx regs bs M regsT 62%nat 30%nat eq_refl ltac:(lia));
          unfold adextra, adrowv; cbn [map app nth]; reflexivity).
    assert (NEXT : forall (E' : env) (ms' : machine_state) (md' : Model),
      st_ok_pi SEGS VAL E' (adbz 3) (restrict (w_H W) ms') ->
      sh_ok SEGS ADBx adSH E' (mrestrict (w_H W) (ms_mem ms')) ->
      img_env VAL A_LIM E' ->
      ajournal SEGS B REAC_BOXREG_ADD_STK (spZ regs) [(r, r + REG_SIZE)] ly S W mem md []
        ly S W (ms_mem ms') md' 0 ->
      (forall a : Z, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 80 <= a < spZ regs) ->
         aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) memT a) ->
      env_agree 113 (adET regs bs M regsT) E' ->
      ~ (Boxreg.bx_mac bs 3 = Boxreg.zero6 /\ Boxreg.bx_nch bs 3 = k) ->
      SRr SEGS W (mkCfg ms' md') (treac_boxreg_add_post regs ly S W mem md r k bs M)).
    { clear HS SHOK KEEP0.
      intros E' ms' md' HSn SHOKn HEIn HJn KEEPn AGe FACT.
      pose proof (proj1 AGe) as AG.
      assert (Usp' : bv_unsigned (ew E' 2) = spZ regs) by (rewrite (AG 2%nat ltac:(lia)); exact Usp).
      assert (E1' : ew E' 1 = getr regs 1) by (rewrite (AG 1%nat ltac:(lia)); exact E1).
      assert (HAE' : env_agree 32 (Ereg regs (adextra bs M)) E')
        by (eapply env_agree_trans;
            [exact HAE | split; [intros nn Hnn; apply AG; lia | exact (proj2 AGe)]]).
      paj_run_tok RUN HSn HJn SHOKn ADspan; [awr_ok_tac; exact Usp' |].
      ad_upd KEEPn Usp' W (spZ regs - 80) (spZ regs).
      psrr_branch_tok RUN BR HSn SHOKn ADspan.
      { (* i + 1 <> n: the next row *)
        ad_atg AG E105 105%nat E105a.
        rewrite (ad_bne_lit _ 4 105%nat (Boxreg.bx_n bs) E105a ltac:(lia) ltac:(lia)) in Hc.
        apply negb_true_iff, Z.eqb_neq in Hc.
        paj_run_to_tok RUNTO HSn HJn SHOKn ADspan 7512; [awr_ok_tac; exact Usp' |].
        ad_upd KEEPn Usp' W (spZ regs - 80) (spZ regs).
        ad_ag113x (adET regs bs M regsT) AGe AGn.
        pmkst HSn.
        refine (IH ly S W regs mem md ch r p k bs M _ _ _ 4
          HPRE H10 H11 H12 Hk Hin Hinv HML HMnz HWO HNH _ _ _
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CONT).
        - lia.
        - lia.
        - intros j Hj. destruct (Z.eq_dec j 3) as [->|Hne]; [exact FACT | apply HINV; lia].
        - ad_qreg (adET regs bs M regsT) AGn (2%bv : bv 5). exact Dsp.
        - ad_qreg (adET regs bs M regsT) AGn (3%bv : bv 5). exact D3.
        - ad_qreg (adET regs bs M regsT) AGn (4%bv : bv 5). exact D4.
        - ad_qreg (adET regs bs M regsT) AGn (8%bv : bv 5). exact Dk.
        - ad_qreg (adET regs bs M regsT) AGn (9%bv : bv 5). exact Dp.
        - ad_qreg (adET regs bs M regsT) AGn (12%bv : bv 5). rewrite Dr. unfold w64. f_equal; try lia.
        - ad_qreg (adET regs bs M regsT) AGn (13%bv : bv 5). rewrite Dr. unfold w64. f_equal; try lia.
        - ad_qreg (adET regs bs M regsT) AGn (18%bv : bv 5). rewrite Dr. unfold w64. f_equal; try lia.
        - ad_qreg (adET regs bs M regsT) AGn (19%bv : bv 5). rewrite Dr. unfold w64. f_equal; try lia.
        - ad_qreg (adET regs bs M regsT) AGn (20%bv : bv 5). cbn [sv_denot]. unfold w64. f_equal; try lia.
        - ad_qreg (adET regs bs M regsT) AGn (22%bv : bv 5). exact D32.
        - ad_qreg (adET regs bs M regsT) AGn (23%bv : bv 5). exact D7.
        - ad_qreg (adET regs bs M regsT) AGn (24%bv : bv 5).
          rewrite (ad_ewj_den regs bs M regsT 105%nat 24%nat eq_refl ltac:(lia)).
          cbn [adrl nth]. exact R24.
        - ad_qreg (adET regs bs M regsT) AGn (25%bv : bv 5). exact D25.
        - ad_qreg (adET regs bs M regsT) AGn (26%bv : bv 5). exact D26.
        - ad_qreg (adET regs bs M regsT) AGn (27%bv : bv 5). exact D27.
        - eapply ad_frame_of_st;
            [ exact HSn | reflexivity | rewrite ((proj1 AGn) 2%nat ltac:(lia)); exact Usp
            | intros nn x Hnn Hx; rewrite ((proj1 AGn) nn ltac:(lia));
              apply (ad_ewr regs bs M regsT nn x Hx Hnn) ].
        - intros o Ho. change REG_SIZE with 288 in Ho. rewrite KEEPn by lia. exact (Hbs o Ho).
        - lazymatch goal with |- afobj _ _ _ _ _ ?mx _ _ =>
            apply (ad_afobj_keep W ly S memT mx p (spZ regs - 80) (spZ regs) HFO KEEPn) end.
          intros x Hx. apply (adb_shadow_out regs ly p C1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) x Hx).
        - intros o Ho. rewrite KEEPn by lia. exact (HMv o Ho).
        - exact HJn. }
      { (* i + 1 = n: the loop is over *)
        ad_atg AG E105 105%nat E105a.
        rewrite (ad_bne_lit _ 4 105%nat (Boxreg.bx_n bs) E105a ltac:(lia) ltac:(lia)) in Hc.
        apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HEQn.
        paj_run_tok RUN HSn HJn SHOKn ADspan; [awr_ok_tac; exact Usp' |].
        ad_upd KEEPn Usp' W (spZ regs - 80) (spZ regs).
        psrr_branch_tok RUN BR HSn SHOKn ADspan.
        { (* n <= 4: the new-row tail at 0x81d90 *)
          ad_atg AG E33 33%nat E33a.
          rewrite (ad_bge4 _ 33%nat (ad4 bs 280) E33a (ad_4_rng bs 280)) in Hc.
          apply negb_true_iff, Z.ltb_ge in Hc. rewrite <- (ad_bx_n bs HLbs) in Hc.
          paj_run_to_tok RUNTO HSn HJn SHOKn ADspan 7748; [awr_ok_tac; exact Usp' |].
          ad_upd KEEPn Usp' W (spZ regs - 80) (spZ regs).
          ad_ag113x (adET regs bs M regsT) AGe AGn.
          pmkst HSn.
          refine (CONT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
          - ad_qreg (adET regs bs M regsT) AGn (2%bv : bv 5). exact Dsp.
          - ad_qreg (adET regs bs M regsT) AGn (3%bv : bv 5). exact D3.
          - ad_qreg (adET regs bs M regsT) AGn (4%bv : bv 5). exact D4.
          - ad_qreg (adET regs bs M regsT) AGn (8%bv : bv 5). exact Dk.
          - ad_qreg (adET regs bs M regsT) AGn (9%bv : bv 5). exact Dp.
          - ad_qreg (adET regs bs M regsT) AGn (18%bv : bv 5). rewrite Dr. unfold w64. f_equal; try lia.
          - ad_qreg (adET regs bs M regsT) AGn (19%bv : bv 5). rewrite Dr. unfold w64. f_equal; try lia.
          - ad_qreg (adET regs bs M regsT) AGn (22%bv : bv 5). exact D32.
          - ad_qreg (adET regs bs M regsT) AGn (23%bv : bv 5). exact D7.
          - ad_qreg (adET regs bs M regsT) AGn (24%bv : bv 5).
            rewrite (ad_sext_den (adET regs bs M regsT) 33%nat (ad4 bs 280) E33 (ad_4_rng bs 280)).
            rewrite <- (ad_bx_n bs HLbs). reflexivity.
          - ad_qreg (adET regs bs M regsT) AGn (25%bv : bv 5). exact D25.
          - ad_qreg (adET regs bs M regsT) AGn (26%bv : bv 5). exact D26.
          - ad_qreg (adET regs bs M regsT) AGn (27%bv : bv 5). exact D27.
          - eapply ad_frame_of_st;
              [ exact HSn | reflexivity | rewrite ((proj1 AGn) 2%nat ltac:(lia)); exact Usp
              | intros nn x Hnn Hx; rewrite ((proj1 AGn) nn ltac:(lia));
                apply (ad_ewr regs bs M regsT nn x Hx Hnn) ].
          - intros o Ho. change REG_SIZE with 288 in Ho. rewrite KEEPn by lia. exact (Hbs o Ho).
          - lazymatch goal with |- afobj _ _ _ _ _ ?mx _ _ =>
              apply (ad_afobj_keep W ly S memT mx p (spZ regs - 80) (spZ regs) HFO KEEPn) end.
            intros x Hx. apply (adb_shadow_out regs ly p C1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) x Hx).
          - intros o Ho. rewrite KEEPn by lia. exact (HMv o Ho).
          - exact HJn.
          - intros j Hj. destruct (Z.eq_dec j 3) as [->|Hne]; [exact FACT | apply HINV; lia].
          - lia. }
        { (* 5 <= n: the function returns -1 *)
          ad_atg AG E33 33%nat E33a.
          rewrite (ad_bge4 _ 33%nat (ad4 bs 280) E33a (ad_4_rng bs 280)) in Hc.
          apply negb_false_iff, Z.ltb_lt in Hc. rewrite <- (ad_bx_n bs HLbs) in Hc.
          paj_run_tok RUN HSn HJn SHOKn ADspan; [awr_ok_tac; exact Usp' |].
          ad_upd KEEPn Usp' W (spZ regs - 80) (spZ regs).
          ad_ret HSn HJn E1' Hra HAE' (-1) bs.
          split.
          - right. right. right. left.
            split; [exact HWO|]. split; [exact HMnz|]. split; [exact HNH|].
            split; [intros j Hj; destruct (Z.eq_dec j 3) as [->|Hne];
                    [exact FACT | apply HINV; lia]|].
            split; [left; lia|]. split; reflexivity.
          - intros o Ho. change REG_SIZE with 288 in Ho. rewrite KEEPn by lia. exact (Hbs o Ho). } } }
    paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
    ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
    psrr_branch_tok RUN BR HS SHOK ADspan.
    { (* the MAC byte 0 of the row is not zero *)
      ad_at EB0 56%nat EBa0.
      rewrite (ad_bnz_b _ 56%nat bs (56 * 3 + 0) EBa0) in Hc.
      apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into HNZ.
      paj_run_to_tok RUNTO HS HJ SHOK ADspan 7632; [awr_ok_tac; exact Usp |].
      ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
      ad_ag113 (adET regs bs M regsT) AGx;
                lazymatch goal with
                | HSx : st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?Wx) ?msx) |- _ =>
                  pose proof (adbz_reabs 3 Ex (abs_ss VAL ss) (restrict (w_H Wx) msx)
                    (getr (ms_regs (restrict (w_H Wx) msx)) 11) (getr (ms_regs (restrict (w_H Wx) msx)) 14)
                    (getr (ms_regs (restrict (w_H Wx) msx)) 15) (getr (ms_regs (restrict (w_H Wx) msx)) 16)
                    (getr (ms_regs (restrict (w_H Wx) msx)) 17)
                    ltac:(lia) HSx ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                    eq_refl eq_refl eq_refl eq_refl eq_refl) as HSm
                end;
                apply (NEXT _ _ _ HSm
                  ltac:(apply adbz_shok; exact SHOK) ltac:(apply adbz_img; assumption)
                  HJ KEEP0
                  ltac:(split;
                        [ intros nn Hnn; rewrite (adbz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn
                        | reflexivity ])
                  ltac:(intros Hzz; apply HNZ;
                  exact (proj1 (ad_mac_zero bs 3 HLbs ltac:(lia)) (proj1 Hzz) 0 ltac:(lia)))). }
    { (* the MAC byte 0 of the row is zero *)
      ad_at EB0 56%nat EBz0.
      rewrite (ad_bnz_b _ 56%nat bs (56 * 3 + 0) EBz0) in Hc.
      apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HZ0.
      paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
      ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
      psrr_branch_tok RUN BR HS SHOK ADspan.
      { (* the MAC byte 1 of the row is not zero *)
        ad_at EB1 57%nat EBa1.
        rewrite (ad_bnz_b _ 57%nat bs (56 * 3 + 1) EBa1) in Hc.
        apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into HNZ.
        paj_run_to_tok RUNTO HS HJ SHOK ADspan 7632; [awr_ok_tac; exact Usp |].
        ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
        ad_ag113 (adET regs bs M regsT) AGx;
                  lazymatch goal with
                  | HSx : st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?Wx) ?msx) |- _ =>
                    pose proof (adbz_reabs 3 Ex (abs_ss VAL ss) (restrict (w_H Wx) msx)
                      (getr (ms_regs (restrict (w_H Wx) msx)) 11) (getr (ms_regs (restrict (w_H Wx) msx)) 14)
                      (getr (ms_regs (restrict (w_H Wx) msx)) 15) (getr (ms_regs (restrict (w_H Wx) msx)) 16)
                      (getr (ms_regs (restrict (w_H Wx) msx)) 17)
                      ltac:(lia) HSx ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                      eq_refl eq_refl eq_refl eq_refl eq_refl) as HSm
                  end;
                  apply (NEXT _ _ _ HSm
                    ltac:(apply adbz_shok; exact SHOK) ltac:(apply adbz_img; assumption)
                    HJ KEEP0
                    ltac:(split;
                          [ intros nn Hnn; rewrite (adbz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn
                          | reflexivity ])
                    ltac:(intros Hzz; apply HNZ;
                    exact (proj1 (ad_mac_zero bs 3 HLbs ltac:(lia)) (proj1 Hzz) 1 ltac:(lia)))). }
      { (* the MAC byte 1 of the row is zero *)
        ad_at EB1 57%nat EBz1.
        rewrite (ad_bnz_b _ 57%nat bs (56 * 3 + 1) EBz1) in Hc.
        apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HZ1.
        paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
        ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
        psrr_branch_tok RUN BR HS SHOK ADspan.
        { (* the MAC byte 2 of the row is not zero *)
          ad_at EB2 58%nat EBa2.
          rewrite (ad_bnz_b _ 58%nat bs (56 * 3 + 2) EBa2) in Hc.
          apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into HNZ.
          paj_run_to_tok RUNTO HS HJ SHOK ADspan 7632; [awr_ok_tac; exact Usp |].
          ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
          ad_ag113 (adET regs bs M regsT) AGx;
                    lazymatch goal with
                    | HSx : st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?Wx) ?msx) |- _ =>
                      pose proof (adbz_reabs 3 Ex (abs_ss VAL ss) (restrict (w_H Wx) msx)
                        (getr (ms_regs (restrict (w_H Wx) msx)) 11) (getr (ms_regs (restrict (w_H Wx) msx)) 14)
                        (getr (ms_regs (restrict (w_H Wx) msx)) 15) (getr (ms_regs (restrict (w_H Wx) msx)) 16)
                        (getr (ms_regs (restrict (w_H Wx) msx)) 17)
                        ltac:(lia) HSx ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                        eq_refl eq_refl eq_refl eq_refl eq_refl) as HSm
                    end;
                    apply (NEXT _ _ _ HSm
                      ltac:(apply adbz_shok; exact SHOK) ltac:(apply adbz_img; assumption)
                      HJ KEEP0
                      ltac:(split;
                            [ intros nn Hnn; rewrite (adbz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn
                            | reflexivity ])
                      ltac:(intros Hzz; apply HNZ;
                      exact (proj1 (ad_mac_zero bs 3 HLbs ltac:(lia)) (proj1 Hzz) 2 ltac:(lia)))). }
        { (* the MAC byte 2 of the row is zero *)
          ad_at EB2 58%nat EBz2.
          rewrite (ad_bnz_b _ 58%nat bs (56 * 3 + 2) EBz2) in Hc.
          apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HZ2.
          paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
          ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
          psrr_branch_tok RUN BR HS SHOK ADspan.
          { (* the MAC byte 3 of the row is not zero *)
            ad_at EB3 59%nat EBa3.
            rewrite (ad_bnz_b _ 59%nat bs (56 * 3 + 3) EBa3) in Hc.
            apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into HNZ.
            paj_run_to_tok RUNTO HS HJ SHOK ADspan 7632; [awr_ok_tac; exact Usp |].
            ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
            ad_ag113 (adET regs bs M regsT) AGx;
                      lazymatch goal with
                      | HSx : st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?Wx) ?msx) |- _ =>
                        pose proof (adbz_reabs 3 Ex (abs_ss VAL ss) (restrict (w_H Wx) msx)
                          (getr (ms_regs (restrict (w_H Wx) msx)) 11) (getr (ms_regs (restrict (w_H Wx) msx)) 14)
                          (getr (ms_regs (restrict (w_H Wx) msx)) 15) (getr (ms_regs (restrict (w_H Wx) msx)) 16)
                          (getr (ms_regs (restrict (w_H Wx) msx)) 17)
                          ltac:(lia) HSx ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                          eq_refl eq_refl eq_refl eq_refl eq_refl) as HSm
                      end;
                      apply (NEXT _ _ _ HSm
                        ltac:(apply adbz_shok; exact SHOK) ltac:(apply adbz_img; assumption)
                        HJ KEEP0
                        ltac:(split;
                              [ intros nn Hnn; rewrite (adbz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn
                              | reflexivity ])
                        ltac:(intros Hzz; apply HNZ;
                        exact (proj1 (ad_mac_zero bs 3 HLbs ltac:(lia)) (proj1 Hzz) 3 ltac:(lia)))). }
          { (* the MAC byte 3 of the row is zero *)
            ad_at EB3 59%nat EBz3.
            rewrite (ad_bnz_b _ 59%nat bs (56 * 3 + 3) EBz3) in Hc.
            apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HZ3.
            paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
            ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
            psrr_branch_tok RUN BR HS SHOK ADspan.
            { (* the MAC byte 4 of the row is not zero *)
              ad_at EB4 60%nat EBa4.
              rewrite (ad_bnz_b _ 60%nat bs (56 * 3 + 4) EBa4) in Hc.
              apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into HNZ.
              paj_run_to_tok RUNTO HS HJ SHOK ADspan 7632; [awr_ok_tac; exact Usp |].
              ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
              ad_ag113 (adET regs bs M regsT) AGx;
                        lazymatch goal with
                        | HSx : st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?Wx) ?msx) |- _ =>
                          pose proof (adbz_reabs 3 Ex (abs_ss VAL ss) (restrict (w_H Wx) msx)
                            (getr (ms_regs (restrict (w_H Wx) msx)) 11) (getr (ms_regs (restrict (w_H Wx) msx)) 14)
                            (getr (ms_regs (restrict (w_H Wx) msx)) 15) (getr (ms_regs (restrict (w_H Wx) msx)) 16)
                            (getr (ms_regs (restrict (w_H Wx) msx)) 17)
                            ltac:(lia) HSx ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                            eq_refl eq_refl eq_refl eq_refl eq_refl) as HSm
                        end;
                        apply (NEXT _ _ _ HSm
                          ltac:(apply adbz_shok; exact SHOK) ltac:(apply adbz_img; assumption)
                          HJ KEEP0
                          ltac:(split;
                                [ intros nn Hnn; rewrite (adbz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn
                                | reflexivity ])
                          ltac:(intros Hzz; apply HNZ;
                          exact (proj1 (ad_mac_zero bs 3 HLbs ltac:(lia)) (proj1 Hzz) 4 ltac:(lia)))). }
            { (* the MAC byte 4 of the row is zero *)
              ad_at EB4 60%nat EBz4.
              rewrite (ad_bnz_b _ 60%nat bs (56 * 3 + 4) EBz4) in Hc.
              apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HZ4.
              paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
              ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
              psrr_branch_tok RUN BR HS SHOK ADspan.
              { (* the MAC byte 5 of the row is not zero *)
                ad_at EB5 61%nat EBa5.
                rewrite (ad_bnz_b _ 61%nat bs (56 * 3 + 5) EBa5) in Hc.
                apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into HNZ.
                paj_run_to_tok RUNTO HS HJ SHOK ADspan 7632; [awr_ok_tac; exact Usp |].
                ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
                ad_ag113 (adET regs bs M regsT) AGx;
                          lazymatch goal with
                          | HSx : st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?Wx) ?msx) |- _ =>
                            pose proof (adbz_reabs 3 Ex (abs_ss VAL ss) (restrict (w_H Wx) msx)
                              (getr (ms_regs (restrict (w_H Wx) msx)) 11) (getr (ms_regs (restrict (w_H Wx) msx)) 14)
                              (getr (ms_regs (restrict (w_H Wx) msx)) 15) (getr (ms_regs (restrict (w_H Wx) msx)) 16)
                              (getr (ms_regs (restrict (w_H Wx) msx)) 17)
                              ltac:(lia) HSx ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                              eq_refl eq_refl eq_refl eq_refl eq_refl) as HSm
                          end;
                          apply (NEXT _ _ _ HSm
                            ltac:(apply adbz_shok; exact SHOK) ltac:(apply adbz_img; assumption)
                            HJ KEEP0
                            ltac:(split;
                                  [ intros nn Hnn; rewrite (adbz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn
                                  | reflexivity ])
                            ltac:(intros Hzz; apply HNZ;
                            exact (proj1 (ad_mac_zero bs 3 HLbs ltac:(lia)) (proj1 Hzz) 5 ltac:(lia)))). }
              { (* the MAC byte 5 of the row is zero *)
                ad_at EB5 61%nat EBz5.
                rewrite (ad_bnz_b _ 61%nat bs (56 * 3 + 5) EBz5) in Hc.
                apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HZ5.
                paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
                ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
                assert (HMZ : Boxreg.bx_mac bs 3 = Boxreg.zero6).
                { apply (proj2 (ad_mac_zero bs 3 HLbs ltac:(lia))). intros jj Hjj.
                  assert (Hj6 : jj = 0 \/ jj = 1 \/ jj = 2 \/ jj = 3 \/ jj = 4 \/ jj = 5) by lia.
                  destruct Hj6 as [-> | [-> | [-> | [-> | [-> | ->]]]]];
                    [exact HZ0 | exact HZ1 | exact HZ2 | exact HZ3 | exact HZ4 | exact HZ5]. }
                ad_at ENC 62%nat ENCa. ad_at E12a 12%nat E12b.
                psrr_branch_tok RUN BR HS SHOK ADspan.
                { rewrite (ad_beq_sext _ 62%nat (ad4 bs (56 * 3 + 12)) 12%nat k ENCa (ad_4_rng bs (56 * 3 + 12)) E12b Hk) in Hc.
                  apply Z.eqb_eq in Hc. rewrite <- (ad_bx_nch bs 3 HLbs ltac:(lia)) in Hc.
                  paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
                            ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
                            ad_ag113 (adET regs bs M regsT) AGb.
                            assert (HspR : 0 <= spZ regs - 80 < 2 ^ 64) by lia.
                            lazymatch goal with
                            | HSx : st_ok _ ?Ex ?ss (restrict (w_H W) ?msx) |- _ =>
                              assert (HFRm : adfr regs W (ms_mem msx))
                                by (eapply ad_frame_of_st;
                                    [ exact HSx | reflexivity | rewrite ?(AGb 2%nat ltac:(lia)); exact Usp
                                    | intros nn x Hnn Hx; rewrite ?(AGb nn ltac:(lia));
                                      apply (ad_ewr regs bs M regsT nn x Hx Hnn) ]);
                              assert (HFOm : afobj SEGS B ly S W (ms_mem msx) p 6)
                                by (apply (ad_afobj_keep W ly S memT (ms_mem msx) p (spZ regs - 80) (spZ regs) HFO KEEP0);
                                    intros x Hx;
                                    apply (adb_shadow_out regs ly p C1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) x Hx));
                              assert (HMvm : forall o, 0 <= o < 6 ->
                                        aview SEGS (w_H W) (ms_mem msx) (p + o) = Some (adtb M o))
                                by (intros o Ho; rewrite KEEP0 by lia; exact (HMv o Ho));
                              assert (Hbsm : forall o, 0 <= o < 288 ->
                                        aview SEGS (w_H W) (ms_mem msx) (r + o) = Some (adtb bs o))
                                by (intros o Ho; rewrite KEEP0 by lia; apply Hbs; unfold REG_SIZE; lia)
                            end.
                            pmkst HS.
                            prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
                            prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp.
                            prreg HS (4%bv : bv 5) Rtp. prreg HS (20%bv : bv 5) Rs4.
                            prreg HS (25%bv : bv 5) Rs9. prreg HS (26%bv : bv 5) Rs10. prreg HS (27%bv : bv 5) Rs11.
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qa0 : getr rg2 (10%bv : bv 5) = w64 (r + 56 * 3)) end.
                            { rewrite Ra0. rewrite ?(AGb 10%nat ltac:(lia)).
                              rewrite (ad_ewr regs bs M regsT 10%nat 10%bv eq_refl ltac:(lia)), H10.
                              unfold w64. rewrite ?unsigned_lit_small by lia. f_equal; try lia. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qa1 : getr rg2 (11%bv : bv 5) = w64 p) end.
                            { rewrite Ra1. rewrite ?(AGb 11%nat ltac:(lia)).
                              rewrite (ad_ewr regs bs M regsT 11%nat 11%bv eq_refl ltac:(lia)), H11.
                              unfold w64. rewrite ?unsigned_lit_small by lia. f_equal; try lia. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qa2 : getr rg2 (12%bv : bv 5) = w64 6) end.
                            { rewrite Ra2. reflexivity. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qsp2 : getr rg2 (2%bv : bv 5) = w64 (spZ regs - 80)) end.
                            { rewrite Rsp. rewrite ?(AGb 2%nat ltac:(lia)).
                              rewrite (ad_ewr regs bs M regsT 2%nat 2%bv eq_refl ltac:(lia)).
                              unfold spZ, w64. f_equal; try lia. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qsp : spZ rg2 = spZ regs + -80) end.
                            { unfold spZ at 1. rewrite Qsp2. unfold w64.
                              rewrite unsigned_lit_small by lia. lia. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qgp : getr rg2 (3%bv : bv 5) = w64 (as_gp B)) end.
                            { rewrite Rgp. rewrite ?(AGb 3%nat ltac:(lia)).
                              rewrite (ad_ewr regs bs M regsT 3%nat 3%bv eq_refl ltac:(lia)). exact Hgp. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qtp : getr rg2 (4%bv : bv 5) = w64 (as_tp B)) end.
                            { rewrite Rtp. rewrite ?(AGb 4%nat ltac:(lia)).
                              rewrite (ad_ewr regs bs M regsT 4%nat 4%bv eq_refl ltac:(lia)). exact Htp. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qs4 : getr rg2 (20%bv : bv 5) = w64 3) end.
                            { rewrite Rs4. reflexivity. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qs9 : getr rg2 (25%bv : bv 5) = getr regs 25) end.
                            { rewrite Rs9. rewrite ?(AGb 25%nat ltac:(lia)).
                              apply (ad_ewr regs bs M regsT 25%nat 25%bv eq_refl ltac:(lia)). }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qs10 : getr rg2 (26%bv : bv 5) = getr regs 26) end.
                            { rewrite Rs10. rewrite ?(AGb 26%nat ltac:(lia)).
                              apply (ad_ewr regs bs M regsT 26%nat 26%bv eq_refl ltac:(lia)). }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qs11 : getr rg2 (27%bv : bv 5) = getr regs 27) end.
                            { rewrite Rs11. rewrite ?(AGb 27%nat ltac:(lia)).
                              apply (ad_ewr regs bs M regsT 27%nat 27%bv eq_refl ltac:(lia)). }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ ?mm _) _) _ =>
                              eapply SRr_bind;
                              [ eapply (aj_intrin_at SEGS B LAWS Hsegs OCpy (SIGMA BS___asan_memcpy) AMEMCPY W rg2 mm
                                  REAC_BOXREG_ADD_STK (spZ regs) [(r, r + REG_SIZE)] ly S W mem md (@nil (Z * Z)) ly S _ 0
                                  (r + 56 * 3) p 6 (-80) _ HJ) | ] end.
                            { exact Qa0. }
                            { exact Qa1. }
                            { exact Qa2. }
                            { lia. }
                            { lia. }
                            { lia. }
                            { exact Qsp. }
                            { reflexivity. }
                            { lia. }
                            { rewrite WS. unfold ESTACK. lia. }
                            { exact Qgp. }
                            { exact Qtp. }
                            { exact Rra. }
                            { apply ret_ok_codeptr_v; [lia | reflexivity]. }
                            { intros a Ha. split.
                              - right. left. split.
                                + exists (r, r + REG_SIZE). split; [left; reflexivity | cbn [fst snd]; unfold REG_SIZE; lia].
                                + exists r, REG_SIZE. split; [exact Hin | change (req_size REG_SIZE) with 288; lia].
                              - unfold ESTACK. lia. }
                            { eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hin);
                                change (req_size REG_SIZE) with 288; lia. }
                            { eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hin);
                                change (req_size REG_SIZE) with 288; lia. }
                            { intros _.
                              eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hin);
                                change (req_size REG_SIZE) with 288; lia. }
                            { split; [lia|]. split; [lia|]. split.
                              - intros a Ha. split.
                                + replace a with (p + (a - p)) by lia.
                                  rewrite (HMvm (a - p) ltac:(lia)). discriminate.
                                + rewrite Qsp. unfold ESTACK. lia.
                              - split; [destruct Hrf as [Hd1|Hd2]; [left; lia | right; lia]|].
                                split.
                                + apply (amem_range_sub_app (frame_addr ly cid pos) (fs_frame_bytes cid) p 6
                                           Hfapp Hfceil ltac:(lia) ltac:(lia) ltac:(lia)).
                                + split; [exact (proj2 (proj2 HFOm))|].
                                  intros _.
                                  lazymatch goal with |- shadow_hull_vis (aview _ _ ?mm) _ _ =>
                                    apply (BoxFrame.shadow_hull_vis_of_frame SEGS B LAWS ly S W mm _ cid pos p 6
                                             (proj1 HJ) Hfin ltac:(lia) ltac:(lia) ltac:(lia)) end. }
                            cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0 & Heff & Hfr2 & Hpres2).
                            lazymatch goal with
                            | HFRx : adfr regs W ?mm |- _ =>
                              apply (ad_tailret ly S W regs mem md ch r k 3 bs M
                                       (BoxregUpd.bind_bytes bs M 3) regs2 mem2 md2 HPRE HJ2 Hin);
                              [ apply (ad_fr_of_aview W regs mm mem2);
                                [ intros a Ha; apply Hfr2; [lia | lia | unfold ESTACK; lia] | exact HFRx ] | .. ]
                            end.
                            { rewrite (ad_pres_get _ regs2 (2%bv : bv 5) 2 HP2 eq_refl
                                 ltac:(unfold acallee_saved; lia)). exact Qsp2. }
                            { rewrite (ad_pres_get _ regs2 (20%bv : bv 5) 20 HP2 eq_refl
                                 ltac:(unfold acallee_saved; lia)). exact Qs4. }
                            { rewrite (ad_pres_get _ regs2 (3%bv : bv 5) 3 HP2 eq_refl
                                 ltac:(unfold acallee_saved; lia)). rewrite Qgp. symmetry. exact Hgp. }
                            { rewrite (ad_pres_get _ regs2 (4%bv : bv 5) 4 HP2 eq_refl
                                 ltac:(unfold acallee_saved; lia)). rewrite Qtp. symmetry. exact Htp. }
                            { rewrite (ad_pres_get _ regs2 (25%bv : bv 5) 25 HP2 eq_refl
                                 ltac:(unfold acallee_saved; lia)). exact Qs9. }
                            { rewrite (ad_pres_get _ regs2 (26%bv : bv 5) 26 HP2 eq_refl
                                 ltac:(unfold acallee_saved; lia)). exact Qs10. }
                            { rewrite (ad_pres_get _ regs2 (27%bv : bv 5) 27 HP2 eq_refl
                                 ltac:(unfold acallee_saved; lia)). exact Qs11. }
                            { lia. }
                            { right. right. left.
                              split; [exact HWO|]. split; [exact HMnz|]. split; [exact HNH|].
                              split.
                              - split; [lia|]. split; [exact HMZ|]. split; [exact Hc|].
                                intros j Hj. apply HINV. lia.
                              - reflexivity. }
                            { intros o Ho. change REG_SIZE with 288 in Ho.
                              rewrite (ad_bind_view bs M 3 o HLbs HML ltac:(lia) ltac:(lia)).
                              destruct (Z.leb_spec (56 * 3) o) as [HA|HA];
                              destruct (Z.ltb_spec o (56 * 3 + 6)) as [HBb|HBb]; cbn [andb];
                              first
                              [ replace (r + o) with ((r + 56 * 3) + (o - 56 * 3)) by lia;
                                rewrite (Heff (o - 56 * 3) ltac:(lia));
                                rewrite (HMvm (o - 56 * 3) ltac:(lia)); reflexivity
                              | rewrite (Hfr2 (r + o) ltac:(lia) ltac:(lia) ltac:(unfold ESTACK; lia));
                                exact (Hbsm o ltac:(lia)) ]. }
                }
                { rewrite (ad_beq_sext _ 62%nat (ad4 bs (56 * 3 + 12)) 12%nat k ENCa (ad_4_rng bs (56 * 3 + 12)) E12b Hk) in Hc.
                  apply Z.eqb_neq in Hc. rewrite <- (ad_bx_nch bs 3 HLbs ltac:(lia)) in Hc.
                  paj_run_to_tok RUNTO HS HJ SHOK ADspan 7632; [awr_ok_tac; exact Usp |].
                  ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
                  ad_ag113 (adET regs bs M regsT) AGx;
                            lazymatch goal with
                            | HSx : st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?Wx) ?msx) |- _ =>
                              pose proof (adbz_reabs 3 Ex (abs_ss VAL ss) (restrict (w_H Wx) msx)
                                (getr (ms_regs (restrict (w_H Wx) msx)) 11) (getr (ms_regs (restrict (w_H Wx) msx)) 14)
                                (getr (ms_regs (restrict (w_H Wx) msx)) 15) (getr (ms_regs (restrict (w_H Wx) msx)) 16)
                                (getr (ms_regs (restrict (w_H Wx) msx)) 17)
                                ltac:(lia) HSx ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                                eq_refl eq_refl eq_refl eq_refl eq_refl) as HSm
                            end;
                            apply (NEXT _ _ _ HSm
                              ltac:(apply adbz_shok; exact SHOK) ltac:(apply adbz_img; assumption)
                              HJ KEEP0
                              ltac:(split;
                                    [ intros nn Hnn; rewrite (adbz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn
                                    | reflexivity ])
                              ltac:(intros Hzz; exact (Hc (proj2 Hzz)))). }
}}}}}}
  + (* ---------------- row 4 ---------------- *)
    assert (EB0 : ew (adET regs bs M regsT) 63%nat = Z_to_bv 64 (adtb bs (56 * 4 + 0)))
      by (rewrite (ad_ewx regs bs M regsT 63%nat 31%nat eq_refl ltac:(lia));
          unfold adextra, adrowv; cbn [map app nth]; reflexivity).
    assert (EB1 : ew (adET regs bs M regsT) 64%nat = Z_to_bv 64 (adtb bs (56 * 4 + 1)))
      by (rewrite (ad_ewx regs bs M regsT 64%nat 32%nat eq_refl ltac:(lia));
          unfold adextra, adrowv; cbn [map app nth]; reflexivity).
    assert (EB2 : ew (adET regs bs M regsT) 65%nat = Z_to_bv 64 (adtb bs (56 * 4 + 2)))
      by (rewrite (ad_ewx regs bs M regsT 65%nat 33%nat eq_refl ltac:(lia));
          unfold adextra, adrowv; cbn [map app nth]; reflexivity).
    assert (EB3 : ew (adET regs bs M regsT) 66%nat = Z_to_bv 64 (adtb bs (56 * 4 + 3)))
      by (rewrite (ad_ewx regs bs M regsT 66%nat 34%nat eq_refl ltac:(lia));
          unfold adextra, adrowv; cbn [map app nth]; reflexivity).
    assert (EB4 : ew (adET regs bs M regsT) 67%nat = Z_to_bv 64 (adtb bs (56 * 4 + 4)))
      by (rewrite (ad_ewx regs bs M regsT 67%nat 35%nat eq_refl ltac:(lia));
          unfold adextra, adrowv; cbn [map app nth]; reflexivity).
    assert (EB5 : ew (adET regs bs M regsT) 68%nat = Z_to_bv 64 (adtb bs (56 * 4 + 5)))
      by (rewrite (ad_ewx regs bs M regsT 68%nat 36%nat eq_refl ltac:(lia));
          unfold adextra, adrowv; cbn [map app nth]; reflexivity).
    assert (ENC : ew (adET regs bs M regsT) 69%nat = Z_to_bv 64 (ad4 bs (56 * 4 + 12)))
      by (rewrite (ad_ewx regs bs M regsT 69%nat 37%nat eq_refl ltac:(lia));
          unfold adextra, adrowv; cbn [map app nth]; reflexivity).
    assert (NEXT : forall (E' : env) (ms' : machine_state) (md' : Model),
      st_ok_pi SEGS VAL E' (adbz 4) (restrict (w_H W) ms') ->
      sh_ok SEGS ADBx adSH E' (mrestrict (w_H W) (ms_mem ms')) ->
      img_env VAL A_LIM E' ->
      ajournal SEGS B REAC_BOXREG_ADD_STK (spZ regs) [(r, r + REG_SIZE)] ly S W mem md []
        ly S W (ms_mem ms') md' 0 ->
      (forall a : Z, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 80 <= a < spZ regs) ->
         aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) memT a) ->
      env_agree 113 (adET regs bs M regsT) E' ->
      ~ (Boxreg.bx_mac bs 4 = Boxreg.zero6 /\ Boxreg.bx_nch bs 4 = k) ->
      SRr SEGS W (mkCfg ms' md') (treac_boxreg_add_post regs ly S W mem md r k bs M)).
    { clear HS SHOK KEEP0.
      intros E' ms' md' HSn SHOKn HEIn HJn KEEPn AGe FACT.
      pose proof (proj1 AGe) as AG.
      assert (Usp' : bv_unsigned (ew E' 2) = spZ regs) by (rewrite (AG 2%nat ltac:(lia)); exact Usp).
      assert (E1' : ew E' 1 = getr regs 1) by (rewrite (AG 1%nat ltac:(lia)); exact E1).
      assert (HAE' : env_agree 32 (Ereg regs (adextra bs M)) E')
        by (eapply env_agree_trans;
            [exact HAE | split; [intros nn Hnn; apply AG; lia | exact (proj2 AGe)]]).
      paj_run_tok RUN HSn HJn SHOKn ADspan; [awr_ok_tac; exact Usp' |].
      ad_upd KEEPn Usp' W (spZ regs - 80) (spZ regs).
      psrr_branch_tok RUN BR HSn SHOKn ADspan.
      { (* i + 1 <> n: the next row *)
        ad_atg AG E105 105%nat E105a.
        rewrite (ad_bne_lit _ 5 105%nat (Boxreg.bx_n bs) E105a ltac:(lia) ltac:(lia)) in Hc.
        apply negb_true_iff, Z.eqb_neq in Hc.
        paj_run_to_tok RUNTO HSn HJn SHOKn ADspan 7512; [awr_ok_tac; exact Usp' |].
        ad_upd KEEPn Usp' W (spZ regs - 80) (spZ regs).
        ad_ag113x (adET regs bs M regsT) AGe AGn.
        pmkst HSn.
        refine (IH ly S W regs mem md ch r p k bs M _ _ _ 5
          HPRE H10 H11 H12 Hk Hin Hinv HML HMnz HWO HNH _ _ _
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CONT).
        - lia.
        - lia.
        - intros j Hj. destruct (Z.eq_dec j 4) as [->|Hne]; [exact FACT | apply HINV; lia].
        - ad_qreg (adET regs bs M regsT) AGn (2%bv : bv 5). exact Dsp.
        - ad_qreg (adET regs bs M regsT) AGn (3%bv : bv 5). exact D3.
        - ad_qreg (adET regs bs M regsT) AGn (4%bv : bv 5). exact D4.
        - ad_qreg (adET regs bs M regsT) AGn (8%bv : bv 5). exact Dk.
        - ad_qreg (adET regs bs M regsT) AGn (9%bv : bv 5). exact Dp.
        - ad_qreg (adET regs bs M regsT) AGn (12%bv : bv 5). rewrite Dr. unfold w64. f_equal; try lia.
        - ad_qreg (adET regs bs M regsT) AGn (13%bv : bv 5). rewrite Dr. unfold w64. f_equal; try lia.
        - ad_qreg (adET regs bs M regsT) AGn (18%bv : bv 5). rewrite Dr. unfold w64. f_equal; try lia.
        - ad_qreg (adET regs bs M regsT) AGn (19%bv : bv 5). rewrite Dr. unfold w64. f_equal; try lia.
        - ad_qreg (adET regs bs M regsT) AGn (20%bv : bv 5). cbn [sv_denot]. unfold w64. f_equal; try lia.
        - ad_qreg (adET regs bs M regsT) AGn (22%bv : bv 5). exact D32.
        - ad_qreg (adET regs bs M regsT) AGn (23%bv : bv 5). exact D7.
        - ad_qreg (adET regs bs M regsT) AGn (24%bv : bv 5).
          rewrite (ad_ewj_den regs bs M regsT 105%nat 24%nat eq_refl ltac:(lia)).
          cbn [adrl nth]. exact R24.
        - ad_qreg (adET regs bs M regsT) AGn (25%bv : bv 5). exact D25.
        - ad_qreg (adET regs bs M regsT) AGn (26%bv : bv 5). exact D26.
        - ad_qreg (adET regs bs M regsT) AGn (27%bv : bv 5). exact D27.
        - eapply ad_frame_of_st;
            [ exact HSn | reflexivity | rewrite ((proj1 AGn) 2%nat ltac:(lia)); exact Usp
            | intros nn x Hnn Hx; rewrite ((proj1 AGn) nn ltac:(lia));
              apply (ad_ewr regs bs M regsT nn x Hx Hnn) ].
        - intros o Ho. change REG_SIZE with 288 in Ho. rewrite KEEPn by lia. exact (Hbs o Ho).
        - lazymatch goal with |- afobj _ _ _ _ _ ?mx _ _ =>
            apply (ad_afobj_keep W ly S memT mx p (spZ regs - 80) (spZ regs) HFO KEEPn) end.
          intros x Hx. apply (adb_shadow_out regs ly p C1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) x Hx).
        - intros o Ho. rewrite KEEPn by lia. exact (HMv o Ho).
        - exact HJn. }
      { (* i + 1 = n: the loop is over *)
        ad_atg AG E105 105%nat E105a.
        rewrite (ad_bne_lit _ 5 105%nat (Boxreg.bx_n bs) E105a ltac:(lia) ltac:(lia)) in Hc.
        apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HEQn.
        paj_run_tok RUN HSn HJn SHOKn ADspan; [awr_ok_tac; exact Usp' |].
        ad_upd KEEPn Usp' W (spZ regs - 80) (spZ regs).
        psrr_branch_tok RUN BR HSn SHOKn ADspan.
        { (* n <= 4: the new-row tail at 0x81d90 *)
          ad_atg AG E33 33%nat E33a.
          rewrite (ad_bge4 _ 33%nat (ad4 bs 280) E33a (ad_4_rng bs 280)) in Hc.
          apply negb_true_iff, Z.ltb_ge in Hc. rewrite <- (ad_bx_n bs HLbs) in Hc.
          paj_run_to_tok RUNTO HSn HJn SHOKn ADspan 7748; [awr_ok_tac; exact Usp' |].
          ad_upd KEEPn Usp' W (spZ regs - 80) (spZ regs).
          ad_ag113x (adET regs bs M regsT) AGe AGn.
          pmkst HSn.
          refine (CONT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
          - ad_qreg (adET regs bs M regsT) AGn (2%bv : bv 5). exact Dsp.
          - ad_qreg (adET regs bs M regsT) AGn (3%bv : bv 5). exact D3.
          - ad_qreg (adET regs bs M regsT) AGn (4%bv : bv 5). exact D4.
          - ad_qreg (adET regs bs M regsT) AGn (8%bv : bv 5). exact Dk.
          - ad_qreg (adET regs bs M regsT) AGn (9%bv : bv 5). exact Dp.
          - ad_qreg (adET regs bs M regsT) AGn (18%bv : bv 5). rewrite Dr. unfold w64. f_equal; try lia.
          - ad_qreg (adET regs bs M regsT) AGn (19%bv : bv 5). rewrite Dr. unfold w64. f_equal; try lia.
          - ad_qreg (adET regs bs M regsT) AGn (22%bv : bv 5). exact D32.
          - ad_qreg (adET regs bs M regsT) AGn (23%bv : bv 5). exact D7.
          - ad_qreg (adET regs bs M regsT) AGn (24%bv : bv 5).
            rewrite (ad_sext_den (adET regs bs M regsT) 33%nat (ad4 bs 280) E33 (ad_4_rng bs 280)).
            rewrite <- (ad_bx_n bs HLbs). reflexivity.
          - ad_qreg (adET regs bs M regsT) AGn (25%bv : bv 5). exact D25.
          - ad_qreg (adET regs bs M regsT) AGn (26%bv : bv 5). exact D26.
          - ad_qreg (adET regs bs M regsT) AGn (27%bv : bv 5). exact D27.
          - eapply ad_frame_of_st;
              [ exact HSn | reflexivity | rewrite ((proj1 AGn) 2%nat ltac:(lia)); exact Usp
              | intros nn x Hnn Hx; rewrite ((proj1 AGn) nn ltac:(lia));
                apply (ad_ewr regs bs M regsT nn x Hx Hnn) ].
          - intros o Ho. change REG_SIZE with 288 in Ho. rewrite KEEPn by lia. exact (Hbs o Ho).
          - lazymatch goal with |- afobj _ _ _ _ _ ?mx _ _ =>
              apply (ad_afobj_keep W ly S memT mx p (spZ regs - 80) (spZ regs) HFO KEEPn) end.
            intros x Hx. apply (adb_shadow_out regs ly p C1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) x Hx).
          - intros o Ho. rewrite KEEPn by lia. exact (HMv o Ho).
          - exact HJn.
          - intros j Hj. destruct (Z.eq_dec j 4) as [->|Hne]; [exact FACT | apply HINV; lia].
          - lia. }
        { (* 5 <= n: the function returns -1 *)
          ad_atg AG E33 33%nat E33a.
          rewrite (ad_bge4 _ 33%nat (ad4 bs 280) E33a (ad_4_rng bs 280)) in Hc.
          apply negb_false_iff, Z.ltb_lt in Hc. rewrite <- (ad_bx_n bs HLbs) in Hc.
          paj_run_tok RUN HSn HJn SHOKn ADspan; [awr_ok_tac; exact Usp' |].
          ad_upd KEEPn Usp' W (spZ regs - 80) (spZ regs).
          ad_ret HSn HJn E1' Hra HAE' (-1) bs.
          split.
          - right. right. right. left.
            split; [exact HWO|]. split; [exact HMnz|]. split; [exact HNH|].
            split; [intros j Hj; destruct (Z.eq_dec j 4) as [->|Hne];
                    [exact FACT | apply HINV; lia]|].
            split; [left; lia|]. split; reflexivity.
          - intros o Ho. change REG_SIZE with 288 in Ho. rewrite KEEPn by lia. exact (Hbs o Ho). } } }
    paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
    ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
    psrr_branch_tok RUN BR HS SHOK ADspan.
    { (* the MAC byte 0 of the row is not zero *)
      ad_at EB0 63%nat EBa0.
      rewrite (ad_bnz_b _ 63%nat bs (56 * 4 + 0) EBa0) in Hc.
      apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into HNZ.
      paj_run_to_tok RUNTO HS HJ SHOK ADspan 7632; [awr_ok_tac; exact Usp |].
      ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
      ad_ag113 (adET regs bs M regsT) AGx;
                lazymatch goal with
                | HSx : st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?Wx) ?msx) |- _ =>
                  pose proof (adbz_reabs 4 Ex (abs_ss VAL ss) (restrict (w_H Wx) msx)
                    (getr (ms_regs (restrict (w_H Wx) msx)) 11) (getr (ms_regs (restrict (w_H Wx) msx)) 14)
                    (getr (ms_regs (restrict (w_H Wx) msx)) 15) (getr (ms_regs (restrict (w_H Wx) msx)) 16)
                    (getr (ms_regs (restrict (w_H Wx) msx)) 17)
                    ltac:(lia) HSx ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                    eq_refl eq_refl eq_refl eq_refl eq_refl) as HSm
                end;
                apply (NEXT _ _ _ HSm
                  ltac:(apply adbz_shok; exact SHOK) ltac:(apply adbz_img; assumption)
                  HJ KEEP0
                  ltac:(split;
                        [ intros nn Hnn; rewrite (adbz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn
                        | reflexivity ])
                  ltac:(intros Hzz; apply HNZ;
                  exact (proj1 (ad_mac_zero bs 4 HLbs ltac:(lia)) (proj1 Hzz) 0 ltac:(lia)))). }
    { (* the MAC byte 0 of the row is zero *)
      ad_at EB0 63%nat EBz0.
      rewrite (ad_bnz_b _ 63%nat bs (56 * 4 + 0) EBz0) in Hc.
      apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HZ0.
      paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
      ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
      psrr_branch_tok RUN BR HS SHOK ADspan.
      { (* the MAC byte 1 of the row is not zero *)
        ad_at EB1 64%nat EBa1.
        rewrite (ad_bnz_b _ 64%nat bs (56 * 4 + 1) EBa1) in Hc.
        apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into HNZ.
        paj_run_to_tok RUNTO HS HJ SHOK ADspan 7632; [awr_ok_tac; exact Usp |].
        ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
        ad_ag113 (adET regs bs M regsT) AGx;
                  lazymatch goal with
                  | HSx : st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?Wx) ?msx) |- _ =>
                    pose proof (adbz_reabs 4 Ex (abs_ss VAL ss) (restrict (w_H Wx) msx)
                      (getr (ms_regs (restrict (w_H Wx) msx)) 11) (getr (ms_regs (restrict (w_H Wx) msx)) 14)
                      (getr (ms_regs (restrict (w_H Wx) msx)) 15) (getr (ms_regs (restrict (w_H Wx) msx)) 16)
                      (getr (ms_regs (restrict (w_H Wx) msx)) 17)
                      ltac:(lia) HSx ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                      eq_refl eq_refl eq_refl eq_refl eq_refl) as HSm
                  end;
                  apply (NEXT _ _ _ HSm
                    ltac:(apply adbz_shok; exact SHOK) ltac:(apply adbz_img; assumption)
                    HJ KEEP0
                    ltac:(split;
                          [ intros nn Hnn; rewrite (adbz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn
                          | reflexivity ])
                    ltac:(intros Hzz; apply HNZ;
                    exact (proj1 (ad_mac_zero bs 4 HLbs ltac:(lia)) (proj1 Hzz) 1 ltac:(lia)))). }
      { (* the MAC byte 1 of the row is zero *)
        ad_at EB1 64%nat EBz1.
        rewrite (ad_bnz_b _ 64%nat bs (56 * 4 + 1) EBz1) in Hc.
        apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HZ1.
        paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
        ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
        psrr_branch_tok RUN BR HS SHOK ADspan.
        { (* the MAC byte 2 of the row is not zero *)
          ad_at EB2 65%nat EBa2.
          rewrite (ad_bnz_b _ 65%nat bs (56 * 4 + 2) EBa2) in Hc.
          apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into HNZ.
          paj_run_to_tok RUNTO HS HJ SHOK ADspan 7632; [awr_ok_tac; exact Usp |].
          ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
          ad_ag113 (adET regs bs M regsT) AGx;
                    lazymatch goal with
                    | HSx : st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?Wx) ?msx) |- _ =>
                      pose proof (adbz_reabs 4 Ex (abs_ss VAL ss) (restrict (w_H Wx) msx)
                        (getr (ms_regs (restrict (w_H Wx) msx)) 11) (getr (ms_regs (restrict (w_H Wx) msx)) 14)
                        (getr (ms_regs (restrict (w_H Wx) msx)) 15) (getr (ms_regs (restrict (w_H Wx) msx)) 16)
                        (getr (ms_regs (restrict (w_H Wx) msx)) 17)
                        ltac:(lia) HSx ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                        eq_refl eq_refl eq_refl eq_refl eq_refl) as HSm
                    end;
                    apply (NEXT _ _ _ HSm
                      ltac:(apply adbz_shok; exact SHOK) ltac:(apply adbz_img; assumption)
                      HJ KEEP0
                      ltac:(split;
                            [ intros nn Hnn; rewrite (adbz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn
                            | reflexivity ])
                      ltac:(intros Hzz; apply HNZ;
                      exact (proj1 (ad_mac_zero bs 4 HLbs ltac:(lia)) (proj1 Hzz) 2 ltac:(lia)))). }
        { (* the MAC byte 2 of the row is zero *)
          ad_at EB2 65%nat EBz2.
          rewrite (ad_bnz_b _ 65%nat bs (56 * 4 + 2) EBz2) in Hc.
          apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HZ2.
          paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
          ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
          psrr_branch_tok RUN BR HS SHOK ADspan.
          { (* the MAC byte 3 of the row is not zero *)
            ad_at EB3 66%nat EBa3.
            rewrite (ad_bnz_b _ 66%nat bs (56 * 4 + 3) EBa3) in Hc.
            apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into HNZ.
            paj_run_to_tok RUNTO HS HJ SHOK ADspan 7632; [awr_ok_tac; exact Usp |].
            ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
            ad_ag113 (adET regs bs M regsT) AGx;
                      lazymatch goal with
                      | HSx : st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?Wx) ?msx) |- _ =>
                        pose proof (adbz_reabs 4 Ex (abs_ss VAL ss) (restrict (w_H Wx) msx)
                          (getr (ms_regs (restrict (w_H Wx) msx)) 11) (getr (ms_regs (restrict (w_H Wx) msx)) 14)
                          (getr (ms_regs (restrict (w_H Wx) msx)) 15) (getr (ms_regs (restrict (w_H Wx) msx)) 16)
                          (getr (ms_regs (restrict (w_H Wx) msx)) 17)
                          ltac:(lia) HSx ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                          eq_refl eq_refl eq_refl eq_refl eq_refl) as HSm
                      end;
                      apply (NEXT _ _ _ HSm
                        ltac:(apply adbz_shok; exact SHOK) ltac:(apply adbz_img; assumption)
                        HJ KEEP0
                        ltac:(split;
                              [ intros nn Hnn; rewrite (adbz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn
                              | reflexivity ])
                        ltac:(intros Hzz; apply HNZ;
                        exact (proj1 (ad_mac_zero bs 4 HLbs ltac:(lia)) (proj1 Hzz) 3 ltac:(lia)))). }
          { (* the MAC byte 3 of the row is zero *)
            ad_at EB3 66%nat EBz3.
            rewrite (ad_bnz_b _ 66%nat bs (56 * 4 + 3) EBz3) in Hc.
            apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HZ3.
            paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
            ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
            psrr_branch_tok RUN BR HS SHOK ADspan.
            { (* the MAC byte 4 of the row is not zero *)
              ad_at EB4 67%nat EBa4.
              rewrite (ad_bnz_b _ 67%nat bs (56 * 4 + 4) EBa4) in Hc.
              apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into HNZ.
              paj_run_to_tok RUNTO HS HJ SHOK ADspan 7632; [awr_ok_tac; exact Usp |].
              ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
              ad_ag113 (adET regs bs M regsT) AGx;
                        lazymatch goal with
                        | HSx : st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?Wx) ?msx) |- _ =>
                          pose proof (adbz_reabs 4 Ex (abs_ss VAL ss) (restrict (w_H Wx) msx)
                            (getr (ms_regs (restrict (w_H Wx) msx)) 11) (getr (ms_regs (restrict (w_H Wx) msx)) 14)
                            (getr (ms_regs (restrict (w_H Wx) msx)) 15) (getr (ms_regs (restrict (w_H Wx) msx)) 16)
                            (getr (ms_regs (restrict (w_H Wx) msx)) 17)
                            ltac:(lia) HSx ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                            eq_refl eq_refl eq_refl eq_refl eq_refl) as HSm
                        end;
                        apply (NEXT _ _ _ HSm
                          ltac:(apply adbz_shok; exact SHOK) ltac:(apply adbz_img; assumption)
                          HJ KEEP0
                          ltac:(split;
                                [ intros nn Hnn; rewrite (adbz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn
                                | reflexivity ])
                          ltac:(intros Hzz; apply HNZ;
                          exact (proj1 (ad_mac_zero bs 4 HLbs ltac:(lia)) (proj1 Hzz) 4 ltac:(lia)))). }
            { (* the MAC byte 4 of the row is zero *)
              ad_at EB4 67%nat EBz4.
              rewrite (ad_bnz_b _ 67%nat bs (56 * 4 + 4) EBz4) in Hc.
              apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HZ4.
              paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
              ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
              psrr_branch_tok RUN BR HS SHOK ADspan.
              { (* the MAC byte 5 of the row is not zero *)
                ad_at EB5 68%nat EBa5.
                rewrite (ad_bnz_b _ 68%nat bs (56 * 4 + 5) EBa5) in Hc.
                apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into HNZ.
                paj_run_to_tok RUNTO HS HJ SHOK ADspan 7632; [awr_ok_tac; exact Usp |].
                ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
                ad_ag113 (adET regs bs M regsT) AGx;
                          lazymatch goal with
                          | HSx : st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?Wx) ?msx) |- _ =>
                            pose proof (adbz_reabs 4 Ex (abs_ss VAL ss) (restrict (w_H Wx) msx)
                              (getr (ms_regs (restrict (w_H Wx) msx)) 11) (getr (ms_regs (restrict (w_H Wx) msx)) 14)
                              (getr (ms_regs (restrict (w_H Wx) msx)) 15) (getr (ms_regs (restrict (w_H Wx) msx)) 16)
                              (getr (ms_regs (restrict (w_H Wx) msx)) 17)
                              ltac:(lia) HSx ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                              eq_refl eq_refl eq_refl eq_refl eq_refl) as HSm
                          end;
                          apply (NEXT _ _ _ HSm
                            ltac:(apply adbz_shok; exact SHOK) ltac:(apply adbz_img; assumption)
                            HJ KEEP0
                            ltac:(split;
                                  [ intros nn Hnn; rewrite (adbz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn
                                  | reflexivity ])
                            ltac:(intros Hzz; apply HNZ;
                            exact (proj1 (ad_mac_zero bs 4 HLbs ltac:(lia)) (proj1 Hzz) 5 ltac:(lia)))). }
              { (* the MAC byte 5 of the row is zero *)
                ad_at EB5 68%nat EBz5.
                rewrite (ad_bnz_b _ 68%nat bs (56 * 4 + 5) EBz5) in Hc.
                apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HZ5.
                paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
                ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
                assert (HMZ : Boxreg.bx_mac bs 4 = Boxreg.zero6).
                { apply (proj2 (ad_mac_zero bs 4 HLbs ltac:(lia))). intros jj Hjj.
                  assert (Hj6 : jj = 0 \/ jj = 1 \/ jj = 2 \/ jj = 3 \/ jj = 4 \/ jj = 5) by lia.
                  destruct Hj6 as [-> | [-> | [-> | [-> | [-> | ->]]]]];
                    [exact HZ0 | exact HZ1 | exact HZ2 | exact HZ3 | exact HZ4 | exact HZ5]. }
                ad_at ENC 69%nat ENCa. ad_at E12a 12%nat E12b.
                psrr_branch_tok RUN BR HS SHOK ADspan.
                { rewrite (ad_beq_sext _ 69%nat (ad4 bs (56 * 4 + 12)) 12%nat k ENCa (ad_4_rng bs (56 * 4 + 12)) E12b Hk) in Hc.
                  apply Z.eqb_eq in Hc. rewrite <- (ad_bx_nch bs 4 HLbs ltac:(lia)) in Hc.
                  paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
                            ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
                            ad_ag113 (adET regs bs M regsT) AGb.
                            assert (HspR : 0 <= spZ regs - 80 < 2 ^ 64) by lia.
                            lazymatch goal with
                            | HSx : st_ok _ ?Ex ?ss (restrict (w_H W) ?msx) |- _ =>
                              assert (HFRm : adfr regs W (ms_mem msx))
                                by (eapply ad_frame_of_st;
                                    [ exact HSx | reflexivity | rewrite ?(AGb 2%nat ltac:(lia)); exact Usp
                                    | intros nn x Hnn Hx; rewrite ?(AGb nn ltac:(lia));
                                      apply (ad_ewr regs bs M regsT nn x Hx Hnn) ]);
                              assert (HFOm : afobj SEGS B ly S W (ms_mem msx) p 6)
                                by (apply (ad_afobj_keep W ly S memT (ms_mem msx) p (spZ regs - 80) (spZ regs) HFO KEEP0);
                                    intros x Hx;
                                    apply (adb_shadow_out regs ly p C1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) x Hx));
                              assert (HMvm : forall o, 0 <= o < 6 ->
                                        aview SEGS (w_H W) (ms_mem msx) (p + o) = Some (adtb M o))
                                by (intros o Ho; rewrite KEEP0 by lia; exact (HMv o Ho));
                              assert (Hbsm : forall o, 0 <= o < 288 ->
                                        aview SEGS (w_H W) (ms_mem msx) (r + o) = Some (adtb bs o))
                                by (intros o Ho; rewrite KEEP0 by lia; apply Hbs; unfold REG_SIZE; lia)
                            end.
                            pmkst HS.
                            prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
                            prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp.
                            prreg HS (4%bv : bv 5) Rtp. prreg HS (20%bv : bv 5) Rs4.
                            prreg HS (25%bv : bv 5) Rs9. prreg HS (26%bv : bv 5) Rs10. prreg HS (27%bv : bv 5) Rs11.
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qa0 : getr rg2 (10%bv : bv 5) = w64 (r + 56 * 4)) end.
                            { rewrite Ra0. rewrite ?(AGb 10%nat ltac:(lia)).
                              rewrite (ad_ewr regs bs M regsT 10%nat 10%bv eq_refl ltac:(lia)), H10.
                              unfold w64. rewrite ?unsigned_lit_small by lia. f_equal; try lia. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qa1 : getr rg2 (11%bv : bv 5) = w64 p) end.
                            { rewrite Ra1. rewrite ?(AGb 11%nat ltac:(lia)).
                              rewrite (ad_ewr regs bs M regsT 11%nat 11%bv eq_refl ltac:(lia)), H11.
                              unfold w64. rewrite ?unsigned_lit_small by lia. f_equal; try lia. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qa2 : getr rg2 (12%bv : bv 5) = w64 6) end.
                            { rewrite Ra2. reflexivity. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qsp2 : getr rg2 (2%bv : bv 5) = w64 (spZ regs - 80)) end.
                            { rewrite Rsp. rewrite ?(AGb 2%nat ltac:(lia)).
                              rewrite (ad_ewr regs bs M regsT 2%nat 2%bv eq_refl ltac:(lia)).
                              unfold spZ, w64. f_equal; try lia. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qsp : spZ rg2 = spZ regs + -80) end.
                            { unfold spZ at 1. rewrite Qsp2. unfold w64.
                              rewrite unsigned_lit_small by lia. lia. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qgp : getr rg2 (3%bv : bv 5) = w64 (as_gp B)) end.
                            { rewrite Rgp. rewrite ?(AGb 3%nat ltac:(lia)).
                              rewrite (ad_ewr regs bs M regsT 3%nat 3%bv eq_refl ltac:(lia)). exact Hgp. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qtp : getr rg2 (4%bv : bv 5) = w64 (as_tp B)) end.
                            { rewrite Rtp. rewrite ?(AGb 4%nat ltac:(lia)).
                              rewrite (ad_ewr regs bs M regsT 4%nat 4%bv eq_refl ltac:(lia)). exact Htp. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qs4 : getr rg2 (20%bv : bv 5) = w64 4) end.
                            { rewrite Rs4. reflexivity. }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qs9 : getr rg2 (25%bv : bv 5) = getr regs 25) end.
                            { rewrite Rs9. rewrite ?(AGb 25%nat ltac:(lia)).
                              apply (ad_ewr regs bs M regsT 25%nat 25%bv eq_refl ltac:(lia)). }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qs10 : getr rg2 (26%bv : bv 5) = getr regs 26) end.
                            { rewrite Rs10. rewrite ?(AGb 26%nat ltac:(lia)).
                              apply (ad_ewr regs bs M regsT 26%nat 26%bv eq_refl ltac:(lia)). }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                              assert (Qs11 : getr rg2 (27%bv : bv 5) = getr regs 27) end.
                            { rewrite Rs11. rewrite ?(AGb 27%nat ltac:(lia)).
                              apply (ad_ewr regs bs M regsT 27%nat 27%bv eq_refl ltac:(lia)). }
                            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ ?mm _) _) _ =>
                              eapply SRr_bind;
                              [ eapply (aj_intrin_at SEGS B LAWS Hsegs OCpy (SIGMA BS___asan_memcpy) AMEMCPY W rg2 mm
                                  REAC_BOXREG_ADD_STK (spZ regs) [(r, r + REG_SIZE)] ly S W mem md (@nil (Z * Z)) ly S _ 0
                                  (r + 56 * 4) p 6 (-80) _ HJ) | ] end.
                            { exact Qa0. }
                            { exact Qa1. }
                            { exact Qa2. }
                            { lia. }
                            { lia. }
                            { lia. }
                            { exact Qsp. }
                            { reflexivity. }
                            { lia. }
                            { rewrite WS. unfold ESTACK. lia. }
                            { exact Qgp. }
                            { exact Qtp. }
                            { exact Rra. }
                            { apply ret_ok_codeptr_v; [lia | reflexivity]. }
                            { intros a Ha. split.
                              - right. left. split.
                                + exists (r, r + REG_SIZE). split; [left; reflexivity | cbn [fst snd]; unfold REG_SIZE; lia].
                                + exists r, REG_SIZE. split; [exact Hin | change (req_size REG_SIZE) with 288; lia].
                              - unfold ESTACK. lia. }
                            { eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hin);
                                change (req_size REG_SIZE) with 288; lia. }
                            { eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hin);
                                change (req_size REG_SIZE) with 288; lia. }
                            { intros _.
                              eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hin);
                                change (req_size REG_SIZE) with 288; lia. }
                            { split; [lia|]. split; [lia|]. split.
                              - intros a Ha. split.
                                + replace a with (p + (a - p)) by lia.
                                  rewrite (HMvm (a - p) ltac:(lia)). discriminate.
                                + rewrite Qsp. unfold ESTACK. lia.
                              - split; [destruct Hrf as [Hd1|Hd2]; [left; lia | right; lia]|].
                                split.
                                + apply (amem_range_sub_app (frame_addr ly cid pos) (fs_frame_bytes cid) p 6
                                           Hfapp Hfceil ltac:(lia) ltac:(lia) ltac:(lia)).
                                + split; [exact (proj2 (proj2 HFOm))|].
                                  intros _.
                                  lazymatch goal with |- shadow_hull_vis (aview _ _ ?mm) _ _ =>
                                    apply (BoxFrame.shadow_hull_vis_of_frame SEGS B LAWS ly S W mm _ cid pos p 6
                                             (proj1 HJ) Hfin ltac:(lia) ltac:(lia) ltac:(lia)) end. }
                            cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0 & Heff & Hfr2 & Hpres2).
                            lazymatch goal with
                            | HFRx : adfr regs W ?mm |- _ =>
                              apply (ad_tailret ly S W regs mem md ch r k 4 bs M
                                       (BoxregUpd.bind_bytes bs M 4) regs2 mem2 md2 HPRE HJ2 Hin);
                              [ apply (ad_fr_of_aview W regs mm mem2);
                                [ intros a Ha; apply Hfr2; [lia | lia | unfold ESTACK; lia] | exact HFRx ] | .. ]
                            end.
                            { rewrite (ad_pres_get _ regs2 (2%bv : bv 5) 2 HP2 eq_refl
                                 ltac:(unfold acallee_saved; lia)). exact Qsp2. }
                            { rewrite (ad_pres_get _ regs2 (20%bv : bv 5) 20 HP2 eq_refl
                                 ltac:(unfold acallee_saved; lia)). exact Qs4. }
                            { rewrite (ad_pres_get _ regs2 (3%bv : bv 5) 3 HP2 eq_refl
                                 ltac:(unfold acallee_saved; lia)). rewrite Qgp. symmetry. exact Hgp. }
                            { rewrite (ad_pres_get _ regs2 (4%bv : bv 5) 4 HP2 eq_refl
                                 ltac:(unfold acallee_saved; lia)). rewrite Qtp. symmetry. exact Htp. }
                            { rewrite (ad_pres_get _ regs2 (25%bv : bv 5) 25 HP2 eq_refl
                                 ltac:(unfold acallee_saved; lia)). exact Qs9. }
                            { rewrite (ad_pres_get _ regs2 (26%bv : bv 5) 26 HP2 eq_refl
                                 ltac:(unfold acallee_saved; lia)). exact Qs10. }
                            { rewrite (ad_pres_get _ regs2 (27%bv : bv 5) 27 HP2 eq_refl
                                 ltac:(unfold acallee_saved; lia)). exact Qs11. }
                            { lia. }
                            { right. right. left.
                              split; [exact HWO|]. split; [exact HMnz|]. split; [exact HNH|].
                              split.
                              - split; [lia|]. split; [exact HMZ|]. split; [exact Hc|].
                                intros j Hj. apply HINV. lia.
                              - reflexivity. }
                            { intros o Ho. change REG_SIZE with 288 in Ho.
                              rewrite (ad_bind_view bs M 4 o HLbs HML ltac:(lia) ltac:(lia)).
                              destruct (Z.leb_spec (56 * 4) o) as [HA|HA];
                              destruct (Z.ltb_spec o (56 * 4 + 6)) as [HBb|HBb]; cbn [andb];
                              first
                              [ replace (r + o) with ((r + 56 * 4) + (o - 56 * 4)) by lia;
                                rewrite (Heff (o - 56 * 4) ltac:(lia));
                                rewrite (HMvm (o - 56 * 4) ltac:(lia)); reflexivity
                              | rewrite (Hfr2 (r + o) ltac:(lia) ltac:(lia) ltac:(unfold ESTACK; lia));
                                exact (Hbsm o ltac:(lia)) ]. }
                }
                { rewrite (ad_beq_sext _ 69%nat (ad4 bs (56 * 4 + 12)) 12%nat k ENCa (ad_4_rng bs (56 * 4 + 12)) E12b Hk) in Hc.
                  apply Z.eqb_neq in Hc. rewrite <- (ad_bx_nch bs 4 HLbs ltac:(lia)) in Hc.
                  paj_run_to_tok RUNTO HS HJ SHOK ADspan 7632; [awr_ok_tac; exact Usp |].
                  ad_upd KEEP0 Usp W (spZ regs - 80) (spZ regs).
                  ad_ag113 (adET regs bs M regsT) AGx;
                            lazymatch goal with
                            | HSx : st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?Wx) ?msx) |- _ =>
                              pose proof (adbz_reabs 4 Ex (abs_ss VAL ss) (restrict (w_H Wx) msx)
                                (getr (ms_regs (restrict (w_H Wx) msx)) 11) (getr (ms_regs (restrict (w_H Wx) msx)) 14)
                                (getr (ms_regs (restrict (w_H Wx) msx)) 15) (getr (ms_regs (restrict (w_H Wx) msx)) 16)
                                (getr (ms_regs (restrict (w_H Wx) msx)) 17)
                                ltac:(lia) HSx ltac:(vm_compute; reflexivity) ltac:(reflexivity)
                                eq_refl eq_refl eq_refl eq_refl eq_refl) as HSm
                            end;
                            apply (NEXT _ _ _ HSm
                              ltac:(apply adbz_shok; exact SHOK) ltac:(apply adbz_img; assumption)
                              HJ KEEP0
                              ltac:(split;
                                    [ intros nn Hnn; rewrite (adbz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn
                                    | reflexivity ])
                              ltac:(intros Hzz; exact (Hc (proj2 Hzz)))). }
}}}}}}
Qed.
Theorem pb_reac_boxreg_add : treac_boxreg_add_spec.
Proof.
unfold treac_boxreg_add_spec.
intros ly S W regs mem md ch r p k bs M HPRE H10 H11 H12 Hk Hin Hbs Hinv HFO HML HMv.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
destruct (ad_entry ly S W regs mem md ch r p bs M HPRE H10 H11 Hin Hbs HFO HMv) as [HS SHOK].
pose proof (ajournal_init SEGS B REAC_BOXREG_ADD_STK [(r, r + REG_SIZE)] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hchn & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOXREG_ADD_STK = 8320) by reflexivity.
destruct (al_blocks SEGS B LAWS ly S W mem md r REG_SIZE HAR Hin)
  as (Hr16 & Hr4096 & Hrceil & Hria & Hrpres & _).
change (req_size REG_SIZE) with 288 in *.
rewrite WS in Hslo.
assert (HRHI : r + 288 <= spZ regs - 8320) by lia.
remember (adE regs bs M) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; unfold adE; apply Eimg_env).
assert (E2 : ew E 2 = getr regs 2)
by (rewrite HE; unfold adE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E1 : ew E 1 = getr regs 1)
by (rewrite HE; unfold adE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E12 : ew E 12 = Z_to_bv 64 k)
by (rewrite HE; unfold adE; rewrite Eimg_low by (unfold A_TEXT; lia);
    rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (Ea8 : ew E 8 = getr regs 8)
by (rewrite HE; unfold adE; rewrite Eimg_low by (unfold A_TEXT; lia);
    exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (Ea9 : ew E 9 = getr regs 9)
by (rewrite HE; unfold adE; rewrite Eimg_low by (unfold A_TEXT; lia);
    exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
assert (Ea18 : ew E 18 = getr regs 18)
by (rewrite HE; unfold adE; rewrite Eimg_low by (unfold A_TEXT; lia);
    exact (ew_Ereg_nat regs _ 18 18%bv eq_refl)).
assert (Ea19 : ew E 19 = getr regs 19)
by (rewrite HE; unfold adE; rewrite Eimg_low by (unfold A_TEXT; lia);
    exact (ew_Ereg_nat regs _ 19 19%bv eq_refl)).
assert (Ea20 : ew E 20 = getr regs 20)
by (rewrite HE; unfold adE; rewrite Eimg_low by (unfold A_TEXT; lia);
    exact (ew_Ereg_nat regs _ 20 20%bv eq_refl)).
assert (Ea21 : ew E 21 = getr regs 21)
by (rewrite HE; unfold adE; rewrite Eimg_low by (unfold A_TEXT; lia);
    exact (ew_Ereg_nat regs _ 21 21%bv eq_refl)).
assert (Ea22 : ew E 22 = getr regs 22)
by (rewrite HE; unfold adE; rewrite Eimg_low by (unfold A_TEXT; lia);
    exact (ew_Ereg_nat regs _ 22 22%bv eq_refl)).
assert (Ea23 : ew E 23 = getr regs 23)
by (rewrite HE; unfold adE; rewrite Eimg_low by (unfold A_TEXT; lia);
    exact (ew_Ereg_nat regs _ 23 23%bv eq_refl)).
assert (Ea24 : ew E 24 = getr regs 24)
by (rewrite HE; unfold adE; rewrite Eimg_low by (unfold A_TEXT; lia);
    exact (ew_Ereg_nat regs _ 24 24%bv eq_refl)).
assert (Ea25 : ew E 25 = getr regs 25)
by (rewrite HE; unfold adE; rewrite Eimg_low by (unfold A_TEXT; lia);
    exact (ew_Ereg_nat regs _ 25 25%bv eq_refl)).
assert (Ea26 : ew E 26 = getr regs 26)
by (rewrite HE; unfold adE; rewrite Eimg_low by (unfold A_TEXT; lia);
    exact (ew_Ereg_nat regs _ 26 26%bv eq_refl)).
assert (Ea27 : ew E 27 = getr regs 27)
by (rewrite HE; unfold adE; rewrite Eimg_low by (unfold A_TEXT; lia);
    exact (ew_Ereg_nat regs _ 27 27%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 ADSB) by (ad_atom HE 32%nat 0%nat).
assert (E33 : ew E 33 = Z_to_bv 64 (ad4 bs 280)) by (ad_atom HE 33%nat 1%nat).
assert (E3 : ew E 3 = getr regs 3)
by (rewrite HE; unfold adE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4)
by (rewrite HE; unfold adE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 r)
by (rewrite HE; unfold adE; rewrite Eimg_low by (unfold A_TEXT; lia);
    rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 p)
by (rewrite HE; unfold adE; rewrite Eimg_low by (unfold A_TEXT; lia);
    rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
pose proof HFO as HFOc.
destruct HFOc as ((cid & pos & Hfin & Hcid & Hfal & Hflo & Hfhi) & Hp8 & HRAp).
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfapp).
assert (HPLO : 4096 <= p) by lia.
assert (HPHI : p + 6 <= spZ regs - 8320) by lia.
assert (HAE : env_agree 32 (Ereg regs (adextra bs M)) E)
by (rewrite HE; unfold adE; split;
    [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
pose proof Hinv as HINV.
destruct Hinv as ((HLbs & HB1 & HB2 & HB3 & HB4 & HB5 & HB6) & HB7).
assert (Hn4 : ad4 bs 280 = Boxreg.bx_n bs).
{ pose proof (ad4_range bs 280). pose proof (ad_bx_n bs HLbs) as HBn. unfold Boxreg.boxreg_B1 in HB1.
  rewrite HBn in HB1 |- *. unfold bv_swrap, bv_wrap in *.
  change (bv_modulus 32) with (2 ^ 32) in *. change (bv_half_modulus 32) with (2 ^ 31) in *.
  Z.div_mod_to_equations. lia. }
assert (KEEP0 : forall a : Z, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 8320 <= a < spZ regs) ->
  aview SEGS (w_H W) mem a = aview SEGS (w_H W) mem a) by (intros; reflexivity).
unfold cfg_at, A_reac_boxreg_addP.
change (w64 (BASE + AF_reac_boxreg_add)) with (Z_to_bv 64 (BASE + AF_reac_boxreg_add)).
paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
ad_upd KEEP0 Usp W (spZ regs - 8320) (spZ regs).
psrr_branch_tok RUN BR HS SHOK ADspan.
- (* k is not an even width 2..40: the function returns -1 *)
  rewrite (ad_wtest E 12 k E12 Hk) in Hc. apply negb_true_iff in Hc.
  paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
  ad_upd KEEP0 Usp W (spZ regs - 8320) (spZ regs).
  ad_ret HS HJ E1 Hra HAE (-1) bs.
  split; [left; split; [left; intros (Hev & Hw2 & Hw3); rewrite (proj2 (Z.leb_le 2 k) ltac:(lia)) in Hc;
            rewrite (proj2 (Z.leb_le k 40) ltac:(lia)) in Hc; discriminate Hc | split; reflexivity]|].
  intros i Hi. change REG_SIZE with 288 in Hi. rewrite KEEP0 by lia. exact (Hbs i Hi).
- rewrite (ad_wtest E 12 k E12 Hk) in Hc. apply negb_false_iff in Hc.
  apply andb_prop in Hc as [Hk2 Hk40]. apply Z.leb_le in Hk2. apply Z.leb_le in Hk40.
  paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
  ad_upd KEEP0 Usp W (spZ regs - 8320) (spZ regs).
  psrr_branch_tok RUN BR HS SHOK ADspan.
  { (* k is odd: the function returns -1 *)
    rewrite (ad_odd E 12 k E12) in Hc. apply negb_true_iff in Hc.
    paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
    ad_upd KEEP0 Usp W (spZ regs - 8320) (spZ regs).
    ad_ret HS HJ E1 Hra HAE (-1) bs.
    split; [left; split; [left; intros (Hev & _); rewrite Hev in Hc; discriminate Hc | split; reflexivity]|].
    intros i Hi. change REG_SIZE with 288 in Hi. rewrite KEEP0 by lia. exact (Hbs i Hi). }
  { (* k is an even width in 2..40 *)
    rewrite (ad_odd E 12 k E12) in Hc. apply negb_false_iff in Hc. rename Hc into Hev.
    paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
    ad_upd KEEP0 Usp W (spZ regs - 8320) (spZ regs).
    assert (E34 : ew E 34 = Z_to_bv 64 (ad4 bs 284)) by (ad_atom HE 34%nat 2%nat).
    psrr_branch_tok RUN BR HS SHOK ADspan.
    { (* the fabric is narrower than k: the function returns -1 *)
      ad_at E34 34%nat E34a. ad_at E12 12%nat E12a.
      rewrite (ad_blt _ 34 (ad4 bs 284) 12 k E34a (ad4_range bs 284) E12a Hk) in Hc.
      apply Z.ltb_lt in Hc.
      paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
      ad_upd KEEP0 Usp W (spZ regs - 8320) (spZ regs).
      ad_ret HS HJ E1 Hra HAE (-1) bs.
      split; [left; split; [left; intros (_ & _ & Hw3); rewrite (ad_bx_fabric bs HLbs) in Hw3; lia
              | split; reflexivity]|].
      intros i Hi. change REG_SIZE with 288 in Hi. rewrite KEEP0 by lia. exact (Hbs i Hi). }
    { ad_at E34 34%nat E34a. ad_at E12 12%nat E12a.
      rewrite (ad_blt _ 34 (ad4 bs 284) 12 k E34a (ad4_range bs 284) E12a Hk) in Hc.
      apply Z.ltb_ge in Hc.
      paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
      ad_upd KEEP0 Usp W (spZ regs - 8320) (spZ regs).
      rename Hc into Hfab.
      assert (EM0 : ew E 70 = Z_to_bv 64 (adtb M 0)) by (ad_atom HE 70%nat 38%nat).
      assert (EM1 : ew E 71 = Z_to_bv 64 (adtb M 1)) by (ad_atom HE 71%nat 39%nat).
      assert (EM2 : ew E 72 = Z_to_bv 64 (adtb M 2)) by (ad_atom HE 72%nat 40%nat).
      assert (EM3 : ew E 73 = Z_to_bv 64 (adtb M 3)) by (ad_atom HE 73%nat 41%nat).
      assert (EM4 : ew E 74 = Z_to_bv 64 (adtb M 4)) by (ad_atom HE 74%nat 42%nat).
      assert (EM5 : ew E 75 = Z_to_bv 64 (adtb M 5)) by (ad_atom HE 75%nat 43%nat).
      (* The rest of the function, from the test of the MAC at 0x81c64 on: the six scan paths differ only in
         the byte that stopped them, and they all reach this state. *)
      assert (CONT : forall (E' : env) (ms' : machine_state) (md' : Model) (vv : Z),
        st_ok_pi SEGS VAL E' admz (restrict (w_H W) ms') ->
        sh_ok SEGS ADBx adSH E' (mrestrict (w_H W) (ms_mem ms')) ->
        img_env VAL A_LIM E' ->
        ajournal SEGS B REAC_BOXREG_ADD_STK (spZ regs) [(r, r + REG_SIZE)] ly S W mem md []
          ly S W (ms_mem ms') md' 0 ->
        (forall a : Z, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 8320 <= a < spZ regs) ->
           aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) mem a) ->
        env_agree 32 (Ereg regs (adextra bs M)) E' ->
        (forall n : nat, (n < 76)%nat -> ew E' n = ew E n) ->
        ew E' 76 = Z_to_bv 64 vv -> 0 <= vv < 256 -> (vv = 0 <-> M = Boxreg.zero6) ->
        SRr SEGS W (mkCfg ms' md') (treac_boxreg_add_post regs ly S W mem md r k bs M)).
      { clear HS SHOK HJ KEEP0.
        intros E' ms' md' vv HS SHOK HEIc HJ KEEP0 HAEc AG E76 Hvv HMZ.
        assert (E1' : ew E' 1 = getr regs 1) by (rewrite (AG 1%nat ltac:(lia)); exact E1).
        assert (E33' : ew E' 33 = Z_to_bv 64 (ad4 bs 280))
          by (rewrite (AG 33%nat ltac:(lia)); exact E33).
        assert (Ec8 : ew E' 8 = getr regs 8) by (rewrite (AG 8%nat ltac:(lia)); exact Ea8).
        assert (Ec9 : ew E' 9 = getr regs 9) by (rewrite (AG 9%nat ltac:(lia)); exact Ea9).
        assert (Ec18 : ew E' 18 = getr regs 18) by (rewrite (AG 18%nat ltac:(lia)); exact Ea18).
        assert (Ec19 : ew E' 19 = getr regs 19) by (rewrite (AG 19%nat ltac:(lia)); exact Ea19).
        assert (Ec20 : ew E' 20 = getr regs 20) by (rewrite (AG 20%nat ltac:(lia)); exact Ea20).
        assert (Ec21 : ew E' 21 = getr regs 21) by (rewrite (AG 21%nat ltac:(lia)); exact Ea21).
        assert (Ec22 : ew E' 22 = getr regs 22) by (rewrite (AG 22%nat ltac:(lia)); exact Ea22).
        assert (Ec23 : ew E' 23 = getr regs 23) by (rewrite (AG 23%nat ltac:(lia)); exact Ea23).
        assert (Ec24 : ew E' 24 = getr regs 24) by (rewrite (AG 24%nat ltac:(lia)); exact Ea24).
        assert (Ec25 : ew E' 25 = getr regs 25) by (rewrite (AG 25%nat ltac:(lia)); exact Ea25).
        assert (Ec26 : ew E' 26 = getr regs 26) by (rewrite (AG 26%nat ltac:(lia)); exact Ea26).
        assert (Ec27 : ew E' 27 = getr regs 27) by (rewrite (AG 27%nat ltac:(lia)); exact Ea27).
        assert (Ec3 : ew E' 3 = getr regs 3) by (rewrite (AG 3%nat ltac:(lia)); exact E3).
        assert (Ec4 : ew E' 4 = getr regs 4) by (rewrite (AG 4%nat ltac:(lia)); exact E4).
        assert (Ec10 : ew E' 10 = Z_to_bv 64 r) by (rewrite (AG 10%nat ltac:(lia)); exact E10).
        assert (Ec11 : ew E' 11 = Z_to_bv 64 p) by (rewrite (AG 11%nat ltac:(lia)); exact E11).
        assert (Ec12 : ew E' 12 = Z_to_bv 64 k) by (rewrite (AG 12%nat ltac:(lia)); exact E12).
        assert (Ec32 : ew E' 32 = Z_to_bv 64 ADSB) by (rewrite (AG 32%nat ltac:(lia)); exact E32).
        assert (HWOK : reac_boxreg_add_c.add_width_ok k (Boxreg.bx_fabric bs)).
        { unfold reac_boxreg_add_c.add_width_ok. split; [exact Hev|]. split; [lia|].
          rewrite (ad_bx_fabric bs HLbs). exact Hfab. }
        assert (Usp' : bv_unsigned (ew E' 2) = spZ regs) by (rewrite (AG 2%nat ltac:(lia)); exact Usp).
        psrr_branch_tok RUN BR HS SHOK ADspan.
        - (* the MAC is zero: the function returns -1 *)
          rewrite (ad_beq0 E' 76 vv E76 ltac:(lia)) in Hc. apply Z.eqb_eq in Hc.
          paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp' |].
          ad_upd KEEP0 Usp' W (spZ regs - 8320) (spZ regs).
          ad_ret HS HJ E1' Hra HAEc (-1) bs.
          split; [left; split; [right; exact (proj1 HMZ Hc) | split; reflexivity]|].
          intros i Hi. change REG_SIZE with 288 in Hi. rewrite KEEP0 by lia. exact (Hbs i Hi).
        - rewrite (ad_beq0 E' 76 vv E76 ltac:(lia)) in Hc. apply Z.eqb_neq in Hc.
          assert (HMnz : M <> Boxreg.zero6) by (intros Hz; apply Hc; exact (proj2 HMZ Hz)).
          clear Hc.
          paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp' |].
          ad_upd KEEP0 Usp' W (spZ regs - 8320) (spZ regs).
          prreg HS (1%bv : bv 5) Rra2. prreg HS (2%bv : bv 5) Rsp2. prreg HS (3%bv : bv 5) Rgp2.
          prreg HS (4%bv : bv 5) Rtp2. prreg HS (8%bv : bv 5) Rs0f. prreg HS (10%bv : bv 5) Ra0f.
          prreg HS (11%bv : bv 5) Ra1f.
          lazymatch goal with HSx : st_ok _ ?Ex _ _ |- _ =>
            assert (AG2 : forall n : nat, (n < 76)%nat -> ew Ex n = ew E' n)
            by (let nn := fresh "nn" in let Hnn := fresh "Hnn" in
                intros nn Hnn; rewrite ?ew_ewset_other by lia;
                rewrite ?ew_havoc_old by lia; reflexivity) end.
          lazymatch goal with HSx : st_ok _ _ _ (restrict (w_H W) ?msx) |- _ =>
            assert (HbsT : forall i, 0 <= i < REG_SIZE ->
                      aview SEGS (w_H W) (ms_mem msx) (r + i) = Some (adtb bs i))
              by (intros i Hi; change REG_SIZE with 288 in Hi; rewrite KEEP0 by lia; exact (Hbs i Hi));
            assert (HMvT : forall i, 0 <= i < 6 ->
                      aview SEGS (w_H W) (ms_mem msx) (p + i) = Some (adtb M i))
              by (intros i Hi; rewrite KEEP0 by lia; exact (HMv i Hi));
            assert (HFOT : afobj SEGS B ly S W (ms_mem msx) p 6)
              by (apply (ad_afobj_keep W ly S mem (ms_mem msx) p (spZ regs - 8320) (spZ regs) HFO KEEP0);
                  intros x Hx; unfold shadow_of_addr, SHADOW_OFF; split; lia)
          end.
          eapply SRr_bind.
          { eapply (aj_call SEGS B LAWS Hsegs W _ _ _ REAC_BOXREG_ADD_STK (spZ regs)
                      [(r, r + REG_SIZE)] ly S W mem md (@nil (Z * Z)) ly S _ 0
                      ReacBoxregFind.REAC_BOXREG_FIND_STK (@nil (Z * Z)) 0 (-80)).
            - exact HS.
            - vm_compute. reflexivity.
            - exact HJ.
            - rewrite Rsp2. cbn [sv_denot]. reflexivity.
            - reflexivity.
            - rewrite ?(AG2 2%nat ltac:(lia)). exact Usp'.
            - reflexivity.
            - lia.
            - unfold ReacBoxregFind.REAC_BOXREG_FIND_STK, ESTACK. lia.
            - unfold ReacBoxregFind.REAC_BOXREG_FIND_STK, ESTACK. rewrite WS. lia.
            - rewrite Rgp2. rewrite ?(AG2 3%nat ltac:(lia)). rewrite ?(AG 3%nat ltac:(lia)).
              rewrite E3. exact Hgp.
            - rewrite Rtp2. rewrite ?(AG2 4%nat ltac:(lia)). rewrite ?(AG 4%nat ltac:(lia)).
              rewrite E4. exact Htp.
            - reflexivity.
            - rewrite Rra2. apply ret_ok_codeptr_v; [lia | reflexivity].
            - rewrite Rra2, unsigned_lit_small by (pose proof pa_base_lo; pose proof pa_B_ok; lia).
              pose proof pa_base_lo. lia.
            - apply achain_low. unfold s0Z. rewrite Rs0f. rewrite ?(AG2 12%nat ltac:(lia)).
              rewrite ?(AG 12%nat ltac:(lia)). rewrite E12, unsigned_lit_small by lia. lia.
            - intros HPRE2.
              rewrite pa_sigma_reac_boxreg_find.
              lazymatch type of HPRE2 with
              | afn_pre _ _ _ _ _ _ ?rg ?mm ?mdd _ =>
                assert (Ha0 : getr rg 10 = w64 r)
                  by (rewrite Ra0f; rewrite ?(AG2 10%nat ltac:(lia));
                      rewrite ?(AG 10%nat ltac:(lia)); exact E10);
                assert (Ha1 : getr rg 11 = w64 p)
                  by (rewrite Ra1f; rewrite ?(AG2 11%nat ltac:(lia));
                      rewrite ?(AG 11%nat ltac:(lia)); exact E11);
                pose proof (FINDC ly S W rg mm mdd _ r p bs M HPRE2 Ha0 Ha1 Hin HLbs HbsT HB1 HFOT HML HMvT)
                  as HFIND
              end.
              unfold ReacBoxregFind.treac_boxreg_find_post, apost_base, cfg_at,
                     ReacBoxregFind.A_reac_boxreg_findP in HFIND.
              exact HFIND.
            - intros a Hfp. destruct (inFP_nil a Hfp). }
          cbv beta.
          intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJo & HJi & HP2 &
                          (-> & -> & -> & HPerm & Hbs2 & HMv2 & zz & Rz & Hfind)).
          lazymatch goal with HSx : st_ok _ ?Ex _ _ |- _ =>
            assert (URr : bv_unsigned (ew Ex 10) = r)
              by (rewrite ?(AG2 10%nat ltac:(lia)); rewrite ?(AG 10%nat ltac:(lia)); rewrite E10;
                  apply unsigned_lit_small; lia);
            assert (URp : bv_unsigned (ew Ex 11) = p)
              by (rewrite ?(AG2 11%nat ltac:(lia)); rewrite ?(AG 11%nat ltac:(lia)); rewrite E11;
                  apply unsigned_lit_small; lia);
            assert (URsp : bv_unsigned (ew Ex 2) = spZ regs)
              by (rewrite ?(AG2 2%nat ltac:(lia)); exact Usp') end.
          jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W) mem2) HP2 [0;1;2]%nat HS2.
          match type of HS2 with ?Q -> _ => assert (HRK : Q); [|specialize (HS2 HRK); clear HRK] end.
          { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
            - eapply (region_kept_block_sub SEGS B);
              [exact HJi | exact URr | exact Hin | exact Hin | lia
               | change (req_size REG_SIZE) with 288; lia | lia
               | intros a Ha Hfp; exact (inFP_nil _ Hfp)].
            - eapply (region_kept_frame_sub B);
              [exact HJi | exact URp | exact Hfin | lia | cbn [fs_frame_bytes]; lia
               | intros a Ha Hfp; exact (inFP_nil _ Hfp) | intros a Ha; lia].
            - eapply (region_kept_stack_sub SEGS B);
              [exact HJi | exact HJo | exact URsp | lia | rewrite WS; lia | lia | lia | lia]. }
          clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
          rewrite Rra2.
          assert (HFO2 : afobj SEGS B ly S W mem2 p 6) by (eapply ad_afobj_j; [exact HJi | exact HFOT]).
          assert (HAR2 : AR SEGS B ly S W mem2 md2) by (exact (proj1 HJo)).
          clear HbsT HMvT HFOT.
          lazymatch goal with HSx : st_ok_pi _ _ ?Ex _ _ |- _ =>
            assert (HEIn : img_env VAL A_LIM Ex)
              by (apply img_env_havoc_hi; [assumption | cbv; lia]);
            assert (Uspn : bv_unsigned (ew Ex 2) = spZ regs)
              by (rewrite ew_havoc_old by (cbv; lia); rewrite ?(AG2 2%nat ltac:(lia)); exact Usp') end.
          lazymatch goal with HSx : st_ok_pi _ _ ?Ex _ _ |- _ =>
            assert (SHOK2 : sh_ok SEGS ADBx adSH Ex (mrestrict (w_H W) mem2));
            [ apply (ad_shok Ex W ly S mem2 md2 r p HAR2 Hin HFO2);
              [ rewrite ew_havoc_old by (cbv; lia); rewrite ?(AG2 32%nat ltac:(lia));
                rewrite ?(AG 32%nat ltac:(lia)); exact E32
              | rewrite ew_havoc_old by (cbv; lia); rewrite ?(AG2 10%nat ltac:(lia));
                rewrite ?(AG 10%nat ltac:(lia)); exact E10
              | rewrite ew_havoc_old by (cbv; lia); rewrite ?(AG2 11%nat ltac:(lia));
                rewrite ?(AG 11%nat ltac:(lia)); exact E11
              | lia | lia | exact Hria | lia | lia
              | revert Hfapp Hflo Hfhi; clear; unfold in_app, kLowShadowBeg, kHighMemBeg; intros; lia ]
            | ] end.
          clear SHOK. rename SHOK2 into SHOK.
          assert (KEEPG : forall a : Z, alloc_ceiling <= a < 2 ^ 64 ->
            ~ (spZ regs - 8320 <= a < spZ regs) ->
            aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
          { intros a Ha Hw. pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & K1 & _).
            rewrite (K1 a ltac:(lia) ltac:(unfold ReacBoxregFind.REAC_BOXREG_FIND_STK, ESTACK; lia)).
            apply KEEP0; lia. }
          assert (KEEPB : forall a : Z, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 8320 <= a < spZ regs) ->
            aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem2 a) by (intros; reflexivity).
          clear KEEP0.
          prreg HS (10%bv : bv 5) Rz10.
          lazymatch goal with HSx : st_ok_pi _ _ ?Ex _ _ |- _ =>
            assert (Ez : ew Ex 516 = Z_to_bv 64 zz)
              by (cbn [ew havoc Nat.ltb Nat.sub]; rewrite <- Rz10; exact Rz) end.
          assert (Hzr : - 2 ^ 31 <= zz < 2 ^ 31).
          { destruct Hfind as [(_ & ->) | [(_ & Hfm & _) | (_ & -> & _)]]; [lia | | lia].
            unfold Boxreg.boxreg_B1 in HB1. lia. }
          paj_run_tok RUN HS HJo SHOK ADspan; [awr_ok_tac; exact Uspn |].
          ad_upd KEEPB Uspn W (spZ regs - 8320) (spZ regs).
          psrr_branch_tok RUN BR HS SHOK ADspan.
          { (* the MAC is already held by a row: return its index *)
            rewrite (ad_bge0 _ 516 zz Ez ltac:(lia)) in Hc.
            apply negb_true_iff, Z.ltb_ge in Hc.
            paj_run_tok RUN HS HJo SHOK ADspan; [awr_ok_tac; exact Uspn |].
            ad_upd KEEPB Uspn W (spZ regs - 8320) (spZ regs).
            assert (Hheld : reac_boxreg_add_c.add_held bs M zz).
            { destruct Hfind as [(Hz6 & _) | [(_ & Hfm) | (_ & Hm1 & _)]].
              - exfalso. exact (HMnz Hz6).
              - unfold reac_boxreg_add_c.add_held, reac_boxreg_find_c.first_mac in *. exact Hfm.
              - exfalso. lia. }
            lazymatch goal with HSx : st_ok_pi _ _ ?Ex _ _ |- _ =>
              assert (Ezn : ew Ex 516 = Z_to_bv 64 zz)
                by (cbn [ew ewset Nat.eqb]; exact Ez) end.
            prreg_raw HS (10%bv : bv 5) Rr10.
            ad_ret_t HS HJo E1' Hra HAEc zz bs.
            split; [rewrite Rr10; exact (ad_sextw0 _ 516 zz Ezn ltac:(lia))|].
            split; [right; left; split; [exact HWOK|]; split; [exact HMnz|];
                    split; [exact Hheld | reflexivity]|].
            intros i Hi. change REG_SIZE with 288 in Hi.
            rewrite KEEPB by lia. exact (Hbs2 i ltac:(change REG_SIZE with 288; lia)). }
          { (* the registry does not hold the MAC yet *)
            rewrite (ad_bge0 _ 516 zz Ez ltac:(lia)) in Hc.
            apply negb_false_iff, Z.ltb_lt in Hc.
            assert (Hnone : reac_boxreg_add_c.add_none_held bs M).
            { destruct Hfind as [(Hz6 & _) | [(_ & Hfm) | (_ & _ & Hnh)]].
              - exfalso. exact (HMnz Hz6).
              - exfalso. destruct Hfm as (Hb & _). lia.
              - exact Hnh. }
            rename Hc into Hzneg.
            paj_run_tok RUN HS HJo SHOK ADspan; [awr_ok_tac; exact Uspn |].
            ad_upd KEEPB Uspn W (spZ regs - 8320) (spZ regs).
            ad_at E33' 33%nat E33n.
            psrr_branch_tok RUN BR HS SHOK ADspan.
            { (* the registry is empty: go straight to the new row *)
              rewrite (ad_blez _ 33 (ad4 bs 280) E33n (ad4_range bs 280)) in Hc.
              rewrite <- (ad_bx_n bs HLbs) in Hc.
              apply negb_true_iff, Z.ltb_ge in Hc.
              paj_run_to_tok RUNTO HS HJo SHOK ADspan 7748; [awr_ok_tac; exact Uspn |].
              ad_upd KEEPB Uspn W (spZ regs - 8320) (spZ regs).
              (* the premises of the new-row lemma *)
              prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
              prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
              prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19.
              prreg HS (22%bv : bv 5) P22. prreg HS (25%bv : bv 5) P25.
              prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
              prreg_raw HS (23%bv : bv 5) P23. prreg_raw HS (24%bv : bv 5) P24.
              lazymatch goal with HSx : st_ok_pi _ _ ?Ex ?ssx (restrict (w_H W) ?msx) |- _ =>
                assert (R2 : getr (ms_regs msx) 2 = w64 (spZ regs - 80))
                  by (rewrite P2, (AG 2%nat ltac:(lia)), Usp; reflexivity);
                assert (R3 : getr (ms_regs msx) 3 = getr regs 3) by (rewrite P3; exact Ec3);
                assert (R4 : getr (ms_regs msx) 4 = getr regs 4) by (rewrite P4; exact Ec4);
                assert (R8 : getr (ms_regs msx) 8 = w64 k) by (rewrite P8; exact Ec12);
                assert (R9 : getr (ms_regs msx) 9 = w64 p) by (rewrite P9; exact Ec11);
                assert (R18 : getr (ms_regs msx) 18 = w64 r) by (rewrite P18; exact Ec10);
                assert (R19 : getr (ms_regs msx) 19 = w64 (r + 280))
                  by (rewrite P19, Ec10, unsigned_lit_small by (unfold M64; lia); reflexivity);
                assert (R22 : getr (ms_regs msx) 22 = w64 ADSB) by (rewrite P22; exact Ec32);
                assert (R23 : getr (ms_regs msx) 23 = w64 (ADSB + (r + 280) / 8))
                  by (rewrite P23; apply (ad_shaddr Ex 10 32 r ADSB);
                      [ad_ewat Ec10 | lia | lia | ad_ewat Ec32 | unfold ADSB; lia | unfold ADSB; lia]);
                assert (R24 : getr (ms_regs msx) 24 = w64 (Boxreg.bx_n bs))
                  by (rewrite P24, (ad_sext_val Ex 33 (ad4 bs 280) ltac:(ad_ewat E33')
                                      ltac:(unfold Boxreg.boxreg_B1 in HB1; lia)), Hn4; reflexivity);
                assert (R25 : getr (ms_regs msx) 25 = getr regs 25) by (rewrite P25; exact Ec25);
                assert (R26 : getr (ms_regs msx) 26 = getr regs 26) by (rewrite P26; exact Ec26);
                assert (R27 : getr (ms_regs msx) 27 = getr regs 27) by (rewrite P27; exact Ec27);
                assert (Uspc : bv_unsigned (ew Ex 2) = spZ regs)
                  by (cbn [ew ewset Nat.eqb]; rewrite ?ew_havoc_old by (cbv; lia);
                      rewrite (AG 2%nat ltac:(lia)); exact Usp);
                pose proof (ad_frames Ex ssx W msx regs HSx ltac:(vm_compute; right; right; left; reflexivity) Uspc
                  ltac:(ad_ewat E1') ltac:(ad_ewat Ec8) ltac:(ad_ewat Ec9) ltac:(ad_ewat Ec18)
                  ltac:(ad_ewat Ec19) ltac:(ad_ewat Ec20) ltac:(ad_ewat Ec21) ltac:(ad_ewat Ec22)
                  ltac:(ad_ewat Ec23) ltac:(ad_ewat Ec24)) as FRS;
                assert (HbsT : forall o, 0 <= o < REG_SIZE ->
                          aview SEGS (w_H W) (ms_mem msx) (r + o) = Some (adtb bs o))
                  by (intros o Ho; rewrite KEEPB by (change REG_SIZE with 288 in Ho; lia); exact (Hbs2 o Ho));
                assert (HMvT : forall o, 0 <= o < 6 ->
                          aview SEGS (w_H W) (ms_mem msx) (p + o) = Some (adtb M o))
                  by (intros o Ho; rewrite KEEPB by lia; exact (HMv2 o Ho));
                assert (HFOT : afobj SEGS B ly S W (ms_mem msx) p 6)
                  by (apply (ad_afobj_keep W ly S mem2 (ms_mem msx) p (spZ regs - 8320) (spZ regs) HFO2 KEEPB);
                      intros x Hx; unfold shadow_of_addr, SHADOW_OFF; split; lia)
              end.
              assert (Hunb : reac_boxreg_add_c.add_none_unbound bs k).
              { unfold reac_boxreg_add_c.add_none_unbound. intros i Hi. exfalso. lia. }
              lazymatch goal with
              | HSx : st_ok_pi _ _ ?Ex ?ssx (restrict (w_H W) ?msx) |- SRr _ _ (mkCfg _ ?mdx) _ =>
                rewrite (st_ok_pi_restrict_mkst (w_H W) Ex ssx msx HSx eq_refl);
                exact (ad_newrow ly S W regs mem md (ms_regs msx) (ms_mem msx) mdx r p k bs M HJo Hin
                         H10 H11 H12 Hra Hgp Htp R2 R3 R4 R8 R9 R18 R19 R22 R23 R24 R25 R26 R27 FRS
                         HbsT HMvT HFOT HML HINV ltac:(unfold Boxreg.boxreg_B1 in HB1; lia) Hk HWOK HMnz
                         Hnone Hunb)
              end. }
            { (* the registry holds rows: scan them *)
              rewrite (ad_blez _ 33 (ad4 bs 280) E33n (ad4_range bs 280)) in Hc.
              rewrite <- (ad_bx_n bs HLbs) in Hc.
              apply negb_false_iff, Z.ltb_lt in Hc.
              paj_run_to_tok RUNTO HS HJo SHOK ADspan 7512; [awr_ok_tac; exact Uspn |].
              ad_upd KEEPB Uspn W (spZ regs - 8320) (spZ regs).
              (* the premises of the loop lemma *)
              prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
              prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (12%bv : bv 5) P12.
              prreg HS (13%bv : bv 5) P13. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19.
              prreg HS (20%bv : bv 5) P20. prreg HS (22%bv : bv 5) P22. prreg HS (25%bv : bv 5) P25.
              prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
              prreg_raw HS (23%bv : bv 5) P23. prreg_raw HS (24%bv : bv 5) P24.
              lazymatch goal with HSx : st_ok_pi _ _ ?Ex ?ssx (restrict (w_H W) ?msx) |- _ =>
                assert (R2 : getr (ms_regs msx) 2 = w64 (spZ regs - 80))
                  by (rewrite P2, (AG 2%nat ltac:(lia)), Usp; reflexivity);
                assert (R3 : getr (ms_regs msx) 3 = getr regs 3) by (rewrite P3; exact Ec3);
                assert (R4 : getr (ms_regs msx) 4 = getr regs 4) by (rewrite P4; exact Ec4);
                assert (R8 : getr (ms_regs msx) 8 = w64 k) by (rewrite P8; exact Ec12);
                assert (R9 : getr (ms_regs msx) 9 = w64 p) by (rewrite P9; exact Ec11);
                assert (R12 : getr (ms_regs msx) 12 = w64 (r + 56 * 0))
                  by (rewrite P12, Ec10; unfold w64; f_equal; lia);
                assert (R13 : getr (ms_regs msx) 13 = w64 (r + 56 * 0))
                  by (rewrite P13, Ec10; unfold w64; f_equal; lia);
                assert (R18 : getr (ms_regs msx) 18 = w64 r) by (rewrite P18; exact Ec10);
                assert (R19 : getr (ms_regs msx) 19 = w64 (r + 280))
                  by (rewrite P19, Ec10, unsigned_lit_small by (unfold M64; lia); reflexivity);
                assert (R20 : getr (ms_regs msx) 20 = w64 0) by (rewrite P20; reflexivity);
                assert (R22 : getr (ms_regs msx) 22 = w64 ADSB) by (rewrite P22; exact Ec32);
                assert (R23 : getr (ms_regs msx) 23 = w64 (ADSB + (r + 280) / 8))
                  by (rewrite P23; apply (ad_shaddr Ex 10 32 r ADSB);
                      [ad_ewat Ec10 | lia | lia | ad_ewat Ec32 | unfold ADSB; lia | unfold ADSB; lia]);
                assert (R24 : getr (ms_regs msx) 24 = w64 (Boxreg.bx_n bs))
                  by (rewrite P24, (ad_sext_val Ex 33 (ad4 bs 280) ltac:(ad_ewat E33')
                                      ltac:(unfold Boxreg.boxreg_B1 in HB1; lia)), Hn4; reflexivity);
                assert (R25 : getr (ms_regs msx) 25 = getr regs 25) by (rewrite P25; exact Ec25);
                assert (R26 : getr (ms_regs msx) 26 = getr regs 26) by (rewrite P26; exact Ec26);
                assert (R27 : getr (ms_regs msx) 27 = getr regs 27) by (rewrite P27; exact Ec27);
                assert (Uspc : bv_unsigned (ew Ex 2) = spZ regs)
                  by (cbn [ew ewset Nat.eqb]; rewrite ?ew_havoc_old by (cbv; lia);
                      rewrite (AG 2%nat ltac:(lia)); exact Usp);
                pose proof (ad_frames Ex ssx W msx regs HSx ltac:(vm_compute; right; right; left; reflexivity) Uspc
                  ltac:(ad_ewat E1') ltac:(ad_ewat Ec8) ltac:(ad_ewat Ec9) ltac:(ad_ewat Ec18)
                  ltac:(ad_ewat Ec19) ltac:(ad_ewat Ec20) ltac:(ad_ewat Ec21) ltac:(ad_ewat Ec22)
                  ltac:(ad_ewat Ec23) ltac:(ad_ewat Ec24)) as FRS;
                assert (HbsT : forall o, 0 <= o < REG_SIZE ->
                          aview SEGS (w_H W) (ms_mem msx) (r + o) = Some (adtb bs o))
                  by (intros o Ho; rewrite KEEPB by (change REG_SIZE with 288 in Ho; lia); exact (Hbs2 o Ho));
                assert (HMvT : forall o, 0 <= o < 6 ->
                          aview SEGS (w_H W) (ms_mem msx) (p + o) = Some (adtb M o))
                  by (intros o Ho; rewrite KEEPB by lia; exact (HMv2 o Ho));
                assert (HFOT : afobj SEGS B ly S W (ms_mem msx) p 6)
                  by (apply (ad_afobj_keep W ly S mem2 (ms_mem msx) p (spZ regs - 8320) (spZ regs) HFO2 KEEPB);
                      intros x Hx; unfold shadow_of_addr, SHADOW_OFF; split; lia)
              end.
              lazymatch goal with
              | HSx : st_ok_pi _ _ ?Ex ?ssx (restrict (w_H W) ?msx) |- SRr _ _ (mkCfg _ ?mdx) _ =>
                rewrite (st_ok_pi_restrict_mkst (w_H W) Ex ssx msx HSx eq_refl);
                apply (ad_bindloop (Z.to_nat (Boxreg.bx_n bs)) ly S W regs mem md ch r p k bs M
                         (ms_regs msx) (ms_mem msx) mdx 0 HPRE H10 H11 H12 Hk Hin HINV HML HMnz HWOK Hnone
                         ltac:(lia) ltac:(lia) ltac:(intros j Hj; exfalso; lia)
                         R2 R3 R4 R8 R9 R12 R13 R18 R19 R20 R22 R23 R24 R25 R26 R27
                         ltac:(destruct FRS as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10);
                               unfold adfr; repeat split; assumption)
                         HbsT HFOT HMvT HJo)
              end.
              (* the new row, when no row is free for k *)
              intros regsT' memT' mdT' Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q22 Q23 Q24 Q25 Q26 Q27 QF QB QFO QM QJ QU QN.
              apply (ad_newrow ly S W regs mem md regsT' memT' mdT' r p k bs M QJ Hin H10 H11 H12 Hra Hgp Htp
                       Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q22 Q23 Q24 Q25 Q26 Q27
                       ltac:(destruct QF as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10);
                             unfold nxFR; repeat split; assumption)
                       QB QM QFO HML HINV QN Hk HWOK HMnz Hnone QU). } } }
      psrr_branch_tok RUN BR HS SHOK ADspan.
      { (* the MAC byte 0 is not zero *)
        ad_at EM0 70%nat EM0a.
        rewrite (ad_bnz _ 70 (adtb M 0) EM0a ltac:(pose proof (adtb_range M 0); lia)) in Hc.
        apply negb_true_iff, Z.eqb_neq in Hc.
        paj_run_to_tok RUNTO HS HJ SHOK ADspan 7448; [awr_ok_tac; exact Usp |].
        ad_upd KEEP0 Usp W (spZ regs - 8320) (spZ regs).
        ad_ag E AGx. ad_mz_leaf M EM0 70%nat (adtb M 0) HSm E76.
        change (st_ok SEGS ?e (abs_ss VAL admz) ?m) with (st_ok_pi SEGS VAL e admz m) in HSm.
        apply (CONT _ _ _ (adtb M 0) HSm
          ltac:(apply admz_shok; exact SHOK) ltac:(apply admz_img; assumption) HJ KEEP0
          ltac:(apply admz_agree32; eapply env_agree_trans;
                [exact HAE | split; [intros nn Hnn; rewrite ?ew_ewset_other by lia;
                                     rewrite ?ew_havoc_old by lia; reflexivity | reflexivity]])
          ltac:(intros nn Hnn; rewrite (admz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn)
          E76 ltac:(pose proof (adtb_range M 0); lia)
          ltac:(split; [intros Hz; exfalso; exact (Hc Hz)
                       | intros Hz; exact (proj1 (ad_M_zero M HML) Hz 0 ltac:(lia))])).
      }
      { (* the MAC byte 0 is zero *)
        rename Hc into Hz0.
        ad_at EM0 70%nat EM0a.
        rewrite (ad_bnz _ 70 (adtb M 0) EM0a ltac:(pose proof (adtb_range M 0); lia)) in Hz0.
        apply negb_false_iff, Z.eqb_eq in Hz0.
        paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
        ad_upd KEEP0 Usp W (spZ regs - 8320) (spZ regs).
      psrr_branch_tok RUN BR HS SHOK ADspan.
      { (* the MAC byte 1 is not zero *)
        ad_at EM1 71%nat EM1a.
        rewrite (ad_bnz _ 71 (adtb M 1) EM1a ltac:(pose proof (adtb_range M 1); lia)) in Hc.
        apply negb_true_iff, Z.eqb_neq in Hc.
        paj_run_to_tok RUNTO HS HJ SHOK ADspan 7448; [awr_ok_tac; exact Usp |].
        ad_upd KEEP0 Usp W (spZ regs - 8320) (spZ regs).
        ad_ag E AGx. ad_mz_leaf M EM1 71%nat (adtb M 1) HSm E76.
        change (st_ok SEGS ?e (abs_ss VAL admz) ?m) with (st_ok_pi SEGS VAL e admz m) in HSm.
        apply (CONT _ _ _ (adtb M 1) HSm
          ltac:(apply admz_shok; exact SHOK) ltac:(apply admz_img; assumption) HJ KEEP0
          ltac:(apply admz_agree32; eapply env_agree_trans;
                [exact HAE | split; [intros nn Hnn; rewrite ?ew_ewset_other by lia;
                                     rewrite ?ew_havoc_old by lia; reflexivity | reflexivity]])
          ltac:(intros nn Hnn; rewrite (admz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn)
          E76 ltac:(pose proof (adtb_range M 1); lia)
          ltac:(split; [intros Hz; exfalso; exact (Hc Hz)
                       | intros Hz; exact (proj1 (ad_M_zero M HML) Hz 1 ltac:(lia))])).
      }
      { (* the MAC byte 1 is zero *)
        rename Hc into Hz1.
        ad_at EM1 71%nat EM1a.
        rewrite (ad_bnz _ 71 (adtb M 1) EM1a ltac:(pose proof (adtb_range M 1); lia)) in Hz1.
        apply negb_false_iff, Z.eqb_eq in Hz1.
        paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
        ad_upd KEEP0 Usp W (spZ regs - 8320) (spZ regs).
      psrr_branch_tok RUN BR HS SHOK ADspan.
      { (* the MAC byte 2 is not zero *)
        ad_at EM2 72%nat EM2a.
        rewrite (ad_bnz _ 72 (adtb M 2) EM2a ltac:(pose proof (adtb_range M 2); lia)) in Hc.
        apply negb_true_iff, Z.eqb_neq in Hc.
        paj_run_to_tok RUNTO HS HJ SHOK ADspan 7448; [awr_ok_tac; exact Usp |].
        ad_upd KEEP0 Usp W (spZ regs - 8320) (spZ regs).
        ad_ag E AGx. ad_mz_leaf M EM2 72%nat (adtb M 2) HSm E76.
        change (st_ok SEGS ?e (abs_ss VAL admz) ?m) with (st_ok_pi SEGS VAL e admz m) in HSm.
        apply (CONT _ _ _ (adtb M 2) HSm
          ltac:(apply admz_shok; exact SHOK) ltac:(apply admz_img; assumption) HJ KEEP0
          ltac:(apply admz_agree32; eapply env_agree_trans;
                [exact HAE | split; [intros nn Hnn; rewrite ?ew_ewset_other by lia;
                                     rewrite ?ew_havoc_old by lia; reflexivity | reflexivity]])
          ltac:(intros nn Hnn; rewrite (admz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn)
          E76 ltac:(pose proof (adtb_range M 2); lia)
          ltac:(split; [intros Hz; exfalso; exact (Hc Hz)
                       | intros Hz; exact (proj1 (ad_M_zero M HML) Hz 2 ltac:(lia))])).
      }
      { (* the MAC byte 2 is zero *)
        rename Hc into Hz2.
        ad_at EM2 72%nat EM2a.
        rewrite (ad_bnz _ 72 (adtb M 2) EM2a ltac:(pose proof (adtb_range M 2); lia)) in Hz2.
        apply negb_false_iff, Z.eqb_eq in Hz2.
        paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
        ad_upd KEEP0 Usp W (spZ regs - 8320) (spZ regs).
      psrr_branch_tok RUN BR HS SHOK ADspan.
      { (* the MAC byte 3 is not zero *)
        ad_at EM3 73%nat EM3a.
        rewrite (ad_bnz _ 73 (adtb M 3) EM3a ltac:(pose proof (adtb_range M 3); lia)) in Hc.
        apply negb_true_iff, Z.eqb_neq in Hc.
        paj_run_to_tok RUNTO HS HJ SHOK ADspan 7448; [awr_ok_tac; exact Usp |].
        ad_upd KEEP0 Usp W (spZ regs - 8320) (spZ regs).
        ad_ag E AGx. ad_mz_leaf M EM3 73%nat (adtb M 3) HSm E76.
        change (st_ok SEGS ?e (abs_ss VAL admz) ?m) with (st_ok_pi SEGS VAL e admz m) in HSm.
        apply (CONT _ _ _ (adtb M 3) HSm
          ltac:(apply admz_shok; exact SHOK) ltac:(apply admz_img; assumption) HJ KEEP0
          ltac:(apply admz_agree32; eapply env_agree_trans;
                [exact HAE | split; [intros nn Hnn; rewrite ?ew_ewset_other by lia;
                                     rewrite ?ew_havoc_old by lia; reflexivity | reflexivity]])
          ltac:(intros nn Hnn; rewrite (admz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn)
          E76 ltac:(pose proof (adtb_range M 3); lia)
          ltac:(split; [intros Hz; exfalso; exact (Hc Hz)
                       | intros Hz; exact (proj1 (ad_M_zero M HML) Hz 3 ltac:(lia))])).
      }
      { (* the MAC byte 3 is zero *)
        rename Hc into Hz3.
        ad_at EM3 73%nat EM3a.
        rewrite (ad_bnz _ 73 (adtb M 3) EM3a ltac:(pose proof (adtb_range M 3); lia)) in Hz3.
        apply negb_false_iff, Z.eqb_eq in Hz3.
        paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
        ad_upd KEEP0 Usp W (spZ regs - 8320) (spZ regs).
      psrr_branch_tok RUN BR HS SHOK ADspan.
      { (* the MAC byte 4 is not zero *)
        ad_at EM4 74%nat EM4a.
        rewrite (ad_bnz _ 74 (adtb M 4) EM4a ltac:(pose proof (adtb_range M 4); lia)) in Hc.
        apply negb_true_iff, Z.eqb_neq in Hc.
        paj_run_to_tok RUNTO HS HJ SHOK ADspan 7448; [awr_ok_tac; exact Usp |].
        ad_upd KEEP0 Usp W (spZ regs - 8320) (spZ regs).
        ad_ag E AGx. ad_mz_leaf M EM4 74%nat (adtb M 4) HSm E76.
        change (st_ok SEGS ?e (abs_ss VAL admz) ?m) with (st_ok_pi SEGS VAL e admz m) in HSm.
        apply (CONT _ _ _ (adtb M 4) HSm
          ltac:(apply admz_shok; exact SHOK) ltac:(apply admz_img; assumption) HJ KEEP0
          ltac:(apply admz_agree32; eapply env_agree_trans;
                [exact HAE | split; [intros nn Hnn; rewrite ?ew_ewset_other by lia;
                                     rewrite ?ew_havoc_old by lia; reflexivity | reflexivity]])
          ltac:(intros nn Hnn; rewrite (admz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn)
          E76 ltac:(pose proof (adtb_range M 4); lia)
          ltac:(split; [intros Hz; exfalso; exact (Hc Hz)
                       | intros Hz; exact (proj1 (ad_M_zero M HML) Hz 4 ltac:(lia))])).
      }
      { (* the MAC byte 4 is zero *)
        rename Hc into Hz4.
        ad_at EM4 74%nat EM4a.
        rewrite (ad_bnz _ 74 (adtb M 4) EM4a ltac:(pose proof (adtb_range M 4); lia)) in Hz4.
        apply negb_false_iff, Z.eqb_eq in Hz4.
        paj_run_tok RUN HS HJ SHOK ADspan; [awr_ok_tac; exact Usp |].
        ad_upd KEEP0 Usp W (spZ regs - 8320) (spZ regs).
      psrr_branch_tok RUN BR HS SHOK ADspan.
      { (* the MAC byte 5 is not zero *)
        ad_at EM5 75%nat EM5a.
        rewrite (ad_bnz _ 75 (adtb M 5) EM5a ltac:(pose proof (adtb_range M 5); lia)) in Hc.
        apply negb_true_iff, Z.eqb_neq in Hc.
        paj_run_to_tok RUNTO HS HJ SHOK ADspan 7448; [awr_ok_tac; exact Usp |].
        ad_upd KEEP0 Usp W (spZ regs - 8320) (spZ regs).
        ad_ag E AGx. ad_mz_leaf M EM5 75%nat (adtb M 5) HSm E76.
        change (st_ok SEGS ?e (abs_ss VAL admz) ?m) with (st_ok_pi SEGS VAL e admz m) in HSm.
        apply (CONT _ _ _ (adtb M 5) HSm
          ltac:(apply admz_shok; exact SHOK) ltac:(apply admz_img; assumption) HJ KEEP0
          ltac:(apply admz_agree32; eapply env_agree_trans;
                [exact HAE | split; [intros nn Hnn; rewrite ?ew_ewset_other by lia;
                                     rewrite ?ew_havoc_old by lia; reflexivity | reflexivity]])
          ltac:(intros nn Hnn; rewrite (admz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn)
          E76 ltac:(pose proof (adtb_range M 5); lia)
          ltac:(split; [intros Hz; exfalso; exact (Hc Hz)
                       | intros Hz; exact (proj1 (ad_M_zero M HML) Hz 5 ltac:(lia))])).
      }
      { (* the MAC byte 5 is zero *)
        ad_at EM5 75%nat EMxa.
        rewrite (ad_bnz _ 75 (adtb M 5) EMxa ltac:(pose proof (adtb_range M 5); lia)) in Hc.
        apply negb_false_iff, Z.eqb_eq in Hc.
        paj_run_to_tok RUNTO HS HJ SHOK ADspan 7448; [awr_ok_tac; exact Usp |].
        ad_upd KEEP0 Usp W (spZ regs - 8320) (spZ regs).
        ad_ag E AGx. ad_mz_leaf M EM5 75%nat (adtb M 5) HSm E76.
        change (st_ok SEGS ?e (abs_ss VAL admz) ?m) with (st_ok_pi SEGS VAL e admz m) in HSm.
        apply (CONT _ _ _ (adtb M 5) HSm
          ltac:(apply admz_shok; exact SHOK) ltac:(apply admz_img; assumption) HJ KEEP0
          ltac:(apply admz_agree32; eapply env_agree_trans;
                [exact HAE | split; [intros nn Hnn; rewrite ?ew_ewset_other by lia;
                                     rewrite ?ew_havoc_old by lia; reflexivity | reflexivity]])
          ltac:(intros nn Hnn; rewrite (admz_other _ _ _ _ _ _ nn Hnn); apply AGx; exact Hnn)
          E76 ltac:(pose proof (adtb_range M 5); lia)
          ltac:(split;
                [intros _; apply (proj2 (ad_M_zero M HML)); intros j Hj;
                 destruct (Z.eq_dec j 0) as [Hj0|Hj0]; [rewrite Hj0; exact Hz0|];
                 destruct (Z.eq_dec j 1) as [Hj1|Hj1]; [rewrite Hj1; exact Hz1|];
                 destruct (Z.eq_dec j 2) as [Hj2|Hj2]; [rewrite Hj2; exact Hz2|];
                 destruct (Z.eq_dec j 3) as [Hj3|Hj3]; [rewrite Hj3; exact Hz3|];
                 destruct (Z.eq_dec j 4) as [Hj4|Hj4]; [rewrite Hj4; exact Hz4|];
                 assert (Hj5 : j = 5) by lia; rewrite Hj5; exact Hc
                | intros _; exact Hc])).
      }
      }
      }
      }
      }
      }
    } }
Qed.
End h.
End f.
End d.
