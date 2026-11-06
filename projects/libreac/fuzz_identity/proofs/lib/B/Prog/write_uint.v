(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACaa.v:43-46; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:140-143, 148-156, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* write_uint (fuzz_identity.asan-ubsan 0x84460, listing offset AF_write_uint = 0x3cec) on the ASan+UBSan build:
   it writes the decimal digits of v (the plain model, lib/Prog/write_uint_c.v) at o and returns their count.
   The build-B twin of lib/A/Prog/write_uint.v: the same statement over the build-B listing layer (IdentBSyms,
   IdentBList, IdentBPa, IdentBCJ).

   Callers. The only caller is reac_identity_reac_ver_str (0x842ec, 0x84354, 0x843d0), which has no side-stack
   frame and passes o inside the buffer it got from LLVMFuzzerTestOneInput: a buffer in the entry's side-stack
   frame or a heap block. twrite_uint_spec is in cgif's caller-journal form (lib/YC20.v:311-365; the shapes
   tcj_kept, twr_ok and tdst_ok are IdentBCJ.v's): the premise is the caller's journal, the right to write
   [o, o + n) is the caller's per-byte premise, the post extends the same journal. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YC5d YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaRun PaShadow PaJournal IdentBase YC81 YC4b.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBCJ IdentBFrame YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require write_uint_c write_uint.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import write_uint_post.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* ---- the model of the digits, and the machine's magic division ------------------------------- *)
(* How many digits v has, by range: the five cases the walk splits on. *)
Lemma wu_n_cases : forall v, 0 <= v < 65536 ->
  (write_uint_c.write_uint_n v = 1 /\ v < 10) \/ (write_uint_c.write_uint_n v = 2 /\ 10 <= v < 100) \/
  (write_uint_c.write_uint_n v = 3 /\ 100 <= v < 1000) \/ (write_uint_c.write_uint_n v = 4 /\ 1000 <= v < 10000) \/
  (write_uint_c.write_uint_n v = 5 /\ 10000 <= v).
Proof.
intros v Hv. unfold write_uint_c.write_uint_n, write_uint_c.write_uint_D. rewrite length_rev.
cbn [write_uint_c.write_uint_lsd].
destruct (Z.ltb_spec v 10) as [H1|H1]; cbn [length]; [left; split; [reflexivity | lia]|].
destruct (Z.ltb_spec (v / 10) 10) as [H2|H2]; cbn [length];
[right; left; split; [reflexivity|]; split; [lia | Z.div_mod_to_equations; lia]|].
destruct (Z.ltb_spec (v / 10 / 10) 10) as [H3|H3]; cbn [length];
[right; right; left; split; [reflexivity|]; split; Z.div_mod_to_equations; lia|].
destruct (Z.ltb_spec (v / 10 / 10 / 10) 10) as [H4|H4]; cbn [length];
[right; right; right; left; split; [reflexivity|]; split; Z.div_mod_to_equations; lia|].
right; right; right; right.
split; [destruct (v / 10 / 10 / 10 / 10 <? 10); reflexivity | Z.div_mod_to_equations; lia].
Qed.
Lemma wu_n_pos : forall v, 1 <= write_uint_c.write_uint_n v.
Proof.
intros v. unfold write_uint_c.write_uint_n, write_uint_c.write_uint_D. rewrite length_rev.
cbn [write_uint_c.write_uint_lsd length]. lia.
Qed.
(* The symbolic value the walk carries is wrapped in "+ 0" at each turn of loop 1. *)
Lemma U_add0 : forall E e, U E (SAlu ALU_ADD e (SLit 0)) = U E e.
Proof.
intros E e. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. unfold zcanon at 2. rewrite Zmod_0_l, Z.add_0_r.
apply zcanon_id. exact (U_range E e).
Qed.
(* x / 10 as the build computes it: mulhu (x << 48) 0xcccd0000, then >> 19. *)
Lemma wu_qU : forall E e x, U E e = x -> 0 <= x < 65536 ->
  U E (SAlu ALU_SRL (SMd M_MULHU (SAlu ALU_SLL e (SLit 48)) (SLit 3435986944)) (SLit 19)) = x / 10.
Proof.
intros E e x Hx Hr.
assert (HA : U E (SAlu ALU_SLL e (SLit 48)) = x * 2 ^ 48).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, Hx. change (zcanon 48) with 48.
  change (Z.land 48 63) with 48. rewrite Z.shiftl_mul_pow2 by lia. apply zcanon_id. unfold M64. lia. }
assert (HM : U E (SMd M_MULHU (SAlu ALU_SLL e (SLit 48)) (SLit 3435986944)) = x * 52429).
{ rewrite U_SMd. cbn [zmd_raw]. rewrite HA, U_SLit. change (zcanon 3435986944) with 3435986944.
  change (Z.of_N 64) with 64. rewrite Z.shiftr_div_pow2 by lia.
  replace (x * 2 ^ 48 * 3435986944) with (x * 52429 * 2 ^ 64) by lia.
  rewrite Z.div_mul by lia. apply zcanon_id. unfold M64. lia. }
rewrite U_SAlu. cbn [zalu_raw]. rewrite HM, U_SLit. change (zcanon 19) with 19. change (Z.land 19 63) with 19.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 19) with 524288.
rewrite zcanon_id by (unfold M64; Z.div_mod_to_equations; lia).
Z.div_mod_to_equations. lia.
Qed.
(* The digit byte the build stores: (x - 10 * (x / 10)) | 48. *)
Lemma wu_digU : forall E e q x, U E e = x -> U E q = x / 10 -> 0 <= x < 65536 ->
  U E (SAlu ALU_OR (SAlu ALU_SUB e (SMd M_MUL q (SLit 10))) (SLit 48)) = 48 + x mod 10.
Proof.
intros E e q x Hx Hq Hr.
assert (HM : U E (SMd M_MUL q (SLit 10)) = x / 10 * 10).
{ rewrite U_SMd. cbn [zmd_raw]. rewrite Hq, U_SLit. change (zcanon 10) with 10.
  apply zcanon_id. unfold M64. Z.div_mod_to_equations. lia. }
assert (HS : U E (SAlu ALU_SUB e (SMd M_MUL q (SLit 10))) = x mod 10).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite HM, Hx.
  replace (x - x / 10 * 10) with (x mod 10) by (Z.div_mod_to_equations; lia).
  apply zcanon_id. unfold M64. pose proof (Z.mod_pos_bound x 10 ltac:(lia)). lia. }
pose proof (Z.mod_pos_bound x 10 ltac:(lia)) as Hmb.
rewrite U_SAlu. cbn [zalu_raw]. rewrite HS, U_SLit. change (zcanon 48) with 48.
rewrite (write_uint.wu_lor48 (x mod 10) Hmb).
unfold zcanon, M64. apply Z.mod_small. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Definition A_write_uint : Z := BASE + AF_write_uint.
(* The stack the call needs, measured from the build-B listing: the 64-byte frame (0x84460 addi sp,sp,-64), the
   32-byte alignment of sp (0x84484 andi sp,sp,-32: up to 16 more bytes), and below the aligned sp the ESTACK
   window of the side-stack frame allocation it calls at 0x844b4 (class 0). The other sp writes (0x84688
   addi sp,s0,-64 and 0x846a4 addi sp,sp,64) restore sp; the fallback frame 0x844c8..0x844e0 is not reached. *)
Definition WRITE_UINT_STK : Z := 80 + ESTACK.
(* The digits of v (the plain model, lib/Prog/write_uint_c.v), as byte values. *)
Definition wu_bytes (v : Z) : list Z := map (fun b : byte => bv_unsigned b) (write_uint_c.write_uint_D v).
(* One digit byte as a value: 48 + d for a decimal digit d. *)
Lemma wu_dg_u : forall d, 0 <= d < 10 -> bv_unsigned (write_uint_c.write_uint_dg d) = 48 + d.
Proof.
  intros d Hd. unfold write_uint_c.write_uint_dg. rewrite Z_to_bv_unsigned.
  apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.
(* The i-th element of the least-significant-first list is the i-th decimal digit of v. *)
Lemma wu_lsd_nth : forall k v i, (i < length (write_uint_c.write_uint_lsd k v))%nat ->
  nth i (write_uint_c.write_uint_lsd k v) (write_uint_c.write_uint_dg 0)
  = write_uint_c.write_uint_dg ((v / 10 ^ Z.of_nat i) mod 10).
Proof.
  induction k as [|k IH]; intros v i Hi.
  - cbn [write_uint_c.write_uint_lsd length] in Hi. lia.
  - destruct (Z.ltb_spec v 10) as [Hv|Hv].
    + rewrite (write_uint.wu_lsd_lt10 k v Hv) in Hi |- *. cbn [length] in Hi.
      destruct i as [|i]; [|lia]. cbn [nth]. change (Z.of_nat 0) with 0.
      rewrite Z.pow_0_r, Z.div_1_r. reflexivity.
    + rewrite (write_uint.wu_lsd_ge10 k v Hv) in Hi |- *. cbn [length] in Hi.
      destruct i as [|i].
      * cbn [nth]. change (Z.of_nat 0) with 0. rewrite Z.pow_0_r, Z.div_1_r. reflexivity.
      * cbn [nth]. rewrite IH by lia.
        rewrite Z.div_div by first [lia | apply Z.pow_pos_nonneg; lia].
        rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. reflexivity.
Qed.
(* The j-th byte written is the (n-1-j)-th decimal digit of v, most significant first. *)
Lemma wu_bytes_nth : forall v j, (j < length (wu_bytes v))%nat ->
  nth j (wu_bytes v) 0 = 48 + (v / 10 ^ Z.of_nat (length (wu_bytes v) - 1 - j)) mod 10.
Proof.
  intros v j Hj. unfold wu_bytes, write_uint_c.write_uint_D in *.
  rewrite length_map, length_rev in *.
  rewrite nth_indep with (d' := bv_unsigned (write_uint_c.write_uint_dg 0))
    by (rewrite length_map, length_rev; exact Hj).
  rewrite (map_nth (fun b : byte => bv_unsigned b)). cbv beta.
  rewrite rev_nth by exact Hj.
  rewrite wu_lsd_nth by lia.
  replace (length (write_uint_c.write_uint_lsd 5 v) - S j)%nat
    with (length (write_uint_c.write_uint_lsd 5 v) - 1 - j)%nat by lia.
  apply wu_dg_u. apply Z.mod_pos_bound. lia.
Qed.
Lemma wu_bytes_len : forall v, Z.of_nat (length (wu_bytes v)) = write_uint_c.write_uint_n v.
Proof. intros v. unfold wu_bytes, write_uint_c.write_uint_n. rewrite length_map. reflexivity. Qed.
Lemma wu_bytes_rng : forall v j, (j < length (wu_bytes v))%nat -> 0 <= nth j (wu_bytes v) 0 < 256.
Proof.
  intros v j Hj. rewrite wu_bytes_nth by exact Hj.
  pose proof (Z.mod_pos_bound (v / 10 ^ Z.of_nat (length (wu_bytes v) - 1 - j)) 10 ltac:(lia)). lia.
Qed.
(* The 32-byte alignment of sp at 0x84484 (cgif lib/A/ACja.v land_m32 / denot_and_m32 / sp1_facts). *)
Lemma wu_land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = 32 * (x / 32).
Proof.
intros x Hx.
assert (E1 : 2 ^ 64 - 32 = Z.ldiff (Z.ones 64) (Z.ones 5)) by reflexivity. rewrite E1.
rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land.
rewrite Z.land_ones, Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. lia.
Qed.
Lemma wu_denot_and_m32 : forall E j w c, ew E j = Z_to_bv 64 w -> 0 <= w + c -> w + c < 2 ^ 64 -> 0 <= w < 2 ^ 64 ->
  sv_denot E (SAlu ALU_AND (SOff j c) (SLit (-32))) = Z_to_bv 64 (32 * ((w + c) / 32)).
Proof.
intros E j w c Hn H0 H1 Hw. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E j w c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite wu_land_m32 by lia. apply zcanon_id. unfold M64.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (w + c) 32 ltac:(lia)). lia.
Qed.
Lemma wu_sp1_facts : forall x, 0 <= x -> x mod 16 = 0 ->
  x - 16 <= 32 * (x / 32) <= x /\ (32 * (x / 32)) mod 32 = 0 /\ (32 * (x / 32)) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
split; [lia|]. split.
- apply (proj2 (Z.mod_divide (32 * (x / 32)) 32 ltac:(lia))). exists (x / 32). lia.
- apply (proj2 (Z.mod_divide (32 * (x / 32)) 16 ltac:(lia))). exists (2 * (x / 32)). lia.
Qed.

(* The side-stack frame allocation counts no event (cgif lib/YG00.v:569 stack_malloc has no tick) and
   write_uint allocates no heap block. *)
Definition EV_WRITE_UINT : Z := 0.
Section h.
Variable B : asyms.
(* ---- the contract, caller-journal form (the one callers take) --------------------------------- *)
Definition twrite_uint_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
(lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
(regs : bvmap 5 word) (o v : Z) : world SEGS -> config -> Prop :=
fun W2 c2 => W2 = W /\ exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_WRITE_UINT) /\
aregs_preserved regs regs2 /\
getr regs2 10 = w64 (write_uint_c.write_uint_n v) /\
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
garr8 SEGS (mrestrict (w_H W2) mem2) o (wu_bytes v) /\
tcj_kept B WRITE_UINT_STK lyc Sc W memc W2 mem2 (spZ regs) (fun a => o <= a < o + write_uint_c.write_uint_n v).
Definition twrite_uint_spec : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) ch (o v : Z),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
achain lyc (aview SEGS (w_H W) memc) (spZ regs) (s0Z regs) ch ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - WRITE_UINT_STK -> spZ regs <= sp0 ->
getr regs 10 = w64 o -> getr regs 11 = w64 v -> 0 <= v < 65536 ->
twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) o (write_uint_c.write_uint_n v) ->
tdst_ok B lyc Sc o (write_uint_c.write_uint_n v) ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF o (write_uint_c.write_uint_n v) ->
Z.of_nat (length (frames Sc)) <= 8 ->
SRr SEGS W (cfg_at SEGS A_write_uint regs memc mdc)
(twrite_uint_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs o v).
End h.
(* ---- the walk (CONVENTIONS.md section 5; cgif lib/A/AChf.v for the side-stack frame) ---------- *)
(* A contiguous range none of whose bytes has property P is disjoint from a range all of whose bytes
   have P: otherwise the larger of the two starts is in both. *)
Lemma wu_range_disj : forall (P : Z -> Prop) (q m x k : Z),
  (forall a, q <= a < q + m -> ~ P a) -> (forall a, x <= a < x + k -> P a) -> 0 < m -> 0 < k ->
  q + m <= x \/ x + k <= q.
Proof.
intros P q m x k Hq Hx Hm Hk.
destruct (Z_le_gt_dec (q + m) x) as [H1|H1]; [left; exact H1|].
destruct (Z_le_gt_dec (x + k) q) as [H2|H2]; [right; exact H2|].
exfalso. apply (Hq (Z.max q x) ltac:(lia)). apply Hx. lia.
Qed.
Section walk.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM0 : astack_malloc_realizes SEGS B 0.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_identb) (PI := PI).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
(* Where a byte of the destination lies: in a heap block or in a side-stack frame of the call state.
   Either way it is application memory below the ceiling, outside the image and outside the shadow band. *)
Lemma wu_dst_byte : forall lyc Sc W memc mdc q m a,
  AR SEGS B lyc Sc W memc mdc -> tdst_ok B lyc Sc q m -> q <= a < q + m ->
  4096 <= a < alloc_ceiling /\ ~ (IMG_LO <= a < IMG_TOP) /\
  ~ (SHADOW_OFF <= a < SHADOW_OFF + 17592186044416).
Proof.
intros lyc Sc W memc mdc q m a HAR HDST Ha.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (HDST a Ha) as [(b & w & Hin & Hb) | (cid & pos & Hin & Hr)].
- destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b w HAR Hin) as (_ & H4096 & Hceil & Hia & _).
  pose proof (blk_off_imgP _ _ _ _ _ _ b w HAR Hin) as Himg.
  pose proof (in_app_addr _ _ a Hia ltac:(lia)) as Hap.
  unfold app_addr, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in Hap |- *. split; [lia|]. split; lia.
- unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
  destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (H4096 & Hceil & Hia).
  pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR Hin) as Himg.
  pose proof (in_app_addr _ _ a Hia ltac:(lia)) as Hap.
  unfold app_addr, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in Hap |- *. split; [lia|]. split; lia.
Qed.
(* A byte of the destination is kept by a call that writes nothing (the frame allocation). *)
Lemma wu_out_kept : forall lyc Sc (W : world SEGS) memc mem2 slo shi q m a,
  acall_kept SEGS B lyc Sc W memc W mem2 slo shi (fun _ => False) ->
  tdst_ok B lyc Sc q m -> q <= a < q + m ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a.
Proof.
intros lyc Sc W memc mem2 slo shi q m a (K1 & K2 & K3 & K4 & K5 & K6) HDST Ha.
destruct (HDST a Ha) as [(b & w & Hin & Hb) | (cid & pos & Hin & Hr)].
- replace a with (b + (a - b)) by lia. apply (K2 b w (a - b) Hin ltac:(lia)). intros [].
- apply (K4 cid pos a Hin); [left; exact Hr | intros []].
Qed.
(* ... and it is present in any state the allocator invariant holds of. *)
Lemma wu_out_pres : forall lyc Sc (W : world SEGS) mem2 md2 q m a,
  AR SEGS B lyc Sc W mem2 md2 -> tdst_ok B lyc Sc q m -> q <= a < q + m ->
  apresent (w_H W) mem2 a.
Proof.
intros lyc Sc W mem2 md2 q m a HAR HDST Ha.
destruct (HDST a Ha) as [(b & w & Hin & Hb) | (cid & pos & Hin & Hr)].
- destruct (al_blocks _ _ LAWS lyc Sc W mem2 md2 b w HAR Hin) as (_ & _ & _ & _ & Hpres & _).
  replace a with (b + (a - b)) by lia. exact (proj1 (Hpres (b + (a - b)) ltac:(lia))).
- destruct (al_frames _ _ LAWS lyc Sc W mem2 md2 cid pos HAR Hin) as (_ & _ & Hpres & _).
  unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr. exact (proj1 (Hpres a ltac:(lia))).
Qed.
(* No byte of the destination is the allocator's own. *)
Lemma wu_out_notowned : forall lyc Sc (W : world SEGS) memc mdc q m a,
  AR SEGS B lyc Sc W memc mdc -> tdst_ok B lyc Sc q m -> q <= a < q + m -> ~ aowned B lyc Sc a.
Proof.
intros lyc Sc W memc mdc q m a HAR HDST Ha.
destruct (HDST a Ha) as [(b & w & Hin & Hb) | (cid & pos & Hin & Hr)].
- destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b w HAR Hin) as (_ & _ & _ & _ & Hpres & _).
  replace a with (b + (a - b)) by lia. exact (proj2 (Hpres (b + (a - b)) ltac:(lia))).
- destruct (al_frames _ _ LAWS lyc Sc W memc mdc cid pos HAR Hin) as (_ & _ & Hpres & _).
  unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr. exact (proj2 (Hpres a ltac:(lia))).
Qed.
(* The frame the call takes is fresh, so no byte of the destination lies in it. *)
Lemma wu_out_frame_disj : forall lyc Sc S2 (W : world SEGS) mem2 md2 q m cid pos,
  AR SEGS B lyc S2 W mem2 md2 -> tdst_ok B lyc Sc q m ->
  ablocks B lyc S2 = ablocks B lyc Sc -> frames S2 = (cid, pos) :: frames Sc ->
  0 < m -> 0 < fs_frame_bytes cid ->
  q + m <= frame_addr lyc cid pos \/ frame_addr lyc cid pos + fs_frame_bytes cid <= q.
Proof.
intros lyc Sc S2 W mem2 md2 q m cid pos HAR2 HDST Eab Hfrs2 Hm Hb.
apply (wu_range_disj (fun a => frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid)
  q m (frame_addr lyc cid pos) (fs_frame_bytes cid)); [| intros a Ha; exact Ha | exact Hm | exact Hb].
intros a Ha HF.
assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (HDST a Ha) as [(b & w & Hin & Hbb) | (cid' & pos' & Hin & Hr)].
- pose proof (sep_block_frame SEGS B LAWS lyc S2 W mem2 md2 b w cid pos HAR2
    ltac:(rewrite Eab; exact Hin) Hin2) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- apply in_split in Hin as (l1 & l2 & El).
  pose proof (sep_frames_pos SEGS B LAWS lyc S2 W mem2 md2 (cid, pos) (cid', pos') [] l1 l2 HAR2
    ltac:(rewrite Hfrs2, El; reflexivity)) as Hd.
  unfold zdisjoint, frame_rng, in_zr in Hd, Hr. cbn [fst snd] in Hd, Hr. lia.
Qed.
(* ---- the symbolic state at the first slot ----------------------------------------------------- *)
Definition Bx_WU : sv := SLit SB.
Definition Bspan_WU : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* The shadow-base cell holds SHADOW_OFF (AR_const_law), so the walk carries it as a literal. *)
Definition wu_cellR : YP09.region := YP09.mkRegion (Some (A_OBJ 31)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit SB))].
Definition wu_outR (m : Z) : YP09.region := YP09.mkRegion (Some 10%nat) 0 m 0 m [].
(* After the allocation: the frame (atom 516 = a0), its flag cell (528) and its shadow (529).
   The flag byte becomes writable only in the release run, so its window stays empty until then. *)
Definition wu_frameR : YP09.region :=
  YP09.mkRegion (Some 516%nat) 0 64 0 64 [YP09.mkChunk 56 (CVal 8 (SOff 528 0))].
Definition wu_fshR : YP09.region := YP09.mkRegion (Some 529%nat) 0 8 0 8 [].
Definition wu_flagR : YP09.region := YP09.mkRegion (Some 528%nat) 0 1 0 0 [].
Definition ss_wu (m : Z) : sstate :=
mkSS AF_write_uint sr_atoms
[stack_region 64; got_regionP; wu_cellR; uar_got_regionP 32; uar_cell_regionP 32; wu_outR m] None
(mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, PTR 0); (11%nat, mkAF 0 65535 0);
(32%nat, mkAF IMG_LO IMG_TOP 2)] [] []).
Definition wu_extra : list word := [Z_to_bv 64 (as_uar_cell B)].
Lemma wu_entry : forall lyc Sc (W : world SEGS) (regs : bvmap 5 word) memc mdc (o v m : Z),
  AR SEGS B lyc Sc W memc mdc ->
  (forall a, spZ regs - 80 <= a < spZ regs -> apresent (w_H W) memc a) ->
  spZ regs mod 16 = 0 -> alloc_ceiling + 80 <= spZ regs -> spZ regs <= 2 ^ 47 ->
  getr regs 10 = w64 o -> getr regs 11 = w64 v -> 0 <= v < 65536 ->
  4096 <= o -> o + m <= alloc_ceiling -> 0 < m ->
  (forall a, o <= a < o + m -> apresent (w_H W) memc a /\ ~ (IMG_LO <= a < IMG_TOP)) ->
  regions_wf (ss_mem (ss_wu m)) = true ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs wu_extra)) (ss_wu m)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_write_uint)) memc (seg_rom SEGS))).
Proof.
intros lyc Sc W regs memc mdc o v m HAR Hpres Hal16 Hlo Hhi H10 H11 Hv Ho4096 Hoceil Hm Hout Hwf.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBcell in Kcell. rewrite HBgot, HBcell in Kgot. rewrite (palf_got_uar B TLF) in Kguar.
pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Hual.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
destruct Hsep as ((Hs1 & Hs2 & Hs3 & _) & (Hs4 & Hs5 & _) & (Hs6 & _) & _).
pose proof (pa_obj_img 0%nat ltac:(lia)) as Hob0. pose proof (pa_obj_img 1%nat ltac:(lia)) as Hob1.
pose proof (pa_obj_img 31%nat ltac:(lia)) as Hob31.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := Eimg (Ereg regs wu_extra)).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs wu_extra) k)
  by (intros k Hk; subst E; apply Eimg_low; exact Hk).
assert (E2 : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 o)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 v)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 (as_uar_cell B))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs wu_extra 0)).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO31 : ew E (A_OBJ 31) = Z_to_bv 64 (VAL (A_OBJ 31)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (VB : forall k w, ew E k = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some k) = w)
  by (intros k w Hk Hw; cbn [base_val]; rewrite Hk; apply unsigned_lit_small; exact Hw).
assert (DJ : forall x k, IMG_LO <= x -> x + k <= IMG_TOP -> 0 < k -> o + m <= x \/ x + k <= o).
{ intros x k Hx1 Hx2 Hk. apply (wu_range_disj (fun a => IMG_LO <= a < IMG_TOP) o m x k);
  [intros a Ha; exact (proj2 (Hout a Ha)) | intros a Ha; lia | lia | lia]. }
pose proof (DJ (VAL (A_OBJ 0)) 8 (proj1 Hob0) (proj2 Hob0) ltac:(lia)) as D0.
pose proof (DJ (VAL (A_OBJ 1)) 8 (proj1 Hob1) (proj2 Hob1) ltac:(lia)) as D1.
pose proof (DJ (VAL (A_OBJ 31)) 8 (proj1 Hob31) (proj2 Hob31) ltac:(lia)) as D31.
pose proof (DJ (as_uar_cell B) 4 (proj1 Huar) ltac:(lia) ltac:(lia)) as DU.
rewrite restrict_mkst_fx. unfold ss_wu. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- unfold ss_wu in Hwf. cbn [ss_mem] in Hwf. exact Hwf.
- unfold stack_region, got_regionP, wu_cellR, uar_got_regionP, uar_cell_regionP, wu_outR.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem mkst].
  + cbn [base_val]. rewrite E2. split; [lia|]. split; [lia|]. split; [|constructor].
    intros ofs Hofs. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) EO1) by (pose proof (pa_val_range (A_OBJ 1)); lia).
    split; [lia|]. split; [lia|]. split; [intros ofs Hofs; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 31) 0) (VAL (A_OBJ 31)));
    [cbn [sv_denot]; rewrite EO31, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | pose proof (pa_val_range (A_OBJ 31)); zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
  + rewrite (VB (A_OBJ 31) (VAL (A_OBJ 31)) EO31) by (pose proof (pa_val_range (A_OBJ 31)); lia).
    split; [lia|]. split; [lia|]. split; [intros ofs Hofs; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 31)) 0 8 (SLit SB) SB);
    [cbn [sv_denot]; reflexivity | unfold SB; zside | zside |].
    rewrite Z.add_0_r, SB_SHADOW_OFF. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    split; [lia|]. split; [lia|]. split; [intros ofs Hofs; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff 32 0) (as_uar_cell B));
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kguar).
  + rewrite (VB 32%nat (as_uar_cell B) E32) by lia.
    split; [lia|]. split; [lia|]. split; [intros ofs Hofs; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1);
    [cbn [sv_denot]; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) memc _ _ Kuar).
  + rewrite (VB 10%nat o E10) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
    intros ofs Hofs. apply (apresent_writable SEGS). exact (proj1 (Hout (o + ofs) ltac:(lia))).
- apply pairwise_disjoint_of_extents.
  unfold stack_region, got_regionP, wu_cellR, uar_got_regionP, uar_cell_regionP, wu_outR, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB 10%nat o E10) by lia. rewrite (VB 32%nat (as_uar_cell B) E32) by lia.
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by (pose proof (pa_val_range (A_OBJ 0)); lia).
  rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) EO1) by (pose proof (pa_val_range (A_OBJ 1)); lia).
  rewrite (VB (A_OBJ 31) (VAL (A_OBJ 31)) EO31) by (pose proof (pa_val_range (A_OBJ 31)); lia).
  cbn [base_val]. rewrite E2.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
  rewrite E2, E10, E11, E32, !unsigned_lit_small by lia.
  change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat split; lia.
Qed.
(* The caller's right to write a byte of the destination, as every run of the walk needs it. *)
Ltac wu_awr_out d Usp E10 HWR :=
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat d);
  [reflexivity | cbn [ew]; rewrite Usp; lia | cbn; lia | cbn; lia |];
  eapply awr_ok_cons_ro; [cbn; lia|]; eapply awr_ok_cons_ro; [cbn; lia|];
  eapply awr_ok_cons_ro; [cbn; lia|]; eapply awr_ok_cons_ro; [cbn; lia|];
  eapply awr_ok_cons_gen;
  [reflexivity | cbn [ew]; rewrite E10; apply unsigned_lit_small; lia
  | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; exact (proj1 (HWR a ltac:(lia)))
  | apply awr_ok_nil].
(* The shadow address of a frame byte as the walk computes it (((a3 + c) >> 3) + SB, the base a literal) is
   byte c / 8 of the frame's shadow (atom s), the frame being 8-aligned. *)
Lemma wu_shadow_alias : forall E (p s : nat) (pv c : Z),
  ew E p = Z_to_bv 64 pv -> 0 <= pv < 2 ^ 47 -> pv mod 8 = 0 -> 0 <= c < 64 ->
  ew E s = Z_to_bv 64 (SB + pv / 8) ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff p c) (SLit 3)) (SLit SB)) = sv_denot E (SOff s (c / 8)).
Proof.
intros E p s pv c Hp Hpv H8 Hc Hs. apply U_inj.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_srl3, !U_SOff, U_SLit, Hp, Hs. clear Hp Hs.
assert (Hq : 0 <= pv / 8 < 2 ^ 44) by (Z.div_mod_to_equations; lia).
assert (E8 : (pv + c) / 8 = pv / 8 + c / 8) by (clear Hq; Z.div_mod_to_equations; lia).
rewrite (unsigned_lit_small pv) by lia.
rewrite (unsigned_lit_small (SB + pv / 8)) by (unfold SB; lia).
rewrite (zcanon_id (pv + c)) by (unfold M64; lia). rewrite (zcanon_id SB) by (unfold SB, M64; lia).
rewrite E8. f_equal. lia.
Qed.
Ltac wu_alias HS c E516 E529 HFb HF8 :=
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  let HSa := fresh "HSa" in
  pose proof (st_ok_pi_add_alias Ev ssv msv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 c) (SLit 3)) (SLit SB))
    (SOff 529 (c / 8)) HS (wu_shadow_alias Ev 516 529 _ c E516 HFb HF8 ltac:(clear; lia) E529)) as HSa;
  clear HS; rename HSa into HS end;
  lazymatch type of HS with st_ok_pi ?a1 ?a2 ?a3 ?ssv ?a4 =>
  let v := eval vm_compute in ssv in change (st_ok_pi a1 a2 a3 v a4) in HS end.
(* After the allocation the stack region keeps [sp0 - 48, sp0) (the saved registers) and the aligned sp's
   16 bytes [sp1, sp1 + 16) are a region of their own (atom 530): sp1 is sp0 - 64 or sp0 - 80. *)
Definition wu_trim (rs : smem) : smem :=
  map (fun r => match YP09.r_base r with Some 2%nat => trim_lo r (-48) | _ => r end) rs.
Definition wu_sp1R : YP09.region := YP09.mkRegion (Some 530%nat) 0 16 0 16 [].
Lemma wu_sp1_denot : forall E w, ew E 2 = Z_to_bv 64 w -> ew E 530 = Z_to_bv 64 (32 * ((w + -64) / 32)) ->
  64 <= w < 2 ^ 64 ->
  sv_denot E (SOff 530 0) = sv_denot E (SAlu ALU_AND (SOff 2 (-64)) (SLit (-32))) /\
  sv_denot E (SOff 530 0) = sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff 2 (-64)) (SLit (-32))) (SLit 0)).
Proof.
intros E w H2 H530 Hw.
assert (HA : sv_denot E (SAlu ALU_AND (SOff 2 (-64)) (SLit (-32))) = Z_to_bv 64 (32 * ((w + -64) / 32)))
  by (apply wu_denot_and_m32; [exact H2 | lia | lia | lia]).
assert (HO : sv_denot E (SOff 530 0) = Z_to_bv 64 (32 * ((w + -64) / 32)))
  by (cbn [sv_denot]; rewrite H530, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
split; [rewrite HO, HA; reflexivity|].
rewrite HO, <- HA. apply U_inj. rewrite U_add0. reflexivity.
Qed.
Ltac wu_norm HS := lazymatch type of HS with st_ok_pi ?a1 ?a2 ?a3 ?ssv ?a4 =>
  let v := eval vm_compute in ssv in change (st_ok_pi a1 a2 a3 v a4) in HS end.
Ltac wu_submem := lazymatch goal with
  | |- submem [] _ => apply submem_nil
  | |- submem (?r :: _) (?r :: _) => apply submem_keep; [apply subregion_refl | wu_submem]
  | |- submem (_ :: _) (_ :: _) =>
    apply submem_keep;
    [ unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
      split; [reflexivity|]; split; [clear; lia|]; split; [clear; lia|]; split; [right; clear; lia|];
      intros c Hc; cbn [In] in Hc |- *; clear - Hc; tauto
    | wu_submem ]
  end.
(* The caller's write right on a byte stays one when the call's frame joins its own frames. *)
Lemma wu_awr_own_cons : forall STK sp0 FP bl0 blc ly own x a,
  awr_byte STK sp0 FP bl0 blc ly own a -> awr_byte STK sp0 FP bl0 blc ly (x :: own) a.
Proof.
intros STK sp0 FP bl0 blc ly own x a [H | [H | [H | (cid & pos & Hin & Hr)]]];
[left; exact H | right; left; exact H | right; right; left; exact H |].
right; right; right. exists cid, pos. split; [right; exact Hin | exact Hr].
Qed.
(* The bytes the call may change: its stack window, the destination, the frame F it takes, F's shadow and
   F's flag cell. *)
Definition wu_D (sp STK q m F FL a : Z) : Prop :=
  (sp - STK <= a < sp) \/ (q <= a < q + m) \/ (F <= a < F + 64) \/
  (shadow_addr F <= a < shadow_addr F + 8) \/ a = FL.
(* One run keeps every byte outside D when each of its writable windows lies in D. *)
Lemma wu_kd_step : forall E rs (H : word -> bool) (m0 m1 m2 : word -> option byte) (D : Z -> Prop),
  frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> D a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ D a -> aview SEGS H m1 a = aview SEGS H m0 a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ D a -> aview SEGS H m2 a = aview SEGS H m0 a.
Proof.
intros E rs H m0 m1 m2 D HF HW K a Ha HD.
rewrite (kept_of_frame (segs := SEGS) E rs H m1 m2 D HF HW a Ha HD). exact (K a Ha HD).
Qed.
(* A frame byte's shadow byte lies in the frame's shadow. *)
Lemma wu_frame_shadow_in : forall F' L x, F' mod 8 = 0 -> L mod 8 = 0 -> 0 <= F' -> F' <= x < F' + L ->
  shadow_addr F' <= shadow_of_addr SHADOW_OFF x < shadow_addr F' + L / 8.
Proof. intros F' L x H1 H2 H3 H4. unfold shadow_addr, shadow_of_addr. Z.div_mod_to_equations. lia. Qed.
(* What the whole call kept (tcj_kept), from what the run before the allocation kept, what the allocation
   kept (acall_kept), what the runs after it kept (every byte outside D) and the separation of the frame F,
   its shadow and its flag cell FL from the blocks, the frames and the image of the call state. *)
Lemma wu_tcj_chain : forall (STK : Z) lyc Sc (W : world SEGS) memc mdc memT mem2 memF (sp q m F FL slo shi : Z),
  AR SEGS B lyc Sc W memc mdc ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - STK <= a < sp) -> ~ (q <= a < q + m) ->
     aview SEGS (w_H W) memT a = aview SEGS (w_H W) memc a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) memT a) ->
  acall_kept SEGS B lyc Sc W memT W mem2 slo shi (fun _ => False) -> sp - STK <= slo -> shi <= sp ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ wu_D sp STK q m F FL a ->
     aview SEGS (w_H W) memF a = aview SEGS (w_H W) mem2 a) ->
  (forall a, apresent (w_H W) mem2 a -> apresent (w_H W) memF a) ->
  (forall a, sp - STK <= a < sp -> apresent (w_H W) memF a) ->
  alloc_ceiling <= sp - STK -> tdst_ok B lyc Sc q m ->
  4096 <= F -> F + 64 <= alloc_ceiling -> FL < alloc_ceiling ->
  (forall b w i, In (b, w) (ablocks B lyc Sc) -> 0 <= i < req_size w ->
     ~ (F <= b + i < F + 64) /\ b + i <> FL) ->
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     ~ (F <= a < F + 64) /\ ~ (shadow_addr F <= a < shadow_addr F + 8) /\ a <> FL) ->
  (forall a, in_img SEGS a -> ~ (F <= a < F + 64) /\ ~ (shadow_addr F <= a < shadow_addr F + 8) /\ a <> FL) ->
  tcj_kept B STK lyc Sc W memc W memF sp (fun a => q <= a < q + m).
Proof.
intros STK lyc Sc W memc mdc memT mem2 memF sp q m F FL slo shi HAR KA PA (K1 & K2 & K3 & K4 & K5 & K6)
  Hslo Hshi KD PD HPw Hsp HD HF0 HFc HFL HBL HFR HIM.
pose proof asan_consts as (C1 & _).
assert (HSH : forall a, shadow_addr F <= a < shadow_addr F + 8 -> kLowMemEnd <= a < kHighMemBeg).
{ intros a Ha. assert (HFr0 : 0 <= F <= alloc_ceiling) by (clear - HF0 HFc; lia).
  pose proof (wu_shadow_rng F HFr0) as HS.
  unfold kLowMemEnd, kHighMemBeg in *. clear - Ha HS. lia. }
assert (HDI : forall a, q <= a < q + m -> ~ in_img SEGS a).
{ intros a Ha. destruct (HD a Ha) as [(b & w & Hin & Hr) | (cid & pos & Hin & Hr)].
  - exact (blk_img SEGS B LAWS lyc Sc W memc mdc b w a HAR Hin Hr).
  - unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
    exact (frm_img SEGS B LAWS lyc Sc W memc mdc cid pos a HAR Hin Hr). }
unfold tcj_kept. split.
{ intros a Ha Hw HE.
  assert (ND : ~ wu_D sp STK q m F FL a).
  { unfold wu_D. intros [H|[H|[H|[H|H]]]]; [exact (Hw H) | exact (HE H) | clear - H Ha HFc; lia | | clear - H Ha HFL; lia].
    pose proof (HSH a H) as Hz. unfold kHighMemBeg in Hz. clear - Ha Hz C1. lia. }
  rewrite (KD a ltac:(clear - Ha C1; lia) ND).
  rewrite (K1 a Ha ltac:(clear - Hw Hslo Hshi; lia)).
  exact (KA a ltac:(clear - Ha C1; lia) Hw HE). }
split.
{ intros b w i Hin Hi HE.
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b w HAR Hin) as (_ & Hb0 & Hbc & Hbapp & _).
  destruct (HBL b w i Hin Hi) as (HnF & HnFL).
  pose proof (in_app_addr b (req_size w) (b + i) Hbapp ltac:(clear - Hi; lia)) as Happ.
  assert (Hw : ~ (sp - STK <= b + i < sp)) by (clear - Hb0 Hbc Hi Hsp; lia).
  assert (ND : ~ wu_D sp STK q m F FL (b + i)).
  { unfold wu_D. intros [H|[H|[H|[H|H]]]]; [exact (Hw H) | exact (HE H) | exact (HnF H) | | exact (HnFL H)].
    pose proof (HSH _ H) as Hz. destruct Happ as (_ & [Hl | (Hh & _)]).
    - unfold kLowShadowBeg, kLowMemEnd in *. clear - Hz Hl. lia.
    - clear - Hz Hh. lia. }
  rewrite (KD (b + i) ltac:(clear - Hb0 Hbc Hi C1; lia) ND).
  rewrite (K2 b w i Hin Hi (fun x => x)).
  exact (KA (b + i) ltac:(clear - Hb0 Hbc Hi C1; lia) Hw HE). }
split.
{ intros a Him Hns Hne.
  destruct (HIM a Him) as (HnF & HnS & HnFL).
  pose proof (pa_segs_low a Him) as Hlo. unfold kLowMemEnd in Hlo.
  assert (Hw : ~ (sp - STK <= a < sp)) by (clear - Hlo Hsp C1; lia).
  assert (HE : ~ (q <= a < q + m)) by (intros Hq; exact (HDI a Hq Him)).
  assert (ND : ~ wu_D sp STK q m F FL a)
    by (unfold wu_D; intros [H|[H|[H|[H|H]]]]; [exact (Hw H) | exact (HE H) | exact (HnF H) | exact (HnS H) | exact (HnFL H)]).
  rewrite (KD a ltac:(clear - Hlo C1; lia) ND).
  rewrite (K3 a Him Hns Hne).
  exact (KA a ltac:(clear - Hlo C1; lia) Hw HE). }
split.
{ intros cid pos a Hin Hr HE.
  destruct (HFR cid pos a Hin Hr) as (HnF & HnS & HnFL).
  destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf0 & Hfc & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hnn.
  assert (Hz : 0 <= a < alloc_ceiling).
  { unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
    destruct Hr as [Hr | Hr]; [clear - Hr Hf0 Hfc; lia|].
    pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hnn) as Sh3.
    assert (Hq1 : 0 <= frame_addr lyc cid pos <= alloc_ceiling) by (clear - Hf0 Hfc Hnn; lia).
    assert (Hq2 : 0 <= frame_addr lyc cid pos + fs_frame_bytes cid <= alloc_ceiling) by (clear - Hf0 Hfc Hnn; lia).
    pose proof (wu_shadow_rng (frame_addr lyc cid pos) Hq1) as Sh1.
    pose proof (wu_shadow_rng (frame_addr lyc cid pos + fs_frame_bytes cid) Hq2) as Sh2.
    unfold kLowMemEnd in Sh1, Sh2. clear - Hr Sh1 Sh2 Sh3 C1.
    set (k8 := fs_frame_bytes cid / 8) in *. clearbody k8. lia. }
  assert (Hw : ~ (sp - STK <= a < sp)) by (clear - Hz Hsp; lia).
  assert (ND : ~ wu_D sp STK q m F FL a)
    by (unfold wu_D; intros [H|[H|[H|[H|H]]]]; [exact (Hw H) | exact (HE H) | exact (HnF H) | exact (HnS H) | exact (HnFL H)]).
  rewrite (KD a ltac:(clear - Hz C1; lia) ND).
  rewrite (K4 cid pos a Hin Hr (fun x => x)).
  exact (KA a ltac:(clear - Hz C1; lia) Hw HE). }
split.
{ intros a Ha Hw Hp. apply PD. apply K5; [exact Ha | clear - Hw Hslo Hshi; lia | exact (PA a Hp)]. }
exact HPw.
Qed.
(* The index of the region of base n. *)
Ltac wu_idx rs n := lazymatch rs with
  | YP09.mkRegion (Some n) _ _ _ _ _ :: _ => constr:(0%nat)
  | _ :: ?tl => let i := wu_idx tl n in constr:(S i)
  end.
(* Set the writable window of the region of base n to [wlo, whi); tac proves the window writable. *)
Ltac wu_setwin HS n wlo whi tac :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let i := wu_idx rs n in let i := eval vm_compute in i in
  let r := eval vm_compute in (nth i rs got_regionP) in
  let HS3 := fresh "HS3" in
  pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r wlo whi) HS ltac:(vm_compute; reflexivity) eq_refl
    ltac:(vm_compute; reflexivity)
    (region_ok_rewindow _ Ex _ r wlo whi (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
      ltac:(tac))) as HS3;
  clear HS; rename HS3 into HS; wu_norm HS end.
(* A branch the plain runner stops at. *)
Ltac wu_br RUNP BR HS :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
  lazymatch type of RUNP with
  | forall W n E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q, _ -> _ -> sym_runN_pi ?tpi n ss = _ -> _ =>
    let r := eval vm_compute in (snd (sym_runN_pi tpi 1%N ss)) in
    lazymatch r with
    | PRS_stopped (SR_branch ?c ?a ?b) =>
      apply (BR W E ss ms _ _ c a b HS); clear HS; let Hc := fresh "Hc" in intros Hc HS
    | _ => fail "wu_br: not at a branch" r
    end end end.
(* The write right of each writable window after the allocation (the caller's journal, own = (0, fpos) :: own):
   [sp1, sp1 + 16) and [sp0 - 48, sp0) are the caller's stack window, the frame and its shadow are the call's own
   frame, the destination is the caller's premise. *)
Ltac wu_awr_rec U530 U529 U516 Usp2 Uo2 Hsp1r Hlo WS Hhi Eab HWR fpos :=
  lazymatch goal with
  | |- awr_ok _ [] _ _ _ _ _ _ _ => apply awr_ok_nil
  | |- awr_ok _ (YP09.mkRegion ?bs _ _ ?wlo ?whi _ :: _) _ ?sp0 _ _ _ _ _ =>
    first
    [ lazymatch (eval vm_compute in (Z.leb whi wlo)) with true => apply awr_ok_cons_ro; [cbn; clear; lia|] end
    | lazymatch bs with
      | Some 530%nat =>
        lazymatch type of U530 with _ = ?sp1 =>
        eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 530%nat (sp1 - sp0));
        [reflexivity | rewrite U530; clear; lia | cbn; clear - Hsp1r Hlo WS; lia | cbn; clear - Hsp1r Hhi; lia |] end
      | Some 2%nat =>
        lazymatch type of Usp2 with _ = ?spr =>
        eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spr - sp0));
        [reflexivity | rewrite Usp2; clear; lia | cbn; clear - Hlo WS; lia | cbn; clear - Hhi; lia |] end
      | Some 529%nat =>
        eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 529%nat); [reflexivity | exact U529 | | ];
        [ cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          right; right; right; exists 0, fpos; split; [left; reflexivity|];
          right; unfold in_zr, shadow_addr; cbn [fst snd]; change (fs_frame_bytes 0 / 8) with 8;
          unfold SB, SHADOW_OFF in *; clear - Ha; lia | ]
      | Some 516%nat =>
        eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 516%nat); [reflexivity | exact U516 | | ];
        [ cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          right; right; right; exists 0, fpos; split; [left; reflexivity|];
          left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 0) with 64; clear - Ha; lia | ]
      | Some 10%nat =>
        eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat); [reflexivity | exact Uo2 | | ];
        [ cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          apply wu_awr_own_cons; rewrite Eab;
          exact (proj1 (HWR a ltac:(clear - Ha; lia))) | ]
      end ];
    wu_awr_rec U530 U529 U516 Usp2 Uo2 Hsp1r Hlo WS Hhi Eab HWR fpos
  end.
Ltac wu_awr U530 U529 U516 Usp2 Uo2 Hsp1r Hlo WS Hhi Eab HWR fpos :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  wu_awr_rec U530 U529 U516 Usp2 Uo2 Hsp1r Hlo WS Hhi Eab HWR fpos.
(* Each writable window of a run after the allocation lies in D (wu_D). *)
Ltac wu_win U530 U529 U528 U516 Usp2 Uo2 Hsp1r :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
  let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros b wlo whi a Hin Ha;
  lazymatch type of Hin with In _ (windows ?rs) =>
    let w := eval vm_compute in (windows rs) in change (In (b, wlo, whi) w) in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin];
    [ inversion Hin; subst; cbn [base_val] in Ha;
      first [ rewrite U530 in Ha | rewrite U529 in Ha | rewrite U528 in Ha | rewrite U516 in Ha
            | rewrite Usp2 in Ha | rewrite Uo2 in Ha | idtac ];
      unfold wu_D;
      first [ exfalso; clear - Ha; lia
            | left; clear - Ha Hsp1r; lia
            | right; left; clear - Ha; lia
            | right; right; left; clear - Ha; lia
            | right; right; right; left; unfold shadow_addr, SB, SHADOW_OFF in *; clear - Ha; lia
            | right; right; right; right; clear - Ha; lia ]
    | ]);
  destruct Hin.
(* After a run: carry "outside D nothing changed since the allocation" (KD) and "what was present stays"
   (PD) to the run's final memory, and drop the run's frame facts. *)
Ltac wu_kd U530 U529 U528 U516 Usp2 Uo2 Hsp1r :=
  repeat match goal with
  | Hf : frame_of _ _ _ _ |- _ => progress cbn [ms_mem mkst] in Hf
  | Hg : mem_grows _ _ |- _ => progress cbn [ms_mem mkst] in Hg
  end;
  lazymatch goal with
  | KD : forall a, 0 <= a < 2 ^ 64 -> ~ wu_D ?s1 ?s2 ?s3 ?s4 ?s5 ?s6 a -> aview _ ?Hh ?m1 a = aview _ _ ?m0 a,
    Hf : frame_of ?Ef ?rsf (mrestrict ?Hh ?m1) (mrestrict ?Hh ?m2) |- _ =>
    let KD' := fresh "KD" in
    pose proof (wu_kd_step Ef rsf Hh m0 m1 m2 (wu_D s1 s2 s3 s4 s5 s6) Hf
      ltac:(wu_win U530 U529 U528 U516 Usp2 Uo2 Hsp1r) KD) as KD';
    clear KD Hf; rename KD' into KD
  end;
  lazymatch goal with
  | PD : forall a, apresent ?Hh ?m0 a -> apresent ?Hh ?m1 a, Hg : mem_grows (mrestrict ?Hh ?m1) (mrestrict ?Hh ?m2) |- _ =>
    let PD' := fresh "PD" in
    pose proof (fun a (Hp : apresent Hh m0 a) => apresent_grows Hh m1 m2 a Hg (PD a Hp)) as PD';
    clear PD Hg; rename PD' into PD
  end;
  repeat match goal with Hf : frame_of _ _ _ _ |- _ => clear Hf end.
(* ~o as the walk computes it (xor with all ones, the literal in either form). *)
Lemma wu_xorU : forall E n x c, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> zcanon c = 2 ^ 64 - 1 ->
  U E (SAlu ALU_XOR (SOff n 0) (SLit c)) = 2 ^ 64 - 1 - x.
Proof.
intros E n x c Hn Hx Hc. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n x Hn Hx), U_SLit, Hc.
rewrite OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable.YI08.lxor_allones by lia.
apply zcanon_id. unfold M64. lia.
Qed.
(* The release run may also write the flag byte FL (aj_flag_store_pi's write premise): the region right after
   the first one is the flag cell, the others have the caller's write right. *)
Lemma wu_awr_flag : forall E r1 r rs STK sp0 FP bl0 blc ly own FL,
  awr_ok E (r1 :: rs) STK sp0 FP bl0 blc ly own ->
  (forall a, base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r -> a = FL) ->
  forall a, in_wrange E (r1 :: r :: rs) a -> awr_byte STK sp0 FP bl0 blc ly own a \/ a = FL.
Proof.
intros E r1 r rs STK sp0 FP bl0 blc ly own FL H Hf a (r' & [<- | [<- | Hin]] & Ha).
- left. apply H. exists r1. split; [left; reflexivity | exact Ha].
- right. apply Hf. exact Ha.
- left. apply H. exists r'. split; [right; exact Hin | exact Ha].
Qed.
(* After a tok run the environment has new token atoms above every atom of the state: carry a fact about an
   atom below them to the new environment (the one of HS). *)
Ltac wu_re1 H :=
  lazymatch goal with HS0 : st_ok_pi _ _ ?Enew _ _ |- _ =>
  lazymatch type of H with
  | bv_unsigned (ew Enew _) = _ => idtac
  | bv_unsigned (ew _ ?n) = ?v =>
    let H' := fresh "Hre" in
    assert (H' : bv_unsigned (ew Enew n) = v) by (rewrite ?ew_ewset_other by (clear; lia); exact H);
    clear H; rename H' into H
  | ew Enew _ = _ => idtac
  | ew _ ?n = ?v =>
    let H' := fresh "Hre" in
    assert (H' : ew Enew n = v) by (rewrite ?ew_ewset_other by (clear; lia); exact H);
    clear H; rename H' into H
  end end.
Ltac wu_reU U530 U529 U528 U516 Usp2 Uo2 E10v E11v E516 E528 E529 E530 :=
  wu_re1 U530; wu_re1 U529; wu_re1 U528; wu_re1 U516; wu_re1 Usp2; wu_re1 Uo2; wu_re1 E10v; wu_re1 E11v;
  wu_re1 E516; wu_re1 E528; wu_re1 E529; wu_re1 E530.
(* The value loop 1 carries in s3 after i turns (x_i = v / 10^i), as the engine writes it, and the digit byte it
   stores at turn i. *)
Fixpoint wu_se (i : nat) : sv :=
  match i with
  | O => SOff 11 0
  | S i' => SAlu ALU_ADD (SAlu ALU_SRL (SMd M_MULHU (SAlu ALU_SLL (wu_se i') (SLit 48)) (SLit 3435986944))
              (SLit 19)) (SLit 0)
  end.
Definition wu_dig (e : sv) : sv :=
  SAlu ALU_OR (SAlu ALU_SUB e (SMd M_MUL (SAlu ALU_SRL (SMd M_MULHU (SAlu ALU_SLL e (SLit 48)) (SLit 3435986944))
    (SLit 19)) (SLit 10))) (SLit 48).
Lemma wu_x_rng : forall v i, 0 <= v < 65536 -> 0 <= v / 10 ^ Z.of_nat i < 65536.
Proof.
intros v i Hv. pose proof (Z.pow_pos_nonneg 10 (Z.of_nat i) ltac:(lia) ltac:(lia)) as Hp.
split; [apply Z.div_pos; lia|]. apply (Z.le_lt_trans _ v); [|lia].
apply Z.div_le_upper_bound; [lia|]. apply Z.le_trans with (1 * v); [lia|]. apply Z.mul_le_mono_nonneg_r; lia.
Qed.
Lemma wu_seU : forall E v, ew E 11 = Z_to_bv 64 v -> 0 <= v < 65536 ->
  forall i, U E (wu_se i) = v / 10 ^ Z.of_nat i.
Proof.
intros E v H11 Hv. induction i as [|i IH]; cbn [wu_se].
- change (10 ^ Z.of_nat 0) with 1. rewrite Z.div_1_r. apply U_atom; [exact H11 | lia].
- rewrite U_add0, (wu_qU E (wu_se i) _ IH (wu_x_rng v i Hv)).
  rewrite Z.div_div by first [lia | apply Z.pow_pos_nonneg; lia].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. f_equal. ring.
Qed.
Lemma wu_digseU : forall E v i, ew E 11 = Z_to_bv 64 v -> 0 <= v < 65536 ->
  U E (wu_dig (wu_se i)) = 48 + (v / 10 ^ Z.of_nat i) mod 10.
Proof.
intros E v i H11 Hv. unfold wu_dig.
apply wu_digU; [apply wu_seU; assumption | apply wu_qU; [apply wu_seU; assumption | apply wu_x_rng; exact Hv]
  | apply wu_x_rng; exact Hv].
Qed.
(* (x << 48) >> 48 = x for x < 2^16: loop 1's continue test reads x that way. *)
Lemma wu_lo16U : forall E e x, U E e = x -> 0 <= x < 65536 ->
  U E (SAlu ALU_SRL (SAlu ALU_SLL e (SLit 48)) (SLit 48)) = x.
Proof.
intros E e x Hx Hr.
assert (HA : U E (SAlu ALU_SLL e (SLit 48)) = x * 2 ^ 48).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, Hx. change (zcanon 48) with 48.
  change (Z.land 48 63) with 48. rewrite Z.shiftl_mul_pow2 by lia. apply zcanon_id. unfold M64. lia. }
rewrite U_SAlu. cbn [zalu_raw]. rewrite HA, U_SLit. change (zcanon 48) with 48. change (Z.land 48 63) with 48.
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. apply zcanon_id. unfold M64. lia.
Qed.
Definition wu_t3 (i : nat) : sv := SAlu ALU_SRL (SAlu ALU_SLL (wu_se i) (SLit 48)) (SLit 48).
Lemma wu_t3U : forall E v i, ew E 11 = Z_to_bv 64 v -> 0 <= v < 65536 -> U E (wu_t3 i) = v / 10 ^ Z.of_nat i.
Proof. intros E v i H11 Hv. unfold wu_t3. apply wu_lo16U; [apply wu_seU; assumption | apply wu_x_rng; exact Hv]. Qed.
(* Byte j of the destination after loop 2: the digit of turn k of loop 1, zero-extended by the tmp load. *)
Lemma wu_out_byte : forall E (m : word -> option byte) (r : YP09.region) (b v : Z) (j k : nat),
  region_ok SEGS E m r -> YP09.r_base r = Some 10%nat -> bv_unsigned (ew E 10) = b ->
  In (YP09.mkChunk (Z.of_nat j) (CVal 1 (SExt false 8 (wu_dig (wu_se k))))) (YP09.r_chunks r) ->
  ew E 11 = Z_to_bv 64 v -> 0 <= v < 65536 ->
  val_mem SEGS m (b + Z.of_nat j) 1 (48 + (v / 10 ^ Z.of_nat k) mod 10).
Proof.
intros E m r b v j k HR Hb Hbase Hin H11 Hv.
pose proof (Z.mod_pos_bound (v / 10 ^ Z.of_nat k) 10 ltac:(lia)) as Hm.
apply (wu_val_of_chunk1 E m r 10%nat b (Z.of_nat j) _ _ HR Hb Hbase Hin); [| lia].
rewrite denot_lit_U. f_equal. rewrite U_SExt. cbn iota. rewrite (wu_digseU E v k H11 Hv).
change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia. apply zcanon_id. unfold M64. lia.
Qed.
Ltac wu_getn := lazymatch goal with Hn : write_uint_c.write_uint_n _ = ?n |- _ => n end.
Ltac wu_clrc := repeat match goal with Hc : branch_taken _ _ _ = _ |- _ => clear Hc end.
(* Add region r to HS: tok proves it is backed, tdj that it is apart from the others. *)
Ltac wu_addreg HS r tok tdj :=
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  let HSa := fresh "HSa" in
  pose proof (st_ok_pi_add_region Ev ssv msv r HS ltac:(vm_compute; reflexivity) ltac:(tok) ltac:(tdj)) as HSa;
  clear HS; rename HSa into HS; wu_norm HS end.
(* The wrong side of loop 1's continue test 0x845a0 bltu 9, x_i, from the case's range of v. *)
Ltac wu_ref9 E11v Hv Hvr :=
  lazymatch goal with Hc : branch_taken BC_LTU (sv_denot ?E (SLit 9)) (sv_denot ?E ?t) = _ |- _ =>
    exfalso; rewrite branch_ltu_U, U_SLit in Hc; change (zcanon 9) with 9 in Hc;
    first
    [ change t with (wu_se 0) in Hc; rewrite (wu_seU _ _ E11v Hv 0) in Hc; change (10 ^ Z.of_nat 0) with 1 in Hc
    | change t with (wu_t3 1) in Hc; rewrite (wu_t3U _ _ 1 E11v Hv) in Hc; change (10 ^ Z.of_nat 1) with 10 in Hc
    | change t with (wu_t3 2) in Hc; rewrite (wu_t3U _ _ 2 E11v Hv) in Hc; change (10 ^ Z.of_nat 2) with 100 in Hc
    | change t with (wu_t3 3) in Hc; rewrite (wu_t3U _ _ 3 E11v Hv) in Hc; change (10 ^ Z.of_nat 3) with 1000 in Hc
    | change t with (wu_t3 4) in Hc; rewrite (wu_t3U _ _ 4 E11v Hv) in Hc; change (10 ^ Z.of_nat 4) with 10000 in Hc
    | change t with (wu_se 1) in Hc; rewrite (wu_seU _ _ E11v Hv 1) in Hc; change (10 ^ Z.of_nat 1) with 10 in Hc
    | change t with (wu_se 2) in Hc; rewrite (wu_seU _ _ E11v Hv 2) in Hc; change (10 ^ Z.of_nat 2) with 100 in Hc
    | change t with (wu_se 3) in Hc; rewrite (wu_seU _ _ E11v Hv 3) in Hc; change (10 ^ Z.of_nat 3) with 1000 in Hc
    | change t with (wu_se 4) in Hc; rewrite (wu_seU _ _ E11v Hv 4) in Hc; change (10 ^ Z.of_nat 4) with 10000 in Hc ];
    first [apply Z.ltb_lt in Hc | apply Z.ltb_ge in Hc];
    clear - Hc Hvr Hv; Z.div_mod_to_equations; lia
  end.
(* Loop 1: at each continue test one side is impossible; follow the other until the loop exits. *)
Ltac wu_loop1 RUNP BR HS HJ2 E11v Hv Hvr U530 U529 U528 U516 Usp2 Uo2 Hsp1r Hlo WS Hhi Eab HWR fpos :=
  wu_br RUNP BR HS;
  [ first
    [ solve [wu_ref9 E11v Hv Hvr]
    | wu_clrc; paj_run_sh RUNP HS HJ2;
      [ wu_awr U530 U529 U516 Usp2 Uo2 Hsp1r Hlo WS Hhi Eab HWR fpos
      | wu_kd U530 U529 U528 U516 Usp2 Uo2 Hsp1r;
        wu_loop1 RUNP BR HS HJ2 E11v Hv Hvr U530 U529 U528 U516 Usp2 Uo2 Hsp1r Hlo WS Hhi Eab HWR fpos ] ]
  | first [ solve [wu_ref9 E11v Hv Hvr] | wu_clrc ] ].
(* 0x845d4 bltu ~o, j: ~o = 2^64 - 1 - o is far above j. *)
Ltac wu_refo E10v Ho4096 Hoceil C1 :=
  lazymatch goal with Hc : branch_taken BC_LTU _ _ = true |- _ =>
    exfalso; rewrite branch_ltu_U in Hc;
    erewrite (wu_xorU _ 10 _ _ E10v) in Hc by first [clear - Ho4096 Hoceil C1; lia | vm_compute; reflexivity];
    rewrite U_SLit, zcanon_id in Hc by (unfold M64; clear; lia); apply Z.ltb_lt in Hc; clear - Hc Hoceil C1; lia
  end.
(* Loop 2 under the tok runner: refute the pointer-overflow trap, run the copy of one byte, until the release
   (0x84620, offset 16044). *)
Ltac wu_loop2 RUN BR HS HJ2 SHOKc E10v E11v Ho4096 Hoceil C1 U530 U529 U528 U516 Usp2 Uo2 Hsp1r Hlo WS Hhi
    Eab HWR fpos E516 E528 E529 E530 :=
  psrr_branch_tok RUN BR HS SHOKc Bspan_WU;
  [ wu_refo E10v Ho4096 Hoceil C1
  | wu_clrc; paj_run_tok RUN HS HJ2 SHOKc Bspan_WU;
    [ wu_awr U530 U529 U516 Usp2 Uo2 Hsp1r Hlo WS Hhi Eab HWR fpos
    | wu_kd U530 U529 U528 U516 Usp2 Uo2 Hsp1r;
      wu_reU U530 U529 U528 U516 Usp2 Uo2 E10v E11v E516 E528 E529 E530;
      lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
        let p := eval vm_compute in (ss_pc ss) in
        lazymatch p with
        | 15968 => wu_loop2 RUN BR HS HJ2 SHOKc E10v E11v Ho4096 Hoceil C1 U530 U529 U528 U516 Usp2 Uo2 Hsp1r
                     Hlo WS Hhi Eab HWR fpos E516 E528 E529 E530
        | 16044 => idtac
        | _ => fail 1 "wu_loop2: unexpected stop" p
        end end ] ].
(* The walk. The five ranges of v (wu_n_cases) are walked by one script, run on all five goals (n = wu_getn):
   phase A (tok runner, SH = [mkSHE 10 0 n]) to the class-0 side-stack frame allocation (aj_stack_malloc_atS);
   after the re-seat three atoms (528 the flag cell, 529 the frame's shadow, 530 the aligned sp), the frame,
   its shadow, the flag cell and [sp1, sp1 + 16) as regions, and six shadow aliases; phase B (plain runner:
   the frame windows are open) through the descriptor, the poisoning and loop 1 (wu_loop1); phase C (frame
   windows read only, tok runner) through loop 2 (wu_loop2); phase D (windows open again) through the release
   with aj_flag_store_pi, then the ret. The post: the caller's journal from the runs, a0 = n, the blocks
   unchanged, the digits off the out region (wu_out_byte), and tcj_kept from what each run and the
   allocation kept (KA, HK, KD, PD; wu_tcj_chain). *)
Theorem pb_write_uint : twrite_uint_spec B.
Proof.
unfold twrite_uint_spec.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch o v
  HJ Hra Hra4 Hgp Htp Hch Hal Hlo Hhi H10 H11 Hv HWR HDST HRA Hfr.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (pa_base_lo (PL := PL_identb)) as HBLO.
pose proof HJ as (HARc & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hkk & F1 & F2 & F3 & F4 & Hgone & HJpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (wu_n_pos v) as Hn1.
assert (WS : WRITE_UINT_STK = 4176) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hdst : forall a, o <= a < o + write_uint_c.write_uint_n v ->
  4096 <= a < alloc_ceiling /\ ~ (IMG_LO <= a < IMG_TOP) /\
  ~ (SHADOW_OFF <= a < SHADOW_OFF + 17592186044416))
  by (intros a Ha; exact (wu_dst_byte lyc Sc W memc mdc o _ a HARc HDST Ha)).
assert (Ho4096 : 4096 <= o) by (destruct (Hdst o ltac:(lia)); lia).
assert (Hoceil : o + write_uint_c.write_uint_n v <= alloc_ceiling)
  by (destruct (Hdst (o + write_uint_c.write_uint_n v - 1) ltac:(lia)); lia).
assert (Hsplo : alloc_ceiling + 80 <= spZ regs) by lia.
assert (Hsphi : spZ regs <= 2 ^ 47) by lia.
assert (Hpres80 : forall a, spZ regs - 80 <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply HJpres; lia).
assert (Houtp : forall a, o <= a < o + write_uint_c.write_uint_n v ->
  apresent (w_H W) memc a /\ ~ (IMG_LO <= a < IMG_TOP))
  by (intros a Ha; split; [exact (proj1 (proj2 (HWR a Ha))) | exact (proj1 (proj2 (Hdst a Ha)))]).
assert (HBxU : forall (Ex : env), U Ex Bx_WU = SHADOW_OFF)
  by (intros Ex; unfold Bx_WU; rewrite U_SLit; rewrite zcanon_id by (unfold SB, M64; lia); exact SB_SHADOW_OFF).
destruct (wu_n_cases v Hv) as [(Hn & Hvr) | [(Hn & Hvr) | [(Hn & Hvr) | [(Hn & Hvr) | (Hn & Hvr)]]]];
rewrite Hn in *.
(* ---- the five cases n = 1..5 are walked by the same script, run on all five goals (n = wu_getn) ---- *)
all: let n := wu_getn in
  pose proof (wu_entry lyc Sc W regs memc mdc o v n HARc Hpres80 Hal Hsplo Hsphi H10 H11 Hv Ho4096 Hoceil
    ltac:(clear; lia) Houtp ltac:(vm_compute; reflexivity)) as HS.
all: remember (Eimg (Ereg regs wu_extra)) as E eqn:HE.
all: assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
all: assert (EE : forall j (r : bv 5), Z.of_nat j = bv_unsigned r -> ew E j = getr regs r)
  by (intros j r Hj; subst E; apply ew_Eimg_Ereg_nat; exact Hj).
all: assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
all: assert (HAE : env_agree 32 (Ereg regs wu_extra) E)
  by (subst E; split; [intros j Hj; apply Eimg_low; unfold A_TEXT; clear - Hj; lia | reflexivity]).
all: assert (E10 : ew E 10 = Z_to_bv 64 o) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
all: assert (E11 : ew E 11 = Z_to_bv 64 v) by (rewrite (EE 11%nat 11%bv eq_refl); exact H11).
all: assert (E32 : ew E 32 = Z_to_bv 64 (as_uar_cell B))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; clear; lia); exact (ew_Ereg_extra regs wu_extra 0)).
all: assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; clear; lia).
all: assert (EO1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; clear; lia).
all: assert (EO31 : ew E (A_OBJ 31) = Z_to_bv 64 (VAL (A_OBJ 31)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; clear; lia).
all: assert (Uo : bv_unsigned (ew E 10) = o)
  by (rewrite E10; apply unsigned_lit_small; clear - Ho4096 Hoceil C1; lia).
all: assert (U32 : bv_unsigned (ew E 32) = as_uar_cell B)
  by (rewrite E32; apply unsigned_lit_small; pose proof (palf_uar_img B TLF) as Hu; clear - Hu; lia).
all: assert (UO0 : bv_unsigned (ew E (A_OBJ 0)) = VAL (A_OBJ 0))
  by (rewrite EO0; apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 0)) as Hu; clear - Hu; lia).
all: assert (UO1 : bv_unsigned (ew E (A_OBJ 1)) = VAL (A_OBJ 1))
  by (rewrite EO1; apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 1)) as Hu; clear - Hu; lia).
all: assert (UO31 : bv_unsigned (ew E (A_OBJ 31)) = VAL (A_OBJ 31))
  by (rewrite EO31; apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 31)) as Hu; clear - Hu; lia).
all: clear HE.
all: let n := wu_getn in
  assert (SHOK : sh_ok SEGS Bx_WU [mkSHE 10 0 n] E (mrestrict (w_H W) memc))
  by (constructor; [|constructor];
      eapply (shent_ok_of_range SEGS (w_H W) memc E Bx_WU 10%nat o n o 0 n HRA (HBxU E));
      [ rewrite U_SOff, Uo, Z.add_0_r; apply zcanon_id; unfold M64; clear - Ho4096 Hoceil C1; lia
      | clear; lia | clear; lia
      | cbn [Z.min Z.max]; intros x Hx; exact (proj2 (proj2 (Hdst x ltac:(clear - Hx; lia)))) ]).
all: unfold cfg_at, A_write_uint; change (w64 (BASE + AF_write_uint)) with (Z_to_bv 64 (BASE + AF_write_uint)).
all: unfold ss_wu, stack_region, got_regionP, wu_cellR, uar_got_regionP, uar_cell_regionP, wu_outR in HS.
all: paj_run_tok RUN HS HJ SHOK Bspan_WU; [wu_awr_out (spZ regs - sp0) Usp E10 HWR |].
(* 0x844b4: the class-0 side-stack frame allocation, with sp aligned to 32 at 0x84484. *)
all: destruct (wu_sp1_facts (spZ regs + -64) ltac:(clear - Hsplo C1; lia)
  ltac:(rewrite <- Zplus_mod_idemp_l, Hal; reflexivity)) as (Hsp1r & Hsp1a32 & Hsp1a16).
all: prreg HS (1%bv : bv 5) R1; prreg HS (3%bv : bv 5) R3; prreg HS (4%bv : bv 5) R4.
all: lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
  pose proof (st_ok_restrict_reg SEGS (w_H W) Ev ssx msx (2%bv : bv 5) HS) as R2;
  change (sr_get (ss_regs ssx) (2%bv : bv 5)) with (SAlu ALU_AND (SOff 2 (-64)) (SLit (-32))) in R2;
  cbn [ms_regs restrict] in R2;
  rewrite (wu_denot_and_m32 Ev 2 (spZ regs) (-64)
    ltac:(rewrite (EE 2%nat 2%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned)
    ltac:(clear - Hsplo C1; lia) ltac:(clear - Hsphi; lia) ltac:(clear - Hsplo Hsphi C1; lia)) in R2 end.
all: assert (Hsp1b : 0 <= 32 * ((spZ regs + -64) / 32) < 2 ^ 64)
  by (clear - Hsp1r Hsphi Hsplo C1; lia).
all: assert (Rsp1 : spZ (ms_regs ms) = sp0 + (32 * ((spZ regs + -64) / 32) - sp0))
  by (unfold spZ at 1; rewrite R2, (unsigned_lit_small _ Hsp1b); clear; lia).
all: pmkst HS; rewrite (palf_sm0 B TLF).
all: eapply SRr_bind;
  [ eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs errno_low ML SMP 0 ASM0 ltac:(clear; lia) W (ms_regs ms) (ms_mem ms)
      STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (32 * ((spZ regs + -64) / 32) - sp0) _ HJ Rsp1);
    [ rewrite <- Zminus_mod_idemp_l, Hsp1a16, <- Zminus_mod_idemp_r, Hal16; reflexivity
    | clear - Hsp1r Hhi; lia
    | clear - Hsp1r Hlo WS Hes; lia
    | rewrite R3, (EE 3%nat 3%bv eq_refl); exact Hgp
    | rewrite R4, (EE 4%nat 4%bv eq_refl); exact Htp
    | exact R1
    | apply ret_ok_codeptr_v; [unfold AF_write_uint; clear; lia | reflexivity]
    | pose proof (count_cid_le_length 0 (frames Sc)) as Hcc; change (fs_frames 0) with 16384;
      clear - Hfr Hcc; lia ]
  | ].
all: cbv beta.
all: intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2
  & Hz & Hflag & HK & HJsub & (fS2 & ES2)).
(* ---- back at 0x844b8 with the frame: re-seat on what the call kept ---- *)
all: pose proof (proj1 HJ2) as HAR2.
all: assert (Hfin2 : In (0, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
all: destruct (al_frames _ _ LAWS lyc S2 W mem2 md2 0 fpos HAR2 Hfin2) as (HFal32 & _ & HFpres & HFSpres).
all: destruct (frames_bounds SEGS B LAWS lyc S2 W mem2 md2 0 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFapp).
all: destruct (frame_al64 _ _ lyc S2 W mem2 md2 0 fpos HAR2 Hfin2) as (HFal64 & _ & _).
all: pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFimg.
all: destruct (FFL lyc S2 W mem2 md2 0 fpos HAR2 Hfin2)
  as (HFLpres & HFLown & (HFLapp & HFLimg) & (HFL4096 & _ & HFLceil)).
all: change (fs_frame_bytes 0) with 64 in *.
all: pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres2 & _).
all: let n := wu_getn in assert (HDST2 : tdst_ok B lyc S2 o n)
  by (intros a Ha; destruct (HDST a Ha) as [(b & w & Hin & Hb) | (cid & pos & Hin & Hr)];
      [left; exists b, w; split; [rewrite Eab; exact Hin | exact Hb]
      | right; exists cid, pos; split; [rewrite Hfrs2; right; exact Hin | exact Hr]]).
all: let KK := run_K_hi HS in jafter_call_keep_hi HS KK regs2 (mrestrict (w_H W) mem2) HP2 [0;5]%nat HS2.
all: let n := wu_getn in lazymatch type of HS2 with ?Q -> _ => assert (HQ : Q)
  by (cbn [ms_mem restrict]; apply Forall_cons;
      [ split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha;
        [ apply (mbyte_of_aview SEGS); apply (proj1 HK); clear - Ha Hsplo Hsphi Hsp1r Hes C1; lia
        | intros _; apply (apresent_writable SEGS); apply HJpres2; clear - Ha Hlo Hhi WS Hes; lia ]
      | apply Forall_cons; [|apply Forall_nil];
        split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Uo; intros a Ha;
        [ apply (mbyte_of_aview SEGS);
          exact (wu_out_kept lyc Sc W (ms_mem ms) mem2 _ _ o n a HK HDST ltac:(clear - Ha; lia))
        | intros _; apply (apresent_writable SEGS);
          exact (wu_out_pres lyc S2 W mem2 md2 o n a HAR2 HDST2 ltac:(clear - Ha; lia)) ] ]) end.
all: specialize (HS2 HQ); clear HQ; rewrite <- restrict_mkst_fx in HS2; clear HS; rename HS2 into HS.
(* three more atoms: the frame's flag cell (528), the first byte of its shadow (529) and the aligned sp of
   0x84484 (530), so that the store 0x844ec sd a3,8(s1) has a base *)
all: lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_havoc_hi 528 Ev ssv msv
    [Z_to_bv 64 (flag_addr lyc 0 fpos); Z_to_bv 64 (SB + frame_addr lyc 0 fpos / 8);
     Z_to_bv 64 (32 * ((spZ regs + -64) / 32))] HS
    ltac:(vm_compute; reflexivity)) as HSa end.
all: clear HS; rename HSa into HS.
all: lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  assert (HEI1 : img_env VAL A_LIM Ev)
    by (apply img_env_havoc_hi; [apply img_env_havoc_hi; [exact HEI | cbv; clear; lia] | cbv; clear; lia]);
  assert (E516 : ew Ev 516 = Z_to_bv 64 (frame_addr lyc 0 fpos))
    by (rewrite ew_havoc_old by (cbv; clear; lia);
        etransitivity;
        [exact (ew_havoc_new E 512 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0) ltac:(cbv; clear; lia)) | exact Ha0]);
  assert (E528 : ew Ev 528 = Z_to_bv 64 (flag_addr lyc 0 fpos))
    by exact (ew_havoc_new _ 528
         [Z_to_bv 64 (flag_addr lyc 0 fpos); Z_to_bv 64 (SB + frame_addr lyc 0 fpos / 8);
          Z_to_bv 64 (32 * ((spZ regs + -64) / 32))]
         0 (Z_to_bv 64 0) ltac:(cbn; clear; lia));
  assert (E529 : ew Ev 529 = Z_to_bv 64 (SB + frame_addr lyc 0 fpos / 8))
    by exact (ew_havoc_new _ 528
         [Z_to_bv 64 (flag_addr lyc 0 fpos); Z_to_bv 64 (SB + frame_addr lyc 0 fpos / 8);
          Z_to_bv 64 (32 * ((spZ regs + -64) / 32))]
         1 (Z_to_bv 64 0) ltac:(cbn; clear; lia));
  assert (E530 : ew Ev 530 = Z_to_bv 64 (32 * ((spZ regs + -64) / 32)))
    by exact (ew_havoc_new _ 528
         [Z_to_bv 64 (flag_addr lyc 0 fpos); Z_to_bv 64 (SB + frame_addr lyc 0 fpos / 8);
          Z_to_bv 64 (32 * ((spZ regs + -64) / 32))]
         2 (Z_to_bv 64 0) ltac:(cbn; clear; lia));
  assert (Usp2 : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite !ew_havoc_old by (cbv; clear; lia); exact Usp);
  assert (E2v : ew Ev 2 = Z_to_bv 64 (spZ regs)) by (rewrite <- Usp2; symmetry; apply Z_to_bv_bv_unsigned);
  assert (Uo2 : bv_unsigned (ew Ev 10) = o) by (rewrite !ew_havoc_old by (cbv; clear; lia); exact Uo);
  assert (E10v : ew Ev 10 = Z_to_bv 64 o) by (rewrite !ew_havoc_old by (cbv; clear; lia); exact E10);
  assert (E11v : ew Ev 11 = Z_to_bv 64 v) by (rewrite !ew_havoc_old by (cbv; clear; lia); exact E11)
end.
all: unfold app_addr in HFLapp.
all: assert (U516 : bv_unsigned (ew _ 516) = frame_addr lyc 0 fpos)
  by (rewrite E516; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia).
all: assert (U528 : bv_unsigned (ew _ 528) = flag_addr lyc 0 fpos)
  by (rewrite E528; apply unsigned_lit_small; clear - HFL4096 HFLceil C1; lia).
all: assert (U529 : bv_unsigned (ew _ 529) = SB + frame_addr lyc 0 fpos / 8)
  by (rewrite E529; apply unsigned_lit_small; unfold SB;
      clear - HF4096 HFceil C1; Z.div_mod_to_equations; lia).
all: assert (U530 : bv_unsigned (ew _ 530) = 32 * ((spZ regs + -64) / 32))
  by (rewrite E530; apply unsigned_lit_small; exact Hsp1b).
(* the frame, its shadow and its flag cell are apart from the stack window and from the destination *)
all: let n := wu_getn in
  assert (HFoutD : o + n <= frame_addr lyc 0 fpos \/ frame_addr lyc 0 fpos + 64 <= o)
  by exact (wu_out_frame_disj lyc Sc S2 W mem2 md2 o n 0 fpos HAR2 HDST Eab Hfrs2
       ltac:(clear; lia) ltac:(change (fs_frame_bytes 0) with 64; clear; lia)).
all: let n := wu_getn in
  assert (HShoutD : o + n <= SB + frame_addr lyc 0 fpos / 8 \/ SB + frame_addr lyc 0 fpos / 8 + 8 <= o)
  by (apply (wu_range_disj (fun a => SHADOW_OFF <= a < SHADOW_OFF + 17592186044416) o n
        (SB + frame_addr lyc 0 fpos / 8) 8);
      [ intros a Ha; exact (proj2 (proj2 (Hdst a ltac:(clear - Ha; lia))))
      | intros a Ha; unfold SB, SHADOW_OFF in *; clear - Ha HF4096 HFceil C1; Z.div_mod_to_equations; lia
      | clear; lia | clear; lia ]).
all: let n := wu_getn in
  assert (HFLoutD : o + n <= flag_addr lyc 0 fpos \/ flag_addr lyc 0 fpos + 1 <= o)
  by (apply (wu_range_disj (fun a => aowned B lyc S2 a) o n (flag_addr lyc 0 fpos) 1);
      [ intros a Ha; exact (wu_out_notowned lyc S2 W mem2 md2 o n a HAR2 HDST2 ltac:(clear - Ha; lia))
      | intros a Ha; replace a with (flag_addr lyc 0 fpos) by (clear - Ha; lia); exact HFLown
      | clear; lia | clear; lia ]).
all: assert (HFLFD : flag_addr lyc 0 fpos + 1 <= frame_addr lyc 0 fpos
                \/ frame_addr lyc 0 fpos + 64 <= flag_addr lyc 0 fpos)
  by (destruct (Z_le_gt_dec (flag_addr lyc 0 fpos + 1) (frame_addr lyc 0 fpos)) as [H1|H1]; [left; exact H1|];
      destruct (Z_le_gt_dec (frame_addr lyc 0 fpos + 64) (flag_addr lyc 0 fpos)) as [H2|H2]; [right; exact H2|];
      exfalso; exact (proj2 (HFpres (flag_addr lyc 0 fpos) ltac:(clear - H1 H2; lia)) HFLown)).
all: assert (HFsh : SB + frame_addr lyc 0 fpos / 8 = shadow_addr (frame_addr lyc 0 fpos))
  by (unfold shadow_addr, SB, SHADOW_OFF; clear; lia).
(* the frame region *)
all: wu_addreg HS wu_frameR
  ltac:(unfold wu_frameR, region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite U516; split; [clear - HF4096; lia|]; split; [clear - HFceil C1; lia|]; split;
        [ intros ofs Hofs; apply (apresent_writable SEGS);
          exact (proj1 (HFpres (frame_addr lyc 0 fpos + ofs) ltac:(clear - Hofs; lia)))
        | constructor; [|constructor];
          apply (chunk_ok_val SEGS _ _ (frame_addr lyc 0 fpos) 56 8 (SOff 528 0) (flag_addr lyc 0 fpos));
          [ cbn [sv_denot]; rewrite E528, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | clear - HFLapp HFLceil C1; zside | zside |];
          replace (frame_addr lyc 0 fpos + 56) with (frame_addr lyc 0 fpos + 64 - 8) by (clear; lia);
          exact (val_mem_of_rdword SEGS (w_H W) mem2 _ _ Hflag) ])
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
          let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
        unfold wu_frameR; cbn [all_disjoint]; unfold extent_disjoint;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite U516, Usp2, Uo2;
        clear - HF4096 HFceil C1 Hsplo Hsphi Hlo Hhi WS Hes HFoutD; repeat split; lia).
(* the frame's shadow *)
all: wu_addreg HS wu_fshR
  ltac:(unfold wu_fshR, region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite U529; split; [unfold SB; clear - HF4096; Z.div_mod_to_equations; lia|];
        split; [unfold SB; clear - HFceil C1; Z.div_mod_to_equations; lia|];
        split; [|constructor];
        intros ofs Hofs; apply (apresent_writable SEGS); rewrite HFsh; exact (proj1 (HFSpres ofs Hofs)))
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
          let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
        unfold wu_fshR; cbn [all_disjoint]; unfold extent_disjoint;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite U529, U516, Usp2, Uo2;
        unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp;
        clear - HF4096 HFceil C1 Hsplo Hsphi HFapp HShoutD; unfold SB in *;
        repeat split; Z.div_mod_to_equations; lia).
(* the frame's flag cell: no writable window until the release run *)
all: wu_addreg HS wu_flagR
  ltac:(unfold wu_flagR, region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite U528; split; [clear - HFL4096; lia|]; split; [clear - HFLceil C1; lia|];
        split; [intros ofs Hofs; exfalso; clear - Hofs; lia | constructor])
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
          let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
        unfold wu_flagR; cbn [all_disjoint]; unfold extent_disjoint;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite U528, U529, U516, Usp2, Uo2;
        unfold kLowShadowBeg, kHighMemBeg in HFLapp;
        clear - HFLapp HFLceil C1 Hsplo Hsphi HFLFD HFLoutD HF4096 HFceil; unfold SB in *;
        repeat split; Z.div_mod_to_equations; lia).
(* the facts the engine needs to place the frame's descriptor and shadow stores *)
all: lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_add_fact Ev ssv msv 516 (PTR 6) HS
    ltac:(unfold afact_ok, PTR; cbn [af_lo af_hi af_al2]; rewrite U516; change (2 ^ 6) with 64;
          clear - HF4096 HFceil HFal64 C1; lia)) as HSa end.
all: clear HS; rename HSa into HS; wu_norm HS.
all: lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_add_fact Ev ssv msv 528 (PTR 0) HS
    ltac:(unfold afact_ok, PTR; cbn [af_lo af_hi af_al2]; rewrite U528, Z.pow_0_r, Z.mod_1_r;
          clear - HFL4096 HFLceil C1; lia)) as HSa end.
all: clear HS; rename HSa into HS; wu_norm HS.
all: lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_add_fact Ev ssv msv 529 (mkAF (SB + 512) (SB + 17592186044416) 3) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U529; change (2 ^ 3) with 8; unfold SB;
          clear - HF4096 HFceil HFal64 C1; Z.div_mod_to_equations; lia)) as HSa end.
all: clear HS; rename HSa into HS; wu_norm HS.
(* the frame's shadow at (a3 >> 3) + SB (the poisoning and the release) and at ((a3 + 32 + i) >> 3) + SB (the
   tmp check of loop 1, i < 5) *)
all: assert (HF8 : frame_addr lyc 0 fpos mod 8 = 0) by (clear - HFal64; Z.div_mod_to_equations; lia).
all: assert (HFb : 0 <= frame_addr lyc 0 fpos < 2 ^ 47) by (clear - HF4096 HFceil C1; lia).
all: wu_alias HS 0 E516 E529 HFb HF8; wu_alias HS 32 E516 E529 HFb HF8; wu_alias HS 33 E516 E529 HFb HF8;
  wu_alias HS 34 E516 E529 HFb HF8; wu_alias HS 35 E516 E529 HFb HF8; wu_alias HS 36 E516 E529 HFb HF8.
(* s1 and sp hold the aligned sp of 0x84484: name them atom 530 *)
all: lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  destruct (wu_sp1_denot Ev (spZ regs) E2v E530 ltac:(clear - Hsplo Hsphi C1; lia)) as (Dsp & Ds1) end.
all: lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict ?Hx ?msy) =>
  pose proof (ast_ok_pi_set_reg_fp Ev ssx (restrict Hx msy) (9%bv : bv 5) (SOff 530 0) HS
    ltac:(vm_compute; reflexivity)
    ltac:(cbn [ms_regs restrict]; rewrite (st_ok_pi_restrict_reg Hx Ev ssx msy (9%bv : bv 5) HS); exact Ds1))
    as HSa end.
all: clear HS; rename HSa into HS; wu_norm HS.
all: lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict ?Hx ?msy) =>
  pose proof (ast_ok_pi_set_reg_fp Ev ssx (restrict Hx msy) (2%bv : bv 5) (SOff 530 0) HS
    ltac:(vm_compute; reflexivity)
    ltac:(cbn [ms_regs restrict]; rewrite (st_ok_pi_restrict_reg Hx Ev ssx msy (2%bv : bv 5) HS); exact Dsp))
    as HSa end.
all: clear HS; rename HSa into HS; wu_norm HS; clear Dsp Ds1.
all: lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_add_fact Ev ssv msv 530 (mkAF (2 ^ 46) (2 ^ 47) 5) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U530; change (2 ^ 5) with 32;
          clear - Hsp1r Hsp1a32 Hsplo Hsphi C1; lia)) as HSa end.
all: clear HS; rename HSa into HS; wu_norm HS.
(* the stack region keeps the saved registers, [sp0 - 48, sp0); [sp1, sp1 + 16) becomes a region of its own *)
all: lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  let rs' := eval vm_compute in (wu_trim (ss_mem ssx)) in
  pose proof (st_ok_pi_submem Ev ssx msx rs' HS ltac:(cbn [ss_mem]; wu_submem) ltac:(vm_compute; reflexivity))
    as HSa end.
all: clear HS; rename HSa into HS; wu_norm HS.
all: wu_addreg HS wu_sp1R
  ltac:(unfold wu_sp1R, region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite U530; split; [clear - Hsp1r Hsplo C1; lia|]; split; [clear - Hsp1r Hsphi; lia|];
        split; [|constructor];
        intros ofs Hofs; apply (apresent_writable SEGS); apply HJpres2; clear - Hofs Hsp1r Hlo Hhi WS Hes; lia)
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
          let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
        unfold wu_sp1R; cbn [all_disjoint]; unfold extent_disjoint;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite U530, U528, U529, U516, Usp2, Uo2;
        clear - Hsp1r Hsplo Hsphi C1 HFLceil HFceil HF4096 Hoceil; unfold SB in *;
        repeat split; Z.div_mod_to_equations; lia).
(* ---- what the run before the allocation and the allocation kept (for the post and the phase-C shadow) ---- *)
all: assert (Hwin : alloc_ceiling <= spZ regs - 4176) by (clear - Hceil Hslo Hlo WS; lia).
all: let n := wu_getn in
  lazymatch goal with HFrA : frame_of ?EA ?rsA (mrestrict ?Hh ?mc) (mrestrict ?Hh ?mT) |- _ =>
  assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 4176 <= a < spZ regs) -> ~ (o <= a < o + n) ->
     aview SEGS (w_H W) mT a = aview SEGS (w_H W) memc a);
  [ intros a Ha Hw HE;
    apply (kept_of_frame (segs := SEGS) EA rsA (w_H W) memc mT
      (fun x => (spZ regs - 4176 <= x < spZ regs) \/ (o <= x < o + n)) HFrA);
    [ let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a' := fresh "a" in
      let Hin := fresh "Hin" in let Ha' := fresh "Ha" in
      intros b wlo whi a' Hin Ha';
      lazymatch type of Hin with In _ (windows ?rs) =>
        let w := eval vm_compute in (windows rs) in change (In (b, wlo, whi) w) in Hin end;
      cbn [In] in Hin;
      repeat (destruct Hin as [Hin | Hin];
        [ inversion Hin; subst; cbn [base_val] in Ha'; first [rewrite Usp in Ha' | rewrite Uo in Ha' | idtac];
          first [exfalso; clear - Ha'; lia | left; clear - Ha'; lia | right; clear - Ha'; lia]
        | ]);
      destruct Hin
    | exact Ha | intros [Hx | Hx]; [exact (Hw Hx) | exact (HE Hx)] ]
  | clear HFrA ] end.
all: lazymatch goal with HGA : mem_grows (mrestrict ?Hh ?mc) (mrestrict ?Hh ?mT) |- _ =>
  assert (PA : forall a, apresent (w_H W) memc a -> apresent (w_H W) mT a)
    by (intros a Hp; exact (apresent_grows _ _ _ a HGA Hp)); clear HGA end.
all: repeat match goal with Hf : frame_of _ _ _ _ |- _ => clear Hf end.
all: pose proof HK as (HK1 & HK2 & HK3 & HK4 & HK5 & HK6).
(* the frame, its shadow and its flag cell are apart from the blocks, the frames and the image of the call *)
all: assert (HBL : forall b w i, In (b, w) (ablocks B lyc Sc) -> 0 <= i < req_size w ->
  ~ (frame_addr lyc 0 fpos <= b + i < frame_addr lyc 0 fpos + 64) /\ b + i <> flag_addr lyc 0 fpos)
  by (intros b w i Hin Hi; assert (Hin2 : In (b, w) (ablocks B lyc S2)) by (rewrite Eab; exact Hin);
      pose proof (sep_block_frame SEGS B LAWS lyc S2 W mem2 md2 b w 0 fpos HAR2 Hin2 Hfin2) as Hd;
      unfold zdisjoint in Hd; cbn [fst snd] in Hd; change (fs_frame_bytes 0) with 64 in Hd;
      destruct (al_blocks _ _ LAWS lyc S2 W mem2 md2 b w HAR2 Hin2) as (_ & _ & _ & _ & Hpres & _);
      split; [clear - Hd Hi; lia|];
      intros Heq; apply (proj2 (Hpres (b + i) ltac:(clear - Hi; lia))); rewrite Heq; exact HFLown).
all: assert (HFR : forall cid pos a, In (cid, pos) (frames Sc) ->
  (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
  ~ (frame_addr lyc 0 fpos <= a < frame_addr lyc 0 fpos + 64) /\
  ~ (shadow_addr (frame_addr lyc 0 fpos) <= a < shadow_addr (frame_addr lyc 0 fpos) + 8) /\
  a <> flag_addr lyc 0 fpos)
  by (intros cid pos a Hin Hr;
      assert (HinS2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; right; exact Hin);
      destruct (in_split _ _ Hin) as (l1 & l2 & El);
      assert (Hzd : forall x,
        (in_zr x (frame_rng lyc (0, fpos)) \/ in_zr x (shadow_addr (frame_addr lyc 0 fpos), fs_frame_bytes 0 / 8)) ->
        (in_zr x (frame_rng lyc (cid, pos)) \/ in_zr x (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
        False)
        by (intros x Hx1 Hx2; exact (frames_zone_disj SEGS B LAWS lyc S2 W mem2 md2 (0, fpos) (cid, pos) [] l1 l2 x
              HAR2 ltac:(rewrite Hfrs2, El; reflexivity) Hx1 Hx2));
      split; [intros HF; apply (Hzd a); [left; unfold in_zr, frame_rng; cbn [fst snd];
        change (fs_frame_bytes 0) with 64; clear - HF; lia | exact Hr]|];
      split; [intros HS'; apply (Hzd a); [right; unfold in_zr; cbn [fst snd];
        change (fs_frame_bytes 0 / 8) with 8; clear - HS'; lia | exact Hr]|];
      intros Heq; rewrite Heq in Hr;
      destruct (al_frames _ _ LAWS lyc S2 W mem2 md2 cid pos HAR2 HinS2) as (_ & _ & Hp & Hsp);
      destruct Hr as [Hr | Hr]; unfold frame_rng, in_zr in Hr; cbn [fst snd] in Hr;
      [ exact (proj2 (Hp _ Hr) HFLown)
      | pose proof (Hsp (flag_addr lyc 0 fpos - shadow_addr (frame_addr lyc cid pos)) ltac:(clear - Hr; lia)) as Hq;
        replace (shadow_addr (frame_addr lyc cid pos) + (flag_addr lyc 0 fpos - shadow_addr (frame_addr lyc cid pos)))
          with (flag_addr lyc 0 fpos) in Hq by (clear; lia);
        exact (proj2 Hq HFLown) ]).
all: assert (HIM : forall a, in_img SEGS a ->
  ~ (frame_addr lyc 0 fpos <= a < frame_addr lyc 0 fpos + 64) /\
  ~ (shadow_addr (frame_addr lyc 0 fpos) <= a < shadow_addr (frame_addr lyc 0 fpos) + 8) /\
  a <> flag_addr lyc 0 fpos)
  by (intros a Him; split; [intros HF; exact (frm_img SEGS B LAWS lyc S2 W mem2 md2 0 fpos a HAR2 Hfin2 HF Him)|];
      split; [intros HS'; pose proof (pa_segs_low a Him) as Hl;
        assert (Hq1 : 0 <= frame_addr lyc 0 fpos <= alloc_ceiling) by (clear - HF4096 HFceil; lia);
        pose proof (wu_shadow_rng (frame_addr lyc 0 fpos) Hq1) as Hr;
        unfold kLowMemEnd in *; clear - Hl Hr HS'; lia|];
      intros Heq; subst a; exact (HFLimg Him)).
(* a byte of a frame of the call state (or of its shadow) off the destination: outside D, and the
   allocation kept it *)
all: let n := wu_getn in
  assert (KZ : forall cid pos a, In (cid, pos) (frames Sc) ->
  (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
  ~ (o <= a < o + n) ->
  ~ wu_D (spZ regs) 4176 o n (frame_addr lyc 0 fpos) (flag_addr lyc 0 fpos) a /\
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a)
  by (intros cid pos a Hin Hr HE;
      destruct (HFR cid pos a Hin Hr) as (HnF & HnS & HnFL);
      destruct (frame_zone SEGS B LAWS lyc Sc W memc mdc cid pos a HARc Hin Hr) as (Hzc & Hz2);
      destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HARc Hin) as (Hf0 & _ & _);
      assert (Ha64 : 0 <= a < 2 ^ 64)
        by (destruct Hz2 as [(Hq & _) | Hq]; unfold kLowMemEnd in *; clear - Hq Hzc Hf0 C1; lia);
      assert (Hw : ~ (spZ regs - 4176 <= a < spZ regs)) by (clear - Hzc Hwin; lia);
      split; [unfold wu_D; intros [H|[H|[H|[H|H]]]];
        [exact (Hw H) | exact (HE H) | exact (HnF H) | exact (HnS H) | exact (HnFL H)]|];
      rewrite (HK4 cid pos a Hin Hr (fun x => x)); exact (KA a Ha64 Hw HE)).
(* since the allocation: outside D nothing changed (KD), what was present stays (PD) *)
all: let n := wu_getn in
  assert (KD : forall a, 0 <= a < 2 ^ 64 ->
  ~ wu_D (spZ regs) 4176 o n (frame_addr lyc 0 fpos) (flag_addr lyc 0 fpos) a ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem2 a) by (intros; reflexivity).
all: assert (PD : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) mem2 a) by (intros a Hp; exact Hp).
(* ---- phase B: the descriptor, the poisoning and loop 1, with the plain runner (the frame windows are open) ---- *)
all: paj_run_sh RUNP HS HJ2; [wu_awr U530 U529 U516 Usp2 Uo2 Hsp1r Hlo WS Hhi Eab HWR fpos |].
all: wu_kd U530 U529 U528 U516 Usp2 Uo2 Hsp1r.
(* loop 1: one turn per digit; 0x845a0 bltu 9, x_i continues while x_i = v / 10^i > 9 *)
all: wu_loop1 RUNP BR HS HJ2 E11v Hv Hvr U530 U529 U528 U516 Usp2 Uo2 Hsp1r Hlo WS Hhi Eab HWR fpos.
all: wu_clrc.
(* ---- phase C: loop 2 with the tok runner; the frame and its shadow are read only there ---- *)
all: wu_setwin HS 516%nat 0 0 ltac:(intros ofs Hofs; clear - Hofs; lia).
all: wu_setwin HS 529%nat 0 0 ltac:(intros ofs Hofs; clear - Hofs; lia).
all: let n := wu_getn in
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msX) =>
  assert (HRAc : range_addressable (aview SEGS (w_H W) (ms_mem msX)) SHADOW_OFF o n);
  [ intros x Hx; pose proof (Hdst x Hx) as (Hx1 & _ & _);
    destruct (HDST x Hx) as [(b & w & Hin & Hb) | (cid & pos & Hin & Hr)];
    [ destruct (al_shadow _ _ LAWS lyc S2 W _ _ b w (proj1 HJ2) ltac:(rewrite Eab; exact Hin)) as (HBS & _);
      exact (block_shadow_range _ _ b (req_size w) x 1 HBS ltac:(clear - Hb; lia) ltac:(clear - Hb; lia) x
               ltac:(clear; lia))
    | destruct (HRA x Hx) as (sv & Hs & Hok); exists sv; split; [|exact Hok];
      destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HARc Hin) as (Hf0 & _ & _);
      destruct (al_frames _ _ LAWS lyc Sc W memc mdc cid pos HARc Hin) as (Hfal & _);
      destruct (frame_al64 _ _ lyc Sc W memc mdc cid pos HARc Hin) as (_ & Hbal & _);
      unfold frame_rng, in_zr in Hr; cbn [fst snd] in Hr;
      pose proof (wu_frame_shadow_in (frame_addr lyc cid pos) (fs_frame_bytes cid) x
        ltac:(clear - Hfal; Z.div_mod_to_equations; lia) ltac:(clear - Hbal; Z.div_mod_to_equations; lia)
        ltac:(clear - Hf0; lia) Hr) as Hsx;
      assert (HEs : ~ (o <= shadow_of_addr SHADOW_OFF x < o + n));
      [ intros Hq; apply (proj2 (proj2 (Hdst (shadow_of_addr SHADOW_OFF x) Hq)));
        unfold shadow_of_addr, SHADOW_OFF in *; clear - Hx1 C1; Z.div_mod_to_equations; lia
      | destruct (KZ cid pos _ Hin (or_intror Hsx) HEs) as (ND & Heq);
        rewrite (KD (shadow_of_addr SHADOW_OFF x)
          ltac:(unfold shadow_of_addr, SHADOW_OFF in *; clear - Hx1 C1; Z.div_mod_to_equations; lia) ND),
          Heq;
        exact Hs ] ]
  | ];
  assert (SHOKc : sh_ok SEGS Bx_WU [mkSHE 10 0 n] Ev (mrestrict (w_H W) (ms_mem msX)));
  [ constructor; [|constructor];
    eapply (shent_ok_of_range SEGS (w_H W) (ms_mem msX) Ev Bx_WU 10%nat o n o 0 n HRAc (HBxU Ev));
    [ rewrite U_SOff, Uo2, Z.add_0_r; apply zcanon_id; unfold M64; clear - Ho4096 Hoceil C1; lia
    | clear; lia | clear; lia
    | cbn [Z.min Z.max]; intros x Hx; exact (proj2 (proj2 (Hdst x ltac:(clear - Hx; lia)))) ]
  | ]
  end.
all: paj_run_tok RUN HS HJ2 SHOKc Bspan_WU; [wu_awr U530 U529 U516 Usp2 Uo2 Hsp1r Hlo WS Hhi Eab HWR fpos |].
all: wu_kd U530 U529 U528 U516 Usp2 Uo2 Hsp1r.
all: wu_reU U530 U529 U528 U516 Usp2 Uo2 E10v E11v E516 E528 E529 E530.
(* loop 2: one turn per byte; the trap tests are static but 0x845d4 bltu ~o, j *)
all: wu_loop2 RUN BR HS HJ2 SHOKc E10v E11v Ho4096 Hoceil C1 U530 U529 U528 U516 Usp2 Uo2 Hsp1r Hlo WS Hhi
  Eab HWR fpos E516 E528 E529 E530.
(* ---- phase D: the release, with the frame, its shadow and the flag byte writable again ---- *)
all: wu_setwin HS 529%nat 0 8 ltac:(intros ofs Hofs; cbn [YP09.r_base base_val ms_mem restrict]; rewrite U529;
  apply (apresent_writable SEGS); rewrite HFsh;
  destruct (al_frames _ _ LAWS lyc S2 W _ _ 0 fpos (proj1 HJ2) Hfin2) as (_ & _ & _ & HSP);
  exact (proj1 (HSP ofs ltac:(change (fs_frame_bytes 0 / 8) with 8; clear - Hofs; lia)))).
all: wu_setwin HS 516%nat 0 64 ltac:(intros ofs Hofs; cbn [YP09.r_base base_val ms_mem restrict]; rewrite U516;
  apply (apresent_writable SEGS);
  destruct (al_frames _ _ LAWS lyc S2 W _ _ 0 fpos (proj1 HJ2) Hfin2) as (_ & _ & HFP & _);
  exact (proj1 (HFP (frame_addr lyc 0 fpos + ofs) ltac:(change (fs_frame_bytes 0) with 64; clear - Hofs; lia)))).
all: wu_setwin HS 528%nat 0 1 ltac:(intros ofs Hofs; cbn [YP09.r_base base_val ms_mem restrict]; rewrite U528;
  apply (apresent_writable SEGS);
  destruct (FFL lyc S2 W _ _ 0 fpos (proj1 HJ2) Hfin2) as (HFLp & _);
  replace (flag_addr lyc 0 fpos + ofs) with (flag_addr lyc 0 fpos) by (clear - Hofs; lia); exact HFLp).
all: paj_run_flag_sh RUNF HS HJ2;
  [ clear; lia
  | eapply wu_awr_flag;
    [ wu_awr U530 U529 U516 Usp2 Uo2 Hsp1r Hlo WS Hhi Eab HWR fpos
    | cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite U528 in Ha; clear - Ha; lia ]
  | intros msr HSr;
    lazymatch type of HSr with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let rs := eval vm_compute in (ss_mem ssx) in
      let i := wu_idx rs 528%nat in let i := eval vm_compute in i in
      let r := eval vm_compute in (nth i rs got_regionP) in
      pose proof (st_ok_pi_region_nth Ex ssx msx i r HSr ltac:(vm_compute; reflexivity)) as HRf end;
    pose proof (field_of_region_any _ _ 528%nat _ _ _ _ _ _ 0 1%N (SLit 0) HRf U528
      ltac:(cbn [In]; left; reflexivity) ltac:(clear; lia) 0%nat ltac:(clear; lia)) as Hv0;
    cbn [Z.of_nat] in Hv0; rewrite !Z.add_0_r in Hv0; exact Hv0
  | wu_kd U530 U529 U528 U516 Usp2 Uo2 Hsp1r ].
(* ---- the return, 0x846a8 ret ---- *)
all: lazymatch type of HS with st_ok_pi _ _ ?Ef ?ssf (restrict _ ?msf) =>
  pose proof (st_ok_pi_restrict_reg (w_H W) Ef ssf msf (1%bv : bv 5) HS) as RR1;
  pose proof (st_ok_pi_restrict_reg (w_H W) Ef ssf msf (10%bv : bv 5) HS) as RR10;
  let e1 := eval vm_compute in (sr_get (ss_regs ssf) (1%bv : bv 5)) in
  change (sr_get (ss_regs ssf) (1%bv : bv 5)) with e1 in RR1;
  let e10 := eval vm_compute in (sr_get (ss_regs ssf) (10%bv : bv 5)) in
  change (sr_get (ss_regs ssf) (10%bv : bv 5)) with e10 in RR10;
  assert (HAEf : env_agree 32 (Ereg regs wu_extra) Ef)
    by (destruct HAE as [HA HD]; split;
        [ intros j Hj; rewrite ?ew_ewset_other by (clear - Hj; lia); rewrite !ew_havoc_old by (clear - Hj; lia);
          apply HA; exact Hj
        | exact HD ]);
  assert (EF1 : ew Ef 1 = getr regs 1)
    by (destruct HAEf as [HA _]; rewrite (HA 1%nat ltac:(clear; lia)); apply ew_Ereg_nat; reflexivity);
  rename msf into msF
end.
all: assert (Ra : v_jalr (getr (ms_regs msF) 1) 0 = getr regs 1)
  by (rewrite RR1; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, EF1; exact Hra).
all: eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)); intros mat'.
all: unfold twrite_uint_post; split; [reflexivity|].
all: eexists lyc, (stack_free_state 0 fpos S2), _, _, _.
all: split; [rewrite Ra; reflexivity|].
all: split; [unfold EV_WRITE_UINT; rewrite Z.add_0_r; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ2|].
all: split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs wu_extra HS); [exact HAEf | vm_compute; reflexivity]|].
all: split; [rewrite Hn, RR10; reflexivity|].
all: split;
  [ assert (Eab' : ablocks B lyc (stack_free_state 0 fpos S2) = ablocks B lyc Sc)
      by (rewrite <- Eab; unfold ablocks; rewrite blocks_stack_free_state; reflexivity);
    rewrite Eab'; apply Permutation_refl |].
(* the digits, off the out region's chunks: byte j is the digit of loop 1's turn n - 1 - j *)
all: split;
  [ lazymatch type of HS with st_ok_pi _ _ ?Ef ?ssf ?msx =>
      let rs := eval vm_compute in (ss_mem ssf) in
      let i := wu_idx rs 10%nat in let i := eval vm_compute in i in
      let r := eval vm_compute in (nth i rs got_regionP) in
      pose proof (st_ok_pi_region_nth Ef ssf msx i r HS ltac:(vm_compute; reflexivity)) as HRo end;
    let n := wu_getn in
    assert (Hlen : length (wu_bytes v) = Z.to_nat n)
      by (rewrite <- (Nat2Z.id (length (wu_bytes v))), wu_bytes_len, Hn; reflexivity);
    apply wu_garr8_of_vals; [|intros j Hj; exact (wu_bytes_rng v j Hj)];
    intros j Hj; rewrite Hlen in Hj; cbn in Hj;
    do 5 (destruct j as [|j];
      [ first
        [ exfalso; clear - Hj; lia
        | rewrite wu_bytes_nth by (rewrite Hlen; cbn; clear - Hj; lia); rewrite Hlen;
          eapply wu_out_byte;
          [ exact HRo | reflexivity | exact Uo2 | cbn [YP09.r_chunks In]; repeat first [left; reflexivity | right]
          | exact E11v | exact Hv ] ]
      | ]);
    exfalso; clear - Hj; lia
  | ].
(* what the call kept *)
all: rewrite Hn, WS; let n := wu_getn in
  eapply (wu_tcj_chain 4176 lyc Sc W memc mdc _ mem2 _ (spZ regs) o n (frame_addr lyc 0 fpos) (flag_addr lyc 0 fpos)
    _ _ HARc KA PA HK);
  [ clear - Hsp1r Hes; lia
  | clear - Hsp1r; lia
  | exact KD
  | exact PD
  | pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpF & _);
    intros a Ha; apply HJpF; clear - Ha Hlo Hhi WS; lia
  | exact Hwin | exact HDST | exact HF4096 | exact HFceil | exact HFLceil | exact HBL | exact HFR | exact HIM ].
Qed.
End walk.

End f.
End d.
