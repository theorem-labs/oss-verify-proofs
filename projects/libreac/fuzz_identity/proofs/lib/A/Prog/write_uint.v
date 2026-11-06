(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the contract and ASan-build program walk of fuzz_identity's write_uint, adapting the side-stack frame walk of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChf.v (andi-sp rebase, frame allocation, reseat after the call, flag store) and the leaf walk of lib/A/AChd.v. *)
(* write_uint (fuzz_identity.asan 0x84160, listing offset AF_write_uint = 0x3a54) on the ASan build: it
   writes the decimal digits of v (the plain model, lib/Prog/write_uint_c.v) at o and returns their count.

   Callers. The only caller is reac_identity_reac_ver_str (0x84090, 0x840c0, 0x840f8), which has no
   side-stack frame and passes o inside the buffer it got from LLVMFuzzerTestOneInput: a buffer in the
   entry's side-stack frame (0x81094) or a heap block (0x8176c). A byte in a frame of the caller's caller
   cannot be composed through YCbq.v ajournal_sub (it needs every written byte in a heap block or a tmp
   block), so twrite_uint_spec is in cgif's caller-journal form (lib/YC20.v:311-365; the shapes tcj_kept,
   twr_ok and tdst_ok are IdentCJ.v's): the premise is the caller's journal, the right to write [o, o + n)
   is the caller's per-byte premise, the post extends the same journal.

   The walk runs on the caller's journal. Its phases: entry to the frame allocation at 0x841b4 (plain
   run); the class-0 side-stack frame allocation (YC85.aj_stack_malloc_atS); the frame setup and the first
   digit loop (plain runs, one symbolic branch per digit); the copy loop 0x842c8..0x84304 (a run with
   shadow tokens: the shadow bytes of [o, o + n) are read through the token mechanism); the release of
   the frame and the return (IdentFrame.aj_flag_store_pi, IdentPaLib.paj_ret_at). What the call keeps
   (tcj_kept) is carried by hand from the call point: after each run from its frame_of and mem_grows, across
   the allocation from its acall_kept. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s YI16.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentCJ
YC1g YC1h YC4b YC45 YC81 YC85 IdentFrame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require write_uint_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* #[local]: this flag must not leak to files that Require this one. *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Definition A_write_uint : Z := BASE + AF_write_uint.
(* The stack the call needs, measured from the listing: the 64-byte frame (0x84160 addi sp,sp,-64), the
   32-byte alignment of sp (0x84184 andi sp,sp,-32: up to 16 more bytes), and below the aligned sp the
   ESTACK window of the side-stack frame allocation it calls at 0x841b4 (class 0). *)
Definition WRITE_UINT_STK : Z := 80 + ESTACK.
(* The digits of v (the plain model, lib/Prog/write_uint_c.v), as byte values. *)
Definition wu_bytes (v : Z) : list Z := map (fun b : byte => bv_unsigned b) (write_uint_c.write_uint_D v).
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
End f.
End d.
(* ---- the arithmetic of the digit loop ------------------------------------------------------------- *)
(* The quotient by 10 the loop computes (0x84270..0x84280): mulhu with 0xcccd0000 of v << 48, then >> 19. *)
Definition wq (e : sv) : sv := SAlu ALU_SRL (SMd M_MULHU (SAlu ALU_SLL e (SLit 48)) (SLit 3435986944)) (SLit 19).
(* The value of s3 after i digits, as the symbolic run writes it. *)
Fixpoint wx (i : nat) : sv := match i with O => SOff 11 0 | S j => SAlu ALU_ADD (wq (wx j)) (SLit 0) end.
(* The digit byte the loop stores (0x84284..0x84290): x - 10 (x / 10) with the bits of '0' set. *)
Definition wdig (e : sv) : sv := SAlu ALU_OR (SAlu ALU_SUB e (SMd M_MUL (wq e) (SLit 10))) (SLit 48).
(* The loop-1 back edge compares 9 with the low 16 bits of x (0x84270, 0x8427c). *)
Definition wlo16 (e : sv) : sv := SAlu ALU_SRL (SAlu ALU_SLL e (SLit 48)) (SLit 48).
Fixpoint wdv (v : Z) (i : nat) : Z := match i with O => v | S j => wdv v j / 10 end.
Lemma wu_div10 : forall x, 0 <= x < 65536 -> x * 52429 / 524288 = x / 10.
Proof.
intros x Hx. pose proof (Z.div_mod x 10 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 10 ltac:(lia)) as M.
assert (Hq : 0 <= x / 10 < 6554) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
symmetry. apply (Z.div_unique (x * 52429) 524288 (x / 10) (2 * (x / 10) + 52429 * (x mod 10))); [left; lia | lia].
Qed.
Lemma wu_lor48 : forall r, 0 <= r < 10 -> Z.lor r 48 = 48 + r.
Proof.
intros r Hr.
assert (H : r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7 \/ r = 8 \/ r = 9) by lia.
destruct H as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; reflexivity.
Qed.
Lemma wu_U_add0 : forall E e, U E (SAlu ALU_ADD e (SLit 0)) = U E e.
Proof.
intros E e. rewrite U_SAlu, U_SLit. cbn [zalu_raw]. rewrite (zcanon_id 0) by (unfold M64; lia).
rewrite Z.add_0_r. apply zcanon_id. apply U_range.
Qed.
Lemma wu_U_sll48 : forall E e, 0 <= U E e < 65536 -> U E (SAlu ALU_SLL e (SLit 48)) = U E e * 281474976710656.
Proof.
intros E e He. rewrite U_SAlu, U_SLit. cbn [zalu_raw]. rewrite (zcanon_id 48) by (unfold M64; lia).
change (Z.land 48 63) with 48. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 48) with 281474976710656.
apply zcanon_id. unfold M64. lia.
Qed.
Lemma wu_U_lo16 : forall E e, 0 <= U E e < 65536 -> U E (wlo16 e) = U E e.
Proof.
intros E e He. unfold wlo16. rewrite U_SAlu, (wu_U_sll48 E e He), U_SLit. cbn [zalu_raw].
rewrite (zcanon_id 48) by (unfold M64; lia). change (Z.land 48 63) with 48.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 48) with 281474976710656.
rewrite Z.div_mul by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma wu_U_q : forall E e, 0 <= U E e < 65536 -> U E (wq e) = U E e / 10.
Proof.
intros E e He. unfold wq. rewrite U_SAlu, U_SMd, (wu_U_sll48 E e He), !U_SLit. cbn [zalu_raw zmd_raw].
rewrite (zcanon_id 3435986944) by (unfold M64; lia). rewrite (zcanon_id 19) by (unfold M64; lia).
change (Z.land 19 63) with 19. change (Z.of_N 64) with 64.
rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 64) with 18446744073709551616. change (2 ^ 19) with 524288.
replace (U E e * 281474976710656 * 3435986944) with (U E e * 52429 * 18446744073709551616) by lia.
rewrite Z.div_mul by lia. rewrite (zcanon_id (U E e * 52429)) by (unfold M64; lia).
rewrite (wu_div10 (U E e) He). apply zcanon_id. unfold M64.
split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
Lemma wu_U_dig : forall E e, 0 <= U E e < 65536 -> U E (wdig e) = 48 + U E e mod 10.
Proof.
intros E e He. unfold wdig. rewrite U_SAlu, U_SAlu, U_SMd, (wu_U_q E e He), !U_SLit. cbn [zalu_raw zmd_raw].
rewrite (zcanon_id 10) by (unfold M64; lia). rewrite (zcanon_id 48) by (unfold M64; lia).
pose proof (Z.div_mod (U E e) 10 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (U E e) 10 ltac:(lia)) as M.
rewrite (zcanon_id (U E e / 10 * 10)) by (unfold M64; lia).
replace (U E e - U E e / 10 * 10) with (U E e mod 10) by lia.
rewrite (zcanon_id (U E e mod 10)) by (unfold M64; lia).
rewrite (wu_lor48 _ M). apply zcanon_id. unfold M64. lia.
Qed.
Lemma wu_U_wx : forall E v, U E (SOff 11 0) = v -> 0 <= v < 65536 ->
forall i, U E (wx i) = wdv v i /\ 0 <= wdv v i < 65536.
Proof.
intros E v Hv Hr i. induction i as [|i [IH1 IH2]]; cbn [wx wdv]; [split; [exact Hv | exact Hr]|].
rewrite wu_U_add0, wu_U_q by lia. rewrite IH1. split; [reflexivity|].
split; [apply Z.div_pos; lia | apply (Z.le_lt_trans _ (wdv v i)); [apply Z.div_le_upper_bound; lia | lia]].
Qed.
Lemma wu_U_byte : forall E v i, U E (SOff 11 0) = v -> 0 <= v < 65536 ->
U E (SExt false 8 (wdig (wx i))) = 48 + wdv v i mod 10.
Proof.
intros E v i Hv Hr. destruct (wu_U_wx E v Hv Hr i) as [H1 H2].
rewrite U_SExt, (wu_U_dig E (wx i)) by lia. rewrite H1. change (2 ^ Z.of_N 8) with 256.
pose proof (Z.mod_pos_bound (wdv v i) 10 ltac:(lia)).
rewrite Z.mod_small by lia. apply zcanon_id. unfold M64. lia.
Qed.
(* The digits: write_uint_lsd 5 v from the loop-1 exit facts. *)
Lemma wu_lsd_exit : forall k v j, 0 <= v -> (forall t, (t < j)%nat -> 10 <= wdv v t) -> wdv v j < 10 -> (j < k)%nat ->
write_uint_c.write_uint_lsd k v = map (fun t => write_uint_c.write_uint_dg (wdv v t mod 10)) (seq 0 (S j)).
Proof.
induction k as [|k IH]; intros v j Hv Hge Hlt Hjk; [lia|].
cbn [write_uint_c.write_uint_lsd]. destruct j as [|j].
- cbn [wdv] in Hlt. rewrite (proj2 (Z.ltb_lt v 10) Hlt). reflexivity.
- pose proof (Hge 0%nat ltac:(lia)) as H0. cbn [wdv] in H0. rewrite (proj2 (Z.ltb_ge v 10) H0).
  assert (Hd : forall t, wdv (v / 10) t = wdv v (S t)).
  { induction t as [|t IHt]; cbn [wdv]; [reflexivity|]. rewrite IHt. reflexivity. }
  rewrite (IH (v / 10) j); [| apply Z.div_pos; lia | intros t Ht; rewrite Hd; apply Hge; lia | rewrite Hd; exact Hlt | lia].
  change (seq 0 (S (S j))) with (0%nat :: seq 1 (S j)). rewrite map_cons. cbv beta. cbn [wdv]. f_equal.
  rewrite <- seq_shift, map_map. apply map_ext. intros t. cbv beta. rewrite Hd. reflexivity.
Qed.
Lemma wu_bytes_exit : forall v j, 0 <= v -> (forall t, (t < j)%nat -> 10 <= wdv v t) -> wdv v j < 10 -> (j < 5)%nat ->
write_uint_c.write_uint_n v = Z.of_nat (S j) /\
forall i, (i <= j)%nat -> nth i (wu_bytes v) 0 = 48 + wdv v (j - i) mod 10.
Proof.
intros v j Hv Hge Hlt Hj.
pose proof (wu_lsd_exit 5 v j Hv Hge Hlt Hj) as HL.
unfold write_uint_c.write_uint_n, wu_bytes, write_uint_c.write_uint_D. rewrite HL.
split; [rewrite length_rev, length_map, length_seq; reflexivity|].
intros i Hi. rewrite <- map_rev. rewrite map_map.
rewrite (nth_indep _ 0 ((fun t => bv_unsigned (write_uint_c.write_uint_dg (wdv v t mod 10))) 0%nat))
  by (rewrite length_map, length_rev, length_seq; lia).
rewrite (map_nth (fun t => bv_unsigned (write_uint_c.write_uint_dg (wdv v t mod 10))) (rev (seq 0 (S j))) 0%nat i).
rewrite rev_nth by (rewrite length_seq; lia). rewrite length_seq, seq_nth by lia.
cbv beta. unfold write_uint_c.write_uint_dg. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
replace (0 + (S j - S i))%nat with (j - i)%nat by lia.
pose proof (Z.mod_pos_bound (wdv v (j - i)) 10 ltac:(lia)). apply Z.mod_small. lia.
Qed.
Lemma wu_dv4 : forall v, 0 <= v < 65536 -> wdv v 4 < 10.
Proof.
intros v Hv. cbn [wdv]. rewrite !Z.div_div by lia. change (10 * 10 * 10 * 10) with 10000.
apply Z.div_lt_upper_bound; lia.
Qed.
(* ---- small facts of the side-stack frame (cgif lib/A/ACja.v) ------------------------------------- *)
Lemma wu_sp1_facts : forall x, 0 <= x -> x mod 16 = 0 ->
x - 16 <= 32 * (x / 32) <= x /\ (32 * (x / 32)) mod 32 = 0 /\ (32 * (x / 32)) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.
Lemma wu_land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = 32 * (x / 32).
Proof.
intros x Hx.
assert (E1 : 2 ^ 64 - 32 = Z.ldiff (Z.ones 64) (Z.ones 5)) by reflexivity. rewrite E1.
rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land.
rewrite Z.land_ones, Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. lia.
Qed.
Lemma wu_denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, U_SOff, Hn, unsigned_lit_small by lia.
rewrite (zcanon_id (v + c)) by (unfold M64; lia).
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite wu_land_m32 by lia. apply zcanon_id. unfold M64.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
(* The shadow address of a byte of the frame's tmp array [F + 32, F + 37) is the shadow cell F / 8 + 4. *)
Lemma wu_tmp_alias : forall E (f b s : nat) F SBv c, ew E f = Z_to_bv 64 F -> 4096 <= F -> F + 64 <= 2 ^ 47 -> F mod 64 = 0 ->
ew E b = Z_to_bv 64 SBv -> 0 <= SBv < 2 ^ 32 -> ew E s = Z_to_bv 64 (SBv + F / 8) -> 32 <= c < 40 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff f c) (SLit 3)) (SOff b 0)) = sv_denot E (SOff s 4).
Proof.
intros E f b s F SBv c Hf HF0 HF1 HF64 Hb HB Hs Hc. apply U_inj.
assert (H8 : 0 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_srl3, !U_SOff, Hf, Hb, Hs, Z.add_0_r.
rewrite !unsigned_lit_small by lia. rewrite (zcanon_id (F + c)) by (unfold M64; lia).
rewrite (zcanon_id SBv) by (unfold M64; lia).
assert (Hq : (F + c) / 8 = F / 8 + 4).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D.
  rewrite D. replace (64 * (F / 64) + c) with ((8 * (F / 64) + 4) * 8 + (c - 32)) by lia.
  replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia.
  rewrite Z.div_add_l, Z.div_mul by lia. rewrite (Z.div_small (c - 32) 8) by lia. lia. }
rewrite Hq. f_equal. lia.
Qed.
Lemma wu_ivl_disj : forall o n lo len, 0 < n -> 0 < len ->
(forall a, o <= a < o + n -> ~ (lo <= a < lo + len)) -> o + n <= lo \/ lo + len <= o.
Proof.
intros o n lo len Hn Hl H. destruct (Z_le_gt_dec (o + n) lo); [left; lia|].
destruct (Z_le_gt_dec (lo + len) o); [right; lia|]. exfalso. apply (H (Z.max o lo)); lia.
Qed.
Section d2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f2.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Section w.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF (PI := PI) B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM0 : astack_malloc_realizes SEGS B 0.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
(* ---- what the call keeps, carried from the call point ---------------------------------------------- *)
(* A byte outside every class of tcj_kept: the call may change it. *)
Definition tcj_out (lyc : alayout) (Sc : astate) (a : Z) : Prop :=
a < alloc_ceiling /\
(forall b m, In (b, m) (ablocks B lyc Sc) -> ~ (b <= a < b + req_size m)) /\
~ in_img SEGS a /\
(forall cid pos, In (cid, pos) (frames Sc) ->
~ (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8))).
Lemma wu_zone_lo : forall ly S W mem md cid pos a,
AR SEGS B ly S W mem md -> In (cid, pos) (frames S) ->
(in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
4096 <= a < alloc_ceiling.
Proof.
intros ly S W mem md cid pos a HAR Hin Hr.
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (Hf0 & Hfc & Hfh).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (fs_frame_bytes_nonneg cid) as Hnn.
pose proof (YCbq.shadow_addr_bounds (frame_addr ly cid pos) ltac:(lia)) as S1.
pose proof (YCbq.shadow_addr_bounds (frame_addr ly cid pos + fs_frame_bytes cid) ltac:(lia)) as S2.
pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) Hnn) as S3.
unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr. unfold kLowMemEnd in *. lia.
Qed.
Lemma tcj_init : forall STK lyc Sc W memc sp (E : Z -> Prop),
(forall a, sp - STK <= a < sp -> apresent (w_H W) memc a) -> tcj_kept B STK lyc Sc W memc W memc sp E.
Proof.
intros STK lyc Sc W memc sp E Hp.
split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
split; [intros; reflexivity|]. split; [intros a _ _ H; exact H|]. exact Hp.
Qed.
Lemma tcj_step : forall STK lyc Sc W memc mdc m1 m2 sp (E Zw : Z -> Prop),
AR SEGS B lyc Sc W memc mdc -> alloc_ceiling <= sp - STK -> (forall a, E a -> ~ in_img SEGS a) ->
tcj_kept B STK lyc Sc W memc W m1 sp E ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Zw a -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m1 a) ->
(forall a, apresent (w_H W) m1 a -> apresent (w_H W) m2 a) ->
(forall a, Zw a -> (sp - STK <= a < sp) \/ E a \/ tcj_out lyc Sc a) ->
tcj_kept B STK lyc Sc W memc W m2 sp E.
Proof.
intros STK lyc Sc W memc mdc m1 m2 sp E Zw HAR Hc HEi (T1 & T2 & T3 & T4 & T5 & T6) HK HP HZ.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof pa_segs_low as Hsegs.
split.
{ intros a Ha Hw He. rewrite (HK a ltac:(lia)); [apply T1; assumption|].
  intros Hz. destruct (HZ a Hz) as [H|[H|(H & _)]]; [exact (Hw H) | exact (He H) | lia]. }
split.
{ intros b m i Hin Hi He.
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hin) as (_ & H4096 & Hce & _).
  rewrite (HK (b + i) ltac:(lia)); [apply (T2 b m i); assumption|].
  intros Hz. destruct (HZ _ Hz) as [H|[H|(_ & Hb & _)]]; [lia | exact (He H) | exact (Hb b m Hin ltac:(lia))]. }
split.
{ intros a Hi Hns Her. pose proof (Hsegs a Hi) as Hlo. unfold kLowMemEnd in Hlo.
  rewrite (HK a ltac:(lia)); [apply T3; assumption|].
  intros Hz. destruct (HZ _ Hz) as [H|[H|(_ & _ & Hni & _)]]; [lia | exact (HEi a H Hi) | exact (Hni Hi)]. }
split.
{ intros cid pos a Hin Hr He. pose proof (wu_zone_lo lyc Sc W memc mdc cid pos a HAR Hin Hr) as Hz0.
  rewrite (HK a ltac:(lia)); [apply (T4 cid pos a); assumption|].
  intros Hz. destruct (HZ _ Hz) as [H|[H|(_ & _ & _ & Hf)]]; [lia | exact (He H) | exact (Hf cid pos Hin Hr)]. }
split.
{ intros a Ha Hw Hp. apply HP. apply (T5 a); assumption. }
intros a Ha. apply HP. apply T6. exact Ha.
Qed.
Lemma tcj_acall : forall STK lyc Sc W memc m1 m2 sp slo shi (E : Z -> Prop),
alloc_ceiling <= sp - STK -> sp - STK <= slo -> shi <= sp -> sp <= 2 ^ 64 ->
tcj_kept B STK lyc Sc W memc W m1 sp E ->
acall_kept SEGS B lyc Sc W m1 W m2 slo shi (fun _ => False) ->
tcj_kept B STK lyc Sc W memc W m2 sp E.
Proof.
intros STK lyc Sc W memc m1 m2 sp slo shi E Hc Hlo Hhi H64 (T1 & T2 & T3 & T4 & T5 & T6) (K1 & K2 & K3 & K4 & K5 & K6).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [intros a Ha Hw He; rewrite (K1 a Ha ltac:(lia)); apply T1; assumption|].
split; [intros b m i Hin Hi He; rewrite (K2 b m i Hin Hi ltac:(tauto)); apply (T2 b m i); assumption|].
split; [intros a Hi Hns Her; rewrite (K3 a Hi Hns Her); apply (T3 a); assumption|].
split; [intros cid pos a Hin Hr He; rewrite (K4 cid pos a Hin Hr ltac:(tauto)); apply (T4 cid pos a); assumption|].
split; [intros a Ha Hw Hp; apply (K5 a Ha ltac:(lia)); apply (T5 a); assumption|].
intros a Ha. destruct (Z_lt_le_dec a slo) as [H1|H1]; [|destruct (Z_lt_le_dec a shi) as [H2|H2]].
- apply (K5 a ltac:(lia) ltac:(lia)). apply T6. exact Ha.
- apply K6. lia.
- apply (K5 a ltac:(lia) ltac:(lia)). apply T6. exact Ha.
Qed.
Lemma tcj_out_frame : forall lyc Sc S2 W m md pos a,
AR SEGS B lyc S2 W m md -> frames S2 = (0, pos) :: frames Sc -> ablocks B lyc S2 = ablocks B lyc Sc ->
(frame_addr lyc 0 pos <= a < frame_addr lyc 0 pos + 64 \/
 shadow_addr (frame_addr lyc 0 pos) <= a < shadow_addr (frame_addr lyc 0 pos) + 8 \/ a = flag_addr lyc 0 pos) ->
tcj_out lyc Sc a.
Proof.
intros lyc Sc S2 W m md pos a HAR Hfrs Eab Ha.
assert (Hin0 : In (0, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (Hsc : forall c p, In (c, p) (frames Sc) -> In (c, p) (frames S2)) by (intros c p H; rewrite Hfrs; right; exact H).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof pa_segs_low as Hsegs.
destruct Ha as [Ha | [Ha | Ha]].
3: { subst a. destruct (FFL lyc S2 W m md 0 pos HAR Hin0) as (Hp & Hown & (Happ & Himg) & (H4096 & Hz2 & Hce)).
  split; [exact Hce|]. split.
  { intros b mm Hb Hr. rewrite <- Eab in Hb.
    destruct (al_blocks _ _ LAWS lyc S2 W m md b mm HAR Hb) as (_ & _ & _ & _ & Hbb & _).
    exact (proj2 (Hbb _ Hr) Hown). }
  split; [exact Himg|].
  intros cid p Hin [Hr | Hr]; destruct (al_frames _ _ LAWS lyc S2 W m md cid p HAR (Hsc _ _ Hin)) as (_ & _ & Hfb & Hfs).
  - unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. exact (proj2 (Hfb _ Hr) Hown).
  - unfold in_zr in Hr. cbn [fst snd] in Hr.
    specialize (Hfs (flag_addr lyc 0 pos - shadow_addr (frame_addr lyc cid p)) ltac:(lia)).
    replace (shadow_addr (frame_addr lyc cid p) + (flag_addr lyc 0 pos - shadow_addr (frame_addr lyc cid p)))
      with (flag_addr lyc 0 pos) in Hfs by lia. exact (proj2 Hfs Hown). }
all: assert (Hz : in_zr a (frame_rng lyc (0, pos)) \/ in_zr a (shadow_addr (frame_addr lyc 0 pos), fs_frame_bytes 0 / 8))
  by (unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 0) with 64; change (64 / 8) with 8; lia).
all: destruct (frame_zone SEGS B LAWS lyc S2 W m md 0 pos a HAR Hin0 Hz) as (Hce & Hw).
all: split; [exact Hce|].
all: split; [intros b mm Hb Hr; rewrite <- Eab in Hb;
  apply (block_not_frame_zone SEGS B LAWS lyc S2 W m md b mm (a - b) 0 pos HAR Hb Hin0); [lia|];
  replace (b + (a - b)) with a by lia; exact Hz|].
all: split; [intros Hi; pose proof (Hsegs a Hi) as Hl; destruct Hw as [(Hr & _) | Hr];
  [exact (frm_img SEGS B LAWS lyc S2 W m md 0 pos a HAR Hin0 Hr Hi) | unfold kLowMemEnd in *; lia]|].
all: intros cid p Hin Hz'; apply in_split in Hin as (l1 & l2 & El);
  apply (frames_zone_disj SEGS B LAWS lyc S2 W m md (0, pos) (cid, p) [] l1 l2 a HAR);
  [rewrite Hfrs, El; reflexivity | exact Hz | exact Hz'].
Qed.
Lemma wu_tdst_where : forall lyc Sc W memc mdc o n a,
AR SEGS B lyc Sc W memc mdc -> tdst_ok B lyc Sc o n -> o <= a < o + n ->
4096 <= a < alloc_ceiling /\ app_addr a /\ ~ in_img SEGS a.
Proof.
intros lyc Sc W memc mdc o n a HAR HDST Ha.
destruct (HDST a Ha) as [(b & m & Hin & Hr) | (cid & pos & Hin & Hr)].
- destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hin) as (_ & H4096 & Hce & Happ & _).
  split; [lia|]. split; [exact (in_app_addr _ _ _ Happ Hr)|]. exact (blk_img SEGS B LAWS lyc Sc W memc mdc b m a HAR Hin Hr).
- unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
  destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (H4096 & Hce & Happ).
  split; [lia|]. split; [exact (in_app_addr _ _ _ Happ Hr)|]. exact (frm_img SEGS B LAWS lyc Sc W memc mdc cid pos a HAR Hin Hr).
Qed.
Lemma wu_tdst_out : forall lyc Sc o n a y, tdst_ok B lyc Sc o n -> o <= a < o + n -> tcj_out lyc Sc y -> a <> y.
Proof.
intros lyc Sc o n a y HDST Ha (_ & Hb & _ & Hf) ->.
destruct (HDST y Ha) as [(b & m & Hin & Hr) | (cid & pos & Hin & Hr)]; [exact (Hb b m Hin Hr) | exact (Hf cid pos Hin (or_introl Hr))].
Qed.
Lemma wu_ra_out : forall STK lyc Sc W memc mdc S2 m md sp o n,
AR SEGS B lyc Sc W memc mdc -> AR SEGS B lyc S2 W m md -> ablocks B lyc S2 = ablocks B lyc Sc ->
tdst_ok B lyc Sc o n ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF o n ->
tcj_kept B STK lyc Sc W memc W m sp (fun a => o <= a < o + n) ->
range_addressable (aview SEGS (w_H W) m) SHADOW_OFF o n.
Proof.
intros STK lyc Sc W memc mdc S2 m md sp o n HARc HAR2 Eab HDST HRA (_ & _ & _ & T4 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
intros x Hx. destruct (HDST x Hx) as [(b & mm & Hb & Hr) | (cid & pos & Hin & Hr)].
- rewrite <- Eab in Hb.
  assert (H1 : range_addressable (aview SEGS (w_H W) m) SHADOW_OFF x 1)
    by (apply (range_addressable_of_block SEGS B LAWS lyc S2 W m md b mm x 1 HAR2 Hb); lia).
  exact (H1 x ltac:(lia)).
- destruct (HRA x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok]. rewrite <- Hs.
  unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
  destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HARc Hin) as (Hf0 & Hfc & Hfapp).
  destruct (frame_al64 SEGS B lyc Sc W memc mdc cid pos HARc Hin) as (H64 & Hb64 & Hb64').
  set (F := frame_addr lyc cid pos) in *. set (L := fs_frame_bytes cid) in *.
  pose proof (Z.div_mod F 64 ltac:(lia)) as DF. pose proof (Z.div_mod L 64 ltac:(lia)) as DL.
  rewrite H64, Z.add_0_r in DF. rewrite Hb64, Z.add_0_r in DL.
  assert (HF8 : F / 8 = 8 * (F / 64)) by (rewrite DF at 1; replace (64 * (F / 64)) with (8 * (F / 64) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
  assert (HL8 : L / 8 = 8 * (L / 64)) by (rewrite DL at 1; replace (64 * (L / 64)) with (8 * (L / 64) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
  assert (Hxs : F / 8 <= x / 8 < F / 8 + L / 8).
  { split; [apply Z.div_le_mono; lia|]. rewrite HF8, HL8. apply Z.div_lt_upper_bound; lia. }
  assert (Hsx : kLowMemEnd <= shadow_of_addr SHADOW_OFF x < kHighShadowEnd).
  { unfold shadow_of_addr, SHADOW_OFF, kLowMemEnd, kHighShadowEnd. split; [pose proof (Z.div_pos x 8); lia|].
    assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. }
  apply (T4 cid pos (shadow_of_addr SHADOW_OFF x) Hin).
  + right. unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd]. fold F L. lia.
  + intros Hxo. destruct (wu_tdst_where lyc Sc W memc mdc o n _ HARc HDST Hxo) as (_ & Happ & _).
    unfold app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowMemEnd, kHighShadowEnd in *. lia.
Qed.
Lemma awr_frame0 : forall STK sp0 FP bl0 blc ly own pos a,
(frame_addr ly 0 pos <= a < frame_addr ly 0 pos + 64 \/
 shadow_addr (frame_addr ly 0 pos) <= a < shadow_addr (frame_addr ly 0 pos) + 8) ->
awr_byte STK sp0 FP bl0 blc ly ((0, pos) :: own) a.
Proof.
intros STK sp0 FP bl0 blc ly own pos a Ha. right; right; right. exists 0, pos. split; [left; reflexivity|].
unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 0) with 64. change (64 / 8) with 8. exact Ha.
Qed.
Lemma awr_byte_cons_own : forall STK sp0 FP bl0 blc blc' ly own f a,
blc' = blc -> awr_byte STK sp0 FP bl0 blc ly own a -> awr_byte STK sp0 FP bl0 blc' ly (f :: own) a.
Proof.
intros STK sp0 FP bl0 blc blc' ly own f a -> [H | [H | [H | (cid & pos & Hin & Hr)]]];
[left | right; left | right; right; left | right; right; right; exists cid, pos; split; [right; exact Hin | exact Hr]]; exact H.
Qed.
Lemma subregion_trim_ro : forall r lo, r_lo r <= lo ->
subregion (YP09.mkRegion (YP09.r_base r) lo (YP09.r_hi r) 0 0 (List.filter (fun c => lo <=? YP09.c_off c) (YP09.r_chunks r))) r.
Proof.
intros r lo Hlo. unfold subregion. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [left; lia|].
intros c Hc. apply List.filter_In in Hc. exact (proj1 Hc).
Qed.
Definition wu_trim (lo : Z) (r : YP09.region) : YP09.region :=
YP09.mkRegion (YP09.r_base r) lo (YP09.r_hi r) 0 0 (List.filter (fun c => lo <=? YP09.c_off c) (YP09.r_chunks r)).
Definition wu_facts0 : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (11%nat, mkAF 0 65535 0); (32%nat, mkAF SB SB 0); (33%nat, mkAF IMG_LO IMG_TOP 2) ] [] [].
Definition wu_ss0 : sstate :=
mkSS AF_write_uint sr_atoms [stack_region 64; got_regionP; bcell_regionP 32; uar_got_regionP 33; uar_cell_regionP 33] None wu_facts0.
Definition wu_extra : list word := [Z_to_bv 64 SB; Z_to_bv 64 (as_uar_cell B)].
Definition wu_box (P : Prop) : Prop := P.
Definition wu_ro (r : YP09.region) : YP09.region :=
YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) 0 0 (YP09.r_chunks r).
Lemma submem_map_ro : forall rs, submem (map wu_ro rs) rs.
Proof.
induction rs as [|r rs IH]; cbn [map]; [apply submem_nil|].
apply submem_keep; [|exact IH]. unfold subregion, wu_ro. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [left; lia|]. intros c Hc; exact Hc.
Qed.
Ltac wu_rreg_by HS r v pf H :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?Ex ?ss (restrict ?Hh ?ms) =>
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in
  let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
  assert (H : getr rg r = v) by (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ss ms r HS) _); change (sv_denot Ex e = v); exact pf)
| st_ok ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in
  let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
  assert (H : getr rg r = v) by (refine (eq_trans (st_ok_restrict_reg segs Hh Ex ss ms r HS) _); change (sv_denot Ex e = v); exact pf)
end.
Ltac wu_norm_ss HS := lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
Ltac wu_awr_norm := lazymatch goal with |- awr_ok ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?lyx ?ownx =>
  let rs' := eval vm_compute in rsx in change (awr_ok Ex rs' stkx spx fpx b0x bcx lyx ownx) end.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUN := paj_run B LAWS.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_ident) (PI := PI).
Theorem pb_write_uint : twrite_uint_spec B.
Proof.
unfold twrite_uint_spec.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch o v
HJ Hra Hra4 Hgp Htp Hch Hal Hlo Hhi H10 H11 Hv HWR HDST HRA Hfr.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : WRITE_UINT_STK = 4176) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
rewrite HSTK in Hlo.
pose proof HJ as (HARc & Hlyc & _ & _ & _ & Hfrsc & _ & _ & _ & _ & _ & _ & _ & Hpresc & HST & _).
pose proof HST as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (HSPlo : alloc_ceiling + 4176 <= spZ regs) by lia.
assert (HSPhi : spZ regs <= 2 ^ 47) by lia.
set (n := write_uint_c.write_uint_n v) in *.
assert (HEimg : forall a, o <= a < o + n -> ~ in_img SEGS a)
  by (intros a Ha; exact (proj2 (proj2 (wu_tdst_where lyc Sc W memc mdc o n a HARc HDST Ha)))).
destruct (al_const _ _ LAWS lyc Sc W memc mdc HARc) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL), <- SB_SHADOW_OFF in Kcell.
rewrite (palf_got_uar B TLF) in Kguar.
pose proof (pa_obj_img 30 ltac:(lia)) as HcellR. pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
pose proof (pa_obj_img 0 ltac:(lia)) as HguarR.
pose proof (palf_uar_img B TLF) as HuarR. pose proof (palf_uar_al B TLF) as Huaral. pose proof (palf_sep B TLF) as Hsep.
cbn [zseps zseps_from fst snd] in Hsep.
remember (Eimg (Ereg regs wu_extra)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (AGE : env_agree 32 (Ereg regs wu_extra) E)
  by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs r)
  by (intros nn r Hnn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hnn).
assert (ER : regs_ok E sr_atoms regs) by (rewrite HE; apply regs_ok_Eimg_Ereg).
assert (E1 : ew E 1 = getr regs 1) by exact (EE 1%nat 1%bv eq_refl).
assert (E2 : ew E 2 = getr regs 2) by exact (EE 2%nat 2%bv eq_refl).
assert (E3 : ew E 3 = w64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl); exact Hgp).
assert (E4 : ew E 4 = w64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl); exact Htp).
assert (E10 : ew E 10 = Z_to_bv 64 o) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 v) by (rewrite (EE 11%nat 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Eg0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (apply (img_env_atomP E (A_OBJ 0) HEI); unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eg1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (apply (img_env_atomP E (A_OBJ 1) HEI); unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eg30 : ew E (A_OBJ 30) = Z_to_bv 64 (VAL (A_OBJ 30))) by (apply (img_env_atomP E (A_OBJ 30) HEI); unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HE.
pose proof (pa_val_range (A_OBJ 0)) as Rg0. pose proof (pa_val_range (A_OBJ 1)) as Rg1. pose proof (pa_val_range (A_OBJ 30)) as Rg30.
assert (HS : st_ok_pi SEGS VAL E wu_ss0 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_write_uint)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold wu_ss0. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - unfold stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros a Ha. apply (apresent_writable SEGS). apply Hpresc. lia.
    + rewrite Eg1, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 30) 0) (VAL (A_OBJ 30)));
      [cbn [sv_denot]; rewrite Eg30, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
    + rewrite Eg30, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 30)) 0 8 (SOff 32 0) SB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
    + rewrite Eg0, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff 33 0) (as_uar_cell B));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kguar).
    + rewrite E33, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) memc _ _ Kuar).
  - apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite Usp, Eg0, Eg1, Eg30, E33, !unsigned_lit_small by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [wu_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E11, E32, E33, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SB; lia. }
clear Hsep.
unfold cfg_at, A_write_uint. change (w64 (BASE + AF_write_uint)) with (Z_to_bv 64 (BASE + AF_write_uint)).
(* ---- entry to the frame allocation at 0x841b4 -------------------------------------------------- *)
paj_run_shc RUNP RUNC HS HJ.
{ wu_awr_norm.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
  [reflexivity | rewrite Usp; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]). apply awr_ok_nil. }
lazymatch goal with HG : mem_grows (mrestrict _ memc) (mrestrict _ (ms_mem ?msA)), HFr : frame_of _ _ (mrestrict _ memc) _ |- _ =>
assert (TK1 : tcj_kept B 4176 lyc Sc W memc W (ms_mem msA) (spZ regs) (fun a => o <= a < o + n));
[ apply (tcj_step 4176 lyc Sc W memc mdc memc (ms_mem msA) (spZ regs) _ (fun x => spZ regs - 64 <= x < spZ regs) HARc ltac:(lia) HEimg
    (tcj_init 4176 lyc Sc W memc (spZ regs) _ ltac:(intros a Ha; apply Hpresc; lia)));
  [ intros a Ha Hn; apply (kept_of_frame E _ (w_H W) memc (ms_mem msA) (fun x => spZ regs - 64 <= x < spZ regs) HFr); [|exact Ha|exact Hn];
    intros bb wlo whi aa Hin Hr; unfold wu_ss0 in Hin;
    cbn [ss_mem windows map stack_region got_regionP bcell_regionP uar_got_regionP uar_cell_regionP YP09.r_base YP09.r_wlo YP09.r_whi] in Hin;
    destruct Hin as [Hq | [Hq | [Hq | [Hq | [Hq | []]]]]]; injection Hq as <- <- <-; cbn [base_val] in Hr;
    [rewrite Usp in Hr; lia | lia | lia | lia | lia]
  | intros a Hp; eapply apresent_grows; [exact HG | exact Hp]
  | intros a Ha; left; lia ]
| clear HF HFr HG ] end.
(* ---- the side-stack frame allocation (class 0) ------------------------------------------------------ *)
set (SP1 := 32 * ((spZ regs - 64) / 32)).
destruct (wu_sp1_facts (spZ regs - 64) ltac:(lia) ltac:(rewrite Zminus_mod, Hal; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
fold SP1 in Hsp1r, Hsp1al, Hsp1al16.
wu_rreg_by HS (2%bv : bv 5) (Z_to_bv 64 SP1)
  (wu_denot_and_m32 E 2 (spZ regs) (-64) ltac:(rewrite E2; symmetry; apply Z_to_bv_bv_unsigned) ltac:(lia) ltac:(lia) ltac:(lia)) R2.
prreg HS (1%bv : bv 5) R1. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
pose proof (count_cid_le_length 0 (frames Sc)) as Hcnt.
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msA) |- _ =>
pmkst HS; rewrite (palf_sm0 B TLF);
eapply SRr_bind;
[ eapply (aj_stack_malloc_atS SEGS B LAWS pa_segs_low (pal_env B TL) ML SMP 0 ASM0 ltac:(lia) W (ms_regs msA) (ms_mem msA)
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (SP1 - sp0) (Z_to_bv 64 (BASE + 15020)) HJ);
  [ unfold spZ at 1; rewrite R2, unsigned_lit_small by lia; lia
  | rewrite Zminus_mod, Hsp1al16, Hsp0al; reflexivity
  | lia
  | rewrite Hes; lia
  | rewrite R3; exact E3
  | rewrite R4; exact E4
  | exact R1
  | apply ret_ok_codeptr_v; [lia | reflexivity]
  | change (fs_frames 0) with 16384; lia ]
| ];
cbv beta;
let W2 := fresh "W2" in let c2 := fresh "c2" in
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HJs & (fS2 & ES2));
rewrite Hes in HK;
assert (TK2 : tcj_kept B 4176 lyc Sc W memc W mem2 (spZ regs) (fun a => o <= a < o + n))
  by (refine (tcj_acall 4176 lyc Sc W memc (ms_mem msA) mem2 (spZ regs) _ _ _ _ _ _ _ TK1 HK); lia);
jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W) mem2) HP2 [0%nat] HS2;
match type of HS2 with ?Q -> _ => assert (HQ : Q); [| specialize (HS2 HQ); clear HQ] end;
[ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil;
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha;
  [ apply (mbyte_of_aview SEGS); destruct HK as (K1 & _); apply K1; lia
  | apply (writable_kept (w_H W) _ mem2 a); intros Hp; destruct HK as (_ & _ & _ & _ & K5 & _); apply K5; [lia | lia | exact Hp] ]
| clear HS TK1 R1 R2 R3 R4 ]
end.
rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
(* ---- the state after the allocation: the frame F, its shadow, the flag word, sp1 -------------------- *)
pose proof (proj1 HJ2) as HAR2.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
assert (Hfin2 : In (0, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 pos HAR2 Hfin2) as (HFal32 & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 pos HAR2 Hfin2) as (HF4096 & HFceil & _).
destruct (frame_al64 SEGS B _ _ _ _ _ 0 pos HAR2 Hfin2) as (HF64 & _ & _).
destruct (FFL lyc S2 W mem2 md2 0 pos HAR2 Hfin2) as (HFLpres & HFLown & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLce)).
change (fs_frame_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
set (F := frame_addr lyc 0 pos) in *. set (FL := flag_addr lyc 0 pos) in *.
unfold shadow_addr in HFSpres. rewrite <- SB_SHADOW_OFF in HFSpres.
unfold zero_shadow, shadow_of_addr in Hz. rewrite <- SB_SHADOW_OFF in Hz. change (64 / 8) with 8 in Hz.
assert (HF8 : F / 8 = 8 * (F / 64)).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D at 1.
  replace (64 * (F / 64)) with (8 * (F / 64) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
pose proof (Z.div_mod F 8 ltac:(lia)) as DF8. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as MF8.
assert (HF8r : 512 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (ss_mem ssx) in
  lazymatch rs with [?r0] =>
  pose proof (st_ok_pi_submem Ex ssx msx [wu_trim (-48) r0] HS
    ltac:(cbn [ss_mem]; apply submem_keep; [unfold wu_trim; apply subregion_trim_ro; cbn; lia | apply submem_nil])
    ltac:(vm_compute; reflexivity)) as HS3 end end.
clear HS. rename HS3 into HS. wu_norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  pose proof (st_ok_pi_havoc_hi 528 Ex ssx msx [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8); Z_to_bv 64 SP1] HS
    ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS.
remember (havoc (havoc E 512 (map (getr regs2) CLOB)) 528 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8); Z_to_bv 64 SP1]) as Ev2 eqn:HE2.
assert (HEI2 : img_env VAL A_LIM Ev2)
  by (rewrite HE2; apply img_env_havoc_hi; [apply img_env_havoc_hi; [exact HEI | cbv; lia] | cbv; lia]).
assert (AG2 : forall nn, (nn < 512)%nat -> ew Ev2 nn = ew E nn) by (intros nn Hnn; rewrite HE2, !ew_havoc_old by lia; reflexivity).
assert (X516 : ew Ev2 516 = Z_to_bv 64 F).
{ rewrite HE2, ew_havoc_old by lia. change 516%nat with (512 + 4)%nat.
  rewrite (ew_havoc_new E 512 _ 4 (Z_to_bv 64 0)) by (cbn; lia). cbn [nth map CLOB]. rewrite Ha0. reflexivity. }
assert (X528 : ew Ev2 528 = Z_to_bv 64 FL)
  by (rewrite HE2; change 528%nat with (528 + 0)%nat; rewrite (ew_havoc_new _ 528 _ 0 (Z_to_bv 64 0)) by (cbn; lia); reflexivity).
assert (X529 : ew Ev2 529 = Z_to_bv 64 (SB + F / 8))
  by (rewrite HE2; change 529%nat with (528 + 1)%nat; rewrite (ew_havoc_new _ 528 _ 1 (Z_to_bv 64 0)) by (cbn; lia); reflexivity).
assert (X530 : ew Ev2 530 = Z_to_bv 64 SP1)
  by (rewrite HE2; change 530%nat with (528 + 2)%nat; rewrite (ew_havoc_new _ 528 _ 2 (Z_to_bv 64 0)) by (cbn; lia); reflexivity).
assert (Usp2 : bv_unsigned (ew Ev2 2) = spZ regs) by (rewrite AG2 by lia; exact Usp).
assert (X2 : ew Ev2 2 = Z_to_bv 64 (spZ regs)) by (rewrite AG2 by lia; rewrite E2; symmetry; apply Z_to_bv_bv_unsigned).
assert (X10 : ew Ev2 10 = Z_to_bv 64 o) by (rewrite AG2 by lia; exact E10).
assert (X11 : ew Ev2 11 = Z_to_bv 64 v) by (rewrite AG2 by lia; exact E11).
assert (X32 : ew Ev2 32 = Z_to_bv 64 SB) by (rewrite AG2 by lia; exact E32).
assert (AGv2 : env_agree 32 (Ereg regs wu_extra) Ev2).
{ eapply env_agree_trans; [exact AGE|]. rewrite HE2.
  apply env_agree_havoc_ge; [lia|]. apply env_agree_havoc_ge; [lia|]. apply env_agree_refl. }
clear HE2.
wu_rreg_by HS (2%bv : bv 5) (Z_to_bv 64 SP1) (wu_denot_and_m32 Ev2 2 (spZ regs) (-64) X2 ltac:(lia) ltac:(lia) ltac:(lia)) Q2.
wu_rreg_by HS (9%bv : bv 5) (Z_to_bv 64 SP1)
  (eq_trans (U_inj Ev2 _ _ (wu_U_add0 Ev2 _)) (wu_denot_and_m32 Ev2 2 (spZ regs) (-64) X2 ltac:(lia) ltac:(lia) ltac:(lia))) Q9.
assert (D530 : sv_denot Ev2 (SOff 530 0) = Z_to_bv 64 SP1) by (cbn [sv_denot]; rewrite X530, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp Ex ssx msx (2%bv : bv 5) (SOff 530 0) HS ltac:(vm_compute; reflexivity)
    ltac:(cbn [ms_regs restrict mkst]; rewrite D530; symmetry; exact Q2)) as HS3 end.
clear HS. rename HS3 into HS. wu_norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp Ex ssx msx (9%bv : bv 5) (SOff 530 0) HS ltac:(vm_compute; reflexivity)
    ltac:(cbn [ms_regs restrict mkst]; rewrite D530; symmetry; exact Q9)) as HS3 end.
clear HS. rename HS3 into HS. wu_norm_ss HS.
assert (F516 : afact_ok Ev2 516 (mkAF 4096 140737479966720 6))
  by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite X516, unsigned_lit_small by lia; change (2 ^ 6) with 64; lia).
assert (F528 : afact_ok Ev2 528 (mkAF 4096 140737479966720 0))
  by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite X528, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
assert (F529 : afact_ok Ev2 529 (mkAF (SB + 512) (SB + 17592186044416) 3)).
{ unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite X529, unsigned_lit_small by (unfold SB; lia). change (2 ^ 3) with 8.
  split; [unfold SB; lia|]. split; [|lia].
  replace (SB + F / 8) with ((268431360 + F / 64) * 8) by (unfold SB; lia). apply Z_mod_mult. }
assert (F530 : afact_ok Ev2 530 (mkAF (2 ^ 46 - 128) (2 ^ 47) 5))
  by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite X530, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  pose proof (st_ok_pi_add_fact Ex _ msx 530 _ (st_ok_pi_add_fact Ex _ msx 529 _
    (st_ok_pi_add_fact Ex _ msx 528 _ (st_ok_pi_add_fact Ex ssx msx 516 _ HS F516) F528) F529) F530) as HS3 end.
clear HS. rename HS3 into HS. wu_norm_ss HS.
assert (HSBr : 0 <= SB < 2 ^ 32) by (unfold SB; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  pose proof (st_ok_pi_add_alias Ex ssx msx _ _ HS (shadow_decl_ok Ex 516 32 529 F SB X516 ltac:(lia) X32 X529)) as HS3 end.
clear HS. rename HS3 into HS. wu_norm_ss HS.
Ltac wu_tmp_alias_add HS c :=
  lazymatch goal with X516 : ew ?Ex 516 = _, X32 : ew _ 32 = _, X529 : ew _ 529 = _, HF64 : _ mod 64 = 0,
    HSBr : 0 <= SB < _ |- _ =>
  lazymatch type of HS with st_ok_pi _ _ Ex ?ssx ?msx =>
    let HS3 := fresh "HS3" in
    pose proof (st_ok_pi_add_alias Ex ssx msx _ _ HS (wu_tmp_alias Ex 516 32 529 _ SB c X516 ltac:(lia) ltac:(lia) HF64 X32 HSBr X529 ltac:(lia))) as HS3;
    clear HS; rename HS3 into HS; wu_norm_ss HS end end.
wu_tmp_alias_add HS 36. wu_tmp_alias_add HS 35. wu_tmp_alias_add HS 34. wu_tmp_alias_add HS 33. wu_tmp_alias_add HS 32.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  pose proof (st_ok_pi_add_region Ex ssx msx (YP09.mkRegion (Some 530%nat) 0 16 8 16 []) HS eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
      rewrite X530, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
      intros a Ha; apply (apresent_writable SEGS); apply Hpres2; lia)
    ltac:(cbn [ss_mem all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
      rewrite X530, Usp2, unsigned_lit_small by lia; split; [lia | exact I])) as HS3 end.
clear HS. rename HS3 into HS. wu_norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  pose proof (st_ok_pi_add_region Ex ssx msx (YP09.mkRegion (Some 516%nat) 0 64 0 64 [YP09.mkChunk 56 (CVal 8 (SOff 528 0))]) HS eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
      rewrite X516, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
      [ intros a Ha; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + a) ltac:(lia)))
      | apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Ex _ F 56 8 (SOff 528 0) FL);
        [ cbn [sv_denot]; rewrite X528, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside
        | replace (F + 56) with (F + 64 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag) ] ])
    ltac:(cbn [ss_mem all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
      rewrite X516, X530, Usp2, !unsigned_lit_small by lia; split; [lia | split; [lia | exact I]])) as HS3 end.
clear HS. rename HS3 into HS. wu_norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  pose proof (st_ok_pi_add_region Ex ssx msx (YP09.mkRegion (Some 529%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SLit 0))]) HS eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
      rewrite X529, unsigned_lit_small by (unfold SB; lia); split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
      [ intros a Ha; apply (apresent_writable SEGS); apply (proj1 (HFSpres a ltac:(lia)))
      | apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Ex _ (SB + F / 8) 0 8 (SLit 0) 0);
        [ reflexivity | zside | zside | rewrite Z.add_0_r; apply val_mem_zero8; intros i Hi; apply Hz; lia ] ])
    ltac:(cbn [ss_mem all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
      rewrite X529, X516, X530, Usp2, !unsigned_lit_small by (unfold SB; lia);
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in HFapp |- *;
      split; [lia | split; [lia | split; [lia | exact I]]])) as HS3 end.
clear HS. rename HS3 into HS. wu_norm_ss HS.
assert (U516 : bv_unsigned (ew Ev2 516) = F) by (rewrite X516; apply unsigned_lit_small; lia).
assert (U528 : bv_unsigned (ew Ev2 528) = FL) by (rewrite X528; apply unsigned_lit_small; lia).
assert (U529 : bv_unsigned (ew Ev2 529) = SB + F / 8) by (rewrite X529; apply unsigned_lit_small; unfold SB; lia).
assert (U530 : bv_unsigned (ew Ev2 530) = SP1) by (rewrite X530; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew Ev2 10) = o).
{ rewrite X10. apply unsigned_lit_small.
  assert (Hn1 : 1 <= n) by (unfold n, write_uint_c.write_uint_n, write_uint_c.write_uint_D; rewrite length_rev;
    cbn [write_uint_c.write_uint_lsd length]; lia).
  destruct (wu_tdst_where lyc Sc W memc mdc o n o HARc HDST ltac:(lia)) as (Ho & _). lia. }
assert (U11 : U Ev2 (SOff 11 0) = v) by (apply U_atom; [exact X11 | lia]).
set (Zw := fun a => (spZ regs - 4176 <= a < spZ regs) \/ (o <= a < o + n) \/
  (F <= a < F + 64 \/ SB + F / 8 <= a < SB + F / 8 + 8 \/ a = FL)).
assert (HZ : forall a, Zw a -> (spZ regs - 4176 <= a < spZ regs) \/ (o <= a < o + n) \/ tcj_out lyc Sc a).
{ intros a [Ha | [Ha | Ha]]; [left; exact Ha | right; left; exact Ha | right; right].
  apply (tcj_out_frame lyc Sc S2 W mem2 md2 pos a HAR2 Hfrs2 Eab).
  unfold shadow_addr. rewrite <- SB_SHADOW_OFF. exact Ha. }
assert (Hn1 : 1 <= n) by (unfold n, write_uint_c.write_uint_n, write_uint_c.write_uint_D; rewrite length_rev;
  cbn [write_uint_c.write_uint_lsd length]; lia).
destruct (wu_tdst_where lyc Sc W memc mdc o n o HARc HDST ltac:(lia)) as (Ho4096 & _).
destruct (wu_tdst_where lyc Sc W memc mdc o n (o + n - 1) HARc HDST ltac:(lia)) as ((_ & Hoce) & _).
assert (F10 : afact_ok Ev2 10 (mkAF 4096 (2 ^ 47 - 8) 0))
  by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U10, Z.pow_0_r, Z.mod_1_r; lia).
assert (UB32 : U Ev2 (SOff 32 0) = SB) by (apply U_atom; [exact X32 | unfold SB; lia]).
assert (UO10 : U Ev2 (SOff 10 0) = o) by (apply U_atom; [exact X10 | lia]).
assert (HFRo : o + n <= F \/ F + 64 <= o).
{ apply wu_ivl_disj; [lia | lia |]. intros a Ha Hf.
  exact (wu_tdst_out lyc Sc o n a a HDST Ha (tcj_out_frame lyc Sc S2 W mem2 md2 pos a HAR2 Hfrs2 Eab (or_introl Hf)) eq_refl). }
assert (HFLo : o + n <= FL \/ FL + 1 <= o).
{ apply wu_ivl_disj; [lia | lia |]. intros a Ha Hf. assert (a = FL) by lia. subst a.
  exact (wu_tdst_out lyc Sc o n FL FL HDST Ha (tcj_out_frame lyc Sc S2 W mem2 md2 pos FL HAR2 Hfrs2 Eab (or_intror (or_intror eq_refl))) eq_refl). }
assert (HSHo : o + n <= SB + F / 8 \/ SB + F / 8 + 8 <= o).
{ apply wu_ivl_disj; [lia | lia |]. intros a Ha Hs. destruct (wu_tdst_where lyc Sc W memc mdc o n a HARc HDST Ha) as (_ & Happ & _).
  unfold app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *. lia. }
assert (HFLf : FL + 1 <= F \/ F + 64 <= FL).
{ destruct (Z_lt_le_dec FL F); [left; lia|]. destruct (Z_lt_le_dec FL (F + 64)); [|right; lia].
  exfalso. exact (proj2 (HFpres FL ltac:(lia)) HFLown). }
assert (HFLs : FL + 1 <= SB + F / 8 \/ SB + F / 8 + 8 <= FL).
{ destruct (Z_lt_le_dec FL (SB + F / 8)); [left; lia|]. destruct (Z_lt_le_dec FL (SB + F / 8 + 8)); [|right; lia].
  exfalso. specialize (HFSpres (FL - (SB + F / 8)) ltac:(lia)). replace (SB + F / 8 + (FL - (SB + F / 8))) with FL in HFSpres by lia.
  exact (proj2 HFSpres HFLown). }
(* disjunctions are case splits for lia: keep them boxed outside the two places that use them *)
change (wu_box (o + n <= F \/ F + 64 <= o)) in HFRo. change (wu_box (o + n <= FL \/ FL + 1 <= o)) in HFLo.
change (wu_box (o + n <= SB + F / 8 \/ SB + F / 8 + 8 <= o)) in HSHo.
change (wu_box (FL + 1 <= F \/ F + 64 <= FL)) in HFLf. change (wu_box (FL + 1 <= SB + F / 8 \/ SB + F / 8 + 8 <= FL)) in HFLs.
let wu_awr := idtac; wu_awr_norm;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 530%nat (SP1 - sp0));
    [reflexivity | rewrite U530; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
    [reflexivity | rewrite Usp2; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 516%nat F);
    [reflexivity | exact U516 | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply awr_frame0; fold F; left; lia |]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 529%nat (SB + F / 8));
    [reflexivity | exact U529 | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply awr_frame0; fold F; right;
     unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia |]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat o);
    [reflexivity | exact U10 | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha;
     apply (awr_byte_cons_own _ _ _ _ (ablocks B lyc Sc)); [exact Eab | exact (proj1 (HWR a ltac:(lia)))] |] ] in
let wu_tcj := idtac;
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?m1) (mrestrict _ ?m2), HG : mem_grows _ _, TK2 : tcj_kept _ _ _ _ _ _ _ _ _ _ |- _ =>
  let TK3 := fresh "TK" in
  assert (TK3 : tcj_kept B 4176 lyc Sc W memc W m2 (spZ regs) (fun a => o <= a < o + n));
  [ apply (tcj_step 4176 lyc Sc W memc mdc m1 m2 (spZ regs) _ Zw HARc ltac:(lia) HEimg TK2);
    [ let a := fresh "a" in let Ha := fresh "Ha" in let Hnz := fresh "Hnz" in
      intros a Ha Hnz; apply (kept_of_frame Ex rs (w_H W) m1 m2 Zw HFr); [|exact Ha|exact Hnz];
      let bb := fresh "bb" in let wlo := fresh "wlo" in let whi := fresh "whi" in let aa := fresh "aa" in
      let Hin := fresh "Hin" in let Hr := fresh "Hr" in let Hq := fresh "Hq" in
      intros bb wlo whi aa Hin Hr; cbn [windows map ss_mem YP09.r_base YP09.r_wlo YP09.r_whi] in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr;
        rewrite ?Usp2, ?U516, ?U528, ?U529, ?U530, ?U10 in Hr; unfold Zw; lia |]); destruct Hin
    | let a := fresh "a" in let Hp := fresh "Hp" in intros a Hp; eapply apresent_grows; [exact HG | exact Hp]
    | exact HZ ]
  | clear TK2 HFr HG; try match goal with HF : frame_of _ _ _ _ |- _ => clear HF end; rename TK3 into TK2 ] end in
(* ---- after the digit loop: the copy loop (shadow tokens), the release, the return --------------- *)
let tail j := idtac;
  let nl := eval vm_compute in (Z.of_nat (Nat.succ j)) in
  paj_run_to_sh RUNTOP HS HJ2 15292; [ wu_awr | ];
  wu_tcj;
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
    let HS3 := fresh "HS3" in
    pose proof (st_ok_pi_submem Ex ssx msx (map wu_ro (ss_mem ssx)) HS (submem_map_ro _) ltac:(vm_compute; reflexivity)) as HS3;
    clear HS; rename HS3 into HS end;
  wu_norm_ss HS;
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msc) =>
    let HS3 := fresh "HS3" in
    pose proof (st_ok_pi_add_region Ex _ (restrict (w_H W) msc) (YP09.mkRegion (Some 10%nat) 0 nl 0 nl [])
      (st_ok_pi_add_fact Ex ssx (restrict (w_H W) msc) 10 _ HS F10) eq_refl
      ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite U10; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
        intros a Ha; apply (apresent_writable SEGS);
        exact (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (o + a) HJ2
          (awr_byte_cons_own _ _ _ _ (ablocks B lyc Sc) _ _ _ _ _ Eab (proj1 (HWR (o + a) ltac:(lia)))))))
      ltac:(cbn [ss_mem all_disjoint add_atom]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
        rewrite U10, U529, U516, U530, Usp2; unfold wu_box in HFRo, HSHo; repeat split; lia)) as HS3;
    clear HS; rename HS3 into HS end;
  wu_norm_ss HS;
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict _ ?msc) =>
    assert (SHOK : sh_ok SEGS (SOff 32 0) [mkSHE 10 0 nl] Ex (mrestrict (w_H W) (ms_mem msc)));
    [ unfold sh_ok; apply Forall_cons; [|apply Forall_nil];
      unfold shent_ok, app_apart; cbn [she_m she_lo she_hi]; rewrite UB32, UO10;
      split;
      [ rewrite <- (aview_rd_of SEGS); rewrite Z.add_0_r; replace (nl - 0) with n by lia; rewrite SB_SHADOW_OFF;
        exact (wu_ra_out 4176 lyc Sc W memc mdc S2 (ms_mem msc) _ (spZ regs) o n HARc (proj1 HJ2) Eab HDST HRA TK2)
      | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [Z.min Z.max] in Ha;
        let Happ := fresh "Happ" in
        destruct (wu_tdst_where lyc Sc W memc mdc o n a HARc HDST ltac:(lia)) as (_ & Happ & _);
        unfold app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *; lia ]
    | ] end;
  paj_run_tok RUN HS HJ2 SHOK Bspan; [ wu_awr | ];
  wu_tcj;
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    let AG3 := fresh "AG3" in
    assert (AG3 : forall nn, (nn < 531)%nat -> ew Ex nn = ew Ev2 nn)
      by (let nn := fresh "nn" in let Hnn := fresh "Hnn" in
          intros nn Hnn; repeat rewrite ew_ewset_other by (clear - Hnn; lia); reflexivity);
    let V := fresh "V" in
    assert (V : bv_unsigned (ew Ex 516) = F) by (rewrite AG3 by (apply Nat.ltb_lt; reflexivity); exact U516); clear U516; rename V into U516;
    assert (V : bv_unsigned (ew Ex 528) = FL) by (rewrite AG3 by (apply Nat.ltb_lt; reflexivity); exact U528); clear U528; rename V into U528;
    assert (V : bv_unsigned (ew Ex 529) = SB + F / 8) by (rewrite AG3 by (apply Nat.ltb_lt; reflexivity); exact U529); clear U529; rename V into U529;
    assert (V : bv_unsigned (ew Ex 530) = SP1) by (rewrite AG3 by (apply Nat.ltb_lt; reflexivity); exact U530); clear U530; rename V into U530;
    assert (V : bv_unsigned (ew Ex 10) = o) by (rewrite AG3 by (apply Nat.ltb_lt; reflexivity); exact U10); clear U10; rename V into U10;
    assert (V : bv_unsigned (ew Ex 2) = spZ regs) by (rewrite AG3 by (apply Nat.ltb_lt; reflexivity); exact Usp2); clear Usp2; rename V into Usp2;
    assert (V : U Ex (SOff 11 0) = v)
      by (apply U_atom; [rewrite AG3 by (apply Nat.ltb_lt; reflexivity); exact X11 | clear - Hv; lia]); clear U11; rename V into U11;
    assert (V : env_agree 32 (Ereg regs wu_extra) Ex)
      by (eapply env_agree_trans; [exact AGv2 | split; [let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; apply AG3; clear - Hi; lia | reflexivity]]);
    clear AGv2; rename V into AGv2;
    assert (V : ew Ex 1 = getr regs 1) by (rewrite AG3, AG2 by (apply Nat.ltb_lt; reflexivity); exact E1); rename V into Y1
  end;
  let HFp3 := fresh "HFp3" in let HFs3 := fresh "HFs3" in let HFLp3 := fresh "HFLp3" in
  destruct (al_frames _ _ LAWS _ _ _ _ _ 0 pos (proj1 HJ2) Hfin2) as (_ & _ & HFp3 & HFs3);
  destruct (FFL _ _ _ _ _ 0 pos (proj1 HJ2) Hfin2) as (HFLp3 & _ & _ & _);
  change (fs_frame_bytes 0) with 64 in HFp3, HFs3; change (64 / 8) with 8 in HFs3;
  fold F in HFp3, HFs3; fold FL in HFLp3; unfold shadow_addr in HFs3; rewrite <- SB_SHADOW_OFF in HFs3;
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msc) =>
    let r1 := eval vm_compute in (nth 1 (ss_mem ssx) (stack_region 0)) in
    let HS3 := fresh "HS3" in
    pose proof (ast_ok_pi_set_region Ex ssx (restrict (w_H W) msc) 1 r1 (set_window r1 0 8) HS
      ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
      ltac:(apply region_ok_rewindow; [exact (st_ok_pi_region_nth Ex ssx _ 1 r1 HS ltac:(vm_compute; reflexivity)) |];
        let oo := fresh "oo" in let Hoo := fresh "Hoo" in
        intros oo Hoo; cbn [YP09.r_base base_val ms_mem restrict mkst]; rewrite U529;
        apply (apresent_writable SEGS); exact (proj1 (HFs3 oo ltac:(lia))))) as HS3;
    clear HS; rename HS3 into HS end;
  wu_norm_ss HS;
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msc) =>
    let r2 := eval vm_compute in (nth 2 (ss_mem ssx) (stack_region 0)) in
    let HS3 := fresh "HS3" in
    pose proof (ast_ok_pi_set_region Ex ssx (restrict (w_H W) msc) 2 r2 (set_window r2 0 8) HS
      ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
      ltac:(apply region_ok_rewindow; [exact (st_ok_pi_region_nth Ex ssx _ 2 r2 HS ltac:(vm_compute; reflexivity)) |];
        let oo := fresh "oo" in let Hoo := fresh "Hoo" in
        intros oo Hoo; cbn [YP09.r_base base_val ms_mem restrict mkst]; rewrite U516;
        apply (apresent_writable SEGS); exact (proj1 (HFp3 (F + oo) ltac:(lia))))) as HS3;
    clear HS; rename HS3 into HS end;
  wu_norm_ss HS;
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msc) =>
    let HS3 := fresh "HS3" in
    pose proof (st_ok_pi_add_region Ex ssx (restrict (w_H W) msc) (YP09.mkRegion (Some 528%nat) 0 1 0 1 []) HS eq_refl
      ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite U528; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
        let oo := fresh "oo" in let Hoo := fresh "Hoo" in
        intros oo Hoo; replace (FL + oo) with FL by lia; apply (apresent_writable SEGS); exact HFLp3)
      ltac:(cbn [ss_mem all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
        rewrite U528, U10, U529, U516, U530, Usp2; unfold wu_box in HFLo, HFLs, HFLf; repeat split; lia)) as HS3;
    clear HS; rename HS3 into HS end;
  wu_norm_ss HS;
  paj_run_flag_sh RUNF HS HJ2;
  [ lia
  | let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
    intros a (r & Hin & Hr); cbn [ss_mem] in Hin;
    repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
       rewrite ?Usp2, ?U516, ?U528, ?U529, ?U530, ?U10 in Hr;
       first [ right; fold FL; lia
             | left; apply awr_frame0; fold F; first [left; lia | right; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia]
             | left; apply (awr_byte_cons_own _ _ _ _ (ablocks B lyc Sc)); [exact Eab | exact (proj1 (HWR a ltac:(lia)))]
             | exfalso; lia ] |]);
    destruct Hin
  | let msr := fresh "msr" in let HSr := fresh "HSr" in intros msr HSr;
    let HR0 := fresh "HR0" in pose proof (st_ok_pi_region_nth _ _ msr 0%nat _ HSr eq_refl) as HR0;
    let V := fresh "V" in
    pose proof (field_of_region _ _ 528%nat FL _ _ _ _ _ 0 1%N (SLit 0) 0 HR0 U528 ltac:(cbn; left; reflexivity) eq_refl
      ltac:(cbn; lia) ltac:(cbn; lia)) as V;
    specialize (V 0%nat ltac:(cbn; lia)); change (Z.of_nat 0) with 0 in V; rewrite !Z.add_0_r in V;
    change (flag_addr lyc 0 pos) with FL; rewrite V; reflexivity
  | ];
  wu_tcj;
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msc) =>
    let R1 := fresh "R1" in let R10 := fresh "R10" in
    prreg HS (1%bv : bv 5) R1; prreg HS (10%bv : bv 5) R10;
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
    let mat' := fresh "mat" in intros mat';
    unfold twrite_uint_post; fold n;
    split; [reflexivity|];
    exists lyc, (stack_free_state 0 pos S2), (ms_regs msc), (ms_mem msc); eexists;
    split; [cbn [ms_regs]; rewrite R1; first [rewrite Y1 | rewrite (AG2 1%nat) by (apply Nat.ltb_lt; reflexivity); rewrite E1];
            unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|];
    split; [unfold EV_WRITE_UINT; rewrite Z.add_0_r;
            apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ2|];
    split; [eapply (aregs_preserved_of_st_ok SEGS _ Ex _ _ regs wu_extra HS); [exact AGv2 | vm_compute; reflexivity]|];
    split; [cbn [ms_regs]; rewrite R10, Hn; reflexivity|];
    split; [unfold ablocks in Eab |- *; rewrite blocks_stack_free_state, Eab; apply Permutation_refl|];
    split;
    [ let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
      let Hlen := fresh "Hlen" in
      assert (Hlen : length (wu_bytes v) = Z.to_nat n)
        by (unfold wu_bytes, n, write_uint_c.write_uint_n; rewrite length_map, Nat2Z.id; reflexivity);
      rewrite Hlen, Hn in Hi; cbn in Hi;
      rewrite (Hbytes i ltac:(clear - Hi; lia));
      let HR1 := fresh "HR1" in
      pose proof (st_ok_pi_region_nth _ _ _ 1%nat _ HS eq_refl) as HR1; cbn [ms_mem restrict mkst] in HR1;
      split; [| let Hm := fresh "Hm" in pose proof (Z.mod_pos_bound (wdv v (j - i)) 10 ltac:(reflexivity)) as Hm; clear - Hm; lia];
      do 5 (destruct i as [|i];
        [ first
          [ exfalso; clear - Hi; lia
          | cbn [Z.of_nat Pos.of_succ_nat Pos.succ Nat.sub];
            lazymatch goal with |- val_mem _ ?mm (o + ?zi) 1 (48 + wdv v ?t mod 10) =>
              let V := fresh "V" in
              pose proof (field_of_region_any _ mm 10%nat o _ _ _ _ _ zi 1%N _ HR1 U10
                ltac:(cbn; solve [repeat (first [left; reflexivity | right])]) ltac:(cbn; lia)) as V;
              lazymatch type of V with val_mem _ _ _ _ (bv_unsigned (sv_denot ?Ey ?e) mod _) =>
                replace (bv_unsigned (sv_denot Ey e)) with (48 + wdv v t mod 10) in V
                  by (symmetry; exact (wu_U_byte Ey v t U11 Hv)) end;
              change (N.to_nat 1) with 1%nat in V; change (2 ^ (8 * Z.of_N 1)) with 256 in V;
              let Hm := fresh "Hm" in
              pose proof (Z.mod_pos_bound (wdv v t) 10 ltac:(reflexivity)) as Hm;
              rewrite Z.mod_small in V by (clear - Hm; lia); exact V end ]
        | ]); exfalso; clear - Hi; lia
    | exact TK2 ]
  end in
let rec loop1 j :=
  paj_run_sh RUNP HS HJ2; [ wu_awr | ];
  wu_tcj;
  psrr_branch_pi RUNP BR HS;
  [ (* the branch is taken: one more digit *)
    let Hge := fresh "Hge" in
    lazymatch goal with Hc : branch_taken _ (sv_denot _ (SLit 9)) (sv_denot _ ?x) = true |- _ =>
      let Hop := fresh "Hop" in
      assert (Hop : U Ev2 x = wdv v j)
        by (first [ exact U11
                  | change x with (wlo16 (wx j)); rewrite wu_U_lo16 by (rewrite (proj1 (wu_U_wx Ev2 v U11 Hv j)); exact (proj2 (wu_U_wx Ev2 v U11 Hv j)));
                    exact (proj1 (wu_U_wx Ev2 v U11 Hv j)) ]);
      assert (Hge : 10 <= wdv v j) by (rewrite branch_ltu_U, U_lit, Hop in Hc by lia; apply Z.ltb_lt in Hc; lia);
      clear Hc Hop end;
    lazymatch j with
    | 4%nat => exfalso; pose proof (wu_dv4 v Hv) as H4; clear - H4 Hge; lia
    | _ => let j' := eval compute in (Nat.succ j) in loop1 j' end
  | (* the branch is not taken: write_uint_n v = j + 1 *)
    let Hlt := fresh "Hlt" in
    lazymatch goal with Hc : branch_taken _ (sv_denot _ (SLit 9)) (sv_denot _ ?x) = false |- _ =>
      let Hop := fresh "Hop" in
      assert (Hop : U Ev2 x = wdv v j)
        by (first [ exact U11
                  | change x with (wlo16 (wx j)); rewrite wu_U_lo16 by (rewrite (proj1 (wu_U_wx Ev2 v U11 Hv j)); exact (proj2 (wu_U_wx Ev2 v U11 Hv j)));
                    exact (proj1 (wu_U_wx Ev2 v U11 Hv j)) ]);
      assert (Hlt : wdv v j < 10) by (rewrite branch_ltu_U, U_lit, Hop in Hc by lia; apply Z.ltb_ge in Hc; lia);
      clear Hc Hop end;
    let Hall := fresh "Hall" in
    assert (Hall : forall t, (t < j)%nat -> 10 <= wdv v t)
      by (let t := fresh "t" in let Ht := fresh "Ht" in intros t Ht; do 5 (destruct t as [|t]; [first [assumption | lia] |]); lia);
    destruct (wu_bytes_exit v j ltac:(clear - Hv; lia) Hall Hlt ltac:(clear; lia)) as (Hn & Hbytes);
    cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hn; fold n in Hn;
    tail j ]
in loop1 0%nat.
Qed.
End w.
End f2.
End d2.
