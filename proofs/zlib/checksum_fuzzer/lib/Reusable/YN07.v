(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK15 YK0n YP0n YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a YO0b YO0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH00 YH03 YN0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section g.
Variable xv : nat -> Z.
Hypothesis XR : forall n, 0 <= xv n < 2 ^ 64.
Lemma ew_EV n : bv_unsigned (ew (EV xv) n) = xv n.
Proof. cbn. apply lit64_small. apply XR. Qed.
Lemma U_off n z : 0 <= xv n + z < 2 ^ 64 -> bv_unsigned (sv_denot (EV xv) (SOff n z)) = xv n + z.
Proof. intros H. cbn [sv_denot]. rewrite ew_EV. apply lit64_small. exact H. Qed.
Lemma U_off0 n : bv_unsigned (sv_denot (EV xv) (SOff n 0)) = xv n.
Proof. rewrite U_off; [lia|]. pose proof (XR n). lia. Qed.
Lemma U_lit z : bv_unsigned (sv_denot (EV xv) (SLit z)) = z mod 2 ^ 64.
Proof. cbn [sv_denot]. apply lit64_unsigned. Qed.
Lemma base_val_EV n : base_val (EV xv) (Some n) = xv n.
Proof. cbn [base_val]. apply ew_EV. Qed.
End g.
Lemma nth_regs_init n : (1 <= n <= 31)%nat -> nth n regs_init (SLit 0) = SOff n 0.
Proof.
intros H. unfold regs_init.
do 32 (destruct n as [|n]; [first [reflexivity | lia] |]). lia.
Qed.
Definition nat_to_reg (n : nat) : reg :=
match n with
| 1%nat => (1%bv : reg)
| 2%nat => (2%bv : reg)
| 3%nat => (3%bv : reg)
| 4%nat => (4%bv : reg)
| 5%nat => (5%bv : reg)
| 6%nat => (6%bv : reg)
| 7%nat => (7%bv : reg)
| 8%nat => (8%bv : reg)
| 9%nat => (9%bv : reg)
| 10%nat => (10%bv : reg)
| 11%nat => (11%bv : reg)
| 12%nat => (12%bv : reg)
| 13%nat => (13%bv : reg)
| 14%nat => (14%bv : reg)
| 15%nat => (15%bv : reg)
| 16%nat => (16%bv : reg)
| 17%nat => (17%bv : reg)
| 18%nat => (18%bv : reg)
| 19%nat => (19%bv : reg)
| 20%nat => (20%bv : reg)
| 21%nat => (21%bv : reg)
| 22%nat => (22%bv : reg)
| 23%nat => (23%bv : reg)
| 24%nat => (24%bv : reg)
| 25%nat => (25%bv : reg)
| 26%nat => (26%bv : reg)
| 27%nat => (27%bv : reg)
| 28%nat => (28%bv : reg)
| 29%nat => (29%bv : reg)
| 30%nat => (30%bv : reg)
| 31%nat => (31%bv : reg)
| _ => (0%bv : reg)
end.
Lemma nat_to_reg_unsigned n : (n <= 31)%nat -> bv_unsigned (nat_to_reg n) = Z.of_nat n.
Proof. intros H. do 32 (destruct n as [|n]; [reflexivity|]). lia. Qed.
Lemma nat_to_reg_ridx (r : reg) : nat_to_reg (Z.to_nat (bv_unsigned r)) = r.
Proof.
pose proof (u5_range r). apply bv_eq. rewrite nat_to_reg_unsigned by lia. lia.
Qed.
Lemma regs_ok_init xv regs :
(forall n, (1 <= n <= 31)%nat -> Z_to_bv 64 (xv n) = getr regs (nat_to_reg n)) ->
regs_ok (EV xv) regs_init regs.
Proof.
intros H r. unfold sr_get. pose proof (u5_range r) as Hr. destruct (bv_eqb r 0) eqn:E.
- unfold getr. rewrite E. reflexivity.
- assert (Hr0 : bv_unsigned r <> 0).
{ intros Z0. assert (r = 0%bv) as -> by (apply bv_eq; exact Z0). rewrite bv_eqb_refl in E. discriminate. }
unfold ridx. rewrite nth_regs_init by lia. cbn [sv_denot EV ew]. rewrite Z.add_0_r.
specialize (H (Z.to_nat (bv_unsigned r)) ltac:(lia)). rewrite nat_to_reg_ridx in H.
rewrite <- H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Z.mod_mod; [reflexivity|]. cbv; discriminate.
Qed.
Definition bytes_are (m : word -> option byte) (a : Z) (w : nat) (v : Z) : Prop :=
forall k, (k < w)%nat -> mbyte src0segs m (a + Z.of_nat k) = Some (Z_to_bv 8 (le_byte v w k)).
Lemma Z_to_bv8_mod x : Z_to_bv 8 (x mod 256) = Z_to_bv 8 x.
Proof. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_mod. lia. Qed.
Lemma chunk_ok_val xv m base off (w : N) (e : sv) v :
bv_unsigned (sv_denot (EV xv) e) = v -> 0 <= v < 2 ^ (8 * Z.of_N w) ->
bytes_are m (base + off) (N.to_nat w) v ->
chunk_ok src0segs (EV xv) m base (mkChunk off (CVal w e)).
Proof.
intros Hv Hr Hb i Hi. cbn [c_off c_val c_len cv_len] in *.
exists (byte_of_word (sv_denot (EV xv) e) i). split; [reflexivity|].
specialize (Hb (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in Hb by lia. rewrite Hb. f_equal.
unfold byte_of_word, le_byte. rewrite Hv. rewrite Z_to_bv8_mod. f_equal.
rewrite Z2Nat.id by lia. rewrite N_nat_Z. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma chunk_ok_lit0 xv m base off (w : N) :
(forall k, (k < N.to_nat w)%nat -> mbyte src0segs m (base + off + Z.of_nat k) = Some (Z_to_bv 8 0)) ->
chunk_ok src0segs (EV xv) m base (mkChunk off (CVal w (SLit 0))).
Proof.
intros Hb. apply (chunk_ok_val xv m base off w (SLit 0) 0).
- cbn [sv_denot]. rewrite Z_to_bv_unsigned. reflexivity.
- split; [lia|]. apply Z.pow_pos_nonneg; lia.
- intros k Hk. rewrite Hb by exact Hk. f_equal. unfold le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia). reflexivity.
Qed.
Lemma region_ok_intro E m r :
0 <= base_val E (r_base r) + r_lo r -> base_val E (r_base r) + r_hi r <= 2 ^ 64 ->
(forall o, r_wlo r <= o < r_whi r -> writable_at src0segs m (base_val E (r_base r) + o)) ->
Forall (chunk_ok src0segs E m (base_val E (r_base r))) (r_chunks r) ->
region_ok src0segs E m r.
Proof. intros. unfold region_ok. auto. Qed.
Record fvals := FV {
fv_regs : bvmap 5 word;
fv_g : Z; fv_mem : Z; fv_off : Z; fv_h3 : Z; fv_idx : Z; fv_rsv : Z; fv_bits : Z;
fv_av : Z; fv_fr : Z; fv_area : Z; fv_sc : Z; fv_scl : Z; fv_last : Z; fv_ml : Z;
fv_end : Z; fv_pn : Z; fv_glo : Z; fv_ghi : Z;
fv_sec : Z   }.
Definition fv_p (v : fvals) : Z := bv_unsigned (getr (fv_regs v) 10).
Definition fv_sp (v : fvals) : Z := bv_unsigned (getr (fv_regs v) 2).
Definition xvf (v : fvals) (n : nat) : Z :=
if (n <? 32)%nat then bv_unsigned (getr (fv_regs v) (nat_to_reg n))
else match n with
| 40%nat => fv_g v | 41%nat => fv_mem v | 42%nat => fv_off v | 43%nat => fv_h3 v | 44%nat => fv_idx v
| 45%nat => fv_rsv v | 46%nat => fv_bits v | 47%nat => fv_av v | 48%nat => fv_fr v | 49%nat => fv_area v
| 50%nat => fv_sc v | 51%nat => TBL + 2 * fv_sc v | 52%nat => fv_scl v | 53%nat => fv_last v
| 54%nat => fv_ml v | 55%nat => 4096 * fv_ml v
| 57%nat => fv_end v | 58%nat => fv_pn v | 59%nat => fv_end v - fv_p v
| 39%nat => fv_sec v
| _ => 0
end.
Definition in_img1 (a : Z) : Prop := 0x10000 <= a < 0x51000.
Record free_pre (k : kcase) (r : rcase) (v : fvals) (m : word -> option byte) : Prop := {
fp_vals : 0 <= fv_g v /\ 0 <= fv_mem v /\ 0 <= fv_off v /\ 0 <= fv_h3 v < 256 /\ 0 <= fv_idx v /\ 0 <= fv_rsv v < 2 ^ 32 /\
0 <= fv_bits v < 2 ^ 64 /\ 0 <= fv_av v < 2 ^ 32 /\ 0 <= fv_fr v < 2 ^ 32 /\ 0 <= fv_area v /\
0 <= fv_sc v < 64 /\ 0 <= fv_scl v <= 8191 /\ 0 <= fv_last v <= 31 /\ 0 <= fv_ml v < 2 ^ 51 /\
0 <= fv_end v /\ 0 <= fv_pn v /\ 0 <= fv_sec v < 2 ^ 64;
fp_sp : CEIL + 8192 <= fv_sp v < 2 ^ 63 /\ fv_sp v mod 16 = 0;
fp_p : 4096 <= fv_p v /\ fv_p v mod 16 = 0;
fp_grp : 4096 <= fv_glo v /\ fv_ghi v <= CEIL /\ fv_glo v <= fv_mem v /\ fv_mem v + 8 <= fv_p v - 4 /\
fv_p v <= fv_end v /\ fv_end v + 1 <= fv_ghi v /\ fv_p v <= fv_pn v /\ fv_pn v + 1 <= fv_ghi v /\
(forall a, fv_glo v <= a < fv_ghi v -> ~ in_img1 a);
fp_ar : 4096 <= fv_area v /\ fv_area v + 4096 <= CEIL /\ fv_area v mod 4096 = 0 /\
fv_area v + 24 <= fv_g v /\ fv_g v + 40 <= fv_area v + 4096 /\
(forall a, fv_area v <= a < fv_area v + 4096 -> ~ in_img1 a) /\
(fv_ghi v <= fv_area v \/ fv_area v + 4096 <= fv_glo v);
fp_pmem : fv_p v = fv_mem v + 16 + 16 * fv_off v;
fp_off16 : fv_off v <= 65535;
fp_h3idx : Z.land (fv_h3 v) 31 = fv_idx v;
fp_idx : fv_idx v <= fv_last v;
fp_bits : fv_bits v = bits_enc (fv_last v) (fv_sc v) (fv_ml v);
fp_avbit : Z.testbit (fv_av v) (fv_idx v) = false;
fp_frbit : Z.testbit (fv_fr v) (fv_idx v) = false;
fp_k : match k with
| K1 => fv_ml v = 0 /\ fv_sc v <= 47 /\ 1 <= fv_scl v /\ fv_scl v * fv_idx v <= fv_off v < fv_scl v * (fv_idx v + 1) /\
fv_end v = fv_mem v + 12 + 16 * fv_scl v * (fv_idx v + 1)
| K2 => 1 <= fv_ml v /\ fv_sc v <= 47 /\ 1 <= fv_scl v /\ fv_scl v * fv_idx v <= fv_off v < fv_scl v * (fv_idx v + 1) /\
fv_off v <= 256 * fv_ml v - 1 /\ 1 <= fv_last v /\
fv_end v = fv_mem v + 12 + 16 * fv_scl v * (fv_idx v + 1)
| K3a => 1 <= fv_ml v /\ fv_sc v <= 47 /\ 1 <= fv_scl v /\ fv_scl v * fv_idx v <= fv_off v < fv_scl v * (fv_idx v + 1) /\
fv_off v <= 256 * fv_ml v - 1 /\ fv_idx v = 0 /\ fv_last v = 0 /\
fv_end v = fv_mem v + 4096 * fv_ml v - 4
| K3b => 1 <= fv_ml v /\ fv_sc v = 63 /\ fv_off v <= 256 * fv_ml v - 1 /\ fv_idx v = 0 /\ fv_last v = 0 /\
fv_end v = fv_mem v + 4096 * fv_ml v - 4
end;
fp_r : match r with
| R0 => fv_h3 v = fv_idx v
| R14 => fv_h3 v = fv_idx v + 32 * fv_rsv v /\ 1 <= fv_rsv v <= 4 /\ fv_pn v = fv_end v - fv_rsv v /\ fv_rsv v <= fv_end v - fv_p v
| R5 => fv_h3 v = fv_idx v + 160 /\ fv_rsv v = 5 /\ fv_rsv v <= fv_end v - fv_p v
| R6 => fv_h3 v = fv_idx v + 160 /\ 6 <= fv_rsv v /\ fv_pn v = fv_end v - fv_rsv v /\ fv_rsv v <= fv_end v - fv_p v
end;
fp_c_p4 : bytes_are m (fv_p v - 4) 1 0;
fp_c_p3 : bytes_are m (fv_p v - 3) 1 (fv_h3 v);
fp_c_p2 : bytes_are m (fv_p v - 2) 2 (fv_off v);
fp_c_mem : bytes_are m (fv_mem v) 8 (fv_g v);
fp_c_g16 : bytes_are m (fv_g v + 16) 8 (fv_mem v);
fp_c_g24 : bytes_are m (fv_g v + 24) 4 (fv_av v);
fp_c_g28 : bytes_are m (fv_g v + 28) 4 (fv_fr v);
fp_c_g32 : bytes_are m (fv_g v + 32) 8 (fv_bits v);
fp_c_area : bytes_are m (fv_area v) 8 (fv_sec v);
fp_c_ctx : bytes_are m src0_D_malloc_context 8 (fv_sec v);
fp_c_nl : bytes_are m (src0_D_libc + 3) 1 0;
fp_c_tq : match k with K3b => True | _ => bytes_are m (TBL + 2 * fv_sc v) 2 (fv_scl v) end;
fp_c_end : bytes_are m (fv_end v) 1 0;
fp_c_end5 : match r with R5 | R6 => bytes_are m (fv_end v - 4) 4 (fv_rsv v) /\ bytes_are m (fv_end v - 5) 1 0 /\ fv_p v <= fv_end v - 5 | _ => True end;
fp_c_pn : match r with R14 | R6 => bytes_are m (fv_pn v) 1 0 | _ => True end;
fp_pn6 : match r with R6 => fv_pn v + 1 <= fv_end v - 5 | R14 => fv_pn v + 1 <= fv_end v | _ => True end;
fp_w_hdr : forall a, fv_p v - 3 <= a < fv_p v -> writable_at src0segs m a;
fp_w_meta : forall a, fv_g v + 28 <= a < fv_g v + 32 -> writable_at src0segs m a;
fp_w_stk : forall a, fv_sp v - 8192 <= a < fv_sp v -> writable_at src0segs m a
}.
Section h.
Variable xv : nat -> Z.
Hypothesis XR : forall n, 0 <= xv n < 2 ^ 64.
Lemma den_off n z : 0 <= xv n + z < 2 ^ 64 -> sv_denot (EV xv) (SOff n z) = Z_to_bv 64 (xv n + z).
Proof. intros H. cbn [sv_denot]. rewrite (ew_EV xv XR). reflexivity. Qed.
Lemma den_off0 n : sv_denot (EV xv) (SOff n 0) = Z_to_bv 64 (xv n).
Proof. cbn [sv_denot]. rewrite (ew_EV xv XR), Z.add_0_r. reflexivity. Qed.
Lemma den_lit z : sv_denot (EV xv) (SLit z) = Z_to_bv 64 z.
Proof. reflexivity. Qed.
Lemma U_sext32 a : bv_unsigned (sv_denot (EV xv) (SExt true 32 a)) = sx32 (bv_unsigned (sv_denot (EV xv) a)).
Proof.
cbn [sv_denot]. rewrite sext64_32_unsigned, bv_extract_unsigned, Z.shiftr_0_r, bv_wrap32.
change (bv_unsigned (sv_denot (EV xv) a) mod 2 ^ 32) with (lo32 (bv_unsigned (sv_denot (EV xv) a))). apply sx32_lo32.
Qed.
End h.
Lemma xvf_reg v n : (n <= 31)%nat -> xvf v n = bv_unsigned (getr (fv_regs v) (nat_to_reg n)).
Proof. intros H. unfold xvf. replace (n <? 32)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity. Qed.
Lemma xvf_range k r v m : free_pre k r v m -> forall n, 0 <= xvf v n < 2 ^ 64.
Proof.
intros FP n. pose proof (fp_vals _ _ _ _ FP) as V. pose proof (fp_sp _ _ _ _ FP) as SPf. pose proof (fp_p _ _ _ _ FP) as Pf.
pose proof (fp_grp _ _ _ _ FP) as GR. pose proof (fp_ar _ _ _ _ FP) as AR.
pose proof (fp_off16 _ _ _ _ FP) as O16. pose proof (fp_idx _ _ _ _ FP) as IX.
destruct (Nat.le_gt_cases n 31) as [Hn|Hn].
- rewrite xvf_reg by exact Hn. apply (wd_range (getr (fv_regs v) (nat_to_reg n))).
- unfold xvf. replace (n <? 32)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
unfold fv_p in *.
pose proof (proj1 alloc_ceiling_val) as ACV.
do 60 (destruct n as [|n]; [first [lia | (cbn; unfold CEIL, TBL, src0_D_size_classes in *; lia)] |]). cbn. lia.
Qed.
Lemma lin_facts k r v m (FP : free_pre k r v m) :
let P := fv_p v in let SP := fv_sp v in
0 <= fv_g v /\ 0 <= fv_mem v /\ 0 <= fv_off v <= 65535 /\ 0 <= fv_h3 v < 256 /\ 0 <= fv_idx v <= fv_last v /\ 0 <= fv_rsv v < 2 ^ 32 /\
0 <= fv_bits v < 2 ^ 64 /\ 0 <= fv_av v < 2 ^ 32 /\ 0 <= fv_fr v < 2 ^ 32 /\
0 <= fv_sc v < 64 /\ 0 <= fv_scl v <= 8191 /\ 0 <= fv_last v <= 31 /\ 0 <= fv_ml v < 2 ^ 51 /\
0 <= fv_sec v < 2 ^ 64 /\
CEIL + 8192 <= SP < 2 ^ 63 /\ 4096 <= P /\ P = fv_mem v + 16 + 16 * fv_off v /\
4096 <= fv_glo v /\ fv_ghi v <= CEIL /\ fv_glo v <= fv_mem v /\ fv_mem v + 8 <= P - 4 /\
P <= fv_end v /\ fv_end v + 1 <= fv_ghi v /\ P <= fv_pn v /\ fv_pn v + 1 <= fv_ghi v /\
4096 <= fv_area v /\ fv_area v + 4096 <= CEIL /\ fv_area v + 24 <= fv_g v /\ fv_g v + 40 <= fv_area v + 4096 /\
(fv_ghi v <= fv_area v \/ fv_area v + 4096 <= fv_glo v) /\
(fv_ghi v <= 0x10000 \/ 0x51000 <= fv_glo v) /\
(fv_area v + 4096 <= 0x10000 \/ 0x51000 <= fv_area v).
Proof.
pose proof (fp_vals _ _ _ _ FP) as V. pose proof (fp_sp _ _ _ _ FP) as [S1 _]. pose proof (fp_p _ _ _ _ FP) as [P1 _].
pose proof (fp_grp _ _ _ _ FP) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GI).
pose proof (fp_ar _ _ _ _ FP) as (A1 & A2 & _ & A4 & A5 & AI & AD).
pose proof (fp_pmem _ _ _ _ FP). pose proof (fp_off16 _ _ _ _ FP). pose proof (fp_idx _ _ _ _ FP).
cbn zeta. repeat (split; [lia|]). split.
- destruct (Z_le_dec (fv_ghi v) 0x10000); [left; lia|]. destruct (Z_le_dec 0x51000 (fv_glo v)); [right; lia|].
exfalso. destruct (Z_le_dec (fv_glo v) 0x10000).
+ apply (GI 0x10000); [lia | unfold in_img1; lia].
+ apply (GI (fv_glo v)); [lia | unfold in_img1; lia].
- destruct (Z_le_dec (fv_area v + 4096) 0x10000); [left; lia|]. destruct (Z_le_dec 0x51000 (fv_area v)); [right; lia|].
exfalso. destruct (Z_le_dec (fv_area v) 0x10000).
+ apply (AI 0x10000); [lia | unfold in_img1; lia].
+ apply (AI (fv_area v)); [lia | unfold in_img1; lia].
Qed.
End d.
Ltac lin := match goal with FP : free_pre _ _ _ _ |- _ => pose proof (lin_facts _ _ _ _ FP) as LF; cbn zeta in LF; pose proof (proj1 (@YM05.alloc_ceiling_val _)) as LFacv; unfold CEIL, TBL, src0_D_size_classes, src0_D_malloc_context, src0_D_libc in *; unfold fv_p, fv_sp in *; lia end.
Ltac reg_num := match goal with FP : free_pre _ _ _ _ |- _ =>
unfold extent_disjoint; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks reg_hdr reg_grp reg_meta reg_area reg_ctx reg_nl reg_stk reg_tq reg_end1 reg_end5 reg_pn];
rewrite ?(base_val_EV (xvf _) (xvf_range _ _ _ _ FP)); cbn [base_val];
unfold aP, aSP, aTP, aG, aMEM, aOFF, aH3, aIDX, aRSV, aBITS, aAV, aFR, aAREA, aSC, aTQ, aSCL, aLAST, aML, aMP, aEND, aPN, aEP, aSEC;
cbn [xvf Nat.ltb Nat.leb nat_to_reg] end.
Section j. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma pd_common k r v m (FP : free_pre k r v m) : pairwise_disjoint (EV (xvf v)) common_mem.
Proof.
unfold common_mem. cbn [pairwise_disjoint all_disjoint].
repeat match goal with |- _ /\ _ => split | |- True => exact I end; reg_num; lin.
Qed.
Lemma cross_tq k r v m (FP : free_pre k r v m) : Forall (fun x => extent_disjoint (EV (xvf v)) x reg_tq) common_mem.
Proof. unfold common_mem. repeat (apply Forall_cons || apply Forall_nil); reg_num; lin. Qed.
Lemma cross_end1 k r v m (FP : free_pre k r v m) : Forall (fun x => extent_disjoint (EV (xvf v)) x reg_end1) common_mem.
Proof. unfold common_mem. repeat (apply Forall_cons || apply Forall_nil); reg_num; lin. Qed.
Lemma cross_end5 k r v m (FP : free_pre k r v m) : match r with R5 | R6 => Forall (fun x => extent_disjoint (EV (xvf v)) x reg_end5) common_mem | _ => True end.
Proof.
pose proof (fp_c_end5 _ _ _ _ FP) as E5. destruct r; try exact I; destruct E5 as (_ & _ & E5);
unfold common_mem; repeat (apply Forall_cons || apply Forall_nil); reg_num; lin.
Qed.
Lemma cross_pn k r v m (FP : free_pre k r v m) : match r with R14 | R6 => Forall (fun x => extent_disjoint (EV (xvf v)) x reg_pn) common_mem | _ => True end.
Proof.
pose proof (fp_pn6 _ _ _ _ FP) as P6. destruct r; try exact I; unfold common_mem; repeat (apply Forall_cons || apply Forall_nil); reg_num; lin.
Qed.
Lemma pairwise_disjoint_app E l1 l2 :
pairwise_disjoint E l1 -> pairwise_disjoint E l2 ->
(forall y, In y l2 -> Forall (fun x => extent_disjoint E x y) l1) ->
pairwise_disjoint E (l1 ++ l2).
Proof.
revert l2. induction l1 as [|a t IH]; intros l2 H1 H2 HX; cbn; [exact H2|].
destruct H1 as [Ha Ht]. split.
- clear IH. induction t as [|b u IHt]; cbn.
+ induction l2 as [|c w IH2]; cbn; [exact I|]. split.
* pose proof (HX c (or_introl eq_refl)) as F. inversion F; subst. assumption.
* apply IH2; [destruct H2; assumption | intros y Hy; apply HX; right; exact Hy].
+ destruct Ha as [Hab Hau]. split; [exact Hab|]. apply IHt; [exact Hau | destruct Ht; assumption |].
intros y Hy. pose proof (HX y Hy) as F. inversion F as [|? ? Fa Ft]; subst. inversion Ft; subst. constructor; assumption.
- apply IH; [exact Ht | exact H2 |]. intros y Hy. pose proof (HX y Hy) as F. inversion F; subst. assumption.
Qed.
Lemma pd_all k r v m (FP : free_pre k r v m) : pairwise_disjoint (EV (xvf v)) (free_mem k r).
Proof.
unfold free_mem. apply pairwise_disjoint_app; [apply (pd_common _ _ _ _ FP) | |].
- pose proof (fp_pn6 _ _ _ _ FP) as P6. pose proof (fp_c_end5 _ _ _ _ FP) as E5.
destruct k, r; cbn [k_mem r_mem app pairwise_disjoint all_disjoint];
repeat match goal with |- _ /\ _ => split | |- True => exact I end; try (destruct E5 as (_ & _ & E5)); reg_num; lin.
- pose proof (cross_tq _ _ _ _ FP) as CT. pose proof (cross_end1 _ _ _ _ FP) as C1. pose proof (cross_end5 _ _ _ _ FP) as C5. pose proof (cross_pn _ _ _ _ FP) as CP.
intros y Hy. destruct k, r; cbn [k_mem r_mem app] in Hy, C5, CP;
repeat (destruct Hy as [<-|Hy]; [assumption|]); destruct Hy.
Qed.
Lemma bytes_are_at m a a' w v : bytes_are m a w v -> a = a' -> bytes_are m a' w v.
Proof. intros H <-. exact H. Qed.
End j.
Ltac val_tac := match goal with FP : free_pre _ _ ?v _ |- _ =>
rewrite (U_off0 (xvf v) (xvf_range _ _ _ _ FP));
unfold aP, aSP, aTP, aG, aMEM, aOFF, aH3, aIDX, aRSV, aBITS, aAV, aFR, aAREA, aSC, aTQ, aSCL, aLAST, aML, aMP, aEND, aPN, aEP, aSEC;
cbn [xvf Nat.ltb Nat.leb nat_to_reg]; reflexivity end.
Ltac chunk_from H := eapply chunk_ok_val; [val_tac | lin | eapply (bytes_are_at _ _ _ _ _ H); lin].
Section l. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma le_byte_0 w kk : le_byte 0 w kk = 0.
Proof. unfold le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity. Qed.
End l.
Ltac chunk0_from H := apply chunk_ok_lit0; intros kk Hk; pose proof (H kk Hk) as B; rewrite le_byte_0 in B; rewrite <- B; f_equal; lin.
Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma rok_hdr k r v m (FP : free_pre k r v m) : region_ok src0segs (EV (xvf v)) m reg_hdr.
Proof.
apply region_ok_intro; reg_num; [lin | lin | intros o Ho; apply (fp_w_hdr _ _ _ _ FP); lin |].
repeat (apply Forall_cons || apply Forall_nil).
- chunk0_from (fp_c_p4 _ _ _ _ FP).
- chunk_from (fp_c_p3 _ _ _ _ FP).
- chunk_from (fp_c_p2 _ _ _ _ FP).
Qed.
Lemma rok_grp k r v m (FP : free_pre k r v m) : region_ok src0segs (EV (xvf v)) m reg_grp.
Proof.
apply region_ok_intro; reg_num; [lin | lin | intros o Ho; lia |].
repeat (apply Forall_cons || apply Forall_nil). chunk_from (fp_c_mem _ _ _ _ FP).
Qed.
Lemma rok_meta k r v m (FP : free_pre k r v m) : region_ok src0segs (EV (xvf v)) m reg_meta.
Proof.
apply region_ok_intro; reg_num; [lin | lin | intros o Ho; apply (fp_w_meta _ _ _ _ FP); lin |].
repeat (apply Forall_cons || apply Forall_nil).
- chunk_from (fp_c_g16 _ _ _ _ FP).
- chunk_from (fp_c_g24 _ _ _ _ FP).
- chunk_from (fp_c_g28 _ _ _ _ FP).
- eapply chunk_ok_val; [val_tac | pose proof (fp_vals _ _ _ _ FP); cbn; lia | eapply (bytes_are_at _ _ _ _ _ (fp_c_g32 _ _ _ _ FP)); lin].
Qed.
Lemma rok_area k r v m (FP : free_pre k r v m) : region_ok src0segs (EV (xvf v)) m reg_area.
Proof.
apply region_ok_intro; reg_num; [lin | lin | intros o Ho; lia |].
repeat (apply Forall_cons || apply Forall_nil). chunk_from (fp_c_area _ _ _ _ FP).
Qed.
Lemma rok_ctx k r v m (FP : free_pre k r v m) : region_ok src0segs (EV (xvf v)) m reg_ctx.
Proof.
apply region_ok_intro; reg_num; [lin | lin | intros o Ho; lia |].
repeat (apply Forall_cons || apply Forall_nil). chunk_from (fp_c_ctx _ _ _ _ FP).
Qed.
Lemma rok_nl k r v m (FP : free_pre k r v m) : region_ok src0segs (EV (xvf v)) m reg_nl.
Proof.
apply region_ok_intro; reg_num; [lin | lin | intros o Ho; lia |].
repeat (apply Forall_cons || apply Forall_nil). chunk0_from (fp_c_nl _ _ _ _ FP).
Qed.
Lemma rok_stk k r v m (FP : free_pre k r v m) : region_ok src0segs (EV (xvf v)) m reg_stk.
Proof.
apply region_ok_intro; reg_num; [lin | lin | intros o Ho; apply (fp_w_stk _ _ _ _ FP); lin | apply Forall_nil].
Qed.
Lemma rok_tq k r v m (FP : free_pre k r v m) : k <> K3b -> region_ok src0segs (EV (xvf v)) m reg_tq.
Proof.
intros Hk. apply region_ok_intro; reg_num; [lin | lin | intros o Ho; lia |].
repeat (apply Forall_cons || apply Forall_nil).
pose proof (fp_c_tq _ _ _ _ FP) as C. destruct k; try (exfalso; exact (Hk eq_refl)); chunk_from C.
Qed.
Lemma rok_end1 k r v m (FP : free_pre k r v m) : region_ok src0segs (EV (xvf v)) m reg_end1.
Proof.
apply region_ok_intro; reg_num; [lin | lin | intros o Ho; lia |].
repeat (apply Forall_cons || apply Forall_nil). chunk0_from (fp_c_end _ _ _ _ FP).
Qed.
Lemma rok_end5 k r v m (FP : free_pre k r v m) : match r with R5 | R6 => region_ok src0segs (EV (xvf v)) m reg_end5 | _ => True end.
Proof.
pose proof (fp_c_end5 _ _ _ _ FP) as C. destruct r; try exact I; destruct C as (C4 & C5 & LE);
(apply region_ok_intro; reg_num; [lin | lin | intros o Ho; lia |]);
repeat (apply Forall_cons || apply Forall_nil);
first [chunk0_from C5 | chunk_from C4 | chunk0_from (fp_c_end _ _ _ _ FP)].
Qed.
Lemma rok_pn k r v m (FP : free_pre k r v m) : match r with R14 | R6 => region_ok src0segs (EV (xvf v)) m reg_pn | _ => True end.
Proof.
pose proof (fp_c_pn _ _ _ _ FP) as C. destruct r; try exact I;
(apply region_ok_intro; reg_num; [lin | lin | intros o Ho; lia |]);
repeat (apply Forall_cons || apply Forall_nil); chunk0_from C.
Qed.
Lemma regions_ok_all k r v m (FP : free_pre k r v m) : Forall (region_ok src0segs (EV (xvf v)) m) (free_mem k r).
Proof.
pose proof (rok_hdr _ _ _ _ FP). pose proof (rok_grp _ _ _ _ FP). pose proof (rok_meta _ _ _ _ FP). pose proof (rok_area _ _ _ _ FP).
pose proof (rok_ctx _ _ _ _ FP). pose proof (rok_nl _ _ _ _ FP). pose proof (rok_stk _ _ _ _ FP). pose proof (rok_tq _ _ _ _ FP) as T.
pose proof (rok_end1 _ _ _ _ FP). pose proof (rok_end5 _ _ _ _ FP) as E5. pose proof (rok_pn _ _ _ _ FP) as PN.
unfold free_mem, common_mem. destruct k, r; cbn [k_mem r_mem app] in *;
repeat (apply Forall_cons || apply Forall_nil); try assumption; apply T; discriminate.
Qed.
Theorem free_mem_ok k r v m (FP : free_pre k r v m) : mem_ok src0segs (EV (xvf v)) m (free_mem k r).
Proof.
split; [destruct k, r; vm_compute; reflexivity|]. split; [apply (regions_ok_all _ _ _ _ FP) | apply (pd_all _ _ _ _ FP)].
Qed.
Lemma atoms_ok_app E l1 l2 : atoms_ok E l1 -> atoms_ok E l2 -> atoms_ok E (l1 ++ l2).
Proof. induction l1 as [|[n f] t IH]; cbn; intros H1 H2; [exact H2|]. destruct H1; split; auto. Qed.
Lemma conds_ok_app E l1 l2 : conds_ok E l1 -> conds_ok E l2 -> conds_ok E (l1 ++ l2).
Proof. induction l1 as [|c t IH]; cbn; intros H1 H2; [exact H2|]. destruct H1; split; auto. Qed.
Lemma alias_ok_app E l1 l2 : alias_ok E l1 -> alias_ok E l2 -> alias_ok E (l1 ++ l2).
Proof. induction l1 as [|[a b] t IH]; cbn; intros H1 H2; [exact H2|]. destruct H1; split; auto. Qed.
End p.
Ltac atom_prep := match goal with FP : free_pre _ _ ?v _ |- _ =>
cbn [atoms_ok]; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite ?(ew_EV (xvf v) (xvf_range _ _ _ _ FP));
unfold aP, aSP, aTP, aG, aMEM, aOFF, aH3, aIDX, aRSV, aBITS, aAV, aFR, aAREA, aSC, aTQ, aSCL, aLAST, aML, aMP, aEND, aPN, aEP, aSEC;
cbn [xvf Nat.ltb Nat.leb nat_to_reg];
repeat match goal with |- _ /\ _ => split | |- True => exact I end end.
Section q. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma atoms_common k r v m (FP : free_pre k r v m) : atoms_ok (EV (xvf v)) common_atoms.
Proof.
pose proof (fp_sp _ _ _ _ FP) as [_ S16]. pose proof (fp_p _ _ _ _ FP) as [_ P16]. unfold fv_sp, fv_p in S16, P16.
unfold common_atoms. atom_prep; first [lin | exact S16 | exact P16 | apply Z.mod_1_r].
Qed.
Lemma atoms_k k r v m (FP : free_pre k r v m) : atoms_ok (EV (xvf v)) (k_atoms k).
Proof.
pose proof (fp_k _ _ _ _ FP) as K. pose proof (fp_bits _ _ _ _ FP) as HB. unfold bits_enc in HB.
destruct k; unfold k_atoms; atom_prep; first [lin | apply Z.mod_1_r | nia].
Qed.
Lemma atoms_r k r v m (FP : free_pre k r v m) : atoms_ok (EV (xvf v)) (r_atoms r).
Proof.
pose proof (fp_r _ _ _ _ FP) as R.
destruct r; unfold r_atoms; atom_prep; first [lin | apply Z.mod_1_r].
Qed.
End q.
Ltac den := match goal with FP : free_pre _ _ ?v _ |- _ =>
unfold SELF, MASK, ALL, FREED, MLCHK, XCL, XPG; unfold STR16;
cbn [sv_denot]; rewrite ?(ew_EV (xvf v) (xvf_range _ _ _ _ FP));
unfold aP, aSP, aTP, aG, aMEM, aOFF, aH3, aIDX, aRSV, aBITS, aAV, aFR, aAREA, aSC, aTQ, aSCL, aLAST, aML, aMP, aEND, aPN, aEP, aSEC;
cbn [xvf Nat.ltb Nat.leb nat_to_reg]; rewrite ?Z.add_0_r end.
Ltac weq := apply (proj2 (word_eq _ _)).
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma bits_hyps k r v m (FP : free_pre k r v m) : 0 <= fv_last v < 32 /\ 0 <= fv_sc v < 64 /\ 0 <= fv_ml v /\ fv_ml v < 2 ^ 52.
Proof. lin. Qed.
Lemma al_h3idx k r v m (FP : free_pre k r v m) : sv_denot (EV (xvf v)) (SAlu ALU_AND (SOff aH3 0) (SLit 31)) = sv_denot (EV (xvf v)) (SOff aIDX 0).
Proof. weq. den. rewrite alu64_and, !lit64_small by lin. apply (fp_h3idx _ _ _ _ FP). Qed.
Lemma al_pmem k r v m (FP : free_pre k r v m) : sv_denot (EV (xvf v)) (SAlu ALU_SUB (SOff aP 0) (SAlu ALU_SLL (SOff aOFF 0) (SLit 4))) = sv_denot (EV (xvf v)) (SOff aMEM 16).
Proof.
weq. den. rewrite alu64_sub, alu64_sll, !lit64_small by lin. unfold fv_p.
unfold sll64, sub64. rewrite Z.shiftl_mul_pow2 by lia. change (4 mod 64) with 4. change (2^4) with 16.
pose proof (lin_facts _ _ _ _ FP) as L; cbn zeta in L; unfold fv_p in L.
rewrite (Z.mod_small (fv_off v * 16)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma al_garea k r v m (FP : free_pre k r v m) : sv_denot (EV (xvf v)) (SAlu ALU_AND (SOff aG 0) (SLit (-4096))) = sv_denot (EV (xvf v)) (SOff aAREA 0).
Proof.
weq. den. rewrite alu64_and, (lit64_unsigned (-4096)), !lit64_small by lin.
change ((-4096) mod 2 ^ 64) with (2 ^ 64 - 2 ^ 12). rewrite land_neg_pow2_u64 by lin.
pose proof (fp_ar _ _ _ _ FP) as (_ & _ & AM & A4 & A5 & _). change (2 ^ 12) with 4096.
pose proof (lin_facts _ _ _ _ FP) as L; cbn zeta in L.
rewrite <- (Z.mod_unique (fv_g v) 4096 (fv_area v / 4096) (fv_g v - fv_area v)); [lia | left; lia |].
pose proof (proj2 (Z.div_exact (fv_area v) 4096 ltac:(lia)) AM). lia.
Qed.
Lemma al_ep k r v m (FP : free_pre k r v m) : sv_denot (EV (xvf v)) (SAlu ALU_SUB (SOff aEND 0) (SOff aP 0)) = sv_denot (EV (xvf v)) (SOff aEP 0).
Proof. weq. den. rewrite alu64_sub, !lit64_small by lin. unfold sub64, fv_p. rewrite Z.mod_small; [reflexivity|lin]. Qed.
Lemma alias_common k r v m (FP : free_pre k r v m) : alias_ok (EV (xvf v)) common_alias.
Proof.
unfold common_alias. cbn [alias_ok]. split; [apply (al_h3idx _ _ _ _ FP)|]. split; [apply (al_pmem _ _ _ _ FP)|]. split; [apply (al_garea _ _ _ _ FP)|]. split; [apply (al_ep _ _ _ _ FP)|]. exact I.
Qed.
Lemma bits_facts k r v m (FP : free_pre k r v m) :
fv_bits v = bits_enc (fv_last v) (fv_sc v) (fv_ml v) /\ 0 <= fv_last v < 32 /\ 0 <= fv_sc v < 64 /\ 0 <= fv_ml v /\ fv_ml v < 2 ^ 52.
Proof. split; [apply (fp_bits _ _ _ _ FP) | lin]. Qed.
End s.
Ltac bitsF := match goal with FP : free_pre _ _ _ _ |- _ =>
let B := fresh "B" in let L1 := fresh "L1" in let L2 := fresh "L2" in let L3 := fresh "L3" in let L4 := fresh "L4" in
destruct (bits_facts _ _ _ _ FP) as (B & L1 & L2 & L3 & L4); rewrite B end.
Section a0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma al_last k r v m (FP : free_pre k r v m) :
sv_denot (EV (xvf v)) (SAlu ALU_AND (SOff aBITS 0) (SLit 31)) = sv_denot (EV (xvf v)) (SOff aLAST 0).
Proof. weq. den. rewrite alu64_and, !lit64_small by lin. bitsF. apply bits_land31; lia. Qed.
Lemma al_last0 k r v m (FP : free_pre k r v m) : fv_last v = 0 ->
sv_denot (EV (xvf v)) (SAlu ALU_AND (SOff aBITS 0) (SLit 31)) = sv_denot (EV (xvf v)) (SLit 0).
Proof. intros H0. weq. den. rewrite alu64_and, !lit64_small by lin. bitsF. rewrite bits_land31; lia. Qed.
Lemma al_sc k r v m (FP : free_pre k r v m) :
sv_denot (EV (xvf v)) (SAlu ALU_SRL (SAlu ALU_SLL (SOff aBITS 0) (SLit 52)) (SLit 58)) = sv_denot (EV (xvf v)) (SOff aSC 0).
Proof.
weq. den. rewrite alu64_srl, alu64_sll, !lit64_small by lin. change (52 mod 64) with 52. change (58 mod 64) with 58.
bitsF. apply bits_sc; lia.
Qed.
Lemma al_sc63 k r v m (FP : free_pre k r v m) : fv_sc v = 63 ->
sv_denot (EV (xvf v)) (SAlu ALU_SRL (SAlu ALU_SLL (SOff aBITS 0) (SLit 52)) (SLit 58)) = sv_denot (EV (xvf v)) (SLit 63).
Proof.
intros H. weq. den. rewrite alu64_srl, alu64_sll, !lit64_small by lin. change (52 mod 64) with 52. change (58 mod 64) with 58.
bitsF. rewrite bits_sc; lia.
Qed.
Lemma al_tq k r v m (FP : free_pre k r v m) :
sv_denot (EV (xvf v)) (SAlu ALU_SLL (SOff aSC 0) (SLit 1)) = sv_denot (EV (xvf v)) (SOff aTQ (- TBL)).
Proof.
weq. den. rewrite alu64_sll, !lit64_small by lin. change (1 mod 64) with 1. unfold sll64. rewrite Z.shiftl_mul_pow2 by lia.
rewrite Z.mod_small by lin. lin.
Qed.
Lemma al_ml0 k r v m (FP : free_pre k r v m) : fv_ml v = 0 ->
sv_denot (EV (xvf v)) (SAlu ALU_SRL (SOff aBITS 0) (SLit 12)) = sv_denot (EV (xvf v)) (SLit 0).
Proof. intros H. weq. den. rewrite alu64_srl, !lit64_small by lin. change (12 mod 64) with 12. bitsF. rewrite bits_shiftr12; lia. Qed.
Lemma al_ml k r v m (FP : free_pre k r v m) :
sv_denot (EV (xvf v)) (SAlu ALU_SRL (SOff aBITS 0) (SLit 12)) = sv_denot (EV (xvf v)) (SOff aML 0).
Proof. weq. den. rewrite alu64_srl, !lit64_small by lin. change (12 mod 64) with 12. bitsF. rewrite bits_shiftr12; lia. Qed.
Lemma al_2sc k r v m (FP : free_pre k r v m) :
sv_denot (EV (xvf v)) (SAlu ALU_AND (SAlu ALU_SRL (SOff aBITS 0) (SLit 5)) (SLit 126)) = sv_denot (EV (xvf v)) (SOff aTQ (- TBL)).
Proof.
weq. den. rewrite alu64_and, alu64_srl, !lit64_small by lin. change (5 mod 64) with 5. bitsF. rewrite bits_2sc by lia. lin.
Qed.
Lemma al_mp k r v m (FP : free_pre k r v m) :
sv_denot (EV (xvf v)) (SAlu ALU_AND (SOff aBITS 0) (SLit (-4096))) = sv_denot (EV (xvf v)) (SOff aMP 0).
Proof.
weq. den. rewrite alu64_and, (lit64_unsigned (-4096)), !lit64_small by lin. change ((-4096) mod 2 ^ 64) with (2 ^ 64 - 4096).
bitsF. rewrite bits_maplen_bytes by lia. lia.
Qed.
Lemma al_xcl k r v m (FP : free_pre k r v m) :
fv_end v = fv_mem v + 12 + 16 * fv_scl v * (fv_idx v + 1) ->
sv_denot (EV (xvf v)) XCL = sv_denot (EV (xvf v)) (SOff aEND (-12)).
Proof.
intros HE. weq. den. rewrite !alu64_add, mul64_unsigned, !alu64_sll, !lit64_small by lin. change (4 mod 64) with 4.
pose proof (lin_facts _ _ _ _ FP) as L; cbn zeta in L. unfold CEIL in L.
unfold sll64, mul64, add64. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
assert (BSI : 0 <= fv_scl v <= 8191 /\ 0 <= fv_idx v <= 31) by lia.
assert (0 <= fv_scl v * 16 * fv_idx v <= 8191 * 16 * 31) by (clear -BSI; nia). clear BSI.
rewrite (Z.mod_small (fv_scl v * 16)) by lia. rewrite (Z.mod_small (fv_scl v * 16 * fv_idx v)) by lia.
rewrite (Z.mod_small (fv_mem v + _)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma al_xpg k r v m (FP : free_pre k r v m) :
fv_idx v = 0 -> fv_end v = fv_mem v + 4096 * fv_ml v - 4 -> 1 <= fv_ml v ->
sv_denot (EV (xvf v)) XPG = sv_denot (EV (xvf v)) (SOff aEND (-12)).
Proof.
intros HI HE HM. weq. den. rewrite HI.
pose proof (lin_facts _ _ _ _ FP) as L; cbn zeta in L. unfold CEIL in L.
rewrite !alu64_add, mul64_unsigned, !lit64_small by lia.
unfold mul64, add64. rewrite Z.mul_0_r. change (0 mod 2 ^ 64) with 0. rewrite Z.add_0_r.
rewrite (Z.mod_small (fv_mem v + -16 + _)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma al_code k r v m (FP : free_pre k r v m) code :
fv_h3 v = fv_idx v + 32 * code -> 0 <= code < 8 ->
sv_denot (EV (xvf v)) (SAlu ALU_SRL (SOff aH3 0) (SLit 5)) = sv_denot (EV (xvf v)) (SLit code).
Proof.
intros HH HC. weq. den. rewrite alu64_srl, !lit64_small by lin. change (5 mod 64) with 5.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32. pose proof (lin_facts _ _ _ _ FP) as L; cbn zeta in L.
rewrite HH. rewrite Z.add_comm, Z.mul_comm, Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.
Lemma al_code_rsv k r v m (FP : free_pre k r v m) :
fv_h3 v = fv_idx v + 32 * fv_rsv v -> fv_rsv v < 8 ->
sv_denot (EV (xvf v)) (SAlu ALU_SRL (SOff aH3 0) (SLit 5)) = sv_denot (EV (xvf v)) (SOff aRSV 0).
Proof.
intros HH HC. rewrite (al_code _ _ _ _ FP (fv_rsv v) HH ltac:(lin)). weq. den. reflexivity.
Qed.
Lemma al_pn k r v m (FP : free_pre k r v m) :
fv_pn v = fv_end v - fv_rsv v -> fv_rsv v <= fv_end v - fv_p v ->
sv_denot (EV (xvf v)) (SAlu ALU_SUB (SOff aEND 0) (SOff aRSV 0)) = sv_denot (EV (xvf v)) (SOff aPN 0).
Proof. intros HP HR. weq. den. rewrite alu64_sub, !lit64_small by lin. unfold sub64. rewrite Z.mod_small by lin. lin. Qed.
Lemma al_end5 k r v m (FP : free_pre k r v m) :
fv_rsv v = 5 -> fv_rsv v <= fv_end v - fv_p v ->
sv_denot (EV (xvf v)) (SAlu ALU_SUB (SOff aEND 0) (SOff aRSV 0)) = sv_denot (EV (xvf v)) (SOff aEND (-5)).
Proof. intros HP HR. weq. den. rewrite alu64_sub, !lit64_small by lin. unfold sub64. rewrite Z.mod_small by lin. lin. Qed.
Lemma alias_k k r v m (FP : free_pre k r v m) : alias_ok (EV (xvf v)) (k_alias k).
Proof.
pose proof (fp_k _ _ _ _ FP) as K. destruct k; unfold k_alias; cbn [alias_ok].
- destruct K as (M0 & _ & _ & _ & E). repeat split.
+ apply (al_last _ _ _ _ FP). + apply (al_sc _ _ _ _ FP). + apply (al_tq _ _ _ _ FP). + apply (al_ml0 _ _ _ _ FP M0).
+ apply (al_2sc _ _ _ _ FP). + apply (al_xcl _ _ _ _ FP E).
- destruct K as (M1 & _ & _ & _ & _ & _ & E). repeat split.
+ apply (al_last _ _ _ _ FP). + apply (al_sc _ _ _ _ FP). + apply (al_tq _ _ _ _ FP). + apply (al_ml _ _ _ _ FP).
+ apply (al_2sc _ _ _ _ FP). + apply (al_xcl _ _ _ _ FP E).
- destruct K as (M1 & _ & _ & _ & _ & I0 & L0 & E). repeat split.
+ apply (al_last0 _ _ _ _ FP L0). + apply (al_sc _ _ _ _ FP). + apply (al_tq _ _ _ _ FP). + apply (al_ml _ _ _ _ FP).
+ apply (al_mp _ _ _ _ FP). + apply (al_xpg _ _ _ _ FP I0 E M1).
- destruct K as (M1 & S63 & _ & I0 & L0 & E). repeat split.
+ apply (al_last0 _ _ _ _ FP L0). + apply (al_sc63 _ _ _ _ FP S63). + apply (al_ml _ _ _ _ FP).
+ apply (al_mp _ _ _ _ FP). + apply (al_xpg _ _ _ _ FP I0 E M1).
Qed.
Lemma alias_r k r v m (FP : free_pre k r v m) : alias_ok (EV (xvf v)) (r_alias r).
Proof.
pose proof (fp_r _ _ _ _ FP) as R. destruct r; unfold r_alias; cbn [alias_ok].
- repeat split. apply (al_code _ _ _ _ FP 0); [lia|lia].
- destruct R as (H & B & P & Q). repeat split; [apply (al_code_rsv _ _ _ _ FP H); lia | apply (al_pn _ _ _ _ FP P Q)].
- destruct R as (H & B & Q). repeat split; [apply (al_code _ _ _ _ FP 5); lia | apply (al_end5 _ _ _ _ FP B Q)].
- destruct R as (H & B & P & Q). repeat split; [apply (al_code _ _ _ _ FP 5); lia | apply (al_pn _ _ _ _ FP P Q)].
Qed.
End a0.
Ltac cond_prep := unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite ?branch_geu, ?branch_ltu, ?branch_eq, ?branch_ne; den.
Section b0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma U_SELF k r v m (FP : free_pre k r v m) : bv_unsigned (sv_denot (EV (xvf v)) SELF) = sx32 (2 ^ fv_idx v).
Proof.
den. rewrite sllw_rr_unsigned, !lit64_small by lin. rewrite sllw_1 by lin. rewrite Z.mod_small by lin. reflexivity.
Qed.
Lemma cd_lastidx k r v m (FP : free_pre k r v m) : acond_ok (EV (xvf v)) (mkAC BC_GEU (SOff aLAST 0) (SOff aIDX 0)).
Proof. cond_prep. rewrite !lit64_small by lin. apply negb_true_iff. apply Z.ltb_ge. lin. Qed.
Lemma cd_avbit k r v m (FP : free_pre k r v m) : acond_ok (EV (xvf v)) (mkAC BC_EQ (SAlu ALU_AND (SExt true 32 (SOff aAV 0)) SELF) (SLit 0)).
Proof.
pose proof (U_SELF _ _ _ _ FP) as US. unfold acond_ok; cbn [ac_c ac_a ac_b]. rewrite branch_eq. apply Z.eqb_eq.
change (sv_denot (EV (xvf v)) (SAlu ALU_AND (SExt true 32 (SOff aAV 0)) SELF)) with
(alu64 ALU_AND (sv_denot (EV (xvf v)) (SExt true 32 (SOff aAV 0))) (sv_denot (EV (xvf v)) SELF)).
rewrite alu64_and, US, U_sext32. den. rewrite !lit64_small by lin. change (0 mod 2 ^ 64) with 0.
pose proof (lin_facts _ _ _ _ FP) as L; cbn zeta in L.
destruct (land_sx32_bit (fv_av v) (fv_idx v) ltac:(lia) ltac:(lia)) as [-> E]. apply (proj2 E). apply (fp_avbit _ _ _ _ FP).
Qed.
Lemma cd_frbit k r v m (FP : free_pre k r v m) : acond_ok (EV (xvf v)) (mkAC BC_EQ (SAlu ALU_AND (SExt true 32 (SOff aFR 0)) SELF) (SLit 0)).
Proof.
pose proof (U_SELF _ _ _ _ FP) as US. unfold acond_ok; cbn [ac_c ac_a ac_b]. rewrite branch_eq. apply Z.eqb_eq.
change (sv_denot (EV (xvf v)) (SAlu ALU_AND (SExt true 32 (SOff aFR 0)) SELF)) with
(alu64 ALU_AND (sv_denot (EV (xvf v)) (SExt true 32 (SOff aFR 0))) (sv_denot (EV (xvf v)) SELF)).
rewrite alu64_and, US, U_sext32. den. rewrite !lit64_small by lin. change (0 mod 2 ^ 64) with 0.
pose proof (lin_facts _ _ _ _ FP) as L; cbn zeta in L.
destruct (land_sx32_bit (fv_fr v) (fv_idx v) ltac:(lia) ltac:(lia)) as [-> E]. apply (proj2 E). apply (fp_frbit _ _ _ _ FP).
Qed.
Lemma U_MASK k r v m (FP : free_pre k r v m) : bv_unsigned (sv_denot (EV (xvf v)) MASK) = sx32 (Z.lor (fv_av v) (fv_fr v)).
Proof.
change (sv_denot (EV (xvf v)) MASK) with (alu64 ALU_OR (sv_denot (EV (xvf v)) (SExt true 32 (SOff aAV 0))) (sv_denot (EV (xvf v)) (SExt true 32 (SOff aFR 0)))).
rewrite alu64_or, !U_sext32. den. rewrite !lit64_small by lin. apply lor_sx32.
Qed.
Lemma cd_maskbit k r v m (FP : free_pre k r v m) : acond_ok (EV (xvf v)) (mkAC BC_EQ (SAlu ALU_AND MASK SELF) (SLit 0)).
Proof.
pose proof (U_SELF _ _ _ _ FP) as US. pose proof (U_MASK _ _ _ _ FP) as UM. unfold acond_ok; cbn [ac_c ac_a ac_b]. rewrite branch_eq. apply Z.eqb_eq.
change (sv_denot (EV (xvf v)) (SAlu ALU_AND MASK SELF)) with (alu64 ALU_AND (sv_denot (EV (xvf v)) MASK) (sv_denot (EV (xvf v)) SELF)).
rewrite alu64_and, US, UM. cbn [sv_denot]. change (bv_unsigned (Z_to_bv 64 0)) with 0.
pose proof (lin_facts _ _ _ _ FP) as L; cbn zeta in L.
destruct (land_sx32_bit (Z.lor (fv_av v) (fv_fr v)) (fv_idx v) ltac:(lia) ltac:(apply Z.lor_nonneg; lia)) as [-> E]. apply (proj2 E).
rewrite Z.lor_spec, (fp_avbit _ _ _ _ FP), (fp_frbit _ _ _ _ FP). reflexivity.
Qed.
Lemma cd_sclo k r v m (FP : free_pre k r v m) : fv_scl v * fv_idx v <= fv_off v ->
acond_ok (EV (xvf v)) (mkAC BC_GEU (SOff aOFF 0) (SMd M_MUL (SOff aSCL 0) (SOff aIDX 0))).
Proof.
intros H. cond_prep. rewrite mul64_unsigned, !lit64_small by lin. apply negb_true_iff. apply Z.ltb_ge.
pose proof (lin_facts _ _ _ _ FP) as L; cbn zeta in L. unfold mul64.
assert (BSI : 0 <= fv_scl v <= 8191 /\ 0 <= fv_idx v <= 31) by lia. assert (0 <= fv_scl v * fv_idx v <= 8191 * 31) by (clear -BSI; nia). clear BSI. rewrite Z.mod_small by lia. lia.
Qed.
Lemma cd_schi k r v m (FP : free_pre k r v m) : fv_off v < fv_scl v * (fv_idx v + 1) ->
acond_ok (EV (xvf v)) (mkAC BC_LTU (SOff aOFF 0) (SMd M_MUL (SOff aIDX 1) (SOff aSCL 0))).
Proof.
intros H. unfold acond_ok; cbn [ac_c ac_a ac_b]. rewrite branch_ltu.
cbn [sv_denot]. rewrite ?(ew_EV (xvf v) (xvf_range _ _ _ _ FP)). unfold aOFF, aIDX, aSCL. cbn [xvf Nat.ltb Nat.leb nat_to_reg]. rewrite ?Z.add_0_r.
pose proof (lin_facts _ _ _ _ FP) as L; cbn zeta in L.
rewrite mul64_unsigned, !lit64_small by lia. apply Z.ltb_lt. unfold mul64.
assert (BSI : 0 <= fv_scl v <= 8191 /\ 0 <= fv_idx v <= 31) by lia. assert (0 <= (fv_idx v + 1) * fv_scl v <= 32 * 8191) by (clear -BSI; nia). clear BSI. rewrite Z.mod_small by lia. lia.
Qed.
Lemma cd_mlchk k r v m (FP : free_pre k r v m) : 1 <= fv_ml v -> fv_off v <= 256 * fv_ml v - 1 ->
acond_ok (EV (xvf v)) (mkAC BC_GEU MLCHK (SOff aOFF 0)).
Proof.
intros H1 H2. cond_prep. rewrite alu64_add, alu64_sll, (lit64_unsigned (-1)), !lit64_small by lin. change (8 mod 64) with 8.
apply negb_true_iff. apply Z.ltb_ge. pose proof (lin_facts _ _ _ _ FP) as L; cbn zeta in L.
unfold sll64, add64. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
rewrite (Z.mod_small (fv_ml v * 256)) by lia.
replace (fv_ml v * 256 + (2 ^ 64 - 1)) with ((fv_ml v * 256 - 1) + 1 * 2 ^ 64) by lia. rewrite Z.mod_add, Z.mod_small by lia. lia.
Qed.
Lemma cd_eprsv k r v m (FP : free_pre k r v m) : fv_rsv v <= fv_end v - fv_p v ->
acond_ok (EV (xvf v)) (mkAC BC_GEU (SOff aEP 0) (SOff aRSV 0)).
Proof. intros H. cond_prep. rewrite !lit64_small by lin. apply negb_true_iff. apply Z.ltb_ge. lin. Qed.
Lemma conds_common k r v m (FP : free_pre k r v m) : conds_ok (EV (xvf v)) common_conds.
Proof.
unfold common_conds. cbn [conds_ok].
split; [apply (cd_lastidx _ _ _ _ FP)|]. split; [apply (cd_avbit _ _ _ _ FP)|]. split; [apply (cd_frbit _ _ _ _ FP)|].
split; [apply (cd_maskbit _ _ _ _ FP)|]. exact I.
Qed.
Lemma conds_k k r v m (FP : free_pre k r v m) : conds_ok (EV (xvf v)) (k_conds k).
Proof.
pose proof (fp_k _ _ _ _ FP) as K. destruct k; unfold k_conds; cbn [conds_ok].
- destruct K as (_ & _ & _ & [A B] & _). split; [apply (cd_sclo _ _ _ _ FP A)|]. split; [apply (cd_schi _ _ _ _ FP B)|]. exact I.
- destruct K as (M1 & _ & _ & [A B] & C & _). split; [apply (cd_sclo _ _ _ _ FP A)|]. split; [apply (cd_schi _ _ _ _ FP B)|].
split; [apply (cd_mlchk _ _ _ _ FP M1 C)|]. exact I.
- destruct K as (M1 & _ & _ & [A B] & C & _). split; [apply (cd_sclo _ _ _ _ FP A)|]. split; [apply (cd_schi _ _ _ _ FP B)|].
split; [apply (cd_mlchk _ _ _ _ FP M1 C)|]. exact I.
- destruct K as (M1 & _ & C & _). split; [apply (cd_mlchk _ _ _ _ FP M1 C)|]. exact I.
Qed.
Lemma conds_r k r v m (FP : free_pre k r v m) : conds_ok (EV (xvf v)) (r_conds r).
Proof.
pose proof (fp_r _ _ _ _ FP) as R. destruct r; unfold r_conds; cbn [conds_ok]; [exact I| | |];
(split; [apply (cd_eprsv _ _ _ _ FP); lia | exact I]).
Qed.
Lemma free_regs_ok v : regs_ok (EV (xvf v)) regs_init (fv_regs v).
Proof. apply regs_ok_init. intros n Hn. rewrite xvf_reg by lia. apply Z_to_bv_bv_unsigned. Qed.
Theorem free_entry_st_ok k r v m (FP : free_pre k r v m) :
st_ok src0segs (EV (xvf v)) (ss_free k r) (mkst (fv_regs v) (Z_to_bv 64 src0_A_free) m (seg_rom src0segs)).
Proof.
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_resv ss_regs ss_mem ss_facts ss_free resv_denot].
repeat (split; [reflexivity|]). split; [apply free_regs_ok|]. split; [apply (free_mem_ok _ _ _ _ FP)|].
unfold free_facts. split; [| split].
- apply atoms_ok_app; [apply (atoms_common _ _ _ _ FP) | apply atoms_ok_app; [apply (atoms_k _ _ _ _ FP) | apply (atoms_r _ _ _ _ FP)]].
- apply conds_ok_app; [apply (conds_common _ _ _ _ FP) | apply conds_ok_app; [apply (conds_k _ _ _ _ FP) | apply (conds_r _ _ _ _ FP)]].
- apply alias_ok_app; [apply (alias_common _ _ _ _ FP) | apply alias_ok_app; [apply (alias_k _ _ _ _ FP) | apply (alias_r _ _ _ _ FP)]].
Qed.
End b0.
