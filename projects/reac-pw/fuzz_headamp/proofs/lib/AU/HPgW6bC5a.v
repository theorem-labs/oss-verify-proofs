(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6bC5.v at f3898085bda (the model values
   of ent_build's case 5, their arithmetic, the pod's byte list and the shape of the case's head run) for
   reac-pw/fuzz_headamp's image B: image B's own code and registers, its two pointer-overflow tests (each shown not
   taken by hand), the engine kit of lib/AU/HPgW6bBase.v (hb_entry / hb_shok / hb_tbl / HBx / hb_SH) in place of
   role's, and the block post of lib/AU/HPgSteps.v (hdu_blk_postE) in place of role's own post; the leaf, the
   keep-across-a-run step and the register / byte helpers are written here for that post. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, whose loaded bytes there equal the pin's):
   the HEAD of ent_build's case 5 inside LLVMFuzzerTestOneInput (0x80c40), from the case entry 0x81e6c to the
   `jal` to __asan_memcpy at 0x81ec4 (which returns to 0x81ec8). Proves no function (kind: segment lemma).

   THE CODE (registers as at a case entry, HPgW6bBase.hw6b_in: s1 = R, s11 = the shadow offset, s2 = c the cursor,
   a7 = c - 1, t1 = |r| + 1, s4 = |r|, a6 = 1, a3 = the kind byte sign-extended; [R+0x118] = F + 0x218 = &e62.body):
     0x81e6c  beqz s4 -> 0x82214                       no byte left
     0x81e70  addi a0,s2,1 / bltu a6,a0 -> 0x81e7c     the cursor's pointer-overflow test (else `unimp` 0x83a14)
     0x81e7c  mv s7,a3; srli a0,s2,3; add a0,a0,s11; lb a0,0(a0); ld s5,0x118(s1); bnez a0 -> 0x82828
                                                        the input byte's shadow check (its slow block)
     0x81e94  lbu a0,0(s2) (= n); s10 := t1 - 2 (= what is left after it); s2 := a7 + 2; s4 := n & 0x1f
     0x81ea4  bltu s4,s10 -> 0x81eac, else 0x81ea8 s4 := s10        s4 = min(n mod 32, what is left)
     0x81eac  not a0,s2 / bgeu a0,s4 -> 0x81eb8         the copy's pointer-overflow test (else `unimp` 0x83a14)
     0x81eb8  a0 := s5; a1 := s2; a2 := s4; jal 0x51d8c (__asan_memcpy), returning to 0x81ec8
     0x82214  mv s7,a3; s10 := 0; ld s5,0x118(s1); bgeu s4,zero -> 0x81ea8 (always, s4 = 0 there)
   The engine decides the first test from the cursor's interval and a6 pinned to the literal 1; the second one is
   taken by hand on both arms (its `not` leaves no interval), and its `unimp` arm is killed from c + 1 <= 2 ^ 47.
   The real-frame cells this piece reads: [R+0x118]; the cells it may write: none (the write windows of the kit's
   entry state are [R+0x58, R+0x60), [R+0x110, R+0x118) and e62 = [F+0x210, F+0x278)). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSeg HPgSteps HPgCaseBJ HPgW6bBase HPgCaseB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ======================================== the pcs ======================================== *)
Definition HC5_RET : Z := 0x81ec8.      (* after the `jal` to __asan_memcpy at 0x81ec4 *)

(* ======================================== the model's values ========================================
   (n, r1) = fuzz_u8 r; p = firstn (n mod 32) r1 (fuzz_take), the bytes the memcpy copies. *)
Definition hc5_k (r : list byte) : nat := Z.to_nat (fst (fuzz_u8 r) mod 32).
Definition hc5_r1 (r : list byte) : list byte := snd (fuzz_u8 r).
Definition hc5_p (r : list byte) : list byte := firstn (hc5_k r) (hc5_r1 r).
Definition hc5_n (r : list byte) : Z := Z.of_nat (length (hc5_p r)).
Definition hc5_left (r : list byte) : Z := Z.of_nat (length (hc5_r1 r)).
(* the memcpy source: c + 1 after a byte, c when none is left *)
Definition hc5_src (c : Z) (r : list byte) : Z := c + Z.of_nat (length r) - Z.of_nat (length (hc5_r1 r)).
(* the kind byte as `srai a3,a0,0x38` leaves it *)
Definition hc5_kds (kd : Z) : Z := kd - 256 * (kd / 128).

Lemma hc5_nil : forall c, hc5_src c [] = c /\ hc5_n [] = 0 /\ hc5_left [] = 0 /\ hc5_p [] = [].
Proof.
intros c. unfold hc5_src, hc5_n, hc5_left, hc5_p, hc5_r1, hc5_k. cbn [fuzz_u8 fst snd]. rewrite firstn_nil.
cbn [length]. split; [lia|]. split; [reflexivity|]. split; reflexivity.
Qed.
Lemma hc5_cons : forall c (m : byte) r1, hc5_src c (m :: r1) = c + 1 /\ hc5_left (m :: r1) = Z.of_nat (length r1) /\
  hc5_n (m :: r1) = Z.min (bv_unsigned m mod 32) (Z.of_nat (length r1)) /\
  hc5_p (m :: r1) = firstn (Z.to_nat (bv_unsigned m mod 32)) r1.
Proof.
intros c m r1. pose proof (byte_range m) as Hm.
unfold hc5_src, hc5_n, hc5_left, hc5_p, hc5_r1, hc5_k. cbn [fuzz_u8 fst snd length].
split; [lia|]. split; [reflexivity|]. split; [|reflexivity].
rewrite length_firstn, Nat2Z.inj_min, Z2Nat.id by (apply Z.mod_pos_bound; lia). reflexivity.
Qed.
Lemma hc5_bounds : forall c r, c <= hc5_src c r /\ hc5_src c r + hc5_n r <= c + Z.of_nat (length r) /\
  0 <= hc5_n r <= 31 /\ hc5_n r <= hc5_left r /\ hc5_src c r + hc5_left r = c + Z.of_nat (length r) /\
  (length (hc5_p r) <= 31)%nat /\ hc5_n r = Z.of_nat (length (hc5_p r)).
Proof.
intros c [|m r1].
- destruct (hc5_nil c) as (Q1 & Q2 & Q3 & Q4). rewrite Q1, Q2, Q3, Q4. cbn [length]. lia.
- destruct (hc5_cons c m r1) as (Q1 & Q2 & Q3 & Q4). pose proof (byte_range m) as Hm.
  pose proof (Z.mod_pos_bound (bv_unsigned m) 32 ltac:(lia)) as Hm32.
  assert (Hl : (length (hc5_p (m :: r1)) <= 31)%nat) by (rewrite Q4, length_firstn; lia).
  split; [lia|]. split; [rewrite Q1, Q3; cbn [length]; lia|]. split; [rewrite Q3; lia|].
  split; [rewrite Q3, Q2; lia|]. split; [rewrite Q1, Q2; cbn [length]; lia|]. split; [exact Hl | reflexivity].
Qed.
Lemma hc5_skip_len : forall r, Z.of_nat (length (skipn (hc5_k r) (hc5_r1 r))) = hc5_left r - hc5_n r.
Proof.
intros r. unfold hc5_left, hc5_n, hc5_p. rewrite length_skipn, length_firstn. lia.
Qed.
(* Model.ent_build case 5 *)
Lemma hc5_model : forall (b : byte) (r : list byte), bv_unsigned b mod 10 = 5 ->
  ent_build (b :: r) = (ent_text (hc5_p r) (negb (Z.testbit (bv_unsigned b) 7)), skipn (hc5_k r) (hc5_r1 r)).
Proof.
intros b r H. unfold ent_build, hc5_p, hc5_k, hc5_r1, fuzz_take. cbn [fuzz_u8 fst snd]. rewrite H.
destruct (fuzz_u8 r) as [n r1]. reflexivity.
Qed.
(* the 104 bytes of the pod: e62.type, e62.size, the body and zeros (with the NUL, the body's last byte is zero) *)
Lemma hc5_ent_mem : forall p (nul : bool), (length p <= 95)%nat ->
  ent_mem (ent_text p nul) = le32 8 ++ le32 (Z.of_nat (length p) + (if nul then 1 else 0)) ++ p ++ zeros (96 - length p).
Proof.
intros p nul Hp. unfold ent_mem, ent_text. cbn [e_type e_size e_body]. rewrite firstn_all2 by lia.
destruct nul.
- rewrite length_app. cbn [length].
  replace (96 - (length p + 1))%nat with (95 - length p)%nat by lia.
  replace (96 - length p)%nat with (S (95 - length p)) by lia.
  rewrite <- app_assoc. cbn [app]. unfold zeros. cbn [repeat]. rewrite Nat2Z.inj_add. reflexivity.
- rewrite Z.add_0_r. reflexivity.
Qed.

(* s4 = n & 0x1f, as the engine computes it from the loaded byte (atom 35) *)
Lemma hc5_s4_val : forall E m, ew E 35 = Z_to_bv 64 m -> 0 <= m < 256 ->
  sv_denot E (SAlu ALU_AND (SExt false 8 (SOff 35 0)) (SLit 31)) = Z_to_bv 64 (m mod 32).
Proof.
intros E m Hm Hr.
transitivity (sv_denot (cb_envz m) (SAlu ALU_AND (SExt false 8 (SOff 35 0)) (SLit 31)));
  [cbn [sv_denot ew cb_envz]; rewrite Hm; reflexivity|].
apply bv_eq. apply Z.eqb_eq.
exact (cb_all256 (fun m => bv_unsigned (sv_denot (cb_envz m)
  (SAlu ALU_AND (SExt false 8 (SOff 35 0)) (SLit 31))) =? bv_unsigned (Z_to_bv 64 (m mod 32)))
  ltac:(vm_compute; reflexivity) m Hr).
Qed.
Lemma hc5_s4z_val : forall E m, ew E 35 = Z_to_bv 64 m -> 0 <= m < 256 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SExt false 8 (SOff 35 0)) (SLit 31)) (SLit 0)) = Z_to_bv 64 (m mod 32).
Proof.
intros E m Hm Hr.
transitivity (sv_denot (cb_envz m) (SAlu ALU_ADD (SAlu ALU_AND (SExt false 8 (SOff 35 0)) (SLit 31)) (SLit 0)));
  [cbn [sv_denot ew cb_envz]; rewrite Hm; reflexivity|].
apply bv_eq. apply Z.eqb_eq.
exact (cb_all256 (fun m => bv_unsigned (sv_denot (cb_envz m)
  (SAlu ALU_ADD (SAlu ALU_AND (SExt false 8 (SOff 35 0)) (SLit 31)) (SLit 0))) =? bv_unsigned (Z_to_bv 64 (m mod 32)))
  ltac:(vm_compute; reflexivity) m Hr).
Qed.
Lemma hc5_s4_U : forall E m, ew E 35 = Z_to_bv 64 m -> 0 <= m < 256 ->
  U E (SAlu ALU_AND (SExt false 8 (SOff 35 0)) (SLit 31)) = m mod 32.
Proof.
intros E m Hm Hr. unfold U. rewrite (hc5_s4_val E m Hm Hr). apply unsigned_lit_small.
pose proof (Z.mod_pos_bound m 32 ltac:(lia)). lia.
Qed.
(* `bltz s7` with s7 = the kind byte sign-extended is taken exactly when bit 7 of the kind is set *)
Lemma hc5_bltz : forall E kd, ew E 23 = Z_to_bv 64 (hc5_kds kd) -> 0 <= kd < 256 ->
  branch_taken BC_LT (sv_denot E (SOff 23 0)) (sv_denot E (SLit 0)) = Z.testbit kd 7.
Proof.
intros E kd Hk Hr. unfold hc5_kds in Hk.
transitivity (branch_taken BC_LT (sv_denot (cb_envz (kd - 256 * (kd / 128))) (SOff 23 0))
  (sv_denot (cb_envz 0) (SLit 0)));
  [cbn [sv_denot ew cb_envz]; rewrite Hk; reflexivity|].
apply Bool.eqb_prop.
exact (cb_all256 (fun kd => Bool.eqb (branch_taken BC_LT
  (sv_denot (cb_envz (kd - 256 * (kd / 128))) (SOff 23 0)) (sv_denot (cb_envz 0) (SLit 0)))
  (Z.testbit kd 7)) ltac:(vm_compute; reflexivity) kd Hr).
Qed.
(* the values of the engine's symbolic forms *)
Lemma hc5_U_lit : forall E z, 0 <= z < 2 ^ 64 -> U E (SLit z) = z.
Proof. intros E z Hz. rewrite U_SLit. apply zcanon_id. unfold M64. lia. Qed.
Lemma hc5_den_lit : forall E z, 0 <= z < 2 ^ 64 -> sv_denot E (SLit z) = Z_to_bv 64 z.
Proof. intros E z Hz. rewrite denot_lit_U, hc5_U_lit by exact Hz. reflexivity. Qed.
Lemma hc5_den_off : forall E n v x, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + x < 2 ^ 64 ->
  sv_denot E (SOff n x) = Z_to_bv 64 (v + x).
Proof. intros E n v x H Hv Hx. rewrite denot_lit_U, (U_atom_off E n v x H Hv Hx). reflexivity. Qed.
Lemma hc5_den0 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H Hv. rewrite (hc5_den_off E n v 0 H Hv) by lia. rewrite Z.add_0_r. reflexivity. Qed.
Lemma hc5_den_add : forall E a b va vb, ew E a = Z_to_bv 64 va -> ew E b = Z_to_bv 64 vb ->
  0 <= va -> 0 <= vb -> va + vb < 2 ^ 64 -> sv_denot E (SAlu ALU_ADD (SOff a 0) (SOff b 0)) = Z_to_bv 64 (va + vb).
Proof.
intros E a b va vb Ha Hb H1 H2 H3. rewrite denot_lit_U, U_SAlu, (U_atom E a va Ha), (U_atom E b vb Hb) by lia.
cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). reflexivity.
Qed.
Lemma hc5_den_sub : forall E a b va vb, ew E a = Z_to_bv 64 va -> ew E b = Z_to_bv 64 vb -> 0 <= va <= vb -> vb < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff a 0) (SLit (-1))) (SOff b 0)) = Z_to_bv 64 (vb - va).
Proof.
intros E a b va vb Ha Hb H1 H2. rewrite denot_lit_U, U_SAlu, U_SMd, (U_atom E a va Ha), (U_atom E b vb Hb), U_SLit by lia.
cbn [zalu_raw zmd_raw]. unfold zcanon, M64. f_equal. rewrite Zplus_mod_idemp_l.
replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
replace (va * (2 ^ 64 - 1) + vb) with ((vb - va) + va * 2 ^ 64) by ring.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
(* the sign-extended kind byte as an atom's value, without a range on it *)
Lemma hc5_den_kds : forall E (n : nat) kd, ew E n = Z_to_bv 64 (hc5_kds kd) ->
  sv_denot E (SOff n 0) = Z_to_bv 64 (hc5_kds kd).
Proof.
intros E n kd Hk. rewrite <- (Z_to_bv_mod64 (hc5_kds kd)). apply hc5_den0.
- rewrite Z_to_bv_mod64. exact Hk.
- apply Z.mod_pos_bound. lia.
Qed.

(* ======================================== small helpers ======================================== *)
Lemma hc5_val_kept : forall (H H' : word -> bool) m m' a n v, val_mem rsegs (mrestrict H m) a n v ->
  (forall i, 0 <= i < Z.of_nat n -> aview rsegs H' m' (a + i) = aview rsegs H m (a + i)) ->
  val_mem rsegs (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v V K k Hk. apply (hm_aview_mbyte rsegs). rewrite K by lia.
unfold aview. rewrite (V k Hk). cbn [option_map]. reflexivity.
Qed.
Lemma hc5_aview0 : forall (H : word -> bool) m a, mbyte rsegs (mrestrict H m) a = Some (Z_to_bv 8 0) ->
  aview rsegs H m a = Some 0.
Proof. intros H m a E. unfold aview. rewrite E. reflexivity. Qed.
Lemma hc5_input_bytes : forall H mem c r, hm_bytes rsegs H mem c r -> hm_bytes rsegs H mem (hc5_src c r) (hc5_p r).
Proof.
intros H mem c [|m r1] B.
- destruct (hc5_nil c) as (_ & _ & _ & Q). rewrite Q. unfold hm_bytes. cbn [map]. apply garr8_nil.
- destruct (hc5_cons c m r1) as (Q1 & _ & _ & Q4). rewrite Q1, Q4.
  change (m :: r1) with ([m] ++ r1) in B. apply hm_bytes_app in B as [_ B]. cbn [length] in B.
  replace (c + Z.of_nat 1) with (c + 1) in B by lia.
  rewrite <- (firstn_skipn (Z.to_nat (bv_unsigned m mod 32)) r1) in B. apply hm_bytes_app in B as [B _]. exact B.
Qed.
(* e62 as the tail leaves it: e62.type, e62.size, the copied bytes, then zeros *)
Lemma hc5_e_bytes : forall (H : word -> bool) mem F (p : list byte) n sz, n = Z.of_nat (length p) ->
  (length p <= 96)%nat ->
  val_mem rsegs (mrestrict H mem) (F + 0x210) 4 8 -> val_mem rsegs (mrestrict H mem) (F + 0x214) 4 sz ->
  hm_bytes rsegs H mem (F + 0x218) p ->
  (forall i, 0 <= i < 96 - n -> aview rsegs H mem (F + 0x218 + n + i) = Some 0) ->
  hm_bytes rsegs H mem (F + 0x210) (le32 8 ++ le32 sz ++ p ++ zeros (96 - length p)).
Proof.
intros H mem F p n sz -> Hl V0 V4 Bp Z0. unfold le32.
apply hm_bytes_app. split; [apply hm_bytes_of_val; exact V0|].
rewrite length_Z_to_le_bytes. replace (F + 0x210 + Z.of_nat 4) with (F + 0x214) by lia.
apply hm_bytes_app. split; [apply hm_bytes_of_val; exact V4|].
rewrite length_Z_to_le_bytes. replace (F + 0x214 + Z.of_nat 4) with (F + 0x218) by lia.
apply hm_bytes_app. split; [exact Bp|].
unfold zeros, NUL. apply hm_memset_bytes. intros i Hi. rewrite (Z0 i) by lia. reflexivity.
Qed.
Lemma hc5_band_ra : forall x, 0 <= x <= 2 ^ 47 - 1 ->
  0x7fff8000 <= shadow_of_addr SHADOW_OFF x < 0x10007fff8000.
Proof.
intros x Hx. unfold shadow_of_addr, SHADOW_OFF.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)) as D1.
pose proof (Z.div_le_mono x (2 ^ 47 - 1) 8 ltac:(lia) ltac:(lia)) as D2.
change ((2 ^ 47 - 1) / 8) with 17592186044415 in D2. lia.
Qed.
Lemma hc5_band_hull : forall x n a, 0 <= x -> x + n <= 2 ^ 47 -> 0 < n -> cb_hull x n a ->
  0x7fff8000 <= a < 0x10007fff8000.
Proof.
intros x n a Hx Hn Hn0 Ha. unfold cb_hull, shadow_addr, SHADOW_OFF in Ha.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)) as D1.
pose proof (Z.div_le_mono (x + n - 1) (2 ^ 47 - 1) 8 ltac:(lia) ltac:(lia)) as D2.
change ((2 ^ 47 - 1) / 8) with 17592186044415 in D2.
pose proof (Z.div_le_mono 2147450880 (2147450880 + x / 8) 8 ltac:(lia) ltac:(lia)) as D3.
change (2147450880 / 8) with 268431360 in D3.
pose proof (Z.div_le_mono (2147450880 + (x + n - 1) / 8) 17594333495295 8 ltac:(lia) ltac:(lia)) as D4.
change (17594333495295 / 8) with 2199291686911 in D4.
lia.
Qed.
Lemma hc5_hull_kept : forall (H : word -> bool) m m' x n,
  shadow_hull_vis (aview rsegs H m) x n ->
  (forall a, cb_hull x n a -> aview rsegs H m' a = aview rsegs H m a) ->
  shadow_hull_vis (aview rsegs H m') x n.
Proof. intros H m m' x n HV HK s Hs. rewrite HK by exact Hs. exact (HV s Hs). Qed.
Lemma hc5_ra_kept : forall (H : word -> bool) m m' x n,
  range_addressable (aview rsegs H m) SHADOW_OFF x n ->
  (forall a, x <= a < x + n -> aview rsegs H m' (shadow_of_addr SHADOW_OFF a) = aview rsegs H m (shadow_of_addr SHADOW_OFF a)) ->
  range_addressable (aview rsegs H m') SHADOW_OFF x n.
Proof.
intros H m m' x n HR HK y Hy. destruct (HR y Hy) as (s & Hs & Hok). exists s. split; [|exact Hok].
rewrite HK by lia. exact Hs.
Qed.

(* ======================================== tactics ======================================== *)
(* a register of the engine's last state, as its symbolic value *)
Ltac hc5_reg HS r :=
  lazymatch type of HS with st_ok ?segs ?Ev ?ssv (restrict ?H ?ms) =>
    rewrite (st_ok_restrict_reg segs H Ev ssv ms r HS);
    let e := eval vm_compute in (sr_get (ss_regs ssv) r) in
    change (sr_get (ss_regs ssv) r) with e end.
(* region i of the engine's last state *)
Ltac hc5_rnth HS i Hr :=
  lazymatch type of HS with st_ok _ _ ?ss _ =>
    let o := eval vm_compute in (nth_error (ss_mem ss) i) in
    lazymatch o with Some ?r =>
      let Hn := fresh "Hn" in
      assert (Hn : nth_error (ss_mem ss) i = Some r) by (vm_compute; reflexivity);
      pose proof (st_ok_region_at _ _ _ i r HS Hn) as Hr; clear Hn; cbn [restrict ms_mem] in Hr
    end end.
(* an env fact carried over the fresh atoms of a token run *)
Ltac hc5_ew HS H :=
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
  let H' := fresh H "'" in
  lazymatch type of H with
  | ew _ ?n = ?v => assert (H' : ew Ev n = v) by (rewrite ?ew_ewset_other by lia; exact H)
  | bv_unsigned (ew _ ?n) = ?v => assert (H' : bv_unsigned (ew Ev n) = v) by (rewrite ?ew_ewset_other by lia; exact H)
  end end.
Ltac hc5_in := cbn [YP09.r_chunks]; cbv [In]; repeat (first [left; reflexivity | right]).
(* after a run: KE (every byte outside Zn as at the start) moves to the run's last memory *)
Ltac hc5_keep Zn wrl :=
  lazymatch goal with
  | HFr : frame_of ?E ?rs (mrestrict ?H ?m1) (mrestrict ?H ?m2) |- _ =>
    lazymatch goal with
    | KE : forall a, 0 <= a < 2 ^ 64 -> ~ _ -> aview _ _ m1 a = _ |- _ =>
      let KS := fresh "KS" in
      pose proof (cb_kept_run Zn E rs H _ m1 m2 KE HFr ltac:(wrl)) as KS;
      clear KE HFr; rename KS into KE
    end
  end;
  repeat match goal with Hx : frame_of _ _ _ _ |- _ => clear Hx end;
  repeat match goal with old : machine_state |- _ => clear old end.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* ===================== the head's write windows =====================
   the write windows of HPgW6bBase's entry state: [R+0x58, R+0x60), [R+0x110, R+0x118) and e62 *)
Definition hc5_HWr (R F : Z) : Z -> Prop :=
  fun a => (R + 0x58 <= a < R + 0x60) \/ (R + 0x110 <= a < R + 0x118) \/ (F + 0x210 <= a < F + 0x278).
Lemma hc5_hb_wr : forall E rs (byte : bool) R F, YP09.skeleton rs = YP09.skeleton (hb_regions byte) ->
  bv_unsigned (ew E 9) = R -> bv_unsigned (ew E 32) = F -> forall a, in_wrange E rs a -> hc5_HWr R F a.
Proof.
intros E rs byte R F Hsk H9 H32 a Ha. apply (in_wrange_skeleton E rs (hb_regions byte) a Hsk) in Ha.
destruct Ha as (r & Hin & Ha). unfold hc5_HWr.
destruct byte; cbn [hb_regions In] in Hin; repeat destruct Hin as [<-|Hin]; try contradiction;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val hb_rA hb_rB hb_rC hb_rD hb_rE hb_rF hb_rI] in Ha;
  rewrite ?H9, ?H32 in Ha; lia.
Qed.
Section d0.
Variable B : asyms.
Lemma hc5_hb_awr : forall E rs (byte : bool) STK sp0 FP bl0 blc lyc own R F pos,
  YP09.skeleton rs = YP09.skeleton (hb_regions byte) ->
  bv_unsigned (ew E 9) = R -> bv_unsigned (ew E 32) = F ->
  R + 0x220 <= sp0 -> sp0 - STK <= R - 16384 -> In (4, pos) own -> F = frame_addr lyc 4 pos ->
  awr_ok E rs STK sp0 FP bl0 blc lyc own.
Proof.
intros E rs byte STK sp0 FP bl0 blc lyc own R F pos Hsk H9 H32 HR1 HR2 Hown HF a Ha.
apply (in_wrange_skeleton E rs (hb_regions byte) a Hsk) in Ha.
destruct Ha as (r & Hin & Ha). unfold awr_byte.
destruct byte; cbn [hb_regions In] in Hin; repeat destruct Hin as [<-|Hin]; try contradiction;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val hb_rA hb_rB hb_rC hb_rD hb_rE hb_rF hb_rI] in Ha;
  rewrite ?H9, ?H32 in Ha;
  first [ lia | left; lia
        | right; right; right; exists 4, pos; split; [exact Hown|]; left;
          unfold in_zr; cbn [fst snd]; rewrite <- HF; change (fs_frame_bytes 4) with 1024; lia ].
Qed.
End d0.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* ===================== what the head leaves at the call ===================== *)
Definition hc5_HR (F c kd : Z) (r : list byte) :
  world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop :=
fun W2 regs2 mem2 =>
  getr regs2 1 = w64 HC5_RET /\ getr regs2 10 = w64 (F + 0x218) /\ getr regs2 11 = w64 (hc5_src c r) /\
  getr regs2 12 = w64 (hc5_n r) /\ getr regs2 18 = w64 (hc5_src c r) /\ getr regs2 20 = w64 (hc5_n r) /\
  getr regs2 21 = w64 (F + 0x218) /\ getr regs2 23 = w64 (hc5_kds kd) /\ getr regs2 26 = w64 (hc5_left r) /\
  (forall i, 0 <= i < 104 -> mbyte rsegs (mrestrict (w_H W2) mem2) (F + 0x210 + i) = Some (Z_to_bv 8 0)).

Definition hc5_clob : list (bv 5) := [1; 10; 11; 12; 16; 18; 20; 21; 23; 26]%bv.

(* the leaf of a run: the engine's last state at HB_MEMCPY gives the block post *)
Ltac hc5_leaf HAE KE MTLh :=
  apply SRr_ret; unfold hdu_blk_postE; do 5 eexists;
  lazymatch goal with
  | HS : st_ok _ _ _ (restrict (w_H ?Wx) _) |- _ =>
    split; [rewrite (st_ok_restrict_mkst rsegs (w_H Wx) _ _ _ HS eq_refl) at 1; reflexivity|];
    lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => split; [exact HJx|] end;
    split; [eapply (regs_kept_of_st_ok rsegs _ _ _ _ _ (w_H Wx) hc5_clob);
            [exact HS | env_agree_chain HAE | vm_compute; reflexivity]|];
    split; [reflexivity|]; split; [apply Permutation_refl|]; split; [cb_kio|];
    split; [apply mo_le_refl; exact MTLh|]; split; [exact KE|]
  end.

Lemma hc5_head : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word)
  (R F pos c pp kd : Z) (r : list byte),
  hw6b_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
  kd mod 10 = 5 ->
  hw6b_in B W memc regs R F c pp kd r ->
  SRr rsegs W (cfg_at rsegs HB_D5 regs memc mdc)
  (hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc HB_MEMCPY hc5_clob
    (hc5_HWr R F) (hc5_HR F c kd r)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c pp kd r Hctx Hkd5 Hin.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
destruct Hctx as (HJ & HR32 & HRsp & HspR & Hown & HF & Hrom).
destruct Hin as (H2 & H3 & H4 & H9 & H27 & H18 & H17 & H6 & H20 & H16 & H13 & V40 & Ve8 & V118 & V130 & V138 & V148 &
  (Hkd0 & Hkd1) & Hpp & Hppc & HF4 & HFc & HF32 & HRc & Hpres & Ez & Hrae & Hhe & Hc1 & Hwin & Hhin & Hdis).
destruct Hwin as (Hg & Hrain & Hc0 & Hcr & Ham & Hdr).
specialize (H13 ltac:(lia)).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres2 & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _). clear Hstk.
pose proof (@asan_consts rc) as (Hac & _).
unfold T_SEG_STK, ASTACK in HspR, HRc, Hdr.
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (_ & HFapp & _ & _).
rewrite <- HF in HFapp. change (fs_frame_bytes 4) with 1024 in HFapp.
assert (HRb1 : alloc_ceiling <= R) by lia.
assert (HRb2 : R + 0x220 <= 2 ^ 47) by lia.
assert (HR16 : R mod 16 = 0).
{ pose proof (Z.div_mod R 32 ltac:(lia)) as Em. rewrite HR32, Z.add_0_r in Em. rewrite Em.
  replace (32 * (R / 32)) with (2 * (R / 32) * 16) by ring. apply Z.mod_mul. lia. }
assert (Hcb : c + Z.of_nat (length r) <= 2 ^ 47 - 1)
  by (pose proof Ham as X; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in X; lia).
assert (Hppb : pp + 0x4000 < 2 ^ 64) by (unfold Layout.PP_SIZE in Hppc; lia).
assert (Hshb : forall a, F + 0x210 <= a < F + 0x278 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 17592186044416)).
{ intros a Ha. pose proof HFapp as X. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in X.
  unfold SHADOW_OFF. lia. }
assert (Pw : forall o, (0x58 <= o < 0x60 \/ 0x110 <= o < 0x118) -> apresent (w_H W) memc (R + o))
  by (intros o Ho; apply Hpres2; lia).
assert (Pe : forall o, 0 <= o < 104 -> apresent (w_H W) memc (F + 0x210 + o))
  by (intros o Ho; replace (F + 0x210 + o) with (F + (0x210 + o)) by lia; apply Hpres; lia).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ hc5_HWr R F a -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
  by reflexivity.
clear Hpres2 Hfrs HAR Hin4 Hceil Hslo Hshi H47 HFapp Ham Hpres.
unfold cfg_at. change (w64 HB_D5) with (Z_to_bv 64 HB_D5).
destruct r as [|m r1].
- (* ---------------- no byte left: the source is c, n = 0 ---------------- *)
  destruct (hc5_nil c) as (Q1 & Q2 & Q3 & _).
  pose proof (hb_entry HB_D5 false W regs memc R F c pp 0 ltac:(unfold HB_D5; lia) H9 H27 H18
    HRb1 HRb2 HR16 HF4 HFc ltac:(cbn [length] in Hcb; lia) ltac:(lia) ltac:(lia) Hppb
    V40 Ve8 V118 V130 V138 V148 Pw Ez Pe ltac:(intros X; discriminate X)) as HS.
  remember (Ereg regs (hb_extra F pp ((- (F + 0x219)) mod 2 ^ 64) 0)) as E eqn:HE.
  assert (HAE : env_agree 32 (Ereg regs (hb_extra F pp ((- (F + 0x219)) mod 2 ^ 64) 0)) E)
    by (subst E; apply env_agree_refl).
  assert (U9 : bv_unsigned (ew E 9) = R) by (subst E; exact (hb_U_reg regs _ 9 9%bv R eq_refl H9 ltac:(lia))).
  assert (E32 : ew E 32 = Z_to_bv 64 F) by (subst E; exact (ew_Ereg_extra regs _ 0)).
  assert (U32 : bv_unsigned (ew E 32) = F) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (E13 : ew E 13 = Z_to_bv 64 (hc5_kds kd))
    by (subst E; rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
  assert (E18 : ew E 18 = Z_to_bv 64 c) by (subst E; rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
  assert (SHOK : sh_ok rsegs HBx hb_SH E (mrestrict (w_H W) memc))
    by (subst E; exact (hb_shok regs (w_H W) memc F pp _ _ H27 HF4 HFc Hrae Hshb)).
  clear HE.
  pose proof (st_ok_pin_lit rsegs _ _ _ (16%bv : bv 5) 1 HS eq_refl
    ltac:(try rewrite restrict_mkst_fx; cbn [ms_regs restrict mkst]; exact H16)) as HS1.
  clear HS. rename HS1 into HS.
  pose proof (st_ok_pin_lit rsegs _ _ _ (20%bv : bv 5) 0 HS eq_refl
    ltac:(try rewrite restrict_mkst_fx; cbn [ms_regs restrict mkst]; rewrite H20; cbn [length]; reflexivity)) as HS1.
  clear HS. rename HS1 into HS.
  (* 0x81e6c .. 0x82214 .. 0x81ea8 .. the copy's pointer-overflow test 0x81eb0 *)
  aj_run_to_tok hb_tbl_ok HS HJ SHOK HBspan HB_MEMCPY.
  { apply (hc5_hb_awr _ _ false _ _ _ _ _ _ _ R F pos); [vm_compute; reflexivity | exact U9 | exact U32 | lia | lia
      | exact Hown | exact HF]. }
  hc5_keep (hc5_HWr R F) ltac:(apply (hc5_hb_wr _ _ false R F); [vm_compute; reflexivity
    | rewrite ?ew_ewset_other by lia; exact U9 | rewrite ?ew_ewset_other by lia; exact U32]).
  hc5_ew HS E18. hc5_ew HS E13. hc5_ew HS E32. hc5_ew HS U9. hc5_ew HS U32.
  srr_branch_tok hb_tbl_ok HS SHOK HBspan.
  { (* taken: the copy's range is sound *)
    clear Hc.
    aj_run_to_tok hb_tbl_ok HS HJ SHOK HBspan HB_MEMCPY.
    { apply (hc5_hb_awr _ _ false _ _ _ _ _ _ _ R F pos); [vm_compute; reflexivity | exact U9' | exact U32'
        | lia | lia | exact Hown | exact HF]. }
    hc5_keep (hc5_HWr R F) ltac:(apply (hc5_hb_wr _ _ false R F); [vm_compute; reflexivity
      | rewrite ?ew_ewset_other by lia; exact U9 | rewrite ?ew_ewset_other by lia; exact U32]).
    clear E18' E13' E32' U9' U32'.
    hc5_ew HS E18. hc5_ew HS E13. hc5_ew HS E32. hc5_ew HS U9. hc5_ew HS U32.
    hc5_leaf HAE KE MTL.
    unfold hc5_HR. rewrite Q1, Q2, Q3.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))).
    { hc5_reg HS (1%bv : bv 5). unfold w64, HC5_RET. apply hc5_den_lit. lia. }
    { hc5_reg HS (10%bv : bv 5). unfold w64. apply hc5_den_off; [exact E32' | lia | lia]. }
    { hc5_reg HS (11%bv : bv 5). unfold w64. apply hc5_den0; [exact E18' | lia]. }
    { hc5_reg HS (12%bv : bv 5). unfold w64. apply hc5_den_lit. lia. }
    { hc5_reg HS (18%bv : bv 5). unfold w64. apply hc5_den0; [exact E18' | lia]. }
    { hc5_reg HS (20%bv : bv 5). unfold w64. apply hc5_den_lit. lia. }
    { hc5_reg HS (21%bv : bv 5). unfold w64. apply hc5_den_off; [exact E32' | lia | lia]. }
    { hc5_reg HS (23%bv : bv 5). unfold w64. apply (hc5_den_kds _ 13 kd). exact E13'. }
    { hc5_reg HS (26%bv : bv 5). unfold w64. apply hc5_den_lit. lia. }
    hc5_rnth HS 5%nat Hr5. intros i Hi.
    pose proof (hb_chunk_zero _ _ _ 0x210 104 Hr5 ltac:(hc5_in) i Hi) as Z0.
    cbn [YP09.r_base base_val] in Z0. rewrite U32' in Z0. exact Z0. }
  (* not taken: the `unimp` word; c + 1 <= 2 ^ 47 makes it dead *)
  exfalso. rewrite branch_geu_U, (U_not _ 18 c E18' ltac:(lia)), hc5_U_lit in Hc by lia.
  apply negb_false_iff in Hc. apply Z.ltb_lt in Hc. lia.
- (* ---------------- a byte m, the rest r1 ---------------- *)
  pose proof (byte_range m) as Hmb.
  destruct (hc5_cons c m r1) as (Q1 & Q2 & Q3 & _).
  assert (Hm0 : val_mem rsegs (mrestrict (w_H W) memc) c 1 (bv_unsigned m)).
  { destruct (Hg 0%nat ltac:(cbn [length map hd_zbytes]; lia)) as [Hv _]. cbn [nth map hd_zbytes] in Hv.
    replace (c + Z.of_nat 0) with c in Hv by lia. exact Hv. }
  assert (Hpos : c + 1 <= R + 0x40 \/ R + 0x150 <= c).
  { pose proof (Hdr c ltac:(cbn [length]; lia)). lia. }
  assert (Hpos2 : c + 1 <= F + 0x210 \/ F + 0x278 <= c).
  { pose proof (Hdis c ltac:(cbn [length]; lia)). lia. }
  pose proof (hb_entry HB_D5 true W regs memc R F c pp (bv_unsigned m) ltac:(unfold HB_D5; lia) H9 H27 H18
    HRb1 HRb2 HR16 HF4 HFc ltac:(cbn [length] in Hcb; lia) Hmb ltac:(lia) Hppb
    V40 Ve8 V118 V130 V138 V148 Pw Ez Pe (fun _ => conj Hm0 (conj Hpos Hpos2))) as HS.
  clear Hpos Hpos2.
  remember (Ereg regs (hb_extra F pp ((- (F + 0x219)) mod 2 ^ 64) (bv_unsigned m))) as E eqn:HE.
  assert (HAE : env_agree 32 (Ereg regs (hb_extra F pp ((- (F + 0x219)) mod 2 ^ 64) (bv_unsigned m))) E)
    by (subst E; apply env_agree_refl).
  assert (U9 : bv_unsigned (ew E 9) = R) by (subst E; exact (hb_U_reg regs _ 9 9%bv R eq_refl H9 ltac:(lia))).
  assert (E32 : ew E 32 = Z_to_bv 64 F) by (subst E; exact (ew_Ereg_extra regs _ 0)).
  assert (U32 : bv_unsigned (ew E 32) = F) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (E13 : ew E 13 = Z_to_bv 64 (hc5_kds kd))
    by (subst E; rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
  assert (E17 : ew E 17 = Z_to_bv 64 (c - 1)) by (subst E; rewrite (ew_Ereg_nat regs _ 17 17%bv eq_refl); exact H17).
  assert (E18 : ew E 18 = Z_to_bv 64 c) by (subst E; rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
  assert (E20 : ew E 20 = Z_to_bv 64 (Z.of_nat (length (m :: r1))))
    by (subst E; rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
  assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF)
    by (subst E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
  assert (E6 : ew E 6 = Z_to_bv 64 (Z.of_nat (length (m :: r1)) + 1))
    by (subst E; rewrite (ew_Ereg_nat regs _ 6 6%bv eq_refl); exact H6).
  assert (E35 : ew E 35 = Z_to_bv 64 (bv_unsigned m)) by (subst E; exact (ew_Ereg_extra regs _ 3)).
  assert (SHOK : sh_ok rsegs HBx hb_SH E (mrestrict (w_H W) memc))
    by (subst E; exact (hb_shok regs (w_H W) memc F pp _ _ H27 HF4 HFc Hrae Hshb)).
  clear HE.
  cbn [length] in Hcb, Hrain.
  pose proof (st_ok_pin_lit rsegs _ _ _ (16%bv : bv 5) 1 HS eq_refl
    ltac:(try rewrite restrict_mkst_fx; cbn [ms_regs restrict mkst]; exact H16)) as HS1.
  clear HS. rename HS1 into HS.
  (* 0x81e6c beqz s4: s4 = |r| > 0 *)
  srr_branch_tok hb_tbl_ok HS SHOK HBspan.
  { exfalso. rewrite branch_eq_U, (U_atom _ 20 _ E20), hc5_U_lit in Hc by (cbn [length]; lia).
    apply Z.eqb_eq in Hc. cbn [length] in Hc. lia. }
  (* 0x81e70 .. the `bltu s4,s10` at 0x81ea4 *)
  clear Hc.
  aj_run_to_tok hb_tbl_ok HS HJ SHOK HBspan HB_MEMCPY.
  { apply (obl_of_range rsegs (w_H W) memc _ HBx _ _ c (Z.of_nat (Datatypes.S (length r1))) Hrain).
    - apply (U_atom _ 27 SHADOW_OFF E27). unfold SHADOW_OFF. lia.
    - rewrite (U_atom _ 18 c E18) by lia. lia.
    - rewrite (U_atom _ 18 c E18) by lia. lia. }
  { apply (hc5_hb_awr _ _ true _ _ _ _ _ _ _ R F pos); [vm_compute; reflexivity | exact U9 | exact U32 | lia | lia
      | exact Hown | exact HF]. }
  hc5_keep (hc5_HWr R F) ltac:(apply (hc5_hb_wr _ _ true R F); [vm_compute; reflexivity
    | rewrite ?ew_ewset_other by lia; exact U9 | rewrite ?ew_ewset_other by lia; exact U32]).
  hc5_ew HS E35. hc5_ew HS E6. hc5_ew HS E17. hc5_ew HS E13. hc5_ew HS E32. hc5_ew HS U9. hc5_ew HS U32.
  srr_branch_tok hb_tbl_ok HS SHOK HBspan.
  { (* the byte mod 32 < what is left: n = the byte mod 32 *)
    rewrite branch_ltu_U, (hc5_s4_U _ _ E35' Hmb), (U_atom_off _ 6 _ (-2) E6') in Hc by (cbn [length]; lia).
    apply Z.ltb_lt in Hc. cbn [length] in Hc. rename Hc into Hlt.
    aj_run_to_tok hb_tbl_ok HS HJ SHOK HBspan HB_MEMCPY.
    { apply (hc5_hb_awr _ _ true _ _ _ _ _ _ _ R F pos); [vm_compute; reflexivity | exact U9' | exact U32'
        | lia | lia | exact Hown | exact HF]. }
    hc5_keep (hc5_HWr R F) ltac:(apply (hc5_hb_wr _ _ true R F); [vm_compute; reflexivity
      | rewrite ?ew_ewset_other by lia; exact U9 | rewrite ?ew_ewset_other by lia; exact U32]).
    clear E35' E6' E17' E13' E32' U9' U32'.
    hc5_ew HS E35. hc5_ew HS E6. hc5_ew HS E17. hc5_ew HS E13. hc5_ew HS E32. hc5_ew HS U9. hc5_ew HS U32.
    srr_branch_tok hb_tbl_ok HS SHOK HBspan.
    { clear Hc.
      aj_run_to_tok hb_tbl_ok HS HJ SHOK HBspan HB_MEMCPY.
      { apply (hc5_hb_awr _ _ true _ _ _ _ _ _ _ R F pos); [vm_compute; reflexivity | exact U9' | exact U32'
          | lia | lia | exact Hown | exact HF]. }
      hc5_keep (hc5_HWr R F) ltac:(apply (hc5_hb_wr _ _ true R F); [vm_compute; reflexivity
        | rewrite ?ew_ewset_other by lia; exact U9 | rewrite ?ew_ewset_other by lia; exact U32]).
      clear E35' E6' E17' E13' E32' U9' U32'.
      hc5_ew HS E35. hc5_ew HS E6. hc5_ew HS E17. hc5_ew HS E13. hc5_ew HS E32. hc5_ew HS U9. hc5_ew HS U32.
      hc5_leaf HAE KE MTL.
      unfold hc5_HR. rewrite Q1, Q2, Q3, Z.min_l by (set (mm := bv_unsigned m mod 32) in *; lia).
      refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))).
      { hc5_reg HS (1%bv : bv 5). unfold w64, HC5_RET. apply hc5_den_lit. lia. }
      { hc5_reg HS (10%bv : bv 5). unfold w64. apply hc5_den_off; [exact E32' | lia | lia]. }
      { hc5_reg HS (11%bv : bv 5). unfold w64. rewrite (hc5_den_off _ 17 (c - 1) 2 E17') by lia. f_equal. lia. }
      { hc5_reg HS (12%bv : bv 5). unfold w64. exact (hc5_s4z_val _ _ E35' Hmb). }
      { hc5_reg HS (18%bv : bv 5). unfold w64. rewrite (hc5_den_off _ 17 (c - 1) 2 E17') by lia. f_equal. lia. }
      { hc5_reg HS (20%bv : bv 5). unfold w64. exact (hc5_s4_val _ _ E35' Hmb). }
      { hc5_reg HS (21%bv : bv 5). unfold w64. apply hc5_den_off; [exact E32' | lia | lia]. }
      { hc5_reg HS (23%bv : bv 5). unfold w64. apply (hc5_den_kds _ 13 kd). exact E13'. }
      { hc5_reg HS (26%bv : bv 5). unfold w64.
        rewrite (hc5_den_off _ 6 _ (-2) E6') by (cbn [length]; lia). f_equal. cbn [length]. lia. }
      hc5_rnth HS 5%nat Hr5. intros i Hi.
      pose proof (hb_chunk_zero _ _ _ 0x210 104 Hr5 ltac:(hc5_in) i Hi) as Z0.
      cbn [YP09.r_base base_val] in Z0. rewrite U32' in Z0. exact Z0. }
    exfalso. rewrite branch_geu_U, (U_not_off _ 17 (c - 1) 2 E17' ltac:(lia) ltac:(lia)),
      (hc5_s4_U _ _ E35' Hmb) in Hc.
    apply negb_false_iff in Hc. apply Z.ltb_lt in Hc.
    pose proof (Z.mod_pos_bound (bv_unsigned m) 32 ltac:(lia)). lia. }
  (* the byte mod 32 >= what is left: n = what is left *)
  rewrite branch_ltu_U, (hc5_s4_U _ _ E35' Hmb), (U_atom_off _ 6 _ (-2) E6') in Hc by (cbn [length]; lia).
  apply Z.ltb_ge in Hc. cbn [length] in Hc. rename Hc into Hlt.
  aj_run_to_tok hb_tbl_ok HS HJ SHOK HBspan HB_MEMCPY.
  { apply (hc5_hb_awr _ _ true _ _ _ _ _ _ _ R F pos); [vm_compute; reflexivity | exact U9' | exact U32'
      | lia | lia | exact Hown | exact HF]. }
  hc5_keep (hc5_HWr R F) ltac:(apply (hc5_hb_wr _ _ true R F); [vm_compute; reflexivity
    | rewrite ?ew_ewset_other by lia; exact U9 | rewrite ?ew_ewset_other by lia; exact U32]).
  clear E35' E6' E17' E13' E32' U9' U32'.
  hc5_ew HS E35. hc5_ew HS E6. hc5_ew HS E17. hc5_ew HS E13. hc5_ew HS E32. hc5_ew HS U9. hc5_ew HS U32.
  srr_branch_tok hb_tbl_ok HS SHOK HBspan.
  { clear Hc.
    aj_run_to_tok hb_tbl_ok HS HJ SHOK HBspan HB_MEMCPY.
    { apply (hc5_hb_awr _ _ true _ _ _ _ _ _ _ R F pos); [vm_compute; reflexivity | exact U9' | exact U32'
        | lia | lia | exact Hown | exact HF]. }
    hc5_keep (hc5_HWr R F) ltac:(apply (hc5_hb_wr _ _ true R F); [vm_compute; reflexivity
      | rewrite ?ew_ewset_other by lia; exact U9 | rewrite ?ew_ewset_other by lia; exact U32]).
    clear E35' E6' E17' E13' E32' U9' U32'.
    hc5_ew HS E35. hc5_ew HS E6. hc5_ew HS E17. hc5_ew HS E13. hc5_ew HS E32. hc5_ew HS U9. hc5_ew HS U32.
    hc5_leaf HAE KE MTL.
    unfold hc5_HR. rewrite Q1, Q2, Q3, Z.min_r by (set (mm := bv_unsigned m mod 32) in *; lia).
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))).
    { hc5_reg HS (1%bv : bv 5). unfold w64, HC5_RET. apply hc5_den_lit. lia. }
    { hc5_reg HS (10%bv : bv 5). unfold w64. apply hc5_den_off; [exact E32' | lia | lia]. }
    { hc5_reg HS (11%bv : bv 5). unfold w64. rewrite (hc5_den_off _ 17 (c - 1) 2 E17') by lia. f_equal. lia. }
    { hc5_reg HS (12%bv : bv 5). unfold w64.
      rewrite (hc5_den_off _ 6 _ (-2) E6') by (cbn [length]; lia). f_equal. cbn [length]. lia. }
    { hc5_reg HS (18%bv : bv 5). unfold w64. rewrite (hc5_den_off _ 17 (c - 1) 2 E17') by lia. f_equal. lia. }
    { hc5_reg HS (20%bv : bv 5). unfold w64.
      rewrite (hc5_den_off _ 6 _ (-2) E6') by (cbn [length]; lia). f_equal. cbn [length]. lia. }
    { hc5_reg HS (21%bv : bv 5). unfold w64. apply hc5_den_off; [exact E32' | lia | lia]. }
    { hc5_reg HS (23%bv : bv 5). unfold w64. apply (hc5_den_kds _ 13 kd). exact E13'. }
    { hc5_reg HS (26%bv : bv 5). unfold w64.
      rewrite (hc5_den_off _ 6 _ (-2) E6') by (cbn [length]; lia). f_equal. cbn [length]. lia. }
    hc5_rnth HS 5%nat Hr5. intros i Hi.
    pose proof (hb_chunk_zero _ _ _ 0x210 104 Hr5 ltac:(hc5_in) i Hi) as Z0.
    cbn [YP09.r_base base_val] in Z0. rewrite U32' in Z0. exact Z0. }
  exfalso. rewrite branch_geu_U, (U_not_off _ 17 (c - 1) 2 E17' ltac:(lia) ltac:(lia)),
    (U_atom_off _ 6 _ (-2) E6' ltac:(cbn [length]; lia) ltac:(cbn [length]; lia)) in Hc.
  apply negb_false_iff in Hc. apply Z.ltb_lt in Hc. cbn [length] in Hc. lia.
Qed.

End d.
End b.

Print Assumptions hc5_head.
