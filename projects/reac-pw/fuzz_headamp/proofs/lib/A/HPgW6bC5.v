(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6bC5.v at f3898085bda; for reac-pw/fuzz_headamp image A: module paths and the rm_ prefix renamed, every pc moved by the code's uniform shift +0xd20 over [0x80a80, 0x81af0), __asan_memcpy 0x51d0c, the real-frame cells by the plan's slot map (in.n R+0xf8 -> R+0x118, vb R+0xb0 -> R+0xd0, pp R+0x80 -> R+0xf0, &e R+0xf0 -> R+0x110, &e.body R+0xc0 -> R+0xe0), the tail's R-based region re-cut for that layout ([R+0xd0, R+0x120) for [R+0x80, R+0x100), chunks in address order), the frame for locals of class 4 (1024 bytes), RPgCfgChanges.cfg_wx / cfg_segs_low / same_io_wvb / kept_run -> HPgSteps' img_wx / img_segs_low / same_io_wvb and HPgW7bBase.kept_run. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, same loaded bytes except .note.gnu.build-id): the block lemma w6b_c5 of
   lib/A/HPgW6bBase.v, case 5 of ent_build's `switch (kind % 10)` (pod.h:333-339, ent_text pod.h:209-219) inside
   LLVMFuzzerTestOneInput (0x80bc0), from the case entry 0x81d40 to the join J 0x8237c. Proves no function (kind:
   segment lemma).

   THE CODE (registers as at a case entry, HPgW6bBase.w6b_in: s1 = R, s7 = SHADOW_OFF, s8 = c, a4 = c - 1, s9 = |r|,
   [R+0x118] = |r| + 1, s4 = the kind byte sign-extended):
     0x81d40  beqz s9 -> 0x82068                     no byte left
     0x81d44 .. 0x81d50  the instrumented check of s8 (slow block 0x82734)
     0x81d54  lbu a0,0(s8) (= m); s11 := [R+0x118] - 2 (= |r1|); s8 := a4 + 2 (= c + 1); s9 := m & 0x1f
     0x81d68  bltu s9,s11 -> 0x81d70, else 0x81d6c s9 := s11            n' = min(m mod 32, |r1|)
     0x81d70  sd s11,0x118(s1); s11 := [R+0xe0] (= F + 0xf8, e.body); a0 := s11; a1 := s8; a2 := s9
     0x81d84  jal __asan_memcpy (0x51d0c)            e.body[0 .. n') := the n' input bytes after m
     0x81d88  a0 := s9; bltz s4 -> 0x81d9c           kind & 0x80: no NUL
     0x81d90  a0 := s9 + 1; sb zero,0(s11 + s9)      the NUL at e.body + n' (no instrumented check)
     0x81d9c  s8 += s9; [R+0x118] -= s9; s9 := s8; e.type := 8; e.size := a0; s11 := [R+0xf0] (= pp); j 0x8216c
     0x8216c  s4 := [R+0xd0]; j J
     0x82068  s11 := 0; bgeu s9,zero -> 0x81d6c (always): n' = 0, the source at c.
   THE PROOF is three blocks in the journal form of lib/A/HPgW7bBase.v (w7_post: the world, the layout and the state
   of the runtime kept), chained by SRr_bind:
     c5_head  0x81d40 .. 0x51d0c: one token-engine run per arm from HPgEntBKit's entry state (the shadow entry over e
              is eb_SH; the instrumented check of the input byte leaves one obligation `range_addressable`, paid from
              w6_in); the branches on s9 = 0 and on `bltu` split by srr_branch_tok.
     the call HPgW7bKit.w7_memcpy_at (__asan_memcpy, the section hypothesis MCPY): both ranges addressable, the
              destination in the frame for locals (4, pos), the source inside the input.
     c5_tail  0x81d88 .. J: one plain-engine run per arm from a fresh entry state whose regions are [R+0xd0, R+0x120),
              e.type and e.size, and the one byte e.body + n'; the address s11 + s9 of the NUL store is the extra atom
              36 by an alias fact; `bltz s4` split by srr_branch_with (the sign of the kind byte, c5_bltz).
   The pod (Model.ent_build case 5) is ent_text p (kind & 0x80 = 0) with p = firstn (m mod 32) r1 (c5_model), whose
   104 bytes are le32 8, le32 |body|, p and zeros (c5_ent_mem). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgSteps HPgW6aBase HPgW6bBase.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgMem HPgEntBKit HPgW7bBase HPgW7bKit.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgW6aC2h.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ======================================== the pcs ======================================== *)
Definition C5_RET : Z := 0x81d88.     (* after the __asan_memcpy call at 0x81d84 *)

(* ======================================== the model's values ======================================== *)
(* (m, r1) = fuzz_u8 r; p = firstn (m mod 32) r1 (fuzz_take), the bytes the memcpy copies *)
Definition c5_k (r : list byte) : nat := Z.to_nat (fst (fuzz_u8 r) mod 32).
Definition c5_r1 (r : list byte) : list byte := snd (fuzz_u8 r).
Definition c5_p (r : list byte) : list byte := firstn (c5_k r) (c5_r1 r).
Definition c5_n (r : list byte) : Z := Z.of_nat (length (c5_p r)).
Definition c5_left (r : list byte) : Z := Z.of_nat (length (c5_r1 r)).
(* the memcpy source: c + 1 after a byte, c when none is left *)
Definition c5_src (c : Z) (r : list byte) : Z := c + Z.of_nat (length r) - Z.of_nat (length (c5_r1 r)).

Lemma c5_nil : forall c, c5_src c [] = c /\ c5_n [] = 0 /\ c5_left [] = 0 /\ c5_p [] = [].
Proof.
intros c. unfold c5_src, c5_n, c5_left, c5_p, c5_r1, c5_k. cbn [fuzz_u8 fst snd]. rewrite firstn_nil.
cbn [length]. split; [lia|]. split; [reflexivity|]. split; reflexivity.
Qed.
Lemma c5_cons : forall c (m : byte) r1, c5_src c (m :: r1) = c + 1 /\ c5_left (m :: r1) = Z.of_nat (length r1) /\
  c5_n (m :: r1) = Z.min (bv_unsigned m mod 32) (Z.of_nat (length r1)) /\
  c5_p (m :: r1) = firstn (Z.to_nat (bv_unsigned m mod 32)) r1.
Proof.
intros c m r1. pose proof (byte_range m) as Hm.
unfold c5_src, c5_n, c5_left, c5_p, c5_r1, c5_k. cbn [fuzz_u8 fst snd length].
split; [lia|]. split; [reflexivity|]. split; [|reflexivity].
rewrite length_firstn, Nat2Z.inj_min, Z2Nat.id by (apply Z.mod_pos_bound; lia). reflexivity.
Qed.
Lemma c5_bounds : forall c r, c <= c5_src c r /\ c5_src c r + c5_n r <= c + Z.of_nat (length r) /\
  0 <= c5_n r <= 31 /\ c5_n r <= c5_left r /\ c5_src c r + c5_left r = c + Z.of_nat (length r) /\
  (length (c5_p r) <= 31)%nat /\ c5_n r = Z.of_nat (length (c5_p r)).
Proof.
intros c [|m r1].
- destruct (c5_nil c) as (Q1 & Q2 & Q3 & Q4). rewrite Q1, Q2, Q3, Q4. cbn [length]. lia.
- destruct (c5_cons c m r1) as (Q1 & Q2 & Q3 & Q4). pose proof (byte_range m) as Hm.
  pose proof (Z.mod_pos_bound (bv_unsigned m) 32 ltac:(lia)) as Hm32.
  assert (Hl : (length (c5_p (m :: r1)) <= 31)%nat) by (rewrite Q4, length_firstn; lia).
  split; [lia|]. split; [rewrite Q1, Q3; cbn [length]; lia|]. split; [rewrite Q3; lia|].
  split; [rewrite Q3, Q2; lia|]. split; [rewrite Q1, Q2; cbn [length]; lia|]. split; [exact Hl | reflexivity].
Qed.
Lemma c5_skip_len : forall r, Z.of_nat (length (skipn (c5_k r) (c5_r1 r))) = c5_left r - c5_n r.
Proof.
intros r. unfold c5_left, c5_n, c5_p. rewrite length_skipn, length_firstn. lia.
Qed.
(* Model.ent_build case 5 *)
Lemma c5_model : forall (b : byte) (r : list byte), bv_unsigned b mod 10 = 5 ->
  ent_build (b :: r) = (ent_text (c5_p r) (negb (Z.testbit (bv_unsigned b) 7)), skipn (c5_k r) (c5_r1 r)).
Proof.
intros b r H. unfold ent_build, c5_p, c5_k, c5_r1, fuzz_take. cbn [fuzz_u8 fst snd]. rewrite H.
destruct (fuzz_u8 r) as [n r1]. reflexivity.
Qed.
(* the 104 bytes of the pod: e.type, e.size, the body and zeros (with the NUL, the body's last byte is a zero too) *)
Lemma c5_ent_mem : forall p (nul : bool), (length p <= 95)%nat ->
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

(* ======================================== the arithmetic ======================================== *)
(* s9 = m & 0x1f, as the engine computes it from the loaded byte (atom 35) *)
Lemma c5_s9_val : forall E m, ew E 35 = Z_to_bv 64 m -> 0 <= m < 256 ->
  sv_denot E (SAlu ALU_AND (SExt false 8 (SOff 35 0)) (SLit 31)) = Z_to_bv 64 (m mod 32).
Proof.
intros E m Hm Hr.
transitivity (sv_denot (HPgW6aC2h.c2_envz m) (SAlu ALU_AND (SExt false 8 (SOff 35 0)) (SLit 31)));
  [cbn [sv_denot ew HPgW6aC2h.c2_envz]; rewrite Hm; reflexivity|].
apply bv_eq. apply Z.eqb_eq.
exact (HPgW6aC2h.c2_all256 (fun m => bv_unsigned (sv_denot (HPgW6aC2h.c2_envz m)
  (SAlu ALU_AND (SExt false 8 (SOff 35 0)) (SLit 31))) =? bv_unsigned (Z_to_bv 64 (m mod 32)))
  ltac:(vm_compute; reflexivity) m Hr).
Qed.
Lemma c5_s9z_val : forall E m, ew E 35 = Z_to_bv 64 m -> 0 <= m < 256 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SExt false 8 (SOff 35 0)) (SLit 31)) (SLit 0)) = Z_to_bv 64 (m mod 32).
Proof.
intros E m Hm Hr.
transitivity (sv_denot (HPgW6aC2h.c2_envz m) (SAlu ALU_ADD (SAlu ALU_AND (SExt false 8 (SOff 35 0)) (SLit 31)) (SLit 0)));
  [cbn [sv_denot ew HPgW6aC2h.c2_envz]; rewrite Hm; reflexivity|].
apply bv_eq. apply Z.eqb_eq.
exact (HPgW6aC2h.c2_all256 (fun m => bv_unsigned (sv_denot (HPgW6aC2h.c2_envz m)
  (SAlu ALU_ADD (SAlu ALU_AND (SExt false 8 (SOff 35 0)) (SLit 31)) (SLit 0))) =? bv_unsigned (Z_to_bv 64 (m mod 32)))
  ltac:(vm_compute; reflexivity) m Hr).
Qed.
Lemma c5_s9_U : forall E m, ew E 35 = Z_to_bv 64 m -> 0 <= m < 256 ->
  U E (SAlu ALU_AND (SExt false 8 (SOff 35 0)) (SLit 31)) = m mod 32.
Proof.
intros E m Hm Hr. unfold U. rewrite (c5_s9_val E m Hm Hr). apply unsigned_lit_small.
pose proof (Z.mod_pos_bound m 32 ltac:(lia)). lia.
Qed.
(* `bltz s4` with s4 = the kind byte sign-extended is taken exactly when bit 7 of the kind is set *)
Lemma c5_bltz : forall E kd, ew E 20 = Z_to_bv 64 (kd - 256 * (kd / 128)) -> 0 <= kd < 256 ->
  branch_taken BC_LT (sv_denot E (SOff 20 0)) (sv_denot E (SLit 0)) = Z.testbit kd 7.
Proof.
intros E kd Hk Hr.
transitivity (branch_taken BC_LT (sv_denot (HPgW6aC2h.c2_envz (kd - 256 * (kd / 128))) (SOff 20 0))
  (sv_denot (HPgW6aC2h.c2_envz 0) (SLit 0)));
  [cbn [sv_denot ew HPgW6aC2h.c2_envz]; rewrite Hk; reflexivity|].
apply Bool.eqb_prop.
exact (HPgW6aC2h.c2_all256 (fun kd => Bool.eqb (branch_taken BC_LT
  (sv_denot (HPgW6aC2h.c2_envz (kd - 256 * (kd / 128))) (SOff 20 0)) (sv_denot (HPgW6aC2h.c2_envz 0) (SLit 0)))
  (Z.testbit kd 7)) ltac:(vm_compute; reflexivity) kd Hr).
Qed.
(* the values of the engine's symbolic forms *)
Lemma c5_U_lit : forall E z, 0 <= z < 2 ^ 64 -> U E (SLit z) = z.
Proof. intros E z Hz. rewrite U_SLit. apply zcanon_id. unfold M64. lia. Qed.
Lemma c5_den_lit : forall E z, 0 <= z < 2 ^ 64 -> sv_denot E (SLit z) = Z_to_bv 64 z.
Proof. intros E z Hz. rewrite denot_lit_U, c5_U_lit by exact Hz. reflexivity. Qed.
Lemma c5_den_off : forall E n v x, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + x < 2 ^ 64 ->
  sv_denot E (SOff n x) = Z_to_bv 64 (v + x).
Proof. intros E n v x H Hv Hx. rewrite denot_lit_U, (U_atom_off E n v x H Hv Hx). reflexivity. Qed.
Lemma c5_den0 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H Hv. rewrite (c5_den_off E n v 0 H Hv) by lia. rewrite Z.add_0_r. reflexivity. Qed.
Lemma c5_den_add : forall E a b va vb, ew E a = Z_to_bv 64 va -> ew E b = Z_to_bv 64 vb ->
  0 <= va -> 0 <= vb -> va + vb < 2 ^ 64 -> sv_denot E (SAlu ALU_ADD (SOff a 0) (SOff b 0)) = Z_to_bv 64 (va + vb).
Proof.
intros E a b va vb Ha Hb H1 H2 H3. rewrite denot_lit_U, U_SAlu, (U_atom E a va Ha), (U_atom E b vb Hb) by lia.
cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). reflexivity.
Qed.
Lemma c5_den_sub : forall E a b va vb, ew E a = Z_to_bv 64 va -> ew E b = Z_to_bv 64 vb -> 0 <= va <= vb -> vb < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff a 0) (SLit (-1))) (SOff b 0)) = Z_to_bv 64 (vb - va).
Proof.
intros E a b va vb Ha Hb H1 H2. rewrite denot_lit_U, U_SAlu, U_SMd, (U_atom E a va Ha), (U_atom E b vb Hb), U_SLit by lia.
cbn [zalu_raw zmd_raw]. unfold zcanon, M64. f_equal. rewrite Zplus_mod_idemp_l.
replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
replace (va * (2 ^ 64 - 1) + vb) with ((vb - va) + va * 2 ^ 64) by ring.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

(* ======================================== small helpers ======================================== *)
Lemma c5_val_kept : forall (H H' : word -> bool) m m' a n v, val_mem rsegs (mrestrict H m) a n v ->
  (forall i, 0 <= i < Z.of_nat n -> aview rsegs H' m' (a + i) = aview rsegs H m (a + i)) ->
  val_mem rsegs (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v V K k Hk. apply (hm_aview_mbyte rsegs). rewrite K by lia.
unfold aview. rewrite (V k Hk). cbn [option_map]. reflexivity.
Qed.
Lemma c5_aview0 : forall (H : word -> bool) m a, mbyte rsegs (mrestrict H m) a = Some (Z_to_bv 8 0) ->
  aview rsegs H m a = Some 0.
Proof. intros H m a E. unfold aview. rewrite E. reflexivity. Qed.
(* every non-zero register outside w6b_clob is callee-saved (checked over the 31 registers) *)
Definition c5_cs_b (z : Z) : bool :=
  (z =? 2) || (z =? 3) || (z =? 4) || (z =? 8) || (z =? 9) || ((18 <=? z) && (z <=? 27)).
Lemma c5_cs_check :
  forallb (fun r : bv 5 => existsb (fun c => bv_eqb c r) w6b_clob || c5_cs_b (bv_unsigned r)) nz_regs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma c5_cs : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r w6b_clob -> acallee_saved (bv_unsigned r).
Proof.
intros r Hr0 Hn.
pose proof (proj1 (forallb_forall _ _) c5_cs_check r (in_nz_regs r Hr0)) as Hq. cbv beta in Hq.
apply orb_prop in Hq as [Hq|Hq].
- exfalso. apply Hn. apply existsb_exists in Hq as (c0 & Hc & Hb). apply bv_eqb_eq in Hb. subst c0. exact Hc.
- unfold c5_cs_b in Hq. unfold acallee_saved.
  repeat rewrite orb_true_iff in Hq. rewrite andb_true_iff, ?Z.eqb_eq, ?Z.leb_le in Hq. lia.
Qed.
Lemma c5_reg_cs : forall (regs1 regs2 : bvmap 5 word) (r : bv 5), aregs_preserved regs1 regs2 ->
  acallee_saved (bv_unsigned r) -> getr regs2 r = getr regs1 r.
Proof. intros regs1 regs2 r HP Hr. pose proof (HP _ Hr) as X. rewrite !Z_to_bv_bv_unsigned in X. exact X. Qed.
Lemma c5_input_bytes : forall H mem c r, hm_bytes rsegs H mem c r -> hm_bytes rsegs H mem (c5_src c r) (c5_p r).
Proof.
intros H mem c [|m r1] B.
- destruct (c5_nil c) as (_ & _ & _ & Q). rewrite Q. unfold hm_bytes. cbn [map]. apply garr8_nil.
- destruct (c5_cons c m r1) as (Q1 & _ & _ & Q4). rewrite Q1, Q4.
  change (m :: r1) with ([m] ++ r1) in B. apply hm_bytes_app in B as [_ B]. cbn [length] in B.
  replace (c + Z.of_nat 1) with (c + 1) in B by lia.
  rewrite <- (firstn_skipn (Z.to_nat (bv_unsigned m mod 32)) r1) in B. apply hm_bytes_app in B as [B _]. exact B.
Qed.
(* e as the tail leaves it: e.type, e.size, the copied bytes, then zeros *)
Lemma c5_e_bytes : forall (H : word -> bool) mem F (p : list byte) n sz, n = Z.of_nat (length p) ->
  (length p <= 96)%nat ->
  val_mem rsegs (mrestrict H mem) (F + 0xf0) 4 8 -> val_mem rsegs (mrestrict H mem) (F + 0xf4) 4 sz ->
  hm_bytes rsegs H mem (F + 0xf8) p ->
  (forall i, 0 <= i < 96 - n -> aview rsegs H mem (F + 0xf8 + n + i) = Some 0) ->
  hm_bytes rsegs H mem (F + 0xf0) (le32 8 ++ le32 sz ++ p ++ zeros (96 - length p)).
Proof.
intros H mem F p n sz -> Hl V0 V4 Bp Z0. unfold le32.
apply hm_bytes_app. split; [apply hm_bytes_of_val; exact V0|].
rewrite length_Z_to_le_bytes. replace (F + 0xf0 + Z.of_nat 4) with (F + 0xf4) by lia.
apply hm_bytes_app. split; [apply hm_bytes_of_val; exact V4|].
rewrite length_Z_to_le_bytes. replace (F + 0xf4 + Z.of_nat 4) with (F + 0xf8) by lia.
apply hm_bytes_app. split; [exact Bp|].
unfold zeros, NUL. apply hm_memset_bytes. intros i Hi. rewrite (Z0 i) by lia. reflexivity.
Qed.
(* the shadow bytes of [x, x + n) (and their 8-byte hull) lie in the shadow band, below every frame and real frame *)
Lemma c5_band_ra : forall x, 0 <= x <= 2 ^ 47 - 1 ->
  0x7fff8000 <= shadow_of_addr SHADOW_OFF x < 0x10007fff8000.
Proof.
intros x Hx. unfold shadow_of_addr, SHADOW_OFF.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)) as D1.
pose proof (Z.div_le_mono x (2 ^ 47 - 1) 8 ltac:(lia) ltac:(lia)) as D2.
change ((2 ^ 47 - 1) / 8) with 17592186044415 in D2. lia.
Qed.
Lemma c5_band_hull : forall x n a, 0 <= x -> x + n <= 2 ^ 47 -> 0 < n -> w7_hull x n a -> 0x7fff8000 <= a < 0x10007fff8000.
Proof.
intros x n a Hx Hn Hn0 Ha. unfold w7_hull, shadow_addr, SHADOW_OFF in Ha.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)) as D1.
pose proof (Z.div_le_mono (x + n - 1) (2 ^ 47 - 1) 8 ltac:(lia) ltac:(lia)) as D2.
change ((2 ^ 47 - 1) / 8) with 17592186044415 in D2.
pose proof (Z.div_le_mono 2147450880 (2147450880 + x / 8) 8 ltac:(lia) ltac:(lia)) as D3.
change (2147450880 / 8) with 268431360 in D3.
pose proof (Z.div_le_mono (2147450880 + (x + n - 1) / 8) 17594333495295 8 ltac:(lia) ltac:(lia)) as D4.
change (17594333495295 / 8) with 2199291686911 in D4.
lia.
Qed.

(* ======================================== tactics ======================================== *)
(* a register of the engine's last state, as its symbolic value *)
Ltac c5_reg HS r :=
  lazymatch type of HS with st_ok ?segs ?Ev ?ssv (restrict ?H ?ms) =>
    rewrite (st_ok_restrict_reg segs H Ev ssv ms r HS);
    let e := eval vm_compute in (sr_get (ss_regs ssv) r) in
    change (sr_get (ss_regs ssv) r) with e end.
(* region i of the engine's last state *)
Ltac c5_rnth HS i Hr :=
  lazymatch type of HS with st_ok _ _ ?ss _ =>
    let o := eval vm_compute in (nth_error (ss_mem ss) i) in
    lazymatch o with Some ?r =>
      let Hn := fresh "Hn" in
      assert (Hn : nth_error (ss_mem ss) i = Some r) by (vm_compute; reflexivity);
      pose proof (w7_region_nth _ _ _ i r HS Hn) as Hr; clear Hn; cbn [restrict ms_mem] in Hr
    end end.
(* an env fact carried over the fresh atoms of a token run *)
Ltac c5_ew HS H :=
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
  let H' := fresh H "'" in
  lazymatch type of H with
  | ew _ ?n = ?v => assert (H' : ew Ev n = v) by (rewrite ?ew_ewset_other by lia; exact H)
  | bv_unsigned (ew _ ?n) = ?v => assert (H' : bv_unsigned (ew Ev n) = v) by (rewrite ?ew_ewset_other by lia; exact H)
  end end.
Ltac c5_kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; c5_kio].
Ltac c5_in := cbn [YP09.r_chunks]; cbv [In]; repeat (first [left; reflexivity | right]).
(* after a run: KE (every byte outside Zn as at the start) and GE (bytes only appear) move to the run's last memory *)
Ltac c5_keep Zn wrl :=
  lazymatch goal with
  | HFr : frame_of ?E ?rs (mrestrict ?H ?m1) (mrestrict ?H ?m2) |- _ =>
    lazymatch goal with
    | KE : forall a, 0 <= a < 2 ^ 64 -> ~ _ -> aview _ _ m1 a = _,
      HG : mem_grows (mrestrict _ m1) (mrestrict _ m2),
      GE : mem_grows _ (mrestrict _ m1) |- _ =>
      let KS := fresh "KS" in let GS := fresh "GS" in
      pose proof (kept_run Zn E rs H _ m1 m2 KE HFr ltac:(wrl)) as KS;
      pose proof (mem_grows_trans _ _ _ GE HG) as GS;
      clear KE HFr HG GE; rename KS into KE; rename GS into GE
    end
  end;
  repeat match goal with Hx : frame_of _ _ _ _ |- _ => clear Hx end;
  repeat match goal with old : machine_state |- _ => clear old end.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* ======================================== the head's regions ======================================== *)
(* the write windows of HPgEntBKit's entry state: [R+0x68, R+0x70), [R+0x118, R+0x120) and e *)
Definition c5_HWr (R F : Z) : Z -> Prop :=
  fun a => (R + 0x68 <= a < R + 0x70) \/ (R + 0x118 <= a < R + 0x120) \/ (F + 0xf0 <= a < F + 0x158).
Lemma c5_eb_wr : forall E rs (byte : bool) R F, YP09.skeleton rs = YP09.skeleton (eb_regions byte) ->
  bv_unsigned (ew E 9) = R -> bv_unsigned (ew E 32) = F -> forall a, in_wrange E rs a -> c5_HWr R F a.
Proof.
intros E rs byte R F Hsk H9 H32 a Ha. apply (in_wrange_skeleton E rs (eb_regions byte) a Hsk) in Ha.
destruct Ha as (r & Hin & Ha). unfold c5_HWr.
destruct byte; cbn [eb_regions In] in Hin; repeat destruct Hin as [<-|Hin]; try contradiction;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val eb_rA eb_rB eb_rC eb_rE eb_rI] in Ha; rewrite ?H9, ?H32 in Ha; lia.
Qed.
Lemma c5_eb_awr : forall E rs (byte : bool) STK sp0 FP bl0 blc lyc own R F pos,
  YP09.skeleton rs = YP09.skeleton (eb_regions byte) ->
  bv_unsigned (ew E 9) = R -> bv_unsigned (ew E 32) = F ->
  R + 0x120 <= sp0 -> sp0 - STK <= R -> In (4, pos) own -> F = frame_addr lyc 4 pos ->
  awr_ok E rs STK sp0 FP bl0 blc lyc own.
Proof.
intros E rs byte STK sp0 FP bl0 blc lyc own R F pos Hsk H9 H32 HR1 HR2 Hown HF a Ha.
apply (in_wrange_skeleton E rs (eb_regions byte) a Hsk) in Ha.
destruct Ha as (r & Hin & Ha). unfold awr_byte.
destruct byte; cbn [eb_regions In] in Hin; repeat destruct Hin as [<-|Hin]; try contradiction;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val eb_rA eb_rB eb_rC eb_rE eb_rI] in Ha; rewrite ?H9, ?H32 in Ha;
  first [ lia | left; lia
        | right; right; right; exists 4, pos; split; [exact Hown|]; left;
          unfold in_zr; cbn [fst snd]; rewrite <- HF; change (fs_frame_bytes 4) with 1024; lia ].
Qed.

(* ======================================== the tail's entry state ======================================== *)
(* [R+0xf0] = pp (atom 35), [R+0xd0] = vb (atom 33), [R+0x110] = F + 0xf0 (atom 32 = F), [R+0x118] = left (atom 34),
   written; e.type and e.size, written; the byte e.body + n' (atom 36), zero, written. s11 + s9 is atom 36. *)
Definition c5_tR : YP09.region := YP09.mkRegion (Some 9%nat) 0xd0 0x120 0x118 0x120
  [YP09.mkChunk 0xd0 (CVal 8 (SOff 33 0)); YP09.mkChunk 0xf0 (CVal 8 (SOff 35 0));
   YP09.mkChunk 0x110 (CVal 8 (SOff 32 0xf0)); YP09.mkChunk 0x118 (CVal 8 (SOff 34 0))].
Definition c5_tE : YP09.region := YP09.mkRegion (Some 32%nat) 0xf0 0xf8 0xf0 0xf8 [].
Definition c5_tN : YP09.region := YP09.mkRegion (Some 36%nat) 0 1 0 1 [YP09.mkChunk 0 (CZero 1)].
Definition c5_tfacts : facts := mkFacts [] [] [(SAlu ALU_ADD (SOff 27 0) (SOff 25 0), SOff 36 0)].
Definition ss_c5T : sstate := mkSS C5_RET sr_atoms [c5_tR; c5_tE; c5_tN] None c5_tfacts.
Definition c5_textra (F vb left pp n : Z) : list word :=
  [Z_to_bv 64 F; Z_to_bv 64 vb; Z_to_bv 64 left; Z_to_bv 64 pp; Z_to_bv 64 (F + 0xf8 + n)].
(* the tail's write set, and its exact write windows *)
Definition c5_TWr (R F : Z) : Z -> Prop := fun a => (R + 0x118 <= a < R + 0x120) \/ (F + 0xf0 <= a < F + 0x158).
Definition c5_TWw (R F n : Z) : Z -> Prop :=
  fun a => (R + 0x118 <= a < R + 0x120) \/ (F + 0xf0 <= a < F + 0xf8) \/ (F + 0xf8 + n <= a < F + 0xf8 + n + 1).
Lemma c5_T_wr : forall E rs R F n, YP09.skeleton rs = YP09.skeleton [c5_tR; c5_tE; c5_tN] ->
  bv_unsigned (ew E 9) = R -> bv_unsigned (ew E 32) = F -> bv_unsigned (ew E 36) = F + 0xf8 + n ->
  forall a, in_wrange E rs a -> c5_TWw R F n a.
Proof.
intros E rs R F n Hsk H9 H32 H36 a Ha. apply (in_wrange_skeleton E rs _ a Hsk) in Ha.
destruct Ha as (r & Hin & Ha). unfold c5_TWw. cbn [In] in Hin. repeat destruct Hin as [<-|Hin]; try contradiction;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val c5_tR c5_tE c5_tN] in Ha; rewrite ?H9, ?H32, ?H36 in Ha; lia.
Qed.
Lemma c5_T_awr : forall E rs STK sp0 FP bl0 blc lyc own R F pos n,
  YP09.skeleton rs = YP09.skeleton [c5_tR; c5_tE; c5_tN] ->
  bv_unsigned (ew E 9) = R -> bv_unsigned (ew E 32) = F -> bv_unsigned (ew E 36) = F + 0xf8 + n -> 0 <= n <= 31 ->
  R + 0x120 <= sp0 -> sp0 - STK <= R -> In (4, pos) own -> F = frame_addr lyc 4 pos ->
  awr_ok E rs STK sp0 FP bl0 blc lyc own.
Proof.
intros E rs STK sp0 FP bl0 blc lyc own R F pos n Hsk H9 H32 H36 Hn HR1 HR2 Hown HF a Ha.
apply (in_wrange_skeleton E rs _ a Hsk) in Ha.
destruct Ha as (r & Hin & Ha). unfold awr_byte. cbn [In] in Hin. repeat destruct Hin as [<-|Hin]; try contradiction;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val c5_tR c5_tE c5_tN] in Ha; rewrite ?H9, ?H32, ?H36 in Ha;
  first [ left; lia
        | right; right; right; exists 4, pos; split; [exact Hown|]; left;
          unfold in_zr; cbn [fst snd]; rewrite <- HF; change (fs_frame_bytes 4) with 1024; lia ].
Qed.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Hypothesis MCPY : aintrin_realizes rsegs B OCpy W7_MEMCPY.

(* ======================================== c5_head: 0x81d40 .. the call ======================================== *)
Definition c5_HR (W : world rsegs) (R F c : Z) (r : list byte) : bvmap 5 word -> (word -> option byte) -> Prop :=
fun regs2 mem2 =>
  getr regs2 1 = w64 C5_RET /\ getr regs2 10 = w64 (F + 0xf8) /\ getr regs2 11 = w64 (c5_src c r) /\
  getr regs2 12 = w64 (c5_n r) /\ getr regs2 24 = w64 (c5_src c r) /\ getr regs2 25 = w64 (c5_n r) /\
  getr regs2 27 = w64 (F + 0xf8) /\ val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x118) 8 (c5_left r) /\
  (forall i, 0 <= i < 104 -> mbyte rsegs (mrestrict (w_H W) mem2) (F + 0xf0 + i) = Some (Z_to_bv 8 0)).

Lemma c5_head : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word)
  (R F pos c vb pp kd : Z) (r : list byte),
  w6_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
  w6b_in B W memc regs R F c vb pp kd r ->
  SRr rsegs W (cfg_at rsegs W6B_D5 regs memc mdc)
  (w7_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k W7_MEMCPY regs memc mdc [1; 10; 11; 12; 24; 25; 27]%bv
    (c5_HWr R F) (c5_HR W R F c r)).
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c vb pp kd r Hctx Hin.
destruct Hctx as (HJ & HR16 & HRsp & HspR & Hown & HF & _).
destruct Hin as (_ & _ & _ & H9 & H23 & H24 & H14 & H25 & H21 & H27 & _ & Vf8 & Vb0 & Vf0 & Vc0 & V20 & V70 & V80 &
  Hvb & _ & Hpp & Hpp2 & HF4 & HFc & _ & Ez & Hrae & _ & Hc1 & Hwin & _ & Hdis).
destruct Hwin as (Hg & Hrain & Hc0 & Hcr & Ham & Hdr).
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _). clear Hstk.
assert (Hin3 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 4 pos HAR Hin3) as (_ & HFapp & HFpres & _).
rewrite <- HF in HFapp, HFpres. change (fs_frame_bytes 4) with 1024 in HFapp, HFpres.
pose proof asan_consts as (C1 & _).
unfold T_SEG_STK, ASTACK in HspR, Hdr.
assert (HRb1 : alloc_ceiling <= R) by lia.
assert (HRb2 : R + 0x1e0 <= 2 ^ 47) by lia.
assert (Hcb : c + Z.of_nat (length r) <= 2 ^ 47 - 1)
  by (pose proof Ham as X; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in X; lia).
assert (Hshb : forall a, F + 0xf0 <= a < F + 0x158 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 17592186044416)).
{ intros a Ha. pose proof HFapp as X. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in X.
  unfold SHADOW_OFF. lia. }
assert (Pw : forall o, (0x68 <= o < 0x70 \/ 0x118 <= o < 0x120) -> apresent (w_H W) memc (R + o))
  by (intros o Ho; apply Hpres; lia).
assert (Pe : forall o, 0 <= o < 104 -> apresent (w_H W) memc (F + 0xf0 + o))
  by (intros o Ho; exact (proj1 (HFpres (F + 0xf0 + o) ltac:(lia)))).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ c5_HWr R F a -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
  by reflexivity.
assert (GE : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) memc)) by apply mem_grows_refl.
clear Hpres HFpres Hfrs HAR Hin3 Hceil Hslo Hshi H47 HFapp Ham.
unfold cfg_at. change (w64 W6B_D5) with (Z_to_bv 64 W6B_D5).
destruct r as [|m r1].
- (* ---- no byte left: n' = 0, the source at c ---- *)
  destruct (c5_nil c) as (Q1 & Q2 & Q3 & _).
  pose proof (eb_entry W6B_D5 false W regs memc R F c vb (Z.of_nat (length (@nil byte)) + 1) 0 pp
    ltac:(unfold W6B_D5; lia) H9 H23 H24 H21 H27 HRb1 HRb2 HR16 HF4 HFc ltac:(lia) Hvb ltac:(cbn [length]; lia)
    ltac:(lia) ltac:(lia) Hpp2 V20 V70 V80 Vb0 Vc0 Vf0 Vf8 Pw Ez Pe ltac:(intros X; discriminate X)) as HS.
  remember (Ereg regs (eb_extra F vb (Z.of_nat (length (@nil byte)) + 1) 0)) as E eqn:HE.
  assert (HAE : env_agree 32 (Ereg regs (eb_extra F vb (Z.of_nat (length (@nil byte)) + 1) 0)) E)
    by (subst E; apply env_agree_refl).
  assert (U9 : bv_unsigned (ew E 9) = R) by (subst E; exact (eb_U_reg regs _ 9 9%bv R eq_refl H9 ltac:(lia))).
  assert (E32 : ew E 32 = Z_to_bv 64 F) by (subst E; exact (ew_Ereg_extra regs _ 0)).
  assert (U32 : bv_unsigned (ew E 32) = F) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (E24 : ew E 24 = Z_to_bv 64 c) by (subst E; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact H24).
  assert (SHOK : sh_ok rsegs EBx eb_SH E (mrestrict (w_H W) memc))
    by (subst E; exact (eb_shok regs (w_H W) memc F vb _ _ H23 HF4 HFc Hrae Hshb)).
  clear HE.
  pose proof (st_ok_pin_lit rsegs _ _ _ (25%bv : bv 5) 0 HS eq_refl
    ltac:(cbn [ms_regs restrict mkst]; rewrite H25; reflexivity)) as HS1.
  clear HS. rename HS1 into HS.
  (* 0x81d40 .. 0x82068 .. 0x81d6c .. the call *)
  aj_run_to_tok eb_tbl_ok HS HJ SHOK Espan W7_MEMCPY.
  + apply (c5_eb_awr _ _ false _ _ _ _ _ _ _ R F pos); [vm_compute; reflexivity | exact U9 | exact U32 | lia | lia
      | exact Hown | exact HF].
  + c5_keep (c5_HWr R F) ltac:(apply (c5_eb_wr _ _ false R F); [vm_compute; reflexivity
      | rewrite ?ew_ewset_other by lia; exact U9 | rewrite ?ew_ewset_other by lia; exact U32]).
    eapply (w7_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | c5_kio | | exact KE | exact GE | ].
    * eapply (HPgSteps.regs_kept_of_st_ok rsegs _ _ _ regs _ (w_H W) _ HS); [env_agree_chain HAE | vm_compute; reflexivity].
    * unfold c5_HR. rewrite Q1, Q2, Q3. c5_ew HS E32. c5_ew HS E24. c5_ew HS U9. c5_ew HS U32.
      refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
      -- c5_reg HS (1%bv : bv 5). unfold w64, C5_RET. apply c5_den_lit. lia.
      -- c5_reg HS (10%bv : bv 5). unfold w64. apply c5_den_off; [exact E32' | lia | lia].
      -- c5_reg HS (11%bv : bv 5). unfold w64. apply c5_den0; [exact E24' | lia].
      -- c5_reg HS (12%bv : bv 5). unfold w64. apply c5_den_lit. lia.
      -- c5_reg HS (24%bv : bv 5). unfold w64. apply c5_den0; [exact E24' | lia].
      -- c5_reg HS (25%bv : bv 5). unfold w64. apply c5_den_lit. lia.
      -- c5_reg HS (27%bv : bv 5). unfold w64. apply c5_den_off; [exact E32' | lia | lia].
      -- c5_rnth HS 2%nat Hr2.
         exact (w7_field _ _ 9%nat R _ _ _ _ _ 0x118 8 (SLit 0) 0 Hr2 U9' ltac:(c5_in) (c5_den_lit _ 0 ltac:(lia))
           ltac:(cbn; lia) ltac:(cbn; lia)).
      -- c5_rnth HS 3%nat Hr3. intros i Hi.
         pose proof (eb_chunk_zero _ _ _ 0xf0 104 Hr3 ltac:(c5_in) i Hi) as Z0.
         cbn [YP09.r_base base_val] in Z0. rewrite U32' in Z0. exact Z0.
- (* ---- a byte m, the rest r1 ---- *)
  pose proof (byte_range m) as Hmb.
  destruct (c5_cons c m r1) as (Q1 & Q2 & Q3 & _).
  assert (Hm0 : val_mem rsegs (mrestrict (w_H W) memc) c 1 (bv_unsigned m)).
  { destruct (Hg 0%nat ltac:(cbn [length map]; lia)) as [Hv _]. cbn [nth map] in Hv.
    replace (c + Z.of_nat 0) with c in Hv by lia. exact Hv. }
  assert (Hpos : c + 1 <= R + 0x48 \/ R + 0x120 <= c).
  { pose proof (Hdr c ltac:(cbn [length]; lia)). lia. }
  assert (Hpos2 : c + 1 <= F + 0xf0 \/ F + 0x158 <= c).
  { pose proof (Hdis c ltac:(cbn [length]; lia)). lia. }
  pose proof (eb_entry W6B_D5 true W regs memc R F c vb (Z.of_nat (length (m :: r1)) + 1) (bv_unsigned m) pp
    ltac:(unfold W6B_D5; lia) H9 H23 H24 H21 H27 HRb1 HRb2 HR16 HF4 HFc ltac:(lia) Hvb ltac:(lia) Hmb
    ltac:(lia) Hpp2 V20 V70 V80 Vb0 Vc0 Vf0 Vf8 Pw Ez Pe (fun _ => conj Hm0 (conj Hpos Hpos2))) as HS.
  clear Hpos Hpos2.
  remember (Ereg regs (eb_extra F vb (Z.of_nat (length (m :: r1)) + 1) (bv_unsigned m))) as E eqn:HE.
  assert (HAE : env_agree 32 (Ereg regs (eb_extra F vb (Z.of_nat (length (m :: r1)) + 1) (bv_unsigned m))) E)
    by (subst E; apply env_agree_refl).
  assert (U9 : bv_unsigned (ew E 9) = R) by (subst E; exact (eb_U_reg regs _ 9 9%bv R eq_refl H9 ltac:(lia))).
  assert (E32 : ew E 32 = Z_to_bv 64 F) by (subst E; exact (ew_Ereg_extra regs _ 0)).
  assert (U32 : bv_unsigned (ew E 32) = F) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (E14 : ew E 14 = Z_to_bv 64 (c - 1)) by (subst E; rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact H14).
  assert (E23 : ew E 23 = Z_to_bv 64 SHADOW_OFF)
    by (subst E; rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact H23).
  assert (E24 : ew E 24 = Z_to_bv 64 c) by (subst E; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact H24).
  assert (E25 : ew E 25 = Z_to_bv 64 (Z.of_nat (length (m :: r1))))
    by (subst E; rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25).
  assert (E34 : ew E 34 = Z_to_bv 64 (Z.of_nat (length (m :: r1)) + 1)) by (subst E; exact (ew_Ereg_extra regs _ 2)).
  assert (E35 : ew E 35 = Z_to_bv 64 (bv_unsigned m)) by (subst E; exact (ew_Ereg_extra regs _ 3)).
  assert (SHOK : sh_ok rsegs EBx eb_SH E (mrestrict (w_H W) memc))
    by (subst E; exact (eb_shok regs (w_H W) memc F vb _ _ H23 HF4 HFc Hrae Hshb)).
  clear HE.
  cbn [length] in Hcb, Hrain.
  (* 0x81d40 beqz s9: s9 = |r| > 0 *)
  srr_branch_tok eb_tbl_ok HS SHOK Espan.
  + exfalso. rewrite branch_eq_U, (U_atom _ 25 _ E25), c5_U_lit in Hc by (cbn [length]; lia).
    apply Z.eqb_eq in Hc. cbn [length] in Hc. lia.
  + (* 0x81d44 .. the `bltu` at 0x81d68 *)
    clear Hc.
    aj_run_to_tok eb_tbl_ok HS HJ SHOK Espan W7_MEMCPY.
    * apply (obl_of_range rsegs (w_H W) memc _ EBx _ _ c (Z.of_nat (Datatypes.S (length r1))) Hrain).
      -- apply (U_atom _ 23 SHADOW_OFF E23). unfold SHADOW_OFF. lia.
      -- rewrite (U_atom _ 24 c E24) by lia. lia.
      -- rewrite (U_atom _ 24 c E24) by lia. lia.
    * apply (c5_eb_awr _ _ true _ _ _ _ _ _ _ R F pos); [vm_compute; reflexivity | exact U9 | exact U32 | lia | lia
        | exact Hown | exact HF].
    * c5_keep (c5_HWr R F) ltac:(apply (c5_eb_wr _ _ true R F); [vm_compute; reflexivity
        | rewrite ?ew_ewset_other by lia; exact U9 | rewrite ?ew_ewset_other by lia; exact U32]).
      c5_ew HS E35. c5_ew HS E34. c5_ew HS U9. c5_ew HS U32.
      srr_branch_tok eb_tbl_ok HS SHOK Espan.
      -- (* m mod 32 < |r1|: n' = m mod 32 *)
         rewrite branch_ltu_U, (c5_s9_U _ _ E35' Hmb), (U_atom_off _ 34 _ (-2) E34') in Hc by (cbn [length]; lia).
         apply Z.ltb_lt in Hc. cbn [length] in Hc.
         aj_run_to_tok eb_tbl_ok HS HJ SHOK Espan W7_MEMCPY.
         ++ apply (c5_eb_awr _ _ true _ _ _ _ _ _ _ R F pos); [vm_compute; reflexivity | exact U9' | exact U32' | lia
              | lia | exact Hown | exact HF].
         ++ c5_keep (c5_HWr R F) ltac:(apply (c5_eb_wr _ _ true R F); [vm_compute; reflexivity
              | rewrite ?ew_ewset_other by lia; exact U9 | rewrite ?ew_ewset_other by lia; exact U32]).
            eapply (w7_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | c5_kio | | exact KE | exact GE | ].
            ** eapply (HPgSteps.regs_kept_of_st_ok rsegs _ _ _ regs _ (w_H W) _ HS);
                 [env_agree_chain HAE | vm_compute; reflexivity].
            ** unfold c5_HR. rewrite Q1, Q2, Q3, Z.min_l by lia.
               clear E35' E34' U9' U32'.
               c5_ew HS E35. c5_ew HS E34. c5_ew HS E32. c5_ew HS E14. c5_ew HS U9. c5_ew HS U32.
               refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
               --- c5_reg HS (1%bv : bv 5). unfold w64, C5_RET. apply c5_den_lit. lia.
               --- c5_reg HS (10%bv : bv 5). unfold w64. apply c5_den_off; [exact E32' | lia | lia].
               --- c5_reg HS (11%bv : bv 5). unfold w64. rewrite (c5_den_off _ 14 (c - 1) 2 E14') by lia.
                   f_equal. lia.
               --- c5_reg HS (12%bv : bv 5). unfold w64. exact (c5_s9z_val _ _ E35' Hmb).
               --- c5_reg HS (24%bv : bv 5). unfold w64. rewrite (c5_den_off _ 14 (c - 1) 2 E14') by lia.
                   f_equal. lia.
               --- c5_reg HS (25%bv : bv 5). unfold w64. exact (c5_s9_val _ _ E35' Hmb).
               --- c5_reg HS (27%bv : bv 5). unfold w64. apply c5_den_off; [exact E32' | lia | lia].
               --- c5_rnth HS 2%nat Hr2.
                   exact (w7_field _ _ 9%nat R _ _ _ _ _ 0x118 8 (SOff 34 (-2)) (Z.of_nat (length r1)) Hr2 U9'
                     ltac:(c5_in) ltac:(rewrite (c5_den_off _ 34 _ (-2) E34') by (cbn [length]; lia);
                       f_equal; cbn [length]; lia)
                     ltac:(cbn; lia) ltac:(cbn; lia)).
               --- c5_rnth HS 3%nat Hr3. intros i Hi.
                   pose proof (eb_chunk_zero _ _ _ 0xf0 104 Hr3 ltac:(c5_in) i Hi) as Z0.
                   cbn [YP09.r_base base_val] in Z0. rewrite U32' in Z0. exact Z0.
      -- (* m mod 32 >= |r1|: n' = |r1| *)
         rewrite branch_ltu_U, (c5_s9_U _ _ E35' Hmb), (U_atom_off _ 34 _ (-2) E34') in Hc by (cbn [length]; lia).
         apply Z.ltb_ge in Hc. cbn [length] in Hc.
         aj_run_to_tok eb_tbl_ok HS HJ SHOK Espan W7_MEMCPY.
         ++ apply (c5_eb_awr _ _ true _ _ _ _ _ _ _ R F pos); [vm_compute; reflexivity | exact U9' | exact U32' | lia
              | lia | exact Hown | exact HF].
         ++ c5_keep (c5_HWr R F) ltac:(apply (c5_eb_wr _ _ true R F); [vm_compute; reflexivity
              | rewrite ?ew_ewset_other by lia; exact U9 | rewrite ?ew_ewset_other by lia; exact U32]).
            eapply (w7_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | c5_kio | | exact KE | exact GE | ].
            ** eapply (HPgSteps.regs_kept_of_st_ok rsegs _ _ _ regs _ (w_H W) _ HS);
                 [env_agree_chain HAE | vm_compute; reflexivity].
            ** unfold c5_HR. rewrite Q1, Q2, Q3, Z.min_r by lia.
               clear E35' E34' U9' U32'.
               c5_ew HS E35. c5_ew HS E34. c5_ew HS E32. c5_ew HS E14. c5_ew HS U9. c5_ew HS U32.
               refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
               --- c5_reg HS (1%bv : bv 5). unfold w64, C5_RET. apply c5_den_lit. lia.
               --- c5_reg HS (10%bv : bv 5). unfold w64. apply c5_den_off; [exact E32' | lia | lia].
               --- c5_reg HS (11%bv : bv 5). unfold w64. rewrite (c5_den_off _ 14 (c - 1) 2 E14') by lia.
                   f_equal. lia.
               --- c5_reg HS (12%bv : bv 5). unfold w64.
                   rewrite (c5_den_off _ 34 _ (-2) E34') by (cbn [length]; lia). f_equal. cbn [length]. lia.
               --- c5_reg HS (24%bv : bv 5). unfold w64. rewrite (c5_den_off _ 14 (c - 1) 2 E14') by lia.
                   f_equal. lia.
               --- c5_reg HS (25%bv : bv 5). unfold w64.
                   rewrite (c5_den_off _ 34 _ (-2) E34') by (cbn [length]; lia). f_equal. cbn [length]. lia.
               --- c5_reg HS (27%bv : bv 5). unfold w64. apply c5_den_off; [exact E32' | lia | lia].
               --- c5_rnth HS 2%nat Hr2.
                   exact (w7_field _ _ 9%nat R _ _ _ _ _ 0x118 8 (SOff 34 (-2)) (Z.of_nat (length r1)) Hr2 U9'
                     ltac:(c5_in) ltac:(rewrite (c5_den_off _ 34 _ (-2) E34') by (cbn [length]; lia);
                       f_equal; cbn [length]; lia)
                     ltac:(cbn; lia) ltac:(cbn; lia)).
               --- c5_rnth HS 3%nat Hr3. intros i Hi.
                   pose proof (eb_chunk_zero _ _ _ 0xf0 104 Hr3 ltac:(c5_in) i Hi) as Z0.
                   cbn [YP09.r_base base_val] in Z0. rewrite U32' in Z0. exact Z0.
Qed.

(* ======================================== c5_tail: 0x81d88 .. J ======================================== *)
Lemma c5_tail : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word)
  (R F pos src lf vb pp kd n : Z) (p : list byte),
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  R mod 16 = 0 -> R + 0x1e0 <= sp0 -> sp0 - STK <= R - T_SEG_STK -> In (4, pos) own -> F = frame_addr lyc 4 pos ->
  n = Z.of_nat (length p) ->
  getr regs 9 = w64 R -> getr regs 20 = w64 (kd - 256 * (kd / 128)) -> getr regs 21 = w64 (pp + 0x4000) ->
  getr regs 24 = w64 src -> getr regs 25 = w64 n -> getr regs 27 = w64 (F + 0xf8) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf0) 8 pp ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xd0) 8 vb ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x110) 8 (F + 0xf0) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 lf ->
  0 <= kd < 256 -> 0 <= vb < 2 ^ 64 -> 0 <= pp -> pp + 0x4000 < 2 ^ 64 -> 0 <= src -> src + n < 2 ^ 64 ->
  (length p <= 31)%nat -> n <= lf < 2 ^ 64 ->
  hm_bytes rsegs (w_H W) memc (F + 0xf8) p ->
  (forall i, 0 <= i < 96 - n -> aview rsegs (w_H W) memc (F + 0xf8 + n + i) = Some 0) ->
  SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 C5_RET) memc (seg_rom rsegs)) mdc)
  (w7_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k W6_J regs memc mdc [10; 11; 12; 20; 24; 25; 27]%bv
    (c5_TWr R F)
    (fun regs2 mem2 => getr regs2 20 = w64 vb /\ getr regs2 21 = w64 (pp + 0x4000) /\ getr regs2 27 = w64 pp /\
       getr regs2 25 = w64 (src + n) /\ val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x118) 8 (lf - n) /\
       hm_bytes rsegs (w_H W) mem2 (F + 0xf0)
         (le32 8 ++ le32 (n + (if Z.testbit kd 7 then 0 else 1)) ++ p ++ zeros (96 - length p)))).
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos src lf vb pp kd n p
  HJ HR16 HRsp HspR Hown HF Hneq H9 H20 H21 H24 H25 H27 V80 Vb0 Vf0 Vf8 Hkd Hvb Hpp Hpp2 Hsrc Hsrc2 Hpl Hlf Bp Hz.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _). clear Hstk.
assert (Hin3 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 4 pos HAR Hin3) as (_ & HFapp & HFpres & _).
rewrite <- HF in HFapp, HFpres. change (fs_frame_bytes 4) with 1024 in HFapp, HFpres.
pose proof asan_consts as (C1 & _).
unfold T_SEG_STK, ASTACK in HspR.
assert (HFb : 4096 <= F /\ F + 1024 <= R).
{ pose proof HFapp as X. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in X. lia. }
assert (Hn : 0 <= n <= 31) by lia.
assert (HRb2 : R + 0x1e0 <= 2 ^ 47) by lia.
remember (Ereg regs (c5_textra F vb lf pp n)) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs (c5_textra F vb lf pp n)) E) by (subst E; apply env_agree_refl).
assert (U9 : bv_unsigned (ew E 9) = R) by (subst E; exact (eb_U_reg regs _ 9 9%bv R eq_refl H9 ltac:(lia))).
assert (E20 : ew E 20 = Z_to_bv 64 (kd - 256 * (kd / 128)))
  by (subst E; rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
assert (E21 : ew E 21 = Z_to_bv 64 (pp + 0x4000)) by (subst E; rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact H21).
assert (E24 : ew E 24 = Z_to_bv 64 src) by (subst E; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact H24).
assert (E25 : ew E 25 = Z_to_bv 64 n) by (subst E; rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25).
assert (E27 : ew E 27 = Z_to_bv 64 (F + 0xf8)) by (subst E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
assert (E32 : ew E 32 = Z_to_bv 64 F) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 vb) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 lf) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 pp) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (F + 0xf8 + n)) by (subst E; exact (ew_Ereg_extra regs _ 4)).
assert (U32 : bv_unsigned (ew E 32) = F) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = F + 0xf8 + n) by (rewrite E36; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs E ss_c5T (restrict (w_H W) (mkst regs (Z_to_bv 64 C5_RET) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_c5T. rewrite HE. apply (entry_st_ok_full rsegs); try rewrite <- HE.
  - rewrite HE. apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + unfold c5_tR. apply (hm_rw_region rsegs _ _ _ 9%nat R); [exact U9 | lia | lia | intros o Ho; apply Hpres; lia |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
      * apply (chunk_ok_val rsegs _ _ _ _ _ _ vb);
          [apply c5_den0; [exact E33 | lia] | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact Vb0].
      * apply (chunk_ok_val rsegs _ _ _ _ _ _ pp);
          [apply c5_den0; [exact E35 | lia] | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact V80].
      * apply (chunk_ok_val rsegs _ _ _ _ _ _ (F + 0xf0));
          [apply c5_den_off; [exact E32 | lia | lia] | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia
          | exact Vf0].
      * apply (chunk_ok_val rsegs _ _ _ _ _ _ lf);
          [apply c5_den0; [exact E34 | lia] | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact Vf8].
    + unfold c5_tE. apply (hm_rw_region rsegs _ _ _ 32%nat F); [exact U32 | lia | lia | | apply Forall_nil].
      intros o Ho. exact (proj1 (HFpres (F + o) ltac:(lia))).
    + unfold c5_tN. apply (hm_rw_region rsegs _ _ _ 36%nat (F + 0xf8 + n)); [exact U36 | lia | lia | |].
      * intros o Ho. exact (proj1 (HFpres (F + 0xf8 + n + o) ltac:(lia))).
      * apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. intros i Hi.
        apply (hm_aview_mbyte rsegs). replace (F + 0xf8 + n + 0 + i) with (F + 0xf8 + n + 0) by lia.
        exact (Hz 0 ltac:(lia)).
  - cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val c5_tR c5_tE c5_tN]. rewrite U9, U32, U36. repeat split; lia.
  - unfold facts_ok. cbn [c5_tfacts f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [exact I|]. split; [exact I|]. split; [|exact I].
    rewrite (c5_den_add E 27 25 (F + 0xf8) n E27 E25) by lia. rewrite (c5_den0 E 36 _ E36) by lia. reflexivity. }
clear HE.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ c5_TWw R F n a -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
  by reflexivity.
assert (GE : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) memc)) by apply mem_grows_refl.
clear Hpres HFpres Hfrs HAR Hin3 Hceil Hslo Hshi H47 HFapp.
(* 0x81d88 .. the `bltz s4` at 0x81d8c *)
aj_run_to eb_tbl_ok HS HJ W6_J.
- apply (c5_T_awr _ _ _ _ _ _ _ _ _ R F pos n); [vm_compute; reflexivity | exact U9 | exact U32 | exact U36 | lia | lia
    | lia | exact Hown | exact HF].
- c5_keep (c5_TWw R F n) ltac:(apply (c5_T_wr _ _ R F n); [vm_compute; reflexivity | exact U9 | exact U32 | exact U36]).
  srr_branch_with eb_tbl_ok HS.
  + (* kind & 0x80: no NUL, e.size = n' *)
    rewrite (c5_bltz E kd E20 Hkd) in Hc.
    aj_run_to eb_tbl_ok HS HJ W6_J.
    * apply (c5_T_awr _ _ _ _ _ _ _ _ _ R F pos n); [vm_compute; reflexivity | exact U9 | exact U32 | exact U36 | lia
        | lia | lia | exact Hown | exact HF].
    * c5_keep (c5_TWw R F n) ltac:(apply (c5_T_wr _ _ R F n); [vm_compute; reflexivity | exact U9 | exact U32
        | exact U36]).
      eapply (w7_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | c5_kio | | | exact GE | ].
      -- eapply (HPgSteps.regs_kept_of_st_ok rsegs _ _ _ regs _ (w_H W) _ HS); [exact HAE | vm_compute; reflexivity].
      -- intros a Ha Hw. apply KE; [exact Ha|]. intros X. apply Hw. unfold c5_TWw, c5_TWr in *. lia.
      -- cbv beta. rewrite Hc.
         refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
         ++ c5_reg HS (20%bv : bv 5). unfold w64. apply c5_den0; [exact E33 | lia].
         ++ c5_reg HS (21%bv : bv 5). unfold w64. apply c5_den0; [exact E21 | lia].
         ++ c5_reg HS (27%bv : bv 5). unfold w64. apply c5_den0; [exact E35 | lia].
         ++ c5_reg HS (25%bv : bv 5). unfold w64. apply c5_den_add; [exact E24 | exact E25 | lia | lia | lia].
         ++ c5_rnth HS 0%nat Hr0.
            exact (w7_field _ _ 9%nat R _ _ _ _ _ 0x118 8 (SAlu ALU_ADD (SMd M_MUL (SOff 25 0) (SLit (-1))) (SOff 34 0))
              (lf - n) Hr0 U9 ltac:(c5_in) (c5_den_sub E 25 34 n lf E25 E34 ltac:(lia) ltac:(lia))
              ltac:(cbn; lia) ltac:(cbn; lia)).
         ++ c5_rnth HS 1%nat Hr1. c5_rnth HS 2%nat Hr2. rewrite Z.add_0_r.
            apply (c5_e_bytes _ _ F p n n); [exact Hneq | lia | | | |].
            ** exact (w7_field _ _ 32%nat F _ _ _ _ _ 0xf0 4 (SLit 8) 8 Hr1 U32 ltac:(c5_in)
                 (c5_den_lit _ 8 ltac:(lia)) ltac:(cbn; lia) ltac:(cbn; lia)).
            ** exact (w7_field _ _ 32%nat F _ _ _ _ _ 0xf4 4 (SOff 25 0) n Hr1 U32 ltac:(c5_in)
                 (c5_den0 _ 25 n E25 ltac:(lia)) ltac:(cbn; lia) ltac:(cbn; lia)).
            ** apply (hm_bytes_kept rsegs (w_H W) memc); [exact Bp|]. intros x Hx. apply KE; [lia|].
               unfold c5_TWw. lia.
            ** intros i Hi. destruct (Z.eq_dec i 0) as [->|Hi0].
               --- pose proof (eb_chunk_zero _ _ _ 0 1 Hr2 ltac:(c5_in) 0 ltac:(lia)) as Z0.
                   cbn [YP09.r_base base_val] in Z0. rewrite U36 in Z0.
                   lazymatch type of Z0 with mbyte _ _ ?a = _ => replace a with (F + 0xf8 + n + 0) in Z0 by lia end.
                   apply c5_aview0. exact Z0.
               --- rewrite KE by (unfold c5_TWw; lia). exact (Hz i Hi).
  + (* the NUL at e.body + n', e.size = n' + 1 *)
    rewrite (c5_bltz E kd E20 Hkd) in Hc.
    aj_run_to eb_tbl_ok HS HJ W6_J.
    * apply (c5_T_awr _ _ _ _ _ _ _ _ _ R F pos n); [vm_compute; reflexivity | exact U9 | exact U32 | exact U36 | lia
        | lia | lia | exact Hown | exact HF].
    * c5_keep (c5_TWw R F n) ltac:(apply (c5_T_wr _ _ R F n); [vm_compute; reflexivity | exact U9 | exact U32
        | exact U36]).
      eapply (w7_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | c5_kio | | | exact GE | ].
      -- eapply (HPgSteps.regs_kept_of_st_ok rsegs _ _ _ regs _ (w_H W) _ HS); [exact HAE | vm_compute; reflexivity].
      -- intros a Ha Hw. apply KE; [exact Ha|]. intros X. apply Hw. unfold c5_TWw, c5_TWr in *. lia.
      -- cbv beta. rewrite Hc.
         refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
         ++ c5_reg HS (20%bv : bv 5). unfold w64. apply c5_den0; [exact E33 | lia].
         ++ c5_reg HS (21%bv : bv 5). unfold w64. apply c5_den0; [exact E21 | lia].
         ++ c5_reg HS (27%bv : bv 5). unfold w64. apply c5_den0; [exact E35 | lia].
         ++ c5_reg HS (25%bv : bv 5). unfold w64. apply c5_den_add; [exact E24 | exact E25 | lia | lia | lia].
         ++ c5_rnth HS 0%nat Hr0.
            exact (w7_field _ _ 9%nat R _ _ _ _ _ 0x118 8 (SAlu ALU_ADD (SMd M_MUL (SOff 25 0) (SLit (-1))) (SOff 34 0))
              (lf - n) Hr0 U9 ltac:(c5_in) (c5_den_sub E 25 34 n lf E25 E34 ltac:(lia) ltac:(lia))
              ltac:(cbn; lia) ltac:(cbn; lia)).
         ++ c5_rnth HS 1%nat Hr1. c5_rnth HS 2%nat Hr2.
            apply (c5_e_bytes _ _ F p n (n + 1)); [exact Hneq | lia | | | |].
            ** exact (w7_field _ _ 32%nat F _ _ _ _ _ 0xf0 4 (SLit 8) 8 Hr1 U32 ltac:(c5_in)
                 (c5_den_lit _ 8 ltac:(lia)) ltac:(cbn; lia) ltac:(cbn; lia)).
            ** exact (w7_field _ _ 32%nat F _ _ _ _ _ 0xf4 4 (SOff 25 1) (n + 1) Hr1 U32 ltac:(c5_in)
                 (c5_den_off _ 25 n 1 E25 ltac:(lia) ltac:(lia)) ltac:(cbn; lia) ltac:(cbn; lia)).
            ** apply (hm_bytes_kept rsegs (w_H W) memc); [exact Bp|]. intros x Hx. apply KE; [lia|].
               unfold c5_TWw. lia.
            ** intros i Hi. destruct (Z.eq_dec i 0) as [->|Hi0].
               --- pose proof (w7_field _ _ 36%nat (F + 0xf8 + n) _ _ _ _ _ 0 1 (SLit 0) 0 Hr2 U36 ltac:(c5_in)
                     (c5_den_lit _ 0 ltac:(lia)) ltac:(cbn; lia) ltac:(cbn; lia)) as V.
                   exact (hm_val1_aview rsegs _ _ _ _ V ltac:(lia)).
               --- rewrite KE by (unfold c5_TWw; lia). exact (Hz i Hi).
Qed.

(* ======================================== the block lemma ======================================== *)
Theorem w6b_c5 : w6b_c5_stmt B MT.
Proof using MTL LAWS MCPY.
unfold w6b_c5_stmt, w6b_case_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c vb pp b r Hctx Hkd5 Hin _.
cbv beta in Hkd5.
pose proof (c5_head STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c vb pp (bv_unsigned b) r Hctx Hin)
  as HH.
destruct Hctx as (HJ & HR16 & HRsp & HspR & Hown & HF & _).
destruct Hin as (H2 & H3 & H4 & H9 & H23 & H24 & H14 & H25 & H21 & H27 & H20 & Vf8 & Vb0 & Vf0 & Vc0 & V20 & V70 & V80 &
  Hvb & Hkd & Hpp & Hpp2 & HF4 & HFc & _ & Ez & Hrae & Hhe & Hc1 & Hwin & Hhin & Hdis).
destruct Hwin as (Hg & Hrain & Hc0 & Hcr & Ham & Hdr).
specialize (H20 ltac:(lia)).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _). clear Hstk.
assert (Hin3 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 4 pos HAR Hin3) as (_ & HFapp & _ & _).
rewrite <- HF in HFapp. change (fs_frame_bytes 4) with 1024 in HFapp.
pose proof asan_consts as (C1 & _).
unfold T_SEG_STK, ASTACK in HspR, Hdr.
assert (HRb1 : 0x7fff7f800000 <= R) by lia.
assert (HRb2 : R + 0x1e0 <= 2 ^ 47) by lia.
assert (HRb0 : alloc_ceiling + 16384 <= R) by lia.
assert (HFb : 4096 <= F /\ F + 1024 <= R /\ (F + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= F)).
{ pose proof HFapp as X. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in X. lia. }
assert (Hcb : c + Z.of_nat (length r) <= 2 ^ 47 - 1)
  by (pose proof Ham as X; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in X; lia).
clear HAR Hfrs Hin3 Hceil Hslo Hshi H47 HFapp.
remember (c5_src c r) as src eqn:Hsrc_eq. remember (c5_n r) as n eqn:Hn_eq. remember (c5_left r) as lf eqn:Hlf_eq.
destruct (c5_bounds c r) as (Bs1 & Bs2 & Bs3 & Bs4 & Bs5 & Bs6 & Bs7).
rewrite <- Hsrc_eq in Bs1, Bs2, Bs5. rewrite <- Hn_eq in Bs2, Bs3, Bs4, Bs7. rewrite <- Hlf_eq in Bs4, Bs5.
assert (Hpin : hm_bytes rsegs (w_H W) memc src (c5_p r)) by (subst src; exact (c5_input_bytes (w_H W) memc c r Hg)).
(* ---- 0x81d40 .. the call ---- *)
eapply SRr_bind; [exact HH|]. clear HH.
intros W1 c1 _ (-> & regs1 & mem1 & md1 & -> & HJ1 & Hio1 & Hk1 & Hm1 & Hp1 & HR1).
destruct HR1 as (R1 & R10 & R11 & R12 & R24 & R25 & R27 & Rf8 & Rez).
rewrite <- Hsrc_eq in R11, R24. rewrite <- Hn_eq in R12, R25. rewrite <- Hlf_eq in Rf8.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ c5_HWr R F a -> aview rsegs (w_H W) mem1 a = aview rsegs (w_H W) memc a)
  by exact Hm1.
clear Hm1.
(* the input after the head *)
assert (Hin1 : forall x, c <= x < c + Z.of_nat (length r) -> ~ c5_HWr R F x).
{ intros x Hx. pose proof (Hdr x Hx). pose proof (Hdis x Hx). unfold c5_HWr. lia. }
assert (Hsh1 : forall x, 0x7fff8000 <= x < 0x10007fff8000 -> ~ c5_HWr R F x) by (intros x Hx; unfold c5_HWr; lia).
assert (Hp1' : hm_bytes rsegs (w_H W) mem1 src (c5_p r)).
{ apply (hm_bytes_kept rsegs (w_H W) memc); [exact Hpin|]. intros x Hx. rewrite <- Bs7 in Hx.
  apply K1; [lia | apply Hin1; lia]. }
assert (Hsp1 : getr regs1 2 = w64 R).
{ transitivity (getr regs 2); [apply Hk1; [apply HPgW6aC2h.c2_nz; reflexivity | apply HPgW6aC2h.c2_notin; reflexivity]|].
  exact H2. }
(* ---- __asan_memcpy(e.body, src, n') ---- *)
eapply SRr_bind.
{ apply (w7_memcpy_at B LAWS MCPY W regs1 mem1 STK sp0 FP ly S W0 mem0 md0 own lyc Sc md1 k (F + 0xf8) src n
    (R - sp0) (w64 C5_RET) HJ1 R10 R11 R12).
  - lia.
  - lia.
  - lia.
  - unfold spZ. rewrite Hsp1. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, HR16, Hsp0al. reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - transitivity (getr regs 3); [apply Hk1; [apply HPgW6aC2h.c2_nz; reflexivity | apply HPgW6aC2h.c2_notin; reflexivity]|].
    exact H3.
  - transitivity (getr regs 4); [apply Hk1; [apply HPgW6aC2h.c2_nz; reflexivity | apply HPgW6aC2h.c2_notin; reflexivity]|].
    exact H4.
  - exact R1.
  - apply ret_ok_even. vm_compute. reflexivity.
  - intros a Ha. split.
    + unfold awr_byte. right; right; right. exists 4, pos. split; [exact Hown|]. left.
      unfold in_zr. cbn [fst snd]. rewrite <- HF. change (fs_frame_bytes 4) with 1024. lia.
    + unfold ESTACK. lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
  - apply (hm_ra_kept rsegs (w_H W) memc); [apply (ra_sub _ _ (F + 0xf0) 104); [exact Hrae | lia | lia]|].
    intros x Hx. apply K1; [pose proof (c5_band_ra x ltac:(lia)); lia | apply Hsh1; apply c5_band_ra; lia].
  - intros Hn0. apply (w7_hull_kept W memc mem1); [apply (hm_hull_sub _ (F + 0xf0) 104); [exact Hhe | lia | lia | lia]|].
    intros a Ha. pose proof (c5_band_hull (F + 0xf8) n a ltac:(lia) ltac:(lia) Hn0 Ha). apply K1; [lia | apply Hsh1; lia].
  - lia.
  - lia.
  - intros a Ha. split.
    + rewrite Bs7 in Ha. pose proof (proj1 (hm_bytes_aview rsegs (w_H W) mem1 src (c5_p r)) Hp1' (Z.to_nat (a - src))
        ltac:(lia)) as A.
      rewrite Z2Nat.id in A by lia. replace (src + (a - src)) with a in A by lia. rewrite A. discriminate.
    + unfold spZ. rewrite Hsp1. unfold w64. rewrite unsigned_lit_small by lia. unfold ESTACK.
      pose proof (Hdr a ltac:(lia)). lia.
  - destruct (Z_le_gt_dec n 0) as [Hn0|Hn0]; [lia|].
    destruct (Z_le_gt_dec (F + 0xf8 + n) src) as [X|X]; [left; exact X|].
    destruct (Z_le_gt_dec (src + n) (F + 0xf8)) as [Y|Y]; [right; exact Y|].
    exfalso. apply (Hdis (Z.max src (F + 0xf8))); lia.
  - unfold amem_range in *. lia.
  - apply (hm_ra_kept rsegs (w_H W) memc); [apply (ra_sub _ _ c (Z.of_nat (length r))); [exact Hrain | lia | lia]|].
    intros x Hx. apply K1; [pose proof (c5_band_ra x ltac:(lia)); lia | apply Hsh1; apply c5_band_ra; lia].
  - intros Hn0. apply (w7_hull_kept W memc mem1).
    + apply (hm_hull_sub _ c (Z.of_nat (length r))); [apply Hhin; lia | lia | lia | lia].
    + intros a Ha. pose proof (c5_band_hull src n a ltac:(lia) ltac:(lia) Hn0 Ha). apply K1; [lia | apply Hsh1; lia]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hio2 & HP2 & _ & HD2 & HK2 & Hpr2).
replace (sp0 + (R - sp0)) with R in HK2 by lia.
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ c5_HWr R F a -> ~ (F + 0xf8 <= a < F + 0xf8 + n) -> ~ (R - ESTACK <= a < R) ->
  aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memc a).
{ intros a Ha X1 X2 X3. rewrite (HK2 a Ha X2 X3). exact (K1 a Ha X1). }
(* ---- 0x81d88 .. J ---- *)
eapply SRr_mono.
{ apply (c5_tail STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W mem2 md2 regs2 R F pos src lf vb pp (bv_unsigned b) n
    (c5_p r) HJ2 HR16 HRsp ltac:(unfold T_SEG_STK, ASTACK; lia) Hown HF Bs7).
  - transitivity (getr regs1 9); [exact (HP2 9 ltac:(unfold acallee_saved; lia))|].
    transitivity (getr regs 9); [apply Hk1; [apply HPgW6aC2h.c2_nz; reflexivity | apply HPgW6aC2h.c2_notin; reflexivity]|].
    exact H9.
  - transitivity (getr regs1 20); [exact (HP2 20 ltac:(unfold acallee_saved; lia))|].
    transitivity (getr regs 20); [apply Hk1; [apply HPgW6aC2h.c2_nz; reflexivity | apply HPgW6aC2h.c2_notin; reflexivity]|].
    exact H20.
  - transitivity (getr regs1 21); [exact (HP2 21 ltac:(unfold acallee_saved; lia))|].
    transitivity (getr regs 21); [apply Hk1; [apply HPgW6aC2h.c2_nz; reflexivity | apply HPgW6aC2h.c2_notin; reflexivity]|].
    exact H21.
  - transitivity (getr regs1 24); [exact (HP2 24 ltac:(unfold acallee_saved; lia)) | exact R24].
  - transitivity (getr regs1 25); [exact (HP2 25 ltac:(unfold acallee_saved; lia)) | exact R25].
  - transitivity (getr regs1 27); [exact (HP2 27 ltac:(unfold acallee_saved; lia)) | exact R27].
  - apply (c5_val_kept (w_H W) (w_H W) memc mem2 _ _ _ V80). intros i Hi. apply K2; [lia | unfold c5_HWr; lia | lia
      | unfold ESTACK; lia].
  - apply (c5_val_kept (w_H W) (w_H W) memc mem2 _ _ _ Vb0). intros i Hi. apply K2; [lia | unfold c5_HWr; lia | lia
      | unfold ESTACK; lia].
  - apply (c5_val_kept (w_H W) (w_H W) memc mem2 _ _ _ Vf0). intros i Hi. apply K2; [lia | unfold c5_HWr; lia | lia
      | unfold ESTACK; lia].
  - apply (c5_val_kept (w_H W) (w_H W) mem1 mem2 _ _ _ Rf8). intros i Hi. apply HK2; [lia | lia | unfold ESTACK; lia].
  - exact Hkd.
  - exact Hvb.
  - lia.
  - exact Hpp2.
  - lia.
  - lia.
  - exact Bs6.
  - lia.
  - apply (hm_memcpy_bytes rsegs (w_H W) mem1 (w_H W) mem2 src); [exact Hp1'|]. intros i Hi. apply HD2. lia.
  - intros i Hi.
    rewrite (HK2 (F + 0xf8 + n + i) ltac:(lia) ltac:(lia) ltac:(unfold ESTACK; lia)).
    apply c5_aview0. replace (F + 0xf8 + n + i) with (F + 0xf0 + (8 + n + i)) by lia. apply Rez. lia. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & Hio3 & Hk3 & Hm3 & Hp3 & HR3).
destruct HR3 as (T20 & T21 & T27 & T25 & Tf8 & Te).
exists lyc, Sc, regs3, mem3, md3.
split; [reflexivity|]. split; [exact HJ3|].
split.
{ intros rr Hr0 Hn.
  rewrite (Hk3 rr Hr0 ltac:(intros X; apply Hn; cbv [In w6b_clob] in X |- *; tauto)).
  rewrite (c5_reg_cs regs1 regs2 rr HP2 (c5_cs rr Hr0 Hn)).
  apply Hk1; [exact Hr0 | intros X; apply Hn; cbv [In w6b_clob] in X |- *; tauto]. }
split; [reflexivity|]. split; [apply Permutation_refl|].
split; [eapply same_io_trans; [exact Hio1 | eapply same_io_trans; [exact Hio2 | exact Hio3]]|].
split; [apply mo_le_refl; exact MTL|].
split.
{ intros a Ha Hw. unfold w6b_wr, T_SEG_STK, ASTACK in Hw.
  rewrite (Hm3 a Ha ltac:(unfold c5_TWr; lia)). apply K2; [exact Ha | unfold c5_HWr; lia | lia | unfold ESTACK; lia]. }
(* ---- the state at J: the pod of Model.ent_build ---- *)
unfold w6b_J_R. rewrite (c5_model b r Hkd5). cbn [fst snd]. rewrite c5_skip_len, <- Hn_eq, <- Hlf_eq.
split; [exact T20|]. split; [exact T21|]. split; [exact T27|].
split; [rewrite T25; unfold w64; f_equal; lia|].
split; [exact Tf8|].
rewrite c5_ent_mem by lia. rewrite <- Bs7.
revert Te. destruct (Z.testbit (bv_unsigned b) 7); intros Te; exact Te.
Qed.

End d.
End b.

Print Assumptions w6b_c5.
