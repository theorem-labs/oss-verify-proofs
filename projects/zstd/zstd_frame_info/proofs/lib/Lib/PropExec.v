(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Export LiaTuning.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Class FPState := mkFP { fp_regs : bvmap 5 word; fp_csr : bv 32 }.
Definition fx0 : FPState := mkFP bvmap_empty (Z_to_bv 32 0).

Definition mkst `{fx : FPState} (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) : machine_state :=
  {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
     ms_svc_pending := None; ms_resv := None; ms_fcsr := fp_csr;
     ms_mem := mem; ms_rom := rom |}.

Section WithFP1.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition getr (regs : bvmap 5 word) (r : reg) : word :=
  if bv_eqb r 0 then Z_to_bv 64 0 else reg_get regs r.
Definition regupd (regs : bvmap 5 word) (r : reg) (v : word) : bvmap 5 word :=
  bvmap_set r v regs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma bv_eqb0_is_x0 : forall r : reg, bv_eqb r 0 = is_x0 r.
Proof. reflexivity. Qed.

#[using="Type"] Lemma is_x0_0 : is_x0 0 = true.
Proof. reflexivity. Qed.

#[using="Type"] Lemma bv_wrap64_mod : forall z : Z, bv_wrap 64 z = (z mod 2^64)%Z.
Proof. reflexivity. Qed.

#[using="Type"] Lemma bv_wrap32_mod : forall z : Z, bv_wrap 32 z = (z mod 2^32)%Z.
Proof. reflexivity. Qed.

#[using="Type"] Lemma bv_eqb_refl : forall {n} (a : bv n), bv_eqb a a = true.
Proof. intros n a. unfold bv_eqb. apply Z.eqb_refl. Qed.

#[using="Type"] Lemma bv_eqb_neq : forall {n} (a b : bv n), a <> b -> bv_eqb a b = false.
Proof.
  intros n a b Hne. unfold bv_eqb. apply Z.eqb_neq.
  intro Hu. apply Hne. apply bv_eq. exact Hu.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma arg_reg_0 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg).
Proof. apply bv_eq. reflexivity. Qed.
#[using="Type"] Lemma arg_reg_1 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg).
Proof. apply bv_eq. reflexivity. Qed.
#[using="Type"] Lemma arg_reg_2 : Z_to_bv 5 (10 + Z.of_nat 2) = (12 : reg).
Proof. apply bv_eq. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma Z_testbit_high : forall n a k, (0 <= n)%Z -> (0 <= a < 2^n)%Z -> (n <= k)%Z ->
  Z.testbit a k = false.
Proof.
  intros n a k Hn [Ha1 Ha2] Hk.
  exact (proj1 (Z.bounded_iff_bits_nonneg n a Hn Ha1) Ha2 k Hk).
Qed.

#[using="Type"] Lemma Z_bounded_by_bits : forall n a, (0 <= n)%Z -> (0 <= a)%Z ->
  (forall k, (n <= k)%Z -> Z.testbit a k = false) -> (a < 2^n)%Z.
Proof.
  intros n a Hn Ha Hb. exact (proj2 (Z.bounded_iff_bits_nonneg n a Hn Ha) Hb).
Qed.

#[using="Type"] Lemma Z_land_range : forall a b : Z, (0 <= a < 2^64)%Z -> (0 <= b)%Z ->
  (0 <= Z.land a b < 2^64)%Z.
Proof.
  intros a b Ha Hb. Local Ltac2 Set LiaHints.tbl := fun () => "0050=35497642355.735497643772.544204549936.556765665507.758230442238.700000100200600:00>SSS2HaS2HaS2Hk".
split; [apply Z.land_nonneg; lia|].
  apply Z_bounded_by_bits; [lia| apply Z.land_nonneg; lia |].
  intros k Hk. rewrite Z.land_spec.
  rewrite (Z_testbit_high 64 a k) by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma Z_lor_range : forall a b : Z, (0 <= a < 2^64)%Z -> (0 <= b < 2^64)%Z ->
  (0 <= Z.lor a b < 2^64)%Z.
Proof.
  intros a b Ha Hb. Local Ltac2 Set LiaHints.tbl := fun () => "0060=35497642355.735497643772.544204549936.556765665507.758230442238.758931717343.700000100200900=00A00ESSS2Ha2HbS2HaS2HkS2Hb".
split; [apply Z.lor_nonneg; lia|].
  apply Z_bounded_by_bits; [lia| apply Z.lor_nonneg; lia |].
  intros k Hk. rewrite Z.lor_spec.
  rewrite (Z_testbit_high 64 a k) by lia.
  rewrite (Z_testbit_high 64 b k) by lia.
  reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma Z_lxor_range : forall a b : Z, (0 <= a < 2^64)%Z -> (0 <= b < 2^64)%Z ->
  (0 <= Z.lxor a b < 2^64)%Z.
Proof.
  intros a b Ha Hb. Local Ltac2 Set LiaHints.tbl := fun () => "0060=28262574075.535497642355.735497643772.556765665507.758230442238.758931717343.700000700800900=00A00ES2Ha2HbSSS2HaS2HkS2Hb".
split; [apply Z.lxor_nonneg; lia|].
  apply Z_bounded_by_bits; [lia| apply Z.lxor_nonneg; lia |].
  intros k Hk. rewrite Z.lxor_spec.
  rewrite (Z_testbit_high 64 a k) by lia.
  rewrite (Z_testbit_high 64 b k) by lia.
  reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma Z_shiftr_range : forall a k : Z, (0 <= a < 2^64)%Z -> (0 <= k)%Z ->
  (0 <= Z.shiftr a k < 2^64)%Z.
Proof.
  intros a k Ha Hk. Local Ltac2 Set LiaHints.tbl := fun () => "0050=11321447016.626981515745.641415986323.551794599906.564252374674.600000400800900=00@S2HaS2HaSS2HkS1H".
rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk).
  split; [apply Z.div_pos; lia|].
  apply Z.le_lt_trans with a; [|lia].
  apply Z.div_le_upper_bound; nia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma bv_swrap_add_idemp_l : forall n x y,
  bv_swrap n (bv_wrap n x + y) = bv_swrap n (x + y).
Proof.
  intros n x y. unfold bv_swrap. f_equal.
  Local Ltac2 Set LiaHints.tbl := fun () => "0020=32175347472.450963383203.4000001002SS".
replace (bv_wrap n x + y + bv_half_modulus n)%Z
    with (bv_wrap n x + (y + bv_half_modulus n))%Z by lia.
  rewrite bv_wrap_add_idemp_l. f_equal. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma bv_swrap_add_idemp_r : forall n x y,
  bv_swrap n (x + bv_wrap n y) = bv_swrap n (x + y).
Proof.
  intros n x y. rewrite Z.add_comm, bv_swrap_add_idemp_l, Z.add_comm. reflexivity.
Qed.

#[using="Type"] Lemma bv_swrap_wrap' : forall n z, bv_swrap n (bv_wrap n z) = bv_swrap n z.
Proof. intros. apply bv_swrap_wrap. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zsig (x : word) : Z := bv_signed x.

Definition v_addi (x : word) (imm : Z) : word := Z_to_bv 64 (bv_unsigned x + imm).
Definition v_add (x y : word) : word := Z_to_bv 64 (bv_unsigned x + bv_unsigned y).
Definition v_sub (x y : word) : word := Z_to_bv 64 (bv_unsigned x - bv_unsigned y).
Definition v_mul (x y : word) : word := Z_to_bv 64 (bv_unsigned x * bv_unsigned y).
Definition v_andi (x : word) (imm : Z) : word := Z_to_bv 64 (Z.land (bv_unsigned x) (bv_wrap 64 imm)).
Definition v_ori (x : word) (imm : Z) : word := Z_to_bv 64 (Z.lor (bv_unsigned x) (bv_wrap 64 imm)).
Definition v_xori (x : word) (imm : Z) : word := Z_to_bv 64 (Z.lxor (bv_unsigned x) (bv_wrap 64 imm)).
Definition v_and (x y : word) : word := Z_to_bv 64 (Z.land (bv_unsigned x) (bv_unsigned y)).
Definition v_or (x y : word) : word := Z_to_bv 64 (Z.lor (bv_unsigned x) (bv_unsigned y)).
Definition v_xor (x y : word) : word := Z_to_bv 64 (Z.lxor (bv_unsigned x) (bv_unsigned y)).

Definition c_eq (x y : word) : bool := bv_eqb x y.
Definition c_lts (x y : word) : bool := bv_lts x y.
Definition c_ltu (x y : word) : bool := bv_ltu x y.

Definition btgt (pc : word) (imm : Z) : word := v_addi pc imm.

(* [comment removed for export] *)
Definition v_slti (x : word) (imm : Z) : word :=
  if (zsig x <? imm)%Z then Z_to_bv 64 1 else Z_to_bv 64 0.
Definition v_sltiu (x : word) (imm : Z) : word :=
  if (bv_unsigned x <? bv_wrap 64 imm)%Z then Z_to_bv 64 1 else Z_to_bv 64 0.
Definition v_slt (x y : word) : word := if c_lts x y then Z_to_bv 64 1 else Z_to_bv 64 0.
Definition v_sltu (x y : word) : word := if c_ltu x y then Z_to_bv 64 1 else Z_to_bv 64 0.

(* [comment removed for export] *)
Definition v_slli (x : word) (sh : Z) : word := Z_to_bv 64 (Z.shiftl (bv_unsigned x) sh).
Definition v_srli (x : word) (sh : Z) : word := Z_to_bv 64 (Z.shiftr (bv_unsigned x) sh).
Definition v_srai (x : word) (sh : Z) : word := Z_to_bv 64 (Z.shiftr (bv_signed x) sh).

(* [comment removed for export] *)
Definition v_sll (x y : word) : word :=
  Z_to_bv 64 (Z.shiftl (bv_unsigned x) (bv_unsigned y mod 64)).
Definition v_srl (x y : word) : word :=
  Z_to_bv 64 (Z.shiftr (bv_unsigned x) (bv_unsigned y mod 64)).
Definition v_sra (x y : word) : word :=
  Z_to_bv 64 (Z.shiftr (bv_signed x) (bv_unsigned y mod 64)).

(* [comment removed for export] *)
Definition v_lui (imm : Z) : word := Z_to_bv 64 imm.
Definition v_auipc (pc : word) (imm : Z) : word := Z_to_bv 64 (imm + bv_unsigned pc).

(* [comment removed for export] *)
Definition v_addiw (x : word) (imm : Z) : word :=
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned x + imm)).
Definition v_slliw (x : word) (sh : Z) : word :=
  Z_to_bv 64 (bv_swrap 32 (Z.shiftl (bv_unsigned x) sh)).
Definition v_srliw (x : word) (sh : Z) : word :=
  Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned x)) sh)).
Definition v_sraiw (x : word) (sh : Z) : word :=
  Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_swrap 32 (bv_unsigned x)) sh)).
Definition v_addw (x y : word) : word :=
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned x + bv_unsigned y)).
Definition v_subw (x y : word) : word :=
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned x - bv_unsigned y)).
Definition v_sllw (x y : word) : word :=
  Z_to_bv 64 (bv_swrap 32 (Z.shiftl (bv_unsigned x) (bv_unsigned y mod 32))).
Definition v_srlw (x y : word) : word :=
  Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned x)) (bv_unsigned y mod 32))).
Definition v_sraw (x y : word) : word :=
  Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_swrap 32 (bv_unsigned x)) (bv_unsigned y mod 32))).

(* [comment removed for export] *)
Definition v_mulh (x y : word) : word :=
  Z_to_bv 64 (Z.shiftr (bv_signed x * bv_signed y) 64).
Definition v_mulhsu (x y : word) : word :=
  Z_to_bv 64 (Z.shiftr (bv_signed x * bv_unsigned y) 64).
Definition v_mulhu (x y : word) : word :=
  Z_to_bv 64 (Z.shiftr (bv_unsigned x * bv_unsigned y) 64).
Definition v_mulw (x y : word) : word :=
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned x * bv_unsigned y)).

(* [comment removed for export] *)
Definition v_div (x y : word) : word :=
  if (bv_unsigned y =? 0)%Z then Z_to_bv 64 (-1)
  else Z_to_bv 64 (Z.quot (zsig x) (zsig y)).
Definition v_rem (x y : word) : word :=
  if (bv_unsigned y =? 0)%Z then x
  else Z_to_bv 64 (Z.rem (zsig x) (zsig y)).
Definition v_divw (x y : word) : word :=
  if (bv_wrap 32 (bv_unsigned y) =? 0)%Z then Z_to_bv 64 (-1)
  else Z_to_bv 64 (bv_swrap 32 (Z.quot (bv_swrap 32 (bv_unsigned x)) (bv_swrap 32 (bv_unsigned y)))).
Definition v_remw (x y : word) : word :=
  if (bv_wrap 32 (bv_unsigned y) =? 0)%Z then Z_to_bv 64 (bv_swrap 32 (bv_unsigned x))
  else Z_to_bv 64 (bv_swrap 32 (Z.rem (bv_swrap 32 (bv_unsigned x)) (bv_swrap 32 (bv_unsigned y)))).
Definition v_divuw (x y : word) : word :=
  if (bv_wrap 32 (bv_unsigned y) =? 0)%Z then Z_to_bv 64 (-1)
  else Z_to_bv 64 (bv_swrap 32 (bv_wrap 32 (bv_unsigned x) / bv_wrap 32 (bv_unsigned y))).
Definition v_remuw (x y : word) : word :=
  if (bv_wrap 32 (bv_unsigned y) =? 0)%Z then Z_to_bv 64 (bv_swrap 32 (bv_unsigned x))
  else Z_to_bv 64 (bv_swrap 32 (bv_wrap 32 (bv_unsigned x) mod bv_wrap 32 (bv_unsigned y))).

(* [comment removed for export] *)
Definition v_lb (b : byte) : word := Z_to_bv 64 (bv_signed b).
Definition v_lh (v : word) : word := Z_to_bv 64 (bv_swrap 16 (bv_unsigned v)).
Definition v_lw (v : word) : word := Z_to_bv 64 (bv_swrap 32 (bv_unsigned v)).

(* [comment removed for export] *)
Definition jalr_tgtZ (x : word) (imm : Z) : Z := Z.land (bv_unsigned x + imm) (-2).
Definition jalr_tgt (x : word) (imm : Z) : word := Z_to_bv 64 (jalr_tgtZ x imm).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition seg_rom (segs : list Segment) : word -> option byte :=
  fun addr => match memory_read segs addr 1 with Some (b :: _) => Some b | _ => None end.

Fixpoint rdn (segs : list Segment) (mem : word -> option byte) (a : word) (n : nat) : option (list byte) :=
  match n with
  | O => Some []
  | S n' =>
    match (match mem a with Some b => Some b | None => seg_rom segs a end) with
    | Some b => match rdn segs mem (a+1) n' with Some rest => Some (b :: rest) | None => None end
    | None => None
    end
  end.

(* [comment removed for export] *)
#[using="Type"] Lemma ov_rdn : forall segs (mem : word -> option byte) n a,
  ov_read_bytes segs mem a n = rdn segs mem a n.
Proof.
  intros segs mem n. induction n as [|n' IH]; intro a; [reflexivity|].
  simpl. unfold seg_rom.
  destruct (mem a) as [b|].
  - rewrite IH. reflexivity.
  - destruct (memory_read segs a 1) as [[|b rest]|]; [reflexivity| rewrite IH; reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma le_word_1 : forall b : byte, le_bytes_to_word [b] = Z_to_bv 64 (bv_unsigned b).
Proof.
  intro b. unfold le_bytes_to_word. cbn [bytes_le_to_Z].
  rewrite Z.shiftl_0_l, Z.lor_0_r. reflexivity.
Qed.

#[using="Type"] Lemma le_word_v : forall bs (v : word),
  bytes_le_to_Z bs = bv_unsigned v -> le_bytes_to_word bs = v.
Proof.
  intros bs v Hv. unfold le_bytes_to_word. rewrite Hv.
  apply Z_to_bv_bv_unsigned.
Qed.

#[using="Type"] Lemma b_extract8_id : forall b : byte, bv_extract 0 8 (Z_to_bv 64 (bv_unsigned b)) = b.
Proof.
  intro b. apply bv_eq.
  rewrite bv_extract_unsigned, Z_to_bv_unsigned, Z.shiftr_0_r.
  pose proof (bv_unsigned_in_range _ b) as Hb.
  change (bv_modulus 8) with 256%Z in Hb.
  Local Ltac2 Set LiaHints.tbl := fun () => "0020=21374812823.344409080154.3000004008S2HbS2Hb".
rewrite (bv_wrap_small 64) by (change (bv_modulus 64) with (2^64)%Z; lia).
  apply bv_wrap_small. change (bv_modulus 8) with 256%Z. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma b_lb_val : forall b : byte, sext 64 (bv_extract 0 8 (le_bytes_to_word [b])) = v_lb b.
Proof.
  intro b. rewrite le_word_1, b_extract8_id. apply bv_eq.
  unfold sext, v_lb. rewrite bv_sign_extend_unsigned, Z_to_bv_unsigned.
  reflexivity.
Qed.

#[using="Type"] Lemma b_lh_val : forall v : word, sext 64 (bv_extract 0 16 v) = v_lh v.
Proof.
  intro v. apply bv_eq. unfold sext, v_lh.
  rewrite bv_sign_extend_unsigned, Z_to_bv_unsigned.
  f_equal. unfold bv_signed.
  rewrite bv_extract_unsigned, Z.shiftr_0_r.
  apply bv_swrap_wrap.
Qed.

#[using="Type"] Lemma b_lw_val : forall v : word, sext 64 (bv_extract 0 32 v) = v_lw v.
Proof.
  intro v. apply bv_eq. unfold sext, v_lw.
  rewrite bv_sign_extend_unsigned, Z_to_bv_unsigned.
  f_equal. unfold bv_signed.
  rewrite bv_extract_unsigned, Z.shiftr_0_r.
  apply bv_swrap_wrap.
Qed.

#[using="Type"] Lemma rdn_length : forall segs mem n a bs,
  rdn segs mem a n = Some bs -> length bs = n.
Proof.
  intros segs mem n. induction n as [|n IH]; intros a bs H; cbn in H.
  - inversion H; reflexivity.
  - destruct (match mem a with Some b => Some b | None => seg_rom segs a end); [|discriminate].
    destruct (rdn segs mem (a+1) n) eqn:E; [|discriminate].
    inversion H; subst; cbn. f_equal. eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma bytes_le_to_Z_nonneg : forall bs, (0 <= bytes_le_to_Z bs)%Z.
Proof.
  Local Ltac2 Set LiaHints.tbl := fun () => "0020=15045616202.127841896117.5000001004SS1H".
induction bs as [|b bs IH]; cbn; [lia|].
  apply Z.lor_nonneg. split.
  - pose proof (bv_unsigned_in_range _ b). lia.
  - apply Z.shiftl_nonneg. exact IH.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma bytes_le_to_Z_bound : forall bs,
  (bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (length bs)))%Z.
Proof.
  Local Ltac2 Set LiaHints.tbl := fun () => "00;0=10821503339.815384171349.823021094264.627848182751.638651611658.84712172158.8 51794599906.860318695090.863368325619.868399279967.69563010060.1 00000900@00A00E00I00M00Q00U00Y00\00]S2IH1H2HkS2Hb2HkSS2HbS2HkS2HkS2HkS2HkS2HkS1HS".
induction bs as [|b bs IH]; cbn [bytes_le_to_Z length]; [cbn; lia|].
  pose proof (bytes_le_to_Z_nonneg bs).
  pose proof (bv_unsigned_in_range _ b) as Hb.
  change (bv_modulus 8) with 256%Z in Hb.
  apply Z_bounded_by_bits; [lia| |].
  { apply Z.lor_nonneg. split; [lia|]. apply Z.shiftl_nonneg. lia. }
  intros k Hk. rewrite Z.lor_spec.
  rewrite (Z_testbit_high 8 (bv_unsigned b) k) by lia.
  rewrite Z.shiftl_spec by lia.
  rewrite (Z_testbit_high (8 * Z.of_nat (length bs)) (bytes_le_to_Z bs) (k - 8)) by lia.
  reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma bytes_le_app : forall xs ys,
  bytes_le_to_Z (xs ++ ys) =
  Z.lor (bytes_le_to_Z xs) (Z.shiftl (bytes_le_to_Z ys) (8 * Z.of_nat (length xs))).
Proof.
  induction xs as [|x xs IH]; intro ys; cbn [bytes_le_to_Z app length].
  - rewrite Z.mul_0_r, Z.shiftl_0_r, Z.lor_0_l. reflexivity.
  - rewrite IH.
    Local Ltac2 Set LiaHints.tbl := fun () => "0020=2671875789.5 38652380690.5000001002SS".
rewrite Z.shiftl_lor, Z.shiftl_shiftl by lia.
    rewrite Z.lor_assoc. f_equal. f_equal. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma le2_spec : forall b1 b0, bv_unsigned (le2 b1 b0) = bytes_le_to_Z [b0; b1].
Proof.
  intros b1 b0. unfold le2.
  rewrite bv_concat_unsigned by reflexivity.
  cbn [bytes_le_to_Z].
  rewrite Z.shiftl_0_l, Z.lor_0_r. apply Z.lor_comm.
Qed.

#[using="Type"] Lemma le4_spec : forall b3 b2 b1 b0,
  bv_unsigned (le4 b3 b2 b1 b0) = bytes_le_to_Z [b0; b1; b2; b3].
Proof.
  intros b3 b2 b1 b0. unfold le4.
  rewrite bv_concat_unsigned by reflexivity.
  rewrite !le2_spec.
  change [b0; b1; b2; b3] with ([b0; b1] ++ [b2; b3]).
  rewrite bytes_le_app. cbn [length]. apply Z.lor_comm.
Qed.

#[using="Type"] Lemma le8_spec : forall b7 b6 b5 b4 b3 b2 b1 b0,
  bv_unsigned (le8 b7 b6 b5 b4 b3 b2 b1 b0) = bytes_le_to_Z [b0; b1; b2; b3; b4; b5; b6; b7].
Proof.
  intros. unfold le8.
  rewrite bv_concat_unsigned by reflexivity.
  rewrite !le4_spec.
  change [b0; b1; b2; b3; b4; b5; b6; b7] with ([b0; b1; b2; b3] ++ [b4; b5; b6; b7]).
  rewrite bytes_le_app. cbn [length]. apply Z.lor_comm.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma ok_mkst_eq : forall (r1 r2 : bvmap 5 word) (p1 p2 : word) (m1 m2 ro : word -> option byte),
  r1 = r2 -> p1 = p2 -> (forall a, m1 a = m2 a) ->
  MachineOk (mkst r1 p1 m1 ro) = MachineOk (mkst r2 p2 m2 ro).
Proof.
  intros r1 r2 p1 p2 m1 m2 ro Hr Hp Hm.
  assert (Em : m1 = m2) by (apply functional_extensionality; exact Hm).
  subst. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma u64_range : forall x : word, (0 <= bv_unsigned x < 2^64)%Z.
Proof. intro x. exact (bv_unsigned_in_range _ x). Qed.

#[using="Type"] Lemma u8_range : forall b : byte, (0 <= bv_unsigned b < 256)%Z.
Proof. intro b. exact (bv_unsigned_in_range _ b). Qed.

#[using="Type"] Lemma u6_range : forall s : bv 6, (0 <= bv_unsigned s < 64)%Z.
Proof. intro s. exact (bv_unsigned_in_range _ s). Qed.

#[using="Type"] Lemma u5_range : forall s : bv 5, (0 <= bv_unsigned s < 32)%Z.
Proof. intro s. exact (bv_unsigned_in_range _ s). Qed.

#[using="Type"] Lemma wrap64_range : forall z, (0 <= bv_wrap 64 z < 2^64)%Z.
Proof. intro z. exact (bv_wrap_in_range 64 z). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma bv_swrap_congr : forall n x y,
  bv_wrap n x = bv_wrap n y -> bv_swrap n x = bv_swrap n y.
Proof.
  intros n x y H. unfold bv_swrap. f_equal.
  rewrite <- (bv_wrap_add_idemp_l n x), H, bv_wrap_add_idemp_l. reflexivity.
Qed.

#[using="Type"] Lemma bv_swrap_add_swrap_l : forall n x y,
  bv_swrap n (bv_swrap n x + y) = bv_swrap n (x + y).
Proof.
  intros n x y. apply bv_swrap_congr.
  unfold bv_swrap.
  Local Ltac2 Set LiaHints.tbl := fun () => "0020=26497822128.455148356039.4000001002SS".
replace (bv_wrap n (x + bv_half_modulus n) - bv_half_modulus n + y)%Z
    with (bv_wrap n (x + bv_half_modulus n) + (y - bv_half_modulus n))%Z by lia.
  rewrite bv_wrap_add_idemp_l.
  f_equal. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma bv_swrap_add_swrap_r : forall n x y,
  bv_swrap n (x + bv_swrap n y) = bv_swrap n (x + y).
Proof.
  intros n x y. rewrite Z.add_comm, bv_swrap_add_swrap_l, Z.add_comm. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma b_addsext : forall (a : word) {n} (imm : bv n),
  a + sext 64 imm = v_addi a (bv_signed imm).
Proof.
  intros. apply bv_eq. unfold v_addi, sext.
  rewrite bv_add_unsigned, bv_sign_extend_unsigned, Z_to_bv_unsigned.
  apply bv_wrap_add_idemp_r.
Qed.

#[using="Type"] Lemma b_npc4 : forall p : word, p + Z_to_bv 64 4 = v_addi p 4.
Proof.
  intros. apply bv_eq. unfold v_addi.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  apply bv_wrap_add_idemp_r.
Qed.

#[using="Type"] Lemma alu_addi : forall (a : word) {n} (imm : bv n),
  alu64 ALU_ADD a (sext 64 imm) = v_addi a (bv_signed imm).
Proof. intros. apply b_addsext. Qed.

#[using="Type"] Lemma alu_andi : forall (a : word) {n} (imm : bv n),
  alu64 ALU_AND a (sext 64 imm) = v_andi a (bv_signed imm).
Proof.
  intros. apply bv_eq. unfold v_andi.
  change (alu64 ALU_AND a (sext 64 imm)) with (bv_and a (sext 64 imm)).
  rewrite bv_and_unsigned. unfold sext. rewrite bv_sign_extend_unsigned.
  rewrite Z_to_bv_unsigned.
  symmetry; apply bv_wrap_small.
  apply Z_land_range; [apply u64_range | apply wrap64_range].
Qed.

#[using="Type"] Lemma alu_ori : forall (a : word) {n} (imm : bv n),
  alu64 ALU_OR a (sext 64 imm) = v_ori a (bv_signed imm).
Proof.
  intros. apply bv_eq. unfold v_ori.
  change (alu64 ALU_OR a (sext 64 imm)) with (bv_or a (sext 64 imm)).
  rewrite bv_or_unsigned. unfold sext. rewrite bv_sign_extend_unsigned.
  rewrite Z_to_bv_unsigned.
  symmetry; apply bv_wrap_small.
  apply Z_lor_range; [apply u64_range | apply wrap64_range].
Qed.

#[using="Type"] Lemma alu_xori : forall (a : word) {n} (imm : bv n),
  alu64 ALU_XOR a (sext 64 imm) = v_xori a (bv_signed imm).
Proof.
  intros. apply bv_eq. unfold v_xori.
  change (alu64 ALU_XOR a (sext 64 imm)) with (bv_xor a (sext 64 imm)).
  rewrite bv_xor_unsigned. unfold sext. rewrite bv_sign_extend_unsigned.
  rewrite Z_to_bv_unsigned.
  symmetry; apply bv_wrap_small.
  apply Z_lxor_range; [apply u64_range | apply wrap64_range].
Qed.

#[using="Type"] Lemma alu_slti : forall (a : word) (imm : bv 12),
  alu64 ALU_SLT a (sext 64 imm) = v_slti a (bv_signed imm).
Proof.
  intros. unfold v_slti, zsig.
  change (alu64 ALU_SLT a (sext 64 imm))
    with (if bv_lts a (sext 64 imm) then Z_to_bv 64 1 else Z_to_bv 64 0).
  unfold bv_lts, sext.
  Local Ltac2 Set LiaHints.tbl := fun () => "0010=54439458487.3000001S".
rewrite bv_sign_extend_signed by lia.
  reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma alu_sltiu : forall (a : word) {n} (imm : bv n),
  alu64 ALU_SLTU a (sext 64 imm) = v_sltiu a (bv_signed imm).
Proof.
  intros. unfold v_sltiu.
  change (alu64 ALU_SLTU a (sext 64 imm))
    with (if bv_ltu a (sext 64 imm) then Z_to_bv 64 1 else Z_to_bv 64 0).
  unfold bv_ltu, sext.
  rewrite bv_sign_extend_unsigned.
  reflexivity.
Qed.

#[using="Type"] Lemma alu_add : forall a b : word, alu64 ALU_ADD a b = v_add a b.
Proof. reflexivity. Qed.

#[using="Type"] Lemma alu_sub : forall a b : word, alu64 ALU_SUB a b = v_sub a b.
Proof. reflexivity. Qed.

#[using="Type"] Lemma alu_slt : forall a b : word, alu64 ALU_SLT a b = v_slt a b.
Proof. reflexivity. Qed.

#[using="Type"] Lemma alu_sltu : forall a b : word, alu64 ALU_SLTU a b = v_sltu a b.
Proof. reflexivity. Qed.

#[using="Type"] Lemma alu_and : forall a b : word, alu64 ALU_AND a b = v_and a b.
Proof.
  intros. apply bv_eq. unfold v_and.
  change (alu64 ALU_AND a b) with (bv_and a b).
  rewrite bv_and_unsigned, Z_to_bv_unsigned.
  symmetry; apply bv_wrap_small.
  apply Z_land_range; [apply u64_range | apply u64_range].
Qed.

#[using="Type"] Lemma alu_or : forall a b : word, alu64 ALU_OR a b = v_or a b.
Proof.
  intros. apply bv_eq. unfold v_or.
  change (alu64 ALU_OR a b) with (bv_or a b).
  rewrite bv_or_unsigned, Z_to_bv_unsigned.
  symmetry; apply bv_wrap_small.
  apply Z_lor_range; apply u64_range.
Qed.

#[using="Type"] Lemma alu_xor : forall a b : word, alu64 ALU_XOR a b = v_xor a b.
Proof.
  intros. apply bv_eq. unfold v_xor.
  change (alu64 ALU_XOR a b) with (bv_xor a b).
  rewrite bv_xor_unsigned, Z_to_bv_unsigned.
  symmetry; apply bv_wrap_small.
  apply Z_lxor_range; apply u64_range.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma shamt6_mask : forall s : bv 6,
  bv_unsigned (bv_and (zext 64 s) (Z_to_bv 64 63)) = bv_unsigned s.
Proof.
  intro s. rewrite bv_and_unsigned. unfold zext.
  Local Ltac2 Set LiaHints.tbl := fun () => "0030=21656728183.254435691437.263968618315.2000001002003SSS".
rewrite bv_zero_extend_unsigned by lia.
  rewrite Z_to_bv_small by (change (bv_modulus 64) with (2^64)%Z; lia).
  change 63%Z with (Z.ones 6).
  rewrite Z.land_ones by lia.
  apply Z.mod_small. change (2^6)%Z with 64%Z. apply u6_range.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma regamt64_mask : forall b : word,
  bv_unsigned (bv_and b (Z_to_bv 64 63)) = (bv_unsigned b mod 64)%Z.
Proof.
  intro b. rewrite bv_and_unsigned.
  Local Ltac2 Set LiaHints.tbl := fun () => "0020=21656451552.263968898268.2000001002SS".
rewrite Z_to_bv_small by (change (bv_modulus 64) with (2^64)%Z; lia).
  change 63%Z with (Z.ones 6).
  rewrite Z.land_ones by lia.
  reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma alu_slli : forall (a : word) (s : bv 6),
  alu64 ALU_SLL a (zext 64 s) = v_slli a (bv_unsigned s).
Proof.
  intros. apply bv_eq. unfold v_slli.
  change (alu64 ALU_SLL a (zext 64 s)) with (a ≪ bv_and (zext 64 s) (Z_to_bv 64 63)).
  rewrite bv_shiftl_unsigned, Z_to_bv_unsigned, shamt6_mask.
  reflexivity.
Qed.

#[using="Type"] Lemma alu_srli : forall (a : word) (s : bv 6),
  alu64 ALU_SRL a (zext 64 s) = v_srli a (bv_unsigned s).
Proof.
  intros. apply bv_eq. unfold v_srli.
  change (alu64 ALU_SRL a (zext 64 s)) with (a ≫ bv_and (zext 64 s) (Z_to_bv 64 63)).
  rewrite bv_shiftr_unsigned, Z_to_bv_unsigned, shamt6_mask.
  symmetry; apply bv_wrap_small.
  apply Z_shiftr_range; [apply u64_range | apply u6_range].
Qed.

#[using="Type"] Lemma alu_srai : forall (a : word) (s : bv 6),
  alu64 ALU_SRA a (zext 64 s) = v_srai a (bv_unsigned s).
Proof.
  intros. apply bv_eq. unfold v_srai.
  change (alu64 ALU_SRA a (zext 64 s))
    with (bv_ashiftr a (bv_and (zext 64 s) (Z_to_bv 64 63))).
  rewrite bv_ashiftr_unsigned, Z_to_bv_unsigned, shamt6_mask.
  reflexivity.
Qed.

#[using="Type"] Lemma alu_sll : forall a b : word, alu64 ALU_SLL a b = v_sll a b.
Proof.
  intros. apply bv_eq. unfold v_sll.
  change (alu64 ALU_SLL a b) with (a ≪ bv_and b (Z_to_bv 64 63)).
  rewrite bv_shiftl_unsigned, Z_to_bv_unsigned, regamt64_mask.
  reflexivity.
Qed.

#[using="Type"] Lemma alu_srl : forall a b : word, alu64 ALU_SRL a b = v_srl a b.
Proof.
  intros. apply bv_eq. unfold v_srl.
  change (alu64 ALU_SRL a b) with (a ≫ bv_and b (Z_to_bv 64 63)).
  rewrite bv_shiftr_unsigned, Z_to_bv_unsigned, regamt64_mask.
  symmetry; apply bv_wrap_small.
  apply Z_shiftr_range; [apply u64_range |].
  Local Ltac2 Set LiaHints.tbl := fun () => "0020=35495972604.356736467285.4000001004SS1H".
pose proof (Z.mod_pos_bound (bv_unsigned b) 64 ltac:(lia)). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma alu_sra : forall a b : word, alu64 ALU_SRA a b = v_sra a b.
Proof.
  intros. apply bv_eq. unfold v_sra.
  change (alu64 ALU_SRA a b) with (bv_ashiftr a (bv_and b (Z_to_bv 64 63))).
  rewrite bv_ashiftr_unsigned, Z_to_bv_unsigned, regamt64_mask.
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma low32_unsigned : forall a : word,
  bv_unsigned (low32 a) = bv_wrap 32 (bv_unsigned a).
Proof.
  intro a. unfold low32. rewrite bv_extract_unsigned.
  change (Z.of_N 0) with 0%Z. rewrite Z.shiftr_0_r. reflexivity.
Qed.

#[using="Type"] Lemma low32_signed : forall a : word,
  bv_signed (low32 a) = bv_swrap 32 (bv_unsigned a).
Proof.
  intro a. unfold low32. rewrite bv_extract_signed.
  change (Z.of_N 0) with 0%Z. rewrite Z.shiftr_0_r. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma shamt5_mask : forall s : bv 5,
  bv_unsigned (bv_and (zext 32 s) (Z_to_bv 32 31)) = bv_unsigned s.
Proof.
  intro s. rewrite bv_and_unsigned. unfold zext.
  Local Ltac2 Set LiaHints.tbl := fun () => "0030=29311394875.242077958263.254435691437.2000001002003SSS".
rewrite bv_zero_extend_unsigned by lia.
  rewrite Z_to_bv_small by (change (bv_modulus 32) with (2^32)%Z; lia).
  change 31%Z with (Z.ones 5).
  rewrite Z.land_ones by lia.
  apply Z.mod_small. change (2^5)%Z with 32%Z. apply u5_range.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma regamt32_mask : forall b : word,
  bv_unsigned (bv_and (low32 b) (Z_to_bv 32 31)) = (bv_unsigned b mod 32)%Z.
Proof.
  intro b. rewrite bv_and_unsigned, low32_unsigned.
  Local Ltac2 Set LiaHints.tbl := fun () => "0040=29311643564.242044206763.242078239712.242464732859.2000001002003004SSSS".
rewrite Z_to_bv_small by (change (bv_modulus 32) with (2^32)%Z; lia).
  change 31%Z with (Z.ones 5).
  rewrite Z.land_ones by lia.
  rewrite bv_wrap32_mod.
  symmetry. apply Znumtheory.Zmod_div_mod; [lia|lia|].
  exists (2^27)%Z. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma sext32_unsigned : forall v : bv 32,
  bv_unsigned (sext 64 v) = bv_wrap 64 (bv_swrap 32 (bv_unsigned v)).
Proof.
  intro v. unfold sext. rewrite bv_sign_extend_unsigned. reflexivity.
Qed.

#[using="Type"] Lemma w_addiw : forall (a : word) (imm : bv 12),
  sext 64 (alu32 ALU_ADD (low32 a) (sext 32 imm)) = v_addiw a (bv_signed imm).
Proof.
  intros. apply bv_eq. unfold v_addiw.
  rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
  change (alu32 ALU_ADD (low32 a) (sext 32 imm)) with (low32 a + sext 32 imm).
  rewrite bv_add_unsigned, low32_unsigned.
  unfold sext. rewrite bv_sign_extend_unsigned.
  rewrite bv_swrap_wrap', bv_swrap_add_idemp_l, bv_swrap_add_idemp_r.
  reflexivity.
Qed.

#[using="Type"] Lemma w_slliw : forall (a : word) (s : bv 5),
  sext 64 (alu32 ALU_SLL (low32 a) (zext 32 s)) = v_slliw a (bv_unsigned s).
Proof.
  intros. apply bv_eq. unfold v_slliw.
  rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
  change (alu32 ALU_SLL (low32 a) (zext 32 s))
    with (low32 a ≪ bv_and (zext 32 s) (Z_to_bv 32 31)).
  rewrite bv_shiftl_unsigned, shamt5_mask, low32_unsigned.
  rewrite bv_swrap_wrap'.
  apply bv_swrap_congr.
  rewrite !Z.shiftl_mul_pow2 by apply u5_range.
  rewrite !bv_wrap32_mod.
  apply Z.mul_mod_idemp_l. Local Ltac2 Set LiaHints.tbl := fun () => "0010=38718487946.3000001S".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma w_srliw : forall (a : word) (s : bv 5),
  sext 64 (alu32 ALU_SRL (low32 a) (zext 32 s)) = v_srliw a (bv_unsigned s).
Proof.
  intros. apply bv_eq. unfold v_srliw.
  rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
  change (alu32 ALU_SRL (low32 a) (zext 32 s))
    with (low32 a ≫ bv_and (zext 32 s) (Z_to_bv 32 31)).
  rewrite bv_shiftr_unsigned, shamt5_mask, low32_unsigned.
  reflexivity.
Qed.

#[using="Type"] Lemma w_sraiw : forall (a : word) (s : bv 5),
  sext 64 (alu32 ALU_SRA (low32 a) (zext 32 s)) = v_sraiw a (bv_unsigned s).
Proof.
  intros. apply bv_eq. unfold v_sraiw.
  rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
  change (alu32 ALU_SRA (low32 a) (zext 32 s))
    with (bv_ashiftr (low32 a) (bv_and (zext 32 s) (Z_to_bv 32 31))).
  rewrite bv_ashiftr_unsigned, shamt5_mask, low32_signed.
  rewrite bv_swrap_wrap'. reflexivity.
Qed.

#[using="Type"] Lemma w_addw : forall a b : word,
  sext 64 (alu32 ALU_ADD (low32 a) (low32 b)) = v_addw a b.
Proof.
  intros. apply bv_eq. unfold v_addw.
  rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
  change (alu32 ALU_ADD (low32 a) (low32 b)) with (low32 a + low32 b).
  rewrite bv_add_unsigned, !low32_unsigned.
  rewrite bv_swrap_wrap', bv_swrap_add_idemp_l, bv_swrap_add_idemp_r.
  reflexivity.
Qed.

#[using="Type"] Lemma w_subw : forall a b : word,
  sext 64 (alu32 ALU_SUB (low32 a) (low32 b)) = v_subw a b.
Proof.
  intros. apply bv_eq. unfold v_subw.
  rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
  change (alu32 ALU_SUB (low32 a) (low32 b)) with (low32 a - low32 b).
  rewrite bv_sub_unsigned, !low32_unsigned.
  rewrite bv_swrap_wrap'.
  apply bv_swrap_congr.
  rewrite !bv_wrap32_mod.
  rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r.
  reflexivity.
Qed.

#[using="Type"] Lemma w_sllw : forall a b : word,
  sext 64 (alu32 ALU_SLL (low32 a) (low32 b)) = v_sllw a b.
Proof.
  intros. apply bv_eq. unfold v_sllw.
  rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
  change (alu32 ALU_SLL (low32 a) (low32 b))
    with (low32 a ≪ bv_and (low32 b) (Z_to_bv 32 31)).
  rewrite bv_shiftl_unsigned, regamt32_mask, low32_unsigned.
  rewrite bv_swrap_wrap'.
  apply bv_swrap_congr.
  Local Ltac2 Set LiaHints.tbl := fun () => "0030=38717875063.444021889276.360254530389.4000001002005SSS1H".
pose proof (Z.mod_pos_bound (bv_unsigned b) 32 ltac:(lia)).
  rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite !bv_wrap32_mod.
  apply Z.mul_mod_idemp_l. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma w_srlw : forall a b : word,
  sext 64 (alu32 ALU_SRL (low32 a) (low32 b)) = v_srlw a b.
Proof.
  intros. apply bv_eq. unfold v_srlw.
  rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
  change (alu32 ALU_SRL (low32 a) (low32 b))
    with (low32 a ≫ bv_and (low32 b) (Z_to_bv 32 31)).
  rewrite bv_shiftr_unsigned, regamt32_mask, low32_unsigned.
  reflexivity.
Qed.

#[using="Type"] Lemma w_sraw : forall a b : word,
  sext 64 (alu32 ALU_SRA (low32 a) (low32 b)) = v_sraw a b.
Proof.
  intros. apply bv_eq. unfold v_sraw.
  rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
  change (alu32 ALU_SRA (low32 a) (low32 b))
    with (bv_ashiftr (low32 a) (bv_and (low32 b) (Z_to_bv 32 31))).
  rewrite bv_ashiftr_unsigned, regamt32_mask, low32_signed.
  rewrite bv_swrap_wrap'. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma m_mul : forall a b : word, mul_div M_MUL a b = v_mul a b.
Proof. reflexivity. Qed.

#[using="Type"] Lemma m_mulh : forall a b : word, mul_div M_MULH a b = v_mulh a b.
Proof. reflexivity. Qed.

#[using="Type"] Lemma m_mulhsu : forall a b : word, mul_div M_MULHSU a b = v_mulhsu a b.
Proof. reflexivity. Qed.

#[using="Type"] Lemma m_mulhu : forall a b : word, mul_div M_MULHU a b = v_mulhu a b.
Proof. reflexivity. Qed.

#[using="Type"] Lemma m_div : forall a b : word, mul_div M_DIV a b = v_div a b.
Proof. reflexivity. Qed.

#[using="Type"] Lemma m_rem : forall a b : word, mul_div M_REM a b = v_rem a b.
Proof. reflexivity. Qed.

#[using="Type"] Lemma w_mulw : forall a b : word,
  sext 64 (mul_div M_MUL (low32 a) (low32 b)) = v_mulw a b.
Proof.
  intros. apply bv_eq. unfold v_mulw.
  rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
  change (mul_div M_MUL (low32 a) (low32 b)) with (low32 a * low32 b).
  rewrite bv_mul_unsigned, !low32_unsigned.
  rewrite bv_swrap_wrap'.
  apply bv_swrap_congr.
  rewrite !bv_wrap32_mod.
  rewrite Z.mul_mod_idemp_l, Z.mul_mod_idemp_r by lia.
  reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma div0_32 : forall b : word,
  (bv_unsigned (low32 b) =? 0)%Z = (bv_wrap 32 (bv_unsigned b) =? 0)%Z.
Proof. intro b. rewrite low32_unsigned. reflexivity. Qed.

#[using="Type"] Lemma w_divw : forall a b : word,
  sext 64 (mul_div M_DIV (low32 a) (low32 b)) = v_divw a b.
Proof.
  intros. unfold mul_div, v_divw.
  rewrite div0_32.
  destruct (bv_wrap 32 (bv_unsigned b) =? 0)%Z.
  - apply bv_eq. reflexivity.
  - apply bv_eq. rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
    rewrite bv_quots_unsigned, bv_swrap_wrap', !low32_signed.
    reflexivity.
Qed.

#[using="Type"] Lemma w_remw : forall a b : word,
  sext 64 (mul_div M_REM (low32 a) (low32 b)) = v_remw a b.
Proof.
  intros. unfold mul_div, v_remw.
  rewrite div0_32.
  destruct (bv_wrap 32 (bv_unsigned b) =? 0)%Z.
  - apply bv_eq. rewrite sext32_unsigned, Z_to_bv_unsigned, low32_unsigned.
    rewrite bv_swrap_wrap'. reflexivity.
  - apply bv_eq. rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
    rewrite bv_rems_unsigned, bv_swrap_wrap', !low32_signed.
    reflexivity.
Qed.

#[using="Type"] Lemma w_divuw : forall a b : word,
  sext 64 (mul_div M_DIVU (low32 a) (low32 b)) = v_divuw a b.
Proof.
  intros. unfold mul_div, v_divuw.
  rewrite div0_32.
  destruct (bv_wrap 32 (bv_unsigned b) =? 0)%Z.
  - apply bv_eq. reflexivity.
  - apply bv_eq. rewrite sext32_unsigned, Z_to_bv_unsigned.
    f_equal; rewrite ?bv_divu_unsigned, ?low32_unsigned; reflexivity.
Qed.

#[using="Type"] Lemma w_remuw : forall a b : word,
  sext 64 (mul_div M_REMU (low32 a) (low32 b)) = v_remuw a b.
Proof.
  intros. unfold mul_div, v_remuw.
  rewrite div0_32.
  destruct (bv_wrap 32 (bv_unsigned b) =? 0)%Z.
  - apply bv_eq. rewrite sext32_unsigned, Z_to_bv_unsigned, low32_unsigned.
    rewrite bv_swrap_wrap'. reflexivity.
  - apply bv_eq. rewrite sext32_unsigned, Z_to_bv_unsigned.
    f_equal; rewrite ?bv_modu_unsigned, ?low32_unsigned; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma bv_swrap_hi : forall n z, n <> 0%N ->
  (bv_half_modulus n <= z)%Z -> (z < bv_modulus n)%Z ->
  bv_swrap n z = (z - bv_modulus n)%Z.
Proof.
  intros n z Hn Hlo Hhi. unfold bv_swrap, bv_wrap.
  pose proof (bv_half_modulus_twice n Hn) as Htw.
  pose proof (bv_modulus_pos n) as Hpos.
  Local Ltac2 Set LiaHints.tbl := fun () => "0030=24976235314.832578738057.84940663228.8 00000100200DSSS3Hlo3Hhi3Htw4Hpos".
replace (z + bv_half_modulus n)%Z
    with ((z + bv_half_modulus n - bv_modulus n) + 1 * bv_modulus n)%Z by lia.
  rewrite Z_mod_plus_full.
  rewrite Z.mod_small by lia.
  lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma b_lui : forall imm : bv 20,
  sext 64 (bv_concat 32 imm (Z_to_bv 12 0)) = v_lui (Z.shiftl (bv_signed imm) 12).
Proof.
  intros imm. apply bv_eq. unfold v_lui.
  rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
  rewrite bv_concat_unsigned by reflexivity.
  Local Ltac2 Set LiaHints.tbl := fun () => "00:0=17210505260.323000396487.432816205960.433669193954.341187194487.44258558384.4 50782857205.4526368104.4  53410339469.254729297018.400000100600>00?00C00H00I00Q00R00VSS3HgeS2Hr3HltSS2HrS3HgeSS2Hr3HltSS2Hr".
rewrite (Z_to_bv_small 12 0) by (change (bv_modulus 12) with (2^12)%Z; lia).
  rewrite Z.lor_0_r.
  unfold bv_signed.
  pose proof (bv_unsigned_in_range _ imm) as Hr.
  change (bv_modulus 20) with (2^20)%Z in Hr.
  rewrite !Z.shiftl_mul_pow2 by lia.
  change (Z.of_N 12) with 12%Z.
  destruct (Z.lt_ge_cases (bv_unsigned imm) (2^19)) as [Hlt|Hge].
  - rewrite (bv_swrap_small 32)
      by (change (bv_half_modulus 32) with (2^31)%Z; lia).
    rewrite (bv_swrap_small 20)
      by (change (bv_half_modulus 20) with (2^19)%Z; lia).
    reflexivity.
  - rewrite (bv_swrap_hi 32)
      by first [discriminate
               |change (bv_half_modulus 32) with (2^31)%Z;
                change (bv_modulus 32) with (2^32)%Z; lia].
    rewrite (bv_swrap_hi 20)
      by first [discriminate
               |change (bv_half_modulus 20) with (2^19)%Z;
                change (bv_modulus 20) with (2^20)%Z; lia].
    change (bv_modulus 32) with (2^32)%Z.
    change (bv_modulus 20) with (2^20)%Z.
    lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma b_auipc : forall (p : word) (imm : bv 20),
  p + sext 64 (bv_concat 32 imm (Z_to_bv 12 0)) = v_auipc p (Z.shiftl (bv_signed imm) 12).
Proof.
  intros. rewrite b_lui. apply bv_eq. unfold v_lui, v_auipc.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  rewrite bv_wrap_add_idemp_r. f_equal. Local Ltac2 Set LiaHints.tbl := fun () => "0010=61223505919.3000001S".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma Z_land_m2_wrap : forall z,
  Z.land (bv_wrap 64 z) (bv_wrap 64 (-2)) = bv_wrap 64 (Z.land z (-2)).
Proof.
  intro z. rewrite !bv_wrap64_mod.
  apply Z.bits_inj'. intros k Hk.
  rewrite Z.land_spec.
  destruct (Z.lt_ge_cases k 64) as [Hlt|Hge].
  - rewrite !Z.mod_pow2_bits_low by lia.
    rewrite Z.land_spec. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia.
    apply andb_false_r.
Qed.

#[using="Type"] Lemma b_jalr : forall (a : word) (imm : bv 12),
  bv_and (a + sext 64 imm) (bv_not (Z_to_bv 64 1)) = jalr_tgt a (bv_signed imm).
Proof.
  intros. rewrite b_addsext. apply bv_eq.
  unfold jalr_tgt, jalr_tgtZ, v_addi.
  rewrite bv_and_unsigned, bv_not_unsigned, !Z_to_bv_unsigned.
  change (bv_wrap 64 1) with 1%Z.
  change (Z.lnot 1) with (-2)%Z.
  apply Z_land_m2_wrap.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End WithFP1.

Ltac step_pipeline Hfetch Hecall Hdecode :=
  unfold RiscvSemantics.step, RiscvSemantics.step_accesses;
  cbn [ms_pc ms_pc_val mkst];
  rewrite Hfetch;
  cbv beta iota;
  unfold RiscvSemantics.drop_access_report,
    RiscvSemantics.decode_exec_accesses;
  rewrite Hecall;
  cbv beta iota;
  rewrite Hdecode;
  cbv beta iota zeta delta
    [RiscvSemantics.interp_eff_accesses
     RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
     Sem.exec Sem.load_val Sem.store_val
     Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv
     Sem.inval_resv Sem.w0 Sem.w1
     Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
     ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom mkst];
  rewrite ?bv_eqb0_is_x0.

Section WithFP2.
Context {fx : FPState}.

(* [comment removed for export] *)
#[using="Type"] Lemma step_opimm_gen : forall segs regs pc mem rom w op rd rs (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm op rd rs imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs
                   else regupd regs rd (alu64 op (getr regs rs) (sext 64 imm)))
                  (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w op rd rs imm Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

#[using="Type"] Lemma step_shiftimm_gen : forall segs regs pc mem rom w op rd rs (sh : bv 6),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm op rd rs sh, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs
                   else regupd regs rd (alu64 op (getr regs rs) (zext 64 sh)))
                  (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w op rd rs sh Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

#[using="Type"] Lemma step_op_gen : forall segs regs pc mem rom w op rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs
                   else regupd regs rd (alu64 op (getr regs rs1) (getr regs rs2)))
                  (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w op rd rs1 rs2 Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

#[using="Type"] Lemma step_opimm32_gen : forall segs regs pc mem rom w rd rs (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm32 rd rs imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs
                   else regupd regs rd (sext 64 (alu32 ALU_ADD (low32 (getr regs rs)) (sext 32 imm))))
                  (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

#[using="Type"] Lemma step_shiftimm32_gen : forall segs regs pc mem rom w op rd rs (sh : bv 5),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm32 op rd rs sh, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs
                   else regupd regs rd (sext 64 (alu32 op (low32 (getr regs rs)) (zext 32 sh))))
                  (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w op rd rs sh Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

#[using="Type"] Lemma step_op32_gen : forall segs regs pc mem rom w op rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op32 op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs
                   else regupd regs rd (sext 64 (alu32 op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
                  (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w op rd rs1 rs2 Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

#[using="Type"] Lemma step_mul_gen : forall segs regs pc mem rom w op rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs
                   else regupd regs rd (mul_div op (getr regs rs1) (getr regs rs2)))
                  (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w op rd rs1 rs2 Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

#[using="Type"] Lemma step_mul32_gen : forall segs regs pc mem rom w op rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul32 op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs
                   else regupd regs rd (sext 64 (mul_div op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
                  (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w op rd rs1 rs2 Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma step_branch_tk_gen : forall segs regs pc mem rom w c rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
  branch_taken c (getr regs rs1) (getr regs rs2) = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (btgt pc (bv_signed imm)) mem rom).
Proof.
  intros segs regs pc mem rom w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
  destruct (is_x0 rs1); destruct (is_x0 rs2);
    cbv beta iota; rewrite Hc; cbv beta iota;
    rewrite b_addsext; reflexivity.
Qed.

#[using="Type"] Lemma step_branch_ft_gen : forall segs regs pc mem rom w c rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
  branch_taken c (getr regs rs1) (getr regs rs2) = false ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
  destruct (is_x0 rs1); destruct (is_x0 rs2);
    cbv beta iota; rewrite Hc; cbv beta iota;
    rewrite b_npc4; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma step_addi : forall segs regs pc mem rom w rd rs (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm ALU_ADD rd rs imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi (getr regs rs) (bv_signed imm))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_opimm_gen by eassumption.
  rewrite alu_addi. reflexivity.
Qed.

#[using="Type"] Lemma step_andi : forall segs regs pc mem rom w rd rs (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm ALU_AND rd rs imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_andi (getr regs rs) (bv_signed imm))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_opimm_gen by eassumption.
  rewrite alu_andi. reflexivity.
Qed.

#[using="Type"] Lemma step_ori : forall segs regs pc mem rom w rd rs (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm ALU_OR rd rs imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_ori (getr regs rs) (bv_signed imm))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_opimm_gen by eassumption.
  rewrite alu_ori. reflexivity.
Qed.

#[using="Type"] Lemma step_xori : forall segs regs pc mem rom w rd rs (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm ALU_XOR rd rs imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_xori (getr regs rs) (bv_signed imm))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_opimm_gen by eassumption.
  rewrite alu_xori. reflexivity.
Qed.

#[using="Type"] Lemma step_sltiu : forall segs regs pc mem rom w rd rs (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm ALU_SLTU rd rs imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_sltiu (getr regs rs) (bv_signed imm))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_opimm_gen by eassumption.
  rewrite alu_sltiu. reflexivity.
Qed.

#[using="Type"] Lemma step_slti : forall segs regs pc mem rom w rd rs (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm ALU_SLT rd rs imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_slti (getr regs rs) (bv_signed imm))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_opimm_gen by eassumption.
  rewrite alu_slti. reflexivity.
Qed.

#[using="Type"] Lemma step_slli : forall segs regs pc mem rom w rd rs (sh : bv 6),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm ALU_SLL rd rs sh, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_slli (getr regs rs) (bv_unsigned sh))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_shiftimm_gen by eassumption.
  rewrite alu_slli. reflexivity.
Qed.

#[using="Type"] Lemma step_srli : forall segs regs pc mem rom w rd rs (sh : bv 6),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm ALU_SRL rd rs sh, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_srli (getr regs rs) (bv_unsigned sh))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_shiftimm_gen by eassumption.
  rewrite alu_srli. reflexivity.
Qed.

#[using="Type"] Lemma step_srai : forall segs regs pc mem rom w rd rs (sh : bv 6),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm ALU_SRA rd rs sh, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_srai (getr regs rs) (bv_unsigned sh))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_shiftimm_gen by eassumption.
  rewrite alu_srai. reflexivity.
Qed.

#[using="Type"] Lemma step_add : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_ADD rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_add (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_op_gen by eassumption.
  rewrite alu_add. reflexivity.
Qed.

#[using="Type"] Lemma step_sub : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_SUB rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_sub (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_op_gen by eassumption.
  rewrite alu_sub. reflexivity.
Qed.

#[using="Type"] Lemma step_slt : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_SLT rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_slt (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_op_gen by eassumption.
  rewrite alu_slt. reflexivity.
Qed.

#[using="Type"] Lemma step_sltu : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_SLTU rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_sltu (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_op_gen by eassumption.
  rewrite alu_sltu. reflexivity.
Qed.

#[using="Type"] Lemma step_and : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_AND rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_and (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_op_gen by eassumption.
  rewrite alu_and. reflexivity.
Qed.

#[using="Type"] Lemma step_or : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_OR rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_or (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_op_gen by eassumption.
  rewrite alu_or. reflexivity.
Qed.

#[using="Type"] Lemma step_xor : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_XOR rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_xor (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_op_gen by eassumption.
  rewrite alu_xor. reflexivity.
Qed.

#[using="Type"] Lemma step_sll : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_SLL rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_sll (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_op_gen by eassumption.
  rewrite alu_sll. reflexivity.
Qed.

#[using="Type"] Lemma step_srl : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_SRL rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_srl (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_op_gen by eassumption.
  rewrite alu_srl. reflexivity.
Qed.

#[using="Type"] Lemma step_sra : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_SRA rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_sra (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_op_gen by eassumption.
  rewrite alu_sra. reflexivity.
Qed.

#[using="Type"] Lemma step_addiw : forall segs regs pc mem rom w rd rs (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm32 rd rs imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addiw (getr regs rs) (bv_signed imm))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_opimm32_gen by eassumption.
  rewrite w_addiw. reflexivity.
Qed.

#[using="Type"] Lemma step_slliw : forall segs regs pc mem rom w rd rs (sh : bv 5),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm32 ALU_SLL rd rs sh, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_slliw (getr regs rs) (bv_unsigned sh))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_shiftimm32_gen by eassumption.
  rewrite w_slliw. reflexivity.
Qed.

#[using="Type"] Lemma step_srliw : forall segs regs pc mem rom w rd rs (sh : bv 5),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm32 ALU_SRL rd rs sh, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_srliw (getr regs rs) (bv_unsigned sh))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_shiftimm32_gen by eassumption.
  rewrite w_srliw. reflexivity.
Qed.

#[using="Type"] Lemma step_sraiw : forall segs regs pc mem rom w rd rs (sh : bv 5),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm32 ALU_SRA rd rs sh, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_sraiw (getr regs rs) (bv_unsigned sh))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_shiftimm32_gen by eassumption.
  rewrite w_sraiw. reflexivity.
Qed.

#[using="Type"] Lemma step_addw : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op32 ALU_ADD rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_op32_gen by eassumption.
  rewrite w_addw. reflexivity.
Qed.

#[using="Type"] Lemma step_subw : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op32 ALU_SUB rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_subw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_op32_gen by eassumption.
  rewrite w_subw. reflexivity.
Qed.

#[using="Type"] Lemma step_sllw : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op32 ALU_SLL rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_sllw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_op32_gen by eassumption.
  rewrite w_sllw. reflexivity.
Qed.

#[using="Type"] Lemma step_srlw : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op32 ALU_SRL rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_srlw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_op32_gen by eassumption.
  rewrite w_srlw. reflexivity.
Qed.

#[using="Type"] Lemma step_sraw : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op32 ALU_SRA rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_sraw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_op32_gen by eassumption.
  rewrite w_sraw. reflexivity.
Qed.

#[using="Type"] Lemma step_mul : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul M_MUL rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_mul (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_mul_gen by eassumption.
  rewrite m_mul. reflexivity.
Qed.

#[using="Type"] Lemma step_mulh : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul M_MULH rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_mulh (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_mul_gen by eassumption.
  rewrite m_mulh. reflexivity.
Qed.

#[using="Type"] Lemma step_mulhsu : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul M_MULHSU rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_mulhsu (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_mul_gen by eassumption.
  rewrite m_mulhsu. reflexivity.
Qed.

#[using="Type"] Lemma step_mulhu : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul M_MULHU rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_mulhu (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_mul_gen by eassumption.
  rewrite m_mulhu. reflexivity.
Qed.

#[using="Type"] Lemma step_div : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul M_DIV rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_div (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_mul_gen by eassumption.
  rewrite m_div. reflexivity.
Qed.

#[using="Type"] Lemma step_rem : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul M_REM rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_rem (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_mul_gen by eassumption.
  rewrite m_rem. reflexivity.
Qed.

#[using="Type"] Lemma step_mulw : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul32 M_MUL rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_mulw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_mul32_gen by eassumption.
  rewrite w_mulw. reflexivity.
Qed.

#[using="Type"] Lemma step_divw : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul32 M_DIV rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_divw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_mul32_gen by eassumption.
  rewrite w_divw. reflexivity.
Qed.

#[using="Type"] Lemma step_divuw : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul32 M_DIVU rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_divuw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_mul32_gen by eassumption.
  rewrite w_divuw. reflexivity.
Qed.

#[using="Type"] Lemma step_remw : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul32 M_REM rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_remw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_mul32_gen by eassumption.
  rewrite w_remw. reflexivity.
Qed.

#[using="Type"] Lemma step_remuw : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul32 M_REMU rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_remuw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom).
Proof.
  intros. erewrite step_mul32_gen by eassumption.
  rewrite w_remuw. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma step_beq_tk : forall segs regs pc mem rom w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_EQ rs1 rs2 imm, 4%Z) ->
  c_eq (getr regs rs1) (getr regs rs2) = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (btgt pc (bv_signed imm)) mem rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hc.
  apply (step_branch_tk_gen segs regs pc mem rom w BC_EQ rs1 rs2 imm Hf He Hd).
  exact Hc.
Qed.

#[using="Type"] Lemma step_beq_ft : forall segs regs pc mem rom w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_EQ rs1 rs2 imm, 4%Z) ->
  c_eq (getr regs rs1) (getr regs rs2) = false ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hc.
  apply (step_branch_ft_gen segs regs pc mem rom w BC_EQ rs1 rs2 imm Hf He Hd).
  exact Hc.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma step_bne_tk : forall segs regs pc mem rom w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_NE rs1 rs2 imm, 4%Z) ->
  c_eq (getr regs rs1) (getr regs rs2) = false ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (btgt pc (bv_signed imm)) mem rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hc.
  apply (step_branch_tk_gen segs regs pc mem rom w BC_NE rs1 rs2 imm Hf He Hd).
  cbn [branch_taken]. unfold c_eq in Hc. rewrite Hc. reflexivity.
Qed.

#[using="Type"] Lemma step_bne_ft : forall segs regs pc mem rom w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_NE rs1 rs2 imm, 4%Z) ->
  c_eq (getr regs rs1) (getr regs rs2) = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hc.
  apply (step_branch_ft_gen segs regs pc mem rom w BC_NE rs1 rs2 imm Hf He Hd).
  cbn [branch_taken]. unfold c_eq in Hc. rewrite Hc. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma step_blt_tk : forall segs regs pc mem rom w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_LT rs1 rs2 imm, 4%Z) ->
  c_lts (getr regs rs1) (getr regs rs2) = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (btgt pc (bv_signed imm)) mem rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hc.
  apply (step_branch_tk_gen segs regs pc mem rom w BC_LT rs1 rs2 imm Hf He Hd).
  exact Hc.
Qed.

#[using="Type"] Lemma step_blt_ft : forall segs regs pc mem rom w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_LT rs1 rs2 imm, 4%Z) ->
  c_lts (getr regs rs1) (getr regs rs2) = false ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hc.
  apply (step_branch_ft_gen segs regs pc mem rom w BC_LT rs1 rs2 imm Hf He Hd).
  exact Hc.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma step_bge_tk : forall segs regs pc mem rom w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_GE rs1 rs2 imm, 4%Z) ->
  c_lts (getr regs rs1) (getr regs rs2) = false ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (btgt pc (bv_signed imm)) mem rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hc.
  apply (step_branch_tk_gen segs regs pc mem rom w BC_GE rs1 rs2 imm Hf He Hd).
  cbn [branch_taken]. unfold c_lts in Hc. rewrite Hc. reflexivity.
Qed.

#[using="Type"] Lemma step_bge_ft : forall segs regs pc mem rom w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_GE rs1 rs2 imm, 4%Z) ->
  c_lts (getr regs rs1) (getr regs rs2) = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hc.
  apply (step_branch_ft_gen segs regs pc mem rom w BC_GE rs1 rs2 imm Hf He Hd).
  cbn [branch_taken]. unfold c_lts in Hc. rewrite Hc. reflexivity.
Qed.

#[using="Type"] Lemma step_bltu_tk : forall segs regs pc mem rom w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_LTU rs1 rs2 imm, 4%Z) ->
  c_ltu (getr regs rs1) (getr regs rs2) = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (btgt pc (bv_signed imm)) mem rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hc.
  apply (step_branch_tk_gen segs regs pc mem rom w BC_LTU rs1 rs2 imm Hf He Hd).
  exact Hc.
Qed.

#[using="Type"] Lemma step_bltu_ft : forall segs regs pc mem rom w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_LTU rs1 rs2 imm, 4%Z) ->
  c_ltu (getr regs rs1) (getr regs rs2) = false ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hc.
  apply (step_branch_ft_gen segs regs pc mem rom w BC_LTU rs1 rs2 imm Hf He Hd).
  exact Hc.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma step_bgeu_tk : forall segs regs pc mem rom w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_GEU rs1 rs2 imm, 4%Z) ->
  c_ltu (getr regs rs1) (getr regs rs2) = false ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (btgt pc (bv_signed imm)) mem rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hc.
  apply (step_branch_tk_gen segs regs pc mem rom w BC_GEU rs1 rs2 imm Hf He Hd).
  cbn [branch_taken]. unfold c_ltu in Hc. rewrite Hc. reflexivity.
Qed.

#[using="Type"] Lemma step_bgeu_ft : forall segs regs pc mem rom w rs1 rs2 (imm : bv 13),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch BC_GEU rs1 rs2 imm, 4%Z) ->
  c_ltu (getr regs rs1) (getr regs rs2) = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hc.
  apply (step_branch_ft_gen segs regs pc mem rom w BC_GEU rs1 rs2 imm Hf He Hd).
  cbn [branch_taken]. unfold c_ltu in Hc. rewrite Hc. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma step_lui : forall segs regs pc mem rom w rd (imm : bv 20),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Lui rd imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lui (Z.shiftl (bv_signed imm) 12))) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd imm Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode.
  destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4, ?b_lui; reflexivity.
Qed.

#[using="Type"] Lemma step_auipc : forall segs regs pc mem rom w rd (imm : bv 20),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Auipc rd imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_auipc pc (Z.shiftl (bv_signed imm) 12))) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd imm Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode.
  destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4, ?b_auipc; reflexivity.
Qed.

#[using="Type"] Lemma step_jal_x0 : forall segs regs pc mem rom w (imm : bv 21),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Jal 0 imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (btgt pc (bv_signed imm)) mem rom).
Proof.
  intros segs regs pc mem rom w imm Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode.
  rewrite is_x0_0; cbv beta iota.
  rewrite b_addsext. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma step_jalr_gen : forall segs regs pc mem rom w rd rs1 (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Jalr rd rs1 imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
                  (jalr_tgt (getr regs rs1) (bv_signed imm)) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 imm Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_jalr, ?b_npc4; reflexivity.
Qed.

#[using="Type"] Lemma step_ecall : forall segs regs pc mem rom w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := Some (getr regs 17);
               ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}.
Proof.
  intros segs regs pc mem rom w Hfetch Hecall.
  unfold RiscvSemantics.step, RiscvSemantics.step_accesses.
  cbn [ms_pc ms_pc_val mkst].
  rewrite Hfetch. cbv beta iota.
  unfold RiscvSemantics.drop_access_report,
    RiscvSemantics.decode_exec_accesses.
  rewrite Hecall. cbv beta iota.
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma step_lbu : forall segs regs pc mem rom w rd rs (imm : bv 12) b,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 1%nat = Some [b] ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 (bv_unsigned b))) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm b Hfetch Hecall Hdecode Hread.
  assert (Hz : zext 64 (bv_extract 0 8 (le_bytes_to_word [b])) = Z_to_bv 64 (bv_unsigned b)).
  { rewrite le_word_1, b_extract8_id. apply bv_eq.
    unfold zext. Local Ltac2 Set LiaHints.tbl := fun () => "0020>44402793520.1654426366652.15000003004S1HS".
rewrite bv_zero_extend_unsigned by lia.
    rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
    pose proof (u8_range b). change (bv_modulus 64) with (2^64)%Z. lia. }
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite Hz, b_npc4.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma step_lb : forall segs regs pc mem rom w rd rs (imm : bv 12) b,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ1 true rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 1%nat = Some [b] ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lb b)) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm b Hfetch Hecall Hdecode Hread.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite b_lb_val, b_npc4.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
Qed.

#[using="Type"] Lemma step_lh : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ2 true rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 2%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lh v)) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), b_lh_val, b_npc4.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
Qed.

#[using="Type"] Lemma step_lhu : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ2 false rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 2%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
  assert (Hz : zext 64 (bv_extract 0 16 v) = v).
  { pose proof (rdn_length _ _ _ _ _ Hread) as Hlen.
    pose proof (bytes_le_to_Z_bound bs) as Hb.
    pose proof (bytes_le_to_Z_nonneg bs) as Hnn.
    rewrite Hlen in Hb. rewrite Hv in Hb, Hnn.
    apply bv_eq. unfold zext.
    Local Ltac2 Set LiaHints.tbl := fun () => "0020>51840270755.2054438950454.2000000=00FS4Hlen2Hb3HnnS4Hlen2Hb".
rewrite bv_zero_extend_unsigned by lia.
    rewrite bv_extract_unsigned, Z.shiftr_0_r.
    apply bv_wrap_small.
    change (bv_modulus 16) with 65536%Z.
    change (2 ^ (8 * Z.of_nat 2))%Z with 65536%Z in Hb. lia. }
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), Hz, b_npc4.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma step_lw : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ4 true rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 4%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lw v)) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), b_lw_val, b_npc4.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
Qed.

#[using="Type"] Lemma step_lwu : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ4 false rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 4%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
  assert (Hz : zext 64 (bv_extract 0 32 v) = v).
  { pose proof (rdn_length _ _ _ _ _ Hread) as Hlen.
    pose proof (bytes_le_to_Z_bound bs) as Hb.
    pose proof (bytes_le_to_Z_nonneg bs) as Hnn.
    rewrite Hlen in Hb. rewrite Hv in Hb, Hnn.
    apply bv_eq. unfold zext.
    Local Ltac2 Set LiaHints.tbl := fun () => "0020>51840270755.2054438950454.2000000=00FS4Hlen2Hb3HnnS4Hlen2Hb".
rewrite bv_zero_extend_unsigned by lia.
    rewrite bv_extract_unsigned, Z.shiftr_0_r.
    apply bv_wrap_small.
    change (bv_modulus 32) with 4294967296%Z.
    change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z in Hb. lia. }
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), Hz, b_npc4.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma step_ld : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ8 true rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 8%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
  assert (Hz : bv_extract 0 64 v = v).
  { apply bv_eq.
    rewrite bv_extract_unsigned, Z.shiftr_0_r.
    apply bv_wrap_bv_unsigned. }
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), Hz, b_npc4.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma two64_pos : (0 < 2^64)%Z.
Proof. Local Ltac2 Set LiaHints.tbl := fun () => "0010=38948964769.1000001S".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma v_addi_nneg : forall x imm, (0 <= imm)%Z -> (bv_unsigned x + imm < 2^64)%Z ->
  bv_unsigned (v_addi x imm) = (bv_unsigned x + imm)%Z.
Proof.
  intros x imm Hi Hs. unfold v_addi.
  rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  apply Z.mod_small. pose proof (u64_range x). Local Ltac2 Set LiaHints.tbl := fun () => "0010=15931679264.6000009S2Hi2Hs1H".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma v_addi_0 : forall x : word, v_addi x 0 = x.
Proof.
  intro x. apply bv_eq. unfold v_addi.
  rewrite Z_to_bv_unsigned, Z.add_0_r. apply bv_wrap_bv_unsigned.
Qed.

#[using="Type"] Lemma v_add_small : forall x y : word, (bv_unsigned x + bv_unsigned y < 2^64)%Z ->
  bv_unsigned (v_add x y) = (bv_unsigned x + bv_unsigned y)%Z.
Proof.
  intros x y H. unfold v_add.
  rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  apply Z.mod_small. pose proof (u64_range x). pose proof (u64_range y). Local Ltac2 Set LiaHints.tbl := fun () => "0010<8929201569.6000009S1H2H02H1".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma v_sub_small : forall x y : word, (bv_unsigned y <= bv_unsigned x)%Z ->
  bv_unsigned (v_sub x y) = (bv_unsigned x - bv_unsigned y)%Z.
Proof.
  intros x y H. unfold v_sub.
  rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  apply Z.mod_small. pose proof (u64_range x). pose proof (u64_range y). Local Ltac2 Set LiaHints.tbl := fun () => "0010<8929201569.6000009S1H2H02H1".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma v_slli_3 : forall x : word, (8 * bv_unsigned x < 2^64)%Z ->
  bv_unsigned (v_slli x 3) = (8 * bv_unsigned x)%Z.
Proof.
  intros x H8. unfold v_slli.
  rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  Local Ltac2 Set LiaHints.tbl := fun () => "0030=29784467158.343933807290.47789250740.4 000001007008SS2H81HS".
rewrite Z.shiftl_mul_pow2 by lia.
  change (2^3)%Z with 8%Z.
  pose proof (u64_range x).
  rewrite Z.mod_small by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma v_addi_0_1 : v_addi (Z_to_bv 64 0) 1 = Z_to_bv 64 1.
Proof. apply bv_eq. reflexivity. Qed.

#[using="Type"] Lemma v_addi_0_64 : v_addi (Z_to_bv 64 0) 64 = Z_to_bv 64 64.
Proof. apply bv_eq. reflexivity. Qed.

#[using="Type"] Lemma v_addi_Sj : forall j : nat, (Z.of_nat j + 1 < 2^64)%Z ->
  v_addi (nat_to_word j) 1 = nat_to_word (S j).
Proof.
  intros j _. apply bv_eq. unfold v_addi, nat_to_word.
  rewrite !Z_to_bv_unsigned.
  rewrite bv_wrap_add_idemp_l. f_equal. Local Ltac2 Set LiaHints.tbl := fun () => "0010=12526898174.2000001S".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma bv_signed_small : forall x : word, (bv_unsigned x < 2^63)%Z ->
  bv_signed x = bv_unsigned x.
Proof.
  intros x Hx. unfold bv_signed. apply bv_swrap_small.
  change (bv_half_modulus 64) with (2^63)%Z.
  pose proof (u64_range x). Local Ltac2 Set LiaHints.tbl := fun () => "0010=45126151194.4000006S2Hx1H".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma bv_signed_hi : forall x : word, (2^63 <= bv_unsigned x)%Z ->
  bv_signed x = (bv_unsigned x - 2^64)%Z.
Proof.
  intros x Hx. unfold bv_signed.
  Local Ltac2 Set LiaHints.tbl := fun () => "0010=56069883578.3000004S2Hx".
rewrite (bv_swrap_hi 64);
    [ change (bv_modulus 64) with (2^64)%Z; reflexivity
    | discriminate
    | change (bv_half_modulus 64) with (2^63)%Z; lia
    | change (bv_modulus 64) with (2^64)%Z; apply u64_range ].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma c_lts_small : forall x y : word,
  (bv_unsigned x < 2^63)%Z -> (bv_unsigned y < 2^63)%Z ->
  c_lts x y = bv_ltu x y.
Proof.
  intros x y Hx Hy. unfold c_lts, bv_lts, bv_ltu.
  rewrite !bv_signed_small by assumption. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma c_lts_neg_0 : forall x : word, (2^63 <= bv_unsigned x)%Z ->
  c_lts x (Z_to_bv 64 0) = true.
Proof.
  intros x Hx. unfold c_lts, bv_lts.
  change (bv_signed (Z_to_bv 64 0)) with 0%Z.
  rewrite bv_signed_hi by exact Hx.
  apply Z.ltb_lt. pose proof (u64_range x). Local Ltac2 Set LiaHints.tbl := fun () => "0010=39535074504.4000003S1H".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma c_lts_pos_0 : forall x : word, (bv_unsigned x < 2^63)%Z ->
  c_lts x (Z_to_bv 64 0) = false.
Proof.
  intros x Hx. unfold c_lts, bv_lts.
  change (bv_signed (Z_to_bv 64 0)) with 0%Z.
  rewrite bv_signed_small by exact Hx.
  apply Z.ltb_ge. pose proof (u64_range x). Local Ltac2 Set LiaHints.tbl := fun () => "0010=54651417507.4000003S1H".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma c_lts_0_pos : forall n : word,
  (1 <= bv_unsigned n)%Z -> (bv_unsigned n < 2^63)%Z ->
  c_lts (Z_to_bv 64 0) n = true.
Proof.
  intros n H1 H2.
  rewrite c_lts_small;
    [ unfold bv_ltu; apply Z.ltb_lt;
      change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia
    | change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia
    | lia ].
Qed.

#[using="Type"] Lemma errno_ret_range : forall e, (1 <= e)%Z -> (e <= 4095)%Z ->
  (2^63 <= bv_unsigned (errno_ret e))%Z /\ (bv_unsigned (errno_ret e) < 2^64)%Z.
Proof.
  intros e H1 H2. unfold errno_ret.
  rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  Local Ltac2 Set LiaHints.tbl := fun () => "0030=13019971807.441619028705.450358283322.400000700800?S2H12H2SS2H12H2".
replace (- e)%Z with ((2^64 - e) + (-1) * 2^64)%Z by lia.
  rewrite Z_mod_plus_full.
  rewrite Z.mod_small by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma errno_ret_signed : forall e, (1 <= e)%Z -> (e <= 4095)%Z ->
  bv_signed (errno_ret e) = (- e)%Z.
Proof.
  intros e H1 H2.
  destruct (errno_ret_range e H1 H2) as [Hlo Hhi].
  rewrite bv_signed_hi by exact Hlo.
  unfold errno_ret in *.
  rewrite Z_to_bv_unsigned, bv_wrap64_mod in *.
  Local Ltac2 Set LiaHints.tbl := fun () => "0030=39321484675.641616922552.650360369507.6000001002009SSS2H12H2".
replace (- e)%Z with ((2^64 - e) + (-1) * 2^64)%Z by lia.
  rewrite Z_mod_plus_full.
  rewrite Z.mod_small by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma c_lts_errno : forall e, (1 <= e)%Z -> (e <= 4095)%Z ->
  c_lts (errno_ret e) (Z_to_bv 64 0) = true.
Proof.
  intros e H1 H2. destruct (errno_ret_range e H1 H2) as [Hlo _].
  apply c_lts_neg_0; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma c_eq_small : forall x y : word, c_eq x y = bv_eqb x y.
Proof. reflexivity. Qed.

#[using="Type"] Lemma c_ltu_small : forall x y : word, c_ltu x y = bv_ltu x y.
Proof. reflexivity. Qed.

#[using="Type"] Lemma c_eq_0_false : forall x : word, bv_unsigned x <> 0%Z ->
  c_eq x (Z_to_bv 64 0) = false.
Proof.
  intros x Hnz. unfold c_eq, bv_eqb. apply Z.eqb_neq.
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. exact Hnz.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma c_eq_0_of_u : forall x : word, bv_unsigned x = 0%Z ->
  c_eq x (Z_to_bv 64 0) = true.
Proof.
  intros x Hx. unfold c_eq, bv_eqb. rewrite Hx. reflexivity.
Qed.

#[using="Type"] Lemma c_eq_0_true : c_eq (Z_to_bv 64 0) (Z_to_bv 64 0) = true.
Proof. reflexivity. Qed.

#[using="Type"] Lemma c_eq_neq : forall x y : word, bv_unsigned x <> bv_unsigned y ->
  c_eq x y = false.
Proof. intros x y Hne. unfold c_eq, bv_eqb. apply Z.eqb_neq. exact Hne. Qed.

#[using="Type"] Lemma c_eq_refl : forall x : word, c_eq x x = true.
Proof. intro x. apply bv_eqb_refl. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma getr_same : forall regs (r : reg) v, r <> 0 -> getr (regupd regs r v) r = v.
Proof.
  intros regs r v H. unfold getr, regupd, reg_get.
  rewrite (bv_eqb_neq r 0 H), bvmap_get_set_same. reflexivity.
Qed.

#[using="Type"] Lemma getr_other : forall regs (r : reg) v r', r' <> r ->
  getr (regupd regs r v) r' = getr regs r'.
Proof.
  intros regs r v r' H. unfold getr, regupd, reg_get.
  destruct (bv_eqb r' 0); [reflexivity|].
  rewrite bvmap_get_set_other by congruence. reflexivity.
Qed.

#[using="Type"] Lemma getr_nz : forall regs (r : reg), r <> 0 -> getr regs r = reg_get regs r.
Proof.
  intros regs r H. unfold getr. rewrite (bv_eqb_neq r 0 H). reflexivity.
Qed.

#[using="Type"] Lemma regupd_other : forall regs (r : reg) v r', r' <> r ->
  reg_get (regupd regs r v) r' = reg_get regs r'.
Proof.
  intros regs r v r' H. unfold regupd, reg_get.
  rewrite bvmap_get_set_other by congruence. reflexivity.
Qed.

#[using="Type"] Lemma regupd_same : forall regs (r : reg) v, reg_get (regupd regs r v) r = v.
Proof.
  intros. unfold regupd, reg_get. rewrite bvmap_get_set_same. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP2.
Ltac split_value_ifs :=
  repeat match goal with
  | |- context [if ?b then _ else _] =>
      lazymatch type of b with
      | bool =>
          lazymatch b with
          | true => fail
          | false => fail
          | _ => destruct b
          end
      end
  end.

Section WithFP3.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma bytes_le_single : forall b : byte, bytes_le_to_Z [b] = bv_unsigned b.
Proof. intro b. cbn. apply Z.lor_0_r. Qed.

#[using="Type"] Lemma bv_wrap8_mod : forall z : Z, bv_wrap 8 z = (z mod 2^8)%Z.
Proof. reflexivity. Qed.

#[using="Type"] Lemma bytes_le_Z_to_le : forall k z, (0 <= z)%Z ->
  bytes_le_to_Z (Z_to_le_bytes k z) = (z mod 2^(8 * Z.of_nat k))%Z.
Proof.
  induction k as [|k IH]; intros z Hz.
  - cbn. change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. rewrite Z.mod_1_r. reflexivity.
  - cbn [Z_to_le_bytes bytes_le_to_Z].
    Local Ltac2 Set LiaHints.tbl := fun () => "00=0>10351595562.8 15550977503.1017512634527.9 20020705838.1020020705915.9 2672677186.5  29015431002.9 37870071051.1045144394663.1047068977701.1057467540542.5 59021195150.108661093874.9  00000400;00@00E00L00M00R00S00X00]00a00h00mS2HiS1H3HikS3Hi8S3HikS1H3Hi8SS3Hi8SS3Hi8S3HikS2HzS1H3HikS3Hi8".
rewrite IH by (apply Z.shiftr_nonneg; lia).
    rewrite Z_to_bv_unsigned, bv_wrap8_mod.
    replace (8 * Z.of_nat (S k))%Z with (8 * Z.of_nat k + 8)%Z by lia.
    pose proof (Nat2Z.is_nonneg k).
    apply Z.bits_inj'. intros i Hi.
    rewrite Z.lor_spec, Z.shiftl_spec by lia.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + rewrite (Z.mod_pow2_bits_low z 8 i) by lia.
      rewrite (Z.mod_pow2_bits_low z (8 * Z.of_nat k + 8) i) by lia.
      rewrite (Z.testbit_neg_r _ (i - 8)) by lia.
      apply orb_false_r.
    + rewrite (Z.mod_pow2_bits_high z 8 i) by lia.
      rewrite orb_false_l.
      destruct (Z.lt_ge_cases i (8 * Z.of_nat k + 8)) as [Hik|Hik].
      * rewrite (Z.mod_pow2_bits_low _ (8 * Z.of_nat k) (i - 8)) by lia.
        rewrite Z.shiftr_spec by lia.
        rewrite (Z.mod_pow2_bits_low z (8 * Z.of_nat k + 8) i) by lia.
        f_equal. lia.
      * rewrite (Z.mod_pow2_bits_high _ (8 * Z.of_nat k) (i - 8)) by lia.
        rewrite (Z.mod_pow2_bits_high z (8 * Z.of_nat k + 8) i) by lia.
        reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma bytes_le_N : forall k (v : word),
  bytes_le_to_Z (word_to_le_bytes k v) = (bv_unsigned v mod 2^(8 * Z.of_nat k))%Z.
Proof.
  intros k v. unfold word_to_le_bytes.
  apply bytes_le_Z_to_le. apply u64_range.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma n_to_le_8_spec : forall v : word, word_le8 v = word_to_le_bytes 8 v.
Proof. reflexivity. Qed.

#[using="Type"] Lemma bytes_le_n_to_le_8 : forall v : word, bytes_le_to_Z (word_le8 v) = bv_unsigned v.
Proof.
  intro v. rewrite n_to_le_8_spec, bytes_le_N.
  change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z.
  apply Z.mod_small. apply u64_range.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma nth_error_skipn_cons : forall {A} (bs : list A) d, (d < length bs)%nat ->
  exists b, nth_error bs d = Some b /\ skipn d bs = b :: skipn (S d) bs.
Proof.
  intros A bs. Local Ltac2 Set LiaHints.tbl := fun () => "0020=39781402342.46252201786.7 000004008S2HdS2Hd".
induction bs as [|x bs IH]; intros d Hd; [cbn in Hd; lia|].
  destruct d as [|d'].
  - exists x. split; reflexivity.
  - cbn [length] in Hd. destruct (IH d' ltac:(lia)) as [b [H1 H2]].
    exists b. split; [exact H1|]. cbn [skipn]. exact H2.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma u_add1 : forall a : word, (bv_unsigned a + 1 < 2^64)%Z ->
  bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z.
Proof.
  intros a Ha. rewrite bv_add_unsigned.
  change (bv_unsigned (1 : word)) with 1%Z.
  rewrite bv_wrap64_mod. apply Z.mod_small.
  pose proof (u64_range a). Local Ltac2 Set LiaHints.tbl := fun () => "0010=19622140058.4000006S2Ha1H".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma rdn_stack : forall segs sp bytes k addr,
  (bv_unsigned sp <= bv_unsigned addr)%Z ->
  (Z.to_nat (bv_unsigned addr - bv_unsigned sp) + k <= length bytes)%nat ->
  (bv_unsigned sp + Z.of_nat (length bytes) < 2^64)%Z ->
  rdn segs (stack_to_mem sp bytes) addr k =
  Some (firstn k (skipn (Z.to_nat (bv_unsigned addr - bv_unsigned sp)) bytes)).
Proof.
  intros segs sp bytes k. induction k as [|k IH]; intros addr Hsp Hlen Hnw.
  - cbn. reflexivity.
  - cbn [rdn].
    Local Ltac2 Set LiaHints.tbl := fun () => "0080>14214055304.1015582862278.1320176326353.1623117262644.1630147437522.15525791011.16  53058843585.1460129627789.1600000600@00J00T00b01001601DS4HlenS3Hsp4HlenS4Hlen3HnwS4Hlen3Hu1S4Hlen3Hnw3HltS4Hlen3Hle3Hu1S4HlenS4Hlen3Hle3Hu1".
destruct (nth_error_skipn_cons bytes (Z.to_nat (bv_unsigned addr - bv_unsigned sp)) ltac:(lia)) as [b [Hnth Hskip]].
    unfold stack_to_mem.
    assert (Hle : Z.leb (bv_unsigned sp) (bv_unsigned addr) = true) by (apply Z.leb_le; lia).
    rewrite Hle.
    assert (Hlt : Z.ltb (bv_unsigned addr - bv_unsigned sp) (Z.of_nat (length bytes)) = true)
      by (apply Z.ltb_lt; lia).
    rewrite Hlt. rewrite Hnth.
    assert (Hu1 : bv_unsigned (addr + 1) = (bv_unsigned addr + 1)%Z) by (apply u_add1; lia).
    rewrite IH by lia.
    rewrite Hskip.
    replace (Z.to_nat (bv_unsigned (addr + 1) - bv_unsigned sp))
      with (S (Z.to_nat (bv_unsigned addr - bv_unsigned sp))) by lia.
    reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma rdn_ext : forall segs k m1 m2 (a : word),
  (bv_unsigned a + Z.of_nat k <= 2^64)%Z ->
  (forall x : word, (bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat k)%Z -> m1 x = m2 x) ->
  rdn segs m1 a k = rdn segs m2 a k.
Proof.
  intros segs k. induction k as [|k IH]; intros m1 m2 a Hnw Hext; [reflexivity|].
  cbn [rdn].
  Local Ltac2 Set LiaHints.tbl := fun () => "0040>11406160495.9 20965832707.1256948188685.1065876346564.1000000500A00F00OS3HnwS3Hnw3Hu12HxS3HnwS3Hnw3Hu1".
rewrite (Hext a ltac:(pose proof (u64_range a); lia)).
  destruct k as [|k'].
  - reflexivity.
  - assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
    rewrite (IH m1 m2 (a+1) ltac:(lia)
              ltac:(intros x Hx; apply Hext; lia)).
    reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma length_n_to_le_8 : forall v : word, length (word_le8 v) = 8%nat.
Proof. reflexivity. Qed.

#[using="Type"] Lemma length_flat_map_le8 : forall l : list word, length (flat_map word_le8 l) = (8 * length l)%nat.
Proof.
  induction l as [|x l IH]; [reflexivity|].
  cbn [flat_map length]. rewrite length_app, IH, length_n_to_le_8. Local Ltac2 Set LiaHints.tbl := fun () => "0010=24243817879.4000004S2IH".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Definition total_arg_bytes_nat (args : list (list byte)) : nat :=
  fold_right (fun a acc => length a + 1 + acc)%nat 0%nat args.

#[using="Type"] Lemma total_arg_bytes_Z : forall l,
  total_arg_bytes l = Z.of_nat (total_arg_bytes_nat l).
Proof.
  induction l as [|x l IH]; [reflexivity|].
  cbv [total_arg_bytes total_arg_bytes_nat] in *. cbn [fold_right].
  rewrite IH. Local Ltac2 Set LiaHints.tbl := fun () => "0010=41340549263.4000001S".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma length_flatten_strings : forall l, length (flatten_strings l) = total_arg_bytes_nat l.
Proof.
  induction l as [|x l IH]; [reflexivity|].
  cbv [flatten_strings total_arg_bytes_nat] in *. cbn [flat_map fold_right].
  rewrite length_app, IH. rewrite length_app. cbn [length]. Local Ltac2 Set LiaHints.tbl := fun () => "0010=27449323548.4000004S2IH".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma len_word_nat : forall {A} (l : list A), len_word l = nat_to_word (length l).
Proof. reflexivity. Qed.

#[using="Type"] Lemma word1_nat : (1 : word) = nat_to_word 1.
Proof. apply bv_eq. reflexivity. Qed.

#[using="Type"] Lemma word_add_0 : forall a : word, a + nat_to_word 0 = a.
Proof.
  intro a. apply bv_eq. unfold nat_to_word.
  rewrite bv_add_unsigned, Z_to_bv_unsigned.
  change (bv_wrap 64 (Z.of_nat 0)) with 0%Z.
  rewrite Z.add_0_r. apply bv_wrap_bv_unsigned.
Qed.

#[using="Type"] Lemma nat_to_word_merge : forall m k : nat,
  nat_to_word m + nat_to_word k = nat_to_word (m + k).
Proof.
  intros m k. apply bv_eq. unfold nat_to_word.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  rewrite bv_wrap_add_idemp_l, bv_wrap_add_idemp_r.
  f_equal. Local Ltac2 Set LiaHints.tbl := fun () => "0010=66083752519.3000001S".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma nat_to_word_add_merge : forall (a : word) (m k : nat),
  a + nat_to_word m + nat_to_word k = a + nat_to_word (m + k).
Proof.
  intros a m k.
  rewrite <- (assoc_L bv_add).
  rewrite nat_to_word_merge. reflexivity.
Qed.

#[using="Type"] Lemma string_addrs_fst_structure : forall strs (base : word),
  fst (string_addrs base strs) =
  match strs with
  | [] => []
  | s :: rest => base :: fst (string_addrs (base + len_word s + 1) rest)
  end.
Proof.
  intros strs base. destruct strs as [|s rest]; [reflexivity|].
  cbn [string_addrs].
  destruct (string_addrs (base + len_word s + 1) rest) as [ptrs fin] eqn:E.
  reflexivity.
Qed.

#[using="Type"] Lemma string_addrs_pair : forall strs (base : word),
  string_addrs base strs = (fst (string_addrs base strs), base + nat_to_word (total_arg_bytes_nat strs)).
Proof.
  induction strs as [|s rest IH]; intro base.
  - cbn. rewrite word_add_0. reflexivity.
  - cbn [string_addrs].
    rewrite (IH (base + len_word s + 1)).
    cbn [fst]. f_equal.
    rewrite len_word_nat, word1_nat, !nat_to_word_add_merge.
    cbv [total_arg_bytes_nat]. cbn [fold_right]. f_equal. f_equal. Local Ltac2 Set LiaHints.tbl := fun () => "0010=35832502097.5000001S".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma length_string_addrs_fst : forall strs (base : word),
  length (fst (string_addrs base strs)) = length strs.
Proof.
  induction strs as [|s rest IH]; intro base; [reflexivity|].
  rewrite string_addrs_fst_structure. cbn [length]. rewrite IH. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma build_stack_bytes_within_span : forall ph (sp : word) a e uid hw rnd,
  (Z.of_nat (length (build_stack_bytes ph sp a e uid hw rnd))
   <= entry_stack_span a e)%Z.
Proof.
  intros ph sp a e uid hw rnd.
  unfold entry_stack_span, build_stack_bytes. cbv zeta.
  rewrite (string_addrs_pair a). cbv beta iota.
  rewrite (string_addrs_pair e). cbv beta iota.
  rewrite !length_app, repeat_length, !length_flat_map_le8,
    !length_string_addrs_fst, !length_n_to_le_8, length_auxv_bytes,
    !length_flatten_strings, length_at_random_bytes.
  rewrite !total_arg_bytes_Z.
  Local Ltac2 Set LiaHints.tbl := fun () => "0020=41906240739.963369996410.8000005006S3HpdS".
match goal with
  | |- context [Z.to_nat ?pd] =>
      assert (Hpd : (0 <= pd < 8)%Z) by (apply Z.mod_pos_bound; lia)
  end.
  unfold auxv_size. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma bsb_argc_prefix : forall ph (sp : word) argv envp uid hw rnd, exists tl,
  build_stack_bytes ph sp argv envp uid hw rnd = word_le8 (len_word argv) ++ tl.
Proof.
  intros ph sp argv envp uid hw rnd. unfold build_stack_bytes.
  rewrite (string_addrs_pair argv). cbv beta iota.
  rewrite (string_addrs_pair envp). cbv beta iota.
  eexists. rewrite <- !app_assoc. reflexivity.
Qed.

#[using="Type"] Lemma read_at_offset : forall segs (sp : word) bytes pre mid post k,
  bytes = pre ++ mid ++ post -> length mid = k ->
  (bv_unsigned sp + Z.of_nat (length bytes) < 2^64)%Z ->
  rdn segs (stack_to_mem sp bytes) (sp + nat_to_word (length pre)) k = Some mid.
Proof.
  intros segs sp bytes pre mid post k Hb Hk Hnw.
  pose proof (u64_range sp) as Hsp64.
  Local Ltac2 Set LiaHints.tbl := fun () => "0050>22622882728.1443764808952.12675391163.16  6899969816.15 8935498613.13 00000?00C00W00c019S2Hk7Hlenpre2HuS2HkS2Hk7Hlenpre2Hu4HlenS2Hk7HlenpreS2Hk3Hnw5Hsp647Hlenpre".
assert (Hlenpre : (length pre <= length bytes)%nat)
    by (rewrite Hb, !length_app; lia).
  assert (Hu : bv_unsigned (sp + nat_to_word (length pre)) = (bv_unsigned sp + Z.of_nat (length pre))%Z).
  { unfold nat_to_word. rewrite bv_add_unsigned, Z_to_bv_unsigned.
    rewrite bv_wrap_add_idemp_r, bv_wrap64_mod.
    apply Z.mod_small. lia. }
  assert (Hsp : (bv_unsigned sp <= bv_unsigned (sp + nat_to_word (length pre)))%Z) by lia.
  assert (Hlen : (Z.to_nat (bv_unsigned (sp + nat_to_word (length pre)) - bv_unsigned sp) + k <= length bytes)%nat)
    by (rewrite Hu, Hb, !length_app; lia).
  rewrite (rdn_stack segs sp bytes k _ Hsp Hlen Hnw).
  rewrite Hu.
  replace (Z.to_nat (bv_unsigned sp + Z.of_nat (length pre) - bv_unsigned sp)) with (length pre) by lia.
  rewrite Hb, skipn_app, skipn_all, Nat.sub_diag.
  cbn [app]. rewrite skipn_O.
  rewrite firstn_app, <- Hk, firstn_all, Nat.sub_diag.
  cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma rdn_image_in_block :
  forall segs ph (sp : word) argv envp uid hwcap draw (a : word) n,
  (bv_unsigned a + Z.of_nat n
   <= entry_block_top sp (build_stack_bytes ph sp argv envp uid hwcap draw))%Z ->
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  rdn segs (stack_to_mem sp (entry_stack_image ph sp argv envp uid hwcap draw)) a n
  = rdn segs (stack_to_mem sp (build_stack_bytes ph sp argv envp uid hwcap draw)) a n.
Proof.
  intros segs ph sp argv envp uid hwcap draw a n Hin Hnw.
  apply rdn_ext; [exact Hnw|].
  intros x Hx. apply stack_to_mem_image_in_block. Local Ltac2 Set LiaHints.tbl := fun () => "0010=5620982045.15000008S3Hin2Hx".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma read_at_offset_image :
  forall segs ph (sp : word) argv envp uid hwcap draw pre mid post k,
  build_stack_bytes ph sp argv envp uid hwcap draw = pre ++ mid ++ post ->
  length mid = k ->
  (bv_unsigned sp
   + Z.of_nat (length (build_stack_bytes ph sp argv envp uid hwcap draw)) < 2^64)%Z ->
  rdn segs (stack_to_mem sp (entry_stack_image ph sp argv envp uid hwcap draw))
      (sp + nat_to_word (length pre)) k
  = Some mid.
Proof.
  intros segs ph sp argv envp uid hwcap draw pre mid post k Hb Hk Hnw.
  pose proof (u64_range sp) as Hsp64.
  Local Ltac2 Set LiaHints.tbl := fun () => "0040>23847354003.1932059413533.1949609335268.178941791228.18 00000=00F00J00]S2Hk3Hnw4HlenS2Hk4HlenS2HkS2Hk3Hnw5Hsp644Hlen".
assert (Hlen : (length pre + length mid <= length (build_stack_bytes ph sp argv envp uid hwcap draw))%nat)
    by (rewrite Hb, !length_app; lia).
  assert (Hu : bv_unsigned (sp + nat_to_word (length pre))
               = (bv_unsigned sp + Z.of_nat (length pre))%Z).
  { unfold nat_to_word. rewrite bv_add_unsigned, Z_to_bv_unsigned.
    rewrite bv_wrap_add_idemp_r, bv_wrap64_mod. apply Z.mod_small. lia. }
  rewrite rdn_image_in_block
    by (unfold entry_block_top; rewrite Hu; lia).
  exact (read_at_offset segs sp _ pre mid post k Hb Hk Hnw).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma read_argc : forall ph segs (sp : word) argv envp uid hw rnd,
  (bv_unsigned sp + Z.of_nat (length (build_stack_bytes ph sp argv envp uid hw rnd)) < 2^64)%Z ->
  rdn segs (stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rnd)) sp 8%nat
  = Some (word_le8 (len_word argv)).
Proof.
  intros ph segs sp argv envp uid hw rnd Hnw.
  destruct (bsb_argc_prefix ph sp argv envp uid hw rnd) as [tl E].
  pose proof (read_at_offset_image segs ph sp argv envp uid hw rnd [] (word_le8 (len_word argv)) tl 8%nat) as H.
  cbn [length] in H.
  rewrite word_add_0 in H.
  apply H; [rewrite E; reflexivity|reflexivity|exact Hnw].
Qed.

#[using="Type"] Lemma read_byte_at : forall segs (sp : word) bytes pre s post j,
  bytes = pre ++ s ++ post -> (j < length s)%nat ->
  (bv_unsigned sp + Z.of_nat (length bytes) < 2^64)%Z ->
  rdn segs (stack_to_mem sp bytes) (sp + nat_to_word (length pre + j)) 1%nat
  = Some [nth j s (Z_to_bv 8 0)].
Proof.
  intros segs sp bytes pre s post j Hb Hj Hnw.
  destruct (nth_error_skipn_cons s j Hj) as [b [Hnth Hskip]].
  assert (Hsj : s = firstn j s ++ b :: skipn (S j) s)
    by (rewrite <- Hskip; symmetry; apply firstn_skipn).
  pose proof (read_at_offset segs sp bytes (pre ++ firstn j s) [b] (skipn (S j) s ++ post) 1%nat) as H.
  rewrite length_app in H.
  Local Ltac2 Set LiaHints.tbl := fun () => "0010>39868555619.16000004S2Hj".
rewrite firstn_length_le in H by lia.
  replace (nth j s (Z_to_bv 8 0)) with b by (symmetry; apply (nth_error_nth _ _ _ Hnth)).
  apply H; [|reflexivity|exact Hnw].
  rewrite Hb. rewrite Hsj at 1. rewrite <- !app_assoc. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma read_byte_at_image :
  forall segs ph (sp : word) argv envp uid hwcap draw pre s post j,
  build_stack_bytes ph sp argv envp uid hwcap draw = pre ++ s ++ post ->
  (j < length s)%nat ->
  (bv_unsigned sp
   + Z.of_nat (length (build_stack_bytes ph sp argv envp uid hwcap draw))
     < 2^64)%Z ->
  rdn segs (stack_to_mem sp (entry_stack_image ph sp argv envp uid hwcap draw))
      (sp + nat_to_word (length pre + j)) 1%nat
  = Some [nth j s (Z_to_bv 8 0)].
Proof.
  intros segs ph sp argv envp uid hwcap draw pre s post j Hb Hj Hnw.
  destruct (nth_error_skipn_cons s j Hj) as [b [Hnth Hskip]].
  assert (Hsj : s = firstn j s ++ b :: skipn (S j) s)
    by (rewrite <- Hskip; symmetry; apply firstn_skipn).
  pose proof (read_at_offset_image segs ph sp argv envp uid hwcap draw
                (pre ++ firstn j s) [b] (skipn (S j) s ++ post) 1%nat) as H.
  rewrite length_app in H.
  Local Ltac2 Set LiaHints.tbl := fun () => "0010>39868555619.21000004S2Hj".
rewrite firstn_length_le in H by lia.
  replace (nth j s (Z_to_bv 8 0)) with b by (symmetry; apply (nth_error_nth _ _ _ Hnth)).
  apply H; [|reflexivity|exact Hnw].
  rewrite Hb. rewrite Hsj at 1. rewrite <- !app_assoc. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma nth_app0_bound : forall (a1 : list byte) j,
  (bv_unsigned (nth j (a1 ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)) < 256)%Z.
Proof.
  intros a1 j. apply u8_range.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma page_round_up_Z_le : forall z b,
  (z <= b)%Z -> (b mod page_size = 0)%Z -> (page_round_up_Z z <= b)%Z.
Proof.
  intros z b Hzb Hb. unfold page_round_up_Z, page_size in *.
  Local Ltac2 Set LiaHints.tbl := fun () => "0060=18926749606.518926758641.618928853613.733901671357.738589249114.759861017451.600000100200300;00?00KSSSS2Hb3HbmS2HqS3Hzb2Hb3Hbm".
pose proof (Z.div_mod b 4096 ltac:(lia)) as Hbm.
  assert (Hq : ((z + 4096 - 1) / 4096 < b / 4096 + 1)%Z)
    by (apply Z.div_lt_upper_bound; lia).
  apply Z.le_trans with (m := (b / 4096 * 4096)%Z); [|lia].
  apply Z.mul_le_mono_nonneg_r; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma entry_page_top_within_window :
  forall ph (sp : word) argv envp uid hwcap draw,
  entry_stack_fits sp argv envp ->
  (entry_page_top sp (build_stack_bytes ph sp argv envp uid hwcap draw)
   <= sp_window_hi)%Z.
Proof.
  intros ph sp argv envp uid hwcap draw Hfit.
  pose proof (build_stack_bytes_within_span ph sp argv envp uid hwcap draw) as Hlen.
  unfold entry_stack_fits in Hfit. unfold entry_page_top.
  Local Ltac2 Set LiaHints.tbl := fun () => "0010>42336781841.1000000;S4Hfit4Hlen".
apply page_round_up_Z_le; [ unfold entry_block_top; lia | reflexivity ].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Definition wrap_mem (ph : PhdrInfo) (sp : word) (argv envp : list (list byte))
    (uid : word) (hw : word) (rnd : EntryDraw) : word -> option byte :=
  fun addr =>
    match stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rnd) addr with
    | Some b => Some b
    | None =>
      if andb (Z.leb (bv_unsigned sp - stack_max_size) (bv_unsigned addr))
              (Z.ltb (bv_unsigned addr) (bv_unsigned sp))
      then Some (Z_to_bv 8 0) else None
    end.

#[using="Type"] Lemma init_mkst : forall segs (pc : N) ph (sp : word) argv envp uid hw rnd,
  init_machine_state segs pc ph sp rnd argv envp uid hw =
  @mkst fx0 (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp)
       (Z_to_bv 64 (Z.of_N pc)) (wrap_mem ph sp argv envp uid hw rnd) (seg_rom segs).
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma wrap_above_sp : forall ph (sp : word) argv envp (x : word) uid hw rnd,
  (bv_unsigned sp <= bv_unsigned x)%Z ->
  wrap_mem ph sp argv envp uid hw rnd x = stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rnd) x.
Proof.
  intros ph sp argv envp x uid hw rnd Hx. unfold wrap_mem.
  destruct (stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rnd) x) as [b|] eqn:E; [reflexivity|].
  Local Ltac2 Set LiaHints.tbl := fun () => "0010>29668388163.11000004S2Hx".
assert (Hltf : Z.ltb (bv_unsigned x) (bv_unsigned sp) = false) by (apply Z.ltb_ge; lia).
  rewrite Hltf, andb_false_r. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma rdn_wrap_stack_above : forall segs ph (sp : word) argv envp (a : word) n uid hw rnd,
  (bv_unsigned sp <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  rdn segs (wrap_mem ph sp argv envp uid hw rnd) a n
  = rdn segs (stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rnd)) a n.
Proof.
  intros segs ph sp argv envp a n uid hw rnd Hsp Hnw.
  apply rdn_ext; [exact Hnw|].
  intros x Hx. apply wrap_above_sp. Local Ltac2 Set LiaHints.tbl := fun () => "0010>29666112188.15000008S3Hsp2Hx".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End WithFP3.
