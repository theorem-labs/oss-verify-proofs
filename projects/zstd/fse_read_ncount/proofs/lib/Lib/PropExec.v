(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Export LiaTuning.
Class FPState := mkFP { fp_regs : bvmap 5 word; fp_csr : bv 32 }.
Definition fx0 : FPState := mkFP bvmap_empty (Z_to_bv 32 0).
Definition mkst `{fx : FPState} (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) : machine_state :=
{| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := None; ms_resv := None; ms_fcsr := fp_csr;
ms_mem := mem; ms_rom := rom |}.
Section WithFP1.
Context {fx : FPState}.
Definition getr (regs : bvmap 5 word) (r : reg) : word :=
if bv_eqb r 0 then Z_to_bv 64 0 else reg_get regs r.
Definition regupd (regs : bvmap 5 word) (r : reg) (v : word) : bvmap 5 word :=
bvmap_set r v regs.
#[using="Type"] Lemma bv_eqb0_is_x0 : forall r : reg, bv_eqb r 0 = is_x0 r.
Proof. reflexivity. Qed.
#[using="Type"] Lemma bv_wrap32_mod : forall z : Z, bv_wrap 32 z = (z mod 2^32)%Z.
Proof. reflexivity. Qed.
#[using="Type"] Lemma bv_eqb_refl : forall {n} (a : bv n), bv_eqb a a = true.
Proof. intros n a. unfold bv_eqb. apply Z.eqb_refl. Qed.
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
Definition c_lts (x y : word) : bool := bv_lts x y.
Definition c_ltu (x y : word) : bool := bv_ltu x y.
Definition btgt (pc : word) (imm : Z) : word := v_addi pc imm.
Definition v_slti (x : word) (imm : Z) : word :=
if (zsig x <? imm)%Z then Z_to_bv 64 1 else Z_to_bv 64 0.
Definition v_sltiu (x : word) (imm : Z) : word :=
if (bv_unsigned x <? bv_wrap 64 imm)%Z then Z_to_bv 64 1 else Z_to_bv 64 0.
Definition v_slt (x y : word) : word := if c_lts x y then Z_to_bv 64 1 else Z_to_bv 64 0.
Definition v_sltu (x y : word) : word := if c_ltu x y then Z_to_bv 64 1 else Z_to_bv 64 0.
Definition v_slli (x : word) (sh : Z) : word := Z_to_bv 64 (Z.shiftl (bv_unsigned x) sh).
Definition v_srli (x : word) (sh : Z) : word := Z_to_bv 64 (Z.shiftr (bv_unsigned x) sh).
Definition v_srai (x : word) (sh : Z) : word := Z_to_bv 64 (Z.shiftr (bv_signed x) sh).
Definition v_sll (x y : word) : word :=
Z_to_bv 64 (Z.shiftl (bv_unsigned x) (bv_unsigned y mod 64)).
Definition v_srl (x y : word) : word :=
Z_to_bv 64 (Z.shiftr (bv_unsigned x) (bv_unsigned y mod 64)).
Definition v_sra (x y : word) : word :=
Z_to_bv 64 (Z.shiftr (bv_signed x) (bv_unsigned y mod 64)).
Definition v_lui (imm : Z) : word := Z_to_bv 64 imm.
Definition v_auipc (pc : word) (imm : Z) : word := Z_to_bv 64 (imm + bv_unsigned pc).
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
Definition v_mulh (x y : word) : word :=
Z_to_bv 64 (Z.shiftr (bv_signed x * bv_signed y) 64).
Definition v_mulhsu (x y : word) : word :=
Z_to_bv 64 (Z.shiftr (bv_signed x * bv_unsigned y) 64).
Definition v_mulhu (x y : word) : word :=
Z_to_bv 64 (Z.shiftr (bv_unsigned x * bv_unsigned y) 64).
Definition v_mulw (x y : word) : word :=
Z_to_bv 64 (bv_swrap 32 (bv_unsigned x * bv_unsigned y)).
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
Definition v_lw (v : word) : word := Z_to_bv 64 (bv_swrap 32 (bv_unsigned v)).
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
#[using="Type"] Lemma ov_rdn : forall segs (mem : word -> option byte) n a,
ov_read_bytes segs mem a n = rdn segs mem a n.
Proof.
intros segs mem n. induction n as [|n' IH]; intro a; [reflexivity|].
simpl. unfold seg_rom.
destruct (mem a) as [b|].
- rewrite IH. reflexivity.
- destruct (memory_read segs a 1) as [[|b rest]|]; [reflexivity| rewrite IH; reflexivity | reflexivity].
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
#[using="Type"] Lemma u64_range : forall x : word, (0 <= bv_unsigned x < 2^64)%Z.
Proof. intro x. exact (bv_unsigned_in_range _ x). Qed.
#[using="Type"] Lemma u6_range : forall s : bv 6, (0 <= bv_unsigned s < 64)%Z.
Proof. intro s. exact (bv_unsigned_in_range _ s). Qed.
#[using="Type"] Lemma u5_range : forall s : bv 5, (0 <= bv_unsigned s < 32)%Z.
Proof. intro s. exact (bv_unsigned_in_range _ s). Qed.
#[using="Type"] Lemma wrap64_range : forall z, (0 <= bv_wrap 64 z < 2^64)%Z.
Proof. intro z. exact (bv_wrap_in_range 64 z). Qed.
#[using="Type"] Lemma bv_swrap_congr : forall n x y,
bv_wrap n x = bv_wrap n y -> bv_swrap n x = bv_swrap n y.
Proof.
intros n x y H. unfold bv_swrap. f_equal.
rewrite <- (bv_wrap_add_idemp_l n x), H, bv_wrap_add_idemp_l. reflexivity.
Qed.
#[using="Type"] Lemma b_addsext : forall (a : word) {n} (imm : bv n),
a + sext 64 imm = v_addi a (bv_signed imm).
Proof.
intros. apply bv_eq. unfold v_addi, sext.
rewrite bv_add_unsigned, bv_sign_extend_unsigned, Z_to_bv_unsigned.
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
End WithFP2.
Section WithFP3.
Context {fx : FPState}.
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
End WithFP3.
