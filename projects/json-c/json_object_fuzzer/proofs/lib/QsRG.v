(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Export Q6q3.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import ListNotations.
Open Scope bv_scope.

Class FPF : Type := fpF : bvmap 5 word.
Class FPC : Type := fpC : bv 32.
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Definition fp0F : FPF := bvmap_empty.
Definition fp0C : FPC := Z_to_bv 32 0.
End FPGEN1.

Ltac bvwf_has_var t := match t with context [?x] => is_var x end.
Ltac solve_BvWf_fast :=
lazymatch goal with
| |- BvWf ?n ?v =>
tryif bvwf_has_var v then fail else
tryif bvwf_has_var n then fail else
tryif has_evar v then fail else
tryif has_evar n then fail else
(vm_compute; exact I)
end.
#[global] Hint Extern 9 (BvWf _ _) => solve_BvWf_fast : typeclass_instances.

Ltac noncert_clear_all := repeat match goal with H : _ |- _ => clear H end.
Ltac noncert_goal_has_var :=
match goal with |- ?G => match G with context [?x] => is_var x end end.

Ltac lia ::=
rc_lia_prep;
tryif noncert_goal_has_var then (Qo9G.term_slim ltac:(Zify.zify; xlia zchecker))
else first [ solve [Qo9G.term_slim ltac:(noncert_clear_all; Zify.zify; xlia zchecker)]
| Qo9G.term_slim ltac:(Zify.zify; xlia zchecker) ]. Ltac mkr__lia_0 := rc_lia_prep;
tryif noncert_goal_has_var then (Qo9G.term_slim ltac:(Zify.zify; xlia zchecker))
else first [ solve [Qo9G.term_slim ltac:(noncert_clear_all; Zify.zify; xlia zchecker)]
| Qo9G.term_slim ltac:(Zify.zify; xlia zchecker) ].
Ltac nia ::=
rc_lia_prep;
tryif noncert_goal_has_var then (Qo9G.term_slim ltac:(Zify.zify; xnia zchecker))
else first [ solve [Qo9G.term_slim ltac:(noncert_clear_all; Zify.zify; xnia zchecker)]
| Qo9G.term_slim ltac:(Zify.zify; xnia zchecker) ]. Ltac mkr__nia_1 := rc_lia_prep;
tryif noncert_goal_has_var then (Qo9G.term_slim ltac:(Zify.zify; xnia zchecker))
else first [ solve [Qo9G.term_slim ltac:(noncert_clear_all; Zify.zify; xnia zchecker)]
| Qo9G.term_slim ltac:(Zify.zify; xnia zchecker) ].
Section FPGEN2.
Context {fF : FPF} {fC : FPC}.

Definition mkst (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) : machine_state :=
{| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc;
ms_svc_pending := None; ms_resv := None; ms_fcsr := fC;
ms_mem := mem; ms_rom := rom |}.

Definition getr (regs : bvmap 5 word) (r : reg) : word :=
if bv_eqb r 0 then Z_to_bv 64 0 else reg_get regs r.
Definition regupd (regs : bvmap 5 word) (r : reg) (v : word) : bvmap 5 word :=
bvmap_set r v regs.

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

#[using="Type"] Lemma arg_reg_0 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg).
Proof. apply bv_eq. reflexivity. Qed.
#[using="Type"] Lemma arg_reg_1 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg).
Proof. apply bv_eq. reflexivity. Qed.
#[using="Type"] Lemma arg_reg_2 : Z_to_bv 5 (10 + Z.of_nat 2) = (12 : reg).
Proof. apply bv_eq. reflexivity. Qed.

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
intros a b Ha Hb. split; [apply Z.land_nonneg; lia|].
apply Z_bounded_by_bits; [lia| apply Z.land_nonneg; lia |].
intros k Hk. rewrite Z.land_spec.
rewrite (Z_testbit_high 64 a k) by lia. reflexivity.
Qed.

#[using="Type"] Lemma Z_lor_range : forall a b : Z, (0 <= a < 2^64)%Z -> (0 <= b < 2^64)%Z ->
(0 <= Z.lor a b < 2^64)%Z.
Proof.
intros a b Ha Hb. split; [apply Z.lor_nonneg; lia|].
apply Z_bounded_by_bits; [lia| apply Z.lor_nonneg; lia |].
intros k Hk. rewrite Z.lor_spec.
rewrite (Z_testbit_high 64 a k) by lia.
rewrite (Z_testbit_high 64 b k) by lia.
reflexivity.
Qed.

#[using="Type"] Lemma Z_lxor_range : forall a b : Z, (0 <= a < 2^64)%Z -> (0 <= b < 2^64)%Z ->
(0 <= Z.lxor a b < 2^64)%Z.
Proof.
intros a b Ha Hb. split; [apply Z.lxor_nonneg; lia|].
apply Z_bounded_by_bits; [lia| apply Z.lxor_nonneg; lia |].
intros k Hk. rewrite Z.lxor_spec.
rewrite (Z_testbit_high 64 a k) by lia.
rewrite (Z_testbit_high 64 b k) by lia.
reflexivity.
Qed.

#[using="Type"] Lemma Z_shiftr_range : forall a k : Z, (0 <= a < 2^64)%Z -> (0 <= k)%Z ->
(0 <= Z.shiftr a k < 2^64)%Z.
Proof.
intros a k Ha Hk. rewrite Z.shiftr_div_pow2 by lia.
pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk).
split; [apply Z.div_pos; lia|].
apply Z.le_lt_trans with a; [|lia].
apply Z.div_le_upper_bound; nia.
Qed.

#[using="Type"] Lemma bv_swrap_add_idemp_l : forall n x y,
bv_swrap n (bv_wrap n x + y) = bv_swrap n (x + y).
Proof.
intros n x y. unfold bv_swrap. f_equal.
replace (bv_wrap n x + y + bv_half_modulus n)%Z
with (bv_wrap n x + (y + bv_half_modulus n))%Z by lia.
rewrite bv_wrap_add_idemp_l. f_equal. lia.
Qed.

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

Definition c_eq (x y : word) : bool := bv_eqb x y.
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

Definition v_lb (b : byte) : word := Z_to_bv 64 (bv_signed b).
Definition v_lh (v : word) : word := Z_to_bv 64 (bv_swrap 16 (bv_unsigned v)).
Definition v_lw (v : word) : word := Z_to_bv 64 (bv_swrap 32 (bv_unsigned v)).

Definition jalr_tgtZ (x : word) (imm : Z) : Z := Z.land (bv_unsigned x + imm) (-2).
Definition jalr_tgt (x : word) (imm : Z) : word := Z_to_bv 64 (jalr_tgtZ x imm).

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
rewrite (bv_wrap_small 64) by (change (bv_modulus 64) with (2^64)%Z; lia).
apply bv_wrap_small. change (bv_modulus 8) with 256%Z. lia.
Qed.

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

#[using="Type"] Lemma bytes_le_to_Z_nonneg : forall bs, (0 <= bytes_le_to_Z bs)%Z.
Proof.
induction bs as [|b bs IH]; cbn; [lia|].
apply Z.lor_nonneg. split.
- pose proof (bv_unsigned_in_range _ b). lia.
- apply Z.shiftl_nonneg. exact IH.
Qed.

#[using="Type"] Lemma bytes_le_to_Z_bound : forall bs,
(bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (length bs)))%Z.
Proof.
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
Qed.

#[using="Type"] Lemma bytes_le_app : forall xs ys,
bytes_le_to_Z (xs ++ ys) =
Z.lor (bytes_le_to_Z xs) (Z.shiftl (bytes_le_to_Z ys) (8 * Z.of_nat (length xs))).
Proof.
induction xs as [|x xs IH]; intro ys; cbn [bytes_le_to_Z app length].
- rewrite Z.mul_0_r, Z.shiftl_0_r, Z.lor_0_l. reflexivity.
- rewrite IH.
rewrite Z.shiftl_lor, Z.shiftl_shiftl by lia.
rewrite Z.lor_assoc. f_equal. f_equal. lia.
Qed.

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

#[using="Type"] Lemma ok_mkst_eq : forall (r1 r2 : bvmap 5 word) (p1 p2 : word) (m1 m2 ro : word -> option byte),
r1 = r2 -> p1 = p2 -> (forall a, m1 a = m2 a) ->
MachineOk (mkst r1 p1 m1 ro) = MachineOk (mkst r2 p2 m2 ro).
Proof.
intros r1 r2 p1 p2 m1 m2 ro Hr Hp Hm.
assert (Em : m1 = m2) by (apply functional_extensionality; exact Hm).
subst. reflexivity.
Qed.

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
replace (bv_wrap n (x + bv_half_modulus n) - bv_half_modulus n + y)%Z
with (bv_wrap n (x + bv_half_modulus n) + (y - bv_half_modulus n))%Z by lia.
rewrite bv_wrap_add_idemp_l.
f_equal. lia.
Qed.

#[using="Type"] Lemma bv_swrap_add_swrap_r : forall n x y,
bv_swrap n (x + bv_swrap n y) = bv_swrap n (x + y).
Proof.
intros n x y. rewrite Z.add_comm, bv_swrap_add_swrap_l, Z.add_comm. reflexivity.
Qed.

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
rewrite bv_sign_extend_signed by lia.
reflexivity.
Qed.

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
rewrite bv_zero_extend_unsigned by lia.
rewrite Z_to_bv_small by (change (bv_modulus 64) with (2^64)%Z; lia).
change 63%Z with (Z.ones 6).
rewrite Z.land_ones by lia.
apply Z.mod_small. change (2^6)%Z with 64%Z. apply u6_range.
Qed.

#[using="Type"] Lemma regamt64_mask : forall b : word,
bv_unsigned (bv_and b (Z_to_bv 64 63)) = (bv_unsigned b mod 64)%Z.
Proof.
intro b. rewrite bv_and_unsigned.
rewrite Z_to_bv_small by (change (bv_modulus 64) with (2^64)%Z; lia).
change 63%Z with (Z.ones 6).
rewrite Z.land_ones by lia.
reflexivity.
Qed.

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
pose proof (Z.mod_pos_bound (bv_unsigned b) 64 ltac:(lia)). lia.
Qed.

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
rewrite bv_zero_extend_unsigned by lia.
rewrite Z_to_bv_small by (change (bv_modulus 32) with (2^32)%Z; lia).
change 31%Z with (Z.ones 5).
rewrite Z.land_ones by lia.
apply Z.mod_small. change (2^5)%Z with 32%Z. apply u5_range.
Qed.

#[using="Type"] Lemma regamt32_mask : forall b : word,
bv_unsigned (bv_and (low32 b) (Z_to_bv 32 31)) = (bv_unsigned b mod 32)%Z.
Proof.
intro b. rewrite bv_and_unsigned, low32_unsigned.
rewrite Z_to_bv_small by (change (bv_modulus 32) with (2^32)%Z; lia).
change 31%Z with (Z.ones 5).
rewrite Z.land_ones by lia.
rewrite bv_wrap32_mod.
symmetry. apply Znumtheory.Zmod_div_mod; [lia|lia|].
exists (2^27)%Z. reflexivity.
Qed.

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
apply Z.mul_mod_idemp_l. lia.
Qed.

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
pose proof (Z.mod_pos_bound (bv_unsigned b) 32 ltac:(lia)).
rewrite !Z.shiftl_mul_pow2 by lia.
rewrite !bv_wrap32_mod.
apply Z.mul_mod_idemp_l. lia.
Qed.

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
replace (z + bv_half_modulus n)%Z
with ((z + bv_half_modulus n - bv_modulus n) + 1 * bv_modulus n)%Z by lia.
rewrite Z_mod_plus_full.
rewrite Z.mod_small by lia.
lia.
Qed.

#[using="Type"] Lemma b_lui : forall imm : bv 20,
sext 64 (bv_concat 32 imm (Z_to_bv 12 0)) = v_lui (Z.shiftl (bv_signed imm) 12).
Proof.
intros imm. apply bv_eq. unfold v_lui.
rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
rewrite bv_concat_unsigned by reflexivity.
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
Qed.

#[using="Type"] Lemma b_auipc : forall (p : word) (imm : bv 20),
p + sext 64 (bv_concat 32 imm (Z_to_bv 12 0)) = v_auipc p (Z.shiftl (bv_signed imm) 12).
Proof.
intros. rewrite b_lui. apply bv_eq. unfold v_lui, v_auipc.
rewrite bv_add_unsigned, !Z_to_bv_unsigned.
rewrite bv_wrap_add_idemp_r. f_equal. lia.
Qed.

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
End FPGEN2.

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
Section FPGEN3.
Context {fF : FPF} {fC : FPC}.

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
MachineOk {| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc; ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fC; ms_mem := mem; ms_rom := rom |}.
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
unfold zext. rewrite bv_zero_extend_unsigned by lia.
rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
pose proof (u8_range b). change (bv_modulus 64) with (2^64)%Z. lia. }
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
rewrite Hz, b_npc4.
destruct (is_x0 rd); cbv beta iota;
reflexivity.
Qed.

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
Qed.

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
Qed.

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

#[using="Type"] Lemma two64_pos : (0 < 2^64)%Z.
Proof. lia. Qed.

#[using="Type"] Lemma v_addi_nneg : forall x imm, (0 <= imm)%Z -> (bv_unsigned x + imm < 2^64)%Z ->
bv_unsigned (v_addi x imm) = (bv_unsigned x + imm)%Z.
Proof.
intros x imm Hi Hs. unfold v_addi.
rewrite Z_to_bv_unsigned, bv_wrap64_mod.
apply Z.mod_small. pose proof (u64_range x). lia.
Qed.

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
apply Z.mod_small. pose proof (u64_range x). pose proof (u64_range y). lia.
Qed.

#[using="Type"] Lemma v_sub_small : forall x y : word, (bv_unsigned y <= bv_unsigned x)%Z ->
bv_unsigned (v_sub x y) = (bv_unsigned x - bv_unsigned y)%Z.
Proof.
intros x y H. unfold v_sub.
rewrite Z_to_bv_unsigned, bv_wrap64_mod.
apply Z.mod_small. pose proof (u64_range x). pose proof (u64_range y). lia.
Qed.

#[using="Type"] Lemma v_slli_3 : forall x : word, (8 * bv_unsigned x < 2^64)%Z ->
bv_unsigned (v_slli x 3) = (8 * bv_unsigned x)%Z.
Proof.
intros x H8. unfold v_slli.
rewrite Z_to_bv_unsigned, bv_wrap64_mod.
rewrite Z.shiftl_mul_pow2 by lia.
change (2^3)%Z with 8%Z.
pose proof (u64_range x).
rewrite Z.mod_small by lia. lia.
Qed.

#[using="Type"] Lemma v_addi_0_1 : v_addi (Z_to_bv 64 0) 1 = Z_to_bv 64 1.
Proof. apply bv_eq. reflexivity. Qed.

#[using="Type"] Lemma v_addi_0_64 : v_addi (Z_to_bv 64 0) 64 = Z_to_bv 64 64.
Proof. apply bv_eq. reflexivity. Qed.

#[using="Type"] Lemma v_addi_Sj : forall j : nat, (Z.of_nat j + 1 < 2^64)%Z ->
v_addi (nat_to_word j) 1 = nat_to_word (S j).
Proof.
intros j _. apply bv_eq. unfold v_addi, nat_to_word.
rewrite !Z_to_bv_unsigned.
rewrite bv_wrap_add_idemp_l. f_equal. lia.
Qed.

#[using="Type"] Lemma bv_signed_small : forall x : word, (bv_unsigned x < 2^63)%Z ->
bv_signed x = bv_unsigned x.
Proof.
intros x Hx. unfold bv_signed. apply bv_swrap_small.
change (bv_half_modulus 64) with (2^63)%Z.
pose proof (u64_range x). lia.
Qed.

#[using="Type"] Lemma bv_signed_hi : forall x : word, (2^63 <= bv_unsigned x)%Z ->
bv_signed x = (bv_unsigned x - 2^64)%Z.
Proof.
intros x Hx. unfold bv_signed.
rewrite (bv_swrap_hi 64);
[ change (bv_modulus 64) with (2^64)%Z; reflexivity
| discriminate
| change (bv_half_modulus 64) with (2^63)%Z; lia
| change (bv_modulus 64) with (2^64)%Z; apply u64_range ].
Qed.

#[using="Type"] Lemma c_lts_small : forall x y : word,
(bv_unsigned x < 2^63)%Z -> (bv_unsigned y < 2^63)%Z ->
c_lts x y = bv_ltu x y.
Proof.
intros x y Hx Hy. unfold c_lts, bv_lts, bv_ltu.
rewrite !bv_signed_small by assumption. reflexivity.
Qed.

#[using="Type"] Lemma c_lts_neg_0 : forall x : word, (2^63 <= bv_unsigned x)%Z ->
c_lts x (Z_to_bv 64 0) = true.
Proof.
intros x Hx. unfold c_lts, bv_lts.
change (bv_signed (Z_to_bv 64 0)) with 0%Z.
rewrite bv_signed_hi by exact Hx.
apply Z.ltb_lt. pose proof (u64_range x). lia.
Qed.

#[using="Type"] Lemma c_lts_pos_0 : forall x : word, (bv_unsigned x < 2^63)%Z ->
c_lts x (Z_to_bv 64 0) = false.
Proof.
intros x Hx. unfold c_lts, bv_lts.
change (bv_signed (Z_to_bv 64 0)) with 0%Z.
rewrite bv_signed_small by exact Hx.
apply Z.ltb_ge. pose proof (u64_range x). lia.
Qed.

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
replace (- e)%Z with ((2^64 - e) + (-1) * 2^64)%Z by lia.
rewrite Z_mod_plus_full.
rewrite Z.mod_small by lia. lia.
Qed.

#[using="Type"] Lemma errno_ret_signed : forall e, (1 <= e)%Z -> (e <= 4095)%Z ->
bv_signed (errno_ret e) = (- e)%Z.
Proof.
intros e H1 H2.
destruct (errno_ret_range e H1 H2) as [Hlo Hhi].
rewrite bv_signed_hi by exact Hlo.
unfold errno_ret in *.
rewrite Z_to_bv_unsigned, bv_wrap64_mod in *.
replace (- e)%Z with ((2^64 - e) + (-1) * 2^64)%Z by lia.
rewrite Z_mod_plus_full.
rewrite Z.mod_small by lia. lia.
Qed.

#[using="Type"] Lemma c_lts_errno : forall e, (1 <= e)%Z -> (e <= 4095)%Z ->
c_lts (errno_ret e) (Z_to_bv 64 0) = true.
Proof.
intros e H1 H2. destruct (errno_ret_range e H1 H2) as [Hlo _].
apply c_lts_neg_0; assumption.
Qed.

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
End FPGEN3.

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
Section FPGEN4.
Context {fF : FPF} {fC : FPC}.

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
Qed.

#[using="Type"] Lemma bytes_le_N : forall k (v : word),
bytes_le_to_Z (word_to_le_bytes k v) = (bv_unsigned v mod 2^(8 * Z.of_nat k))%Z.
Proof.
intros k v. unfold word_to_le_bytes.
apply bytes_le_Z_to_le. apply u64_range.
Qed.

#[using="Type"] Lemma n_to_le_8_spec : forall v : word, word_le8 v = word_to_le_bytes 8 v.
Proof. reflexivity. Qed.

#[using="Type"] Lemma bytes_le_n_to_le_8 : forall v : word, bytes_le_to_Z (word_le8 v) = bv_unsigned v.
Proof.
intro v. rewrite n_to_le_8_spec, bytes_le_N.
change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z.
apply Z.mod_small. apply u64_range.
Qed.

#[using="Type"] Lemma nth_error_skipn_cons : forall {A} (bs : list A) d, (d < length bs)%nat ->
exists b, nth_error bs d = Some b /\ skipn d bs = b :: skipn (S d) bs.
Proof.
intros A bs. induction bs as [|x bs IH]; intros d Hd; [cbn in Hd; lia|].
destruct d as [|d'].
- exists x. split; reflexivity.
- cbn [length] in Hd. destruct (IH d' ltac:(lia)) as [b [H1 H2]].
exists b. split; [exact H1|]. cbn [skipn]. exact H2.
Qed.

#[using="Type"] Lemma u_add1 : forall a : word, (bv_unsigned a + 1 < 2^64)%Z ->
bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z.
Proof.
intros a Ha. rewrite bv_add_unsigned.
change (bv_unsigned (1 : word)) with 1%Z.
rewrite bv_wrap64_mod. apply Z.mod_small.
pose proof (u64_range a). lia.
Qed.

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
Qed.

#[using="Type"] Lemma rdn_ext : forall segs k m1 m2 (a : word),
(bv_unsigned a + Z.of_nat k <= 2^64)%Z ->
(forall x : word, (bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat k)%Z -> m1 x = m2 x) ->
rdn segs m1 a k = rdn segs m2 a k.
Proof.
intros segs k. induction k as [|k IH]; intros m1 m2 a Hnw Hext; [reflexivity|].
cbn [rdn].
rewrite (Hext a ltac:(pose proof (u64_range a); lia)).
destruct k as [|k'].
- reflexivity.
- assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
rewrite (IH m1 m2 (a+1) ltac:(lia)
ltac:(intros x Hx; apply Hext; lia)).
reflexivity.
Qed.

#[using="Type"] Lemma length_n_to_le_8 : forall v : word, length (word_le8 v) = 8%nat.
Proof. reflexivity. Qed.

#[using="Type"] Lemma length_flat_map_le8 : forall l : list word, length (flat_map word_le8 l) = (8 * length l)%nat.
Proof.
induction l as [|x l IH]; [reflexivity|].
cbn [flat_map length]. rewrite length_app, IH, length_n_to_le_8. lia.
Qed.

Definition total_arg_bytes_nat (args : list (list byte)) : nat :=
fold_right (fun a acc => length a + 1 + acc)%nat 0%nat args.

#[using="Type"] Lemma total_arg_bytes_Z : forall l,
total_arg_bytes l = Z.of_nat (total_arg_bytes_nat l).
Proof.
induction l as [|x l IH]; [reflexivity|].
cbv [total_arg_bytes total_arg_bytes_nat] in *. cbn [fold_right].
rewrite IH. lia.
Qed.

#[using="Type"] Lemma length_flatten_strings : forall l, length (flatten_strings l) = total_arg_bytes_nat l.
Proof.
induction l as [|x l IH]; [reflexivity|].
cbv [flatten_strings total_arg_bytes_nat] in *. cbn [flat_map fold_right].
rewrite length_app, IH. rewrite length_app. cbn [length]. lia.
Qed.

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
f_equal. lia.
Qed.

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
cbv [total_arg_bytes_nat]. cbn [fold_right]. f_equal. f_equal. lia.
Qed.

#[using="Type"] Lemma length_string_addrs_fst : forall strs (base : word),
length (fst (string_addrs base strs)) = length strs.
Proof.
induction strs as [|s rest IH]; intro base; [reflexivity|].
rewrite string_addrs_fst_structure. cbn [length]. rewrite IH. reflexivity.
Qed.

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
match goal with
| |- context [Z.to_nat ?pd] =>
assert (Hpd : (0 <= pd < 8)%Z) by (apply Z.mod_pos_bound; lia)
end.
unfold auxv_size. lia.
Qed.

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
Qed.

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
intros x Hx. apply stack_to_mem_image_in_block. lia.
Qed.

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
assert (Hlen : (length pre + length mid <= length (build_stack_bytes ph sp argv envp uid hwcap draw))%nat)
by (rewrite Hb, !length_app; lia).
assert (Hu : bv_unsigned (sp + nat_to_word (length pre))
= (bv_unsigned sp + Z.of_nat (length pre))%Z).
{ unfold nat_to_word. rewrite bv_add_unsigned, Z_to_bv_unsigned.
rewrite bv_wrap_add_idemp_r, bv_wrap64_mod. apply Z.mod_small. lia. }
rewrite rdn_image_in_block
by (unfold entry_block_top; rewrite Hu; lia).
exact (read_at_offset segs sp _ pre mid post k Hb Hk Hnw).
Qed.

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
rewrite firstn_length_le in H by lia.
replace (nth j s (Z_to_bv 8 0)) with b by (symmetry; apply (nth_error_nth _ _ _ Hnth)).
apply H; [|reflexivity|exact Hnw].
rewrite Hb. rewrite Hsj at 1. rewrite <- !app_assoc. reflexivity.
Qed.

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
rewrite firstn_length_le in H by lia.
replace (nth j s (Z_to_bv 8 0)) with b by (symmetry; apply (nth_error_nth _ _ _ Hnth)).
apply H; [|reflexivity|exact Hnw].
rewrite Hb. rewrite Hsj at 1. rewrite <- !app_assoc. reflexivity.
Qed.

#[using="Type"] Lemma nth_app0_bound : forall (a1 : list byte) j,
(bv_unsigned (nth j (a1 ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)) < 256)%Z.
Proof.
intros a1 j. apply u8_range.
Qed.

#[using="Type"] Lemma page_round_up_Z_le : forall z b,
(z <= b)%Z -> (b mod page_size = 0)%Z -> (page_round_up_Z z <= b)%Z.
Proof.
intros z b Hzb Hb. unfold page_round_up_Z, page_size in *.
pose proof (Z.div_mod b 4096 ltac:(lia)) as Hbm.
assert (Hq : ((z + 4096 - 1) / 4096 < b / 4096 + 1)%Z)
by (apply Z.div_lt_upper_bound; lia).
apply Z.le_trans with (m := (b / 4096 * 4096)%Z); [|lia].
apply Z.mul_le_mono_nonneg_r; lia.
Qed.

#[using="Type"] Lemma entry_page_top_within_window :
forall ph (sp : word) argv envp uid hwcap draw,
entry_stack_fits sp argv envp ->
(entry_page_top sp (build_stack_bytes ph sp argv envp uid hwcap draw)
<= sp_window_hi)%Z.
Proof.
intros ph sp argv envp uid hwcap draw Hfit.
pose proof (build_stack_bytes_within_span ph sp argv envp uid hwcap draw) as Hlen.
unfold entry_stack_fits in Hfit. unfold entry_page_top.
apply page_round_up_Z_le; [ unfold entry_block_top; lia | reflexivity ].
Qed.

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
@mkst fp0F fp0C (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp)
(Z_to_bv 64 (Z.of_N pc)) (wrap_mem ph sp argv envp uid hw rnd) (seg_rom segs).
Proof. intros. reflexivity. Qed.

#[using="Type"] Lemma wrap_above_sp : forall ph (sp : word) argv envp (x : word) uid hw rnd,
(bv_unsigned sp <= bv_unsigned x)%Z ->
wrap_mem ph sp argv envp uid hw rnd x = stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rnd) x.
Proof.
intros ph sp argv envp x uid hw rnd Hx. unfold wrap_mem.
destruct (stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rnd) x) as [b|] eqn:E; [reflexivity|].
assert (Hltf : Z.ltb (bv_unsigned x) (bv_unsigned sp) = false) by (apply Z.ltb_ge; lia).
rewrite Hltf, andb_false_r. reflexivity.
Qed.

#[using="Type"] Lemma rdn_wrap_stack_above : forall segs ph (sp : word) argv envp (a : word) n uid hw rnd,
(bv_unsigned sp <= bv_unsigned a)%Z ->
(bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
rdn segs (wrap_mem ph sp argv envp uid hw rnd) a n
= rdn segs (stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rnd)) a n.
Proof.
intros segs ph sp argv envp a n uid hw rnd Hsp Hnw.
apply rdn_ext; [exact Hnw|].
intros x Hx. apply wrap_above_sp. lia.
Qed.
End FPGEN4.

End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Fs.ReadWrite.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpox.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpox. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsV0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsV0.

Import ListNotations. Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= Stdlib.omega.PreOmega.Z.to_euclidean_division_equations.
Open Scope bv_scope.

Lemma read_aux_read_byte : forall ms k a,
read_bytes_aux (ms_read_byte ms) a k = ms_read_bytes_aux ms a k.
Proof.
intros ms. induction k as [|k IH]; intro a; [reflexivity|].
cbn [read_bytes_aux ms_read_bytes_aux].
destruct (ms_read_byte ms a) as [b|]; [rewrite IH|]; reflexivity.
Qed.

Lemma read_bytes_map_read_byte : forall ms a len,
read_bytes_map (ms_read_byte ms) a len = ms_read_bytes ms a len.
Proof. intros. rewrite read_bytes_map_eq. unfold ms_read_bytes.
apply read_aux_read_byte. Qed.

Lemma apply_effect_no_write : forall ms r,
apply_effect ms (mkEffect r [] []) = set_gpr0 ms r.
Proof.
intros ms r. unfold apply_effect, set_gpr0.
cbn [eff_ret eff_writes eff_zeros apply_zeros apply_writes].
reflexivity.
Qed.

Lemma apply_effect_copyins_no_write : forall ms r copyins,
apply_effect ms (with_copyins copyins (mkEffect r [] [])) = set_gpr0 ms r.
Proof.
intros ms r copyins. unfold with_copyins, apply_effect, set_gpr0.
cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies
apply_unmaps apply_zeros apply_copies apply_writes].
reflexivity.
Qed.

Lemma in_sysno_sys_input64 : forall segs ms x8,
in_sysno (sys_input segs ms x8) = x8.
Proof. reflexivity. Qed.
Lemma in_arg0_sys_input64 : forall segs ms x8,
in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0.
Proof. reflexivity. Qed.
Lemma in_arg1_sys_input64 : forall segs ms x8,
in_arg (sys_input segs ms x8) 1 = ms_gpr ms 1.
Proof. reflexivity. Qed.
Lemma in_arg2_sys_input64 : forall segs ms x8,
in_arg (sys_input segs ms x8) 2 = ms_gpr ms 2.
Proof. reflexivity. Qed.
Lemma in_mem_sys_input : forall segs ms x8,
in_mem (sys_input segs ms x8) = ms_read_byte ms.
Proof. reflexivity. Qed.

Lemma syscall_spec_write : forall segs ms x8 model o,
bv_unsigned x8 = 64%Z ->
(syscall_spec (sys_input segs ms x8) model o
<-> write_spec (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
(sys_input segs ms x8) model o).
Proof.
intros segs ms x8 model o Hno.
unfold syscall_spec, dispatch.
change (in_sysno (sys_input segs ms x8)) with x8.
rewrite Hno. reflexivity.
Qed.

Definition fd1chan (model : Model) : Prop :=
fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).

Definition buf_modeled (b : list byte) : Prop :=
(Z.of_nat (length b) <= rw_bytes_max)%Z.

Definition bufs_modeled (bufs : list (list byte)) : Prop :=
Forall buf_modeled bufs.

Lemma bufs_modeled_single : forall b, buf_modeled b -> bufs_modeled [b].
Proof. intros b H. apply Forall_cons; [exact H | apply Forall_nil]. Qed.

Lemma buf_modeled_nil : buf_modeled [].
Proof. unfold buf_modeled. cbn. unfold rw_bytes_max. lia. Qed.

Lemma buf_modeled_skipn : forall n (b : list byte),
buf_modeled b -> buf_modeled (skipn n b).
Proof.
intros n b H. unfold buf_modeled in *. rewrite length_skipn. lia.
Qed.

Lemma write1_check_n : forall segs ms x8 model buf n,
fd1chan model ->
bv_unsigned x8 = 64%Z ->
ms_gpr ms 0 = Z_to_bv 64 1 ->
ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
buf_modeled buf ->
(1 <= n)%nat -> (n <= length buf)%nat ->
check_write (sys_input segs ms x8)
(fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
(with_copyins [(ms_gpr ms 1, n)]
(mkEffect (len_word (firstn n buf)) [] [])) model
= CheckOk model (map (WriteEv (Z_to_bv 64 1)) (firstn n buf)).
Proof.
intros segs ms x8 model buf n Hfd Hno Hg Hr Hcnt Hn1 Hn2.
unfold fd1chan in Hfd.
assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
(ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
{ rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
pose proof (word_unsigned_range (ms_gpr ms 2)) as Hcr.
assert (Hcw : (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z)
by (unfold buf_modeled in Hcnt; lia).
assert (Hmc : negb (modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2)) = false)
by (apply rw_range_in_range; exact Hcw).
unfold check_write.
rewrite Hg; norm_fd32; rewrite Hfd.
change (w_is0 (Z_to_bv 64 1)) with false. cbv beta iota.
rewrite Hmc. cbv beta iota.
assert (Hc : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
rewrite Hc. cbv beta iota. cbv zeta.
rewrite (write_source_of_rw _ _ _ Hcw), (readable_bytes_full _ _ _ _ Hrb).
assert (Hg0 : Nat.eqb (length buf) 0 = false) by (apply Nat.eqb_neq; lia).
rewrite Hg0. cbv beta iota. unfold with_copyins; cbn.
assert (Hlenf : Z.of_nat (length (firstn n buf)) = Z.of_nat n)
by (rewrite length_firstn; lia).
assert (Hru : bv_unsigned (len_word (firstn n buf)) = Z.of_nat n).
{ rewrite (len_word_unsigned (firstn n buf));
[exact Hlenf | rewrite Hlenf; lia]. }
rewrite ?Hru.
assert (Hg1 : (1 <=? Z.of_nat n)%Z = true) by (apply Z.leb_le; lia).
assert (Hg2 : (Z.of_nat n <=? Z.of_nat (length buf))%Z = true)
by (apply Z.leb_le; lia).
rewrite ?Hg1, ?Hg2. cbn [andb].
rewrite ?Nat2Z.id, bv_eqb_refl, Nat.eqb_refl. reflexivity.
Qed.

Lemma write1_ok_n : forall segs ms x8 model buf n,
fd1chan model ->
bv_unsigned x8 = 64%Z ->
ms_gpr ms 0 = Z_to_bv 64 1 ->
ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
buf_modeled buf ->
(1 <= n)%nat -> (n <= length buf)%nat ->
syscall_spec (sys_input segs ms x8) model
(Ok (with_copyins [(ms_gpr ms 1, n)]
(mkEffect (len_word (firstn n buf)) [] [])) model
(map (WriteEv (Z_to_bv 64 1)) (firstn n buf))).
Proof.
intros segs ms x8 model buf n Hfd Hno Hg Hr Hcnt Hn1 Hn2.
apply (proj2 (syscall_spec_write _ _ _ _ _ Hno)).
apply check_write_sound_ok. apply write1_check_n; assumption.
Qed.

Lemma write1_ok_inv : forall segs ms x8 model eff model' evs buf,
fd1chan model ->
bv_unsigned x8 = 64%Z ->
ms_gpr ms 0 = Z_to_bv 64 1 ->
ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
(1 <= length buf)%nat ->
syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
exists n, (1 <= n)%nat /\ (n <= length buf)%nat /\
eff = with_copyins [(ms_gpr ms 1, n)]
(mkEffect (len_word (firstn n buf)) [] []) /\ model' = model /\
evs = map (WriteEv (Z_to_bv 64 1)) (firstn n buf).
Proof.
intros segs ms x8 model eff model' evs buf Hfd Hno Hg Hr Hnb Hspec.
unfold fd1chan in Hfd.
assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
(ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
{ rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
apply (proj1 (syscall_spec_write _ _ _ _ _ Hno)) in Hspec.
apply check_write_complete_ok in Hspec.
unfold check_write in Hspec.
rewrite Hg in Hspec; norm_fd32; rewrite Hfd in Hspec.
change (w_is0 (Z_to_bv 64 1)) with false in Hspec. cbv beta iota in Hspec.

destruct (negb (modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2)));
cbv beta iota in Hspec; [discriminate|].
assert (Hc : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
rewrite Hc in Hspec. cbv beta iota zeta in Hspec.

rewrite (write_source_prefix _ _ _ _ Hrb) in Hspec.
pose proof (rw_count_clamp_range (ms_gpr ms 2)) as Hcl.
set (c := Z.to_nat (rw_count_clamp (ms_gpr ms 2))) in *.
assert (Hcpos : (1 <= c)%nat)
by (unfold c, rw_count_clamp, MAX_RW_COUNT in *; lia).
assert (Hfl : length (firstn c buf) = Nat.min c (length buf))
by apply length_firstn.
assert (Hg0 : Nat.eqb (length (firstn c buf)) 0 = false)
by (rewrite Hfl; apply Nat.eqb_neq; lia).
rewrite Hg0 in Hspec. cbv beta iota in Hspec.
destruct eff as [ret ws zs us cs copyins]; destruct ws as [|? ?];
destruct zs as [|? ?]; destruct us as [|? ?];
destruct cs as [|? ?]; try discriminate.
destruct ((1 <=? bv_unsigned ret)%Z
&& (bv_unsigned ret <=? Z.of_nat (length (firstn c buf)))%Z) eqn:Hgr;
[|discriminate].
destruct (access_ranges_eqb copyins [(ms_gpr ms 1, Z.to_nat (bv_unsigned ret))])
eqn:Hreads; [|discriminate].
inversion Hspec; clear Hspec; subst.
apply andb_true_iff in Hgr as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2.
rewrite Hfl in H2.
apply access_ranges_eqb_eq in Hreads. subst copyins.
exists (Z.to_nat (bv_unsigned ret)).
assert (Hff : firstn (Z.to_nat (bv_unsigned ret)) (firstn c buf)
= firstn (Z.to_nat (bv_unsigned ret)) buf)
by (rewrite firstn_firstn; f_equal; lia).
rewrite Hff.
assert (Hlw : len_word (firstn (Z.to_nat (bv_unsigned ret)) buf) = ret)
by (apply len_word_firstn_ret; lia).
rewrite Hlw. repeat split; try reflexivity; lia.
Qed.

Lemma write1_no_unmodeled : forall segs ms x8 model buf,
fd1chan model ->
bv_unsigned x8 = 64%Z ->
ms_gpr ms 0 = Z_to_bv 64 1 ->
ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
buf_modeled buf ->

(1 <= length buf)%nat ->
~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
intros segs ms x8 model buf Hfd Hno Hg Hr Hcnt Hnb Hspec.
unfold fd1chan in Hfd.
assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
(ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
{ rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
assert (Hcw : (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z)
by (unfold buf_modeled in Hcnt; lia).
assert (Hmc : negb (modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2)) = false)
by (apply rw_range_in_range; exact Hcw).
apply (proj1 (syscall_spec_write _ _ _ _ _ Hno)) in Hspec.
apply (check_write_complete_unmodeled _ _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
in Hspec.
unfold check_write in Hspec.
rewrite Hg in Hspec; norm_fd32; rewrite Hfd in Hspec.
change (w_is0 (Z_to_bv 64 1)) with false in Hspec. cbv beta iota in Hspec.
rewrite Hmc in Hspec. cbv beta iota in Hspec.
destruct (w_is0 (ms_gpr ms 2)) eqn:Hc; try rewrite Hc in Hspec.
{ exfalso.
assert (Hc0 : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
congruence. }
rewrite (write_source_of_rw _ _ _ Hcw), (readable_bytes_full _ _ _ _ Hrb)
in Hspec.
destruct (length buf =? 0)%nat eqn:Hz; try rewrite Hz in Hspec.
{ now apply check_ret_only_no_unmodeled in Hspec. }
discriminate Hspec.
Qed.

Lemma is_prefix_app_mono {A} : forall (l a b : list A),
is_prefix a b -> is_prefix (l ++ a) (l ++ b).
Proof.
induction l as [|x l IH]; intros a b H; cbn; [exact H | split; [reflexivity | apply IH; exact H]].
Qed.

Fixpoint wevents_ch (ch : word) (bufs : list (list byte)) : list event :=
match bufs with
| [] => []
| buf :: rest => map (WriteEv ch) buf ++ wevents_ch ch rest
end.

Inductive wpick (ch : word) : list (list byte) -> list event -> Prop :=
| wp_nil : wpick ch [] []
| wp_cons : forall buf bufs n tr,
(1 <= n)%nat -> (n <= length buf)%nat ->
wpick ch bufs tr ->
wpick ch (buf :: bufs) (map (WriteEv ch) (firstn n buf) ++ tr).

Lemma wpick_wevents : forall ch bufs,
Forall (fun b => (1 <= length b)%nat) bufs ->
wpick ch bufs (wevents_ch ch bufs).
Proof.
intros ch bufs H; induction H as [|b bs Hb Hbs IH].
- apply wp_nil.
- cbn [wevents_ch].
pose proof (wp_cons ch b bs (length b) _ Hb (Nat.le_refl _) IH) as Hc.
rewrite firstn_all in Hc. exact Hc.
Qed.

Section WithSegs.
Variable segs : list Segment.

Inductive to_wexit : machine_state -> list (list byte) -> word -> Prop :=
| tw_exit : forall ms x8,
ms_svc_pending ms = Some x8 ->
is_exit_no x8 ->
to_wexit ms [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
| tw_write : forall ms x8 buf bufs code,
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 64%Z ->
ms_gpr ms 0 = Z_to_bv 64 1 ->
ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
(1 <= length buf)%nat ->
(forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
to_wexit (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) bufs code) ->
to_wexit ms (buf :: bufs) code
| tw_step : forall ms ms' bufs code,
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
to_wexit ms' bufs code ->
to_wexit ms bufs code.

Inductive msteps : machine_state -> machine_state -> Prop :=
| mst_refl : forall ms, msteps ms ms
| mst_step : forall ms ms' ms'',
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
msteps ms' ms'' ->
msteps ms ms''.

#[using="Type"] Lemma msteps_one : forall ms ms',
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
msteps ms ms'.
Proof. intros ms ms' Hsvc Hstep. eapply mst_step; [exact Hsvc | exact Hstep | apply mst_refl]. Qed.

#[using="Type"] Lemma msteps_trans : forall ms ms' ms'',
msteps ms ms' -> msteps ms' ms'' -> msteps ms ms''.
Proof.
intros ms ms' ms'' H; induction H; [auto|].
intro H2. eapply mst_step; eauto.
Qed.

#[using="Type"] Lemma msteps_to_wexit : forall ms ms' bufs code,
msteps ms ms' -> to_wexit ms' bufs code -> to_wexit ms bufs code.
Proof.
intros ms ms' bufs code H; induction H; [auto|].
intro Hw. eapply tw_step; eauto.
Qed.

#[using="Type"] Lemma to_wexit_bufs_nonempty : forall ms bufs code,
to_wexit ms bufs code ->
Forall (fun b => (1 <= length b)%nat) bufs.
Proof.
intros ms bufs code H;
induction H as
[ms x8 Hsvc Hx8
| ms x8 buf bufs code Hsvc Hno Hg Hr Hnb Hcont IH
| ms ms' bufs code Hsvc Hstep Hte IH].
- constructor.
- constructor; [exact Hnb | apply (IH (length buf)); lia].
- exact IH.
Qed.

#[using="Type"] Lemma sstep_write_next_inv : forall ms model x8 buf evs c',
m_halted model = None ->
m_vm_lazy model = [] ->
fd1chan model ->
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 64%Z ->
ms_gpr ms 0 = Z_to_bv 64 1 ->
ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
(1 <= length buf)%nat ->
sstep segs (mkCfg ms model) evs (SNext c') ->
exists n, (1 <= n)%nat /\ (n <= length buf)%nat /\
evs = map (WriteEv (Z_to_bv 64 1)) (firstn n buf) /\
c' = mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model.
Proof.
intros ms model x8 buf evs c' Hh Hlazy Hfd Hsvc Hno Hg Hr Hnb Hss.
inversion Hss; subst; try congruence.
-
match goal with
| H2 : ms_svc_pending ms = Some ?x, H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf Hfd Hno Hg Hr Hnb H3)
as (n & Hn1 & Hn2 & Heff & Hm & Hevs);
subst eff model' evs0; exists n
end.
match goal with
| Hmat : materialize_model_accesses model _ = Some ?model'' |- _ =>
rewrite (materialize_model_accesses_no_lazy model _ Hlazy) in Hmat;
inversion Hmat; subst model''
end.
rewrite apply_effect_copyins_no_write. repeat split; auto.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_halted ?model' = Some ?code |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf Hfd Hno Hg Hr Hnb H3)
as (n & _ & _ & _ & Hm & _);
subst model'; rewrite Hh in H6; discriminate
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_killed ?model' = Some ?sig |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf Hfd Hno Hg Hr Hnb H3)
as (n & _ & _ & _ & Hm & _);
subst model'; rewrite (m_killed_of_m_halted_none model Hh) in H6;
discriminate
end.
Qed.

#[using="Type"] Lemma sstep_write_inv : forall ms model x8 buf evs st,
m_halted model = None ->
m_vm_lazy model = [] ->
fd1chan model ->
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 64%Z ->
ms_gpr ms 0 = Z_to_bv 64 1 ->
ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
buf_modeled buf ->
(1 <= length buf)%nat ->
sstep segs (mkCfg ms model) evs st ->
exists n, (1 <= n)%nat /\ (n <= length buf)%nat /\
evs = map (WriteEv (Z_to_bv 64 1)) (firstn n buf) /\
st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model).
Proof.
intros ms model x8 buf evs st Hh Hlazy Hfd Hsvc Hno Hg Hr Hcnt Hnb Hss.
destruct st as [c'|].
- destruct (sstep_write_next_inv ms model x8 buf evs c'
Hh Hlazy Hfd Hsvc Hno Hg Hr Hnb Hss) as (n & Hn1 & Hn2 & Hevs & Hc').
exists n. repeat split; [exact Hn1 | exact Hn2 | exact Hevs | now rewrite Hc'].
-
exfalso. inversion Hss; subst; try congruence.
+ match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
Hmat : materialize_model_accesses ?model' _ = None |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf
Hfd Hno Hg Hr Hnb H3)
as (n & _ & _ & _ & Hm & _);
subst model'; rewrite (materialize_model_accesses_no_lazy model _ Hlazy) in Hmat;
discriminate
end.
+ match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
assert (Hx : x = x8) by congruence; subst x;
apply (write1_no_unmodeled segs ms x8 model buf Hfd Hno Hg Hr Hcnt Hnb H3)
end.
Qed.

Fixpoint wevents (bufs : list (list byte)) : list event :=
match bufs with
| [] => []
| buf :: rest => map (WriteEv (Z_to_bv 64 1)) buf ++ wevents rest
end.

Definition wexit_post (bufs : list (list byte)) (code : word) (fs : Fs.Fs) : post :=
fun tr o =>
(exists full, wpick (Z_to_bv 64 1) bufs full /\ tr = full ++ [ExitEv code fs])
/\ exits_with code tr o.

#[using="Type"] Lemma to_wexit_exec : forall ms bufs code,
to_wexit ms bufs code ->
forall model,
m_halted model = None ->
m_vm_lazy model = [] ->
fd1chan model ->
bufs_modeled bufs ->
OmniRun.exec segs (mkCfg ms model) (wexit_post bufs code (m_fs model)).
Proof.
intros ms bufs code Hte.
induction Hte as
[ms x8 Hsvc Hx8
| ms x8 buf bufs code Hsvc Hno Hg Hr Hnb Hcont IH
| ms ms' bufs code Hsvc Hstep Hte IH];
intros model Hh Hlazy Hfd Hbm.
-
apply (exec_step_only segs _ _
[ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
(mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))).
+ replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
(m_fs (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
by (cbn; reflexivity).
apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
(with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
(bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
* exact Hh.
* exact Hsvc.
* apply (exit_dispatch_ok (sys_input segs ms x8) model).
rewrite in_sysno_sys_input. exact Hx8.
* cbn. reflexivity.
* apply m_killed_with_halted.
+ intros evs st Hss. exact (sstep_exit_inv segs ms model x8 evs st Hh Hsvc Hx8 Hss).
+ apply exec_halt.
* cbn. rewrite m_halted_with_halted. discriminate.
* unfold wexit_post. cbn beta. rewrite app_nil_r. split.
-- exists []. split; [apply wp_nil | reflexivity].
-- cbn [exits_with cfg_model]. split;
[ rewrite m_halted_with_halted; reflexivity
| apply m_killed_with_halted ].
-
apply Forall_cons_iff in Hbm as [Hb Hbs].
apply exec_step; [exact Hh | | |].
+
eexists; eexists.
apply (sstep_syscall segs ms model x8
(with_copyins [(ms_gpr ms 1, length buf)]
(mkEffect (len_word (firstn (length buf) buf)) [] [])) model model
(map (WriteEv (Z_to_bv 64 1)) (firstn (length buf) buf))).
* exact Hh.
* exact Hsvc.
* apply write1_ok_n; try assumption. apply Nat.le_refl.
* exact Hh.
* rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity.
+ intros evs Hss.
destruct (sstep_write_inv ms model x8 buf evs SError
Hh Hlazy Hfd Hsvc Hno Hg Hr Hb Hnb Hss) as (n & _ & _ & _ & Habs).
discriminate Habs.
+ intros evs c' Hss.
destruct (sstep_write_inv ms model x8 buf evs (SNext c')
Hh Hlazy Hfd Hsvc Hno Hg Hr Hb Hnb Hss) as (n & Hn1 & Hn2 & -> & Hc').
injection Hc' as ->.
eapply exec_conseq; [exact (IH n Hn1 Hn2 model Hh Hlazy Hfd Hbs) |].
intros tr o ((full & Hpick & ->) & Hx). split.
* exists (map (WriteEv (Z_to_bv 64 1)) (firstn n buf) ++ full).
split; [apply wp_cons; assumption | apply app_assoc].
* exact Hx.
-
apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
+ apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
+ intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
+ eapply exec_conseq; [exact (IH model Hh Hlazy Hfd Hbm) |].
intros tr o H. cbn [app]. exact H.
Qed.

#[using="Type"] Lemma to_wexit_star_admits : forall ms bufs code,
to_wexit ms bufs code ->
forall model full,
m_halted model = None ->
m_vm_lazy model = [] ->
fd1chan model ->
bufs_modeled bufs ->
wpick (Z_to_bv 64 1) bufs full ->
exists c, star segs (mkCfg ms model) (full ++ [ExitEv code (m_fs model)]) c.
Proof.
intros ms bufs code Hte.
induction Hte as
[ms x8 Hsvc Hx8
| ms x8 buf bufs code Hsvc Hno Hg Hr Hnb Hcont IH
| ms ms' bufs code Hsvc Hstep Hte IH];
intros model full Hh Hlazy Hfd Hbm Hpick.
-
inversion Hpick; subst. cbn [app].
exists (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model)).
apply star_one.
replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
(m_fs (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
by (cbn; reflexivity).
apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
(with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
(bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
+ exact Hh.
+ exact Hsvc.
+ apply (exit_dispatch_ok (sys_input segs ms x8) model).
rewrite in_sysno_sys_input. exact Hx8.
+ cbn. reflexivity.
+ apply m_killed_with_halted.
-
apply Forall_cons_iff in Hbm as [Hb Hbs].
inversion Hpick as [|buf' bufs' n tr Hn1 Hn2 Hpick']; subst.
destruct (IH n Hn1 Hn2 model tr Hh Hlazy Hfd Hbs Hpick') as [c Hstar].
exists c. rewrite <- app_assoc.
eapply star_step; [| exact Hstar].
rewrite <- (apply_effect_copyins_no_write ms
(len_word (firstn n buf)) [(ms_gpr ms 1, n)]).
apply (sstep_syscall segs ms model x8
(with_copyins [(ms_gpr ms 1, n)]
(mkEffect (len_word (firstn n buf)) [] [])) model model
(map (WriteEv (Z_to_bv 64 1)) (firstn n buf))).
+ exact Hh.
+ exact Hsvc.
+ apply write1_ok_n; assumption.
+ exact Hh.
+ rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity.
-
destruct (IH model full Hh Hlazy Hfd Hbm Hpick) as [c Hstar].
exists c.
replace (full ++ [ExitEv code (m_fs model)])
with ([] ++ (full ++ [ExitEv code (m_fs model)])) by reflexivity.
eapply star_step; [| exact Hstar].
apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

#[using="Type"] Lemma to_wexit_star_only : forall ms bufs code,
to_wexit ms bufs code ->
forall model,
m_halted model = None ->
m_vm_lazy model = [] ->
fd1chan model ->
bufs_modeled bufs ->
forall tr c, star segs (mkCfg ms model) tr c ->
exists full, wpick (Z_to_bv 64 1) bufs full /\
is_prefix tr (full ++ [ExitEv code (m_fs model)]).
Proof.
intros ms bufs code Hte model Hh Hlazy Hfd Hbm tr c Hstar.
destruct (exec_realizes _ _ _
(exec_star _ _ _ _ _ (to_wexit_exec ms bufs code Hte model Hh Hlazy Hfd Hbm) Hstar))
as (tr' & o & _ & HQ).
unfold wexit_post in HQ. cbn beta in HQ. destruct HQ as ((full & Hpick & Heq) & _).
exists full. split; [exact Hpick |]. rewrite <- Heq. apply is_prefix_app.
Qed.

#[using="Type"] Lemma to_wexit_no_error : forall ms model bufs code,
m_halted model = None ->
m_vm_lazy model = [] ->
fd1chan model ->
to_wexit ms bufs code ->
bufs_modeled bufs ->
~ reaches_error segs (mkCfg ms model).
Proof.
intros ms model bufs code Hh Hlazy Hfd Hte Hbm. apply exec_no_error.
eapply exec_conseq; [exact (to_wexit_exec ms bufs code Hte model Hh Hlazy Hfd Hbm) |].
intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

End WithSegs.

Lemma init_model_fd1chan : forall reserved brk0 mb sp lim inp,
fd1chan (init_model reserved brk0 mb sp lim inp).
Proof. reflexivity. Qed.

Lemma cat_omni_run_te : forall segs pc ph sp brk0 mb rnd lim inp bufs code,
to_wexit segs (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) bufs code ->
bufs_modeled bufs ->
omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp
(wexit_post bufs code (in_fs inp)).
Proof.
intros segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm.
cbn [omni_run]. unfold init_config.
exact (to_wexit_exec segs _ bufs code Hte
(init_model (segments_reserved segs) brk0 mb sp lim inp)
eq_refl eq_refl eq_refl Hbm).
Qed.

Lemma cat_obs_iff_te : forall segs pc ph sp brk0 mb rnd lim inp bufs code,
to_wexit segs (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) bufs code ->
bufs_modeled bufs ->
forall tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr
<-> exists full, wpick (Z_to_bv 64 1) bufs full /\
is_prefix tr (full ++ [ExitEv code (in_fs inp)]).
Proof.
intros segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm tr.
set (fs0 := in_fs inp) in *.
unfold init_config in *.
set (ms := init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) in *.
assert (Hh : m_halted (init_model (segments_reserved segs) brk0 mb sp lim inp) = None) by reflexivity.
assert (Hlazy : m_vm_lazy (init_model (segments_reserved segs) brk0 mb sp lim inp) = []) by reflexivity.
assert (Hfd : fd1chan (init_model (segments_reserved segs) brk0 mb sp lim inp)) by reflexivity.
assert (Hfs : m_fs (init_model (segments_reserved segs) brk0 mb sp lim inp) = fs0) by reflexivity.
split.
- intros (tr' & c & Hstar & Hp).
destruct (to_wexit_star_only segs ms bufs code Hte _ Hh Hlazy Hfd Hbm tr' c Hstar)
as (full & Hw & Hpref).
rewrite Hfs in Hpref.
exists full. split; [exact Hw|].
eapply is_prefix_trans; eauto.
- intros (full & Hw & Hp).
destruct (to_wexit_star_admits segs ms bufs code Hte _ full Hh Hlazy Hfd Hbm Hw)
as [c Hstar].
rewrite Hfs in Hstar.
exists (full ++ [ExitEv code fs0]), c. split; assumption.
Qed.

Lemma cat_no_error_run_te : forall segs pc ph sp brk0 mb rnd lim inp bufs code,
to_wexit segs (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) bufs code ->
bufs_modeled bufs ->
~ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp).
Proof.
intros segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm. apply exec_no_error.
eapply exec_conseq; [exact (cat_omni_run_te segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm) |].
intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

Lemma cat_must_exit_with_te : forall segs pc ph sp brk0 mb rnd lim inp bufs code,
to_wexit segs (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) bufs code ->
bufs_modeled bufs ->
must_exit_with code (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp.
Proof.
intros segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm. apply must_exit_with_iff.
eapply exec_conseq; [exact (cat_omni_run_te segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm) |].
intros tr o (_ & Hx). exact Hx.
Qed.

Lemma cat_omni_run_te_code_unique : forall segs pc ph sp brk0 mb rnd lim inp bufs code code',
to_wexit segs (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) bufs code ->
bufs_modeled bufs ->
omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp (exits_with code') ->
code' = code.
Proof.
intros segs pc ph sp brk0 mb rnd lim inp bufs code code' Hte Hbm Hex.
pose proof (cat_omni_run_te segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm) as Hrun.
cbn [omni_run] in Hrun, Hex.
destruct (exec_realizes _ _ _ Hrun) as (tr & [c' | c'] & Hm & _ & Hx); [| destruct Hx].
pose proof (exec_sound _ _ _ Hex _ _ Hm) as Hx'.
cbn [exits_with] in Hx, Hx'. destruct Hx as (Hx & _). destruct Hx' as (Hx' & _).
rewrite Hx in Hx'. injection Hx' as Hx'. symmetry. exact Hx'.
Qed.

Lemma cat_omni_strong_equiv_te :
forall source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bufs code inp,
to_wexit source_segs (init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) bufs code ->
to_wexit target_segs (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) bufs code ->
bufs_modeled bufs ->
omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
(mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bufs code inp
Hsource Htarget Hbm.
split.
{ cbn [img_segments].
eapply coexec_conseq;
[apply exec_coexec;
exact (cat_omni_run_te source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bufs code Hsource Hbm) |].
intros tr o (_ & Hx).
exact (never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)). }
right. split.
- apply trace_equiv_iff_omni. intro tr. cbn.
rewrite (cat_obs_iff_te source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bufs code Hsource Hbm tr).
rewrite (cat_obs_iff_te target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code Htarget Hbm tr).
reflexivity.
- apply bh_errors_iff. cbn.
apply (cat_no_error_run_te target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code Htarget Hbm).
Qed.

Lemma cat_strong_equiv_te :
forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bufs code inp,
to_wexit source_segs (init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) bufs code ->
to_wexit target_segs (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) bufs code ->
bufs_modeled bufs ->
Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
/\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
(run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bufs code inp Hsource Htarget Hbm.
split.
{ apply no_error_run_modeled.
apply (cat_no_error_run_te source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code Hsource Hbm). }
right. split.
- intro tr. cbn.
rewrite (cat_obs_iff_te source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code Hsource Hbm tr).
rewrite (cat_obs_iff_te target_segs apc aph asp abrk amb arnd alim inp bufs code Htarget Hbm tr).
reflexivity.
- cbn. apply (cat_no_error_run_te target_segs apc aph asp abrk amb arnd alim inp bufs code Htarget Hbm).
Qed.

Definition fdchan (fd ch : word) (model : Model) : Prop :=
fd_lookup (m_fds model) fd = Some (FdChannel ch) /\ w_is0 ch = false.

Lemma fd1chan_fdchan : forall model,
fd1chan model -> fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model.
Proof.
intros model H. split; [exact H | reflexivity].
Qed.

Lemma init_model_fdchan2 : forall reserved brk0 mb sp lim inp,
fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) (init_model reserved brk0 mb sp lim inp).
Proof. intros. split; reflexivity. Qed.

Lemma write_ch_check_n : forall segs ms x8 model fd ch buf n,
fdchan fd ch model ->
fd32 fd = fd ->
bv_unsigned x8 = 64%Z ->
ms_gpr ms 0 = fd ->
ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
buf_modeled buf ->
(1 <= n)%nat -> (n <= length buf)%nat ->
check_write (sys_input segs ms x8)
(fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
(with_copyins [(ms_gpr ms 1, n)]
(mkEffect (len_word (firstn n buf)) [] [])) model
= CheckOk model (map (WriteEv ch) (firstn n buf)).
Proof.
intros segs ms x8 model fd ch buf n [Hfd Hch] H32 Hno Hg Hr Hcnt Hn1 Hn2.
assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
(ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
{ rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
pose proof (word_unsigned_range (ms_gpr ms 2)) as Hcr.
assert (Hcw : (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z)
by (unfold buf_modeled in Hcnt; lia).
assert (Hmc : negb (modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2)) = false)
by (apply rw_range_in_range; exact Hcw).
unfold check_write.
rewrite Hg, H32, Hfd, Hch. cbv beta iota.
rewrite Hmc. cbv beta iota.
assert (Hc : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
rewrite Hc. cbv beta iota. cbv zeta.
rewrite (write_source_of_rw _ _ _ Hcw), (readable_bytes_full _ _ _ _ Hrb).
assert (Hg0 : Nat.eqb (length buf) 0 = false) by (apply Nat.eqb_neq; lia).
rewrite Hg0. cbv beta iota. unfold with_copyins; cbn.
assert (Hlenf : Z.of_nat (length (firstn n buf)) = Z.of_nat n)
by (rewrite length_firstn; lia).
assert (Hru : bv_unsigned (len_word (firstn n buf)) = Z.of_nat n).
{ rewrite (len_word_unsigned (firstn n buf));
[exact Hlenf | rewrite Hlenf; lia]. }
rewrite ?Hru.
assert (Hg1 : (1 <=? Z.of_nat n)%Z = true) by (apply Z.leb_le; lia).
assert (Hg2 : (Z.of_nat n <=? Z.of_nat (length buf))%Z = true)
by (apply Z.leb_le; lia).
rewrite ?Hg1, ?Hg2. cbn [andb].
rewrite ?Nat2Z.id, bv_eqb_refl, Nat.eqb_refl. reflexivity.
Qed.

Lemma write_ch_ok_n : forall segs ms x8 model fd ch buf n,
fdchan fd ch model -> fd32 fd = fd ->
bv_unsigned x8 = 64%Z ->
ms_gpr ms 0 = fd ->
ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
buf_modeled buf ->
(1 <= n)%nat -> (n <= length buf)%nat ->
syscall_spec (sys_input segs ms x8) model
(Ok (with_copyins [(ms_gpr ms 1, n)]
(mkEffect (len_word (firstn n buf)) [] [])) model
(map (WriteEv ch) (firstn n buf))).
Proof.
intros segs ms x8 model fd ch buf n Hfdc H32 Hno Hg Hr Hcnt Hn1 Hn2.
apply (proj2 (syscall_spec_write _ _ _ _ _ Hno)).
apply check_write_sound_ok. eapply write_ch_check_n; eassumption.
Qed.

Lemma write_ch_ok_inv : forall segs ms x8 model fd ch eff model' evs buf,
fdchan fd ch model -> fd32 fd = fd ->
bv_unsigned x8 = 64%Z ->
ms_gpr ms 0 = fd ->
ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
(1 <= length buf)%nat ->
syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
exists n, (1 <= n)%nat /\ (n <= length buf)%nat /\
eff = with_copyins [(ms_gpr ms 1, n)]
(mkEffect (len_word (firstn n buf)) [] []) /\ model' = model /\
evs = map (WriteEv ch) (firstn n buf).
Proof.
intros segs ms x8 model fd ch eff model' evs buf Hfdc H32 Hno Hg Hr Hnb Hspec.
destruct Hfdc as [Hfd Hch].
assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
(ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
{ rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
apply (proj1 (syscall_spec_write _ _ _ _ _ Hno)) in Hspec.
apply check_write_complete_ok in Hspec.
unfold check_write in Hspec.
rewrite Hg, H32, Hfd, Hch in Hspec. cbv beta iota in Hspec.

destruct (negb (modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2)));
cbv beta iota in Hspec; [discriminate|].
assert (Hc : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
rewrite Hc in Hspec. cbv beta iota zeta in Hspec.

rewrite (write_source_prefix _ _ _ _ Hrb) in Hspec.
pose proof (rw_count_clamp_range (ms_gpr ms 2)) as Hcl.
set (c := Z.to_nat (rw_count_clamp (ms_gpr ms 2))) in *.
assert (Hcpos : (1 <= c)%nat)
by (unfold c, rw_count_clamp, MAX_RW_COUNT in *; lia).
assert (Hfl : length (firstn c buf) = Nat.min c (length buf))
by apply length_firstn.
assert (Hg0 : Nat.eqb (length (firstn c buf)) 0 = false)
by (rewrite Hfl; apply Nat.eqb_neq; lia).
rewrite Hg0 in Hspec. cbv beta iota in Hspec.
destruct eff as [ret ws zs us cs copyins]; destruct ws as [|? ?];
destruct zs as [|? ?]; destruct us as [|? ?];
destruct cs as [|? ?]; try discriminate.
destruct ((1 <=? bv_unsigned ret)%Z
&& (bv_unsigned ret <=? Z.of_nat (length (firstn c buf)))%Z) eqn:Hgr;
[|discriminate].
destruct (access_ranges_eqb copyins [(ms_gpr ms 1, Z.to_nat (bv_unsigned ret))])
eqn:Hreads; [|discriminate].
inversion Hspec; clear Hspec; subst.
apply andb_true_iff in Hgr as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2.
rewrite Hfl in H2.
apply access_ranges_eqb_eq in Hreads. subst copyins.
exists (Z.to_nat (bv_unsigned ret)).
assert (Hff : firstn (Z.to_nat (bv_unsigned ret)) (firstn c buf)
= firstn (Z.to_nat (bv_unsigned ret)) buf)
by (rewrite firstn_firstn; f_equal; lia).
rewrite Hff.
assert (Hlw : len_word (firstn (Z.to_nat (bv_unsigned ret)) buf) = ret)
by (apply len_word_firstn_ret; lia).
rewrite Hlw. repeat split; try reflexivity; lia.
Qed.

Lemma write_ch_no_unmodeled : forall segs ms x8 model fd ch buf,
fdchan fd ch model -> fd32 fd = fd ->
bv_unsigned x8 = 64%Z ->
ms_gpr ms 0 = fd ->
ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
buf_modeled buf ->

(1 <= length buf)%nat ->
~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
intros segs ms x8 model fd ch buf [Hfd Hch] H32 Hno Hg Hr Hcnt Hnb Hspec.
assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
(ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
{ rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
assert (Hcw : (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z)
by (unfold buf_modeled in Hcnt; lia).
assert (Hmc : negb (modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2)) = false)
by (apply rw_range_in_range; exact Hcw).
apply (proj1 (syscall_spec_write _ _ _ _ _ Hno)) in Hspec.
apply (check_write_complete_unmodeled _ _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
in Hspec.
unfold check_write in Hspec.
rewrite Hg, H32, Hfd, Hch in Hspec. cbv beta iota in Hspec.
rewrite Hmc in Hspec. cbv beta iota in Hspec.
destruct (w_is0 (ms_gpr ms 2)) eqn:Hc; try rewrite Hc in Hspec.
{ exfalso.
assert (Hc0 : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
congruence. }
rewrite (write_source_of_rw _ _ _ Hcw), (readable_bytes_full _ _ _ _ Hrb)
in Hspec.
destruct (length buf =? 0)%nat eqn:Hz; try rewrite Hz in Hspec.
{ now apply check_ret_only_no_unmodeled in Hspec. }
discriminate Hspec.
Qed.

Section WithSegsCh.
Variable segs : list Segment.
Variable fd ch : word.

Inductive to_wexit_ch : machine_state -> list (list byte) -> word -> Prop :=
| twc_exit : forall ms x8,
ms_svc_pending ms = Some x8 ->
is_exit_no x8 ->
to_wexit_ch ms [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
| twc_write : forall ms x8 buf bufs code,
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 64%Z ->
ms_gpr ms 0 = fd ->
ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
(1 <= length buf)%nat ->
(forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
to_wexit_ch (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) bufs code) ->
to_wexit_ch ms (buf :: bufs) code
| twc_step : forall ms ms' bufs code,
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
to_wexit_ch ms' bufs code ->
to_wexit_ch ms bufs code.

#[using="Type"] Lemma msteps_to_wexit_ch : forall ms ms' bufs code,
msteps segs ms ms' -> to_wexit_ch ms' bufs code -> to_wexit_ch ms bufs code.
Proof.
intros ms ms' bufs code H; induction H; [auto|].
intro Hw. eapply twc_step; eauto.
Qed.

Hypothesis Hfd32 : fd32 fd = fd.

#[using="Hfd32"] Lemma sstep_write_ch_inv : forall ms model x8 buf evs st,
m_halted model = None ->
m_vm_lazy model = [] ->
fdchan fd ch model ->
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 64%Z ->
ms_gpr ms 0 = fd ->
ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
buf_modeled buf ->
(1 <= length buf)%nat ->
sstep segs (mkCfg ms model) evs st ->
exists n, (1 <= n)%nat /\ (n <= length buf)%nat /\
evs = map (WriteEv ch) (firstn n buf) /\
st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model).
Proof.
intros ms model x8 buf evs st Hh Hlazy Hfdc Hsvc Hno Hg Hr Hcnt Hnb Hss.
revert Hg Hfdc. inversion Hss; subst; intros Hg Hfdc; try congruence.
- match goal with
| H2 : ms_svc_pending ms = Some ?x, H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (write_ch_ok_inv segs ms x8 model fd ch eff model' evs0 buf Hfdc Hfd32 Hno Hg Hr Hnb H3)
as (n & Hn1 & Hn2 & Heff & Hm & Hevs);
subst eff model' evs0; exists n
end.
match goal with
| Hmat : materialize_model_accesses model _ = Some ?model'' |- _ =>
rewrite (materialize_model_accesses_no_lazy model _ Hlazy) in Hmat;
inversion Hmat; subst model''
end.
rewrite apply_effect_copyins_no_write. repeat split; auto.
- exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
Hmat : materialize_model_accesses ?model' _ = None |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (write_ch_ok_inv segs ms x8 model fd ch eff model' evs0 buf
Hfdc Hfd32 Hno Hg Hr Hnb H3)
as (n & _ & _ & _ & Hm & _);
subst model'; rewrite (materialize_model_accesses_no_lazy model _ Hlazy) in Hmat;
discriminate
end.
- exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_halted ?model' = Some ?code |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (write_ch_ok_inv segs ms x8 model fd ch eff model' evs0 buf Hfdc Hfd32 Hno Hg Hr Hnb H3)
as (n & _ & _ & _ & Hm & _);
subst model'; rewrite Hh in H6; discriminate
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_killed ?model' = Some ?sig |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (write_ch_ok_inv segs ms x8 model fd ch eff model' evs0 buf Hfdc Hfd32 Hno Hg Hr Hnb H3)
as (n & _ & _ & _ & Hm & _);
subst model'; rewrite (m_killed_of_m_halted_none model Hh) in H6;
discriminate
end.
- exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x, H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
assert (Hx : x = x8) by congruence; subst x;
apply (write_ch_no_unmodeled segs ms x8 model fd ch buf Hfdc Hfd32 Hno Hg Hr Hcnt Hnb H3)
end.
Qed.

End WithSegsCh.

Lemma to_wexit_ch_1 : forall segs ms bufs code,
to_wexit segs ms bufs code ->
to_wexit_ch segs (Z_to_bv 64 1) ms bufs code.
Proof.
intros segs ms bufs code H; induction H.
- eapply twc_exit; eassumption.
- eapply twc_write; eassumption.
- eapply twc_step; eassumption.
Qed.

Lemma wevents_ch_1 : forall bufs, wevents_ch (Z_to_bv 64 1) bufs = wevents bufs.
Proof.
induction bufs as [|b bs IH]; cbn [wevents_ch wevents]; [reflexivity|].
rewrite IH. reflexivity.
Qed.
