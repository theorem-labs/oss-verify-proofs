(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Q5Rg Lib.SepCache Qfw3_c1 Q7UD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import Qfw3_c1.Mq0.
Import Q7UD.
Notation rsegs := asegs.
Import ListNotations.
Open Scope bv_scope.

Definition memset_entry := 0xdb750%Z.

Ltac with_arr tac :=
lazymatch goal with
| ARR : u8arr ?segs ?m ?A ?bs, FIL : filled ?cb ?bs _, LEN : length ?bs = _ |- _ => tac segs ARR FIL LEN A cb
end.

Ltac brute256 c Rc :=
first [ apply word_eq_of_eqb | apply Z.eqb_eq | idtac ];
repeat match goal with H : context [c] |- _ => tryif constr_eq H Rc then fail else clear H end;
revert c Rc; apply brute256_ok; vm_compute; reflexivity.

Ltac reg_val r :=
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end)
end.

Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.

Lemma land4_of_aligned : forall x, (0 <= x)%Z -> (x mod 4 = 0)%Z -> Z.land x 4 = (x mod 8)%Z.
Proof.
intros x Hx H4.
transitivity (Z.land (x mod 8) 4).
{ change 8%Z with (2^3)%Z. rewrite <- Z.land_ones by lia. change (Z.ones 3) with 7%Z.
rewrite <- Z.land_assoc. reflexivity. }
assert (R : (x mod 8 = 0 \/ x mod 8 = 4)%Z) by (Z.div_mod_to_equations; lia).
destruct R as [R|R]; rewrite R; reflexivity.
Qed.

Definition memset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 a2 : word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' (bv_unsigned a0)
[CB (Z.to_nat (bv_unsigned a2)) (repeat (Z_to_bv 8 (bv_unsigned a1 mod 256)) (Z.to_nat (bv_unsigned a2)))].

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Hypothesis MI0 : mem_inv rsegs m.
Hypothesis AB : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 <= 2^64 /\ 0 <= bv_unsigned a2 < 2^64)%Z.

Notation A := (bv_unsigned a0).
Notation n := (bv_unsigned a2).
Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
Notation POST := (memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m).

Notation ST pc mm x11 x12 x13 x14 x15 x16 :=
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

Ltac fin_with cover :=
zstep;
with_arr ltac:(fun segs ARR FIL LEN A cb =>
let E := fresh "E" in
pose proof (filled_all _ _ _ FIL ltac:(cover)) as E;
rewrite LEN in E; rewrite E in ARR;
apply rw_cells_of_u8arr in ARR; rewrite repeat_length in ARR);
finish; subst; assumption.
Ltac fin := fin_with ltac:(intros j Hj; cbv beta; lia).
Ltac disj_lia := first [ lia | right; lia | left; disj_lia ].

Lemma memset_loop : forall (K : nat) (c p r e : Z) (m1 : word -> option byte) (bs : list byte) (Q : Z -> Prop)
(x15 x16 : word),
Z.to_nat r = K ->
c = (bv_unsigned a1 mod 256)%Z ->
u8arr rsegs m1 A bs -> filled (Z_to_bv 8 c) bs Q -> length bs = Z.to_nat n ->
mem_inv rsegs m1 -> munch W m m1 -> wmono rsegs m m1 ->
(forall j, (0 <= j < p \/ e <= j < n) -> Q j)%Z ->
(0 <= p)%Z -> (32 <= r)%Z -> (exists q, r = 4 * q)%Z -> (p + r <= n)%Z -> (e + 28 <= p + r)%Z ->
evt rsegs POST (ST 0xdb828 m1 (Z_to_bv 64 (A + p)) (Z_to_bv 64 (c * BC8)) (Z_to_bv 64 31) (Z_to_bv 64 r) x15 x16).
Proof using AB.
induction K as [K IH] using lt_wf_ind; intros c p r e m1 bs Q x15 x16 HK Hc ARR FIL LEN MI MU WM HQ Hp Hr [q4 Hq4] Hpr He;
assert (Rc : (0 <= c < 256)%Z) by (subst c; apply Z.mod_pos_bound; lia).
mst p 8%nat ltac:(symmetry; apply le8_bcast; lia).
mst (p + 8)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
mst (p + 16)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
mst (p + 24)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
zstep. zstep. zstep.
if_cases KK; zify_cond KK.
-
replace (A + p + 32)%Z with (A + (p + 32))%Z by lia.
replace (r + -32)%Z with (r - 32)%Z by lia.
eapply (IH (Z.to_nat (r - 32)) ltac:(lia) c (p + 32)%Z (r - 32)%Z e _ _ _ x15 x16 eq_refl Hc ARR); try eassumption; try lia.
2:{ exists (q4 - 8)%Z. lia. }
intros j Hj.
destruct (Z_lt_le_dec j p) as [Hlt|Hge]. { left; left; left; left. apply HQ. lia. }
destruct (Z_lt_le_dec j (p + 32)) as [Hlt2|Hge2]. 2:{ left; left; left; left. apply HQ. lia. }
assert (D : ((p <= j < p + 8 \/ p + 8 <= j < p + 16) \/ (p + 16 <= j < p + 24 \/ p + 24 <= j < p + 32))%Z) by lia.
destruct D as [[?|?]|[?|?]]; [left; left; left; right| left; left; right| left; right| right]; lia.
- fin_with ltac:(intros j Hj; destruct (Z_lt_le_dec j p); [repeat left; apply HQ; lia|];
destruct (Z_lt_le_dec j (p + 32)); [|repeat left; apply HQ; lia]; disj_lia).
Qed.

Lemma memset_body : forall junk,
rw_cells rsegs m A [CB (Z.to_nat n) junk] ->
evt rsegs POST (ST 0xdb750 m a1 a2 a3 a4 a5 a6).
Proof using AB MI0.
intros junk DST. pose proof MI0 as MI.
pose proof (munch_refl W m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (zr_word a1) as R1. unfold inr64 in R1.
remember (bv_unsigned a1 mod 256)%Z as c eqn:Hc.
assert (Rc : (0 <= c < 256)%Z) by (subst c; apply Z.mod_pos_bound; lia).
pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as ARR.
pose proof (rw_cells_CB_length _ _ _ _ _ DST) as LEN.
pose proof (filled_init (Z_to_bv 8 c) junk) as FIL.

zstep. if_cases K0; zify_cond K0. { fin. }
assert (MF : ms_facts A n 0 1) by (unfold ms_facts; lia).
pose proof (ms_store_ok rsegs _ A n _ 0 1 a0 ARR LEN MF (eq_sym (Z_to_bv_plus0 a0))) as SOK.
zstep. ms_arr_store MF ltac:(rewrite Hc, le1_byte; reflexivity).
zstep. zstep. mst (n - 1)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
zstep. if_cases K3; zify_cond K3. { fin. }
mst 1%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
mst 2%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
zstep.
mst (n - 3)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
mst (n - 2)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
zstep. if_cases K7; zify_cond K7. { fin. }
mst 3%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
zstep.
mst (n - 4)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
zstep. if_cases K9; zify_cond K9. { fin. }

zstep. zstep.
setreg 16%Z (Z_to_bv 64 (c * 2^56)) ltac:(apply Z_to_bv_eqm; rewrite Z.shiftl_mul_pow2 by lia; subst c; Z.div_mod_to_equations; lia).
zstep. zstep.
remember (Z.land (bv_swrap 32 (0 - A) mod 18446744073709551616) 3) as k eqn:Hk.
assert (Rk : (0 <= k < 4 /\ (A + k) mod 4 = 0)%Z).
{ subst k. change 3%Z with (2^2 - 1)%Z. rewrite zb_land_mask by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ (Z.of_N 32 - 1))%Z with (2^31)%Z. change (2 ^ Z.of_N 32)%Z with (2^32)%Z.
Z.div_mod_to_equations. lia. }
clear Hk.
zstep. zstep. zstep. zstep. zstep.
change 18446744073709551612%Z with (2^64 - 2^2)%Z. rewrite land_align_down by lia.
remember (n - k - (n - k) mod 2^2)%Z as n4 eqn:Hn4.
assert (Rn4 : (exists q, n4 = 4 * q)%Z /\ (n - k - 3 <= n4 <= n - k)%Z).
{ split. { exists ((n - k) / 4)%Z. subst n4. Z.div_mod_to_equations. lia. } subst n4. Z.div_mod_to_equations. lia. }
clear Hn4. destruct Rn4 as [[q4 Hq4] Rn4].
zstep. setreg 12%Z (Z_to_bv 64 (c * BC4)) ltac:(unfold BC4; brute256 c Rc).

mst k 4%nat ltac:(symmetry; apply le4_bcast; lia).
zstep. mst (k + n4 - 4)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
zstep. if_cases K9'; zify_cond K9'. { fin. }
mst (k + 4)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + 8)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
zstep.
mst (k + n4 - 12)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + n4 - 8)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
zstep. if_cases K25; zify_cond K25. { fin. }
mst (k + 12)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + 16)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + 20)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + 24)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).

zstep.
remember (Z.land (A + k) 4) as k4 eqn:Hk4.
assert (Rk4 : ((k4 = 0 \/ k4 = 4) /\ (A + k + k4 + 24) mod 8 = 0)%Z).
{ subst k4. rewrite land4_of_aligned by lia. Z.div_mod_to_equations. lia. }
clear Hk4.
zstep. zstep. zstep.
mst (k + n4 - 28)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + n4 - 24)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + n4 - 20)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + n4 - 16)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
zstep. if_cases K32; zify_cond K32. { fin. }

zstep. zstep. zstep. zstep. setreg 12%Z (Z_to_bv 64 (c * BC8)) ltac:(unfold BC4, BC8; brute256 c Rc).
zstep.
replace (A + k + (k4 + 24))%Z with (A + (k + k4 + 24))%Z by lia.
eapply (memset_loop _ c (k + k4 + 24) _ (k + n4 - 28) _ _ _ _ _ eq_refl Hc ARR); try eassumption; try lia.
exists (q4 - Z.div k4 4 - 6)%Z. lia.
Qed.
End Proofs.

Lemma memset_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (junk : list byte),
rw_cells rsegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
mem_inv rsegs m ->
evt rsegs (memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdb750) fc None m (seg_rom rsegs)).
Proof.
intros until junk. intros DST MI.
eapply memset_body; [exact MI | | exact DST].
pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R. cbn. lia.
Qed.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import Qfw3_c1.Mq0.
Import QbFI.
Notation rsegs := asegs.
Import ListNotations.
Open Scope bv_scope.

Definition memset_entry := 0xdde14%Z.

Ltac with_arr tac :=
lazymatch goal with
| ARR : u8arr ?segs ?m ?A ?bs, FIL : filled ?cb ?bs _, LEN : length ?bs = _ |- _ => tac segs ARR FIL LEN A cb
end.

Ltac brute256 c Rc :=
first [ apply word_eq_of_eqb | apply Z.eqb_eq | idtac ];
repeat match goal with H : context [c] |- _ => tryif constr_eq H Rc then fail else clear H end;
revert c Rc; apply brute256_ok; vm_compute; reflexivity.

Ltac reg_val r :=
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end)
end.

Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.

Lemma land4_of_aligned : forall x, (0 <= x)%Z -> (x mod 4 = 0)%Z -> Z.land x 4 = (x mod 8)%Z.
Proof.
intros x Hx H4.
transitivity (Z.land (x mod 8) 4).
{ change 8%Z with (2^3)%Z. rewrite <- Z.land_ones by lia. change (Z.ones 3) with 7%Z.
rewrite <- Z.land_assoc. reflexivity. }
assert (R : (x mod 8 = 0 \/ x mod 8 = 4)%Z) by (Z.div_mod_to_equations; lia).
destruct R as [R|R]; rewrite R; reflexivity.
Qed.

Definition memset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 a2 : word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' (bv_unsigned a0)
[CB (Z.to_nat (bv_unsigned a2)) (repeat (Z_to_bv 8 (bv_unsigned a1 mod 256)) (Z.to_nat (bv_unsigned a2)))].

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Hypothesis MI0 : mem_inv rsegs m.
Hypothesis AB : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 <= 2^64 /\ 0 <= bv_unsigned a2 < 2^64)%Z.

Notation A := (bv_unsigned a0).
Notation n := (bv_unsigned a2).
Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
Notation POST := (memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m).

Notation ST pc mm x11 x12 x13 x14 x15 x16 :=
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

Ltac fin_with cover :=
zstep;
with_arr ltac:(fun segs ARR FIL LEN A cb =>
let E := fresh "E" in
pose proof (filled_all _ _ _ FIL ltac:(cover)) as E;
rewrite LEN in E; rewrite E in ARR;
apply rw_cells_of_u8arr in ARR; rewrite repeat_length in ARR);
finish; subst; assumption.
Ltac fin := fin_with ltac:(intros j Hj; cbv beta; lia).
Ltac disj_lia := first [ lia | right; lia | left; disj_lia ].

Lemma memset_loop : forall (K : nat) (c p r e : Z) (m1 : word -> option byte) (bs : list byte) (Q : Z -> Prop)
(x15 x16 : word),
Z.to_nat r = K ->
c = (bv_unsigned a1 mod 256)%Z ->
u8arr rsegs m1 A bs -> filled (Z_to_bv 8 c) bs Q -> length bs = Z.to_nat n ->
mem_inv rsegs m1 -> munch W m m1 -> wmono rsegs m m1 ->
(forall j, (0 <= j < p \/ e <= j < n) -> Q j)%Z ->
(0 <= p)%Z -> (32 <= r)%Z -> (exists q, r = 4 * q)%Z -> (p + r <= n)%Z -> (e + 28 <= p + r)%Z ->
evt rsegs POST (ST 0xddeec m1 (Z_to_bv 64 (A + p)) (Z_to_bv 64 (c * BC8)) (Z_to_bv 64 31) (Z_to_bv 64 r) x15 x16).
Proof using AB.
induction K as [K IH] using lt_wf_ind; intros c p r e m1 bs Q x15 x16 HK Hc ARR FIL LEN MI MU WM HQ Hp Hr [q4 Hq4] Hpr He;
assert (Rc : (0 <= c < 256)%Z) by (subst c; apply Z.mod_pos_bound; lia).
mst p 8%nat ltac:(symmetry; apply le8_bcast; lia).
mst (p + 8)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
mst (p + 16)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
mst (p + 24)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
zstep. zstep. zstep.
if_cases KK; zify_cond KK.
-
replace (A + p + 32)%Z with (A + (p + 32))%Z by lia.
replace (r + -32)%Z with (r - 32)%Z by lia.
eapply (IH (Z.to_nat (r - 32)) ltac:(lia) c (p + 32)%Z (r - 32)%Z e _ _ _ x15 x16 eq_refl Hc ARR); try eassumption; try lia.
2:{ exists (q4 - 8)%Z. lia. }
intros j Hj.
destruct (Z_lt_le_dec j p) as [Hlt|Hge]. { left; left; left; left. apply HQ. lia. }
destruct (Z_lt_le_dec j (p + 32)) as [Hlt2|Hge2]. 2:{ left; left; left; left. apply HQ. lia. }
assert (D : ((p <= j < p + 8 \/ p + 8 <= j < p + 16) \/ (p + 16 <= j < p + 24 \/ p + 24 <= j < p + 32))%Z) by lia.
destruct D as [[?|?]|[?|?]]; [left; left; left; right| left; left; right| left; right| right]; lia.
- fin_with ltac:(intros j Hj; destruct (Z_lt_le_dec j p); [repeat left; apply HQ; lia|];
destruct (Z_lt_le_dec j (p + 32)); [|repeat left; apply HQ; lia]; disj_lia).
Qed.

Lemma memset_body : forall junk,
rw_cells rsegs m A [CB (Z.to_nat n) junk] ->
evt rsegs POST (ST 0xdde14 m a1 a2 a3 a4 a5 a6).
Proof using AB MI0.
intros junk DST. pose proof MI0 as MI.
pose proof (munch_refl W m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (zr_word a1) as R1. unfold inr64 in R1.
remember (bv_unsigned a1 mod 256)%Z as c eqn:Hc.
assert (Rc : (0 <= c < 256)%Z) by (subst c; apply Z.mod_pos_bound; lia).
pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as ARR.
pose proof (rw_cells_CB_length _ _ _ _ _ DST) as LEN.
pose proof (filled_init (Z_to_bv 8 c) junk) as FIL.

zstep. if_cases K0; zify_cond K0. { fin. }
assert (MF : ms_facts A n 0 1) by (unfold ms_facts; lia).
pose proof (ms_store_ok rsegs _ A n _ 0 1 a0 ARR LEN MF (eq_sym (Z_to_bv_plus0 a0))) as SOK.
zstep. ms_arr_store MF ltac:(rewrite Hc, le1_byte; reflexivity).
zstep. zstep. mst (n - 1)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
zstep. if_cases K3; zify_cond K3. { fin. }
mst 1%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
mst 2%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
zstep.
mst (n - 3)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
mst (n - 2)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
zstep. if_cases K7; zify_cond K7. { fin. }
mst 3%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
zstep.
mst (n - 4)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
zstep. if_cases K9; zify_cond K9. { fin. }

zstep. zstep.
setreg 16%Z (Z_to_bv 64 (c * 2^56)) ltac:(apply Z_to_bv_eqm; rewrite Z.shiftl_mul_pow2 by lia; subst c; Z.div_mod_to_equations; lia).
zstep. zstep.
remember (Z.land (bv_swrap 32 (0 - A) mod 18446744073709551616) 3) as k eqn:Hk.
assert (Rk : (0 <= k < 4 /\ (A + k) mod 4 = 0)%Z).
{ subst k. change 3%Z with (2^2 - 1)%Z. rewrite zb_land_mask by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ (Z.of_N 32 - 1))%Z with (2^31)%Z. change (2 ^ Z.of_N 32)%Z with (2^32)%Z.
Z.div_mod_to_equations. lia. }
clear Hk.
zstep. zstep. zstep. zstep. zstep.
change 18446744073709551612%Z with (2^64 - 2^2)%Z. rewrite land_align_down by lia.
remember (n - k - (n - k) mod 2^2)%Z as n4 eqn:Hn4.
assert (Rn4 : (exists q, n4 = 4 * q)%Z /\ (n - k - 3 <= n4 <= n - k)%Z).
{ split. { exists ((n - k) / 4)%Z. subst n4. Z.div_mod_to_equations. lia. } subst n4. Z.div_mod_to_equations. lia. }
clear Hn4. destruct Rn4 as [[q4 Hq4] Rn4].
zstep. setreg 12%Z (Z_to_bv 64 (c * BC4)) ltac:(unfold BC4; brute256 c Rc).

mst k 4%nat ltac:(symmetry; apply le4_bcast; lia).
zstep. mst (k + n4 - 4)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
zstep. if_cases K9'; zify_cond K9'. { fin. }
mst (k + 4)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + 8)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
zstep.
mst (k + n4 - 12)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + n4 - 8)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
zstep. if_cases K25; zify_cond K25. { fin. }
mst (k + 12)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + 16)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + 20)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + 24)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).

zstep.
remember (Z.land (A + k) 4) as k4 eqn:Hk4.
assert (Rk4 : ((k4 = 0 \/ k4 = 4) /\ (A + k + k4 + 24) mod 8 = 0)%Z).
{ subst k4. rewrite land4_of_aligned by lia. Z.div_mod_to_equations. lia. }
clear Hk4.
zstep. zstep. zstep.
mst (k + n4 - 28)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + n4 - 24)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + n4 - 20)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + n4 - 16)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
zstep. if_cases K32; zify_cond K32. { fin. }

zstep. zstep. zstep. zstep. setreg 12%Z (Z_to_bv 64 (c * BC8)) ltac:(unfold BC4, BC8; brute256 c Rc).
zstep.
replace (A + k + (k4 + 24))%Z with (A + (k + k4 + 24))%Z by lia.
eapply (memset_loop _ c (k + k4 + 24) _ (k + n4 - 28) _ _ _ _ _ eq_refl Hc ARR); try eassumption; try lia.
exists (q4 - Z.div k4 4 - 6)%Z. lia.
Qed.
End Proofs.

Lemma memset_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (junk : list byte),
rw_cells rsegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
mem_inv rsegs m ->
evt rsegs (memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdde14) fc None m (seg_rom rsegs)).
Proof.
intros until junk. intros DST MI.
eapply memset_body; [exact MI | | exact DST].
pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R. cbn. lia.
Qed.
End Mq1.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition frame : Type := (Z * Z)%type.
Definition fr_base (f : frame) : Z := fst f.
Definition fr_class (f : frame) : Z := snd f.
Definition fr_size (k : Z) : Z := 64 * 2 ^ k.
Definition fr_shadow_len (k : Z) : Z := 8 * 2 ^ k.

Fixpoint fr_remove (F : Z) (FR : list frame) : list frame :=
match FR with
| [] => []
| f :: FR' => if Z.eqb (fr_base f) F then FR' else f :: fr_remove F FR'
end.

Definition shadow_bytes (n : Z) : list byte :=
repeat (Z_to_bv 8 0) (Z.to_nat (n / 8))
++ (if Z.eqb (n mod 8) 0 then [] else [Z_to_bv 8 (n mod 8)]).

Record bud := Bud { bB : Z; bD : Z; bN : Z; bM : Z; bQ : Z }.
Definition charge (x : bud) (cm cd cn : Z) : bud := Bud (bB x - cm) (bD x - cd) (bN x - cn) (bM x) (bQ x).
Definition chargeM (x : bud) (k : Z) : bud := Bud (bB x) (bD x) (bN x) (bM x - k) (bQ x).

Definition chargeQ (x : bud) (q : Z) : bud := Bud (bB x) (bD x) (bN x) (bM x) (bQ x - q).

Definition acostA (n : Z) : Z := if n <=? 64512 then 0 else 3 * n + 45101.

Lemma acostA_nonneg : forall n, 0 <= n -> 0 <= acostA n.
Proof. intros n H. unfold acostA. destruct (Z.leb_spec n 64512); lia. Qed.

Inductive uwd :=
| UWptr
| UWfp (ra2 v2 : Z)
| UWpaid.
Definition uw_cost (u : uwd) : Z := match u with UWpaid => 1 | _ => 0 end.
Definition uw_key (entry ra : Z) (u : uwd) : option (Z * Z * option Z) :=
match u with UWptr => Some (entry, ra, None) | UWfp ra2 _ => Some (entry, ra, Some ra2) | UWpaid => None end.

Record heap_layout_A := HLA {
hla_base :> heap_layout;
hl_sb : Z;
hl_sb_cell : Z;
hl_got_sb : Z;
hl_uar_cell : Z;
hl_got_uar : Z;
hl_stack_malloc : Z -> Z;
hl_strdup : Z;
hl_stack_A : Z;
hl_gp : Z;
hl_pristine : list (Z * Z);
hl_globals : list (Z * Z);
hl_reg_globals : list (Z * Z * Z);
hl_straces : list (Z * Z * option Z);
hl_rt_consts : list (Z * list byte);
hl_sb_range : 0 < hl_sb /\ hl_sb + 2^61 < 2^64
}.

Fixpoint img_shadow_val (regs : list (Z * Z * Z)) (g : Z) : Z :=
match regs with
| [] => 0
| (b, sz, szr) :: regs' =>
if ((b <=? 8 * g) && (8 * g <? b + szr))%bool then
(if 8 * g + 8 <=? b + sz then 0 else if 8 * g <? b + sz then (b + sz) mod 8 else 0xf9)
else img_shadow_val regs' g
end.

Record aj_base (segs : list Segment) := AJB {
AJ : TSet -> config -> machine_state -> Prop;
CK : config -> Prop;
CNEXT : config -> config -> Prop;

aj_evt : forall T c ms, evt segs (AJ T c) ms -> AJ T c ms;
aj_conseq : forall T T' c ms, AJ T c ms -> t_eq T T' -> AJ T' c ms;
ck_halted : forall c, CK c -> m_halted (cfg_model c) = None;
cnext_ck : forall c c', CNEXT c c' -> CK c';
cnext_trans : forall a b c, CNEXT a b -> CNEXT b c -> CNEXT a c
}.
Arguments AJ {segs}. Arguments CK {segs}. Arguments CNEXT {segs}.

Section IfaceA.
Variable L : heap_layout_A.
Let segs : list Segment := hl_segs L.
Notation errno_a := (hl_tp L - 164).

Definition shad (a : Z) : Z := a / 8 + hl_sb L.

Definition fr_ivs (FR : list frame) : list blk :=
flat_map (fun f => [(fr_base f, fr_size (fr_class f) - 8); (shad (fr_base f), fr_shadow_len (fr_class f))]) FR.

Definition uw_pre (hi : Z) (m : word -> option byte) (sp s0 : Z) (u : uwd) : Prop :=
match u with
| UWptr => s0 < alloc_ceiling \/ s0 mod 8 <> 0 \/ hi - 16 <= s0
| UWfp ra2 v2 => sp < s0 /\ s0 mod 8 = 0 /\ s0 < hi - 16 /\
bytes_at segs m (s0 - 16) (le8 (Z_to_bv 64 v2) ++ le8 (Z_to_bv 64 ra2)) /\
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= s0 \/ hi - 16 <= v2) /\
0 <= v2 < 2^64
| UWpaid => True
end.

Definition uw_ok (entry : Z) (ra : word) (u : uwd) : Prop :=
match uw_key entry (bv_unsigned ra) u with Some k => In k (hl_straces L) | None => True end.

Record heap_iface_A := HIA {
hiA_J : aj_base (hl_segs L);
ASA : Type;
HEAPA : ASA -> list blk  -> list blk  -> list frame  -> bud  ->
(word -> option byte) -> config -> Prop;
hiA_top : Z;
hiA_top_hi : alloc_ceiling < hiA_top;
hiA_top_le : hiA_top <= 2^47;

hiA_bot : Z;

hiA_bot_top : hiA_bot mod 8 = 0 /\ hiA_bot <= hiA_top;

heapA_cok : forall A LB LM FR B m c, HEAPA A LB LM FR B m c -> CK hiA_J c;
heapA_mem_inv : forall A LB LM FR B m c, HEAPA A LB LM FR B m c -> mem_inv segs m;
heapA_budget : forall A LB LM FR B m c, HEAPA A LB LM FR B m c -> 0 <= bB B /\ 0 <= bD B /\ 0 <= bN B /\ 0 <= bM B /\ 0 <= bQ B;
heapA_bB_bound : forall A LB LM FR B m c, HEAPA A LB LM FR B m c -> bB B + 2^23 <= 2^39;

heapA_cfg_next : forall A LB LM FR B m c c', HEAPA A LB LM FR B m c -> CNEXT hiA_J c c' -> HEAPA A LB LM FR B m c';

heapA_blk_lt40 : forall A LB LM FR B m c a n, HEAPA A LB LM FR B m c -> In (a, n) (LB ++ LM) -> n < 2^40;

heapA_blk_le26 : forall A LB LM FR B m c a n, HEAPA A LB LM FR B m c -> In (a, n) LB -> n <= 2^26;
heapA_blk : forall A LB LM FR B m c a n, HEAPA A LB LM FR B m c -> In (a, n) (LB ++ LM) ->
0 <= n /\ a mod 16 = 0 /\ 0 < a /\ a + n <= alloc_ceiling /\ wr_at segs m a n;
heapA_blk_img : forall A LB LM FR B m c a n, HEAPA A LB LM FR B m c -> In (a, n) (LB ++ LM) ->
a + n <= hl_img_lo L \/ hl_img_hi L <= a;
heapA_blk_disjoint : forall A LB LM FR B m c a n a' n', HEAPA A LB LM FR B m c ->
In (a, n) (LB ++ LM) -> In (a', n') (LB ++ LM) -> a <> a' -> (a + n <= a' \/ a' + n' <= a);
heapA_blk_nodup : forall A LB LM FR B m c, HEAPA A LB LM FR B m c -> List.NoDup (map blk_addr (LB ++ LM));
heapA_blk_not_static : forall A LB LM FR B m c a n i, HEAPA A LB LM FR B m c -> In (a, n) (LB ++ LM) ->
0 <= i < n -> ~ hl_client_static L (a + i);
heapA_perm : forall A LB LB' LM LM' FR FR' B m c, HEAPA A LB LM FR B m c ->
Permutation LB LB' -> Permutation LM LM' -> Permutation FR FR' -> HEAPA A LB' LM' FR' B m c;

heapA_blk_slack : forall A LB LM FR B m c a n, HEAPA A LB LM FR B m c -> In (a, n) (LB ++ LM) ->
exists junk, bytes_at segs m (a + n) junk /\ Z.of_nat (length junk) = (16 - n mod 16) mod 16;

heapA_shadow_blk : forall A LB LM FR B m c a n, HEAPA A LB LM FR B m c -> In (a, n) LB ->
bytes_at segs m (shad a) (shadow_bytes n);
heapA_shadow_glob : forall A LB LM FR B m c, HEAPA A LB LM FR B m c ->
Forall (fun g => bytes_at segs m (shad (fst g)) (repeat (Z_to_bv 8 0) (Z.to_nat (snd g / 8)))) (hl_globals L);

heapA_shadow_sep : forall A LB LM FR B m c a n i, HEAPA A LB LM FR B m c -> In (a, n) LB -> 0 <= i < (n + 7) / 8 ->
~ client_addr (hla_base L) (LB ++ LM) alloc_ceiling (shad a + i)
/\ (shad a + i < hl_img_lo L \/ hl_img_hi L <= shad a + i);

heapA_sb_cells : forall A LB LM FR B m c, HEAPA A LB LM FR B m c ->
bytes_at segs m (hl_got_sb L) (le8 (Z_to_bv 64 (hl_sb_cell L))) /\
bytes_at segs m (hl_sb_cell L) (le8 (Z_to_bv 64 (hl_sb L))) /\
bytes_at segs m (hl_got_uar L) (le8 (Z_to_bv 64 (hl_uar_cell L))) /\
bytes_at segs m (hl_uar_cell L) (le4 (Z_to_bv 64 1));

heapA_frame : forall A LB LM FR B m c F k, HEAPA A LB LM FR B m c -> In (F, k) FR ->
0 <= k <= 3 /\ F mod fr_size k = 0 /\ 0 < F /\ F + fr_size k <= alloc_ceiling /\
(F + fr_size k <= hl_img_lo L \/ hl_img_hi L <= F) /\
wr_at segs m F (fr_size k - 8) /\
wr_at segs m (shad F) (fr_shadow_len k) /\

(exists fp, bytes_at segs m (F + fr_size k - 8) (le8 (Z_to_bv 64 fp)) /\ 0 < fp < 2^64 /\
~ client_addr (hla_base L) (LB ++ LM) alloc_ceiling fp /\ (fp < hl_img_lo L \/ hl_img_hi L <= fp) /\
~ hl_scratch L fp /\
(forall F' k', In (F', k') FR -> ~ (F' <= fp < F' + fr_size k') /\ ~ (shad F' <= fp < shad F' + fr_shadow_len k')));
heapA_frame_disjoint : forall A LB LM FR B m c F k a n, HEAPA A LB LM FR B m c -> In (F, k) FR -> In (a, n) (LB ++ LM) ->
F + fr_size k <= a \/ a + n <= F;

heapA_frame_apart : forall A LB LM FR B m c F k F' k', HEAPA A LB LM FR B m c ->
In (F, k) FR -> In (F', k') FR -> F <> F' ->
F + fr_size k <= F' \/ F' + fr_size k' <= F;

heapA_frame_nodup : forall A LB LM FR B m c, HEAPA A LB LM FR B m c -> NoDup (map fr_base FR);

heapA_frame_appmem : forall A LB LM FR B m c F k, HEAPA A LB LM FR B m c -> In (F, k) FR ->
F + fr_size k + 8 <= hl_sb L \/ (2^47 - 1) / 8 + hl_sb L + 1 <= F;

heapA_frame_shadow_sep : forall A LB LM FR B m c F k i, HEAPA A LB LM FR B m c -> In (F, k) FR ->
0 <= i < fr_shadow_len k ->
~ client_addr (hla_base L) (LB ++ LM) alloc_ceiling (shad F + i)
/\ (shad F + i < hl_img_lo L \/ hl_img_hi L <= shad F + i);

heapA_client_frame : forall A LB LM FR B m m' c, HEAPA A LB LM FR B m c ->
(forall a, 0 <= a < 2^64 ->
~ client_addr (hla_base L) (LB ++ LM) alloc_ceiling a ->
~ hl_scratch L a ->
~ (exists F k, In (F, k) FR /\ (F <= a < F + fr_size k - 8 \/ shad F <= a < shad F + fr_shadow_len k)) ->
m' (wa a) = m (wa a)) ->
(forall x, wview segs m x <> None -> wview segs m' x <> None) ->
mem_inv segs m' ->
HEAPA A LB LM FR B m' c;
heapA_canary : forall A LB LM FR B m c, HEAPA A LB LM FR B m c ->
exists g : word,
bytes_at segs m (hl_got_guard L) (le8 (Z_to_bv 64 (hl_guard L))) /\
bytes_at segs m (hl_guard L) (le8 g) /\ bytes_at segs m (hl_tp L - 16) (le8 g);
heapA_need_locks : forall A LB LM FR B m c, HEAPA A LB LM FR B m c -> bytes_at segs m (hl_libc L + 3) [Z_to_bv 8 0];
heapA_consts : forall A LB LM FR B m c, HEAPA A LB LM FR B m c -> Forall (fun c => bytes_at segs m (fst c) (snd c)) (hl_consts L);

heapA_rtc : forall A LB LM FR B m c, HEAPA A LB LM FR B m c -> Forall (fun c => bytes_at segs m (fst c) (snd c)) (hl_rt_consts L);

heapA_errno : forall A LB LM FR B m c, HEAPA A LB LM FR B m c -> exists errv : word, rw_cells segs m errno_a [C4 errv];

heapA_frame_above : forall A LB LM FR B m c F k, HEAPA A LB LM FR B m c -> In (F, k) FR -> hl_img_hi L <= F;

heapA_shadow_words : forall A LB LM FR B m c a n i, HEAPA A LB LM FR B m c -> In (a, n) LB -> 0 <= i < (n + 7) / 8 ->
exists w : list byte, length w = 8%nat /\ bytes_at segs m ((shad a + i) / 8 * 8) w;

heapA_shadow_stack : forall A LB LM FR B m c a n, HEAPA A LB LM FR B m c ->
hiA_bot <= a -> a + n <= hiA_top + 2^22 -> a + n <= 2^47 -> 0 < n ->
bytes_at segs m (shad a) (repeat (Z_to_bv 8 0) (Z.to_nat ((a + n - 1) / 8 - a / 8 + 1)));

heapA_shadow_img : forall A LB LM FR B m c g, HEAPA A LB LM FR B m c ->
hl_img_lo L <= 8 * g -> 8 * g + 8 <= hl_img_hi L ->
bytes_at segs m (g + hl_sb L) [Z_to_bv 8 (img_shadow_val (hl_reg_globals L) g)];

heapA_blk_appmem : forall A LB LM FR B m c a n, HEAPA A LB LM FR B m c -> In (a, n) (LB ++ LM) ->
a + n + 8 <= hl_sb L \/ (2^47 - 1) / 8 + hl_sb L + 1 <= a;

hiA_malloc : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : ASA) (LB LM : list blk) (FR : list frame) (B : bud) (n lo : Z) (errv : word) (u : uwd),
HEAPA A LB LM FR B m c ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top + 64 ->
rw_cells segs m errno_a [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) -> gp = Z_to_bv 64 (hl_gp L) ->
a0 = Z_to_bv 64 n -> 1 <= n <= 2^26 ->
uw_pre hiA_top m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok (hl_malloc L) ra u ->
1 <= bN B -> acostA n <= bB B -> uw_cost u <= bD B -> n + 8192 <= bQ B ->
(forall ms' m' c' A' (r : Z) (errv' : word),
ret_state (hla_base L) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres (hla_base L) (LB ++ LM ++ fr_ivs FR) (bv_unsigned sp) m m' ->
rw_cells segs m' errno_a [C4 errv'] ->
r <> 0 -> (exists junk, rw_cells segs m' r [CB (Z.to_nat n) junk]) ->
HEAPA A' ((r, n) :: LB) LM FR (chargeQ (charge B (acostA n) (uw_cost u) 1) (n + 8192)) m' c' ->
AJ hiA_J T c' ms') ->
AJ hiA_J T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_malloc L)) fc None m (seg_rom segs));

hiA_free : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : ASA) (LB LM : list blk) (FR : list frame) (B : bud) (p lo : Z) (errv : word) (u : uwd),
HEAPA A LB LM FR B m c ->
(p = 0 \/ exists n, In (p, n) LB) ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top + 64 ->
rw_cells segs m errno_a [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) -> gp = Z_to_bv 64 (hl_gp L) ->
a0 = Z_to_bv 64 p ->
uw_pre hiA_top m (bv_unsigned sp) (bv_unsigned s0) u /\ uw_ok (hl_free L) ra u ->
(if Z.eqb p 0 then 0 else uw_cost u) <= bD B ->
(forall ms' m' c' A' (r : word),
ret_state (hla_base L) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' ->
model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres (hla_base L) (lb_remove p LB ++ LM ++ fr_ivs FR) (bv_unsigned sp) m m' ->
rw_cells segs m' errno_a [C4 errv] ->
HEAPA A' (lb_remove p LB) LM FR (charge B 0 (if Z.eqb p 0 then 0 else uw_cost u) 0) m' c' ->
AJ hiA_J T c' ms') ->
AJ hiA_J T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_free L)) fc None m (seg_rom segs));

hiA_calloc : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : ASA) (LB LM : list blk) (FR : list frame) (B : bud) (cnt sz lo : Z) (errv : word) (u : uwd),
HEAPA A LB LM FR B m c ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top + 64 ->
rw_cells segs m errno_a [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) -> gp = Z_to_bv 64 (hl_gp L) ->
a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 sz -> 0 <= cnt < 2^32 -> 0 <= sz < 2^32 -> 1 <= cnt * sz <= 2^26 ->
uw_pre hiA_top m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok (hl_calloc L) ra u ->
1 <= bN B -> acostA (cnt * sz) <= bB B -> uw_cost u <= bD B -> cnt * sz + 8192 <= bQ B ->
(forall ms' m' c' A' (r : Z) (errv' : word),
ret_state (hla_base L) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres (hla_base L) (LB ++ LM ++ fr_ivs FR) (bv_unsigned sp) m m' ->
rw_cells segs m' errno_a [C4 errv'] ->
r <> 0 -> rw_cells segs m' r [CB (Z.to_nat (cnt * sz)) (repeat (Z_to_bv 8 0) (Z.to_nat (cnt * sz)))] ->
HEAPA A' ((r, cnt * sz) :: LB) LM FR (chargeQ (charge B (acostA (cnt * sz)) (uw_cost u) 1) (cnt * sz + 8192)) m' c' ->
AJ hiA_J T c' ms') ->
AJ hiA_J T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_calloc L)) fc None m (seg_rom segs));

hiA_realloc : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : ASA) (LB LM : list blk) (FR : list frame) (B : bud) (p n0 n lo : Z) (errv : word) (old junk0 : list byte) (u : uwd),
HEAPA A LB LM FR B m c -> In (p, n0) LB ->
rw_cells segs m p [CB (Z.to_nat n0) (old ++ junk0)] ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top + 64 ->
rw_cells segs m errno_a [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) -> gp = Z_to_bv 64 (hl_gp L) ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 n -> 1 <= n <= 2^26 ->
uw_pre hiA_top m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok (hl_realloc L) ra u ->
1 <= bN B -> acostA n <= bB B -> uw_cost u <= bD B -> n + 8192 <= bQ B ->
(forall ms' m' c' A' (r : Z) (errv' : word),
ret_state (hla_base L) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
rw_cells segs m' errno_a [C4 errv'] ->
r <> 0 -> heap_pres (hla_base L) (lb_remove p LB ++ LM ++ fr_ivs FR) (bv_unsigned sp) m m' ->
(exists junk, rw_cells segs m' r
[CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n (Z.of_nat (length old)))) old ++ junk)]) ->
HEAPA A' ((r, n) :: lb_remove p LB) LM FR (chargeQ (charge B (acostA n) (uw_cost u) 1) (n + 8192)) m' c' ->
AJ hiA_J T c' ms') ->
AJ hiA_J T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_realloc L)) fc None m (seg_rom segs));

hiA_strdup : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : ASA) (LB LM : list blk) (FR : list frame) (B : bud) (src ab nb lo : Z) (str : list byte) (errv : word) (u : uwd),
HEAPA A LB LM FR B m c ->
In (ab, nb) LB -> ab <= src -> src + Z.of_nat (length str) + 1 <= ab + nb ->
bytes_at segs m src (str ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) + 1 <= 2^26 ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top + 64 ->
rw_cells segs m errno_a [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) -> gp = Z_to_bv 64 (hl_gp L) ->
a0 = Z_to_bv 64 src ->
uw_pre hiA_top m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok (hl_strdup L) ra u ->
1 <= bN B -> acostA (Z.of_nat (length str) + 1) <= bB B -> uw_cost u <= bD B -> Z.of_nat (length str) + 1 + 8192 <= bQ B ->
(forall ms' m' c' A' (r : Z) (errv' : word),
ret_state (hla_base L) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres (hla_base L) (LB ++ LM ++ fr_ivs FR) (bv_unsigned sp) m m' ->
rw_cells segs m' errno_a [C4 errv'] ->
r <> 0 -> bytes_at segs m' r (str ++ [Z_to_bv 8 0]) ->
HEAPA A' ((r, Z.of_nat (length str) + 1) :: LB) LM FR
(chargeQ (charge B (acostA (Z.of_nat (length str) + 1)) (uw_cost u) 1) (Z.of_nat (length str) + 1 + 8192)) m' c' ->
AJ hiA_J T c' ms') ->
AJ hiA_J T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_strdup L)) fc None m (seg_rom segs));

hiA_malloc2 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : ASA) (LB LM : list blk) (FR : list frame) (B : bud) (n lo : Z) (errv : word),
HEAPA A LB LM FR B m c ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top + 64 ->
rw_cells segs m errno_a [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) -> gp = Z_to_bv 64 (hl_gp L) ->
a0 = Z_to_bv 64 n -> 1 <= n <= 4096 -> Z.of_nat (length LM) < 8 ->
1 <= bM B ->
(forall ms' m' c' A' (r : Z) (errv' : word),
ret_state (hla_base L) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres (hla_base L) (LB ++ LM ++ fr_ivs FR) (bv_unsigned sp) m m' ->
rw_cells segs m' errno_a [C4 errv'] ->
( (r = 0 /\ errv' = Z_to_bv 64 ENOMEMv /\ HEAPA A' LB LM FR (chargeM B 1) m' c')
\/ (r <> 0 /\ (exists junk, rw_cells segs m' r [CB (Z.to_nat n) junk])
/\ HEAPA A' LB ((r, n) :: LM) FR (chargeM B 1) m' c') ) ->
AJ hiA_J T c' ms') ->
AJ hiA_J T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_malloc2 L)) fc None m (seg_rom segs));

hiA_free2 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : ASA) (LB LM : list blk) (FR : list frame) (B : bud) (p lo : Z) (errv : word),
HEAPA A LB LM FR B m c ->
(p = 0 \/ exists n, In (p, n) LM) ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top + 64 ->
rw_cells segs m errno_a [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) -> gp = Z_to_bv 64 (hl_gp L) ->
a0 = Z_to_bv 64 p ->
(forall ms' m' c' A' (r : word),
ret_state (hla_base L) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' ->
model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres (hla_base L) (LB ++ lb_remove p LM ++ fr_ivs FR) (bv_unsigned sp) m m' ->
rw_cells segs m' errno_a [C4 errv] ->
HEAPA A' LB (lb_remove p LM) FR B m' c' ->
AJ hiA_J T c' ms') ->
AJ hiA_J T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_free2 L)) fc None m (seg_rom segs));

hiA_stack_malloc : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : ASA) (LB LM : list blk) (FR : list frame) (B : bud) (k bytes lo : Z),
HEAPA A LB LM FR B m c ->
(0 <= k <= 2 \/ (k = 3 /\ hl_stack_malloc L 3 <> 0 /\ Z.of_nat (length FR) < 2048)) -> 1 <= bytes <= fr_size k -> bytes mod 8 = 0 ->
(Z.of_nat (length FR) < 4096) ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top + 64 ->
tp = Z_to_bv 64 (hl_tp L) -> gp = Z_to_bv 64 (hl_gp L) ->
a0 = Z_to_bv 64 bytes ->
(forall ms' m' A' (Fr : Z),
ret_state (hla_base L) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 Fr) m' ms' ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres (hla_base L) (LB ++ LM ++ fr_ivs FR) (bv_unsigned sp) m m' ->
Fr <> 0 ->
(exists junk, rw_cells segs m' Fr [CB (Z.to_nat (fr_size k - 8)) junk]) ->
bytes_at segs m' (shad Fr) (repeat (Z_to_bv 8 0) (Z.to_nat (fr_shadow_len k))) ->
HEAPA A' LB LM ((Fr, k) :: FR) B m' c ->
AJ hiA_J T c ms') ->
AJ hiA_J T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_stack_malloc L k)) fc None m (seg_rom segs));

hiA_frame_release : forall (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config)
(T : TSet) (A : ASA) (LB LM : list blk) (FR : list frame) (B : bud) (Fr k fp pc : Z) (rX : bv 5),
HEAPA A LB LM FR B m c -> In (Fr, k) FR ->
bytes_at segs m (Fr + fr_size k - 8) (le8 (Z_to_bv 64 fp)) ->
0 <= fp < 2^64 ->
Sem.reg_get R rX = Z_to_bv 64 fp ->
bv_unsigned rX <> 0 ->
code_at segs pc [0x23 + Z.shiftl (bv_unsigned rX) 15] ->
(forall m' A',
HEAPA A' LB LM (fr_remove Fr FR) B m' c ->
(forall a, 0 <= a < 2^64 -> a <> fp -> m' (wa a) = m (wa a)) ->
(forall x, wview segs m x <> None -> wview segs m' x <> None) ->
AJ hiA_J T c (MS R F (Z_to_bv 64 (pc + 4)) fc None m' (seg_rom segs))) ->
AJ hiA_J T c (MS R F (Z_to_bv 64 pc) fc None m (seg_rom segs))
}.

Section Parts.
Variable hiA_J : aj_base (hl_segs L).
Variable ASA : Type.
Variable HEAPA : ASA -> list blk -> list blk -> list frame -> bud -> (word -> option byte) -> config -> Prop.
Variables hiA_top hiA_bot : Z.

Record hia_tier1 : Prop := HIA_T1 {
t1_heapA_frame : forall A LB LM FR B m c F k, HEAPA A LB LM FR B m c -> In (F, k) FR ->
0 <= k <= 3 /\ F mod fr_size k = 0 /\ 0 < F /\ F + fr_size k <= alloc_ceiling /\
(F + fr_size k <= hl_img_lo L \/ hl_img_hi L <= F) /\
wr_at segs m F (fr_size k - 8) /\
wr_at segs m (shad F) (fr_shadow_len k) /\

(exists fp, bytes_at segs m (F + fr_size k - 8) (le8 (Z_to_bv 64 fp)) /\ 0 < fp < 2^64 /\
~ client_addr (hla_base L) (LB ++ LM) alloc_ceiling fp /\ (fp < hl_img_lo L \/ hl_img_hi L <= fp) /\
~ hl_scratch L fp /\
(forall F' k', In (F', k') FR -> ~ (F' <= fp < F' + fr_size k') /\ ~ (shad F' <= fp < shad F' + fr_shadow_len k')));
t1_heapA_frame_disjoint : forall A LB LM FR B m c F k a n, HEAPA A LB LM FR B m c -> In (F, k) FR -> In (a, n) (LB ++ LM) ->
F + fr_size k <= a \/ a + n <= F;
t1_heapA_frame_apart : forall A LB LM FR B m c F k F' k', HEAPA A LB LM FR B m c ->
In (F, k) FR -> In (F', k') FR -> F <> F' ->
F + fr_size k <= F' \/ F' + fr_size k' <= F;
t1_heapA_frame_nodup : forall A LB LM FR B m c, HEAPA A LB LM FR B m c -> NoDup (map fr_base FR);
t1_heapA_frame_appmem : forall A LB LM FR B m c F k, HEAPA A LB LM FR B m c -> In (F, k) FR ->
F + fr_size k + 8 <= hl_sb L \/ (2^47 - 1) / 8 + hl_sb L + 1 <= F;
t1_heapA_frame_shadow_sep : forall A LB LM FR B m c F k i, HEAPA A LB LM FR B m c -> In (F, k) FR ->
0 <= i < fr_shadow_len k ->
~ client_addr (hla_base L) (LB ++ LM) alloc_ceiling (shad F + i)
/\ (shad F + i < hl_img_lo L \/ hl_img_hi L <= shad F + i);
t1_hiA_stack_malloc : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : ASA) (LB LM : list blk) (FR : list frame) (B : bud) (k bytes lo : Z),
HEAPA A LB LM FR B m c ->
(0 <= k <= 2 \/ (k = 3 /\ hl_stack_malloc L 3 <> 0 /\ Z.of_nat (length FR) < 2048)) -> 1 <= bytes <= fr_size k -> bytes mod 8 = 0 ->
(Z.of_nat (length FR) < 4096) ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top + 64 ->
tp = Z_to_bv 64 (hl_tp L) -> gp = Z_to_bv 64 (hl_gp L) ->
a0 = Z_to_bv 64 bytes ->
(forall ms' m' A' (Fr : Z),
ret_state (hla_base L) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 Fr) m' ms' ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres (hla_base L) (LB ++ LM ++ fr_ivs FR) (bv_unsigned sp) m m' ->
Fr <> 0 ->
(exists junk, rw_cells segs m' Fr [CB (Z.to_nat (fr_size k - 8)) junk]) ->
bytes_at segs m' (shad Fr) (repeat (Z_to_bv 8 0) (Z.to_nat (fr_shadow_len k))) ->
HEAPA A' LB LM ((Fr, k) :: FR) B m' c ->
AJ hiA_J T c ms') ->
AJ hiA_J T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_stack_malloc L k)) fc None m (seg_rom segs));
t1_hiA_frame_release : forall (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config)
(T : TSet) (A : ASA) (LB LM : list blk) (FR : list frame) (B : bud) (Fr k fp pc : Z) (rX : bv 5),
HEAPA A LB LM FR B m c -> In (Fr, k) FR ->
bytes_at segs m (Fr + fr_size k - 8) (le8 (Z_to_bv 64 fp)) ->
0 <= fp < 2^64 ->
Sem.reg_get R rX = Z_to_bv 64 fp ->
bv_unsigned rX <> 0 ->
code_at segs pc [0x23 + Z.shiftl (bv_unsigned rX) 15] ->
(forall m' A',
HEAPA A' LB LM (fr_remove Fr FR) B m' c ->
(forall a, 0 <= a < 2^64 -> a <> fp -> m' (wa a) = m (wa a)) ->
(forall x, wview segs m x <> None -> wview segs m' x <> None) ->
AJ hiA_J T c (MS R F (Z_to_bv 64 (pc + 4)) fc None m' (seg_rom segs))) ->
AJ hiA_J T c (MS R F (Z_to_bv 64 pc) fc None m (seg_rom segs))
}.

Record hia_tier2 : Prop := HIA_T2 {
t2_hiA_realloc : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : ASA) (LB LM : list blk) (FR : list frame) (B : bud) (p n0 n lo : Z) (errv : word) (old junk0 : list byte) (u : uwd),
HEAPA A LB LM FR B m c -> In (p, n0) LB ->
rw_cells segs m p [CB (Z.to_nat n0) (old ++ junk0)] ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top + 64 ->
rw_cells segs m errno_a [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) -> gp = Z_to_bv 64 (hl_gp L) ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 n -> 1 <= n <= 2^26 ->
uw_pre hiA_top m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok (hl_realloc L) ra u ->
1 <= bN B -> acostA n <= bB B -> uw_cost u <= bD B -> n + 8192 <= bQ B ->
(forall ms' m' c' A' (r : Z) (errv' : word),
ret_state (hla_base L) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
rw_cells segs m' errno_a [C4 errv'] ->
r <> 0 -> heap_pres (hla_base L) (lb_remove p LB ++ LM ++ fr_ivs FR) (bv_unsigned sp) m m' ->
(exists junk, rw_cells segs m' r
[CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n (Z.of_nat (length old)))) old ++ junk)]) ->
HEAPA A' ((r, n) :: lb_remove p LB) LM FR (chargeQ (charge B (acostA n) (uw_cost u) 1) (n + 8192)) m' c' ->
AJ hiA_J T c' ms') ->
AJ hiA_J T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_realloc L)) fc None m (seg_rom segs));
t2_hiA_strdup : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : ASA) (LB LM : list blk) (FR : list frame) (B : bud) (src ab nb lo : Z) (str : list byte) (errv : word) (u : uwd),
HEAPA A LB LM FR B m c ->
In (ab, nb) LB -> ab <= src -> src + Z.of_nat (length str) + 1 <= ab + nb ->
bytes_at segs m src (str ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) + 1 <= 2^26 ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top + 64 ->
rw_cells segs m errno_a [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) -> gp = Z_to_bv 64 (hl_gp L) ->
a0 = Z_to_bv 64 src ->
uw_pre hiA_top m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok (hl_strdup L) ra u ->
1 <= bN B -> acostA (Z.of_nat (length str) + 1) <= bB B -> uw_cost u <= bD B -> Z.of_nat (length str) + 1 + 8192 <= bQ B ->
(forall ms' m' c' A' (r : Z) (errv' : word),
ret_state (hla_base L) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres (hla_base L) (LB ++ LM ++ fr_ivs FR) (bv_unsigned sp) m m' ->
rw_cells segs m' errno_a [C4 errv'] ->
r <> 0 -> bytes_at segs m' r (str ++ [Z_to_bv 8 0]) ->
HEAPA A' ((r, Z.of_nat (length str) + 1) :: LB) LM FR
(chargeQ (charge B (acostA (Z.of_nat (length str) + 1)) (uw_cost u) 1) (Z.of_nat (length str) + 1 + 8192)) m' c' ->
AJ hiA_J T c' ms') ->
AJ hiA_J T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_strdup L)) fc None m (seg_rom segs))
}.

Record hia_static : Prop := HIA_ST {
st_heapA_shadow_glob : forall A LB LM FR B m c, HEAPA A LB LM FR B m c ->
Forall (fun g => bytes_at segs m (shad (fst g)) (repeat (Z_to_bv 8 0) (Z.to_nat (snd g / 8)))) (hl_globals L);
st_heapA_canary : forall A LB LM FR B m c, HEAPA A LB LM FR B m c ->
exists g : word,
bytes_at segs m (hl_got_guard L) (le8 (Z_to_bv 64 (hl_guard L))) /\
bytes_at segs m (hl_guard L) (le8 g) /\ bytes_at segs m (hl_tp L - 16) (le8 g);
st_heapA_need_locks : forall A LB LM FR B m c, HEAPA A LB LM FR B m c -> bytes_at segs m (hl_libc L + 3) [Z_to_bv 8 0];
st_heapA_consts : forall A LB LM FR B m c, HEAPA A LB LM FR B m c -> Forall (fun c => bytes_at segs m (fst c) (snd c)) (hl_consts L);
st_heapA_shadow_stack : forall A LB LM FR B m c a n, HEAPA A LB LM FR B m c ->
hiA_bot <= a -> a + n <= hiA_top + 2^22 -> a + n <= 2^47 -> 0 < n ->
bytes_at segs m (shad a) (repeat (Z_to_bv 8 0) (Z.to_nat ((a + n - 1) / 8 - a / 8 + 1)));
st_heapA_shadow_img : forall A LB LM FR B m c g, HEAPA A LB LM FR B m c ->
hl_img_lo L <= 8 * g -> 8 * g + 8 <= hl_img_hi L ->
bytes_at segs m (g + hl_sb L) [Z_to_bv 8 (img_shadow_val (hl_reg_globals L) g)]
}.

Record hia_donorx : Prop := HIA_DX {
dx_heapA_blk_slack : forall A LB LM FR B m c a n, HEAPA A LB LM FR B m c -> In (a, n) (LB ++ LM) ->
exists junk, bytes_at segs m (a + n) junk /\ Z.of_nat (length junk) = (16 - n mod 16) mod 16;
dx_heapA_shadow_words : forall A LB LM FR B m c a n i, HEAPA A LB LM FR B m c -> In (a, n) LB -> 0 <= i < (n + 7) / 8 ->
exists w : list byte, length w = 8%nat /\ bytes_at segs m ((shad a + i) / 8 * 8) w
}.

Record hia_place : Prop := HIA_PL {
pl_heapA_shadow_sep : forall A LB LM FR B m c a n i, HEAPA A LB LM FR B m c -> In (a, n) LB -> 0 <= i < (n + 7) / 8 ->
~ client_addr (hla_base L) (LB ++ LM) alloc_ceiling (shad a + i)
/\ (shad a + i < hl_img_lo L \/ hl_img_hi L <= shad a + i);
pl_heapA_blk_appmem : forall A LB LM FR B m c a n, HEAPA A LB LM FR B m c -> In (a, n) (LB ++ LM) ->
a + n + 8 <= hl_sb L \/ (2^47 - 1) / 8 + hl_sb L + 1 <= a
}.

Definition hiA_malloc_paid_ty : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : ASA) (LB LM : list blk) (FR : list frame) (B : bud) (n lo : Z) (errv : word) (u : uwd),
u = UWpaid ->
HEAPA A LB LM FR B m c ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top + 64 ->
rw_cells segs m errno_a [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) -> gp = Z_to_bv 64 (hl_gp L) ->
a0 = Z_to_bv 64 n -> 1 <= n <= 2^26 ->
uw_pre hiA_top m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok (hl_malloc L) ra u ->
1 <= bN B -> acostA n <= bB B -> uw_cost u <= bD B -> n + 8192 <= bQ B ->
(forall ms' m' c' A' (r : Z) (errv' : word),
ret_state (hla_base L) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres (hla_base L) (LB ++ LM ++ fr_ivs FR) (bv_unsigned sp) m m' ->
rw_cells segs m' errno_a [C4 errv'] ->
r <> 0 -> (exists junk, rw_cells segs m' r [CB (Z.to_nat n) junk]) ->
HEAPA A' ((r, n) :: LB) LM FR (chargeQ (charge B (acostA n) (uw_cost u) 1) (n + 8192)) m' c' ->
AJ hiA_J T c' ms') ->
AJ hiA_J T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_malloc L)) fc None m (seg_rom segs)).
Definition hiA_free_paid_ty : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : ASA) (LB LM : list blk) (FR : list frame) (B : bud) (p lo : Z) (errv : word) (u : uwd),
u = UWpaid ->
HEAPA A LB LM FR B m c ->
(p = 0 \/ exists n, In (p, n) LB) ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top + 64 ->
rw_cells segs m errno_a [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) -> gp = Z_to_bv 64 (hl_gp L) ->
a0 = Z_to_bv 64 p ->
uw_pre hiA_top m (bv_unsigned sp) (bv_unsigned s0) u /\ uw_ok (hl_free L) ra u ->
(if Z.eqb p 0 then 0 else uw_cost u) <= bD B ->
(forall ms' m' c' A' (r : word),
ret_state (hla_base L) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' ->
model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres (hla_base L) (lb_remove p LB ++ LM ++ fr_ivs FR) (bv_unsigned sp) m m' ->
rw_cells segs m' errno_a [C4 errv] ->
HEAPA A' (lb_remove p LB) LM FR (charge B 0 (if Z.eqb p 0 then 0 else uw_cost u) 0) m' c' ->
AJ hiA_J T c' ms') ->
AJ hiA_J T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_free L)) fc None m (seg_rom segs)).
Definition hiA_calloc_paid_ty : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : ASA) (LB LM : list blk) (FR : list frame) (B : bud) (cnt sz lo : Z) (errv : word) (u : uwd),
u = UWpaid ->
HEAPA A LB LM FR B m c ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top + 64 ->
rw_cells segs m errno_a [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) -> gp = Z_to_bv 64 (hl_gp L) ->
a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 sz -> 0 <= cnt < 2^32 -> 0 <= sz < 2^32 -> 1 <= cnt * sz <= 2^26 ->
uw_pre hiA_top m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok (hl_calloc L) ra u ->
1 <= bN B -> acostA (cnt * sz) <= bB B -> uw_cost u <= bD B -> cnt * sz + 8192 <= bQ B ->
(forall ms' m' c' A' (r : Z) (errv' : word),
ret_state (hla_base L) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres (hla_base L) (LB ++ LM ++ fr_ivs FR) (bv_unsigned sp) m m' ->
rw_cells segs m' errno_a [C4 errv'] ->
r <> 0 -> rw_cells segs m' r [CB (Z.to_nat (cnt * sz)) (repeat (Z_to_bv 8 0) (Z.to_nat (cnt * sz)))] ->
HEAPA A' ((r, cnt * sz) :: LB) LM FR (chargeQ (charge B (acostA (cnt * sz)) (uw_cost u) 1) (cnt * sz + 8192)) m' c' ->
AJ hiA_J T c' ms') ->
AJ hiA_J T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_calloc L)) fc None m (seg_rom segs)).

Definition hiA_free2_null_ty : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : ASA) (LB LM : list blk) (FR : list frame) (B : bud) (p lo : Z) (errv : word),
p = 0 ->
HEAPA A LB LM FR B m c ->
(p = 0 \/ exists n, In (p, n) LM) ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top + 64 ->
rw_cells segs m errno_a [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) -> gp = Z_to_bv 64 (hl_gp L) ->
a0 = Z_to_bv 64 p ->
(forall ms' m' c' A' (r : word),
ret_state (hla_base L) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' ->
model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres (hla_base L) (LB ++ lb_remove p LM ++ fr_ivs FR) (bv_unsigned sp) m m' ->
rw_cells segs m' errno_a [C4 errv] ->
HEAPA A' LB (lb_remove p LM) FR B m' c' ->
AJ hiA_J T c' ms') ->
AJ hiA_J T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_free2 L)) fc None m (seg_rom segs)).
End Parts.

End IfaceA.
End RC__1.

Arguments AJ {segs} _ _ _ _.
Arguments CK {segs} _ _.
Arguments CNEXT {segs} _ _ _.
Arguments aj_evt {segs} _ _ _ _ _.
Arguments aj_conseq {segs} _ _ _ _ _ _ _.
